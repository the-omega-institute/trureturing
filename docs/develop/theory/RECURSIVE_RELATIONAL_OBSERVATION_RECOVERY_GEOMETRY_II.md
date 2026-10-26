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

## 44. The acquired source with a finite nonnegative pulse menu

**Definition 44.1 (one retained origin and its controlled chronology).** Retain exactly the source, preparation and installed premises of Definitions 36.1–36.3. Perform Theorem 37.2 on that actual source, retaining its native matrix, law and the same callable installation. Write

$$
b=e_0,\qquad x_*=T^{2N}b,\qquad
K=[b,Tb,\ldots,T^{N-1}b],\qquad M=K^{-1}TK.
$$

Thus $x_*$ is the actual acquired phase. Invertibility of $K$ is supplied by Lemma 37.1, rather than supplied as order or coefficient advice. Whenever pulses are used, the separate Add right of Assumption 36.2 is installed. Fix an integer $H\ge0$. A pulse word of length $L\ge0$ is the actual ordered input list

$$
u=(u_0,\ldots,u_{L-1})\in\{0,\ldots,H\}^L.
$$

Its $i$th action is literally Tick; Add$(u_i)$; Read. If $x_i$ is the field before that action, the intermediate Tick output, acknowledgement and final Read output are respectively

$$
\tau_i=b^{\mathsf T}Tx_i,\qquad \mathrm{ack}_{\rm Add},\qquad
y_i=b^{\mathsf T}(Tx_i+u_i b),
\qquad x_{i+1}=Tx_i+u_i b.
$$

All three are outputs. Hold and local calculation produce no additional Ticks. The initial acquired origin and the completed pulse length $L$ are retained; $L$ is an earned counter, not an inferred passive epoch. The target is this word, including zero pulses and their positions. An archive of earlier inputs or emitted replies is a separate retained object. The current field need not contain that archive.

**Definition 44.2 (the integer polynomial of the earned law).** In §§44–51 denote the monic rational polynomial of Proposition 37.4 by $\bar q$. Clear its coefficient denominators and divide by their positive greatest common divisor, choosing positive leading coefficient, to obtain the unique primitive polynomial

$$
q(z)=\sum_{j=0}^{N}q_jz^j\in\mathbb Z[z],\qquad
a=q_N>0,\qquad \bar q=q/a,\qquad
h=\max_{0\le j\le N}|q_j|.
$$

No irreducibility hypothesis is imposed. Both $q(T)=0$ and the absence of a nonzero annihilator of $b$ of degree below $N$ are supplied by Proposition 37.4 and Lemma 37.1. In fact $a\ge2$: the roots $\lambda_i$ of $\bar q$ are the $N$ eigenvalues of the actual symmetric $T$, with $0<\lambda_i<1$, so

$$
0<|q_0|=a\prod_{i=1}^{N}\lambda_i<a.
$$

The two endpoint inequalities use $N\ge1$ and strict positivity and contraction. Since $q_0$ is a nonzero integer, they imply the assertion. In particular $h\ge a$.

**Proposition 44.3 (the exact pulse polynomial on the actual phase).** For every promised source, $H,L$ and actual word $u$,

$$
\begin{aligned}
x_L(u)&=T^Lx_*+E_L(u),\\
E_L(u)&=\sum_{j=0}^{L-1}T^jb\,u_{L-1-j}.
\end{aligned}
$$

For two words of this same length, put

$$
P_{uv}(z)=\sum_{j=0}^{L-1}
 (u_{L-1-j}-v_{L-1-j})z^j\in\mathbb Z[z].
$$

Their full native endpoints agree if and only if $q\mid P_{uv}$ in $\mathbb Q[z]$. This is also equivalent to $P_{uv}=qS$ for some $S\in\mathbb Z[z]$.

Proof. The state formula is Lemma 38.2 with pulses at the successive post-Tick epochs; equivalently its induction has step $x\mapsto Tx+ub$. In particular the homogeneous term is $T^{L+2N}b$, with no new zero preparation. Subtracting two equal-length formulas gives $P_{uv}(T)b$.

Divide an arbitrary rational $P$ by the monic $\bar q$, obtaining $P=\bar q A+R$ with $\deg R<N$. If $P(T)b=0$, then $R(T)b=0$, hence $R=0$ by the independence of the columns of $K$. The converse follows from $q(T)=0$. Scaling $\bar q$ by $a$ does not change rational divisibility.

For the integral quotient, apply Gauss's primitive-divisibility lemma with coefficient domain $\mathbb Z$, fraction field $\mathbb Q$, primitive divisor $q$ and integral dividend $P_{uv}$. Its precise supplied statement is `Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map` in [pinned Mathlib, GaussLemma](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Polynomial/GaussLemma.lean). It requires primitivity of the divisor, not irreducibility or primitivity of the dividend. It supplies $S\in\mathbb Z[z]$ directly. This mature algebraic step is an intermediate supplier, not a new divisibility theorem. $\square$

## 45. The sharp all-length menu threshold and a bounded collision

**Lemma 45.1 (the actual bounded region and the pulse lattices).** Define the computable rational vector and integer

$$
s=(I-T)^{-1}b,\qquad
R=\left\lceil a\max_{0\le i<N}\sum_{k=0}^{N-1}
 |(K^{-1})_{ik}|s_k\right\rceil,\qquad
C=(2R+1)^N.
$$

All entries of $s$ are positive. For $L\ge N$ put

$$
\Lambda_L=\sum_{j=0}^{L-1}\mathbb Z M^j e_0\subset\mathbb Q^N.
$$

Then $\Lambda_N=\mathbb Z^N$ and

$$
[\Lambda_L:\mathbb Z^N]=a^{L-N}.
$$

For every word over $\{0,\ldots,a\}$ its vector $K^{-1}E_L(u)$ belongs to $\Lambda_L\cap[-R,R]^N$, and this intersection has at most $Ca^{L-N}$ points.

Proof. Positive definiteness makes every diagonal entry of $T$ positive, and the links are positive. Thus $T$ is entrywise nonnegative. The finite-dimensional geometric series, justified by $\|T\|_2<1$, gives

$$
s=\sum_{j\ge0}T^jb.
$$

For cell $k$ the term $T^kb$ has positive $k$th coordinate by Lemma 37.1. Consequently $s_k>0$, and nonnegative pulse digits at most $a$ give the entrywise bound $0\le E_L(u)\le as$. The definition of $R$ therefore bounds every power-basis coordinate by $R$. These constants are rational matrix calculations followed by an integer ceiling, with no spectral or response oracle.

Since $K^{-1}b=e_0$ and $K^{-1}T^jb=e_j$ for $j<N$, the initial lattice is $\mathbb Z^N$. For $l\ge N$ the quotient $\Lambda_{l+1}/\Lambda_l$ is generated by the class of $M^le_0$. The relation $z^{l-N}q(z)$ shows that this class has order dividing $a$. Conversely, if $nM^le_0\in\Lambda_l$ for an integer $n$, there is an integral polynomial of the form

$$
nz^l-\sum_{j<l}c_jz^j
$$

that annihilates $b$ at $T$. Proposition 44.3 and its primitive-divisibility supplier make it an integral multiple of $q$. If $n\ne0$, comparison of leading coefficients gives $a\mid n$. Thus the cyclic quotient has exactly $a$ elements. Multiplication of these finite indices proves the displayed index for every $L\ge N$.

Each of its $a^{L-N}$ cosets modulo $\mathbb Z^N$ has at most $(2R+1)^N$ points in $[-R,R]^N$: in each coordinate a translate of $\mathbb Z$ has at most $2R+1$ points in an interval of length $2R$. This proves the count without replacing an actual lattice count by a volume approximation. $\square$

**Theorem 45.2 (exact finite-menu chronology threshold).** For each promised acquired source and integer $H\ge0$,

$$
\bigl[\text{$E_L$ is injective on $\{0,\ldots,H\}^L$
 for every finite $L$}\bigr]\quad\Longleftrightarrow\quad H<a.
$$

If $H\ge a$, two distinct words of one common length can be constructed from the earned finite law alone. One sufficient explicit length is

$$
\ell=N+aC,
$$

with $C$ as in Lemma 45.1. More sharply, any $l\ge N$ satisfying $(a+1)^l>Ca^{l-N}$ suffices. The construction uses digits at most $a$, hence is valid for every $H\ge a$.

Proof. Suppose $H<a$ and two endpoints agree. A nonzero difference polynomial $P_{uv}$ would equal $qS$ with integral nonzero $S$ by Proposition 44.3. Its leading coefficient would be $a$ times a nonzero integer, so its magnitude would be at least $a$. Every coefficient of $P_{uv}$ has magnitude at most $H$, a contradiction. Thus $P_{uv}=0$, giving equality of all word positions. This also covers $H=0$ and the empty word.

For the converse, the $(a+1)^l$ words over $\{0,\ldots,a\}$ map, in the same power coordinates, into the at most $Ca^{l-N}$ points of Lemma 45.1. The finite pigeonhole principle gives distinct words with equal $E_l$, hence equal actual native endpoints from $x_*$. For $l=N+aC$, Bernoulli's inequality gives

$$
\frac{(a+1)^l}{a^{l-N}}
=(a+1)^N(1+1/a)^{aC}
\ge(a+1)^N(1+C)>C.
$$

This verifies a finite bound by integer inequalities. To find a pair, form the finite list of those words, evaluate their endpoint vectors by rational arithmetic on the earned $T,x_*$, and compare the exact vectors until equality. The pigeonhole bound proves termination. These evaluations are local calculations; none enacts a hypothetical input on the specimen, queries an unobserved response or requires another initialization. One may instead compare polynomial remainders modulo the earned $q$. Neither option is asserted to have small cost. $\square$

**Corollary 45.3 (short horizons and delayed collisions).** For every menu bound $H$, no collision is possible at $L\le N$. At $L=N+1$, a collision exists if and only if $H\ge h$. Consequently, when $a\le H<h$, collisions exist at some finite lengths but none at or before $N+1$.

Proof. A nonzero polynomial of degree below $N$ cannot annihilate $b$. At length $N+1$, a nonzero divisible difference polynomial has degree $N$ and, by integral divisibility, equals $cq$ for an integer $c\ne0$. Its maximum coefficient magnitude is $|c|h\ge h$. Conversely, if $H\ge h$, write $q_j=q_j^+-q_j^-$ with $q_j^\pm\in\{0,\ldots,h\}$ and assign these coefficients in reverse order to two length-$N+1$ words. They are distinct and their difference polynomial is $q$. Apply Proposition 44.3. The remaining assertion follows from Theorem 45.2. $\square$

**Example 45.4 (a nonempty delay interval).** The promised native path

$$
T=\begin{pmatrix}3/4&1/8\\1/8&3/4\end{pmatrix}
$$

has eigenvalues $5/8,7/8$ and primitive polynomial $q(z)=64z^2-96z+35$. Thus $N=2$, $a=64$ and $h=96$. Every integer menu bound $64\le H<96$ has eventual collisions by Theorem 45.2, although lengths at most three are injective. The example illustrates the distinction between the leading-coefficient threshold and the first possible degree; the quantified assertions do not depend on this example.

## 46. Post-pulse acquisition and the independently meaningful expressions

**Definition 46.1 (the four controlled expressions and their shared context).** Fix the actually acquired installation of Definition 44.1 and an earned length $L$. The following data have distinct meanings.

| Expression | Exposed data at the declared pulse cut |
| --- | --- |
| Space | The actual rooted native path and its current field $(T,x_L)$. |
| Time | The actual ordered paid input word $u\in\{0,\ldots,H\}^L$. |
| Boundary | The literal callable root service; an acquired numerical boundary window consists of its next $N$ scalar root replies under Read followed by $N-1$ Ticks. |
| Memory | The earned law and the current predictive vector $w=\mathcal O_Nx_L$, with the acquired origin, length, and original retained callable installation. |

Here $\mathcal O_N=K^{\mathsf T}$ is exactly the native observation matrix of Proposition 39.3. All numerical recovery directions below may use the shared earned law, $H$, $L$ and the original origin $x_*$. The boundary window contains prospective observations, not prior pulse symbols. Predictive Memory stores $N$ current predictions, not a definitionally inserted copy of Time. Space exposes actual native cells, not arbitrary realization coordinates. The handle, rights, assurance and backing are additional actual parts of the installation. None of the four numerical descriptions certifies them from a transcript.

**Theorem 46.2 (same-specimen acquisition and exact word recovery).** Suppose $H<a$. After any actual length-$L$ pulse word, there is a terminating procedure that recovers that word using exactly $N$ new scalar root replies and $N-1$ new Ticks on the same specimen, then finite local calculation. It recovers the native field at the pulse endpoint and leaves a predictive record synchronized with the actual current field after those observation Ticks.

Proof. Read the present root value $z_0$ and then execute $N-1$ Ticks, retaining their scalar returns $z_1,\ldots,z_{N-1}$. No Add occurs during this observation window. Its exact semantics are

$$
z_j=b^{\mathsf T}T^jx_L,\qquad
z=\mathcal O_Nx_L.
$$

Invertibility of $\mathcal O_N=K^{\mathsf T}$ is already earned by Lemma 37.1. Apply the finite observability inverse of Proposition 39.3 to obtain $x_L=\mathcal O_N^{-1}z$. This is the supplied observability algebra with state space $\mathbb R^N$, evolution $T$, scalar readout $b^{\mathsf T}$ and horizon $N$, not another law-identification experiment. It also matches `finite_observability_equivalence` in [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs): its stacked map uses times $0,\ldots,N-1$, and $K$ supplies its full-rank hypothesis here. The infinite-family law and authentic origin were earned before these calls.

Compute $d=x_L-T^Lx_*$. Among the finite $(H+1)^L$ menu words, compare $E_L$ with $d$ by exact local rational calculation. Existence of a match follows from the actual run, and Theorem 45.2 supplies uniqueness. At $L=0$ the sole candidate is the empty word and the same observation procedure is still permitted. No new calls are used in this finite decoding.

During the window the actual specimen has advanced to $x_{\rm now}=T^{N-1}x_L$. Hold it while setting

$$
\widehat x=x_{\rm now},\qquad w_{\rm now}=\mathcal O_Nx_{\rm now}.
$$

The new record therefore represents the true current field. If $N=1$, the window has one Read and no Tick, so the two fields coincide. In general the procedure keeps the recovered historical endpoint $x_L$ distinct from $x_{\rm now}$; it performs no rollback or Reset. The $N-1$ diagnostic Ticks are retained as such, not silently reinterpreted as pulse actions or erased from the source's actual chronology. $\square$

**Proposition 46.3 (agreement of recovery routes and subsequent actual use).** In the regime $H<a$, the numerical Space, Time and predictive Memory of Definition 46.1 determine one another on their declared actual images, with the shared acquired context. The paid Boundary window determines the same pulse endpoint and Time. Every numerical recovery route through these data agrees. The retained installation after Theorem 46.2 supports every finite common legal adaptive continuation, predicting all its outputs and actual successors, including subsequent rational Add inputs when authorized.

Proof. Time computes $x_L$ by Proposition 44.3 and then $w=\mathcal O_Nx_L$. Space computes $w$, and Memory recovers $x_L$ by the supplied observation inverse. Each computes the same unique pulse word by Theorem 45.2 and the finite decoding in Theorem 46.2. Thus every route factors through this same actual native field and its unique word. The numerical boundary window gives that field by the same inverse. From Time or Space one may calculate its predicted window, but only actual Read/Tick calls acquire that window's source provenance and advance its cut.

At the new held cut the invariant of Theorem 40.2 holds with $\widehat x=x_{\rm now}$ and $w_{\rm now}=\mathcal O_Nx_{\rm now}$. Its proof applies to every rational current vector, so use it directly for subsequent calls. For clarity, writing $\bar q=q/a$, the predictive Tick update is

$$
w'_j=w_{j+1}\ (j<N-1),\qquad
w'_{N-1}=-\sum_{j<N}(q_j/a)w_j,
$$

and Add$(v)$ replaces $w_j$ by $w_j+v\mu_j$. The actual service and record use the same supplied $v$, source binding and serialized calls. These identities give the intermediate Tick root, Add acknowledgement and final Read separately. Equal prior replies also give equal adaptive choices, exactly as in Theorem 40.2. This reuses its complete-action invariant; no journal inverse follows from that invariant alone.

On a pulse cut before diagnostic Ticks, appending one actual pulse satisfies

$$
x_{L+1}=Tx_L+u_Lb,\qquad E_{L+1}=TE_L+u_Lb.
$$

The inverse at the earned length $L+1$ therefore returns exactly the old word followed by $u_L$. After diagnostic Ticks, continued prediction starts at the advanced actual field. A later consecutive pulse block may use that retained field as its known initial phase; the same affine difference and injectivity argument applies, with its own retained block length. It is not asserted to have started at $x_*$ without those intervening Ticks. $\square$

## 47. Endpoint erasure, common futures and the price of an archive

**Theorem 47.1 (exponential equal-endpoint histories).** Suppose $H\ge a$, and let $U\ne V$ be any equal-endpoint pulse pair of common length $\ell$. For each integer $m\ge0$, the actual source admits $2^m$ distinct legal pulse histories of length $m\ell$ with identical current native fields, law, origin, length and retained rights. If no distinguishing past information is retained, every common future source operation sequence, including a finite adaptive one, has identical complete outputs and successors on those histories. Consequently those present data, even supplemented with all common future source behavior, cannot recover the pulse word on the full declared domain.

Proof. A fixed block $W$ acts on every starting field by

$$
F_W(x)=T^\ell x+E_\ell(W).
$$

The block collision says $E_\ell(U)=E_\ell(V)$, so $F_U=F_V$ as maps on every current field. Choose independently $U$ or $V$ in each of the $m$ block positions. Starting from the same actual $x_*$, all block-boundary fields, in particular the final field, agree. The $2^m$ concatenated words are distinct because their equal-length blocks have fixed boundaries and $U\ne V$. All of them are permitted drives of this original acquired installation; no extra source is used to enact a block within a run.

From an equal field and the same $T$, Read and Hold give equal outputs without changing the field, Tick gives the same updated field and root output, and any common Add input gives the same acknowledgement and updated field. Thus the present-state equality is a congruence for the entire installed menu. Induction gives the assertion for common finite sequences. An adaptive policy depending only on the shared current data and later replies makes identical choices at each step; a shared random tape gives the same conclusion pathwise. Equality for all finite prefixes also gives equality of any common infinite response stream where that stream is defined.

The theorem concerns erased past information. A controller state, external reference or input supplier that still distinguishes the earlier words is additional retained information and cannot be omitted from its premise. Past emissions are likewise not equated by endpoint equality. $\square$

**Proposition 47.2 (complete past emissions reveal the inputs).** For every $H$, including $H\ge a$, retaining both scalar replies of each original pulse permits exact recovery of every input by

$$
u_i=y_i-\tau_i.
$$

In particular the histories in Theorem 47.1 do not have identical complete past emissions. On its $2^m$-element equal-endpoint family, any fixed-width binary archive that, together with the common present data, recovers the word must contain at least $m$ variable data bits.

Proof. The root has $b^{\mathsf T}b=1$. Add$(u_i)$ changes its value by exactly $u_i$, with no intervening Tick, giving the identity. At the first differing pulse of two words, the prior fields and intermediate Tick replies agree, whereas the final Read replies differ by the nonzero input difference. Thus equality of complete past emissions would imply equality of every pulse input. Finally $m$ independent block choices require at least $2^m$ distinct archive values; a fixed-width binary store of $r$ bits has at most $2^r$ values. $\square$

**Corollary 47.3 (the exact failure boundary).** For each fixed acquired source, a pulse-word inverse valid at all retained finite lengths from current native state and the earned law exists exactly when $H<a$. At $H\ge a$, current Boundary and predictive Memory still support exact future prediction as in Theorem 40.2, while some earlier pulse words remain indistinguishable unless past information is retained. This obstruction neither applies to an archive that distinguishes them nor contradicts the original passive phase inverse.

Proof. The positive direction is Theorem 45.2 with finite decoding, and the negative direction is Theorem 47.1. Future prediction uses the already supplied current-state invariant. Definition 39.1's passive domain has no Add pulses, and its Time is the acquired passive root transcript rather than the controlled input word of Definition 44.1. Proposition 47.2 accounts for the archive alternative explicitly. $\square$

## 48. Bounded fields still carry unbounded exact chronology

**Theorem 48.1 (exact-state information lower bound).** Fix a promised acquired source and $1\le H<a$. For every fixed length $L$, its actual pulse menu realizes exactly $(H+1)^L$ distinct native endpoints. All of them, simultaneously for every finite $L$, lie in the bounded box

$$
\prod_{i=0}^{N-1}[0,(H+1)s_i],\qquad s=(I-T)^{-1}b.
$$

Any fixed-width binary representation that distinguishes all the configurations on this length stratum, with a common decoder and the shared acquired context, needs at least

$$
\left\lceil L\log_2(H+1)\right\rceil
$$

variable data bits. This applies also to the full predictive vector, since its map from the native field is invertible.

Proof. The actual finite controller can drive any of the $(H+1)^L$ allowed words. Theorem 45.2 makes their endpoints distinct. Every term $T^jb$ is entrywise nonnegative, and their sum is $s$. The authentic acquired-phase term $T^{2N+L}b$ is one of those terms, so it is bounded entrywise by $s$; the pulse term is bounded by $Hs$. This proves the same fixed box for all $L$, preserving the actual nonzero initial phase.

If a fixed-width representation had $r$ variable bits, it would have at most $2^r$ values. Distinguishing the realized endpoints forces $2^r\ge(H+1)^L$ and hence the displayed ceiling. The observation inverse transports distinctness to predictive Memory. A reference to varying external backing counts that backing as part of the representation; a common law description can be shared because it does not vary among these words. The bound concerns fixed-width distinguishability, not a lower bound for every individual variable-length codeword. $\square$

**Corollary 48.2 (no uniform positive exact-resolution margin).** Under Theorem 48.1 the minimum distance between distinct endpoints cannot have a positive lower bound independent of $L$, either in native Euclidean coordinates or in the fixed predictive coordinates. Consequently bounded native amplitude and finite vector dimension do not supply a uniform finite-precision exact chronology instrument.

Proof. A bounded box in finite-dimensional Euclidean space can be partitioned into finitely many boxes of diameter less than any specified $\varepsilon>0$. Once $(H+1)^L$ exceeds that finite count, two distinct endpoints lie in one box. The predictive image is another bounded finite-dimensional set because $\mathcal O_N$ is a fixed linear map, so the same argument applies there. This proves the absence of a uniform margin, without postulating a noise distribution or asserting impossibility for a differently specified approximate task. $\square$

## 49. One attained acquisition, decoding and continued-use account

**Definition 49.1 (binary sizes of the same source and observer).** Use Convention 41.1's reduced rational encoding and denote the native coefficient size by $B$. Let $D$ be the product of their positive denominators, so $DT$ is integral and $\log_2D\le B$. After acquisition one may retain the following finite rational data:

$$
T,\ K,\ K^{-1},\ \mathcal O_N,\ \mathcal O_N^{-1},\ q,\ \mu,\ x_*,\ s.
$$

Let $F\ge B+N$ bound their total binary encoding, including the numerators and denominators of the fixed matrices, and the maximum intermediate width in the fixed calculations used to construct them. These data are computed from the earned source law by finite matrix arithmetic; their widths are charged. Such an $F$ is finite for every earned source and can be chosen after those fixed calculations. No bound $F$ is supplied before acquisition. For a fixed $H,L$, put

$$
\begin{aligned}
Q_L&=(H+1)^L,\qquad d_H=\lceil\log_2(H+1)\rceil,\\
W_L&=1+F+(L+3N)\lceil\log_2(D+1)\rceil
       +\lceil\log_2(H+2)\rceil
       +\lceil\log_2(L+2)\rceil.
\end{aligned}
$$

$W_L$ is an envelope up to absolute constant factors for the explicitly described variable-width rational calculations below. Binary counters, copying, comparisons, rational reduction, input/output serialization, source operations, reference/rights and backing have their own charges. In particular a field-operation count does not set the cost of operating on a $W_L$-bit integer to one bit operation.

**Proposition 49.2 (source calls and complete traffic on one run).** One attained route consists of the original acquisition, $L$ pulse actions, the observation window of Theorem 46.2, and the subsequent held local decoding. Before a later continuation, its exact totals are

$$
\begin{array}{c|c}
\text{Source operation or output}&\text{Count}\\ \hline
\mathrm{Tick}&2N+L+(N-1)=3N+L-1\\
\mathrm{Add}&L\\
\mathrm{Read}&1+L+1=L+2\\
\text{Scalar root replies}&(2N+1)+2L+N=3N+1+2L\\
\text{Add acknowledgements}&L.
\end{array}
$$

One can use the $N+1$ acquisition Holds of Proposition 41.2 and one additional Hold after the observation window. Any further Holds, policy calls and copied outputs are charged separately. The pulse symbols are $L$ paid serialized input words even if subsequently discarded.

Proof. Acquisition has one Read and $2N$ Ticks. Each pulse has one Tick, one Add and one Read; its Tick return and final Read are two scalar outputs. The final window has one Read and $N-1$ Ticks, giving $N$ scalar replies. Fixed acknowledgements are added rather than counted as scalars. No autonomous Tick occurs between these operations, so the source's actual state at the held decoding cut is exactly $T^{N-1}x_L$.

For the direct two-buffer native multiplication of Proposition 41.2, multiply the Tick count by $3N-2$ source scalar multiplications and $2N-2$ additions. Add also performs its actual root addition. Literal bit traffic is the sum of the serialized lengths of every input, reply and acknowledgement, together with operation/control framing. Source preparation, acquired-class assurance, root binding, the installed Add right and all retained backing remain additional coexisting resources, as in Assumption 36.2. $\square$

**Proposition 49.3 (attained exact widths and local work).** The above route can use the acquisition bound of Proposition 41.3, followed by $O(N^3)$ rational operations to construct fixed inverse matrices. The $L$ pulse updates and the observation-window synchronization use $O(N(L+N))$ further rational operations when the redundant native record is retained. For $H<a$, one finite local decoder uses at most

$$
O\bigl(Q_LN(L+1)+N^2+NL\bigr)
$$

additional rational operations and exact comparisons, without further source calls. Its current rational words and transient numerator products have width $O(W_L)$; its menu words and output require $O(Ld_H+L+1)$ binary data bits. The numerical input and scalar-root traffic of Proposition 49.2 is at most $O((N+L)W_L)$ bits, with actual fixed acknowledgements and operation framing added. These are sufficient bounds, without an optimality assertion.

Proof. The acquisition calculation and its square-root charges are already supplied in §41. Constructing $K$ and the observation matrix uses successive sparse products; exact elimination constructs their inverses with a conservative cubic field-operation allowance, at the actual fixed widths included in $F$.

After $t$ total Ticks from the authentic preparation, all native coordinate denominators divide $D^t$: Tick multiplies by $D^{-1}(DT)$ and an integral pulse introduces no new denominator. Through the last observation reply, $t\le L+3N-1$. Every current coordinate has magnitude at most $(H+1)\|s\|_\infty$. This was proved in Theorem 48.1 at pulse cuts, and remains true during diagnostic Ticks because $Ts=s-b\le s$ entrywise. Intermediate Tick and post-Add cuts have the same bound. Since the total encoding of $s$ is included in $F$, the reduced numerator and denominator lengths are

$$
O\bigl(F+(L+3N)\log_2(D+1)+\log_2(H+2)\bigr).
$$

For fixed-matrix products use a common denominator equal to the product of the relevant fixed denominators, whose logarithm is at most $F$, together with $D^t$. Taking at most $N$ summands adds only $O(\log(N+1))$ bits. Reduction and cross-multiplication for equality use widths within an absolute constant factor of this envelope. The same argument bounds the recovered pulse endpoint, the current predictive vector, the computed baseline $T^Lx_*$ and every locally simulated candidate. Intermediate products before reduction have at most twice these widths.

For a decoder with an explicit finite bound, list the $Q_L$ candidate menu words and evaluate each starting at the retained $x_*$ by $L$ sparse local updates $v\mapsto Tv+u_i b$. Compare its final native vector with the recovered $x_L$. Each candidate takes $O(N(L+1))$ rational operations and comparisons, and no candidate sends a command to the specimen. A candidate counter and its $L$ symbols suffice to form the finite list successively; no table of all endpoints is required. The actual-image promise supplies one match and Theorem 45.2 supplies exactly one. A candidate word and a distinct retained output copy each have at most $Ld_H$ symbol bits, with length and framing charged. The baseline calculation, matrix-vector observation inverse and current synchronization fit the remaining allowance. All counters, including the enumeration counter of at most $\lceil\log_2 Q_L\rceil+1$ bits, are finite and charged. Finally each of the $O(N+L)$ scalar replies has width $O(W_L)$, and each of the $L$ nonnegative integer inputs has width $O(\log_2(H+2))\subseteq O(W_L)$. This proves the numerical traffic bound. $\square$

**Proposition 49.4 (simultaneous stores and later use).** There is one layout realizing Propositions 49.2–49.3 in which the following resources coexist at the decoding cut:

| Coexisting resource | Size or mathematical charge |
| --- | --- |
| Actual source | $N$ cells, $N-1$ links, coefficient store $B$ and two state buffers of $O(NW_L)$ bits. |
| Acquired data and fixed observer law | The retained $2N+1$-value acquisition record, of $O(N^2B+N)$ bits by §41, and the fixed $F$-bit data of Definition 49.1. |
| Current observer and observation record | Native/predictive vectors, the $N$ paid observation replies, and $O(NW_L)$ bits of current numeric data. |
| Inverse-matrix scratch | At most $O(N^2W_L)$ bits, retained here as a conservative allowance even if some fixed calculations have finished. |
| Candidate, counters and recovered word | $O(Ld_H+L+\log(N+2)+1)$ bits, with distinct retained input/output copies added when present. |
| Optional pulse-reply archive | Its actual $A_{\rm past}$ bits, including both scalar replies if both are retained. |
| Serialization and extra delivery copies | Their actual simultaneous $A_{\rm io}$ bits. |
| Installation and access | Actual origin/class assurance, finite controller description, source reference, Read/Tick/Hold/Add rights and their backing. |

Consequently the stated numerical stores have the simultaneous sufficient bound

$$
O\bigl(F+N^2B+N^2W_L+Ld_H+L+A_{\rm past}+A_{\rm io}+1\bigr),
$$

with the actual installation, description, reference/rights and backing charges added. A store shared in fact need be counted only once; a second retained copy is added. Acquisition peak scratch retains its separate bound from §41, and may be allocated together with these stores if a single larger layout is wanted.

Proof. Add the listed stores, rather than selecting different components from incompatible runs. Theorem 46.2's replies are acquired by this same source, while the source buffers, earned law, optional archives and retained installation remain present. Proposition 49.3 gives the common width envelope and the finite candidate scratch. A bit-cost realization can apply any terminating exact integer arithmetic to these finite words: for example, grade-school multiplication/division and Euclidean reduction give a polynomial bit charge per listed rational operation. Comparisons and copying pay their actual word lengths. No bounded bit cost independent of $W_L$ is inferred from the operation count.

After decoding, use Proposition 46.3's actual current predictive record. Each subsequent call pays its source work, literal traffic, predictive update and any redundant native update, as specified in Proposition 41.5. A later rational Add has its own input numerator/denominator widths, so the integer-menu envelope $W_L$ is not asserted for an unrestricted rational continuation. A long additional finite integer-menu run obtains an envelope with its actual larger tick/pulse counts. These bounds allow growing precision and storage; Theorem 48.1 forbids concluding uniformly bounded information memory from fixed $N$. $\square$

**Proposition 49.5 (finite cost of constructing a collision).** In Theorem 45.2 put $Q=(a+1)^\ell$ and use $W_\ell$ with menu bound $a$. A local construction can retain the $Q$ words and their evaluated endpoints in

$$
O\bigl(Q(NW_\ell+\ell\lceil\log_2(a+1)\rceil+1)+F\bigr)
$$

bits. It takes $O(QN(\ell+1))$ rational operations for the vectors and at most $O(Q^2N)$ coordinate comparisons to locate a matching pair. No source call is part of this construction.

Proof. Apply the same finite candidate evaluations and width bound as in Proposition 49.3, retaining rather than discarding their endpoints. Compare every distinct pair if necessary. Theorem 45.2 ensures one comparison succeeds. These deliberately conservative finite bounds record the cost of the asserted construction; they do not assert efficient search or require enacting the listed words. $\square$

## 50. Which history and which length the theorem recovers

**Proposition 50.1 (integer granularity is material).** The threshold of Theorem 45.2 cannot be extended merely by bounding the magnitudes of arbitrary rational pulses by a number smaller than $a$. For the original promised scalar source $T=(1/2)$, the acquired phase is $x_*=1/4$, $q(z)=2z-1$ and $a=2$. Its original rational Add interface admits the distinct equal-length words

$$
u=(1/4,0),\qquad v=(0,1/8),
$$

with the same endpoint $3/16$, despite all their pulse magnitudes being at most $1/4<a$.

Proof. The common baseline is $T^2x_*=1/16$. The pulse contribution of $u$ is $(1/2)(1/4)=1/8$ and that of $v$ is $1/8$. Their difference polynomial is $z/4-1/8=q(z)/8$. The integral quotient and the integral leading-coefficient obstruction used in Theorem 45.2 do not apply to this rational difference polynomial. These inputs are legal in the original interface but are outside the integer menu of Definition 44.1. $\square$

**Definition 50.2 (domain of the controlled inverse).** The inverse theorems in §§45–49 concern the actual consecutive pulse word from the acquired phase, its finite nonnegative integer alphabet and its retained earned length. Recovering an erased $L$ is not a supplied step, and the equal-length proof makes no assertion that such recovery is impossible in every individual source. The inverse does not identify Hold durations, extra Reads, arbitrary rational input journals, unrecorded diagnostic Ticks or an unauthenticated origin. It preserves the countermodels of §42 and the original passive meaning of §39. Exact access, fixed-law membership and the installed operations remain premises. No finite transcript is taken to install calibration, source-class membership, additional ports, permission or physical realization. Theorem 47.1 concerns identical current fields and common futures, while Proposition 47.2 explicitly distinguishes earlier emissions.

## 51. Mathematical supplier correspondence and the source-relative gain

**Definition 51.1 (supplied intermediate mathematics and its actual use).** The cited repository statements are used with their own hypotheses, through the following correspondences.

| Supplier | Correspondence inside these proofs |
| --- | --- |
| This volume, §§36–38 | Authentic $b=e_0$, actual $2N$-Tick acquisition, recovered native $T$, positive links, $0<T<I$, cyclic $K$ and $x_*=T^{2N}b$ are exactly the source here. Lemma 38.2 supplies the affine forced response. No new preparation or order service is substituted. |
| This volume, §§39–41 | $\mathcal O_N=K^{\mathsf T}$, the current-state inverse, adaptive action transport and acquisition resources are reused. The new Time is the finite pulse word; the old Time remains the paid passive scalar transcript on its original domain. |
| [FiniteHoKalmanBlocks](../../../D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.scribe.cs) | Its selected Hankel factorization and all-time realization algebra are prior suppliers to the earned law. Its arbitrary-candidate rank theorem supplies a lower dimension bound, not this integer-menu injectivity threshold or unknown-source membership. |
| [CoefficientDrivenJacobiCharacteristicPolynomial](../../../D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.scribe.cs) | The power basis is $T^jb$, the moment pairing is the actual Euclidean inner product, and coefficient multiplication is $T$ in that basis. Its private monicity/triangularity and positive-norm helpers and public characteristic-polynomial conclusion supply the §37 correspondence. The primitive $q$ here is a scalar multiple of that monic polynomial; neither irreducibility nor a trace-weight hypothesis is added. |
| [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) and its owning Scribe | Take state $\mathbb R^N$, output $\mathbb R$, evolution $T$, readout $b^{\mathsf T}$, horizon $N$. The supplied equivalence of zero kernel, full stacked rank and positive Gram is used through the actual invertible $K^{\mathsf T}$, with prospective source replies earned in Theorem 46.2. Generic observability is not a new conclusion. |
| Pinned Mathlib's primitive-divisibility lemma cited in Proposition 44.3 | Domain $\mathbb Z$, fraction field $\mathbb Q$, primitive divisor $q$ and arbitrary integral difference polynomial. This supplies the integral quotient even for reducible $q$, which is necessary both for the leading-coefficient obstruction and the exact lattice indices. |

These are intermediate suppliers inside the controlled-source proof. The additional inference is the exact leading-coefficient/menu threshold, its effective bounded same-length collision, its delayed first possible horizon, and the consequent actual pulse recovery/archive/precision distinction. It is a source-relative mathematical synthesis, not an attribution of generic Gauss, observability, finite coding or pigeonhole principles to this source.

**Definition 51.2 (literature and overlap boundary).** [Akiyama–Thuswaldner–Zaïmi, *Comments on the height reducing property II*, arXiv:1403.7480v1, Theorem 3](https://arxiv.org/html/1403.7480v1) supplies finite-automaton recognition of bounded-digit zero representations for an algebraic number with no unit-modulus conjugate. With one irreducible factor of $q$, one may take an eigenvalue as its algebraic number and the difference digits as its bounded alphabet; all conjugates of that eigenvalue are among the roots of $q$ and lie in $(0,1)$. The theorem concerns zero representations and does not install this acquired native path, an actual pulse experiment or the retained phase. For reducible $q$, a zero at only one chosen root does not imply annihilation of the cyclic vector. Proposition 44.3 requires divisibility by the whole $q$. The primitive-divisibility, bounded-region and finite-index argument of §45 treats that whole polynomial directly and supplies its stated length bound. Neither finite-automaton zero recognition nor number-system terminology is claimed as new here.

The [Predictive Waves volume, Definitions 4.1 and Theorems 4.2–4.4](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md) assumes cross-inner-product conservation for an isometric recursion; its positive-metric criterion requires unit-modulus eigenvalues. The present native $T$ has all eigenvalues strictly between zero and one, so no positive metric turns its Tick into that isometry. Its Theorem 6.4's hidden-leaf memory is a continuous forced equation, not the finite integer pulse word considered here. The retained joint reference and growing-record requirements of its Definition 12.1 are compatible disciplines, not a supplier of the menu threshold.

[Sharp Task Retained Environment Memory, Theorem 24.1](RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md) uses its specified isometry $B:\mathbb C^3\to\mathbb C^5$, actual full-space acquisition operators, complex-linear CPTP map, immediate/one-step effects and raw depth-two effects with only the first acquisition label erased. Its conclusion is a uniform diamond-norm stability estimate relative to $\operatorname{Ad}_B$. No CPTP map, qutrit input family or those effects occur in Definitions 44.1–44.2. Its partial erasure is not an equality of these native rational pulse endpoints. There is no source transport making that estimate a proof of this threshold, and no quantum stability conclusion is inferred here.

**Definition 51.3 (remaining mathematical scope).** The recovered structure in this continuation is the original acquired path, its actual field, its literal root observations and predictive memory, with a sharply delimited new chronology task. The all-length inverse is conditional on the nonnegative integer menu bound $H<a$ and the retained earned length; outside that menu range the equal-length obstruction is exact. The original arbitrary rational controlled-journal failure, passive-domain claims and initialization remain unchanged. No conclusion here settles an original fixed-$G_{\rm gc}$, original-$Q$ or parked-consumer obligation, identifies unknown call rights, proves a universal $\alpha/\beta$ reduction or completes an all-source four-expression recovery theorem. Deriving physical laws or authenticating a physical device is not a premise-free consequence of these conditional digital-source theorems.

## 追加锚（本行以下为增补区）

## 52. The authentic acquired phase separates every integer pulse length

**Definition 52.1 (the original endpoint without a supplied length).** Keep precisely Definitions 36.1–36.2 and the actual acquisition of Theorem 37.2. Write $b=e_0$, $K=[b,Tb,\ldots,T^{N-1}b]$, $\mathcal O_N=K^{\mathsf T}$, and $x_*=T^{2N}b$. Use Definition 44.2's primitive integer law $q$, its positive leading coefficient $a\ge2$, and the monic rational law $\bar q=q/a$. A finite signed integer word $u=(u_0,\ldots,u_{L-1})\in\mathbb Z^L$ means the same actual consecutive actions as in Definition 44.1: for each symbol, Tick; Add$(u_i)$; Read. In particular a zero symbol still executes all three commands. The native endpoint is

$$
X(u)=T^{L+2N}b+\sum_{i=0}^{L-1}u_iT^{L-1-i}b.
\tag{52.1}
$$

The empty word has $X(\varepsilon)=x_*$. Length is part of the mathematical finite-list type, but a separately retained old length is not an input to any inverse below. The origin, root binding, earned law, installed menu, exact access, successful serialization and backing remain those of §§36–41. No change to preparation or source class accompanies this removal of an input.

For a word $u$ define its integer endpoint polynomial

$$
A_u(z)=z^{L+2N}+\sum_{i=0}^{L-1}u_i z^{L-1-i},
\qquad X(u)=A_u(T)b.
\tag{52.2}
$$

The leading term represents the evolution of the actual original unit preparation through acquisition and the pulses. It is not an extra prepared marker or a source operation.

**Lemma 52.2 (the integral annihilator ideal and its leading coefficients).** For every $P\in\mathbb Z[z]$,

$$
P(T)b=0\quad\Longleftrightarrow\quad
P=qS\text{ for some }S\in\mathbb Z[z].
\tag{52.3}
$$

Consequently every nonzero integral annihilator of $b$ has leading coefficient divisible by $a$; in particular there is no monic integral annihilator.

Proof. This is the arbitrary-polynomial argument of Proposition 44.3: divide over $\mathbb Q$ by $\bar q$; the remainder has degree below $N$ and vanishes on $b$, so independence of $b,Tb,\ldots,T^{N-1}b$ makes it zero. Gauss's primitive-divisibility lemma then gives an integral quotient by $q$. Conversely $q(T)=0$. For nonzero $S$, the leading coefficient of $qS$ is $a$ times the nonzero integral leading coefficient of $S$. Since $a\ge2$, it cannot be one. This uses the whole earned polynomial, with no irreducibility premise or selection of one eigenvalue. $\square$

**Theorem 52.3 (length separation for arbitrary signed integer words).** For every acquired source of Definition 52.1, all $L,M\ge0$, and all $u\in\mathbb Z^L$, $v\in\mathbb Z^M$,

$$
X(u)=X(v)\quad\Longrightarrow\quad L=M.
\tag{52.4}
$$

There is no bound on the magnitudes or signs of the symbols. The assertion includes comparison with the empty word.

Proof. Suppose, by exchanging the words if necessary, that $L>M$. The polynomial $A_u-A_v$ is monic of degree $L+2N$. Indeed, the other preparation term has degree $M+2N<L+2N$, and every pulse term has degree at most $L-1<L+2N$. Thus nothing cancels its leading coefficient one, including when $M=0$. Equality of the native endpoints would make this monic integer polynomial annihilate $b$, contrary to Lemma 52.2. Hence unequal lengths are impossible. $\square$

The theorem separates the length strata of the actual affine endpoints $X(u)$, not those of the forced terms $E_L(u)$ alone. For example $E_L(0,\ldots,0)=0$ at every length. Subtracting the preparation term before length has been recovered would discard exactly the distinction used in the proof. Neither monotonicity of controlled root values nor a special sign pattern of the pulses is assumed.

## 53. The sharp menu threshold on the disjoint union of lengths

**Theorem 53.1 (complete finite-word recovery criterion without length advice).** Fix any acquired original source and integer $H\ge0$. On the disjoint union

$$
\mathcal U_H=\coprod_{L\ge0}\{0,\ldots,H\}^L,
\tag{53.1}
$$

the native endpoint map $u\mapsto X(u)$ is injective if and only if $H<a$.

Proof. If two endpoints agree, Theorem 52.3 first gives equal lengths. For $H<a$, Theorem 45.2 then gives equal words, since their common preparation terms cancel and their forced endpoints agree. Conversely, for $H\ge a$ reuse exactly the equal-length collision supplier of Theorem 45.2. With its computed $R,C$, it constructs distinct words $U,V\in\{0,\ldots,a\}^{\ell}$, where $\ell=N+aC$ suffices, with $E_\ell(U)=E_\ell(V)$. Adding the same $T^\ell x_*$ gives $X(U)=X(V)$. These words lie in $\mathcal U_H$. No new collision hypothesis or irreducible factor is substituted. $\square$

**Corollary 53.2 (binary recovery and the actual failure boundary).** Every acquired original source admits complete endpoint recovery of every finite binary pulse word, including its length, because $1<a$. The zero-only menu is also injective across all finite lengths. If $H\ge a$, the length remains recoverable as a function of the endpoint on its integer image, but the full word is not: the obstruction is already within a single length stratum. The short-horizon conclusions of Corollary 45.3 remain exact: no same-length collision at $L\le N$, and one at $L=N+1$ exactly when $H\ge h$, where $h=\max_j|q_j|$.

Proof. Apply Theorem 53.1 for $H=1$ and $H=0$, and Theorem 52.3 for length alone. The supplied equal-length conclusions and collisions are unchanged by removing length advice. $\square$

**Proposition 53.3 (limits imposed by integer granularity, origin and outputs).** The conclusions above do not extend to arbitrary rational pulse histories in the original legal menu. For the original one-cell source $T=(1/2)$, $x_*=1/4$, the empty word and the one-symbol rational word $(1/8)$ have the same native endpoint. Moreover, the distinct equal-length words in Proposition 50.1 still collide. Neither a bounded rational amplitude below $a$ nor knowledge of the earned law repairs these failures.

Proof. The nonempty endpoint is $(1/2)(1/4)+1/8=1/4$. This is a legal Tick; Add$(1/8)$; Read, with Tick reply $1/8$, Add acknowledgement and final Read $1/4$. It is not the empty command/output sequence. Proposition 50.1 supplies the equal-length collision within the same promised scalar source. In both examples rational difference polynomials need not have integral quotients of the kind used in Lemma 52.2. $\square$

The authentic origin is also material: at a different preparation $x=0$, zero pulse words of all lengths have endpoint zero. This is Counterexample 42.4's excluded origin, not a counterexample to Theorem 52.3. Likewise insertion of Read calls or Hold intervals changes a complete journal without changing the field. The current theorem recovers the specified consecutive integer pulse word, not those insertions, wall time or arbitrary rational journals. For $H\ge a$, Theorem 47.1's equal-field block family still has identical common future behavior, while Proposition 47.2 still recovers each symbol from its retained pair of earlier scalar outputs. No archive is assumed destroyed: the inverse question specifies its inputs, and any coexisting distinguishing archive remains additional information.

## 54. An exact local inverse that receives no old length

**Definition 54.1 (the length-first search).** The numerical inputs are the earned $N,T$, the actual acquired origin $x_*=T^{2N}b$, the task menu bound $H<a$, and a rational vector $x$ promised to lie in $X(\mathcal U_H)$. No old length, old word, source response oracle or archive is an input. Retain a scratch length $l$, initially zero. At this length enumerate the finite set $\{0,\ldots,H\}^l$ in lexicographic order, including its sole empty candidate at $l=0$. For each candidate $c$, copy $x_*$ to a scratch vector and execute locally, in chronological order,

$$
v\longmapsto Tv+c_i b.
\tag{54.1}
$$

Compare the resulting vector with $x$ by exact rational equality. On a match output $(l,c)$ and stop; after an unsuccessful finite stratum increment $l$. The scratch length is a search variable built by this computation, not a supplied count of source events. None of these candidate calculations calls Tick or Add on the specimen.

**Theorem 54.2 (termination and uniqueness on the actual image).** Definition 54.1 terminates on every promised input and returns exactly its actual pulse word and length. It uses no further source call and can run while the original source is held.

Proof. Write the actual word as $u$ and its mathematical length as $L$. Each stratum below $L$ is finite, and Theorem 52.3 excludes every candidate there. The finite stratum at $L$ contains $u$; its simulation is (52.1), so a match is reached. Theorem 53.1 excludes any other matching word. At $L=0$ the first candidate succeeds. Finite exact rational arithmetic and comparisons implement every step, without an a priori bound on $L$ or its operand widths. On vectors outside the promised image the search need not halt; a total image-recognition algorithm is not asserted. $\square$

**Proposition 54.3 (effective length recovery on the whole signed integer image).** Even without a finite digit menu, the earned law and a promised endpoint of some finite signed integer word effectively determine its length. This does not make the signed word unique.

Proof. At successive integers $r=0,1,2,\ldots$, examine all words of lengths at most $r$ with entries in $\{-r,\ldots,r\}$, simulating (54.1), and stop at a matching endpoint. Each stage is finite. If the actual word has length $L$ and maximum absolute entry $J$ (take $J=0$ for the empty word), stage $r\ge\max(L,J)$ includes it. Thus some match occurs, and Theorem 52.3 makes the length of every match equal to $L$. There can be distinct matching words at that same length; for example the reverse coefficient list of $q$ and the all-zero list, both of length $N+1$, have the same forced endpoint. The proposition returns a length and one witness, not a unique signed history. $\square$

The finite-menu consumer below uses Definition 54.1. The signed search is only a length procedure with its own finite, potentially much larger work; no finite-menu cost bound is assigned to its unbounded-height enumeration.

## 55. Four expressions with the old counter removed

**Definition 55.1 (one domain and independent exposed data).** Fix the original acquired installation, its earned law and authentic origin, and an integer task menu $0\le H<a$. The domain consists of all completed consecutive pulse cuts $X(u)$ for $u\in\mathcal U_H$. The shared numerical context is $(N,T,q,\mu,x_*,H)$, with redundant components optionally computed from the earned law as in §§37–40. It contains no old $L$ or old pulse record. Define the four expressions by their own data:

| Expression | Exposed data and meaning |
| --- | --- |
| Space | The actual rooted weighted path and present native cell field $(T,X(u))$, with cells identified by their native rooted distances. |
| Time | The finite ordered actual input list $u$, including zero symbols; its list structure has its own length. It is not a list of Hold durations or all commands ever issued. |
| Boundary | The same literal callable root service. Its acquired numerical window is $z_j=b^{\mathsf T}T^jX(u)$ for $0\le j<N$, obtained by one actual Read and $N-1$ returning Ticks. |
| Memory | The earned recurrence and initial impulse values, and the current predictive vector $w=\mathcal O_NX(u)$. Its entries are the next $N$ autonomous root predictions, not stored old symbols or a stored old pulse count. |

The installed source handle, rights, authentic origin/class assurance, serialization, controller and backing are retained separately from these numerical data. Boundary as an actual capability includes its real binding and permissions; a computed vector of predicted replies is only its numerical expression. An acquired boundary window has a named starting cut and its known diagnostic protocol, rather than a supplied count of earlier pulses.

**Theorem 55.2 (effective recovery and agreeing routes).** On Definition 55.1's actual images, Space, Time and numerical Memory effectively determine one another without an old length input. The numerical Boundary window determines those same data. Conversely each of the other numerical expressions computes exactly that window's values. Every composition of these recovery maps agrees with the direct map.

Proof. Time computes (52.1), using its own finite list, and then $w=\mathcal O_NX(u)$. Space computes this same $w$. Memory recovers $X(u)=\mathcal O_N^{-1}w$ by the earned invertible observation matrix. The Boundary window satisfies $z=\mathcal O_NX(u)$ and uses the identical inverse. Apply Definition 54.1 and Theorem 54.2 to the recovered field to obtain the unique actual word and its length. All these maps therefore factor through the same $(T,X(u),u)$, proving route agreement. Conversely multiplication by the fixed $\mathcal O_N$ computes the numerical window from the field. It does not acquire its observations, advance the source, restore a past cut or create a missing capability. $\square$

**Proposition 55.3 (pulse dynamics and every declared output).** At a pulse cut, write $x=X(u)$, $w=\mathcal O_Nx$, and let $v\in\{0,\ldots,H\}$ be the next actually supplied symbol. The actual pulse and its predictive implementation are

$$
\begin{aligned}
x^{\rm tick}&=Tx,&\quad \tau&=b^{\mathsf T}Tx,\\
x^+&=Tx+vb,& y&=b^{\mathsf T}Tx+v,\\
w^{\rm tick}_j&=w_{j+1}\ (j<N-1),&
w^{\rm tick}_{N-1}&=-\sum_{j<N}(q_j/a)w_j,\\
w^+_j&=w^{\rm tick}_j+v\mu_j.&&
\end{aligned}
\tag{55.1}
$$

Tick emits $\tau$ after its update, Add emits its fixed acknowledgement, and Read emits $y$. Hold, if called, emits its fixed acknowledgement and preserves the field. If the installed Add also declares a post-Add scalar, it is the same $y$ and is an additional output. The inverse at the new pulse cut returns exactly $u$ followed by $v$, without receiving its length separately. The recovered word and earned origin also compute the complete scalar replies and fixed acknowledgements of every original pulse.

Proof. These are the actual service semantics and Definition 40.1's all-field predictive identities, with $\bar q=q/a$. The last formula uses $(\mathcal O_Nb)_j=m_j=\mu_j$ and $\mu_0=1$. Also $X(uv)=TX(u)+vb$ by (52.1). Theorem 53.1 supplies the unique word at this new endpoint; hence inverse and append agree. Applying $\mathcal O_N$ gives the same update along the Space, Boundary-numerical and Memory routes. None of the separate pulse outputs is suppressed by calling the pulse one alphabet symbol. Starting the local recurrence at $x_*$ and applying the recovered list reproduces every intermediate $x_i$, hence each $\tau_i$, acknowledgement and $y_i$ by induction. These reconstructed numerical replies agree with the actual emitted values; the computation does not acquire their original observation provenance or identify unrecorded extra commands. $\square$

## 56. Actual endpoint acquisition and continued service at the advanced cut

**Theorem 56.1 (same-specimen no-length recovery and synchronized installation).** After any actual word in Definition 55.1, the original root service acquires its endpoint and recovers its word and length with exactly $N$ new scalar replies and $N-1$ new Ticks, followed by finite local decoding during Hold. At completion the installed predictor represents the actual specimen at its true advanced cut, not the historical pulse endpoint.

Proof. Apply exactly Theorem 46.2's observation protocol: one Read at the pulse endpoint, then $N-1$ actual returning Ticks with no Add, then Hold. The received values satisfy

$$
z=\mathcal O_Nx_{\rm hist},\qquad
x_{\rm hist}=X(u),\qquad
x_{\rm now}=T^{N-1}x_{\rm hist}.
\tag{56.1}
$$

Compute $x_{\rm hist}=\mathcal O_N^{-1}z$ and use Theorem 54.2 to recover $u,L$ without any supplied old count. During the held interval initialize and commit

$$
\widehat x=x_{\rm now}=T^{N-1}x_{\rm hist},\qquad
w_{\rm now}=\mathcal O_Nx_{\rm now}.
\tag{56.2}
$$

No source Tick occurs during these local computations. The actual state is consequently the one in (56.2) when the next call is exposed. For $N=1$ there is no diagnostic Tick and the historical and current fields coincide. This protocol uses the already acquired law and its root binding; it neither rediscovers the law nor obtains a new preparation, port or right. $\square$

**Proposition 56.2 (diagnostic chronology is not a pulse journal).** The recovered $L$ counts only the original consecutive pulse actions. The specimen in Theorem 56.1 has undergone $2N+L+N-1$ actual Ticks from its original unit preparation. Its $N-1$ diagnostic Ticks have not been rolled back. Numerically,

$$
x_{\rm now}=X\bigl(u\,0^{N-1}\bigr),
\tag{56.3}
$$

but the diagnostic command/output suffix is not the actual pulse suffix $0^{N-1}$.

Proof. Applying Tick $N-1$ times multiplies (52.1) by $T^{N-1}$, which gives (56.3). A zero pulse would additionally issue Add$(0)$ and Read after each Tick, with their acknowledgement and scalar output. The diagnostic protocol issues neither of those after each Tick; it has the one initial Read and the final Hold. Thus the equality is an equality of native fields, not of complete histories or their emissions. The historical field in (56.1), recovered from the acquired window with its stated starting cut, is the input to the word inverse. Applying that inverse instead to the advanced field would recover the numerical word $u0^{N-1}$, whose extra symbols cannot be called actual executed pulses. $\square$

**Theorem 56.3 (complete finite common adaptive service).** Retain the original binding, legal rights and backing after Theorem 56.1. For every finite common adaptive continuation in the original installed Read/Tick/Hold/Add menu, including arbitrary authorized rational Add inputs, the predictor returns every declared output exactly and stays synchronized with the complete actual native field at each committed cut.

Proof. Initialization is (56.2). Theorem 40.2 applies to this rational current field and its predictive image; its invariant does not require a passive or integer-word history. Explicitly Read and Hold preserve the field, Tick uses the shift/recurrence in (55.1) and emits its new root, and Add$(r)$ replaces $\widehat x$ by $\widehat x+rb$ and every $w_j$ by $w_j+r\mu_j$, emitting the installed acknowledgement and optional post-Add scalar. These identities preserve $\widehat x=x_{\rm actual}$ and $w=\mathcal O_Nx_{\rm actual}$. Each local commit completes before exposing the next call. Induction on the continuation gives equal preceding outputs, hence identical adaptive choices of next command, rational input and stopping decision. A common random tape is included pathwise. This is the existing complete-action invariant initialized at the actual advanced cut, not an assertion that a history inverse remains valid on every controlled field. $\square$

Theorem 55.3's no-length append law concerns consecutive pulses from $x_*$. After the diagnostic suffix or arbitrary later rational controls, continued prediction uses (56.2), while a new history-inversion claim must establish its own original-domain correspondence. Knowing an arbitrary new starting field alone supplies the same-length affine cancellation, but not Theorem 52.3's monic preparation term. No unknown-length inverse for all blocks from every rational starting field is inferred. In particular the rational and journal counterexamples of §§42 and 53 remain in force.

## 57. An attained simultaneous resource account without the old input

**Definition 57.1 (width and candidate quantities on the actual run).** Use Convention 41.1 and Definition 49.1's acquired-source quantities $B,D,F$, including the fixed matrices, $x_*,s=(I-T)^{-1}b$ and their actual construction widths. Use Proposition 41.3's acquisition width envelope $U$. For the actual word length $L$ define, for analysis rather than as decoder advice,

$$
\begin{aligned}
S_L&=\sum_{l=0}^{L}(H+1)^l,\qquad d_H=\lceil\log_2(H+1)\rceil,\\
W_L&=1+F+(L+3N)\lceil\log_2(D+1)\rceil
 +\lceil\log_2(H+2)\rceil+\lceil\log_2(L+2)\rceil,\\
V_L&=\max(U,W_L).
\end{aligned}
\tag{57.1}
$$

All counters and storage expand as needed during search. These after-the-fact envelopes need not be known at entry. For $H=0$, $S_L=L+1$; for $H\ge1$, it is the stated finite geometric sum. No exponential candidate table is retained by Definition 54.1.

**Proposition 57.2 (same-run source operations and complete traffic).** One realization is the original acquisition, the $L$ original pulse actions, and Theorem 56.1's diagnostic acquisition and held decoding. With Add returning its original fixed acknowledgement, its exact source counts before a later continuation are

| Source operation or emitted item | Count |
| --- | --- |
| Tick | $3N+L-1$ |
| Add | $L$ |
| Read | $L+2$ |
| Hold | $N+2$ |
| Scalar root replies | $3N+1+2L$ |
| Add acknowledgements | $L$ |
| Hold acknowledgements | $N+2$ |

The Hold count selects the $N+1$ acquisition Holds of Proposition 41.2 and the final diagnostic Hold; extra Holds are added when used. If Add also emits the optional post-Add root, add $L$ scalar outputs and their serialization. Every pulse input, command frame, acknowledgement, Read and returning-Tick scalar is part of the traffic.

Proof. These are Proposition 49.2's counts on the identical physical operation sequence, with the explicit selected Holds added. The decoder's additional length strata are local computations during the final Hold, so they add no source operation. A direct two-buffer source Tick performs $3N-2$ scalar multiplications and $2N-2$ additions. Thus these source totals multiply by $3N+L-1$, and the $L$ Adds contribute $L$ actual root additions. Read serialization and Hold/control work have their own actual costs. Fixed acknowledgements are not silently counted as rational scalars. $\square$

**Proposition 57.3 (attained exact arithmetic, precision and search work).** The same realization admits acquisition with Proposition 41.3's $O(N^4)$ rational operations and its $N-1$ promised-square root extractions, fixed matrix construction with a conservative additional $O(N^3)$ rational operations, and $O(N(L+N))$ rational operations for retained pulse updates and diagnostic synchronization. Definition 54.1's subsequent local decoding uses at most

$$
O\bigl(N(L+1)S_L+N^2+NL\bigr)
\tag{57.2}
$$

rational operations and coordinate comparisons. Its rational data and transient arithmetic products have width $O(W_L)$. The scalar/input numerical traffic is $O((N+L)W_L)$ bits, with literal command framing and all acknowledgements added. These are sufficient upper bounds for the specified algorithm, with no total-cost or decoder-optimality claim.

Proof. Reuse the acquisition and fixed-data calculations of §§41 and 49. In the local search every candidate has length $l\le L$, because a match is reached in the actual stratum. There are at most $S_L$ examined candidates. A fresh copy of $x_*$, $l$ sparse updates and one native-vector comparison cost $O(N(l+1))$ field operations and comparisons. Summing gives the first term in (57.2); observation inversion, propagation to the current cut and its predictive conversion fit the remaining terms. None is a source query.

For widths, all actual coordinates through the diagnostic suffix have denominators dividing $D^t$ at total Tick count $t\le L+3N-1$. Integer Adds introduce no new denominator. The same holds for every simulated candidate through its at most $l+2N\le L+2N$ ticks from unit preparation. Entrywise nonnegativity, $Ts=s-b\le s$, and $0\le u_i\le H$ give $0\le x_i\le(H+1)s$ for every actual intermediate field and every such candidate, exactly as in §§48–49. Thus their reduced numerator and denominator widths are $O(W_L)$. For the fixed-matrix observation inverse and synchronization use common denominators of the fixed entries, whose total encoding is bounded by $F$, together with the actual $D^t$; summing $N$ terms adds $O(\log(N+1))$. Multiplication before reduction and cross-products for equality change widths by only a constant factor. This also bounds each actual scalar reply, each locally predicted scalar and the recovered historical vector. The input symbols have $O(\log_2(H+2))$ bits each. Proposition 57.2 now gives the numerical traffic bound. The acquisition calculations retain their distinct width $O(U)$, included in $O(V_L)$ for a whole-run allowance.

Candidate creation, lexicographic increments, indexing and output copying are charged in addition to field operations. They admit the conservative bound $O((L+1)(d_H+\log_2(L+2)+1)S_L)$ bit steps by scanning each finite candidate and its binary counters. Exact arithmetic has a finite bit realization: school multiplication/division takes $O(V_L^2)$ per pair of $O(V_L)$-bit integers; Euclid needs $O(V_L)$ such divisions, giving the safe $O(V_L^3)$ allowance for reduction or a rational field operation. Binary-search integer square roots also fit $O(V_L^3)$. Consequently one sufficient local arithmetic/control bound is

$$
O\!\left(
 [N^4+N^3+N(L+N)+N(L+1)S_L]V_L^3
 +(L+1)(d_H+\log_2(L+2)+1)S_L
\right),
\tag{57.3}
$$

with actual installation, input/output handling and delivery work added. The source arithmetic of Proposition 57.2 adds at most $O(((3N+L-1)(5N-4)+L)V_L^3)$ bit steps using the same conservative rational-arithmetic implementation. All these estimates allow growing words; exact rationals have not been replaced by constant-width real registers. $\square$

**Proposition 57.4 (coexisting source, producer, observer and retained material).** A single layout attaining the preceding claims may retain all of the following simultaneously. Let $P_{\rm live}$ be the actual producer/input-provider store, $A_{\rm past}$ the actual retained pulse-input/reply archive beyond the separately listed stores, and $A_{\rm io}$ the actual extra simultaneous I/O and delivery copies. None is a decoder input.

| Coexisting component | Charge in this layout |
| --- | --- |
| Original source | $N$ cells, $N-1$ links, its $B$-bit coefficient store, and two state buffers of $O(NV_L)$ bits. |
| Earned observer data | The actual $2N+1$-value acquisition record of $O(N^2B+N)$ bits and the fixed $F$-bit law/matrix data. |
| Historical endpoint, current predictor and acquired window | A constant number of $N$-vectors, including distinct $x_{\rm hist}$ and $x_{\rm now}$, and $O(NV_L)$ bits. |
| Matrix/elimination and exact-arithmetic scratch | A conservative $O(N^2V_L)$ bits, sufficient also for acquisition scratch. |
| Local search and its result | One candidate, one evaluated vector, search length/cursors and one recovered output word, using $O(NV_L+L(d_H+1)+\log_2(L+2)+1)$ bits. |
| Producer/input provider | Its actual $P_{\rm live}$ bits and retained backing, even if it keeps the original input list or its own event count. |
| Additional archives and serialization copies | $A_{\rm past}+A_{\rm io}$ actual bits; distinct copies are added. |
| Installed access and control | Actual source reference, authentic preparation/class/root assurance, Read/Tick/Hold/Add rights, exclusive serial control, finite programs and their storage/service backing. |

The numerical/data stores have the simultaneous sufficient allowance

$$
O\bigl(F+N^2B+N^2V_L+L(d_H+1)+\log_2(L+2)
 +P_{\rm live}+A_{\rm past}+A_{\rm io}+1\bigr),
\tag{57.4}
$$

with the actual installed-access/control/backing charges added. A shared object is counted once only when it is actually shared; a retained second copy is additional.

Proof. Allocate the displayed finite stores on the same run and add their sizes. The decoder reads only its stated inputs, so a producer's retained list, a pulse-reply archive or a separate counter can coexist without being used to prove recovery. For a concrete attained producer, supply the actual finite word as its paid list, retain that list and its cursor, and issue its original pulses in order. Its list/cursor store is $O(L(d_H+1)+\log_2(L+2)+1)$ bits and is charged even after completion if retained. Reading its inputs, issuing its calls and retaining its data have their actual work costs. The decoder does not inspect this list or its cursor. Other producers have their own $P_{\rm live}$ and work charges. A decision to begin acquisition is invocation at an already completed pulse cut, not a new marker command or an algorithm inferring that a still-active producer has finished.

The source, producer, acquired records, predictor, scratch, old emissions, output and access installation coexist; selecting one component's peak from a different run cannot remove any of them. Proposition 57.3 and the width bound of §41 make the scratch allowance sufficient. Optional archives add their actual writing and retention costs. Later calls add their actual source arithmetic, predictor updates, input/output and retained-data costs as in Proposition 41.5 and Theorem 56.3. For arbitrary later rational Adds, use their actual new numerator/denominator widths; (57.1) is an integer-menu envelope for the stated run, not for all rational continuations. $\square$

**Corollary 57.5 (removing advice does not bound memory or precision).** For $1\le H<a$, Theorem 48.1's lower bound $\lceil L\log_2(H+1)\rceil$ for fixed-width distinguishability at length $L$ still applies, and Corollary 48.2's absence of a uniform positive exact-resolution margin still applies. Even for $H=0$, Theorem 52.3 supplies infinitely many distinct endpoints as length varies. Hence a finite number of cells, a finite predictive dimension and a finite decoder program do not supply a uniform finite information-memory bound for exact all-length recovery.

Proof. Restrict the new domain to any one old length stratum and reuse the supplied lower bounds. For $H=0$, the distinct fields are $T^{L+2N}b$ for all $L\ge0$ by Theorem 52.3; a fixed finite state set cannot distinguish infinitely many fields. The local decoder pays for its growing search counter, precision, scratch and output. Eliminating its old-length input establishes sufficiency with less advice; the present enumeration bound does not imply less total computation, storage or acquisition cost than every decoder receiving that advice. $\square$

## 58. Mathematical correspondence, covered suppliers and remaining bridges

**Correspondence 58.1 (the reused source and the additional inference).** The mathematical supplier relationships are exact:

| Supplier | Hypothesis correspondence and role |
| --- | --- |
| This volume, §§36–41 | The same rational positive-link path, $0<T<I$, authentic $b=e_0$, actual $2N$-Tick acquisition, native $T$, cyclic $K$, $x_*=T^{2N}b$, exact root binding and installed rights are retained. Native acquisition and the all-field predictive invariant are reused. |
| This volume, §§44–45 | The same primitive whole law $q$, $a\ge2$, Gauss integral quotient, sharp $H<a$ same-length criterion and effective $H\ge a$ collision are reused, including reducible laws and the original $R,C,\ell$. No collision or generic numeration theorem is presented as a new supplier. |
| This volume, §§46–49 | The same prospective root window, observation inverse, advanced cut, complete-output distinction, bounded-field information lower bound and width calculations are reused. The length-first decoder changes the candidate count from $(H+1)^L$ to at most $S_L$; its counter is computed locally. |
| [FiniteHoKalmanBlocks](../../../D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.lean) and its [Scribe](../../../Blueprint/D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.scribe.cs) | The selected Hankel realization algebra is already part of the earned-law supplier. Its explicit reference order and arbitrary-candidate rank lower bound are not source-order advice added here. |
| [CoefficientDrivenJacobiCharacteristicPolynomial](../../../D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.lean) and its [Scribe](../../../Blueprint/D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.scribe.cs) | Use $E=\mathbb R^N$, power basis $T^jb$, actual Euclidean moment pairing and multiplication by $T$. Its private monicity, upper-coordinate vanishing, positive squared norm and Jacobi subdiagonal/tridiagonal arguments, and public characteristic-polynomial results, are covered suppliers to §37. They are not missing lemmas re-created for this extension. |
| [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) and its [Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs) | State $\mathbb R^N$, output $\mathbb R$, update $T$, readout $b^{\mathsf T}$ and horizon $N$ give the stacked map $\mathcal O_N=K^{\mathsf T}$. Native triangularity supplies its full-rank hypothesis, while the literal Read/returning-Tick protocol supplies the actual window. |
| [Pinned Mathlib, GaussLemma](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Polynomial/GaussLemma.lean), `Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map` | Take $R=\mathbb Z$, $K=\mathbb Q$, primitive divisor $q$ and arbitrary integer dividend $P$. Its hypotheses require neither irreducibility of $q$ nor primitivity of $P$. It is the mature integral-divisibility step in Lemma 52.2. |

The additional `repo-derived` inference is that unequal-length authentic endpoints give a monic integral annihilator, excluded by the already earned $a\ge2$. Combining that inference with the supplied same-length theorem removes length advice on the entire finite-menu union. Sections 54–57 supply its terminating local consumer, actual observation/synchronization and simultaneous resource account. The role of the authentic preparation term is essential; no statement of external mathematical priority is made.

**Correspondence 58.2 (numeration and exact acquisition boundaries).** The following results have different exact source domains and retain their proved conclusions.

[Akiyama–Thuswaldner–Zaïmi, *Comments on the height reducing property II*, arXiv:1403.7480v1, Theorem 3](https://arxiv.org/html/1403.7480v1) already supplies finite-automaton recognition of bounded-digit zero representations at an algebraic number with no conjugate on the unit circle. This is `literature-attested` numeration mathematics, as credited in Definition 51.2. Applied to a root of an irreducible factor of the earned $q$, its hypothesis holds because all conjugates are among roots in $(0,1)$. However vanishing at one root need not annihilate the whole native cyclic vector when $q$ is reducible. The proof here uses the full annihilator ideal and does not infer a whole-source inverse from one spectral factor. No automaton construction, fast digit-extraction bound or optimal decoder is claimed.

[Signed Passive Clock, Theorems 2.1, 4.2 and 5.1](RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_PASSIVE_CLOCK.md) supplies its exact rooted interior-weight/cubic criterion, two-output passive phase recovery, native acquisition and true advanced-cut predictor for its signed contraction class. Its theorem concerns an authentic passive orbit and its declared two-value window; it is not the controlled integer word map (52.1). Here positivity and strict contraction are the original assumptions, not the larger signed class. The all-field predictive identities common to these sources are credited rather than counted as an additional discovery.

[Cyclic Leaf Boundary Ambiguity, §§1–7](RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_LEAF_BOUNDARY_AMBIGUITY.md) uses a supplied size, zero entrance, multiple leaf ports and acknowledgement-only Tick, with its separately installed extra read for positive identification. [Native Discovery and Retained Context, §§8–12](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DISCOVERY_AND_RETAINED_CONTEXT.md) uses immutable ordered labelled trees, all literal finite addresses, independent completions and selected terminal-measurability contracts; its fixed-source expected factor two is a paid tree-discovery result. Neither service is the original one-root returning-Tick path, and neither supplies its integer pulse-history inverse. Their conclusions are preserved without importing their extra ports, source caps, probability laws or retained-context assumptions.

[Unknown Field Native Startup, Theorems 3.1, 5.1, 6.2 and 7.3](RECURSIVE_RELATIONAL_OBSERVATION_UNKNOWN_FIELD_NATIVE_STARTUP.md) supplies capped-order unknown-field identification, paid actual unit preparation, entry into the original passive domain, and the stated uncapped deterministic obstruction. Its cap, startup pulse and later preparation are actual premises/operations of those theorems. They are not substituted for this volume's already authentic unit preparation and original acquisition. In particular this extension neither solves the uncapped unknown-field startup problem nor asserts that such startup was previously unsolved in the capped case.

[Arithmetic Acquisition Return, §§10–11](RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_ACQUISITION_RETURN.md) already proves positive modular closing on the actual original $R/G$ apparatus, its sharp paid-read return theorem, synchronized retained continuation and same-run costs. Its positive closing words restore the original modular arithmetic behavior while the integer source continues forward. No gap in that closing/return result is inferred from a different Scribe, and no part of it is claimed here. Its source, outputs, quotient and target are distinct from exact native integer pulse endpoints.

**Scope 58.3 (the remaining bridges).** Sections 50–51 delimit the earlier retained-length results; §§52–57 prove the additional no-length recovery on the explicitly stated integer domain. The retained-length theorems, their collisions and every other earlier scoped outcome stand unchanged. The newly recovered Time is exactly a finite consecutive integer pulse list from the authentic acquired cut. It is not a complete command/output journal, a noisy physical measurement theorem, a replacement for authentic preparation or an inferred permission system.

Native $\alpha/\beta$ generation remains a candidate foundation. Identifying its native constructors, legal operations, root observations, acquired origin and retained capability with the affine symbols $x\mapsto Tx$ and $x\mapsto Tx+b$ would require an explicit common realization, a proved state/operation/output correspondence and its resource account. Binary pulse injectivity alone supplies none of those bridges: the two binary choices are the paid Tick; Add$(0)$; Read and Tick; Add$(1)$; Read actions on this fixed path, not native $\alpha$ and $\beta$ constructors. The existing original-$G_{\rm gc}$, original-$Q$, parked-consumer, arbitrary-source geometry and full four-expression programme therefore retain their own obligations. Physical authentication, a universal reduction and completion of that programme require additional stated bridges.

## 追加锚（本行以下为增补区）

## 59. An earned later origin on the actual scalar source

**Definition 59.1 (scalar specialization and a later held cut).** Specialize Definitions 36.1–36.3 to the actual one-cell source $N=1$. Its unknown law is multiplication by a reduced rational

$$
\lambda=\frac rs,\qquad r,s\in\mathbb Z,\quad 1\le r<s,\quad \gcd(r,s)=1.
\tag{59.1}
$$

Theorem 37.2's actual experiment earns this law and leaves the cell at $\lambda^2$. Keep the original root-bound callable reference, exact rational ports, Read/Tick/Add/Hold rights, complete replies, serialization and sufficient finite backing. At a later settled cut, an actual Read followed by Hold earns the current reduced scalar

$$
v=\frac pq,\qquad p\in\mathbb Z,\quad q\ge1,\quad \gcd(|p|,q)=1.
\tag{59.2}
$$

For $v=0$ take $p=0,q=1$. The scalar is an observed actual origin for the subsequent experiment. The law alone does not assert this preparation. One explicit paid entrance, for any prescribed rational $v$, is to execute Add$(v-\lambda^2)$; Read; Hold after the original acquisition. The returned Read must equal $v$ by the actual Add law. An already reached later origin can instead be used after its own paid preparation and Read/Hold; its preceding costs remain attached to that run.

For a finite signed word $u=(u_0,\ldots,u_{L-1})\in\mathbb Z^L$, execute literally Tick; Add$(u_i)$; Read for each symbol, including zero. If $x_i$ is the state before symbol $i$, its first scalar reply is $\lambda x_i$, its Add reply is the installed fixed acknowledgement (with the updated scalar too if that version declares it), its final Read is $x_{i+1}=\lambda x_i+u_i$, and its successor is that actual scalar. Thus

$$
X_v(u)=\lambda^L v+\sum_{i=0}^{L-1}u_i\lambda^{L-1-i},\qquad X_v(\varnothing)=v.
\tag{59.3}
$$

The formula follows by induction on the actual actions. No tick, Add, reply or change of origin is implicit in this notation. The erased-past recovery input consists of $r,s,v$ and the current exact endpoint, with the fixed installed context; it contains neither $L$, $u$ nor their earlier reply archive.

## 60. Exact origin classification for signed pulse length

**Theorem 60.1 (all signed lengths, with a constructive converse).** For every actual scalar law and earned origin in Definition 59.1,

$$
\begin{split}
&\bigl[\ \forall L,M\ge0\ \forall u\in\mathbb Z^L\ \forall w\in\mathbb Z^M,
\quad X_v(u)=X_v(w)\Longrightarrow L=M\ \bigr]\\
&\hspace{45mm}\Longleftrightarrow\quad s\nmid p.
\end{split}
\tag{60.1}
$$

When $s\nmid p$, one prime divisor of $s$ gives an exact length formula on the whole signed image. When $s\mid p$, two unequal positive lengths, both at most $2q$, and signed words at those lengths with equal endpoints can be constructed by finite integer arithmetic. This is length separation, not signed-word uniqueness.

**Proof.** Suppose first that $s\nmid p$. Then $p\ne0$. Choose a prime $\ell\mid s$ with $\nu_\ell(p)<e:=\nu_\ell(s)$. For nonzero rationals, $\nu_\ell$ denotes numerator valuation minus denominator valuation, so $c:=\nu_\ell(v)<e$. Since $\ell\nmid r$, multiplication by $\lambda$ lowers this valuation by $e$. After the first such multiplication its valuation is $c-e<0$. Adding an integer cannot change a negative valuation: for nonzero integer $k$, $\nu_\ell(k)\ge0$, and the valuation of a sum of two nonzero terms of different valuations is their minimum. Adding zero leaves the term unchanged. In particular the resulting term cannot vanish. Induction gives, for every signed word, including the empty word,

$$
X_v(u)\ne0,\qquad \nu_\ell(X_v(u))=c-Le,
\qquad L=\frac{c-\nu_\ell(X_v(u))}{e}.
\tag{60.2}
$$

The $L=0$ assertion uses $v\ne0$ directly; the induction only uses the negative valuation after each Tick. Equal endpoints therefore have equal lengths. All valuations here are of nonzero rationals; no convention assigning a finite valuation to zero is used.

Now suppose $s\mid p$. Reducedness implies $\gcd(q,s)=1$. Put

$$
m=q,\qquad q_r=\gcd(q,r^m),\qquad q_0=q/q_r.
\tag{60.3}
$$

For each prime $\ell\mid r$, if $\ell^t\mid q$ then $t\le q=m$, and $r^m$ contains the entire $\ell$-primary part of $q$. Thus $q_r$ contains exactly the primary factors of $q$ whose primes divide $r$, $\gcd(q_r,q_0)=1$, and $\gcd(q_0,rs)=1$. If $q_0=1$, take $d=1$. Otherwise the unit $sr^{-1}$ modulo $q_0$ has a positive power equal to one with exponent at most $q_0$: among $q_0+1$ consecutive powers two coincide, and cancellation is valid for a unit. In either case choose

$$
1\le d\le q_0,\qquad s^d\equiv r^d\pmod {q_0},\qquad n=m+d.
\tag{60.4}
$$

Then $2\le n\le2q$. The factor $q_r$ divides $r^m$, while $q_0$ divides $s^d-r^d$. Consequently

$$
Z=\frac{r^m(s^d-r^d)p}{qs}\in\mathbb Z.
\tag{60.5}
$$

The additional division by $s$ is legitimate because $s\mid p$. Since $\gcd(r^{n-1},s^{n-1})=1$, extended Euclid constructs integers $A,B$ with

$$
Ar^{n-1}+Bs^{n-1}=Z.
\tag{60.6}
$$

Take the length-$m$ zero word and the length-$n$ word whose first and last symbols are $A,B$, with every intervening symbol zero. Formula (59.3) gives

$$
\begin{aligned}
X_v(A,0,\ldots,0,B)
 &=\lambda^n v+\frac{Z}{s^{n-1}}\\
 &=\lambda^n v+\frac{r^m(s^d-r^d)p}{q s^n}
 =\lambda^m v=X_v(0^m).
\end{aligned}
\tag{60.7}
$$

For $p=0$ this also works, with $A=B=0$. The lengths differ because $d\ge1$. Searching the finitely many exponents in (60.4), then applying Euclid, is a terminating construction. The two-symbol words $(s,0)$ and $(0,r)$ always have equal endpoints at the same length two, since their input contributions are both $r$. Thus even the favorable case in (60.1) does not give arbitrary signed-word uniqueness. $\square$

**Corollary 60.2 (what an endpoint collision erases).** At the equal endpoints of (60.7), fix the same actual law, root binding and currently enabled Read/Tick/Add/Hold rights. Every common finite adaptive continuation has identical complete future outputs and identical scalar successors. Therefore those present data and common future experiments cannot recover the erased signed length on the full bad-origin domain. Earlier emissions or a distinguishing archive are additional data to which this obstruction does not apply.

**Proof.** Read and Hold have identity successors; Read returns the same current scalar and Hold its fixed acknowledgement. Tick multiplies that same scalar by $\lambda$ and returns the same result. Add applies the same supplied rational and returns the same acknowledgement and any declared updated scalar. Induction on calls proves equality of outputs and successors. An adaptive selector that has received the same preceding replies makes the same next choice. The complete past outputs were not asserted equal in (60.7). $\square$

## 61. Direct bounded digits and the reciprocal converse

**Theorem 61.1 (later-origin bounded-word inverse).** Let $D_s=\{0,\ldots,s-1\}$ and suppose $s\nmid p$. On the promised image of all finite actual $D_s$ pulse words, $r,s,v$ and the exact endpoint determine the entire word and its length by a finite direct residue procedure, with one digit decision per symbol and no enumeration of candidate words.

**Proof.** Recover $L$ by (60.2). If $L=0$, return the empty word. For $L>0$ form

$$
A_0=\frac{s^Lx-r^Lv}{s}\in\mathbb Z,
\qquad R_i=r^{L-1-i}\quad(0\le i<L).
\tag{61.1}
$$

Every $R_i$ is invertible modulo $s$. With $[t]_s$ the unique representative in $D_s$, set successively

$$
d_i=[A_iR_i^{-1}]_s,\qquad
A_{i+1}=\frac{A_i-d_iR_i}{s}.
\tag{61.2}
$$

The input promise and (59.3) give the invariant

$$
A_i=\sum_{j=i}^{L-1}u_j r^{L-1-j}s^{j-i}.
\tag{61.3}
$$

Modulo $s$ it forces $d_i=u_i$, since both belong to $D_s$. Subtraction and division give the invariant for $i+1$. Hence all divisions are exact and $A_L=0$. Powers can be generated by repeated multiplication; after the initial $R_0$, the next $R_i$ is obtained by exact division by $r$ until $i=L-1$. No negative exponent is needed. This proves termination, uniqueness and correctness, including zero digits and leading or trailing zeros. $\square$

**Theorem 61.2 (bounded-word iff for reciprocal scalars).** If $r=1$, the endpoint map (59.3) is injective on the disjoint union $\coprod_{L\ge0}D_s^L$ if and only if $s\nmid p$. For $s\mid p$, unequal-length colliding $D_s$ words can be constructed finitely.

**Proof.** Sufficiency is Theorem 61.1. For necessity, $\gcd(q,s)=1$. Choose $d\ge1$ with $s^d\equiv1\pmod q$, using $d=1$ if $q=1$. Then

$$
C=\frac{(s^d-1)v}{s}\in\mathbb Z.
\tag{61.4}
$$

If $C\ge0$, put $j=0,k=C$. If $C<0$, put $j=\lceil -C/s^d\rceil$ and $k=C+s^dj$, so $0\le k<s^d$. In both cases $j,k\ge0$ and $k-s^dj=C$. Choose $m\ge1$ large enough that $j<s^m$ and $k<s^{m+d}$. Write $j$ and $k$ in base $s$, padding with zeros to exactly $m$ and $m+d$ digits, respectively, with the least significant digit first in chronological order. These are allowed actual pulse words. A length-$h$ such word encoding integer $J$ has endpoint $(v+sJ)/s^h$ by (59.3). Therefore

$$
\frac{v+sj}{s^m}=\frac{v+sk}{s^{m+d}},
\tag{61.5}
$$

because $sk-s^{d+1}j=(s^d-1)v$. The lengths are unequal. This covers negative and zero $v$ as well as positive $v$. $\square$

**Scope 61.3 (digit limitations).** For every coprime $1\le r<s$, Theorem 60.1 is an exact signed-length classification and Theorem 61.1 gives the stated sufficient bounded-digit recovery domain. The necessity direction of Theorem 61.2 is restricted to $r=1$. The signed collision construction (60.6) places no bound on $A,B$, and cannot be substituted as a bounded-digit converse for $r>1$. No such general converse is asserted. The equal-length signed collision in Theorem 60.1 also explains why the signed-length task is strictly less than recovery of a signed word.

## 62. Scalar views, actual continued use and simultaneous resources

**Definition 62.1 (independent scalar data and common context).** Fix the earned $(r,s,v)$, installed source and rights. On the actual $D_s$ image with $s\nmid p$, Space is the actual one-cell weighted geometry and current field $x$; Time is the actual finite consecutive pulse list; Boundary is a literal current root Read made at that endpoint; numerical Memory is the current autonomous prediction scalar $w=x$ with its earned multiplication law. These are the scalar specializations of field geometry, pulse chronology, root data and sufficient predictive state. The common context contains the earned origin but no old word or length. The callable reference and authority are retained outside these numerical data; a computed copy of a boundary value is not a newly observed reply. This geometry has one cell, and no higher-dimensional geometry is inferred from it.

**Proposition 62.2 (recovery, concatenation and the original service).** On that image the four numerical data determine one another, all routes agree, and pulse concatenation is compatible with the actual dynamics. At the held endpoint, the retained scalar predictor supplies every declared output and successor of every finite common adaptive continuation in the original legal menu, including rational Adds outside $D_s$ when authorized. History recovery after those general continuations is not asserted.

**Proof.** Space, Boundary and Memory each provide the same $x$; Theorem 61.1 recovers the unique Time. Conversely Time computes $x$ by (59.3), hence all three numerical data. Every route therefore passes through the same unique word and endpoint. For finite words $u,t$,

$$
X_v(ut)=\lambda^{|t|}X_v(u)+\sum_{i<|t|}t_i\lambda^{|t|-1-i},
\tag{62.1}
$$

by iterating the actual affine update; this also proves compatibility of all pulse composites on the inverse domain. For future primitive calls, the predictor keeps $w=x$. Read returns $w$ without change; Tick sets $w\leftarrow\lambda w$ and returns it; Add$(h)$ sets $w\leftarrow w+h$ and returns the installed fixed acknowledgement and the updated scalar if declared; Hold returns its fixed acknowledgement without change. The implementation forwards each enabled call through the actual retained handle, consumes its entire reply and return, and commits this same record update at the settled cut. The one-step identities and induction give the complete adaptive assertion. The model's finite frames, exact rational encoding and rights are retained, not inferred by the numerical calculation. $\square$

**Proposition 62.3 (one explicit paid run).** Use Definition 59.1's prescribed-$v$ entrance after the original acquisition, then $L$ actual pulses, then an endpoint Read and Hold, even if the last pulse already read that scalar. With fixed-acknowledgement Add, this one run has exactly

$$
\begin{array}{c|ccccc}
 &\mathrm{Tick}&\mathrm{Add}&\mathrm{Read}&\mathrm{Hold}&\text{mandatory scalar replies}\\ \hline
\text{total}&L+2&L+1&L+3&4&2L+5.
\end{array}
\tag{62.2}
$$

There are $L+5$ fixed Add/Hold acknowledgements. If Add also declares its updated scalar, there are $L+1$ additional scalar replies. All literal rational inputs, framing, call completion, delivery and cleanup have their actual costs. This run leaves the actual scalar at $X_v(u)$; its diagnostic Read/Hold causes no advance. An arbitrary earlier route to $v$ substitutes its own actual preparation costs for the displayed single Add entrance.

**Proof.** For $N=1$, Theorem 37.2 uses two returning Ticks, one Read, two Holds and three scalar replies. The prescribed entrance adds one Add, one Read and one Hold. Each pulse adds one Tick, one Add, one Read and two mandatory scalars. The last endpoint Read/Hold adds one of each and one scalar. Summing gives (62.2), including $L=0$; Add and Hold supply their fixed acknowledgements. $\square$

**Proposition 62.4 (actual scalar widths and work).** Use reduced binary rational encodings. Let $B$ bound the total numerical encoding size of $r,s,v$ and the prescribed preparation operand, with $B\ge1$. For $D_s$ pulses there is a direct implementation of Theorem 61.1 whose numerical intermediate widths obey

$$
W=O\bigl(B+(L+2)\log_2(s+1)+1\bigr).
\tag{62.3}
$$

It uses finitely many trial divisions to factor $s$ and select $\ell$, repeated exact divisions to compute (60.2), and $L$ residue decisions. A conservative sufficient bit-work bound, including ordinary Euclid and reduced rational arithmetic, is

$$
O\bigl((s+W+L+1)W^3\bigr).
\tag{62.4}
$$

An attained simultaneous numerical layout uses $O(B+W+L\log_2(s+1)+\log_2(L+2))$ bits for source scalar/law buffers, the scalar predictive record, arithmetic workspace, counters and the decoded word. Actual source preparation and its producer, any separately retained old input/reply archives, I/O copies, program/parser, reference/grants and finite backing are additional coexisting stores and work, charged once each. They are neither decoder advice nor bounded by its information payload.

**Proof.** After $i$ pulses the denominator divides $q s^i$, and $|x_i|\le |v|+(s-1)/(1-r/s)$. Thus numerator and denominator widths have the envelope (62.3). The powers in (61.1), the integers in (61.3), their products and Euclid coefficients have the same envelope up to an absolute constant. Trial factorization using candidate divisors at most $s$ takes at most $s$ tests with operands within this envelope. The valuations require at most $O(W)$ repeated divisions on the nonzero numerator and denominator. Powers, residue extraction and exact updates require $O(L+1)$ further arithmetic operations and Euclid calls, which can each be paid by a conservative $O(W^3)$ school arithmetic bound, including rational reduction. Retaining the output digits and one current collection of scalar arithmetic operands gives the claimed layout. One may retain and pay an additional producer/archive on the same run without reading it as decoder input. The estimate depends on the value $s$, not polynomially on its binary length. The signed collision construction can have length proportional to $q$ and very large digits; its work and stores pay those actual lengths and widths instead. For unbounded signed input words, their supplied magnitudes and resulting widths must likewise be paid. Neither (62.4) nor finite scalar dimension supplies a uniform finite-precision instrument or a total-performance optimum. $\square$

## 63. Computed coordinates for the acquired pulse lattices

**Definition 63.1 (the authentic arbitrary-order input).** Return to the actual rational path of Definitions 36.1–36.3 with arbitrary unknown finite $N\ge1$, positive links and $0<T<I$, authentic preparation $b=e_0$, and Theorem 37.2's executed acquisition. Retain its earned native $T$, cyclic matrix $K=[b,Tb,\ldots,T^{N-1}b]$, $M=K^{-1}TK$, $v_j=M^je_0$, and actual acquired origin $x_*=T^{2N}b$. Here $v_j$ denotes a vector, independently of the scalar origin $v$ in §§59–62. The primitive whole integer law is $q(z)=a z^N+\sum_{i<N}q_i z^i$, with $a\ge2$, and its monic rational law is $\bar q=q/a$. Neither irreducibility nor a selected spectral factor is assumed.

For $n\ge N$ use exactly Lemma 45.1's lattice

$$
\Lambda_n=\sum_{j<n}\mathbb Z v_j,\qquad
\Lambda_N=\mathbb Z^N.
\tag{63.1}
$$

The same lemma already supplies that $\Lambda_{n+1}/\Lambda_n$ is cyclic of exact order $a$, generated by $v_n$. This exact-order statement is an input from its full primitive-law proof, not an additional lattice-order theorem. The computational task here is to produce finite membership matrices and explicit residue maps and consume them at the actual acquired endpoint. All matrix entries and vectors below are rational or integer encodings computed from this earned input.

**Proposition 63.2 (one explicit extension step).** Starting with $C_N=I$, finite integer arithmetic constructs nonsingular integer matrices $C_n$ such that

$$
C_n\Lambda_n=\mathbb Z^N,\qquad
\Lambda_n=\{y\in\mathbb Q^N:C_ny\in\mathbb Z^N\}.
\tag{63.2}
$$

At each $n\ge N$, it also constructs a homomorphism

$$
\phi_n:\Lambda_{n+1}\longrightarrow\mathbb Z/a\mathbb Z,
\qquad \ker\phi_n=\Lambda_n,\qquad \phi_n(v_n)=1.
\tag{63.3}
$$

Membership is computed by exact rational matrix multiplication and integrality of all coordinates. Evaluation of $\phi_n$ on its declared domain is computed by one integer residue of an explicit rational linear form.

**Proof.** Suppose (63.2) holds at $n$. Exact order $a$ gives $a v_n\in\Lambda_n$, so

$$
t=a C_n v_n\in\mathbb Z^N\setminus\{0\}.
\tag{63.4}
$$

Nonvanishing follows because $T$, hence $M$, is invertible. Put $g=\gcd(|t_0|,\ldots,|t_{N-1}|)>0$. Construct an integer unimodular matrix $U$ with $Ut=g e_0$. For completeness, swap a nonzero coordinate into the first position and change its sign if necessary. If the current first entry and another entry are $R,S$, not both zero, Euclid gives $A R+B S=g'$, where $g'=\gcd(|R|,|S|)>0$. Apply on these two rows the integer matrix

$$
\begin{pmatrix}A&B\\-S/g'&R/g'\end{pmatrix}.
\tag{63.5}
$$

It has determinant one and sends $(R,S)^{\mathsf T}$ to $(g',0)^{\mathsf T}$. Skip pairs of zeros. Repeating over the other coordinates gives the asserted $U$, including $N=1$ by a possible sign change. Each operation has an integer inverse, so the product is unimodular.

The vector $C_n v_n=t/a$ has exact order $a$ modulo $\mathbb Z^N$, since $C_n$ is an isomorphism of the lattices in (63.2). After applying $U$ that order is the order of $g/a$ modulo $\mathbb Z$, namely $a/\gcd(g,a)$. Hence $\gcd(g,a)=1$. Therefore

$$
\begin{aligned}
U C_n\Lambda_{n+1}
 &=\mathbb Z^N+\mathbb Z(g/a)e_0
   =(a^{-1}\mathbb Z)\times\mathbb Z^{N-1},\\
C_{n+1}&=\operatorname{diag}(a,1,\ldots,1)U C_n.
\end{aligned}
\tag{63.6}
$$

The last matrix is nonsingular and integer, and maps $\Lambda_{n+1}$ onto $\mathbb Z^N$. Its full preimage of $\mathbb Z^N$ is precisely that lattice, since it is invertible over $\mathbb Q$. This proves (63.2) inductively.

Choose $h\in\mathbb Z$ by Euclid so that $hg\equiv1\pmod a$. For $y\in\Lambda_{n+1}$ define

$$
\phi_n(y)=\bigl[h a(U C_n y)_0\bigr]_a.
\tag{63.7}
$$

The expression inside the residue is an integer on this domain by (63.6). It is additive. Its value at $v_n$ is $[hg]_a=1$. Its zero condition is $a(U C_n y)_0\equiv0\pmod a$, since $h$ is a unit modulo $a$. Equivalently $(U C_n y)_0$ is an integer. All other coordinates already are integers by (63.6), so this condition is $UC_n y\in\mathbb Z^N$, or $y\in\Lambda_n$. This proves (63.3). In particular (63.7) is not a residue operation on an arbitrary rational outside its stated domain. The construction computes $v_{n+1}=Mv_n$, its integer row transformations and all denominators by ordinary finite arithmetic; it invokes no membership, basis or quotient oracle. $\square$

## 64. A lattice clock and direct digits without an old length

**Theorem 64.1 (computed clock on the entire signed image).** For every source of Definition 63.1, every $L\ge0$ and every actual signed integer pulse word $u\in\mathbb Z^L$, put $x=X(u)$ as in (52.1) and $z=K^{-1}x$. Then

$$
\min\{n\ge N:z\in\Lambda_n\}=L+2N+1.
\tag{64.1}
$$

Starting with $C_N$, Proposition 63.2's successive membership tests therefore recover $L$ without an old length, word or archive, using exactly $L+N+1$ extension steps and $L+N+2$ tests on this promised input. This computes the signed length already known to be unique by Theorem 52.3, with no candidate-word enumeration.

**Proof.** In power coordinates the actual endpoint identity is

$$
z=v_d+\sum_{j=0}^{L-1}p_jv_j,
\qquad d=L+2N,\qquad p_j=u_{L-1-j}.
\tag{64.2}
$$

The sum belongs to $\Lambda_d$, because every $j<L<d$. Exact order $a\ge2$ gives $v_d\notin\Lambda_d$. Thus $z\notin\Lambda_d$, but $z\in\Lambda_{d+1}$. Since the lattices increase, it belongs to none of the earlier lattices with index at least $N$. This proves (64.1), including $L=0$, when the sum is empty. Testing $N,N+1,\ldots,d+1$ uses $d+2-N=L+N+2$ tests and requires construction of $C_{N+1},\ldots,C_{d+1}$, exactly $d+1-N=L+N+1$ extensions. At each step the predicate is computed by (63.2). The analysis uses the actual $L$ only to count the run; the controller stops at its first successful membership test. $\square$

**Theorem 64.2 (direct bounded-menu consumer).** Fix an integer $0\le H<a$. From the earned source data and a rational endpoint promised to belong to $X(\coprod_{L\ge0}\{0,\ldots,H\}^L)$, the computed filtration and residues return the entire actual word and length. Besides the ascending membership tests of Theorem 64.1, the procedure makes exactly $L$ digit decisions and finitely many vector operations. It consumes the same inverse domain as Theorem 53.1.

**Proof.** Recover $L$ by Theorem 64.1, retain the matrices and residue forms already constructed, and form

$$
\rho=z-v_{L+2N}=\sum_{j<L}p_jv_j.
\tag{64.3}
$$

For $j=L-1,L-2,\ldots,N$, when this range is nonempty, the current residual is in $\Lambda_{j+1}$. Its coefficient $p_j$ is the unique representative in $\{0,\ldots,H\}$ of $\phi_j(\rho)$: the lower-index part is in $\Lambda_j$, and $\phi_j(v_j)=1$. Because $H<a$, two allowed coefficients cannot have the same residue modulo $a$. Compute the least nonnegative residue by integer division; the promise ensures that it is at most $H$. Use this value for $p_j$ and replace $\rho\leftarrow\rho-p_jv_j$. The residual then lies in $\Lambda_j$ with precisely its lower-index expansion, proving the descent invariant.

At its end, or immediately when $L\le N$, the residual is

$$
\rho=\sum_{j<\min(L,N)}p_je_j,
\tag{64.4}
$$

because $v_j=e_j$ for $j<N$. Its first $\min(L,N)$ coordinates give the remaining digits directly; all other coordinates are zero. Reverse their order to obtain the chronological word $u$. There are $\max(L-N,0)$ residue decisions and $\min(L,N)$ coordinate decisions, totaling $L$. For $L=0$, the residual is zero and the procedure returns the empty word. This proves termination and the exact answer without re-proving the supplied injectivity or collision threshold. $\square$

**Scope 64.3 (recognition and signed ambiguity).** The clock terminates on the full signed endpoint image; signed digits themselves can be ambiguous. The bounded consumer terminates on its promised image. For a general rational input, successive membership tests need not terminate. A successful membership test by itself is not a certificate of a legal history: its index could give a negative proposed length, and its residual could fail the allowed digit conditions. Theorems 64.1–64.2 are exact promised-domain inverses, not a total membership decision for their infinite image. At $H\ge a$, the supplied equal-length collisions remain, while the authentic signed length still has (64.1). No extension to arbitrary later vector origins is made by subtracting the original $v_{L+2N}$ without justification.

## 65. Literal boundary acquisition and the actual advanced predictor

**Definition 65.1 (one endpoint window on the same specimen).** After any actual pulse word on the authentic source, let $x_{\rm hist}=X(u)$ be its endpoint. Execute the original diagnostic of Theorem 56.1: Read once, perform $N-1$ returning Ticks, then Hold. The literal scalar list and the actual held field are

$$
\begin{aligned}
y&=(b^{\mathsf T}T^j x_{\rm hist})_{j=0}^{N-1}
   =\mathcal O_Nx_{\rm hist},\qquad \mathcal O_N=K^{\mathsf T},\\
x_{\rm now}&=T^{N-1}x_{\rm hist}.
\end{aligned}
\tag{65.1}
$$

The inverse $\mathcal O_N^{-1}$ and native $T$ are earned suppliers from §§37, 40 and 56. The decoder takes their finite encodings and this actually acquired $y$. It does not receive a full response oracle. It computes $x_{\rm hist}=\mathcal O_N^{-1}y$, then applies §§63–64 during the actual Hold. It installs its live record at $x_{\rm now}$ in (65.1). The diagnostic metadata says that exactly $N-1$ observation Ticks have occurred; it is independent of the erased $L$.

**Theorem 65.2 (installed lattice consumer and complete future service).** For each promised actual source, $0\le H<a$ and every finite actual allowed pulse word, Definition 65.1 followed by Theorem 64.2 recovers the original word and length and retains an exact predictor for the actual advanced specimen. It needs exactly $N$ new scalar replies and $N-1$ new Ticks, with no further source calls for the lattice arithmetic. Every finite common adaptive continuation in the original installed menu has its complete outputs and actual successors predicted exactly.

**Proof.** Native cyclicity gives $\mathcal O_N^{-1}$, so the paid list recovers the exact historical endpoint. This meets Theorem 64.2's authentic input promise. Its finite arithmetic terminates while Hold preserves the advanced actual field. Initialize the live predictive vector by

$$
w_j=b^{\mathsf T}T^j x_{\rm now}\quad(0\le j<N).
\tag{65.2}
$$

For the full menu, Read returns $w_0$ without changing the state. Tick uses the monic whole law:

$$
w'_j=w_{j+1}\ (j<N-1),\qquad
w'_{N-1}=-\sum_{i<N}\bar q_iw_i,
\tag{65.3}
$$

and returns $w'_0$. For $N=1$, (65.3) consists solely of its last formula. An authorized rational Add$(h)$ gives

$$
w'_j=w_j+h\mu_j,\qquad \mu_j=b^{\mathsf T}T^jb,
\tag{65.4}
$$

and returns the installed fixed acknowledgement, together with $w'_0$ if that Add version declares it. Hold returns its fixed acknowledgement and preserves $w$. These identities are the supplied all-field predictive invariant of Theorem 56.3, here initialized at (65.1). Indeed the next native states are $Tx$, $x+hb$, $x$, $x$ for Tick, Add, Read, Hold, respectively; multiplication by $\mathcal O_N$ gives (65.3)–(65.4). Thus $w=\mathcal O_Nx$ remains true for every rational current field, including after a future Add outside the decoding alphabet.

Retain and use the actual root-bound service reference, enabled rights, exact frame convention, serialization, reply/return and finite backing. The consumer forwards each admitted call there, consumes every declared output and the completed return, and commits the corresponding record update before the next settled cut. Numerical evaluation supplies predictions of these outputs; it is not an extra source read or a substitute handle. One-step equality and induction prove equality along any finite common adaptive choice of operations. This establishes actual continued use of the same advanced specimen, rather than merely computation of a historical predictor. $\square$

**Proposition 65.3 (the two cuts and diagnostic provenance).** At the returned held cut, Space and live Memory refer to $x_{\rm now}$; the stored Boundary list in (65.1) starts at $x_{\rm hist}$. Both endpoints are retained as distinct records if both are needed. There is no rollback. Numerically $x_{\rm now}=X(u0^{N-1})$, but the diagnostic suffix is not an actual zero-pulse suffix and is not part of the recovered pulse Time.

**Proof.** The zero-input affine updates multiply by $T$, giving the numerical identity. An actual zero pulse additionally executes Add$(0)$ and Read and has their complete outputs and returns; the diagnostic only executes the stated returning Ticks after its initial Read. Hence equality of numeric endpoints does not identify command lists or emitted outputs. Equation (65.1) gives the actual advance and determines which record the live invariant must use. $\square$

## 66. Independently meaningful expressions at the returned cut

**Definition 66.1 (the joint returned image).** Fix the earned authentic source, task bound $H<a$, original binding/rights and the diagnostic schedule of Definition 65.1. The domain consists exactly of returned held cuts after some finite actual $\{0,\ldots,H\}$ pulse list from $x_*$ and that diagnostic. Shared numerical context is the earned $(N,T,q,\mu,x_*,H)$ and the known diagnostic count $N-1$, without an old $L$ or pulse list. Define the expressions independently:

| Expression | Exposed numerical data and meaning |
| --- | --- |
| Space | The actual rooted weighted path and complete present native field $x_{\rm now}$, modulo root-preserving weighted coordinate identification |
| Time | The actual finite consecutive pulse list before the prescribed diagnostic, with that diagnostic distinguished by its fixed schedule |
| Boundary | The literal paid ordered $N$-value root window $y$ of (65.1), retained from its actual observation |
| Memory | The earned law and the live sufficient vector $(b^{\mathsf T}T^j x_{\rm now})_{j<N}$ of current autonomous root predictions |

The law/origin metadata is common context, not a hidden copy of Time. The retained callable handle, rights, actual record encodings and backing are additional resources attached to this service, not numerical coordinates manufactured by a view inverse. Source outputs may be copied into records with their ordinary copy cost; merely calculating their equal numeric values does not earn observation provenance.

**Theorem 66.2 (returned-cut recovery, routes and task kernel).** On Definition 66.1's exact actual image, each expression determines the other three numerical expressions, the original pulse length, the historical endpoint and the actual present endpoint. Every recovery route agrees. These data have exactly the same kernel as the complete current original continuation task on this fixed image. The maps respect pulse concatenation at historical pulse cuts and passage through the prescribed diagnostic. They also respect every finite legal primitive continuation for which the claimed initial and final view domains are met; intervening all-field prediction is always provided by Theorem 65.2.

**Proof.** From Boundary apply $\mathcal O_N^{-1}$ to get $x_{\rm hist}$, Theorem 64.2 to get Time, and $T^{N-1}$ to get actual Space and hence Memory. From Space invert $T^{N-1}$, which is possible because $T$ is positive definite, obtaining the historical endpoint and the same inverse. From Memory first use $\mathcal O_N^{-1}$ to get $x_{\rm now}$ and proceed as from Space. From Time use (52.1) for $x_{\rm hist}$, then (65.1)–(65.2) for all other numerical data. These are equalities on the same jointly realized process. A reconstructed numerical window is equal to the recorded window; its actual observation is the supplied diagnostic, not an additional conclusion about a computation. Every route factors through the unique original word and these two deterministic endpoints, proving route agreement.

Equal present fields give equal full future output/successor behavior by Theorem 65.2. Conversely if two present fields differ, their difference has nonzero image under invertible $\mathcal O_N$. Consequently Read followed by at most $N-1$ returning Ticks distinguishes a coordinate of that image, using the actual legal ports. Thus full continuation equivalence is exactly equality of $x_{\rm now}$. Invertible $T^{N-1}$ and Theorem 53.1 make this exactly equality of the original allowed pulse list on the declared image. This proves the kernel assertion without identifying complete old journals with current state outside that image.

For pulse dynamics, (59.3)'s vector analogue follows directly from the same affine updates:

$$
X(ut)=T^{|t|}X(u)+\sum_{i<|t|}t_iT^{|t|-1-i}b.
\tag{66.1}
$$

Applying the diagnostic after the concatenated word gives the actual present field $T^{N-1}X(ut)$. Transport through these equalities proves compatibility for formation of pulse lists followed by their diagnostic. This is not an instruction to append $t$ from the already advanced returned state and call its pulse list $ut$. For a primitive continuation starting at a returned cut, use the actual present field as its initial field, not $x_{\rm hist}$. Theorem 65.2 gives its actual successors and all outputs. Whenever the ending cut also meets Definition 66.1 with its specified original-origin history and diagnostic, the inverse just proved recovers that ending cut's unique data. Composition therefore agrees with the direct recovery there. No assertion that every primitive continuation remains in this inverse domain is needed. $\square$

## 67. Arithmetic counts and all actual coexisting material

**Proposition 67.1 (one path run and its literal traffic).** Realize Definition 63.1's original acquisition, $L$ actual pulses, Definition 65.1's diagnostic and held lattice decoding on one source. With fixed-acknowledgement Add the counts before a later continuation are exactly

$$
\begin{array}{c|ccccc}
 &\mathrm{Tick}&\mathrm{Add}&\mathrm{Read}&\mathrm{Hold}&\text{mandatory scalar replies}\\ \hline
\text{total}&3N+L-1&L&L+2&N+2&3N+2L+1.
\end{array}
\tag{67.1}
$$

There are $L+N+2$ fixed Add/Hold acknowledgements. If Add also returns its updated scalar, add $L$ scalar replies. No lattice step is a source primitive, and no reduction of these source counts relative to Proposition 57.2 is claimed.

**Proof.** The original acquisition has $2N$ Ticks, one Read, $N+1$ Holds and $2N+1$ scalar replies. The pulses add $L$ Ticks, $L$ Adds, $L$ Reads and $2L$ mandatory scalars. The diagnostic adds $N-1$ Ticks, one Read, one Hold and $N$ scalars. Summing proves (67.1), including $N=1$ and $L=0$. Every call pays its actual input encoding, framing, transmission, complete reply/return, record construction, delivery and cleanup in addition to this count. $\square$

**Proposition 67.2 (a fully computed local bill).** Let

$$
E=L+N+1.
\tag{67.2}
$$

One implementation retains all $C_n$, necessary residue forms and vectors constructed before the first successful test. Excluding Euclidean subroutines, the ascending construction, membership tests and descending decoder use $O(E N^3)$ integer/rational arithmetic operations. Lattice row reduction and modular inverses require at most $N E$ calls to extended Euclid. Ordinary gcd reductions within rational arithmetic are additional subroutines included in its width-dependent bit cost below. There are no oracle operations. The live table, vectors, output digits and numerical workspace have $O((E+1)N^2)$ integer/rational entries. These are counts in the actual $L$ and $N$, not a polynomial bound in the binary input size.

**Proof.** There are exactly $E$ extensions by Theorem 64.1. At one extension, compute $C_n v_n$ and $Mv_n$ with $O(N^2)$ rational operations. The row reduction (63.5) uses at most $N-1$ pairwise extended gcd calls, followed by one call for the inverse of $g$ modulo $a$, at most $N$ in all. Explicitly retaining and multiplying the row matrices and $C_n$ can conservatively be done in $O(N^3)$ further arithmetic operations; applying $C_n$ to $z$ costs $O(N^2)$. Each of the $L$ digit decisions and vector subtractions costs $O(N^2)$ or less from the saved forms and vectors. Initial and final fixed-size matrix applications are within this bound. The table has $E+1$ matrices of $N^2$ entries and at most $O(E N)$ vector/form entries; the output and remaining workspace fit the same bound. The case $N=1$ uses only sign normalization and the one modular-inverse Euclid call per extension. No candidate word is generated or tested. $\square$

**Proposition 67.3 (width-dependent bit work and one simultaneous layout).** Let $W\ge1$ be the maximum actual signed-integer bit width on this implementation, including numerators, denominators, unreduced products and sums, Euclid inputs/intermediates/coefficients, row and membership calculations, digits and counters. Let $S_{\rm fixed}$ be the actual numeric storage for the already acquired native law, moments, fixed matrices/inverses, literal boundary record and the live/historical/predictive vectors, and $S_{\rm source}$ the source's actual law and active buffers. One conservative additional decoding bound is

$$
\text{bit work}=O(E N^3W^3),\qquad
\text{table/output/workspace bits}=O((E+1)N^2W).
\tag{67.3}
$$

An attained simultaneous total-space account at the held decoding cut is

$$
\begin{split}
S_{\rm source}+S_{\rm fixed}
 +O((E+1)N^2W)
 +P_{\rm live}+A_{\rm past}+A_{\rm io}+S_{\rm access}.
\end{split}
\tag{67.4}
$$

Here $P_{\rm live}$ is actual producer/input-provider material, $A_{\rm past}$ separately retained input/reply archives, $A_{\rm io}$ extra simultaneous I/O and delivery copies, and $S_{\rm access}$ program/parser, actual references, grants and other finite backing. These denote disjoint charged stores; shared material is counted once, and no archive or producer record is consulted by the decoder. Their arbitrary encodings have no bound inferred from the numerical estimate.

**Proof.** School integer addition, multiplication and division on operands/intermediates of width at most $W$ have a conservative $O(W^2)$ cost; Euclid and rational reduction have a conservative $O(W^3)$ cost. Paying this bound for the arithmetic and Euclid calls in Proposition 67.2 proves (67.3). Its entry count times actual width proves its storage estimate. Retain the source's two field buffers, acquired fixed matrices, current native/predictive vectors, literal boundary record and historical endpoint, while the same observer holds the lattice tables and decoded list. Retain any actual producer, old archive, I/O copies and access material alongside them. This is a single layout realizing the sum (67.4), rather than unrelated minima of different runs.

Source execution and acquisition are additional work: the existing tridiagonal Tick uses $3N-2$ products and $2N-2$ additions, Add changes the root, and all actual operands pay their widths. Theorem 37.2's native acquisition can use Proposition 41.3's $O(N^4)$ rational operations and $N-1$ promised rational-square extractions; fixed inverses use an additional $O(N^3)$ rational operations. Retained source/predictor updates for the pulses and diagnostic use the existing $O(N(L+N))$ rational-operation implementation. Each square extraction, I/O operation, source-creation/preparation step, producer action and later continuation has its separate actual work and width cost. Combining these with (67.3) is the account for this one run. Later rational inputs can increase widths and material, and must be charged at their actual later values. $\square$

**Scope 67.4 (payload, constructive work and complexity).** The table procedure removes the candidate enumeration of §54 and supplies finite exact membership/residue arithmetic. No bound polynomial in the encoded initial input has been proved here for $W$, $L$ or the total work. Equation (67.3) is conditional on the actual maximum width, not an estimate setting that width to one. The information lower bounds of §48 remain: for $1\le H<a$, length-$L$ endpoints distinguish $(H+1)^L$ actual words, requiring at least $\lceil L\log_2(H+1)\rceil$ bits in a fixed-width lossless record. Table storage, source, programs, authority and archives are further material, not that payload. For $H=0$ the clock still has unbounded distinct lengths. No uniform precision bound, lower source-call count, optimal lattice basis, total-runtime improvement or peak-memory dominance follows. A supplied enumeration remains a sufficient alternative whenever its own actual costs meet the task.

## 68. Supplier correspondence, scalar overlap and exact remaining bridges

**Proposition 68.1 (the common scalar case is one result).** On the authentic $N=1$ specialization, the clock/residue consumer and the scalar valuation/digit consumer recover the same length and word. Their common authentic scalar case is a single deduction. The later-origin classification of §§59–61 and arbitrary-order computed consumer of §§63–67 have distinct additional domains.

**Proof.** The primitive law is $q(z)=sz-r$, so $a=s$ and $v_j=(r/s)^j$. For $n\ge1$,

$$
\Lambda_n=s^{-(n-1)}\mathbb Z.
\tag{68.1}
$$

Indeed each generator is in the right-hand side; conversely $1$ and $r^{n-1}/s^{n-1}$ generate it by $\gcd(r^{n-1},s^{n-1})=1$. The authentic origin is $\lambda^2=r^2/s^2$, whose reduced numerator is coprime to $s$. For every prime $\ell\mid s$, its valuation formula is $\nu_\ell(X(u))=-(L+2)\nu_\ell(s)$. Hence the first membership index in (68.1) is $L+3$, agreeing with $L+2N+1$ and the scalar formula. For the allowed digits $H<s$, both procedures return the unique actual word; for $H=s-1$ the scalar residue formula applies directly, and restriction gives the smaller alphabets. No second independent authentic-scalar theorem is needed. An arbitrary actual later scalar $p/q$ need not equal $\lambda^2$, so its exact good/bad-origin classification is additional. Conversely §§59–61 do not supply the matrix construction or whole-law residues for arbitrary $N$. $\square$

**Correspondence 68.2 (mathematical inputs and their hypotheses).** Repository suppliers in this section are interpreted at fixed public revision [1de6e6e8a3a3b77e922bc23dad5636224d083358](https://github.com/the-omega-institute/trureturing/tree/1de6e6e8a3a3b77e922bc23dad5636224d083358). The deductions are `repo-derived` relative to the following supplied mathematics, without a worldwide priority assertion.

| Supplier | Exact correspondence and role |
| --- | --- |
| This volume, §§36–41 | The original rational positive-link native path, authentic unit preparation, unknown-size paid acquisition, cyclic $K$, native law and actual $T^{2N}b$ are reused. The scalar experiment deliberately earns a later actual origin; the arbitrary-order consumer keeps the authentic one. |
| This volume, Lemma 45.1, Proposition 44.3 and Lemma 52.2 | The whole primitive integral annihilator ideal and exact order $a$ of every successive lattice quotient are supplied. They permit reducible $q$. Proposition 63.2 computes the matrices and maps for those specific lattices; it does not present their exact quotient order as new. |
| This volume, §§52–58 | Authentic signed-length separation, the sharp finite-menu inverse/collisions, original enumerative consumer, observation inverse, complete original menu, retained capability and advanced-cut/resource distinctions are supplied. The new arbitrary-order work is the computed filtration clock and descending residue consumer on that same image. |
| [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) and its [Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs) | State $\mathbb R^N$, output $\mathbb R$, update $T$, readout $b^{\mathsf T}$ and horizon $N$ give $\mathcal O_N$. Native cyclicity supplies injectivity, while the actual Read/returning-Tick diagnostic supplies its input. Its general observation inverse is a reused intermediate. |
| [CoefficientDrivenJacobiCharacteristicPolynomial](../../../D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.lean) and its [Scribe](../../../Blueprint/D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.scribe.cs) | The actual moment pairing, power basis and multiplication by $T$ supply the native Jacobi reconstruction used in §37. Its private monicity, degree/orthogonality and positive-norm/tridiagonal proofs are covered suppliers, not absent interfaces re-proved here. |
| [Pinned Mathlib Gauss lemma](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Polynomial/GaussLemma.lean), `Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map` | The primitive divisor is the whole $q\in\mathbb Z[z]$, fraction field $\mathbb Q$, dividend an arbitrary integer annihilator. This supplies the integral quotient in the already proved lattice order; irreducibility is unnecessary. |
| [Pinned rational valuation library](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean) | The classical nonzero rational valuation product and unequal-valuation sum laws underlie (60.2). The proof uses ordinary valuations only on nonzero terms, explicitly separating zero integer inputs. The later-origin iff and its actual signed collisions are source-specific deductions. |

Extended Euclid, unimodular two-row reduction, cyclic integer residues and ordinary base-$s$ expansion are `literature-attested` elementary arithmetic. They are proved to act on the required objects in (60.3)–(60.7), (61.1)–(61.5) and (63.4)–(63.7); no new general Euclidean or lattice normal-form theorem is claimed. [Akiyama–Thuswaldner–Zaïmi, *Comments on the height reducing property II*, arXiv:1403.7480v1, Theorem 3, its proof and Remark 11](https://arxiv.org/html/1403.7480v1) give finite-automaton recognition of bounded-digit zero representations for an algebraic number without unit-circle conjugates. A root of an irreducible factor of the present $q$ satisfies their hypothesis because all its conjugates are roots in $(0,1)$. Vanishing at that root alone need not annihilate the full cyclic vector when $q$ is reducible. Their zero-representation automaton does not install this path, earn its origin or identify its complete observation/continuation interface. Its numeration mathematics is credited; the present whole-law consumer uses the supplied integral ideal instead of claiming an unsupplied equivalence with one spectral factor.

**Correspondence 68.3 (other public sources retain their own domains).** [Atomic Generation Acquisition II, §§61–67](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md) supplies actual randomized guard acquisition, fixed-input weighted minimax and full LAB continuation on its reached tree image. [Unknown Field Native Startup, §§27–33](RECURSIVE_RELATIONAL_OBSERVATION_UNKNOWN_FIELD_NATIVE_STARTUP.md) supplies signed localized-ring producer provenance, its principal-Hankel stopping certificate, actual preparation and continued service. [Native Leaf Boundary Acquisition II, §§24–29](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md) supplies actual raw-binding separation through fresh-zero growth, complete raw/canonical continuation and its own same-run binary/age tradeoffs. These are supplied results, not new randomized minimax, signed startup, binding or original-tree inverse theorems of this scalar/lattice construction. Its later scalar Read does not replace the signed producer's acquisition hypotheses, and its computed matrices are not a raw-label decoder.

[Native Attractive Boundary Response, §18](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE.md) concerns the full complex spectral count for its fixed unit-source marginal and natural angular fibres, conditional on its analytic hypotheses. [Boundary Geometry Continuation III Appendix, §108](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md) gives a necessary annular germ of original maximal zero modes, without establishing their existence or selection. [Private-Randomization Quadratic Clock, §8](FIB_UNCALIBRATED_QUADRATIC_CLOCK_PRIVATE_RANDOMIZATION.md) treats independent seeds and complete real-report worlds with bounded report errors and an unrestricted expected-loss criterion. None of those operators, exact-real report ports or probability/energy quantities is identified with the rational path's Tick/Add law by (59.3) or (64.2). No common physical realization is inferred from their scalar, clock or boundary terminology.

**Scope 68.4 (what these two theorems establish).** The scalar result gives exact later-origin signed-length recovery/collisions, a direct bounded-digit inverse on its sufficient domain, and the reciprocal-only bounded converse, all after an earned actual origin. The arbitrary-order result gives a computed lattice clock/residue consumer on the authentically acquired path, its actual returned-cut recovery and synchronized original-menu service, with arithmetic counts paid at actual widths. Their common authentic scalar specialization is credited once. The independently meaningful geometries are the stated one-cell or native weighted-path fields; Time is the specified consecutive pulse list, Boundary the specified paid root data, and Memory the stated sufficient present predictor.

No arbitrary signed-word uniqueness, general bounded-alphabet converse for nonreciprocal later scalars, arbitrary later vector-origin classification, arbitrary rational command-history inverse, complete old-output journal recovery, physical authentication or polynomial-input/total-resource optimum is obtained. Current equal fields can erase old histories even when their common futures are predicted exactly. Archives that retain the distinction remain additional material. Exact source membership, reference binding, current authority, held serialization and sufficient backing remain hypotheses rather than facts certified by these finite observations.

Native $\alpha/\beta$ constructors are not identified with the paid affine pulse actions. A common native realization would need a proved state, legal-operation, initialization, complete-output, observation and resource correspondence. Binary scalar/pulse recovery supplies none of these bridges by terminology alone. The original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization, final-no-Ready and erased-history claims retain their exact original scopes; this work proves no new statement in them. Joining LAB, rational-path and quantum models, and completing the sustained four-expression programme, remain separate obligations.

## 追加锚（本行以下为增补区）

## 69. Two precise transport classes on the original native and path sources

**Definition 69.1 (actual sources, bindings and complete calls).** The native source is the owned, rooted and ordered LAB source of [Atomic Generation Acquisition, §§17,20](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md), with logical terms

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle,
\qquad P_p:\alpha\longmapsto\beta,
\qquad S_p:\beta\longmapsto\langle\beta,\alpha\rangle.
\tag{69.1}
$$

Addresses are finite words in $L,R$. The logical leaf $\beta$ has a material unary left marker; that marker is not an additional logical leaf or an admissible logical target. The material encoding $C(t)$ has one vertex for $\alpha$, two for $\beta$, and an ordered root with the two encodings below it for a branch. A promotion retains its root and adds one marker. A split retains the root, reuses its old marker as the new left beta root, and adds a marker and a right alpha, hence adds two vertices. Logical reachability has the original birth constraint: no alpha leaf occurs at an address ending in $L$.

Use exactly the guards and framing of [Atomic Generation Acquisition II, Definition 53.3](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md). For either request kind, an absent address returns Refusal(absent), and a branch returns Refusal(branch). At an alpha, $P$ returns Growth$(P,p)$ and performs (69.1), whereas $S$ returns Refusal(wrong type). At a beta, $S$ returns Growth$(S,p)$ and performs (69.1), whereas $P$ returns Refusal(wrong type). Every refusal leaves the source unchanged. With $A(p)=1^{|p|}0p$, a complete addressed request has its three-bit kind tag followed by $A(p)$, length $2|p|+4$. Growth has the original three-bit reply tag, kind bit and $A(p)$, length $2|p|+5$; each of the three distinct refusal reasons has length five. Each of the other six three-bit request tags returns the original three-bit BadFrame, unchanged. A proper incomplete addressed frame waits; a handler consumes exactly one frame. Every completed answer includes all its bits, End, the supplied local acknowledgement and Return with the prescribed cleanup. Missing authority or a wrong phase disables the primitive; it does not manufacture a type refusal. No Tag, size read, journal, history reader or indirect logical-leaf read is added.

The path source is exactly Definition 36.1: a finite, initially unknown $N\ge1$, rational symmetric tridiagonal $T$, strictly positive adjacent links, and $0<T<I$, with $b=e_0$ and actual initial field $b$. The original Read returns $b^{\mathsf T}x$ without changing $x$; Tick changes $x$ to $Tx$ and returns $b^{\mathsf T}Tx$; Add$(u)$, $u\in\mathbb Q$, changes $x$ to $x+ub$ and returns its fixed acknowledgement. If the installed Add also returns the updated root scalar, that scalar is an additional complete output. Hold leaves the field unchanged, returns its acknowledgement and prevents autonomous evolution during the held local calculation. The actual entrance is Theorem 37.2's unknown-size acquisition, not a supplied matrix or a reset: it executes $2N$ Ticks, one Read and $N+1$ Holds, consumes the $2N+1$ scalar outputs, earns $N,T$, and ends at

$$
x_*=T^{2N}b.
\tag{69.2}
$$

All endpoints below use this preparation. The root binding, exact arithmetic and responses, installed Add/Read/Tick/Hold rights, exclusive serialization, absence of concurrent writers or revocation, and sufficient finite source, response and working backing are premises. Earning a law does not authenticate those premises or allocate their resources.

**Definition 69.2 (independent views and the paired-source declaration).** Native Space is the present rooted, ordered material address support with its original edge meanings; Boundary is its terminal-address antichain; Time is the labelled causal order of successful promotions and splits, with predecessor constraints at their actual addresses. These are the original independent meanings of Atomic Generation Acquisition §17, whose source, boundary and causal inverses are used on their reached images. The original root binding is fixed; semantic equality disregards fresh allocation-name spellings exactly as $Q_A$ does. Recovering the address geometry does not allocate its vertices or recover an additional raw-name roster. Time here forgets the serial ordering of independent successful events and does not include failed probes. Recovering it does not recover an erased serial journal. Native Memory in the tasks below is sufficient present information for their stated guards and successors, rather than a copy of that journal.

A paired execution means two actually supplied sources: the native source and the path source just specified, with their actual references, authorities, backing and held serialization. A selector first causes its prescribed native calls, then its prescribed path calls; a settled cut occurs only after all complete replies, acknowledgements, source effects and local commits. The union of those resources is charged on that execution. This declaration supplies no map identifying the two physical sources. A native realization by one path would additionally require an initialization, legal-operation, complete-output, successor and resource correspondence. The endpoint restrictions in §§71 and 74 concern two different classes of proposed correspondences; neither asserts that every native-to-path correspondence belongs to its class.

## 70. Repeatable independent native growth with actual distinguishing guards

**Definition 70.1 (the two native growth coordinates).** Put

$$
C_0=\beta,\qquad C_{j+1}=\langle C_j,\alpha\rangle,
\qquad t_{a,b}=\langle C_a,C_b\rangle\quad(a,b\in\mathbb N).
\tag{70.1}
$$

Here $C_j$ denotes a logical comb, distinct from the material-encoding notation $C(t)$. From the owned known alpha, the actual calls $P_\varepsilon;S_\varepsilon;P_R$, with their whole Growth replies, prepare $t_{0,0}$. Define $H_L$ as follows. Start at address $q=L$ and issue $P_q$. On Refusal(branch), replace $q$ by $qL$ and repeat. On Refusal(wrong type), issue $S_q$, consume its whole Growth reply and return. Define $H_R$ with initial address $R$. These are guarded native procedures, not fixed-length native command words. They use the original paid address traversal and call framing; an unexpected different reply does not satisfy their declared source domain.

**Proposition 70.2 (all coordinate pairs, full guards and independent events).** At $t_{a,b}$, $H_L$ terminates at $t_{a+1,b}$ after exactly $a+1$ refused $P$ calls and one successful $S$ call; $H_R$ terminates at $t_{a,b+1}$ after $b+1$ refused $P$ calls and one successful $S$ call. Both orders of the two procedures are legal and have identical final native source. Every pair $(a,b)\in\mathbb N^2$ is reached. Distinct pairs are distinguished by an actual original guard.

**Proof.** In the left comb, addresses $L,LL,\ldots,LL^{a-1}$ are branches, and $LL^a$ is beta. Thus the first $a$ probes give the complete branch-refusal frame, the next gives the complete wrong-type-refusal frame, and the following $S$ grows that beta. It inserts one further comb branch, leaving every right-side object unchanged. This proves the count and successor, also when $a=0$. The right proof has the same address calculation with initial $R$. The subtrees are disjoint, so either order has successor $t_{a+1,b+1}$. Induction reaches all pairs.

If $a<a'$, issue $P_{LL^a}$ to the two states. It returns Refusal(wrong type) at $t_{a,b}$ and Refusal(branch) at $t_{a',b'}$, with both sources unchanged. If the left coordinates agree and $b<b'$, use $P_{RL^b}$. Reversing the pair covers the remaining inequalities. These are different original complete replies, not abstract tests added to the source. The material source has exactly $5+2(a+b)$ vertices. Its causal successful-event order consists of the fixed preparation and two independent chains; its possible serial shuffles are additional history information. $\square$

## 71. Complete classification of fixed original-command blocks

**Definition 71.1 (fixed-block field representation).** After (69.2), choose two finite straight-line blocks $W_L,W_R$ of the original path menu. Their commands and rational Add operands may depend on the earned law and fixed context, but not on future selectors, intermediate returned values or the current field. Reads, Holds and all acknowledgements are actually executed and consumed. No reset, inverse Tick or other field actuator is allowed. Interpreting a selector $L$ as the paired procedure $H_L;W_L$ and $R$ as $H_R;W_R$, ask whether the settled path field is a single function $E(a,b)$ of the current native source, independent of the selector route. This is an endpoint requirement; complete native and path reply traces remain their respective actual traces, without an assumed equality between them.

Let $m,n$ be the numbers of Ticks in $W_L,W_R$. Command induction gives their field effects

$$
F(x)=T^m x+c,\qquad G(x)=T^n x+d,\qquad c,d\in\mathbb Q^N.
\tag{71.1}
$$

An Add operand $u$ contributes $uT^r b$, where $r$ is the number of subsequent Ticks in that block. Reads and Holds do not change (71.1). This formula counts the actual block, including zero operands and redundant observations.

**Theorem 71.2 (route or collision, with every zero-Tick case).** For every source of Definition 69.1 and every pair of blocks of Definition 71.1, define

$$
\Delta=(T^n-I)c-(T^m-I)d.
\tag{71.2}
$$

A route-independent field representation on all $\mathbb N^2$ exists if and only if $\Delta=0$. If $\Delta\ne0$, the legal native routes $LR$ and $RL$ reach the same native source and path fields differing by $\Delta$. If $\Delta=0$, the following is the complete equality classification, and in every case $E$ fails to be injective.

1. If $m,n>0$, there is a common rational point

$$
z=(I-T^m)^{-1}c=(I-T^n)^{-1}d,
\qquad E(a,b)=z+T^{ma+nb}(x_*-z).
\tag{71.3}
$$

If $x_*=z$, all fields agree. Otherwise

$$
E(a,b)=E(a',b')\quad\Longleftrightarrow\quad ma+nb=ma'+nb'.
\tag{71.4}
$$

In particular, for $g=\gcd(m,n)$, the distinct pairs $(n/g,0)$ and $(0,m/g)$ collide.

2. If $m=0<n$, then $c=0$, $F=I$, and, with $z=(I-T^n)^{-1}d$,

$$
E(a,b)=z+T^{nb}(x_*-z).
\tag{71.5}
$$

It is constant when $x_*=z$; otherwise equality holds exactly when $b=b'$, so the entire first coordinate is lost. If $n=0<m$, the symmetric assertion holds: $d=0$, and nonconstant equality is exactly $a=a'$.

3. If $m=n=0$, there are rational $r,s$ with $c=rb$, $d=sb$, and

$$
E(a,b)=x_*+(ra+sb)b,
\qquad E(a,b)=E(a',b')\Longleftrightarrow
r(a-a')+s(b-b')=0.
\tag{71.6}
$$

This map also has a collision between distinct nonnegative pairs, including when either or both coefficients vanish.

**Proof.** Applying the individual command effects proves (71.1) by induction through each block. Direct composition gives

$$
G(F(x))-F(G(x))=T^n c+d-T^m d-c=\Delta.
\tag{71.7}
$$

The two legal routes in Proposition 70.2 therefore prove necessity. If $\Delta=0$, the affine maps commute on every field. Any two finite selector words with the same multiplicities are related by adjacent interchanges of $LR$ and $RL$: move the first required letter leftward, and continue inductively on the remaining suffix. Each interchange preserves the field by (71.7). Consequently the endpoint depends only on $(a,b)$, proving sufficiency without restricting later routes.

The eigenvalues of $T$ lie in $(0,1)$. Hence $T^j$ and $I-T^j$ are invertible for every positive $j$. Their rational inverses exist because their matrices are rational and have nonzero determinants. In the first case, $\Delta=0$ says $(I-T^n)c=(I-T^m)d$. The two invertible polynomial matrices commute with each other and with their inverses. Multiplication gives the equality defining $z$. Both affine maps then fix $z$; induction gives (71.3). If exponents $p<q$ produced equal nonconstant fields, then

$$
0=T^p(I-T^{q-p})(x_*-z),
\tag{71.8}
$$

whose invertible factors would imply $x_*=z$. Equal exponents suffice, proving (71.4). The displayed distinct pairs have common exponent $mn/g$.

If $m=0<n$, (71.2) reduces to $(T^n-I)c=0$, so $c=0$. Centering $G$ at its unique fixed point proves (71.5), and (71.8) proves its exact equality classification. Exchanging the blocks proves the other case.

If neither block has a Tick, its Adds only sum scalar multiples of the same $b$, proving (71.6). If $r=0$, varying $a$ gives a collision; if $s=0$, varying $b$ does. Otherwise choose a positive common denominator $D$ and integers $A=Dr$, $B=Ds$. The nonzero integer vector $(B,-A)$ satisfies the kernel equation. Writing it as its coordinatewise positive part minus its negative part gives two distinct pairs in $\mathbb N^2$ with the same image. This also treats opposite signs without assuming positive translations. The alternatives exhaust all nonnegative $m,n$. $\square$

## 72. Actual distinguishing futures and the conditional price of extra records

**Proposition 72.1 (route separation is observable; collisions have equal path futures).** In the noncommuting case of Theorem 71.2, the two route endpoints are distinguished by a common original-menu continuation consisting of Read followed by $N-1$ returning Ticks. In any collision case, equal field endpoints with the same earned law, binding, rights and all other selected recovery inputs have identical complete replies and equal successors for every common finite adaptive original-path continuation. The common continuation has the same initial local continuation state and selects its next command only from its declared inputs and acquired complete replies. Their different native states nevertheless have the distinguishing guard of Proposition 70.2.

**Proof.** The positive-link path has the triangular cyclic matrix $K=[b,Tb,\ldots,T^{N-1}b]$: the coordinate $j$ of $T^j b$ is the positive product of the first $j$ links, and all coordinates beyond $j$ vanish. Thus $K$ and $\mathcal O_N=K^{\mathsf T}$ are invertible, as in Lemma 37.1. For unequal endpoint fields $y,y'$, at least one entry of $\mathcal O_N(y-y')$ is nonzero. The prescribed actual continuation returns exactly $b^{\mathsf T}T^j y$ for $0\le j<N$, including the first nondestructive Read and all subsequent Tick outputs. It therefore distinguishes the fields. It leaves them at $T^{N-1}y,T^{N-1}y'$, rather than granting a free vector observation.

For equal fields, a common Read has equal scalar reply and unchanged equal successors; a common Tick has equal returned scalar and equal $T$-successors; a common Add with the same operand has equal acknowledgements, equal optional root outputs and equal translated successors; a common Hold has equal acknowledgement and unchanged successors. Given a common adaptive protocol and equal other selected inputs, its next choice is the same after equal complete reply prefixes. Induction proves the assertion, with identical legal-domain conditions and completed acknowledgements. A pending incomplete request stays pending in both. Proposition 70.2 supplies the different native guard. Old block outputs need not have agreed: this proof does not delete a surviving archive or a controller distinction. $\square$

**Corollary 72.2 (an exact conditional auxiliary alphabet).** Suppose $m,n>0$, $\Delta=0$, and a decoder is required to recover every present native pair from the current path field and a jointly selected auxiliary value $A$. For every $h\ge0$, the collision fibre contains

$$
(a_j,b_j)=\left(\frac ng j,\frac mg(h-j)\right),
\qquad 0\le j\le h,
\qquad ma_j+nb_j=\operatorname{lcm}(m,n)h.
\tag{72.1}
$$

Thus the auxiliary values actually available on those $h+1$ cases must have at least $h+1$ distinguishable possibilities. A fixed-width binary auxiliary register needs at least $\lceil\log_2(h+1)\rceil$ bits on that fibre. If $x_*=z$, the same conclusion still holds, with an even larger field fibre.

For each zero-Tick identity case of Theorem 71.2, the analogous fibre contains $h+1$ pairs obtained by varying the lost coordinate from zero to $h$. In the case $m=n=0$, choose a nonzero integer vector $w$ in the kernel of $(r,s)$ as in that theorem, and write $w=w^+-w^-$ with nonnegative coordinatewise parts. Then the $h+1$ pairs $jw^++(h-j)w^-$, $0\le j\le h$, share one field. Thus every commuting case requires arbitrarily large auxiliary alphabets if recovery of all native pairs is required.

**Proof.** All pairs in (72.1) are distinct, nonnegative and actually reachable. Equation (71.3) gives a common field. The zero-Tick identity cases follow from (71.5). In the translation case, the difference between the $j$th and $j'$th displayed pairs is $(j-j')w$, nonzero for distinct indices, while the functional $(r,s)$ annihilates that difference. Equation (71.6) therefore gives a common field. Two cases with the same jointly selected auxiliary value would give identical decoder inputs and different required answers. Injectivity on each finite set proves the alphabet bound and its fixed-width binary consequence. $\square$

Here $A$ includes every varying selected input: retained request or reply traces, a selector count, addresses, controller state, source-dependent code or constants, references and rights, archive contents and accessible backing, and any surviving source-dependent scratch. A short archive handle does not replace the distinguishable contents or callable behavior behind that handle. If an actual native guard is admitted as a recovery query, its distinguishing response is additional input and cannot be declared absent. A surviving archive can satisfy the bound; the corollary is not an erased-history theorem in its presence. A route-dependent path field can also escape the route-independent premise. No count of variable-length encodings or total resource optimum follows from this fixed-fibre alphabet statement.

**Resource statement 72.3 (the same paired execution).** At native endpoint $t_{a,b}$ the material source is $5+2(a+b)$ vertices. Beyond its three-call preparation, its actual guard-scan refusals number $a(a+1)/2+b(b+1)/2$, and its successful splits number $a+b$. The preparation's request/Growth payload is 31 bits. One $H$ call at local coordinate $j$ has refusal probes at depths $1,\ldots,j+1$ and a successful split at depth $j+1$; its request/reply payload is

$$
\sum_{d=1}^{j+1}(2d+9)+4(j+1)+9=j^2+16j+24.
\tag{72.2}
$$

Summing (72.2) for $0\le j<a$ and $0\le j<b$ gives the complete addressed payload beyond preparation. End, acknowledgement, Return, navigation, backing and local address calculations are separate real operations. The path has its original $N$ vertices and actual field values. If $B_{L,Q},B_{R,Q}$ count occurrences of command $Q$ in the two literal blocks, the continuation executes exactly $aB_{L,Q}+bB_{R,Q}$ such commands, in addition to entrance; its Tick count is $ma+nb$. Every returning Tick, Read, optional Add scalar and fixed acknowledgement remains paid. Both source supports, root references, actual grants, law storage, fixed block literals, controller and work arena, all selected records and any coexisting archives/backing are charged together. Each arbitrarily long finite native run requires its own adequate finite provision; no fixed finite source quota serves all pairs. Finite blocks do not bound the widths of repeatedly evolved rational fields, addresses or counters. The optimized obstruction concerns a canonical field representation; it is not a bound on every augmented representation or on the entire cost vector.

## 73. An actual finite independent layer and complete settled auxiliary inputs

**Definition 73.1 (the native independent layer).** Fix an integer $k\ge1$. From the owned alpha, for $j=0,\ldots,k-1$ execute $P_{R^j}$ and then $S_{R^j}$, consuming both whole Growth replies. This prepares incomparable beta leaves

$$
p_i=R^iL\quad(0\le i<k),
\qquad\text{and one continuing alpha at }R^k.
\tag{73.1}
$$

A valid selector Select$(i)$, $0\le i<k$, means the actual original call $S_{p_i}$. For a subset $U\subseteq\{0,\ldots,k-1\}$, let $t_U$ be the source after precisely those distinct selections in $U$. At an unused $i$ the complete reply is Growth$(S,p_i)$ and the successor is $t_{U\cup\{i\}}$; at a used $i$ the reply is Refusal(branch) and the source stays $t_U$. Every subset, every ordering of its elements and every finite sequence with repetitions is legal under sufficient backing. Different subsets are distinguished by an actual Select in their symmetric difference. The original $P_{p_i}$ also distinguishes beta from branch by wrong-type versus branch refusal, without changing either source. Each partial sequence extends to one reaching all $k$ selected leaves. Thus equality of subsets is exactly equality of the complete Select continuation task on this reached layer, although that task is smaller than unrestricted $Q_A$.

**Proof of the source assertions.** At step $j$ the continuing leaf $R^j$ is alpha, so its promotion and split have the stated guards and leave the next continuing alpha at $R^{j+1}$. Its left beta is never touched by later preparation. The addresses $p_i$ are incomparable; a split at one cannot affect another. After that split the same address is a branch, proving the two complete-reply cases and all successor statements. Choosing any enumeration of a subset reaches it, and appending its complement reaches the full subset. Initially the prepared support has $1+3k$ vertices; at $t_U$ it has $1+3k+2|U|$, reaching $1+5k$ at the full subset. The same source, terminal-boundary and causal-order inverses of Definition 69.2 recover this present layer; the causal order does not specify the permutation of its independent selections. $\square$

**Definition 73.2 (adaptive canonical-cut pulse class).** Fix the actual acquired path of (69.2), its whole primitive integer law $q$ of Definition 44.2, positive leading coefficient $a\ge2$, and a digit bound $0\le H<a$. A pulse with digit $d\in\{0,\ldots,H\}$ is literally Tick; Add$(d)$; Read, including when $d=0$. At pre-pulse field $x$ its complete outputs are

$$
\tau=b^{\mathsf T}Tx,\quad\mathrm{ack}_{\rm Add},\quad
 y=b^{\mathsf T}(Tx+db)=\tau+d,
\qquad x'=Tx+db,
\tag{73.2}
$$

with any installed optional Add scalar included as well. A translator must serve every finite valid Select sequence on the actual layer, with its complete native replies and successors, under the supplied adequate finite backing. In particular every reached partial subset admits service of its remaining selections; excluding an order or stopping at a partial subset is outside this class. It may adapt its finite pulse block for each Select to all actually available inputs and replies, and may use arbitrary finite paid scratch while busy. Reads and Holds may occur outside pulses; every post-entrance Tick and Add must belong to a completed pulse. There is no other path motion, reset or source re-preparation. Intermediate cuts can be busy, but settled cuts have completed calls, outputs and commits and no pending external request.

The canonical-field condition is that every settled history reaching native $t_U$ has the same actual path field $z_U$. This includes differing orders, repetitions and any admitted choices of the translator. The recovery condition is an exact decoder of $U$ from that field and a joint auxiliary input taking at most $R$ distinguishable values over all these cuts, for some integer $R\ge1$. The fixed common context may contain $k,R$, the earned law and origin, a fixed program, fixed references and rights and a common cleared workspace capacity. Every other varying selected decoder input is part of the joint auxiliary value: records, old inputs and outputs, counters, pending selectors retained after commit, code/control state, reference or grant variations, source-dependent allocation shape, accessible archives and their backing contents, and surviving scratch. Callable side objects are counted by their distinguishable permitted recovery behavior, not just handle bytes. Random choices, if admitted, satisfy these same requirements on every admitted execution and are included when retained or selected.

The lower bound grants the decoder the exact current field; granting it does not install a free vector-reading port. A decoder that selects an original native guard or a surviving native/producer archive as additional recovery input must include its distinguishable behavior in the auxiliary alphabet. In particular, querying all $k$ original $P_{p_i}$ guards can reveal the subset, and then a bound $R<2^k$ cannot describe that complete collection of inputs. The supplied native source may be the object of the later actual Select actuation without being selected as a free earlier recovery oracle. All coexisting objects remain paid physical resources even when they are outside the decoder's selected inputs. Unbounded busy scratch is allowed; only information surviving or accessible at a settled recovery cut is bounded by $R$.

For a finite digit word $w$ of length $l$, the actual field is

$$
X(w)=T^{l+2N}b+\sum_{i=0}^{l-1}w_iT^{l-1-i}b.
\tag{73.3}
$$

Theorems 52.3 and 53.1 supply its injectivity on all finite words over this menu, including different lengths and the empty word. They use the authentic origin and the full primitive law, not one chosen spectral root. We use that result as a supplier, without replacing it by an extra clock construction.

## 74. Cofinal canonical cuts force a motion-capacity restriction

**Theorem 74.1 (complete auxiliary-capacity bound).** Every translator of Definition 73.2 serving the actual layer of Definition 73.1 satisfies the following. If a finite execution reaches the full subset after $M$ post-entrance pulses, then

$$
2^k\le R(M+1),\qquad
M\ge\left\lceil\frac{2^k}{R}\right\rceil-1.
\tag{74.1}
$$

All full-subset executions have the same literal pulse word. For each subset $U$, all histories reaching it have a unique pulse word $v_U$, which is a prefix of that common full word. A refused repeat Select executes no pulse between its two settled cuts. Thus (74.1) holds on every full execution, including executions containing repeated selectors, not merely on a separately chosen optimal order.

**Proof.** Choose one actual full execution and call its pulse word $W$, length $M$. Another full execution has the same final field by canonicality. Injectivity of (73.3) makes its entire word equal to $W$, including its length. Now take any finite history reaching $U$. Definition 73.1 extends its actual native history to the full subset. Serving the appended selectors appends a pulse word; it cannot remove earlier pulses. The resulting full word is $W$, so the partial word is a prefix of $W$. Two histories reaching the same $U$ have the same canonical field and hence, by the same injectivity, identical pulse words. This defines $v_U$. No assumption of fixed blocks or order-independent busy computations has been used.

For each of the $2^k$ subsets, choose one reached settled cut and its actual jointly selected auxiliary value $A_U$. The map

$$
U\longmapsto(v_U,A_U)
\tag{74.2}
$$

is injective. Indeed, equal pairs give equal exact fields by (73.3) and equal all selected auxiliary inputs, so the exact decoder must return the same subset. The word $W$ has exactly $M+1$ prefixes, including the empty and whole words, and the joint auxiliary alphabet has at most $R$ values. Counting the possible pairs proves the first inequality. Since $M+1$ is an integer, it implies the second.

Finally, a repeat Select leaves $U$ unchanged. If its pre-cut pulse word is $v$ and its post-cut word is $vw$, canonicality gives $X(v)=X(vw)$. Injectivity gives equality of the literal finite words, hence $|w|=0$. Reads, Holds, complete refusals and busy work can still occur and are paid. This proves all claims. $\square$

**Scope 74.2 (the quantified restriction).** The argument uses three separate premises: actual independent cofinal native subsets, injectivity of the original bounded-digit pulse words from the actual acquired phase, and canonical settled fields with a complete jointly bounded auxiliary alphabet. It is not a restriction on arbitrary adaptive path commands, signed/unbounded menus, noncanonical fields retaining route information, an altered origin, an unconstrained auxiliary archive or a decoder with uncounted source queries. A retained backing that distinguishes subsets either enlarges $R$ or violates the premise; it cannot be silently removed from the count. No pulse bound is inferred merely from a finite program, a bounded number of named registers or a small handle. The bound concerns pulse motion and settled distinguishability, not peak scratch, field bit widths, total source material, elapsed work or serial-history recovery.

## 75. A paid two-source consumer attains exactly the restricted bound

**Definition 75.1 (installation and the two counted coordinates).** Supply both actual sources, their preparation and acquisition as in Definitions 69.1 and 73.1, with one serial controller and adequate finite material for the following fixed $k,R$ task. Keep their two references and original authorities; no source is manufactured by a numerical representation of the other. At each settled cut require the native source to be $t_U$, and put

$$
r(U)=\sum_{i\in U}2^i,\qquad
n(U)=\left\lfloor\frac{r(U)}R\right\rfloor,\qquad
s(U)=r(U)-Rn(U),
\qquad
M_* =\left\lfloor\frac{2^k-1}{R}\right\rfloor
     =\left\lceil\frac{2^k}{R}\right\rceil-1.
\tag{75.1}
$$

The required path field and sole varying selected auxiliary register are

$$
x_U=T^{2N+n(U)}b,
\qquad s=s(U)\in\{0,\ldots,R-1\}.
\tag{75.2}
$$

No $n$, rank, mask, current predictor, input journal, past outputs or selector count is retained as another selected register. Fixed code and context may contain $k,R,N,T$ and the earned origin. The scalar-origin and direct residue consumers of §§59–67 are suppliers for exactly this kind of finite arithmetic consumption; the following uses only their original passive-root specialization, Lemma 39.2. It claims no additional implementation of a clock.

The recovery phase selects only the path root Read and the residue register. The native reference is used for the subsequent actual Select actuation; it is not queried to recover $U$. A native traversal, separate archived subset, hidden counter or surviving source-dependent allocator state would be an additional selected input and would change the claimed alphabet. A common fixed-capacity work arena, including fixed-format exact integer and rational buffers large enough for this finite task, is supplied and charged. All scratch, request/reply buffers and variable local state are cleared before each settled cut; its available capacity and allocation shape there are the same for every subset. This finite backing requirement is an explicit installation premise, not a consequence of the number of program instructions. The path's actual rational values and their physical encoding are paid field material. Their finite maximum encoding capacity can likewise be fixed across this task, with canonical value encodings and zero padding; no additional source-dependent header or stale payload is offered to the decoder. Native source material is also paid, whether selected by the decoder or not.

**Theorem 75.2 (actual recovery and every finite Select continuation).** The installation of Definition 75.1 has an exact finite service for every valid finite adaptive sequence of Select requests, including repetitions. At its settled cuts it satisfies (75.2), recovers the native subset and hence its present Space, Boundary and causal Time, and returns the complete original native reply and actual native successor. A first successful selection of $i$ executes exactly

$$
\left\lfloor\frac{r(U)+2^i}{R}\right\rfloor
 -\left\lfloor\frac{r(U)}R\right\rfloor
\tag{75.3}
$$

zero pulses. A repeated selection executes none. Every full-subset execution has exactly $M_*$ post-entrance pulses and at most $R$ jointly selected auxiliary values. It therefore attains (74.1) in precisely those two coordinates.

**Proof.** Initially $U=\varnothing$, $r=n=s=0$, and the preparations put the sources at $t_\varnothing,x_*$, as required. Suppose the invariant holds at a settled cut. Enter a busy phase and Hold the actual path. Its actual Read returns

$$
y=b^{\mathsf T}T^{2N+n}b=m_{2N+n}.
\tag{75.4}
$$

For a nonzero $b$ and $0<T<I$, the passive moments strictly decrease:

$$
m_j-m_{j+1}=b^{\mathsf T}T^j(I-T)b>0\quad(j\ge0).
\tag{75.5}
$$

Indeed, diagonalizing the real symmetric $T$ makes this a sum of nonnegative terms $c_\ell^2\lambda_\ell^j(1-\lambda_\ell)$, at least one strictly positive. This is the supplied passive-moment fact. Using the actually earned rational $T$, enumerate $n_0=0,\ldots,M_*$ and compute each rational $m_{2N+n_0}$ by finite exact matrix arithmetic until it equals the actually returned $y$. Existence follows from (75.2) and $n\le M_*$; uniqueness follows from (75.5). Thus this paid local procedure obtains the correct $n$, then $r=Rn+s$, then the unique $k$-bit subset $U$. It has no unearned passive epoch or response oracle. The number, sizes and cost of its arithmetic operations are paid busy work.

Decode the valid request $i$ and issue the actual original $S_{p_i}$, consuming its entire framed response, End, local acknowledgement and Return. If $i\notin U$, Definition 73.1 gives Growth$(S,p_i)$ and source $t_{U'}$, $U'=U\cup\{i\}$. The recovered rank has zero $i$th bit, so $r'=r+2^i$ exactly, without a carry into other subset bits. Put $n'=\lfloor r'/R\rfloor$, $s'=r'-Rn'$. Then $n'\ge n$. Execute $n'-n$ complete zero pulses on the same path, consuming every returning Tick scalar, Add acknowledgement and Read scalar. They change $T^{2N+n}b$ to $T^{2N+n'}b$ and establish (75.2) for $U'$. Store $s'$. If $i\in U$, the actual response is Refusal(branch), both the subset and its rank stay unchanged, and execute no pulse. Thus both branches agree with the actual full native reply and successor, not just with a predicted Boolean success flag.

A final Hold fixes the path while the controller completes its local commit, emits the buffered original native response and clears its temporary data under the supplied End/acknowledgement/Return convention. No later request is admitted until cleanup and commit have finished. The busy interval, including the interval after the native source has changed and before its path/residue update, is not exposed as a settled recovery cut. The fixed response frame is itself consumed or cleared before that cut; a surviving external archive, if later selected, is additional input. The invariant is restored. Induction covers every finite adaptive valid sequence, since equality of earlier complete replies allows the next request to be selected from exactly its actual prefix.

For this restricted Select service, one may use fixed-format local request fields of width $\max(1,\lceil\log_2k\rceil)$ with a complete-message delimiter. A complete malformed or out-of-range local request returns a declared local rejection, leaves both sources and $s$ unchanged and executes no source call. A proper incomplete frame remains busy/pending until completed, rather than producing an original source refusal. Missing authority disables the actual source call. None of these local conventions adds an original native guard outcome or offers the full unrestricted $Q_A$ through a new tag. For valid selectors the actual addressed request sent to the source is exactly Definition 69.1's original $S$ frame.

The rank is nondecreasing, and each successful step executes the difference of its two successive quotients. Telescoping from zero to $\lfloor(2^k-1)/R\rfloor$ gives exactly $M_*$ pulses, regardless of selection order or repeats. The final field depends only on $U$ at every settled cut, so canonicality holds. The residue has at most $R$ values; no other varying selected input survives by the installation's explicit clearing and fixed-capacity conditions. This proves attainment. If $R\ge2^k$, $M_*=0$ and the residue already holds the whole rank; that boundary case is included. Finally, the recovered subset specifies exactly the actual prepared source with its selected incomparable splits. Applying the original native inverses recovers its present support, terminal boundary and causal event order. Conversely, the support parses the present constructor at each $p_i$, which is a branch exactly for $i\in U$; the terminal boundary recovers that support by prefix closure; and the labelled causal order contains $S_{p_i}$ exactly for $i\in U$. Each of these independent native views therefore recovers $U$, and then the two Memory coordinates in (75.2) by (75.1), on the paired invariant image. These are mathematical recovery maps on the stated views; they do not add a geometric-read port or allocate a replacement source. The actual installed recovery procedure above uses only the original path root and the paid residue. None of these maps reconstructs the order of the independent selections or earlier emitted replies. $\square$

**Resource statement 75.3 (actual calls, replies and widths).** Let $J\ge k$ be the number of valid Select requests on a full-subset execution, including repeats. Native preparation executes $k$ promotions and $k$ splits. Continuation executes $k$ successful splits and $J-k$ branch refusals. Its final support has $1+5k$ vertices. Preparation request/Growth payload is

$$
\sum_{j=0}^{k-1}2(4j+9)=4k^2+14k;
\tag{75.6}
$$

successful continuation payload is

$$
\sum_{i=0}^{k-1}\bigl(4(i+1)+9\bigr)=2k^2+11k.
\tag{75.7}
$$

Each repeated request at index $i$ additionally pays $2i+11$ addressed request/refusal bits. These equations exclude the separately paid End, acknowledgement, Return, local selector input/output, source navigation, assignments and local buffering.

Choose exactly the initial Hold and recovery Read and final Hold of Theorem 75.2 on each valid call, with no other continuation Holds. Including the original unknown-size path acquisition, the actual original-menu counts are

$$
\begin{aligned}
\#\mathrm{Tick}&=2N+M_*,&\#\mathrm{Add}&=M_*,\\
\#\mathrm{Read}&=1+J+M_*,&\#\mathrm{Hold}&=N+1+2J.
\end{aligned}
\tag{75.8}
$$

Consequently mandatory scalar replies number $2N+1+J+2M_*$; Add/Hold acknowledgements number $M_*+N+1+2J$. An optional updated-root Add reply contributes another $M_*$ scalars. These are counts of actual calls and complete outputs, not unit-cost bounds for their payloads or arithmetic. All original native and path supports coexist with their two roots, original source and response ports, retained authorities, earned matrix and origin, fixed code/constants, selector input, residue encoding, current field encoding, cleared work arena and any external response/archive/backing that actually survives. A fixed-width residue implementation uses $\lceil\log_2R\rceil$ bits, permitting zero bits when $R=1$; its control and physical slot overhead is separate. If a backing, allocator, controller or external caller retains varying information accessible to recovery, it enlarges the joint alphabet and the two-coordinate assertion must be reevaluated with that actual alphabet.

The enumeration and update require temporary $n,r,U$, rational powers, comparisons, buffered responses and loop counters; their widths and work are charged while busy, though their cleared contents are absent at the next settled cut. Adequate common capacity can be supplied for fixed finite $k,R,N,T$: there are finitely many possible subsets, valid inputs and intermediate arithmetic calculations in the stated bounded enumeration and at most $M_*$ pulses. Reserve their maximum required finite capacities in advance, with fixed allocation shape and complete clearing. This explains the finite existence of such backing without supplying it for free or imposing a uniform bound over all $k$.

An authentic scalar example exposes the separate width cost. For $N=1,T=(1/2)$ the original acquisition ends at $x_*=1/4$. After $n$ zero pulses the field is $1/2^{n+2}$ and its reduced denominator needs $n+3$ binary digits. In particular the final field alone has denominator width $M_*+3$. The Tick and Read of pulse $s$, $1\le s\le M_*$, both return $1/2^{s+2}$; just the sum of their reduced-denominator digit lengths is

$$
2\sum_{s=1}^{M_*}(s+3)=M_*^2+7M_*.
\tag{75.9}
$$

Phase-recovery Reads, entrance outputs, signs, numerators, frame syntax, acknowledgements and all temporary arithmetic add to this lower accounting. Thus sharpness of $(M_*,R)$ is not a peak-memory, total-bit, total-work or total-material optimum. The native source has been supplied alongside the path throughout; the construction is not a native realization by a path.

## 76. Exact supplier correspondence and the remaining realization obligations

**Correspondence 76.1 (the mathematical delta).** The route criterion in Theorem 71.2 uses the mature commuting-square and affine-map principles represented by [Faithful Observation Commutation Criterion](../../../Blueprint/D5/S3/ConceptDynamics/Faithfulness/FaithfulObservationCommutationCriterion.md), [Integer Affine Square Collision](../../../Blueprint/D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerAffineSquareCollision.md) and [Enabled Path Swap Connectivity](../../../Blueprint/D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.md). Their general square/kernel facts do not specify the actual repeatable LAB procedures, the legal guards, the original rational command normal forms, all zero-Tick alternatives or the exact equality kernels (71.4)–(71.6). Those hypotheses and calculations provide the source-specific classification here. The fixed-point semiconjugacy supplier [Fixed Point Semiconjugacy](../../../Blueprint/D5/S3/Observer/Bridges/FixedPointSemiconjugacy.md), and the elementary upstream `Function.IsFixedPt.map` in [pinned Mathlib](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Dynamics/FixedPoints/Basic.lean), carry fixed points under an already given semiconjugacy; neither installs the missing native/path map. Proposition 72.1 uses the actual path observability matrix, consistently with [Finite Observability Equivalence](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.md), and pays the actual destructive observation continuation.

Theorem 74.1 uses ordinary finite-cardinality injection, as in upstream `Fintype.card_le_of_injective`, after proving the cofinal common-prefix property from actual native continuations and authentic pulse-word injectivity. The new restriction is this property for the precise adaptive canonical-cut class with all selected auxiliary inputs included, not a new general counting theorem. Theorems 52.3 and 53.1 already supply the whole-law, all-length bounded-digit injectivity; §§59–67 already supply scalar-origin/lattice clocks and direct residue consumers, including later returned-root and continuation limits. Theorem 75.2 consumes those supplied capabilities only to attain the bound's pulse/settled-alphabet coordinates, with complete replies, two sources, finite backing and numerical widths retained in the bill.

The integral algebra behind the supplied pulse result uses Gauss's primitive-divisibility lemma over $\mathbb Z\subset\mathbb Q$, with the full primitive annihilator and no irreducibility assumption, as attached to Proposition 44.3. [Akiyama–Thuswaldner–Zaïmi, *Comments on the height reducing property II*, Theorem 3 and Remark 11](https://arxiv.org/html/1403.7480v1) concern bounded-digit zero representations at an algebraic number with no unit-circle conjugates. Applying a scalar root result alone would not identify the full cyclic-vector kernel of a reducible path law, the actual acquired origin, a LAB guard or the complete callable service. This numeration result is a credited supplier comparison, not a substitute for those hypotheses. The source-specific results in §§70–75 are repository-derived mathematical synthesis; no claim of worldwide priority follows from a finite source or literature comparison.

**Correspondence 76.2 (other public models do not identify the translator classes).** [Native Continuation Affine Obstruction and Approximation, Definition 4.1](FIB_NATIVE_CONTINUATION_AFFINE_OBSTRUCTION_AND_APPROXIMATION.md) allows arbitrary finite-dimensional affine lifts of its full continuous probability-displacement service with an affine ten-coordinate readout. Its lawful intervals, quantum preparation, square-root output functions and continuum of displacements are different from (69.1), (69.2) and the two literal original-path blocks. That obstruction supplies neither this fixed-block classification nor the adaptive bounded-digit prefix restriction.

[Returned Arithmetic Behavior and Serial Continued Use](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.md) supplies positive closing from natural-pair sources, the actual fixed-modulus reply $\gcd(2a+3b,H)$, actions $(a,b)\mapsto(b,a+b)$ and $(a,b)\mapsto(a+1,b)$, and same-handle continuation under its explicit service/completion premises. Its immutable acquired entry and maintained current residue are not LAB's addressed alpha/beta constructors or an earned original rational-path field. [Native Full Source Producer](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.md) likewise assumes its own material observations and retained production information; a source read or retained trace there does not become a free guard or erased journal here.

The centered circular `OriginalM5` source and its full-word consumer in [M5SourceRows](../../../Blueprint/D5/S3/Combinatorics/Circle/M5SourceRows.md) and [M5FullWordConsumer](../../../Blueprint/D5/S3/Combinatorics/Circle/M5FullWordConsumer.md) have their own source-row, extrema and capacity hypotheses. The exact-real quadratic-report and private-randomization models of [Private-Randomization Quadratic Clock, §§9–10](FIB_UNCALIBRATED_QUADRATIC_CLOCK_PRIVATE_RANDOMIZATION.md) quantify compatible report worlds, error budgets and decision losses, rather than this original path command service. The original critical Heisenberg zero-mode subspace of [Boundary Geometry Continuation III Appendix, §109](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md) concerns its stated continuous differential operator, weights and maximal zero domain. None of these source hypotheses identifies its objects, operations, observations or resources with both actual sources of Definition 69.1. Their arithmetic, clock or geometric terminology is insufficient to transport a verdict or a resource bound between those models.

[Predictive Waves and Relational Spectra II, Definitions 39.1–39.2 and Theorems 39.3–39.4](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_II.md) fixes the actual five-dimensional Kraus instrument, a known mixing angle, retained labels and a prescribed terminal binary measurement. Its exact operator/probability version retains complete joint weights for the same instrument and does not turn finite samples into exact probabilities or supply an extra input-preparation menu. The resulting qutrit observation-space and successor-fibre criteria act on complex CPTP channels; they are not a correspondence with the LAB guards or the rational affine pulse field. Similarly, [Entanglement Buffer Availability Lower Bound](../../../Blueprint/D5/S3/Quantum/Decoherence/EntanglementBufferAvailabilityLowerBound.md) compares its supplied discrete-time probability/fidelity formula under admissible purification coefficients; its memory count is not the complete settled auxiliary alphabet of Definition 73.2. No result in either conditional domain is contradicted or duplicated by (71.2) or (74.1).

**Limits 76.3 (two restrictions and an unfilled bridge).** The fixed-block result says that a route-independent encoding of all repeatable native coordinate pairs into the original path field by two fixed original-command blocks must collide, and gives every collision kernel and its actual native/path distinguishing consequences. It does not prohibit route-dependent fields, adaptive blocks or properly charged auxiliary records. The adaptive result says that a cofinal independent native layer encoded by injective bounded-digit pulse words with canonical settled fields needs at least $\lceil2^k/R\rceil-1$ pulses when all selected settled auxiliary inputs jointly have at most $R$ values. It does not prohibit other adaptive encodings, other origins or menus, or a surviving archive whose capacity violates that premise. The paid attainment proves only this latter coordinate tradeoff in an explicitly augmented two-source installation.

A common-source native-to-original-path installation remains a separate obligation: identify one actual initialization and reference binding, match every claimed legal operation and refusal, complete outputs and acknowledgements, successor states and continuing rights, and account for all coexisting field, source, control, record and backing resources. None of the endpoint arguments constructs this identification. Recovering a native causal order or current subset does not recover an arbitrary erased serial record; a surviving producer or archive must be included as material and, when selected, as input. No quantum/window/future-closure correspondence is inferred. The original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization and final-no-Ready statements keep their own hypotheses and unresolved boundaries. The sustained four-expression objective requires these actual-source and task correspondences beyond the two translator-class restrictions proved here.

## 追加锚（本行以下为增补区）

## 77. Uniform tree laws and rational symmetric endpoint compatibility

**Definition 77.1 (the actual uniform source and the compatibility question).**
Let $\Gamma=(V,E)$ be a nonempty finite connected simple tree, let $N=|V|$,
and suppose every vertex has degree at most three. Let $o\in V$ be an
actually selected vertex, $e_o$ its unit coordinate vector, and $A$ the
unit, zero-diagonal adjacency matrix of this same tree. Fix

$$
a\in\mathbb Q,\qquad c\in\mathbb Q_{>0},\qquad
T=aI+cA,\qquad m_k=e_o^{\mathsf T}T^ke_o\quad(k\ge0).
\tag{77.1}
$$

Here $a$ may be zero or negative. No positivity or contraction of $T$ is
assumed. A singleton is a path whose sole vertex is an endpoint. For a
path with at least two vertices, its endpoints are its degree-one
vertices. The selected port is part of the question; recognizing an
unrooted path does not put an interior port at an endpoint.

A **rational symmetric endpoint competitor** is a nonempty finite matrix
$J\in\mathbb Q^{n\times n}$, of arbitrary order $n$, with diagonal entries
$\alpha_i\in\mathbb Q$, adjacent entries
$J_{i,i+1}=J_{i+1,i}=\gamma_i>0$, and all other off-diagonal entries zero.
The port is $e_0$. For $n=1$ the adjacent-link condition is empty.
Compatibility means exactly

$$
e_0^{\mathsf T}J^ke_0=m_k\qquad\text{for every }k\ge0.
\tag{77.2}
$$

This definition asks for an exact scalar impulse response, including
normalization $m_0=1$. It assumes no correspondence of allocation names,
other ports, constructors, source dimensions, rights or physical costs.
There is no supplied full-response oracle: the $m_k$ in this algebraic
definition are mathematical quantities. Section 80 specifies which of
them an actual observer can earn.

**Definition 77.2 (a fixed chain recurrence).** Put

$$
Q_{-1}(y)=0,\quad Q_0(y)=1,\quad
Q_{j+1}(y)=yQ_j(y)-Q_{j-1}(y),\qquad
p_j(z)=Q_j((z-a)/c),\quad v_j=p_j(T)e_o.
\tag{77.3}
$$

Thus $v_{-1}=0$, $v_0=e_o$ and $v_{j+1}=Av_j-v_{j-1}$. Write
$p_j(z)=\sum_{i=0}^j q_{j,i}z^i$. Symmetry of this actual $T$ gives

$$
\begin{aligned}
G_{ij}&:=\langle v_i,v_j\rangle
 =\sum_{s=0}^i\sum_{t=0}^j q_{i,s}q_{j,t}m_{s+t},\\
D_j&:=\langle v_j,Tv_j\rangle
 =\sum_{s,t=0}^j q_{j,s}q_{j,t}m_{s+t+1},\\
h_j&:=G_{jj}=\|p_j(T)e_o\|^2.
\end{aligned}
\tag{77.4}
$$

All coefficients and sums are rational. In particular $h_j$ uses only
moments through $2j$, and $D_j$ uses only moments through $2j+1$.
These are local calculations on a supplied or earned prefix, rather than
additional observation primitives. The moment inner product and its
three-term reconstruction are the classical tools of
[Teschl, §2.5, (2.94)–(2.118) and the finite-support paragraph](../../../Library/Dynamics/teschl2000jacobi.md).
The source-specific issue below is the rationality of the normalized
symmetric links forced by this particular tree.

## 78. The first departure gives the complete compatibility classification

**Lemma 78.1 (the first departure on the actual tree).** There is a first
integer $r\ge1$ for which $h_r\ne1$. Exactly the following cases occur.

1. If $\Gamma$ is a path and $o$ is an endpoint, then $r=N$ and $h_r=0$.
2. If $\deg(o)\in\{2,3\}$, then $r=1$ and $h_r=\deg(o)$.
3. Otherwise, if the first case does not hold, $o$ is a leaf. Follow its
   unique chain until the first degree-three vertex, at distance $d$.
   Then $r=d+1$ and $h_r=2$.

For every case, $v_0,\ldots,v_{r-1}$ are the successive distinct unit
vectors of the initial stem. Consequently

$$
G_{ij}=\delta_{ij}\quad(0\le i,j<r),\qquad
D_j=a\quad(0\le j<r),\qquad 1\le r\le N.
\tag{78.1}
$$

**Proof.** If $N=1$, $A=0$, so $v_1=0$ and the first case holds with
$r=1$. If $\deg(o)$ is two or three, $v_1=Ae_o$ is the sum of its distinct
neighbor vectors. Its squared norm is that degree, giving the second
case and the one-vector stem $v_0=e_o$.

In the remaining nonsingleton case $o$ has degree one. Set $v_0=e_{z_0}$,
$z_0=o$. While the chain has neither terminated nor forked, let $z_{j+1}$
be the unique neighbor of $z_j$ other than $z_{j-1}$. Starting with
$v_1=e_{z_1}$, the recurrence gives

$$
Ae_{z_j}-e_{z_{j-1}}=e_{z_{j+1}}.
\tag{78.2}
$$

There is no repeated chain vertex, since that would give a cycle. At an
endpoint $z_{r-1}$ the next vector is zero. If a degree-three vertex is
first reached at $z_{r-1}$, with its two forward neighbors $w_1,w_2$, the
next vector is $e_{w_1}+e_{w_2}$, of squared norm two. Finiteness forces
one of these events. If the chain terminates without a fork, it exhausts
$V$: a path from any additional vertex to the chain would require an
additional incident edge at a chain vertex. It is therefore exactly the
endpoint path, of $r=N$ vertices. Conversely an endpoint path has exactly
this recurrence and termination. These observations prove the exhaustive
cases, first-departure assertion and bound on $r$. Distinct unit vectors
are orthonormal, and the diagonal of $T$ is $a$, proving (78.1). $\square$

At $r=1$, a value two can mean an interior port of a path; it need not
mean that the tree branches. The certificate concerns endpoint-port
compatibility. Only the leaf-started case with $r>1$ identifies a first
forward fork at distance $r-1$.

**Lemma 78.2 (rigidity of every positive symmetric competitor).** Suppose
a finite real symmetric positive-link Jacobi matrix $J$ has the same
moments as (77.1) through index $2r$, where $r$ is from Lemma 78.1. Its
order is at least $r$. Its first $r$ diagonals are $a$, and its first
$r-1$ links are $c$. If its order is exactly $r$, then $h_r=0$. If its
order is larger, its next link satisfies

$$
\gamma_{r-1}^2=c^2h_r.
\tag{78.3}
$$

In particular $h_r=0$ forces order exactly $r$ and uniquely specifies $J$.

**Proof.** Let $w_j=p_j(J)e_0$ and $w_{-1}=0$. Moment agreement and
(77.4), (78.1) give orthonormal $w_0,\ldots,w_{r-1}$ and
$\langle w_j,Jw_j\rangle=a$ for $j<r$. All these identities use indices
at most $2r-1$. The squared norm of $w_r$ is $h_r$ by the last moment.

Start with $w_0=e_0$. Its diagonal pairing fixes $\alpha_0=a$. If another
unit polynomial vector is required, the recurrence gives
$w_1=(\gamma_0/c)e_1$; an absent coordinate would give zero. Unit norm
and $\gamma_0,c>0$ force $\gamma_0=c$ and $w_1=e_1$. Inductively, if
$w_j=e_j$, the preceding links are $c$, and the preceding diagonals are
$a$, its diagonal pairing fixes $\alpha_j=a$ and

$$
w_{j+1}=((J-aI)/c)e_j-e_{j-1}
       =(\gamma_j/c)e_{j+1}.
\tag{78.4}
$$

For $j=0$ the subtracted vector is zero. If $J$ ends at $j$, the right
side means zero. Thus for $j+1<r$, the required unit norm forces the next
coordinate, link $c$ and vector $e_{j+1}$. This proves the order bound
and all preceding coefficients, including $\alpha_{r-1}=a$ using its
own diagonal pairing. Applying (78.4) once more gives zero at order $r$
or norm squared $\gamma_{r-1}^2/c^2$ at larger order. Positivity excludes
a zero norm in the latter case. This proves every assertion. $\square$

**Theorem 78.3 (rational symmetric endpoint compatibility).** For every
source and port of Definition 77.1,

$$
\begin{aligned}
&\text{there is a rational symmetric endpoint competitor satisfying (77.2)}\\
&\hspace{15mm}\Longleftrightarrow\quad
  \Gamma\text{ is a path and }o\text{ is an endpoint}.
\end{aligned}
\tag{78.5}
$$

If the condition fails, the finite moments $m_0,\ldots,m_{2r}$ already
exclude every such competitor, of every order. If the condition holds,
these moments uniquely specify its order $N=r$ and matrix

$$
J_N=aI_N+cA_{P_N}.
\tag{78.6}
$$

**Proof.** In the negative case $h_r=b\in\{2,3\}$. Lemma 78.2 excludes a
shorter or terminating competitor, and otherwise forces
$(\gamma_{r-1}/c)^2=b$. No positive rational has square two or three.
Indeed write it as $u/v$ in relatively prime positive integers. From
$u^2=bv^2$, the prime $b$ divides $u$, and substituting $u=bw$ makes $b$
divide $v$, a contradiction. Hence even this finite prefix cannot match
a rational symmetric positive-link competitor.

In the positive case enumerate the actual path vertices by their distance
$0,\ldots,N-1$ from $o$. The associated permutation $U$ satisfies

$$
Ue_o=e_0,\qquad UT=J_NU.
\tag{78.7}
$$

It gives (77.2) and rational positive links $c$. Lemma 78.2 with $h_N=0$
forces every matching competitor to have order $N$, every diagonal $a$
and every link $c$, proving the finite-prefix uniqueness assertion.
The singleton uses the same argument, with no adjacent links. $\square$

**Proposition 78.4 (sharpness of the negative moment prefix).** In the
negative case the rational endpoint path on the $r$ initial stem vertices,
with the same $a,c$, has moments $\widehat m_k$ satisfying

$$
\widehat m_k=m_k\quad(0\le k<2r),\qquad
m_{2r}-\widehat m_{2r}=bc^{2r},\qquad b=h_r\in\{2,3\}.
\tag{78.8}
$$

**Proof.** For $r=1$ the stem is just $o$ and has $b$ omitted neighbors.
For $r>1$ its last vertex has the two omitted forward neighbors from
Lemma 78.1, so $b=2$. Expand $(T^k)_{oo}$ into walks with diagonal stays
of weight $a$ and edge traversals of weight $c$. This is the weighted
matrix-power expansion, whose unit-edge counting substrate is the pinned
[Mathlib adjacency-power walk theorem](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean),
`SimpleGraph.adjMatrix_pow_apply_eq_card_walk`.

A closed walk using an omitted vertex must go at least $r$ edges outward
and $r$ edges back. Thus none contributes before degree $2r$. At that
degree it must go directly along the stem, take one of the $b$ omitted
edges, and return directly. These are exactly $b$ walks of weight
$c^{2r}$. They have no diagonal stays, even when $a$ is signed. All
remaining walks occur in both trees with identical weights. This proves
(78.8) without a positivity assumption on $a$. $\square$

## 79. Rationality boundaries and the material-tree specialization

**Proposition 79.1 (the degree-four boundary).** If the degree restriction
is dropped, a branching unit tree can have a rational symmetric endpoint
competitor. For the star with four leaves and port at its center, put
$u=\frac12\sum_{\ell\text{ leaf}}e_\ell$. Then $e_o,u$ are orthonormal,
$Ae_o=2u$, $Au=2e_o$, and the restriction of $T$ to their invariant span is

$$
\begin{pmatrix}a&2c\\2c&a\end{pmatrix}.
\tag{79.1}
$$

It has all the same port moments, although the tree has five vertices.

**Proof.** The four disjoint leaf coordinates give $\|u\|^2=1$ and
$\langle e_o,u\rangle=0$. The two adjacency identities follow by summing
the four center-leaf incidences. They prove invariance and (79.1), so
all powers applied to $e_o$ have the asserted same scalar. $\square$

The distinction from real tridiagonalization is essential. Classical
normalized Lanczos, in the exact convention attached to
[Static Seams, Theorem 29.8](AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md),
represents the cyclic subspace of a finite real symmetric $T$ by a real
positive-link Jacobi matrix, stopping at its first zero residual. Its
link at the departure in Lemma 78.1 is $c\sqrt b$. Theorem 78.3 excludes
rational symmetric links there; it does not exclude that real matrix.
A rational monic orthogonal basis can instead have opposite entries
$1$ and a rational squared-norm ratio. The precise distinction is already
present in [Coefficient-Driven Jacobi Characteristic Polynomial](../../../Blueprint/D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.md),
including its monicity, positive-norm and tridiagonal helpers and
[owning Scribe](../../../Blueprint/D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.scribe.cs).
Its matrix is not asserted symmetric in that monic basis.

For example, at the center of the three-leaf unit star the basis
$e_o,\sum_\ell e_\ell$ gives the rational nonsymmetric matrix
$\left(\begin{smallmatrix}a&3c\\c&a\end{smallmatrix}\right)$ on the cyclic
span. The adjacency sends the first vector to the second and the second
to three times the first, proving the assertion and its same port
moments. Orthogonal unit normalization replaces its links by
$c\sqrt3$. This supplied normalization principle is an illustration of
why a rational nonsymmetric response is outside Definition 77.1.
Neither cyclic representation identifies the invisible orthogonal
complement, all native coordinates or a constructor interface.

**Corollary 79.2 (actual LAB material, with no free change of port or law).**
Let $t$ be any reachable term of
[Atomic Generation Acquisition, Definitions 17.1 and 17.3](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md).
Use its actual material vertices $C(t)$ and their unit adjacency in
(77.1). At the original root, compatibility holds exactly for $t=\alpha$
or $t=\beta$. If $t$ has a logical branch below the root, compatibility
fails for every selection of a material vertex as port. More generally
the exact criterion at any granted port is (78.5).

**Proof.** The material encoding has a terminal for $\alpha$, a unary root
and terminal marker for $\beta$, and a binary root with the two material
children for a branch. Its underlying graph is a finite connected simple
tree of maximum degree three. Alpha and beta are endpoint paths at their
original roots. Every branch term has degree two at that root, which
fails the endpoint-port condition even when the underlying material graph
is a path. A logical branch below the root has its parent edge and its
two child edges, hence degree three. Its material tree is not a path,
so no selected port satisfies (78.5). Apply Theorem 78.3 to these actual
vertices and coefficients. $\square$

The corollary is conditional on the field law and actual scalar port
being installed on those vertices. LAB's addressed $P/S$ guards do not
supply a scalar field, a full Reset, a different port binding or the law
$aI+cA$. In the unit native field specialization $a=0,c=1$, the law is
exactly $A$; no contraction is inferred. If a contracting uniform example
is required, $a=1/2,c=1/8$ supplies it explicitly. Indeed

$$
|z^{\mathsf T}Az|
 \le\sum_{\{v,w\}\in E}(z_v^2+z_w^2)
 =\sum_v\deg(v)z_v^2\le3\|z\|^2,
\qquad \tfrac18I\le T\le\tfrac78I.
\tag{79.2}
$$

The first inequality follows from $2|z_vz_w|\le z_v^2+z_w^2$.
Thus $0<T<I$ in that example, on every tree under consideration. This is
an additional uniform law, not an implementation of it by LAB growth.
The condition $c>0$ is also substantive: at $c=0$ every tree has the
same singleton response $m_k=a^k$.

A supplied complete degree-one roster of size at least three already
excludes a path. In particular the public source promise of
[Native Leaf Boundary Acquisition, Definition 1.1](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md)
already settles that negative topology question. The next scalar trial
claims acquisition only in the distinct service without such a roster.

## 80. One reduced scalar service without geometry or order advice

**Definition 80.1 (the actual installation and complete five-command menu).**
Fix one actual tree, port and uniform law from Definition 77.1. Its field
is $x\in\mathbb Q^V$. The observer receives the two public rationals $a,c$,
one authentic opaque port-bound reference, the five call rights below,
exclusive serialization and sufficient owned finite source, arithmetic,
input/output and record backing for each finite run asserted to complete.
It receives no $N$, order cap, incidence data, leaf roster, other port,
logical source code, coefficient list, spectrum, response table or
source-dependent advice. Reference spelling, acknowledgement, timing,
work, storage-capacity and parser behavior expose no further source
information. The port is fixed; there is no selector or growth operation.
The initial cut for the classification task is full field zero.

| Complete valid command | Actual field successor | Complete reply |
| --- | --- | --- |
| Reset | $0$ on every actual cell | fixed acknowledgement |
| Add$(u)$, $u\in\mathbb Q$ | $x+ue_o$ | fixed acknowledgement |
| Tick | $Tx$ | fixed acknowledgement |
| Read | $x$ | the literal reduced rational $e_o^{\mathsf T}x$ |
| Hold | $x$, with updates prevented during local processing | fixed acknowledgement |

A requested Tick ends the preceding held interval and performs exactly
one update. There are no autonomous updates between calls and no other
writer. Reset is calibrated on the whole actual field, including unknown
internal cells. The trial of §81 actually executes it and Add$(1)$ to
earn a unit preparation. That trial also works from an arbitrary old
field after this Reset; the every-source lower horizon in §82 is stated
from the specified zero cut, not for arbitrary informative entry fields.

Commands and rational operands use a fixed exact serialization. Every
complete ill-formed packet returns a fixed rejection and leaves the
field unchanged; an incomplete packet retains its actual pending input
and has no completed reply or field effect. Those pending bytes and
rejections carry no hidden source metadata. Absent rights disable the
call, rather than returning a numerical source observation. Calls under
the theorem have their installed rights and finite input/output progress.
All complete replies, acknowledgements, End/return framing and local
commits are processed before the next completed cut. They and their
literal widths are paid. These are conditions of the mathematical
service, not a conformance certificate obtained from its scalars.

**Definition 80.2 (independent data meanings and the recovery task).**
Space is the actual incidence metric, coefficients and present field,
modulo graph isomorphisms carrying the selected port to the selected
port. Time is the serial command order and commanded Tick ordinal since
the actual unit preparation, excluding Hold duration and external wall
time. Boundary is the current literal scalar at that one bound port.
Memory is the observer's finite earned scalar prefix, counter,
polynomial work data and returned certificate, together with its retained
actual reference, rights and their backing. Only Memory retains that
trial record. Space and the instantaneous Boundary are not given copies
of its command or output history.

The acquisition task is to report whether (77.2) is possible and, in the
positive case, the path order and its current distance-coordinate field.
A negative report owes a finite obstruction, not the rest of the tree.
This is recovery of a specified spatial/port eligibility property from
paid temporal boundary evidence. It asserts no mutual inverse between
these four data types, no recovery of an erased old journal and no
acquisition of raw labels or authority. The positive continued-use claim
has exactly the menu in Definition 80.1.

## 81. A finite earned certificate and the genuine observation endpoint

**Theorem 81.1 (uniform terminating scalar trial).** There is one fixed
procedure, with no geometry or size advice, for every source of Definition
80.1. Let $r$ be its first departure in Lemma 78.1. The procedure earns
$m_0,\ldots,m_{2r}$ on this actual source, returns the finite certificate
below, and stops held at

$$
x_{\rm out}=T^{2r}e_o.
\tag{81.1}
$$

Its exact successful source-call vector is

$$
(\mathrm{Reset},\mathrm{Add},\mathrm{Tick},\mathrm{Read},\mathrm{Hold})
 =(1,1,2r,2r+1,2r+1).
\tag{81.2}
$$

The output is $\mathrm{Path}(r)$ when $h_r=0$, or
$\mathrm{Incompatible}(r,b)$ when $h_r=b\in\{2,3\}$, accompanied by
$a,c$ and the literal acquired moment prefix. No observation is treated
as leaving the field at the earlier unit origin.

**Proof.** Execute Reset; Add$(1)$; Hold; Read. The state is now $e_o$
and the actual reply is $m_0=1$. At stage $j=1,2,\ldots$, execute twice
Tick; Hold; Read, obtaining the next two moments. While held, form $p_j$
by (77.3) and compute $h_j$ by (77.4). Continue exactly when $h_j=1$.
Lemma 78.1 proves finite termination at $r$, with precisely one of the
three announced stopping values. No bound on $r$ is an input to the
procedure. At each acquired epoch $k$, induction on the actual calls
gives field $T^ke_o$ and Read reply $m_k$. Local calculations under Hold
do not alter it. This proves the endpoint and all counts in (81.2).

The certificate has an explicit finite rational verifier. First check a
positive integer $r$, exactly $2r+1$ rational moment entries, the supplied
rational $a,c$ with $c>0$, and one correctly formed output tag. The public
parameters must be those of the actual installation. Reconstruct
$p_0,\ldots,p_r$ from them and check

$$
\begin{gathered}
m_0=1,\qquad G_{ij}=\delta_{ij}\ (0\le i,j<r),\qquad
D_j=a\ (0\le j<r),\\
h_j=1\ (0\le j<r),\qquad
h_r=0\text{ or }h_r\in\{2,3\},
\end{gathered}
\tag{81.3}
$$

using only (77.4) and the acquired prefix. Check that the tag is
$\mathrm{Path}(r)$ exactly when $h_r=0$, and otherwise is
$\mathrm{Incompatible}(r,h_r)$. The procedure performs these
finite checks before returning; they hold by Lemma 78.1. The $G$ and $D$
checks make explicit all moment pairings used in Lemma 78.2, not just a
squared-norm slogan. In the negative case Lemma 78.2 and the rational-square
argument prove that no competitor matches this very prefix. In the
positive case the actual-tree promise and Lemma 78.1 prove endpoint-path
membership and order $r$; Theorem 78.3 specifies its whole matrix.
The verifier checks the arithmetic implication of the reported prefix.
Its identification of this prefix with actual observations, and the
positive classification of the actual source, retain the installation
and tree-class hypotheses. It does not authenticate those hypotheses.

All arithmetic, checks, output encoding and optional clearing are finite
local work under the last Hold. They use growing actual backing and are
additional to the source-call vector. Unexpected stopping values or a
failed check can be tagged outside the declared promise; neither occurs
on this domain. No termination or complete classification of arbitrary
off-domain instruments is asserted. $\square$

**Theorem 81.2 (positive-branch continued use, and the negative limit).**
After a positive output, the same actual reference and rights support a
full-field predictor for every finite common adaptive continuation of
Definition 80.1, initialized at $J_r^{2r}e_0$. In distance coordinates
its outputs and actual successors agree at every completed cut. On the
negative branch the certificate retains actual callable access at (81.1)
but does not identify the whole tree or initialize a full-field predictor.

**Proof.** For a positive result $r=N$ and the same-specimen permutation
$U$ of (78.7) is defined on every actual cell. Compute locally, while
held, $\widehat x=J_N^{2N}e_0$. Equation (81.1) gives $\widehat x=Ux$.
For Reset set $\widehat x=0$; for Add$(u)$ set
$\widehat x=\widehat x+ue_0$; for Tick set
$\widehat x=J_N\widehat x$; for Read and Hold leave it unchanged. Predict
$e_0^{\mathsf T}\widehat x$ on Read and the fixed acknowledgement on the
other valid commands. The source's five successor formulas and (78.7)
preserve $\widehat x=Ux$ in each case. Complete rejections preserve both
fields; incomplete frames have no completed successor and retain their
actual pending bytes. Commit updates and output processing serially.
Equal prior replies select the same next command and rational operand
under a common adaptive policy, so induction proves the complete claim,
including a common source-independent random tape when used. This is
the supplied predictor-induction principle of §40 applied at a genuinely
earned uniform path, with the present acknowledgement-only Tick and
additional Reset explicitly respected. It creates no new right.

On a negative source choose a leaf beyond or at the first departure
frontier and attach one further vertex to it. Such a leaf exists in a
forward component in Lemma 78.1; in the $r=1$ case choose any leaf other
than an interior port. Its distance from $o$ is at least $r$. The extension
is still a finite simple subcubic tree, with the same $a,c$, and is still
negative. Reaching the new edge and returning requires at least $2r+2$
steps, so its moments through $2r$, its returned certificate and all
trial replies agree with the original negative source. Its order differs.
If the extended old leaf is at distance $L$, their moments first differ
at $2L+2$: the unique new outward-and-return walk contributes
$c^{2L+2}$ and has no stays. A later unit trial can therefore distinguish
their scalar continuations as well. Thus the finite negative record does
not identify the full tree or a uniform complete predictor for both. The
actual experiment has still advanced its own specimen to (81.1), with
its own retained access. No local reconstruction of its remaining field
or acquisition of other ports follows. $\square$

**Proposition 81.3 (one simultaneous resource account).** The trial and
finite verifier admit an exact rational implementation whose material
and work are finite for every actual $N,a,c,r$. Its source-call count
is (81.2), without a claim of minimum Reads, bits or total work. The
following sufficient layout charges source, records and arithmetic on
that one run.

Compute $D$ as the least common multiple of the positive reduced
denominators of the public $a,c$, charging that local arithmetic. Write
$u=Da\in\mathbb Z$, $v=Dc\in\mathbb Z_{>0}$, and put

$$
H=|u|+3v,\qquad
B=2+\lceil\log_2(1+D)\rceil+\lceil\log_2(1+H)\rceil.
\tag{81.4}
$$

At epoch $k$, every actual cell and scalar has a reduced rational word
of $O((k+1)B)$ bits. All $2r+1$ scalar records use $O(r^2B)$ numerical
bits. Retaining every coefficient array $p_0,\ldots,p_r$ and performing
(81.3) takes a sufficient $O(r^3B)$ numerical-bit layout and $O(r^4)$
rational arithmetic operations at $O(rB)$ operand widths. The physical
field and a separate Tick buffer use $O(N(r+1)B)$ numerical bits at the
observation endpoint; source incidence, address, reference, control,
framing and authority backing are additional. Each actual Tick performs
its actual sparse field update, for $O(Nr)$ rational arithmetic operations
over the trial. These counts are added, not interchanged.

**Proof.** Let $M=uI+vA$. It is integral and each absolute row sum is at
most $H$. Thus $\|M^ke_o\|_\infty\le H^k$ and
$T^ke_o=D^{-k}M^ke_o$. A reduced numerator is no larger in magnitude
than $H^k$, and its denominator divides $D^k$, giving the word bound.
Summing it over the observed indices gives the scalar-record bound.
No internal cell values were observed merely because they enter this
physical-material account.

For polynomial widths put $R_j(z)=v^jp_j(z)$. These are integer
polynomials satisfying

$$
R_0=1,\quad R_1=Dz-u,\quad
R_{j+1}=(Dz-u)R_j-v^2R_{j-1}.
\tag{81.5}
$$

If $K=1+D+|u|+v^2$, induction bounds their coefficient absolute sums by
$K^j$. Since $\log_2K=O(B)$, each coefficient of $p_j=R_j/v^j$ has
$O((j+1)B)$ reduced bits. There are $O(r^2)$ retained coefficients.
For every finite sum in (81.3) a common denominator divides
$v^{2r}D^{2r}$; the coefficient-sum bound and the preceding moment bound
also bound the numerator of every partial sum by a number with $O(rB)$
bits. Reducing after each operation therefore gives the asserted operand
widths. Computing the polynomials and the successive $h_j$ requires at
most $O(r^3)$ rational operations. Checking all $r^2$ Gram entries by
the displayed double sums requires at most $O(r^4)$; the diagonal tests
require at most $O(r^3)$. This proves a sufficient, unoptimized finite
arithmetic account, with the genuine multiplication, reduction and
comparison work at those widths still charged.

A tree has $N-1$ edges. Updating every cell by $a$ times its value plus
$c$ times its neighbor sum is $O(N)$ rational operations per Tick and
uses its real source and buffer cells. Reset writes all $N$ cells. Add
writes the bound-port cell. In addition to the stated numerical arrays,
charge the actual $N$ vertices, $N-1$ links, incidence machinery, calibrated
Reset, exact I/O, Hold control, literal input and output frames, counters,
program, port reference, rights and all backing. The $4r+3$ fixed
acknowledgements and $2r+1$ scalar replies are processed, as are the
returned certificate and its copies. Clearing costs its actual writes;
keeping an archive costs its actual retained storage. A positive predictor
uses a separately paid $N$-cell record and local sparse multiplications
to compute $J_N^{2N}e_0$, then pays its later operations. No component is
silently supplied by another view or by a short handle. $\square$

For $a=1/2,c=1/8$ take $D=8,u=4,v=1$. Every observed denominator divides
$8^k$, and its nonnegative numerator is at most $7^k\le8^k$ before
reduction. Linear growth of individual exact word widths does not give
a lifetime-uniform precision or storage bound, nor remove the unknown
actual source material from the account.

## 82. The sharp horizon in this exact scalar information model

**Lemma 82.1 (every adaptive scalar uses only earned-age moments).** In
Definition 80.1, start at full zero. At a completed cut let $t$ be the
number of Ticks since the most recent Reset, and let Add$(u_\ell)$ have
occurred at its Tick epochs $s_\ell\le t$. If there has been no Reset,
use the initial zero cut. Then the actual state and scalar are

$$
x=\sum_\ell u_\ell T^{t-s_\ell}e_o,\qquad
e_o^{\mathsf T}x=\sum_\ell u_\ell m_{t-s_\ell}.
\tag{82.1}
$$

Consequently two actual installations with the same public $a,c$, matched
opaque context and moment prefix through $K$ have identical complete
observations and adaptive command choices until more than $K$ total
Ticks have been executed, starting from their respective zero fields.

**Proof.** Zero has the empty sum. Add appends the exponent-zero term,
Tick increases all ages by one, Read and Hold preserve every term, and
Reset removes all terms and restarts the local epoch. Complete rejections
do nothing and incomplete frames make no completed change. Induction on
actual calls proves (82.1) separately on each actual source. Every age
is at most the total Ticks on that run, even with repeated Resets.

For identical command and input prefixes, (82.1) gives identical scalar
replies within the stated moment prefix. All other complete replies are
fixed. Inductively identical prior observations give identical adaptive
choices, local records and stopping decisions. This includes arbitrary
finite rational amplitudes, repeated Reads, local computation and a
common source-independent random tape. No fields from different
installations are added together; the sums in (82.1) are the jointly
realized pulses of one actual run. $\square$

**Theorem 82.2 (every-source exact classification horizon).** Consider
procedures uniformly correct on all sources of Definition 80.1 from its
zero cut. For each negative source, with first departure $r$, no such
procedure can issue an exact compatibility classification before its
$2r$th actual Tick. For each positive $N$-path source it cannot do so
before its $2N$th actual Tick. This holds almost surely for a uniformly
zero-error randomized procedure. The bound allows every command in the
reduced menu, arbitrary adaptive rational inputs and arbitrary finite
local processing. Theorem 81.1 attains the bound on each source.

**Proof.** Fix an actual negative source first. Its $r$-vertex stem path
in Proposition 78.4 is a positive rival with the same $a,c$ and moments
through $2r-1$. Give the rival its own zero field, corresponding genuine
endpoint binding and the same public observable context. These are two
alternative actual installations, not a claimed identity of their
material. Lemma 82.1 makes all complete transcripts equal before the
$2r$th Tick. The required binary classifications are opposite, so an
exact uniformly correct procedure cannot stop there on the negative
source.

Now fix any positive endpoint path of $N$ vertices. Attach two new leaves
to its far endpoint. For $N\ge2$ that vertex changes from degree one to
three; for $N=1$ the old singleton changes from degree zero to two.
The resulting tree is subcubic and negative at the old port. It has first
departure $r=N$, $h_r=2$, and the original positive path is its truncated
stem. Proposition 78.4 again gives equality through $2N-1$ and first
difference $2c^{2N}$ at $2N$. The same transcript argument prohibits early
certification on this individually fixed positive source.

For randomization couple the same source-independent tape on each fixed
pair. A positive-probability early exact report on the first source has
the same report on the rival. Removing the null error events on that
fixed pair makes this a positive-probability wrong report on one source,
contradicting uniform zero error. Thus the lower horizon holds almost
surely. The paid trial reaches exactly $2r$ or $2N$, respectively, and
returns the justified answer there. $\square$

The horizon concerns commanded source Ticks in this information model.
It is not a lower bound of $2r+1$ Reads, an input-amplitude bound, a
minimum bit/work/reset count, or a total resource ordering. A supplied
roster, order cap, accessible coefficient, additional scalar port,
timing channel or informative entry field changes the evidence available
in Lemma 82.1. Such a different service needs its own lower-bound proof.
The contracting instance in (79.2) preserves both rivals, so this horizon
also holds in that explicitly uniformly enclosed subclass. A different
extra spectral restriction must be checked on the rivals before the
bound is transported to it. Finite precision is not an assumption here:
every equality, norm and zero test uses literal exact rational data.

## 83. Source correspondence and the remaining common-process boundary

**Definition 83.1 (the source-relative mathematical scope).** The
classification (78.5), finite first-departure certificate and paid sharp
horizon constitute a `repo-derived` synthesis for the uniform subcubic
source and selected port in (77.1). Moment Gram identities, normalized
Lanczos, finite-support Jacobi reconstruction, walk locality and
predictor induction are `literature-attested` or already supplied
intermediate mathematics. In particular
[Teschl, §2.5, printed pp. 40–44](https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf)
determines squared normalized links and diagonals from the moments and
explicitly handles finite-support breakdown after Theorem 2.13. That
theorem's nonfinite-support hypothesis is not substituted for the finite
paragraph. The pinned
[Mathlib Gram–Schmidt orthogonality, triangularity and span results](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean)
and the coefficient-driven Jacobi source cited in §79 supply the
orthogonal-basis framework. Lemmas 78.1–78.2 identify its actual first
residual and all required prefix pairings for this tree, rather than
asserting a new general tridiagonalization theorem. The
[Hankel Jacobi determinant source](../../../Blueprint/D5/S3/Constants/Moments/HankelJacobiDeterminant.md)
only identifies its determinant-defined candidate; it does not already
identify a recurrence link or remove the rational square-root condition.

Sections 36–41 supply unknown general rational-path acquisition from
an authentic unit field and complete returning-Tick prediction. Sections
59–68 supply the earned later scalar-origin classification and computed
lattice/residue consumer on their specified path images. None of those
pulse-word inverses is the reduced tree-eligibility task, and none is
reproved as a new consumer here. The guard-only recoverable acquisition
and the initialized global-history transaction in
[Atomic Generation Acquisition II, §§68–83](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md)
have their own actual $P/S$ sources, represented or original request
services, preparation and retained records. They do not install the
scalar menu or uniform law of §80. The two translator restrictions in
§§69–76 likewise have separate paired-source hypotheses. They are not
premises that identify this moment competitor with a native constructor
or that turn endpoint compatibility into an acquisition or total-cost
conclusion.

The exact distinctions are as follows. Existence is (78.5).
Identifiability is endpoint-path eligibility and, on its positive branch,
$N$ and distance-coordinate coefficients within the declared class.
Acquisition is the real trial (81.2), with its earned prefix and changed
field. Certification is the finite calculation (81.3) under the actual
source/observation hypotheses. Continued predictive use is Theorem 81.2
on the positive branch, with the actual advanced field and original
reference; the negative branch retains access and a finite obstruction.
No numerical computation grants a new binding, selector, right or source
conformance guarantee. Source and observer resources coexist as in
Proposition 81.3; this is not a scalarized resource optimum.

Compatibility in (77.2) is deliberately a scalar-response condition.
With zero preparation, its complete five-command scalar behavior follows
from (82.1); conversely a paid unit trial exposes the moments. For the
positive tree case (78.7) additionally proves an actual full-field
coordinate permutation, carrying every declared command, complete output
and successor. That stronger correspondence is proved because this tree
is an endpoint path. It is not inferred from an arbitrary scalar moment
match or from real cyclic tridiagonalization. Neither correspondence
contains native $P/S$ growth, other raw labels or an unrestricted journal.
The acknowledgement-only Tick of §80 is also different from §36's
returning Tick. The macro Tick; Read consumes an additional actual call
and acknowledgement; an earned law does not erase that difference of
complete interfaces.

The boundary assumptions are a finite connected simple unit tree,
uniform rational $a,c$ with $c>0$, degree at most three, a genuine selected
unit port, exact data, and a rational symmetric competitor with every
adjacent link positive. Nonuniform weights, general graphs, real or
algebraic symmetric links, rational nonsymmetric forms, other inner
products, nonlinear representations and task restrictions remain outside
the exclusion. Proposition 79.1 prevents replacing this domain by
unqualified branching. A root or port change still needs its own actual
binding and rights. No four-way recovery of the independent data in
Definition 80.2 is asserted: an instantaneous boundary value is not a
whole acquired response record, and only the observer Memory here retains
the finite trial evidence.

A common actual process joining native alpha/beta constructors, the
original rational path and quantum phase/window services still requires
its initialization, legal operations, complete outputs and successors,
selection, observation and simultaneous resource correspondence. No such
native/path realization, quantum correspondence, future-closed
translation, physical authenticity or universal minimal-generator claim
is supplied by this compatibility theorem. The original fixed-$G_{\rm gc}$,
original-$Q$, parked-consumer, unchanged-initialization, final-no-Ready
and erased-history claims retain their exact scopes. The scalar trial
recovers neither an arbitrary erased serial record nor a prohibited old
initialization. The full four-expression objective therefore retains
these separate common-source and continuation obligations.

## 追加锚（本行以下为增补区）

## 84. The full bounded scalar alphabet at every rational origin

**Definition 84.1 (the scalar task and its suppliers).** Use the original
one-cell source of §§59–62, with its authentic acquisition and installed
Read, returning Tick, authorized rational Add and Hold. Its earned law is
$\lambda=r/s$, where $r,s$ are coprime integers and $1\le r<s$.
Fix a reduced, actually earned and retained origin $v=p/q$, where
$p\in\mathbb Z$, $q\ge1$, $\gcd(|p|,q)=1$, and zero is written $0/1$.
The alphabet here is the entire $D_s=\{0,\ldots,s-1\}$.
For every chronological word $u\in D_s^L$, including $L=0$, execute each
digit literally as Tick; Add$(u_i)$; Read. Its endpoint is

$$
X_v(u)=\lambda^L v+
 \sum_{i=0}^{L-1}u_i\lambda^{L-1-i}.
\tag{84.1}
$$

The favorable direction of Theorem 60.1, the fixed-length inverse of
§61.1, and the reciprocal converse of §61.2 are suppliers. In particular,
fixed-length injectivity holds for every $v$, with no favorable-origin
hypothesis. The missing direction concerns bounded digits when $r>1$;
a collision using unrestricted signed integers does not supply it.

**Lemma 84.2 (a legal finite carrier when $s\mid p$).** Suppose $s\mid p$.
Then $q$ is a unit modulo $s$. For an integer $k$, define

$$
d(k)=[-rkq^{-1}]_s,\qquad
F(k)=\frac{rk+qd(k)}s,\qquad k_0=p/s,
\tag{84.2}
$$

where $[\cdot]_s$ is the least representative in $D_s$ and $q^{-1}$ is
computed by integer Euclid. Put

$$
\begin{aligned}
\ell_0&=\min(k_0,0),\\
U_0&=\max\left(k_0,
 \left\lceil\frac{q(s-1)}{s-r}\right\rceil\right),\\
R&=U_0-\ell_0+1.
\end{aligned}
\tag{84.3}
$$

The integer interval $I=[\ell_0,U_0]\cap\mathbb Z$ contains $k_0$ and is
$F$-invariant. There are effectively obtainable indices
$1\le i<j\le R+1$ such that the two nonempty actual pulse prefixes

$$
u^{(i)}=(d(k_0),\ldots,d(k_{i-1})),\qquad
u^{(j)}=(d(k_0),\ldots,d(k_{j-1})),\qquad k_{t+1}=F(k_t),
\tag{84.4}
$$

have the same endpoint. All their digits belong to the required $D_s$.

**Proof.** Any prime dividing $s$ divides $p$ and therefore cannot divide
$q$. This proves the asserted unit condition. The residue definition
makes $rk+qd(k)$ divisible by $s$, so $F$ is integer-valued. If
$\ell_0\le k\le U_0$, then, using $\ell_0\le0$ and $0\le d(k)\le s-1$,

$$
F(k)\ge r\ell_0/s\ge\ell_0,
\qquad
F(k)\le\frac{rU_0+q(s-1)}s\le U_0.
\tag{84.5}
$$

The last inequality is exactly $(s-r)U_0\ge q(s-1)$. Hence the interval
is invariant. It has $R$ integers, so two of $k_1,\ldots,k_{R+1}$ agree.
Computing these integers and comparing the retained entries finds such
a pair, without an unbounded search.

The actual scalar field after $t$ prescribed pulses is $sk_t/q$. At
the next pulse its update is exactly

$$
\lambda\frac{sk_t}{q}+d(k_t)
 =\frac{rk_t+qd(k_t)}q=\frac{sF(k_t)}q.
\tag{84.6}
$$

Induction starts at $sk_0/q=p/q=v$. Thus the repeated integers give
equal real source endpoints of distinct positive lengths. The proof
includes $p<0$ and $p=0$; no positive-origin assumption or signed-digit
replacement has entered it. $\square$

**Theorem 84.3 (the original full-$D_s$ iff).** For every pair $r,s$ and
every earned reduced origin in Definition 84.1,

$$
X_v:\coprod_{L\ge0}D_s^L\longrightarrow\mathbb Q
\quad\hbox{is injective}\quad\Longleftrightarrow\quad s\nmid p.
\tag{84.7}
$$

Equivalently, the attainable endpoint sets of different lengths are
disjoint exactly when $s\nmid p$. In the other case Lemma 84.2 supplies
an actual bounded-digit witness; its periodic tail gives infinitely many
distinct finite pulse words with a common endpoint.

**Proof.** Here is the precise favorable supplier correspondence. If
$s\nmid p$, some prime $\ell\mid s$ has
$\nu_\ell(p)<e=\nu_\ell(s)$. Because $r$ is coprime to $s$, its
$\ell$-valuation is zero. Reducedness gives
$c=\nu_\ell(v)<e$. A Tick lowers the valuation by $e$; its resulting
valuation is negative, so adding any integer leaves that valuation
unchanged. The elementary unequal-valuation sum identity therefore gives
for every length $L$, including zero,

$$
X_v(u)\ne0,\qquad \nu_\ell(X_v(u))=c-Le.
\tag{84.8}
$$

Thus equal endpoints imply equal lengths. To recall the supplied
fixed-length inverse explicitly, for a given $L$ and $0\le i<L$ set

$$
A_0=\frac{s^Lx-r^Lv}s,
\qquad R_i=r^{L-1-i},
\qquad
u_i=[A_iR_i^{-1}]_s,\qquad
A_{i+1}=\frac{A_i-u_iR_i}s.
\tag{84.9}
$$

For an actual endpoint $A_i$ is the integer
$\sum_{h=i}^{L-1}u_h r^{L-1-h}s^{h-i}$; $R_i$ is a unit modulo $s$.
Consequently the displayed residues recover exactly the actual digits,
and $A_L=0$. This proves fixed-length injectivity at every origin, as
in §61.1. It also proves favorable injectivity once (84.8) has fixed $L$.
For $L=0$ the equation is simply $x=v$.

If $s\mid p$, Lemma 84.2 gives two different positive lengths at the
same endpoint. Determinism of $F$ makes $k_{i+t}=k_{j+t}$ for all
$t\ge0$, and in particular $k_{i+n(j-i)}=k_i$ for every $n\ge0$.
Their finite prefixes therefore have a common endpoint. Each finite
realization still requires its own sufficient finite backing; the
statement does not assert a completed infinite physical execution.
Fixed-length injectivity explains the equivalent length-separation
form. The argument for $r=1$ agrees with the supplied reciprocal case;
only its bounded nonreciprocal extension is needed here. $\square$

## 85. Scalar acquisition, independently meaningful views and common futures

**Proposition 85.1 (earning and using the specified scalar origin).**
Start from the authentic one-cell preparation $b=1$ and run Theorem
37.2. It earns the unknown one-cell law and ends at $\lambda^2$.
With the installed rational Add right, execute

$$
\operatorname{Add}(v-\lambda^2);\ \operatorname{Read};\ \operatorname{Hold}.
\tag{85.1}
$$

The returned scalar is the prescribed rational $v$ and is retained as
the prospective origin. For $s\mid p$, compute Lemma 84.2's orbit table
while held, stop at the first repetition among the positive-indexed
entries, and execute its first $j$ pulse digits on this same specimen.
A final Read; Hold returns its current endpoint. The table's $i$th
entry and the actually visited $i$th pulse cut certify the two prefixes
in (84.4). For $s\nmid p$, an arbitrary actual finite $D_s$ pulse word
from this earned origin is recoverable from its endpoint and the fixed
earned context, without an old length or word archive.

**Proof.** Formula (85.1) changes $\lambda^2$ to $v$ exactly; its Read
is an actual observation and its Hold permits the finite local work.
The unknown-size protocol supplies $N=1$ rather than assuming a
source-size port. Lemma 84.2 and (84.6) verify every subsequent actual
pulse, including its zero digits. In the favorable case (84.8) earns
$L=(c-\nu_\ell(x))/e$ from the nonzero observed endpoint; (84.9) then
gives the word. These calculations do not reread an old reply archive.
An already earned origin produced by a different legal prior segment
can be used directly instead; (85.1) is one paid way to realize every
specified rational origin, not an assertion about all earlier journals.
$\square$

**Definition 85.2 (the scalar expressions).** Fix the actual one-cell
installation, earned $(r,s,v)$, alphabet $D_s$, and a completed pulse
endpoint, allowing subsequent nondestructive Reads and Holds. Its
Boundary is an actual Read at that endpoint: the completed final pulse
Read is sufficient for $L>0$, while $L=0$ uses the paid origin Read.
Protocol 86.1 additionally performs final Read; Hold and uses that
Read. The numerical meanings of the four views are as follows.

| Expression | Independently specified meaning |
| --- | --- |
| Space | The actual single rooted cell, its earned multiplier and its present native scalar $x$ |
| Time | The actual ordered bounded pulse list from the retained origin, including zeros |
| Boundary | The literal endpoint scalar delivered by the paid Read |
| Memory | The earned law and the present sufficient scalar predictor $w=x$ |

The actual bound handle, rights, serialization, retained record encodings
and backing accompany the installed service. They are not recovered as
physical authority from a rational number. The shared context contains
$v$ and the law, and contains no erased Time or unrestricted old journal.
A calculated equal scalar has the same numerical value as Boundary;
only the actual Read supplies that Boundary's observation provenance.

**Theorem 85.3 (scalar recovery and exact scope of the obstruction).**
If $s\nmid p$, all four numerical expressions recover one another on
the actual pulse image, all routes agree, and their equality kernel is
the complete current original continuation kernel. If $s\mid p$,
Space, Boundary and Memory still determine one another and give exact
current continuation, but they do not determine Time. Lemma 84.2 gives
the latter failure on the same actual source with legal inputs.

**Proof.** Space, Boundary and Memory expose the same current scalar
through their independently stated meanings. Time gives (84.1).
Theorem 84.3 gives the inverse from that scalar exactly in the favorable
case. Every route then factors through the same unique word and scalar.
Read already distinguishes unequal current scalars. Equal scalars,
with the same law and installed access, give the same complete next
outputs and successors for every original primitive: Read returns $w$
and preserves it; Tick sends $w$ to $\lambda w$ and returns that new
scalar; Add$(h)$ sends it to $w+h$ and returns its fixed acknowledgement
(and its new scalar only if that declared Add variant includes it);
Hold preserves it and returns its fixed acknowledgement. These formulas
hold for every rational $h$, including inputs outside $D_s$.

Forward the call through the retained real handle, consume all declared
outputs and its completed return, and commit the corresponding scalar
update at each settled cut. Induction on a finite common adaptive
continuation proves equality of all future outputs and actual successors.
An external future selector must be common; two controllers allowed to
consult different old archives need not choose the same next action.
The scalar predictor alone does not erase or identify those archives.

In the unfavorable case the two pulse lists in (84.4) are distinct
Times with equal current fields. Starting at either cut with a common
future action rule gives equal current/future service. Their completed
past pulse lists, elapsed counters, producer tables and emitted reply
archives need not agree. Endpoint-only erased-past recovery therefore
fails; no assertion of equality of the complete past transcripts is
made. Supplying the actual length removes this particular ambiguity,
because (84.9) works at every origin.

Finally, for any two finite pulse lists $u,t$ the actual affine identity is

$$
X_v(ut)=\lambda^{|t|}X_v(u)+
 \sum_{h<|t|}t_h\lambda^{|t|-1-h}.
\tag{85.2}
$$

It follows by induction from the literal pulse update. On the favorable
image it makes the recovered concatenation and the directly executed
concatenation agree. General primitive continuations are covered by the
all-rational predictor; a claim about a word inverse after such a
continuation requires that the resulting cut again belong to its stated
pulse image. $\square$

## 86. One attained scalar witness account

**Proposition 86.1 (the stored-orbit realization).** Use precisely the
following single realization for the unfavorable branch: authentic
acquisition, (85.1), a stored orbit table with a linear comparison scan
among positive-indexed entries, its first repeated index $j$, those $j$
actual pulses, and final Read; Hold. Excluding subsequent optional
continuations, its exact primitive counts are

| Stage | Tick | Add | Read | Hold |
| --- | ---: | ---: | ---: | ---: |
| Authentic one-cell acquisition | $2$ | $0$ | $1$ | $2$ |
| Prospective origin installation | $0$ | $1$ | $1$ | $1$ |
| Actual witness prefix | $j$ | $j$ | $j$ | $0$ |
| Final endpoint read and holding | $0$ | $0$ | $1$ | $1$ |
| Total | $j+2$ | $j+1$ | $j+3$ | $4$ |

There are $2j+5$ mandatory scalar replies and $j+5$ acknowledgements.
The declared post-Add-scalar variant additionally emits $j+1$ scalars.
Here $1\le i<j\le R+1$; the actual witness lengths, widths and stored
entries, rather than a different regenerated or online implementation,
are the parameters of this account.

**Proof and simultaneous resources.** The authentic schedule starts
with Hold; Read, then two returning Ticks and Hold. Each pulse includes
its own Tick scalar, Add acknowledgement and final Read. The two
additional Reads and Holds are exactly those displayed in the table;
no hypothetical second execution of the shorter word is charged as an
actual source execution. It is the prefix already visited in this run,
whose completed last pulse Read supplies its literal boundary value.

Let $W_S\ge1$ be the largest binary width of any integer numerator,
denominator, counter or arithmetic intermediate in this implementation,
including $r,s,p,q$, (85.1), interval endpoints, the inverse of $q$
modulo $s$, residue products, all source scalars and all table entries.
A straightforward school-arithmetic implementation of the orbit
construction and its linear scans uses
$O((j+1)^2W_S^3)$ bit work and
$O((j+1)W_S)$ bits for its numeric table, digits and arithmetic workspace.
Indeed there are $O(j+1)$ recurrence computations and at most
$O((j+1)^2)$ exact comparisons; rational reduction, Euclid and each
bounded-width arithmetic operation are paid by the conservative cubic
bound. The constant-size scalar acquisition, origin arithmetic and
actual Tick/Add arithmetic fit the same bound when their actual widths
are included. Finite parsing, bit traffic and output copying are
additional actual work, rather than zero-cost arithmetic instructions.
The horizon $R$ can be large as a function of the input values; there
is no polynomial-in-input-bit-length claim.

At the same run, also retain and pay the actual source's current scalar
and update buffers, the installed law and predictor, $v$, the orbit and
witness records, loop marks, parser/program, reference and grants, all
live I/O copies and whatever producer or old input/reply archives are
actually retained. Count shared backing once and distinct coexisting
copies separately. None of those archives is advice to an endpoint
inverse. If a favorable arbitrary word of length $L$ is run using the
same acquisition/origin/final-read schedule, its command totals are the
same table with $j$ replaced by $L$; its word inverse instead uses the
valuation/residue algorithm of §§61–62 and its own actual operands.
This is a separate favorable run, not a coordinate of the collision
run's resource optimum.

For favorable unbounded $L$, (84.8) forces reduced denominators to carry
$\ell^{Le-c}$ whenever $Le-c>0$. For the unfavorable witness, the finite
integer carrier gives a different precision behavior, but the literal
word/table and actual source traffic still have their stated cost.
Neither finite scalar dimension nor a compact program implies uniformly
bounded total memory, uniformly bounded instrument precision, or a
joint optimum over other implementations. $\square$

## 87. A finitely tested class of rational path laws

**Definition 87.1 (the acquired path and a denominator-prime certificate).**
For the vector problem retain Definitions 36.1–36.3's actual rational
symmetric tridiagonal $T\in\mathbb Q^{N\times N}$, $N\ge1$, positive
adjacent links, $0<T<I$, root $b=e_0$ and authentic preparation. Run
Theorem 37.2 on that specimen before the later-origin task. Retain its
earned native matrix, moments and matrices

$$
K=[b,Tb,\ldots,T^{N-1}b],\qquad
\mathcal O=K^{\mathsf T},\qquad M=K^{-1}TK.
\tag{87.1}
$$

Both $K$ and $\mathcal O$ are invertible by native triangularity.
Retain the primitive whole integer characteristic law of Definition
44.2, renamed here to avoid a scalar-denominator ambiguity:

$$
Q(z)=az^N+\sum_{h=0}^{N-1}q_hz^h,\qquad a\ge2,
\qquad Q/a=\det(zI-T).
\tag{87.2}
$$

This is the law of the whole cyclic source, whether or not it factors.
A denominator-prime certificate is a triple $(s,\ell,J)$ satisfying

$$
s\in\mathbb Z,\ s\ge2,\qquad J=sT\in\mathbb Z^{N\times N},
\qquad \ell\text{ prime},\quad \ell\mid s,\quad \ell\nmid\det J.
\tag{87.3}
$$

All installation and authority promises of Assumption 36.2 persist:
actual root binding, declared rational Add right, full replies and
completed returns, exclusive serial use, no autonomous Ticks, and
sufficient finite computation, communication and source backing.
Numerical certificate (87.3) does not establish those promises.

**Proposition 87.2 (a total law-class test).** Given the earned finite
rational matrix $T$, existence of any certificate (87.3) is decidable
by finite integer arithmetic. Let $D$ be the least common multiple of
the positive reduced denominators of its entries, including denominator
one at zero, and put $J_D=DT$. Factor $D$ by finite trial division.
The test accepts exactly when some prime divisor $\ell$ of $D$ does
not divide $\det J_D$; on success it returns $(D,\ell,J_D)$.
It terminates and refuses when no such prime exists, including $D=1$.

**Proof.** The displayed data and determinant are finite integers. A
trial divisor loop through $2,\ldots,D$, dividing out factors when found,
is a finite factorization algorithm; no efficiency assertion is needed.
An accepted prime gives (87.3) directly, with $D\ge2$.
Conversely, if $sT$ is integral, every reduced entry denominator divides
$s$, hence $s=mD$ for an integer $m\ge1$ and $J=mJ_D$.
If $\ell\mid m$, then $\ell\mid m^N\det J_D=\det J$, since $N\ge1$,
contradicting (87.3). Thus $\ell\nmid m$, and $\ell\mid s=mD$ implies
$\ell\mid D$. The same determinant identity gives
$\ell\nmid\det J_D$, so the test finds a permitted prime. Refusal means
precisely failure of this certificate class. It does not prove failure
of pulse recovery for that source. $\square$

**Lemma 87.3 (the nonzero vector valuation).** Fix a successful
certificate and write $e=\nu_\ell(s)>0$. For a nonzero rational vector
$z$ define

$$
c(z)=\min_{h:z_h\ne0}\nu_\ell(z_h).
\tag{87.4}
$$

Zero is handled by a separate symbol and never assigned this minimum.
Then $Tz\ne0$ and

$$
c(Jz)=c(z),\qquad c(Tz)=c(z)-e.
\tag{87.5}
$$

If $c(z)<0$ and $d$ is any integer, then $z+db\ne0$ and
$c(z+db)=c(z)$.

**Proof.** Let $m=c(z)$ and $z=\ell^m z_0$. All coordinates of $z_0$
belong to the localization $\mathbb Z_{(\ell)}$, whose denominators are
prime to $\ell$, and at least one has nonzero reduction modulo $\ell$.
Since $\ell\nmid\det J$, the reduction of $J$ is invertible over the
field $\mathbb F_\ell$. Therefore $Jz_0$ has a nonzero reduction and all
its coordinates still lie in $\mathbb Z_{(\ell)}$. Its minimum valuation
is zero. Scaling back proves the first equality and nonvanishing;
dividing by $s$ proves the second. This also follows from the adjugate
inverse, whose denominator is a unit in that localization.

For the last assertion, adding $db$ changes only coordinate zero.
An unchanged coordinate attaining the negative minimum continues to do
so; if only coordinate zero attains it, its sum with an integer has
the same negative valuation by the unequal-valuation sum identity.
No coordinate can acquire a valuation below the old minimum. These
facts prove both nonvanishing and equality, including zero coordinates
and negative rational coordinates. $\square$

## 88. A paid prospective entrance after any finite legal later segment

**Theorem 88.1 (entrance with at most one Add).** On the acquired
certificate-bearing source of Definition 87.1, let $W$ be any finite
completed legal segment on the same bound installation, leaving a
rational field $y_0$ and preserving the law and needed rights. There
is a paid finite protocol, without reset, rollback or a second specimen,
which earns and retains an actual subsequent origin $v\ne0$ satisfying

$$
c(v)<e.
\tag{88.1}
$$

The protocol uses $N-1$ Ticks, $1+\delta$ Reads, $2+\delta$ Holds and
$\delta$ Adds, where $\delta\in\{0,1\}$ is determined by its actual
observed field. It has $N+\delta$ scalar replies. It does not reconstruct
the possibly erased segment $W$.

**Proof and protocol.** Execute

$$
\operatorname{Hold};\ \operatorname{Read};\
 (N-1\text{ returning Ticks});\ \operatorname{Hold}.
\tag{88.2}
$$

The literal $N$-scalar window is
$B_0=(b^{\mathsf T}T^hy_0)_{h<N}=\mathcal O y_0$.
During Hold compute $y_0=\mathcal O^{-1}B_0$ and the actual now-held
field $w=T^{N-1}y_0$. These are earned numerical values, using the
previously acquired law rather than an unknown-source response oracle.
If $w\ne0$ and $c(w)<e$, set $\delta=0$ and retain $v=w$.
Otherwise set $\delta=1$ and actually execute

$$
\operatorname{Add}(1);\ \operatorname{Read};\ \operatorname{Hold},
\qquad v=w+b.
\tag{88.3}
$$

If $w=0$, then $v=b$ has $c(v)=0<e$. In the other remaining case
$c(w)\ge e\ge1$, every nonzero coordinate of $w$ has valuation at least
$e$. Its root coordinate plus one has valuation zero, including when
the old root coordinate is zero. The other coordinates are unchanged
and have valuation at least $e$ when nonzero. Thus again $v\ne0$ and
$c(v)=0<e$. This proves (88.1). The new Read confirms the actual root
return; the earned law and actual Add successor give the whole vector.

The protocol retains the finite rational vector $v$ before the target
word begins, together with its certificate and origin convention. The
entry window, any extra root Read and the known $N-1$-Tick advance are
paid. The proof of $v$ uses
the actual entry window, so it neither presupposes the unknown $y_0$
nor restores it as the current field. The commands displayed give
exactly the stated counts, also for $N=1$ and $y_0=0$. A prior Add
outside the future digit alphabet is allowed in $W$ under the original
rational Add right; this is a prospective new task, not recovery of
that earlier input list. If the entry is zero, Read, Hold and Tick
alone keep it zero, so some Add is necessary for this nonzero-origin
task; (88.3) suffices with one. This is a task-specific necessity at
zero, not a broader generator minimum. Nor is zero a free preparation:
from a known actual field $y$, $N$ legal rational pulses with power-order
input vector $-K^{-1}T^Ny$ end at zero, since their input contribution
is $-T^Ny$. Their chronological inputs are that vector in reverse
order. Such a prior segment is part of $W$ and pays all $N$ Ticks,
Adds and Reads; it makes the zero entrance branch actually attainable.
$\square$

**Theorem 88.2 (a later-origin clock for every integer pulse word).**
Fix any actual retained origin $v\ne0$ satisfying (88.1), whether earned
by Theorem 88.1 or by another fully paid legitimate entrance. For every
$L\ge0$ and every $u\in\mathbb Z^L$ executed with the original literal
pulse schedule, put

$$
X_v(u)=T^Lv+\sum_{i=0}^{L-1}u_iT^{L-1-i}b.
\tag{88.4}
$$

Then

$$
X_v(u)\ne0,\qquad c(X_v(u))=c(v)-Le.
\tag{88.5}
$$

Consequently a rational endpoint in this signed pulse image determines
its length. This assertion does not claim signed-word uniqueness.

**Proof.** At $L=0$ this is the retained origin. If the current minimum
is $c(v)-Le<e$, its Tick successor has minimum
$c(v)-(L+1)e<0$ by (87.5). Adding the next integer cannot change it by
Lemma 87.3. Induction proves nonvanishing and (88.5). The whole
primitive law is not replaced by this clock: the clock separates
lengths, while same-length digits need the whole-law supplier below.
$\square$

## 89. A total rational-input bounded-pulse recognizer

**Definition 89.1 (the fixed decision problem).** Fix the earned data
$(N,T,K,\mathcal O,Q,a,s,\ell,e,v)$ of §§87–88 and an integer
$0\le H<a$. All encodings are exact finite rational or integer data,
and $v\ne0$, $c(v)<e$. The input is any vector $x\in\mathbb Q^N$,
without a pulse-image, length, sign or nonzero promise. The required
answer is either NOT_IN_THIS_PULSE_IMAGE or ACCEPT$(L,u)$ with
$L\ge0$, $u\in\{0,\ldots,H\}^L$ and the exact endpoint equality
$x=X_v(u)$. Acceptance is a numerical membership assertion; it is not
a certificate that this input was historically observed or produced by
the installed specimen.

Use the supplied lattice construction of §§45 and 63 with

$$
\eta_j=M^je_0,\qquad
\Lambda_n=\sum_{j<n}\mathbb Z\eta_j\quad(n\ge N),
\qquad\eta_j=e_j\ (j<N).
\tag{89.1}
$$

Its computed nonsingular integer matrices $C_n$ satisfy
$\Lambda_n=\{z:C_nz\in\mathbb Z^N\}$. Its computed homomorphisms
$\phi_n:\Lambda_{n+1}\to\mathbb Z/a\mathbb Z$ have kernel
$\Lambda_n$ and $\phi_n(\eta_n)=1$. These are whole-law suppliers.
In particular their exact cyclic order $a$ follows from primitive
integer divisibility, not from a selected irreducible spectral factor.
Their formulas and their domain tests are part of the algorithm, not
membership or residue oracles.

**Algorithm 89.2 (finite decision and reconstruction).** Perform the
following exact operations.

1. If $x=0$, return NOT_IN_THIS_PULSE_IMAGE. Otherwise compute $c(x)$
   by taking valuations of its nonzero coordinates. Form
   $L=(c(v)-c(x))/e$. If this is not an integer $L\ge0$, refuse.
2. Compute the residual
   $\rho=K^{-1}(x-T^Lv)$ by finite matrix arithmetic.
3. If $L\le N$, require that coordinates $0,\ldots,L-1$ of $\rho$
   are integers in $[0,H]$ and that all its other coordinates are zero.
   Set $d_j=\rho_j$ for $j<L$. Refuse if any requirement fails.
4. If $L>N$, construct $\eta_j$, $C_n$ and the residue formulas from
   Proposition 63.2 through $C_L$. First require $C_L\rho\in\mathbb Z^N$;
   otherwise refuse. Then for $j=L-1,L-2,\ldots,N$ compute the least
   representative $d_j\in\{0,\ldots,a-1\}$ of $\phi_j(\rho)$.
   Refuse if $d_j>H$; otherwise replace
   $\rho\leftarrow\rho-d_j\eta_j$.
   At the end require every coordinate of $\rho$ to be an integer in
   $[0,H]$ and set $d_j=\rho_j$ for $j<N$; otherwise refuse.
5. In either non-refused branch return ACCEPT$(L,u)$, where
   $u_i=d_{L-1-i}$ for $0\le i<L$. The empty branch requires $\rho=0$
   and returns $u=\varnothing$.

**Theorem 89.3 (termination, soundness, completeness and uniqueness).**
Algorithm 89.2 terminates on every input of Definition 89.1 and accepts
exactly

$$
\mathcal P_{v,H}=
 \{X_v(u):L\ge0,\ u\in\{0,\ldots,H\}^L\}.
\tag{89.2}
$$

For an accepted input its returned pair $(L,u)$ is unique. All negative
coordinates, zero coordinates, $N=1$, $H=0$, $L=0$ and $L=N$ are
included in this statement. A certificate test or origin-premise failure
before this problem is initialized refuses the certified class; it is
not a negative membership decision for an uninitialized pulse problem.

**Proof.** Rational equality, integrality, integer interval membership,
finite powers and finite exact matrix arithmetic are decidable. A
nonzero rational coordinate is an integer numerator divided by a
positive integer denominator. Repeated division of their absolute
values by the prime $\ell$ computes its integer valuation and terminates.
Sign has no effect; zero coordinates are skipped. Step 1 either refuses
or yields a particular finite nonnegative integer $L$, which bounds
every remaining loop. Thus no ascending search with an unknown stopping
index remains.

The only residue evaluations occur in step 4. Its first membership
test puts the initial residual in $\Lambda_L$. At a descending step,
if $\rho\in\Lambda_{j+1}$ and $d_j$ is the representative of
$\phi_j(\rho)$, then

$$
\phi_j(\rho-d_j\eta_j)=0,
\qquad \rho-d_j\eta_j\in\Lambda_j.
\tag{89.3}
$$

This proves the required domain of every next residue evaluation and
at the end gives $\rho\in\Lambda_N=\mathbb Z^N$. It is legitimate to
refuse for a digit exceeding $H$ before continuing. For clarity, one
explicit supplied evaluation uses $t=aC_j\eta_j$, a unimodular $U_j$
with $U_jt=g_je_0$, and an integer $h_j$ satisfying
$h_jg_j\equiv1\pmod a$. On $\Lambda_{j+1}$ only, it is
$[h_ja(U_jC_j\rho)_0]_a$. Its argument is an integer on exactly the
proved domain. No residue of an arbitrary off-lattice rational is taken.

For completeness suppose $x=X_v(u)$ with allowed digits. The clock
(88.5) makes step 1 return its actual $L$ and excludes zero. In power
coordinates the initial residual is

$$
\rho=\sum_{j=0}^{L-1}d_j\eta_j,
\qquad d_j=u_{L-1-j}\in[0,H]\cap\mathbb Z.
\tag{89.4}
$$

For $L\le N$, $\eta_j=e_j$ proves exactly step 3's conditions.
For $L>N$, (89.4) lies in $\Lambda_L$; at the first descending step
all lower terms lie in $\Lambda_{L-1}$. Therefore its residue is the
class of its actual top digit. Since $0\le d_j\le H<a$, its least
representative is the actual digit. Subtract it and repeat. The last
residual is the vector of the lowest $N$ actual digits. No test refuses,
and reversal returns the original chronology.

For soundness, an accepted small-$L$ coordinate check is precisely an
identity of the form (89.4). In the large-$L$ branch, reverse all the
performed subtractions starting with its accepted low-coordinate vector;
this gives that same identity, with every digit in $[0,H]$. Multiplying
by $K$ and adding $T^Lv$ gives exactly $x=X_v(u)$. Thus every accepted
output satisfies the required endpoint equality.

Two such words at the same endpoint have the same length by (88.5).
At that length step 3 or the deterministic residues and low coordinates
force all their digits to agree. Equivalently, Theorem 45.2 supplies
fixed-length injectivity for $H<a$, independently of the retained origin.
For $L=0$ the check is exactly $x=v$; for $H=0$ the only words are the
zero words and their lengths remain separated by the clock. All other
listed boundary cases were included by the explicit branch domains.
$\square$

**Corollary 89.4 (image refusals do not assert a history obstruction).**
The test can refuse a zero input, a negative proposed length, a fractional
proposed length, an off-lattice residual, an excessive quotient digit,
or invalid low coordinates. Every such refusal has the exact meaning
$x\notin\mathcal P_{v,H}$. It gives no negative claim about arbitrary
signed words, other origins, sources failing (87.3), or histories using
other legal operations. A negative coordinate by itself is never a
refusal condition.

**Proof.** This is the soundness/completeness biconditional with the
algorithm's exhaustive branches. The input space in Definition 89.1
contains all rational signs, whereas the target image has the specified
origin and nonnegative bounded digits. Changing that target changes
the decision problem. $\square$

## 90. Nonempty certified later-origin tasks in every dimension

**Theorem 90.1 (an all-dimensional family).** For every integer $N\ge1$
there is a rational positive-link path satisfying Definition 87.1 and
the denominator-prime test, and hence admitting Theorems 88.1–89.3
after every finite legal later segment. These tasks include origins
which are not passive powers $T^mb$ of the authentic preparation.

**Proof.** Let $J_N$ be the symmetric tridiagonal integer matrix with
all diagonal entries $2$ and all adjacent links $1$. Its leading
principal determinants satisfy $D_0=1$, $D_1=2$ and
$D_n=2D_{n-1}-D_{n-2}$. Expanding the tridiagonal determinant proves
this recurrence, and induction gives $D_n=n+1$.
For $z\in\mathbb R^N$ the exact quadratic identities are

$$
\begin{aligned}
z^{\mathsf T}J_Nz
 &=\sum_{h=0}^{N-2}(z_h+z_{h+1})^2+z_0^2+z_{N-1}^2,\\
z^{\mathsf T}(4I-J_N)z
 &=\sum_{h=0}^{N-2}(z_h-z_{h+1})^2+z_0^2+z_{N-1}^2.
\end{aligned}
\tag{90.1}
$$

Both are strictly positive for $z\ne0$: equality would force the
endpoints to vanish and then, successively along the path, every
coordinate to vanish. For $N=1$ the sums are empty and both displayed
endpoint terms remain, giving $2z_0^2$ as required.
Choose a prime $s>\max(4,N+1)$ and set $T=J_N/s$ and $\ell=s$.
Then $0<J_N<4I<sI$, so $0<T<I$, and all required adjacent links are
positive rational numbers. Also $\ell\mid s$ and
$\ell\nmid\det J_N=N+1$. This is a certificate (87.3); the finite test
therefore succeeds. Existence of such primes is the ordinary unboundedness
of the primes, rather than an additional apparatus promise.

For an explicit nonpassive later example on this same source, let
$W$ after authentic acquisition be Add$(1)$. Its actual endpoint is
$y_0=T^{2N}b+b$. Here $c(b)=0$, $e=1$ and (87.5) gives
$c(T^{2N}b)=-2N$. Adding $b$ cannot change this negative minimum, so
$c(y_0)=-2N$. The entrance (88.2) ends at

$$
v=w=T^{3N-1}b+T^{N-1}b,\qquad
c(v)=-(3N-1),\qquad\delta=0.
\tag{90.2}
$$

The zero-extra-Add branch is therefore actually selected. If this $v$
were $T^mb$ for an integer $m\ge0$, (87.5) would force $m=3N-1$.
But then (90.2) would force $T^{N-1}b=0$, contradicting invertibility
of $T$. Thus even these particular earned origins are genuine later
vector origins rather than a disguised passive epoch. The argument
also includes $N=1$. The general entrance remains valid for every
other finite legal $W$, including ones ending at zero. $\square$

## 91. Literal observation and complete service at the actual advanced field

**Definition 91.1 (historical and present cuts).** After the prospective
entrance, execute an actual finite word
$u\in\{0,\ldots,H\}^L$, $0\le H<a$, from the retained $v$. At its
endpoint $x_{\rm hist}=X_v(u)$ execute precisely

$$
\operatorname{Read};\ (N-1\text{ returning Ticks});\ \operatorname{Hold}.
\tag{91.1}
$$

The literal Boundary and actual returned current field are

$$
B=(b^{\mathsf T}T^h x_{\rm hist})_{h<N}
 =\mathcal O x_{\rm hist},\qquad
x_{\rm now}=T^{N-1}x_{\rm hist}.
\tag{91.2}
$$

The diagnostic's fixed $N-1$-Tick count is known metadata, independent
of the old unknown $L$. During the final Hold compute
$x_{\rm hist}=\mathcal O^{-1}B$, apply Algorithm 89.2 to it, and install
the current predictor $m=\mathcal O x_{\rm now}$. Retain the actually
advanced specimen and its actual service access, together with the
origin $v$. No rollback is performed or promised.

As in the original post-pulse experiment, the pulse producer and
controller schedule this diagnostic after their finite completed input
segment. Their input reception, completion control and retained backing
are actual resources. They supply no extra source port exposing $L$;
the numerical decoder receives only the earned fixed context and $B$,
without a producer counter or word archive.

**Theorem 91.2 (installed inverse and all-field original continuation).**
For every actual word in Definition 91.1, its paid diagnostic and finite
local algorithm recover exactly that word and its length and return
the live predictor at the field $x_{\rm now}$ in (91.2). The diagnostic
has exactly $N$ scalar replies, $N-1$ Ticks, one Read and one Hold.
From that returned cut, every finite common adaptive legal continuation
in the full original menu has its complete declared outputs and actual
successors predicted exactly, including authorized rational Adds outside
the decoding alphabet.

**Proof.** The literal window and earned invertible $\mathcal O$ recover
its historical starting field, which belongs to $\mathcal P_{v,H}$.
Theorem 89.3 terminates and returns its unique pair. The diagnostic makes
exactly $N-1$ native advances, so the installed predictor describes
$x_{\rm now}=T^{N-1}x_{\rm hist}$, including their equality for $N=1$. Let
$\mu_h=b^{\mathsf T}T^hb$, $0\le h<N$, be the already earned impulse
data. At any current rational field $x$ use the invariant
$m_h=b^{\mathsf T}T^hx$. The complete one-step rules are:

| Legal primitive | Predictor successor | Declared output |
| --- | --- | --- |
| Read | $m'=m$ | scalar $m_0$ |
| Tick | $m'_h=m_{h+1}$ for $h<N-1$, and $m'_{N-1}=-\sum_{h<N}(q_h/a)m_h$ | scalar $m'_0$ |
| Add$(t)$, $t\in\mathbb Q$, with its installed input right | $m'_h=m_h+t\mu_h$ for all $h<N$ | fixed Add acknowledgement, with $m'_0$ additionally only in the declared scalar-return variant |
| Hold | $m'=m$ | fixed Hold acknowledgement |

For $N=1$ Tick consists of the last-coordinate formula alone. The
whole characteristic identity $Q(T)=0$ proves that formula; the other
rows follow directly from the actual native successors $x$, $Tx$,
$x+tb$, $x$. Thus every row preserves $m=\mathcal O x$ and reproduces
all original scalar outputs, acknowledgements and the successor.

In particular the recovered $u$ and retained $v$ also determine every
numerical output and successor of the original target pulses: recursively
$x_{i+1}=Tx_i+u_ib$, with Tick scalar $b^{\mathsf T}Tx_i$, the complete
declared Add reply and final Read scalar $b^{\mathsf T}x_{i+1}$. The
fixed diagnostic then gives (91.2). This calculation does not create
an actually observed old transcript or execute another source run.

Keep the real root-bound handle, rights, frame convention, serialization
and finite backing. The installed consumer forwards each admitted call
there, consumes every declared reply and its completed return, and
commits the stated record successor before the next settled cut.
Enabledness is the original installed enabledness; an absent right is
not replaced by a new numerical refusal output. Induction over a finite
common adaptive sequence proves the service assertion. Equality of
predicted numbers alone would neither execute the call nor create its
authority. The all-field invariant applies after arbitrary rational
Adds even when the field leaves $\mathcal P_{v,H}$. It needs no further
claim that such a field has a bounded-word inverse. $\square$

**Proposition 91.3 (two cuts remain distinct).** The recovered Time in
Theorem 91.2 stops before the diagnostic, whereas the retained actual
source and live Memory are at its advanced cut. Numerically one has
$x_{\rm now}=X_v(u0^{N-1})$, but the diagnostic is not the literal
zero-pulse suffix $0^{N-1}$.

**Proof.** A zero pulse has Tick; Add$(0)$; Read and all their declared
outputs. Schedule (91.1) has one initial Read and only the stated
returning Ticks before its Hold. The affine updates give the displayed
numeric equality, while the actual command words and replies are
different. Formula (91.2) identifies the source actually returned, and
Theorem 91.2 initializes at that field. $\square$

## 92. Independent later-origin expressions, route agreement and dynamics

**Definition 92.1 (the joint returned image).** Fix the earned law,
certificate, actual retained origin $v$, digit bound $H<a$, binding and
rights, and the diagnostic schedule (91.1). The domain consists of
returned held cuts after some actual bounded pulse list from that $v$
and this diagnostic. The law/origin/diagnostic data are common context;
there is no shared old $L$, old pulse word, earlier $W$ or unrestricted
reply archive. The four numerical expressions have these meanings:

| Expression | Exposed content |
| --- | --- |
| Space | The actual rooted weighted native path with its full present field $x_{\rm now}$, up to root-preserving weighted coordinate identification |
| Time | The actual chronological bounded pulse list before the fixed diagnostic |
| Boundary | The actual paid ordered $N$-scalar window $B$ beginning at $x_{\rm hist}$ |
| Memory | The earned law and live sufficient vector $m=(b^{\mathsf T}T^h x_{\rm now})_{h<N}$ of current autonomous root predictions |

In particular Boundary is historical and Memory is current. The retained
callable access and its finite material resources accompany the common
process. A view inverse computes numerical content and a semantic
service description in the fixed context; it does not mint a physical
binding, rights or an observed record from a number.

**Theorem 92.2 (four-view inverse and complete task kernel).** On
Definition 92.1's joint actual image every expression determines the
other three numerical expressions, the historical field and the actual
current field. Every recovery route agrees. Their equality kernel is
exactly equality of the complete current original continuation task
at that fixed installation. All proposed rational Space, Boundary or
Memory values have a total numerical image test by the corresponding
invertible transport and Algorithm 89.2; acceptance asserts membership
only, not provenance.

**Proof.** From Boundary compute $x_{\rm hist}=\mathcal O^{-1}B$;
Theorem 89.3 returns its unique Time. Formula (91.2) then gives Space
and multiplication by $\mathcal O$ gives Memory. From Space compute
$T^{-(N-1)}x_{\rm now}=x_{\rm hist}$, possible since $T$ is positive
definite, and use the same inverse. From Memory use
$\mathcal O^{-1}m=x_{\rm now}$ and proceed as from Space. From Time
use (88.4) and (91.2), then $m=\mathcal O x_{\rm now}$. All these maps
act on the same fixed earned native coordinates and actual process.
Every composition fixes the unique word and its two determined fields,
so all routes agree.

Theorem 91.2 shows that equal current fields have equal complete
continuation outputs and related actual successors. Conversely, if
$x_{\rm now}\ne x'_{\rm now}$, their difference has nonzero image under
invertible $\mathcal O$. Read followed by at most $N-1$ returning Ticks
therefore distinguishes one coordinate of that image through original
legal ports. Thus equality of the full continuation task is exactly
equality of $x_{\rm now}$. Invertible $T^{N-1}$ and the unique bounded
inverse make it exactly equality of Time on this domain, and hence of
each view. This does not identify larger controller archives or their
possible future selectors.

For any proposed rational Boundary list use $\mathcal O^{-1}$, for a
proposed Space field use $T^{-(N-1)}$, and for a proposed Memory vector
use $T^{-(N-1)}\mathcal O^{-1}$. Each transport is a total exact rational
map to the candidate historical endpoint. Theorem 89.3 decides precisely
whether this is generated by a permitted pulse word; composing back
checks the original proposed value because these transports are
invertible. This establishes a numeric returned-image decision.
Actual-image observation, the binding and authority still have the
installation's original provenance premises. $\square$

**Theorem 92.3 (the exact dynamics agreements).** The preceding inverse
respects pulse concatenation at historical pulse cuts, passage through
the prescribed diagnostic, and the complete original primitive dynamics
at actual present cuts. For a primitive continuation, inverse transport
at its end is asserted whenever that end again meets the specified
joint returned-image domain; all-field prediction remains valid at all
its intermediate settled cuts.

**Proof.** For every pair of finite allowed pulse words $u,t$, direct
induction on the actual pulse updates gives

$$
X_v(ut)=T^{|t|}X_v(u)+
 \sum_{h=0}^{|t|-1}t_hT^{|t|-1-h}b.
\tag{92.1}
$$

Theorem 89.3 returns exactly $ut$ from that historical endpoint.
Applying (91.1) next gives precisely $T^{N-1}X_v(ut)$ and its window
and current prediction vector. Hence the routes through concatenation
and through reconstruction agree, with every literal pulse output
supplied by the actual step rules of Theorem 91.2.

Starting a new continuation at a returned cut instead starts from
$x_{\rm now}$; its first native successor is the successor from that
field in Theorem 91.2. It generally does not start from $X_v(u)$.
The invariant $m=\mathcal O x$ proves commutation of the native and
predictor one-step updates at each actual present cut, including every
output and completed call. Induction proves the same for all finite
adaptive continuations with a common selector and the given access.
Whenever an ending cut belongs to Definition 92.1, its unique inverse
in Theorem 92.2 agrees with these actual values. An intermediate field
outside that image is served by the all-field predictor, without an
invented bounded Time. This proves exactly the stated dynamics domain
and makes no closure assertion under arbitrary rational interventions.
$\square$

## 93. One attained later-vector implementation and its simultaneous bill

**Proposition 93.1 (one-Add entrance, stored lattice descent).** Use
Theorem 37.2, an actual legal $W$, Theorem 88.1's particular entrance,
$L$ actual bounded pulses, and the final diagnostic (91.1). Store the
lattice matrices and residue forms needed by Algorithm 89.2 and perform
its descending reconstruction while held. Excluding only the separately
attached actual counts of $W$, the exact operation account is

| Stage | Tick | Add | Read | Hold |
| --- | ---: | ---: | ---: | ---: |
| Authentic acquisition | $2N$ | $0$ | $1$ | $N+1$ |
| Later prospective entrance | $N-1$ | $\delta$ | $1+\delta$ | $2+\delta$ |
| Actual target pulses | $L$ | $L$ | $L$ | $0$ |
| Final historical window | $N-1$ | $0$ | $1$ | $1$ |
| Total apart from $W$ | $4N+L-2$ | $L+\delta$ | $L+3+\delta$ | $N+4+\delta$ |

The mandatory scalar total is $4N+2L+\delta+1$, and the acknowledgement
total is $N+L+4+2\delta$. A declared post-Add-scalar variant adds
$L+\delta$ scalar outputs. If $W$ contains $t_W,a_W,r_W,h_W$ Ticks,
Adds, Reads and Holds, add those counts respectively, add $t_W+r_W$
mandatory scalars, $a_W+h_W$ acknowledgements, and $a_W$ optional Add
scalars in that variant. Its input, local computation, output and
backing costs remain part of the same run.

**Proof.** The authentic schedule has one initial Hold and one Hold
after each of its $N$ two-Tick stages. The later entrance has exactly
the commands (88.2) and, when $\delta=1$, (88.3). The pulses and
final diagnostic have their literal specified commands. Addition of
these four rows proves the table and reply counts. For $N=1,L=0$ no
negative Tick count occurs: the entrance and final window use zero
Ticks, and the acquisition still uses two. This account uses the same
chosen one-Add entrance, its actual $\delta$, and stored descent; it
does not combine their operation count with a different entrance or
regeneration algorithm's storage or work. $\square$

**Proposition 93.2 (finite work, precision and coexisting backing).**
Let $W_V\ge1$ be the actual maximum binary width of integer numerators,
denominators, Euclid coefficients, matrix intermediates and counters
in the chosen finite run and its decoder, including its input and
output encodings. The following is one sufficient arithmetic layout,
not an optimality claim.

For a nonzero rational candidate, computing all coordinate valuations
uses $O(NW_V)$ integer divisions of operands of width at most $W_V$,
hence $O(NW_V^3)$ conservative school bit work. After a finite
nonnegative proposed $L$ has been obtained, residual formation, the
stored lattice construction, membership and descending digits require

$$
O((L+N+1)N^3)\text{ rational/integer arithmetic operations},\qquad
O((L+N+1)N)\text{ Euclid calls}.
\tag{93.1}
$$

A conservative bit bound is $O((L+N+1)N^3W_V^3)$, with
$O((L+N+1)N^2W_V)$ numeric storage for the lattice/residue tables,
output digits and arithmetic workspace. An earlier refusal pays only
the prefix actually computed. These are finite bounds in the proposed
length and actual operand widths, not input-bit-polynomial bounds.

**Proof and accounting.** Powers for $T^Lv$ and $\eta_j$ can be formed
sequentially with finite vector multiplication. Each of the at most
$\max(L-N,0)$ lattice extensions uses at most $N$ extended Euclid
reductions and ordinary at most cubic matrix work, as explicitly in
(63.4)–(63.7). A membership test and each residue/subtraction have at
most quadratic matrix/vector work. The low-coordinate check is finite
and the output has $L$ digits. Keeping all these matrices and residue
forms gives the stated storage. Euclid and reduced rational arithmetic
at actual width $W_V$ have a conservative cubic school bound, yielding
(93.1)'s bit estimate. Valuations use at most one division per factor
of $\ell$ in each numerator and denominator, with at most $O(W_V)$
factors per coordinate, which proves the separate valuation bound.

The law-class test is a separately paid finite computation: form the
least common denominator and integer determinant and perform its actual
trial divisions of $D$. A loop bounded by the value $D$ is sufficient;
there is no free factorization or primality oracle. The authentic
acquisition separately pays its $O(N^4)$ rational elimination and
orthogonalization work, $N-1$ promised rational-square extractions,
whole-law coefficient arithmetic, and the construction/inversion of
$K,\mathcal O$ and $T$ when required. An integer square root here is
found and checked by a finite integer algorithm on the promised rational
square. The entrance and final window separately pay their reads,
T-multiplications, rational solves, vector transfers and valuations.
Precomputed inverses can be shared and counted once; separate retained
copies are separate material.

For this specified local arithmetic, trial division through $D$,
school elimination and binary-search integer square roots give the
combined sufficient bit bound

$$
O\!\left(\bigl[D+N^4+(L+N+1)N^3+1\bigr]W_V^3\right).
\tag{93.2}
$$

There are at most $O(D+W_V)$ trial divisions including removal of
repeated prime factors, and at most $O(W_V)$ square-root search steps
per numerator or denominator. The displayed bound includes these,
the acquired-law arithmetic, entrance/window arithmetic and the decoder;
it excludes no other arithmetic from those specified algorithms. Work
inside the arbitrary earlier $W$, the actual source backend and the
input/output and producer mechanisms below remains separately attached
to this same run, with no uniform bound assumed for those mechanisms.

On the actual source, a tridiagonal Tick can be implemented with
$3N-2$ rational multiplications and $2N-2$ additions using old/new
field buffers; Add changes the root coordinate. The pulse producer,
segment $W$, actual output transmission and consumption, parser,
program and counter work, and all copies also have their actual finite
cost. A reduced rational at precision $W_V$ is not one free bit and a
completed return is not an uncharged read oracle.

At the largest simultaneous live cut count the source state and its
update buffers; earned $T,Q,\mu,K,\mathcal O$ and required inverses;
certificate and retained $v$; entrance window and recovered entry/current
vectors if still stored; final historical window and the distinct
historical, present and prediction vectors when simultaneously retained;
lattice/residue tables, reconstructed word, all counters and arithmetic
workspace; pulse producer and any separately retained old word or reply
archives; request/return and output buffers; code, actual reference
widths and grants; and sufficient backing for each occupied or reserved
record. Each present shared object is counted once, and coexisting
old/new or I/O copies are counted separately. Cleared temporary records
need not be retained, but their allocated backing and any clearing work
are not inferred to vanish from a total-resource comparison. None of
these separate archives is a decoder input or an origin substitute.

Finally, (88.5) implies that if $Le-c(v)>0$, some nonzero endpoint
coordinate has reduced denominator divisible by
$\ell^{Le-c(v)}$. Thus exact target runs of unbounded length require
unbounded available precision in this sense. The final diagnostic has
the exact current valuation $c(x_{\rm now})=c(v)-(L+N-1)e$, and its
actual widths are included too.
The finite-dimensional predictor, finite program and total decision do
not imply a uniform finite-memory device, a total resource optimum or
an asymptotically free observer. $\square$

## 94. Direct supplier correspondences and the mathematical increment

**Definition 94.1 (scalar numeration correspondence).** The classical
numeration input is [Akiyama–Frougny–Sakarovitch, *Powers of rationals
modulo 1 and rational base number systems*, primary manuscript, §3.1,
Lemma 5 and Theorem 1](https://www.math.tsukuba.ac.jp/~akiyama/papers/3half_H65fullTH-060406.pdf).
Their base numerator and denominator correspond to $s$ and $r$ here,
not to the origin numerator and denominator $p,q$. Put $\alpha=s/r>1$.
For $w=u_{L-1}\cdots u_0$ their evaluation convention is

$$
\pi(w)=\frac1r\sum_{i=0}^{L-1}u_i\alpha^i,
\qquad \alpha^LX_v(u)=v+s\pi(w).
\tag{94.1}
$$

Thus their alphabet is exactly $D_s$, and their Lemma 5 supplies the
fixed-length uniqueness used in (84.9). Their Euclidean digit recurrence
$rN_i=sN_{i+1}+a_i$ concerns canonical integer expansions. Their
Proposition 26's exclusion of nonzero ultimately periodic infinite
words concerns labels of infinite paths from their tree root: every
finite prefix belongs to $0^*L_{s/r}$, the leading-zero closure of the
canonical integer-expansion language, and $r>1$. An arbitrary controlled
pulse string in $D_s^*$ is not required to satisfy that prefix-language
hypothesis. Neither that exclusion nor canonical expansion existence
is used to replace the bounded witness in Lemma 84.2.

There is also a direct mature division-dynamics supplier:
[Akiyama–Thuswaldner–Zaïmi, *Comments on the height reducing property II*,
arXiv:1403.7480v1, equations (4)–(6), Propositions 6–7 and Corollary
8(ii)](https://arxiv.org/html/1403.7480v1). For $s\mid p$ use

$$
\mathbb Z[\alpha]=\mathbb Z[1/r],\qquad
\mathcal R=\{-qd/r:0\le d<s\}.
\tag{94.2}
$$

The ring equality follows from Bezout for $r,s$. Reduction modulo
$\alpha$ identifies its quotient with $\mathbb Z/s\mathbb Z$, since
$r$ is a unit. Because $q$ is prime to $s$, $\mathcal R$ is a complete
residue system in that quotient. The unique representative of an
integer $k$ is $-qd(k)/r$, and their division map is exactly

$$
\frac{k-(-qd(k)/r)}{\alpha}=F(k).
\tag{94.3}
$$

The rational algebraic number $\alpha>1$ is expanding, so their
Corollary 8(ii) already supplies eventual periodicity in this ring.
Lemma 84.2 verifies the stronger concrete facts needed for this source
application: this initial integer remains in a specified finite integer
interval, a repetition occurs by $R+1$ at positive indices, and the
residues correspond to actual legal post-Tick Adds on the original
specimen. Eventual periodicity, rational-base numeration, Euclid and the
finite pigeonhole principle are literature-attested suppliers, not new
abstract results or claims of worldwide priority.

**Definition 94.2 (repository and pinned-library subtraction).** The
following correspondences identify the reused content and the remaining
source-specific mathematical increment.

| Supplier | Applied hypotheses and precise boundary |
| --- | --- |
| §§36–37, 44–45 | Authentic $b$, positive-link rational symmetric path, $0<T<I$ and original ports earn $N,T,K,\mathcal O,Q$ on one actual source. The whole primitive law supplies $a\ge2$ and the exact cyclic lattice order. These are preserved promises and supplied proofs, not conclusions of the new numeric class test. |
| §§59–62 | The all-signed favorable valuation clock and every-origin fixed-length bounded inverse already supply the favorable half of (84.7); the reciprocal converse and scalar origin installation are already present. The finite full-$D_s$ nonreciprocal converse and its actual witness complete the bounded question in Scope 61.3 and Definition 68.4. No signed collision is substituted for a bounded one. |
| §§63–68 | The computed $C_n,\phi_n$ and whole-law bounded digit descent are reused. Their authentic-phase ascending clock and promised-image termination do not themselves decide every rational input at a later origin. The increment is (87.3)–(88.5), the paid prospective entrance, and the initialized finite accept/refuse test of §89; the retained historical/current service is transported with its actual advance. |
| [FiniteOrbitPeriodBound](../../../D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean) and its [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.scribe.cs) | Its `finite_orbit_and_readout_eventually_periodic` applies with the finite carrier $I$, map $F$, initial $k_1$ and readout $k\mapsto sk/q$. The generic finite-state period bound and readout propagation supply the carrier step; the integer interval, pulse correspondence and installed experiment are the additional application conditions proved here. |
| [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs) | Apply over $\mathbb R^N$ with update $T$, output $b^{\mathsf T}$ and horizon $N$. Native triangularity identifies the full-rank stacked map as $\mathcal O$. The generic residual/rank/Gram equivalence supplies observability, not an actual paid observation, later-origin clock, interface right or total pulse-image decision. |
| [CoefficientDrivenJacobiCharacteristicPolynomial](../../../D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.scribe.cs) | The supplied coefficient multiplication, positive Hankel form and self-adjointness match the actual power basis and moments in Proposition 37.3. Its private orthogonal/monic, degree-support, tridiagonal and norm-ratio helpers and public characteristic result concern that given law. They are not missing later-origin acquisition APIs, and no duplicate Jacobi result is claimed. |
| [Pinned Mathlib GaussLemma](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Polynomial/GaussLemma.lean) | `Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map` applies to the primitive whole $Q\in\mathbb Z[z]$ and integral annihilator dividends over $\mathbb Q$. It requires neither irreducibility nor a primitive dividend. Its integer quotient is the leading-coefficient and exact-order supplier of §§44–45, retained in §89. |
| [Pinned Mathlib rational valuation facts](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean) | Nonzero multiplication/division and unequal-valuation addition give the scalar clock and the coordinatewise part of Lemma 87.3. The vector minimum is taken only over nonzero coordinates; the library's conventional value at rational zero is not used as a minimum or clock. Invertibility of $J$ modulo $\ell$ is the additional vector hypothesis. |
| [Atomic generation/acquisition II §§68–74, 75–83 at the public source](https://github.com/the-omega-institute/trureturing/blob/1da4ec9203b30624611f5bdff2b7503472050a45/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md) | The supplied guard acquisition has its actual split sweep and represented service; its global-history supplement has known-alpha initialization, maintained source annotations and complete original request lifecycle. Those are substantive common-source results in their own LAB domain. They supply neither the rational native $T$ nor (87.3), and neither bounded pulse Time here nor a rational membership decision supplies that supplement's arbitrary original generation service. |
| [SmallSignedEntryTranscriptCompensation](https://github.com/the-omega-institute/trureturing/blob/1da4ec9203b30624611f5bdff2b7503472050a45/D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.lean) and its [owning Scribe at the public source](https://github.com/the-omega-institute/trureturing/blob/1da4ec9203b30624611f5bdff2b7503472050a45/Blueprint/D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation.scribe.cs) | The original `small_entry_complete_transcript_compensation`, `no_deterministic_exact_acquisition` and `no_fair_zero_error_exact_acquisition` concern source-blind acquisition from arbitrary rational entries in a positive-radius ball, with unknown order and law. Their rational symmetric positive-link tridiagonal sources have quadratic bounds $\tfrac14I\le A\le\tfrac34I$, no common order bound and no positive uniform lower link bound; Add returns an acknowledgement. One fixed small entry compensates each complete finite command transcript. Here authentic acquisition precedes $W$ and the later window uses that already earned law. No conclusion about unknown-law arbitrary-entry startup is inferred from this different premise. |

The last comparison's actual quantifier distinction is essential:
$\forall W$ after one authentic acquired law is not arbitrary-entry
unknown-source acquisition. Similarly a finite alphabet's inverse is
not an arbitrary-journal inverse. These are differences in objects and
information supplied, not differences in confidence attached to a proof.

**Definition 94.3 (whole law versus one algebraic root).** The same
height-reduction paper's Theorem 3, its proof and Remark 11 already
supply finite-automaton recognition of bounded-digit zero
representations for an algebraic number with no unit-circle conjugate.
Any root of an irreducible factor of $Q$ meets that spectral condition,
because all roots of this actual $T$ lie in $(0,1)$. When $Q$ is
reducible, vanishing at just that root need not annihilate the whole
cyclic vector. Therefore it cannot replace the whole-law lattice or
certify (89.4). Conversely the constructive rational membership test
here does not claim a new general zero-representation automaton.

The abstract arithmetic, local-ring valuation, finite observability,
whole-law divisibility and source acquisition are supplied mathematics.
The source-relative results of §§84–93 are the explicitly quantified
bounded scalar completion and certified later-vector construction with
its paid service correspondence. Their attribution is repository-derived
synthesis and application; it makes no claim of universal novelty from
a finite literature comparison.

## 95. Exact recovery limits of the two outcomes

**Proposition 95.1 (separate domains).** The scalar iff is for every
reduced rational origin, every coprime $1\le r<s$ and the full $D_s$.
It does not classify all smaller digit menus. In particular the new
nonreciprocal case has $s\ge3$ and does not establish a new native
binary classification. Its collisions identify current fields and
common future service, not complete earlier transcripts. Its favorable
inverse recovers the prescribed pulse word, not arbitrary Read/Hold/Add
journals or an erased preparation.

The vector result is a sufficient, finitely recognizable law class
with a paid actual origin $v\ne0$, $c(v)<e$. It is nonempty in every
finite dimension and permits any finite prior legal $W$ after authentic
acquisition, including a zero resulting field, via the specified
prospective entrance. Algorithm 89.2 is total on all rational candidate
vectors for that initialized problem. Failure of the certificate test
or of an origin condition does not classify all other later-vector
origins; the general later-vector classification remains a separate
problem. At $H\ge a$, the supplied equal-length collisions of Theorem
45.2 persist at every retained $v$, since the common homogeneous term
cancels. Length recovery alone does not remove those digit collisions.

**Proof.** The scalar scope is exactly Definitions 84.1 and 85.2 and
the two implications of Theorem 84.3. The vector assertions follow
from Propositions 87.2, Theorems 88.1–90.1 and the inverse's stated
input domain. Subtracting two same-length copies of (88.4) removes
$T^Lv$ and leaves the supplied collision polynomial, proving the final
assertion. None of these arguments concerns a different command journal
or an uncertified actual installation. $\square$

The two attained resource accounts describe their own actual runs.
No scalar collision horizon, vector one-Add entrance, regenerative
storage, online scheduling or alternative acquisition coordinate is
combined into a synthetic total optimum. Numeric recognition does not
authenticate a physical source, bind a handle, grant a missing right,
create backing or make a computed boundary into an actual observation.
Common-future comparisons use the same declared law, current access
and future selector; they do not erase private old memories.

The native alpha/beta constructors, this rational path and quantum
phase/window services still have different actual laws and interfaces.
A common realization would have to match their actual initialization,
legal operations, complete outputs and successors, selection, observed
records, authority and simultaneous resources. No such native/path or
quantum realization, broader generator minimum, universal minimal
relation structure or total-resource optimum follows here. The prior
fixed-$G_{\rm gc}$, original-$Q$, parked-consumer,
unchanged-initialization and final-no-Ready statements keep their
original domains. The prospective origin protocol neither changes
those tasks nor recovers their erased histories. The full common-source
four-expression objective retains those additional obligations.

## 追加锚（本行以下为增补区）

## 96. Persistent local calibration on the native material

**Definition 96.1 (one calibrated alternative).** Let $t$ range over the
birth-typed domain $\mathcal D$ of [Atomic Generation Acquisition,
Definition 17.1 and Theorem 17.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#17-birth-typed-local-growth-and-its-causal-reconstruction),
written AA below. Thus $t::=\alpha\mid\beta\mid\langle t,t\rangle$,
addresses are finite words in $L,R$, and no logical alpha leaf ends in
$L$. Use its actual material $C(t)$: alpha has one vertex, beta has a
root and one left terminal marker, and a branch has its root and its two
ordered child materials. Write $V_t\subset\{L,R\}^*$ for all material
addresses, $N(t)=|V_t|$, and $e=e_\varepsilon$. A beta marker is material
but is not a logical target. No lower bound on the number of leaves is
imposed here.

Every material vertex at address $p$ carries two actual local rational
calibration records $(a_p,\ell_p)$. They are installed by the fixed rules

$$
(a_\varepsilon,\ell_\varepsilon)=(0,1),\qquad
(a_{pL},\ell_{pL})=(a_p+\ell_p/8,\ell_p/8),\qquad
(a_{pR},\ell_{pR})=(a_p+3\ell_p/4,\ell_p/8).
\tag{96.1}
$$

Put $d_p=a_p+\ell_p/2$. The actual field update on $C(t)$ is the symmetric
rational matrix

$$
(T_t)_{pp}=d_p,\qquad
(T_t)_{p,\operatorname{parent}(p)}
=(T_t)_{\operatorname{parent}(p),p}=\ell_p/100\quad(p\ne\varepsilon),
\tag{96.2}
$$

with all other entries zero. These are local stored coefficients and
local edge couplings, not a coefficient table handed to the observer.
Their dependence on the original ordered addresses is an installation
condition. An arbitrary unknown weighted tree is not the declared class.

The actual source starts as a genuinely zero-field alpha. An unknown
finite legal successful $P/S$ word prepares its current term $t$; no field
input or Tick occurs during this preparation. The persistent material edits
are AA Definition 20.2's templates, also used in [Native Leaf Boundary
Acquisition, Assumption 10.2](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md#10-a-changed-installation-ordered-leaf-waves-on-the-actual-lab-material),
written NLBA below. Promotion at $p$ retains $p$ and appends $pL$.
Splitting at $p$ retains both $p$ and its old marker $pL$, makes that marker
the left logical beta root, and appends $pLL,pR$. Every old cell value,
calibration record and edge coefficient persists; fresh fields are zero.
Fresh coefficients are computed from the actual parent's records by
(96.1)–(96.2). Consequently the old matrix is the principal submatrix on
old vertices. No global recalibration is hidden in an edit.

**Assumption 96.2 (paid root installation and complete menu).** The observer
receives a genuine binding to this same source's original root, the
original addressed $P/S$ authority with its $L/R$ interpretation, the fixed
law and finite control program, and actual finite work and completion
backing. It receives no term, size, height, terminal roster, coefficient
array, old word, allocation ordinal, internal field array or answer table.
Add and Read have only the root field port. There is no Reset, clone,
terminal port or interior field port. At a settled state $(u,x)$ the menu is:

| Complete request | Actual successor | Semantic reply |
| --- | --- | --- |
| Add$(q)$, $q\in\mathbb Q$ | $(u,x+qe)$ | fixed ACK |
| Read | $(u,x)$ | literal $e^{\mathsf T}x$ |
| Tick | $(u,T_ux)$ | literal $e^{\mathsf T}T_ux$ |
| Hold | $(u,x)$, held for local work | fixed ACK |
| $P_p$ | original promotion and zero lift if enabled | Growth$(P,p)$, otherwise the original tagged refusal |
| $S_p$ | original split and zero lift if enabled | Growth$(S,p)$, otherwise the original tagged refusal |

In particular Tick returns the updated scalar. It is not the
acknowledgement-only Tick of §§80–82. Logical navigation passes through
branches only. Absent address, branch target and wrong leaf type have
three distinct refusal tags, each with identity source and field successor.
A unary marker cannot be reached by navigating through its beta leaf.
There is no Tag, HasPromotion, HasSplit, FetchGrowth or Next port.

Fix a finite framing realization: a request has its kind, self-delimiting
payload and End token. Use AA's $A(p)=1^{|p|}0p$ for addresses and
length-prefixed signed reduced numerator/positive denominator words for
rationals. Its response has the specified semantic reply and one output
End; the observer consumes it, commits the corresponding local update,
emits one fixed LocalACK and completes one fixed Return before Ready.
LocalACK is distinct from a semantic ACK. These outer tokens carry no
source-dependent information. Complete malformed frames return BadFrame without a source
change. A proper incomplete prefix is retained as pending bytes and has
no completed response. Missing rights, a wrong protocol phase, revocation
and exhausted backing are not leaf refusals. The theorem domain supplies
exclusive current rights, finite fresh cells and grants, complete request,
End, output and return delivery, and a matching local commit before the
next settled call. All such frames, fixed transport acknowledgements,
parser states, finite local work, copies and clearing are paid. They carry
no extra timing, meter, allocation or coefficient information.

Only commanded Ticks apply (96.2); Add and growth have exactly the listed
effects. Calls and material edits are
serialized, Hold permits arbitrary finite local calculation, and there is
no concurrent writer, autonomous Tick, crash or loss of authority. The
backing condition is sourcewise: every finite execution considered has
its required actual material. It is not a free finite uniform memory bound.
Quantification is over finite resource-supplied runs; every reserve or
replenishment is charged on that same run. A single fixed finite reserve
is not asserted to serve unbounded growth.
The installed zero provenance, calibration, original-root binding and
rights are hypotheses about the actual process. Root data do not certify
them. They and any retained provider or authority machinery remain in the
resource account.

**Proposition 96.3 (persistent realization and generation cost).** Every
$t\in\mathcal D$ has such a finite preparation. If that preparation has
$p$ promotions and $s$ splits, then

$$
N(t)=1+p+2s.
\tag{96.3}
$$

Its field at attachment is genuinely zero. Each coefficient is obtainable
from its actual parent's two records with fixed finite rational work.

**Proof.** AA Theorem 17.2 supplies exactly the legal generation words and
reachable domain. Each promotion allocates one vertex and each split two;
the retained marker in a split is not allocated twice. Induction over that
actual word gives (96.3), prefix preservation of all material addresses,
and zero fields, since no field command occurs. The new records use the
parent's already retained pair; changing a vertex from marker to logical
root changes no address and hence no old coefficient. Every allocation,
record computation, dispatch, grant and output is an actual paid step.
This does not reconstruct or retain the chosen serial word for free.

The source-side linear update also has a finite implementation without a
size query. Its fixed controller traverses actual material child links,
including unary markers, and writes each weighted old-neighbor sum into
that vertex's second buffer. Old values are retained throughout this pass.
A second traversal commits the buffers, then returns the updated root
scalar. A backed parent/continuation stack permits root return and detects
traversal completion by exhaustion of actual children, rather than a
supplied $N$. Structural induction on the finite material proves both
passes terminate and visit every vertex once. Each edge is traversed out
and back per pass, and at most three neighbor contributions enter a row.
Thus a Tick uses $O(N)$ rational work and link visits, with its actual
buffers, stack, synchronization and bit work paid. This source-side access
to its own physical incidence exposes no interior observer port or roster.
Serialized edits preserve the traversal premise at the next Ready cut.
$\square$

## 97. Spectral windows identify the actual ordered support

**Lemma 97.1 (one occupied window per material address).** For every
finite $t\in\mathcal D$ define

$$
I_p=[a_p,a_p+\ell_p],\qquad
J_p=[d_p-\ell_p/40,d_p+\ell_p/40].
\tag{97.1}
$$

The windows $J_p$ for distinct finite addresses are disjoint and contained
in $(0,1)$. The matrix $T_t$ has exactly one eigenvalue in each $J_p$ with
$p\in V_t$, no other eigenvalues, and simple spectrum. The same assertion
holds for every rooted principal subtree, retaining its original diagonals.

**Proof.** Relative to $I_p$, the child intervals occupy
$[1/8,1/4]$ and $[3/4,7/8]$, while $J_p$ occupies
$[19/40,21/40]$. Thus a vertex window is disjoint from every descendant
window, and the two child cones are disjoint. Comparing the first differing
letter, or the prefix relation, proves global disjointness. The relative
windows are strictly interior, including the root window.

At a nonroot vertex the sum of absolute off-diagonal entries is at most

$$
\ell_p/100+2\ell_p/800=\ell_p/80<\ell_p/40;
\tag{97.2}
$$

the root has no parent contribution. Removing a parent or child edge only
reduces this bound. Write the relevant matrix as $D+B$, with $D$ diagonal.
For every $0\le\tau\le1$, the eigenvalues of $D+\tau B$ belong to the
union of the present $J_p$. Indeed choose a largest absolute coordinate
of an eigenvector: its row equation gives
$|\lambda-d_p|\le\sum_{q\ne p}|\tau B_{pq}|$. This is the classical
Gershgorin argument; the pinned upstream
[`Matrix.eigenvalue_mem_ball`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Gershgorin.lean)
is the corresponding supplied inclusion result.

Inclusion alone would not prove one eigenvalue per window. For the count,
order the real eigenvalues decreasingly with multiplicity. The
[finite symmetric spectral theorem](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Matrix/Spectrum.lean)
gives an orthonormal eigenbasis. In dimension $m$, its min–max formula is
$\lambda_j(A)=\min_{\dim W=m-j+1}\max_{x\in W,\|x\|=1}x^{\mathsf T}Ax$,
for $1\le j\le m$: the span of eigenvectors $j,\ldots,m$ gives the upper
bound, and any such $W$ intersects the span of eigenvectors $1,\ldots,j$
nontrivially, giving the lower bound. This formula gives
$|\lambda_j(A)-\lambda_j(A')|\le\|A-A'\|$: every unit-vector Rayleigh
quotient changes by at most that norm, and taking the two nested extrema
preserves the bound. Thus each ordered eigenvalue is continuous along
$D+\tau B$. At $\tau=0$ exactly one lies in each present window, at its
center. There are finitely many present windows and positive gaps between
them. A continuous eigenvalue confined to their union cannot cross a gap.
The counts therefore remain one at $\tau=1$. This proves simplicity and
also proves the assertion for every rooted principal subtree. $\square$

**Theorem 97.2 (root cyclicity and ordered identification).** For every
$t\in\mathcal D$, all eigenvectors of $T_t$ have nonzero original-root
coordinate. The rational matrix

$$
K_t=[e,T_te,\ldots,T_t^{N-1}e],\qquad N=N(t),
\tag{97.3}
$$

is invertible. Moreover, for any $t,u\in\mathcal D$,

$$
\det(zI-T_t)=\det(zI-T_u)\quad\Longrightarrow\quad
V_t=V_u\quad\Longrightarrow\quad t=u.
\tag{97.4}
$$

Thus this law identifies the ordered native support, not just an
abstract root-cyclic similarity class or its tridiagonal representative.

**Proof.** Prove the eigenvector statement by induction over rooted
material subtrees. It is immediate for a singleton. Suppose a nonzero
eigenvector has zero coordinate at a subtree root. Its restrictions to
child subtrees satisfy their own eigenvalue equations. Their spectra lie
in the disjoint child intervals $I_{pL},I_{pR}$ by Lemma 97.1; hence at
most one restriction is nonzero. At least one must be nonzero. Its own
root coordinate is nonzero by induction. The equation at the parent root
then has exactly one nonzero term, multiplied by a positive edge weight,
and cannot equal zero. The unary case uses that same argument with one
child. This proves the claim at every subtree root.

Let $v_j$ be an orthonormal eigenbasis and $\lambda_j$ the distinct
eigenvalues. In this basis (97.3) has row
$\langle v_j,e\rangle(1,\lambda_j,\ldots,\lambda_j^{N-1})$.
All prefactors are nonzero and the Vandermonde determinant is nonzero.
The classical determinant identity is also supplied by pinned mathlib's
[`Matrix.det_vandermonde_ne_zero_iff`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Vandermonde.lean).
The rational determinant of $K_t$ is therefore nonzero, so its inverse
exists over $\mathbb Q$ as well.

Equal characteristic polynomials give the same eigenvalues with
multiplicity. Each eigenvalue belongs to exactly one globally defined
address window. Lemma 97.1 gives one such eigenvalue for every actual
material address and none for an absent address. The occupied address
sets must therefore agree. Finally arity parses the material support:
no children is alpha, one left marker child is beta, and two children
is a branch whose subterms are parsed recursively. The marker is consumed
by the beta clause, not parsed as a logical alpha. This is AA Definition
17.3's existing material parsing, applied to the identified support.
$\square$

The windows are used to prove uniqueness, not as a free spectral oracle.
The finite decoder below requires neither eigenvalue extraction nor an
unbounded search through all possible address windows.

## 98. A root-only trial earns size, ordered geometry and the advanced state

**Definition 98.1 (the fixed trial).** From the attachment cut of
Assumption 96.2, execute Hold; Add$(1)$; Read, storing its scalar as $m_0$.
For $n=1,2,\ldots$ execute two returning Ticks, storing $m_{2n-1},m_{2n}$,
then Hold. While held form the rational Hankel matrix

$$
H_n=(m_{i+j})_{0\le i,j\le n}.
\tag{98.1}
$$

Use exact finite rational elimination to test singularity. Continue when
it is nonsingular, and stop at the first singular $H_n$. There is no
runtime size bound or supplied geometry in this control. The local counter,
all entries, elimination work and zero tests have actual growing backing.
No $P/S$ or coefficient query occurs in the trial.

**Theorem 98.2 (finite acquisition at the actual endpoint).** For every
installation of Assumption 96.2 prepared at any $t\in\mathcal D$, the
trial terminates at $n=N(t)$, with literal moments

$$
m_j=e^{\mathsf T}T_t^je\quad(0\le j\le2N),\qquad
x_\star(t)=T_t^{2N}e
\tag{98.2}
$$

as its actual held field. Its source-call vector, excluding old preparation,
is

$$
(\mathrm{Add},\mathrm{Read},\mathrm{Tick},\mathrm{Hold})
=(1,1,2N,N+1).
\tag{98.3}
$$

There are $2N+1$ semantic scalar replies and $N+2$ fixed ACKs. Complete
transport and local work are additional costs, not extra source data.

**Proof.** Genuine zero and Add$(1)$ give $e$. Induction on actual Ticks
gives the field and scalar in (98.2) at every epoch; Hold and local work
leave them unchanged. Symmetry gives

$$
H_n=K_n^{\mathsf T}K_n,\qquad K_n=[e,T_te,\ldots,T_t^ne].
\tag{98.4}
$$

The first $N$ columns are independent by Theorem 97.2. Hence $H_n$ is
positive definite for $n<N$ and singular for $n=N$, since $N+1$ vectors
then lie in $\mathbb Q^N$. This includes $N=1$, where the first tested
matrix is $H_1$. Every completed call and finite local test finishes by
the installation assumptions. Counting the initial calls and the $N$
two-Tick stages proves (98.3) and the reply counts. No previous field is
restored and the endpoint is not $e$. $\square$

**Definition 98.3 (the paid finite decoder).** Having earned $N$, solve

$$
H_{N-1}c=-(m_N,\ldots,m_{2N-1})^{\mathsf T},\qquad
q(z)=z^N+\sum_{i=0}^{N-1}c_i z^i.
\tag{98.5}
$$

Enumerate finite valid syntax words with at most $N$ logical nodes, parse
them, and retain candidates in $\mathcal D$ of material size exactly $N$.
This is a finite enumeration: preorder words over alpha, beta and branch
with length at most $N$ suffice. Equivalently use the size clauses
$1,2,1+n_L+n_R$ and recurse on positive smaller child sizes, enforcing
the born-beta left-root restriction. For each candidate construct
(96.1)–(96.2), compute its rational characteristic polynomial by finite
polynomial determinant arithmetic, and compare it with the earned $q$.
Return the first match. Only one candidate need be stored at a time.
No source-specific catalogue, bound or hidden coefficient array is input.

**Theorem 98.4 (earned current representation).** This decoder terminates
with the unique actual ordered term $t$. It computes its actual calibration,
material addresses and field $x_\star(t)$ in original-root coordinates.
Retaining that code and field, together with the genuine binding and
current rights, installs the predictor of §100 on the same specimen.

**Proof.** The system (98.5) is nonsingular by (98.4). Its equations say
that $q(T_t)e$ is orthogonal to $e,T_te,\ldots,T_t^{N-1}e$. This basis
spans, so $q(T_t)e=0$. Taking coordinates in the eigenbasis, whose root
overlap is nonzero, gives $q(\lambda_j)=0$ for all $N$ distinct eigenvalues.
A monic degree-$N$ polynomial with those roots is exactly
$\det(zI-T_t)$. Every finite logical tree has at most as many logical
nodes as material vertices, so the actual $t$ occurs in the enumeration.
Its test succeeds. Any other success has the same characteristic polynomial
and hence the same ordered term by Theorem 97.2. Every earlier finite
candidate test terminates, proving finite decoding without an oracle.

From the earned $t$, the fixed recurrences compute all actual address
coefficients. Paid local multiplication computes $T_t^{2N}e$. The genuine
address-to-actual-cell correspondence is the one maintained by the original
persistent construction, not a freely chosen rerooting. Equation (98.2)
identifies this computed vector with the current field. The held source
is unchanged during decoding; retaining the model, program and real access
therefore establishes the required current invariant. Numerical agreement
does not manufacture access or validate the installation promises.
$\square$

This acquisition uses finite moment rank and annihilating-polynomial
reconstruction, mature supplied mathematics. Its additional step is the
source-specific implication (97.4) and its persistent implementation:
Jacobi reconstruction alone would leave actual ordered branching unresolved.

## 99. Four independent expressions on the earned canonical image

**Definition 99.1 (domain and meanings).** Fix the genuine installation
context of Assumption 96.2: specimen binding, address convention, current
rights and complete-service premises. For every $t\in\mathcal D$ let
$\Xi_t$ be its held, empty-parser cut after the trial and decoding, with
actual field $x_\star(t)$. Different legal pure preparation words ending
at the same $t$ are allowed. Define the following views of this one process.

Here $\Xi_t$ denotes the settled descriptor, not the complete past
trajectory. A later paid re-entry must produce the same current field and
a fresh literal unit-probe record; its earlier field controls are not
silently identified with the original pure preparation.

| View | Independently specified content |
| --- | --- |
| Space $\mathsf S_t$ | Actual ordered material incidence rooted at the original root, its local calibration and its current field |
| Time $\mathsf T_t$ | The labelled native generation events and their creating-parent/local-guard causal order |
| Boundary $\mathsf B_t$ | The literal ordered scalar record $(m_0,\ldots,m_{2N})$ actually returned by the root trial |
| Memory $\mathsf M_t$ | The earned live native syntax word and mutable original-address field record $(\operatorname{code}(t),\widehat x_\star)$ used by the predictor |

Space uses intrinsic original ordered coordinates, not allocator names or
internal access handles. Its recovery identifies the bound actual incidence
under that coordinate correspondence; it grants no extra ports. Memory's
syntax word is canonical constructor preorder, left subtree before right.
Space is an incidence/field object, not a supplied observer roster. Time
is the actual generation-dependency projection: branch events $S_p$,
promotions $P_p$ at born-alpha positions now non-alpha, creating-split
precedence, and promotion-before-split precedence at a position. These are
exactly AA (AA.67); they discard serial shuffles, waiting, field commands
and transport microsteps. Boundary exposes only the paid scalar port,
not an internal coefficient or endpoint certificate oracle. Memory is
mutable acquired working state, not an unrestricted history archive.
For example it need not retain which independent producer event happened
first. Keeping the literal Boundary record as an additional archive is a
separate paid choice; the layout of §102 keeps it.

The four view images consist exactly of these objects at $\Xi_t$ as $t$
ranges over $\mathcal D$. Numerical contents are fixed by the declared
probe schedule. The images are not all finite graphs, event orders,
rational lists or arbitrary current predictor records. The common context
is a parameter of every recovery statement, not recoverable authority
encoded in a scalar. Two distinct physical specimens with the same $t$
are not made the same specimen by recovering their mathematical content.

**Theorem 99.2 (all recovery routes on this image).** Every one of these
four views determines the actual ordered $t$, its current canonical field,
and the other three view contents. Every round trip is identity on its
specified image, and all routes with the same source and destination
agree. These are effective finite recoveries under paid exact rational
work. They neither recover a selected old serial word nor create a new
physical binding, grant or historical measurement event.

**Proof.** From Space, start at its given original root and recursively
parse ordered arity, consuming a beta marker in the unary case. This yields
the actual $t$, rather than an unrooted rival, and retains its actual
address correspondence. From Time, apply AA Theorem 17.2: the logical
positions are the root and children of listed splits; splits designate
branches, and at a remaining leaf its birth type and promotion membership
designate alpha or beta. The supplied theorem identifies these with the
actual native events and constructors, independently of a serial extension.
From Boundary, its odd list length gives the tested index; compute its
Hankel matrices and (98.5), then use Definition 98.3. On the declared image
Theorems 98.2–98.4 give that index as the actual $N$ and return exactly $t$.
From Memory, parse the live syntax word whose acquisition is Theorem 98.4;
its field record satisfies the current invariant.

Once $t$ has been recovered, the finite material recursion and (96.1)–(96.2)
construct the Space contents with $T_t^{2N}e$. AA (AA.67) constructs the
Time contents with precisely its actual generating events and dependencies.
Finite multiplication constructs the same scalar list $e^{\mathsf T}T_t^je$
that the trial actually returned. Syntax encoding and that same advanced
vector construct the Memory contents. Computing this list from another
view recovers its values; it does not repeat the old measurement or supply
its provenance. Every step uses a finite earned term and paid local work.

More explicitly, let $d_i$ be the respective four decoders just described
and let $f_i(t)$ be those independently defined contents. The preceding
arguments prove $d_i(f_i(t))=t$ and $f_i(d_i(v))=v$ for every $v$ in the
$i$th image. Hence the concrete recovery is
$R_{ij}(v)=f_j(d_i(v))$, and

$$
R_{ji}R_{ij}(v)=v,\qquad
R_{jk}R_{ij}(v)=R_{ik}(v)
\tag{99.1}
$$

for every $i,j,k$ and every such $v$. The non-generic obligations in these
identities are the actual ordered-support decoder, actual probe endpoint
and paid acquisition already established above. They are not supplied by
the identities themselves. $\square$

The source-only Time is intentionally coarser off this image. For the
singleton alpha, $T=[1/2]$ and $x_\star=1/4$. A raw Tick leaves the same
term and empty native causal order but makes the field $1/8$. Thus there
is no recovery of arbitrary raw field states from this Time view, even
in this smallest example. Replacing the chronological task by the native
causal task is explicit; it does not solve an unrestricted serial-history
inverse problem.

## 100. The acquired model serves the complete native menu

**Theorem 100.1 (current one-step and adaptive service).** At any settled
cut retain an earned current term $u$, its material calibration, and a
mutable vector satisfying

$$
\widehat x_p=x_{\iota_u(p)}\quad(p\in V_u),
\tag{100.1}
$$

where $\iota_u$ is the actual persistent original-address correspondence.
Retain the same callable binding, current rights, program, parser and
backing. Every complete request of Assumption 96.2 has a finite computable
complete reply and model successor agreeing with its actual reply and
source/field successor. Starting with the model earned in §98, this holds
for every finite common adaptive continuation, including unsuccessful
native requests and arbitrarily large finite addresses and rational inputs.

**Proof.** On Add$(q)$ add $qe$ to the retained vector and predict ACK.
On Read predict its root coordinate, without change. On Tick replace it
by $T_u\widehat x$ and return the updated root coordinate. On Hold retain
it and predict ACK. The local coefficient and edge correspondences make
these operations agree coordinate by coordinate on the actual source.

For $P_p,S_p$, navigate the retained logical syntax using the supplied
address, descending only at a branch. Missing position, branch target and
wrong leaf type give exactly the original distinct refusal and identity
successor. On successful promotion retain the value at $p$, add zero at
$pL$, and install its coefficients from the retained parent pair. On
successful splitting retain the values at $p,pL$ and all other old cells,
add zero at $pLL,pR$, and install their coefficients. In particular the old
marker value is not erased when it becomes a left beta root. The actual
material templates perform precisely these inclusions. Extend $\iota_u$
by the actual fresh cells; existing coefficients and all old coordinates
still agree. Predict the complete tagged Growth reply. The required fresh
rights belong to the actual installation, not to the computed map.

This is NLBA Theorem 12.1's persistent-field/native-guard correspondence
with its terminal-ordinal field operations replaced by (96.2) and the present
returning Tick. The preceding formulas check that replacement explicitly;
no terminal roster or Reset is used. Complete BadFrame has the same identity
successor. The fixed parser can track a supplied proper prefix using its
actual pending bytes; there is no premature completed reply. Disabled or
unbacked calls are outside the theorem's completed-service domain.

At the acquisition return, Theorem 98.4 establishes (100.1) with the actual
$T_t^{2N}e$. Update the retained record only in its serialized corresponding
transaction, and expose the next Ready cut after the complete reply and
commit. Induction on completed requests preserves (100.1), original native
syntax, calibration and the entire reply. Equal prior observations and
common retained inputs make a common adaptive policy choose the same next
request, rational operand and stopping decision. Fixing a common
source-independent random tape proves the same statement for each finite
realized randomized continuation. This is the existing adaptive-service
induction, now initialized by the root-only acquisition on this actual
source. Merely computing a successor does not execute a physical request.
$\square$

**Corollary 100.2 (actual selection without a free selector).** A later
task supplies a finite native address and request, or an explicitly given
finite policy acting on the earned current record and earlier replies.
The retained syntax decides its guards and expected outputs, and the
retained entry issues the real request. In particular a current global
substitution $\rho$ is implementable by listing the current logical leaves
from that earned syntax, then applying $P$ at each current alpha and $S$
at each current beta, once, without visiting newborns. If there are
$a$ alpha and $b$ beta leaves, this uses exactly $a+b$ original growth
requests, $a+2b$ fresh material vertices, and their complete Growth replies.
It leaves $\rho(u)$ with all old fields and coefficients retained and all
fresh fields zero.

**Proof.** Guard lookup is the finite navigation used in Theorem 100.1;
its input is a real task or earned code, not unknown source advice. The
current leaves are an antichain, so editing one does not alter another's
constructor or address. The native templates therefore apply once at each
listed leaf and give exactly the defining substitution. The field statement
follows by composing the zero lifts. This uses the already supplied
NLBA Proposition 12.3 mechanism; the calibrated coefficients additionally
persist by Definition 96.1. All list construction, local control, frames,
navigation, grants and fields remain paid. $\square$

**Theorem 100.3 (exact continuation equivalence at Ready cuts).** In the
fixed complete-service context, two settled finite calibrated states
are indistinguishable by every finite common experiment in the full menu
of Assumption 96.2 if and only if their ordered terms and original-address
fields are equal. For a fixed term of size $N$, the root window

$$
\mathcal O_u x=(e^{\mathsf T}x,e^{\mathsf T}T_ux,\ldots,
 e^{\mathsf T}T_u^{N-1}x)
\tag{100.2}
$$

is an equivalent finite current-field record. On the canonical image of
§99, every view has exactly this task equivalence kernel.

**Proof.** Equal term and field give equal complete outputs and successors
by Theorem 100.1. If terms differ, descend to a first differing constructor;
all its strict ancestors are common branches, so its address exists in
both. A $P$ request there yields success at alpha, wrong-type refusal at
beta, and branch refusal at a branch. Thus the terms are distinguishable
regardless of their fields. This is an existence argument for a separating
finite literal request, not a free runtime address oracle.

For equal terms, symmetry and invertibility of $K_u$ make
$\mathcal O_u=K_u^{\mathsf T}$ invertible. If fields differ, at least one
entry of (100.2) differs. Read followed by at most $N-1$ returning Ticks
exposes all these entries on the actual field, without a reset or pulse.
It is a uniformly executable field test after $N$ has been earned. Conversely
(100.2) recovers $x$ by paid rational solution and thus predicts the whole
menu. If that window is actually acquired by this test, the specimen ends
at $T_u^{N-1}x$ and any continued current predictor is advanced to that
vector. The test is not a nondisturbing observation of its entry field.
The general fixed-dimension observability/Gram equivalences are the
existing D5 suppliers cited in §103; the new source-specific premise here
is the proved cyclicity and actual acquisition of $u$.

At $\Xi_t$, its field is determined by $t$ and the actual acquisition
schedule. Theorem 99.2 shows that equality of any one view is exactly
equality of $t$. Distinct terms have the separating native request just
proved; equal terms have equal canonical fields. This proves the final
kernel statement. It asserts sufficiency for current continuation, not
retention of every old observation or serial producer choice. $\square$

## 101. Raw dynamics and a separately charged return to the image

**Definition 101.1 (paid return).** Suppose one complete raw request has
been executed from an acquired state and its actual successor is $(u,z)$,
known to the retained predictor. Set $n=N(u)$ and $T=T_u$. For this return
procedure issue Hold and locally form the controllability matrix

$$
C_u=[T^{n-1}e,T^{n-2}e,\ldots,e].
\tag{101.1}
$$

Solve $C_uv=e-T^nz$. Then execute, for $i=1,\ldots,n$, the two actual
commands Tick; Add$(v_i)$. Issue Hold; Read and retain this Read as a new
$m_0$. Execute $n$ pairs of returning Ticks, each pair followed by Hold,
retaining their $2n$ scalars as the new moment prefix. Decode or check the
already known term and update the current retained field. The raw request
and this return procedure form a new composite operation; the return is
never implicit in the meaning or cost of a raw request.

**Theorem 101.2 (real return, full transcript and exact call vector).**
For every finite acquired $(u,z)$ in this model, Definition 101.1 terminates
at the actual canonical field $T_u^{2n}e$ on that same specimen and syntax.
Beyond the raw request, it uses exactly

$$
(\mathrm{Tick},\mathrm{Add},\mathrm{Read},\mathrm{Hold})
=(3n,n,1,n+2).
\tag{101.2}
$$

Its semantic output word contains $3n+1$ literal scalars and $2n+2$ ACKs,
in actual order, in addition to the complete raw output. It does not
suppress control-phase Ticks, field transients, native refusals or returns.

**Proof.** Theorem 97.2 makes (101.1) invertible, since it reverses the
columns of $K_u$. The rational amplitudes therefore exist and are computable
from the earned current $u,z$, with paid finite work and precision. If
$w_0=z$, the actual Tick/Add pairs satisfy

$$
w_i=Tw_{i-1}+v_i e,\qquad
w_n=T^nz+\sum_{i=1}^n v_iT^{n-i}e=e.
\tag{101.3}
$$

The first return-phase Hold allows that computation without an autonomous
field change. The next Hold; Read returns $1$, and the last $2n$ actual
Ticks yield exactly $m_j=e^{\mathsf T}T^je$, ending at $T^{2n}e$.
All calls and local work are finite under the same backing premises.
There are $n$ control Ticks, $n$ control Adds, one initial Hold, one
post-control Hold/Read and $n$ final Hold stages. This proves (101.2).
Each control Tick emits its actual $e^{\mathsf T}Tw_{i-1}$; each Add and
Hold emits ACK; the final Read and Ticks emit their actual scalars.
These account for every semantic reply. Fixed framing, End and return
outputs are additionally transmitted and charged as in Assumption 96.2.
There is no Reset, cloned branch, hidden state read or retroactive claim
that the raw successor was canonical. $\square$

**Corollary 101.3 (precise compatibility of dynamics).** For a complete
raw request $r$ admitted at a canonical Ready cut, let its actual ordered
successor be $g_r(t)$ and let $W_r(t)$ be the complete output word of that
raw request followed by Definition 101.1. For every view $i$, define the
composite action by decoding its earned $t$, predicting that complete
word by Theorem 100.1 and (101.3), and returning

$$
\bigl(W_r(t),f_i(g_r(t))\bigr).
\tag{101.4}
$$

Recovery between any two views commutes with these composite actions,
including their entire output words. It also gives the correct raw output
and raw successor in the full $(t,x)$ predictor, without claiming that raw
successor belongs to the canonical four-view image.

**Proof.** A successful $P/S$ changes the syntax by precisely its native
rule; every field request, refusal or BadFrame leaves syntax unchanged.
Theorem 100.1 computes the actual raw field $z$ and all raw outputs from
the earned canonical model. Theorem 101.2 returns that actual successor
to $\Xi_{g_r(t)}$, with the same word predicted in every view because all
decode to the same $t$. Filtering the run to successful native growth
leaves a legal AA word ending at $g_r(t)$, so its Time is the actual native
causal projection. Its Boundary is the fresh literal unit-probe block;
the complete word still includes the control scalars outside that block.
Equation (99.1) therefore transports (101.4)
identically on every route. This proves a labelled input/output
compatibility, not merely equality of final terms. A proper incomplete
prefix has no completed raw successor and hence no completed composite;
its pending parser state is handled by the full service, not by (101.4).
$\square$

For a multi-request native macro such as $\rho$, one may predict every raw
intermediate state and apply one return after the whole macro. Its extra
vector is (101.2) with $n=N(\rho(u))$. Returning after each constituent
request is a different, more expensive execution with different intermediate
fields and outputs. Neither execution changes the native macro's literal
raw semantics. The singleton counterexample after Theorem 99.2 prevents
extending (101.4) to all raw actions while retaining the same four images.

## 102. One simultaneous operation, storage and precision account

**Proposition 102.1 (finite exact resources for acquisition and use).**
The acquisition, decoder and retained service have finite exact rational
implementations on each finite promised source. They have the source-call
vectors (98.3) and (101.2), with the following sufficient unoptimized
account. No minimum number of Ticks, bits, coefficients, rights or total
cost is asserted for this calibrated alternative.

Let $H$ be the actual maximum material depth, known to the analyst but not
an initial controller input. For a depth-$h$ material vertex,

$$
\ell_p=8^{-h},\qquad a_p=A_p/8^h,\qquad
A_{pL}=8A_p+1,\quad A_{pR}=8A_p+6.
\tag{102.1}
$$

All local coefficients have $O(h+1)$ bits. Put $D=100\cdot8^H$. Every
coefficient denominator divides $D$. Throughout the passive trial, at
Tick epoch $k$, all fields and returned scalars have denominators dividing
$D^k$, values in $[0,1]$, and reduced word widths
$O(1+k(H+1))$. In particular the literal prefix through $2N$ takes
$O(N^2(H+1))$ numerical bits. This is exact finite precision per run,
not a lifetime-uniform precision or a noisy-data stability bound.

Testing successive Hankel matrices afresh takes $O(N^4)$ rational
operations. Extraction of (98.5) takes $O(N^3)$. There are fewer than
$3^{N+1}$ syntax words of length at most $N$. A deliberately simple
candidate polynomial determinant, summing over $N!$ permutations and
multiplying their $N$ linear factors, takes $O(N!\,(N+1)^3)$ rational
operations per candidate. Hence a sufficient total numerical-operation
bound for acquisition, including actual sparse source Ticks and local
formation of the current field, is

$$
A_N=O\bigl(N^4+3^{N+1}N!\,(N+1)^3\bigr).
\tag{102.2}
$$

Syntax enumeration, comparisons, address manipulation, framing, integer
arithmetic and output delivery are actual additional work. This finite
bound is not a polynomial-time or efficient-decoder claim.

A concrete conservative bit account is available even without a sharp
elimination estimate. Let $A$ be the actual number of rational additions,
subtractions, multiplications and divisions in this implementation, so
$A\le A_N$ with a suitable fixed constant in (102.2). Let $b$ bound the
initial reduced numerical word widths used by it. One may take
$b=O(N(H+N+1))$, covering the acquired moments and every size-$N$
candidate's locally constructed depth coefficients. Reducing rational
words after each operation gives the sufficient maximum width

$$
W\le (b+2)2^{A+1}.
\tag{102.3}
$$

This intentionally loose bound includes exact zero decisions and does not
price a rational operation as a unit-cost physical primitive. Schoolbook
integer multiplication/division, signed addition, comparison and Euclidean
reduction at widths at most a constant times $W$ supply finite bit work
for every such operation, all charged separately; their integer scratch
can be streamed in $O(W)$ bits.

With one candidate and one permutation processed at a time, a sufficient
simultaneous layout uses $O(N^2)$ rational slots and
$O(N(H+N)+N\log(N+1))$ address, syntax and indexing bits, plus the actual
installation and communication material. The rational slots include the
physical field and Tick buffer, retained current model and its work buffer,
literal moments, Hankel/elimination workspace, $c,q$, candidate matrix,
polynomial accumulators and reconstruction scratch. Thus their numerical
storage is at most $O(N^2W)$. One need not retain all candidate matrices
or all permutations simultaneously. Keeping source and observer arrays,
or returned and archived records, in distinct places counts their copies
separately; sharing one actual array counts it once.

**Proof.** Formula (102.1) follows immediately from (96.1), with
$0\le a_p<a_p+\ell_p\le1$. The diagonal denominator divides
$2\cdot8^h$ and the parent edge denominator divides $100\cdot8^h$, both
divisors of $D$. Nonnegative row sums of $T_t$ are less than one:
$d_p+\ell_p/80<a_p+\ell_p\le1$, with a still smaller root radius.
Thus $T_t$ preserves the unit cube. Multiplying $D T_t$, an integral
matrix, repeatedly gives denominator divisibility and the asserted bit
bound for $T_t^ke$. Nonnegative partial row sums satisfy the same magnitude
bound. Summing the word widths over the acquired prefix proves its storage
bound; none of these internal cells is thereby observed for free.

Rational elimination is a finite pivot-search algorithm, using $O(n^3)$
operations on an $(n+1)$-square Hankel matrix; its singular pivots are
explicit zero tests. Summing over $n\le N$ proves $O(N^4)$. The promised
nonsingular solve and each finite determinant calculation terminate.
A preorder word has at most $N$ symbols, giving the enumeration bound.
Each determinant product and its coefficient accumulation need only a
polynomial-size workspace, yielding (102.2) with the stated simple
algorithm. Every candidate depth is at most $N-1$, so its initial
coefficient widths fit the bound on $b$.

For (102.3), if all previous numerator/denominator widths are at most
$B$, one rational operation before reduction has widths at most $2B+2$;
reduction cannot increase them. Solving this scalar recurrence gives the
bound. Divisions are used only after a nonzero pivot test. Euclidean
reduction terminates by strict decrease of positive remainders, so the
associated integer work is finite as well. The matrices and vectors just
listed use only a constant number of square arrays and linear arrays;
streaming syntax words and permutations avoids an exponential simultaneous
list. Material address lengths sum to at most $N(H+1)$, and candidate
addresses to $O(N^2)$. This proves the layout claims. $\square$

**Definition 102.2 (material that remains charged).** In addition to those
arrays, count the actual $N$ source vertices, $N-1$ links, stored local
pairs and coupling machinery, all initial and fresh zero writes, original
root reference and $L/R$ dispatch, program, held scheduling, current and
fresh authority grants, reserved fresh material, and every provider or
backing object actually retained to make these facilities callable. Count
the actual pending request/output/End/return buffers, counters, parser,
transport acknowledgements, returned code and certificates, and all retained
archives. Their actual bit storage and cell/link counts are separate
resource coordinates; none is bounded by the length of an opaque handle. If their chosen
implementation retains the old preparation word or allocation history,
that archive is charged although the decoder never reads it. Clearing an
array or archive is an actual finite write sequence; retaining it continues
to occupy its material.

For an explicit simultaneous bit bound, let $B_{\rm extra}(c)$ count actual
retained bits of installation, communication and archives outside the
counted arrays at cut $c$, including their authority/provider backing and
avoiding overlap. Acquisition peak storage is bounded by the maximum,
over cuts of this same run, of
$O(N^2W+N(H+N)+N\log(N+1))+B_{\rm extra}(c)$.
Transmitted bits and arithmetic bit work are separate resource coordinates;
neither is inferred from the number of scalar replies.

Old preparation contributes its $p+s$ genuine growth transactions, its
$1+p+2s$ material cells and zero writes at birth, their coefficient
installation, navigation and grants, and its complete outputs. On the
trial's one actual run, the $2N$ sparse field updates use $O(N^2)$ rational
operations on the actual source, in addition to the observer's work.
Initial trial costs are $3N+3$ semantic source transactions in total,
not just the informative scalars. If the returned acquisition payload
contains the earned term, size, $q$, literal prefix and current field,
its encoding, return and every copy are charged. The genuine bound entry
and rights remain owned after that return.

In the fixed framing realization, each completed transaction additionally
has one input End, one output End, one LocalACK and one Return. Thus each
of these four token counts is $3N+3$ for the trial and $5n+3$ for a paid
return alone. Payload bits, copies, navigation and finite local updates
are charged in addition to those fixed tokens. No incomplete prefix is
counted as an already completed transaction.

For a later finite continuation, charge each actual current tree and its
fresh extensions, all requested address and operand words, all replies and
new numerical widths, local predictor updates and any simultaneous record
copies. Each paid return additionally solves a finite $n$-square rational
system, computes its $n$ pulse amplitudes, transmits them, performs its
$3n$ actual field updates and retains or consumes its $3n+1$ scalars and
$2n+2$ ACKs. Its finite arithmetic admits the same width recurrence with
its actual initial $z$ and operands; there is no uniform amplitude bound
being assumed. Arbitrarily long finite operands, arbitrarily deep growth
and arbitrarily many Ticks prevent a uniform lifetime bit or memory bound.

**Proposition 102.3 (what the indispensable premises buy).** In the
nonediting root field menu, if the observer never injects a nonzero Add
from the zero preparation, every scalar is zero on every term. Such a
record cannot acquire geometry. Conversely the present one-pulse trial
needs no further field port or size/roster query. Genuine binding, rights,
completion and the declared calibration supply operational facilities
which are not consequences of scalar identifiability. Equality of all
future task replies requires the current information in Theorem 100.3;
it does not require a serial producer archive.

**Proof.** With no nonzero Add, zero is invariant under the linear update,
Read and Hold. The positive assertion is Theorem 98.4, and exact current
information sufficiency and necessity are Theorem 100.3. These observations
concern the declared task and menu; they do not compare total costs of all
alternative generators, installations or encodings. $\square$

## 103. Uniform scalars, serial history and exact supplier boundaries

**Proposition 103.1 (uniform root data do not identify ordered guards).**
Consider instead a uniform law $aI+cA$ on the same native material, with
common rational $a,c$ and genuine zero preparation. The two reachable
ordered sources

$$
t_1=\langle\beta,\langle\beta,\alpha\rangle\rangle,\qquad
t_2=\langle\langle\beta,\alpha\rangle,\beta\rangle
\tag{103.1}
$$

have identical complete root Add/Read/returning-Tick/Hold observations
under every common finite adaptive policy, but different original guards.
This remains true for an arbitrarily long root field experiment.

**Proof.** They are generated respectively by
$P_\varepsilon S_\varepsilon P_R S_R$ and
$P_\varepsilon S_\varepsilon S_L P_R$, so both belong to $\mathcal D$.
Each has seven material vertices. Swapping the two root child subtrees
is a root-fixing unlabelled graph isomorphism between their material trees.
Its permutation matrix $U$ satisfies $Ue=e$ and
$U(aI+cA_1)=(aI+cA_2)U$. Initial zero, every root Add, Tick, Read and Hold
therefore preserve conjugate states and equal entire replies. Induction
includes adaptive choices, exact rational operands, identical framing and
a common random tape. Yet $P_L$ yields wrong-type refusal on $t_1$ and
branch refusal on $t_2$. No amount of reduced uniform scalar information
selects those ordered native guards. $\square$

The address-dependent calibration (96.1) breaks precisely that conjugacy
hypothesis. It does not refute the existing uniform path/endpoint results
or turn their negative branch into whole-tree identification. Sections
77–82 concern $aI+cA$ on subcubic trees, rational positive-link symmetric
endpoint competitors, a first-departure certificate and its exact Tick
horizon. Their positive branch gives an endpoint path and their negative
branch excludes the competitor without identifying the remaining tree.
Those statements and costs remain their exact suppliers. The present
$2N$-Tick acquisition is an attained construction under a different law,
not a transferred lower bound or total optimum.

AA Theorem 17.2 supplies the actual causal order and its source inverse;
AA Definition 17.3 supplies material parsing. Neither recovers a chosen
serial extension: independent events can be shuffled with the same final
term. NLBA §§10–12 supply the persistent vertex/zero-lift templates and
native guard/adaptive-service method, with a complete ordered terminal
roster and different field ports and law. Removing that supplied roster
requires the proof of §§97–98; it cannot be licensed by the old inverse.
[Atomic Generation Acquisition II, §§68–70](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md#68-a-recoverable-source-encoding-on-the-original-lab-attachment)
supply a different acquisition through a destructive split sweep ending
at its encoded $J(t)$ and a represented service on that image. Their actual
raw/composite distinction is retained here, not counted as a new abstract
replay theorem.

The scalar-alphabet and later-vector results in §§84–95
already supply their full-digit iff, their restricted total recognizer,
paid entrance and continued-service statements. Their exact actuator
alphabets, certificates, later-field domains and task scopes remain in
force. They are not additional outcomes of this calibrated branching
construction, nor an excuse to omit its actual zero entrance and root
experiment.

The relevant D5 suppliers have different inputs. Module paths below are
under `D5/S3/`, with paired owning Scribes under `Blueprint/D5/S3/`. In
`Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition`, including
its private coordinate, enumeration and uniqueness helpers and owning
Scribe, `original_rigidity` and `effective_inverse` assume a full unrooted
finite adjacency presentation, complete linear terminal order and at least
three logical leaves. They identify original material coordinates under
those inputs; they do not acquire them from one scalar port. In
`Arith/FibonacciAtomic/Observer/NativeUniformTree`, private navigation and
readout helpers interpret an already given native code.
`NativeFullSourceProducer.native_source_producer`, with its private
traversal and stationarity proofs and owning Scribe, acquires by actual
logical reads and retains its native chronology. That is a different
observable port from this root field trial.

`Observer/Linear/FiniteObservabilityEquivalence.finite_observability_equivalence`
and `ObserverMemory/Dynamics/FiniteTimeTomographySaturation.all_future_kernel_eq_finrank_kernel`
supply fixed finite-dimensional observability and the Cayley–Hamilton
finite-horizon principle. `Analytic/GoldenTomography/FinitePronyHankelReconstruction`
supplies the Hankel/Vandermonde reconstruction substrate under distinct
nodes and nonzero weights. The present spectral and root-overlap proofs
establish those conditions for the actual material; matrix factorization
alone would not. `Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial`,
including its private Gram–Schmidt/coordinate proofs and owning Scribe,
constructs a multiplication/Jacobi characteristic polynomial from supplied
coefficients, bases and positive Hankel hypotheses. Such a representative
is not by itself the ordered native source. These are reused mathematical
suppliers, not new formalization claims.

For classical provenance, [Teschl, *Jacobi Operators and Completely
Integrable Nonlinear Lattices*, §2.5](https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf)
gives cyclic vectors, moment pairings and the orthogonal-polynomial
construction in (2.94)–(2.118); the paragraph following Theorem 2.13 treats
finite-support breakdown and the finite Jacobi matrix. Gershgorin inclusion,
finite symmetric spectral theory, Vandermonde invertibility, finite moment
rank and single-input controllability are mature mathematics. The finite
procedures here use exact rational arithmetic rather than a claim that
spectroscopy yields exact real numbers at no cost.

[Burgarth and Maruyama, *Indirect Hamiltonian Identification through a
small gateway*, §§II–IV](https://arxiv.org/abs/0903.0612v1) assume a known
coupling graph, Heisenberg interaction with known anisotropy and their
coupling-sign conditions; their gateway theorem uses an infecting set,
and their acquisition uses the stated preparation and tomography. A
branching root alone need not be such a gateway. Their result is not an
unknown ordered-native-topology inverse and supplies no physical bridge
for (96.2). The address-window/native-service connection is a
repository-derived source-specific synthesis of these credited methods;
search absence is not a claim of source or world novelty.

The retained limits are exact. Canonical four-view recovery does not
recover arbitrary raw fields from native causal Time, old serial shuffles,
all busy states, unavailable rights, or an unknown nonzero entrance.
Failure of calibration, zero provenance or source binding is outside the
proved promise and is not authenticated by a matching finite record.
Exact zero tests have no established noisy-data replacement; shrinking
windows and small couplings give no uniform conditioning bound. The
construction supplies no universal alpha/beta minimum, common
native/path/quantum realization, physical evolution law, or solution of
the unchanged original fixed-$G_{\rm gc}$/original-$Q$ obligations. Those
require their actual model and task bridges. The broader four-expression
objective therefore retains those unresolved domains.

## 追加锚（本行以下为增补区）

## 104. One shared input and the exact rational-origin dichotomy

**Definition 104.1 (the cyclic rational spectral class).** Fix $N\ge2$, $T\in\mathbb Q^{N\times N}$ and $b\in\mathbb Q^N$ such that $K=[b,Tb,\ldots,T^{N-1}b]$ is invertible. Suppose the $N$ eigenvalues, counted with multiplicity, are reduced fractions $\lambda_i=r_i/s_i$, with $1\le r_i<s_i$, $s_i\ge2$, and $\gcd(s_i,s_j)=1$ for $i\ne j$. Put $a=\prod_i s_i$ and $D_a=\{0,\ldots,a-1\}$. There is one input: a digit $d$ acts on the whole field by $x\mapsto Tx+db$. For a fixed rational origin $v$ and a chronological word $u\in D_a^L$, including the empty word, write $X_v(u)=T^Lv+\sum_{j<L}u_jT^{L-1-j}b$. Normalize rational left eigenrows by $h_iT=\lambda_i h_i$ and $h_ib=1$, and write $h_iv=p_i/q_i$ in lowest terms, $q_i>0$, with $0=0/1$. The rows and their normalization are justified below. The abstract class needs cyclicity, not symmetry; its actual-service specialization is the symmetric positive-link path of §36 with $b=e_0$. In that specialization each digit is literally Tick; Add$(d)$; Read, with the intermediate Tick scalar, the complete declared Add reply and the final Read scalar all retained or consumed as actual outputs.

**Theorem 104.2 (all rational origins, with a common-input converse).** For every pair and every origin in Definition 104.1, the map $X_v:\coprod_{L\ge0}D_a^L\to\mathbb Q^N$ is injective if and only if $s_i\nmid p_i$ for at least one $i$. At each fixed length it is injective for every origin. If $s_i\mid p_i$ for every $i$, two different positive prefixes of one legal common-digit run have exactly the same whole field. Proof of the algebraic prerequisites and fixed-length assertion. Distinct reduced denominators give distinct eigenvalues. Rational elimination supplies a nonzero rational left eigenrow at each rational eigenvalue. If it annihilated $b$, it would annihilate every column of $K$, which is impossible; hence normalization is legal. In a dependence between the normalized rows, right multiplication by $\prod_{j\ne i}(T-\lambda_j I)$ isolates the $i$th row with a nonzero multiplier. Thus their matrix $E$ is invertible. Put $Q(z)=\prod_i(s_i z-r_i)$. Modulo any prime each factor is a nonzero polynomial, since $\gcd(r_i,s_i)=1$; their product remains nonzero. Hence $Q$ is primitive, has leading coefficient $a$, and $Q/a=\det(zI-T)$. For any rational polynomial $P$, divide by this monic characteristic polynomial. Its remainder has degree below $N$; if $P(T)b=0$, the remainder annihilates $b$ and invertibility of $K$ forces all its coefficients to vanish. Thus $P(T)b=0$ exactly when $Q$ divides $P$ over $\mathbb Q$. The whole-law supplier of §44.3, specifically primitive Gauss divisibility over $\mathbb Z\subset\mathbb Q$, gives an integer quotient when $P$ is integral. A nonzero such $P$ has leading coefficient of magnitude at least $a$. The difference of two equal-length digit polynomials has every coefficient of magnitude at most $a-1$, so it cannot be a nonzero annihilator. The common homogeneous term $T^Lv$ cancels, proving fixed-length uniqueness without any origin restriction.

Proof of the favorable implication. If $s_i\nmid p_i$, choose a prime $\ell\mid s_i$ with $\nu_\ell(p_i)<e=\nu_\ell(s_i)$, and set $c=\nu_\ell(h_iv)<e$. In particular $h_iv\ne0$. The projected update is the actual identity $h_i(Tx+db)=\lambda_i h_ix+d$. Since $\ell\nmid r_i$, Tick decreases its nonzero valuation by $e$. Starting at valuation $c$, the first such result has negative valuation. An integer digit, including zero, cannot cancel it or alter that valuation: after taking a common denominator divisible by $\ell$, the numerator of the negative-valuation summand is an $\ell$-unit and the integer contributes an $\ell$-multiple. Induction therefore gives $h_iX_v(u)\ne0$ and $\nu_\ell(h_iX_v(u))=c-Le$ for every $L\ge0$. This is exactly the nonzero scalar valuation mechanism already used in §§60 and 84, applied to one earned eigenrow. Equality of whole endpoints forces equal lengths; the whole-law fixed-length result then forces equal words. The projection supplies a length clock, not the vector's digit inverse.

Proof of the common-input converse. Suppose $s_i\mid p_i$ for every $i$. Reducedness implies $\gcd(q_i,s_i)=1$; set $k_i(0)=p_i/s_i\in\mathbb Z$. For every integer vector $k$, choose the unique $d(k)\in D_a$ satisfying $q_i d(k)\equiv-r_i k_i\pmod{s_i}$ simultaneously for all $i$, and set $F_i(k)=(r_i k_i+q_i d(k))/s_i$. Euclid computes the inverses of the $q_i$, and the ordinary Chinese remainder theorem for the positive pairwise-coprime moduli supplies this one bounded digit. All $F_i(k)$ are integers. Define $\ell_i=\min(k_i(0),0)$, $U_i=\max(k_i(0),\lceil q_i(a-1)/(s_i-r_i)\rceil)$ and $R=\prod_i(U_i-\ell_i+1)$. The integer box $\mathcal B=\prod_i([\ell_i,U_i]\cap\mathbb Z)$ contains $k(0)$ and is invariant: for $k\in\mathcal B$, $F_i(k)\ge r_i\ell_i/s_i\ge\ell_i$ and $F_i(k)\le(r_iU_i+q_i(a-1))/s_i\le U_i$. On the actual source issue precisely the digits $d(k(t))$, with $k(t+1)=F(k(t))$. The induction $h_ix_t=s_i k_i(t)/q_i$ follows from $\lambda_i s_i k_i/q_i+d=(r_i k_i+q_i d)/q_i=s_iF_i(k)/q_i$. Among $k(1),\ldots,k(R+1)$ two agree, at $1\le t<t'\le R+1$; invertibility of $E$ makes $x_t=x_{t'}$ on this very trajectory. The prefixes have different positive lengths. Determinism propagates the repetition, so arbitrarily many distinct finite prefixes can have a common field when their actual finite backing is supplied. This last step is the finite-self-map supplier: [FiniteOrbitPeriodBound](../../../D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean), with its [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.scribe.cs), applies to $\mathcal B$, $F$, initial state $k(1)$ and readout $k\mapsto E^{-1}(s_i k_i/q_i)_i$. The new conditions supplied here are the common legal digit, the invariant box and its actual pulse correspondence. Separate scalar cycles with independently chosen digits would not prove this conclusion. Old reply archives and counters can differ at the repeated cuts; the equality is of fields and common future source service, not complete past transcripts. $\square$

## 105. A law class outside every determinant-unit certificate

**Proposition 105.1 (separation of certificate classes).** No pair of dimension $N\ge2$ in Definition 104.1 admits any certificate (87.3): for every positive integer $m$ with $mT$ integral, every prime dividing $m$ divides $\det(mT)$. Proof. A rational eigenvalue of an integral matrix is an integer: if $u/v$ is reduced and satisfies its monic integer characteristic polynomial, multiplication by $v^N$ forces $v\mid u^N$, hence $v=1$. Applying this to $mr_i/s_i$ gives $s_i\mid m$ for every $i$. For a prime $\ell\mid m$, at most one $s_i$ is divisible by $\ell$. Since $N\ge2$, choose $j$ with $\ell\nmid s_j$. Then the integer eigenvalue $(m/s_j)r_j$ is divisible by $\ell$. All the other scaled eigenvalues are integers, so their product $\det(mT)$ is divisible by $\ell$. This excludes every denominator clearing, rather than only the least one. It separates the stated sufficient-certificate law classes; it does not make failure of that older certificate an impossibility theorem for recovery. Theorem 104.2 supplies a positive recovery criterion in this disjoint class.

The class has infinitely many actual two-cell path witnesses. For any coprime integers $2\le p<q$, take $T=\frac12\begin{pmatrix}1/p+1/q&1/p-1/q\\1/p-1/q&1/p+1/q\end{pmatrix}$ and $b=e_0$. The off-diagonal entry is positive, the eigenvalues are $1/p,1/q\in(0,1)$, and the normalized rows are $(1,1)$ and $(1,-1)$. The two-column $K$ has nonzero determinant equal to the off-diagonal entry. Thus every hypothesis of the actual path specialization is met; taking $p=2$ and arbitrarily large odd $q$ gives infinitely many laws. The $p=2,q=3$ member is already [Unknown Field Native Startup, Proposition 32.2](RECURSIVE_RELATIONAL_OBSERVATION_UNKNOWN_FIELD_NATIVE_STARTUP.md#32-exact-countermodels-and-incomparable-entrances), not a new matrix example. No existence in every dimension is asserted. There is also a precise reason to keep the whole vector in the inverse: for any fixed $i$, the distinct allowed length-two words $(s_i,0)$ and $(0,r_i)$ have the same $i$th projection, because $s_i\lambda_i=r_i$. They are allowed since $s_i<a$, and their whole-field difference is $(s_iT-r_iI)b\ne0$ by cyclicity and $N\ge2$. The length clock therefore cannot be substituted for the whole-law equality test. These examples are consumers of the classification and its distinction from §87, not additional classification outcomes. $\square$

## 106. Earned law selection and a prospective origin on the same path

**Theorem 106.1 (the installed path consumer).** Retain exactly §36's unknown rational symmetric positive-link path, $0<T<I$, authentic initial $b=e_0$, literal Read, scalar-returning Tick, authorized rational Add and Hold. Keep the genuine root binding, fixed exact serialization, exclusive completed calls, no autonomous motion, protected finite local work and sufficient actual finite source, observer and completion backing. Neither $N$, coefficients, a spectral basis, a later entry field nor a response table is initially supplied. The actual acquisition of §37, followed by a finite numerical class test, either locally declines Definition 104.1's subclass or earns $N,T,Q,K,\mathcal O=K^{\mathsf T}$ and $E$ in the actual native coordinates. On acceptance, after every finite completed legal segment $W$ preserving this law and the needed access, a paid window and at most one Add earn a favorable retained prospective origin $v$. The law acquisition actually ends at $T^{2N}b$; the later entrance described below actually ends at $v$. This is acquisition before $W$, followed by a new origin, not arbitrary-entry unknown-law startup.

Proof of the acquisition and class test. Theorem 37.2 uses Hold; Read and successive pairs of returning Ticks followed by Hold, stopping at the first singular $H_r=(m_{j+k})_{j,k\le r}$. Its source correspondence is native triangularity: $T^jb$ first reaches cell $j$ with coefficient $\beta_j=\prod_{h<j}b_h>0$, so $K$ is invertible, $H_r=K_r^{\mathsf T}K_r$ is positive definite for $r<N$, and $H_N$ is the first singular block. The paid observations through $m_{2N}$ therefore earn $N$ and the actual endpoint $T^{2N}b$. In §37.3 the monic orthogonal polynomials satisfy $p_j(T)b=\beta_j e_j$ and $h_j=\beta_j^2$; their diagonal pairings and positive ratios $\sqrt{h_{j+1}/h_j}$ recover the actual native coefficients with the positive orientation. For the [coefficient-driven Jacobi supplier](../../../D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.scribe.cs), the space is $\mathbb R^N$, the power basis is $(T^jb)_{j<N}$, coefficient multiplication is this $T$, and the actual Euclidean Hankel pairing is strictly positive and self-adjoint. Thus its private orthogonal, monic, support, tridiagonal and norm-ratio helpers concern exactly this already supplied construction, rather than an unearned observation port. Rational-square links are extracted by finite integer square-root search and exact squaring checks. From the earned primitive characteristic polynomial $Q_0$ of §44.2, whose constant term is nonzero, enumerate reduced positive candidate roots with numerator dividing $|Q_0(0)|$ and denominator dividing its leading coefficient. These divisibilities follow by clearing the root equation and reducing modulo its coprime numerator and denominator. Exact evaluation and polynomial division decide whether there are $N$ rational roots in $(0,1)$. Check $N\ge2$ and the pairwise-coprime reduced denominators. Failure is a local subclass answer and leaves the held source unchanged; it is not a source refusal or a failure certificate for every other recovery class. Success identifies $Q_0=Q$ of §104 and rational elimination earns the normalized rows $E$. Divisor trials, root tests, comparisons and solves are finite local work, with no factorization, spectral or response oracle.

Proof of the later entrance and attainability. If $y$ is the unknown current field after $W$, actually execute Hold; Read; $(N-1\text{ returning Ticks})$; Hold. The literal window is $B_0=\mathcal O y$; compute $y=\mathcal O^{-1}B_0$ and the actual held $w=T^{N-1}y$. If some reduced numerator of $h_iw$ is not divisible by $s_i$, choose the least such index and retain $v=w$, with $\delta=0$. Otherwise actually execute Add$(1)$; Read; Hold, set $v=w+b$ and $\delta=1$. In the latter case $h_iw=p_i/q_i$ has $s_i\mid p_i$ and $\gcd(q_i,s_i)=1$ for every $i$, while $(p_i+q_i)/q_i$ is still reduced and has numerator coprime to $s_i$. Hence every mode is now favorable. The root Read and the known actual Add successor concern this same specimen. Fix the least favorable index and least qualifying prime for the subsequent clock; these selectors are computed from earned data. The entrance uses $(\mathrm{Tick},\mathrm{Add},\mathrm{Read},\mathrm{Hold})=(N-1,\delta,1+\delta,2+\delta)$ and returns $N+\delta$ scalars. It restores neither $y$ nor an erased history of $W$. Every specified rational origin, including a bad one, is separately attainable from an earned known current $z$: solve $Kc=v-T^Nz$ and actually issue $N$ Tick; Add$(c_{N-1-j})$; Read pulses, then Hold. Expansion gives endpoint $T^Nz+Kc=v$. Those controls need not be in $D_a$ and their acquisition, calls and output are paid separately. This is a preparation using forward control, not a reverse Tick or a Reset. $\square$

## 107. A total numerical inverse using the earned length clock

**Theorem 107.1 (acceptance, refusal and uniqueness).** Fix an earned favorable origin, and its selected $(i,\ell,e,c)$ from §104. For every proposed rational historical field $z\in\mathbb Q^N$, there is a terminating exact local decision returning its unique $u\in D_a^{\ast}$ with $z=X_v(u)$ or returning NotInPulseImage. Compute $h_i z$. If it is zero, refuse without assigning it a valuation. Otherwise compute $L=(c-\nu_\ell(h_i z))/e$ and refuse unless $L$ is a nonnegative integer. If it is, enumerate exactly the finite $D_a^L$ in lexicographic order, compute each full-vector endpoint, and accept its match; if none matches, refuse. For $L=0$ the sole candidate is the empty word and its endpoint is $v$. A proposed dimension, list length or rational encoding incompatible with the fixed earned data is rejected locally before this test.

Proof. Every accepted candidate satisfies the explicit whole-vector endpoint equality; Theorem 104.2 gives uniqueness. For every actual endpoint its nonzero projection supplies precisely its actual length by the proved valuation identity, and its actual word occurs in the finite enumeration, so the decision is complete. Every refusal branch terminates, and even an arbitrarily large proposed nonnegative $L$ yields a finite enumeration. Sequentially compute each candidate from the retained $v$, storing one word and vector at a time; neither a saved producer word nor its counter is an input to this inverse. Prime valuations are computed by repeated exact division of the reduced numerator and denominator. The elementary nonzero multiplication, division and unequal-valuation sum facts are the supplied [pinned rational valuation facts](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean), with the zero digit handled separately. This implementation makes no efficiency claim and does not use an infinite search over possible lengths or an optional lattice table. Its result is numerical image membership. It does not authenticate a literal old measurement, a preparation, source calibration, a root binding or authority to call that root. $\square$

## 108. Historical boundary, present memory and agreement of all routes

**Definition 108.1 (the joint returned image).** Fix the earned native $T,b,v,D_a$, origin and framing conventions, real source access and common future-selector context. An actual finite received or owned $D_a$ word $u$ is executed as its literal pulses; its producer's input reception and completion control are actual paid resources. At $x_{\rm hist}=X_v(u)$ actually execute Read; $(N-1\text{ returning Ticks})$; Hold. Boundary is the resulting literal ordered list $B=(b^{\mathsf T}T^h x_{\rm hist})_{h<N}=\mathcal O x_{\rm hist}$. Space is the actual rooted weighted native path with its entire present field $x_{\rm now}=T^{N-1}x_{\rm hist}$. Time is the actual ordered target pulse-input list $u$ before this diagnostic, including its zeros, and excludes acquisition, $W$, preparation, diagnostic commands, waiting and arbitrary event journals. Memory is the earned law and the current prediction block $m=(b^{\mathsf T}T^h x_{\rm now})_{h<N}=\mathcal O x_{\rm now}$. These meanings are specified by cell values, executed inputs, literal observations and future predictions respectively; none is an unrestricted copy of history. The common context contains no old word or length counter. Any surviving producer, observer or caller archive is an additional store, with its isolation from the inverse's inputs explicit. Bound handles and rights accompany the actual service and are not numerical coordinates of these four views.

**Theorem 108.2 (every inverse and every route on this image).** Each of these four numerical expressions determines the other three, and all directed recovery maps, round trips and routes agree on Definition 108.1's image. Proposed rational Space, Boundary and Memory data have total numerical image tests at the fixed law. Proof. Boundary gives $x_{\rm hist}=\mathcal O^{-1}B$, then Theorem 107.1 gives the unique $u$ and its length; compute $x_{\rm now}=T^{N-1}x_{\rm hist}$ and $m=\mathcal O x_{\rm now}$. Space gives $x_{\rm hist}=T^{-(N-1)}x_{\rm now}$ since $0<T$ makes $T$ invertible, and takes the same route. Memory first gives $x_{\rm now}=\mathcal O^{-1}m$. Time computes $X_v(u)$, the window and both current expressions. Every composite therefore fixes the same unique word and its two determined fields. This proves all twelve directed inverses and the agreement of arbitrarily long routes, not just selected pairs. For image tests use respectively $T^{-(N-1)}$, $\mathcal O^{-1}$ and $T^{-(N-1)}\mathcal O^{-1}$ to reach a proposed historical field and apply Theorem 107.1; reject a mismatching Space geometry first. All these transports are invertible, so acceptance reconstructs precisely the proposed numerical value. Computation of a former Boundary from another view supplies equal numbers, not another literal observation or its provenance.

The common-future kernel on this image is exactly equality of $x_{\rm now}$, hence exactly equality of each view. Equal fields on this fixed law and access propagate to equal complete primitive outputs and successors by §109. Conversely, a nonzero field difference has nonzero $\mathcal O$ image; Read followed by at most $N-1$ returning Ticks distinguishes it. The [finite observability supplier](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs) apply over $\mathbb R^N$ with update $T$, readout $b^{\mathsf T}$ and horizon $N$: its stacked map is precisely this full-rank $\mathcal O=K^{\mathsf T}$, so the residual/rank/Gram conditions are met. It supplies no unpaid window or grant. For pulse concatenation the actual recurrence gives $X_v(ut)=T^{|t|}X_v(u)+\sum_{j<|t|}t_jT^{|t|-1-j}b$ by induction, and its unique inverse returns $ut$. Applying the prescribed diagnostic next gives exactly its new historical window and advanced current field. Native and predictor dynamics commute at every current settled cut by §109; inverse transport at a later cut is asserted only when that cut again satisfies Definition 108.1. The final diagnostic contains no Add$(0)$ and is not a literal zero-pulse suffix, although its field numerically equals $X_v(u0^{N-1})$. Future policies here have the same accessible current data, future replies and any common random tape; policies consulting unequal old archives enlarge the task and are outside this kernel claim. $\square$

## 109. Complete retained use beyond the inverse image

**Theorem 109.1 (all-field predictive and callable correspondence).** Retain the actual binding and rights and let $\mu_h=b^{\mathsf T}T^hb$, $0\le h<N$, be earned impulse data. At every rational current field maintain $m_h=b^{\mathsf T}T^hx$. Read returns $m_0$ without changing $m$; Hold returns its fixed acknowledgement and preserves $m$. Authorized Add$(t)$ sets $m'_h=m_h+t\mu_h$ and returns exactly its fixed Add acknowledgement, together with $m'_0$ only in the explicitly installed post-Add-scalar variant. Tick sets $m'_h=m_{h+1}$ for $h<N-1$ and $m'_{N-1}=-\sum_{h<N}(q_h/a)m_h$, where $Q(z)=az^N+\sum_{h<N}q_hz^h$, and returns $m'_0$. These are the original §36 operations. Proof. The Read, Hold and Add identities follow from the actual successors $x,x,x+tb$. The actual successor $Tx$ gives the Tick shift, and $b^{\mathsf T}Q(T)x=0$ gives its last coordinate. Each row therefore preserves $m=\mathcal O x$ and its full declared reply. Forward the actual request through the retained source handle, consume its complete real reply and return, and commit this matching predictor before the next settled cut. Induction proves every finite sufficiently backed common adaptive continuation, including rational controls outside $D_a$ and fields outside the pulse image. Starting from retained $v$ and recovered $u$, the same four rows also reconstruct every numerical target-pulse reply and successor in its actual order: its intermediate Tick scalar, complete Add reply and final Read scalar. This computes equal numbers and does not create another literal observation or old archive. No predicted reply is substituted for execution of a source call. This is the all-field service supplier of §§91–92 with a different earned clock; the whole-law predictor, not the old determinant certificate, is what its proof uses.

For an explicit finite framing of this same four-command service, fix source-independent kind and End words, canonical signed reduced rational payloads, output End, a distinct transport LocalACK and Return. At a settled Ready cut the pending input is empty. An input byte is accepted only with backing for its stored successor; otherwise that input step is disabled and leaves the state unchanged. A receiving parser retains every proper incomplete request prefix without a completed semantic response or source operation. The request End closes a frame. If its kind, arity or canonical payload is invalid, consume that complete frame, emit local FrameReject; output End; LocalACK; Return, clear the pending frame and restore Ready; this is a framing answer, not an invented plant refusal. A valid closed frame is stored as a parsed pending call. If its current operation right or required backing is absent, retain that call without dispatch, output or source step; its waiting state is the same in both representations. Otherwise dispatch it through the genuine reference and enter Busy. While waiting or Busy, further input is disabled and leaves the stored control state unchanged. During the dispatched call consume every actual semantic scalar or acknowledgement and the declared output End, LocalACK and Return; then commit the predictor, clear the completed call and restore Ready. Rights or backing can change only through the common installation's actual external transitions, which are mirrored identically and are not numerical grants. The two representations use this same parser, pending bytes or call, real reference, rights and phase. Thus every received-prefix step, local rejection, disabled branch, external control step and busy completion has the same control successor; the only field steps are precisely the four proved rows. This proves correspondence for the complete relevant framed interaction as well as completed legal calls. If a fixed installation already exposes its own malformed-frame reply, that actual reply and its actual unchanged-field successor are forwarded instead of adding FrameReject. No new source request, coefficient port, ordinal selector, failure oracle or grant is installed by the numerical inverse. The inverse comparisons remain at completed cuts with this common control state; they do not identify different pending parsers, authority stores, timing/capacity channels or archive-visible tasks. $\square$

## 110. The same realized run pays its calls, work, widths and traffic

**Proposition 110.1 (one attained implementation account).** Use the §37 acquisition, an actual $W$, §106's particular entrance with its actual $\delta$, $L$ literal target pulses, the §108 diagnostic and §107's sequential enumerator on one path. Apart from the actual installation/preparation and $W$, the source-call vector is $(\mathrm{Tick},\mathrm{Add},\mathrm{Read},\mathrm{Hold})=(4N+L-2,L+\delta,L+3+\delta,N+4+\delta)$; mandatory scalars number $4N+2L+1+\delta$ and semantic acknowledgements number $N+L+4+2\delta$. The optional post-Add-scalar variant adds $L+\delta$ scalars. Proof. Acquisition contributes $(2N,0,1,N+1)$, entrance $(N-1,\delta,1+\delta,2+\delta)$, pulses $(L,L,L,0)$, and diagnostic $(N-1,0,1,1)$. Adding the rows proves the identities. Add $W$'s actual four counts, scalars, inputs and acknowledgements, and the actual provider construction, initialization, binding/grants, local work, copies and traffic to obtain the full-run account; authentic $b$ is a supplied preparation with those real costs, not a free unknown seed. A separate attained bad-origin witness uses acquisition, the $N$ rational preparation pulses and Hold of §106, then $j\le R+1$ CRT pulses and Hold. That different run has $(3N+j,N+j,N+j+1,N+3)$ calls, $4N+2j+1$ mandatory scalars and $2N+j+3$ semantic acknowledgements. Its shorter collision prefix is actually visited. Precompute modular inverses and CRT coefficients from earned denominators, choose each digit from the current $k$, and compare each positive-index vector with the earlier retained positive-index vectors; $O(Nj)$ integer/digit slots and $O(Nj^2)$ comparisons suffice, in addition to law/preparation work and the actual-width CRT arithmetic. No favorable coordinate of this separate witness is combined with the good-origin run.

Let $W_{\rm run}\ge1$ bound the actual bit widths of the integer numerators, denominators, products, Euclid coefficients, polynomial/matrix intermediates, counters and records used by this chosen finite implementation; it is a posterior width, not a supplied precision bound. The repeated Hankel eliminations, native reconstruction and matrix preprocessing use $O(N^4)$ rational operations. Binary search extracts each promised integer square root with $O(W_{\rm run})$ integer multiplications/comparisons, hence $O(NW_{\rm run})$ such operations for the links, with exact squaring checks. Root-class testing can use trial loops through $|Q_0(0)|$ and its leading coefficient $a$, at most $|Q_0(0)|a$ positive numerator/denominator candidate pairs, and $O(N)$ rational evaluation/division work per pair; eigenrow solves separately use $O(N^4)$ rational operations. Computing $Ev$ and choosing the least favorable index use $O(N^2)$ rational operations and $N$ divisibility tests; choosing its least qualifying prime uses at most $s_i\le a$ trial divisors, and each valuation uses $O(W_{\rm run})$ divisions. After preprocessing, sequential word recognition uses $O(N(L+1)a^L)$ rational operations on the path, with one candidate and an $L$-digit odometer; early refusals pay only their actual prefix. School integer and reduced-rational operations have a conservative $O(W_{\rm run}^3)$ bit bound each; all input/output, source, selection, copying and control work remains additional. A source tridiagonal Tick uses $3N-2$ rational products and $2N-2$ additions with separate old/new buffers; the separate prediction block's Tick and Add each have $O(N)$ actual-width arithmetic and copies. Precision is indispensable: $h_iX_v(u)$ has valuation $c-Le$, so when $Le-c>0$ its reduced denominator contains $\ell^{Le-c}$. At the returned source cut the corresponding valuation is $c-(L+N-1)e$. More explicitly, with $\alpha_i=\min_{h_{ij}\ne0}\nu_\ell(h_{ij})$, the nonzero-sum inequality gives $\min_{x_j\ne0}\nu_\ell(x_j)\le\nu_\ell(h_ix)-\alpha_i$; since $h_i$ is fixed, native source widths also cannot stay uniformly bounded as these lengths grow. The finite-dimensional state, total algorithm and finite controller therefore establish neither efficient decoding nor fixed lifetime memory.

A sufficient core layout has $O(N^2+L+1)$ rational/integer/digit slots at their actual widths: actual source field and Tick buffer; native path coefficients; separate current prediction vector and its update buffer; earned $Q,K,\mathcal O,E$ and needed inverses, moments and clock data; retained $v$, literal entrance and diagnostic windows, distinct historical/current/candidate vectors while live; reconstruction and elimination scratch, candidate/output words and counters. Shared matrix backing is counted once only when it is actually shared; separate buffers and copies coexist and count separately. Add the real finite program/control, source/reference/rights and provider support, pending requests, completions, I/O backing, and every surviving acquisition, $W$, producer, observer and caller archive. Isolation from decoder inputs does not remove a store's material cost; clearing pays its actual writes and does not retroactively remove earlier allocations. For literal traffic, one compatible self-delimiting natural code writes $k$ one bits, one zero and the $k$-bit binary expansion of $n$, where $k=\operatorname{bitlen}(n)$ and $\operatorname{bitlen}(0)=1$; its length is $2\operatorname{bitlen}(n)+1$; a sign bit and the codes for reduced $|p|$ and $q>0$ give $\rho(p/q)=2\operatorname{bitlen}(|p|)+2\operatorname{bitlen}(q)+3$. With this chosen codec the semantic rational payload is exactly $\sum_{\text{actual Tick/Read replies }y}\rho(y)+\sum_{\text{actual Add inputs }t}\rho(t)$, plus the explicitly selected optional Add outputs. Add every actual operation tag, semantic ACK, local rejection, End, LocalACK, Return, producer digit/termination input, law/origin handoff and decoded-word/length output at its literal encoded size. Equivalently the complete traffic is $\sum_{\pi\in\Pi}|\pi|$ for the multiset of all packets actually transmitted on this run, including inner/outward copies with their multiplicities; no zero, unused Tick reply or retained archive export is omitted. Installed reference/grant widths, allocation and input selection have their actual costs as well. These are sufficient finite layouts and exact call/payload accounts for the stated algorithms, with the remaining provider and continuation costs attached to the same run; they assert no resource optimum or cross-installation dominance. $\square$

## 111. Supplier subtraction and boundaries supported by counterpairs

**Proposition 111.1 (the exact recovered content and its exclusions).** The new joint assertion is the $N\ge2$ all-origin iff under one $D_a$ input, its actual shared-digit collision converse, and its separation from every certificate (87.3). Sections 36–37 already earn the actual path, §§44–45 supply whole-law fixed-length divisibility and separation, §§84–86 supply the scalar all-origin iff, and §§87–95 supply the other certificate class and the paid entrance, recognition, historical/current-view and predictive-service patterns consumed above. Their scalar, lattice and transport results are not additional new outcomes here. The current address-calibrated native root acquisition of §§96–103 is also a positive supplier under its genuine-zero/pure-growth entrance, persistent address-dependent diagonals and links, original-root binding and returning Tick; it is not an unresolved generic root-acquisition claim, and it neither supplies nor is supplied by the fixed-path spectral criterion. The known-alpha growing-history results of [Atomic Generation Acquisition II, §§84–92](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md#84-growing-native-fields-with-two-declared-clock-phases) likewise retain their positive/invertible field laws, earned seed, maintained addresses and distinct pre/post-clock services. The [clocked Native recovery](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md#1-the-concrete-component-and-its-suppliers) already acquires a tree and serves its fixed controller with real receipt clocks; [paid conversion](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md#1-domain-suppliers-and-the-additional-interface) keeps its acquired fixed-$H$ entrance, unused lanes and owner-authorized Ready installation. [PR57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#57-a-complete-paid-ideal-realization-of-the-original-ordered-tree-interface) realizes its Clifford-$E$, whole-candidate-guarded source with constructed tapes; [Process Geometry §37](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md#37-有序-fib-源运输的中心化刚性与入口恢复) inverts an already acquired exponent/current-tree pair on the certified substitution image; [Structural Atlas 13.7](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md#13-restricted-set-to-value-refinement-by-three-slot-relocations) preserves genuine-source, supplied-code and atomic-patch conditions separately from fine clocks, access and prices. These positive suppliers already establish their declared acquisition, replay, conversion and use results. The additional relation here is the shared-digit spectral origin criterion, rather than another generic view or callable wrapper. No original unit-native, path or quantum law, preparation, right or cost vector is identified with another by numerical similarity.

Proof of the stated boundaries and attribution. Before the retained origin, insert legal Add$(t)$; Add$(-t)$ into a history on the same path. The subsequent field and all common future replies are unchanged, while its old journal differs; excluded old archives cannot be recovered from the four numerical values. At any known present field, the separately paid $N$-control construction of §106 reaches zero. That field has $h_i x=0$ and is outside the favorable pulse/diagnostic image, while §109 continues to predict every legal call there. Thus full current service does not extend the word inverse's domain. Authentic preparation is also a substantive condition: on the already supplied $p=2,q=3$ two-cell path, entrance field $(1,1)^{\mathsf T}$ is an eigenvector of eigenvalue $1/2$, so its passive root Hankel block first becomes singular at order one despite the actual order two. The §37 stopping argument cannot simply be used for arbitrary unknown-law entrance fields. Copying numerical records to an actor without a genuine root binding or Add grant leaves those missing rights missing; image membership proves no authority or physical provenance. A direct identification with original zero-diagonal unit adjacency also fails its first prepared-root test: this path has $b^{\mathsf T}Tb=a_0>0$, while a unit tree at its root has zero first return. This refutes that direct identification, not every conceivable adapter. A broader transfer would need its own common preparation, lawful operations, complete outputs/refusals and successors, retained selectors/records, references/rights and simultaneous resources. For classical attribution, primitive Gauss divisibility is exactly [Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Polynomial/GaussLemma.lean) for primitive integral $Q$ over $\mathbb Q$; the bounded simultaneous digit uses [Nat.chineseRemainderOfList and its product-bound/uniqueness results](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/ChineseRemainder.lean) with the proved positive pairwise-coprime moduli. [Akiyama, Thuswaldner and Zaïmi, Comments on the height reducing property II, equations (4)–(6), Propositions 6–7 and Corollary 8(ii)](https://arxiv.org/html/1403.7480v1) supply expanding-base division dynamics and eventual periodicity for a complete residue system in one algebraic ring. Their scalar system is already a supplier in §94; separately choosing its scalar residues does not install the common $D_a$ input here, whose simultaneous box and actual correspondence were proved in §104. Their Theorem 3's bounded zero-representation automaton at one algebraic number does not replace whole-law vector equality, as §105's projection pair demonstrates. The attribution is repository-derived synthesis and source-specific application of these mature tools, not worldwide novelty from search absence. Arbitrary erased history, arbitrary unknown-law startup, universal native/path/quantum transfer, noisy or finite-precision certification, universal generator minimality and total resource optimality remain outside these quantified conclusions. The original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer and unchanged-initialization obligations keep their original statements. $\square$

## 追加锚（本行以下为增补区）

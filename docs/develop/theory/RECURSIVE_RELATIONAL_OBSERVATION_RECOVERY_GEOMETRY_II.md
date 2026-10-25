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

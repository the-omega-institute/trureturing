# Recursive relational observation: unknown-field native startup and an earned unit origin

The model in this volume has an unknown initial field and a supplied order cap. Its endpoint operations are those of [Recovery Geometry II][P], §36, but its initialization is different. A paid startup separates the unknown free response from an injected response, identifies the native law and the actual advanced field, and retains their common callable predictor. Actual controls subsequently establish a new unit origin. Only a further actual passive prefix is interpreted by P's four-view recovery theorem. The old unit-prepared, no-order-advice result retains its original hypotheses.

Repository suppliers throughout are read at the fixed public revision `39687802cb999fa97ebdbf17f226a541563cc351`. Mathematical results, input promises, numerical predictions and actual source observations have distinct roles below. Physical conformance to the declared digital service is `ASSUMED-UNVERIFIED`.

## 1. One specimen, an unknown field and a supplied order cap

**Definition 1.1 (the capped source class).** The supplied input is an integer $R\ge1$. The unknown specimen has an integer $1\le N\le R$, rooted cells $0,\ldots,N-1$, a fixed matrix

$$
T=\begin{pmatrix}
a_0&b_0&&0\\
b_0&a_1&\ddots&\\
&\ddots&\ddots&b_{N-2}\\
0&&b_{N-2}&a_{N-1}
\end{pmatrix}\in\mathbb Q^{N\times N},
\qquad b_i>0,\qquad 0<T<I,
\tag{UFS.1}
$$

and an arbitrary initial field $x^{\rm in}\in\mathbb Q^N$. Both strict matrix inequalities mean positive definiteness. There is no common norm, energy, sign or bit-length bound on $x^{\rm in}$. It may be zero or fail to excite any chosen collection of eigenmodes. Cell names mean distance from the bound root, rather than supplied identifiers or physical positions.

**Assumption 1.2 (installed resources and complete service).** The following operations act serially on this same field and matrix.

| Command | Actual successor | Complete declared output |
| --- | --- | --- |
| Read | $x$ | $e_0^{\mathsf T}x\in\mathbb Q$ |
| Tick | $Tx$ | $e_0^{\mathsf T}Tx\in\mathbb Q$, after the update |
| Hold | $x$ throughout the held processing interval | a fixed acknowledgement |
| Add$(u)$ | $x+u e_0$ for the supplied $u\in\mathbb Q$ | a fixed acknowledgement |

Every rational Add input, including a negative input, is authorized. Holds end before the next commanded state-changing operation. No autonomous Tick occurs between serial calls. Each completed Tick return is received and retained by the specified construction; it is never a silent state transition. Acknowledgements carry no metadata. Exact signed rational serialization, class and fixedness assurance, the binding to the actual root, exclusive serial access, call and input rights, Hold control, and storage and control backing are supplied premises. The cap $R$ and its assurance are supplied resources too. The exact $N$, coefficients and initial field are not advice.

There is no Reset, clone, coefficient or size port, chosen-index response port, free control, or distinguishing size/work/timing side channel. The controller's only specimen-dependent inputs are these actual declared outputs. A common endpoint reference binds the specimen without revealing its law. The same specimen persists during source acquisition, local computation, controlled preparation and later calls. Physical installation, class assurance and the realization of the rights/backing are not certified by the algebra.

**Definition 1.3 (free, impulse and controlled responses).** Define the mathematical sequences

$$
f_j=e_0^{\mathsf T}T^j x^{\rm in},\qquad
m_j=e_0^{\mathsf T}T^j e_0\quad(j\ge0).
\tag{UFS.2}
$$

The $f_j$ are unknown free responses; the $m_j$ are root impulse moments with $m_0=1$. They are not initially accessible arrays. At any completed cut with $t$ actual Ticks and pulses $u_l$ applied at tick epochs $s_l\le t$, induction on the actual commands gives

$$
x=T^t x^{\rm in}+\sum_lu_lT^{t-s_l}e_0,
\qquad
e_0^{\mathsf T}x=f_t+\sum_lu_lm_{t-s_l}.
\tag{UFS.3}
$$

Only pulses already executed at that cut occur in the sum. Read and Hold preserve the formula; Add appends its exponent-zero term, and Tick multiplies the entire state by $T$. This is [Process Geometry][PG], Definition 12.5's free/forced distinction with $A=T$, $H=e_0^{\mathsf T}$, $B=e_0$. Its one-step forced convention becomes the displayed age convention because Add and Tick are separate operations here.

A uniform finite controller means one finite effective program taking $R$ as input, with finite but growing work storage on each run. It does not mean a fixed finite-state machine or a common bound on literal rational widths.

## 2. Earning the free response without assuming a cyclic initial field

**Lemma 2.1 (visible modes and a signed Hankel block).** For a source of Definition 1.1 there are $r\le N$ distinct numbers $\lambda_1,\ldots,\lambda_r\in(0,1)$ and nonzero real coefficients $c_1,\ldots,c_r$ such that

$$
f_j=\sum_{l=1}^r c_l\lambda_l^j\quad(j\ge0).
\tag{UFS.4}
$$

The empty sum is allowed. For $M\ge r$ the $M$-row Hankel matrix $G_M=(f_{i+j})_{0\le i,j<M}$ has rank exactly $r$. If $r>0$, its leading $r$-row block $G_r$ is nonsingular. These assertions allow signed $c_l$; no positive-moment stopping test is asserted for the free response.

Proof. P Lemma 37.1 supplies native triangularity: $T^j e_0$ has last nonzero coordinate $\prod_{i<j}b_i>0$ at cell $j$, for $j<N$. Thus $e_0$ is cyclic. A real symmetric matrix has an orthonormal eigenbasis. If an eigenspace had dimension at least two, it would contain a nonzero vector perpendicular to $e_0$; that vector would be perpendicular to every $T^j e_0$, contradicting cyclicity. Its eigenvalues are therefore simple. For each normalized eigenvector $v_l$, the coefficient in the free response is $(e_0^{\mathsf T}v_l)(v_l^{\mathsf T}x^{\rm in})$. Retain only its nonzero coefficients. The first factor never vanishes, whereas the second may vanish or have either sign. The spectral restrictions follow from $0<T<I$.

For these retained nodes put $V_M(i,l)=\lambda_l^i$ and $D_c=\operatorname{diag}(c_l)$. The existing finite atomic Hankel factorization gives $G_M=V_MD_cV_M^{\mathsf T}$. The first $r$ rows of $V_M$ are a nonsingular Vandermonde matrix, so $V_M$ has a left inverse $L$. Consequently $L G_M L^{\mathsf T}=D_c$, proving rank at least $r$; the factorization gives rank at most $r$. At $M=r$ both Vandermonde factors and $D_c$ are invertible. For $r=0$ the matrix is zero. This proves all cases. $\square$

The factorization is supplied by `FiniteAtomicHankelVandermonde.hankel_moment_matrix_factorization`, allowing complex weights and hence these real signed weights. Distinctness/nonzero weights are the additional hypotheses just verified. The Vandermonde determinant criterion is mature algebra, including pinned upstream `Matrix.det_vandermonde_ne_zero_iff`; the exact source correspondence is given in §9.

**Proposition 2.2 (a capped free-response certificate).** From the actual initial passive values

$$
f_0,\ldots,f_{2R-1}
\tag{UFS.5}
$$

one can effectively compute a rational recurrence generating the entire actual free response. No spectral factorization, initial-field bound, or assumption that $r=N$ is required.

Proof. Compute $r=\operatorname{rank}G_R$ by rational elimination, using only indices through $2R-2$. Lemma 2.1 and $N\le R$ identify this rank as the number of visible modes. If $r=0$, the free response is identically zero. In fact $x^{\rm in}=0$, since cyclicity and $f_j=0$ make it perpendicular to a basis, although the controller does not need this conclusion before acquiring $T$.

If $r>0$, solve over $\mathbb Q$

$$
G_r(\gamma_0,\ldots,\gamma_{r-1})^{\mathsf T}
=-(f_r,\ldots,f_{2r-1})^{\mathsf T}.
\tag{UFS.6}
$$

The needed last index is at most $2R-1$. The invertibility in Lemma 2.1 gives unique rational coefficients. For $p(z)=z^r+\sum_{l<r}\gamma_lz^l$, the equations are

$$
\sum_{l=1}^r c_l\lambda_l^i p(\lambda_l)=0\quad(0\le i<r).
$$

The square Vandermonde matrix and $D_c$ are invertible, so $p(\lambda_l)=0$ for every visible node. Multiplication by $c_l\lambda_l^j$ and summation therefore give

$$
f_{j+r}=-\sum_{l<r}\gamma_l f_{j+l}\quad(j\ge0).
\tag{UFS.7}
$$

Its first $r$ values and the coefficients generate the entire actual sequence by induction. This also shows that the recurrence has least possible degree when $r>0$: a lower-degree recurrence would give a polynomial vanishing at all $r$ distinct nodes by the same Vandermonde argument. All calculations use exact rational data. The cap is load-bearing in interpreting the full $R$-row rank as the complete visible rank; singularity of an earlier signed block is not that certificate. $\square$

In particular this procedure must not stop at the first singular leading free-response block. For example a signed exponential sum can have $f_0=0$ and $f_1\ne0$. P's first-flat-block test applies later to extracted impulse moments, whose weights are positive.

## 3. A single paid pulse and the actual advanced native field

**Theorem 3.1 (D1: uniform unknown-field startup).** For every supplied $R\ge1$, every $1\le N\le R$, every matrix (UFS.1) and every $x^{\rm in}\in\mathbb Q^N$, one uniform controller terminates with the exact native $N,T$, the complete impulse law, and the actual native field at its stopping cut. It installs a predictor for the entire Read/Tick/Hold/Add menu of Assumption 1.2. One attained startup uses exactly

$$
2R-1+2N\ \text{Ticks},\qquad
2R+2N+1\ \text{scalar returns},\qquad
1\ \text{Add}.
\tag{UFS.8}
$$

Proof. Begin with Hold and Read $f_0$. Execute $2R-1$ Ticks, receiving and recording every returned scalar through $f_{2R-1}$. Write $s=2R-1$. Hold and compute the certificate of Proposition 2.2. At this actual cut the source field is $z=T^s x^{\rm in}$; local computation has not changed it.

Execute Add$(1)$, receive its acknowledgement, and Read the actual root $v_0$. Starting from this cut, execute Ticks in pairs. Let $v_j$ be the return after $j$ such Ticks. Hold after each pair for the finite tests below. Formula (UFS.3) gives, on this same run,

$$
w=z+e_0,\qquad
v_j=e_0^{\mathsf T}T^jw=f_{s+j}+m_j.
\tag{UFS.9}
$$

Generate $f_{s+j}$ using the earned free recurrence and form $d_j=v_j-f_{s+j}$. Thus $d_j=m_j$ exactly, including $d_0=1$. These are arithmetic differences of paid observations and earned predictions, rather than a new observation port.

Apply P Theorem 37.2's even-block test to $(d_j)$. The actual path triangularity and positive impulse Gram identity used there hold for the present $T$ independently of $x^{\rm in}$. The first singular block $(d_{i+j})_{0\le i,j\le n}$ occurs at $n=N$. Thus exactly $2N$ Ticks after the pulse supply $d_0,\ldots,d_{2N}$ and earn the stopping size. P Propositions 37.3–37.4 recover the exact rooted coefficients, positive link orientations, least impulse recurrence $q$ and transfer $F_T$. Their hypotheses concern these actual impulse moments; they do not require the post-pulse field $w$ to be cyclic.

For completeness, the native correspondence in that supplier is monic moment orthogonalization $p_j(T)e_0=\beta_j e_j$ with $\beta_j=\prod_{i<j}b_i>0$. Its formulas are

$$
a_j=\frac{\langle Xp_j,p_j\rangle_m}{h_j},\qquad
b_j=\sqrt{h_{j+1}/h_j}>0,\qquad h_j=\langle p_j,p_j\rangle_m.
\tag{UFS.10}
$$

The finite rational positive square roots exist because these are the promised rational links. Integer square-root extraction on numerator and denominator computes them. This reuses native Jacobi reconstruction, rather than selecting an arbitrary similar realization.

The acquired native field is not guessed to be $T^{2N}e_0$. Form the observability matrix

$$
\mathcal O_N=\begin{pmatrix}
e_0^{\mathsf T}\\ e_0^{\mathsf T}T\\ \vdots\\ e_0^{\mathsf T}T^{N-1}
\end{pmatrix}.
\tag{UFS.11}
$$

It is the transpose of P's invertible native Krylov matrix. Solve the exact rational system

$$
\mathcal O_N\widehat w=(v_0,\ldots,v_{N-1})^{\mathsf T},
\qquad
\widehat x_*=T^{2N}\widehat w.
\tag{UFS.12}
$$

All these $v_j$ are already present. Equations (UFS.9) and invertibility give $\widehat w=w$. Hence, at the actual stopping cut,

$$
\widehat x_*=x_*=T^{s+2N}x^{\rm in}+T^{2N}e_0.
\tag{UFS.13}
$$

Keep the source held during the solve and record installation, within the final pair's Hold. Section 4 gives the complete future invariant. The operation count is $2R-1$ initial Ticks, one pulse and post-pulse Read, and $2N$ further Ticks. Initial Read plus the first $2R-1$ Tick returns give $2R$ scalars; the post-pulse Read and later Tick returns add $2N+1$. Every loop and exact solve is finite on the promised class. $\square$

Even if $w=0$, the differences in (UFS.9) still give the full impulse law: the earned free response is then $f_{s+j}=-m_j$. No assumption that a fixed Add amplitude makes the physical field cyclic is used. Likewise $r$ may be strictly smaller than $N$ or zero. The controller never equates visible free order with native path order.

The extracted $(m_j)$ is not yet P's actual Time expression from an authentic unit preparation. In this startup the physical trajectory is (UFS.9); only its subtracted response is an impulse sequence. The distinction is removed by actual preparation in §5, with its extra costs.

## 4. Retained complete adaptive use at the earned cut

**Definition 4.1 (the synchronized observer record).** At the held cut of Theorem 3.1 retain $N,T,q$, $\mu=(m_0,\ldots,m_{N-1})$, a native record $\widehat x=x_*$, and $a=\mathcal O_N\widehat x$. Also retain the actual bound source reference, required rights and backing. They remain distinct from numerical encodings. Calls are serialized; the local update is committed before exposing the next completed cut.

| Actual command | Native-record update | Predictive-record update | Predicted complete output |
| --- | --- | --- | --- |
| Read | unchanged | unchanged | $a_0$ |
| Tick | $\widehat x\gets T\widehat x$ | $a'_j=a_{j+1}$ for $j<N-1$, $a'_{N-1}=-\sum_{j<N}q_ja_j$ | $a'_0$ after the update |
| Add$(u)$ | $\widehat x\gets\widehat x+u e_0$ | $a'_j=a_j+u\mu_j$ | fixed acknowledgement |
| Hold | unchanged | unchanged | fixed acknowledgement |

Here $q(z)=z^N+\sum_{j<N}q_jz^j$. At $N=1$ the Tick row consists only of its recurrence formula. A forecast on scratch records sends no actual command and obtains no actual observation. All source and observer work and scalar serialization remain charged.

**Theorem 4.2 (complete callable predictor).** For every finite adaptive continuation in this menu, using arbitrary authorized rational inputs and the actual earlier outputs, the installed record predicts every declared output and the complete native successor exactly. At every completed cut

$$
\widehat x=x_{\rm actual},\qquad a=\mathcal O_Nx_{\rm actual}.
\tag{UFS.14}
$$

Proof. Initialization is (UFS.12)–(UFS.13). The recovered native law satisfies $q(T)=0$ by P Proposition 37.4. Therefore $\mathcal O_NTx$ is precisely the predictive shift/recurrence in Definition 4.1 for every $x$, including noncyclic and controlled fields. Moreover $(\mathcal O_Ne_0)_j=m_j$, giving the Add update. Read and Hold preserve both identities; Tick returns the updated, rather than the old, root. These are exactly P Theorem 40.2's one-operation identities, now initialized by the earned field (UFS.13).

Induct over the actual finite command history. Equal previous outputs make a common adaptive policy choose the same next command, input and stopping decision on the source and predictor. The displayed identities preserve synchronization and the complete output, including acknowledgements. This proves every finite continuation, not merely one passive forecast or one predetermined pulse schedule. Retained numerical predictions do not create another specimen, a new input right, or erased command history. $\square$

## 5. A unit origin earned by actual controls

**Theorem 5.1 (D2: actual unit preparation).** From the stopping cut in Theorem 3.1 the allowed controls prepare the actual field $e_0$ using exactly $N$ additional Ticks and $N$ additional Adds. Every one of their Tick returns is retained and predicted. This establishes a new named origin on the same specimen, without Reset or access to the initial field as advice.

Proof. The known controllability matrix

$$
C_N=[T^{N-1}e_0,T^{N-2}e_0,\ldots,e_0]
\tag{UFS.15}
$$

is P's invertible Krylov matrix with reversed columns. Compute the unique rational vector $u=(u_0,\ldots,u_{N-1})^{\mathsf T}$ satisfying

$$
C_Nu=e_0-T^Nx_*.
\tag{UFS.16}
$$

For each $j=0,\ldots,N-1$, execute Tick, receive its actual scalar return, and then execute Add$(u_j)$ and receive its acknowledgement. Use the synchronized predictor throughout. After $j$ pairs, induction on these actual updates gives

$$
x_j=T^jx_*+\sum_{l=0}^{j-1}u_lT^{j-1-l}e_0.
\tag{UFS.17}
$$

At $j=N$, (UFS.16) makes this field exactly $e_0$. Inputs may be signed and large; their exact representations, transmission and root-addition work are included. If a computed $u_j$ is zero, the specified sequence still executes its Add$(0)$, so the attained count is exactly $N$. No clone, silent Tick or state replacement has occurred. The terminal held cut after the final Add is the named origin $o$, justified by this actual state identity. $\square$

Native controllability is mature finite linear control. The additional content here is its paid execution from the actual acquired cut with the full Tick-return menu. It is not a claim that observing the root automatically installs a control right.

**Proposition 5.2 (the origin is new, rather than an old chronology inverse).** The preparation proves that the state at $o$ is $e_0$ and authenticates subsequent passive Tick count relative to $o$. It does not recover unrecorded pre-entry chronology, prior Holds or controlled journals.

Proof. For any fixed promised $T$ and rational entry field $x^{\rm in}$, the histories starting directly at $x^{\rm in}$ and starting one Tick earlier at $T^{-1}x^{\rm in}$ have the same field at entry. The inverse exists and is rational since $T>0$. Both initial fields belong to the present unrestricted class. Subsequent common commands therefore have identical successors and outputs. Their earlier elapsed Tick counts differ. Extra unrecorded Holds likewise have no declared output distinction at entry. This uses no illicit reset in either run: it compares two admitted histories leading to the same entry configuration.

Even complete recovery of the mathematical entry vector, which could now be computed as $T^{-s}(\widehat w-e_0)$, does not distinguish these pre-entry histories. The newly retained marker $o$ records an event actually performed by this controller. It asserts no earlier unit preparation and reconstructs no lost control journal. P Counterexamples 42.1 and 42.4 retain these same current-state/chronology boundaries. $\square$

## 6. A further real passive prefix and four independently meaningful views

**Definition 6.1 (the new passive segment).** While the final preparation Hold remains in force at $o$, Read the actual root $1$. Execute $k\ge2N$ further Ticks, with no Add in this segment, receiving the actual roots $m_1,\ldots,m_k$. Relative to the actual origin $o$, the current field is $x=T^ke_0$. The following independently specified data are exactly P Definition 39.1's data at this new origin.

| View | Exposed data and meaning |
| --- | --- |
| Space | actual rooted weighted path $T$ and current cell field $x$ |
| Time | paid ordered root list $(m_0,\ldots,m_k)$ in this real passive segment |
| Boundary | rational endpoint transfer $F_T(z)=e_0^{\mathsf T}(zI-T)^{-1}e_0$ and present root $m_k$ |
| Memory | least impulse recurrence $q$, its initial $N$ moments $\mu$, and present predictive vector $a=(e_0^{\mathsf T}T^jx)_{j<N}$ |

No view is defined as an unrestricted copy of a full command journal. Space carries native adjacency and a current field; Boundary carries a port law and one current value; Memory is a finite sufficient predictive state; Time carries a specified paid scalar segment. Numerical view data do not by themselves include the source reference or its call rights. The installation and actual origin are common contextual premises for all four views.

**Theorem 6.2 (earned entry into the original P39 domain).** For every source in Theorem 3.1, actual preparation by Theorem 5.1 followed by $k\ge2N$ passive Ticks puts the same specimen in P39's domain, with all four recovery directions, route agreement and passive Tick compatibility at that domain's original threshold. At the attained choice $k=2N$, total operations from the original unknown-field entry are

$$
2R-1+5N\ \text{Ticks},\qquad
N+1\ \text{Adds},\qquad
2R+5N+2\ \text{scalar returns}.
\tag{UFS.18}
$$

Proof. The actual preparation identity gives precisely P's authentic unit initial field at $o$. Fixedness and exclusive serial access preserve the same $T$; no Add occurs in the segment. Thus all hypotheses of P Definition 39.1 are instantiated, including actual paid Time data through index $k\ge2N$.

The recovery maps are the supplied ones, with this parameter correspondence. Time's first flat block recovers $N,T$. Boundary's rational function generates impulse moments locally and hence recovers $T$. Memory's least degree gives $N$, and $(q,\mu)$ generates the same moments. Space already contains $T$. Since $0<T<I$, its root impulse sequence satisfies $1=m_0>m_1>\cdots>0$; the present root identifies the unique $k$ by finite enumeration on the actual image. Each route therefore recovers the same $(T,k,T^ke_0)$, giving all view conversions and agreement. The Time list reconstructed arithmetically equals the already paid list; this does not pay or authenticate an unexecuted segment. Memory inversion uses the same $\mathcal O_N$ as (UFS.11). P Propositions 39.3–39.4 supply exactly these inverses and their transported passive Tick.

The subsequent complete adaptive predictor is still Theorem 4.2's synchronized record, which has tracked all preparation commands and passive Ticks. If a later Add is made, that predictor remains valid, while the P39 passive phase assertion requires its own domain and cannot be extended to arbitrary controlled journals.

For the attained count add $N$ preparation Ticks to the $2R-1+2N$ startup Ticks, and $2N$ real passive Ticks. Add counts are $1+N$. Startup scalars number $2R+2N+1$; preparation contributes all $N$ Tick returns; the new-origin Read contributes one; passive Ticks contribute $2N$. Summing proves (UFS.18). $\square$

Thus one actually acquired and subsequently controlled relation process reaches Space, Time, Boundary and Memory with the existing independent meanings. The result strengthens acquisition for this different initialization; it neither changes P's no-order-advice experiment nor identifies arbitrary controlled history with a passive clock.

## 7. No cap and no unit preparation: an exact deterministic obstruction

**Definition 7.1 (the uncapped task).** Remove both the supplied order cap and the authentic unit-preparation premise. Retain every finite rational positive-link rooted path with $0<T<I$, every arbitrary signed rational initial field, and the complete interface of Assumption 1.2. A deterministic source-blind protocol has the same source-independent initial information and installed program on all these specimens. Its choices may depend on the entire finite declared history and arbitrary local computation. It must halt after finite work on each specimen, returning either its exact native law or a finite installed predictor correct for every legal finite adaptive continuation from its actual stopping cut. The predictor evaluates hypothetical finite command words locally from its terminal record, without further source observations, as in Definition 4.1; actual execution then keeps that record synchronized with the same specimen. This is complete future behavior, rather than forwarding an unpredicted future return or claiming correctness only along a preselected continuation.

**Lemma 7.2 (a positive contracting path with any finite free prefix).** For every integer $t\ge0$ and every rational list $g_0,\ldots,g_t$, there is a rational initial field $z$ on the connected $(t+2)$-cell path

$$
S=\frac12 I+\frac18 A_{t+2},
\tag{UFS.19}
$$

where $A_{t+2}$ is the ordinary path adjacency matrix, such that $e_0^{\mathsf T}S^jz=g_j$ for $0\le j\le t$. All links are positive and $0<S<I$.

Proof. For any real vector $v$,

$$
\left|\frac14\sum_{i=0}^{t}v_iv_{i+1}\right|
\le\frac18\sum_{i=0}^{t}(v_i^2+v_{i+1}^2)
\le\frac14\|v\|^2.
$$

This is the offdiagonal part of $v^{\mathsf T}Sv$. Hence $\frac14I\le S\le\frac34I$, which implies both strict inequalities in the claim. The entries and links have the required rational values.

For $j\le t$, the row $e_0^{\mathsf T}S^j$ is zero beyond cell $j$ and has entry $(1/8)^j\ne0$ at that cell. Therefore the square matrix formed by these $t+1$ rows and columns $0,\ldots,t$ is triangular with nonzero rational diagonal. Set the last coordinate of $z$ to zero and solve this square system for the remaining coordinates. It has a rational solution for every target list. Its signs and amplitudes are unrestricted, exactly as allowed by the task. $\square$

**Theorem 7.3 (D3: no deterministic all-source termination without a cap).** No protocol in Definition 7.1 terminates correctly on every admitted specimen, for either exact native-law identification or a complete correct future predictor. This remains true with arbitrary finite adaptive rational Add pulses, with all Tick returns exposed and with unlimited finite Hold computation.

Proof. Suppose such a protocol exists. Run it on the one-cell specimen $T_0=(1/2)$ with entry field zero. By source-total termination it has a finite complete command history ending at some tick epoch $t$. List every pulse in that history as $(s_l,u_l)$, where $s_l$ is its actual tick epoch. Let $m_j^0=2^{-j}$. Choose the larger fixed path $S$ in Lemma 7.2 and let $\eta_j=e_0^{\mathsf T}S^je_0$. Define rational targets

$$
g_j=\sum_{l:s_l\le j}u_l\bigl(m^0_{j-s_l}-\eta_{j-s_l}\bigr)
\quad(0\le j\le t).
\tag{UFS.20}
$$

Including all pulses at epoch $j$ causes no anticipatory ambiguity: each has coefficient $m_0^0-\eta_0=1-1=0$. Pulses at later epochs are excluded. Lemma 7.2 supplies one rational field $z$ whose free responses through $t$ are precisely these targets. This fixes a single initial specimen $(S,z)$ before its replay; the field is not adjusted during its run.

At a cut in the reference history with tick epoch $j$, write $P$ for the pulses already executed. Formula (UFS.3) on $(S,z)$ gives

$$
\begin{aligned}
e_0^{\mathsf T}x_S
 &=g_j+\sum_{l\in P}u_l\eta_{j-s_l}\\
 &=\sum_{l\in P}u_lm^0_{j-s_l}
 =e_0^{\mathsf T}x_{T_0}.
\end{aligned}
\tag{UFS.21}
$$

All pulses with $s_l<j$ have already occurred, and any excluded pulse with $s_l=j$ contributes zero to the difference in (UFS.20); this proves the middle equality even when many Adds and Reads occur at one epoch. The same equality at the next epoch includes every root returned by a Tick. Fixed Add and Hold acknowledgements also agree. Therefore induction on this complete command history makes the deterministic protocol choose the same commands, rational inputs and termination decision on $(S,z)$. Local duration, source size or a hidden identifier cannot change the decision in the declared interface.

The returned native law cannot be correct for both specimens: one has order one and the other order $t+2\ge2$. Their impulse laws already differ at index two, since

$$
m_2^0=\frac14,\qquad \eta_2=\frac14+\frac1{64}.
\tag{UFS.22}
$$

To cover a predictor-only output, let $a,b$ be the two actual fields at their common stopping cut. Consider the legal future words $W={\rm Tick}^2$ and $W^+={\rm Add}(1)\,{\rm Tick}^2$. In each system, the difference between these words' last scalar outputs is its own second impulse moment, independently of $a$ or $b$. If the two systems agreed on both complete words, these differences would agree, contradicting (UFS.22). Thus at least one legal finite continuation distinguishes their complete future behavior. The controller's identical terminal record and common future program cannot be correct on both. This is a contradiction for either output requirement. $\square$

The two continuations in this argument specify two possible future choices, not an actual cloning operation. A predictor claimed complete for the menu must be correct for each choice from its stated cut. On the pair, one of those choices witnesses failure.

The witness is symmetric, connected, has positive links and is strictly positive contracting. It is not PG17.3's general delayed nilpotent chain. Its arbitrary signed initial field absorbs the finite input-dependent differences through the stopping cut. No fixed norm/energy bound on that field is claimed. The construction selects its field after inspecting a deterministic terminating history to prove existence of a counterexample; it does not let a source change during the experiment.

This theorem makes no randomized, bounded-field, nonnegative-field, noisy, physical or universal impossibility assertion. A random-tape-dependent witness would not prove a fixed-source randomized result. An order cap is one sufficient remedy by Theorem 3.1; neither this obstruction nor that construction proves that a cap is the only possible additional premise.

## 8. Same-run returns, simultaneous storage and finite width-dependent work

**Convention 8.1 (traffic and source work).** Rational values use reduced signed numerator and positive denominator in binary, with self-delimiting framing. Commands, inputs, scalar returns and fixed acknowledgements have their own actual framing. A raw call is paid even if its return is redundant. No exact scalar is assigned unit bit cost independent of width.

One concrete Hold schedule is: an initial Hold before the first Read; one Hold after the $2R$ free values; one after each of the $N$ post-pulse Tick pairs; one after each of the $N$ preparation Tick/Add pairs; and one after each of the $N$ final passive Tick pairs. The last Hold of startup covers predictor installation and the control solve. The last preparation Hold covers the new-origin Read. These Holds protect local processing without any silent Tick.

**Proposition 8.2 (complete attained traffic).** The following counts refer to that single schedule, with the final passive segment stopped at $k=2N$.

| Coordinate | At unknown-field startup | Through actual unit preparation and the paid P39 cut |
| --- | --- | --- |
| Ticks | $J_*=2R-1+2N$ | $J=2R-1+5N$ |
| Adds, including the startup Add$(1)$ | $1$ | $N+1$ |
| Reads | $2$ | $3$ |
| Scalar returns, including every Tick return | $J_*+2=2R+2N+1$ | $J+3=2R+5N+2$ |
| Explicit Holds | $N+2$ | $3N+2$ |
| Fixed acknowledgements, Add plus Hold | $N+3$ | $4N+3$ |
| Total calls and return frames | $2R+3N+4$ | $2R+9N+5$ |

Proof. The initial and post-pulse Reads account for the first two Reads. The only further Read is the actual new-origin Read. The Tick and Add counts were proved in Theorems 3.1, 5.1 and 6.2. The enumerated Hold schedule has respectively $1+1+N$ and $1+1+N+N+N$ Holds. Each Hold and Add produces one fixed acknowledgement; each Read and Tick produces one scalar. Summing the disjoint return types also equals the number of calls, giving the last row. $\square$

There are also $N+1$ transmitted pulse rationals: the literal $1$ and the computed $u_j$. Their widths and all command/return framing are added to scalar payload, as are the initial cap input and its assurance. Acknowledgements are counted even when fixed. This attained schedule claims neither minimum Read count nor minimum total call or bit cost.

For the direct simultaneous-buffer implementation of P Proposition 41.2, each source Tick uses $3N-2$ rational multiplications and $2N-2$ rational additions. Thus the final schedule has $J(3N-2)$ such multiplications and $J(2N-2)$ such additions, plus the $N+1$ actual root additions, input decoding, holds, output and framing. For $N=1$ the addition count for Tick is zero. Both source buffers coexist with the observer's stores.

**Proposition 8.3 (finite attained arithmetic and widths).** Let $B$ be the total binary encoding length of the actual $2N-1$ coefficient words and $X$ that of the initial $N$ field words, including their signs and denominators. These are proof parameters, not startup advice. There is an exact implementation of the construction through (UFS.18) with $O(R^4)$ rational arithmetic/gcd/lcm/comparison operations, $N-1$ promised rational-square-root extractions, and a conservative intermediate integer/rational width

$$
U=O\!\left(R^2\bigl(B+X+\log(R+1)+1\bigr)\right).
\tag{UFS.23}
$$

In particular every admitted specimen has finite work and storage. No bound on these widths or on the control amplitudes follows from $R$ alone.

Proof. Let $D$ be the product of coefficient denominators and $E$ the product of entry-field denominators, so $\log_2 D\le B$ and $\log_2 E\le X$. They need not be known by the observer. Before unit preparation, the freely evolving term has denominators dividing $ED^j$ and norm at most $\|x^{\rm in}\|\le\sqrt N\,2^X$. After the startup Add$(1)$, its extra term has denominators dividing $D^j$ and norm at most one. Every free value, impulse value and actual startup scalar used has exponent $O(R)$ and reduced width $O(X+RB+\log(R+1)+1)$.

For the signed rank test, clear denominators with the lcm of the observed entries. This lcm divides $ED^{2R-1}$. The recurrence solve has right-hand side from the same prefix. For an $h$-row integer matrix with entry width $L$, Hadamard's bound gives minor width $O(hL+h\log(h+1))$. Rank-revealing fraction-free elimination with row/column pivoting computes its rank and solves its nonsingular selected systems with intermediate widths of this size. Here $h\le R$ and $L=O(X+RB+\log(R+1)+1)$, within (UFS.23). Zero pivots are dealt with by pivot search; signed free blocks need no positivity assumption.

Retain the $\gamma_j$ with a common determinant denominator from (UFS.6). In extrapolation, clear the current free-value window by its lcm before forming the recurrence sum. Its denominator divides $ED^h$ for the largest actual index $h$ of that window, which remains $O(R)$ during startup. Products, sums and reduction therefore retain width $O(U)$: unrelated denominators are not multiplied afresh for every summand. The reduced predicted values are the actual $f_j$ by Proposition 2.2. Subtraction yields actual impulse values with their stated denominators.

P's coefficient/recurrence decoding uses integer-scaled positive impulse blocks, their minors, monic orthogonality solves and finite pairings. The same minor bound applies, with $X$ unnecessary for those impulse blocks. Pairings can use their common determinant denominators; their product and sum widths are $O(U)$. Each link square root is taken on the reduced numerator and denominator of a promised rational square. Integer roots and exact squaring checks are finite at these widths. Matrix powers to exponents $O(R)$ construct $\mathcal O_N$, the actual field and $C_N$ using common denominators and reduced arithmetic. The observability solve has startup values as its right-hand side and has the same augmented-minor bound.

For control, $T^Nx_*$ has denominators dividing $ED^{s+3N}$. Clearing the coefficients and right-hand side of (UFS.16) therefore gives entries of width $O(X+RB+\log(R+1)+1)$. The inverse/control solve gives all pulse inputs with a common determinant denominator $\Delta$ and numerator/denominator widths $O(U)$. During actual preparation, (UFS.17) shows that every source coordinate has a denominator dividing $E\Delta D^{s+3N}$, and magnitude at most $\|x_*\|+\sum_j|u_j|$. Both its logarithmic denominator and logarithmic magnitude are $O(U)$. Adding the final $2N$ passive Ticks only increases the exponent by $O(R)$; in fact after preparation their states are exactly $T^ke_0$. Thus source buffers, all returns, predictor states and control arithmetic have finite $O(U)$ width as claimed.

One rank elimination and free recurrence solve cost $O(R^3)$ arithmetic operations. Free extrapolation through $s+2N$ costs $O(R^2)$ operations. Successive pulse-block tests and separate monic-polynomial solves cost $O(\sum_{j\le N}(j+1)^3)=O(N^4)$. Observability, control and record installation add at most cubic arithmetic and quadratic sparse power generation. Gcd/lcm calculations, comparisons and counter work fit a conservative $O(R^4)$ allowance at these widths. This proves the displayed attained bounds.

For an explicit bit interpretation let $A(U)$ bound a reduced rational arithmetic/gcd/lcm/comparison operation at width $O(U)$, and let $Q(U)$ bound an integer square-root extraction with its exact test. Schoolbook integer algorithms give finite polynomial bounds; for example conservative choices $A(U)=O(U^3)$ and $Q(U)=O(U^3)$ suffice. Algebraic observer work is then at most

$$
O\bigl(R^4A(U)+R Q(U)\bigr),
\tag{UFS.24}
$$

with the source operations, serialization, allocated storage, rights/backing and any separately materialized output charged in addition. No unit-cost real-number or root oracle has been used. $\square$

**Definition 8.4 (one simultaneous layout).** An attained implementation can retain all the following resources together. The quantities are added, rather than drawn from incompatible cheap implementations.

| Coexisting resource | Attained numerical store or separately specified charge |
| --- | --- |
| Actual source | $N$ cells, $N-1$ links, coefficient store $B$ |
| Simultaneous source update buffers | $O(NU)$ bits |
| Supplied cap and cap assurance | $O(\log(R+1))$ numerical bits, plus actual assurance representation/backing |
| Actual scalar records, command/pulse journal, acknowledgements | $O((R+N)U)$ numerical bits, plus their actual framing; another retained copy is added |
| Free-response certificate, generated window and extracted impulse records | $O((R+N)U)$ bits, including rank/pivot information |
| Retained native law, $q,\mu$, actual native record and predictive state | $O(B+NU)$ bits |
| Pulse list and preparation progress | $O(NU+\log(R+1))$ bits |
| Elimination, polynomial, observability and control scratch | a constant number of $O(R^2)$-word arrays, or $O(R^2U)$ bits |
| Generic program, parsing, counters and communication buffers | their actual allocated bits; all $O(R)$-bounded indices use $O(\log(R+1))$ bits |
| Root/source reference, serialization and exclusive-access resources | their actual retained representations and backing |
| Read/Tick/Hold and signed Add rights, source-class/fixedness assurance, Hold/control installation | their actual retained representations, setup and backing |
| Exported view/predictor copies and output buffers | their actual simultaneous lengths, including every separately materialized Time list |

The explicitly bounded numerical stores total $O(B+R^2U)$ bits for this run, plus the separately named framing, output, program, assurance, rights and backing resources. Shared backing is counted once only when actually shared. Holding the specimen during local elimination is a supplied paid control capability, not an inference from the data.

**Proposition 8.5 (no cap-only amplitude or lifetime-width bound).** Fixed $R$ does not bound startup scalar widths, preparation amplitudes or later literal output widths.

Proof. At $R=N=1$, $T=(1/2)$ and entry field $x^{\rm in}=M\in\mathbb Q$, the first Read already returns arbitrary $M$. Here $s=1$ and the startup ends at $x_*=M/8+1/4$. The one-pair preparation input is $u_0=1-Tx_*=7/8-M/16$, whose amplitude is unbounded as $M$ ranges over rational integers. Even after the unit origin has been earned, the passive root $2^{-k}$ has denominator width $k+1$ at epoch $k$. A finite controller and finite native order therefore do not bound the storage or traffic of all finite continuations. $\square$

## 9. Credited suppliers, exact contribution and remaining scope

**Correspondence 9.1 (classical and repository mathematics).** The following suppliers are credited with their actual uses. Relative repository links in this table refer to the fixed public revision specified at the start of this volume. Owning Scribes explain the declarations; they do not supply an additional observation or operation.

| Supplier | Instantiated hypotheses, supplied content and subtraction |
| --- | --- |
| [P §§36–38][P] | Same rational rooted Jacobi matrix, positive links, $0<T<I$, and actual root-returning Tick/Read/Hold/Add operations. P starts at $e_0$ without order advice. Here the initial field is arbitrary, $R$ is supplied, and a paid free-response certificate plus Add exposes impulse moments. Native triangularity, positive impulse flatness and Jacobi decoding are reused. P38's unit-origin lower horizon is not transported to this changed initialization. |
| [P §§39–42][P] | P39's independent four views, strict passive phase separation, inverses and Tick agreement are consumed only after actual unit preparation and a new paid $k\ge2N$ passive prefix. P40's arbitrary-field predictive update identities are initialized at the actual cut (UFS.13). P42.4 owns the unauthenticated-origin boundary; the new control construction earns an origin instead of treating the old one as supplied. |
| [PG Definition 12.5 and §17][PG] | $A=T,H=e_0^{\mathsf T},B=e_0$ gives the unknown free term and the input convolution; separating Add from Tick fixes the age convention in (UFS.3). Finite realization and known-order algebra are mature. PG17's general delayed-chain obstruction does not itself meet the symmetric positive contracting path conditions of §7. |
| [FiniteAtomicHankelVandermonde][HVD] and its [owning Scribe][HVDs] | `hankel_moment_matrix_factorization` with `order = R`, nodes the visible $\lambda_l$, weights the signed $c_l$, supplies $G_R=V D_c V^{\mathsf T}$. Its theorem is an algebraic identity without distinctness, positivity or rank conclusions. Lemma 2.1 verifies the additional native simple-spectrum and nonzero-visible-weight conditions and derives the rank consequence. |
| [FiniteHoKalmanBlocks][HK] and its [owning Scribe][HKs] | `sample_factorizations` and `finite_samples_exact_recovery` use $2h$ samples and a nonsingular selected order-$r$ block. For the free response, $h=R$, scalar ports and visible diagonal realization $(\operatorname{diag}\lambda,\mathbf1,c^{\mathsf T})$ give these sample semantics, with the first $r$ indices as pivots. The signed rank proof earns $r$ under the cap. `finite_samples_order_lower_bound` alone gives only a lower bound; it does not infer absence of a larger hidden native source. The explicit rational recurrence is the same finite realization algebra in companion coordinates. |
| [CoefficientDrivenJacobiCharacteristicPolynomial][JAC] and its [owning Scribe][JACs] | `coefficient_driven_jacobi_characteristic_polynomial` uses real Euclidean $E=\mathbb R^N$, power basis $T^je_0$, positive impulse Hankel inner product, self-adjoint multiplication and monic $q$. P37 supplies this exact correspondence. Its private `orthogonal_power_basis_monic`, `orthogonal_power_basis_upper_zero`, `squared_norm_pos` and Jacobi-entry helpers are part of the supplied proof, rather than missing results to re-prove. No normalized uniform trace-moment premise is assumed for root weights. |
| [Pinned mathlib Vandermonde][MV] | At repository `lake-manifest.json`'s mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, `Matrix.det_vandermonde_ne_zero_iff` identifies a nonsingular square Vandermonde with injectivity of its nodes. Its convention has node-index rows and degree columns; the first $r$ rows of our $V_R$ are its transpose. All $r$ visible nodes are distinct. |
| [G. Teschl, *Jacobi Operators and Completely Integrable Nonlinear Lattices*, §2.5][Teschl] | Equations (2.109)–(2.118), printed pp. 42–43, own moment orthogonalization and positive norm-ratio Jacobi reconstruction; the finite-support paragraph on p. 44 gives termination at $C(N+1)=0$. Here $C(N+1)=\det H_N$, his offdiagonal $a(n)$ is our $b_{n-1}$, and his diagonal $b(n)$ is our $a_{n-1}$. His Theorem 2.13 assumes nonfinite support and is not literally invoked for this finite matrix. |
| R. E. Kalman, *Mathematical Description of Linear Dynamical Systems*, [DOI][Kalman]; B. L. Ho and R. E. Kalman, *Effective Construction of Linear State-Variable Models from Input/Output Functions*, [DOI][HoKalman] | Mature finite realization, controllability and observability background. The single-input controllability columns here are $T^je_0$, observation rows are $e_0^{\mathsf T}T^j$, and their nonsingularity is supplied by P's native path triangularity. The actual signed rational solve and command order in (UFS.15)–(UFS.17) prove the required source-specific preparation; no physical implementation or fee theorem is imported from these citations. |

**Correspondence 9.2 (other common-source owners).** [Native Discovery and Retained Context][NDR], Definitions 1.1–1.4, Theorems 3.1 and 4.1, and §§5–6 distinguish a source-relative determining certificate from one common discovery procedure, actual paid reacquisition from a retained context, and current recovered geometry from erased chronology. Here the source is a changing rational field on a fixed weighted path, not its stationary free ordered tree with four-valued arbitrary-address replies. The cap and free-response certificate are explicit additional supplied/earned data; neither NDR's factor-two ratio nor its tree reconstruction port is invoked for this service. Its finite static-witness discipline is respected by (UFS.20)–(UFS.21): one actual initial field is chosen, rather than a source changed along replay.

[Native Constructor Boundary Networks][CBN], Definition 1.2, Convention 6.3 and §7, counts all source-bearing retained fields, complete replies, late target inputs, entry/isolation and same-source rights. Its coupled constructor relations and finite table elimination refer to original literal tree observations. The related [NativeRelativePrefixBoxes][NRP], `canonical_factor_levels`, and its [owning Scribe][NRPs] concern `Source = FreeMagma Bool`, actual `readout`, $\Gamma$ blocking factors and canonical tree levels with $|q|<d$. They neither supply rational root samples nor an initial-field bound or source-control capability. No independent reply array, extra donor query or free source-varying selector is used here. Source binding, cap assurance, control/input rights and all retained free/pulse records remain part of the common run and resource layout.

[Compatible Predictive Waves][Wave], §§2 and 4, supplies positive-kernel/Gram representation and the distinction between a recurrence and a norm-preserving coherent wave. Its §12 supplies a common model only with its declared references, controls and growing record carriers; §13 credits the mature ingredients. Our free-response Hankel form may be indefinite and is not such a strong positive coherent kernel. Only the extracted impulse blocks are positive Gram blocks. Moreover $0<T<I$ is contracting rather than unitary; no complex phase, coherent recombination, arbitrary measurement or quantum wave origin follows. The common-source and growing-record obligations agree, while the operational and algebraic hypotheses remain separate.

**Conclusion 9.3 (conditional source-relative advance).** The advanced cut in Theorem 3.1 is the actual field after $2R-1+2N$ Ticks and one Add, not a putative unit field or an earlier symbolic realization. Theorems 3.1 and 4.2 establish acquisition and complete callable use there despite zero or noncyclic entry fields. Theorem 5.1 earns an actual unit origin by the existing paid root controls. Theorem 6.2 then enters the already supplied four-view domain with a separately paid real passive prefix. Theorem 7.3 proves a deterministic no-cap obstruction within the same positive contracting path class, using unbounded signed initial fields. These source-specific deductions reuse finite exponential interpolation, Hankel factorization, inverse Jacobi theory, controllability and observability; they make no claim of worldwide priority.

The sufficient cap remedy trades P's installed unit preparation for supplied order advice and paid rational control. It is not P37's no-order-advice assertion with a renamed initialization, nor a solution of any old fixed-$G_{\rm gc}$/original-$Q$ problem. No optimal startup horizon, minimum total memory/traffic, noisy rank instrument, arbitrary graph inverse, norm-bounded or randomized lower bound, physical implementation, universal $\alpha/\beta$ generation, or recovery of erased pre-startup chronology has been established. The continuing four-expression programme requires its further source-specific realization and recovery bridges beyond this conditional digital model.

[P]: RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md
[PG]: RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DISCOVERY_AND_RETAINED_CONTEXT.md
[CBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[Wave]: AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md
[HVD]: ../../../D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.lean
[HVDs]: ../../../Blueprint/D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.scribe.cs
[HK]: ../../../D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.lean
[HKs]: ../../../Blueprint/D5/S3/Observer/Hankel/FiniteHoKalmanBlocks.scribe.cs
[JAC]: ../../../D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.lean
[JACs]: ../../../Blueprint/D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.scribe.cs
[NRP]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeRelativePrefixBoxes.lean
[NRPs]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeRelativePrefixBoxes.scribe.cs
[MV]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Vandermonde.lean
[Teschl]: https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf
[Kalman]: https://doi.org/10.1137/0301010
[HoKalman]: https://doi.org/10.1524/auto.1966.14.112.545

## 追加锚（本行以下为增补区）

## 10. A confidence-qualified contract without order advice

**Definition 10.1 (the randomized uncapped task).** Fix one finite specimen $(N,T,x^{\rm in})$ satisfying (UFS.1), with arbitrary signed $x^{\rm in}\in\mathbb Q^N$, before any random bits are drawn. Retain Assumption 1.2's exact Read, returning Tick, Hold and signed rational Add service, common root binding, class/fixedness assurance, exclusive serial access and paid storage/control backing, but remove the cap and its assurance. The public numerical input is an integer $b\ge1$. No $N$, coefficient, entry-field, energy or word-length bound is supplied. Reset, cloning and additional specimen ports remain absent.

The controller additionally has a paid source of independent fair bits, independent of the fixed specimen and of all preceding draws. This is an explicit randomness resource and independence premise; it is not inferred from the endpoint observations or replaced by a finite deterministic seed. Only finitely many bits are requested on each run. The generator, its current material, access right, output framing and actual work/backing are charged separately from the specimen. The controller is one finite effective program with growing finite stores, in the sense of §1.

The correctness contract is now

$$
\forall (N,T,x^{\rm in})\ \forall b\ge1,\qquad
\mathbb P_\omega\!\left[\mathcal C(N,T,x^{\rm in},b,\omega)\right]
\ge1-2^{-b},
\tag{UFS.25}
$$

where $\mathcal C$ is one joint assertion: the exported native law and current field are exact, the retained predictor is correct for every legal finite adaptive continuation, a unit field has actually been prepared, and a subsequent actual passive segment has reached P Definition 39.1's domain with its original four meanings. Termination is required on every tape. A rejected local candidate is not an error certificate about the specimen. An exported result is confidence-qualified: on exceptional tapes its model, preparation assertion and view interpretation may be wrong without a warning. There is no claim of an exact hidden-order certificate or of one tape correct for every specimen.

**Definition 10.2 (stage amplitudes).** For $n\ge1$ set

$$
\ell_n=\lceil\log_2(n+1)\rceil,\qquad
k_n=b+n+\ell_n,\qquad M_n=2^{k_n},\qquad
\delta_n=2^{-b-n}.
\tag{UFS.26}
$$

At stage $n$ exactly $k_n$ fresh bits, interpreted as an unsigned binary integer, choose $U_n$ uniformly from $\{0,\ldots,M_n-1\}$. There is no rejection sampling. The stage number is a computed search variable, not native-order advice.

**Lemma 10.3 (a randomized determinant gate on the actual field).** At a held cut let the actual field be any $z\in\mathbb Q^N$. Execute Add$(u)$, Read the resulting root $y_0(u)$, and execute $2n$ actual Ticks with all their returns $y_1(u),\ldots,y_{2n}(u)$. Define

$$
\begin{aligned}
y_j(u)&=e_0^{\mathsf T}T^j(z+u e_0),\\
D_{n,z}(u)&=\det\bigl(y_{i+j}(u)\bigr)_{0\le i,j\le n}.
\end{aligned}
\tag{UFS.27}
$$

If $n<N$, this is a nonzero rational polynomial of degree exactly $n+1$, with strictly positive leading coefficient. Consequently, conditional on any preceding history that reaches this cut, a fresh $U_n$ satisfies

$$
\mathbb P\bigl[D_{n,z}(U_n)=0\mid\text{preceding history}\bigr]
\le\frac{n+1}{M_n}\le\delta_n.
\tag{UFS.28}
$$

If $n=N$, then $D_{N,z}(u)=0$ for every $z$ and every rational $u$.

Proof. Write $g_j=e_0^{\mathsf T}T^jz$. The matrix in (UFS.27) is $G+uH_n$, where $G=(g_{i+j})$ and $H_n=(m_{i+j})$. Multilinearity of the determinant gives its coefficient of $u^{n+1}$ as $\det H_n$. P Lemma 37.1 gives $H_n=K_n^{\mathsf T}K_n>0$ for $n<N$, so that coefficient is nonzero. This argument uses no sign or cyclicity assumption on $z$. The finite atomic factorization of §2 is compatible with these signed free weights; positivity is required only of the impulse leading coefficient.

The mature univariate root bound says that a nonzero degree-$(n+1)$ polynomial has at most $n+1$ distinct rational roots. This is, in particular, the bound supplied by pinned mathlib's `Polynomial.card_roots'` and `Polynomial.card_le_degree_of_subset_roots`, together with `Polynomial.mem_roots` for a nonzero polynomial. Uniform sampling and $2^{\ell_n}\ge n+1$ give (UFS.28). Conditional on the preceding history, $z$ is fixed before these bits, even if earlier rejected branches changed it.

For $n=N$, put $w=z+u e_0$. The same observed matrix factors as

$$
\bigl(y_{i+j}(u)\bigr)_{0\le i,j\le N}
=[e_0,Te_0,\ldots,T^Ne_0]^{\mathsf T}
 [w,Tw,\ldots,T^Nw].
\tag{UFS.29}
$$

Both factors pass through $\mathbb Q^N$, so this $(N+1)$-row matrix is singular. This proves the last assertion without interpreting an early zero determinant as native flatness. $\square$

## 11. A bounded candidate branch with no rollback

**Definition 11.1 (the total candidate branch $\mathcal B_n$).** The input to this branch is the current held specimen, the finite search value $n$, and its existing complete command/return record. The statement $N\le n$ is a trial hypothesis, not supplied information. The following finite construction is a guarded version of §§2–6 with trial cap $R=n$.

1. Issue a new Hold and Read $f_0$. Execute exactly $2n-1$ returning Ticks, then Hold. In this branch only, $f_j$ denotes the free response from its actual entry field $z$; no Add has occurred during this prefix. Compute $r=\operatorname{rank}(f_{i+j})_{0\le i,j<n}$ by rational elimination with bounded pivot search. For $r=0$ take the candidate free sequence to be zero. For $r>0$ require the leading $r$-row block to be nonsingular before solving (UFS.6). Generate the candidate recurrence sequence $\widehat f_j$ from its first $r$ values through index $4n-1$, and require agreement with every observed $f_0,\ldots,f_{2n-1}$. A failed determinant, solve or comparison rejects the branch at this held cut. This includes the $r=0$ case when the observed prefix is not all zero.

2. Write $s=2n-1$. Execute Add$(1)$ and Read $v_0$. Execute at most $n$ pairs of returning Ticks, with a Hold after each pair. After $j$ pairs form $d_i=v_i-\widehat f_{s+i}$ for $0\le i\le2j$, and require $d_0=1$. Examine $H_j(d)=(d_{i+l})_{0\le i,l\le j}$. Continue only while this matrix is positive definite and $j<n$. At its first singular occurrence, require its preceding leading block $H_{j-1}(d)>0$ and set $d=j$ for the trial native dimension. A nonsingular block that is not positive definite rejects the branch. A positive definite block at $j=n$ also rejects it. Thus the branch never searches beyond $2n$ post-pulse Ticks. In the singular case the positive preceding block and the zero Schur complement imply positive semidefiniteness and rank exactly $d$; these are finite matrix statements, not an assertion about the hidden order.

3. For this $1\le d\le n$, apply the monic moment-orthogonalization formulas (UFS.10) to the available $d_i$. Require every denominator used to be nonzero and every required norm to be positive. For each positive reduced norm ratio, compute the floor integer square roots of its numerator and denominator and square them back. Reject unless both are exact squares. Use their positive rational ratio as the link. Form the symmetric tridiagonal candidate $A\in\mathbb Q^{d\times d}$; require positive links, $A>0$ and $I-A>0$. Positive definiteness is decided by the finitely many leading principal minors. Compute its monic characteristic polynomial $q_A$, impulse vector $\mu_A$, and finite rational transfer $F_A$ as in P Proposition 37.4. Require $e_0^{\mathsf T}A^j e_0=d_j$ for every acquired $0\le j\le2d$. All these calculations have bounded degree and dimension. No factorization into unknown real eigenvalues is requested.

4. Form $\mathcal O_d(A)$ and $C_d(A)$ by (UFS.11) and (UFS.15), replacing $T,N$ with $A,d$. Check nonsingularity before each solve. Set

$$
\widehat w=\mathcal O_d(A)^{-1}(v_0,\ldots,v_{d-1})^{\mathsf T},\qquad
\widehat x_*=A^{2d}\widehat w,\qquad
C_d(A)u=e_0-A^d\widehat x_*.
\tag{UFS.30}
$$

Retain the candidate native/predictive records of Definition 4.1 with this $A,\widehat x_*$. Reject if any required arithmetic or check fails. Otherwise retain the finite rational pulse list $u_0,\ldots,u_{d-1}$. At this point the actual specimen has undergone the free prefix, Add$(1)$, and $2d$ further Ticks. The vector in (UFS.30) is only a candidate for that actual cut until correctness has been established.

5. Execute exactly $d$ pairs Tick; Add$(u_j)$, including Add$(0)$ when prescribed, with a Hold after each pair. Update the candidate predictor as in Definition 4.1 and retain every actual Tick scalar and acknowledgement. Compare every Tick scalar with its candidate prediction, retaining a Boolean conjunction of these finite comparisons. After the final pair, Read the actual root and include comparison with $1$. This is a proposed new origin, not yet an unconditional unit-origin assertion.

6. Execute exactly $2d$ further returning Ticks with no Add, and a Hold after every pair. Retain the origin Read and all these actual scalar replies as a new segment, and compare them with $e_0^{\mathsf T}A^j e_0$ for $0\le j\le2d$. Continue to update the candidate native/predictive record. Once step 5 has begun, complete steps 5–6 even if a scalar comparison fails; the conjunction records failure. All prescribed inputs have already been computed. This convention gives a fixed finite suffix and leaves every real output accounted for.

7. If every comparison succeeded, accept the candidate and export its law, synchronized candidate field/predictor and its four proposed views at $k=2d$. Space, Boundary and Memory are computed from $(A,A^{2d}e_0)$ by Definition 6.1; Time is the actual segment of step 6, including its origin Read. Otherwise reject at the final held cut. No P39 phase-enumeration or image-recognition search is run on an unverified candidate: $2d$ is the actually executed suffix length. Later view inverses are guaranteed only on the correctness event and their declared images.

All divisions in these steps are preceded by nonzero tests. Rank, determinant, linear-system, positivity, equality and square tests use exact finite integer/rational algorithms; a failed arithmetic precondition returns rejection. There is no unbounded search for a rational square root, a spectrum, an image point or a later flat block. A branch rejected before steps 5–6 issues none of their commands. A branch rejected after that suffix has performed all of it.

**Proposition 11.2 (totality, exact capped specialization and preserved field).** For every finite promised specimen, every current rational field, and every $n\ge1$, $\mathcal B_n$ either accepts or rejects after finite work. If the actual $N\le n$, it accepts, with $d=N$, the exact native law and actual field, genuine unit preparation and a real P39 passive segment. Its counts in that case are exactly those of Proposition 8.2 with $R=n$.

On every branch, including a rejected one, the next source state is the actual advanced state. If $t$ Ticks and pulses $(s_l,u_l)$ have been executed since that branch's entry field $z$, then

$$
x_{\rm next}=T^t z+\sum_l u_lT^{t-s_l}e_0.
\tag{UFS.31}
$$

The specimen remains at this field and all its emitted values, input words and acknowledgements remain in the retained record. Rejection does not restore $z$, undo a pulse or erase a returned scalar. It need not reveal the coordinates of $x_{\rm next}$.

Proof. Every loop has a bound in $n$ or $d\le n$; all exact tests terminate on rational/integer inputs. Elimination searches a finite set of pivots, and a singular required system rejects before division. The integer square-root tests are finite also when the input is not a rational square. The suffix has predetermined finite length and rational inputs even if $A$ is not the actual law. The actual source remains finite and rational under every such command. These facts prove totality without assuming the trial cap.

If $N\le n$, Proposition 2.2 proves the free recurrence, including zero and noncyclic entry fields. Every added guard in step 1 then succeeds. Theorem 3.1 makes the differences in step 2 the actual impulse moments. P Lemma 37.1 makes the first singular block occur at $d=N$, with all required positive leading blocks. P Proposition 37.3 gives the actual positive rational links, so every root, positivity and moment check succeeds and $A=T$. The observability solve in (UFS.30) is exactly (UFS.12); hence $\widehat x_*$ is the true advanced field. Theorems 4.2 and 5.1 make every preparation comparison true and the actual proposed origin equal to $e_0$. Theorem 6.2 then makes the passive segment and every comparison true. The fresh initial Hold and all pair Holds follow Convention 8.1, yielding the same capped counts. The guards add local calculation, not source commands.

Finally (UFS.31) is (UFS.3), based on the actually executed prefix, whether or not a candidate passed. Read and Hold leave it unchanged. Retaining the same source and its complete command/return record proves the asserted preservation. Neither the rank calculated in step 1, the singularity in step 2, nor finite consistency in step 7 certifies the trial cap on its own. $\square$

## 12. The cap-free finite procedure and its specimenwise probability

**Definition 12.1 (the stagewise startup).** Begin at stage $n=1$. Hold the current source while drawing exactly the bits in Definition 10.2. Execute the gate of Lemma 10.3: Add$(U_n)$, Read, and $2n$ returning Ticks. Hold and evaluate its observed determinant. If it is nonzero, pass to stage $n+1$. If it is zero, run $\mathcal B_n$ from the actual held field $T^{2n}(z+U_n e_0)$ left by that gate. Accept and halt precisely when the branch accepts; after a rejection pass to stage $n+1$ with the actual field and record left by (UFS.31). The determinant is computed directly from its paid samples; its polynomial coefficients and the hidden $T$ are not inputs. The only randomness in this startup is the prescribed finite bit block at each reached stage.

**Theorem 12.2 (termination on every tape by the native-order stage).** Definition 12.1 is one finite program independent of the unknown specimen. On every admitted finite specimen, every $b\ge1$ and every bit tape, it halts at a stage $m\le N$. Every attempted branch and every intervening local computation is finite. No order bound or field-width bound is an input.

Proof. Induct over the stages. The actual field at each entry remains rational by the command semantics and Proposition 11.2. The stage uses a fixed finite bit block, $2n$ Ticks and a finite determinant calculation. A nonzero determinant advances the stage after finite work; a zero determinant invokes a total branch. If no earlier stage accepted, stage $N$ is therefore reached. Lemma 10.3 makes its determinant zero for every amplitude and every entry field. Here the trial hypothesis of $\mathcal B_N$ is true. Proposition 11.2 makes this branch accept with no further randomness. Thus no run enters stage $N+1$. This is a stage bound in terms of the hidden actual order, not a public deadline or a constant bound on rational computation time. $\square$

**Theorem 12.3 (one high-probability correctness event).** For each fixed specimen and $b$, there is an event $E$ of tapes with

$$
\mathbb P(E)\ge
1-2^{-b}\bigl(1-2^{-(N-1)}\bigr)\ge1-2^{-b}
\tag{UFS.32}
$$

on which every gate at $n<N$ is nonzero, the stopping stage is $N$, and the accepted branch has the exact conclusions of Proposition 11.2. For $N=1$ every tape belongs to $E$.

Proof. Let $Z_n$ be the event that stage $n<N$ is reached and its gate determinant is zero. Conditional on any preceding finite history reaching that stage, the actual field is fixed and the next block is independent and uniform. Lemma 10.3 gives conditional probability at most $\delta_n$. Averaging over these histories gives $\mathbb P(Z_n)\le\delta_n$, including histories in which previous candidate branches were rejected after real controls. Define $E$ to be the complement of $\bigcup_{n=1}^{N-1}Z_n$. The finite union bound gives

$$
\mathbb P(E^c)\le\sum_{n=1}^{N-1}2^{-b-n}
=2^{-b}\bigl(1-2^{-(N-1)}\bigr).
\tag{UFS.33}
$$

On $E$, stage 1, and successively every stage below $N$, has a nonzero gate and invokes no candidate branch. Stage $N$ is reached; Theorem 12.2 and Proposition 11.2 give its exact acceptance. The empty union at $N=1$ proves the last assertion. The ordinary root bound and union bound are the only probability estimates used; no distribution on specimens, entries or spectral weights is assumed. $\square$

## 13. The joint event includes acquisition, real preparation and continued use

**Theorem 13.1 (complete confidence-qualified unknown-field startup).** On the single event $E$ of Theorem 12.3, the same run has all the following properties simultaneously.

- Its accepted $N,T$, impulse law, native field at the acquisition cut (UFS.30), and final native field are exact. The initial random pulses and every gate Tick are included in the actual entry field of the successful branch, rather than treated as a reset or a second specimen.
- The branch's $N$ actual Tick/Add pairs prepare exactly $e_0$ at a new recorded origin $o$. The subsequent origin Read and $2N$ actual passive Ticks have the exact ordered values $(m_0,\ldots,m_{2N})$. At the terminal cut the physical field is $T^{2N}e_0$ relative to this new origin.
- Its retained $T,q,\mu$, native vector $\widehat x$ and predictive vector $a$ satisfy $\widehat x=x_{\rm actual}$ and $a=\mathcal O_Nx_{\rm actual}$. They predict every declared output and native successor for every finite legal adaptive continuation in the original Read/Tick/Hold/signed-Add menu. Scratch forecasts require no new source observation. Real calls retain their original rights, update the actual specimen, and keep this record synchronized.
- Space, Time, Boundary and Memory have precisely Definition 6.1's independent meanings and satisfy P Definition 39.1 with $k=2N$. Every recovery route and transported passive Tick agrees as in P Propositions 39.3–39.4. The independently retained command/output record does not become an extra field of each view.

These are one joint probability-$\ge1-2^{-b}$ claim, including the universal quantifier over later finite continuations; there is no extra error probability per output or continuation.

Proof. On $E$ the candidate branch is $\mathcal B_N$ with a true cap hypothesis, so Proposition 11.2 supplies its exact actual-cut identity, control execution and passive segment. Its unknown entry field is whatever the preceding random gate operations actually produced. The capped theorem applies to every such rational field, without requiring cyclicity, sign or a size bound. Substituting its earned law and field in Theorem 4.2 proves the invariant for every future field and legal operation. Induction on any common adaptive policy gives all of its outputs and successors, including arbitrary rational Add inputs and common future random choices. This is a deterministic consequence on each tape in $E$, so it does not require a union bound over policies.

Theorem 5.1 justifies the new unit origin by actual source operations. Theorem 6.2 then applies only to the separately paid passive suffix, which has no Add. It supplies the four-view domain, all inverses and route agreement. A later Add preserves the complete predictor but need not preserve that passive domain. Nothing identifies the earlier gate trajectory or the unknown entry history with a passive unit trajectory. $\square$

**Proposition 13.2 (the correctness contract has changed).** Theorems 12.2–13.1 neither contradict nor weaken Theorem 7.3. They give (UFS.25) for specimens fixed before independent bits. They give no exact order assertion from a zero gate or finitely many matching outputs, no all-tape correctness on every specimen, and no recovery of erased pre-entry chronology.

Proof. An early zero gate at $n<N$ is explicitly allowed by Lemma 10.3's finite root set. A consistent rational candidate at such a stage has dimension at most $n<N$; acceptance there exports a wrong native law. The probability argument bounds the event allowing this outcome, rather than certifying each accepted transcript. In particular its order of quantifiers is $\forall$ fixed specimen, probability over independent tapes. A witness chosen after a tape, as in a deterministic indistinguishability argument, cannot be substituted into that probability bound as though it had been fixed in advance. Conversely Theorem 7.3 still rules out a deterministic protocol with exact correctness and termination on all admitted specimens. This construction has removed that correctness requirement and added paid independent randomness; it does not claim a Las Vegas or zero-error solution.

Such silent errors are possible, rather than merely left unclassified. Fix $b$ and one particular stage-1 bit block. On $T_0=(1/2)$ with zero entry field, that block gives a finite accepting stage-1 history by Proposition 11.2. Apply Lemma 7.2 and exactly the input-compensation construction (UFS.20) to this finite history, including the selected random Add as an ordinary prescribed pulse. It gives one larger positive contracting rational path and one rational entry field that reproduce every scalar and acknowledgement through that acceptance. The selected block is then fixed in defining this specimen, before its fresh bits are drawn. With probability $1/M_1>0$ the new run draws that block, replays the same finite calculations and exports the one-cell law on the larger specimen. No later random block is requested. This reuses the old finite-history witness and is consistent with (UFS.32); it does not choose the specimen after the fresh draw.

The actual origin is newly earned, and Proposition 5.2 still supplies distinct older histories with the same entry field. The source, arbitrary signed-field class and missing Reset/clone/coefficient ports are unchanged. The earlier deterministic obstruction, capped counts and all passive/journal domain restrictions therefore retain their exact scopes. $\square$

## 14. Same-run calls, bits, traffic and rejected attempts

**Definition 14.1 (the attained Hold schedule and run quantities).** A gate uses one initial Hold during bit selection, Add$(U_n)$, one Read, $2n$ returning Ticks, and a final Hold during its determinant calculation. A candidate branch uses the fresh initial Hold, the free-prefix Hold and the pair Holds of Definition 11.1. No additional Hold is needed for its bounded checks. Rejecting a prefix leaves the last such Hold in effect. Successive Holds may be redundant but are still issued and charged. Let $m\le N$ be the actual stopping stage, and let $J,A,R,H$ count all actual specimen Ticks, Adds, Reads and Holds through its acceptance. The random source has its own draws and frames.

**Proposition 14.2 (all-tape resource counts).** Every run uses exactly

$$
K_m=\sum_{n=1}^m k_n
=mb+\frac{m(m+1)}2+\sum_{n=1}^m\ell_n
\le mb+\frac{m(m+1)}2+m\lceil\log_2(m+1)\rceil
\tag{UFS.34}
$$

fresh fair bits. For each reached stage its gate has exactly $(2n,1,1,2)$ in the coordinate order (Tick, Add, Read, Hold). A branch rejected at any prefix contributes at most $(7n-1,n+1,3,3n+2)$. Consequently all actual runs, including every failed check and preparation, satisfy

| Coordinate | Upper bound through stage $m$ |
| --- | --- |
| Ticks $J$ | $9m(m+1)/2-m$ |
| Adds $A$ | $m(m+1)/2+2m$ |
| Reads $R$ | $4m$ |
| Holds $H$ | $3m(m+1)/2+4m$ |
| Scalar returns $J+R$ | $9m(m+1)/2+3m$ |
| Fixed acknowledgements $A+H$ | $2m(m+1)+6m$ |
| Specimen calls and return frames $J+A+R+H$ | $13m(m+1)/2+9m$ |

The exact counts on any run are obtained by adding the displayed gate counts and the actual executed prefixes of its candidate branches. Each Add transmits its actual rational input, including the random integer and every zero or signed preparation pulse. The random generator contributes its $K_m$ bit returns, draws and actual framing in addition to this table.

Proof. No randomness is used inside a candidate branch, so (UFS.34) is exact. A complete candidate of dimension $d\le n$ uses $2n-1+5d$ Ticks, $d+1$ Adds, three Reads and $3d+2$ Holds, by the actual command list and Proposition 8.2. A rejected prefix cannot exceed these bounds with $d$ replaced by $n$; a failed first-flat-block search still stops after $2n$ post-pulse Ticks. Adding the gate gives per-stage upper bounds $9n-1,n+2,4,3n+4$. Sum them over $1\le n\le m$. Every Tick and Read emits one scalar, every Add and Hold one acknowledgement, and every command has one return frame, giving the last three rows. $\square$

**Proposition 14.3 (exact traffic on the stated success event).** On $E$, all stages $n<N$ consist only of their gates; stage $N$ has its gate and the complete true capped branch with $R=N$. The exact totals are

$$
\begin{aligned}
J&=N^2+8N-1,& A&=2N+1,\\
R&=N+3,& H&=5N+2,\\
J+R&=N^2+9N+2,& A+H&=7N+3,\\
J+A+R+H&=N^2+16N+5,& K&=K_N.
\end{aligned}
\tag{UFS.35}
$$

Proof. The gates contribute $2\sum_{n=1}^N n=N(N+1)$ Ticks, $N$ Adds, $N$ Reads and $2N$ Holds. The successful candidate contributes $7N-1$ Ticks, $N+1$ Adds, three Reads and $3N+2$ Holds, exactly Proposition 8.2 at $R=N$. Sum these actual disjoint portions. These are new procedure counts, not replacements for any count in §§3–8 or P §§37–41 and 57. $\square$

**Proposition 14.4 (source work and literal widths).** With P Proposition 41.2's direct simultaneous-buffer source update, the very same run performs $J(3N-2)$ source rational multiplications and $J(2N-2)+A$ source rational additions. Every scalar, Add input, random-bit return, command, acknowledgement and final export has its literal encoding and framing cost. A fixed acknowledgement is not a rational scalar. Neither a failed candidate nor a merely predicted scalar removes any actual source work or emitted item.

Proof. Each real Tick uses the original $N$-cell source, regardless of a candidate's smaller dimension. Every actual Add performs one real root addition. Read, Hold and serialization contribute their own actual work. The counts thus follow from the original service and the attained totals, with no substitution of the candidate size for the physical $N$. $\square$

## 15. Finite widths and material on every tape

**Definition 15.1 (widths and separately supplied material).** Let $B$ and $X$ be the total binary lengths of the true coefficient words and original entry-field words as in Proposition 8.3. They are proof parameters, not controller inputs. For a completed run $\rho$, let $W_\rho\ge1$ be the maximum actual integer/rational width in its source buffers, inputs, replies, candidate computations and predictor, including intermediate numerators/denominators and integer square tests. Use reduced rationals as in Convention 8.1. Let $L_{\rm io}$ count the actual bits written/read in all numerical traffic, framing, retained command/return records and exports, including separately materialized copies. Let $G_{\rm work},G_{\rm live}$ be the actual randomness provider's work and coexisting retained material, and let $I_{\rm access}$ denote the actual source/random references, program, rights, assurances and control/storage backing, with numerical representation sizes and nonnumerical backing distinguished.

**Proposition 15.2 (finite rational work, including false branches).** There is an attained choice of the finite exact algorithms in Definition 11.1 with observer arithmetic/comparison work $O(m^5)$, and $O(m^2)$ integer square-root tests, on every run stopping at stage $m$. These counts include the detector determinants, failed elimination or positivity tests, false extrapolations, rejected link roots, candidate decoding, preparation, passive checking and retained predictor installation. There are absolute constants $c,C$ for this choice such that every tape on a fixed specimen satisfies

$$
\begin{aligned}
H_0&=B+X+b+N+\lceil\log_2(N+2)\rceil+10,\\
W_\rho&\le C\,8^{\,c(N+1)^5}H_0.
\end{aligned}
\tag{UFS.36}
$$

In terms of actual attained widths, one sufficient bit-work bound, including the direct source arithmetic, is

$$
O\!\left(\left[m^5+(5N-4)J+A\right]W_\rho^3
       +K_m+L_{\rm io}\right)+G_{\rm work},
\tag{UFS.37}
$$

with actual installation/control/backing work added. This is a finite sufficient bound, without a claim of arithmetic optimality or a polynomial width bound for false candidates.

Proof. Reduced rational Gaussian elimination with finite pivot search costs $O(n^3)$ field operations per matrix of size at most $n+1$. Computing the at most $n$ successive blocks and all their finite leading-minor tests costs $O(n^4)$ if previously needed minors are reused. Alternatively, computing each matrix's positive-definiteness criterion by one symmetric elimination, rejecting zero or negative pivots, gives the same bound. Monic solves, moment pairings, native decoding and observability/control construction fit $O(n^4)$ as in Proposition 8.3, with all guards included. Determinants or the characteristic polynomial can be computed by elimination or the tridiagonal continuant; permutation enumeration is unnecessary. Generating and checking at most $4n$ free values takes $O(n^2)$ field operations. Each of the at most $n-1$ candidate links needs two finite integer-root tests. Propagating its bounded preparation/passive suffix and its predictor also fits the same arithmetic bound. A failed prefix costs at most the complete bounded calculation. Summing $O(n^4)$ and $O(n)$ over $n\le m$ gives the asserted bounds.

For finiteness of widths on exceptional tapes, the smaller true-cap width estimate (UFS.23) is not used. In particular a false extrapolated value need not have a true-response denominator. Instead use the elementary height estimate for exact rational operations. If the existing operand widths are at most $h\ge1$, addition, subtraction, multiplication, division by a tested nonzero value, gcd/lcm and their unreduced cross-products have widths at most $4h+4$. Reduction does not increase widths. Integer floor-root extraction and squaring checks use widths bounded by a constant multiple of their input widths. These estimates also cover rejected tests and the actual source's additions and multiplications.

The original source words have widths at most $B+X$. Each new random integer has width at most $k_N+1\le b+N+\lceil\log_2(N+1)\rceil+1$. Apart from bit copying/counters, all later rational words are obtained from those words and fixed small constants by the stated operations. The observer uses $O(N^5)$ such operations because $m\le N$. The source uses $O(NJ+A)=O(N^3)$ of them by Proposition 14.2. Increasing an absolute constant $c$ absorbs fixed factors and root-test intermediate widths into at most $c(N+1)^5$ height-growth steps, each bounded by multiplication by $8$. This proves (UFS.36). It allows bad candidate pulses to increase all later source widths; none has been omitted or bounded using a fictitious rollback.

School integer multiplication/division at width $O(W_\rho)$ takes $O(W_\rho^2)$ bit steps. Euclidean reduction and binary-search integer square roots each admit the safe $O(W_\rho^3)$ bound. The preceding arithmetic counts, Proposition 14.4's source work, $K_m$ bit assembly, and actual I/O therefore give (UFS.37). The generosity of (UFS.36) makes no assumption that these widths are public or actually attained. It is a proof envelope; (UFS.37) charges actual widths. $\square$

**Proposition 15.3 (one coexisting layout).** A single attained layout can keep all the following on every tape. Numerical words have their actual widths bounded by $W_\rho$; an archive's framing and any separate copy are additional material.

| Coexisting component | Sufficient charge |
| --- | --- |
| Actual specimen | $N$ cells, $N-1$ links, true $B$-bit coefficients, and two state buffers of $O(NW_\rho)$ bits. |
| Complete actual startup record | Every command, transmitted pulse, scalar return and acknowledgement, including rejected attempts: $O(m^2W_\rho)$ numerical bits plus actual framing/indexing. No failed branch is erased from this record. |
| Randomness material | The $K_m$ consumed bits if retained, the current amplitude/cursor, actual $G_{\rm live}$, randomness access/independence assurance and backing. A separate retained bit copy is charged separately. |
| Detector and candidate arrays | A constant number of at most $(m+1)$-row rational arrays, including elimination/pivot scratch, free/impulse windows, observability/control matrices: $O(m^2W_\rho)$ bits. |
| Law, predictor and preparation | Candidate/native coefficients, $q,\mu,F$, a constant number of native/predictive vectors, the computed pulse list and progress: $O(m^2W_\rho)$ bits suffices concurrently with the arrays. |
| Four exported views | Their actual separate encodings. At acceptance their prescribed numerical data take $O(mW_\rho)$ bits; Time has $2d+1$ actual entries. Extra export, delivery or future Time-list copies are added. |
| Program, counters and access | The actual finite program, $b$ and expanding stage/call counters, serialization buffers, root/source reference, Read/Tick/Hold/signed-Add rights, exclusive control, class/fixedness assurance and all storage/control backing. |

Thus one simultaneous numerical-store allowance is

$$
O\!\left(B+(N+m^2)W_\rho+K_m+\log_2(b+1)\right),
\tag{UFS.38}
$$

plus actual framing, generator/program/access representations, additional output/archive copies and their backing. The generator and source work in (UFS.37) belongs to this same run and layout. Shared material is counted once only if actually shared.

Proof. Retain the full actual record, while reusing only the local arithmetic arrays after a rejection. Their maximum dimension is $m+1$, and every candidate has $d\le m$. The listed constant number of arrays and vectors supports the bounded algorithms of Proposition 15.2; no array indexed by an unbounded unknown order or by all candidate histories is allocated. The two source buffers coexist with them and use the physical $N$, not a false candidate's $d$. The bit store, current random amplitude, accepted predictor and its actual passive segment also coexist. Adding these numerical stores gives (UFS.38), with all extra copies and supplied material explicitly added. No numeric state or source reference creates the missing call or random-generation rights. $\square$

**Proposition 15.4 (the confidence parameter does not bound literal memory).** Fixed $b$ and $N$ give no bound on required startup widths independent of $B,X$, and no bound on all later literal output widths or retained Time material.

Proof. Already for $N=1$, $T=(1/2)$ and entry $x^{\rm in}=M\in\mathbb Z$, the first gate Read is $M+U_1$. The finite random amplitude range for fixed $b$ cannot bound its width as $M$ varies. After successful preparation, the passive outputs $2^{-k}$ have denominator width $k+1$. These are the same exact serialization and growing-record boundaries as Proposition 8.5 and P Proposition 41.5. Neither high confidence nor finite program/order changes them. $\square$

## 16. Supplier correspondence and the exact remaining boundaries

**Definition 16.1 (mathematical source correspondence).** The repository suppliers in this correspondence are interpreted at the public revision `f47bca550530488dc21a7a4443c14166932452e3`, with the following hypothesis correspondence.

| Supplier | Exact supplied content and subtraction |
| --- | --- |
| This volume, §§1–6 and 8 | The rational unknown-field service, signed visible-rank argument, capped free-response certificate, impulse subtraction, native decode, true advanced-cut predictor, executed controllability solve, earned unit origin and paid P39 entry are reused. The branch's correctness under a true trial cap is exactly these results. Their old counts are unchanged. |
| This volume, §7 | The uncapped deterministic exact obstruction includes arbitrary finite adaptive signed Adds and returning Ticks on the same positive contracting path class. It is retained with its exact all-source deterministic contract. It does not supply a fixed-specimen randomized obstruction. |
| [P §§36–41][P] | The same native positive-link Jacobi matrix gives cyclic root columns and positive impulse Gram blocks. Native reconstruction, observability, all-field predictive updates, the original passive four-view domain and source arithmetic are supplied. Unknown entry fields and random gates do not inherit the authentic-origin premise until actual preparation has earned it. |
| [P §§52–58][P] | The no-retained-length integer-pulse inverse starts from the authentically prepared and already acquired source with its earned law and origin. It supplies neither the unknown-field randomized gate nor hidden-order advice. Its integer-word, origin, diagnostic-advance, journal and resource boundaries remain exact; no such history inverse is applied to this startup's arbitrary rational preparation journal. |
| [FiniteAtomicHankelVandermonde][HVD] and its [Scribe][HVDs] | `hankel_moment_matrix_factorization` supplies finite signed atomic factorization, not early signed-block positivity or an upper order certificate. Lemma 10.3's positive leading coefficient is supplied instead by the actual impulse Gram matrix and native triangularity. |
| [FiniteHoKalmanBlocks][HK] and its [Scribe][HKs] | `sample_factorizations` and `finite_samples_exact_recovery` retain their explicit reference-order hypothesis; `finite_samples_order_lower_bound` is a lower bound only. The new trial procedure does not turn either into a finite-data hidden-order certificate. |
| [CoefficientDrivenJacobiCharacteristicPolynomial][JAC] and its [Scribe][JACs] | The original native decode uses its coefficient multiplication, Gram--Schmidt and characteristic-polynomial results, including private `orthogonal_power_basis_monic`, `orthogonal_power_basis_upper_zero`, `squared_norm_pos` and Jacobi-entry/tridiagonal helpers. These are covered suppliers, not new lemmas here. |
| [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) and its [Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs) | Use state $\mathbb R^N$, output $\mathbb R$, update $T$, readout $e_0^{\mathsf T}$ and horizon $N$. P's native Krylov triangularity supplies the nonsingular observation map; the paid branch prefix supplies its actual right-hand side. |
| [Teschl, §2.5][Teschl], equations (2.109)–(2.118), printed pp. 42–43, with the finite-support paragraph on p. 44 | These own moment orthogonalization and positive Jacobi reconstruction. Here $C(N+1)=\det H_N=0$ is justified for extracted true impulse moments at a true cap. Theorem 2.13's nonfinite-support hypothesis is not imposed on a finite specimen, and its inverse theory does not certify an early signed gate. |
| [Pinned mathlib, polynomial roots](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Polynomial/Roots.lean) | `Polynomial.card_roots'`, `Polynomial.card_le_degree_of_subset_roots` and `Polynomial.mem_roots` give the mature univariate root-count step for the nonzero rational polynomial $D_{n,z}$. The conditional sampling and summable error allocation use ordinary finite probability and the union bound. None of these general algebraic/probability facts is asserted as a new theorem. |

The additional source-relative content is the actual-field determinant gate with a positive impulse leading coefficient, its independent summable confidence allocation, the total guarded capped branch on false hypotheses, and their combination into every-tape termination by stage $N$ with one joint correctness event and the same-run accounts above. This is a construction for this declared service and changed correctness contract, not an assertion of worldwide priority for randomized rank tests, inverse Jacobi theory or finite linear control.

**Definition 16.2 (scope of the new result).** The continuing limitations are part of the stated domain. Exact rational serialization, installed class/fixedness/root assurance, arbitrary signed input rights, effective Hold, successful serial calls, retained backing and independent fair bits are premises; physical authenticity is not acquired by the probability calculation. The result gives no noisy or finite-resolution instrument, zero-error uncapped identification, all-source correctness on one tape, bounded-energy lower bound, optimal horizon, minimum total resource claim, recovery of erased chronology, or all-controlled-history four-view equivalence. The passive P39 statement applies after the actual new unit origin and its actual paid suffix, while complete prediction has the larger original action domain.

No correspondence with native $\alpha/\beta$ constructors, universal generator pair, original fixed-$G_{\rm gc}$/original-$Q$ apparatus, parked consumer, or arbitrary graph/physical geometry is supplied. Such a correspondence still requires its own common-source initialization, operation/output transport, acquisition and retained-right/resource bridge. This bounded stochastic startup theorem leaves those original obligations and the full four-expression programme in their original scopes.

## 追加锚（本行以下为增补区）

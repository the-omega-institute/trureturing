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

## 17. An actual nonnegative root-pulse producer without order advice

**Definition 17.1 (the positive-history entrance class).** Let $N\ge1$ be arbitrary and unknown, and let $T$ be any rational native rooted Jacobi matrix satisfying (UFS.1). On this same fixed specimen an actual producer starts with every cell zero. It executes a finite serial word of Tick and Add commands, with every producer input a nonnegative rational. Read and Hold may be interspersed. There are no other field inputs or uncommanded Ticks. If the word contains $J_{\rm p}$ Ticks, and its $A_{\rm p}$ Adds have inputs $c_l\ge0$ at Tick epochs $s_l\le J_{\rm p}$, its actual handover field is

$$
x^{\rm in}=p(T)e_0,\qquad
p(z)=\sum_{l=1}^{A_{\rm p}}c_lz^{J_{\rm p}-s_l}
\in\mathbb Q_{\ge0}[z].
\tag{UFS.39}
$$

Here $\mathbb Q_{\ge0}[z]$ means polynomials whose coefficients are nonnegative rationals, including the zero polynomial. Several Adds at one epoch contribute separate actual operations and may combine in $p$. The producer's zero initialization is an actual preparation with its own work and backing. It is not a Reset port available to the receiving observer. Every producer Tick emits the updated root scalar; every producer Read emits its root scalar; Add and Hold emit their fixed acknowledgements. All are real outputs to the producer, whether or not their archive survives handover. An archive, when retained, is separate material.

Formula (UFS.39) follows by induction from the actual zero field: an Add appends $c_le_0$, and a later Tick multiplies every extant term by $T$. Read and Hold change neither field nor exponent. The formula describes the endpoint of the executed word, not a list supplied to the receiver.

**Assumption 17.2 (common-source handover and receiving service).** The receiver is supplied assurance of Definition 17.1's actual initialization and producer restriction, the same bound root and fixed law, and precisely Assumption 1.2's serial Read, returning Tick, Hold and arbitrary signed rational Add service. In particular, after handover the receiver may use negative as well as nonnegative inputs. Exact rational serialization, successful calls, exclusive access, effective Hold, references, call/input rights, class/fixedness assurance and sufficient finite storage/control backing remain installed premises. Handover permits no hidden Tick, field replacement, rebinding or law change.

The producer word, $p$, its degree and coefficients, $J_{\rm p},A_{\rm p},N,T,x^{\rm in}$, coefficient lengths and all upper bounds on them are not receiver inputs. There is no order cap, random-bit source, response table, coefficient or size port, clone, Reset, or size/work/timing side channel. The initialization assurance is not inferred from a finite root transcript. Both the producer's actual resources and the receiver's subsequent resources are charged on this one specimen. Physical conformance to these exact digital-service premises is `ASSUMED-UNVERIFIED`.

**Definition 17.3 (uniformity and the two responses).** A receiver is one finite effective program independent of the hidden source and producer, with finite growing stores on each completed run. This does not mean a finite-state controller or bounded lifetime memory. Put

$$
C=I+p(T),\qquad b=x^{\rm in}+e_0=Ce_0,\qquad
y_j=e_0^{\mathsf T}T^jb,\qquad
m_j=e_0^{\mathsf T}T^je_0.
\tag{UFS.40}
$$

The $y_j$ become actual paid observations after a first receiver Add$(1)$. The $m_j$ are the native impulse moments; they are initially mathematical quantities. Neither is an initially supplied array. The letter $C$ denotes a matrix used in the proof; it is not given to, computed by, or queried by the receiver.

## 18. The producer restriction earns a deterministic stopping certificate

**Theorem 18.1 (positive-history order acquisition and full first-response recurrence).** For every entrance satisfying Definitions 17.1–17.3 and Assumption 17.2, the following deterministic receiver stops its first stage after exactly $2N$ actual Ticks. Hold, execute Add$(1)$, and Read $y_0$. For $n=1,2,\ldots$, execute two returning Ticks, retain $y_{2n-1},y_{2n}$, then Hold and test

$$
Y_n=(y_{i+j})_{0\le i,j\le n}
\tag{UFS.41}
$$

for singularity by exact rational elimination. Stop at the first singular block. Its index is the actual $N$, its preceding block $Y_{N-1}$ is positive definite, and the actual field at this cut is $T^{2N}b$. From this paid prefix the receiver computes the characteristic polynomial of the native $T$ and a recurrence generating every $y_j$, without obtaining the native coefficients from $Y_n$.

Proof. Every eigenvalue $\lambda$ of $T$ lies in $(0,1)$. Since $p$ has nonnegative coefficients, $1+p(\lambda)\ge1$. The finite spectral theorem therefore gives $C\ge I>0$. Also $C$ is symmetric and commutes with $T$, because it is a polynomial in $T$. This uses the producer restriction on the whole spectrum; it does not follow from coordinate signs of $x^{\rm in}$.

For P Lemma 37.1's native columns $K_n=[e_0,Te_0,\ldots,T^ne_0]$, symmetry and commutation give the exact identity

$$
Y_n=K_n^{\mathsf T}C K_n.
\tag{UFS.42}
$$

That lemma supplies independence of these columns for $n<N$, and invertibility of $K_{N-1}$. Positive definiteness of $C$ then makes $Y_n$ positive definite for every $n<N$. At $n=N$ the columns span $\mathbb R^N$ but are dependent. Consequently $Y_N$ has rank $N$ and is singular, while $Y_{N-1}>0$. This proves the stopping claim, including $N=1$, when $Y_0=(y_0)$ is strictly positive. Each acquired block uses only the observations already emitted through epoch $2n$. No source-dependent search bound is needed.

With this earned $N$, solve the nonsingular rational system

$$
Y_{N-1}(q_0,\ldots,q_{N-1})^{\mathsf T}
=-(y_N,\ldots,y_{2N-1})^{\mathsf T},\qquad
q(z)=z^N+\sum_{j<N}q_jz^j.
\tag{UFS.43}
$$

Its equations are $K_{N-1}^{\mathsf T}Cq(T)e_0=0$. Both square factors $K_{N-1}^{\mathsf T}$ and $C$ are invertible, so $q(T)e_0=0$. Polynomial commutation then makes $q(T)$ vanish on every $T^je_0$, $j<N$, hence on a basis. Thus $q(T)=0$. No nonzero polynomial of degree below $N$ can annihilate $e_0$, by native triangularity. Cayley--Hamilton and subtraction of two monic degree-$N$ annihilators now identify $q=\det(zI-T)$. This is the same characteristic/companion algebra as P Proposition 37.4, with the invertible weighted form supplying its orthogonality equations here.

For every $s\ge0$, multiplication by $e_0^{\mathsf T}T^s$ and by $b$ gives

$$
y_{s+N}=-\sum_{j<N}q_jy_{s+j}.
\tag{UFS.44}
$$

The first $N$ actual values and rational coefficients generate the entire sequence effectively. Its least all-shift recurrence degree is also $N$: a lower-degree recurrence polynomial $r$ would imply $K_{N-1}^{\mathsf T}Cr(T)e_0=0$, hence $r(T)e_0=0$, a contradiction. Local processing takes place during the issued Holds, so the stopped physical field is exactly $T^{2N}b$. $\square$

**Definition 18.2 (the weighted/native distinction).** Theorem 18.1 earns the order and recurrence of the first actual response. Its moment pairing is $\langle f,g\rangle_y=(f(T)e_0)^{\mathsf T}C(g(T)e_0)$, whereas native impulse orthogonalization uses the ordinary Euclidean pairing $\langle f,g\rangle_m=(f(T)e_0)^{\mathsf T}(g(T)e_0)$. The first form is positive and has the full native order, but does not identify its orthogonal vectors with native cells. In particular $y_0$ need not equal $1$. The native reconstruction below uses extracted $m_j$, not $y_j$ or $y_j/y_0$.

## 19. A second real pulse earns the native law and actual current field

**Theorem 19.1 (deterministic uncapped native startup).** Under Assumption 17.2, one uniform deterministic receiver terminates on every finite positive-history entrance with the exact $N,T$, native impulse law, and actual native field at its stopping cut. After Theorem 18.1 it uses one further Add$(1)$, one Read and exactly $2N-1$ further returning Ticks, followed by a Hold. Its actual stopped field is

$$
x_*=T^{4N-1}(x^{\rm in}+e_0)+T^{2N-1}e_0.
\tag{UFS.45}
$$

Proof. At the first held cut the actual field is $z=T^{2N}b$. Execute the second Add$(1)$ and Read $v_0$. Retain every return of the next $2N-1$ Ticks as $v_1,\ldots,v_{2N-1}$. The command semantics on this same specimen give

$$
w=z+e_0,\qquad
v_j=e_0^{\mathsf T}T^jw=y_{2N+j}+m_j
\quad(0\le j\le2N-1).
\tag{UFS.46}
$$

Using (UFS.44), generate the finite missing portion of $y$ through index $4N-1$. Subtract the generated $y_{2N+j}$ from each paid $v_j$. Equation (UFS.46) proves that these arithmetic differences are exactly the native $m_0,\ldots,m_{2N-1}$, with $m_0=1$. They are neither a new chosen-index response port nor a second specimen.

P Proposition 37.3 explicitly recovers all native coefficients from impulse moments through $2N-1$. Its additional moment $m_{2N}$ is needed there for unknown-order termination, not coefficient decoding; here Theorem 18.1 has already earned the true order. Thus the available extracted prefix meets its decoding hypotheses. Apply its monic impulse orthogonalization and positive norm-ratio formulas (UFS.10). The identity $p_j(T)e_0=\beta_je_j$ in that supplier fixes the actual rooted cells and positive link orientations. Every required positive rational square root is computed by finite integer roots of the reduced numerator and denominator, with exact squaring checks, as in P Proposition 37.3. No real-number root oracle or arbitrary similarity gauge is used. The resulting exact $T$ and $q$ generate all impulse moments and the finite rational transfer $F_T$ by P Proposition 37.4.

Form $\mathcal O_N=K_{N-1}^{\mathsf T}$, as in (UFS.11), using this recovered native $T$, and solve

$$
\mathcal O_N\widehat w=(v_0,\ldots,v_{N-1})^{\mathsf T},\qquad
\widehat x_*=T^{2N-1}\widehat w.
\tag{UFS.47}
$$

Invertibility is P Lemma 37.1's native triangularity. The right-hand side contains the first $N$ observations from the actual $w$ in (UFS.46), so $\widehat w=w$. The source has executed exactly $2N-1$ further Ticks since that cut. Consequently $\widehat x_*=x_*=T^{2N-1}w$, which is (UFS.45). Keep the final Hold during decoding, this solve and record installation. Each elimination, recurrence generation and promised rational-root calculation is finite, and the only unbounded search was the first-stage loop already proved to stop at $N$. All receiver decisions use paid outputs and local calculations; none uses $p$ or producer advice. $\square$

**Theorem 19.2 (complete continued use from the earned cut).** Retain Definition 4.1's same-source record with the $T,q,\mu=(m_0,\ldots,m_{N-1})$ earned above, $\widehat x=x_*$, and $a=\mathcal O_Nx_*$. Retain the actual root reference, signed input/call rights and backing separately. For every legal finite common adaptive continuation in the full Read/Tick/Hold/Add menu, this record predicts every declared output and the complete native successor. At each completed cut,

$$
\widehat x=x_{\rm actual},\qquad a=\mathcal O_Nx_{\rm actual}.
\tag{UFS.48}
$$

Proof. Theorem 19.1 establishes both identities at installation. Apply the existing updates of Definition 4.1. For any current rational $x$, not only a positive-history field, $q(T)=0$ makes $\mathcal O_NTx$ the shift/recurrence update of $a$. Also $(\mathcal O_Ne_0)_j=m_j$, so an actual Add$(u)$ and its numerical update both add $u\mu$ to $a$ and $ue_0$ to the native vector. Read returns the unchanged $a_0$. Tick returns the updated $a_0$, and Add and Hold return exactly their fixed acknowledgements. Hold and Read preserve both state identities.

These are precisely Theorem 4.2's all-field one-operation identities, now initialized by (UFS.45)–(UFS.47). Induction over a common adaptive policy makes equal earlier outputs give the same next command, rational input and stopping decision, and the identities preserve the complete outputs and successors. Arbitrary authorized signed inputs are included. Local scratch forecasts issue no source commands; real calls still require their retained rights, perform their actual state updates and retain their real returns. Serialization commits the corresponding record update before the next completed cut. Thus the universal continuation claim is earned at the actual advanced field, even when later signed controls leave the positive-history class. $\square$

## 20. Paid entrance to the supplied four-expression passive domain

**Definition 20.1 (one real unit origin and independent views).** From the held cut of Theorem 19.1, keep the same specimen and use Theorem 5.1's control construction with its newly earned $T,x_*$. Namely compute the rational $u$ from

$$
[T^{N-1}e_0,\ldots,e_0]u=e_0-T^Nx_*.
\tag{UFS.49}
$$

Execute $N$ pairs Tick; Add$(u_j)$ in their specified order, including zero inputs, and retain every Tick scalar and acknowledgement. Issue a Hold after each pair. Call the final held cut $o$. Read its actual root and then execute $k\ge2N$ further actual passive Ticks with no Add. The four views at that segment's endpoint are exactly Definition 6.1's data: Space is $(T,x)$ in native rooted cells; Time is the paid ordered root list from $o$ through these $k$ Ticks; Boundary is $(F_T,x_0)$; Memory is $(q,\mu,a)$ with $a_j=e_0^{\mathsf T}T^jx$ for $j<N$.

These meanings precede the recovery maps. Space exposes current cells and adjacency; Time exposes a specified actual scalar segment and order; Boundary exposes a port law and present endpoint; Memory exposes a least recurrence and present sufficient predictive state. None includes an unrestricted producer or control history. Their numerical data do not include the separately retained reference, rights or source assurance. The actual origin and common-source installation are shared contextual premises.

**Theorem 20.2 (actual four-view entry, all recoveries and passive transport).** For every positive-history entrance in Assumption 17.2, the operations of Definition 20.1 actually prepare $e_0$ at $o$ and then reach P Definition 39.1's domain with current state $x=T^ke_0$. On that domain every view recovers the same $(T,k,x)$, hence every other view; all recovery routes agree and commute with actual passive Tick. This consumes P's existing four-view theorem, with a paid entrance earned by Theorems 18.1–19.2.

Proof. The reversed native Krylov matrix in (UFS.49) is invertible. After the first $j$ actual Tick/Add pairs the field is

$$
x_j=T^jx_*+\sum_{l<j}u_lT^{j-1-l}e_0.
$$

At $j=N$, (UFS.49) gives $x_N=e_0$. This is exactly Theorem 5.1's actual preparation proof; it uses only the known native law and current field, both earned here. Theorem 19.2 predicts and retains every intermediate Tick return, including outputs before a pair's Add. Thereafter the actual passive field is $T^ke_0$, and the origin Read and all $k$ Tick returns are exactly $(m_0,\ldots,m_k)$. Thus the full actual-source and paid-list hypotheses of P39 hold, rather than merely a numerical recurrence matching a unit orbit.

For explicit recovery correspondence, Time's length gives $k$; its first flat impulse block gives $N$, and P37 gives the native $T$. Boundary's finite transfer generates native moments locally, thereby recovering $T$; its present root identifies $k$. Memory's least recurrence degree gives $N$, and its initial values and recurrence generate the same native moments, thereby recovering $T$; its first predictive entry identifies $k$, and $\mathcal O_N^{-1}a$ is the current native $x$. Space already exposes $T,x$ and uses its present root to identify $k$. Each phase inversion terminates on the stated actual image because P Lemma 39.2 gives $1=m_0>m_1>\cdots>0$. There is no terminating off-image recognition claim.

Each route therefore recovers the unique same $(T,k,T^ke_0)$. Re-forming any target view from that triple gives the direct result, as in P Propositions 39.3–39.4. In particular a reconstructed numerical Time list equals this already paid list, without creating provenance for an unexecuted segment. Actual passive Tick sends the triple to $(T,k+1,Tx)$, appends its real root to Time, keeps $F_T$ and updates Boundary's present root, and shifts Memory with its last entry supplied by $q(T)=0$. Read and Hold preserve the passive epoch. These updates agree under every recovery route. A later Add remains correctly predicted by Theorem 19.2, but does not inherit this passive-domain claim for arbitrary controlled journals. $\square$

## 21. One attained schedule including the actual producer

**Definition 21.1 (receiver schedule and cost coordinates).** Use one initial Hold before the first receiver Add$(1)$ and Read. Issue one Hold after each of the $N$ first-stage Tick pairs, and one after the $2N-1$ second-stage Ticks. The last first-stage Hold covers the recurrence solve; the second-stage final Hold covers native decoding, synchronization, predictor installation and the preparation solve. For preparation issue one Hold after each of its $N$ Tick/Add pairs; its last held interval covers the new-origin Read. For passive entry choose $k=2N$ and issue one Hold after each passive Tick pair. An existing Hold ends before the next commanded field change. Redundant Holds in this specified schedule are executed and charged.

Use Convention 8.1's literal reduced rational encoding and actual framing for all commands, inputs, outputs and acknowledgements. Acknowledgements are separate frames, not rational scalar values. Work, literal bits, simultaneous material, initial preparation, rights and backing are separate cost coordinates, not one unit-cost real arithmetic budget.

**Theorem 21.2 (exact receiver traffic on this one run).** The schedule of Definition 21.1 has the following attained counts, without producer commands included in either column.

| Coordinate | Through native startup and predictor installation | Through actual unit preparation and the paid $k=2N$ passive cut |
| --- | --- | --- |
| Returning Ticks | $4N-1$ | $7N-1$ |
| Adds | $2$ | $N+2$ |
| Reads | $2$ | $3$ |
| Explicit Holds | $N+2$ | $3N+2$ |
| Scalar returns, every Read and Tick | $4N+1$ | $7N+2$ |
| Fixed Add/Hold acknowledgements | $N+4$ | $4N+4$ |
| Total calls and complete return frames | $5N+5$ | $11N+6$ |
| Random bits | $0$ | $0$ |

Proof. First-stage and second-stage Tick counts are respectively $2N$ and $2N-1$. Each stage has one Add and one Read. Its Holds are the initial one, the $N$ first-stage pair Holds and the final second-stage Hold. Preparation adds $N$ Ticks, $N$ Adds and $N$ Holds, including the prescribed Add$(0)$ whenever a computed input vanishes. Passive entry adds one origin Read, $2N$ Ticks and $N$ Holds. Summing gives the first four rows. Each Tick and Read returns one scalar; each Add and Hold returns one acknowledgement. Their sum is also the number of calls. Every operation is deterministic. $\square$

**Theorem 21.3 (producer and direct-source charges).** Let the actual producer also have $R_{\rm p}$ Reads and $H_{\rm p}$ Holds. End-to-end through the right-hand column of Theorem 21.2, define

$$
J=J_{\rm p}+7N-1,\quad A=A_{\rm p}+N+2,\quad
R=R_{\rm p}+3,\quad H=H_{\rm p}+3N+2.
\tag{UFS.50}
$$

These are the actual respective operation counts. There are $J+R$ scalar returns, $A+H$ fixed acknowledgements, $J+A+R+H$ service calls and $A$ transmitted pulse rationals. Producer zero initialization, source construction, assurance, reference/grant setup and actual retained producer material are additional charges. The direct simultaneous-buffer path update of P Proposition 41.2 performs

$$
J(3N-2)\ \text{rational multiplications},\qquad
J(2N-2)+A\ \text{rational additions},
\tag{UFS.51}
$$

with $NJ$ destination-cell writes, in addition to initialization and all decoding, Read, Hold, framing and control work. There is no bound on the producer coordinates in (UFS.50) from $N$ alone.

Proof. The producer and receiver act consecutively on the same actual $N$-cell source. Each Tick, including a producer Tick, has P41.2's $3N-2$ products and $2N-2$ additions; every Add has one actual root addition. Every destination cell is written in a simultaneous-buffer update. Initial zeroing writes all $N$ cells; any additional buffer initialization or coefficient/source installation has its actual further cost. The producer's scalar and acknowledgement semantics are those of Definition 17.1, giving the complete traffic sums. Optional surviving archives are counted rather than assumed to vanish or given to the receiver for free. Finally arbitrarily many producer zero Adds or Ticks from zero preserve an admitted endpoint, so producer command counts have no $N$-only upper bound. Their actual emitted frames and work remain charged even when endpoints coincide. $\square$

**Theorem 21.4 (finite attained computation and simultaneous material).** There is one exact receiver realization of the preceding schedule using $O(N^4)$ rational arithmetic/gcd/lcm/comparison operations, $N-1$ positive rational-square-root extractions, and $O(N^2)$ numerical workspace. These counts include block testing, recurrence extension, native decoding, current-field and control solves, predictor installation, actual preparation tracking and the $2N$ passive segment. Literal widths and all source work remain paid.

More precisely, let $W\ge1$ be the maximum actual integer/rational word width, including intermediate numerators and denominators, on the whole chosen finite producer/receiver run. Include binary counter widths in $W$. Let $L_{\rm io}$ be all actual traffic and output bits, including framing, producer traffic, transmitted controls and separately materialized copies. Let $G_{\rm p}^{\rm ctl}$ be producer controller work apart from the direct source arithmetic in (UFS.51), and let $I_{\rm work}$ be actual remaining setup, access and backing work. One conservative attained bit-work allowance is

$$
O\!\left([N^4+NJ+A]W^3+L_{\rm io}\right)
+G_{\rm p}^{\rm ctl}+I_{\rm work}.
\tag{UFS.52}
$$

One coexisting layout has numerical material $O(B+N^2W)$, where $B$ is the actual coefficient-store length, plus actual producer material, actual framing and extra journal/export copies, program, reference, rights, assurance and storage/control backing. These quantities refer to this same execution. They are not public input bounds or lifetime bounds.

Proof. A cubic exact elimination for each block $Y_n$, $1\le n\le N$, costs $O(\sum_{n\le N}(n+1)^3)=O(N^4)$ operations. The receiver grows arrays as observations arrive, without allocating by an unknown cap. The one recurrence solve is cubic. Extending $y$ through $4N-1$ costs $O(N^2)$ operations. Apply the existing native impulse orthogonality solves and norm pairings separately in degree order; their total is $O(N^4)$, as in P Proposition 41.3. There are exactly $N-1$ positive link roots, each obtained by finite integer-root extraction and exact tests on numerator and denominator. Sparse powers construct the observation/control matrices and current vectors in at most cubic further arithmetic, their nonsingular solves are cubic, and transfer continuants also fit that allowance. Updating native/predictive vectors during the remaining $O(N)$ receiver commands fits $O(N^2)$ further operations. No producer history search or polynomial $p$ reconstruction is performed.

All observed rationals are finite because the actual producer word and each source are finite. All subsequent receiver arithmetic has finitely many rational operands, all divisions have the proved nonzero denominators, and integer-root algorithms terminate. Thus $W$ is finite on every admitted run, without knowing it in advance. School integer arithmetic, Euclidean reduction and binary-search integer square roots admit a conservative $O(W^3)$ bit cost per indicated arithmetic/root operation. This gives the receiver term $O(N^4W^3)$, including its $O(N)$ roots. Equation (UFS.51), cell writes and source Add work fit $O((NJ+A)W^3)$; all remaining producer-controller, setup/control and literal traffic work is explicitly added in (UFS.52).

For simultaneous material, retain a constant number of $O(N^2)$-word arrays for elimination, polynomial, observation and control calculations, reusing scratch after its result is retained. Keep the $O(N)$ actual receiver scalar returns, the $O(N)$-command/pulse/acknowledgement journal, $T,q,\mu$, native and predictive vectors, the control list, counters, parsing and communication buffers. These coexist with the source coefficients and both actual $N$-word state buffers; they fit $O(B+N^2W)$ numerical bits. Actual framing, separately retained archives or exports, the surviving producer store and all program/access/backing resources are added. A producer journal is neither an invisible receiver input nor a compulsory field in each view. Later actual continuations and longer materialized Time lists pay their own additional work and storage. $\square$

## 22. Exact boundaries of positivity, weighting and old chronology

**Proposition 22.1 (coordinatewise nonnegativity does not certify the stopping test).** Replacing Definition 17.1 by the weaker condition $x^{\rm in}\ge0$ coordinatewise invalidates Theorem 18.1's order certificate, even on a two-cell rational positive contracting Jacobi path.

Proof. Take

$$
T=\begin{pmatrix}1/2&1/8\\1/8&1/2\end{pmatrix},\qquad
x^{\rm in}=e_1.
$$

Its eigenvalues are $3/8,5/8$, so $0<T<I$ and the link is positive. The first Add$(1)$ makes the actual field $(1,1)^{\mathsf T}$, an eigenvector with eigenvalue $5/8$. Thus its root response is $y_j=(5/8)^j$, and $Y_1$ is singular with $Y_0=(1)>0$, although the actual order is two.

This field is not a hidden counterexample to Definition 17.1. On this $T$, every native impulse moment $m_j$ is positive. If $p$ has nonnegative coefficients and $e_0^{\mathsf T}p(T)e_0=0$, every coefficient is zero. Therefore $p(T)e_0=e_1$, whose root coordinate is zero but which is nonzero, is impossible. The failed weakened premise allows spectral cancellation that the positive-history $C>0$ proof excludes. This counterexample invalidates that stopping test under coordinate signs alone; it asserts no impossibility theorem for every other nonnegative-field procedure. $\square$

**Proposition 22.2 (positive weighted moments are not native impulse data).** Even on the positive-history class, normalizing the first response by $y_0$ and applying native moment decoding need not recover the original native law.

Proof. For any admitted $N\ge2$, let the actual producer execute Add$(1)$; Tick from zero. Then $p(z)=z$ and $y_j=m_j+m_{j+1}$. Since $m_1=a_0$ and $m_2=a_0^2+b_0^2$, the first diagonal coefficient obtained from normalized weighted moments is

$$
\frac{y_1}{y_0}-a_0
=\frac{m_2-m_1^2}{1+m_1}
=\frac{b_0^2}{1+a_0}>0.
$$

It differs from the actual root diagonal. The first response has full order and a valid positive measure, but that measure has reweighted the native root spectrum. The second pulse in Theorem 19.1 removes this unknown weight by (UFS.46) before native decoding. Its schedule is sufficient, without an assertion that two pulses are necessary for every alternative protocol. $\square$

**Proposition 22.3 (entry state does not identify the producer word or old age).** Positive-history startup and subsequent complete prediction do not recover an erased producer journal or pre-handover Tick chronology.

Proof. On the one-cell specimen $T=(1/2)$ compare two producers from zero: Add$(1)$; Tick, and Add$(1/2)$. Both satisfy Definition 17.1 and hand over the same field $1/2$, but their earlier Tick counts differ. Their earlier output histories also differ; those histories are not receiver inputs. Starting at handover, the same actual $T,x^{\rm in}$ and common commands give identical complete successors and declared outputs, by the service laws. A deterministic receiver therefore cannot distinguish these two old histories from subsequent outputs. Splitting an Add into two nonnegative Adds at the same epoch gives further identical endpoints with different old pulse counts. The new origin $o$ in Definition 20.1 records a genuinely executed preparation, not an inverse of those erased histories. $\square$

**Proposition 22.4 (finite order does not bound widths or preparation inputs).** Positive-history initialization gives no $N$-only bound on receiver scalar widths, required signed preparation amplitudes or all later literal memory.

Proof. With $N=1$, $T=(1/2)$, let the producer use Add$(M)$ from zero for an arbitrary nonnegative integer $M$. The first receiver Read after Add$(1)$ is $M+1$. Theorem 19.1's stopped field and the one-pair preparation input are respectively

$$
x_*=(M+5)/8,\qquad u_0=1-\tfrac12x_*=(11-M)/16.
$$

Their widths, and the absolute preparation input, are unbounded as $M$ grows. The initial nonnegative producer restriction does not remove the receiver's need for its supplied signed Add right. After actual unit preparation, the passive root $2^{-k}$ has denominator width $k+1$; materializing the paid Time list also grows with $k$. All such finite continuations remain correctly predicted, with their actual width and backing costs. $\square$

## 23. Supplier correspondence and the remaining recovery domain

**Definition 23.1 (mathematical suppliers and subtraction).** Repository references in this section are interpreted at the fixed public revision `4e30bf1cda180366afd2fb93ed9aa13e1e09e8c7`. The following correspondence fixes the supplied mathematics and the source-relative deduction.

| Supplier | Exact correspondence and supplied content |
| --- | --- |
| This volume, Definitions 1.1–1.3 and §§3–6 | The receiving source retains the rational positive-link $0<T<I$ class and complete Read/returning-Tick/Hold/signed-Add service. The capped arbitrary-field acquisition is supplied but is not invoked with an unearned cap. Its all-field predictive identities, native observation solve, executed unit preparation and real passive-entry argument are reused once $T,x_*$ have been earned here. |
| This volume, §7 and §§10–16 | The deterministic no-cap obstruction keeps arbitrary signed initial fields. The randomized construction keeps specimens fixed before independent fair bits, all-tape termination and its confidence-qualified correctness event. Definition 17.1 restricts the actual initializer instead, and Theorems 18.1–19.1 use no randomness. Neither old claim is reclassified or contradicted. |
| [P §§36–41][P] | Native Krylov triangularity is used for $K_n$ and $\mathcal O_N$. Native Jacobi reconstruction is applied only to the extracted $m_j$, whose prefix through $2N-1$ suffices once $N$ is earned. Least impulse recurrence, transfer, complete all-field updates, independent passive views, strict root phase separation and direct source arithmetic are supplied. The first observed $Y_n$ is the different weighted Gram form (UFS.42), not P's unit-impulse transcript. |
| [P §§44–58][P] | The finite/integer pulse-word inverses start after actual unit preparation and native-law acquisition, retain their own menu/origin conditions, and concern their specific controlled word tasks. Definition 17.1 instead precedes native-law acquisition and permits arbitrary finite nonnegative rational producer pulses with no word or length supplied. Those existing inverses are not invoked on this missing producer history. |
| [FiniteAtomicHankelVandermonde][HVD] and its [owning Scribe][HVDs] | `hankel_moment_matrix_factorization` gives the algebraic factorization. Here the spectral nodes are the simple native eigenvalues, and weights are $(1+p(\lambda))|v_\lambda^{\mathsf T}e_0|^2>0$. Native cyclicity and actual producer positivity verify nonvanishing; the identity itself supplies no initializer assurance or observation. The Gram proof in Theorem 18.1 uses the same mature algebra. |
| [FiniteHoKalmanBlocks][HK] and its [owning Scribe][HKs] | `sample_factorizations` applies to scalar Markov samples with update $T$, input $b=Ce_0$, output $e_0^{\mathsf T}$ and prefix parameter $h=N$ after the stopping stage. `finite_samples_exact_recovery` has an explicit matching reference order; `finite_samples_order_lower_bound` alone is not an upper-order certificate. The positive-history first-singular argument earns the missing order premise before any such use. |
| [CoefficientDrivenJacobiCharacteristicPolynomial][JAC] and its [owning Scribe][JACs] | With the native impulse power basis, ordinary Euclidean inner product and self-adjoint multiplication by $T$, the supplied positive coefficient-Hankel/Jacobi result and characteristic-polynomial result apply exactly as in P37. The private monicity, norm-positivity, Jacobi-entry and tridiagonal helpers are supplied proof components. With the weighted $y$ pairing the abstract theorem still concerns that weighted inner product; it cannot silently identify its orthogonal vectors with actual native cells. |
| [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs) | State $\mathbb R^N$, output $\mathbb R$, update $T$, readout $e_0^{\mathsf T}$ and horizon $N$ give the usual stacked observability map. Native triangularity supplies nonsingularity, and the paid second-stage values supply the actual right-hand side (UFS.47). Generic observability is supplied, rather than new. |
| [Pinned mathlib Vandermonde][MV] | `Matrix.det_vandermonde_ne_zero_iff` supplies the distinct-node determinant criterion for the spectral form of the same finite Hankel algebra. Its node-row convention is the transpose of the degree-row features here. No compiled specialization or unknown-source acquisition follows from the determinant identity alone. |
| [Teschl, §2.5][Teschl], equations (2.109)–(2.118), printed pp.42–43, and the finite-support paragraph on p.44 | `literature-attested`: positive moment orthogonalization, Jacobi reconstruction, sign choice and termination after the number of support points are classical. His $C(N+1)=0$ is the $(N+1)$-row flat block. Apply the native reconstruction to $m$; the weighted measure for $y$ has the same number of support points but different weights. Theorem 2.13's nonfinite-support premise is not asserted for this finite matrix. |
| [PG Definition 12.5][PG], and the Kalman/Ho--Kalman references in Correspondence 9.1 | Free/forced response separation, finite realization, observability and controllability are mature suppliers. Here Add and Tick are separate real operations, which fixes the ages in (UFS.39) and (UFS.46). The preparation uses the actual earned state and executed signed controls, not an inferred control right. |

The `repo-derived` contribution is the operational combination: the actual nonnegative producer history makes $C=I+p(T)>0$ without exposing $p$; this earns uncapped exact order and the first-response recurrence; a second actual pulse subtracts that earned free response to obtain native impulse moments and the actual advanced field. It then initializes the supplied complete predictor and pays for entrance to the supplied passive four-view domain. Generic positive moment algebra, Jacobi reconstruction, control and four-view transport are subtracted suppliers. This description asserts no worldwide priority for the mathematical ingredients or their possible other applications.

**Definition 23.2 (scope retained by the result).** The source class, exact rational port, fixed law, authentic zero/nonnegative producer history, bound root, successful exclusive calls, signed input rights, Hold, assurances and actual backing are premises. The theorem acquires numerical native order/law/state and their continued callable use conditional on that installation. It does not acquire or certify those service premises from the root observations, replace missing rights by numerical data, or supply a physical realization. No noisy-rank instrument, uniform width or lifetime-memory bound, global resource optimum, producer-word inverse, or arbitrary controlled-history four-view inverse is asserted.

P's authentic unit entrance, the capped arbitrary-field entrance, the randomized arbitrary-field confidence contract and this deterministic positive-history entrance remain distinct sufficient constructions. Their counts concern their own stated schedules and resources. Positive producer provenance is stronger than coordinatewise field nonnegativity, while a cap is different advice supporting a broader field class. No universal comparison of all resource coordinates is made.

The original arbitrary-signed-field obstruction and every fixed-$G_{\rm gc}$/original-$Q$, parked-consumer, unchanged-initialization and lost-chronology statement retain their exact original domains. This rational path result supplies no transport to native $\alpha/\beta$ constructors, universal generator pair, arbitrary graph geometry or another physical process. Such a transport still requires a common actual initialization, operation/output correspondence, internal acquisition and retained-resource bridge. The four-expression recovery here is the authentic newly prepared passive domain of Theorem 20.2; the full unrestricted programme remains beyond this bounded result.

## 追加锚（本行以下为增补区）

## 24. Arbitrarily small signed entry fields can conceal a longer native path

**Definition 24.1 (uncapped entry balls and the exact acquisition task).**
Retain precisely Assumption 1.2's bound root, serial Read, returning Tick,
Hold and arbitrary rational signed Add, with its assurances, rights and
sufficient finite backing. There is no order cap. For a supplied rational
$\rho\ge0$, let $\mathcal C_\rho$ consist of all finite $N\ge1$, rational
symmetric Jacobi matrices with strictly positive adjacent links, and
rational entry vectors $z$, such that

$$
\tfrac14 I\le T\le\tfrac34 I,\qquad \|z\|_2\le\rho.
\tag{UFS.53}
$$

The enclosure is fixed for the entire class. No common positive lower
bound on the links, denominator/width bound, order bound or additional
source observation is supplied. The radius bounds the entry field only;
subsequent authorized Add inputs need not obey it. The one-cell case has
no adjacent-link condition. A controller is one source-independent finite
effective program for the public $\rho$, with arbitrary finite adaptive
computation, storage and commands on each finite run.

An exact acquisition must terminate successfully with either the actual
native order and law, the entire native impulse law in an effective
finite description, or a finite self-sufficient predictor for the complete
service from its **actual advanced stopping cut**. Such a predictor must
compute the complete declared returns of every finite legal continuation,
including its successive updated predictive state, without consulting new
source returns for hypothetical evaluation. Fixed words are included;
induction on matching replies then covers adaptive continuations. Keeping
a callable reference and forwarding an unpredicted request is actual use,
but alone is not this predictive acquisition. No claim here requires
recovering an erased entry journal.

**Lemma 24.2 (small signed compensation of a complete finite transcript).**
Fix $\rho>0$ and any finite completed command transcript $\pi$ on the
reference specimen $T_0=(\lambda)$, $\lambda=1/2$, with entry zero. Include
every scalar return, every returning Tick, fixed acknowledgement and
local stopping decision. Suppose $\pi$ has $t$ Ticks. There is one fixed
specimen $(S,z)\in\mathcal C_\rho$ of order $M=t+2$ that gives exactly
this complete transcript under replay of its commands, with
$\|z\|_1<\rho$. Its second native impulse moment is
$\lambda^2+\epsilon^2$ for some rational $\epsilon>0$, whereas the
reference moment is $\lambda^2$.

Proof. Put $c=1/8$. For rational $0<\epsilon\le c$, take $S=S_\epsilon$
to have all diagonal entries $\lambda$, first link $\epsilon$ and all
remaining links $c$. For every real vector $v$, writing $b_i$ for these
links gives

$$
\left|v^{\mathsf T}(S-\lambda I)v\right|
\le\sum_{i=0}^{M-2}b_i(v_i^2+v_{i+1}^2)
\le\tfrac14\|v\|_2^2.
\tag{UFS.54}
$$

Each coordinate meets at most two links of size at most $1/8$. Thus
(UFS.53) holds, uniformly in $M$ and $\epsilon$, and every actual link is
positive.

Write $\eta_j=(S_\epsilon^j)_{00}$. Expanding matrix powers as finite
walk sums, every walk from cell zero back to zero crosses its first link
an even number of times. A walk never crossing it stays at zero.
Consequently there are polynomials $H_j\in\mathbb Q[X]$ with

$$
\eta_j=\lambda^j+\epsilon^2 H_j(\epsilon^2),\qquad
H_0=H_1=0,\quad H_2=1.
\tag{UFS.55}
$$

For $1\le i\le t$ the same parity argument gives rational polynomials
$K_{ji}$ such that $(S_\epsilon^j)_{0i}=\epsilon K_{ji}(\epsilon^2)$.
They vanish when $i>j$. At $i=j$ the unique length-$j$ path has no stay
or backward step, so $K_{jj}=c^{j-1}$. Setting $\epsilon=0$ in these
polynomial identities is only bookkeeping; it is never the admitted
witness matrix.

List the transcript's Add inputs as $(s_\ell,u_\ell)$, where $s_\ell$
is the number of Ticks preceding that actual Add. For $0\le j\le t$
define

$$
g_j=\sum_{s_\ell\le j}u_\ell
       (\lambda^{j-s_\ell}-\eta_{j-s_\ell})
    =\epsilon^2 D_j(\epsilon^2),\qquad D_j\in\mathbb Q[X].
\tag{UFS.56}
$$

Here $g_0=0$. Define rational polynomials successively by

$$
W_j(X)=c^{1-j}\left(D_j(X)-\sum_{i=1}^{j-1}K_{ji}(X)W_i(X)\right)
\quad(1\le j\le t).
\tag{UFS.57}
$$

These triangular pivots are fixed nonzero constants, not powers of
$\epsilon$. Set $z_0=z_{t+1}=0$ and
$z_i=\epsilon W_i(\epsilon^2)$ for $1\le i\le t$. When $t=0$, take
$z=0$ in dimension two. The triangular identities prove
$e_0^{\mathsf T}S_\epsilon^jz=g_j$ for every $0\le j\le t$.

To choose one rational witness, let $C$ be one plus the sum of the absolute
values of all coefficients of all the $W_i$; the empty sum is zero.
For $0<\epsilon\le c<1$,
$\|z\|_1\le\epsilon(C-1)<\epsilon C$. Choose
$\epsilon=\min\{c,\rho/(2C)\}$. Then $z$ is rational and
$\|z\|_2\le\|z\|_1<\rho$. This choice fixes the entire specimen before
any replay.

Consider now any chronological cut of $\pi$, at epoch $j$, with only
its already executed pulses $P$ included. Formula (UFS.3) gives the root
on the new specimen as

$$
g_j+\sum_{\ell\in P}u_\ell\eta_{j-s_\ell}
   =\sum_{\ell\in P}u_\ell\lambda^{j-s_\ell}.
\tag{UFS.58}
$$

Indeed every pulse at an earlier epoch has already occurred. A pulse at
epoch $j$ that is in (UFS.56) but has not yet occurred contributes zero
to $g_j$, since $\lambda^0=\eta_0=1$. Thus the identity applies before
and after each Add, to repeated Reads and to the output immediately
following **each** Tick update. Holds and Adds have the same fixed
acknowledgements. The right-hand side is exactly the reference root.
This proves equality of all declared outputs, not merely a selected
subsequence. With identical inputs and outputs, induction through the
controller's local computation gives the same subsequent adaptive
command, rational input, local state and stopping/export decision.
Finally (UFS.55) at $j=2$ proves the stated impulse difference, whether
or not that index was observed in $\pi$. $\square$

## 25. Exact finite acquisition has a closed zero-radius endpoint

**Theorem 25.1 (one exact-acquisition dichotomy).** For Definition 24.1's
closed classes the following statements hold.

1. For every rational $\rho>0$, no deterministic controller terminates
   successfully and correctly on every specimen in $\mathcal C_\rho$
   for any of the exact acquisition targets in Definition 24.1.
2. For the same positive radii, no controller using independent paid fair
   bits has both zero error on every fixed specimen and almost-sure
   successful finite acquisition on every specimen. A successful finite
   computation is required to have read only finitely many bits. Zero
   error means probability zero of an incorrect successful export;
   unsuccessful runs or nontermination do not count as successful
   acquisition.
3. At $\rho=0$ the already supplied authentic unit-impulse construction
   does terminate exactly, acquire the native law and initialize the
   complete retained predictor from its actual stopping state.

Proof. For part 1, run a proposed total correct controller on the
one-cell zero-entry reference. Its successful stopping transcript
$\pi$ is finite. Lemma 24.2 supplies one admitted specimen that repeats
that whole transcript and hence the same successful export. The two
native orders differ, and their impulse laws differ already at the
second moment. Thus neither a native-law export nor an impulse-law
export can be correct on both.

For the predictor target it is essential to use the actual final states,
not the entries or an unexecuted reset. They are respectively

$$
a=\sum_\ell u_\ell\lambda^{t-s_\ell},\qquad
b=S^t z+\sum_\ell u_\ell S^{t-s_\ell}e_0.
\tag{UFS.59}
$$

Starting at these very cuts, consider the two legal alternative words
$W=$ Tick; Tick and $W^+=$ Add$(1)$; Tick; Tick. On any one source the
last-root difference between these two alternatives is its second
native impulse moment, independently of its current state. If the
complete continuations agreed between the two sources for both words,
subtracting their final scalars would force
$\lambda^2=\lambda^2+\epsilon^2$. Hence at least one word has different
returns. The same exported self-sufficient predictor cannot be correct
on both actual stopping states. These are two alternatives quantified
by the task, not an experiment requiring cloning, reset or execution
of both words on one specimen. A failure on fixed words also defeats
prediction of every legal adaptive continuation.

For part 2, first fix the reference specimen, independently of all bits.
Almost-sure successful finite acquisition implies that at least one
successful finite execution reads a finite bit word $w$. More explicitly,
the successful finite executions are a countable union of cylinders of
finite bit prefixes; every such cylinder has probability
$2^{-|w|}>0$, with probability one when $w$ is empty. Fix one stopping
prefix. All its infinite extensions give the same finite transcript
$\pi$ and export, because no further bit has been read at this stop.
Zero error on the reference forces that export to be correct there:
an incorrect fixed export on this cylinder would already have positive
error probability.

Construct the single witness $(S,z)$ from this one $\pi$ by Lemma 24.2,
and fix it before a fresh independent fair-bit run. On its $w$ cylinder,
local computation and all returning observations agree by induction,
so the controller again stops with the identical export. The native-law
or actual-cut predictor contradiction from part 1 makes it incorrect
on this witness. Its error probability is at least $2^{-|w|}>0$.
This contradicts zero error. The witness is not selected separately for
each infinite tape. No numerical error floor independent of the
controller, transcript or radius is asserted. The exported predictor
here is the finite locally evaluable exact predictor in Definition 24.1;
future random bits are not a source observation. Even if its evaluation
were allowed fresh independent bits with zero-error almost-sure exact
answers, their common law could not equal two different required scalar
answers almost surely on the separating word.

For part 3, the closed condition $\|z\|_2\le0$ gives $z=0$ on the
actual source, without an observation or an inferred unknown norm.
Execute the authorized Add$(1)$ and receive its acknowledgement. This
really establishes $e_0$. Apply [P Theorem 37.2][P]: the initial Read
and $2N$ actual returning Ticks give $2N+1$ scalar returns; the first
singular positive impulse Hankel block earns the uncapped order.
[P Propositions 37.3–37.4][P] supply native rational Jacobi inversion,
least recurrence and transfer. The actual final vector is
$T^{2N}e_0$, and [P §§40–41][P] supply its retained complete-menu
predictor and continued same-root use, conditional on the already
supplied binding and rights. Every Hold, acknowledgement, scalar,
calculation and retained record has its stated real cost. These are
applications of the supplied positive endpoint, not new inversion or
retention theorems. The fixed enclosure lies strictly inside $0<T<I$,
so all those supplier hypotheses hold. $\square$

An open radius-zero ball is empty and is not this positive endpoint.
The dichotomy concerns exactly these nested **closed** entry classes,
this service and these exact successful acquisition contracts.

## 26. Small-entry scope, mathematical credit and the remaining bridge

**Definition 26.1 (source-relative content).** Lemma 24.2 contributes
the small-entry compensation: one weak first link changes every finite
forced impulse response by $\epsilon^2$ while the triangular observation
solve needs only an $O(\epsilon)$ signed entry. Its constants and the
chosen positive link depend on the whole finite reference transcript;
its spectral enclosure does not. Since the witness has
$\|z\|_1<\rho$, the same obstruction also applies when a positive open
or closed $\ell^1$ or $\ell^\infty$ entry ball replaces (UFS.53), using
$\|z\|_\infty\le\|z\|_2\le\|z\|_1$. No norm equivalence with a hidden
dimension-dependent constant is needed.

The existing §7 supplies arbitrary-field finite-transcript
indistinguishability and actual-final-cut separation. Formula (UFS.3)
supplies the exact free/forced ages, and the present proof preserves
every returning Tick. Finite-prefix cylinders give the elementary
fair-bit consequence; no new general probability principle is claimed.
Native inversion and retained use at the zero endpoint belong to
[P §§37,40–41][P]. The classical moment/Jacobi supplier is
[Teschl, §2.5][Teschl], equations (2.109)–(2.118) and the finite-support
paragraph on printed p.44. That paragraph, rather than Theorem 2.13's
nonfinite-support hypothesis, is the finite-chain correspondence.
The `repo-derived` delta is the consolidated positive-radius signed-entry
obstruction, its specified zero-error consequence and its contrast with
the credited closed-zero endpoint. This is a source-relative claim,
without a worldwide novelty or new Lean-certification claim.

**Definition 26.2 (unmoved acquisition and realization boundaries).**
Theorem 25.1 permits an arbitrarily weak positive first link and
unbounded rational widths and order. It supplies no fixed-positive-lower-link,
bounded-width or capped-order obstruction. Exact equality of returns
and exact successful acquisition are essential to its statement; no
approximate/noisy or confidence lower bound follows. In particular,
§§10–16's randomized confidence-qualified acquisition permits an error
event and keeps its original contract. The positive-probability error
found here does not contradict that contract.

Sections 17–23 instead assume an authentic zero-start producer using
nonnegative rational pulses: $z=p(T)e_0$ with nonnegative polynomial
coefficients. That provenance makes $I+p(T)>0$ and supplies their
positive weighted-Hankel stopping argument. A small arbitrary signed
vector is not a certificate of that producer history. The compensation
lemma does not assert that its witness belongs to this producer class,
and it leaves its deterministic acquisition, preparation and real passive
entrance intact. The coordinatewise nonnegative-field counterexample
in Proposition 22.1 still concerns its specified test alone.

The result depends on the actual installed rational path service,
exclusive rights, class assurance and finite backing. It acquires none
of those premises and certifies no physical conformance. It transports
neither to alpha/beta growth nor to a fixed universal relation structure.
All fixed-$G_{\rm gc}$, original-$Q$, parked-consumer,
unchanged-initialization and erased-chronology statements keep their
original scopes. No arbitrary controlled-history four-view inverse,
physical realization, global resource optimum or completion of the
unrestricted common-process programme is asserted.

## 追加锚（本行以下为增补区）

## 27. Authentic signed producers over a localized rational ring

**Definition 27.1 (arithmetic entrance on one actual source).** Fix a public prime $p$ and put

$$
R_p=\mathbb Z_{(p)}=\{a/b\in\mathbb Q:\ a,b\in\mathbb Z,\ b\ne0,\ p\nmid b\}.
\tag{UFS.60}
$$

The denominator condition may equivalently be imposed on the reduced fraction. The unknown order is any finite $N\ge1$. The fixed native rooted Jacobi matrix $T$ satisfies (UFS.1), with the additional condition that every entry belongs to $R_p$. Adjacent links are strictly positive rationals; they need not be units of $R_p$. There is no supplied order, width, degree or producer-length bound.

On this very source an actual producer initializes every cell to zero and executes a finite serial word of Tick, Add$(c)$ with $c\in R_p$, Read and Hold. Producer inputs may have either sign. There is no other input, autonomous evolution, field replacement or law change. Every producer Tick returns its updated root, every Read its present root, and every Add and Hold its fixed acknowledgement. These are real producer outputs, with their own traffic and any retained archives. The receiver is not given the producer word or its archive for free.

Inductively assign a polynomial $h\in R_p[X]$ to the producer cut. Initially $h=0$; a Tick replaces $h$ by $Xh$, an Add$(c)$ by $h+c$, and a Read or Hold leaves it unchanged. Thus the actual handover field is

$$
x^{\rm in}=h(T)e_0.
\tag{UFS.61}
$$

This is a consequence of an executed root-producer history, not a coordinatewise sign condition, a supplied polynomial, or an observer reconstruction of that history. With $J_{\rm p}$ producer Ticks and inputs $c_l$ at epochs $s_l$, its expression is $h(X)=\sum_l c_lX^{J_{\rm p}-s_l}$. The receiver need know none of these coefficients or epochs.

**Assumption 27.2 (handover, rights and full receiving menu).** The initialization, producer restriction, coefficient restriction and fixedness are assured premises. Handover preserves the same field, native law and bound root without a hidden Tick. Retain Assumption 1.2's exact serial Read, returning Tick, arbitrary rational signed Add and Hold service, including its complete outputs, reference, exclusive access, call and input rights, serialization, effective Hold and sufficient finite backing. The receiving Add domain is all of $\mathbb Q$, even though the producer domain was $R_p$. In particular Add$(1/p)$ is authorized. No Reset, clone, size/coefficient port, chosen-index response oracle or timing/work/size side channel is introduced. Neither an order cap nor random bits are inputs. One finite receiving program takes $p$ as public input and applies to every admitted finite source and producer.

The theorem below acquires numerical law and state conditional on this installation. It does not acquire or certify the installation, rights or producer assurance by observing roots. Actual provenance, an algebraic representation such as (UFS.61), and the receiver's acquired numerical record remain different objects. Physical conformance retains the volume's `ASSUMED-UNVERIFIED` boundary.

## 28. Arithmetic provenance prevents premature principal-Hankel singularity

**Theorem 28.1 (signed principal-minor stopping certificate).** For every source and actual producer of Definition 27.1 under Assumption 27.2, execute Hold; Add$(1/p)$; Read. Write the returned root as $y_0$. Subsequently execute returning Ticks in pairs, retaining every scalar, and Hold after each pair. At pair number $n\ge1$, test over $\mathbb Q$ the block

$$
Y_n=(y_{i+j})_{0\le i,j\le n},\qquad z_j=p y_j,\qquad H_n=(z_{i+j})_{0\le i,j\le n}.
\tag{UFS.62}
$$

The first singular tested block occurs exactly at $n=N$, after exactly $2N$ Ticks. Also $Y_0$ is nonsingular. No link-unit premise, nonnegative producer input, positive spectral weight, or positive-definite signed Hankel premise is required. All tests are exact rational singularity tests; reduction modulo $p$ is a proof of noncancellation, not the stopping algorithm.

Proof. Reduction $\rho:R_p\longrightarrow\mathbb F_p$ sends $a/b$ to $\bar a\bar b^{-1}$. Cross multiplication shows it is well defined; it respects sums and products, and its kernel is $pR_p$. In particular an element with reduction $1$ is nonzero in $\mathbb Q$.

Let $b$ denote the actual field just after the exceptional Add, and define the mathematical matrix $C$ by

$$
b=x^{\rm in}+p^{-1}e_0=p^{-1}Ce_0,\qquad C=I+p h(T).
\tag{UFS.63}
$$

All entries of $h(T)$ lie in $R_p$. The real symmetric matrix $C$ commutes with $T$, and its entrywise reduction is $I$. For every native coordinate subset $S$, its principal submatrix $C_{S,S}$ reduces to $I_{S,S}$. The determinant is a sum of products of entries, so

$$
\rho(\det C_{S,S})=1,\qquad \det C_{S,S}\ne0.
\tag{UFS.64}
$$

In particular $C$ is invertible. This conclusion makes no assertion about the signs of its eigenvalues or principal determinants.

Because the source actually evolves from $b$, its returns satisfy $z_j=e_0^{\mathsf T}T^jCe_0$. For $n<N$ put $K_n=[e_0,Te_0,\ldots,T^ne_0]$. Native path triangularity, supplied by [P Lemma 37.1][P], gives

$$
K_n=\begin{pmatrix}L_n\\0\end{pmatrix},\qquad
(L_n)_{jj}=\beta_j,\qquad
\beta_0=1,\quad \beta_j=\prod_{i=0}^{j-1}b_i>0.
\tag{UFS.65}
$$

Here $L_n$ is upper triangular and the zero rows correspond to cells beyond $n$. Symmetry of $T$ and commutation with $C$ now give, with $S_n=\{0,\ldots,n\}$,

$$
\begin{aligned}
H_n&=K_n^{\mathsf T}CK_n=L_n^{\mathsf T}C_{S_n,S_n}L_n,\\
\det H_n&=\left(\prod_{j=0}^n\beta_j\right)^2\det C_{S_n,S_n}\ne0.
\end{aligned}
\tag{UFS.66}
$$

The factors $\beta_j$ need only be nonzero in $\mathbb Q$. They may reduce to zero modulo $p$. At $n=N$, the matrix $K_N$ has $N+1$ columns and only $N$ rows, so $H_N=K_N^{\mathsf T}CK_N$ has rank at most $N$. Since $H_n=pY_n$, scaling does not affect rational singularity. Equations (UFS.64)–(UFS.66) include $n=0$, and prove every assertion. The program grows its arrays pair by pair and therefore needs no advance knowledge of $N$. $\square$

**Proposition 28.2 (the earned recurrence is valid at every shift).** At this actual first stop solve

$$
H_{N-1}(q_0,\ldots,q_{N-1})^{\mathsf T}
=-(z_N,\ldots,z_{2N-1})^{\mathsf T},\qquad
q(X)=X^N+\sum_{j<N}q_jX^j.
\tag{UFS.67}
$$

Then $q$ is the characteristic polynomial of the actual native $T$, and

$$
y_{s+N}=-\sum_{j<N}q_jy_{s+j}\quad(s\ge0).
\tag{UFS.68}
$$

Its degree $N$ is the least degree of a monic recurrence holding at all nonnegative shifts of $y$. These are all-future statements, rather than a finite-prefix fit.

Proof. Theorem 28.1 gives the nonsingular solve. Let $K=K_{N-1}$. Its equations are $K^{\mathsf T}Cq(T)e_0=0$. Both $K$ and $C$ are invertible, whence $q(T)e_0=0$. Commutation implies $q(T)T^je_0=0$ for every $j$; these vectors include a basis, so $q(T)=0$. No nonzero polynomial of degree less than $N$ annihilates $e_0$, by the same native triangularity. The monic characteristic polynomial has degree $N$ and annihilates $T$; its difference from $q$ therefore vanishes and has degree less than $N$, so it is zero. Multiplying $q(T)=0$ by the actual readout and state gives (UFS.68).

If a monic polynomial $r$ of smaller degree supplied an all-shift recurrence for $y$, its first $N$ equations would give $K^{\mathsf T}Cr(T)e_0=0$, hence $r(T)e_0=0$, a contradiction. Thus the recurrence is least. This proof uses the newly earned principal-minor certificate; finite Ho--Kalman recovery with a reference order is not substituted for that certificate. $\square$

The noncancellation mechanism is specifically $C\equiv I\pmod p$ in native coordinates, followed by a rational triangular congruence. It does not identify the Hankel rank over $\mathbb F_p$. If some link is divisible by $p$ in $R_p$, a reduced Hankel block can be singular well before the correct rational stopping index. Conversely an invertible symmetric $C$ alone would not ensure its smaller coordinate principal blocks were invertible; (UFS.64) supplies exactly that additional condition.

## 29. The actual second pulse, native coordinates and complete retained use

**Theorem 29.1 (native acquisition at the true advanced cut).** Continue on this same specimen from Theorem 28.1's held cut, where the field is $T^{2N}b$. Execute Add$(1)$; Read, then $2N-1$ returning Ticks and a final Hold. Denote these $2N$ actual scalar returns by $v_0,\ldots,v_{2N-1}$. There is an effective exact rational construction of the native $T$, its impulse law and the actual field at this final cut, without reconstructing the producer word or $h$.

Proof. The acquired recurrence extends the first response locally through $y_{4N-1}$. Put $w=T^{2N}b+e_0$, the actual post-second-pulse field. The free/forced identity (UFS.3), with Add and Tick kept as separate actual operations, gives

$$
v_j=e_0^{\mathsf T}T^jw=y_{2N+j}+m_j,\qquad
m_j=v_j-y_{2N+j}\quad(0\le j\le2N-1).
\tag{UFS.69}
$$

Consequently the subtraction yields the true native impulse moments $m_j=e_0^{\mathsf T}T^je_0$, not the signed weighted moments $y_j$ or their normalization. The $v_j$ are paid observations; the extended $y_j$ are computations from the earned recurrence. Neither is a response-query oracle.

Apply [P Proposition 37.3][P] to these moments with the now-earned order $N$. Its monic moment-orthogonal polynomials $P_j$, $0\le j<N$, have the exact native correspondence

$$
P_j(T)e_0=\beta_je_j,\quad h_j=\langle P_j,P_j\rangle_m=\beta_j^2,\quad
a_j=\frac{\langle XP_j,P_j\rangle_m}{h_j},\quad
b_j=\sqrt{h_{j+1}/h_j}>0.
\tag{UFS.70}
$$

The moment pairing is the ordinary Euclidean pairing of polynomial vectors on this actual source. The smaller native impulse Gram matrices are positive because their native Krylov columns are independent; this positivity is not asserted for the first signed response. The diagonal formulas need only moments through $2N-1$, and the link norms through $2N-2$. P's additional moment $m_{2N}$ was an unknown-order stopping certificate; here Theorem 28.1 has already earned the order. Each positive root in (UFS.70) is rational by the source promise. Integer roots of the reduced numerator and denominator, with exact squaring checks, compute it without a real-root oracle. Positive links fix the native orientation. Thus this is an application of the supplied native inverse, not a new moment/Jacobi theorem.

Form the observability matrix $\mathcal O_N=K_{N-1}^{\mathsf T}$ using the recovered $T$, and solve

$$
\mathcal O_N w=(v_0,\ldots,v_{N-1})^{\mathsf T},\qquad
x_*=T^{2N-1}w
=T^{4N-1}(x^{\rm in}+p^{-1}e_0)+T^{2N-1}e_0.
\tag{UFS.71}
$$

Native triangularity makes this solve nonsingular. The right-hand side consists of actual returns from $w$, and there really have been $2N-1$ Ticks since that field. Hence $x_*$ is the actual present field, rather than a reset or handover field. At $N=1$ all formulas still apply: the second stage has one Tick, one diagonal and no link-root extraction. The acquired $q$ and true moments also give the supplied uncancelled transfer

$$
F_T(z)=e_0^{\mathsf T}(zI-T)^{-1}e_0
=\sum_{j\ge0}m_jz^{-j-1},
\tag{UFS.72}
$$

as finite rational polynomial data, by [P Proposition 37.4][P]. $\square$

**Corollary 29.2 (all-field and all-menu service from this cut).** Retain $N,T,q$, $\mu=(m_0,\ldots,m_{N-1})$, $\widehat x=x_*$ and $a=\mathcal O_Nx_*$. Retain also the actual source reference, applicable call/input rights and backing, and the prescribed actual return records. The following supplied predictive updates are correctly initialized at this actual cut for every finite adaptive continuation with arbitrary rational Add inputs.

| Actual command | Native record after the command | Predictive record after the command | Complete output |
| --- | --- | --- | --- |
| Read | $\widehat x$ | $a$ | $a_0$ |
| Tick | $T\widehat x$ | $a'_j=a_{j+1}$ for $j<N-1$; $a'_{N-1}=-\sum_{j<N}q_ja_j$ | $a'_0$ |
| Add$(r)$, $r\in\mathbb Q$ | $\widehat x+r e_0$ | $a'=a+r\mu$ | fixed acknowledgement |
| Hold | $\widehat x$ | $a$ | fixed acknowledgement |

Proof. Theorem 29.1 establishes $\widehat x=x_{\rm actual}$ and $a=\mathcal O_Nx_{\rm actual}$ at installation. For every $x\in\mathbb Q^N$, not merely for a cyclic or producer-reachable $x$, the identity $q(T)=0$ gives the Tick row and $\mathcal O_Ne_0=\mu$ gives the Add row. Read and Hold preserve the two identities. Tick's output is the updated root, and no scalar is declared for Add or Hold. Serial receipt and local commit precede the next exposed completed cut. Induction therefore preserves both identities and every output through any finite common adaptive continuation. Equal earlier outputs give the same next chosen command and rational input, so adaptation adds no exception. This is the exact initialization and use of §4 and [P Theorem 40.2][P], with (UFS.71) replacing their entry-state input.

Numerical forecasts on scratch records neither execute a command nor acquire an observation, source reference or right. Actual continued use still calls the same retained source, receives every declared frame and pays all work, traffic and growing records. After receiving an Add outside $R_p$, the arithmetic entrance premise need no longer describe the new field; the all-field predictive invariant still holds. $\square$

## 30. Executed preparation and the exact four-expression image

**Corollary 30.1 (paid entrance, mutual recovery and passive dynamics).** From the held cut (UFS.71), the supplied native controllability construction earns a new actual unit origin on this specimen. After a further actual passive segment of $k\ge2N$ Ticks, the four independently specified data below lie in [P Definition 39.1][P]'s domain, mutually recover one another, agree along every recovery route and commute with passive Tick, Read and Hold.

Proof. Solve, over $\mathbb Q$,

$$
[T^{N-1}e_0,\ldots,e_0](u_0,\ldots,u_{N-1})^{\mathsf T}
=e_0-T^Nx_*.
\tag{UFS.73}
$$

The reversed Krylov matrix is invertible. Execute in order $N$ pairs Tick; Add$(u_j)$, including any zero Add, and Hold after each pair. Retain every Tick scalar before that pair's Add and every acknowledgement. Induction gives the actual field after $j$ completed pairs as

$$
x_j=T^jx_*+\sum_{l<j}u_lT^{j-1-l}e_0\quad(0\le j\le N).
\tag{UFS.74}
$$

Equation (UFS.73) makes $x_N=e_0$. Call this actual held cut $o$. Read its root and execute $k\ge2N$ returning Ticks with no Add, retaining the origin return and all $k$ subsequent scalars. The actual field is now $x=T^ke_0$. This is §§5–6 and 20's supplied preparation and passive entrance, now applied to the genuinely acquired $T,x_*$. No unexecuted reset is substituted.

The four numerical views have the following independent meanings, relative to this actual origin and common installation.

| View | Exposed data and meaning |
| --- | --- |
| Space | $(T,x)$: native rooted cell adjacency/weights and the present native cell field |
| Time | $(m_0,\ldots,m_k)$: this actual paid ordered passive root segment from $o$ |
| Boundary | $(F_T,x_0)$: finite endpoint transfer law and present endpoint value |
| Memory | $(q,\mu,a)$: least native recurrence, its initial impulse values, and present sufficient predictive state $a=\mathcal O_Nx$ |

References, rights, backing and assurance are retained common context, separately charged and not hidden coordinates inside every numerical view. Producer and preparation archives are separate records; none of these views is an unrestricted copy of them.

For completeness the supplier's recovery correspondence is as follows. Time's length gives $k$; its first flat positive impulse block gives $N$, and (UFS.70) gives native $T$. Boundary's rational function expands at infinity to the same moments and thus gives $T$. Memory's least degree gives $N$ and its recurrence and initial values generate the same moments, hence $T$; also $\mathcal O_N^{-1}a=x$. Space already gives $T,x$. Because $0<T<I$, the native impulse law has

$$
1=m_0>m_1>\cdots>0,\qquad m_j\longrightarrow0.
\tag{UFS.75}
$$

Indeed its spectral form is a sum of $\lambda^j$ with positive weights summing to one and $0<\lambda<1$. Thus for Space, Boundary and Memory, enumeration of these rational moments until the current root equals $m_k$ terminates uniquely on their declared actual images. Each route recovers precisely $(T,k,T^ke_0)$; reconstructing a target view from that triple gives route agreement. Reconstructing the numerical Time list reproduces an already paid segment; it does not establish provenance for an unexecuted segment.

Passive Tick sends the triple to $(T,k+1,Tx)$, appends its actual return to Time, preserves $F_T$ and updates Boundary's present root, and shifts Memory by $q$. Read and Hold preserve epoch and field and have their stated complete outputs. These are exactly [P Lemma 39.2 and Propositions 39.3–39.4][P]. On this image, equality of any numerical view fixes the same $(T,k,x)$ and therefore suffices for equality of all complete finite adaptive continuation outputs and corresponding native successors under the common installed menu, by Corollary 29.2. References and legal rights are still common context for that comparison. Enumeration is an inverse on the actual image, not a terminating off-image recognizer or an $N$-only cost bound at arbitrarily late phase. A later Add remains in Corollary 29.2's complete service but does not thereby put an arbitrary controlled journal in this passive four-view domain. $\square$

## 31. One same-run arithmetic-entrance account

**Definition 31.1 (specified schedule and separate bills).** Use exactly §21's schedule with its first receiver Add$(1)$ replaced by Add$(1/p)$: one initial Hold; one Hold after each first-stage Tick pair; one final Hold after the second-stage Ticks, covering native computation and the preparation solve; one Hold after each preparation Tick/Add pair; then the origin Read and $2N$ passive Ticks with one Hold after each passive pair. A Hold ends before the next state-changing command. All indicated Holds and zero Adds are real calls. Use Convention 8.1's literal reduced-rational encoding and actual framing. Initialization, source arithmetic, controller arithmetic, traffic, simultaneous material, retained archives, references and rights are distinct coordinates.

**Proposition 31.2 (attained exact traffic).** For every admitted run, the receiver counts are

| Coordinate | Through native acquisition and predictor installation | Through actual preparation and passive $k=2N$ cut |
| --- | --- | --- |
| Returning Ticks | $4N-1$ | $7N-1$ |
| Adds | $2$ | $N+2$ |
| Reads | $2$ | $3$ |
| Holds | $N+2$ | $3N+2$ |
| Scalar returns | $4N+1$ | $7N+2$ |
| Fixed acknowledgements | $N+4$ | $4N+4$ |
| Calls and complete return frames | $5N+5$ | $11N+6$ |
| Random bits | $0$ | $0$ |

Proof. First-stage stopping uses $2N$ Ticks and $N$ pair Holds. The second stage uses $2N-1$ Ticks and its final Hold. Together they have two Adds, two Reads and the initial Hold. Preparation adds $N$ Ticks, $N$ Adds and $N$ Holds; passive entry adds an origin Read, $2N$ Ticks and $N$ Holds. Every Tick and Read emits a scalar, every Add and Hold an acknowledgement. The resulting sums are precisely §21.2's supplied schedule counts; the changed exceptional pulse changes literal input bits and subsequent rational widths, not command counts. $\square$

**Proposition 31.3 (producer, source, computation and material on that run).** Let the actual producer have counts $J_{\rm p},A_{\rm p},R_{\rm p},H_{\rm p}$. Through the right-hand endpoint in Proposition 31.2, put

$$
J=J_{\rm p}+7N-1,\quad A=A_{\rm p}+N+2,\quad
R=R_{\rm p}+3,\quad H=H_{\rm p}+3N+2.
\tag{UFS.76}
$$

There are $J+R$ actual scalar returns, $A+H$ acknowledgements, $J+A+R+H$ service calls and $A$ transmitted pulse rationals. The direct simultaneous-buffer implementation of [P Proposition 41.2][P] uses

$$
J(3N-2)\ \text{rational products},\qquad
J(2N-2)+A\ \text{rational additions},\qquad NJ\ \text{Tick destination writes}.
\tag{UFS.77}
$$

Add's root writes, the actual $N$ initial zero writes, any extra buffer initialization, coefficient installation, parsing/framing/control, reference and grant setup, assurance and storage/backing work are additional paid resources. No producer count is bounded by $N$ alone.

One receiver implementation uses $O(N^4)$ exact rational arithmetic/reduction/comparison operations, $N-1$ positive rational-root extractions and $O(N^2)$ numerical words through this endpoint. Let $W\ge1$ bound the actual widths of every integer/rational operand and intermediate and binary counter on this one finite producer/receiver run, including $p$, transmitted inputs and source operations. Let $L_{\rm io}$ be all actual traffic bits, framing and separately materialized output copies; $G_{\rm p}^{\rm ctl}$ the remaining producer controller work; and $I_{\rm work}$ all remaining setup, access and backing work. A conservative attained bit-work bound is

$$
O\!\left((N^4+NJ+A)W^3+L_{\rm io}\right)
+G_{\rm p}^{\rm ctl}+I_{\rm work}.
\tag{UFS.78}
$$

A coexisting numerical layout uses $O(B+N^2W)$ bits, where $B$ is the actual native coefficient-store length, plus actual producer stores, framing, extra archives/export copies, program, references, rights, assurance and backing. Neither $W$ nor these stores are uniformly bounded by $N$ or the finite program.

Proof. Counts in (UFS.76) add consecutive operations on the same source. Equation (UFS.77) is the supplied direct sparse update count, independent of signs and denominator divisibility; $N=1$ gives one product and no Tick addition. Each Add has one actual root addition. Arbitrarily many producer Ticks from zero or zero Adds can precede a fixed endpoint, proving the absence of an $N$-only producer-count bound.

For receiving computation use exact elimination with row pivoting for each rational $H_n$, including the final singular block. It costs $O(\sum_{n=1}^N(n+1)^3)=O(N^4)$ operations and needs no positivity or modular-rank test. Scaling returns by $p$, solving (UFS.67) and extending (UFS.68) through $4N-1$ fit that bound. Native orthogonality solves and pairings in (UFS.70) are the supplied $O(N^4)$ implementation of P41.3. There are exactly $N-1$ rational link roots. Sparse powers, the observability and control solves, current-state propagation and prediction through the remaining $O(N)$ actual commands fit within cubic additional arithmetic. No search for $h$ or its word is performed.

All divisions have nonzero denominators proved above or in the positive native impulse inverse. Each rational root is computed by integer square roots and exact squaring. Thus every admitted finite run terminates with finite $W$, without receiving $W$ in advance. School integer arithmetic, Euclidean fraction reduction and binary-search integer roots have a conservative $O(W^3)$ bit allowance per indicated operation. The source work, cell writes, actual input parsing and complete traffic give (UFS.78), with the other producer and installation work explicitly added.

A constant number of quadratic arrays for elimination, orthogonality, observability and preparation suffice; scratch is reused after its needed result is retained. The acquired law, two source state buffers, native/predictive state, controls, counters and the $O(N)$ receiver scalars and command/acknowledgement journal fit the numerical allowance. Separate producer archives or exported duplicates remain charged where retained, rather than silently discarded or made free receiver advice. Later arbitrary continuations, extra view conversions, phase enumeration at late $k$, and longer literal Time records incur their actual further work and material. This is a finite attained implementation, not a minimum-total-cost theorem or lifetime-memory bound. $\square$

## 32. Exact countermodels and incomparable entrances

**Proposition 32.1 (coordinate membership does not replace root provenance).** It is false that $x^{\rm in}\in R_p^N$ alone permits Theorem 28.1's stopping test, even when all coefficients lie in $R_p$ and the links are positive but nonunits.

Proof. Set $p=3$ and

$$
T=\begin{pmatrix}41/100&3/100\\3/100&49/100\end{pmatrix},\qquad x^{\rm in}=e_1.
\tag{UFS.79}
$$

Its eigenvalues are $1/2,2/5$, so $0<T<I$. All coefficients and coordinates lie in $R_3$, and the link $3/100$ is a nonunit. The exceptional pulse makes $b=(1/3,1)^{\mathsf T}$, an eigenvector with eigenvalue $1/2$. Hence $y_j=(1/3)(1/2)^j$ and $Y_1$ is singular although $N=2$, with $Y_0\ne0$. This field has no representation $h(T)e_0$ with $h\in R_3[X]$: modulo $3$, $T$ is diagonal, so every such polynomial vector has second coordinate zero, whereas $e_1$ does not. Thus the example violates precisely the weakened provenance premise, not the authentic producer theorem. It refutes that stopping test under the weakening, not every possible algorithm on the larger class. $\square$

**Proposition 32.2 (both arithmetic restrictions matter).** Keeping the actual $R_p$ producer while dropping the coefficient restriction can invalidate the same stopping certificate. Keeping the coefficient restriction while permitting arbitrary rational producer pulses can also invalidate it.

Proof. For the first assertion take $p=3$,

$$
T=\begin{pmatrix}5/12&1/12\\1/12&5/12\end{pmatrix},
\tag{UFS.80}
$$

whose eigenvalues are $1/2,1/3$. The actual producer Add$(-1)$; Tick starts from zero and uses only $R_3$ inputs. Its handover field is $-Te_0$. Add$(1/3)$ then leaves $(-1/12,-1/12)^{\mathsf T}$, an eigenvector of eigenvalue $1/2$. The observed response has nonzero $y_0$ and singular $Y_1$, despite order two. The coefficients of (UFS.80) are not in $R_3$, so reduction of $h(T)$ was unavailable. For the second assertion, on any allowed coefficient matrix, the arbitrary rational producer Add$(-1/p)$ leaves $-e_0/p$ and the marker cancels it completely. All $y_j$ vanish. That pulse lies outside $R_p$. Neither example is an obstruction to all other acquisition strategies. $\square$

**Proposition 32.3 (nonunit links and indefinite signed weights really occur).** The arithmetic entrance is nonempty for every prime $p$ and every finite $N$, even if every adjacent link is a nonunit. It also contains genuinely indefinite $C$, so a positive-weight argument cannot be its general proof.

Proof. Let $A_N$ be the adjacency matrix of the $N$-cell path, including $A_1=0$. Choose an integer $d>4p$ coprime to $p$, and set $T=p(2I+A_N)/d$. For $N>1$ the quadratic form of $2I+A_N$ is

$$
x_0^2+x_{N-1}^2+\sum_{i=0}^{N-2}(x_i+x_{i+1})^2.
\tag{UFS.81}
$$

It is strictly positive for nonzero $x$ and at most $4\|x\|_2^2$. The $N=1$ form is $2x_0^2$. Thus $0<T<I$, all coefficients lie in $R_p$, and every adjacent link $p/d$ is a nonunit. Any finite allowed producer, including the empty word, is admitted.

For indefiniteness choose $p=3$, $T=\left(\begin{smallmatrix}3/8&1/8\\1/8&3/8\end{smallmatrix}\right)$ and the actual producer Add$(-1)$; Tick. Then $h(X)=-X$ and $C=I-3T$ has eigenvalues $1/4,-1/2$. Both spectral components are seen at the root, so the first response has signed spectral weights of opposite signs. Nevertheless every native coordinate principal block has determinant nonzero by (UFS.64), and Theorem 28.1 applies. $\square$

**Proposition 32.4 (the arithmetic and nonnegative-history entrances are incomparable).** For each fixed public prime $p$, Definition 27.1 and Definition 17.1 supply different sufficient source/provenance classes; neither contains the other.

Proof. Choose any integer $d>1$ coprime to $p$ and the one-cell $T=(1/d)$. The arithmetic producer Add$(-1)$ gives a negative handover field. In the nonnegative producer class, $T$ is entrywise nonnegative and every nonnegative root pulse and its later iterates are coordinatewise nonnegative, so that field cannot arise. Conversely Add$(1/p)$ from zero is an allowed nonnegative producer and leaves $e_0/p$. On this same $R_p$ coefficient matrix, every $R_p$ root-producer field belongs to $R_p^N$; $e_0/p$ does not. Thus even fixing this common coefficient matrix does not make either endpoint class include the other. Both protocols retain their original counts and literal bills; neither is declared globally cheaper. $\square$

These countermodels address necessity for this arithmetic certificate and the distinction of the entrances. They do not turn one sufficient construction into a universal characterization of exact acquisition. In particular, the already published small-signed-entry obstruction in §§24–26 concerns arbitrary signed fields with only a norm bound and has its original spectral enclosure and quantifiers. Its witnesses are not asserted to be authentic $R_p$ root-producer endpoints. That obstruction is a supplier boundary, not a new result of the arithmetic entrance. The erased-chronology statement of Proposition 22.3 also retains its scope: an endpoint polynomial or the acquired native law is not an inverse of the actual producer chronology.

## 33. Mathematical provenance and remaining realization boundaries

The source-relative addition is Theorem 28.1's arithmetic-provenance certificate and Proposition 28.2's resulting uncapped all-shift recurrence, together with their actual-source initialization of the existing native acquisition and use constructions. Polynomial evolution (UFS.61) is the signed root-producer version of (UFS.3). Reduction in $\mathbb Z_{(p)}$, determinant compatibility with ring homomorphisms, triangular determinants and congruence are ordinary algebra. For example pinned upstream [matrix determinant algebra](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean) supplies `Matrix.det_mul`, `Matrix.det_transpose` and `Matrix.det_one` over a commutative ring. The new use is the native-coordinate principal-block certificate before the rational Krylov congruence, which permits nonunit links and signed or indefinite weights. This is `repo-derived` mathematical content without a worldwide priority claim.

Native moment inversion is `literature-attested`: [Teschl §2.5][Teschl], equations (2.109)–(2.118), and the finite-support paragraph on printed p.44 give the classical moment/Jacobi construction and its finite termination. Theorem 2.13's nonfinite-support premise is not used for a finite path. [P37][P] supplies the exact native-cell, positivity and rational-root correspondence needed in (UFS.70). The [coefficient-driven Jacobi declarations and their private helpers][JAC], with their [owning Scribe][JACs], use the real Euclidean space $\mathbb R^N$, actual power basis $T^je_0$, self-adjoint multiplication by $T$ and the now-earned characteristic recurrence. The signed $y$ pairing is not that Euclidean native impulse pairing. [FiniteAtomicHankelVandermonde][HVD] and its [Scribe][HVDs] supply the generic finite signed moment factorization, not the new early-block certificate. [FiniteHoKalmanBlocks][HK] and its [Scribe][HKs] retain their explicit reference-order hypothesis; an order lower bound alone supplies no upper-order stopping certificate.

For [finite observability](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs), the exact correspondence is state $\mathbb R^N$, scalar readout $e_0^{\mathsf T}$, update $T$ and horizon $N$. Native triangularity proves invertibility and the paid $v$ supplies its right-hand side. Sections 4–6, 20–21 and [P39–41][P] supply all-field prediction, executed controllability, the actual passive four-view image and the direct-source/resource mechanics; §§29–31 apply them at the newly earned cut with the exceptional marker. None of that mature reconstruction, control or view algebra is presented as newly proved abstract theory. The exact supplier hypotheses are established before each application.

The actual zero initialization, producer/coefficient restrictions, installed fixed law, bound root, exclusive serial menu, exact rational returns, exceptional rational-input right, Hold and sufficient backing remain premises. They are paid or assured as specified, and are not inferred from a matching finite transcript. There is no noisy/approximate rank instrument, uniform literal-width bound, retained-history inverse, minimum-total-resource theorem or physical-conformance certificate here. The no-cap conclusion is termination for each admitted finite source, with an actual-source-dependent finite bill, rather than a common finite horizon over all orders.

No map from native alpha/beta material constructors, a full ordered terminal-list reconstruction, a private-randomization clock experiment, or a quantum boundary realization to this arithmetic root-producer service is supplied. Such a map would have to preserve actual initialization, coefficient/input conditions, complete operations/outputs, root binding, legal access, records and resource costs; a common name or an abstract inverse does not provide it. The fixed-$G_{\rm gc}$/original-$Q$, parked-consumer, unchanged-initialization and final-no-Ready obligations keep their original exact domains. A common native-LAB/path realization, broader mutually recoverable controlled views, independently acquired authority/provenance and full resource minimality remain separate full-programme gaps. The bounded arithmetic entrance and its paid passive four-expression application do not complete that programme.

## 追加锚（本行以下为增补区）

## 34. An original-unit comb with an explicitly installed internal-root interface

**Definition 34.1 (the unit comb installation).** This installation uses AA §§17 and 20's birth-typed local syntax and NLBA II §17's persistent material templates, but changes the field ports. Put

$$
u_0=\alpha,\qquad u_{n+1}=\langle\beta,u_n\rangle,\qquad
G_n=C(u_n),\qquad N_n=3n+1.
\tag{UFS.82}
$$

Here $C(\alpha)$ is one vertex; $C(\beta)$ is a root with one terminal left marker; and a branch has a root and its two ordered material subtrees. Thus the original root of $G_n$ is internal when $n>0$. Logical navigation descends only through branches, never through a beta marker. Material coordinates are root-based words, ordered by a fixed depth-first traversal. Let $A_n$ be the symmetric, zero-diagonal, unit adjacency matrix in these coordinates, and let $e$ be the original-root coordinate vector. No diagonal calibration, edge rescaling or contraction is applied.

The concealed entry is some $u_n$, $n\ge3$, with arbitrary $x^0\in\mathbb Q^{N_n}$. Neither $n$, the term, the coordinates nor $x^0$ is supplied to the receiving controller. This is a class promise about an actually prepared source, not an assertion that every native term is a comb. The following root field interface is installed on that same source, in addition to the original addressed $P/S$ dispatcher:

| Request | Actual successor | Complete semantic reply |
| --- | --- | --- |
| Read | $x$ | the literal original-root value $e^{\mathsf T}x$ |
| Add$(q)$, $q\in\mathbb Q$ | $x+qe$ | fixed ACK |
| Tick | $A_u x$ for the current material tree $C(u)$ | fixed ACK |
| Hold | $x$, with no autonomous evolution during local work | fixed ACK |
| $P_p$ at logical alpha | retain $p$, add a fresh zero marker $pL$ | Growth$(P,p)$ |
| $S_p$ at logical beta | retain $p,pL$, add fresh zero cells $pLL,pR$ | Growth$(S,p)$ |

At a split, $pL$ becomes the left logical beta root and $p$ becomes a branch; all old fields and old material addresses persist. These are the original material edits, not grafts or surrogate operations. A growth request at an absent address, branch, or wrong leaf type returns, respectively, AbsentRefusal, BranchRefusal or WrongTypeRefusal, with identical material and field successor. There is no Reset. Tick has no scalar payload. There are no terminal labels or terminal ports, constructor Read, interior-coordinate Read, size port, old-journal port, inverse Tick, clone or response table. In particular, this is an added internal-root Add/Read installation, not the unchanged original terminal-only installation of NLBA II §17.

**Assumption 34.2 (actual preparation, binding and service).** The source was actually allocated as a zero-field alpha and grown by the original $P/S$ operations. Finite rational root controls may prepare its entry field. Before attachment, every construction- or field-dependent producer record is cleared or isolated from the receiver's accessible state: operands, old input/output and parser buffers, caches, selectors, callable archives and observable layout/capacity distinctions are not alternative advice channels. Clearing/isolation and its authority are explicit handoff premises, with actual work charged. Any producer, observer or caller copy retained elsewhere is real additional storage. The receiver begins with the source-independent program, one authentic binding to the original root dispatcher, the original left/right orientation, current call and rational-input rights, and the fixed interface and class assurance. A reference is an actual binding, not a number cast into an object. These premises do not reveal $n$ or certify an unknown field by fiat.

Calls, output consumption and local updates are serial. Only an actual Tick evolves the field; growth adds fresh zeros without a hidden Tick. Hold permits the finite computations below on this very specimen. There is no competing writer, crash or revocation during a stated completed execution. Exact rational arithmetic, full replies, finite work storage, output backing and sufficient finite fresh material for each enabled requested growth are supplied. Allocation exhaustion, elapsed time, allocator identities, work and capacity metadata are not observation ports in this task. If such outputs are added, their state and costs must be added too. There is no common finite capacity or lifetime-width bound. Genuine installation, calibration, provenance and authority are premises; a matching numerical record cannot prove or grant them.

For specificity, the growth channel retains AA Definition 20.2's designated three-bit $P/S$ tags, address code $1^{|p|}0p$, three-bit reply tags, two-bit refusal reason and kind/address Growth payload. Other complete growth-channel requests are unsupported and return BadFrame; AA's Tag and history-tape queries are not installed. A separate field channel has fixed three-bit tags for Read, Add, Tick and Hold. Only Add has a payload. For $k\ge0$, encode $k$ as $1^{\ell(k)}0\operatorname{bin}(k)$, where $\ell(k)=|\operatorname{bin}(k)|$ and $\operatorname{bin}(0)=0$. A reduced rational $p/q$, $q>0$, is a sign bit and the codes for $|p|,q$; negative zero and noncanonical fractions are invalid. Field replies have fixed two-bit tags for ACK, rational or BadFrame. Each input packet and output has an explicit End delimiter. A proper unfinished prefix without End remains pending; premature End, excess payload, an unsupported tag or an invalid complete rational packet yields BadFrame without an inner source operation. Missing current rights or an unavailable service phase disables the corresponding primitive; it is not a completed refusal or ACK. Root Read/Add have no ordinal parameter and hence no RangeRefusal branch. All bits, delimiters, local acknowledgements, cursor return and cleanup are real operations with backing and charges.

## 35. The original unit comb supplies the missing root rank

**Theorem 35.1 (cyclicity in the original material coordinates).** For every $n\ge0$, with exactly the material and unit law of Definition 34.1,

$$
K_n=[e,A_ne,\ldots,A_n^{N_n-1}e]
\quad\hbox{is invertible over }\mathbb Q.
\tag{UFS.83}
$$

Consequently the $N_n$ original-root observations at successive Tick epochs distinguish every pair of rational fields on this fixed comb. This conclusion does not require the unknown entry field itself to be cyclic, and does not assert that $A_n$ is invertible.

Proof. Write $p_n(z)=\det(zI-A_n)$, and let $q_n(z)$ be the characteristic polynomial after deleting the original root; the empty determinant is one. The initial polynomials are $p_0=z,q_0=1$. At the root of $G_{n+1}$ the left attached component is the two-vertex beta material, whose characteristic polynomial is $z^2-1$ and whose own root-deleted polynomial is $z$; the right component is $G_n$. The elementary rooted determinant expansion therefore gives

$$
q_{n+1}=(z^2-1)p_n,\qquad
p_{n+1}=z(z^2-2)p_n-(z^2-1)q_n.
\tag{UFS.84}
$$

For clarity, the root expansion is
$z(z^2-1)p_n-zp_n-(z^2-1)q_n$: either the root is unmatched in the determinant expansion or it uses one of its two incident edges. One can also obtain it by a root block Schur complement away from the finitely many component eigenvalues and then use polynomial equality. Thus it applies at all $z$, including those eigenvalues.

At $z=1$ or $z=-1$, the recurrence says $p_{n+1}(z)=-zp_n(z)$, so these two values are never zero. Inductively $p_n,q_n$ have no common complex root: this is true initially; a common root $\lambda$ of $p_{n+1},q_{n+1}$ is not $\pm1$, hence $p_n(\lambda)=0$ by the first equation, and $q_n(\lambda)=0$ by the second, a contradiction.

Now apply the classical rooted walk-matrix criterion: a vertex of a real symmetric graph is controllable precisely when its characteristic polynomial is coprime to that of its vertex deletion. This is Godsil, *Controllable Subsets in Graphs*, [arXiv:1010.3231v1, Lemma 5.2](https://arxiv.org/html/1010.3231v1), with the root as the one-vertex subset. Its application here can be checked directly. If the span $W$ of the columns in (UFS.83) were proper, Cayley–Hamilton would make $W$ invariant under $A_n$; symmetry makes $W^\perp$ invariant too. The real symmetric restriction to nonzero $W^\perp$ has an eigenvector $v\ne0$. Since $e\in W$, its root coordinate is zero. Deleting that coordinate leaves a nonzero eigenvector of the root-deleted matrix with the same eigenvalue. This contradicts the coprimality just proved. Hence $K_n$ is nonsingular over $\mathbb R$, and its integer determinant is nonzero, so it is nonsingular over $\mathbb Q$.

Symmetry identifies the observability matrix as

$$
O_n=\begin{pmatrix}e^{\mathsf T}\\e^{\mathsf T}A_n\\\vdots\\e^{\mathsf T}A_n^{N_n-1}\end{pmatrix}
=K_n^{\mathsf T}.
\tag{UFS.85}
$$

Thus equality of all $N_n$ observations is exactly $K_n^{\mathsf T}(x-x')=0$, and implies $x=x'$. $\square$

This is a source-specific application of the classical criterion, not a new abstract controllability criterion. Native comb construction is already public, for example AA II Theorem 50.4's all-beta left comb. Formula (UFS.82) explicitly chooses an alpha-ended right spine from the same original local templates; neither combs nor their legal local construction are claimed as new general content. The new rank bridge concerns this family's unmodified unit adjacency and original internal root. No separated address potentials from Recovery Geometry II §§96–98 enter (UFS.84).

## 36. Unknown size earned by original refusals

**Definition 36.1 (the finite comb guard).** Actually Hold. Start with logical address $p=\varepsilon$ and counter $j=0$. Issue $S_p$ and consume its complete reply. On BranchRefusal, issue $P_{pL}$, require WrongTypeRefusal, increment $j$, replace $p$ by $pR$, and repeat. On WrongTypeRefusal to $S_p$, stop and accept exactly if $j\ge3$. Every other reply rejects. In particular, a successful Growth reply is consumed and causes rejection; it is not retrospectively converted into a refusal or rolled back.

**Theorem 36.2 (actual unknown-size class acquisition).** On every admitted $u_n$, the guard terminates, accepts, earns exactly $n$, and leaves the whole field and material unchanged. It makes $n+1$ actual $S$ requests and $n$ actual $P$ requests, all refusals. Conversely, on any finite native term, acceptance of the guard entails that the term at attachment was exactly $u_j$, $j\ge3$, and no growth occurred in that accepted execution. There is no size advice or fixed search horizon.

Proof. At a branch $p$, $S_p$ returns BranchRefusal. At its left logical child, WrongTypeRefusal to $P$ means exactly beta: alpha would grow, a branch has its distinct refusal, and an absent address has its distinct refusal. At an alpha $p$, $S_p$ returns WrongTypeRefusal. At a beta $p$ it grows and is rejected. Hence an accepting path has precisely a finite right spine of branches, a beta left child at each, and an alpha end. Induction back up this spine reconstructs exactly (UFS.82), with $j$ branches. All replies used in acceptance are identity refusals; Hold also preserves the field. Conversely $u_n$ supplies these exact replies, so the counter stops at $n$. A finite term has a finite right spine, so every iteration either descends strictly or terminates/rejects. This proves termination even off the class, but a rejecting off-class execution can already have grown. No nondestructive rejection or restoration promise is made off the accepted class. $\square$

The addresses are lawful selections constructed from the actual accepted replies, not a supplied list of the unknown source's vertices. From the earned $n$ the controller constructs the finite term, material-address table, $A_n$, $e$, $K_n$ and its rational inverse. Its authentic original-root dispatcher remains bound throughout. A source-dependent constructor oracle is not being smuggled into the guard.

## 37. Arbitrary entry, actual preparation and an earned new origin

**Theorem 37.1 (uncapped arbitrary-entry acquisition on the comb).** Under §§34–36, one source-independent finite program terminates for every $n\ge3$ and every $x^0\in\mathbb Q^{N_n}$, earns the original unit comb and its exact entry field, and establishes the actual new origin $e$ on the same source. From attachment to this origin it uses no Reset and no successful growth. With $N=N_n$, its actual primitive counts, in the order $(P,S,\mathrm{Tick},\mathrm{Add},\mathrm{Read},\mathrm{Hold})$, are

$$
(n,n+1,\ 2N-1,N+1,N+1,2N+1).
\tag{UFS.86}
$$

At the returned cut it retains a synchronized full-field predictor, the authentic callable binding and current rights. The entry-field report is not a restoration of that field or of its old control history.

Proof. Run the guard. Its initial Hold is retained as the hold for the first observation. Read $y_0$. For $j=1,\ldots,N-1$, actually Tick, Hold and Read $y_j$. All Tick ACKs and scalar replies are consumed. There have been no Adds and no growth, so

$$
y_j=e^{\mathsf T}A_n^j x^0,\qquad
y=K_n^{\mathsf T}x^0,\qquad
x^1=A_n^{N-1}x^0.
\tag{UFS.87}
$$

Solve $\widehat x^0=K_n^{-\mathsf T}y$, which equals the actual attachment field by Theorem 35.1. Compute $x^1$ by forward powers. This is the actual current field; it is not $x^0$. Keep the source held during computation.

Compute the rational coefficient vector

$$
c=-K_n^{-1}A_n^N x^1.
\tag{UFS.88}
$$

For $i=0,\ldots,N-1$, actually execute Tick; Add$(c_{N-1-i})$; Hold, consuming every ACK and updating the retained predictor. Induction on these rounds gives the actual endpoint

$$
A_n^N x^1+\sum_{i=0}^{N-1}c_{N-1-i}A_n^{N-1-i}e
=A_n^N x^1+K_nc=0.
\tag{UFS.89}
$$

Now actually Add$(1)$; Hold; Read. The complete field is $e$ and the literal Read is one. The read alone would not certify whole-field zero or $e$; (UFS.87)–(UFS.89), the cyclicity and the installed exact law prove the full-field statement. Zero, signed, noncyclic and arbitrarily large entry fields all obey the same argument. No inverse of $A_n$ has been used.

There are $N-1$ observation Ticks and $N$ control Ticks, $N$ control Adds and the final unit Add, and $N$ observation Reads and the final Read. The initial Hold and the $N-1$ observation Holds total $N$; controls add $N$ and the final origin adds one. Together with Theorem 36.2 this is (UFS.86). Every matrix operation, addressed loop and finite output terminates at this finite $n$ and these finite rational widths. The program is uniform in the unknown $n,x^0$. $\square$

**Proposition 37.2 (every rational entry has genuine native preparation).** For every $n\ge3$ and target $z\in\mathbb Q^{N_n}$, the installed source can actually be prepared from one allocated zero alpha, using the original native edits and root controls, to attachment at exactly $(u_n,z)$. One such producer makes $n$ successful $P$ and $n$ successful $S$ calls, then $N$ Ticks, $N$ Adds and one Hold. Thus Theorem 37.1's arbitrary-field class is not an assumed family of unconstructible initial states.

Proof. At $p=R^j$, for $j=0,\ldots,n-1$, execute $P_p;S_p$. The target was alpha, becomes beta, and splits into the required left beta and next right alpha. Induction constructs exactly $u_n$ and leaves every field zero, by the persistent fresh-zero templates. Compute $b=K_n^{-1}z$. Execute $N$ rounds Tick; Add$(b_{N-1-i})$, $0\le i<N$, then Hold. The actual endpoint is $K_nb=z$. The producer knows its owned construction target and supplies the actual controls; the receiving controller is given neither that target nor those coefficients. References, grants, allocations, preparation control traffic and producer storage are real resources. Combining this producer with (UFS.86) gives the same-run counts

$$
(2n,2n+1,\ 3N-1,2N+1,N+1,2N+2)
\tag{UFS.90}
$$

from the allocated alpha through acquisition to the new origin. A different authentic preparation can have a different bill and old chronology; (UFS.86) still applies from its attachment cut. $\square$

The linear-control step is the already used control-to-origin mechanism of this volume §5, now supplied with $A_n,e$ and an earned invertible $K_n$. The new application earns the unknown dimension through original refusals and measures an arbitrary entry by root-only Read with ACK-only Tick; it neither assumes the earlier capped positive Jacobi law nor silently inherits its scalar-returning Tick.

## 38. Root sampling of the restricted binary continuation

**Definition 38.1 (the actual binary phase).** At the actual new origin of Theorem 37.1 keep the comb fixed. A binary request supplies a real bit $d\in\{0,1\}$. Next$(d)$ executes Tick; Add$(d)$; Hold; Read, including an actual Add$(0)$ when $d=0$, and returns the three ACKs and literal rational reply in that order. Write $w=d_0\cdots d_{m-1}$ for the binary input chain actually executed since this origin. Its field is

$$
x_w=A_n^m e+\sum_{i=0}^{m-1}d_iA_n^{m-1-i}e,\qquad
x_{wd}=A_nx_w+de.
\tag{UFS.91}
$$

The empty chain has field $e$. There is no growth, extra Tick, nonbinary Add or Reset in this phase. Read and Hold are permitted identity operations. No old binary word or length must be retained as the inverse's input. The current full predictive vector and the earned finite graph can be retained; their actual storage is charged.

**Theorem 38.2 (the public binary supplier applies at the internal root).** The fields (UFS.91) distinguish all finite binary chains, including length and the empty chain. A sequential finite-word enumeration recovers the unique chain from any full field promised to be in this image. It is not asserted to halt off the image.

Proof. Apply NLBA II Theorem 30.2's leading-term separation mechanism to this actual graph and seed. Its graph hypothesis is satisfied: $G_n$ has $n+1\ge4$ material leaves, maximum degree three, and exactly $n-1\ge2$ degree-three vertices. Its seed was a canonical terminal there; the proof's actual seed requirement is the strict positivity of the pairing below, which also holds at this installed internal root.

In detail, choose two degree-three vertices and their joining path. Give each path vertex weight two, their four off-path endpoint neighbours weight one, and other vertices zero, obtaining $g$. A tree makes these four neighbours distinct and outside the path. At path vertices the neighbouring weight sum is at least four, and at the four selected neighbours at least two; hence $A_ng\ge2g$. Set $h=(I+A_n)^{N-1}g$. Every vertex reaches a positive coordinate in at most $N-1$ edges, and the identity terms pad paths, so $h$ is strictly positive and integral. Commutation gives $A_nh\ge2h$. In particular, for the actual original-root $e$,

$$
s_j=h^{\mathsf T}A_n^je,\qquad
s_0=h_{\varepsilon}>0,\qquad
s_{j+1}\ge2s_j,\qquad
s_D>\sum_{j<D}s_j\quad(D\ge1).
\tag{UFS.92}
$$

The last inequality follows by bounding $s_j\le2^{j-D}s_D$ and summing the finite geometric series. For a nonzero polynomial $P(z)=\sum_{j\le D}a_jz^j$, $a_j\in\{-1,0,1\}$, its leading $h$-pairing has absolute value $s_D$ and all lower pairings have total absolute value strictly smaller; when $D=0$, use $s_0>0$. Thus $P(A_n)e\ne0$. Distinct binary chains give distinct monic polynomials in (UFS.91), whose difference has those coefficients, so their fields are distinct. Enumerating chains by increasing length and lexicographic order, computing each finite field and comparing all coordinates reaches the unique match on the promised image. Neither $h^{\mathsf T}x$ nor a past-word query is an installed port. This verifies the changed seed hypothesis in the credited supplier; it supplies no sharp leaf threshold or new general numeration theorem. $\square$

**Definition 38.3 (literal root Sample).** At an actual binary-image field $x_w$, execute Hold; Read, then $N-1$ rounds Tick; Add$(0)$; Hold; Read. Store the literal ordered scalar window $y_0,\ldots,y_{N-1}$. Decode its pre-window vector using $K_n^{-\mathsf T}$ and then apply Theorem 38.2. Sample returns all inner replies, the window and the decoded pre-window chain and length, with every exported copy charged. The local predictor is installed at the actual final field, not at the reconstructed pre-window field.

**Theorem 38.4 (sample recovery and endpoint).** For every promised $w$, Sample terminates and simultaneously satisfies

$$
y=K_n^{\mathsf T}x_w,\qquad
x_w=K_n^{-\mathsf T}y,\qquad
x_{\rm return}=A_n^{N-1}x_w=x_{w0^{N-1}}.
\tag{UFS.93}
$$

Its actual counts are $N-1$ Ticks, $N-1$ Adds, $N$ Holds and $N$ Reads. All Add inputs are zero. The returned predictor equals $x_{w0^{N-1}}$ even if the pre-window predictor and binary journal had been discarded before sampling.

Proof. The $j$th actual sampled field is $A_n^jx_w$: Read and Hold preserve it, and the actual zero Adds also preserve it. Its root value is the $j$th row of $K_n^{\mathsf T}x_w$, giving the first two identities. Theorem 38.2 recovers $w$. Each intervening Tick with its zero Add is an actual binary zero pulse, proving the third identity. Compute the retained endpoint by $N-1$ forward multiplications of the recovered vector. These are computations, not inverse Ticks or extra source calls. Counts follow from the specified sequence. In particular, no inversion of possibly singular $A_n$ is needed to recover the pre-window vector from this full window. $\square$

## 39. Four independent meanings at completed sampled cuts

**Definition 39.1 (the sampled four-expression domain).** Consider completed Sample cuts of the fixed comb binary phase, after every input, reply and predictor update has finished and the controller has returned to Ready. Put $v=w0^{N-1}$ for the actual binary chain including the last Sample's zero pulses. The four expressions expose the following different objects.

| Expression | Independently specified content |
| --- | --- |
| Space | The actual rooted ordered unit material tree and its current field $x_v$, modulo rooted order-preserving isomorphism |
| Time | The actual successful labelled native generation projection, and the actual binary pulse chain $v$ since the earned origin |
| Boundary | Only the framed ordered list of $N$ literal root values received in the last Sample |
| Memory | The retained current recursive native term and current full predictive field $x_v$ in its material-address coordinates |

Space does not contain a command journal; Memory does not contain a binary word or an old-history oracle. Boundary is a finite actual window, not a table of arbitrary future responses or a counterfactual full-field measurement. Time's generation projection includes only actual successful original $P/S$ events. For this comb it is the forced chain

$$
P_{\varepsilon}S_{\varepsilon}P_RS_R\cdots
P_{R^{n-1}}S_{R^{n-1}}.
\tag{UFS.94}
$$

Time excludes old field preparation, acquisition, nulling, refused requests, Reads, Holds, waiting and wrapper segmentation. Two zero pulses issued as Next requests and two zero pulses inside a Sample are not distinguished by this Time expression. It is an event projection with this stated meaning, not the total old serialization or a claim about elapsed physical time. These exclusions are necessary to the inverse statement.

The common callable context consists of the actual original-root binding and orientation, current rights, the source-independent codec/program, available backing and the authentic installation and binary-origin promises. It is not a hidden second copy of $n$, the term, window or word supplied to each expression. When an expression is used as the sole numerical input, missing finite arrays are reconstructed from it. Numeric reconstruction never reconstructs a grant. The actual joint process may retain the predictive arrays and last window simultaneously, paying for both. Receiving an exported numerical expression without its lawful context does not authorize calls on its source.

**Theorem 39.2 (all inverses and all routes on the sample image).** On Definition 39.1's domain, each of Space, Time, Boundary and Memory determines the other three. Every round trip is the identity up to the stated spatial isomorphism, and every route with the same endpoints agrees. The common recovered parameters are exactly $(n,v)$ with $n\ge3$ and $v$ ending in at least $N_n-1$ zeros.

Proof. First, (UFS.94) is the actual generation projection, not a chosen replay. A branch at $R^j$ had to be created by its $S$ event, before any event at $R^{j+1}$. That right child was born alpha and needs its $P$ before its $S$. Each left beta is born beta and never changes in $u_n$. Original growth has no deletion. Thus these are all and only the successful generation events, in this forced order, even if field operations or refusals occurred between them. This also follows by applying AA Theorem 17.2's labelled causal order to $u_n$.

From Space, count its $N$ vertices to obtain $n=(N-1)/3$ and parse the rooted ordered material by arity: zero children is alpha, one terminal left marker is beta, and two children is a branch recursively. The marker is consumed in the beta clause. This yields $u_n$ and the canonical coordinates without choosing a spatial embedding. Use Theorem 38.2 on the actual present field to recover its unique chain $v$. Memory supplies the same term and coordinate field, so yields the same $n,v$. From Time, the generation chain yields $n$ and $u_n$ and its second component is $v$ itself; evaluating (UFS.91) gives the present field. No old field-control chronology is inferred in any of these directions.

From Boundary, count the actually framed $N$ values; this is the extent of a performed Sample, not initial order advice. Recover $n=(N-1)/3$, construct its actual-class $A_n,K_n$, and solve $x_w=K_n^{-\mathsf T}y$. Theorem 38.4 identifies this as the pre-window field. Theorem 38.2 recovers $w$; append precisely $N-1$ zeros to obtain the present $v$ and evaluate its field. This establishes Boundary to every other expression, with the actual advanced endpoint.

Conversely, given the recovered $(n,v)$, remove exactly its last $N-1$ zeros to obtain $w$. This removal is unambiguous on the declared domain, including when the word has additional trailing zeros. Form $K_n^{\mathsf T}x_w$ and serialize it in the installed rational framing. By (UFS.93) this equals the last literal window numerically and byte-for-byte in the canonical codec. This computation reproduces the record; it is not another Read or a proof of physical provenance. Build Space and Memory from $(u_n,x_v)$, and Time from (UFS.94) and $v$. Each recovered value is equal to its independently defined actual expression.

Every such $(n,v)$ is actually attainable: prepare its comb by Proposition 37.2, run Theorem 37.1 to the actual origin, execute Next on the bits of the stripped word $w$, and actually Sample. Theorem 38.4 gives precisely $v=w0^{N-1}$. Thus the stated parameter set is the joint actual image, not merely four separately realizable numerical images.

These constructions make every expression encode and decode the same $(n,v)$. The decoding after encoding is the identity by binary injectivity, the sample identity and unique ordered material parsing. Thus any two compositions recover the same parameters and re-encode the same target expression, proving every directed inverse, round trip and route agreement. All computations terminate on this image. $\square$

**Proposition 39.3 (dynamics and the source-service kernel).** The sampled domain is stable under any finite sequence of Next requests and Reads/Holds followed by another Sample. On that domain the four expressions determine the same content state for the root/native continuation task, relative to their common lawful context. This equivalence does not extend to arbitrary archives, authority states, noisy measurements or wrapper histories.

Proof. From a sampled chain $v$, Next$(d)$ produces $vd$ by (UFS.91). Read/Hold preserve it. The next Sample appends exactly $N-1$ actual zeros. Hence its new expressions are precisely those of Theorem 39.2 at the new chain; decoding before, updating by these actual operations and encoding after agrees with observing the resulting expression directly.

Here continuation equivalence quantifies over common future input policies with the same retained selector context; it does not silently compare callers holding different old archives. For a fixed earned $n$, equal present fields give equal outputs and successors under every such finite root/native continuation by Theorem 40.2 below. Unequal fields are distinguished by an actual root window: invertibility of $K_n^{\mathsf T}$ forces at least one of its $N$ Read values to differ. If two comb sizes $n<m$ are compared under a binding-preserving correspondence of otherwise equal lawful contexts, the actual request $S_{R^n}$ returns WrongTypeRefusal on $u_n$ and BranchRefusal on $u_m$, changing neither source. Thus the primitive continuation equivalence, with the declared scalar and refusal outputs, is exactly equality of $n$ and the present field. On the binary image, equality of that field is exactly equality of $v$ by Theorem 38.2. This establishes agreement of the four-expression equivalence with this content task.

Extra exposed archives, pointer-identity tests between unrelated bindings, capacity metadata or differing rights enlarge the task and need their own retained state. They are not numerical consequences of $(n,v)$. Growth or arbitrary rational controls can leave the sampled inverse domain; the forward predictor still serves them as stated next. $\square$

## 40. Lawful selectors and complete continued source service

**Definition 40.1 (the retained callable state).** At the origin and every later completed cut retain the real source binding, current rights and phase, the acquired current recursive term, its material-address-to-coordinate table, the unit adjacency representation and the exact current predictive vector $\widehat x$. Retain separate scratch for a Tick or growth update, parser and actual pending bits, finite counters, output backing and return cursor. The initialization is $\widehat x=e$ in Theorem 37.1; at a sampled return it is the advanced field in (UFS.93).

The guard selector is the actual backed address $p$ and counter. Preparation controls are actual computed rational coefficients in reverse order. Next's bit is received and backed before use. A future growth address or rational operand is an actual received finite packet, not a hidden selector oracle. A finite adaptive caller can use previously returned actual outputs and its own retained inputs; its records and selection work are charged. No part of this definition supplies an arbitrary native tree as free input to a numerical inverse.

The service forwards actual calls on the retained binding and consumes the entire actual reply. It updates and commits the local record before exposing the next completed cut. Its exact primitive prediction and record updates are:

| Case | Complete output | Committed numerical/material successor |
| --- | --- | --- |
| Read | literal rational $e^{\mathsf T}\widehat x$ | identity |
| Add$(q)$ | ACK | $\widehat x+qe$ |
| Tick | ACK | $A_u\widehat x$ |
| Hold | ACK | identity |
| enabled $P_p$ | original Growth$(P,p)$ | original term edit, old-coordinate values retained, fresh $pL$ zero |
| enabled $S_p$ | original Growth$(S,p)$ | original term edit, old-coordinate values retained, fresh $pLL,pR$ zero |
| absent, branch or wrong-type growth target | corresponding distinct original refusal | identity |
| complete malformed/unsupported packet | BadFrame | no inner operation; identity source |
| proper incomplete packet | no completed reply | its real acquired prefix and pending parser state |
| missing rights or unavailable phase | no completed reply; primitive disabled | no primitive source transition |

After growth, rebuild the finite material table and adjacency on the actual old-vertex inclusion, retaining the original root coordinate and real dispatcher binding. No field is read at a newly created internal coordinate; fresh zeros come from the installed growth law. A BadFrame consumes the malformed packet and returns to Ready after output and cleanup; an incomplete packet does not. A disabled invocation is not silently replaced by a tagged refusal. Pending source edits, outputs and returns are real phases, not extra completed cuts. There is no range branch for root-only Read/Add, and every unsupported constructor, history, Reset or terminal-label request is covered by the malformed/unsupported row, not an invented auxiliary port.

Valid Next and Sample wrappers expose their complete ordered inner replies and computed results. For a fixed codec, use three-bit request tags for Next, Sample, Recall and Length; Next has one bit payload and the others none. Other tags or excess payload are BadFrame. Each reply has a fixed three-bit result tag, a list of length-delimited complete inner reply frames and its typed result payload. Encode every list/frame length by Assumption 34.2's nonnegative-integer code; encode a word by its coded length followed by its actual bits. Next has no further result beyond its four inner replies. Sample appends the coded list of its $N$ canonical rational values and the pre-window word and coded length. Recall appends the decoded word, and Length its coded length. BadFrame has no inner frames or result payload. Outer End, local acknowledgement and Return complete each enabled wrapper. Invalid complete wrapper input returns BadFrame without inner calls, and a proper prefix remains pending. Optional Recall and Length are admitted only while the binary-origin promise is maintained: actually Hold, enumerate from the current predictive field as in Theorem 38.2, and return that ACK followed by the decoded current chain or its length. These are backed computations after an actual Hold, not a source word oracle. On arbitrary controls or growth the wrapper admission flag is cleared; no off-image termination claim is made. Read/Hold and the admitted binary wrappers preserve it.

**Theorem 40.2 (complete adaptive use on the same actual source).** For every finite enabled continuation after Theorem 37.1, including arbitrary rational controls and all original growth requests, the retained service predicts every complete declared reply and the matching full source successor. Each complete enabled finite packet returns through finite output, End, local acknowledgement, root return and cleanup to Ready. At every such cut,

$$
\widehat u=u_{\rm actual},\qquad
\widehat x=x_{\rm actual}
\quad\hbox{in the retained actual material coordinates}.
\tag{UFS.95}
$$

The stated incomplete and disabled behaviours also agree. Numerical predictions never replace the genuine calls or create the required current authority.

Proof. The base is Theorem 37.1. For a primitive, use the installed operation in Definition 34.1. Add and Tick obey their displayed linear updates for every rational field, without a binary promise; Read and Hold preserve it and have the stated outputs. At a legal growth, the known term selects exactly the original guard's enabled target. Its persistent old fields and fresh zeros are exactly the local record update, and its reply is exactly Growth with that actual kind/address. The three distinct refusal conditions are computed from the same logical arity navigation and all preserve the source. These identities preserve (UFS.95), also when the current term has ceased to be a comb. Rebuilding its finite table is a finite traversal of the earned/updated term, not a new measurement or tree acquisition from advice.

For framing, each received bit is copied to actual request backing before its input latch is cleared. The finite parser stores its tag, subphase, length counter and payload; its state is therefore exactly the acquired prefix. End either completes precisely one valid packet or selects BadFrame without dispatch. A valid finite address traversal has finite length, stopping at its actual target or first absent logical edge. The assumed backing supports each finite enabled edit and output. The service seals the real reply backing, transmits precisely its bits and End, takes its supplied local acknowledgement, returns the actual cursor to the root, and clears scratch before Ready. These finite loops finish for complete enabled packets. An incomplete prefix waits with its retained bytes, and a missing right or wrong phase enables no primitive step, exactly as in the installation. These are ordinary finite-list and cursor operations in AA §20's service pattern; its history tapes and extra queries are not assumed here.

Induct over the actual completed requests. Equal prior outputs make the same finite adaptive policy choose the same next received command and operand. The primitive identities and finite parser/return argument preserve both (UFS.95) and every declared output. Wrapper correctness follows by applying the primitive induction to their real inner calls, (UFS.91), (UFS.93), and the promised-image inverse. No speculative forecast is counted as a source observation. Rights, input buffers, caller records and phases remain part of the common process even where the four numerical expressions omit them. $\square$

## 41. Attained calls, literal traffic, simultaneous backing and work

**Proposition 41.1 (one joined call bill).** For the producer of Proposition 37.2 followed by accepted acquisition and origin preparation, the counts are exactly (UFS.90). Subsequent $k$ Next calls, $r$ Sample calls and $q$ admitted Recall/Length calls add, with $a=k+r(N-1)$,

$$
\begin{array}{c|cccc}
&\mathrm{Tick}&\mathrm{Add}&\mathrm{Read}&\mathrm{Hold}\\ \hline
\text{binary continued use}&a&a&k+rN&k+rN+q.
\end{array}
\tag{UFS.96}
$$

Every other future primitive is added at its actual occurrence. No successful growth or Reset is hidden in accepted acquisition or binary sampling. There is no common bound over unknown $n$, arbitrary entry precision, continuation length or requested growth.

Proof. Proposition 37.2 and Theorem 37.1 give their same-source counts before the origin. Next contributes one of each displayed operation. Sample contributes $(N-1,N-1,N,N)$ by Theorem 38.4. Each admitted Recall/Length contributes one actual Hold and no Tick, Add or Read. Summation gives (UFS.96). The number of binary zero/one pulse steps actually executed after the origin is $a$, including all sample zeros; Recall does not add a pulse. $\square$

**Proposition 41.2 (literal communication is not a scalar-count convention).** Let

$$
\rho(p/q)=2\ell(|p|)+2\ell(q)+3,\qquad q>0,
\tag{UFS.97}
$$

for the reduced rational codec in Assumption 34.2. Thus $\rho(0)=\rho(1)=7$. On the fixed bound channels, accepted acquisition has the following exact operation-tag and payload lengths, before End, channel routing, acknowledgement/return machinery and exported report copies:

$$
\begin{aligned}
B_{\rm guard,in}&=2n^2+10n+4,\\
B_{\rm guard,out}&=10n+5,\\
B_{\rm field,in}&=3(6N+2)+\sum_{j=0}^{N-1}\rho(c_j)+\rho(1),\\
B_{\rm field,out}&=2(6N+2)+\sum_{j=0}^{N-1}\rho(y_j)+\rho(1).
\end{aligned}
\tag{UFS.98}
$$

In particular the ACKs are counted: there are $5N+1$ field ACK replies, $N+1$ scalar replies and $2n+1$ distinct-reason growth refusals. The complete number of primitive completions in this acquisition is $C=6N+2n+3$.

Proof. A growth request at depth $d$ has $3+(2d+1)=2d+4$ bits. The $S$ depths are $0,\ldots,n$ and the $P$ depths are $1,\ldots,n$. Their sum is $2n^2+10n+4$. All $2n+1$ growth replies have a three-bit tag and two-bit refusal payload, giving $10n+5$. There are $6N+2$ field calls by (UFS.86), each with a three-bit request tag and a two-bit reply tag. The only request payloads are the $N$ coefficients and final unit. The only reply payloads are the $N$ observed $y_j$ and final literal one. Tick, Add and Hold give $5N+1$ ACKs; Read gives $N+1$ scalars. Summing the completed calls gives $C$. $\square$

For the chosen producer alone, its growth request bits total $2n^2+6n$, and its Growth reply bits total $2n^2+8n$: each of the two calls at depth $j<n$ returns $3+1+(2j+1)=2j+5$ bits. Its field operation tags and reply tags total $5(2N+1)$ bits and its control payloads total $\sum_j\rho(b_j)$. Its $2n+2N+1$ completions, the actual initial allocation and every producer-to-receiver transfer have their additional charges. This producer bill is joined to (UFS.98), not replaced by a free arbitrary seed.

For the continuation in (UFS.96), let $C'=4k+r(4N-2)+q$ be its inner field completions. Their tags contribute $5C'$ bits; their actual binary Add payloads contribute $7a$ bits; and their literal Read payloads contribute the sum of $\rho$ over the $k+rN$ actually returned values. Wrapper input tags, the received $k$ bits, wrapper lengths, decoded words/lengths, windows, entry-field reports and any copied scalar tuples are additional literal transmissions. In particular, returning $x^0$ means transmitting its $N$ rational entries, not merely naming its computed vector.

A complete traffic account for any of these finite runs is the sum

$$
B_{\rm run}=B_{\rm operation\ tags/payloads}
+B_{\rm Ends/routing/local\ acknowledgements/return}
+B_{\rm bindings/grants/setup/input\ capture}
+B_{\rm wrappers/reports/copies}.
\tag{UFS.99}
$$

Each term is the sum of the actual encoded lengths moved in that category, with one chosen counting boundary so the same transmission is not counted twice. The second term includes exactly one input End, output End, local completion acknowledgement and Return sequence for each completed primitive, hence $C$ such sequences in (UFS.98), and the corresponding sequences for the producer and $C'$ continuation calls. Add the $k+r+q$ outer wrapper completion sequences; their inner completions do not pay for them. Proper incomplete packets contribute their actual received prefix and parser/backing traffic without a fictitious completion sequence. Disabled calls contribute only the actual input/control activity that occurred. Binding and grant widths, routed reference traffic and actual return-cursor operations are supplied implementation resources, not assumed one-bit or unit-size names. A local edge that carries no transmitted bits still incurs its local operation and retained-state cost. Formula (UFS.99), together with (UFS.98), specifies what must be counted without assigning a fictitious numerical width to an unspecified physical reference. Caller archives and repeated exported copies are charged where actually retained or moved.

**Proposition 41.3 (finite implementation with unbounded literal widths).** For each finite admitted run the algorithms above use finite backing and work. They can be implemented with $O(N^2+m+1)$ simultaneous scalar/digit slots during acquisition and a promised binary inversion of length at most $m$, besides the explicit structural, reference, parser, output and retained-copy backing. This slot statement gives no bound on their literal widths and no efficient word inverse.

Proof. Build $K_n$ by $N-1$ sparse powers and invert by rational elimination. Retain the source's $N$ field cells and its distinct next-Tick buffer, the observer's $N$ predictive cells and its separate update buffer, $K_n,K_n^{-1}$, the current window, control and reconstruction vectors, and elimination scratch. For example, a layout allocating at most $4N^2+24N$ scalar slots for these source/observer arrays suffices: two $N$-square stored matrices, a separate $N$-by-$2N$ elimination array, and twenty-four length-$N$ vectors more than cover the stated fields, snapshot buffers, right-hand sides, controls, windows and temporary products. Unused slots can be reused, but cannot be declared absent while their values coexist. This count is for these arrays, not for arbitrary retained caller output copies.

A sequential word enumerator needs one candidate word and vector, its length/lexicographic counters, comparison scratch and the eventual output, rather than all candidates at once. For a length-$m$ promised answer, at most $2^{m+1}-1$ candidates are reached, each of length at most $m$. Their words and counters use $O(m+1)$ digit slots; no retained old-word input is needed. The material table has $N$ addresses of length at most $n+1$, hence $O(N^2)$ address bits in an explicit-word representation, or actual backed links with their real reference widths. Term storage, the actual source edges, grants, pending packets, output buffers, program/control, returned arrays and any archives remain simultaneous additional stores. Future growth adds its actual new cells and updated backing.

For work, a unit-tree Tick implemented by a frozen snapshot, one zero initialization per target cell and one directed addition per incident edge uses $N$ initializations and $2(N-1)$ scalar additions. This provider computation and the observer's separate sparse prediction both cost work; the ACK does not make the field update free. The $N-1$ powers constructing $K_n$ take $O(N^2)$ scalar additions. Elimination and dense products can be performed in $O(N^3)$ rational arithmetic operations; the powers and products for (UFS.87)–(UFS.89) are within that bound. A direct candidate evaluation by (UFS.91) takes $O(N(m+1))$ scalar operations, so sequential inversion has the attained bound $O(N(m+1)2^{m+1})$ scalar operations, in addition to graph construction and acquisition. This exponential bound is not an efficiency assertion. Each actual invocation is charged, including repeated inversions in different wrappers. With direct root-based dispatch the guard makes exactly $n(n+1)$ downward address steps and $n(n+1)$ return upward steps, since its request depths sum to $n(n+1)$. Each step incurs its actual reference-field loads, arity/identity tests and cursor assignment, at the real widths. There are $2n+1$ target guard decisions and one dispatch/current-authorization check for each of the $C$ acquisition primitives; field calls require no logical address walk. Input/output, backing allocation, copying, root-register uses, return and cleanup add their actual finite work. Growth outside the frozen phase uses the then-current size, not the old $N$, in its rebuilt table and future Tick bills.

Let $W_{\rm run}$ be the largest numerator, denominator, digit counter or intermediate integer bit length actually needed by the chosen implementation up to that finite cut, including elimination, unreduced intermediate products and decoding scratch. It is finite. School integer arithmetic and Euclidean normalization give, for example, a conservative polynomial $O(W_{\rm run}^3)$ bit-work bound per rational operation when all its intermediates are included in this width, in addition to literal traversal/copy costs. Matrix slot counts must therefore be multiplied by actual encoded widths to obtain bits. There is no size-only bound on $W_{\rm run}$ over arbitrary $x^0$: even at a fixed comb, one entry can have an arbitrarily long numerator or denominator.

After the new origin the fields are nonnegative integers. If $M_j$ is their largest coordinate after $j$ actual binary pulse steps, $M_0=1$ and $M_{j+1}\le3M_j+1$, hence $M_j<3^{j+1}$. Their field-coordinate widths are $O(j+1)$ for this fixed degree bound. Conversely along the all-zero chain, $h^{\mathsf T}x_{0^j}=s_j\ge2^j h_{\varepsilon}$ by (UFS.92). Thus its largest coordinate is at least $2^jh_{\varepsilon}/\sum_vh_v$, forcing unbounded width even at this fixed $N$. Actual sampling advances this same $j$ and is included. A finite program, a fixed number of field coordinates and a finite execution are therefore all compatible with unbounded lifetime memory demand. $\square$

Relative to this task, original native construction of $u_n$ really needs the $n$ promotions and $n$ splits of (UFS.94), since they are its forced successful events. With only Tick, Read, Hold and fresh-zero growth, a zero field remains zero; reaching the nonzero earned origin therefore needs a genuine field input. With no Read, the ACK and growth outputs in this installation carry no field information, so arbitrary entry-field reporting cannot be obtained from them alone. These facts justify resources actually used, not the optimality of the particular nulling schedule, protected-work Holds, guard or enumeration.

The comparison with public NLBA II Sample is a vector comparison between different installed ports. On the same comb, its all-leaf window has $b=n+1$, $I=N-b=2n$, and uses $(n+1)(2n+1)$ Reads and $2n$ Ticks. This root window uses $3n+1$ Reads and $3n$ Ticks. One coordinate decreases and another increases; root and leaf actuation/binding also differ. No total-cost dominance, universal minimum or optimum is inferred.

## 42. Concrete counterevidence to stronger promotions

**Proposition 42.1 (original-unit root cyclicity is not arbitrary-native cyclicity).** There is a reachable original native term with an unobservable rational field for root-only fixed-geometry Tick/Read/Add/Hold. Thus Theorem 35.1 cannot be promoted from combs to all native material trees with the same unit law.

Proof. Take $t=\langle\beta,\beta\rangle$, reachable by $P_{\varepsilon};S_{\varepsilon};P_R$. Its material consists of the root, two beta roots and their two markers. In the order root, left root, left marker, right root, right marker, put $z=(0,1,1,-1,-1)$. Directly from the five unit-adjacency row equations, $A_tz=z$ and $e^{\mathsf T}z=0$. The zero field and $z$ therefore have identical root Read histories. Under any common root Add the field difference remains $z$, and under Tick it remains $z$; Hold and Read preserve it. Induction gives identical complete outputs under every finite adaptive root-only continuation with geometry fixed.

Both fields can in fact be prepared with the original growth and root controls alone. Zero needs only the legal growth word. For $z$, first construct $u_1=\langle\beta,\alpha\rangle$. Its four-cell root matrix is cyclic by Theorem 35.1, so four Tick/Add rounds with reversed coefficients $K_1^{-1}(0,2,2,0)^{\mathsf T}$ prepare the field $(0,2,2,0)$. Now execute $P_R$, obtaining $t$ with fresh-zero field $y=(0,2,2,0,0)$. On $t$,

$$
A_t^3y=(6,4,4,2,2),\qquad
A_te=(0,1,0,1,0),\qquad
A_t^2e=(2,0,1,0,1).
$$

The three actual rounds Tick; Add$(-3)$, Tick; Add$(-3)$, Tick; Add$(0)$ therefore end at $A_t^3y-3A_t^2e-3A_te=z$. With one Hold for the coefficient computation and one final Hold, this chosen preparation uses two $P$, one $S$, seven Ticks, seven Adds, two Holds and no Reads. No terminal preparation port is used. Growth after attachment could break the symmetry and is not ruled out as another acquisition method. The obstruction is precisely to the stronger fixed-geometry root-cyclicity assertion. $\square$

**Proposition 42.2 (new origin is not erased-history or old-field restoration).** The recovered expressions do not determine arbitrary field controls before attachment or the entire old serialization. Their actual-source correspondence cannot be replaced by calling the reconstructed entry or pre-window field the returned source field.

Proof. In an old held preparation insert Add$(q)$; Add$(-q)$, $q\ne0$, with no intervening Tick. It changes the actual old command word while leaving exactly the same material and field at attachment. Every later deterministic interface output and every expression in §39 is unchanged. Such an omitted old word therefore cannot be recovered. Moreover (UFS.89) maps every observed entry field to zero and the final Add maps it to $e$. Keeping the computed entry vector as an optional paid report does not perform the physical operations needed to restore it; if that report is discarded, the four origin-based expressions do not retain it. Finally a Sample actually applies $N-1$ Ticks, so its returned state is the last field of (UFS.93), not its first field. The window can recover a pre-window field despite this advance; that algebraic recovery does not reverse the actual advance. $\square$

**Proposition 42.3 (the word inverse is not an arbitrary-field recognizer).** A lawful rational intervention can leave the promised binary image while complete continued source service remains available.

Proof. At the new origin actually Add$(-1)$, obtaining zero. Every field in (UFS.91) has strictly positive $h$-pairing, since it has leading pairing $s_m>0$ and nonnegative remaining pairings. Thus zero is outside the image. The enumerator of Theorem 38.2 never finds zero; no termination promise applies. The forward predictor nonetheless updates to zero and Theorem 40.2 continues to serve every enabled source request. The same separation applies to growth, which changes the graph on which the old inverse was defined. $\square$

**Proposition 42.4 (the unit root does not install a rational endpoint path or grant).** Matching even the first three root impulse moments of this comb by a symmetric positive-link endpoint Jacobi matrix would require an irrational first link. A copied numerical expression also need not carry any callable source right.

Proof. At the actual root seed, $m_0=1$, $m_1=e^{\mathsf T}A_ne=0$, and $m_2=e^{\mathsf T}A_n^2e=2$, the original root's degree. For a symmetric endpoint tridiagonal $J$ with positive first link, these moments require $J_{00}=0$ and $J_{01}^2=2$, hence $J_{01}=\sqrt2\notin\mathbb Q$. A one-cell candidate already fails $m_2=2$. The positive-contraction condition $0<J<I$ fails as well because its root diagonal could not be zero. This refutes that particular exact rational endpoint-law identification; it does not rule out all representations, real-coefficient Lanczos realizations, nonorthogonal simulations or other operational bridges. None would be an installed native/path/quantum equivalence without its actual preparation, operations, outputs, successors, rights and cost correspondence.

For authority, copy the same correctly encoded $(n,v)$, field or window to a receiver with no Add grant on the source. The original holder can perform Add; the copied receiver's primitive is disabled. All numerical bytes can agree while legal actions differ. The inverse thus neither grants authority nor certifies that a supplied record was physically measured on that specimen. Calibration and provenance have the same premise boundary: equality with a computed ideal record is not authentication of the actual law. $\square$

## 43. Exact supplier correspondence and the source-relative addition

The source-relative addition in §§34–41 is the joined original-unit comb theorem: (UFS.84) proves cyclicity at its original internal root; original refusal calls earn its unknown size without accepted growth; the paid root window acquires an arbitrary rational entry; actual controls earn a new unit origin; and a literal root Sample supports the restricted four-expression inverse and complete retained use on that same source. The material class, changed root interface, arbitrary entry and actual advanced endpoints are all needed in that statement. This is a `repo-derived` application and synthesis, with no worldwide-priority claim for the comb calculation or classical control mechanisms.

The native syntax, reachable domain, forced labelled generation and material parsing are credited to [AA §§17–20](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md). Public native combs and their paid construction occur, for example, in [AA II Theorem 50.4](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md), whose all-beta left comb differs explicitly from (UFS.82)'s alpha-ended right spine. The persistent material/field inclusions are those of [NLBA II Definitions 17.1–17.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md); its terminal binding, zero entry, Reset and raw roster are not inherited. Its Theorem 30.2 supplies the branching binary separation consumed in Theorem 38.2, with the changed seed condition verified explicitly. Its §§31–38 supply the sampled advanced-endpoint, restricted-history, complete-service and literal-resource disciplines applied here. Neither that binary theorem nor the general linear control-to-origin mechanism is presented as new abstract mathematics.

For the repository's [finite observability declaration](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean), `finite_observability_equivalence`, and its [owning Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs), the parameters are State $=\mathbb R^N$, Output $=\mathbb R$, update $=A_n$, readout $=e^{\mathsf T}$ and horizon $=N$. Its stacked operator is exactly $K_n^{\mathsf T}$; the kernel, full rank and Gram-positivity equivalence is the existing result. Theorem 35.1 supplies this source's missing full-rank hypothesis, and the actual $y$ supplies its measured right-hand side. Ordinary rational nonsingularity, not a new Lean application, is used in the displayed solves.

The [native source producer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean), including its private traversal, paid-read and stationarity helpers, and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs), prove a different acquisition with an actual constructor Read, a retained native trace and growing stack workspace. They do not install a constructor Read in §34. The [native uniform tree definitions](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.lean), their private navigation/readout helpers and [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.scribe.cs) compute from a supplied tree code; they are not unknown-source observations. Here the term used by local computation is earned by Theorem 36.2 before being traversed.

At the pinned upstream mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, [`SimpleGraph.adjMatrix_pow_apply_eq_card_walk`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean) supplies the finite unit-graph walk interpretation of powers. The finite graph is this actual material $G_n$; the entries and scalars used here are rational. It supplies no authentication or free impulse readout. The two-sided nonsingular inverse identities in [`Matrix.NonsingularInverse`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean) have the determinant-unit hypothesis supplied here by (UFS.83), not by a compiler run. Godsil's primary paper, Lemma 5.2 and its §2 resolvent background, supplies the classical root-deletion criterion; §7 relates its walk matrix to linear control and observation. Those are credited suppliers inside the new source-specific argument.

The public positive root and original-terminal results are also subtracted. [NLBA II §§45–50](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md) already acquires arbitrary signed rational amplitudes from a cleared handoff on its known constructed cherry family, using terminal Add preparation, root Read and paid asymmetric growth. Its field subspace, known geometry, actuation and successful acquisition growth differ from this unknown-size arbitrary-full-field comb entrance. NLBA II §§51–54 already gives an actual selected original-first-terminal experiment separating an owned pair of candidate fields, with at most one successful growth and the correct advanced endpoint. That candidate-advice pair task is not exact acquisition of an arbitrary unknown field; its alternative experiment functions are not an actual response table. Their terminal controls and candidate advice are not included for free in the root-only bill here. [NLBA II §§55–66](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md) also supplies terminal-seeded branching binary recovery with two actual Reads, preserved-entry restoration on a grown plant, and rank-many terminal-Read acquisition of an advanced current-field predictor from an earned complete graph/map. These terminal-access and correspondence contracts do not supply the unknown-comb root-only entrance proved here.

[Recovery Geometry II §§96–103](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md) already gives persistent-address calibration, all-native root cyclicity, ordered identification and an actual no-size-advice root acquisition. Its law has separated rational address potentials and small links, its initial field is zero, and its Tick returns a scalar. Its spectral-window proof is valid under those hypotheses. This addition changes none of those conclusions; it instead retains the original unit zero-diagonal adjacency, restricts to combs, accepts arbitrary entry fields, uses ACK-only Tick plus actual Read, and earns size by original refusals. [Atomic Generation Acquisition II §§84–92](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md) already supplies terminal-observed growing-history recovery under its positive-diagonal, positive-edge invertible laws, respective post-clock and pre-clock conventions, actual known initialization and nonzero seed: Definition 84.2 installs indexed terminal Read$(j)$, and Theorem 87.3 samples all $b$ terminals at every diagnostic epoch. Those growing-history laws and provenance conditions are not the fixed unit law and arbitrary entry here. Thus neither root observation, native growth, uncapped acquisition nor history coding in general is claimed to originate in this addition.

## 44. Quantified scope and remaining realization boundaries

**Theorem 44.1 (the joined conditional outcome).** For every actually prepared finite original comb $u_n$, $n\ge3$, every rational entry field, and every authentic installation satisfying §§34 and 40's exact-law, original-root, framing, authority, serialization and finite-backing premises, there is one uniform finite controller with the following properties on that same source. It earns $n$, the ordered material coordinates and the arbitrary attachment field; without Reset or successful growth in accepted acquisition, it actually establishes the whole-field root seed $e$; it retains complete source service for every finite enabled subsequent root/native continuation; and at completed Samples in its fixed-comb binary phase its Space, Time, Boundary and Memory expressions have all the inverses and route agreement of Theorem 39.2. Its actual endpoint is $e$ after acquisition and $A_n^{N-1}x_w$ after Sample, and its attained same-run resources are those of §41, including preparation, control, literal widths, backing, full outputs and returns.

Proof. Theorem 36.2 earns the finite graph without changing an accepted field. Theorem 35.1 supplies the exact native-coordinate rank needed by (UFS.87). Theorem 37.1 performs observation, nulling and unit preparation; Proposition 37.2 gives an actual producer for every quantified rational entry, with its additional bill. Theorem 40.2 installs and preserves complete continued source service, including outputs and successors outside the binary inverse domain. Theorem 38.2 checks the public binary supplier at this particular root; Theorem 38.4 performs the literal sample and computes its actual advanced endpoint. Theorem 39.2 proves the four inverses and route agreement, and Proposition 39.3 proves their admitted dynamics and continuation-kernel correspondence. Section 41 counts the joined actual operations and the real finite algorithms, with widths and copies kept explicit. These applications use one acquired binding and trajectory, not separately attainable marginal optima. $\square$

This theorem does not settle unchanged original terminal-only acquisition, arbitrary-native unit-root cyclicity, arbitrary old-history recovery, restoration of the old entry field, or an inverse after unrestricted field controls or growth. Its Time is the native generation projection and prospective binary pulse chain, not every refused call, wrapper boundary or erased field preparation. Theorem 42.1 is specific counterevidence to the arbitrary-native fixed-geometry promotion; Propositions 42.2–42.4 exhibit erased-history, image-domain and operational-identification boundaries. Accessible old archives or differing grants change the task and cannot be silently omitted from its state or bill.

There is no asserted uniform source-size bound, literal-width bound, efficient off-image recognition, bounded lifetime storage, universal minimum or total-cost optimum. Physical conformance, noise robustness, finite-capacity implementation and provenance/authority acquisition have not been derived from the ideal rational model. No common installed alpha/beta, rational-path and quantum process is obtained by numerical similarity. The fixed-$G_{\rm gc}$/original-$Q$, parked-consumer, unchanged-initialization and final-no-Ready problems retain their original exact conditions. This scoped comb bridge and its paid sampled four-expression application leave those stronger realization and full-programme questions unresolved.

## 追加锚（本行以下为增补区）

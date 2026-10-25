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

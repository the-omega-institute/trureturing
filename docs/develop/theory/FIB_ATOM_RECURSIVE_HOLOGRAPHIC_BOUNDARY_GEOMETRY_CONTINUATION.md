# FIB-ATOM 递归全息边界几何·Whole-rho 续卷

本卷是 [FIB-ATOM 递归全息边界几何](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md) 的同题续卷，承接原卷第 54 章后的第 55 章。原卷保存来源、操作、INITIAL、资源和此前边界；本卷的第 55.1–55.8 条给出同一来源合同上的 Whole-rho 场、绑定、紧性、谱延拓和资源边界。公式、引文与条目编号沿用第 55 章的数学语义。 下文的 §37–§54、§52.4、§52.6 与 §54.1 均指向上述原卷的同编号条目。

## 55. Whole-rho source histories: an isolated field, binding compactness and full spectral continuation

**Definition 55.1 (original source, event version and the added realization).** Let $t$ be any original nonempty finite ordered $\alpha/\beta$ tree of [Continuation Definition1.1](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md). Labels, brackets, left/right order and distinct equal-valued occurrences remain part of $t$. Use the original whole substitution

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle s,u\rangle=\langle\rho s,\rho u\rangle.
\tag{55.1}
$$

An actual whole-rho history retains its original initialization, all commands, actual acceptances or refusals, every numerical Read and Stop, and any already acquired records. At an event $e$, let $j(e)$ count accepted substitutions, not attempted commands or Reads. Its actual current source is $t_{j(e)}=\rho^{j(e)}t$, and INITIAL is always $t$. This chapter introduces no other executed source action. Under the fixed-$H$ TM30/57 interface, INITIAL belongs to its original prior $\mathcal T_H$ and the whole candidate must pass its original leaf-count guard; refusal leaves both the current tree and $j(e)$ unchanged, appends the original refusal, and returns no candidate Read. Reads preserve the current tree and retain their original functions. [Process44](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)'s uncapped menu instead permits each finite whole-rho prefix. Statements quantified over all $j$ mean this uncapped mathematical family or separately legal finite prefixes, never a cap increase in one fixed-$H$ execution. A stopped history has no subsequent events; a natural-number-indexed history has no event after an infinite prefix. Only versions actually reached by a chosen history are asserted as its event domains. The other $D_j(t)$ belong to the source-indexed mathematical family of separately legal finite prefixes; they are not an execution continuation of that stopped or capped history. The common realization is attached to the same immutable source and root, not acquired by a post-prefix event.

Write $D_j(t)=\operatorname{Pos}(\rho^jt)$, with root $o=\varepsilon$. Consume [Transport Memory TM22.2 and TM23.2](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), rather than reproving their persistence and exhaustion: the inclusion $D_j\subset D_{j+1}$ is the same-address map, every old parent–child seam and its order persists, every finite address eventually occurs, and the birth bound is $b_t(p)\le2|p|$. In particular

$$
B_{\lfloor j/2\rfloor}:=\{p:|p|\le\lfloor j/2\rfloor\}\subset D_j(t),
\qquad \bigcup_jD_j(t)=\mathcal P:=\{L,R\}^{*}.
\tag{55.2}
$$

The actual domains are the irregular trees $D_j(t)$, not replacement balls. A ball in (55.2) is only a comparison subset inside each actual domain. TM23's birth field and versioned tags still determine the ordered source and its semantic whole-rho versions in their stated scope; they do not authenticate which actual actions occurred. A persistent address can change from $\alpha$ to $\beta$ to a branch. Persistence of a geometric site therefore does not mean persistence of its label or of its complete subtree.

Supply the following additional joint mathematical contract. The graph on $\mathcal P$ has exactly the parent–child seams $\{p,pL\},\{p,pR\}$; each seam has length and symmetric conductance one, each site has counting measure one, and the same root $o$ is fixed throughout. Root degree is two, all other degrees are three. The source of the scalar field is one unit at this root, with no homogeneous background, screening term, moving anchor or added parent seam at the root. Its exterior condition is decay at infinity, and the field is taken in $\ell^2(\mathcal P)$. Complex amplitudes have the counting-measure norm. Public constants $a,g>0$ specify the common kinetic and attractive energy units. The clock $\tau$ for the supplied heat law is distinct from source-event order; the supplied amplitude law is $i\partial_\tau f=\mathsf Hf$ with unit action scale. Its solution is $e^{-i\tau\mathsf H}f(0)$, which preserves the full counting-measure norm because $\mathsf H$ is bounded self-adjoint. No relation between an accepted substitution and elapsed $\tau$ is inferred. Unit weights, symmetry, field access, amplitude preparation, this clock and these laws are added contracts, not native operations, prices or physical facts.

The faithful joint object retains $(t,\mathsf h,e,j(e),D_j(t),\operatorname{tag}_{t_j},b_t)$ together with the restrictions of the following field and operators. Forgetting its added coordinates returns exactly the original source/history, actions, every Read/refusal/Stop and immutable INITIAL. This is a mathematical association on the same actual realization, not an extra observer record, a source-specific controller initialization or an acquired certificate. Geometry alone is a strictly smaller projection of this object.

**Definition 55.2 (one field, common kinetic law and all missing-child data).** On $\ell^2(\mathcal P)$ put

$$
(Lf)(p)=\deg(p)f(p)-\sum_{q\sim p}f(q),\qquad
Q(f)=\sum_{\{p,q\}}|f(p)-f(q)|^2=\langle f,Lf\rangle,
\qquad \mathsf H=aL-gM_\phi.
\tag{55.3}
$$

Every unoriented seam is counted once. The degree bound makes $L$ bounded self-adjoint, $0\le L\le6I$, and all displayed form domains are the full $\ell^2$ space. For an actual domain $D=D_j(t)$ let $I_D$ denote zero extension and $P_D=I_DI_D^*$ the orthogonal projection. Wavefunction Dirichlet data mean zero exterior amplitude, hence

$$
\begin{aligned}
L_D&=I_D^*LI_D,\
Q_D(f)&=\sum_{\{p,q\}\subset D}|f(p)-f(q)|^2
 +2\sum_{p\in\operatorname{Leaf}(t_j)}|f(p)|^2,\
\mathsf H_D&=aL_D-gM_{\phi|D},\
\mathcal E_D(f)&=aQ_D(f)-g\sum_{p\in D}\phi(p)|f(p)|^2
 =\langle I_Df,\mathsf H I_Df\rangle.
\end{aligned}
\tag{55.4}
$$

A current leaf has both missing children, irrespective of its $\alpha/\beta$ label. A nonroot leaf also retains its parent seam. Thus $L_D$ has diagonal two at the root and three at every other node, including every leaf; its off-diagonal entry on an existing seam is $-1$. The root has no artificial killing seam. If $D=\{o\}$, its two missing children give $L_D=[2]$. These are the actual inherited seams and exterior terms, not the single-root killing convention of the moving-root graft in §52.

The field in (55.3)–(55.4) is the *one common infinite solution* restricted to $D$. It retains its actual exterior field values, even though the amplitude exterior is zero. For comparison only, write $\phi_D^0$ for the newly solved killed field $L_D\phi_D^0=\mathbf1_o$. Replacing $\phi|D$ by $\phi_D^0$ gives a different finite potential and is never implicit in (55.4).

**Theorem 55.3 (joint irregular-domain field, propagation and sufficient negative binding).** For every source/history of Definition55.1, the same realization has the unscreened anchored field

$$
\phi(p)=2^{-|p|},\qquad L\phi=\mathbf1_o,\qquad
\|\phi\|_2^2=2,
\qquad Q(\phi)=1.
\tag{55.5}
$$

Its outward flux across every actual $D_j(t)$ is one. Its gradient energy on all seams whose parent has depth at least $R$ is $2^{-R}$. The common heat law has bounded rate and strictly positive propagation between any two actual occurrences. All finite domains and the infinite operator have the uniform normalized lower bound

$$
\mathcal E_D(f)\ge(a\lambda_*-g)\|f\|_2^2,
\qquad \langle f,\mathsf Hf\rangle\ge(a\lambda_*-g)\|f\|_2^2,
\qquad \lambda_*=3-2\sqrt2>0.
\tag{55.6}
$$

The escape threshold is $\epsilon_*=a\lambda_*$. If $g>3a/4$, the infinite normalized infimum $m$ is negative, attained, and strictly below $\epsilon_*$. Every source's sufficiently advanced legal finite domain has an attained negative minimum. For $0<g\le a\lambda_*$ there is no negative normalized energy; no sharp coupling threshold or all-positive-coupling negative binding is asserted.

Proof. The field is calculated on the occurrences identified by TM22–23. At a nonroot depth $d$, $3\,2^{-d}-2^{-(d-1)}-2\,2^{-(d+1)}=0$; at the root $2-2(1/2)=1$. There are $2^d$ sites at depth $d$ and $2^{d+1}$ seams to depth $d+1$. Therefore

$$
\sum_{d\ge0}2^d4^{-d}=2,
\qquad
\sum_{d\ge R}2^{d+1}(2^{-d}-2^{-d-1})^2=2^{-R}.
\tag{55.7}
$$

This is an isolated unit charge with finite total and far-field gradient energy, without a screening mass. It is not a Euclidean point charge or a claim about an Euclidean dimension. The root value one is fixed by this source and exterior solution, not by an unknown-source calibration. Uniqueness in the declared field space follows from the positive kinetic gap proved below. Decaying real harmonic differences also vanish by the maximum principle: a positive maximum of a nonzero decaying function is attained on a finite set, propagates to all neighbours, and contradicts decay; apply this to both signs and to real and imaginary parts.

Each actual finite full binary domain has $\sum_{p\in\operatorname{Leaf}(t_j)}2^{-|p|}=1$: splitting a leaf replaces its weight by the two half weights. The two outgoing field differences at each leaf are $\phi(p)/2$, so the total flux is one on the actual irregular cut, including a singleton. More precise identities useful for the finite correspondence are

$$
\begin{aligned}
Q_{\rm outside\ D}(\phi)&=\sum_{p\in\operatorname{Leaf}(t_j)}\phi(p)^2,\
Q_{\rm internal\ D}(\phi)&=1-\sum_{p\in\operatorname{Leaf}(t_j)}\phi(p)^2,\
L_D(\phi|D)&=\mathbf1_o+b_D,
\qquad b_D(p)=\mathbf1_{\operatorname{Leaf}(t_j)}(p)\phi(p),\
Q_D(\phi|D)&=1+\sum_{p\in\operatorname{Leaf}(t_j)}\phi(p)^2.
\end{aligned}
\tag{55.8}
$$

Here “outside” includes every seam below a current leaf. The outgoing infinite field subtree rooted at such a leaf has energy $\phi(p)^2$ by the geometric series in (55.7). In the compressed field equation the exterior input is the sum of the two child values, namely $\phi(p)$. The last identity concerns the zero-extended *amplitude* equal to the field on $D$; it is not the energy of the continued common field. This explicitly prevents confusing field exterior data with amplitude killing.

For heat put $P=I-L/3$. Its entries are nonnegative, its row sums are one, and symmetry gives the column sums. In the declared clock,

$$
K_\tau=e^{-\tau aL}
=e^{-3a\tau}\sum_{n\ge0}\frac{(3a\tau)^n}{n!}P^n,
\qquad K_\tau(p,q)\ge e^{-3a\tau}\frac{(a\tau)^r}{r!}>0
\quad(\tau>0),
\tag{55.9}
$$

where $r$ is the length of the actual seam path. This conserves nonnegative $\ell^1$ mass and has rate at most $3a$, hence no explosion. Replacing $L$ by $L_D$ gives a substochastic law, with loss through the two missing-child seams at every current leaf and the same positive path bound inside $D$. Positivity is not finite signal velocity, an original Read or a physical clock.

For the gap, use the classical positive-function graph transform cited in the existing Keller–Pinchover–Pogorzelski note, with $h(p)=2^{-|p|/2}$. Directly on the common seams,

$$
\frac{Lh}{h}(p)=\lambda_*+(\sqrt2-1)\mathbf1_o(p).
\tag{55.10}
$$

The transform expresses $Q(f)-\lambda_*\|f\|^2$ as a sum of nonnegative transformed seam differences and $(\sqrt2-1)|f(o)|^2$, initially for finite support and then by density. The transform's positive $h$ need not be square summable. On $D$, zero extension retains exactly the missing-child terms, so the same inequality applies. Since $0<\phi\le1$, (55.6) follows. The simpler certificate $h=1$ has finite pointwise term $2a\mathbf1_{\operatorname{Leaf}}-g\phi$ and infinite pointwise term $-g\phi$; neither certificate asserts a normalized state merely from positivity.

For the threshold, take normalized radial strings on $n$ consecutive levels of a subtree far from $o$, with level coefficients proportional to $\sin(k\pi/(n+1))$, $1\le k\le n$, and amplitude constant on each level after counting-measure normalization. Their kinetic Rayleigh value is $3-2\sqrt2\cos(\pi/(n+1))$. Moving the subtree deeper and letting $n\to\infty$ gives weakly null unit vectors, kinetic value $\lambda_*$ and potential expectation tending to zero. Together with the global gap this fixes the escape threshold $\epsilon_*$. The adjacent-level operator residual of these strings tends to zero as well, so they are singular Weyl sequences there. The diagonal $M_\phi$ is compact, since truncating it to $B_R$ has norm error at most $2^{-R-1}$. The standard compact-perturbation conclusion, in the precise Weyl scope of Teschl Theorem6.19 cited by the existing Lenz–Stollmann–Wingert note, preserves this essential threshold. Below it only isolated finite-multiplicity eigenvalues can occur. In particular the operator has no global compact resolvent.

The unit vector $\phi/\sqrt2$ gives the explicit common trial

$$
\frac{\langle\phi,\mathsf H\phi\rangle}{\|\phi\|^2}
=\frac a2-\frac{2g}{3},
\qquad \sum_p\phi(p)^3=\sum_{d\ge0}4^{-d}=\frac43.
\tag{55.11}
$$

It is negative when $g>3a/4$. Attainment and all-near-minimizer compactness are proved in Theorem55.4, not inferred from finite matrix minimization. Its truncations to the actual $D_j(t)$ converge in norm by (55.2), and boundedness of $\mathsf H$ makes their normalized energies converge to (55.11), proving eventual finite negativity. Finite attained minima themselves follow from the finite unit sphere. If $g\le a\lambda_*$, (55.6) excludes negative values. The intervening positive-coupling range is not classified here; “negative”, “below escape” and “attained” are distinct properties. □

The killed-field comparison is also on these same domains. Positivity of $L_D^{-1}=\int_0^\infty e^{-sL_D}\,ds$, justified by $L_D\ge\lambda_*I$, and (55.8) give $0<\phi_D^0\le\phi|D$. For $D\subset D'$ the restricted $\phi_{D'}^0$ solves the smaller equation with a nonnegative exterior input, so $\phi_D^0\le\phi_{D'}^0|D$. Galerkin convergence for the uniformly positive $L$ gives

$$
I_D\phi_D^0\longrightarrow\phi\text{ in }\ell^2,
\qquad \|I_D\phi_D^0-\phi\|_\infty\longrightarrow0
\tag{55.12}
$$

along the actual exhaustion. To verify that convergence without a pointwise-to-norm inference, let $w_D$ solve the compressed equation and $w=L^{-1}\mathbf1_o$. The $L$-energy orthogonality to every vector supported in $D$ implies
$\|w-w_D\|_L\le\inf_{\operatorname{supp}(v)\subseteq D}\|w-v\|_L$; boundedness and the lower gap convert this to norm convergence. The common field (55.5) is this $w$. For any actual $D\supset B_R$, the same estimate gives the uniform source-family bound

$$
\|I_D\phi_D^0-\phi\|_2
\le\sqrt{6/\lambda_*}\,\|(I-P_D)\phi\|_2
\le\sqrt{6/\lambda_*}\,2^{-R/2},
\qquad \|(I-P_{B_R})\phi\|_2^2=2^{-R}.
\tag{55.12a}
$$

Thus using the killed potential raises each finite amplitude energy, but changes its operator by norm at most $g\|\phi|D-\phi_D^0\|_\infty\to0$. The subsequent limit statements also hold for that expressly different family by this norm comparison. No finite claim for the common restriction is attributed to a newly solved field.

**Theorem 55.4 (all near-minimizers and actual-source finite-to-common preservation).** Fix the supplied $a,g$ and root. Whenever $m:=\inf_{\|f\|=1}\langle f,\mathsf Hf\rangle<\epsilon_*$, every normalized sequence whose energies tend to $m$ has a strongly convergent subsequence, and every such limit is a normalized ground state. This includes, in particular, $g>3a/4$, where $m<0$. It is compactness of *all* normalized near-minimizers, not of all bounded-energy amplitudes.

For every fixed original $t$, let $m_j(t)$ be the minimum of (55.4). For all supplied $a,g>0$, $m_j(t)\downarrow m$. Under the strict-gap hypothesis $m<\epsilon_*$, if $f_j$ is any normalized finite state with $\mathcal E_{D_j}(f_j)-m_j(t)\to0$, all its zero extensions are strongly precompact and their cluster points are common normalized ground states. Under that same hypothesis the common ground state is simple and strictly positive up to phase; no phase selection is required for precompactness. The minimum-value bound, which does not require attainment, is

$$
0\le m_j(t)-m\le m_{B_{\lfloor j/2\rfloor}}-m\longrightarrow0
\quad\text{uniformly over all finite original }t.
\tag{55.13}
$$

Thus arbitrary varying sources have the same minimum-value convergence if their accepted-substitution indices tend to infinity, with all embeddings root fixed as declared; their state compactness and ground-state conclusions additionally require $m<\epsilon_*$. More precisely, for any $t_n$ and indices $j_n\to\infty$, the conclusions apply to $D_{j_n}(t_n)$. Each actual source/history remains separately retained. No varying-source authentication or convergence of their initial syntax is asserted.

Proof. Let $f_n$ be any unit near-minimizing sequence. Extract a weakly convergent subsequence $f_n\rightharpoonup f$ and put $r_n=f_n-f$. Compactness of $M_\phi$ implies $\langle r_n,M_\phi r_n\rangle\to0$. Boundedness of $L$ gives vanishing cross terms, and $\|r_n\|^2\to1-\|f\|^2$. Consequently

$$
\begin{aligned}
m&\ge\langle f,\mathsf Hf\rangle+\epsilon_*(1-\|f\|^2)\
&\ge m\|f\|^2+\epsilon_*(1-\|f\|^2)
=m+(\epsilon_*-m)(1-\|f\|^2).
\end{aligned}
\tag{55.14}
$$

The strict binding gap forces $\|f\|=1$. Weak convergence and convergence of norms imply strong convergence, and boundedness of $\mathsf H$ gives energy $m$. This proves attainment and the stated subsequence property for every near-minimizer. It also shows precisely where escape would be allowed if the gap vanished. It does not confuse compact probability-law completion with compactness of amplitudes in the common Hilbert norm.

A minimizer satisfies $\mathsf Hf=mf$ by unit-sphere variation. Replacing it by its absolute value can only decrease the seam energy, so there is a nonnegative minimizer. Its eigen-equation, written $(a\deg(p)-g\phi(p)-m)f(p)=a\sum_{q\sim p}f(q)$, shows that a zero forces all neighbouring values zero and hence, by connectivity, the whole vector zero. Thus it is strictly positive. Any ground eigenvector has positive modulus; equality in the absolute-value energy comparison forces the same phase along every seam. If the ground eigenspace had dimension at least two, a nonzero linear combination could vanish at $o$, contradicting that property. This establishes simplicity. Permuting children in the common unlabelled graph commutes with $\mathsf H$ and fixes its positive normalized ground state, so it is radial as a *consequence*, not as a restriction of the minimization problem. This graph symmetry does not permute the retained original source history.

Every finite unit vector has exactly its common energy after zero extension, so $m_j(t)\ge m$ and nested domains give monotonicity. For any $\eta>0$, choose a common unit trial with energy below $m+\eta$ and approximate it by a normalized finite-support vector. Boundedness of $\mathsf H$ preserves this energy approximation, and exhaustion places that support in all sufficiently advanced $D_j(t)$. This gives the reverse limiting inequality without assuming a common ground state. The same reasoning for $B_R$ and (55.2) gives (55.13). Under $m<\epsilon_*$, any finite near-minimizer therefore becomes a common near-minimizer, to which (55.14) applies. The uniform bound also applies to arbitrary $t_j$ with $j\to\infty$. At fixed accepted index no such assertion is made; varying initial domains need separately tend to exhaust the common rooted graph. The killed-field family in (55.12)–(55.12a) has nonnegative, vanishing norm perturbation, so its minimum values have the same limits; under $m<\epsilon_*$ its normalized near-minimizers have the same strong compactness and ground-state conclusions. □

The strict gap is material even at positive coupling: (55.18b) below gives $m=\epsilon_*$ for $0<g\le a/(2+3\sqrt2)$, and the same escaping strings are normalized near-minimizers with weak limit zero. For $g=0$, the same radial escape strings are unit near-minimizers of $aL$ with weak limit zero and energy tending to $a\lambda_*$. No normalized vector attains $a\lambda_*$: equality in (55.10)'s transform forces its root value zero and every transformed seam difference zero, hence the vector zero. This is an explicit gap-boundary failure of strong compactness. For any fixed $g$, far angular states also have bounded energies and disjoint escaping support. Bounded energy alone never proves the compactness in Theorem55.4. With unrestricted amplitude rather than unit normalization, any negative trial can be multiplied to make the quadratic energy tend to $-\infty$. The normalized lower certificate therefore does not assert convexity or amplitude-independent stability.

**Theorem 55.5 (full spectral boundary and negative-sector continuation for the same domains).** On every actual $D_j(t)$, all energies, multiplicities and states are represented by energy-dependent finite elimination with the inherited diagonal of (55.4), together with internal spectral data and full-state normalization. Exceptional internal energies and root-invisible states are retained. On the common infinite realization the same block account is valid off internal spectra and, below $\epsilon_*$, at isolated internal exceptions with their kernel data. In every compact spectral window below $\epsilon_*$ whose endpoints lie in resolvent gaps of $\mathsf H$, the finite eigenvalues, total multiplicities and full normalized eigenspaces converge to those of the common operator. In particular this applies to the entire negative sector with a cutoff at zero if $0\notin\sigma(\mathsf H)$, and always to negative windows with endpoints in gaps. There is no global compact-resolvent or all-energy finite spectral preservation claim.

Proof. Reuse the classical finite block elimination in §52.4, including (52.17), (52.18), (52.18a) and (52.18b), after verifying the operator's source and boundary data. For each actual subtree at $p\in D$, take the principal submatrix of $\mathsf H_D$, retaining its global diagonal, not its free-standing closed-tree diagonal. Write $D_p(z)$ for its characteristic determinant, $P_p(z)$ for the root-deleted determinant, and

$$
\delta_p(z)=a\deg_{\mathcal P}(p)-g2^{-|p|}-z.
\tag{55.15}
$$

A current leaf has $D_p=\delta_p$, $P_p=1$. An actual branch satisfies the polynomial identities

$$
P_p=D_{pL}D_{pR},\qquad
D_p=\delta_pD_{pL}D_{pR}
-a^2P_{pL}D_{pR}-a^2D_{pL}P_{pR}.
\tag{55.16}
$$

The two entries $-a$ are exactly the two inherited child seams. At a nonroot subtree root, its parent contribution is already present in diagonal $3a$; at a current leaf its two missing children are also present. The potential depends on *global* depth, so reindexing a subtree must retain its depth offset and may not restart the field at one. Expansion of the specified parent matrix gives (55.16) by the same elimination as §52.4; the result is a polynomial at every $z$, including internal exceptional energies. It verifies this source application, without claiming new determinant or Schur theory.

For an arbitrary retained boundary $B\subset D$ and interior $I$, put $K(z)=\mathsf H_{II}-zI$. Where $K(z)$ is invertible,

$$
S_B(z)=\mathsf H_{BB}-zI-\mathsf H_{BI}K(z)^{-1}\mathsf H_{IB},
\qquad
\psi=(b,-K(z)^{-1}\mathsf H_{IB}b).
\tag{55.17}
$$

Full eigenvectors are exactly those with $S_B(z)b=0$, and at real such energies
$\|\psi\|^2=-b^*S_B'(z)b$. The determinant and inertia include the internal block, as in (52.17); a stationary interior value is a fixed-boundary minimum only if that interior block is positive. Negative spectral shifts are not assigned static Schur positivity. Even where $G_o=P_o/D_o$ exists, it is only the root resolvent, not a complete spectral record.

At a real internal exception retain the original equations, equivalently the precise kernel construction of (52.18a): with $\Pi$ the kernel projection and $K^+$ its inverse on the orthogonal complement, require $\Pi\mathsf H_{IB}b=0$, write $h=-K^+\mathsf H_{IB}b+u$, $u\in\ker K$, and impose
$(\mathsf H_{BB}-zI-\mathsf H_{BI}K^+\mathsf H_{IB})b+\mathsf H_{BI}u=0$.
The full norm is $\|b\|^2+\|K^+\mathsf H_{IB}b\|^2+\|u\|^2$. Its solution-space dimension is the complete multiplicity; (52.18b) retains the coupled-kernel inertia. In particular $b=0$ and $u\in\ker K\cap\ker\mathsf H_{BI}$ gives a root-invisible sector. Cancellation of a common factor in $P_o/D_o$ does not discard that sector from $D_o$ or from the state space. Thus the retained data are the determinant, energy-dependent boundary operator, coupled internal kernels and normalizations, rather than a scalar response alone.

The infinite counterpart partitions the *same* $\ell^2(\mathcal P)$ into a finite boundary and its complement. Its bounded self-adjoint internal operator has essential lower edge $\epsilon_*$, because the cut changes only finitely many seams and $M_\phi$ is compact. At nonreal $z$, or real $z$ outside its spectrum, (55.17) uses a bounded resolvent and reconstructs a full $\ell^2$ state. At an isolated internal energy below $\epsilon_*$, the kernel is finite dimensional and $K^+$ is bounded; the same compatibility, norm and multiplicity construction applies. At a real energy in the essential spectrum no bounded pseudoinverse or square-summable continuation is assumed.

There is also an explicit full-state decomposition showing how much a root port omits. Let $u_n$ be the unit vector constant on level $n$, with value $2^{-n/2}$. For each vertex $v$ of depth $d$ and each $n\ge0$, let $w_{v,n}$ have value $+2^{-(n+1)/2}$ on the level-$n$ descendants of $vL$, the negative of that value on those of $vR$, and zero elsewhere. These form mutually orthogonal channel bases. On level $k$ the radial vector and the contrasts of ancestors of depth $d<k$ supply
$1+\sum_{d<k}2^d=2^k$ orthogonal vectors, proving completeness level by level. Parent cancellation at $v$ makes each contrast channel invariant; adjacent normalized levels have coupling $-a\sqrt2$. Hence

$$
\mathsf H\simeq J_o\ \oplus\ \bigoplus_{d\ge0}J_d^{\oplus2^d},
\tag{55.18}
$$

where $J_o$ on $\ell^2(\mathbb N_0)$ has diagonal $2a-g$ at $n=0$ and $3a-g2^{-n}$ at $n\ge1$, while $J_d$ has diagonal $3a-g2^{-(d+1+n)}$ at every $n\ge0$. All have neighbouring coupling $-a\sqrt2$. Every $J_d$ channel is root invisible; it is an actual amplitude sector, not an executed tree symmetry or a radial approximation. A channel eigenvector is reconstructed by these normalized basis vectors, so its sequence norm is exactly its full counting-measure norm. Each half-line eigenvalue is simple by the endpoint recurrence; its full multiplicity includes the $2^d$ identical channels and any coincidences across channels. At large $d$, $J_d\ge\epsilon_*-g2^{-d-1}>0$, so only finitely many depths contribute negative modes. The constant-diagonal half-line sine transform has band $a[3-2\sqrt2,3+2\sqrt2]$; the channel potentials and the radial endpoint change are compact perturbations. This confirms the essential band and the threshold used above while retaining all hidden channels. It does not identify a finite irregular $D_j$ with a collection of independently substituted complete balls.

Let $U$ be the unitary map from channel coefficients to the displayed occurrence basis, and write $f=U(c,(v_{p})_{p\in\mathcal P})$, where $v_p$ is the contrast channel anchored at $p$. Orthogonality and completeness give the full amplitude and energy-dependent spectral account

$$
\begin{aligned}
\|f\|_2^2&=\|c\|_2^2+\sum_{p\in\mathcal P}\|v_p\|_2^2,\\
E_{\mathsf H}(\Omega)&=U\left(E_{J_o}(\Omega)\oplus
 \bigoplus_{p\in\mathcal P}E_{J_{|p|}}(\Omega)\right)U^*,
\qquad \Omega\subset\mathbb R\text{ Borel}.
\end{aligned}
\tag{55.18a}
$$

The functional calculus of the same direct sum proves this identity, including continuous spectral subspaces. Each channel resolvent is the corresponding Jacobi resolvent at nonreal energies, so this record retains all spectral measures as well as point multiplicities. The root vector lies only in $J_o$; its scalar response gives no spectral measure for the contrast summands. A generalized state at a continuous-spectrum energy is not thereby a normalized $\ell^2$ eigenstate.

The same complete channel decomposition also supplies an explicit positive-coupling escape exclusion. For a channel sequence $v$, the kinetic excess above $\epsilon_*$ is
$q_o(v)=a(\sqrt2-1)|v_0|^2+a\sqrt2\sum_{n\ge0}|v_{n+1}-v_n|^2$ in the root channel, and
$q_d(v)=a\sqrt2(|v_0|^2+\sum_{n\ge0}|v_{n+1}-v_n|^2)$ in a contrast channel. Telescoping $v_n=v_0+\sum_{k<n}(v_{k+1}-v_k)$ and weighted Cauchy–Schwarz give
$|v_n|^2\le[(a(\sqrt2-1))^{-1}+n/(a\sqrt2)]q_o(v)$ and
$|v_n|^2\le(n+1)q_d(v)/(a\sqrt2)$.
Using $\sum_{n\ge0}2^{-n}=\sum_{n\ge0}n2^{-n}=2$ yields

$$
\begin{aligned}
\sum_{n\ge0}2^{-n}|v_n|^2&\le\frac{2+3\sqrt2}{a}q_o(v),\\
\sum_{n\ge0}2^{-(d+1+n)}|v_n|^2&\le\frac{\sqrt2\,2^{-d}}a q_d(v),\\
\langle f,M_\phi f\rangle&\le\frac{2+3\sqrt2}{a}
 \bigl(aQ(f)-\epsilon_*\|f\|^2\bigr),\\
0<g\le\frac{a}{2+3\sqrt2}&\quad\Longrightarrow\quad
\mathsf H\ge\epsilon_*I,\qquad m=\epsilon_*.
\end{aligned}
\tag{55.18b}
$$

These form identities hold first for finite sequences and then by density; the potential is diagonal within every channel. The lower inequality and the earlier escape trials give the last equality. Those trials remain weakly null normalized near-minimizers because their potential expectation tends to zero, so all-near-minimizer strong compactness fails in this positive range. This is a sufficient no-binding range, not a sharp threshold, and does not alter the negative-binding range $g>3a/4$.

For the actual finite limit, first use the classical min-max principle in the primary scope of Teschl Theorem4.10. Finite compressions have no lower variational eigenvalues than $\mathsf H$. Truncating the span of any finite collection of common subthreshold eigenvectors to $D_j(t)$ preserves its dimension and approximates all its Rayleigh values uniformly on its unit sphere. This supplies the reverse limiting inequalities for each subthreshold eigenvalue, with multiplicity. Finite-rank approximation to $M_\phi$ and $aL\ge\epsilon_*I$ show that below any $c<\epsilon_*$ there are only finitely many independent spectral directions: beyond a sufficiently deep finite ball, $g\phi<\epsilon_*-c$. Min-max therefore also excludes extra finite eigenvalues in gaps or extra multiplicities below that cutoff. Endpoints at eigenvalues require a separate inclusion convention and are not covered by the gap statement.

Full-state compactness in such windows requires more than this eigenvalue argument. For real $z\le c<\epsilon_*$ put

$$
R_D(z)=I_D(aL_D-zI)^{-1}I_D^*,
\qquad R(z)=(aL-zI)^{-1},
\qquad \|R_D(z)\|,\|R(z)\|\le(\epsilon_*-c)^{-1}.
\tag{55.19}
$$

The same uniformly coercive Galerkin argument as in (55.12) proves strong convergence $R_D(z)\to R(z)$, uniformly for $z$ in a compact interval and on compact sets of right-hand sides. A finite normalized eigenvector, zero extended as $f_D$, satisfies exactly

$$
f_D=gR_D(z)M_\phi f_D.
\tag{55.20}
$$

The family of right-hand sides is strongly precompact because $M_\phi$ is compact. The uniform inverse bound and convergence then force strong precompactness of *all* these eigenvectors in the specified window, with unit limiting norm and the correct full eigen-equation. This proof retains every angular mode and does not replace strong compactness by local operator convergence. Combining it with the multiplicity count, any sequence of finite orthonormal bases has subsequences converging to common orthonormal bases. Their zero-extended finite spectral projections converge in operator norm to the common finite-rank window projection. Degenerate eigenspaces are preserved as spaces; independently chosen vectors inside them need not converge without a subsequence or basis choice.

The proofs use only containment of sufficiently deep finite balls inside each actual domain. They also hold for varying original sources with accepted indices tending to infinity by (55.2), or for any supplied family whose minimum contained-ball radius tends to infinity. They do not identify those sources' INITIAL syntax. The killed-field alternative of (55.12) has a vanishing norm perturbation, so the same gap-window conclusions hold there, with its finite eigenvectors and values explicitly understood as belonging to that alternative. Outside the stated windows, local operator or scalar-resolvent convergence alone is not a preservation theorem. □

**Proposition 55.6 (an exact original whole-rho history with a hidden negative sector).** Take the actual INITIAL source $t=E=\langle\beta,\alpha\rangle$ and the original fixed cap $H=3$. In the TM30/57 Clifford port, $E(\alpha)=A$, $E(\beta)=B$, $A^2=1$, $B^2=-1$, $AB+BA=1$. The complete actual history

$$
\operatorname{Read}[BA];\quad\rho[\mathrm{accept}];\quad
\operatorname{Read}[A+B];\quad\rho[\mathrm{reject}];\quad
\operatorname{Read}[A+B];\quad\operatorname{Stop}
\tag{55.21}
$$

has leaf counts $2,3,5$ for the initial, accepted and refused candidates. The current accepted tree is $\langle\langle\beta,\alpha\rangle,\beta\rangle$; the refused candidate is
$\langle\langle\langle\beta,\alpha\rangle,\beta\rangle,\langle\beta,\alpha\rangle\rangle$ and is not installed. INITIAL and its original target remain $t$ and the literal tag-1 target $(1,(1,1),BA,A+B)$. The geometric quantities below belong to this original source and this actually accepted version; none is an additional numerical Read or a later-state replacement target.

In the order $(o,L,R,LL,LR)$ its actual matrix and common restricted field are

$$
L_D=\begin{pmatrix}
2&-1&-1&0&0\\
-1&3&0&-1&-1\\
-1&0&3&0&0\\
0&-1&0&3&0\\
0&-1&0&0&3
\end{pmatrix},
\qquad \phi|D=(1,1/2,1/2,1/4,1/4)^T.
\tag{55.22}
$$

There are six exterior killing seams, two each at $R,LL,LR$. The newly killed field, and the exterior input for the common restriction, are respectively

$$
\phi_D^0=(21,9,7,3,3)^T/26,
\qquad b_D=(0,0,1/2,1/4,1/4)^T.
\tag{55.23}
$$

For the explicitly sufficient-coupling choice $a=1,g=16$, the common-restriction amplitude matrix has diagonal $(-14,-5,-5,-1,-1)$ and the same $-1$ seam entries. Its *full* characteristic polynomial is

$$
D_o(z)=-(z+1)(z^4+25z^3+185z^2+465z+202).
\tag{55.24}
$$

It has the normalized root-invisible eigenstate
$\psi_{\rm hid}=(0,0,0,1,-1)^T/\sqrt2$ at $z=-1$, with multiplicity one. All five eigenvalues are negative. The remaining four are exactly the roots of the displayed quartic, retaining their full algebraic multiplicities and their reconstruction below.

Proof. The source substitution is literal (55.1). Associativity of the original Clifford leaf product gives $(BA)B=B(AB)=B-B^2A=A+B$, confirming every original Read in (55.21), including the unchanged Read after refusal. The guard accepts at three leaves and refuses the five-leaf whole candidate. The geometric nodes, labels and seams of the installed version are therefore exactly those in (55.22); $LL$ is a $\beta$ leaf, $LR$ an $\alpha$ leaf and $R$ a $\beta$ leaf. The potential weights ignore these labels but the joint source record retains them.

Multiplication verifies $L_D(\phi|D)=\mathbf1_o+b_D$ and $L_D\phi_D^0=\mathbf1_o$. The complete boundary and norm quantities are

$$
Q_D(\phi|D)=11/8,
\quad \|\phi|D\|^2=13/8,
\quad \sum_{p\in D}\phi(p)^3=41/32,
\quad Q_D(\phi_D^0)=21/26.
\tag{55.25}
$$

They differ even though both field choices concern the same actual source domain. The internal common-field gradient energy is $5/8$ and its remaining continued exterior energy is $3/8$, whereas its zero-extended amplitude energy is $11/8$. These values consume, rather than delete, the six boundary seams.

Put $x=-5-z$, $y=-1-z$, $r=-14-z$, $B_z=xy-2$. The internal left block has determinant $yB_z$, the right block determinant $x$, and the root-deleted determinant is $P_o=yB_zx$. Direct elimination gives

$$
D_o=y\bigl((rx-1)B_z-xy\bigr),\qquad
S_o(z)=r-\frac y{B_z}-\frac1x,
\qquad G_o(z)=P_o(z)/D_o(z).
\tag{55.26}
$$

Expanding gives (55.24). The internal exceptional energies are $-1,-5,-3-\sqrt6,-3+\sqrt6$. At $-1$ the two left leaves support their opposite-sign kernel vector and cancel at their parent; $D_o$ has a simple zero because the quartic equals $-102$ there, while $G_o$ cancels the $z+1$ factor. At $-5$, compatibility forces the retained root amplitude zero and the sole right internal kernel coefficient then zero, so no full eigenvector remains; indeed $D_o(-5)=8$. At the two left-block eigenvalues $B_z=0$, their left-root coefficient is nonzero and cannot cancel through the invertible right block when the retained root is zero; again there is no full eigenstate at that exceptional energy. Algebraically $D_o=-xy^2\ne0$ there. The exceptions have thus been checked with full block equations, not assigned spurious inverse values.

At each quartic root $z$, all inverses in (55.26) exist and the full root-amplitude-one eigenvector and its norm are

$$
\psi_z=(1,y/B_z,1/x,1/B_z,1/B_z)^T,
\qquad N(z)=1+\frac{y^2+2}{B_z^2}+\frac1{x^2}=-S_o'(z).
\tag{55.27}
$$

The full normalized state is $\psi_z/\sqrt{N(z)}$; the boundary amplitude alone is not unit full norm. The endpoint recurrence or these equations show that each such root eigenspace has dimension one. The leading principal minors of $-\mathsf H_D$ are $14,69,340,271,202$, so Sylvester's criterion gives all five negative eigenvalues. The hidden vector contributes its own norm and multiplicity to that count. Its zero extension is not silently identified with an infinite eigenstate: the four child seams beyond $LL,LR$ give $\|(\mathsf H+I)I_D\psi_{\rm hid}\|^2=2$. In the common depth-one contrast channel, the first two normalized levels have matrix $\left(\begin{smallmatrix}-1&-\sqrt2\\-\sqrt2&1\end{smallmatrix}\right)$, with minimum $-\sqrt3<-1$. Those levels occur in sufficiently advanced actual whole-rho domains, and the compactness proof (55.14) applies to this invariant channel: its kinetic lower bound is $\lambda_*$ and its diagonal potential tends to zero. It yields a negative normalized channel ground state below $-1$. Both depth-one vertices supply identical channel copies, giving two channel-ground eigendirections; any coincidence with another channel adds its multiplicity as in (55.18). The finite value $-1$ therefore need not stay fixed under continuation; the window theorem preserves limiting full states and multiplicities, not each finite energy verbatim.

One rational off-spectrum check retains normalization as well as response:

$$
\begin{aligned}
S_o(-16)&=3258/1793,&G_o(-16)&=1793/3258,\
\psi_{-16}&=(1,15/163,1/11,1/163,1/163)^T,
&\|\psi_{-16}\|^2&=3268885/3214849,\
(\mathsf H_D+16I)\psi_{-16}&=S_o(-16)\mathbf1_o,
&\frac{\langle\psi_{-16},\mathsf H_D\psi_{-16}\rangle}{\|\psi_{-16}\|^2}
&=-46460566/3268885.
\end{aligned}
\tag{55.28}
$$

This check is a resolvent reconstruction and a normalized trial, not an eigenstate at $-16$. The root-visible eigenstates instead have the quartic energies and (55.27). The determinant was also calculated independently of the subtree recursion by the permutation formula for the matrix (55.22) with its potential diagonal: its coefficients in ascending powers are $(-202,-667,-650,-210,-26,-1)$, and the root-deleted coefficients are $(15,48,44,12,1)$. They reproduce (55.24)–(55.26). Exact rational elimination of (55.22) gives (55.23), and direct multiplication gives the hidden vector, norms, residual and principal minors. These finite identities are reproducible ordinary exact calculations; the general source and infinite conclusions rest on the preceding proofs.

As a boundary discriminator at $g=0$, the normalized constant on these five actual sites has $Q_D=6/5$. The graft's single outgoing killing would instead give $1/5$, while a closed finite matrix would give zero. Neither is compression of the present common operator. A three-node identity or a root response with the hidden factor cancelled would miss this actual irregular-domain distinction. □

**Definition 55.7 (INITIAL information and the retained resource boundary).** The unlabelled common graph, field, norm and operator of Definitions55.1–55.2 are the same for every finite INITIAL tree. They deliberately depend on the actual root and persistent addresses while forgetting initial labels, brackets beyond their finite birth domains, and the timing and content of actual events. Thus a universal common ground state or full common spectrum cannot authenticate which INITIAL syntax was supplied. It does not even distinguish the one-leaf sources $\alpha$ and $\beta$, whose first branching times differ under the original substitution. The joint correspondence is faithful because it *retains* the original source/history; its geometric projection is not injective.

Finite domains can distinguish some original source histories, as Proposition55.6 does, but calculating their matrices presupposes the correct actual domain and its version. The numerical Read histories are not spectral ports. Reuse §52.6's source-specific INITIAL escape obstruction in its exact Clifford/fixed-preparation/guard scope; no new blind-pair example or acquired certificate is claimed from that prerequisite. Extra syntax, provenance or spectrum cannot be inferred from its originally accepted numeric target or retagged verification receipt. Likewise this chapter neither changes $\mathcal D_2$ nor gives §54.1's untagged layers, independent arbitrary unbounded $a$, exact actuation or jointly adversarial Read errors an occurrence-field realization. The exact/hidden-gain, noise and update/Read-budget laws of §§37–54 remain on their own sources, targets and menus.

A consumer needing an INITIAL-dependent finite spectral output must expressly pay for an authentic initial code or a genuinely separating source channel. The existing `ActualTreeReadoutAcquisition` has original immutable-source address replies `alpha/beta/branch/absent`, actual acquired terminal histories, and its own Boolean task and fees. A declared syntax-output consumer of a retained complete authentic initial history can use the existing source decoder; it does not give those queries or a new numeric output task to the original controller for free. TM23's paid replay/birth-record contract can supply its own finite initial reconstruction only with its actual navigation, absolute epoch, root/version and record permissions. An early record is useful only when it was genuinely acquired, retained and bound to INITIAL. An old-version answer cannot be obtained from a later current register without that retained record or a separately authorized supplier. None of these conditions is supplied by $\phi$, (55.18), a common limit or (55.21).

There is no source-dependent initialization, tag, copy, reset, navigation, resampling, calibration or free authenticated memory in the original numerical execution. Every original repeated Read, attempted update, refusal, prepared context if present, and Stop remains a separate event with its original resources. Preparing the new field or an amplitude state and measuring it would require additional suppliers and prices. The finite rational determinants and algebraic eigenstates above are exact mathematical quantities, not claims of fixed-word arithmetic, finite-bit acquisition or physical measurement. For finite operators, an expressly supplied operator error bound $\|\Delta\mathsf H\|\le\eta$ gives eigenvalue error at most $\eta$ by the classical variational inequalities; identifying a window or state also requires its gap. This is conditional precision analysis, not a noise law or calibration port inferred from the original Read history. No all-source stable syntax inverse, exact minimax sensor rate or free averaging is obtained.

**Definition 55.8 (consumed mathematics, scope and remaining bridges).** The primary ground-state-transform scope is Keller–Pinchover–Pogorzelski, *From Hardy to Rellich inequalities on graphs*, [arXiv:1909.02286v1, §6, proof of Theorem6.1](https://arxiv.org/pdf/1909.02286v1), as recorded in [the existing graph-transform note](../../../Library/GraphInvariants/kellerpinchoverpogorzelski2021rellich.md). Its general identity is an intermediate in (55.10), not a new graph theorem or a supplied square-summable ground state. [Dörfler–Bullo's existing note](../../../Library/GraphInvariants/dorflerbullo2013kron.md) records [arXiv:1102.2950, §2.1](https://arxiv.org/pdf/1102.2950); that primary network-closure lemma requires its loopy-Laplacian assumptions and at least two retained nodes. The singleton, indefinite spectral account here instead consumes the finite algebra given in §52.4, with its positivity and inverse boundaries. `SchurMinimum.schur_quadratic_is_least` and `SchurComplementAssociativity.schur_complement_associativity` retain their positive-block or invertibility hypotheses, which remain part of their stated scope.

The primary text of Gerald Teschl, [*Mathematical Methods in Quantum Mechanics*](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorems4.10 and6.19, gives the min-max and compact-resolvent-difference Weyl tools consumed above. The latter source is already cited in [the existing Lenz–Stollmann–Wingert note](../../../Library/Weil/lenz2010compactness.md); its mixed theta operator is not substituted for this occurrence graph. Teschl Theorem6.38 and Lemma6.39 distinguish strong-resolvent spectral inclusion/projection limits from norm-resolvent spectral equality. The negative-window norm projection conclusion here additionally uses (55.19)–(55.20), compact potential and multiplicity control; it is not inferred from local convergence alone. These primary scopes, finite elimination, bounded-rate heat, orthogonal level contrasts and Hilbert-space variational tools are classical intermediates. The result claimed as `repo-derived` is their joint application to *all original whole-rho source histories*, with the actual irregular domains, two-child boundary data, isolated field, binding gap, all-near-minimizer compactness, hidden spectral channels and retained INITIAL boundary. No global mathematical priority or exhaustive literature absence is claimed.

The neighbouring covered contracts retain their distinct scopes. TM22–23 supplies occurrences, births, exhaustion and its paid source-recovery permissions. Auric §§12–14 supplies affine moment and positive Gaussian closure, while §§15–19 and §§22–35 keep their separately supplied shape, phase, quotient and symmetry laws; these do not supply unit occurrence conductance or this field. Original H43's same-run six-row acquisition uses its growing-memory delayed-output machine. Ordered probability-history modules retain named dependent coordinates, conditional archives, finite law completion and their explicitly introduced innovation sources; their weak law compactness is not (55.14) or (55.20). Observer86's conditional $E_m$ register evaluator pays for its own tables, fields, transactions and all-representative consistency. KBonacci15–18's protected INITIAL labels and width-five calendar boundary have their original joint source and complete-block fees. No source/action/port/cost-preserving map from these acquisition contracts to a spectral instrument has been established here. Their known deductions are reused as scope prerequisites, not duplicated or identified by notation.

The positive field and binding results answer an actual missing same-source correspondence, but use exponential rooted occurrence geometry with unit seams and a positive kinetic escape threshold. They do not select Euclidean spatial dimension three, identify graph degree with dimension, prove an isotropic Euclidean second-order point-source law, establish all-positive-coupling negative binding, determine a sharp threshold, or establish extensive many-body stability. Unit scale is fixed; source growth is not mesh refinement. Alternatives on moving-root grafts, including weighted or weak-coupling contracts, keep their own incomparable resources and hypotheses. The unscreened single-seam obstruction and screened nonattainment of §52 remain valid for that different actual source family.

Hypothesis15.1's native full-rotation bridge, faithful actual displacement bridge, physical maintenance/leakage/precision/record price bridge and common-environment propagation/task-capacity bridge all remain unproved. A native operation/metric/field/kinetic realization, authentic spectral acquisition, physical clock and component laws, and many-body scale consistency require separate evidence. The present joint realization is ordinary conditional mathematics; it does not establish a physical realization or the full why-three-dimensions objective.

## 追加锚（本行以下为增补区）

## 56. Fixed positive Read noise: the exact original minimax risk and nonattainment

**Definition 56.1 (unchanged INITIAL contract and contact parameter).** This chapter uses exactly original Boundary Definitions54.1,45.1,46.1,51.1, with

$$
E=\operatorname{Im}\mathbb H,\qquad W=E\oplus\mathbb H,\qquad
\mathcal D_2=E\times
\{b:|b|\in\{7,25\},\ \operatorname{Re}b\ge(4/5)|b|\}.
\tag{56.1}
$$

The initial $a$ is independent of $b$, arbitrary and unbounded, including zero. Both radius caps are closed and unlabelled. The sole overwritten register has only the original exact updates
$A_c(a',b')=(c\times a',b'c)$ for pure imaginary $|c|\le1$, and
$A_d(a',b')=(\operatorname{Im}b',-a')$.
Every nondestructive Read returns $a'+e$ with $|e|\le\delta$; the closed error balls may be jointly adversarial, correlated and history dependent. Repeated Reads confer no averaging guarantee.
The controller has common source-independent initialization, is deterministic and causal on actual finite prefixes, and retains every actual Read, ordered action identity and Stop. Every original finite or natural-number-indexed countable complete history remains in scope, with its original $W$-valued estimate and no event after an infinite prefix. The target is the full INITIAL $(a,b)$ with its Euclidean distance, not a later state, a hidden coordinate alone or a radius label. There is no reset, copy, hidden tag, new archive or observation port, limit Read or native realization privilege.

Fix $0<\delta\le1/100$. Keep $K,t_R,S_R,B,\rho_-,\rho_+$ exactly as defined in original (54.2); in particular
$B(\rho,\delta)=\sqrt{2\delta^2+S_{25}(\rho,\delta)^2}$,
$\rho_-=\delta/12$ and $\rho_+=\delta/12+\delta^2/100$.
The new public parameter is the contact root

$$
g(\rho):=24\rho-7(1-K(\rho)),\qquad
g(\rho_*)=2\delta,\qquad \rho_-<\rho_*<\rho_+.
\tag{56.2}
$$

The risks $\mathcal E_\pi(\delta),R_N(\delta),R_\infty(\delta)$ and policy classes are the unchanged original (46.3). The budget counts only original destructive updates; Reads, control descriptions, arithmetic, records and physical costs are separate resources.

**Proposition 56.2 (unique root, explicit value and order).** The root in (56.2) exists uniquely in $[0,1/10]$. With $m=7+2\delta$ it is

$$
\rho_*=
\frac{24m-7\sqrt{625-m^2}}{625}
=\frac{4\delta(7+\delta)}
 {24m+7\sqrt{625-m^2}}.
\tag{56.3}
$$

Furthermore $B(\rho_*,\delta)<1$, and $B(\rho,\delta)$ is strictly increasing in $\rho$ on $[0,1/10]$.

Proof. On this interval $K\ge99/100$ and
$g'(\rho)=24-7\rho/K>23$. At the lower comparison point,
$g(\rho_-)-2\delta=-7(1-K(\rho_-))<0$.
Use the unchanged endpoint estimate (54.16), whose assumptions are precisely $\rho=\rho_+$ and $0<\delta\le1/100$:

$$
g(\rho_+)-2\delta
\ge\frac{551}{3025}\delta^2>0,\qquad
0<\rho_+\le\delta/11<1/10.
\tag{56.4}
$$

Continuity and strict monotonicity give the asserted root and both strict orders. The unsquared root equation is $24\rho+7K=m$. Squaring gives
$625\rho^2-48m\rho+m^2-49=0$, with roots
$(24m\pm7\sqrt{625-m^2})/625$.
The plus root has $m-24\rho<0$: here $7<m\le351/50$ and $\sqrt{625-m^2}>23$, so $7m-24\sqrt{625-m^2}<0$.
It cannot satisfy the unsquared equation. For the minus root,
$m-24\rho=7(7m+24\sqrt{625-m^2})/625>0$, so it has the required sign. Rationalizing its numerator gives the second expression in (56.3), using $m^2-49=4\delta(7+\delta)$.

Strict increase of $B$ is exactly the derivative calculation (54.11), not a new envelope. For the needed comparison with the large-error witnesses, $\rho_+\le\delta/11$ gives
$25\rho_+\le1/44$ and
$t_{25}(\rho_+,\delta)^2\le100\delta+625\delta^2/121<121/100$.
Consequently

$$
B(\rho_*,\delta)^2\le B(\rho_+,\delta)^2
<\frac1{5000}+\left(\frac{247}{440}\right)^2<1.
\tag{56.5}
$$

These statements use only the public $\delta$. They supply neither a source observation nor a radius label. □

**Theorem 56.3 (strict bound for every original policy).** Every individual authorized original policy, including the entire finite/countable class $\mathcal P_\infty$, satisfies

$$
\mathcal E_\pi(\delta)>B(\rho_*,\delta).
\tag{56.6}
$$

Each lower bound below comes from two fixed original INITIAL sources and a common actual complete history.

Proof. Fix $\pi$. Before the first anchor, follow the common zero-report branch. For $a=0$ all those reports are exact. For either $a=\delta v$ or $a=-\delta v$, with any fixed unit $v\in E$, every internal prefix still has visible norm at most $\delta$, so its opposite is a legal error yielding the same zero report. Thus this branch, its action identities and its stopping decision are determined without the hidden source or a radius tag.

Reuse the first-anchor state law and contraction argument from original §§40,46 and Theorem54.2. If a first anchor occurs, it is a finite event. Before it the actual internal product and visible map are

$$
p=c_1\cdots c_k,\qquad
M=(c_k\times)\cdots(c_1\times),\qquad
(a',b')=(Ma,bp).
\tag{56.7}
$$

The empty product is one and the empty $M$ is the identity. If $p\ne0$, write
$p=\sigma\lambda q$ with $0<\lambda=|p|\le1$,
$\sigma\in\{1,-1\}$,
$q=\alpha+\nu u$, $\alpha\ge0$, $\nu=\sqrt{1-\alpha^2}$ and $|u|=1$.
The sign is retained in the actual response, and $\|M\|\le\lambda\le1$.
The first anchor gives $(\sigma\lambda\operatorname{Im}(bq),-Ma)$.

The original continuation argument applies whenever, just after this anchor, both current difference slots have norm at most $2\delta$.
Every common $A_c$ contracts them separately. Every common $A_d$ sends them to
$(\operatorname{Im}\Delta b',-\Delta a')$, preserving that bound.
At each actual Read use the midpoint of the two current visible values; its two errors are opposite half differences and lie in the closed $\delta$ balls.
Equal actual report prefixes force the same next event, control and Stop.
The complete finite records coincide; for a countable history every finite prefix coincides. This adds no event after an infinite prefix and uses only the output already assigned to that complete record by the original contract.
Two-run comparison here is a proof of a lower bound, not a second register supplied to $\pi$.

The following cases exhaust the common zero-report branch.

1. **No anchor, or an erased register before the first anchor.** Take $a=0$ in both runs and $b_0=20-15i$, $b_1=20+15i$. These are actual radius25 cap points. Without an anchor every Read remains zero, including an infinite internal/Read history or a finite Stop. If $p=0$ at a finite first anchor, one earlier internal control was zero; with $a=0$ that action erased the whole register, so subsequent states and records agree. The INITIAL half-distance is $15>B(\rho_*,\delta)$.

2. **A nonzero product with $\alpha\ge3/5$.** Take $a=0$ and exactly the two different-radius same-projection sources of original Lemma45.2(ii): for $3/5\le\alpha<4/5$ set its $h=(4/5)\nu-(3/5)\alpha$, $H=(4/5)\nu+(3/5)\alpha$, choose $r=(25h+7H)/2\in[25h,7H]$ and $b_R=(\sqrt{R^2-r^2}+ru)q^{-1}$; for $\alpha\ge4/5$ choose $b_R=Rq^{-1}$, $R=7,25$. Their source legality and identical projections are the unchanged lemma. Both full states agree after the first anchor. Their INITIAL distance is at least $25-7=18$, hence the half-distance is at least $9>B(\rho_*,\delta)$. Zero future errors give a common record.

3. **A nonzero product with $0\le\alpha<3/5$ and $\rho>1/10$.** Use original (45.4),
$\rho=(3/5)\nu-(4/5)\alpha>0$ and
$K=(3/5)\alpha+(4/5)\nu=\sqrt{1-\rho^2}$.
Take $a=0$ and the original Lemma45.2(i) sources
$b_\pm=(\pm25\rho+25Ku)q^{-1}$.
They have identical first-anchor projections and identical full states thereafter. Their INITIAL half-distance is $25\rho>5/2>B(\rho_*,\delta)$.

4. **The same direction range, with $0<\rho\le\rho_*$.** Instantiate exactly the original cross-layer cap witnesses (54.7):

$$
h=(4/5)\nu-(3/5)\alpha=\frac{7K+24\rho}{25},\qquad
l=(4/5)\alpha+(3/5)\nu,\qquad
b_7=(7u)q^{-1},\quad b_{25}=(25l+25hu)q^{-1}.
\tag{56.8}
$$

Use $a=0$ in both runs. The original cap check gives $|b_7|=7$,
$\operatorname{Re}b_7=7\nu\ge28/5$, $|b_{25}|=25$ and
$\operatorname{Re}b_{25}=20$; $l^2+h^2=1$.
Monotonicity of $g$ gives
$0<g=25h-7\le2\delta$.
The first-anchor difference is $(\sigma\lambda gu,0)$, so the common midpoint continuation above is legal. The actual INITIAL half-distance, rather than a distance between later visible states, is

$$
\frac{|b_{25}-b_7|}{2}
=\sqrt{\frac{(25l)^2+(25h-7)^2}{4}}
=\sqrt{144-\frac72g}
\ge\sqrt{144-7\delta}>1>B(\rho_*,\delta).
\tag{56.9}
$$

5. **The remaining range $\rho_*<\rho\le1/10$.** Use the unchanged same-layer witnesses (54.8), now in their already proved range $\rho\ge\rho_->0$:

$$
t=t_{25}(\rho,\delta),\qquad
x_0=(\delta v,(-25\rho+25Ku)q^{-1}),\qquad
x_1=(-\delta v,(t+(25K-2\delta)u)q^{-1}).
\tag{56.10}
$$

Both hidden points are original radius25 cap points by (54.9), and the independent initial $a$ contract allows both full sources.
Every pre-anchor Read has the same zero report with error norm at most $\delta$. Immediately after the anchor the visible difference has norm $2\lambda\delta\le2\delta$, and the hidden difference has norm $2\delta|Mv|\le2\delta$.
The same common continuation therefore supplies an actual complete record. Original (54.10), including the initial $a$ difference, gives
$|x_1-x_0|/2=B(\rho,\delta)>B(\rho_*,\delta)$ by strict monotonicity.

In each case both sources can be fixed before the run: the pre-anchor zero branch determining the case and $q$ does not depend on $b$, and the selected $a$ values legally realize that branch. Sources are not changed during continuation. The common complete record has one estimate in $W$; the original same-data half-distance argument forces loss at least the stated half-distance for one of its two fixed INITIAL sources.
This proves the strict inequality separately for every $\pi$, without a uniform positive excess over all policies. Contractions, extra anchors, adaptive future controls, repeated Reads, early Stops and countable histories are all included. □

**Definition 56.4 (public finite family and total original decoder).** For every public parameter
$\rho\in(\rho_*,\rho_+]$, reuse exactly original (54.12)–(54.14), replacing their single selected value $\rho_+$ by this $\rho$. Explicitly set

$$
\alpha=(3/5)K(\rho)-(4/5)\rho,\qquad
\nu=(4/5)K(\rho)+(3/5)\rho,\qquad q=\alpha+\nu i,
\quad c_1=j,\quad c_2=-\alpha j+\nu k,\quad
h=\frac{7K(\rho)+24\rho}{25},\quad T=\frac{7+25h}{2}.
\tag{56.11}
$$

These are public exact constants, $c_1,c_2$ are unit pure imaginary controls, and $c_1c_2=q$. The controller $\pi_\rho$ executes the fixed original events

$$
\operatorname{Read}(y_0);\ A_{c_1};\
\operatorname{Read}(y_1);\ A_{c_2};\
\operatorname{Read}(y_2);\ A_d;\
\operatorname{Read}(y_3);\ \operatorname{Stop}.
\tag{56.12}
$$

Keep all four reports and all three action identities and Stop. On the entire report space $E^4$, put $r=|y_3|$, select $R=7$ if $r\le T$ and $R=25$ otherwise, and use the unchanged scalar decoder and closed-ball projection (54.14):

$$
\begin{aligned}
d_R^-&=\min\{R,\max(0,r-\delta)\},&
d_R^+&=\min\{R,r+\delta\},\\
\ell_R&=\sqrt{R^2-(d_R^+)^2},&
u_R&=\sqrt{R^2-(d_R^-)^2},\\
\widehat s&=
\begin{cases}
(\ell_R+u_R)/2,&\ell_R>R\rho,\\
(u_R-R\rho)/2,&\ell_R\le R\rho,
\end{cases}
&\widehat w&=P_R(y_3),\\
\widehat x_\rho&=(y_0,(\widehat s+\widehat w)q^{-1}).&&
\end{aligned}
\tag{56.13}
$$

Here $P_R(y)=y$ for $|y|\le R$, and $P_R(y)=Ry/|y|$ otherwise. In particular zero reports require no division. For every report, including impossible reports, $0\le d_R^-\le d_R^+\le R$, so this is a total $W$-valued decoder. The two middle report values need not enter the output formula, but their actual acquisition and retention are part of (56.12).
The computational branch $R$ is determined from $y_3$, not supplied at initialization as a cap tag. The only initial $a$ estimate is its acquired first report $y_0$.

**Theorem 56.5 (exact own risk and its actual maximum).** For every $\rho\in(\rho_*,\rho_+]$, the lawful finite policy in Definition56.4 has exactly three original updates and four actual Reads, and

$$
\mathcal E_{\pi_\rho}(\delta)=B(\rho,\delta).
\tag{56.14}
$$

Its worst loss is realized by explicit original sources and legal errors. At the common witness report its output is also the unique Chebyshev center of that report's full INITIAL candidate fiber.

Proof. The sole additional condition needed to reuse the original upper-bound proof is strict layer separation. Proposition56.2 gives
$g(\rho)>g(\rho_*)=2\delta$.
For any actual original source $bq=s+w$, the unchanged cap estimates from §45 and Theorem54.4 give
$s\ge-R_0\rho$, $R_0h\le|w|\le R_0$, $R_0=|b|$.
Thus the actual fourth report obeys

$$
R_0=7\ \Longrightarrow\ r\le7+\delta<T,\qquad
R_0=25\ \Longrightarrow\ r\ge25h-\delta>T.
\tag{56.15}
$$

The decoder selects the true layer on every legal history.
Apply exactly the original scalar interval estimates (54.17)–(54.19) to this same report and the true $R_0$: they imply
$|\widehat s-s|\le S_{R_0}(\rho,\delta)\le S_{25}(\rho,\delta)$.
In particular the allowed-negative-sign branch still uses its own report condition $r\ge R_0K- \delta$; no independently optimal radial endpoints are combined.
The unchanged ball-projection estimate gives $|\widehat w-w|\le\delta$, and the actual initial Read gives $|y_0-a|\le\delta$ for every unbounded initial $a$.
Their orthogonal INITIAL error decomposition (54.20) proves the upper bound $B(\rho,\delta)$ on the whole source and all jointly adversarial errors. No statistical independence is used.

For equality instantiate the published witness (54.22) at this $\rho$:

$$
x_0=(\delta j,(-25\rho+25Ki)q^{-1}),\qquad
x_1=(-\delta j,(t_{25}(\rho,\delta)+(25K-2\delta)i)q^{-1}).
\tag{56.16}
$$

The existing cap check (54.9) applies throughout this parameter interval. The actual four errors are respectively
$(-\delta j,0,0,-\delta i)$ and $(\delta j,0,0,\delta i)$.
The first $j$ action kills both visible states, the next internal action keeps them zero, and the anchor exposes the two specified imaginary parts. All four actual reports, actions and Stop are common:

$$
(y_0,y_1,y_2,y_3)=(0,0,0,(25K-\delta)i).
\tag{56.17}
$$

This report is in the radius25 branch by (56.15). As in original Proposition54.5,
$d_{25}^-=25K-2\delta$, $d_{25}^+=25K$,
$\ell_{25}=25\rho$ and $u_{25}=t_{25}(\rho,\delta)$.
The equality branch in (56.13) therefore outputs the exact Euclidean midpoint of $x_0,x_1$. Their full INITIAL half-distance is $B(\rho,\delta)$ by (54.10), and each endpoint has that loss. The upper bound is consequently an attained maximum for this individual policy, not just a supremum approached by examples.

For any legal report of this finite word the full candidate fiber is compact: $y_0$ confines $a$ to a closed ball of radius $\delta$, both $b$ caps are compact, and all four exact-menu/error constraints are closed. Classical finite-dimensional minimax-center existence applies in $W$; it supplies an output center, not another event or source port. The explicit decoder uses centers of enclosing scalar intervals and is not claimed to minimize every report's exact fiber radius. At (56.17), however, the upper bound encloses the entire fiber in its midpoint ball of radius $B(\rho,\delta)$, while the two actual endpoints force that radius. A ball of this radius containing two points at distance $2B(\rho,\delta)$ has their midpoint as its unique center. Thus the asserted local center attainment follows.
Any alternative decoder for the same finite word also faces those endpoints; its risk cannot be smaller than $B(\rho,\delta)$. None of these decoder or maximum attainments asserts attainment of the infimum over policies. □

**Proposition 56.6 (closed contact pair and all-continuation obstruction).** At $\rho=\rho_*$, the same original three-update word has two legal fixed INITIAL sources with the common four reports $(0,0,0,(7+\delta)i)$ and INITIAL half-distance $\sqrt{144-7\delta}$. Every authorized future continuation of that common prefix can still be given identical actual reports and actions for these two sources. In particular arbitrary report postprocessing or continuation cannot turn the contact direction into a policy with risk $B(\rho_*,\delta)$.

Proof. Use (56.11) with $\rho=\rho_*$, and let
$l=(4/5)\alpha+(3/5)\nu$.
The actual full source pair is the original cross-layer pair (54.7), written in original coordinates:

$$
x_7=(0,7\nu+7\alpha i)=(0,(7i)q^{-1}),\qquad
x_{25}=(0,20-15i)
       =(0,(25l+(7+2\delta)i)q^{-1}).
\tag{56.18}
$$

Indeed $25h=7+2\delta$ at contact,
$l^2+h^2=1$ and $\alpha l+\nu h=4/5$.
The inner source has norm7 and real part $7\nu\ge28/5$; the outer source has norm25 and real part exactly20, on its original closed cap boundary. Both initial visible coordinates are exactly zero.
Under the literal original events (56.12), the first three true visible values are zero. The fourth values are respectively $7i$ and $(7+2\delta)i$.
Choose errors $(0,0,0,\delta i)$ and $(0,0,0,-\delta i)$.
They are legal on the closed error-ball boundary, and give the common report $(7+\delta)i$ exactly. The full ordered action records and Stop, if taken there, are identical.

The two fixed INITIAL values satisfy

$$
\frac{|x_{25}-x_7|^2}{4}
=\frac{(25l)^2+(2\delta)^2}{4}
=\frac{625-(7+2\delta)^2+4\delta^2}{4}
=144-7\delta.
\tag{56.19}
$$

This is the full INITIAL distance. It does not pair independently chosen maxima from different realizations.
After the fourth Read the actual residual states are $(7i,0)$ and $((7+2\delta)i,0)$: their histories agree, while their visible state difference is exactly $2\delta i$ and their hidden difference is zero.
The original two-slot contraction and midpoint continuation used in Theorem56.3 preserves differences of norm at most $2\delta$ in each slot under every future original action. Every subsequent actual Read can therefore be common with errors of norm at most $\delta$.
Causality keeps the future actions and stopping decisions common, for finite or countable continuations, with no post-infinite event. The erased real-coordinate distinction cannot be recovered by any of these continuations.

The two closed report balls touch at the actual fourth report, and the outer cap point attaining the smaller outer projection is allowed. Strict $g(\rho)>2\delta$ is consequently essential for uniform separation in this word; equality cannot be repaired by a choice of threshold or a decoder tie rule. The common-record half-distance gives risk at least
$\sqrt{144-7\delta}>1>B(\rho_*,\delta)$ for every such continuation. This is a source-realizable contact obstruction, not only an overlap of numerical ranges. □

**Theorem 56.7 (all budgets at least three, exact infimum and nonattainment).** For every $0<\delta\le1/100$ and every integer $N\ge3$,

$$
R_N(\delta)=R_\infty(\delta)=B(\rho_*,\delta).
\tag{56.20}
$$

No individual original policy in any of these classes attains this infimum. Every positive approximation tolerance is nevertheless realized by a finite three-update/four-Read policy with a total decoder.

Proof. Theorem56.3 supplies $R_\infty(\delta)\ge B(\rho_*,\delta)$, and $\mathcal P_N\subseteq\mathcal P_\infty$ supplies the same lower bound for $R_N$.
For an unambiguous tolerance choice, given public $\varepsilon>0$ take

$$
\rho_\varepsilon=\rho_*+
\min\left\{\frac{\rho_+-\rho_*}{2},\frac{\varepsilon}{26}\right\}.
\tag{56.21}
$$

It lies strictly in $(\rho_*,\rho_+]$.
Reuse the derivative bound (54.26), valid on the unchanged interval $[\rho_-,\rho_+]$, to obtain

$$
0<\mathcal E_{\pi_{\rho_\varepsilon}}(\delta)-B(\rho_*,\delta)
=B(\rho_\varepsilon,\delta)-B(\rho_*,\delta)
\le13(\rho_\varepsilon-\rho_*)\le\varepsilon/2<\varepsilon.
\tag{56.22}
$$

Definition56.4 and Theorem56.5 make this a source-independent lawful finite policy in $\mathcal P_3\subseteq\mathcal P_N\subseteq\mathcal P_\infty$, with its exact own risk. Taking the infimum for every positive $\varepsilon$ proves all equalities, without exchanging an update-budget limit with an infimum.
The strict individual inequality (56.6) rules out every optimizer, including a policy with countable complete histories. Conversely (56.22) rules out a uniform positive excess shared by all policies.

Equivalently the public choices
$\rho_m=\rho_*+(\rho_+-\rho_*)/(m+1)$, $m=1,2,\ldots$, give a sequence of separate finite policies with risks decreasing to the displayed infimum. This sequence is not one execution, adds no infinite-prefix operation, and does not authorize a root-direction limit Read.
The distinctions are exact: the global policy infimum is not attained; a report's minimax center can be attained; and each constructed $\pi_\rho$ has an attained own-policy worst loss (56.17). No claim is made that an arbitrary original policy's worst-loss supremum is attained. □

**Definition 56.8 (reused mathematics and retained limits).** The first-anchor state law, pure-imaginary menu, contractions, cap direction classification, cross-layer witnesses, same-layer witnesses, scalar decoder and envelope are the unchanged original §§40,45,46,51,54 prerequisites. The additional deduction is the exact contact root, the strict all-policy bound at that root, the enlarged admissible parameter interval for the existing finite decoder, and the exact fixed-positive-noise infima and their global nonattainment. The contact pair and the full INITIAL endpoint witnesses provide the actual same-history bridges. Original §54.8's fixed-positive-noise minimax question is answered by (56.20) in this range.

Same-data half-distance bounds, interval midpoints, closed-ball projections and finite-dimensional Chebyshev centers are mature mathematics. Reuse [Recovery Geometry §3.1–3.2](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md#31-候选纤维半径与恢复的最小最坏误差) in its stated source/target relation; its unrestricted per-fiber map selection is not an implementation theorem for an adaptive destructive controller.
Foucart–Liao, [*Optimal Recovery from Inaccurate Data in Hilbert Spaces: Regularize, but what of the Parameter?*, arXiv:2111.02601v1, §1.1 and Lemma11](https://arxiv.org/html/2111.02601v1), supplies classical same-data lower-bound background. Its subspace-approximation and fixed linear-observation assumptions in Theorem10, and the two-affine-norm-constraint assumptions in Theorem4, are not the union of two caps and the adaptive overwritten-register menu here. Neither theorem is used to assert this all-policy equality. The original §54.8 references on local centers retain their own scopes. These are ordinary *repo-derived* deductions on the declared original source, with no mathematical priority or current Lean/kernel certification claim.

The result fixes $0<\delta\le1/100$, exact real arithmetic and original exact actuation. It supplies no new result for $N\le2$, larger noise, randomized control, noisy actuation, higher asymptotic coefficients or a generic recovery framework.
Source preparation and calibration, exact directions and control identities, Read precision, report storage, arithmetic and control descriptions, finite-bit realization and physical costs remain separately supplied or priced. Three destructive updates and four Reads are only the original mathematical event counts.
The native full-rotation, faithful displacement, physical maintenance/leakage/precision/record-price and common-environment propagation/task-capacity bridges remain unproved. No extra source port, physical realization, full DEV/RH result or completion of a broader research objective follows from (56.20).

## 56.99 追加锚（本行以下为增补区）

## 57. Uniform paid acquisition of actual-image certificates at exact composition

**Definition 57.1 (source, target, actual replies and the two costs).** The source is one unknown complete, nonempty, finite ordered binary tree $U$ whose leaves have the literal labels $\alpha,\beta$. Brackets, left/right order, and distinct occurrences are retained. Use exactly

$$
\rho\alpha=\beta,\qquad \rho\beta=(\beta,\alpha),\qquad
\rho(S,T)=(\rho S,\rho T),\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
\tag{57.1}
$$

Fix public integers $d=3k$, $k\ge1$, $a,b\ge0$, $n=a+b\ge1$. The exact composition promise is

$$
C=(A,B)=M^d(a,b)
=\bigl(F_{d-1}a+F_db,\ F_da+F_{d+1}b\bigr),
\qquad N=A+B,
\tag{57.2}
$$

where $F_0=0,F_1=1$. Let $\mathcal T_C$ contain *every* complete ordered tree of this composition and let
$\mathcal P=\mathcal T_C\cap\operatorname{im}\rho^d$.
The Boolean target is literal membership in $\operatorname{im}\rho^d$, on all of $\mathcal T_C$. There is no promise that a negative source has the height of a positive source. The structural fact that an $N$-leaf complete binary tree has height at most $N-1$ is available; replacing the negative domain by trees of positive height is not.

An address is any finite word in $L,R$, with root $\varepsilon$ at depth zero. Its exact endpoint reply is $\alpha$ or $\beta$ at that labelled leaf, $\mathsf{br}$ at a branch, and $\varnothing$ after crossing a leaf. A legal query requests the endpoint of one such word with $|u|\le h$. It neither changes the tree nor requires a preceding query of its ancestors. This is the address port specified by `ActualTreeReadoutAcquisition.readout`; it is not a physical navigation operation. A policy has common source-independent initialization and empty acquired history. Each next address or Boolean return depends only on its own finite chronological actual query/reply history and the public parameters. It must halt correctly on every $U\in\mathcal T_C$.

For an actual terminal transcript $T$, its primary cost is $|Q(T)|$, where $Q(T)$ is the set of *distinct requested addresses*. Every reply type is paid. Its query-action count is the length of $T$, including repeats. Repeating an address can add an action without adding a paid address. Let

$$
D_h(a,b;d)=\min_\pi\max_{V\in\mathcal P}|Q(T_\pi(V))|,
\tag{57.3}
$$

with value $+\infty$ if no correct depth-$h$ policy exists. The maximum prices positive inputs; correctness and finite termination also include all negative inputs. $D_\infty$ allows arbitrary finite address depths, with the same finite-run requirement. Neither quantity is the original globally correct third-image `Strategy` optimization over every composition. Control computation, candidate tables, memory, word encoding, output events, and physical traversal have no price assigned by (57.3). The constructions below specify and pay every actual address request; they do not claim these other resources are free or have a runtime bound.

**Lemma 57.2 (literal block calculus and the positive family).** Put $X_t=\rho^t\alpha$. Then $\rho^d\beta=X_{d+1}$ and

$$
X_0=\alpha,\quad X_1=\beta,\quad
X_t=(X_{t-1},X_{t-2})\quad(t\ge2).
\tag{57.4}
$$

For $t\ge2$ put $w(u)=\#L(u)+2\#R(u)$. The *entire* endpoint table of $X_t$ is

$$
r_{X_t}(u)=
\begin{cases}
\mathsf{br},&w(u)\le t-2,\\
\beta,&w(u)=t-1,\\
\alpha,&w(u)=t\ \text{and }u\text{ ends in }R,\\
\varnothing,&\text{otherwise}.
\end{cases}
\tag{57.5}
$$

Write $z_t=L^{t-2}R$ for $t\ge2$. Thus $z_t$ is an actual $\alpha$ address of $X_t$. If $r_{X_t}(u)=\alpha$, deleting the first letter of $u$ cannot leave another $\alpha$ address of $X_t$. Heights are $\operatorname{ht}(X_t)=t-1$ for $t\ge1$. There are exactly

$$
p:=|\mathcal P|=\operatorname{Cat}_{n-1}\binom na
\tag{57.6}
$$

positive trees. They are obtained by replacing the leaves of every ordered $n$-leaf tree of composition $(a,b)$ by $X_d,X_{d+1}$ respectively, preserving every original bracket.

Proof. Equation (57.4) follows from the literal substitution. Along a path, $L$ subtracts one and $R$ subtracts two from the block index until index one or zero is reached. Every word of weight at most $t-2$ ends at an index at least two and is a branch. Weight $t-1$ ends at index one and gives $\beta$. Weight $t$ can reach index zero exactly when its last step is $R$; a last $L$ would already have crossed the index-one leaf. Larger weights cross a leaf. This proves all four cases, including absent replies, and the deletion assertion follows because the deleted positive weight makes the remaining weight strictly less than $t$. Induction in (57.4) gives the heights.

The substitution is injective on complete ordered trees. At one step an output root $\beta$ decodes to $\alpha$; the literal pair $(\beta,\alpha)$ decodes to $\beta$; any other image branch must decode recursively as a source branch. The special pair cannot also be the image of a source branch, since no one-step image has root $\alpha$. This gives a unique inverse on the image, and iteration remains injective. Since $\det M=-1$, an image of composition $C$ has initial composition exactly $(a,b)$. The classical Catalan shape count and the choice of $a$ labelled positions now give (57.6). These counts describe public candidates, not a known index of the actual source. □

**Theorem 57.3 (complete one-colour certificates, rigidity and actual histories).** For $V\in\mathcal P$ write $\mathcal A(V),\mathcal B(V)$ for its actual $\alpha,\beta$ address sets. A finite set $Q$ is a sound positive certificate at $V$ on the exact competitor domain $\mathcal T_C$ if and only if

$$
\mathcal A(V)\subseteq Q\quad\text{or}\quad\mathcal B(V)\subseteq Q.
\tag{57.7}
$$

Here sound means that *every* $U\in\mathcal T_C$ agreeing with $V$ at all requested endpoints in $Q$ is positive. In fact either complete colour frontier uniquely determines $V$ within $\mathcal T_C$. Moreover

$$
B-A=F_{d-2}a+F_{d-1}b\ge n>0.
\tag{57.8}
$$

The minimum static cost is $A$, and its unique minimum set is $\mathcal A(V)$. Every correct uniform policy's actual terminal paid set at a positive $V$ satisfies (57.7). If that actual cost is less than $B$, it contains *all* $\mathcal A(V)$, and

$$
|Q(T_\pi(V))|
=A+|Q(T_\pi(V))\setminus\mathcal A(V)|.
\tag{57.9}
$$

Proof. Reuse the static minimum, unique-optimum and sensitive-swap mechanisms supplied by `ActualImageAddressCertificate.result` and `rigidity`, as ordinary mathematical prerequisites. Their relevant literal structure can also be checked directly: every twice-substituted tree is assembled from $(\beta,\alpha)$ and $((\beta,\alpha),\beta)$ blocks. Every branch has both an $\alpha$ descendant and a $\beta$ descendant; every $\alpha$ is the right leaf of a $(\beta,\alpha)$ cherry. No $\alpha$ is a left leaf, and no terminal cherry is $(\beta,\beta)$. Further substitution preserves membership in the twice-image.

For sufficiency there is a useful symmetric reconstruction argument. Take either colour $c$, its full address frontier in $V$, and the finite trie consisting of all prefixes of these addresses. Every branch of $V$ lies in this trie because it has a $c$ descendant. Its missing child slots are therefore precisely opposite-coloured single leaves in $V$. A complete competitor agreeing at all these $c$ endpoints must contain the same trie. Its exact number of $c$ leaves is already exhausted there. Each missing slot must contain a nonempty all-opposite-colour subtree. The exact total leaf count is the minimum completion count already attained by $V$, so every slot must contain just one leaf. Hence the competitor equals $V$. This argument also proves the $\beta$-frontier sufficiency, without a height assumption on the competitor.

For necessity suppose that $x\in\mathcal A(V)$ and $y\in\mathcal B(V)$ both escape $Q$. Exchange just their leaf labels, retaining the entire shape. The resulting complete tree $W$ has composition $C$, and every endpoint except $x,y$ has exactly its former reply, including branches and absent endpoints. Let $x=rR$ and let $rL$ be its $\beta$ sibling. If $y=rL$, the new left leaf is $\alpha$, which is forbidden in an image. Otherwise the old cherry at $r$ becomes $(\beta,\beta)$, also forbidden. Thus $W$ is a same-composition negative agreeing on $Q$, proving necessity. Equation (57.8) is the Fibonacci difference in (57.2), with both coefficients at least one. The static statements follow immediately from (57.7).

Finally let a uniform policy actually accept $V$, after its own paid transcript. Any competitor agreeing on that paid set reproduces the *whole chronological history*: at each step the deterministic selector sees the same prefix and requests the same next address, with the same reply, including repetitions. It therefore takes the same finite return. Correctness makes the paid set sound. This is a causal proof about one actual transcript, rather than a replacement of acquisition by an existential static set. Below $B$, (57.7) forces the alpha frontier and yields (57.9). □

**Theorem 57.4 (exact depth solvability and independence above the frontier).** Define

$$
H=d+n-2+\mathbf1_{b>0}.
\tag{57.10}
$$

A uniform correct policy exists if and only if $h\ge H$. At every feasible cap,

$$
D_h(a,b;d)=D_H(a,b;d)=D_\infty(a,b;d).
\tag{57.11}
$$

The equality is on this exact composition contract; it adds no height promise for negatives.

Proof. A positive tree substitutes blocks into an $n$-leaf macro tree. Every macro leaf has depth at most $n-1$; its block height is $d-1$ for $\alpha$ and $d$ for $\beta$. This gives the upper bound $H$. A comb attains depth $n-1$ at a leaf of type $\beta$ when $b>0$; otherwise all leaves have type $\alpha$. For $n=1$ the appropriate sole block attains the same expression. Thus $H$ is the exact maximum positive height. Its attaining tree has a deepest $\alpha$ leaf: (57.4), or the twice-image cherry description, shows this first for each block and then for their assembled tree. Its $\beta$ sibling has the same depth $H$.

If $h<H$, exchange this deepest cherry's labels. It is a same-composition negative, unchanged at every endpoint of depth at most $h$. Every causal history remains common, so correct opposite returns are impossible. If $h\ge H$, query the finite union of all positive alpha frontiers and accept exactly when some candidate's entire alpha frontier has returned $\alpha$. Theorem57.3 proves correctness on every complete competitor, with no positive-height restriction on it. This gives finite termination and solvability.

For independence, take any correct policy with unrestricted finite query depths. Keep only its finitely many positive terminal executions, making the finite decision tree of these actual histories. Repeated queries can be suppressed by using their already acquired exact replies. Any edge with no positive-compatible continuation returns false. Every positive terminal leaf names one particular $V$, because its paid set contains a complete colour frontier and that frontier determines $V$ within $\mathcal T_C$.

An address deeper than $H$ has reply $\varnothing$ on *every positive candidate*. Delete that query node and retain its $\varnothing$ continuation. The compressed selector uses only its actual acquired history and a public decision-tree template. Deleted replies are not entered as acquired reports; the common candidate prediction merely specifies which public continuation replaces the removed node. Every complete colour frontier from a positive terminal execution lies at depth at most $H$, so its actual requests remain in the compressed tree. A positive follows its former path and pays no more. A negative either reaches a rejected edge or a positive-labelled terminal leaf; the latter would require the actual matching complete colour frontier and hence, by Theorem57.3, would equal that positive. Wrong acceptance is impossible. The resulting finite tree is therefore a genuine depth-$H$ policy correct on all competitors, with no larger positive cost. This proves $D_H\le D_\infty$; the reverse inequality and (57.11) follow from nested policy permissions.

Minima in (57.3) exist when feasible. The competitor set and depth-$H$ alphabet are finite, exact replies are deterministic, and repeats add no information. One may minimize over finite trees without repeated queries on a path; the exhaustive finite address scan already solves the target. Thus (57.11) compares attained integer minima, not an unattained limit of controllers. □

**Theorem 57.5 (pointwise favouritism does not make a uniform static optimum).** Any one uniform policy pays exactly $A$ on at most one positive tree. Conversely for every separately chosen $V_0\in\mathcal P$ there is a uniform policy correct on all of $\mathcal T_C$ whose actual cost on $V_0$ is $A$. At feasible depth,

$$
D_h=A\quad\Longleftrightarrow\quad p=1
\quad\Longleftrightarrow\quad
n=1\ \text{or}\ (n=2\text{ and }ab=0).
\tag{57.12}
$$

Proof. A cost-$A$ accepting run has paid set exactly $\mathcal A(V)$ and therefore every chronological reply is $\alpha$, even if it repeats requests. A source-independent deterministic selector has only one such all-alpha trajectory and return. Two positives attaining $A$ would have the same actual trajectory, the same paid alpha frontier and hence the same tree. This excludes a policy attaining the static optimum on two different positives.

To favour $V_0$, request its public alpha template first, with no acquired record at initialization. On a mismatch continue a finite correct union-frontier scan, using and retaining the replies actually obtained; on completion accept. Every candidate, including $V_0$, still has its addresses paid when requested. Theorem57.3 makes both branches correct against all negatives. On $V_0$ exactly its $A$ addresses are requested. This is a separately parameterized policy, not a controller secretly initialized with the actual source. The cardinality formula (57.6), $\operatorname{Cat}_0=\operatorname{Cat}_1=1$ and $\operatorname{Cat}_{n-1}>1$ for $n\ge3$ give (57.12). □

**Corollary 57.5a (an explicit static/uniform separation).** At $d=3$, $(a,b)=(1,1)$, let $X=X_3=((\beta,\alpha),\beta)$ and $Y=X_4=(X,(\beta,\alpha))$. The two positives $V=(X,Y)$ and $W=(Y,X)$ have exact composition $(A,B)=(3,5)$, with

$$
\mathcal A(V)=\{LLR,RLLR,RRR\},\qquad
\mathcal A(W)=\{LLLR,LRR,RLR\}.
\tag{57.12a}
$$

Each unique static minimum is three, but no uniform policy attains three on both. At every $h\ge4$ the query $LLR$ replies alpha on $V$ and beta on $W$; subsequent actual alpha completion pays respectively three and four. Thus $D_h=4$, against all complete $(3,5)$ competitors, whose possible native heights extend to seven. This witness preserves the distinction between $\forall V\,\exists Q$ and $\exists\pi\,\forall V$ rather than inferring one from the other. The lower bound is Theorem57.5 and the upper procedure is the literal two-leaf diagnostic in Theorem57.10. □

**Definition 57.6 (finite weighted identification on the matched positive family).** A positive-identification decision tree uses only original actual address replies, has no repeated address on a path, and has a terminal label $V\in\mathcal P$ which must be correct when its actual source is positive. It is a public finite diagnostic tree, not an acquired tree identifier or a new task required on negatives. For a query at $u$ its weight on $V$ is

$$
\omega_V(u)=\mathbf1_{r_V(u)\ne\alpha}.
\tag{57.13}
$$

Let $E_h$ be the minimum worst positive sum of these weights. It is sufficient to use the finite union of positive node addresses: elsewhere every positive replies absent. Uniformly constant replies can be removed for identification. For a nonempty candidate set $S$ put $e(S)=0$ when $|S|=1$ and otherwise

$$
e(S)=\min_{u\ \mathrm{splits}\ S}\
\max_{y:S_y\ne\emptyset}
\left(\mathbf1_{y\ne\alpha}+e(S_y)\right),
\quad S_y=\{V\in S:r_V(u)=y\}.
\tag{57.14}
$$

The minimum ranges over allowed addresses with at least two realized replies. This is the ordinary finite decision-tree recurrence with source-dependent path weights. It counts every non-alpha reply, including $\beta$, branch and absence; it is not an alpha-only query budget. At $h\ge H$ the candidates are distinguishable, the recurrence is finite, $E_h=e(\mathcal P)$, and $E_h=E_H=E_\infty$.

**Theorem 57.7 (verified identification-to-acquisition bridge and its threshold).** At every feasible depth,

$$
D_h\le A+E_h.
\tag{57.15}
$$

If $D_h<B$, then $E_h\le D_h-A$. In particular

$$
A+E_h<B\quad\Longrightarrow\quad D_h=A+E_h.
\tag{57.16}
$$

More generally either $D_h\ge B$ or $D_h=A+E_h$. No unconditional identity $D_h=A+E_h$ across the beta-frontier threshold is asserted.

Proof. Run a finite weighted identification tree, recording every actual request and reply. Reject immediately on an edge not realized by any surviving positive. When a leaf names $V$, request every *still unqueried* address of $\mathcal A(V)$ and check for $\alpha$. A mismatch rejects; completion accepts. On a positive all these requests are within $H$, its diagnostic leaf is correct, and the distinct acquired alpha addresses finally total $A$. The other distinct requests are exactly its diagnostic non-alpha addresses. Hence its paid cost is $A$ plus its diagnostic weight. Every actual negative either takes a rejected diagnostic edge, fails the final frontier, or would supply an entire matching frontier of $V$; the last case is impossible by Theorem57.3. This proves (57.15) for an actual causal policy against the whole negative domain.

For the converse restrict an optimal policy with $D_h<B$ to its positive actual runs. Its terminal transcripts contain all alphas and uniquely identify their positive source. Suppress repeats and discard empty positive edges to obtain a finite positive-identification tree. Its path weight at $V$ is exactly the non-alpha term in (57.9), so $E_h\le D_h-A$. If $A+E_h<B$, (57.15) puts the optimum below $B$ and the two inequalities give (57.16). If the optimum is below $B$ without that hypothesis, the same lower inequality and (57.15) still give equality. Identification depth independence follows by deleting universally absent queries deeper than $H$, exactly as in Theorem57.4. □

**Theorem 57.8 (nonrepeated finite universal upper constructions).** Let
$\mathcal F=\bigcup_{V\in\mathcal P}\mathcal A(V)$. At feasible depth,

$$
D_h\le A+E_h\le
\min\{A+p-1,\ |\mathcal F|\}
=\min\left\{A+\operatorname{Cat}_{n-1}\binom na-1,
\left|\bigcup_{V\in\mathcal P}\mathcal A(V)\right|\right\}.
\tag{57.17}
$$

Both stated upper protocols terminate correctly on every negative, with no repeated query calls. The candidate protocol makes at most $A+p$ calls on any competitor and at most $A+p-1$ on a positive. The union protocol makes at most $|\mathcal F|$ calls on any competitor.

Proof. For candidate verification maintain the set of public positives compatible with the entire actual transcript. Choose any remaining candidate by one fixed public order. Request its unqueried alpha endpoints in a fixed order until all are verified or one reply differs from $\alpha$. A mismatch is one paid non-alpha address and removes that candidate; full agreement accepts by Theorem57.3. Previously requested endpoints use their actual retained replies and are not requested again. On a positive its true candidate is never removed, so there are at most $p-1$ mismatch calls. Distinct alpha-returning addresses number at most $A$ on *every* source in $\mathcal T_C$, since its alpha count is exactly $A$. On a negative no candidate can pass; at most $p$ mismatch calls remove them all and cause rejection. This proves all call bounds and the first inequality for $E_h$.

Alternatively request each member of $\mathcal F$ once and test whether any whole candidate alpha frontier has all actual replies $\alpha$. Theorem57.3 gives correctness for tall negatives as well as positives. Each positive returns $\alpha$ at exactly $A$ members of $\mathcal F$, so the diagnostic non-alpha weight is at most $|\mathcal F|-A$. One may identify its positive candidate after this scan and use Theorem57.7, or use the direct membership test. Every response is paid in either version. The public candidate/frontier computation, endpoint-word construction and finite bookkeeping are specified control tasks, with resources distinct from these call counts. □

**Lemma 57.9 (a two-unit weighted obstruction with literal witnesses).** For mixed composition $ab>0$, $n\ge3$, or homogeneous composition $ab=0$, $n\ge4$, every finite positive-identification tree has worst non-alpha weight at least two. Consequently

$$
D_h\ge A+2
\tag{57.18}
$$

at every feasible depth in these ranges.

Proof. First consider six three-leaf macro trees with two occurrences of block $Z$ and one of block $W$, where $Z$ is either $X_d$ or $X_{d+1}$ and $W$ is the other. At either root child their actual subtree multiset is

$$
\{Z,Z,W,(Z,Z),(Z,W),(W,Z)\}.
\tag{57.19}
$$

For any nonempty raw address $u=cv$, if $r_Z(v)\ne\alpha$, its two copies in (57.19) already give a non-alpha reply bucket of size at least two. If $r_Z(v)=\alpha$, then $v$ is nonempty, and deleting its first letter leaves a non-alpha address of $Z$ by (57.5). Among the three pairs in (57.19), two have $Z$ on the side selected by that first letter. They therefore give that same non-alpha reply, again in a bucket of size at least two. The root itself gives six common branch replies. Thus every address has some non-alpha reply realized by at least two different candidates.

For the five homogeneous four-leaf shapes define

$$
\begin{aligned}
S_1&=(((Z,Z),Z),Z),&S_2&=((Z,(Z,Z)),Z),\\
S_3&=((Z,Z),(Z,Z)),&S_4&=(Z,((Z,Z),Z)),\\
S_5&=(Z,(Z,(Z,Z))).&&
\end{aligned}
\tag{57.20}
$$

At either root child the subtree multiset is
$\{Z,Z,(Z,Z),((Z,Z),Z),(Z,(Z,Z))\}$.
The two copies of $Z$ give the same argument when $r_Z(v)\ne\alpha$. When it is alpha, the pair $(Z,Z)$ and one of the two triples have $Z$ on the side selected by the first letter of $v$; both reply at the shortened non-alpha address. The root is again a repeated branch reply. This verifies the same obstruction for all raw addresses, rather than only at macro leaves or a selected positive-height enumeration.

An identification tree with worst weight at most one cannot operate on either core family. Queries which return alpha on every candidate do not shrink that family. At the first other query there is a non-alpha bucket containing at least two candidates. Its query has spent their only non-alpha allowance. From that node all their subsequent replies would have to be alpha, so the deterministic all-alpha continuation could not separate those two distinct candidates into correct leaves. This is a decision-tree contradiction, not a vote about a proposed strategy.

For any larger mixed composition choose two leaves of a majority colour and one of the other colour, and put the six alternatives into one fixed ordered context. Fill all remaining leaves with the remaining prescribed labels. For a larger homogeneous composition similarly put the five four-leaf shapes into a fixed context. Inside the hole the same raw-address obstruction holds. Outside it all candidates have the same reply: a common alpha gives no separation, and any common non-alpha also has a bucket of size at least two. The embedded candidates have the required exact common composition. Thus the lower bound transfers without changing their actual readout port.

Finally a policy costing at most $A+1$ in these ranges would be below $B$ by (57.8). Theorem57.7 would yield an identification tree of weight at most one, contradicting the cores. Since the primary cost is integral, (57.18) follows. In particular static existence of an $A$-set is not a universal $A$ acquisition algorithm. □

**Theorem 57.10 (exact low-macro-leaf regimes, with all-negative-correct implementations).** At every $h\ge H$,

| Exact initial composition | Uniform positive worst paid cost |
| --- | --- |
| $n=1$, or $n=2$ and $ab=0$ | $A$ |
| $n=2$, $a=b=1$; or $n=3$, $ab=0$ | $A+1$ |
| $n=3$, $ab>0$; or $n=4$, $ab=0$ | $A+2$ |

Each equality holds for every $d=3k$, $k\ge1$. The following explicit diagnostic tables followed by the actual alpha-frontier completion of Theorem57.7 attain them. Every omitted reply edge rejects, every repeated request is suppressed, and every final alpha request is actually acquired and checked. Thus none of these implementations classifies merely a positive enumeration.

For a singleton family use no diagnostic queries and check its alpha frontier. For the mixed two-leaf candidates $(X_d,X_{d+1})$ and $(X_{d+1},X_d)$, query $Lz_d$: its replies are respectively $\alpha,\beta$. This identifies them with at most one non-alpha reply.

For three homogeneous macro leaves put $Z=X_t$, where $t=d$ for initial alpha and $t=d+1$ for initial beta. Query $Lz_t$. The right-associated tree $(Z,(Z,Z))$ replies alpha and the left-associated tree $((Z,Z),Z)$ replies beta. Its maximum diagnostic weight is one.

For $(a,b)=(2,1)$ enumerate the six macro trees in this order, with $x=\alpha,y=\beta$ before substitution:

$$
(x,(x,y)),\ (x,(y,x)),\ (y,(x,x)),\
((x,x),y),\ ((x,y),x),\ ((y,x),x).
\tag{57.21}
$$

Their positive indices are $0,1,\ldots,5$. The entire diagnostic is specified by this table; a candidate-set row is the set reaching that node, and a singleton reply is the identified index.

| Reaching indices | Actual query | Reply and continuation |
| --- | --- | --- |
| $0,1,2,3,4,5$ | $z_d$ | $\beta:\{0,1\}$; $\mathsf{br}:\{2,3,4,5\}$ |
| $0,1$ | $Rz_d$ | $\beta:0$; $\mathsf{br}:1$ |
| $2,3,4,5$ | $Lz_{d+1}$ | $\beta:5$; $\alpha:\{2,3,4\}$ |
| $2,3,4$ | $LRz_{d-1}$ | $\alpha:2$; $\beta:3$; $\mathsf{br}:4$ |

The first query spends one non-alpha unit on every positive. In the beta branch only one more query is used. In the branch branch, a beta terminates with the second unit; an alpha keeps indices $2,3,4$ and their final query spends at most the second unit. Thus the worst diagnostic weight is exactly two, with at most three actual diagnostic calls.

For $(a,b)=(1,2)$ enumerate instead

$$
(x,(y,y)),\ (y,(x,y)),\ (y,(y,x)),\
((x,y),y),\ ((y,x),y),\ ((y,y),x).
\tag{57.22}
$$

Use the following complete positive diagnostic, retaining every absent reply as a paid query result.

| Reaching indices | Actual query | Reply and continuation |
| --- | --- | --- |
| $0,1,2,3,4,5$ | $z_d$ | $\beta:0$; $\mathsf{br}:\{1,2,3,4,5\}$ |
| $1,2,3,4,5$ | $RRz_{d-1}$ | $\mathsf{br}:1$; $\beta:2$; $\alpha:\{3,4\}$; $\varnothing:5$ |
| $3,4$ | $Lz_d$ | $\beta:3$; $\mathsf{br}:4$ |

The first query spends one unit. Every non-alpha second reply identifies its source with the second unit, whereas an alpha second reply leaves the pair resolved with one more non-alpha unit. There are at most three diagnostic calls. The longest query in (57.21) has depth $d+1$, and every query in (57.22) has depth at most $d$. They obey the feasible mixed-three cap $H=d+2$.

For four homogeneous macro leaves use (57.20), $Z=X_t$. The table is

| Reaching candidates | Actual query | Reply and continuation |
| --- | --- | --- |
| $S_1,S_2,S_3,S_4,S_5$ | $Lz_t$ | $\mathsf{br}:S_1$; $\beta:\{S_2,S_3\}$; $\alpha:\{S_4,S_5\}$ |
| $S_2,S_3$ | $Rz_t$ | $\alpha:S_2$; $\beta:S_3$ |
| $S_4,S_5$ | $RLz_t$ | $\beta:S_4$; $\alpha:S_5$ |

Its maximum diagnostic weight is two, attained at $S_3$. Its addresses have depth at most $t+1$, below $H=t+2$. The table supplies an ordinary proof of the homogeneous-four upper bound in addition to the independent core lower bound; this regime is not left to positive-only numerical evidence.

Proof of all table entries and minima. Apply (57.5) after the displayed macro prefix. For example $r_{X_d}(z_d)=\alpha$, $r_{X_{d+1}}(z_d)=\beta$, and removing the initial $L$ from $z_d$ leaves weight $d-1$, which yields beta in $X_d$ and branch in $X_{d+1}$. In (57.21), $Lz_{d+1}$ leaves weight $d+1$ in a sole left $X_{d+1}$ but weight $d$ after the two left macro edges in a pair; this yields the stated three-alpha/one-beta split. The query $LRz_{d-1}$ leaves respectively weight $d+1$ in the sole left $X_{d+1}$, weight $d-1$ in a right $X_d$ of the left pair, and weight $d-1$ in its right $X_{d+1}$; these replies are alpha, beta, branch. In (57.22), $RRz_{d-1}$ reads within a right pair at weight $d-1$, giving branch for its $X_{d+1}$ and beta for its $X_d$; within a sole right block its remaining weight is $d+1$, giving alpha for $X_{d+1}$ and absent for $X_d$. The other entries follow by the same literal one- or two-edge calculation, including $d=3$ where $z_{d-1}=R$.

Alpha completion makes the paid positive cost $A$ plus the diagnostic non-alpha weight, rather than $A$ plus the number of diagnostic calls. Its already queried alpha endpoints are retained and not bought again. A singleton cannot improve on $A$. Theorem57.5 gives the $A+1$ lower bound for every nonsingleton; Lemma57.9 gives the $A+2$ lower bound in the final row. All the upper costs are below $B$, since $B-A\ge n$, so the weighted bridge also matches these minima. The final actual frontier check proves negative correctness, even for replies compatible with a diagnostic positive leaf. □

**Definition 57.11 (finite verification scope and unclosed targets).** The general assertions above have ordinary proofs. Finite diagnostics independently used literal tree substitution, endpoint recursion, and inverse parsing rather than treating positive votes or an identification table as a hypothesis. They checked: the block reply formula at $t=3,\ldots,14$ for every word of length at most $t+1$; every exact low-regime diagnostic/completion construction at $d=3,6,9,12,15$; and the sensitive exchanges for every composition with macro $n=1,\ldots,4$ at $d=3$. A separate exhaustive finite decision-tree recurrence on the union of positive nodes was evaluated at $d=3,6,9$, all compositions with $n=1,\ldots,4$. It returned the respective diagnostic weights $0$, $1$, and $2$ for the regimes asserted in Theorem57.10; for mixed four-leaf compositions it returned $3$ in those tested depths. These latter finite values are not a formula for all depths or larger families.

Every complete same-composition competitor was also enumerated at $d=3$ for initial compositions $(1,0),(0,1),(2,0),(1,1),(0,2),(3,0)$. These domains have respectively $6,140,630,24024,1021020,120120$ trees, using the Catalan shape count and every permitted label placement. They include all their tall negatives, with no height filter; the maximum native competitor heights are respectively $2,4,5,7,9,8$. The construction's return was compared with independent inverse parsing on every such tree. Its actual calls were nonrepeated and within the asserted cap. Both complete-colour reconstruction tests were also checked on these entire domains. The successful checks cover 55 positive parameter cases and 160 positive runs, 5502 sensitive swaps, and 1165940 complete competitors, including 1130084 negatives taller than the corresponding $H$. The decision-tree recurrence covers 42 parameter cases. A separate execution of its resulting diagnostics followed by actual alpha completion checked 306 positive runs and the identity paid cost $=A+$ non-alpha diagnostic weight. It also checked 804168 actual absent replies at depth $H+1$ across those cases; they support the finite implementation of the compression argument without serving as its universal proof. All of these completed bounded checks returned exit zero. These bounded checks do not replace the all-negative proofs of Theorems57.3,57.7 and57.10.

The exact uniform minimum for mixed $n\ge4$ or homogeneous $n\ge5$ remains open here. What is established for those ranges is (57.10)–(57.11), the two-unit lower bound, the finite universal upper bound (57.17), and the threshold-qualified weighted reduction (57.16). Computing $E_h$ in larger families, or determining when a strategy acquiring the beta frontier beats the alpha-completion route, is a separate remaining problem. No larger closed formula follows from the low-order tables or finite recurrence values. The selected source is finite, deterministic and exact; this chapter gives no randomized, runtime, memory, finite-bit, address-encoding, physical-traversal, original global `Strategy`, physical realization or full broader-goal result.

**Definition 57.12 (sources, mathematical standing and verification boundary).** The matched ordinary suppliers are the `ActualImageAddressCertificate` Blueprint and its `result`, `rigidity` and structural swap arguments, the original `ActualTreeReadoutAcquisition` endpoint/policy/paid definitions, and `ActualLeafHistoryRigidity`'s literal actual-address geometry. Their filenames identify fallible mathematical sources, not current kernel evidence. All the complete-colour, actual-history, depth-independence, weighted-threshold and low-regime claims in this chapter are ordinary mathematical derivations, with the independent finite implementation checks specified in Definition57.11. No Lean was written or compiled, no ingestion or coverage state was produced, and no independent review is claimed.

Classical certificate complexity and deterministic decision trees, the Catalan enumeration of ordered binary trees, tries, finite weighted decision-tree recursion and version-space elimination are reused tools. The background references already accompanying the certificate supplier are Nisan, *CREW PRAMs and Decision Trees* (1991), and Buhrman–de Wolf, *Complexity Measures and Decision Tree Complexity: A Survey* (2002). Those general tools do not by themselves supply the literal source-specific tables, the exact competing-tree domain, actual causal acquisition, or the paid-cost/colour-frontier bridge. The results here are repo-derived deductions under the explicit matched contract. There is no exhaustive literature search, novelty or priority claim, and no inference from a search miss. The chapter does not grant an old-source archive, a true candidate index, free actual frontiers, a reset, a new readout or a physical source action to the controller.

## 57.99 追加锚（本行以下为增补区）

## 58. Native whole-rho renewal: source labels, retained spectral state and finite-clock fidelity

This chapter consumes the same original source and the full interaction realization of §55. It addresses a joint question left by a static spectral description: what changes when an actually accepted native substitution creates new occurrences, what information determines that change, and when can the resulting finite amplitude trajectory preserve a common full spectral state? The positive result is uniform over the original finite sources and their actual irregular domains, on a supplied finite clock. The source/action and amplitude contracts remain distinct.

**Definition 58.1 (the joint renewal contract and its task).** Retain Definition55.1 in full: one immutable INITIAL tree $t$, its original initialization and actual history, the root $o$, actual ordered addresses, accepted index $j$, current source $s=\rho^jt$ and domain $D=\operatorname{Pos}(s)$. No source is replaced, unlabelled or identified with another source. Only whole-rho source actions are considered here. An accepted command installs the literal $\rho s$; an original refusal keeps $s,j,D$ unchanged and supplies no candidate Read. Every actual original Read, command identity, acceptance/refusal and Stop is retained with its original port and charge. A command is not evidence of its execution. Under Process44 the numerical ports are exactly its declared functions; under a fixed-$H$ TM30/57 interface its original whole-candidate guard and literal Clifford Read remain in force. Statements about arbitrarily large $j$ concern uncapped finite prefixes or separately legal capped prefixes. They do not increase a fixed cap, continue a stopped execution or create an event after an infinite prefix.

Keep precisely Definition55.2's counting norm, unit parent–child seams, global-depth potential $\phi(p)=2^{-|p|}$, constants $a,g>0$, common operator $\mathsf H=aL-gM_\phi$ and Dirichlet compressions $\mathsf H_D=I_D^*\mathsf H I_D$. In particular a leaf retains both missing-child Dirichlet terms; its diagonal is $3a-g2^{-|p|}$ off the root, and the root diagonal is $2a-g$. The potential does not restart at a new subtree root. The heat law, field exterior values and normalized amplitude law retain their different meanings in §55.

Supply, in addition, the following amplitude/evolution/clock/preparation contract on this same source/history. At an accepted renewal $D\subset D'$, the transfer preserves every old same-address amplitude and its full counting norm. Between events it obeys $i\partial_\tau f=\mathsf H_Df$ on the currently installed domain. Reads and refusals introduce no amplitude kick under this additional contract. There are finitely many supplied nonnegative clock intervals of total length $S\le T<\infty$, including all declared evolution before Stop; their sum is not inferred from event counts. The actual amplitude trajectory is asserted only on $[0,S]$. Renewal itself takes zero duration in this idealization. A source apparatus implementing old-amplitude preservation, a coherent state, this Hamiltonian, nondisturbing source Reads and zero-duration transfer is not supplied by the original native menu. Its construction, preparation, execution duration and prices remain obligations. A nonzero-duration or disturbing implementation needs its own comparison law.

The interaction task includes the entire complex amplitude in $\ell^2(\mathcal P)$, its full spectral coefficients and relative phases, and any expressly supplied bounded response $C:\ell^2(\mathcal P)\to Y$ with $\|C\|\le1$ or effect $0\le E\le I$. These are mathematical target functions, never renamed original native Read ports. A prepared initial amplitude is a separately supplied state, not a new source-dependent initialization of the original controller. Knowledge of an operator is not preparation or knowledge of its actual state.

**Theorem 58.2 (forced transfer, exact native frontier defect and full modal update).** Let

$$
\mathcal B(s)=\{p\in D:s|_p=\beta\},\qquad
D'=D\sqcup\{pL,pR:p\in\mathcal B(s)\}.
\tag{58.1}
$$

The domain identity is TM22.2's actual-source identity. The transfer required by Definition58.1 is necessarily zero extension $J:\ell^2(D)\to\ell^2(D')$, even if no linearity of the proposed transfer was assumed. With $P_{\mathcal B}$ the projection onto the old beta-leaf coordinates, the generator defect is exactly

$$
\begin{aligned}
\Delta_s&=\mathsf H_{D'}J-J\mathsf H_D,\\
\Delta_sf&=-a\sum_{p\in\mathcal B(s)}f(p)(e_{pL}+e_{pR}),\\
\Delta_s^*\Delta_s&=2a^2P_{\mathcal B},\qquad
\|\Delta_sf\|^2=2a^2\sum_{p\in\mathcal B(s)}|f(p)|^2.
\end{aligned}
\tag{58.2}
$$

Thus every nonzero singular value is $a\sqrt2$, with complex multiplicity $|\mathcal B(s)|$. At the switch the two new amplitudes at each $p$ are zero, and their initial derivatives are both $iaf(p)$. Their exact prediction consumes the actual beta-leaf positions and the old amplitudes at those positions, rather than just a leaf count, kinetic spectrum or root amplitude.

For a complete orthonormal finite eigenbasis $\psi_\mu$ of $\mathsf H_D$, with energies $\lambda_\mu$, and a complete orthonormal basis $\chi_\nu$ of $\mathsf H_{D'}$, with energies $\lambda'_\nu$, set

$$
\begin{aligned}
\Gamma_{\nu\mu}&=\langle\chi_\nu,J\psi_\mu\rangle,\qquad
\Gamma^*\Gamma=I,\\
c'_\nu&=\sum_\mu\Gamma_{\nu\mu}e^{-i\theta\lambda_\mu}c_\mu,\\
(\lambda'_\nu-\lambda_\mu)\Gamma_{\nu\mu}
&=-a\sum_{p\in\mathcal B(s)}\psi_\mu(p)
 \bigl(\overline{\chi_\nu(pL)}+\overline{\chi_\nu(pR)}\bigr).
\end{aligned}
\tag{58.3}
$$

Here $\theta$ is the supplied old-domain evolution interval and $c_\mu$ are the actual retained old modal coefficients, including phases. This gives the complete next state, including all new exceptional and root-invisible directions. No finite mode is discarded by a cancellation in a scalar resolvent. On the common realization the full state is the channel vector $U(c,(v_p))$ and the complete spectral projection-valued account (55.18a), retaining channel sequences and their relative phases, not an assumed complete basis of square-summable eigenvectors in the essential band. Only the positive fidelity theorem restricts that complete state to a subescape subspace. Degenerate bases may be changed unitarily; the corresponding coefficient change leaves the actual state and this update invariant.

Proof. If $F(f)|_D=f$ and $\|F(f)\|=\|f\|$, orthogonality of old and new coordinates gives $\|F(f)|_{D'\setminus D}\|^2=0$. Hence $F(f)=Jf$ for every $f$. On old coordinates the principal block of $\mathsf H_{D'}$ is exactly $\mathsf H_D$: labels do not alter its diagonal, all old seams persist, and global depths and missing-child terms are inherited. On a new child of an old beta leaf the only nonzero old input is the seam $-af(p)$. TM22.2 makes these new child pairs disjoint, proving (58.2). Multiplying by $-i$ gives the new-child derivative. Taking inner products of the defect equation with every $\chi_\nu$ proves the last line of (58.3); completeness and $J^*J=I$ give $\Gamma^*\Gamma=I$. Expansion of the old evolution and then of $Jf$ gives the coefficient update. Full finite spectral bases exist by self-adjointness; §55.5 supplies their boundary reconstruction, internal-kernel compatibility and full normalization, including exceptional energies. □

The rank $|\mathcal B(s)|$ of the newly born derivative map is a classical linear-rank consequence of (58.2). It counts independent complex amplitude coordinates in this particular task. It is not a finite-bit memory bound, a physical storage formula or an acquisition price. For a tolerance $\eta\ge0$, the exact one-step condition is $\sum_{p\in\mathcal B(s)}|f(p)|^2\le\eta^2/(2a^2)$. Zero instantaneous frontier mass does not imply permanent fidelity: later old-domain evolution can reach the frontier. Complete future prediction uses the retained full state and the time-ordered generators, as in (58.3).

**Proposition 58.3 (scope of the all-state obstruction).** Whenever $\mathcal B(s)\ne\varnothing$, exact intertwining
$e^{-i\tau\mathsf H_{D'}}J=Je^{-i\tau\mathsf H_D}$ for every $\tau$ is impossible. Moreover put $M=6a+g$. For every such $s$ and $0<\tau\le a/(4M^2)$,

$$
\bigl\|e^{-i\tau\mathsf H_{D'}}J-Je^{-i\tau\mathsf H_D}\bigr\|
\ge\frac{a\tau}{\sqrt2}.
\tag{58.4}
$$

After at least one accepted whole-rho substitution every nonempty original source has a beta leaf. Therefore this all-state operator obstruction persists uniformly at arbitrarily advanced separately legal versions. The operator comparison concerns an actually accepted next renewal or its separately legal source-indexed mathematical pair; a refusal leaves the installed operator unchanged. It does not assert failure for every particular state or for the subescape finite-clock task below.

Proof. Differentiation at zero would give $\Delta_s=0$, contrary to (58.2). The first-order term has norm $a\sqrt2\tau$. The two exponential remainders together have norm at most $M^2\tau^2e^{M\tau}$. Since $M\ge6a$ and $M\tau\le1/24$, $e^{M\tau}<2$ and the remainder is at most $a\tau/2$. This is less than $a\tau/\sqrt2$, yielding (58.4). Finally the exact source composition update is $(A,B)\mapsto(B,A+B)$, so the new beta count is the old positive leaf count. This uses the original source substitution, not an amplitude sensor. □

**Proposition 58.4 (a native source distinction consumed by the next response).** In the uncapped Process44 numerical contract take the two actual INITIAL sources

$$
u=\langle\langle\alpha,\alpha\rangle,\langle\beta,\beta\rangle\rangle,
\qquad
v=\langle\langle\alpha,\beta\rangle,\langle\alpha,\beta\rangle\rangle.
\tag{58.5}
$$

Their old seven-site domains and the entire old addressed operator $\mathsf H_D$ coincide. Both have original $\eta=((2,2),0)$, so Process44.7 gives identical histories for every allowed numerical adaptive protocol with common initialization and matched prepared contexts. In particular the actual finite word

$$
\operatorname{Read}_\eta[((2,2),0)];\quad
\rho;\quad\operatorname{Read}_\eta[((2,4),0)];\quad
\operatorname{Stop}
\tag{58.6}
$$

is common. Its two installed domains differ, because the beta frontiers are respectively $\{RL,RR\}$ and $\{LR,RR\}$. At the supplied values $a=1,g=16,z=-16$, write
$G_o(D;z)=\langle e_o,(\mathsf H_D-zI)^{-1}e_o\rangle$. Then

$$
\begin{aligned}
G_o(D(u);-16)=G_o(D(v);-16)&=163/296,\\
G_o(D(\rho u);-16)&=448087/813700,\\
G_o(D(\rho v);-16)&=41237/74884,\\
G_o(D(\rho u);-16)-G_o(D(\rho v);-16)&=1/7616638850.
\end{aligned}
\tag{58.7}
$$

Thus the full old operator and its complete spectral catalogue, together with these genuine numerical records, do not determine this next mathematical response. This does not equate the sources in the wider authenticated-address interface or in a different Clifford port.

Proof. The original cross-product leaf evaluation vanishes on both trees: each root multiplies two zero or two equal-axis child values. The actual compositions agree, and $c\rho=Mc$, $q\rho=Rq$ give both replies in (58.6). Process44.7 already owns the adaptive-history statement; no counterfactual execution is inferred from it. The old shape is the same complete two-level tree, so (55.4) gives the identical addressed matrix for every supplied $a,g$.

At $z=-16$ the resolvent matrix diagonal at depths $0,1,2,3$ is respectively $2,11,15,17$. In the old domain each depth-one Schur pivot is $11-2/15=163/15$, giving $G_o=(2-30/163)^{-1}=163/296$. On a beta depth-two leaf actually split by $\rho$, its pivot becomes $15-2/17=253/17$. The depth-one pivots for $\rho u$ are $163/15$ and $2749/253$, while those for $\rho v$ are both $41237/3795$. Taking the root inverse gives precisely (58.7). These are applications of §55.5's existing elimination on the literal renewed trees, not a new Schur theorem. The uniform lower bound $\mathsf H_D\ge(3-2\sqrt2-16)I>-16I$ makes every inverse legitimate. The displayed difference is also obtained by full rational matrix elimination.

If a new scalar port for this response were expressly authorized with jointly adversarial absolute error $\varepsilon_z$, this one response separates the pair exactly when $2\varepsilon_z<1/7616638850$. At equality the two closed report intervals touch. This is only the distinguishability condition for that added port; it supplies neither that port nor its precision, cost or execution. Original $\operatorname{Read}_\eta$ has acquired neither number in (58.7). □

**Proposition 58.5 (a retained hidden phase becomes interaction-visible on one source).** Use the single INITIAL $t=\langle\beta,\alpha\rangle$, its old domain $D=(o,L,R)$ and the actually renewed domain $D'=(o,L,R,LL,LR)$. With $a=1,g=16$ the two expressly prepared unit states

$$
h=e_L-e_R,\qquad f_\pm=(e_o\pm h)/\sqrt3
\tag{58.8}
$$

have energy $-8$, identical energy weights in the complete old spectral decomposition, and identical old root-amplitude functions for every supplied clock value. They are different relative-phase states. Under the transfer and evolution of Definition58.1, their renewed root probabilities differ; their difference has the expansion

$$
\begin{aligned}
\langle e_o,e^{-i\tau\mathsf H_{D'}}Jf_+\rangle
-\langle e_o,e^{-i\tau\mathsf H_{D'}}Jf_-\rangle
&=-\frac{2i\tau^3}{3\sqrt3}+O(\tau^4),\\
\left|\langle e_o,e^{-i\tau\mathsf H_{D'}}Jf_+\rangle\right|^2
-\left|\langle e_o,e^{-i\tau\mathsf H_{D'}}Jf_-\rangle\right|^2
&=-\frac{31}{9}\tau^4+O(\tau^6).
\end{aligned}
\tag{58.9}
$$

At $\tau=1/100$ this probability difference is strictly negative. In the original Process44 port both preparations are attached to the same actual source word
$\operatorname{Read}_\eta[((1,1),k)];\rho;\operatorname{Read}_\eta[((1,2),a_{\rm axis})];\operatorname{Stop}$, with $k=b_{\rm axis}\times a_{\rm axis}$ and $Ra_{\rm axis}=b_{\rm axis}$, $Rk=a_{\rm axis}$. This port does not observe either amplitude state. For a fixed-cap Clifford history one instead retains exactly §55.6's Read/accept/Read/reject/Read/Stop, with $H=3$; its refused second candidate is not installed. A positive supplied interval on $D'$ may be assigned before the next event or Stop. No effect measurement is thereby inserted into either native word.

Proof. The old matrix is
$\left(\begin{smallmatrix}-14&-1&-1\\-1&-5&0\\-1&0&-5\end{smallmatrix}\right)$.
Thus $\mathsf H_Dh=-5h$ and the hidden span is orthogonal to the root's invariant symmetric span. The two states have identical visible coefficients and opposite hidden coefficients; the hidden coefficient's modulus is unchanged. Their old root responses and spectral energy weights therefore coincide. Their root coefficients have the same nonzero sign, so they are not global-phase copies. Direct calculation gives $(-14-10)/3=-8$ for both energies.

The renewed matrix is exactly (55.22) with diagonal $(-14,-5,-5,-1,-1)$, including all inherited exterior seams and the common potential. Direct powers of this full matrix give

$$
\langle e_o,\mathsf H_{D'}^nJh\rangle
=(0,0,0,-2,50,-880,13680)\quad(0\le n\le6).
\tag{58.10}
$$

The classical Taylor/Krylov criterion in Causal Response13.3.2 and13.5.2 applies with generator $-i\mathsf H_{D'}$, input $Jh$ and output $\langle e_o,\cdot\rangle$. Substitution gives the first line of (58.9). Write $A_o=\langle e_o,e^{-i\tau\mathsf H_{D'}}e_o\rangle$ and $A_h=\langle e_o,e^{-i\tau\mathsf H_{D'}}Jh\rangle$. The probability difference is $\frac43\operatorname{Re}(A_o\overline{A_h})$. Here $A_o=1+14i\tau+O(\tau^2)$ and $A_h=-i\tau^3/3+25\tau^4/12+O(\tau^5)$, which gives $-31/9$. Real matrices and real initial vectors make each probability an even function of $\tau$, giving the stated remainder order.

There is a finite exact certificate away from zero. Truncate each normalized amplitude exponential at order eight at $\tau=1/100$, and let $d_8$ be the difference of the two squared truncated root amplitudes. Fraction arithmetic gives

$$
 d_8=-\frac{20971415346759163700136246832031}
 {609638400000000000000000000000000000000},\qquad
 \left|d(1/100)-d_8\right|
 <\frac{2357947691}{59062500000000000000}.
\tag{58.11}
$$

Indeed $\|\mathsf H_{D'}\|\le22$, so each amplitude remainder is at most $r_8=2(22/100)^9/9!$, using $e^{22/100}<2$. An exact root amplitude has modulus at most one; its truncated counterpart has modulus at most $1+r_8$. The two squared-modulus errors together are at most $4r_8+2r_8^2<6r_8$, which is the bound in (58.11). The upper endpoint $d_8+6r_8$ is negative. In decimal notation the certified interval lies between $-3.444\cdot10^{-8}$ and $-3.435\cdot10^{-8}$; the rational inequalities, not rounding, establish separation.

This example shows that the old root-autonomous hidden subspace need not remain hidden under the actual asymmetric renewal. It does not refute a complete retained state: (58.3) uses the distinguishing signed coefficient. A spectral catalogue or even all spectral energy weights lacks that relative phase. The root effect here requires a separately supplied preparation/effect/clock contract and is not an acquired original Read. □

**Theorem 58.6 (uniform localization of the complete common subescape space).** Put

$$
\epsilon_*=a(3-2\sqrt2),\quad c<\epsilon_*,\quad
Q_c=\mathbf1_{(-\infty,c]}(\mathsf H),\quad
 d=\epsilon_*-c,\quad b=(6a+\epsilon_*)/2,\quad
 r=(6a-\epsilon_*)/2,\quad q=r/(b-c)<1.
\tag{58.12}
$$

This is the full spectral projection from (55.18a), including every contrast channel and any coincident or exceptional eigenvalue. For every integer $R\ge0$ and $0\le s\le R$,

$$
\|(I-P_{B_R})Q_c\|
\le\min\left\{1,\frac gd\left(q^{R-s+1}+2^{-s-1}\right)\right\}.
\tag{58.13}
$$

In particular, with $s=\lfloor R/2\rfloor$, denote the displayed right side by $\ell_R$. Then $\ell_R\to0$. No cutoff-gap assumption is needed for this common projection, even if $c$ itself is an eigenvalue. An empty projection has no unit state to prepare; for $g>3a/4$, choosing $m\le c<\epsilon_*$ guarantees nonemptiness by §55.3–55.4. At $g=16a,c=-a$ this includes, in particular, both depth-one hidden channel ground states of §55.6, since their energies are at most $-a\sqrt3<-a$.

Proof. Write $A=aL$, let $\mathcal K=\operatorname{ran}Q_c$, let $X:\mathcal K\to\ell^2(\mathcal P)$ be inclusion, and put $C=\mathsf H|_{\mathcal K}$. The existing gap and norm bounds give $\epsilon_*I\le A\le6aI$, $\|b-A\|\le r$, $C\le cI$ and $\|(b-C)^{-1}\|\le1/(b-c)$. From the actual potential equation,

$$
 AX-XC=gM_\phi X,\qquad
 X=(b-A)X(b-C)^{-1}+gM_\phi X(b-C)^{-1}.
\tag{58.14}
$$

The iteration is norm contracting by $q<1$; hence its unique bounded solution is the convergent operator series

$$
 X=g\sum_{n\ge0}(b-A)^nM_\phi X(b-C)^{-n-1}.
\tag{58.15}
$$

This is the ordinary Neumann-series method applied to this two-operator equation, not an assumed resolvent decay theorem. Split $M_\phi=P_{B_s}M_\phi+(I-P_{B_s})M_\phi$. The tail has norm $2^{-s-1}$. The first factor has range in $B_s$, and each multiplication by $b-A$ enlarges support by at most one actual seam. Therefore its terms with $n\le R-s$ vanish after multiplication by $I-P_{B_R}$. Summing the remaining geometric bounds yields
$gq^{R-s+1}/(b-c-r)=gq^{R-s+1}/d$; summing the potential-tail terms yields $g2^{-s-1}/d$. Since $X$ is isometric and $Q_c=XX^*$, this proves (58.13). The floor choice makes both terms tend to zero. The proof makes no root-visible or radial reduction and uses no finite-domain eigenvalue endpoint convention. □

**Theorem 58.7 (source-composed finite-clock fidelity).** At an actually reached version $j_0$ of any original finite source, put $R=\lfloor j_0/2\rfloor$ and suppose $\ell_R<1$. Supply a common unit state $f\in\operatorname{ran}Q_c$ and expressly prepare on the actual domain $D_0=D_{j_0}(t)$ the unit state

$$
 f_0=I_{D_0}^*f/\|P_{D_0}f\|.
\tag{58.16}
$$

Continue through any finite legal whole-rho history and any supplied clock partition as in Definition58.1, with total duration $S\le T$. Let $u(\tau)$ be its actual amplitude embedded by the same addresses in $\ell^2(\mathcal P)$. Then

$$
\sup_{0\le\tau\le S}\|u(\tau)-e^{-i\tau\mathsf H}f\|
\le(\sqrt2+2MT)\ell_R,\qquad M=6a+g.
\tag{58.17}
$$

The bound is uniform over all those original sources, actual irregular domains, finite renewal counts and partitions. Both amplitudes have full norm one. It bounds every supplied contraction response by the same number, and every supplied effect probability by twice that number. It does not require projecting the renewed state into a finite spectral window at each switch; such projections would introduce another state law.

Proof. TM23.2 and (55.2) give $B_R\subset D_0$, and actual whole-rho persistence gives $D_0\subset D(\tau)$ throughout. Balls are only contained comparison sets; every generator remains the compression on its actual $D(\tau)$. If $\alpha=\|(I-P_{D_0})f\|\le\ell_R$, then

$$
\left\|\frac{P_{D_0}f}{\|P_{D_0}f\|}-f\right\|^2
 =2(1-\sqrt{1-\alpha^2})\le2\alpha^2.
\tag{58.18}
$$

Thus (58.16) exists and the initial norm error is at most $\sqrt2\ell_R$.

On the common Hilbert space set $A_D=P_D\mathsf H P_D$. It is bounded self-adjoint, has norm at most $M$, and its unitary flow restricted to the support $D$ is exactly the finite flow. Forced zero extension makes $u$ continuous in this space at every renewal. Put $v(\tau)=e^{-i\tau\mathsf H}f$. The spectral projection commutes with the common flow and generator, so both $v$ and $\mathsf Hv$ lie in $\operatorname{ran}Q_c$. Theorem58.6 gives, on every installed domain,

$$
\begin{aligned}
\|(A_D-\mathsf H)v\|
&\le\|P_D\mathsf H(P_D-I)v\|+\|(P_D-I)\mathsf Hv\|\\
&\le M\ell_R+\ell_R\|\mathsf Hv\|\le2M\ell_R.
\end{aligned}
\tag{58.19}
$$

Apply the unitary Duhamel bound of Causal Response13.6.2 on each supplied interval, or concatenate those finite propagators in time order. Unitarity carries an earlier error without amplification, and continuity at the switches adds no jump error. Integration of (58.19) over the total interval and (58.18) proves (58.17). This is not a sum of the all-state defects in (58.2), which would grow with the number of switches. Finally $\|C(u-v)\|\le\|u-v\|$, and for unit states $|\langle u,Eu\rangle-\langle v,Ev\rangle|\le2\|u-v\|$. □

Consequently, for every supplied finite $T$ and positive accuracy $\varepsilon$, a finite radius $R$ with $(\sqrt2+2MT)\ell_R<\varepsilon$ suffices, if the source actually reaches an accepted index $j_0\ge2R$ and the preparation in (58.16) is supplied. For a concrete finite instance, take $a=1,g=16,c=-1,T=1$. Then $d>1$, $q<5/7$ because $3-2\sqrt2>1/6$, and $\sqrt2+2MT<46$. At $R=66$,

$$
 (\sqrt2+2MT)\ell_{66}
 <736\left((5/7)^{34}+2^{-34}\right)<1/100.
\tag{58.17a}
$$

The final inequality is an exact rational inequality. Thus an actually reached $j_0\ge132$ and the expressly supplied preparation suffice for norm error below $1/100$ throughout this clock window, including the hidden channel ground directions. This is an explicit sufficient relation among accepted depth, full-state accuracy and clock length. It supplies neither the number or prices of original Reads needed to authenticate that version nor a physical preparation method. A fixed-$H$ run unable to reach that index gets no additional acceptance permission from the inequality.

**Corollary 58.8 (actually finite spectral preparation and explicit error contracts).** Let $W=[v_-,v_+]\subset(-\infty,c]$ be a compact interval with endpoints in common resolvent gaps; keep $D_0,j_0,R,S,T$ as in Theorem58.7. For any unit finite state $u_0\in\operatorname{ran}Q_{D_0}(W)$, zero extended, put
$\delta_{D_0}=\|Q_{D_0}(W)-Q(W)\|$, and suppose $\delta_{D_0}<1$. Then $f=Q(W)u_0/\|Q(W)u_0\|$ is a common unit state and the same actual finite continuation satisfies

$$
 \sup_{0\le\tau\le S}\|u(\tau)-e^{-i\tau\mathsf H}f\|
 \le\sqrt2\delta_{D_0}+2MT\ell_R.
\tag{58.20}
$$

Here $\delta_{D_0}\to0$ along the actual source family of §55.5, including varying original sources with accepted indices tending to infinity. In a further expressly supplied precision model, suppose preparation has unit-state norm error at most $\eta_0$, actual between-event generators are self-adjoint on the same authenticated domains with integrated operator error at most $\eta_H$, actual isometric transfers have errors at most $\eta_k$ relative to $J$ on the states transferred, and clock-interval discrepancies sum to at most $\eta_\tau$. Then the norm budgets in (58.17) or (58.20) gain at most

$$
 \eta_0+\eta_H+\sum_k\eta_k+M\eta_\tau.
\tag{58.21}
$$

The operator-error integral is over the actual intervals; the reference partition in (58.17) or (58.20) has total length at most $T$. This further model explicitly relaxes the ideal amplitude contract. Literal native source actions, authentic domains and original error models are unchanged.

Proof. The projection distance bounds $\|(I-Q(W))u_0\|$ by $\delta_{D_0}$, and the normalization identity (58.18) bounds $\|u_0-f\|$ by $\sqrt2\delta_{D_0}$. Then (58.19) and the same Duhamel argument apply. The projection convergence is the already proved full-state, all-multiplicity theorem55.5, not a new eigenbasis-acquisition theorem. For the additional model, unitarity and isometric transfers propagate errors without norm amplification. Duhamel bounds each generator discrepancy by its operator-error integral, telescoping the finite transfers gives their actual error sum, and $\|e^{-isA_D}-e^{-itA_D}\|\le M|s-t|$ bounds interval-clock discrepancies. If a separately authorized contraction-response readout has error at most $\eta_{\rm read}$ in $Y$, its reported error gains that amount; an effect-probability readout with scalar error at most $\eta_{\rm read}$ has reported error at most twice the state-norm budget plus $\eta_{\rm read}$. These are additional response-error contracts, never the original native Read error model. These estimates require no independent errors, statistical averaging or resampling. □

Exact real source execution, exact amplitudes and exact operator arithmetic in these theorems are mathematical contracts. Finite-bit control descriptions, an implemented actuator, clock calibration, normalization/preparation and readout need actual supplied bounds before (58.21) has numerical content. A wrong source/version or beta mask is not automatically a small operator error. An original Process44 reply error or the $\mathcal D_2$ Read error is not $\eta_0$, $\eta_H$ or a coherent transfer error. Even at a known gap, formal modal coefficients are not an acquired archive or a prepared field state.

**Corollary 58.9 (exact renewal energy and uniform ground-ray fidelity).** Under Definition58.1, every finite trajectory has constant common energy expectation, through all between-event evolution and all accepted renewals:

$$
 J^*\mathsf H_{D'}J=\mathsf H_D,\qquad
 \langle u(\tau),\mathsf Hu(\tau)\rangle
 =\langle u(0),\mathsf Hu(0)\rangle=:E_0.
\tag{58.21a}
$$

Assume $m<\epsilon_*$ as in §55.4, let $w$ be its positive unit ground state, and let
$\gamma=\inf\sigma(\mathsf H|_{w^\perp})-m>0$ be the common ground-state spectral gap. Then every such trajectory, on every finite supplied clock interval $[0,S]$, satisfies

$$
 \sup_{0\le\tau\le S}\ \inf_{|z|=1}\|u(\tau)-zw\|
 \le\sqrt{\frac{2(E_0-m)}\gamma}.
\tag{58.21b}
$$

Every supplied effect probability therefore differs from that of $w$ by at most $2\sqrt{2(E_0-m)/\gamma}$, independently of $S$ and of the finite number of renewals. In particular, expressly preparing the actual positive finite ground state on $D_{j_0}(t)$ gives $E_0=m_{j_0}(t)$; (55.13) makes this ray/effect bound tend to zero uniformly over all original sources as their separately legal accepted indices tend to infinity. This is an all-finite-clock bound for near-ground rays, not for all subescape states, all states or their full phases.

Proof. The first equality is exactly the old principal-block equality used in Theorem58.2, also the compression energy identity of (55.4). Each unitary finite flow preserves its own energy expectation; zero extension at renewal preserves that expectation by the displayed congruence. Their finite composition proves (58.21a). The common ground eigenvalue is simple and isolated below the essential threshold by §55.3–55.4, so $\gamma>0$. The spectral inequality
$\mathsf H-mI\ge\gamma(I-|w\rangle\langle w|)$ then gives
$1-|\langle w,u(\tau)\rangle|^2\le(E_0-m)/\gamma$.
Choosing the aligning phase and using
$2(1-|\langle w,u\rangle|)\le2(1-|\langle w,u\rangle|^2)$ proves (58.21b). Effects do not depend on the aligning global phase, and the unit-state effect inequality used in Theorem58.7 gives the stated probability bound. The finite-ground specialization uses §55.4's already proved minimum-value comparison, not another source-learning or ground-state acquisition assertion. □

The norm-preserving and energy-preserving mathematical transfer does not assign zero physical work, preparation cost or implementation duration. In the further precision model of Corollary58.8 energy need not be exactly conserved; this clock-independent conclusion requires either the ideal contract or an additional uniform accumulated energy-error bound. The theorem quantifies over finite histories of arbitrary finite duration, without an event after an infinite prefix or after Stop.

**Proposition 58.10 (the clock restriction is material for the full-phase task).** For $g>3a/4$, fix one original finite source. Let $m_j$ be its finite ground energies and $w_j$ the zero-extended positive normalized finite ground vectors. Let $m,w$ be the common ground pair. Then

$$
 m_j>m,\qquad m_j\downarrow m,\qquad w_j\to w,
\qquad \tau_j=\frac\pi{m_j-m}<\infty,
\qquad
 \|e^{-i\tau_jm_j}w_j-e^{-i\tau_jm}w\|\longrightarrow2.
\tag{58.22}
$$

These are separate finite histories with a supplied holding interval before Stop on their actually reached domains; no renewals during that interval are required. Consequently a uniform unbounded-clock full-amplitude guarantee cannot replace (58.17), even though initial states and energies converge. This discriminator alone does not refute gauge-invariant probability fidelity; Corollary58.9 proves a clock-independent ground-ray/effect bound in precisely that restricted task.

Proof. Theorem55.4 supplies convergence and the simple strictly positive common ground state. Every finite connected compression likewise has a positive simple ground vector by the same absolute-value and connectivity argument; choose the positive phases. If $m_j=m$, its finite-support zero extension would minimize the common form and hence be a multiple of $w$, impossible because $w$ is strictly positive at every address. Thus $m_j>m$. Compactness and uniqueness give $w_j\to w$. At the stated finite time the relative scalar phase is $-1$, so the norm in (58.22) equals $\|w_j+w\|\to2$. A scalar phase cancels from a one-state effect probability, which is why this particular obstruction is scoped to the full complex-amplitude task. It asserts neither failure of every probability task nor a native waiting, phase sensor or limit Read. □

**Definition 58.11 (authentic information consumed and its prices).** Conditional on the known actual addressed old domain, the next domain and the defect consume the beta-leaf mask $\mathcal B(s)$. The whole addressed defect recovers that mask, since $\Delta_s^*\Delta_s/(2a^2)=P_{\mathcal B}$. For one specified state the born derivatives only consume its beta-frontier amplitudes; for the full subsequent interaction task the retained full state, its modal coefficients/phases and the actual time-ordered operators are sufficient as in (58.3). An old autonomous root response law is insufficient by Proposition58.5. A complete retained operator-plus-state record is not contradicted by either example.

In a free ordered binary source, the actual domain together with this mask already determines every current leaf label and all ordered brackets. It is therefore not a newly demonstrated certificate cheaper than full current syntax. For a sequence of renewals the authentic current source and actual accepted action record determine all later masks by the existing source substitution, not by new label telemetry. To bind current reconstruction back to INITIAL also retain the root, absolute epoch and original source/history correspondence. The image-only inverses in `GenealogicalFiberTransport` and `SourceTransportCentralizer` are mathematical decoders, not authorized inverse actions.

The already supplied immutable-source address acquisition of `ActualTreeReadoutAcquisition` may restore a tree from a genuinely acquired, retained, complete authentic address history. Its original query actions, Boolean task, `alpha/beta/branch/absent` replies and distinct-address fees stay unchanged. A syntax-output consumer of that archive can calculate this mask. TM23's paid birth/replay supplier retains its own epoch, navigation and record permissions. Neither supplier acquires the actual amplitude coefficients, prepares a coherent state, reads a resolvent or obtains a physical clock. Old-version answers do not become a free cache for later current versions. Source decoding and state acquisition are different obligations.

Current §57's paid acquisition is already available under Definition57.1's exact public composition/image contract: third-multiple depth $d=3k$, $k\ge1$, nonempty complete ordered sources, exact composition $C=M^d(a,b)$, the original four endpoint replies at depth at most $h$, empty acquired history and source-independent causal initialization. Its substitution depth, composition parameters and Fibonacci matrix are §57's own, distinct from this chapter's spectral distance, kinetic coefficient and norm bound. Correctness and finite termination cover every complete same-composition competitor, including tall negatives; the target is image membership, not an assumed actual candidate identifier. Theorems57.3–57.4 supply complete-colour rigidity and exact depth solvability, Theorem57.7 supplies the threshold-qualified weighted diagnostic/frontier-completion bridge, and Theorem57.10 supplies its exact low-macro-leaf regimes. An actually accepted positive transcript contains a complete colour frontier and hence determines the current ordered labelled source and this beta mask within that competitor domain. Reuse requires an authentic binding of that acquired tree, root and epoch to this trajectory. Distinct requested addresses remain paid, repeats remain actual query actions, and control computation, memory, encoding and physical traversal retain their unpriced status in that contract. Static certificates and paid causal source acquisition are therefore established in their declared scope; they do not supply a coherent amplitude state, hidden relative phases, Hamiltonian actuation, physical transport or a clock.

The resource comparison must therefore keep at least original native commands and actual acceptances/refusals, all actual numerical/address Reads and their fees, source preparation, source/epoch authentication, acquired archive storage, amplitude preparation and retention, operator/actuator calibration, finite clock duration and precision, response implementation and readout precision. The count of amplitude coordinates in (58.2), event count $j$, accuracy bound (58.17) and original source syntax length are different coordinates. No actual matched price vector is supplied here; no cheap acquisition, storage reduction, energy saving, minimax price or physical superiority is inferred.

Nothing in this chapter changes $\mathcal D_2$, its independent arbitrary unbounded initial visible $a$ including zero, its untagged radius7/25 hidden $b$, destructive $\Gamma_d$ law, source-independent causal initialization, exact versus commanded/executed controls, actual Reads, joint adversarial errors, INITIAL target or §56's exact risk and nonattainment. No map from that register to this occurrence-amplitude realization is supplied.

**Definition 58.12 (reused sources, mathematical delta and remaining correspondence).** TM22.2 and TM23.2 own the literal same-address birth/exhaustion identities. Process44.1–44.7 owns the numerical task, shared initialization and equal-history source comparison. The fixed-cap original interface is TM30/57 and the specific literal history is §55.6. The kinetic gap, common potential, all-source domain containment, hidden channel decomposition, exceptional spectral account and gap-window limits are §§55.1–55.6 prerequisites. They are reused with the same counting measure, root, global depth, source, inherited boundary and normalization. The new deduction is their *joint native renewal interaction*: forced norm-preserving transfer, exact label-dependent frontier coupling, complete coefficient transport, finite-clock full-subescape fidelity and energy-based ground-ray preservation, with the consumed native-source and hidden-phase discriminators. Generic rank/fiber theory, a static tree-square identity, kernel arithmetic and syntax decoding are not claimed as that delta.

[FiniteHereditaryPatternRealization.result](../../../D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.lean) supplies the existing static shared-information-leaf realization for $m\ge2$ and a finite inclusion-lower family $K$ of subsets of `Fin m` containing every singleton. In its own notation $T=\operatorname{card}(\mathrm{Column}\ K)\ge1$ and $N=M(K)$, for every bijective column ordering the right-comb, face-column and private-row-padding construction gives injective families $Q_i,P_i$, $P_i=\rho^3Q_i$ in the actual third image, compositions $(T+N,N)$ and $(T+3N,2T+5N)$, total image leaf count $3T+8N$, and unique third preimages. For each index set $S$ with $|S|\ge2$, the set of addresses that are leaves in every indexed $P_i$ and bear both labels among them is nonempty exactly when $S\in K$. The original hole-address/suffix decomposition and disjoint-hole correspondence are retained. Its pattern parameters, information-leaf set and static source family are distinct from the clock bound, spectral projection and generator defect here. We reuse this established hereditary syntax/readout realization with its stated cardinality and singleton hypotheses; it does not supply a Hamiltonian, coherent phases, preparation, an energy law or renewal fidelity.

The classical exponential/Taylor/Krylov and unitary Duhamel tools are the existing [Causal Relational Response §§13.3,13.5–13.6](CAUSAL_RELATIONAL_RESPONSE_GEOMETRY.md). Gerald Teschl's primary [*Mathematical Methods in Quantum Mechanics*, Theorem5.1 and equation(2.87)](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf) supplies self-adjoint unitary evolution and the bounded Neumann-series method, already a source of §55.8. Theorem58.6 proves the particular two-operator support estimate (58.13); it does not attribute that estimate to a general decay citation. Finite Hermitian diagonalization, isometries, geometric series and Cauchy–Schwarz are mature intermediates. No additional Library supplier is needed.

A bounded comparison with the relevant immutable source at `6879f5b00c12ebded0eb5f088e4cafb8bd336de9` retains the neighbouring results in their own scopes. `LateLabelStateBound` concerns lawful three-bit FIB windows, signed scalar extrema and surviving vertices of finite full-path graphs. `TriangularPathNormalization` concerns legal reduced binary root paths, canonical probability columns and dyadic bit cost. [Fiber Calculus Continuation II §33](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md) concerns the original cyclic binary device, high-bit Read, charged Moore/Advance/Halt state counts and joint memory/read/action bounds, including sharing and loops. [Joint Moment Fibers §§1–8](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md) concerns one positive leaf-event word, fixed endpoints and area, its supplied planar reference, and its actual joint third-order moment image. None of these source contracts supplies the Hamiltonian transfer, amplitude preparation or a clock used here.

`ActualSpectralSeries.kernel_hasSum_of_eigenbasis` consumes an actual integral-operator factory and a complete supplied eigenbasis; `SameNoiseSecondChaos.secondIntegral_characterization` and `finiteFrequency_sameNoise` preserve their one Gaussian map and original probability law. These are not an occurrence-domain switching sensor or a new resampling permission. `MaximalUnobservableSubspace`, `ObservableKrylovGrowthBound`, `HankelMinimalStateDimension` and `BalancedRealizationTransport`, including their private kernel-descent and coordinate-transport helpers, retain their fixed finite linear realization, input/output, stability and Gramian assumptions. Their classical response structure is compatible with the uses above but does not make the changing addressed Hamiltonians conjugate or supply a switched acquisition protocol. `ExactRealProbeCosts` keeps its exact scalar probe, parameter charges and seed-correctness quantifiers; `OrderedPermutationDefectMass` keeps its finite ordered integer permutation and floor bounds. Neither turns a mathematical spectral quantity into a paid original Read.

The ordinary proofs and exact finite discriminators establish `repo-derived` deductions under the displayed contracts. The bounded repository/source and external literature comparison does not establish global absence or mathematical priority. No fresh Lean/kernel/axiom, repository test, current CI, coverage or physical validation is asserted.

The remaining native correspondence is substantive: exhibit an actually permitted source apparatus implementing an amplitude transfer and between-event Hamiltonian, with matched original actions/records, preparation, clock, errors and prices; bind the authentic source/root/epoch and beta masks using the existing paid acquisition when its exact promises apply, and acquire and retain the consumed hidden coefficients/phases through authorized channels; or prove a different faithful positive interaction bridge. Hypothesis15.1's full rotations, attainable faithful Euclidean displacement, physical field/kinetic/maintenance/precision/record prices and common-environment propagation/task-capacity remain unproved. The unit occurrence geometry is not mesh refinement or an open Euclidean three-dimensional region. Finite-clock full-state preservation is a useful conditional interaction relation on the same original source; it does not by itself settle physical spatial dimension, unbounded time, all-state fidelity or the full why-three-dimensions objective.

## 58.99 追加锚（本行以下为增补区）
## 59. 混色实际地址费用的部分界

**定义 59.1（部分界接口）。** 在原定义57.1的同组成、空取得历史与四值原地址合同下，若 $d=3k\ge3$、$a,b>0$、$n=a+b\ge4$、$h\ge d+n-1$，则 [混色实际地址费用卷定理1.4、5.3、7.3](FIB_ATOM_MIXED_ACTUAL_ADDRESS_PARTIAL_BOUNDS.md) 给出 $A+3\le D_h\le A+n-2+c_d(a,b)$，其中 $c_3=a$，$d\ge6$ 时 $c_d=\min(a,b)$；这是部分界，不是准确值。

其普通证明保留同一固定正源的完整原历史、重复动作、不同实际地址收费与两色终端分支；上界实际诊断、真实缓存和完整前沿补查覆盖全部同组成高负源。

## 59.99 追加锚（本行以下为增补区）

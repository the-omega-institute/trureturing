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

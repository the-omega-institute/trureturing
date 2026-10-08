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

## 60. A source-owned finite actuator for the installed whole-rho interaction

**Definition 60.1 (the source, apparatus and two clocks).** Fix a public integer $H\ge1$ and the exact private-source processor [PR57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#57-a-complete-paid-ideal-realization-of-the-original-ordered-tree-interface). Its actual source is its current valid $N=2H-1$ slot packet, with the literal two-bit tokens PAD, alpha, beta, PAIR of PR57.6. This packet, its preparation occurrence and its original INITIAL identity are the source throughout. There is no source selected from an observer fiber. Every supplied private ingress bit, validation, original request, complete candidate, guard, committed response, chronological row, copy, refusal and Stop uses PR57's own routines and ownership. The public actor starts with its original source-independent initialization and receives exactly its original records. Only original whole-rho modifications are used for the interaction trajectory here. The full PR57 source menu is retained: any actual named Left/Right context is still completely supplied, processed, guarded and recorded by its original routines. Rejected contexts leave the actuator installed. An accepted context may be compiled by Theorem60.2 on its actual new packet, but ends a commissioned whole-rho comparison; its different occurrence injection is not relabelled as the same-address transfer of §58. Any new amplitude commission after such a graft needs its own supplied supported state and paid carrier/preparation, with no reset of an unknown state.

Adjoin the following explicitly supplied ideal apparatus, owned by the producer. Its classical private workspace is read only with respect to the current-source packet. At an idle cut it locks that actual producer block, saves the public cursor positions, obtains the actual original interval descriptor by the paid read/copy routine of Lemma60.10, scans its fixed $N$ slots with the PR57 read/Boolean routines, and restores every borrowed cursor before releasing the lock. Save, seek, scan and restoration are charged apparatus work; no original packet data bit is written. It may compute private derived bits, but these bits have no actor, verifier or consumer observation port. Its quantum bank has one qubit for each address in

$$
\mathcal A_H=\{p\in\{L,R\}^*:|p|\le H-1\},\qquad
K=2^H-1,
\tag{60.1}
$$

and one additional qubit $r$ for a phase reference. All are constructed individually in $|0\rangle$ by a charged `QNew` occurrence. An excitation at address $p$ is denoted $|p\rangle$; an excitation at $r$ is $|r\rangle$. The declared operating sector is
$\mathcal U_H=\operatorname{span}\{|r\rangle,|p\rangle:p\in\mathcal A_H\}$, the one-excitation sector of these $K+1$ qubits. The much larger sectors of the qubit tensor product are not identified with occurrence amplitudes.

The supplied interaction blocks are a one-mode phase and a two-mode hopping gate, together with fixed finite preparation gates and an exact identity hold. With a classical private enable bit $v\in\{0,1\}$, the first two have the literal matrices

$$
\begin{aligned}
P_p(v,\xi)&=\exp(-iv\xi n_p),\qquad n_p=|1\rangle\langle1|_p,\\
B_{pq}(v,\xi)|_{\{|p\rangle,|q\rangle\}}
&=\begin{pmatrix}\cos(v\xi)&i\sin(v\xi)\\i\sin(v\xi)&\cos(v\xi)\end{pmatrix}.
\end{aligned}
\tag{60.2}
$$

$B$ fixes $|00\rangle,|11\rangle$ on its two qubits; $P=\operatorname{diag}(1,e^{-iv\xi})$ on its qubit. Both act as identity on untouched qubits. A block has public wiring and a finite signed dyadic angle string. Classical enable bits are loaded by charged fixed-address reads into a private latch. They are not quantum address queries. To execute a block without a word-sized angle latch, write $\xi=\sigma\sum_{j=0}^{J-1}d_j2^{j-b}$, $d_j\in\{0,1\}$, and scan every one of its $J$ digits. On digit $j$ execute the fixed rotation of angle $\sigma2^{j-b}$ with enable $vd_j$. The apparatus explicitly supplies a finite catalog of these elementary $P$ and $B$ rotations for all public exponents and signs required by the commissioned finite run. Catalog control descriptions and every digit fetch are installed and paid. Rotations within one block commute, so their product is exactly (60.2) at the written angle. Disabled digits still execute their charged identity slots. The catalog entries have exactly their declared matrices; that is the new ideal executed-parameter permission, not an inference from a numerical native Read or a claim that precision is free. A further error model below permits discrepancies at each elementary rotation. No physical implementation of this catalog is postulated as a consequence of FIB.

Each elementary catalog rotation occupies one logical gate tick; an angle block occupies $J$ such ticks, in addition to all its classical fetch work. All ingress, classical computation, construction, wire/angle description, fetch, gate execution and retention are paid. Keep the original PR57 receipt chain and fence numbering for original-processor work. The added actuator has a separately owned receipt chain for its extra routines and quantum events; its boundary cells and control are explicitly supplied and counted as apparatus foundation. Original work still appends exactly its original receipts, and extra work appends only actuator receipts. The total logical count is the sum of these two actual chains. Thus the original archive's closed-cut numerals and fees are preserved rather than silently reinterpreted as actuator time. The supplied phase reference has generator zero during interaction gates, and all modes have exact identity evolution during classical source service and compilation. Identity hold is an additional memory permission with its own retention price. The comparison clock $\tau$ advances by declared nonnegative rational intervals at completed interaction checkpoints. It is not PR57's receipt count, the number of substitutions or a calibrated physical time. Intermediate digital gate cuts are retained execution cuts, but are not asserted to satisfy the continuous Schrödinger equation of §58.1. Finite gate and compilation duration can therefore realize its zero-duration switch in the comparison clock without asserting zero work or zero apparatus time.

The additional carrier, classical private access, gate matrices, reference coherence, perfect ideal hold, supply of angle parameters, clock interpretation and all their prices are new permissions. The original source menu has acquired none of them.

**Theorem 60.2 (literal private compilation and the complete installed generator).** From the authentic current packet of any $s\in\mathcal T_H$, a finite fixed-schedule private Boolean computation constructs, for every public $p\in\mathcal A_H$,

$$
x_p=[p\in\operatorname{Pos}(s)],\qquad
b_p=[s|_p=\beta].
\tag{60.3}
$$

It constructs these bits from the current source, without a source-size reply, address oracle, acquired archive, private-data-dependent seek or counterfactual source. The resulting supplied gate decomposition has, on $\mathcal U_H$, generator

$$
\widehat H_s=
\sum_{p\in\mathcal A_H}x_p\bigl(a d_p-g2^{-|p|}\bigr)|p\rangle\langle p|
-a\sum_{\substack{q\in\mathcal A_H\\q\ne\varepsilon}}
 x_q\bigl(|q^-\rangle\langle q|+|q\rangle\langle q^-|\bigr),
\qquad d_p=\begin{cases}2,&p=\varepsilon,\\3,&p\ne\varepsilon.\end{cases}
\tag{60.4}
$$

Here $q^-$ is the actual parent address. It fixes the reference and inactive coordinates. If $V_s:\ell^2(D)\to\mathcal U_H$, $D=\operatorname{Pos}(s)$, sends $e_p$ to $|p\rangle$, then

$$
\widehat H_s=0_{\mathbb C r}\oplus V_s\mathsf H_DV_s^*
 \oplus0_{\operatorname{span}\{|p\rangle:x_p=0\}}.
\tag{60.5}
$$

In particular every actual leaf keeps both missing-child killing terms, the potential is the common $2^{-|p|}$ restriction, and every internal, exceptional and root-invisible direction is retained. No free-standing subtree potential or newly solved killed field occurs.

Proof. The all-source address cover and its size are the existing [Fiber Calculus II Lemma38.40](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md#384-叶预算的原几何与精确迹编译), with its leaf-budget parameter set to this $H$. This is only a finite cover for allocating the bank; it does not restrict the original menu or make a source reply available.

Here are explicit compiler instructions. Use $H+1$ private pending-address rows, each containing an $H$-bit zero-padded path and a length, and a private stack height $h$. Put the root in row zero and set $h=1$. Use width $w=\lceil\log_2(4H+8)\rceil$ for lengths and signed temporary counters. For each of the $N$ token slots, in its public order, select the top row by OR-ing the row bits under the masks $[j=h-1]$ over every $0\le j\le H$. The case $h=0$ selects a zero dummy row. Record its path and length with the token's non-PAD bit. Every row and bit is scanned even on PAD.

For PAIR, replace row $h-1$ by that path followed by $R$, replace row $h$ by that path followed by $L$, and set $h$ to $h+1$. For a leaf set $h$ to $h-1$; for PAD leave it unchanged. These are bitwise MUX writes to every row, selected by equality masks, not writes at a private address. Stale rows above the new height are immaterial and remain private. Form both possible children even when the token is a leaf or PAD. A child path is formed by scanning every path-bit position and testing equality with the old length; incrementing its length is a fixed-width addition. Actual branch depths are at most $H-2$, while unused leaf-child expressions have length at most $H$, so the reserved path and counter widths suffice. The unselected arithmetic arms are inside the signed range; no underflow is interpreted as a valid address.

The pending rows, from top downward, are exactly the remaining preorder node addresses. This invariant follows by replacing the first pending address by left then right on a branch and by deleting it on a leaf. It holds initially and at each active token. Valid padding begins only after closure by PR57.T1, when $h=0$. The stack never has more than $H$ pending nodes: every pending subtree is nonempty and their disjoint leaves belong to the same source of at most $H$ leaves. Thus each recorded active address is exactly that token's actual address. Fold all $N$ recorded rows against each public $p$, using full path-and-length equality, and OR the active matches to get $x_p$; add the beta-token test to get $b_p$. Distinct active tokens have distinct addresses, although the OR recipe does not assume a unique match as a machine primitive.

All operations just described expand into PR57.5's fixed-width additions, comparisons, Boolean truth tables and MUXs; PR57.3 supplies allocation, unary descriptors and every seek. For example a sufficient upper bound on the number of Boolean gates, including initial constant writes, is

$$
G_{\rm flag}(H)=100N(H+1)(H+w+1)^2+20NK(H+w+1).
\tag{60.6}
$$

To check this bound, in each token iteration the two counter updates, top equality selection, child construction and two MUX writes per row take at most $100(H+1)(H+w+1)^2$ gates using the five-gate adder, three-gate-per-bit equality and one-gate MUX of PR57.5. Each recorded-row/public-address match and the two folds take at most $20(H+w+1)$ gates. The generous constants also cover initialization and the terminal height check. This is a Boolean-gate bound, not a native tick count. Generation writes every instruction and all unary references, and their native costs are counted separately in Definition60.7.

The only edges installed in (60.4) are parent–child seams with an actual child. Downward closure gives an actual parent. A leaf diagonal is never obtained by counting its installed neighbours: it is the inherited $a d_p-g2^{-|p|}$ even when its children are absent. Consequently (55.4) is exactly the active principal block, proving (60.5). The common field values are generated from public depth by a binary shift, not read from a hidden field oracle. $\square$

**Theorem 60.3 (guarded installation, same-source renewal and record projection).** Supply a producer lock excluding simultaneous source service and interaction gates. Compile the initial current block after its original valid preparation. Thereafter run the original PR57 source schedule for each whole-rho request, including its complete candidate guard and original response. At whole-rho acceptance compile from the just-installed current block and atomically release the new actuator version; at rejection retain the old actuator version. During service and compilation hold the entire quantum bank. Each Read preserves the current source and installed actuator, and each refusal supplies no candidate Read. Every Stop is absorbing for source requests, interaction checkpoints and quantum readout. Any commissioned terminal quantum readout is completed before Stop; only the original finite record delivery, verification and consumer-output routines may remain after its source-stop commitment.

Every finite original lawful source history retains its unique original service and records. For a whole-rho interaction commission with finite public local work, the additional schedules give a unique finite joint execution as well. Projection retains its exact INITIAL, current source, original initialization, chronological requests, every original Read/accept/reject/Stop and all original record fields and copies. If $s'=\rho s$ is actually accepted, then the unchanged bank realizes precisely §58.2's $J$:

$$
V_{s'}J=V_s,\qquad
\widehat H_{s'}V_s-V_s\mathsf H_D
=-a\sum_{p:b_p=1}|pL\rangle\langle e_p|
-a\sum_{p:b_p=1}|pR\rangle\langle e_p|.
\tag{60.7}
$$

No new excitation, copy or measurement of the old state is used at renewal. The private label changes are installed even when $D'=D$, as for a single alpha leaf becoming beta.

Proof. PR57.T1–T2 give the authentic original packet, full-candidate guard, exact responses and actual successor. PR57.L4 gives chronological record and copy authenticity, and PR57.T5 gives finite progress. The new flag compiler terminates by its finite public loops and PR57's terminating routines. The lock makes its input one committed current version. No actuator descriptor refers to an uncommitted or refused candidate. Since $\rho$ preserves old addresses and only adds children at old beta leaves, §58.2 gives $D\subset D'$. The same physical bank vectors therefore satisfy $V_{s'}J=V_s$. Their initially unoccupied new coordinates stay zero during hold; identity release is the forced transfer, with no state-dependent preparation. The old principal block and newly enabled child seams give (60.7). This consumes the established renewal identity rather than rederiving it from a scalar spectrum.

Induction on original cuts proves the projection assertion. Source service and original archives are the original routines; additional private computations do not edit their source or response fields. Private compiled bits are derived workspace, not a second callable source, current-to-INITIAL reset or an actor-readable source copy. All original record-copy work remains executed and charged. The separate actuator receipts do not advance the original processor's meter. Each borrowed source cursor is restored before original service resumes; the original routine therefore has exactly its old entry cursor, packet and meter. Original fence numerals, source records and copies retain their literal original values and framing, while actuator fences belong to its separately named chain. No response is synthesized from an actuator or a retained spectral calculation.

There is also an observation boundary. Give the original actor the public extra instruction, address, busy/idle and fee labels, but no enables, unreleased private workspace or quantum measurement. At each fixed $H$, the flag compiler, wire schedule and gate count depend only on public bounds and original committed responses. If interval/preparation choices are supplied publicly or selected from that same acquired prefix, PR57.T3 extends by simulating these extra fixed schedules with dummy private bits. Thus these added labels disclose no source distinction beyond the actor's original acquired history. This is an ideal observation theorem: electrical activity, state-dependent failure, a leaked enable or a quantum readout would be additional observations requiring another contract. A separately commissioned quantum readout may distinguish sources, but is never an original Clifford Read. $\square$

**Theorem 60.4 (source-generated finite circuits with full-phase error).** Suppose $a,g>0$ are public rationals, or come with paid effective rational enclosures and public upper bounds $\bar a,\bar g$. Choose nonnegative rational approximants $\widetilde a,\widetilde g$ within those upper bounds and certified errors $\delta_a,\delta_g$. Exact rational coefficients permit $\delta_a=\delta_g=0$. Set

$$
\overline M=6\bar a+\bar g,\qquad F=K+(K-1)=2K-1.
\tag{60.8}
$$

There is a public three-colouring of the bank's parent–child seams such that each colour is a matching. One product slice executes the $K$ phase slots of (60.2), then all edge slots in colour order $0,1,2$, using the installed private bits (60.3). For an interval $\theta\ge0$, use $m\ge1$ slices with $\delta=\theta/m$, angle $\delta(\widetilde a d_p-\widetilde g2^{-|p|})$ at site $p$ and angle $\delta\widetilde a$ on every edge. Round every angle to a signed dyadic with absolute error at most $u=2^{-b}$; retain and fetch all angle bits. Let $\widetilde U_s(\theta)$ be the actually executed ideal circuit. Then, on the whole one-excitation sector,

$$
\left\|\widetilde U_s(\theta)-e^{-i\theta\widehat H_s}\right\|
\le \frac{\overline M^2\theta^2}{2m}+Fm\,2^{-b}
+\theta(6\delta_a+\delta_g).
\tag{60.9}
$$

This is an operator norm with the reference phase fixed, not a distance modulo a scalar phase. The product-formula part is independent of $H$; its actual gate and angle-precision prices still depend on $K$.

Proof. Assign a virtual incoming colour zero at the root, without installing an incoming edge. At a vertex with incoming colour $c$, assign colours $c+1,c+2$ modulo three to its left and right child seams. Each nonroot vertex has three distinct incident colours; the root has two. Removing inactive edges preserves the matching property. This public recursive wire list is generated from addresses, with no private traversal.

On $\mathcal U_H$, group all diagonal terms as $A_0$ and each matching's hopping terms as $A_1,A_2,A_3$, using the approximated coefficients. The diagonal norm is at most $3\bar a+\bar g$. Each matching is an orthogonal direct sum of two-by-two matrices of norm at most $\bar a$, and zero coordinates. Hence

$$
\sum_{j=0}^3\|A_j\|\le\overline M.
\tag{60.10}
$$

This estimate is on the declared one-excitation sector, not on every excitation sector of the qubits. Terms in each group commute, so its exponential is exactly the corresponding list of local gates before angle rounding. In particular no scalar identity part of $A_0$ is dropped.

Use the classical first-order Hermitian product bound of Childs–Su–Tran–Wiebe–Zhu, [*A Theory of Trotter Error*, Proposition15, equation(145)](https://arxiv.org/html/1912.08854v3#S5.SS1), published as *Theory of Trotter Error with Commutator Scaling*, [DOI10.1103/PhysRevX.11.011020](https://doi.org/10.1103/PhysRevX.11.011020). It bounds a slice's error by
$\delta^2\sum_{j<k}\|[A_j,A_k]\|/2\le\delta^2\overline M^2/2$.
Its hypotheses hold because the four groups just constructed are Hermitian on this same finite invariant sector. Unitary telescoping over $m$ slices gives the first term in (60.9). This mature simulation estimate is an intermediate, not new Trotter theory.

The generators of each enabled $P$ or $B$ have norm at most one, so changing its angle by $u$ changes its unitary by at most $u$, by the unitary Duhamel estimate already used in §58.8. There are exactly $Fm$ slots, including disabled ones; telescoping gives the second term. Finally (60.5) and $\|L_D\|\le6$, $\|M_\phi\|\le1$ give generator error at most $6\delta_a+\delta_g$. The reference and inactive blocks are zero for both coefficient choices. Duhamel gives the last term. Every gate leaves the inactive amplitude subspace invariant, because no enabled edge leaves the actual domain. $\square$

**Corollary 60.5 (finite histories, executed parameters and complete spectral correspondence).** Commission $L$ finite interaction checkpoints at original idle cuts, with intervals $\theta_\ell\ge0$, total $S\le T<\infty$, and any finite number of intervening original Reads, refused requests and accepted whole-rho renewals. Let $U_{\rm hist}$ be §58.1's exact time-ordered finite-domain propagator with its forced transfers, represented in the fixed bank. Execute the circuits of Theorem60.4 on the current committed packet at each interval. For possibly different $m_\ell,b_\ell$ put

$$
E_{\rm circ}=
\sum_{\ell=1}^L\left[
\frac{\overline M^2\theta_\ell^2}{2m_\ell}
+F m_\ell2^{-b_\ell}
+\theta_\ell(6\delta_a+\delta_g)\right].
\tag{60.11}
$$

At every completed commissioned checkpoint, the operator difference from $U_{\rm hist}$, on the initially active sector and the reference, is at most the corresponding prefix of this sum. It includes arbitrary hidden coefficients and their relative phases. Zero intervals need no gate slots.

For a supplied unit prepared state with norm error $\eta_{\rm prep}$, actual unitary gates preserving the declared sector with deviations bounded there in operator norm by $\zeta_j$, accumulated sector-preserving unitary hold/locking error $\eta_{\rm hold}$, and a declared comparison-clock interval discrepancy sum $\eta_\tau$, the state bound gains at most

$$
\eta_{\rm prep}+\sum_j\zeta_j+\eta_{\rm hold}
+(6a+g)\eta_\tau.
\tag{60.12}
$$

The ideal model executes the literal dyadic angles, so $\zeta_j=0$; its comparison clock is the commanded interval string, so $\eta_\tau=0$. For a perturbed angle law, a certificate $|\xi_j^{\rm exec}-\xi_j^{\rm cmd}|\le\gamma_j$ supplies $\zeta_j\le\gamma_j$. Other gate, reference or hold faults need their own bounds; they are not inferred from native Read errors. No error independence is required. The formula is conditional on the authentic packet, exact source guard and version lock; a wrong source or omitted channel is not a precision certificate.

Proof. The bank is unchanged at switches and holds, so Theorem60.3 gives the exact transfer at every accepted renewal and identity on refusal/Read. Telescope the finite unitary factors, using (60.9) at each actually installed version. Unitarity propagates errors without amplification. The same argument for the actual gate products gives the sum of $\zeta_j$; the stipulated hold error is added on its actual cuts. The source-independent bound $6a+g$ and the clock comparison of §58.8 give the final term. Nothing takes an event after an infinite prefix or after Stop.

For exact spectral correspondence, extend $V_s$ by the reference. Formula (60.5) implies for every Borel set $\Omega$ that the restriction of $E_{\widehat H_s}(\Omega)$ to the active sector is $V_sE_{\mathsf H_D}(\Omega)V_s^*$. Its reference block is $\mathbf1_{0\in\Omega}$, and the inactive zero blocks are explicitly outside the target. Thus every finite exceptional energy, full multiplicity, hidden eigenvector and full normalization in §55.5 survives in the installed target generator. For complete old/new orthonormal eigenbases, its renewal coefficients are exactly $\Gamma_{\nu\mu}$ of (58.3), because $V_{s'}J=V_s$. The actual finite gate product has the propagator error (60.11); it is not claimed to have the exact eigenvectors of $\mathsf H_D$ or to supply an acquired spectral archive.

If the preparation and reached-domain hypotheses of §58.7, or of §58.8, are separately fulfilled, its common full-state comparison gains (60.11)–(60.12). That inference reuses the same common field, all contrast channels, actual irregular domains and full phases. The present source compiler does not prepare an unspecified infinite spectral state or remove those hypotheses. $\square$

For example, given rational $\varepsilon>0$, $L\ge1$, a public $T$ and coefficient upper bounds, choose a common
$m=\max\{1,\lceil2\overline M^2T^2/\varepsilon\rceil\}$ and a finite integer $b\ge0$ with $2^b\ge4LFm/\varepsilon$. The first two terms in (60.11) total at most $\varepsilon/4$ each, since $\sum\theta_\ell^2\le T^2$. Supply coefficient errors with $T(6\delta_a+\delta_g)\le\varepsilon/4$ and preparation/remaining errors at most $\varepsilon/4$. The total is at most $\varepsilon$. This supplies finite parameters for every commissioned finite accuracy, not a physical calibration or an accuracy uniform over unbounded $T$.

**Proposition 60.6 (paid preparations, full phase and an operational boundary).** An input-independent preparation is available for every actual source: construct all $K+1$ zero qubits, apply a supplied exact bit flip at $r$, then a supplied balanced two-mode gate mapping $|r\rangle$ to $(|r\rangle+|\varepsilon\rangle)/\sqrt2$. These two fixed finite gates and their descriptions are charged. The reference and target amplitudes are retained in this one carrier, not in two copies of an unknown state.

More generally an explicitly supplied finite nonzero complex rational array $z=(z_p)$, supported on the actual domain, permits paid preparation of either $V_sz/\|z\|$ or
$(|r\rangle+V_sz/\|z\|)/\sqrt2$ to any positive norm tolerance. This is effective known-state preparation from material data, not preparation of an arbitrary unknown state or inference of coefficients from the source's spectrum.

Proof. The first construction has the stated literal result and requires no source-dependent controller initialization. For the second, start either with a charged root bit flip or with that balanced reference/root preparation, and apply the following address-mode rotations, which fix $r$. Let $f=z/\|z\|$ and enumerate the bank with root first. A succession of real two-mode rotations between root and each other mode $p_j$ splits off its prescribed nonnegative magnitude. At step $j$, choose

$$
\sin\vartheta_j=
\frac{|f_{p_j}|}{\sqrt{|f_\varepsilon|^2+\sum_{k\ge j}|f_{p_k}|^2}};
\tag{60.13}
$$

a zero denominator gives the identity. The remaining root amplitude is the square root of the unused total weight, so induction gives all magnitudes. Phase gates then install $\arg f_p$ at each nonzero coordinate. Real rotations are conjugates of $B$ by the supplied fixed phases $\operatorname{diag}(1,i)$ and its inverse. The balanced gate, these fixed phases, and the bit flip are finite constant matrices explicitly included in the apparatus, not arbitrary angle advice.

There are at most $K-1$ variable rotations and $K$ variable phases, with their fixed conjugating gates. For rational input the zero cases are decidable. Rational interval arithmetic, square-root bisection and sine/cosine bisection on fixed quadrants compute each angle to any given positive tolerance: positive denominators have finite rational lower bounds obtained from the nonzero input entries; the continuous inverse on $[0,\pi/2]$ can be bracketed to any positive angle width. Trigonometric values can be enclosed by their convergent Taylor series with explicit factorial remainder. Use overlapping brackets of width below the desired angle tolerance, with strict outward inequalities; a root on one mesh boundary is interior to a neighbouring overlapping bracket. Refining the value enclosures then certifies a bracket in finitely many steps. The zero and unit endpoints are detected from rational squared magnitudes. Thus no exact equality test on computable transcendental values is required. Charge all these arithmetic steps and all supplied input bits. Rounding these $2K-1$ variable angles within $v$ changes the preparation by at most $(2K-1)v$; fixed conjugations are exact in the ideal model. This is a constructive finite procedure, with no unknown-state oracle. A promise that the array is supported on $D$ must either be supplied or checked privately against (60.3), and that check is paid. A falsely supported array has no promised target preparation.

The phase reference is load bearing. For a singleton current source at $H=1$, the exact target is $[2a-g]$, and after interval $\theta$ the prepared joint state is
$(|r\rangle+e^{-i(2a-g)\theta}|\varepsilon\rangle)/\sqrt2$. The separately supplied terminal effect onto $(|r\rangle+|\varepsilon\rangle)/\sqrt2$ has probability
$[1+\cos((2a-g)\theta)]/2$. Dropping a scalar shift from the target changes this relative phase and generally changes this probability. A one-state ray account cannot replace (60.9).

For a common preparation digit width $J_P=b_P+3$, retaining every variable slot gives $G_P=1+(2K-1)J_P+2(K-1)$ elementary preparation gates for the target alone, or $G_P=2+(2K-1)J_P+2(K-1)$ for the joint reference/target state. The extra one is the balanced gate; the two fixed phase conjugations per hopping block are included. The magnitude margin covers all angles in $[-\pi,\pi]$. These are declared schedule counts, including zero entries; all rational-array ingress, normalization/angle computation, root-to-mode wire and signed-catalog descriptions, fetches and classical receipts remain additional in (60.16). Choosing a finite $b_P$ and certified angle brackets with $(2K-1)v\le\eta_{\rm prep}$ gives the stated preparation tolerance. This uses explicitly supplied root-to-mode preparation wiring, not an original source operation.

The displayed terminal effect is implemented by the inverse balanced gate on $(r,\varepsilon)$ followed by one explicitly supplied computational-basis measurement of the reference qubit. These are two quantum slots; output-bit construction, framing and delivery are separately paid classical work. Other terminal effects require their own specified finite measurement circuit and error contract. A single execution gives one outcome, not an exact calibrated probability Read. No repetition, fresh source, reset or independent noise law is supplied. Arbitrary supplied states are transported by the all-state operator bounds without being measured or copied, but their acquisition and preparation must come from an actually permitted source. The construction does not add a coherent reference to an arbitrary unknown input: an unknown joint input must already have its expressly supplied reference/preparation contract. $\square$

**Definition 60.7 (finite descriptions, exact logical prices and simultaneous storage).** The following prices belong to this ideal apparatus. They do not replace the original charges or claim physical optimality. All added classical routines use PR57's opcodes, complete tape encodings, actual allocator recipes, one-cell receipt rule and fee two per core occurrence, routed to the actuator's own chain. Source cursors borrowed under the producer lock are restored by paid Home/Seek routines. Original service retains its original meter and charges; no source-service event is omitted or assigned to both chains. Add `QNew`, one enabled/disabled elementary catalog rotation and a fixed terminal measurement as finite-local quantum core occurrences, each with one new meter receipt and fee two. An elementary rotation changes only its named one or two qubits; its enable is a finite private latch, and its public catalog index is already installed finite control. Digit/enable loading and all catalog/description work are separate classical occurrences. `QNew` creates one qubit in the stated state; it never resets an already constructed qubit. An ideal hold has identity action; retention costs one quantum-mode unit per bank mode per logical tick, including compilation and original service. One quantum mode and eight classical bits are separate storage coordinates.

A public bank description lists every address, wire and three-colour edge, plus the reference, and is installed bit by bit. The address of each qubit is its bank-list ordinal in unary, with its actual connection specified by the public list. No private integer chooses a qubit. Each angle block has a literal record consisting of its opcode, unary endpoint ordinal(s), unary enable-workspace offset, sign, unary scale $U(b)$ and length-framed fixed-width angle magnitude; a terminal marker ends the list. A fixed interpreter scans/copies these fields using PR57's complete routines, then loops over the stored finite magnitude length. Each iteration reads the next digit, reads the fixed enable, computes their AND with `BF`, executes the installed catalog rotation for that public digit position/sign, advances the digit cursor and paid unary position counter, and tests its stored bound. Its only new quantum transition is the declared fixed-angle local rotation; no primitive reads an unbounded angle word. Catalog selection depends on public position, never the private enable. All these finite control, scan and counter occurrences are counted. In particular fixed wiring is supplied material, not a qRAM lookup. Parameter length, synthesis and routing costs are retained, even for disabled gates.

For positive intervals put

$$
G_{\rm block}=F\sum_{\ell=1}^L m_\ell,\qquad
G_Q=F\sum_{\ell=1}^L m_\ell J_\ell,
\quad J_\ell=b_\ell+k_\ell,
\quad k_\ell=\left\lceil\log_2(2+(3\bar a+\bar g)\theta_\ell+\bar a\theta_\ell)\right\rceil+2.
\tag{60.14}
$$

These are respectively the exact interaction angle-block count and elementary quantum rotation count when all magnitudes use that declared fixed width. The integer margin covers sign/magnitude rounding. Zero enable/digit slots are included. Preparation and terminal measurement add their own actual elementary gate counts. Write every repeated slot in full, or retain a finite literal body with a paid unary loop counter; either representation is charged by its actual routine. One elementary finite description bound is obtained by writing the complete list. If $R_c$ is the largest allocated enable-workspace offset and $B_\ell$ bounds a signed fixed-point angle string, the length of its interaction part is at most

$$
1+\sum_{\ell=1}^L Fm_\ell(40+4K+R_c+2B_\ell),
\quad
B_\ell=4(b_\ell+k_\ell)+20.
\tag{60.15}
$$

The $2B_\ell$ allowance covers sign, unary scale, unary length framing and all $J_\ell$ magnitude digits; the constant covers opcodes, separators and field terminators. The enable offset is stored in unary, and the two endpoint ordinals are at most $K$. A publicly supplied rational upper bound can replace the expression inside the logarithm; its width is found by the paid integer-doubling routine. This is a finite encoding bound, not an automatically installed program.

For a finite joint run let $E_C$ be its actual classical core count, obtained by expanding all PR57 service and generator recipes, including source supply, compilation, parameter arithmetic, instruction construction/fetch, original policy, all original rows/copies and any record-only verification/output actually commissioned. Let $Q_N=K+1$ count qubit construction, and let $G_P,G_R$ count actual preparation and readout quantum slots. Then the declared exact price coordinates include

$$
\begin{aligned}
E&=E_C+Q_N+G_Q+G_P+G_R,\qquad \mathrm{Fee}=2E,\\
\mathrm{Storage}(c)&=
\bigl(S_0+b_{\rm ctl}(c)+8A(c)+8E(c),\ Q(c)\bigr),\\
\mathrm{Retention}(r)&=\sum_{c\text{ a logical tick of }r}Q(c).
\end{aligned}
\tag{60.16}
$$

$A(c)$ counts all constructed ordinary cells, including erased compiler versions, the authentic current packet, complete refused-candidate scratch, all instructions/angles, private flags, original archives, mailboxes and verifier/consumer copies simultaneously. Here $Q(c)$ is the number of qubits already constructed at that same cut, at most $K+1$; after bank construction it is $K+1$, and this is its peak. The second storage coordinate is qubits. Classical peak is the maximum of the displayed first coordinate over the same cuts, not a sum of separate phase maxima. Retained but erased cells are still counted. Every original or added core event constructs one receipt in its own chain, so their total cumulative meter term is $8E(c)$, including quantum events; the two chains' boundary/control foundations are counted in $S_0$. Original fee $2E_{\rm original}$ and added fee $2E_{\rm actuator}$ are separate coordinates whose sum is $2E$. Any separately supplied hardware/control/reference description outside the fixed primitive basis is installed and counted in $b_{\rm ctl}$ or $A$.

These expressions are effective finite evaluations of displayed recipes. For each compiler Boolean gate, its literal code length and interpreter cost are PR57.05–PR57.06 with the actual constructed operand addresses; thus (60.6) does not silently price one Boolean operation as one tape tick. Initial supply has exactly the original $2N$ private ingress bits and their paid writes. Each subsequent compilation reads the very same committed source block, generates all flags and retains their version binding. Finite $H$, finite effective public parameter supply, finite original local computations and a finite commissioned checkpoint list give finite description, $E$, simultaneous storage and retention. There is no uniform bound over arbitrary finite histories, an optimality claim, a physical energy price or a source-copy credit.

**Proposition 60.8 (actual guarded distinctions and finite certificates).** Let $H=3$ and take two actual INITIAL trees

$$
t=\langle\langle\alpha,\alpha\rangle,\alpha\rangle,
\qquad u=\langle\alpha,\langle\alpha,\alpha\rangle\rangle.
\tag{60.17}
$$

Both have the original Clifford history
$\operatorname{Read}[A];\rho[\mathrm{accept}];\operatorname{Read}[-B];
\rho[\mathrm{reject}];\operatorname{Read}[-B];\operatorname{Stop}$.
The actual leaf counts are $3,3,6$. On the common bank, at their initial or once-accepted versions, for $a=1,g=16$,

$$
(\widehat H_t-\widehat H_u)|L\rangle
=-|LL\rangle-|LR\rangle,\qquad
\|(\widehat H_t-\widehat H_u)|L\rangle\|^2=2.
\tag{60.18}
$$

This distinction is generated by their authentic private packets although their original numerical records coincide. It need not be exported to the original actor. The refused second renewal never enables its candidate children.

Proof. Their leaf words are both $\alpha\alpha\alpha$, and after one whole substitution both are $\beta\beta\beta$. The original relations give $A^3=A$, $B^3=-B$; the complete guard at $H=3$ accepts the first three-leaf candidate and rejects the next six-leaf candidate. The installed domains are respectively $\{o,L,R,LL,LR\}$ and $\{o,L,R,RL,RR\}$, with unchanged shapes after the first substitution. Formula (60.4) gives the identical inherited diagonal at $L$ in both, the identical parent seam, and only the first source's two actual child seams there. This gives (60.18). Compiling a public representative of their shared Read fiber would fail this all-state identity on one of the actual sources.

For the single actual source $E=\langle\beta,\alpha\rangle$ at the same cap, the accepted domain and full matrix are exactly (55.22) with potential diagonal $(-14,-5,-5,-1,-1)$. In preorder $(o,L,R,LL,LR)$ the producer-generated edge groups are
$\{(L,LR)\}$ in colour zero, $\{(o,L)\}$ in colour one, and $\{(o,R),(L,LL)\}$ in colour two. The last two edges are disjoint. The normalized hidden state $(0,0,0,1,-1)/\sqrt2$ remains an exact target eigenvector at $-1$, even though the digital factors individually need not preserve that eigenspace. The full target characteristic polynomial is precisely (55.24), not the cancelled root resolvent. Thus (60.9) bounds its complete phase evolution as well as the visible modes.

The prepared $f_\pm$ of §58.5 are known finite vectors and can be supplied by Proposition60.6 to any positive norm tolerance. After the actual accepted renewal their original full target probability difference at $\theta=1/100$ has the exact certificate (58.11), whose magnitude exceeds $3.435\cdot10^{-8}$. Reuse that certificate. If each separately prepared and executed comparison has state error at most $\eta$, its root-effect probability error is at most $2\eta$, so the difference error is at most $4\eta$. Choosing, for example, $\eta\le10^{-9}$ preserves the negative sign. This is finite by (60.11) and Proposition60.6, with all preparation and execution work charged. It does not assert an exact-probability native Read or an independently resampled experiment.

A less demanding explicit parameter certificate is $\bar a=1,\bar g=16,T=1$, $L=4$, $K=7$, $\varepsilon=1/100$. The sufficient choices above give $m=96800$, $b=31$ and $G_{\rm block}=5033600$; choosing the common public magnitude width $J=38$ gives $G_Q=191276800$ elementary rotations, before preparation/readout; the product-formula budget is $1/400$ and the angle budget is $5033600/2^{31}<1/400$. These counts concern exactly four commissioned positive intervals with total at most one, independently of how many original source Reads occur between them. They are upper bounds for declared ideal precision, not timings of a physical apparatus. $\square$

**Definition 60.9 (source attributions and mathematical boundary).** The source algebra, actual substitution, ordered labels and brackets are `GenealogicalFiberTransport.Source/substitution/composition`, and their actual address functions are `ActualTreeReadoutAcquisition.readout/nodes/leaves`. PR57.1–PR57.11 supplies the actual material packet, private fixed schedules, original Clifford responses, whole guard, unchanged INITIAL, paid ownership/copy records, effective finite control and exact logical tally. The source is that installed packet, not the readout function of a different immutable-source consumer. §§55.1–55.5 supplies the exact common potential, counting norm, inherited kinetic/boundary operator and complete spectral account; §§58.1–58.3 supplies the renewal law, forced transfer and complete modal update. Those facts are prerequisites consumed at their original objects and parameters.

Fiber Calculus II §38 supplies bounded address coverage and distinguishes exact actual-trace preservation from protocol redesign, coarse quotient and finite observer claims. Only its address cover is used to allocate this actuator; no original Read, including a long request in an auxiliary supplied interface, is deleted by an absent-address optimization. [Joint Moment Fibers §§28–35](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md#28-同一原生树的完整前沿与任务取得) supplies genuine complete-frontier acquisition, raw/coarse separation, same-controller costs and retained-record scope. If such an authentic acquired archive is actually supplied to another consumer, its known decoding may recover syntax; this construction requires no such archive and obtains no phase, actuation or INITIAL history from those acquisition theorems. Their proofs and costs are not repeated or identified with (60.16).

Number-conserving two-mode rotations and phase gates are mature circuit tools; the [existing circuit note](../../../Library/QuantumStates/kerenidis2026scalablequantumml.md) records their one-excitation matrices and the danger of losing a common vacuum phase. Barenco et al., [*Elementary gates for quantum computation*](https://arxiv.org/abs/quant-ph/9503016), [DOI10.1103/PhysRevA.52.3457](https://doi.org/10.1103/PhysRevA.52.3457), supplies the mature one-/two-qubit circuit setting. It does not supply this source's enable bits, prices or physical gates. Its general universality is not substituted for the explicit source compiler. The product-formula and Duhamel facts have their precise roles in Theorem60.4. Known-state rotation preparation is a classical intermediate in Proposition60.6. No additional Library construction is required for these uses.

The `repo-derived` content is the source-private fixed-schedule producer of the exact installed field/kinetic interaction, its guard-locked same-bank renewal, the reference-preserving complete-sector correspondence, and the finite circuit/resource/error composition on the actual original records. It is an ordinary mathematical construction in an explicitly supplied finite ideal actuation model. No global novelty, current kernel verification, physical hardware conformance or optimal circuit complexity is asserted.

The actuator's public address wiring is an added computational carrier, not an Euclidean displacement system. Tree degree, qubit count, local direction dimension, retained source information, precision and physical cost remain different quantities. The original $\mathcal D_2$ model, its arbitrary independent unbounded visible initialization, untagged hidden value, destructive actions, command/executed-control distinctions, joint adversarial Read errors and INITIAL target remain unchanged. No identification with that source is made. Actual rotations/displacements, physical field and kinetic suppliers, calibrated elapsed time, extensive many-body stability, mesh/continuum limits and the complete why-three-dimensions objective remain separate obligations. The finite circuit comparison is at its declared checkpoints and finite comparison clock; it does not strengthen §58's full-phase scope to unbounded time, create a limit Read, or prepare an unspecified common bound state.

**Lemma 60.10 (expanded Boolean code, authentic input and cursor restoration).** The compiler of Theorem60.2 admits a literal implementation in (PR57.05), with no instruction depending on a private address. One implementation allocates two constant cells, a private $2N$-bit input cache, and one fresh result cell for every Boolean gate. Constants and input-cache cells are initialized by actual writes. This dedicated workspace begins at data index zero on its own apparatus port. Its $R$ signal cells and fixed code can be reused at subsequent versions after a complete charged erase/initialization and authentic input copy. Every signal is rewritten before its current use. Erased cells remain constructed, and any separately commissioned retained flag snapshot is actually copied and charged. This is classical workspace reuse under the lock, not a quantum reset or a new original source. The cache is a derived private workspace, has no callable source/actor port, and is bound to the locked current block and its original version. Copying it does not duplicate the running source, acquire INITIAL from a later version, or permit another original action on a copy. This additional private read/copy permission is precisely Definition60.1's producer access, and its complete work and retained cells are charged.

Use little-endian two's-complement counter vectors. Construct $h-1,h+1$ by the five-gate addition recurrence with constant vectors $-1,1$. For each row $j$ form $e_j=[j=h-1]$ by the three-gate equality fold, and select every top-row bit by the AND/OR fold over all $j$. The dummy row at $h=0$ is zero. For each path position $i$ compute $[i=\mathrm{length}]$; a left child replaces that position by zero and a right child by one, using one MUX for each output bit. Increment the child length by the same adder. For every row compute both $[j=h-1]$ and $[j=h]$ and perform the two branch-conditioned MUX writes, with right replacement first and left replacement second. These masks are disjoint. Finally select the two counter updates or the old counter according to PAIR, leaf or PAD. Recorded top rows refer to values before these writes. Implement a recorded/public-address match as the equality of all $H+w$ path/length bits, then the active/beta ANDs and the two OR folds. No expression tests a private bit to choose a control edge. Sharing a previously computed signal is a literal operand reference; a new signal receives its own initialized cell and encoded reference.

For this expansion, writing each constant row/counter bit by a projection gate, the exact public Boolean count is

$$
\begin{aligned}
C_{\rm init}&=(H+1)(H+w)+w,\\
C_{\rm token}&=(H+1)(4H+10w+2)+3Hw+17w+2H+5,\\
C_{\rm match}&=3(H+w)+4,\\
\mathcal G&=C_{\rm init}+NC_{\rm token}+NKC_{\rm match}+3w.
\end{aligned}
$$

The last $3w$ computes the terminal height equality. The two constant cells themselves are initialized by separate material writes. The token count consists of five token gates, $10w$ height-update gates, $3w(H+1)$ top masks, $2(H+w)(H+1)$ top-bit folds, $3Hw$ child-position masks, $2H$ child MUXs, $5w$ child-length gates, $(H+1)(2+3w+2(H+w))$ row-update gates and $2w$ height MUXs. Each match uses its complete equality, two ANDs and two ORs. These exact expressions are bounded by (60.6): the token count is below $50(H+1)(H+w+1)^2$, each match below $20(H+w+1)$, and initialization/terminal work fits the remaining $50N(H+1)(H+w+1)^2$ allowance. Thus the total bound concerns the fully expanded gates, including unused arithmetic arms and constant writes, rather than an unspecified word operation. The width condition is substantive: a discarded $h-1$ can be $-1$, a discarded $h+1$ can be $H+1$, and a leaf-child length can be $H$. All are strictly inside the signed range at the stated $w$. The computation uses their bit values only, and no negative temporary becomes a seek address.

Here is a reversible cursor-save routine using only the existing primitives. Borrow the actual source port and, when separately stored, its original public interval-descriptor port; the actuator's code, cache, saved positions and latches use its separately constructed ports. No original private latch is used. The source packet can lie at a nonzero arena offset. Copy the original descriptor's complete finite address/length fields into an apparatus tape by actual `RD/AppendWord` work under the same lock, saving and restoring that descriptor port by the cursor routine below. These fields name the original constructed interval and its $2N$ fixed bits, not its private active length or a newly chosen source. The copied literal $U(b)$ then drives ordinary `Seek(source,U(b))`; copying all $2N$ bits uses fixed loop bounds. Thus this compiler does not obtain a source origin from a free integer or assume that the original packet starts at index zero. The descriptor is read only, has no new public output, and its copy, save/restore, reference and version binding are charged. Apply the following routine separately to each borrowed port. On a private apparatus tape append a public separator. While the source head is not at $L$, execute `RD(source); ML(source); Append(save,1)`; append a terminal zero when the boundary test succeeds. It constructs $U(h)$ for the original head distance $h$ without reading a source bit into public control. Ordinary 0/1 have the same successor. Apart from positioning the save tape, this takes $5h+7$ occurrences including its separator. Copy all $2N$ bits from the actual current interval by fixed-address reads/writes; its existing descriptor, or a complete paid origin/descriptor scan, supplies the starting position. No source data cell is written.

Before unlock, run `Home(source)`, position the saved $U(h)$, and for each leading 1 execute `RD(save); MR(source); MR(save)`, reading the terminal zero once. This restores the original source head, including the case $h=0$ at $L$. Locating the latest saved block can itself be done by `Tail(save); ML; RD(0); ML`, then `RD; ML` across the leading ones until the public separator, followed by `MR`. Its cost is $2h+6$ when entered at the right marker. If the source head is at distance $q$ before restoration, save plus restore costs $10h+2q+15$, apart from initial save-tape positioning, lock/unlock and the actual fixed input-copy work. All these additional occurrences append only actuator receipts. Original source ownership and availability are returned before the next original service. Both borrowed cursors and their symbols are restored; all other original cursors, latches, control, receipt append/read heads and fence counter remain untouched.

Proof. The Boolean instructions are the displayed recurrences of PR57.5, expanded in a public loop order. The pending-address invariant in Theorem60.2 therefore applies to their actual bits. Each `Emit` writes the complete truth table and all four unary references, including zero operands, through `AppendWord`; public unary increments construct the fresh reference. Thus there is no assumed gate list or reference allocator. Source copying reads the same committed block under the lock and initializes the input wires used by this very program. During cursor saving the source head moves left once for each appended leading 1. During restoration it moves right exactly that many times from $L$. Only moves affect the source head and only reads/moves touch its data interval. Consequently its symbols and cursor are exactly restored. The separately routed receipt side effect preserves every original fence and closed-cut numeral; it is not a renumbering of an interleaved single chain. Restored source state, ownership and unchanged original control establish the entry condition for the next original routine. Induction using PR57.L4 retains all original archive fields and actual copies, rather than recomputing them from actuator time. $\square$

**Proposition 60.11 (finite tape execution and catalog prices).** Let $\mathcal G$ be the actual number of generated flag gates, $\mathcal G\le G_{\rm flag}(H)$, and $R=2+2N+\mathcal G$. All four gate references are less than $R$. The complete instruction length has the concrete bound

$$
B_{\rm flag}=1+\sum_{g=1}^{\mathcal G}(13+d_g+a_g+b_g+c_g)
\le1+\mathcal G(13+4R).
\tag{60.19}
$$

The interpreter can keep four append-only field-cache tapes and four public descriptor tapes. Before copying a field, position its descriptor tape at its existing right marker by `Tail`, then execute `Base` on its cache, appending a separator and the actual resulting $U(b)$ to its descriptor tape. Copy every field bit by `RD(code); EX(cache); WR(cache,bit); MR(cache); MR(code)`, including its terminal zero. Position its descriptor's latest block by the paid reverse separator scan of Lemma60.10, then execute the ordinary `Seek(cache,U(b))`. Its head is now at the actual newly cached field; the ordinary workspace seek consumes that literal field. Private operand latches survive these public scans exactly as in PR57.5. All previous fields/descriptors remain constructed. This uses the original gate encoding and interpreter operations; the reverse scan merely makes its allowed descriptor positioning explicit.

Let $A_0$ count the apparatus ordinary cells already constructed before this compiler version, excluding its constant boundary/control foundation. Put $M=A_0+\mathcal G(R+1)$. Each cache has at most $M$ cells, and each cached-base descriptor has magnitude at most $M$. The total ordinary cells after code, workspace and these eight tapes, with input-copy/save tapes separately added, are bounded by

$$
A_{\rm flag}\le A_0+B_{\rm flag}+R+4\mathcal G(R+1)
 +4\mathcal G(M+2).
\tag{60.20}
$$

Their gate-interpreter core count, including all Base scans, field copies, descriptor positions, operand/result seeks and the terminal header/exit, satisfies

$$
E_{\rm flag}\le200\mathcal G\bigl(M+R+10\bigr)+2.
\tag{60.21}
$$

These are bounds for this particular deliberately inefficient interpreter, not a native one-tick Boolean model. Code writes cost $3B_{\rm flag}$ append occurrences before their actual generator reads, frame/reference creation and public arithmetic; workspace allocation and all input copies are additional. A generator traverses the finite expression forest in the order specified in Lemma60.10, storing its frames and references and emitting each full record. Its work is the sum of PR57.D9's actual `Base`, `Allocate`, unary increment/copy, frame push/pop and `AppendWord` event words for those finite visits. This sum, together with (60.21) and the source-cursor routine, gives a total finite classical price for a compiler version; it is not replaced by $\mathcal G$. Public parameter arithmetic, all original services and record copies are added by the same disjoint event recurrence. There is no history-independent bound on arbitrary effective policy/parameter-supply computation.

For an interaction run with common exponent set of size $J$, its literal local catalog has $2FJ$ signed wire entries: $2KJ$ phase entries and $2(K-1)J$ hopping entries. Each entry specifies its public wire, kind, sign and dyadic exponent, with its exact matrix (60.2). Its control description is installed by finite bit writes and remains in the control/tape storage coordinate. The endpoint descriptions and every entry are retained material. Preparation adds the root-to-mode wires it actually uses, their signed angle catalogs, the bit flip, balanced gate and fixed phase conjugations; these are separate from the $2FJ$ interaction entries. A reference qubit is one of the $K+1$ constructed/retained modes, and a reference preparation/effect is charged in $G_P,G_R$ and their descriptions. No unknown-state reference attachment is implemented by this catalog.

Proof. Record length is PR57.05. There are at most $\mathcal G$ new fields on each cache, each of length at most $R+1$, in addition to at most $A_0$ previously constructed cells. Workspace reuse keeps its literal signal references at offsets less than $R$; cache/descriptor offsets are separately constructed by Base and may grow across versions. A descriptor has at most $M$ leading ones, one separator and one terminal zero. This gives (60.20). `Base` costs at most $7M+20$ with its positioning, separator and descriptor-tail positioning (the previous descriptor head is at its last terminal zero); a field copy costs at most $5(R+1)$. Locating its latest descriptor, seeking its cache and then its workspace costs at most $7M+5R+30$. There are four of each per gate, plus 18 header/table occurrences, four data reads/writes and one BF. Their sum is below the allowance in (60.21). Native code installation and generation precede execution and are counted separately, so these bounds omit no instruction supply by treating it as a primitive. All generated forest visits and public loops have finite sealed bounds, and PR57.L1–L3 supplies each visit's finite expanded event word. Sequence adds those words; this proves effective finiteness of the entire producer, including its generator, rather than assuming runtime access to source flags.

Every enabled digit fetch selects one installed entry by public position and sign. Its private enable is only an argument of a finite local quantum transition, never a port/address selector. A catalog entry is a new exact apparatus permission for its full local matrix, including identity on vacuum/double excitation; an equality only up to a scalar phase is insufficient. Catalog construction/control, command digits and their reads, and the quantum events are different charged occurrences. The actual ideal executed angle is therefore exactly the signed sum of all fetched enabled dyadic digits. Since the local generator is the same within a block, commuting its finite digit factors proves its exact commanded block matrix. Rounding affects that angle by the certified $2^{-b}$; a physical departure from a catalog entry instead requires the elementary $\zeta_j$ certificate of (60.12). Neither certificate is a native Clifford Read. $\square$

**Proposition 60.12 (instruction and full-phase finite evidence).** The following independently generated finite calculations instantiate the preceding construction; their scopes are deliberately finite. A Boolean assembler using exactly the five-gate adder, three-gate equality fold and complete three-input truth tables generated flags for every labelled ordered source at caps $H=1,2,3,4,5$. There are respectively $2,6,22,102,550$ sources. Its respective program sizes are $224,985,3017,6806,15029$ Boolean gates, all below (60.6). Every output address/beta mask agrees with independent structural preorder recursion. Every complete guarded renewal agrees with the same-address born-child set and with (60.7), including unchanged refused sources and alpha-to-beta steps with unchanged domain.

A separate primitive-routine calculation also checked 1,696 source/descriptor cursor cases at caps $1,2$, with block offsets $0,1,2,3$ and every head position on the two constructed tapes, including $L$ and $R$. The input packet was copied through its actual unary base descriptor; both original tapes and heads were restored and the original receipt/archive fixture retained. The save/restore counts agree with $10h+2q+15$ for each borrowed cursor, excluding the separately counted copy/positioning work.

Separate Boolean expansions of the original full Read and $3N$-slot rho candidate, parser and all-$N$-slot commit MUXs checked those same 682 cap/source cases. The original Read coefficients agree with direct Clifford multiplication; complete candidate tokens and whole guards agree with literal substitution/leaf counting. No rejected candidate was installed. Exhaustive grammar checking at caps $1,2,3$ covers all $4,64,1024$ fixed token words, including premature padding, post-closure active tokens and every valid packet. The original source-action proof remains PR57.T2; these calculations do not manufacture original replies from a quantum response.

Literal programs of (PR57.05) were executed by a standalone tape interpreter for all eight valid sources at $H=1,2$, using actual `RD/WR/ML/MR/EX/BF` operations, full field copies, `Base`, descriptor scans and `Seek`. The tape lengths are respectively 61,296 and 1,203,360 instruction bits. The respective interpreter-only core counts are 62,748,306 and 5,648,797,037. Including the test's literal code writes, workspace/input material, cursor save/restore, flag extraction and 16 tape boundary pairs gives 63,060,395 and 5,654,873,903 core occurrences, with fee twice the count, and 4,552,468 and 404,865,959 constructed ordinary cells. Its additional receipt counts equal those complete core counts. These figures concern that explicitly stated standalone initialization, not the complete original runtime or a minimal compiler. The host executes the shared public opcode/address word once per cap while evaluating all that cap's private source bits in parallel; every source has its own workspace values. `BF` evaluates the specified table for each source, and no private value selects a simulated successor, port or move. This is an exact finite execution of the common interpreter word, not a private-data timing model. Within each cap that opcode/address trace is identical across all sources while the private output flags differ. Original source bytes and cursor are restored and the separate original receipt/archive fixtures are unchanged. The host represents its uniform receipt-symbol run by a run-length count that is never read by simulated control; it does not grant a native integer counter. The generated code is installed by actual bit writes in this check. Native generator/frame construction, complete control bootstrap, original source-service/archive-copy routines, higher-cap interpreter runs and quantum hardware are not exhaustively emulated; their general mathematical construction and prices are supplied by the displayed recipes and the consumed PR57 lemmas.

There is also a certified full-sector digital calculation on the actual accepted source $\rho\langle\beta,\alpha\rangle$, at $H=3$, $a=1,g=16$, $\theta=1/100$, $m=32$, $b=24$, $J=31$. Flags are generated from its authentic packet by the above Boolean assembler. Executing every one of the $13\cdot32\cdot31=12896$ digit slots, of which 2144 have enable one, gives a whole eight-dimensional one-excitation matrix. Its operator error against the complete matrix exponential is bounded by

$$
\left\|U_{\rm digits}-e^{-i\mathsf H_{\rm bank}/100}\right\|
\le\frac{4486959180075231302540271}
{19807040628566084398385987584}
<\frac{255933}{327680000},
\tag{60.22}
$$

where the last fraction is (60.9)'s analytic budget. The reference and both inactive rows remain exact identity rows. This is an absolute full-phase operator bound, not a root response or an eigenbasis comparison.

For a reproducible arithmetic certificate, use outward integer interval arithmetic with scale $2^{100}$. Round an angle by taking the floor of its scaled absolute magnitude and then restoring its sign. Every digit slot is applied, with exact identity entries when its enable is zero. Each used sine/cosine is enclosed by its real degree-13 Taylor polynomial with remainder at most $|\xi|^{14}/14!$. Multiply the actual individual signed dyadic local matrices with outward rounding at every scalar product. Compare with the degree-20 Taylor polynomial of the full $-i\mathsf H_{\rm bank}/100$, enclosing its operator remainder by $2(22/100)^{21}/21!$. If $v$ is the largest resulting real/imaginary component discrepancy interval bound, $\|\Delta U\|\le16v$ bounds the complex eight-by-eight Frobenius norm and hence its operator norm; this gives the first fraction in (60.22). Thus floating roundoff is not an unpriced precision premise.

The larger example of Proposition60.8 has exactly $5,033,600$ blocks, magnitude width 38, $191,276,800$ elementary interaction rotations, and 988 signed wire catalog entries for exponents $-31,\ldots,6$. Its angle budget is $39325/16777216<1/400$. These are independently reproducible integer/rational counts, not an execution of that entire commission. Classical compilation, original service/archives, catalog/control installation, preparation, reference, holds and readout still add their actual prices through (60.16). In particular the qubit count or quantum-rotation count alone is not a total cost estimate.

The finite calculations support the expanded ordinary proofs and their explicit ideal apparatus hypotheses. They supply no current Lean evidence, physical calibration, exact-probability measurement, all-history machine verification, unbounded-clock theorem or complete why-three-dimensions conclusion.

## 60.99 追加锚（本行以下为增补区）


## 61. 两个四叶混色格的显式证书入口

**定义 61.1（具体证书与原供应）。** 对原定义57.1的完整同组成来源、原四值端点、空取得历史与不同实际地址收费，[四叶显式证书卷定理5.1](FIB_ATOM_MIXED_FOUR_LEAF_EXPLICIT_CERTIFICATES.md#5-具体证书有效性的普通证明与精确费用)列全 $(a,b,d)=(2,2,3),(3,1,3)$ 的有限普通上界证书，并证明其对全部同组成负源正确且有限终止。与[混色部分界卷定义9.1及定理5.3](FIB_ATOM_MIXED_ACTUAL_ADDRESS_PARTIAL_BOUNDS.md#9-两个四叶混色格的显式证书)所引下界配合，对每个 $h\ge6$ 含无穷得到费用9、8。

定义57.11已经报告混色四叶 $E=3$ 的有限数值；定理57.3提供两色完整前沿与同组成刚性，定理57.4提供深度独立性，定理57.7已提供真实诊断、缓存和补查的实际取得桥。新增内容归于两张具体上界证书的完整有限证据与普通有效性证明，不归于数值发现、一般操作桥或下界。原一般混色、GeneralH、同一实际整数严格预算及长期几何代数目标保持原域和未解边界。

## 61.99 追加锚（本行以下为增补区）

## 62. Source-owned hard-core Green interactions and population-uniform renewal retention

**Definition 62.1 (commissioned occupation sectors and the original source).** Use the actual PR57 source, INITIAL occurrence, fixed leaf cap $H$, complete candidate guard and chronological original records of Definition60.1. Write $M=2H-1$ for its packet-slot count and $K=2^H-1$ for the address-bank size; neither is the particle count. The inherited occurrence seams, counting measure, root $o=\varepsilon$, $L$, $L_D$, $\phi(p)=2^{-|p|}$ and $\lambda=3-2\sqrt2$ are exactly §§55.1–55.3. For an authentic current domain $D=\operatorname{Pos}(s)$ and a commissioned integer $1\le N\le |D|$, set

$$
\mathcal C_N(D)=\{S\subset D:|S|=N\},\qquad
\mathscr H_{D,N}=\ell^2(\mathcal C_N(D)).
\tag{62.1}
$$

Different equal-valued occurrences remain different sites. The occupation is zero or one at each site. Adjoin three explicitly supplied computational qubits $c,u,v$, initially zero, to §60's $K$ address qubits and reference qubit $r$. Thus the retained quantum carrier has $K+4$ qubits. The additional wires connect $c$ to every public address and to $u,v$; the old parent–child wires are retained. These are computational wires with construction and control prices, not new occurrence seams, distances or displacements. The supplied interaction matrices are still exactly $P$ and $B$ of (60.2) on their full two-/one-qubit spaces. A private classical enable is not a quantum control or a public observation.

Let $b_p=|0\rangle\langle1|_p$ and $n_p=b_p^*b_p$. The target isometry $E_{D,N}$ sends $e_S$ to the bit string occupied at $S$, with $c,u,v,r$ zero and all inactive addresses zero. A separately supplied reference vector has $r=1$ and every other qubit zero; it is fixed by the interaction. A commissioned coherent reference/target input must itself be supplied with its preparation contract. For $N>1$ these two branches have different total excitation numbers; no number-conserving gate is alleged to attach that reference to an unknown input. The default known preparations below need no such superposition.

There are two pair prescriptions, both retaining the original one-body potential:

$$
\begin{aligned}
G^{\rm c}_D(p,q)&=\langle e_p,L^{-1}e_q\rangle,\\
G^{\rm k}_D(p,q)&=\langle e_p,L_D^{-1}e_q\rangle,\\
H^\diamond_{D,N}&=
aK_{D,N}-g\sum_{p\in D}\phi(p)n_p
-\nu\sum_{\{p,q\}\subset D}G^\diamond_D(p,q)n_pn_q,\qquad \diamond\in\{\mathrm c,\mathrm k\},\\
K_{D,N}&=\left.\left[\sum_{p\in D}d_pn_p-
\sum_{\{p,q\}\text{ actual seam in }D}(b_p^*b_q+b_q^*b_p)\right]\right|_{\mathscr H_{D,N}},
\qquad d_o=2,\quad d_p=3\ (p\ne o).
\end{aligned}
\tag{62.2}
$$

Here $a,g>0$ and $\nu\ge0$ are commissioned Hamiltonian parameters, independent of the hidden source and original actor initialization. This $a$ imposes no condition on the original $\mathcal D_2$ actor variable. The notation in (62.2) transports the qubit operators through the occupation isometry. The new charge strength and supported occupation sector are commissioned premises. At $N=1$ the pair term vanishes and the target is literally $aL_D-gM_\phi$ of §60, for both prescriptions. The killed prescription re-solves only the pair coefficients; it does not replace $\phi$ by $\phi_D^0$.

**Theorem 62.2 (literal statistics, full carrier and the same-L pair field).** On the full qubit carrier, $P_p(1,\xi)=e^{-i\xi n_p}$ and $B_{pq}(1,\xi)=e^{i\xi(b_p^*b_q+b_q^*b_p)}$, including their vacuum and double-occupation entries. Consequently their installed one-body generator on (62.1) is exactly the hard-core operator in (62.2). Its diagonal counts inherited exterior and collision killing; it is not the Laplacian obtained by counting only allowed configuration moves. It is not an exterior-power substitution for the literal gates.

For all addresses $p,q$ in the same infinite rooted occurrence tree, let $p\wedge q$ be their longest common prefix and let $d(p,q)=|p|+|q|-2|p\wedge q|$. Then

$$
G^{\rm c}(p,q)=\frac23\,2^{-d(p,q)}+\frac13\,2^{-(|p|+|q|)}.
\tag{62.3}
$$

It is the kernel of the already installed $L^{-1}$, not a new pair-field supplier. For every authentic $D$,

$$
0<G_D^{\rm k}(p,q)\le G^{\rm c}(p,q),\qquad
0<L_D^{-1}\le\lambda^{-1}I,\qquad
0<P_DL^{-1}P_D\le\lambda^{-1}I.
\tag{62.4}
$$

Proof. The generator $b_p^*b_q+b_q^*b_p$ interchanges $10,01$ and kills $00,11$. Exponentiation gives exactly (60.2), including phase one on $11$. Operators at distinct sites commute; a permitted hop has coefficient $-a$ with no ordering sign. Embed $e_S$ into the normalized symmetric sum of the $N!$ ordered distinct-site tensors. Compression of $\sum_{i=1}^N L_D^{(i)}$ to these tensors gives diagonal $\sum_{p\in S}d_p$ and coefficient $-1$ for each allowed single-site replacement. A replacement onto an occupied site is projected out; its inherited diagonal contribution remains. This proves the operator correspondence and, from §55's gap, $K_{D,N}\ge N\lambda I$. The normalized symmetric embedding is a proof device, not a carrier copy or a preparation permission.

For (62.3), fix $q$. At each nonroot $p\ne q$, the distance term satisfies $3f(p)-f(p^-)-f(pL)-f(pR)=0$. At $p=q\ne o$ its value after applying $L$ is $3(2/3)-3(1/3)=1$. The depth term is harmonic off the root. When $q\ne o$, the distance term's root residual is $-(1/3)2^{-|q|}$, canceled by the depth term's root residual $+(1/3)2^{-|q|}$. When $q=o$, both terms combine to $2^{-|p|}$ and the root residual is one by (55.5). Each column is square summable: split into the finitely many branches meeting the root-to-$q$ path and use the geometric sum $\sum_{j\ge0}2^j4^{-j}$. Hence $LG^{\rm c}(\cdot,q)=e_q$ in $\ell^2$. The positive gap makes this column $L^{-1}e_q$ uniquely.

For the entrywise comparison use $L=3(I-P)$, with $P=I-L/3$ the nonnegative substochastic/compression matrix of §55. The parent–child adjacency has norm at most $2\sqrt2$: sum $2|f(p)f(pz)|\le2^{-1/2}|f(p)|^2+2^{1/2}|f(pz)|^2$ over the two children. Hence $\lambda I\le L\le(3+2\sqrt2)I=(6-\lambda)I$, and $\|P\|\le1-\lambda/3<1$. The inverse is $\frac13\sum_{n\ge0}P^n$. Compressing after every factor retains only paths staying in $D$; compressing the infinite inverse retains all paths with endpoints in $D$. All terms are nonnegative and some finite path connects every two sites. This proves the entrywise assertions. The operator inequalities follow directly from the gap, and do not assert that an arbitrary entrywise comparison is an operator comparison. $\square$

**Theorem 62.3 (all-source extensive stability in the commissioned sectors).** For every authentic finite $D$, every supported $N$, either pair prescription and every $f\in\mathscr H_{D,N}$,

$$
\langle f,H^\diamond_{D,N}f\rangle
\ge \left[a\lambda-g-\frac{\nu}{2\lambda}\right]N\|f\|^2.
\tag{62.5}
$$

The same bound holds for the infinite common operator on $\ell^2(\mathcal C_N(\{L,R\}^*))$. The constant is independent of the source, its cap, its irregular boundary and $N$. It is an extensive bound for this hard-core/Green law, not for unrestricted product-state attraction.

Proof. For a realized occupation $S$, put $z_p=\mathbf1_{p\in S}$. On the same $D$ and the same pair kernel,

$$
\sum_{\{p,q\}\subset S}G^\diamond_D(p,q)
=\frac12\left[z^*G^\diamond_Dz-\sum_{p\in S}G^\diamond_D(p,p)\right]
\le\frac{N}{2\lambda}.
\tag{62.6}
$$

This uses $\|z\|^2=N$, the positive diagonal and the operator bound (62.4). It does not combine separately attained estimates on different realizations. Also $0<\phi\le1$, so the one-body attraction is bounded by $gN$. Apply the kinetic bound proved inside Theorem62.2. The infinite kinetic operator is bounded and has the same compressed tensor proof; (62.6) applies to each finite occupation. Thus its pair multiplier is bounded for each fixed $N$ and the conclusion extends by density. These estimates prove lower boundedness, not a negative ground state, its attainment or precompactness of near-minimizers. $\square$

**Theorem 62.4 (authentic renewal: common compression and exact killed update).** Let a whole-rho candidate actually be accepted, let $D'=\operatorname{Pos}(\rho s)$, and let $\mathcal B$ be the authentic old beta-leaf mask. Let $J_Ne_S=e_S$ be the unchanged-bank injection. Old addresses and occupations retain their identities. For the common prescription,

$$
G^{\rm c}_{D'}|_{D\times D}=G^{\rm c}_D,
\qquad
J_N^*H^{\rm c}_{D',N}J_N=H^{\rm c}_{D,N}.
\tag{62.7}
$$

Equality of this compression does not give $H^{\rm c}_{D',N}J_N=J_NH^{\rm c}_{D,N}$. Born-child hopping survives in the latter difference. In the one-particle case it is exactly (60.7); in an occupation it moves each occupied beta leaf to each empty born child with coefficient $-a$.

For the killed prescription let $U:\mathbb C^{\mathcal B}\to\ell^2(D)$ have columns $e_p$, $p\in\mathcal B$, and put $G=L_D^{-1}$. If $\mathcal B$ is empty the update is zero. Otherwise

$$
\begin{aligned}
G^{\rm k}_{D'}|_{D\times D}
&=\left(L_D-\frac23UU^*\right)^{-1}\\
&=G+GU\left(\frac32I-U^*GU\right)^{-1}U^*G.
\end{aligned}
\tag{62.8}
$$

All inverse factors displayed here exist and the increment is nonnegative entrywise. For an old occupation basis vector,

$$
\langle J_Ne_S,H^{\rm k}_{D',N}J_Ne_S\rangle
-\langle e_S,H^{\rm k}_{D,N}e_S\rangle
=-\nu\sum_{\{p,q\}\subset S}
\left[G^{\rm k}_{D'}(p,q)-G^{\rm k}_D(p,q)\right].
\tag{62.9}
$$

Proof. TM22–23 and §58.2 give precisely two new children at each old beta leaf. Old diagonals, old seams and the root field are unchanged. This proves (62.7), since a new occupied site is absent in $J_Ne_S$. It also identifies the nonzero born hopping rather than asserting intertwining.

In old/new site blocks, $L_{D'}$ has old block $L_D$, new block $3I$, and two $-1$ entries from each beta leaf to its children. The old Schur complement is therefore $L_D-(2/3)UU^*$. Positivity of $L_{D'}$ implies positivity of that complement. The inverse identity in (62.8) follows by multiplying its proposed right-hand side by that complement. Positivity also gives $I-(2/3)U^*GU>0$. Its nonnegative inverse follows from the convergent series in $(2/3)U^*GU$, whose spectral radius is below one. All entries of $G$ are nonnegative, so the increment is entrywise nonnegative. Finally a basis occupation has zero hopping expectation, and every unchanged diagonal cancels in the energy comparison. $\square$

**Proposition 62.5 (jointly realized unbounded-population retention defect).** For each integer $h\ge1$, choose the authentic complete ordered depth-$h$ source with every leaf beta. Its old leaf count is $2^h$ and it has an accepted whole-rho step at public cap $H=2^{h+1}$. Put

$$
S_h=\{p:|p|=h-1\}\ \cup\ \{pL:|p|=h-1\},
\qquad N_h=|S_h|=2^h.
\tag{62.10}
$$

A paid known preparation of $e_{S_h}$ then has, for the killed prescription at this one actual renewal,

$$
\langle e_{S_h},H^{\rm k}_{D_h,N_h}e_{S_h}\rangle
-\langle J_{N_h}e_{S_h},H^{\rm k}_{D_h',N_h}J_{N_h}e_{S_h}\rangle
\ge\frac{\nu N_h}{81}.
\tag{62.11}
$$

For the same occupation and common prescription the expectation difference is zero. Thus a cap-/population-independent absolute tolerance on retaining old-state energy through the killed renewal cannot tend to zero for $\nu>0$. The extensive lower bound (62.5) remains valid.

Proof. The nonnegative series for the old inverse gives $G(p,p)\ge1/3$ and $G(p,p^-)\ge1/9$ for each beta leaf $p$. Expansion of (62.8), keeping just its first nonnegative term and the column of that very beta leaf, gives

$$
G'(p,p^-)-G(p,p^-)
\ge\frac23G(p,p)G(p,p^-)
\ge\frac{2}{81}.
\tag{62.12}
$$

The $2^{h-1}$ distinct selected parent/left-leaf pairs all belong to the one occupation $S_h$. All other pair increments are nonnegative. Summing in (62.9) proves (62.11). Every tree, mask, occupation and successor used here belongs to that same realization. This is not a combination of individually optimal states, and it uses no new source copy, reset or sampling. The paid source preparation and population are part of this explicitly growing family, rather than free resources at fixed $H$. $\square$

**Theorem 62.6 (fixed-N infima and their recovery quantifiers).** Fix $a,g,\nu$ and a finite integer $N$. On the infinite occurrence tree let $H_N^{\rm c}$ be the common operator of (62.2), and put $m_N=\inf_{\|f\|=1}\langle f,H_N^{\rm c}f\rangle$. For any original nonempty finite source $t$, let $D_j=\operatorname{Pos}(\rho^jt)$ as in §55. Once $|D_j|\ge N$, let $m_{j,N}^{\rm c},m_{j,N}^{\rm k}$ be the finite normalized infima. Then

$$
m_{j,N}^{\rm k}\ge m_{j,N}^{\rm c}\ge m_N,
\qquad
\lim_{j\to\infty}m_{j,N}^{\rm c}
=\lim_{j\to\infty}m_{j,N}^{\rm k}=m_N.
\tag{62.13}
$$

More precisely, for every $\epsilon>0$ there is a unit vector $f$ with finite configuration support and $\langle f,H_N^{\rm c}f\rangle\le m_N+\epsilon/2$. For each $t$ there is a finite $j_0$ such that for every $j\ge j_0$ its identical-address embedding $f_j$ is defined and

$$
\langle f_j,H_{D_j,N}^{\rm c}f_j\rangle
=\langle f,H_N^{\rm c}f\rangle,
\quad
0\le\langle f_j,(H_{D_j,N}^{\rm k}-H_{D_j,N}^{\rm c})f_j\rangle
\le\epsilon/2.
\tag{62.14}
$$

The vector is selected for fixed $N,\epsilon$, before the tail comparison; it is not an exact state acquired by a Read. These claims contain no strong precompactness or ground-attainment conclusion, and no quantifier uniform in growing $N$ or unbounded clock time.

Proof. The infinite fixed-$N$ operator is bounded, by the kinetic degree bound and (62.6). Finite configuration vectors are dense, hence supply the stated variational recovery vector. The all-source exhaustion in §55 eventually contains every address in its support and their old identities. Zero-extension makes the common expectation exactly equal, including killing. Entrywise domination in (62.4) makes the killed-minus-common pair multiplier nonnegative, proving the inequalities of infima.

For fixed $p,q$, the path expansion proving (62.4) also proves $G_{D_j}^{\rm k}(p,q)\uparrow G^{\rm c}(p,q)$. Indeed each finite path is eventually in $D_j$, and the nonnegative convergent series permits taking its increasing union. Only finitely many coefficients occur in the expectation of the selected $f$. Their differences tend to zero, so choose $j_0$ for their finite weighted sum. This proves (62.14) and the matching limsup, while the common lower bound supplies the liminf.

For actual finite execution each specified prefix $j$ is commissioned at a finite cap at least its largest actual leaf count; the bank and every word are finite. A fixed-cap source may instead refuse further growth. The mathematical family in (62.13) is a comparison of finite supported prefixes, not permission to change a running cap, prepare copies of an unknown source, sample independent histories, or execute a Read after an infinite prefix. The growing occupations in Proposition62.5 are outside the fixed-$N$ quantifier and prevent reversing that distinction. $\square$

**Theorem 62.7 (a derived density phase with three retained auxiliaries).** Let $p\ne q$ be two public address wires, and put

$$
F_{ab}=P_a(1,\pi/2)P_b(1,\pi/2)B_{ab}(1,\pi/2).
\tag{62.15}
$$

Products act rightmost first. This is the full matrix which swaps $01,10$, fixes $00$, and negates $11$. Let $C_{cp}$ be the chronological word

$$
F_{cu},\ F_{cp},\ F_{cv},\ F_{cu},\ F_{cp},\ F_{cv},\ F_{cp}.
\tag{62.16}
$$

On $u=v=0$, it returns both auxiliary bits to zero and acts as $(-1)^{n_cn_p}$ on $c,p$. Define

$$
U_{pq}=B_{qc}(1,\pi/4)\,C_{cp}\,B_{qc}(1,-\pi/4)\,C_{cp}.
\tag{62.17}
$$

On the clean input $c=u=v=0$,

$$
U_{pq}^*P_c(1,\xi)U_{pq}
=e^{-i\xi n_pn_q},
\tag{62.18}
$$

with all three auxiliaries returned to zero and every original state phase preserved. Its expanded chronological word has exactly 89 $P/B$ angle blocks. The reference wire is untouched. The signs and angles in (62.15)–(62.18) describe a real-angle reference, not an exact signed-dyadic catalog or a free inverse.

Proof. A hop of angle $\pi/2$ multiplies each single-occupation swap by $i$. The two phases multiply that swapped excitation by $-i$ and multiply $11$ by $(-i)^2=-1$, proving (62.15) on all four inputs. This is precisely the mature fermionic-swap matrix of Brod–Childs equation(4), consumed from [the matchgate note](../../../Library/QuantumStates/brodchilds2014matchgates.md); it does not change the statistics of the old literal hopping generator.

Track (62.16) on its four clean inputs. With zero or one excitation every swap has sign one and returns the input bits. With $c=p=1$, the occupied pairs are successively $\{u,p\},\{u,c\},\{u,v\},\{c,v\},\{p,v\},\{p,c\},\{p,c\}$. Only the final swap has both endpoints occupied, so it contributes exactly minus one. This proves the clean controlled sign by linearity, including entanglement with every untouched wire.

If $p=0$, the two $C$ factors in (62.17) act as identity and the two $B$ factors cancel. If $p=1$, they act as $Z_c$, and $Z_cB_{qc}(-\pi/4)Z_c=B_{qc}(\pi/4)$ on the single-occupation space. Thus $U$ moves $q=1,c=0$ to $q=0,c=1$ with phase $i$, while fixing the joint vacuum. At this cut $n_c=n_pn_q$ on all four clean input columns. Applying $P_c(\xi)$ and then the explicitly reversed, negated 44-block word returns the complete input with precisely the phase in (62.18). Each $C$ uses $7\cdot3=21$ blocks, so $U$ uses 44 and (62.18) uses $44+1+44=89$. The auxiliaries are shared sequentially between pair words, never measured, projected or reset. $\square$

**Theorem 62.8 (finite private rational coefficients from the actual packet).** At a locked original idle cut, the fixed flag word of Theorem60.2 yields actual address bits $x_p$ and the beta mask. There is a public fixed-order arithmetic word, independent of these bit values, that computes every killed pair coefficient exactly as an unreduced rational with positive denominator. It needs neither a pair oracle, a private-address seek nor a private pivot selection.

For each public address $p$, process the bank from deepest to shallowest. Set absent child pairs to $(A,B)=(1,1)$, put $d_p^x=1+x_p(d_p-1)$, and set

$$
\begin{aligned}
B_p&=A_{pL}A_{pR},\\
A_p&=d_p^xA_{pL}A_{pR}
-x_{pL}B_{pL}A_{pR}-x_{pR}B_{pR}A_{pL}.
\end{aligned}
\tag{62.19}
$$

Then process root to leaves, retaining unreduced numerator/denominator pairs $C_p=N_p/D_p$:

$$
C_o=B_o/A_o,
\qquad
C_p=B_p/A_p+x_p C_{p^-}(B_p/A_p)^2\quad(p\ne o).
\tag{62.20}
$$

For $w=p\wedge q$ the required all-bank output is

$$
\gamma_{pq}=x_px_q C_w
\prod_{w\prec z\preceq p}\frac{B_z}{A_z}
\prod_{w\prec z\preceq q}\frac{B_z}{A_z}.
\tag{62.21}
$$

It is zero for an inactive endpoint and is $G_D^{\rm k}(p,q)$ otherwise. The common prescription uses (62.3) at the same public endpoints and masks. In neither prescription is a computed coefficient a public source reply.

Proof. Extend $L_D$ to the full bank by identity on inactive sites. Its active edge to child $z$ is $-x_z$. Downward closure implies that an inactive parent has no active descendant. Eliminating children gives pivot $t_p=A_p/B_p=d_p^x-\sum_{z=pL,pR}x_z/t_z$. An active nonroot pivot is at least two by bottom-up induction, and the active root pivot is at least one; an inactive pivot is one. Thus all denominators are positive. More explicitly, put $T_{p,p^-}=x_p/t_p$ and all other entries zero. The extended matrix is $(I-T)^*\operatorname{diag}(t_p)(I-T)$: each off-diagonal is $-x_p$, and its diagonal is $t_p+\sum_{z=pL,pR}x_z/t_z=d_p^x$. Since $T$ is strictly triangular, $(I-T)^{-1}$ is its finite path sum. Multiplying this sum, $\operatorname{diag}(t_p^{-1})$, and its adjoint gives (62.20) for the diagonal and (62.21) for the two common-ancestor paths. This is direct finite factorization of the actual installed $L_D$, not an assumed inverse supplier.

Here are finite widths and Boolean recurrences for this word. Let $B_0$ bound the bit lengths of all supplied rational parameter numerators/denominators, including interval lengths, $m$, and public coefficient approximants. Let $b,k$ be the digit bounds of Theorem62.9. A sufficient signed workspace width is

$$
W=64K(H+1)+8(B_0+b+k+1).
\tag{62.22}
$$

No fraction reduction is necessary. If $s_p$ is the size of the public bank subtree rooted at $p$, (62.19) gives $1\le A_p,B_p\le3^{s_p}$. Expanding (62.20) as
$N_p=B_pA_pD_{p^-}+x_pN_{p^-}B_p^2$, $D_p=A_p^2D_{p^-}$
shows that the maximum numerator/denominator bit length increases by at most $4K+2$ per level. Multiplying the two public paths in (62.21) adds at most $4KH$ bits. Parameter multiplication and scaling by $2^b$ add at most $4B_0+b+2$ bits. All products, discarded subtraction arms and restoring-division trials therefore lie strictly inside the signed range of (62.22), with two spare bits.

Use PR57.07's five-gate full adder, complement-plus-adder subtraction, PR57.08's seven-gate comparison, and a one-gate bit MUX. A schoolbook product forms every partial AND bit and adds every shifted row; fewer than $10W^2$ Boolean gates suffice, including unused high bits and copies. Every division is the $W$-step recurrence, from most significant numerator bit downward,

$$
z=2r+n_i,\quad e=[z\ge d],\quad r'=\operatorname{MUX}(e,z-d,z),
\quad q'=2q+e,
\tag{62.23}
$$

with zero initial remainder/quotient. Both subtraction arms and the complete comparison execute regardless of $e$. Since $0\le r<d$, the recurrence maintains the Euclidean division invariant and ends with the exact quotient and remainder. No private bit selects a code edge. Constants, copies, masks, additions, multiplications and division all expand into literal truth-table records (PR57.05). A sufficient bound on new Boolean gates for (62.19)–(62.23), all coefficient digits and all endpoint masks is

$$
G_{\rm pair}\le
100W^2\left[20K+\binom K2(8H+20)+1\right].
\tag{62.24}
$$

Indeed (62.19) uses at most ten integer products/masks/additions per node and (62.20) at most eight, so their combined allowance is $20K$. Each pair uses at most four products per path level plus its parameter products, mask and one restoring division. Each such operation, including its constant/copy bits, is below the allowance $100W^2$; grouping the two node recurrences and the path operations gives the displayed deliberately loose bound. The flag gates are additional. Every gate's material record, operand references, field fetches and tape execution have their separate prices in Proposition62.11. $\square$

**Theorem 62.9 (both actual signed-dyadic evolutions).** Fix a supported maximum $N_*$, public nonnegative rational parameter approximants $\widetilde a,\widetilde g,\widetilde\nu$ with rational bounds $0\le\widetilde a\le\bar a$, $0\le\widetilde g\le\bar g$, $0\le\widetilde\nu\le\bar\nu$, a finite checkpoint list, and public rational intervals $\theta_\ell\ge0$. For an interval put $\delta=\theta/m$, $m\ge1$. One reference product slice consists of the $K$ diagonal phase slots with angles $\delta(\widetilde a d_p-\widetilde g\phi(p))$, the $K-1$ inherited seam slots with angles $\delta\widetilde a$ in §60's three matching colours, and every public unordered bank pair in a fixed order. The pair word is (62.18) with

$$
\xi_{pq}=-\delta\widetilde\nu\gamma_{pq}
\quad\hbox{or}\quad
\xi_{pq}=-\delta\widetilde\nu G^{\rm c}(p,q),
\qquad \text{enable }x_px_q.
\tag{62.25}
$$

All one-body enables remain the authentic $x_p,x_q$ of §60. The pair word's enable multiplies every constituent rotation, including all fixed-angle rotations. There are exactly

$$
F_*=2K-1+89\binom K2
\tag{62.26}
$$

angle blocks per slice. Choose public $k\ge2$ with
$2^k>2+T(3\bar a+\bar g+6\bar\nu)$, where $T$ bounds the total commissioned comparison time, and put $J=b+k$, $b\ge0$. Compute each fixed $\pi/2,\pi/4$ angle effectively and round it to a signed dyadic within $2^{-b}$. Compute killed rational digits by (62.23), and common digits by the rational (62.3); round each coefficient angle within $2^{-b}$. Every block scans all $J$ magnitude digits. Every enabled digit invokes the already supplied literal $P$ or $B$ catalog matrix of signed angle $\pm2^{j-b}$. A disabled digit invokes its charged identity matrix. The public elementary angle cap is therefore $2^{k-1}$, with enable amplitude in $\{0,1\}$; a common finite run uses the maximum of these caps across its commissioned intervals. This is part of the supplied finite catalog contract, not an inferred physical control-amplitude capability.

Thus both prescriptions have finite actual evolutions from the same original packet and the supplied P/B vocabulary. The matrices executed at finite accuracy are the dyadic products, rather than the real-angle reference in Theorem62.7.

Proof. The width covers the fixed constants, diagonal angles, edge angles and pair angles, since (62.4) gives $G_D^{\rm k}(p,q)\le\lambda^{-1}<6$. The rational quotient from (62.23) supplies the floor of the scaled magnitude. A fixed effective enclosure of $\pi$ follows, for example, from the classical identity $\pi=16\arctan(1/5)-4\arctan(1/239)$ and alternating-series remainders. Its finite rational terms, additions and required digit determination are paid public computation. When an enclosure crosses a digit threshold, a certified overlapping bracket of width below $2^{-b}$ followed by rational rounding still gives the required angle error; no exact equality test on $\pi$ is needed. No catalog entry has an alleged exact-dyadic $\pi$ angle.

Digits of a block use the same generator and hence commute; their product is the exact literal matrix at the written dyadic angle. Negating and reversing a word constructs and executes its inverse by all its actual slots. In particular the last 44 blocks of the pair word are charged, and the same rounded constants can be used in reverse. The private enable affects only its finite local matrix, never its wiring, successor or timing. The central pair sign is the public minus sign even when its magnitude is zero; diagonal signs depend only on public depth and supplied parameters. No computed private zero or sign chooses a catalog row. A zero or inactive pair retains all 89 blocks and all $89J$ digit slots. Public original responses can select the next finite commission, but private flags cannot select a public schedule. The new classical signals have no callable actor, verifier or consumer port. $\square$

**Theorem 62.10 (full retained-state finite error, leakage and clock budget).** Put

$$
\overline A=(6\bar a+\bar g+3\bar\nu)N_*,
\qquad
\Delta_A=(6\delta_a+\delta_g+3\delta_\nu)N_*.
\tag{62.27}
$$

Here the coefficient errors are certified absolute errors; exact rational inputs permit all three to be zero. For a finite history of actual accepted/refused whole-rho requests and original Reads, use the just-committed prescription at each idle interval, hold the entire carrier through service and compilation, and keep the carrier unchanged at renewal. If $U_{\rm hist}^\diamond$ is the exact finite time-ordered occupation propagator with these injections, the actually ideal dyadic circuit on a supplied clean supported input obeys, at every completed checkpoint,

$$
\eta_{\rm circ}\le
\sum_{\ell\text{ in prefix}}\left[
\frac{\overline A^2\theta_\ell^2}{2m_\ell}
+F_*m_\ell2^{-b_\ell}+\theta_\ell\Delta_A\right].
\tag{62.28}
$$

This is a norm bound against the complete target vector with its phases, including a separately supplied reference branch. Every imperfect auxiliary component remains in the full carrier. No clean-subspace projection or auxiliary reset is used between pair words, slices, source events or checkpoints.

Suppose additionally that the supplied preparation has norm error $\eta_P$, actual elementary gates have full-carrier unitary error bounds $\zeta_j$, all actual locking/service/retention holds have accumulated full-carrier unitary error $\eta_H$, and actual comparison intervals have discrepancy sum $\eta_\tau$. Then the state bound gains

$$
\eta_P+\sum_j\zeta_j+\eta_H
+(6a+g+3\nu)N_*\eta_\tau.
\tag{62.29}
$$

No independence of errors is assumed. At a checkpoint the auxiliary-excitation amplitude norm is at most the total bound $\eta$; its mathematical probability is at most $\eta^2$. For any separately commissioned terminal effect $0\le F\le I$, the ideal/actual probabilities differ by at most $2\eta$ for unit inputs. Neither number is an acquired exact probability Read.

Proof. On the supported occupation sector the diagonal group has norm at most $(3\bar a+\bar g)N_*$. Each matching hopping group has norm at most $\bar a N_*$: its disjoint local generators have eigenvalues $0,\pm1$, and at most $N_*$ of their pairs can have single occupation simultaneously. The pair multiplier has norm at most $\bar\nu N_*/(2\lambda)<3\bar\nu N_*$. Thus the sum of group norms is bounded by $\overline A$. The first-order Hermitian product bound used in Theorem60.4, from Childs–Su–Tran–Wiebe–Zhu, gives the first term of (62.28); this is its application to the literal occupation groups, not new product-formula theory. Duhamel with the same fixed coefficients gives $\Delta_A$.

For each pair block, compare the complete 89-factor dyadic word with its real-angle word on the full $2^{K+4}$ carrier. Each local generator has norm at most one there, so its angle perturbation contributes at most $2^{-b}$. Full-space unitary telescoping gives $89\,2^{-b}$ without assuming that the perturbed input to any later factor is clean. The exact reference word returns auxiliaries to zero at block endpoints and implements (62.18), so applying this full-space estimate successively compares with the clean ideal target. The one-body factors use the same estimate. This proves the second term and, importantly, prices all imperfect components rather than deleting them.

At a switch the same addressed occupation is retained. This gives an isometry, even though the killed old energy changes and even though the common generator does not intertwine. At a refusal/Read no actuator version changes. Telescope along the finite actual history. The same argument handles arbitrary correlated gate errors and holds on the whole retained carrier, including leakage. The clock term follows from the source-independent target norm bound; comparison intervals are not native receipt counts or calibrated physical durations. Finally the target has zero auxiliary components, so their orthogonal component in the actual vector is bounded by its norm difference, without performing a projection as an action. The effect estimate follows by inserting the ideal vector in the two quadratic factors.

For any public rational accuracy $\epsilon>0$, finite checkpoint count $L\ge1$ and time bound $T$, one finite choice is $m=\max\{1,\lceil2\overline A^2T^2/\epsilon\rceil\}$, together with $2^b\ge4LF_*m/\epsilon$. These give at most $\epsilon/4$ each for the first two accumulated terms, since $\sum\theta_\ell^2\le T^2$. Supply coefficient enclosures with $T\Delta_A\le\epsilon/4$ and the entire preparation/gate/hold/clock sum at most $\epsilon/4$. The total is then at most $\epsilon$. Each required increase in $m,b$ changes the actual words, catalog, fetches and retention in (62.32); accuracy is not free. Zero-time intervals may retain zero interaction slots by a public choice. $\square$

**Proposition 62.11 (complete native prices of the derived words).** Use §60's separately owned actuator receipt chain, producer lock and restored original cursors. Every added classical operation is expanded into the existing PR57 finite tape primitives. Let $\mathcal G$ be the actual number of emitted flag, coefficient, division, enable and preparation-check Boolean gates, and let $B_{\rm in}$ count additional material input bits used as operands, including any supplied occupation array and parameter bits. Put $R=2+2M+B_{\rm in}+\mathcal G$ for the two constant cells, authentic input cache, those additional operand cells and fresh signal cells. Every input cell has its actual ingress/copy and initialization word. An exact code-size bound is

$$
B_{\rm code}=1+\sum_{g=1}^{\mathcal G}(13+d_g+a_g+b_g+c_g)
\le1+\mathcal G(13+4R).
\tag{62.30}
$$

Every record is emitted by actual `AppendWord`, all four unary operand fields are fetched, and each gate's interpreter word has exactly the count (PR57.06), with its actual tape-head positions and complete descriptor positioning. In particular $\mathcal G$ is not the native event count.

Let $\omega_C$ denote the concatenation of the following finite primitive words in their actual chronological order: apparatus control/boundary construction; original private source ingress, complete source services and every original archive/copy/output actually commissioned; lock and authentic descriptor/input copy with both borrowed cursor saves/restorations; initialization and generation of the flag expressions in Theorem60.2 and the arithmetic expressions (62.19)–(62.23); their entire interpreters; public parameter and $\pi$ arithmetic; every coefficient/angle/enable reference and instruction write; every wire/catalog description write; every digit and enable fetch and Boolean AND; known preparation data/support checks; holds' classical control; terminal output/framing. Each of these words is given by PR57.3–57.5, PR57.D9, Lemma60.10 and Proposition60.11, applied to the displayed finite expressions and bounds. No private pivot, discarded arm, disabled slot, field-cache positioning or original refused candidate is omitted.

Define $E_C=|\omega_C|$. More explicitly, Boolean interpreter contributions are $\sum_g I(g)+2$ per program, where $I(g)$ is (PR57.06); instruction writes contribute $3B_{\rm code}$ plus the generator's actual frame/reference/arithmetic words. The latter are the PR57 depth-first finite-forest traversal, allocating one fresh result and emitting each complete record after its children. Sequence adds word lengths, a public unary loop sums its body at every stored digit, and each `Home`, `Base`, `Seek`, `Allocate`, `Append` is counted by its already supplied primitive recurrence. This defines an effective exact integer from the material input and descriptors, rather than an unspecified charge for a word operation. For an interpreter with $A_0$ already constructed apparatus cells, the explicit upper bounds (60.20)–(60.21) apply with this $\mathcal G,R$; generator/input/catalog work is additional. They permit reuse of classical signal cells only after every current signal is rewritten; erased material remains counted.

The interaction wiring has $K+3$ phase endpoints and $2K+1$ hop wires: the $K-1$ inherited seams, $K$ center/address wires and the two center/auxiliary wires. A common $J$-digit catalog therefore has

$$
2(3K+4)J
\tag{62.31}
$$

signed kind/wire/exponent entries. Its full endpoint and control descriptions are constructed and retained. A word description stores its kind, public endpoint ordinals, sign, scale, $J$ magnitude bits and the unary enable/bit-field addresses. Their complete lengths are the sums of these literal fields, and their construction uses `AppendWord`; computed private angle bits still require their actual reads and writes. Any preparation/reference wire or fixed gate not in (62.31) adds its own description and construction slots.

Here is one explicit serial fetch word, including the public descriptions. Store every instruction field in the literal unary-reference/framed-bit format of PR57.03 and PR57.05. At each digit, copy and position the complete bit and enable reference fields by the four-cache/descriptor routine of Proposition60.11, then execute `Seek(workspace,U(bit)); RD(workspace,0)`, `Seek(workspace,U(enable)); RD(workspace,1)`, and one `BF(AND)` into latch 3. Each seek uses its actual field head and current workspace head; its count is $2h+3v+3$, with the field's complete positioning counted separately. The operand latches survive these public scans. Consume the complete kind, endpoint, sign and exponent fields of the scheduled catalog entry by their paid `RD; MR` scan, driven by their constructed public lengths. The corresponding fixed local catalog row then executes one quantum occurrence with latch 3 as enable. No private bit chooses that row or an endpoint. Its finite installed control row and wire descriptions were already constructed bit by bit; their control size is in $b_{\rm ctl}$. For later use, reposition these sealed descriptions by their actual unary descriptors and the same paid seek routine. All descriptions, source bits and discarded digit slots remain retained. Literal code-bit installation contributes three append occurrences per bit; when a material bit string is copied, its additional source `RD; MR` pair makes the complete `AppendWord` cost five per bit. Those reads and moves belong to $\omega_C$ as well.

This recipe is applied on every one of the $G_Q$ slots, including coefficient-zero, enable-zero and magnitude-zero slots. A supplied known-preparation bit is fetched by the same word before its fixed bit-flip slot. Terminal effect descriptions and their output framing are likewise consumed before delivery. Every requested additional idle hold tick is an explicit identity-control `CTL` occurrence with its receipt; classical service ticks already hold the complete carrier. Thus no additional clock interval, preparation/effect visit or catalog/wire fetch is absorbed into an unpriced word operation.


Let $G_Q=\sum_\ell F_*m_\ell J_\ell$ include every enabled and disabled elementary interaction slot, and let $G_P,G_R$ be actual preparation and terminal quantum slots. All $K+4$ qubits are individually constructed and retained. With all holds represented by their actual classical control intervals, the complete logical price and storage coordinates are

$$
\begin{aligned}
E&=E_C+(K+4)+G_Q+G_P+G_R,\qquad \mathrm{Fee}=2E,\\
\mathrm{Storage}(z)&=\left(S_0+b_{\rm ctl}(z)+8A(z)+8E(z),\ Q(z)\right),\\
\mathrm{Retention}&=\sum_{z\text{ logical tick}}Q(z).
\end{aligned}
\tag{62.32}
$$

Here $A(z)$ includes original current packet, complete rejected scratch, original rows/copies, private coefficient integers and digits, all instructions, flags, descriptors and caches simultaneously. $E(z)$ counts both disjoint receipt chains, $Q(z)$ is the constructed qubit count, and $S_0$ includes both chains' actual foundations. After full bank construction $Q(z)=K+4$ through preparation, service, arithmetic, catalog fetch, all interaction cuts and terminal delivery. Holding an auxiliary's imperfect state is included in exactly the same retention coordinate. Classical peak is the maximum at one common cut, not the sum of separate maxima.

Proof. The source-copy/cursor routine is exactly Lemma60.10 on the actual current packet descriptor. The arithmetic word has finite fixed loops and positive denominators by Theorem62.8. PR57.L1–L3 expands its additions, comparisons and truth tables into terminating native words and establishes that private values never select their traces. The interpreter field lengths give (62.30); all its seeks and cache descriptors are actual constructed strings. The wire enumeration gives (62.31), with both signs and every exponent paid. A digit consumes its fixed stored bit and enable, computes their AND on actual latches, and invokes one supplied matrix; no digit or identity slot is skipped on a private zero. Each core event constructs exactly one receipt and has fee two, including the added finite quantum events of §60. Summing those disjoint actual words gives (62.32). Every parameter-supply algorithm declared effective has finite work here, but no history-independent cost bound over arbitrary effective policies or rational input lengths is asserted. These are ideal logical prices and simultaneous material counts, not physical energy, calibrated elapsed time or a minimal circuit price. $\square$

**Proposition 62.12 (known preparation, version authentication and original records).** A known supported occupation $S$ has a finite paid preparation: construct all $K+4$ zero qubits, supply its $K$-bit occupation array, execute one explicitly supplied fixed bit-flip slot at every public address with that array's private enable, and retain every zero slot. Thus $G_P=K$ before optional reference/other preparation slots. The support and count are privately checked by fixed Boolean folds against $x_p$ and the public commissioned $N$; their ingress, additions, comparisons and complete code are paid. They do not become source-dependent public preparation labels. This preparation uses known material coefficients, not acquired amplitudes or an inferred ground state.

An arbitrary supported unit state may instead be supplied by its own permitted preparation with the error and full carrier of Theorem62.10. The theorem transports its unknown phases but does not acquire them. A joint reference input likewise requires its own actual finite preparation word and all its prices; for $N=1$ the balanced reference/root construction is exactly Proposition60.6. A terminal computational-basis effect has one supplied measurement slot plus all classical framing/delivery; more elaborate effects require their own finite word. No measurement is used in the interaction or renewal, and no probability is an original exact Read.

At actual accepted whole-rho requests the held bank is released with coefficients from the just-installed authenticated packet. At refusal the old installed coefficients remain. Original Reads and source stops use their unchanged routines, errors and original response fields; Stop is absorbing for quantum checkpoints/readout as well. Any terminal effect precedes Stop. Projection of the joint chronological record to original fields is precisely the record of §60.3, including INITIAL, preparation identity, every command, executed acceptance/refusal, Read and original copy/fence numeral.

Proof. Enabled bit flips on the complete zero bank create exactly its supplied occupation; every unused address remains present. The support/count fold is a fixed-width Boolean expression, so its private values have no public successor. Its success is a premise of the supported preparation contract; it is not a free particle-count reply or an actor initialization depending on the source. Every active program and gate is installed while the original source block is locked, and all borrowed original heads are restored. Induct using PR57.T1–T5 and Theorem60.3. Extra private arithmetic/quantum events append only to the added chain, so no original numeral is renumbered. Private coefficient arrays have no callable source port and provide no action on a duplicate source. An accepted non-whole context retains its original full guard and response but ends this same-address comparison, exactly as in Definition60.1. Holding and refusing require neither a new quantum state nor an auxiliary reset. $\square$

**Proposition 62.13 (the actual H3 discriminator, statistics and phase).** At $H=3$ the authentic INITIAL $\langle\beta,\alpha\rangle$ has the actual chronological history

$$
\operatorname{Read}[BA];\ \rho[\mathrm{accept}];\
\operatorname{Read}[A+B];\ \rho[\mathrm{reject}];\
\operatorname{Read}[A+B];\ \operatorname{Stop}.
\tag{62.33}
$$

Its original INITIAL target is $(1,(1,1),BA,A+B)$, unchanged by the added apparatus. Old addresses are $D=\{o,L,R\}$; accepted addresses are $D'=\{o,L,R,LL,LR\}$. Their killed root/left coefficients are respectively $1/4,9/26$ and their common coefficient is $1/2$ at both versions. Hence the old two-particle occupation $\{o,L\}$ has killed renewal energy change $-5\nu/52$ and common change zero, with the same one-body $\phi$ in both.

The two-particle hard-core kinetic operator on $D'$ is not spectrally equivalent to $\Lambda^2 L_{D'}$: with $a=1,g=\nu=0$,

$$
\operatorname{tr}(K_{D',2}^6)=759280,
\qquad
\operatorname{tr}((\mathrm d\Gamma_{\wedge^2}L_{D'})^6)=759256.
\tag{62.34}
$$

In particular their full-phase finite propagators differ. At $\theta=1/100$ the real part of their trace difference is strictly between

$$
-\frac{23121015983636759877992957832379}
{694702008000000000000000000000000000000000000}
\quad\text{and}\quad
-\frac{23121015983636725212194415013051}
{694702008000000000000000000000000000000000000}.
\tag{62.35}
$$

Proof. The leaf counts are $2,3,5$, giving exactly one acceptance. The actual products are $BA$ and $BAB=A+B$, using the original $A^2=1,B^2=-1,AB+BA=1$. The full second candidate is refused and supplies no Read. The matrices for the old and new domains have diagonals $2,3,\ldots,3$ and $-1$ on the displayed actual seams. Their old Schur complements are respectively $L_D$ and $L_D-(2/3)|L\rangle\langle L|$. Direct rational inversion gives the stated two entries; (62.3) gives $1/2$. Substitution in (62.9) proves the energy change.

For (62.34), enumerate the ten two-site configurations in the displayed address order. The hard-core diagonal at $S$ is $\sum_{p\in S}d_p$; each allowed move contributes $-1$. The exterior diagonal is the same, but a move $q\mapsto p$ contributes $-(-1)^{\#\{i\in S:i<q\}+\#\{i\in S\setminus\{q\}:i<p\}}$. These complete finite matrix formulas give (62.34) by six matrix multiplications. The six-move closed occupation path
$\{o,LL\},\{L,LL\},\{LL,LR\},\{L,LR\},\{o,LR\},\{o,L\},\{o,LL\}$
has hard-core hopping product $+1$ and exterior hopping product $-1$. This closed sign discriminator is stronger than a removable single basis-edge sign.

For the explicit finite phase inequality, form powers through degree sixteen of those same integer matrices and sum the even Taylor trace terms of $e^{-i\theta K}$. Both matrices have norm at most twelve by the one-body compression bound. Each ten-dimensional trace tail after degree sixteen is at most $20(12\theta)^{17}/17!$; the two tails together are at most $40(12\theta)^{17}/17!$, since $12\theta<1/2$. Adding/subtracting this rational remainder from the computed rational even sum gives exactly (62.35). It is a mathematical propagator calculation, not an acquired trace or a new original Read. $\square$

**Proposition 62.14 (finite actual dyadic pair certificates).** For either killed coefficient in Proposition62.13, take $\nu=1$, $\theta=1/10$, $b=24$, $J=26$ and the 89-block pair word with all fixed-angle magnitudes rounded down to multiples of $2^{-24}$ and every negative sign restored. The actual central phase angles are

$$
\widetilde\xi_{\rm old}=-209715/8388608,
\qquad
\widetilde\xi_{\rm new}=-580749/16777216.
\tag{62.36}
$$

Executing every $89\cdot26=2314$ digit slots, including identities, gives on the four clean data input columns of the full five-qubit pair carrier the full-phase operator-error bounds

$$
\begin{aligned}
\eta_{\rm old}&\le
\frac{15469415171574642961544437}{40564819207303340847894502572032}<10^{-6},\\
\eta_{\rm new}&\le
\frac{30335154456616661277356327}{40564819207303340847894502572032}<10^{-6}.
\end{aligned}
\tag{62.37}
$$

Both are below the analytic $89\cdot2^{-24}$ bound. For the common coefficient $1/2$, the same finite prescription has central angle $-209715/4194304$ and operator-error upper bound $30909823706171090313337097/40564819207303340847894502572032<10^{-6}$. The reached auxiliary amplitudes are included, rather than discarded. At $H=3$, $a=g=\nu=1$ and $T=1/10$, the public width $J=26$ is valid: a whole public slice has 1,882 angle blocks, 48,932 digit slots, 1,300 signed catalog entries and 11 constructed quantum modes. These are interaction/carrier coordinates, to which every classical, preparation, hold and terminal coordinate of (62.32) is added.

Proof. The scaled rational magnitudes are divided by their positive denominators by the forty-step restoring recurrence (62.23); the quotient gives (62.36). For the fixed constants use the Machin identity in Theorem62.9 with ninety terms for each alternating arctangent. Both endpoints have the same required dyadic floor.

Here is a rational interval prescription for all scalar matrix entries. Use integer scale $2^{110}$ and outward lower/upper rounding at every real multiplication and addition. For each actual digit angle $x$, enclose its sine and cosine by their degree-48 real Taylor polynomials with remainder $|x|^{49}/49!$. Multiply all individual signed local digit matrices in the exact chronological word of Theorem62.7 on each of the four clean columns; an enable-zero slot is the exact identity matrix. Compare each reached component with the ideal clean column of $e^{-i\xi n_pn_q}$, enclosing its central sine/cosine by the same prescription. If $v$ is the maximum real/imaginary component discrepancy, the complex $32\times4$ Frobenius norm is at most $16v$. Outward arithmetic gives respectively the two fractions in (62.37). Since all 32 components are included, this bounds the clean-input operator norm into the full carrier, including leakage.

The rational coefficient word (62.19)–(62.21) agrees with direct inversion for every authentic source at caps $1,2,3,4$, respectively $2,6,22,102$ sources: the complete comparison contains 11,190 unordered public-bank coefficient outputs, including masked zeros. The largest unreduced integer in that finite comparison has 36 bits. Its 30 accepted renewals satisfy the complete beta-mask inverse update, including 16 acceptances without domain growth; its 102 refusals retain the old packet. The common expression also satisfies 441 exact local field equations for addresses through depth five and charge addresses through depth two. The mathematical comparison is the displayed factorization, independently evaluated against rational Gaussian elimination of each authentic $L_D$; Gaussian elimination is only the comparison calculation, not the private producer. For Proposition62.5 at depths $1,2,3$, the exact pair losses divided by $\nu$ are $1/8,263/840,5727/8680$, respectively, above $2/81,4/81,8/81$. These finite consequences corroborate the general proofs; they do not replace their all-source quantifiers or give unknown-state preparation, physical calibration or an infinite-time gate law.

There is also a separately assembled literal Boolean witness from the two authentic ten-bit $H=3$ packets in Proposition62.13. Its fixed-order flag word uses 3,738 Boolean gates. All seven public-bank downward pivots and upward diagonal rational pairs are then formed by the five-gate adder, seven-gate comparison, complete schoolbook products and MUX masks of PR57.5, followed by the root/left coefficient and a forty-step restoring division. The unreduced outputs are $9/36$ and $567/1638$, not externally supplied inverse coefficients. Scaling their numerators by $2^{24}$ and their denominators by ten gives respectively $(150994944,360)$ and $(9512681472,16380)$. The actual quotients are 419,430 and 580,749, with remainders 144 and 12,852. Both give exactly (62.36). The displayed public width (62.22) is a general sufficient width; this finite witness uses a verified forty-bit arithmetic workspace.

This witness contains 679,659 complete truth-table records and 679,671 signal cells. Its literal unary-field code length is 620,738,706,249 bits. Replaying those truth-table records on the two authentic input caches gives the same outputs under one source-independent instruction/address trace. Counting the four caches, their complete base descriptors, every actual head position and every unary loop by the primitive recurrences of PR57.03–06 gives 1,964,789,879,561,424,993 interpreter core occurrences and fee 3,929,579,759,122,849,986. Independent summation by (PR57.06) gives the same count. The four caches and four descriptor tapes retain 140,342,222,930,423,142 ordinary cells at their final common cut. Literal code appends add 1,862,216,118,747 core occurrences; copying all material code bits adds their further 1,241,477,412,498 reads/moves. These are deliberately inefficient interpreter coordinates, not a total commission price or an optimality claim: source/lock/cursor work, bootstrap, generator frames and references, workspace allocation, catalog/fetch work, preparation, gates, holds and effects are additionally the explicit words of Proposition62.11. The host calculation represents unary runs by their exact finite primitive-count recurrence, rather than materializing that many receipts or executing a full original-processor bootstrap. No compressed host representation becomes an extra native primitive, accessible counter or free code supplier.

A finite extension of that same authentic coefficient circuit computes one pair enable and then emits a full AND record for each of its 2,314 digit slots. The AND operands are the actual restoring-division output cells for the central magnitude and the constructed constant cells for the fixed magnitudes. Its 681,974 Boolean records have 1,238 enabled and 1,076 disabled quantum slots on each of the two sources. Use the seven address-bank ordinals $0,\ldots,6$, inherited reference ordinal $7$, and auxiliary ordinals $c=8,u=9,v=10$. Every slot consumes its complete public kind, two endpoint, sign and exponent fields; these fields contain 62,023 bits in total. Their literal `RD; MR` scan, initial `Home; MR` and final exit use 124,051 core occurrences. Every AND result remains in the private latch through its paid destination seek/write and supplies the fixed quantum row.

The complete coefficient/enable/digit interpreter, that public field scan and the 2,314 quantum rows together have 1,984,959,124,199,447,681 core occurrences, fee 3,969,918,248,398,895,362 and, with the eleven-mode bank already constructed and held throughout, 21,834,550,366,193,924,491 qubit-ticks of retention. The code, fields, descriptors, workspace and receipts remain retained. These are exact coordinates of this expanded finite subword, not a total commission price: its control/bootstrap, generation and installation, original source/input/cursor/service words, preparation, terminal effect/framing and additional idle holds contribute their separately expanded words in Proposition62.11. No measurement result or exact probability is inferred from this price calculation. $\square$


**Definition 62.15 (scope of the interaction correspondence).** Equations(62.2), (62.7)–(62.9), (62.18)–(62.32) concern one authentic finite ordered source, the inherited unit occurrence realization and its expressly supplied ideal carrier. Their mathematical correspondence consumes §§55,58,60 and PR57 directly. The fermionic-swap matrix and branching-wire method are classical intermediates from Brod–Childs; the particular source coefficients, produced finite pair words, original-record projection and the joint renewal/retention relation are the deduction here. No primary-paper originality or abstract general-theorem priority is assigned to them.

The physical gates, clocks, noise bounds, displacement law, unknown-state ingress and reference acquisition are independent unverified realization premises. Tree degree, local three-dimensional direction, computational wiring, state-sector dimension, coefficient precision and retained population are different objects. In particular no operation-/metric-preserving correspondence from the original local direction interface to a Euclidean region is defined here. The original $\mathcal D_2$ source, independent arbitrary unbounded $a$ including zero, untagged radius-$7/25$ $b$, destructive actions, joint adversarial/history-dependent errors, source-independent initialization, actual Reads and INITIAL/Stop target keep their original domains. No tags, copies of a running source, reset, independent resampling or limit Read is added to that menu. Fixed-$N$ infimum convergence, extensive lower boundedness, old-energy retention, dynamical intertwining, ground-state attainment, precompactness, continuum convergence and thermodynamic/physical stability remain distinct mathematical assertions; only the displayed implications are used.

## 追加锚（本行以下为增补区）

## 63. Fixed-population cluster escape, attained binding and complete recursive spectral retention

**Definition 63.1 (one commissioned source and its fixed-population operator).** Retain the whole joint source of §§55.1,58.1,60.1 and62.1: immutable ordered INITIAL, actual source packet, authentic addressed versions $D_j(t)$, original preparation, complete candidate guards, every actual Read, acceptance, refusal and Stop. The added occurrence realization has the same root $o$, counting measure, unit parent–child seams, inherited degrees $d_o=2$, $d_p=3$ otherwise, root field $\phi(p)=2^{-|p|}$ and $\lambda=3-2\sqrt2$. Its commissioned parameters are $a,g>0$, $\nu\ge0$. Fix any finite integer $N\ge2$. On $\mathscr H_N=\ell^2(\mathcal C_N(\mathcal P))$ write

$$
\begin{aligned}
H_N&=aK_N-g\sum_{p\in S}\phi(p)
-\nu\sum_{\{p,q\}\subset S}G^{\rm c}(p,q),\\
G^{\rm c}(p,q)&=G_0(p,q)+\tfrac13\phi(p)\phi(q),\qquad
G_0(p,q)=\tfrac23\,2^{-d(p,q)},\\
m_k&=\inf\sigma(H_k),\qquad m_0=0,\qquad
\Sigma_N=\inf\sigma_{\rm ess}(H_N).
\end{aligned}
\tag{63.1}
$$

Multipliers in this notation act at the occupation $S$. The $k$-particle operators have the same parameters and literal hard-core statistics. By §§62.2–62.3 they are bounded self-adjoint, and $K_k\ge k\lambda I$. An allowed configuration edge replaces one occupied address by one empty adjacent address, with coefficient $-a$. Its graph degree is at most $3k$, but its kinetic diagonal is $\sum_{p\in S}d_p$, including every collision and exterior killing term. The two degrees are not interchangeable. Finite common operators are precisely compressions of $H_N$; finite killed operators retain the same $\phi$ and replace only pair coefficients by $G_D^{\rm k}$. All occupation embeddings below are same-address zero extensions. An index beyond one actual execution belongs to §55.1's mathematical family of separately legal finite prefixes; only actually reached versions belong to that execution.

The task is the missing implication from fixed-$N$ infimum recovery to actual bound states and their complete finite spectral spaces. An escaping group may remain internally adjacent, so its pair multiplier need not tend to zero. Nothing here replaces that group by independent particles or regards the many-particle potential as compact.

**Lemma 63.2 (joint occupation bounds used by the escape certificate).** Put $c_0=b_0=r_0=A_0=0$, and for $m\ge1$ define

$$
\begin{aligned}
c_m&=\min\left\{\frac{m(m-1)}6,\frac{m}{2\lambda}-\frac m3\right\},
&b_m&=am\lambda-\nu c_m,\\
r_m&=\min\left\{\frac{m(m-1)}4,\frac{m}{2\lambda}-\frac m3\right\}.
\end{aligned}
\tag{63.2}
$$

Order the addresses by increasing depth, breaking ties by left/right lexicographic order; let $S_m$ be the first $m$ addresses and set

$$
A_m=\sum_{p\in S_m}\phi(p),\qquad
P_m=\sum_{\{p,q\}\subset S_m}G^{\rm c}(p,q).
\tag{63.3}
$$

In particular $A_m=h+(m-2^h+1)2^{-h}$ when $2^h\le m+1<2^{h+1}$. For every actual $m$-site occupation $Y$,

$$
\sum_{\{p,q\}\subset Y}G_0(p,q)\le c_m,
\quad
\sum_{\{p,q\}\subset Y}G^{\rm c}(p,q)\le r_m,
\quad
\sum_{p\in Y}\phi(p)\le A_m,
\quad
m_m\ge am\lambda-gA_m-\nu r_m.
\tag{63.4}
$$

Proof. Off the diagonal, $G_0\le1/3$ and $G^{\rm c}\le1/2$: in the latter case $d(p,q)\ge1$ and distinct addresses satisfy $|p|+|q|\ge1$. These give the first alternatives in (63.2). For $z=\mathbf1_Y$, the already supplied inverse bound gives $z^*G^{\rm c}z\le m/\lambda$, while $G^{\rm c}(p,p)\ge2/3$. Subtracting the diagonal and dividing by two gives the second alternative for $r_m$. Also

$$
z^*G_0z=z^*G^{\rm c}z-\tfrac13\left(\sum_{p\in Y}\phi(p)\right)^2\le m/\lambda,
\qquad G_0(p,p)=2/3,
$$

giving the second alternative for $c_m$. No new positivity assumption on a comparison kernel is needed. The depth ordering maximizes the sum of the $m$ largest field values. Combining these pointwise bounds with $K_m\ge m\lambda I$ proves the operator lower bound. These are consumed consequences of the same-L kernel and occupation bound of §62, rather than an independent stability claim. $\square$

**Theorem 63.3 (all-configuration localization with an explicit exterior error).** Define the joint lower escape certificate

$$
B_N=\min_{0\le k<N}\{m_k+b_{N-k}\}.
\tag{63.5}
$$

For each integer $R\ge2$ let $\mathcal F_R=\mathcal C_N(B_{(2N+1)R})$. Every $f\in\mathscr H_N$ vanishing on this finite configuration core satisfies

$$
\begin{aligned}
\langle f,H_Nf\rangle&\ge(B_N-\eta_N(R))\|f\|^2,\\
\eta_N(R)&=\frac{6aN(9N+1)}{R^2}
+\left(gN+\frac{\nu N^2}4\right)2^{-R}
+\frac{\nu N(N-1)}6\,2^{-2R} \longrightarrow0.
\end{aligned}
\tag{63.6}
$$

The estimate includes partial, multiple and intact cluster escape, with no cluster-separation hypothesis on $f$ and no attainment assumption on any $m_k$.

Proof. For a configuration $S$, sort its depths as $d_1\le\cdots\le d_N$, with $d_0=0$. Define the continuous piecewise affine functions

$$
\begin{aligned}
\psi_R(x)&=\begin{cases}
1,&x\le2NR,\\
((2N+1)R-x)/R,&2NR<x<(2N+1)R,\\
0,&x\ge(2N+1)R,
\end{cases}\\
\gamma_R(x)&=\begin{cases}
0,&x\le R,\\
(x-R)/R,&R<x<2R,\\
1,&x\ge2R.
\end{cases}
\end{aligned}
\tag{63.7}
$$

Set $w_N(S)=\psi_R(d_N)$, $w_k(S)=\psi_R(d_k)\gamma_R(d_{k+1}-d_k)$ for $0\le k<N$, and

$$
\chi_k(S)=\frac{w_k(S)}{\left(\sum_{i=0}^Nw_i(S)^2\right)^{1/2}}.
\tag{63.8}
$$

The denominator is at least one. Indeed, if $d_N\le2NR$ then $w_N=1$. Otherwise some consecutive gap is at least $2R$. Before the first such gap all gaps are less than $2R$, so its preceding depth $d_k\le2kR\le2NR$ and $w_k=1$. This covers every configuration, including tied depths, and $\sum\chi_k^2=1$. The support of $\chi_N$ is inside the finite core. On the support of $\chi_k$ for $k<N$, the $k$ shallowest particles form a uniquely determined group $X$, with

$$
\max_{p\in X}|p|<(2N+1)R,\qquad
\min_{q\in Y}|q|-\max_{p\in X}|p|>R,\qquad Y=S\setminus X,
\tag{63.9}
$$

when $k>0$; for $k=0$ every particle has depth greater than $R$.

A permitted hop changes each depth order statistic by at most one, hence a gap by at most two. Thus each $w_k$, $k<N$, changes by at most $3/R$, and $w_N$ by at most $1/R$. For vectors $u,v$ with norms at least one,
$\|u/\|u\|-v/\|v\|\|\le2\|u-v\|$; consequently every allowed edge $S\sim T$ satisfies

$$
\sum_{k=0}^N|\chi_k(S)-\chi_k(T)|^2\le\frac{4(9N+1)}{R^2}.
\tag{63.10}
$$

Write $q_N(f)=\langle f,H_Nf\rangle$. All diagonal terms cancel in the discrete IMS identity, leaving exactly

$$
\sum_kq_N(\chi_kf)-q_N(f)
=a\sum_{\{S,T\}:S\sim T}\operatorname{Re}(\overline{f(S)}f(T))
\sum_k(\chi_k(S)-\chi_k(T))^2.
\tag{63.11}
$$

Using $2|f(S)f(T)|\le|f(S)|^2+|f(T)|^2$, the configuration degree bound $3N$ and (63.10), its absolute value is at most $6aN(9N+1)\|f\|^2/R^2$. Collision killing and inherited exterior degrees remain on the diagonal throughout this identity.

It remains to estimate each localized piece, rather than assume a cluster formula. For $k<N$ put $m=N-k$ and $h=\chi_kf$. Map its support isometrically by $S\mapsto(X,Y)$ into
$\ell^2(\mathcal C_k(\mathcal P))\otimes\ell^2(\mathcal C_m(\mathcal P))$, putting zero at every other pair. The gap in (63.9) is greater than two. An allowed hop between two support configurations therefore cannot exchange membership across this split. Conversely every nonzero tensor hopping matrix entry between supported pairs is precisely one allowed original hop. On the support the two groups are disjoint and not adjacent, so no between-group collision term is lost. The diagonal remains the sum of all original site degrees. Hence the kinetic form is exactly the form of $K_k\otimes I+I\otimes K_m$ on this zero-extended tensor vector. For $k=0$ the first factor is the scalar vacuum.

Keep the full root potential and full common pair attraction inside $X$. These terms and its kinetic operator give $H_k\ge m_kI$ in the first factor. Keep *all* $G_0$ pair attractions inside $Y$, even if $Y$ consists of several clusters or one intact cluster; Lemma63.2 and the inherited kinetic gap give $aK_m-\nu\sum_YG_0\ge b_mI$. The remaining attractive terms are small pointwise. Every far address has $\phi(q)\le2^{-R}$. A near/far pair has $d(p,q)>R$ and $|p|+|q|>R$, so $G^{\rm c}(p,q)\le2^{-R}$. Therefore

$$
q_N(h)\ge\left[m_k+b_m-gm2^{-R}
-\nu km2^{-R}-\frac\nu3\binom m2\,2^{-2R}\right]\|h\|^2.
\tag{63.12}
$$

All estimates refer to the same tensor vector and the same actual occupation; separately optimal configurations were not combined. If $f$ vanishes on $\mathcal F_R$, then $\chi_Nf=0$. Sum (63.12), use $km\le N^2/4$, $m\le N$, the partition norm identity and (63.11). This proves (63.6). In particular the far group never needed an internal partition, so equal-depth clusters and arbitrarily many mutually escaping subgroups are covered. $\square$

**Theorem 63.4 (two-sided certificates and actual escaping trial families).** For every fixed finite $N\ge2$,

$$
B_N\le\Sigma_N\le
\min_{0\le k<N}\{m_k+u_{N-k}\},
\qquad
u_m:=\min\{am\lambda,3am-\nu w_m\},\qquad
w_m:=\tfrac23(m-2+2^{1-m}).
\tag{63.13}
$$

Proof. First, any weakly null unit sequence $f_n$ has

$$
\liminf_n q_N(f_n)\ge B_N.
\tag{63.14}
$$

For fixed $R$, $\chi_N$ has finite support, so $\chi_Nf_n\to0$ strongly and its energy tends to zero. Apply (63.11)–(63.12) to the other pieces, take the lower limit, then let $R\to\infty$. If the spectral subspace below some $c<B_N$ were infinite dimensional, an orthonormal sequence in it would be weakly null with energies at most $c$, contradicting (63.14). Thus below each such $c$ the full spectral subspace is finite dimensional, proving $\Sigma_N\ge B_N$.

For the upper bounds fix $k<N$, $m=N-k$ and a unit finite-support root trial $f$ for $H_k$ with energy at most $m_k+\epsilon$. For $k=0$ take the scalar vacuum. For the free branch, use the actual radial sine packets of §55.3, each on finitely many levels of a deep descendant subtree. Choose $m$ such subtrees pairwise disjoint and separated by distances tending to infinity, and also escaping the finite support of $f$. Each packet has kinetic expectation tending to $\lambda$ and root-field expectation tending to zero. Their tensor product has exactly one particle in each disjoint support. Union of its occupations with those of $f$ is a literal occupation isometry; there are no factorial normalization or ordering signs. The inherited kinetic expectations add, including support-boundary killing. All far-far and near-far pair terms tend to zero, since the support separations tend to infinity. These weakly null unit trials have limiting energy at most $m_k+\epsilon+am\lambda$.

For the intact-cluster branch take one basis occupation on $m$ consecutive nonroot vertices of a ray, translated to depth tending to infinity. Its diagonal kinetic expectation is exactly $3m$, even though adjacent particles block moves. Its root-field and image-pair terms tend to zero, while

$$
\sum_{r=1}^{m-1}(m-r)\frac23\,2^{-r}
=\frac23(m-2+2^{1-m})=w_m.
\tag{63.15}
$$

The same union isometry with $f$ gives weakly null unit trials of limiting energy at most $m_k+\epsilon+3am-\nu w_m$. Cross-group attraction tends to zero because $f$ is fixed and finite. These basis occupations are variational trials, not asserted Weyl eigenvectors.

For a bounded self-adjoint operator, any weakly null unit sequence has energy lower limit at least the essential lower edge: its projection onto the finite-dimensional spectral subspace below any number smaller than that edge tends to zero. This also follows directly from the min-max principle of §55.8. Apply it to the two trial families, let $\epsilon\downarrow0$ and minimize over $k$. The constructed finite-energy weakly null families also show the essential spectrum is nonempty. The result is a sufficient sandwich, not an assumed sharp HVZ identity. $\square$

**Theorem 63.5 (an explicit nonempty binding regime for every fixed N).** The actual occupation trial $e_{S_N}$ has energy

$$
E_N^{\rm root}=a(3N-1)-gA_N-\nu P_N.
\tag{63.16}
$$

If, for every $0\le k<N$,

$$
g(A_N-A_k)>
a(3N-1-N\lambda)+\nu(r_k+c_{N-k}-P_N),
\tag{63.17}
$$

then $m_N\le E_N^{\rm root}<B_N\le\Sigma_N$. This is a nonempty regime for each fixed $N,a,\nu$: every $A_N-A_k$ is strictly positive, so any positive $g$ larger than all the finitely many right-hand-side quotients in (63.17) suffices. No common $g$ for unbounded $N$ is asserted.

Whenever $m_N<B_N$, the infimum is attained, the ground eigenspace is nonzero and finite dimensional, and *every* normalized near-minimizing sequence is strongly precompact. Its cluster points are unit ground states. There is a positive gap from $m_N$ to the spectrum on the orthogonal complement of that entire groundspace.

Proof. The breadth-first occupation includes the root. Its diagonal is $2+3(N-1)$, and a single occupation basis vector has zero hopping expectation, proving (63.16). Lemma63.2 gives

$$
m_k+b_{N-k}\ge aN\lambda-gA_k-\nu(r_k+c_{N-k}).
\tag{63.18}
$$

Inequality(63.17) compares the *one* actual trial (63.16) strictly with every lower channel in (63.18). It proves the claimed gap without assuming the existence of a bound state in any smaller sector.

For attainment, let $f_n$ be any unit near-minimizing sequence, pass to a weak limit $f$ and put $r_n=f_n-f$. Boundedness of $H_N$ makes the cross energy vanish; $\|r_n\|^2\to1-\|f\|^2$. Rescaling (63.14), including the zero-norm case by boundedness, gives

$$
\begin{aligned}
m_N&\ge q_N(f)+B_N(1-\|f\|^2)\\
&\ge m_N\|f\|^2+B_N(1-\|f\|^2).
\end{aligned}
\tag{63.19}
$$

The strict gap forces $\|f\|=1$, hence strong convergence and energy $m_N$. Variation gives $H_Nf=m_Nf$. This argument applies to every near-minimizing sequence. The finite-dimensional subthreshold spectral conclusion in Theorem63.4, applied at a number strictly between $m_N$ and $B_N$, gives finite ground multiplicity and isolates $m_N$ from the rest. No single radial channel, source-label permutation or ground-state preparation was used. $\square$

**Lemma 63.6 (actual-domain buffers for killed coefficients and moving packets).** Set $\varrho=1-\lambda/3<1$. If an authentic domain $D$ contains the occurrence ball of radius $b$ around $p$, then, for every $q\in D$,

$$
0\le G^{\rm c}(p,q)-G_D^{\rm k}(p,q)
\le\frac{\varrho^{b+1}}\lambda.
\tag{63.20}
$$

For a normalized finite state whose every occupied address has such a buffer, its killed-minus-common energy is at most
$\nu\binom N2\varrho^{b+1}/\lambda$.

Proof. Consume §62.2's nonnegative path expansion $L^{-1}=\frac13\sum_{n\ge0}P^n$, with $P=I-L/3$ and $\|P\|\le\varrho$. The killed expansion keeps exactly the paths staying in $D$. A path starting at $p$ with at most $b$ steps cannot leave the contained ball; all differences therefore start at $n=b+1$. Bound each matrix entry of $P^n$ by $\|P\|^n$ and sum the geometric tail, using $3(1-\varrho)=\lambda$. Sum this same coefficient bound over the pairs in each actual occupation and then over its probability weights. $\square$

Every finite packet used in Theorem63.4 can consequently be placed on actual, separately commissioned whole-rho prefixes with buffers tending to infinity, giving the same common and killed trial limits. Indeed choose a finite radius $r$ containing all its addresses and a buffer $b$, and a finite accepted index $j\ge2(r+b)$. The already proved $B_{\lfloor j/2\rfloor}\subset D_j(t)$ supplies all required buffers, uniformly in the original finite source $t$. Commission that finite prefix at a cap sufficient for its actual leaf counts. This construction retains the actual irregular domain; it is not a replacement ball or a change to a running cap. A moving address merely belonging to a frontier does not satisfy (63.20) with $b\to\infty$, so no moving-frontier killed limit follows without this buffer.

**Theorem 63.7 (all finite near-minimizers, common and killed).** Suppose $m_N<B_N$, in particular under (63.17). For every sequence of original finite sources $t_n$ and legal-prefix indices $j_n\to\infty$, write $D_n=D_{j_n}(t_n)$. For either prescription $\diamond\in\{\mathrm c,\mathrm k\}$, let $f_n\in\ell^2(\mathcal C_N(D_n))$ be unit and satisfy

$$
\langle f_n,H^\diamond_{D_n,N}f_n\rangle
-\inf\sigma(H^\diamond_{D_n,N})\longrightarrow0.
\tag{63.21}
$$

Their identical-address zero extensions are strongly precompact in $\mathscr H_N$, and every cluster point is a unit common ground state. In particular this holds along every fixed original source's legal-prefix family.

Proof. Theorem62.6 supplies the finite infimum recovery. Its proof is uniform under contained-ball exhaustion: choose its finite recovery vector first, contain its finitely many occupied addresses in $B_r$, and use (63.20) with $b=\lfloor j_n/2\rfloor-r$. This gives the needed local coefficient recovery for arbitrary varying $t_n$, without a norm limit of the full Green operators. The finite inequalities are exactly

$$
m_N\le q_N(I_{D_n,N}f_n)
=\langle f_n,H^{\rm c}_{D_n,N}f_n\rangle
\le\langle f_n,H^{\rm k}_{D_n,N}f_n\rangle.
\tag{63.22}
$$

Thus either near-minimizer family is a common near-minimizer. Apply Theorem63.5. This uses the actual inherited diagonal and the pointwise killed/common ordering, not a claim that all finite pair multipliers converge in operator norm. $\square$

**Theorem 63.8 (uniform tightness of every certified subthreshold eigenvector).** Fix $c<B_N$. For all sufficiently large integers $R$, every unit eigenvector with energy $z\le c$, either of $H_N$ or of any authentic finite common/killed operator, has

$$
\bigl\|\mathbf1_{\mathcal C_N(\mathcal P)\setminus
\mathcal C_N(B_{(2N+2)R})}f\bigr\|^2
\le\frac{3aN}{(B_N-c)R^2}.
\tag{63.23}
$$

Finite vectors in this formula are zero extended. No radial, root-visible or occupation-symmetry sector is removed.

Proof. Let $r(S)=\max_{p\in S}|p|$ and let $h_R(S)$ be zero for $r(S)\le(2N+1)R$, one for $r(S)\ge(2N+2)R$, and affine between. It is $1/R$-Lipschitz on allowed configuration edges, and $h_Rf$ vanishes on $\mathcal F_R$. For a finite eigenvector use its *finite* eigen-equation; all diagonal terms, including its killed pair multiplier, cancel in the exact identity

$$
q^\diamond_D(h_Rf)-z\|h_Rf\|^2
=a\sum_{\{S,T\}\text{ allowed in }D}
\operatorname{Re}(\overline{f(S)}f(T))(h_R(S)-h_R(T))^2
\le\frac{3aN}{2R^2}.
\tag{63.24}
$$

The same identity holds for a common infinite eigenvector. Exterior and collision killing stay in both diagonal expressions. The common exterior bound (63.6) applies after zero extension, and killed energy is at least common energy. Hence

$$
(B_N-z-\eta_N(R))\|h_Rf\|^2\le\frac{3aN}{2R^2}.
\tag{63.25}
$$

Choose $R$ so that $\eta_N(R)\le(B_N-c)/2$; where $r(S)\ge(2N+2)R$, $h_R=1$. This proves (63.23). Its finite cores and vanishing tails imply strong precompactness of all such eigenvectors over arbitrary authentic domains. The conclusion is stronger than local convergence of their matrix entries. $\square$

**Theorem 63.9 (complete finite spectral windows on actual recursive domains).** Fix a compact window $W=[\alpha,\beta]$ with $\beta<B_N$ and $\alpha,\beta\notin\sigma(H_N)$. Let $D_n=D_{j_n}(t_n)$ with arbitrary original finite $t_n$ and $j_n\to\infty$. For both common and killed prescriptions, the ordered eigenvalues in $W$ converge to the common eigenvalues, repeated by multiplicity; eventually the total rank in $W$ equals the common rank. More precisely, for every common variational eigenvalue $\lambda_\ell<B_N$, ordered from the bottom and repeated by multiplicity,

$$
\lambda_\ell(H^\diamond_{D_n,N})\longrightarrow\lambda_\ell(H_N),
\qquad
\left\|I_{D_n,N}\mathbf1_W(H^\diamond_{D_n,N})I_{D_n,N}^*
-\mathbf1_W(H_N)\right\|\longrightarrow0.
\tag{63.26}
$$

The projection statement includes every hidden occupation mode and exceptional or degenerate eigenspace. In particular, for an isolated common eigenvalue $z<B_N$, choose gap endpoints enclosing $z$ and no other common eigenvalue. The finite eigenvalues in that interval may split; their total multiplicity eventually equals $\dim\ker(H_N-zI)$, and the projection onto their entire cluster converges to the full common eigenspace projection. An individual split finite eigenspace is not identified with the whole limiting degenerate space. An empty common window is eventually empty in both finite prescriptions.

Proof. The common spectrum below every $c<B_N$ has finite total multiplicity by Theorem63.4. The min-max principle in §55.8 and finite killed/common ordering give the lower inequalities for every finite variational level. For the reverse inequality, choose the finite span of the first $\ell$ common eigenvectors. Truncate it to configurations in $B_r$, with $r\to\infty$. Boundedness of $H_N$ gives uniform norm and form convergence on its finite-dimensional unit sphere; its dimension is eventually preserved. Place this one truncated span in $D_n$. Its common form is unchanged. For fixed $r$, (63.20), with $b=\lfloor j_n/2\rfloor-r$, makes the killed correction tend uniformly to zero on that span. Min-max gives the required limiting upper inequalities, first taking $n\to\infty$ and then $r\to\infty$. This argument neither assumes bound states in all smaller particle sectors nor changes the source realization.

If $c<B_N$ is in a common gap and $r_c$ common eigenvalues lie below it, their convergence supplies at least $r_c$ finite eigenvalues below $c$. There cannot be $r_c+1$: their finite spectral span would, after zero extension, have common Rayleigh values below $c$, contradicting common min-max. Thus the count is eventually exactly $r_c$. Apply this at both window endpoints to get complete rank and exclude spectral pollution or excess multiplicities. All variational levels below $\beta$ have already been controlled, so isolated common gaps inside the window contain no extra finite eigenvalues.

To prove preservation of the spaces, not just their eigenvalues, take any sequence of finite unit eigenvectors with energies in $W$. Theorem63.8 gives a strongly convergent subsequence with unit limit $f$, and the energies have a convergent subsequence, say $z_n\to z$. For any finite-support configuration test $v$, its occupied addresses and every address reached by one hop are eventually in $D_n$. Thus the common compressed test operator is exactly the common operator there. For the killed alternative its difference on this fixed test support tends to zero by (63.20). In the finite eigen-equation, passage to the limit gives

$$
\langle H_Nv,f\rangle=z\langle v,f\rangle.
\tag{63.27}
$$

Density and boundedness yield $H_Nf=zf$. The gap endpoints ensure $z\in W$.

Choose complete finite orthonormal eigenbases in $W$. Their eventually fixed finite size, tightness and subsequence extraction give orthonormal common limits. The rank equality makes those limits a complete basis of the common window space. Strong convergence of these finitely many basis vectors implies operator-norm convergence of their rank-one projection sums. Any subsequence has a further subsequence with this same limiting projection, proving the full projection limit (63.26). Degenerate vectors may rotate within their space; the space itself is preserved. No root resolvent cancellation or radial reduction enters this proof. $\square$

**Corollary 63.10 (recursive groundspace retention for both ideal prescriptions).** Assume $m_N<B_N$, and let $P_0$ be the full common ground projection. Write

$$
\gamma_N=\inf\sigma(H_N|_{\operatorname{ran}(I-P_0)})-m_N>0.
\tag{63.28}
$$

Consider any finite legal whole-rho history with the ideal same-occupation transfer and between-checkpoint finite generators already supplied in §§60,62. At original Reads and refusals there is no actuator change. Use consistently either the common or the killed pair prescription. If the initial supplied unit state has finite energy $E_0^\diamond$, then its actual ideal states $u(\tau)$, zero extended by their same addresses, obey throughout every supplied finite clock interval

$$
\|(I-P_0)u(\tau)\|^2\le\frac{E_0^\diamond-m_N}{\gamma_N},
\qquad
\operatorname{dist}\bigl(u(\tau),\{v\in\operatorname{ran}P_0:\|v\|=1\}\bigr)
\le\sqrt{\frac{2(E_0^\diamond-m_N)}{\gamma_N}}.
\tag{63.29}
$$

Proof. For the common prescription its finite energy is unchanged through every switch, by (62.7). For the killed prescription (62.8) makes every old pair coefficient increase, so its compression on old occupations decreases as a quadratic form. Thus its finite energy can only decrease at a renewal. Each between-event ideal unitary preserves its currently installed energy. At every cut the common energy of the zero extension is at most the current killed energy by (63.22). In either case $q_N(u(\tau))\le E_0^\diamond$. Apply the spectral inequality $H_N-m_NI\ge\gamma_N(I-P_0)$. Normalizing $P_0u$ and the identity $2(1-\|P_0u\|)\le2(1-\|P_0u\|^2)$ give the second bound; if the projection is zero, any unit ground vector has distance $\sqrt2$ and the same inequality still holds. $\square$

Expressly supplied finite ground states, or states satisfying (63.21), make this bound tend to zero along the actual-prefix families of Theorem63.7. The result is a bound on distance to the entire groundspace, for arbitrary finite duration and renewal count under the ideal law. It is not a full-phase dynamical intertwining theorem. Digital-gate checkpoints retain §62.10's accumulated state-error budget, which can be added to the distance bound when its preparation, parameter, hold and clock conditions are actually supplied. Energy monotonicity does not price physical work or prepare an unknown ground state.

**Proposition 63.11 (an actual pair binds although its one-particle sector is unbound).** Take exactly §55.6's INITIAL $t=\langle\beta,\alpha\rangle$ and fixed cap $H=3$, with its actual history

$$
\operatorname{Read}[BA];\quad\rho[\mathrm{accept}];\quad
\operatorname{Read}[A+B];\quad\rho[\mathrm{refuse}];\quad
\operatorname{Read}[A+B];\quad\operatorname{Stop}.
\tag{63.30}
$$

Commission $a=1$, $g=1/10$, $\nu=360$, $N=2$, and the existing paid known occupation $S=\{o,L\}$. The accepted domain is precisely $(o,L,R,LL,LR)$, with §55.6's inherited matrix and six exterior seams. Then

$$
\begin{aligned}
m_1&=\lambda\quad\text{with no attained one-particle minimum},\\
B_2&=2\lambda-120=-114-4\sqrt2,\\
\langle e_S,H^{\rm c}_{D,2}e_S\rangle&=-3503/20<B_2,\\
\langle e_S,H^{\rm k}_{D,2}e_S\rangle&=-31139/260<B_2,\\
B_2-\langle e_S,H^{\rm c}_{D,2}e_S\rangle
&=1223/20-4\sqrt2>0,\\
B_2-\langle e_S,H^{\rm k}_{D,2}e_S\rangle
&=1499/260-4\sqrt2>0.
\end{aligned}
\tag{63.31}
$$

Consequently $m_2<B_2$, so the common pair has an attained finite-dimensional groundspace and all-near-minimizer compactness, with the finite common/killed preservation of Theorems63.7–63.9. This is interaction-induced root binding despite the unbound one-particle sector, in a model whose coescaping adjacent pairs also retain attraction.

Proof. The no-binding range (55.18b) applies because $1/10<1/(2+3\sqrt2)$. It gives $m_1=\lambda$ and escape near-minimizers. It also excludes a nonzero threshold eigenvector: its proof gives
$H_1-\lambda I\ge[1-g(2+3\sqrt2)](L-\lambda I)$, with strictly positive prefactor, and the channel excess forms displayed before (55.18b) have zero kernel. Indeed their sums of squared differences and positive endpoint term can vanish only for the zero sequence. Hence the one-particle infimum is not attained.

Here $c_1=0$, $c_2=1/3$, so the two lower channels are $m_1+b_1=2\lambda$ and $b_2=2\lambda-120$; the latter is $B_2$. The occupied root/left pair has kinetic diagonal five, field sum $3/2$ and common pair coefficient $1/2$. Direct inversion of the actual accepted $L_D$ gives $G_D^{\rm k}(o,L)=9/26$, as in §62.13. Substitution gives

$$
5-\frac3{20}-180=-\frac{3503}{20},\qquad
5-\frac3{20}-\frac{360\cdot9}{26}=-\frac{31139}{260}.
\tag{63.32}
$$

The killed strict margin is certified without rounding by $1499^2-32\cdot260^2=83801>0$. On the initial three-site domain the killed coefficient is only $1/4$, giving trial energy $-1703/20$; that particular trial does not certify separation from $B_2$. No absence of other initial finite bound trials is inferred from it. The accepted pair trial is a genuine common trial by zero extension; the higher killed value also lies below the same lower escape certificate. All original leaf counts $2,3,5$, numerical replies, refusal and INITIAL target remain exactly §55.6's. No spectrum is inserted into an original Read. $\square$

**Proposition 63.12 (actual coescape distinguishes a retained pair from separated particles).** In separately legal finite prefixes of the same INITIAL of (63.30), let

$$
S_h^{\rm adj}=\{L^h,L^{h+1}\},\qquad
S_h^{\rm sep}=\{L^h,R^h\},\qquad h\ge1.
\tag{63.33}
$$

Commission a finite cap sufficient to reach an index $j_h\ge2(h+1+b_h)$, where $b_h\to\infty$, and use the authentic $D_{j_h}(t)$. Both known occupation preparations are within that same source-domain family. These are separate finite commissions with this INITIAL, not continuations of the stopped $H=3$ history. Their common, and buffered killed, basis-trial energies have limits

$$
E_h^{\rm adj}\longrightarrow6a-\nu/3,
\qquad E_h^{\rm sep}\longrightarrow6a.
\tag{63.34}
$$

Proof. All occupied sites are nonroot, so both inherited kinetic diagonals are six. Their root potentials tend to zero. Formula(62.3) gives

$$
G^{\rm c}(L^h,L^{h+1})=\frac13+\frac13\,2^{-(2h+1)},
\qquad
G^{\rm c}(L^h,R^h)=2^{-2h}.
\tag{63.35}
$$

The contained global ball supplies the stated buffers; Lemma63.6 makes the killed/common differences tend to zero. Thus (63.34) follows. Each family of basis vectors is weakly null, but no operator-residual estimate or Weyl eigenvector claim is made. For (63.31), these limits are $-114$ and $6$, while the root pair trial lies strictly below the lower certificate $-114-4\sqrt2$. The retained attraction of the adjacent escape family explains why the one-particle essential threshold alone cannot establish pair binding. $\square$

**Definition 63.13 (consumed methods, new relation and remaining correspondence).** The exact suppliers are §§55.1–55.5 for the same-root carrier, gap and actual contained-ball exhaustion; §§58,60 for the separate ideal transfer/actuator/clock contract and its source-record projection; §§62.2,62.4,62.6 for literal statistics, the same-L pair kernel, killed ordering/update and fixed-$N$ variational recovery. They are consumed, not re-delivered as new results. Teschl's primary min-max theorem, already supplied in §55.8, applies to the bounded self-adjoint operators and their full variational subspaces used here. Its compact-perturbation Weyl theorem is not applied to the noncompact many-particle pair multiplier.

The primary comparisons are Mathieu Lewin, [*Geometric methods for nonlinear many-body quantum systems*, arXiv:1009.2836v3, §3.2, Theorem3.1](https://arxiv.org/pdf/1009.2836v3); Christoph Fischbacher and Günter Stolz, [*Droplet states in quantum XXZ spin systems on general graphs*, arXiv:1712.10276v2, §2.1–2.4](https://arxiv.org/pdf/1712.10276v2); and Jonathan Breuer, Sergey Denisov and Latif Eliaz, [*On the essential spectrum of Schrödinger operators on trees*, arXiv:1711.10049v2, Theorems2–4](https://arxiv.org/pdf/1711.10049v2). Lewin's theorem concerns Euclidean many-body operators, with even pair potential, and both external and pair potentials finite sums of $L^p(\mathbb R^d)$ functions with $\max(d/2,1)<p<\infty$, or $L^\infty$ functions tending to zero at infinity; its cluster-localization method motivates retaining the escaping group's energy, but its formula is not imported to this tree. Fischbacher–Stolz supply the mature symmetric-configuration-graph viewpoint for connected countable bounded-degree graphs; their XXZ potential is not (63.1), whose total-degree diagonal and Green attraction remain literal. Breuer–Denisov–Eliaz distinguish general bounded-degree R-limit inclusion from the regular-tree equality and exhibit failure of the reverse inclusion on a general graph. The $N$-occupation graph is not the one-particle regular tree, so that equality does not supply a sharp threshold here. The partition, tensor-form equality, exterior error and spectral tightness needed for this carrier are proved in (63.7)–(63.12), (63.24)–(63.27). These primary methods require no additional Library supplier for the deduction.

The `repo-derived` relation is the joint chain on the already commissioned source: all fixed-$N$ partial/intact/multiple escape is controlled with vanishing error; an explicit nonempty coupling regime and the actual pair witness force strict separation; this gives attained states, compactness of every near-minimizer, and complete common/killed finite spectral spaces through actual whole-rho exhaustion. The primary comparisons and ordinary calculations do not assert global mathematical priority or exhaustive literature absence.

The existing [same-source three-axis interface, §§10.1–10.6](AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md) already supplies a conditional common $\Pi$ under its full-vector, spanning, common-zero, quadratic-distance/PSD-Gram, at least two independent directions, alternating-bilinear/exact-area/Jacobi, actual orthonormal-probe and finite binary-calibration conditions, with every actual linear generator preserving its hidden kernel. Its seven-value native direction image and its five-dimensional direction-plus-count task retain their scopes. It is a genuine conditional task bridge; it is not an isometry or operator transport from this unit occurrence graph to a Euclidean displacement region. [Local Choice, §§9–10](https://github.com/the-omega-institute/trureturing/blob/f41910858bd5ad5592fae12340cfb62c79a8c673/docs/develop/theory/FIB_ATOM_LOCAL_CHOICE_GEOMETRY.md) adds a separately supplied same-label probe-and-guard contract and preserves its missing joint-statistic and single-archive acquisition boundaries. Neither source supplies or contradicts the configuration localization of this chapter. The Robin dyadic resolvent concerns arithmetic weighted recursion; the KBonacci mixed-tail root-zero cut prices concern their own immutable INITIAL reader and complete-block fees. Their inverses and recursive costs are not identified with occurrence transport by shared notation.

The [finite acquisition correspondence, Atomic Generation Acquisition §12](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#12-不可逆根后的被动切口阶梯容量与原生关系呈现) retains its paid positive-root archive, exact nonadvancing cut port, finite stopping/decoding, protected written records after refusal/closure, aligned actual generation, trusted markers, no unrecorded source change, actual write/protect/retain/query rights, closed strong ports and inclusion of every reply-affecting retained source influence in the service price. It is not unknown-state acquisition or preparation of a spectral state. The ideal known occupation preparations in (63.30)–(63.35) consume §62's paid premise; they do not grant ground-state preparation, unknown-source copies, reset or independent sampling.

All infinite quantifiers describe common mathematical operators and families of separately commissioned finite prefixes. A fixed-cap execution can refuse, a stopped source has no later event, and there is no Read after an infinite prefix. The original $\mathcal D_2$ source retains independent arbitrary unbounded $a$, including zero, untagged radius-$7/25$ $b$, destructive actions, joint adversarial/history-dependent errors, source-independent initialization and its actual INITIAL/Read/Stop task. The positive commissioned kinetic parameter in (63.1) is not that actor variable. No extra geometric/quantum controls or physical clock are inferred.

The constants, core size, binding criterion and spectral windows are for each fixed finite $N$. They give neither uniform population/refinement/thermodynamic/continuum control nor a vanishing moving-boundary Green norm, and they do not overturn §62.5's growing-population killed-renewal defect. Full subthreshold eigenspaces are preserved only in certified windows below $B_N$ with common-gap endpoints; (63.29) preserves near-groundspace distance under the supplied ideal law, not global all-energy dynamics or full-phase rho intertwining. Authentic spectral acquisition, operation-/metric-/field-/kinetic-preserving physical transport, calibrated time and matched maintenance/precision/storage prices remain unproved. Local direction dimension, ordered syntax, graph growth/degree, Hilbert dimension and physical cost stay distinct. These ordinary conditional results advance stable native structure on the commissioned carrier; they do not settle Euclidean spatial dimension three or the whole why-three objective.

## 63.99 追加锚（本行以下为增补区）

## 64. Same-source Green channels and the retained one/two-occupation response

**Definition 64.1 (the joint source witness and the two pair laws).** Use the actual INITIAL
$t=\langle\beta,\alpha\rangle$ and the fixed-cap history of Proposition55.6:
\[
\operatorname{Read}[BA];\quad \rho[\mathrm{accept}];\quad
\operatorname{Read}[A+B];\quad \rho[\mathrm{refuse}];\quad
\operatorname{Read}[A+B];\quad \operatorname{Stop}.
\]
The leaf counts are $2,3,5$; the second candidate is refused and supplies no candidate
Read. The accepted current domain is, in the ordered basis
\[
D=(o,L,R,LL,LR),
\]
the same five-site domain of §§55,60,62, with the same source version, labels, reference,
clock and retained original records. In particular, no source state, event, or later Read is
created by the calculations below.

The ten unordered H3 pair targets are retained together. The common field law of
(62.3) gives
\[
\begin{array}{c|cccccccccc}
\{p,q\}&oL&oR&oLL&oLR&LR&L\,LL&L\,LR&R\,LL&R\,LR&LL\,LR\\ \hline
G^{\rm c}(p,q)&
1/2&1/2&1/4&1/4&1/4&3/8&3/8&1/8&1/8&3/16
\end{array}
\]
and direct inversion of the actual $L_D$ gives
\[
\begin{array}{c|cccccccccc}
\{p,q\}&oL&oR&oLL&oLR&LR&L\,LL&L\,LR&R\,LL&R\,LR&LL\,LR\\ \hline
G^{\rm k}_D(p,q)&
9/26&7/26&3/26&3/26&3/26&5/26&5/26&1/26&1/26&5/78 .
\end{array}
\]
Here $G^{\rm c}(p,q)=\langle e_p,L^{-1}e_q\rangle$ is the one common field restricted
to $D$, whereas $G_D^{\rm k}(p,q)=\langle e_p,L_D^{-1}e_q\rangle$ is the separately
solved killed pair law. Both use the same $\phi(p)=2^{-|p|}$ in the one-body term. The
common field is not replaced by $\phi_D^0$, and neither pair table changes the original
source or its history.

**Lemma 64.2 (a three-channel one-calibration metric floor).** Let $x,y,o$ be three
distinct points in an injectively metrized space, and suppose one positive calibration
$\kappa$ is used for all three pair readings,
\[
\widehat G(p,q)=\frac{\kappa}{d(\iota p,\iota q)}.
\]
If $w,u,v>0$, $w=G(o,o)$, $G(o,x)=wu$, $G(o,y)=wv$, and $G(x,y)=wuv$ with
$u+v<1$, then the maximum relative error on these three readings obeys
\[
\max_{pq\in\{ox,oy,xy\}}
\frac{|\widehat G(p,q)-G(p,q)|}{G(p,q)}
\ \ge\ \frac{1-u-v}{1+u+v}.                                      \tag{64.1}
\]
If the error is measured in the Green units themselves, then
\[
\max_{pq}|\widehat G(p,q)-G(p,q)|
\ \ge\delta(A,B,C),\qquad
\delta(A,B,C)=\frac{2(A+B-C)-\sqrt{4(A+B-C)^2-12(AB-C(A+B))}}{6},
\tag{64.2}
\]
where $A=G(o,x)$, $B=G(o,y)$, and $C=G(x,y)$.

Proof. Put $r_{pq}=\kappa/\widehat G(p,q)$. The metric triangle inequality is
$r_{xy}\le r_{ox}+r_{oy}$. For $\epsilon\ge1$ the claimed lower bound is immediate. Under a relative error $0\le\epsilon<1$, the most favorable
choice for this inequality has $\widehat G(x,y)=(1+\epsilon)wuv$ and
$\widehat G(o,x),\widehat G(o,y)$ equal to $(1-\epsilon)wu,(1-\epsilon)wv$.
Therefore
\[
\frac1{(1+\epsilon)uv}\le\frac1{(1-\epsilon)u}
+\frac1{(1-\epsilon)v},
\]
which is equivalent to (64.1). For an additive error at most $\delta$, the favorable
endpoints are $x_1=A-\delta$, $x_2=B-\delta$, $x_3=C+\delta$; positivity holds at the
smaller root below. The reciprocal triangle inequality is
$x_3\ge x_1x_2/(x_1+x_2)$. Equality gives
\[
3\delta^2-2(A+B-C)\delta+\bigl(AB-C(A+B)\bigr)=0,
\]
and the smaller root is (64.2). No choice of the common $\kappa$ or of the three
distances can evade this argument. $\square$

**Theorem 64.3 (the actual H3 joint defect).** For the common table choose
$(x,y)=(LL,R)$. Then $(w,u,v)=(1,1/4,1/2)$, and (64.1) gives
\[
\epsilon_{\rm c}\ge\frac17,\qquad
\delta_{\rm c}\ge\frac{5-\sqrt{19}}{24}.
\tag{64.3}
\]
For the killed table the same source triple has
$(w,u,v)=(21/26,1/7,1/3)$, and therefore
\[
\epsilon_{\rm k}\ge\frac{11}{31},\qquad
\delta_{\rm k}\ge\frac{9-4\sqrt3}{78}.
\tag{64.4}
\]
The three entries $(o,LL),(o,R),(LL,R)$ are one joint defect: they are not three
independently fitted sector marginals. The other seven entries in Definition64.1 remain
part of the same source-qualified target.

Proof. In the common case $(A,B,C)=(1/4,1/2,1/8)$, and in the killed case
$(A,B,C)=(3/26,7/26,1/26)$. Substitution in (64.2) gives (64.3) and (64.4);
the relative forms follow from (64.1). The source, calibration and pair law are held
fixed across all three channels. $\square$

**Theorem 64.4 (the defect survives a consistent one/two-occupation operator law).**
Let $h_D=aL_D-gM_{\phi|D}$ and let $P_{D,2}$ be the hard-core symmetric projection
inside the two-fold symmetric tensor of $\ell^2(D)$. For one common calibration
$\widehat G$ on all ten pairs, define
\[
\widehat H_{D,1}=B,\qquad
\widehat H_{D,2}=P_{D,2}\,d\Gamma(B)\,P_{D,2}
-\nu\sum_{\{p,q\}}\widehat G(p,q)n_pn_q,
\]
where $B$ is any Hermitian one-body law and $\nu\ge0$ is the same coefficient used
in the source operator. For either $\diamond\in\{\mathrm c,\mathrm k\}$, put
\[
H^\diamond_{D,1}=h_D,\qquad
H^\diamond_{D,2}=P_{D,2}\,d\Gamma(h_D)\,P_{D,2}
-\nu\sum_{\{p,q\}}G_D^\diamond(p,q)n_pn_q .
\]
The compression keeps the diagonal $\sum_{p\in S}d_p$ and hence every inherited
collision and exterior-killing contribution of (62.2). With
\[
E_1=\|B-h_D\|,\qquad E_2^\diamond=
\|\widehat H_{D,2}-H^\diamond_{D,2}\|,
\]
one has
\[
E_2^\diamond+2E_1\ \ge\
\nu\max_{\{p,q\}\subset D}|\widehat G(p,q)-G_D^\diamond(p,q)|
\ \ge\ \nu\delta_\diamond .                              \tag{64.5}
\]
Consequently a same-$L_D$ installation has $E_1=0$ and $E_2^\diamond\ge\nu\delta_\diamond$
for both pair prescriptions. At $N=1$ the pair multiplier vanishes, so the two
prescriptions have exactly the same one-occupation operator $h_D$.

Proof. On a pair basis vector $e_{\{p,q\}}$, the diagonal pair difference is
$-\nu(\widehat G(p,q)-G_D^\diamond(p,q))$. The norm of the hard-core compression of
$d\Gamma(B-h_D)$ is at most $2E_1$. Taking the largest diagonal entry and applying the
triangle inequality gives the first inequality. The second is Theorem64.3. This argument
uses the full ten-pair diagonal and the same $B,\widehat G$ in both sectors; fitting a
different one-body or pair calibration in the two sectors would not be the stated
operator law. $\square$

**Definition 64.5 (one producer measure and its actual collision domain).**
For every authentic nonempty finite $D$, let $X_D$ have one unit cable for each
inherited seam and two distinct unit grounded stubs at each current leaf. The
outer stub ends have zero trace and no atomic mass. Every actual port has atomic
mass one; every open cable has the same mass density $0<\delta\le1$. Thus
\[
\mu_\delta=\sum_{p\in D}\delta_p+\delta\sum_{e\in\mathcal E_D}dx_e,
\qquad \mathcal K_{D,1}=L^2(X_D,\mu_\delta).
\tag{64.6}
\]
Here $\delta_p$ is a Dirac measure, distinct from the cable density $\delta$.
Stub incidence plus actual seam incidence is exactly $d_p$, including $d_o=2$.
Neither degrees nor source operators are recalibrated with $\delta$.
If $d=|D|$, the full binary source has $d-1$ internal seams and $d+1$
grounded stubs, hence $2d$ unit cables. The retained one-position measure has
total mass $d+2d\delta$. Before exchange restriction, the two-position account
has $d(d-1)$ atomic coordinates, $4d^2$ atom/cable slices and $4d^2$
cable/cable cells, with norm weights $1,\delta,\delta^2$. Each of the $2d$
same-cable cells is dissected, not removed. Thus its total measure is
$d(d-1)+4d^2\delta+4d^2\delta^2$. These are storage measures and stratum
counts, not physical masses, finite mode counts or a price formula; every
interval and cell retains its entire infinite-dimensional function space.

For two identical particles take the symmetric part of
$L^2((X_D\times X_D)\setminus\Delta,\mu_\delta\otimes\mu_\delta)$, where
$\Delta=\{(x,x):x\in X_D\}$ is the actual same-position set. In particular the
positive-mass atomic states $(p,p)$ are absent. Keep all atom/cable and cable/cable
strata. A same-cable square is dissected into $x<y$ and $x>y$; both collision
traces are zero. Different-cable rectangles are retained, including cables incident
at the same port. Write this Hilbert space as $\mathcal K_{D,2}^{\rm hc}$.
It is a genuine two-position space on $X_D$, with exchange symmetry and no ordering
sign. It is not a graph whose vertices are occupation labels.

The form domain $\mathcal Q_{D,1}$ consists of cable $H^1$ functions with endpoint
traces equal to the corresponding atomic port values, and zero grounded traces.
The domain $\mathcal Q_{D,2}$ consists of symmetric, piecewise $H^1$ functions on
all rectangles and dissected triangles, and $H^1$ functions on all atom/cable
slices, with the following trace equalities. A rectangle's boundary at a port
is the corresponding atom/cable slice; that slice's endpoint is the corresponding
atomic pair value. Set the missing atomic value $(p,p)$ to zero in these endpoint
conditions. Grounded ends give zero traces in either coordinate. Both traces on
each same-cable diagonal are zero. These requirements also cover collision at a
shared vertex approached along different incident cables: the incident slices end
at the same zero atomic collision value. No pointwise trace of an arbitrary
rectangle $H^1$ function at its corner is assumed.

Let $k_{\delta,1}(F)=\sum_e\int|F'_e|^2$. For $N=2$, using ordered coordinates
before restriction to the symmetric space, put
\[
\begin{split}
k_{\delta,2}(F)={}&
\sum_{e\in\mathcal E_D,\ q\in D}\int|\partial_xF(e,x;q)|^2dx
+\sum_{p\in D,\ e\in\mathcal E_D}\int|\partial_yF(p;e,y)|^2dy\\
&+\delta\sum_{e,f\in\mathcal E_D}\int_{e\times f}
 (|\partial_xF|^2+|\partial_yF|^2)dxdy .
\end{split}                                                    \tag{64.7}
\]
For $e=f$ the last integral is over both triangles. The corresponding norm has
weights $1,\delta,\delta^2$ on atomic pairs, slices and cells respectively. Formula
(64.7) is the sum of the same one-coordinate cable derivative forms integrated
against the other coordinate's measure. Hard-core conditions change its domain,
not its kinetic coefficient. This conditional producer choice replaces the
unrestricted $\operatorname{Sym}^2d\Gamma(T)$ domain; it is not a new native control.

Let $A_{\delta,D,N}$ be the operator associated with $a k_{\delta,N}$ on this domain.
Define $\phi_A$ to equal $\phi(p)$ at port $p$ and zero on open cables. Use the bounded
real multiplication operators
\[
\begin{aligned}
U^\diamond_{D,1}(x)&=-g\phi_A(x),\\
U^\diamond_{D,2}(x,y)&=-g(\phi_A(x)+\phi_A(y))
-\nu\mathbf1_{x=p,y=q\in D,\ p\ne q}G_D^\diamond(p,q),\\
\mathcal T^\diamond_{\delta,D,N}&=A_{\delta,D,N}+U^\diamond_{D,N}.
\end{aligned}                                                    \tag{64.8}
\]
The pair multiplier has the same value on $(p,q)$ and $(q,p)$ and is zero on other
strata. The one-body potential is additive even on mixed strata. All ten actual
coefficients of Definition64.1 are used, including $G^{\rm c}(LL,LR)=3/16$.
This explicitly declared atomic interaction is a mathematical supplier choice;
a physical field-mediated force or its switching mechanism is not inferred.

**Lemma 64.5a (closed forms and invariant literal hard-core statistics).**
The forms in (64.7) are densely defined, nonnegative and closed. Operators (64.8)
are self-adjoint and semibounded. For $N=2$ their full unitary evolution preserves
$\mathcal K_{D,2}^{\rm hc}$ and its form domain $\mathcal Q_{D,2}$. Thus any
admissible finite-energy input has zero atomic double occupation and zero
same-cable collision trace throughout evolution, for every finite clock value.

Proof. For fixed $\delta>0$, the sum of the weighted norm and derivative norm is
an equivalent direct-sum $H^1$ norm on the finitely many intervals, rectangles
and triangles, with their atomic coordinates. Endpoint, boundary and diagonal
trace maps are continuous into their respective finite-dimensional or $L^2$
trace spaces. All stipulated equalities therefore define a closed subspace.
For density, first approximate a cell function by a smooth function supported
away from every boundary, including the diagonal. For prescribed atomic data,
use linear endpoint bumps of width $h<1/2$ on each incident cable. Lift a pair
value by the products of its two endpoint bumps. On a same-cable square use
$u(p,q)[\theta_p(x)\theta_q(y)+\theta_q(x)\theta_p(y)]$; the two endpoint supports
are disjoint, so its collision trace is zero. Slice traces match these products,
with zero at collision and ground corners. Their additional slice and cell
masses tend to zero as $h\to0$, while each positive-width function has finite
energy. To approximate a slice independently, take its desired function compactly
supported away from its endpoints, then extend it into each incident cell by an
endpoint bump in the other coordinate. Choose the bump width smaller than the
slice's distance from its endpoints; this also avoids the same-cable diagonal.
The additional cell mass tends to zero. There are finitely many strata, so these
three constructions approximate arbitrary Hilbert data. Exchange averaging
preserves the conditions and proves density in the symmetric space. Bounded real $U$ is a bounded self-adjoint perturbation of
the represented operator, with unchanged form domain and lower bound
$-M_N$, where
\[
M_N=Ng+\binom N2\nu/\lambda,\qquad N=1,2.
\]
Here $G_D^\diamond(p,q)\le\lambda^{-1}$ is the supplied same-source bound (62.4).
The positive form of $\mathcal T+M_N+1$ has domain $\mathcal Q_{D,N}$ and obeys
\[
a k_{\delta,N}(F)+\|F\|^2
\le \| (\mathcal T+M_N+1)^{1/2}F\|^2
\le a k_{\delta,N}(F)+(2M_N+1)\|F\|^2.
\]
Its spectral calculus commutes with the full unitary evolution and preserves
this square-root norm, proving form-domain invariance even though multiplication
by the atomic potential need not itself preserve the trace equalities.
Atomic collision coordinates
are absent in that space and continuum collision traces vanish in that domain.
This is invariance of the actual producer state, without deleting any evolved
output or applying a clean-state projection. $\square$

**Lemma 64.5b (the source diagonal, a uniform fast-state bound and a trial lift).**
Let $R_N$ restrict a producer vector to its atomic distinct-port coordinates,
identified with $\mathscr H_{D,N}$; let $J_N=R_N^*$ be the atomic injection. For
$N=2$ the ordered atomic values are
$u(p,q)=f(\{p,q\})/\sqrt2$ for $p\ne q$, and $u(p,p)=0$.
Then $\sum_{p,q}|u(p,q)|^2=\|f\|^2$. Write $K_{D,1}=L_D$ and take $K_{D,2}$
literally from (62.2). For every form vector,
\[
k_{\delta,N}(F)\ge\langle R_NF,K_{D,N}R_NF\rangle,
\qquad
R_NZ=0\ \Longrightarrow\ \|Z\|^2\le9\delta k_{\delta,N}(Z).
\tag{64.9}
\]
There is a linear symmetric form-domain lift $I_N$ with $R_NI_N=I$ such that
\[
\begin{aligned}
k_{\delta,1}(I_1f)&=\langle f,L_Df\rangle,
&\|I_1f-J_1f\|^2&\le\tfrac32\delta\|f\|^2,\\
0\le k_{\delta,2}(I_2f)-\langle f,K_{D,2}f\rangle&\le18\delta\|f\|^2,
&\|I_2f-J_2f\|^2&\le(3\delta+\tfrac94\delta^2)\|f\|^2.
\end{aligned}                                                    \tag{64.10}
\]
All constants are independent of the finite source, cap, boundary and installed $D$.

Proof. An interval with endpoint values $v,w$ has derivative energy at least
$|v-w|^2$. Apply this to every slice, using zero at grounded ends and at an
occupied endpoint. The resulting sum is exactly the symmetric compression of
$L_D\otimes I+I\otimes L_D$: the hopping coefficient is $-1$ on every allowed
move, while the diagonal is $d_p+d_q$. A blocked hop has a zero collision
endpoint and contributes its killing energy; it does not disappear with the hop.
Grounded stubs similarly retain every exterior contribution. This proves the
first inequality, including the normalization factors. For $N=1$ the same
argument gives the original $L_D$.

For $R_NZ=0$, each slice has zero endpoints, so
$\int|Z|^2\le\int|Z'|^2$ by the fundamental theorem of calculus and
Cauchy--Schwarz. A same-cable function with zero traces on both diagonals glues
to an $H^1$ function on the square; no derivative delta mass is introduced.
On any square, choose its first cable's endpoint $v_e$, and use
\[
\int_{e\times f}|Z|^2\le
2\int_f|Z(v_e,y)|^2dy+2\int_{e\times f}|\partial_x Z|^2dxdy.
\]
The boundary term is zero if $v_e$ is grounded. Otherwise a port is chosen at
most three times, since its total incidence is at most three. Summing with mass
$\delta^2$, and adding all slice masses $\delta$, bounds the norm by
$(\delta+6\delta^2)$ times the slice derivative energy plus $2\delta$ times the
cell part of (64.7). This is at most $9\delta k_{\delta,2}(Z)$ for $\delta\le1$.
The one-particle bound is smaller. This proof counts every slice and cell, rather
than assuming that the continuum modes have been removed.

For the trial lift, interpolate every one-particle cable linearly. For two
particles interpolate each atom/cable slice linearly from its atomic endpoints.
On distinct-cable rectangles use bilinear interpolation of the four atomic corner
values, treating ground and collision corners as zero. On a same-cable square
with distinct port endpoints $p,q$, use
\[
(I_2f)_{ee}(x,y)=u(p,q)|x-y| .
\]
On a stub's same-cable square this is zero. The slice boundary values match,
both collision traces vanish, and the lift is symmetric. It has the exact source
slice energy just proved. For a rectangle with corners $v_{ij}$, convexity gives
$\int|I_2f|^2\le\tfrac14\sum_{ij}|v_{ij}|^2$ and
$\int|\nabla I_2f|^2\le2\sum_{ij}|v_{ij}|^2$. On a same-cable square the respective
integrals are $|u(p,q)|^2/6$ and $2|u(p,q)|^2$, obeying the same upper bounds.
A given ordered atomic corner occurs at most $d_pd_q\le9$ times. Each coordinate's
slice norm is at most $\tfrac12\sum_{p,q}d_p|u(p,q)|^2\le\tfrac32\|f\|^2$.
Summing these exact integrals proves both two-particle bounds. For one particle
integration gives $I_1^*I_1=I+\delta(D_D/3+A_D/6)$, whose continuum Gram norm is
at most $3/2$. $\square$

**Theorem 64.6 (admissible harmonic calibration and the missing operator relation).**
For each $N=1,2$ and $f\in\mathscr H_{D,N}$, let $E_Nf$ minimize $k_{\delta,N}$
over all form vectors with $R_NF=f$. Put
\[
\begin{aligned}
\langle f,B_Nh\rangle&=k_{\delta,N}(E_Nf,E_Nh),\\
F_N&=E_N^*E_N=I+(E_N-J_N)^*(E_N-J_N),\\
S_N&=F_N^{-1/2},\qquad W_N=E_NS_N,\\
\beta_1&=\sqrt{3\delta/2},\qquad
\beta_2=\sqrt{3\delta+9\delta^2/4}+9\sqrt2\,\delta.
\end{aligned}                                                    \tag{64.11}
\]
These are supplied preparation/identification maps defined by the same measure
and form rule, with no fit of a separate kinetic scale, potential, pair coefficient
or clock in either sector. They are independent of $g,\nu$ and the pair choice.
They satisfy
\[
\begin{gathered}
R_NE_N=I,\qquad W_N^*W_N=I,\qquad
\|E_N-J_N\|\le\beta_N,\\
B_1=L_D,\qquad 0\le B_2-K_{D,2}\le18\delta I,\qquad
A_{\delta,D,N}E_N=J_NaB_N.
\end{gathered}
\]
In particular $W_Nf$ lies in the actual operator domain of (64.8), has full norm
$\|f\|$, and is an admissible finite-energy hard-core preparation. Its calibration
mixes distinct-port data only; it cannot produce an atomic collision. Its kinetic
preparation energy has the uniform bound
\[
a k_{\delta,N}(W_Nf)\le a(6N+18\delta\mathbf1_{N=2})\|f\|^2,
\]
since $\|K_{D,N}\|\le6N$ and $\|S_N\|\le1$.

Proof. On the closed form subspace $Z_N=\ker R_N$, (64.9) makes $k$ an equivalent
complete form norm. Solve
$k(z,v)=-k(I_Nf,v)$ for $v\in Z_N$ by the Hilbert-space representation theorem,
and set $E_Nf=I_Nf+z$. This gives existence, uniqueness, linearity and
$k(E_Nf,Z_N)=0$, as well as the minimum. Exchange symmetry is retained in this
construction. Comparing the minimum with the first inequality in (64.9) and with
(64.10) proves the two matrix bounds for $B_N$. In particular
\[
k_{\delta,2}(E_2f-I_2f)
=k_{\delta,2}(I_2f)-k_{\delta,2}(E_2f)\le18\delta\|f\|^2.
\]
This difference has zero atomic values. The fast-state bound (64.9) therefore gives
$\|E_2f-I_2f\|\le9\sqrt2\,\delta\|f\|$. Combine it with the trial norm in (64.10)
to obtain $\beta_2$. For one particle the linear lift already annihilates $Z_1$
in the kinetic form, so $E_1=I_1$ and $\beta_1$ follows. Orthogonality of atomic and
continuum strata gives the formula for $F_N$; thus $S_N$ exists and $W_N$ is an
isometry into the whole retained space.

Every form test $v$ decomposes as $E_NR_Nv+(v-E_NR_Nv)$, with its second term in
$Z_N$. Hence
\[
a k_{\delta,N}(E_Nf,v)=\langle aB_Nf,R_Nv\rangle
=\langle J_NaB_Nf,v\rangle .
\]
The defining operator criterion for a closed form proves the displayed operator
identity and puts $E_Nf$, and therefore $W_Nf$, in $\operatorname{Dom}(A)$.
The bounded potential does not change that operator domain. This is the needed
input/domain/operator relation, proved on the untruncated continuum. Merely
imposing a named barrier or interpolating a collision-free trial would not prove
this relation: the trial $I_2$ need not itself satisfy the operator criterion.
$\square$

**Theorem 64.7 (homogeneous full retained-state finite-horizon correspondence).**
For every authentic finite installed $D$, both prescriptions, $N=1,2$, and every
$f\in\mathscr H_{D,N}$, define
\[
\begin{aligned}
C_N&=6aN+M_N,\qquad s_N=1-(1+\beta_N^2)^{-1/2},\\
r_N&=18a\delta\mathbf1_{N=2}+2C_Ns_N+\beta_N(C_N+M_N).
\end{aligned}
\]
For every declared $T<\infty$ and every $|\tau|\le T$,
\[
\left\|e^{-i\tau\mathcal T^\diamond_{\delta,D,N}}W_Nf
-W_Ne^{-i\tau H^\diamond_{D,N}}f\right\|
\le |\tau|r_N\|f\|\le Tr_N\|f\| .                    \tag{64.12}
\]
This norm includes every atomic, mixed and continuum component and every phase.
An initial admissible component $z\in\mathcal Q_{D,N}$ with $\|z\|\le\eta$ adds
at most $\eta$, without any orthogonality assumption or reset. For fixed
$a,g,\nu,T$ the bound tends to zero with $\delta$, uniformly over all finite
installed $D$ and both fixed populations. It is not uniform over unbounded
population or unbounded horizon. Decreasing $\delta$ changes storage mass at
fixed unit seam lengths; no mesh, thermodynamic or physical-mass limit is supplied.

Proof. Write $V_N=H^\diamond_{D,N}-aK_{D,N}$. The multiplier in (64.8) satisfies
$U J_N=J_NV_N$, $\|U\|,\|V_N\|\le M_N$, and
$\|H^\diamond_{D,N}\|\le C_N$. Set $Q_N=E_N-J_N$ and
$D_N=a(B_N-K_{D,N})$. The exact operator identity of Theorem64.6 gives
\[
\mathcal T W_N-W_NH
=J_N[H,S_N]+J_ND_NS_N+UQ_NS_N-Q_NS_NH .
\]
Since $\|S_N\|\le1$, $\|S_N-I\|\le s_N$ and
$\|D_N\|\le18a\delta\mathbf1_{N=2}$, its norm is at most $r_N$.
For the entire finite target space $W_Nf\in\operatorname{Dom}(\mathcal T)$, so
integrating the exact derivative of
$e^{-i(\tau-s)\mathcal T}W_Ne^{-isH}f$ is justified. Unitarity gives (64.12),
including its factor $\|f\|$. An initial $z$ contributes exactly its preserved
norm bound. The constants use only total incidence at most three and the common
Green bound, not the number or shape of sites. $\square$

There is one density choice for the whole joint approximation, without a
sector-specific fit. For $0<\delta\le1$, $\beta_N\le16\sqrt\delta$ and
$s_N\le\beta_N^2/2\le128\delta$. Put
\[
M=2g+\nu/\lambda,\qquad C=12a+M,\qquad
R=18a+256C+16(C+M).
\]
Then $r_N\le R\sqrt\delta$ for both $N=1,2$ and both pair prescriptions,
on every authentic finite $D$. For a declared $T>0$ and absolute unit-input
tolerance $\varepsilon>0$, any single
$0<\delta\le\min\{1,(\varepsilon/(TR))^2\}$ gives error at most
$\varepsilon\|f\|$ throughout the horizon. At $T=0$ every declared density
works. This is a common mathematical storage/preparation choice, not a native
density control or a finite-price preparation procedure.

For a singleton $D=\{o\}$ both grounded stubs remain and $B_1=[2]$.
The target $\mathscr H_{D,2}$ is the zero space, so $E_2,W_2$ are its unique zero
maps and (64.12) holds for its zero input. The full two-position cable space still
exists and all its modes are retained; an auxiliary initial state there is covered
by its $\eta$ budget. No unit two-port preparation is commissioned when $|D|<2$.
This treats the degenerate finite domain without excluding that source. Zero
$\nu$, zero comparison time, identical-domain alpha-to-beta versions and every
finite source boundary are included. The strictly positive commissioned $a$ is
independent of the original actor's arbitrary unbounded parameter, including zero.

A supplied zero-generator reference branch may be adjoined by direct sum, using
$0\oplus\mathcal T$, $0\oplus H$ and $I\oplus W_N$; tensoring supplied retained
registers with identity gives the same bound. This keeps relative reference phase
and the same comparison clock, with no phase quotient. Unknown joint reference
preparation remains a separate permission. The joint object retains all original
classical records. Unused address-bank modes and the $c,u,v$ and supplied clock/
reference registers remain explicit full auxiliary factors with their stipulated
identity holds; (64.12) also holds for target inputs entangled with those factors.
The active target is transported through $W_N$, without preparing a second copy.
Their construction,
preparation, storage, hold and any error budgets are additional resources; (64.12)
does not supply them or replace §62's actual digital circuit by a cable device.

**Proposition 64.8 (source discriminators and the retained mathematical boundary).**
The finite form account is source qualified. Its one-coordinate lift gives exactly
$L_D$, so §55's hidden vector and §60's mirrored-source operator distinction
remain full-vector target identities. Its slice form is the literal symmetric
$K_{D,2}$, including the six-move sign and trace discriminator (62.34); no
fermionic or determinantal replacement is made. Either full pair multiplier is
$V_N$ on the same atomic data. A shared inverse-distance replacement is therefore
still subject to (64.5), independently of the vanishing cable-density error.

The unrestricted symmetric generator fails on the same adjacent input:
\[
(I-P_{D,2})d\Gamma(h_D)e_{\{o,L\}}
=-\sqrt2a(e_{o,o}+e_{L,L}),\qquad\text{norm }2a.
\]
Those positive-mass output states are absent in the producer domain of Definition64.5,
and the admitted $W_2e_{\{o,L\}}$ has zero collision traces at preparation and
throughout its actual evolution by Lemma64.5a. In particular for the actual H3
source, $a=g=1$, $\nu=0$, $\delta=10^{-8}$, $T=10^{-2}$, the elementary bounds
$\beta_2<1/5000$, $s_2\le\beta_2^2/2$ give
\[
Tr_2<\frac1{100}
 \left(\frac{18}{10^8}+\frac{14}{5000^2}+\frac{16}{5000}\right)
<\frac1{30000}.
\]
For input norm 100 this bound is multiplied by 100. This tests the identical
finite-clock source counterexample against the repaired construction, in its
whole retained norm. The bound rests on the analytic operator proof, not a
finite cable-mode simulation. Atomic double occupation is exactly zero, rather
than a discarded component of this error budget.

For an already commissioned target contraction $C$, its mathematical transport
is $CW_N^*$ on the whole producer space. Its norm is at most one and
\[
\|CW_N^*e^{-i\tau\mathcal T}W_Nf-Ce^{-i\tau H}f\|
\le |\tau|r_N\|f\|,
\]
by $W_N^*W_N=I$ and (64.12). An already commissioned target effect
$0\le F\le I$ transports to $W_NFW_N^*$; for unit inputs its probability
error is at most $2|\tau|r_N$. Thus the hidden-vector, mirrored-source and
relative-phase target tests of §§55,58,60 and the literal-statistics test of §62
can be checked on their supplied known inputs during an actual installed idle
interval. The full-state theorem still accounts for all components outside the
calibrated range. These target maps neither add an original numerical Read nor
supply physical measurement, acquisition, or a transfer between cable spaces.

The common pair field is the supplied static restriction of $L^{-1}$.
Both installed amplitude targets use $L_D$ and the same common $\phi$.
No common exterior amplitude-memory target is inferred from the common static
pair table. A separately commissioned common exterior dynamic response would
need its full retained exterior state and further calibration.

The mathematical producer must supply the forms, all atomic and cable masses,
the correlated harmonic preparations $W_Nf$, and the full retained evolution.
Preparing $W_2f$ is not obtained by tensoring independently prepared $W_1$ modes.
The variational construction proves an admissible state and its correspondence;
it is not a finite-price native preparation algorithm or acquisition of unknown
coefficients. The domain conditions and atomic interaction are conditional
realization choices within this contract, with no claim that native or physical
rights implement them. Replacing grounded stubs at a renewal changes these
continuum domains: (64.12) is a uniform theorem on each installed idle interval,
not an unproved full-state switch between cable spaces. A physical switching,
renewal transfer or nonidentity hold needs its own supplied law and error/price.

Unpaid obligations remain: an operation- and metric-preserving displacement map,
isotropy and a physical three-dimensional local realization; field-mediated force
and its actual implementation; switching, renewal, acquisition and unknown-state
ingress; same-reference preparation and calibrated physical time; finite precision,
all auxiliary modes/masses, storage, retention, production, maintenance and total
price. The original $\mathcal D_2$ independent arbitrary unbounded $a$ including
zero, untagged radius-$7/25$ $b$, destructive actions, joint adversarial/history-dependent
errors, source-independent initialization and actual INITIAL/Read/refusal/Stop
remain unchanged. The conditional $\Pi$ and paid promised-family acquisition
retain all their existing hypotheses and rights. No source copy, reset,
independent resampling, exact limit Read or new native geometric/quantum control
is inferred. Nothing here selects spatial dimension three, supplies a physical
realization, validates a kernel or completes the broader goal.

**Definition 64.9 (exact suppliers and ordinary-proof scope).**
The exact source suppliers are §§55.1–55.6 for the actual source, $L_D$, common
field and grounded boundary; §§58,60 for source/record/clock ownership and the
complete retained target; §§62.1–62.4 for literal symmetric statistics and both
pair laws; and legacy §52.7 for the distinct Euclidean point-source contract.
Chapter63's already completed binding/escape/spectral results are inherited;
none is claimed as another accomplishment here.

Bolte--Kerner, [*Quantum graphs with two-particle contact interactions*,
arXiv:1207.5648v1, Definition3.1 and Proposition3.2](https://arxiv.org/pdf/1207.5648v1),
supplies the mature diagonal-Dirichlet hard-core form method on a finite compact
metric graph with Lebesgue edge-product measure. Its boundary maps $P,L$ are
bounded and measurable, $P$ is an orthogonal projection, and $L$ is self-adjoint
on $\ker P$; contact and vertex blocks are separated. Hard-core contact chooses
$P_{\rm contact}=I$, $L_{\rm contact}=0$. Its delta-type Lipschitz strength is a
different case. Proposition3.2 supplies closed semibounded forms, not automatic
$H^2$ operator regularity; that further identification in Proposition3.3 requires
additional regularity. It supplies neither atomic port masses, the mixed-stratum
gluing nor this calibrated small-density limit and preparation. Lemmas64.5a–64.5b
and Theorems64.6–64.7 prove those missing relations directly; no supplier theorem
is applied outside its conditions. Closed-form representation, Hilbert-space
orthogonal minimization and unitary Duhamel are classical intermediates. No
additional Library note is needed.

Equations (64.1)–(64.5) are ordinary metric/finite-matrix deductions with the full
ten-pair target. Equations (64.6)–(64.12) are a new conditional stratified particle
form, its admissible joint calibration and whole-state operator estimate.
Exact finite checks of source coefficients, slice matrices, collision-free trial
integrals and the stated bounds support the displayed finite identities; they
cannot replace the continuum closedness, minimization or evolution proofs.
These are ordinary repo-derived mathematics, without literature-priority,
fresh Lean/kernel, current CI or physical evidence claims.

## 64.99 追加锚（本行以下为增补区）

## 65. Authentic all-pair obstruction to a homogeneous hyperbolic point-Green law

**Definition 65.1 (separately commissioned sources and their actual history).**
Keep the free nonempty ordered source algebra of [Continuation Definition1.1](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md),
the whole substitution (55.1), and the fixed-cap TM30/PR57 contract used in
Definitions55.1 and60.1. Define a family of original sources by

$$
T_0=\beta,\qquad T_{h+1}=\langle T_h,T_h\rangle,\qquad
B_h=\operatorname{Pos}(T_h)=\{p\in\{L,R\}^*:|p|\le h\}.
\tag{65.1}
$$

The two subtrees in this mathematical definition have distinct ordered occurrences.
Each $T_h$ is a separately supplied INITIAL source, as in Proposition62.5;
(65.1) is not a source-copy operation on a running unknown tree. INITIAL,
labels, brackets, left/right order, the root and all addressed occurrences belong
to the full source. The domain $B_h$ is its actual initial domain, rather than a
ball substituted for an irregular source domain.

For $h\ge3$, fix the public cap $H=2^{h+1}$ before execution. The source-independent
command word $\operatorname{Read};\rho;\operatorname{Read};\rho;
\operatorname{Read};\operatorname{Stop}$ has the actual record

$$
\operatorname{Read}[B^{2^h}];\quad\rho[\mathrm{accept}];\quad
\operatorname{Read}[(BA)^{2^h}];\quad\rho[\mathrm{reject}];\quad
\operatorname{Read}[(BA)^{2^h}];\quad\operatorname{Stop}.
\tag{65.2}
$$

Here $A=E(\alpha)$ and $B=E(\beta)$ are the original Clifford readings,
not spatial coordinates or Green coefficients. Their source relations are
$A^2=1$, $B^2=-1$ and $AB+BA=1$. The initial, first-candidate and
second-candidate leaf counts are $2^h$, $2^{h+1}$ and $3\cdot2^h$.
Equality with the cap is accepted. The rejected candidate produces no candidate
Read, and the following Read is of the unchanged accepted current source.
The accepted domain is $B_{h+1}$, but its depth-$(h+1)$ child labels are
$\beta,\alpha$ at each former beta leaf: this successor is not the separately
commissioned all-beta INITIAL $T_{h+1}$.

In particular $h=3$, $H=16$ gives eight beta leaves and fifteen initial sites.
Writing $S=BA$, the identity $S^2=S+1$ gives $S^8=13+21S$, whereas $B^8=1$.
Thus (65.2) becomes

$$
\operatorname{Read}[1];\quad\rho[\mathrm{accept}];\quad
\operatorname{Read}[13+21BA];\quad\rho[\mathrm{reject}];\quad
\operatorname{Read}[13+21BA];\quad\operatorname{Stop}.
\tag{65.3}
$$

The installed site counts are $15,31,31$; the refused candidate has twenty-four
leaves. In TM30's literal field order the immutable original target is
$q_{16}(T_3)=(1,(0,8),1,13+21BA)$. It is not the boundary of the stopped current
source. These statements follow from the actual ordered leaf substitution and
the complete candidate guard, not from the unlabelled domain alone. For example,
the all-alpha depth-three INITIAL has the same domain $B_3$ and initial Read
$A^8=1$, but its first two candidates have eight and sixteen leaves and are both
accepted. Its readings in the same command word are $1,1,13+21BA$, and its
INITIAL boundary has tag two. An equality of initial geometric domains therefore
does not authenticate the source or its history.

All original source services and charges remain attached. At $H=16$, PR57's
source packet has $2H-1=31$ slots and sixty-two ingress bits; the separately
supplied §62 address bank has $K=2^H-1=65535$ address qubits and $K+4=65539$
total qubits. These different counts retain their original meanings. A Green
coefficient is no additional public Read, and the geometric calculations below
provide no source acquisition, free preparation, cap increase or event after Stop.
The full original menu also retains each named, actually supplied nonempty
Left/Right whole-context request, with its complete candidate guard and actual
response. The witness (65.2) simply chooses whole substitution. An accepted graft
keeps Definition60.1's distinct occurrence injection and ends its commissioned
whole-rho comparison; it is not silently treated as same-address renewal.

**Definition 65.2 (the complete response target and the point-field model).**
Use the unit-conductance, counting-measure rooted occurrence operator $L$ and
its authentic Dirichlet compression $L_D$ from Definitions55.1–55.2. Retain,
separately, the common and killed pair prescriptions of (62.2):

$$
G_D^{\rm c}(p,q)=\langle e_p,L^{-1}e_q\rangle,\qquad
G_D^{\rm k}(p,q)=\langle e_p,L_D^{-1}e_q\rangle,
\qquad p,q\in D.
\tag{65.4}
$$

Neither prescription changes the common one-body field $\phi(p)=2^{-|p|}$.
The inherited root diagonal is two, every other diagonal is three, and every
actual seam has entry $-1$. Missing-child and collision contributions are
retained as in (62.2). There is no added parent seam at the root.

The representation under consideration assigns finite points $x_p$ in the
complete homogeneous hyperbolic space $\mathbb H^3_\ell$ of curvature
$-\ell^{-2}$ and uses

$$
\widehat G_D(p,q)=
\frac{\kappa}{\exp(2d_{\mathbb H^3_\ell}(x_p,x_q)/\ell)-1},
\qquad \kappa>0,\quad\ell>0,\quad p\ne q.
\tag{65.5}
$$

There is one calibration $\kappa$ for the entire table. Both $\kappa$ and $\ell$,
and the whole configuration, may be independently refitted for each source or
installed version. Pair-specific calibration, alteration of prescribed entries
or removal of actual pairs is outside (65.5). At $D=B_3$ the target comprises
all $\binom{15}{2}=105$ unordered off-diagonal pairs, for either choice in (65.4).
Restrictions to eight or five terminal sites below are necessary witnesses for
that full target, not new target domains.

The unscreened, decaying, volume-normalized Laplace–Beltrami point fundamental
solution in this complete homogeneous space is the special case
$\kappa=(2\pi\ell)^{-1}$. Cohl–Kalnins,
[arXiv:1201.4406v1, Theorem3.1, its dimension-three evaluation and Proposition4.1](https://arxiv.org/pdf/1201.4406v1),
supplies this law with precisely those source, operator and exterior conditions.
Indeed the area of a geodesic sphere is $4\pi\ell^2\sinh^2 r$,
$r=d/\ell$; unit flux and decay give
$(4\pi\ell)^{-1}\int_r^\infty\sinh^{-2}u\,du
=(4\pi\ell)^{-1}(\coth r-1)$, which equals (65.5) at that normalization.
Allowing arbitrary positive $\kappa$ enlarges the admissible family, so an
obstruction for (65.5) also obstructs the unit-source subfamily.

Exact positive responses would fix the normalized distances and their candidate
Lorentz Gram matrix by

$$
r_{pq}=\frac12\log\left(1+\frac{\kappa}{G_D^\diamond(p,q)}\right),
\qquad C_{pp}=1,\qquad C_{pq}=\cosh r_{pq}\quad(p\ne q),
\qquad \diamond\in\{\mathrm c,\mathrm k\}.
\tag{65.6}
$$

Thus $\ell$ does not change the normalized dimension test. The diagonal one
in $C$ is hyperboloid normalization. It is not a fitted value of the finite
original $G_D^\diamond(p,p)$: a point-field self-response in (65.5) is singular.
Coincident modeled sites have infinite off-diagonal response and cannot give
a finite-error fit to the positive finite original coefficients.

**Theorem 65.3 (rooted coefficients on the authentic complete domains).**
For terminal addresses $|p|=|q|=h\ge1$, $p\ne q$, put
$k=|p\wedge q|<h$. The two responses are

$$
g^{\rm c}_{h,k}=\frac{2\cdot4^k+1}{3\cdot4^h},\qquad
g^{\rm k}_{h,k}=F_k,
\tag{65.7}
$$

where, for the killed domain $B_h$,

$$
A_d=2^{h-d+1}-1\quad(0\le d\le h),\qquad
F_k=\frac1{2^{h+1}A_0}
+\sum_{r=1}^k\frac1{A_{r-1}A_r}.
\tag{65.8}
$$

More generally, for arbitrary $p,q\in B_h$, including the diagonal, with
$d=|p|$, $e=|q|$ and $k=|p\wedge q|$,

$$
G_{B_h}^{\rm k}(p,q)=A_dA_eF_k.
\tag{65.9}
$$

Each terminal response in (65.7) is strictly positive and strictly increasing
with $k$. At depth three the complete twenty-eight-pair terminal restriction is

| Common-prefix depth $k$ | Number of unordered terminal pairs | $g^{\rm c}_{3,k}$ | $g^{\rm k}_{3,k}$ |
| --- | ---: | ---: | ---: |
| $0$ | $16$ | $1/64$ | $1/240$ |
| $1$ | $8$ | $3/64$ | $23/1680$ |
| $2$ | $4$ | $11/64$ | $103/1680$ |

Proof. The common coefficient is the direct terminal restriction of the already
supplied exact identity (62.3), retaining both its tree-distance term and its
rooted image term. For the killed coefficient, expose the rooted triangular
factorization used in (62.19)–(62.21). Set

$$
s_0=\frac{2^{h+1}}{A_0},\qquad
s_d=\frac{A_{d-1}}{A_d}\quad(1\le d\le h).
$$

For real site coordinates $x$, expansion gives

$$
x^\mathsf TL_{B_h}x
=s_0x_o^2+\sum_{v\in B_h\setminus\{o\}}
s_{|v|}\left(x_v-\frac{x_{v^-}}{s_{|v|}}\right)^2.
\tag{65.10}
$$

Every cross term is $-2x_vx_{v^-}$. At an internal nonroot site of depth $d$,
the diagonal is $s_d+2/s_{d+1}=3$, because
$A_{d-1}=2A_d+1$ and $A_d=2A_{d+1}+1$. At a leaf it is $s_h=3$.
At the root it is $s_0+2/s_1=2$. For $h=0$ the empty sum leaves
$s_0=2$ and $L_{B_0}=[2]$, so the same formula includes the singleton without
an artificial root edge.

Write $x_v=A_{|v|}w_v$. Equation (65.10) then has root coefficient
$2^{h+1}A_0$ on $w_o^2$ and coefficient $A_{r-1}A_r$ on each
$(w_v-w_{v^-})^2$ at depth $r$. The map from $w$ to its root and edge
differences is triangular and invertible. Its inverse expresses $w_p$ as the
sum of those differences along the root-to-$p$ path. Inverting the diagonal
quadratic form therefore gives a matrix entry equal to the sum of reciprocal
coefficients on the shared path, namely $F_{|p\wedge q|}$.
Multiplying by $A_dA_e$ proves (65.9). This is finite algebra on the actual
occurrence operator; no random innovations, resampled source or extra seam
is supplied by the factorization. Since $A_h=1$, (65.7) follows. Positivity
and strict increase follow from the positive summands in (65.8). Substituting
$h=3$ gives the displayed table, and counting the ordered binary clusters gives
its pair multiplicities. $\square$

**Theorem 65.4 (all-calibration terminal inertia and exact distance dimension).**
For either prescription, every finite $h\ge1$ and every $\kappa>0$, the matrix
in (65.6) on the $n=2^h$ terminal sites has inertia

$$
(n_+,n_-,n_0)=(1,n-1,0).
\tag{65.11}
$$

Every restriction to $m\ge1$ distinct terminals has inertia $(1,m-1,0)$.
Consequently its exact normalized hyperbolic distance dimension is $m-1$:
the distances can be realized on a common future hyperboloid sheet in
$\mathbb H^{m-1}$, and cannot be realized in a smaller hyperbolic dimension.
For $m=1$ this means the singleton. In particular any five terminals obstruct
$\mathbb H^3$, whereas every restriction to at most four terminals can be
realized in $\mathbb H^3$. This cardinality statement concerns terminal
restrictions, not arbitrary sets of internal and terminal sites.

Proof. Fix one prescription and write $g_k=g^\diamond_{h,k}$. Define

$$
f(z)=\cosh\left(\tfrac12\log(1+z)\right)-1,
\qquad a_k=f(\kappa/g_k).
$$

Theorem65.3 and strict monotonicity of $f$ on $z>0$ give
$a_0>a_1>\cdots>a_{h-1}>0$. Let $J$ be the all-ones matrix on the
terminals. For $1\le r\le h-1$, let $Q_r$ have entry one when two
addresses have the same first $r$ letters and zero otherwise. It is the sum
of outer products of the depth-$r$ cluster indicators, hence is positive
semidefinite. The exact matrix identity is

$$
C=(1+a_0)J
-\sum_{r=1}^{h-1}(a_{r-1}-a_r)Q_r-a_{h-1}I.
\tag{65.12}
$$

For a distinct pair with common-prefix depth $k$, the sum telescopes to
$1+a_k$; on the diagonal it gives one. Thus, on the zero-sum subspace,

$$
\begin{aligned}
\sum_i z_i=0\quad\Longrightarrow\quad
z^\mathsf TCz
&=-a_{h-1}\|z\|_2^2\\
&\quad-\sum_{r=1}^{h-1}(a_{r-1}-a_r)
\sum_{|u|=r}\left(\sum_{p\text{ below }u}z_p\right)^2
\le-a_{h-1}\|z\|_2^2.
\end{aligned}
\tag{65.13}
$$

The variational characterization of inertia supplies at least $n-1$
strictly negative eigenvalues. Since $\operatorname{tr}C=n>0$, the remaining
eigenvalue is positive and none is zero. Restrict (65.12) to any terminal
subset: its restricted cluster matrices are still positive semidefinite,
and the same argument applies on its $(m-1)$-dimensional zero-sum subspace.
The trace there is $m$, proving the restricted assertion.

For the dimension conclusion, use the classical Lorentz Gram recognition in
Keller-Ressel–Nargang,
[arXiv:1903.08977v2, LemmaA.1 and its proof](https://arxiv.org/pdf/1903.08977v2).
In the sign convention here, points $v_i$ on the unit future hyperboloid have
$C_{ij}=v_i^\mathsf T\operatorname{diag}(1,-I_d)v_j=\cosh r_{ij}$.
Such a Gram matrix has at most one positive and at most $d$ negative
eigenvalues. Conversely a real symmetric matrix with diagonal one, all
off-diagonal entries greater than one and inertia $(1,m-1,0)$ has a real
factorization in that Lorentz space. Each factored row has Lorentz norm one.
Any two rows have positive Lorentz product, so their timelike sheets agree;
a common sign puts all rows on the future sheet. Their geodesic distances
are exactly $\operatorname{arcosh}C_{ij}$, without altering any prescribed entry.
The negative index forces $d\ge m-1$, and the factorization attains equality.
Embedding this hyperboloid as a totally geodesic subspace gives the assertion
for at most four terminals. $\square$

The hierarchical step has mature precedents. The matrix $C-J$, with zero
diagonal and off-diagonal entries $a_{|p\wedge q|}$, is an ultrametric distance
matrix: longer shared prefixes give smaller distances, and in every triple
the largest distance occurs at least twice. Faver et al.,
[arXiv:1201.6669v5, Theorem5.1 and Corollaries5.3–5.5](https://arxiv.org/pdf/1201.6669v5),
supplies strict $p$-negative type for ultrametrics for every $p\ge0$.
The cluster-indicator method is also present in Gorman–Lladser,
[arXiv:2208.09927v1, Definitions1.1–1.2 and equations1.1–1.3](https://arxiv.org/pdf/2208.09927v1),
for strict ultrametric covariance matrices. Equation (65.13) supplies the
explicit margin needed here; it does not infer fixed hyperbolic dimension from
a Hilbert embedding or add the covariance representation's auxiliary root edge
to the occurrence graph.

**Proposition 65.5 (the authentic class obstruction with sourcewise refitting).**
For each separate prescription $\diamond\in\{\mathrm c,\mathrm k\}$, the
INITIAL $T_3$ of (65.3) has no exact realization (65.5) of all its actual pairs,
for every $\kappa>0$ and $\ell>0$. Hence both assertions

$$
\begin{aligned}
&\exists\kappa,\ell>0\quad
\forall\text{ authentic }D\quad\exists(x_p)_{p\in D}\quad
\forall p\ne q\in D\quad \widehat G_D(p,q)=G_D^\diamond(p,q),\\
&\forall\text{ authentic }D\quad
\exists\kappa_D,\ell_D>0\quad\exists(x_p)_{p\in D}\quad
\forall p\ne q\in D\quad \widehat G_D(p,q)=G_D^\diamond(p,q)
\end{aligned}
\tag{65.14}
$$

are false. The admissible $D$ in these quantifiers are actual installed domains
or separately commissioned original finite sources and legal finite versions,
with the full source/history contract of Definition65.1. Even a fresh whole-table
fit for every such source does not remove the obstruction. More generally,
under the same radial transformation (65.6), no fixed finite hyperbolic dimension
realizes this all-beta source class at every depth.

Proof. Every full-domain representation restricts to its eight depth-three
terminals. Theorem65.4 gives seven negative eigenvalues there, whereas a Gram
matrix of $\mathbb H^3$ has at most three. Already the five actual terminals

$$
\mathcal S_5=\{LLL,LLR,LRL,RLL,RRL\}\subset B_3
\tag{65.15}
$$

give inertia $(1,4,0)$. Their ten pairs are a principal restriction of the
original 105-pair target. This contradiction holds for every positive calibration,
and normalized distances make the radius irrelevant to it. Definition65.1
provides this actual source and legal record, so it refutes each universal
assertion in (65.14). For any fixed $d<\infty$, choose a separately commissioned
$T_h$ with $2^h-1>d$ and apply the same negative-index argument. $\square$

The terminal table does have an exact distance realization in
$\mathbb H^{2^h-1}$, by Theorem65.4. This is only a statement about those
terminal distances under (65.6). No full-$B_h$ distance realization in that
dimension is established, and (65.5) is the dimension-three Laplace Green law:
its use as a response-to-distance transform does not make it a Laplace Green
field in dimension $2^h-1$. Edge completion cannot evade (65.14), because all
pairs are already prescribed. In Putinar–Vishwakarma,
[arXiv:2609.10403v1, TheoremsA, B and D, Proposition2.7 and §7.1](https://arxiv.org/pdf/2609.10403v1),
anchored positive-semidefinite rank recognition controls dimension, chordal
completion requires compatible specified clique data, and tree product completion
chooses unspecified pairs while preserving supplied edges. None authorizes
changing this complete table or dropping its fixed dimension requirement.
Likewise the opposite-sign characterization in Tabaghi–Dokmanić,
[arXiv:2005.08672v2, Propositions1–2, §3.1 and AppendixA](https://arxiv.org/pdf/2005.08672v2),
retains both rank constraints: the positive and negative semidefinite parts have
ranks at most $d$ and one, with diagonal $-1$ and entries at most $-1$.
Relaxing rank or projecting a matrix can change prescribed distances and is not
an exact fit of (65.4).

**Theorem 65.6 (strictly positive relative-response floors uniform in calibration).**
For an authentic domain with at least two sites, define the full-table relative
error of (65.5) by

$$
E_D^\diamond=\max_{\{p,q\}\subset D}
\left|\frac{\widehat G_D(p,q)}{G_D^\diamond(p,q)}-1\right|.
\tag{65.16}
$$

Coincident modeled sites give $E_D^\diamond=+\infty$. On $D=B_3$, every
positive $\kappa,\ell$ and every finite configuration in $\mathbb H^3_\ell$
satisfy both the eight-terminal bounds

$$
E_{B_3}^{\rm c}\ge\varepsilon_{{\rm c},8}
:=1-\sqrt{\frac{847}{848}}>0,\qquad
E_{B_3}^{\rm k}\ge\varepsilon_{{\rm k},8}
:=1-\sqrt{\frac{10609}{10616}}>0,
\tag{65.17}
$$

and the stronger five-terminal bounds

$$
E_{B_3}^{\rm c}\ge\varepsilon_{{\rm c},5}
:=1-\sqrt{\frac{484}{485}}>\frac1{970},\qquad
E_{B_3}^{\rm k}\ge\varepsilon_{{\rm k},5}
:=1-\sqrt{\frac{42436}{42485}}>\frac{49}{84970}.
\tag{65.18}
$$

The respective restriction errors on the eight terminals or on $\mathcal S_5$
already obey the displayed bound. These are certified uniform lower bounds,
not identified optimal minimax errors.

Proof. For the function $f$ in Theorem65.4, put $u=\sqrt{1+z}>1$.
Then $f(z)=(u-1)^2/(2u)$ and

$$
\frac{zf'(z)}{f(z)}
=\frac{(1+(1+z)^{-1/2})^2}{2}\le2\qquad(z>0).
\tag{65.19}
$$

Integrating this logarithmic derivative gives, for $t\ge1$,
$f(tz)\le t^2f(z)$. If $g_{\min}$ and $g_{\max}$ are the smallest and
largest coefficients on the complete terminal table, set
$a_{\max}=f(\kappa/g_{\min})$ and
$a_{\min}=f(\kappa/g_{\max})$. Thus

$$
\frac{a_{\min}}{a_{\max}}
\ge\left(\frac{g_{\min}}{g_{\max}}\right)^2.
\tag{65.20}
$$

This controls the relative negative margin even when $\kappa$ tends to zero
or to infinity; a fixed-parameter rank argument alone would not give this
uniform response bound.

Consider a restriction to $m\ge5$ terminals. Let $E$ be its relative-response
error. For $E\ge1$ all the claimed bounds hold. If $E<1$, every pair satisfies
$(1-E)g\le\widehat g\le(1+E)g$. Applying (65.19) to
$f(\kappa/\widehat g)$ and $f(\kappa/g)$ yields

$$
\left|f(\kappa/\widehat g)-f(\kappa/g)\right|
\le a_{\max}\bigl[(1-E)^{-2}-1\bigr].
\tag{65.21}
$$

For the lower endpoint use
$f(\kappa/\widehat g)\ge(1+E)^{-2}f(\kappa/g)$ and
$1-(1+E)^{-2}\le(1-E)^{-2}-1$; the upper endpoint uses
$(1-E)^{-2}$. The modeled Gram $\widehat C$ and the prescribed $C$ have
the same diagonal one. The symmetric row-sum bound therefore gives

$$
\|\widehat C-C\|_{\rm op}
\le(m-1)a_{\max}\bigl[(1-E)^{-2}-1\bigr].
\tag{65.22}
$$

If the right side were smaller than $a_{\min}$, (65.13) would make
$\widehat C$ strictly negative on the $(m-1)$-dimensional zero-sum subspace.
The classical variational perturbation argument is immediate here:
$z^\mathsf T\widehat Cz\le
[-a_{\min}+\|\widehat C-C\|_{\rm op}]\|z\|^2$ on that subspace.
Since a hyperbolic-three Gram has at most three negative eigenvalues, this is
impossible. Equations (65.20)–(65.22) consequently imply

$$
E\ge1-\left[1+\frac{(g_{\min}/g_{\max})^2}{m-1}\right]^{-1/2}.
\tag{65.23}
$$

The depth-three ratios are $1/11$ and $7/103$. With $m=8$, (65.23) gives
(65.17); with $m=5$ and the actual subset (65.15), it gives (65.18).
That subset includes a sibling pair and a pair separated at the root, so both
terminal extremes are retained. Its negative margin follows from the same
restricted cluster identity, without fitting only five chosen response entries.
The bounds apply to all its ten pairs and hence to the full 105 pairs.
Finally $1-\sqrt{1-x}=x/(1+\sqrt{1-x})>x/2$ for $0<x<1$
proves the rational strict lower bounds in (65.18). $\square$

**Theorem 65.7 (lawful all-source refinement and buffered killed targets).**
Let $t$ be any original nonempty finite source and let
$D_j(t)=\operatorname{Pos}(\rho^jt)$ retain the actual irregular domain,
root and history interpretation of Definition55.1. For every actually reached
version, or every separately legal finite prefix, with $j\ge6$, the common
full-table target has

$$
E_{D_j(t)}^{\rm c}\ge\varepsilon_{{\rm c},5}
\ge\varepsilon_{{\rm c},8}.
\tag{65.24}
$$

Set $\lambda=3-2\sqrt2$, $\varrho=1-\lambda/3$ and, for an integer $R\ge3$,

$$
\eta_R=\frac{64\varrho^{R-2}}{\lambda}.
\tag{65.25}
$$

For every such separately legal $j\ge2R$, the killed full-table target obeys

$$
E_{D_j(t)}^{\rm k}\ge
\max\{0,\varepsilon_{{\rm c},5}-\eta_R\}.
\tag{65.26}
$$

In particular the finite choice $R=241$, $j\ge482$, certifies, uniformly
over all original finite $t$ and all sourcewise refits,

$$
E_{D_j(t)}^{\rm k}\ge\tfrac12\varepsilon_{{\rm c},8}>0.
\tag{65.27}
$$

These quantifiers permit arbitrary varying finite $t$ with separately legal
indices; they do not permit an increase of a running cap, installation of a
refused candidate, an event after Stop or an event after an infinite prefix.

Proof. Equation (55.2) gives $B_3\subset D_j(t)$ for $j\ge6$.
The common coefficients on its eight terminals are exactly the unchanged
common table of Theorem65.3. Restriction and Theorem65.6 prove (65.24).
For $j\ge2R$ one has $B_R\subset D_j(t)$. Every depth-three address then
has an occurrence-metric buffer of radius $R-3$ contained in that actual
domain. Lemma63.6, applied with this buffer, gives on the terminal pairs

$$
0\le G^{\rm c}(p,q)-G_{D_j(t)}^{\rm k}(p,q)
\le\frac{\varrho^{R-2}}\lambda,
\qquad
0\le1-\frac{G_{D_j(t)}^{\rm k}(p,q)}{G^{\rm c}(p,q)}\le\eta_R,
\tag{65.28}
$$

since their common minimum is $1/64$. If a modeled response has relative
killed error $e_{pq}$ and
$d_{pq}=1-G_{D_j(t)}^{\rm k}(p,q)/G^{\rm c}(p,q)$, then

$$
\frac{\widehat G(p,q)}{G^{\rm c}(p,q)}-1
=(1-d_{pq})e_{pq}-d_{pq}.
$$

Positivity and killed domination give $0\le d_{pq}<1$, and hence its absolute
value is at most $|e_{pq}|+\eta_R$. Apply the common five-terminal bound to
the same modeled responses on $\mathcal S_5$. Their maximum killed error
is at least $\varepsilon_{{\rm c},5}-\eta_R$, proving (65.26).
This comparison uses one actual table and one configuration throughout, rather
than combining independently attainable fits.

For the stated finite threshold, the rational inequalities

$$
\sqrt2<\frac{99}{70},\qquad
\lambda>\frac6{35},\qquad\varrho<\frac{33}{35},\qquad
64\frac{35}{6}\left(\frac{33}{35}\right)^{239}
\le\frac1{3392}<\frac{\varepsilon_{{\rm c},8}}2
\tag{65.29}
$$

give $\eta_{241}<\varepsilon_{{\rm c},8}/2$. The power inequality is an
exact rational certificate, equivalently
$3392\cdot64\cdot35\cdot33^{239}\le6\cdot35^{239}$.
The last strict inequality follows from
$\varepsilon_{{\rm c},8}>1/1696$. Equations (65.26) and
$\varepsilon_{{\rm c},5}>\varepsilon_{{\rm c},8}$ imply (65.27).
$\square$

At each finite prefix the cap must cover that source's actual candidate leaf
counts; no assertion here supplies its bank, preparation or price for free.
The domain remains $D_j(t)$, not $B_R$. Under actual accepted renewal, the
common old-pair values retain (62.7), whereas the killed values undergo the
authentic mask-dependent Schur update (62.8). At a refusal or Read the installed
source and operator version do not change. A static obstruction with arbitrary
sourcewise refitting is already a necessary failure for any stronger demand
of one persistent geometric assignment through those versions; this implication
does not establish a retained-state switching law.

**Theorem 65.8 (necessary consequence for the same full one/two-occupation law).**
Fix the actual INITIAL $D=B_3$ of Definition65.1 and one prescription.
Retain the full source-qualified Hilbert spaces $\mathscr H_{D,1}$ and
$\mathscr H_{D,2}$ of (62.1), with their counting-measure norms and literal
hard-core symmetric statistics. Let

$$
\begin{aligned}
h_D&=aL_D-gM_{\phi|D},\\
H_{D,1}^\diamond&=h_D,\\
H_{D,2}^\diamond&=P_{D,2}\,d\Gamma(h_D)\,P_{D,2}
-\nu\sum_{\{p,q\}\subset D}G_D^\diamond(p,q)n_pn_q.
\end{aligned}
\tag{65.30}
$$

The two-occupation space has dimension 105. The compression retains the
diagonal $d_p+d_q$, including inherited exterior and blocked-collision killing;
it is not a Laplacian of only allowed moves or a fermionic exterior power.
Here $a,g>0$ and $\nu\ge0$ are the commissioned parameters of §62,
independent of the original $\mathcal D_2$ actor variable.

For any one Hermitian one-body law $B_D$ used consistently in both sectors,
and any whole-table point law (65.5) with finite distinct points, define

$$
\begin{aligned}
\widehat H_{D,1}&=B_D,\\
\widehat H_{D,2}&=P_{D,2}\,d\Gamma(B_D)\,P_{D,2}
-\nu\sum_{\{p,q\}\subset D}\widehat G_D(p,q)n_pn_q,\\
E_1&=\|B_D-h_D\|_{\rm op},\qquad
E_2^\diamond=\|\widehat H_{D,2}-H_{D,2}^\diamond\|_{\rm op}.
\end{aligned}
\tag{65.31}
$$

Put

$$
\delta_{{\rm c},65}=\frac{\varepsilon_{{\rm c},5}}{64},\qquad
\delta_{{\rm k},65}=\frac{\varepsilon_{{\rm k},5}}{240}.
$$

Then the necessary joint bound is

$$
E_2^\diamond+2E_1
\ge\nu\max_{\{p,q\}\subset D}
|\widehat G_D(p,q)-G_D^\diamond(p,q)|
\ge\nu\delta_{\diamond,65}.
\tag{65.32}
$$

In particular, preserving the original one-body and kinetic terms gives $E_1=0$
and, for $\nu>0$, a strictly positive full two-occupation generator-norm floor
$E_2^\diamond\ge\nu\delta_{\diamond,65}$. At $N=1$ the pair multiplier
vanishes for both prescriptions, and at $\nu=0$ this obstruction yields no
positive joint generator floor.

Proof. On $\mathscr H_{D,2}$ the pair difference is diagonal. Its entry at the
actual occupation $\{p,q\}$ is
$-\nu(\widehat G_D(p,q)-G_D^\diamond(p,q))$, so its operator norm is
$\nu$ times the maximum absolute coefficient error on all 105 pairs. The
hard-core compression of $d\Gamma(B_D-h_D)$ has norm at most $2E_1$.
The triangle inequality proves the first inequality in (65.32), precisely as
the same-sector argument in Theorem64.4. This consumes that operator principle;
the new bound is supplied by the distinct hyperbolic class obstruction.

The five-terminal restriction has maximum relative error at least
$\varepsilon_{\diamond,5}$. On that restriction its smallest common coefficient
is $1/64$ and its smallest killed coefficient is $1/240$. Consequently the
maximum absolute error there is at least $\delta_{\diamond,65}$, and the
maximum on the full domain is no smaller. An actual pair attaining that finite
maximum gives the diagonal occupation witness. No alternative one-body fit
can cancel it in the two-occupation sector without entering the same $E_1$
budget. $\square$

This is a necessary condition on a law that transports the same complete
$N=1$ and $N=2$ generators, with the supplied source, reference and clock.
It does not replace that task by a static configuration or one-body task.
No finite-time propagator, state, acquired probability, measurement or clock
error lower bound follows merely from (65.32). Such a bound needs its own
common input, time, reference, observation and spectral argument; Duhamel's
usual generator-norm upper estimate cannot be reversed for this purpose.
Neither independent sector fits nor a quotient by global phase is part of
the unchanged full joint target.

**Definition 65.9 (supplier scopes and the remaining full correspondence).**
The source and history suppliers are Continuation Definition1.1, TM30's
fixed-cap boundary and guard, PR57's authentic processor, and §§55.1–55.2,
58 and60. The response and literal-statistics suppliers are (62.2)–(62.4);
the rooted factorization is (62.19)–(62.21), actual renewal is (62.7)–(62.8),
and the buffered coefficient comparison is Lemma63.6. The conditional
stratified producer, its common preparation and complete finite-horizon
retained-state correspondence remain exactly Definitions64.5 and
Theorems64.6–64.7. The pair obstruction here does not alter that producer's
explicit atomic interaction. Chapter64's conditional results retain that scope.
Chapter63's binding, cluster escape and spectral retention are likewise
inherited in their stated scope.

The all-beta depth-three source at cap sixteen and the terminal subset
$\mathcal S_5$ differ from Chapter64's cap-three source and its five-site domain
$\{o,L,R,LL,LR\}$. The term “H3 source” for the latter cap is distinct from
the ambient space $\mathbb H^3_\ell$. Prior finite five-site fits retain their
original finite targets and conditions. An obstruction to a class containing
$T_3$ does not deny a fit of a different finite table, and the inverse-distance
law in (64.1) is not the hyperbolic point law (65.5).

Cohl–Kalnins supplies only the complete homogeneous Laplace–Beltrami point
problem with its stated volume normalization and decay. Keller-Ressel–Nargang
and Tabaghi–Dokmanić supply finite Lorentz/rank recognition with exact prescribed
entries and normalization. Faver et al. and Gorman–Lladser supply the mature
ultrametric and cluster methods in the scopes identified after Theorem65.4.
Putinar–Vishwakarma supplies recognition and compatible completion, not freedom
to complete already specified all-pair values at an imposed lower dimension.
The row-sum and variational perturbation steps in Theorem65.6 are classical
matrix estimates. The rooted source coefficients, all-parameter application,
response floors and lawful-source joint consequences here are repo-derived
ordinary mathematical deductions from these suppliers. They carry no claim of
global novelty, fresh kernel validation or physical verification. Finite exact
instances can corroborate coefficients and inertia identities; the all-depth,
all-calibration and all-source assertions depend on the displayed ordinary
proofs, not an extrapolation from those instances. Optimal minimax response
error, full-domain higher-dimensional distance realization and a corresponding
higher-dimensional Green field are not established.

The obstruction applies to the entire specified homogeneous unscreened
point-field model class (65.5). It excludes neither physical three-space nor
inhomogeneous media, screening, different operators, finite boundary problems,
extended sources or other realization contracts. It selects no physical
dimension. The distinct Euclidean point-source and localization contract in
[legacy §52.7](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md#527-reuse-exact-scope-and-the-missing-native-connection)
retains its own domain, isotropic second-order operator, far-field and form
assumptions; no transfer of that classification is asserted by equal site degree,
direction count or terminal embedding dimension.

The unchanged full joint problem retains actual INITIAL acquisition and every
original numerical response, all ordered operations and legal histories, every
cap guard, refusal and Stop. It retains the complete $N=1/N=2$ amplitudes and
phases, kinetic law and propagators, the common one-body field, separate pair
prescriptions, exterior and collision terms, all auxiliary and retained state,
authentic renewal and switching, reference coherence, the same clock and the
full norm without discarding components. A field-mediated interaction, an
operation- and metric-preserving displacement map, isotropy and local physical
realization remain unproved bridges. Finite unknown-state ingress, preparation,
measurement, precision and time calibration, together with construction,
control, service, production, storage, retention, maintenance and total resource
price, remain independent obligations. No unlimited horizon, unlimited population
or finite total-price conclusion is supplied by (65.24)–(65.32).

In particular the original $\mathcal D_2$ source keeps independent arbitrary
unbounded $a$, including zero, untagged radius-$7/25$ $b$, destructive actions,
joint adversarial and history-dependent errors, source-independent initialization
and its original INITIAL/Read/Stop task. The positive commissioned kinetic $a$
in (65.30) is another variable. The existing common $\Pi$ bridge, consumed in
Definition63.13, keeps its full-vector, spanning, common-zero, whole quadratic
distance/positive-semidefinite Gram, at least two independent directions,
alternating bilinear exact-area/Jacobi, actual orthonormal-probe, finite binary
calibration and hidden-kernel-preserving generator hypotheses. It supplies no
new spatial/operator transport here. Section57 retains its separate
composition-promised immutable endpoint-query contract, with all its original
depth caps, common source-independent initialization, actual retained
query/reply histories, correct finite stopping on every same-composition
positive and negative source, and distinct-address fees; Definition57.12 grants
no old-source archive. The separate [paid promised-family archive/cut acquisition
contract, Atomic Generation Acquisition §12](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#12-不可逆根后的被动切口阶梯容量与原生关系呈现),
consumed in Definition63.13, retains its paid positive-root archive, exact
nonadvancing cut port, finite stopping/decoding, protected written records after
refusal/closure, aligned actual generation, trusted markers, no unrecorded source
change, actual write/protect/retain/query rights, closed strong ports and inclusion
of every reply-affecting retained source influence in the service price. These
acquisition contracts and the common $\Pi$ bridge supply no source copy, reset,
independent resampling, exact limit Read or new native geometric or quantum
control. The necessary exclusion of (65.5) and its generator consequence
leave these full operational and physical obligations intact.

## 65.99 追加锚（本行以下为增补区）
## 66. Whole-rho transport of the full stratified state, finite histories and the graft boundary

**Definition 66.1 (one actual source and the finite comparison).** The source is the actual labelled, bracketed, ordered nonempty tree of Definitions55.1,60.1 and62.1, installed by PR57 at its declared fixed leaf cap $H$. Its immutable INITIAL, original source-independent actor initialization, current root, epoch, request/context identities, actual candidate, whole-candidate guard, every accepted or refused response, every original Read, retained chronological row and copy, and absorbing Stop remain part of the joint object. Equal-valued occurrences are distinct. An attempted whole-rho is not an accepted renewal; refusal supplies no candidate Read. A beta-empty acceptance changes labels and epoch even when the geometric domain does not change. The full original Left/Right menu is retained, with each named actual positive context supplied and guarded by its original routines. Accepted context grafts are considered separately in Proposition66.8; they are not whole-rho inclusions.

Use exactly the measure, mixed strata, symmetric hard-core form and atomic interaction of Definition64.5, at one density $0<\delta\le1$ for the entire commission. The intrinsic length and conductance of every cable are one. Root incidence is two, nonroot incidence three; every current leaf retains two distinct grounded stubs. The one-body field is always the same $\phi(p)=2^{-|p|}$ on actual atomic addresses and zero on open cables. The separate pair choices are the complete common restriction $G^{\rm c}_D$ and the complete killed inverse $G^{\rm k}_D$, without changing $\phi$. The commissioned $a,g>0,\nu\ge0$ are independent of the original actor's parameters. Retain $\lambda=3-2\sqrt2$ from (62.4). Write

$$
\mathcal K_{D,1}=L^2(X_D,\mu_\delta),\qquad
\mathcal K_{D,2}=\mathcal K^{\rm hc}_{D,2},\qquad
\mathcal Q_{D,N}=\mathcal Q_{D,N}^{(64.5)}.
$$

A finite commissioned whole-rho trajectory can contain any finite number of original Reads, refused rho/context attempts and accepted whole-rho steps, and supplied idle intervals with total comparison time at most $T<\infty$. It stops at or before an accepted graft, or original Stop. The graft is still executed and recorded by the original source contract; the positive whole-rho amplitude theorem is not asserted across it. Proposition66.8 proves why one natural full-data/full-norm graft requirement fails, rather than treating that event as a reset or omitting it from the original menu. A fixed-cap trajectory never changes its cap, never has an event after an infinite prefix, and has no interaction or readout after Stop. Any commissioned readout precedes Stop.

The preparations $W_{D,N}$, atomic injections $J_{D,N}=R_{D,N}^*$, and constants $\beta_N,s_N,r_N$ below are exactly Theorems64.6–64.7. They are mathematical identifications, not newly acquired coefficients, free controls or physical preparation procedures. Empty $D$ is only a zero-space convention for statements about maps: $X_\varnothing$ and its $N=1,2$ Hilbert/form spaces are empty or zero, with their unique maps. No original source is empty. For a singleton, the full two-position producer space still contains all its slice and cell modes, although $\mathscr H_{D,2}=0$.

**Definition 66.2 (the labelled cable inclusion).** Let the actual whole-rho candidate be accepted, with old source $s$, beta-leaf set $\mathcal B(s)$, and $D'=\operatorname{Pos}(\rho s)$. Retain each old seam with its intrinsic coordinate. At each $p\in\mathcal B(s)$, name its two old grounded stubs by $pL,pR$. Identify the complete open stub named $pz$ with the new unit seam from $p$ to $pz$, preserving its coordinate from $p$ toward its former ground tip. That tip becomes the new atomic port $pz$. Its old zero trace is retained; its newly created atomic coordinate is assigned zero at the transfer. Add the two new grounded stubs at each newborn child. At an old alpha leaf both old grounded stubs remain grounded. This identifies every old open cable with exactly one new open cable and never identifies two occurrences, two stubs or two coordinates.

Define $\mathsf T_{D'D,1}$ on the entire direct-sum Hilbert space by copying all old atomic coordinates and every old open-cable function to these identified strata, and putting zero on every new atomic coordinate and new open cable. This is a direct-sum definition: assigning a new mass-one atom at a former mass-zero ground tip does not copy a value from an $L^2$ representative at that tip. It assigns zero independently. For $N=2$, copy all old distinct atomic pairs, all ordered old atom/cable slices and all old cable/cable cells under the same identification, and put zero on every stratum involving a new atom or a new cable. Same-cable cells keep both dissected triangles and both zero diagonal traces. Denote its symmetric restriction by $\mathsf T_{D'D,2}$. The target occupation injection is the distinct-occurrence map $\jmath_{D'D,N}e_S=e_S$ of Theorem62.4. These definitions specify the full maps before restricting to any calibrated range.

**Theorem 66.3 (full-space isometric kinetic-form and collision-domain transfer).** For every actual accepted whole-rho, $N=1,2$, and every vector in the indicated spaces,

$$
\begin{aligned}
\mathsf T_{D'D,N}^*\mathsf T_{D'D,N}&=I,
& R_{D',N}\mathsf T_{D'D,N}&=\jmath_{D'D,N}R_{D,N},\\
\mathsf T_{D'D,N}J_{D,N}&=J_{D',N}\jmath_{D'D,N},
&\mathsf T_{D'D,N}\mathcal Q_{D,N}&\subseteq\mathcal Q_{D',N},\\
k_{\delta,D',N}(\mathsf T_{D'D,N}F,\mathsf T_{D'D,N}G)
&=k_{\delta,D,N}(F,G).
\end{aligned}                                                    \tag{66.1}
$$

Here the isometry is an injection defined on the whole old Hilbert space, including arbitrary old continuum components, rather than only on $W_{D,N}\mathscr H_{D,N}$. It need not be onto the new space. It preserves the actual form/collision domain, not an asserted equality of operator domains or propagators. If $\mathcal B(s)=\varnothing$, it is the identity on every stratum even though the source version and labels are updated. For successive accepted steps and their canonical cable identifications,

$$
\mathsf T_{D''D',N}\mathsf T_{D'D,N}=\mathsf T_{D''D,N},\qquad
\jmath_{D''D',N}\jmath_{D'D,N}=\jmath_{D''D,N}.       \tag{66.2}
$$

The right-hand cable map means the direct inclusion along this actual source history; it does not identify different sources or different histories.

Proof. The one-position norm is the sum of atomic norm squares and $\delta$ times every open-cable norm square. Each copied stratum keeps exactly its old coefficient and intrinsic coordinate; every added coordinate is zero. Thus its norm is unchanged. In ordered two-position coordinates the same argument applies with weights $1,\delta,\delta^2$, before exchange restriction. Diagonal atomic coordinates are absent on both sides. The map commutes with exchange and is therefore an isometry on its symmetric hard-core subspace, with exactly the old normalization of distinct atomic pairs. This also proves the two identities involving $R,J$.

For the one-particle form, an old stub's value at its old atomic end is unchanged. Its former grounded zero trace is now the trace at a new atom whose assigned value is zero. Each new grounded stub has zero function and zero port value. Every other endpoint equality is the old equality. Derivative integrals are unchanged, and zero new functions contribute no energy.

For two particles consider every trace type of Definition64.5. The boundary of a copied old cell at an old port remains its copied old slice; that slice ends at the copied old atomic pair, or at zero when its two port labels coincide. A copied old cell boundary at a newly atomic former ground tip was a grounded zero boundary and is still zero, now matching the new atom/old-cable slice assigned zero. An old atom/old-stub slice likewise has old grounded endpoint zero, matching the newly created atomic pair assigned zero. A cell involving a new cable is zero: at a newborn child its incident slice is a new-atom slice and hence zero, and its grounded boundary is zero. A slice involving a new cable has zero atomic endpoints for the same reason. These statements include cells between two old stubs which simultaneously become seams, and cells between incident cables meeting an old port. Both traces on an old same-cable diagonal are retained, while new same-cable diagonals have zero function. Distinct-cable shared-port collisions still terminate their slices at the same zero atomic collision coordinate. No corner value of a general two-dimensional $H^1$ function is used. All required trace equalities therefore hold.

The two-coordinate derivative form is the sum of slice derivatives and $\delta$ times both cell derivatives in (64.7). Every old term is copied with its coefficient, including all collision and grounded-end terms. Every new term is zero. Equality follows, and polarization gives (66.1) for complex $F,G$. This proof treats all old mixed and cell functions, not merely separable or interpolated states. The zero-space and singleton conventions satisfy the same statements; in particular the singleton's full two-position space is transported by the preceding stratum argument rather than declared absent.

A cable, once created, is never deleted or split under whole-rho. A currently grounded tip may later become an atom, but a zero assigned coordinate remains zero under further inclusions. Existing atomic coordinates keep their addresses. Copying a stratum twice is consequently the same as copying it directly, and a coordinate introduced after the starting version is zero in both compositions. This proves (66.2). When there is no beta leaf, no stratum changes at all. $\square$

**Proposition 66.3a (a nonzero full two-position transfer with zero atomic target).** For the actual singleton source $s=\beta$, followed by its accepted whole-rho at cap $H=2$, the old target $\mathscr H_{\{o\},2}$ is zero but the full-space transfer in Theorem66.3 has nonzero admissible mixed inputs. Parameterize its two old stubs from the root by $x\in[0,1]$. On every ordered root/stub slice use $g(x)=x(1-x)$, with no atomic pair. On each same-stub cell use

$$
h(x,y)=|x-y|(1-\max(x,y)),
$$

and on each different-stub cell use

$$
b(x,y)=g(y)(1-x)+g(x)(1-y).
$$

These functions define a symmetric form vector $F$ with

$$
\|F\|^2=\frac{2\delta}{15}+\frac{17\delta^2}{180},\qquad
k_{\delta,2}(F)=\frac43+\frac{56\delta}{45}.          \tag{66.1a}
$$

Both quantities are preserved by its actual whole-rho transfer. In particular at $\delta=1/10$ they are $257/18000$ and $328/225$ respectively. This vector is full retained continuum data, not a unit two-port target preparation.

Proof. The slice has zero trace at both endpoints. The same-stub function has root boundaries $g$, grounded boundaries zero, and zero traces on both sides of the diagonal. The different-stub function has root boundaries $g$ and grounded boundaries zero; its shared-root corner agrees with the missing atomic collision value zero. Exchange symmetry is literal. Each triangular polynomial is $H^1$, as is the different-stub polynomial, so these are the actual domain conditions without a corner trace assumption for general $H^1$ data. Direct polynomial integration gives slice norm/derivative integrals $1/30,1/3$, same-stub full-square integrals $1/90,1/3$, and different-stub integrals $13/360,13/45$. There are four ordered slices, two same-stub cells and two different-stub cells. Multiply their norm integrals by $\delta,\delta^2$ and their derivative integrals by $1,\delta$ as in (64.7), obtaining (66.1a). At renewal all these old functions are copied; their old ground boundaries are zero at the new atoms and all new strata are zero. Thus the positive-mass mixed input meets Theorem66.3, including the zero-target case. $\square$

**Proposition 66.4 (complete potential update, without dynamic intertwining).** Let $q^\diamond_{D,N}=a k_{\delta,D,N}+\langle\cdot,U^\diamond_{D,N}\cdot\rangle$ be the full form of (64.8). For the common prescription,

$$
U^{\rm c}_{D',N}\mathsf T_{D'D,N}=\mathsf T_{D'D,N}U^{\rm c}_{D,N},\qquad
q^{\rm c}_{D',N}(\mathsf TF)=q^{\rm c}_{D,N}(F).     \tag{66.3}
$$

For the killed prescription the one-particle equality is the same, while for $N=2$,

$$
q^{\rm k}_{D',2}(\mathsf TF)-q^{\rm k}_{D,2}(F)
=-\nu\sum_{\{p,q\}\subset D}\Delta G(p,q)
       |(R_{D,2}F)(\{p,q\})|^2,                  \tag{66.4}
$$

where the entire actual update, not a selected pair fit, is

$$
\Delta G=GU\left(\tfrac32 I-U^*GU\right)^{-1}U^*G,
\qquad G=L_D^{-1},\quad U=(e_p)_{p\in\mathcal B(s)}. \tag{66.5}
$$

An empty beta mask means zero update. All inverse and positivity conditions in (66.5) are supplied by Theorem62.4.

Proof. Every old atomic depth is unchanged. A copied mixed slice has precisely its old additive one-body potential, and a copied cell still has zero atomic one-body multiplier. New strata have zero state. The common inverse is the same infinite $L^{-1}$ at every version, so all old atomic pair multipliers coincide. Theorem66.3 proves the remaining kinetic equality. For the killed choice only the old atomic pair coefficients change on the transferred state. Apply (62.8) with its authentic beta mask and the normalized symmetric atomic coordinates of Lemma64.5b to obtain (66.4)–(66.5). No positive-mass coordinate or trace is dropped in this computation. $\square$

Form equality on the isometric image is a compression statement. After release, the new generator acts on the larger space and may move amplitude out of that image. The actual born-child hopping of (60.7),(62.7) persists. For the killed choice the old pair energy change in (62.9) persists as well; it is not a small-$\delta$ calibration error. Proposition58.3's failure of all-time rho intertwining and Proposition62.5's growing-population killed-energy defect are inherited, not contradicted. The full-space inclusion alone grants neither a physical switching law nor a new common exterior dynamic state.

**Lemma 66.5 (calibration mismatch at an actual enlargement).** Put

$$
\omega_N=\sqrt{\beta_N^2+s_N^2},\qquad
s_N=1-(1+\beta_N^2)^{-1/2},\qquad
\omega=\max(\omega_1,\omega_2).
$$

For either pair prescription, using the same preparation rule and density on both versions,

$$
\|W_{D,N}-J_{D,N}\|\le\omega_N,\qquad
\|\mathsf T_{D'D,N}W_{D,N}-W_{D',N}\jmath_{D'D,N}\|
\le2\omega_N.                                      \tag{66.6}
$$

When $D'=D$ the second norm is zero. For $0<\delta\le1$, $\omega\le16\sqrt\delta+128\delta\le144\sqrt\delta$.

Proof. Consume Theorem64.6: $W=(J+Q)S$, $Q=E-J$, $\|Q\|\le\beta_N$, $\|S\|\le1$ and $\|S-I\|\le s_N$. Atomic and continuum ranges are orthogonal, so

$$
\|(W-J)f\|^2=\|J(S-I)f\|^2+\|QSf\|^2
\le(s_N^2+\beta_N^2)\|f\|^2.
$$

Insert $\mathsf TJ=J'\jmath$ from (66.1), and use the full isometry of $\mathsf T$ and $\jmath$ to bound the two remaining differences by $\omega_N$ each. An unchanged geometric domain has literally the same measure, form, restriction and unique harmonic minimizer, so $W'=W$ and $\mathsf T=\jmath=I$. The last bound uses the already supplied $\beta_N\le16\sqrt\delta$ and $s_N\le128\delta$ from §64. No minimization, idle operator relation or continuum-mode elimination is re-proved here. $\square$

**Theorem 66.6 (same-clock finite histories in the full joint norm).** Fix an actual finite legal trajectory of Definition66.1. Let $m$ count its accepted whole-rho steps, and let $q\le m$ count only those with nonempty beta mask. At its idle intervals, use its actual current $D_i$ and the complete $H^\diamond_{D_i,N}$ of (62.2). The exact target history $\mathsf V^\diamond_h$ is the time-ordered composition of $e^{-i\theta_iH^\diamond_{D_i,N}}$, the accepted occurrence injections $\jmath$, and identity at the other source-service cuts. The producer history $\mathsf P^\diamond_{\delta,h}$ uses the actual full unitaries $e^{-i\theta_i\mathcal T^\diamond_{\delta,D_i,N}}$, the full-space inclusions $\mathsf T$, and the same identity cuts. No calibrated state is prepared again at a switch. For every target vector $f$ and every checkpoint of that history,

$$
\|\mathsf P^\diamond_{\delta,h}W_{D_0,N}f
     -W_{D_h,N}\mathsf V^\diamond_h f\|
\le\left(\sum_i\theta_i r_N+2q\omega_N\right)\|f\|. \tag{66.7}
$$

Use each checkpoint's actual prefix sums. For the joint object, set

$$
\begin{aligned}
\mathscr H_D^{\rm joint}
 &=\mathbb C r\oplus\mathscr H_{D,1}\oplus\mathscr H_{D,2},\\
\mathcal K_D^{\rm joint}
 &=\mathbb C r\oplus\mathcal K_{D,1}\oplus\mathcal K_{D,2},\\
W_D^{\rm joint}&=I_r\oplus W_{D,1}\oplus W_{D,2},
\end{aligned}
$$

with zero reference generator and identity reference transfer. Tensor all these maps with identity on any supplied retained auxiliary Hilbert space $\mathcal A$, including unused bank modes, $c,u,v$, clock/reference registers and all quantum retention factors. This requires their supplied fixed-factor identification and identity law across the whole commission, rather than inferring such a law from an idle interval. Newly born atomic coordinates of $\mathcal K_{D',N}$ are not taken from an unknown auxiliary register. Physically promoting a previously retained bank mode into an active atom, or coupling an auxiliary during service, requires its own complete joint transfer certificate; a second copy or reset of that mode is not supplied. For every $f\in\mathscr H_{D_0}^{\rm joint}\otimes\mathcal A$, with arbitrary unknown correlations between its sectors, reference and auxiliaries, the bound is

$$
\|\mathsf P^\diamond_{\delta,h}W_{D_0}^{\rm joint}f
-W_{D_h}^{\rm joint}\mathsf V^\diamond_h f\|
\le (TR\sqrt\delta+2q\omega)\|f\|
\le(TR+288m)\sqrt\delta\,\|f\|,                   \tag{66.8}
$$

where $R$ is the common constant displayed after Theorem64.7. The two prescriptions are separate full commissions, each satisfying the same bound; they are not blended or independently optimized marginals. An initial retained component $z$ of norm at most $\eta$ adds at most $\eta$ and is carried through the whole history without projection, reset, resampling or a new copy. If $z$ is a form vector, its form admissibility is retained at every ideal cut and every idle interval. Hilbert vectors without a finite-energy premise still satisfy the norm assertion.

Proof. The one-interval discrepancy is exactly (64.12). Suppose the current discrepancy from $W_Df_i$ is $e$. An idle unitary preserves its norm and adds at most $\theta_i r_N\|f_i\|$; the target unitary has $\|f_i\|=\|f\|$. At an accepted enlargement the full isometry preserves the old discrepancy and (66.6) adds at most $2\omega_N\|f\|$. An identical-domain acceptance, Read or refusal adds zero. Induction gives (66.7). No inference that the actual producer state remains in the calibrated range is made: its entire previous discrepancy is propagated in its full norm. Direct-sum operator norm is the maximum of the two sector bounds, and tensoring with identity leaves the operator norm unchanged, proving the entangled-input statement. Apply the uniform residual $r_N\le R\sqrt\delta$ of Theorem64.7. Every factor in the ideal history is an isometry or a unitary, so $z$ retains its norm. Theorem66.3 and Lemma64.5a retain its form domain when supplied. $\square$

For fixed finite $T,m,a,g,\nu$ and target norm, this bound decreases to zero with the single density $\delta$. No subescape, spectral-gap, localization or visible-state restriction on $f$ is imposed. In particular it includes the hidden phases and complete contrast directions of §§55,58,63, every one/two-particle basis direction, and arbitrary combinations with the same reference. It is not uniform as $T$ or the number of renewals becomes unbounded. Finite cap is a legality condition, not permission to complete an infinite refinement or make an exact limit Read.

**Theorem 66.7 (ingress, service, calibration and comparison-clock errors).** The following explicit certificates extend (66.8) to a supplied finite implementation. They are premises on the actual commission, not conclusions about a native apparatus. Every ideal and actual map acts on the whole declared retained space, including all leakage modes, reference and auxiliaries; actual maps are linear isometries, or contractions without conditioning or postselection. Their source version and all original guards/responses are authentic. A wrong source, lost row or omitted retained mode is not a small calibration error.

Let actual ingress differ from $W_{D_0}^{\rm joint}$ by operator norm at most $\epsilon_{\rm in}$, with additional supplied initial component of norm at most $\eta$. For every service/locking/hold/transfer block $k$, let its actual full map differ from its ideal identity or $\mathsf T$ by operator norm at most $h_k$. A supplied full-space certificate of this kind includes phase/reference faults and any nonidentity auxiliary evolution. At idle interval $i$, let the actual evolution differ by full-space operator norm at most $e_i$ from the evolution of the declared producer with comparison interval $\widehat\theta_i\ge0$, commissioned approximants $\widehat a_i>0,\widehat g_i>0,\widehat\nu_i\ge0$, and its actual approximate atomic pair multiplier. There is no assumed bounded-generator operator-norm clock estimate on arbitrary continuum modes.

Use common finite upper bounds $\bar a,\bar g,\bar\nu$ for the exact and approximate commissioned parameters. Supply

$$
\begin{gathered}
|\widehat a_i-a|\le d_{a,i},\quad
|\widehat g_i-g|\le d_{g,i},\quad
|\widehat\nu_i-\nu|\le d_{\nu,i},\\
\max_{\{p,q\}\subset D_i}|\widehat G_i(p,q)-G^\diamond_{D_i}(p,q)|
\le\kappa_i,\qquad
|\widehat\theta_i-\theta_i|\le t_i.
\end{gathered}
$$

The maximum over an empty pair set is defined as zero. The complete pair certificate covers every actual pair of the selected common or killed law. Suppose any additional bounded multiplier discrepancy, for example a certified implementation departure from the unchanged common one-body field, has full norm at most $v_i$. Define

$$
\begin{aligned}
\bar M&=2\bar g+\bar\nu/\lambda,
&\bar C&=12\bar a+\bar M,\\
\bar R&=18\bar a+256\bar C+16(\bar C+\bar M),
& C&=12a+2g+\nu/\lambda,\\
b_i&=12d_{a,i}+2d_{g,i}+d_{\nu,i}/\lambda
                 +\bar\nu\kappa_i+v_i,
&\Delta_\tau&=\sum_i t_i.
\end{aligned}
$$

Then at every completed commissioned checkpoint the actual retained vector $\widehat F_h$ satisfies

$$
\begin{aligned}
\|\widehat F_h-W_{D_h}^{\rm joint}\mathsf V^\diamond_h f\|
\le\eta+\Bigl[\epsilon_{\rm in}+\sum_k h_k+\sum_i e_i
  +(T+\Delta_\tau)\bar R\sqrt\delta
  +2q\omega+\sum_i\widehat\theta_i b_i
  +C\Delta_\tau\Bigr]\|f\|.                       \tag{66.9}
\end{aligned}
$$

The bound allows jointly correlated, history-dependent certified errors; no independence assumption is used. It covers all target vectors, not just known prepared inputs. Actual acquisition/preparation of an unknown correlated $f$ remains a supplied ingress right, never an inference from that quantifier.

Proof. Apply Theorem64.7 to the exact source pair law with the approximant parameters, at interval $\widehat\theta_i$. Its preparation $W_D$ is unchanged because Theorem64.6 makes it independent of $a,g,\nu$ and pair choice. Its residual is at most $\bar R\sqrt\delta$. Replacing the exact source pair coefficient by $\widehat G_i$ changes the full producer only by a bounded atomic multiplier, of norm at most $\bar\nu\kappa_i$ for $N=2$ and zero for $N=1$. The further multiplier change has norm at most $v_i$. Bounded-perturbation unitary Duhamel gives their contribution $\widehat\theta_i(\bar\nu\kappa_i+v_i)$ on every retained vector. This step applies to unbounded kinetic generators because their difference here is bounded.

On the finite target, $\|K_{D,N}\|\le6N$, $0\le\phi\le1$ and $G^\diamond_D(p,q)\le1/\lambda$. Its coefficient difference is at most $12d_{a,i}+2d_{g,i}+d_{\nu,i}/\lambda$ in the joint sectors. Unitary Duhamel on that bounded target gives the corresponding $\widehat\theta_i$ contribution. Its exact generator norm is at most $C$, so the remaining target clock difference is at most $Ct_i$. Combining these steps yields a one-interval bound on input $W_D f_i$ of

$$
[\widehat\theta_i\bar R\sqrt\delta
 +\widehat\theta_i b_i+Ct_i]\|f_i\|.
$$

This avoids assigning a finite global clock-Lipschitz constant to the unbounded continuum generator. Arbitrary previously accumulated continuum discrepancy is simply propagated by the actual contraction. For a service block, its difference on the ideal comparison vector $W_Df_i$ is at most $h_k\|f\|$, in addition to (66.6) if it is an enlargement. For an idle block its extra discrepancy is $e_i\|f\|$. Telescope as in Theorem66.6; $\sum_i\widehat\theta_i\le T+\Delta_\tau$. The actual maps propagate the ingress component and ingress error without amplification. Direct sums and identity tensors retain the same bounds and all correlations. This proves (66.9). $\square$

At fixed $T,m$ the total bound tends to zero when the single density and all displayed supplied error budgets tend to zero, with bounded parameter envelopes. If an ingress, hold or calibration budget is fixed positive, (66.9) retains it and does not promise vanishing total error. For a desired unit-input tolerance $\varepsilon$, if all terms other than the density terms total at most $\varepsilon/2$, one sufficient single choice is

$$
0<\delta\le\min\left\{1,
 \left(\frac{\varepsilon}{2[(T+\Delta_\tau)\bar R+288m]}\right)^2\right\}, \tag{66.10}
$$

when the denominator is positive; if it is zero, no density restriction beyond $\delta\le1$ is needed. This is a finite mathematical accuracy allocation. The actual supply and price of each certified ingress, multiplier, evolution and hold are independent obligations. A paid service/compilation hold has positive apparatus duration and retention cost. Freezing the comparison clock during it is its stated premise, not zero physical time; any departure must satisfy the indicated clock/hold certificates.

Every original request, source-service routine, record write/copy, refusal, acquisition and Stop remains executed and charged as in §§60,62. Forgetting the additional continuum state and certificates returns that actual original history, rather than synthesizing replies from a Green calculation. The uniform bounds do not depend on an observer acquiring $D$, a beta mask or a coefficient, or having source-specific initialization. Public scheduling must use only the original supplied public data and actually acquired prefix. If new apparatus telemetry, fee labels, preparation data or readout reveals private source influence, source-independent observation needs its own contract, such as the fixed-public-schedule and private-enable boundary of Theorem60.3; the form theorem does not certify that implementation. An already commissioned terminal contraction $C_0$ can be compared mathematically through $C_0(W_{D_h}^{\rm joint})^*$, whose norm is at most one. Its error is bounded by (66.9). An already commissioned effect transports through $W_{D_h}^{\rm joint}F(W_{D_h}^{\rm joint})^*$; for unit normalized inputs its probability error is at most twice the full-state error. These are comparison maps, not new native ports or physical acquisition procedures, and no evolved component is silently discarded.

**Proposition 66.8 (an accepted graft obstructs exact full-data/full-norm inclusion).** Consider an actual accepted original Right$(v)$ graft with its supplied nonempty context $v$, or its Left analogue. The old occurrence injection is respectively $p\mapsto Lp$ or $p\mapsto Rp$. It relocates the old root to a nonroot port and adds a parent seam; it is not the same-address whole-rho injection. Identify the old seams and old grounded stubs with the corresponding seams/stubs in the relocated subtree, with their intrinsic coordinates unchanged. Suppose a candidate transfer is required to retain every old atomic and open-cable component literally under this injection, and to preserve its full norm in the new active producer space, without a separate retained carrier or repreparation. For any old form vector $F$ with nonzero old-root atomic value, no such transfer can belong to the new one-particle form domain. Consequently no transfer meeting these requirements works on the full joint $N=1/N=2$ state space.

Proof. The retained old strata already contribute exactly $\|F\|^2$ to the new norm. Full-norm equality forces every new atomic and open-cable component to be zero in its $L^2$ space. In particular the newly added parent cable is zero almost everywhere. If its function is $H^1$, both endpoint traces are zero. The trace at the relocated old root must instead equal its retained nonzero atomic value. This contradicts the new form-domain equality. The argument uses orthogonal positive-mass strata and does not assume that the transfer is linear. Failure on one one-particle input also rules out a map satisfying the joint all-input requirement. Keeping only old atomic data instead of all old components is a different retention requirement and is not covered by this impossibility. $\square$

This has a minimal actual fixed-cap witness. At $H=2$, initialize the genuine source $t=\alpha$ and supply the named context $v=\alpha$. The original Right$(\alpha)$ candidate $\langle\alpha,\alpha\rangle$ has two leaves and is accepted at equality. Its immutable INITIAL is still the one-leaf source. The old $X_{\{o\}}$ has two grounded stubs. Let $F(o)=c$, with $F_e(x)=c(1-x)$ on both stubs and

$$
|c|^2=(1+2\delta/3)^{-1}.
$$

Then $F\in\mathcal Q_{\{o\},1}$, $\|F\|=1$ and $k(F)=2|c|^2$. It is also a calibrated input: the harmonic lift is exactly $E_1e_o$, and normalization gives $W_{\{o\},1}e_o$. The retained old components alone have new norm one. The new parent cable from the current root to $L$ would require trace $c$ at $L$, which zero added norm cannot supply. This is an actually legal source/context pair, not an idle theorem counterexample or an unguarded hypothetical graft. The Left case uses the same construction at $R$.

There is a quantitative boundary if one instead allows added norm but imposes finite kinetic budget. Let $h$ be the new parent-cable function, parameterized with its old-root endpoint at $1$, with $h(1)=c\ne0$, and suppose $\int_0^1|h'|^2\le E<\infty$. Setting $n=\int_0^1|h|^2$, the fundamental theorem and Cauchy--Schwarz give

$$
|c|^2\le n+2\sqrt{nE},\qquad
n\ge\left(\sqrt{E+|c|^2}-\sqrt E\right)^2>0.        \tag{66.11}
$$

Indeed integrate $|h(1)|^2=|h(x)|^2+2\operatorname{Re}\int_x^1h'\overline h$ over $x$, and bound the last integral by $2\|h'\|_2\|h\|_2$. Solve the resulting quadratic in $\sqrt n$. Thus retaining all old components entails squared-norm increase at least $\delta(\sqrt{E+|c|^2}-\sqrt E)^2$, before accounting for any other new strata. Boundary layers can make this addition small only by relaxing exact norm or allowing increasing energy; they do not supply exact full-data/full-norm transfer at a fixed density. Rescaling the whole vector to recover its norm changes its retained old amplitudes and relative reference data.

Even at the finite target level a graft is not the common compression of (62.7). With current-root degrees and field defined as in §55 on the new source, the relocated old root gains degree one, and its old field values become $\phi(Lp)=\phi(Rp)=\phi(p)/2$. For the one-particle occurrence injection $\iota$ this gives

$$
\iota^*L_{D'}\iota=L_D+|e_o\rangle\langle e_o|,
\qquad
\iota^*H_{D',1}\iota-H_{D,1}
=a|e_o\rangle\langle e_o|+\tfrac g2 M_{\phi|D}.     \tag{66.12}
$$

Old seams persist, but current-root anchoring does not. If a different graft comparison retains the old physical root/field instead, it must declare that law and all added ports and boundary conditions; it cannot use (62.7) by renaming addresses. Likewise its common and killed pair targets need their own faithful identification/update, rather than importing (66.5). The moving-root realization of legacy §52 is a distinct field/boundary contract. Proposition66.8 is an obstruction to the stated active-space full-retention requirement, not a proof that every physical graft realization is impossible. An alternative would have to specify an actual joint retained carrier, its unknown-state isometric ingress, the location and continued accessibility of all old data, new active generator and field, reference phase, collision conditions, clock, acquisition rights and finite price, and prove its correspondence without copying or resetting the unknown state. That bridge remains unresolved here.

**Proposition 66.9 (a planar incidence realization of the same conditional mathematics).** All the full-space maps, trace domains, atomic multipliers and finite-history bounds above admit a compatible injective planar placement of their one-position supports. The same placement included in $\mathbb R^3$ has identical mathematics. This supplies a two-dimensional ambient incidence comparison, not a physical field-mediated counterrealization or a dimension-three selection.

Proof. For each binary address $p$ of depth $d$, let $I_p$ be its dyadic interval in $[0,1]$ and place its port at $(\operatorname{mid}(I_p),-d)$. Join it by a straight segment to the corresponding centers of $I_{pL},I_{pR}$ at level $-d-1$. In each horizontal level band the two children of one parent remain inside that parent's dyadic strip, different parents have disjoint strip interiors, and the two sibling segments meet only at their parent. Bands meet only at their designated port points. This is an injective embedding of the full binary cable tree; every compact planar region meets only finitely many of its level bands and finitely many edges in those bands. For a finite current $D$, retain all actual seams and the next two segments at each current leaf as its grounded stubs, putting zero mass and zero trace at their outer tips. At whole-rho these very tips become the newborn atoms, so Definition66.2 is compatible with this single drawing. At fixed cap only a finite public address cover and its ground tips are needed; the infinite drawing is a mathematical comparison, not an infinite commissioned apparatus.

Push forward the mass-one atomic measure and $\delta\,dx$ on each intrinsic unit cable. An intrinsic coordinate, not the planar segment's Euclidean length, defines the derivative form. The resulting map is a one-particle Hilbert/form isometry. Its product placement is injective on ordered pairs and carries the actual diagonal to the same-position diagonal, so its symmetric restriction preserves all mixed measures, dissected cells, boundary equalities and collision traces of Definition64.5. Copy the explicitly declared $\phi_A$ and both complete atomic pair multipliers; the transported operators are unitarily equivalent by closed-form representation. The full-space inclusions, calibrated preparations and error estimates therefore transport as well. They are not merely a fit of a root response or a ten-pair scalar table. $\square$

If an edge has Euclidean arclength $\ell_e$, rewriting its intrinsic form in arclength $s$ gives cable density $\delta/\ell_e$ and derivative coefficient $\ell_e$: $\delta\int_0^1|F|^2dx=(\delta/\ell_e)\int_0^{\ell_e}|f|^2ds$ and $\int_0^1|F'|^2dx=\ell_e\int_0^{\ell_e}|f'|^2ds$. These are declared graph weights with singular atomic masses and junction/collision conditions, not an isotropic ambient Laplace operator. No ambient inverse-distance or hyperbolic point Green law is substituted for $G^{\rm c},G^{\rm k}$, so the actual all-pair obstructions of Chapters64–65 remain intact. Positive tube width, transverse modes, leakage, local spatial force, finite packing, displacement metrics and construction resources are absent from an incidence drawing.

For contrast, any injective continuous cable-support embedding with a degree-three port cannot lie in $\mathbb R$. Three distinct incident arc germs must have disjoint interiors. Each image germ is an interval extending to the left or right of the image port; two of the three choose the same side, and their intervals overlap, violating injectivity. Every nonroot port of $X_D$ has incidence three, including its grounded stubs, so a nonsingleton authentic $D$ gives this one-dimensional obstruction. The singleton's two-stub interval has no such obstruction. It is a topological limitation of this particular injective-support contract, not exclusion of every one-dimensional encoded, nonlocal or temporally routed apparatus. A planar placement defeats inference that this graph-support mechanism alone requires three ambient dimensions, but it supplies no full physical two-space counterexample.

**Definition 66.10 (exact suppliers, completed relations and remaining obligations).** Source, occurrence, boundary, record and actual renewal semantics are supplied by Continuation Definition1.1, TM22–23, TM30, PR57 and §§55,58,60,62. The fixed-space harmonic minimizers, actual collision domain, residual operator relation and idle evolution estimate are precisely Definition64.5 and Theorems64.6–64.7. Their mature closed-form and contact-domain methods are credited in Definition64.9, including Bolte--Kerner arXiv:1207.5648v1, Definition3.1 and Proposition3.2 in its Lebesgue-product metric-graph scope. It does not supply the atomic mixed-stratum enlargement map used here. No new third-party theorem about changing atomic cable spaces is assumed. Direct-sum isometry, trace continuity, polarization, bounded-perturbation Duhamel and the endpoint estimate are classical intermediates. The new source-qualified deductions are (66.1)–(66.9), the faithful accepted-graft retention obstruction and finite-energy cost (66.11)–(66.12), and their compatible planar incidence comparison. They are ordinary repo-derived proofs, without mathematical-priority, fresh Lean/kernel, physical or CI claims.

The full whole-rho state-transfer and finite-history gap named in Proposition64.8 is resolved within its explicitly supplied stratified producer: every old mixed component is kept, every new atomic mass is treated, identity versions and composition hold, and one density gives a common full-norm bound for both occupations and both separately commissioned pair prescriptions. This does not construct the source-owned cable switch or license its physical execution. The graft obstruction concerns exactly literal old-stratum retention plus exact norm in the new active cable space; other retained-carrier graft contracts remain unresolved. No idle isometry or old-root relabeling is offered as their proof.

All remaining physical/native bridges of Definition65.9 retain their scope: the operation- and metric-preserving displacement map; an isotropic local physical realization and its packing/transverse/exterior/collision controls; a genuine field mediator producing every common/killed pair coefficient with the unchanged one-body field; actual switching and retained-state graft law; source-independent ingress, unknown-input correlations, preparation, acquisition and readout; same-reference coherence and calibrated physical time; finite precision and every construction, control, service, production, storage, hold, retention, maintenance and total resource cost. A continuum support contains infinite-dimensional interval/cell spaces even at fixed cap. Its mass counts are not finite memory, apparatus mass, a minimum price or an unlimited-resource implementation. Chapter63's binding/spectral conclusions and Chapter65's dimension/reuse limits are consumers and constraints, not new capabilities supplied by the transfer.

In particular the original $\mathcal D_2$ source still has its independent arbitrary unbounded actor $a$, including zero, its untagged radius-$7/25$ $b$, destructive actions, jointly adversarial/history-dependent errors, source-independent initialization and original INITIAL/Read/refusal/Stop. Those variables are not the positive commissioned $a$ and supplied error certificates above. The common $\Pi$ of Definition63.13 retains full-vector, spanning, common-zero, whole quadratic-distance/positive-semidefinite Gram, at least two independent directions, alternating bilinear exact-area/Jacobi, actual orthonormal-probe, finite binary-calibration and hidden-kernel-preserving-generator hypotheses. It supplies no cable ingress, new spatial operation or field mediator.

The immutable composition-promised endpoint acquisition of §57 retains its depth caps, common source-independent initialization, actual query/reply histories, finite correct stopping on every same-composition positive and negative source, and distinct actual-address fees. Definition57.12 supplies no old-source archive. The separate paid promised-family archive/cut acquisition of Atomic Generation Acquisition §12 retains its paid positive-root archive, exact nonadvancing cut port, finite stopping/decoding, protected written records after refusal/closure, aligned actual generation, trusted markers, no unrecorded source change, actual write/protect/retain/query rights, closed strong ports and all reply-affecting retained source influence in the service price. Neither acquisition is unknown-state harmonic preparation, source cloning, reset, independent sampling or an exact limit Read. The phase-coherent full-tail minimax theory uses its own once-sampled-depth actual Read process and paid stopped transcript; none of its radii, finite-state counts, update matrices or clock is transferred to these occurrence/cable states.

The planar comparison is compatible with the exact conditional graph laws and defeats only a graph-incidence inference of dimension three. It neither certifies a full physical lower-dimensional counterrealization nor adds a reason selecting three. The original sustained why-three-dimensions question, with its full source/operation/field/acquisition/resource target, remains open beyond this finite ordinary-proof increment.

## 66.99 追加锚（本行以下为增补区）


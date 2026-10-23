# Sparse coherent renewal outputs: the exact first phase-sensitive horizon

This independent companion volume determines the first coherent post-tick horizon at which an arbitrary allowed sparse shift/reset support has a phase-dependent terminal flag law. The result concerns the same observation model as Definition 25.1 of [Real renewal instruments and detector rank II](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK_II.md), with fixed known strictly positive probabilities. Its complete-history formulas, integer phase quotient and sufficient full-orbit separator are antecedents. The additional deductions are an exact per-relation occurrence cost, a source-wide matching lower bound and actual-history witness, a finite cutoff, conformal minimality, and a four-step optimum for the supplied Proposition 25.4 support. The supplied DEV26 append is credited below for its three-support complete-identification horizon and its separate $K=\{1,2,3,4\}$ equality-fiber resolution.

## 1. Scope and evidence

**Convention 1.1 (Handwritten, source-relative theory).** The mathematical statements below are ordinary handwritten deductions for the explicitly supplied family and access hypotheses. This volume is reference input, not Lean truth. It contains no kernel certificate, computational experiment or claim of worldwide originality. Its source correspondence is to the entire supplied Sections 23–25 of `FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK_II.md` at revision `07123ef6f510e6df2d990240c55e29ed9d7c2485`; the entire supplied DEV26 append at revision `87b17201b5fbcbf41101aaf5541c8f990829b021` is a credited input for the identification boundaries recorded below. References embedded in those sources are not independent premises imported here from their original publications.

**Convention 1.2 (Three different questions).** First sensitivity means that the exact probability-law map is nonconstant somewhere on the permitted phase family. Full identification means that its equality fibers are exactly the affine phase orbits. Finite-sample recovery concerns inference from realized measurement records. The theorem of this volume resolves the first question for every allowed support. Supplied DEV26 resolves the complete-identification horizon for every three-support family and for the specified $K=\{1,2,3,4\}$ family; the general least horizon for arbitrary supports remains unresolved here, and no zero-error finite-sample recovery of an unknown continuous phase is supplied.

## 2. The precise preparation and observation model

**Definition 2.1 (Sparse shift/reset family and actual post-tick start).** Let $H\ge2$ be an integer and let $K$ be a finite nonempty subset of $\{1,\ldots,H\}$ containing $H$. Fix known probabilities $p_k>0$ for every $k\in K$, with $\sum_{k\in K}p_k=1$. There is no equal-probability or genericity assumption. Write $\mathbb T=\mathbb R/(2\pi\mathbb Z)$, and allow every $\theta\in\mathbb T^K$. On the orthonormal basis $e_0,\ldots,e_H$ of $\mathbb C^{H+1}$ put

$$
c_k=\sqrt{p_k}e^{i\theta_k},\qquad
x_\theta=\sum_{k\in K}c_ke_{H-k},\qquad
Se_j=e_{j+1}\ (j<H),\quad Se_H=0,\qquad
J_\theta=x_\theta e_H^\dagger.
\tag{2.1}
$$

For nonnegative integers outside $K$, including zero, set $c_k=0$. The classical CP branches are $A\mapsto SAS^\dagger$ and $A\mapsto J_\theta A J_\theta^\dagger$. An actual observed outcome $1$ is a tick. The coherent run starts immediately after such an actual tick, in its normalized posterior $x_\theta x_\theta^\dagger$. An independently posited preparation with different phase dependence is not substituted for this posterior.

**Definition 2.2 (Exactly the additional coherent access).** After the actual tick, apply successively the same stable, accessible isometry

$$
V_\theta\psi=S\psi\otimes|0\rangle+J_\theta\psi\otimes|1\rangle.
\tag{2.2}
$$

Retain all output flags in chronological order, coherently and accessibly. The branch representatives and their phases are stable across these uses. No inaccessible system retains a record distinguishing the coherent histories. There is no intermediate intervention or measurement during this run, and no final memory measurement. All terminal flag POVMs whose effects commute with total tick count are available, including arbitrary effects inside each fixed-count subspace. No access to effects mixing different counts is supplied.

For a chronological word $w=b_1\cdots b_n$, set $K_0=S$, $K_1=J_\theta$ and $K_w=K_{b_n}\cdots K_{b_1}$. Inner products are conjugate-linear in the first entry. The complete terminal datum is

$$
\begin{aligned}
|\Psi_n(\theta)\rangle&=\sum_{w\in\{0,1\}^n}K_wx_\theta\otimes|w\rangle,\\
\Omega_n(\theta)&=\operatorname{Tr}_{\rm mem}|\Psi_n(\theta)\rangle\langle\Psi_n(\theta)|,\\
Q_n|w\rangle&=|w|_1|w\rangle,\\
T_n(\theta)&=\sum_{m=0}^n P_m^{(n)}\Omega_n(\theta)P_m^{(n)},\qquad T_0=1,
\end{aligned}
\tag{2.3}
$$

where $P_m^{(n)}$ projects onto words with $m$ ticks. This is precisely the count twirl of source (25.3), not a state enlarged by a memory readout or a different reference frame.

**Proposition 2.3 (Normalization, observable completeness and the classical-access boundary; source facts).** The preparation and states in Definitions 2.1–2.2 are normalized. Equality of $T_n$ is equivalent to equality of all permitted terminal measurement laws at that horizon. The classical CP branches alone do not supply this coherent access.

**Proof.** One has $\|x_\theta\|=1$ and

$$
S^\dagger S=I-e_He_H^\dagger,\qquad
J_\theta^\dagger J_\theta=e_He_H^\dagger.
\tag{2.4}
$$

Thus $V_\theta$ is an isometry and all its iterated output states are normalized. For every input density $\sigma$,

$$
J_\theta\sigma J_\theta^\dagger=\sigma_{HH}x_\theta x_\theta^\dagger.
\tag{2.5}
$$

Whenever the tick occurs with positive probability, normalization gives exactly the stated posterior. A terminal effect commuting with $Q_n$ is block diagonal and has equal expectation on $\Omega_n$ and $T_n$. Conversely, rank-one effects within any count block are allowed; their expectations determine every quadratic form, and hence the whole Hermitian block. These effects therefore determine $T_n$.

For the access boundary, take a fresh inaccessible orthogonal record at each use:

$$
\widetilde V_\theta\psi
=S\psi\otimes|0\rangle\otimes|r_0\rangle
 +J_\theta\psi\otimes|1\rangle\otimes|r_1\rangle,
\qquad \langle r_0,r_1\rangle=0.
\tag{2.6}
$$

Measuring the flag gives exactly the same two CP branches. Tracing the fresh records makes distinct chronological words orthogonal in the inaccessible system, removing their flag coherences. This is source (24.18) for the present memory. It explicitly separates a classical instrument interface from Definition 2.2. Constant scalar phases on $S,J_\theta$ cancel within each fixed length/count block; phases varying independently from use to use do not fall under the stable-isometry assumption. $\square$

## 3. Integer relations and the endpoint cost

**Definition 3.1 (Affine quotient and its integer lattice).** Put

$$
\Gamma_K=\{(a+bk)_{k\in K}:a,b\in\mathbb T\},\qquad
L_K=\left\{z\in\mathbb Z^K:\sum_kz_k=0,\ \sum_k kz_k=0\right\}.
\tag{3.1}
$$

This is the full integer lattice of source (25.4), rather than a real nullspace or a selected list of triple relations. For $0\ne z\in L_K$, write

$$
\begin{aligned}
z_k^+&=\max(z_k,0),&z_k^-&=\max(-z_k,0),\\
m_z&=\sum_k z_k^+=\sum_k z_k^-,&
s_z&=\sum_k k z_k^+=\sum_k k z_k^-,\\
\ell_z&=m_z+s_z,&
P_z&=\max\{k:z_k>0\},\\
M_z&=\max\{k:z_k<0\},&
B_z&=\min(P_z,M_z),\\
\tau(z)&=\ell_z-1-B_z.
\end{aligned}
\tag{3.2}
$$

Both sign supports are nonempty and disjoint. Thus $P_z\ne M_z$, and $m_z\ge2$: degree one would equate two single labels, forcing $z=0$. The parameters $m_z,s_z,\ell_z$ are source (25.5); $B_z$ and $\tau(z)$ encode the terminal endpoint saving.

Equivalently,

$$
\tau(z)=\max\left\{
\sum_k(k+1)z_k^+-(P_z+1),\quad
\sum_k(k+1)z_k^--(M_z+1)
\right\}.
\tag{3.3}
$$

Each term is the duration of the remaining completed blocks after deleting one largest label on that side. It is a nonnegative integer. The two sides are disjoint integer multisets with equal cardinality and equal label sum; the longer remaining completed duration is the cost, and a terminal unfinished tail supplies the duration difference.

**Definition 3.2 (First sensitivity and character occurrence).** Define

$$
n_{\rm sens}(K,p)=\min\{n\ge0:\theta\mapsto T_n(\theta)\text{ is nonconstant on }\mathbb T^K\},
\tag{3.4}
$$

with value $\infty$ when the set is empty. Entries of $T_n$ will be finite sums of characters $e^{iz\cdot\theta}$ with nonnegative real coefficients. A relation $z$ occurs at a horizon if at least one entry has a nonzero coefficient of its character after grouping equal exponents. Distinct integer exponents are distinct characters on the unrestricted torus $\mathbb T^K$; their coefficients are unique, as follows by integrating against the conjugate character coordinate by coordinate. Occurrence is a statement about the probability-law family, not about separately recovering a character from a single mixed entry at an unknown phase.

**Proposition 3.3 (Affine invariance and integer annihilator; source facts).** Every $T_n$ is invariant under $\theta\mapsto\theta+\delta$ for $\delta\in\Gamma_K$. Moreover

$$
\{\delta\in\mathbb T^K:z\cdot\delta=0\text{ for all }z\in L_K\}=\Gamma_K.
\tag{3.5}
$$

Consequently nonconstancy may equally be considered on $\mathbb T^K/\Gamma_K$. If $|K|\le2$, the integer lattice is zero and the affine image is the entire phase torus.

**Proof.** The all-history calculation in Proposition 4.1 shows that every entry character belongs to $L_K$. An affine difference contributes $a\sum z_k+b\sum kz_k=0$, proving invariance.

For the reverse annihilator inclusion, when $|K|\ge2$ write $k_0=\min K$, list the other labels as $k_i$, and put $d_i=k_i-k_0$ and $g=\gcd_i d_i>0$. Choose integers $t_i$ with $\sum_i t_i d_i=g$. Given a phase difference annihilating $L_K$, put $\eta_i=\delta_{k_i}-\delta_{k_0}$ and $\beta=\sum_i t_i\eta_i\in\mathbb T$. Every integer vector $v$ with $\sum_i d_i v_i=0$ extends to an element of $L_K$ by setting its $k_0$ coordinate to $-\sum_i v_i$. Apply this to $v=\mathbf e_i-(d_i/g)t$; annihilation gives $\eta_i=(d_i/g)\beta$. Choose $b\in\mathbb T$ with $gb=\beta$, possible because multiplication by a positive integer on a circle is onto. With $a=\delta_{k_0}-bk_0$, this gives $\delta_k=a+bk$ on all of $K$. For one label take $a=\delta_H,b=0$. The forward inclusion follows directly from the two integer equations.

With one label the count equation forces $z=0$. With two distinct labels the count and weighted-count equations together force $z=0$. Equation (3.5) then gives the asserted affine image. This is the direct compact-circle proof of source (25.21); replacing it by real spanning would not justify the conclusion. $\square$

## 4. Every actual overlap, its lower bound and matching witness

**Proposition 4.1 (Complete-history and terminal-coordinate formulas; source facts).** A chronological word with $m$ ticks has a unique decomposition

$$
w=0^{a_1}1\cdots0^{a_m}1\,0^t,
\qquad
K_wx_\theta=\left(\prod_{j=1}^m c_{a_j}\right)S^t x_\theta.
\tag{4.1}
$$

The empty product includes the no-tick history. A completed gap outside $K$ or a tail beyond $H$ gives zero amplitude. For two nonzero length-$n$ histories of the same count $m$, let $a,b\in\mathbb N_0^K$ be their completed-gap multiplicities and let their tails be $t,u$. Then

$$
\begin{aligned}
\sum_k a_k&=\sum_k b_k=m,\\
n&=m+\sum_kka_k+t=m+\sum_kkb_k+u,\\
\langle w|T_n(\theta)|v\rangle
&=c^a\overline{c^b}
\sum_{\substack{k,l\in K\\ k\ge t,\ l\ge u\\ k-t=l-u}}
c_k\overline{c_l},
\qquad c^a=\prod_k c_k^{a_k}.
\end{aligned}
\tag{4.2}
$$

Every summand has a positive coefficient depending only on $p$ and exponent

$$
z=a+\mathbf e_k-b-\mathbf e_l\in L_K.
\tag{4.3}
$$

This formula covers every unfinished tail and every common terminal memory coordinate. Entries between different count sectors are zero.

**Proof.** Since $e_H^\dagger S^j x_\theta=c_j$, each actual completed block obeys $J_\theta S^j x_\theta=c_jx_\theta$. Iteration proves (4.1), including invalid completed gaps. Also

$$
S^t x_\theta=\sum_{k\in K,\ k\ge t}c_ke_{H-(k-t)}.
\tag{4.4}
$$

The partial-trace entry is $\langle K_vx_\theta,K_wx_\theta\rangle$. Equality of the terminal basis coordinates is exactly $k-t=l-u$, giving (4.2). Equal count yields $\sum_jz_j=0$. Equal duration yields $\sum_jj(a_j-b_j)=u-t$, whereas coordinate equality gives $k-l=t-u$. Their sum yields $\sum_jjz_j=0$. Each coefficient is a product of strictly positive square roots of the fixed probabilities. The count twirl deletes unequal-count entries. In the no-tick case there is a single word, $t=u=n$ and $k=l$, so its exponents are zero. These are source (25.13)–(25.16), retained with the same chronology and actual start. $\square$

**Theorem 4.2 (Exact first occurrence of each integer relation).** Under Definitions 2.1–2.2, every $0\ne z\in L_K$ has exact first character occurrence at

$$
\boxed{\tau(z)=\ell_z-1-\min(P_z,M_z).}
\tag{4.5}
$$

No actual terminal overlap summand carries $z$ at any smaller horizon. An occurrence with a nonzero common factor between its two nonnegative exponent vectors is strictly later than $\tau(z)$. At $\tau(z)$, an explicit pair of distinct actual histories of the same count has a coefficient at $z$ of at least

$$
A_z=\prod_{k\in K}p_k^{|z_k|/2}>0.
\tag{4.6}
$$

A fixed permitted three-outcome projective measurement at that horizon has a nonconstant probability law. The assertion does not require that the chosen entry contain only one character.

**Proof.** First consider any summand of any actual overlap (4.2) having exponent $z\ne0$. Write its common terminal residual label as

$$
\rho=k-t=l-u\ge0,
\qquad A=a+\mathbf e_k,\quad B=b+\mathbf e_l.
\tag{4.7}
$$

Define their coordinatewise common factor $f_j=\min(A_j,B_j)$. Then

$$
A=z^++f,\qquad B=z^-+f,\qquad
W(f)=\sum_j(j+1)f_j.
\tag{4.8}
$$

Counting degrees gives $m+1=m_z+\sum_j f_j$. Counting weighted labels in $A$ gives $\sum_jja_j+k=s_z+\sum_jjf_j$. Substituting into $n=m+\sum_jja_j+t$ and using $t=k-\rho$ gives the exact identity

$$
\boxed{n=\ell_z-1+W(f)-\rho.}
\tag{4.9}
$$

If $f=0$, the selected label $k$ belongs to the positive support and $l$ to the negative support. Thus $\rho\le\min(k,l)\le B_z$, and $n\ge\tau(z)$.

If $f\ne0$, put $J=\max\operatorname{supp}f$. The largest labels available on the two sides are $\max(P_z,J)$ and $\max(M_z,J)$. Hence

$$
\rho\le\min\{\max(P_z,J),\max(M_z,J)\}=\max(B_z,J),
\qquad W(f)\ge J+1.
\tag{4.10}
$$

When $J\le B_z$, (4.9) gives $n-\tau(z)\ge W(f)>0$. When $J>B_z$, it gives

$$
n-\tau(z)\ge W(f)+B_z-J\ge B_z+1>0.
\tag{4.11}
$$

This proves the universal lower bound and the strict common-factor delay. It has used every term of the complete overlap formula, including arbitrary multiplicities, unfinished tails and shared terminal coordinates.

For attainment, choose

$$
k=P_z,\quad l=M_z,\quad \rho=B_z,\qquad
a=z^+-\mathbf e_k,\quad b=z^--\mathbf e_l,\qquad
t=k-\rho,\quad u=l-\rho.
\tag{4.12}
$$

The vectors $a,b$ are nonnegative and each has degree $m_z-1$. Concatenate exactly $a_j$ blocks $0^j1$, for example in increasing label order, and append $0^t$ to form $w$. Do the same with $b$ and $u$ to form $v$. Both words have count $m_z-1$ and length

$$
(m_z-1)+(s_z-k)+(k-\rho)
=\ell_z-1-\rho=\tau(z),
\tag{4.13}
$$

with the analogous equality on the negative side. Their tails satisfy $0\le t\le k\le H$ and $0\le u\le l\le H$. Each actual terminal vector is nonzero, because (4.4) includes its selected label. The two vectors share coordinate $e_{H-\rho}$, contributing

$$
c^{a+\mathbf e_k}\overline{c^{b+\mathbf e_l}}
=c^{z^+}\overline{c^{z^-}}
=A_z e^{iz\cdot\theta}.
\tag{4.14}
$$

The sign supports are disjoint, so $k\ne l$. Thus the tails differ, one is zero, and the histories are distinct. No memory projection has been applied: (4.14) is an ordinary contribution of the partial trace.

It remains to establish an observable variation, rather than merely exhibit a formal monomial. Put $C(\theta)=\langle w|T_{\tau(z)}(\theta)|v\rangle$. Formula (4.2), after grouping equal exponents, has the form

$$
C(\theta)=\sum_\gamma D_\gamma e^{i\gamma\cdot\theta},
\qquad D_\gamma\ge0,\qquad D_z\ge A_z>0.
\tag{4.15}
$$

There is no cancellation of its $z$ coefficient. Choose a coordinate $j$ with $z_j\ne0$ and take $\theta_j=\pi/z_j$ modulo $2\pi$, with all other phases zero. Each term has real part at most its value at zero phase, and the $z$ term changes from $D_z$ to $-D_z$. Therefore

$$
\operatorname{Re}C(0)-\operatorname{Re}C(\theta)\ge2D_z\ge2A_z>0.
\tag{4.16}
$$

Use the fixed projectors onto $(|w\rangle+|v\rangle)/\sqrt2$, $(|w\rangle-|v\rangle)/\sqrt2$, and their orthogonal complement. They sum to $I$ and commute with $Q_{\tau(z)}$, since $w,v$ have equal count. Their probability difference is

$$
\Pr(+\mid\theta)-\Pr(-\mid\theta)=2\operatorname{Re}C(\theta),
\tag{4.17}
$$

which varies by (4.16). This uses only one allowed terminal flag measurement, with no intermediate action or final memory readout. It is the real-quadrature construction of source (25.24)–(25.26), applied to the new actual histories. $\square$

## 5. Exact first sensitivity and a finite structural formula

**Theorem 5.1 (Arbitrary-support first-sensitive horizon).** For every family and access model in Definitions 2.1–2.2,

$$
\boxed{
n_{\rm sens}(K,p)=
\begin{cases}
\infty,& |K|\le2,\\
\displaystyle\min_{0\ne z\in L_K}\bigl[\ell_z-1-\min(P_z,M_z)\bigr],& |K|\ge3.
\end{cases}}
\tag{5.1}
$$

For $|K|\ge3$ the minimum is attained. Its value depends only on $K$, for every fixed strictly positive probability vector allowed on that support. At every smaller horizon the entire datum $T_n$ is phase independent; at the displayed horizon a fixed count-preserving terminal measurement has a nonconstant law.

**Proof.** If $|K|\le2$, Proposition 3.3 gives $L_K=0$. Every character in every actual equal-count entry then has exponent zero by Proposition 4.1; invalid histories and unequal-count entries are zero independently of phase. Hence every $T_n$, including $T_0$, is constant.

If $|K|\ge3$, any three ordered labels supply the nonzero integer relation written in the proof of Theorem 5.2 below. Thus $L_K\setminus\{0\}$ is nonempty. Equation (3.3) makes all costs nonnegative integers, so their set has an attained minimum $V$. If $n<V$, Theorem 4.2 excludes every nonzero overlap exponent at that horizon. All remaining terms have zero exponent, and Proposition 4.1 covers the whole matrix, including every unfinished tail, terminal coordinate and count sector. Thus the entire $T_n$ is independent of phase. A minimizing relation has the actual-history witness and permitted measured variation of Theorem 4.2 at $V$. Consequently $n_{\rm sens}=V$. Strict positivity of $p$ was used only to keep the required amplitudes and coefficients positive. It does not alter the integer cost or its minimum. $\square$

**Definition 5.2 (Explicit finite cutoff).** Assume $|K|\ge3$ and put $h=\max(K\setminus\{H\})$. For every $a<b<c$ in $K$, define

$$
g_{abc}=\gcd(b-a,c-a),\qquad
q_{abc}=\frac{c-a}{g_{abc}},\qquad
U_K=\min_{a<b<c\text{ in }K}(b+1)(q_{abc}-1).
\tag{5.2}
$$

Set

$$
E_K=U_K+h+1,\qquad
\mathcal F_K=\{0\ne z\in L_K:\ell_z\le E_K\}.
\tag{5.3}
$$

These are definitions in finite support arithmetic and bounded integer relations. They do not refer to matrix entries, phase nonconstancy tests or an executed enumeration.

**Theorem 5.2 (Finite exact minimum and support bounds).** The set $\mathcal F_K$ is finite and nonempty, and

$$
\boxed{n_{\rm sens}(K,p)=\min_{z\in\mathcal F_K}\tau(z).}
\tag{5.4}
$$

Every member satisfies

$$
|z_k|\le\left\lfloor\frac{E_K}{k+1}\right\rfloor\quad(k\in K).
\tag{5.5}
$$

Writing, as in source (25.8),

$$
k_0=\min K,\qquad
g=\gcd\{k-k_0:k\in K\},\qquad
d=\frac{H-k_0}{g},
\tag{5.6}
$$

one has $d\ge2$ and

$$
n_{\rm sens}(K,p)\le U_K\le H(d-1)<Hd,\qquad E_K\le Hd.
\tag{5.7}
$$

The strict comparison with $Hd$ concerns first sensitivity; $Hd$ is the source's sufficient full-orbit separation window, a different target.

**Proof.** For any $a<b<c$ the vector supported on that triple with coordinates

$$
z_a=\frac{c-b}{g_{abc}},\qquad
z_b=-\frac{c-a}{g_{abc}},\qquad
z_c=\frac{b-a}{g_{abc}}
\tag{5.8}
$$

is a nonzero integer relation. Its positive and negative degree is $q_{abc}$, its weighted label sum is $bq_{abc}$, and its sign maxima are $c,b$. Thus

$$
\ell_z=(b+1)q_{abc},\qquad
\tau(z)=(b+1)(q_{abc}-1).
\tag{5.9}
$$

Theorem 5.1 gives $n_{\rm sens}\le U_K$. A triple attaining $U_K$ has $\ell_z=U_K+b+1\le E_K$, so it belongs to $\mathcal F_K$.

For every nonzero relation, the two sign maxima are distinct and only one can be $H$. Hence $B_z\le h$. If $\ell_z>E_K$, then

$$
\tau(z)=\ell_z-1-B_z>U_K+h-B_z\ge U_K.
\tag{5.10}
$$

Such a vector cannot minimize the unrestricted cost. Every minimizing vector therefore lies in $\mathcal F_K$, proving (5.4). On either sign side $\ell_z=\sum_j(j+1)z_j^\pm$. For a coordinate on that side, $(k+1)|z_k|\le\ell_z\le E_K$, proving (5.5). A finite product of these bounded coordinate sets is finite, so $\mathcal F_K$ is finite.

For the uniform estimates, choose any interior label $b$ in the endpoint triple $k_0<b<H$. Its gcd $g_{k_0bH}$ is a multiple of the global $g$, so $q_{k_0bH}\le d$. Also $b+1\le H$, and thus its cost is at most $H(d-1)$. This proves $U_K\le H(d-1)$. There is an interior positive multiple of $g$ strictly less than $H-k_0$, so $d\ge2$. Finally $h+1\le H$, giving $E_K=U_K+h+1\le Hd$. All claims are symbolic bounds for arbitrary supports, not results of a support catalogue or numerical search. $\square$

## 6. Necessary conformal minimality

**Definition 6.1 (Conformal decomposition).** A nonzero integer relation $z$ is conformally decomposable if $z=w+v$ for nonzero $w,v\in L_K$ without coordinate sign cancellation. Equivalently $w^+\le z^+$ and $w^-\le z^-$ coordinatewise, with $v=z-w$. Otherwise it is conformally indecomposable. This is an integer sign condition, not a real-span condition or a claim that a particular list generates the lattice.

**Theorem 6.2 (Every proper conformal subrelation is cheaper).** If $z=w+v$ is a conformal decomposition into nonzero relations, then

$$
\tau(w)<\tau(z),\qquad \tau(v)<\tau(z).
\tag{6.1}
$$

Consequently every minimizing relation in Theorems 5.1–5.2 is conformally indecomposable. The exact finite minimum (5.4) may be restricted to the conformally indecomposable members of $\mathcal F_K$.

**Proof.** Absence of sign cancellation gives $\ell_z=\ell_w+\ell_v$. Therefore

$$
\tau(z)-\tau(w)=\ell_v+B_w-B_z.
\tag{6.2}
$$

If $B_z\le B_w$, the right side is positive because $\ell_v>0$. If $B_z>B_w$, choose a sign side of $w$ whose largest label is $B_w$. The same sign side of $z$ has largest label at least $B_z$. Since $w$ has no label that large on this side and there is no cancellation, $v$ contains a label $j\ge B_z$ there. Its sign-side duration gives $\ell_v\ge j+1\ge B_z+1$. Substitution into (6.2) yields $\tau(z)-\tau(w)\ge B_w+1>0$. Interchanging $w,v$ proves the other inequality.

A minimizing relation therefore cannot decompose. A proper conformal subrelation has strictly smaller $\ell$, so if $z\in\mathcal F_K$ then both subrelations remain inside the cutoff. The finite set has a minimizing relation by Theorem 5.2, and that relation is indecomposable; hence the restricted minimum exists and is unchanged. No general finiteness or generation theorem for conformal relations is needed. $\square$

## 7. Three labels and the four-label optimum

**Corollary 7.1 (Exact three-label first sensitivity; supplied DEV26.2 overlap).** For $K=\{a,b,c\}$ with $a<b<c=H$, every allowed positive probability vector has

$$
\boxed{n_{\rm sens}(K,p)=(b+1)\left(\frac{c-a}{\gcd(b-a,c-a)}-1\right).}
\tag{7.1}
$$

**Credit.** Under the same actual post-tick preparation, stable coherent isometry, count-preserving terminal access, and fixed strictly positive probabilities, supplied DEV26.2 proves the least complete single post-tick horizon for every three-support family as

$$
N=(d-1)(b+1),\qquad d=\frac{c-a}{\gcd(b-a,c-a)}.
$$

Its first-sensitivity specialization is exactly (7.1). This corollary is retained as that general-theorem specialization and credited overlap; it is not current-source new mathematical content. The arbitrary-support first-sensitivity theorem and its proof remain the content of Theorems 4.2 and 5.1.

The value six for $K=\{1,2,4\}$ is covered both by source Theorem 25.3 and by the supplied DEV26.2 three-support theorem. The source already proves more for that support: its six-step entry

$$
\langle010100|T_6(\theta)|001001\rangle
=p_1p_2^{3/2}\sqrt{p_4}\,e^{i(2\theta_1-3\theta_2+\theta_4)}
\tag{7.2}
$$

is a pure primitive lattice character and identifies the full orbit through its two quadratures. The supplied DEV26.2 result gives the corresponding general three-support complete-identification horizon. These full-identification and six-step results are credited antecedents rather than current-source newness; the arbitrary-support statement retained here is about first sensitivity.

**Theorem 7.2 (Four-step optimum and failure of triple-only minimization).** Let $H=6$, $K=\{1,3,4,6\}$ and fix any $p_1,p_3,p_4,p_6>0$ summing to one. Then

$$
\boxed{n_{\rm sens}(K,p)=4,}
\tag{7.3}
$$

with actual one-tick coherence

$$
\boxed{
\langle0001|T_4(\theta)|0100\rangle
=p_1p_3+\sqrt{p_1p_3p_4p_6}\,
e^{i(-\theta_1+\theta_3+\theta_4-\theta_6)}.}
\tag{7.4}
$$

Every nonzero relation supported on a triple within this $K$ has cost at least eight. Restricting the exact minimization to triple-supported relations therefore misses the true first horizon.

**Proof.** In coordinate order $(1,3,4,6)$ the relation

$$
z=(-1,1,1,-1)
\tag{7.5}
$$

is source (25.34), and its length-nine complete-tick realization is already source (25.35). Here $m_z=2$, $s_z=7$, $\ell_z=9$, $P_z=4$, $M_z=6$, so the new endpoint cost is $\tau(z)=9-1-4=4$.

The actual amplitudes of the shorter words are $K_{0001}x=c_3x$ and $K_{0100}x=c_1S^2x$. Explicitly,

$$
x=c_6e_0+c_4e_2+c_3e_3+c_1e_5,\qquad
S^2x=c_6e_2+c_4e_4+c_3e_5.
\tag{7.6}
$$

Their common coordinates are $e_2,e_5$, and the partial trace gives

$$
\begin{aligned}
\langle c_1S^2x,c_3x\rangle
&=c_3\overline{c_1}(c_4\overline{c_6}+c_1\overline{c_3})\\
&=\sqrt{p_1p_3p_4p_6}\,e^{iz\cdot\theta}+p_1p_3.
\end{aligned}
\tag{7.7}
$$

This proves (7.4) without measuring the memory. Both words have count one. Their fixed real-quadrature projective measurement is allowed, and its probability difference changes when $\theta_3$ goes from zero to $\pi$ while the other phases remain zero.

For the complete shorter-horizon lower bound, two ticks require at least two completed blocks of length two, hence at least four uses. At $n\le3$ there is at most one tick, and the only completed allowed gap that fits is label $1$: label $3$ already needs four uses. A one-tick word is therefore necessarily $01\,0^{n-2}$, when it fits. The no-tick sector also has only its single word. Every count sector consequently has at most one nonzero history. Its diagonal entry is a product of completed-gap probabilities times

$$
\|S^t x\|^2=\sum_{k\in K,\ k\ge t}p_k,
\tag{7.8}
$$

which is phase independent. Invalid histories are zero and the twirl removes cross-count entries. Thus the whole $T_n$ is constant for $0\le n\le3$, proving the exact optimum four.

For the method counterexample, every triple $a<b<c$ here has $b\ge3$. Its $q_{abc}$ is at least two. Equality $q_{abc}=2$ would force $b-a=g_{abc}$ and $c-a=2g_{abc}$, a three-term arithmetic progression. None exists in this support: an interior midpoint is either $3$ or $4$, and neither has two distinct support partners summing to twice its value. Hence $q_{abc}\ge3$ and its primitive cost is $(b+1)(q_{abc}-1)\ge8$. The full integer-kernel statement of supplied DEV26.2, equation (26.7), applies to the restriction of the two defining equations of $L_K$ to each candidate triple $\{a,b,c\}$, with that triple as the source support; nonzero multiples only increase $\ell$ while leaving $B$ fixed. Relations on at most two labels are zero. Thus every triple-supported candidate costs at least eight, while the four-label relation attains four. This obstruction concerns horizon minimization. It is distinct from source Proposition 25.4's index-five defect for its particular endpoint-anchored triple list, which concerns integer lattice generation. $\square$

## 8. Identification boundaries and separately counted resources

**Convention 8.1 (What the first-sensitive witness determines).** A positive nonzero coefficient in a possibly mixed entry proves nonconstancy of an exact law. It does not imply that equal values of that entry force equal values of each character in it. Consequently Theorem 4.2 does not establish injectivity of $\theta\mapsto T_{n_{\rm sens}}(\theta)$ on every affine orbit. The exact general first full-identification horizon remains unresolved here for arbitrary supports. Supplied DEV26.2 settles every three-support family, and supplied DEV26.3 settles the specified $K=\{1,2,3,4\}$ family. For $|K|\le2$, the source's zero-horizon deterministic orbit identifier and this volume's infinite first-sensitive horizon are compatible: there is only one affine orbit and no phase-dependent law to detect.

The credited source full separator has a different guarantee. For any finite generating family $\mathcal Z$ of the entire integer lattice $L_K$, source (25.6) supplies pure characters at complete-tick lengths $\ell_z$, and source (25.18) supplies them as terminal marginals at one horizon $N\ge\max_{z\in\mathcal Z}\ell_z$. The two quadratures per relation then recover the generator characters, and the integer annihilator (3.5) gives full affine-orbit identification. Source (25.9)–(25.12) constructs an integer generating family with sufficient horizon $Hd\le H(H-1)$ when $|K|\ge3$. This antecedent does not assert a generally optimal full-identification horizon; the strict first-sensitive bound (5.7) does not upgrade it to one.

**Convention 8.2 (Supplied DEV26 identification credits).** The entire supplied DEV26 append at revision `87b17201b5fbcbf41101aaf5541c8f990829b021` uses the same actual post-tick preparation, stable accessible isometry, retained chronological flags, no inaccessible distinguishing record, no intermediate intervention, no terminal memory measurement, count-commuting terminal effects, and fixed strictly positive support probabilities as Definitions 2.1–2.2. Its results are credited supplied results, not re-proved here.

For $K=\{a,b,c\}$, supplied DEV26.2 proves the exact complete-identification horizon $N=(d-1)(b+1)$ with $d=(c-a)/\gcd(b-a,c-a)$, and its theorem includes the first-sensitivity formula retained in Corollary 7.1. It therefore supplies a complete three-support case while the arbitrary-support first full-identification question remains open.

For $H=4$, $K=\{1,2,3,4\}$, supplied DEV26.3 gives the exact equality-fiber obstruction. With

$$
z_1=(1,-2,1,0),\qquad z_2=(1,-1,-1,1),
$$

these vectors form an integral basis of $L_K$. Both characters occur with positive coefficients in the observed whole-density coefficient

$$
C_3=p_1p_2+p_2\sqrt{p_1p_3}\,e^{i(\theta_1-2\theta_2+\theta_3)}
 +\sqrt{p_1p_2p_3p_4}\,e^{i(\theta_1-\theta_2-\theta_3+\theta_4)}.
$$

The terms are aggregated in this single measured coefficient of the full $T_3$; no individually measured monomial is assumed. Supplied DEV26.3 identifies this coefficient and its conjugate as the only phase-dependent entries of the full $T_3$, and provides distinct affine (and corresponding channel/instrument) orbits with the same $C_3$, hence the same full $T_3$, for every fixed positive probability vector. At horizon four the additional whole-density coefficient

$$
C_4=p_1p_3+\sqrt{p_1p_2p_3p_4}\,e^{i(\theta_1-\theta_2-\theta_3+\theta_4)}
$$

isolates the second character after subtracting its known offset and dividing by its known positive coefficient; combining it with $C_3$ isolates the first character. The integral basis then gives exact full identification at horizon four, while all shorter horizons retain the supplied collision. This is a credited DEV26 result and does not alter the arbitrary-support first-sensitivity claims above.

**Proposition 8.2 (Actual herald and sufficient first-sensitive trial resources; source preparation).** If $N=n_{\rm sens}<\infty$, a first-sensitive trial can be prepared from any initial density using at most $H+1+N$ device uses almost surely, with $N$ coherent post-tick uses. This counts logical uses of the supplied device and additional registers; it is not an optimum for hardware, elapsed time, energy or control complexity.

**Proof.** From an arbitrary density $\sigma$, the probability that the first tick follows $a$ observed zeros is

$$
\Pr_\sigma(0^a1)
=\operatorname{Tr}(J_\theta S^a\sigma(S^\dagger)^aJ_\theta^\dagger)
=\sigma_{H-a,H-a}\quad(0\le a\le H),\qquad
\Pr_\sigma(0^{H+1})=0.
\tag{8.1}
$$

The $H+1$ mutually exclusive first-tick probabilities sum to one. The final equality also follows from $S^{H+1}=0$. By (2.5), the actual tick resets to $x_\theta x_\theta^\dagger$ irrespective of the conditional input. Thus monitoring until that tick takes at most $H+1$ uses almost surely, including the tick itself. Stop monitoring at that instant and perform the $N$ coherent applications; the measurement of Theorem 4.2 is made only at their terminal time. Reherald before each trial, including after a previous terminal measurement has changed the conditional memory. No stationary initialization is needed.

A sufficient logical apparatus has source memory $\mathbb C^{H+1}$, $N$ retained two-dimensional flags of joint dimension $2^N$, a reusable two-level herald detector and a three-level terminal outcome pointer. Only one fixed projective setting is needed for sensitivity. The source's $N+3$-state controller, with states $\mathrm{wait},\mathrm{captured}_0,\ldots,\mathrm{captured}_N,\mathrm{done}$, is sufficient. Keeping the waiting time adds a record with $H+1$ possible values. Repetitions require separately stored or processed outcome records; these registers are not absorbed for free into the source memory dimension.

For the three terminal projectors $P_+,P_-,P_0$, a pointer coupling can be chosen as

$$
W=\sum_{o\in\{+,-,0\}}P_o\otimes R_o,\qquad
R_o|\mathrm{ready}\rangle=|o\rangle,\qquad
[W,Q_N\otimes I]=0,
\tag{8.2}
$$

where each $R_o$ is a unitary on the pointer. Orthogonal complete projectors make $W$ unitary; their count commutators imply the displayed conservation. This is the source (25.28) logical terminal realization, applied to the first-sensitive witness. No memory measurement or intermediate observation is added. $\square$

The source full separator with $M$ relations instead uses $2M$ projective settings, a $2M$-valued setting register, a three-level pointer and $6M$ labeled setting/outcome values. Its generator choices and identification objective do not become resources for free in a sensitivity comparison. Conversely, the single sensitivity setting here is not claimed to replace those settings for full identification.

For a continuous affine quotient, a fixed finite number of records from a finite terminal alphabet cannot uniquely identify every quotient point with zero error. Exact probability-law variation is not a finite-sample probability oracle. Repetition can supply statistical estimates, but this volume gives no sample-complexity or generally perfect-discrimination theorem. The presence of a real phase choice with the same classical renewal law also persists from source Theorem 23.2; coherent phase discrimination gives no complex-over-real advantage for generating that classical law and no native physical or field implementation.

## 9. Source correspondence, new content and open boundaries

**Convention 9.1 (Precise source ownership).** The following correspondence uses the supplied Sections 23–25 revision and the supplied DEV26 append revision named in Convention 1.1. Equation numbers refer to those supplied sources unless explicitly marked as equations of this volume.

| Supplied source scope | Role in this companion volume |
| --- | --- |
| Definition 23.1, (23.2)–(23.3), (23.11), Theorem 23.2 | Shift/reset family, normalization, actual reset, and phase-independent classical renewal law. No new classical-law or spectrum result is claimed. |
| Definition 24.1, (24.3), (24.18); Definition 25.1, (25.1)–(25.3) | Stable coherent post-tick access, chronological retained flags, total-count twirl, arbitrary within-sector terminal effects, and the inaccessible-record counterexample. Definitions 2.1–2.2 preserve this access. |
| (25.4)–(25.5), (25.13)–(25.16) | Full integer affine lattice, complete-tick duration, every actual history, and every terminal memory overlap. Definitions 3.1 and Proposition 4.1 expose these as antecedents. |
| (25.20)–(25.21) and the source family-orbit argument (24.7)–(24.9) | Compact integer annihilator and the affine channel/labeled-instrument orbit classification within this family. Proposition 3.3 reuses the direct annihilator proof; no classification of arbitrary CP realizations is claimed. |
| (25.6)–(25.12), (25.18), (25.24)–(25.28) | Pure complete-tick characters, full integer generation, sufficient common full-separation horizon, terminal marginals, quadrature measurements, heralding and logical resource accounting. These remain source results; no new general optimal identification theorem is inferred. |
| Theorem 25.3, (25.29)–(25.32) | Existing exact six-step result and full-orbit identification for $\{1,2,4\}$. Equation (7.2) is credited reuse. |
| Proposition 25.4, (25.33)–(25.36) | Existing four-label relation $(-1,1,1,-1)$, its nine-step complete-tick coherence, and the anchored-triple index-five obstruction. The four-step realization and optimality in Theorem 7.2 are additional deductions. |
| Entire supplied DEV26 append, revision `87b17201b5fbcbf41101aaf5541c8f990829b021`, including Definition 26.1 and Theorems 26.2–26.3 | Three-support complete-identification horizon and the $K=\{1,2,3,4\}$ full-$T_3$ equality-fiber collision with its exact horizon-four separator. These are credited supplied results; no individual monomial readout is inferred. |

**Convention 9.2 (Source-relative additional deductions).** Theorems 4.2, 5.1–5.2 and 6.2 provide the exact arbitrary-support occurrence cost, strict common-factor exclusion, source-wide lower/upper equality, explicit finite cutoff and necessary conformal minimality. Corollary 7.1 is the supplied DEV26.2 general three-support specialization and is not counted as current-source new content. Theorem 7.2 proves the separate four-step optimum for the supplied Proposition 25.4 support and the failure of triple-only horizon minimization. Supplied DEV26.3 independently credits the specified $K=\{1,2,3,4\}$ full-identification resolution. The retained deductions are source-relative and do not claim absence from worldwide mathematics. Naming a lattice relation, reusing its complete-tick character, or reproducing the source six-step case is not counted as additional content.

The source credits phase-enhanced stochastic models to Liu–Elliott–Binder–Di Franco–Gu, binomial exponent relations to Sottile, integer-lattice distinctions to Eisenbud–Sturmfels, and charge twirls to Bartlett–Rudolph–Spekkens. Those credits remain with their stated source scopes. No nested paper or mathematical manuscript was independently checked here; the horizon proof uses the explicit family calculations reproduced above, rather than an unverified transfer from those bibliographies.

**Open question 9.3 (First full identification).** Determine, for arbitrary $K$ beyond the supplied three-support and specified $K=\{1,2,3,4\}$ cases, the least horizon at which the whole count-twirled flag datum separates every affine orbit. The missing step is a characterization of equality fibers of the potentially mixed character entries. Positivity proves nonconstancy at the first occurrence; it does not separate all of their character values pointwise. The source's sufficient full separator and the supplied DEV26 exact cases do not settle the general minimum.

**Open question 9.4 (Efficient exact minimization).** Determine an efficient method to minimize $\tau$ over the finite integer set $\mathcal F_K$, using conformal indecomposability without losing an optimum. The cutoff proves finiteness and gives coordinate bounds, but establishes no complexity bound or efficient algorithm. No enumeration, numerical experiment or computed support catalogue supports an algorithmic claim in this volume.

**Convention 9.5 (Remaining evidence boundary).** These results concern every allowed support and every fixed strictly positive probability vector under the exact stable coherent access and actual post-tick preparation. Allowing zero probabilities, time-varying branch phases, inaccessible distinguishing records, different preparations, intermediate interventions, final memory measurements or cross-count effects changes the problem and is not covered. The handwritten results carry no Lean or external-literature certification, empirical machine-learning conclusion, optimized physical advantage, finite-bit producer result, original hidden-parameter recovery or general parity theorem.

## 追加锚（本行以下为增补区）

# Four-path full-record recovery: coupled collision descent and global phase rigidity

## 48. Coupled effect--trace descent and global phase rigidity

**Definition 48.0 (original domain and cross-volume conventions).** This
section retains the original normalized domain
$\mathcal K=\operatorname{Dens}_2\times U(4)$, ordinary transpose, the two
optimizer signs, one whole feedback unitary, the exact joint squared
Frobenius distance, and exactly one common feedback scalar quotient. Put
$R_\star=13/4$ and retain $g$, $f=g-\kappa\rho$, $V(\xi)$, the attained
sets $\mathcal A_\xi$ and $\mathcal A_{\mathrm{ph,p},\xi}$, and the endpoint
set $\mathcal E_\xi(a_\xi)$ from Sections 42 and 45 of Continuation II.

References to Section 23 and its numbered identities mean the
[source volume, Section 23](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND.md#23-exact-global-reduction-to-realizable-feedback-diagonals).
References to Section 37 and Theorem 37.5 mean
[Continuation I, Section 37](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_I.md#37-exact-cap-envelopes-unique-scalar-selection-and-core-screening);
references to (39.1) mean
[Continuation I, Section 39](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_I.md#39-original-first-transition-endpoints-and-a-selected-level-eighteen-fifths-obstruction).
References to Section 42, Theorem 42.3 and (42.16)--(42.20) mean
[Continuation II, Section 42](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md#42-a-selected-thirteen-fourths-obstruction-and-all-effect-phase-transport).
References to Section 45, Lemma 45.2, Theorems 45.5 and 45.7, and
(45.20)--(45.21) mean
[Continuation II, Section 45](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md#45-strict-fixed-feedback-purification-and-global-purity-through-thirteen-fourths).
References to Section 46, Lemma 46.2, Theorems 46.3, 46.4 and 46.6,
Corollary 46.5 and (46.28)
mean [Continuation II, Section 46](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md#46-global-coherent-cone-remainder-and-the-exact-two-sign-canonical-slice-comparison).
Numbers 48 and 49 refer to the sections, statements and identities of this
volume; the distinct Section 47 remains in Continuation II.

**Definition 48.1 (active rows, labels and the coupled producer).** Let
$h=1/\sqrt2$, $c=\cos(\pi/8)$, $s=\sin(\pi/8)$,
$d=2(h+c)$ and $e=2(h+s)$. In the certificate basis
$F=T^\dagger E^{\mathsf T}T$, write $F\succeq0$ and
$\operatorname{Tr}F=1$, with $H_0=\operatorname{diag}(d^2,e^2)$. For the
active sign $\sigma$ use the rows

$$
\begin{aligned}
 r_1^+&=(h,h),&r_2^+&=(h,-h),
 &r_3^+&=(c,is),&r_4^+&=(c,-is),\\
 r_1^-&=(h,h),&r_2^-&=(-h,h),
 &r_3^-&=(-ic,s),&r_4^-&=(ic,s).
\end{aligned}
\tag{48.1}
$$

These are the two source recovery rows after expressing the feedback
relative to $U_\sigma$. If $V_\sigma=UU_\sigma^\dagger$, define

$$
 a_\sigma(V_\sigma)=\sum_{i=1}^4(V_\sigma)_{ii}r_i^\sigma,\qquad
 L_i^\sigma=r_i^\sigma F^{1/2},\qquad
 b_\sigma=a_\sigma(V_\sigma)F^{1/2}.
\tag{48.2}
$$

The source identity is

$$
 g(E,U)=\operatorname{Tr}(H_0F)-\|b_\sigma\|_2^2.
\tag{48.3}
$$

For a pure effect $F=\psi\psi^\dagger$, $\|\psi\|=1$, put
$\ell_i^\sigma=r_i^\sigma\psi$, $\chi_\sigma=a_\sigma(V_\sigma)\psi$, and

$$
 q_+(\psi)=|\psi_2|^2,\qquad q_-(\psi)=|\psi_1|^2.
\tag{48.4}
$$

The active branch of the exact original distance is

$$
 \rho_\sigma(E,U)=8+2q_\sigma(\psi)-2|\operatorname{Tr}V_\sigma|.
\tag{48.5}
$$

On $0<\xi\le R_\star$, a branch at level $\xi$ is the unique minimizing
original sign by the supplied two-sign budget (42.17)--(42.20). Every
phase feedback below is a whole unitary
$U=\operatorname{diag}(v)U_\sigma$ with $v_i\in\mathbb T$; no independent
column or effect control is introduced. The four rows in (48.1) are
pairwise distinct.

**Lemma 48.2 (reused spectral rectangle descent).** Suppose an actual pair
at $0<\rho(E,U)=\xi\le R_\star$ has an active sign $\sigma$ and, for some
$i\ne j$,

$$
 (V_\sigma)_{ij}\ne0,\qquad L_i^\sigma\ne L_j^\sigma.
\tag{48.6}
$$

Then there is an actual phase pair $(E,U')$ with the same effect $E$, the
same active sign $\sigma$, the same complex active trace
$\operatorname{Tr}V_\sigma$, and the same true original level $\xi$; it
satisfies $g(E,U')<g(E,U)$. In particular, for a positive-definite $F$ every
nonphase input has such a strict phase improvement.

**Proof.** Spectrally write
$V_\sigma=Z\operatorname{diag}(\zeta_1,\ldots,\zeta_4)Z^\dagger$ and
$D_{ik}=|Z_{ik}|^2$. The matrix $D$ is doubly stochastic. Row orthogonality
shows that (48.6) supplies two common-support columns $k,l$ with
$\zeta_k\ne\zeta_l$: if all common-support eigenvalues were equal, the
$(i,j)$ entry of $V_\sigma$ would be that common value times the zero row
inner product. Put

$$
 \delta=\min\{D_{ik},D_{il},D_{jk},D_{jl}\}>0
$$

and let $R_{ij;kl}$ have entries $+1$ at $(i,k),(j,l)$, entries $-1$ at
$(i,l),(j,k)$, and zero elsewhere. Both
$D+\delta R_{ij;kl}$ and $D-\delta R_{ij;kl}$ are nonnegative doubly
stochastic matrices. By the finite Birkhoff--von Neumann decomposition,
each is a convex combination of permutation matrices. For a permutation
$\Pi$ let

$$
 U_\Pi=\operatorname{diag}(\Pi\zeta)U_\sigma,\qquad
 b_\Pi=\sum_i(\Pi\zeta)_iL_i^\sigma.
\tag{48.7}
$$

Every $U_\Pi$ is one actual whole unitary. It has the same complex active
trace $\operatorname{Tr}(U_\Pi U_\sigma^\dagger)=\sum_k\zeta_k$ as $U$.
The exact active-distance identity therefore gives
$\rho_\sigma(E,U_\Pi)=\rho_\sigma(E,U)=\xi$. The effect is unchanged, so
the same $\epsilon=2\det F$ applies. Since (42.19) gives
$\xi+\epsilon<9-L$, (42.20) gives
$$
\rho_{-\sigma}(E,U_\Pi)
 \ge 2(9-L-\epsilon)-\xi>\xi.
$$
Thus the active distance is the true original distance for every
permutation pair. This is the exact Continuation II, Section 42 opposite-sign transport
premise, rather than a consequence of injectivity alone.
If $b^\pm$ denote the two convex averages of the $b_\Pi$ from the two
Birkhoff decompositions, linearity gives

$$
 b^\pm=b_\sigma\pm\delta(\zeta_k-\zeta_l)(L_i^\sigma-L_j^\sigma).
\tag{48.8}
$$

The parallelogram identity and convexity give

$$
\frac12\left(\|b^+\|_2^2+\|b^-\|_2^2\right)
 \ge \|b_\sigma\|_2^2+
 \delta^2|\zeta_k-\zeta_l|^2\|L_i^\sigma-L_j^\sigma\|_2^2.
\tag{48.9}
$$

The inequality includes the nonnegative within-mixture variance. Hence one
of the actual permutation pairs in the two mixtures has squared recovery at
least the right side of (48.9). By (48.3) its $g$ is strictly smaller. The
argument is the supplied spectral rectangle relation, used here only as an
actual same-effect, same-trace comparison. It does not assert that either
perturbed matrix is itself a diagonal law of a prescribed normal orbit.
If $F$ is positive definite, right multiplication by $F^{1/2}$ is injective,
so the distinct rows in (48.1) give $L_i^\sigma\ne L_j^\sigma$ for every
$i\ne j$; a nonphase $V_\sigma$ has a nonzero off-diagonal entry. Together
with the preceding exact-level and opposite-sign transport calculation,
this proves the stated positive-definite mixed conclusion. No pointwise
claim for singular mixed effects is obtained from this injectivity step.
$\square$

**Theorem 48.3 (strict coupled collision descent).** Let
$F=\psi\psi^\dagger$ be pure, $0<\rho(E,U)=\xi\le R_\star$, and let
$U=\operatorname{diag}(v)U_\sigma$ be phase. If, for some $i\ne j$,

$$
 \ell_i^\sigma=\ell_j^\sigma,\qquad v_i\ne v_j,\qquad
 \chi_\sigma\ne0,
\tag{48.10}
$$

then an actual pure phase pair exists at exactly the same true original
level $\xi$ and has strictly smaller $g$. Consequently every pure phase
global minimizer in this interval obeys the collision-locking relation

$$
 r_i^\sigma\psi=r_j^\sigma\psi\quad\Longrightarrow\quad v_i=v_j
 \qquad(1\le i,j\le4).
\tag{48.11}
$$

**Proof.** Write $S=\operatorname{Tr}(\operatorname{diag}(v))=\sum_i v_i$.
The active level formula gives

$$
 |S|=4+q_\sigma(\psi)-\xi/2\ge4-\frac{\xi}{2}\ge\frac{19}{8}>2.
\tag{48.12}
$$

Because $v_i\ne v_j$, the four phases are not all equal, so $|S|<4$.
There is an index $k$ with
$\operatorname{Im}(\overline S v_k)\ne0$. Otherwise every $v_k$ is
$S/|S|$ or $-S/|S|$, and the sum of four such phases has modulus only
$0$, $2$, or $4$, contrary to $2<|S|<4$.
Let $\pi$ interchange $i$ and $j$, and write $\widetilde v=\pi v$. Choose
$k'$ equal to $k$ if $k\notin\{i,j\}$, and equal to $\pi(k)$ otherwise.
Then the entry at $k'$ of $\widetilde v$ is the same phase $v_k$, and the
corresponding labels at $k$ and $k'$ are equal at $t=0$.

Put

$$
 a_0=a_\sigma(\operatorname{diag}v),\qquad
 a_1=a_\sigma(\operatorname{diag}\widetilde v),\qquad
 c_1=a_1-a_0=(v_j-v_i)(r_i^\sigma-r_j^\sigma).
\tag{48.13}
$$

Then $c_1\psi=0$, $c_1\ne0$, and $a_0\psi=a_1\psi=\chi_\sigma$.
Set $\eta=\chi_\sigma c_1^\dagger$. Since
$\psi^\dagger\eta=\overline{c_1\psi}\,\chi_\sigma=0$, the normalized curve

$$
 \psi(t)=\frac{\psi+t\eta}{\sqrt{1+t^2\|\eta\|_2^2}},\qquad t\in\mathbb R
\tag{48.14}
$$

is an actual pure-effect curve with $\psi'(0)=\eta$. Its away population
is $q(t)=q_\sigma(\psi(t))$. Set
$s(t)=4+q(t)-\xi/2$. At $t=0$, $s(0)=|S|$.
The real implicit-function theorem applied to

$$
 \Phi(t,\theta)=\left|S+(e^{i\theta}-1)v_k\right|^2-s(t)^2
\tag{48.15}
$$

produces a real $\theta(t)$ near zero with $\theta(0)=0$ and
$\Phi(t,\theta(t))=0$, because
$\partial_\theta\Phi(0,0)=-2\operatorname{Im}(\overline S v_k)\ne0$.
Rotate entry $k$ of $v$ by $e^{i\theta(t)}$ and entry $k'$ of
$\widetilde v$ by the same factor. Call the resulting phase vectors
$v_0(t)$ and $v_1(t)$. Their complex traces are identical, and their
moduli equal $s(t)$. Therefore the two corresponding actual pairs have
active distance $\xi$. The strict opposite-sign gap at $t=0$ from
(42.20) persists for small $t$, so this active distance remains the true
original distance.

Let $\chi_j(t)=a_\sigma(\operatorname{diag}v_j(t))\psi(t)$ and
$g_j(t)=\psi(t)^\dagger H_0\psi(t)-|\chi_j(t)|^2$. At zero,
$g_0(0)=g_1(0)$ and $\chi_0(0)=\chi_1(0)=\chi_\sigma$.
The phase-correction terms in $\chi_0'(0)$ and $\chi_1'(0)$ agree: when
$k'=k$ this is immediate, and when $k'=\pi(k)$ it follows from
$\ell_i^\sigma=\ell_j^\sigma$. The common energy derivative also cancels.
The remaining difference is

$$
 \chi_1'(0)-\chi_0'(0)=c_1\eta
     =\chi_\sigma\|c_1\|_2^2.
\tag{48.16}
$$

Consequently

$$
 g_1'(0)-g_0'(0)
 =-2\operatorname{Re}\!\left(\overline{\chi_\sigma}
       [\chi_1'(0)-\chi_0'(0)]\right)
 =-2|\chi_\sigma|^2\|c_1\|_2^2<0.
\tag{48.17}
$$

Since the derivative difference in (48.17) is nonzero, at least one of
$g_0' (0)$ and $g_1' (0)$ is nonzero. Choose the sign of a sufficiently
small real $t$ opposite to the sign of that nonzero derivative. The
corresponding actual curve then has $g_j(t)<g_j(0)=g(E,U)$. This is a
coupled effect--trace descent: the population changes with the effect while
the trace is corrected on that same whole feedback. No fixed-population or
separately optimized value has been used. $\square$

**Theorem 48.4 (all nonphase pure low-defect inputs descend to phase).** Let
$F=\psi\psi^\dagger$, $0<\rho(E,U)=\xi\le R_\star$, $g(E,U)<e^2$, and let
$\sigma$ be the active sign. If $U$ is nonphase relative to $U_\sigma$,
there is an actual pure phase pair at the same true original level with
strictly smaller $g$.

**Proof.** Apply Lemma 48.2 whenever some off-diagonal entry of
$V_\sigma$ connects two unequal labels $\ell_i^\sigma\ne\ell_j^\sigma$.
Otherwise $V_\sigma$ is block diagonal in the partition defined by equal
labels: every off-diagonal entry between different blocks is zero. In each
block diagonalize the unitary block and assign its eigenvalues to the
coordinates of that block. This produces a phase vector $v$ with the same
complex trace. Since the label is constant on a block,

$$
 \sum_{i\ \mathrm{in\ block}}(V_\sigma)_{ii}\ell_i^\sigma
 =\ell_{\mathrm{block}}\operatorname{Tr}(V_{\sigma,\mathrm{block}})
 =\ell_{\mathrm{block}}\sum_{i\ \mathrm{in\ block}}v_i.
\tag{48.18}
$$

Thus the phase pair has the same $E$, $\psi$, active sign, level, scalar
recovery and $g$. If all blocks were scalar, $V_\sigma$ would be diagonal,
contrary to the hypothesis. A nonscalar unitary block has two distinct
assigned eigenvalues in two positions $i,j$, while their labels agree.
Since $g<e^2$ and $H_0\succeq e^2I$, the original scalar recovery is
nonzero: $g=\psi^\dagger H_0\psi-|\chi_\sigma|^2<e^2$ implies
$|\chi_\sigma|>0$. Theorem 48.3 now gives a strict same-level phase
improvement. All spectral eigenvalue multiplicities, zero entries of
$Z$, zero individual recoveries, and repeated labels are allowed. $\square$

**Theorem 48.5 (global phase rigidity and the attained minimizing set).** For
$0<\xi\le R_\star$, the actual minimizing sets satisfy

$$
 \boxed{\quad
 \mathcal A_\xi=\mathcal A_{\mathrm{ph,p},\xi}
                  =\mathcal E_\xi(a_\xi).
 \quad}
\tag{48.19}
$$

Every global minimizer obeys (48.11). In particular, the complete actual
nonphase lift ambiguity in the pure minimizer problem is absent throughout
this interval, including selected determinant-zero levels and either active
sign. The equality representatives are exactly those in the explicit set
$\mathcal E_\xi(a_\xi)$ of (45.20), with all common scalar representatives
retained.

**Proof.** The supplied Theorem 45.5 gives global purity. Theorem 45.7,
specifically (45.21), gives
$a_\xi\le V(\xi)<e^2/4-3/16<e^2$. If a global minimizer were nonphase,
Theorem 48.4 would give a strict same-level decrease of $g$ and hence of
$f$, a contradiction. Thus every global minimizer is phase. The attained
phase value and its complete phase representatives are exactly
Theorem 45.7, namely
$\mathcal A_{\mathrm{ph,p},\xi}=\mathcal E_\xi(a_\xi)$; inclusion in the
original domain and the equality of attained values then give (48.19).
The collision-locking relation follows from Theorem 48.3 because every
global minimizer has $g=a_\xi<e^2$ and hence nonzero scalar recovery.

For completeness, a zero total scalar recovery is not silently removed:
if $\chi_\sigma=0$, then $g=\psi^\dagger H_0\psi\ge e^2>a_\xi$, so it cannot
be a global minimizer in this interval. Individual recovery coordinates may
vanish, and zero coherence, singular effects, repeated eigenvalues and
repeated spectral entries remain allowed. The argument uses neither a
population, coherence, $P$, $Q$, effect eigenvalue, eigenvalue gap, nor a
selected determinant as a divisor. The only inversion is the explicitly
nonzero trace derivative in (48.15). $\square$

**Corollary 48.6 (new two-sign global exclusion of the q=0 endpoint).**
For every $0<\xi\le R_\star$, no global minimizer has $q_\sigma=0$, for either
active sign. Hence every minimizing pure phase representative has

$$
 0<q_\sigma<\min\{1,\xi/2\}.
\tag{48.20}
$$

**Proof.** Suppose a global minimizer had $q_\sigma=0$. By (48.19) it has a
phase representative with the same effect and level. The pure active-level
identity gives $x=1-\xi/4\in[3/16,1)$ and $y=\sqrt{1-x^2}>0$. In the notation
of Section 46, $k=b-a>0$, $R_0=ax+b>0$ and, at $q=0$,

$$
 \mu=\frac{ak}{2R_0}>0,\qquad \nu=\frac{k}{2}>0,\qquad t_c=0,\qquad
 \mathfrak D_\sigma(x,0)=\frac{4\mu\nu x^2}{1+x}>0.
\tag{48.21}
$$

Theorem 46.4 says that the canonical corner is the unique equality case in
this fixed $(\sigma,x,q)$ slice. Since a global minimizer cannot be improved
inside that same slice, it must be one of the canonical pairs (46.28). On
that pair the two feedback phases on the active pair $J$ are
$x+iy$ and $x-iy$, hence are different. On the active optimizer effect the
corresponding labels in (48.1) are equal: they are $h,h$ for
$\sigma=+$ and $s,s$ for $\sigma=-$. Theorem 48.3 gives a strict actual
same-level phase competitor, contradicting global minimality.

This is a full-level conclusion. The nonphase matrices
$U U_\sigma^\dagger=\lambda(W_2\oplus I_2)$ (with the block placed according
to $\sigma$) and $\operatorname{Tr}W_2=2x$ from Corollary 46.5 remain genuine
fixed-slice equality representatives. The coupled descent changes the effect
and the trace together, so it does not alter that fixed-slice theorem; it
shows only that none of those nonphase representatives can minimize after
population and level are allowed to vary jointly. The exclusions at $q=1$ and
at the scalar endpoint $x=1$ are the supplied results of Lemma 45.2,
Theorem 45.5, Theorem 46.6 and Theorem 37.5, respectively, and are not
claimed as new here. Thus (48.20) follows. $\square$

## 49. Source correspondence, boundaries and remaining obligations

**Definition 49.1 (mathematical source correspondence).** The normalized-effect basis,
ordinary-transpose convention, exact recoveries, both optimizer signs and
joint metric in (48.1)--(48.5) are the identities (23.2), (23.9)--(23.13)
and (39.1). The exact same-effect, same-complex-trace spectral permutations
and their nonnegative variance are the supplied Theorem 42.3 and identity
(42.16). The rectangle perturbation in Lemma 48.2 is the supplied
Birkhoff/spectral relation specialized to the same actual $E$, sign and
trace; no convex combination is promoted to a new normal-orbit realization.

The finite Birkhoff--von Neumann theorem used in the proof is the standard
finite statement that a nonnegative matrix with all row and column sums one
is a convex combination of permutation matrices; see Vourdas,
*Markov chains with doubly stochastic transition matrices and application
to a sequence of non-selective quantum measurements*,
[arXiv:2203.09468v1, §II.1, (18)](https://arxiv.org/html/2203.09468v1).
The prescribed-diagonal/singular-value theorem of
Jasper--Loreaux--Weiss, [arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3), is used only in the
already supplied realization correspondence for the full diagonal domain; it does not assert that the perturbed doubly stochastic matrices in Lemma 48.2 are diagonals of a fixed normal orbit.

The global purity and the attained phase certificate are supplied
Theorems 45.5 and 45.7. The exact two-sign triangle, determinant-zero fixed
slice and the genuine nonphase $q=0$ equality family are supplied
Lemma 46.2, Theorems 46.3--46.4 and Corollary 46.5. The new deduction is the common exact-level
population--trace deformation (48.14)--(48.17), its collision-locking
consequence, the global nonphase lift elimination and the two-sign full-level
$q=0$ exclusion. No literature-wide originality or absence claim is made.

**Definition 49.2 (unresolved comparison problems).** Equation (48.19) identifies
all actual minimizers with the still unevaluated phase endpoint set, but it
does not evaluate $a_\xi$ or that set. The universal preceding-level phase
inequality remains the supplied same-realization comparison over every
population, both signs, every attained $(X,Y)$ triangle point and every
coherence/alignment phase. In particular the positive unstable sector, the
negative canonical and interior sectors, and their coupled ordering against
$V(\xi)$ remain open.

The exact $\alpha$ and $\beta$, whether they coincide, the maximal exhaustive
geometric-equality prefix, endpoint inclusion or exclusion, and every first
actual competing branch remain undetermined. Pure phase coalescence,
separated pure contact and simultaneous contact remain possible, including at
selected determinant zero; (48.19) removes nonphase lifts but does not turn a
stationary or fixed-slice equality into a global branch certificate. The full
zero set of the phase comparison and the order and attainment of all earliest
branches still require proof.

The statements stop at $0<\xi\le13/4$. No purity, transport or equality
extension beyond that interval is asserted. The zero level retains its
existing optimizer classes. Singular and mixed nonminimizing inputs, zero
coherence, zero individual recoveries, inactive zero trace, repeated
feedback eigenvalues and all common scalar representatives remain in the
original domain. No physical-acquisition or whole-POVM extension is asserted; the full
comparison problem remains unresolved.

## 追加锚（本行以下为增补区）

## 51. Ordered maximizing lengths and the exact vertical-fibre reduction

**Definition 51.1 (fixed slices, original realization and the uniqueness question).**
Retain the original domain
$\mathcal K=\operatorname{Dens}_2\times U(4)$, where
$\operatorname{Dens}_2=\{E\in\mathbb C^{2\times2}:E\succeq0,
\operatorname{Tr}E=1\}$, and the ordinary transpose $\mathsf T$.
The original optimizer pairs $(E_\sigma,U_\sigma)$ and certificate basis
$T=(b_+\ b_-)$ are those of Sections 23 and 48. The distance remains

$$
\begin{aligned}
 \rho_\sigma(E,U)
 &=\min_{|\lambda|=1}
   \bigl(\|E-E_\sigma\|_{\mathrm F}^2
          +\|U-\lambda U_\sigma\|_{\mathrm F}^2\bigr),\\
 \rho(E,U)&=\min\{\rho_+(E,U),\rho_-(E,U)\}.
\end{aligned}
\tag{51.1}
$$

Here $\|A\|_{\mathrm F}^2=\operatorname{Tr}(A^\dagger A)$.
The scalar $\lambda$ multiplies the whole feedback; there are no separate
pair or column quotients. Fix parameters in the full range

$$
 \sigma\in\{+,-\},\qquad
 0<\xi\le\frac{13}{4},\qquad
 0<q<\min\{1,\xi/2\},
\tag{51.2}
$$

and set

$$
\begin{aligned}
 p&=1-q,&x&=1-\frac\xi4+\frac q2,&y&=\sqrt{1-x^2},&L&=1+x,\\
 h&=\frac1{\sqrt2},&c&=\cos(\pi/8),&s&=\sin(\pi/8),
 &d&=2(h+c),\qquad e=2(h+s).
\end{aligned}
\tag{51.3}
$$

Thus $3/16<x<1$, $p,q>0$ and $y>0$. No uniform separation from the
excluded population or $x=1$ limits is assumed. Use exactly the fixed
pair order of (46.2):

$$
\begin{array}{c|c|c|c|c}
 \sigma&J&K&(a,b,\ell,m)&(K_\sigma,K_{-\sigma})\\ \hline
 +&(1,2)&(3,4)&(h,c,h,s)&(d,e)\\
 -&(3,4)&(1,2)&(s,h,c,h)&(e,d).
\end{array}
\tag{51.4}
$$

In particular $0<a<b$ and $\ell>m>0$. For an actual phase feedback
$U=\operatorname{diag}(v)U_\sigma$, $v\in\mathbb T^4$, define

$$
 X=\frac14\left|\sum_{j\in J}v_j\right|^2,
 \qquad
 Y=\frac14\left|\sum_{j\in K}v_j\right|^2,
 \qquad
 \left|\sum_jv_j\right|=2L.
\tag{51.5}
$$

The complete attained domain, including its boundary, is

$$
 \mathcal T_x=\{(X,Y)\in[0,1]^2:\sqrt X+\sqrt Y\ge L\}.
\tag{51.6}
$$

On it put $k=b-a$ and

$$
\begin{aligned}
 Z&=\frac{L^2-X-Y}{2\sqrt{XY}},
 &\Delta&=4XY-(L^2-X-Y)^2,\\
 F&=\sqrt{(1-X)(1-Y)}\sqrt{1-Z^2},\\
 R&=\sqrt{a^2X+b^2Y+ab(L^2-X-Y)}
   =\sqrt{abL^2-akX+bkY},\\
 C&=\sqrt{\ell^2(1-X)+m^2(1-Y)+2\ell mF},\\
 \Gamma_\sigma(x,q;X,Y)&=\sqrt p\,R+\sqrt q\,C.
\end{aligned}
\tag{51.7}
$$

All square roots are nonnegative. Lemma 46.2 gives $X,Y\ge x^2$,
$XY\ge x^2>0$ and $|Z|\le1$. Since
$|\sqrt X-\sqrt Y|<L$, the factorization of $\Delta$ shows that
$\Delta=0$ precisely on $\sqrt X+\sqrt Y=L$.
Also $R^2\ge abL^2-ak>a^2>0$ throughout $\mathcal T_x$.

These formulas retain a single actual realization. In fact Lemma 46.2
constructs, for every point of $\mathcal T_x$, phases $\theta_J,\theta_K$
and signs $\varepsilon_J,\varepsilon_K\in\{\pm1\}$ with

$$
\begin{aligned}
 (v_j)_{j\in J}
 &=e^{i\theta_J}\bigl(\sqrt X+i\varepsilon_J\sqrt{1-X},
                         \sqrt X-i\varepsilon_J\sqrt{1-X}\bigr),\\
 (v_j)_{j\in K}
 &=e^{i\theta_K}\bigl(\sqrt Y+i\varepsilon_K\sqrt{1-Y},
                         \sqrt Y-i\varepsilon_K\sqrt{1-Y}\bigr),\\
 \cos(\theta_J-\theta_K)&=Z.
\end{aligned}
\tag{51.8}
$$

The ordered recoveries are those of (46.4), namely

$$
\begin{aligned}
 M_+(v)&=h(v_1+v_2)+c(v_3+v_4),
 &N_+(v)&=h(v_1-v_2)+is(v_3-v_4),\\
 M_-(v)&=h(v_1+v_2)+s(v_3+v_4),
 &N_-(v)&=h(v_1-v_2)-ic(v_3-v_4).
\end{aligned}
\tag{51.9}
$$

Choosing $\varepsilon_J\varepsilon_K$ with the sign of
$\sin(\theta_J-\theta_K)$ gives, on that same whole feedback,
$|M_\sigma|=2R$ and the maximal $|N_\sigma|=2C$.
If the sine vanishes either product is allowed. The one arbitrary common
scalar on all four $v_j$ remains allowed, including at boundary points.

The pure effects and energy at this population are

$$
\begin{aligned}
 \psi_+^\phi&=(\sqrt p,e^{i\phi}\sqrt q)^{\mathsf T},
 &\psi_-^\phi&=(e^{i\phi}\sqrt q,\sqrt p)^{\mathsf T},\\
 E&=(T\psi_\sigma^\phi(\psi_\sigma^\phi)^\dagger T^\dagger)^{\mathsf T},
 &\mathsf E_\sigma(q)&=K_\sigma^2p+K_{-\sigma}^2q.
\end{aligned}
\tag{51.10}
$$

The same-feedback identity used in Theorem 46.4 is
$g(E,U)=\mathsf E_\sigma(q)-|\chi|^2$, with
$\chi=\sqrt p\,M_\sigma+e^{i\phi}\sqrt q\,N_\sigma$.
The free coherence phase aligns these two recoveries and attains
$|\chi|=2\Gamma_\sigma$ in (51.8). A zero weighted term imposes no
alignment condition. The active branch distance is
$8+2q-4L=4(1-x)+2q=\xi$; the two-sign budget
(42.17)--(42.20) makes it the true original distance throughout (51.2).
Thus the fixed-slice minimum is exactly
$\mathsf E_\sigma(q)-4(\max_{\mathcal T_x}\Gamma_\sigma)^2$.
This is a simultaneous recovery and distance realization, rather than
independent optimizations of $M_\sigma$ and $N_\sigma$.

Finally retain the determinant of (46.13), writing $D_\sigma$ for
$\mathfrak D_\sigma$:

$$
\begin{aligned}
 R_0&=ax+b,&\Gamma_0&=\sqrt p\,R_0+\sqrt q\,\ell y,\\
 \mu&=\frac12\left(\frac{ak\sqrt p}{R_0}
                         +\frac{\ell\sqrt q}{y}\right)>0,\\
 \nu&=\frac12\left(k\sqrt p
                +\frac{(\ell^2x-m^2)\sqrt q}{\ell y}\right),\\
 D_\sigma(x,q)&=\frac{4\mu\nu x^2}{L}-m^2q.
\end{aligned}
\tag{51.11}
$$

No sign assumption on $\nu$ is made. The unresolved universal question is
whether, for every tuple (51.2) with $D_\sigma(x,q)<0$, there is exactly
one ordered pair $(X_*,Y_*)\in\mathcal T_x$ such that

$$
 \Gamma_\sigma(x,q;X,Y)
 \le\Gamma_\sigma(x,q;X_*,Y_*)
 \qquad\text{for every }(X,Y)\in\mathcal T_x.
\tag{51.12}
$$

Only ordered pair lengths are at issue in (51.12); distinct feedback
phases or effects with the same lengths are not identified by this question.

**Proposition 51.2 (boundary exclusion and strict fixed-label ordering).**
For every tuple (51.2) with $D_\sigma(x,q)<0$, every global maximizer
of $\Gamma_\sigma$ on the complete domain $\mathcal T_x$ lies in

$$
 \Omega_x=\{(X,Y):x^2<X<Y<1,\ \sqrt X+\sqrt Y>L\}.
\tag{51.13}
$$

**Proof.** Fix the tuple and suppress its parameters in $\Gamma$.
Compact attainment is Definition 47.1. On all of $\mathcal T_x$,

$$
 F^2=\frac{(1-X)(1-Y)\Delta}{4XY}.
\tag{51.14}
$$

At a point of the curved boundary with $X,Y<1$, increase $X$ by
$\varepsilon>0$. This is feasible for sufficiently small
$\varepsilon$, and $\Delta_X=2(L^2-X+Y)>0$. Consequently
$F(X+\varepsilon,Y)=A\sqrt\varepsilon+O(\varepsilon^{3/2})$
for a constant $A>0$. At the original point $F=0$ and
$C^2=\ell^2(1-X)+m^2(1-Y)>0$. The square root defining $C$ therefore gives

$$
 C(X+\varepsilon,Y)-C(X,Y)
 =\frac{\ell mA}{C(X,Y)}\sqrt\varepsilon+O(\varepsilon).
\tag{51.15}
$$

The change in $R$ is $O(\varepsilon)$ because $R>0$. Since $q>0$,
the positive leading term in (51.15) increases $\Gamma$, excluding
every such curved-boundary point.

On $X=1$ with $x^2<Y<1$, one has $\Delta>0$ and $C=m\sqrt{1-Y}>0$.
Decreasing $X$ introduces a positive order-$\sqrt\varepsilon$
coherent gain by (51.14); the remaining changes in $C$ are
$O(\varepsilon)$, and $R$ increases. On $Y=1$ with $x^2<X<1$,
decreasing $Y$ likewise introduces a positive coherent
order-$\sqrt\varepsilon$ gain, whereas the possible loss in $R$
is only $O(\varepsilon)$; here initially $C=\ell\sqrt{1-X}>0$.
At $(1,1)$, decreasing $X$ is feasible and gives
$C=\ell\sqrt\varepsilon$ while increasing $R$.

At the canonical corner $(x^2,1)$,
$\Gamma=\Gamma_0$. The strict same-slice competitor in Theorem 46.4,
specifically (46.29)--(46.31), gives
$\max_{\mathcal T_x}\Gamma>\Gamma_0$ when $D_\sigma<0$.
Its reconstruction and the two-sign budget are precisely those retained
in Definition 51.1, so this exclusion uses a legal competitor at the
same true original distance.

To compare the two fixed labels, suppose $X>Y$. The point $(Y,X)$
is also in $\mathcal T_x$, while symmetry of $F$ gives

$$
\begin{aligned}
 R(Y,X)^2-R(X,Y)^2&=k(a+b)(X-Y)>0,\\
 C(Y,X)^2-C(X,Y)^2&=(\ell^2-m^2)(X-Y)>0.
\end{aligned}
\tag{51.16}
$$

Both weights are positive, so $\Gamma(Y,X)>\Gamma(X,Y)$.
This is a comparison between distinct ordered points, not a quotient
which exchanges the labels. It also excludes the remaining corner
$(1,x^2)$.

The only diagonal points not already excluded are interior points with
$X=Y<1$ and $\sqrt X+\sqrt Y>L$. The direction $(-1,1)$ is feasible
there. Symmetry and differentiability give zero directional derivative
for $F$, while the directional derivatives of $R^2$ and $C^2$ are
$k(a+b)>0$ and $\ell^2-m^2>0$, respectively. Since $R,C>0$ there,
this direction strictly increases $\Gamma$.
The curved arc, the two straight edges and their three corners exhaust
the boundary of $\mathcal T_x$. Together with the diagonal and
$X>Y$ comparison they leave exactly the region in (51.13).
$\square$

**Theorem 51.3 (unique interior maximum on each open vertical fibre).**
For either row and every tuple (51.2), independently of the sign of
$D_\sigma$, every $Y\in(x^2,1)$ has exactly one maximizing point
$\widehat X(Y)$ on its full closed vertical fibre, and

$$
 (L-\sqrt Y)^2<\widehat X(Y)<1,
 \qquad
 \Gamma_{XX}(X,Y)<0
 \quad\bigl((L-\sqrt Y)^2<X<1\bigr).
\tag{51.17}
$$

**Proof.** The fibre is exactly $[(L-\sqrt Y)^2,1]$.
On its interior set

$$
 u=1-X,\qquad
 v=\frac\Delta X
   =2(L^2+Y)-X-\frac{(L^2-Y)^2}{X}.
\tag{51.18}
$$

Here $u,v>0$; these auxiliary real functions are distinct from the
feedback vector $v$ in (51.5). They satisfy

$$
 F=\sqrt{\frac{1-Y}{4Y}}\sqrt{uv},\qquad
 u_{XX}=0,\qquad
 v_{XX}=-\frac{2(L^2-Y)^2}{X^3}<0.
\tag{51.19}
$$

For $f=\sqrt{uv}$, ordinary differentiation yields

$$
 f_{XX}
 =\frac{u_{XX}v+uv_{XX}}{2\sqrt{uv}}
   -\frac{(u_Xv-uv_X)^2}{4(uv)^{3/2}}<0.
\tag{51.20}
$$

Thus $F_{XX}<0$. Write $Q=C^2$. Since $R,C>0$ on the open fibre,

$$
\begin{aligned}
 C_{XX}&=\frac{\ell mF_{XX}}{C}-\frac{Q_X^2}{4C^3}<0,\\
 R_{XX}&=-\frac{a^2k^2}{4R^3}<0,\\
 \Gamma_{XX}&=\sqrt p\,R_{XX}+\sqrt q\,C_{XX}<0.
\end{aligned}
\tag{51.21}
$$

The lower fibre endpoint has $X,Y<1$ and lies on the curved boundary;
the positive coherent gain in (51.15) excludes it as a fibre maximum.
The upper endpoint is $X=1$ with $x^2<Y<1$, and the inward gain used
in Proposition 51.2 excludes it as well. Neither of these two
perturbations uses $D_\sigma<0$. Continuity gives a maximum on the
closed fibre. All maxima are interior, where the strictly negative
second derivative gives strict concavity and hence uniqueness.
$\square$

**Proposition 51.4 (exact scalar profile, its derivatives and the stationary identity).**
For a fixed tuple (51.2), retain both endpoint fibres and define

$$
 M(Y)=\max_{(L-\sqrt Y)^2\le X\le1}\Gamma(X,Y),
 \qquad x^2\le Y\le1.
\tag{51.22}
$$

Then $M$ is continuous on $[x^2,1]$ and smooth on $(x^2,1)$.
Each endpoint fibre also has exactly one maximizer, so extend the
notation by $\widehat X(x^2)=1$ and $\widehat X(1)=x^2$.
With $\operatorname{argmax}_S H$ denoting the set of all points of $S$
where $H$ attains its largest value, one has the exact set identity

$$
 \operatorname{argmax}_{\mathcal T_x}\Gamma
 =\{(\widehat X(Y),Y):
              Y\in\operatorname{argmax}_{[x^2,1]}M\}.
\tag{51.23}
$$

For $Y\in(x^2,1)$ the derivatives, evaluated at
$(\widehat X(Y),Y)$, are

$$
\begin{aligned}
 \widehat X'(Y)&=-\frac{\Gamma_{XY}}{\Gamma_{XX}},\\
 M'(Y)&=\Gamma_Y,\\
 M''(Y)&=\Gamma_{YY}-\frac{\Gamma_{XY}^2}{\Gamma_{XX}}.
\end{aligned}
\tag{51.24}
$$

If $D_\sigma<0$, every global maximizing pair additionally satisfies

$$
 bF_X+aF_Y=\frac{b\ell^2+am^2}{2\ell m}.
\tag{51.25}
$$

**Proof.** Put $A(Y)=(L-\sqrt Y)^2$ and parameterize the fibre by
$X=A(Y)+(1-A(Y))t$, $0\le t\le1$. The composed objective is continuous
on the fixed compact rectangle $[x^2,1]\times[0,1]$.
Uniform continuity implies continuity of its maximum over $t$,
which is precisely $M(Y)$. This is the compact maximum principle
used here only for the concrete fibres (51.22).

At $Y=x^2$ the fibre is the singleton $X=1$. At $Y=1$ one has
$F=0$ and $C=\ell\sqrt{1-X}$; both $R(X,1)$ and $C(X,1)$ strictly
decrease with $X$. Thus the unique endpoint-fibre maximizers are
$(1,x^2)$ and $(x^2,1)$, respectively. Combined with Theorem 51.3,
this proves that every fibre has exactly one maximizer and proves
(51.23) in both directions.

On the open triangle all the radicands needed for $F,R,C$ are positive,
so $\Gamma$ is smooth. At each fibre maximum
$\Gamma_X(\widehat X(Y),Y)=0$ and $\Gamma_{XX}<0$.
The real implicit-function theorem (Rudin, *Principles of Mathematical
Analysis*, third edition, Theorem 9.28) gives the smooth local graph.
Fibre uniqueness identifies these local graphs with $\widehat X$.
Differentiating this stationarity equation and then
$M(Y)=\Gamma(\widehat X(Y),Y)$ gives (51.24).
The same calculation as (51.18)--(51.21), with coordinates interchanged,
gives $F_{YY}<0$, $C_{YY}<0$ and
$R_{YY}=-b^2k^2/(4R^3)<0$. Hence $\Gamma_{YY}<0$ in the interior.

For $D_\sigma<0$, Proposition 51.2 places every global maximum in
$\Omega_x$, where both first derivatives vanish. Using
$R_X=-ak/(2R)$ and $R_Y=bk/(2R)$ gives

$$
 b\Gamma_X+a\Gamma_Y
 =\frac{\sqrt q}{2C}
   \bigl(2\ell m(bF_X+aF_Y)-b\ell^2-am^2\bigr).
\tag{51.26}
$$

Here $q,C>0$, so stationarity gives (51.25). This identity is necessary
at a global maximum, not a sufficient global comparison.
$\square$

**Corollary 51.5 (conditional restriction of the actual aligning endpoint set).**
Retain $a_\xi=m(\xi)+\kappa\xi$ and the literal aligning endpoint set
$\mathcal E_\xi(a_\xi)$ of (45.20), with all its actual common scalar
representatives. Its definition retains
$|z|^2=t_\sigma(1-t_\sigma)$ and
$\operatorname{Re}(Pz\overline Q)=|P||Q||z|$; when this product is zero
every phase satisfying the modulus condition remains allowed.
Suppose an actual endpoint $(E,U)\in\mathcal E_\xi(a_\xi)$ has an
active sign and population satisfying (51.2) and $D_\sigma(x,q)<0$.
Then its ordered lengths obey

$$
 (X,Y)\in\Omega_x,\qquad
 X=\widehat X(Y),\qquad
 Y\in\operatorname{argmax}_{[x^2,1]}M,
 \qquad
 a_\xi=\mathsf E_\sigma(q)-4M(Y)^2.
\tag{51.27}
$$

**Proof.** Theorem 45.7 and Theorem 48.5 identify this actual endpoint
with a full original minimizer, under their original hypotheses
$0<\xi\le13/4$. It must therefore minimize its own fixed sign,
population and trace-modulus slice. Indeed, Definition 51.1 provides,
for every competing point in the whole $\mathcal T_x$, one actual
whole feedback and an aligning pure effect with those same slice
parameters and the same true original distance. For the actual
endpoint and its lengths, the same-source recovery estimate gives

$$
\begin{aligned}
 g(E,U)
 &\ge\mathsf E_\sigma(q)-4\Gamma(X,Y)^2\\
 &\ge\mathsf E_\sigma(q)
                   -4\bigl(\max_{\mathcal T_x}\Gamma\bigr)^2.
\end{aligned}
\tag{51.28}
$$

The last value is attained inside the same actual slice.
Global minimality forces equality in both comparisons. Since
$\Gamma>0$, its lengths must maximize $\Gamma$. Proposition 51.2
and (51.23) now give all of (51.27).

This implication is conditional on an endpoint from this slice actually
belonging to $\mathcal E_\xi(a_\xi)$; it asserts no contribution by any
negative-determinant slice. Even a unique maximizing length pair within
such a slice would not determine the winning sign or population,
$a_\xi$, or all aligning phase preimages. $\square$

## 52. Source correspondence and the unresolved global scalar comparison

**Definition 52.1 (supplied comparisons and their exact scope).**
The deduction in Section 51 is a repo-derived application and reduction
of the four-path formulas, using ordinary real differentiation,
compactness and the implicit-function theorem. The following source
correspondence specifies its mathematical premises.

The ordinary-transpose convention, both original optimizer signs,
joint squared Frobenius metric and same-feedback identity are
Definition 23.1, (23.9)--(23.13), (39.1), Definition 46.1 and
Definition 48.1. The attained triangle, its boundary reconstruction,
and simultaneous $|M_\sigma|=2R$, maximal $|N_\sigma|=2C$ are exactly
Lemma 46.2. The free effect coherence aligns these same recoveries.
Definition 47.1 supplies compact attainment. The sign-distance
identification uses the two-sign budget (42.17)--(42.20) only on
$0<\xi\le13/4$. These sources do not provide within-slice uniqueness
when $D_\sigma<0$.

Theorem 46.4 supplies the strict canonical competitor used in
Proposition 51.2 when $D_\sigma<0$. Its separate canonical uniqueness
statement for $D_\sigma\ge0$, including $D_\sigma=0$, is retained
with its original phase-equality conditions. Section 51 neither
replaces that statement nor imposes a sign condition on $\nu$.
The new deductions are the exclusion of every other boundary component,
strict fixed-label ordering, uniqueness on every vertical fibre, and
the exact scalar-profile comparison (51.23)--(51.26).

The both-sign gain bound of Theorem 47.2 holds on the whole attained
triangle for $0<x<1$ and $q\in[0,1]$. It is an upper envelope for
$\Gamma-\Gamma_0$ and supplies no equality characterization which
would identify a maximizing pair from the envelope's scalar vertex.
Theorem 37.5 orders rank-one effects only in the enlarged geometric
feedback family $\mathcal C_{34}$, on its stated levels
$0<\xi\le4$; that family is not the full fixed-population triangle.
Theorem 50.3 concerns the positive-active pure branch on
$[11/5,9/4]$, with $\rho_+=\rho=\xi$, and strictly separates its
negative-determinant slices from the selected value $V(\xi)$.
It does not compare two maximizing pairs inside such a slice.
Theorems 45.7 and 48.5 supply the actual endpoint-set identification
used in Corollary 51.5. None of these results is promoted to a
full sign, population or length-uniqueness comparison beyond its domain.

The repository result
$\texttt{StrongConcavityAttainment.exists\_unique\_maximizer}$
has premises of a nonempty complete domain, positive strong-concavity
modulus, upper semicontinuity and boundedness above. Strong concavity
for this $\Gamma$ has not been established. These are sufficient
supplier hypotheses, not necessary conditions added to (51.12).

The external synchronization certificates also retain their own
domains and hypotheses. Boumal,
[arXiv:1601.06114v3, Lemma 2](https://arxiv.org/html/1601.06114v3),
uses a positive semidefinite certificate $S(z)$ for phase
synchronization, with rank $n-1$ giving uniqueness modulo common phase.
Bandeira--Boumal--Singer,
[arXiv:1411.3272v3, Lemma 4.3](https://arxiv.org/html/1411.3272v3),
requires unit diagonal, primal and dual positivity, annihilation and
a real diagonal shift of the objective matrix; its rank-$n-1$ clause
gives a unique rank-one semidefinite optimizer.
[arXiv:1303.0152v1, Theorem 2](https://arxiv.org/html/1303.0152v1)
requires a unimodular vector in the maximal-eigenvalue subspace of
the unconstrained quadratic objective; the lifted formulation and its
semidefinite relaxation are (29)--(30) there.
No matching certificate or fixed-trace, fixed-population,
same-realization bridge to (51.6)--(51.12) is supplied by these
statements. Phase uniqueness is a different conclusion from ordered
length uniqueness. No literature-wide priority or absence claim is made.

**Definition 52.2 (exact residual and limits of the length reduction).**
By (51.23), for every tuple (51.2) with $D_\sigma<0$,

$$
 \text{there is exactly one global maximizing pair in }\mathcal T_x
 \quad\Longleftrightarrow\quad
 \text{$M$ has exactly one global maximum on }[x^2,1].
\tag{52.1}
$$

This equivalence is established, as are boundary exclusion and unique
vertical-fibre maximization. Both endpoint fibres remain in the
comparison; Proposition 51.2 proves that neither can be globally
maximizing when $D_\sigma<0$. The endpoint $\xi=13/4$ is included.
The population endpoints, $\xi=0$ and $x=1$ lie outside (51.2) itself;
they are not removed from the original domain or classified by this
reduction.

The right side of (52.1), uniformly over the original parameter range,
remains unresolved. In (51.24), $\Gamma_{XX}<0$ and
$\Gamma_{YY}<0$, but
$-\Gamma_{XY}^2/\Gamma_{XX}\ge0$.
Separate strict concavity therefore does not determine the sign of
$M''$. No positive Schur complement, failure of uniqueness, or globally
maximizing tie follows from this missing sign control.
A sufficient derivative certificate would have to control the global
profile, for example a global positive-to-negative one-crossing pattern
for $M'$ excluding a maximizing plateau; a local crossing alone is
insufficient. Neither such a certificate nor an actual globally
maximizing tie is established here.

Unique fibre lengths do not assert joint strict concavity, phase
uniqueness, uniqueness in (51.12), or uniqueness for the full original
optimization. Even a proof of (51.12) would leave the winning sign and
population, $a_\xi$, complete phase preimages, the exact $\alpha$ and
$\beta$, first-branch and endpoint classification, and the full
original ordering to their separate comparisons. The conditional
restriction (51.27) does not assert that a negative-determinant slice
contributes to the original minimizing set. No physical-acquisition or
whole-POVM conclusion is drawn.

## 追加锚（本行以下为增补区）

## 53. Positive-trace localization and global uniqueness of the ordered lengths

**Definition 53.1 (full original parameter domain and objective).**
Retain the fixed labels of Definition 46.1 and Definition 51.1. Fix

$$
 \sigma\in\{+,-\},\qquad 0<\xi\le\frac{13}{4},\qquad
 0<q<\min\{1,\xi/2\},\qquad p=1-q,
\tag{53.1}
$$

and put

$$
 x=1-\frac\xi4+\frac q2,\qquad y=\sqrt{1-x^2},\qquad L=1+x,
 \qquad h=\frac1{\sqrt2},\quad c=\cos(\pi/8),\quad s=\sin(\pi/8).
\tag{53.2}
$$

Thus $3/16<x<1$ and $p,q,y>0$, including when $\xi=13/4$.
Use exactly the two rows

$$
\begin{array}{c|c|c|c}
 \sigma&J&K&(a,b,\ell,m)\\ \hline
 +&(1,2)&(3,4)&(h,c,h,s)\\
 -&(3,4)&(1,2)&(s,h,c,h).
\end{array}
\tag{53.3}
$$

Here $0<a<b$, $\ell>m>0$ and $k=b-a>0$. The complete domain is

$$
 \mathcal T_x=\{(X,Y)\in[0,1]^2:\sqrt X+\sqrt Y\ge L\}.
\tag{53.4}
$$

On this whole domain, with nonnegative square roots, retain

$$
\begin{aligned}
 Z&=\frac{L^2-X-Y}{2\sqrt{XY}},\\
 F&=\sqrt{(1-X)(1-Y)}\sqrt{1-Z^2},\\
 R&=\sqrt{a^2X+b^2Y+ab(L^2-X-Y)},\\
 C&=\sqrt{\ell^2(1-X)+m^2(1-Y)+2\ell mF},\\
 \Gamma_\sigma(x,q;X,Y)&=\sqrt p\,R+\sqrt q\,C.
\end{aligned}
\tag{53.5}
$$

Lemma 46.2 gives $X,Y\ge x^2>0$, $XY\ge x^2$ and $|Z|\le1$
throughout $\mathcal T_x$. These are therefore the original continuous
functions on the entire compact triangle, including its curved and
straight boundaries and both endpoint fibres. Finally set

$$
\begin{aligned}
 R_0&=ax+b,\\
 \mu&=\frac12\left(\frac{ak\sqrt p}{R_0}
                              +\frac{\ell\sqrt q}{y}\right),\\
 \nu&=\frac12\left(k\sqrt p+
                 \frac{(\ell^2x-m^2)\sqrt q}{\ell y}\right),\\
 D_\sigma(x,q)&=\frac{4\mu\nu x^2}{1+x}-m^2q.
\end{aligned}
\tag{53.6}
$$

These are the quantities of (46.13) and (51.11); $\mu>0$, and no
hypothesis on the sign of $\nu$ is imposed.

**Lemma 53.2 (positive-trace-cosine localization of every global maximum).**
For every tuple in Definition 53.1 with $D_\sigma(x,q)<0$, every
global maximizer of $\Gamma_\sigma$ on $\mathcal T_x$ satisfies

$$
 x^2<X<Y<1,\qquad \sqrt X+\sqrt Y>L,\qquad X+Y<L^2.
\tag{53.7}
$$

In particular every such maximizer lies in the open convex set

$$
 \mathcal D_A=\{(X,Y):0<X<1,\ 0<Y<1,\ X+Y<A,
                           \ \sqrt X+\sqrt Y>\sqrt A\},
 \qquad A=L^2>1.
\tag{53.8}
$$

**Proof.** Definition 47.1 gives compact attainment on the entire
$\mathcal T_x$. Proposition 51.2 places every global maximizer in
$\Omega_x$ of (51.13), giving all but the last inequality of (53.7).
That proposition excludes the complete curved arc, both straight
edges, all three corners, the diagonal and the reversed ordering.
Its exclusion of the canonical corner uses the same-slice strict
competitor (46.29)--(46.31), valid for $D_\sigma<0$ without $\nu>0$.

Suppress the fixed parameters. At an interior point with $X,Y<1$
and $\sqrt X+\sqrt Y>L$, one has $|Z|<1$, $R,C>0$ and

$$
 Z_X=-\frac{A+X-Y}{4X^{3/2}\sqrt Y}<0.
\tag{53.9}
$$

Indeed $A>1$, $Y\le1$ and $X>0$. If $Z\le0$, putting
$u=1-X>0$ and $v=1-Y>0$ gives

$$
 F_X=-\frac12\sqrt{\frac vu}\sqrt{1-Z^2}
       -\frac{\sqrt{uv}\,Z Z_X}{\sqrt{1-Z^2}}<0.
\tag{53.10}
$$

The second term is nonpositive, while the first is strictly negative.
Moreover

$$
 R_X=-\frac{ak}{2R}<0,\qquad
 C_X=\frac{-\ell^2+2\ell mF_X}{2C}<0.
\tag{53.11}
$$

Thus $\Gamma_X<0$ wherever $Z\le0$ in this interior. A global
maximizer in $\Omega_x$ is an interior point of the original domain,
so its first derivatives vanish. It must have $Z>0$, equivalently
$X+Y<A$, proving (53.7).

The square restrictions and the half-plane $X+Y<A$ are convex.
The strict superlevel set of the concave function
$\sqrt X+\sqrt Y$ is convex as well; hence $\mathcal D_A$ is convex.
On this set $0<Z<1$. $\square$

**Lemma 53.3 (strict joint curvature of the original coherent factor).**
For any fixed scalar $A>0$, define $\mathcal D_A$ by the inequalities
in (53.8). The function

$$
 F_A(X,Y)=\sqrt{(1-X)(1-Y)}
       \sqrt{1-\frac{(A-X-Y)^2}{4XY}}
\tag{53.12}
$$

has negative definite Hessian at every point of $\mathcal D_A$ and
is strictly concave there.

**Proof.** On $\mathcal D_A$ put

$$
 S=X+Y,\qquad B=A-S>0,\qquad
 \theta=\frac{B^2}{4XY}\in(0,1),\qquad u=1-X>0,\quad v=1-Y>0.
\tag{53.13}
$$

All quantities in the following differentiation are smooth there.
For $H=4\theta=B^2/(XY)$, the Hessian is

$$
 \nabla^2H=
 \begin{pmatrix}
 \dfrac{2(A-Y)^2}{X^3Y}&
 \dfrac{A^2-X^2-Y^2}{X^2Y^2}\\[4pt]
 \dfrac{A^2-X^2-Y^2}{X^2Y^2}&
 \dfrac{2(A-X)^2}{XY^3}
 \end{pmatrix},
\tag{53.14}
$$

and

$$
 \det(\nabla^2H)=
 \frac{(A-X-Y)^2\bigl(3A^2-2A(X+Y)-(X-Y)^2\bigr)}{X^4Y^4}.
\tag{53.15}
$$

The full numerator factorization is

$$
\begin{aligned}
 &4(A-X)^2(A-Y)^2-(A^2-X^2-Y^2)^2\\
 &\quad=\bigl[2(A-X)(A-Y)-(A^2-X^2-Y^2)\bigr]
          \bigl[2(A-X)(A-Y)+(A^2-X^2-Y^2)\bigr]\\
 &\quad=(A-S)^2\bigl(3A^2-2AS-(X-Y)^2\bigr).
\end{aligned}
\tag{53.16}
$$

Since $A>S$, the last factor satisfies

$$
 3A^2-2AS-(X-Y)^2>S^2-(X-Y)^2=4XY>0.
\tag{53.17}
$$

The diagonal entries of (53.14) are positive. Thus $\nabla^2\theta$
is positive definite, although positive semidefiniteness will suffice.
Also

$$
 \theta_X=-\frac{B(A+X-Y)}{4X^2Y}<0,\qquad
 \theta_Y=-\frac{B(A-X+Y)}{4XY^2}<0.
\tag{53.18}
$$

Define column vectors

$$
 e=\begin{pmatrix}1/u\\1/v\end{pmatrix},\qquad
 d=\begin{pmatrix}1/u\\-1/v\end{pmatrix},\qquad
 r=-\frac{\nabla\theta}{2(1-\theta)}.
\tag{53.19}
$$

Here $d,e$ are auxiliary vectors, distinct from the optimizer constants
in (51.3), and both components $r_1,r_2$ are positive. Factor
$F_A=wg$, where $w=\sqrt{uv}$ and $g=\sqrt{1-\theta}$. Then

$$
\begin{aligned}
 \frac{\nabla w}{w}&=-\frac e2,&
 \frac{\nabla^2w}{w}&=-\frac14dd^{\mathsf T},&
 \frac{\nabla g}{g}&=r,\\
 \frac{\nabla^2g}{g}
 &=-\frac{\nabla^2\theta}{2(1-\theta)}-rr^{\mathsf T}.
\end{aligned}
\tag{53.20}
$$

The product rule gives the exact joint identity

$$
 -\frac{\nabla^2F_A}{F_A}
 =\frac{\nabla^2\theta}{2(1-\theta)}
   +\frac14dd^{\mathsf T}+rr^{\mathsf T}
   +\frac12\bigl(er^{\mathsf T}+re^{\mathsf T}\bigr).
\tag{53.21}
$$

The mixed term carries a plus sign because $w$ decreases and $g$
increases in both coordinates. This mixed term alone need not be
positive semidefinite. To control it together with the other terms,
write uniquely

$$
 r=\alpha e+\beta d,\qquad
 \alpha=\frac{ur_1+vr_2}{2},\qquad
 \beta=\frac{ur_1-vr_2}{2}.
\tag{53.22}
$$

These auxiliary coefficients obey

$$
 \alpha>0,\qquad \alpha^2-\beta^2=uvr_1r_2>0.
\tag{53.23}
$$

For a column direction $h_0$, put $t=e^{\mathsf T}h_0$ and
$z=d^{\mathsf T}h_0$. The quadratic form of the last three
summands of (53.21) is exactly

$$
\begin{aligned}
 \frac14z^2+(\alpha t+\beta z)^2+t(\alpha t+\beta z)
   &=(\alpha^2+\alpha)t^2
       +\beta(2\alpha+1)tz+(\beta^2+1/4)z^2.
\end{aligned}
\tag{53.24}
$$

Its symmetric coefficient matrix has positive first diagonal entry,
and its determinant is

$$
 (\alpha^2+\alpha)(\beta^2+1/4)
       -\beta^2(\alpha+1/2)^2
   =\frac{\alpha+\alpha^2-\beta^2}{4}>0.
\tag{53.25}
$$

It is therefore positive definite. The vectors $e,d$ are linearly
independent, so a nonzero $h_0$ cannot give $t=z=0$.
The first summand of (53.21) is positive semidefinite by
(53.14)--(53.17). Hence the full right side is positive definite.
Since $F_A>0$, its Hessian is negative definite. Restricting to any
nonconstant line segment in the convex set $\mathcal D_A$ gives a
strictly negative second directional derivative and proves strict
concavity. $\square$

**Theorem 53.4 (unique global maximizing ordered length pair on the entire triangle).**
For every tuple in Definition 53.1 with $D_\sigma(x,q)<0$, there
exists exactly one ordered pair $(X_*,Y_*)\in\mathcal T_x$ such that

$$
 \Gamma_\sigma(x,q;X,Y)\le\Gamma_\sigma(x,q;X_*,Y_*)
 \qquad\text{for every }(X,Y)\in\mathcal T_x.
\tag{53.26}
$$

This pair satisfies all the strict inequalities (53.7). The assertion
holds for both original signs, including $\xi=13/4$, with arbitrary
sign of $\nu$.

**Proof.** Compact attainment gives at least one global maximizer
on the entire $\mathcal T_x$. Lemma 53.2 puts every global maximizer
in $\mathcal D_A$, where $A=L^2$. Lemma 53.3 applies there to the
original $F$. The squared main recovery is the positive affine function

$$
 R^2=abA-akX+bkY.
\tag{53.27}
$$

The squared crossed recovery
$Q_C=C^2=\ell^2(1-X)+m^2(1-Y)+2\ell mF$ is positive and has
Hessian $2\ell m\nabla^2F$. The square-root derivative identities give

$$
\begin{aligned}
 \nabla^2C&=\frac{\ell m}{C}\nabla^2F
       -\frac{\nabla Q_C(\nabla Q_C)^{\mathsf T}}{4C^3},\\
 \nabla^2R&=-\frac{\nabla(R^2)\nabla(R^2)^{\mathsf T}}{4R^3}.
\end{aligned}
\tag{53.28}
$$

The first Hessian is negative definite and the second is negative
semidefinite. Since $p,q>0$, the Hessian of the original
$\Gamma=\sqrt pR+\sqrt qC$ is negative definite on $\mathcal D_A$;
thus $\Gamma$ is strictly concave on that convex set.

If there were two distinct global maximizing pairs on
$\mathcal T_x$, both would belong to $\mathcal D_A$. Their midpoint
would lie in the same convex set and hence in $\mathcal T_x$.
Strict concavity would make its value strictly larger than the common
global maximum, a contradiction. This proves uniqueness against
every competitor in the original compact domain; existence was already
established. Lemma 53.2 gives (53.7). No concavity outside
$\mathcal D_A$ is needed: all boundary points, both endpoint fibres
and every point outside the localization set remain in the original
compact comparison. $\square$

**Proposition 53.5 (original realization, slice value and distance correspondence).**
For every tuple in Definition 53.1 with $D_\sigma<0$, let
$G_*:=\Gamma_\sigma(x,q;X_*,Y_*)$. In the original
$\operatorname{Dens}_2\times U(4)$ problem, the fixed-sign,
fixed-population, fixed-trace phase-slice minimum is exactly

$$
 \mathsf E_\sigma(q)-4G_*^2,\qquad
 \mathsf E_\sigma(q)=K_\sigma^2p+K_{-\sigma}^2q,\qquad
 K_+=2(h+c),\quad K_-=2(h+s).
\tag{53.29}
$$

Every triangle competitor has a simultaneous realization of its main
and maximal crossed recoveries on one whole feedback and an aligning
normalized pure effect, at the true original distance $\xi$.
The scalar identification is the single common scalar of the whole
feedback.

**Proof.** The source correspondence is Definition 23.1 and
(23.9)--(23.13) in the
[original volume](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND.md),
and (42.17)--(42.20), Definition 46.1 and Lemma 46.2 in
[Continuation II](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md).
In the original coordinate order the recoveries remain

$$
\begin{aligned}
 M_+(v)&=h(v_1+v_2)+c(v_3+v_4),&
 N_+(v)&=h(v_1-v_2)+is(v_3-v_4),\\
 M_-(v)&=h(v_1+v_2)+s(v_3+v_4),&
 N_-(v)&=h(v_1-v_2)-ic(v_3-v_4).
\end{aligned}
\tag{53.30}
$$

For every $(X,Y)\in\mathcal T_x$, Lemma 46.2 gives
$U=\operatorname{diag}(v)U_\sigma$ with

$$
\begin{aligned}
 (v_j)_{j\in J}&=e^{i\alpha_0}
   \bigl(\sqrt X+i\varepsilon_J\sqrt{1-X},
         \sqrt X-i\varepsilon_J\sqrt{1-X}\bigr),\\
 (v_j)_{j\in K}&=e^{i\beta_0}
   \bigl(\sqrt Y+i\varepsilon_K\sqrt{1-Y},
         \sqrt Y-i\varepsilon_K\sqrt{1-Y}\bigr),\\
 \cos(\alpha_0-\beta_0)&=Z,\qquad
 \left|\operatorname{Tr}(UU_\sigma^\dagger)\right|=2L.
\end{aligned}
\tag{53.31}
$$

The signs $\varepsilon_J,\varepsilon_K$ take values in $\{\pm1\}$.
Choose their product with the sign of $\sin(\alpha_0-\beta_0)$;
when that sine vanishes either product is allowed. This yields,
simultaneously on the same whole feedback,
$|M_\sigma|=2R$ and $|N_\sigma|=2C$, the latter being the largest
crossed modulus compatible with these lengths and trace.
There remains one arbitrary common unit scalar multiplying all four
entries. The ordered pairs $J,K$ are precisely (53.3), without
interchanging their labels. The reconstruction includes all triangle
boundaries and does not discard their phase representatives.

The normalized effects retain the ordinary transpose:

$$
\begin{aligned}
 \psi_+^\phi&=(\sqrt p,e^{i\phi}\sqrt q)^{\mathsf T},&
 \psi_-^\phi&=(e^{i\phi}\sqrt q,\sqrt p)^{\mathsf T},\\
 E&=(T\psi_\sigma^\phi(\psi_\sigma^\phi)^\dagger
                                  T^\dagger)^{\mathsf T},&
 T&=(b_+\ b_-).
\end{aligned}
\tag{53.32}
$$

Thus $p$ is the population on $b_+$ in the positive row and on $b_-$
in the negative row; $q$ is the population away from that active
optimizer. The free coherence phase aligns the two actual recoveries
in the same-feedback identity

$$
 g(E,U)=\mathsf E_\sigma(q)-|\chi|^2,\qquad
 |\chi|=\sqrt p\,|M_\sigma|+\sqrt q\,|N_\sigma|=2\Gamma_\sigma.
\tag{53.33}
$$

If a weighted recovery vanishes its alignment condition is void.
The original joint squared Frobenius distance is

$$
 \rho(E,U)=\min_{\tau\in\{+,-\}}\ \min_{|\zeta|=1}
 \left(\|E-E_\tau\|_{\mathrm F}^2
                    +\|U-\zeta U_\tau\|_{\mathrm F}^2\right).
\tag{53.34}
$$

For the active branch, (53.31)--(53.32) give

$$
 2q+8-4L=4(1-x)+2q=\xi.
\tag{53.35}
$$

The two-sign budget (42.17)--(42.20) makes the other branch strictly
larger throughout $0<\xi\le13/4$. Hence this is the true original
distance, including at its upper endpoint. The sign choice in
(53.34) is joint and $\zeta$ multiplies the entire feedback.
For arbitrary phases the same-source recovery estimate is
$|\chi|\le2\Gamma_\sigma$; the construction above attains equality
for every triangle point. Maximizing over the whole triangle and
using Theorem 53.4 proves (53.29). $\square$

**Corollary 53.6 (the scalar uniqueness question and the actual endpoint consumer).**
For every tuple in Definition 53.1 with $D_\sigma<0$, retain the
full profile and both endpoint fibres from Proposition 51.4:

$$
 M(Y)=\max_{(L-\sqrt Y)^2\le X\le1}\Gamma_\sigma(x,q;X,Y),
 \qquad x^2\le Y\le1.
\tag{53.36}
$$

It has exactly one global maximizing argument $Y_*$, with
$X_*=\widehat X(Y_*)$. Thus the right side of (52.1) holds uniformly
over all the parameters (53.1) with $D_\sigma<0$.

Retain the actual aligning endpoint set $\mathcal E_\xi(a_\xi)$
of (45.20), where $a_\xi=m(\xi)+\kappa\xi$. If an actual endpoint
$(E,U)\in\mathcal E_\xi(a_\xi)$ has active sign and population
satisfying these hypotheses, its ordered lengths are exactly
$(X_*,Y_*)$ and

$$
 a_\xi=\mathsf E_\sigma(q)-4G_*^2.
\tag{53.37}
$$

Its literal endpoint coherence conditions remain

$$
 |z_{\rm coh}|^2=t_\sigma(1-t_\sigma),\qquad
 \operatorname{Re}(Pz_{\rm coh}\overline Q)
                       =|P||Q||z_{\rm coh}|.
\tag{53.38}
$$

Every modulus-compatible phase remains allowed when the product on
the right is zero.

**Proof.** Proposition 51.4 gives the exact argmax identity (51.23),
including both endpoint fibres and their unique fibre maximizers.
Theorem 53.4 makes its left side the singleton $\{(X_*,Y_*)\}$.
Its right side therefore has exactly one argument $Y_*$, and
$X_*=\widehat X(Y_*)$. This answers the uniform scalar uniqueness
question isolated in Definition 52.2. Separate concavity in the two
coordinates did not control the mixed derivative in (51.24).
Here (53.21)--(53.25) control the full mixed term on a convex set,
and Lemma 53.2 places every possible original global maximizer in
that set. Global concavity of $M$ on its entire interval is not a
premise of this conclusion.

For the actual endpoint, Theorems 45.7 and 48.5 and Corollary 51.5
force its lengths to maximize the entire original triangle.
Indeed, (51.28) compares it with every same-slice competitor,
and Proposition 53.5 retains their actual simultaneous realization
and the same true original distance. Equality forced by original
global minimality makes its lengths a global maximizing pair.
Theorem 53.4 fixes that pair to $(X_*,Y_*)$; substituting into
(51.27) gives (53.37). The coherence conditions in (53.38) are those
of the original endpoint set. This implication is conditional on an
endpoint from the slice actually belonging to
$\mathcal E_\xi(a_\xi)$; it proves no existence of a contributing
negative-determinant slice. $\square$

**Definition 53.7 (source dependencies and remaining mathematical boundaries).**
Lemma 46.2 and Definition 47.1 supply exact realization and compact
attainment. Proposition 51.2 supplies full boundary and ordering
exclusion, using the strict canonical competitor of Theorem 46.4.
Theorem 51.3 and Proposition 51.4 supply fibre uniqueness and the
profile correspondence; Corollary 51.5 supplies the conditional
endpoint restriction. The added deductions are the localization
(53.9)--(53.11), the specific Hessian-square calculation
(53.14)--(53.18), the complete mixed-term positivity
(53.21)--(53.25), and their use to establish the full-domain
uniqueness (53.26). The square-root composition and the fact that
strict concavity on a convex set excludes two maximizing points are
elementary steps within these proofs, not separate new results.
No literature-wide originality assertion is made.

Theorem 53.4 and Corollary 53.6 settle the scalar question in (52.1)
on exactly (53.1) with $D_\sigma<0$. They impose no sign restriction
on $\nu$ and include $\xi=13/4$. They do not compute $G_*$, choose
a winning sign or population, evaluate $a_\xi$, identify a
contributing slice, or establish uniqueness of a whole feedback,
effect or phase representative. They do not classify all aligning
phase preimages, the full first-transition ordering, or the exact
$\alpha,\beta$ of the original optimization. The auxiliary
coefficients in (53.22) are unrelated to those optimization quantities.
No physical-acquisition or whole-POVM conclusion follows from ordered
length uniqueness.

The cases $q=0$, $q=1$, $\xi=0$ and $x=1$ are outside (53.1) and
receive no new classification here. The separate canonical result
of Theorem 46.4 for $D_\sigma\ge0$, including determinant zero and
its original phase-equality conditions, is unchanged. No larger
distance interval is claimed. The synchronization and semidefinite
certificate-existence conditions discussed in Definition 52.1 are
neither used nor established by this curvature argument.

## 追加锚（本行以下为增补区）

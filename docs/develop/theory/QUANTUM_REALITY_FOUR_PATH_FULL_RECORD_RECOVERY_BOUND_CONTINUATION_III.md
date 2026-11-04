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

# Finite original-label cores and omitted mass

Section 14 of [Complete event laws and first-hit costs](43-sharp-first-hit-ambiguity-with-identical-complete-event-laws.md), using the [section 13 overlap interface](46-rectangular-overlap-and-all-height-budgets.md).

## 14. Retain a finite original-label core and pay the omitted actual mass

This is an ordinary extension of the rectangular defect certificate, with
no Lean or literature-priority claim. The actual full family, original
numerical moduli, residues, incoming probability and clipping kernel stay
fixed throughout. Selecting a core is an auxiliary proof operation, not a
new physical experiment with the omitted labels removed.

### 14.1. Data and certificate

Use the finite interface of Section 13: X,Y are old coordinate blocks;
Z is a fresh uniform current coordinate, |Z|=n. Original label i is
R_i x J_i, where R_i=A_i x B_i. Its actual full forbidden union has mass
alpha(x,y), and rho is the actual incoming old probability, possibly
correlated and with holes. The fixed actual threshold is delta(x,y) in
(0,1), u=min(alpha,delta)/(1-min(alpha,delta)), and T=E_rho[u].

The defects e_X,e_Y are still those of the FULL clipped law, relative to
rho_X x nu and rho_Y x nu. Choose any subset I of the original labels.
Let

\[
 \begin{aligned}
 B_I(x,y)&=\bigcup_{\substack{i\in I\\(x,y)\in R_i}}J_i,\\
 \alpha_I(x,y)&=\nu(B_I(x,y)),\\
 \alpha_I^*&=\max_{\text{all }(x,y)\in X\times Y}\alpha_I(x,y),\\
 S_I&=\sum_{i\in I}\nu(J_i),\\
 D_I&=\mathbb E_\rho\!\left[u\frac{\alpha-\alpha_I}{\alpha}\right].
 \end{aligned}
 \tag{FA93}
\]

The last integrand is zero when alpha=0. All geometric maxima include
zero-probability cells. Then

\[
 e_X+e_Y+D_I\ge T\left(1-\sqrt{\alpha_I^*S_I}\right)_+.
 \tag{FA94}
\]

The omitted mass admits the actual-source bounds

\[
 \begin{aligned}
 D_I&\le\mathbb E_\rho\!\left[\frac{\alpha-\alpha_I}{1-\delta}\right]\\
 &\le\sum_{i\notin I}\nu(J_i)\int_{R_i}\frac{1}{1-\delta}\,d\rho.
 \end{aligned}
 \tag{FA95}
\]

In particular, if delta(x,y)<=delta_bar<1 everywhere on the support of
rho, put c=1/(1-delta_bar). Then

\[
 e_X+e_Y\ge
 \left[T\left(1-\sqrt{\alpha_I^*S_I}\right)_+
       -c\sum_{i\notin I}\rho(R_i)\nu(J_i)\right]_+.
 \tag{FA96}
\]

Empty I and T=0 are allowed and give valid, possibly zero bounds. No
claim is made that a useful core or a positive bound always exists.

### 14.2. Proof with the full kernel unchanged

Assume T>0, the other case being immediate. For every current leaf z set
U_z={(x,y):z in B(x,y)} and U_z^I={(x,y):z in B_I(x,y)}. Define the SAME
weights and targets as in Section 12:

    W=rho u/(n alpha),  M_z=W 1_{U_z},
    H=sum_z M_z=rho u,
    m=T/n,  a=H_X/T,  b=H_Y/T,

where W=0 at alpha=0. The matrices M_z have the same actual defect
expressions e_X,e_Y as before. Row-then-column trimming supplies matrices
M'_z<=M_z with marginals bounded by ma,mb and total retained mass at least
T-e_X-e_Y. This uses the full forbidden union and full original kernel.

Now set F_z=M'_z 1_{U_z^I}. Removing these entries can only reduce row
and column sums. Its removed mass satisfies

\[
 \begin{aligned}
 \sum_z\sum_{x,y}(M'_z-F_z)
 &\le\sum_z\sum_{x,y}W\mathbf1_{U_z\setminus U_z^I}\\
 &=\sum_{x,y}\rho u\frac{\alpha-\alpha_I}{\alpha}\\
 &=D_I.
 \end{aligned}
 \tag{FA97}
\]

Consequently total mass in the F_z is at least T-e_X-e_Y-D_I.
Split each F_z among only the retained original rectangles whose current
prefix contains z. Replace each component by its rank-one matrix with
the same marginals, as in Section 12. The resulting matrices Q_z remain
within U_z^I, retain the marginal caps, and have rank at most the number
N_z^I of retained labels active at that current leaf.

Whitening by the same a,b gives A_z with operator norm <=m and
Hilbert--Schmidt square <=m^2 N_z^I. The complete geometric multiplicity
of these retained supports is K_I=n alpha_I^*, and
sum_z N_z^I=n S_I. Exactly the same entrywise Cauchy--Schwarz argument
therefore gives

\[
 \begin{aligned}
 T-e_X-e_Y-D_I
 &\le\left\|\sum_z A_z\right\|_{\mathrm{HS}}\\
 &\le m\sqrt{K_I\sum_z N_z^I}\\
 &=T\sqrt{\alpha_I^*S_I}.
 \end{aligned}
 \tag{FA98}
\]

All quantities e_X,e_Y,D_I are nonnegative, so (FA98) proves (FA94), including
the positive-part notation. A zero marginal of a or b is handled by
deleting that zero row or column, without ignoring interior zero-source
cells when defining K_I.

For the omitted-mass estimate, t=min(alpha,delta) satisfies

    u/alpha = t/[alpha(1-t)] <= 1/(1-delta)

whenever alpha>0. Further, pointwise,

    alpha-alpha_I
      =nu(B \ B_I)
      <=sum_{i notin I} 1_{R_i} nu(J_i).

Integrating gives (FA95). Apply the common cap c and rearrange (FA94) to
obtain (FA96). Omitted labels are charged separately only in the upper
bound; their overlaps are preserved exactly in D_I.

### 14.3. A sufficient arithmetic estimate for the omitted-label payment

Suppose an actual density certificate supplies rho<=D nu_old, where
nu_old is product full Haar on all complete old prime-power coordinates,
and assume the current base nu is also full Haar.
For an original modulus m_i=d_i p^(a_i), with d_i involving only these
old primes, its literal old cylinder and current prefix then satisfy

\[
 \rho(R_i)\nu(J_i)\le\frac{D}{d_i p^{a_i}}=\frac{D}{m_i}.
 \tag{FA99}
\]

The density certificate is an additional input, not a consequence of
the rank argument. The same D must bound the actual incoming rho, with
its real source normalization and preceding caps retained.

Thus c D sum_{i notin I} 1/m_i is a sufficient payment in (FA96). This sum
is over original labels; numerical distinctness permits domination by
the corresponding no-repeat sum over allowed exponent vectors. For any
fixed finite prime support those complete sums and height tails have
convergent geometric-product expressions. This observation provides a
way to certify a chosen omitted tail; it asserts neither an inexpensive
uniform D over all stages nor an all-prime numerical saving.

For a pure-survivor reference base, use the actual cylinder masses of
that base. Formula (FA99) is specifically for full Haar and must not be
used unchanged after conditioning out roots.

### 14.4. Scope of the improvement

The full-family certificate can become vacuous when the unweighted
current-prefix cost S is large because there are many old cofactors.
This version allows a selected original-label core with a smaller
geometric cost, paying the rest by actual old-cylinder masses. Tiny
omitted cylinders cannot be dismissed for free; their exact payment is
D_I or the certified upper bound in (FA95).

It remains a certificate for a defect of two specified complete block
marginals. It is not a first-hit gain, a surviving-mass lower bound, or
a correction automatically available beyond the existing profile333
payments. Converting the non-scalar defect into useful tail alignment or
a same-family comparison margin remains unproved. In particular, simply
turning a pair defect into a lower bound on total head surplus loses
strength: S>=alpha_* and the pointwise bound
E_rho[(1-alpha)u]>=(1-alpha_*)T already dominates that scalar route.
The core variant does not evade this issue. With
q_I=(1-sqrt(alpha_I^* S_I))_+, the union bound gives q_I<=1-alpha_I^*,
and hence

\[
 \begin{aligned}
 Tq_I-D_I
 &\le\mathbb E_\rho\!\left[u\left(\frac{\alpha_I}{\alpha}-\alpha_I^*\right)\right]\\
 &\le\mathbb E_\rho\!\left[u\frac{\alpha_I(1-\alpha)}{\alpha}\right]\\
 &\le\mathbb E_\rho[u(1-\alpha)].
 \end{aligned}
 \tag{FA100}
\]

At alpha=0 these integrands are zero. Taking positive parts, or replacing
D_I by a larger certified payment, cannot improve this upper bound by
the already known full head surplus. The certificate's additional
information concerns the two specified pair marginals, not their
projection back to scalar head surplus.

At the largest prime of a hypothetical whole cover, a nonzero actual killed incoming measure xi is supported on old survivors whose entire current fibres must be covered. Hence alpha=1 xi-almost everywhere and the actual current kernel equals its declared uniform base; both block-current defects for xi vanish. In this interface the core inequality reduces to xi(u alpha_I)<=xi(u) min(1,sqrt(alpha_I^* S_I)), already implied pointwise by alpha_I<=alpha_I^*<=min(1,sqrt(alpha_I^* S_I)). Thus the terminal interface alone supplies no new contradiction. This statement concerns the actual killed input xi and does not replace the distinct physical input rho. Additional same-family old-cylinder or earlier-stage information is still needed.

### 14.5. An actual nine-label arithmetic source with a strict improvement

Start with the original pure classes 0 modulo 3 and 0 modulo 5. Applying
the full-Haar clipped stages with thresholds 1/3 and 1/5 gives the actual
old law rho equal to the product of the two uniform pure-survivor bases.
Retain complete old heights 9 and 1. The current 7-coordinate is full
Haar and its actual threshold is fixed at 1/14.

There are seven current-ending original labels. The core consists of

    x_3=1 modulo 3,  x_5=1 modulo 5,  z_7=0 modulo 7.

For each a=4,...,9 add the label

    x_3=1 modulo 3^a,  x_5=1 modulo 5,
    z_7=a-3 modulo 7.

The original numerical (residue,modulus) pairs, including the old pure
classes, are

    (0,3), (0,5), (91,105), (1,2835), (2431,8505),
    (21871,25515), (32806,76545), (196831,229635),
    (590491,688905).

All moduli are pairwise distinct, odd, and greater than one. The integer
2 avoids every class, so this is not a covering counterexample.

All seven current colors are forbidden on the deepest old cylinder.
Thus the full-family geometric maximum is alpha_*=1 and its cost is
S=7/7=1. The full-family lower bound is zero. For the one-label core,

\[
 \alpha_I^*=S_I=\frac17,\qquad q_I=\frac67,\qquad T=\frac1{104}.
 \tag{FA101}
\]

Indeed the active old region {x_3=1 mod3, x_5=1 mod5} has probability
1/8; on it alpha>=1/7>delta and u=1/13. Off it u=0.

For a direct exact calculation, partition that old region by its bad
color count k. The actual joint old masses are

    m_1=1/8-1/(8*3^3),
    m_k=1/(8*3^(k+1))-1/(8*3^(k+2)),  k=2,...,6,
    m_7=1/(8*3^8).

They sum to 1/8. The retained core color is bad throughout this region,
so

\[
 \begin{aligned}
 D_I&=\frac1{13}\sum_{k=1}^7m_k\frac{k-1}{k}
     =\frac{28943}{143292240},\\
 c\sum_{i\notin I}\rho(R_i)\nu(J_i)
    &=\frac{14}{13}\frac17\frac18\sum_{a=4}^9 3^{1-a}
     =\frac7{6561}.
 \end{aligned}
 \tag{FA102}
\]

Consequently the exact and upper-payment core bounds are respectively

\[
 \begin{aligned}
 Tq_I-D_I&=\frac{1152037}{143292240}>0,\\
 Tq_I-\frac7{6561}&=\frac{17135}{2388204}>0.
 \end{aligned}
 \tag{FA103}
\]

For completeness, the actual full-coordinate pair defects are

\[
 \begin{aligned}
 e_X&=\frac{19501}{2388204},\\
 e_Y&=\frac{1152037}{143292240}.
 \end{aligned}
 \tag{FA104}
\]

The first follows from (1/13) sum_k m_k(1-k/7), since only the y_5=1
root is active. For the second, the core current color 0 has negative
marginal difference throughout the active old region, and all six
other current colors have positive aggregate difference. To check the
last sign, each nonzero color can be forbidden only on an old region of
mass at most 1/216, with k>=2. Its positive contribution is T/7=1/728,
whereas its subtraction is at most (1/13)(1/216)/2=1/5616.
Thus e_Y=(1/13) sum_k m_k(1/k-1/7), yielding (FA104). These full-coordinate
values are exact: the actual density is constant on each of the stated
complete prefix cells, including their unqueried digits.

The complete original family, incoming preparation, and current kernel
are identical for all of these comparisons. Only the auxiliary core
used in the certificate changes. The example shows a strict improvement
from a zero bound to a positive bound for the specified pair defects;
it does not change the first-hit and scalar limitations above.

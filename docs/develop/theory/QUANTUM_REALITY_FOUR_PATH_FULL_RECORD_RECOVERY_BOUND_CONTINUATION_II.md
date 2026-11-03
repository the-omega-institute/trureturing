# Four-path full-record recovery: mixed geometric comparison and local effect exclusion

## 40. All-effect geometric ordering and its selected-feedback interface

**Definition 40.1 (original objects and geometric level coordinates).**
Keep the record, normalized effects, ordinary transpose and actual shared
feedback of the [source volume](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND.md),
Definitions 1.1, 11.1 and 23.1. All section numbers 24--39 below refer to
[Continuation I](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_I.md).
The original domain is still $\mathcal K=\operatorname{Dens}_2\times U(4)$;
$\rho$ is the joint distance (39.1), with both optimizer signs and only
one common scalar feedback phase, and $f=g-\kappa\rho$.
The realizable diagonal $w=\operatorname{diag}(UU_+^\dagger)$ and all of
$A,B,P,Q,u,v$ are evaluated on that same actual $U$.

Use $\mathcal C_{34}$ exactly as in Definition 35.4, with arbitrary
normalized positive effects. Use $N_{\mathrm{geo}}$ exactly as in (38.2),
its existing scalar argument $\delta_\circ(t)$ from Theorem 37.5,
and its two selected original-pair orbits $\mathcal G_\xi$ from (39.2).
These definitions make no full-domain minimizing assertion.
Write $\epsilon(E)=1-\operatorname{Tr}(E^2)$ and $D_0=d^2-e^2$.
The fixed constants of source Definition 23.1 satisfy

$$
 h=1/\sqrt2,\qquad 2hc=c+s,\qquad D_0=4h+8s,
 \qquad \frac7{10}<h<\frac34,\quad c>\frac9{10},\quad s<\frac25.
\tag{40.1}
$$

The rational inequalities follow by squaring and using
$c^2=(1+h)/2$, $s^2=(1-h)/2$.
For a geometric feedback with $x\ge0$ write

$$
\begin{aligned}
 y&=\sqrt{1-x^2},& \delta&=2(1-x),& \tau&\in\{+1,-1\},\\
 U&=\lambda\operatorname{diag}(x+\tau iy,x-\tau iy,1,1)U_+,
       &|\lambda|&=1,\\
 A&=2(1+x),& B&=2y,& P&=\lambda u,&Q&=\lambda\tau iv,\\
 u&=2(hx+c)=d-h\delta,& v&=2hy,&
 b&=u^2-v^2-D_0.
\end{aligned}
\tag{40.2}
$$

At $y=0$ either orientation describes the same feedback.
For a positive-sign effect put

$$
 T^\dagger E^{\mathsf T}T
   =\begin{pmatrix}1-r&z\\\bar z&r\end{pmatrix},\qquad
 a=|z|,\qquad \eta=\epsilon(E)/2=r(1-r)-a^2.
\tag{40.3}
$$

Thus $0\le r\le1$, $0\le a^2\le r(1-r)$, and positivity includes
both rank-one and positive definite effects. When the positive sign
attains $\rho=2t$, (36.10) gives

$$
 t=\delta+r^2+a^2,\qquad
 a^2=t-\delta-r^2,\qquad \eta=\delta+r-t.
\tag{40.4}
$$

For the coherence phase $z=\tau ia$, the exact defect is

$$
 \Phi_t(\delta,r)
 =d^2-u^2+br-2uv\sqrt{t-\delta-r^2}.
\tag{40.5}
$$

This is a specialization of source (23.12), not an optimization over
independently chosen amplitudes. Replacing an arbitrary $z$ by
$\tau i|z|$ at this same feedback cannot increase $g$ and preserves
positivity, impurity and both original sign distances. If $v=0$,
all coherence phases have the same value.

**Theorem 40.2 (all-effect comparison in the enlarged geometric shape).**
For every original $(E,U)\in\mathcal C_{34}$ with
$0<\rho(E,U)=\xi\le4$, there is an original rank-one pair
$(\widehat E,\widehat U)\in\mathcal C_{34}$ such that

$$
 \rho(\widehat E,\widehat U)=\xi,\qquad
 f(E,U)\ge f(\widehat E,\widehat U)
                       +\frac{49}{180}\epsilon(E).
\tag{40.6}
$$

The comparison feedback $\widehat U$ is allowed to differ from $U$.
Consequently, at every such original level,

$$
\begin{aligned}
 \min_{\substack{(E,U)\in\mathcal C_{34}\\\rho(E,U)=\xi}}f(E,U)
     &=N_{\mathrm{geo}}(\xi),\\
 f(E,U)&\ge N_{\mathrm{geo}}(\xi)+\frac{49}{180}\epsilon(E).
\end{aligned}
\tag{40.7}
$$

The complete preimage of equality $f(E,U)=N_{\mathrm{geo}}(\xi)$
in this all-effect comparison is exactly $\mathcal G_\xi$.
It consists of the existing two selected pure orientations, with
all their actual common-scalar representatives and no other pairs.

*Proof.* First account for the original signs before choosing a path.
For an arbitrary geometric feedback, $A=2(1+x)$ and $B=2|y|$.
If $x<0$, both feedback-distance terms exceed four:
$8-2A=4-4x>4$ and $8-2B=8-4|y|>4$.
The corresponding effect-distance terms are nonnegative, so such a
feedback cannot occur at the stated levels, even with a mixed effect.
Thus $x\ge0$. A negative minimizing sign at $\rho\le4$ requires
$8-4|y|\le4$, hence $x=0$, $|y|=1$ and $\rho=4$;
its effect-distance term must vanish, so $E=E_-$.
This is an already pure pair. At $x=0$ the positive branch likewise
has level at most four only for $E=E_+$, also pure.
In particular every mixed case has $x>0$ and the positive sign is
unique, since its negative feedback-distance term alone exceeds four.
For an already pure input take $(\widehat E,\widehat U)=(E,U)$
in (40.6). Theorem 37.5 applies to its later comparison with $N_{\mathrm{geo}}$,
including the negative-sign exception just identified.

It remains to prove (40.6) for mixed inputs. Align the coherence as
in (40.3)--(40.5), keeping the original feedback for this first step.
This does not increase $f$, and $\eta>0$ is unchanged. The following
two estimates cover every remaining geometric feedback.
First, substitution of (40.1) gives

$$
\begin{aligned}
 b(x)&=4x^2+8hcx-2h-8s,\\
 b(2/3)&=\frac{16}{9}+\frac83c-\frac{16}{3}s-2h
       >\frac{16}{9}+\frac{12}{5}-\frac{32}{15}-\frac32
        =\frac{49}{90}.
\end{aligned}
\tag{40.8}
$$

The function $b(x)$ is strictly increasing for $x\ge0$.
If $x\ge2/3$, apply (36.20) to the actual positive branch,
with its population $r$ and its pure endpoint $t-\delta$.
The resulting rank-one effect uses this unchanged $U$, has the same
original distance and decreases $g$ by at least
$b(x)\eta\ge(49/90)\eta$.
This proves (40.6) in this sector, including $x=1$, where $v=0$;
no phase division is required there.

Second, suppose $0<x<2/3$. Regard $t,r$ as fixed and decrease
$\delta$, so $x=1-\delta/2$ increases, until

$$
 \delta_f=\max\{2/3,t-r\}.
\tag{40.9}
$$

The starting $\delta_i$ is greater than both $2/3$ and $t-r$.
For every $\delta\in[\delta_f,\delta_i]$ use the single actual
unitary in (40.2) and the single effect

$$
 E_\delta=
 \left[T\begin{pmatrix}
 1-r&\tau i\sqrt{t-\delta-r^2}\\
 -\tau i\sqrt{t-\delta-r^2}&r
 \end{pmatrix}T^\dagger\right]^{\mathsf T}.
\tag{40.10}
$$

Here $r$ is the original fixed population. As $\delta$ decreases,
$a^2=t-\delta-r^2$ increases from its nonnegative initial value,
and its upper bound $a^2\le r(1-r)$ is exactly $\delta\ge t-r$.
Thus (40.10) remains positive with trace one and ends either at purity
or at $x=2/3$. Its positive branch remains exactly $2t$ by (40.4).
Throughout this path $x>0$ and $y<1$, so the negative feedback-distance
term is $8-4y>4\ge2t$. Hence the preserved distance is the original
joint minimum, not merely one chosen branch.
The phase $\lambda$ and orientation $\tau$ may be kept fixed along
this entire path.

For $a>0$, differentiation of the exact expression (40.5) gives

$$
 \partial_\delta\Phi_t
 =2hu(1-r)-2xr+2hva
          +2hu\left(\frac ya-\frac{xa}{y}\right).
\tag{40.11}
$$

Indeed $u_\delta=-h$, $v_\delta=hx/y$ and $a_\delta=-1/(2a)$.
On the present segment $x\le2/3$, $y^2\ge5/9$ and $a\le1/2$.
Consequently

$$
 \frac ya-\frac{xa}{y}
 =\frac{y^2-xa^2}{ya}
 \ge\frac{5/9-1/6}{1/2}=\frac79.
\tag{40.12}
$$

The first and third terms of (40.11) are nonnegative,
$2xr\le4/3$, and $2hu\ge4hc>63/25$ by (40.1).
It follows that

$$
 \partial_\delta\Phi_t
   >-\frac43+\frac{63}{25}\frac79=\frac{47}{75}.
\tag{40.13}
$$

If the initial coherence is zero, it is positive at every interior
point of this decreasing-$\delta$ path. Apply the derivative estimate
on closed subsegments with positive coherence and pass to the initial
endpoint using continuity of (40.5). This gives, also in that case,

$$
 \Phi_t(\delta_i,r)-\Phi_t(\delta_f,r)
       \ge\frac{47}{75}(\delta_i-\delta_f).
\tag{40.14}
$$

If $\delta_f=t-r$, the final effect is already pure.
Otherwise $\delta_f=2/3$ and its remaining half-impurity is
$\eta_f=\delta_f+r-t\ge0$.
Apply the same-feedback construction of (36.20) at this actual endpoint
feedback. By (40.8) it decreases $g$ by at least $(49/90)\eta_f$
and yields a rank-one pair at the same original distance.
Because $\eta_i-\eta_f=\delta_i-\delta_f$ and
$47/75>49/90$, the total decrease is at least
$(49/90)\eta_i=(49/180)\epsilon(E)$.
Every intermediate pair and the final pair are realized by the explicit
unitaries and ordinary-transpose effects above. Since the original
level is unchanged, subtracting $\kappa\xi$ preserves the entire
comparison. This proves (40.6).

Apply Theorem 37.5 to the final rank-one pair to obtain (40.7).
Its selected pairs themselves are admissible original all-effect
competitors, so they attain the asserted minimum. Equality at
$N_{\mathrm{geo}}$ forces $\epsilon(E)=0$ by (40.7);
Theorem 37.5 then supplies exactly $\mathcal G_\xi$ and its converse.
In particular its strict comparison against the negative-sign pair
at level four remains applicable. All zero-coherence and population
endpoints have either been handled directly or reduced to that
rank-one equality theorem. No mixed equality case or alternative
actual lift is introduced. $\square$

**Theorem 40.3 (actual selected-feedback endpoint, value and strict arc margin).**
Fix $0<\xi\le4$, let $t=\xi/2$, $\delta=\delta_\circ(t)$,
$k=t-\delta$, $x=1-\delta/2$, $y=\sqrt{1-x^2}$,
and take either selected feedback in $\mathcal G_\xi$.
Evaluate all amplitudes on that actual feedback as in (40.2).
In Definition 36.1 one then has

$$
 0<k=t_+<1,\qquad k<J_+,\qquad uv>0,\qquad t_-<0.
\tag{40.15}
$$

Thus only the positive original sign is admissible. The right derivative
of its exact effect arc at the pure endpoint is

$$
 \chi(\xi)=b+2uv\sqrt{\frac{k}{1-k}}>\frac{49}{90}.
\tag{40.16}
$$

The actual fixed-feedback profile has the endpoint and value

$$
 q_+^\sharp=k,\qquad
 M_+(w,\xi)=N_{\mathrm{geo}}(\xi)+\kappa\xi,\qquad
 M_-(w,\xi)=+\infty.
\tag{40.17}
$$

Its unique minimizing original effect is the selected one at that
feedback. More quantitatively every original effect at this same
$U$ and original level satisfies

$$
 g(E,U)\ge N_{\mathrm{geo}}(\xi)+\kappa\xi
                         +\frac{\chi(\xi)}2\epsilon(E).
\tag{40.18}
$$

Equality to $N_{\mathrm{geo}}(\xi)+\kappa\xi$ holds exactly for
that selected effect, with its ordinary-transpose convention.

*Proof.* Theorem 37.5 gives $0<\delta<2$ and $0<k<1$;
hence $x,y,u,v>0$. At its attained scalar pair, the strict original
sign comparison (37.23) gives $k<J_+$.
The trace $B=2y<2$ and $\xi\le4$ give
$t_-=(\xi-8+4y)/2<0$. This proves (40.15), including the original
negative-sign exclusion rather than an independent sign selection.

The pure-endpoint value of the positive effect arc is the value of
the actual aligned pair in Theorem 37.5, namely
$N_{\mathrm{geo}}(\xi)+\kappa\xi$.
It remains to show that this endpoint minimizes the full mixed arc.
If $x\ge2/3$, (40.8) and $uv,k>0$ give
$\chi>b>49/90$ directly.
If $x<2/3$, use the interior scalar stationarity from Theorem 37.5.
At fixed $t$, its scalar function is
$\Phi_t(\delta,t-\delta)-2\kappa t$.
At the selected argument its derivative vanishes, so

$$
 0=\partial_\delta\Phi_t-\partial_r\Phi_t,
 \qquad
 \partial_r\Phi_t\big|_{r=k}
    =b+\frac{2uvk}{\sqrt{k-k^2}}=\chi(\xi).
\tag{40.19}
$$

All derivatives are at positive $y$ and positive
$a=\sqrt{k(1-k)}$. The estimate (40.13), which uses only the
feasible scalar coordinates, applies there. Therefore
$\chi>47/75>49/90$. This proves (40.16) at every selected level,
without assuming that the selected pair is a full-domain minimizer.

By (36.15) the positive effect arc is strictly convex up to its
possible zero-coherence upper endpoint, and its right derivative at
$k$ is $\chi>0$. For every feasible population $q\ge k$ its value
is at least its endpoint value plus $\chi(q-k)$.
Continuity includes $q=\sqrt k$ if this is the upper endpoint.
Equation (36.13) gives $2(q-k)=\epsilon(E)$, and phase misalignment
can only increase $g$. This proves (40.18), and also proves that
the complete arc minimum is attained only at $q=k$ with aligned phase.
Thus (40.17) concerns the actual profile $M_+$, not just a candidate
endpoint value. Since $u,v,k,1-k$ are positive, alignment fixes
$z=\tau i\sqrt{k(1-k)}$ uniquely. Returning by
$E=(TFT^\dagger)^{\mathsf T}$ gives exactly the selected effect.

Every entry of the selected diagonal has modulus one. For any
actual unitary lift $V=UU_+^\dagger$ with that diagonal, the full
squared norm of each row is already supplied by its diagonal entry.
All off-diagonal entries vanish. Hence there are no extra
nondiagonal lifts at these equality feedbacks, while every common
scalar representative has been retained. $\square$

**Theorem 40.4 (relative neighborhoods and exclusion of mixed minimizing coalescence).**
Give $\mathscr D=(0,4]\times U(4)$ the relative product topology
from the real level coordinate and the matrix Frobenius norm.
For $(\xi,U)\in\mathscr D$ compute the original data on
$w=\operatorname{diag}(UU_+^\dagger)$ and set

$$
 k=t_+(w,\xi),\qquad
 D(w,\xi)=b_+(w)+2u(w)v(w)\sqrt{\frac{k}{1-k}}
 \quad (0<k<1).
\tag{40.20}
$$

The set

$$
 \Omega=\left\{(\xi,U)\in\mathscr D:
 \begin{array}{c}
 uv>0,\quad 0<k<1,\quad k<J_+,\\
 t_-<0,\quad D(w,\xi)>49/180
 \end{array}\right\}
\tag{40.21}
$$

is relatively open, invariant under $U\mapsto\lambda U$, and
contains all selected feedbacks over $(0,4]$.
For every $(\xi,U)\in\Omega$ there is a unique fixed-feedback
minimizing effect $\widehat E$ at original level $\xi$.
It has rank one and is given by

$$
 \widehat E=
 \left[T\begin{pmatrix}
 1-k&\sqrt{k(1-k)}\,\bar P Q/(uv)\\
 \sqrt{k(1-k)}\,P\bar Q/(uv)&k
 \end{pmatrix}T^\dagger\right]^{\mathsf T}.
\tag{40.22}
$$

For every original effect $E$ at that same $U$ and level,

$$
 \rho(\widehat E,U)=\rho(E,U)=\xi,\qquad
 f(E,U)\ge f(\widehat E,U)+\frac{49}{360}\epsilon(E).
\tag{40.23}
$$

This includes all actual nondiagonal feedbacks in $\Omega$.
For each nonempty compact $K\subset(0,4]$, write
$\mathscr U_\xi=\{U:(E,U)\in\mathcal G_\xi\}$.
There is $r_K>0$ such that, uniformly for $\xi\in K$,

$$
 \operatorname{dist}_{\mathrm F}(U,\mathscr U_\xi)<r_K
       \quad\Longrightarrow\quad (\xi,U)\in\Omega.
\tag{40.24}
$$

Both the radius and the minimizing effect refer to actual matrices;
the distance is to the full common-scalar orbits.
The coefficient $49/360$ in (40.23) is independent of $K$.

In particular, suppose $\xi_n\in(0,4]$ tends to
$\xi_0\in(0,4]$, $\operatorname{dist}_{\mathrm F}(U_n,\mathscr U_{\xi_n})\to0$,
and each $E_n$ minimizes its original fixed-$U_n$ level problem.
Then $E_n$ has rank one for all sufficiently large $n$.
The same conclusion holds for full-domain global minimizers.
Thus a mixed minimizing branch cannot coalesce with a selected
geometric pair at a positive level in this relative range.

*Proof.* The diagonal map from the actual unitary group is continuous,
as are $A,B,u,v,b_\pm,t_\pm,J_\pm$. On $0<k<1$ the expression
$D$ is continuous. All inequalities in (40.21) are strict, proving
relative openness. They are common-phase invariant, as are
$\bar P Q/(uv)$ and the selected feedback orbits.
Theorems 37.5 and 40.3 give (40.15) and $D>49/90$ at every
selected feedback. Hence this entire graph lies in $\Omega$.

For an actual $U$ in $\Omega$, $t_-<0$ excludes the negative
sign at the prescribed level for every effect.
The conditions $0<k<1$ and $k<J_+$ make the positive arc nonempty
and put its pure endpoint strictly below both possible upper endpoints.
The phase-aligned effect (40.22) is positive with trace one and
determinant zero. Its positive distance is exactly $\xi$, and its
positive sign is strictly minimizing because $k<J_+$.
Every other effect at that original level is on this same positive
arc, with population $q\ge k$ and impurity $2(q-k)$.
Convexity (36.15), including the upper endpoint by continuity, gives

$$
 g(E,U)-g(\widehat E,U)
      \ge D(w,\xi)(q-k)
      \ge\frac{49}{360}\epsilon(E).
\tag{40.25}
$$

When $q>k$ the inequality before the fixed constant is strictly
positive. When $q=k$, $uv>0$ and $k(1-k)>0$ give a unique
aligning phase. This proves uniqueness, (40.23), and the actual
same-feedback realization. The calculation used only data of the
specified $U$, so it applies to every actual lift without imposing
any diagonal-feedback restriction.

The continuity of the scalar selector and the Hausdorff continuity
of $\mathcal G_\xi$ are supplied by Theorem 39.2.
Consequently the selected feedback graph over compact $K$ is compact
in $K\times U(4)$ and lies inside the relatively open $\Omega$.
A positive product-metric neighborhood of that compact graph lies
inside $\Omega\cap(K\times U(4))$. At a fixed level this proves
(40.24); since each feedback orbit is compact, the distance used
there is attained. It is invariant under the single scalar action.
For the sequence in the statement choose one compact positive-level
interval containing its tail. Equation (40.24) puts its tail in
$\Omega$, where a mixed effect has a strictly better same-feedback
competitor by (40.23). This contradicts either fixed-feedback or
full-domain minimality, proving eventual purity. $\square$

The neighborhood assertion at $\xi=4$ is relative to $\xi\le4$;
it asserts no exclusion for levels above four. Zero is excluded:
no positive neighborhood radius uniform down to $\xi=0$ is asserted.
At boundaries where $uv=0$, $k\in\{0,1\}$, $k=J_+$,
$t_-=0$ or the derivative margin fails, Theorem 40.4 gives no
conclusion; the complete degenerate profile remains (36.5)--(36.7).
Away from selected feedbacks the value at (40.22) is not asserted
to equal or exceed $N_{\mathrm{geo}}(\xi)+\kappa\xi$.
Pure nongeometric minimizing branches may coalesce, and mixed
branches separated from the selected graph are not excluded.

**Proposition 40.5 (a fixed-feedback mixed counterexample at distance $25/8$).**
Set

$$
\begin{aligned}
 w_0&=\left(\frac{1+i\sqrt{15}}4,
             \frac{1-i\sqrt{15}}4,1,1\right),&
 U_0&=\operatorname{diag}(w_0)U_+,\\
 F_{\mathrm p}&=\begin{pmatrix}
 15/16&i\sqrt{15}/16\\-i\sqrt{15}/16&1/16
 \end{pmatrix},&
 F_{\mathrm m}&=\begin{pmatrix}
 7/8&i\sqrt3/8\\-i\sqrt3/8&1/8
 \end{pmatrix},\\
 E_j&=(TF_jT^\dagger)^{\mathsf T},& j&\in\{\mathrm p,\mathrm m\}.
\end{aligned}
\tag{40.26}
$$

These are actual original pairs with
$\rho(E_{\mathrm p},U_0)=\rho(E_{\mathrm m},U_0)=25/8$.
The effect $E_{\mathrm p}$ has rank one and $E_{\mathrm m}$ is
positive definite. Every rank-one original effect $E$ at this same
$U_0$ and original level satisfies

$$
 f(E_{\mathrm m},U_0)
    < f(E_{\mathrm p},U_0)-\frac7{640}
    \le f(E,U_0)-\frac7{640}.
\tag{40.27}
$$

Thus universal prescribed-level purification at unchanged actual
feedback fails, even inside $\mathcal C_{34}$.
This statement concerns one fixed feedback and one level; it asserts
no mixed optimality for the all-feedback geometric or full-domain problem.

*Proof.* Every entry of $w_0$ has modulus one, so $U_0$ is an
actual unitary, of geometric shape $x=1/4$, $y=\sqrt{15}/4$.
The matrices in (40.26) are Hermitian with trace one and positive
diagonal entries. Their determinants are respectively zero and
$1/16$, proving the stated positivity and ranks after the prescribed
unitary conjugation and ordinary transpose.
The actual common data are

$$
 A=5/2,\quad B=\sqrt{15}/2,\quad
 P=u=2c+h/2,\quad Q=iv,\quad v=h\sqrt{15}/2.
\tag{40.28}
$$

For both effects the positive-branch coordinates satisfy
$r^2+|z|^2=1/16$:
these are $1/256+15/256$ for $F_{\mathrm p}$ and
$1/64+3/64$ for $F_{\mathrm m}$.
Equation (36.10) gives the positive distance $3+2/16=25/8$.
For every effect the negative feedback-distance term alone is
$8-\sqrt{15}>4$, so the positive sign is unique for both displayed
pairs and for every other effect on this fixed-feedback level.
No negative-sign pure competitor has been omitted.

At this level a pure effect must have
$r=r^2+|z|^2=1/16$ by positivity with determinant zero.
Its best possible coherence phase is $z=i\sqrt{15}/16$,
since the actual $P$ is positive and $Q$ is positive imaginary.
Thus $E_{\mathrm p}$ minimizes over every pure effect at this same
feedback and original level, not just over one chosen orientation.
For the two aligned effects the exact identity (23.12) gives

$$
\begin{aligned}
 b&=u^2-v^2-D_0=\frac14+c-7s-2h,\\
 16\bigl[g(E_{\mathrm m},U_0)-g(E_{\mathrm p},U_0)\bigr]
   &=b+(c+s+1/4)(15-6\sqrt5).
\end{aligned}
\tag{40.29}
$$

For completeness, $s>3/8$ follows from
$\sqrt2<10/7$ and $s^2=(2-\sqrt2)/4>1/7>9/64$.
Also $c<1$, $2h>7/5$ and $0<15-6\sqrt5<8/5$;
the last bounds follow by squaring the positive rational comparisons
$\sqrt5<5/2$ and $\sqrt5>67/30$.
Since $c+s+1/4>0$, the last line of (40.29) is strictly smaller than

$$
 \frac{13}{5}c-\frac{27}{5}s+\frac{13}{20}-2h
 <\frac{13}{5}-\frac{81}{40}+\frac{13}{20}-\frac75
 =-\frac7{40}.
\tag{40.30}
$$

This proves (40.27) for $g$ and hence for $f$, since all compared
objects have the identical original distance.
All amplitudes, both sign tests and both effects have used the one
actual $U_0$. Theorem 40.2 can nevertheless improve this mixed pair
by a pure pair with a changed geometric feedback; (40.27) does not
compare such different feedbacks. $\square$

**Mathematical source correspondence 40.6.** The mixed comparison uses
the original same-object identities (23.9)--(23.12), the exact
prescribed-level arcs and their equality preimage in Theorem 36.2,
and the conditional same-feedback construction (36.20).
Its final scalar ordering and pure equality classification are
Theorem 37.5; neither the cap profiles nor the scalar selector is
replaced. The selected-feedback identity (40.17) additionally uses
scalar stationarity to control the actual mixed effect arc, as shown
in (40.19). These are fixed-record, joint-distance deductions.

For the primary-literature correspondence,
Gregoratti--Werner, [*Quantum Lost and Found*, quant-ph/0209025v1,
Proposition 8 and (16)--(21)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8),
optimize correction fidelity for a fixed Kraus decomposition.
Their intermediate operator is $t_j=\operatorname{diag}(R_0b_j)$
here, in input dimension four. Their correction bound and equality
form do not impose this producer's joint distance, compare its
feedbacks at a prescribed level, or imply same-feedback purification.
Buscemi--Chiribella--D'Ariano,
[*Inverting Quantum Decoherence by Classical Feedback from the Environment*,
quant-ph/0504195v5, (6) and (9)](https://arxiv.org/html/quant-ph/0504195v5),
supply the four-dimensional rank-two correlation example:
their Heisenberg matrix is $\overline{R_0R_0^\dagger}$,
consistent with their Schrödinger transpose.
This correspondence does not change the ordinary transpose of the
effects in the present model.

Thompson's prescribed complex-diagonal and singular-value theorem,
in the formulation of Jasper--Loreaux--Weiss,
[*Thompson's theorem for compact operators and diagonals of unitary operators*,
arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3),
gives exactly $\mathcal W$ when all four singular values are one,
as applied in source Theorem 23.2. It supplies realizability, not
any prescribed-level ordering. The paths and diagnostic in this
section instead have the direct actual unitary realizations displayed
above. None of these general literature inputs states the geometric
mixed comparison or the selected-feedback endpoint/value identity.

**Unresolved mathematical obligations 40.7.** Theorem 40.2 removes
mixed competitors inside $\mathcal C_{34}$ at $0<\xi\le4$ from
the full comparison problem. Theorem 40.4 excludes only mixed
minimizing branches that approach the selected feedback graph in its
specified relative range. At either $b=\alpha$ or $b=\beta$,
if $\mathcal A_b=\mathcal G_b$, Theorem 39.6 and Theorem 40.4
imply that all global minimizers on sufficiently nearby levels are
pure. This does not exclude coalescing pure competing branches.
If there are additional endpoint minimizers, separated mixed limits
are not excluded by that argument.

The outstanding original comparison is still

$$
 M_\sigma(w,\xi)\ge N_{\mathrm{geo}}(\xi)+\kappa\xi
\tag{40.31}
$$

for every realizable $w\in\mathcal W$ and every admissible original
sign on the required preceding levels, together with its complete
attained equality preimage in actual $\operatorname{Dens}_2\times U(4)$.
Every mixed arc, singular endpoint, zero amplitude, sign tie and
actual unitary lift outside the proved neighborhood remains subject
to that comparison. The geometric comparison beyond level four is
also not established here. Sections 38--39 already give strict
full-domain competitors below the selected geometric value at
positive levels below four; (40.31) cannot hold through that entire
range. No all-$\mathcal W$ certificate is asserted.

The exact evaluation of $\alpha$ and $\beta$, their possible
coincidence, the full equality sets at both boundaries, the inclusion
or exclusion of the exhaustive-equality endpoint, the identities
and exhaustion of the first competing actual branches, and the
required right-side behavior beyond their existing conditional
conclusions remain unresolved. The determinant-zero case of the
phase variation still needs its higher-order and global comparison.
An effect-arc margin, a local purity neighborhood, a scalar threshold,
an unattained core-infimum tie or a strict failure window is not a
selected first-loss boundary. The full original first-loss goal is
unchanged.

## 追加锚（本行以下为增补区）

## 41. Increasing selected defect and global mixed-contact consequences

**Definition 41.1 (selected raw value and original sign distances).**
Retain the original domain $\mathcal K=\operatorname{Dens}_2\times U(4)$,
ordinary transpose, certificate basis $T$, constants $h,c,s,d,e,\kappa$,
and actual shared feedback of Definition 40.1. All references to
Sections 23 and 24--39 have the source-volume conventions stated there.
For $0<\xi\le4$ put

$$
 V(\xi)=N_{\mathrm{geo}}(\xi)+\kappa\xi.
\tag{41.1}
$$

Here $N_{\mathrm{geo}}$, its argument $\delta_\circ(\xi/2)$ and
$\mathcal G_\xi$ are exactly (38.2), Theorem 37.5 and (39.2).
Thus $V(\xi)$ is the actual $g$-value attained by every pair in
$\mathcal G_\xi$. Its definition makes no assertion of unrestricted
geometric optimality. Keep $\mathcal A_\xi$, $\mathcal B$, $\mathcal S$,
$\alpha$ and $\beta$ exactly as in Definition 39.1; in particular
$0<\alpha\le\beta<18/5$ is Theorem 39.4.

For an arbitrary original pair write

$$
\begin{aligned}
 w&=\operatorname{diag}(UU_+^\dagger),&
 F&=T^\dagger E^{\mathsf T}T
       =\begin{pmatrix}p&z\\\bar z&1-p\end{pmatrix},\\
 \epsilon&=\epsilon(E)=1-\operatorname{Tr}(E^2)
       =2\bigl(p(1-p)-|z|^2\bigr),\\
 \rho_\sigma(E,U)
   &=\|E-E_\sigma\|_{\mathrm F}^2
           +\min_{|\lambda|=1}\|U-\lambda U_\sigma\|_{\mathrm F}^2.
\end{aligned}
\tag{41.2}
$$

The scalar $\lambda$ multiplies the entire feedback matrix.
The original distance is $\rho=\min\{\rho_+,\rho_-\}$.
The identities (23.9)--(23.12) give, on these same actual data,

$$
\begin{aligned}
 \rho_+(E,U)&=10-2p-2A(w)-\epsilon,\\
 \rho_-(E,U)&=8+2p-2B(w)-\epsilon,\\
 g(E,U)&=d^2p+e^2(1-p)-pu^2-(1-p)v^2
                          -2\operatorname{Re}(Pz\bar Q).
\end{aligned}
\tag{41.3}
$$

All of $A,B,P,Q,u,v$ in this section are evaluated on that one $w$.
An effect is mixed precisely when $\epsilon>0$; for a normalized
positive two-by-two effect this is equivalent to positive definiteness.

**Theorem 41.2 (strict increase of the attained selected raw defect).**
The function $V$ is continuously differentiable on $(0,4)$,
continuous on $(0,4]$, and has a finite positive left derivative at four.
At its existing selected coordinates

$$
\begin{aligned}
 t&=\xi/2,& \delta&=\delta_\circ(t),&q&=t-\delta,&p&=1-q,\\
 x&=1-\delta/2,&y&=\sqrt{1-x^2},&
 u&=2(hx+c),&v&=2hy,\\
 S&=u\sqrt p+v\sqrt q,
\end{aligned}
$$

one has

$$
 q<y^2,\qquad
 V'(\xi)=hS\left(\sqrt p-\frac{x\sqrt q}{y}\right)>0.
\tag{41.4}
$$

At $\xi=4$ the derivative in (41.4) means the left derivative.
Consequently $V$ is strictly increasing throughout $0<\xi\le4$.

*Proof.* For independent variables $0<\delta<2$, $0<q<1$ define
$x=1-\delta/2$, $y=\sqrt{1-x^2}$, $u=2(hx+c)$, $v=2hy$ and

$$
 L(\delta,q)
   =d^2(1-q)+e^2q-
       \bigl(u\sqrt{1-q}+v\sqrt q\bigr)^2,
 \qquad \mathcal H(t,\delta)=L(\delta,t-\delta).
\tag{41.5}
$$

These functions are smooth on the indicated open domain and its
corresponding open domain in $(t,\delta)$.
Theorem 37.5 supplies the unique interior minimum on
$J(t)=[\max\{0,t-1\},t]$, for $0<t\le2$.
Subtracting $2\kappa t$ from $\mathcal H$ gives exactly the scalar
objective of that theorem, so its argument remains $\delta_\circ(t)$.
The actual selected value is therefore

$$
 W(t):=V(2t)=\mathcal H(t,\delta_\circ(t)).
\tag{41.6}
$$

In particular the selected $\delta,q,x,y,u,v,p$ are all strictly
positive, and $\delta<2$, $q<1$. No zero population or zero amplitude
is differentiated in this proof.

We justify differentiation of this attained value without assuming
differentiability of the selector. Its continuity, and continuity of
$V$ through four, are supplied by Theorem 39.2.
Fix $t_0\in(0,2]$, put $\delta_0=\delta_\circ(t_0)$, and restrict
to $t$ sufficiently near $t_0$ in $(0,2]$.
Interiority and continuity ensure that $\delta_0\in J(t)$ and
$\delta_\circ(t)\in J(t_0)$, and that both points lie in one open
neighborhood on which (41.5) is smooth. Minimality at the two levels gives

$$
\begin{aligned}
 \mathcal H(t,\delta_\circ(t))
       -\mathcal H(t_0,\delta_\circ(t))
 &\le W(t)-W(t_0)\\
 &\le\mathcal H(t,\delta_0)-\mathcal H(t_0,\delta_0).
\end{aligned}
\tag{41.7}
$$

After division by $t-t_0$, both outer difference quotients tend to
$\partial_t\mathcal H(t_0,\delta_0)$, by continuity of the selector
and of that partial derivative. For $t<t_0$ both inequality directions
reverse, giving the same limit. It follows that
$W'(t)=L_q(\delta_\circ(t),t-\delta_\circ(t))$ in the interior,
with the analogous left derivative at $t=2$.
This expression is continuous in $t$. The interior scalar stationarity
also gives $L_\delta=L_q$ at every selected point.

Writing $D_0=d^2-e^2$ and $S=u\sqrt{1-q}+v\sqrt q$, direct
differentiation of (41.5), with the other variable held fixed, yields

$$
\begin{aligned}
 L_\delta
   &=2hS\left(\sqrt{1-q}-\frac{x\sqrt q}{y}\right),\\
 L_q&=u^2-v^2-D_0
             +uv\frac{2q-1}{\sqrt{q(1-q)}},\\
 L_{qq}&=\frac{uv}{2[q(1-q)]^{3/2}}>0.
\end{aligned}
\tag{41.8}
$$

For each fixed selected $\delta$, evaluate the second line at $q=y^2$.
Since $\sqrt{1-y^2}=x>0$, substitution gives

$$
 L_q(\delta,y^2)
    =4c^2+\frac{4hc}{x}-D_0
    \ge4c^2+4hc-D_0
    =4s(h+s-1)>0.
\tag{41.9}
$$

Here the last identity uses $D_0=4h+8s$, $c^2=(1+h)/2$ and
$c=(1+2h)s$. The latter follows from $2hc=c+s$ and $h^2=1/2$.
For the strict sign, $1/2<h<1$ and $s^2=(1-h)/2$ give

$$
 s^2-(1-h)^2=(1-h)(h-1/2)>0.
$$

Both $s$ and $1-h$ are positive; hence $s>1-h$, proving (41.9).

If a selected point had $q\ge y^2$, the last line of (41.8) and
(41.9) would give $L_q>0$. On the other hand
$q\ge y^2$ is equivalent to
$\sqrt{1-q}\le x\sqrt q/y$, so $L_\delta\le0$.
This contradicts the selected stationarity $L_\delta=L_q$.
Thus $q<y^2$, and the first line of (41.8) is strictly positive.
Combining $V'(\xi)=W'(\xi/2)/2=L_q/2=L_\delta/2$ proves
(41.4), including its continuous left limit at four.
The mean value theorem on any $[a,b]\subset(0,4]$ now proves
$V(b)>V(a)$ whenever $a<b$. This calculation uses the attained
selected scalar minimum only. $\square$

**Theorem 41.3 (exact constant-defect motion at unchanged actual feedback).**
For every original $(E,U)\in\mathcal K$ there is a continuous family
$E_\theta\in\operatorname{Dens}_2$, $0\le\theta\le\epsilon(E)$,
starting at $E_0=E$, such that the actual matrix $U$ and the
certificate-basis population $p$ remain unchanged and

$$
\begin{aligned}
 g(E_\theta,U)&=g(E,U),&
 \epsilon(E_\theta)&=\epsilon(E)-\theta,\\
 \rho_\sigma(E_\theta,U)&=\rho_\sigma(E,U)+\theta
                                      &&(\sigma=+,-),\\
 \rho(E_\theta,U)&=\rho(E,U)+\theta.
\end{aligned}
\tag{41.10}
$$

Every original minimizing sign, including a tie, is preserved.
If $\epsilon(E)>0$, then $E_\theta$ is positive definite for
$0\le\theta<\epsilon(E)$ and has rank one at $\theta=\epsilon(E)$.
For $\epsilon(E)=0$ the family consists of its original single point.

*Proof.* Use the actual coordinates (41.2) and set $C=P\bar Q$.
Choose a unit complex number $\zeta$ such that

$$
 \operatorname{Re}(C\zeta)=0,\qquad
 a_0:=\operatorname{Re}(z\bar\zeta)\ge0.
\tag{41.11}
$$

If $C\ne0$, the two choices $\pm i\bar C/|C|$ satisfy the first
condition; one of them satisfies the second. If $C=0$, start with
any unit direction and choose its sign to satisfy the second condition.
When $a_0=0$ either sign is allowed. For $0\le\theta\le\epsilon$
put

$$
\begin{aligned}
 \nu_\theta&=\sqrt{a_0^2+\theta/2}-a_0,&
 z_\theta&=z+\nu_\theta\zeta,\\
 F_\theta&=\begin{pmatrix}p&z_\theta\\\bar z_\theta&1-p\end{pmatrix},&
 E_\theta&=(TF_\theta T^\dagger)^{\mathsf T}.
\end{aligned}
\tag{41.12}
$$

The square root is nonnegative and $a_0\ge0$, so $\nu_0=0$.
Thus this family is continuous and begins at exactly the input effect,
with no preliminary phase alignment. Its two relevant identities are

$$
\begin{aligned}
 |z_\theta|^2
   &=|z|^2+2a_0\nu_\theta+\nu_\theta^2
     =|z|^2+\theta/2,\\
 \operatorname{Re}(Cz_\theta)&=\operatorname{Re}(Cz),\\
 \det F_\theta
   &=p(1-p)-|z_\theta|^2=(\epsilon-\theta)/2\ge0.
\end{aligned}
\tag{41.13}
$$

The diagonal entries of $F_\theta$ are nonnegative and its trace is one.
Together with the determinant inequality this proves positivity.
Unitary conjugation and ordinary transpose preserve positivity, trace,
eigenvalues and $\operatorname{Tr}(E^2)$; hence
$E_\theta$ is an original normalized effect with impurity
$\epsilon-\theta$. Formula (41.3), including its actual coherence
term, gives exactly constant $g$. The same formula for each sign
distance gives the identical increment $\theta$ for both signs.
Taking their minimum proves the last line of (41.10) and preserves
the entire minimizing-sign set. Because $U$ itself never changes,
the scalar phases minimizing its distance to each $U_\sigma$ also
remain unchanged, including the full phase circle when the trace is zero.

For $\epsilon>0$, positivity of the initial determinant forces
$0<p<1$. The determinant in (41.13) is strictly positive before the
terminal parameter and zero there. Trace one then gives exactly the
rank assertions. If $p=0$ or $p=1$, positivity initially forces
$z=0$ and $\epsilon=0$, so only the original point is used.
Every other already pure input likewise has the singleton family.
At $z=0$ one has $a_0=0$ and the formula is still continuous;
no derivative at the initial parameter is needed.
If either $P=0$ or $Q=0$, then $C=0$ and the stated arbitrary-direction
choice avoids division by that amplitude. This also covers both
amplitudes zero. No condition on $A$ or $B$ is used, so zero feedback
traces, sign ties and all population and rank boundaries are included.

All amplitudes, feedback traces and every off-diagonal entry of $U$
remain those of the original actual matrix throughout. In particular
the construction covers every nondiagonal unitary lift without a new
realization assumption. Under the single common scalar action on $U$,
$C=P\bar Q$ is invariant. The choices in (41.11) are pointwise choices
for each input pair; the theorem asserts continuity in $\theta$ for
that pair, and asserts no globally continuous selection of directions
over $\mathcal K$. It is a family in the original mathematical domain,
with no assertion of a physical control implementation. $\square$

**Theorem 41.4 (quantitative comparison on the value-preserving prefix).**
For every original pair with $0<\rho(E,U)=\xi\le\beta$, put

$$
 \theta_* =\min\{\epsilon(E),\beta-\xi\},\qquad
 \eta_* =\xi+\theta_* =\min\{\beta,\xi+\epsilon(E)\}.
\tag{41.14}
$$

Then

$$
\begin{aligned}
 g(E,U)&\ge V(\eta_*),\\
 f(E,U)&\ge N_{\mathrm{geo}}(\xi)+V(\eta_*)-V(\xi).
\end{aligned}
\tag{41.15}
$$

For every mixed effect and $0<\xi<\beta$ this is strictly stronger
than $f(E,U)\ge N_{\mathrm{geo}}(\xi)$. In particular

$$
 \mathcal A_\xi\subseteq
    \{(E,U)\in\mathcal K:\operatorname{rank}E=1\},
                      \qquad 0<\xi<\beta.
\tag{41.16}
$$

For any family in Theorem 41.3, equality in (41.15) holds exactly
when $(E_{\theta_*},U)\in\mathcal A_{\eta_*}$.

*Proof.* Theorem 39.5 supplies the existing identity
$m(\eta)=N_{\mathrm{geo}}(\eta)$ for every $0<\eta\le\beta$,
including $\eta=\beta$. Apply Theorem 41.3 at $\theta_*$.
The resulting actual pair is at the exact original level $\eta_*$
and has unchanged $g$. Therefore

$$
\begin{aligned}
 g(E,U)&=g(E_{\theta_*},U)\\
       &=f(E_{\theta_*},U)+\kappa\eta_*\\
       &\ge m(\eta_*)+\kappa\eta_*=V(\eta_*).
\end{aligned}
\tag{41.17}
$$

Subtracting $\kappa\xi$ proves the second line of (41.15).
The only inequality in (41.17) is equality precisely for a global
minimizer at $\eta_*$, proving the asserted equality criterion.
When $\xi<\beta$ and $\epsilon(E)>0$, one has $\theta_*>0$;
Theorem 41.2 gives $V(\eta_*)-V(\xi)>0$. This excludes every mixed
equality pair there, regardless of its actual feedback or minimizing sign.
Since the global value at $\xi$ is the stated geometric value,
all global minimizers there are pure, proving (41.16).

If $\epsilon=0$, the increment is zero and equality means exactly
original global minimality at $\xi$. If $\xi=\beta$, the increment
is again zero and gives no mixed exclusion at that endpoint.
For a mixed input with $\xi+\epsilon\le\beta$, the comparison point
is the pure endpoint; equality in (41.15) requires that actual pure
pair to minimize at $\xi+\epsilon$. If $\xi+\epsilon>\beta$, the
comparison point is still mixed and lies at $\beta$; equality requires
that actual mixed endpoint minimizer. These cases include
$\xi+\epsilon=\beta$ and exhaust the saturation possibilities.
None of the equality conditions identifies the remaining feedback
preimages of those global minimizing sets. $\square$

**Corollary 41.5 (actual mixed contact and the two first boundaries).**
Suppose $0<b<4$ and an actual mixed pair satisfies
$\rho(E,U)=b$ and $g(E,U)\le V(b)$.
The continuous family of Theorem 41.3 satisfies, for every
$0<\theta\le\min\{\epsilon(E),4-b\}$,

$$
\begin{aligned}
 \rho(E_\theta,U)&=b+\theta,\\
 f(E_\theta,U)-N_{\mathrm{geo}}(b+\theta)
    &=g(E,U)-V(b+\theta)\\
    &\le V(b)-V(b+\theta)<0.
\end{aligned}
\tag{41.18}
$$

At an equality contact $g(E,U)=V(b)$, the inequality before the last
strict sign is an equality. Every displayed competitor is an attained
original pair, and $E_\theta\to E$ as $\theta\downarrow0$.
The comparison includes level four when reached, and includes the pure
endpoint when $b+\epsilon(E)\le4$. It implies $\beta\le b$.

In particular a mixed pair in $\mathcal A_\alpha$ forces
$\alpha=\beta$. It is an additional endpoint minimizer and the
exhaustive-geometric-equality prefix excludes its endpoint.
If $\alpha<\beta$, every extra minimizer at $\alpha$, and every
minimizer at any level in $[\alpha,\beta)$, is pure.
A mixed pair in $\mathcal A_\beta$ also supplies (41.18), but does
not rule out an earlier pure equality tie at $\alpha<\beta$.
The produced strict right competitors need not be globally minimizing.

*Proof.* Constant $g$ and the exact original distance in (41.10)
give the equality in (41.18). Theorem 41.2 makes its final comparison
strict for every indicated positive parameter. For arbitrarily small
such parameters with $b+\theta<4$, the attained competitor implies
$m(b+\theta)<N_{\mathrm{geo}}(b+\theta)$, so
$b+\theta\in\mathcal S$. Taking their infimum gives $\beta\le b$.
This conclusion uses actual pairs, with no core-infimum attainment
assumption and no continuation of a globally minimizing branch.

At either $b=\alpha$ or $b=\beta$, Theorem 39.5 gives
$g(E,U)=V(b)$ for every pair in $\mathcal A_b$.
If a mixed one occurs at $\alpha$, the preceding result and
$\alpha\le\beta$ imply equality of the boundaries.
The sets $\mathcal G_b$ consist of pure effects, so this mixed pair
belongs to $\mathcal A_\alpha\setminus\mathcal G_\alpha$.
The endpoint alternative in Theorem 39.5 then excludes $\alpha$
from the initial exhaustive-equality prefix.
If $\alpha<\beta$, Theorem 41.4 instead forces purity throughout
$[\alpha,\beta)$. No assertion that such extra pure pairs exist at
$\alpha$ is needed; the endpoint may also have only geometric minimizers.

For a mixed minimizer at $\beta$, (41.18) establishes strict loss
immediately to its right. It supplies no restriction on an earlier
pure extra minimizer, so it supplies no general coincidence conclusion.
Theorem 40.4 does retain its separation consequence: with
$\mathscr U_\beta=\{U:(E,U)\in\mathcal G_\beta\}$ there is
$r_\beta>0$ such that every mixed pair in $\mathcal A_\beta$ satisfies

$$
 \operatorname{dist}_{\mathrm F}(U,\mathscr U_\beta)\ge r_\beta.
\tag{41.19}
$$

Indeed (40.24) with $K=\{\beta\}$ would otherwise put its feedback
in the neighborhood where (40.23) gives a strictly better same-level
effect. This uses the full actual common-scalar feedback orbits.
It neither identifies nor excludes those separated mixed endpoints.
The bounds above compare the constructed pairs with the selected value;
they do not compare them with all other original competitors at their
new levels. Thus global minimality of the right competitors is not
implied. $\square$

**Mathematical source correspondence 41.6.** The identities (41.2)--(41.3)
are the original normalized-effect, joint-distance and linear-defect
identities (23.9)--(23.12). Theorem 41.3 uses the affine sections of
their complex coherence disk while retaining its original starting
point and its actual coherence contribution to $g$.
The scalar value in Theorem 41.2 is precisely the selected attained
value of Theorem 37.5 and (38.2); selector continuity is Theorem 39.2.
The difference-quotient argument (41.7) is the elementary sensitivity
argument for an interior unique minimum. It adds no replacement scalar
selection. The local impurity comparison (34.20)--(34.22), the cap and
fixed-feedback profiles of Sections 36--37, the phase-instability
comparisons of Sections 36 and 38--39, and the geometric ordering and
selected-feedback margins of Section 40 retain their stated domains.
Theorem 41.4 consumes Theorem 39.5's already defined value-preserving
prefix; (41.19) consumes the existing local exclusion in Theorem 40.4.
The fixed-feedback, fixed-level diagnostic of Proposition 40.5 is
consistent with (41.10), whose level increases by its impurity reduction.

For the primary-literature correspondence,
Gregoratti--Werner, [*Quantum Lost and Found*, quant-ph/0209025v1,
Proposition 8 and (16)--(21)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8),
fix a Kraus decomposition while optimizing correction fidelity.
Their operators here are $t_j=\operatorname{diag}(R_0b_j)$ in input
dimension four. The correction bound and its polar equality form do
not impose the present joint distance or give its prescribed-level
ordering. In particular the columns of one original effect retain
one shared $U$ in (41.3).
Buscemi--Chiribella--D'Ariano,
[*Inverting Quantum Decoherence by Classical Feedback from the Environment*,
quant-ph/0504195v5, (6) and (9)](https://arxiv.org/html/quant-ph/0504195v5),
supply the four-dimensional rank-two correlation example. Their
Heisenberg matrix is $\overline{R_0R_0^\dagger}$; the Schrödinger
transpose in their (6) gives the source's Schur record. The ordinary
transpose on the effects remains exactly the one in source (1.4)--(1.5).

Thompson's prescribed complex-diagonal and singular-value theorem,
as stated by Jasper--Loreaux--Weiss,
[*Thompson's theorem for compact operators and diagonals of unitary operators*,
arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3),
with four singular values equal to one, gives exactly $\mathcal W$
in source Theorem 23.2. It supplies the existing feedback-realization
input. The motion (41.12) keeps an already actual $U$ and requires
no new lifting theorem. These cited theorem statements provide record,
correction and realization correspondences; they do not assert
(41.4), (41.10), the prefix increment (41.15), or the first-boundary
consequences (41.18). No exhaustive literature-absence or priority
claim is attached to these fixed-record deductions.

**Unresolved mathematical obligations 41.7.** The complete preceding-level
comparison still requires

$$
 M_\sigma(w,\xi)\ge V(\xi)
\tag{41.20}
$$

for every realizable $w\in\mathcal W$ and every admissible original
sign on the required preceding levels, with the full attained equality
preimage in actual $\operatorname{Dens}_2\times U(4)$.
Equivalently, using the exact fixed-feedback profile, every
$r\in[t_\sigma,\min\{\sqrt{t_\sigma},J_\sigma\}]$ must satisfy

$$
 \Delta_\sigma+b_\sigma r-2uv\sqrt{t_\sigma-r^2}
                       \ge V(\xi),
\tag{41.21}
$$

with the original zero-amplitude, zero-coherence, singular-endpoint,
sign-tie and actual-lift cases retained. Theorem 41.4 uses
$m=N_{\mathrm{geo}}$ on the existing prefix $(0,\beta]$; it does not
certify that a proposed value is $\beta$. Using its purity conclusion
to discard mixed strict competitors in a proof locating that prefix
would be circular. The full all-effect comparison remains required.

The exact evaluations of $\alpha$ and $\beta$, their general
coincidence or separation, every actual boundary equality preimage,
and inclusion or exclusion of the exhaustive-equality endpoint remain
undetermined. If $\alpha<\beta$, the equality-only alternatives
involve pure effects. Their actual separated ties, their coalescence
with the selected graph, and the identities and exhaustion of the
first competing global minimizing branches still require analysis.
Mixed equality at $\beta$ remains possible on a separated feedback
branch; its existence or exclusion and full endpoint preimage remain
unresolved. Neither existence of such a mixed endpoint nor the absence
of an earlier pure tie follows from the explicit right competitors.
Those competitors need not minimize globally, so they do not exhaust
the first competing minimizing branches.

The determinant-zero phase-variation case still requires higher-order
and global comparison. The geometric ordering beyond level four,
any missing core-infimum attainment, and all previously conditional
right-side branch-identification obligations retain their existing
boundaries. No local curvature condition, unattained tie, or prefix
purity theorem evaluates the first loss. The full original first-loss
and equality problem remains unresolved.

## 追加锚（本行以下为增补区）

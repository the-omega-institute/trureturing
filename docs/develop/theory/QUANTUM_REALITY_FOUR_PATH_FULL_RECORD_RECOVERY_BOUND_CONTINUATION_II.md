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

## 42. A selected thirteen-fourths obstruction and all-effect phase transport

**Definition 42.1 (actual phase levels).** Retain exactly the original
$\mathcal K=\operatorname{Dens}_2\times U(4)$, ordinary transpose,
one shared actual feedback, constants, distances $\rho_\pm,\rho$,
defect $g$, $f=g-\kappa\rho$, and sets of Definitions 39.1 and 41.1.
In particular $N=N_{\mathrm{geo}}$, $V(\xi)=N(\xi)+\kappa\xi$,
and $\mathcal G_\xi$ are the existing selected quantities, without
an added assertion of global optimality. Put

$$
\begin{aligned}
 R&=\frac{13}{4},&
 L&=4(c+s),& \zeta&=9-L,&
 \mathbb T&=\{z\in\mathbb C:|z|=1\},\\
 \mathcal K_{\mathrm{ph}}
   &=\{(E,\operatorname{diag}(v)U_+):
                     E\in\operatorname{Dens}_2,\ v\in\mathbb T^4\},\\
 \mathcal P_\xi&=\{X\in\mathcal K_{\mathrm{ph}}:\rho(X)=\xi\},\\
 m_{\mathrm{ph}}(\xi)&=\min_{X\in\mathcal P_\xi}f(X),&
 \mathcal A_{\mathrm{ph},\xi}
   &=\{X\in\mathcal P_\xi:f(X)=m_{\mathrm{ph}}(\xi)\}.
\end{aligned}
\tag{42.1}
$$

For $0<\xi\le R$ the phase level is compact and nonempty, since it
contains $\mathcal G_\xi$. Thus its displayed minimum is attained.
Every common scalar representative remains in these sets. The four
entries of $v$ are actual feedback parameters; only multiplication
of the whole feedback by one common scalar has the identification
already present in (39.1). Effects of every rank remain allowed.

For each actual pair write $F=T^\dagger E^{\mathsf T}T$ as in (23.9)
and let $a(U)=(P(w),Q(w))$, a row vector, where
$w=\operatorname{diag}(UU_+^\dagger)$. All of $A,B,P,Q$ always refer
to this same actual $w$.

**Theorem 42.2 (strict obstruction at the selected original level
$13/4$).** At $t_R=13/8$, let
$x_R=1-\delta_\circ(t_R)/2$, and put

$$
 p_R=\frac{11}{8}-2x_R,\qquad
 q_R=2x_R-\frac38,\qquad y_R=\sqrt{1-x_R^2}.
$$

For the determinant $\mathscr D$ of (36.43),

$$
 \frac13<x_R<\frac12,\qquad
 \mathscr D(x_R,p_R)<-\frac{q_R}{56}<0,\qquad
 m(R)<N(R).
\tag{42.2}
$$

Every pair in $\mathcal G_R$ has arbitrarily close original pure
effect and phase-feedback competitors at exactly the same joint
distance $R$, with strictly smaller $g$ and $f$. There is
$\varepsilon_R>0$ with $(R-\varepsilon_R,R]\subseteq\mathcal S$.
Consequently the original first boundaries satisfy

$$
             0<\alpha\le\beta<\frac{13}{4}.
\tag{42.3}
$$

*Proof.* Under $\delta=2(1-x)$, the scalar interval of Theorem 37.5
at $t_R$ is $[3/16,11/16]$. On it set

$$
\begin{aligned}
 p(x)&=\frac{11}{8}-2x,&q(x)&=2x-\frac38,&
 y(x)&=\sqrt{1-x^2},\\
 S(x)&=2(c+hx)\sqrt{p(x)}+2hy(x)\sqrt{q(x)},\\
 W(x)&=d^2p(x)+e^2q(x)-S(x)^2,&D_0&=d^2-e^2=4h+8s.
\end{aligned}
\tag{42.4}
$$

Theorem 37.5 makes $W(x)-\kappa R$ exactly its strictly convex
scalar objective, with the unique minimizer $x_R$. In the interior,

$$
\begin{aligned}
 W'(x)&=-2[D_0+S(x)S'(x)],\\
 S'(x)&=2h\sqrt p-\frac{2(c+hx)}{\sqrt p}
                    -\frac{2hx\sqrt q}{y}+\frac{2hy}{\sqrt q}.
\end{aligned}
\tag{42.5}
$$

Use the positive-square and half-angle inequalities

$$
 \frac7{10}<h<\frac57<\frac34,\quad
 \frac{11}{12}<c<1,\quad
 \frac38<s<\frac25,\quad
 0<c-h<\frac14,\quad s^2>\frac17,\quad c+s>\frac{13}{10}.
\tag{42.6}
$$

The bounds already in (39.11) give the corresponding weaker
inequalities. For the strengthened ones, $h^2=1/2<25/49$,
$c^2=(1+h)/2>17/20>121/144$, and
$(c+s)^2=1+h>17/10>169/100$ suffice; also
$s^2=(1-h)/2>1/7$.

At $x=1/3$, one has $p=17/24$, $q=7/24$,
$y=2\sqrt2/3>9/10$ and $hy=2/3$.
The bounds $\sqrt p>5/6$, $\sqrt q<3/5$ and (42.6) give

$$
 S'(1/3)>
       \frac76-3-\frac13+\frac{20}{9}=\frac1{18}>0.
\tag{42.7}
$$

For the negative second term use $c+hx<5/4$; for the negative third
term use $2hx<1/2$. Thus $W'(1/3)<0$.

At $x=1/2$, $p=3/8$, $q=5/8$ and $y=\sqrt3/2$.
Multiplication of the two expressions in (42.4)--(42.5), using
$h^2=1/2$ and $2hc=c+s$, gives

$$
\begin{aligned}
 4[D_0+S(1/2)S'(1/2)]
   &=8h+27s-5c-5+\frac{1-13(c+s)}{\sqrt5}\\
   &<\frac{40}{7}+\frac{54}{5}-\frac{55}{12}
                                  -5-\frac{106}{15}
     =-\frac{19}{140}<0.
\end{aligned}
\tag{42.8}
$$

Here $\sqrt5<9/4$ and $1-13(c+s)<-159/10$ give the last negative
fraction; its sign is retained when bounding its denominator.
It follows that $W'(1/2)>0$. Strict convexity proves the asserted
bracket for the actual selected $x_R$.

We next bound (36.43) throughout $1/3\le x\le1/2$, with
$p,q,y$ from (42.4) and $\alpha_0=c-h$. On this interval,

$$
\begin{gathered}
 \sqrt p<\frac67,\qquad \sqrt q<\frac45,\qquad
 hx+c>1,\qquad hy>\frac35,\\
 \frac{x^2}{(1+x)q}\le\frac27,\qquad
 \frac{x^2}{1+x}\le\frac16,\qquad qy^2\ge\frac7{27}>\frac14.
\end{gathered}
\tag{42.9}
$$

For the first ratio, clearing its positive denominator reduces the
claim to $(3x-1)(4x-3)\le0$. The second ratio increases with $x$.
For the last inequality, $(qy^2)'=2-6x^2+3x/4>0$ here, and its
value at $x=1/3$ is $7/27$.
The remaining bounds follow from the interval endpoints and (42.6);
in particular $(hy)^2\ge3/8>9/25$.
Substitution in the exact $L_a$ of (36.43) yields

$$
 0<\frac{L_a}{q}
   =\frac{h\alpha_0\sqrt p}{hx+c}\frac{x^2}{(1+x)q}
       +\frac{hx^2}{1+x}\frac1{\sqrt q\,y}
   <\frac9{196}+\frac14=\frac{29}{98}<\frac13.
\tag{42.10}
$$

If $h^2x-s^2\le0$, then $L_b<3/14$. Otherwise
$h^2x-s^2<1/4-1/7=3/28$, and

$$
 L_b<\frac3{14}+\frac3{28}\frac43
                   =\frac5{14}<\frac38.
\tag{42.11}
$$

If $L_b\le0$ its product with $L_a/q$ is nonpositive; if $L_b>0$,
(42.10)--(42.11) bound that product by $1/8$. In both cases,

$$
 \frac{\mathscr D}{q}=\frac{L_a}{q}L_b-s^2
                         <\frac18-\frac17=-\frac1{56}.
\tag{42.12}
$$

All these estimates apply at the selected $x_R$.

The original sign condition required by Theorem 36.5 holds strictly:

$$
 1+2p_R+2x_R-2y_R
       =\frac{15}{4}-2(x_R+y_R)>\frac34,
\tag{42.13}
$$

since $x_R+y_R\le\sqrt2<3/2$. Its two original sign distances
therefore have gap greater than $3/2$.
Take the actual curve (36.47)--(36.50) through either selected
orientation, and on that curve set
$a=(s\sqrt{q_R}/L_a)b$. It consists of whole diagonal unitaries
and normalized rank-one effects aligned with their own actual
amplitudes. Equations (36.48) and (36.50) keep $A$, population and
purity exactly fixed. The strict sign gap persists near zero, so
the original joint distance is exactly $R$, including its common
scalar minimization. The amplitude sum increases by

$$
       -\frac{\mathscr D}{L_a}b^2+o(b^2)>0
\tag{42.14}
$$

for all sufficiently small nonzero $b$. Its base value is positive,
so $g$ and then $f$ strictly decrease. Multiplication of the whole
curve by the selected common scalar covers every representative.
This proves the actual strict competitors and $m(R)<N(R)$.

Left continuity of $m$ and continuity of $N$ in Theorem 39.2 give
the asserted left interval of strict loss. Theorem 39.4 supplies
$0<\alpha\le\beta$; the interval just obtained gives $\beta<R$.
No first-boundary identification follows from the negative
variation alone. $\square$

**Theorem 42.3 (same-effect phase transport on every level through
$13/4$).** For every original $X=(E,U)$ with
$0<\rho(X)=\xi\le R$, its minimizing original sign $\sigma$ is unique.
There are finitely many probabilities $\theta_j>0$ and actual
unitaries $U_j$, each of phase-feedback form relative to $U_+$,
such that

$$
\begin{aligned}
 \sum_j\theta_j&=1,&
 \operatorname{Tr}(U_jU_\sigma^\dagger)
     &=\operatorname{Tr}(UU_\sigma^\dagger),\\
 \rho_\sigma(E,U_j)&=\xi=\rho(E,U_j),&
 \rho_{-\sigma}(E,U_j)&>\xi,\\
 w&=\sum_j\theta_j w_j,&
 a(U)&=\sum_j\theta_j a(U_j),&
 w_j&=\operatorname{diag}(U_jU_+^\dagger).
\end{aligned}
\tag{42.15}
$$

The effect $E$, its ordinary transpose, positivity, trace, impurity
and rank are all unchanged. With $a=a(U)$ and $a_j=a(U_j)$ one has
the exact identity

$$
 \boxed{\quad
 f(E,U)=\sum_j\theta_j f(E,U_j)
               +\sum_j\theta_j\|(a_j-a)F^{1/2}\|_2^2 .
 \quad}
\tag{42.16}
$$

In particular at least one actual phase pair with this same effect
and original distance has no larger value.

*Proof.* First establish the two-sign budget on the original domain.
For $d_{\mathrm{tr}}=(1,-1,i,-i)$ and any actual diagonal $w$,
$|w_k|\le1$ and the identity
$|a_0|+|b_0|=\max_{|\mu|=1}|a_0+\mu b_0|$ give

$$
\begin{aligned}
 A(w)+B(w)
 &\le\max_{\phi\in\mathbb R}
                 \sum_{k=1}^4|1+e^{i\phi}d_{\mathrm{tr},k}|\\
 &=\max_{\phi\in\mathbb R}
        2\left(\sqrt{1+|\sin\phi|}+\sqrt{1+|\cos\phi|}\right)\\
 &\le4\sqrt{1+h}=4(c+s)=L.
\end{aligned}
\tag{42.17}
$$

Pair the coefficients with $d_{\mathrm{tr},k}=\pm1$ and with
$d_{\mathrm{tr},k}=\pm i$ to obtain the second line.
Concavity of the square root and
$|\sin\phi|+|\cos\phi|\le\sqrt2=2h$ give the last line.
No condition on independently chosen amplitudes is used.

The half-angle identities and $h<5/7$ imply

$$
 (c+s)^2=1+h<\frac{12}{7}<\left(\frac{21}{16}\right)^2,
 \qquad \zeta>\frac{15}{4}.
\tag{42.18}
$$

For every normalized positive two-by-two effect, (23.9)--(23.10)
give $0\le\epsilon=2\det F\le1/2$. Hence throughout the claimed
interval,

$$
             \xi+\epsilon\le\frac{13}{4}+\frac12
                            =\frac{15}{4}<\zeta.
\tag{42.19}
$$

For this same $E$ and any actual feedback $U'$,
(41.3) and (42.17) imply

$$
 \rho_+(E,U')+\rho_-(E,U')
      =18-2(A(w')+B(w'))-2\epsilon
      \ge2(\zeta-\epsilon).
\tag{42.20}
$$

If one branch equals $\xi$, (42.19) makes the other strictly larger
than $\xi$. This proves uniqueness of the input minimizing sign
and will also prove exact level preservation for each replacement.

Spectrally decompose the actual unitary
$V_\sigma=UU_\sigma^\dagger$:

$$
 V_\sigma=Z\operatorname{diag}(\lambda_1,\ldots,\lambda_4)Z^\dagger,
 \qquad Z\in U(4),\qquad |\lambda_k|=1.
\tag{42.21}
$$

The matrix $D_{ik}=|Z_{ik}|^2$ is doubly stochastic, since every row
and column of $Z$ has squared norm one. Apply the finite
Birkhoff--von Neumann theorem, in the form stated in
[Vourdas, arXiv:2203.09468v1, Section II.1, (18)](https://arxiv.org/html/2203.09468v1):
write $D=\sum_j\theta_j\Pi_j$, with permutation matrices $\Pi_j$
and probabilities, discarding zero weights. Set

$$
               U_j=\operatorname{diag}(\Pi_j\lambda)U_\sigma,
 \qquad \lambda=(\lambda_1,\ldots,\lambda_4)^{\mathsf T}.
\tag{42.22}
$$

Every $U_j$ is a whole actual unitary.
The matrix $C_\sigma=U_\sigma U_+^\dagger$ is diagonal and unitary:
it is $I_4$ for $\sigma=+$ and
$\operatorname{diag}(1,-1,-i,i)$ for $\sigma=-$.
Thus $U_j$ is also of the form $\operatorname{diag}(v_j)U_+$
with $v_j\in\mathbb T^4$.
The permutation preserves $\sum_k\lambda_k$, proving the complex
trace equality in (42.15). By (23.11), with $E$ unchanged, its
$\sigma$ distance is exactly $\xi$. Equations (42.19)--(42.20)
prove its other branch is strictly larger, so its true original
joint distance is $\xi$.

The diagonal of (42.21) is $D\lambda=\sum_j\theta_j\Pi_j\lambda$.
Multiplication on the right by the fixed diagonal $C_\sigma$
therefore gives $w=\sum_j\theta_jw_j$. The definitions of $P,Q$
in (23.2) are complex linear in $w$, so $a=\sum_j\theta_ja_j$.
This is a forward consequence of the spectral representation of
the given actual matrix. It asserts no converse that every convex
combination is a diagonal in a specified normal unitary orbit.

Finally (23.12) gives, on every one of these actual pairs,

$$
 g(E,U)=d^2p+e^2(1-p)-aFa^\dagger.
$$

Expansion using $\sum_j\theta_j(a_j-a)=0$ yields

$$
 \sum_j\theta_j(a_j-a)F(a_j-a)^\dagger
             =\sum_j\theta_j a_jFa_j^\dagger-aFa^\dagger\ge0.
\tag{42.23}
$$

All the pairs have the same original level, so subtracting
$\kappa\xi$ proves (42.16). A finite weighted average cannot be
strictly below every one of its terms, proving the last assertion.

The argument divides by no effect eigenvalue, feedback trace,
amplitude or spectral gap. It includes singular $F$, the
maximally mixed effect, $P=0$, $Q=0$, zero coherence, zero original
diagonal entries, repeated unitary eigenvalues and nonunique
Birkhoff decompositions. A zero active trace and a minimizing-sign
tie are excluded here by the proved level bound, not by a discarded
case: nonnegativity of the effect-distance term gives its active
trace modulus at least $4-\xi/2\ge19/8$, and (42.20) excludes a tie.
The inactive trace may vanish. The probabilities compare alternative
whole original pairs, with the same $E$ and one shared $U_j$ per
pair; they do not give different controls to columns or outcomes.
$\square$

**Theorem 42.4 (attained phase value and exact original minimizing
preimage).** For every $0<\xi\le R$,

$$
          m(\xi)=m_{\mathrm{ph}}(\xi),\qquad
          \mathcal A_{\mathrm{ph},\xi}
                         =\mathcal A_\xi\cap\mathcal P_\xi.
\tag{42.24}
$$

For any $X=(E,U)$ at that level and any spectral/Birkhoff
decomposition in Theorem 42.3,

$$
\begin{aligned}
 X\in\mathcal A_\xi
 \quad\Longleftrightarrow\quad&
  (E,U_j)\in\mathcal A_{\mathrm{ph},\xi}
                          \quad\hbox{for every }j,\\
 & (a_j-a)F^{1/2}=0\quad\hbox{for every }j.
\end{aligned}
\tag{42.25}
$$

This condition holds for every such decomposition when $X$ minimizes,
and its validity for one such decomposition is sufficient.
Moreover,

$$
       \mathcal A_\xi=\mathcal G_\xi
       \quad\Longleftrightarrow\quad
       \mathcal A_{\mathrm{ph},\xi}=\mathcal G_\xi.
\tag{42.26}
$$

Every nongeometric original global minimizer has a nongeometric phase
global replacement with exactly the same effect. In particular, a
mixed original global minimizer exists at a level in this interval
if and only if a mixed phase global minimizer exists there.

*Proof.* Theorem 42.3 compares every original pair with a phase pair
at the same original level, giving $m\ge m_{\mathrm{ph}}$.
The reverse inequality is set inclusion. Both minima are attained
by compactness, proving (42.24).
Every summand $f(E,U_j)$ in (42.16) is at least their common
minimum and every variance summand is nonnegative. All weights
are positive. Equality to $m(\xi)$ is therefore equivalent to
exactly the two conditions in (42.25).
For positive definite $F$, the variance condition forces $a_j=a$.
For rank-one $F$ it only forces the displayed seminorm condition,
and is not replaced by equality of the two amplitude rows.

Suppose now that every phase global minimizer belongs to
$\mathcal G_\xi$, and let $X\in\mathcal A_\xi$.
By (42.25), all its positive-weight replacements lie in
$\mathcal G_\xi$. The selected effects for its two orientations
are distinct because the selected $p,q$ are positive.
Since $E$ is unchanged, it fixes one orientation $\tau$ for all
these replacements. Every selected geometric pair has unique
minimizing sign $+$ by (37.23), so the common sign in (42.15)
must be $+$. Write their feedbacks as
$\lambda_j\operatorname{diag}(w_\tau)U_+$, using exactly (39.2).
The preserved complex active trace equals

$$
       \operatorname{Tr}(U_jU_+^\dagger)=2(1+x)\lambda_j,
\tag{42.27}
$$

with the same selected $x>0$. It fixes $\lambda_j$, so all $U_j$
coincide. Their averaged diagonal $w$ is consequently that same
selected diagonal, with every coordinate of modulus one.
For the actual unitary $UU_+^\dagger$, each row's entire squared
norm is then already supplied by its diagonal entry. All its
off-diagonal entries vanish. Thus $U$ is that selected feedback
itself, and $X\in\mathcal G_\xi$.
The phase assumption also gives $m=N$ and hence
$\mathcal G_\xi\subseteq\mathcal A_\xi$, proving the forward
rigidity needed in (42.26).
Conversely, if $\mathcal A_\xi=\mathcal G_\xi$, (42.24) and
$\mathcal G_\xi\subseteq\mathcal P_\xi$ prove its phase version.

The same rigidity argument shows that a nongeometric original
minimizer cannot have only geometric positive-weight replacements.
At least one is nongeometric and keeps its exact original $E$.
For a mixed original minimizer all replacements are mixed; in the
opposite direction a phase mixed minimizer is already an original
one by (42.24). No assertion that every original minimizer itself
has phase feedback is made when the phase minimizing set is larger
than $\mathcal G_\xi$. $\square$

**Corollary 42.5 (the original bad sets and first boundaries are
phase-domain questions).** Define subsets of $(0,R]$ by

$$
\begin{aligned}
 \mathcal B_{\mathrm{ph}}
   &=\{\xi:\exists X\in\mathcal P_\xi\setminus\mathcal G_\xi,\
                                      f(X)\le N(\xi)\},\\
 \mathcal S_{\mathrm{ph}}
   &=\{\xi:m_{\mathrm{ph}}(\xi)<N(\xi)\}.
\end{aligned}
\tag{42.28}
$$

Then

$$
\begin{aligned}
 \mathcal B\cap(0,R]&=\mathcal B_{\mathrm{ph}},&
 \mathcal S\cap(0,R]&=\mathcal S_{\mathrm{ph}},\\
 \alpha&=\inf\mathcal B_{\mathrm{ph}},&
 \beta&=\inf\mathcal S_{\mathrm{ph}}.
\end{aligned}
\tag{42.29}
$$

At both $b=\alpha,\beta$, the value is $m_{\mathrm{ph}}(b)=N(b)$,
and every selected geometric pair is a phase and original global
minimizer. The exhaustive-equality prefix includes $\alpha$
exactly when
$\mathcal A_{\mathrm{ph},\alpha}=\mathcal G_\alpha$.
For every $0<\xi\le R$ the exact value formula is

$$
 m(\xi)=
   \min_{\substack{w\in\mathbb T^4,\ \sigma\in\{+,-\}\\
                              \sigma\ \mathrm{admissible}}}
                    M_\sigma(w,\xi)-\kappa\xi .
\tag{42.30}
$$

Consequently the full original value certificate $m(\xi)=N(\xi)$
at such a level is equivalent to

$$
 M_\sigma(w,\xi)\ge V(\xi)
 \quad\hbox{for every }w\in\mathbb T^4
                       \hbox{ and every admissible }\sigma.
\tag{42.31}
$$

All effects on both arcs of Theorem 36.2, including their mixed and
singular endpoints, remain in this certificate.

*Proof.* Equation (42.24) proves equality of the strict-loss sets.
For either the original or phase domain, geometric feasibility
gives a value at most $N$. If it is strictly less, an attained
minimizer is nongeometric and witnesses the corresponding bad set.
If it equals $N$, a bad-set witness is exactly an extra global
minimizer outside $\mathcal G_\xi$. Thus membership in each bad set
is exactly failure of exhaustive geometric equality.
Equation (42.26) now proves equality of the bad sets, even though
an arbitrary nonglobal witness need not transport to a
nongeometric witness term by term.
By (42.3), both original infima lie strictly below $R$; restricting
either original set to $(0,R]$ therefore leaves its infimum
unchanged. This proves (42.29).
The endpoint value and prefix-inclusion statements are Theorem 39.5
combined with (42.24)--(42.26).

Every $w\in\mathbb T^4$ here has the explicit actual realization
$U=\operatorname{diag}(w)U_+$. Applying the attained effect profile
(36.6)--(36.7) at each such $U$ and then (42.24) proves (42.30).
Its minimum is attained since $\mathcal P_\xi$ is compact.
Geometric feasibility proves the equivalence with (42.31).
The profile and its equality preimage are unchanged, including
$uv=0$, zero coherence, degenerate arcs and rank changes.
For a proposed boundary, (42.31) must still be proved on all the
required preceding levels; the equivalence does not supply that
inequality. $\square$

**Corollary 42.6 (actual phase branches and mixed boundary contact).**
For $b=\alpha$ or $b=\beta$, there is a sufficiently short interval
$(b,b+\varepsilon)\subset(0,R)$ with a real analytic semialgebraic
branch of actual phase global minimizers

$$
       \xi\longmapsto (E(\xi),U(\xi))
                              \in\mathcal A_{\mathrm{ph},\xi},
\tag{42.32}
$$

having an actual phase limit in $\mathcal A_{\mathrm{ph},b}$.
At $\beta$ it is strictly below $N$ throughout that interval.
Whenever every level in a right interval at $b$ has a nongeometric
original global minimizer, (42.32) can be chosen nongeometric
throughout a shorter interval. This applies at $\alpha$ when
$\mathcal A_\alpha=\mathcal G_\alpha$, in which case the endpoint
limit lies in $\mathcal G_\alpha$.

A mixed original global minimizer at either boundary has a mixed
phase global replacement with the identical effect. At such a phase
contact $(E,U_{\mathrm{ph}})$, the family of Theorem 41.3 keeps
that same actual phase feedback and, for
$0<\theta\le\min\{\epsilon(E),4-b\}$, satisfies

$$
\begin{aligned}
 \rho(E_\theta,U_{\mathrm{ph}})&=b+\theta,\\
 f(E_\theta,U_{\mathrm{ph}})-N(b+\theta)
                       &=V(b)-V(b+\theta)<0.
\end{aligned}
\tag{42.33}
$$

These are actual strict competitors, with no assertion of global
minimality at their new levels. A mixed minimizer at $\alpha$
still forces $\alpha=\beta$; one at $\beta$ does not exclude an
earlier pure equality tie.

*Proof.* The actual phase condition is semialgebraic and closed:
in real and imaginary coordinates it is the condition that
$UU_+^\dagger$ be diagonal unitary. Intersect the original
semialgebraic minimizing graph of Theorem 39.4 with this condition.
By (42.24) every level fiber on $(0,R)$ is nonempty and compact.
Use the selection argument of Theorem 39.6 on this graph.
Hardt triviality, in the form of
[Drusvyatskiy--Lewis, arXiv:1004.0368v1, Theorem 2.25 and
Corollary 2.27](https://arxiv.org/html/1004.0368v1), applies to its
continuous semialgebraic coordinate projection, compatibly with
the geometric subgraph. On a sufficiently short right interval,
fixing one point of the trivialized fiber gives a continuous
semialgebraic section. Theorem 3.4 of
[Drusvyatskiy--Ioffe--Lewis, arXiv:1504.07694v1](https://arxiv.org/html/1504.07694v1)
applied to this already selected single-valued map makes it
analytic after shortening the interval. No finite-fiber or
generic-minimizer assumption is required.
Its bounded semialgebraic real coordinates have finite one-sided
limits, by the monotonicity argument used in Theorem 39.6.
Closedness of the phase condition and value continuity at $b$
in Theorem 39.5 place the actual limit in
$\mathcal A_{\mathrm{ph},b}$.

If every original fiber has a nongeometric minimizer, Theorem 42.4
gives such a phase minimizer in every fiber. Compatible
trivialization then permits choosing the section outside the
geometric subgraph. Theorem 39.5 supplies the asserted nongeometric
right interval at $\alpha$ under its stated endpoint condition,
and the strict-loss interval at $\beta$.
If the endpoint has only geometric minimizers, the endpoint limit
must be geometric. No nongeometric right interval at $\alpha$
is inferred solely from an extra endpoint minimizer.

For a mixed endpoint minimizer, use (42.25) and unchanged $E$ to
obtain a mixed phase endpoint minimizer, whose $g$ equals $V(b)$.
Theorem 41.3 changes only its effect and keeps both original
distance branches, with their common increment $\theta$.
Theorem 41.2 supplies the strict increase of $V$, giving (42.33)
exactly as in Corollary 41.5.
The coincidence statement at $\alpha$ and its stated limitation at
$\beta$ are therefore the existing conclusions of that corollary,
now realized with actual phase feedback. The separated mixed
feedback alternative of (41.19) remains in force; the transport
does not exclude it. $\square$

**Mathematical source correspondence 42.7.** The selected scalar,
its strict convexity and its actual geometric preimage are
Theorem 37.5 and (39.2). The phase variation, fixed-level identities
and its determinant are exactly Theorem 36.5; (42.4)--(42.14)
place the selected point of level $13/4$ inside its strict region.
The continuity and endpoint inputs are Theorems 39.2 and 39.5.
The all-effect geometric ordering and selected-feedback margins
of Section 40 retain their stated domains.

The spectral/Birkhoff replacement, preservation of the complex
active trace, the sufficient region $\xi+\epsilon<\zeta$, and the
positive quadratic variance remainder are the inherited
phase-feedback/mixed-tail transport argument. Its mathematical
ingredients are used explicitly in (42.17)--(42.23).
The additional fixed-record consequence is that
$\zeta>15/4$ and the selected obstruction at $13/4$ put both first
boundaries and right neighborhoods of them inside a region where
that transport covers every effect without changing it. The
complementary impurity region $\epsilon\ge\zeta-\xi$ is empty
throughout $0<\xi\le R$, since $\epsilon\le1/2$.
The exact original minimizing preimage, exhaustive-equality
equivalence and bad-set consequences are (42.25)--(42.31).
Theorem 41.2 and the exact motion of Theorem 41.3 are the supplied
inputs to (42.33); the prefix purity of Theorem 41.4 is not used
to establish the transport region or to certify a proposed $\beta$.

The finite Birkhoff--von Neumann theorem recalled in Vourdas,
Section II.1, (18), concerns a nonnegative matrix with every row
and column sum one. Its sole matrix here is
$D_{ik}=|Z_{ik}|^2$ for the actual four-dimensional spectral
eigenbasis in (42.21). The finite weights give actual permutation
unitaries in (42.22), rather than a presumed converse for normal
diagonals. Thompson's prescribed singular-value theorem, as
stated in
[Jasper--Loreaux--Weiss, arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3),
with four singular values equal to one gives precisely the
existing $\mathcal W$ in source Theorem 23.2.
Its introduction distinguishes this class from a specified normal
orbit, whose diagonals need not form the full convex hull of
spectral permutations. The present proof needs only the forward
spectral representation of its given $U$ and explicit actual
replacement matrices; it uses no such converse.
These standard matrix theorems and the semialgebraic selection
theorems inside Corollary 42.6 are intermediate tools for the
fixed-record deduction, with no literature-priority or exhaustive
literature-absence assertion.

**Unresolved mathematical obligations 42.8.** Equations
(42.24)--(42.31) remove the arbitrary-feedback value comparison
through $13/4$, but leave the all-effect phase-torus comparison
(42.31) on the required preceding levels unproved.
Every mixed and singular arc and both original signs must remain
in that problem. The pre-$\beta$ purity in Theorem 41.4 cannot be
used to discard mixed strict competitors while locating $\beta$.
A strict witness at $R$ supplies only the strict upper bound
(42.3), not the value of either first boundary.

The exact $\alpha,\beta$, their coincidence or separation, the
complete phase minimizing sets, and the evaluated original
variance-zero preimages in (42.25) remain undetermined.
In particular the endpoint inclusion of exhaustive equality,
additional pure ties, pure coalescence, separated mixed contact
at $\beta$, the identity and exhaustion of first competing global
minimizing branches, and determinant-zero higher-order and global
ordering are not supplied by these deductions.
The branches (42.32) give existence and actual limits, and
(42.33) gives strict competitors; neither identifies or exhausts
the global minimizing branches.
Beyond the proved interval the sufficient condition
$\xi+\epsilon<\zeta$ need not cover every effect.
All previously unresolved beyond-four geometric comparisons and
core-attainment obligations retain their stated boundaries.
The full original first-loss and equality problem remains open.

## 追加锚（本行以下为增补区）

## 43. Complete local phase isolation and attained first-boundary contact

**Definition 43.1 (selected determinant and feedback displacement).**
Retain the original domain $\mathcal K=\operatorname{Dens}_2\times U(4)$,
ordinary transpose, joint distance (39.1), both optimizer signs, and
one common scalar feedback phase. The phase domain is exactly
$\mathcal K_{\mathrm{ph}}$ of Definition 42.1, with arbitrary normalized
positive effects. All of $w,A,B,P,Q,u,v$ refer to the same actual
$w=\operatorname{diag}(UU_+^\dagger)$.
For $0<\xi<4$ put

$$
\begin{aligned}
 t&=\xi/2,& \delta_\xi&=\delta_\circ(t),&
 x_\xi&=1-\delta_\xi/2,&y_\xi&=\sqrt{1-x_\xi^2},\\
 q_\xi&=t-\delta_\xi,&p_\xi&=1-q_\xi,&
 D_{\mathrm{sel}}(\xi)&=\mathscr D(x_\xi,p_\xi),\\
 \mathscr U_\xi&=\{U:(E,U)\in\mathcal G_\xi\},&
 d_U(U,\xi)&=\operatorname{dist}_{\mathrm F}(U,\mathscr U_\xi).
\end{aligned}
\tag{43.1}
$$

Here $\mathscr D$ is precisely (36.43); its second argument specifies
$p$, with $q=1-p$. The scalar selector, $N$, $V=N+\kappa\xi$ and
$\mathcal G_\xi$ are unchanged. Theorem 37.5 gives
$0<x_\xi,y_\xi,p_\xi,q_\xi<1$. The auxiliary displacement $d_U$
measures proximity to both full selected scalar orbits. It does not
replace any summand or minimization in the original distance $\rho$.
In particular the phase orientation $\tau$ below is not the optimizer
sign $\sigma$ in that distance.

**Theorem 43.2 (a complete local chart on actual phase feedbacks).**
Fix $0<\delta_0<2$, $x_0=1-\delta_0/2$,
$y_0=\sqrt{1-x_0^2}$ and $\tau\in\{+1,-1\}$.
A neighborhood, modulo the one common scalar, of
$(x_0+\tau i y_0,x_0-\tau i y_0,1,1)$ in $\mathbb T^4$
has the real analytic coordinates $(\delta,a,b)$
near $(\delta_0,0,0)$ given by

$$
\begin{aligned}
 x&=1-\delta/2,\\
 X&=-\cos b\cos a+
              \sqrt{(1+x)^2-\cos^2b\sin^2a},&
 Y&=\sqrt{1-X^2},\\
 w_\tau(\delta,a,b)
   &=\bigl(e^{ia}(X+\tau iY),e^{ia}(X-\tau iY),
                         e^{i\tau b},e^{-i\tau b}\bigr),\\
 U&=\lambda\operatorname{diag}(w_\tau(\delta,a,b))U_+,
                         &|\lambda|&=1.
\end{aligned}
\tag{43.2}
$$

All square roots here are the positive branches at the base point.
The coordinate $\delta$ is exactly $4-A(w)$, not a new distance.
For this single actual feedback, before multiplication by $\lambda$,

$$
\begin{aligned}
 A&=2(1+x)=4-\delta,\\
 P&=2(hXe^{ia}+c\cos b),\\
 Q&=2\tau(ihYe^{ia}-s\sin b),\\
 B&=2|iYe^{ia}-\sin b|.
\end{aligned}
\tag{43.3}
$$

Thus varying $\delta$ in (36.47), along with its two phase variables,
exhausts every nearby phase feedback after exactly the original
scalar identification.

*Proof.* Use continuous local arguments for four phase entries near
the displayed base point. Their third and fourth arguments determine
one common mean phase $\lambda$. After removing it, write the last
two entries as $e^{i\tau b},e^{-i\tau b}$, with $b$ small. The mean
argument of the first two entries determines $a$ near zero. Their
half difference has the form $\tau\theta$, where
$\theta$ is near $\arccos x_0\in(0,\pi/2)$. Hence the first two
entries are uniquely $e^{ia}(X+\tau iY),e^{ia}(X-\tau iY)$,
where $X=\cos\theta>0$, $Y=\sin\theta>0$.
These choices recover all three local coordinates of the quotient;
no relative phase has been removed by the common normalization.

Their trace modulus is $2|Xe^{ia}+\cos b|$. Set
$x=A/2-1$ and $\delta=2(1-x)$. The equation for this modulus is

$$
 X^2+2X\cos b\cos a+\cos^2b=(1+x)^2.
\tag{43.4}
$$

At the base point its derivative in $X$ is $2(1+x_0)>0$.
The quadratic root near $x_0$ is exactly (43.2); its other root is
$-2-x_0$ at the base point and cannot represent the recovered $X$.
The radicals remain positive and $0<X<1$ on a smaller neighborhood.
Conversely (43.2) solves (43.4), has four entries of modulus one,
and recovers the same local arguments and trace coordinate.
The argument coordinates and these square roots are analytic there,
so both the chart and its local inverse are analytic.
Every displayed feedback is an actual unitary. Substitution in the
original linear amplitude formulas (23.2) proves (43.3).
Multiplication by $\lambda$ multiplies $P,Q$ by that same scalar
and preserves $A,B,u,v$. It supplies every actual scalar representative.
$\square$

**Theorem 43.3 (quantitative all-effect phase isolation).**
Suppose $0<\xi_0<4$ and $D_{\mathrm{sel}}(\xi_0)>0$.
There are an open interval $I$ about $\xi_0$, with
$\overline I\subset(0,4)$, and constants $r,c_1,c_2>0$ such that
every original phase pair $(E,U)$ satisfying

$$
 \rho(E,U)=\xi\in I,\qquad d_U(U,\xi)<r
\tag{43.5}
$$

has coordinates (43.2) near one of the selected orientations and
obeys

$$
\begin{aligned}
 f(E,U)-N(\xi)
 &\ge c_1\bigl[(\delta-\delta_\xi)^2+a^2+b^2\bigr]
                         +\frac{49}{360}\epsilon(E),\\
 f(E,U)-N(\xi)
 &\ge c_2 d_U(U,\xi)^2+\frac{49}{360}\epsilon(E).
\end{aligned}
\tag{43.6}
$$

Equality $f(E,U)=N(\xi)$ within (43.5) holds if and only if
$(E,U)\in\mathcal G_\xi$. Every normalized positive effect at
these actual feedbacks is included, with no rank or coherence-phase
restriction on the input.

*Proof.* Work first near one selected orientation at $\xi_0$.
The selected level and feedback lie in the open set $\Omega$ of
Theorem 40.4. Shrink a product neighborhood in level and chart
coordinates so that all its points remain in $\Omega$. In particular
$uv>0$, the negative sign has $t_-<0$, and the positive pure endpoint
$k=t_+$ satisfies $0<k<1$ and $k<J_+$. Equations (43.3) and (36.2)
give, with $t=\xi/2$,

$$
                  k=t-\delta=:q,\qquad p=1-q.
\tag{43.7}
$$

The unique minimizing effect at this same actual feedback and
original level is

$$
 \widehat E=\left[T\begin{pmatrix}
 p&\sqrt{pq}\,\bar P Q/(uv)\\
 \sqrt{pq}\,P\bar Q/(uv)&q
 \end{pmatrix}T^\dagger\right]^{\mathsf T}.
\tag{43.8}
$$

It is positive, trace one and rank one, and the strict condition
$k<J_+$ makes the positive sign uniquely minimizing in the original
joint distance. The exclusion $t_-<0$ applies to every effect at
this $U$ and level, not just to (43.8). The inherited comparison is

$$
 f(E,U)\ge f(\widehat E,U)+\frac{49}{360}\epsilon(E).
\tag{43.9}
$$

This comparison is unconditional on full-domain geometric optimality.
It retains mixed effects and singular effects on the exact feasible
arc, including its zero-coherence upper endpoint.

Define the reduced analytic objective on this neighborhood by

$$
 \Psi(t,\delta,a,b)
   =d^2p+e^2q-(\sqrt p\,u+\sqrt q\,v)^2-2\kappa t.
\tag{43.10}
$$

Here $u,v$ are evaluated on (43.2), and $p,q$ are (43.7).
It equals $f(\widehat E,U)$ by the original same-feedback identity.
All square roots and amplitude moduli are analytic because
$p,q,u,v$ are positive. At $a=b=0$ it is exactly
$\mathcal H_{+,t}(\delta)=H^+_\delta(t-\delta)$ of (37.12).
Put $\gamma_c=c-h>0$ and, for these scalar parameters, write

$$
\begin{aligned}
 y&=\sqrt{1-x^2},&
 S_0&=2(hx+c)\sqrt p+2hy\sqrt q,\\
 L_a&=\frac{hx^2}{1+x}
       \left(\frac{\gamma_c\sqrt p}{hx+c}+\frac{\sqrt q}{y}\right),&
 L_b&=\gamma_c\sqrt p+
                      \frac{(h^2x-s^2)\sqrt q}{hy},\\
 K&=\begin{pmatrix}L_a&-s\sqrt q\\-s\sqrt q&L_b\end{pmatrix}.
\end{aligned}
\tag{43.11}
$$

These are the coefficients of (36.43), with $S_0>0$, $L_a>0$.
For every nearby $t,\delta$, (36.52)--(36.54) give

$$
 \Psi(t,\delta,a,b)
 =\mathcal H_{+,t}(\delta)
       +2S_0\bigl(L_aa^2+L_bb^2-2s\sqrt q\,ab\bigr)
       +o(a^2+b^2).
\tag{43.12}
$$

The expansion holds for both orientations. Analyticity shows that
$\partial_a\Psi=\partial_b\Psi=0$ identically along $a=b=0$;
therefore the scalar--phase entries of its Hessian vanish there.
The scalar stationary point is $\delta_\xi$, by Theorem 37.5.

To bound its scalar Hessian, use $F,G$ in (37.12). On the interior
of the positive feasible scalar interval, (37.22) gives
$F''\le1-8hc$ and $G''\le0$. They are positive concave functions
there, so their geometric mean is concave. Indeed its second
derivative is

$$
 (\sqrt{FG})''
   =\tfrac12\sqrt{G/F}\,F''+\tfrac12\sqrt{F/G}\,G''
                    -\frac{(F'G-FG')^2}{4(FG)^{3/2}}\le0.
\tag{43.13}
$$

The remaining terms of $\mathcal H_{+,t}$ are affine in $\delta$.
Consequently, at every selected interior point,

$$
\begin{aligned}
 h_t&:=\mathcal H''_{+,t}(\delta_\xi)\ge8hc-1>0,\\
 \nabla^2_{(\delta,a,b)}\Psi(t,\delta_\xi,0,0)
       &=\begin{pmatrix}h_t&0\\0&4S_0K\end{pmatrix},&
 \det K&=D_{\mathrm{sel}}(\xi).
\end{aligned}
\tag{43.14}
$$

The scalar implicit function theorem applies to
$\mathcal H'_{+,t}(\delta)=0$ because $h_t>0$.
The selected solution is locally analytic in $t$: uniqueness and
continuity from Theorems 37.5 and 39.2 identify it with that implicit
solution. Thus its stationary point in (43.14) varies analytically.
At $\xi_0$, $L_a>0$ and $\det K>0$ make the whole three-variable
Hessian positive definite. By continuity choose a closed parameter
interval about $\xi_0$ and a small convex coordinate ball about
each $(\delta_\xi,0,0)$ on which the Hessian is uniformly bounded
below by $\mu I_3$ for some $\mu>0$. This is possible by first
taking a ball at the base point and then shrinking the parameter
interval so that its centers remain inside a smaller ball.

For $\mathbf z=(\delta,a,b)$ and
$\mathbf z_\xi=(\delta_\xi,0,0)$, Taylor's integral formula on
the connecting segment gives

$$
\begin{aligned}
 \Psi(t,\mathbf z)-N(\xi)
 &=\int_0^1(1-s_0)(\mathbf z-\mathbf z_\xi)^{\mathsf T}
     \nabla^2\Psi(t,\mathbf z_\xi+s_0(\mathbf z-\mathbf z_\xi))
                 (\mathbf z-\mathbf z_\xi)\,ds_0\\
 &\ge\frac\mu2\|\mathbf z-\mathbf z_\xi\|_2^2.
\end{aligned}
\tag{43.15}
$$

The constant and linear Taylor terms are respectively $N(\xi)$
and zero. Shrinking the balls if necessary, bounded chart derivatives
give a uniform $C>0$ with

$$
 \|U-\lambda\operatorname{diag}
                 (w_\tau(\delta_\xi,0,0))U_+\|_{\mathrm F}
       \le C\|\mathbf z-\mathbf z_\xi\|_2.
\tag{43.16}
$$

The displacement $d_U$ is no larger than the left side.
Both orientations have the same objective calculation; take the
smaller of their neighborhoods and bounds. Their selected orbits
are disjoint at positive levels, and remain disjoint over a small
closed level interval. The complete chart and its local inverse,
together with compactness of the scalar circle, supply $r>0$ such
that every phase feedback with $d_U<r$ lies in one of these coordinate
balls, uniformly over a smaller interval $I$. More explicitly, a
failure of such a radius would give levels in that closed interval
and phase feedbacks converging to its selected graph from outside
the open chart neighborhoods. A convergent subsequence and the
continuity of that graph contradict their openness.
This proves complete neighborhood coverage, not just coverage of
chosen variation curves.

Combining (43.9), (43.15) and (43.16) proves (43.6), with
$c_1=\mu/2$ and $c_2=\mu/(2C^2)$ after any needed reduction of
$\mu$. If $f=N$, (43.15) forces
$\delta=\delta_\xi$, $a=b=0$. At that actual selected feedback,
Theorem 40.4 gives the unique minimizing effect (43.8), which is
the selected effect in (39.2). In particular a pure effect with
misaligned coherence is not an additional equality case.
Conversely every pair in $\mathcal G_\xi$ has $f=N(\xi)$ and
satisfies (43.5). This proves the exact equality assertion. $\square$

**Theorem 43.4 (noncoalescence off zero determinant and the simple
reduced null mode).** Let $0<\xi_0<4$ and
$D_{\mathrm{sel}}(\xi_0)\ne0$. If $\xi_n\to\xi_0$ and
$X_n=(E_n,U_n)$ minimizes $f$ on the actual phase level
$\mathcal P_{\xi_n}$, with $d_U(U_n,\xi_n)\to0$, then
$X_n\in\mathcal G_{\xi_n}$ for all sufficiently large $n$.
Thus a sequence of nongeometric phase global minimizers coalescing
with the selected graph at a positive interior level requires
$D_{\mathrm{sel}}(\xi_0)=0$.

If $D_{\mathrm{sel}}(\xi_0)=0$, the reduced Hessian in (43.14)
is positive semidefinite with exactly one null direction, in the
coordinate order $(\delta,a,b)$:

$$
 \ker\nabla^2_{(\delta,a,b)}\Psi
    =\operatorname{span}_{\mathbb R}
           \left\{\left(0,\frac{s\sqrt{q_{\xi_0}}}{L_a},1\right)\right\}.
\tag{43.17}
$$

The coefficients in (43.17) are evaluated at $\xi_0$.
This is the Hessian after the same-level effect minimum and the
single common scalar quotient. It asserts no Hessian statement for
the full positive-effect boundary, and no higher-order sign,
existence of a new branch, or global sufficiency at determinant zero.

*Proof.* The chart and analytic objective in the proof of Theorem
43.3 exist irrespective of the determinant sign. The Hessian
(43.14) is invertible when $D_{\mathrm{sel}}\ne0$. Apply the
implicit function theorem to the three equations
$\nabla_{(\delta,a,b)}\Psi=0$, with $t$ as parameter.
It gives a unique stationary solution near the selected point for
each nearby $t$. The selected analytic scalar solution already
satisfies those equations, so it is that unique solution.

By Theorem 40.4, every sufficiently late $X_n$ has the unique
fixed-feedback minimizing effect $\widehat E_n$. Indeed phase
minimality implies fixed-feedback minimality, since varying only
$E$ keeps the feedback in the phase domain. After choosing the
nearby selected orientation and its common scalar representative,
the local inverse chart puts its coordinates near
$(\delta_{\xi_0},0,0)$. The reduced point must be stationary:
every nearby chart feedback with its effect (43.8) is an actual
phase pair at this same original level. Local variation is open
in all three coordinates. The unique stationary solution therefore
forces $U_n\in\mathscr U_{\xi_n}$, and fixed-feedback uniqueness
forces $X_n\in\mathcal G_{\xi_n}$. The two orientation charts
and their compact scalar orbits give the assertion for the whole
sequence. In the negative-determinant case the selected stationary
point has a decreasing direction, so a global minimizer cannot
actually occur there; the stated noncoalescence conclusion still
holds.

At zero determinant, $L_a>0$ gives $L_b=s^2q/L_a>0$, and

$$
             (a,b)K(a,b)^{\mathsf T}
                   =L_a\left(a-\frac{s\sqrt q}{L_a}b\right)^2.
\tag{43.18}
$$

The scalar block $h_t$ is strictly positive and $S_0>0$.
Hence the only reduced null direction is (43.17), and both
remaining reduced eigenvalues are positive. The common phase was
already quotiented out; it is not an additional null coordinate
in this statement. $\square$

**Theorem 43.5 (attained separated contact at a positive-determinant
first boundary).** At either original first boundary
$b\in\{\alpha,\beta\}$,

$$
                         D_{\mathrm{sel}}(b)\ge0.
\tag{43.19}
$$

If $D_{\mathrm{sel}}(b)>0$, there is an actual phase pair
$X_b=(E_b,U_b)$ such that

$$
 X_b\in\mathcal A_{\mathrm{ph},b}\setminus\mathcal G_b
          \subseteq\mathcal A_b\setminus\mathcal G_b,
                   \qquad d_U(U_b,b)\ge r>0,
\tag{43.20}
$$

for a sufficiently small isolation radius from Theorem 43.3.
In fact every nongeometric phase global minimizer at every sufficiently
nearby level is outside that radius of the selected feedbacks.
Consequently

$$
\begin{aligned}
 \mathcal A_b=\mathcal G_b
    &\ \Longrightarrow\ D_{\mathrm{sel}}(b)=0,\\
 D_{\mathrm{sel}}(\alpha)>0
    &\ \Longrightarrow
          \text{the exhaustive-equality prefix is }(0,\alpha).
\end{aligned}
\tag{43.21}
$$

If $\alpha<\beta$, any additional contact at $\alpha$ in
(43.20) is pure. No identity between a determinant-zero level and
either first boundary is asserted.

*Proof.* Theorem 42.2 puts $0<\alpha\le\beta<R<4$.
Theorem 39.5 gives $m(b)=N(b)$ and actual selected global minimizers
at both endpoints. Their positive sign is strict by (37.23).
A negative determinant would therefore give the actual same-distance
strict competitor of Theorem 36.5, contradicting global minimality.
This proves (43.19), using both original distances in that theorem.

Suppose the determinant is positive. Choose the interval $I$ and
radius $r$ in Theorem 43.3 with $\overline I\subset(0,R)$.
For any $\xi\in I$, (42.24) gives
$m_{\mathrm{ph}}(\xi)=m(\xi)\le N(\xi)$.
If a phase global minimizer has $d_U<r$, (43.6) and its exact
equality statement force its value to be $N(\xi)$ and the pair
to lie in $\mathcal G_\xi$. Thus every nongeometric phase global
minimizer in this interval has $d_U\ge r$.

For $b=\alpha$, (42.29) supplies levels of
$\mathcal B_{\mathrm{ph}}$ tending to $\alpha$ from at or above
$\alpha$. An isolated bad endpoint is included by taking that level
itself. At each such level there is a nongeometric phase global
minimizer: if $m_{\mathrm{ph}}<N$, any phase global minimizer is
nongeometric; if the values coincide, the bad-set witness is an
additional global minimizer. For $b=\beta$, choose levels tending
down to $\beta$ in the strict-loss right interval (39.29).
Equation (42.24) supplies phase global minimizers on these levels,
and their strictly lower values make them nongeometric.
All chosen feedbacks satisfy $d_U\ge r$.

The phase domain, with all effects, is compact. A subsequential
limit is an actual phase pair at level $b$. Endpoint value continuity
(39.27) makes its value $m(b)=N(b)$, so (42.24) puts it in both
minimizing sets. Hausdorff continuity of $\mathscr U_\xi$ preserves
$d_U\ge r$ at the limit. This proves (43.20) as an attained pair,
without identifying an explicit globally minimizing branch.
The first implication in (43.21) now follows from (43.19)--(43.20).
The contact at $\alpha$ belongs to the original bad set, so the
endpoint alternative in Theorem 39.5 proves the prefix assertion.
If $\alpha<\beta$, Theorem 41.4 forces purity at level $\alpha$.
That existing prefix result is used only for this final rank conclusion;
it is not used to locate $\beta$ or to exclude a mixed strict competitor.
$\square$

**Theorem 43.6 (uniform separation of original strict global
minimizers and their actual endpoint limits).** Suppose
$D_{\mathrm{sel}}(\beta)>0$. Choose $0<r\le1$ as in Theorems
43.3 and 43.5 near $\beta$. There is $\eta>0$ such that every
original global minimizer at every level
$\beta<\xi<\beta+\eta$ satisfies

$$
              d_U(U,\xi)\ge\frac{r^2}{4}.
\tag{43.22}
$$

These minima have $m(\xi)<N(\xi)$; no phase-feedback or rank
restriction is imposed on the minimizing input. Every subsequential
actual endpoint limit of such minimizers belongs to
$\mathcal A_\beta\setminus\mathcal G_\beta$ and retains the same
positive feedback separation. In particular an original strict global
minimizing branch coalescing with $\mathcal G_\beta$ can do so only
if $D_{\mathrm{sel}}(\beta)=0$.

*Proof.* Take $\eta$ small enough that the entire right interval
lies in $(0,R)$, in the isolation interval, and in (39.29).
Fix any $X=(E,U)\in\mathcal A_\xi$ there. The same-effect
spectral/Birkhoff decomposition of Theorem 42.3 has
$w=\sum_j\theta_jw_j$ with all $\theta_j>0$ and
$w_j\in\mathbb T^4$. By (42.25), every $(E,U_j)$ is a phase
global minimizer at this same original level. Their values are
$m(\xi)<N(\xi)$, so none is geometric and all satisfy
$d_U(U_j,\xi)\ge r$. This inference uses actual global minimality
and its equality preimage, not merely existence of a strict competitor.

Let $v$ be any selected diagonal, including either orientation and
any common scalar representative. Frobenius invariance under
multiplication by $U_+$ gives $\|w_j-v\|_2\ge r$ for every $j$.
Since $v,w_j$ have four unit-modulus coordinates,

$$
\begin{aligned}
 \operatorname{Re}\langle v,v-w\rangle
    &=\sum_j\theta_j\bigl(4-
                          \operatorname{Re}\langle v,w_j\rangle\bigr)\\
    &=\frac12\sum_j\theta_j\|v-w_j\|_2^2
      \ge\frac{r^2}{2}.
\end{aligned}
\tag{43.23}
$$

Here $\langle v,w\rangle=\sum_k\bar v_kw_k$ and $\|v\|_2=2$.
Cauchy--Schwarz therefore implies $\|v-w\|_2\ge r^2/4$.
The original unitary $V_U=UU_+^\dagger$ has diagonal $w$, so

$$
 \|U-\operatorname{diag}(v)U_+\|_{\mathrm F}
   =\|V_U-\operatorname{diag}(v)\|_{\mathrm F}
   \ge\|w-v\|_2\ge r^2/4.
\tag{43.24}
$$

Taking the infimum over all selected $v$ proves (43.22).
This support calculation compares alternative whole feedbacks from
the existing transport; it does not assign independent controls to
spectral pieces of one effect. The input $E$ is unchanged in every
replacement, including when it is mixed or singular.

The compactness and endpoint continuity of Theorem 39.6 put every
actual subsequential limit in $\mathcal A_\beta$.
Continuity of the selected feedback orbits preserves (43.22), excluding
$\mathcal G_\beta$. Actual global minimizing branches on a short
right interval exist by that theorem and obey the same uniform
separation. Finally (43.19) excludes negative determinant at $\beta$,
and (43.22) excludes coalescence at positive determinant, proving the
necessary zero-determinant condition. $\square$

**Mathematical source correspondence 43.7.** The complete chart uses
the actual phase variation (36.47) and its exact trace and amplitude
identities, now with its trace coordinate allowed to vary. Its reduced
scalar block uses the unique interior selector and strict scalar
convexity of Theorem 37.5. The transverse block is exactly the
expansion (36.52)--(36.54). The unchanged-effect comparison and its
uniform impurity coefficient are Theorem 40.4. These inputs do not
require the selected pair to be globally minimizing. The additional
fixed-record deductions are complete local phase coverage, the full
reduced Hessian isolation, the simple reduced null mode, and their
attained-contact and original-minimizer separation consequences.
The implicit function theorem and Taylor's integral formula enter
only with the analytic domains and invertible or positive Hessians
specified in (43.7)--(43.15).

The boundary arguments use Theorems 39.5--39.6 and the exact
same-effect phase value and minimizing preimage in Theorems 42.3--42.4.
The only convex decomposition used in (43.23) is the spectral/Birkhoff
decomposition of the given actual $U$. Its matrix
$|Z_{ik}|^2$ is doubly stochastic, as required by the finite
Birkhoff--von Neumann theorem cited in Section 42.7. No converse
statement about the convexity of a specified normal-unitary orbit
is needed. The reduced null mode is a second-derivative conclusion;
no parameter transversality or higher-order bifurcation condition
has been established by that calculation.

For comparison with a global certificate,
[Bandeira--Boumal--Singer, *Tightness of the maximum likelihood
semidefinite relaxation for angular synchronization*,
arXiv:1411.3272v3, Lemmas 4.3--4.4 and Section 4.3](https://arxiv.org/html/1411.3272v3),
consider a Hermitian objective matrix $C$ and the feasible matrices
$X\succeq0$ with $\operatorname{diag}X=\mathbf1$. Their certificate
requires a Hermitian slack $S\succeq0$, $SX=0$, and $S+C$ real
diagonal; rank $n-1$ of the slack yields uniqueness. Their Section
4.3 distinguishes this full positivity from positivity only on the
phase tangent space. The prescribed original distance and variable
effect of (42.31) are additional constraints and parameters. No such
uniform slack or equality kernel for them is supplied by (43.14).

Likewise [Boumal, *Nonconvex phase synchronization*,
arXiv:1601.06114v3, Theorem 4](https://arxiv.org/html/1601.06114v3)
proves global sufficiency of second-order conditions for its
unconstrained torus quadratic problem with $C=zz^*+\Delta$,
unit-modulus $z$, $\operatorname{diag}C\ge0$, and the bounds

$$
 \|\Delta\|_{\mathrm{op}}\le\frac{n^{2/3}}{14},\qquad
 \|\Delta z\|_\infty\le\frac{n^{2/3}\sqrt{\log n}}{14}.
\tag{43.25}
$$

An exact correspondence of its feasible set and these hypotheses
to the prescribed-distance, all-effect problem is absent here.
Its global conclusion therefore is not an implication of the local
Hessian calculation. These cited standard tools are intermediate
comparisons; Theorems 43.2--43.6 are repo-derived fixed-record
deductions, with no literature-priority assertion.

**Unresolved mathematical obligations 43.8.** For any proposed
preceding interval, the full value certificate remains

$$
 \Delta_\sigma(w)+b_\sigma(w)r
            -2u(w)v(w)\sqrt{t_\sigma(w,\xi)-r^2}
       \ge V(\xi)
 \quad
 \left\{\begin{array}{l}
 w\in\mathbb T^4,\quad \sigma\text{ admissible},\\
 r\in[t_\sigma,\min\{\sqrt{t_\sigma},J_\sigma\}].
 \end{array}\right.
\tag{43.26}
$$

This is (42.31), with the complete effect arc displayed. It requires
all preceding levels, both original signs, every mixed and singular
arc, and all zero-amplitude and active-endpoint cases. Theorem 43.3
controls a neighborhood of the selected phase feedbacks when its
selected determinant is positive. It supplies no comparison on the
complement, where separated pure or mixed pairs can tie or win.
Exact phase equality sets still require (36.7), and all original
minimizing lifts still require the variance-zero conditions (42.25).
Their complete evaluation is unresolved.

The exact $\alpha,\beta$, their coincidence or separation, the
identity and exhaustion of first competing globally minimizing
branches, separated mixed contact at $\beta$, and any earlier pure
equality ties remain undetermined. Endpoint exclusion at $\alpha$
is established by (43.21) only under its positive-determinant
hypothesis; endpoint inclusion or exclusion at determinant zero is
unresolved. Nongeometric phase coalescence and original strict global
minimizer coalescence in the stated scopes require determinant zero,
but a zero determinant need not produce either coalescence or first
loss and does not exclude simultaneous separated contact.
The higher-order and global signs in the simple reduced null direction
remain unresolved. An attained strict right competitor from a mixed
contact is still not thereby a globally minimizing branch.

The original mixed-minimizer exclusion near selected feedbacks in
Theorem 40.4 remains valid without a determinant hypothesis. Purity
on the already defined pre-$\beta$ prefix is not a certificate for
locating that prefix, and cannot remove the mixed strict competitors
in (43.26). Beyond $R$ the same-effect transport retains only its
proved sufficient domain; all-effect transport outside it, beyond-four
geometric ordering, and the remaining core-attainment obligations
retain their unresolved boundaries. The full original first-loss
ordering and actual equality/attainment problem is not settled by
these local and endpoint alternatives.

## 追加锚（本行以下为增补区）
## 44. Population-sensitive global spectral exclusion

**Definition 44.1 (the fixed original spectral data).** Retain the original
$\operatorname{Dens}_2\times U(4)$ domain, ordinary transpose, both original
optimizer signs, one actual shared feedback $U$, and the single common
scalar quotient from Definitions 11.1 and 23.1. For the actual pair
$(E,U)$ write

$$
F=T^\dagger E^{\mathsf T}T
 =\begin{pmatrix}p&z\\\bar z&1-p\end{pmatrix},
\qquad
0\le p\le1,\qquad |z|^2\le p(1-p),
$$

and put

$$
H=\operatorname{diag}(d^2,e^2),\qquad
D(p)=d^2p+e^2(1-p),\qquad
\epsilon=2\det F=2\bigl(p(1-p)-|z|^2\bigr).
\tag{44.1}
$$

Thus $\epsilon=1-\operatorname{Tr}(E^2)$ is the original impurity of the
same effect. Define

$$
 k=\frac{e^2}{d^2},\qquad
 L(p,\epsilon)=
 \frac{D(p)-\sqrt{D(p)^2-2d^2e^2\epsilon}}{2},
\qquad
 \theta(p)=\frac p2+k\left(\frac38-\frac p2\right).
\tag{44.2}
$$

The square root in (44.2) is the smaller-eigenvalue expression for the
positive matrix introduced in the proof below; its reality is part of
that proof and does not impose a new restriction on the original domain.

**Theorem 44.2 (population-sensitive lower bound and complete actual
saturation).** For every original normalized effect $E$ and every actual
shared feedback $U$,

$$
\boxed{\qquad g(E,U)\ge L(p,\epsilon).\qquad}
\tag{44.3}
$$

Equality in (44.3) holds exactly in the following union, with
$|\lambda|=1$:

$$
\begin{aligned}
&z=0,\quad U=\lambda U_+,\quad d^2p\ge e^2(1-p),\\
&\hspace{2.9cm}\text{or}\\[-2pt]
&z=0,\quad U=\lambda U_-,\quad d^2p\le e^2(1-p).
\end{aligned}
\tag{44.4}
$$

The description includes singular effects, coincident weighted eigenvalues,
and every common scalar representative. In the coincident case both lines
of (44.4) are allowed. No independent feedback is assigned to the two
certificate columns.

**Proof.** For a fixed actual $U$, let $a=(P,Q)$ be the row from (23.12) and
write

$$
K=H-a^\dagger a.
\tag{44.5}
$$

Formula (23.12), applied to every normalized pure effect while this same
$U$ is held fixed, and nonnegativity of the actual defect from Lemma 9.3,
give $b^\dagger Kb\ge0$ for every unit vector $b$. Hence $K\succeq0$.
Because $H$ is positive definite, the row
$b_0=aH^{-1/2}$ satisfies

$$
b_0^\dagger b_0\preceq I,\qquad \|b_0\|\le1.
\tag{44.6}
$$

Set

$$
C=H^{1/2}FH^{1/2}\succeq0.
\tag{44.7}
$$

The same actual $U$ and the original transpose give, directly from
(23.12),

$$
g(E,U)=\operatorname{Tr}(C)-b_0Cb_0^\dagger.
\tag{44.8}
$$

Therefore

$$
g(E,U)\ge\operatorname{Tr}(C)-\lambda_{\max}(C)
          =\lambda_{\min}(C).
\tag{44.9}
$$

The trace and determinant of $C$ are

$$
\operatorname{Tr}(C)=D(p),\qquad
\det C=d^2e^2\det F=\frac{d^2e^2\epsilon}{2}.
\tag{44.10}
$$

The characteristic polynomial of the Hermitian two-by-two matrix $C$ has
discriminant $D(p)^2-2d^2e^2\epsilon\ge0$. Its smaller root is exactly
$L(p,\epsilon)$, proving (44.3).

It remains to prove that no equality case has been lost. If $F$ is positive
definite and equality holds, both inequalities in (44.9) are equalities.
Thus $\|b_0\|=1$ and $b_0^\dagger$ lies in the top eigenspace of $C$.
The first condition makes $K$ singular. Choose a unit vector in $\ker K$
and use it as a pure certificate-basis effect with this same actual $U$.
Its actual defect is zero by (44.5), so Lemma 11.2 forces
$U=\lambda U_+$ or $U=\lambda U_-$. In the first case the row in
(23.12) is $(\lambda d,0)$, and in the second it is $(0,\lambda e)$.
The top-eigenspace condition then becomes respectively

$$
z=0,\quad d^2p\ge e^2(1-p),
\qquad\text{or}\qquad
z=0,\quad d^2p\le e^2(1-p).
\tag{44.11}
$$

Conversely, each condition in (44.11) gives equality directly in (23.12)
and (44.9). If $F$ is singular, its trace-one positivity makes it rank one,
so $L=0$; equality is $g=0$, and Lemma 11.2 gives exactly the two original
zero pairs. Those are the $p=1$ and $p=0$ instances already contained in
(44.4). A repeated eigenvalue is the equality case
$d^2p=e^2(1-p)$ in one of the two diagonal lines, and both optimizer rows
attain the same value. This proves the complete saturation statement.

**Theorem 44.3 (strict prescribed-level exclusion through $13/4$).** Let
$0<\rho(E,U)=\xi\le13/4$ and suppose

$$
\epsilon(E)\ge\theta(p).
\tag{44.12}
$$

Then

$$
\boxed{\qquad
 f(E,U)>N_{\mathrm{geo}}(\xi)+\frac3{16}.
\qquad}
\tag{44.13}
$$

Consequently this sector contains neither a prescribed-level tie nor a
strict-loss witness for the existing geometric envelope.

**Proof.** Put $c_0=e^2/4$. Since $D(p)\ge e^2$, the matrix
$C-c_0I$ has strictly positive trace. Its determinant is

$$
\det(C-c_0I)
 =\frac{d^2e^2\epsilon}{2}-\frac{e^2D(p)}4+\frac{e^4}{16}.
\tag{44.14}
$$

The condition (44.12) is exactly the condition that (44.14) be nonnegative:
after division by the positive $d^2e^2$, it reads
$\epsilon\ge D(p)/(2d^2)-e^2/(8d^2)=\theta(p)$.
A Hermitian two-by-two matrix with positive trace and nonnegative determinant
is positive semidefinite. Hence $L(p,\epsilon)\ge c_0$, and Theorem 44.2
gives $g(E,U)\ge c_0$.

For the strict numerical margin, reuse the actual rank-one geometric
comparison at level $13/4$. Take $x=1/2$, $y=\sqrt3/2$ and
$\tau\in\{+1,-1\}$, and use

$$
w_\tau=(x+\tau iy,x-\tau iy,1,1),\qquad
\psi_\tau=\sqrt{\frac38}\,b_+-\tau i\sqrt{\frac58}\,b_-,
$$

$$
E_\tau=\overline{\psi_\tau}\,
       \overline{\psi_\tau}^{\dagger},\qquad
U_\tau=\operatorname{diag}(w_\tau)U_+.
\tag{44.15}
$$

This is one actual shared feedback and one original pure effect. Its two
original sign distances are

$$
\rho_+(E_\tau,U_\tau)=\frac{13}{4},\qquad
\rho_-(E_\tau,U_\tau)=\frac{35}{4}-2\sqrt3>\frac{13}{4}.
\tag{44.16}
$$

Writing

$$
J_R=h+2c+h\sqrt5,\qquad
G_R=\frac{3d^2+5e^2-3J_R^2}{8},
\tag{44.17}
$$

the same-feedback formula (23.12) gives $g(E_\tau,U_\tau)=G_R$.
Theorem 37.5's actual rank-one level ordering gives
$V(13/4)=N_{\mathrm{geo}}(13/4)+\kappa(13/4)\le G_R$.
The source half-angle identities and strict rational bounds give

$$
J_R>\frac{101}{25}>4,\qquad
d^2+e^2=8+8c<\frac{31}{2}.
\tag{44.18}
$$

Indeed the first inequality uses $h>7/10$, $c>9/10$ and
$\sqrt5>11/5$; the second uses $c<15/16$.
Consequently

$$
c_0-G_R=\frac38\bigl(J_R^2-d^2-e^2\bigr)>\frac3{16}.
\tag{44.19}
$$

Theorem 41.2 says that $V$ is strictly increasing on $(0,4]$, so
$V(\xi)\le V(13/4)<c_0-3/16$. Since
$f(E,U)=g(E,U)-\kappa\xi$ and
$V(\xi)=N_{\mathrm{geo}}(\xi)+\kappa\xi$, (44.13) follows.

The witness is used only to bound the already selected geometric value; it
does not assert a new globally minimizing branch. Both signs, the common
scalar quotient, and the original joint distance remain those of
(23.11)--(23.12). $\square$

**Corollary 44.4 (the older high-impurity screen is contained).** Every
original pair with $\epsilon(E)\ge3/8$ lies in the sector (44.12).

**Proof.** Positivity gives $\epsilon=2(p(1-p)-|z|^2)\le2p(1-p)$. Thus
$\epsilon\ge3/8$ implies $p(1-p)\ge3/16$, hence $1/4\le p\le3/4$.
Since $d^2>2e^2$ by the strict half-angle inequality used below, $0<k<1/2$
and

$$
\theta(p)=\frac{3k}{8}+\frac{(1-k)p}{2}
 \le\frac{3k}{8}+\frac{3(1-k)}8=\frac38.
\tag{44.20}
$$

Therefore $\epsilon\ge3/8\ge\theta(p)$. $\square$

**Proposition 44.5 (an actual low-impurity nongeometric sector).** There are
actual original pairs outside $\mathcal C_{34}$ and both older caps, with
$\epsilon<3/8$, satisfying the strict sector condition. One explicit pair is
obtained from

$$
F=\begin{pmatrix}\frac12&\frac{\sqrt6}{8}\\[2pt]
                  \frac{\sqrt6}{8}&\frac12\end{pmatrix},\qquad
E=(TFT^\dagger)^{\mathsf T},
$$

$$
w=\left(1,1,\frac{1+i\sqrt3}{2},
             \frac{1-i\sqrt3}{2}\right),\qquad
U=\operatorname{diag}(w)U_+.
\tag{44.21}
$$

For this actual pair,

$$
\det F=\frac5{32},\quad \epsilon=\frac5{16}<\frac38,\quad F\succ0,
$$

and

$$
\rho_+=\frac{43}{16},\qquad
\rho_-=\frac{139}{16}-2\sqrt3,\qquad
\rho_--\rho_+=6-2\sqrt3>0.
\tag{44.22}
$$

Moreover $A(w)=3$, $B(w)=\sqrt3$, so $A+B>4$; the diagonal has unequal
last two entries and is outside $\mathcal C_{34}$, while
$A<2+\sqrt{8/3}$ and $B<23/6$, so it lies outside both older caps.
The half-angle identities give

$$
d^2-2e^2
 =4\left(-1+\frac{3h}{2}+c+s-4hs\right)
 >4\left(-1+\frac{21}{20}+\frac{13}{10}-\frac87\right)
 =\frac{29}{35}>0.
\tag{44.23}
$$

Here $h>7/10$, $h<5/7$, $s<2/5$ and $c+s>13/10$ are the only
strict bounds used in the displayed comparison. Hence $k<1/2$ and

$$
\theta(1/2)=\frac14+\frac{k}{8}<\frac5{16}=\epsilon.
\tag{44.24}
$$

All inequalities in (44.22)--(44.24) are strict. They therefore persist
on a relative neighborhood of these actual pairs inside the original
domain. This is a nongeometric low-impurity sector for the universal
bound; it is neither a strict competitor nor a new minimizing branch.
The assertion is only realizability and screening, with no rank,
feedback, optimizer-sign or coherence-phase restriction beyond the
displayed actual construction. $\square$

**Mathematical source correspondence 44.6.** The identities
(23.9)--(23.12), the zero-set classification in Lemma 11.2, the actual
optimizer rows, and the scalar-quotient distance formula (23.11) are
reused exactly. Theorem 37.5 supplies only the comparison
$V(13/4)\le G_R$, and Theorem 41.2 supplies monotonicity of the selected
raw value $V$; neither is treated as a premise for the spectral lower
bound. The new content is the fixed-$U$ positive residual $K$, its
population-sensitive two-by-two spectral minimum, the complete equality
propagation, the strict sector, and the displayed low-impurity
realization.

For primary literature overlap, compare Bandeira--Boumal--Singer,
*Tightness of the maximum likelihood semidefinite relaxation for angular
synchronization*, arXiv:1411.3272v3, Lemmas 4.3--4.4 and Section 4.3
([primary HTML](https://arxiv.org/html/1411.3272v3)). Their certificate
has a positive semidefinite Hermitian slack, an annihilation condition,
and a real-diagonal condition for the angular-synchronization feasible
set. Those hypotheses explain the shape of a global spectral certificate,
but the prescribed original distance and variable $F$ here add parameters
for which no uniform slack is supplied by their lemmas. Tangent-space
positivity therefore cannot replace (44.3).

Likewise compare Xia--Wang--Sheu, *S-Lemma with Equality and Its
Applications*, arXiv:1403.2816v3, Theorem 3 and Section 4
([primary HTML](https://arxiv.org/html/1403.2816v3)). Their exactness
result concerns one real quadratic equality with its regularity and
exceptional affine cases. The original problem has four unit-modulus
constraints together with a prescribed joint distance and a variable
effect. No correspondence eliminating those constraints was established
here, so this S-lemma supplies no unclaimed equality theorem for the
present domain. These are bounded correspondence checks, not literature
priority claims.

**Theorem 44.7 (current consumer and exact remaining boundary).** On the
existing all-effect phase certificate (42.31), retain

$$
p_+(r)=1-r,\qquad p_-(r)=r,\qquad
\epsilon=2(r-t_\sigma)
\tag{44.25}
$$

on each already defined admissible effect arc. Every point satisfying

$$
2(r-t_\sigma)\ge\theta\bigl(p_\sigma(r)\bigr)
\tag{44.26}
$$

now has the strict raw-defect conclusion

$$
f(E,U)-N_{\mathrm{geo}}(\xi)>\frac3{16}
$$

through $\xi\le13/4$, whenever that point is realized by the original
same-$U$ arc. Thus (44.26) removes this entire screened subset from the
possible equality or strict-loss search. The complementary arc, including
all zero-amplitude, zero-coherence, singular, population-boundary and
both-sign cases, remains in the exact source certificate.

The universal bound (44.3) and its saturation set (44.4) do not determine
the constrained value envelope on a fixed distance level: equality in
$g=L$ can be incompatible with a prescribed $\rho$, and a constrained
minimum can lie strictly above $L$. The exact alpha and beta, phase
equality sets, exhaustive equality, first globally ordered or exhausted
branches, higher-order determinant-zero alternatives, and all inherited
full-global obligations therefore remain open.

**Proof.** Substitute (44.25) into (44.12), then apply Theorem 44.3 to
every original arc point with $\xi\le13/4$. The retained phase formula
and all endpoint conventions are those of (42.31); no new minimization or
lifting assumption is introduced. The last paragraph follows directly
from the distinction between a universal lower bound and a constrained
level problem, together with the unresolved obligations in (43.8).

The source results used here include singular and mixed effects and the
actual common scalar quotient. The proof never chooses separate
feedbacks for spectral components and never changes the original metric.
$\square$

**Unresolved mathematical obligations 44.8.** The append does not prove
the full preceding-level inequalities on the complementary arcs or beyond
$13/4$. It does not compute exact $\alpha,\beta$, their coincidence or
separation, endpoint inclusion, or exhaustive phase equality. It does not
evaluate the variance-zero lift conditions (42.25), identity or
exhaustion of first globally minimizing branches, determinant-zero
higher-order signs, beyond-four geometric ordering, core-attainment
questions. Those obligations
remain in force together with (43.26).

## 追加锚（本行以下为增补区）

## 45. Strict fixed-feedback purification and global purity through thirteen-fourths

**Definition 45.1 (pure levels and the unchanged effect arcs).** Retain
exactly the original domain $\mathcal K=\operatorname{Dens}_2\times U(4)$,
the ordinary transpose, the joint Frobenius distance (39.1), its two
optimizer signs, and its one common scalar quotient. Keep $g$, $f=g-\kappa\rho$,
$N=N_{\mathrm{geo}}$, $V=N+\kappa\xi$, $\mathcal G_\xi$, and the original
and phase minimizing sets of Definitions 39.1 and 42.1. Put

$$
\begin{aligned}
 R&=13/4,& c_0&=e^2/4,\\
 \mathcal K_{\mathrm p}&=\{(E,U)\in\mathcal K:\operatorname{rank}E=1\},\\
 \mathcal L_{\mathrm p,\xi}
   &=\{X\in\mathcal K_{\mathrm p}:\rho(X)=\xi\},&
 \mathcal P_{\mathrm p,\xi}
   &=\mathcal P_\xi\cap\mathcal K_{\mathrm p},\\
 m_{\mathrm p}(\xi)&=\min_{X\in\mathcal L_{\mathrm p,\xi}}f(X),&
 m_{\mathrm{ph,p}}(\xi)&=\min_{X\in\mathcal P_{\mathrm p,\xi}}f(X).
\end{aligned}
\tag{45.1}
$$

Write $\mathcal A_{\mathrm p,\xi}$ and $\mathcal A_{\mathrm{ph,p},\xi}$
for the respective minimizing sets. For $0<\xi\le R$ these pure levels
are nonempty because they contain $\mathcal G_\xi$. They are compact:
the rank-one condition on a normalized positive two-by-two effect is
$\epsilon(E)=1-\operatorname{Tr}(E^2)=0$, a closed condition. Their
minima are therefore attained, as are the full original and phase
minima in Theorem 35.2 and Definition 42.1.

For an actual $U$, all of $w,A,B,P,Q,u,v,\Delta_\pm,S_\pm,t_\sigma,
J_\sigma,b_\sigma,I_\sigma,Q_\sigma$ retain exactly the definitions
(23.2) and (36.1)--(36.3). Here $v=|Q|$ and $Q_\sigma$ is a real arc
endpoint, distinct from the complex amplitude $Q$. For an admissible
sign define its full effect arc by

$$
 \mathfrak E_\sigma(U,\xi)=
 \left\{\bigl(TF_\sigma(q,z)T^\dagger\bigr)^{\mathsf T}:
       q\in I_\sigma,\quad |z|^2=t_\sigma-q^2\right\},
\tag{45.2}
$$

where $F_\pm(q,z)$ are exactly the two matrices in (36.7). No coherence
phase condition is imposed in (45.2). Equations (36.10)--(36.13) say
that this is precisely the nonempty compact set of original effects
at level $\xi$ for which $\sigma$ attains the original joint distance.
Every point on it has

$$
 \epsilon(E)=2(q-t_\sigma),\qquad
 t_\sigma\le q\le\min\{\sqrt{t_\sigma},J_\sigma\}.
\tag{45.3}
$$

In particular its pure effects have exactly $q=t_\sigma$; a mixed
point has $0<t_\sigma<q<1$. The quantities in this arc always come
from the one fixed whole feedback $U$.

**Lemma 45.2 (crossed-amplitude defect floor at an active sign).** Let
$U\in U(4)$ be actual, let $0<\xi\le R$, and let $\sigma$ be admissible
for its level arc. Then

$$
                       \Delta_{-\sigma}>c_0.
\tag{45.4}
$$

The bound applies to arbitrary actual unitary lifts, including zero
amplitudes and repeated feedback eigenvalues.

*Proof.* Choose any effect in (45.2). The minimizing sign is unique
by Theorem 42.3. Set $x_i=(UU_\sigma^\dagger)_{ii}$,
$S=|\sum_i x_i|=S_\sigma$, and $\mu=\frac14\sum_i x_i$.
Nonnegativity of the effect-distance summand in (39.1) gives
$8-2S\le\xi$, so $S\ge19/8$. Unitarity gives $|x_i|\le1$ and hence

$$
 \sum_{i=1}^4|x_i-\mu|^2
   =\sum_{i=1}^4|x_i|^2-\frac{S^2}{4}
   \le4-\frac{S^2}{4}
   \le\frac{663}{256}<\frac{13}{5}.
\tag{45.5}
$$

The arithmetic mean $\mu$ is only used to center this vector; it is
not a new feedback phase or an additional quotient.
For the positive sign, $x=w$. For the negative sign, the fixed
identity $U_-U_+^\dagger=\operatorname{diag}(1,-1,-i,i)$ gives
$x=(w_1,-w_2,iw_3,-iw_4)$. Consequently (23.2) yields

$$
\begin{array}{c|c|c|c}
 \sigma&\text{crossed amplitude }\sum_i\ell_i x_i
           &\ell&\sum_i|\ell_i|^2\\ \hline
 +&Q&(h,-h,is,-is)&2-h\\
 -&P&(h,-h,-ic,ic)&2+h .
\end{array}
\tag{45.6}
$$

In each row $\sum_i\ell_i=0$, so the amplitude equals
$\sum_i\ell_i(x_i-\mu)$. The finite complex Cauchy--Schwarz inequality
therefore gives

$$
\begin{aligned}
 \sigma=+\quad v^2
   &\le(2-h)\sum_i|x_i-\mu|^2
          <\frac{13}{10}\frac{13}{5}=\frac{169}{50},\\
 \sigma=-\quad u^2
   &\le(2+h)\sum_i|x_i-\mu|^2
          <\frac{11}{4}\frac{13}{5}=\frac{143}{20}.
\end{aligned}
\tag{45.7}
$$

Here $h>7/10$ and $h<3/4$ are among (42.6).
Those same half-angle bounds, with $c>9/10$ and $s>3/8$, give

$$
\begin{aligned}
 e^2=4(h+s)^2&>4(43/40)^2>23/5,\\
 d^2=4(h+c)^2&>4(8/5)^2>10,\\
 e^2&<4(23/20)^2<6,
\end{aligned}
\tag{45.8}
$$

where the last line uses $h<3/4$ and $s<2/5$. Thus for the same
actual feedback as in (45.5)--(45.7),

$$
\begin{aligned}
 \sigma=+\quad
 \Delta_--c_0&=\frac{3e^2}{4}-v^2
       >\frac{69}{20}-\frac{169}{50}=\frac7{100}>0,\\
 \sigma=-\quad
 \Delta_+&=d^2-u^2>10-\frac{143}{20}
                  =\frac{57}{20}>\frac32>c_0.
\end{aligned}
\tag{45.9}
$$

This proves (45.4). Every trace and amplitude in these inequalities
is evaluated on the given $U$; no separately attained extrema have
been combined. The active trace cannot vanish because $S\ge19/8$;
the inactive trace is unrestricted. $\square$

**Lemma 45.3 (no low-defect mixed arc minimum).** For any actual $U$,
any $0<\xi\le R$, and any admissible sign $\sigma$, every mixed effect
minimizing $g(E,U)$ on $\mathfrak E_\sigma(U,\xi)$ has $g(E,U)>c_0$.

*Proof.* Apply the exact arc minimum and phase-equality formulas
(36.5)--(36.7), whose derivation minimizes each individual arc before
taking the minimum over signs. Write $t=t_\sigma$, $b=b_\sigma$,
$\omega=uv$ and $\Lambda=\sqrt{b^2+4\omega^2}$; thus $\Lambda$ is
$R_\sigma$ of (36.4). Suppose a minimizing effect is mixed, so
$0<t<q<1$. It has $q<J_\sigma$: equality would make both original
signs minimizing by (36.11), contrary to Theorem 42.3. That theorem
applies to every point here since its actual original level is
$0<\xi\le R$; equivalently, its proof uses
$\xi+\epsilon\le15/4<\zeta$ and (42.20), including mixed effects.

If $\Lambda=0$, then $b=0$ and $uv=0$. Since $d^2>e^2$,

$$
 u^2-v^2=d^2-e^2>0,
 \qquad v=0,
 \qquad u^2=d^2-e^2,
 \qquad \Delta_+=\Delta_-=e^2.
\tag{45.10}
$$

The exact identity (36.14) is consequently constant with value
$e^2>c_0$ throughout the arc, including every coherence phase.

Suppose $\Lambda>0$. Formula (36.5) gives

$$
 q=\min\{Q_\sigma,\max\{t,q^\circ\}\},\qquad
 q^\circ=\frac{\sqrt t\,(-b)_+}{\Lambda}\le\sqrt t.
\tag{45.11}
$$

Since $q>t$, one has $q^\circ>t$, and hence $b<0$.
The truncation at $J_\sigma$ cannot be active because $q<J_\sigma$;
the other upper endpoint $\sqrt t$ cannot cut off $q^\circ$.
Therefore $q=q^\circ$. The aligning-phase equality in (36.7) and
the nonnegative square roots give, without dividing by $u$ or $v$,

$$
\begin{aligned}
 q&=\frac{\sqrt t(-b)}{\Lambda},&
 |z|=\sqrt{t-q^2}&=\frac{2\omega\sqrt t}{\Lambda},\\
 g(E,U)&=\Delta_\sigma+bq-2\omega\sqrt{t-q^2}
              =\Delta_\sigma-\Lambda\sqrt t.
\end{aligned}
\tag{45.12}
$$

Because $q>t$ and $t>0$, one has $-b>\Lambda\sqrt t$.
Lemma 45.2 now yields

$$
 g(E,U)>\Delta_\sigma+b=\Delta_{-\sigma}>c_0.
\tag{45.13}
$$

If $P=0$ or $Q=0$ and $\Lambda>0$, the same argument is exactly
the affine case of (36.5): a mixed minimum requires $b<0$ and
$q=\sqrt t<J_\sigma$, with $z=0$. Equations (45.12)--(45.13)
still hold. When $\omega>0$ the minimizing phase is the one in
(36.7); if $\omega|z|=0$ its phase condition is vacuous. Thus no
zero-coherence endpoint is lost. An arc with $t=0$ or $t=1$ is a
pure singleton; any other singleton has $Q_\sigma=t$ and is also
pure. The lower endpoint $q=t$ is pure, the possible mixed endpoint
$q=\sqrt t$ has been included, and a sign-truncation endpoint at
$q=J_\sigma$ is excluded by the proved sign separation. This
exhausts all degenerate and truncated arcs. $\square$

**Theorem 45.4 (strict same-feedback, same-level purification below
$c_0$).** Let $(E,U)$ be an original pair with $E$ mixed and
$0<\rho(E,U)=\xi\le R$. If $g(E,U)\le c_0$, there is a normalized
positive semidefinite rank-one effect $\widehat E$ satisfying

$$
\begin{aligned}
 \rho(\widehat E,U)&=\rho(E,U)=\xi,\\
 \rho_\sigma(\widehat E,U)&=\xi<\rho_{-\sigma}(\widehat E,U),\\
 g(\widehat E,U)&<g(E,U),&
 f(\widehat E,U)&<f(E,U),
\end{aligned}
\tag{45.14}
$$

where $\sigma$ is the unique minimizing sign of the input. The actual
whole matrix $U$ is unchanged, and $\widehat E$ is a pure endpoint of
that same sign arc. No uniform positive improvement size is asserted.

*Proof.* The input belongs to $\mathfrak E_\sigma(U,\xi)$. Minimize
$g(\cdot,U)$ on this nonempty compact arc. Its minimum is no larger
than $g(E,U)\le c_0$, so Lemma 45.3 excludes every mixed minimizer.
Every minimizing effect therefore has $q=t=t_\sigma$ by (45.3),
and its coherence has an aligning phase by (36.7). Explicitly one
may choose

$$
\begin{aligned}
 \widehat z&=
 \begin{cases}
  \sqrt{t(1-t)}\,\bar P Q/(uv),&uv>0,\\
  \sqrt{t(1-t)}\,\eta,&uv=0,\quad |\eta|=1,
 \end{cases}\\
 \widehat E&=\bigl(TF_\sigma(t,\widehat z)T^\dagger\bigr)^{\mathsf T}.
\end{aligned}
\tag{45.15}
$$

All allowed choices in (45.15) have that same arc-minimum value.
For a mixed input, (45.3) gives $0<t<1$. The reconstructed matrix has

$$
 \operatorname{Tr}F_\sigma(t,\widehat z)=1,\qquad
 \det F_\sigma(t,\widehat z)=t(1-t)-|\widehat z|^2=0,\qquad
 F_\sigma(t,\widehat z)\succeq0.
\tag{45.16}
$$

Unitary conjugation followed by ordinary transpose preserves positivity,
trace and rank, so this is an actual normalized rank-one original effect.
Moreover $t<q_{\mathrm{input}}<J_\sigma$, so its sign remains strictly
$\sigma$. Equation (36.10), with $t^2+|\widehat z|^2=t$, proves exact
preservation of the original level. Since $U$ is unchanged, the scalar
phases minimizing its distance to either original $U_\pm$ are unchanged
as well. No separate feedback is assigned to an effect component.

If the new value equalled the input value, the old mixed input itself
would attain the arc minimum at a value at most $c_0$, contradicting
Lemma 45.3. The decrease is therefore strict. Subtracting the same
$\kappa\xi$ proves the assertion for $f$. The construction includes
$P=0$, $Q=0$ and zero input coherence, without dividing by a vanishing
amplitude. $\square$

**Theorem 45.5 (all original and phase global minimizers are pure).**
For every $0<\xi\le R$,

$$
\begin{aligned}
 m(\xi)&=m_{\mathrm p}(\xi)=m_{\mathrm{ph}}(\xi)
                                      =m_{\mathrm{ph,p}}(\xi),\\
 \mathcal A_\xi&=\mathcal A_{\mathrm p,\xi}
                                      \subset\mathcal K_{\mathrm p},\\
 \mathcal A_{\mathrm{ph},\xi}
   &=\mathcal A_{\mathrm{ph,p},\xi}
     =\mathcal A_\xi\cap\mathcal P_\xi.
\end{aligned}
\tag{45.17}
$$

These are equalities of attained values and of the minimizing sets in
their stated domains, not a classification of those pure sets.

*Proof.* Reuse the delivered geometric comparison in the proof of
Theorem 44.3, namely (44.19) together with its stated consequence
throughout this interval:

$$
 m(\xi)+\kappa\xi\le V(\xi)<c_0-\frac3{16},\qquad
 m_{\mathrm{ph}}(\xi)+\kappa\xi\le V(\xi)<c_0-\frac3{16}.
\tag{45.18}
$$

The first inequalities use $\mathcal G_\xi$ as actual feasible pairs
in both domains. The comparison concerns the selected value $V$;
no assumption $m=N$ or $\xi<\beta$ enters it.
Original minima are attained by Theorem 35.2. A mixed original global
minimizer would have $g<c_0$ by (45.18), and Theorem 45.4 would strictly
improve it at exactly the same original level. This is impossible.
The phase level is compact and nonempty by Definition 42.1. A mixed
phase global minimizer has the same contradiction, because Theorem
45.4 never changes its phase feedback $U$.

Restriction to the pure subsets can consequently remove no minimizer.
Set inclusion gives the equal values and equal minimizing sets in
each domain. The cross-domain value equality and intersection identity
are exactly (42.24). This proves (45.17) without using prefix purity.
$\square$

**Corollary 45.6 (pure boundary contacts and pure right branches).**
At each of $b=\alpha$ and $b=\beta$, every original and phase global
minimizer is pure. Every global minimizing branch whose positive levels
remain in $(0,R]$ is pointwise pure. In particular the actual analytic
phase branches and their attained boundary limits in (42.32) are pure
on their sufficiently short right intervals. Separated contact at
$\beta$ and competing global branches inside this interval can therefore
only be pure.

*Proof.* Theorem 42.2 gives $0<\alpha\le\beta<R$. Apply Theorem 45.5
to these boundary levels and to every level of the branches. The
endpoint limit in (42.32) is already an attained boundary global
minimizer by Corollary 42.6, so it is pure as well. The mixed-global-contact
implications of Corollaries 41.5 and 42.6 retain their conditional
validity; their mixed-minimizer antecedents have no instance at these
levels. This conclusion neither identifies a pure contact nor orders
a competing branch. $\square$

**Theorem 45.7 (exact pure phase value and geometric-equality
certificate).** For $0<\xi\le R$, $w\in\mathbb T^4$ and an admissible
sign $\sigma$, put

$$
 C_\sigma(w,\xi)=\Delta_\sigma(w)+b_\sigma(w)t_\sigma(w,\xi)
       -2u(w)v(w)\sqrt{t_\sigma(w,\xi)(1-t_\sigma(w,\xi))}.
\tag{45.19}
$$

This is the minimum over the coherence phases of the pure endpoint,
not the minimum over the whole effect arc. Define its full aligning
endpoint set at a real raw value $a$ by

$$
\begin{aligned}
 \mathcal E_\xi(a)=\bigcup_{\substack{w\in\mathbb T^4,\ \sigma\ \mathrm{admissible}\\
                                     C_\sigma(w,\xi)=a}}
 \biggl\{\Bigl(\bigl(TF_\sigma(t_\sigma,z)T^\dagger\bigr)^{\mathsf T},
                            \operatorname{diag}(w)U_+\Bigr):\ &
 |z|^2=t_\sigma(1-t_\sigma),\\[-2pt]
 &\operatorname{Re}(Pz\bar Q)=uv|z|\biggr\}.
\end{aligned}
\tag{45.20}
$$

Every actual common scalar representative is retained. If $uv|z|=0$,
all phases satisfying the modulus condition are allowed. Then

$$
\begin{aligned}
 a_\xi&:=m(\xi)+\kappa\xi
       =\min_{\substack{w\in\mathbb T^4,\ \sigma\ \mathrm{admissible}}}
                                      C_\sigma(w,\xi),\\
 \mathcal A_{\mathrm{ph},\xi}
       &=\mathcal A_{\mathrm{ph,p},\xi}=\mathcal E_\xi(a_\xi).
\end{aligned}
\tag{45.21}
$$

The minimum displayed here is attained. The original value certificate
is precisely the pure phase lower inequality

$$
 m(\xi)=N(\xi)
 \quad\Longleftrightarrow\quad
 C_\sigma(w,\xi)\ge V(\xi)
 \quad\text{for every }w\in\mathbb T^4
                         \text{ and every admissible }\sigma.
\tag{45.22}
$$

The exhaustive geometric-equality certificate requires both this
inequality and its complete equality set:

$$
\begin{aligned}
 \mathcal A_\xi=\mathcal G_\xi
 \quad\Longleftrightarrow\quad
 \mathcal A_{\mathrm{ph,p},\xi}=\mathcal G_\xi
 \quad\Longleftrightarrow\quad
 \bigl[&C_\sigma(w,\xi)\ge V(\xi)
                  \text{ for every admissible }(w,\sigma),\\
       &\mathcal E_\xi(V(\xi))=\mathcal G_\xi\bigr].
\end{aligned}
\tag{45.23}
$$

For an arbitrary original pure pair $X=(E,U)$ with $\rho(X)=\xi$, write
$F=T^\dagger E^{\mathsf T}T=\psi\psi^\dagger$ with $\|\psi\|=1$.
Its exact original minimizing-lift condition remains, for any
spectral/Birkhoff decomposition of Theorem 42.3,

$$
 X\in\mathcal A_\xi
 \quad\Longleftrightarrow\quad
 \left\{\begin{array}{ll}
  (E,U_j)\in\mathcal E_\xi(a_\xi)&\text{for every positive-weight }j,\\
  (a_j-a)\psi=0&\text{for every positive-weight }j.
 \end{array}\right.
\tag{45.24}
$$

It is sufficient for one such decomposition to satisfy these conditions;
when $X$ minimizes, every such decomposition satisfies them. Outside
exhaustive geometric equality, (45.24) does not assert that $U$ is phase.

*Proof.* Every pure original effect at an admissible sign has
$q=t_\sigma$ by (45.3). Substitution in the exact same-feedback identity
(36.14) gives its lower value (45.19), attained exactly by the phases
in (45.20). For $uv=0$ the identity is independent of the coherence
phase; for $t_\sigma=0$ or $1$ its coherence is zero. Thus the statement
also includes all pure singletons and zero amplitudes. Every
$w\in\mathbb T^4$ has the explicit whole unitary realization
$\operatorname{diag}(w)U_+$, and every endpoint constructed in (45.20)
has the exact original distance by (36.10)--(36.12). No relaxation of
phase feasibility, rank or sign is being minimized.

Theorem 45.5 makes the full original minimum equal to this pure phase
minimum. Compact attainment from Definition 45.1, and the exact endpoint
phase equality just proved, give both lines of (45.21) and attainment
of its right side. The selected geometric pairs attain raw value
$V(\xi)$, so $a_\xi\le V(\xi)$. Formula (45.21) now proves (45.22)
in both directions. Under that lower inequality, equality of a pure
phase input to $V$ forces both $C_\sigma=V$ and the aligning phase
condition. Hence its entire minimizing set is exactly
$\mathcal E_\xi(V)$, proving the last equivalence in (45.23).
The first equivalence is (42.26) with the phase purity of Theorem 45.5.
The equality-set condition by itself is not a lower bound and cannot
replace the first condition in the brackets.

Finally apply (42.25). Since $F$ is a rank-one projection,
$F^{1/2}=F=\psi\psi^\dagger$, and
$(a_j-a)F^{1/2}=0$ is equivalent to $(a_j-a)\psi=0$.
Insert the phase minimizing set (45.21) to obtain (45.24), with the
same necessity for every decomposition and sufficiency for one as in
Theorem 42.4. This is a condition on the actual original lift, not an
identification of every pure lift with a diagonal feedback. $\square$

**Corollary 45.8 (pure phase bad sets retain the original first
boundaries).** Define subsets of $(0,R]$ by

$$
\begin{aligned}
 \mathcal B_{\mathrm{ph,p}}
  &=\{\xi:\exists X\in\mathcal P_{\mathrm p,\xi}\setminus\mathcal G_\xi,
                                            \ f(X)\le N(\xi)\},\\
 \mathcal S_{\mathrm{ph,p}}
  &=\{\xi:\min_{w\in\mathbb T^4,\ \sigma\ \mathrm{admissible}}
                                  C_\sigma(w,\xi)<V(\xi)\}.
\end{aligned}
\tag{45.25}
$$

Then

$$
\begin{aligned}
 \mathcal B\cap(0,R]&=\mathcal B_{\mathrm{ph,p}},&
 \mathcal S\cap(0,R]&=\mathcal S_{\mathrm{ph,p}},\\
 \alpha&=\inf\mathcal B_{\mathrm{ph,p}},&
 \beta&=\inf\mathcal S_{\mathrm{ph,p}}.
\end{aligned}
\tag{45.26}
$$

*Proof.* Strict loss is exactly the strict inequality in (45.21),
which proves the assertion for $\mathcal S$. If the common value is
below $N$, an attained pure phase global minimizer is outside
$\mathcal G_\xi$ and witnesses $\mathcal B_{\mathrm{ph,p}}$.
If the value is $N$, a bad-set witness in either domain is exactly
an extra global minimizer; (45.23) identifies failure of exhaustive
geometric equality in the two domains. Conversely every witness in
$\mathcal B_{\mathrm{ph,p}}$ is an original witness by inclusion.
This proves equality of the bad sets without asserting pointwise
transport of every nonglobal witness. Both original boundaries lie
strictly inside $(0,R)$ by (42.3), so restriction to this interval
does not change their infima. $\square$

**Mathematical source correspondence 45.9.** The objects and exact
ordinary-transpose identities are (23.2), (23.9)--(23.12) and (39.1).
The individual arc minimizers, all scalar truncations, aligning phases
and impurity formula are (36.5)--(36.7) and (36.10)--(36.16).
Theorem 42.3 supplies sign separation on the full stated interval,
including all mixed effects; Theorems 35.2 and 42.4 supply compact
attainment and the phase value/equality transport. The selected
comparison below $c_0-3/16$ is the existing conclusion of Theorem 44.3,
using (44.19) and Theorem 41.2. Its witness and scalar calculation
are not additional hypotheses about a globally minimizing branch.

The finite Cauchy--Schwarz inequality is a standard intermediate tool;
compare [NIST DLMF, Section 1.7(i), (1.7.1)](https://dlmf.nist.gov/1.7.E1).
For the complex sum in Lemma 45.2, the triangle inequality followed
by that real finite-sum inequality with
$a_i=|\ell_i|$, $b_i=|x_i-\mu|$ gives exactly the squared-norm bound
used in (45.7). The zero-sum coefficient rows permit centering; they
supply no new independent realization assumption. The compact-minimum
argument is the finite-dimensional extreme-value theorem on the actual
closed level sets. No new spectral-diagonal realization theorem is
needed: the feedback remains fixed in Theorem 45.4, and phase endpoints
have the explicit unitary realization in (45.20).

The fixed-record deductions are the crossed-amplitude floor, the
exclusion of low mixed arc minima, strict same-level purification under
$g\le c_0$, and its global purity and pure phase certificate consequences.
Theorem 36.3 proves earlier same-level purification only under its
stated sign or small-level hypotheses; Theorem 41.4 proves purity on
an already value-preserving prefix. Neither is used to certify a
prefix here. Proposition 40.5's failure of universal same-feedback
purification at arbitrary defect remains valid. The present argument
does not assert $g>c_0$ for every mixed input: Lemma 45.3 applies to
mixed arc minimizers, whereas a mixed input with $g\le c_0$ has the
strict improvement in Theorem 45.4. The population-sensitive pointwise
screen of Theorem 44.3 remains useful with its own hypotheses. These
are constrained-optimization deductions for the fixed record, with no
claim of literature-wide originality.

**Unresolved mathematical obligations 45.10 (complete pure phase
ordering and actual equality).** On every level of a proposed preceding
value prefix inside $(0,R]$, the remaining universal inequality is
(45.22), for every actual $w\in\mathbb T^4$ and both admissible signs.
For a proposed exhaustive-equality prefix, its additional obligation
is the complete endpoint equality classification in (45.23), with
all zero-amplitude and zero-coherence cases retained. Equations
(45.19)--(45.26) provide an equivalent certificate and boundary
problem, not its evaluation.

The exact infima $\alpha,\beta$, whether they coincide, the inclusion
or exclusion of the exhaustive-equality endpoint, and any earlier
pure equality ties remain undetermined. Every first competing global
branch inside this interval must be pure, but its actual identity,
ordering against all other pure branches, exhaustion, boundary limits
and full attainment/equality sets are still required. Pure coalescence
and separated pure contact are both retained. Determinant zero is only
the necessary condition in the scopes of Section 43; its higher-order
and global consequences and possible simultaneous separated pure
contact remain unresolved.

The rank-one variance-zero original lifts in (45.24) still require
complete evaluation. Purity alone supplies no classification of
nonphase original minimizing lifts. The sufficient phase-transport
condition beyond $R$ retains exactly its domain in Section 42;
no purification or pure phase reduction outside $(0,R]$ follows here.
The inherited beyond-four geometric ordering and core-attainment
obligations remain. The normalized-effect pair-domain conclusions
above do not assert a whole-POVM or native-acquisition result.

## 追加锚（本行以下为增补区）
## 46. Global coherent cone remainder and the exact two-sign canonical-slice comparison

This section keeps the original record, ordinary transpose, one common feedback
scalar, and the joint distance

$$
 \rho(E,U)=\min_{\sigma\in\{+,-\}}
 \min_{|\lambda|=1}
 \left(\|E-E_\sigma\|_{\mathrm F}^{2}
       +\|U-\lambda U_\sigma\|_{\mathrm F}^{2}\right).
\tag{46.1}
$$

Write $g$ for the original defect, $f=g-\kappa\rho$, and
$V(\xi)=N_{\mathrm{geo}}(\xi)+\kappa\xi$ for the existing selected
geometric value. The fixed constants are $h=1/\sqrt2$,
$c=\cos(\pi/8)$, $s=\sin(\pi/8)$, $d=2(h+c)$ and $e=2(h+s)$;
$T=(b_+\ b_-)$ is the source certificate basis. Write
$R_\star=13/4$ for the established level cutoff, reserving $R$ below
for a recovery half-modulus. No new quotient or independent feedback
is introduced.

**Definition 46.1 (the two active rows and the attained phase triangle).**
Fix an optimizer sign $\sigma$. Relative to $U_\sigma$, put
$v=\operatorname{diag}(UU_\sigma^\dagger)$. The fixed pair order and the
main and crossed recoveries are

$$
\begin{array}{c|c|c|c|c|c|c}
 \sigma&J&K&M&N&(a,b,\ell,m)&(K_\sigma,K_{-\sigma})\\ \hline
 +&(1,2)&(3,4)&P&Q&(h,c,h,s)&(d,e)\\
 -&(3,4)&(1,2)&Q&P&(s,h,c,h)&(e,d).
\end{array}
\tag{46.2}
$$

Here the source recoveries are

$$
\begin{aligned}
 P(w)&=h(w_1+w_2)+c(w_3+w_4),\\
 Q(w)&=h(w_1-w_2)+is(w_3-w_4),
\end{aligned}
\tag{46.3}
$$

with $w=\operatorname{diag}(UU_+^\dagger)$. Thus, with indices
kept in the original coordinate order,

$$
\begin{aligned}
M_+(v)&=h(v_1+v_2)+c(v_3+v_4),
&N_+(v)&=h(v_1-v_2)+is(v_3-v_4),\\
M_-(v)&=h(v_1+v_2)+s(v_3+v_4),
&N_-(v)&=h(v_1-v_2)-ic(v_3-v_4).
\end{aligned}
\tag{46.4}
$$

The second row follows from $U_-U_+^\dagger=\operatorname{diag}(1,-1,-i,i)$;
the labels $J,K$ specify which fixed pair is active while all
coordinate indices remain unchanged. In both rows $0<a<b$, $\ell>m>0$, and $k=b-a$.

Let $q$ be the population away from the active optimizer and put $p=1-q$.
The pure effects in the two rows are represented in the $T=(b_+\ b_-)$ basis
by

$$
 \beta_+^\phi=\begin{pmatrix}\sqrt p\\ e^{i\phi}\sqrt q\end{pmatrix},
 \qquad
 \beta_-^\phi=\begin{pmatrix}e^{i\phi}\sqrt q\\ \sqrt p\end{pmatrix},
 \qquad
 E=(T\beta_\sigma^\phi(\beta_\sigma^\phi)^\dagger T^\dagger)^{\mathsf T}.
\tag{46.5}
$$

Every $\phi$ is allowed. Define the energy, with a notation separate from the
determinant below, by

$$
 \mathsf E_\sigma(q)=K_\sigma^2p+K_{-\sigma}^2q.
\tag{46.6}
$$

For $0<x<1$, let $y=\sqrt{1-x^2}$, $L=1+x$, and impose the active complex
trace modulus

$$
 \left|\operatorname{Tr}(UU_\sigma^\dagger)\right|=2L.
\tag{46.7}
$$

The pure distance to this sign branch is then

$$
 \xi=8-4L+2q=4(1-x)+2q.
\tag{46.8}
$$

All conclusions below concerning the true original distance and original
equality lifts use $0<\xi\le R_\star$. The two-sign budget
(42.17)--(42.20) implies that a sign branch equal to $\xi$ in this range
is the unique minimizing original sign. In particular (46.8) is then
$\rho(E,U)$, and $x=1-\xi/4+q/2\ge3/16>0$. The phase-triangle
identities and the fixed-branch comparison themselves hold for every
$0<x<1$ and $q\in[0,1]$.

For the phase calculation restrict now to actual phase feedbacks
$U=\operatorname{diag}(v)U_\sigma$, with $|v_j|=1$ for every $j$.
For arbitrary actual $U$, the passage to these phase calculations is
the same-effect, same-complex-trace transport used in Corollary 46.5.
Set

$$
 X=\frac14\left|\sum_{j\in J}v_j\right|^2,
 \qquad
 Y=\frac14\left|\sum_{j\in K}v_j\right|^2.
\tag{46.9}
$$

The actually attained two-pair domain is

$$
 0\le X,Y\le1,
 \qquad \sqrt X+\sqrt Y\ge L.
\tag{46.10}
$$

For a point in this domain define

$$
\begin{aligned}
 Z&=\frac{L^2-X-Y}{2\sqrt{XY}},
&F&=\sqrt{(1-X)(1-Y)}\sqrt{1-Z^2},\\
 R_0&=ax+b,&C_0&=\ell y,\\
 R&=\sqrt{a^2X+b^2Y+ab(L^2-X-Y)},\\
 C&=\sqrt{\ell^2(1-X)+m^2(1-Y)+2\ell mF},\\
 \Gamma&=\sqrt p\,R+\sqrt q\,C,&
 \Gamma_0&=\sqrt p\,R_0+\sqrt q\,C_0.
\end{aligned}
\tag{46.11}
$$

The lower bounds in (46.10) imply $X,Y>0$ when $0<x<1$, so $Z$ is defined.
The quantities $R,C$ are half-moduli of the main and crossed recoveries. In
particular, $C$ is the largest crossed half-modulus attainable with these same
pair lengths and the same trace. It is not obtained by optimizing the two
recoveries independently.

Use the cone coordinates

$$
 A_c=X-x^2,\qquad B_c=1-Y,\qquad H_c=A_c-xB_c,\qquad
 K_c=\frac{\sqrt L\,y}{x}.
\tag{46.12}
$$

These are distinct from the source feedback moduli $A(w)$ and $B(w)$. Put

$$
\begin{aligned}
 \mu&=\frac12\left(\frac{ak\sqrt p}{R_0}+\frac{\ell\sqrt q}{y}\right)>0,\\
 \nu&=\frac12\left(k\sqrt p+
       \frac{(\ell^2x-m^2)\sqrt q}{\ell y}\right),\\
 t_c&=\frac{m\sqrt q\sqrt L}{x},\\
 \mathfrak D_\sigma(x,q)&=\frac{4\mu\nu x^2}{L}-m^2q.
\end{aligned}
\tag{46.13}
$$

Equivalently, with $L_a=2\mu x^2/L$ and $L_b=2\nu$,
$\mathfrak D_\sigma=L_aL_b-m^2q$. On the positive row this is exactly the
local determinant $\mathscr D$ in (36.43), after $p=1-q$; the new assertion
below is global on (46.10), rather than a local second-variation test.

**Lemma 46.2 (actual pair reconstruction and the coupled triangle).** Every
point of (46.10) is attained by a whole phase feedback, and every whole phase
feedback with (46.7) gives a point of (46.10). More precisely, write
$r=\sqrt X$, $z=\sqrt Y$. There are phases $\alpha,\beta$ and signs
$\varepsilon_1,\varepsilon_2\in\{\pm1\}$ such that, in the fixed pair order,

$$
\begin{aligned}
(v_j)_{j\in J}
 &=e^{i\alpha}\bigl(r+i\varepsilon_1\sqrt{1-X},
                         r-i\varepsilon_1\sqrt{1-X}\bigr),\\
(v_j)_{j\in K}
 &=e^{i\beta}\bigl(z+i\varepsilon_2\sqrt{1-Y},
                         z-i\varepsilon_2\sqrt{1-Y}\bigr),
\end{aligned}
\tag{46.14}
$$

and

$$
 \cos(\alpha-\beta)=Z.
\tag{46.15}
$$

There remains one arbitrary common scalar multiplying all four entries.
For these pairs the largest crossed modulus is $2C$, and it is attained by
choosing $\varepsilon_1\varepsilon_2$ to have the sign of
$\sin(\alpha-\beta)$; if that sine vanishes either product is allowed.

*Proof.* Since $r,z\le1$ and $r+z\ge1+x$, each of $r,z$ is at least $x$.
Also $(1-r)(1-z)\ge0$ gives $rz\ge r+z-1\ge x$, hence
$XY\ge x^2$. The trace equation for the two pair sums is

$$
 L^2=X+Y+2\sqrt{XY}\cos(\alpha-\beta),
\tag{46.16}
$$

which proves (46.15) and the necessity of (46.10). Conversely,
(46.10) gives $X,Y\in[x^2,1]$ and $r+z\ge L$, while
$|r-z|\le1<L$. These two triangle inequalities give $|Z|\le1$
and hence the two pairs in (46.14);
taking a cosine with value $Z$ realizes the trace. This proves exact
attainment, including the boundary. Expanding (46.4) on (46.14) gives
$|M|=2R$ and

$$
 \frac{|N|^2}{4}=\ell^2(1-X)+m^2(1-Y)
 +2\ell m\varepsilon_1\varepsilon_2
       \sqrt{(1-X)(1-Y)}\sin(\alpha-\beta).
\tag{46.17}
$$

The stated orientation realizes $C$ and no larger value is possible. The
construction is a single whole feedback, so no independently chosen pair or
column has been introduced. $\square$

**Theorem 46.3 (global coherent cone inequality and the exact five-term
remainder).** On all of the attained triangle (46.10),

$$
\begin{aligned}
 \Delta&:=4XY-(L^2-X-Y)^2
       =4LH_c-(A_c+B_c)^2,\\
 F^2&=\frac{(1-X)B_c\Delta}{4XY},\\
 0&\le F\le K_c\sqrt{B_cH_c}.
\end{aligned}
\tag{46.18}
$$

Equality in the last inequality holds exactly when $B_c=0$; it is
strict whenever $B_c>0$. On the same entire triangle,

$$
\boxed{\begin{aligned}
 \Gamma_0-\Gamma={}&
 \mu\left(\sqrt{H_c}-\frac{t_c\sqrt{B_c}}{2\mu}\right)^2
 +\frac{L\mathfrak D_\sigma(x,q)}{4\mu x^2}B_c\\
 &+\frac{\sqrt q\,\ell m}{C_0}
       \left(K_c\sqrt{B_cH_c}-F\right)\\
 &+\frac{\sqrt p}{2R_0}(R-R_0)^2
 +\frac{\sqrt q}{2C_0}(C-C_0)^2 .
\end{aligned}}
\tag{46.19}
$$

This identity is valid for $q=0$ and $q=1$, and when $C=0$.
Its denominators use the positive fixed slice quantities
$x,y,R_0,C_0,\mu$; the cone identity additionally uses $XY\ge x^2>0$.
Here $R_0=ax+b>0$, $C_0=\ell y>0$, and $\mu>0$ even at
$q=0$ or $q=1$, since $a,k,\ell>0$ and $p+q=1$.

*Proof.* Substitution of $X=x^2+A_c$, $Y=1-B_c$ into the first expression
in (46.18) gives the second expression. Since $\Delta\ge0$ on the attained
triangle, $H_c\ge0$. From (46.12), $1-X\le y^2$ and $XY\ge x^2$; hence

$$
 F^2=\frac{(1-X)B_c\Delta}{4XY}
 \le\frac{y^2}{x^2}B_cLH_c=K_c^2B_cH_c.
\tag{46.20}
$$

If $B_c>0$, then $A_c+B_c>0$ and (46.18) gives $H_c>0$ and
$\Delta<4LH_c$. If $X<1$ the preceding estimates are strict. If $X=1$,
then $F=0$ whereas $K_c\sqrt{B_cH_c}>0$. Thus the final inequality is
strict on every such point, including repeated-pair and aligned-center
boundaries.

The same trace equation gives

$$
 R^2=R_0^2-akA_c-bkB_c,\qquad
 C^2=C_0^2-\ell^2A_c+m^2B_c+2\ell mF.
\tag{46.21}
$$

For $z\ge0$ and $z_0>0$,

$$
 z_0-z=-\frac{z^2-z_0^2}{2z_0}
       +\frac{(z-z_0)^2}{2z_0}.
\tag{46.22}
$$

Apply (46.22) to $R,R_0$ and $C,C_0$, with weights $\sqrt p,\sqrt q$.
After substituting $A_c=H_c+xB_c$, the linear part is

$$
 \mu H_c+\nu B_c-\frac{\sqrt q\,\ell m}{C_0}F.
\tag{46.23}
$$

Since $\sqrt q\,\ell mK_c/C_0=t_c$, completing the square in (46.23) gives

$$
 \mu H_c+\nu B_c-t_c\sqrt{B_cH_c}
 =\mu\left(\sqrt{H_c}-\frac{t_c\sqrt{B_c}}{2\mu}\right)^2
  +\frac{L\mathfrak D_\sigma(x,q)}{4\mu x^2}B_c.
\tag{46.24}
$$

Together with the two root remainders this is (46.19). No division by
$q,p,C$, a variable recovery amplitude, a coherence or a determinant
was made. $\square$

**Theorem 46.4 (necessary and sufficient canonical comparison in both signs).**
For fixed $\sigma$, $0<x<1$ and $q\in[0,1]$, define

$$
 G_\sigma^{\mathrm{can}}(x,q)
   =\mathsf E_\sigma(q)-4\Gamma_0^2.
\tag{46.25}
$$

Then the canonical corner $(X,Y)=(x^2,1)$ is a minimum of the complete
pure phase slice with (46.7) and population $q$ if and only if

$$
                 \mathfrak D_\sigma(x,q)\ge0.
\tag{46.26}
$$

If (46.26) holds, every pure phase pair in that slice satisfies

$$
                   g(E,U)\ge G_\sigma^{\mathrm{can}}(x,q),
\tag{46.27}
$$

and equality holds exactly at the canonical pairs

$$
\begin{array}{c|c|c}
\sigma&v_\sigma^\tau&\beta_\sigma^\tau\\ \hline
+&(x+\tau iy,x-\tau iy,1,1)&(\sqrt p,-\tau i\sqrt q)\\
-&(1,1,x+\tau iy,x-\tau iy)&(\tau\sqrt q,\sqrt p),
\end{array}
\qquad \tau\in\{\pm1\},
\tag{46.28}
$$

up to the one common scalar. This equality statement is unchanged when the
determinant is zero. For $\mathfrak D_\sigma(x,q)<0$, actual pure phase pairs
with the same $x,q$ and sign-branch distance have strictly smaller $g$
than (46.25). When $0<\xi\le R_\star$, that sign is active and
these are strict competitors at the same true original distance.

*Proof.* By (46.17), the aligned pure recovery is
$\chi=\sqrt p\,M+e^{i\phi}\sqrt q\,N$, and
$|\chi|\le2\Gamma$. Every point of the triangle, including the value $2C$,
is attained by one whole feedback and a phase $\phi$ aligning the two terms;
if a weighted term is zero, there is no phase condition. The exact
same-feedback identity (23.12) therefore gives
$g=\mathsf E_\sigma(q)-|\chi|^2$ and the lower estimate in (46.27).
The sign-branch distance is (46.8). Whenever $0<\xi\le R_\star$,
(42.17)--(42.20) makes the other original sign strictly larger, so
this is also the true joint distance.

If $\mathfrak D_\sigma\ge0$, every term in (46.19) is nonnegative, hence
$\Gamma\le\Gamma_0$. If $q>0$ and $B_c>0$, the third term is strictly
positive by (46.18). If $B_c=0$ and $A_c>0$, then (46.21) gives
$C^2<C_0^2$ and the last square is positive. Thus for $q>0$ equality
forces $A_c=B_c=0$. For $q=0$, $t_c=0$, $\nu=k/2>0$, and the
unsquared linear form in (46.23) forces $H_c=B_c=0$, hence $A_c=0$. At
the corner, on the positive row $M=2\lambda R_0$ and
$N=2\tau i\lambda C_0$, while on the negative row
$M=2\lambda R_0$ and $N=2\tau\lambda C_0$. Aligning the two
weighted terms gives exactly (46.28). If $q=0$ or $q=1$, the unused phase
represents the same singleton effect; zero recovery amplitudes likewise impose
no phase condition. This proves necessity and sufficiency and the complete
phase kernel, including determinant zero.

For the converse, $\mathfrak D_\sigma<0$ implies $q>0$. Put
$d_0=(t_c/(2\mu))^2>0$. For sufficiently small
$\varepsilon>0$, set

$$
 B_c=\varepsilon,\qquad H_c=d_0\varepsilon,\qquad
 A_c=(x+d_0)\varepsilon.
\tag{46.29}
$$

Then $X=x^2+A_c$, $Y=1-B_c$ lie in $(0,1)$ and

$$
 \Delta=4Ld_0\varepsilon-(1+x+d_0)^2\varepsilon^2>0.
\tag{46.30}
$$

Thus (46.29) is an actual interior triangle family. From (46.18),
$F=K_c\sqrt{d_0}\varepsilon+O(\varepsilon^2)$; substituting in (46.19)
gives

$$
 \Gamma-\Gamma_0
 =\left(\frac{t_c^2}{4\mu}-\nu\right)\varepsilon
   +O(\varepsilon^2)
 =-\frac{L\mathfrak D_\sigma(x,q)}{4\mu x^2}\varepsilon
   +O(\varepsilon^2)>0
\tag{46.31}
$$

for all sufficiently small nonzero $\varepsilon$. The reconstruction in
Lemma 46.2 and the aligning phase give one actual whole unitary and one pure
effect at the unchanged branch distance, which is the true original
distance when $0<\xi\le R_\star$. Hence its $g$ is strictly smaller.
For the positive interior-population sector with (36.42), the local
same-distance direction already present in Theorem 36.5 is recovered
as the local part of this construction. The global contribution here is
(46.18)--(46.24); the positive local instability is the cited result. $\square$

**Corollary 46.5 (all actual original equality lifts in the nonnegative
slices).** Suppose $0<\xi\le R_\star$, the active sign is $\sigma$, and
$\mathfrak D_\sigma(x,q)\ge0$. The lower bound (46.27) and its equality set
hold for every actual $U\in U(4)$ with the stated pure effect, active trace
and distance. The complete original equality lifts are as follows.

1. If $0<q<1$, the two effects in (46.28) are distinct. A source42
spectral/Birkhoff decomposition of the given $U$ has the same effect, the same
complex active trace and positive weights. Equality in the source42 identity
(42.16) forces every positive-weight phase replacement to be one of the same
canonical orientation. The effect selects one $\tau$, and the nonzero trace
$2L\lambda$ fixes the same common scalar in every replacement. Their averaged
diagonal therefore has four entries of modulus one. Row norms of the actual
unitary $UU_\sigma^\dagger$ force all off-diagonal entries to vanish, so

$$
 U=\lambda\operatorname{diag}(v_\sigma^\tau)U_\sigma.
\tag{46.32}
$$

2. If $q=1$, the two orientations represent the same singleton effect, but
their nonzero scalar recoveries are opposite: they are
$2\tau i\ell y\lambda$ on the positive row and $2\tau\ell y\lambda$ on
the negative row. The variance term in (42.16) permits only one orientation
with positive weight. The same row-norm argument gives (46.32), with either
orientation allowed for this singleton effect.

3. If $q=0$, the equality family is larger. In the fixed pair order of
(46.2), every equality lift and only an equality lift has

$$
 UU_\sigma^\dagger=\lambda\,(W_2\oplus I_2),
 \qquad W_2\in U(2),\qquad \operatorname{Tr}W_2=2x.
\tag{46.33}
$$

Here $W_2$ acts on the active pair $J$ and $I_2$ on $K$. In the original
coordinate order this is $\lambda(W_2\oplus I_2)$ for $\sigma=+$ and
$\lambda(I_2\oplus W_2)$ for $\sigma=-$; the fixed pair order in (46.2)
only records which block is active. Equivalently,

$$
 W_2=Z_2\begin{pmatrix}x+iy&0\\0&x-iy\end{pmatrix}Z_2^\dagger,
 \qquad Z_2\in U(2).
\tag{46.34}
$$

Indeed the two entries on $K$ are $\lambda$ in every phase replacement,
so unitarity isolates that two-dimensional block. Their active trace is
$2x\lambda$, giving (46.33). The two unit eigenvalues of $W_2$ have positive real
sum $2x$, so they are $x+iy$ and $x-iy$; the unitary spectral theorem
gives exactly (46.34). Conversely (46.33) has the required active
trace and main recovery, and therefore attains (46.27). This is the required
larger $q=0$ block lift; it is a fixed-slice equality family, not an assertion
that all such points minimize the unrestricted level.

*Proof.* Theorem 42.3 supplies actual phase replacements with the same complex
trace, same effect, same active sign and the exact variance identity. Apply
Theorem 46.4 to each replacement. Equality in the weighted sum is equivalent
to equality in every positive-weight phase term and to zero variance. The
three cases above then follow from the displayed recoveries and the unitary
row norms. Conversely, the listed matrices have the same trace and the same
recovery data, so the original formula (23.12) and the active distance formula
(23.11) give equality. The argument retains singular effects, zero coherence,
zero recoveries, repeated eigenvalues and nonunique Birkhoff decompositions in
the source transport; no phase formula is applied directly to a nonphase
unitary diagonal. $\square$

**Theorem 46.6 (positive-sign whole-class exclusion and separated-contact
consequence).** At a fixed $0<\xi\le R_\star$, the pure positive-active population
range is

$$
 0\le q\le\min\{1,\xi/2\},\qquad
 x=1-\frac{\xi}{4}+\frac q2.
\tag{46.35}
$$

For $0<x<1$, the canonical value in (46.25) is the positive geometric
scalar value with $\delta=2(1-x)$ and $q=\xi/2-\delta$. The existing scalar
ordering of Theorem 37.5 gives

$$
 G_+^{\mathrm{can}}(x,q)\ge V(\xi),
\tag{46.36}
$$

with equality only at the selected geometric population. If $x=1$ the
slice is treated directly: an actual unitary with active trace modulus four
is $\lambda I_4$ relative to $U_\sigma$, so

$$
 \xi=2q,\qquad g=K_{-\sigma}^2q
\tag{46.37}
$$

for every relative coherence phase. The other sign distance is
$8+2p>2q$, so these are the true original distances for both signs.
At $q=0$ this is the original optimizer at distance zero.
The positive scalar endpoint in (46.37)
is strictly above the unique interior value $V(\xi)$ at every feasible positive
level. Consequently, every nongeometric pure positive-active original pair
with $g\le V(\xi)$ (equivalently $f\le N_{\mathrm{geo}}(\xi)$) satisfies

$$
                 0<x<1,\qquad \mathfrak D_+(x,q)<0.
\tag{46.38}
$$

All pure original pairs in the positive slices with
$\mathfrak D_+\ge0$ obey $g\ge V(\xi)$. Equality to $V(\xi)$
requires the unique selected population of Theorem 37.5 and is exactly
$\mathcal G_\xi$, the selected $0<q<1$ part of Corollary 46.5.
By Theorem 45.5 every original global minimizer through $R_\star$ is
pure, so these slice conclusions apply to every positive-active global
minimizer in this interval.

At either established boundary $b=\alpha$ or $b=\beta$, the
selected geometric pair is an original global minimizer. Its determinant cannot
be negative, because (46.31) would give a strict same-level competitor. Any
additional pure positive-active global contact at that level therefore has a
different away-population, even when the selected determinant is zero.

*Proof.* The relation (46.35) is (46.8) solved for $x$, and the displayed
population range is exactly the pure interval. For $0<x<1$ combine
(46.27) with (46.36). If a nongeometric pair had
$\mathfrak D_+\ge0$ and $g\le V$, both inequalities would be equalities;
Corollary 46.5 and the unique scalar selection would then put the pair
in $\mathcal G_\xi$, a contradiction. The endpoint
$x=1$ follows from equality in the trace triangle: all four diagonal entries
are the same scalar, and (46.37) follows from the inactive recovery being zero.
No division by $y$ is used there. At either boundary, Theorem 39.5
gives the attained original minimum $g=V(b)$ and the geometric
minimizers; (42.3) places these levels below $R_\star$. Theorem 45.5
provides purity of all their global contacts. A negative selected determinant
contradicts (46.31), while a zero determinant still has the unique fixed-slice
equality kernel (46.28); hence another contact must change $q$. $\square$

**Corollary 46.7 (a sector beyond the earlier shifted-support hypotheses).**
For $q=1$ on the positive row, the determinant has the sign of

$$
 n(x)=(h^2+s^2)x^3-s^2(1+x).
\tag{46.39}
$$

Its root from (36.44) is below $4/5$, since
$n(4/5)=(32-161s^2)/125>0$ and $s^2<3/20$. Hence every
$x\in(4/5,\sqrt{2/3})$ has $\mathfrak D_+(x,1)>0$ and
$\xi=6-4x\in(0,13/4)$. At the same time the shifted-support hypotheses of
(36.30) fail: the first required shift is
$h(\sqrt p-x\sqrt q/y)=-hx/y<0$. These slices also satisfy
$2(1+x)<2+\sqrt{8/3}$. By continuity, nearby $0<q<1$ slices retain these
strict inequalities. Theorem 46.4 and Corollary 46.5 nevertheless order every actual feedback
and every pure-effect coherence phase in these slices. This is a full-triangle result,
with all feedbacks in the fixed slice included.

**Mathematical source correspondence 46.8.** The ordinary-transpose density
coordinates, exact recoveries, common scalar action and both joint-distance
branches are source (23.2), (23.9)--(23.13). The attained diagonal domain and
its direct unitary realizations are source Theorem 23.2; the exact two-pair
phase reconstruction used in Lemma 46.2 is the established compatibility
argument behind Sections 35 and 42. The source42 theorem (42.15)--(42.16)
provides same-effect, same-complex-trace phase replacements and the positive
scalar variance used in Corollary 46.5. Theorem 36.5 and (36.43)--(36.56)
provide the previously established positive local instability direction; it
is reused here only for attribution. Theorem 37.5 supplies the positive
rank-one scalar ordering through distance four. Theorem 45.5 states, through
$R_\star$, the exact equalities (45.17)
$m=m_{\mathrm p}=m_{\mathrm{ph}}=m_{\mathrm{ph,p}}$ and
$\mathcal A_{\mathrm{ph},\xi}=\mathcal A_\xi\cap\mathcal P_\xi$; its proof and
the purity reduction are not reproved here.

For the realizability correspondence, Jasper--Loreaux--Weiss,
*Thompson's theorem for compact operators and diagonals of unitary operators*,
[arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3),
states the finite prescribed-complex-diagonal and singular-value theorem.
For dimension four and singular values all equal to one, its partial-sum
conditions are $\sum_{j=1}^k|w|_j^*\le k$ for $1\le k\le4$,
and its final condition is $|w|_1^*+|w|_2^*+|w|_3^*-|w|_4^*\le2$.
These are exactly $|w_j|\le1$ and
$\sum_j|w_j|-2\min_j|w_j|\le2$, the source domain (23.1).
A square matrix with these four singular values is unitary. This is a
realizability statement over all unitaries, with no converse asserted
for one fixed normal orbit. The Birkhoff--von Neumann step used in
source42 is the finite doubly-stochastic decomposition cited there from
Vourdas, arXiv:2203.09468v1, Section II.1, equation (18); it is used only
forward from the spectral decomposition of the given actual unitary.

The global-certificate comparisons are bounded correspondences only.
Bandeira--Boumal--Singer, *Tightness of the maximum likelihood semidefinite
relaxation for angular synchronization*, [arXiv:1411.3272v3](https://arxiv.org/html/1411.3272v3),
Lemma 4.3 and Section 4.3 require a positive-semidefinite Hermitian slack,
an annihilation condition and a real-diagonal condition for their fixed
unit-diagonal SDP. Soltanalian--Stoica, *Designing Unimodular Codes via
Quadratic Optimization is not Always Hard*, [arXiv:1303.0152v1](https://arxiv.org/html/1303.0152v1),
Theorem 2 assumes an actual unimodular vector in the top eigenspace of the
unchanged unconstrained quadratic objective. Neither result matches the
prescribed trace/population problem with a variable effect, so neither is
used as a proof premise. The new proof is the explicit nonlinear remainder
(46.19) on the actual coupled triangle. No literature-wide originality claim
is made.

**Unresolved mathematical obligations 46.9.** The new result does not order
all remaining populations and both signs against $V(\xi)$. It leaves the
negative-determinant positive sector, the entire negative canonical and
interior families, and their coupled level/population comparison. It does not
compute exact $\alpha$ or $\beta$, decide whether they coincide, determine the
maximal exhaustive-geometric-equality prefix or endpoint inclusion, or
identify and exhaust the first globally minimizing branch. A determinant-zero
slice has a complete fixed-population equality kernel, but coupled variation
of population and level can still have higher-order behavior; it does not
select a first boundary. Separated pure contacts, simultaneous contacts and
coalescence remain possible.

Through $R_\star$, (45.17) already excludes mixed global minimizers
and identifies the attained pure, phase and original minimum values.
Outside the canonical nonnegative slices, the remaining pure phase
minimizers and their complete actual original lifts still require
classification by the source42 variance-zero condition (42.25), with
singular effects, zero coherence, zero recovery and repeated phases
retained. For mixed sublevel competitors, Theorem 45.4 supplies the
same-level strict pure improvement in its stated value range; no direct
pure-slice bound for a mixed input is asserted here. Beyond $R_\star$,
the purity and transport consumers do not apply, and all mixed effects
and actual nondiagonal lifts remain in the unrestricted comparison.
The exact alpha/beta endpoint equality, immediate right-side behavior, all first-branch
obligations, and the full unrestricted first-loss/equality problem therefore
remain open. This section supplies a necessary global relation toward the unchanged
first-loss and equality problem and does not determine its unrestricted solution.

## 追加锚（本行以下为增补区）

## 47. Both-sign quantitative recovery gain and a negative-determinant strict-exclusion region

**Definition 47.1 (gain on the same attained triangle).** Use exactly the
rows, recoveries, pure effects, active complex trace and constants of
Definition 46.1. In particular $p=1-q$, $k=b-a>0$, $L=1+x$,
$y=\sqrt{1-x^2}$, $R_0=ax+b$ and $C_0=\ell y$. For either sign,
$0<x<1$ and $0\le q\le1$, let

$$
\begin{aligned}
 \mathcal T_x&=\{(X,Y)\in[0,1]^2:\sqrt X+\sqrt Y\ge1+x\},\\
 I_\sigma(x,q)&=\max_{(X,Y)\in\mathcal T_x}(\Gamma-\Gamma_0),\\
 \eta_\sigma(x,q)&=\max\left\{0,
       -\frac{L\mathfrak D_\sigma(x,q)}{4\mu x^2}\right\},\\
 C_{\mathrm{gain},\sigma}(x,q)
   &=\frac{\sqrt p\,k^2}{8R_0}
       +\frac{2m\sqrt q\,L}{3\sqrt3\,x},\\
 J_\sigma(x,q)&=\frac{\eta_\sigma(x,q)^2}
                         {4C_{\mathrm{gain},\sigma}(x,q)}.
\end{aligned}
\tag{47.1}
$$

Here $\mu$ and $\mathfrak D_\sigma$ are exactly (46.13), and
$\Gamma,\Gamma_0$ are the jointly attainable half-recovery amplitudes
(46.11), not separately optimized recoveries. The maximum exists:
$\mathcal T_x$ is compact, $XY\ge x^2>0$, and the expressions in
(46.11) are continuous there. The canonical corner belongs to this same
triangle and has $\Gamma=\Gamma_0$. Both summands defining
$C_{\mathrm{gain},\sigma}$ are nonnegative and at least one is positive,
including $q=0$ and $q=1$.

**Theorem 47.2 (global quadratic gain envelope in both signs).** For both
rows of (46.2), every $0<x<1$, every $q\in[0,1]$, and every point of the
complete attained triangle, including its boundary,

$$
\begin{aligned}
 \Gamma-\Gamma_0
   &\le\eta_\sigma B_c-C_{\mathrm{gain},\sigma}B_c^2
    \le J_\sigma,\\
 0&\le I_\sigma(x,q)\le J_\sigma(x,q).
\end{aligned}
\tag{47.2}
$$

In particular the possible improvement is at most quadratic in the
negative part of the normalized determinant in (47.1). No sign assumption
on $\nu$ or $\mathfrak D_\sigma$ is imposed.

*Proof.* Abbreviate $A=A_c$, $B=B_c$, $H=H_c$ and
$K=K_c=\sqrt L\,y/x$ only within this proof. Theorem 46.3 gives
$A=H+xB\ge0$, $B,H\ge0$ and
$\Delta=4LH-(H+LB)^2\ge0$. Its main-recovery identity yields

$$
 R_0^2-R^2=k(aH+R_0B),\qquad
 0\le R\le R_0,\qquad
 R_0-R=\frac{k(aH+R_0B)}{R_0+R}\ge\frac{kB}{2}.
\tag{47.3}
$$

Consequently the fourth term of (46.19) is at least
$\sqrt p\,k^2B^2/(8R_0)$.

For the coherent term, if $B>0$ then $H>0$. Put
$u=(H+LB)^2/(4LH)\in[0,1]$. The exact formula for $F^2$ and the
inequalities $1-X\le y^2$, $XY\ge x^2$ give

$$
 F\le K\sqrt{BH}\sqrt{1-u},\qquad
 K\sqrt{BH}-F
 \ge\frac{K(H+LB)^2\sqrt B}{8L\sqrt H}.
\tag{47.4}
$$

The last step uses $1-\sqrt{1-u}\ge u/2$, valid also at $u=0,1$.
For $z>0$, differentiation gives

$$
 \frac{d}{dz}\frac{(z+L)^2}{\sqrt z}
   =\frac{(z+L)(3z-L)}{2z^{3/2}},\qquad
 \frac{(z+L)^2}{\sqrt z}
   \ge\frac{16L^{3/2}}{3\sqrt3}.
\tag{47.5}
$$

Apply (47.5) with $z=H/B$. Equation (47.4) becomes the uniform estimate

$$
 K_c\sqrt{B_cH_c}-F
       \ge\frac{2Ly}{3\sqrt3\,x}B_c^2.
\tag{47.6}
$$

When $B_c=0$, both sides of (47.6) vanish, so this includes that boundary
without division by $B_c$ or $H_c$. Multiplying by
$\sqrt q\,\ell m/C_0=m\sqrt q/y$ gives the second summand of
$C_{\mathrm{gain},\sigma}B_c^2$. Drop only the other nonnegative
squares in the exact remainder (46.19). With
$\delta_\sigma=L\mathfrak D_\sigma/(4\mu x^2)$, this proves

$$
 \Gamma_0-\Gamma
   \ge\delta_\sigma B_c+C_{\mathrm{gain},\sigma}B_c^2.
\tag{47.7}
$$

Since $-\delta_\sigma\le\eta_\sigma$, completing the remaining scalar
square gives

$$
 \eta_\sigma B_c-C_{\mathrm{gain},\sigma}B_c^2
 =\frac{\eta_\sigma^2}{4C_{\mathrm{gain},\sigma}}
   -C_{\mathrm{gain},\sigma}
       \left(B_c-\frac{\eta_\sigma}{2C_{\mathrm{gain},\sigma}}\right)^2.
\tag{47.8}
$$

Taking the maximum and using the canonical corner proves (47.2).
All denominators are positive fixed-slice quantities. The proof uses no
division by $p$, $q$, $R$, $C$ or a determinant. At $q=0$ the coefficient
$\nu=k/2>0$ and $\mathfrak D_\sigma>0$, so $J_\sigma=I_\sigma=0$;
at $q=1$ the coherent summand keeps $C_{\mathrm{gain},\sigma}>0$ and
the displayed proof applies unchanged. In the nonnegative-determinant
slices $J_\sigma=0$, consistently with the already established
Theorem 46.4; no new equality classification is asserted. $\square$

**Theorem 47.3 (same-level lower bound for every actual pure input).**
For $0<\xi\le R_\star=13/4$, either active sign, a pure original effect
of away-population $q\in[0,1]$ and every relative coherence phase, put

$$
 x=1-\frac\xi4+\frac q2,\qquad
 G_{\sigma}^{\mathrm{low}}(x,q)
 =G_{\sigma}^{\mathrm{can}}(x,q)
             -8\Gamma_0J_\sigma-4J_\sigma^2.
\tag{47.9}
$$

If $0<x<1$, every actual $U\in U(4)$ with that effect and active
complex-trace modulus $2(1+x)$ satisfies

$$
\begin{aligned}
 g(E,U)&\ge G_{\sigma}^{\mathrm{low}}(x,q),\\
 M_\sigma(\xi,q)&:=G_{\sigma}^{\mathrm{low}}(x,q)-V(\xi)>0
 \quad\Longrightarrow\quad
 g(E,U)>V(\xi),\quad f(E,U)>N_{\mathrm{geo}}(\xi).
\end{aligned}
\tag{47.10}
$$

The original distance is $\xi$ and its minimizing sign is unique.
The feasible population range is $0\le q\le\min\{1,\xi/2\}$.
For its endpoint $x=1$, (47.9) is replaced by the direct statement

$$
 UU_\sigma^\dagger=\lambda I_4,\qquad
 \rho(E,U)=2q=\xi,\qquad
 g(E,U)=K_{-\sigma}^2q.
\tag{47.11}
$$

Here $|\lambda|=1$ is the one common feedback scalar. The feedback
slice is a singleton modulo that scalar and its gain over the canonical
amplitude is zero. No singular coefficient in (47.1) is evaluated at
$x=1$.

*Proof.* For a phase feedback, the same-feedback identity (23.12) and
(46.17) imply, for every effect phase,

$$
 |\chi|\le2\Gamma\le2(\Gamma_0+J_\sigma),\qquad
 g(E,U)=\mathsf E_\sigma(q)-|\chi|^2
       \ge\mathsf E_\sigma(q)-4(\Gamma_0+J_\sigma)^2.
\tag{47.12}
$$

This is (47.9); the two recoveries in $\chi$ belong to the same whole
feedback. For an arbitrary actual $U$, apply Theorem 42.3 to that given
matrix. Each positive-weight phase replacement has the same effect,
the same complex active trace and the same true original level. In
particular it has the same $q,x,\sigma$ and the same lower bound
(47.12). The variance identity (42.16), with $\kappa\xi$ restored,
gives

$$
 g(E,U)=\sum_j\theta_jg(E,U_j)
               +\sum_j\theta_j\|(a_j-a)F^{1/2}\|_2^2
       \ge G_{\sigma}^{\mathrm{low}}(x,q).
\tag{47.13}
$$

The effect and its coherence phase are unchanged throughout this
transport. The two-sign budget (42.17)--(42.20) proves the claimed
unique minimizing sign, including for each replacement. Formula
(46.8) gives the population range and $x\ge3/16>0$. At $x=1$ use the
direct trace-equality argument (46.37), whose other sign distance is
$8+2p>2q$. Finally $f=g-\kappa\xi$ proves the last comparison.
The negative row uses its own $G_-^{\mathrm{can}}$; no ordering of
negative canonical values against positive canonical values is assumed.
No pure-slice estimate has been applied to a mixed input. $\square$

**Theorem 47.4 (an explicit negative-determinant exclusion region).**
Let $\mathcal R_+$ be the following region, defined entirely by the
fixed functions in (46.11), (46.13), (46.25) and (47.1):

$$
\begin{aligned}
 \mathcal R_+=\biggl\{(\xi,q):\;&0<\xi\le13/4,\quad 0<q<1,
          \quad q<\xi/2,\quad x=1-\xi/4+q/2<\sqrt{2/3},\\
 &\mathfrak D_+(x,q)<0,\quad C_{\mathrm{gain},+}(x,q)>1/4,
       \quad\eta_+(x,q)<2/5,\\
 &\Gamma_0(x,q)<13/10,\quad G_+^{\mathrm{can}}(x,q)>3\biggr\}.
\end{aligned}
\tag{47.14}
$$

It contains $(\xi,q)=(13/4,1/8)$, where $x=1/4$, and contains a
relative neighborhood of that point in $(0,13/4]\times(0,1)$.
For every slice in $\mathcal R_+$, every actual original pure pair in
that slice, with arbitrary relative coherence phase, obeys

$$
 g(E,U)>\frac{771}{625}>\frac{17}{16}>V(\xi),\qquad
 g(E,U)-V(\xi)>\frac{1711}{10000}.
\tag{47.15}
$$

Thus this nonempty interior-population region excludes both same-level
equality and strict competition even though its determinant is negative.

*Proof.* First certify the anchor using rational inequalities. At
$x=1/4$, $q=1/8$, put $u_0=\sqrt{7/8}$, $v_0=\sqrt{1/8}$,
$y=\sqrt{15}/4$. The following open intervals have exact rational
endpoints:

$$
\begin{array}{c|rrrrrr}
 z&h&c&s&u_0&v_0&y\\ \hline
 1000z\text{ lower bound}&707&923&382&935&353&968\\
 1000z\text{ upper bound}&708&924&383&936&354&969.
\end{array}
\tag{47.16}
$$

They follow by squaring and $h^2=1/2$, $c^2=(1+h)/2$,
$s^2=(1-h)/2$. For the upper bound on $c$, use also
$h<442/625$, which follows by squaring; then
$(1+h)/2<1067/1250<(924/1000)^2$. In particular

$$
 \frac{215}{1000}<k<\frac{217}{1000},\qquad
 \frac{4399}{4000}<R_0<\frac{1101}{1000},\qquad
 \frac{73}{500}<s^2<\frac{293}{2000}.
\tag{47.17}
$$

At this anchor the exact coefficients reduce to

$$
 \mu=\frac12\left(\frac{hk u_0}{R_0}+\frac{hv_0}{y}\right),
 \qquad
 \nu=\frac12\left(k u_0-\frac{(s^2-1/8)v_0}{hy}\right).
\tag{47.18}
$$

For completeness, monotone substitution of (47.16)--(47.17) gives

$$
\begin{aligned}
 \mu&>\frac12\left(
  \frac{707\cdot215\cdot935}{1101\cdot10^6}
        +\frac{707\cdot353}{969\cdot1000}\right)>\frac{19}{100},\\
 \mu&<\frac12\left(
  \frac{708\cdot217\cdot936\cdot4}{4399\cdot10^6}
        +\frac{708\cdot354}{968\cdot1000}\right)<\frac15,\\
 \nu&>\frac12\left(\frac{215\cdot935}{10^6}
        -\frac{43\cdot354}{2\cdot707\cdot968}\right)>\frac9{100},\\
 \nu&<\frac{217\cdot936}{2\cdot10^6}<\frac{11}{100}.
\end{aligned}
\tag{47.19}
$$

Here $s^2-1/8>0$. Since $x^2/L=1/20$, these exact bounds imply

$$
\begin{aligned}
 \mathfrak D_+&=\frac{\mu\nu}{5}-\frac{s^2}{8}
  <\frac15\frac15\frac{11}{100}-\frac{73}{4000}<0,\\
 0<\eta_+&=\frac{5s^2}{8\mu}-\nu
  <\frac{5(293/2000)}{8(19/100)}-\frac9{100}<\frac25.
\end{aligned}
\tag{47.20}
$$

For the gain coefficient it suffices to retain the coherent summand.
Using $s>3/8$, $v_0>7/20$ and $\sqrt3<7/4$ gives

$$
 C_{\mathrm{gain},+}
   >\frac{10s v_0}{3\sqrt3}
   >\frac{10(3/8)(7/20)}{3(7/4)}=\frac14.
\tag{47.21}
$$

The amplitude and energy satisfy

$$
\begin{aligned}
 \Gamma_0&=u_0(c+h/4)+v_0hy\\
 &<\frac{936}{1000}\frac{1101}{1000}
       +\frac{354\cdot708\cdot969}{10^9}<\frac{13}{10},\\
 \mathsf E_+(1/8)
   &=\frac72(h+c)^2+\frac12(h+s)^2\\
   &>\frac72\left(\frac{1630}{1000}\right)^2
       +\frac12\left(\frac{1089}{1000}\right)^2>\frac{49}{5},\\
 G_+^{\mathrm{can}}
   &>\frac{49}{5}-4\left(\frac{13}{10}\right)^2
      =\frac{76}{25}>3.
\end{aligned}
\tag{47.22}
$$

Also $1/4<\sqrt{2/3}$ and all population and level inequalities in
(47.14) hold. This certifies the anchor without a numerical optimization.
All functions defining its strict inequalities are continuous for
$0<x<1$, $0<q<1$ and $C_{\mathrm{gain},+}>0$. Thus (47.14) contains
a relative neighborhood of the anchor, with levels strictly below
$13/4$ and populations on both sides of $1/8$.

On every slice in (47.14), $0\le J_+<4/25$. Theorem 47.3 yields

$$
 g(E,U)>3-8\frac{13}{10}\frac4{25}
                -4\left(\frac4{25}\right)^2
          =\frac{771}{625}.
\tag{47.23}
$$

For the selected comparator reuse (44.19) and Theorem 41.2, not an
unproved negative-branch comparison:

$$
 V(\xi)\le V(13/4)<(h+s)^2-\frac3{16}<\frac{17}{16}.
\tag{47.24}
$$

Indeed $h<5/7$, $s<2/5$ give
$(h+s)^2<(39/35)^2<5/4$. Finally
$771/625-17/16=1711/10000$, proving (47.15). $\square$

**Proposition 47.5 (actual core population and nongeometric strict
exclusions).** The slices in (47.14) contain actual pairs beyond both
older cap sectors, the trace-triangle sector, the population-sensitive
spectral-exclusion sector (44.12), and the nonnegative-determinant
slices of Theorem 46.6. It includes nongeometric phase feedbacks in
the interior of the attained triangle with both pairs split.

*Proof.* At the certified anchor take either $\tau\in\{+1,-1\}$ and
one common scalar $|\lambda|=1$, and set

$$
\begin{aligned}
 v^\tau&=\left(\frac{1+\tau i\sqrt{15}}4,
                  \frac{1-\tau i\sqrt{15}}4,1,1\right),\\
 \beta^\tau&=\begin{pmatrix}\sqrt{7/8}\\-\tau i\sqrt{1/8}\end{pmatrix},
 \qquad E=(T\beta^\tau(\beta^\tau)^\dagger T^\dagger)^{\mathsf T},
 \qquad U=\lambda\operatorname{diag}(v^\tau)U_+.
\end{aligned}
\tag{47.25}
$$

This is a pure original effect and a whole unitary. The two trace
moduli and original sign distances are exactly

$$
\begin{aligned}
 A(v^\tau)&=\frac52,& B(v^\tau)&=\frac{\sqrt{15}}2,\\
 \rho_+(E,U)&=\frac{13}{4},&
 \rho_-(E,U)&=\frac{39}{4}-\sqrt{15}>\frac{13}{4}.
\end{aligned}
\tag{47.26}
$$

Thus the true original distance, not merely a branch distance, is the
stated level. Moreover

$$
 A<2+\sqrt{8/3},\qquad B<2<23/6,\qquad
 A+B=\frac{5+\sqrt{15}}2>4.
\tag{47.27}
$$

These are the strict defining inequalities of the old core
$\mathcal O$ in (37.1). Since $E$ is pure,
$\epsilon(E)=0$, $L(p,0)=0$ in (44.2), and
$\theta(p)>0$ for $p=7/8$; thus (44.12) does not apply. The
spectral lower bound zero cannot yield the positive strict exclusion
(47.15). Equation (47.20) separately rules out using the old
nonnegative-determinant slice theorem.

The anchor feedback itself is canonical, so its scalar comparison is
already covered by Theorem 37.5. To demonstrate the new whole-slice
consumer, retain $x=1/4$, $q=1/8$ but put

$$
 B_c=\varepsilon,\qquad H_c=d_0\varepsilon,\qquad
 A_c=(x+d_0)\varepsilon,\qquad
 d_0=\left(\frac{t_c}{2\mu}\right)^2>0.
\tag{47.28}
$$

For

$$
 0<\varepsilon<\min\left\{1,\frac{y^2}{x+d_0},
                    \frac{4Ld_0}{(L+d_0)^2}\right\},
\tag{47.29}
$$

one has $0<X,Y<1$ and
$\Delta=4Ld_0\varepsilon-(L+d_0)^2\varepsilon^2>0$.
Consequently Lemma 46.2 reconstructs actual whole phase feedbacks
in the strict interior of the same triangle, with the same complex
active trace $2L\lambda$. Both pairs in (46.14) have distinct entries;
in particular the last pair is unequal, outside the enlarged geometric
shape $\mathcal C_{34}$ of Definition 35.4. Choose the crossed
orientation and effect phase aligning its two weighted recoveries.
The already established instability formula (46.31) then gives, for
all sufficiently small positive $\varepsilon$,

$$
 g(E_\varepsilon,U_\varepsilon)
       <G_+^{\mathrm{can}}(1/4,1/8),\qquad
 g(E_\varepsilon,U_\varepsilon)>V(13/4)+\frac{1711}{10000}.
\tag{47.30}
$$

The second inequality is the new whole-slice comparison (47.15).
The first shows why the canonical lower bound alone cannot prove it.
The reconstruction can be chosen continuously at the canonical
orientation: $X\to x^2$, $Y\to1$ and the pair centers align. Hence
(47.27) persists for small $\varepsilon$. The effect stays pure with
interior population, so the spectral-exclusion hypothesis remains
false. The branch distance is still $13/4$ and the other branch is
strictly larger by (42.20). Strict core inequalities, the sign gap,
and membership in (47.14) persist on a relative neighborhood in the
pure original domain restricted to $0<\rho\le13/4$, allowing level
and population to vary. These
are actual unscreened nongeometric pairs, not independent choices of
recovery moduli. $\square$

**Mathematical source correspondence and boundaries 47.6.** The new
repo-derived deductions are the uniform cone-gap coefficient (47.6),
the both-sign gain bound (47.2), its actual pure-slice consumer
(47.9)--(47.13), and the nonempty negative-determinant exclusion region
(47.14)--(47.30). Their mathematical premises are the original
same-feedback formulas (23.9)--(23.13), Theorem 46.3's exact global
remainder, and Theorem 42.3's same-effect, same-complex-trace variance
transport. The finite Birkhoff--von Neumann statement used by that
transport is the primary statement in Vourdas,
[arXiv:2203.09468v1, Section II.1, (18)](https://arxiv.org/html/2203.09468v1),
with probabilities over permutation matrices. It is applied forward
to the doubly stochastic matrix of the given unitary's spectral
basis, exactly as in (42.21)--(42.23). No new realization theorem,
synchronization SDP exactness, unconstrained top-eigenspace premise,
or literature-wide originality claim is used. The elementary
square-root inequality and one-variable minimum in (47.4)--(47.5)
are intermediate steps for this fixed record, not separate imported
research results. The canonical determinant criterion, its equality
lifts and the instability family are reused from Section 46; the
positive geometric selection and selected-value monotonicity are
reused from Theorems 37.5 and 41.2. The cutoff selected-value bound is
(44.19). Theorem 45.5 already supplies global purity through $13/4$;
it is not reproved by these slice estimates.

The gain bound itself holds on the complete triangle for both signs,
every $0<x<1$ and both endpoint populations. The actual original
common-level consumer is restricted to pure effects and
$0<\xi\le13/4$, with $x=1$ treated by (47.11). No mixed-input
pointwise bound follows from (47.13) or from global-minimizer purity.
No coefficient extension to $x=0$ is asserted. The bound is an upper
estimate of the available gain, not its exact maximum or a
classification of its maximizing triangle points. Outside the
explicit strict region, $M_\sigma\le0$ is only failure of this
certificate, not a competing original pair. The negative canonical
comparison remains unevaluated, even though its own gain envelope
and sufficient test (47.10) are available.

The remaining negative-determinant positive slices, the unscreened
negative branch, their joint level/population ordering, exact
$\alpha,\beta$, endpoint equality and inclusion, first-branch
exhaustion and immediate right-side behavior remain unresolved.
Outside the classified slices, complete actual minimizing lifts
still require the source42 variance-zero conditions, with singular
effects, zero recoveries, zero coherence and repeated phases retained.
Beyond $13/4$ these common-level transport and purity consumers give
no unrestricted conclusion; mixed effects and nondiagonal lifts
remain in the full problem. The strict excluded region narrows the
unchanged first-loss/equality problem and does not solve it.

## 追加锚（本行以下为增补区）

## 50. Uniform positive pure-branch comparison on an interior distance interval

**Definition 50.1 (original pairs and the positive scalar supplier).** Keep the original certificate basis $T=(b_+\ b_-)$, ordinary transpose and one actual shared feedback. Set

$$
\begin{aligned}
 I&=[11/5,9/4],&h&=\sqrt{1/2},&c&=\sqrt{(1+h)/2},&s&=\sqrt{(1-h)/2},\\
 k&=c-h,&d&=2(h+c),&e&=2(h+s),&p&=1-q,\\
 \beta^\phi&=(\sqrt p,e^{i\phi}\sqrt q)^{\mathsf T},&
 E&=(T\beta^\phi(\beta^\phi)^\dagger T^\dagger)^{\mathsf T},&q&\in[0,1],&\phi&\in\mathbb R.
\end{aligned}
\tag{50.1}
$$

Thus $E\ge0$, $\operatorname{Tr}E=1$ and $\operatorname{rank}E=1$, and every original normalized pure effect occurs. For one $U\in U(4)$, let $w=\operatorname{diag}(UU_+^\dagger)$ and use the same $A,B,P,Q$ as (23.2). In particular $A=|\sum_jw_j|$ and $B=|w_1-w_2+i(w_3-w_4)|$. The original distances and defect are

$$
\begin{aligned}
 \rho_\sigma(E,U)&=\min_{|\lambda|=1}\bigl(\|E-E_\sigma\|_{\mathrm F}^2+\|U-\lambda U_\sigma\|_{\mathrm F}^2\bigr),&
 \rho&=\min\{\rho_+,\rho_-\},\\
 \rho_+&=8+2q-2A,&\rho_-&=10-2q-2B,\\
 g(E,U)&=d^2p+e^2q-|\sqrt p\,P+e^{i\phi}\sqrt q\,Q|^2.
\end{aligned}
\tag{50.2}
$$

Each $\lambda$ is a single scalar on the whole feedback, as in (23.11); there are no column controls. If $\rho_+=\rho=\xi\in I$, put

$$
\begin{aligned}
 t&=\xi/2,&x&=1-\xi/4+q/2,&y&=\sqrt{1-x^2},&L&=1+x,\\
 R_0&=hx+c,&\Gamma_0&=\sqrt p\,R_0+\sqrt q\,hy,&
 G_\xi(q)&=d^2p+e^2q-4\Gamma_0^2,\\
 \mu&=\tfrac12(hk\sqrt p/R_0+h\sqrt q/y),&
 \nu&=\tfrac12\bigl(k\sqrt p+(h^2x-s^2)\sqrt q/(hy)\bigr),&t_c&=s\sqrt{qL}/x,\\
 \mathfrak D_+(x,q)&=4\mu\nu x^2/L-s^2q,&
 \omega(\xi,q)&=\nu-t_c^2/(4\mu)=L\mathfrak D_+(x,q)/(4\mu x^2),\\
 B_{\mathrm{gain}}&=\frac{k^2\sqrt p}{8R_0}+\frac{2s\sqrt q\,L}{3\sqrt3\,x},&
 J&=\frac{\max\{0,-\omega\}^2}{4B_{\mathrm{gain}}}.
\end{aligned}
\tag{50.3}
$$

These are exactly the positive row $(a,b,\ell,m)=(h,c,h,s)$ of (46.2): $B_{\mathrm{gain}}=C_{\mathrm{gain},+}$, $\max\{0,-\omega\}=\eta_+$ and $J=J_+$ in (47.1). In particular $B_{\mathrm{gain}}$ is distinct from the trace modulus $B$. The full population range is $[0,\min\{1,\xi/2\}]=[0,1]$, and throughout it

$$
 7/16\le x\le19/20<1,\qquad y>0,\quad R_0>0,\quad\mu>0,\quad B_{\mathrm{gain}}>0.
\tag{50.4}
$$

At $q=0$ the first summands keep $\mu,B_{\mathrm{gain}}$ positive; at $q=1$ the second summands do so. No singular $x=1$ slice occurs in $I$. Let $\delta_\circ(t)$ be the unique positive geometric selector of Theorem 37.5, and set

$$
 q_\xi=t-\delta_\circ(t),\qquad
 V(\xi)=G_\xi(q_\xi)=N_{\mathrm{geo}}(\xi)+\kappa\xi,\qquad
 D_{\mathrm{sel}}(\xi)=\mathfrak D_+(1-\xi/4+q_\xi/2,q_\xi).
\tag{50.5}
$$

The determinant agrees with (36.43) and (43.1), with their second argument $p=1-q$. The supplier $V$ here is only the selected positive rank-one geometric value, without a premise of unrestricted optimality.

**Theorem 50.2 (four exact continuous-domain enclosures).** The following rational closed enclosures hold; the derivative in C4 is at fixed $\xi$, evaluated only at $q=9/20$.

| Certificate | Function | Closed variable domain | Required bound | Pieces | Outward enclosure of the entire image |
| --- | --- | --- | --- | --- | --- |
| C1 | $\omega(9/4,q)$ | $q\in[0,1/10]$ | $\ge1/10000$ | 10 | $[313809/250000000,23008109/200000000]$ |
| C2 | $\omega(9/4,q)$ | $q\in[3/8,1]$ | $\ge1/10000$ | 27 | $[129303/1000000000,19833451/31250000]$ |
| C3 | $\omega(9/4,q)$ | $q\in[1/10,3/8]$ | $\ge-21/1000$ | 132 | $[-20992343/1000000000,4663773/250000000]$ |
| C4 | $G'_\xi(9/20)$ | $\xi\in I$ | $\le-1/10$ | 1 | $[-453826117/1000000000,-24250863/125000000]$ |

*Proof.* The derivative expression used in C4 is

$$
 G'_\xi(q)=-(4h+8s)-4\Gamma_0\left(h\sqrt p-\frac{R_0}{\sqrt p}+\frac{hy}{\sqrt q}-\frac{hx\sqrt q}{y}\right).
\tag{50.6}
$$

Indeed $dx/dq=1/2$, $dy/dq=-x/(2y)$, and $d^2-e^2=4h+8s$, using $c^2-s^2=h$ and $h(c-s)=s$. Formula (50.6) is used only at the interior population $9/20$; it is not evaluated at $q=0,1$.

Here is the complete compact partition specification. In each row let $[a,b]$ be its stated variable domain and normalize $z=(v-a)/(b-a)$. A run $(u,v,r)$ with denominator $N$ denotes all consecutive closed intervals $[j/N,(j+r)/N]$, $j=u,u+r,\ldots,v-r$, pulled back by $a+(b-a)z$.

| Certificate | $N$ | All runs, in order |
| --- | --- | --- |
| C1 | 32 | $(0,8,4),(8,16,8),(16,24,4),(24,30,2),(30,32,1)$ |
| C2 | 4096 | $(0,2,1),(2,8,2),(8,16,4),(16,48,8),(48,96,16),(96,192,32),(192,384,64),(384,512,128),(512,1024,256),(1024,2048,512),(2048,4096,1024)$ |
| C3 | 512 | $(0,32,32),(32,96,16),(96,136,8),(136,172,4),(172,204,2),(204,262,1),(262,296,2),(296,336,4),(336,384,8),(384,448,16),(448,512,32)$ |
| C4 | 1 | $(0,1,1)$ |

Every run ends where the next begins, the first starts at $0$, and the last ends at $N$. Their positive lengths sum exactly to $N$, and their counts $\sum(v-u)/r$ are respectively $10,27,132,1$. Thus these are full closed covers with disjoint interiors, including both original endpoints; no grid-point sign assertion is substituted for an interval image.

The rational interval rules specifying those images are as follows. Use exact rational addition, negation, and multiplication by the minimum and maximum of the four endpoint products. For $0\notin[\ell,u]$, reciprocal is $[1/u,1/\ell]$. Squaring has upper endpoint $\max\{\ell^2,u^2\}$ and lower endpoint $0$ if the interval contains zero, otherwise $\min\{\ell^2,u^2\}$. With $S=2^{96}$, for each rational $r\ge0$ put $n=\operatorname{isqrt}(\lfloor rS^2\rfloor)$. The lower root endpoint is $n/S$; the upper is $(n+1)/S$, except that it is $n/S$ when $n^2=rS^2$. Apply these at the lower and upper radicand endpoints respectively. The inequalities

$$
 (n/S)^2\le r<((n+1)/S)^2
\tag{50.7}
$$

prove root containment, including $r=0$ and exact-square upper endpoints. These rules preserve inclusion by induction through every expression; all reciprocal intervals exclude zero and all root radicands are nonnegative.

Initialize $h,c,s$ in that order from (50.1), using these root rules. In C1--C3 evaluate (50.3) with the identities $h^2=1/2$, $s^2=(1-h)/2$ and $t_c^2=s^2q(1+x)/x^2$; do not separately interval-square an enclosure of $s$. In C4 use (50.6) at $q=9/20$. On each leaf, natural interval evaluation of the whole variable interval satisfies the named threshold. Taking the minimum of all leaf lower endpoints and the maximum of all leaf upper endpoints, then rounding them down and up respectively to multiples of $10^{-9}$, gives exactly the table's rational aggregate enclosures. They imply each displayed bound, since every argument is in a leaf and its function value is in that leaf image.

The complete rational leaf endpoints and images, including the endpoint-square and zero-exclusion rules, are specified by [the enclosure manifest](https://github.com/the-omega-institute/trureturing-experiments/blob/f6566d53e43290d7ff7148da38f48f96238fc9f7/experiments/auric/four-path/positive-pure-interval-11-5-9-4/certificate.json) and [its defining exact evaluator](https://github.com/the-omega-institute/trureturing-experiments/blob/f6566d53e43290d7ff7148da38f48f96238fc9f7/experiments/auric/four-path/positive-pure-interval-11-5-9-4/certify_interval.py). The manifest SHA256 is `661b9582e4425abb56e4fc17e73d7aa68a2b5970233c0a95f1109c33a85f4046`; its mathematical supplier pin is `5fd6a884f9173f778cfa040217d7d51f748ac9c6`. The partition and rational rules above specify the continuous certificate independently of adaptive subdivision choices. The same rules also give

$$
\begin{aligned}
 \omega(9/4,1/4)&\in[-9840817/500000000,-19681633/10^9]\subset(-\infty,-19/1000),\\
 8hc-1&>4,&s&>19/50,&k&>21/100,\\
 h(51/80)+c&<7/5,&h+c&<5/3,&\sqrt{30}&<11/2,\\
 18-8(c+s)-9/2&>76187407/25000000>3.
\end{aligned}
\tag{50.8}
$$

These last constant inequalities can equally be checked by rational endpoint squaring with positive denominators. $\square$

**Theorem 50.3 (the entire positive-active pure branch on $I$).** For every $\xi\in[11/5,9/4]$, every original normalized positive rank-one $E$ with the ordinary transpose convention, and every single original $U\in U(4)$ such that $\rho_+(E,U)=\rho(E,U)=\xi$,

$$
 g(E,U)\ge V(\xi),\qquad D_{\mathrm{sel}}(\xi)>0.
\tag{50.9}
$$

Both level endpoints and both population endpoints are included. If the actual population slice satisfies $\mathfrak D_+(x,q)<0$, then

$$
 g(E,U)-V(\xi)>\frac{1196031}{1600000000}>\frac7{10000}.
\tag{50.10}
$$

Such negative-determinant slices are nonempty. The existing selected positive geometric pairs attain $V(\xi)$; negative-determinant slices cannot attain it. No additional exhaustive equality or original-lift classification is asserted here.

*Proof.* First compare scalars on the entire feasible population interval. Under $\delta=t-q=2(1-x)$, the positive-row quantities of (37.12) are $F=4(1-q)R_0^2$ and $G=4qh^2y^2$, and

$$
 \mathcal H_{+,t}(\delta)+\kappa\xi=G_\xi(q),\qquad
 G_\xi''(q)\ge8hc-1>4\quad(0<q<1).
\tag{50.11}
$$

Indeed $d\delta/dq=-1$, (37.22) gives $F''\le1-8hc$, $G''\le0$, and the geometric mean $\sqrt{FG}$ is concave as in the proof of Theorem 37.5. The remaining energy term is affine. The source selector is interior, so integration of (50.11), using $G'_\xi(q_\xi)=0$, gives

$$
 G_\xi(q)-V(\xi)\ge2(q-q_\xi)^2\qquad(0\le q\le1).
\tag{50.12}
$$

Continuity extends this inequality to $q=0,1$. C4 certifies $G'_\xi(9/20)\le-1/10<0$ for every $\xi\in I$. The strictly increasing derivative and its unique zero therefore imply

$$
                        q_\xi>9/20.
\tag{50.13}
$$

Next extend C1--C3 from $\xi=9/4$ to the whole level interval, rather than assuming those one-level signs suffice. At fixed $0<q\le1$, differentiation in $x$ gives

$$
 \nu_x=\frac{\sqrt q(h^2-s^2x)}{2hy^3}>0,\qquad
 \frac{\mu_x}{\mu}\ge-\frac h{R_0},\qquad
 \partial_x\log(t_c^2/\mu)\le\frac1L-\frac2x+\frac h{R_0}<\frac1L-\frac1x<0.
\tag{50.14}
$$

For the middle inequality, the logarithmic derivatives of the two nonnegative summands of $2\mu$ are $-h/R_0$ and $x/y^2$; take their positive weighted average, omitting a zero summand. This also handles $q=1$ directly. The strict inequality uses $R_0=hx+c>hx$. Thus $\omega_x>0$. At $q=0$ the formula is instead $\omega=k/2>0$, independent of $x$, without a logarithm of zero. Since decreasing $\xi$ increases $x$ at fixed $q$, C1--C3 yield throughout $I$

$$
\begin{aligned}
 \omega(\xi,q)&\ge1/10000&&\text{if }q\in[0,1/10]\cup[3/8,1],\\
 \omega(\xi,q)&\ge-21/1000&&\text{if }q\in[1/10,3/8].
\end{aligned}
\tag{50.15}
$$

In particular $\mathfrak D_+<0$ forces $1/10<q<3/8$ and $0<-\omega\le21/1000$, because the determinant has the sign of $\omega$. At the selected $q_\xi>9/20>3/8$, (50.15) gives $\omega\ge1/10000>0$, hence $D_{\mathrm{sel}}(\xi)>0$ under the exact determinant identification of (50.5).

On a negative slice, $x\le\bar x=9/20+q/2\le51/80$. The function $\sqrt q(1+\bar x)/\bar x$ increases on $[1/10,3/8]$: its derivative has the sign of $\bar x^2+\bar x-q\ge1/4+1/2-3/8=3/8>0$. Since $(1+x)/x$ decreases with $x$, its left endpoint gives

$$
 \frac{2s\sqrt q\,L}{3\sqrt3\,x}\ge\frac{2s}{\sqrt{30}}>\frac{38}{275}.
\tag{50.16}
$$

Also $\sqrt p>3/4$, $k>21/100$ and $R_0\le h(51/80)+c<7/5$. Consequently

$$
\begin{aligned}
 B_{\mathrm{gain}}&>\frac{38}{275}+\frac{6615}{2240000}=\frac{99359}{704000}>\frac7{50},\\
 J&\le\frac{(21/1000)^2}{4(7/50)}=\frac{63}{80000},\\
 \Gamma_0^2&\le R_0^2+h^2y^2=h^2+c^2+2hc x<(h+c)^2<(5/3)^2,\\
 G_\xi(q)-V(\xi)&>2(9/20-3/8)^2=9/800.
\end{aligned}
\tag{50.17}
$$

The third line is Cauchy--Schwarz with $p+q=1$, so $\Gamma_0<5/3$. The last line uses (50.12)--(50.13) and the strict separation $q<3/8$.

For a whole phase feedback, apply the existing quadratic-gain consumer (47.9)--(47.12) directly with the parameter map in (50.3). It gives, for every effect phase,

$$
 g(E,U)-V(\xi)\ge G_\xi(q)-V(\xi)-8\Gamma_0J-4J^2.
\tag{50.18}
$$

This invokes the simultaneous main and crossed recoveries on the same attained triangle; it does not replace them by independently attainable extrema. If $\omega\ge0$, then $J=0$ and (50.12) proves (50.9), including $q=0,1$. If $\omega<0$, (50.17)--(50.18) give

$$
\begin{aligned}
 g(E,U)-V(\xi)&>\frac9{800}-\frac{40}{3}\frac{63}{80000}-4\left(\frac{63}{80000}\right)^2
                    =\frac{1196031}{1600000000},\\
 \frac{1196031}{1600000000}-\frac7{10000}&=\frac{76031}{1600000000}>0.
\end{aligned}
\tag{50.19}
$$

Finally transfer these inequalities to each arbitrary original $U$, without identifying phase-only feedbacks with all unitaries. Theorem 42.3, applied forward to that very $U$, supplies positive weights $\theta_j$ of sum one and whole phase unitaries $U_j$ with the same effect and the same complex trace $\operatorname{Tr}(U_jU_+^\dagger)=\operatorname{Tr}(UU_+^\dagger)$. Thus $q,x,\xi$ are unchanged. The original two-sign budget (42.17) gives for the original pair and for every replacement

$$
 \rho_- -\xi\ge18-8(c+s)-2\xi\ge18-8(c+s)-9/2>3.
\tag{50.20}
$$

Their positive branches are therefore uniquely active, their true joint distances equal $\xi$, and the original metric still uses one whole-feedback scalar. Put $F=T^\dagger E^{\mathsf T}T$ and $\mathbf a=(P(w),Q(w))$, $\mathbf a_j=(P(w_j),Q(w_j))$. Equations (42.15)--(42.23) give $\mathbf a=\sum_j\theta_j\mathbf a_j$ and the exact nonnegative variance identity

$$
 g(E,U)=\sum_j\theta_jg(E,U_j)+\sum_j\theta_j\|(\mathbf a_j-\mathbf a)F^{1/2}\|_2^2.
\tag{50.21}
$$

Every replacement satisfies the same bound (50.18), because its population slice and determinant are unchanged. A finite positive weighted average preserves the strict uniform bound (50.19), and the nonnegative variance preserves both comparisons. This proves (50.9)--(50.10) for every original $U$, with the ordinary transpose and all relative effect phases retained.

For nonemptiness, (50.8) gives a negative determinant at $(\xi,q)=(9/4,1/4)$, where $x=9/16$. The actual phase diagonal $(x+iy,x-iy,1,1)$ with its single feedback $U=\operatorname{diag}(w)U_+$ and any effect (50.1) at that population has $A=2(1+x)$ and true original level $9/4$ by (50.20). Thus the strict exclusion concerns realized original slices. Attainment at each level by the existing selected positive pairs follows from Theorem 37.5 and its actual-distance check (37.23), without a new equality or lift argument. $\square$

**Mathematical sources and scope 50.4.** The new deduction is the full positive-active pure-branch consumer on the closed interior interval $I$, including the separated negative-determinant slices. The both-sign quadratic gain is reused from Section 47, the original-unitary transport from Section 42, the selected scalar and curvature from Section 37, and the determinant identification and attained triangle from Sections 43 and 46. The interval inclusion method is standard; see Moore, Kearfott and Cloud, *Introduction to Interval Analysis*, SIAM (2009), [DOI 10.1137/1.9780898717716](https://doi.org/10.1137/1.9780898717716). Its rational rules are stated explicitly in Theorem 50.2. The geometric-mean concavity argument is the existing source37 intermediate step. Neither these mature methods nor the already established suppliers are claimed as new mathematical content or as literature priority.

The interval $I$ is not a prefix from zero and does not identify first loss. The negative-active family, mixed-input pointwise comparisons, ordering on the entire original level range, exact $\alpha,\beta$, complete equality/lift classification and behavior outside $I$ remain unresolved by this result. In particular $D_{\mathrm{sel}}>0$ here is not a global criterion for the original optimization problem. The unchanged long-term AURIC question is not exhausted by this bounded interval theorem.

## 追加锚（本行以下为增补区）

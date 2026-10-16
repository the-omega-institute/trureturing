# Native complete-continuation distinguishability gap

## 1. The fixed experiment and its mathematical claim

**Convention 1.1 (scope and provenance).** This volume concerns exactly the
normalized live-cut experiment of [Acquired Continuation Limits][AC],
§§2–4 and Corollary 6.2. The fixed parameters are

$$
c=\frac14,\qquad Z=\frac12,\qquad
 a=\frac1{16},\qquad h=\frac{11}{256},\qquad
 d=\frac3{128}=\frac6{256},\qquad L=1.
\tag{CG.1}
$$

The twelve prescribed histories have

$$
\mathcal H=\left\{(x,\beta,m):
 x\in\left\{\frac5{256},\frac{16}{256},\frac{27}{256}\right\},\quad
 \beta\in\{0,\pi\},\quad m\in\{0,1\}\right\}.
\tag{CG.2}
$$

Their actual preparation, original-control realization, reached-cut
meaning and canonical continuation laws are credited premises from [AC].
The additional deduction is the coherence-retaining endpoint comparison
in §§5–6. Its ordinary proof is given in full. Trace-norm identities,
channel affinity, convexity and CPTP contractivity are standard tools;
they are proved below to fix the normalization and output conventions.
Mathematical provenance is `repo-derived`; no literature priority claim
is made. The source's nested control and instrument suppliers enter through
its stated premises, rather than through a separate certification here.

The resulting lower bound applies to one common CPTP processor on the sole
specimen and fixed common inputs, with all outcomes counted. It determines
neither the exact complete-output minimax value nor an attaining simulator.

## 2. Actual original histories from one preparation

**Definition 2.1 (original source and real phases).** The original class
in [AC, Definition 2.1][AC] has a valid base $b=(X,Y,Z)$ with
$r=1-Z$, $0<Z<1$, $0<X,Y<r$, and

$$
\begin{aligned}
J_b&=(\max(0,X+Y-r),\min(X,Y)),\\
p_b(k)&=(r-X-Y+k,X-k,Z,Y-k,k),\\
\mathbf d&=(1,-1,0,-1,1),\qquad
 I_b(k)=\sum_{i\in\{0,1,3,4\}}p_b(k)_i^{-1},\\
w_b(k)_i&=\frac{\mathbf d_i}{p_b(k)_i I_b(k)}.
\end{aligned}
\tag{CG.3}
$$

Index $4$ denotes original mode $13$ throughout. An original history has
finite duration $T\geq0$, continuous real coordinates $k,\chi$, strict
$k(t)\in J_b$, finite variation of $\chi$, and either both coordinates
absolutely continuous or the source's finite-piecewise-$C^1$ alternative
with derivative rates continuous on each closed piece. With the compatible
common preparation lift $\theta$, the actual normalized live vector is

$$
\psi_i(t)=\sqrt{p_b(k(t))_i}\,e^{-i(\theta_i+H_i(t))},\qquad
H_i(t)=\int_0^t w_b(k(s))_i\chi'(s)\,ds.
\tag{CG.4}
$$

The real lift and signed integer winding in
$\chi(T)-\chi(0)=2\pi m$ are retained. The catalogue (CG.2) selects
particular lawful histories; it changes no original regularity, duration,
signed-sector or domain permission.

For the present double wall $b=(c,c,Z)$, $r=2c$, $J_b=(0,c)$,
$p_b(k)=(k,c-k,Z,c-k,k)$ and

$$
w_b(k)=\left(\frac{c-k}{2c},-\frac{k}{2c},0,
                    -\frac{k}{2c},\frac{c-k}{2c}\right).
\tag{CG.5}
$$

Take the source's fixed preparation calibration $\theta=0$ and define
orthonormal directions

$$
|+\rangle=\frac{e_0+e_4}{\sqrt2},\qquad
|-\rangle=\frac{e_1+e_3}{\sqrt2},\qquad |2\rangle=e_2,
\qquad V=\operatorname{span}\{|+\rangle,|-\rangle,|2\rangle\}.
\tag{CG.6}
$$

Write $P_j=|j\rangle\langle j|$. The source's actual endpoint states are

$$
\begin{aligned}
\psi_{x,\beta,m}&=\sqrt Z\,|2\rangle+
 e^{-i\beta}\left(\sqrt{2x}\,|+\rangle+
       (-1)^m\sqrt{2(c-x)}\,|-\rangle\right),\\
\rho_{x,\beta,m}&=|\psi_{x,\beta,m}\rangle
                         \langle\psi_{x,\beta,m}|.
\end{aligned}
\tag{CG.7}
$$

**Proposition 2.2 (credited realization and positive reached-cut mass).**
Every member of (CG.2) is realized from the same preparation at
$a_0=1/8$ with auxiliary rectangle height $q_0=1/16$. Set
$B=8\beta-4\pi m$. The following six legs each take one unit, with
affine coordinates and literal chronological joins:

| Leg | Height coordinate | Actual real phase coordinate |
| --- | --- | --- |
| 1 | $a_0$ | $0\longrightarrow2\pi m$ |
| 2 | $a_0\longrightarrow q_0$ | $2\pi m$ |
| 3 | $q_0$ | $2\pi m\longrightarrow2\pi m+B$ |
| 4 | $q_0\longrightarrow a_0$ | $2\pi m+B$ |
| 5 | $a_0$ | $2\pi m+B\longrightarrow2\pi m$ |
| 6 | $a_0\longrightarrow x$ | $2\pi m$ |

The residual is exactly
$(\beta,\beta-\pi m,0,\beta-\pi m,\beta)$, giving (CG.7).
Under the supplied canonical execution, the probabilities of reaching
this live cut at time six are

$$
q_{5/256}=\frac{32}{177},\qquad
q_{16/256}=\frac29,\qquad q_{27/256}=\frac{32}{111}.
\tag{CG.8}
$$

Proof. This is [AC, Proposition 3.1, (AC.5)–(AC.6), (AC.22)][AC],
using the original synthesis and composition credited there. Its displayed
phase correspondence can be checked directly: the phase leg and rectangle
contribute

$$
2\pi m\,w_b(a_0)+B\bigl(w_b(q_0)-w_b(a_0)\bigr).
\tag{CG.9}
$$

Here $w_b(a_0)=(1/4,-1/4,0,-1/4,1/4)$ and
$w_b(q_0)-w_b(a_0)=(1/8,1/8,0,1/8,1/8)$.
Since $B/8=\beta-\pi m/2$, substitution gives the stated five
residual entries. Leg 6 has $\chi'=0$ and changes only height.
All heights are strictly internal. The finitely many affine pieces
satisfy both regularity alternatives and have phase variation
$2\pi|m|+2|B|$. The phase pairs used later have $m=0$ and
$B=0$ or $8\pi$; they are actual histories, not newly chosen preparations.

The supplied double-wall survival charge has rate
$(k')_+/k+(-k')_+/(c-k)$. The phase legs contribute zero charge;
the rectangle descent and ascent contribute survival factors $2/3$ and
$1/2$. Since each catalogue height is below $a_0$, the final leg gives
$(c-a_0)/(c-x)$. Their product is
$q_x=(c-a_0)/(3(c-x))$, which gives (CG.8).
Every earlier failure stays in its own absorbing stopped archive.
These positive live branches require no replacement or repeated preparation.
$\square$

**Definition 2.3 (conditioning and legal continuation).** The experiment
starts with each actual history conditioned on reaching its old live cut
at the common time six. The sole specimen there is the normalized state
(CG.7). The different masses (CG.8) describe that earlier execution; they
are not silently used as new mixture weights or acceptance probabilities.
No new acquisition acceptance event is conditioned upon.

The public requested relative command is $k_x(t)=x+dt$,
$\chi(6+t)=\chi(6)$, $0\leq t\leq1$. In the original relative-command
convention, increments $A(t),C(t)$ starting at zero have height domain
$(\ell_b-\min A,u_b-\max A)$ when $J_b=(\ell_b,u_b)$.
Thus this ramp has domain

$$
(0,c-d)=\left(0,\frac{58}{256}\right).
\tag{CG.10}
$$

All three catalogue heights belong to it, and their terminal heights are
$11/256,22/256,33/256$. Permissions are common and the request is promised
legal on this catalogue. Naming a partial request supplies no detector of
an unknown domain violation. Known denial or mismatch has its visible
unexecuted rejection and controller update. Literal composition preserves
the old real phase lift; it does not read or reset it. Zero duration permits
only the matching zero-displacement identity, not an instantaneous nonzero
leg. These are the permissions of [AC, Definition 2.4][AC].

For this finite seven-unit experiment the original populations stay at
least $5/256$ from zero; the height speed is at most $27/256$, phase
speed at most $8\pi$, and phase variation at most $16\pi$.
These follow from the table, $B\in\{0,-4\pi,8\pi,4\pi\}$ and the
ramp speed $6/256$. No wall limit or infinite winding is used.

## 3. One common processor and the complete output distance

**Definition 3.1 (available input and common CPTP comparison).** Alongside
the sole cut specimen there is a fixed common state $\tau$ of metadata
and blanks: the complete accessible input is
$\rho_{x,\beta,m}\otimes\tau$. The metadata contain the no-failure flag,
aligned cut time, common source/preparation/epoch identity, fixed reference
calibration, permissions and controller state. They contain no unknown
history index, readable old waveform, generator word, source callback,
height programme, parity helper,
environment port or additional specimen. No source-dependent installed
processor is supplied.

Arbitrary independent ancillary spaces, private randomness, computation,
finite adaptive instruments and retained classical or quantum records are
allowed. Branch maps remain unnormalized, and every branch, including
acquisition abort and unexecuted rejection, contributes to the output.
Composition with a fixed common output interpretation gives a single
history-independent CPTP map. Absorb $\tau$ and independent ancillas into
it and write this map as $\Phi$ on $V$. Enlarging the comparison to all
such common CPTP maps only makes a necessary lower bound stronger; it
supplies no new legal quantum read, original actuator or permission.

The ideal continuation is a source-indexed target family. Its dependence
on $x$ does not install $x$ in $\Phi$. Earlier source-sensitive assistance
would be a different joint-input premise, outside this experiment.

**Definition 3.2 (complete stopped cq metric).** The canonical output has
one terminal live quantum block and five classical failure sectors indexed
by the original mode, each carrying the exact first-failure time and
stopped state $P_f=|f\rangle\langle f|$. Time $t\in[0,1]$ is elapsed
continuation time, equivalently the exact absolute time $6+t$ by a common
translation. It is a measurable variable, with no time binning or assumed
finite-bit representation. The first executed failure is absorbing: no
later operation, retry, reversal, reset or replacement specimen follows it.
All old archives and declared controller updates remain in their
corresponding branches. The displayed canonical factors give a necessary
marginal of any larger required joint output.

For normalized outputs $\omega,\eta$ the convention is [AC, (AC.4)][AC]:

$$
\operatorname{dist}(\omega,\eta)
       =\frac12\|\omega-\eta\|_{1,\mathrm{cq}}.
\tag{CG.11}
$$

When both outputs have canonical densities, this is

$$
\frac12\left(\|\omega_{\rm live}-\eta_{\rm live}\|_1+
 \sum_{i=0}^4\int_0^1\|\omega_i(t)-\eta_i(t)\|_1\,dt\right).
\tag{CG.12}
$$

For arbitrary simulated measures, take densities relative to a common
dominating scalar measure in each sector and integrate their trace norms.
This includes singular time events. Additional abort, rejection or other
output sectors are included in the same direct-sum norm; their ideal
weights are zero where absent from the target. Retained auxiliary records
can be included jointly or subjected to the same fixed interpretation.
Forgetting only extra fields gives a necessary canonical-output test; it
does not discard any acquisition outcome or first-failure event. No branch
mass is divided by its success probability.

This is a pointwise comparison of source-indexed statistical experiments,
not a common-input metric between different source-dependent instruments.

## 4. The entire prescribed ramp law

**Proposition 4.1 (credited canonical CP law and its specialization).**
Put $\nu=d/L=d$ and, for $0<x<c-d$, define

$$
S_x(t)=\frac{x}{x+\nu t},\qquad
f_x(t)=\frac{\nu x}{(x+\nu t)^2},\qquad s_x=S_x(1)=\frac{x}{x+d}.
\tag{CG.13}
$$

In basis $(+,-,2)$ the terminal no-failure operator and separate original
failure CP densities supplied by [AC, Proposition 4.1, (AC.8)][AC] are

$$
\begin{aligned}
K_x&=\operatorname{diag}\left(1,
 \sqrt{\frac{x(c-x-d)}{(x+d)(c-x)}},\sqrt{\frac{x}{x+d}}\right),\\
\mathcal I_{x,2}(dt)(\rho)
 &=f_x(t)|f\rangle\langle2|\rho|2\rangle\langle f|\,dt,\\
\mathcal I_{x,i}(dt)(\rho)
 &=\frac{c f_x(t)}{2(c-x)}
            |f\rangle\langle-|\rho|-\rangle\langle f|\,dt
                 \quad(i=1,3),\\
\mathcal I_{x,0}(dt)&=\mathcal I_{x,4}(dt)=0.
\end{aligned}
\tag{CG.14}
$$

On the actual state (CG.7) the complete normalized target
$\Omega_{x,\beta,m}$ consequently has live block and five separate
mode densities

$$
\begin{aligned}
(\Omega_{x,\beta,m})_{\rm live}&=s_x\rho_{x+d,\beta,m},\\
\bigl((\Omega_{x,\beta,m})_i(t)\bigr)_{i=0}^4
   &=(0,c,Z,c,0)f_x(t)P_f.
\end{aligned}
\tag{CG.15}
$$

In particular the two equal minus-mode densities remain distinct original
modes $1,3$, and the last zero-density sector retains the name $13$.

Proof. The underlying calibrated CP transport and jump laws are premises
credited in [AC] to its instrument supplier. Their displayed correspondence
also checks (CG.14) directly. On this ramp put $k=x+\nu t$. The canonical
hazard is $\lambda=\nu/k$, and
$\gamma_i=\lambda-(\log p_b(k)_i)'$ gives

$$
\gamma_0=\gamma_4=0,\qquad
\gamma_1=\gamma_3=\frac\nu k+\frac\nu{c-k},\qquad
\gamma_2=\frac\nu k.
\tag{CG.16}
$$

The no-failure transport is
$\sqrt{S_x(t)}\operatorname{diag}_i
\sqrt{p_b(k)_i/p_b(x)_i}$, and the mode-$i$ jump is
$\sqrt{\gamma_i}|f\rangle\langle i|$ after that transport.
Each of the original modes $1,3$ has squared projection $1/2$ from
$|-\rangle$. Their reduced jump effects therefore have coefficient

$$
\frac12\left(\frac\nu k+\frac\nu{c-k}\right)
 \frac{x(c-k)}{k(c-x)}=\frac{c}{2(c-x)}f_x(t),
\tag{CG.17}
$$

while the mode-$2$ coefficient is $f_x(t)$. This recovers all five
separate CP densities, not just total survival.

The input populations in $(+,-,2)$ are $2x,2(c-x),Z$. Thus the traces
of these densities are exactly (CG.15), with weights $0,c,Z,c,0$
summing to $2c+Z=1$. Also

$$
K_x\psi_{x,\beta,m}=\sqrt{s_x}\psi_{x+d,\beta,m},\qquad
\int_0^1 f_x(t)\,dt=1-s_x.
\tag{CG.18}
$$

The phases are unchanged, so (CG.18) fixes the entire coherent live block.
For completeness on all of $V$, the integrated jump effects sum to

$$
(1-s_x)\left(P_2+\frac{c}{c-x}P_-\right)=I_V-K_x^*K_x.
\tag{CG.19}
$$

Hence the full law is trace preserving, the live trace is $s_x$, and the
failure trace is $1-s_x$. None of this identifies the different $K_x$
with one common processor available at an unresolved cut. $\square$

**Definition 4.2 (the fixed minimax quantity).** For one common map of
Definition 3.1, using the entire target (CG.15) and metric (CG.11), set

$$
E(\Phi)=\max_{(x,\beta,m)\in\mathcal H}
 \operatorname{dist}\bigl(\Phi(\rho_{x,\beta,m}),
                              \Omega_{x,\beta,m}\bigr),\qquad
E_* =\inf_{\Phi\ \mathrm{common\ CPTP}}E(\Phi).
\tag{CG.20}
$$

All twelve targets remain prescribed, including those not used in a
particular necessary lower test.

## 5. A four-history witness preserving quantum coherence

**Lemma 5.1 (weighted rank-one trace norm).** If $p,q$ are unit vectors,
$A,B\geq0$ and $r=\langle p,q\rangle$, then

$$
\bigl\|A|p\rangle\langle p|-B|q\rangle\langle q|\bigr\|_1
 =\sqrt{(A+B)^2-4AB|r|^2}.
\tag{CG.21}
$$

Proof. Suppose first that $A,B>0$ and the vectors are not parallel.
On their two-dimensional span the operator has trace $A-B$ and determinant
$-AB(1-|r|^2)<0$. Its two eigenvalues have opposite signs. The square of
the sum of their absolute
values is therefore
$(A-B)^2+4AB(1-|r|^2)=(A+B)^2-4AB|r|^2$.
When a weight is zero or the vectors are parallel, direct evaluation gives
the same formula. In particular, for $A=B=1$ the norm is
$2\sqrt{1-|r|^2}$. $\square$

**Proposition 5.2 (actual phase-paired inputs and their exact distance).**
Use the four histories

$$
\left(\frac5{256},0,0\right),\quad
\left(\frac5{256},\pi,0\right),\quad
\left(\frac{27}{256},0,0\right),\quad
\left(\frac{27}{256},\pi,0\right).
\tag{CG.22}
$$

For $0<y<64$ put

$$
b_y=\frac{\sqrt y\,|+\rangle+\sqrt{64-y}\,|-\rangle}{8},
\qquad Q_y=|b_y\rangle\langle b_y|.
\tag{CG.23}
$$

For $y=5,27$ define the mathematical phase averages

$$
\Gamma_y=\frac12\left(\rho_{y/256,0,0}+
                            \rho_{y/256,\pi,0}\right)
         =\frac{P_2+Q_y}{2}.
\tag{CG.24}
$$

They retain the $(+,-)$ coherence, and their input distance is exactly

$$
u=\frac{\sqrt{135}+\sqrt{2183}}{64},\qquad
\delta_{\rm in}=\operatorname{dist}(\Gamma_5,\Gamma_{27})
                   =\frac{\sqrt{1-u^2}}{2}.
\tag{CG.25}
$$

Proof. Each $b_y$ has norm one. From (CG.7), for $m=0$,
$\psi_{y/256,\beta,0}=(|2\rangle+e^{-i\beta}b_y)/\sqrt2$.
Averaging only $\beta=0,\pi$ cancels the entries between $|2\rangle$
and the other two directions. In the ordered basis $(+,-,2)$ it gives

$$
\Gamma_y=\frac1{128}
\begin{pmatrix}
y&\sqrt{y(64-y)}&0\\
\sqrt{y(64-y)}&64-y&0\\
0&0&64
\end{pmatrix}.
\tag{CG.26}
$$

In particular no diagonalization of the coherent $(+,-)$ block has been
imposed. The overlap is
$\langle b_5,b_{27}\rangle=(\sqrt{5\cdot27}+\sqrt{59\cdot37})/64=u$.
These positive unit vectors are not parallel, so $0<u<1$.
The common $P_2/2$ terms cancel. Lemma 5.1 gives

$$
\frac12\|\Gamma_5-\Gamma_{27}\|_1
 =\frac14\|Q_5-Q_{27}\|_1
 =\frac12\sqrt{1-u^2}.
\tag{CG.27}
$$

Adding a fixed independent state and discarding it are CPTP operations;
equivalently trace norms multiply under tensoring. Thus tensoring $\tau$
does not change this input distance. The averages are convex witnesses
among the actual histories of Proposition 2.2, not additional preparations,
extra specimens or readable mixture labels. $\square$

**Proposition 5.3 (exact complete output distance).** Let

$$
\Theta_y=\frac12\left(\Omega_{y/256,0,0}+
                           \Omega_{y/256,\pi,0}\right)
\qquad(y=5,27).
\tag{CG.28}
$$

Define

$$
v=\frac{\sqrt{363}+\sqrt{1643}}{64}.
\tag{CG.29}
$$

Their exact complete-output distance, retaining live coherence and all
marked failures, is

$$
\delta_{\rm out}=\operatorname{dist}(\Theta_5,\Theta_{27})
          =\frac3{11}+\frac{\sqrt{49-45v^2}}{22}.
\tag{CG.30}
$$

Proof. Equations (CG.13)–(CG.15) give, at every exact $t\in[0,1]$,

$$
\begin{aligned}
s_y&=\frac{y}{y+6},\qquad f_y(t)=\frac{6y}{(y+6t)^2},\\
(\Theta_y)_{\rm live}&=\frac{s_y}{2}(P_2+Q_{y+6}),\\
\bigl((\Theta_y)_i(t)\bigr)_{i=0}^4
       &=\left(0,\frac14,\frac12,\frac14,0\right)f_y(t)P_f.
\end{aligned}
\tag{CG.31}
$$

The live $(+,-)$ off-diagonal entry is
$s_y\sqrt{(y+6)(58-y)}/128$, so the live block is still coherent.
Its trace is $s_y$ and the integrated failure trace is $1-s_y$;
$\Theta_y$ is normalized without success renormalization. At the
endpoints, $s_5=5/11$ and $s_{27}=9/11$.

First evaluate every marked failure sector. Write $w=6t$, so

$$
f_5(t)-f_{27}(t)=
\frac{132(135-w^2)}{(5+w)^2(27+w)^2}>0
                   \qquad(0\leq w\leq6).
\tag{CG.32}
$$

The denominator is positive and $135-w^2\geq135-36>0$.
Each nonzero original-mode difference has this same sign and its own
weight in (CG.31). Since those weights sum to one, their summed norm is

$$
\begin{aligned}
\sum_{i=0}^4\int_0^1
 \|(\Theta_5)_i(t)-(\Theta_{27})_i(t)\|_1\,dt
 &=\int_0^1(f_5(t)-f_{27}(t))\,dt\\
 &=(1-s_5)-(1-s_{27})=\frac4{11}.
\end{aligned}
\tag{CG.33}
$$

Modes $0$ and $13$ contribute zero, not omitted outcomes. This equality
sums exact-time norms with the original labels still present.

Next evaluate the quantum live block. Its $P_2$ part has norm
$(s_{27}-s_5)/2=2/11$. Its orthogonal $(+,-)$ part, up to an overall
sign, is

$$
\frac9{22}Q_{33}-\frac5{22}Q_{11},\qquad
\langle b_{11},b_{33}\rangle
       =\frac{\sqrt{11\cdot33}+\sqrt{53\cdot31}}{64}=v.
\tag{CG.34}
$$

Again $0<v<1$. With $A=9/22$ and $B=5/22$, Lemma 5.1 gives

$$
\left\|\frac9{22}Q_{33}-\frac5{22}Q_{11}\right\|_1
 =\sqrt{\left(\frac7{11}\right)^2-
                         \frac{45}{121}v^2}
 =\frac{\sqrt{49-45v^2}}{11}.
\tag{CG.35}
$$

The two live subspaces and all classical failure sectors are orthogonal
direct summands for this difference. Applying the one-half factor in
(CG.11) to their total norm therefore yields

$$
\delta_{\rm out}=\frac12\left(
       \frac4{11}+\frac2{11}+\frac{\sqrt{49-45v^2}}{11}\right)
       =\frac3{11}+\frac{\sqrt{49-45v^2}}{22}.
\tag{CG.36}
$$

This is the entire cq distance, not just a survival-event discrepancy.
$\square$

## 6. The common-channel obstruction and its strict quantitative gap

**Theorem 6.1 (complete-output lower bound).** For every common CPTP map
of Definition 3.1,

$$
E(\Phi)\geq L_{\rm full},\qquad
E_*\geq L_{\rm full},
\tag{CG.37}
$$

where the exact constant is

$$
\boxed{L_{\rm full}=\frac3{22}
       +\frac{\sqrt{49-45v^2}}{44}
       -\frac{\sqrt{1-u^2}}4},\qquad
u=\frac{\sqrt{135}+\sqrt{2183}}{64},\quad
v=\frac{\sqrt{363}+\sqrt{1643}}{64}.
\tag{CG.38}
$$

Proof. Put $E=E(\Phi)$. Linearity and trace-norm convexity, applied to
the two actual histories at each endpoint, give

$$
\begin{aligned}
\operatorname{dist}(\Phi(\Gamma_y),\Theta_y)
 &\leq\frac12\operatorname{dist}
       (\Phi(\rho_{y/256,0,0}),\Omega_{y/256,0,0})\\
 &\quad+\frac12\operatorname{dist}
       (\Phi(\rho_{y/256,\pi,0}),\Omega_{y/256,\pi,0})
 \leq E\qquad(y=5,27).
\end{aligned}
\tag{CG.39}
$$

For clarity, contractivity here includes the full measurable-time output.
For any Hermitian input $H=H_+-H_-$, positivity and trace preservation
imply

$$
\|\Phi(H)\|_{1,\mathrm{cq}}
 \leq\|\Phi(H_+)\|_{1,\mathrm{cq}}+
          \|\Phi(H_-)\|_{1,\mathrm{cq}}
 =\operatorname{tr}H_++\operatorname{tr}H_-=\|H\|_1.
\tag{CG.40}
$$

A positive cq measure has norm equal to its total trace, so this argument
requires no finite time alphabet. It includes any singular events and
extra sectors. Consequently
$\operatorname{dist}(\Phi(\Gamma_5),\Phi(\Gamma_{27}))
\leq\delta_{\rm in}$. The triangle inequality now gives

$$
\begin{aligned}
\delta_{\rm out}
 &\leq\operatorname{dist}(\Theta_5,\Phi(\Gamma_5))
      +\operatorname{dist}(\Phi(\Gamma_5),\Phi(\Gamma_{27}))
      +\operatorname{dist}(\Phi(\Gamma_{27}),\Theta_{27})\\
 &\leq2E+\delta_{\rm in}.
\end{aligned}
\tag{CG.41}
$$

Substituting (CG.25) and (CG.30) proves
$E\geq(\delta_{\rm out}-\delta_{\rm in})/2=L_{\rm full}$,
with exactly the factors in (CG.38).

Independent ancillas and randomness are already inside the common map.
Abort and rejection outputs, and any simulated outcomes of zero ideal
weight, stay in the two error norms in (CG.39); no acceptance denominator
can remove them. A processor required to handle all twelve histories must
handle (CG.22) with their original targets. This restriction supplies a
necessary test and does not alter the other eight targets. Finally the
constant is independent of $\Phi$, so taking its infimum proves the
second inequality in (CG.37). No compactness or attainment assumption is
used. $\square$

**Corollary 6.2 (strict separation from the supplied baseline).**

$$
L_{\rm full}>\frac{53}{528}>\frac1{22},\qquad
E_*-\frac1{22}>\frac{29}{528}.
\tag{CG.42}
$$

Thus, in this fixed complete-output experiment, $1/22$ can neither be
attained nor approached by the common CPTP comparison class.

Proof. Every radical comparison below is between positive quantities, so
squaring preserves order. The exact rational differences

$$
135-\left(\frac{58}{5}\right)^2=\frac{11}{25}>0,\qquad
2183-\left(\frac{233}{5}\right)^2=\frac{286}{25}>0
\tag{CG.43}
$$

imply $u>291/320>10/11$, the last inequality being $3201>3200$.
Together with $u<1$ this yields

$$
\delta_{\rm in}<\frac{\sqrt{21}}{22}<\frac5{24},
\qquad \left(\frac{55}{12}\right)^2-21=\frac1{144}>0.
\tag{CG.44}
$$

For the other overlap,

$$
\left(\frac{77}{4}\right)^2-363=\frac{121}{16}>0,\qquad
\left(\frac{163}{4}\right)^2-1643=\frac{281}{16}>0
\tag{CG.45}
$$

imply $0<v<15/16$. Therefore

$$
49-45v^2>\frac{2419}{256}>9,\qquad
\frac{2419}{256}-9=\frac{115}{256}>0,
\tag{CG.46}
$$

and (CG.30) gives $\delta_{\rm out}>9/22$.
It follows that

$$
L_{\rm full}=\frac{\delta_{\rm out}-\delta_{\rm in}}2
 >\frac12\left(\frac9{22}-\frac5{24}\right)=\frac{53}{528}.
\tag{CG.47}
$$

Since $1/22=24/528$, (CG.37) proves the claimed gap exceeding
$29/528$. These positive rational squarings and the preceding norm
identities are ordinary analytic arguments. $\square$

## 7. The credited baseline, attribution and remaining boundary

**Comparison 7.1 (what the supplied $D/2$ bound says).** In [AC, Lemma
3.2 and Theorem 6.1][AC], averaging both phases and both parities gives

$$
\bar\rho_x=\frac14\sum_{\beta\in\{0,\pi\},\ m\in\{0,1\}}
 \rho_{x,\beta,m}=2xP_++2(c-x)P_-+ZP_2.
\tag{CG.48}
$$

Hence $\bar\rho_a=(\bar\rho_{a-h}+\bar\rho_{a+h})/2$.
Writing $\bar\Omega_x$ for the corresponding complete ideal output
average, the supplied Corollary 6.2 computes the exact mixture defect

$$
D=\operatorname{dist}\left(\bar\Omega_a,
          \frac{\bar\Omega_{a-h}+\bar\Omega_{a+h}}2\right)
   =\frac1{11}.
\tag{CG.49}
$$

The source evaluates this defect with its full live block and marked
failure laws, not merely a survival bit. Its affinity and triangle
argument gives $E(\Phi)\geq D/2=1/22$. This is a credited lower bound;
it was not an exact full-output minimax result. Equation (CG.48) cancels
the $(+,-)$ coherence by parity averaging. In contrast, (CG.24) cancels
only the coherences involving $|2\rangle$ and retains the coherent block
that appears in (CG.35). That endpoint calculation, together with the
separate marked-failure contribution (CG.33), yields (CG.38)–(CG.42).
The old mixture-defect identity remains valid.

**Attribution 7.2 (premises and additional deduction).** The fixed source
is [Acquired Continuation Limits][AC] at commit
`11e2a65d554143d0e3f38b37f1b686453451e3c4`, with the precise uses below.

| Fixed source location | Credited mathematical input |
| --- | --- |
| [AC] §§2–3, (AC.1)–(AC.6), Proposition 3.1 | Original class, preparation, actual histories, real lifts and positive old live-cut masses. |
| [AC] Definitions 2.3–2.5, (AC.4) | Sole specimen, fixed common inputs, legality and permissions, all-outcome comparison and complete cq half trace norm. |
| [AC] §4, (AC.8)–(AC.10) | Source-indexed calibrated CP law, coherent live successors, original-mode and exact-time stopped outputs. |
| [AC] §6, Theorem 6.1 and Corollary 6.2 | The separate exact defect $D=1/11$ and necessary lower bound $D/2=1/22$. |

The actual synthesis and composition are credited there to
[FiniteRectangleTransport's owning Scribe][FRT] and
[OriginalControlComposition's owning Scribe][OCC]. The calibrated
instrument is credited to [Instrument Boundaries][IB] §§4–5.2 and
17.1–17.2, including (OC.55)–(OC.58). These nested sources are fixed at
`1f58736f50945c7cfeca93ce160eb9b46a3a7e7e` in [AC]; they are credited
premises, not additional results established by this volume.

The added result consists of the two-phase endpoint witnesses, the exact
input distance (CG.25), the full coherent and marked output distance
(CG.30), and the resulting uniform gap (CG.42). The norm and channel tools
are mature. No external literature search or independent literature
originality conclusion is asserted.

**Open problem 7.3 (exact full-output minimax).** The exact value of
$E_*$ and an attaining common simulator remain unresolved here. The proof
provides a strict lower bound, not a matching construction or a proof that
$L_{\rm full}$ is optimal.

All assertions are confined to (CG.1)–(CG.2), normalized at the reached
old live cut with the common-input premise of Definition 3.1. They do not
replace the source's separate unconditional-prefix analysis, construct an
acquisition protocol or actuator, or rule out earlier source-sensitive
assistance or every original control. No bridge to KBONACCI, N2 or PCA,
no general neural-network or empirical learning result, no physical
implementation or efficiency theorem, and no completion of the broader
programme follows from this fixed experiment.

[AC]: https://github.com/the-omega-institute/trureturing/blob/11e2a65d554143d0e3f38b37f1b686453451e3c4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_ACQUIRED_CONTINUATION_LIMITS.md
[FRT]: https://github.com/the-omega-institute/trureturing/blob/1f58736f50945c7cfeca93ce160eb9b46a3a7e7e/Blueprint/D5/S3/Quantum/Fibers/FiniteRectangleTransport.scribe.cs
[OCC]: https://github.com/the-omega-institute/trureturing/blob/1f58736f50945c7cfeca93ce160eb9b46a3a7e7e/Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.scribe.cs
[IB]: https://github.com/the-omega-institute/trureturing/blob/1f58736f50945c7cfeca93ce160eb9b46a3a7e7e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md

## 追加锚（本行以下为增补区）

## 8. Common channel compatibility and exact-time attainment

**Convention 8.1 (the unchanged comparison class).** Sections 8–11 use
exactly (CG.20): one normalized specimen at the already reached old live
cut, the same fixed metadata and blanks, all twelve actual histories
(CG.2), and the entire targets (CG.15). Write

$$
y=256x\in\{5,16,27\},\qquad
W=\operatorname{span}\{|+\rangle,|-\rangle\},\qquad
s_y=\frac{y}{y+6},\quad f_y(t)=\frac{6y}{(y+6t)^2},\qquad
(w_0,w_1,w_2,w_3,w_4)=\left(0,\frac14,\frac12,\frac14,0\right).
\tag{CG.50}
$$

Here $s_y,f_y$ are the dimensionless versions of (CG.13); index $4$
still names original mode $13$. The class is the expressly enlarged class
of all common CPTP maps, including countably additive simulated exact-time
laws with atoms or singular continuous parts. It is not a subclass defined
by finite physical implementations. All error norms count every outcome.
The different old live masses (CG.8) are neither priors nor acceptance
weights in this normalized problem. The original calibrated source,
permissions, real lifts and literal continuation convention remain those
of §§2–4; no new original actuator, helper, source parameter or port is
supplied by this comparison.

**Proposition 8.2 (target-fixing canonical reduction).** The infimum in
(CG.20) is unchanged if the output consists of a live matrix on $V$, five
scalar measures on the separately labelled time intervals $[0,1]$, each
with stopped state $P_f$, and one scalar other outcome. All zero-target
output mass, including abort and rejection, remains counted.

Proof. Apply the same output operation to every candidate. In its live
sector compress to $V$, sending the trace of the orthogonal compression
to other; discard cross terms between these orthogonal subspaces. This
is a CP trace-preserving operation: its retained branch is a compression
and its other branch is a positive trace functional. At each stopped
mode and exact time, replace the quantum state by its trace times $P_f$,
keeping that mode and time. Pool all further zero-target sectors into the
scalar other outcome. Fixed common metadata may be discarded and
reappended in their same fixed state. These operations compose to one
common CPTP map and fix each target (CG.15).

The output contraction argument (CG.40), applied to this common operation,
shows that none of the twelve errors increases. Pooling zero-target
positive sectors retains their entire trace contribution: their norm is
the sum of their masses before pooling and the same total mass afterwards.
No outcome is deleted and no branch is normalized by success. The five
original stopped intervals are not pooled or binned. Conversely a reduced
channel is a candidate in the enlarged class, with its other outcome
embedded as a declared zero-target event and the fixed metadata appended.
Thus reduced candidates have infimum at least the full infimum, whereas
the reduction gives the reverse inequality. $\square$

**Lemma 8.3 (one joint Choi–measure condition).** Let

$$
K=\coprod_{i=0}^4\bigl(\{i\}\times[0,1]\bigr)\ \sqcup\ \{\mathrm o\},
\tag{CG.51}
$$

with the disjoint-union compact metric topology and isolated other point
$\mathrm o$. A reduced common channel is equivalent to a pair $(J,B)$,
where $J\geq0$ is a matrix on $V_{\rm in}\otimes V_{\rm live}$ and
$B$ is a positive $3$ by $3$ matrix-valued finite Borel measure on $K$,
countably additive entrywise, such that

$$
\operatorname{Tr}_{\rm live}J+B(K)=I_V.
\tag{CG.52}
$$

In the fixed basis $(+,-,2)$, its live matrix and scalar record measure
on an input $\rho$ are

$$
L_\rho=\operatorname{Tr}_{\rm in}[(\rho^T\otimes I_V)J],\qquad
\mu_\rho(A)=\operatorname{tr}(\rho^T B(A))\quad(A\subseteq K\text{ Borel}).
\tag{CG.53}
$$

Proof. Use the Choi convention

$$
J=\sum_{a,b}|a\rangle\langle b|\otimes
                   \Phi_{\rm live}(|a\rangle\langle b|).
\tag{CG.54}
$$

The CP Choi correspondence gives positivity of $J$ and the first formula
in (CG.53). Each scalar record branch has a positive effect $E(A)$;
put $B(A)=E(A)^T$. Its output is
$\operatorname{tr}(\rho E(A))=\operatorname{tr}(\rho^T B(A))$.
Entrywise countable additivity follows from that of the output laws and
linearity on a finite matrix basis. Trace preservation for every $\rho$
then gives (CG.52). In particular $\operatorname{Tr}_{\rm live}J$
is the transpose of the live effect, so the two terms in (CG.52) use
the same transpose convention.

Conversely, a positive $J$ gives its CP live map by (CG.53).
Each $B(A)^T$ is positive and defines a CP scalar-output map: diagonalizing
this effect expresses its trace functional as a sum of positive rank-one
Kraus branches. The countably additive family of these effects defines
the scalar record instrument, with $P_f$ prepared on each stopped branch.
Equivalently every finite Borel partition gives CP branches, also after
tensoring an arbitrary reference identity; their countable sums have the
specified measures. Equation (CG.52) makes the total output trace
$\operatorname{tr}(\rho^T I_V)=\operatorname{tr}\rho$.
This proves sufficiency for a single CPTP channel. It does not permit
independently selecting an output for each history. $\square$

**Theorem 8.4 (attainment with arbitrary countably additive time laws).**
There is a common channel $\Phi_{\min}$ in the enlarged class (CG.20)
with $E(\Phi_{\min})=E_*$. Its time laws need not have densities.

Proof. The class is nonempty, for example by the channel that always
returns other, and its errors lie in $[0,1]$. By Proposition 8.2 take a
minimizing sequence represented by $(J_n,B_n)$ of Lemma 8.3. Taking the
trace of (CG.52) gives

$$
\operatorname{tr}J_n+\operatorname{tr}B_n(K)=3.
\tag{CG.55}
$$

Thus the positive matrices $J_n$ have a convergent subsequence with
positive limit $J$. Every component of $B_n$ has uniformly bounded total
variation. Indeed, for every finite Borel partition $(A_j)$, positivity
and Cauchy–Schwarz give

$$
\sum_j|(B_n)_{ab}(A_j)|
 \leq\sum_j\sqrt{(B_n)_{aa}(A_j)(B_n)_{bb}(A_j)}
 \leq\sqrt{(B_n)_{aa}(K)(B_n)_{bb}(K)}\leq3.
\tag{CG.56}
$$

Choose a countable uniformly dense family of real continuous functions
on compact metric $K$, including $1$. A diagonal subsequence makes their
integrals against the real and imaginary parts of all nine components
converge. The uniform variation bound extends these limits, by uniform
approximation, to bounded linear functionals on all continuous functions.
For every vector $z$ and nonnegative continuous function $h$, the limit
of $\int h\,d(z^\dagger B_nz)$ is nonnegative. Riesz–Markov
representation of positive functionals on $C(K)$, and polarization in
$z$, therefore supply a positive matrix-valued regular Borel measure $B$
with these component functionals. Its components are genuine countably
additive measures. No finitely additive completion is used. Testing the
constant $1$ passes (CG.52) to the limit. Thus $(J,B)$ is feasible.

It remains to check the topology against the complete error, rather than
assume norm compactness of measures. For each fixed history, (CG.53)
gives matrix convergence of $L_{\rho,n}$, hence continuity of its live
trace-norm error, and weak convergence of $\mu_{\rho,n}$ against all
continuous functions on $K$. Write $\nu_\rho$ for the fixed target
record measure, having densities $w_i f_y(t)$ and zero other mass.
For a finite real signed regular measure $\xi$ on compact metric $K$,

$$
\|\xi\|_{\rm TV}
 =\sup_{h\in C(K;\mathbb R),\ \|h\|_\infty\leq1}
                         \left|\int_K h\,d\xi\right|.
\tag{CG.57}
$$

The inequality from right to left follows from the definition of total
variation. For the reverse inequality, approximate the positive and
negative Hahn sets by disjoint compact subsets in their respective
variation measures. A continuous function bounded by one can equal
$+1$ and $-1$ on these two compact subsets. The omitted variation tends
to zero by regularity, proving the formula. Each integral on the right
is continuous in the convergence just obtained, so the supremum is lower
semicontinuous. Consequently

$$
\frac12\left(\|L_\rho-(\Omega_\rho)_{\rm live}\|_1
                         +\|\mu_\rho-\nu_\rho\|_{\rm TV}\right)
\tag{CG.58}
$$

is lower semicontinuous, as is the maximum of these twelve expressions.
On the disjoint space $K$, its variation is exactly the sum over all
five labelled intervals and other; atoms and singular continuous mass
are included. The limiting channel has error at most the liminf of the
minimizing errors, namely $E_*$. Membership in the same class supplies
the reverse inequality, proving equality. This is existence in the
all-common-CPTP class; it gives no finite description, finite event
storage or physical implementation of the limiting channel. $\square$

## 9. Equality at the coherent lower bound is impossible

**Lemma 9.1 (covariance from the actual sign catalogue).** In the reduced
class it suffices, for minimizing error or testing equality at a universal
lower bound, to consider channels covariant under

$$
G=\{U_{a,b}=\operatorname{diag}((-1)^a,(-1)^b,1):a,b\in\{0,1\}\}.
\tag{CG.59}
$$

The action conjugates the live output and fixes every scalar record.

Proof. Put $j=\beta/\pi$. The actual vector (CG.7) has signs
$((-1)^j,(-1)^{j+m},1)$. The unitary $U_{a,b}$ sends its bits to
$(j+a,m+a+b)$ modulo two. This permutes the four actual histories at
each height, and permutes their live targets in precisely the same way.
The stopped targets depend only on height and remain fixed. With
$\mathcal U_g$ denoting the indicated output action, define

$$
\overline\Phi(\rho)=\frac14\sum_{g\in G}
           \mathcal U_g\bigl(\Phi(U_g^\dagger\rho U_g)\bigr).
\tag{CG.60}
$$

This is one CPTP map and is covariant by reindexing the group sum.
For each history, unitary invariance and convexity bound its error by
the average of the four permuted errors of $\Phi$ at that height.
Thus $E(\overline\Phi)\leq E(\Phi)$. The reduction of Proposition 8.2
commutes with this action. If $E(\Phi)=L_{\rm full}$, (CG.37) forces
both reductions to retain equality. These operations are in the enlarged
comparison class and confer no newly acquired original source operation.
$\square$

**Lemma 9.2 (two preserved bases into three live dimensions).** Let
$\Psi:M(W)\to M(V)$ be CP and trace preserving, with
$\dim W=2$ and $\dim V=3$. Let $e_+,e_-$ be an orthonormal basis and

$$
f_+=\alpha e_++\beta e_-,\qquad
f_-=-\beta e_++\alpha e_-,\qquad
\alpha,\beta\in\mathbb R,\quad \alpha^2+\beta^2=1,\quad\alpha\beta\ne0.
\tag{CG.61}
$$

If the two outputs within each of these bases have orthogonal supports,
then $\Psi(\rho)=T_0\rho T_0^\dagger$ for an isometry $T_0:W\to V$.

Proof. A spectral factorization of the positive Choi matrix supplies
finite Kraus operators for $\Psi$. Trace preservation makes their Kraus
dilation an isometry $T:W\to V\otimes\mathcal E$. Put $u=Te_+$,
$v=Te_-$. Orthogonality of their reduced live supports implies
$u\in S_+\otimes\mathcal E$ and $v\in S_-\otimes\mathcal E$ with
$S_+\perp S_-$. Hence for every environment operator $R$ both cross
matrix elements $\langle u,(I\otimes R)v\rangle$ and
$\langle v,(I\otimes R)u\rangle$ vanish. The second preserved basis
likewise gives

$$
\begin{aligned}
0&=\langle\alpha u+\beta v,
                    (I\otimes R)(-\beta u+\alpha v)\rangle\\
 &=\alpha\beta\bigl(\langle v,(I\otimes R)v\rangle
                         -\langle u,(I\otimes R)u\rangle\bigr).
\end{aligned}
\tag{CG.62}
$$

Thus the two environment marginals are the same density matrix $\sigma$.
In a common eigenbasis for its positive eigenvalues $\lambda_r$, write

$$
u=\sum_r\sqrt{\lambda_r}\,a_r\otimes r,\qquad
v=\sum_r\sqrt{\lambda_r}\,b_r\otimes r.
\tag{CG.63}
$$

Both families $a_r$ and $b_r$ are orthonormal, as follows by evaluating
the matrix entries of the common environment marginal. Moreover every
$a_r$ is orthogonal to every $b_s$ since $S_+\perp S_-$. Therefore
$2\operatorname{rank}\sigma\leq3$. Since $\operatorname{tr}\sigma=1$,
its rank is one. The two dilation vectors share a single environment
factor. Sending $e_+,e_-$ to their respective orthonormal live factors
defines $T_0$, and linearity, including the cross operators, gives the
asserted channel on every $\rho$. This uses complete positivity and the
three-dimensional output hypothesis. $\square$

**Theorem 9.3 (strict nonoptimality of $L_{\rm full}$).** Every common
channel in (CG.20) has error strictly greater than $L_{\rm full}$, and

$$
L_{\rm full}<E_*.
\tag{CG.64}
$$

Proof. Suppose a channel had $E(\Phi)=L_{\rm full}$. By Proposition 8.2,
Lemma 9.1 and the universal bound (CG.37), take it reduced and covariant
with the same error. Use the actual phase averages $\Gamma_y,\Theta_y$
of (CG.24) and (CG.28), only for $y=5,27$. Put
$H=\Gamma_5-\Gamma_{27}$ and $X=\Theta_5-\Theta_{27}$. The previously
computed exact distances give

$$
\|X\|_{1,\rm cq}=4L_{\rm full}+\|H\|_1.
\tag{CG.65}
$$

In the identity

$$
X=(\Theta_5-\Phi\Gamma_5)+\Phi H+(\Phi\Gamma_{27}-\Theta_{27}),
\tag{CG.66}
$$

the first and last norms are at most $2E(\Phi)$ by convexity over their
two actual histories, while $\|\Phi H\|_{1,\rm cq}\leq\|H\|_1$.
At the supposed equality, (CG.65) forces all these estimates and the
triangle inequality to be equalities.

Choose a norming Hermitian contraction $D$ for $X$ as follows: on the
live block take its spectral sign, and on every stopped sector and other
point take $+1$. This norms the entire $X$. Indeed (CG.32) gives
$f_5(t)-f_{27}(t)>0$ at every time; all nonzero marked weights are
positive, and the remaining record differences are zero. The choice
$+1$ is also valid on every zero-target mode and on arbitrary singular
simulated events. Pairing (CG.66) with this same $D$ and using the saturated
sum of bounds forces

$$
\langle D,\Phi H\rangle=\|H\|_1.
\tag{CG.67}
$$

Otherwise that pairing would be strictly smaller than $\|X\|_{1,\rm cq}$.

On $W$, the input difference is the real matrix

$$
H=\frac1{128}\begin{pmatrix}-22&\zeta\\\zeta&22\end{pmatrix},\qquad
\zeta=\sqrt{295}-\sqrt{999}\ne0.
\tag{CG.68}
$$

It is zero on $|2\rangle$, and its $W$ eigenvalues are
$\pm\lambda$, where $\lambda=\sqrt{484+\zeta^2}/128>0$.
Choose real unit eigenvectors $e_+,e_-$. Both coordinates of each are
nonzero, since a coordinate eigenvector would contradict the nonzero
off-diagonal entry. Write $R=\Phi^\dagger(D)$ for the dual pullback.
Unital positivity gives $-I\leq R\leq I$. Equation (CG.67) becomes

$$
\lambda\bigl(\langle e_+,Re_+\rangle-\langle e_-,Re_-\rangle\bigr)
                         =2\lambda.
\tag{CG.69}
$$

The two expectations must be $1$ and $-1$. Positivity of $I-R$ and
$I+R$ makes the corresponding vectors eigenvectors of $R$. Thus for
$A=\Phi^\dagger((I+D)/2)$ its $W$ compression is
$|e_+\rangle\langle e_+|$.

Let $F$ be the input effect of the whole nonlive output, including all
mode/time and other mass. Because $D=+1$ on that event, $0\leq F\leq A$.
Covariance makes $F$ invariant under both independent coordinate signs,
so $F$ is diagonal in $(+,-,2)$. Its $W$ compression is a nonnegative
diagonal matrix $\operatorname{diag}(f_+,f_-)$ dominated by
$|e_+\rangle\langle e_+|$. Testing in $e_-$ gives

$$
0\leq f_+|\langle+|e_-\rangle|^2+
       f_-|\langle-|e_-\rangle|^2\leq0.
\tag{CG.70}
$$

Both squared coordinates are positive, so $f_+=f_-=0$. Every positive
$W$-supported input therefore has no nonlive output. Its live restriction
$\Psi:M(W)\to M(V)$ is CP and trace preserving. Equality above gives
$\|\Psi(H)\|_1=\|H\|_1$; covariance also gives the same equality for
$UHU^\dagger$, with $U=\operatorname{diag}(1,-1)$ on $W$.

For two density matrices, trace distance one forces orthogonal supports:
a norming Hermitian contraction for their difference must have expectation
$+1$ on one and $-1$ on the other, placing their supports in its disjoint
$+1$ and $-1$ eigenspaces. Applying this to
$H=\lambda(P_{e_+}-P_{e_-})$ shows that $\Psi(P_{e_+})$ and
$\Psi(P_{e_-})$ have orthogonal supports. The same is true for the
eigenbasis of $UHU^\dagger$.

These bases meet the nonzero-overlap hypothesis of Lemma 9.2. In fact
$P_{e_+}=(I_W+H/\lambda)/2$ gives directly

$$
\langle e_+,Ue_+\rangle=\frac{-22}{\sqrt{484+\zeta^2}}.
\tag{CG.71}
$$

Its absolute value is strictly between zero and one. Up to real phase
choices the rotated basis therefore has form (CG.61), with
$\alpha^2=484/(484+\zeta^2)$ and
$\beta^2=\zeta^2/(484+\zeta^2)$. Lemma 9.2 implies
$\Psi(\rho)=T_0\rho T_0^\dagger$ for a single isometry.

The group element $U_0=\operatorname{diag}(-1,-1,1)$ fixes every
$W$-supported input operator by conjugation. Covariance consequently fixes
each pure output $|T_0z\rangle\langle T_0z|$ under $U_0$. Each nonzero
vector in $\operatorname{range}T_0$ is an eigenvector of $U_0$.
A linear subspace with this property lies in one eigenspace, since a sum
of nonzero vectors from the opposite eigenspaces is not an eigenvector.
The $+1$ eigenspace has dimension one, while this range has dimension
two. Hence $\operatorname{range}T_0=W$.

Now test the output event terminal live and in $W$ on
$\Gamma_5=(P_2+Q_5)/2$. Its simulated probability is at least $1/2$:
the $Q_5/2$ part goes isometrically into $W$, and the $P_2/2$ part
contributes nonnegative mass. Its ideal probability in $\Theta_5$ is
$s_5/2=5/22$. Complete half trace distance dominates an event probability
difference. Explicitly, for a normalized-output difference $\Delta$ and
an event effect $Q$, pairing with $2Q-I$ gives
$|\operatorname{tr}Q\Delta|\leq\|\Delta\|_{1,\rm cq}/2$.
Thus

$$
\operatorname{dist}(\Phi\Gamma_5,\Theta_5)
                         \geq\frac12-\frac5{22}=\frac3{11}.
\tag{CG.72}
$$

Yet (CG.39) bounds this by $L_{\rm full}<3/11$. To check the last strict
inequality symbolically, (CG.29) gives
$v>(18+40)/64=29/32>2/3$, using $363>18^2$ and $1643>40^2$.
Therefore $\sqrt{49-45v^2}<\sqrt{29}<6$, whence
$\delta_{\rm out}<6/11$ and
$L_{\rm full}=(\delta_{\rm out}-\delta_{\rm in})/2<3/11$.
This contradicts (CG.72).

No channel can attain the old lower bound. Theorem 8.4 supplies an actual
minimizer in the same enlarged class; if $E_*=L_{\rm full}$, that
minimizer would contradict the result just proved. Together with (CG.37)
this proves (CG.64). Attainment is essential to this last infimum step;
excluding equality for individual channels alone would not give a strict
infimum gap. No explicit positive size for $E_*-L_{\rm full}$ is obtained.
The auxiliary $W$-supported operators are linear tests of the channel,
not additional supplied preparations or specimens. $\square$

## 10. One common processor with exact complete twelve-history error

**Proposition 10.1 (a fixed feasible processor).** Define

$$
g(t)=\frac{f_5(t)+f_{27}(t)}2,
\qquad (\Phi_0\rho)_{\rm live}=\frac7{11}\rho,\qquad
(\Phi_0\rho)_i(dt)=w_i g(t)\operatorname{tr}(\rho)P_f\,dt
                         \quad(i=0,\ldots,4).
\tag{CG.73}
$$

There is no other output mass. This is one common CPTP map on all $V$.

Proof. The live branch is a positive scalar multiple of the identity
channel and every stopped branch is CP trace-and-prepare. The endpoint
failure masses are $1-s_5=6/11$ and $1-s_{27}=2/11$, so

$$
\int_0^1g(t)\,dt=\frac4{11},\qquad
\frac7{11}+\sum_iw_i\int_0^1g(t)\,dt=1.
\tag{CG.74}
$$

Thus the joint map is trace preserving. Its constants use only the fixed
public catalogue, not the actual height or either sign. One ideal
realization keeps the old specimen live with independent probability
$7/11$; otherwise it resets that specimen into the absorbing stopped
state, chooses the original mode with distribution $(w_i)$ and records
an exact time with normalized density $(11/4)g(t)$. There is no operation
after failure. This is a specification of a common simulated output law
in the enlarged class, with the same ideal measurable-time convention
as (CG.20), not a finite physical sampling or source-actuation theorem.
It requires no copy, replacement, callback, source parameter, helper or
new acceptance event. Fixed common metadata are carried identically.
Both zero-weight original modes remain named. $\square$

**Theorem 10.2 (the exact achieved error).** Put

$$
r_y=\frac12+
\frac{\sqrt{y(y+6)}+\sqrt{(64-y)(58-y)}}{128}
                         \quad(y\in\{5,16,27\}).
\tag{CG.75}
$$

The error of the single processor (CG.73), over all twelve histories and
their complete outputs, is exactly

$$
E(\Phi_0)=M=\frac1{22}\max\left\{
2+\sqrt{144-140r_5^2},\quad
1+\sqrt{225-224r_{16}^2},\quad
2+\sqrt{256-252r_{27}^2}\right\}.
\tag{CG.76}
$$

Proof. For every one of the four actual sign choices at a height $y$,
the inner product of the input vector and its shifted target vector is
$r_y$: the signs cancel coordinate by coordinate in (CG.7). Lemma 5.1
therefore gives the live-block difference norm

$$
N_y=\sqrt{(7/11+s_y)^2-4(7/11)s_y r_y^2}.
\tag{CG.77}
$$

The stopped blocks have the same nonnegative weights $(w_i)$ summing to
one. With their original labels and exact times kept separate, their
summed difference norm is

$$
a_y=\sum_iw_i\int_0^1|g(t)-f_y(t)|\,dt
                    =\int_0^1|g(t)-f_y(t)|\,dt.
\tag{CG.78}
$$

The complete error for every sign history at that height is
$(N_y+a_y)/2$. There is no success renormalization.

By (CG.32), $f_5>f_{27}$ pointwise, so
$a_5=a_{27}=\tfrac12\int(f_5-f_{27})=2/11$.
For the middle height, the sign of the density difference must also be
checked. Set $w=6t$ and subtract the survival functions to obtain

$$
J_0(t)=\frac{16}{16+w}-\frac12\left(\frac5{5+w}+\frac{27}{27+w}\right)
       =\frac{121w}{(w+5)(w+16)(w+27)}.
\tag{CG.79}
$$

This is the specialization of [AC, (AC.21)][AC]. A direct derivative
check is as follows. The denominator before squaring is
$D(w)=w^3+48w^2+647w+2160$, so

$$
\begin{aligned}
D(w)-wD'(w)&=-2w^3-48w^2+2160\\
           &=2(6-w)(w^2+30w+180),\\
J_0'(t)&=g(t)-f_{16}(t)
 =6\,\frac{242(6-w)(w^2+30w+180)}
              {(w+5)^2(w+16)^2(w+27)^2}\geq0
                         \quad(0\leq w\leq6).
\end{aligned}
\tag{CG.80}
$$

The factor $6$ is the time/displacement chain factor. It follows that

$$
a_{16}=\int_0^1(g-f_{16})\,dt
                       =\frac4{11}-\frac3{11}=\frac1{11}.
\tag{CG.81}
$$

This evaluates the full exact-time variation, rather than inferring it
from total survival alone. Substituting $s_5=5/11$, $s_{16}=8/11$ and
$s_{27}=9/11$ into (CG.77)–(CG.81) gives the three expressions in
(CG.76). Each applies to all four sign histories at that height, so
their maximum is exactly the twelve-history error of one common map.
No maximizing height or optimality over processors is asserted. $\square$

**Corollary 10.3 (symbolic strict upper comparison).**

$$
\boxed{L_{\rm full}<E_*\leq M
 <\frac{128+\sqrt{32449}}{1408}
 <\frac{39}{176}<\frac29.}
\tag{CG.82}
$$

Proof. For $5\leq y\leq27$ write

$$
\begin{aligned}
A_y&=(\sqrt{y+6}-\sqrt y)^2+
                  (\sqrt{64-y}-\sqrt{58-y})^2,\\
r_y&=1-\frac{A_y}{256},\\
A_y&=\frac{36}{(\sqrt{y+6}+\sqrt y)^2}
        +\frac{36}{(\sqrt{64-y}+\sqrt{58-y})^2}.
\end{aligned}
\tag{CG.83}
$$

These are expansion and rationalization identities. The first denominator
is greater than $25$, since $\sqrt{11}>3$ and $\sqrt5>2$.
The second is greater than $121$, since $\sqrt{37}>6$ and
$\sqrt{31}>5$. Hence

$$
A_y<\frac{36}{25}+\frac{36}{121}=\frac{5256}{3025}<2,\qquad
r_y>\frac{127}{128},\qquad 1-r_y^2<\frac{255}{16384}.
\tag{CG.84}
$$

At the three catalogue heights,
$|7/11-s_y|\leq2/11$ and $4(7/11)s_y\leq252/121$. Thus

$$
N_y^2=(7/11-s_y)^2+4(7/11)s_y(1-r_y^2)
 <\frac{4+252(255/16384)}{121}
 =\frac{32449}{4096\cdot121}.
\tag{CG.85}
$$

Using $a_y\leq2/11$, each complete error, and therefore their finite
maximum $M$, is strictly below $(128+\sqrt{32449})/1408$.
The next comparison follows from $32449<184^2=33856$, giving
$(128+\sqrt{32449})/1408<312/1408=39/176$.
Finally $39/176<2/9$ is the integer comparison $351<352$.
Feasibility gives $E_*\leq M$, and Theorem 9.3 gives the strict lower
inequality. These are symbolic ordinary inequalities. $\square$

## 11. The exact remaining minimax problem and attribution

**Proposition 11.1 (simultaneous feasibility at a proposed error).** For
$e\geq0$, there is a common channel in (CG.20) with error at most $e$
if and only if there is one pair $(J,B)$ of Lemma 8.3 satisfying, for
every one of the twelve histories $h=(x,\beta,m)$,

$$
\frac12\left(
 \left\|\operatorname{Tr}_{\rm in}[(\rho_h^T\otimes I)J]
                    -s_{256x}\rho_{x+d,\beta,m}\right\|_1
 +\|\mu_h-\nu_h\|_{\rm TV}\right)\leq e,
\quad
\mu_h(A)=\operatorname{tr}(\rho_h^T B(A)).
\tag{CG.86}
$$

Here $\nu_h$ has the five separately labelled densities
$w_i f_{256x}(t)$ and zero other mass; $J\geq0$, $B$ is positive and
countably additive, and (CG.52) holds.

Proof. Reduce a feasible channel by Proposition 8.2 and apply Lemma 8.3.
Its full output metric is precisely (CG.58), giving necessity.
Conversely Lemma 8.3 constructs one normalized CP map from the pair,
and (CG.86) bounds every prescribed history error, giving sufficiency.
Separate nearby outputs, separate attaining maps or pairwise distance
tests do not supply the shared positive pair. $\square$

**Open problem 11.2 (exact minimum and identified minimizing channel).**
A minimizing common CPTP channel exists in the enlarged class. The exact
value $E_*$ and an explicitly identified minimizing channel remain
undetermined. The required result is one pair $(J,B)$ satisfying
(CG.52) and all twelve inequalities (CG.86) at an identified value,
together with a matching lower proof for every allowed common pair.
The displayed $\Phi_0$ attains its own feasible error $M$; it is not
proved to minimize error. The old constant $L_{\rm full}$ is strictly
below the minimum, with no explicit positive increment established here.
Thus existential attainment is settled, while the exact-minimax and
identified-optimizer obligation of Open problem 7.3 remains.

**Attribution 11.3 (credited premises and checked scope).** The original
experiment, histories, common-input contract, full calibrated stopped
law, endpoint distances and $L_{\rm full}$ are credited to §§2–7 and
[AC] at the locations in Attribution 7.2. The middle-height survival
defect used in (CG.79) is [AC, (AC.21)][AC]; its exact-time derivative
and its application to the upper channel are displayed in full above.
The supplied ordinary attainment/strict-gap/upper proposal and ordinary
check are credited mathematical inputs to this exposition, not proof
authorities. The joint-channel, rigidity and upper-error deductions here
are ordinary, `repo-derived` results. They claim no new Lean verification.

Choi's CP correspondence, Kraus/Stinespring dilation, Schmidt
decomposition, finite group averaging, positive-effect comparison,
trace-norm convexity and contractivity, Riesz–Markov representation and
regular-measure variation duality are mature tools. Their needed
applications, normalization and compatibility conditions are given in
§§8–10. No external literature search or worldwide originality conclusion
is asserted. Nonduplication is limited to the compared supplied theory
bodies: these added results are not stated in their original CG §§1–7
or in the supplied [current AC volume][ACR] §§1–20. The proposal and its
check already contain the candidate package and are credited accordingly.

In particular, [current AC][ACR] §§14–20 presuppose the extra source-bound
calibrated actuator of its Definition 14.4. They optimize common relative
returns at two mirrored heights and the record-only calibration score
(AC.56), with finite-mixture nonattainment in Theorems 16.2–17.1.
That class and score are distinct from the common-CPTP complete-output
problem (CG.20). Their nonattainment does not contradict Theorem 8.4,
and their approaching constructions neither implement $\Phi_0$ nor
identify a CG.20 minimizer. No theorem is transferred between those
optimization problems merely through their shared original source.

**Boundary 11.4 (what the ordinary results establish).** The additions
preserve all twelve actual histories, the single normalized old specimen,
fixed common metadata/blanks, one history-independent processor, coherent
live outputs, original five-mode exact-time stopped laws and every
zero-target abort/rejection/other mass. There is no new postselection,
copy, replacement, source callback, installed source parameter, original
actuator or hidden joint assistance. First failure remains absorbing.
The proofs concern the expressly enlarged comparison class, not finite
physical realizability, exact-event bit complexity or efficiency.

The source synthesis and calibrated original instrument remain credited
premises at their stated visible scope; their nested suppliers and the
literature statements in AC are not separately certified here. Ordinary
proofs do not constitute Lean/kernel truth or a machine admission result.
No unconditional-prefix optimum, acquired observer, full original-control
closure, general neural-network or empirical learning result follows.
There is no assertion of worldwide priority, broader research completion,
or a solution of the independent fixed-Hamiltonian minimax problem.

[ACR]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_ACQUIRED_CONTINUATION_LIMITS.md

## 追加锚（本行以下为增补区）

## 12. A fixed-filter common instrument with error below 149/1000

**Definition 12.1 (fixed filter and exact-time output).** Retain the
experiment, common-input premise and complete metric of Definitions
2.3, 3.1, 3.2 and 4.2, including all twelve actual histories. The
existence of a minimizing
common channel is already supplied by Theorem 8.4, and its error is
strictly above $L_{\rm full}$ by Theorem 9.3. The scalar-live channel
$\Phi_0$ remains the distinct processor of Proposition 10.1. In the
ordered basis $(+,-,2)$ of $V$, put

$$
\begin{aligned}
K_{\mathrm{ff}}&=\operatorname{diag}\left(1,\frac1{\sqrt2},
                                  \sqrt{\frac{21}{32}}\right),\\
D_{\mathrm{ff}}&=I_V-K_{\mathrm{ff}}^\dagger K_{\mathrm{ff}}
       =\operatorname{diag}\left(0,\frac12,\frac{11}{32}\right),\\
h_{\mathrm{ff}}(t)&=\frac2{(1+t)^2},\qquad
w=(0,\tfrac14,\tfrac12,\tfrac14,0).
\end{aligned}
\tag{CG.87}
$$

For every complex matrix $A\in M_3(\mathbb C)$ define one linear map
$\Phi_{\mathrm{ff}}$ by its live block and five original-mode failure measures:

$$
\begin{aligned}
\Phi_{\mathrm{ff},\mathrm{live}}(A)&=K_{\mathrm{ff}} A K_{\mathrm{ff}}^\dagger,\\
\Phi_{\mathrm{ff},i}(A)(dt)&=w_i\operatorname{tr}(D_{\mathrm{ff}}A)h_{\mathrm{ff}}(t)\,dt\,P_f
                         \qquad(0\leq i\leq4).
\end{aligned}
\tag{CG.88}
$$

The output time is the exact $t\in[0,1]$, equivalently $6+t$.
Modes $1$ and $3$ remain distinct, and mode index $4$ retains its original
name $13$. The map assigns zero measure to all additional abort,
rejection and other zero-ideal sectors. It has no singular time part.
These are specifications of the entire output, not postselection rules.
All coefficients are fixed before the specimen arrives; no coefficient
uses its unknown history or its old-cut survival mass.

**Theorem 12.2 (constructive full-output upper bound).** The map
$\Phi_{\mathrm{ff}}$ is CPTP on the whole complex matrix algebra, and for the
unchanged minimax quantity (CG.20),

$$
\boxed{
L_{\rm full}<E_*\leq E(\Phi_{\mathrm{ff}})
       <\frac{104759}{704000}<\frac{149}{1000}.
}
\tag{CG.89}
$$

The strict lower comparison reuses Theorem 9.3 and the credited lower
bound of Theorem 6.1; no new lower-bound proof is asserted. The upper
bound retains the joint live quantum
block, every original failure-mode label and the full exact-time law.

Proof. First establish legality independently of performance on the
catalogue. The density $h_{\mathrm{ff}}$ is nonnegative, bounded and measurable, and

$$
\int_0^1h_{\mathrm{ff}}(t)\,dt
 =\left[-\frac2{1+t}\right]_0^1=1.
\tag{CG.90}
$$

For each original label $i$, introduce Kraus densities

$$
J^{\mathrm{ff}}_{i,-}(t)=\sqrt{\frac{w_i h_{\mathrm{ff}}(t)}2}\,|f\rangle\langle-|,
\qquad
J^{\mathrm{ff}}_{i,2}(t)=\sqrt{\frac{11w_i h_{\mathrm{ff}}(t)}{32}}\,
                                      |f\rangle\langle2|.
\tag{CG.91}
$$

Their Kraus sum is precisely the density in (CG.88), for every complex
$A$, including non-Hermitian matrices. For every ancillary dimension
$n$ and every positive $X\in M_n\otimes M_3$, the live image is
$(I_n\otimes K_{\mathrm{ff}})X(I_n\otimes K_{\mathrm{ff}})^\dagger\geq0$. Each failure
density is a sum of the corresponding positive conjugations by
$I_n\otimes J^{\mathrm{ff}}_{i,j}(t)$. Its integral over any Borel time set is
positive. The bounded integrable densities define finite measures, so
this proves positivity at every amplification on the full joint output
space. Moreover,

$$
K_{\mathrm{ff}}^\dagger K_{\mathrm{ff}}+
 \sum_{i=0}^4\int_0^1
 \bigl(J^{\mathrm{ff}}_{i,-}(t)^\dagger J^{\mathrm{ff}}_{i,-}(t)
       +J^{\mathrm{ff}}_{i,2}(t)^\dagger J^{\mathrm{ff}}_{i,2}(t)\bigr)\,dt
 =K_{\mathrm{ff}}^\dagger K_{\mathrm{ff}}+D_{\mathrm{ff}}=I_V.
\tag{CG.92}
$$

Thus the map is completely positive and trace preserving, without a
restriction to real matrices, diagonal states or the twelve inputs.

It also has an explicit extension to the entire original five-mode
complex algebra: in the original basis $(e_0,e_1,e_2,e_3,e_4)$ take

$$
\widehat K_{\mathrm{ff}}=\operatorname{diag}
 \left(1,\frac1{\sqrt2},\sqrt{\frac{21}{32}},
                           \frac1{\sqrt2},1\right),\qquad
\widehat D_{\mathrm{ff}}=\operatorname{diag}
 \left(0,\frac12,\frac{11}{32},\frac12,0\right).
\tag{CG.93}
$$

Use (CG.88) with these operators. Kraus densities
$\sqrt{w_i h_{\mathrm{ff}}(t)(\widehat D_{\mathrm{ff}})_{jj}}\,|f\rangle\langle e_j|$
prove complete positivity by the same all-amplification argument;
$\widehat K_{\mathrm{ff}}^\dagger\widehat K_{\mathrm{ff}}+\widehat D_{\mathrm{ff}}=I_5$ proves trace
preservation. On inputs supported in $V$ this extension agrees with
$\Phi_{\mathrm{ff}}$ and has no live component outside $V$.

Next evaluate the complete error. For $0<z<64$ and $y\in\{5,16,27\}$ write

$$
a_z^{\mathrm{ff}}=\begin{pmatrix}
\sqrt{z/128}\\ \sqrt{(64-z)/128}\\1/\sqrt2
\end{pmatrix},\qquad
s_y=\frac y{y+6},\qquad
\xi_y^{\mathrm{ff}}=\sqrt{s_y}\,a_{y+6}^{\mathrm{ff}},\qquad B_y^{\mathrm{ff}}=\xi_y^{\mathrm{ff}}(\xi_y^{\mathrm{ff}})^\dagger
\quad(y\in\{5,16,27\}).
\tag{CG.94}
$$

Here $a_y^{\mathrm{ff}}$ is a unit vector, and $B_y^{\mathrm{ff}}$ is the unnormalized target live
block. For $\epsilon=e^{-i\beta}\in\{1,-1\}$ and
$\eta=e^{-i\beta}(-1)^m$, let
$U_{\epsilon,\eta}=\operatorname{diag}(\epsilon,\eta,1)$.
Equation (CG.7) gives the actual input vector $U_{\epsilon,\eta}a_y^{\mathrm{ff}}$,
and (CG.15) gives target live block
$U_{\epsilon,\eta}B_y^{\mathrm{ff}}U_{\epsilon,\eta}^\dagger$ and failure
densities $w_i f_y(t)P_f$, where $f_y(t)=6y/(y+6t)^2$.
The four allowed $(\beta,m)$ give all four sign pairs. Since $K_{\mathrm{ff}}$ and
$D_{\mathrm{ff}}$ commute with each $U_{\epsilon,\eta}$, unitary invariance of
the live trace norm and the identical failure laws show that all four
errors at a fixed $y$ are equal. This uses only the covariance of this
explicit map; it imposes no restriction on other maps in (CG.20).

Define its live and failure masses and its positive live overlap by

$$
\begin{aligned}
S_y^{\mathrm{ff}}&=\|K_{\mathrm{ff}}a_y^{\mathrm{ff}}\|^2=\frac{y+148}{256},\qquad
r_y^{\mathrm{ff}}=1-S_y^{\mathrm{ff}}=\frac{108-y}{256},\\
C_y^{\mathrm{ff}}&=\langle K_{\mathrm{ff}}a_y^{\mathrm{ff}},\xi_y^{\mathrm{ff}}\rangle
 =\frac y{128}+\sqrt{M_y^{\mathrm{ff}}}+\sqrt{N_y^{\mathrm{ff}}},\\
M_y^{\mathrm{ff}}&=\frac{y(64-y)(58-y)}{32768(y+6)},\qquad
N_y^{\mathrm{ff}}=\frac{21y}{128(y+6)}.
\end{aligned}
\tag{CG.95}
$$

Lemma 5.1, applied with weights $S_y^{\mathrm{ff}},s_y$, gives the full live norm

$$
L_y^{\mathrm{ff}}:=\|K_{\mathrm{ff}}a_y^{\mathrm{ff}}(a_y^{\mathrm{ff}})^\dagger K_{\mathrm{ff}}^\dagger-B_y^{\mathrm{ff}}\|_1
       =\sqrt{(S_y^{\mathrm{ff}}+s_y)^2-4(C_y^{\mathrm{ff}})^2}.
\tag{CG.96}
$$

In particular this norm counts all three live coherences. For the five
separate failure sectors, positivity of $P_f$ and $\sum_i w_i=1$
give exactly

$$
F_y^{\mathrm{ff}}:=\sum_{i=0}^4\int_0^1
 \|w_i(r_y^{\mathrm{ff}}h_{\mathrm{ff}}(t)-f_y(t))P_f\|_1\,dt
 =\int_0^1|r_y^{\mathrm{ff}}h_{\mathrm{ff}}(t)-f_y(t)|\,dt.
\tag{CG.97}
$$

This is an equality of the labelled-sector norm sum. The two zero-weight
labels and all zero-ideal extra sectors contribute zero because the map
actually outputs zero there. There are no uncounted singular or abort
masses. Thus the original half full cq norm, on all twelve histories, is

$$
E(\Phi_{\mathrm{ff}})=\frac12\max_{y\in\{5,16,27\}}(L_y^{\mathrm{ff}}+F_y^{\mathrm{ff}}).
\tag{CG.98}
$$

The failure integrals admit exact analytic control over the entire time
interval. At the two endpoint heights the density ratios satisfy

$$
\begin{aligned}
\frac{r_5^{\mathrm{ff}}h_{\mathrm{ff}}(t)}{f_5(t)}
 &=\frac{103}{3840}\left(\frac{5+6t}{1+t}\right)^2
 \leq\frac{12463}{15360}<1,\\
\frac{r_{27}^{\mathrm{ff}}h_{\mathrm{ff}}(t)}{f_{27}(t)}
 &=\frac1{256}\left(\frac{27+6t}{1+t}\right)^2
 \geq\frac{1089}{1024}>1.
\end{aligned}
\tag{CG.99}
$$

Indeed $(y+6t)/(1+t)$ has derivative $(6-y)/(1+t)^2$;
the first ratio is maximized at $1$, and the second minimized there.
Using $\int f_y=1-s_y$ consequently gives the exact values

$$
F_5^{\mathrm{ff}}=(1-s_5)-r_5^{\mathrm{ff}}=\frac{403}{2816},\qquad
F_{27}^{\mathrm{ff}}=r_{27}^{\mathrm{ff}}-(1-s_{27})=\frac{379}{2816}.
\tag{CG.100}
$$

For the middle height the ratio

$$
\frac{r_{16}^{\mathrm{ff}}h_{\mathrm{ff}}(t)}{f_{16}(t)}
 =\frac{23}{3072}\left(\frac{16+6t}{1+t}\right)^2
\tag{CG.101}
$$

is strictly decreasing from $23/12>1$ to $2783/3072<1$.
It crosses one exactly once, at

$$
t_{\mathrm{ff}}=\frac{8\sqrt{23}-16\sqrt3}{16\sqrt3-3\sqrt{23}}
 \in(0,1).
\tag{CG.102}
$$

The cumulative signed difference is

$$
R_{\mathrm{ff}}(t)=\int_0^t(r_{16}^{\mathrm{ff}}h_{\mathrm{ff}}(u)-f_{16}(u))\,du
 =\frac{t(88-27t)}{32(1+t)(8+3t)},\qquad R_{\mathrm{ff}}(1)=\frac{61}{704}.
\tag{CG.103}
$$

Splitting the absolute-value integral at the sole crossing gives
$F_{16}^{\mathrm{ff}}=2R_{\mathrm{ff}}(t_{\mathrm{ff}})-R_{\mathrm{ff}}(1)$. The uniform rational certificate

$$
\frac3{32}-R_{\mathrm{ff}}(t)
 =\frac{24-55t+36t^2}{32(1+t)(8+3t)}>0
                  \qquad(0\leq t\leq1)
\tag{CG.104}
$$

holds because its denominator is positive and its numerator is
$36(t-55/72)^2+431/144>0$. Hence

$$
F_{16}^{\mathrm{ff}}=2R_{\mathrm{ff}}(t_{\mathrm{ff}})-\frac{61}{704}<\frac{71}{704}.
\tag{CG.105}
$$

Equations (CG.96), (CG.100) and (CG.105) also specify the exact error of
this particular map: substitute $2R_{\mathrm{ff}}(t_{\mathrm{ff}})-61/704$ for $F_{16}^{\mathrm{ff}}$ in
(CG.98). No time sampling or discretization enters the equality.

It remains to certify the live bounds strictly by rational arithmetic.
The following positive rational numbers are lower bounds for the two
radicals in (CG.95):

| $y$ | $M_y^{\mathrm{ff}}$ | $N_y^{\mathrm{ff}}$ | $\ell_y^{\mathrm{ff}}<\sqrt{M_y^{\mathrm{ff}}}$ | $n_y^{\mathrm{ff}}<\sqrt{N_y^{\mathrm{ff}}}$ |
| --- | --- | --- | --- | --- |
| $5$ | $15635/360448$ | $105/1408$ | $20827/100000$ | $27308/100000$ |
| $16$ | $63/1408$ | $21/176$ | $21152/100000$ | $34542/100000$ |
| $27$ | $10323/360448$ | $189/1408$ | $16923/100000$ | $36637/100000$ |

For an explicit certificate for all six comparisons, the positive square
remainders are

| $y$ | $M_y^{\mathrm{ff}}-(\ell_y^{\mathrm{ff}})^2$ | $N_y^{\mathrm{ff}}-(n_y^{\mathrm{ff}})^2$ |
| --- | --- | --- |
| $5$ | $643867/3520000000000$ | $16187/13750000000$ |
| $16$ | $49607/13750000000$ | $88149/27500000000$ |
| $27$ | $1995867/3520000000000$ | $657541/110000000000$ |

Set

$$
(c_5^{\mathrm{ff}},c_{16}^{\mathrm{ff}},c_{27}^{\mathrm{ff}})=
 \left(\frac{5204}{10000},\frac{6819}{10000},
                                      \frac{74653}{100000}\right),
\qquad
(u_5^{\mathrm{ff}},u_{16}^{\mathrm{ff}},u_{27}^{\mathrm{ff}})=
 \left(\frac{309}{2000},\frac18,\frac{81}{500}\right).
\tag{CG.106}
$$

Here $y/128+\ell_y^{\mathrm{ff}}+n_y^{\mathrm{ff}}-c_y^{\mathrm{ff}}$ equals, respectively,
$1/80000$, $1/25000$ and $3/400000$. Thus $C_y^{\mathrm{ff}}>c_y^{\mathrm{ff}}>0$.
The remaining exact positive remainders are

$$
\begin{aligned}
(u_5^{\mathrm{ff}})^2-(S_5^{\mathrm{ff}}+s_5)^2+4(c_5^{\mathrm{ff}})^2
 &=\frac{20019639}{3097600000000}>0,\\
(u_{16}^{\mathrm{ff}})^2-(S_{16}^{\mathrm{ff}}+s_{16})^2+4(c_{16}^{\mathrm{ff}})^2
 &=\frac{857889559}{193600000000}>0,\\
(u_{27}^{\mathrm{ff}})^2-(S_{27}^{\mathrm{ff}}+s_{27})^2+4(c_{27}^{\mathrm{ff}})^2
 &=\frac{11020208559}{77440000000000}>0.
\end{aligned}
\tag{CG.107}
$$

Since (CG.96) is the square root of a nonnegative norm square,
$C_y^{\mathrm{ff}}>c_y^{\mathrm{ff}}$ and (CG.107) imply $L_y^{\mathrm{ff}}<u_y^{\mathrm{ff}}$. Combining these strict
live bounds with (CG.100) and (CG.105), the three orbit errors are,
respectively, strictly below

$$
\frac12\left(\frac{309}{2000}+\frac{403}{2816}\right)
 =\frac{104759}{704000},\qquad
\frac12\left(\frac18+\frac{71}{704}\right)
 =\frac{159}{1408},\qquad
\frac12\left(\frac{81}{500}+\frac{379}{2816}\right)
 =\frac{104399}{704000}.
\tag{CG.108}
$$

The first of these three rational bounds is the largest, and

$$
\frac{149}{1000}-\frac{104759}{704000}
 =\frac{137}{704000}>0.
\tag{CG.109}
$$

This proves the upper inequalities in (CG.89); $E_*\leq E(\Phi_{\mathrm{ff}})$
is immediate from Definition 4.2. The strict lower inequality reuses
Theorem 9.3 without altering its witness or proof.

The improvement over $\Phi_0$ is strict for the achieved errors, not
only for their displayed upper certificates. At height $y=5$, the
live trace of $\Phi_0$ is $7/11$ and its ideal live trace is $5/11$.
The trace norm of that Hermitian live difference is at least the absolute
trace difference $2/11$. Its full failure norm is exactly $2/11$ by
(CG.78). Consequently Theorem 10.2's exact achieved error obeys

$$
E(\Phi_{\mathrm{ff}})<\frac{104759}{704000}
 <\frac2{11}\leq E(\Phi_0)=M.
\tag{CG.110}
$$

The middle strict comparison follows from
$2/11-104759/704000=23241/704000>0$. The scalar-live construction and
its error formula remain valid. $\square$

**Convention 12.3 (credit and the remaining observation/control bridge).**
The fixed-filter construction and its rational certificate are credited
supplied ordinary mathematical results; their complete proof is retained
above. Their mathematical provenance is repo-derived, using mature
channel and trace-norm tools; no literature priority is claimed. The
all-amplification meaning of complete positivity and the finite-matrix
extension framework are literature-attested in Heinosaari, Jivulescu,
Reeb and Wolf, *Extending quantum operations*,
[arXiv:1205.0641v3](https://arxiv.org/abs/1205.0641v3), §2.1 and §6.1,
[J. Math. Phys. 53, 102208](https://doi.org/10.1063/1.4755845).
Those finite-output results do not supply this continuous-time upper
bound; (CG.90)–(CG.92) prove legality of the actual measure-valued output
directly. The weighted pure-block norm is reused from Lemma 5.1, and the
original history/target laws and $L_{\rm full}$ retain their credit
in §§1–7. Theorem 8.4 supplies existential attainment, Theorem 9.3 supplies
the strict lower comparison, and Proposition 10.1 and Theorem 10.2 supply
the distinct scalar-live feasible channel and its exact error. These
are ordinary uncompiled mathematical proofs, with no Lean-verified claim.

The processor receives one normalized reached-old-live-cut specimen.
Fixed common metadata may be carried along unchanged in every sector;
tensoring identical fixed metadata preserves the norm calculation. No
history label, callback, helper specimen, old-cut mass as a weight, or
free retry enters (CG.88). The emitted live block and failure records
are the joint canonical output of the same instrument. Modes and times
remain separate, every branch is unnormalized, and first failure is
absorbing. Sign covariance is used only to evaluate this particular
map's twelve errors. It neither reduces the class of all allowed maps
to fixed filters nor asserts that every sign-covariant map is Schur.
No physical complex-conjugation operation is used.

The map is a feasible abstract common CPTP simulator in Definition 3.1's
comparison class. Implementing it with the original calibrated control
menu still requires an actuator/interface bridge; the source-indexed
operators $K_x$ in (CG.14) do not provide that common implementation.
Open problems 7.3 and 11.2 still require the exact $E_*$, an identified
optimal common channel and a matching lower certificate over the whole
class. Existence of some minimizing channel is already settled by
Theorem 8.4. The fixed-filter bound sharpens the feasible side of that
problem; it gives neither optimality of $\Phi_{\mathrm{ff}}$ nor a
further class-wide reduction or dual certificate. It does not close the
continuing AURIC FIB ATOM research goal.

## 追加锚（本行以下为增补区）

## 13. An isolated algebraic specification for the complete-output optimum

**Definition 13.1 (the fixed states and algebraic variables).** Retain
Definition 4.2 without changing its input resources, comparison class or
output norm. Index the basis $(+,-,2)$ by $0,1,2$ only inside the matrices
in §§13–16; these indices are not the five original failure labels.
For $0<y<58$ put

$$
\begin{aligned}
p_y&=\left(\frac y{128},\frac{64-y}{128},\frac12\right),\\
d_y&=\left(\frac y{128},
 \frac{y(58-y)}{128(y+6)},\frac{y}{2(y+6)}\right),\\
a_y&=(\sqrt{p_{y0}},\sqrt{p_{y1}},\sqrt{p_{y2}})^T,
\qquad \xi_y=(\sqrt{d_{y0}},\sqrt{d_{y1}},\sqrt{d_{y2}})^T,\\
\rho_y&=a_ya_y^T,\qquad B_y=\xi_y\xi_y^T.
\end{aligned}
\tag{CG.111}
$$

The vectors $p_y,a_y$ are also defined by the same formulas for
$58\leq y<64$. All radicals are the positive real roots. The input is normalized,
$\operatorname{tr}B_y=s_y=y/(y+6)$, and
$\xi_y=\sqrt{s_y}\,a_{y+6}$. For
$U_{e,n}=\operatorname{diag}(e,n,1)$, $e,n\in\{\pm1\}$, the actual
inputs and live targets are $U_{e,n}\rho_yU_{e,n}^T$ and
$U_{e,n}B_yU_{e,n}^T$. Indeed (CG.7) has
$e=(-1)^{\beta/\pi}$ and $n=e(-1)^m$, which run through all four
pairs. The five separate failure densities remain $w_\ell f_y(t)P_f$
with the $w,f_y$ of (CG.50), not functions of $e,n$.

Let $x=(\lambda,\alpha_1,\alpha_2,\beta_1,\beta_2,z)$ and define

$$
\begin{aligned}
v_5&=(\alpha_1,\alpha_2,-1)^T,
&v_{27}&=(\beta_1,\beta_2,1)^T,\\
R_y&=\frac{v_yv_y^T}{v_y^Tv_y},
&A_5&=\lambda R_5,\qquad A_{27}=(1-\lambda)R_{27},\\
\zeta&=\left(z,\frac{59\lambda}{128},\frac\lambda2\right),
&Z_d&=\operatorname{diag}\zeta,\\
N&=A_5\odot\rho_5+A_{27}\odot\rho_{27},
&S_0&=Z_d-N.
\end{aligned}
\tag{CG.112}
$$

Here $\odot$ is entrywise multiplication. For $i<j$ set

$$
S_{ij}=\begin{pmatrix}
\displaystyle\zeta_j-\sum_{y\in\{5,27\}}(A_y)_{ii}p_{yj}
&-N_{ij}\\
-N_{ij}&\displaystyle\zeta_i-\sum_{y\in\{5,27\}}(A_y)_{jj}p_{yi}
\end{pmatrix}.
\tag{CG.113}
$$

The two distinct uses of the letter $\beta$ are separated: $\beta_1,
\beta_2$ here are algebraic coordinates, not the original history phase
$\beta\in\{0,\pi\}$. Define

$$
\begin{aligned}
F(x)&=\operatorname{tr}(A_5B_5)+\operatorname{tr}(A_{27}B_{27})
       -\sum_i\zeta_i+\frac6{11}\lambda,\\
g(x)&=(1000\det S_0,\det S_{01},\det S_{02}),\\
\mathcal L(x,\eta)&=F(x)+\sum_{k=0}^2\eta_k g_k(x),\\
\Psi(x,\eta)&=(\nabla_x\mathcal L,g_0,g_1,g_2).
\end{aligned}
\tag{CG.114}
$$

These nine equations have real algebraic coefficients and rational
dependence on their nine variables. Their chart denominators are
$1+\alpha_1^2+\alpha_2^2$ and $1+\beta_1^2+\beta_2^2$, both positive.

**Proposition 13.2 (root isolation and strict arithmetic margins).** Let
$c$ have the following exact rational decimal coordinates, in order
$(x,\eta)$, and let $C=\prod_{i=0}^8[c_i-10^{-24},c_i+10^{-24}]$.

| Coordinate | Exact rational center |
| --- | --- |
| $\lambda$ | $0.479508042205945691075728241615$ |
| $\alpha_1$ | $1.412018697539825943102823246594$ |
| $\alpha_2$ | $1.185897402486986028204155873343$ |
| $\beta_1$ | $0.413330945620125544606320492846$ |
| $\beta_2$ | $0.809647491041060318009094562763$ |
| $z$ | $0.066998926272600209516864472757$ |
| $\eta_0$ | $0.279795267654829218213193898783$ |
| $\eta_1$ | $0.199570407911600478528148253443$ |
| $\eta_2$ | $0.091392615490799158339482855657$ |

There is exactly one zero $u_*=(x_*,\eta_*)$ of $\Psi$ in $C$.
The strict bounds below hold throughout $C$, before imposing $\Psi=0$:

$$
\begin{gathered}
\frac{47}{100}<\lambda<\frac{49}{100},\qquad \eta_k>0,\\
\zeta_0-\lambda p_{50}>\frac6{125},\qquad
(S_0)_{00}>\frac6{125},\qquad
\det S_0[\{0,1\}]>\frac{23}{10000},\\
(S_{01})_{00}>\frac1{10},\qquad (S_{02})_{00}>\frac1{10},\\
(S_{12})_{00}>\frac{69}{1000},\qquad
\det S_{12}>\frac{11}{2000}.
\end{gathered}
\tag{CG.115}
$$

For any point of $C$, form the following matrices and quantities:

$$
\begin{aligned}
H&=1000\eta_0\operatorname{adj}S_0,\qquad
Q^{01}=\eta_1\operatorname{adj}S_{01},\qquad
Q^{02}=\eta_2\operatorname{adj}S_{02},\qquad Q^{12}=0,\\
r_0&=H_{00}+Q^{01}_{11}+Q^{02}_{11},\qquad
r_1=H_{11}+Q^{01}_{00},\qquad r_2=H_{22}+Q^{02}_{00},\\
m&=(0,1-r_1,1-r_2),\qquad q_y=p_y\cdot m,\\
(C_y)_{ii}&=H_{ii}p_{yi}
 +\sum_{j>i}Q^{ij}_{00}p_{yj}
 +\sum_{j<i}Q^{ji}_{11}p_{yj},\\
(C_y)_{ij}&=H_{ij}(\rho_y)_{ij}
                  +Q^{ij}_{01}(\rho_y)_{ji}\quad(i<j),
\qquad (C_y)_{ji}=(C_y)_{ij},\\
\Delta_y&=B_y-C_y,\qquad
\delta_y=\operatorname{tr}(R_y\Delta_y)\quad(y=5,27),\qquad
T_{16}=\frac1{10}I_3-\Delta_{16}.
\end{aligned}
\tag{CG.116}
$$

The following additional inequalities hold throughout $C$:

$$
\begin{gathered}
H_{00}>0,\qquad Q^{01}_{00}>0,\qquad Q^{02}_{00}>0,\\
\frac{49}{100}<m_1<\frac12,\qquad
\frac{34}{100}<m_2<\frac{35}{100},\\
\delta_5>\frac3{1000},\qquad \delta_{27}>\frac{37}{250},\qquad
q_5<\frac{60}{121},\quad q_{27}>\frac{36}{121},\quad q_{16}>\frac7{20},\\
(T_{16})_{00}>\frac{97}{1000},\qquad
\det T_{16}[\{0,1\}]>\frac{45}{10000},\qquad
\det T_{16}>\frac{48}{10^6},\\
0.14817810291080132013<F(x)<0.14817810291080132014,\\
0.14817810291080132013<\delta_{27}<0.14817810291080132014.
\end{gathered}
\tag{CG.117}
$$

Proof. The finite arithmetic part is specified using directed dyadic
enclosures, so the strict comparisons and the exact root have different
roles. Put $D=2^{224}$. Represent an interval by its integer endpoints
$[a/D,b/D]$. Embed a rational $q$ by
$[\lfloor Dq\rfloor/D,\lceil Dq\rceil/D]$. Addition and negation
are exact endpoint operations. For multiplication take the minimum and
maximum of the four endpoint products, rounded down and up to multiples
of $1/D$. For division take the four quotients, with the same directed
rounding, only when the denominator interval excludes zero. For a
nonnegative interval its square-root enclosure has integer endpoints

$$
\left[\left\lfloor\sqrt{aD}\right\rfloor,
       \left\lceil\sqrt{bD}\right\rceil\right].
\tag{CG.118}
$$

The integer endpoints in (CG.118) are again divided by $D$. Integer
square comparison establishes their direction; no floating-point
operation is required. Construct off-diagonal entries of $\rho_y,B_y$
as square roots of the corresponding products of rational diagonal
entries, and keep their diagonal entries rational.

For differentiation, evaluate (CG.112)–(CG.114) in the truncated
polynomial algebra on six formal increments, keeping degrees at most
two. At a base point $x$, the variable $x_i$ is replaced by
$[x_i]+X_i$. Multiply by polynomial convolution and discard degrees
above two. For inversion, if the constant term is $a$ and the remaining
terms are $v$, use

$$
(a+v)^{-1}=a^{-1}-a^{-2}v+a^{-3}v^2\pmod{\deg>2}.
\tag{CG.119}
$$

The linear coefficients give first derivatives. The coefficient of
$X_iX_j$ gives the $ij$ Hessian entry when $i\ne j$, and twice the
coefficient of $X_i^2$ gives the diagonal entry. Evaluate sums in
increasing index order, determinants by their first-row expansion,
and divisions as multiplication by (CG.119). Thus, writing $\mathscr I$
for this enclosure calculus, the full Jacobian is enclosed by

$$
D\Psi=
\begin{pmatrix}
F_{xx}+\sum_k\eta_k(g_k)_{xx}&
 [\nabla g_0\ \nabla g_1\ \nabla g_2]\\
[\nabla g_0\ \nabla g_1\ \nabla g_2]^T&0_{3\times3}
\end{pmatrix}.
\tag{CG.120}
$$

Let $M$ be the entrywise rational midpoint of
$\mathscr I(D\Psi(c))$. Rational elimination gives an inverse
$\mathcal R=M^{-1}$, with $\mathcal RM=I_9$ verified over $\mathbb Q$.
Enclose each entry of $\mathcal R$ before interval matrix multiplication.
The resulting arithmetic bounds are

| Quantity | Strict rational upper bound |
| --- | --- |
| $\|\mathcal R\Psi(c)\|_\infty$ | $1/10^{28}$ |
| $\sup_{u\in C}\|I_9-\mathcal R D\Psi(u)\|_\infty$ | $1/10^{15}$ |

For the second row, take the maximum of the sums of interval absolute
bounds along each row of $I_9-\mathcal R\mathscr I(D\Psi(C))$.
Endpoint embedding may enlarge $C$ by less than $1/D$ per endpoint;
this only enlarges the derivative enclosure. Applying the same endpoint
operations directly to (CG.112), (CG.113) and (CG.116) gives every
comparison in (CG.115) and (CG.117). The bounds for $F$ and $\delta_{27}$
can also be enclosed more tightly as follows, with rational endpoints:

$$
\begin{aligned}
0.14817810291080132013688243935582
 &<F(x)<0.14817810291080132013689280825907,\\
0.14817810291080132013685287501998
 &<\delta_{27}<0.14817810291080132013692237259040.
\end{aligned}
\tag{CG.121}
$$

Only the weaker strict bounds (CG.117) are needed below. All inputs to
these calculations are the rational center, radius, positive radicals
and displayed expressions; no fitted residual is asserted to equal zero.

For completeness, the enclosure bounds imply existence, not just a
small numerical residual. On the exact rational closed box $C$, define
$T(u)=u-\mathcal R\Psi(u)$. The derivative bound and the mean-value
formula make $T$ Lipschitz with constant $k<10^{-15}$ in the maximum
norm. For $\epsilon=10^{-24}$ and $b<10^{-28}$,

$$
\|T(u)-c\|_\infty\leq b+k\epsilon<\epsilon.
\tag{CG.122}
$$

Thus $T$ maps $C$ strictly into itself and is a contraction. The complete
metric space $C$ has a unique fixed point. Since $\mathcal R$ is
invertible, its fixed points are precisely the zeros of $\Psi$.
The derivative bound also makes $D\Psi(u_*)$ invertible. Clearing the
positive chart denominators gives polynomial equations over the real
algebraic numbers with a nonsingular isolated zero; the coordinates
of that zero are algebraic. Only uniqueness in $C$ is asserted. The
equations may have other zeros outside $C$. $\square$

**Corollary 13.3 (exact ranks at the isolated point).** At $u_*$,

$$
\begin{gathered}
S_0\succeq0,\quad\operatorname{rank}S_0=2,\qquad
S_{01},S_{02}\succeq0,\quad
\operatorname{rank}S_{01}=\operatorname{rank}S_{02}=1,\qquad
S_{12}\succ0,\\
Z_d\succeq\lambda\operatorname{diag}(p_5)\succeq0,
\end{gathered}
\tag{CG.123}
$$

and the $H,Q^{01},Q^{02}$ of (CG.116) are nonzero positive semidefinite
rank-one matrices.

Proof. The last three components of $\Psi=0$ give precisely
$\det S_0=\det S_{01}=\det S_{02}=0$. The leading two-dimensional
block of $S_0$ is positive definite by (CG.115). Its Schur complement is
zero because its determinant is zero and that leading block is
invertible. Thus $S_0$ is positive semidefinite of rank two.
Each active two-dimensional block has positive first pivot and zero
determinant, giving positive semidefiniteness and rank one by the same
Schur-complement argument. The two strict leading minors of $S_{12}$
give positive definiteness. This does not use the false general
criterion that nonnegative leading minors alone imply semidefiniteness.
The last matrix inequality follows from
$\zeta_1=\lambda p_{51}$, $\zeta_2=\lambda p_{52}$ and the strict
coordinate-zero slack in (CG.115). Positive multipliers and the spectral
formula for an adjugate of a positive matrix of corank one give the
stated ranks and positivity of $H,Q^{01},Q^{02}$. $\square$

## 14. A full-class lower witness on the original output space

**Theorem 14.1 (unrestricted lower certificate).** Evaluating (CG.112)
at $u_*$, every allowed common CPTP map in (CG.20) satisfies

$$
E(\Phi)\geq F(x_*).
\tag{CG.124}
$$

This includes complex maps with population transfer and reverse
coherence, arbitrary countably additive time laws and all additional
zero-ideal output sectors.

Proof. Use the output-first, unnormalized Choi convention

$$
J_\Lambda=\sum_{i,j}\Lambda(|i\rangle\langle j|)
                         \otimes|i\rangle\langle j|.
\tag{CG.125}
$$

It is the tensor-factor swap of the input-first convention (CG.54).
For a CP live map $\Lambda$ with input effect $G_L=\Lambda^\dagger(I_3)$,
the correct identities are

$$
\operatorname{Tr}_{\rm out}J_\Lambda=G_L^T,\qquad
\operatorname{tr}((A\otimes\rho^T)J_\Lambda)
 =\operatorname{tr}(A\Lambda(\rho)),\qquad
\operatorname{tr}((I\otimes Z)J_\Lambda)
 =\operatorname{tr}(Z^TG_L).
\tag{CG.126}
$$

In particular the last transpose can be suppressed for the present real
diagonal $Z_d$, but not for an arbitrary matrix $Z$. Define

$$
W=\frac14\sum_{e,n\in\{\pm1\}}
(U_{e,n}\otimes U_{e,n})
(A_5\otimes\rho_5^T+A_{27}\otimes\rho_{27}^T)
(U_{e,n}\otimes U_{e,n})^\dagger.
\tag{CG.127}
$$

The conjugate input representation in a general Choi covariance formula
is $\overline U$; all four present $U_{e,n}$ are real, so it equals $U$.
In output-input order the character spaces are

$$
\begin{aligned}
&\langle|00\rangle,|11\rangle,|22\rangle\rangle,\qquad
\langle|01\rangle,|10\rangle\rangle,\\
&\langle|02\rangle,|20\rangle\rangle,\qquad
\langle|12\rangle,|21\rangle\rangle.
\end{aligned}
\tag{CG.128}
$$

Indeed an entry $|ai\rangle\langle bj|$ survives the group average
exactly when the products of its two coordinate signs agree. On the
first space $W_{ii,jj}=N_{ij}$. On the $ij$ space its diagonal entries
are $\sum_y(A_y)_{ii}p_{yj}$ and
$\sum_y(A_y)_{jj}p_{yi}$, and its off-diagonal entry is $N_{ij}$.
Consequently the full nine-dimensional inequality is

$$
S:=I_3\otimes Z_d-W
 =S_0\oplus S_{01}\oplus S_{02}\oplus S_{12}\succeq0.
\tag{CG.129}
$$

The direct-sum equality uses the order (CG.128). In particular the
three two-dimensional spaces have not been suppressed. A real symmetric
positive semidefinite witness is also positive on complex vectors,
so (CG.129) bounds an arbitrary complex Hermitian positive Choi matrix.

For each of the four $y=5$ histories choose a mathematical output effect
with live part $U_{e,n}R_5U_{e,n}^\dagger$, identity on the entire
canonical five-label failure register at every time, and zero on other
sectors. For the four $y=27$ histories choose live part
$U_{e,n}R_{27}U_{e,n}^\dagger$ and zero on every nonlive sector.
Give these effects weights $\lambda/4$ and $(1-\lambda)/4$,
respectively. The eight weights are positive and sum to one. They are
coefficients of a lower witness, not preparation priors or labels
accessible to the simulator. The $y=16$ errors remain in the original
maximum.

For normalized full outputs and an effect $0\preceq M\preceq I$,

$$
\operatorname{tr}M(\Omega-\omega)
 \leq\frac12\|\Omega-\omega\|_{1,\mathrm{cq}}.
\tag{CG.130}
$$

To see the factor, $\operatorname{tr}(\Omega-\omega)=0$ and
$2M-I$ is a Hermitian contraction, whose pairing is bounded by the
trace norm. This argument also applies to measures using a common
dominating scalar measure. Summing the eight ideal payoffs gives

$$
\operatorname{tr}(A_5B_5)+\operatorname{tr}(A_{27}B_{27})
                         +\frac6{11}\lambda.
\tag{CG.131}
$$

Now let $\Phi$ be any allowed common channel, without assuming covariance.
Compress its live output to $V$ to obtain the CP map $\Lambda$.
Let $G_f$ be the input effect of its entire canonical failure register,
including any stopped quantum support and singular time measures there.
The uncounted-by-the-test, but still present, output effect is

$$
G_o=I-G_L-G_f\succeq0.
\tag{CG.132}
$$

It includes live mass outside $V$, abort, rejection and all remaining
zero-ideal sectors. The eight weighted simulated live payoffs are
$\operatorname{tr}(WJ_\Lambda)$, and the weighted failure payoff is
$\operatorname{tr}(D_fG_f)$ for
$D_f=\lambda\operatorname{diag}(p_5)$: averaging the four actual input
signs gives $\operatorname{diag}(p_5)$. Equations (CG.126) and (CG.132)
give the exact budget identity

$$
\begin{aligned}
\operatorname{tr}Z_d-\operatorname{tr}(WJ_\Lambda)
                    -\operatorname{tr}(D_fG_f)
={}&\operatorname{tr}(S J_\Lambda)
   +\operatorname{tr}((Z_d-D_f)G_f)
   +\operatorname{tr}(Z_dG_o)\geq0.
\end{aligned}
\tag{CG.133}
$$

Every term on the right pairs positive semidefinite matrices. Thus the
simulated payoff is at most $\operatorname{tr}Z_d$. Subtract this from
(CG.131), apply (CG.130), and bound the weighted average error by the
original maximum. This proves (CG.124).

The failure effect is constant on the exact time interval. Atoms and
singular continuous mass therefore enter $G_f$ with their entire mass.
Wrong stopped support in that register is also included in $G_f$.
Other wrong-support and extra mass enters $G_o$. The half full norm in
(CG.130) continues to count it all. No output-fixing reduction, finite
time partition, minimax interchange, strong duality theorem or channel
covariance restriction is needed for this lower proof. $\square$

## 15. The complementary common channel and exact-time equality

**Theorem 15.1 (a legitimate same-point common instrument).** Evaluate
all quantities in (CG.116) at $u_*$. Define

$$
h=\frac{He_0}{\sqrt{H_{00}}},\qquad
b^{0j}=\frac{Q^{0j}e_0}{\sqrt{Q^{0j}_{00}}}\quad(j=1,2),\qquad
K_0=\operatorname{diag}(h),\qquad
K_{0j}=b^{0j}_0|0\rangle\langle j|
                  +b^{0j}_1|j\rangle\langle0|.
\tag{CG.134}
$$

There is one CPTP instrument on all of $M_3(\mathbb C)$ given by

$$
\begin{aligned}
\Lambda_*(A)&=K_0AK_0^\dagger+K_{01}AK_{01}^\dagger
                                 +K_{02}AK_{02}^\dagger,\\
\Phi_{*,\mathrm{live}}(A)&=\Lambda_*(A),\\
\Phi_{*,\ell}(A)(dt)&=w_\ell\operatorname{tr}(\operatorname{diag}(m)A)
                   h_0(t)\,dt\,P_f\quad(\ell=0,1,2,3,4),\\
h_0(t)&=\frac2{(1+t)^2}.
\end{aligned}
\tag{CG.135}
$$

It assigns zero mass to all additional sectors. It has a specified
extension to the whole original five-mode complex input algebra.

Proof. The pivots in (CG.117) are positive. For a positive semidefinite
rank-one matrix $A$ with $A_{00}>0$,
$A=(Ae_0)(Ae_0)^\dagger/A_{00}$. Corollary 13.3 therefore implies
$H=hh^T$ and $Q^{0j}=b^{0j}(b^{0j})^T$. The live Choi matrix of
(CG.134) is exactly

$$
J_*=H\oplus Q^{01}\oplus Q^{02}\oplus0
\tag{CG.136}
$$

in (CG.128). In particular the live map is CP on the whole complex
algebra. Its action for arbitrary complex $A$, without imposing
$A_{ij}=A_{ji}$, has entries

$$
\begin{aligned}
(\Lambda_*A)_{ii}
 &=H_{ii}A_{ii}+\sum_{j>i}Q^{ij}_{00}A_{jj}
                         +\sum_{j<i}Q^{ji}_{11}A_{jj},\\
(\Lambda_*A)_{ij}
 &=H_{ij}A_{ij}+Q^{ij}_{01}A_{ji}\quad(i<j),\\
(\Lambda_*A)_{ji}
 &=H_{ji}A_{ji}+Q^{ij}_{10}A_{ij}\quad(i<j).
\end{aligned}
\tag{CG.137}
$$

Thus $C_y$ in (CG.116) is the actual live output on $\rho_y$. The
reverse-coherence terms are part of a Kraus map, not a physical
transposition gate.

It remains to prove trace preservation as an exact identity. At a root,
the adjugate identity gives

$$
S_0H=S_{01}Q^{01}=S_{02}Q^{02}=0.
\tag{CG.138}
$$

The determinant differential is
$d\det S=\operatorname{tr}(\operatorname{adj}(S)\,dS)$. Consequently,
when $\eta$ is held fixed at its value at the point of differentiation,

$$
d_x\mathcal L
 =\sum_{y\in\{5,27\}}\operatorname{tr}(dA_y\,\Delta_y)
   +\sum_i(r_i-1)d\zeta_i+\frac6{11}d\lambda.
\tag{CG.139}
$$

To verify (CG.139) directly, use (CG.137) to expand

$$
\operatorname{tr}(S_0H)+\sum_{i<j}\operatorname{tr}(S_{ij}Q^{ij})
 =\sum_i\zeta_i r_i
             -\sum_{y\in\{5,27\}}\operatorname{tr}(A_y C_y).
\tag{CG.140}
$$

This is linear in the entries of $\zeta,A_y$, holding $H,Q$ fixed.
Its differential, combined with $dF$, proves (CG.139), including the
factor $1000$ in $H$. In this first differential $H,Q$ are the
adjugate coefficients at that point; differentiating them again would
not be the determinant differential being used.

The $z$ stationarity equation gives $r_0-1=0$, because only
$\zeta_0=z$ depends on $z$ in (CG.139). The Kraus column masses are
$\sum_aK_a^\dagger K_a=\operatorname{diag}(r_0,r_1,r_2)$ by
(CG.134). Thus, exactly at $u_*$,

$$
\sum_{a\in\{0,01,02\}}K_a^\dagger K_a
                      +\operatorname{diag}(m)=I_3.
\tag{CG.141}
$$

The two strict bounds on $m$ in (CG.117) make its diagonal nonnegative.
Each failure density in (CG.135) is CP, with Kraus densities
$\sqrt{w_\ell m_j h_0(t)}\,|f\rangle\langle j|$ for $j=1,2$.
Their integrals are countably additive and remain positive at every
ancillary amplification. Since $\int_0^1h_0(t)dt=1$ by (CG.90) and
$\sum_\ell w_\ell=1$, (CG.141) proves joint trace preservation.

Let $E:\mathbb C^3\to\mathbb C^5$ have the three orthonormal columns
in (CG.6), and put $P_V=EE^\dagger$. A concrete five-dimensional
extension is

$$
\begin{aligned}
\widehat\Phi_{*,\mathrm{live}}(A)
 &=E\Lambda_*(E^\dagger AE)E^\dagger,\\
\widehat\Phi_{*,\ell}(A)(dt)
 &=h_0(t)\left[
 w_\ell\operatorname{tr}(E\operatorname{diag}(m)E^\dagger A)
 +\mathbf1_{\ell=2}\operatorname{tr}((I_5-P_V)A)
 \right]dt\,P_f.
\end{aligned}
\tag{CG.142}
$$

Each summand is a CP compression/Kraus or trace-and-prepare map.
Its total effect is $E I_3E^\dagger+(I_5-P_V)=I_5$ by
(CG.141), so it is CPTP, including on non-Hermitian inputs by linearity.
Every one of the twelve inputs lies in $V$, so the extension changes
none of their outputs. The complementary input subspace is sent to
original failure index $2$, not to a new history label. $\square$

**Theorem 15.2 (matching error for all twelve complete outputs).** The
single channel (CG.135) has

$$
e_5=e_{27}=F(x_*)=\delta_{27},\qquad
e_{16}<\frac{71}{484}<\frac{37}{250}<\delta_{27},
\tag{CG.143}
$$

where $e_y$ denotes each of its four actual-history errors at height $y$.
In particular $E(\Phi_*)=F(x_*)$ in precisely (CG.20).

Proof. First extract the exact eigenvector and equal-error identities
from the same root; stationarity alone is not being asserted to prove
optimality. In the two $v_5$ coordinates of (CG.139) only $A_5$ varies,
with its nonzero scalar weight $\lambda$. Likewise the two $v_{27}$
coordinates vary only $A_{27}$, with weight $1-\lambda>0$.
For a real symmetric $\Delta$, $v=(a,b,\sigma)^T$, $\sigma=\pm1$,
and $\delta=v^T\Delta v/(v^Tv)$, the chart derivatives are

$$
\frac{\partial\delta}{\partial a}
 =\frac{2((\Delta v)_0-\delta v_0)}{v^Tv},\qquad
\frac{\partial\delta}{\partial b}
 =\frac{2((\Delta v)_1-\delta v_1)}{v^Tv}.
\tag{CG.144}
$$

Here $\Delta_y$ is held fixed as the coefficient of $dA_y$ in
(CG.139). Vanishing of these two components, and
$v^T(\Delta v-\delta v)=0$, force the remaining component to vanish
because $v_2=\sigma\ne0$. Hence

$$
\Delta_5v_5=\delta_5v_5,\qquad
\Delta_{27}v_{27}=\delta_{27}v_{27}.
\tag{CG.145}
$$

Each $B_y$ has rank one and each $C_y\succeq0$ by Theorem 15.1, so
$\Delta_y=B_y-C_y$ has at most one positive eigenvalue: a
two-dimensional strictly positive subspace would intersect
$\xi_y^\perp$, where the quadratic form is nonpositive. Both endpoint
$\delta_y$ are positive by (CG.117). Therefore
$\operatorname{tr}(\Delta_y)_+=\delta_y$ for $y=5,27$.

The $\lambda$ equation in (CG.139), with $r_0=1$ and
$q_5=p_{51}(1-r_1)+p_{52}(1-r_2)$, gives

$$
\delta_5+\frac6{11}-q_5=\delta_{27}.
\tag{CG.146}
$$

Complementarity (CG.138), evaluated in (CG.140), gives
$\sum_y\operatorname{tr}(A_yC_y)=\sum_i\zeta_i r_i$.
Substitution into the definition of $F$, using
$\zeta_i=\lambda p_{5i}$ for $i=1,2$, yields

$$
\begin{aligned}
F(x_*)&=\lambda\delta_5+(1-\lambda)\delta_{27}
              +\sum_i\zeta_i(r_i-1)+\frac6{11}\lambda\\
 &=\lambda\left(\delta_5+\frac6{11}-q_5\right)
                         +(1-\lambda)\delta_{27}=\delta_{27}.
\end{aligned}
\tag{CG.147}
$$

Next compute the original half norm, including its exact-time part.
At an unsigned input the live ideal-minus-simulated block is
$\Delta_y$, and the five stopped differences are
$w_\ell(f_y-q_yh_0)P_f\,dt$. Their trace sums satisfy

$$
\operatorname{tr}\Delta_y=q_y-(1-s_y),\qquad
\int_0^1(f_y-q_yh_0)dt=1-s_y-q_y.
\tag{CG.148}
$$

Using $\|X\|_1=2\operatorname{tr}X_+-\operatorname{tr}X$ on a
Hermitian matrix and the corresponding signed-density identity, these
trace terms cancel. Since $w_\ell\geq0$, $\sum w_\ell=1$, and each
stopped state has trace one, the complete half norm is exactly

$$
e_y=\operatorname{tr}(\Delta_y)_+
                  +\int_0^1(f_y(t)-q_yh_0(t))_+dt.
\tag{CG.149}
$$

This equality sums the norms in the five separately named sectors;
it does not replace their output alphabet by one pooled label. This
channel has no mass in extra or singular sectors, so their actual
contributions to its full norm are zero. The lower certificate allowed
arbitrary mass there.

Exact-time signs follow from the elementary rational function

$$
\frac{f_y(t)}{h_0(t)}
 =3y\left(\frac{1+t}{y+6t}\right)^2,\qquad
\left(\frac{f_y}{h_0}\right)'(t)
 =\frac{6y(y-6)(1+t)}{(y+6t)^3}.
\tag{CG.150}
$$

The denominators are positive throughout $[0,1]$. Thus

$$
\min_{[0,1]}\frac{f_5}{h_0}=\frac{60}{121},\qquad
\max_{[0,1]}\frac{f_{27}}{h_0}=\frac{36}{121},\qquad
\max_{[0,1]}\frac{f_{16}}{h_0}=\frac{48}{121}.
\tag{CG.151}
$$

The strict bounds on $q_5,q_{27}$ in (CG.117) give
$f_5-q_5h_0>0$ and $f_{27}-q_{27}h_0<0$ at every exact time.
Consequently (CG.145)–(CG.149) give
$e_5=\delta_5+6/11-q_5=\delta_{27}=e_{27}$.

At the middle height the three positive leading minors of $T_{16}$
in (CG.117) prove $T_{16}\succ0$. Hence every eigenvalue of
$\Delta_{16}$ is strictly less than $1/10$. Its at-most-one-positive
property implies $\operatorname{tr}(\Delta_{16})_+<1/10$.
The positive part must be retained in the time estimate:

$$
\begin{aligned}
\int_0^1(f_{16}-q_{16}h_0)_+dt
 &=\int_0^1h_0(t)
       \left(\frac{f_{16}(t)}{h_0(t)}-q_{16}\right)_+dt\\
 &\leq\left(\frac{48}{121}-q_{16}\right)_+
 \leq\frac{48}{121}-\frac7{20}.
\end{aligned}
\tag{CG.152}
$$

The last right-hand side is positive, and $q_{16}>7/20$.
Together with (CG.149) this gives

$$
e_{16}<\frac1{10}+\frac{48}{121}-\frac7{20}
 =\frac{71}{484}<\frac{37}{250}<\delta_{27}.
\tag{CG.153}
$$

Finally $K_0$ commutes with all four $U_{e,n}$. Each of $K_{01}$ and
$K_{02}$ transforms by a single sign character, and
$\operatorname{diag}(m)$ is invariant. Thus (CG.135) is covariant on
every complex input. Its four errors at each height are identical by
unitary invariance and unchanged failure densities. This proves
(CG.143) for all twelve actual histories, without supplying a
history index to the map. $\square$

## 16. Exact minimax value and the remaining native-control obligation

**Theorem 16.1 (the original full-output minimax).** With the exact
isolated point of Proposition 13.2 and the whole-complex common channel
of Theorem 15.1,

$$
\boxed{
\inf_{\Phi\ \mathrm{common\ CPTP}}
\max_{(x,\beta,m)\in\mathcal H}
 \frac12\|\Phi(\rho_{x,\beta,m})-\Omega_{x,\beta,m}\|_{1,\mathrm{cq}}
 =E(\Phi_*)=F(x_*)=\delta_{27},
\quad
0.14817810291080132013<E_*<0.14817810291080132014.
}
\tag{CG.154}
$$

The symbol $x_*$ on the right is the six-coordinate algebraic variable
of Definition 13.1; the history height $x$ on the left is still the
original scalar $y/256$.

Proof. Theorem 14.1 bounds every allowed channel below by $F(x_*)$.
Theorem 15.2 proves the reverse inequality using one legitimate channel
at the very same exact point. Proposition 13.2 supplies the strict
decimal enclosure. This is a matching witness and attainer argument,
not an inference from KKT stationarity to global optimality. $\square$

**Corollary 16.2 (relation to the earlier results).** The exact-value
and identified-simulator questions in Open problems 7.3 and 11.2 have
the answer (CG.154) in the enlarged comparison class (CG.20). Theorem
8.4's attainment result, Theorem 9.3's strict inequality
$L_{\rm full}<E_*$, the scalar-live construction of §10 and the
fixed-filter construction of §12 remain valid with their stated scope.
No uniqueness of a minimizing channel follows.

Proof. Theorems 14.1 and 15.2 directly fulfill the simultaneous
feasibility and matching-lower requirements of Proposition 11.1.
All quantities and classes in the earlier results are unchanged.
Uniqueness in Proposition 13.2 concerns only a zero in a specified
parameter box; it is not a classification of optimal channels or
other algebraic zeros. $\square$

**Convention 16.3 (mathematical attribution and control boundary).** The
algebraic ansatz (CG.112)–(CG.116), its rational center and the
complementary three-Kraus construction are credited supplied
mathematics. The particular instance-specific contribution is their
root isolation, strict inequalities, full-class witness and exact-time
attaining-channel deduction for (CG.20). The original histories,
calibrated target law and common-input contract retain Attribution 7.2;
the attainment, strict lower gap and fixed-filter upper facts are
reused from §§8–12. These are ordinary computer-assisted and analytic
proofs; no Lean/kernel verification or worldwide priority is asserted.

The finite-matrix Choi/Kraus and joint CP/TP framework is established
in Heinosaari, Jivulescu, Reeb and Wolf, *Extending quantum operations*,
[arXiv:1205.0641v3](https://arxiv.org/html/1205.0641v3), §2.1 and §6.1.
Their Theorem 5 concerns at-most-qubit pairs and is not a qutrit
pairwise substitute for a common channel. The full diagonal-sign
covariance form, including population transfer and transposed
coherence terms, is established in Nechita and Park, *Random covariant
quantum channels*, [arXiv:2403.03667v2, §5](https://arxiv.org/html/2403.03667v2),
[DOI:10.1007/s00023-025-01558-y](https://doi.org/10.1007/s00023-025-01558-y).
The explicit block calculation (CG.128)–(CG.129) is the required
specialization here. Jenčová, *Comparison of quantum channels and
statistical experiments*,
[arXiv:1512.07016v2](https://arxiv.org/html/1512.07016v2), Theorem 4,
uses one common channel and the $2\epsilon$ trace-norm convention.
These finite-dimensional literature results do not by themselves
settle exact-time outputs; (CG.130)–(CG.133) and (CG.148)–(CG.153)
provide the needed measure-level comparison directly.

The attaining instrument acts on one normalized reached-old-live-cut
specimen. The fixed metadata can be tensored onto every output in their
same state. No height, parity, waveform, callback, helper specimen or
survival-mass prior is furnished to it. All live coherences and five
original labels are retained, with index $4$ still denoting mode $13$;
the output time is exactly $t\in[0,1]$, equivalently $6+t$.
The instrument specifies a joint output law and has no post-failure
operation or acceptance renormalization. Mathematical sign averaging
and real matrices install no physical conjugation gate.

Realizing this particular common CPTP instrument using only the
original native calibrated-actuator menu remains a separate interface
obligation. Neither the source-indexed $K_x$ of (CG.14), an ideal
continuous phase-record law nor a linear-observation coercivity lemma
supplies that correspondence. The result provides the exact benchmark
for such an interface, without constructing the interface or granting
extra observations or controls. It asserts neither finite physical
storage of an exact time, efficient synthesis, uniqueness of the
optimizer, an unconditional-prefix optimum nor completion of the
continuing research programme.

## 追加锚（本行以下为增补区）

## 17. Equality identifies the sign-averaged live part of every optimizer

**Convention 17.1 (credited point and a necessary finite output test).**
All quantities with a star in §§17–20 refer to the exact point $u_*$
and channel of §§13–16. In particular, the root, ranks, strict margins,
invertibility of $D\Psi(u_*)$ and value $E_*=F(x_*)$ are the credited
ordinary computer-assisted premises of Proposition 13.2, Corollary 13.3
and Theorem 16.1. The deductions below use those premises without
introducing another numerical certificate. The basis indices $0,1,2$
mean $(+,-,2)$, and the Choi order and normalization are exactly
(CG.125), with no factor $1/3$.

Define a common CPTP output operation $\mathcal C$ that keeps the live
compression to $V$, sends its complementary trace to a scalar other
flag, and sends the trace of the entire canonical failure register to
a scalar failure flag. It discards cross terms between $V$ and its
orthogonal live complement. All additional output sectors also go to
other. Every original failure label, time and stopped quantum support
contributes its entire mass to failure, including singular measures;
none is selected or normalized. This is only a necessary lower test of
the unchanged complete output task (CG.20).

Its output algebra, target and arbitrary common channel have the forms

$$
\begin{aligned}
\mathcal A_c&=M_3(\mathbb C)\oplus\mathbb C\oplus\mathbb C,\\
\Omega^c_{y,U}&=(UB_yU^\dagger,\ a_y^{\mathrm f},\ 0),
& a_y^{\mathrm f}&=1-s_y=\frac6{y+6},\\
\Theta(A)&=(\Lambda(A),\ \operatorname{tr}(G_fA),
                                     \operatorname{tr}(G_oA)),\\
J_\Lambda&\succeq0,\quad G_f,G_o\succeq0,
&\operatorname{Tr}_{\rm out}J_\Lambda+G_f^T+G_o^T&=I_3,\\
E_c(\Theta)&=\max_{y,U}\frac12\left(
 \|UB_yU^\dagger-\Lambda(U\rho_yU^\dagger)\|_1
 +|a_y^{\mathrm f}-\operatorname{tr}(G_fU\rho_yU^\dagger)|
 +\operatorname{tr}(G_oU\rho_yU^\dagger)\right).
\end{aligned}
\tag{CG.155}
$$

Here $y\in\{5,16,27\}$ and $U$ runs over the same four actual signs
as (CG.111). The superscript on $a_y^{\mathrm f}$ distinguishes this
scalar failure mass from the input vector $a_y$ of that equation.
The input effects are $G_f,G_o$; the transposes in the Choi budget
are essential for complex maps. Choi positivity and positive scalar
functionals make this budget necessary and sufficient for one CPTP
$\Theta$. Contractivity gives $E_c(\mathcal C\Phi)\leq E(\Phi)$.
The effects in Theorem 14.1 factor through $\mathcal C$, so its same
budget proof gives $E_c(\Theta)\geq F(x_*)$ for every finite-output
$\Theta$, including ones not supplied as reductions of a particular
full-output channel. The credited $\mathcal C\Phi_*$ supplies equality.
Consequently $\min_\Theta E_c(\Theta)=E_*$. This auxiliary equality
does not replace the original comparison by its finite marginal.

**Theorem 17.2 (rigidity of the averaged live Choi matrix).** For every
CPTP $\Theta$ in (CG.155) with $E_c(\Theta)=E_*$, its mathematical
average under the four actual signs has live Choi matrix

$$
\overline J_\Lambda=H_*\oplus Q_*^{01}\oplus Q_*^{02}\oplus0
\tag{CG.156}
$$

in precisely the output-input block order (CG.128). Before averaging,
$G_o=0$, $G_f|0\rangle=0$ and
$\operatorname{range}J_\Lambda\subseteq\ker S_*$.

Proof. Let $e_h$ be an individual finite-output error, $M_h$ the endpoint
effect used in Theorem 14.1, $\pi_h=\lambda_*/4$ at height $5$ and
$\pi_h=(1-\lambda_*)/4$ at height $27$. Put
$P_h=\operatorname{tr}M_h(\Omega_h^c-\Theta(\rho_h))$.
Equations (CG.130)–(CG.133), now on $\mathcal A_c$, give

$$
\begin{aligned}
E_*&\leq\sum_h\pi_hP_h\leq\sum_h\pi_he_h\leq E_*,\\
0&=\operatorname{tr}(S_*J_\Lambda)
 +\operatorname{tr}((Z_{d,*}-D_{f,*})G_f)
 +\operatorname{tr}(Z_{d,*}G_o),
\qquad D_{f,*}=\lambda_*\operatorname{diag}(p_5).
\end{aligned}
\tag{CG.157}
$$

Every weight is strictly positive, so every endpoint test saturates:
$P_h=e_h=E_*$. Each of the three nonnegative budget terms is zero.
The credited inequalities imply $Z_{d,*}\succ0$ and
$Z_{d,*}-D_{f,*}=\kappa P_0$ with $\kappa>0$. Thus $G_o=0$ and
$(G_f)_{00}=0$. Positivity gives $G_f|0\rangle=0$, since a zero
positive diagonal entry has zero row and column. Likewise, for positive
$S,J$, $\operatorname{tr}(SJ)=\|S^{1/2}J^{1/2}\|_2^2=0$
forces $\operatorname{range}J\subseteq\ker S$.

Average the channel by (CG.60), with the two scalar flags fixed.
This is a mathematical operation on candidates. It permutes the four
actual input/target pairs at each height and contracts their maximum
error, while the lower bound in Convention 17.1 prevents any decrease
below $E_*$. Thus the averaged channel also satisfies (CG.157).
Its Choi matrix is the average of conjugations by $U\otimes U$;
the input representation is $\overline U=U$ here. Its character blocks
are (CG.128). Their ranges lie in the respective slack kernels.
The credited ranks (CG.123) therefore imply that for some real numbers
$\widetilde\eta_k\geq0$,

$$
\begin{aligned}
\overline H&=1000\widetilde\eta_0\operatorname{adj}S_{0,*},\\
\overline Q^{01}&=\widetilde\eta_1\operatorname{adj}S_{01,*},
&\overline Q^{02}&=\widetilde\eta_2\operatorname{adj}S_{02,*},
&\overline Q^{12}&=0.
\end{aligned}
\tag{CG.158}
$$

Indeed a positive Hermitian operator supported on a one-dimensional
real kernel is a nonnegative real multiple of its rank-one real
adjugate. This also proves that all surviving blocks are real; no
complex-conjugation operation has been imposed on the channel.

Define $\widetilde r_i$, $\widetilde C_y$ using (CG.116) with these
blocks, and put
$\widetilde\Delta_y=B_y-\widetilde C_y$ and
$\widetilde\delta_y=\operatorname{tr}(R_{y,*}\widetilde\Delta_y)$.
Covariance makes the averaged failure effect diagonal. The budget,
$G_o=0$ and $G_f|0\rangle=0$ give

$$
\widetilde r_0=1,\qquad
\overline G_f=\operatorname{diag}(0,1-\widetilde r_1,
                                      1-\widetilde r_2),\qquad
\widetilde q_y=p_{y1}(1-\widetilde r_1)
                         +p_{y2}(1-\widetilde r_2).
\tag{CG.159}
$$

Saturation for the unsigned endpoint histories reads

$$
\widetilde\delta_5+\frac6{11}-\widetilde q_5
             =E_*=\widetilde\delta_{27}.
\tag{CG.160}
$$

There is a further consequence of Helstrom equality that is needed to
identify the coefficients. Hold the averaged channel and its output
differences fixed. Vary just the rank-one live projector $R_y$ in its
two real chart coordinates of (CG.112), keeping the failure/other
parts of $M_y$ fixed. Every perturbed $M_y$ remains an effect, and
its pairing with that fixed difference is at most $e_y=E_*$. At the
credited projector equality holds, so its first derivative vanishes:

$$
\operatorname{tr}(dR_5\,\widetilde\Delta_5)=0,\qquad
\operatorname{tr}(dR_{27}\,\widetilde\Delta_{27})=0
\quad\text{in both projector coordinates at each endpoint}.
\tag{CG.161}
$$

This is a local maximum of a differentiable scalar pairing, not an
assumption that an arbitrary optimizer satisfies the ansatz equations.
Equivalently, using (CG.144) with $\widetilde\Delta_y$ fixed,
its first two coordinates give
$(\widetilde\Delta_yv_y)_i=\widetilde\delta_y(v_y)_i$ for $i=0,1$.
The identity
$v_y^T(\widetilde\Delta_yv_y-\widetilde\delta_yv_y)=0$ and
$(v_y)_2=\pm1$ give the third coordinate. Thus these projectors are
also eigenprojectors of the averaged live differences.

Now evaluate the FIRST differential of (CG.114) at $x_*$ with
$\eta=\widetilde\eta$ held fixed. The determinant differential used
in (CG.139) is valid for these coefficients too. It says

$$
\left.d_x\mathcal L(x,\widetilde\eta)\right|_{x_*}
 =\sum_{y=5,27}\operatorname{tr}(dA_y\,\widetilde\Delta_y)
   +\sum_i(\widetilde r_i-1)d\zeta_i+\frac6{11}d\lambda.
\tag{CG.162}
$$

In this identity $\overline H,\overline Q$ are fixed adjugate
coefficients at $x_*$. Differentiating them as functions of $x$ would
produce an incorrect extra term. The $z$ coefficient is zero by
$\widetilde r_0=1$. The four projector coefficients are zero by
(CG.161) and the positive weights $\lambda_*,1-\lambda_*$. Since
$d\zeta_1=p_{51}d\lambda$, $d\zeta_2=p_{52}d\lambda$, the remaining
$\lambda$ coefficient is

$$
\widetilde\delta_5-\widetilde\delta_{27}
 -\widetilde q_5+\frac6{11}=0
\tag{CG.163}
$$

by (CG.160). This essential equal-payoff equation completes all six
components of $\nabla_x\mathcal L(x_*,\widetilde\eta)=0$.

Let $G=[\nabla g_0\ \nabla g_1\ \nabla g_2]_{x_*}$, a real
$6$ by $3$ matrix. The credited Jacobian has the form

$$
D\Psi(u_*)=\begin{pmatrix}A&G\\G^T&0\end{pmatrix}.
\quad
Gc=0\ \Longrightarrow\
D\Psi(u_*)\binom{0}{c}=0\ \Longrightarrow\ c=0.
\tag{CG.164}
$$

Here $A$ is its $6$ by $6$ Hessian block, not an input operator.
Invertibility of $D\Psi(u_*)$ therefore makes $G$ injective. Subtracting the
credited equation $\nabla F(x_*)+G\eta_*=0$ from (CG.162)'s
stationarity gives $G(\widetilde\eta-\eta_*)=0$.
Hence $\widetilde\eta=\eta_*$, proving (CG.156). The argument uses
nonsingularity at the credited point, not uniqueness of arbitrary
solutions of $\Psi$ outside its box. $\square$

**Corollary 17.3 (population transfer is necessary for every full optimizer).**
For any optimal common full-output map $\Phi$ of (CG.20), let $\Lambda$
be its live compression to $V$, and define
$T_{ij}=\langle i|\Lambda(|j\rangle\langle j|)|i\rangle$.
Its sign-averaged live Choi matrix is (CG.156), and

$$
\begin{aligned}
T_{01}&=(Q_*^{01})_{00}>0,&T_{10}&=(Q_*^{01})_{11}>0,\\
T_{02}&=(Q_*^{02})_{00}>0,&T_{20}&=(Q_*^{02})_{11}>0.
\end{aligned}
\tag{CG.165}
$$

Proof. The reduction $\mathcal C\Phi$ has error at most $E_*$ and
at least $E_*$ by Convention 17.1. It has precisely the same live
compression, so Theorem 17.2 applies. Directly on the original full
outputs, equality also holds throughout (CG.130)–(CG.133): the same
positive endpoint weights and saturated lower bound force every
endpoint effect to attain its individual half norm, and force every
nonnegative budget term to vanish. Thus the support and effect conclusions
of Theorem 17.2 hold before reduction as well.

In the unnormalized output-input convention,
$T_{ij}=\langle ij|J_\Lambda|ij\rangle$. Every $U\otimes U$
conjugation fixes these diagonal entries. For $i<j$, $|ij\rangle$
is coordinate $0$ and $|ji\rangle$ coordinate $1$ in its block,
which gives exactly the four indices in (CG.165). The two coordinate-$0$
positivities are (CG.117). The other two follow without new arithmetic:

$$
(Q_*^{01})_{11}=\eta_{1,*}(S_{01,*})_{00}>0,\qquad
(Q_*^{02})_{11}=\eta_{2,*}(S_{02,*})_{00}>0.
\tag{CG.166}
$$

These are the diagonal entries of the two-dimensional adjugates, using
(CG.115) and $\eta_{1,*},\eta_{2,*}>0$. Averaging has supplied no
physical sign gate. Equation (CG.156) identifies an averaged live map,
not the whole unaveraged channel or its exact-time failure laws. $\square$

## 18. A strict complete-output gap for zero-transfer live implementations

**Theorem 18.1 (Schur live maps cannot approach the credited optimum).**
Call a common full-output map zero-transfer when its live compression
satisfies $T_{ij}=0$ for every $i\ne j$ in the fixed basis $(+,-,2)$.
For a CP trace-nonincreasing live map this condition is equivalent to
having diagonal Kraus operators, and to
$\Lambda(A)=C\odot A$ with $C\succeq0$, $0\leq C_{ii}\leq1$.
There exists a constant $\epsilon_0>0$, depending only on this fixed
twelve-history task, such that every zero-transfer common full-output
map satisfies

$$
E(\Phi)\geq E_*+\epsilon_0.
\tag{CG.167}
$$

This is an existential gap in the original half full cq norm. No
numerical value of $\epsilon_0$ or solution of the restricted minimax
is asserted.

Proof. The Schur characterization is a mature finite-dimensional fact;
its trace-nonincreasing version is Theorem 2 in de Vicente and Streltsov,
[*The power of the resource theory of genuine quantum coherence*,
arXiv:1604.08031v2](https://arxiv.org/html/1604.08031v2), §II.2.
For clarity, its exact zero-transfer hypothesis here can be checked
without imposing covariance. A finite Kraus family exists for any
finite-dimensional CP map, and

$$
T_{ij}=\sum_a|(L_a)_{ij}|^2.
\tag{CG.168}
$$

All terms are nonnegative. Zero off-diagonal $T_{ij}$ therefore makes
every $L_a$ diagonal in every Kraus representation. Writing its diagonal
as $l_a$ gives $C=\sum_a l_al_a^\dagger\succeq0$ and
$\Lambda(A)=C\odot A$. Conversely a spectral factorization of $C$
gives diagonal Kraus operators and no transfer. The effect is
$\operatorname{diag}(C_{ii})$, so trace nonincrease is exactly
$C_{ii}\leq1$. This standard characterization is an intermediate step;
the task-specific conclusion is the strict gap (CG.167).

Consider ALL finite-output candidates (CG.155), independently of whether
they came from a full instrument. Their Choi/effect feasible set
$\mathcal K$ is compact: it is closed in the real vector space of
Hermitian triples, and its positive variables obey

$$
\operatorname{tr}J+\operatorname{tr}G_f+\operatorname{tr}G_o=3.
\tag{CG.169}
$$

Thus each positive variable is bounded. Let $\mathcal K_0$ impose the
closed conditions $J_{ij,ij}=0$ for all $i\ne j$. This subset is
nonempty, for example $J=0,G_f=I,G_o=0$, and compact. The twelve
finite-output errors are continuous functions of the triple, as is
their maximum. Hence

$$
\mu_0=\min_{\mathcal K_0}E_c
\quad\text{exists},\qquad \mu_0\geq E_*.
\tag{CG.170}
$$

If $\mu_0=E_*$, a minimizing finite-output channel in $\mathcal K_0$
would satisfy Theorem 17.2. Its transition diagonals are unchanged by
sign averaging, yet (CG.165)–(CG.166), applied to that theorem's same
blocks, give four strictly positive transfers. This contradicts its
membership in $\mathcal K_0$. Therefore $\mu_0>E_*$; define
$\epsilon_0=\mu_0-E_*$. This excludes equality for the relaxed finite
output task itself, not by assuming that a marginal optimizer lifts to
a full optimizer.

For every original full-output zero-transfer $\Phi$, the reduction
$\mathcal C\Phi$ belongs to $\mathcal K_0$ and retains its live map.
Consequently
$E(\Phi)\geq E_c(\mathcal C\Phi)\geq\mu_0$, which proves (CG.167).
The finite test contracts the complete norm; it supplies a lower bound
on the unchanged exact-time task, without identifying that norm with
a survival marginal or discarding its singular/other outcomes. $\square$

**Definition 18.2 (a conditional diagonal closure).** Fix the common
calibrated basis of $V$. Consider an implementation class with one
specimen and independent initial apparatus, whose only live interactions
have Kraus operators diagonal on that specimen. More generally, if $R$
is an actually retained apparatus/record, allow live Kraus operators
$\sum_j P_j\otimes B_{a,j}$ on $V\otimes R$. Allow operations
$I_V\otimes B$ on $R$, choices from actually acquired classical records,
independent randomization, finite composition, and summation over
unobserved branch records. Failure branches are absorbing and never
return population to a live direction. All apparatus, selection rules,
permissions and numerical coefficients are common, rather than
programmed by an unknown source height. No additional specimen-bearing
interaction is included in this definition.

**Corollary 18.3 (obstruction for exactly that closure).** Every common
CPTP implementation built from Definition 18.2, with all outcomes
included in the original comparison, satisfies (CG.167).

Proof. A live Kraus operator $\sum_jP_j\otimes B_{a,j}$ leaves each
specimen subspace $|j\rangle\otimes R$ invariant. Record-local operations
have the same property, and products of such operators retain it.
Thus an input $|j\rangle\langle j|\otimes\tau_R$ has live specimen
support only on $|j\rangle$ along every surviving branch. Sums,
independent mixtures and tracing out the record preserve this support.
An absorbing branch contributes no later live mass. Hence the resulting
live map has $T_{ij}=0$ for $i\ne j$, and Theorem 18.1 applies.
The same conclusion holds for any explicitly defined limit of these
live maps in Choi norm, because those zero diagonal entries form a closed
set. No continuous control limit is presumed available by this statement.
$\square$

## 19. Equal effects and reference marginals do not fix live successors

**Theorem 19.1 (a same-effects pair at the credited point).** Reuse $h$,
$b^{01},b^{02}$ and $K_0,K_{01},K_{02}$ from (CG.134). Define

$$
D_0=K_0,\qquad
D_{0j}=b^{0j}_1P_0+b^{0j}_0P_j,\qquad
U_{0j}=|0\rangle\langle j|+|j\rangle\langle0|
                        +\sum_{k\notin\{0,j\}}P_k
\quad(j=1,2).
\tag{CG.171}
$$

Replace the three live Kraus operators in (CG.135) by $D_0,D_{01},D_{02}$
and leave its five failure CP densities unchanged. Call this full
instrument $\Phi_D$; call the credited instrument $\Phi_K=\Phi_*$.
Both are CPTP on the full complex algebra. They have identical
classical live-branch probabilities, identical failure labels/times and
identical unnormalized reference marginals in every corresponding branch,
for arbitrary joint specimen/reference inputs. Nevertheless their live
successors differ, and their original complete-output performances satisfy

$$
E(\Phi_K)=E_*,\qquad E(\Phi_D)\geq E_*+\epsilon_0>E_*.
\tag{CG.172}
$$

Proof. The fixed swaps are unitary and

$$
\begin{aligned}
K_{0j}&=U_{0j}D_{0j},\\
D_{0j}^\dagger D_{0j}
 &=|b^{0j}_1|^2P_0+|b^{0j}_0|^2P_j
 =K_{0j}^\dagger K_{0j},\\
\sum_{a\in\{0,01,02\}}D_a^\dagger D_a
       +\operatorname{diag}(m_*)&=I_3.
\end{aligned}
\tag{CG.173}
$$

The last equation reuses (CG.141). The diagonal entries of $D_{0j}$
need not be positive; their signed amplitudes are retained. These are
diagonal Kraus operators, not replacements by square-root effects that
silently remove phase data. Kraus conjugations and the unchanged positive
failure densities prove complete positivity at every reference
amplification. Equation (CG.173) proves joint trace preservation.

For any complex joint operator $X$ on $V\otimes R$ and any branch $a$,
cyclicity of the partial trace on the specimen gives

$$
\begin{aligned}
\operatorname{Tr}_V[(K_a\otimes I_R)X(K_a^\dagger\otimes I_R)]
 &=\operatorname{Tr}_V[(K_a^\dagger K_a\otimes I_R)X]\\
 &=\operatorname{Tr}_V[(D_a^\dagger D_a\otimes I_R)X]\\
 &=\operatorname{Tr}_V[(D_a\otimes I_R)X(D_a^\dagger\otimes I_R)].
\end{aligned}
\tag{CG.174}
$$

This includes entangled, mixed and history-correlated references; no
factorization of $X$ has been used. Tracing the reference proves equality
of the corresponding classical branch probabilities. Failure CP maps
are identical, so their joint stopped-state/reference measures agree
on every Borel set, with the same five labels, exact-time laws and
absorbing successor. In particular, complete failure records are equal,
not only their integrated probabilities.

The live difference is already explicit on the operator test $P_0$:

$$
\begin{aligned}
\Lambda_D(P_0)&=P_0,\\
\Lambda_K(P_0)&=|h_0|^2P_0
        +|b^{01}_1|^2P_1+|b^{02}_1|^2P_2,\\
|b^{01}_1|^2+|b^{02}_1|^2&>0.
\end{aligned}
\tag{CG.175}
$$

Here $h_0$ is coordinate $0$ of $h$, not the time density $h_0(t)$.
The equality $\Lambda_D(P_0)=P_0$ uses $r_{0,*}=1$; strict positivity
uses (CG.166). This test is not an extra supplied preparation.
The difference also occurs on actual catalogue inputs. For every sign
at height $y$,

$$
\bigl(\Lambda_D(U\rho_yU^\dagger)
             -\Lambda_K(U\rho_yU^\dagger)\bigr)_{22}
 =\frac{(Q_*^{02})_{00}}2-\frac y{128}(Q_*^{02})_{11}.
\tag{CG.176}
$$

The right side is a strictly decreasing affine function of $y$, so it
vanishes at at most one of the three distinct heights. Thus the live
successors differ for at least eight of the twelve actual histories.
All four signs and all complex coherence entries remain part of the
maps; diagonal statistics have only been used to witness inequality.
Since every $D_a$ is diagonal, $\Phi_D$ is zero-transfer and (CG.167)
gives its strict performance separation. The value for $\Phi_K$ is
credited Theorem 16.1, not a new minimax calculation.

For the original five-mode algebra use the same fixed isometry $E$ and
$P_V$ as (CG.142). Set $\widehat K_a=EK_aE^\dagger$ and
$\widehat D_a=ED_aE^\dagger$, and use for BOTH instruments the full
failure measures

$$
 h_0(t)\left[w_\ell\operatorname{tr}
       (E\operatorname{diag}(m_*)E^\dagger A)
  +\mathbf1_{\ell=2}\operatorname{tr}((I_5-P_V)A)\right]dt\,P_f.
\tag{CG.177}
$$

Their common total effect is $I_5$. The complementary live support is
sent to original failure label $2$ with its entire mass; cross operators
between $V$ and its complement have the same zero image in both
instruments. Thus the equality of effects and reference marginals
extends to arbitrary complex five-mode/reference inputs. On the actual
inputs the complete outputs and errors are those already stated.

The local Kraus label $a$ can be kept as an internal generated record
when defining the branch comparison in (CG.174). The canonical live
output in (CG.20) sums over it. No claim of the same error for a different
joint task that exposes this extra label is being made. This is the
instance-specific strengthening of the mature distinction between an
effect and an instrument; the repository's
`StaticEffectSequentialSeparation.same_effects_different_two_step_joint_law`
and `FiniteKrausInstrumentBornMarginal.finite_kraus_instrument_born_marginal`
already supply the corresponding general lesson and finite Born identity.
Here the same-effects pair straddles the exact benchmark and the strict
zero-transfer gap. $\square$

## 20. A conditional synthesis interface and its native boundary

**Definition 20.1 (explicit additional services).** A conditional
realization of $\Phi_K$ consists of the following COMMON services,
with parameters fixed by $u_*$ before receiving the specimen:

1. A calibrated diagonal instrument on $V$ with distinguishable live
   operations $A\mapsto D_aAD_a^\dagger$, $a=0,01,02$, and complementary
   effect $M=\operatorname{diag}(m_*)$. Its complete branch operations,
   including signed/complex amplitudes, are supplied. Equivalently its
   complementary precursor can have Kraus operator $\sqrt M$ before the
   absorbing router. The instrument acts on the sole specimen and tensors
   by identity on every retained reference.
2. On a live record $01$ or $02$, the corresponding fixed calibrated
   swap $U_{01}$ or $U_{02}$ on that specimen; on record $0$, identity.
   This is control by a generated branch, not by an unknown height,
   sign or history. Each swap fixes the remaining active basis direction.
3. An absorbing router for the complementary branch, with stopped
   successor $f$, original-label distribution
   $w=(0,1/4,1/2,1/4,0)$, and no later specimen operation. For the
   five-dimensional completion it also routes $V^\perp$ to original
   label $2$, using a supplied calibrated support decomposition
   $V\oplus V^\perp$ and exactly (CG.177).
4. An EXACT-TIME output service with normalized law
   $h_0(t)dt=2(1+t)^{-2}dt$ on $[0,1]$. It is independent of the
   specimen, reference and branch conditional state. The router records
   the label and this exact time together and preserves the old archive,
   source/epoch, aligned clock, permissions and declared controller
   updates. For a physical first-failure realization, this service must
   additionally make the absorbing event occur at that actual elapsed
   time, with live output at terminal time $1$ and no later positive-
   carrier action on a failed branch. An ideal timestamp register alone
   is not that physical timing service.

The live branch record may be discarded under the fixed canonical output
interpretation after its swap. Independent randomness here supplies no
readable history, helper specimen, survival prior, reset, retry or
source-bound programme. The services and their permissions are hypotheses
of this interface, not consequences of the comparison class.

**Proposition 20.2 (conditional whole-complex construction).** If the
services of Definition 20.1 are supplied with their stated complete
operations, they realize the common CPTP law (CG.135) and its five-mode
extension (CG.142). Their canonical output performance is $E_*$.
The exact random timestamp has inverse CDF

$$
H_0(t)=\int_0^t\frac2{(1+s)^2}ds=\frac{2t}{1+t},\qquad
H_0^{-1}(u)=\frac{u}{2-u}\quad(0\leq u\leq1).
\tag{CG.178}
$$

Proof. On each live branch the composite Kraus operator is $D_0=K_0$
or $U_{0j}D_{0j}=K_{0j}$ by (CG.173). Summing these unnormalized
branches gives exactly $\Lambda_*$. The complementary precursor and
absorbing trace-and-prepare router compose to the CP density
$w_\ell h_0(t)\operatorname{tr}(MA)dt\,P_f$.
At reference amplification its reference factor is
$\operatorname{Tr}_V[(M\otimes I_R)X]$, so the construction preserves
the entire stipulated joint operation, not just scalar probabilities.
The complementary five-mode branch adds precisely the second term in
(CG.177). Completeness is (CG.173) plus the complementary support effect,
and no branch mass is divided by its probability. These operator
identities hold for every complex matrix unit and therefore every
complex input, including all actual coherences. The performance statement
reuses Theorem 16.1 on the same canonical complete outputs.

Integration and inversion give (CG.178); $2-u\geq1$ throughout the
unit interval. This specifies a measurable random variable with the
required density. It proves neither finite-bit exact time storage nor
that a device emits its first absorbing failure at that time. The latter
claim depends on the additional physical timing service explicitly
required in Definition 20.1. A time-bin approximation or a timestamp
written after another failure would change the output contract.
$\square$

**Convention 20.3 (source correspondence, attribution and remaining scope).**
The native objects used here are the actual twelve histories of §§2–4,
not a replacement source. The following correspondence fixes the limits
of applying Corollary 18.3 or Proposition 20.2 to those objects.

| Source and mathematical contract | Consequence and unsupplied bridge |
| --- | --- |
| `OriginalControlComposition.OriginalControl`, `FiniteC1Control`, `concatenate_original` and its owning Scribe | These are regularity, strict-domain and literal chronological composition statements about real paths. They construct no common actuator, unknown-height sensor or swap on $M_3$. The private absolute-continuity and concatenation lemmas support those same path conclusions. |
| [Acquired Continuation Limits][ACR], Definitions 2.3–2.5 and Proposition 4.1 | One normalized unresolved specimen, fixed common metadata and all-outcome error; the calibrated $K_x$ and complete original failure densities are source-indexed targets. Their dependence on $x$ neither makes $x$ readable nor installs a common implementation. |
| [Quantum Carrier Minimum](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md), Definition 1.3, (QC.8)–(QC.17), Theorem 3.1 | A fixed calibrated qutrit correspondence retains every separate failure CP measure and every actual joint reference. The prescribed no-failure kernels are diagonal in $(+,-,2)$, conditional on the waveform and calibrated instrument services. Encoding, decoding, clocks, recording and operations remain declared resources; the representation theorem acquires none of them. |
| [Instrument Boundaries](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md), §§4–5.2, Proposition 17.2 and Definition 17.3 | Canonical prescribed no-failure filters and full stopped successors are conditional CP instruments. The known-height/full-orbit rigidity and programme contracts differ from this approximate three-height common-channel task. They do not show that every callable native operation belongs to Definition 18.2. |
| [Probability/Phase Transport](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md), §8.5 and §9.1 | The actual fields include $P=\partial_k$ and $Q=(1/2-k/r)\partial_u-(k/r)\partial_v$, with $[P,Q]=-(\partial_u+\partial_v)/r\ne0$. Probability-changing paths and this noncommuting geometry cannot be identified with an exhaustive Schur operation menu. The relative-path convention itself asserts no additional physical actuator. |

The current source sections and path supplier named in this table
are taken at revision `3c285d3b1e09bcfe8dcc9818db0665914d81bbdf`;
the historical links [AC] and [IB] retain their earlier fixed attribution
for the credited target. No earlier source hypothesis is replaced by a
stronger service in Definition 20.1. The five-mode support decomposition
and conditional swaps in that definition are resources in their own
right, not arbitrary rotations authorized by geometric reachability.

The new task-specific deductions are (CG.156)–(CG.166), the strict gap
(CG.167) for the explicitly defined subclass, and the same-effects
benchmark/separation pair (CG.171)–(CG.177) with its conditional synthesis.
Their provenance is `repo-derived` ordinary mathematics conditional on
the credited certificate, rather than another certificate for (CG.154).
The finite Choi/Kraus framework is reused from the repository's
`FiniteKrausRepresentation` (including `choi_of_kraus`,
`choi_PSD_iff_CP_map` and `krausRepresentation`) and its cited Physlib
source at `6a09b2d1761a0d4430083045a247eb121d8da260`.
These declarations are source references here, not new compiled
applications. Standard CP/TP facts are also literature-attested in
Heinosaari, Jivulescu, Reeb and Wolf,
[*Extending quantum operations*, arXiv:1205.0641v3](https://arxiv.org/html/1205.0641v3),
§§2.1 and 6.1. Their at-most-qubit Theorem 5 is not used as a qutrit
compatibility criterion.

The Schur equivalence is the cited de Vicente–Streltsov §II.2 result,
not new mathematical content. Sign covariance and its population and
reverse-coherence blocks are literature-attested in Nechita and Park,
[*Random covariant quantum channels*, arXiv:2403.03667v2](https://arxiv.org/html/2403.03667v2),
§5, especially Proposition 5.3. Covariance there permits population
transfer and does not imply diagonal Kraus operators. The present
trace-decreasing live block is handled by its explicit positive Choi
budget, rather than importing a trace-preserving hypothesis. The
Helstrom support/equality argument, determinant first differential and
finite-dimensional compactness used above are mature tools; their
particular equality-to-stationarity composition and all-optimizer
consequence are proved in §17.

A related recent joint-operation contract is Definition 1 and Proposition 1
of Muñoz-Moller, Leppäjärvi and Heinosaari,
[*Adversarial Information Gain in Non-ideal Quantum Measurements*,
arXiv:2602.20941v1](https://arxiv.org/html/2602.20941v1): meter/instrument
compatibility requires one joint instrument with both prescribed
marginals; its conjugate-instrument characterization uses meters on
a dilation ancilla. Equality of effects in (CG.173) grants no such
access. Jing, Guo, Zhu, Yao and Wang,
[*Programmable Open Quantum Systems*, arXiv:2512.08279v1](https://arxiv.org/html/2512.08279v1),
Propositions 3–4, instead concern retrieving a fixed-generator
Lindbladian semigroup from its programme family on arbitrary inputs.
Those hypotheses supply neither the diagonal instrument nor the swaps
and exact-time service required here; their exclusions are not a native
impossibility theorem for this stopped task. These comparisons bound
the claimed reuse and assert no worldwide originality.

The source result `SchurHornEntropyMonotonicity.spectral_readout_entropy_le`
concerns a finite unitary conjugate of a diagonal nonnegative spectrum
and its doubly stochastic diagonal readout. It supplies no equality
classification for this trace-decreasing live map or exact-time stopped
instrument; no entropy inference is used here.

The all-optimizer necessity does not establish uniqueness of the whole
channel or its failure laws. The subclass gap does not establish
impossibility for the full native operation menu. Exact synthesis in
Definition 20.1 is conditional on actually supplied operations and
permissions, and is distinct from acquiring them from the original
unresolved specimen. The global original acquisition/physical realization
problem and the continuing programme remain open. No Lean/kernel evidence,
physical efficiency bound or finite exact-clock implementation is asserted.

## 追加锚（本行以下为增补区）

## 21. The original experiment across an actual acquisition cut

**Convention 21.1 (unchanged source, processor and output).** In §§21–25,
the experiment remains (CG.20), with the credited value and instrument
of Theorem 16.1 and the all-optimizer conclusion of Theorem 17.2.
The fixed isometry $E:\mathbb C^3\to\mathbb C^5$ has columns
$(|+\rangle,|-\rangle,|2\rangle)$ from (CG.6). In these coordinates,
the twelve ACTUAL normalized reached-old-live-cut inputs are

$$
\rho_{y,e,n}=U_{e,n}\rho_yU_{e,n}^\dagger,\qquad
U_{e,n}=\operatorname{diag}(e,n,1),\qquad y\in\{5,16,27\},
\tag{CG.179}
$$

where $\rho_y$ and $B_y$ are exactly (CG.111). The correspondence to
the original source parameters, rather than a newly prepared ensemble, is

$$
x=y/256,\qquad e=(-1)^{\beta/\pi},\qquad n=e(-1)^m.
\tag{CG.180}
$$

| Original $(\beta,m)$ | $(e,n)$ |
| --- | --- |
| $(0,0)$ | $(1,1)$ |
| $(0,1)$ | $(1,-1)$ |
| $(\pi,0)$ | $(-1,-1)$ |
| $(\pi,1)$ | $(-1,1)$ |

The ideal live block is $U_{e,n}B_yU_{e,n}^\dagger$. Each of the five
failure sectors has the entire measure
$w_\ell f_y(t)dt\,P_f$, where
$w=(0,1/4,1/2,1/4,0)$ and $f_y(t)=6y/(y+6t)^2$ on $[0,1]$.
Its total mass is $6/(y+6)$, complementary to the live mass $y/(y+6)$.
The objective is the maximum over these twelve histories of HALF the
complete cq trace norm. All complex live coherences, exact failure
labels/times, singular measures, aborts, rejections, wrong support and
additional zero-ideal sectors remain in that norm. No subsequent
acquisition outcome is conditioned upon. The earlier reach probabilities
(CG.8) are not source priors.

There is one common CPTP processor on the entire complex input algebra,
with the original five-mode completion and common metadata of Definition
3.1. Its coefficients cannot depend on $y,e,n$ or a readable history.
The compressed live map $\Lambda:M_3\to M_3$ is CP and TNI; it is
generally not TP. The finite necessary output test $\mathcal C$ of
Convention 17.1 is used only to obtain lower bounds for this full task.

**Definition 21.2 (actual tagged acquisition factorization).** An
acquisition cut lies after receiving the sole normalized specimen and
before later execution. Its placement in the original aligned clock and
the duration of acquisition are obligations of the implementation; this
definition grants no extra execution time. In the finite version its entire retained
input-dependent quantum payload and an actual classical record have algebra

$$
\mathcal B=\bigoplus_{\alpha\in A}M_{d_\alpha}(\mathbb C),
\qquad |A|<\infty,\quad 1\leq d_\alpha<\infty.
\tag{CG.181}
$$

The implementation supplies common CP maps $\mathcal E_\alpha$ and
common full-output CPTP maps $\mathcal R_\alpha$ such that

$$
\begin{aligned}
\mathcal E_\alpha &:M_3\longrightarrow M_{d_\alpha},
&\sum_\alpha\mathcal E_\alpha^\dagger(I_{d_\alpha})&=I_3,\\
\Phi&=\sum_\alpha\mathcal R_\alpha\mathcal E_\alpha,
&p_\alpha(\rho)&=\operatorname{tr}\mathcal E_\alpha(\rho).
\end{aligned}
\tag{CG.182}
$$

These are identities on ALL complex matrix units, not a fit only to
twelve densities. The actual five-mode implementation must restrict to
(CG.182); its action outside $V$ retains its own full TP contract.
Only the sum of encoder branches is TP. Each branch is CP/TNI, including
branches destined for failure or abort. Every decoder includes all its
outcomes and is TP; its live compression $\mathcal R_\alpha^L$ is TNI.
The record $\alpha$ is generated in the implementation from this input,
and may be kept internally or discarded by the canonical interpretation.
It is not an unknown source label granted to the implementation.

The block $M_{d_\alpha}$ counts JOINTLY every quantum system accessible
to later execution that can influence its output: the specimen if retained,
quantum memory and controller parts, accessible environment, returned
systems, and any retained entanglement share. There is no later source
callback, helper specimen, copy, retry, source-dependent timing port or
uncounted quantum bypass. A passive inaccessible reference is allowed,
but neither operation can use it. All identities tensor by its identity.
Independent local ancillary states can be absorbed into the encoder and
decoder. Independent blank ancillas introduced later remain free. A
receiver's share of entanglement with an encoder system is not such a
blank and must be counted in the joint payload. Fixed common classical
metadata and actually acquired classical records remain available.

An algebraic Kraus decomposition, Choi decomposition or sign average
does not by itself supply this classical record, an observable hardware
flag, encoding access or later controlled operations. A coherent sum of
putative branch subspaces is one quantum payload until a classical
direct-sum factorization is actually supplied.

**Convention 21.3 (alphabet, integral and closure scope).** The primary
version is (CG.181). The same necessity statements below also cover
countable classical $A$ with finite-dimensional fibres when (CG.182)
converges as CP instruments and its total effect is $I_3$. They cover
an explicitly supplied integral factorization

$$
\Phi=\int \mathcal R_\alpha\mathcal E_\alpha\,d\nu(\alpha),
\qquad
\int \mathcal E_\alpha^\dagger(I)\,d\nu(\alpha)=I_3,
\tag{CG.183}
$$

provided the fibre dimensions are measurable finite integers, the encoder
and live-decoder Kraus fields are measurable, and the effects and live
Choi matrices are integrable. Decoders are full-output TP almost
everywhere. Encoder densities are CP, but need not individually be TNI
relative to $\nu$; it is their integrated instrument that has total
effect $I_3$. Branch probabilities are integrals of unnormalized encoder
traces. These hypotheses specify the integral model; no disintegration
theorem or arbitrary infinite-dimensional coding theorem is presumed.
The lower-dimensional class has $d_\alpha\leq2$ everywhere or almost
everywhere. Its closure statement below concerns convergence of the
reduced finite Choi/effect triples (CG.155), not compactness of the
complete exact-time output space. A limit without an actual tagged
factorization carries the class obstruction but no inferred branch flag
or branch-probability interpretation.

## 22. Every optimal live map requires three-dimensional coherence

**Theorem 22.1 (a strict homogeneous Schmidt witness for every optimizer).**
Use the output-input, unnormalized Choi convention (CG.125), and put

$$
\begin{aligned}
|\Omega\rangle&=|00\rangle+|11\rangle+|22\rangle,
&W_3&=|\Omega\rangle\langle\Omega|-2I_9,\\
t_*&=\operatorname{tr}H_*+\operatorname{tr}Q_*^{01}
                             +\operatorname{tr}Q_*^{02},
&\delta_*&=\mathbf1^TH_*\mathbf1-2t_*.
\end{aligned}
\tag{CG.184}
$$

For every optimal full-output common processor, and also every optimal
finite-test channel in (CG.155), its actual live Choi matrix satisfies

$$
\operatorname{tr}(W_3J_\Lambda)=\delta_*>\frac{19}{10}.
\tag{CG.185}
$$

In particular its live Choi matrix has Schmidt number exactly three:
it admits no decomposition into positive rank-one terms whose vectors,
viewed as $3$ by $3$ matrices, all have rank at most two. Equivalently,
every Kraus representation of the live CP map contains a rank-three
operator. This is a coherent bottleneck dimension statement; it is not
an entropic coherent-information or capacity formula.

Proof. The mature Schmidt-number definition and maximally-entangled
overlap bound are Terhal–Horodecki,
[*A Schmidt number for density matrices*, quant-ph/9911117v4](https://arxiv.org/pdf/quant-ph/9911117v4),
Definition 1 and Lemma 1. For the present unnormalized convention,
write $|L\rangle\!\rangle=\sum_{a,i}L_{ai}|ai\rangle$. The exact
homogeneous bound is

$$
\operatorname{rank}L\leq2
\quad\Longrightarrow\quad
|\operatorname{tr}L|^2\leq2\|L\|_F^2
\quad\Longrightarrow\quad
\langle\!\langle L|W_3|L\rangle\!\rangle\leq0.
\tag{CG.186}
$$

Indeed $|\operatorname{tr}L|$ is at most the sum of its singular values,
and Cauchy–Schwarz bounds their squared sum by twice their sum of
squares when at most two are nonzero. This holds for arbitrary complex
$L$. Summing gives the bound on the entire homogeneous cone

$$
\mathfrak S_2=\left\{\sum_s|L_s\rangle\!\rangle
 \langle\!\langle L_s|:\operatorname{rank}L_s\leq2\right\}.
\tag{CG.187}
$$

There is no trace-one condition in (CG.186)–(CG.187). The
Choi/Kraus–Schmidt equivalence is the standard vectorization identity;
Chruściński–Kossakowski,
[*On partially entanglement breaking channels*, quant-ph/0511244v1](https://arxiv.org/pdf/quant-ph/0511244v1),
§2, (6)–(13), give it for TP channels with normalized Choi states.
Here it is applied directly to positive rank-one Choi sums, so no TP
assumption is imposed on the live map or an individual branch. Sekatski,
[*The bottleneck dimension of quantum operations*, arXiv:2608.25010v1](https://arxiv.org/pdf/2608.25010v1),
§II.A, (2) and Definition 1, states the corresponding classical-assisted
single-channel bottleneck and CP-map Schmidt number. No independently
programmable family of instruments is supplied here.

Theorem 17.2 fixes $\overline J_\Lambda=J_*$ for every channel in the
statement. Each actual sign satisfies
$(U_{e,n}\otimes U_{e,n})|\Omega\rangle=|\Omega\rangle$.
Consequently its conjugation fixes $W_3$, and hence

$$
\operatorname{tr}(W_3J_\Lambda)
 =\operatorname{tr}(W_3\overline J_\Lambda)
 =\mathbf1^TH_*\mathbf1
    -2(\operatorname{tr}H_*+\operatorname{tr}Q_*^{01}
                              +\operatorname{tr}Q_*^{02}).
\tag{CG.188}
$$

The two off-diagonal character blocks have zero pairing with
$|\Omega\rangle$. Its squared norm is $3$, not $1$; dividing the Choi
matrix by $3$ would divide both sides of (CG.185) by $3$. The real-sign
input representation is $\overline U=U$, as in §14. This invariance is
why the averaged live matrix constrains every unaveraged optimizer,
without asserting their equality.

The following additional coarse rational enclosures follow from the
credited box $C$ in Proposition 13.2, using just (CG.112), (CG.113) and
the adjugate formulas (CG.116). They hold throughout that box; no root
identity is needed for these new inequalities.

| Quantity | Strict lower bound | Strict upper bound |
| --- | --- | --- |
| $(H)_{00}$ | $968/1000$ | $970/1000$ |
| $(H)_{11}$ | $498/1000$ | $500/1000$ |
| $(H)_{22}$ | $655/1000$ | $656/1000$ |
| $(H)_{01}$ | $695/1000$ | $696/1000$ |
| $(H)_{02}$ | $796/1000$ | $798/1000$ |
| $(H)_{12}$ | $571/1000$ | $573/1000$ |
| $\operatorname{tr}Q^{01}+\operatorname{tr}Q^{02}$ | $35/1000$ | $36/1000$ |

For an exact arithmetic specification of these comparisons, embed
each endpoint $c_i\pm10^{-24}$ on the directed grid with denominator
$D=2^{224}$, as in (CG.118). Form $v_yv_y^T/(v_y^Tv_y)$ for
$y=5,27$, then $A_y,N,\zeta,S_0,S_{01},S_{02}$ in their displayed
order. Embed the rational diagonal entries of $\rho_y$ directly and
its off-diagonal entries as directed square roots of $p_{yi}p_{yj}$.
For each adjugate entry use the signed transposed minor: for a $3$ by
$3$ matrix $\operatorname{adj}(S)_{ij}=(-1)^{i+j}
\det S[\widehat j,\widehat i]$, with each two-dimensional determinant
evaluated as $ad-bc$. For a two-dimensional adjugate use
$\left(\begin{smallmatrix}d&-b\\-c&a\end{smallmatrix}\right)$.
Multiply by $1000\eta_0,\eta_1,\eta_2$ respectively. Round every
product and quotient outwards on that same grid; square roots use
(CG.118). All divided chart denominators are positive. These operations
give the seven strict comparisons in the table. Their coarse endpoints
alone give the new margin

$$
\begin{aligned}
\delta_*
 &=2(H_{01}+H_{02}+H_{12})
       -(H_{00}+H_{11}+H_{22})
       -2(\operatorname{tr}Q^{01}+\operatorname{tr}Q^{02})\\
 &>\frac{2(695+796+571)-(970+500+656)-2\cdot36}{1000}
   =\frac{963}{500}>\frac{19}{10}.
\end{aligned}
\tag{CG.189}
$$

By (CG.186), (CG.185) excludes $J_\Lambda\in\mathfrak S_2$.
Every vector in $\mathbb C^3\otimes\mathbb C^3$ has Schmidt rank
at most three, so the Schmidt number is exactly three. No whole-channel
or exact-time failure-law uniqueness is used or obtained. $\square$

## 23. Strict complete-output separation for acquisition through qubits

**Theorem 23.1 (classical-assisted lower-dimensional acquisition gap).**
There is a task-dependent constant $\epsilon_2>0$ such that every common
full-output processor whose compressed live Choi matrix belongs to
$\mathfrak S_2$ satisfies

$$
E(\Phi)\geq E_*+\epsilon_2.
\tag{CG.190}
$$

In particular this holds for every actual factorization of Definition
21.2 or Convention 21.3 with $d_\alpha\leq2$, allowing all its classical
records, independent blanks, arbitrary common decoders and all outcomes.
It also holds for the closure of this class in reduced Choi/effect
triples. The gap is existential; neither a numerical additive error gap
nor the restricted optimum is asserted.

Proof. The standard bottleneck mechanism in Sekatski §II.A is especially
simple for the actual live submap. Choose encoder Kraus matrices
$C_{\alpha u}:\mathbb C^3\to\mathbb C^{d_\alpha}$ and live-decoder
Kraus matrices $D_{\alpha v}:\mathbb C^{d_\alpha}\to\mathbb C^3$.
Their products give

$$
\Lambda(A)=\sum_{\alpha,u,v}
 L_{\alpha vu}A L_{\alpha vu}^\dagger,
\qquad L_{\alpha vu}=D_{\alpha v}C_{\alpha u},
\qquad \operatorname{rank}L_{\alpha vu}\leq d_\alpha.
\tag{CG.191}
$$

This uses the same joint implementation, not separately attained output
laws. The live-decoder budget is $\sum_vD_{\alpha v}^\dagger
D_{\alpha v}\preceq I_{d_\alpha}$; equality need not hold. Thus
the product-rank argument gives $J_\Lambda\in\mathfrak S_2$ without
treating a live branch as TP or dividing by a branch probability.

For compactness, normalized rank-at-most-two vectors form a compact
set, and their rank-one projectors do also. Their convex hull in the
finite-dimensional Hermitian matrix space is compact. Consequently
$\mathfrak S_2\cap\{J:\operatorname{tr}J\leq3\}$ is compact, including
$J=0$. This is the homogeneous form of Terhal–Horodecki's compact
Schmidt-number sets. Positive countable sums and the integrals specified
in (CG.183) stay in that cone by closedness and integrability.

Let $\mathcal K$ be ALL finite-output triples in (CG.155) and put

$$
\mathcal K_2=\{(J,G_f,G_o)\in\mathcal K:J\in\mathfrak S_2\},
\qquad \mu_2=\min_{\mathcal K_2}E_c.
\tag{CG.192}
$$

The budget $\operatorname{Tr}_{\rm out}J+G_f^T+G_o^T=I_3$ gives
$\operatorname{tr}J+\operatorname{tr}G_f+\operatorname{tr}G_o=3$.
Positivity makes $\mathcal K_2$ compact; it is nonempty, for example
at $J=0,G_f=I_3,G_o=0$. The maximum of twelve continuous finite-output
errors is continuous, so $\mu_2$ exists. Convention 17.1 gives
$\mu_2\geq E_*$. Equality would supply an optimizer in $\mathcal K_2$,
contradicting Theorem 22.1. Hence $\epsilon_2=\mu_2-E_*>0$.

The reduction $\mathcal C\Phi$ retains the live map and contracts the
complete norm. Therefore
$E(\Phi)\geq E_c(\mathcal C\Phi)\geq\mu_2$. Any convergent sequence
of reduced triples with Schmidt number at most two has a limit in
$\mathcal K_2$, proving exactly the stated closure result. Neither
compactness of the complete output space nor a lift of an arbitrary
finite triple to an optimal exact-time law is needed. $\square$

## 24. A positive acquired high-dimensional mass on every original input

**Theorem 24.1 (uniform unconditional branch-mass necessity).** Suppose
an ACTUAL tagged factorization in Definition 21.2 or Convention 21.3
realizes a common processor attaining $E_*$. Let
$A_{\geq3}=\{\alpha:d_\alpha\geq3\}$ and define

$$
\begin{aligned}
\Lambda_H&=\sum_{\alpha\in A_{\geq3}}
                 \mathcal R_\alpha^L\mathcal E_\alpha,\\
p_H^{\rm acq}(\rho)&=\sum_{\alpha\in A_{\geq3}}
                         \operatorname{tr}\mathcal E_\alpha(\rho),
&p_H^L(\rho)&=\operatorname{tr}\Lambda_H(\rho).
\end{aligned}
\tag{CG.193}
$$

Use the corresponding integrals in the integral model. Then, for EVERY
normalized $\rho\in M_3$, and thus for each of all twelve original
inputs individually,

$$
p_H^{\rm acq}(\rho)\ \geq\ p_H^L(\rho)
 \ \geq\ \frac{\delta_*^2}{24}
 \ >\ \frac{361}{2400}\ >\ \frac3{20}.
\tag{CG.194}
$$

The probability is measured on the original normalized reached-cut
specimen, before any new postselection. The stronger middle quantity
counts branches that both traverse a high-dimensional acquisition block
and later contribute to the canonical supported live output. No source
prior, external entangled test preparation or observed extra flag is
required for this bound.

Proof. Decompose the actual live channel into the low- and high-block
contributions $\Lambda=\Lambda_L+\Lambda_H$. Their Choi matrices are
positive, and (CG.191) puts $J_L$ in $\mathfrak S_2$. Equations
(CG.185)–(CG.186) give

$$
\delta_*\leq\operatorname{tr}(W_3J_H).
\tag{CG.195}
$$

The high-block contribution is a finite-dimensional CP submap even if
the supplied classical alphabet is infinite. Choose any finite Kraus
representation $\Lambda_H(A)=\sum_s L_s A L_s^\dagger$ of this aggregate
map. It need not be the observed encoder record. Full TP of the processor
and positivity of the other output branches imply

$$
\Lambda_H^\dagger(I)\preceq I_3,\qquad
t_H:=\sum_s\|L_s\|_F^2=\operatorname{tr}J_H\leq3.
\tag{CG.196}
$$

For a unit vector $\psi$, let $P=|\psi\rangle\langle\psi|$,
$Q=I-P$, and set

$$
\begin{aligned}
p&=\sum_s\|L_s\psi\|^2=p_H^L(P),\\
a_s&=\operatorname{tr}(QL_s),
&b_s&=\operatorname{tr}(PL_s)=\langle\psi|L_s|\psi\rangle.
\end{aligned}
\tag{CG.197}
$$

Hilbert–Schmidt Cauchy–Schwarz on the rank-two projection $Q$, and
then on the unit vector $\psi$, give

$$
\sum_s|a_s|^2\leq2(t_H-p),\qquad
\sum_s|b_s|^2\leq p.
\tag{CG.198}
$$

For the first inequality, take an orthonormal basis with first vector
$\psi$: the squared modulus of the sum of the other two diagonal entries
is bounded by twice the squared Frobenius norm of the other two columns. Equivalently
$\|L_sQ\|_F^2=\|L_s\|_F^2-\|L_s\psi\|^2$.
Trace and Frobenius norm are invariant under this simultaneous basis
change. Thus the calculation includes all complex phases, not just real
matrix entries or the sign-invariant subfamily.

Since $\operatorname{tr}L_s=a_s+b_s$, another Cauchy–Schwarz inequality
over $s$ yields

$$
\begin{aligned}
\operatorname{tr}(W_3J_H)
 &=\sum_s|a_s+b_s|^2-2t_H\\
 &\leq2(t_H-p)+p+2\sqrt{2(t_H-p)p}-2t_H\\
 &=2\sqrt{2(t_H-p)p}-p
 \leq2\sqrt{6p}.
\end{aligned}
\tag{CG.199}
$$

Here $0\leq p\leq t_H\leq3$. Combining (CG.195) with (CG.199)
and squaring nonnegative quantities gives $p\geq\delta_*^2/24$.
For any mixed normalized input, a spectral decomposition and linearity
of $p_H^L$ give the same lower bound. Finally,
$\mathcal R_\alpha^L$ is TNI, so summing its trace inequalities gives
$p_H^L\leq p_H^{\rm acq}$. The strict arithmetic in (CG.194) follows
from $\delta_*>19/10$ and
$(19/10)^2/24=361/2400>3/20$.

All sums defining low/high submaps are positive CP sums; in (CG.183)
they are integrals over the measurable dimension sets. Closedness of
$\mathfrak S_2$, integrable effects and the finite input/output live
algebras justify the same split and finite Kraus representation of the
aggregate high submap. This proves the countable and specified integral
versions without interpreting a limiting virtual split as an actual flag.
$\square$

## 25. Abstract sufficiency, counterexamples and the native boundary

**Proposition 25.1 (an explicit sufficient acquisition factorization).**
For the credited channel $\Phi_*$ there is an abstract factorization
(CG.182) with fibre dimensions $3,2,2,1,1$, and a scalar extra branch
for its original five-mode completion. In that factorization the sole
three-dimensional branch has actual-input probability

$$
p_3(\rho_{y,e,n})
 =H_{00,*}\frac y{128}
   +H_{11,*}\frac{64-y}{128}+\frac{H_{22,*}}2.
\tag{CG.200}
$$

It is independent of the four signs. For $y=5,16,27$ respectively it
belongs to $(595/1000,596/1000)$, $(635/1000,637/1000)$ and
$(676/1000,678/1000)$. These are probabilities for this construction,
not an optimal lower bound for arbitrary factorizations.

Proof. Retain the signed amplitudes of (CG.134). On the qutrit branch
use encoder Kraus matrix $C_0=K_0$ and decode by the live identity.
On branch $0j$, $j=1,2$, use a two-dimensional carrier with basis
$|q_0\rangle,|q_1\rangle$ and put

$$
\begin{aligned}
C_{0j}&=b^{0j}_1|q_0\rangle\langle0|
                +b^{0j}_0|q_1\rangle\langle j|,\\
V_{0j}&=|j\rangle\langle q_0|+|0\rangle\langle q_1|,
&V_{0j}^\dagger V_{0j}&=I_2,
&V_{0j}C_{0j}&=K_{0j}.
\end{aligned}
\tag{CG.201}
$$

The decoder $X\mapsto V_{0j}XV_{0j}^\dagger$ is TP into the live
output. For each $k=1,2$, a scalar acquisition branch has Kraus row
$C_{f,k}=\sqrt{m_{k,*}}\langle k|$. Its decoder sends scalar $s$ to
the entire five-labelled failure law
$s\,w_\ell h_0(t)dt\,P_f$ with $h_0(t)=2/(1+t)^2$.
This decoder is TP since $\sum_\ell w_\ell=1$ and
$\int_0^1h_0(t)dt=1$. Equation (CG.141) gives the JOINT encoder
normalization

$$
C_0^\dagger C_0+
 \sum_{j=1}^2C_{0j}^\dagger C_{0j}
 +\sum_{k=1}^2C_{f,k}^\dagger C_{f,k}=I_3.
\tag{CG.202}
$$

The branch products and failure maps give exactly (CG.135) on every
complex matrix, including at arbitrary passive reference amplification.
For five modes, compress the supported branches by
$A\mapsto E^\dagger AE$. Add the scalar CP branch
$A\mapsto\operatorname{tr}((I_5-EE^\dagger)A)$, decoded to original
failure label $2$ with law $h_0(t)dt$. Its effect completes $EE^\dagger$
to $I_5$, and the resulting full map is precisely (CG.142), including
the discarded cross-support entries. No new output label is exposed.

The table in Theorem 22.1 makes each diagonal entry of $H_*$ positive.
Its rank-one factorization $H_*=hh^T$ makes $C_0$ rank three;
both other live matrices have rank two by (CG.165)–(CG.166).
The qutrit encoder effect is
$C_0^\dagger C_0=\operatorname{diag}(H_{00,*},H_{11,*},H_{22,*})$,
which proves (CG.200). The more precise rational enclosures from the
same endpoint calculation used in Theorem 22.1 are

$$
\begin{aligned}
0.968927785409&<H_{00,*}<0.968927785410,\\
0.498837910301&<H_{11,*}<0.498837910302,\\
0.655285923793&<H_{22,*}<0.655285923794.
\end{aligned}
\tag{CG.203}
$$

Substitution of $y=5,16,27$ in (CG.200) gives the stated coarse
probability intervals. Every branch is unnormalized throughout.
$\square$

**Proposition 25.2 (boundaries of the resource inference).** A nominal
three-dimensional output span does not imply the obstruction (CG.185),
and a three-dimensional carrier does not suffice for optimal performance.
Omitting an accessible entanglement share from the cut can invalidate
the dimension obstruction. None of these facts supplies a native
acquisition or timing service.

Proof. The qutrit dephasing channel has Kraus matrices $P_0,P_1,P_2$
of rank one and has a measure-and-prepare factorization with scalar
quantum fibres, despite its three-dimensional output span. Its witness
pairing is $3-2\cdot3=-3$. Conversely the qutrit identity channel has
Choi matrix $|\Omega\rangle\langle\Omega|$ of Schmidt number three.
If it always outputs live, its canonical failure mass at height $5$ is
zero, whereas the ideal mass is $6/11$. The effect of the entire failure
register therefore gives $E\geq6/11>E_*$. Three-dimensional coherence
is necessary here, not a sufficient performance specification.

At the rank-two boundary $L=\operatorname{diag}(1,1,0)$,
$|\operatorname{tr}L|^2=2\|L\|_F^2=4$; the non-strict sign in
(CG.186) is essential. For $L=I_3$, its witness pairing is $9-6=3$.
These also distinguish homogeneous CP/TNI calculations from an
incorrect trace-one or TP restriction on each live branch.

Finally, standard qutrit teleportation uses a maximally entangled qutrit
pair, a nine-outcome Bell measurement at the encoder and a controlled
unitary on the retained receiver share to realize the identity channel.
For each Bell outcome $(a,b)\in\{0,1,2\}^2$, the unnormalized receiver
state is $W_{ab}\rho W_{ab}^\dagger/9$ for the corresponding qutrit
Weyl unitary. The correction $W_{ab}^\dagger$ gives $\rho/9$, and
the nine outcomes sum to $\rho$, also at reference amplification.
Counting only the classical Bell outcome would assign scalar fibres to
a Schmidt-number-three channel. That assignment fails Definition 21.2:
the retained receiver qutrit is an accessible quantum payload, and is
not an independent blank. Counting it jointly removes the contradiction.
This is a counterexample to the omitted-share premise, not a permitted
extra resource for the original experiment. $\square$

**Convention 25.3 (mathematical correspondence and remaining supply).**
The new source-specific consequences are the positive witness (CG.185),
its all-optimizer use, the strict complete-output class gap (CG.190),
and especially the unconditional bound (CG.194) on each original input
of an actual joint acquisition factorization. They are `repo-derived`
ordinary deductions conditional on the credited C137/C138 premises.
The Schmidt-number overlap inequality, Choi/Kraus equivalence and
classical-assisted compression mechanism used inside their proofs are
`literature-attested` by the three primary sources cited in Theorem 22.1;
they are not new results. The finite Choi and actual flagged-port
foundations are also present in `FiniteKrausRepresentation`, including
its private/public proof dependencies, and
`CoherentFlagPort.FlagPort`, `flagged_cptp_roundtrip` and
`port_component_lower_bound`. The latter exact probe-preservation
hypothesis is not the present approximate complete-output objective;
Theorems 22.1 and 24.1 supply that missing task-specific relation.
No new kernel-verified application is presumed from these references.

Definition 21.2 constrains what an ACTUAL acquisition/execution
implementation must retain. Proposition 25.1 is an abstract sufficient
factorization of one channel, not a conclusion that its encoder
instrument, classical flags, coherent storage, decoding isometries or
permissions are supplied by the original source. Even keeping the whole
qutrit by the calibrated isometry $E$ requires actual access and retention.
The prescribed diagonal no-failure kernels in Quantum Carrier Minimum
do not install (CG.201). `OriginalControl` remains a path predicate,
and probability-changing noncommuting fields in Probability/Phase
Transport prevent identifying Definition 18.2 with an exhaustive native
operation menu. Existing classical replay, preselected allocation and
profinite separation similarly supply no such quantum acquisition map.

The exact failure-time law in Proposition 25.1 is a mathematical output
measure. A physical implementation additionally needs the absorbing
event to occur at that elapsed time, no later positive-carrier action
after failure, terminal live output at time $1$, and all matching old
archives, clocks and controller updates. An internal acquisition record
destining a later failure, or a timestamp sampled from $h_0$, does not
by itself satisfy this physical timing condition. The native acquisition,
actuation and first-failure timing services remain to be supplied or
derived under the original permissions. No global native impossibility,
exhaustive Schur menu, optimizer whole-channel uniqueness, numerical
restricted error gap, sharp branch-mass bound or native realization
is asserted.

## 追加锚（本行以下为增补区）

## 26. Quantitative stability of the original sign-averaged live map

**Convention 26.1 (source and evidence scope).** Retain the entire
experiment of Definition 3.1, (CG.20) and Convention 21.1. In particular,
the inputs are the twelve actual normalized reached-cut specimens
$U_{e,n}\rho_yU_{e,n}^\dagger$, with $y=5,16,27$ and all four
$U_{e,n}=\operatorname{diag}(e,n,1)$. There is one history-independent
common channel, with the original five-mode completion and fixed common
metadata, acting on the entire complex algebra. The ideal failure output
is still the five separate measures $w_\ell f_y(t)dt\,P_f$ with
$w=(0,1/4,1/2,1/4,0)$, $f_y(t)=6y/(y+6t)^2$ and exact $t\in[0,1]$.
The error $E$ is HALF the full cq trace norm, maximized over the twelve
histories, including singular measures, wrong support, aborts and every
additional zero-ideal sector. It is not acceptance-normalized.

The starred data, $E_*$ and $J_*$ are precisely the credited ordinary
computer-assisted data of §§13–17, and $W_3,\delta_*$ are (CG.184).
The results below are ordinary mathematical deductions from those data.
They neither replace their certificate nor claim a new Lean verification.
The finite test (CG.155) and sign average are analytic lower-test devices;
neither is a supplied native operation or a preparation prior.

**Definition 26.2 (finite positive source constants).** Let $S(x)$ be the
full nine-dimensional slack (CG.129), formed from (CG.112)–(CG.113) in
a neighbourhood of $x_*$. Use the coordinate order
$x=(\lambda,\alpha_1,\alpha_2,\beta_1,\beta_2,z)$ of Definition 13.1.
All unmarked data in the following definitions are evaluated at $x_*$.
Let $P$ be the orthogonal projection onto $\ker S_*$, and put

$$
\begin{aligned}
s&=\min\{\nu:\nu\text{ is a positive eigenvalue of }S_*\},\\
c_f&=\zeta_{0,*}-\lambda_*p_{50},
&z_{\min}&=\min_i\zeta_{i,*},\\
\mathcal B_0&=(1000\operatorname{adj}S_{0,*})\oplus0\oplus0\oplus0,\\
\mathcal B_1&=0\oplus\operatorname{adj}S_{01,*}\oplus0\oplus0,\\
\mathcal B_2&=0\oplus0\oplus\operatorname{adj}S_{02,*}\oplus0,\\
M_j&=\left.\frac{\partial S(x)}{\partial x_j}\right|_{x_*}
\quad(1\leq j\leq6),
&L&=\left(\sum_{j=1}^6\|M_j\|_{\rm op}^2\right)^{1/2},\\
b&=\left(\sum_{k=0}^2\|\mathcal B_k\|_1^2\right)^{1/2},
&G&=[\nabla g_0\ \nabla g_1\ \nabla g_2]_{x_*},\\
\sigma&=\min_{\|u\|_2=1}\|Gu\|_2,
&a&=2\sqrt{3/s},\\
r_\lambda&=\lambda_*^{-1}+(1-\lambda_*)^{-1}
                        +p_{50}/c_f+z_{\min}^{-1},
&r_z&=c_f^{-1}+z_{\min}^{-1},\\
A&=\left(r_\lambda^2+r_z^2
       +\frac{16\lambda_*}{\|v_{5,*}\|_2^2}
       +\frac{16(1-\lambda_*)}{\|v_{27,*}\|_2^2}\right)^{1/2},\\
C&=a+\frac b\sigma(A+La).
\end{aligned}
\tag{CG.204}
$$

The direct sums use exactly (CG.128). Matrix trace norm is denoted by
$\|\cdot\|_1$, operator norm by $\|\cdot\|_{\rm op}$, and vector
Euclidean norm by $\|\cdot\|_2$. Thus $\sigma$ uses real vectors in
$\mathbb R^3$ and the Euclidean norm in $\mathbb R^6$. The constant
$C$ is distinct from the root-isolation box called $C$ in §13.
The positive certificate slack $c_f$ has no identification with a signed
weak-binding parameter or with an occupancy.

Here every denominator is positive and every constant is finite, with
$s,c_f,z_{\min},b,\sigma,a,A,C>0$ and $L\geq0$. Indeed Corollary 13.3
gives the ranks $2,1,1,2$ of the four slack blocks. Thus $S_*$ has rank
six, its kernel has dimension three, and its six positive eigenvalues
have a finite positive minimum. Equation (CG.115) gives $c_f>0$;
$\zeta_{1,*}=\lambda_*p_{51}>0$ and
$\zeta_{2,*}=\lambda_*p_{52}>0$, while
$\zeta_{0,*}>\lambda_*p_{50}>0$. The three $\mathcal B_k$ are
nonzero positive rank-one matrices, so their trace norms are their
positive finite traces. The chart denominators
$1+\alpha_1^2+\alpha_2^2$ and $1+\beta_1^2+\beta_2^2$ are positive;
hence all six Hermitian derivatives $M_j$ exist and have finite norms.

For injectivity, use precisely the credited block Jacobian (CG.164).
If $Gu=0$, then $D\Psi(u_*)(0,u)^T=0$, so $u=0$ by its credited
invertibility. The continuous function $u\mapsto\|Gu\|_2$ attains
its minimum on the compact unit sphere in $\mathbb R^3$. A zero minimum
would give a unit vector in the kernel. Therefore $\sigma>0$ and
$\|Gu\|_2\geq\sigma\|u\|_2$ for every $u$, including $u=0$.
This is the finite-dimensional injective-map norm principle represented
by pinned mathlib's `LinearMap.exists_antilipschitzWith`; the displayed
minimum fixes the particular modulus used here. The fixed coordinates
of $v_5,v_{27}$ are $-1,1$, respectively, so their norms are nonzero.
Finally $0<\lambda_*<1$ by (CG.115). These facts justify every operation
in (CG.204), without estimating a new numerical certificate.

**Theorem 26.3 (source-specific square-root stability).** For every
original common full-output processor $\Phi$ and every $0\leq\epsilon\leq1$,
let $J$ be the unnormalized output-input Choi matrix of its compressed
live map and let

$$
\overline J=\frac14\sum_{e,n}
(U_{e,n}\otimes U_{e,n})J(U_{e,n}\otimes U_{e,n})^\dagger.
\tag{CG.205}
$$

With the single constant $C$ of (CG.204),

$$
E(\Phi)\leq E_*+\epsilon
\quad\Longrightarrow\quad
\|\overline J-J_*\|_1\leq C\sqrt\epsilon.
\tag{CG.206}
$$

The same implication holds for every finite-test channel (CG.155),
with $E_c$ in the premise. No equality of the unaveraged live matrices
or of the complete failure laws is asserted.

Proof. Reduce a full-output candidate by $\mathcal C$ of Convention
17.1, and then mathematically average the finite channel over the four
actual signs, keeping both scalar flags fixed. Both operations contract
the maximum error, because the signs permute the original four histories
at each height. Write this averaged candidate as
$(\overline\Lambda,\overline G_f,\overline G_o)$. Its live Choi matrix
is (CG.205), its two effects are diagonal, and its errors at a fixed
height are independent of the sign. Let $e_y$ be those finite errors,
put $w_5=\lambda_*$, $w_{27}=1-\lambda_*$, and define

$$
\begin{aligned}
\Delta_y&=B_y-\overline\Lambda(\rho_y),
&\ell_y&=\operatorname{tr}(R_{y,*}\Delta_y)\quad(y=5,27),\\
q_5&=\operatorname{tr}(\overline G_f\rho_5),
&P_5&=\ell_5+6/11-q_5,
&P_{27}&=\ell_{27},\\
D&=\operatorname{tr}(S_*\overline J)
  +c_f(\overline G_f)_{00}
  +\operatorname{tr}(Z_{d,*}\overline G_o).
\end{aligned}
\tag{CG.207}
$$

The full certificate identity (CG.133) and its endpoint effects give

$$
w_5P_5+w_{27}P_{27}=E_*+D,\qquad
P_y\leq e_y\leq E_*+\epsilon,\qquad D\geq0.
\tag{CG.208}
$$

Consequently $D\leq\epsilon$ and
$\sum_{y=5,27}w_y(e_y-P_y)\leq\epsilon$. Solving (CG.208) for
each payoff using the upper bound on the other one yields

$$
0\leq e_y-P_y\leq\epsilon/w_y,
\qquad |P_y-E_*|\leq\epsilon/w_y.
\tag{CG.209}
$$

All quantities in $D$ are nonnegative. In particular, since
$Z_{d,*}\succeq z_{\min}I$,

$$
\operatorname{tr}(S_*\overline J)\leq\epsilon,\qquad
(\overline G_f)_{00}\leq\epsilon/c_f,\qquad
\operatorname{tr}\overline G_o\leq\epsilon/z_{\min}.
\tag{CG.210}
$$

First control the distance to the complementary face. Put
$\widehat J=P\overline JP$. Positivity and the TNI live budget give
$t:=\operatorname{tr}\overline J\leq3$. Spectral decomposition of
$S_*$ gives $S_*\succeq s(I-P)$, hence
$\operatorname{tr}((I-P)\overline J)\leq\epsilon/s$.
Apply the existing positive compression inequality
`TraceClassCompression.norm_sub_compress_le` in
`D5/S3/Quantum/Analysis/TraceClass/FiniteCompression.lean` to
$\overline J/t$ on $\mathbb C^9$, using an orthonormal basis adapted
to $\operatorname{range}P$. Its tail mass is
$\operatorname{tr}((I-P)\overline J)/t$. Rescaling gives

$$
\|\overline J-\widehat J\|_1
\leq2\sqrt{t\operatorname{tr}((I-P)\overline J)}
\leq a\sqrt\epsilon.
\tag{CG.211}
$$

If $t=0$, positivity gives $\overline J=\widehat J=0$, and the
inequality holds directly without division. Thus this use does not
assume a normalized live map. The compression is an analytic matrix;
it is not asserted to be a feasible TNI processor or a physical cut.

The sign characters commute with $S_*$ and $P$. Accordingly
$\widehat J$ is block diagonal in (CG.128), and in each of the first
three blocks it is supported on the respective one-dimensional real
kernel. The fourth block is zero. A Hermitian positive operator on
one complex line is a nonnegative real multiple of its rank-one
projection, even when the original operator is complex. Therefore

$$
\widehat J=\sum_{k=0}^2\widehat\eta_k\mathcal B_k,
\qquad \widehat\eta_k\geq0,
\qquad J_*=\sum_{k=0}^2\eta_{k,*}\mathcal B_k.
\tag{CG.212}
$$

It remains to control these coefficients quantitatively. Define the
real linear map on Hermitian matrices
$\mathscr L(X)=(\operatorname{tr}(M_jX))_{j=1}^6$.
The trace-pairing bound gives

$$
\|\mathscr L(X)\|_2\leq L\|X\|_1.
\tag{CG.213}
$$

This is the direct finite-dimensional instance of
`TraceClass.norm_tracePairingLinearMap_apply_le` in
`D5/S3/Quantum/Analysis/TraceClass/Pairing.lean`, followed by Euclidean
Cauchy–Schwarz. The determinant differential, including the factor
$1000$ in $g_0$, gives
$\mathscr L(\mathcal B_k)=\nabla g_k(x_*)$. Thus (CG.212) implies
$\mathscr L(\widehat J)=G\widehat\eta$.

For the uncompressed averaged candidate, the exact first-differential
identity is

$$
\begin{aligned}
\mathscr R&:=\nabla F(x_*)+\mathscr L(\overline J),\\
\mathscr R\cdot dx
 &=\sum_{y=5,27}\operatorname{tr}(dA_y\,\Delta_y)
   +\sum_i(r_i-1)d\zeta_i+\frac6{11}d\lambda,\\
r_i&=(\operatorname{Tr}_{\rm out}\overline J)_{ii}
     =1-(\overline G_f)_{ii}-(\overline G_o)_{ii}.
\end{aligned}
\tag{CG.214}
$$

Indeed differentiate $F$ and $S=I\otimes Z_d-W$ while holding
$\overline J$ fixed. In the $dW$ pairing, invariance of
$\overline J$ removes the sign average, and (CG.126) gives
$\operatorname{tr}(dA_y\overline\Lambda(\rho_y))$. This proves
(CG.214) for arbitrary complex block matrices, without assuming
stationarity or differentiating their coefficients.

The $z$ coordinate of (CG.214) is $r_0-1$, of absolute value at most
$r_z\epsilon$ by (CG.210). Its $\lambda$ coordinate is exactly

$$
\mathscr R_\lambda=P_5-P_{27}
 +p_{50}(\overline G_f)_{00}
 -p_{51}(\overline G_o)_{11}-p_{52}(\overline G_o)_{22}.
\tag{CG.215}
$$

Use (CG.209), (CG.210), and $0\leq p_{51},p_{52}\leq1$ to bound
its absolute value by $r_\lambda\epsilon$.

For the four projector coordinates, a small effect deficit controls
the off-eigenvector part. Here is the needed algebra, including
degenerate spectra. For either endpoint put
$u=v_{y,*}/\|v_{y,*}\|_2$, $R=uu^\dagger$, and
$\mu=u^\dagger\Delta_yu$. Positivity and trace at most one of
$B_y$ and $\overline\Lambda(\rho_y)$ imply
$-I\preceq\Delta_y\preceq I$. Let $m,M$ be its extreme eigenvalues.
Since $(MI-\Delta_y)(\Delta_y-mI)\succeq0$, its expectation gives

$$
\|(I-R)\Delta_yu\|_2^2
 =u^\dagger\Delta_y^2u-\mu^2
 \leq(M-\mu)(\mu-m)
 \leq2(M-\mu).
\tag{CG.216}
$$

Write $\Delta_+$ for the positive part. One always has
$M\leq\operatorname{tr}\Delta_+$, including when $M\leq0$.
The finite half norm is the total positive mass of the ideal-minus-
simulated direct-sum difference. For the height-$5$ effect its scalar
failure contribution is the entire signed failure difference, and for
height $27$ it is zero. In both cases the unused scalar contribution
to that positive mass is nonnegative. Therefore

$$
\operatorname{tr}(\Delta_y)_+-\mu\leq e_y-P_y
\leq\epsilon/w_y,
\qquad
\|(I-R)\Delta_yu\|_2\leq\sqrt{2\epsilon/w_y}.
\tag{CG.217}
$$

For a real chart coordinate $v_i$, $i=0,1$, the normalized vector has
derivative $(I-R)e_i/\|v\|_2$. Thus, holding $\Delta_y$ fixed,

$$
\left|\frac{\partial}{\partial v_i}
       \operatorname{tr}(R\Delta_y)\right|
\leq\frac{2}{\|v\|_2}\sqrt{2\epsilon/w_y}.
\tag{CG.218}
$$

The two coordinates at each endpoint in (CG.214) carry the factor
$w_y$, so each is bounded by
$2\sqrt{2w_y\epsilon}/\|v_{y,*}\|_2$.
Combining the six coordinate bounds and using $\epsilon^2\leq\epsilon$
on $[0,1]$ yields

$$
\|\mathscr R\|_2\leq A\sqrt\epsilon.
\tag{CG.219}
$$

Finally the credited stationarity is
$\nabla F(x_*)+G\eta_*=0$. Subtract it from
$\nabla F(x_*)+\mathscr L(\widehat J)$ and use (CG.211),
(CG.213), and (CG.219):

$$
\begin{aligned}
\sigma\|\widehat\eta-\eta_*\|_2
 &\leq\|G(\widehat\eta-\eta_*)\|_2
 \leq(A+La)\sqrt\epsilon,\\
\|\widehat J-J_*\|_1
 &\leq\sum_k|\widehat\eta_k-\eta_{k,*}|\|\mathcal B_k\|_1
 \leq\frac b\sigma(A+La)\sqrt\epsilon.
\end{aligned}
\tag{CG.220}
$$

The triangle inequality with (CG.211) proves (CG.206).
The proof uses only the finite test's necessary error bound and the
unchanged full-output lower certificate; it imposes no restriction on
the original simulated exact-time laws. At $\epsilon=0$ all estimates
are valid and recover the credited averaged rigidity. $\square$

## 27. Quantitative population and every-input quantum-resource consequences

**Corollary 27.1 (actual transfers and the homogeneous witness).** Under
the hypothesis of Theorem 26.3, define actual live transfers
$T_{ij}=\langle i|\Lambda(|j\rangle\langle j|)|i\rangle$ and their
credited values $\tau_{ij}=\langle ij|J_*|ij\rangle$ for all
$i,j\in\{0,1,2\}$. In particular, put

$$
\begin{aligned}
\tau_{01}&=(Q_*^{01})_{00},&\tau_{10}&=(Q_*^{01})_{11},\\
\tau_{02}&=(Q_*^{02})_{00},&\tau_{20}&=(Q_*^{02})_{11},\\
d(\epsilon)&=\max\{\delta_*-2C\sqrt\epsilon,0\}.
\end{aligned}
\tag{CG.221}
$$

All four $\tau_{ij}$ are finite and positive by (CG.165)–(CG.166), and

$$
\begin{aligned}
|T_{ij}-\tau_{ij}|&\leq C\sqrt\epsilon
 &&(i,j\in\{0,1,2\}),\\
\operatorname{tr}(W_3J)&\geq\delta_*-2C\sqrt\epsilon.
\end{aligned}
\tag{CG.222}
$$

Proof. Every sign conjugation fixes every Choi diagonal entry, so
$T_{ij}=\langle ij|\overline J|ij\rangle$. Pair the difference in
(CG.206) with the rank-one projector $|ij\rangle\langle ij|$ of
operator norm one. This bounds each actual transfer, without identifying
the unaveraged live map. Also $W_3$ is sign invariant, so its pairing
with $J$ equals its pairing with $\overline J$. Its eigenvalue on
$|\Omega\rangle/\sqrt3$ is $1$, and its other eight eigenvalues are
$-2$; thus $\|W_3\|_{\rm op}=2$. Apply the trace-pairing bound and
$\operatorname{tr}(W_3J_*)=\delta_*$. $\square$

**Theorem 27.2 (retained coherent mass for every complex input).** Suppose
the same near-optimal processor has an ACTUAL fully counted factorization
of Definition 21.2, or a countable or explicitly supplied integral
factorization with precisely Convention 21.3's hypotheses. Let
$p_H^{\rm acq},p_H^L$ be (CG.193), with high meaning
$d_\alpha\geq3$ for the JOINT future-accessible quantum payload. Then
for EVERY normalized complex qutrit density matrix $\rho$,

$$
p_H^{\rm acq}(\rho)\geq p_H^L(\rho)
\geq\frac{d(\epsilon)^2}{24}
=\frac{[\max\{\delta_*-2C\sqrt\epsilon,0\}]^2}{24}.
\tag{CG.223}
$$

In particular this holds for every original specimen separately. It is
strictly positive whenever $\epsilon<\delta_*^2/(4C^2)$.
The bound counts all retained entanglement shares and all other quantum
systems available to execution, as required by Definition 21.2.

Proof. Use the actual split $\Lambda=\Lambda_L+\Lambda_H$ of
Theorem 24.1. The supplied factorization makes $J_L\in\mathfrak S_2$
by (CG.191), including the specified countable and integral models.
Hence (CG.186) and (CG.222) imply

$$
\delta_*-2C\sqrt\epsilon\leq\operatorname{tr}(W_3J_H).
\tag{CG.224}
$$

The every-input homogeneous estimate already proved in
(CG.196)–(CG.199) applies to this same aggregate CP/TNI high submap:
for every unit complex vector $\psi$,
$\operatorname{tr}(W_3J_H)\leq2\sqrt{6p_H^L(|\psi\rangle\langle\psi|)}$.
It does not require the full channel to be exactly optimal. When
$d(\epsilon)>0$, combine with (CG.224) and square nonnegative
quantities; when $d(\epsilon)=0$, positivity of the branch probability
gives the claimed zero lower bound directly. Spectral decomposition and
linearity give the same bound for every mixed $\rho$. Finally each live
decoder is TNI, so its trace is at most its encoder trace; summation or
integration gives $p_H^L\leq p_H^{\rm acq}$.

The aggregate high map has a finite Kraus representation because its
input and compressed live output are both $M_3$, regardless of its
actual classical alphabet. This representation is used only in the
already established homogeneous estimate. It does not replace the
actual acquisition record by a Choi decomposition. If the high set has
zero measure, its aggregate map is zero; then (CG.224) forbids positive
$d(\epsilon)$, consistently with (CG.223). A finite-test closure limit
without an actual factorization has no branch-probability interpretation.
$\square$

**Corollary 27.3 (explicit positive error penalties).** Put
$\eta=E(\Phi)-E_*$. For an original common processor one has
$0\leq\eta\leq1$, since both outputs in the original metric are
normalized, so Theorem 26.3 applies with $\epsilon=\eta$. Then

$$
\begin{aligned}
J\in\mathfrak S_2
&\quad\Longrightarrow\quad
E(\Phi)\geq E_*+\frac{\delta_*^2}{4C^2},\\
T_{ij}=0
&\quad\Longrightarrow\quad
E(\Phi)\geq E_*+\frac{\tau_{ij}^2}{C^2}
\quad(ij\in\{01,10,02,20\}),\\
E(\Phi)-E_*
&\geq\frac{[\max\{\delta_*-\sqrt{24p_H^L(\rho)},0\}]^2}{4C^2}
\quad\text{for each normalized }\rho
\text{ in an actual factorization}.
\end{aligned}
\tag{CG.225}
$$

The last line remains valid with $p_H^{\rm acq}(\rho)$ in place of
$p_H^L(\rho)$. These are positive symbolic source-dependent penalties,
not numerical evaluations or sharp gaps. In particular the first line
quantifies the earlier existential qubit-acquisition separation, and
the second constrains each of the four individual transfers.

Proof. For $J\in\mathfrak S_2$ the witness pairing is nonpositive;
combine with (CG.222). For a vanishing transfer use its first bound in
(CG.222). For the last line combine (CG.224) at $\epsilon=\eta$ with
the homogeneous bound used in Theorem 27.2, and rearrange before
squaring. Replacing the live probability by its larger acquisition
probability can only decrease the right side. All four transfer
penalties and the first witness penalty are finite and strictly positive
by Definition 26.2 and the credited margins. The same first-line
obstruction holds for closure of the finite-test low-dimensional class:
$\mathfrak S_2$ is closed and the witness pairing is continuous.
It supplies no actual flags to a limit. $\square$

## 28. Source correspondence, literature and remaining native supply

**Convention 28.1 (reused content and the new relation).** The quantitative
link (CG.206), the resource bound (CG.223) and penalties (CG.225) are
`repo-derived` ordinary results. They reuse the exact point, ranks,
strict margins and nonsingular Jacobian of §§13–16, the equality
identification in §17, and the homogeneous witness and every-input
estimate in §§22–24. Those results are not reclassified as new content.
The added step is a controlled distance from near-optimal original
performance to the complementary live face and then to its unique
credited coefficients. No unchanged minimax solve, root isolation or
certificate recertification enters this deduction.

The existing `TraceClassCompression.norm_sub_compress_le` supplies (CG.211)
after trace rescaling and an adapted finite Hilbert basis. Its actual
private helpers `compress_norm_le`, `sqrt_column` and
`finiteSpan_projection_basis` address positive compression and its basis
calculation; they are not assumed absent because of visibility.
`TraceClass.norm_tracePairingLinearMap_apply_le` supplies the
operator/trace-norm pairing. `FiniteKrausRepresentation` supplies the
general finite Choi/Kraus mechanism, while `CoherentFlagPort` and its
private normalization and scalar-component helpers concern actual
flagged ports with exact probe-preservation hypotheses. Those latter
hypotheses do not assert the near-optimal objective here. The pinned
mathlib finite-dimensional injective-map norm principle is sufficient
for the positive modulus in Definition 26.2; it does not assert
source-specific error stability. No new generic interface or duplicate
Lean declaration is needed for these ordinary applications.

**Convention 28.2 (primary literature and applicable scope).**
Ding–Udell, [*A Strict Complementarity Approach to Error Bound and
Sensitivity of Solution of Conic Programs*, arXiv:2012.00183v2](https://arxiv.org/pdf/2012.00183v2),
Theorem 1, Corollary 1 and §3.3, give complementary-face error bounds.
Their hypotheses include their strong-duality and dual-strict-
complementarity conditions; their SDP projection estimates concern
finite real symmetric matrices with the indicated norm conventions.
These are mature antecedents of the projection-plus-face strategy.
Their conic error bound is not invoked as a theorem about the present
full cq objective. In particular, the single fixed lower payoff does
not itself isolate $J_*$ on its entire complementary face: the
quantitative endpoint effect deficits and injective matrix $G$ are
needed in (CG.214)–(CG.220).

Nishijima–Li–Lourenço, [*Radial-type error bounds for semidefinite
feasibility problems without strict feasibility: qualitative estimates
and asymptotic tightness*, arXiv:2608.09013v2](https://arxiv.org/pdf/2608.09013v2),
Theorems 3.17 and 3.19, provide explicit moduli involving facial-reduction
data and potentially exponents $1/2^j$. Their Theorem 5.2 provides
linear-plus-square-root optimality-system bounds under Assumption 5.1's
strict-complementarity premises. None automatically proves a
square-root modulus for an unencoded complete-output benchmark.
Definition 26.2 instead fixes all constants directly from the credited
source, and (CG.208)–(CG.220) justify the required exponent without
assuming a new SDP representation, Slater point or exact-time feasible
law. The full complex matrix scope follows from the Hermitian
compression, trace pairing and spectral argument used here.

The Schmidt-number and Choi/Kraus literature cited in Theorem 22.1
continues to supply exactly its homogeneous overlap and factorization
facts. The compatible-ecosystem search includes physlib's trace norm
and trace distance, QICLean's trace pairing, positive compression and
semidefinite duality, and lean-quantum's trace inequalities. Their
examined upstream toolchain/mathlib pairs differ from this repository's
pin; no new dependency or transplant is used. No source-specific
near-optimal theorem was identified in those examined sources. This
search scope does not establish literature absence or worldwide novelty.

**Convention 28.3 (native bridge and quantitative boundary).** The
constants and inequalities constrain the actual common processor and,
when supplied, its actual joint acquisition/execution factorization.
They grant no acquisition channel, coherent memory, classical flag,
controlled decoder, actuator or first-failure clock. The remaining
native bridge must supply lawful access to the sole unknown specimen,
the fully counted retained quantum payload and any actually acquired
record, and controlled execution with the original permissions and
clock. It must reproduce the full five-label elapsed-time law with
failure absorbing at that event time, no later positive-carrier action
after failure, terminal live output at time one, and the matching old
archives, aligned clocks and controller updates. A sampled timestamp,
effect equality or abstract Stinespring realization does not supply
those operations or that first-failure event.

`OriginalControlComposition.OriginalControl` specifies a geometric path
predicate. The probability-changing and noncommuting fields
$P=\partial_\kappa$ and
$Q=\sum_a w_a(\kappa)\partial_{h_a}$ of Probability/Phase Transport,
Definition 10.1, do not justify replacing the native menu by the
conditional Schur closure of Definition 18.2. The classical structural
storage atlas and the known-parameter endpoint timing model supply no
unknown quantum specimen acquisition. No signed weak-binding parameter
is substituted for a nonnegative retained probability here.

The mathematical average and complementary-face compression are not
implementations, and (CG.206) asserts neither whole-channel uniqueness
nor stability of each failure-time law. It gives no physical native
realization, quantum capacity formula or sharp resource threshold.
When $d(\epsilon)=0$, (CG.223) asserts only nonnegativity; for smaller
error it gives a uniform positive resource requirement on every complex
input in every actual fully counted factorization. The finite result
advances the continuing quantum programme without completing its
native acquisition and control objectives.

## 追加锚（本行以下为增补区）

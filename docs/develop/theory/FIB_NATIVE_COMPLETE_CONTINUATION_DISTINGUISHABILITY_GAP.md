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

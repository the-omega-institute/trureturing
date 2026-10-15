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

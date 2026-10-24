# Shared affine gain and zero-crossing recovery

This companion works in the common-source model of Definition 38.1. It gives a fixed forward path that recovers the effective relation, the relative affine-gain slope, and the complete bounded-degree additive drift for every real gain slope, including every gain-zero case. The only remaining ambiguity is the positive relation/gain scale.

## 1. Model and target

Let

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

Matrix products act on the left, so a displayed product is executed from right to left. The initial relation is

$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},\qquad p,q,r,s>0,\qquad ps=qr.
$$

There are fixed numbers $\alpha>0$ and $\beta\in\mathbb R$, and an unknown real polynomial $D$ of degree at most a known integer $d\ge0$. At recorded scalar-reading index $i$ the exact reading is

$$
z_i=(1+\kappa i)\operatorname{tr}(A_iS)+D(i),
\qquad \kappa=\frac\beta\alpha.
$$

Here $S=\alpha R$ for the original positive rank-one relation $R$. Every read, including an empty-word repeat at the unchanged initial state, advances $i$ by one; an unread atomic operation does not. There is one forward history, one fixed row instrument during a run, and no reset, copy, inverse operation, second source, or combination of unexecuted histories. The recovery target is $(S,\kappa,D)$, with the positive scale fibre described below.

Put

$$
B=\max(d+1,2).
$$

## 2. A $\max(d+6,7)$-read path

### Theorem 2.1 (uniform recovery with nine atomic operations)

For every $d\ge0$, a predetermined finite-composite-word path recovers $(S,\kappa,D)$ from $B+5=\max(d+6,7)$ exact reads. It uses nine atomic $M/J$ operations and is valid for every real $\kappa$, including all zero crossings of $1+\kappa i$.

The cumulative matrices at the recorded positions are

$$
A_i=I\quad(0\le i<B),
$$

followed by

$$
A_B=U,\quad A_{B+1}=U^2,
$$

$$
A_{B+2}=F=M^2U^2=\begin{pmatrix}1&3\\1&4\end{pmatrix},\quad
A_{B+3}=G=JM^2U^2=\begin{pmatrix}1&4\\1&3\end{pmatrix},
$$

and

$$
A_{B+4}=H=UJM^2U^2=\begin{pmatrix}2&7\\1&3\end{pmatrix}.
$$

The operation blocks after the last initial read, written as left-multiplying matrix products, are respectively $JM$, $JM$, $MM$, $J$, and $JM$, so their lengths are $2,2,2,1,2$.

#### Proof

Write $a=p+s=\operatorname{tr}(S)$ and define

$$
P(t)=D(t)+a(1+\kappa t).
$$

Its degree is at most $\max(d,1)=B-1$. At each of the first $B$ positions the cumulative matrix is $I$, hence

$$
z_i=P(i)\qquad(0\le i<B).
$$

The $B$ distinct values determine $P$ uniquely. Explicitly,

$$
P(t)=\sum_{j=0}^{B-1}z_j
\prod_{\substack{0\le h<B\\h\ne j}}
\frac{t-h}{j-h},
$$

whose denominators are fixed nonzero integers.

Direct multiplication gives

$$
\operatorname{tr}(US)=a+r,\qquad
\operatorname{tr}(U^2S)=a+2r.
$$

Define

$$
v_0=z_B-P(B),\qquad
v_1=\frac{z_{B+1}-P(B+1)}2.
$$

Then

$$
v_0=r(1+\kappa B),\qquad
v_1=r(1+\kappa(B+1)).
$$

Consequently, with

$$
\eta=v_1-v_0,\qquad r_* =v_0-B\eta,
$$

we have $\eta=\kappa r$, $r_*=r>0$, and

$$
\kappa_* =\frac\eta{r_*}=\kappa.
$$

No division by a gain is used, so either shear reading may itself have zero gain.

For the last three positions, write $g_i=1+\kappa i$. The affine function $g_i$ is not identically zero and has at most one zero. Whenever $g_i\ne0$, set

$$
V_i=\frac{z_i-P(i)}{g_i}=\operatorname{tr}(A_iS)-a.
$$

A zero gain simply makes that position unavailable for this division.

Expanding the three final matrices gives

$$
V_{B+2}=q+3r+3s,\qquad
V_{B+3}=q+4r+2s,\qquad
V_{B+4}=p+q+7r+2s.
$$

Thus define, at every available position,

$$
X=V_{B+2}-3r=q+3s,\qquad
Y=V_{B+3}-4r=q+2s,\qquad
Z=V_{B+4}-7r=p+q+2s.
$$

At least two of $X,Y,Z$ are available. Each available one is positive on the declared source domain.

If $X,Y$ are available, then

$$
s=X-Y,\qquad q=Y-2s,\qquad p=\frac{qr}{s}.
$$

The denominator is $s>0$.

If $Y,Z$ are available, then

$$
p=Z-Y,\qquad s=\frac{rY}{p+2r},\qquad q=\frac{ps}{r}.
$$

Here $p>0$ and $p+2r>0$ on the source domain. Indeed, $Z-Y=p$ and $Y=q+2s=s(p/r+2)$.

If $X,Z$ are available, put $h=Z-X$ and $b=h+3r$. Since $h=p-s$ and $X=(p/r+3)s$, the entry $s$ satisfies

$$
s^2+bs-rX=0.
$$

The product of the two roots is $-rX<0$, so exactly one root is positive. It is

$$
s=\frac{2rX}{\sqrt{b^2+4rX}+b},
$$

because the denominator is positive: $\sqrt{b^2+4rX}>|b|$. Then $p=s+h$ and $q=ps/r$. Thus this pair also has a unique positive inverse, including $b=0$ and either sign of $h$.

Use any available pair, with the first pair preferred when all three are available. The pair calculations recover the same true $S$; an extra available value is redundant. Finally set

$$
D(t)=P(t)-a(1+\kappa t),\qquad a=p+s.
$$

This is the original polynomial for every real $t$. When $d=0$, $P$ was allowed to be affine, but its linear coefficient is exactly $a\kappa$, so the subtraction leaves a constant. Hence the declared degree bound is preserved.

For injectivity, suppose two actual common-source realizations give the same $B+5$ readings. The initial block gives the same $P$. The two shear equations give the same positive $r$ and the same $\kappa$, hence the same gain-zero positions. At least one of the three final pairs is common and available, and its positive inverse gives the same $S$. The displayed formula then gives the same entire $D$. Therefore the target is recovered globally.

All matrices above are reached on one legal forward history: $U$ is obtained by $M$ then $J$, $U^2$ by another $M$ then $J$, $F$ by two $M$ operations, $G$ by $J$, and $H$ by $U$. The instrument row is never acted on. If $S=c\ell$ with $c,\ell$ strictly positive, then $M$ and $J$ send positive columns to positive columns, so every recorded state has the same one-source, fixed-instrument realization. ∎

### Corollary 2.2 (exact positive scale fibre)

For the data in Theorem 2.1, all strictly positive rank-one realizations are exactly

$$
R=\frac{S}{t},\qquad \alpha=t>0,\qquad \beta=\kappa t,\qquad D\text{ fixed}.
$$

Equivalently, two realizations have the same data exactly when some $\lambda>0$ satisfies

$$
R'=\lambda^{-1}R,\qquad
\alpha'=\lambda\alpha,\qquad
\beta'=\lambda\beta,\qquad D'=D.
$$

#### Proof

The recovered effective relation is $S=\alpha R$. If another realization has the same data, Theorem 2.1 gives $\alpha'R'=S$ and $\beta'/\alpha'=\kappa=\beta/\alpha$. Taking $t=\alpha'$ gives the displayed parameterization. Conversely, substitution preserves every reading and preserves positivity and rank one. ∎

## 3. Finite-data compatibility

### Proposition 3.1 (exact common-model existence test)

For arbitrary proposed real data $z_0,\ldots,z_{B+4}$ on the path of Theorem 2.1, the following finite procedure is necessary and sufficient for membership in the declared common-source model.

1. Interpolate $P$ from $z_0,\ldots,z_{B-1}$ and form $v_0,v_1,\eta,r_*$ as in the proof. Require $r_*>0$ and set $\kappa=\eta/r_*$.
2. Mark the exact zeros of $1+\kappa i$ among the last three indices and choose an available pair among $X,Y,Z$. Require its inverse to be defined and to produce $p,q,r_*,s>0$ with $ps=qr_*$. For the $X,Z$ pair, require $X>0$ before taking the positive root.
3. Form $a=p+s$ and $D(t)=P(t)-a(1+\kappa t)$. Require $\deg D\le d$ and require every one of the $B+5$ exact observation equations

$$
z_i=(1+\kappa i)\operatorname{tr}(A_iS)+D(i)
$$

on the displayed path, including every zero-gain position.

These conditions are necessary and sufficient.

#### Proof

Necessity is every identity in Theorem 2.1, including positivity, the rank-one equation, the denominator conditions, and the full read check. Conversely, suppose the listed conditions hold. Set $\alpha=1$, $\beta=\kappa$, $R=S$, choose

$$
c=\begin{pmatrix}p\\r_*\end{pmatrix},\qquad
\ell=\left(1,\frac q p\right).
$$

Both vectors are strictly positive and

$$
c\ell=\begin{pmatrix}p&q\\r_*&r_*q/p\end{pmatrix}=S
$$

because $ps=qr_*$. Executing the stated forward path with this one fixed instrument and the checked polynomial $D$ gives every proposed equation. This is a genuine common-source realization, not an independent lifted pair. ∎

## 4. Sharpness inside the calibration-prefix class

### Theorem 4.1 (three continuation reads are necessary for this prefix)

Fix the prefix consisting of $B$ reads at $I$, then reads at $U$ and $U^2$. Among predetermined continuations, no protocol with at most two further reads recovers the full target uniformly. Thus the $B+5$ bound is sharp within this explicit prefix class. This does not assert global sharpness over other fixed paths.

#### Proof

It is enough to consider two further reads, since a shorter continuation can be padded by empty words. Let $j=B+2$ be the first additional index, and let $T=\begin{pmatrix}A&Beta\\C&E\end{pmatrix}$ be the cumulative matrix at the last additional read. It has nonnegative integer entries and determinant $1$ or $-1$.

For a fixed $x>0$ consider

$$
S(s)=\begin{pmatrix}x-s&s(x-s)\\1&s\end{pmatrix},\qquad 0<s<x.
$$

Every such matrix is strictly positive, rank one, and has the actual factorization $c=(x-s,1)^{\mathsf T}$, $\ell=(1,s)$. Moreover

$$
\operatorname{tr}(S(s))=x,\qquad
\operatorname{tr}(US(s))=x+1,\qquad
\operatorname{tr}(U^2S(s))=x+2.
$$

Thus the entire prefix has identical unweighted signals on this fibre.

The last unweighted signal is

$$
\operatorname{tr}(TS(s))=Ax+Beta+(E-A)s+Cs(x-s).
$$

If $C=0$, unimodularity and nonnegative integer diagonal entries force $AE=1$, hence $A=E=1$, so this signal is independent of $s$. Take $x=2$ and $s=2/3,4/3$.

If $C>0$, choose

$$
x=1+\frac{|E-A|}{C},\qquad
s_* =\frac{x+(E-A)/C}{2}.
$$

Then $0<s_*<x$. Two distinct points symmetric about $s_*$ give the same quadratic value; for example choose $\varepsilon=\frac12\min(s_*,x-s_*)$ and use $s_*-\varepsilon,s_*+\varepsilon$.

Use the same actual gain parameters for the two sources,

$$
\alpha=1,\qquad \beta=\kappa=-1/j,\qquad D=0.
$$

The first additional read has gain $1+\kappa j=0$, so its observed value is zero for both sources. At the final index $j+1$, the gain is the common nonzero value $-1/j$, while the two final unweighted signals were chosen equal. All observations and operation histories therefore coincide although the effective sources differ. Both runs use one fixed positive instrument. The three-read continuation in Theorem 2.1 succeeds everywhere, so the prefix-specific optimum is exactly three continuation reads. ∎

## 5. An unrestricted fixed-path lower bound

### Theorem 5.1 (every fixed path needs at least $d+5$ reads)

For every $d\ge0$, no predetermined fixed cumulative $M/J$ path with fewer than $d+5$ exact scalar reads uniformly recovers $(S,\kappa,D)$ on the declared common-source model.

#### Proof

Let $n=d+5$ and use the actual parameter chart

$$
\mathcal V=(0,\infty)^3\times\mathbb R^{d+2}
$$

with coordinates $(p,q,r,\kappa,\delta_0,\ldots,\delta_d)$,

$$
S=\begin{pmatrix}p&q\\r&qr/p\end{pmatrix},\qquad
D(t)=\sum_{h=0}^{d}\delta_h t^h.
$$

This is an injective chart of actual targets. Every chart point is physically realized by $\alpha=1$, $\beta=\kappa$, $R=S$, $c=(p,r)^{\mathsf T}$ and $\ell=(1,q/p)$.

For any fixed list of $m$ recorded cumulative matrices $A_i$, the observation map $F:\mathcal V\to\mathbb R^m$ has components

$$
F_i=(1+\kappa i)\left((A_i)_{00}p+(A_i)_{10}q+(A_i)_{01}r+(A_i)_{11}\frac{qr}{p}\right)
 +\sum_{h=0}^{d}\delta_h i^h.
$$

It is smooth on $\mathcal V$. Assume $m<n$, and let $\rho$ be the largest Jacobian rank attained on $\mathcal V$; then $\rho\le m<n$.

If $\rho=0$, the derivative vanishes on a small convex ball and integration along line segments makes $F$ constant there, giving distinct actual targets with the same observations.

Suppose $\rho>0$. Choose a point at which a $\rho\times\rho$ Jacobian minor is nonzero and a neighborhood on which it remains nonzero. By maximality, the rank is exactly $\rho$ throughout that neighborhood. Permute coordinates and output components so that this minor uses the first $\rho$ coordinates and first $\rho$ components. The implicit function theorem says that the level set of those first components through the chosen point is a smooth graph over an open ball in the remaining $n-\rho$ coordinates, which is nonempty because $n-\rho>0$.

On this graph, the differentials of all remaining components of $F$ are linear combinations of the differentials of the first $\rho$ components, since the total rank is $\rho$. They therefore vanish on every tangent vector to the graph. Integrating along paths in a sufficiently small connected parameter ball makes every remaining component constant on the graph as well. The first components are constant by construction, so $F$ is constant on a graph containing distinct points of $\mathcal V$. The corresponding targets are different but have the same $m$ readings, contradicting uniform recovery.

A fixed protocol that may stop earlier can be padded with empty words along its same predetermined sequence to its claimed uniform read limit. A collision for the padded observation map has identical history up to every stopping decision, so padding does not remove the collision. The argument is for fixed paths; it does not apply to adaptive word selection. ∎

## 6. Bounds, credits, and remaining sharp questions

Let $C_{\mathrm{fix}}(d)$ denote the smallest uniform exact-read bound over all predetermined finite-composite-word cumulative $M/J$ paths in this model. The results above give

$$
d+5\le C_{\mathrm{fix}}(d)\le \max(d+6,7).
$$

Thus, for $d\ge1$, the unrestricted optimum is confined to $d+5$ or $d+6$, while for $d=0$ it is confined to $5,6,7$. The original all-fixed-path sharp problem remains open: no $d+5$ construction is supplied, and no $d+5$ collision theorem is claimed. The prefix-specific theorem does not settle paths with a different calibration prefix.

The source results are credited as follows. Definitions 10.1–10.3 and 38.1 supply the positive rank-one source, trace convention, counted initial read, finite-composite-word contract, and effective target. Sections 1–5 supply the trace identity, Fibonacci closure, four-read relation inverse, and positive factorization scale. Sections 10–17 supply the unweighted fixed/adaptive read results and the nonnegative unimodular collision mechanism; those results are not re-labelled as the present gain/drift theorem. Sections 18–32 concern fixed unbiased shear fibres, action costs, stability, and word-frontier limitations, and are not used to claim a global frontier classification here. Sections 33–35 supply the affine-drift and arbitrary-degree drift interfaces and their recurrences. Section 36 supplies the positive rank-one known-unit-gain five-read result and its fixed-path lower-bound context. Section 37 supplies the lifted ten-read inverse and its warning that independent lifted matrices need not be one common source. Theorem 38.2 and Proposition 38.5 supply the credited $d+7$ restricted-gain and $d+8$ unrestricted single-switch results and their finite-data conditions; the present path and inverse are proved directly. Corollary 38.3 supplies the positive scale gauge, and Proposition 38.4 supplies the credited same-source $d=1$ zero-gain collision. None of these credits is used as an independent physical realization of the new path.

Definition 39.1 and Theorem 39.2 of the main source treat the broader common polynomial-gain model $z_i=G(i)\operatorname{tr}(A_iR)+D(i)$ for arbitrary nonzero real $G$ of known degree at most $k$ and additive drift of known degree at most $d$. In that section's notation, the normalized target is $(R_0,H,D)$, where $R_0=R/\operatorname{tr}R$ and $H=(\operatorname{tr}R)G$. Its predetermined single-switch path recovers this target in $3k+d+5$ reads, including initial gain zero, all other gain-zero positions, lower actual degrees, repeated roots, and a missing Fibonacci mode. Proposition 39.3 checks common-source compatibility at every recorded position, including each zero-gain residual, and Corollary 39.4 gives the complete positive-scale fibre; zero relation, zero trace, and identically zero gain remain outside that recovery domain. For the affine submodel here, $G(t)=\alpha+\beta t$ with $\alpha>0$, the targets correspond by $R_0=S/\operatorname{tr}S$, $H(t)=(\operatorname{tr}S)(1+\kappa t)$, and conversely $S=H(0)R_0$, $\kappa=H'(0)/H(0)$ with $H(0)>0$. Thus its $k=1$ sufficient bound is $d+8$, while Theorem 2.1 gives the smaller $\max(d+6,7)$ bound on the stated affine submodel. The polynomial-gain result also covers $G(0)=0$, which is outside the present $\alpha>0$ model. Section 39 does not determine the sharper affine optimum over all fixed paths.

The nine-operation count is a construction upper bound, not an optimal operation count, bit-complexity bound, noisy-stability statement, time bound, or acquisition-cost theorem. The proof uses exact real interpolation, divisions by proved-positive source entries, and exact comparisons. It makes no claim about adaptive protocols, general neural-network performance, external novelty, or the absence of other results. The mathematics here is an ordinary conditional argument for the stated model and is not a Lean or empirical certification.

## 追加锚（本行以下为增补区）
## 7. Adaptive continuation after the affine calibration prefix

Use the model and target contract of Sections 1–2. In particular, the source is one positive rank-one relation with one fixed positive row, the gain and drift are fixed throughout each run, the reads are exact real values on the original clock, and all cumulative matrices lie on one forward trajectory generated by total deterministic finite-composite $M/J$ words, with the empty word allowed. Thus

$$
z_i=(1+\kappa i)\operatorname{tr}(A_iS)+D(i),
\qquad
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},
\quad p,q,r,s>0,\quad ps=qr.
$$

A finite composite word is one continuation action; a read advances the clock index and an unread atom does not. A continuation protocol is causal: its next word, stopping decision, and answer depend only on the acquired history. No continuity, measurability, computability, or other regularity is assumed. The protocol has no reset, copy, inverse acquisition, second source, or second observation channel, and no world changes after an observed response.

Set

$$
B=\max\{d+1,2\}.
$$

The fixed calibration prefix reads $B$ times at $I$, then once at $U$, then once at $U^2$, at clock indices $0,\ldots,B+1$. Its continuation starts at

$$
j=B+2.
\tag{7.1}
$$

Let $q_{\mathrm{ad}}(d)$ be the least uniform number of further reads after this prefix for which a causal deterministic continuation recovers the complete target $(S,\kappa,D)$ for every legal world. The prefix produces

$$
P(t)=D(t)+a(1+\kappa t),
\qquad a=\operatorname{tr}(S)=p+s.
\tag{7.2}
$$

### Theorem 7.1 (exact adaptive continuation count)

Under this contract,

$$
\boxed{q_{\mathrm{ad}}(0)=2,\qquad q_{\mathrm{ad}}(d)=3\quad(d\ge1).}
\tag{7.3}
$$

For $d\ge1$, three reads suffice by Theorem 2.1 of this volume, whose last three readings follow the same prefix. Two reads cannot suffice even for a fully adaptive continuation. For $d=0$, two reads suffice and one read cannot suffice.

#### Proof for $d\ge1: the two-read lower bound

Assume a protocol uses at most two continuation reads. Write $j=B+2$ and

$$
g(t)=1-\frac{t}{j}.
$$

For $x>0$ and $0<u<x$, define

$$
S_x(u)=
\begin{pmatrix}
 x-u&u(x-u)\\
 1&u
\end{pmatrix},
\qquad
D_x(t)=-xg(t).
\tag{7.4}
$$

Then

$$
S_x(u)=(x-u,1)^{\mathsf T}(1,u),
$$

so $S_x(u)$ is strictly positive and rank one, and

$$
\operatorname{tr}(S_x(u))=x,
\qquad
\operatorname{tr}(US_x(u))=x+1,
\qquad
\operatorname{tr}(U^2S_x(u))=x+2.
\tag{7.5}
$$

Use the same affine gain $1+\kappa t=g(t)$ in every world. At each of the first $B$ identity reads, the signal and drift cancel:

$$
g(i)\operatorname{tr}(S_x(u))+D_x(i)=0.
$$

At the two shear reads, (7.5) gives

$$
z_B=g(B)=\frac2j,
\qquad
z_{B+1}=2g(B+1)=\frac2j.
\tag{7.6}
$$

Thus every $x,u$ gives the same complete prefix history, including the actions selected before continuation.

The first continuation action is therefore fixed by this common history. At index $j$, both gain and drift vanish, so $z_j=0$ for every cumulative matrix. If the protocol stops there, two distinct matrices in the family already give different targets with the same history.

Otherwise the second continuation action is also fixed by the same history. Let its final cumulative matrix be

$$
T=\begin{pmatrix}A&b\\C&E\end{pmatrix}.
$$

Every product of $M$ and $J$ has nonnegative integer entries and determinant $\pm1$. If $C=0$, then $AE=\det T=\pm1$ and nonnegativity force $A=E=1$. In that case

$$
\operatorname{tr}(TS_x(u))-x=b
\tag{7.7}
$$

is independent of $x,u$; choose two distinct values of $u$.

If $C>0$, set

$$
x=1+\frac{|E-A|}{C},
\qquad
u_* =\frac{x+(E-A)/C}{2}.
\tag{7.8}
$$

Both $u_*>0$ and $x-u_*>0$. Define

$$
\Phi_x(u)=\operatorname{tr}(TS_x(u))-x
=(A-1)x+b+(E-A)u+C\,u(x-u).
\tag{7.9}
$$

The two points $u_* -\varepsilon$ and $u_*+\varepsilon$, for any

$$
0<\varepsilon<\min(u_*,x-u_*),
$$

are distinct, lie in $(0,x)$, and have the same value of $\Phi_x$, by symmetry about its vertex. At index $j+1$, the common drift is $D_x(j+1)=x/j$ and the gain is $-1/j$, so

$$
z_{j+1}=-\frac{\Phi_x(u)}{j}.
\tag{7.10}
$$

The two worlds therefore have the same second continuation read as well, while their effective relations differ. They use the same fixed gain and the same fixed affine drift, with all parameters fixed before the run. Stopping earlier gives the same collision, and continuing to the second read gives (7.10); hence no adaptive two-read continuation is uniformly correct and

$$
q_{\mathrm{ad}}(d)\ge3\qquad(d\ge1).
\tag{7.11}
$$

#### Proof for $d=0: the one-read lower bound

Use the family

$$
S(p,u)=
\begin{pmatrix}p&pu\\1&u\end{pmatrix},
\qquad p,u>0,
\qquad \kappa=0,
\qquad D(t)=-(p+u).
\tag{7.12}
$$

It is strictly positive and rank one. Since the prefix has $B=2$, its common readings are

$$
(z_0,z_1,z_2,z_3)=(0,0,1,2),
\tag{7.13}
$$

because the two identity signals are $p+u$, while the $U$ and $U^2$ signals are $p+u+1$ and $p+u+2$.

With only one continuation read, its word is fixed by this common history. Let its cumulative matrix at index $4$ be

$$
T=WU^2=\begin{pmatrix}A&b\\C&E\end{pmatrix},
$$

where $W$ is the chosen finite $M/J$ word. The residual read is

$$
\Psi_T(p,u)
=\operatorname{tr}(TS(p,u))-(p+u)
=(A-1)p+b+(E-1)u+C\,pu.
\tag{7.14}
$$

If $C=0$, then $AE=\det T=\pm1$ and nonnegativity force $A=E=1$, so $\Psi_T=b$ is constant. If $C>0$, write

$$
W=\begin{pmatrix}a&b_0\\c&e_0\end{pmatrix},
\qquad
T=WU^2=\begin{pmatrix}a&2a+b_0\\c&2c+e_0\end{pmatrix}.
$$

Thus $E\ge2C$ and $E-1+Cp>0$ for every $p>0$. Fix any positive point $(p_0,u_0)$ and let $h=\Psi_T(p_0,u_0)$. Near $p_0$, the level set $\Psi_T(p,u)=h$ is the graph

$$
u(p)=\frac{h-b-(A-1)p}{E-1+Cp}.
\tag{7.15}
$$

It contains $(p_0,u_0)$ and stays positive for nearby distinct $p$. Thus two different legal targets have the same prefix and the same one-read continuation, so

$$
q_{\mathrm{ad}}(0)\ge2.
\tag{7.16}
$$

#### Proof for $d=0: a two-read adaptive continuation

For the fixed prefix, define

$$
P(t)=z_0+(z_1-z_0)t,
\qquad
v_0=z_2-P(2),
\qquad
v_1=\frac{z_3-P(3)}2.
\tag{7.17}
$$

The prefix matrices are $U$ and $U^2$, hence

$$
v_0=r(1+2\kappa),
\qquad
v_1=r(1+3\kappa),
$$

and therefore

$$
r=3v_0-2v_1>0,
\qquad
\kappa=\frac{v_1-v_0}{r}.
\tag{7.18}
$$

No sampled gain is divided out.

If $\kappa=0$, use the two continuation cumulative matrices

$$
F=M^2U^2=\begin{pmatrix}1&3\\1&4\end{pmatrix},
\qquad
G=JF=\begin{pmatrix}1&4\\1&3\end{pmatrix}.
\tag{7.19}
$$

At continuation indices $4$ and $5$, the gain is one. The residuals

$$
X=\bigl(z_4-P(4)\bigr)-3r=q+3s,
\qquad
Y=\bigl(z_5-P(5)\bigr)-4r=q+2s
\tag{7.20}
$$

give

$$
s=X-Y,
\qquad q=Y-2s,
\qquad p=\frac{qr}{s},
\qquad a=p+s.
\tag{7.21}
$$

The rank-one identity $ps=qr$ supplies the displayed $p$, and finally $D=P-a$ is constant.

If $\kappa\ne0$, then

$$
a=\frac{z_1-z_0}{\kappa}>0,
\qquad D=z_0-a.
\tag{7.22}
$$

The remaining relation entry is $s\in(0,a)$, with

$$
p=a-s,
\qquad q=\frac{s(a-s)}r.
\tag{7.23}
$$

Choose an integer $n>2+a/r$, let $L=MJ$, and execute the finite word $U^nL$ after the prefix. Its cumulative matrix is

$$
T=U^nLU^2=\begin{pmatrix}n+1&3n+2\\1&3\end{pmatrix}.
\tag{7.24}
$$

As a function of $s$,

$$
f(s)=\operatorname{tr}(TS)
=(n+1)a+(3n+2)r+(2-n)s+\frac{s(a-s)}r,
\tag{7.25}
$$

and

$$
f'(s)=2-n+\frac{a-2s}{r}<0
\qquad(0<s<a).
\tag{7.26}
$$

If the gain at index $4$ is nonzero, the first continuation read gives $f(s)$ after subtracting $D$ and dividing by that known gain, so strict monotonicity recovers $s$ and then $S$.

If the gain at index $4$ is zero, execute $JJ$ after the first continuation read. The cumulative matrix is again $T$ at index $5$, while $1+5\kappa\ne0$ because a nonzero affine function cannot vanish at two distinct clock indices. The second read recovers $f(s)$ and hence $S$. Thus two continuation reads suffice for every constant-drift world:

$$
q_{\mathrm{ad}}(0)\le2.
\tag{7.27}
$$

On histories that do not satisfy the legal-world algebraic branches used above, assign any fixed finite word and answer. This arbitrary totalization makes the continuation protocol defined on every history and does not affect its guarantee on legal worlds.

For $d\ge1$, Theorem 2.1 of this volume gives $q_{\mathrm{ad}}(d)\le3$. Combining (7.11), (7.16), and (7.27) proves (7.3). ∎

## 8. Finite-history model validation obstruction

The recovery theorem is conditional on the declared drift degree. Let a deterministic causal protocol acquire only finitely many readings at clock indices in a finite set $I$, while the admissible drift class contains arbitrary real polynomials. Fix the same $S$ and affine gain in two worlds, and let $D$ be the drift in the first. For any future index $t_*\notin I$, choose

$$
Q(t)=c\prod_{i\in I}(t-i),
\qquad c\ne0,
\tag{8.1}
$$

and put $D'(t)=D(t)+Q(t)$. Then $Q(i)=0$ for every acquired index, while $Q(t_*)\ne0$.

### Proposition 8.1 (causal finite-history obstruction)

The two worlds $(S,\kappa,D)$ and $(S,\kappa,D')$ have the same finite transcript and every causal action up to the last acquired index, but they give different readings at $t_*$. Thus no finite transcript can certify an unrestricted arbitrary-degree drift model at an unacquired clock index.

#### Proof

Proceed inductively over the acquired reads. Before the first read the worlds have the same initial state. If their histories agree through a read, causality selects the same next finite-composite word and the same stopping decision in both worlds. The cumulative matrix and clock index are therefore the same. At every acquired index $i\in I$, the added term $Q(i)$ is zero, so the next readings agree. The induction reaches the last acquired index, hence the complete histories and actions coincide. At $t_*$ the matrix, gain, and source are still the common ones, but

$$
z'_{t_*}-z_{t_*}=Q(t_*)\ne0.
$$

This is the finite-history obstruction stated in Corollary 39.4 of [FIB self-calibrating relation mathematics](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md); the induction supplies its causal same-history justification. ∎

## 9. Scope of the continuation result

Theorem 7.1 concerns exact deterministic causal continuation after the fixed identity–$U$–$U^2$ calibration prefix. It does not determine the problem in which that initial prefix may itself be chosen adaptively. It also does not alter the fixed-path bounds: [FIB affine six-read sharp recovery, Section 10](FIB_AFFINE_SIX_READ_SHARP_RECOVERY.md) gives $C_{\mathrm{fix}}(d)=d+5$ for $d\ge1$ and $5\le C_{\mathrm{fix}}(0)\le6$, while Theorem 4.1 here gives the three-read optimum only inside the stated calibration-prefix class.

The statements use exact real arithmetic and unrestricted data-dependent finite-composite words. They make no assertion about randomized protocols, noisy reads, bit complexity, physical time, atom cost, physical realization beyond the declared common-source assumptions, or any Lean or empirical certification. The $d=0$, $\kappa\ne0$ construction permits an unbounded data-dependent finite atom count because the integer $n$ is selected from the recovered real parameters. These limitations are part of the quantifier boundary and do not weaken the exact mathematical conclusion (7.3).

The separate polynomial-gain and every-atom cubic contracts remain outside this affine-prefix continuation theorem. Other calibration prefixes and the unrestricted adaptive-prefix problem are also outside its quantifiers.

## 追加锚（本行以下为增补区）

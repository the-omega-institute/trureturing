# Two-node self-conjugate grids and the Schur ratio bounds at the points one and zero

This volume is reference input; nothing in it is kernel-verified. Its text is append-only: corrections and additions belong after the final append anchor.

## 1. Scope

Ostrovskii and Shcherbakov define a symmetric rational function $Q_{t,n,k}$ of $n$ variables, built from hook Schur polynomials, and state a conjecture with two inequalities for self-conjugate grids in the closed unit disk (cited fact (a)). This volume treats the case $n=2$, $k=1$. For every self-conjugate grid of two nodes it determines exactly when the first inequality holds for all degrees $t$ (Theorem 4.1), and, for grids with nonnegative real parts, exactly when the second inequality holds for all $t$ (Theorem 5.1). In both cases the condition for all $t$ coincides with the condition at $t=3$, and the admissible grids form an explicit region bounded by a line and by a branch of a hyperbola, respectively. In particular, Theorems 4.1 and 5.1 show that both inequalities fail on part of $\mathbb{D}^2$ for $(n,k)=(2,1)$. Corollary 4.3 gives the largest origin-centred disk on which the first inequality holds for all two-node self-conjugate grids.

## 2. Notation and cited facts

**Cited facts.**

(a) D. M. Ostrovskii and P. S. Shcherbakov, *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*, arXiv:2508.13554v2, Section 6. There $\mathbb{D}$ is the closed unit disk, $e_m$ and $h_m$ are the elementary and complete homogeneous symmetric polynomials, and $s_{(a\mid b)}$ is the Schur polynomial of the hook partition $(a+1,1^b)$ in Frobenius notation. For $0\le k<n\le t$ the function $Q_{t,n,k}:\mathbb{C}^n\to\mathbb{C}$ is defined by

$$
Q_{t,n,k}(\zeta_1,\dots,\zeta_n)=\sum_{d=0}^{t-n}(-1)^d\,\frac{\binom{t}{n+d}\,s_{(d\mid n-k-1)}(\zeta_1,\dots,\zeta_n)}{\binom{t}{n}\,e_{n-k}(\zeta_1,\dots,\zeta_n)}.
$$

A list $z_1,\dots,z_n$ is self-conjugate when its characteristic polynomial $f(x)=\prod_j(x-z_j)$ has real coefficients and every real root of $f$ has even multiplicity. Conjecture 6.2 of the paper states: for all $0\le k<n\le t$ and every self-conjugate $(z_1,\dots,z_n)\in\mathbb{D}^n$,

$$
\lvert Q_{t,n,k}(z_1+1,\dots,z_n+1)\rvert\le 1,
$$

and, if in addition $\operatorname{Re} z_j\ge0$ for all $j$, then

$$
\lvert s_{(t-n\mid n-k-1)}(z_1,\dots,z_n)\rvert\le\binom{t}{n}\,\lvert e_{n-k}(z_1,\dots,z_n)\rvert .
$$

The paper presents this as equivalent to its Conjecture 6.1 on worst-case Lagrange interpolation errors at the test points $1$ and $0$. It records that both inequalities hold with equality when $t=n$; it proves the first inequality for $t=n+1$ and even $k$, using a Newton-type inequality of Ellard and Šmigoc for self-conjugate lists (Theorem 2.2(1) of their paper, applied with $n-k$ even); since a self-conjugate list contains each real node an even number of times and its nonreal nodes in conjugate pairs, $n$ is even, so "$k$ even" and "$n-k$ even" are the same condition; and it obtains the second inequality for real grids in $[0,1]^n$ from a monotonicity theorem of Khare and Tao for ratios of Schur polynomials on the positive orthant. It proves no other case.

(b) Classical facts on two variables, used as inline steps: $h_m(x,y)=\sum_{i=0}^m x^iy^{m-i}$, so $(x-y)\,h_m(x,y)=x^{m+1}-y^{m+1}$; $h_m(x,y)=(x+y)\,h_{m-1}(x,y)-xy\,h_{m-2}(x,y)$ for $m\ge2$; $(\partial_x+\partial_y)\,h_m=(m+1)\,h_{m-1}$; the hook Schur polynomial $s_{(d\mid 0)}$ equals $h_{d+1}$; and the binomial theorem.

**Convention 2.1 (Two-node grids and the parameter $w$).** For $n=2$, $k=1$ write $Q_t=Q_{t,2,1}$. By cited fact (b), $s_{(d\mid 0)}=h_{d+1}$, so

$$
Q_t(\zeta_1,\zeta_2)=\frac{1}{\binom{t}{2}\,(\zeta_1+\zeta_2)}\sum_{d=0}^{t-2}(-1)^d\binom{t}{d+2}\,h_{d+1}(\zeta_1,\zeta_2),
$$

defined whenever $\zeta_1+\zeta_2\ne0$. A pair $(z_1,z_2)\in\mathbb{D}^2$ is self-conjugate exactly when $z_2=\overline{z_1}$: either $z_1$ is nonreal and $z_2$ is its conjugate, or $z_1=z_2$ is real. Since $Q_t$ is symmetric, every such pair is written $z=(-w,-\overline{w})$ with $w=a+ib$, $a,b\in\mathbb{R}$, $a^2+b^2\le1$; doubled real nodes are the case $b=0$. The shifted nodes are $\zeta=z+1=(1-w,1-\overline{w})$ and $e_1(\zeta)=2(1-a)$, which vanishes only for $w=1$, that is $z=(-1,-1)$; there $Q_t(z+1)$ is undefined, and this grid is excluded wherever $Q_t(z+1)$ appears. For the second inequality the nodes are written directly as $z=(u,\overline{u})$ with $u=a+ib$. Stance: repo-derived (notation fixed in this volume; the reduction $s_{(d\mid0)}=h_{d+1}$ is cited fact (b)).

**Convention 2.2 (The functions $F_t$ and $G_t^{\pm}$).** For $t\ge2$ and real $a,b$ put $w=a+ib$ and

$$
F_t(a,b)=t(t-1)(1-a)-t+h_{t-1}(w,\overline{w}),\qquad G_t^{\pm}(a,b)=t(t-1)\,a\pm h_{t-1}(w,\overline{w}).
$$

Since $h_{t-1}$ has real coefficients and is symmetric, $h_{t-1}(w,\overline{w})$ is real and is a polynomial in $a$ and $b^2$; hence $F_t$ and $G_t^{\pm}$ are real polynomials, even in $b$. For $\lvert w\rvert\le1$ the $m+1$ monomials of $h_m(w,\overline{w})$ all have modulus $\lvert w\rvert^m$, so

$$
\lvert h_m(w,\overline{w})\rvert\le(m+1)\,\lvert w\rvert^{m}\le m+1 .
$$

Stance: repo-derived (notation and an elementary bound used throughout).

## 3. Closed form

**Lemma 3.1 (Closed form of $Q_t$ on two-node self-conjugate grids).** For every $t\ge2$ and all $x,y$,

$$
\sum_{d=0}^{t-2}(-1)^d\binom{t}{d+2}\,h_{d+1}(x,y)=t-h_{t-1}(1-x,\,1-y)
$$

as polynomials. Consequently, for $w=a+ib$ with $w\ne1$ and $z=(-w,-\overline{w})$,

$$
Q_t(z_1+1,z_2+1)=\frac{t-h_{t-1}(w,\overline{w})}{t(t-1)(1-a)} .
$$

In particular $Q_2(z_1+1,z_2+1)=1$ for every such grid. Stance: suspected-novel (see Section 7).

**Proof.** Put $j=d+2$, so $(-1)^d=(-1)^j$ and the left side is $\sum_{j=2}^{t}(-1)^j\binom{t}{j}h_{j-1}(x,y)$. Multiply by $x-y$ and use $(x-y)h_{j-1}(x,y)=x^j-y^j$. The binomial theorem gives $\sum_{j=0}^{t}(-1)^j\binom{t}{j}(x^j-y^j)=(1-x)^t-(1-y)^t$; the terms $j=0$ and $j=1$ of this sum are $0$ and $-t(x-y)$. Hence

$$
(x-y)\sum_{j=2}^{t}(-1)^j\binom{t}{j}h_{j-1}(x,y)=(1-x)^t-(1-y)^t+t(x-y).
$$

Since $(1-x)-(1-y)=-(x-y)$, the right side equals $(x-y)\bigl(t-h_{t-1}(1-x,1-y)\bigr)$. Both sides of the claimed identity are polynomials, and their difference times the nonzero polynomial $x-y$ vanishes in the integral domain $\mathbb{Z}[x,y]$, so the identity holds. For the consequence take $(x,y)=(1-w,1-\overline{w})$, so that $(1-x,1-y)=(w,\overline{w})$, and divide by $\binom{t}{2}e_1(\zeta)=\tfrac{t(t-1)}{2}\cdot2(1-a)$, which is nonzero because $w\ne1$ and $\lvert w\rvert\le1$ force $a<1$. For $t=2$ the numerator is $2-2a$ and the denominator is $2(1-a)$. $\square$

**Lemma 3.2 (Reduction of the first inequality).** Let $t\ge2$, $w=a+ib$ with $a^2+b^2\le1$, $w\ne1$, and $z=(-w,-\overline{w})$. Then $\lvert Q_t(z_1+1,z_2+1)\rvert\le1$ if and only if $F_t(a,b)\ge0$. Stance: suspected-novel (see Section 7).

**Proof.** By Lemma 3.1, $Q_t(z+1)$ is real and its denominator $t(t-1)(1-a)$ is positive. By the bound of Convention 2.2, $h_{t-1}(w,\overline{w})\le t$, so the numerator $t-h_{t-1}(w,\overline{w})$ is nonnegative. Hence $\lvert Q_t(z+1)\rvert\le1$ is equivalent to $t-h_{t-1}(w,\overline{w})\le t(t-1)(1-a)$, which is $F_t(a,b)\ge0$. $\square$

## 4. The first inequality

**Theorem 4.1 (Region of the first inequality).** Let $w=a+ib$ with $a^2+b^2\le1$ and $w\ne1$, let $z=(-w,-\overline{w})$, and let $f(x)=(x+w)(x+\overline{w})$ be the characteristic polynomial of $z$. The following are equivalent.

1. $\lvert Q_{t,2,1}(z_1+1,z_2+1)\rvert\le1$ for every $t\ge2$.
2. $\lvert Q_{3,2,1}(z_1+1,z_2+1)\rvert\le1$.
3. $b^2\le3(1-a)^2$; equivalently, $z$ lies in the closed sector with vertex $-1$, bisected by the ray $[-1,\infty)$, of half-opening angle $\pi/3$.
4. $f'(-1)^2\ge f(-1)$.

Stance: suspected-novel (see Section 7).

**Proof.** Since $h_2(w,\overline{w})=(w+\overline{w})^2-w\overline{w}=4a^2-(a^2+b^2)=3a^2-b^2$,

$$
F_3(a,b)=6(1-a)-3+3a^2-b^2=3(1-a)^2-b^2,
$$

so 2 and 3 are equivalent by Lemma 3.2. In terms of $z_1=-w$ the inequality $\lvert b\rvert\le\sqrt3\,(1-a)$ reads $\lvert\operatorname{Im}z_1\rvert\le\sqrt3\,(\operatorname{Re}z_1+1)$, which is the stated sector. Further $f(-1)=(1-w)(1-\overline{w})=(1-a)^2+b^2$ and $f'(x)=2x+2a$, so $f'(-1)^2=4(1-a)^2$, and $f'(-1)^2\ge f(-1)$ is $3(1-a)^2\ge b^2$; thus 3 and 4 are equivalent. Clearly 1 implies 2.

It remains to show that 3 implies 1. Let

$$
S=\{(a,b)\in\mathbb{R}^2:\ a^2+b^2\le1,\ b^2\le3(1-a)^2\}.
$$

By Lemma 3.2 it suffices to show $F_t\ge0$ on $S$ for every $t\ge2$; the point $(1,0)$ belongs to $S$ and causes no difficulty, since $F_t(1,0)=-t+h_{t-1}(1,1)=0$. For $t=2$, $h_1(w,\overline{w})=2a$ gives $F_2\equiv0$. For $t=3$ the claim is the definition of $S$. Let $t\ge4$. Since $F_t$ is even in $b$, assume $b\ge0$.

*Monotonicity in $a$.* For fixed $b$, $\partial_a$ acts on $h_{t-1}(a+ib,a-ib)$ as $\partial_x+\partial_y$, so by cited fact (b) and the bound of Convention 2.2,

$$
\partial_aF_t(a,b)=-t(t-1)+t\,h_{t-2}(w,\overline{w})\le-t(t-1)+t(t-1)\lvert w\rvert^{t-2}\le0
$$

on the closed unit disk. For $0\le b\le1$, the condition $b^2\le3(1-a)^2$ together with $a\le1$ is equivalent to $a\le1-b/\sqrt3$, so the horizontal section of $S$ at height $b$ is the interval $-\sqrt{1-b^2}\le a\le\alpha(b)$ with $\alpha(b)=\min\{\sqrt{1-b^2},\,1-b/\sqrt3\}$; it is nonempty because $1-b/\sqrt3>0$. The segment lies in the unit disk, so $F_t(a,b)\ge F_t(\alpha(b),b)$ on it. Squaring shows $(1-b/\sqrt3)^2\le1-b^2$ exactly when $b\le\sqrt3/2$. Therefore the points $(\alpha(b),b)$ form two arcs: the edge $w=1+\beta\omega$, $0\le\beta\le1$, with $\omega=e^{2\pi i/3}$ and $\beta=2b/\sqrt3$; and the circular arc $w=e^{i\theta}$, $\pi/3\le\theta\le\pi/2$. It suffices to prove $F_t\ge0$ on both.

*Circular arc.* For $w=e^{i\theta}$ with $\pi/3\le\theta\le\pi/2$ one has $1-a=1-\cos\theta\ge\tfrac12$ and $h_{t-1}(w,\overline{w})=\sin(t\theta)/\sin\theta\ge-1/\sin\theta\ge-2/\sqrt3$. Hence

$$
F_t\ge\frac{t(t-1)}{2}-t-\frac{2}{\sqrt3}=\frac{t(t-3)}{2}-\frac{2}{\sqrt3}\ge2-\frac{2}{\sqrt3}>0\qquad(t\ge4).
$$

*Edge.* Let $w=1+\beta\omega$ with $0<\beta\le1$ (the endpoint $\beta=0$ is $(1,0)$). Then $1-a=\beta/2$ and $w-\overline{w}=\beta(\omega-\overline{\omega})=i\sqrt3\,\beta$. Write $\omega^j-\overline{\omega}^j=2i\sin(2\pi j/3)=i\sqrt3\,\chi(j)$, where $\chi(j)$ equals $1$, $-1$, $0$ according as $j\equiv1,2,0\pmod 3$. The binomial theorem gives

$$
h_{t-1}(w,\overline{w})=\frac{w^t-\overline{w}^t}{w-\overline{w}}=\sum_{j=1}^{t}\binom{t}{j}\beta^{j-1}\chi(j)=\sum_{m\ge0}\Bigl[\binom{t}{3m+1}\beta^{3m}-\binom{t}{3m+2}\beta^{3m+1}\Bigr],
$$

with binomial coefficients vanishing beyond $t$. The term $m=0$ is $t-\binom{t}{2}\beta$, which cancels $t(t-1)(1-a)-t=\binom{t}{2}\beta-t$. Hence

$$
F_t(1-\tfrac{\beta}{2},\tfrac{\sqrt3}{2}\beta)=\sum_{m\ge1}\binom{t}{3m+1}\beta^{3m}\Bigl[1-\beta\,\frac{t-3m-1}{3m+2}\Bigr],
$$

using $\binom{t}{3m+2}=\binom{t}{3m+1}\frac{t-3m-1}{3m+2}$, valid also when $3m+1>t$ since then both coefficients vanish. For $m\ge1$ and $3m+1\le t$ one has $\frac{t-3m-1}{3m+2}\le\frac{t-4}{5}$. Therefore every bracket with a nonzero coefficient is nonnegative whenever $\beta(t-4)\le5$, and then $F_t\ge0$. This covers every $\beta\in(0,1]$ when $t\le9$. Let $t\ge10$ and $\beta>5/(t-4)$. Using $\lvert w\rvert\le1$,

$$
\lvert h_{t-1}(w,\overline{w})\rvert=\frac{\lvert w^t-\overline{w}^t\rvert}{\sqrt3\,\beta}\le\frac{2}{\sqrt3\,\beta},
\qquad
F_t\ge g(\beta):=\frac{t(t-1)}{2}\beta-t-\frac{2}{\sqrt3\,\beta}.
$$

The function $g$ is increasing on $(0,\infty)$, and

$$
g\Bigl(\frac{5}{t-4}\Bigr)=\frac{5t(t-1)-2t(t-4)}{2(t-4)}-\frac{2(t-4)}{5\sqrt3}=\frac{3t(t+1)}{2(t-4)}-\frac{2(t-4)}{5\sqrt3}>\frac{3t}{2}-\frac{t}{4}>0,
$$

because $\frac{t+1}{t-4}>1$ and $\frac{2}{5\sqrt3}<\frac14$. Hence $F_t\ge g(\beta)>g(5/(t-4))>0$. Thus $F_t\ge0$ on the edge for every $t\ge4$, which completes the proof. $\square$

**Remark 4.2 (Doubled real nodes).** For $b=0$, that is $z=(-a,-a)$ with $-1\le a<1$, one has $h_{t-1}(a,a)=ta^{t-1}$ and

$$
F_t(a,0)=t(1-a)\Bigl[(t-1)-\sum_{j=0}^{t-2}a^j\Bigr]\ge0,
$$

since each $a^j\le1$; this is the case $b=0$ of Theorem 4.1, where condition 3 always holds. The statement for doubled real nodes has a precedent: the source reports (Section 6) a theorem of Kallioniemi [H. Kallioniemi, *On bounds for the derivatives of a complex-valued function on a compact interval*, Math. Scand. 39 (1976) 295–314] that for a simple real grid $z_1<\dots<z_n$ in $[-1,1]$ the monomial $\frac{1}{n!}z^n$ is pointwise worst-case for the $k$-th derivative of the interpolation error on the segments $I_s$, the last of which is $I_{n-k}=[z_n,1]$ and contains the test point $1$; the first inequality at a doubled real node is the confluent limit of this bound at $1$: away from the excluded grid, $Q_t(z+1)$ is a rational function of the nodes with nonvanishing denominator $e_1(z+1)$, hence continuous, so the inequality for simple grids $z_1<z_2$ in $[-1,1)$ passes to the limit $z_1,z_2\to-a$; the direct computation above proves the doubled case independently. Stance: precedent: Kallioniemi's pointwise theorem for simple real grids (`literature-attested`, as reported in the source); the extension to doubled nodes by the confluent limit, and the direct proof given here, are `repo-derived`.

**Corollary 4.3 (Largest admissible disk).** Let $0<\rho\le1$. The inequality $\lvert Q_{t,2,1}(z_1+1,z_2+1)\rvert\le1$ holds for every $t\ge2$ and every self-conjugate grid $z\in\{\lvert\zeta\rvert\le\rho\}^2$ with $z\ne(-1,-1)$ if and only if $\rho\le\sqrt3/2$. Stance: suspected-novel (see Section 7).

**Proof.** By Convention 2.1 these grids are $z=(-w,-\overline{w})$ with $\lvert w\rvert\le\rho$, $w\ne1$. For $\lvert w\rvert\le1$ one has $a\le1$, so condition 3 of Theorem 4.1 reads $\sqrt3\,a+\lvert b\rvert\le\sqrt3$. If $\rho\le\sqrt3/2$, the Cauchy–Schwarz inequality gives $\sqrt3\,a+\lvert b\rvert\le2\lvert w\rvert\le\sqrt3$, and Theorem 4.1 applies. If $\rho>\sqrt3/2$, the point $w=\rho e^{i\pi/6}$ satisfies $\lvert w\rvert=\rho\le1$, $w\ne1$ and $\sqrt3\,a+b=2\rho>\sqrt3$, so by Theorem 4.1 the inequality fails at $t=3$. $\square$

**Remark 4.4 (Relation to the case $t=n+1$).** Theorem 4.1 reduces the first inequality for $(n,k)=(2,1)$ and all $t$ to the single degree $t=n+1=3$, the degree at which the source proves the inequality for even $k$ (cited fact (a)); here $k=1$ is odd. For the grid $z=(-\tfrac{9}{10}+\tfrac{2}{5}i,\,-\tfrac{9}{10}-\tfrac{2}{5}i)\in\mathbb{D}^2$ one has $w=\tfrac{9}{10}-\tfrac{2}{5}i$, so $b^2=\tfrac{4}{25}>\tfrac{3}{100}=3(1-a)^2$, and Lemma 3.1 gives $Q_3(z_1+1,z_2+1)=\frac{3-h_2(w,\overline{w})}{6(1-a)}=\frac{3-227/100}{6/10}=\frac{73}{60}>1$. Stance: repo-derived (consequence of Theorem 4.1 and Lemma 3.1).

## 5. The second inequality

**Theorem 5.1 (Region of the second inequality).** Let $u=a+ib$ with $a\ge0$ and $a^2+b^2\le1$, let $z=(u,\overline{u})$, and let $f(x)=(x-u)(x-\overline{u})$. For $(n,k)=(2,1)$ the second inequality of cited fact (a) reads $\lvert s_{(t-2\mid0)}(z)\rvert\le\binom{t}{2}\lvert e_1(z)\rvert$, that is,

$$
\lvert h_{t-1}(u,\overline{u})\rvert\le t(t-1)\,a .
$$

The following are equivalent.

1. This inequality holds for every $t\ge2$.
2. This inequality holds for $t=3$.
3. $b^2\le3a^2+6a$.
4. $f(0)\le f'(0)^2-3f'(0)$.

For $t=2$ the inequality holds with equality for every such $u$. Stance: suspected-novel (see Section 7).

**Proof.** For $t=2$, $h_1(u,\overline{u})=2a$. For $t=3$, $h_2(u,\overline{u})=3a^2-b^2$ as in the proof of Theorem 4.1, so the inequality reads $-6a\le3a^2-b^2\le6a$. The right half holds because $0\le a\le1$ gives $3a^2\le6a$, and the left half is $b^2\le3a^2+6a$; so 2 and 3 are equivalent. Since $f(0)=a^2+b^2$ and $f'(0)=-2a$, condition 4 reads $a^2+b^2\le4a^2+6a$, which is 3. Clearly 1 implies 2.

It remains to show that 3 implies 1. Let $H=\{(a,b):\ a\ge0,\ a^2+b^2\le1,\ b^2\le3a^2+6a\}$. The inequality for $t$ is $G_t^{+}\ge0$ and $G_t^{-}\ge0$. The case $t=2$ is done; let $t\ge3$, and assume $b\ge0$ since $G_t^{\pm}$ is even in $b$.

*Monotonicity in $a$.* As in the proof of Theorem 4.1,

$$
\partial_aG_t^{\pm}(a,b)=t(t-1)\pm t\,h_{t-2}(u,\overline{u})\ge t(t-1)-t(t-1)\lvert u\rvert^{t-2}\ge0
$$

on the closed unit disk. Since $3a^2+6a$ is increasing for $a\ge0$, the horizontal section of $H$ at height $b\ge0$ is the interval $a_0(b)\le a\le\sqrt{1-b^2}$, where $a_0(b)=\sqrt{1+b^2/3}-1\ge0$ is the nonnegative root of $3a^2+6a=b^2$, whenever this interval is nonempty; the segment lies in the unit disk. Hence $G_t^{\pm}(a,b)\ge G_t^{\pm}(a_0(b),b)$, and the left endpoint $(a_0,b)$ lies in $H$, so $a_0^2+b^2=4a_0^2+6a_0\le1$, which means $0\le a_0\le a^*:=\frac{\sqrt{13}-3}{4}$. It therefore suffices to prove, for $0\le a\le a^*$, $b=\sqrt{3a^2+6a}$ and $u=a+ib$,

$$
\lvert h_{t-1}(u,\overline{u})\rvert\le t(t-1)\,a\qquad(t\ge3).
$$

On this arc $r^2:=\lvert u\rvert^2=4a^2+6a\le1$, and $a^*<\tfrac14$ because $\sqrt{13}<4$. Write $H_m=h_m(u,\overline{u})$. By cited fact (b), $H_0=1$, $H_1=2a$ and $H_m=2aH_{m-1}-r^2H_{m-2}$, which yields

$$
H_2=-6a,\quad H_3=-8a^3-24a^2,\quad H_4=-16a^4-24a^3+36a^2,\quad H_5=96a^4+216a^3,
$$

$$
H_6=64a^6+384a^5+432a^4-216a^3 .
$$

Using $0\le a\le\tfrac14$:

- $t=3$: $\lvert H_2\rvert=6a$, equality.
- $t=4$: $\lvert H_3\rvert=a(8a^2+24a)\le a\bigl(\tfrac12+6\bigr)<12a$.
- $t=5$: $H_4=4a^2(9-6a-4a^2)$ with $0\le9-6a-4a^2\le9$, so $\lvert H_4\rvert\le36a^2\le9a<20a$.
- $t=6$: $\lvert H_5\rvert=a(96a^3+216a^2)\le a\bigl(\tfrac32+\tfrac{27}{2}\bigr)=15a<30a$.
- $t=7$: $\lvert H_6\rvert\le a(64a^5+384a^4+432a^3+216a^2)\le a\bigl(\tfrac1{16}+\tfrac32+\tfrac{27}{4}+\tfrac{27}{2}\bigr)=\tfrac{349}{16}a<42a$.
- $t\ge8$: by the bound of Convention 2.2 and $r\le1$, $\lvert H_{t-1}\rvert\le t\,r^{t-1}\le t\,r^2=t(4a+6)\,a\le7t\,a\le t(t-1)\,a$.

This proves the inequality on the arc for every $t\ge3$, and hence on $H$. $\square$

**Remark 5.2 (Shape of the region).** The boundary curve $b^2=3a^2+6a$ is a branch of the hyperbola $3(a+1)^2-b^2=3$ through the origin; it meets the unit circle at $a=a^*=\frac{\sqrt{13}-3}{4}$. On the imaginary axis the region contains only $u=0$: for $u=\pm ib$ with $b\ne0$ one has $e_1(z)=0$ while $h_2(u,\overline{u})=-b^2\ne0$. Every doubled real node $u=a\in[0,1]$ belongs to the region; this is the two-node case of the source's earlier result for real grids in $[0,1]^n$ (cited fact (a)). Stance: repo-derived (direct consequences of Theorem 5.1), with the doubled-real-node statement `literature-attested` through cited fact (a).

## 6. Boundaries and open questions

**Remark 6.1 (What is not claimed).** This volume makes no statement about $Q_{t,n,k}$ for $n\ge3$, about the case $(n,k)=(2,0)$, about Conjecture 6.1 or Conjecture 6.3 of the source, or about the grid $z=(-1,-1)$, where $Q_{t,2,1}(z+1)$ is undefined. It does not treat the interpolation-theoretic formulation of cited fact (a) beyond the Schur-polynomial inequalities stated there. Stance: repo-derived.

**Open question 6.2 (The case $k=0$ for two nodes).** For $(n,k)=(2,0)$ the first inequality involves $s_{(d\mid1)}$ and $e_2$, and the second involves $s_{(t-2\mid1)}$ and $e_2$. Determine, for two-node self-conjugate grids in $\mathbb{D}^2$, the set of grids on which each inequality holds for every $t\ge2$, and decide whether, as in Theorems 4.1 and 5.1, it coincides with the set on which it holds at $t=3$. Stance: repo-derived (question posed in this volume).

## 7. Sources and literature status

| Source | Exact scope and use |
| --- | --- |
| D. M. Ostrovskii, P. S. Shcherbakov, *Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation*, arXiv:2508.13554v2, Section 6 (Definition 6.1, Conjectures 6.1 and 6.2, Corollary 6.1) | `literature-attested`: the definition of the function $Q_{t,n,k}$, of self-conjugate lists, and the wording of Conjecture 6.2 (cited fact (a)); the equality cases $t=n$, the first inequality for $t=n+1$ and even $k$ (equivalently $n-k$ even, since $n$ is even for self-conjugate lists), and the second inequality for real grids in the unit cube. Not used for any statement about the first inequality with $t>n$ and odd $k$, or about the second inequality for nonreal grids, about which the paper proves nothing. |
| A. Khare, T. Tao, *On the sign patterns of entrywise positivity preservers in fixed dimension*, Amer. J. Math. 143 (2021) 1863–1929 | `literature-attested`: the monotonicity theorem through which the source obtains the second inequality for real grids. Not used in any proof of this volume. |
| R. Ellard, H. Šmigoc, *Families of Newton-like inequalities for sets of self-conjugate complex numbers*, Linear Algebra Appl. 597 (2020) 46–68 | `literature-attested`: the notion of self-conjugate list and the inequality through which the source treats $t=n+1$ for even $k$. Not used in any proof of this volume. |
| H. Kallioniemi, *On bounds for the derivatives of a complex-valued function on a compact interval*, Math. Scand. 39 (1976) 295–314, as reported in Section 6 of arXiv:2508.13554v2 | `literature-attested` (through the source's report; the original was not consulted): the pointwise worst-case property of $\frac{1}{n!}z^n$ on the segments $I_s$ for simple real grids, precedent for Remark 4.2 (simple real grids only). Not used in any proof of this volume. |
| — | `repo-derived`: Conventions 2.1 and 2.2, the proof in Remark 4.2 and its extension of Kallioniemi's simple-grid bound to doubled real nodes by the confluent limit, Remarks 4.4, 5.2 and 6.1, Open question 6.2. The two-variable facts of cited fact (b) are classical and enter only as inline steps. |
| — | `suspected-novel`: Lemmas 3.1 and 3.2, Theorems 4.1 and 5.1, Corollary 4.3. Searched: the full text of arXiv:2508.13554v2 and its version history; the citation index of that paper, whose only citing item concerns a trinomial difference equation and does not address Conjecture 6.2; arXiv metadata queries combining self-conjugate, Schur and interpolation; web searches combining Ostrovskii, Shcherbakov, self-conjugate nodes, Schur ratio and the conjectures of the paper. No statement of these results was found in the searched scope; this establishes no worldwide priority. |

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）

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
## 8. Analytic endpoint separation on the nonreal sector boundary

**Definition 8.1 (Actual interpolation grid and entire target class).** Let $\mathbb D=\{z\in\mathbb C:|z|\le1\}$ and $I=[-1,1]$. For every real $d$ with $0<d\le\tfrac12$, put

$$
w_d=1-d+i\sqrt3\,d,\qquad W_d=(w_d,\overline{w_d}),\qquad
p_d(z)=(z-w_d)(z-\overline{w_d}).
$$

For every entire function $g:\mathbb C\to\mathbb C$, let $I_dg$ be the unique polynomial of degree at most one with the same values as $g$ at the two nodes of $W_d$, and define

$$
L_d(g)=g'(1)-(I_dg)'(1)
=g'(1)-\frac{g(w_d)-g(\overline{w_d})}{w_d-\overline{w_d}}.
$$

Write $\|h\|_{\mathbb D}=\sup_{z\in\mathbb D}|h(z)|$, and set

$$
\mathscr E_2(\mathbb D)=
\{g:\mathbb C\to\mathbb C:\ g\text{ is entire and }\|g''\|_{\mathbb D}\le1\},
$$

$$
\mathcal K_d=
\left\{x\in I:\
\sup_{g\in\mathscr E_2(\mathbb D)}
|g'(x)-(I_dg)'(x)|=\frac{|p_d'(x)|}{2}\right\}.
$$

Thus $\mathcal K_d$ is exactly the analytic Kallioniemi set $\mathcal I^{\mathbb D}_{2,1}(W_d)$ in equation (35) of [Ostrovskii–Shcherbakov, arXiv:2508.13554v2, Section 6.2](https://arxiv.org/html/2508.13554v2#S6.SS2). The class is the entire complex-valued class specified there, without a real-coefficient restriction. For integers $t\ge2$ write $m_t(z)=z^t/[t(t-1)]$; these are the source's normalized monomials $(t-2)!z^t/t!$, and $\|m_t''\|_{\mathbb D}=\|z^{t-2}\|_{\mathbb D}=1$.

**Proposition 8.2 (Reflection correspondence and all monomial degrees).** For every real $0<d\le\tfrac12$, the actual grid $W_d$ is simple and self-conjugate in $\mathbb D^2$, and

$$
\frac{|p_d'(1)|}{2}=d,\qquad
\frac{L_d(m_t)}d
=Q_{t,2,1}(1-w_d,1-\overline{w_d})\quad(t\in\mathbb Z,\ t\ge2).
$$

The reflected supplier grid in Theorem 4.1 is $Z_d=(-w_d,-\overline{w_d})$, so the argument of $Q$ here is $Z_d+(1,1)$, not $W_d+(1,1)$. Moreover,

$$
\sup_{t\in\mathbb Z,\ t\ge2}|L_d(m_t)|=d,
\qquad L_d(m_2)=L_d(m_3)=d.
$$

Stance: repo-derived; the all-degree bound is reused from the whole applicable Theorem 4.1, with the correspondence below.

**Proof.** The imaginary part $\sqrt3\,d$ is positive and

$$
|w_d|^2=(1-d)^2+3d^2=1-2d+4d^2\le1.
$$

Hence the nodes are distinct nonreal conjugates in $\mathbb D$, and have a real characteristic polynomial with no real roots. Also

$$
p_d'(1)=2-w_d-\overline{w_d}=2d>0.
$$

For every integer $t\ge2$, the two-variable identity in cited fact (b) gives

$$
(I_dm_t)'(1)
=\frac{h_{t-1}(w_d,\overline{w_d})}{t(t-1)},\qquad
L_d(m_t)=\frac{t-h_{t-1}(w_d,\overline{w_d})}{t(t-1)}.
$$

Lemma 3.1 identifies the quotient of the last expression by $d=1-\operatorname{Re}w_d$ with $Q_{t,2,1}(Z_d+(1,1))$. This is also the specialization of the source's Corollary 6.1, equation (30), to test point $z=1$, $(n,k)=(2,1)$ and actual nodes $W_d$: its argument is $1_2-z^{-1}W_d=(1-w_d,1-\overline{w_d})$. Its denominator is nonzero, since $p_d'(1)=2d$, and its interpolation premises hold for this simple disk grid (one may take both radius bounds equal to one). This verifies the sign and the normalization directly, without the reduction in the source's Proposition 6.2.

Now $a=1-d$, $b=\sqrt3\,d$ satisfy $a^2+b^2\le1$, $w_d\ne1$, and $b^2=3(1-a)^2$. Theorem 4.1 therefore gives $|Q_{t,2,1}(Z_d+(1,1))|\le1$ for every integer $t\ge2$. Thus $|L_d(m_t)|\le d$ for all such $t$. Finally,

$$
h_1(w_d,\overline{w_d})=2(1-d),\qquad
h_2(w_d,\overline{w_d})=3(1-d)^2-3d^2=3-6d,
$$

so the displayed formula for $L_d(m_t)$ gives $L_d(m_2)=L_d(m_3)=d$. Both degrees attain the supremum. $\square$

**Theorem 8.3 (An entire quartic exceeding every normalized monomial).** For every real $0<d\le\tfrac12$, define

$$
e=\frac{d^2}{6},\qquad N=\sqrt{1+4e^2},\qquad
G_d(z)=\frac{z^3/6+e(z^2/2-z^4/12)}{N}.
$$

Then $G_d$ has real coefficients and degree exactly four, belongs to $\mathscr E_2(\mathbb D)$ with $\|G_d''\|_{\mathbb D}=1$, and satisfies

$$
L_d(G_d)=d\sqrt{1+\frac{d^4}{9}}>d
=\sup_{t\in\mathbb Z,\ t\ge2}|L_d(m_t)|.
$$

Stance: repo-derived.

**Proof.** Since $e>0$ and $N>0$, the coefficient of $z^4$ is $-e/(12N)\ne0$. Differentiating twice gives

$$
G_d''(z)=\frac{z+e(1-z^2)}N.
$$

For $z=e^{i\theta}$ on the unit circle,

$$
z+e(1-z^2)=z\bigl(1-2ie\sin\theta\bigr),\qquad
|z+e(1-z^2)|^2=1+4e^2\sin^2\theta\le N^2,
$$

with equality at $z=i$ and $z=-i$. The classical maximum modulus principle, applied to this polynomial on the closed unit disk, gives $\|G_d''\|_{\mathbb D}=1$. Thus the polynomial is an admissible entire input to the exact class of Definition 8.1.

To calculate its error, set $a=1-d$ and $b=\sqrt3\,d$. The two-variable identity $h_3(a+ib,a-ib)=4a(a^2-b^2)$ gives

$$
h_3(w_d,\overline{w_d})
=4(1-d)(1-2d-2d^2)=4-12d+8d^3,
$$

and hence, by the monomial error formula in Proposition 8.2,

$$
L_d(m_4)=d-\frac23d^3,\qquad
L_d(m_2-m_4)=\frac23d^3=4de.
$$

The functional $L_d$ is complex-linear and $G_d=[m_3+e(m_2-m_4)]/N$. Using Proposition 8.2 at degrees two and three therefore gives

$$
L_d(G_d)=\frac{d+4de^2}{N}=dN
=d\sqrt{1+\frac{d^4}{9}}>d.
$$

The final comparison uses $d>0$ and Proposition 8.2 for every degree $t\ge2$. $\square$

**Proposition 8.4 (Minimum polynomial degree of a violation).** For every real $0<d\le\tfrac12$ and every polynomial $P\in\mathbb C[z]$ of degree at most three with $\|P''\|_{\mathbb D}\le1$,

$$
|L_d(P)|\le d.
$$

The bound is attained by $m_2$ and $m_3$. Consequently the minimum degree of a polynomial in $\mathscr E_2(\mathbb D)$ with $|L_d(P)|>d$ is exactly four, for each grid $W_d$. Stance: repo-derived.

**Proof.** Write $P''(z)=A+Bz$ with $A,B\in\mathbb C$. Then $P=A m_2+B m_3+R$ for some affine polynomial $R$. Interpolation reproduces $R$, so $L_d(R)=0$, and Proposition 8.2 yields $L_d(P)=d(A+B)$. For complex $A,B$,

$$
\|A+Bz\|_{\mathbb D}=|A|+|B|.
$$

The upper bound is the triangle inequality. If $A$ and $B$ are both nonzero, equality is attained at $z=(A/|A|)(\overline B/|B|)$, which has modulus one and makes $Bz$ a nonnegative real multiple of $A$. If either coefficient is zero, equality is immediate. Therefore

$$
|L_d(P)|=d|A+B|\le d(|A|+|B|)
=d\|P''\|_{\mathbb D}\le d.
$$

Theorem 8.3 provides a violating polynomial of degree four, and the preceding bound excludes every lower degree, including all complex coefficient choices. $\square$

**Corollary 8.5 (Analytic endpoint exclusion and pointwise failure of monomial maximization).** For every real $0<d\le\tfrac12$,

$$
\sup_{g\in\mathscr E_2(\mathbb D)}|L_d(g)|
\ \ge\ d\sqrt{1+\frac{d^4}{9}}
\ >\ \frac{|p_d'(1)|}{2}=d,
\qquad 1\notin\mathcal K_d.
$$

Thus on each identical actual interpolation grid $W_d$, every normalized-monomial test at $1$ passes, but the analytic equality at $1$ fails. In particular the pointwise normalized-monomial maximization assertion of [Ostrovskii–Shcherbakov, arXiv:2508.13554v2, Proposition 6.2, Section 6.3](https://arxiv.org/html/2508.13554v2#S6.SS3) fails for $(n,k)=(2,1)$, test point $1$, and these simple grids. Stance: repo-derived, with the target class, Kallioniemi-set definition and disputed assertion cited from the source.

**Proof.** Theorem 8.3 supplies an entire member of the supremum class whose error strictly exceeds $|p_d'(1)|/2$, so Definition 8.1 excludes $1$. Proposition 8.2 bounds all normalized monomials at that same grid and test point by $d$. Multiplying a monomial by a unimodular constant, or adding an affine polynomial, does not change its absolute error, so neither enlargement repairs the maximization assertion.

The correspondence is pointwise between the analytic test on $W_d$ and the Schur test on $Z_d=-W_d$ established in Proposition 8.2. The reflection is a bijection of the class of self-conjugate disk grids, but $W_d$ and $Z_d$ are distinct grids. The separation does not assign different truth values to the two globally universal Conjectures 6.1 and 6.2: the former fails by the quartic above, and the latter already fails by the distinct $73/60$ example of Remark 4.4. That example and the all-monomial region of Theorem 4.1 are preserved as separate mathematical facts. The conclusion here concerns the asserted pointwise supplier reduction, not the source's separate amplitude-maximization theorems.

The parameter range includes $d=\tfrac12$, when $|w_d|=1$, and has $|w_d|<1$ for $0<d<\tfrac12$. At $d=0$ the two nodes coalesce at $1$, the divided difference defining $L_d$ is undefined, and the strict gap in the displayed formula vanishes; no confluent statement follows. For $d>\tfrac12$ the nodes leave $\mathbb D$. Reversing the sign of $\operatorname{Im}w_d$ only interchanges the nodes and leaves interpolation unchanged.

The displayed quartic supplies a strict lower bound, without identifying the exact supremum over all entire functions or over all quartics. These statements impose no conclusion on the rest of the sector interior, arbitrary grids, $n\ge3$, or $k=0$. The real-grid result of Kallioniemi reported in Remark 4.2 is not a premise of this argument. $\square$

## 追加锚（本行以下为增补区）
## 9. The uniform analytic bound for every simple conjugate pair

**Definition 9.1 (Uniform error on the original entire class).** For real $a,b$ satisfying

$$
b>0,\qquad a^2+b^2\le1,
$$

put $w=a+ib$, $W_{a,b}=(w,\overline w)$ and $p_{a,b}(z)=(z-w)(z-\overline w)$. Use the class $\mathscr E_2(\mathbb D)$ of Definition 8.1, with no restriction on the coefficients or real values of its members. The actual two-point interpolant and its slope are

$$
I_{a,b}g(z)=\frac{z-\overline w}{w-\overline w}g(w)
+\frac{w-z}{w-\overline w}g(\overline w),\qquad
S_{a,b}(g)=\frac{g(a+ib)-g(a-ib)}{2ib}.
$$

The denominator is nonzero, and $(I_{a,b}g)'(z)=S_{a,b}(g)$ for every $z$. Define

$$
T_{a,b,x}(g)=g'(x)-S_{a,b}(g),\qquad
E(a,b)=\sup_{g\in\mathscr E_2(\mathbb D)}\ \sup_{-1\le x\le1}|T_{a,b,x}(g)|.
$$

Here the nodes are simple nonreal conjugates, including those on the unit circle. The case $b=0$ is excluded: the displayed interpolant does not define interpolation at a repeated node.

**Lemma 9.2 (A real boundary kernel for the imaginary-axis slope).** Let $0<b\le1$, let $d\mu(\theta)=d\theta/(2\pi)$ on $[0,2\pi]$, and define

$$
B_b(\theta)=2\sum_{j=0}^\infty
\frac{(-1)^{j+1}b^{2j+2}}{(2j+2)(2j+3)}\cos((2j+1)\theta).
$$

This is a continuous real function of $\theta$ and $b\in(0,1]$, has mean zero, and satisfies

$$
B_b(\pi-\theta)=-B_b(\theta),\qquad
\cos\theta\,B_b(\theta)\le0,\qquad
|B_b(\theta)|\le C<\frac{19}{50}<\frac{31}{81},
$$

where arguments are interpreted modulo $2\pi$ and

$$
C=\log\frac53+2\arctan\frac13-\frac79.
$$

If $h$ is entire and $H$ is its entire primitive with $H(0)=0$, then

$$
\frac1{2b}\int_{-b}^b H(it)\,dt
=\int_0^{2\pi}h(e^{i\theta})B_b(\theta)\,d\mu(\theta).
$$

Stance: repo-derived.

**Proof.** The absolute values of the summands are bounded by $2/[(2j+2)(2j+3)]$, a summable sequence independent of $b\le1$ and $\theta$. Thus the series converges absolutely and uniformly, including at $b=1$. The mean and the reflection identity follow term by term.

For the integral identity first take $h(z)=z^m$, $m\ge0$, so $H(z)=z^{m+1}/(m+1)$. Symmetric integration gives

$$
\frac1{2b}\int_{-b}^b H(it)\,dt
=\begin{cases}
0,&m\text{ even},\\
\displaystyle\frac{(-1)^{j+1}b^{2j+2}}{(2j+2)(2j+3)},&m=2j+1.
\end{cases}
$$

These are precisely the moments $\int e^{im\theta}B_b(\theta)\,d\mu(\theta)$: for positive integers $m,r$, the integral of $e^{im\theta}\cos(r\theta)$ is $1/2$ when $m=r$ and zero otherwise. The zeroth moment vanishes. For an arbitrary entire $h(z)=\sum_{m\ge0}c_mz^m$, its Taylor series converges absolutely and uniformly on the closed disk, as does the integrated series for $H$. For example, Cauchy's coefficient estimate on any circle of radius $R>1$ bounds $|c_m|$ by $\max_{|z|=R}|h(z)|R^{-m}$. Consequently both integrals pass through the series, proving the identity for all complex coefficients.

To control the kernel, the geometric series and $\int_0^1t^{2j+1}(1-t)\,dt=1/[(2j+2)(2j+3)]$ give

$$
B_b(\theta)=-2b^2\int_0^1t(1-t)
\operatorname{Re}\frac{e^{-i\theta}}{1+b^2t^2e^{-2i\theta}}\,dt
$$

$$
=-2b^2\cos\theta\int_0^1
\frac{t(1-t)(1+b^2t^2)}{(1-b^2t^2)^2+4b^2t^2\cos^2\theta}\,dt.
$$

The sum of the integrals of the absolute values of the expanded geometric terms is at most $2\sum_{j\ge0}1/[(2j+2)(2j+3)]<\infty$. This justifies the interchange even for $b=1$; the geometric identity is needed only for $t<1$. If $b=1$ and $\cos\theta=0$, the integrand is zero for $t<1$ and its endpoint value can be set to zero. In particular $B_b=0$ when $\cos\theta=0$, and otherwise its sign is opposite to that of $\cos\theta$.

Put $c=|\cos\theta|$. For $c>0$, substituting $y=bt$ gives

$$
|B_b(\theta)|=2c\int_0^b
\frac{y(1-y/b)(1+y^2)}{(1-y^2)^2+4c^2y^2}\,dy
\le\int_0^1(1-t)q(t,c)\,dt,
$$

where

$$
q(t,c)=\frac{2ct(1+t^2)}{(1-t^2)^2+4c^2t^2}.
$$

Indeed $1-y/b\le1-y$ on $0\le y\le b\le1$, and the integrands are nonnegative. For $0\le t\le1/3$, differentiation with respect to $c$ shows that $q(t,c)$ is nondecreasing on $0\le c\le1$: the sign of this derivative is the sign of $(1-t^2)^2-4c^2t^2$, which is nonnegative because $1-t^2\ge2t$. Therefore

$$
q(t,c)\le q(t,1)=\frac{2t}{1+t^2}\quad(0\le t\le1/3).
$$

For $1/3\le t<1$, the inequality $(1-t^2)^2+4c^2t^2\ge4ct(1-t^2)$ instead gives

$$
(1-t)q(t,c)\le\frac{1+t^2}{2(1+t)}.
$$

The preceding bounds also apply at $c=0$ by the already established value $B_b=0$. Integration yields

$$
\begin{aligned}
|B_b(\theta)|
&\le\int_0^{1/3}\frac{2t(1-t)}{1+t^2}\,dt
+\int_{1/3}^1\frac{1+t^2}{2(1+t)}\,dt\\
&=\log\frac{10}{9}-\frac23+2\arctan\frac13
+\log\frac32-\frac19=C.
\end{aligned}
$$

For completeness, the convergent series $\log[(1+s)/(1-s)]=2\sum_{r\ge0}s^{2r+1}/(2r+1)$ at $s=1/4$ gives

$$
\log\frac53\le\frac12+\frac1{96}
+\frac{2}{5}\frac{(1/4)^5}{1-1/16}=\frac{613}{1200}.
$$

The alternating series for $\arctan(1/3)$ gives $\arctan(1/3)\le1/3-1/81+1/1215=391/1215$. Hence

$$
C\le\frac{613}{1200}-\frac{163}{1215}
=\frac{36613}{97200}<\frac{19}{50}<\frac{31}{81}.
$$

Both series follow by integrating their geometric series on compact subintervals of $(-1,1)$; the alternating remainder has the sign of its first omitted term. Thus these bounds involve no approximation of $C$. $\square$

**Lemma 9.3 (The full interval for imaginary-axis nodes).** For every $0<b\le1$, every entire complex-valued $g$, and every $x\in[-1,1]$,

$$
\left|g'(x)-\frac{g(ib)-g(-ib)}{2ib}\right|\le\|g''\|_{\mathbb D}.
$$

Stance: repo-derived.

**Proof.** Write $h=g''$ and $H=g'-g'(0)$. The fundamental theorem of calculus along the vertical segment gives

$$
\frac{g(ib)-g(-ib)}{2ib}=g'(0)+\frac1{2b}\int_{-b}^b H(it)\,dt.
$$

For real $|t|<1$ let

$$
P_t(\theta)=\frac{1-t^2}{1-2t\cos\theta+t^2},\qquad
A_x(\theta)=\int_0^xP_t(\theta)\,dt\quad(|x|<1).
$$

The classical disk Poisson identity is $h(t)=\int h(e^{i\theta})P_t(\theta)\,d\mu(\theta)$. In this setting it follows directly from

$$
P_t(\theta)=1+2\sum_{m\ge1}t^m\cos(m\theta)
$$

and the absolutely convergent Taylor series of $h$ on the circle: its $m$th analytic moment is $t^m$, including negative real $t$. Integrating on the compact segment between $0$ and $x$ is legitimate because $|t|\le|x|<1$. Together with Lemma 9.2 this gives the identity on the actual function $g$,

$$
g'(x)-\frac{g(ib)-g(-ib)}{2ib}
=\int_0^{2\pi}h(e^{i\theta})K_{x,b}(\theta)\,d\mu(\theta),\qquad
K_{x,b}=A_x-B_b.
$$

We prove $\int|K_{x,b}|\,d\mu\le1$ for every $|x|<1$. First let $0\le x<1$. Here $A_x\ge0$, and $\int A_x\,d\mu=x$ because each $P_t$ has mean one. By Lemma 9.2, $B_b\le0$ on the half-circle $\cos\theta\ge0$, so $K_{x,b}\ge0$ there.

On the other half-circle put $c=-\cos\theta\ge0$ and define

$$
A_1(\theta)=\int_0^1\frac{1-t^2}{1+2ct+t^2}\,dt.
$$

This is finite on that half-circle. Its integrand is nonincreasing in $t$: direct differentiation for general $\theta$ gives

$$
\frac{\partial P_t(\theta)}{\partial t}
=\frac{2[(1+t^2)\cos\theta-2t]}{(1-2t\cos\theta+t^2)^2}\le0
\quad(0\le t<1,\ \cos\theta\le0).
$$

The average of a nonincreasing function over $[0,x]$ is at least its average over $[0,1]$, so $A_x\ge xA_1$, also at $x=0$. Moreover,

$$
A_1\ge\int_0^1\frac{1-t^2}{(1+t)^2}\,dt
=2\log2-1\ge\frac{31}{81}>C\ge B_b\ge0.
$$

For the penultimate rational lower bound, the same logarithm series used in Lemma 9.2, now at $s=1/3$, gives $\log2\ge2(1/3+1/81)=56/81$. Therefore, writing $u_+=\max\{u,0\}$,

$$
(B_b-A_x)_+\le(1-x)B_b
\quad\text{on }\cos\theta\le0.
$$

Since this half-circle has $\mu$-measure $1/2$ and $0\le B_b\le C$, while the negative part of $K_{x,b}$ vanishes on the other half-circle, we obtain

$$
\begin{aligned}
\int|K_{x,b}|\,d\mu
&=\int K_{x,b}\,d\mu+2\int(-K_{x,b})_+\,d\mu\\
&\le x+2(1-x)\int_{\cos\theta\le0}B_b\,d\mu\\
&\le x+(1-x)C\le1.
\end{aligned}
$$

Here $\int K_{x,b}\,d\mu=x$ uses the zero mean of $B_b$. For $-1<x<0$, put $u=-x$. The identities $P_{-t}(\theta)=P_t(\pi-\theta)$ and $B_b(\pi-\theta)=-B_b(\theta)$ imply

$$
K_{-u,b}(\theta)=-K_{u,b}(\pi-\theta).
$$

The change of variable $\theta\mapsto\pi-\theta$ preserves circle measure, so the same integral bound follows. The integral representation and the triangle inequality now give, for every $|x|<1$,

$$
\left|g'(x)-\frac{g(ib)-g(-ib)}{2ib}\right|
\le\sup_{|z|=1}|g''(z)|\int|K_{x,b}|\,d\mu
\le\|g''\|_{\mathbb D}.
$$

Finally $g'$ is continuous on the closed interval, and the fixed slope is finite since $b>0$. Letting $x$ tend to either endpoint proves the assertion at $x=\pm1$. No boundary Poisson formula at $t=\pm1$ is required. The kernel of Lemma 9.2 already includes $b=1$, so this argument applies directly to the pair $(i,-i)$ as well. $\square$

**Lemma 9.4 (Horizontal displacement of a conjugate-pair slope).** For every admissible $a,b$ of Definition 9.1 and every entire $g$,

$$
|S_{a,b}(g)-S_{0,b}(g)|\le|a|\,\|g''\|_{\mathbb D}.
$$

Stance: repo-derived.

**Proof.** For real $s$ between $0$ and $a$, set $F(s)=[g(s+ib)-g(s-ib)]/(2ib)$. Since $g$ is entire, differentiation in $s$ and then integration on the vertical segment give

$$
F'(s)=\frac{g'(s+ib)-g'(s-ib)}{2ib}
=\frac1{2b}\int_{-b}^b g''(s+it)\,dt.
$$

Every point of this segment lies in the closed disk: $s^2+t^2\le a^2+b^2\le1$. Thus $|F'(s)|\le\|g''\|_{\mathbb D}$. Integrating on the segment from $0$ to $a$, with its orientation when $a<0$, proves the bound. All segment endpoints are included by continuity. $\square$

**Theorem 9.5 (Complete simple-conjugate-pair classification).** For every real $a,b$ with $b>0$ and $a^2+b^2\le1$, every $g\in\mathscr E_2(\mathbb D)$ and every real $x\in[-1,1]$,

$$
|g'(x)-(I_{a,b}g)'(x)|\le1+|a|.
$$

The exact original entire-function uniform supremum is

$$
E(a,b)=1+|a|=\frac12\|p_{a,b}'\|_{[-1,1]}.
$$

Consequently the equality region for equation (36) of Ostrovskii–Shcherbakov in the simple two-node case $(n,k)=(2,1)$ is the whole admissible upper closed half-disk $\{(a,b):b>0,\ a^2+b^2\le1\}$. In particular every nonreal unit-circle conjugate pair is included. Stance: repo-derived.

**Proof.** Admissibility implies $0<b\le1$, so Lemmas 9.3 and 9.4 yield

$$
\begin{aligned}
|g'(x)-S_{a,b}(g)|
&\le|g'(x)-S_{0,b}(g)|+|S_{0,b}(g)-S_{a,b}(g)|\\
&\le(1+|a|)\|g''\|_{\mathbb D}\le1+|a|.
\end{aligned}
$$

This holds for each actual entire $g$ and each $x$, hence bounds the two suprema in Definition 9.1 without exchanging a limit with either supremum. For the reverse inequality take the actual entire quadratic $g_0(z)=z^2/2$. It has $g_0''=1$, and

$$
S_{a,b}(g_0)=\frac{(a+ib)^2-(a-ib)^2}{4ib}=a,\qquad
T_{a,b,x}(g_0)=x-a.
$$

Its maximum absolute error is $1+|a|$, attained at $x=-1$ when $a\ge0$ and at $x=1$ when $a\le0$. At $a=0$ both endpoints attain it. Finally $p_{a,b}(z)=z^2-2az+a^2+b^2$, so $p_{a,b}'(x)/2=x-a$ and its half-norm has exactly that value. The proof used only $a^2+b^2\le1$ throughout, including equality, and never identified the two distinct nodes. $\square$

## 10. Mathematical correspondence and remaining pointwise questions

**Remark 10.1 (Inputs and the added inference).** The source correspondence is as follows.

| Mathematical input | Exact role |
| --- | --- |
| Ostrovskii–Shcherbakov, [arXiv:2508.13554v2, Section 6.2, Conjecture 6.3, equation (36)](https://arxiv.org/html/2508.13554v2#S6.SS2) | The entire complex-valued class, the closed disk, the real interval, the actual Lagrange interpolant, and the proposed uniform identity. Definition 9.1 specializes those objects with $n=2$, $k=1$ and two distinct nodes. The right side of (36) is $\|p_{a,b}'\|_I/2=1+|a|$. |
| The classical disk Poisson formula, equivalently the geometric Fourier expansion of $P_t$ | Only the boundary representation of $h(t)$ for $|t|<1$ in Lemma 9.3. Its needed scalar moments and convergence are derived there. The usual Poisson kernel is also the one defined in Mathlib's [Analysis/Complex/Poisson](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Complex/Poisson.lean). |
| The fundamental theorem of calculus for holomorphic functions along segments, Cauchy's coefficient estimate, geometric-series integration, and the integral triangle inequality | The slope identities, passage through Taylor series, elementary kernel bounds, and norm control in Lemmas 9.2–9.4. None of these classical inputs supplies the asserted interpolation bound by itself. |
| Theorems 4.1 and 5.1, Remark 4.4, and Propositions 8.2–8.4 with Corollary 8.5 | The exact all-degree Schur-ratio regions, the $73/60$ refutation, and the quartic pointwise separation, respectively. Their existing hypotheses and conclusions are retained; they are not premises of the uniform upper bound. |

The added mathematical inference is the signed boundary kernel $K_{x,b}$ with an explicitly bounded negative part on the whole real interval, combined with the displacement estimate for the actual slope. In particular Lemma 9.3 applies to the full entire-function class, with arbitrary complex coefficients. Its proof does not infer a norm estimate for that class from individual monomial estimates.

**Remark 10.2 (Pointwise and uniform statements have different scopes).** For $0<d\le1/2$, the grid of Section 8 has $a=1-d$, $b=\sqrt3\,d$. Theorem 9.5 therefore gives the exact uniform value

$$
E(1-d,\sqrt3\,d)=2-d,
$$

attained by the quadratic at $x=-1$. On the identical actual grid, Proposition 8.2 and Corollary 8.5 still give

$$
\sup_{t\ge2}|L_d(m_t)|=d,
\qquad
\sup_{g\in\mathscr E_2(\mathbb D)}|L_d(g)|
\ge d\sqrt{1+d^4/9}>d,
\qquad 1\notin\mathcal K_d.
$$

This pointwise strict inequality at $x=1$ is compatible with the uniform value $2-d$; it neither supplies nor refutes the uniform upper bound. Likewise Remark 4.4 remains a refutation of Conjecture 6.2 with value $73/60$ at its stated shifted grid. The sector classification of Theorem 4.1 remains an all-monomial statement, not a characterization of the uniform equality region of Theorem 9.5.

The source's Section 6.3, Proposition 6.2 asserts monomial maximization for a simple grid and a fixed point, and uses a compactness argument followed by an extreme-point assertion. The pointwise separation of Section 8 excludes that proposition on its displayed grids. Theorem 9.5 instead proves the analytic form of equation (36) directly; no compactness, extreme-point description, or asserted reduction to monomials from that section is a premise. The real-grid results of Kallioniemi, Howell and Shadrin, discussed in the source's Section 6.1 and in Remark 4.2, concern real interpolation nodes and are not premises for these nonreal pairs.

**Remark 10.3 (Multiplicity and parameter boundaries).** A pair $(a+ib,a-ib)$ with $b>0$ satisfies the source's Definition 6.1 directly: each nonreal conjugate occurs once, and each real number has multiplicity zero. This fact does not identify arbitrary lists satisfying conjugate membership with lists having equal multiplicities for nonreal conjugates. Conjugate membership alone imposes no such multiplicity equality; the two-node simple case has no multiplicity ambiguity.

The condition $b=0$ is outside Definition 9.1 and Theorem 9.5, irrespective of any confluent convention used for separate results on doubled real nodes. The classification includes all admissible points with $b>0$, so there is no remaining admissible subregion of simple pairs requiring negative witnesses. The cases $k=0$, larger numbers of nodes, and general grids in the original all-$n$, all-$k$ Conjecture 6.3 are not settled by this two-node derivative theorem.

**Open question 10.4 (Exact pointwise analytic error).** For each admissible $a,b$ and each fixed $x\in[-1,1]$, determine

$$
\sup_{g\in\mathscr E_2(\mathbb D)}
\left|g'(x)-\frac{g(a+ib)-g(a-ib)}{2ib}\right|,
$$

and hence the exact analytic Kallioniemi set of that pair. Theorem 9.5 determines the supremum of this quantity over the interval and supplies a quadratic attaining it at a far endpoint, but does not determine every pointwise value. In particular the exact pointwise supremum at $x=1$ on the grids $W_d$ is not identified by the quartic lower bound of Section 8.

## 追加锚（本行以下为增补区）

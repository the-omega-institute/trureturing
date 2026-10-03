# Exact lower bounds and quadratic contact at the Krasniqi boundary

## 1. The function and the exact boundary

**Definition 1.1 (Bernstein functions and the literal family).** A Bernstein function is a nonnegative smooth real function $f$ on $(0,\infty)$ such that $(-1)^n f^{(n+1)}(y)\ge0$ for every integer $n\ge0$ and every $y>0$. Write $\mathrm{BF}$ for this class. For $a>0$ and $0\le c<1$, define

$$
H_{a,c}(y)=\left(1+\frac1y\right)^{ay-c},\qquad y>0.
$$

With $b=-c$, the original parameterization is $F_{a,b}(x)=(1+a/x)^{x+b}$, and $F_{a,b}(ay)=H_{a,-b}(y)$. Define

$$
\alpha_* = \sup\{\alpha>0:H_{\alpha,0}\in\mathrm{BF}\},\qquad
A(b)=\sup\{a>0:H_{a,-b}\in\mathrm{BF}\}\quad(-1<b\le0).
$$

These definitions refer to the exact Bernstein property, without substituting numerical approximations for $\alpha_*$ or $A$. The family and parameterization are those of Krasniqi, arXiv:2609.28707v1, equations (1.1), (3.1), and Theorem 17.

**Definition 1.2 (Regularized density and its coefficients).** For $a>0$, $0\le c<1$, and $k=a+c<3$, put

$$
w_{a,c}(s)=\frac{\sin(\pi(as+c))}{\pi}
 \left(\frac{s}{1-s}\right)^{as+c},\qquad 0<s<1,
$$

$$
\begin{aligned}
q_0(a,c)&=1,\\
q_n(a,c)&=\frac1n\sum_{j=1}^n
 \left(\frac{aj}{j+1}+c\right)q_{n-j}(a,c)\quad(n\ge1),\\
q_1&=\frac a2+c,\qquad
q_2=\frac a3+\frac c2+\frac12\left(\frac a2+c\right)^2,\\
D_{a,c}(t)&=q_1+(q_1-q_2)t\\
&\quad+e^{-a}\int_0^1 w_{a,c}(s)
 \bigl(e^{(1-s)t}-1-(1-s)t\bigr)\,ds,\\
d_n(a,c)&=\sum_{j=0}^n(-1)^j\binom nj q_{j+1}(a,c)\quad(n\ge0).
\end{aligned}
$$

Both endpoint subtractions are part of the definition of $D$. The integral is an improper integral of the entire displayed product; the unsubtracted kernel need not be integrable. The associated Laplace density is $\Phi_{a,c}(t)=e^{a-t}D_{a,c}(t)$. These are Krasniqi's equations (3.5)--(3.8), (3.17), and (3.19). The same coefficient sequence has generating function

$$
\sum_{n=0}^\infty q_n(a,c)z^n
 =\exp\left(\sum_{j=1}^\infty
 \left(\frac{a}{j+1}+\frac cj\right)z^j\right),\qquad |z|<1.
$$

Indeed, differentiating this identity formally and comparing coefficients gives the displayed recurrence and $q_0=1$.

## 2. A uniform lower bound in the two-switch region

**Definition 2.1 (Admissible region and filtered density).** Let

$$
\begin{aligned}
\delta&=3\log3-2,\\
M_\delta(a,c)&=2(\delta a+4c)(5a+26c)-8(a+4c)^2
 -(\delta a+4c)^2(a+4c),\\
U(a,c)&=4(1-c)-(a-2+2c)^2.
\end{aligned}
$$

Define $\mathcal R$ by the simultaneous strict conditions

$$
1<a<\frac73,\qquad 0<c<1,\qquad 2<a+c<3,\qquad
M_\delta(a,c)>0,\qquad U(a,c)>0.
$$

For $(a,c)\in\mathcal R$, put

$$
r=\frac{a+c-2}{a},\qquad R=\frac{a+c-1}{a},\qquad
K_{a,c}(t)=D_{a,c}''(t)-(r+R)D_{a,c}'(t)+rR D_{a,c}(t).
$$

Then $0<r<R<1$. In particular, $R<1$ follows from $c<1$.

**Theorem 2.2 (Uniform positive lower bound).** For every real pair $(a,c)\in\mathcal R$ and every real $t\ge0$,

$$
K_{a,c}(t)\ge\frac{\rho}{a^2}>0,
\qquad \rho=\frac{6583}{11943936}.
$$

**Proof.** Write $D=D_{a,c}$ and

$$
h(x)=e^{-a}x^2w_{a,c}(1-x),\qquad 0<x<1.
$$

The sine factor is $\sin(\pi(k-ax))$. Its signs on $(0,r)$, $(r,R)$, and $(R,1)$ are respectively positive, negative, and positive. All remaining factors in $h$ are positive.

At the endpoints,

$$
h(x)=O(x^{2-k})\quad(x\downarrow0),\qquad
h(x)=O((1-x)^c)\quad(x\uparrow1).
$$

For the first estimate, division by $x^{2-k}$ leaves bounded factors $x^{ax}$, $(1-x)^{k-ax}$, and the sine factor. For the second estimate, division by $(1-x)^c$ leaves bounded factors $(1-x)^{a(1-x)}$, $x^{2-c-a(1-x)}$, and the sine factor. The variable-exponent factors converge to one. Since $2-k>-1$ and $c>-1$, $h\in L^1(0,1)$.

After the change of variable $x=1-s$, the regularized integral in $D$ is

$$
\int_0^1 h(x)\frac{e^{xt}-1-xt}{x^2}\,dx.
$$

For $t$ in a fixed bounded real interval, this quotient and its first derivative are uniformly bounded; this follows either from the exponential series or from Taylor's integral formula. For every derivative of order at least two, the integrand is $x^{n-2}h(x)e^{xt}$, dominated by a constant times $|h(x)|$. Thus differentiation under the integral is justified locally uniformly to every finite order, and

$$
D^{(n)}(t)=\int_0^1x^{n-2}h(x)e^{xt}\,dx\quad(n\ge2).
$$

Consequently, for every integer $n\ge2$,

$$
K^{(n)}(t)=\int_0^1(x-r)(x-R)x^{n-2}h(x)e^{xt}\,dx>0.
\tag{2.1}
$$

The quadratic factor has the same three signs as $h$. The product is strictly positive except at the two switch points, so its integral is strictly positive. This argument does not presume a sign for $K(0)$ or $K'(0)$.

The source coefficient identity $D^{(n)}(0)=d_n$ is Krasniqi's equations (3.17), (3.19), including $d_0=q_1$ and $d_1=q_1-q_2$. It is an intermediate analytic supplier for the following exact polynomial:

$$
\begin{aligned}
p_i(a,c)&=a^2d_{i+2}-a(2a+2c-3)d_{i+1}
 +(a+c-2)(a+c-1)d_i,\\
P_6(a,c,t)&=\sum_{i=0}^6p_i(a,c)\frac{t^i}{i!}.
\end{aligned}
\tag{2.2}
$$

Only $q_0,\ldots,q_9$ enter this definition, and $p_i=a^2K^{(i)}(0)$. The polynomial has coordinate degrees $(11,9,6)$ in $(a,c,t)$. Taylor's integral remainder, together with (2.1), gives

$$
a^2K(t)-P_6(a,c,t)
 =\frac{a^2}{6!}\int_0^t(t-u)^6K^{(7)}(u)\,du\ge0
 \quad(t\ge0).
\tag{2.3}
$$

We next establish the finite-interval lower bound by exact rational coefficients. Put

$$
\delta_0=\frac{1295836866004}{10^{12}},\qquad
\overline M(a,c)=M_{\delta_0}(a,c)+\frac1{10^9}.
$$

The positive series for $2\operatorname{arctanh}(1/2)$ gives

$$
\begin{aligned}
\log3&=L+E,\qquad
L=2\sum_{n=0}^{23}\frac{2^{-(2n+1)}}{2n+1},\\
0<E&<\frac{2\,2^{-49}}{49(1-1/4)}.
\end{aligned}
$$

The tail estimate follows by replacing every denominator after the first omitted term by $49$ and summing the resulting geometric series. Direct rational comparison gives

$$
\delta_0-10^{-12}<3L-2<\delta<3\left(L+
 \frac{2\,2^{-49}}{49(1-1/4)}\right)-2<\delta_0+10^{-12},
\qquad 1<\delta<\frac{13}{10}.
$$

On $1\le a\le7/3$, $0\le c\le1$, $1\le v\le13/10$,

$$
\begin{aligned}
\partial_vM_v&=2a(5a+26c)-2a(va+4c)(a+4c),\\
|\partial_vM_v|&\le
 2\frac73\left(5\frac73+26\right)
 +2\frac73\left(\frac{13}{10}\frac73+4\right)
 \left(\frac73+4\right)
 =\frac{51793}{135}<500.
\end{aligned}
$$

Both $\delta$ and $\delta_0$ lie in the specified $v$-interval. The mean value theorem yields

$$
M_\delta<M_{\delta_0}+5\cdot10^{-10}<\overline M.
\tag{2.4}
$$

In particular, $M_\delta>0$ implies $\overline M>0$. The direction of this relaxation is essential for exclusions.

Consider the closed rational rectangle

$$
B_0=[1,7/3]\times[0,1]\times[0,16].
$$

Its complete partition is specified in Appendix A. The coordinate labels $0,1,2$ mean $a,c,t$. Each pair $jL$ or $jR$ replaces the current closed coordinate interval $[\ell,u]$ by $[\ell,(\ell+u)/2]$ or $[(\ell+u)/2,u]$. Thus a path determines a closed box, and both children include their shared face. Every internal node has one coordinate label and both children; no terminal path is a prefix of another terminal path. The 238 terminal boxes, at maximum depth 17, cover all of $B_0$, including its external and internal faces.

For a polynomial on a box, substitute $a=\ell_0+(u_0-\ell_0)v_0$, $c=\ell_1+(u_1-\ell_1)v_1$, and $t=\ell_2+(u_2-\ell_2)v_2$. If the resulting power coefficients are $C_{j_0j_1j_2}$ and its coordinate degrees are $n_0,n_1,n_2$, its tensor Bernstein coefficients are

$$
b_{i_0i_1i_2}=
 \sum_{j_0=0}^{i_0}\sum_{j_1=0}^{i_1}\sum_{j_2=0}^{i_2}
 C_{j_0j_1j_2}\prod_{\nu=0}^2
 \frac{\binom{i_\nu}{j_\nu}}{\binom{n_\nu}{j_\nu}}.
\tag{2.5}
$$

Zero power coefficients are included. The identity

$$
v^j=\sum_{i=j}^n\frac{\binom ij}{\binom nj}
 \binom ni v^i(1-v)^{n-i}\quad(0\le j\le n)
$$

proves this change of basis. On $[0,1]^3$, the tensor Bernstein weights are nonnegative and sum to one. Every polynomial value therefore lies between its smallest and largest Bernstein coefficients.

The exact rational coefficient comparisons for the paths of Appendix A have the following values. For each of the 134 boxes marked $+$, every coefficient of $P_6$ is at least $\rho$, and the minimum over all these coefficients is exactly $\rho$. For each of the other 104 boxes, every coefficient of the expression indicated by its label is strictly negative: 87 boxes use $\overline M$, one uses $U$, and 16 use $a+c-2$. Such a box contains no point of $\mathcal R$, by (2.4) and the defining strict inequalities. All comparisons use (2.2), the rational recurrence in Definition 1.2, and (2.5); no precomputed polynomial coefficients enter their specification. It follows that

$$
P_6(a,c,t)\ge\rho\quad((a,c)\in\mathcal R,\ 0\le t\le16).
\tag{2.6}
$$

For the polynomial $T(a,c)=\partial_tP_6(a,c,16)$, the same coefficient formula on the entire parameter rectangle $[1,7/3]\times[0,1]$ gives

$$
\min b_{ij}(T)=\eta=\frac{45599851}{571536000}>0.
\tag{2.7}
$$

This is a single-box certificate; the $t$ coordinate is absent from $T$.

Finally, (2.1) implies the explicit identity

$$
\partial_t^2P_6(a,c,t)
 =a^2\sum_{j=0}^4K^{(j+2)}(0)\frac{t^j}{j!}>0\quad(t\ge0).
$$

Hence $\partial_tP_6$ is strictly increasing on $[0,\infty)$. By (2.7), $P_6$ is increasing on $[16,\infty)$, and (2.6) extends to every $t\ge0$. Combining this with (2.3) proves the claimed lower bound. $\square$

## 3. Unique quadratic contact at every interior boundary point

**Theorem 3.1 (Exact boundary-contact consequence).** For every real $b$ with $-1<b<0$, there exists exactly one real $t_b>0$ satisfying

$$
D_{A(b),-b}(t_b)=0.
$$

At this point,

$$
D_t(A(b),-b,t_b)=0,\qquad D_{tt}(A(b),-b,t_b)>0.
$$

Thus the contact has exactly order two, as in Krasniqi's Conjecture 23.

**Proof.** Put $a=A(b)$ and $c=-b$, so $0<c<1$. We first identify the published facts supplying the exact boundary parameters. Krasniqi's Theorem 17 states that the Bernstein region is precisely $0<a\le A(b)$ and that the supremum defining $A(b)$ is attained. It also gives

$$
0<a<\alpha_*,\qquad D_{a,c}(t)\ge0\quad(t\ge0),
$$

and a nonempty finite set of positive zeros of $D_{a,c}$. Proposition 6 supplies $\alpha_*<7/3$. Proposition 2 gives, at every Bernstein pair,

$$
a+c<K_0<3,\qquad M_\delta(a,c)>0,\qquad
 a<2(1-c)+2\sqrt{1-c},
\quad K_0=\frac{10\delta-8}{\delta^2}.
\tag{3.1}
$$

The strict bounds come from its equations (2.11)--(2.14); Proposition 3 supplies the regularized density and its Bernstein criterion. These are facts about the original family, not extra boundary-membership assumptions. No uniqueness or nondegeneracy statement is supplied by them.

Since $D$ is smooth and nonnegative, Fermat's theorem gives $D'(u)=0$ at every positive zero $u$. We distinguish the number of sign switches of $h(x)=e^{-a}x^2w_{a,c}(1-x)$.

If $k=a+c\le1$, then $0<k-ax<1$ for $0<x<1$, so $h(x)>0$ and

$$
D''(t)=\int_0^1h(x)e^{xt}\,dx>0.
$$

Thus $D'$ is strictly increasing. Two positive contacts would give two zeros of $D'$, which is impossible. Existence supplies exactly one contact, and its curvature is positive.

If $1<k\le2$, put $r_1=(k-1)/a$. Since $c<1$, $0<r_1<1$. The signs of $h$ are negative on $(0,r_1)$ and positive on $(r_1,1)$, including the case $k=2$. Define

$$
G(t)=e^{-r_1t}D''(t).
$$

The endpoint estimates and dominated differentiation used in Theorem 2.2 also apply here. They yield

$$
G'(t)=e^{-r_1t}\int_0^1(x-r_1)h(x)e^{xt}\,dx>0.
$$

Hence $G$ is strictly increasing, and $D''$ has at most one zero. If $u<v$ were positive zeros of $D$, Rolle's theorem would give $z\in(u,v)$ with $D'(z)=0$. Fermat gives $D'(u)=D'(v)=0$. Applying Rolle to $D'$ on $[u,z]$ and $[z,v]$ gives two distinct zeros of $D''$, a contradiction.

At the unique contact $u$, suppose $D''(u)\le0$. For every $0<t<u$, strict increase of $G$ gives $G(t)<G(u)\le0$, hence $D''(t)<0$. On an interval ending at $u$, $D'$ is strictly decreasing toward $D'(u)=0$, so $D'(t)>0$ before $u$. The mean value theorem then gives $D(t)<D(u)=0$ for $t$ sufficiently close to $u$ from the left. This contradicts nonnegativity. Thus $D''(u)>0$. Only the sign-switch integral, Fermat, Rolle, and the mean value theorem are needed in this case.

It remains to consider $2<k<3$. Since $c<1$, this implies $a>1$. Also

$$
a-2+2c=(k-2)+c>0.
$$

The square-root bound in (3.1) therefore gives, with the correct squaring direction,

$$
a-2+2c<2\sqrt{1-c},\qquad U(a,c)>0.
$$

Together with $a<\alpha_*<7/3$ and $M_\delta>0$, these conditions place the actual attained boundary pair in $\mathcal R$. Theorem 2.2 applies for every $t\ge0$.

At any contact $u$, $D(u)=D'(u)=0$, so

$$
D''(u)=K(u)\ge\frac\rho{a^2}>0.
$$

Moreover, with $r=(k-2)/a$ and $R=(k-1)/a$, define

$$
J(t)=e^{-Rt}\bigl(D'(t)-rD(t)\bigr).
$$

The product rule gives

$$
J'(t)=e^{-Rt}\bigl(D''(t)-(r+R)D'(t)+rRD(t)\bigr)
 =e^{-Rt}K(t)>0.
$$

Every contact is a zero of $J$. Strict monotonicity permits at most one, and the published existence result supplies one. The positive second derivative and $D(u)=D'(u)=0$ show by Taylor's formula that this zero has exactly order two. The three cases exhaust every $-1<b<0$. $\square$

## 4. Appendix A: complete rational partition

**Definition 4.1 (Terminal path data).** The root is $B_0$ from Theorem 2.2. Paths use the successive closed bisections defined there. A terminal label $+$ requires the Bernstein lower bound $P_6\ge\rho$; labels $M$, $U$, and $k$ require a strictly negative Bernstein upper bound for $\overline M$, $U$, and $a+c-2$, respectively. The complete terminal list is the following. For the tail polynomial $T$, the sole terminal path is the empty path with a positive lower bound $\eta$ on the root parameter rectangle.

| Path | Label |
| --- | --- |
| $\mathtt{0L1L2L0L}$ | $k$ |
| $\mathtt{0L1L2L0R1L}$ | $k$ |
| $\mathtt{0L1L2L0R1R2L0L1L}$ | $k$ |
| $\mathtt{0L1L2L0R1R2L0L1R2L0L}$ | $k$ |
| $\mathtt{0L1L2L0R1R2L0L1R2L0R1L}$ | $k$ |
| $\mathtt{0L1L2L0R1R2L0L1R2L0R1R}$ | $+$ |
| $\mathtt{0L1L2L0R1R2L0L1R2R0L}$ | $k$ |
| $\mathtt{0L1L2L0R1R2L0L1R2R0R}$ | $+$ |
| $\mathtt{0L1L2L0R1R2L0R1L2L0L}$ | $k$ |
| $\mathtt{0L1L2L0R1R2L0R1L2L0R}$ | $+$ |
| $\mathtt{0L1L2L0R1R2L0R1L2R0L}$ | $k$ |
| $\mathtt{0L1L2L0R1R2L0R1L2R0R}$ | $+$ |
| $\mathtt{0L1L2L0R1R2L0R1R}$ | $+$ |
| $\mathtt{0L1L2L0R1R2R}$ | $+$ |
| $\mathtt{0L1L2R}$ | $+$ |
| $\mathtt{0L1R2L0L1L2L0L}$ | $k$ |
| $\mathtt{0L1R2L0L1L2L0R1L}$ | $k$ |
| $\mathtt{0L1R2L0L1L2L0R1R2L0L1L}$ | $k$ |
| $\mathtt{0L1R2L0L1L2L0R1R2L0L1R}$ | $+$ |
| $\mathtt{0L1R2L0L1L2L0R1R2L0R}$ | $+$ |
| $\mathtt{0L1R2L0L1L2L0R1R2R}$ | $+$ |
| $\mathtt{0L1R2L0L1L2R0L}$ | $k$ |
| $\mathtt{0L1R2L0L1L2R0R}$ | $+$ |
| $\mathtt{0L1R2L0L1R2L0L1L2L0L}$ | $k$ |
| $\mathtt{0L1R2L0L1R2L0L1L2L0R}$ | $+$ |
| $\mathtt{0L1R2L0L1R2L0L1L2R0L}$ | $k$ |
| $\mathtt{0L1R2L0L1R2L0L1L2R0R}$ | $+$ |
| $\mathtt{0L1R2L0L1R2L0L1R}$ | $U$ |
| $\mathtt{0L1R2L0L1R2L0R}$ | $+$ |
| $\mathtt{0L1R2L0L1R2R}$ | $+$ |
| $\mathtt{0L1R2L0R1L}$ | $+$ |
| $\mathtt{0L1R2L0R1R2L}$ | $+$ |
| $\mathtt{0L1R2L0R1R2R0L1L}$ | $+$ |
| $\mathtt{0L1R2L0R1R2R0L1R}$ | $M$ |
| $\mathtt{0L1R2L0R1R2R0R}$ | $M$ |
| $\mathtt{0L1R2R0L}$ | $+$ |
| $\mathtt{0L1R2R0R1L2L0L}$ | $+$ |
| $\mathtt{0L1R2R0R1L2L0R1L}$ | $+$ |
| $\mathtt{0L1R2R0R1L2L0R1R2L0L}$ | $+$ |
| $\mathtt{0L1R2R0R1L2L0R1R2L0R1L}$ | $+$ |
| $\mathtt{0L1R2R0R1L2L0R1R2L0R1R}$ | $M$ |
| $\mathtt{0L1R2R0R1L2L0R1R2R0L}$ | $+$ |
| $\mathtt{0L1R2R0R1L2L0R1R2R0R1L}$ | $+$ |
| $\mathtt{0L1R2R0R1L2L0R1R2R0R1R}$ | $M$ |
| $\mathtt{0L1R2R0R1L2R}$ | $+$ |
| $\mathtt{0L1R2R0R1R2L0L1L}$ | $+$ |
| $\mathtt{0L1R2R0R1R2L0L1R}$ | $M$ |
| $\mathtt{0L1R2R0R1R2L0R}$ | $M$ |
| $\mathtt{0L1R2R0R1R2R0L1L}$ | $+$ |
| $\mathtt{0L1R2R0R1R2R0L1R}$ | $M$ |
| $\mathtt{0L1R2R0R1R2R0R}$ | $M$ |
| $\mathtt{0R1L2L0L1L2L0L1L}$ | $k$ |
| $\mathtt{0R1L2L0L1L2L0L1R2L0L1L}$ | $k$ |
| $\mathtt{0R1L2L0L1L2L0L1R2L0L1R}$ | $+$ |
| $\mathtt{0R1L2L0L1L2L0L1R2L0R}$ | $+$ |
| $\mathtt{0R1L2L0L1L2L0L1R2R}$ | $+$ |
| $\mathtt{0R1L2L0L1L2L0R}$ | $+$ |
| $\mathtt{0R1L2L0L1L2R}$ | $+$ |
| $\mathtt{0R1L2L0L1R}$ | $+$ |
| $\mathtt{0R1L2L0R1L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0L1L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0L1R2L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0L1R2R0L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0L1R2R0R1L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0L1R2R0R1R2L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0L1R2R0R1R2R0L1L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0L1R2R0R1R2R0L1R}$ | $M$ |
| $\mathtt{0R1L2L0R1R2R0L1R2R0R1R2R0R}$ | $M$ |
| $\mathtt{0R1L2L0R1R2R0R1L2L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1L2R0L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1L2R0R1L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1L2R0R1R2L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1L2R0R1R2R0L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1L2R0R1R2R0R1L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1L2R0R1R2R0R1R2L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1L2R0R1R2R0R1R2R0L1L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1L2R0R1R2R0R1R2R0L1R}$ | $M$ |
| $\mathtt{0R1L2L0R1R2R0R1L2R0R1R2R0R1R2R0R}$ | $M$ |
| $\mathtt{0R1L2L0R1R2R0R1R2L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1R2R0L1L2L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1R2R0L1L2R0L1L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1R2R0L1L2R0L1R2L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1R2R0L1L2R0L1R2R0L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1R2R0L1L2R0L1R2R0R}$ | $M$ |
| $\mathtt{0R1L2L0R1R2R0R1R2R0L1L2R0R1L}$ | $+$ |
| $\mathtt{0R1L2L0R1R2R0R1R2R0L1L2R0R1R}$ | $M$ |
| $\mathtt{0R1L2L0R1R2R0R1R2R0L1R}$ | $M$ |
| $\mathtt{0R1L2L0R1R2R0R1R2R0R}$ | $M$ |
| $\mathtt{0R1L2R0L}$ | $+$ |
| $\mathtt{0R1L2R0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0L1R2L0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0L1R2L0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0L1R2L0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0L1R2R0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0L1R2R0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0L1R2R0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1R2L0L1L2L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1R2L0L1L2R0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1R2L0L1L2R0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1R2L0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1R2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1R2R0L1L2L0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1R2R0L1L2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1R2R0L1L2R}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1R2R0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2L0R1R2R0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0L1R2L0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0L1R2L0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0L1R2L0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0L1R2R}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0R1R2L0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0R1R2L0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0R1R2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0R1R2R0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0R1R2R0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0L1R2R0R1R2R0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2L0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2L0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2L0R1R2L0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2L0R1R2L0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2L0R1R2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2L0R1R2R0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2L0R1R2R0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2L0R1R2R0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2R0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2R0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2R0R1R2L0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2R0R1R2L0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2R0R1R2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2R0R1R2R0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2R0R1R2R0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1L2L0R1R2R0R1R2R0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1L2R0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2R0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2R0R1R2L0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2R0R1R2L0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2R0R1R2L0R1R2L0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2R0R1R2L0R1R2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1L2R0R1R2L0R1R2R}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1L2R0R1R2R}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0L1R2L0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0L1R2L0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0L1R2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0L1R2R0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0L1R2R0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0L1R2R0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0R1L2L0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0R1L2L0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0R1L2L0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0R1L2R0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0R1L2R0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0R1L2R0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2L0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0L1R2L0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0L1R2L0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0L1R2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0L1R2R0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0L1R2R0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0L1R2R0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0R1L2L0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0R1L2L0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0R1L2L0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0R1L2R0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0R1L2R0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0R1L2R0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1L2R0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0L1L2L0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0L1L2L0L1R2L0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0L1L2L0L1R2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0L1L2L0L1R2R}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0L1L2L0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0L1L2L0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0L1L2R0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0L1L2R0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0L1L2R0R1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2L0R1R2R0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2R0L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2R0R1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2R0R1R2L0L1L}$ | $+$ |
| $\mathtt{0R1L2R0R1R2R0R1R2L0L1R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2R0R1R2L0R}$ | $M$ |
| $\mathtt{0R1L2R0R1R2R0R1R2R}$ | $+$ |
| $\mathtt{0R1R2L0L1L2L}$ | $+$ |
| $\mathtt{0R1R2L0L1L2R0L1L}$ | $+$ |
| $\mathtt{0R1R2L0L1L2R0L1R}$ | $M$ |
| $\mathtt{0R1R2L0L1L2R0R1L2L}$ | $+$ |
| $\mathtt{0R1R2L0L1L2R0R1L2R0L1L}$ | $+$ |
| $\mathtt{0R1R2L0L1L2R0R1L2R0L1R}$ | $M$ |
| $\mathtt{0R1R2L0L1L2R0R1L2R0R1L2L}$ | $+$ |
| $\mathtt{0R1R2L0L1L2R0R1L2R0R1L2R0L}$ | $+$ |
| $\mathtt{0R1R2L0L1L2R0R1L2R0R1L2R0R}$ | $M$ |
| $\mathtt{0R1R2L0L1L2R0R1L2R0R1R}$ | $M$ |
| $\mathtt{0R1R2L0L1L2R0R1R}$ | $M$ |
| $\mathtt{0R1R2L0L1R}$ | $M$ |
| $\mathtt{0R1R2L0R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0L1L}$ | $+$ |
| $\mathtt{0R1R2R0L1L2L0L1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2L0L1L}$ | $+$ |
| $\mathtt{0R1R2R0L1L2L0R1L2L0L1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2L0R1L2L0L1L}$ | $+$ |
| $\mathtt{0R1R2R0L1L2L0R1L2L0R1L2L0L1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2L0R1L2L0R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2L0R1L2R0L1L}$ | $+$ |
| $\mathtt{0R1R2R0L1L2L0R1L2L0R1L2R0L1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2L0R1L2R0R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2L0R1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2R0L1L}$ | $+$ |
| $\mathtt{0R1R2R0L1L2L0R1L2R0L1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2R0R1L2L0L1L}$ | $+$ |
| $\mathtt{0R1R2R0L1L2L0R1L2R0R1L2L0L1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2R0R1L2L0R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2R0R1L2R0L}$ | $+$ |
| $\mathtt{0R1R2R0L1L2L0R1L2R0R1L2R0R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1L2R0R1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2L0R1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2R0L1L}$ | $+$ |
| $\mathtt{0R1R2R0L1L2R0L1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2R0R1L2L0L1L}$ | $+$ |
| $\mathtt{0R1R2R0L1L2R0R1L2L0L1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2R0R1L2L0R1L}$ | $+$ |
| $\mathtt{0R1R2R0L1L2R0R1L2L0R1R}$ | $M$ |
| $\mathtt{0R1R2R0L1L2R0R1L2R}$ | $+$ |
| $\mathtt{0R1R2R0L1L2R0R1R}$ | $M$ |
| $\mathtt{0R1R2R0L1R}$ | $M$ |
| $\mathtt{0R1R2R0R}$ | $M$ |

## 追加锚（本行以下为增补区）

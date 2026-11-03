# Analytic variable exponents obstructing the Sobolev Hornich–Hlawka inequality

## 1. Modulars, derivatives and the two norms

**Definition 1.1 (Lebesgue measure and the Luxemburg norm).** Let $I=(0,1)$ carry ordinary Lebesgue measure $dt$, without an additional weight or normalization. All functions and vector spaces are real, and measurable functions are identified when equal almost everywhere. Let $p:I\to(1,\infty)$ be measurable with

$$
1<p_-:=\mathop{\rm ess\,inf}_{I}p
\le p(t)\le p_+:=\mathop{\rm ess\,sup}_{I}p<\infty
\quad\text{almost everywhere}.
$$

For a measurable function $u$ and $\lambda>0$ put

$$
\rho_p(u)=\int_I |u(t)|^{p(t)}\,dt,
\qquad
\rho_p(u/\lambda)=\int_I\left|\frac{u(t)}{\lambda}\right|^{p(t)}\,dt.
\tag{1.1}
$$

The integral may have value $+\infty$. Define

$$
\begin{aligned}
L^{p(\cdot)}(I)
&=\{u:\rho_p(u/\lambda)<\infty\text{ for some }\lambda>0\},\\
\|u\|_{p(\cdot)}
&=\inf\{\lambda>0:\rho_p(u/\lambda)\le1\}.
\end{aligned}
\tag{1.2}
$$

The scaled finite-modular condition in (1.2) is equivalent to existence of a scale with modular at most one: if a finite modular exceeds one, enlarging the scale by a factor $a\ge1$ reduces the modular by at least the factor $a^{-p_-}$. For a nonzero member the norm is the unique positive scale with modular one. The standard unit-level fact, in the continuous-exponent setting used below, is also stated in Goodrich–Nakhl, *Luxemburg norm localisation for nonlocal differential equations in variable-exponent Lebesgue spaces*, [DOI 10.1007/s11784-026-01321-8](https://doi.org/10.1007/s11784-026-01321-8), §2.1, Lemma 2.1. Removing or adjoining the endpoints of $I$ has no effect on these integrals.

**Definition 1.2 (Weak derivatives and Sobolev norms).** For an integer $k\ge0$, let

$$
W^{k,p(\cdot)}(I)
=\{u\in L^{p(\cdot)}(I):D^ju\in L^{p(\cdot)}(I),\ 1\le j\le k\}.
\tag{1.3}
$$

Here $D^0u=u$, and $D^ju=v$ means the distributional identity

$$
\int_Iu(t)\varphi^{(j)}(t)\,dt
=(-1)^j\int_Iv(t)\varphi(t)\,dt
\quad\text{for every }\varphi\in C_c^\infty(I).
\tag{1.4}
$$

The functions in (1.3) are integrable: at any finite-modular scale, $|u(t)|/\lambda\le1+|u(t)/\lambda|^{p(t)}$. In particular (1.4) is well defined. On this same vector space define the derivative-sum norm $S_k$ and the joint derivative-modular Luxemburg norm $J_k$ by

$$
\begin{aligned}
S_k(u)&=\sum_{j=0}^k\|D^ju\|_{p(\cdot)},\\
\mathcal R_{k,p}(u/\lambda)
&=\sum_{j=0}^k\int_I\left|\frac{D^ju(t)}{\lambda}\right|^{p(t)}dt,\\
J_k(u)&=\inf\{\lambda>0:\mathcal R_{k,p}(u/\lambda)\le1\}.
\end{aligned}
\tag{1.5}
$$

In $J_k$ the sum is outside the individual powers inside the integrals; it is not the Luxemburg norm of the pointwise Euclidean length of the derivative vector. The two zero-boundary spaces mean precisely

$$
\begin{aligned}
W^{k,p(\cdot)}_{0,S}(I)
&=\overline{C_c^\infty(I)}^{\ S_k}\ \text{in }W^{k,p(\cdot)}(I),\\
W^{k,p(\cdot)}_{0,J}(I)
&=\overline{C_c^\infty(I)}^{\ J_k}\ \text{in }W^{k,p(\cdot)}(I).
\end{aligned}
\tag{1.6}
$$

No trace characterization is part of this definition. At a constant exponent $p(t)=s$, the joint norm is exactly

$$
J_k(u)=\left(\sum_{j=0}^k\int_I|D^ju(t)|^sdt\right)^{1/s}.
\tag{1.7}
$$

Formula (1.7) is the printed Sobolev norm preceding Theorem 3 in Marinescu–Niculescu, [*A survey of the Hornich-Hlawka inequality*, arXiv:2407.03278v1](https://arxiv.org/pdf/2407.03278v1), §3, pp. 5–6, and [*A New Look at the Hornich-Hlawka Inequality*, Results Math. 80, 149, DOI 10.1007/s00025-025-02464-9](https://doi.org/10.1007/s00025-025-02464-9), §3, pp. 6–7. Their Problem 4 asks: “Which Sobolev spaces $W^{k,p(\cdot)}(0,1)$ with a variable exponent $p(\cdot):(0,1)\to[1,2]$ verify the Hornich-Hlawka inequality?” Its surrounding setup has positive integer $k$. The question does not separately prescribe both conventions in (1.5); each convention is fixed here by its formula.

**Definition 1.3 (Defect).** For a norm $N$ on a real vector space define

$$
\begin{aligned}
\Delta_N(f,g,h)
={}&N(f+g)+N(g+h)+N(h+f)\\
&-N(f)-N(g)-N(h)-N(f+g+h).
\end{aligned}
\tag{1.8}
$$

The Hornich–Hlawka inequality for $N$ is the assertion $\Delta_N(f,g,h)\le0$ for every triple. A positive defect on a subspace is also a positive defect in any ambient space carrying the restricted norm.

## 2. One analytic exponent and simultaneous counterexamples at every order

**Theorem 2.1 (Quantitative analytic obstruction on the original interval).** For every real $0<\delta<1$ define

$$
\begin{aligned}
q&=1+\delta,&
c&=4^{-1/\delta},&
\varepsilon&=\min\{\delta/2,c/24\},&
r&=1+\varepsilon,\\
p_\delta(t)&=r+(q-r)\sin^2\bigl(\pi(t-1/3)\bigr),\qquad t\in I.
\end{aligned}
\tag{2.1}
$$

Then $p_\delta$ is real analytic and nonconstant, and

$$
1<r\le p_\delta(t)\le q<2,
\qquad
\sup_{t\in I}|p_\delta(t)-1|=\delta.
\tag{2.2}
$$

For this single exponent, for every integer $k\ge0$ there are real functions $f,g,h\in C_c^\infty(I)$ such that the same triple satisfies

$$
\Delta_{S_k}(f,g,h)>\frac c4,
\qquad
\Delta_{J_k}(f,g,h)>\frac c4.
\tag{2.3}
$$

Here both norms use $p=p_\delta$ in (1.5). Consequently the ordinary space $W^{k,p_\delta(\cdot)}(I)$ fails the inequality for each of these two specified norms, and each closure space in (1.6) fails it with its specified norm. The exponent in (2.1) is independent of $k$; the triple may depend on both $\delta$ and $k$.

Proof. Since $0<\varepsilon\le\delta/2$, one has $1<r<q<2$. The minimum $r$ is attained at $a=1/3$ and the maximum $q$ at $b=5/6$. These observations prove (2.2), including the exact supremum, and prove analyticity and nonconstancy.

We use the convex-modular gauge and unit-level properties in (1.2), also for the disjoint union of $k+1$ copies of $I$ with counting measure on the copy index. On that union, $u\mapsto(D^ju)_{j=0}^k$ pulls the Luxemburg norm back to $J_k$. Thus $J_k$ is a norm; $D^0u=u$ makes the map injective. Likewise $S_k$ is a sum of norms. These are the usual convex-gauge facts: for admissible positive scales $A,B$, convexity of $z\mapsto|z|^{p(t)}$ applied with weights $A/(A+B),B/(A+B)$ gives the triangle inequality at scale $A+B$, and taking infima gives the norm inequality. Homogeneity follows by replacing the scale by its ratio with the absolute scalar. If a function is nonzero on a set of positive measure, the modular tends to infinity as the scale decreases to zero, which gives positive definiteness.

For completeness, the unit-level use here follows from continuity and strict decrease in $\lambda$ of the modular of a nonzero member. Boundedness of $p$ supplies an integrable bound on each compact interval of positive scales from any one finite modular. The limit at infinity is zero; a set of positive measure on which $|u|$ is bounded below gives the limit infinity at zero. The same reasoning applies to the finite sum of derivative modulars. These standard facts are used only as gauge and limit tools.

The finite-dimensional sign configuration is the one in the endpoint Luxemburg example of [Marinescu–Niculescu's variable-exponent problem dossier](../../../Problems/marinescu-niculescu-2024-variable-exponent-hornich-hlawka.md) and its [complete endpoint result](https://github.com/the-omega-institute/trureturing/blob/fe7b34d6b30cf7ef13938bcf35fef00afc8dbd1a/D5/S3/Geometry/VariableExponentHornichHlawka.lean), with the matching [mathematical exposition](https://github.com/the-omega-institute/trureturing/blob/fe7b34d6b30cf7ef13938bcf35fef00afc8dbd1a/Blueprint/D5/S3/Geometry/VariableExponentHornichHlawka.md). That supplied endpoint uses the modular $|u_1|+|u_2|+u_3^2$ and its gauge

$$
N_{1,2}(u)=\frac{|u_1|+|u_2|+
\sqrt{(|u_1|+|u_2|)^2+4u_3^2}}2.
\tag{2.4}
$$

Its vectors $(0,1,1/2),(0,-1,1/2),(-1,0,-1/2)$ have pair-sum norms $1,2,2$, while the three individual norms and the triple-sum norm are all $(1+\sqrt2)/2$. Its defect is therefore $3-2\sqrt2>0$. We reuse this configuration and its mixed-power interpretation as the endpoint input. The powers, coefficient and localization needed for (2.1)–(2.3) are as follows.

Define the mixed modular and its gauge on $\mathbb R^3$ by

$$
M_{r,q}(u)=|u_1|^r+|u_2|^r+|u_3|^q,
\qquad
N_{r,q}(u)=\inf\{\lambda>0:M_{r,q}(u/\lambda)\le1\}.
\tag{2.5}
$$

It is again a convex-modular norm, and its nonzero vectors have a strictly decreasing continuous unit-level function. With the coefficient $c$ in (2.1) take

$$
x=(0,1,c),\qquad y=(0,-1,c),\qquad z=(-1,0,-c).
\tag{2.6}
$$

Their pair sums and total sum are

$$
\begin{aligned}
x+y&=(0,0,2c),&y+z&=(-1,-1,0),\\
z+x&=(-1,1,0),&x+y+z&=(-1,0,c).
\end{aligned}
\tag{2.7}
$$

All four norms $N_{r,q}(x),N_{r,q}(y),N_{r,q}(z),N_{r,q}(x+y+z)$ equal the positive root $A$ of

$$
A^{-r}+c^qA^{-q}=1.
\tag{2.8}
$$

The other three norms are, respectively, $2c,2^{1/r},2^{1/r}$. Here $c^{q-1}=1/4$, so $c^q=c/4$. At $L=1+c/4>1$, both powers are at least one and

$$
L^{-r}+c^qL^{-q}\le\frac{1+c^q}{L}=1.
$$

Thus $A\le1+c/4$. For $r=1+\varepsilon$, the tangent-line bound for the exponential gives

$$
\begin{aligned}
2^{1/r}
&=2\exp\left(-\frac{\varepsilon}{1+\varepsilon}\log2\right)\\
&\ge2\left(1-\frac{\varepsilon}{1+\varepsilon}\log2\right)
\ge2-2\varepsilon.
\end{aligned}
$$

Using $\varepsilon\le c/24$ now yields the quantitative mixed-power defect

$$
\begin{aligned}
D&:=\Delta_{N_{r,q}}(x,y,z)
=2c+2\,2^{1/r}-4A\\
&\ge2c+4-4\varepsilon-4(1+c/4)
=c-4\varepsilon\ge\frac{5c}{6}.
\end{aligned}
\tag{2.9}
$$

We next realize these seven mixed-power norms as limits of both Sobolev norms on the original interval. Fix an integer $k\ge0$ and choose a nonzero real $\psi\in C_c^\infty((-1,1))$, extended by zero to $\mathbb R$. For $s\in\{r,q\}$ put

$$
B_s=\left(\int_{-1}^1|\psi^{(k)}(v)|^s\,dv\right)^{1/s},
\qquad
\psi_s=\psi/B_s.
\tag{2.10}
$$

These constants are positive. For $k=0$ this is immediate; for $k\ge1$, an identically zero $k$th derivative would make $\psi$ a polynomial of degree less than $k$, and a compactly supported polynomial is zero. In particular

$$
\int_{-1}^1|\psi_s^{(k)}(v)|^s\,dv=1.
\tag{2.11}
$$

For $0<\eta<1/48$ set

$$
\begin{aligned}
a_{1,\eta}&=a-3\eta,&a_{2,\eta}&=a+3\eta,&a_{3,\eta}&=b,\\
s_1&=r,&s_2&=r,&s_3&=q,\\
F_{i,\eta}(t)&=\eta^{\,k-1/s_i}
\psi_{s_i}\left(\frac{t-a_{i,\eta}}\eta\right),\qquad i=1,2,3,\\
T_\eta u&=\sum_{i=1}^3u_iF_{i,\eta}.
\end{aligned}
\tag{2.12}
$$

The three supports lie in pairwise disjoint intervals compactly contained in $I$. For the first two, these intervals lie in $[a-4\eta,a+4\eta]$, and the third lies in $[b-\eta,b+\eta]$. Thus $T_\eta$ is a linear map from $\mathbb R^3$ into $C_c^\infty(I)$. Its derivatives are classical and also satisfy (1.4).

Write

$$
p_{i,\eta}(v)=p_\delta(a_{i,\eta}+\eta v),\qquad -1\le v\le1.
$$

The trigonometric formula at $a$ and $b$, together with $|\sin w|\le|w|$, gives

$$
\begin{aligned}
|p_{i,\eta}(v)-s_i|&\le C_\delta\eta^2\quad(i=1,2,3),\\
C_\delta&=16\pi^2(q-r).
\end{aligned}
\tag{2.13}
$$

Indeed the arguments near $a$ are $\pi\eta(v-3)$ and $\pi\eta(v+3)$; near $b$ one has $\sin^2(\pi/2+\pi\eta v)=1-\sin^2(\pi\eta v)$. It follows in particular that

$$
\eta^{\,1-p_{i,\eta}(v)/s_i}
=\exp\left(-\frac{p_{i,\eta}(v)-s_i}{s_i}\log\eta\right)
\longrightarrow1
\quad\text{uniformly in }v.
\tag{2.14}
$$

The reason is $\eta^2|\log\eta|\to0$. This factor accounts for the normalization of concentrated functions under the varying exponent.

For any fixed $u\in\mathbb R^3$, $\lambda>0$ and $0\le j\le k$, disjointness and change of variable in each integral give the exact identity

$$
\begin{aligned}
\rho_{p_\delta}(D^jT_\eta u/\lambda)
=\sum_{i=1}^3\int_{-1}^1
\eta^{\,1+(k-j-1/s_i)p_{i,\eta}(v)}
\left|\frac{u_i\psi_{s_i}^{(j)}(v)}{\lambda}\right|^{p_{i,\eta}(v)}dv.
\end{aligned}
\tag{2.15}
$$

For $j=k$, the first factor tends uniformly to one by (2.14). The second factor converges pointwise to the power with exponent $s_i$. It is bounded uniformly for small $\eta$: the base is bounded, all exponents lie in $[r,q]$, and $w^\theta\le\max\{1,K^q\}$ for $0\le w\le K$ and $r\le\theta\le q$. This also covers zeros of the derivatives. Dominated convergence and (2.11) therefore prove

$$
\rho_{p_\delta}(D^kT_\eta u/\lambda)
\longrightarrow
\frac{|u_1|^r+|u_2|^r}{\lambda^r}
+\frac{|u_3|^q}{\lambda^q}
=M_{r,q}(u/\lambda).
\tag{2.16}
$$

For $j<k$, the first factor in (2.15) can be written as

$$
\eta^{\,1-p_{i,\eta}(v)/s_i}
\eta^{(k-j)p_{i,\eta}(v)}.
$$

The first factor is uniformly bounded by (2.14), and the second is at most $\eta^{(k-j)r}$. The same bounded-base estimate for the remaining factor gives

$$
\rho_{p_\delta}(D^jT_\eta u/\lambda)\longrightarrow0
\qquad(0\le j<k).
\tag{2.17}
$$

In particular, for every $\tau>0$, substitution of $\lambda=\tau$ in (2.17) makes the modular at most one for all sufficiently small $\eta$. Definition (1.2) then gives

$$
\|D^jT_\eta u\|_{p_\delta(\cdot)}\longrightarrow0
\qquad(0\le j<k).
\tag{2.18}
$$

For nonzero $u$, let $n=N_{r,q}(u)>0$. Given $0<\theta<n$, strict decrease of the mixed unit-level function implies

$$
M_{r,q}(u/(n-\theta))>1,
\qquad
M_{r,q}(u/(n+\theta))<1.
\tag{2.19}
$$

By (2.16), these same strict inequalities hold for the top-derivative modular at the two fixed scales when $\eta$ is sufficiently small. Monotonicity in the scale brackets its Luxemburg norm between $n-\theta$ and $n+\theta$. By (2.16)–(2.17), the full derivative modular $\mathcal R_{k,p_\delta}(T_\eta u/\lambda)$ also tends to $M_{r,q}(u/\lambda)$ at each fixed positive scale, so the identical bracketing applies directly to $J_k$. Together with (2.18) this proves

$$
S_k(T_\eta u)\longrightarrow N_{r,q}(u),
\qquad
J_k(T_\eta u)\longrightarrow N_{r,q}(u).
\tag{2.20}
$$

For $u=0$ both statements are exact equalities to zero. When $k=0$ the sums of lower derivatives are empty, and the same argument gives (2.20) with $S_0=J_0=\|\cdot\|_{p_\delta(\cdot)}$.

Apply (2.20) to the finite set

$$
\mathcal V=\{x,y,z,x+y,y+z,z+x,x+y+z\}
\tag{2.21}
$$

with $x,y,z$ as in (2.6). Choose one sufficiently small $\eta>0$ such that, for every $v\in\mathcal V$, both errors satisfy

$$
|S_k(T_\eta v)-N_{r,q}(v)|<c/24,
\qquad
|J_k(T_\eta v)-N_{r,q}(v)|<c/24.
\tag{2.22}
$$

There are only fourteen convergence conditions, so their neighborhoods have a common positive radius. Set

$$
f=T_\eta x,\qquad g=T_\eta y,\qquad h=T_\eta z.
\tag{2.23}
$$

Linearity ensures that the same map and the same $\eta$ give all seven function combinations in each defect. Equations (2.9) and (2.22) imply, for each $N\in\{S_k,J_k\}$,

$$
\Delta_N(f,g,h)>D-7c/24
\ge\frac{5c}{6}-\frac{7c}{24}
=\frac{13c}{24}>\frac c4.
\tag{2.24}
$$

This proves (2.3) for the same triple. The functions are already compactly supported and smooth, hence belong to both closure spaces in (1.6). Restricting the respective ambient norm preserves every term in the defect, which proves all the stated failures. $\square$

## 3. Classification predicates beyond the obstruction

**Definition 3.1 (Remaining classification and fixed-interior robustness questions).** For a specified order $k$ and a specified norm convention $N\in\{S_k,J_k\}$, let $\mathcal H_{k,N}$ be the set of exponents $p:I\to(1,2)$ with $1<p_-\le p_+<2$ for which $\Delta_N(f,g,h)\le0$ for every triple in $W^{k,p(\cdot)}(I)$. Theorem 2.1 excludes its explicit analytic exponents from each $\mathcal H_{k,N}$; it does not classify the other nonconstant exponents.

For a prescribed $p_0\in(1,2)$, a distinct robustness question asks whether there is $\epsilon_0>0$ such that every analytic $p:I\to(1,2)$ with $1<p_-\le p_+<2$ and $\|p-p_0\|_\infty<\epsilon_0$ lies in $\mathcal H_{k,N}$, or whether counterexamples can be found in every such neighborhood. Theorem 2.1 supplies neither alternative at a prescribed fixed $p_0>1$: its family approaches the endpoint $1$, since $\|p_\delta-1\|_\infty=\delta$ and $r\downarrow1$ as $\delta\downarrow0$. Its lower defect bound $4^{-1/\delta}/4$ tends to zero. Its quantifiers are $\forall\delta\,\forall k\,\exists(f,g,h)$; no triple common to every order, no uniform support scale, and no transfer to arbitrary equivalent norms are asserted. These classification and robustness predicates are residual questions of the theorem, rather than a classification answer to Problem 4.

## 追加锚（本行以下为增补区）

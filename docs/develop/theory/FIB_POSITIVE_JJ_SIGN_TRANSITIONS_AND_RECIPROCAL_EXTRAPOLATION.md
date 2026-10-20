# FIB Positive JJ Sign Transitions and Reciprocal Extrapolation

## 1. The full domain and the critical original-clock problem

Fix a declared maximum degree $d\ge1$ and put $m=d+1$. A world is a triple $(P,g,\delta)$ in which $P$ is a strictly entrywise positive real $2\times2$ matrix of rank one and trace one, and

$$
g(t)=\sum_{j=0}^{m-1}\beta_jt^j,\qquad
\beta\in\mathbb R^m\setminus\{0\},\qquad \delta\in\mathbb R.
\tag{1.1}
$$

The entire declared coefficient vector is the target of gain extraction. Every lower actual degree, every coefficient sign, sampled and repeated gain roots, constant nonzero gains, and every real constant drift remain in the domain. Let

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\qquad A_i=E_iA_{i-1},\qquad
z_i=g(i)\operatorname{tr}(A_iP)+\delta,
\tag{1.2}
$$

where each individual chronological action $E_i$ is $M$ or $J$ and has its immediate read. The initial read counts. Thus $N$ reads have original clocks $0,\ldots,N-1$. There is one trajectory, with no reset, copy, skipped read, unread compound action, extra sensor, inverse acquisition action, empty-action read, or clock renumbering.

For a terminal word $w$, a fixed linear full-gain-ray output is

$$
C_w(z_0,\ldots,z_{N-1})^{\mathsf T}=s\beta,\qquad s\ne0.
\tag{1.3}
$$

Either sign of $s$ is permitted. A countable palette contains at most countably many preassigned real matrices per terminal word; its history-dependent selector need have no regularity. Matrix entries that depend on observations are outside this mechanism. A preassigned acquisition word is independent of observations. Adaptive gain extraction and recovery of the complete normalized triple $(P,g,\delta)$ are separate problems.

The critical mixed budget is $N=2m+1$. This volume concerns the positive $JJ$ criterion at that budget, uniformly for

$$
m\ge5,\qquad K=2m-2,\qquad
a\in\{0,\ldots,K\},\qquad \rho>0,
\tag{1.4}
$$

and the chronological word

$$
w_a=M^aJJM^{K-a}.
\tag{1.5}
$$

Put $r=a+1$ and $T=\{0,\ldots,2m\}\setminus\{r\}$. Directly from $J^2=I$,

$$
A_r=JM^a,\qquad
A_i=M^{k_i}\quad(i\in T),\qquad
k_i=\begin{cases}i,&i\le a,\\i-2,&i\ge a+2.\end{cases}
\tag{1.6}
$$

The outlier at clock $r$ is acquired. Its eventual output coefficient may be zero. The matrix $M^a$ is acquired twice, at the distinct original clocks $a$ and $a+2$. In retained-clock order the exponent list is

$$
0,1,\ldots,a,\ a,a+1,\ldots,K.
\tag{1.7}
$$

Let $F_{-1}=1,F_0=0,F_1=1$ and $F_{k+2}=F_{k+1}+F_k$. Since $M^2=M+I$, induction gives $M^k=F_{k-1}I+F_kM$ for $k\ge0$. Define

$$
u_k=F_{k-1}-\rho F_k,\qquad
u_0=1,\quad u_1=-\rho,\quad u_{k+2}=u_{k+1}+u_k.
\tag{1.8}
$$

A positive interpolation candidate means a real polynomial $R$ with $\deg R\le m-1$ satisfying every equation

$$
R(k)=\frac1{u_k}\quad(0\le k\le a),\qquad
R(k+2)=\frac1{u_k}\quad(a\le k\le K),
\tag{1.9}
$$

with

$$
u_k\ne0\quad(0\le k\le K).
\tag{1.10}
$$

Thus $R(a)=R(a+2)=1/u_a$. Every exponent in $0,\ldots,K$ occurs in (1.9). Exponent notation is auxiliary algebra; the interpolation nodes in (1.9) are the original acquired clocks.

## 2. The exact operational criterion and its determinant obligation

For $i\in T$ and $0\le j<m$, let $V_T(i,j)=i^j$, with $0^0=1$, and set

$$
\lambda_i=F_{k_i},\qquad
\mathcal D=
\left[
\operatorname{diag}(u_{k_i})V_T\
\operatorname{diag}(\lambda_i)V_T
\right].
\tag{2.1}
$$

Rows are ordered by increasing original clock. The matrix is $2m\times2m$.

The following classification is a credited result of *FIB Critical Mixed Gain Words and Clock-Pencil Obstructions*, Sections 3–10. On the full domain of Section 1, an all-input countable palette on a preassigned critical mixed word exists exactly when some $JJ$ word has a universal identity with functional $L=\rho I+M$, $\rho>0$. For that $JJ$ word the exact condition is (1.9)–(1.10) together with

$$
\det\mathcal D\ne0.
\tag{2.2}
$$

One fixed matrix then suffices everywhere. The classification includes the obstruction on the exceptional positive-source stratum of an opposite-sign functional; it does not merely inspect the scale of one displayed identity. Consequently the countable-palette assertion includes globally nonuniversal matrices and arbitrary selectors. These classification and covering results are supplied premises of the operational application here. The new interpolation proofs below are independent of them.

For completeness, the algebra connecting a positive universal identity to this exact interpolation criterion has the following direct proof. A universal identity with this functional and zero outlier column satisfies, for every auxiliary real matrix $S$,

$$
C\mathbf1=0,\qquad
C\operatorname{diag}\bigl(\operatorname{tr}(A_iS)\bigr)V
=\operatorname{tr}((\rho I+M)S)I_m.
\tag{2.3}
$$

Here $V(i,j)=i^j$ on all $2m+1$ clocks. Auxiliary $S$ express linear identities; they are not additional physical sources. For $i\in T$,

$$
A_i=u_{k_i}I+\lambda_iL,\qquad L=\rho I+M.
\tag{2.4}
$$

The trace functionals represented by $I,L$ are independent. Comparing their coefficients in (2.3), and writing $B_1,B_2$ for the two blocks of $\mathcal D$, gives

$$
C_TB_1=0,\qquad C_TB_2=I_m.
\tag{2.5}
$$

In fact every $u_{k_i}$ is nonzero even before imposing (1.10): $u_0=1$, and $F_{k-1}>0$ for $k\ge2$, whereas $u_k=0$ would require $\rho=F_{k-1}/F_k$ with $k\ge2$. At such a zero $M^k=F_kL$ would be proportional to the functional matrix. The credited critical structural theorem excludes that proportionality for any acquired cumulative matrix of a nonzero identity. This is the only structural input needed for this necessity step. Alternatively (1.10) is already explicit in the interpolation problem.

The $2m$ distinct retained clocks make $V_T$ have rank $m$: a polynomial of degree at most $m-1$ with $m$ distinct zeros vanishes. Nonzero weights give $\operatorname{rank}B_1=m$. Equation (2.5) gives $\operatorname{rank}B_2=m$ and trivial intersection of the two block images, because applying $C_T$ to an element of their intersection makes its second-block coefficient vector zero. Hence $\mathcal D$ is invertible, $C_T$ has rank $m$, and $\ker C_T=\operatorname{range}B_1$. The drift condition is exactly $\mathbf1_T\in\operatorname{range}B_1$, which is equivalent to (1.9).

Conversely, assume (1.9)–(1.10) and (2.2). Set

$$
C_r=0,\qquad
C_T=[\,0_{m\times m}\ \ I_m\,]\mathcal D^{-1}.
\tag{2.6}
$$

The coefficient vector of $R$ expresses $\mathbf1_T$ as $B_1$ times that vector. With $t_P=\operatorname{tr}(MP)>0$, the actual reads therefore obey

$$
Z_T=B_1\beta+B_2\bigl((\rho+t_P)\beta\bigr)
+\delta\mathbf1_T,\qquad
CZ=(\rho+t_P)\beta\ne0.
\tag{2.7}
$$

Positivity of $t_P$ follows from strict entrywise positivity of $P$ and the nonzero nonnegative entries of $M$. This proves sufficiency on every source, coefficient vector, degree drop, root pattern, and drift in Section 1. All entries of $C$ depend only on $m,a,\rho$. The outlier read remains acquired, and no interpolation clock has been replaced by an exponent clock.

There is also an exact determinant identity. If

$$
B_0=\operatorname{diag}(F_{k_i-1})V_T,
$$

then $\mathcal D=[B_0-\rho B_2\ \ B_2]$. Adding $\rho$ times each second-block column to its corresponding first-block column gives

$$
\det\mathcal D=\det[B_0\ \ B_2].
\tag{2.8}
$$

Thus the determinant is independent of $\rho$ for fixed $m,a$. This does not determine its value or sign. No nonsingularity conclusion follows from interpolation alone, and no singularity conclusion follows from an interpolation obstruction.

## 3. Uniform transition-window theorem

For $j\ge1$ write $t_j=F_{j-1}/F_j$. Define the positive open cells

$$
I_2=(1,\infty),\qquad
I_b=\begin{cases}
(t_b,t_{b-2}),&b\ge4\text{ even},\\
(t_{b-2},t_b),&b\ge3\text{ odd}.
\end{cases}
\tag{3.1}
$$

**Theorem 3.1.** Suppose $m\ge5$ and (1.9)–(1.10) hold for some $a,\rho,R$ in the entire domain (1.4). The first same-sign exponent index

$$
b=\min\{k\in\{2,\ldots,K\}:u_{k-1}u_k>0\}
\tag{3.2}
$$

exists and satisfies

$$
2\le b\le m-2,\qquad
m-1\le a\le m+b-2,\qquad \rho\in I_b.
\tag{3.3}
$$

If $a=m-1$, then

$$
b\equiv m\pmod2.
\tag{3.4}
$$

Consequently, for every $m\ge5$ and every $\rho>0$, interpolation is impossible at every gap

$$
0\le a\le m-2,\qquad a=2m-3,\qquad a=2m-2.
\tag{3.5}
$$

These statements do not assume (2.2). The proof occupies Sections 4–9.

The same-sign index is an exponent relation, not an extra action or a changed acquisition clock. Formula (3.3) is a necessary condition, not an existence assertion for any point in its remaining window.

## 4. Sign transitions and exclusion of the latest initial possibility

**Lemma 4.1 (P1).** Under (1.9)–(1.10), $b$ exists and $2\le b\le m$. Put $\epsilon=(-1)^{b-1}$. The signs of $u_0,\ldots,u_{b-1}$ are $(-1)^k$, and every $u_k$ for $k\ge b-1$ has sign $\epsilon$.

**Proof.** Let

$$
\phi=\frac{1+\sqrt5}{2},\qquad
\psi=\frac{1-\sqrt5}{2}=-\phi^{-1}.
$$

Solving the initial equations, or checking the two initial values and the recurrence, gives

$$
u_k=A\phi^k+B\psi^k,\qquad
A=\frac{\phi^{-1}-\rho}{\sqrt5},\qquad
B=\frac{\phi+\rho}{\sqrt5}>0.
\tag{4.1}
$$

If no same-sign pair occurs through exponent $K$, nonvanishing forces signs to alternate at every consecutive exponent. In the retained-clock list (1.7), repeating exponent $a$ inserts an equal-sign pair and removes no sign change. There would be $K=2m-2$ disjoint retained-clock intervals with opposite endpoint signs for $R$. The intermediate value theorem supplies a distinct root in each. Since $R(0)=1$ when $a\ge0$, the polynomial is nonzero, and $\deg R\le m-1<K$ is a contradiction. In particular $A=0$, which would give perpetual alternating signs, is impossible.

At the first same-sign pair, minimality gives $\operatorname{sgn}u_k=(-1)^k$ for $0\le k\le b-1$, and $\operatorname{sgn}u_b=\operatorname{sgn}u_{b-1}=\epsilon$. The recurrence preserves a common nonzero sign: the sum of two numbers of sign $\epsilon$ has that sign. This extends the sign assertion to every later exponent, including in the auxiliary infinite recurrence.

There are exactly $b-1$ sign changes in (1.7), each giving a distinct real root of $R$. Hence $b-1\le\deg R\le m-1$, so $b\le m$. Finally the dominant term in (4.1) has sign $\epsilon$, because $|\psi|<1<\phi$ and the eventual sign is $\epsilon$. Thus $A\ne0$ and $\operatorname{sgn}A=\epsilon$, while $(-1)^b=-\epsilon$. $\square$

**Lemma 4.2 (P2).** The case $b=m$ is impossible.

**Proof.** In that case the $m-1$ sign-changing retained-clock intervals through exponent $m-1$ force degree exactly $m-1$. Their distinct roots exhaust the degree, so all roots are real and simple, strictly before the first clock carrying exponent $m-1$.

Both exponents $m,m+1$ are available, since $m+1\le K$. Their retained clocks, in increasing order, are later than every root. If a nonzero polynomial with roots $z_1,\ldots,z_{m-1}$ is evaluated to the right of all its roots, then

$$
\frac{d}{dt}\log|R(t)|=\sum_{\ell=1}^{m-1}\frac1{t-z_\ell}>0.
\tag{4.2}
$$

Therefore its magnitude strictly increases there. But $u_{m-1},u_m,u_{m+1}$ have the same sign and $u_{m+1}=u_m+u_{m-1}$, so

$$
|u_{m+1}|>|u_m|,\qquad |1/u_{m+1}|<|1/u_m|.
$$

This contradicts the required values at those two increasing clocks. If one exponent is repeated, use either occurrence consistent with increasing exponent order; all its occurrences remain beyond the roots. Thus $b\le m-1$. $\square$

## 5. A positive reciprocal expansion and strict left extrapolation

**Lemma 5.1 (P3).** For any $s\ge b$ with $s\equiv b\pmod2$, there are $H_s>0$ and $0<c_s<1$ such that, for every integer $n\ge0$,

$$
\frac1{u_{s+n}}=
\frac{\epsilon}{H_s}\sum_{\ell=0}^{\infty}c_s^\ell\lambda_\ell^n,
\qquad
\lambda_\ell=(-1)^\ell\phi^{-(2\ell+1)}\in(-1,1).
\tag{5.1}
$$

For $f_n=1/u_{s+n}$ and $\Delta f_n=f_{n+1}-f_n$, every integer $j\ge0$ satisfies

$$
\epsilon(-1)^j\Delta^jf_0>0.
\tag{5.2}
$$

**Proof.** By Lemma 4.1, $\operatorname{sgn}A=\epsilon$ and $(-1)^s=-\epsilon$. Define

$$
H_s=|A|\phi^s,\qquad c_s=\frac{B\phi^{-s}}{H_s}.
$$

Both are positive. Equation (4.1) at $s$ gives $u_s=\epsilon H_s(1-c_s)$. Its sign is $\epsilon$, so $c_s<1$. More generally,

$$
u_{s+n}=\epsilon H_s\phi^n
\left(1-c_s(-\phi^{-2})^n\right).
\tag{5.3}
$$

The geometric series for its reciprocal converges absolutely, since $c_s|\phi^{-2}|^n<1$, and gives (5.1).

A forward difference of order $j$ replaces $\lambda_\ell^n$ at $n=0$ by $(\lambda_\ell-1)^j$. Interchange with the series is justified by the bound $|\lambda_\ell-1|^j\le2^j$ and the convergent sum $\sum c_s^\ell$. Every $\lambda_\ell<1$, so

$$
\epsilon(-1)^j\Delta^jf_0
=\frac1{H_s}\sum_{\ell=0}^{\infty}c_s^\ell(1-\lambda_\ell)^j>0.
$$

This includes $j=0$. The argument is an exact series identity and a finite difference of that identity, with no approximation. Its sequence index is an auxiliary exponent offset; it will be applied only on explicitly identified consecutive original-clock blocks. $\square$

**Lemma 5.2 (P4).** Suppose $H\in\mathcal P_{m-1}$ agrees at consecutive original clocks $t_0,\ldots,t_0+m-1$ with $1/u_s,\ldots,1/u_{s+m-1}$, where $s\ge b$ and $s\equiv b\pmod2$. Then

$$
\epsilon H(t)>0,\qquad \epsilon H'(t)<0
\quad\text{for every real }t\le t_0.
\tag{5.4}
$$

**Proof.** Put $d_j=\Delta^jf_0$ for $0\le j\le m-1$ and $A_j=\epsilon(-1)^jd_j>0$. Newton interpolation on the unit-spaced block gives

$$
H(t_0+x)=\sum_{j=0}^{m-1}d_j\binom{x}{j}.
\tag{5.5}
$$

One verification is the polynomial identity $\Delta\binom{x}{j}=\binom{x}{j-1}$: taking successive differences at zero recovers the coefficients $d_j$, and hence the prescribed data. Agreement at $m$ distinct nodes uniquely determines a degree-at-most-$(m-1)$ polynomial by root counting.

For $x\le0$ set $C_0(x)=1$ and

$$
C_j(x)=(-1)^j\binom{x}{j}
=\frac1{j!}\prod_{h=0}^{j-1}(h-x)\quad(j\ge1).
\tag{5.6}
$$

Each $C_j$ is nonnegative on this half-line. For $x<0$ its factors are strictly positive and decreasing, and differentiation of the product gives $C_j'(x)<0$. At $x=0$ the sole vanishing factor is $-x$, whose derivative contributes a strictly negative product of the remaining factors; the other differentiated terms vanish. This proves $C_j'(0)<0$, also when $j=1$.

It follows that

$$
\epsilon H(t_0+x)=\sum_{j=0}^{m-1}A_jC_j(x)>0.
$$

The derivative is strictly negative: all terms with $j\ge1$ have negative derivative and positive coefficient, and $A_1>0$ because $m\ge2$. This proves (5.4), including the endpoint. In particular $H$ cannot have equal values at two distinct clocks on that half-line. $\square$

## 6. The left-half exclusion and central parity

**Lemma 6.1 (P5).** Every gap $0\le a\le m-2$ is impossible. At $a=m-1$, a candidate must satisfy $b\equiv m\pmod2$.

**Proof.** We know $b\le m-1$. Let $s$ be the largest integer not exceeding $m-1$ with $s\equiv b\pmod2$. Then $s$ is $m-2$ or $m-1$, and $s\ge b$.

If $a\le m-2$, then $s\ge a$. The $m$ exponents $s,\ldots,s+m-1$ are at most $K$. Taking their suffix occurrences in (1.9) gives the consecutive retained original clocks

$$
s+2,\ldots,s+m+1.
\tag{6.1}
$$

Apply Lemma 5.2 with $H=R$ and $t_0=s+2$. The two repeated-state clocks $a$ and $a+2$ are both at most $t_0$. Strict monotonicity there contradicts $R(a)=R(a+2)$.

If $a=m-1$ and $b\equiv m-1\pmod2$, choose $s=a$. The same argument uses the $m$ suffix clocks $a+2,\ldots,2m$ and again excludes the equal values at $a,a+2$. The only remaining parity is $b\equiv m\pmod2$. $\square$

## 7. Excluding the penultimate transition by real roots and concavity

**Lemma 7.1 (P6).** For $m\ge5$, the case $b=m-1$ is impossible.

**Proof.** Lemma 6.1 gives $a\ge m-1=b$. Thus exponents $0,\ldots,b-1$ are at the unchanged original clocks $0,\ldots,b-1$. Their $b-1=m-2$ sign changes force $m-2$ distinct real roots of $R$, all strictly before clock $b-1$.

At most one additional degree remains, because $\deg R\le m-1$. Nonreal roots of a real polynomial occur in conjugate pairs, so there is no degree available for a nonreal root. All roots of $R$ are real.

There is no root anywhere in $[b-1,2m]$. All retained values on that interval are nonzero and of sign $\epsilon$. A root in an interval between consecutive retained clocks would require a positive even total root multiplicity to preserve the endpoint signs, costing at least two degrees in addition to the $m-2$ roots already forced before $b-1$. Only one degree is available. This also covers the omitted-clock interval between $a$ and $a+2$. The endpoints $b-1,2m$ are themselves retained and nonzero.

Consequently $L(t)=\log|R(t)|$ is well defined on this entire interval. Factoring the nonconstant real-rooted polynomial, with distinct roots $z$ and multiplicities $n_z$, gives

$$
L''(t)=-\sum_z\frac{n_z}{(t-z)^2}<0.
\tag{7.1}
$$

Thus $L$ is strictly concave. The argument permits any additional real root outside this interval.

First suppose $a\ge b+1$. The original clocks $a-1,a,a+2$ carry exponents $a-1,a,a$. The recurrence has common sign $\epsilon$ from exponent $b-1$ onward, so $|u_a|>|u_{a-1}|$. Hence

$$
L(a)<L(a-1),\qquad L(a+2)=L(a).
\tag{7.2}
$$

The consecutive secant slopes on $[a-1,a]$ and $[a,a+2]$ are respectively negative and zero. This is impossible for a concave function, whose consecutive secant slopes are nonincreasing.

It remains to consider $a=b$. The three retained original clocks

$$
b+2,\quad b+4,\quad b+6
\tag{7.3}
$$

carry exponents $b,b+2,b+4$. They are acquired because $b+6=m+5\le2m$ when $m\ge5$. Let $H=|A|\phi^b$, $c=B\phi^{-b}/H\in(0,1)$, and $q=\phi^{-4}\in(0,1)$. By (5.3), the three denominator magnitudes are

$$
H(1-c),\qquad H\phi^2(1-cq),\qquad
H\phi^4(1-cq^2).
\tag{7.4}
$$

Their exact difference is

$$
\begin{aligned}
|u_{b+2}|^2-|u_bu_{b+4}|
&=H^2\phi^4\left((1-cq)^2-(1-c)(1-cq^2)\right)\\
&=H^2\phi^4c(1-q)^2>0.
\end{aligned}
\tag{7.5}
$$

Taking reciprocals and using (1.9) gives

$$
|R(b+4)|^2<|R(b+2)R(b+6)|,
$$

and therefore

$$
L(b+4)<\frac{L(b+2)+L(b+6)}2.
\tag{7.6}
$$

This contradicts concavity at the equally spaced original clocks (7.3). Both cases for $a$ are impossible. Together with Lemma 4.2, this proves $2\le b\le m-2$. $\square$

## 8. The moving right-hand gap bound

**Lemma 8.1 (P7).** Every interpolation candidate satisfies $a\le m+b-2$.

**Proof.** If $a\ge m+b-1$, the prefix contains the $m$ consecutive original clocks

$$
b,\ldots,b+m-1,
$$

carrying exactly the exponents $b,\ldots,b+m-1$. Apply Lemma 5.2 at $s=t_0=b$. It gives $\epsilon R(t)>0$ for every $t\le b$.

But the original clocks $0,1$ are retained in this prefix, and

$$
R(0)=1,\qquad R(1)=-1/\rho.
$$

They have opposite signs, so one is opposite to $\epsilon$. Both clocks are at most $b$. This is a contradiction, proving the bound. $\square$

Combining Lemmas 6.1, 7.1, and 8.1 gives

$$
2\le b\le m-2,\qquad m-1\le a\le m+b-2\le2m-4
$$

with the central parity in (3.4). This proves the gap and transition assertions of Theorem 3.1, including both right-edge exclusions.

## 9. Exact positive-parameter cells

**Lemma 9.1 (P8).** For a nonvanishing positive-parameter candidate, the first same-sign index is $b$ exactly when $\rho\in I_b$. In particular let $o,e$ be respectively the largest odd and even integers not exceeding $m-2$. Every candidate in Theorem 3.1 satisfies

$$
0<\rho<t_o\quad\text{or}\quad \rho>t_e,
\tag{9.1}
$$

with all zero-denominator poles still excluded. The whole intervening interval $[t_o,t_e]$, including $\phi^{-1}$, is impossible.

**Proof.** We first establish the order of the thresholds, including what makes the cells exact. Cassini's identity is

$$
F_{j+1}F_{j-1}-F_j^2=(-1)^j\quad(j\ge1).
\tag{9.2}
$$

At $j=1$ both sides equal $-1$. The recurrence makes the left side at $j+1$ the negative of the left side at $j$, proving induction. Consequently

$$
t_{j+2}-t_j
=\frac{F_{j+1}F_j-F_{j-1}F_{j+2}}{F_{j+2}F_j}
=\frac{(-1)^{j-1}}{F_{j+2}F_j}\quad(j\ge1).
\tag{9.3}
$$

Thus odd thresholds strictly increase and even thresholds strictly decrease. The formula

$$
F_j=\frac{\phi^j-\psi^j}{\sqrt5}
\tag{9.4}
$$

follows by checking its initial values and recurrence. Since $|\psi/\phi|<1$, both threshold subsequences tend to $\phi^{-1}$. The odd thresholds lie below this limit and the even thresholds above it. In particular $t_1=0,t_2=1$.

If $A>0$, equivalently $\rho<\phi^{-1}$, all even $u_k$ are positive by (4.1). The odd values change from negative to positive as their thresholds increase through $\rho$. The first same-sign index is the first positive odd index $b\ge3$. Since $F_j>0$ for $j\ge1$, the conditions $u_{b-2}<0$ and $u_b>0$ are exactly

$$
t_{b-2}<\rho<t_b.
\tag{9.5}
$$

Conversely these inequalities place $\rho$ below $\phi^{-1}$ and, by threshold order, make every earlier odd value negative and every later odd value positive. All even values are positive, so the first same-sign index is exactly $b$.

If $A<0$, all odd values are negative. For even $b\ge4$, the first same-sign pair occurs at the first negative even value, exactly when

$$
t_b<\rho<t_{b-2}.
\tag{9.6}
$$

Threshold order proves the converse as well: earlier even values are positive, later even values negative, and all odd values negative. For $b=2$, $u_0=1,u_1=-\rho,u_2=1-\rho$, so the exact condition is $\rho>1$.

No case with $A=0$ survives Lemma 4.1. The open cells just found exclude their zero-denominator endpoints. In fact their ordering also shows that no other threshold lies inside an individual cell; retaining (1.10) explicitly avoids relying on any implicit exception.

Taking the union of odd cells with $b\le m-2$ yields $(0,t_o)$ with the intervening odd pole endpoints removed. The union of even cells yields $(t_e,\infty)$ with their intervening even pole endpoints removed. These are precisely the open cells (3.1); the coarse intervals in (9.1) do not restore any pole. This proves the parameter assertion and completes Theorem 3.1. $\square$

## 10. The exact residual feasibility problem

The original all-degree positive critical existence question is now equivalent to the following restricted existential question:

$$
\begin{gathered}
\exists\,m\in\mathbb Z,\ m\ge5,\quad
\exists\,b\in\mathbb Z,\ 2\le b\le m-2,\quad
\exists\,a\in\mathbb Z,\ m-1\le a\le m+b-2,\\
\exists\,\rho\in I_b,\quad
\exists\,R\in\mathbb R[t],\ \deg R\le m-1,\\
a=m-1\ \Longrightarrow\ b\equiv m\pmod2,\\
u_k=F_{k-1}-\rho F_k\ne0\quad(0\le k\le2m-2),\\
u_kR(k)=1\quad(0\le k\le a),\qquad
u_kR(k+2)=1\quad(a\le k\le2m-2),\\
\det\mathcal D\ne0,
\end{gathered}
\tag{10.1}
$$

where $\mathcal D$ is exactly (2.1), at the retained original clocks (1.6). For a particular fixed $m$, omit only the outer existential quantifier on $m$; every other condition remains.

**Proof of equivalence.** A solution of the original criterion is an interpolation candidate, so Theorem 3.1 forces every restriction displayed in (10.1). Conversely every solution of (10.1) satisfies the original interpolation and nonsingularity requirements without altering any equation or domain. Equation (2.6) then constructs the gain output. No sufficiency claim is made for the inequalities and cells alone. $\square$

A positive answer requires at least one exact witness satisfying all of (10.1), including nonsingularity. A uniform negative answer requires excluding every such tuple for every integer $m\ge5$. Neither is established here. No positive candidate is supplied.

The left-extrapolation argument needs $m$ consecutive retained original clocks with the required tail parity. Within the surviving window neither block used in Sections 6 and 8 is guaranteed to exist. For $b\le m-2$ the initially forced real roots leave at least two degrees of the allowed degree bound available, so nonreal conjugate pairs are no longer excluded by that root count. The real-rooted concavity proof for $b=m-1$ therefore does not automatically extend. These identify the limits of the arguments, not evidence of feasibility.

No value or sign of $\det\mathcal D$ is determined by these proofs. Its independence from $\rho$ is (2.8), not a decision of (10.1). A finite encoding, a determinant expression, or membership in a residual cell is not a solved feasibility problem.

## 11. Fixed-word consequences and the continuing complete-target question

**Corollary 11.1.** For every $m\ge5$, a preassigned word $M^aJJM^{2m-2-a}$ with $a$ in (3.5) admits no all-input countable palette for the full gain vector on the domain of Section 1 at $2m+1$ reads. For the other gaps, any positive critical realization must obey (3.3)–(3.4) and every condition of (10.1).

**Proof.** The credited critical classification of Section 2 makes positive interpolation plus nonsingularity necessary for such fixed-word full-domain success. Theorem 3.1 excludes interpolation itself at the listed gaps. On the remaining gaps it supplies the stated necessary conditions. $\square$

This corollary does not assert that every excluded word has no universal identity of any sign. An opposite-sign functional and its exceptional positive-source stratum are distinct issues; their countable-palette treatment is part of the credited critical theorem.

The credited low-degree exclusions in *FIB Critical Mixed Gain Words and Clock-Pencil Obstructions*, Section 13, resolve $m=2,3,4$. They give sharp fixed mixed gain-ray counts six, eight, and ten for $d=1,2,3$, respectively. The quadratic proof uses equal repeated-state values and reflection; the cubic proofs use fourth differences on consecutive reciprocal values, six centered original clocks, and the positive shifted-parameter check. Those results are prior supplied mathematics, not consequences newly claimed from the $m\ge5$ proof.

For every $m$, the credited mixed word $JM^{2m}$ succeeds at $2m+2$ reads, with positive scale $\operatorname{tr}(JP)$. The credited pure word $M^{2m}$ returns the exact gain and drift at $2m+1$ reads. Together with the earlier mixed obstruction through $2m$ reads, the exact critical classification gives the following status:

| Problem | Established result and boundary |
| --- | --- |
| Fixed acquisition without a mixed-word requirement | Sharp gain count $2d+3=2m+1$, credited Hermite result |
| Fixed mixed gain extraction, $d=1,2,3$ | Sharp counts six, eight, ten, with arbitrary countable palettes |
| Fixed mixed gain extraction, $m\ge5$ | Either $2m+1$ or $2m+2$; the decision remains exactly (10.1) |
| Adaptive gain extraction among several words | No sharp count or new joint-word lower bound follows from the present exclusions |
| Complete-target recovery | The global sharp count remains unresolved, with or without the specified gain-output mechanism |

Separate fixed-word all-input failures do not give an adaptive lower bound: their failure strata need not have a common world, and a protocol may select different words from different histories. A simultaneous common-domain covering or target-ambiguity argument would be needed.

For the complete-target programme the supplied *FIB Moving-Trace Recovery and Sharp Calibrated Continuations* gives the stronger current upper bound

$$
2d+s+5\le3d+5,\qquad s=\deg g,
\tag{11.1}
$$

with exactly the full $\beta$ returned by one fixed matrix per terminal word. This retains the whole domain, including all root patterns and $\eta=0$. Its precise mechanism is as follows. Credited pure-$M$ calibration after the prefix $M^{2d+2}$ costs $2d+3$ reads and provides the exact $g,\delta,t_P$. From the actual state $C=M^{2d+2}$, one $J$ and subsequent individual $M$ actions produce matrices $M^pJC$ at clocks $2d+3+p$. Any two distinct such powers with nonzero sampled gain give two useful source traces. Among $s+2$ consecutive continuation clocks at least two gains are nonzero by the polynomial root bound. Reads at roots are retained and cost only their mandatory action and read; no return is needed.

The all-pairs independence used here has a direct proof. The entries of

$$
aI+bM+cJ+eMJ=\begin{pmatrix}a+e&b+c\\b+c+e&a+b+e\end{pmatrix}
$$

show that $I,M,J,MJ$ are a basis: vanishing of the off-diagonal difference gives $e=0$, then the two diagonal entries give $a=b=0$, and finally $c=0$. Right multiplication by $C=M^{2d+2}$ is invertible and preserves $\operatorname{span}\{I,M\}$ bijectively, since $M^{-1}=M-I$. Thus $I,M,JC,MJC$ are a basis. For any $p<q$, a relation between $M^p,M^q$ tested on the two eigenspaces gives $a+b\phi^{q-p}=a+b\psi^{q-p}=0$. As $\phi>1>|\psi|$, it forces $a=b=0$. Consequently the coordinate rows of these powers in $I,M$ form an invertible matrix. Multiplication by $JC$ changes the last two basis elements invertibly to $M^pJC,M^qJC$. This proves the claimed all-pairs basis for the actual useful indices. Negative powers in this argument are auxiliary algebra only.

The two recovered traces, trace one, and $t_P$ therefore uniquely determine $P$ by nondegeneracy of the trace pairing: a matrix pairing to zero with a basis pairs to zero with every matrix unit and has every entry zero. The actual source supplies the solution. Every division is by a checked nonzero gain. The fixed gain matrix acts only on the original calibration prefix and is padded with zero columns thereafter. This proves the bound and output mechanism on the full declared domain.

For clarity, the same supplied moving-trace source proves sharpness of $s+2$ additional reads only for calibrated continuation from a pure-$M$ state with exact $g,\delta,t_P$ supplied and no additional source information. Its crossing-fiber obstruction uses the entire positive source fiber at $t_P=\phi$ and one common gain hiding the next $s$ clocks by roots. It permits arbitrary deterministic adaptive continuation and nonlinear answers. It also proves the exact total $2d+s+5$, and worst-case $3d+5$, among protocols constrained to start with $M^{2d+2}$. That fixed prefix is essential to the lower bound. These credited results do not establish global complete-target sharpness for earlier mixed protocols or different calibrations.

Writing $N_d^{\mathrm{lin}}$ for the optimal uniform complete-target read bound with the everywhere successful countable fixed-linear gain-ray mechanism, the credited general lower bound and moving-trace upper bound give

$$
2d+3\le N_d^{\mathrm{lin}}\le3d+5.
\tag{11.2}
$$

At $d=1$ the separate common-open-domain complete-target argument in the critical source improves the lower bound to six, so the combined current bounds are $6\le N_1^{\mathrm{lin}}\le8$. No sharp complete-target count follows. The left sides of these mechanism-specific bounds are not asserted for unrestricted nonlinear global recovery.

The valid prior $4d+5$ complete-target upper construction remains a credited result; (11.1) is the supplied moving-trace improvement. The unrestricted original complete-target goal remains open. In particular the present theorem decides neither unrestricted cubic eight-read recovery nor an unrestricted cubic nine-read lower bound.

The current local cubic frontier is supplied by DEV *FIB Self-Calibrating Relation Mathematics VI* and *VII*. This is a separate declared cubic domain $0\ne g\in\mathcal P_3$, not the $m\ge5$ interpolation candidate of this volume. Here an actual history fiber $\mathcal F(H)$ retains every earlier action and reading. For a known family $K$ the losing predicates are

$$
L_0(K,H)\Longleftrightarrow |K|\ge2,\qquad
L_{h+1}(K,H)\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{M,J\}}\exists z:\
L_h(K\cap\mathcal F(H,E,z),(H,E,z)).
\tag{11.3}
$$

Negation is one recovery strategy on the entire known family within $h$ further original-clock reads, including early stops. The exact MMJM parent and matrices are

$$
\begin{gathered}
H_3=(0,M,1,M,23/7,J,331/35),\quad H_4(Y)=(H_3,M,Y),\\
T=M^2=I+M,\quad B=JT=\begin{pmatrix}1&2\\1&1\end{pmatrix},\quad
D=MB=\begin{pmatrix}1&1\\2&3\end{pmatrix},\\
(A_0,\ldots,A_4)=(I,M,T,B,D),\quad Q_M=MD=B+D,\quad Q_J=JD=2B-M.
\end{gathered}
\tag{11.4}
$$

Write $m_5,j_5$ for VI's fifth predictions $m,j$, keeping them distinct from the coefficient dimension $m$. They equal $\delta+g(5)\operatorname{tr}(Q_MP)$ and $\delta+g(5)\operatorname{tr}(Q_JP)$. The supplied chart is

$$
\eta=(DP)_{22}>0,\quad R=P/\eta,\quad H=\eta g,\quad
DR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\quad
R=\begin{pmatrix}(3x-1)y&3x-1\\(1-2x)y&1-2x\end{pmatrix},\quad
1/3<x<1/2,\ y>0.
\tag{11.5}
$$

With $s=x+y,p=xy$ its parent trace factors are $(3p+1-s-x,s-2p,p+1-x,s-p,p+1)$, all positive, and

$$
j_5=\delta+H(5)s,\quad m_5=\delta+H(5)(s+1),\quad
z_6^{MJ}=\delta+H(6)(p+y+1),\quad
z_6^{MM}=\delta+H(6)(p+s+2).
\tag{11.6}
$$

All five actual parent equations with readings $(0,1,23/7,331/35,Y)$ are imposed. Identical $x,y,\delta$ give the same normalized source and, by interpolation at clocks zero through three, the same whole gain. Auxiliary predictions for unchosen actions add no acquired reads.

VI, Theorem 3.1 derives, for every arbitrary exactly three-target set at this same literal $H_4(Y)$, that $L_3$ forces common fifth predictions $m_5\ne j_5$. VI, Theorem 3.2 then recovers every known set of at most three targets in at most three further reads, eight total. Its exact II/V interfaces are II, Theorems 52.1, 53.1–53.2, 58.1 and V, Corollary 4.1: fixed-drift double-last-root uniqueness; common drift, seventh roots and nonzero sixth gains for a two-target $L_2$ actual fifth child; exclusion of a two-target fifth-$J$ bad child; the whole root-five $JJJ$ inverse; and the known-at-most-three-target inverse on one common non-diagonal joint fifth fiber. These nested II/V proofs have not been independently consulted. The complete VI, Lemma 2.1 and Theorem 2.2 proofs of the intervening roots-five-and-seven uniqueness and common-$j_5$ fifth-$M$ pair exclusion, and the bridge and recovery proofs, are reproduced in the companion critical volume, Section 17.1.

The bridge's actual-child argument is essential. Fifth $J$ in a losing triple must retain the whole triple because its two-target losing alternative is excluded. Thus $j_5$ is constant on that original triple. Fifth $M$ must also retain the whole triple because a two-target losing pair with the same $j_5$ is excluded. Equality $m_5=j_5$ puts that whole triple in the root-five inverse and is impossible. The resulting non-diagonal joint fiber meets V's stated premise, so one whole-triple strategy exists. Known pairs use fifth $J$ and its two-target exclusion; singletons stop. Therefore an unrestricted losing family at this MMJM parent must have at least four targets. The arbitrary three-target bridge is resolved, and no extraction of a losing triple from a larger family is asserted.

The other complementary histories retain different ancestors. VI fixes $D_0\in\mathbb R$, $\lambda\ne0$, $0<\varepsilon<1/6$, $a_0=D_0-21\lambda$, $a_2=D_0+5\lambda(1+\varepsilon)$ and uses

$$
C_3=(a_0,M,D_0,J,a_2,M,D_0),\quad
C_4(Y)=(C_3,M,Y),\quad C_5(Y,z)=(C_4(Y),J,z).
\tag{11.7}
$$

This is MJMMJ, with matrices $I,M,U,MU,M^2U,JM^2U$, $U=JM$. VI, Theorem 5.1 excludes a two-target $L_2$ in each entire actual fifth-$J$ child for arbitrary target drifts and both sixth-gain strata. VI, Theorem 6.1 gives an eight-total-read policy on a known family at $C_4(Y)$ only if every entire actual fifth-$J$ child has at most two targets; at $C_3$ the bound is imposed on every actual fourth-$M$, fifth-$J$ joint child.

VII instead uses the JMMJM histories

$$
\begin{aligned}
H_J^-&=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,M,D_0+312\lambda/5),\\
H_J(Y)&=(H_J^-,J,Y),\quad H_{JM}(Y,z)=(H_J(Y),M,z),\qquad\lambda\ne0.
\end{aligned}
\tag{11.8}
$$

Their matrices are $I,J,L,J+L,C,Q$, with $L=MJ$, $C=\left(\begin{smallmatrix}2&1\\1&1\end{smallmatrix}\right)$ and $Q=MC=\left(\begin{smallmatrix}1&1\\3&2\end{smallmatrix}\right)$. VII's bijection $f=g/\lambda$, $e=(\delta-D_0)/\lambda$ normalizes the six readings to $(0,24,48,312/5,(Y-D_0)/\lambda,(z-D_0)/\lambda)$ and preserves sources, clocks, and target distinctions. VII, Theorem 4.1 excludes two-target $L_2$ on every actual fifth-$M$ child for arbitrary drifts and gain samples. Its proof in Sections 1–4 includes the double-last-root stratum and the complete rational Bernstein certificate. VII, Theorem 5.1 gives an eight-total-read policy only under the bound of at most two targets on every whole actual fifth-$M$ child at $H_J(Y)$, or on every fourth-$J$, fifth-$M$ joint child at $H_J^-$. In (11.7)–(11.8), $D_0$ is a history parameter, not a promise that it equals the target drift. Each policy takes the specified actions, retains its actual singleton or pair, and executes a separating suffix of at most two atoms on that whole pair. These pair theorems do not recover arbitrary larger children or identify these histories with MMJM.

VII, Theorem 6.2 adds a whole-known-class result at the MMJM parent (11.4). Write $(a_6,b_6,c_6,d_6)$ for its chronological fifth/sixth responses $(a,b,c,d_6)$ and let $v_6=H(6)$. Then

$$
a_6=\operatorname{read}(JJ)=\delta+v_6(p+1),\quad
b_6=\operatorname{read}(JM)=a_6+v_6x,\quad
c_6=\operatorname{read}(MJ)=a_6+v_6y,\quad
d_6=\operatorname{read}(MM)=c_6+v_6(x+1).
\tag{11.9}
$$

For known constants $Y,m_5,j_5,b_0,d_0$, impose all parent equations and the whole-class promises $m_5(W)=m_5$, $j_5(W)=j_5$, $b_6(W)=b_0$, $d_6(W)=d_0$. Set $\kappa=m_5-j_5$, $\omega=d_0-b_0$. For $\omega\ne0$, at least one of $a_6,c_6$ is injective on the whole class, including disjoint putative collision pairs, giving seven total reads. This case includes $\kappa=0$. The exact response-curve mapping is

$$
t=1/(y+1)\in(0,1),\quad \rho=\kappa/\omega,\quad
e=1-\rho,\quad K=(b_0-j_5)/\omega-\rho,\quad
v_6=\omega t,\quad ex=K+\rho/t-t,\quad
a_6=b_0-\omega tx,\quad c_6=d_0-\omega t(x+1).
\tag{11.10}
$$

The $\rho$ here is a separate response-curve parameter, not the positive interpolation parameter of (1.8). The proof treats all real values of this ratio. For $\omega=0$, $\kappa\ne0$, $v_6=0$, $\delta=b_0$, and $s=(j_5-b_0)/\kappa>0$ is common. The inherited II, Lemma 71.1 on exactly that non-diagonal root-six class makes the last $JJJ$ response $b_0+sH(7)$ injective, giving eight total reads. No $\omega=\kappa=0$ assertion is supplied. VII, Corollary 6.3 applies these inverses to known subsets and to $H_3$ when every actual fourth-$M$ child has supplied known constants placing its entire retained family in such a class. Those promises are not inferred from unrestricted reads. The complete proof, arm choice and II interface correspondence are VII, Section 6, also mapped in the companion critical volume, Section 17.3.

The unresolved local MMJM question is whether some entire $\mathcal F(H_4(Y))$ has $L_3$; any such losing family needs at least four targets. At the distinct MJMM and JMMJ parents, larger actual designated fifth children with at least three targets and their simultaneous opposite-arm realization remain unresolved. Different actions on a larger family can retain different bad pairs. The supplied pair theorems and whole-class promises do not settle arbitrary larger fibers, nor the original-root eight-versus-nine alternative on all cubic worlds. DEV VI/VII's local and original-root simultaneous-realization systems have no feasibility verdict supplied here. All ancestor equations and the distinction between known promised families and unrestricted observations remain in force.

The continuing pure-theory research programme is not completed by this partial all-degree unit. No known-factor restriction of the gain space, generic-source assumption, omitted positive source, deleted root clock, or actual-degree truncation is used here.

## 12. Attribution, correspondence, and evidence boundaries

The supplied mathematical inputs have the following roles:

| Supplied input | Mathematical role |
| --- | --- |
| *FIB Critical Mixed Gain Words and Clock-Pencil Obstructions*, complete integrated source | Full model and domains; universal identities and countable covering; critical span and pencil/exceptional classification; legal-word elimination; positive-source palette bridge; exact positive $JJ$ criterion; credited low-degree exclusions and fixed mixed thresholds |
| All-degree transition proof envelope, P1–P8 | The uniform necessary conditions and infinite-family exclusions proved in Sections 4–9 |
| *FIB Moving-Trace Recovery and Sharp Calibrated Continuations*, complete source | Exact Hermite calibration; useful translated-power pairs; $2d+s+5\le3d+5$ complete-target upper bound; full crossing fiber; sharp calibrated continuation and fixed-prefix counts; continuing global scope |
| DEV *FIB Self-Calibrating Relation Mathematics VI*, complete source | Literal MMJM exactly-three-target common-fifth bridge and at-most-three-target eight-read recovery; distinct MJMMJ pair exclusion and actual-small-child consumers, with stated II/V interfaces |
| DEV *FIB Self-Calibrating Relation Mathematics VII*, complete source | Distinct JMMJM all-drift pair exclusion and actual-small-child consumers; MMJM common-response whole-class inverse with its exact nonzero and non-diagonal zero strata |

The exact proof correspondence for the all-degree contribution is:

| Supplied proof | Present result |
| --- | --- |
| P1 | Lemma 4.1: transition existence, sign pattern, initial bound $b\le m$ |
| P2 | Lemma 4.2: exclusion of $b=m$ by magnitude growth beyond all roots |
| P3 | Lemma 5.1: positive reciprocal expansion and strict difference signs |
| P4 | Lemma 5.2: sign and strict derivative for left polynomial extrapolation |
| P5 | Lemma 6.1: all left-half gaps and the central parity restriction |
| P6 | Lemma 7.1: exclusion of $b=m-1$, including the $m\ge5$ clock check |
| P7 | Lemma 8.1: the moving upper gap bound and two right-edge exclusions |
| P8 | Lemma 9.1: exact positive-$\rho$ cells and the excluded middle interval |

The all-degree synthesis is new relative to the supplied low-degree baseline: it excludes a uniform infinite family of gaps, bounds the first transition by $m-2$, and leaves an explicit moving right-half window with central parity and parameter cells. That content is credited to the supplied P1–P8 proof unit. The exposition does not claim an independently discovered theorem, a full all-degree decision, or a positive critical construction.

The critical source in turn credits *FIB Linear Gain-Ray Capacity and Hermite Readouts* for the model, universal and covering reductions, earlier mixed obstruction, pure-$M$ Hermite threshold, mixed upper construction, pure-terminal ambiguity, and prior complete-target upper bound. Its references to *FIB Self-Calibrating Relation Mathematics IV*, its supplied critical classification B–H, and its quadratic/cubic proof labels Q, L, S, C are inherited attributions. The moving-trace source likewise credits the Hermite calibration and earlier general lower bound. Nested source references introduce no additional verified mathematical premises here. The exact II/V interfaces for the DEV results are stated in Section 11 and remain credited interfaces.

Fibonacci spectral and Cassini identities, geometric series, polynomial root counting, finite differences, Newton and Hermite interpolation, real-rooted logarithmic concavity, elementary linear algebra, the intermediate value theorem, and the Euclidean Baire principle are established tools. The new structural synthesis uses them with the exact retained-clock relations; novelty is not claimed for those tools.

The complete proofs of the all-degree contribution are Sections 4–9; the exact residual equivalence is Section 10. The full moving-trace proof is in the supplied source, Sections 2–6, and is reproduced with the calibrated and prescribed-prefix hypotheses in the companion critical volume, Sections 12 and 16. The DEV frontier statements retain the source-contained proof regions VI, Sections 1–6 and VII, Sections 1–6 and their explicitly credited nested interfaces. The determinant obligation, residual all-degree decision, adaptive joint-word bounds, local larger-family questions and global complete-target sharpness remain as stated above.

## 追加锚（本行以下为增补区）

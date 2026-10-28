# FIB legal-edge load: observable quotients, conditional variance, and erasure summability

This volume proves a sufficient theorem for the actual output law of a stationary finite edge-emitting chain. Two labeled lumpability identities and two uniform bounds over feasible observed blocks imply summable square roots of one-sided output erasure errors. The proof uses classical stochastic-kernel strong data processing and an averaged conditional-variance identity. A triangular example satisfies these hypotheses while violating the proposed pathwise filter bound. It also fails the posterior band, so it is not a counterexample to any band-restricted assertion.

## 1. Standing scope and attribution

**Convention 1.1 (status).** This is a self-contained handwritten mathematical reference volume, not a machine-checked proof.

**Convention 1.2 (sources and contribution).** The original domain, edge clock, erasure fields, component interface, and open-goal notation come from [R]. This volume develops the sufficient quotient theorem, conditional-variance argument, triangular example, and actual stationary-filter and band calculations, together with the explicit correspondence between the stochastic-kernel argument and the original-law output errors. Full bibliographic and evidence boundaries appear in Section 10. Classical chi-square strong data processing, conditional projection, and Markov separation retain classical credit; neither these tools nor their assembly is asserted to have worldwide priority.

**Convention 1.3 (probability notation).** Vectors of probabilities are rows; $\mathbf1$ is the column of ones. For finite probability vectors,

$$
\operatorname{TV}(a,b)=\frac12\sum_i|a_i-b_i|.
$$

For general probability measures, TV is $\sup_E|a(E)-b(E)|$. Conditional expectations and probability kernels are identified almost surely under the law explicitly in use. Every nonnegative series below is initially interpreted in the extended nonnegative reals. An empty observed block generates the trivial field. We use $0^0=1$ in geometric bounds.

## 2. The original domain, clock, and output quantities

**Definition 2.1 (full finite producer domain).** For every integer $N\ge1$, let

$$
\Theta_N=\left\{(\lambda,M_0,M_1):
\lambda\ge0,\quad\lambda\mathbf1=1,\quad M_0,M_1\ge0,\quad
A=M_0+M_1,\quad A\mathbf1=\mathbf1,\quad
\lambda A=\lambda,\quad\lambda M_1^2\mathbf1=0\right\}.
\tag{2.1}
$$

Here $M_0,M_1$ are $N$ by $N$ real matrices. The last condition is the original scalar condition, not the stronger matrix requirement $M_1^2=0$. Structural zeros, zero stationary masses, reducibility, periodicity, and redundant representations are allowed.

The stationary two-sided joint law $J_\theta$ of hidden states $H_i$ and emitted bits $X_i$, $i\in\mathbb Z$, is specified by

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^{b}M_{x_i}(h_i,h_{i+1}).
\tag{2.2}
$$

Thus $X_i$ labels the edge $H_i\longrightarrow H_{i+1}$. In particular, the center variable $U=X_0$ labels $H_0\longrightarrow H_1$; it is not a state observation. Write $P=P_\theta$ for the visible marginal. For a word $w=x_1\cdots x_n$, put $M_w=M_{x_1}\cdots M_{x_n}$ and $M_\varnothing=I$. Then

$$
P(X_{a:a+n-1}=w)=\lambda M_w\mathbf1.
\tag{2.3}
$$

The scalar condition gives $P(X_i=X_{i+1}=1)=0$ for each $i$. A countable union shows that $P$ is supported on the two-sided no11 space. Word concatenation has probability $\lambda M_uM_v\mathbf1$; its seam is never replaced by a product of word marginals.

**Definition 2.2 (original-law erasure fields).** Under this same $P$, define

$$
\begin{aligned}
\mathcal E_0&=\sigma(X_i:i\ne0),&q_0&=\mathbb E_P[X_0\mid\mathcal E_0],\\
\mathcal L_j&=\sigma(X_{-j},\ldots,X_{-1},X_1,X_2,\ldots),&
p_j^L&=\mathbb E_P[X_0\mid\mathcal L_j],\\
\mathcal R_j&=\sigma(X_i:i\le-1,\ X_1,\ldots,X_j),&
p_j^R&=\mathbb E_P[X_0\mid\mathcal R_j],\\
e_L^P(j)&=\mathbb E_P[(q_0-p_j^L)^2],&
e_R^P(j)&=\mathbb E_P[(q_0-p_j^R)^2],\\
A_P(r)&=\sum_{j\ge r}\left(\sqrt{e_L^P(j)}+\sqrt{e_R^P(j)}\right),&
\tau_P(r)&=\sum_{j\ge r}\left(e_L^P(j)+e_R^P(j)\right).
\end{aligned}
\tag{2.4}
$$

Here $j,r$ are nonnegative integers. At $j=0$, $\mathcal L_0$ retains the entire right half-line and $\mathcal R_0$ retains the entire left half-line. Both omit the center. No posterior is recomputed under an altered visible law. On zero-probability conditioning fibers versions are arbitrary and have zero weight in every displayed expectation. Conditional projection shows that each $e_d^P(j)$ decreases to zero, but gives no summability rate by itself.

Explicitly, for finite exterior words $u=X_{-k:-1}$ and $v=X_{1:\ell}$ with positive joint probability, (2.2) gives

$$
\mathbb P(X_0=1\mid X_{-k:-1}=u,X_{1:\ell}=v)
=\frac{\lambda M_uM_1M_v\mathbf1}{\lambda M_u A M_v\mathbf1}.
$$

Thus the unobserved center edge is integrated by $A=M_0+M_1$, not deleted or replaced by an independent bit. Empty words are allowed, and the infinite-field posteriors are the corresponding bounded conditional-expectation limits.

**Definition 2.3 (posterior band).** Let $F_i=\{X_{i-1}=X_{i+1}=0\}$ and let $q_i$ be the translated full-exterior posterior. The band assertion is

$$
\mathsf B(P):\qquad q_i=0\text{ on }F_i^c,\qquad
\frac14\le q_i\le\frac12\text{ on }F_i,
\quad P\text{-almost surely for every }i\in\mathbb Z.
\tag{2.5}
$$

It is not an assumption of the sufficient theorem below. Its reported necessity for original-goal attainment is supplied background, not a result proved in this volume.

## 3. Actual components and labeled observable quotients

**Definition 3.1 (positive stationary component).** A finite stationary hidden chain has finitely many closed irreducible classes $C$ of positive stationary weight

$$
w_C=\sum_{s\in C}\lambda_s>0.
$$

All transient states have zero stationary mass. On $C$, set $\lambda^C_s=\lambda_s/w_C$ and $M_x^C=M_x|_{C\times C}$. These matrices and $\lambda^C$ specify the actual law conditional on belonging to $C$, denoted $J_C$, with visible law $P_C$. Each $\lambda^C_s$ is positive. Because a closed class has no outgoing $A$-edge, it has no outgoing $M_x$-edge, so the restricted matrices still sum to a stochastic matrix. The scalar no11 condition passes to each such class by nonnegativity. No parameter or visible observation is changed by this conditional decomposition.

For the remainder of this section fix $C$ and abbreviate its matrices and normalized stationary vector by $M_x$ and $\lambda$. Define the reverse labeled matrices on $C$ by

$$
\check M_x(s,t)=\frac{\lambda_t M_x(t,s)}{\lambda_s}.
\tag{3.1}
$$

They are defined only on this positive-mass class. Their sum is stochastic by stationarity. Reverse motion from $H_i$ to $H_{i-1}$ reads $X_{i-1}$, whereas forward motion from $H_i$ to $H_{i+1}$ reads $X_i$.

**Definition 3.2 (two labeled strong lumpability identities).** A quotient is a surjection $\pi:C\to S$ onto a finite set. Put $Q_i=\pi(H_i)$ and

$$
\bar\lambda_u=\sum_{s:\pi(s)=u}\lambda_s>0.
$$

Require nonnegative matrices $\bar M_x,\check{\bar M}_x$ on $S$ such that, for every $x\in\{0,1\}$, every $u,v\in S$, and every $s\in C$ with $\pi(s)=u$,

$$
\boxed{\ \sum_{t:\pi(t)=v} M_x(s,t)=\bar M_x(u,v)\ }
\qquad\text{(labeled forward strong lumpability)},
\tag{3.2}
$$

$$
\boxed{\ \sum_{t:\pi(t)=v} \check M_x(s,t)=\check{\bar M}_x(u,v)\ }
\qquad\text{(labeled reverse strong lumpability)}.
\tag{3.3}
$$

These are assumptions on the actual labeled matrices. The term observable quotient refers to preservation of the joint channels proved next; it does not assert that $Q_i$ can be recovered from visible data. Equality of marginal output laws alone is not a substitute for (3.2) and (3.3).

**Lemma 3.3 (actual quotient channel and reverse).** Under (3.2) and (3.3), $\bar A=\bar M_0+\bar M_1$ is stochastic, $\bar\lambda\bar A=\bar\lambda$, and

$$
\bar\lambda_u\check{\bar M}_x(u,v)
=\bar\lambda_v\bar M_x(v,u).
\tag{3.4}
$$

The actual joint marginal of $(Q,X)$ has cylinders

$$
J_C(Q_a=u_a,\ldots,Q_{b+1}=u_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\bar\lambda_{u_a}\prod_{i=a}^b\bar M_{x_i}(u_i,u_{i+1}).
\tag{3.5}
$$

At every cut $i$, the fields generated by $(Q_k:k\le i;X_k:k<i)$ and by $(Q_k:k\ge i;X_k:k\ge i)$ are conditionally independent given $Q_i$. Their finite left and right channel kernels are the products of $\check{\bar M}_x$ and $\bar M_x$, respectively.

**Proof.** Summing (3.2) over $v,x$ gives row sum one. Summing stationary flux over fibers gives stationarity and, using (3.3),

$$
\begin{aligned}
\bar\lambda_u\check{\bar M}_x(u,v)
&=\sum_{s:\pi(s)=u}\sum_{t:\pi(t)=v}\lambda_t M_x(t,s)\\
&=\sum_{t:\pi(t)=v}\lambda_t\bar M_x(v,u)
=\bar\lambda_v\bar M_x(v,u).
\end{aligned}
$$

To prove (3.5), sum the hidden cylinder (2.2) over the last hidden state in its prescribed fiber, using (3.2); repeat back to the first hidden state, whose masses sum to $\bar\lambda_{u_a}$. Equivalently, a finite right channel given $H_i=s$ depends only on $\pi(s)$ by repeated forward lumpability. Repeated reverse lumpability gives the corresponding statement for a finite left channel, including its quotient endpoint.

Under $J_C$ these two sides are independent given $H_i$. Both conditional channel factors are constant on the fiber of $\pi$. Averaging their product over $H_i$ conditional on $Q_i$ therefore preserves the product. This proves the stated independence for cylinders. A monotone-class argument in each side extends the identity to the generated fields and hence to full half-lines. All these spaces are finite or countable products of finite spaces, so the necessary regular conditional laws exist. This proves a joint conditional-channel statement on $J_C$, not only visible marginal equivalence. $\square$

**Definition 3.4 (feasible row diameter and block hypotheses).** For a nonzero nonnegative matrix $B$ with finite row and column sets, let

$$
I_B=\{u:(B\mathbf1)_u>0\},\qquad
K_B(u,v)=\frac{B(u,v)}{(B\mathbf1)_u}\quad(u\in I_B),
$$

and set

$$
\delta(B)=\max_{u,u'\in I_B}\operatorname{TV}\bigl(K_B(u,\cdot),K_B(u',\cdot)\bigr).
\tag{3.6}
$$

A single feasible row gives diameter zero. The zero matrix is excluded rather than assigned a contraction value. For the quotient word matrices below, both index sets are $S$.

For this component independently in each direction, assume integers $m_+,m_-\ge1$ and numbers $0\le\rho_+,\rho_-<1$ such that

$$
\begin{split}
&\text{for every }w\in\{0,1\}^{m_+}\text{ with }\bar\lambda\bar M_w\mathbf1>0,
\qquad\delta(\bar M_w)\le\rho_+,\\
&\text{for every }w\in\{0,1\}^{m_-}\text{ with }\bar\lambda\check{\bar M}_w\mathbf1>0,
\qquad\delta(\check{\bar M}_w)\le\rho_-.
\end{split}
\tag{3.7}
$$

In the second line, $w$ is read in reverse-motion order: its first letter is the first emitted label encountered going left. Matrix products follow that order. The lengths, contractions, quotient, and quotient state count may all depend on $C$ and on the original parameter $\theta$.

Since every $\bar\lambda_u>0$, a stationary word has positive probability exactly when its matrix is nonzero. Thus (3.7) covers every word that can receive positive probability after further conditioning. It assumes no positivity of every row, no aperiodicity, and no common terminal state. The identity quotient always meets (3.2) and (3.3); it need not meet (3.7).

## 4. The classical stochastic-kernel variance contraction

**Lemma 4.1 (Dobrushin bound for chi-square SDPI).** Let $K$ be a stochastic matrix between finite sets, and let

$$
d_K=\max_{i,h}\operatorname{TV}(K(i,\cdot),K(h,\cdot)).
$$

For probability vectors $a\ll b$,

$$
\chi^2(aK\Vert bK)\le d_K\chi^2(a\Vert b),\qquad
\chi^2(a\Vert b)=\sum_{i:b_i>0}\frac{a_i^2}{b_i}-1.
\tag{4.1}
$$

This is the chi-square specialization of the classical distribution-uniform Dobrushin SDPI, with exact Raginsky correspondence specified in Section 10. The proof below fixes the half-$L^1$ convention and pays zero coordinates explicitly.

**Proof.** For $t\ge0$, define

$$
h_t(a,b)=\sum_i(a_i-tb_i)_+-(1-t)_+.
$$

Write the signed vector $a-tb$ as $\alpha r-\beta s$, its positive and negative parts, where $r,s$ are probability vectors whenever the corresponding masses are nonzero. Then $\alpha-\beta=1-t$ and $h_t(a,b)=\min(\alpha,\beta)$.

If $\alpha\ge\beta>0$, the negative mass after applying $K$ is bounded by

$$
\sum_y\bigl(\beta(sK)_y-\alpha(rK)_y\bigr)_+
\le\beta\sum_y\bigl((sK)_y-(rK)_y\bigr)_+
=\beta\operatorname{TV}(sK,rK).
$$

If $\beta\ge\alpha>0$, use the positive mass instead to get $\alpha\operatorname{TV}(rK,sK)$. For any probability vectors $r,s$,

$$
\operatorname{TV}(rK,sK)
\le\sum_{i,h}r_i s_h\operatorname{TV}(K(i,\cdot),K(h,\cdot))
\le d_K.
$$

The total signed mass is preserved by $K$, so the smaller output sign mass is precisely $h_t(aK,bK)$. If one input sign mass is zero, the output remains one-sided and both $h_t$ values are zero. Consequently

$$
h_t(aK,bK)\le d_K h_t(a,b).
\tag{4.2}
$$

For $a\ll b$, discard coordinates $b_i=0$, which also have $a_i=0$. All remaining likelihood ratios are finite. Integrating the finite positive-part expressions gives

$$
2\int_0^\infty h_t(a,b)\,dt
=\sum_i\frac{a_i^2}{b_i}-1
=\chi^2(a\Vert b).
\tag{4.3}
$$

Indeed, the integral of $(a_i-tb_i)_+$ is $a_i^2/(2b_i)$ and that of $(1-t)_+$ is $1/2$; each vanishes past a finite threshold. Also $aK\ll bK$, so zero output coordinates can be discarded in the same way. Integrate (4.2) and use (4.3) on both sides. If one extends the assertion to infinite input divergence, the $d_K>0$ case is vacuous and the $d_K=0$ case is handled directly by identical kernel rows, without forming $0\cdot\infty$. $\square$

**Definition 4.2 (averaged predictive variance).** For a random variable $U\in\{0,1\}$, an observation $Z$, and a random element or field $V$, put

$$
\mathcal D(U;Z\mid V)
=\mathbb E\left[\bigl(\mathbb E[U\mid Z,V]-\mathbb E[U\mid V]\bigr)^2\right].
\tag{4.4}
$$

With trivial $V$ write $\mathcal D(U;Z)$. This is a scalar expectation over all the conditioning data. It is at most $\mathbb E\operatorname{Var}(U\mid V)\le1/4$.

**Lemma 4.3 (binary variance and the conditional-Markov premise).** If $U\longrightarrow Z\longrightarrow Z'$ is a Markov chain, with finite $Z,Z'$ and transition matrix $K$, then

$$
\mathcal D(U;Z')\le d_K\mathcal D(U;Z).
\tag{4.5}
$$

Its conditional form requires

$$
\mathbb P(Z'\in\cdot\mid U,Z,V)=K_V(Z,\cdot)
\quad\text{almost surely},\qquad
\operatorname{diam}_{\rm TV}(K_V)\le d\quad\text{almost surely}.
\tag{4.6}
$$

Under (4.6), $\mathcal D(U;Z'\mid V)\le d\mathcal D(U;Z\mid V)$.

**Proof.** Let $p=\mathbb P(U=1)$. If $p\in\{0,1\}$ both variances vanish. Otherwise set $a=\mathcal L(Z\mid U=1)$, $b=\mathcal L(Z)$. Since $b\ge pa$, $a\ll b$, and Bayes' formula gives

$$
\mathbb E[U\mid Z=i]=p\frac{a_i}{b_i},\qquad
\mathcal D(U;Z)=p^2\chi^2(a\Vert b).
\tag{4.7}
$$

The Markov premise gives the same representation at $Z'$ with $aK,bK$. Lemma 4.1 proves (4.5). Under (4.6), apply this proof on almost every $V$-fiber and integrate. The domination $b\ge pa$ holds fiberwise; null fibers and deterministic $U$ cause no exception. Rows outside the conditional support may be deleted, or extended by an existing feasible row without increasing the diameter. $\square$

**Counterexample 4.4 (conditioning can destroy Markov separation).** An unconditional Markov chain does not suffice for conditioning on an arbitrary $V$. Let $U,Y$ be independent fair bits, $Z$ constant, and $V=U\mathbin{\mathrm{xor}}Y$. Unconditionally $U\longrightarrow Z\longrightarrow Y$ has row diameter zero. Conditional on $V$, $Y$ determines $U$, while $Z$ supplies no information. Thus

$$
\mathcal D(U;Y\mid V)=\frac14,
\qquad\mathcal D(U;Z\mid V)=0.
$$

The conditional kernel of $Y$ given $U,Z,V$ depends on $U$, violating (4.6). In the application below, Lemma 3.3 proves the stronger separation needed for every conditioning step.

## 5. Observed blocks and the averaged variance budget

**Lemma 5.1 (observed-block recursion).** Let $U$ be binary, $Z,Z'$ finite, and $V$ any standard Borel conditioning data. Let $W$ range over a finite family of block words. Suppose nonnegative matrices $B_w$ satisfy $\sum_w B_w\mathbf1=\mathbf1$ and

$$
\mathbb P(W=w,Z'=t\mid Z=i,U,V)=B_w(i,t)
\quad\text{almost surely}.
\tag{5.1}
$$

Assume $\delta(B_w)\le\rho$ for every $w$ with positive probability, with $0\le\rho\le1$. Then

$$
\begin{aligned}
\mathcal D(U;Z'\mid V,W)
&\le\rho\mathcal D(U;Z\mid V,W)\\
&=\rho\bigl[\mathcal D(U;Z\mid V)-\mathcal D(U;W\mid V)\bigr]\\
&\le\rho\mathcal D(U;Z\mid V).
\end{aligned}
\tag{5.2}
$$

**Proof.** Fix a $V$-fiber with $b_v(i)=\mathbb P(Z=i\mid V=v)$. Conditioning further on a feasible word $w$ reweights this prior to

$$
\mathbb P(Z=i\mid V=v,W=w)
=\frac{b_v(i)(B_w\mathbf1)_i}
{\sum_h b_v(h)(B_w\mathbf1)_h}.
\tag{5.3}
$$

Zero-likelihood rows have zero mass. On feasible rows, (5.1) gives the conditional endpoint kernel

$$
\mathbb P(Z'=t\mid U,Z=i,V=v,W=w)
=K_w(i,t):=\frac{B_w(i,t)}{(B_w\mathbf1)_i}.
\tag{5.4}
$$

It is independent of $U,v$ and has diameter at most $\rho$. Extend any excluded row by a feasible row if needed. Lemma 4.3 applies conditional on $(V,W)$ and proves the first inequality in (5.2) after integrating over those data. No contraction is asserted for the nonlinear reweighting (5.3).

To identify its variance cost, put

$$
g=\mathbb E[U\mid Z,V],\qquad
h=\mathbb E[U\mid V,W],\qquad
a=\mathbb E[U\mid V].
$$

By (5.1), $W$ is independent of $U$ conditional on $(Z,V)$, hence $\mathbb E[U\mid Z,V,W]=g$ and $h=\mathbb E[g\mid V,W]$. Therefore

$$
\mathbb E[(g-h)(h-a)]=0,
\qquad
\mathbb E[(g-a)^2]=\mathbb E[(h-a)^2]+\mathbb E[(g-h)^2].
$$

These are exactly

$$
\mathcal D(U;Z\mid V)
=\mathcal D(U;W\mid V)+\mathcal D(U;Z\mid V,W).
\tag{5.5}
$$

Substitution proves the equality and last inequality in (5.2). The identity is averaged over the observed word. A comparison with the old variance on each individual realized word is not asserted or needed. $\square$

## 6. Same-law output erasure on one component

**Theorem 6.1 (sufficient observable-quotient erasure theorem).** Fix an actual positive stationary component $C$ of any $\theta\in\Theta_N$. Suppose it has a quotient satisfying both (3.2) and (3.3), and both all-feasible-word hypotheses (3.7). Then for every integer $j\ge0$,

$$
\boxed{\quad e_L^{P_C}(j)\le\frac14\rho_-^{\lfloor j/m_-\rfloor},
\qquad
e_R^{P_C}(j)\le\frac14\rho_+^{\lfloor j/m_+\rfloor}.\quad}
\tag{6.1}
$$

For every integer $r\ge0$,

$$
\boxed{\quad
A_{P_C}(r)\le\frac12\left[
\frac{m_-\rho_-^{\lfloor r/m_-\rfloor/2}}{1-\sqrt{\rho_-}}
+\frac{m_+\rho_+^{\lfloor r/m_+\rfloor/2}}{1-\sqrt{\rho_+}}
\right]<\infty.\quad}
\tag{6.2}
$$

Also

$$
\tau_{P_C}(r)\le\frac14\left[
\frac{m_-\rho_-^{\lfloor r/m_-\rfloor}}{1-\rho_-}
+\frac{m_+\rho_+^{\lfloor r/m_+\rfloor}}{1-\rho_+}
\right].
\tag{6.3}
$$

Left erasure uses the reverse constants; right erasure uses the forward constants. These are component-dependent bounds for the original emitted-bit indices, with the original center unobserved. They do not assert contraction of a normalized nonlinear filter map.

**Proof.** Work throughout on $J_C$ and let $U=X_0$. For left erasure set

$$
V_j^L=(X_{-j:-1},X_{1:\infty}),\qquad Z_j^L=Q_{-j},\qquad
\Delta_j^L=\mathcal D(U;Z_j^L\mid V_j^L).
\tag{6.4}
$$

At the cut $-j$, a next reverse block of length $m$ is

$$
W=(X_{-j-1},X_{-j-2},\ldots,X_{-j-m}),\qquad Z'=Q_{-j-m}.
$$

It lies to the left of the cut, whereas $(U,V_j^L)$ lies on the other side. Lemma 3.3 gives precisely (5.1), with $B_w=\check{\bar M}_w$. Summing these matrices over all length-$m$ binary words gives $(\check{\bar M}_0+\check{\bar M}_1)^m$, whose row sums are one, as required in Lemma 5.1. Joining $W$ to $V_j^L$ gives $V_{j+m}^L$ as a conditioning field. Every word of positive conditional probability has a nonzero matrix and so, for $m=m_-$, is covered by (3.7). Lemma 5.1 yields

$$
\Delta_{j+m_-}^L\le\rho_-\Delta_j^L.
\tag{6.5}
$$

Initially $V_0^L$ is the whole right half-line, and

$$
\Delta_0^L\le\mathbb E\operatorname{Var}(U\mid V_0^L)\le\frac14.
$$

For $j=km_-+s$, $0\le s<m_-$, first apply $k$ full reverse blocks. If $s>0$, apply one final block of length $s$; every normalized stochastic kernel has row diameter at most one, so Lemma 5.1 shows that this remainder cannot increase $\Delta$. If $s=0$ there is no remainder. Hence

$$
\Delta_j^L\le\frac14\rho_-^k.
\tag{6.6}
$$

It remains to connect this variance to the original output, rather than to an altered hidden comparison. Let

$$
T_j^L=X_{-\infty:-j-1},\qquad
g_j=\mathbb E[U\mid Q_{-j},V_j^L],\qquad
a_j=\mathbb E[U\mid V_j^L].
$$

The remote field $T_j^L$ is independent of $(U,V_j^L)$ given $Q_{-j}$ by Lemma 3.3. It follows that

$$
\mathbb E[U\mid T_j^L,V_j^L]
=\mathbb E[g_j\mid T_j^L,V_j^L].
$$

Subtract $a_j$, apply conditional Jensen, and integrate. Since $T_j^L$ joined to $V_j^L$ is exactly $\mathcal E_0$, while $V_j^L$ generates $\mathcal L_j$, this gives

$$
e_L^{P_C}(j)
=\mathcal D(U;T_j^L\mid V_j^L)
\le\mathcal D(U;Q_{-j}\mid V_j^L)=\Delta_j^L.
\tag{6.7}
$$

For right erasure, use instead

$$
V_j^R=(X_{-\infty:-1},X_{1:j}),\qquad Z_j^R=Q_{j+1},\qquad
T_j^R=X_{j+1:\infty}.
\tag{6.8}
$$

The center edge is on the left of the cut at $j+1$. The next block and endpoint are

$$
W=(X_{j+1},\ldots,X_{j+m}),\qquad Z'=Q_{j+m+1}.
$$

Lemma 3.3 now supplies (5.1) with the forward matrix $B_w=\bar M_w$. Start from $Q_1$ and $\mathcal D(U;Q_1\mid V_0^R)\le1/4$, use full blocks with $m_+,\rho_+$ and a remainder with coefficient one. The same Jensen argument with $T_j^R$ gives $e_R^{P_C}(j)\le\rho_+^{\lfloor j/m_+\rfloor}/4$. This proves (6.1).

All half-line identities above are valid directly by the cylinder extension in Lemma 3.3. The fields are countably generated and $U$ is bounded. Equivalently, truncate the opposite and remote half-lines, use the same uniform variance bounds, pass first through the remote truncation and then through the opposite truncation by bounded $L^2$ martingale convergence. No interchange of an uncontrolled random prefactor and an expectation is present. At $j=0$ the argument has no blocks and retains the opposite infinite half-line. When $\rho_\pm=0$, one complete block makes the corresponding variance and output error zero.

Taking square roots in (6.1) gives the coefficient $1/2$. For $0\le\rho<1$ and integer $m\ge1$, each floor value occurs at most $m$ times among $j\ge r$, whence

$$
\sum_{j\ge r}\rho^{\lfloor j/m\rfloor/2}
\le\frac{m\rho^{\lfloor r/m\rfloor/2}}{1-\sqrt\rho}.
$$

Sum the two directions to obtain (6.2). The same argument without square roots gives (6.3). This is a geometric estimate in original bit time, not in a changed observation clock. $\square$

## 7. Class mixtures, repeated visible laws, and periodicity

**Theorem 7.1 (actual mixture and original-law bounds).** Suppose every positive stationary closed class $C$ has its own quotient and constants satisfying Theorem 6.1. Then for every $j\ge0$ and $d\in\{L,R\}$,

$$
e_d^P(j)=\sum_C w_C e_d^{P_C}(j).
\tag{7.1}
$$

For every $r\ge0$,

$$
\max_C\sqrt{w_C}\,A_{P_C}(r)
\le A_P(r)
\le\sum_C\sqrt{w_C}\,A_{P_C}(r).
\tag{7.2}
$$

In particular,

$$
A_P(r)\le\frac12\sum_C\sqrt{w_C}\left[
\frac{m_{-,C}\rho_{-,C}^{\lfloor r/m_{-,C}\rfloor/2}}{1-\sqrt{\rho_{-,C}}}
+\frac{m_{+,C}\rho_{+,C}^{\lfloor r/m_{+,C}\rfloor/2}}{1-\sqrt{\rho_{+,C}}}
\right]<\infty.
\tag{7.3}
$$

The individual error bounds are the corresponding $w_C$-weighted sums of (6.1), and $\tau_P(r)=\sum_Cw_C\tau_{P_C}(r)$. None of these constants is asserted to be uniform over $\Theta_N$ or over the posterior band.

**Proof.** A stationary finite irreducible Markov chain is ergodic for the one-step shift even if it is periodic. Apply this classical fact to the labeled-edge chain with states $(s,x,t)$ for which $M_x(s,t)>0$ and transitions from $(s,x,t)$ to $(t,y,u)$ of probability $M_y(t,u)$. Its stationary mass at $(s,x,t)$ is $\lambda_sM_x(s,t)$. Irreducibility of the hidden class connects the endpoint of any positive labeled edge to the start of any other, so this finite labeled-edge chain is irreducible. The visible law is its factor, obtained by retaining the label coordinate, and is therefore stationary ergodic. This proves the assertion for every $P_C$ without an aperiodicity premise.

Merge repeated visible laws and write

$$
P=\sum_{\ell=1}^L v_\ell R_\ell,
$$

where the $R_\ell$ are distinct and $v_\ell>0$. For every finite visible word, the forward empirical frequency under $R_\ell$ converges almost surely to its $R_\ell$ cylinder probability. The countable collection of these frequencies identifies $R_\ell$ on the right half-line, since distinct visible laws differ on a cylinder. Therefore there is a right-half-line event $E_\ell^+$ of $R_\ell$ probability one and all other $R_k$ probabilities zero. The inverse shift gives a corresponding left-half-line event $E_\ell^-$.

For $B\in\mathcal L_j$, $E_\ell^+\in\mathcal L_j$ and the conditional expectation identity under $P$ gives

$$
0=\int_{B\cap E_\ell^+}(X_0-p_j^L)\,dP
=v_\ell\int_B(X_0-p_j^L)\,dR_\ell.
$$

Thus the $P$ version of $p_j^L$ restricts to an $R_\ell$ version. The same holds for $q_0$ since $E_\ell^+\in\mathcal E_0$. For $p_j^R$, use $E_\ell^-\in\mathcal R_j$. This works even at $j=0$, because the opposite half-line remains. Integrating the squared difference proves the error identity over distinct visible laws.

If several hidden classes have the same visible law, their $q_0,p_j^d,e_d(j)$ are the same visible-law functionals. Splitting the weight $v_\ell$ among these equal terms proves (7.1) over the actual hidden classes without claiming to observe their hidden labels. Hidden periodic phases are not separate visible ergodic labels.

For nonnegative numbers $a_C$, and any fixed $C_0$,

$$
\sqrt{w_{C_0}a_{C_0}}
\le\sqrt{\sum_Cw_Ca_C}
\le\sum_C\sqrt{w_Ca_C}.
$$

Apply these inequalities to (7.1), sum over both directions and $j\ge r$, and obtain (7.2). The number of classes is finite; inserting (6.2) proves (7.3). Nonnegative summation also proves the asserted $\tau$ identity. In particular, root summability of a finite mixture is equivalent to root summability of each positive-weight visible component, whether or not Theorem 6.1 supplies the latter. No aperiodicity assumption is needed. $\square$

## 8. Exact triangular example and the pathwise obstruction

**Lemma 8.1 (image diameter is not a Lipschitz constant).** For nonzero nonnegative $B$, define the normalized map on positive-likelihood priors by

$$
F_B(\nu)=\frac{\nu B}{\nu B\mathbf1},\qquad \nu B\mathbf1>0.
$$

Its image is exactly the convex hull of its feasible normalized rows, so its image TV diameter is $\delta(B)$. For $BC\ne0$,

$$
F_{BC}=F_C\circ F_B
\quad\text{on positive-product priors},\qquad
\delta(BC)\le\delta(C).
\tag{8.1}
$$

There is no general multiplicative inequality $\delta(BC)\le\delta(B)\delta(C)$.

**Proof.** Put $b_i=(B\mathbf1)_i>0$ on feasible rows and $r_i=B(i,\cdot)/b_i$. Then $F_B(\nu)$ is their convex combination with weights $\nu_i b_i/(\nu B\mathbf1)$. Conversely, any convex weights $a_i$ on feasible rows are realized by $\nu_i$ proportional to $a_i/b_i$. Convexity of TV bounds the distance between two such mixtures by the maximal pairwise row distance, and feasible point masses attain that maximum. The composition identity follows by canceling its intermediate denominator. Its image is contained in that of $F_C$, giving (8.1).

For the failure of multiplication, take

$$
B=C=\frac12\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

The normalized rows of $B$ are $(1/2,1/2)$ and $(0,1)$, so $\delta(B)=1/2$. Direct multiplication gives

$$
B^2=\frac14\begin{pmatrix}1&2\\0&1\end{pmatrix},\qquad
\delta(B^2)=\frac13>\frac14.
\tag{8.2}
$$

Inductively multiplying the triangular matrices gives, for every integer $k\ge0$,

$$
B^k=2^{-k}\begin{pmatrix}1&k\\0&1\end{pmatrix},\qquad
\delta(B^k)=\frac1{k+1}.
\tag{8.3}
$$

For $\nu_p=(p,1-p)$,

$$
F_B(\nu_p)=\left(\frac p{1+p},\frac1{1+p}\right),\qquad
\frac{\operatorname{TV}(F_B(\nu_p),F_B(\nu_q))}
{\operatorname{TV}(\nu_p,\nu_q)}
=\frac1{(1+p)(1+q)}\quad(p\ne q).
\tag{8.4}
$$

The supremum is one, by taking distinct $p,q$ approaching zero. Thus the map's TV Lipschitz constant is one although its image diameter is $1/2$. This distinction is exactly why image diameters cannot be multiplied through nonlinear filtering. $\square$

**Proposition 8.2 (original-domain embedding and output bound).** Set

$$
M_0=B=\frac12\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
M_1=\frac12\begin{pmatrix}0&0\\1&0\end{pmatrix},\qquad
\lambda=(1/2,1/2).
\tag{8.5}
$$

This is an irreducible original-domain producer in $\Theta_2$. Its identity quotient satisfies both labeled lumpability identities and (3.7) with $m_+=m_-=1$ and $\rho_+=\rho_-=1/2$. For its actual output law,

$$
e_L^P(j),e_R^P(j)\le\frac14\,2^{-j},\qquad
A_P(r)\le\frac{2^{-r/2}}{1-1/\sqrt2}.
\tag{8.6}
$$

At the same time every word $0^k$ has positive probability and its forward matrix diameter is $1/(k+1)$.

**Proof.** The matrix $A=M_0+M_1$ has both rows $(1/2,1/2)$, so it is stochastic, irreducible, and stationary under $\lambda$. Also $M_1^2=0$, which verifies the scalar legality condition. With the identity quotient, (3.2) and (3.3) hold exactly. Since $\lambda$ is uniform, $\check M_x=M_x^{\mathsf T}$. The forward $M_0$ has diameter $1/2$ by Lemma 8.1; the reverse $M_0$ has normalized rows $(1,0)$ and $(1/2,1/2)$, again with diameter $1/2$. Each of $M_1$ and $\check M_1$ has only one feasible row and thus diameter zero. Both one-letter words have positive stationary probability. This verifies every feasible word in each length-one hypothesis; Theorem 6.1 gives (8.6) with its exact directional correspondence and constants.

Finally, (8.3) gives

$$
P(0^k)=\lambda B^k\mathbf1=\frac{k+2}{2^{k+1}}>0.
\tag{8.7}
$$

The matrices of these actual words therefore also exhibit the nonmultiplicative image diameter inside the theorem's stated hypothesis class. Their small probabilities are compatible with the averaged output bound; no wordwise contraction was used to prove that bound. $\square$

**Counterexample 8.3 (actual stationary filters).** In the same stationary $J_\theta$, define

$$
\alpha_\infty=\mathcal L(H_0\mid X_{-\infty:-1}),\qquad
\alpha_j=\mathcal L(H_0\mid X_{-j:-1}).
$$

On the event

$$
E=\{X_{-7}=1,\ X_{-6:-1}=0^6\},
$$

one has

$$
J_\theta(E)=\frac7{256},\qquad
\alpha_\infty=(1/7,6/7),\qquad
\alpha_6=(1/8,7/8),\qquad
\operatorname{TV}(\alpha_\infty,\alpha_6)=\frac1{56}>\frac1{64}=(1/2)^6.
\tag{8.8}
$$

**Proof.** Emitting $1$ fixes its endpoint to hidden state $1$. Thus $X_{-7}=1$ fixes $H_{-6}=1$, and observations earlier than $-7$ no longer affect the conditional distribution at $H_0$ after the six specified zeros. By (8.3),

$$
\lambda M_1B^6=(1/256,6/256),\qquad
\frac{(1,0)B^6}{(1,0)B^6\mathbf1}=(1/7,6/7).
$$

The first row vector gives the event probability by summation. With only the six zeros observed, stationarity at $H_{-6}$ instead gives

$$
\alpha_6=\frac{\lambda B^6}{\lambda B^6\mathbf1}=(1/8,7/8).
$$

The binary TV distance is the absolute difference of the first coordinates, $1/56$. This is the actual full-past versus finite-past filter comparison under one stationary law, not a comparison of artificially chosen initial priors. It disproves the asserted bound $\operatorname{TV}(\alpha_\infty,\alpha_j)\le(1/2)^j$ on a positive-probability event. It does not assert failure of every possible almost-sure rate with a random prefactor, and it does not contradict (8.6). $\square$

**Counterexample 8.4 (the band boundary of this example).** The law (8.5) does not satisfy $\mathsf B(P)$. On the exterior event

$$
G=\{X_{-4}=X_4=1,\ X_{-3:-1}=X_{1:3}=000\},
$$

one has $P(G)=1/64$ and $q_0=9/16>1/2$.

**Proof.** For the two possible center bits, the finite cylinder masses are

$$
\begin{aligned}
P(G,X_0=1)&=\lambda M_1B^3M_1B^3M_1\mathbf1=\frac9{1024},\\
P(G,X_0=0)&=\lambda M_1B^3M_0B^3M_1\mathbf1=\frac7{1024}.
\end{aligned}
\tag{8.9}
$$

For example, $\lambda M_1B^3=(1/32,3/32)$. Multiplication by $M_1$ gives $(3/64,0)$, then by $B^3$ gives $(3/512,9/512)$; the final $M_1\mathbf1$ gives $9/1024$. Multiplication instead by $M_0$ gives $(1/64,4/64)$, then by $B^3$ gives $(1/512,7/512)$, hence $7/1024$.

The left boundary $1$ fixes $H_{-3}=1$ and the right boundary $1$ fixes $H_5=1$. More explicitly, $M_1$ has rank one, so any further finite left likelihood and right likelihood multiply both center masses by the same respective factors. They cancel in the conditional center ratio on every feasible exterior extension. Passing to the entire exterior by bounded conditional-expectation convergence preserves this ratio. Therefore

$$
q_0=\frac9{9+7}=\frac9{16}\quad\text{on }G,
\qquad P(G)=\frac{16}{1024}=\frac1{64}.
$$

Both immediate neighbors of the center are zero on $G$, so the upper band bound fails there. This prevents the example from being used as a counterexample to a band-restricted theorem. It does not repair the failed composition step, which already fails within the explicit two-sided block hypotheses. The example has finite output root sum by Proposition 8.2; no divergent root sum is claimed. $\square$

## 9. Original-goal boundaries and unapplied hypotheses

**Definition 9.1 (full open-path optimization target).** For $n\ge1$, let

$$
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\text{ for }1\le i<n\}.
$$

The graph $\Gamma_n$ has every word in $B_n$ as a vertex and every legal Hamming-one pair as an edge. Endpoint tests use $w_0=w_{n+1}=0$; the first and last positions are not joined. On the entire probability simplex $\mathcal P(B_n)$, put

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}
\qquad
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}h(\mu_w,\mu_z),
\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu).
\tag{9.1}
$$

Zero mass does not remove vertices, edges, or seams. The original target uses $c_\star=\lim_{n\to\infty}\kappa_n/n$, whose existence is part of the supplied original-goal background. These open-path quantities are not changed by the quotient construction.

**Open problem 9.2 (universal root summability).** The two assertions

$$
\begin{aligned}
\mathsf Q_{\rm full}:&\quad
\forall N\ge1\ \forall\theta\in\Theta_N,\quad A_{P_\theta}(0)<\infty,\\
\mathsf Q_{\rm band}:&\quad
\forall N\ge1\ \forall\theta\in\Theta_N,\quad
\mathsf B(P_\theta)\Longrightarrow A_{P_\theta}(0)<\infty
\end{aligned}
\tag{9.2}
$$

remain unresolved here. For a proposed application of Theorem 7.1, each actual positive component must separately supply a quotient satisfying both labeled identities and both all-feasible-word bounds. No implication from the posterior band to those combined hypotheses is proved. A failure to find a quotient or a contracting block is not a divergent-root-sum example.

**Statement 9.3 (retained original all-$N$ alternative).** In the notation of the original-goal interface of [R], $d(P)$ is its stationary density functional and $D_r(P)$ its finite-window upper functional. Write

$$
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta).
$$

The full original alternative is whether some finite $N$ and $\theta\in\Theta_N$ attain $d(P_\theta)=c_\star$, or whether $C_N<c_\star$ for every finite $N$. The attributed equivalent formulation of the latter is

$$
\forall N\ge1\ \exists r,m\ge1:\qquad
U_{N,r}<\frac{\kappa_m}{m+1}.
\tag{9.3}
$$

This is an attributed statement of the original problem, not a theorem established here. This volume does not expand the definitions of $d,D_r$ or prove this equivalence; they are retained only as supplier symbols in this paragraph and are not inputs to any proof above. In particular, no new definition of either functional is silently substituted. The standalone erasure theorem is expressed entirely through the fully defined quantities (2.1)–(2.4).

A hypothetical attainer must still establish the quotient and contraction assumptions before using this sufficient theorem. Neither alternative in Statement 9.3 is decided. The volume proves no strict enlargement of other sufficient classes, optimizer-rank growth, nonzero intrinsic-null response, strong-zero property, higher-order continuation obligation, or global continuation bridge. The rectangular-word theorem and flag-block estimates of [R] are not premises of any proof here. Their classes are not compared for strict inclusion. No empirical machine-learning claim is made.

## 10. Sources, exact classical correspondence, and evidence limits

**Attribution 10.1 (project and classical scope).** The following are distinct sources with distinct roles.

| Source | Exact use and boundary |
| --- | --- |
| [R] *FIB 合法边调和负载：单侧擦除可和性与输出滤波边界*, `docs/develop/theory/FIB_LEGAL_EDGE_LOAD_ONE_SIDED_ERASURE_SUMMABILITY_AND_OUTPUT_FILTER_BOUNDARIES.md` | Original $\Theta_N$, $J_\theta/P_\theta$, open-path target, erasure fields, band notation, actual-component interface, and original open alternatives. The component statement is proved here in Theorem 7.1. No rectangular-word, flag-block, loss, response, or higher-order theorem is imported as a premise. Its nested sources are not independently certified by this volume. |
| Maxim Raginsky, *Strong Data Processing Inequalities and $\Phi$-Sobolev Inequalities for Discrete Channels*, arXiv:1411.3575v4, [versioned primary text](https://arxiv.org/html/1411.3575v4), [version metadata](https://arxiv.org/abs/1411.3575) | Section 2's chi-square $\Phi$-divergence, Definition 3.1, and Section 3.1 Theorem 3.1, equations (3.8)–(3.9), give the distribution-uniform bound used in Lemma 4.1. Lemma 4.1 gives a complete handwritten proof of the needed specialization. |
| Cohen, Iwasa, Rautu, Ruskai, Seneta, and Zbaganu, *Relative entropy under mappings by stochastic matrices*, Linear Algebra and its Applications 179 (1993), 211–235 | Earlier attribution given by Raginsky Section 3.1, reference [6]. This secondary citation supplies no additional theorem premise for the proof. No priority conclusion is inferred from the citation chain. |
| Conditional expectation as orthogonal projection, finite-chain stationary decomposition, the ergodic theorem, and Markov data processing | Classical tools used with the laws and fields explicitly specified above. They are not claimed as new mathematical content. |

**Correspondence 10.2 (Raginsky Theorem 3.1).** Raginsky's channel $K(\cdot\mid x)$ is the row $K(x,\cdot)$ of Lemma 4.1. His Dobrushin coefficient is

$$
\vartheta(K)=\max_{x,x'}\operatorname{TV}(K(\cdot\mid x),K(\cdot\mid x'))=d_K.
$$

His distribution-uniform coefficient $\eta_\Phi(K)$ is the supremum of output/input $\Phi$-divergence ratios over admissible reference and input laws. His reference law $\mu$ corresponds to $b$ and the competing law $\nu$ to $a$. Taking $\Phi(u)=(u-1)^2$ gives $D_\Phi(a\Vert b)=\chi^2(a\Vert b)$. Theorem 3.1 states $\eta_\Phi(K)\le\vartheta(K)$; hence its specialization is exactly (4.1), with coefficient $d_K$, not $d_K^2$. In the block application, $K=K_w$, so $d_K=\delta(B_w)$.

Raginsky's positive-reference formulation is matched by restricting to the support of $b$ and then to the support of $bK$. Removing zero coordinates preserves the divergence and can only decrease the row-diameter bound. Lemma 4.1 also proves this extension directly. The binary identity (4.7) transfers that classical inequality to predictive variance. Lemma 5.1 then accounts for the observation's likelihood reweighting by the exact averaged budget (5.5), and Lemma 3.3 plus Theorem 6.1 place it on the original-law channel. This application and its explicit original-clock correspondence are the synthesis retained in this volume; they are not a new classical SDPI.

The proof uses the explicit $h_t$ identity (4.3) throughout. It imports no statistical-information normalization formula from the primary text, so the half-$L^1$ convention is fixed without ambiguity. Nested references are not independently certified here. Evidence for the displayed matrix products and rational values is limited to the handwritten proofs given here.

## 追加锚（本行以下为增补区）


## 11. Forward-only quotient laws and a legal $\Theta_4$ witness

**Proposition 11.1 (forward-only quotient-law reduction).** Fix a finite positive stationary irreducible component $C$, with positive stationary vector $\lambda$, labeled matrices $M_0,M_1$, and visible law $P_C$. Let $\pi:C\to S$ be surjective and suppose only the forward labeled strong lumpability identities (3.2). Define

$$
\bar\lambda_u=\sum_{s:\pi(s)=u}\lambda_s,
\qquad
\sum_{t:\pi(t)=v}M_x(s,t)=\bar M_x(u,v)
\quad (\pi(s)=u).
$$

Then $\bar A=\bar M_0+\bar M_1$ is stochastic, $\bar\lambda\bar A=\bar\lambda$, and $\bar\lambda_u>0$. The quotient producer $\bar\theta=(\bar\lambda,\bar M_0,\bar M_1)$ is in the same legal class $\Theta_{|S|}$, and its visible law equals $P_C$. Its canonical stationary reverse is the family

$$
R_x(u,v)=
\frac{\bar\lambda_v\,\bar M_x(v,u)}{\bar\lambda_u}.
\tag{11.1}
$$

Thus $R_0+R_1$ is stochastic and $\bar\lambda_uR_x(u,v)=\bar\lambda_v\bar M_x(v,u)$. If the forward matrices $\bar M_x$ and the canonical reverse matrices $R_x$ satisfy the two all-feasible-word diameter hypotheses (3.7), with constants $m_\pm,\rho_\pm$, then the original visible law $P_C$ satisfies exactly the bounds (6.1)--(6.3), with those constants. If every positive stationary component of an original producer has such a forward quotient and such constants, the mixture conclusion (7.1)--(7.3) applies.

**Proof.** Summing (3.2) over $v$ and $x$ gives the row sums of $\bar A$. Summing the stationary flux over the fibers gives $\bar\lambda\bar A=\bar\lambda$. For a quotient-state cylinder, repeated use of (3.2) gives

$$
\begin{aligned}
&J_C(Q_a=u_a,\ldots,Q_{b+1}=u_{b+1},X_a=x_a,\ldots,X_b=x_b)\\
&\qquad=\bar\lambda_{u_a}\prod_{i=a}^{b}\bar M_{x_i}(u_i,u_{i+1}),
\end{aligned}
\tag{11.2}
$$

where $Q_i=\pi(H_i)$. Summing (11.2) over the quotient endpoints proves equality of all visible cylinders with the quotient producer. In particular,

$$
\bar\lambda\bar M_1^2\mathbf 1
 =P_C(X_0=X_1=1)=0,
$$

so the quotient remains in $\Theta_{|S|}$. Irreducibility passes to the quotient: a positive hidden $A$-path between two fibers maps to a positive quotient path. Formula (11.1) is well-defined because every $\bar\lambda_u$ is positive; stationarity gives

$$
\sum_{v,x}R_x(u,v)
 =\frac{1}{\bar\lambda_u}\sum_v\bar\lambda_v\bar A(v,u)=1.
$$

The identity quotient of $\bar\theta$ satisfies both labeled identities, with its reverse matrices equal to $R_x$. Applying Theorem 6.1 to this quotient producer yields (6.1)--(6.3) for its visible law. Equation (11.2) identifies that law with $P_C$, so the same bounds hold for the original component; Theorem 7.1 then gives the stated finite-mixture conclusion when the condition holds componentwise. This argument does not claim that the hidden reverse matrices $\check M_x$ are constant on fibers. It uses no new variance proof: the conditional-variance argument is exactly the one already contained in Theorem 6.1. $\square$

**Proposition 11.2 (a legal $\Theta_4$ representation with a forward quotient).** In state order $0,1,2,3$, set

$$
M_0=
\begin{pmatrix}
\frac12&0&\frac12&0\\
0&\frac12&0&\frac12\\
0&0&0&\frac12\\
0&0&\frac12&0
\end{pmatrix},
\qquad
M_1=
\begin{pmatrix}
0&0&0&0\\
0&0&0&0\\
0&\frac12&0&0\\
\frac18&\frac38&0&0
\end{pmatrix},
\qquad
\lambda=\left(\frac1{13},\frac{11}{26},\frac5{26},\frac4{13}\right).
\tag{11.3}
$$

Then $A=M_0+M_1$ is stochastic, $\lambda A=\lambda$, $M_1^2=0$, and $A$ is irreducible; hence (11.3) is a legal positive stationary $\Theta_4$ witness. Let $\pi=\{0,1\}\mid\{2,3\}$. Its forward quotient has

$$
\bar\lambda=\left(\frac12,\frac12\right),
\qquad
\bar M_0=\frac12\begin{pmatrix}1&1\\0&1\end{pmatrix},
\qquad
\bar M_1=\frac12\begin{pmatrix}0&0\\1&0\end{pmatrix},
\tag{11.4}
$$

and the canonical reverse in (11.1) is

$$
R_0=\frac12\begin{pmatrix}1&0\\1&1\end{pmatrix},
\qquad
R_1=\frac12\begin{pmatrix}0&1\\0&0\end{pmatrix}.
\tag{11.5}
$$

The feasible-row diameters of $\bar M_0,R_0$ are $1/2$, and those of $\bar M_1,R_1$ are $0$. Thus (3.7) holds with $m_+=m_-=1$ and $\rho_+=\rho_-=1/2$, and Proposition 11.1 transfers (6.1)--(6.3) to this representation's visible law.

**Proof.** Explicitly,

$$
A=
\begin{pmatrix}
\frac12&0&\frac12&0\\
0&\frac12&0&\frac12\\
0&\frac12&0&\frac12\\
\frac18&\frac38&\frac12&0
\end{pmatrix},
\qquad
\lambda A=\left(\frac1{13},\frac{11}{26},\frac5{26},\frac4{13}\right).
$$

Every row of $A$ sums to one. The range of $M_1$ is contained in the span of the first two coordinate vectors, whose rows in $M_1$ vanish, so $M_1^2=0$ and therefore $\lambda M_1^2\mathbf1=0$. The positive paths $0\to2\to1\to3\to0$ and $3\to2$ show irreducibility. Aggregating the rows of (11.3) over the two fibers gives (11.4); since $\bar\lambda$ is uniform, (11.5) is the transpose family. For $\bar M_0$ and $R_0$, the two normalized feasible rows differ by TV $1/2$; each of $\bar M_1,R_1$ has one feasible row and hence diameter zero. $\square$

The hidden reverse identity (3.3) fails for this same $\pi$. From (3.1), the relevant rows are

$$
\check M_0(2,\cdot)=\left(\frac15,0,0,\frac45\right),
\qquad
\check M_0(3,\cdot)=\left(0,\frac{11}{16},\frac5{16},0\right).
$$

Their reverse $M_0$-mass into the fiber $\{0,1\}$ is $1/5$ and $11/16$, respectively. Hence no hidden reverse channel is fiber-constant here; the canonical quotient reverse in (11.5) is the object used by Proposition 11.1.

For the identity quotient, every $m\ge1$ fails (3.7) in both directions. The rows $2,3$ of $M_0^m$, after normalization, are the two alternating point masses, so $\delta(M_0^m)=1$. The rows $0,1$ of the hidden reverse $\check M_0^m$, after normalization, are the point masses at $0,1$, so $\delta(\check M_0^m)=1$. These are feasible because

$$
(M_0^m\mathbf1)_0=(M_0^m\mathbf1)_1=\frac{m+1}{2^m},
\qquad
(M_0^m\mathbf1)_2=(M_0^m\mathbf1)_3=\frac1{2^m},
$$

and therefore

$$
P(0^m)=\lambda M_0^m\mathbf1=\frac{m+2}{2^{m+1}}>0.
\tag{11.6}
$$

The reverse word has the same positive probability by stationarity. Finally, every forward-labeled strongly lumpable partition refines $\{0,1\}\mid\{2,3\}$: label $1$ has total outgoing mass $0$ from $0,1$ and $1/2$ from $2,3$, so a block cannot cross these fibers. If $0,1$ were merged while $2,3$ were split, their $M_0$-masses into the block containing $2$ would be $1/2$ and $0$. If $2,3$ were merged while $0,1$ were split, their $M_1$-masses into the block containing $0$ would be $0$ and $1/8$. Thus the only forward-lumpable partitions are the identity and $\pi$. The identity fails the diameter hypotheses by (11.6), while $\pi$ fails hidden reverse lumpability by $1/5\ne11/16$; no deterministic quotient of this fixed representation satisfies the old combined criterion (3.2), (3.3), and (3.7).

This obstruction is representation-level only. The quotient matrices (11.4) are exactly the producer in Proposition 8.2, so (11.3) has the same visible law as that triangular example and does not enlarge the output-law class. Its band failure is retained: by Counterexample 8.4, the exterior event $G$ has probability $1/64$ and $q_0=9/16>1/2$. Consequently this witness resolves neither $\mathsf Q_{\rm full}$ nor $\mathsf Q_{\rm band}$, and it claims no divergent root sum.

**Open Question 11.3 (band-preserving obstructions and averaged criteria).** For a legal producer whose visible law satisfies $\mathsf B(P)$, must every positive stationary component admit a forward-labeled quotient whose canonical reverse and forward matrices satisfy (3.7), or can a band-preserving component make every such deterministic quotient fail? If the latter obstruction exists, can a stationary-word-weighted (averaged) diameter condition still imply the bounds (6.1)--(6.3)? This is the next exact question; no answer is asserted here.

**Attribution 11.4.** Proposition 11.1 reuses Definition 3.2's forward identity, the cylinder calculation of Lemma 3.3, and Theorems 6.1 and 7.1. Proposition 11.2 is a direct $\Theta_4$ calculation from Definitions 2.1 and 3.1; its visible-law and band comparisons use Proposition 8.2 and Counterexample 8.4. No hidden reverse lumpability, new variance argument, or resolution of either open assertion is claimed.


## 12. Posterior-variance-weighted block contraction

**Lemma 12.1 (conditional variance-weighted block contraction).** Use the setup of Lemma 5.1: $U$ is binary, $Z,Z'$ are finite, $V$ is conditioning data, $W$ ranges over a finite family of words, and the matrices $B_w$ satisfy (5.1) and $\sum_wB_w\mathbf1=\mathbf1$. For almost every $V=v$, put

$$
p_v(w)=\mathbb P(W=w\mid V=v),\qquad
\Delta_w(v)=\mathcal D(U;Z\mid V=v,W=w)\quad(p_v(w)>0),
\qquad
\Delta(v)=\sum_{w:p_v(w)>0} p_v(w)\Delta_w(v).
\tag{12.1}
$$

Assume $0\le\delta(B_w)\le1$ for every $w$ with $p_v(w)>0$, and that, for some $0\le\kappa<1$,

$$
\sum_{w:p_v(w)>0} p_v(w)\,\delta(B_w)\,\Delta_w(v)
\le \kappa\,\Delta(v)
\tag{12.2}
$$

for almost every $v$ with $\Delta(v)>0$. All sums involving $\Delta_w(v)$ range over positive-probability words; zero-probability conditional versions are omitted. No diameter or conditional variance is assigned to a null word; in particular, the zero matrix remains excluded as in Definition 3.4. Fibers with $\Delta(v)=0$ are vacuous: every $\Delta_w(v)$ with positive $p_v(w)$ is then zero. Under these assumptions,

$$
\mathcal D(U;Z'\mid V,W)
\le
\kappa\bigl[\mathcal D(U;Z\mid V)-\mathcal D(U;W\mid V)\bigr]
\le
\kappa\,\mathcal D(U;Z\mid V).
\tag{12.3}
$$

The hypothesis (12.2) is fiberwise in the posterior variances. It is not a stationary word average.

**Proof.** Fix a $V=v$ fiber and a word $w$ of positive conditional probability. The conditional kernel in (5.4) has row diameter $\delta(B_w)$, so the conditional form of Lemma 4.3, applied on this $(v,w)$-fiber, gives

$$
\mathcal D(U;Z'\mid V=v,W=w)
\le \delta(B_w)\Delta_w(v).
$$

Multiply by $p_v(w)$, sum over $w$, and use (12.2). Integrating over $v$ gives

$$
\mathcal D(U;Z'\mid V,W)\le\kappa\,\mathcal D(U;Z\mid V,W).
$$

The variance identity (5.5) rewrites the last factor as
$\mathcal D(U;Z\mid V)-\mathcal D(U;W\mid V)$, and dropping the nonnegative term $\mathcal D(U;W\mid V)$ gives (12.3). No comparison of the reweighted priors in (5.3) is used. $\square$

**Corollary 12.2 (good/bad sufficient condition).** In the setup of Lemma 12.1, let the word family be split into good and bad words, $G\sqcup H$. Suppose $0\le\rho,\eta\le1$,

$$
\delta(B_w)\le\rho\quad(w\in G,\ p_v(w)>0),
\qquad
\sum_{w\in H,\ p_v(w)>0}p_v(w)\Delta_w(v)\le\eta\,\Delta(v)
\tag{12.4}
$$

for almost every $v$. Then (12.2) holds with

$$
\kappa=\rho+(1-\rho)\eta.
\tag{12.5}
$$

In particular, if $\rho+(1-\rho)\eta<1$, Lemma 12.1 gives strict contraction.

**Proof.** Since every diameter is at most one,

$$
\begin{aligned}
\sum_{w:p_v(w)>0}p_v(w)\delta(B_w)\Delta_w(v)
&\le \rho\sum_{w\in G,\ p_v(w)>0}p_v(w)\Delta_w(v)
   +\sum_{w\in H,\ p_v(w)>0}p_v(w)\Delta_w(v)\\
&=\rho\left(\Delta(v)-\sum_{w\in H,\ p_v(w)>0}p_v(w)\Delta_w(v)\right)
  +\sum_{w\in H,\ p_v(w)>0}p_v(w)\Delta_w(v)\\
&\le \rho\Delta(v)+(1-\rho)\eta\Delta(v).
\end{aligned}
$$

This is (12.2) with (12.5). The endpoint cases $\rho=0,1$ and $\eta=0,1$ are included. $\square$

**Theorem 12.3 (directional quotient application).** Fix a positive stationary component and a quotient as in Proposition 11.1. For the left direction, use exactly

$$
V_j^L=(X_{-j:-1},X_{1:\infty}),\qquad
Z_j^L=Q_{-j}
$$

from (6.4), and put

$$
W_j^L=(X_{-j-1},\ldots,X_{-j-m_-}),
\qquad
Z_{j+m_-}^L=Q_{-j-m_-}.
$$

For the right direction, use exactly

$$
V_j^R=(X_{-\infty:-1},X_{1:j}),\qquad
Z_j^R=Q_{j+1}
$$

from (6.8), and put

$$
W_j^R=(X_{j+1},\ldots,X_{j+m_+}),
\qquad
Z_{j+m_+}^R=Q_{j+m_++1}.
$$

Suppose that, in each direction $d\in\{L,R\}$, there is a positive integer block length $m_d\ge1$ ($m_L=m_-$ and $m_R=m_+$), a good word set $G_d$, numbers $0\le\rho_d,\eta_d\le1$, and

$$
\kappa_d=\rho_d+(1-\rho_d)\eta_d<1
\tag{12.6}
$$

such that every good word of positive conditional probability has the corresponding quotient diameter at most $\rho_d$, and for every recursion cut $j\ge0$ the conditional bad-word variance inequality

$$
\sum_{\substack{w\notin G_d\\p_{j,v}^d(w)>0}}
p_{j,v}^d(w)\,\Delta_{j,w}^d(v)
\le \eta_d\,\Delta_j^d(v)
\tag{12.7}
$$

holds for almost every $v$. Here $p_{j,v}^d(w)$, $\Delta_{j,w}^d(v)$, and $\Delta_j^d(v)$ are the quantities in (12.1) formed from $V_j^d,Z_j^d,W_j^d$.

Then, for every $j\ge0$,

$$
e_L^{P_C}(j)\le\frac14\kappa_-^{\lfloor j/m_-\rfloor},
\qquad
e_R^{P_C}(j)\le\frac14\kappa_+^{\lfloor j/m_+\rfloor}.
\tag{12.8}
$$

Consequently, for every $r\ge0$,

$$
A_{P_C}(r)\le\frac12\left[
\frac{m_-\kappa_-^{\lfloor r/m_-\rfloor/2}}{1-\sqrt{\kappa_-}}
+
\frac{m_+\kappa_+^{\lfloor r/m_+\rfloor/2}}{1-\sqrt{\kappa_+}}
\right],
\tag{12.9}
$$

and

$$
\tau_{P_C}(r)\le\frac14\left[
\frac{m_-\kappa_-^{\lfloor r/m_-\rfloor}}{1-\kappa_-}
+
\frac{m_+\kappa_+^{\lfloor r/m_+\rfloor}}{1-\kappa_+}
\right].
\tag{12.10}
$$

If every positive stationary component satisfies these directional conditions, the finite-mixture conclusions of Theorem 7.1 apply with the component-specific constants.

**Proof.** Work on the quotient producer of Proposition 11.1, whose joint $(Q,X)$ law is (11.2). Apply Lemma 3.3 to its identity quotient and canonical reverse (11.1); no reverse lumpability of the original hidden representation is assumed. This supplies (5.1) at each left cut with $B_w=R_w$ and at each right cut with $B_w=\bar M_w$. Corollary 12.2 and (12.7) give the one-block recursions

$$
\mathcal D(U;Z_{j+m_-}^L\mid V_j^L,W_j^L)
\le\kappa_-\mathcal D(U;Z_j^L\mid V_j^L),
$$

and

$$
\mathcal D(U;Z_{j+m_+}^R\mid V_j^R,W_j^R)
\le\kappa_+\mathcal D(U;Z_j^R\mid V_j^R).
$$

The Jensen step in the proof of Theorem 6.1 transfers these quotient-state variances to the original output erasure errors. Starting from the $1/4$ variance bound at the initial cut, iterate complete blocks; a remainder of length smaller than $m_d$ has coefficient at most one. This proves (12.8). The geometric tail sums are exactly the estimates used for (6.2) and (6.3), with $\rho_\pm$ replaced by $\kappa_\pm$. No variance proof is added beyond Lemma 12.1, and no stationary word-average condition replaces the cutwise requirement (12.7). $\square$

**Warning 12.3A (stationary word diameter alone does not contract).** The following is an abstract block example, not an FIB producer. Let $V$ be trivial, let $0<\varepsilon<1$, let $R\sim\operatorname{Bernoulli}(\varepsilon)$, and let $U$ be a fair bit independent of $R$. Set

$$
Z=
\begin{cases}
\star,&R=0,\\
(1,U),&R=1,
\end{cases}
\qquad
W=
\begin{cases}
g,&R=0,\\
b,&R=1.
\end{cases}
$$

Use endpoint alphabet $\{\mathsf c,(1,0),(1,1)\}$. Define complementary substochastic kernels by
$$
B_g(\star,\mathsf c)=1,\qquad B_g(i,t)=0\ \text{for every other input row }i,
$$
and
$$
B_b(\star,t)=0\ \text{for every }t,\qquad
B_b((1,u),(1,u))=1\ (u\in\{0,1\}),
$$
with all other $B_b$-entries zero. Thus $\sum_wB_w\mathbf1=\mathbf1$: $B_g$ is constant on its only feasible row and $B_b$ is identity on its feasible rows. Let $Z'$ be the corresponding output. Then $W$ is determined by $Z$, so the premise (5.1) holds. The word probabilities are $1-\varepsilon,\varepsilon$, and

$$
\delta(B_g)=0,\qquad \delta(B_b)=1,
\qquad
(1-\varepsilon)\delta(B_g)+\varepsilon\delta(B_b)=\varepsilon.
$$

Nevertheless,

$$
\mathcal D(U;Z)=\frac{\varepsilon}{4},
\qquad
\mathcal D(U;Z'\mid W)=\frac{\varepsilon}{4}.
\tag{12.11}
$$

Indeed, only the $b$-fiber reveals $U$, while the $g$-fiber is constant. Thus an unweighted stationary word-diameter average, even when equal to $\varepsilon<1$, gives no contraction. This warning concerns the abstract block lemma and is not a counterexample to any FIB statement.

**Open Question 12.4 (band-preserving fiberwise concentration).** Under the posterior band $\mathsf B(P)$, can a forward/canonical-reverse quotient satisfy the fiberwise weighted condition (12.7) uniformly at all shifted cuts, or can bad-word variance concentration persist? The assertions $\mathsf Q_{\rm full}$ and $\mathsf Q_{\rm band}$ remain open; no universal tail result is claimed.

**Attribution 12.5.** Lemma 12.1 is the posterior-variance refinement of Lemma 5.1, using the conditional SDPI in Lemma 4.3 and the variance identity (5.5). Theorem 12.3 reuses Lemma 3.3, Proposition 11.1, the Jensen and tail steps of Theorem 6.1, and the existing geometric sums (6.2)--(6.3). Warning 12.3A is abstract and supplies no FIB producer or resolution of either open assertion.

## 13. A band-preserving phase obstruction and its conditional support

**Proposition 13.1 (an actual periodic producer in the posterior band).** Order the states as

$$
A=(0,0),\quad B=(0,1),\quad C=(1,0),\quad D=(1,1),
$$

where $H_i=(S_i,X_{i-1})$ records a phase and the previous emitted bit. Set

$$
M_0=\begin{pmatrix}
0&0&3/4&0\\
0&0&1&0\\
2/3&0&0&0\\
1&0&0&0
\end{pmatrix},\qquad
M_1=\begin{pmatrix}
0&0&0&1/4\\
0&0&0&0\\
0&1/3&0&0\\
0&0&0&0
\end{pmatrix},\qquad
\lambda=\frac1{22}(8,3,9,2).
\tag{13.1}
$$

This is a stationary legal irreducible producer in $\Theta_4$, of period exactly two. Either infinite observed half-line determines $S_0$ almost surely. Its full-exterior posterior is

$$
q_0=\begin{cases}
1/3,&X_{-1}=X_1=0,\ S_0=0,\\
2/5,&X_{-1}=X_1=0,\ S_0=1,\\
0,&\{X_{-1}=X_1=0\}^{c}.
\end{cases}
\tag{13.2}
$$

In particular its visible law satisfies the original band $\mathsf B(P)$.

**Proof.** Every row of $A=M_0+M_1$ sums to one, and multiplication gives

$$
\lambda A=\frac1{22}(9\cdot2/3+2,\ 9/3,\ 8\cdot3/4+3,\ 8/4)
=\frac1{22}(8,3,9,2).
$$

Also $M_1^2=0$. The cycle $A\to D\to A$ and the paths $A\to C\to B\to C\to A$ connect all states. Every transition changes phase, so every return length is even; the two-step return at $A$ makes the period exactly two. These are properties of the original labeled edge law (2.2).

Write $a_0=1/4$, $a_1=1/3$, and $t_s=1-a_s$. Given phase $s$ and previous bit zero, the next emitted bit is one with probability $a_s$; after a one the next bit is zero with probability one. Every transition satisfies $S_{i+1}=1-S_i$ and gives the endpoint previous bit $X_i$. The phase-conditioned stationary distributions of $H_i$ are $(8,3)/11$ on $\{A,B\}$ and $(9,2)/11$ on $\{C,D\}$. The two-step transition matrices on these classes are, respectively,

$$
\begin{pmatrix}3/4&1/4\\2/3&1/3\end{pmatrix},\qquad
\begin{pmatrix}5/6&1/6\\3/4&1/4\end{pmatrix}.
$$

Both have strictly positive entries. The classical finite-chain occupation theorem, applied to these two-step chains, yields the emitted-one frequencies

$$
r_0=\mathbb P(X_i=1\mid S_i=0)=\frac8{11}\frac14=\frac2{11},
\qquad
r_1=\mathbb P(X_i=1\mid S_i=1)=\frac9{11}\frac13=\frac3{11}.
\tag{13.3}
$$

For example, conditional on $S_0=s$, the empirical averages of $X_{2n}$ and $X_{2n-1}$, $1\le n\le k$, converge as $k\to\infty$ to $r_s$ and $r_{1-s}$. One can obtain this directly from the second coordinate of $H_{2n+1}$ and $H_{2n}$, respectively. For the left half-line the averages of $X_{-2n}$ and $X_{-(2n-1)}$ have the same two limits, by the occupation theorem for the stationary reversed two-step chains. Since $r_0\ne r_1$, either half-line determines $S_0$. This is an infinite-frequency assertion: every finite legal word has positive probability under each possible phase at its start, by starting with previous bit zero, so no such finite word identifies the phase.

Conditional on the phase, the visible process has the alternating one-step transition rule just stated. On $F_0=\{X_{-1}=X_1=0\}$, the two possible center paths have respective weights

$$
X_0=0:\ t_st_{1-s}=\frac12,
\qquad
X_0=1:\ a_s\cdot1.
$$

All remaining factors cancel in finite exterior windows conditional on $S_0=s$. Passing to the full exterior by bounded conditional-expectation convergence gives $q_0=a_s/(1/2+a_s)$. The exterior already determines the phase by (13.3), so no phase averaging remains in this ratio. Off $F_0$, legality forces $q_0=0$. This proves (13.2); stationarity gives the same assertion at every translated site. Both nonzero values lie in $[1/4,1/2]$. $\square$

**Proposition 13.2 (every deterministic forward quotient has a global diameter obstruction).** For the fixed representation (13.1), the only forward-labeled strongly lumpable partition is the identity partition. For every nonempty legal word $w$,

$$
\delta(M_w)=\delta(\check M_w)=1,
\tag{13.4}
$$

where the word in the reverse product is read in reverse-motion order, as in Definition 3.4. Thus this band-preserving component makes every deterministic quotient in Question 11.3 fail (3.7).

**Proof.** Equal blocks of a labeled strongly lumpable partition must have equal total outgoing mass for each label. For label one these masses, in state order, are $1/4,0,1/3,0$. Hence $A,C$ are singleton blocks and only $B,D$ could be merged. But $B$ sends its label-zero mass one to $C$, whereas $D$ sends its label-zero mass one to $A$. These singleton targets differ, excluding that merge.

For any legal word of length $m\ge1$, both starting states $A,C$ have positive word likelihood. Forward evolution is deterministic once a starting state and the emitted word are specified; its endpoint is $(S_0+m\bmod2,x_m)$. The two normalized rows therefore are point masses of opposite phase, with TV distance one.

The canonical reverse matrices (3.1) are

$$
\check M_0=\begin{pmatrix}
0&0&3/4&1/4\\
0&0&0&0\\
2/3&1/3&0&0\\
0&0&0&0
\end{pmatrix},\qquad
\check M_1=\begin{pmatrix}
0&0&0&0\\
0&0&1&0\\
0&0&0&0\\
1&0&0&0
\end{pmatrix}.
\tag{13.5}
$$

For a reverse word $w=x_1\cdots x_m$, take the two starting states $(s,x_1)$, $s=0,1$. Each is feasible: a forward path starting at $(s-m\bmod2,0)$ can emit the reversed legal word $x_m\cdots x_1$ with positive probability and end at $(s,x_1)$. Stationary reversal makes the reverse path positive. After $m$ reverse steps the two endpoint distributions are supported on opposite phase classes. Their TV distance is one, whether or not their previous-bit coordinates are deterministic. This proves (13.4). All these words have positive stationary probability since $\lambda$ is strictly positive. $\square$

**Proposition 13.3 (failure of the post-word weighted condition at the right initial cut).** For every $m\ge1$, take the right cut $j=0$ of Theorem 12.3 with the identity quotient:

$$
V=V_0^R=X_{-\infty:-1},\qquad Z=H_1,\qquad W=X_{1:m},\qquad U=X_0.
$$

For almost every $v$ on $\{X_{-1}=0,S_0=s\}$, the post-word residual of (12.1) is

$$
\Delta(v)=\sum_{w:p_v(w)>0}p_v(w)\Delta_w(v)
=\begin{cases}1/6,&s=0,\\1/5,&s=1.\end{cases}
\tag{13.6}
$$

Any good set whose positive-probability words have global diameter at most $\rho<1$ has no positive-probability word here. Consequently its bad-word variance divided by the exact denominator $\Delta(v)$ is one. Thus (12.7) fails for every $\eta<1$ on these positive-measure sets, and the global-diameter condition (12.2) fails for every $\kappa<1$.

**Proof.** The whole past identifies $s$ and the previous bit. On the stated event, $U$ is Bernoulli with parameter $a_s$ and $Z=(1-s,U)$ determines $U$. In particular,

$$
\mathcal D(U;Z\mid V=v)=a_s(1-a_s).
$$

For the word $0^m$, put $T_{s,m}=\prod_{i=2}^{m}t_{s+i\bmod2}$, with the empty product equal to one. Its two center masses are

$$
\mathbb P(U=1,W=0^m\mid V=v)=a_sT_{s,m},\qquad
\mathbb P(U=0,W=0^m\mid V=v)=\frac12T_{s,m}.
\tag{13.7}
$$

Both are positive. Hence $\Delta_{0^m}(v)=q_s(1-q_s)>0$, where $q_s=a_s/(1/2+a_s)$. More generally, $X_1=1$ forces $U=0$, while, conditional on $X_1=0$ and the known phase, observations $X_2,\ldots,X_m$ give no further information about $U$. Since $Z$ determines $U$, summing the posterior variances therefore gives

$$
\Delta(v)=\mathbb P(X_1=0\mid V=v)q_s(1-q_s)
=(a_s+1/2)\frac{a_s(1/2)}{(a_s+1/2)^2}
=\frac{a_s/2}{a_s+1/2}.
$$

This is (13.6), with no dependence on $m\ge1$. Proposition 13.2 says that every positive-probability word has global forward diameter one. Thus the entire positive residual is carried by bad words, and both weighted left-hand sides equal $\Delta(v)$. The phase/previous-zero events have probabilities $8/22$ and $9/22$, respectively, so failure is not confined to null conditioning data.

The denominator is essential. Dividing the same residual by the variance *before* observing $W$ instead gives

$$
\frac{\Delta(v)}{\mathcal D(U;Z\mid V=v)}
=\begin{cases}8/9,&s=0,\\9/10,&s=1.\end{cases}
\tag{13.8}
$$

Accordingly, this obstruction to the exact post-word condition (12.7) does not disprove variants normalized by the pre-observation variance. No failure at the left initial cut or after a finite burn-in follows from this calculation. $\square$

**Application 13.4 (the conditional-support form of the existing variance argument).** Fix a component and a forward quotient as in Proposition 11.1, and work with its joint quotient producer (11.2). Keep the original fields, endpoints, and word order of Theorem 12.3. In each direction separately, fix a positive integer block length $m_d$ and retain the full joint-channel premise

$$
\mathbb P(W_j^d=w,Z_{j+m_d}^d=t\mid U,Z_j^d=z,V_j^d)
=B_w^d(z,t),\qquad
B_w^R=\bar M_w,\quad B_w^L=R_w.
\tag{13.9}
$$

Here $R_w$ uses the canonical quotient reverse, not an assumed lumping of the original hidden reverse. Proposition 11.1 and Lemma 3.3 on the quotient producer supply (13.9) at every cut. For $p_{j,v}^d(w)>0$, restrict the normalized rows to

$$
\begin{aligned}
I_{j,v,w}^d
&=\{z:\mathbb P(Z_j^d=z\mid V_j^d=v,W_j^d=w)>0\},\\
c_{j,v}^d(w)
&=\max_{z,z'\in I_{j,v,w}^d}
\operatorname{TV}\left(
\frac{B_w^d(z,\cdot)}{(B_w^d\mathbf1)_z},
\frac{B_w^d(z',\cdot)}{(B_w^d\mathbf1)_{z'}}\right).
\end{aligned}
\tag{13.10}
$$

This is the posterior support marginal over $U$, not a separate support chosen after conditioning on $U=0$ or $U=1$. It is nonempty and all its row denominators are positive by (5.3). A singleton gives coefficient zero; null words are omitted, with no coefficient assigned to them.

Suppose that, separately for $d=L,R$, there is $0\le\kappa_d<1$ such that at **every required shifted cut** $j$,

$$
\sum_{w:p_{j,v}^d(w)>0}
p_{j,v}^d(w)c_{j,v}^d(w)\Delta_{j,w}^d(v)
\le\kappa_d\Delta_j^d(v)
\quad\text{for almost every }v,
\qquad
\Delta_j^d(v)=\sum_w p_{j,v}^d(w)\Delta_{j,w}^d(v).
\tag{13.11}
$$

The last sum also omits null words. This denominator is again the post-word residual (12.1). If the required cuts are all $j\ge0$, then (12.8)--(12.10) hold with these constants. More generally, if (13.11) holds at every $j\ge b_d$ for fixed integers $b_d\ge0$, then

$$
e_d^{P_C}(j)\le\frac14\kappa_d^{\lfloor(j-b_d)/m_d\rfloor}
\quad(j\ge b_d),
\qquad e_d^{P_C}(j)\le\frac14\quad(0\le j<b_d),
\tag{13.12}
$$

and in particular

$$
A_{P_C}(0)\le\frac{b_L+b_R}{2}
+\frac12\sum_{d=L,R}\frac{m_d}{1-\sqrt{\kappa_d}}<\infty.
\tag{13.13}
$$

These constants may depend on the component. If each positive stationary component supplies them, Theorem 7.1 gives the original-law finite-mixture conclusion.

To obtain these statements, use (13.9), which is exactly (5.1), for both roles it plays in Lemma 5.1. First, it gives the conditional Markov kernel (5.4) on each $(v,w)$-fiber. Restricting that kernel to $I_{j,v,w}^d$ is the classical support restriction already allowed in Lemma 4.3. Its application gives

$$
\mathcal D(U;Z_{j+m_d}^d\mid V_j^d=v,W_j^d=w)
\le c_{j,v}^d(w)\Delta_{j,w}^d(v).
$$

Second, the same joint-channel premise makes $W_j^d$ conditionally independent of $U$ given $(Z_j^d,V_j^d)$ and hence gives the observation-variance identity (5.5). Sum the preceding inequality over words, use (13.11), and integrate, just as in Lemma 12.1. The resulting recursion is bounded by $\kappa_d\mathcal D(U;Z_j^d\mid V_j^d)$, because $\kappa_d\ge0$. Start at $b_d$ with variance at most $1/4$, iterate complete blocks, and handle any positive-length remainder by Lemma 5.1 with coefficient one; a zero-length remainder requires no block. The Jensen step (6.7)--(6.8) and the same geometric sums prove (13.12)--(13.13). This is an application of Lemmas 4.3, 5.1, and 12.1, not a new standalone SDPI. Conditional Markovness alone without the full premise (13.9) would not justify the observation-variance identity.

**Proposition 13.5 (one-step conditional support and finite erasure for the witness).** For (13.1), the identity quotient has

$$
c_{j,v}^L(w)=c_{j,v}^R(w)=0
\quad\text{for every }j\ge0\text{ and every positive-probability one-letter word, a.s.}
\tag{13.14}
$$

Furthermore,

$$
e_L^P(j)=e_R^P(j)=0\quad(j\ge1),\qquad A_P(1)=0.
\tag{13.15}
$$

**Proof.** In the right direction, $V_j^R$ determines the phase from its infinite left half-line. At $j=0$, the posterior support of $Z=H_1$ has a fixed phase and at most the two possible previous-bit coordinates $U$. After observing $W=X_1=1$, legality forces $U=0$, leaving a singleton. After observing $W=0$, all feasible forward $M_0$ rows of that fixed phase normalize to the same endpoint $(S_2,0)$. Their diameter is zero. At $j\ge1$, $X_j$ and the phase are already known from $V_j^R$, so $H_{j+1}$ itself is known; any further posterior support is a singleton.

In the left direction, $V_j^L$ determines the phase from its infinite right half-line. The one-letter reverse observation is $W=X_{-j-1}$, exactly the previous-bit coordinate of $Z_j^L=H_{-j}$. Thus conditioning on $(V_j^L,W)$ fixes both coordinates of $Z_j^L$. Its support is a singleton at every $j\ge0$, irrespective of the endpoint distribution of its reverse row. This proves (13.14) in the required marginal-over-$U$ supports, so (13.11) holds with $m_L=m_R=1$ and $\kappa_L=\kappa_R=0$.

Directly at the output level, for $j\ge1$ either retained field contains both neighbors of the center, and its infinite half-line determines the phase. Hence (13.2) is measurable in both $\mathcal L_j$ and $\mathcal R_j$. The tower identity gives $p_j^L=p_j^R=q_0$, proving (13.15). This also proves $A_P(0)<\infty$, since only the two bounded errors at $j=0$ can contribute.

Alternatively a finite burn-in bypasses the initial obstruction even for the global-diameter variance condition: for $j\ge1$, both cut variances $\mathcal D(U;Z_j^d\mid V_j^d)$ vanish. In the right direction the cut state is already observed as above; in the left direction the phase-conditioned one-step Markov rule separates the center from the earlier cut state once the observed neighbors and phase are given. By (5.5), all post-word residuals at those cuts also vanish. Thus the weighted condition is vacuous after $b_L=b_R=1$. There is no persistent bad-variance obstruction after this burn-in. $\square$

**Open Question 13.6 (universal availability of support-aware eventual-cut conditions).** For every $N\ge1$ and every $\theta\in\Theta_N$ whose visible law satisfies $\mathsf B(P_\theta)$, does each positive stationary component admit a deterministic forward-labeled quotient and constants $m_L,m_R\ge1$, $b_L,b_R\ge0$, and $0\le\kappa_L,\kappa_R<1$ such that the canonical quotient channels satisfy (13.11) for almost every conditioning value at every cut $j\ge b_d$, separately in each direction? Application 13.4 proves sufficiency if these conditions are supplied; their universal availability under the band remains open. Proposition 13.2 answers the deterministic global-diameter obstruction part of Question 11.3 affirmatively, and Proposition 13.3 excludes the all-cut global-diameter version of (12.7) for this witness. Neither result refutes $\mathsf Q_{\rm full}$ or $\mathsf Q_{\rm band}$, and neither classifies alternate realizations of the same visible law.

**Attribution 13.7 (construction and classical intermediates).** The four-state construction and its consequences above are derived from the original domain and edge law of this volume; no novelty claim is made. The finite-chain occupation theorem and conditional projection are the classical tools identified in Section 10. The support restriction in Application 13.4 is the one already used in Lemma 4.3 and Correspondence 10.2; the SDPI remains the chi-square specialization of Raginsky's Theorem 3.1 cited there. Proposition 7.1 of [the universal-posterior-defect volume](FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md) uses an ordinary one-step visible Markov chain for a different band-preserving nonattainment comparison. It supplies no premise for the phase obstruction (13.1)--(13.8). The results here concern this fixed representation, its deterministic partitions, and its actual visible erasure fields, with the original clock and quantifiers unchanged.

## 追加锚（本行以下为增补区）

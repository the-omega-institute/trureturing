# Native coefficient geometry of heterogeneous whole-window teachers

## 1. The common product law and native teachers

**Definition 1.1 (Whole windows and the common law).** Let $n\ge4$, $0<\rho\le1/8$, and $I=\{0,\ldots,n-1\}$. The five-window alphabet, with bits written from low to high, is

$$
\Sigma=(000,100,010,101,001).
$$

An element $\mu\in\operatorname{Laws}(n)$ assigns a real mass $\mu_i(s)$ to each $i\in I$ and $s\in\Sigma$. Assume $\operatorname{Admissible}(\rho,\mu)$, meaning

$$
\mu_i(s)\ge\rho\quad(i\in I,s\in\Sigma),\qquad
\sum_{s\in\Sigma}\mu_i(s)=1\quad(i\in I).
$$

On the complete carrier $\Omega=\Sigma^I=\operatorname{Input}(n)$, define

$$
M_\mu(w)=\prod_{i\in I}\mu_i(w_i),\qquad
\mathbb E_\mu F=\sum_{w\in\Omega}M_\mu(w)F(w)
=\operatorname{productExpectation}(\mu,F).
$$

This is one probability law for every function and coefficient vector below. It includes every complete word, including zero windows and words with occupied adjacent seams. The coordinates $W_i(w)=w_i$ are mutually independent whole windows with their specified, possibly unequal, laws.

**Definition 1.2 (Actual endpoints and increasing roles).** Put

$$
h_i(w)=\operatorname{highIndicator}(w_i),\quad
\ell_i(w)=\operatorname{lowIndicator}(w_i),\quad
t_i(w)=h_i(w)\ell_i(w),
$$

and write

$$
H_i=\mathbb E_\mu h_i=\mu_i(101)+\mu_i(001),\quad
L_i=\mathbb E_\mu\ell_i=\mu_i(101)+\mu_i(100),\quad
T_i=\mathbb E_\mu t_i=\mu_i(101).
$$

Thus the actual same-window joint mass is $T_i$. Define $\widehat h_i=h_i-H_i$, $\widehat\ell_i=\ell_i-L_i$, and $\widehat t_i=t_i-T_i$. The role set is the original

$$
\Theta_n=\operatorname{Roles}(n)=\{(p,q,r)\in I^3:p<q<r\}.
$$

For $\tau=(p,q,r)$ let $C_\tau(w)=\operatorname{classValue}(\tau,w)$: its value is 1 if $h_p\ell_q=1$, otherwise 2 if $h_q\ell_r=1$, otherwise 0. In particular,

$$
C_{pqr}=h_p\ell_q+2(1-h_p\ell_q)h_q\ell_r
=h_p\ell_q+2h_q\ell_r-2h_pt_q\ell_r.                 \tag{1}
$$

The alphabet, means, and (1) are the native identities supplied by [HeterogeneousTeacherSeparation][HTS], respectively `high_indicator_mean`, `low_indicator_mean`, `joint_endpoint_mean`, and `class_value_formula`; the carrier and role order are those of [LegalPriorityTeacher][LPT]. They are also the objects of [FIB ATOM Machine Learning Whitebox][WB], §58.1.

**Definition 1.3 (Diagonal weights and residuals).** All expectations in this definition use the fixed $M_\mu$. Set

$$
\begin{aligned}
Z_{pqr}&=\widehat h_p\widehat t_q\widehat\ell_r,\\
R_{pqr}&=C_{pqr}+2Z_{pqr},\\
d_{pqr}&=4H_p(1-H_p)T_q(1-T_q)L_r(1-L_r),\\
\beta(\rho)&=16\rho^3(1-2\rho)^2(1-\rho).
\end{aligned}                                                   \tag{2}
$$

For an arbitrary real vector $a=(a_\tau)_{\tau\in\Theta_n}$, define

$$
F_a=\sum_{\tau\in\Theta_n}a_\tau C_\tau,\qquad
R_a=\sum_{\tau\in\Theta_n}a_\tau R_\tau,\qquad
G_{\tau\nu}=\mathbb E_\mu(C_\tau C_\nu).
$$

## 2. The coefficient identity and uniform floor

**Theorem 2.1 (Native diagonal plus residual).** Under Definition 1.1, every $a\in\mathbb R^{\Theta_n}$ satisfies

$$
\begin{aligned}
a^{\mathsf T}Ga=\mathbb E_\mu F_a^2
&=\sum_{(p,q,r)\in\Theta_n}d_{pqr}a_{pqr}^2+\mathbb E_\mu R_a^2\\
&\ge\sum_{(p,q,r)\in\Theta_n}d_{pqr}a_{pqr}^2
\ge\beta(\rho)\sum_{\tau\in\Theta_n}a_\tau^2.
\end{aligned}                                                   \tag{3}
$$

Proof. Finite product summation gives $\sum_{w\in\Omega}M_\mu(w)=\prod_{i\in I}\sum_{s\in\Sigma}\mu_i(s)=1$, and every word mass is positive. The product ANOVA orthogonality used here is the existing result in [Recursive Relational Observation Context Geometry][CG], Theorem 14.5. Its precise correspondence is $E=I$, $X_i=W_i$, and the old record is constant. Hypothesis 14.4 is exactly the whole-window product law $M_\mu$; all functions are square integrable on the finite carrier. The full coordinate record determines $w$, so its hidden projection $Q$ is zero. The underlying product decomposition and orthogonality are also given by Art B. Owen, *Monte Carlo theory, methods and examples*, Appendix A, §§A.2–A.4, especially Lemmas A.3–A.4 and (A.11)–(A.12), [primary text](https://artowen.su.domains/mc/A-anova.pdf). Section A.2 explicitly allows independent factors with other marginal distributions; the factors here are whole windows.

For the native application, expand (1) in the centered variables. With
$K_{pqr}=H_pL_q+2H_qL_r-2H_pT_qL_r$, this gives exactly

$$
\begin{aligned}
R_{pqr}={}&K_{pqr}
+(L_q-2T_qL_r)\widehat h_p
+H_p\widehat\ell_q+2L_r\widehat h_q-2H_pL_r\widehat t_q\\
&+(2H_q-2H_pT_q)\widehat\ell_r
+\widehat h_p\widehat\ell_q+2\widehat h_q\widehat\ell_r\\
&-2L_r\widehat h_p\widehat t_q
-2T_q\widehat h_p\widehat\ell_r
-2H_p\widehat t_q\widehat\ell_r.
\end{aligned}                                                   \tag{4}
$$

Every summand of (4) depends on at most two window positions. Each $Z_{pqr}$ is centered in each of its three distinct positions. Consequently $\mathbb E_\mu(Z_{pqr}R_{uvw})=0$ for all roles: a summand of (4) omits some position in $\{p,q,r\}$, and integrating that position gives its centered mean zero.

Also $\mathbb E_\mu(Z_{pqr}Z_{uvw})=0$ for distinct roles. Indeed, increasing order makes the role uniquely determined by its three-element support; distinct supports have a position in one and absent from the other. Integrating that position again gives zero. This is the source-specific orthogonality calculation within the cited product ANOVA, without an assumption about independence of endpoints within a window.

The indicators $h_i,t_i,\ell_i$ are each binary. Independence at the three distinct positions therefore gives

$$
4\mathbb E_\mu Z_{pqr}^2
=4\mathbb E_\mu\widehat h_p^2\,
\mathbb E_\mu\widehat t_q^2\,
\mathbb E_\mu\widehat\ell_r^2
=d_{pqr}.                                                       \tag{5}
$$

These integrations are finite product factorization with $\sum_s\mu_i(s)=1$, as in the source's `product_expectation_two_positions`, `product_expectation_three_positions`, and `product_expectation_factorization`. Unselected positions integrate to one. Substituting $F_a=R_a-2\sum_\tau a_\tau Z_\tau$ and expanding its squared norm gives the equality in (3); finite linearity also gives $\mathbb E_\mu F_a^2=a^{\mathsf T}Ga$. Nonnegative word masses give the first inequality.

For the second inequality, `endpoint_marginal_bounds` gives

$$
2\rho\le H_i,L_i\le1-3\rho,
\qquad \rho\le T_i\le1-4\rho.                                  \tag{6}
$$

The latter interval follows by subtracting the other four masses from one. For $v(x)=x(1-x)$ and $b\le x\le c$, $b<c$, direct expansion gives

$$
v(x)=\frac{c-x}{c-b}v(b)+\frac{x-b}{c-b}v(c)+(x-b)(c-x)
\ge\min\{v(b),v(c)\}.
$$

The endpoint comparisons for the two intervals in (6) are

$$
\begin{aligned}
v(1-3\rho)-v(2\rho)&=\rho(1-5\rho)\ge0,\\
v(1-4\rho)-v(\rho)&=3\rho(1-5\rho)\ge0.
\end{aligned}
$$

Here $1-5\rho>0$ and both intervals have positive length because $0<\rho\le1/8$. Hence

$$
H_i(1-H_i),L_i(1-L_i)\ge2\rho(1-2\rho),\qquad
T_i(1-T_i)\ge\rho(1-\rho).
$$

Multiplication in (2) yields $d_{pqr}\ge\beta(\rho)>0$, proving (3). $\square$

## 3. Attainment on six native positions

**Proposition 3.1 (Attainment for every $n\ge6$).** For every $0<\rho\le1/8$ and $n\ge6$, use the single homogeneous law

$$
\mu_i=\operatorname{extremal}(\rho)
=\left(\frac{1-3\rho}{2},\rho,\frac{1-3\rho}{2},\rho,\rho\right)
\quad(i\in I)
$$

in the alphabet order of Definition 1.1. There is a nonzero native coefficient vector $a$ for which both inequalities in (3) are equalities. In particular $\beta(\rho)$ is the largest constant valid uniformly over all admissible laws and all coefficient vectors for each fixed $n\ge6$.

Proof. The displayed masses sum to one, and $(1-3\rho)/2\ge\rho$ because $\rho\le1/8<1/5$. Thus this is admissible, with $H_i=L_i=2\rho$ and $T_i=\rho$ at every position, so every $d_{pqr}=\beta(\rho)$.

Take $A=\{0,1\}$, $B=\{2,3\}$, $D=\{4,5\}$, and signs
$s_0=s_2=s_4=1$, $s_1=s_3=s_5=-1$. Define

$$
a_{pqr}=\begin{cases}
s_ps_qs_r,&p\in A,\ q\in B,\ r\in D,\\
0,&\text{otherwise}.
\end{cases}                                                     \tag{7}
$$

All eight supported triples satisfy $p<q<r$ and are distinct original roles; $\sum_\tau a_\tau^2=8$. In the signed sum of (1), the first term vanishes after summing over $r$, and the second after summing over $p$. The third factors, giving the pointwise identity

$$
F_a=-2(h_0-h_1)(t_2-t_3)(\ell_4-\ell_5).                       \tag{8}
$$

The common means imply $h_0-h_1=\widehat h_0-\widehat h_1$, and likewise for the $t$ and $\ell$ differences. Expanding their product shows $F_a=-2\sum_\tau a_\tau Z_\tau$, so $R_a=0$ pointwise. This proves equality in the weighted identity and floor.

For completeness, the three differences in (8) depend on disjoint position pairs. Their squared means are respectively $4\rho(1-2\rho)$, $2\rho(1-\rho)$, and $4\rho(1-2\rho)$. This follows by expanding $(X-Y)^2$ for independent identically distributed binary variables of mean $m$, whose squared difference mean is $2m(1-m)$. Thus

$$
\mathbb E_\mu F_a^2
=4\,[4\rho(1-2\rho)]\,[2\rho(1-\rho)]\,[4\rho(1-2\rho)]
=8\beta(\rho)=\beta(\rho)\sum_\tau a_\tau^2.
$$

Positions beyond 5 integrate to one in the same homogeneous law. Dividing (7) by $\sqrt8$ gives a unit coefficient vector attaining $\beta(\rho)$ for every $n\ge6$. Any larger uniform constant would fail on this vector, while Theorem 2.1 supplies the stated constant. $\square$

[HTS]: https://github.com/the-omega-institute/trureturing/blob/1c1f224301df9fb13b8547f96cd2318edb8aaade/D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation.lean
[LPT]: https://github.com/the-omega-institute/trureturing/blob/1c1f224301df9fb13b8547f96cd2318edb8aaade/D5/S3/Arith/FibonacciAtomic/LegalPriorityTeacher.lean
[WB]: https://github.com/the-omega-institute/trureturing/blob/1c1f224301df9fb13b8547f96cd2318edb8aaade/docs/develop/theory/FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md
[CG]: https://github.com/the-omega-institute/trureturing/blob/1c1f224301df9fb13b8547f96cd2318edb8aaade/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md

## 追加锚（本行以下为增补区）

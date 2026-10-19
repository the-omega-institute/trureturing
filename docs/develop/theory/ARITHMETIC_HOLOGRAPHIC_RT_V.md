# Arithmetic holographic RT V

## 120. Effective-rank bounds for full actual quotient stresses

### 120.1. Original channels and the full quotient

Retain the original local CPTP maps $`A,B:\mathcal L(\mathbb C^8)\to\mathcal L(\mathbb C^4)`$, with logical basis $`|f,j\rangle`$ for $`1\le f\le4`$ and $`j\in\{0,1\}`$. Write $`i=(f,j)`$ and $`f(i)=f`$. The target and fixed correlated encodings are

$$
\begin{aligned}
\mathcal F(|f,j\rangle\langle f,k|)&=\delta_{jk}|f\rangle\langle f|,\\
\mathcal F(|f,j\rangle\langle g,k|)&=\tfrac12|f\rangle\langle g|
   &&(f\ne g),\\
V_{\mathrm{in}}|i\rangle&=|i\rangle\otimes|i\rangle,\qquad
V_{\mathrm{out}}|f\rangle=|f,f\rangle.
\end{aligned}
\tag{120.1}
$$

Let $`J_{\mathrm{in}},J_{\mathrm{out}}`$ be their isometric channels and use the unhalved arbitrary-reference error

$$
\delta=\|(A\otimes B)\circ J_{\mathrm{in}}
                   -J_{\mathrm{out}}\circ\mathcal F\|_\diamond.
\tag{120.2}
$$

Its physical output is the full sixteen-dimensional $`\mathbb C^4\otimes\mathbb C^4`$. Choose Stinespring isometries $`V_A,V_B`$ and form the actual correct-output records

$$
g_i=(\langle f(i)|\otimes I)V_A|i\rangle,\qquad
h_i=(\langle f(i)|\otimes I)V_B|i\rangle.
\tag{120.3}
$$

Their forward Grams $`G,H`$ use inner products conjugate-linear in the first argument. Each original fibre block satisfies $`G_{ff},H_{ff}\preceq I_2`$. Put

$$
K=G\odot H,\qquad L=T-K,\qquad
T_{ff}=I_2,\quad T_{fg}=\tfrac12J_2\ (f\ne g).
\tag{120.4}
$$

The encoded product coefficients use $`K^{\mathsf T}`$. The original domain, convention, and leakage-safe witness are those of [RT III §91](ARITHMETIC_HOLOGRAPHIC_RT_III.md#91-adaptive-original-channel-witnesses-and-an-obstruction-to-all-two-fibre-tests) and [RT IV §119](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#119-coherent-input-bounds-for-diffuse-and-isotropic-quotient-stresses).

Assume the full eight-coordinate identities

$$
\begin{aligned}
R&\succeq0,\qquad R_{ii}=1,\qquad a_i\ne0,\qquad\alpha>0,\\
G&=H\odot\bar R,\qquad
P=\alpha\operatorname{diag}(a)R\operatorname{diag}(\bar a)\succeq0,
\qquad PH=0,
\end{aligned}
\tag{120.5}
$$

on these actual Grams. Define

$$
\lambda=\|P\|_{\mathrm{op}}>0,\qquad r=\frac{\operatorname{Tr}P}{\lambda}.
\tag{120.6}
$$

**Theorem 120.1 (effective-rank obstruction with actual leakage).** Under (120.1)–(120.6), if $`r\ge4`$, then

$$
\delta\ge
\min\left\{\frac{34}{81},\frac{176+10\sqrt7}{144}-\frac4r\right\}
\ge\frac{16+5\sqrt7}{72}>\frac25.
\tag{120.7}
$$

No projection identity for $`P`$ or equality $`\operatorname{ran}P=\ker H`$ is assumed.

### 120.2. Proof in the original output and reference spaces

**Proof.** The physical reciprocal gauge in RT IV Lemma 119.1 makes $`a`$ positive. Explicitly, for $`E_{ii}=\bar a_i/|a_i|`$, multiply the whole $`i`$-th Stinespring column of $`A`$ by $`\bar E_{ii}`$ and that of $`B`$ by $`E_{ii}`$. The isometries persist and the phases cancel in the correlated encoding, including all wrong-output components. Thus the entire encoded product channel and $`\delta`$ are unchanged. The transformed data are

$$
G'=EGE^*,\quad H'=E^*HE,\quad a'=Ea,\quad
R'=E^{*2}RE^2,\quad P'=E^*PE.
\tag{120.8}
$$

They satisfy (120.5), with the same $`\lambda,r`$. Suppress primes and set

$$
\begin{aligned}
b_i&=\sqrt{P_{ii}}>0,\qquad t=\sum_i b_i^2=r\lambda,\\
\beta_f&=\|b_f\|_2,\qquad S=\sum_f\beta_f,\qquad c=S^2,\\
A_0&=\sum_i b_i,\qquad s_f=\sum_{i\in f}b_i.
\end{aligned}
\tag{120.9}
$$

Since $`R_{ij}=P_{ij}/(b_i b_j)`$,

$$
b^*Kb=\operatorname{Tr}((H\odot H)P),\qquad
b^*Tb=t+\frac{A_0^2-\sum_f s_f^2}{2}.
\tag{120.10}
$$

The first trace is $`\sum_{i,j}H_{ij}^2P_{ji}`$, with complex squares.

Use four orthonormal reference tags and the unit input

$$
|\psi\rangle=\sum_f\sum_{i\in f}
        \frac{b_i}{\sqrt{S\beta_f}}|i\rangle\otimes|f\rangle_R.
\tag{120.11}
$$

Its squared norm is $`\sum_f\beta_f/S=1`$. In the full sixteen-output by four-reference space, project the target-minus-product output onto the span of $`|f,f\rangle\otimes|f\rangle_R`$. The target lies entirely in this subspace and has trace one. The compressed difference $`C`$ and unit vector $`v`$ satisfy

$$
C_{fg}=\frac{\sum_{i\in f,j\in g}b_i b_jL_{ji}}
                   {S\sqrt{\beta_f\beta_g}},\qquad
v_f=\sqrt{\frac{\beta_f}{S}},\qquad
v^*Cv=\frac{b^*L^{\mathsf T}b}{c}=\frac{b^*Lb}{c}.
\tag{120.12}
$$

The final equality uses real $`b`$ and Hermitian $`L`$. The complementary block of the difference is minus a positive product-output block whose trace equals $`\operatorname{Tr}C`$. Pinching therefore gives $`\delta\ge\|C\|_1+\operatorname{Tr}C=2\operatorname{Tr}C_+\ge2v^*Cv`$, retaining all original leakage. Consequently

$$
\delta\ge\frac2c\left[t+\frac{A_0^2-\sum_f s_f^2}{2}
                           -\operatorname{Tr}((H\odot H)P)\right].
\tag{120.13}
$$

If $`\delta>34/81`$, the first inequality in (120.7) is immediate. Assume henceforth $`\delta\le34/81`$. For the original basis input $`|i\rangle`$, the correct target output has product probability $`G_{ii}H_{ii}=H_{ii}^2`$. Measuring this output against its complement yields

$$
\delta\ge2(1-H_{ii}^2),\qquad
H_{ii}\ge\sqrt{1-\delta/2}\ge\frac89.
\tag{120.14}
$$

Factor $`H=B_0^*B_0`$. Each original two-column block $`B_{0,f}`$ is a contraction, so $`B_0B_0^*=\sum_f B_{0,f}B_{0,f}^*\preceq4I`$. For the projection $`N`$ onto $`\ker H`$, spectral decomposition and complementarity imply

$$
H\preceq4(I-N),\qquad P\preceq\lambda N,\qquad
0<x_i:=\frac{P_{ii}}{\lambda}\le N_{ii}
       \le1-\frac{H_{ii}}4\le\frac79,\qquad\sum_i x_i=r.
\tag{120.15}
$$

The bound $`P\preceq\lambda N`$ uses only $`P\succeq0`$ and $`PH=0`$.

Now $`y_i=4x_i/r`$ satisfy $`0\le y_i\le7/9`$ and $`\sum_i y_i=4`$, because $`r\ge4`$. A minimum of $`\sum_i\sqrt{y_i}`$ on this compact capped simplex exists. If two coordinates are interior, moving them at fixed sum to an endpoint of their feasible segment does not increase this concave objective for at least one endpoint. Repetition leaves at most one fractional coordinate. The sum-four condition then gives five copies of $`7/9`$, one of $`1/9`$, and two zeros. Thus

$$
\sum_i\sqrt{y_i}\ge\frac{5\sqrt7+1}{3},\qquad
\frac{A_0^2}{\lambda}=\frac r4\left(\sum_i\sqrt{y_i}\right)^2
                    \ge\frac{r(176+10\sqrt7)}{36}.
\tag{120.16}
$$

The two-coordinate fibres give $`\sum_f s_f^2\le2t`$, hence $`2b^*Tb\ge A_0^2`$. By Schur positivity and $`H_{ii}\le1`$,

$$
\operatorname{Tr}((H\odot H)P)
   \le\lambda\operatorname{Tr}(H\odot H)
   =\lambda\sum_iH_{ii}^2\le8\lambda,\qquad
c\le4\sum_f\beta_f^2=4r\lambda.
\tag{120.17}
$$

Equation (120.16) makes $`A_0^2-16\lambda>0`$ for $`r\ge4`$, so replacing the denominator by its upper bound is legitimate. Equation (120.13) yields

$$
\delta\ge\frac{A_0^2-16\lambda}{c}
 \ge\frac{176+10\sqrt7}{144}-\frac4r
 \ge\frac{16+5\sqrt7}{72}.
\tag{120.18}
$$

Together with the first case this proves the minimum bound in (120.7). The remaining comparisons are exact: $`(16+5\sqrt7)/72>2/5`$ is equivalent to $`25\sqrt7>64`$, whose squared form is $`4375>4096`$; and $`(16+5\sqrt7)/72<34/81`$ follows from $`\sqrt7<128/45`$, whose squared form is $`14175<16384`$. This proves the theorem. ∎

The rescaling in (120.16) removes the isotropic rank-four hypothesis of RT IV Theorem 119.3. It does not supply (120.5) for arbitrary leaking local minima. For the calibrated full-support rank-seven local-minimum consumer, RT IV Corollary 119.4 already gives the stricter necessary restriction $`r<1129/300`$. Nonisotropic rank-four stresses satisfying that restriction, the opposite-rank-three class, and the global representatives with both ranks at most six remain outside these exclusions. The unrestricted global quarter optimum remains open.

## 追加锚（本行以下为增补区）

## 121. Explicit concentration of the opposite quotient Gram

### 121.1. Calibrated actual quotient and quantitative bounds

Retain the original channels, encodings, forward-Gram convention, full sixteen-dimensional product output, and unhalved arbitrary-reference error $`\delta`$ of (120.1)–(120.4). Assume calibration and the full correlation quotient

$$
G,H\succeq0,\qquad G_{ff}=H_{ff}=I_2,\qquad
G=H\odot\bar R,\qquad R\succeq0,\quad R_{ii}=1.
\tag{121.1}
$$

These are identities of the actual Grams. The concentration below does not require a complementary stress or local minimality; the full-support local-minimum consumer supplies (121.1) through [RT III Lemma 95.2](ARITHMETIC_HOLOGRAPHIC_RT_III.md#952-one-rank-seven-side-gives-a-supported-psd-quotient).

**Theorem 121.1 (explicit quotient concentration).** Suppose (121.1) holds, $`\operatorname{rank}H=4`$, and $`0\le\delta<1/4`$. Write the positive eigenvalues as $`\lambda_1\ge\lambda_2\ge\lambda_3\ge\lambda_4>0`$ and put $`\tau=\lambda_3+\lambda_4`$. Then

$$
\begin{aligned}
\operatorname{Tr}H^2&\ge32-16\delta>28,\\
\lambda_1&\ge\frac{8+4\sqrt{1-3\delta/2}}3
              >\frac{8+\sqrt{10}}3,\\
\tau&\le2-\sqrt{4-8\delta}<2-\sqrt2,\\
\lambda_2&\ge2+\sqrt{4-8\delta}>2+\sqrt2.
\end{aligned}
\tag{121.2}
$$

For every two distinct original fibres,

$$
\|H_{fg}\|_F^2\ge2(1-\delta),\qquad
\sigma_{\min}(H_{fg})^2\ge1-2\delta>\tfrac12.
\tag{121.3}
$$

In particular all six cross blocks are invertible. No sharpness or physical realization of the scalar spectral extremizers is asserted.

### 121.2. The original coherent input and purity

**Proof.** For a union $`S`$ of $`m`$ complete fibres, use the tagged input and target vector of [RT IV Theorem 117.1](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1171-original-channels-and-a-tagged-pure-target):

$$
|\Psi_S\rangle=\frac1{\sqrt m}\sum_{f\in S}|f\rangle_R
 \otimes\frac{|f,0\rangle+|f,1\rangle}{\sqrt2},\qquad
|\Omega_S\rangle=\frac1{\sqrt m}\sum_{f\in S}|f\rangle_R\otimes|f,f\rangle.
\tag{121.4}
$$

Both vectors have norm one, and the target output is $`|\Omega_S\rangle\langle\Omega_S|`$. The full physical product output $`\sigma_S`$ has trace one. The reference tags select the actual correct-output entries, giving

$$
\langle\Omega_S|\sigma_S|\Omega_S\rangle
 =\frac{\boldsymbol1^*K_S\boldsymbol1}{2m^2},\qquad
\delta\ge2-\frac{\boldsymbol1^*K_S\boldsymbol1}{m^2}.
\tag{121.5}
$$

The second inequality tests the full output against the Hermitian contraction $`2|\Omega_S\rangle\langle\Omega_S|-I`$. The forward-Gram convention conjugates the compressed coefficients; their complete scalar sum is real by Hermiticity. Thus (121.5) retains the original unhalved normalization and all output/reference coordinates. No untagged input is substituted.

Since $`|R_{ij}|\le1`$ and $`K_{ij}=H_{ij}^2\overline{R_{ij}}`$,

$$
\boldsymbol1^*K_S\boldsymbol1
 =\operatorname{Re}\sum_{i,j\in S}H_{ij}^2\overline{R_{ij}}
 \le\sum_{i,j\in S}|H_{ij}|^2
 =\operatorname{Tr}(H_S^2).
\tag{121.6}
$$

The physical coefficient uses the complex square before this scalar upper bound. Taking all four fibres proves $`\operatorname{Tr}H^2\ge16(2-\delta)`$. For two fibres, calibration gives $`\operatorname{Tr}(H_S^2)=4+2\|H_{fg}\|_F^2`$, so (121.5)–(121.6) imply the first bound in (121.3). Each $`H_{fg}`$ is the overlap of two isometric record blocks and hence is a contraction. If its singular values are $`s_1\ge s_2`$, then

$$
s_2^2=\|H_{fg}\|_F^2-s_1^2
      \ge\|H_{fg}\|_F^2-1\ge1-2\delta,
\tag{121.7}
$$

proving the second bound.

### 121.3. The capped spectral estimates

The calibrated record-frame operator is a sum of four rank-two orthogonal projections. Its nonzero eigenvalues equal those of $`H`$, so

$$
0<\lambda_i\le4,\qquad \sum_{i=1}^4\lambda_i=8.
\tag{121.8}
$$

RT IV Theorem 117.1 already gives $`\lambda_1+\lambda_2\ge8-4\delta`$. Hence $`0<\tau\le4\delta<1`$. At fixed top-two sum $`8-\tau`$, convexity of $`x^2+(8-\tau-x)^2`$ and the cap $`\lambda_1\le4`$ give

$$
\lambda_1^2+\lambda_2^2\le16+(4-\tau)^2,
\qquad \lambda_3^2+\lambda_4^2\le\tau^2.
\tag{121.9}
$$

Consequently $`32-16\delta\le32-8\tau+2\tau^2`$, or $`(\tau-2)^2\ge4-8\delta`$. Because $`\tau<1<2`$, the root is $`\tau\le2-\sqrt{4-8\delta}`$. Also $`\lambda_2=8-\tau-\lambda_1\ge4-\tau`$, proving both remaining bounds in (121.2).

For the sharper largest-eigenvalue estimate, put $`t=\lambda_1`$. The purity bound and $`\operatorname{Tr}H^2\le8t`$ give $`t\ge4-2\delta>7/2>8/3`$. On the capped simplex $`0\le x_i\le t`$, $`\sum_{i=1}^4x_i=8`$, the convex square sum is maximized at an extreme point. For $`8/3<t\le4`$, that maximum is $`2t^2+(8-2t)^2`$: moving any two interior coordinates at fixed sum to an endpoint increases the convex objective for at least one endpoint, leaving two coordinates equal to $`t`$, one equal to $`8-2t`$, and one zero. Thus

$$
32-16\delta\le6t^2-32t+64,
\qquad 3t^2-16t+16+8\delta\ge0.
\tag{121.10}
$$

The smaller root is below $`8/3`$ and $`t>7/2`$, so the larger root gives the first eigenvalue bound in (121.2). The strict numerical comparisons follow from $`\delta<1/4`$. This proves the theorem. ∎

### 121.4. An explicit bound in the full-record polar chart

**Corollary 121.2 (uniform opposite-record chart).** Under Theorem 121.1, let $`B_f`$ be the original four-dimensional environment record blocks of $`H`$, and let $`E`$ be the top-two eigenspace of their frame operator. In environment coordinates $`E\oplus E^\perp`$, write

$$
B_f=\begin{bmatrix}C_f\\D_f\end{bmatrix}.
\tag{121.11}
$$

Then $`E`$ is uniquely defined and

$$
\begin{aligned}
\sum_f\|D_f\|_F^2&=\tau<2-\sqrt2,\\
C_f^*C_f&\succeq(1-\tau)I_2\succ(\sqrt2-1)I_2,\\
\|C_f^{-1}\|_{\mathrm{op}}&<\sqrt{1+\sqrt2}
       \qquad\text{for every }f.
\end{aligned}
\tag{121.12}
$$

The records themselves are unchanged; no physical projection and renormalization is performed.

**Proof.** Theorem 121.1 gives $`\lambda_2>2+\sqrt2`$ and $`\lambda_3\le\tau<2-\sqrt2`$, so the frame has a strict top-two gap. Tracing its restriction to $`E^\perp`$ gives $`\sum_f\|D_f\|_F^2=\tau`$. Calibration gives $`C_f^*C_f+D_f^*D_f=I_2`$. Each positive $`D_f^*D_f`$ has trace at most $`\tau`$, so $`C_f^*C_f\succeq(1-\tau)I_2`$. Theorem 121.1 and $`1/(\sqrt2-1)=1+\sqrt2`$ prove (121.12). This is the original full-record polar chart of [RT IV Proposition 117.3](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1173-dominant-two-dimensional-record-spaces), with an explicit stronger bound under (121.1). ∎

For a full-domain calibrated local minimum with ranks $`(7,4)`$, a full-support first kernel, and $`0<\delta<1/4`$, the actual common quotient supplies (121.1). Therefore (121.2), (121.3), and (121.12) hold together with the actual-stress restriction $`\operatorname{Tr}P/\|P\|_{\mathrm{op}}<1129/300`$ of [RT IV Corollary 119.4](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1195-the-full-support-local-minimum-consumer). The explicit bounds improve the previously stated $`\lambda_1>7/2`$, top-two sum greater than seven, and tail less than one; no comparison is made with the unspecified numerical separation in RT IV Theorem 117.4. The intersection of these necessary regions has not been excluded. No full quotient or preserved local-minimum ranks are inferred for arbitrary leaking pairs, and the unrestricted global quarter optimum remains open.

## 追加锚（本行以下为增补区）

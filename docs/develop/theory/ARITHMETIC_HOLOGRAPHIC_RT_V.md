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

## 122. Conditional exclusions from the symmetric-square record frame

### 122.1. The actual quotient and the full-output spectral witness

Retain the original channels, encodings, target, forward-Gram convention, and unhalved arbitrary-reference error $`\delta`$ of (120.1)–(120.4). Assume calibration and the full actual quotient

$$
G,H\succeq0,\qquad G_{ff}=H_{ff}=I_2,\qquad
G=H\odot\bar R,\qquad R\succeq0,\quad R_{ii}=1.
\tag{122.1}
$$

These are identities of the original eight-coordinate Grams. No complementary stress, local-minimum hypothesis, or rank assumption is imposed in this subsection. Define $`\mathcal A=H\odot H`$, using the complex square rather than the entrywise modulus square.

**Proposition 122.1 (symmetric-square spectral obstruction).** Under (122.1),

$$
\delta\ge2-\frac{\operatorname{Tr}(\mathcal A R)}{16}
\ge2-\frac12\lambda_{\max}(\mathcal A).
\tag{122.2}
$$

**Proof.** Use the normalized tagged input and target vector

$$
|\Psi\rangle=\frac12\sum_{f=1}^4|f\rangle_R
 \otimes\frac{|f,0\rangle+|f,1\rangle}{\sqrt2},
\qquad |\Omega\rangle=\frac12\sum_{f=1}^4|f\rangle_R\otimes|f,f\rangle.
\tag{122.3}
$$

As in (121.4)–(121.6), the target output is $`|\Omega\rangle\langle\Omega|`$, and the complete physical product output $`\sigma`$ is a density operator with

$$
\langle\Omega|\sigma|\Omega\rangle
=\frac{\boldsymbol1^*K\boldsymbol1}{32}
=\frac{\operatorname{Tr}(\mathcal A R)}{32}.
\tag{122.4}
$$

The last equality follows from $`K_{ij}=H_{ij}^{2}\bar R_{ij}`$ and Hermiticity of $`R`$. The norm-one observable $`2|\Omega\rangle\langle\Omega|-I`$ acts on the reference and the full sixteen-dimensional physical output, so its expectation gives the first inequality of (122.2). Since $`R\succeq0`$ and $`\operatorname{Tr}R=8`$, the second follows from $`\operatorname{Tr}(\mathcal A R)\le8\lambda_{\max}(\mathcal A)`$. There is no conversion to a halved error. ∎

### 122.2. A tail-free exclusion for correlation lifts

Let $`U_f^{(0)}\in U(2)`$, $`1\le f\le4`$, have columns $`u_{f0}^{(0)},u_{f1}^{(0)}`$, and let $`H^{(0)}`$ be the Gram of these eight qubit records. On $`\operatorname{Sym}^2\mathbb C^2`$, put

$$
q_f^{(0)}=\frac{u_{f0}^{(0)}\otimes u_{f1}^{(0)}
                    +u_{f1}^{(0)}\otimes u_{f0}^{(0)}}{\sqrt2},
\qquad m_0=\lambda_{\min}\!\left(\sum_fq_f^{(0)}q_f^{(0)*}\right).
\tag{122.5}
$$

**Theorem 122.2 (correlation-lift exclusion).** Suppose (122.1) holds and, for some positive semidefinite correlation matrix $`\Xi`$ on all eight original coordinates,

$$
H=H^{(0)}\odot\Xi,\qquad \Xi_{ii}=1.
\tag{122.6}
$$

Then

$$
\lambda_{\max}(H\odot H)\le4-m_0,
\qquad \delta\ge\frac{m_0}{2}.
\tag{122.7}
$$

In particular, the entire subclass (122.6) with $`m_0\ge1/2`$ is excluded when $`\delta<1/4`$. Neither a rank-four hypothesis on $`H`$ nor a bound on its bottom-two spectral trace is required.

**Proof.** For each $`f`$, the vectors $`u_{f0}^{(0)\otimes2},q_f^{(0)},u_{f1}^{(0)\otimes2}`$ form an orthonormal basis of the three-dimensional symmetric square. Hence the frame operator of the eight squared seed records is

$$
Q^{(0)}=\sum_{f,i}|u_{fi}^{(0)\otimes2}\rangle
                      \langle u_{fi}^{(0)\otimes2}|
=4I_3-\sum_fq_f^{(0)}q_f^{(0)*}.
\tag{122.8}
$$

Its nonzero spectrum is that of $`\mathcal A_0=H^{(0)}\odot H^{(0)}`$, so $`\lambda_{\max}(\mathcal A_0)=4-m_0`$. The Schur product $`\Xi\odot\Xi`$ is positive semidefinite and has diagonal one. Thus Schur multiplication by it is positive and unital, and

$$
0\preceq\mathcal A_0\preceq(4-m_0)I_8
\quad\Longrightarrow\quad
0\preceq\mathcal A_0\odot(\Xi\odot\Xi)
\preceq(4-m_0)I_8.
\tag{122.9}
$$

This standard positivity step follows, for example, by writing a positive matrix as a sum of $`vv^*`$ and using $`X\odot vv^*=\operatorname{diag}(v)X\operatorname{diag}(v)^*`$; see Levick and Martin, [*Matrix N-dilations of quantum channels*, Example 6](https://doi.org/10.7153/oam-2018-12-59). The middle matrix in (122.9) is $`H\odot H`$. Proposition 122.1 proves the error bound. ∎

Condition (122.6) is a structural restriction, not a factorization asserted for every remaining rank-four Gram. It includes records $`u_{fi}^{(0)}\otimes w_{fi}`$ for arbitrary unit ancillary records $`w_{fi}`$. The quantity $`m_0`$ belongs to the seed bases; it is not identified with the missing-direction minimum of the actual polar chart below.

### 122.3. Tetrahedral seed families

**Corollary 122.3 (tetrahedral correlation lifts).** Set $`c=1/\sqrt3`$, $`d=\sqrt{2/3}`$, and $`\omega=-1/2+i\sqrt3/2`$. Let

$$
U_1^{(0)}=I_2,\qquad
U_f^{(0)}=\begin{pmatrix}c&-d\bar\omega^{\,f-2}\\
d\omega^{f-2}&c\end{pmatrix},\quad f=2,3,4.
\tag{122.10}
$$

Every actual quotient pair satisfying (122.1) whose opposite Gram is a correlation lift (122.6) of these bases obeys $`\delta\ge2/3`$. The blocks (122.12) below give a rank-four correlation lift with bottom-two trace $`2/5`$.

**Proof.** In the orthonormal symmetric basis $`(e_0^{\otimes2},(e_0\otimes e_1+e_1\otimes e_0)/\sqrt2,e_1^{\otimes2})`$, the missing directions are

$$
q_1^{(0)}=(0,1,0)^{\mathsf T},\qquad
q_f^{(0)}=\frac13(-2\bar\omega^{\,f-2},-1,2\omega^{f-2})^{\mathsf T}
\quad(f=2,3,4).
\tag{122.11}
$$

The identities $`1+\omega+\omega^2=0`$ and $`|\omega|=1`$ give $`\sum_fq_f^{(0)}q_f^{(0)*}=\tfrac43I_3`$. Therefore $`m_0=4/3`$, and Theorem 122.2 proves the error bound.

For a rank-four member of this structural family, take original record blocks

$$
V_f=\begin{bmatrix}\sqrt{19/20}\,U_f^{(0)}\\
t_f\sqrt{1/20}\,U_f^{(0)}\end{bmatrix},\qquad
(t_1,t_2,t_3,t_4)=(1,1,-1,-1).
\tag{122.12}
$$

Their Gram has (122.6) with $`\Xi_{fi,gj}=19/20+t_ft_g/20`$, which is the Gram of unit ancillary vectors. Its frame is $`\operatorname{diag}(19/5,19/5,1/5,1/5)`$: each diagonal block follows from unitarity, and the off-diagonal blocks vanish because $`\sum_ft_f=0`$. Thus its bottom-two trace is $`2/5`$, yet Corollary 122.3 still excludes every subquarter actual quotient over this Gram. This calculation asserts no compatible rank-seven $`G`$, common normer, or local minimum. ∎

### 122.4. Exclusion sectors in the unchanged-record polar chart

Assume now (122.1), $`\operatorname{rank}H=4`$, and $`\delta<1/4`$. Write the original four isometric record blocks, in the actual top-two environment space $`E`$ and its orthogonal complement, as

$$
V_f=\begin{bmatrix}C_f\\D_f\end{bmatrix},\qquad
C_f=U_f A_f,\quad A_f=(I_2-D_f^*D_f)^{1/2},\quad U_f\in U(2),
\qquad \tau=\sum_f\|D_f\|_F^2=\lambda_3(H)+\lambda_4(H).
\tag{122.13}
$$

The chart and its invertibility follow from Corollary 121.2 and [RT IV Proposition 117.3](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1173-dominant-two-dimensional-record-spaces). In particular, $`\tau<2-\sqrt2<1`$. The records and channels themselves are unchanged.

Let $`u_{f0},u_{f1}`$ be the columns of $`U_f`$. On $`\operatorname{Sym}^2E`$, define

$$
\begin{aligned}
q_f&=(u_{f0}\otimes u_{f1}+u_{f1}\otimes u_{f0})/\sqrt2,
&m&=\lambda_{\min}\!\left(\sum_fq_fq_f^*\right),\\
B_f&=U_fA_fU_f^*,&T_f&=\operatorname{Sym}^2(B_f),\\
d_{fi}&=\|D_fe_i\|^2,&r_{\mathrm{tail}}&=2\tau-\sum_{f,i}d_{fi}^{2},\\
F_{\mathrm{att}}&=\sum_f(I_3-T_f^2)+\sum_f(T_fq_f)(T_fq_f)^*,
&\beta&=\lambda_{\min}(F_{\mathrm{att}}).
\end{aligned}
\tag{122.14}
$$

Here $`\operatorname{Sym}^2(B_f)`$ is the restriction of $`B_f\otimes B_f`$ to the symmetric tensor space. The symbol $`r_{\mathrm{tail}}`$ is a tensor-frame tail trace, unrelated to the stress effective rank in §120.

**Theorem 122.4 (actual polar and attenuated exclusion bounds).** Under these hypotheses,

$$
\begin{aligned}
\lambda_{\max}(H\odot H)&\le4-\beta+r_{\mathrm{tail}},
&\delta&\ge\frac{\beta-r_{\mathrm{tail}}}{2},\\
\beta&\ge m-2\tau,
&\delta&\ge\frac m2-2\tau+\frac12\sum_{f,i}d_{fi}^{2}.
\end{aligned}
\tag{122.15}
$$

Consequently every rank-four subquarter pair under these hypotheses must have $`\beta-r_{\mathrm{tail}}<1/2`$ and $`m<1/2+4\tau`$.

**Proof.** Put $`h_{fi}=V_fe_i`$. The Gram of the eight vectors $`h_{fi}^{\otimes2}`$ is $`H\odot H`$, whose nonzero spectrum equals that of their positive frame operator $`Q`$ on $`\operatorname{Sym}^2\mathbb C^4`$. Decompose the latter space as $`\operatorname{Sym}^2E`$ and its seven-dimensional orthogonal complement, and write $`Q=(Q_{ab})_{a,b=0,1}`$. Since $`\|h_{fi}\|=1`$ and $`\|C_fe_i\|^2=1-d_{fi}`$,

$$
\operatorname{Tr}Q_{11}
=\sum_{f,i}\bigl(1-(1-d_{fi})^2\bigr)=r_{\mathrm{tail}}.
\tag{122.16}
$$

For a positive block matrix, Cauchy–Schwarz for its positive form gives

$$
|\langle x,Q_{01}y\rangle|^2
\le\langle x,Q_{00}x\rangle\langle y,Q_{11}y\rangle.
\tag{122.17}
$$

Writing $`a=\|Q_{00}\|_{\mathrm{op}}`$ and $`b=\|Q_{11}\|_{\mathrm{op}}`$, its Rayleigh quotient is therefore bounded by
$`(\sqrt a\|x\|+\sqrt b\|y\|)^2\le(a+b)(\|x\|^2+\|y\|^2)`$. Hence

$$
\lambda_{\max}(Q)\le\lambda_{\max}(Q_{00})+\lambda_{\max}(Q_{11})
\le\lambda_{\max}(Q_{00})+r_{\mathrm{tail}}.
\tag{122.18}
$$

The cross blocks of the squared-record frame have been retained in this estimate; no vanishing of $`Q_{01}`$ is assumed.

As in (122.8), set $`P_f=I_3-q_fq_f^*`$. The identity $`C_fe_i=B_fu_{fi}`$ yields

$$
Q_{00}=\sum_fT_fP_fT_f=4I_3-F_{\mathrm{att}},\qquad
\lambda_{\max}(Q_{00})=4-\beta.
\tag{122.19}
$$

Combining (122.18), (122.19), and Proposition 122.1 proves the first line of (122.15).

For the second line, put $`e_f=\|D_f^*D_f\|_{\mathrm{op}}`$. The eigenvalues of $`B_f`$ lie in $`[\sqrt{1-e_f},1]`$, so $`(1-e_f)I_3\preceq T_f\preceq I_3`$ and $`\|T_f-I_3\|_{\mathrm{op}}=e_f`$. Since $`\sum_fe_f\le\tau`$,

$$
\begin{aligned}
\|T_fP_fT_f-P_f\|_{\mathrm{op}}
&=\|(T_f-I_3)P_fT_f+P_f(T_f-I_3)\|_{\mathrm{op}}\le2e_f,\\
\lambda_{\max}(Q_{00})
&\le\lambda_{\max}\!\left(\sum_fP_f\right)+2\tau
=4-m+2\tau.
\end{aligned}
\tag{122.20}
$$

Thus $`\beta\ge m-2\tau`$. Substitute $`r_{\mathrm{tail}}=2\tau-\sum d_{fi}^{2}`$ into the first line of (122.15). Finally, either $`\beta-r_{\mathrm{tail}}\ge1/2`$ or $`m\ge1/2+4\tau`$ would imply $`\delta\ge1/4`$, proving the stated exclusion sectors. ∎

In particular, if the actual polar missing directions satisfy $`\sum_fq_fq_f^*=\tfrac43I_3`$, the sector $`\tau\le5/24`$ is excluded. The structural estimate (122.7) has no tail penalty, but no numerical ordering with (122.15) is asserted when its seed minimum $`m_0`$ differs from the actual polar minimum $`m`$.

The bound $`\tau<2-\sqrt2`$ alone does not imply either exclusion criterion in Theorem 122.4. Theorems 122.2 and 122.4 give conditional exclusions inside the actual-quotient class; they do not prove that every remaining full-support nonisotropic rank-$`(7,4)`$ local minimum belongs to those sectors. No full quotient is inferred for arbitrary leaking local minima, and the unrestricted global quarter optimum remains open.

## 追加锚（本行以下为增补区）

## 123. A strict rank-two quotient gap and a lower spectral-tail bound

### 123.1. The actual calibrated quotient class

Retain the original channels, encodings, target, forward Grams and unhalved arbitrary-reference error $`\delta`$ of (120.1)–(120.4). The physical output is the full sixteen-dimensional $`\mathbb C^4\otimes\mathbb C^4`$. Assume the full actual calibrated quotient

$$
G,H\succeq0,\qquad G_{ff}=H_{ff}=I_2,\qquad
G=H\odot\bar R,\qquad R\succeq0,\quad R_{ii}=1.
\tag{123.1}
$$

All eight original coordinates are retained. No complementary stress or local-minimum hypothesis is imposed yet. On the full calibrated domain, [RT IV (118.1)](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1181-original-domain-and-common-stress-hypotheses) gives the exact norm

$$
\begin{aligned}
F(G,H)&=\mathscr F(G\odot H),\qquad
\mathscr F(K)=\max_{(\rho,W)\in\mathcal C}
                      2\operatorname{Tr}[(T-K)W],\\
\mathcal C&=\{(\rho,W):\rho\succeq0,\ \rho\text{ is fibre-block diagonal},\quad
              \operatorname{Tr}\rho=1,\ 0\preceq W\preceq\rho\}.
\end{aligned}
\tag{123.2}
$$

The formula itself does not require the local-minimum or rank assumptions subsequently imposed in that section. Define

$$
\mathcal Q_2=\{(H,R):H\succeq0,\ H_{ff}=I_2,\ \operatorname{rank}H\le2,
                         \ R\succeq0,\ R_{ii}=1\}.
\tag{123.3}
$$

Calibration forces $`\operatorname{rank}H=2`$ in this set. For each member, $`G=H\odot\bar R`$ is positive semidefinite with $`G_{ff}=I_2`$. Gram realizations $`g_i,h_i`$ give original calibrated Stinespring isometries with columns $`|f(i)\rangle\otimes g_i`$ and $`|f(i)\rangle\otimes h_i`$. The second channel has minimal environment dimension, and hence Kraus rank, two. Thus $`\mathcal Q_2`$ parametrizes physical quotient pairs rather than independent relaxations of their coefficients.

### 123.2. Equality rigidity excludes the rank-two quotient boundary

**Theorem 123.1 (strict rank-two quotient gap).** The minimum

$$
d_Q:=\min_{(H,R)\in\mathcal Q_2}F(H\odot\bar R,H)
       =\frac14+\varepsilon_Q
\qquad\text{has }\varepsilon_Q>0.
\tag{123.4}
$$

No numerical value of $`\varepsilon_Q`$ is specified.

**Proof.** First relate the Bloch axes of four qubit bases to their missing symmetric-square directions in (122.5). For a unit vector $`u=(a,b)^{\mathsf T}`$, every orthogonal unit vector is $`v=\zeta(-\bar b,\bar a)^{\mathsf T}`$ with $`|\zeta|=1`$. In the orthonormal symmetric-square basis $`(e_0^{\otimes2},(e_0\otimes e_1+e_1\otimes e_0)/\sqrt2,e_1^{\otimes2})`$, put

$$
\begin{aligned}
n&=(2\operatorname{Re}(\bar a b),\,
       2\operatorname{Im}(\bar a b),\,|a|^2-|b|^2)^{\mathsf T},\\
q&=\frac{u\otimes v+v\otimes u}{\sqrt2}
   =\zeta Jn,\qquad
J=\begin{pmatrix}-1/\sqrt2&i/\sqrt2&0\\0&0&1\\
                  1/\sqrt2&i/\sqrt2&0\end{pmatrix},
\qquad J^*J=I_3.
\end{aligned}
\tag{123.5}
$$

Indeed the coordinates of $`q/\zeta`$ are $`(-\sqrt2a\bar b,|a|^2-|b|^2,\sqrt2b\bar a)`$. Therefore

$$
\sum_fq_fq_f^*=J\left(\sum_fn_fn_f^{\mathsf T}\right)J^*,\qquad
\lambda_{\min}\!\left(\sum_fq_fq_f^*\right)
 =\lambda_{\min}\!\left(\sum_fn_fn_f^{\mathsf T}\right).
\tag{123.6}
$$

Independent column phases change each $`q_f`$ by a phase. A within-fibre bit swap fixes $`q_f`$ and negates $`n_f`$. An environment unitary induces a unitary on the symmetric square. The axes of $`\bar U_f\operatorname{diag}(1,-1)U_f^{\mathsf T}`$ used in [RT II §82](ARITHMETIC_HOLOGRAPHIC_RT_II.md#82-quarter-error-rigidity-minimal-kraus-product-and-the-complete-rank-two-party-family) reflect the second coordinate of the axes in (123.5). This common orthogonal reflection also preserves (123.6). Hence the frame eigenvalues are compatible with exactly the equivalences allowed in that equality classification.

Every member of $`\mathcal Q_2`$ has $`\delta\ge1/4`$ by the original rank-two-party lower bound in RT II §82.2 (5). Suppose equality holds. By RT II §§82.9–82.12, after environment isometries and simultaneous within-fibre bit swaps in the two parties, its four balanced Bloch axes have a disphenoid Gram with nonzero eigenvalues

$$
4x^2,\quad4y^2,\quad4z^2,\qquad
x^2+y^2+z^2=1,\qquad x^2,y^2,z^2\ge\frac27.
\tag{123.7}
$$

These swaps simultaneously permute $`H,R`$ and preserve (123.1); the environment isometries preserve the Grams. Equations (123.6)–(123.7) give $`m_0\ge8/7`$. Apply Theorem 122.2 with the seed $`H^{(0)}=H`$ itself and the all-ones correlation matrix $`\Xi=J_8`$. It gives

$$
\delta\ge\frac{m_0}{2}\ge\frac47>\frac14,
\tag{123.8}
$$

contradicting the assumed equality. The number $`4/7`$ is used only in this hypothetical-equality contradiction; it is not asserted as a bound for every member of $`\mathcal Q_2`$.

Finally $`\mathcal Q_2`$ is nonempty, by taking four identical qubit bases and $`R=I_8`$. Its positive-semidefinite, calibration, correlation and rank-at-most-two conditions are closed; all entries have modulus at most one. Thus it is compact. The fixed feasible set $`\mathcal C`$ in (123.2) is compact, so the maximum of its continuously parameterized linear objectives is continuous in $`H,R`$. The norm attains its minimum on $`\mathcal Q_2`$. Since every member has error strictly greater than $`1/4`$, that minimum is also strictly greater than $`1/4`$. ∎

### 123.3. A full-norm comparison retaining the same actual correlation

**Theorem 123.2 (same-correlation polar comparison).** Suppose (123.1) holds and, with eigenvalues in decreasing order,

$$
\tau=8-\lambda_1(H)-\lambda_2(H)<1.
\tag{123.9}
$$

Then

$$
\delta\ge d_Q-\eta(\tau),\qquad
\eta(\tau)=2\tau+8(1-\sqrt{1-\tau})\le10\tau.
\tag{123.10}
$$

No rank-four assumption is needed for this comparison.

**Proof.** For two Hermitian coefficients $`K,K'`$ with the same original fibre blocks, set $`E=K-K'`$. For every feasible $`(\rho,W)`$ in (123.2),

$$
\operatorname{Tr}(E\rho)=0,\qquad
2\operatorname{Tr}(EW)=\operatorname{Tr}[E(2W-\rho)],\qquad
-\rho\preceq2W-\rho\preceq\rho.
\tag{123.11}
$$

If $`\Pi_+,\Pi_-`$ are the positive and negative spectral projections of $`X=2W-\rho`$, the last inequalities give $`\operatorname{Tr}|X|\le\operatorname{Tr}[(\Pi_++\Pi_-)\rho]\le1`$. This includes singular densities. Trace-norm duality and the common feasible set yield

$$
|\mathscr F(K)-\mathscr F(K')|\le\|K-K'\|_{\mathrm{op}}.
\tag{123.12}
$$

The factor two in (123.2) has been retained throughout.

Because the four calibrated record blocks are isometries, their frame is bounded by $`4I`$, so $`H\preceq4I`$. Equation (123.9) gives $`\lambda_2(H)>3`$ and $`\lambda_3(H)<1`$. In the unique top-two environment subspace and its orthogonal complement, use the unchanged-record polar chart of [RT IV Proposition 117.3](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1173-dominant-two-dimensional-record-spaces):

$$
V_f=\begin{bmatrix}C_f\\D_f\end{bmatrix},\qquad
C_f=U_f\sqrt{I_2-D_f^*D_f},\qquad U_f\in U(2),\qquad
\sum_f\|D_f\|_F^2=\tau.
\tag{123.13}
$$

Each $`D_f^*D_f\preceq\tau I_2<I_2`$, so the polar factors are well-defined. Concatenate $`U=[U_1\ \cdots\ U_4]`$, and similarly $`C,D`$, and define the comparison pair

$$
H^{(0)}=U^*U,\qquad G^{(0)}=H^{(0)}\odot\bar R,\qquad
K^{(0)}=(H^{(0)}\odot H^{(0)})\odot\bar R.
\tag{123.14}
$$

Here $`R`$ is the same actual matrix as in (123.1). The pair is a physical member of $`\mathcal Q_2`$. It need not share the original pair's null vector, complementary stress or local-minimum property.

Let $`d_k`$ be the eight eigenvalues of the four $`D_f^*D_f`$, so $`d_k\ge0`$ and $`\sum_kd_k=\tau`$. Rationalizing the square roots gives

$$
\begin{aligned}
\|C-U\|_{\mathrm{op}}^2
&\le\|C-U\|_F^2
 =\sum_k\left(\frac{d_k}{1+\sqrt{1-d_k}}\right)^2\\
&\le\frac{\sum_kd_k^2}{(1+\sqrt{1-\tau})^2}
 \le(1-\sqrt{1-\tau})^2.
\end{aligned}
\tag{123.15}
$$

Since $`\|C\|_{\mathrm{op}}\le2`$, $`UU^*=4I_2`$ and $`\|D^*D\|_{\mathrm{op}}\le\tau`$, the exact decomposition $`H=C^*C+D^*D`$ gives

$$
\|H-H^{(0)}\|_{\mathrm{op}}
\le\tau+4(1-\sqrt{1-\tau}).
\tag{123.16}
$$

Schur multiplication by any positive semidefinite correlation matrix is positive and unital, as in (122.9); see Levick and Martin, [*Matrix N-dilations of quantum channels*, Example 6](https://doi.org/10.7153/oam-2018-12-59). Applying it to $`-\|X\|_{\mathrm{op}}I\preceq X\preceq\|X\|_{\mathrm{op}}I`$ shows that it contracts the operator norm of Hermitian $`X`$. Apply this first to the two summands in

$$
H\odot H-H^{(0)}\odot H^{(0)}
=(H-H^{(0)})\odot H+(H-H^{(0)})\odot H^{(0)},
\tag{123.17}
$$

and then to $`\bar R`$. These are complex squares, not entrywise modulus squares. Since $`K=(H\odot H)\odot\bar R`$, (123.12) and (123.16) imply

$$
|F(G,H)-F(G^{(0)},H^{(0)})|
\le\|K-K^{(0)}\|_{\mathrm{op}}
\le2\tau+8(1-\sqrt{1-\tau})\le10\tau.
\tag{123.18}
$$

The final inequality uses $`\sqrt{1-\tau}\ge1-\tau`$. Theorem 123.1 applies to the comparison pair and proves (123.10). All comparisons use the complete original norm; no monotonicity under polar replacement is asserted. ∎

### 123.4. Excluding a near-rank-two sector of the remaining rank-four class

**Corollary 123.3 (positive lower spectral tail).** Under (123.1) and (123.9), if $`\delta<1/4`$, then

$$
\eta(\tau)>\varepsilon_Q,\qquad
\tau>\frac{\varepsilon_Q}{10}.
\tag{123.19}
$$

In particular, if $`\operatorname{rank}H=4`$, then the actual quotient satisfies

$$
\frac{\varepsilon_Q}{10}
 <\lambda_3(H)+\lambda_4(H)<2-\sqrt2.
\tag{123.20}
$$

**Proof.** Equation (123.10) and $`\delta<1/4`$ give $`\varepsilon_Q<\eta(\tau)\le10\tau`$. In the rank-four case, Theorem 121.1 supplies $`\tau=\lambda_3(H)+\lambda_4(H)<2-\sqrt2<1`$, so its hypotheses supply (123.9) and its upper bound completes (123.20). ∎

Consequently the actual-quotient sector $`0\le\tau\le\varepsilon_Q/10`$, and more sharply the sector $`\eta(\tau)\le\varepsilon_Q`$, cannot have error below one quarter. This applies in particular to the full-domain calibrated local minima with $`\operatorname{rank}G=7`$, $`\ker G=\mathbb C a`$ with every $`a_i\ne0`$, $`\operatorname{rank}H=4`$ and $`0<\delta<1/4`$. Their actual quotient, full complementary stress and identity $`\operatorname{ran}R=\ker(H\operatorname{diag}(a))`$ follow from [RT IV §118](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#118-feasible-chord-polarization-and-full-rank-opposite-stresses). Those properties remain attached to the original pair and are not transported to (123.14).

The gap and comparison above combine the rank-two equality classification with the symmetric-square obstruction. The nonnumerical separation in [RT IV Theorem 117.4](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1174-a-uniform-but-nonnumerical-separation) bounds the spectral tail from above; no numerical comparison of its unknown constant with $`\varepsilon_Q`$ is asserted. The original-channel neighborhoods in [RT III §89](ARITHMETIC_HOLOGRAPHIC_RT_III.md#89-an-unrestricted-local-quarter-minimum-from-analytic-descent-at-the-scalar-cone) also obstruct approaching rank-two quarter centers from the physical subquarter set. Here the stronger endpoint statement is that the entire rank-two quotient class has a minimum strictly above one quarter, and (123.18) supplies an explicit same-correlation comparison modulus. The value of that positive gap remains uncomputed. The inequalities do not exclude the whole remaining rank-four class, supply a feasible member of it, or extend the quotient hypothesis to arbitrary leaking local minima. The unrestricted quarter-optimum problem remains open.

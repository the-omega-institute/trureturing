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

## 追加锚（本行以下为增补区）

## 124. An explicit rank-two quotient gap and a computable lower spectral tail

### 124.1. Quantitative stability of the calibrated support witness

Retain the original channels, encodings, target, forward-Gram convention and unhalved arbitrary-reference error $`\delta`$ of (120.1)–(120.4). First assume only that both original channels are calibrated and the second has environment dimension two. Its four record blocks are unitaries $`U_f\in U(2)`$; write the first party's record blocks as isometries $`A_f:\mathbb C^2\to E_A`$. The full physical output is still $`\mathbb C^4\otimes\mathbb C^4`$. No quotient condition is needed in this subsection.

Following [RT II §82.2](ARITHMETIC_HOLOGRAPHIC_RT_II.md#822-correct-output-contractions-and-an-equality-sensitive-support-witness), equip coefficient matrices with the Hilbert–Schmidt inner product and define

$$
\begin{aligned}
C_f&=\frac{A_fU_f^{\mathsf T}}{\sqrt2},&
N_f&=\bar U_f ZU_f^{\mathsf T},& Z&=\operatorname{diag}(1,-1),\\
D_f&=C_fN_f,&S&=\frac14\sum_fC_f,&
p&=\|S\|_F^2,\qquad a=4-4p.
\end{aligned}
\tag{124.1}
$$

Every $`N_f`$ is a traceless Hermitian unitary, and every $`C_f,D_f`$ has Frobenius norm one. Write $`N_f=n_f\cdot\sigma`$ in a fixed Pauli basis, where $`n_f\in\mathbb R^3`$ is a unit vector, and put

$$
N=[n_1\ n_2\ n_3\ n_4],\qquad
m=\lambda_{\min}(NN^{\mathsf T}).
\tag{124.2}
$$

**Proposition 124.1 (quantitative support stability).** Under these original calibrated rank-two-party hypotheses, $`\delta\ge1/4`$. If $`\delta<3/8`$, then

$$
m\ge
\frac{\bigl(\sqrt{2-4\delta}-\sqrt{4\delta-1}\bigr)^2}
     {3/4+\delta/2}.
\tag{124.3}
$$

**Proof.** Let $`Q`$ be the orthogonal projection in the coefficient-matrix Hilbert space onto $`\mathcal L_S=\{SX:\operatorname{Tr}X=0\}`$. Let $`B,L`$ be the maps with four columns $`D_f,SN_f`$, respectively, and set $`B_Q=QB`$, $`B_\perp=(I-Q)B`$. The centroid identity and invariance of Frobenius norm under right multiplication by $`N_f`$ give

$$
\begin{aligned}
a&=\sum_f\|C_f-S\|_F^2
  =\sum_f\|D_f-SN_f\|_F^2\\
 &=\|B_Q-L\|_F^2+\|B_\perp\|_F^2.
\end{aligned}
\tag{124.4}
$$

Here the final decomposition is orthogonal because $`SN_f\in\mathcal L_S`$.

Let $`C_{\mathrm{gram}}`$ be the Gram of the four $`C_f`$, let $`M=B^*B`$, and let $`X_{fg}=\langle C_f,D_g\rangle`$. In the plus/minus bit basis, with all plus coordinates first, the actual product Gram and target coefficient are

$$
\widehat K=\begin{pmatrix}C_{\mathrm{gram}}&X\\X^*&M\end{pmatrix},
\qquad \widehat T=\operatorname{diag}(J_4,I_4).
\tag{124.5}
$$

The cross block $`X`$ is retained. The normalized no-reference inputs

$$
|\psi_\pm\rangle=\frac12\sum_{f=1}^4|f,\pm\rangle,
\qquad |f,\pm\rangle=\frac{|f,0\rangle\pm|f,1\rangle}{\sqrt2}
\tag{124.6}
$$

have physical product outputs $`C_{\mathrm{gram}}^{\mathsf T}/4`$ and $`M^{\mathsf T}/4`$ on the output MC support, with respective target outputs $`J_4/4`$ and $`I_4/4`$. These are exact supported outputs inside the full sixteen-dimensional physical output. Both differences have trace zero. For $`s=\boldsymbol1/2`$, the centroid definition gives

$$
s^*(C_{\mathrm{gram}}-J_4)s=-a,
\qquad \delta\ge\frac a2,
\qquad \operatorname{Tr}(I_4-M)_+\le2\delta.
\tag{124.7}
$$

The first error bound uses a Rayleigh value, not an assumed eigenvector relation.

Next let $`r=\dim\ker B_Q\ge1`$, and let $`\Pi`$ project onto that kernel. Use the normalized full-reference input

$$
|\Omega_8\rangle=\frac1{\sqrt8}\sum_{f,i}
              |f,i\rangle_R\otimes|f,i\rangle_{\mathrm{logical}}.
\tag{124.8}
$$

On the exact support spanned by $`|f,i\rangle_R\otimes|f,f\rangle_{\mathrm{out}}`$, the physical difference is $`(K^{\mathsf T}-T)/8`$. This is a subspace of reference dimension eight times physical output dimension sixteen. Change to the plus/minus coordinates and transpose the test projection along with the forward-Gram matrix. The negative-part test $`\operatorname{diag}(ss^*,\Pi)`$ then gives

$$
\delta\ge\frac{a+r-\operatorname{Tr}(B\Pi B^*)}{4}
       \ge\frac r4\ge\frac14.
\tag{124.9}
$$

Indeed $`B\Pi=B_\perp\Pi`$ and (124.4) imply $`\operatorname{Tr}(B\Pi B^*)\le a`$. The denominator four in (124.9) is the trace-zero positive-part factor two applied to the normalized eighth in (124.8); the error remains unhalved.

Assume now $`\delta<3/8`$. Equation (124.9) forces $`r=1`$. Choose a unit vector $`v`$ spanning $`\ker B_Q`$ and set $`b=\|Bv\|^2=\|B_\perp v\|^2`$. Equations (124.4) and (124.9) give the exact slack decomposition and bound

$$
\begin{aligned}
0\le a-b
 &=\|B_Q-L\|_F^2
   +\|B_\perp(I-vv^*)\|_F^2\le4\delta-1,\\
\|B_Q-L\|_{\mathrm{op}}&\le\sqrt{4\delta-1}.
\end{aligned}
\tag{124.10}
$$

Testing the last inequality of (124.7) with $`vv^*`$ gives $`1-b\le2\delta`$. Since $`b\le a`$,

$$
a\ge1-2\delta,\qquad
p=1-\frac a4\le\frac34+\frac\delta2.
\tag{124.11}
$$

Let $`\mu`$ be the least positive eigenvalue of the rank-three matrix $`B_Q^*B_Q`$, and choose a unit eigenvector $`w\perp v`$ for it. Testing (124.7) with $`vv^*+ww^*`$ yields

$$
\begin{aligned}
2\delta
&\ge2-\|Bv\|^2-\|Bw\|^2\\
&=2-b-\mu-\|B_\perp w\|^2\\
&\ge2-\mu-\|B_\perp\|_F^2
 \ge2-\mu-a.
\end{aligned}
\tag{124.12}
$$

Only orthonormality of $`v,w`$ is used to bound their combined $`B_\perp`$ energy. Neither vector is assumed real or an eigenvector of $`M`$. Since $`a\le2\delta`$ by (124.7),

$$
\mu\ge2-4\delta,
\qquad
s_3(L)\ge\sqrt{2-4\delta}-\sqrt{4\delta-1}>0.
\tag{124.13}
$$

For the singular-value inequality, $`B_Q`$ has lower norm bound $`\sqrt\mu`$ on the three-dimensional space $`v^\perp`$. Subtract the operator-norm error in (124.10), and apply the singular-value max–min principle on that space.

The map $`L`$ factors through $`N`$ followed by $`y\mapsto S(y\cdot\sigma)`$, so $`\operatorname{rank}L\le\operatorname{rank}N\le3`$. The strict positivity in (124.13) forces both ranks to be three, and their complex kernels coincide. Choose a real unit eigenvector $`y`$ of $`NN^{\mathsf T}`$ with eigenvalue $`m>0`$, and define $`x=N^{\mathsf T}y/\sqrt m`$. Then $`x`$ is real, unit, orthogonal to $`\ker N=\ker L`$, and

$$
Nx=\sqrt m\,y,\qquad
N(x):=\sum_fx_fN_f=N(x)^*,\qquad N(x)^2=mI_2.
\tag{124.14}
$$

Consequently, without assuming that $`S^*S`$ is scalar or commutes with $`N(x)`$,

$$
\begin{aligned}
s_3(L)^2&\le\|Lx\|_F^2
 =\operatorname{Tr}[N(x)S^*SN(x)]\\
 &=\operatorname{Tr}[S^*SN(x)^2]=pm.
\end{aligned}
\tag{124.15}
$$

Equations (124.11), (124.13) and (124.15) prove (124.3). The real-vector test uses the actual Bloch-axis matrix, not a lower frame bound inferred from pairwise dot products. ∎

### 124.2. An explicit gap for every rank-two actual quotient

**Theorem 124.2 (computable rank-two quotient gap).** For every member of the full actual calibrated quotient class $`\mathcal Q_2`$ in (123.3),

$$
\delta>\frac{29}{108}=\frac14+\frac1{54}.
\tag{124.16}
$$

In particular, the attained minimum and gap in (123.4) satisfy

$$
d_Q>\frac{29}{108},\qquad \varepsilon_Q>\frac1{54}.
\tag{124.17}
$$

These are lower bounds; they do not specify the exact values of $`d_Q`$ or $`\varepsilon_Q`$.

**Proof.** Such a quotient has original calibrated Gram realizations with the second environment two-dimensional, as established in §123.1. Suppose $`\delta\le29/108`$. Proposition 124.1 gives $`\delta\ge1/4`$, and its proof supplies

$$
2-4\delta\ge\frac{25}{27},\qquad
4\delta-1\le\frac2{27},\qquad
p\le\frac{191}{216}.
\tag{124.18}
$$

Thus (124.13)–(124.15) imply

$$
s_3(L)\ge\frac{5-\sqrt2}{\sqrt{27}},\qquad
m\ge\frac{216-80\sqrt2}{191}.
\tag{124.19}
$$

The Bloch axes in (124.2) use $`\bar U_fZU_f^{\mathsf T}`$. Equations (123.5)–(123.6), including their common-reflection observation, identify their frame spectrum with that of the four missing symmetric-square directions for the same original qubit bases. Apply Theorem 122.2 with seed $`H^{(0)}=H`$ and $`\Xi=J_8`$. This is where the full actual quotient $`G=H\odot\bar R`$ is used. It gives

$$
\delta\ge\frac m2
 \ge\frac{108-40\sqrt2}{191}
 >\frac{154}{573}>\frac{29}{108}.
\tag{124.20}
$$

The strict comparisons are exact: $`\sqrt2<17/12`$ because $`2<289/144`$, and $`154\cdot108-29\cdot573=15>0`$. This contradicts the assumed upper bound and proves (124.16). The minimum over $`\mathcal Q_2`$ is attained by the compactness and continuity argument in Theorem 123.1, so (124.17) follows. No exact-quarter classification is needed for this quantitative proof. ∎

### 124.3. An explicit excluded near-rank-two sector

**Corollary 124.3 (computable lower spectral tail).** Suppose the full actual calibrated quotient (123.1) holds, and let $`\tau=8-\lambda_1(H)-\lambda_2(H)<1`$. If $`\delta<1/4`$, then

$$
\eta(\tau)>\frac1{54},\qquad \tau>\frac1{325}.
\tag{124.21}
$$

In particular, for $`\operatorname{rank}H=4`$ the remaining subquarter actual quotient must satisfy

$$
\frac1{325}<\lambda_3(H)+\lambda_4(H)<2-\sqrt2.
\tag{124.22}
$$

**Proof.** The same-actual-$`R`$ comparison in Theorem 123.2 gives $`\delta\ge d_Q-\eta(\tau)`$. Since $`\delta<1/4`$, (124.17) implies $`\eta(\tau)>\varepsilon_Q>1/54`$. For $`0\le\tau<1`$, rationalization and $`\sqrt{1-\tau}\ge1-\tau`$ give

$$
\eta(\tau)=2\tau+\frac{8\tau}{1+\sqrt{1-\tau}}
 \le2\tau+\frac{8\tau}{2-\tau}.
\tag{124.23}
$$

If $`\tau\le1/325`$, both terms on the right are bounded by their values at $`1/325`$, so

$$
\eta(\tau)\le\frac2{325}+\frac8{649}
 =\frac{3898}{210925}<\frac1{54},
\qquad 3898\cdot54=210492<210925.
\tag{124.24}
$$

This is a contradiction. In the rank-four case Theorem 121.1 already gives $`\tau=\lambda_3(H)+\lambda_4(H)<2-\sqrt2<1`$, which supplies the comparison hypothesis and the upper endpoint in (124.22). ∎

The new content is the quantitative calibrated support-slack estimate (124.3) and its combination with the actual quotient's symmetric-square obstruction. It makes the lower spectral-tail exclusion in §123 computable. The linear-algebra and channel-norm background is standard; see Watrous, [*The Theory of Quantum Information*, Chapters 1 and 3](https://cs.uwaterloo.ca/~watrous/TQI/). The argument uses the full original unhalved norm, and the polar comparison retains the same actual correlation matrix. No complementary stress or local-minimum property is transferred to a comparison pair. The intermediate-tail rank-four class is still open, and neither (124.16) nor (124.22) supplies a feasible member or settles the unrestricted quarter-optimum problem.

## 125. First-record concentration forces common-stress concentration

### 125.1. The actual quotient and an effective-rank bound

Retain the original channels, correlated encoding, forward-Gram convention, full sixteen-dimensional product output and unhalved arbitrary-reference error $`\delta=F(G,H)`$ of (120.1)–(120.4). Suppose the actual channels are calibrated and satisfy

$$
\begin{aligned}
&G,H\succeq0,\qquad G_{ff}=H_{ff}=I_2,\qquad
G=H\odot\bar R,\qquad R\succeq0,\quad R_{ii}=1,\\
&P=\alpha D_aRD_a^*\succeq0,\qquad PH=0,\qquad
\alpha>0,\quad a_i\ne0,\quad D_a=\operatorname{diag}(a).
\end{aligned}
\tag{125.1}
$$

These are the full actual-quotient and complementary-stress hypotheses of [RT IV (119.2)](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1191-actual-channels-and-the-full-quotient-hypothesis). Define

$$
\lambda=\|P\|_{\mathrm{op}},\qquad
x_i=P_{ii}/\lambda,\qquad X=\operatorname{diag}(x),\qquad
r=\operatorname{Tr}P/\lambda=\sum_i x_i,\qquad m=\max_i x_i.
\tag{125.2}
$$

All $`x_i`$ are positive. Write $`\kappa_k(G)=\sum_{j=1}^k\lambda_j(G)`$ for the decreasing spectral sums, with $`\kappa_0(G)=0`$, and set $`\tau_G=8-\kappa_2(G)`$. This is the first-Gram tail; it is distinct from the opposite rank-four tail $`\tau_H=\lambda_3(H)+\lambda_4(H)`$ in §§121–124.

**Theorem 125.1 (actual-stress concentration).** Under (125.1),

$$
\boxed{\quad
0<m\le\frac34,\qquad
r\le2+m\tau_G\le2+4m\delta\le2+3\delta.
\quad}
\tag{125.3}
$$

Consequently

$$
\boxed{\quad
\delta\ge\max\left\{0,\frac{r-2}{4m}\right\}
\ge\max\left\{0,\frac{r-2}{3}\right\},\qquad
\delta<\frac14\ \Longrightarrow\ r<2+m\le\frac{11}{4}.
\quad}
\tag{125.4}
$$

The theorem does not require local minimality or specified ranks. When (125.1) is supplied by a canonical common normer at a full-domain calibrated minimum, it applies to that same actual stress.

### 125.2. The phase-correct weighted-frame contraction

**Proof.** Let $`E=\operatorname{diag}(a_i/|a_i|)`$. Since $`P_{ii}=\alpha|a_i|^2`$, the actual quotient gives the entrywise identity

$$
\frac{H\odot\bar P}{\lambda}
 =E^*X^{1/2}GX^{1/2}E.
\tag{125.5}
$$

Both sides have entry $`\alpha\bar a_i a_jH_{ij}\bar R_{ij}/\lambda`$. Thus no real gauge or change of physical records is needed. Schur positivity, $`0\preceq\bar P\preceq\lambda I_8`$ and $`H_{ii}=1`$ imply

$$
0\preceq H\odot\bar P\preceq\lambda I_8,
\qquad 0\preceq X^{1/2}GX^{1/2}\preceq I_8.
\tag{125.6}
$$

Positivity of the correlation Schur multiplier is standard; see Levick and Martin, [*Matrix N-dilations of quantum channels*, Example 6](https://doi.org/10.7153/oam-2018-12-59).

Set $`A=G^{1/2}X^{1/2}`$ and $`C=AA^*=G^{1/2}XG^{1/2}`$. Equation (125.6) says $`A^*A\preceq I_8`$, hence $`\|A\|_{\mathrm{op}}\le1`$ and $`C\preceq I_8`$. Also $`X\preceq mI_8`$. Therefore

$$
0\preceq C\preceq I_8,\qquad C\preceq mG,
\qquad \operatorname{Tr}C=\operatorname{Tr}(XG)=r.
\tag{125.7}
$$

The last identity uses $`G_{ii}=1`$. No commutation of $`C,G,X`$ is asserted. Let $`\Pi`$ be a rank-two projection onto a top-two eigenspace of $`G`$. Since $`\operatorname{Tr}G=8`$, the two compressed traces satisfy

$$
\begin{aligned}
r&=\operatorname{Tr}(\Pi C)+\operatorname{Tr}[(I_8-\Pi)C]\\
&\le2+m\operatorname{Tr}[(I_8-\Pi)G]
=2+m\tau_G.
\end{aligned}
\tag{125.8}
$$

Positivity of the compressed differences suffices even when $`\Pi`$ and $`C`$ do not commute. The first two eigenvalues exist because calibration forces $`\operatorname{rank}G\ge2`$.

### 125.3. Original full-output normalization and complementary support

For completeness, the first-Gram estimate in [RT IV Theorem 117.1](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1171-original-channels-and-a-tagged-pure-target) uses the normalized input and target vectors

$$
|\Psi\rangle=\frac12\sum_f|f\rangle_R\otimes
               \frac{|f,0\rangle+|f,1\rangle}{\sqrt2},
\qquad
|\Omega\rangle=\frac12\sum_f|f\rangle_R\otimes|f,f\rangle.
\tag{125.9}
$$

The reference has dimension four and the physical product output has dimension sixteen. The target output is $`|\Omega\rangle\langle\Omega|`$. For the full trace-one product output $`\sigma`$ and $`K=G\odot H`$, the reference tags give

$$
\langle\Omega|\sigma|\Omega\rangle
 =\frac{\boldsymbol1^*K\boldsymbol1}{32},\qquad
\delta\ge2-\frac{\boldsymbol1^*K\boldsymbol1}{16}.
\tag{125.10}
$$

The second inequality tests the full difference against $`2|\Omega\rangle\langle\Omega|-I`$. The forward-Gram transpose conjugates the compressed entries; the complete sum is real by Hermiticity. Thus the original unhalved factor and all output/reference coordinates are retained.

The calibrated record frames are sums of four rank-two projections, so $`0\preceq G,H\preceq4I_8`$ and $`\operatorname{Tr}G=\operatorname{Tr}H=8`$. In an eigenbasis of $`G`$, the diagonal entries $`h_j`$ of $`\bar H`$ obey $`0\le h_j\le4`$, $`\sum_jh_j=8`$. Hence

$$
\begin{aligned}
\boldsymbol1^*K\boldsymbol1
 &=\operatorname{Tr}(G\bar H)=\sum_j\lambda_j(G)h_j\\
 &\le\lambda_1(G)h_1+\lambda_2(G)(8-h_1)
 \le4\kappa_2(G),\\
\delta&\ge2-\frac{\kappa_2(G)}4,\qquad \tau_G\le4\delta.
\end{aligned}
\tag{125.11}
$$

Finally let $`N`$ project onto $`\ker H`$. The actual complementarity and calibrated frame cap imply

$$
P\preceq\lambda N,\qquad H\preceq4(I_8-N),\qquad
x_i\le N_{ii}\le\frac34.
\tag{125.12}
$$

Indeed $`PH=0`$ places the range of $`P`$ in $`\ker H`$, and the diagonal of the second inequality is $`1\le4(1-N_{ii})`$. Thus $`m\le3/4`$. Equations (125.8), (125.11) and (125.12) prove (125.3); rearrangement proves (125.4). ∎

### 125.4. The spectral envelope and the residual common-stress sector

The same contraction has the stronger finite spectral form

$$
r\le\sum_{j=1}^{8}\min\{1,m\lambda_j(G)\}
 =\min_{0\le k\le8}\{k+m(8-\kappa_k(G))\}.
\tag{125.13}
$$

To prove it, evaluate both bounds in (125.7) on an eigenbasis of $`G`$ and sum. The minimizing split occurs where $`m\lambda_j(G)`$ crosses one. This is a trace bound from the two operator inequalities, not a claim that its spectral extremizer is physically realizable.

**Corollary 125.2 (remaining rank-four common-stress region).** Let $`(G,H)`$ be a local minimum on the full calibrated domain of [RT IV (118.1)](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1181-original-domain-and-common-stress-hypotheses), with ranks $`(7,4)`$, a full-support first kernel and $`0<\delta<1/4`$. For its actual common stress and its actual quotient, every earlier support identity remains in force, and

$$
\begin{gathered}
\operatorname{rank}P=\operatorname{rank}R=4,\qquad
\operatorname{ran}P=\ker H,\qquad
\operatorname{ran}R=\ker(HD_a),\\
\frac1{325}<\tau_H<2-\sqrt2,\qquad
r<2+m\le\frac{11}{4}.
\end{gathered}
\tag{125.14}
$$

If $`x_{(1)}\le\cdots\le x_{(8)}=m`$ is the ordered normalized stress diagonal, then also

$$
\sum_{i=1}^{7}x_{(i)}=r-m<2,\qquad
x_{(1)}<\frac27,\qquad x_{(2)}<\frac13.
\tag{125.15}
$$

**Proof.** The same common quotient and rank-four support are [RT IV Corollary 118.3](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1184-subquarter-strict-complementarity). Corollary 124.3 supplies the opposite-tail interval. Apply Theorem 125.1 to that original stress to obtain the remaining bound in (125.14). Subtract $`m`$ to obtain the first inequality in (125.15). Its sum contains seven terms at least $`x_{(1)}`$ and six terms at least $`x_{(2)}`$, giving both strict coordinate bounds. ∎

The measured-diagonal lower bound in (125.4) dominates [RT IV (119.11)](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1193-calibrated-spectral-bounds-and-diagonal-concentration). For $`r>2`$, their pre-truncation difference is

$$
\frac{r-2}{4m}-\left(\frac{r}{4m}-\frac4r\right)
 =\frac{8m-r}{2mr}\ge0,
\tag{125.16}
$$

because $`r=\sum_i x_i\le8m`$. For $`r\le2`$, the older term is at most $`2-4/r\le0`$, so the domination persists after taking the maximum with zero. In particular (125.14) removes the entire effective-rank sector $`11/4\le r<1129/300`$ left by the previous uniform cutoff; the refined formula (119.12) has stated domain $`15/4\le r\le4`$, entirely above that new cutoff. This conclusion uses the actual same stress, rather than optimizing a free positive matrix on its support.


### 125.5. Coupled record tails and an intermediate-tail stress exclusion

**Proposition 125.3 (coupled-tail stress bound).** Assume (125.1) and $`\delta<1/4`$. Put $`u=8-\kappa_2(G)`$ and $`v=8-\kappa_2(H)`$, so $`0\le u,v<1`$. Then

$$
\boxed{\quad
8\delta\ge2u+2v-uv,\qquad
r\le2+m\frac{8\delta-2v}{2-v}
 <2+2m\frac{1-v}{2-v}
 \le2+\frac32\frac{1-v}{2-v}.
\quad}
\tag{125.17}
$$

In particular, in the rank-four setting of Corollary 125.2,

$$
\boxed{\qquad \tau_H\ge\frac12\quad\Longrightarrow\quad r<\frac52.\qquad}
\tag{125.18}
$$

**Proof.** Let $`\lambda_1\ge\cdots\ge\lambda_8`$ be the eigenvalues of the actual first Gram and $`h_j`$ the diagonal entries of $`\bar H`$ in that eigenbasis. Retain $`K=G\odot H`$ and set

$$
D=4\kappa_2(G)-\operatorname{Tr}(G\bar H),\qquad
 t=\sum_{j\ge3}h_j.
\tag{125.19}
$$

The spectral sum variational principle gives $`t\ge8-\kappa_2(H)=v`$. Explicitly, the trace of $`\bar H`$ on the first two eigenvectors of $`G`$ is at most the sum of its two largest eigenvalues, and conjugation preserves the spectrum of $`H`$.

The exact deficit identity in [RT IV (117.12)](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1172-exact-rigidity-at-the-spectral-quarter-boundary), using $`\sum_jh_j=8`$, is

$$
D=(\lambda_1-\lambda_2)(4-h_1)
   +\sum_{j\ge3}(\lambda_2-\lambda_j)h_j.
\tag{125.20}
$$

Every term is nonnegative. Since $`\lambda_1\le4`$ and the eigenvalues after the first two sum to $`u`$,

$$
\lambda_2\ge4-u,\qquad \lambda_3\le u,\qquad
D\ge(\lambda_2-\lambda_3)t\ge(4-2u)v.
\tag{125.21}
$$

Here $`u<1`$ ensures the factor is positive. The same original tagged-input estimate (125.10) gives $`\operatorname{Tr}(G\bar H)\ge16(2-\delta)`$, and hence

$$
D\le4(8-u)-16(2-\delta)=4(4\delta-u).
\tag{125.22}
$$

Combining (125.21)–(125.22) proves $`2u+2v-uv\le8\delta`$. Because $`2-v>0`$, solve for $`u`$ and use $`r\le2+mu`$ from Theorem 125.1. The strict inequality follows from $`\delta<1/4`$, and the last bound uses $`m\le3/4`$. Finally $`(1-v)/(2-v)`$ decreases on $`[0,1)`$ and is $`1/3`$ at $`v=1/2`$. In the rank-four case $`v=\tau_H`$, proving (125.18). ∎

Thus the actual intermediate-tail sector $`1/2\le\tau_H<2-\sqrt2`$ is incompatible with a common stress having $`r\ge5/2`$ at a subquarter full-domain calibrated minimum. The bound couples the two actual Grams and the same actual stress; it does not substitute the opposite tail for the first tail in (125.8). The separated remaining region is still open.

Calibration is used in both the weighted-frame trace identity and the complementary-support cap. The class satisfying the combined stress and tail restrictions remains open, and no feasible minimum in it is asserted. No rank or local-minimum transfer is claimed for arbitrary leaking optimizers, and the unrestricted quarter-optimum problem remains open.

## 追加锚（本行以下为增补区）

## 126. Reciprocal cuts constrain the actual error inertia near the rank-two boundary

### 126.1. The original common normer and the excluded sector

Retain the original four two-coordinate fibres, calibrated channels, fixed correlated encodings, and unhalved arbitrary-reference error $`\delta`$ of (120.1)–(120.4). The physical product output is the full sixteen-dimensional space. Suppose $`(G,H)`$ is a local minimum on the full calibrated domain, including rank-changing competitors, with $`\operatorname{rank}G=7`$, $`\ker G=\mathbb C a`$ and every $`a_i\ne0`$, $`\operatorname{rank}H=4`$, and $`0<\delta<1/4`$. Put $`L=T-G\odot H`$. The exact original norm is

$$
\delta=\max\{2\operatorname{Tr}(LW):
 \rho=\bigoplus_f\rho_f\succeq0,\quad
 \operatorname{Tr}\rho=1,\quad0\preceq W\preceq\rho\},
\qquad T_{ff}=I_2,\quad T_{fg}=J_2/2\ (f\ne g).
\tag{126.1}
$$

This is the calibrated full-norm formula of [RT III Theorem 91.1](ARITHMETIC_HOLOGRAPHIC_RT_III.md#911-original-channels-forward-grams-and-the-adaptive-theorem). Choose any canonical common norming pair from [RT III §95.2](ARITHMETIC_HOLOGRAPHIC_RT_III.md#952-one-rank-seven-side-gives-a-supported-psd-quotient), namely one satisfying the simultaneous first-order conditions for both actual Grams. Its same positive scale and opposite stress obey

$$
\begin{aligned}
G&=H\odot\bar R,\qquad R\succeq0,\quad R_{ii}=1,\\
P&=\alpha\operatorname{diag}(a)R\operatorname{diag}(a)^*,
       \quad PH=0,\quad\alpha>0,\\
W_{ij}&=-\frac{\alpha a_i\overline{a_j}}{2\overline{H_{ij}}}
                 \qquad(f(i)\ne f(j)).
\end{aligned}
\tag{126.2}
$$

All denominators are nonzero. For a union $`A`$ of two complete original fibres, define the four-by-four reciprocal cut and the opposite spectral tail by

$$
Q_A=\bigl(1/\overline{H_{ij}}\bigr)_{i\in A,j\in A^c},
\qquad v=8-\kappa_2(H)=\lambda_3(H)+\lambda_4(H).
\tag{126.3}
$$

Write $`n_+(L),n_-(L),n_0(L)`$ for the strictly positive, strictly negative and zero eigenvalue counts.

**Theorem 126.1 (actual reciprocal cuts and inertia).** Under these hypotheses, if $`v\le1/64`$, then every two-plus-two fibre cut satisfies

$$
\begin{aligned}
\sigma_{\min}(Q_A)&>\frac{93337}{1998848}>0,\\
\operatorname{rank}W&\ge4,\qquad
\operatorname{rank}(\rho-W)\ge4,\\
n_+(L)&\le4,\qquad n_-(L)\le4.
\end{aligned}
\tag{126.4}
$$

The normer conclusions hold for every canonical common pair. If $`L`$ is nonsingular, its inertia is therefore exactly $`(4,4)`$. Thus the nonsingular $`(2,6)`$, $`(3,5)`$ and $`(5,3)`$ branches, and every singular branch with either strict index at least five, are excluded in the actual tail sector $`1/325<v\le1/64`$. The lower endpoint comes from §124; the scalar interval does not assert existence of a physical pair or minimum.

### 126.2. Local polar comparison in the original coordinates

**Proof.** For cross-fibre coordinates, the logical matrix unit $`|i\rangle\langle j|`$ has trace norm one. The corresponding correct entry of the full physical product output is $`\overline{G_{ij}H_{ij}}`$, against target entry $`1/2`$. Bounding that entry by the output trace norm gives the original unhalved test of [RT IV (116.6)–(116.8)](ARITHMETIC_HOLOGRAPHIC_RT_IV.md#1161-the-original-channel-principal-quotient):

$$
\delta\ge\left|\tfrac12-G_{ij}H_{ij}\right|,
\qquad
|H_{ij}|^2\ge|G_{ij}H_{ij}|\ge\tfrac12-\delta>\tfrac14.
\tag{126.5}
$$

Here $`|R_{ij}|\le1`$ in the actual quotient was used; no output compression replaces the norm.

Use the unchanged-record top-two environment chart of (121.11)–(121.12) and (123.13):

$$
V_f=\begin{bmatrix}C_f\\D_f\end{bmatrix},\qquad
C_f=U_fA_f,\quad A_f=(I_2-D_f^*D_f)^{1/2},\quad U_f\in U(2),
\qquad t_f=\|D_f\|_F^2,\quad\sum_ft_f=v.
\tag{126.6}
$$

Since $`v<1`$, the polar factors exist. Define only an auxiliary qubit Gram $`H^{(0)}_{fg}=U_f^*U_g`$. No original stress, null vector or normer is transported to it. The actual cross block is $`H_{fg}=A_fU_f^*U_gA_g+D_f^*D_g`$. Rationalizing the square root and using $`\|A_g\|\le1`$ gives

$$
\begin{aligned}
\|H_{fg}-H^{(0)}_{fg}\|_{\mathrm{op}}
&\le\frac{t_f+t_g}{1+\sqrt{1-v}}+\sqrt{t_ft_g}\\
&\le\frac{v}{1+\sqrt{1-v}}+\frac v2
 \le\frac{v}{2-v}+\frac v2\\
&\le\frac1{127}+\frac1{128}
 =\frac{255}{16256}<\frac1{63}.
\end{aligned}
\tag{126.7}
$$

The last line uses the inclusive endpoint $`v\le1/64`$; the preceding inequality uses $`\sqrt{1-v}\ge1-v`$. Every cross-fibre entry therefore satisfies

$$
|H^{(0)}_{ij}|>\frac12-\frac1{63}
 =\frac{61}{126}>\frac{15}{32}.
\tag{126.8}
$$

### 126.3. Uniform Cauchy conditioning and the actual cuts

Consider the four columns $`u_1,\ldots,u_4`$ of two orthonormal qubit bases and the four columns $`z_1,\ldots,z_4`$ of another two. Suppose every overlap between distinct bases in this collection has magnitude at least $`\ell`$, with $`0<\ell\le1/2`$. Write $`B_{ij}=\langle u_i,z_j\rangle`$, $`Q_{ij}=1/B_{ij}`$, and $`[p,q]=\det[p\ q]`$. The Cauchy determinant and its cofactor formula give

$$
\left|(Q^{-1})_{ji}\right|
 =\frac{\displaystyle\prod_{k=1}^4|B_{kj}|
                     \prod_{l=1}^4|B_{il}|}
 {|B_{ij}|\displaystyle\prod_{k\ne i}|[u_i,u_k]|
                      \prod_{l\ne j}|[z_j,z_l]|}.
\tag{126.9}
$$

For completeness, the standard Cauchy double-alternant identity is recorded in Krattenthaler, [*Advanced Determinant Calculus*, §2.1, equation (2.7), page 6](https://www.mat.univie.ac.at/~slc/wpapers/s42kratt.pdf). Choose a common qubit coordinate chart avoiding the finitely many zero components. Row and column scalings turn the overlaps into $`x_i+y_j`$, so that identity yields the homogeneous formula

$$
|\det Q|
 =\frac{\displaystyle\prod_{i<k}|[u_i,u_k]|
                         \prod_{j<l}|[z_j,z_l]|}
        {\displaystyle\prod_{i,j}|B_{ij}|}.
\tag{126.10}
$$

There are no repeated rays on either side: coincidence across two bases would make the overlap with an orthogonal partner zero. All separation factors in (126.10) are therefore nonzero. Applying the same determinant identity to a three-by-three minor and dividing by (126.10) proves (126.9). Continuity gives the homogeneous identity when an initially chosen chart has zero components. Thus no real gauge or nonzero-coordinate restriction is imposed.

For a fixed unit vector, its two overlaps with an orthonormal basis have squared magnitudes summing to one, and their product is at most $`1/2`$. Each four-overlap product in the numerator of (126.9) is therefore at most $`1/4`$. On either side, the separation from the same-basis partner is one; the other two separations have squared magnitudes summing to one and are each at least $`\ell`$. Their product is at least $`\ell\sqrt{1-\ell^2}`$. Consequently

$$
\max_{i,j}|(Q^{-1})_{ji}|
 \le\frac1{16\ell^3(1-\ell^2)},\qquad
\|Q^{-1}\|_{\mathrm{op}}
 \le\frac1{4\ell^3(1-\ell^2)},\qquad
\sigma_{\min}(Q)\ge4\ell^3(1-\ell^2).
\tag{126.11}
$$

Entrywise conjugation preserves singular values, so this also applies to reciprocal conjugates. Fix any original two-plus-two fibre cut and form its reciprocal-conjugate seed matrix $`Q_A^{(0)}`$ from $`H^{(0)}`$. Equations (126.8) and (126.11), with $`\ell=15/32`$, imply

$$
\sigma_{\min}(Q_A^{(0)})
 \ge4(15/32)^3\bigl(1-(15/32)^2\bigr)
 >3(15/32)^3=\frac{10125}{32768}.
\tag{126.12}
$$

Meanwhile each actual reciprocal entry obeys

$$
\left|\frac1{\overline{H_{ij}}}
       -\frac1{\overline{H^{(0)}_{ij}}}\right|
 =\frac{|H_{ij}-H^{(0)}_{ij}|}{|H_{ij}|\,|H^{(0)}_{ij}|}
 <\frac{1/63}{(1/2)(61/126)}=\frac4{61},
\qquad \|Q_A-Q_A^{(0)}\|_{\mathrm{op}}<\frac{16}{61}.
\tag{126.13}
$$

The last inequality bounds the operator norm by the Frobenius norm of the four-by-four matrix. Testing every unit vector now gives

$$
\sigma_{\min}(Q_A)
 \ge\sigma_{\min}(Q_A^{(0)})-\|Q_A-Q_A^{(0)}\|_{\mathrm{op}}
 >\frac{10125}{32768}-\frac{16}{61}
 =\frac{93337}{1998848}>0.
\tag{126.14}
$$

This proves invertibility for all three unordered fibre cuts. The rational tail endpoint is a conservative choice; no optimal conditioning threshold is asserted.

### 126.4. The same full common normer, including singular error matrices

Because $`\rho`$ is block diagonal in the original fibres, (126.2) gives

$$
W_{A,A^c}
 =-\frac\alpha2\operatorname{diag}(a_A)
                    Q_A\operatorname{diag}(\overline{a_{A^c}}),
\qquad (\rho-W)_{A,A^c}=-W_{A,A^c}.
\tag{126.15}
$$

The diagonal factors are invertible. Each displayed cross block therefore has rank four, so both full normer halves have rank at least four. This also forces the same density to be positive definite. Indeed if $`x\in\ker W_{A,A}`$, positivity of $`W`$ makes it annihilate the extension of $`x`$ by zero. Its $`A^c`$ component is $`W_{A^c,A}x`$, whose invertibility gives $`x=0`$. Thus $`W_{A,A}\succ0`$, and similarly on $`A^c`$. Since $`\rho_A\succeq W_{A,A}`$, $`\rho_{A^c}\succeq W_{A^c,A^c}`$, and $`\rho_{A,A^c}=0`$, one has $`\rho\succ0`$.

The original common pair maximizes (126.1) at its own density. Put $`M=\rho^{1/2}L\rho^{1/2}`$. The fixed-density spectral maximization in [RT III §91.4](ARITHMETIC_HOLOGRAPHIC_RT_III.md#914-primal-dual-and-exact-certificates) gives

$$
W=\rho^{1/2}\bigl(\Pi_+(M)+E_0\bigr)\rho^{1/2},
\qquad 0\preceq E_0\preceq\Pi_0(M).
\tag{126.16}
$$

To retain the singular case explicitly, maximizing $`\operatorname{Tr}(ME)`$ over $`0\preceq E\preceq I`$ forces $`E`$ to be one on positive eigenvectors and zero on negative eigenvectors. Positivity of $`E`$ and $`I-E`$ kills the corresponding off-diagonal entries. Only the contraction on the zero eigenspace remains. Hence

$$
\begin{aligned}
4&\le\operatorname{rank}W
 =n_+(M)+\operatorname{rank}E_0\le8-n_-(M),\\
4&\le\operatorname{rank}(\rho-W)
 =n_-(M)+\operatorname{rank}(\Pi_0(M)-E_0)\le8-n_+(M).
\end{aligned}
\tag{126.17}
$$

Congruence by the positive-definite $`\rho^{1/2}`$ preserves inertia, proving (126.4). If $`L`$ is nonsingular its two strict indices sum to eight, forcing $`(4,4)`$. If it is singular, the same actual zero-space completion must additionally satisfy

$$
\operatorname{rank}E_0\ge\max\{0,4-n_+(L)\},\qquad
\operatorname{rank}(\Pi_0(M)-E_0)\ge\max\{0,4-n_-(L)\}.
\tag{126.18}
$$

No new completion or independently chosen density has been substituted. This proves the theorem. ∎

### 126.5. A high-effective-rank consumer for the same actual stress

**Corollary 126.2.** Under the hypotheses of Theorem 126.1, put $`r=\operatorname{Tr}P/\|P\|_{\mathrm{op}}`$ for the actual stress in (126.2). If $`r\ge697/254`$, then $`v<1/64`$ and all conclusions of that theorem hold.

**Proof.** The coupled actual-tail estimate (125.17) gives

$$
r<2+\frac32\frac{1-v}{2-v},\qquad r<\frac{11}{4},\qquad
v<\frac{11-4r}{7-2r}.
\tag{126.19}
$$

The last expression follows by rearranging the first inequality; $`7-2r>0`$. It decreases with $`r`$ in this interval, and therefore

$$
r\ge\frac{697}{254}
\quad\Longrightarrow\quad
v<\frac{11-4(697/254)}{7-2(697/254)}=\frac1{64}.
\tag{126.20}
$$

The stress, its scale, and its associated common normer have remained the same throughout. ∎

The new restriction consumes the uniform reciprocal conditioning in the actual full norming problem. It leaves the balanced nonsingular branch, singular branches compatible with (126.17)–(126.18), and the larger-tail region unresolved. The auxiliary rank-two seed is not asserted to inherit any original stress, normer or local-minimum property. No feasibility of the residual class, sufficiency for local minimality, rank-preserving transfer from arbitrary leaking optimizers, or unrestricted quarter-optimum conclusion follows.

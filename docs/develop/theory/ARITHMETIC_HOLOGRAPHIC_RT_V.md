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

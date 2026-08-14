\sum_{k\ge1}\|Q_k\chi\|^2=1.
}
\]

#### 证明

由相对正交余分解，

\[
R_N
=
E_{N+1}\oplus R_{N+1}.
\]

故

\[
P_{R_N}\chi
=
Q_{N+1}\chi
+
P_{R_{N+1}}\chi
\]

是正交和。Pythagoras 给出第一式。迭代至 \(M>N\)：

\[
d_N^2
=
\sum_{k=N+1}^{M}\|Q_k\chi\|^2
+
d_M^2.
\]

令 \(M\to\infty\)。递减闭子空间投影满足

\[
P_{R_M}\chi\to P_{R_\infty}\chi,
\]

故得到第二式。取初始零空间 \(S_0=\{0\}\)，有 \(d_0^2=\|\chi\|^2=1\)，得到总能量式。最后应用定理 29.4。 \(\square\)

这给出 RH 的概率式读法。对单位目标态 \(\chi\)，壳层权重

\[
p_k=\|Q_k\chi\|^2,
\qquad
p_\infty=\|Q_\infty\chi\|^2
\]

组成概率分布，而

\[
\boxed{
\mathrm{RH}
\iff
p_\infty=0.
}
\]

它不是“所有未知方向消失”，而是：

\[
\boxed{
\text{目标 }\chi\text{ 的全部 Hilbert 质量最终进入有限算术壳层。}
}
\]

---

## 29.6 Gram–Schur 证书：每一轮到底吸收了多少目标质量

令

\[
V_N:\mathbb C^N\to\mathscr H_{\mathrm{NB}},
\qquad
V_Nc=\sum_{a=1}^{N}c_af_a.
\]

定义 Gram 矩阵与目标相关向量

\[
\boxed{
G_N
=
V_N^*V_N
=
\bigl(\langle f_a,f_b\rangle\bigr)_{a,b\le N},
}
\]

\[
\boxed{
b_N
=
V_N^*\chi
=
\bigl(\langle f_a,\chi\rangle\bigr)_{a\le N}.
}
\]

记 \(G_N^\dagger\) 为 Moore–Penrose 逆。

### 定理 29.6（有限阶段最优距离公式）

有

\[
\boxed{
P_{S_N}
=
V_NG_N^\dagger V_N^*,
}
\]

以及

\[
\boxed{
d_N^2
=
1-b_N^*G_N^\dagger b_N.
}
\]

若 \(G_N\) 可逆，则

\[
\boxed{
d_N^2
=
1-b_N^*G_N^{-1}b_N.
}
\]

#### 证明

有限维闭像 \(\operatorname{range}(V_N)=S_N\) 上的正交投影为

\[
V_N(V_N^*V_N)^\dagger V_N^*.
\]

因此

\[
\|P_{S_N}\chi\|^2
=
\langle
V_NG_N^\dagger V_N^*\chi,
\chi
\rangle
=
b_N^*G_N^\dagger b_N.
\]

再由

\[
d_N^2
=
\|\chi\|^2-\|P_{S_N}\chi\|^2
\]

及 \(\|\chi\|^2=1\) 得证。 \(\square\)

目标向量相关项还有显式公式。

### 命题 29.7（目标相关向量的闭式）

对每个整数 \(a\ge1\)，

\[
\boxed{
\langle\chi,f_a\rangle
=
\frac{\log a+1-\gamma_{\mathrm E}}{a},
}
\]

其中 \(\gamma_{\mathrm E}\) 为 Euler 常数。

#### 证明

有

\[
\langle\chi,f_a\rangle
=
\int_0^1
\varrho\left(\frac1{ax}\right)\,dx.
\]

令 \(t=1/(ax)\)，得

\[
\langle\chi,f_a\rangle
=
\frac1a
\int_{1/a}^{\infty}
\frac{\varrho(t)}{t^2}\,dt.
\]

在区间 \([1/a,1]\) 上 \(\varrho(t)=t\)，故该部分为 \(\log a\)。另一方面，

\[
\int_1^\infty\frac{\varrho(t)}{t^2}\,dt
=
\sum_{n\ge1}
\int_n^{n+1}
\frac{t-n}{t^2}\,dt
=
1-\gamma_{\mathrm E}.
\]

合并即得。 \(\square\)

现在定义新生成元相对于既有空间的创新分量：

\[
r_{N+1}
=
(I-P_{S_N})f_{N+1}.
\]

若 \(r_{N+1}\ne0\)，则

\[
E_{N+1}
=
\operatorname{span}(r_{N+1}).
\]

### 定理 29.8（单步 Schur 增益）

若 \(r_{N+1}\ne0\)，则

\[
\boxed{
d_N^2-d_{N+1}^2
=
\frac{
|\langle\chi,r_{N+1}\rangle|^2
}{
\|r_{N+1}\|^2
}.
}
\]

若 \(r_{N+1}=0\)，则 \(d_{N+1}=d_N\)。

#### 证明

当 \(r_{N+1}\ne0\) 时，

\[
e_{N+1}
=
\frac{r_{N+1}}{\|r_{N+1}\|}
\]

是 \(E_{N+1}\) 的单位基，所以

\[
\|Q_{N+1}\chi\|^2
=
|\langle\chi,e_{N+1}\rangle|^2
=
\frac{
|\langle\chi,r_{N+1}\rangle|^2
}{
\|r_{N+1}\|^2
}.
\]

应用定理 29.5。 \(\square\)

因此每个整数 \(N+1\) 对 RH 逼近所提供的真实新信息，不由原函数 \(f_{N+1}\) 的范数决定，而由它在此前全部生成元之外的正交创新

\[
r_{N+1}
\]

以及该创新与目标 \(\chi\) 的耦合决定。

若 \(G_N\) 可逆，还可写成 Gram 行列式证书：

\[
\boxed{
d_N^2
=
\frac{
\det
\begin{pmatrix}
G_N & b_N\\
b_N^* & 1
\end{pmatrix}
}{
\det G_N
}.
}
\]

这把 RH 转化为一列有限维 Gram–Schur 余量的极限消失，但极限消失本身仍需要独立的全局估计。

---

## 29.7 Mellin–Plancherel 图像：余质量就是 \(1-\zeta A_N\) 的加权误差

对适当的 \(f\in L^2(0,\infty)\)，取 Mellin 变换

\[
\mathcal Mf(s)
=
\int_0^\infty f(x)x^{s-1}\,dx.
\]

在临界线

\[
s=\frac12+it
\]

上，Mellin–Plancherel 把 \(L^2(0,\infty)\) 等距映到 \(L^2(\mathbb R,dt/2\pi)\)。

目标向量满足

\[
\boxed{
\mathcal M\chi(s)=\frac1s.
}
\]

而对 \(0<\Re s<1\)，

\[
\int_0^\infty
\varrho(t)t^{-s-1}\,dt
=
-\frac{\zeta(s)}s.
\]

由缩放得到

\[
\boxed{
\mathcal Mf_a(s)
=
-\frac{\zeta(s)}{s\,a^s}.
}
\]

令

\[
A_N(s)
=
\sum_{a=1}^{N}c_aa^{-s}.
\]

则某个有限线性组合的 Mellin 像为

\[
-\frac{\zeta(s)}sA_N(s).
\]

改变系数整体符号后，最优距离可写成

\[
\boxed{
d_N^2
=
\inf_{A_N}
\frac1{2\pi}
\int_{-\infty}^{\infty}

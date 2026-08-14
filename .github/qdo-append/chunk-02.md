
\[
\boxed{
L_n(\rho)
=
4-4\cos(n\theta_\rho)
=
8\sin^2\frac{n\theta_\rho}{2}
\ge0.
}
\]

离线时 \(\beta_\rho\ne0\)，径向因子变为

\[
\cosh(n\beta_\rho),
\]

其大小随 \(n|\beta_\rho|\) 增长。

当 \(|\gamma|\) 很大时，

\[
\beta_\rho
=
\frac12
\log
\left(
1+\frac{1-2\sigma}{\sigma^2+\gamma^2}
\right),
\]

所以在小偏移区间有尺度关系

\[
\boxed{
|\beta_\rho|
\asymp
\frac{|1-2\sigma|}{2\gamma^2}.
}
\]

因此让 \(n|\beta_\rho|\) 达到常数量级所需的 Li 指标大致为

\[
\boxed{
n
\asymp
\frac{2\gamma^2}{|1-2\sigma|}.
}
\]

这不是“第 \(n\) 个 Li 系数必在该位置变负”的断言，因为相位 \(\theta_\rho\)、其他零点轨道与正则化尾项仍会共同作用；它给出的是一个严格的**径向放大尺度**：

\[
\boxed{
\text{零点越高、离线越浅，所需的 Li 频率通常越大。}
}
\]

所以完整证明不能只做以下任一种单参数极限：

\[
T\to\infty
\quad
\text{而固定 }n,
\]

或

\[
n\to\infty
\quad
\text{而固定零点截断 }T.
\]

真正需要控制的是对称正则化后的联合余项

\[
\mathcal R_{n,T}
=
\sum_{|\Im\rho|>T}^{\mathrm{sym}}
\left[
1-
\left(1-\frac1\rho\right)^n
\right],
\]

并在 \(n\) 可随 \(T\) 增长的区域内给出统一估计。至少需要覆盖能够分辨

\[
|\beta_\rho|
\sim T^{-2}
\]

的尺度，因此不能把 \(n\) 与 \(T\) 完全解耦。

这精确说明了本文摘要中“从局部离线轨道暴露到全局 Li 系数负性仍缺 \((n,T)\) 联合截断估计”的含义。仓库 `LiCausalTrichotomy` 已形式化 Li 测试核的整数指标、因果实现与 Cayley monodromy 三分，但它没有证明全部 Li 系数非负；`WeilIdentity` 已形式化显式公式，但没有附加 Weil 正性或 RH 结论。

---

## 29.4 非循环主接口：Nyman–Beurling 目标余质量

定义分数部分函数

\[
\varrho(t)=t-\lfloor t\rfloor.
\]

取

\[
\mathscr H_{\mathrm{NB}}
=
L^2(0,\infty),
\]

目标向量

\[
\boxed{
\chi=\mathbf1_{(0,1)},
\qquad
\|\chi\|_2^2=1,
}
\]

以及显式算术生成元

\[
\boxed{
f_a(x)
=
\varrho\left(\frac1{ax}\right),
\qquad
a\in\mathbb N_{\ge1}.
}
\]

定义嵌套有限维子空间

\[
S_N
=
\operatorname{span}(f_1,\ldots,f_N),
\]

\[
R_N=S_N^\perp,
\]

\[
S_\infty
=
\overline{\bigcup_{N\ge1}S_N},
\]

\[
R_\infty
=
S_\infty^\perp
=
\bigcap_{N\ge1}R_N.
\]

Báez-Duarte 的强 Nyman–Beurling 判据给出

\[
\boxed{
\mathrm{RH}
\iff
\chi\in S_\infty.
}
\]

第 28 节的商—正交余同构立即把它变成一个精确的商余命题。

### 定理 29.4（Nyman–Beurling 目标余类判据）

下列命题等价：

\[
\boxed{
\mathrm{RH};
}
\]

\[
\boxed{
\chi\in S_\infty;
}
\]

\[
\boxed{
[\chi]=0
\quad
\text{于 }
\mathscr H_{\mathrm{NB}}/S_\infty;
}
\]

\[
\boxed{
P_{R_\infty}\chi=0;
}
\]

\[
\boxed{
\operatorname{dist}(\chi,S_N)\longrightarrow0.
}
\]

#### 证明

第一与第二项是强 Nyman–Beurling–Báez-Duarte 判据。第二与第三项由商空间零类定义等价。由第 28 节的规范等距同构

\[
\mathscr H_{\mathrm{NB}}/S_\infty
\cong
R_\infty,
\]

商类 \([\chi]\) 对应唯一正交余代表

\[
P_{R_\infty}\chi.
\]

故第三与第四项等价。最后，对递增闭子空间 \(S_N\)，投影 \(P_{S_N}\) 强收敛到 \(P_{S_\infty}\)，所以

\[
\operatorname{dist}(\chi,S_N)
=
\|(I-P_{S_N})\chi\|
\longrightarrow
\|(I-P_{S_\infty})\chi\|
=
\|P_{R_\infty}\chi\|.
\]

故第四与第五项等价。 \(\square\)

这里必须强调：

\[
\boxed{
\mathrm{RH}
\text{ 不要求 }
R_\infty=\{0\}.
}
\]

它只要求指定目标 \(\chi\) 没有最终余分量：

\[
\boxed{
P_{R_\infty}\chi=0.
}
\]

因此不能把 RH 错写成“全部 Nyman–Beurling 生成元在整个 \(L^2\) 中稠密”。正确命题是目标特定的：

\[
\boxed{
\chi
\text{ 属于生成闭包}.
}
\]

这一区分是商余塔用于 RH 时最重要的类型边界。

---

## 29.5 正交壳层能量：RH 是目标质量被有限算术层完全吸收

令

\[
E_1=S_1,
\]

\[
E_{N+1}
=
S_{N+1}\cap S_N^\perp
\qquad(N\ge1),
\]

并令

\[
Q_N=P_{E_N},
\qquad
Q_\infty=P_{R_\infty}.
\]

则

\[
S_\infty
=
\bigoplus_{N\ge1}^{\ell^2}E_N,
\]

以及

\[
\mathscr H_{\mathrm{NB}}
=
\left(
\bigoplus_{N\ge1}^{\ell^2}E_N
\right)
\oplus
R_\infty.
\]

定义有限阶段剩余误差

\[
\boxed{
d_N
=
\operatorname{dist}(\chi,S_N)
=
\|P_{R_N}\chi\|.
}
\]

### 定理 29.5（壳层递推与最终余质量）

对全部 \(N\ge1\)，

\[
\boxed{
d_N^2
=
d_{N+1}^2
+
\|Q_{N+1}\chi\|^2.
}
\]

并且

\[
\boxed{
d_N^2
=
\sum_{k>N}\|Q_k\chi\|^2
+
\|Q_\infty\chi\|^2.
}
\]

特别地，

\[
\boxed{
1
=
\sum_{k\ge1}\|Q_k\chi\|^2
+
\|Q_\infty\chi\|^2.
}
\]

因此

\[
\boxed{
\mathrm{RH}
\iff
\|Q_\infty\chi\|^2=0
\iff

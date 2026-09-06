# 量子观察者的动态响应、记忆与涨落重建

## ——《钟速—结构反作用理论》第十一至第二十节增订

### 摘要

前文建立了静态关系

$$
\chi(0)=g^2K^{-1},
$$

并证明钟速响应能够在一定标定条件下确定结构恢复矩阵 \(K\)。但静态响应尚不能确定结构惯性、传播时间、隐藏记忆与量子涨落。

本增订将这些对象统一到同一个动态响应函数：

$$
\boxed{
\chi(z)
=
g^2C(K-z^2M)^{-1}C^{\mathsf T}.
}
$$

在有限谐振结构、共轭输入输出接口以及明确的热平衡条件下，证明以下结果：

**动态响应确定最小可观测结构；隐藏接口产生频率相关的记忆项和正的有效惯性修正；响应与平衡涨落共享同一正谱测度；指定量子钟的相干衰减可由该谱测度计算；局域传播结构能够由短时间响应的消失阶数识别。**

最后给出一个双场实例，证明消去隐藏量子模式可以同时改变有效能隙与低频传播速度，从而把“观察接口的完成”进一步连接到“有效时空的重建”。

以下继续沿用前文的假设边界。涨落—耗散关系、Schur 消去和 Krylov 可观测性均有既有理论基础；本增订给出它们在当前观察者模型中的明确组合与证明，不将其一般形式宣称为新发现。

项目依据固定于此次读取的提交 `611c3bf36cfc0fd83727c6b5657d78ec8e0917eb`。其中，Schur 消去结合律已有具体 Lean 证明；观察者完成理论已给出不可观测核、Krylov 空间和记忆余量的定义。下文新增的物理解释及综合命题尚未进行 Lean 编译。

---

# 11．从静态响应提升到动态实验

## 11.1　背景、接口与驱动

固定前文的一个联合能量分支 \(\boldsymbol e_0\)，并平移结构坐标：

$$
\boldsymbol x
=
\boldsymbol\varphi+gK^{-1}\boldsymbol e_0.
$$

略去该分支上的常数能量，结构 Hamiltonian 为

$$
\boxed{
H_{\mathrm G}
=
\frac12\boldsymbol\Pi^{\mathsf T}M^{-1}\boldsymbol\Pi
+
\frac12\boldsymbol x^{\mathsf T}K\boldsymbol x,
}
\tag{11.1}
$$

其中

$$
M=M^{\mathsf T}>0,
\qquad
K=K^{\mathsf T}>0.
$$

令

$$
C:\mathbb R^N\to\mathbb R^m
$$

为已标定的观察接口，定义可读结构扰动

$$
\boxed{
\boldsymbol y=gC\boldsymbol x.
}
\tag{11.2}
$$

它可以表示若干局部钟速扰动，或这些扰动的线性组合。

选取与该读数共轭的驱动：

$$
\boxed{
H_{\mathrm{drv}}(t)
=
\boldsymbol f(t)^{\mathsf T}\boldsymbol y.
}
\tag{11.3}
$$

因此，驱动与读数使用同一个 \(C\)。这一“共轭接口”条件是后续互易性与正性的重要前提。

\(\boldsymbol f(t)\) 表示经过独立制备与标定的控制协议。它不意味着原自治 Hamiltonian 中守恒的源能量会自行变化；将驱动器纳入完整闭合系统时，仍须记录其能量与控制资源。

---

## 定义 11.1　质量归一化结构

定义

$$
\boxed{
A=M^{-1/2}KM^{-1/2},
\qquad
B=gM^{-1/2}C^{\mathsf T},
\qquad
\Omega=A^{1/2}.
}
\tag{11.4}
$$

这里 \(A>0\)，而 \(B\) 同时确定驱动进入和读数退出结构系统的方式。

---

## 定理 11.1　精确延迟响应

比较相同初态下有无驱动的两种演化，则读数均值之差满足

$$
\boxed{
\delta\langle\boldsymbol y(t)\rangle
=
-\int_0^t
\mathcal R(t-s)\boldsymbol f(s)\,ds,
}
\tag{11.5}
$$

其中

$$
\boxed{
\mathcal R(t)
=
\Theta(t)\,
B^{\mathsf T}\Omega^{-1}\sin(\Omega t)B.
}
\tag{11.6}
$$

采用变换约定

$$
\chi(z)
=
\int_0^\infty e^{izt}\mathcal R(t)\,dt,
\qquad
\operatorname{Im}z>0,
$$

则

$$
\boxed{
\chi(z)
=
B^{\mathsf T}(A-z^2I)^{-1}B
=
g^2C(K-z^2M)^{-1}C^{\mathsf T}.
}
\tag{11.7}
$$

### 证明

结构方程为

$$
M\ddot{\boldsymbol x}
+
K\boldsymbol x
=
-gC^{\mathsf T}\boldsymbol f.
$$

令

$$
\boldsymbol q=M^{1/2}\boldsymbol x,
$$

则

$$
\ddot{\boldsymbol q}+A\boldsymbol q=-B\boldsymbol f.
$$

有无驱动的差值具有零初值，故由常系数方程的 Duhamel 公式，

$$
\delta\boldsymbol q(t)
=
-\int_0^t
\Omega^{-1}\sin\bigl(\Omega(t-s)\bigr)
B\boldsymbol f(s)\,ds.
$$

再乘以 \(B^{\mathsf T}\)，得到式（11.5）。

对每个正频率 \(\nu\)，有

$$
\int_0^\infty
e^{izt}\frac{\sin\nu t}{\nu}\,dt
=
\frac1{\nu^2-z^2},
\qquad
\operatorname{Im}z>0.
$$

对 \(A\) 作谱分解即得式（11.7）。∎

### 注 11.1

式（11.5）是线性谐振模型中的精确结果，不需要先作弱耦合或马尔科夫近似。

零频值理解为静态解，或上半平面解析函数在零点的边界值：

$$
\chi(0)=g^2CK^{-1}C^{\mathsf T}.
$$

有限无阻尼系统的时间积分不应未经说明地当作绝对收敛积分。线性谐振模型的精确响应及其与开放系统近似的区别，亦是量子 Langevin 理论中的标准问题。([APS Journals][1])

---

# 12．正谱测度与可实现性约束

## 定理 12.1　响应的正谱表示

设 \(A\) 的不同本征值为

$$
\nu_a^2>0,
$$

相应正交谱投影为 \(P_a\)。定义

$$
W_a=B^{\mathsf T}P_aB.
$$

则

$$
W_a\ge0,
$$

且

$$
\boxed{
\chi(z)
=
\sum_a\frac{W_a}{\nu_a^2-z^2}.
}
\tag{12.1}
$$

### 证明

由

$$
A=\sum_a\nu_a^2P_a
$$

得到

$$
(A-z^2I)^{-1}
=
\sum_a\frac{P_a}{\nu_a^2-z^2}.
$$

对任意 \(v\in\mathbb R^m\)，

$$
v^{\mathsf T}W_av
=
\|P_aBv\|^2\ge0.
$$

代入式（11.7）即得。∎

---

## 定理 12.2　虚频响应的完全单调性

定义

$$
F(s)=\chi(i\sqrt s),
\qquad s\ge0.
$$

则对全部 \(k\ge0\)，

$$
\boxed{
(-1)^kF^{(k)}(s)
=
k!\,B^{\mathsf T}(A+sI)^{-k-1}B
\ge0.
}
\tag{12.2}
$$

### 证明

由

$$
F(s)=B^{\mathsf T}(A+sI)^{-1}B
$$

逐次求导即可。由于 \(A+sI>0\)，其任意负整数次幂正定，夹乘 \(B\) 后得到半正定矩阵。∎

### 推论 12.1　任意响应数据不一定具有当前模型实现

若候选响应在 \(s\ge0\) 上违反式（12.2）的任一矩阵不等式，则它不可能来自本节所定义的正定谐振结构与共轭接口。

这给项目中的 ADMIT 提供了实质内容：**正性不是一个附加标签，而是对整个频率函数的一组可检验限制。**

虚频并不要求观察者实施“虚时间实验”。在有限有理模型中，它可以由实时间响应所确定的解析函数计算；有限噪声数据能否稳定完成这种识别，则是另一项估计问题。

---

## 推论 12.2　完整接口可以同时重建恢复结构与惯性结构

若 \(C=I\)，且 \(g\) 已标定，则

$$
\boxed{
\chi(z)^{-1}
=
\frac1{g^2}(K-z^2M).
}
\tag{12.3}
$$

因此

$$
\boxed{
K=g^2\chi(0)^{-1},
\qquad
M=-g^2\frac{\partial\chi^{-1}}{\partial(z^2)}.
}
\tag{12.4}
$$

### 证明

对式（11.7）求逆并比较 \(z^2\) 的系数。∎

**静态钟速只能识别 \(K/g^2\)；动态实验进一步识别 \(M/g^2\)。**当只保留部分接口时，逆响应一般不再是 \(z^2\) 的一次函数，其非线性部分携带隐藏记忆。

---

# 13．由响应重建最小可观测结构

本节将动态响应与仓库的观察者完成、不可观测核和 Krylov 空间连接起来。仓库已有理论证明

$$
N_\infty
=
\bigcap_{k\ge0}\ker(CT^k)
=
O_\infty^\perp,
$$

并把当前不可见但未来可见的部分定义为记忆余量。

## 定义 13.1　响应矩与块 Hankel 矩阵

定义

$$
T_k=B^{\mathsf T}A^kB,
\qquad k\ge0.
$$

在充分大的 \(|z|\) 上，

$$
\boxed{
\chi(z)
=
-\sum_{k=0}^\infty\frac{T_k}{z^{2k+2}}.
}
\tag{13.1}
$$

对 \(r\ge0\)，定义

$$
\mathbb H_r=[T_{i+j}]_{i,j=0}^r,
$$

以及

$$
\mathcal K_r
=
\operatorname{span}
\{A^kBv:0\le k\le r,\ v\in\mathbb R^m\}.
$$

---

## 定理 13.1　响应矩的正性与可观测维数

有

$$
\boxed{
\mathbb H_r\ge0,
\qquad
\operatorname{rank}\mathbb H_r
=
\dim\mathcal K_r.
}
\tag{13.2}
$$

若

$$
\mathcal K_r=\mathcal K_{r+1},
$$

则对全部 \(s\ge0\)，

$$
\mathcal K_{r+s}=\mathcal K_r.
$$

### 证明

令

$$
V_r=
\begin{pmatrix}
B&AB&\cdots&A^rB
\end{pmatrix}.
$$

由于 \(A=A^{\mathsf T}\)，

$$
\mathbb H_r=V_r^{\mathsf T}V_r.
$$

所以它半正定，且其秩等于 \(V_r\) 的列空间维数。

若 \(\mathcal K_r=\mathcal K_{r+1}\)，则

$$
A\mathcal K_r\subseteq\mathcal K_r.
$$

之后的所有幂都仍落在该空间内。∎

### 推论 13.1

固定有限模型中，响应完成最终稳定。其最终秩给出**可被这些驱动与读数访问的最少结构模式数**，而不是自动给出全部微观模式数。

---

## 定理 13.2　最小对称实现的唯一性

设两组有限模型 \((A,B)\)、\((\widetilde A,\widetilde B)\) 满足

$$
B^{\mathsf T}A^kB
=
\widetilde B^{\mathsf T}\widetilde A^k\widetilde B
\qquad
\forall k\ge0.
$$

并假设两者均为最小实现：

$$
\operatorname{span}_{k\ge0}\operatorname{Ran}(A^kB)
=
\mathbb R^n,
$$

另一组同理。

则存在正交同构 \(Q\)，使

$$
\boxed{
QA=\widetilde A Q,
\qquad
QB=\widetilde B.
}
\tag{13.3}
$$

### 证明

在有限线性组合上定义

$$
Q\left(\sum_kA^kBv_k\right)
=
\sum_k\widetilde A^k\widetilde Bv_k.
$$

任意两种此类线性组合的内积，均由矩

$$
B^{\mathsf T}A^{k+\ell}B
$$

决定。两组矩相同，因此此映射良定义且保持内积。

最小性保证其定义域与像分别为两组完整实现空间，故 \(Q\) 为正交同构。

将每个生成元的幂增加一，得到 \(QA=\widetilde A Q\)；取零次幂得到 \(QB=\widetilde B\)。∎

### 注 13.1

本定理只在**共轭接口、实对称正定结构的最小实现类**中成立。

正交同构不必保持某个事先选定坐标中的稀疏性或局域图解释。因此，完整响应可以确定最小动力学实现，却不保证唯一确定全部隐藏拓扑。

此外，有限精度下的秩判定可能病态；“精确识别”和“稳定识别”仍应分开。

---

# 14．隐藏结构产生精确记忆，而不是自动产生新的局域常数

## 假设 14.1　可见—隐藏分割

将坐标分为 \(V,H\) 两部分，并要求惯性矩阵在该分割下为块对角：

$$
M=
\begin{pmatrix}
M_V&0\\
0&M_H
\end{pmatrix}.
$$

恢复矩阵为

$$
K=
\begin{pmatrix}
K_{VV}&K_{VH}\\
K_{HV}&K_{HH}
\end{pmatrix}.
$$

只从可见部分驱动，记

$$
D(z)=K-z^2M.
$$

---

## 定理 14.1　动态 Schur 消去

在相应逆算子存在的频率上，可见逆响应由

$$
\boxed{
D_{\mathrm{eff}}(z)
=
K_{VV}-z^2M_V
-
K_{VH}(K_{HH}-z^2M_H)^{-1}K_{HV}
}
\tag{14.1}
$$

给出：

$$
\boxed{
\chi_V(z)=g^2D_{\mathrm{eff}}(z)^{-1}.
}
\tag{14.2}
$$

### 证明

频域方程为

$$
\begin{aligned}
(K_{VV}-z^2M_V)x_V+K_{VH}x_H&=-gf,\\
K_{HV}x_V+(K_{HH}-z^2M_H)x_H&=0.
\end{aligned}
$$

由第二式，

$$
x_H=-(K_{HH}-z^2M_H)^{-1}K_{HV}x_V.
$$

代入第一式即得。∎

### 推论 14.1　精确分层消去的顺序相容性

在所有必要逆算子存在时，对多个隐藏块逐层消去，与一次性消去其直和，得到相同的保留算子。

### 证明

在每个固定 \(z\) 上，将 \(D(z)\) 的块代入 Schur 消去结合律即可。仓库 `SchurComplementAssociativity.lean` 已对相应有界算子及逆算子见证给出这一代数恒等式的证明。 ∎

**该结论只保证精确消去的相容性。若每一步提前作静态化、截断或删除初态项，最终近似可能不再相同。**

---

## 定理 14.2　隐藏结构的时域记忆方程

定义隐藏延迟 Green 核

$$
G_H(t)
=
\Theta(t)\,
M_H^{-1/2}\Omega_H^{-1}
\sin(\Omega_Ht)M_H^{-1/2},
$$

其中

$$
\Omega_H^2=M_H^{-1/2}K_{HH}M_H^{-1/2}.
$$

则可见坐标满足

$$
\boxed{
M_V\ddot x_V(t)+K_{VV}x_V(t)
-
\int_0^t\Sigma(t-s)x_V(s)\,ds
=
-gf(t)+\eta(t),
}
\tag{14.3}
$$

其中

$$
\boxed{
\Sigma(t)=K_{VH}G_H(t)K_{HV},
\qquad
\eta(t)=-K_{VH}x_H^{\mathrm{hom}}(t).
}
\tag{14.4}
$$

\(x_H^{\mathrm{hom}}\) 是由隐藏初始坐标与动量决定的齐次解。

### 证明

隐藏方程的精确解为

$$
x_H(t)
=
x_H^{\mathrm{hom}}(t)
-
\int_0^tG_H(t-s)K_{HV}x_V(s)\,ds.
$$

代回可见方程即得。∎

### 注 14.1

\(\eta(t)\) 不是新加入的任意随机数，而是隐藏初值的演化。若初始联合态相关，它还可能与可见初值相关。

隐藏自由度消去后出现记忆核与初值项，是投影动力学和广义 Langevin 理论的基本结构；不能在保留记忆核的同时任意指定独立白噪声。([AIP Publishing][2])

---

## 定理 14.3　可见瞬时状态自治的判据

在上述块对角惯性模型中，要求对全部合法初态，可见相空间均值

$$
q(\rho)=
\bigl(
\langle x_V\rangle_\rho,
\langle\Pi_V\rangle_\rho
\bigr)
$$

独自决定其未来，则必须且只须

$$
\boxed{
K_{VH}=0.
}
\tag{14.5}
$$

### 证明

若 \(K_{VH}=0\)，可见与隐藏方程解耦，结论成立。

若 \(K_{VH}\ne0\)，选取两个具有相同可见态、相同隐藏动量，但隐藏坐标均值相差 \(h\) 的相干态，并使

$$
K_{VH}h\ne0.
$$

其当前可见均值相同，但

$$
\delta\frac{d\langle\Pi_V\rangle}{dt}
=
-K_{VH}h\ne0.
$$

故未来不同，不能仅由当前可见接口决定。∎

这给出仓库 `exact_descent_has_no_carry` 的一个物理反向见证：隐藏位置差异进入可见动量变化，构成明确的 carry，而不是抽象地声称“有记忆”。

---

# 15．隐藏模式的低频效应：恢复作用减小，结构惯性增大

## 定义 15.1　隐藏频率尺度

令

$$
Q=K_{HH}^{-1/2}M_HK_{HH}^{-1/2},
$$

$$
Z=K_{HH}^{-1/2}K_{HV},
$$

并定义

$$
\omega_H=\|Q\|^{-1/2}.
$$

\(\omega_H\) 是孤立隐藏块的最小正常模频率。

---

## 定理 15.1　动态消去的低频展开及余项界

对实数 \(|\omega|<\omega_H\)，有

$$
\boxed{
D_{\mathrm{eff}}(\omega)
=
K_{\mathrm{eff}}
-
\omega^2M_{\mathrm{eff}}
-
R_4(\omega),
}
\tag{15.1}
$$

其中

$$
K_{\mathrm{eff}}
=
K_{VV}-Z^{\mathsf T}Z,
\tag{15.2}
$$

$$
\boxed{
M_{\mathrm{eff}}
=
M_V+Z^{\mathsf T}QZ
=
M_V+
K_{VH}K_{HH}^{-1}
M_HK_{HH}^{-1}K_{HV},
}
\tag{15.3}
$$

且

$$
R_4(\omega)
=
\omega^4
Z^{\mathsf T}Q^2(I-\omega^2Q)^{-1}Z
\ge0.
\tag{15.4}
$$

其范数满足

$$
\boxed{
\|R_4(\omega)\|
\le
\frac{
\omega^4\|Z\|^2\|Q\|^2
}{
1-\omega^2\|Q\|
}.
}
\tag{15.5}
$$

### 证明

首先，

$$
K_{VH}(K_{HH}-\omega^2M_H)^{-1}K_{HV}
=
Z^{\mathsf T}(I-\omega^2Q)^{-1}Z.
$$

由精确恒等式

$$
(I-\omega^2Q)^{-1}
=
I+\omega^2Q+
\omega^4Q^2(I-\omega^2Q)^{-1},
$$

代入式（14.1）即得式（15.1）—（15.4）。

因为 \(\omega^2\|Q\|<1\)，

$$
\|(I-\omega^2Q)^{-1}\|
\le
\frac1{1-\omega^2\|Q\|},
$$

从而得到式（15.5）。∎

### 推论 15.1

隐藏模式的低频消去具有确定的符号：

$$
K_{\mathrm{eff}}\le K_{VV},
$$

$$
\boxed{
M_{\mathrm{eff}}\ge M_V.
}
\tag{15.6}
$$

这里增加的是**有效结构惯性矩阵**，不能直接等同于粒子的引力质量或据此宣布等效原理成立。

---

## 推论 15.2　接近可见共振时，低频展开仍可能失效

令

$$
D_0(\omega)=K_{\mathrm{eff}}-\omega^2M_{\mathrm{eff}}.
$$

若 \(D_0\) 可逆，且

$$
\|D_0^{-1}\|\|R_4\|<1,
$$

则

$$
\boxed{
\|D_{\mathrm{eff}}^{-1}-D_0^{-1}\|
\le
\frac{
\|D_0^{-1}\|^2\|R_4\|
}{
1-\|D_0^{-1}\|\|R_4\|
}.
}
\tag{15.7}
$$

### 证明

使用

$$
D_{\mathrm{eff}}=D_0-R_4
$$

的 Neumann 级数及预解式恒等式。∎

因此，只有隐藏频率较高还不够；若可见响应接近共振，微小算子余项也可能造成显著读数差异。

---

## 例 15.1　三接口模型的动态区别

沿用前文

$$
K=
\begin{pmatrix}
2&-1&0\\
-1&3&-1\\
0&-1&2
\end{pmatrix},
\qquad
M=I.
$$

只观察两端，令

$$
J=
\begin{pmatrix}
1&1\\
1&1
\end{pmatrix}.
$$

则

$$
\boxed{
D_{\mathrm{eff}}(z)
=
(2-z^2)I-\frac{J}{3-z^2}.
}
\tag{15.8}
$$

因此

$$
K_{\mathrm{eff}}=2I-\frac13J,
$$

$$
M_{\mathrm{eff}}=I+\frac19J,
$$

以及

$$
R_4(z)=\frac{z^4}{9(3-z^2)}J.
$$

一个只有两端、但直接采用 \(K_{\mathrm{eff}}\) 的模型，可以复制静态响应；若不加入正确的惯性和记忆，它不能复制完整动态响应。

上述矩阵恒等式已作精确符号核验。

---

# 16．由短时间传播识别局域邻接

本节进一步要求

$$
M=\operatorname{diag}(m_1,\ldots,m_N),
\qquad
m_i>0,
$$

并取 \(C=I\)。

假设 \(K_{ij}<0\) 恰好对应图的边，其他非对角元为零。

## 定理 16.1　最短路径与响应首个非零阶

设 \(i\ne j\) 的图距离为 \(d(i,j)=d<\infty\)。则

$$
\boxed{
\mathcal R_{ij}(t)
=
\frac{
g^2(-1)^d(A^d)_{ij}
}{
\sqrt{m_im_j}(2d+1)!
}
t^{2d+1}
+
O(t^{2d+3}),
}
\tag{16.1}
$$

且首项系数严格为正。

### 证明

由正弦级数，

$$
\mathcal R(t)
=
g^2M^{-1/2}
\sum_{k=0}^\infty
\frac{(-1)^kA^kt^{2k+1}}{(2k+1)!}
M^{-1/2}.
$$

若 \(k<d\)，不可能用 \(k\) 次矩阵乘积沿边从 \(j\) 到达 \(i\)，故

$$
(A^k)_{ij}=0.
$$

当 \(k=d\) 时，所有非零贡献来自长度为 \(d\) 的最短路径；每条路径含 \(d\) 个负的非对角因子，所以

$$
(-1)^d(A^d)_{ij}>0.
$$

取首个非零项即得。∎

### 例 16.1

对前述三节点链，取 \(g=1\)，则

$$
\mathcal R_{13}(t)
=
\frac{\sin t}{3}
-
\frac{\sin(\sqrt2t)}{2\sqrt2}
+
\frac{\sin2t}{12}
=
\frac{t^5}{120}+O(t^7).
$$

若采用静态等价的两节点模型，并取其惯性为 \(I\)，则两端响应从

$$
\frac{t^3}{18}
$$

开始。

因此，精确时间分辨实验能够区分“直接连接”和“通过一个隐藏节点连接”。

### 注 16.1

这一结论恢复的是**指定局域坐标与符号条件下的图距离**，不是未经标定的米制距离。

连续时间有限谐振网络在任意小的正时间上，可以具有高阶但非零的远端响应。式（16.1）不是严格光锥定理。有限精度下，高阶导数识别也可能非常不稳定，不能把形式可识别性当成实验上免费可得的信息。

---

# 17．响应与量子涨落共享同一谱结构

## 假设 17.1　明确的平衡态

在固定源分支平移后，结构系统制备为

$$
\rho_\beta
=
\frac{e^{-\beta H_{\mathrm G}}}
{\operatorname{Tr}e^{-\beta H_{\mathrm G}}},
\qquad
\beta>0.
$$

零温情形取 \(\beta\to\infty\)。

本节不适用于任意非平衡态、任意压缩态，或未经条件化的源能量叠加。

定义对称关联矩阵

$$
C_\beta(t)_{ij}
=
\frac12
\operatorname{Tr}
\left[
\rho_\beta\{y_i(t),y_j(0)\}
\right].
$$

其双边谱为

$$
S_\beta(\omega)
=
\int_{-\infty}^{\infty}
e^{i\omega t}C_\beta(t)\,dt.
$$

---

## 定理 17.1　有限谐振结构的涨落—响应关系

有

$$
\boxed{
C_\beta(t)
=
\sum_a
\frac{\hbar}{2\nu_a}
\coth\!\left(\frac{\beta\hbar\nu_a}{2}\right)
W_a\cos(\nu_at).
}
\tag{17.1}
$$

并在分布意义下满足

$$
\boxed{
S_\beta(\omega)
=
\hbar
\coth\!\left(\frac{\beta\hbar\omega}{2}\right)
\operatorname{Im}\chi(\omega+i0).
}
\tag{17.2}
$$

### 证明

在正常模坐标中，

$$
H_{\mathrm G}
=
\sum_\alpha
\frac12(p_\alpha^2+\nu_\alpha^2q_\alpha^2).
$$

单模热平衡关联为

$$
\frac12\langle\{q_\alpha(t),q_\alpha(0)\}\rangle_\beta
=
\frac{\hbar}{2\nu_\alpha}
\coth\!\left(\frac{\beta\hbar\nu_\alpha}{2}\right)
\cos(\nu_\alpha t).
$$

各模式相互独立，再按 \(B\) 投影，得到式（17.1）。

另一方面，

$$
\operatorname{Im}\chi(\omega+i0)
=
\frac\pi2
\sum_a\frac{W_a}{\nu_a}
\left[
\delta(\omega-\nu_a)-\delta(\omega+\nu_a)
\right].
$$

对式（17.1）作 Fourier 变换，并利用 \(\coth\) 为奇函数，即得式（17.2）。∎

这是 Kubo 涨落—耗散关系在当前有限谐振、共轭接口模型中的直接实现。符号取决于驱动项及 Fourier 约定；本文已在式（11.3）—（11.7）固定这些约定。([Weizmann Institute of Science][3])

### 注 17.1

有限无阻尼模型的谱由 \(\delta\) 峰组成。“吸收谱”不意味着有限封闭系统已经具有不可逆摩擦或永久热化。引入连续谱、开放环境或粗粒化后，才可能得到平滑耗散描述。

---

## 定理 17.2　静态响应与结构惯性的谱和规则

有

$$
\boxed{
\chi(0)
=
\frac2\pi
\int_0^\infty
\frac{\operatorname{Im}\chi(\omega+i0)}{\omega}\,d\omega,
}
\tag{17.3}
$$

以及

$$
\boxed{
B^{\mathsf T}B
=
\frac2\pi
\int_0^\infty
\omega\,\operatorname{Im}\chi(\omega+i0)\,d\omega.
}
\tag{17.4}
$$

### 证明

将式（17.1）证明中的离散吸收谱代入积分。第一式得到

$$
\sum_a\frac{W_a}{\nu_a^2},
$$

第二式得到

$$
\sum_aW_a=B^{\mathsf T}B.
$$

∎

因此，静态恢复响应与短时间惯性不是两个互不相干的测量量，而是同一谱测度的不同矩。

---

## 定理 17.3　固定响应与谱隙下的涨落下界

令

$$
V_\beta=C_\beta(0),
$$

并设所有被当前接口看见的模式满足

$$
\nu_a\ge\nu_*>0.
$$

则

$$
\boxed{
V_\beta\ge\beta^{-1}\chi(0),
}
\tag{17.5}
$$

以及

$$
\boxed{
V_\beta\ge
\frac{\hbar\nu_*}{2}\chi(0).
}
\tag{17.6}
$$

### 证明

将协方差改写为

$$
V_\beta
=
\sum_a
\left[
\frac{\hbar\nu_a}{2}
\coth\!\left(\frac{\beta\hbar\nu_a}{2}\right)
\right]
\frac{W_a}{\nu_a^2}.
$$

对 \(x>0\)，有

$$
x\coth x\ge1,
\qquad
\coth x\ge1.
$$

于是方括号中的系数分别不小于 \(\beta^{-1}\) 和 \(\hbar\nu_*/2\)。每个 \(W_a\) 半正定，逐项求和即得。∎

### 推论 17.1

在当前平衡、有限谐振且固定正谱隙的模型中，某个接口方向若具有非零静态响应，就不能同时具有严格为零的该方向涨落。

这不是任意量子态都必须满足的普遍噪声下界。若允许改变模式频率、采用非平衡压缩态或改变测量协议，就必须重新分析。特别是无隙极限 \(\nu_*\to0\) 时，式（17.6）不能作为统一正下界保留。

---

# 18．由同一响应谱计算量子钟的相干变化

本节将上一节的自由结构谱接入一个实际量子钟，而不是把随机钟速作为外部给定过程。

## 定义 18.1　线性结构耦合钟

取有限维钟 Hamiltonian \(H_C\)，选定接口方向 \(v\in\mathbb R^m\)，定义

$$
Y=v^{\mathsf T}\boldsymbol y.
$$

完整 Hamiltonian 为

$$
\boxed{
H_{\mathrm{tot}}
=
H_C+H_{\mathrm G}+H_CY.
}
\tag{18.1}
$$

初态为

$$
\rho_C\otimes\rho_\beta.
$$

这是新的明确制备条件，不等于钟已处于每个条件位移基态组成的平衡子空间。

---

## 定理 18.1　量子钟的精确去相干模长

设 \(E_a,E_b\) 为两个钟能级，

$$
\Delta E=E_a-E_b.
$$

相应非对角元可写为

$$
\rho_{ab}(t)
=
\rho_{ab}(0)
e^{-i\Delta Et/\hbar}
e^{i\vartheta_{ab}(t)}
e^{-\Gamma_{ab}(t)},
$$

其中 \(\vartheta_{ab}\) 为实相位，并且

$$
\boxed{
\Gamma_{ab}(t)
=
\frac{(\Delta E)^2}{2\hbar}
\sum_a
\frac{v^{\mathsf T}W_av}{\nu_a^3}
\coth\!\left(\frac{\beta\hbar\nu_a}{2}\right)
\bigl(1-\cos\nu_at\bigr).
}
\tag{18.2}
$$

等价地，

$$
\boxed{
\Gamma_{ab}(t)
=
\frac{(\Delta E)^2}{2\hbar^2}
\int_0^t\!\!\int_0^t
v^{\mathsf T}C_\beta(s-s')v\,ds\,ds'.
}
\tag{18.3}
$$

### 证明

由于 \(H_C\) 与结构算子可交换，在每个钟能级上，结构经历一个能级相关的线性力。

对单个正常模，两个钟能级产生的条件位移之差，其模平方为

$$
|\delta\alpha(t)|^2
=
\frac{(\Delta E)^2b_\alpha^2}
{\hbar\nu_\alpha^3}
(1-\cos\nu_\alpha t),
$$

其中 \(b_\alpha\) 为 \(Bv\) 在该正常模中的分量。

热态中 Weyl 位移算子的期望模长为

$$
\exp\left[
-\frac12|\delta\alpha|^2
\coth\!\left(\frac{\beta\hbar\nu_\alpha}{2}\right)
\right].
$$

对全部模式相乘并合并同频权重，得到式（18.2）。

再用

$$
\int_0^t\!\!\int_0^t
\cos\bigl(\nu(s-s')\bigr)\,ds\,ds'
=
\frac{2(1-\cos\nu t)}{\nu^2}
$$

即可得到式（18.3）。∎

这种线性谐振环境中的纯去相干模型可精确求解，不需要把二阶近似误当成一般强耦合结论。([arXiv][4])

### 注 18.1

式（18.2）描述相干模长。相位 \(\vartheta_{ab}\) 含有能量相关的自反作用，不能无条件忽略，再将完整结果解释成同一个经典钟速。

此外，有限离散模式可以发生相干回流；当全部相关频率满足共同复现条件时，\(\Gamma_{ab}\) 可以再次为零。局部相干减小不等于全局信息被永久删除。

---

## 推论 18.1　短时钟相干与静态响应的联系

在有限模式模型中，

$$
\boxed{
\Gamma_{ab}(t)
=
\frac{(\Delta E)^2t^2}{2\hbar^2}
v^{\mathsf T}V_\beta v
+
O(t^4).
}
\tag{18.4}
$$

因此，在第 17 节条件下，其短时二次项满足相应响应下界。

### 证明

对每一项使用

$$
1-\cos\nu_at
=
\frac{\nu_a^2t^2}{2}+O(t^4),
$$

再代入 \(V_\beta\) 的表达式。∎

由此，静态钟速响应、结构涨落与量子钟相干不再是三个独立可调函数。**在本模型及其平衡制备条件下，它们由同一组 \((\nu_a,W_a)\) 联系。**

但仅凭某只钟的去相干模长，通常还不能区分量子结构与具有相同对称相关函数的经典噪声实现；鉴别量子性需要更丰富的联合协议。

---

# 19．从隐藏模式的惯性修正到有效传播几何

前述定理尚未把结构变量识别为空间或引力。本节只给出一个明确的连续传播实例，说明隐藏模式怎样改变低能有效时空。

## 假设 19.1　两个局域实场

考虑两个线性场 \(q,r\)。先在有限空间区域和适当边界条件下建立模式分解，随后研究其局部均匀 Fourier 表示。

取二次 Lagrangian 密度

$$
\begin{aligned}
\mathcal L
={}&
\frac12\dot q^2+\frac12\dot r^2
-\frac{c_0^2}{2}|\nabla q|^2
-\frac{c_h^2}{2}|\nabla r|^2\\
&-\frac{\Omega_0^2}{2}q^2
-\frac{\Omega_h^2}{2}r^2
-\lambda qr,
\end{aligned}
\tag{19.1}
$$

其中

$$
\Omega_0,\Omega_h>0,
\qquad
\Omega_0^2\Omega_h^2>\lambda^2.
$$

这保证零动量处的恢复矩阵正定；非负梯度项保持稳定性。

---

## 定理 19.1　隐藏场消去后的有效传播系数

只保留 \(q\) 时，其精确逆传播函数为

$$
\boxed{
D_{\mathrm{eff}}(\omega,k)
=
\Omega_0^2+c_0^2|k|^2-\omega^2
-
\frac{\lambda^2}
{\Omega_h^2+c_h^2|k|^2-\omega^2}.
}
\tag{19.2}
$$

在

$$
|c_h^2|k|^2-\omega^2|<\Omega_h^2
$$

的范围内，领先阶有效方程具有

$$
Z=1+\frac{\lambda^2}{\Omega_h^4},
\tag{19.3}
$$

$$
\boxed{
c_{\mathrm{eff}}^2
=
\frac{
c_0^2+\lambda^2c_h^2/\Omega_h^4
}{
1+\lambda^2/\Omega_h^4
},
}
\tag{19.4}
$$

以及

$$
\boxed{
\Omega_{\mathrm{eff}}^2
=
\frac{
\Omega_0^2-\lambda^2/\Omega_h^2
}{
1+\lambda^2/\Omega_h^4
}.
}
\tag{19.5}
$$

因此，

$$
D_{\mathrm{eff}}
=
Z\left[
-\omega^2+c_{\mathrm{eff}}^2|k|^2
+\Omega_{\mathrm{eff}}^2
\right]
+\text{受控高阶项}.
\tag{19.6}
$$

### 证明

频域方程为

$$
\begin{aligned}
(\Omega_0^2+c_0^2|k|^2-\omega^2)q+\lambda r&=0,\\
\lambda q+(\Omega_h^2+c_h^2|k|^2-\omega^2)r&=0.
\end{aligned}
$$

消去 \(r\) 得式（19.2）。

令

$$
s=c_h^2|k|^2-\omega^2.
$$

使用精确展开

$$
\frac1{\Omega_h^2+s}
=
\frac1{\Omega_h^2}
-\frac{s}{\Omega_h^4}
+
\frac{s^2}{\Omega_h^4(\Omega_h^2+s)}.
$$

比较常数项、\(\omega^2\) 项及 \(|k|^2\) 项，即得式（19.3）—（19.6）。∎

### 推论 19.1

有

$$
\min(c_0^2,c_h^2)
\le
c_{\mathrm{eff}}^2
\le
\max(c_0^2,c_h^2).
$$

特别是，当隐藏模式不独立传播，即 \(c_h=0\) 时，

$$
\boxed{
c_{\mathrm{eff}}^2
=
\frac{c_0^2}{1+\lambda^2/\Omega_h^4}
<c_0^2
}
\tag{19.7}
$$

只要 \(\lambda\ne0\)。

### 解释

观察者若只访问 \(q\)，并且实验频率足够低，就会读出一个不同于裸参数的有效传播速度。

这不是任意重新命名速度，而是隐藏模式的动态响应增加有效惯性后的结果。

但是：

**\(c_{\mathrm{eff}}\) 是领先阶有效方程的特征速度，不自动等于完整模型在全部频率上的精确信号前沿速度。**

高阶记忆项会带来频散；高频实验仍可分辨完整双场结构。把受限实验中的有效光锥当成绝对因果边界，需要另外证明一致的极限与误差控制。

---

## 命题 19.1　有效时空解释的条件

若式（19.6）的领先阶模型在指定实验窗口内有效，则其无质量主部可以写为

$$
\partial_t^2q-c_{\mathrm{eff}}^2\Delta q.
$$

该主部允许洛伦兹型特征几何解释。

然而，从这一单一传播模式不能推出：

$$
\text{所有物质共享同一 }c_{\mathrm{eff}},
$$

也不能推出：

$$
\text{该有效几何满足 Einstein 方程}.
$$

### 证明

第一项由主符号

$$
-\omega^2+c_{\mathrm{eff}}^2|k|^2
$$

直接得到。

第二项不成立，因为增加另一个探针场并选择不同的 \((c_0,c_h,\lambda,\Omega_h)\)，仍满足本节所有稳定性假设，却一般产生不同的 \(c_{\mathrm{eff}}\)。

第三项也未由假设约束：本节没有给出张量几何自由度、应力能的普适耦合或几何自反作用方程。∎

### 注 19.1

若通过有限体积模型序列研究无隙极限，必须区分：

隐藏模式的高频间隙可以保持，而可见低能间隙趋于零。

此时可以保留隐藏模式消去的低频控制，却不能把第 17 节依赖**全部可见模式统一正下界**的涨落界原样带入无隙极限。

---

# 20．动态观察者完成的统一命题

## 定理 20.1　响应—记忆—涨落的统一重建

固定以下模型类：

有限个正定谐振结构模式；共轭线性输入输出接口；明确的参考钟与驱动标定；第 17—18 节所指定的热平衡和初态条件。

则完整响应函数 \(\chi(z)\) 确定：

$$
\boxed{
\text{最小可观测结构的正交等价类},
}
$$

$$
\boxed{
\text{该接口的静态响应与动态记忆},
}
$$

$$
\boxed{
\text{给定温度下的对称涨落谱},
}
$$

以及

$$
\boxed{
\text{指定线性量子钟耦合下的相干衰减模长}.
}
$$

但它一般不唯一确定完整不可见网络、任意非平衡态、全部允许量子控制，或现实的完整时空几何。

### 证明

由响应的高频展开得到全部矩 \(T_k\)，由定理 13.2 得到最小对称实现的唯一性。

静态响应由 \(\chi(0)\) 得到；时间响应由其延迟逆变换得到。隐藏变量的精确消去与记忆表示由定理 14.1—14.2给出。

在固定温度下，由定理 17.1 得到涨落谱；再由定理 18.1 得到指定钟的去相干模长。

至于非唯一部分：可以附加与可访问子空间完全解耦的结构模式而不改变 \(\chi\)；可以在保持 \(A,B\) 不变时改变非平衡初态；正交等价也不必保持预先指定的微观局域坐标。最后，定理 19.1 只约束特定模式的传播系数，不约束全部物质及几何动力学。∎

---

## 项目层面的对应关系

本增订没有增加与仓库无关的独立语义，而是把既有对象落实为一个动态量子模型：

**CUT** 对应可访问坐标及响应接口 \(C\)。

**FLOW** 对应完整谐振演化，以及经过证明的有效传播。

**carry** 对应隐藏初值通过 \(K_{VH}\) 改变未来可见读数。

**completion** 对应由 \(A^kB\) 生成的最小可观测空间。

**Schur 消去** 对应带完整频率依赖和初态项的隐藏结构约化。

**ADMIT** 不仅检查静态正性，还检查响应的正谱表示、矩正性、可实现初态以及近似误差范围。

仓库已提供线性完成、记忆商和 Schur 结合律的相应基础；这里没有把这些基础直接等同于完整的物理实现，而是逐项补入其所需条件。

---

# 结论

前文得到的是：

$$
\text{静态钟速响应}
\longrightarrow
K^{-1}.
$$

本增订进一步得到：

$$
\boxed{
\text{完整动态响应}
\longrightarrow
\text{恢复结构、惯性结构与隐藏记忆}.
}
$$

在明确平衡条件下，又得到：

$$
\boxed{
\text{同一响应谱}
\longrightarrow
\text{量子结构涨落}
\longrightarrow
\text{观察者钟的相干变化}.
}
$$

对具有局域传播实现的模型，隐藏结构的消去还能产生：

$$
\boxed{
\text{有效惯性修正}
\longrightarrow
\text{有效传播速度}
\longrightarrow
\text{受实验窗口限制的几何描述}.
}
$$

因此，当前理论的进一步推进不在于把“信息逃逸”统一改名为引力，而在于建立了一个更严格的事实：

> **观察者所见的静态关系、动态记忆、量子噪声和有效传播，并不是可以任意拼接的四套解释；在同一个明确的量子实现中，它们受到共同谱结构的约束。**

这使“由量子观察者重建时空”获得了一条新的可核查路径：**先重建实验响应，再检验其最小物理实现；由实现推导波动与传播，最后判断这些传播是否允许共同的时空几何。**

[1]: https://link.aps.org/doi/10.1103/PhysRevA.37.4419 "https://link.aps.org/doi/10.1103/PhysRevA.37.4419"
[2]: https://pubs.aip.org/aip/jcp/article/156/24/244105/2841362/Position-dependent-memory-kernel-in-generalized "https://pubs.aip.org/aip/jcp/article/156/24/244105/2841362/Position-dependent-memory-kernel-in-generalized"
[3]: https://www.weizmann.ac.il/complex/mukamel/sites/complex.mukamel/files/uploads/ftd_kubo_review.pdf "https://www.weizmann.ac.il/complex/mukamel/sites/complex.mukamel/files/uploads/ftd_kubo_review.pdf"
[4]: https://arxiv.org/abs/quant-ph/9702001 "https://arxiv.org/abs/quant-ph/9702001"
# 共同光锥的谱判据与量子观察者的几何一致性

## ——《动态响应、记忆与涨落重建》第二十一至第三十节增订

### 摘要

前文证明，观察者的动态响应可以确定最小可观测结构，并通过隐藏模式的消去产生记忆、有效惯性和传播速度修正。本增订进一步研究：

> **不同观察者、不同探针和不同频率的实验，何时能够被同一个物理时空描述？**

本文在明确的线性量子场模型中，给出共同光锥的矩阵判据，并证明该判据不能通过更换观察者坐标而任意满足。对于一类正定、多隐藏场、非导数耦合模型，进一步证明：低频传播速度相同并不足以保证完整几何一致性；空间四阶响应中存在一个非负的“传播锥失配量”，它不能由不同隐藏模式相互抵消。

由此得到一个条件性刚性结论：

$$
\boxed{
\text{在指定模型族内，四阶几何一致性}
\iff
\text{所有实际耦合模式共享同一传播锥}.
}
$$

本文同时区分共同因果结构、热态的参照系依赖和引力动力学，避免将三者混同。

多组分系统出现多重有效度量，以及单一度量需要额外结构条件，是模拟引力研究中的已知问题。以下给出适用于当前观察者—响应模型的具体定义、证明和有限实验判据，而不将这一一般研究方向宣称为新发现。([arXiv][1])

---

# 21．共同光锥的代数判据

## 假设 21.1　局部二次量子场模型

设已经从前文的交互网络中取得一个局部连续描述。空间维数 \(d\) 在本节作为模型参数，不预先声称它已由观察者定义唯一确定。

令

$$
\Psi=(\psi_1,\ldots,\psi_r)^{\mathsf T}
$$

为 \(r\) 个实量子场。在一个系数可视为常数的局部区域，取二次 Lagrangian：

$$
\boxed{
\mathcal L
=
\frac12\dot\Psi^{\mathsf T}M\dot\Psi
-
\frac12
\sum_{i,j}
(\partial_i\Psi)^{\mathsf T}S^{ij}(\partial_j\Psi)
-
\frac12\Psi^{\mathsf T}K\Psi.
}
\tag{21.1}
$$

要求

$$
M=M^{\mathsf T}>0,
\qquad
K=K^{\mathsf T}\ge0,
$$

$$
S^{ij}=S^{ji}=(S^{ij})^{\mathsf T},
$$

并要求空间梯度二次型正定。

这些条件给出稳定的线性传播模型。量子化后，Heisenberg 场方程仍为

$$
M\partial_t^2\Psi
-
\sum_{i,j}S^{ij}\partial_i\partial_j\Psi
+
K\Psi=0.
$$

其二阶主符号为

$$
\boxed{
\mathcal P_2(\omega,k)
=
-\omega^2M+\sum_{i,j}S^{ij}k_ik_j.
}
\tag{21.2}
$$

质量项 \(K\) 不进入主符号。因此，本节的传播锥不同于某个有质量波包在有限动量下的群速度。

---

## 定义 21.1　共同二阶传播锥

若存在正定空间二次型 \(h^{ij}\)，使任意非零 \(k\) 下，全部内部传播模的特征根均满足

$$
\boxed{
\omega^2=h^{ij}k_ik_j,
}
\tag{21.3}
$$

则称该模型具有共同二阶传播锥。

这里要求所有内部模共享同一特征结构，而不只是某一个被选中的模满足式（21.3）。

---

## 定理 21.1　共同传播锥的充要条件

定义 21.1 成立，当且仅当

$$
\boxed{
S^{ij}=h^{ij}M
\qquad
\text{对全部 }i,j.
}
\tag{21.4}
$$

### 证明

进行质量归一化：

$$
A^{ij}=M^{-1/2}S^{ij}M^{-1/2}.
$$

对固定 \(k\)，特征速度由实对称矩阵

$$
A(k)=\sum_{i,j}A^{ij}k_ik_j
$$

的本征值决定。

若全部本征值均为 \(h^{ij}k_ik_j\)，实对称性意味着

$$
A(k)=\left(h^{ij}k_ik_j\right)I.
$$

该式对所有 \(k\) 成立。比较二次多项式的系数，得到

$$
A^{ij}=h^{ij}I.
$$

左右乘以 \(M^{1/2}\)，即得式（21.4）。

反之，若式（21.4）成立，则

$$
\mathcal P_2(\omega,k)
=
M\left[-\omega^2+h^{ij}k_ik_j\right].
$$

因 \(M\) 可逆，全部特征模具有同一零集合。∎

### 注 21.1

共同光锥不是“每种物质分别都存在某个有效速度”，而是时间惯性矩阵与全部空间传播矩阵具有同一个张量因子。

---

# 22．几何失配不能被观察者更名消除

## 定义 22.1　二阶几何残差

定义

$$
h^{ij}
=
\frac1r\operatorname{Tr}
\left(
M^{-1/2}S^{ij}M^{-1/2}
\right),
$$

以及

$$
\boxed{
\mathcal E^{ij}
=
M^{-1/2}S^{ij}M^{-1/2}
-
h^{ij}I.
}
\tag{22.1}
$$

\(\mathcal E^{ij}\) 表示内部传播模相对于平均二次型的差别。

---

## 定理 22.1　几何残差的零判据

有

$$
\boxed{
\mathcal E^{ij}=0\ \forall i,j
\iff
\text{存在共同二阶传播锥}.
}
\tag{22.2}
$$

### 证明

直接由定理 21.1。∎

---

## 定理 22.2　可逆场表示变换不消除几何失配

令

$$
\Psi=R\widetilde\Psi,
\qquad R\in\operatorname{GL}(r,\mathbb R).
$$

则

$$
\widetilde M=R^{\mathsf T}MR,
\qquad
\widetilde S^{ij}=R^{\mathsf T}S^{ij}R.
$$

在质量归一化后，存在同一个正交矩阵 \(O\)，使

$$
\widetilde A^{ij}=O^{\mathsf T}A^{ij}O.
$$

因此

$$
\boxed{
\mathcal E^{ij}=0\ \forall i,j
}
$$

是表示不变量。

### 证明

取

$$
O=M^{1/2}R\widetilde M^{-1/2}.
$$

则

$$
O^{\mathsf T}O
=
\widetilde M^{-1/2}R^{\mathsf T}MR\widetilde M^{-1/2}
=
I.
$$

又有

$$
\widetilde M^{-1/2}
\widetilde S^{ij}
\widetilde M^{-1/2}
=
O^{\mathsf T}A^{ij}O.
$$

正交共轭保持迹、谱及是否为恒等算子倍数，故结论成立。∎

---

## 推论 22.1　共同坐标变换不能合并原本不同的锥

一个可逆时空坐标变换，在每点对协向量施加同一个可逆线性变换。因此，两个不同的特征零集合不可能被该变换变成同一个集合。

### 证明

若两个集合经同一个双射具有相同像，作用逆映射后，它们原来就必须相同。∎

**因此，“从另一个观察者看”不能作为掩盖不同探针传播结构不相容的理由。**

若两类探针确实具有不同特征锥，这是一项需要解释或约束的物理差别，不是纯粹的坐标问题。多组分模拟时空中的单度量与多度量之分，也正体现了这一点。([arXiv][2])

---

## 定理 22.3　内部不可约对称性是共同光锥的一个充分条件

设群 \(G\) 在内部空间上具有实正交不可约表示 \(R_g\)。若

$$
R_g^{\mathsf T}MR_g=M,
$$

$$
R_g^{\mathsf T}S^{ij}R_g=S^{ij}
$$

对全部 \(g,i,j\) 成立，则存在 \(m>0\) 与实数 \(s^{ij}\)，使

$$
M=mI,
\qquad
S^{ij}=s^{ij}I.
$$

故共同光锥成立，并且

$$
h^{ij}=\frac{s^{ij}}m.
$$

### 证明

任意与全部 \(R_g\) 可交换的实对称矩阵，其每个本征子空间都在群作用下不变。

不可约性排除非平凡本征子空间分解，因此该矩阵只能有一个本征值，即为恒等算子的倍数。

分别应用于 \(M\) 和每个 \(S^{ij}\) 即得。∎

### 注 22.2

这提供了一种“为什么多个模共享几何”的结构机制，但不可约对称性本身仍是需要解释或检验的条件。

若其他相互作用破坏这一对称性，不能仅凭自由二次项的证明就断言全部量子修正仍然保持共同光锥。利用内部对称性控制涌现时空的传播普适性，已有具体多组分凝聚态研究。([arXiv][3])

---

# 23．隐藏记忆与共同几何并不矛盾

前文证明，隐藏模式的消去通常产生非局域记忆。现在需要回答：

> 非局域记忆是否必然破坏共同光锥？

答案是否定的。

## 假设 23.1　常系数共同传播结构

设完整系统满足

$$
S^{ij}=h^{ij}M.
$$

定义

$$
s=h^{ij}k_ik_j-\omega^2.
$$

则完整逆传播算子为

$$
\boxed{
D(\omega,k)=K+sM.
}
\tag{23.1}
$$

将内部场分成可见部分 \(V\) 与隐藏部分 \(H\)。

---

## 定理 23.1　共同传播变量在精确 Schur 消去下闭合

在相应隐藏块可逆的区域，

$$
\boxed{
D_{\mathrm{eff}}(s)
=
D_{VV}(s)
-
D_{VH}(s)D_{HH}(s)^{-1}D_{HV}(s).
}
\tag{23.2}
$$

因此，精确消去后的逆传播算子仍然只依赖 \(s\)，不会分别依赖 \(\omega\) 和 \(k\)。

### 证明

式（23.1）的全部块都是同一个变量 \(s\) 的矩阵函数。矩阵加法、乘法与可逆区域内的求逆，不引入新的自变量。因此式（23.2）仍是 \(s\) 的函数。∎

---

## 定理 23.2　可见响应保留共同锥的正谱表示

设 \(K>0\)，并取固定的、无导数的源—读数接口 \(C\)。则

$$
\chi(\omega,k)
=
C(K+sM)^{-1}C^{\mathsf T}
$$

可以写成

$$
\boxed{
\chi(\omega,k)
=
\sum_a
\frac{W_a}
{\mu_a^2+h^{ij}k_ik_j-(\omega+i0)^2},
\qquad
W_a\ge0.
}
\tag{23.3}
$$

### 证明

令

$$
A=M^{-1/2}KM^{-1/2},
\qquad
B=M^{-1/2}C^{\mathsf T}.
$$

则

$$
\chi=B^{\mathsf T}(A+sI)^{-1}B.
$$

对 \(A\) 作正交谱分解：

$$
A=\sum_a\mu_a^2P_a.
$$

于是

$$
W_a=B^{\mathsf T}P_aB\ge0,
$$

并得到式（23.3）。∎

### 解释

可见响应可以包含多个质量尺度、多个共振和复杂记忆，但它们仍然共享同一个传播二次型。

所以：

$$
\boxed{
\text{有记忆}
\not\Rightarrow
\text{没有共同时空}.
}
$$

真正的问题是记忆的频率与波数依赖，是否与同一个传播结构相容。

项目的 `SchurComplementAssociativity.lean` 已经证明，在给定逆算子见证时，逐层消去与一次消去给出同一个保留算子。本节在固定频率上使用这一代数结构，不将其自动升级为未经验证的无界时域算子结论。

对于空间变化的背景，系数与微分算子不再普遍可交换。因此，本节“只依赖一个 \(s\)”的精确结论针对常系数区域；曲背景中的推广需要另行处理协变算子和梯度修正。

---

# 24．低频速度相同，不保证完整几何一致

现在研究前文双场实例的一般化。

## 假设 24.1　一个可见场与若干独立隐藏场

取可见场 \(q\)，以及隐藏场 \(r_a\)，其二次 Lagrangian 为

$$
\begin{aligned}
\mathcal L
={}&
\frac12\dot q^2
-\frac{c_0^2}{2}|\nabla q|^2
-\frac{\Omega_0^2}{2}q^2\\
&+
\sum_a
\left[
\frac12\dot r_a^2
-\frac{c_a^2}{2}|\nabla r_a|^2
-\frac{\Omega_a^2}{2}r_a^2
-\lambda_aqr_a
\right].
\end{aligned}
\tag{24.1}
$$

要求

$$
\Omega_a>0,
\qquad
c_0>0,
\qquad
c_a\ge0,
$$

以及稳定性条件

$$
\boxed{
m_*^2
:=
\Omega_0^2-\sum_a\frac{\lambda_a^2}{\Omega_a^2}
>0.
}
\tag{24.2}
$$

这里没有加入导数耦合，也没有加入可以任意调节的裸四阶导数项。以下刚性结论限定在这一模型族中。

---

## 定理 24.1　精确可见逆响应

消去全部隐藏场后，

$$
\boxed{
D_{\mathrm{eff}}(\omega,k)
=
\Omega_0^2+c_0^2|k|^2-\omega^2
-
\sum_a
\frac{\lambda_a^2}
{\Omega_a^2+c_a^2|k|^2-\omega^2}.
}
\tag{24.3}
$$

### 证明

每个隐藏场满足

$$
\left(
\Omega_a^2+c_a^2|k|^2-\omega^2
\right)r_a
=
-\lambda_aq.
$$

代入可见方程即可。∎

通过消去重场获得改变后的低能传播速度，是有效场论中已有的机制；但其成立范围与高阶修正必须一起分析。([arXiv][4])

---

## 定义 24.1　低频传播参数

令

$$
r_a=\frac{\lambda_a^2}{\Omega_a^4},
\qquad
Z=1+\sum_ar_a,
$$

并定义

$$
\boxed{
c_*^2
=
\frac{c_0^2+\sum_ar_ac_a^2}{Z}.
}
\tag{24.4}
$$

再记

$$
u=|k|^2,
\qquad
s=c_*^2u-\omega^2,
$$

$$
d_a=c_a^2-c_*^2,
\qquad
a_a=\frac{\lambda_a^2}{\Omega_a^6}.
$$

注意这里的 \(a_a\) 是正权重，不是场或行动标签。

---

## 定理 24.2　四阶低频展开

在

$$
|s+d_au|<\Omega_a^2
$$

的共同区域中，

$$
\boxed{
D_{\mathrm{eff}}
=
m_*^2+Zs
-A_0s^2-2A_1su-A_2u^2
+R_6,
}
\tag{24.5}
$$

其中

$$
A_0=\sum_aa_a,
$$

$$
A_1=\sum_aa_ad_a,
$$

$$
\boxed{
A_2=\sum_aa_ad_a^2\ge0.
}
\tag{24.6}
$$

精确余项为

$$
R_6
=
\sum_a
\frac{
\lambda_a^2(s+d_au)^3
}{
\Omega_a^6(\Omega_a^2+s+d_au)
}.
\tag{24.7}
$$

若

$$
|s+d_au|\le\rho\Omega_a^2,
\qquad 0<\rho<1,
$$

则

$$
\boxed{
|R_6|
\le
\frac1{1-\rho}
\sum_a
\frac{
\lambda_a^2|s+d_au|^3
}{
\Omega_a^8
}.
}
\tag{24.8}
$$

### 证明

使用恒等式

$$
-\frac{\lambda^2}{\Omega^2+x}
=
-\frac{\lambda^2}{\Omega^2}
+\frac{\lambda^2x}{\Omega^4}
-\frac{\lambda^2x^2}{\Omega^6}
+\frac{\lambda^2x^3}{\Omega^6(\Omega^2+x)}.
$$

取 \(x=s+d_au\)，逐项代入式（24.3）。

由 \(c_*^2\) 的定义，

$$
c_0^2-c_*^2+\sum_ar_ad_a=0,
$$

所以独立的一阶 \(u\) 项相消。

展开剩余平方项即得式（24.5）。余项界由分母下界得到。∎

这里的“二阶”“四阶”按共同缩放

$$
(\omega,k)\mapsto(\varepsilon\omega,\varepsilon k)
$$

计数。因此 \(s,u\) 是二阶量，\(R_6=O(\varepsilon^6)\)。

---

# 25．四阶几何一致性的正性刚性

## 定义 25.1　标量响应的单一几何相容性

固定源与读数的局部归一化，不允许通过任意依赖 \((\omega,k)\) 的重新滤波改变实验接口。

若存在单变量函数 \(F\)，使

$$
D_{\mathrm{eff}}(\omega,k)=F(s),
$$

则称该标量响应与传播变量

$$
s=c_*^2|k|^2-\omega^2
$$

精确相容。

若仅在四阶以内具有该形式，则称为四阶相容。

该定义比“一个零点附近的色散关系可以近似拟合某个速度”更强：它约束的是已标定源—读数之间的整个响应。

---

## 定理 25.1　四阶刚性定理

在假设 24.1 的模型族中，以下陈述等价：

1. 可见逆响应精确地只依赖 \(s\)；
2. 可见逆响应在四阶以内只依赖 \(s\)；
3. \(A_2=0\)；
4. 每个实际耦合的隐藏场满足

   $$
   c_a=c_*,
   $$

   且

   $$
   c_0=c_*.
   $$

### 证明

**\(1\Rightarrow2\)。**由解析展开立即成立。

**\(2\Rightarrow3\)。**沿

$$
\omega^2=c_*^2|k|^2
$$

取值，此时 \(s=0\)。若四阶以内只依赖 \(s\)，则四阶中不能出现独立的 \(|k|^4\) 项。

而式（24.5）给出

$$
D_{\mathrm{eff}}\big|_{s=0}
=
m_*^2-A_2|k|^4+O(|k|^6).
$$

故 \(A_2=0\)。

**\(3\Rightarrow4\)。**由于

$$
A_2
=
\sum_a
\frac{\lambda_a^2}{\Omega_a^6}
(c_a^2-c_*^2)^2,
$$

每项非负。因此，对 \(\lambda_a\ne0\) 的全部模式，

$$
c_a^2=c_*^2.
$$

再由式（24.4），得到 \(c_0^2=c_*^2\)。速度取非负，故结论成立。

**\(4\Rightarrow1\)。**此时全部分母变成

$$
\Omega_a^2+s,
$$

并且

$$
D_{\mathrm{eff}}
=
\Omega_0^2+s
-
\sum_a\frac{\lambda_a^2}{\Omega_a^2+s},
$$

精确地只依赖 \(s\)。∎

---

### 结论 25.1

在这一模型族中，

$$
\boxed{
\text{二阶平均速度可以通过加权平均取得一致；}
}
$$

$$
\boxed{
\text{四阶相容性却检测每个实际耦合隐藏模的失配。}
}
$$

尤其，

$$
A_1=\sum_aa_ad_a
$$

可以因正负 \(d_a\) 相消，但

$$
A_2=\sum_aa_ad_a^2
$$

不能这样相消。

**共同几何因此不只是一个平均值条件，而是一项受正性约束的跨模式一致性条件。**

### 适用边界

本定理不声称所有量子场论都具有这项刚性。

加入独立裸四阶算子、导数耦合、非正谱权重或更一般的隐藏场混合后，需要重新证明。不能把本模型的正平方和结论直接推广到未定义的相互作用理论。

---

## 推论 25.1　近似几何对隐藏模式的限制

若 \(A_0>0\)，定义谱权重

$$
p_a=\frac{a_a}{A_0}.
$$

则

$$
\boxed{
\sum_ap_a(c_a^2-c_*^2)^2
=
\frac{A_2}{A_0}.
}
\tag{25.1}
$$

对任意 \(\Delta>0\)，

$$
\boxed{
\sum_{|c_a^2-c_*^2|\ge\Delta}p_a
\le
\frac{A_2}{A_0\Delta^2}.
}
\tag{25.2}
$$

### 证明

在求和集合内，

$$
(c_a^2-c_*^2)^2\ge\Delta^2.
$$

代入式（25.1）即可。∎

这一结果限制的是**被当前接口加权看见的隐藏模式**。极弱耦合或极高频模式的权重可以很小，所以有限实验不能由此断言整个不可见世界全部共享同一速度。

---

# 26．精确反例：时间频谱相同，空间几何不同

取一个可见场和两个隐藏场，并在选定单位下令

$$
\Omega_0^2=\Omega_1^2=\Omega_2^2=1,
$$

$$
\lambda_1=\lambda_2=\frac12,
\qquad
c_0^2=1.
$$

其零动量恢复矩阵为

$$
K=
\begin{pmatrix}
1&1/2&1/2\\
1/2&1&0\\
1/2&0&1
\end{pmatrix}.
$$

本征值为

$$
1,\qquad
1-\frac1{\sqrt2},\qquad
1+\frac1{\sqrt2},
$$

全部为正。

比较两个模型。

### 模型 A

$$
c_1^2=c_2^2=1.
$$

### 模型 B

$$
c_1^2=\frac12,
\qquad
c_2^2=\frac32.
$$

两者都有

$$
Z=\frac32,
\qquad
c_*^2=1,
\qquad
m_*^2=\frac12.
$$

记

$$
s=|k|^2-\omega^2,
\qquad
u=|k|^2.
$$

则

$$
D_A
=
1+s-\frac1{2(1+s)},
$$

$$
D_B
=
1+s-
\frac{1+s}
{2\left[(1+s)^2-u^2/4\right]}.
$$

直接相减：

$$
\boxed{
D_B-D_A
=
-\frac{
u^2
}{
8(1+s)\left[(1+s)^2-u^2/4\right]
}.
}
\tag{26.1}
$$

因此，在 \(k=0\) 上，

$$
\boxed{
D_A(\omega,0)=D_B(\omega,0)
}
$$

对全部非奇异频率成立。

两者不仅静态响应相同，**空间均匀驱动下的完整时间频谱也相同**。

但低频展开给出

$$
D_A
=
\frac12+\frac32s-\frac12s^2+O(\varepsilon^6),
$$

$$
\boxed{
D_B
=
\frac12+\frac32s-\frac12s^2
-\frac18|k|^4
+O(\varepsilon^6).
}
\tag{26.2}
$$

故空间变化的实验可以区分二者。

这些矩阵本征值、精确差值与展开已作符号核验。

### 推论 26.1

仅凭零空间波数的完整时间响应，不能唯一重建空间传播结构。

这不与前文“响应确定最小可观测实现”矛盾：前者只识别该指定接口与驱动族看见的实现；加入空间分辨驱动后，实验语法扩大，可见结构也随之扩大。

因此：

$$
\boxed{
\text{时空重建需要空间分辨的干预协议，
不能只依赖一条时间序列。}
}
$$

---

# 27．有限精度下，四阶几何残差怎样被识别？

形式上的四阶导数存在，不等于有限观察者能够免费精确读取它。

沿 \(s=0\) 定义

$$
F(k)
=
D_{\mathrm{eff}}(c_*|k|,k)-D_{\mathrm{eff}}(0,0).
$$

由前述展开，

$$
F(k)=-A_2|k|^4+R(k).
$$

假设在实验窗口内已经证明

$$
|R(k)|\le C|k|^6.
$$

设测量值 \(\widetilde F(k)\) 的总误差满足

$$
|\widetilde F(k)-F(k)|\le\epsilon.
$$

这里的总误差应包括驱动、读数、参考值和传播参数标定误差。

---

## 定理 27.1　四阶残差估计界

定义

$$
\widehat A_2(k)
=
-\frac{\widetilde F(k)}{|k|^4}.
$$

则

$$
\boxed{
|\widehat A_2(k)-A_2|
\le
\frac{\epsilon}{|k|^4}
+
C|k|^2.
}
\tag{27.1}
$$

### 证明

由三角不等式，

$$
\begin{aligned}
|\widehat A_2-A_2|
&=
\frac{
|\widetilde F+A_2|k|^4|
}{
|k|^4
}\\
&\le
\frac{|\widetilde F-F|+|R(k)|}{|k|^4}.
\end{aligned}
$$

代入假设即得。∎

---

## 推论 27.1　低波数极限不是无条件最优实验

在误差上界 \(\epsilon\) 与 \(k\) 无关、且最优点位于有效窗口内的条件下，式（27.1）右侧在

$$
\boxed{
|k|_{\mathrm{opt}}^6=\frac{2\epsilon}{C}
}
\tag{27.2}
$$

处最小。

最小上界为

$$
\boxed{
\frac{3}{2^{2/3}}
C^{2/3}\epsilon^{1/3}.
}
\tag{27.3}
$$

### 证明

对

$$
f(r)=\epsilon r^{-4}+Cr^2
$$

求导并令其为零。∎

### 解释

波数过大，高阶截断误差增大；波数过小，四阶信号被测量误差淹没。

因此，几何一致性的验证应同时包含：

$$
\text{结构判据}
+
\text{有效窗口}
+
\text{实验误差预算}.
$$

这与项目已有的“精确闭合、条件良好的闭合、物理可实现闭合”三层区分一致。

---

# 28．完整因果界、有效速度与热噪声必须分开

## 定理 28.1　完整多场模型的传播上界

考虑假设 24.1 的常系数完整场方程，并记

$$
c_{\max}=\max(c_0,c_1,\ldots).
$$

若初始数据支持在半径为 \(R\) 的球内，则完整无源解在

$$
|x|>R+c_{\max}t
$$

处为零。

### 证明

将全部场记为 \(q_a\)。定义局部能量密度

$$
e
=
\frac12\sum_a\dot q_a^2
+
\frac12\sum_ac_a^2|\nabla q_a|^2
+
\frac12q^{\mathsf T}Kq,
$$

以及能流

$$
j=-\sum_ac_a^2\dot q_a\nabla q_a.
$$

场方程给出

$$
\partial_t e+\nabla\cdot j=0.
$$

对单位法向量 \(n\)，

$$
\begin{aligned}
|j\cdot n|
&\le
\sum_ac_a^2|\dot q_a|\,|\partial_nq_a|\\
&\le
\frac{c_{\max}}2
\sum_a
\left(
\dot q_a^2+c_a^2|\nabla q_a|^2
\right)\\
&\le c_{\max}e.
\end{aligned}
$$

对向外以速度 \(c_{\max}\) 扩大的球外区域积分，能量不可能从零增加，故球外解保持为零。∎

### 推论 28.1

前文的低频有效速度 \(c_*\)，一般不能直接替代完整传播上界 \(c_{\max}\)。

因此：

$$
\boxed{
\text{低频有效视界}
\not\Rightarrow
\text{完整理论中的绝对因果视界}.
}
$$

只有证明全部允许模式与全部相关频率都不能跨越某个边界，才能获得相应的完整因果结论。

同样，不能把四阶截断式当作任意高频下的基本方程，并据其额外根宣称原本稳定的完整模型出现了不稳定粒子。截断展开必须留在已证明的有效窗口内。

---

## 定理 28.2　固定线性量子模型中，因果响应与状态涨落可具有不同的参照性质

在正则量子化的固定二次模型中，场解线性依赖初始正则算子。因此场交换子为由动力学确定的数值核乘以恒等算子，不依赖所选量子态。

但对称关联函数一般依赖量子态。

### 证明

把初始正则算子合写为 \(X_0\)，线性演化为

$$
X(t)=S(t)X_0.
$$

若

$$
[X_{0,a},X_{0,b}]=i\hbar J_{ab}I,
$$

则

$$
[X_a(t),X_b(t')]
=
i\hbar
\bigl[S(t)JS(t')^{\mathsf T}\bigr]_{ab}I.
$$

右边由演化矩阵和正则结构决定。

相反，

$$
\frac12\langle\{X_a(t),X_b(t')\}\rangle
$$

还依赖初始协方差矩阵。∎

### 注 28.1

因此，一个热态具有自己的静止参照系、不同运动观察者读取不同热关联，并不直接意味着基础传播方程不协变。

必须区分：

$$
\boxed{
\text{动力学的共同因果锥}
}
$$

与

$$
\boxed{
\text{某个状态是否在全部参照变换下不变}.
}
$$

相对论 KMS 理论正是在保留热态特征的同时讨论热关联的协变表达。([arXiv][5])

在存在非线性反作用时，状态本身可能改变有效传播系数；那是需要另行分析的机制，不能套用本节固定二次模型的状态无关结论。

---

# 29．从共同传播锥到几何，以及钟—空间响应的一致性

若定理 21.1 在每个局部点成立，且系数光滑，可以由

$$
-\omega^2+h^{ij}k_ik_j
$$

重建一个洛伦兹共形结构。

若存在共同漂移 \(w^i\)，则主符号变成

$$
-(\omega-w^ik_i)^2+h^{ij}k_ik_j.
$$

对应的一族度量为

$$
\boxed{
ds^2
=
\Omega(x,t)^2
\left[
-dt^2+
h_{ij}
(dx^i-w^idt)(dx^j-w^jdt)
\right],
}
\tag{29.1}
$$

其中 \(h_{ij}\) 为 \(h^{ij}\) 的逆，\(\Omega>0\) 仍需钟尺标定。

**共同光锥只能固定共形结构，不能独自固定全部几何尺度。**

---

## 命题 29.1　弱场钟速与传播速度的联合检验

在局部各向同性、静态弱场实现中，设

$$
ds^2
=
-N(x)^2c_{\mathrm{ref}}^2dt^2
+
A(x)^2d\mathbf x^2.
$$

令

$$
N=1+u+O(u^2),
$$

$$
A=1-\gamma u+O(u^2).
$$

则静止钟满足

$$
\frac{d\tau}{dt}=N,
$$

而局部坐标信号速度满足

$$
\boxed{
\frac{c_{\mathrm{coord}}^2}{c_{\mathrm{ref}}^2}
=
1+2(1+\gamma)u+O(u^2).
}
\tag{29.2}
$$

因此

$$
\boxed{
\gamma
=
\frac12
\left.
\frac{d(c_{\mathrm{coord}}^2/c_{\mathrm{ref}}^2)}{du}
\right|_{u=0}
-1.
}
\tag{29.3}
$$

### 证明

令 \(ds^2=0\)，得到

$$
c_{\mathrm{coord}}^2
=
c_{\mathrm{ref}}^2\frac{N^2}{A^2}.
$$

对 \(u\) 展开即可。∎

### 推论 29.1

在这一弱场表示中，若希望得到广义相对论的 \(\gamma=1\)，则钟速响应与空间传播响应必须满足

$$
\boxed{
\left.
\frac{d(c_{\mathrm{coord}}^2/c_{\mathrm{ref}}^2)}{du}
\right|_{u=0}
=4.
}
\tag{29.4}
$$

这不是“钟变慢”单独能够保证的关系。

参数 \(\gamma\) 同时进入标准的光线偏折与传播延迟检验，因此式（29.4）是一项进一步的物理一致性目标，而不只是改写坐标的自由。([arXiv][6])

---

### 本节的边界

即使全部探针共享一个锥，也仍然可能没有证明：

$$
\text{所有钟共享同一尺度标定},
$$

$$
\text{物质能量普适地改变该几何},
$$

$$
\text{几何自身满足 Einstein 动力学}.
$$

本增订把第一项之前的“共同传播”问题推进为可检验矩阵条件，并给出了继续约束第二项的钟—传播联合响应式，但不以此替代全部引力场方程。

---

# 30．共同几何的观察者完成命题

## 定理 30.1　条件性共同几何重建

考虑本增订定义的稳定二次量子模型及其经过标定的源—读数协议。

若满足：

* 二阶传播矩阵的几何残差全部为零；
* 对允许的隐藏模式消去，完整响应保持同一个传播变量；
* 内部钟能够为该共形结构提供相容标定；

则在这些协议覆盖的范围内，可见实验具有一个共同洛伦兹几何描述。

在假设 24.1 的特殊模型族中，第二项可以由四阶残差

$$
A_2
=
\sum_a
\frac{\lambda_a^2}{\Omega_a^6}
(c_a^2-c_*^2)^2
$$

是否为零来严格判定。

### 证明

第一项由定理 21.1 给出共同二次型。

第二项保证精确约化没有引入与该二次型不相容的独立频率—波数结构。共同传播结构的充分闭合由定理 23.1 给出；特殊模型族的必要性由定理 25.1 给出。

最后，内部钟为尚未确定的共形尺度提供标定，得到式（29.1）所代表的具体几何。∎

---

## 项目中的对应位置

本轮的推进不是把“共同光锥”加入定义后直接宣布成功，而是为项目现有框架增加一组明确目标：

**CUT**：固定源、读数、钟和波数分辨能力，说明实验究竟保留什么信息。

**FLOW**：给出完整的局域量子动力学，而不是只保留某个低频速度。

**Residual**：由 \(\mathcal E^{ij}\) 检测二阶模间失配，由 \(A_2\) 检测指定隐藏模型中的四阶失配。

**Completion**：当新的空间分辨协议揭示差别时，扩大可观测结构，而不是把差别解释为任意观察者选择。

**ADMIT**：同时检查稳定性、正谱权重、共同传播结构、有效窗口与误差预算。

仓库已有的 Schur 结合律和观察者完成理论可以承担其中的代数与闭包基础；本增订的共同锥判据、四阶刚性组合和实验误差结果尚未进行 Lean 编译。

---

# 结论

前一轮建立了：

$$
\text{动态响应}
\longrightarrow
\text{隐藏记忆与有效传播}.
$$

本轮进一步证明：

$$
\boxed{
\text{有效传播并不自动构成共同物理时空。}
}
$$

共同几何必须满足两层相容性：

$$
\boxed{
\text{不同内部模的二阶传播相容},
}
$$

以及

$$
\boxed{
\text{隐藏模式留下的高阶响应，
仍与同一几何变量相容}.
}
$$

最重要的具体结果是：

$$
\boxed{
A_2
=
\sum_a
\frac{\lambda_a^2}{\Omega_a^6}
(c_a^2-c_*^2)^2
\ge0.
}
$$

在所研究的模型族里，平均速度可以通过调参一致，但这一正平方和不会因不同模式的正负失配而相消。它使“所有探针共享一个时空”成为一项可以证明、估计并被实验否定的结构命题。

因此，量子观察者理论可以再收紧为：

> **观察者并不任意选择一个几何来解释数据；它必须检验所有允许的干预、传播与钟比较，能否共同通过同一个几何结构因子化。**

**共同物理时空，就是这种跨探针、跨频率、跨观察接口的一致性结构。**在一致性成立的范围内，几何是有效且可预测的；在高阶响应揭示失配的范围内，理论必须保留更多量子结构，而不能继续把它们压缩成同一张经典时空。

[1]: https://arxiv.org/abs/gr-qc/0111059?utm_source=chatgpt.com "Refringence, field theory, and normal modes"
[2]: https://arxiv.org/abs/gr-qc/0510125?utm_source=chatgpt.com "Analogue quantum gravity phenomenology from a two-component Bose-Einstein condensate"
[3]: https://arxiv.org/abs/1011.4411?utm_source=chatgpt.com "Emergent gravitational dynamics from multi-BEC hydrodynamics?"
[4]: https://arxiv.org/abs/1205.0710?utm_source=chatgpt.com "Heavy fields, reduced speeds of sound and decoupling during inflation"
[5]: https://arxiv.org/abs/hep-th/9807099?utm_source=chatgpt.com "Towards a Relativistic KMS Condition"
[6]: https://arxiv.org/abs/1403.7377?utm_source=chatgpt.com "The Confrontation between General Relativity and Experiment"
# 钟记录、径向俘获与视界红移

## ——量子观察者—关系时空理论第三十一至第四十节增订

### 摘要

“观察者吞噬时间，黑洞吞噬空间”可以保留为研究直觉，但必须分解为不同的数学命题。

对观察者而言，至少存在两种不同现象：**过去的交互被编码进当前记忆；其他过程的时间变化，在该观察者的读数中受到压缩或拉伸。**

对黑洞而言，准确的局部几何内容不是空间消失，而是：**在未来俘获区域内，向更大面积半径运动不再属于任何未来指向因果轨迹的可选行为。**

本增订证明，在一类明确的球对称静态几何实现中，外部静止钟速、径向传播与球面膨胀率由同一个函数控制：

$$
\boxed{
\left(\frac{d\tau_{\mathrm{stat}}}{dT}\right)^2
=
g^{-1}(dr,dr)
=
-\frac{r^2}{4c^2}\theta_+\theta_-.
}
\tag{A}
$$

因此，所谓“时间压缩”与“空间俘获”可以成为**同一因果结构的两种读数**。但它们并不证明观察者与黑洞是同一个物理对象，也不自动给出虫洞。

下文首先给出量子记录与钟的定义，再在特定几何中建立对应。这里不将此前的弱场线性钟速模型无条件外推到视界，也不声称已由一般观察者定义唯一推出黑洞几何。

---

# 31．“吞噬时间”的第一种含义：把历史压缩成当前记录

## 定义 31.1　历史记录接口

设 \(\mathscr H\) 为允许的有限交互历史集合。一个量子记忆接口是映射

$$
\mathcal R:\mathscr H\longrightarrow\mathcal D(\mathcal H_M),
$$

其中 \(\mathcal D(\mathcal H_M)\) 为记忆寄存器的密度矩阵集合。

对历史 \(h\)，记

$$
\rho_M(h)=\mathcal R(h).
$$

这表示：观察者当前保存的不是整个历史本身，而是历史通过实际交互留下的量子记录。

定义当前记忆不可区分关系：

$$
h\sim_M h'
\iff
\rho_M(h)=\rho_M(h').
$$

这一接口核可以作为项目既有 CUT 的实例。但“当前记录相同”不自动保证全部未来实验相同；若外部关联随后重新影响记录，就产生动力接口的 carry。仓库已将这类区别形式化为当前核与未来读数核之间的下降障碍。

---

## 定理 31.1　有限量子记忆的精确历史容量

设

$$
\dim\mathcal H_M=d<\infty.
$$

若历史 \(h_1,\ldots,h_N\) 可以仅凭该记忆、通过一次指定测量被无误地区分，则

$$
\boxed{N\le d.}
\tag{31.1}
$$

### 证明

令对应状态为 \(\rho_1,\ldots,\rho_N\)，并设测量效果满足

$$
E_j\ge0,\qquad \sum_jE_j=I,
$$

$$
\operatorname{Tr}(E_j\rho_i)=\delta_{ij}.
$$

条件 \(\operatorname{Tr}(E_i\rho_i)=1\) 意味着 \(\rho_i\) 的支持包含于 \(E_i\) 的本征值 \(1\) 子空间。

而对 \(j\ne i\)，条件 \(\operatorname{Tr}(E_i\rho_j)=0\) 意味着 \(\rho_j\) 的支持包含于 \(E_i\) 的核。

因此不同 \(\rho_i\) 的支持两两正交。每个支持至少一维，故 \(N\le d\)。∎

### 解释

这个定理不限制密度矩阵的数学参数有多少；它限制的是有限记忆中可以**完美区分**的记录数。

所以，观察者可以把经历压缩成当前记忆，但不能因此被当作一个无损保存无限历史的有限装置。

---

## 定理 31.2　记录合并不等于全局信息删除

设两个正交历史输入通过完整等距过程变为

$$
V|h_i\rangle|0\rangle
=
|m\rangle|e_i\rangle,
\qquad i=1,2.
$$

则

$$
\boxed{\langle e_1|e_2\rangle=0.}
\tag{31.2}
$$

### 证明

等距映射保持内积，因此

$$
0=\langle h_1|h_2\rangle
=
\langle m|m\rangle\langle e_1|e_2\rangle
=
\langle e_1|e_2\rangle.
$$

∎

于是，“历史被吞进当前记忆”只能表示一种**局部编码与压缩**。未被当前记忆保留的区别，可能仍然存在于其他寄存器或关联中。

这与仓库的环境记录模型一致：对环境取偏迹后，局部相干由记录重叠控制，而完整联合过程并没有因此被定义为信息湮灭。

---

# 32．一个同时表达钟速与空间可达性的几何实现

本节接续前文已经建立的共同光锥条件，选择一个具体的球对称静态实现。

## 假设 32.1　穿视界的球对称度量

取

$$
\boxed{
ds^2
=
-c^2dT^2+
\bigl(dr+v(r)dT\bigr)^2+
r^2d\Omega_2^2,
}
\tag{32.1}
$$

其中 \(v(r)\ge0\) 光滑，\(r>0\) 为面积半径，即对称球面的面积为

$$
\mathcal A(r)=4\pi r^2.
$$

定义

$$
\boxed{
f(r)=1-\frac{v(r)^2}{c^2}.
}
\tag{32.2}
$$

\(T\) 是经标定的参照时间，未来方向取 \(dT>0\)。

这类坐标可以穿过某些黑洞视界而不出现坐标退化。Schwarzschild 情形对应

$$
v(r)=c\sqrt{\frac{r_s}{r}},
\qquad
r_s=\frac{2GM}{c^2}.
$$

这里的 \(v\) 是所选分解中的几何漂移参数，不是某种物质相对于局部惯性系的超光速运动。([arXiv][1])

---

## 定理 32.1　钟速—径向特征恒等式

在 \(f(r)>0\) 的区域，保持 \(r,\Omega\) 不变的静止钟满足

$$
\boxed{
\frac{d\tau_{\mathrm{stat}}}{dT}=\sqrt{f(r)}.
}
\tag{32.3}
$$

两类径向 null 信号满足

$$
\boxed{
\dot r_+=c-v(r),
\qquad
\dot r_-=-c-v(r).
}
\tag{32.4}
$$

并且

$$
\boxed{
f(r)
=
-\frac{\dot r_+\dot r_-}{c^2}
=
g^{-1}(dr,dr).
}
\tag{32.5}
$$

### 证明

对静止轨迹取 \(dr=d\Omega=0\)，则

$$
ds^2=-(c^2-v^2)dT^2=-c^2d\tau^2,
$$

得到式（32.3）。

对径向 null 曲线，

$$
0=-c^2+(\dot r+v)^2,
$$

所以得到式（32.4）。

径向度量矩阵与其逆分别为

$$
g_{\mathrm{rad}}
=
\begin{pmatrix}
-c^2+v^2&v\\
v&1
\end{pmatrix},
$$

$$
g_{\mathrm{rad}}^{-1}
=
\begin{pmatrix}
-1/c^2&v/c^2\\
v/c^2&1-v^2/c^2
\end{pmatrix}.
$$

因此 \(g^{-1}(dr,dr)=f\)。同时，

$$
-\frac{(c-v)(-c-v)}{c^2}=f.
$$

∎

### 关键解释

同一个函数 \(f\) 同时回答两个问题：

> 静止钟相对于参照钟积累多少固有时间？

> 向外的信号还能否增加面积半径？

但两者不是两种独立物质被分别吞掉，而是同一个光锥结构的不同表达。

尤其在 \(f=0\) 处，

$$
\det g_{\mathrm{rad}}=-c^2\ne0.
$$

所以，**静止钟公式趋零，并不意味着整个度量消失或时间本身终止。**

---

# 33．“黑洞吞噬空间”的严格局部含义

## 定义 33.1　径向 null 膨胀率

定义两类未来径向 null 法向量：

$$
k_\pm
=
\partial_T+(-v\pm c)\partial_r.
$$

它们满足归一化

$$
g(k_+,k_-)=-2c^2.
$$

定义球面面积沿其变化的膨胀率：

$$
\theta_\pm
=
\frac1{\mathcal A}k_\pm(\mathcal A).
$$

由此：

$$
\boxed{
\theta_+=\frac{2(c-v)}r,
\qquad
\theta_-=-\frac{2(c+v)}r.
}
\tag{33.1}
$$

用双 null 膨胀率描述球对称俘获结构，是黑洞局部几何的标准方法。它与依赖完整未来的事件视界定义相关，但不相同。([arXiv][2])

---

## 定理 33.1　静止钟、径向梯度与俘获结构的统一判据

在本节模型中，

$$
\boxed{
f(r)
=
-\frac{r^2}{4c^2}\theta_+\theta_-.
}
\tag{33.2}
$$

并且：

$$
\begin{array}{c|c|c}
f>0 & \theta_+>0,\ \theta_-<0 & \text{可存在静止类时观察者}\\
f=0 & \theta_+=0,\ \theta_-<0 & \text{向外分支处于边界}\\
f<0 & \theta_+<0,\ \theta_-<0 & \text{未来俘获区域}
\end{array}
$$

### 证明

将式（33.1）相乘：

$$
\theta_+\theta_-
=
-\frac{4(c^2-v^2)}{r^2}.
$$

其余结论由 \(v\ge0\) 和式（32.3）立即得到。∎

---

## 定理 33.2　未来俘获区内，增加面积半径不是可实施行动

若某点 \(v(r)>c\)，则通过该点的任意未来指向类时曲线都满足

$$
\boxed{\frac{dr}{dT}<0.}
\tag{33.3}
$$

未来指向 null 曲线也不能增加 \(r\)。

### 证明

类时条件给出

$$
-c^2+(\dot r+v)^2+r^2|\dot\Omega|^2<0.
$$

因此

$$
\dot r+v<c,
$$

所以

$$
\dot r<c-v<0.
$$

null 情形将严格不等式换成非严格不等式，仍有 \(\dot r\le c-v<0\)。∎

### 解释

“黑洞吞噬空间”在这里可以严格改写为：

$$
\boxed{
\text{原先属于空间选择的“增加 }r\text{”，
不再属于任何未来因果行动。}
}
$$

它不表示空间维数消失。局部观察者仍然有空间方向，仍然可以转动、测量和记录；但所有未来路径都受到同一个径向单调性约束。

---

## 推论 33.1　跨过边界不要求观察者的固有钟停止

取径向轨迹

$$
\frac{dr}{dT}=-v(r).
$$

代入式（32.1）：

$$
ds^2=-c^2dT^2,
$$

故

$$
\boxed{d\tau=dT.}
\tag{33.4}
$$

只要 \(v\) 在边界附近光滑且非零，这条类时轨迹可以在有限固有时间内跨越该边界。

因此：

> **停止存在的是“保持面积半径不变的类时轨迹”，而不是所有观察者的时间。**

这与 Schwarzschild 几何中静止坐标失效、但下落观察者可以跨越视界的区别一致。([David Tong][3])

---

# 34．量子钟如何读取这个临界点？

几何钟速必须进一步落实为量子状态的变化。

## 假设 34.1　理想测试钟

在 \(f(r)>0\) 的固定位置，放置一个有限维量子钟，其内部 Hamiltonian 为 \(H_C\)，初态为 \(|\chi_0\rangle\)。

忽略钟对背景的反作用及其内部噪声，钟态为

$$
|\chi_r(T)\rangle
=
e^{-iH_C\sqrt{f(r)}T/\hbar}|\chi_0\rangle.
\tag{34.1}
$$

这是测试钟近似。保持静止所需的装置与力并不是免费资源，其极限将在下一节处理。

---

## 定理 34.1　时间参数可区分性的缩放

令

$$
(\Delta H_C)^2
=
\langle H_C^2\rangle-\langle H_C\rangle^2.
$$

关于固有时间和参照时间的纯态量子 Fisher 信息分别为

$$
\boxed{
\mathcal F_\tau
=
\frac{4(\Delta H_C)^2}{\hbar^2},
}
\tag{34.2}
$$

$$
\boxed{
\mathcal F_T
=
f(r)\mathcal F_\tau.
}
\tag{34.3}
$$

若 \(\Delta H_C>0\)，则

$$
\boxed{
\frac{\mathcal F_T}{\mathcal F_\tau}
=
-\frac{\dot r_+\dot r_-}{c^2}
=
-\frac{r^2}{4c^2}\theta_+\theta_-.
}
\tag{34.4}
$$

### 证明

纯态族的量子 Fisher 信息为

$$
\mathcal F_T
=
4\left(
\langle\partial_T\chi|\partial_T\chi\rangle
-
|\langle\chi|\partial_T\chi\rangle|^2
\right).
$$

由

$$
\partial_T|\chi\rangle
=
-\frac{i\sqrt f}{\hbar}H_C|\chi\rangle,
$$

得到式（34.3）。固有时间公式同理。再应用定理 32.1 与 33.1。∎

量子 Fisher 信息与酉参数生成元的方差关系，是量子计量中的标准结果；这里的新组合是将其与同一几何中的径向特征和球面膨胀率对应。([arXiv][4])

### 注 34.1

式（34.4）仅在外部静止钟存在的区域成立，不能延拓成内部“负的 Fisher 信息”。

当 \(f\to0^+\) 时：

$$
\mathcal F_T\to0,
$$

但

$$
\mathcal F_\tau
=
\frac{4(\Delta H_C)^2}{\hbar^2}
$$

并未改变。

**下降的是这只钟对参照时间 \(T\) 的编码速率，不是它在自身固有时间中丧失一切变化。**

同样，这不表示关于位置、场强或其他参数的全部实验信息都消失；这里明确指定了所估计的参数。

---

# 35．“静止时间冻结”的资源边界与近视界结构

## 假设 35.1　非退化边界

设

$$
f(r_h)=0,
\qquad
f'(r_h)>0,
$$

并定义

$$
\boxed{
\kappa=\frac{c^2}{2}f'(r_h)>0.
}
\tag{35.1}
$$

在给定时间归一化下，\(\kappa\) 对应此静态边界的表面引力尺度。

---

## 定理 35.1　保持静止所需加速度发散

对外部静止观察者，其固有加速度大小为

$$
\boxed{
a_{\mathrm{stat}}(r)
=
\frac{c^2|f'(r)|}{2\sqrt{f(r)}}.
}
\tag{35.2}
$$

因此

$$
a_{\mathrm{stat}}\to\infty
\qquad(r\to r_h^+),
$$

同时

$$
\boxed{
\sqrt f\,a_{\mathrm{stat}}\to\kappa.
}
\tag{35.3}
$$

### 证明

在外部定义静态时间坐标

$$
dt
=
dT-\frac{v(r)}{c^2-v(r)^2}\,dr.
$$

度量变为

$$
ds^2=-c^2f(r)dt^2+\frac{dr^2}{f(r)}+r^2d\Omega_2^2.
$$

静止四速度为

$$
u=f^{-1/2}\partial_t.
$$

计算 \(a^\mu=u^\nu\nabla_\nu u^\mu\)，其径向分量为

$$
a^r=\frac{c^2}{2}f'(r).
$$

利用 \(g_{rr}=f^{-1}\) 得到式（35.2）。其余由边界展开得到。∎

### 结论

“不断接近边界并保持静止，同时观察自己的钟变慢”不是一个资源不变的极限。

**在理想公式达到零钟速之前，保持该观察者族的加速度要求已经无界增长。**

这阻止我们把静止钟公式直接解释为某个实际观察者能够停在视界上、经历“没有时间”的状态。

---

## 定理 35.2　近边界的径向几何具有 Rindler 形式

定义外部静态切片上的径向固有距离

$$
\ell(r)
=
\int_{r_h}^r\frac{ds}{\sqrt{f(s)}}.
$$

则在边界附近，

$$
\ell
\sim
\sqrt{\frac{2c^2(r-r_h)}{\kappa}},
$$

以及

$$
\boxed{
\sqrt f\sim\frac{\kappa\ell}{c^2}.
}
\tag{35.4}
$$

因此径向度量的领先阶为

$$
\boxed{
ds_{\mathrm{rad}}^2
=
-\left(\frac{\kappa\ell}{c}\right)^2dt^2+d\ell^2.
}
\tag{35.5}
$$

### 证明

使用

$$
f(r)
=
\frac{2\kappa}{c^2}(r-r_h)
+
O((r-r_h)^2)
$$

计算积分并反解即可。∎

式（35.5）正是 Rindler 型径向结构。适当坐标变换

$$
cT_M=\ell\sinh(\kappa t/c),
$$

$$
X_M=\ell\cosh(\kappa t/c)
$$

把该径向部分写成平直形式。

**因此，观察者加速视界与非退化黑洞近视界之间，确实存在局部几何联系；但局部径向形式相同，不意味着全局曲率、拓扑、量子态和全部可访问区域相同。**

在量子场论中，选择相应真空或平衡态后，这种联系进一步表现为 Unruh 与 Hawking 温度结构：

$$
T_U=\frac{\hbar a}{2\pi ck_B},
\qquad
T_H=\frac{\hbar\kappa}{2\pi ck_B}.
$$

温度结论还依赖量子场态与相应条件，不能只由“出现视界”四个字无条件推出。([arXiv][5])

---

# 36．有限源时间如何被拉伸成无限接收时间？

这一节更接近“吞噬时间”的另一种直觉：两个观察者对同一串事件使用的时间标定，可能发生奇异的相对拉伸。

## 假设 36.1　穿越边界的发射者

设发射者在有限固有时间 \(\tau_h\) 到达 \(r_h\)，且

$$
r(\tau)-r_h
=
a(\tau_h-\tau)+O((\tau_h-\tau)^2),
\qquad a>0.
$$

其穿视界坐标 \(T_e(\tau)\) 在该处光滑有限。

位于 \(R>r_h\) 的外部接收者读取发出的径向向外信号。

---

## 定理 36.1　非退化边界的对数接收延迟

信号到达的参照时间满足

$$
\boxed{
T_R(\tau)
=
-\frac c\kappa
\log\left(\frac{\tau_h-\tau}{\tau_*}\right)
+B+o(1),
}
\tag{36.1}
$$

其中 \(\tau_*>0\)、\(B\) 为与归一化及远区传播有关的常数。

等价地，

$$
\boxed{
\tau(T_R)
=
\tau_h-Ae^{-\kappa T_R/c}
+
o(e^{-\kappa T_R/c}),
}
\tag{36.2}
$$

其中 \(A>0\)。

### 证明

由径向向外传播速度，

$$
T_R(\tau)
=
T_e(\tau)
+
\int_{r(\tau)}^R\frac{dr}{c-v(r)}.
$$

又因

$$
f=1-v^2/c^2,
$$

在 \(v(r_h)=c\) 处，

$$
v'(r_h)=-\frac{\kappa}{c}.
$$

所以

$$
c-v(r)
=
\frac{\kappa}{c}(r-r_h)
+
O((r-r_h)^2).
$$

积分的奇异部分为

$$
-\frac c\kappa\log(r(\tau)-r_h).
$$

代入发射者轨迹展开，即得式（36.1）；反解得到式（36.2）。∎

---

## 推论 36.1　无限接收时间不等于接收无限源历史

由式（36.2），

$$
\boxed{
\frac{d\tau}{dT_R}
\sim
\frac{\kappa A}{c}e^{-\kappa T_R/c}
\longrightarrow0.
}
\tag{36.3}
$$

若源钟相位为

$$
\phi_{\mathrm{src}}(\tau)=\omega_0\tau,
$$

则接收相位的瞬时频率为

$$
\boxed{
\omega_{\mathrm{rec}}
=
\omega_0\frac{d\tau}{dT_R}
\longrightarrow0.
}
\tag{36.4}
$$

因此，外部观察者越晚收到的信号，来自越接近 \(\tau_h\) 的那一小段源历史。

**它不是在有限自身时间里看到了源的无限未来。相反，源的一段有限历史被拉伸到越来越晚的接收时间。**

在黑洞情形中，边界之后的源事件并未通过这条向外通道继续抵达外部接收者。视界的全局因果性质不能用“最后一帧越来越慢”代替。([arXiv][6])

---

## 推论 36.2　保持固定时间分辨能力需要增长的局部资源

假设信号理想地携带源钟态

$$
|\chi(\tau)\rangle=e^{-iH_C\tau/\hbar}|\chi_0\rangle,
$$

且忽略损耗、额外噪声和传播引入的其他参数。

则关于接收时间的量子 Fisher 信息为

$$
\boxed{
\mathcal F_{T_R}
=
\frac{4(\Delta H_C)^2}{\hbar^2}
\left(\frac{d\tau}{dT_R}\right)^2.
}
\tag{36.5}
$$

若要求

$$
\mathcal F_{T_R}\ge F_*>0,
$$

则必须有

$$
\boxed{
\Delta H_C
\ge
\frac{\hbar\sqrt{F_*}}
{2|d\tau/dT_R|}.
}
\tag{36.6}
$$

在式（36.3）的情形中，该下界指数增长。

### 证明

式（36.5）由纯态量子 Fisher 信息的参数链式法则得到。整理不等式即得式（36.6）。∎

这不是任意时空测量的普遍能量下界，而是当前钟相位传输协议的限制。资源增长到足以产生显著反作用后，测试钟与固定背景近似也必须重新检查。

---

# 37．量子观察者自身的位置不确定性，如何限制近视界钟？

前文始终允许观察者是量子系统。因此，不能在需要时把它突然当作一个无限精确的位置点。

## 假设 37.1　准静态位置—钟模型

在外部近边界区域，取径向距离变量 \(\ell>0\)，并使用领先阶钟速

$$
N(\ell)=\frac{\kappa\ell}{c^2}.
$$

在一次短时、受控制的询问中，假设位置运动可忽略，钟与位置的有效耦合为

$$
\boxed{
H_{\mathrm{clock}}
=
N(\widehat\ell)\otimes H_C.
}
\tag{37.1}
$$

初态取位置态与钟态的乘积。记位置分布均值和方差为

$$
\ell_0=\langle\widehat\ell\rangle,
\qquad
\sigma_\ell^2
=
\langle(\widehat\ell-\ell_0)^2\rangle.
$$

该模型要求相应位置支持仍位于适用的外部近边界区域；不能让固定宽度波包任意跨过边界后仍沿用“静止钟”描述。

---

## 定理 37.1　相对钟速不确定性与位置宽度

有

$$
\overline N=\frac{\kappa\ell_0}{c^2},
$$

$$
\operatorname{Var}(N)
=
\frac{\kappa^2\sigma_\ell^2}{c^4},
$$

因而

$$
\boxed{
\frac{\sqrt{\operatorname{Var}(N)}}{\overline N}
=
\frac{\sigma_\ell}{\ell_0}.
}
\tag{37.2}
$$

对于钟的能级差 \(\Delta E\)，约化相干因子为

$$
\boxed{
\chi(T)
=
\int p(\ell)
e^{-i\Delta E\,N(\ell)T/\hbar}\,d\ell.
}
\tag{37.3}
$$

若二阶矩存在，则

$$
\boxed{
|\chi(T)|^2
=
1-
\left(\frac{\Delta E\,T}{\hbar}\right)^2
\frac{\kappa^2\sigma_\ell^2}{c^4}
+
o(T^2).
}
\tag{37.4}
$$

### 证明

前两式由 \(N\) 对 \(\ell\) 的线性关系得到。对位置自由度取偏迹，得到式（37.3）。

最后对特征函数在零点展开：

$$
|\langle e^{-iaN}\rangle|^2
=
1-a^2\operatorname{Var}(N)+o(a^2),
$$

取 \(a=\Delta E T/\hbar\) 即得。∎

### 一个重要细节

在坐标 \(r\) 下，

$$
\frac{d\sqrt f}{dr}
$$

在非退化边界附近发散；但在径向固有距离 \(\ell\) 下，

$$
\frac{dN}{d\ell}\sim\frac{\kappa}{c^2}
$$

有限。

所以，不能仅凭某个坐标导数发散，就宣布量子钟的绝对噪声必然无限大。

真正困难的是：**当平均钟速趋近零时，要保持固定的相对精度，位置分布必须相应收窄。**

---

## 推论 37.1　精确静止观察者极限的局域化代价

在额外的局部正则位置—动量模型中，若要求

$$
\frac{\sigma_\ell}{\ell_0}\le\epsilon,
$$

则由不确定性关系，

$$
\boxed{
\sigma_p
\ge
\frac{\hbar}{2\epsilon\ell_0}.
}
\tag{37.5}
$$

因此，当 \(\ell_0\to0^+\) 而相对精度 \(\epsilon\) 固定时，所需动量展宽无界增长。

这不自动给出某个普遍最小长度，也不自动证明新黑洞形成。它说明：**“无限接近边界且位置足够确定、钟速足够稳定”的观察者，不是可以忽略其量子资源和反作用的理想装置。**

量子参照系理论也要求把空间参照与内部钟共同当作物理系统，而不是在不同步骤中交替使用无不确定性的经典参照。([arXiv][7])

---

# 38．真正的黑洞边界必须对全部允许信号成立

局部双 null 膨胀率和全局事件视界必须分开。

## 定义 38.1　事件黑洞区

在具有适当未来无穷远 \(\mathscr I^+\) 的渐近平直时空中，定义

$$
\boxed{
\mathcal B
=
M\setminus J^-(\mathscr I^+).
}
\tag{38.1}
$$

这表示：从 \(\mathcal B\) 中的事件出发，不存在到达该未来无穷远的因果曲线。

局部俘获条件依靠有限邻域中的几何；事件黑洞区则依赖整体未来。两者不能在任意动态时空中不加条件地等同。([arXiv][2])

---

## 定理 38.1　低速模式的边界不自动是普遍视界

考虑允许多个有效传播锥的模型族。若某类模式的径向特征为

$$
\dot r_a=-v+c_a,
$$

则在 \(v=c_1\) 处，若存在

$$
c_2>c_1,
$$

就有

$$
\dot r_2=c_2-c_1>0.
$$

因此，该处只对第一类模式形成向外传播边界，而不是全部允许模式的共同边界。

### 证明

直接代入特征速度。∎

这正是上一轮共同光锥判据的物理意义：

> **只有证明全部相关传播模式具有相容的完整因果结构，才能把某个有效视界提升为普遍的物理视界。**

不能先忽略高频或隐藏模式，再依据低频停止传播宣布“空间已经被绝对吞噬”。

---

## 定理 38.2　局部量子隧穿不取消共同因果支持

设一个局域场方程在适当全局双曲区域内具有延迟 Green 算子 \(G_R\)，并满足

$$
\operatorname{supp}(G_RJ)
\subseteq
J^+(\operatorname{supp}J).
$$

若接收事件 \(x\) 不属于源支持的因果未来，则

$$
\boxed{
(G_RJ)(x)=0.
}
\tag{38.2}
$$

### 证明

由支持条件立即得到。∎

对于正常双曲波方程，这种因果支持性质具有严格的数学基础。([arXiv][8])

因此，穿过经典势垒的量子隧穿，与向共同因果锥之外传送可控制信号，是两种不同问题。

若源位于定义（38.1）的黑洞区，而接收者能够继续向 \(\mathscr I^+\) 传信，那么该源不能通过上述局域延迟过程影响这个接收者，否则由因果关系传递性就与黑洞区定义矛盾。

这里没有借此解决完整黑洞蒸发的信息问题；那涉及量子态、反作用、全局演化和可能的引力修正。**本定理仅说明：不能把一个非零隧穿振幅或量子关联，直接当成跨事件视界的可控信息通道。**

---

# 39．观察者与黑洞之间，什么才是可以证明的“对偶”？

“对偶”至少需要明确对象、映射及其保持的结构。仅有“一个向内、一个向外”的图像不够。

## 定理 39.1　源—读数对偶反转传播方向

设 \(P\) 是实场上的形式自伴正常双曲算子，并在选定的全局双曲时空上具有延迟、超前 Green 算子 \(G_R,G_A\)。

对紧支撑测试源 \(f\) 与读数函数 \(h\)，有

$$
\boxed{
\langle h,G_Rf\rangle
=
\langle G_Ah,f\rangle.
}
\tag{39.1}
$$

即

$$
\boxed{G_R^*=G_A.}
\tag{39.2}
$$

### 证明

令

$$
u=G_Rf,
\qquad
v=G_Ah.
$$

则

$$
Pu=f,\qquad Pv=h.
$$

利用全局双曲性和相应因果支持，可将积分限制在适当紧致的因果交叠区域。形式自伴性与分部积分给出

$$
\langle h,u\rangle
=
\langle Pv,u\rangle
=
\langle v,Pu\rangle
=
\langle G_Ah,f\rangle.
$$

∎

这是 Green 算子理论中的标准因果对偶关系：交换源与读数时，延迟与超前传播互换。([arXiv][9])

### 解释

观察者读取过去，与源影响未来，确实存在严格的配对关系。

但式（39.1）**没有把超前 Green 算子变成实际可以操作的未来信息接收器**。它是方程和边界条件之间的对偶，不是任意穿越时间的许可。

---

## 定理 39.2　时间反演将未来俘获变成过去俘获，而不是变成观察者

对度量（32.1）进行真正的时间定向反演，以

$$
\widetilde T=-T
$$

作为新的未来参数，则形式上有

$$
\widetilde v=-v.
$$

在原先 \(v>c\) 的区域，新未来方向中的两类径向速度为

$$
\frac{dr}{d\widetilde T}=v\pm c>0.
$$

因此原先的未来俘获区域变成反向的、过去俘获结构。

### 证明

代入

$$
dT=-d\widetilde T
$$

得到

$$
ds^2
=
-c^2d\widetilde T^2+
(dr-vd\widetilde T)^2+r^2d\Omega_2^2.
$$

重新指定 \(\widetilde T\) 增大的方向为未来，求 null 特征即可。∎

### 注 39.1

这里必须真正反转时间定向。若只是更换坐标名称，而保持原来的物理未来方向，就没有把黑洞变成别的对象。

在相应的完整几何延拓中，这种反向结构对应白洞方向，而不是某个量子观察者。

因此，当前能成立的区分是：

$$
\boxed{
\text{源与读数：延迟—超前对偶；}
}
$$

$$
\boxed{
\text{未来与过去俘获：黑洞—白洞方向反演；}
}
$$

$$
\boxed{
\text{观察者与黑洞：共享某些可达性与近视界结构，但尚非同一对象。}
}
$$

模理论还能给出可观测代数与交换子代数之间的反射，例如 \(J\mathcal AJ=\mathcal A'\)。在特定 Rindler 真空情形，它与楔区域反射及 boost 演化相联系；但仍不能仅凭这一关系推得任意观察者通过虫洞连接某个黑洞内部。([arXiv][10])

---

# 40．观察者—黑洞关系的条件性统一命题

## 定理 40.1　钟记录、时间读数与径向俘获的分层一致性

在本增订的假设下，下列命题同时成立。

**第一，历史压缩与物理时间消失不同。**

有限量子记忆只能完美区分有限个历史记录；局部记录合并不意味着完整等距过程删除了输入区别。

**第二，静止钟速与径向可达性由同一函数控制。**

在度量（32.1）的外部区域，

$$
\boxed{
\left(\frac{d\tau_{\mathrm{stat}}}{dT}\right)^2
=
g^{-1}(dr,dr)
=
-\frac{r^2}{4c^2}\theta_+\theta_-.
}
$$

**第三，临界点处失效的是静止观察者族，而不是全部时间演化。**

静止钟速趋零时，维持静止所需加速度发散；允许下落的类时观察者仍可在有限固有时间内跨过边界。

**第四，径向俘获不表示空间维数消失。**

它表示更大面积半径不再属于该区域中的未来因果选择。

**第五，有限源时间可以被映射到无限接收时间，但这不增加源历史的长度。**

在非退化边界附近，

$$
\tau_h-\tau\sim Ae^{-\kappa T_R/c},
$$

因此后续接收信号越来越集中于边界之前的有限源历史。

**第六，量子资源限制阻止把理想极限当成免费观察能力。**

固定时间分辨能力需要相应能量展宽；固定相对钟速精度需要相应位置局域化。接近边界时，测试装置的反作用不能无限期忽略。

**第七，共同事件视界必须限制全部允许的因果信号。**

局部记录丢失、特定模式停止传播、低频有效边界和真正的全局事件黑洞区，不是同一个概念。

### 证明

依次由定理 31.1—31.2、32.1、33.1—33.2、34.1、35.1—35.2、36.1 及其推论、37.1 和第 38 节得到。∎

---

## 与项目已有结构的衔接

这一轮最直接的项目对应不是再增加一个“吞噬量”，而是把已有角色用于不同层级：

$$
\boxed{
\mathsf{CUT}:
\text{历史或联合量子态如何变成当前记录};
}
$$

$$
\boxed{
\mathsf{FLOW}:
\text{钟、信号与参照沿哪些过程演化};
}
$$

$$
\boxed{
\mathsf{ADMIT}_{\mathrm{stat}}(r)
\iff f(r)>0:
\text{静止观察者何时具有类时实现};
}
$$

$$
\boxed{
\mathsf{ADMIT}_{\mathrm{escape}}:
\text{是否存在到指定接收目标的未来因果过程}.
}
$$

当前记录的 kernel、有限资源下的分辨能力，以及完整因果不可达性应分别计算。它们不能由同一个未经限定的“信息逃逸率”替代。

本次对径向逆度量、钟速—特征恒等式、双膨胀率恒等式及静止加速度进行了符号核验；新增综合命题尚未进行 Lean 编译。标准相对论结构与量子计量公式不在此作为原创发现申报，新增工作是将其组织成上述可检查的观察者接口与准入关系。

---

# 结论：怎样理解你的原始直觉？

“观察者吞噬时间”可以被精确拆成：

> **观察者把可访问的过去编码成当前记录；不同过程的时间变化，经过传播与参照比较后，以不同速率进入这些记录。**

“黑洞吞噬空间”可以被精确改写成：

> **在未来俘获区域内，原先可以选择的向外径向运动，不再是未来因果过程；空间中的某种方向自由转化成了未来演化的约束。**

两者最深的联系，不是“时间和空间分别被两个物体消灭”，而是：

$$
\boxed{
\text{钟能够怎样继续记录，}
\quad
\text{与信号能够向哪里继续传播，}
\quad
\text{受同一个因果结构约束。}
}
$$

在我们选定的球对称实现中，这个共同结构正由

$$
f(r)=1-\frac{v(r)^2}{c^2}
$$

体现。

当 \(f\to0^+\)，外部静止钟相对于参照时间的变化速率趋零，同时向外 null 分支停在临界位置。

当 \(f<0\)，不能继续说“这只静止钟的时间变成了虚数”。正确结论是：

$$
\boxed{
\text{原来的静止观察者已经不再满足物理准入条件。}
}
$$

观察者仍然可以存在、演化和记录，但必须沿允许的类时过程运动。

**因此，最值得保留的直觉不是“观察者就是黑洞”，而是：观察者的时间结构与世界的空间可达结构不能被分别定义。它们必须共同来自一个量子交互及其因果几何，而视界正是某一类观察者描述与行动方式达到边界的位置。**

[1]: https://arxiv.org/html/gr-qc/0411060v2 "https://arxiv.org/html/gr-qc/0411060v2"
[2]: https://arxiv.org/html/0804.4435v1 "https://arxiv.org/html/0804.4435v1"
[3]: https://davidtong.org/teaching/general-relativity/grhtml/S6.html "https://davidtong.org/teaching/general-relativity/grhtml/S6.html"
[4]: https://arxiv.org/html/1409.4057v2 "https://arxiv.org/html/1409.4057v2"
[5]: https://arxiv.org/abs/0710.5373 "https://arxiv.org/abs/0710.5373"
[6]: https://arxiv.org/html/1407.7295v3 "https://arxiv.org/html/1407.7295v3"
[7]: https://arxiv.org/html/2101.11628v2 "https://arxiv.org/html/2101.11628v2"
[8]: https://arxiv.org/html/1310.0738v2 "https://arxiv.org/html/1310.0738v2"
[9]: https://arxiv.org/html/2303.02993v2 "https://arxiv.org/html/2303.02993v2"
[10]: https://arxiv.org/html/1803.04993v6 "https://arxiv.org/html/1803.04993v6"
这次可以把上一轮的“逐个检查新增耦合”进一步推进：

**不必先求出临界点，也不必先假设低一阶已经全实根，就能直接用实际系数构造一张有限矩阵。它的负方向数，恰好等于对应 Jensen 多项式的非实共轭根对数。**

同时，还能证明一个与量子观察有关的限制：

> **给观察读数叠加独立的高斯噪声，只会平移这套有限模型的谱，不会改变新增耦合的符号，也不会修复任何高阶负方向。**

这把“普通统计波动”和“决定离线的不可约关联”分得更清楚。

下面继续采用定义、定理和证明。使用的 Bézout、Jensen 和实根判别原理属于经典数学；这里的工作是把它们与前文固定的实际 ξ 系数、量子累积量和回返耦合精确连接，而不是宣称发现了一套全新的通用实根理论。

---

# 一、固定对象：仍然研究实际 ξ，不重新挑选有利模型

采用标准归一化：

$$
\xi(s)=
\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
\qquad
\xi(s)=\xi(1-s).
$$

定义：

$$
\mathscr M(b)
=
\frac{\xi(\frac12+b)}{\xi(\frac12)}.
$$

这个函数具有前文使用的正 theta 概率表示：

$$
\mathscr M(b)=\int_{\mathbb R}e^{bx}\,d\nu(x),
$$

其中 \(\nu\) 是固定的正偶概率测度。归一化 ξ 的这种概率表示不需要 RH。([DLMF][1])

令：

$$
m_{2k}=\int x^{2k}\,d\nu(x),
\qquad
a_k=\frac{m_{2k}}{(2k)!}.
$$

于是：

$$
D(v)=\sum_{k\ge0}a_kv^k,
\qquad
D(b^2)=\mathscr M(b),
$$

并且：

$$
a_0=1,\qquad a_k>0.
$$

沿用有限多项式：

$$
P_d(v)=
\sum_{k=0}^d\frac{(d)_k}{d^k}a_kv^k,
$$

以及：

$$
\boxed{
q_d(x)=x^dP_d(-1/x).
}
\tag{C1}
$$

因此：

$$
q_d(x)
=
x^d-a_1x^{d-1}
+\frac{d-1}{d}a_2x^{d-2}
-\cdots
+(-1)^d\frac{d!}{d^d}a_d.
$$

前文的 Jensen 判据给出：

$$
\boxed{
\mathrm{RH}
\iff
q_d\text{ 的全部根为正实数，}\quad\forall d\ge1.
}
\tag{C2}
$$

经典 Jensen–Pólya 理论提供这一分析桥；有限次数的双曲性研究已有大量结果，不能把低阶核对等同于全阶证明。([arXiv][2])

由于 \(a_k>0\)，还有一个方便的事实：

$$
q_d(-x)\ne0\qquad(x\ge0).
$$

所以，对实际 \(q_d\) 而言：

$$
\boxed{
\text{全部根为实数}
\iff
\text{全部根为正实数}.
}
$$

---

# 二、先把上一轮的回返响应写成一个纯系数对象

## 定义 C1：导数多项式与回返分子

对 \(d\ge2\)，定义：

$$
\boxed{
r_d(x)=\frac1d q_d'(x),
\qquad
\mu_d=\frac{a_1}{d}.
}
$$

再定义：

$$
\boxed{
n_d(x)=(x-\mu_d)r_d(x)-q_d(x).
}
\tag{C3}
$$

因为最高两阶恰好抵消：

$$
\deg r_d=d-1,
\qquad
\deg n_d\le d-2.
$$

定义有理函数：

$$
\boxed{
\Sigma_d(x)
=
\frac{n_d(x)}{r_d(x)}
=
x-\mu_d-\frac{dq_d(x)}{q_d'(x)}.
}
\tag{C4}
$$

所有对象都能由 \(a_1,\ldots,a_d\) 直接计算，不需要根。

### 与上一轮耦合的关系

当 \(r_d\) 有互异实根 \(t_1,\ldots,t_{d-1}\) 时：

$$
\boxed{
\Sigma_d(x)=
\sum_{i=1}^{d-1}\frac{\eta_{d,i}}{x-t_i},
}
$$

其中：

$$
\boxed{
\eta_{d,i}
=
-\frac{d\,q_d(t_i)}{q_d''(t_i)}.
}
\tag{C5}
$$

若这些 \(\eta_{d,i}\ge0\)，它们才可以解释为普通正内积中的耦合平方：

$$
\Sigma_d(z)
=
g_d^\dagger(zI-C_d)^{-1}g_d.
$$

这里 \(C_d=\operatorname{diag}(t_i)\)，\(|g_{d,i}|^2=\eta_{d,i}\)。

并且当 \(\Im z>0\)：

$$
\boxed{
\Im\Sigma_d(z)
=
-(\Im z)
\sum_i\frac{\eta_{d,i}}{|z-t_i|^2}
\le0.
}
\tag{C6}
$$

所以，“所有耦合平方非负”同时也是这份指定回返函数的半平面符号约束。

反之，若某个 \(\eta_{d,i}<0\)，则在 \(t_i\) 附近：

$$
\Im\Sigma_d(t_i+i\varepsilon)
\sim-\frac{\eta_{d,i}}{\varepsilon}>0.
$$

**负耦合不是仅仅使总能量数值不漂亮，而是破坏了同一个自伴回返表示必须具有的解析符号。**

不过，上述部分分式表达暂时要求临界点互异且实。下一节会把这个限制也去掉。

---

# 三、核心构造：用一张系数矩阵替代全部临界点计算

## 定义 C2：回返 Bézout 核

定义：

$$
\boxed{
\mathcal B_d(x,y)
=
\frac{
r_d(x)n_d(y)-n_d(x)r_d(y)
}{
x-y
}.
}
\tag{C7}
$$

分子在 \(x=y\) 时为零，因此它是一个多项式，而不是真正带奇点的分式。

它对称于 \(x,y\)，并且每个变量的次数至多为 \(d-2\)。所以唯一存在一个实对称矩阵 \(B_d\)，满足：

$$
\boxed{
\mathcal B_d(x,y)
=
\mathbf v_{d-2}(x)^{\mathsf T}
B_d
\mathbf v_{d-2}(y),
}
$$

其中：

$$
\mathbf v_{d-2}(x)
=
(1,x,\ldots,x^{d-2})^{\mathsf T}.
$$

因此：

$$
\boxed{
B_d\in\mathbb R^{(d-1)\times(d-1)}
}
$$

是一个直接由实际系数计算的矩阵。

Bézout 矩阵与插值、交错和根位置之间的关系是经典工具；我们这里固定的是回返分子 \(n_d\) 与导数多项式 \(r_d\) 这一对。([arXiv][3])

---

## 定理 C1：有限负方向的精确计数

设 \(q_d\) 的互异非实共轭根对数为 \(N_{\mathbb C}(q_d)\)。那么：

$$
\boxed{
n_-(B_d)=N_{\mathbb C}(q_d),
}
\tag{C8}
$$

其中 \(n_-(B_d)\) 是负特征值个数。

因此：

$$
\boxed{
B_d\succeq0
\iff
q_d\text{ 的全部根为实数}.
}
\tag{C9}
$$

这个结论允许 \(q_d\) 有重根，也不要求先知道 \(q_d'\) 的根在哪里。

### 证明：第一步，将回返核加回一个正方向

定义完整 Bézout 核：

$$
\mathcal W_d(x,y)
=
\frac{
q_d(x)r_d(y)-q_d(y)r_d(x)
}{
x-y
}.
$$

代入：

$$
q_d(x)=(x-\mu_d)r_d(x)-n_d(x),
$$

得到：

$$
\boxed{
\mathcal W_d(x,y)
=
r_d(x)r_d(y)+\mathcal B_d(x,y).
}
\tag{C10}
$$

设：

$$
r_d(x)=x^{d-1}+\mathbf a^{\mathsf T}\mathbf v_{d-2}(x).
$$

那么完整核的系数矩阵为：

$$
W_d=
\begin{pmatrix}
B_d+\mathbf a\mathbf a^{\mathsf T}&\mathbf a\\
\mathbf a^{\mathsf T}&1
\end{pmatrix}.
$$

对右下角的 \(1\) 作精确 Schur 消元：

$$
\boxed{
W_d\ \text{合同于}\ B_d\oplus[1].
}
\tag{C11}
$$

所以：

$$
n_-(W_d)=n_-(B_d).
$$

### 证明：第二步，计算完整核的符号

设 \(q_d\) 的互异根为 \(\lambda_j\)，重数为 \(m_j\)。由：

$$
\frac{q_d'(x)}{q_d(x)}
=
\sum_j\frac{m_j}{x-\lambda_j},
$$

得到：

$$
\boxed{
\mathcal W_d(x,y)
=
\frac1d
\sum_jm_j
\frac{q_d(x)}{x-\lambda_j}
\frac{q_d(y)}{y-\lambda_j}.
}
\tag{C12}
$$

对实根 \(\lambda_j\)，对应一个正平方方向。

对非实共轭对，写：

$$
\frac{q_d(x)}{x-\lambda}=A(x)+iB(x),
$$

其中 \(A,B\) 为实多项式。与共轭项相加后：

$$
\boxed{
2\bigl[A(x)A(y)-B(x)B(y)\bigr].
}
$$

每一对贡献一正一负。

这些多项式方向线性独立：若

$$
\sum_jc_j\frac{q_d(x)}{x-\lambda_j}=0,
$$

除以 \(q_d(x)\)，得到一个具有不同简单极点的有理函数恒为零，故所有 \(c_j=0\)。

因此，每一对互异非实共轭根恰好产生一个负方向，实根不产生负方向。重根增加权重，但不增加同一个方向的独立性。

结合式（C11），得到式（C8）。证毕。

这也是 Hermite–Sylvester 实根判据的一种具体 Bézout 实现；一般的“实根当且仅当相关二次型正半定”属于经典理论。([arXiv][4])

---

## 推论：实际 RH 的新有限载体

由式（C2）：

$$
\boxed{
\mathrm{RH}
\iff
B_d\succeq0
\quad\forall d\ge2.
}
\tag{C13}
$$

与前文相比，区别不是又增加一个抽象等价，而是：

**\(B_d\) 可以通过多项式求导、乘法、除以 \(x-y\) 和提取系数直接得到，构造过程不需要求任何零点。**

而且，它准确保留“负方向有多少”，不只输出一个成功／失败标签。

这里计数的是有限 Jensen 多项式的非实根对，不是直接计数实际 ζ 的离线根。由有限失败推出 RH 失败，仍通过固定的 Jensen 分析桥完成。

---

# 四、原来的“可容纳区间”，变成一个单参数线性矩阵问题

上一轮我们写过：

$$
q_d(x)=R_d(x)+\beta_d,
$$

其中 \(R_d\) 由旧系数确定，实际新增常数为：

$$
\beta_d=(-1)^d\frac{d!}{d^d}a_d.
$$

固定旧系数，暂时把 \(\beta\) 当变量。

由于求导消掉常数，\(r_d\) 不随 \(\beta\) 改变。因此：

$$
n_{d,\beta}(x)=n_{d,0}(x)-\beta.
$$

代入式（C7）：

$$
\boxed{
B_d(\beta)=B_d(0)-\beta L_d,
}
\tag{C14}
$$

其中 \(L_d\) 是多项式

$$
\frac{r_d(x)-r_d(y)}{x-y}
$$

的系数矩阵。

所以，下一层合法的全部新增常数构成：

$$
\boxed{
\mathcal I_d
=
\{\beta:B_d(0)-\beta L_d\succeq0\}.
}
\tag{C15}
$$

## 定理 C2：\(\mathcal I_d\) 是闭区间，允许为空或退化

### 证明

对每个实向量 \(u\)，正半定性要求：

$$
u^{\mathsf T}B_d(0)u
-
\beta\,u^{\mathsf T}L_du
\ge0.
$$

这是关于 \(\beta\) 的一个闭半直线、整个实轴或空集。

所有这些条件的交是闭凸集；实轴上的闭凸集就是闭区间，允许无界、单点或空集。证毕。

这使上一轮的延拓问题变得更可操作：

$$
\boxed{
\text{旧系数确定一个矩阵区间，}
\quad
\text{实际高阶矩必须落在其中。}
}
$$

并不需要先显式算出全部临界点。

更重要的是，**实际 \(a_d\) 不能为了进入区间而调整**。它来自同一个 theta 核；若调整了，就换了函数。

---

# 五、把二阶的普通波动剥离后，所有谱障碍只依赖四阶及以上累积量

现在把 \(q_d\) 写成更适合量子统计的形式。

定义：

$$
\boxed{
\log\mathscr M(b)
=
\sum_{k\ge1}\frac{\chi_{2k}}{(2k)!}b^{2k}.
}
\tag{C16}
$$

于是：

$$
\log D(v)
=
\sum_{k\ge1}\frac{\chi_{2k}}{(2k)!}v^k,
\qquad
a_1=\frac{\chi_2}{2}.
$$

由定义直接得到系数提取公式：

$$
\boxed{
q_d(x)
=
\frac{d!}{d^d}
[z^d]\left(e^{dxz}D(-z)\right).
}
\tag{C17}
$$

令：

$$
x=y+\frac{a_1}{d}.
$$

则：

$$
\boxed{
q_d\!\left(y+\frac{a_1}{d}\right)
=
\frac{d!}{d^d}
[z^d]\!
\left[
e^{dyz}
\exp\left(
\sum_{k\ge2}
\frac{(-1)^k\chi_{2k}}{(2k)!}z^k
\right)
\right].
}
\tag{C18}
$$

### 结论

$$
\boxed{
q_d\text{ 的中心化形状只依赖 }
\chi_4,\chi_6,\ldots,\chi_{2d}.
}
\tag{C19}
$$

二阶累积量 \(\chi_2\) 只决定整体平移。

这不是说二阶统计不重要。它仍决定总迹和尺度。但是：

> **是否出现非实根，不由整体平移决定，而由去掉二阶平移后的高阶形状决定。**

式（C17）所属的 Appell／Jensen 生成函数结构是经典的；现代关于 Brenke、Appell 与 Laguerre–Pólya 类的工作也从这一类生成函数研究实根性。([arXiv][5])

---

# 六、继续到第四层：八阶累积量必须进入一个明确区间

前文已经处理二阶、三阶。这次继续一层。

由矩与累积量关系：

$$
\begin{aligned}
m_2&=\chi_2,\\
m_4&=\chi_4+3\chi_2^2,\\
m_6&=\chi_6+15\chi_4\chi_2+15\chi_2^3,\\
m_8&=\chi_8+28\chi_6\chi_2+35\chi_4^2
+210\chi_4\chi_2^2+105\chi_2^4.
\end{aligned}
$$

代入实际 \(q_4\)，再中心化：

$$
\boxed{
\widehat q_4(y)
:=
q_4\!\left(y+\frac{\chi_2}{8}\right)
=
y^4+py^2+qy+r,
}
\tag{C20}
$$

其中：

$$
\boxed{
p=\frac{\chi_4}{32},
\qquad
q=-\frac{\chi_6}{1920},
\qquad
r=\frac{\chi_4^2}{12288}
+\frac{\chi_8}{430080}.
}
\tag{C21}
$$

**二阶累积量完全消失了。**

这时：

$$
\widehat r_4(y)=\frac14\widehat q_4'(y)
=
y^3+\frac p2y+\frac q4,
$$

$$
\widehat n_4(y)
=
-\frac p2y^2-\frac{3q}{4}y-r.
$$

直接按定义 C2 构造矩阵：

$$
\boxed{
\widehat B_4=
\begin{pmatrix}
-\dfrac{pr}{2}+\dfrac{3q^2}{16}
&
\dfrac{pq}{8}
&
-r\\[2mm]
\dfrac{pq}{8}
&
\dfrac{p^2}{4}-r
&
-\dfrac{3q}{4}\\[2mm]
-r
&
-\dfrac{3q}{4}
&
-\dfrac p2
\end{pmatrix}.
}
\tag{C22}
$$

由定理 C1：

$$
\boxed{
\widehat B_4\succeq0
\iff
q_4\text{ 的全部根为正实数}.
}
\tag{C23}
$$

变量平移只对应多项式基底的可逆变化，不改变正负惯性。

因此，第四层可以直接通过一个由 \(\chi_4,\chi_6,\chi_8\) 构成的 \(3\times3\) 矩阵认证，**不需要先求 \(q_4\) 的根**。

仅检查行列式还不够；必须检查正半定性本身，或等价的全部主子式条件。

---

## 定理 C3：在三阶严格通过时，八阶累积量的允许区间

假设：

$$
\chi_4<0,
\qquad
3\chi_6^2<100(-\chi_4)^3.
$$

这保证：

$$
4y^3+2py+q
$$

有三个互异实根：

$$
t_1<t_2<t_3.
$$

定义：

$$
U_i=3t_i^4+pt_i^2.
$$

那么：

$$
\boxed{
q_4\text{ 全实根}
\iff
U_2\le r\le\min(U_1,U_3).
}
\tag{C24}
$$

### 证明

在临界点：

$$
4t_i^3+2pt_i+q=0.
$$

因此：

$$
\widehat q_4(t_i)
=
r-3t_i^4-pt_i^2
=
r-U_i.
$$

\(t_1,t_3\) 是局部极小点，\(t_2\) 是局部极大点。

四次首一多项式全实根，恰好要求：

$$
\widehat q_4(t_1)\le0,\qquad
\widehat q_4(t_2)\ge0,\qquad
\widehat q_4(t_3)\le0.
$$

这就是式（C24）。等号对应允许的重根。证毕。

由于 \(r\) 对 \(\chi_8\) 线性：

$$
\boxed{
430080\left(U_2-\frac{\chi_4^2}{12288}\right)
\le\chi_8
\le
430080\left(\min(U_1,U_3)-\frac{\chi_4^2}{12288}\right).
}
\tag{C25}
$$

这就是“实际八阶信息必须落入的区间”。

---

## 对实际 ξ 的数值核对

本轮直接从：

$$
\chi_{2k}
=
\left.
\frac{d^{2k}}{db^{2k}}
\log\xi\!\left(\frac12+b\right)
\right|_{b=0}
$$

计算，得到：

$$
\chi_8
\approx
-6.68335933695015\times10^{-6}.
$$

由实际 \(\chi_4,\chi_6\) 算出的允许区间为：

$$
\boxed{
-9.55559691188456\times10^{-6}
\le\chi_8
\le
-5.07049958917145\times10^{-6}.
}
$$

实际值在区间内。

相应三个候选耦合为：

$$
\eta_{4,1}\approx4.77080754678\times10^{-7},
$$

$$
\eta_{4,2}\approx1.20919662766\times10^{-6},
$$

$$
\eta_{4,3}\approx5.28358498365\times10^{-6}.
$$

它们全部为正，且精确满足总预算：

$$
\boxed{
\sum_{i=1}^{3}\eta_{4,i}
=
-\frac{\chi_4}{64}.
}
\tag{C26}
$$

我使用了 50 位与 90 位工作精度交叉核对，显示数字一致，并用符号展开检查了矩阵恒等式。

**这些是数值与代数核对，不是区间认证。四次 Jensen 双曲性本身也属于已有低阶研究范围；这里增加的是它与实际累积量、回返耦合的明确对应。**([arXiv][2])

---

# 七、一个更有物理意义的定理：独立高斯噪声不能修复任何负耦合

现在返回量子观察者。

令实际读数变量为 \(X\sim\nu\)。加入一个独立的高斯变量：

$$
G_\tau\sim N(0,\tau),
\qquad\tau\ge0,
$$

定义：

$$
X_\tau=X+G_\tau.
$$

则矩生成函数变为：

$$
\boxed{
\mathscr M_\tau(b)
=
e^{\tau b^2/2}\mathscr M(b).
}
\tag{C27}
$$

因此：

$$
\boxed{
D_\tau(v)=e^{\tau v/2}D(v).
}
\tag{C28}
$$

前面的指数因子处处非零，所以 \(D_\tau\) 与 \(D\) 的零点及重数完全相同。

在相位读数上：

$$
\mathscr M_\tau(it)
=
e^{-\tau t^2/2}\mathscr M(it).
$$

它会压低可见振幅，但不会在任何有限复点创造或删除零点。

## 定理 C4：每个有限 Jensen 层也只发生平移

用 \(D_\tau\) 的实际系数构造 \(q_d^{(\tau)}\)，则：

$$
\boxed{
q_d^{(\tau)}(x)
=
q_d\!\left(x-\frac{\tau}{2d}\right).
}
\tag{C29}
$$

### 证明

由式（C17）：

$$
\begin{aligned}
q_d^{(\tau)}(x)
&=
\frac{d!}{d^d}
[z^d]\left(e^{dxz}D_\tau(-z)\right)\\
&=
\frac{d!}{d^d}
[z^d]\left(e^{dxz-\tau z/2}D(-z)\right)\\
&=
q_d\!\left(x-\frac{\tau}{2d}\right).
\end{aligned}
$$

证毕。

因此，每个根都加上同一个实数：

$$
\lambda_j^{(\tau)}
=
\lambda_j+\frac{\tau}{2d}.
$$

非实部分完全不变。

当临界点简单时：

$$
t_i^{(\tau)}
=
t_i+\frac{\tau}{2d},
$$

并且：

$$
\boxed{
\eta_{d,i}^{(\tau)}
=
-\frac{
d\,q_d^{(\tau)}(t_i^{(\tau)})
}{
(q_d^{(\tau)})''(t_i^{(\tau)})
}
=
\eta_{d,i}.
}
\tag{C30}
$$

也就是说：

$$
\boxed{
\text{增加独立高斯波动，
不会改变任何一条候选耦合平方。}
}
$$

即使遇到重根，式（C29）仍然成立；对应的 \(B_d\) 仅作可逆基变换，负惯性保持不变。

### 它与前文的“高斯筛选”不是同一个操作

这里是：

$$
\nu\longmapsto\nu*N(0,\tau),
$$

即增加独立波动。

之前的后选择则是：

$$
d\nu_a(x)\propto e^{-ax^2}d\nu(x),
$$

即根据原读数重新加权。

前者乘上无零指数因子；后者一般改变整个零点集合。

**两个操作都带“高斯”二字，但在零点几何上完全不同。**

这也回应你之前“更经典、更统计”的直觉：有些普通噪声只改变背景方差，真正决定离线的高阶关联却保持原样。

---

# 八、欧拉常数与这份高阶障碍之间，还存在一个不变量

沿用：

$$
c=\frac{\xi'(1)}{\xi(1)}
=
1+\frac{\gamma_{\mathrm E}}2-\frac12\log4\pi.
$$

这来自 ζ 在 \(s=1\) 的 Laurent 有限部分与 digamma 特殊值，不是可调参数。([DLMF][6])

在上述高斯扩展中：

$$
a_1^{(\tau)}=a_1+\frac{\tau}{2},
$$

以及：

$$
\frac{D_\tau'(1/4)}{D_\tau(1/4)}
=
c+\frac{\tau}{2}.
$$

因此：

$$
\boxed{
a_1^{(\tau)}-c^{(\tau)}
=
a_1-c.
}
\tag{C31}
$$

所以前文的整体回返差额：

$$
4(a_1-c)
$$

对这种高斯扩展保持不变。

这与式（C30）相呼应：新增方差整体移动谱，但不修复内部耦合的符号，也不改变这个特定差额。

然而必须强调，\(c^{(\tau)}\) 不再是原始 ξ 的欧拉常数校准值。

例如定义：

$$
\boxed{
\xi_\tau(s)
=
e^{\tau s(s-1)/2}\xi(s).
}
$$

它仍然满足反射关系、仍有同样的零点，并且：

$$
\xi_\tau(0)=\xi_\tau(1)=\frac12.
$$

但：

$$
\frac{\xi_\tau'(1)}{\xi_\tau(1)}
=
c+\frac{\tau}{2}.
$$

因此，欧拉校准能检测：

$$
\text{“你已经换了函数”},
$$

而零点不变量说明：

$$
\text{“这次换函数没有改变零点”}.
$$

**保真检查与零点检查不是同一件事。两者都需要，但不能互相替代。**

---

# 九、为什么“正量子态”不能自动证明 \(B_d\succeq0\)？

因为 \(B_d\) 不是把原来的概率直接写成 Gram 矩阵。

它先经过：

$$
\text{矩}
\longrightarrow
\text{累积量与 Jensen 系数}
\longrightarrow
\text{多项式乘除}
\longrightarrow
\text{Bézout 核}.
$$

其中存在有意义的减法。

最低阶已经说明这一点。

对 \(d=2\)：

$$
q_2(x)=x^2-a_1x+\frac{a_2}{2},
$$

得到：

$$
\boxed{
B_2=
\left[
\frac{a_1^2}{4}-\frac{a_2}{2}
\right]
=
\left[-\frac{\chi_4}{48}\right].
}
\tag{C32}
$$

普通概率正性保证：

$$
m_4\ge m_2^2,
$$

但 \(B_2\ge0\) 要求：

$$
m_4\le3m_2^2.
$$

这是另一个方向的约束。

例如，取合法的对称三点分布：

$$
\Pr(X=0)=0.9,
\qquad
\Pr(X=1)=\Pr(X=-1)=0.05.
$$

则：

$$
m_2=m_4=0.1,
$$

$$
\chi_4=0.1-3(0.1)^2=0.07>0,
$$

所以：

$$
B_2<0.
$$

这个概率分布完全合法，也能表示成量子纯态在对角可观测量上的分布。它却不满足我们需要的零点正性。

因此：

> **构造正量子态只是第一层；证明实际算术态的不可约关联通过全部 \(B_d\) 测试，是另一项实质工作。**

这也阻止一个循环证明：不能先把 \(B_d\) 定义成某个自由选择的 \(A_d^\dagger A_d\)，再宣布它等于实际系数矩阵。**等式本身才是要证明的桥。**

---

# 十、现在怎样把它变成严格的有限计算？

对固定 \(d\)，计算路径可以完全写成：

$$
\boxed{
a_0,\ldots,a_d
\longrightarrow
q_d
\longrightarrow
r_d,n_d
\longrightarrow
B_d.
}
$$

不需要先定位任何根。

若已得到近似矩阵 \(\widetilde B_d\)，并严格认证每个元素的误差不超过 \(\varepsilon\)，那么矩阵维数为 \(d-1\)，故：

$$
\|B_d-\widetilde B_d\|_{\mathrm{op}}
\le(d-1)\varepsilon.
$$

因此：

$$
\boxed{
\lambda_{\min}(\widetilde B_d)>(d-1)\varepsilon
\Longrightarrow
B_d>0.
}
\tag{C33}
$$

反方向，若存在实向量 \(u\)，满足：

$$
\boxed{
u^{\mathsf T}\widetilde B_du
+
\varepsilon\|u\|_1^2<0,
}
\tag{C34}
$$

就严格得到：

$$
u^{\mathsf T}B_du<0.
$$

由定理 C1，该实际 \(q_d\) 有非实根；再由 Jensen 判据，RH 不成立。

如果误差跨过零，结果只能是未定。

这项程序并不声称很低成本。高阶系数、矩阵基底与小主子式可能非常病态。可以换基改善条件数，但必须同时运输误差与二次型，不能把换基后的数值稳定误认成原问题的正性已经证明。

---

# 十一、与项目的精确连接及剩余目标

本轮沿用前文固定快照，重新读取了相关模块，而没有更改文件。

`JensenPolynomialObstruction.lean` 已经定义有限 Jensen 多项式与实根谓词，但它的分析桥仍作为显式前件。它没有无条件供应实际全阶双曲性。

`SchurComplementAssociativity.lean` 证明了给定逆算子前件时，分步消元与一次消元一致。它能支持回返解释，但不自动证明本轮 \(B_d\) 的正性。

现在最集中的待证命题是：

$$
\boxed{
\forall d\ge2,\qquad
B_d\bigl(a_1,\ldots,a_d\bigr)\succeq0,
}
\tag{C35}
$$

其中每个：

$$
a_k=
\frac1{(2k)!\xi(1/2)}
\int_{\mathbb R}x^{2k}\Phi(x)\,dx
$$

都由实际 theta 核固定。

一个有证明力量的新结构，应当从实际 theta 的模关系、质数尺度操作或跨模式耦合中，推出：

$$
u^{\mathsf T}B_du\ge0
$$

对所有 \(d,u\) 成立。

或者，找到一个带严格误差界的有限负证书。

**本轮完成的是系数矩阵构造、负惯性计数、四阶显式条件，以及高斯扩展不改变障碍的证明；没有完成式（C35）的全阶算术正性。**

---

## 收束

这次把前文推进成了一个更精确的层次：

$$
\boxed{
\text{实际高阶统计}
\longrightarrow
\text{回返 Bézout 矩阵}
\longrightarrow
\text{正耦合是否可能}
\longrightarrow
\text{有限零点定位}.
}
$$

其中：

$$
\boxed{
n_-(B_d)
=
\text{第 }d\text{ 个实际 Jensen 多项式的非实共轭根对数}.
}
$$

因此，负方向不再只是某种抽象“不协调”，而有明确的有限谱含义。

另一方面：

$$
\boxed{
\text{独立高斯噪声}
\longrightarrow
\chi_2\text{ 改变、谱整体平移},
}
$$

但：

$$
\boxed{
\chi_4,\chi_6,\ldots
\text{ 不变，候选耦合符号不变}.
}
$$

这使你的“经典统计与不可约关系”的区分获得了一个严格版本：

> **普通背景波动可以被增加、平滑和重标定；决定正实现能否存在的高阶关系，却不能靠这些操作修复。**

欧拉常数负责校准实际对象的端点响应；Fibonacci 链负责把已经证明的正耦合实现为局部结构；量子观察者负责读取对应振幅。**真正还需要算术来承担的，是这些高阶关系为什么在每一个有限层都不要求负的耦合平方。**

[1]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[2]: https://arxiv.org/abs/1902.07321 "https://arxiv.org/abs/1902.07321"
[3]: https://arxiv.org/abs/1207.2434 "https://arxiv.org/abs/1207.2434"
[4]: https://arxiv.org/abs/1911.01745 "https://arxiv.org/abs/1911.01745"
[5]: https://arxiv.org/abs/2405.18940 "https://arxiv.org/abs/2405.18940"
[6]: https://dlmf.nist.gov/25.2 "https://dlmf.nist.gov/25.2"
# 历史记忆、径向时间与霍金辐射

## ——量子观察者—关系时空理论第四十一至第五十节增订

**你的表述可以发展成一套严格的对应，但其中需要区分三条不同的生成关系：**

$$
\boxed{
\text{可访问的交互历史}
\longrightarrow
\text{观察者中的记忆关联};
}
$$

$$
\boxed{
\text{黑洞的因果结构}
\longrightarrow
\text{径向变量获得时间定向};
}
$$

$$
\boxed{
\text{因果传播结构}+\text{量子场态}
\longrightarrow
\text{内外模式关联与霍金辐射}.
}
$$

这三条关系能够接入同一个理论，但不能简化成“时间被消耗后变成记忆，空间被消耗后变成时间和辐射”。

本增订的核心，是给出它们之间真正可证明的联系，并明确区分：

$$
\text{保存了某段历史的信息},
\qquad
\text{具有纠缠熵},
\qquad
\text{发出了能量}.
$$

三者相关，却不等价。

---

# 41．记忆的本质是保存历史之间的区别，而不是吸收一种“时间物质”

## 定义 41.1　历史—记忆状态

设 \(X\) 是一组已经明确区分的交互历史标签，概率为 \(p_x\)。观察者对历史 \(x\) 形成记忆态

$$
\rho_M^x.
$$

历史与记忆的联合状态为

$$
\boxed{
\rho_{XM}
=
\sum_xp_x|x\rangle\langle x|
\otimes\rho_M^x.
}
\tag{41.1}
$$

这里的 \(X\) 是所研究的历史变量，不表示所有互不相容的量子实验结果都预先具有经典值。

定义记忆中保存的历史信息为

$$
\boxed{
I(X:M)
=
S\!\left(\sum_xp_x\rho_M^x\right)
-
\sum_xp_xS(\rho_M^x),
}
\tag{41.2}
$$

其中

$$
S(\rho)=-\operatorname{Tr}(\rho\log\rho)
$$

采用自然对数，暂不乘 \(k_B\)。

---

## 定理 41.1　高熵不等于有记忆

若全部历史产生相同记忆态：

$$
\rho_M^x=\sigma_M
\qquad\forall x,
$$

则

$$
\boxed{I(X:M)=0.}
\tag{41.3}
$$

即使

$$
\sigma_M=\frac{I}{d},
\qquad
S(\sigma_M)=\log d,
$$

结论仍然成立。

### 证明

代入式（41.2）：

$$
I(X:M)=S(\sigma_M)-\sum_xp_xS(\sigma_M)=0.
$$

∎

因此，记忆不是“内部变得复杂”或“熵增加”本身。

**记忆的必要内容是：不同的过去，在当前留下不同且可利用的记录。**

仓库的 `TwoTimeKnowledge.lean` 已经以接口纤维定义“知道”：目标事件的值必须在当前观察接口的每条纤维上恒定。它还明确构造了“事件仍然存在，但观察者后来不能再区分它”的遗忘实例。这个结构与式（41.1）—（41.3）的区分方向一致。

---

## 定理 41.2　观察者的记忆不由时间长度单独决定

固定任意持续时间 \(T>0\)。存在两种合法量子过程：

一种使

$$
I(X:M)=0;
$$

另一种使有限组可区分历史被完美写入记忆。

### 证明

第一种过程对记忆实施恒等操作，且记忆初态与 \(X\) 独立。

第二种过程对一组正交历史输入实施

$$
|x\rangle|0\rangle_M
\longmapsto
|x\rangle|m_x\rangle_M,
$$

其中 \(\langle m_x|m_y\rangle=\delta_{xy}\)。

通过选择不同的控制 Hamiltonian 或等待区间，可以把这两种过程放入相同总持续时间 \(T\)。第一种没有建立历史—记忆关联，第二种可以建立。∎

所以：

$$
\boxed{
\text{经历了多少时间}
\not\Rightarrow
\text{形成了多少记忆}.
}
$$

“观察者吞噬时间形成记忆”的可保留版本是：

> **观察者把一部分可访问的时序区别，转译成当前可读的物理关联。**

记录过程可能需要能量和资源，但不能从“形成记忆”本身推出某个固定热谱，更不能直接推出霍金辐射。测量、信息擦除和完整循环的热力学成本必须分别计算。([arXiv][1])

---

# 42．“空间形成内部时间”的准确含义：径向变量变成未来演化的单调量

以下明确选择经典 Schwarzschild 黑洞内部作为几何实现，不把结论推广到所有旋转、带电或量子修正黑洞。

设

$$
r_s=\frac{2GM}{c^2},
\qquad
f(r)=1-\frac{r_s}{r}.
$$

在避开视界坐标奇性的区域，度量可写为

$$
\boxed{
ds^2
=
-f(r)c^2dt^2
+
\frac{dr^2}{f(r)}
+
r^2d\Omega_2^2.
}
\tag{42.1}
$$

这一几何及其穿视界延拓是标准 Schwarzschild 结构。([David Tong][2])

---

## 定理 42.1　面积半径在黑洞内部具有类时梯度

在

$$
0<r<r_s
$$

内，

$$
\boxed{
g^{-1}(dr,dr)=f(r)<0.
}
\tag{42.2}
$$

因此，\(r=\mathrm{const}\) 的超曲面为空间性超曲面。选定黑洞而非白洞的未来方向后，每条未来指向因果曲线都满足

$$
dr<0.
$$

从而

$$
\boxed{
T_{\mathrm{rad}}=-\frac rc
}
\tag{42.3}
$$

是该内部区域中的一个时间函数。

### 证明

式（42.2）由逆度量直接得到。

非零类时梯度与任意未来因果切向量的配对具有固定符号；在黑洞未来方向上，其符号由向内的未来径向光线确定为负。因此 \(r\) 沿全部未来因果曲线严格减小。∎

### 解释

外部观察者可以选择“向更大半径”或“向更小半径”运动。

内部的特殊之处是：

$$
\boxed{
\text{更小半径不再只是一个空间选项，
而成为全部未来过程共同满足的方向。}
}
$$

这可以称为**径向时间化**。

但它不是新增加了第二个时间维度，也不是把三维空间烧掉后制造时间。度量仍然具有一个时间方向；发生变化的是哪个变量可以承担时间函数的角色。

---

## 定理 42.2　径向时间化不意味着无限的内部生命期

在经典 Schwarzschild 黑洞内部，任意从视界进入并向 \(r=0\) 延续的类时轨迹，其固有时间满足

$$
\boxed{
\Delta\tau
\le
\frac{\pi GM}{c^3}.
}
\tag{42.4}
$$

### 证明

在内部令

$$
a(r)=\frac{r_s}{r}-1>0.
$$

度量为

$$
ds^2
=
a(r)c^2dt^2
-
\frac{dr^2}{a(r)}
+
r^2d\Omega_2^2.
$$

对类时轨迹，

$$
c^2d\tau^2
=
\frac{dr^2}{a(r)}
-
a(r)c^2dt^2
-
r^2d\Omega_2^2
\le
\frac{dr^2}{a(r)}.
$$

由于 \(r\) 单调减小，

$$
\Delta\tau
\le
\frac1c
\int_0^{r_s}
\sqrt{\frac r{r_s-r}}\,dr
=
\frac{\pi r_s}{2c}
=
\frac{\pi GM}{c^3}.
$$

∎

该结论属于经典 Schwarzschild 几何，不决定接近奇点时的量子引力演化。

因此，**“黑洞形成内部时间”不能被理解成“黑洞里面自动产生一个无限长的宇宙历史”。**

---

# 43．径向时间化本身还不能推出霍金辐射

这里需要加入此前没有包含在纯因果几何中的内容。

## 假设 43.1　半经典辐射模型

采用以下条件：

* 一个形成后趋于非退化静态黑洞的背景；
* 在该背景上传播的自由量子场；
* 一个适当的入射真空或具有相应正则性的初态；
* 由已标定的远处时钟定义入射与出射频率；
* 先研究忽略反向散射的径向二维近似。

霍金计算涉及的是**传播前后的正频率分解之间的关系**，而不是仅对一个经典度量重新命名。标准推导可以在外部量子场传播中完成，不要求把内部解释成一个主动向外发信的观察者。([arXiv][3])

---

## 定义 43.1　射线时间映射

令 \(U\) 为入射信号的仿射时间标签，\(u\) 为远处出射接收时间。

传播建立映射

$$
\boxed{
U=p(u).
}
\tag{43.1}
$$

非退化视界的晚时传播具有指数形式

$$
\boxed{
p(u)=U_H-Ae^{-\lambda u},
\qquad
\lambda=\frac{\kappa}{c}>0.
}
\tag{43.2}
$$

这里 \(\kappa\) 是按远处时间归一化的表面引力。

在真实坍缩模型中，式（43.2）是晚时渐近关系；涉及能流时，还需要控制相应导数的渐近，而不只控制函数值。

该指数关系来自向外信号在视界附近的对数传播延迟，并非“内侧物体把一串信息主动穿过视界发出来”。([arXiv][3])

---

## 定理 43.1　指数时间映射给出热关联形式

在上述二维自由场模型中，导数场二点关联的几何因子为

$$
\mathcal C_p(u,u')
=
\frac{p'(u)p'(u')}
{\bigl[p(u)-p(u')\bigr]^2}.
$$

对式（43.2），有

$$
\boxed{
\mathcal C_p(u,u')
=
\frac{\lambda^2}
{4\sinh^2\!\left[\lambda(u-u')/2\right]}.
}
\tag{43.3}
$$

### 证明

由

$$
p'(u)=A\lambda e^{-\lambda u},
$$

以及

$$
p(u)-p(u')
=
2A e^{-\lambda(u+u')/2}
\sinh\!\left[\lambda(u-u')/2\right],
$$

直接代入得到。∎

配上入射真空给出的正确 Wightman 边界值与解析性，这一关联满足热态的 KMS 条件，温度为

$$
\boxed{
T_H
=
\frac{\hbar\lambda}{2\pi k_B}
=
\frac{\hbar\kappa}{2\pi ck_B}.
}
\tag{43.4}
$$

等价的模式计算给出 Bose 占据数

$$
\boxed{
\bar n_\omega
=
\frac1{e^{2\pi\omega/\lambda}-1}.
}
\tag{43.5}
$$

这里采用的是标准半经典霍金机制，不是由虚时间周期这一条形式性质单独断言热性。([arXiv][3])

### 项目上的重要边界

仓库的 `GoldenHawkingTemperatureNormalization.lean` 已构造一个明确反例：同样的尺度数据，在不同的物理时间归一化下产生不同温度。

所以，**某个比例、指数或黄金尺度本身不能唯一决定霍金温度；必须保留实际钟标定。**

---

## 注 43.1　相同几何不自动给出相同净辐射

在相应静态黑洞外部：

Hartle–Hawking 平衡态具有相平衡的入射、出射热成分，不描述无入射补偿的持续净蒸发。

描述坍缩黑洞晚时辐射的 Unruh 态，则具有不同的入射与出射条件。

因此：

$$
\boxed{
\text{几何}+\text{量子场态}+\text{边界条件}
}
$$

共同决定净能流。仅知道“内部径向变量成为时间”，还不能确定辐射。([Springer][4])

---

# 44．霍金热态可以表现为内外模式的量子关联

为避免把无限连续模式的全部技术问题隐藏起来，本节先研究一个理想的、已正规化的外侧模式及其伙伴模式。

## 定义 44.1　单模式对的纯化态

对 \(\omega>0\)，令

$$
q_\omega=e^{-2\pi\omega/\lambda},
\qquad 0<q_\omega<1.
$$

定义

$$
\boxed{
|\Psi_\omega\rangle
=
\sqrt{1-q_\omega}
\sum_{n=0}^{\infty}
q_\omega^{n/2}
|n\rangle_R|n\rangle_B.
}
\tag{44.1}
$$

\(R\) 表示外侧模式，\(B\) 表示在该分解中未被外侧访问的伙伴模式。

这是玻色两模式压缩态的标准形式。它是理想霍金模式关联的一种实现；真实四维传播还包含灰体散射和更完整的模式结构。([arXiv][5])

---

## 定理 44.1　外侧约化态为 Gibbs 态

有

$$
\boxed{
\rho_R
=
(1-q_\omega)
\sum_{n=0}^{\infty}
q_\omega^n|n\rangle\langle n|.
}
\tag{44.2}
$$

若

$$
H_R=\hbar\omega N_R,
$$

则

$$
\boxed{
\rho_R
=
\frac{e^{-\beta_HH_R}}
{\operatorname{Tr}e^{-\beta_HH_R}},
\qquad
\beta_H=\frac1{k_BT_H}.
}
\tag{44.3}
$$

### 证明

对 \(B\) 取偏迹，正交性消去所有 \(n\ne m\) 项，得到式（44.2）。

再使用

$$
q_\omega=e^{-\beta_H\hbar\omega}
$$

即可。∎

其平均粒子数为

$$
\langle N_R\rangle
=
\frac{q_\omega}{1-q_\omega},
$$

与式（43.5）一致。

---

## 推论 44.1　热态的模生成元与外侧能量成比例

由式（44.3），

$$
\boxed{
-\log\rho_R
=
\beta_HH_R+\log Z_\omega\,I.
}
\tag{44.4}
$$

因此，该热态定义的模生成元与外侧 Hamiltonian 相容。

但这里出现了三种不同的“时间”：

$$
\text{内部观察者的固有时间},
$$

$$
\text{黑洞内部的径向时间函数},
$$

$$
\text{由状态与可观测代数定义的模流参数}.
$$

式（44.4）只说明在这个热态中，模生成元与外侧能量生成元之间存在比例。**它没有把这三种时间自动识别为同一个量。**

---

## 注 44.1　偏迹不是辐射的动力学原因

对任意纠缠态取偏迹，都可能得到混合态。

但“混合”本身不说明存在向无穷远流出的能量。

霍金辐射的实际内容还包括：

$$
\langle N_\omega^{\mathrm{out}}\rangle\ne0,
$$

以及相对于指定场态与参照时间的非零能流。

因此，不能用

$$
\text{看不到内部}\Rightarrow\text{外部一定发热}
$$

替代第 43 节的场传播和模式混合计算。

---

# 45．最直接的统一关系：时间映射、纠缠熵与能流

这一节把你的直觉推进到一个真正的等式。

## 假设 45.1　二维共形场与参照真空

取二维共形场，其中心荷记为 \(\nu>0\)，避免与光速 \(c\) 混淆。

设射线映射 \(p(u)\) 光滑且

$$
p'(u)>0,
$$

并在早时与入射仿射标定相容。

定义截至出射时间 \(u\) 的**真空扣除纠缠熵**

$$
\mathcal S(u).
$$

它不是裸的连续场熵，也不是某个有限记忆装置中保存的经典比特数。

在该共形真空模型中，

$$
\boxed{
\mathcal S(u)
=
-\frac{\nu}{12}\log p'(u),
}
\tag{45.1}
$$

而重整化能流为

$$
\boxed{
\mathcal F(u)
=
-\frac{\hbar\nu}{24\pi}\{p,u\},
}
\tag{45.2}
$$

其中

$$
\{p,u\}
=
\frac{p'''}{p'}
-\frac32\left(\frac{p''}{p'}\right)^2.
$$

这些是已有二维共形场结果，不是本会话首次发现。它们的严格适用条件包括选定的场态、真空扣除与射线映射模型。

---

## 定理 45.1　纠缠熵—能流恒等式

在假设 45.1 下，

$$
\boxed{
\mathcal F(u)
=
\frac{\hbar}{2\pi}
\left[
\frac6\nu\bigl(\mathcal S'(u)\bigr)^2
+
\mathcal S''(u)
\right].
}
\tag{45.3}
$$

### 证明

令

$$
a(u)=\frac{p''(u)}{p'(u)}.
$$

则

$$
\mathcal S'=-\frac{\nu}{12}a,
$$

以及

$$
\mathcal S''
=
-\frac{\nu}{12}
\left(
\frac{p'''}{p'}-a^2
\right).
$$

因此

$$
\frac6\nu(\mathcal S')^2+\mathcal S''
=
-\frac{\nu}{12}
\left(
\frac{p'''}{p'}-\frac32a^2
\right).
$$

乘以 \(\hbar/(2\pi)\) 即得。∎

### 对指数映射的推论

若局部或晚时受控渐近为

$$
p'(u)=A\lambda e^{-\lambda u},
$$

则

$$
\boxed{
\mathcal S'(u)=\frac{\nu\lambda}{12},
}
\tag{45.4}
$$

并且

$$
\boxed{
\mathcal F(u)
=
\frac{\hbar\nu\lambda^2}{48\pi}.
}
\tag{45.5}
$$

因此，在这个模型中：

$$
\boxed{
\text{入射时间相对于出射时间的指数压缩}
}
$$

同时表现为

$$
\boxed{
\text{出射区与其补集之间的纠缠积累}
}
$$

和

$$
\boxed{
\text{正的热能流}.
}
$$

这正是你的直觉中能够被严格保留的核心联系。

但式（45.1）的 \(\mathcal S\) 仍然不是“黑洞记住了多少个人经历”。它衡量的是指定场态和区域划分下的、相对真空的纠缠结构。

---

# 46．霍金辐射是否就是黑洞“吐出的记忆”？

仅凭热谱或纠缠熵，不能得到这个结论。

必须重新引入“究竟是哪一段历史被记住”的标签。

## 定义 46.1　辐射对落入历史的记忆能力

令 \(X\) 区分若干初始历史，例如具有相同宏观质量、角动量和电荷，但微观制备不同的输入。

对每个历史，外侧辐射态为

$$
\rho_R^x.
$$

定义

$$
I(X:R)
=
S\!\left(\sum_xp_x\rho_R^x\right)
-
\sum_xp_xS(\rho_R^x).
$$

它衡量辐射对这些输入历史保留了多少区别。

---

## 定理 46.1　相同热态不保存所选输入历史

若

$$
\rho_R^x=\rho_{\mathrm{th}}
\qquad\forall x,
$$

则

$$
\boxed{I(X:R)=0.}
\tag{46.1}
$$

任何仅接收 \(R\)、且初始时与 \(X\) 无关的探测器，也不能从中产生关于 \(X\) 的新记忆。

### 证明

第一项由定理 41.1 得到。

若探测器过程为量子通道 \(\mathcal D\)，则

$$
\rho_M^x=\mathcal D(\rho_{\mathrm{th}})
$$

对全部 \(x\) 相同，所以其历史信息也为零。∎

### 一个完全自洽的例子

定义等距过程：

$$
\boxed{
V|x\rangle_L
=
|x\rangle_{B_0}
\otimes
|\Psi_\omega\rangle_{RB_1}.
}
\tag{46.2}
$$

它可以让外侧 \(R\) 呈现相同热态，同时把原输入完整保存在 \(B_0\)。

所以：

$$
\boxed{
\text{发出了高熵辐射}
\not\Rightarrow
\text{原输入信息已经向外转移}.
}
$$

量子无隐藏定理进一步限制了如何在一个完全酉模型中把任意输入信息从某个子系统消除：不能任意宣称信息既不在外侧、也不在其补系统，却只藏在两者无法利用的关联中。([arXiv][6])

---

## 定理 46.2　原输入信息的内外平衡恒等式

设初始输入 \(L\) 与参照系统 \(A\) 处于纯态，经等距映射

$$
V:L\to B\otimes R
$$

后，\(ABR\) 仍为纯态。假设相关熵有限，则

$$
\boxed{
I(A:R)+I(A:B)=2S(A).
}
\tag{46.3}
$$

### 证明

纯态给出

$$
S(AR)=S(B),
\qquad
S(AB)=S(R).
$$

因此

$$
I(A:R)=S(A)+S(R)-S(B),
$$

$$
I(A:B)=S(A)+S(B)-S(R).
$$

相加即得。∎

### 解释

式（46.3）与单独的

$$
S(R)
$$

不同。

\(S(R)\) 可以因为辐射与内部纠缠而增加，却不因此证明辐射已经获得更多关于输入的区别。

如果最终全部输入相关的剩余系统 \(B\) 都进入一个固定、与输入无关的纯态，而完整过程仍等距，那么输入信息必须保留在完整辐射系统中。

但它可以出现在**不同辐射片段之间的联合关联**中，未必表现为每个单独模式的非热修正。

因此，“霍金辐射形成外侧记忆”至少有两种含义：

**探测器记住了自己收到哪些辐射结果**，可以直接实现。

**辐射保存了形成黑洞的全部输入历史**，则需要进一步的完整动力学与恢复证明。

二者不能混称。

---

# 47．辐射的能量来自哪里？不能把空间或时间当作燃料

对准静态 Schwarzschild 黑洞，

$$
T_H=\frac{\hbar c^3}{8\pi GMk_B},
$$

$$
S_{\mathrm{BH}}
=
\frac{k_Bc^3A}{4G\hbar}
=
\frac{4\pi k_BGM^2}{\hbar c}.
$$

因此

$$
\boxed{
d(Mc^2)=T_H\,dS_{\mathrm{BH}}.
}
\tag{47.1}
$$

这些是黑洞热力学中的标准半经典关系。([Springer][4])

---

## 定理 47.1　有限能量源不能永久维持固定正辐射功率

若无入射补偿，且剩余能量非负，

$$
\frac{dE_B}{du}=-P(u),
\qquad
E_B(u)\ge0,
$$

则

$$
\boxed{
\int_{u_0}^{\infty}P(u)\,du
\le E_B(u_0).
}
\tag{47.2}
$$

特别地，若某段时间内 \(P(u)=P_0>0\)，则该恒定功率阶段的持续时间满足

$$
\boxed{
\Delta u\le\frac{E_B(u_0)}{P_0}.
}
\tag{47.3}
$$

### 证明

积分能量平衡式，并使用末态能量非负。∎

因此，把固定质量背景与永久恒定霍金能流放在一起，只能是外部背景近似，不能是有限能量封闭系统的最终描述。

对于自洽蒸发，需要加入：

$$
\boxed{
\frac{d(Mc^2)}{du}=-P_H(u)
}
$$

及相应反作用；质量、表面引力、场态和传播映射随之改变。

“形成内部时间”并不是供能机制。**在无外来补偿的蒸发过程中，辐射能量必须由黑洞及其完整引力—物质系统的能量预算支付。**

而且，黑洞熵 \(S_{\mathrm{BH}}\)、辐射纠缠熵 \(\mathcal S\) 与历史信息 \(I(X:R)\)，是三个不同的量，不能统一解释成“被吞进去的空间体积”。

---

# 48．若外侧关联先积累、后来释放，能流不能任意指定

下面给出一个更强的自洽性约束，但仍限定于第 45 节的二维共形模型。

## 假设 48.1　有限的额外纠缠过程

设

$$
\mathcal S\in C_c^2(\mathbb R)
$$

非恒零。也就是说，真空扣除纠缠熵在有限过程中变化，而早晚都回到同一基准。

令

$$
\psi(u)=e^{6\mathcal S(u)/\nu}>0.
$$

---

## 定理 48.1　纠缠恢复过程的加权能流约束

有

$$
\boxed{
\mathcal F(u)
=
\frac{\hbar\nu}{12\pi}
\frac{\psi''(u)}{\psi(u)}.
}
\tag{48.1}
$$

从而

$$
\boxed{
\int_{-\infty}^{\infty}
\mathcal F(u)\psi(u)\,du=0.
}
\tag{48.2}
$$

若过程非平凡，则 \(\mathcal F\) 不能处处非负，也不能处处非正。

### 证明

由

$$
\frac{\psi''}{\psi}
=
\frac6\nu\mathcal S''
+
\frac{36}{\nu^2}(\mathcal S')^2,
$$

结合式（45.3）得到式（48.1）。

由于 \(\mathcal S\) 紧支撑，\(\psi'\) 在两端为零，因此

$$
\int\mathcal F\psi\,du
=
\frac{\hbar\nu}{12\pi}\int\psi''\,du=0.
$$

又因 \(\psi>0\)，若 \(\mathcal F\) 不变号，则只能恒为零。此时 \(\psi''=0\)，结合两端条件得到 \(\psi=1\)、\(\mathcal S=0\)，与非平凡性矛盾。∎

同时，

$$
\boxed{
\int\mathcal F(u)\,du
=
\frac{3\hbar}{\pi\nu}
\int(\mathcal S'(u))^2\,du
>0.
}
\tag{48.3}
$$

所以，出现局部负能流不意味着总辐射能量为负。

这类能流—纠缠约束由 Bianchi 与 Smerlak 在二维共形场模型中建立。它不能未经推广就当成所有四维黑洞蒸发的普遍定理。

### 对当前理论的意义

不能一边任意指定“关联不断增加后又完整释放”，一边独立指定“永远是同样的正热流”，却不检查两者能否由同一个场态和传播映射产生。

**记录结构、纠缠结构与能量流必须来自同一个实现。**

但 \(\mathcal S\) 回到基准，也不单独证明原输入历史已经被外侧完整恢复。输入恢复仍然应由第 46 节的通道与信息判据检验。

---

# 49．如何接入项目的 CUT—FLOW—ADMIT—ANCHOR 结构？

现在可以明确放置这些对象。

## 49.1　CUT：区分三种不同的观察接口

历史记录接口：

$$
x\longmapsto\rho_M^x.
$$

外侧辐射接口：

$$
\rho_{\mathrm{total}}
\longmapsto\rho_R.
$$

几何读数接口：

$$
(g,\rho_{\mathrm{field}},\text{钟标定})
\longmapsto
\text{传播与探测统计}.
$$

这三个 CUT 的核一般不同。

两个历史可以给出相同热谱，却给出不同的多模式联合辐射态；两个背景也可以在有限实验窗口内给出相同能流，却具有不同的远期因果延拓。

因此，“某个读数一样”不能直接升级成“内部结构全部一样”。

## 49.2　FLOW：记录交互与场传播必须分别实现

观察者记忆的写入来自系统—记忆的具体耦合。

霍金辐射来自给定背景、初态与传播关系下的量子场演化。

其共同语言是联合量子过程和约化读数，但不能只因都使用偏迹，就认定二者具有相同 Hamiltonian 或相同能量预算。

仓库 `EnvironmentRecords.lean` 已有受控记录、环境重叠和约化相位阻尼的具体算子构造；把它推广到霍金模式，需要补入场态与模分解，而不是把原有限矩阵定理改名。

## 49.3　ADMIT：至少包含三组独立条件

几何上，需要明确未来方向、适用背景与因果可达性。

量子场上，需要明确初态、正频率定义、模式正规化和近似范围。

记录上，需要明确实际可访问的模式、测量资源和恢复目标。

温度还需要钟标定；仓库已有的同尺度、不同温度反例，恰好阻止省略这一条件。

## 49.4　ANCHOR：不能由形式关联自动生成实际记忆

一个两模式压缩态存在，不等于观察者已经探测并保存了其中结果。

一个热谱可以被计算，也不等于它已经成为某个记忆寄存器中的事实。

实际记录还要求具体探测交互及其结果见证。**理论态、统计规律与实际记忆，应在项目中保持不同类型。**

本增订没有将新的综合命题标记为 Lean 已闭合；其中二维能流—熵恒等式和半经典霍金机制属于已有结果，本文给出的是它们与项目观察接口、历史区分和能量闭合条件的连接。

---

# 50．统一结论：三种“转化”怎样相容？

可以把当前理论总结为以下条件性命题。

## 统一命题

在明确的量子记录模型、经典黑洞几何实现与半经典场态条件下：

### 第一，观察者把时序区别转化为当前关联

$$
\boxed{
\text{过去发生了什么}
\longrightarrow
\text{当前记忆能区分什么}.
}
$$

这由 \(I(X:M)\) 或对应接口的可区分核刻画，而不是由经历时间的长度刻画。

### 第二，黑洞把径向空间选择转化为未来约束

$$
\boxed{
\text{外部可以选择的向内／向外}
\longrightarrow
\text{内部必须满足的径向未来方向}.
}
$$

这由 \(g^{-1}(dr,dr)<0\) 及未来定向刻画，不表示新增一个时间维度。

### 第三，视界传播与量子场态共同产生外侧辐射

$$
\boxed{
p(u)
\longrightarrow
\text{正频率混合}
\longrightarrow
\text{内外模式关联与外侧粒子统计}.
}
$$

在限定的二维模型中，同一个 \(p\) 还同时决定：

$$
\boxed{
\mathcal S=-\frac{\nu}{12}\log p',
\qquad
\mathcal F=-\frac{\hbar\nu}{24\pi}\{p,u\}.
}
$$

### 第四，辐射成为“关于原历史的记忆”需要额外证明

必须检验：

$$
\boxed{
I(X:R)>0,
}
$$

或更强的量子恢复条件。

热辐射本身、外侧高熵本身、内外纠缠本身，都不足以完成这一步。

---

## 最终解释

你的句子可以保留成如下更严格的版本：

> **观察者把可访问的过去写成自身的关联记忆。黑洞的因果结构使某些原本的空间选择变成内部不可回避的时间方向；同一结构对量子场的传播和频率分解产生作用，在适当场态下表现为霍金辐射。辐射是否进一步携带形成黑洞的历史，则由完整信息转移与恢复结构决定。**

因此，最深的对应不是：

$$
\text{时间}\to\text{记忆物质},
\qquad
\text{空间}\to\text{时间物质与辐射}.
$$

而是：

$$
\boxed{
\text{因果结构决定哪些关系能够形成，}
}
$$

$$
\boxed{
\text{量子动力学决定这些关系怎样被编码，}
}
$$

$$
\boxed{
\text{观察接口决定其中哪些区别成为记忆或辐射读数。}
}
$$

**这使“观察者—黑洞”的联系从吞噬比喻，转变成一个统一的关联生成、访问分割与能量约束问题。**

黑洞内部并不会因此自动成为一个唯一观察者；但若要研究内部观察者，它的钟、记忆和行动必须同时服从内部因果结构。霍金辐射也不是这个内部观察者把自己的时间直接吐向外部，而是整个几何—量子场过程在外侧可访问代数上的可测表现。

[1]: https://arxiv.org/abs/0809.4098?utm_source=chatgpt.com "[0809.4098] Minimal Energy Cost for Thermodynamic ..."
[2]: https://davidtong.org/teaching/general-relativity/grhtml/S6.html "6 Black Holes‣ General Relativity by David Tong"
[3]: https://arxiv.org/html/2502.13026v1 "Deriving the paradox: original derivation of Hawking radiation"
[4]: https://link.springer.com/article/10.12942/lrr-2001-6 "The Thermodynamics of Black Holes | Living Reviews in Relativity | Springer Nature Link"
[5]: https://arxiv.org/pdf/2209.09980?utm_source=chatgpt.com "arXiv:2209.09980v1 [gr-qc] 20 Sep 2022"
[6]: https://arxiv.org/abs/gr-qc/0603046?utm_source=chatgpt.com "Quantum information cannot be completely hidden in correlations: implications for the black-hole information paradox"
# 辐射关联、时间编码与观察者可恢复性

## ——量子观察者—关系时空理论第五十一至第六十节增订

### 摘要

前文已经区分：观察者的历史记忆、黑洞内部的径向时间化，以及霍金辐射的热性。本增订进一步研究一个尚未闭合的问题：

> **某段历史进入一个量子系统以后，怎样从内部关联转化为外部观察者可恢复的记忆？这一过程与热辐射、能量守恒和内部时间结构之间有什么约束？**

本增订以项目已有的接口核、目标残差、精化和动力下降为基础，建立有限维量子过程模型，证明：

$$
\boxed{
\text{新增可恢复信息}
=
\text{新辐射相对于旧辐射的条件关联增量};
}
$$

$$
\boxed{
\text{完整外侧恢复}
\iff
\text{补侧不再保留原输入的量子信息};
}
$$

并给出两项不可能性结论：

**普遍、独立的热替换发射不能同时实现内部状态空间的缩小；有限个辐射片段若各自对全部输入完全不可区分，就不能在严格可加的能量守恒下承载一个非平凡的内部钟 Hamiltonian。**

这些结论均具有明确的适用条件，不直接代替真实黑洞的量子引力动力学。

项目依据固定于本次读取的提交 `d3510a14b83a3e36662b0a5aa305213f57f4afd0`。本次读取的 `PetzRecovery.lean` 与 `ConditionalMutualInformation.lean` 处理的是有限经典概率；下文的量子恢复和量子条件互信息命题应单独形式化，不能直接视为这些已有 Lean 模块的结论。

---

# 51．首先补齐项目中的一个关键类型区别

项目定义目标残差：

$$
\operatorname{Residual}(q,T)
=
\ker q\setminus\ker T,
$$

并规定两个接口的静态联合：

$$
(q_1\vee q_2)(x)
=
(q_1(x),q_2(x)).
$$

因此：

$$
\ker(q_1\vee q_2)
=
\ker q_1\cap\ker q_2.
$$

这些关系是严格的。但应用到量子系统时，必须先说明接口输出究竟包含什么。

## 定义 51.1　边缘接口与联合接口

对联合量子态 \(\rho_{12}\)，定义：

$$
q_1(\rho)=\operatorname{Tr}_2\rho,
\qquad
q_2(\rho)=\operatorname{Tr}_1\rho.
$$

分别保存两个边缘态的接口为：

$$
\boxed{
q_{\mathrm{sep}}(\rho)
=
\bigl(q_1(\rho),q_2(\rho)\bigr).
}
\tag{51.1}
$$

保存完整联合态的接口为：

$$
\boxed{
q_{\mathrm{joint}}(\rho)=\rho_{12}.
}
\tag{51.2}
$$

这两个接口不是同一个对象。

---

## 定理 51.1　边缘接口的联合一般不等于量子联合接口

一般有严格包含：

$$
\boxed{
\ker q_{\mathrm{joint}}
\subsetneq
\ker q_{\mathrm{sep}}.
}
\tag{51.3}
$$

### 证明

若联合态相同，其两个边缘态当然相同，因此得到包含关系。

取：

$$
|\Phi_\pm\rangle
=
\frac{|00\rangle\pm|11\rangle}{\sqrt2}.
$$

两者在每一侧的边缘态都是：

$$
\frac I2.
$$

因此：

$$
q_{\mathrm{sep}}(\Phi_+)
=
q_{\mathrm{sep}}(\Phi_-).
$$

但：

$$
\langle X\otimes X\rangle_{\Phi_+}=1,
\qquad
\langle X\otimes X\rangle_{\Phi_-}=-1.
$$

联合态可被区分，故包含严格。∎

### 解释

这里并不是说只能用复杂的联合量子门才能看到差别。两侧分别测量 \(X\)，再保存配对结果的相关性，也能区分上述状态。

区别在于：

$$
\boxed{
\text{只保存各侧统计}
\ne
\text{保存各侧结果之间的关联}.
}
$$

因此，对辐射说“每个片段都一样”，不等于对完整辐射说“没有保存任何历史”。

这不是项目联合核公式失效，而是不能把不同的 CUT 当成同一个 CUT。

---

# 52．用一个闭合过程描述内部记忆与辐射增长

## 假设 52.1　有限有效过程

令 \(L\) 为需要追踪的初始量子信息空间：

$$
\dim\mathcal H_L=d\ge2.
$$

它可以表示有限组历史的量子编码，也可以表示某个观察者内部钟与记忆的一个有限子空间。

在第 \(n\) 个过程阶段，完整编码为等距映射：

$$
\boxed{
V_n:\mathcal H_L
\longrightarrow
\mathcal H_{B_n}\otimes\mathcal H_{R^n},
}
\tag{52.1}
$$

其中：

$$
R^n=r_1r_2\cdots r_n.
$$

\(R^n\) 是已经向外输出并累计保留的系统；\(B_n\) 包含其余全部未访问自由度，包括必要的辅助记录。

每次新发射由等距映射：

$$
W_n:B_{n-1}\longrightarrow B_n\otimes r_n
$$

实现，且不再作用于已经保留的旧辐射：

$$
V_n=(W_n\otimes I_{R^{n-1}})V_{n-1},
$$

省略无物理内容的张量因子排序。

此处 \(n\) 是过程阶段，不是黑洞内部面积半径，也不直接等于固有时间。两者的对应必须由前文的钟与因果实现提供。

有限维与张量分割是本节的有效模型条件，不能直接宣称它们已经严格描述了连续量子场及完整引力约束。

---

## 定义 52.1　内外量子接口

定义外侧接口：

$$
\boxed{
\mathcal N_n(\rho)
=
\operatorname{Tr}_{B_n}
(V_n\rho V_n^\dagger),
}
\tag{52.2}
$$

以及补侧接口：

$$
\boxed{
\mathcal C_n(\rho)
=
\operatorname{Tr}_{R^n}
(V_n\rho V_n^\dagger).
}
\tag{52.3}
$$

它们都是完全正、保迹映射。

---

## 定理 52.1　累计辐射形成物理精化链

有：

$$
\boxed{
\mathcal N_{n-1}
=
\operatorname{Tr}_{r_n}\circ\mathcal N_n.
}
\tag{52.4}
$$

因此，在累计辐射被完整保留的模型中：

$$
\boxed{
\ker\mathcal N_n
\subseteq
\ker\mathcal N_{n-1}.
}
\tag{52.5}
$$

### 证明

对 \(B_n,r_n\) 一并取偏迹，等价于在等距映射 \(W_n\) 之前对 \(B_{n-1}\) 取偏迹。

于是得到式（52.4），再由函数复合得到核包含。∎

### 注 52.1

这不保证实际观察者的记忆始终增长。

若外侧观察者又实施压缩、丢弃、测量或遗忘：

$$
\mathcal D_n:R^n\to M_n,
$$

实际接口是：

$$
\mathcal D_n\circ\mathcal N_n.
$$

它未必构成精化链。

**“辐射已经包含信息”与“某个观察者已经把信息保存成记忆”，是两项不同要求。**

---

# 53．信息输出的正确增量：条件互信息，而不是辐射熵

为检验任意量子输入是否保留，引入与 \(L\) 最大纠缠的参照系统 \(A\)：

$$
|\Phi_d\rangle_{AL}
=
\frac1{\sqrt d}\sum_{j=1}^d|j\rangle_A|j\rangle_L.
$$

经过 \(V_n\) 后：

$$
|\Psi_n\rangle_{AB_nR^n}
=
(I_A\otimes V_n)|\Phi_d\rangle.
$$

该态仍为纯态，并且：

$$
S(A)=\log d.
$$

所有熵采用自然对数。

## 定义 53.1　外侧信息与补侧关联余量

定义：

$$
\boxed{
\mathcal I_n=I(A:R^n),
}
\tag{53.1}
$$

$$
\boxed{
\mathcal L_n=I(A:B_n).
}
\tag{53.2}
$$

\(\mathcal L_n\) 是原输入参照仍与补侧保留的关联，不应直接称为“已经永久丢失的信息”。

---

## 定理 53.1　内外关联守恒式

有：

$$
\boxed{
\mathcal I_n+\mathcal L_n=2\log d.
}
\tag{53.3}
$$

### 证明

由于 \(AB_nR^n\) 纯：

$$
S(AR^n)=S(B_n),
\qquad
S(AB_n)=S(R^n).
$$

因此：

$$
I(A:R^n)=S(A)+S(R^n)-S(B_n),
$$

$$
I(A:B_n)=S(A)+S(B_n)-S(R^n).
$$

相加即得。∎

---

## 定理 53.2　新增辐射的信息增量

令：

$$
\boxed{
\mathcal J_n
=
I(A:r_n\mid R^{n-1}).
}
\tag{53.4}
$$

则：

$$
\boxed{
\mathcal I_n-\mathcal I_{n-1}
=
\mathcal J_n
=
\mathcal L_{n-1}-\mathcal L_n
\ge0.
}
\tag{53.5}
$$

### 证明

互信息链式法则给出：

$$
I(A:R^{n-1}r_n)
=
I(A:R^{n-1})
+
I(A:r_n\mid R^{n-1}).
$$

根据定理 52.1，旧辐射与 \(A\) 的联合边缘态没有改变。

再用量子强次可加性：

$$
I(A:r_n\mid R^{n-1})\ge0,
$$

及式（53.3），即得结论。∎

这里使用的是量子强次可加性。其零条件与量子 Markov 恢复结构具有明确联系，不能直接用经典概率模块代替。([arXiv][1])

---

## 定理 53.3　辐射熵增量不等于输入信息增量

有：

$$
\boxed{
S(R^n)-S(R^{n-1})
=
S(r_n)-I(r_n:R^{n-1}),
}
\tag{53.6}
$$

而：

$$
\boxed{
\mathcal J_n
=
I(r_n:AR^{n-1})
-
I(r_n:R^{n-1}).
}
\tag{53.7}
$$

### 证明

分别展开两侧的熵定义即可。∎

所以：

$$
\boxed{
\text{辐射熵上升、下降或保持不变，}
\quad
\text{都不能单独决定原输入信息输出了多少。}
}
$$

真正需要计算的是：新片段在已有记录的条件下，增加了哪些与原输入有关的可恢复关联。

---

# 54．从“核没有碰撞”提升到真正的量子恢复

## 定义 54.1　完整量子恢复

称阶段 \(n\) 的外侧接口可完整恢复 \(L\)，若存在完全正、保迹映射：

$$
\mathcal R_n:R^n\to L
$$

满足：

$$
\boxed{
\mathcal R_n\circ\mathcal N_n=\operatorname{id}_L.
}
\tag{54.1}
$$

这是信息论层面的恢复存在性。实际观察者是否能够执行 \(\mathcal R_n\)，还要检查其允许操作、时间、能量和控制精度。

恢复存在性与现实可执行性的区别，在黑洞信息检索模型中尤其重要；例如 Hayden–Preskill 模型明确加入了内部混合与对辐射控制能力的假设。([arXiv][2])

---

## 定理 54.1　完整恢复、补侧替换与参照解耦的等价

下列条件等价：

1. 存在式（54.1）的恢复通道；
2. 存在固定态 \(\sigma_{B_n}\)，使

   $$
   \boxed{
   \mathcal C_n(\rho)=\sigma_{B_n}
   \qquad\forall\rho;
   }
   \tag{54.2}
   $$
3. 对最大纠缠测试态，

   $$
   \boxed{
   I(A:B_n)=0.
   }
   \tag{54.3}
   $$

### 证明

**\(2\Rightarrow1\)。**

写：

$$
\sigma_{B_n}
=
\sum_a\lambda_a|a\rangle\langle a|,
\qquad
\lambda_a>0.
$$

对输入基底 \(|i\rangle\)，将编码展开为：

$$
V_n|i\rangle
=
\sum_a\sqrt{\lambda_a}\,
|v_{ia}\rangle_{R^n}|a\rangle_{B_n}.
$$

条件（54.2）不仅约束对角输入，也通过线性性和极化恒等式约束所有 \(|i\rangle\langle j|\)。因此：

$$
\langle v_{jb}|v_{ia}\rangle
=
\delta_{ij}\delta_{ab}.
$$

所以可以在 \(R^n\) 的相应支持上定义等距解码：

$$
|v_{ia}\rangle\longmapsto|i\rangle_L|a\rangle_G.
$$

对辅助寄存器 \(G\) 取偏迹，并在支持之外任意补成保迹操作，即得到恢复通道。

**\(1\Rightarrow3\)。**

恢复后：

$$
I(A:L)=2\log d.
$$

由量子数据处理不等式：

$$
2\log d
\le I(A:R^n).
$$

但定理 53.1 给出：

$$
I(A:R^n)\le2\log d.
$$

所以：

$$
I(A:B_n)=0.
$$

**\(3\Rightarrow2\)。**

零互信息意味着：

$$
\rho_{AB_n}
=
\frac{I_A}{d}\otimes\sigma_{B_n}.
$$

这是补通道的归一化 Choi 态。比较其全部矩阵块，得到：

$$
\mathcal C_n(|i\rangle\langle j|)
=
\delta_{ij}\sigma_{B_n}.
$$

由线性性即得式（54.2）。∎

这是量子纠错中恢复与互补通道信息之间的标准关系；上述证明将其直接写成当前内外接口模型。([arXiv][3])

### 结论

**当外侧已经能够完整恢复任意原输入时，补侧不可能还独立保留另一份完整的同一量子信息。**

可以共享某些经典记录，却不能把任意未知量子态复制成两个彼此独立的完整观察者。

---

# 55．“每一份看起来热”与“每次都产生独立热替换”完全不同

## 定义 55.1　边缘不可区分性

称第 \(j\) 个辐射片段对初始输入边缘不可区分，若：

$$
\boxed{
\operatorname{Tr}_{\overline{r_j}}
(V_n\rho V_n^\dagger)
=
\tau_j
\qquad\forall\rho.
}
\tag{55.1}
$$

\(\tau_j\) 可以是指定 Hamiltonian 下的热态。

该条件只约束单个辐射片段，不约束它与其他片段之间的关联。

---

## 定义 55.2　普遍的单步替换发射

对一步映射：

$$
W_n:B_{n-1}\to B_n\otimes r_n,
$$

若：

$$
\boxed{
\operatorname{Tr}_{B_n}
(W_n\sigma W_n^\dagger)
=
\tau_n
\qquad
\forall\sigma\in\mathcal D(B_{n-1}),
}
\tag{55.2}
$$

则称该步为普遍替换发射。

式（55.2）的量词遍历整个内部输入空间，强于式（55.1）对实际编码输入族的边缘限制。

---

## 定理 55.1　普遍替换发射不增加原输入的外侧信息

在式（55.2）下：

$$
\boxed{
\rho_{AR^{n-1}r_n}
=
\rho_{AR^{n-1}}\otimes\tau_n.
}
\tag{55.3}
$$

因此：

$$
\boxed{\mathcal J_n=0.}
\tag{55.4}
$$

### 证明

替换通道的线性形式是：

$$
X\longmapsto\operatorname{Tr}(X)\tau_n.
$$

对可能与 \(AR^{n-1}\) 纠缠的内部系统应用这一通道，仍然得到式（55.3）。条件互信息随即为零。∎

---

## 定理 55.2　普遍混合替换要求内部容量增加

若式（55.2）成立，则：

$$
\boxed{
\dim B_n
\ge
\dim B_{n-1}\cdot\operatorname{rank}\tau_n.
}
\tag{55.5}
$$

### 证明

将定理 54.1 中的 Schmidt 展开应用于此次发射，但把 \(r_n\) 视为固定边缘。

若：

$$
\tau_n=\sum_{a=1}^{r}\lambda_a|a\rangle\langle a|,
$$

则对 \(B_{n-1}\) 的每个基底输入 \(|i\rangle\)，必须在 \(B_n\) 内出现一组向量 \(|v_{ia}\rangle\)，满足：

$$
\langle v_{jb}|v_{ia}\rangle
=
\delta_{ij}\delta_{ab}.
$$

共有：

$$
\dim B_{n-1}\cdot r
$$

个正交向量，得到结论。∎

### 解释

如果每步都无条件产生一个与全部内部输入无关的混合态，又要求完整过程保持量子信息，那么内侧必须同时容纳：

原输入信息，以及与新混合输出相对应的纯化自由度。

因此：

$$
\boxed{
\text{普遍独立的热发射}
+
\text{整体等距}
+
\text{内部容量持续缩小}
}
$$

不能在这个有限模型中同时成立。

这一点与霍金独立粒子对近似所面临的信息问题方向一致，但不能据此声称已证明所有近似修正都无效。关于小修正的更强结论，依赖具体的误差与纠缠假设。([arXiv][4])

---

# 56．一个明确实例：单份没有信息，两份恢复全部量子记忆

采用已有量子秘密共享中的三份编码。该例不是黑洞动力学，而是用于检验“局部无信息是否排除整体恢复”的精确模型。([arXiv][5])

## 定义 56.1　三 qutrit 编码

所有标签在 \(\mathbb Z_3\) 中计算。定义：

$$
\boxed{
V|s\rangle
=
\frac1{\sqrt3}
\sum_{j=0}^2
|j,j+s,j+2s\rangle,
\qquad s=0,1,2.
}
\tag{56.1}
$$

---

## 定理 56.1　每一份都与任意输入无关

对任意输入态 \(\rho\) 及任意单份 \(r_i\)：

$$
\boxed{
\operatorname{Tr}_{\overline{r_i}}
(V\rho V^\dagger)=\frac{I_3}{3}.
}
\tag{56.2}
$$

### 证明

对矩阵单位 \(|s\rangle\langle t|\) 展开编码。

以保留第一份为例，偏迹要求：

$$
j+s=k+t,
\qquad
j+2s=k+2t.
$$

相减得：

$$
s=t,
$$

继而 \(j=k\)。

所以：

$$
\operatorname{Tr}_{23}
(V|s\rangle\langle t|V^\dagger)
=
\delta_{st}\frac{I_3}{3}.
$$

另外两份同理。∎

---

## 定理 56.2　任意两份足以恢复输入

对第一、二份，定义置换酉：

$$
\boxed{
D_{12}|a,b\rangle
=
|b-a,\;2b-a\rangle.
}
\tag{56.3}
$$

则：

$$
\boxed{
(D_{12}\otimes I)V|\psi\rangle
=
|\psi\rangle
\otimes
\frac1{\sqrt3}\sum_{r=0}^2|r,r\rangle.
}
\tag{56.4}
$$

### 证明

对编码中的基底项：

$$
|j,j+s\rangle
\longmapsto
|s,j+2s\rangle.
$$

第三份正好也是 \(j+2s\)。令 \(r=j+2s\)，对 \(j\) 求和，得到式（56.4）。

编码在三份循环置换下保持同样形式，因此任意两份都可以恢复。∎

---

## 推论 56.1　信息输出与熵变化可以发生在不同阶段

以最大纠缠参照 \(A\) 检验编码，并依次释放三份。

则：

| 已收集辐射 | \(S(R^n)/\log3\) | \(I(A:R^n)/\log3\) |
| ----- | ---------------: | -----------------: |
| 无     |                0 |                  0 |
| 第一份   |                1 |                  0 |
| 前两份   |                2 |                  2 |
| 全三份   |                1 |                  2 |

第二份到达时：

$$
\mathcal J_2=2\log3,
$$

尽管它单独完全不含输入信息。

第三份到达时，辐射熵下降，但：

$$
\mathcal J_3=0.
$$

这些等距、单份替换和解码恒等式已作精确矩阵核验；表中的熵也与直接计算一致。

这里最终辐射熵不为零，是因为它仍与测试参照 \(A\) 纠缠，不是因为编码丢失了纯度。

### 物理边界

\(I_3/3\) 是最大混合态，但这个例子没有给出霍金温度、黑洞几何或能量守恒的辐射 Hamiltonian。

它证明的是：

$$
\boxed{
\text{完全相同的单份读数}
\quad
\text{可以与完整的联合量子恢复相容。}
}
$$

接下来，能量和内部时间会进一步限制这种相容性。

---

# 57．非平凡内部时间不能被任意隐藏在完全相同的局部热态中

这是把本轮重新接回“观察者内部时间”的关键步骤。

## 定义 57.1　时间协变的编码

设初始观察者内部 Hamiltonian 为 \(H_L\)，最终辐射的 Hamiltonian 可加：

$$
H_R=\sum_{j=1}^m h_j.
$$

若编码满足：

$$
\boxed{
H_RV=V(H_L+E_0I),
}
\tag{57.1}
$$

则相应时间演化满足：

$$
e^{-itH_R/\hbar}V
=
Ve^{-it(H_L+E_0I)/\hbar}.
$$

这表示同一个编码保留内部时钟的时间平移结构。\(E_0\) 是固定能量偏置。

---

## 定理 57.1　严格局部不可区分与非平凡时间协变的不相容性

假设：

$$
\operatorname{Tr}_{\overline{r_j}}
(V\rho V^\dagger)
=
\tau_j
\qquad
\forall\rho,\ \forall j,
$$

并满足式（57.1）。

则：

$$
\boxed{
H_L=\alpha I
}
\tag{57.2}
$$

对某个实数 \(\alpha\) 成立。

### 证明

局部输出与输入无关，意味着：

$$
\operatorname{Tr}
\left[
\rho\,V^\dagger h_jV
\right]
=
\operatorname{Tr}(\tau_jh_j)
$$

对全部 \(\rho\) 成立。

因此：

$$
V^\dagger h_jV
=
\operatorname{Tr}(\tau_jh_j)I.
$$

求和：

$$
V^\dagger H_RV
=
\left[
\sum_j\operatorname{Tr}(\tau_jh_j)
\right]I.
$$

再由式（57.1）：

$$
H_L+E_0I=V^\dagger H_RV.
$$

故 \(H_L\) 为标量。∎

### 含义

一个非平凡量子钟，需要：

$$
H_L\ne\alpha I.
$$

但若全部单份辐射都对任意输入给出同一个固定热态，而总输出能量只是这些单份能量之和，那么它们不能严格协变地携带这个量子钟。

这是连续对称性与精确量子纠错之间已知张力的一个直接特化，与协变量子码的限制相联系。([arXiv][6])

### 不构成矛盾的几种情形

如果只在同一个能量简并子空间中编码，那么 \(H_L\) 在该子空间上本来就是标量，可以隐藏其他量子信息，但该子空间不独自承担非平凡钟演化。

如果总能量含有跨片段相互作用项，或者还有未计入的储能和参照系统，则式（57.1）的可加前提需要修改。

如果局部热性只是近似成立，则应该使用下面的定量版本。

---

## 定理 57.2　近似局部不可区分的能量下界

定义迹距离：

$$
D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1.
$$

假设对全部输入：

$$
D(\mathcal N_j(\rho),\tau_j)\le\epsilon_j.
$$

记：

$$
w_j=\lambda_{\max}(h_j)-\lambda_{\min}(h_j),
$$

并允许能量实现误差：

$$
\left\|
V^\dagger H_RV-(H_L+E_0I)
\right\|
\le\delta_E.
$$

则：

$$
\boxed{
\Delta H_L
\le
2\delta_E+2\sum_jw_j\epsilon_j,
}
\tag{57.3}
$$

其中：

$$
\Delta H_L
=
\lambda_{\max}(H_L)-\lambda_{\min}(H_L).
$$

### 证明

取 \(H_L\) 的最大、最小能量本征态 \(\rho_+,\rho_-\)。

由能量误差界：

$$
\Delta H_L
\le
\left|
\operatorname{Tr}
H_R
\bigl(V\rho_+V^\dagger-V\rho_-V^\dagger\bigr)
\right|
+2\delta_E.
$$

而对每个 \(j\)：

$$
D(\mathcal N_j(\rho_+),\mathcal N_j(\rho_-))
\le2\epsilon_j.
$$

利用有限谱宽算子的期望差界：

$$
|\operatorname{Tr}[h_j(\sigma-\rho)]|
\le
w_jD(\sigma,\rho),
$$

求和即得。∎

### 结论

**如果辐射确实携带一个具有非零能量跨度的内部时间结构，那么在上述有限、可加、近似守恒模型中，局部不可区分程度不能任意完美。**

但这不意味着每个单独片段都必须具有很大的非热修正。偏差可以分散在很多片段中，式（57.3）约束的是总预算。

---

# 58．内外可以共享经典记录，但不能各自拥有完整的同一非交换观察者

仅有状态恢复还不够。项目一直强调，观察者还包含读数代数、行动与动态闭合。因此，应当把恢复提升到可观测量层面。

## 定义 58.1　保持编码空间的算子实现

设：

$$
V:L\to R\otimes B.
$$

若逻辑算子 \(a\) 存在外侧实现 \(A_R\)，满足：

$$
\boxed{
(A_R\otimes I)V=Va,
}
\tag{58.1}
$$

则称 \(a\) 可在外侧保持编码空间地实现。

类似地，若：

$$
\boxed{
(I\otimes B_B)V=Vb,
}
\tag{58.2}
$$

则称 \(b\) 可在补侧实现。

这一 Heisenberg 图像与算子代数量子纠错的框架一致。([arXiv][7])

---

## 定理 58.1　分离侧重建的交换性约束

若式（58.1）—（58.2）成立，则：

$$
\boxed{[a,b]=0.}
\tag{58.3}
$$

### 证明

有：

$$
\begin{aligned}
Vab
&=(A_R\otimes I)Vb\\
&=(A_R\otimes I)(I\otimes B_B)V\\
&=(I\otimes B_B)(A_R\otimes I)V\\
&=(I\otimes B_B)Va\\
&=Vba.
\end{aligned}
$$

因 \(V\) 为等距映射，故可消去 \(V\)，得到 \(ab=ba\)。∎

### 推论 58.1

如果同一逻辑代数能在内外两侧各自完整实现，那么该共享代数必须交换。

因此：

$$
\boxed{
\text{某些经典记忆可以被内外重复读取；}
}
$$

$$
\boxed{
\text{同一完整非交换量子观察者不能被复制成两个独立副本。}
}
$$

这比“观察者和黑洞内部是同一个东西”更严格：它要求明确说明哪些逻辑量可以在哪一侧实现，以及它们的代数关系。

---

## 定理 58.2　编码重建不等于跨因果边界传信

对任意联合态 \(\rho_{RB}\) 和补侧保迹量子通道 \(\Lambda_B\)：

$$
\boxed{
\operatorname{Tr}_B
\left[
(\operatorname{id}_R\otimes\Lambda_B)(\rho_{RB})
\right]
=
\rho_R.
}
\tag{58.4}
$$

### 证明

对任意外侧效果 \(E_R\)：

$$
\begin{aligned}
&\operatorname{Tr}
\left[
(E_R\otimes I)
(\operatorname{id}\otimes\Lambda_B)(\rho)
\right]\\
&\quad=
\operatorname{Tr}
\left[
(E_R\otimes\Lambda_B^*(I))\rho
\right]\\
&\quad=
\operatorname{Tr}
[(E_R\otimes I)\rho],
\end{aligned}
$$

其中使用了 \(\Lambda_B^*(I)=I\)。∎

因此，外侧能够重建一个编码量，并不意味着内侧可以通过任意后来操作即时改变外侧结果。

**“信息在哪里被编码”与“新的干预沿哪里传播”，仍然是两个必须分别定义的问题。**

---

# 59．观察者的内部容量缩小时，哪些结论是强制的？

## 定理 59.1　剩余容量对信息保留的限制

在第 53 节的纯态模型中，设：

$$
d_{B_n}=\dim B_n.
$$

则：

$$
\boxed{
\mathcal I_n
\ge
\max\left\{
0,\,
2\log d-2\log d_{B_n}
\right\}.
}
\tag{59.1}
$$

### 证明

互信息满足：

$$
I(A:B_n)\le2S(B_n)\le2\log d_{B_n}.
$$

结合：

$$
\mathcal I_n+I(A:B_n)=2\log d
$$

即可。∎

### 含义

如果原输入维数为 \(d\)，而剩余系统的可用量子容量已经降到小于 \(d\)，那么在整体等距的前提下，外侧必须已经获得一部分原输入关联。

若剩余系统最终只有一个固定纯态：

$$
d_{B_n}=1,
$$

则：

$$
\mathcal I_n=2\log d,
$$

并由定理 54.1得到完整恢复。

但是，实际黑洞的：

$$
\text{面积},
\quad
\text{内部体积},
\quad
\text{有效状态空间维数},
\quad
\text{某个观察者可使用的记忆容量}
$$

不能不加证明地相互替换。

式（59.1）是信息论定理。把 \(d_{B_n}\) 与某个黑洞面积熵识别，是额外的几何—微观状态桥梁，不应藏进定义。

### 对“吞噬空间形成内部时间”的补充

径向因果结构说明内部观察者的未来如何被约束。

本节说明该观察者还能把多少原始量子区别保留在剩余系统中。

二者不是同一量：

$$
\boxed{
\text{拥有更长或更特殊的内部时间方向}
\not\Rightarrow
\text{拥有无限的信息储存能力}.
}
$$

要把两者联系起来，需要具体的内部动力学、能量、记录载体和可访问代数。

---

# 60．把本轮结果重新组织进项目四角色

本轮没有增加一种新的“信息物质”，而是把已有结构推进到更严格的量子过程层。

| 项目角色       | 本轮的具体实现                                               |
| ---------- | ----------------------------------------------------- |
| **CUT**    | 外侧通道 \(\mathcal N_n\)、补侧通道 \(\mathcal C_n\)、边缘接口与联合接口 |
| **FLOW**   | 等距编码 \(V_n\)、逐步发射 \(W_n\)、保持能量或时间协变的实现                |
| **ADMIT**  | 完全正与保迹、编码空间保持、可实施解码、能量预算与局域因果条件                       |
| **ANCHOR** | 实际制备、参照关联、辐射检测与解码结果的见证                                |

由此，项目的“余量”也必须按任务区分：

$$
\ker q\setminus\ker T
$$

描述目标区分失败；

$$
I(A:B_n)
$$

描述与原量子输入有关的补侧关联；

$$
I(A:r_n\mid R^{n-1})
$$

描述新增外侧信息；

而恢复通道：

$$
\mathcal R_n\mathcal N_n=\operatorname{id}
$$

描述完整、物理类型正确的恢复。

**这些量相互联系，但没有理由被压成同一个无条件的标量。**

尤其要保留：

$$
\boxed{
\text{经典接口的因子化}
\ne
\text{量子通道的可恢复性}
\ne
\text{现实观察者的可执行解码}.
}
$$

项目现有的统一下降判据提供了结构出发点；量子恢复、连续时间协变和辐射动力学仍需相应的独立证明。

---

# 结论：从“吞噬”推进到可恢复的时序关联理论

这一轮最重要的推进，是把前文的三个过程区分得更明确：

$$
\boxed{
\text{历史进入内部}
\longrightarrow
\text{内部与历史建立关联};
}
$$

$$
\boxed{
\text{内部产生辐射}
\longrightarrow
\text{某些关联进入外侧联合态};
}
$$

$$
\boxed{
\text{外侧观察者能够解码}
\longrightarrow
\text{这些关联成为可用记忆}.
}
$$

其中，第二步不由“辐射是热的”保证；第三步也不由“信息在数学上存在”保证。

本轮得到的两个最强约束是：

$$
\boxed{
\text{完全独立、对全部内部输入相同的混合发射，}
\quad
\text{要求内部保留甚至增加纯化容量。}
}
$$

以及：

$$
\boxed{
\text{非平凡的内部时间演化，}
\quad
\text{不能在严格可加能量守恒下，}
\quad
\text{被编码成所有单份都完全不依赖输入的辐射。}
}
$$

因此，一个自洽的“量子观察者—黑洞—辐射”理论不能只描述热谱或内部时间。它必须同时说明：

**哪些历史区别被保存，哪些关联真正向外转移，哪些操作能够恢复它们，以及这种转移怎样与能量和因果结构相容。**

**观察者的记忆不是吞下时间的体积；它是可恢复的时序关联。黑洞辐射也不是自动吐出的记忆；它只有在完整过程把原输入区别转移到可访问联合结构，并允许相应恢复时，才承担这一功能。**

[1]: https://arxiv.org/abs/quant-ph/0304007?utm_source=chatgpt.com "Structure of states which satisfy strong subadditivity of quantum entropy with equality"
[2]: https://arxiv.org/abs/0708.4025?utm_source=chatgpt.com "Black holes as mirrors: quantum information in random subsystems"
[3]: https://arxiv.org/html/0907.5391v4 "General conditions for approximate quantum error correction and near-optimal recovery channels"
[4]: https://arxiv.org/abs/0909.1038?utm_source=chatgpt.com "The information paradox: A pedagogical introduction"
[5]: https://arxiv.org/abs/quant-ph/9901025 "[quant-ph/9901025] How to share a quantum secret"
[6]: https://arxiv.org/html/1902.07714v1 "Continuous symmetries and approximate quantum error correction"
[7]: https://arxiv.org/html/0705.1574v1 "Quantum Error Correction of Observables"
# 证明相关的观察者推理与稳健时间重建

## ——量子观察者—关系时空理论第七十一至第八十节增订

**这轮需要把“推理结构能够形式化”落实为一项比“结论有公式”更强的要求：每一次模型变换，都必须携带它保留什么、依赖什么、误差是多少以及能否物理实现的证明。**

因此，我们不再只写：

$$
\text{量子观察者}
\longrightarrow
\text{时间}
\longrightarrow
\text{几何}.
$$

而是要求每条箭头具有明确类型，例如：

$$
\boxed{
\text{具体量子过程}
\xrightarrow[\text{误差界}]{\text{实现与相容性证明}}
\text{观察者可读过程}.
}
$$

本增订同时推进一个物理问题：

> **有限参照造成的相干损耗、多个观察者之间的标定失配，以及真正的几何闭路效应，怎样在理论中分别识别？**

下面给出定义、定理和证明。文末附有一个保存推理链结构的 Lean 源码原型；本轮没有运行 Lean 编译，不能将新增命题标记为机器证明已闭合。

---

# 71．推理结构本身必须是对象，而不只是证明状态标签

项目已经区分 CUT、FLOW、ADMIT 与 ANCHOR，并明确：定义一个合法对象的类型，不会自动产生该类型的实际元素。我们继续保留这一原则。

## 定义 71.1　带状态域的观察接口

一个接口为

$$
\mathfrak A=(X_A,B_A,q_A),
$$

其中

$$
q_A:X_A\to B_A.
$$

\(X_A\) 应当是已经满足当前准入条件的状态类型。例如，有限量子模型中可以取

$$
X_A=
\left\{
\rho\in M_d(\mathbb C):
\rho\ge0,\ \operatorname{Tr}\rho=1
\right\}.
$$

因此，后续定理中的“对全部状态”不是对任意复矩阵，而是对这个明确的合法状态域。

---

## 定义 71.2　精确推理步骤

从接口 \(\mathfrak A\) 到接口 \(\mathfrak B\) 的一个精确步骤，是三元组

$$
\boxed{
s=(F_s,\overline F_s,p_s),
}
\tag{71.1}
$$

其中

$$
F_s:X_A\to X_B,
$$

$$
\overline F_s:B_A\to B_B,
$$

而 \(p_s\) 是命题

$$
\boxed{
\forall x\in X_A,\qquad
q_B(F_sx)=\overline F_s(q_Ax)
}
\tag{71.2}
$$

的证明。

这里不能只声明“\(\overline F_s\) 是下降动力学”。必须实际给出该映射，并填入式（71.2）的证明。

如果讨论量子物理，\(F_s\) 与 \(\overline F_s\) 还必须具有指定的物理实现见证；一般函数的存在不自动满足这一要求。

---

## 定义 71.3　推理链

推理链由以下构造归纳生成：

$$
\operatorname{Id}_{\mathfrak A}
:
\mathfrak A\rightsquigarrow\mathfrak A;
$$

$$
\operatorname{Cons}(s,P)
:
\mathfrak A\rightsquigarrow\mathfrak C,
$$

其中

$$
s:\mathfrak A\rightsquigarrow\mathfrak B
$$

是一个精确步骤，且

$$
P:\mathfrak B\rightsquigarrow\mathfrak C
$$

是已经构造的推理链。

**这是一种保存结构的归纳数据，而不只是一个“已证明”布尔值。**

在 Lean 中，应把这类可检查的推理树放在 `Type`，再证明其语义正确性。仅把它放进 `Prop`，不能期待从证明无关性下的证明对象中读取全部运行时推理结构。Lean 的命题具有证明无关性，并在编译运行时被擦除。([Lean Language][1])

一个最小结构片段为：

```lean
structure ExactStep (A B : Interface) where
  evolve  : A.State → B.State
  descend : A.View → B.View
  square  : ∀ x,
    B.read (evolve x) = descend (A.read x)

inductive Chain : Interface → Interface → Type _ where
  | nil (A) : Chain A A
  | cons (head : ExactStep A B)
         (tail : Chain B C) : Chain A C
```

这不是新的逻辑公理系统。它只是把特定种类的数学推导保存为数据，并让 Lean 的既有逻辑检查每个步骤及整条链。

---

# 72．推理链的语义正确性与失败见证

## 定理 72.1　精确推理链的组合正确性

设推理链 \(P\) 的完整状态映射为 \(F_P\)，读数映射为 \(\overline F_P\)。则

$$
\boxed{
q_B\circ F_P
=
\overline F_P\circ q_A.
}
\tag{72.1}
$$

### 证明

对推理链结构归纳。

恒等链中，两边都等于 \(q_A\)。

假设第一步为 \(s:\mathfrak A\to\mathfrak C\)，后续链为 \(Q:\mathfrak C\to\mathfrak B\)。则

$$
\begin{aligned}
q_BF_QF_s
&=\overline F_Qq_CF_s\\
&=\overline F_Q\overline F_sq_A.
\end{aligned}
$$

第一步使用归纳假设，第二步使用 \(s\) 自带的交换证明。∎

---

## 定理 72.2　精确推理链排除端点 carry

不存在 \(x,y\in X_A\)，使

$$
q_A(x)=q_A(y),
$$

但

$$
q_B(F_Px)\ne q_B(F_Py).
$$

### 证明

由定理 72.1，

$$
q_B(F_Px)
=
\overline F_P(q_Ax)
=
\overline F_P(q_Ay)
=
q_B(F_Py).
$$

矛盾。∎

这正好扩展仓库已有的 `exact_descent_has_no_carry`：已有文件处理一个精确交换方块，本节把它提升为携带各步骤见证的有限推理链。

---

## 例 72.1　一个无法填写下降证明的量子实例

令观察接口只读取

$$
q(\rho)=\rho_{00}.
$$

取两个合法纯态密度矩阵：

$$
\rho_\pm
=
\frac12
\begin{pmatrix}
1&\pm1\\
\pm1&1
\end{pmatrix}.
$$

二者满足

$$
q(\rho_+)=q(\rho_-)=\frac12.
$$

取实酉矩阵

$$
U=
\begin{pmatrix}
3/5&4/5\\
-4/5&3/5
\end{pmatrix}.
$$

直接计算：

$$
\boxed{
q(U\rho_+U^\dagger)=\frac{49}{50},
\qquad
q(U\rho_-U^\dagger)=\frac1{50}.
}
\tag{72.2}
$$

因此，不存在仅作用于原读数 \(q(\rho)\) 的映射 \(\overline F\)，使

$$
q(U\rho U^\dagger)=\overline F(q(\rho))
$$

对全部合法 \(\rho\) 成立。

**这说明：把交换等式写进结构字段，并没有自动证明它；某些真实模型恰好无法提供该字段所需的证明。**

这类反例也应该进入形式化对象，而不是只保留“正向成功”的推理。

---

# 73．物理实现与近似推理必须能够组合

## 定义 73.1　有限量子操作的实现见证

从 \(d\) 维输入到 \(e\) 维输出的一个确定性操作，由有限矩阵族

$$
K_a\in M_{e\times d}(\mathbb C)
$$

及归一化证明

$$
\boxed{
\sum_aK_a^\dagger K_a=I_d
}
\tag{73.1}
$$

给出。

其作用定义为

$$
\Phi(\rho)=\sum_aK_a\rho K_a^\dagger.
$$

这里归一化、完全正性和复合规律都可以转化为有限矩阵命题。

## 定理 73.1　实现见证在复合下闭合

若 \(\Phi\) 由 \(K_a\) 实现，\(\Psi\) 由 \(L_b\) 实现，则 \(\Psi\circ\Phi\) 由

$$
M_{ba}=L_bK_a
$$

实现。

### 证明

有

$$
\sum_{a,b}M_{ba}^\dagger M_{ba}
=
\sum_aK_a^\dagger
\left(\sum_bL_b^\dagger L_b\right)
K_a
=
I.
$$

对任意附加系统，张量后的操作仍以 \(K_a\otimes I\) 为 Kraus 矩阵，保持正性。因此每一步及其复合都完全正、保迹。∎

---

## 定义 73.2　带误差的量子下降证书

本节限定接口 \(Q_i\) 本身也是量子信道。

设完整过程为

$$
\Phi_i:X_{i-1}\to X_i,
$$

候选可见过程为

$$
\overline\Phi_i:B_{i-1}\to B_i.
$$

定义一步误差

$$
\boxed{
\epsilon_i
=
\frac12
\left\|
Q_i\Phi_i-\overline\Phi_iQ_{i-1}
\right\|_\diamond.
}
\tag{73.2}
$$

diamond 范数同时检验输入与任意参考系统相关时的差异，因此适合量子过程的可组合误差分析；只检查若干孤立输入态通常不足以得到同样的组合保证。([arXiv][2])

---

## 定理 73.2　误差沿推理链累加

有

$$
\boxed{
\frac12
\left\|
Q_n\Phi_n\cdots\Phi_1
-
\overline\Phi_n\cdots\overline\Phi_1Q_0
\right\|_\diamond
\le
\sum_{i=1}^n\epsilon_i.
}
\tag{73.3}
$$

### 证明

记

$$
E_i=Q_i\Phi_i-\overline\Phi_iQ_{i-1}.
$$

逐项插入并相消：

$$
\begin{aligned}
&Q_n\Phi_n\cdots\Phi_1
-\overline\Phi_n\cdots\overline\Phi_1Q_0\\
&=
\sum_{j=1}^n
\overline\Phi_n\cdots\overline\Phi_{j+1}
E_j
\Phi_{j-1}\cdots\Phi_1.
\end{aligned}
$$

使用范数三角不等式、次乘性以及每个量子信道的 diamond 范数为一，得到结论。∎

### 条件读数的补充

若最终还要条件于某个事件，而该事件在两个模型中的概率都至少为 \(p_0>0\)，则相应条件概率误差可界为

$$
\boxed{
\frac{2}{p_0}\sum_i\epsilon_i,
}
\tag{73.4}
$$

必要时截断到一。

证明使用分子、分母的概率差分别不超过总迹距离，再对归一化比值作估计。

**所以，“整条过程近似正确”不能不经控制地用于极低概率后选择分支。**

同样，式（73.3）要求每一步确实构成相应通道。若反复使用一个仍保留相关性的环境，就必须把环境记忆包含在状态类型内，而不能默认每步都有新的独立辅助系统。

---

# 74．有限参照与记录重叠：一个完全有限的通道构造

下面继续上一轮的有限参照问题，但选择一个明确的相位记录模型，不把它当作所有参照装置的唯一行为。

## 定义 74.1　有限系数与相干核

取复数序列 \(c_n\)，在整数区间外补零，并满足

$$
c_n=0\quad(n\notin\{0,\ldots,N\}),
$$

$$
\sum_n|c_n|^2=1.
$$

定义

$$
\boxed{
\gamma_\ell
=
\sum_n c_{n+\ell}\overline{c_n}.
}
\tag{74.1}
$$

系统基底 \(|i\rangle\) 具有整数标签 \(q_i\)。

选取足够大的有限整数区间，使以下全部向量都有定义：

$$
|e_i\rangle
=
\sum_m c_{m+q_i}|m\rangle.
$$

于是

$$
\langle e_i|e_i\rangle=1,
$$

并且

$$
\langle e_j|e_i\rangle=\gamma_{q_i-q_j}.
$$

---

## 定理 74.1　有限相干核给出合法量子信道

定义

$$
V|i\rangle=|i\rangle|e_i\rangle.
$$

则 \(V\) 为等距映射，且

$$
\boxed{
\Lambda_c(\rho)_{ij}
=
\gamma_{q_i-q_j}\rho_{ij}
}
\tag{74.2}
$$

是一个完全正、保迹信道。

### 证明

对于任意 \(i,j\)，

$$
\langle Vi|Vj\rangle
=
\langle i|j\rangle\langle e_i|e_j\rangle
=
\delta_{ij}.
$$

所以 \(V^\dagger V=I\)。

对

$$
V\rho V^\dagger
=
\sum_{i,j}\rho_{ij}
|i\rangle\langle j|
\otimes|e_i\rangle\langle e_j|
$$

取环境偏迹，得到式（74.2）。∎

这直接实例化项目的环境记录构造：记录重叠乘在原相干矩阵元上。仓库已有有限版本的偏迹—记录通道恒等式。

有限参照作为量子资源的思想已有系统研究；这里的 \(\Lambda_c\) 是选定记录与约化协议的实现，而不是对全部关系编码方式的普遍限制。([arXiv][3])

### 物理实现边界

定理证明了一个有限等距实现存在。

如果进一步要求它保持某个指定 Hamiltonian 的总能量、满足空间局域性或具有有限操作成本，还必须补充相应实现。不能从“完全正”直接跳到“现实中可以免费执行”。

---

# 75．精确可识别、有限参照与可恢复性之间的严格分离

## 定理 75.1　指定能量差的有限支持上界

对整数 \(\ell\ge1\)，

$$
\boxed{
|\gamma_\ell|
\le
\cos\left(
\frac{\pi}{\lfloor N/\ell\rfloor+2}
\right).
}
\tag{75.1}
$$

该界可以达到。

### 证明

令 \(x_n=|c_n|\)。则

$$
|\gamma_\ell|
\le
\sum_nx_{n+\ell}x_n.
$$

构造实对称矩阵 \(T_\ell\)：当两个指标相差 \(\ell\) 时，矩阵元为 \(1/2\)，其他元素为零。

于是右侧为

$$
x^{\mathsf T}T_\ell x,
\qquad
\|x\|^2=1.
$$

该矩阵按指标模 \(\ell\) 的余数分解为若干路径图块。最长块具有

$$
m=\lfloor N/\ell\rfloor+1
$$

个节点。

一个 \(m\) 节点、相邻矩阵元为 \(1/2\) 的路径块，其本征值为

$$
\cos\frac{k\pi}{m+1},
\qquad
k=1,\ldots,m.
$$

故最大 Rayleigh 商为式（75.1）右侧。

在最长路径块上选取非负正弦本征向量，并令其他分量为零，即可达到等号。∎

---

## 定理 75.2　任意恢复操作的误差下界

设两个系统标签相差 \(\ell\ne0\)，并令

$$
v=|\gamma_\ell|.
$$

对任意恢复信道 \(\mathcal R\)，有

$$
\boxed{
\sup_\rho
D\bigl(\mathcal R\Lambda_c(\rho),\rho\bigr)
\ge
\frac{1-v}{2},
}
\tag{75.2}
$$

其中

$$
D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1.
$$

### 证明

取两态

$$
|\pm\rangle
=
\frac{|i\rangle\pm|j\rangle}{\sqrt2}.
$$

它们的迹距离为一，而

$$
D\bigl(\Lambda_c(\rho_+),\Lambda_c(\rho_-)\bigr)=v.
$$

量子通道不增加迹距离，因此

$$
D\bigl(\mathcal R\Lambda_c(\rho_+),
       \mathcal R\Lambda_c(\rho_-)\bigr)\le v.
$$

若最大恢复误差为 \(\varepsilon\)，三角不等式给出

$$
1\le\varepsilon+v+\varepsilon.
$$

整理即得。∎

---

## 推论 75.1　有限支持下的精确恢复障碍

对任何非零标签差，

$$
\boxed{
\sup_\rho
D\bigl(\mathcal R\Lambda_c(\rho),\rho\bigr)
\ge
\frac12
\left[
1-
\cos\left(
\frac{\pi}{\lfloor N/|\ell|\rfloor+2}
\right)
\right]
>0.
}
\tag{75.3}
$$

这里针对的是定义 74.1—74.2 的具体通道及任意 CPTP 恢复，不禁止通过不受该通道影响的简并子空间传输其他量子信息。

---

## 例 75.1　没有精确碰撞，却不能物理逆转

取

$$
c_n=\frac1{\sqrt{N+1}},
\qquad n=0,\ldots,N.
$$

则

$$
\gamma_\ell=
1-\frac{|\ell|}{N+1}
\qquad(|\ell|\le N).
$$

如果系统标签跨度不超过 \(N\)，全部相关 \(\gamma_\ell\) 非零。因此，式（74.2）在矩阵集合上单射：

$$
\Lambda_c(\rho)=\Lambda_c(\sigma)
\Longrightarrow
\rho=\sigma.
$$

但只要存在两个不同标签，定理 75.2 就排除完美物理恢复。

例如 \(N=2\)，两个标签相差一，则

$$
\gamma_1=\frac23,
$$

而

$$
\boxed{
\text{最坏情形恢复误差}\ge\frac16.
}
\tag{75.4}
$$

**这使项目中一个重要区别完全具体化：**

$$
\boxed{
\ker\Lambda_c=\Delta
}
$$

不意味着

$$
\boxed{
\exists\mathcal R\text{ 为量子信道},
\quad
\mathcal R\Lambda_c=\operatorname{id}.
}
$$

代数上的逆函数和物理上的恢复过程，必须分别证明。

---

# 76．观察者闭路中的相位与损耗不能混为曲率

现在研究多个观察者之间的一串标定或记录传递。

## 假设 76.1　独立实现的二能级边通道

每条有向边 \(e\) 具有通道

$$
\mathcal C_e
\begin{pmatrix}
a&b\\
\overline b&d
\end{pmatrix}
=
\begin{pmatrix}
a&z_eb\\
\overline{z_e}\,\overline b&d
\end{pmatrix},
$$

其中

$$
z_e=v_e e^{i\theta_e},
\qquad
0<v_e\le1.
$$

不同边使用已经明确准备的独立辅助资源，或已经在完整模型中证明可以这样分解。若重复使用仍然相关的同一参照，下面的简单乘积规律不自动成立。

---

## 定理 76.1　路径通道的相干乘法律

对路径 \(P=e_1\cdots e_m\)，

$$
\boxed{
z_P=\prod_{j=1}^m z_{e_j}.
}
\tag{76.1}
$$

因此

$$
\arg z_P=\sum_j\theta_{e_j}\pmod{2\pi},
$$

$$
-\log|z_P|=\sum_j-\log v_{e_j}.
$$

### 证明

每一步都在同一个非对角矩阵元上乘以对应系数，连续作用即得。∎

局部相位参照更名使

$$
z_{ij}\longmapsto
e^{i(\alpha_j-\alpha_i)}z_{ij}.
$$

沿闭路，相位更名相消，所以闭路乘积不变。

但这个不变量有两个独立部分：

$$
\boxed{
\text{闭路相位},
\qquad
\text{闭路相干模长}.
}
$$

---

## 定理 76.2　相位完全闭合仍可能有不可逆损耗

若一条闭路满足

$$
\sum_{e\in P}\theta_e=0\pmod{2\pi},
$$

令

$$
v_P=\prod_{e\in P}v_e.
$$

则

$$
\boxed{
\frac12
\|\mathcal C_P-\operatorname{id}\|_\diamond
=
\frac{1-v_P}{2}.
}
\tag{76.2}
$$

### 证明

零相位的通道可以写成

$$
\mathcal C_P
=
\frac{1+v_P}{2}\operatorname{id}
+
\frac{1-v_P}{2}\mathcal Z,
$$

其中

$$
\mathcal Z(\rho)=Z\rho Z.
$$

因此 diamond 距离不超过 \((1-v_P)/2\)。

对输入 \(|+\rangle\)，输出与原态的迹距离正好等于 \((1-v_P)/2\)，达到该界。∎

### 例

三条边都取

$$
z_e=\frac23.
$$

闭路相位严格为零，但

$$
v_P=\frac8{27},
$$

所以

$$
\boxed{
\frac12
\|\mathcal C_P-\operatorname{id}\|_\diamond
=
\frac{19}{54}.
}
\tag{76.3}
$$

**没有任何相位绕转，闭路实验仍然明显不返回原态。**

这构成一个明确反例：

$$
\boxed{
\text{闭路不返回原态}
\not\Rightarrow
\text{存在几何曲率}.
}
$$

因此，重建几何时，必须把“可逆参照输运的闭路差别”与“实际标定通道的不可逆损耗”分开。即使得到非平凡相位，也还需要证明它属于所研究的几何连接，而不是仪器相位。

---

# 77．共同钟速重建可以写成一个有限线性问题

上一轮给出了闭路乘积为一的精确判据。现在把它推进成带计算证书的形式。

## 定义 77.1　钟比较数据

取有限连通图，固定每条边的方向。实际实验已完成必要的相位解缠、频率估计和初值处理，给出正速率比 \(r_e\)。

定义

$$
a_e=\log r_e.
$$

若节点钟速为

$$
\nu_i=e^{x_i},
$$

则理想关系为

$$
a_e=x_{\mathrm{target}(e)}-x_{\mathrm{source}(e)}.
$$

选定一个根节点并固定 \(x_0=0\)。令 \(D\) 为删除根列后的关联矩阵，则

$$
\boxed{
a=Dx.
}
\tag{77.1}
$$

这一步的输入是已经标定的对数速率数据。不能把第 76 节的相干模长直接当作对数速率误差；二者之间需要具体估计协议的证明。

同步与参照恢复本身是已有的图上重建问题；本节使用其有限线性版本。([arXiv][4])

---

## 定理 77.1　精确共同钟速与回路相容性等价

下列命题等价：

$$
\exists x,\quad a=Dx;
$$

所有有向闭路上的 \(a_e\) 带符号和为零。

若有解，在固定根节点后解唯一。

### 证明

若 \(a=Dx\)，沿闭路求和，所有节点值相消。

反之，从根节点到各节点选取路径，把沿路的带符号和定义为 \(x_i\)。闭路和为零保证路径无关，因此 \(a=Dx\)。

唯一性来自：若 \(D(x-y)=0\)，则连通图上 \(x-y\) 为常数；根节点值固定后该常数为零。∎

---

## 推论 77.1　只有树状比较，无法检验共同钟速的一致性

若比较图是一棵树，则对任意边数据 \(a\)，都存在唯一的根固定解 \(x\)。

### 证明

树具有唯一的根到节点路径，因此可以无条件地沿路径定义 \(x_i\)。不存在独立闭路施加额外相容限制。∎

这是一个重要的实验结构结论：

> **仅有树状的静态钟比较，无论边数据是什么，都能被某个节点钟速表拟合。要检验共同时间描述的自洽性，必须加入独立闭路。**

这与九头蛇式证明树并不矛盾。证明树负责组织推理依赖；物理比较图的闭路负责提供可证伪的一致性条件。二者是不同类型的图。

---

# 78．近似共同时间：存在性、唯一性与稳定性证明

## 定义 78.1　加权共同时间拟合

给每条边一个正权重，组成对角矩阵

$$
W>0.
$$

定义目标函数

$$
J(x)=\|W^{1/2}(a-Dx)\|_2^2.
$$

令

$$
L_0=D^{\mathsf T}WD.
$$

由于图连通且根已固定，\(L_0>0\)。

---

## 定理 78.1　最优共同钟速的唯一性

唯一极小点为

$$
\boxed{
x_*=
L_0^{-1}D^{\mathsf T}Wa.
}
\tag{78.1}
$$

定义残差

$$
r=a-Dx_*,
$$

则

$$
\boxed{
D^{\mathsf T}Wr=0.
}
\tag{78.2}
$$

对任意 \(h\)，有

$$
\boxed{
J(x_*+h)
=
J(x_*)+\|W^{1/2}Dh\|_2^2.
}
\tag{78.3}
$$

### 证明

式（78.1）满足正规方程

$$
D^{\mathsf T}W(a-Dx_*)=0.
$$

展开 \(J(x_*+h)\)，交叉项因正规方程为零，得到式（78.3）。

由于 \(D\) 满列秩，第二项仅在 \(h=0\) 时为零，故极小点唯一。∎

---

## 定理 78.2　重建稳定性

若真实数据满足

$$
a=Dx_{\mathrm{true}}+\eta,
$$

则

$$
\boxed{
\|x_*-x_{\mathrm{true}}\|_2
\le
\frac{\|W^{1/2}\eta\|_2}
{\sqrt{\lambda_{\min}(L_0)}}.
}
\tag{78.4}
$$

### 证明

记

$$
h=x_*-x_{\mathrm{true}}.
$$

正规方程给出

$$
L_0h=D^{\mathsf T}W\eta.
$$

所以

$$
\|W^{1/2}Dh\|_2^2
=
\langle W^{1/2}Dh,W^{1/2}\eta\rangle
\le
\|W^{1/2}Dh\|_2\|W^{1/2}\eta\|_2.
$$

因此

$$
\|W^{1/2}Dh\|_2
\le
\|W^{1/2}\eta\|_2.
$$

再使用

$$
\|W^{1/2}Dh\|_2^2
=
h^{\mathsf T}L_0h
\ge
\lambda_{\min}(L_0)\|h\|_2^2,
$$

即得结论。∎

### 物理意义

同样大小的局部误差，在不同的观察者网络中，会产生不同的全局标定不确定性。

因此：

$$
\boxed{
\text{数学上有唯一共同时间拟合}
}
$$

并不意味着

$$
\boxed{
\text{该拟合在有限误差下可靠}.
}
$$

稳定性还取决于比较图及其权重所决定的谱尺度。

这里得到的是共同钟速场的重建，而不是完整空间度量。空间传播与方向输运仍然需要额外实验。

---

# 79．实际实验见证与数学证明，也必须保持类型区别

“推理结构都形式化”还要求阻止另一种跳跃：

$$
\text{有限次实验看起来一致}
\Longrightarrow
\text{物理模型精确相等}.
$$

这个推理一般不成立。

## 定理 79.1　有限样本不能无误认证任意 Bernoulli 参数的精确相等

固定 \(N<\infty\)，考虑未知参数

$$
p\in(0,1)
$$

的独立 Bernoulli 实验。

不存在一个固定有限样本判定器，同时满足：

* 在 \(p=p_0\) 时，以正概率输出“\(p=p_0\)”；
* 对所有 \(p\ne p_0\)，绝不错误输出这一结论。

### 证明

若在 \(p_0\) 下以正概率输出相等，则至少有一个长度为 \(N\) 的比特串触发该输出。

设该串有 \(k\) 个一，则它在任意 \(p\in(0,1)\) 下的概率为

$$
p^k(1-p)^{N-k}>0.
$$

因此，同一个串在 \(p\ne p_0\) 时也可能出现，判定器会以正概率误报。∎

---

## 定理 79.2　有限实验可以给出有证明的误差概率界

令

$$
\widehat p=\frac1N\sum_{i=1}^NX_i.
$$

则

$$
\mathbb E[\widehat p]=p,
$$

$$
\operatorname{Var}(\widehat p)
=
\frac{p(1-p)}N
\le\frac1{4N}.
$$

对任意 \(r>0\)，

$$
\boxed{
\Pr(|\widehat p-p|\ge r)
\le
\frac1{4Nr^2}.
}
\tag{79.1}
$$

### 证明

对非负随机变量 \((\widehat p-p)^2\) 使用 Markov 不等式：

$$
\Pr((\widehat p-p)^2\ge r^2)
\le
\frac{\mathbb E[(\widehat p-p)^2]}{r^2},
$$

再代入方差界。∎

### 形式化后应当怎样表达？

一个实际样本是 ANCHOR；概率误差界是关于实验模型的定理。

不能把

$$
\Pr(\text{误判})\le\alpha
$$

改写成

$$
\text{本次判断在逻辑上必然正确}.
$$

但可以严格证明：

$$
\boxed{
\text{在给定制备、独立性与噪声模型下，
这一有限程序的错误概率不超过 }\alpha.
}
$$

若存在环境记忆或制备相关性，独立 Bernoulli 假设就必须修改。形式化的作用是暴露这种依赖，而不是替我们消除它。

---

# 80．把整条推理组织成可检查的依赖链

本轮可以整理为下面的依赖结构：

| 推理层    | 必须提供的对象             | 本轮给出的结论            |
| ------ | ------------------- | ------------------ |
| 接口下降   | 完整映射、读数映射、交换证明      | 推理链组合正确、排除端点 carry |
| 量子实现   | Kraus 矩阵或等距实现及归一化证明 | 合法过程的复合仍合法         |
| 近似实现   | 完整参考系统下的通道误差证书      | 总实验误差受链式和控制        |
| 有限参照   | 有限系数、重叠核与实际约化协议     | 可识别性不等于物理可恢复性      |
| 多观察者传递 | 边通道及资源独立性条件         | 相位闭合与相干损耗分离        |
| 共同时间   | 有向比较图、边数据、根与权重      | 精确一致性、最优拟合及稳定性     |
| 实验锚定   | 制备模型、实际记录与统计定理      | 模型相对的误差保证，而非无条件真值  |

这里有三类不同的“闭合”，必须分别保存：

$$
\boxed{
\text{证明链闭合：每一步都有合法的推导依据};
}
$$

$$
\boxed{
\text{物理实现闭合：操作与资源在同一个模型里};
}
$$

$$
\boxed{
\text{观察者图谱闭合：不同接口的比较满足一致性条件}.
}
$$

它们互相支持，但不能彼此替代。

---

## 本轮的 Lean 对应

我生成了一个独立的候选 Lean 源码，包含：

`Interface`、`ExactStep`、保存步骤结构的 `Chain`、完整状态与读数两种执行语义，以及 `chain_sound`、链拼接和 `chain_has_no_carry` 的证明项。

[查看候选 Lean 源码](sandbox:/mnt/data/observer_formalization/ObserverInferenceCore.lean)

**该文件没有使用 `sorry` 或新增 `axiom`，但本轮未运行 Lean，因此不能报告它已通过内核检查。**它只覆盖精确接口链的基础部分，不代表本文的 diamond 范数、谱界和图重建定理已经全部 Lean 化。

本轮另外用精确符号运算核对了式（72.2）的量子反例、三边闭路的 \(8/27\) 相干因子与 \(19/54\) 距离，以及一个根固定图 Laplacian 的正定实例。这些计算不替代一般证明，也不等于 Lean 检查。

---

# 结论

你提出的“推理结构都应形式化”，在这一轮产生了一个实质性的理论要求：

> **任何从量子观察者走向物理时空的推导，都必须同时说明：哪些区别被保留、哪些操作真正存在、哪些误差被累积，以及哪些跨观察者关系具有可检验的一致性。**

这不仅是工程规范，也会改变物理判断。

我们已经得到：

$$
\boxed{
\text{接口单射}
\not\Rightarrow
\text{物理上可以无损恢复};
}
$$

$$
\boxed{
\text{闭路不返回原态}
\not\Rightarrow
\text{存在几何曲率};
}
$$

$$
\boxed{
\text{钟速数据可以拟合}
\not\Rightarrow
\text{共同时间已经受到有效检验};
}
$$

$$
\boxed{
\text{有限实验未发现差异}
\not\Rightarrow
\text{模型精确等价}.
}
$$

同时，每一项否定都有正向替代：物理恢复证书、相位—损耗分解、带独立闭路的比较网络，以及有概率保证的实验程序。

**因此，量子观察者理论的下一层不是再添加一种“时间本质”，而是把“共同物理时间如何由有限量子观察者可靠建立”变成一个完整的、带证明的重建过程。**

只有当这个过程与共同信号传播、空间输运和能量反作用继续相容时，最终得到的时空才不是一个任意解释，而是受到整条形式化推理链约束的物理结构。

[1]: https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/?utm_source=chatgpt.com "Propositions"
[2]: https://arxiv.org/abs/1301.3662?utm_source=chatgpt.com "Composable security of delegated quantum computation"
[3]: https://arxiv.org/abs/quant-ph/0610030?utm_source=chatgpt.com "Reference frames, superselection rules, and quantum information"
[4]: https://arxiv.org/abs/0905.3174?utm_source=chatgpt.com "Angular Synchronization by Eigenvectors and Semidefinite Programming"
# 共享量子参照、闭路记忆与几何曲率的可认证重建

## ——量子观察者—关系时空理论第八十一至第九十节增订

### 摘要

前文已经建立有限参照、量子通道误差和共同钟速重建。本增订处理一个影响整个理论闭合性的关键问题：

> **同一个量子参照被连续使用时，能够把每一步单独观察到的通道直接相乘吗？若不能，观察者怎样区分参照记忆、相干损耗与真正的几何输运？**

本文给出一个精确反例：三条边单独读取时都表现为完全退相干，但共享参照的完整闭路可以严格恢复全部相干。因此，单步通道不足以确定闭路实验。

随后建立三组结果：

$$
\boxed{
\text{纯参照更名}
\iff
\text{适当条件下全部闭路输运为恒等};
}
$$

$$
\boxed{
\text{闭路干涉读数}
\longrightarrow
\text{完整往返算子的定量证书};
}
$$

$$
\boxed{
\text{量子输运结构}
+\text{钟尺标定}
+\text{几何相容条件}
\longrightarrow
\text{度量连接与曲率}.
}
$$

其中，关于共享环境和多时刻过程的区分已有成熟的非马尔科夫量子过程理论；本增订将其落实到项目的接口下降、参照网络和几何重建中。([arXiv][1])

---

# 81．单步通道不是完整的连续交互过程

## 定义 81.1　带共享参照的完整过程

设 \(S\) 为被读取的量子系统，\(R\) 为观察者使用的参照或记忆寄存器。初态为

$$
\rho_S\otimes\sigma_R.
$$

连续操作为联合酉算子

$$
U_1,\ldots,U_n
\]

作用于同一个

$$

\mathcal H_S\otimes\mathcal H_R.

$$

完整的终点通道为

$$

\boxed{
\Phi_{1:n}(\rho)
================

\operatorname{Tr}_R
\left[
U_n\cdots U_1
(\rho\otimes\sigma_R)
U_1^\dagger\cdots U_n^\dagger
\right].
}
\tag{81.1}

$$

另一方面，把每一步单独拿出来、每次重新准备参照态 \(\sigma_R\)，得到

$$

\boxed{
\Phi_j(\rho)
============

\operatorname{Tr}_R
\left[
U_j(\rho\otimes\sigma_R)U_j^\dagger
\right].
}
\tag{81.2}

$$

式（81.1）与

$$

\Phi_n\circ\cdots\circ\Phi_1

$$

描述的通常不是同一个实验。

---

## 命题 81.1　约化与过程组合一般不交换

一般不存在恒等式

$$

\boxed{
\Phi_{1:n}
==========

\Phi_n\circ\cdots\circ\Phi_1.
}
\tag{81.3}

$$

### 证明

式（81.2）的复合等价于每一步丢弃旧参照并重新提供相应初态。

而式（81.1）中，参照在前一步之后可能已经改变，并与系统相关。因此，两式具有不同的中间状态。下一节给出两者不同的精确有限维见证。∎

### 对项目推理链的影响

前文的精确推理链定理仍然成立：

$$

q_{j+1}F_j=\overline F_jq_j

$$

一旦对全部合法中间状态成立，就可以安全组合。

问题在于：**单独实验中拟合出的 \(\Phi_j\)，不自动提供这一交换证明。**

项目 `ExactDescentNoCarry.lean` 要求实际给出下降等式，再推出不存在 carry。它没有允许用一次局部拟合代替所有中间状态上的证明。

因此，共享参照必须进入完整状态类型；否则，推理链可能在每个孤立步骤都“看起来正确”，但组合后失效。

---

# 82．一个精确反例：三条退相干边构成完全相干的闭路

## 定义 82.1　有限共享参照

取一个探针量子比特 \(S\)，以及三个参照量子比特：

$$

R=R_0R_1R_2.

$$

初始参照态为

$$

|r_0\rangle=|+\rangle^{\otimes3}.

$$

令 \(Z_i\) 为作用于第 \(i\) 个参照比特的 Pauli \(Z\) 算子，定义

$$

W_{10}=Z_1Z_0,

$$
$$

W_{21}=Z_2Z_1,

$$
$$

W_{02}=Z_0Z_2.

$$

每条边通过探针控制：

$$

\boxed{
U_{ji}
======

|0\rangle\langle0|_S\otimes I_R
+
|1\rangle\langle1|*S\otimes W*{ji}.
}
\tag{82.1}

$$

这些都是明确的有限维酉操作。

---

## 定理 82.1　每条边单独表现为完全退相干

若每次单独实施一条边，参照都准备在 \(|r_0\rangle\)，则探针通道为

$$

\boxed{
\Delta
\begin{pmatrix}
a&b\
\overline b&d
\end{pmatrix}
=============

\begin{pmatrix}
a&0\
0&d
\end{pmatrix}.
}
\tag{82.2}

$$

### 证明

受控操作后的非对角项乘以

$$

\langle r_0|W_{ji}|r_0\rangle

$$

或其共轭。

由于

$$

\langle+|Z|+\rangle=0,

$$

三条边对应的该重叠都为零。∎

这正是项目环境记录模型的结构：局部相干项乘以两个条件记录态的重叠。

---

## 定理 82.2　共享参照的三边闭路严格为恒等

对同一个参照依次实施三条边，有

$$

\boxed{
U_{02}U_{21}U_{10}=I_{SR}.
}
\tag{82.3}

$$

因此，完整闭路的探针通道为恒等，而不是 \(\Delta\)。

### 证明

三个受控操作的控制投影相同，所以其乘积在 \(|1\rangle_S\) 分支上作用为

$$

\begin{aligned}
W_{02}W_{21}W_{10}
&=(Z_0Z_2)(Z_2Z_1)(Z_1Z_0)\
&=I_R.
\end{aligned}

$$

在 \(|0\rangle_S\) 分支上原本就是恒等。∎

---

## 定理 82.3　相同单边通道可以对应不同闭路

另取三个受控参照操作：

$$

\widetilde W_1=Z_0,\qquad
\widetilde W_2=Z_1,\qquad
\widetilde W_3=Z_2.

$$

每一步的单独探针通道仍为 \(\Delta\)，但完整三步通道为 \(\Delta\)，而不是恒等。

### 证明

每个单独操作的参照期望为零。

完整乘积为

$$

Z_2Z_1Z_0,

$$

其在 \(|+\rangle^{\otimes3}\) 上的期望仍为零。因此最终探针相干消失。∎

对探针输入 \(|+\rangle\)，两种过程的最终态分别是

$$

|+\rangle\langle+|,
\qquad
\frac I2,

$$

迹距离为

$$

\boxed{\frac12.}
\tag{82.4}

$$

### 项目化表达

令模型接口只保存三条单边通道：

$$

# q_{\mathrm{edge}}(\mathfrak M)

(\Phi_1,\Phi_2,\Phi_3),

$$

目标为完整闭路通道：

$$

T_{\mathrm{loop}}(\mathfrak M)=\Phi_{1:3}.

$$

上面的两个模型满足

$$

# q_{\mathrm{edge}}(\mathfrak M_1)

q_{\mathrm{edge}}(\mathfrak M_2),

$$

但

$$

T_{\mathrm{loop}}(\mathfrak M_1)
\ne
T_{\mathrm{loop}}(\mathfrak M_2).

$$

因此

$$

\boxed{
\operatorname{Residual}
(q_{\mathrm{edge}},T_{\mathrm{loop}})
\ne\varnothing.
}
\tag{82.5}

$$

**遗漏的不是某条边的测量精度，而是边与边之间共享的参照关联。**

---

# 83．纯参照更名为什么不能产生真实的路径依赖？

现在从具体量子比特推广到任意有限维可逆输运。

## 假设 83.1　可逆参照网络

取连通图，节点表示参照配置。每条有向边 \(i\to j\) 对应酉映射

$$

U_{ji}:\mathcal H_i\to\mathcal H_j,

$$

各纤维维数相同，并要求反向边真正实现逆映射：

$$

U_{ij}=U_{ji}^{-1}.

$$

这里“闭路”指实验配置或空间路径的闭合，不表示返回过去的同一个物理事件。沿途的实际动力学必须被包括在边映射内，或由另行证明的校准程序扣除。

对路径

$$

P:i_0\to i_1\to\cdots\to i_n,

$$

定义

$$

U_P=U_{i_ni_{n-1}}\cdots U_{i_1i_0}.

$$

---

## 定义 83.1　纯参照更名

若存在从同一个参考纤维到各节点的酉映射

$$

G_i:\mathcal H_*\to\mathcal H_i,

$$

使

$$

\boxed{
U_{ji}=G_jG_i^{-1},
}
\tag{83.1}

$$

则称该网络输运仅来自参照更名。

---

## 定理 83.1　纯更名的端点定理

若式（83.1）成立，则

$$

\boxed{
U_P=G_{i_n}G_{i_0}^{-1}.
}
\tag{83.2}

$$

特别地，每条闭路满足

$$

\boxed{U_P=I.}
\tag{83.3}

$$

### 证明

逐项相乘：

$$

(G_{i_n}G_{i_{n-1}}^{-1})
(G_{i_{n-1}}G_{i_{n-2}}^{-1})
\cdots
(G_{i_1}G_{i_0}^{-1}).

$$

相邻逆映射消去，得到式（83.2）。

该证明不要求不同的 \(G_i\) 彼此可交换。∎

### 结论

非交换的局部参照变换，本身仍然可以只有平凡闭路。

因此：

$$

\boxed{
\text{局部操作不交换}
\not\Rightarrow
\text{闭路非平凡}
\not\Rightarrow
\text{时空弯曲}.
}

$$

项目的 `WormholeHolonomy.lean` 已经明确区分一般往返映射与微分几何 holonomy，并证明真正的左逆使往返等于恒等。本节将两节点往返推广为整个参照网络。

---

# 84．有限个基本闭路足以认证整个有限网络

## 定义 84.1　树参照与基本闭路

在有限连通图中选定根节点 \(0\) 和一棵生成树。

令 \(P_i\) 为树上从根到节点 \(i\) 的唯一路径，并定义

$$

G_i=U_{P_i}.

$$

对任意边 \(e:i\to j\)，定义根纤维上的闭路算子

$$

\boxed{
H_e=G_j^{-1}U_{ji}G_i.
}
\tag{84.1}

$$

它对应：从根沿树到 \(i\)，经过 \(e\) 到 \(j\)，再沿树逆向回到根。

---

## 定理 84.1　有限网络的纯更名判据

以下条件等价：

1. 全部闭路输运为恒等；
2. 存在式（83.1）的参照表示；
3. 每条非树边的 \(H_e\) 都等于恒等。

### 证明

\(2\Rightarrow1\) 由定理 83.1。

\(1\Rightarrow3\) 因 \(H_e\) 本身就是闭路。

若 \(3\) 成立，树边根据 \(G_i\) 的定义已经满足

$$

U_{ji}=G_jG_i^{-1}.

$$

对非树边，由 \(H_e=I\) 得到同一等式。因此 \(2\) 成立。∎

若图有 \(v\) 个节点、\(e\) 条无向边，则只需认证

$$

e-v+1

$$

个非树边基本闭路。

### 边界

这是对给定有限图的完整闭路认证。

若只检查某些“小面”边界，而图所在空间还具有非收缩回路，则小回路平凡不必意味着所有全局闭路平凡。局部曲率与全局拓扑仍然需要区分。

---

# 85．怎样由量子干涉读数认证一个闭路算子？

设两个路径 \(P,Q\) 起终点相同。定义相对输运

$$

H=U_Q^\dagger U_P.

$$

它是作用在起点纤维上的酉算子。

## 定义 85.1　路径比较实验

准备路径控制比特 \(|+\rangle\)，以及纤维态 \(\rho\)。在两个控制分支上分别实施 \(U_Q,U_P\)。

丢弃纤维后，控制比特状态为

$$

\boxed{
\rho_{\mathrm{ctrl}}
====================

\frac12
\begin{pmatrix}
1&\overline\gamma\
\gamma&1
\end{pmatrix},
\qquad
\gamma=\operatorname{Tr}(\rho H).
}
\tag{85.1}

$$

相位为 \(\alpha\) 的分析测量给出

$$

\boxed{
P_+(\alpha)
===========

\frac12
\left[
1+\operatorname{Re}(e^{-i\alpha}\gamma)
\right].
}
\tag{85.2}

$$

这类通过混合态酉期望读取干涉相位与可见度的方案具有标准量子干涉实现；把其中的相位进一步称为“几何相位”，仍需控制动力学相位和输运条件。:contentReference[oaicite:4]{index=4}

---

## 定理 85.1　闭路读数的两个精确恒等式

令 Hilbert–Schmidt 范数为 \(\|\cdot\|_2\)，则

$$

\boxed{
|(H-\gamma I)\rho^{1/2}|_2^2
============================

1-|\gamma|^2,
}
\tag{85.3}

$$

以及

$$

\boxed{
|(H-I)\rho^{1/2}|_2^2
=====================

2\bigl(1-\operatorname{Re}\gamma\bigr).
}
\tag{85.4}

$$

### 证明

使用

$$

H^\dagger H=I,\qquad \operatorname{Tr}\rho=1

$$

及迹的循环性。

例如，

$$

\begin{aligned}
&\operatorname{Tr}
\left[
\rho(H-\gamma I)^\dagger(H-\gamma I)
\right]\
&=1-\gamma\overline\gamma
-\overline\gamma\gamma+|\gamma|^2\
&=1-|\gamma|^2.
\end{aligned}

$$

第二式同理。∎

---

## 推论 85.1　可见度一不等于闭路恒等

若

$$

|\gamma|=1,

$$

只能推出

$$

H=\gamma I

$$

在 \(\rho\) 的支持上成立。

例如

$$

H=-I

$$

具有完整可见度，却给出相位 \(\pi\)。

如果 \(\rho\) 不满秩，即使 \(\gamma=1\)，也不能确定 \(H\) 在支持之外的作用。

因此，**只看干涉条纹是否清晰，不能认证闭路恒等；还要测量相位，并控制测试态覆盖的空间。**

---

## 定理 85.2　满秩测试态给出算子级稳定性界

若

$$

\rho\ge\mu I,\qquad \mu>0,

$$

则

$$

\boxed{
|H-I|_{\mathrm{op}}
\le
\sqrt{
\frac{2(1-\operatorname{Re}\gamma)}{\mu}
}.
}
\tag{85.5}

$$

特别地，

$$

\boxed{
\gamma=1\iff H=I.
}
\tag{85.6}

$$

### 证明

由 \(\rho\ge\mu I\)，

$$

\begin{aligned}
\mu|H-I|_2^2
&\le
\operatorname{Tr}
\left[
\rho(H-I)^\dagger(H-I)
\right]\
&=2(1-\operatorname{Re}\gamma).
\end{aligned}

$$

再使用

$$

|H-I|_{\mathrm{op}}\le|H-I|_2.

$$

∎

这使一个实验平均值与完整算子性质之间出现了明确桥梁。

代价也十分清楚：当 \(\mu\) 很小时，认证变得不稳定。若使用

$$

\rho=I/d,

$$

则 \(\mu=1/d\)，误差界显式依赖被认证空间的维数。

---

# 86．有限闭路读数如何控制任意有限路径？

## 假设 86.1　基本闭路的误差证书

对第 84 节的每个非树边闭路，假设已经得到

$$

|H_e-I|_{\mathrm{op}}\le\epsilon_e.

$$

树边的相应误差取零。反向边使用真正的逆算子，故误差相同。

---

## 定理 86.1　路径误差的可组合上界

对任意从 \(a\) 到 \(b\) 的路径 \(P\)，有

$$

\boxed{
|U_P-G_bG_a^{-1}|*{\mathrm{op}}
\le
\sum*{e\in P}\epsilon_e,
}
\tag{86.1}

$$

其中重复经过的边按次数计入。

### 证明

在树参照中，每条边变为

$$

\widetilde U_e=G_{\mathrm{target}(e)}^{-1}
U_eG_{\mathrm{source}(e)}.

$$

树边为恒等，其他边为 \(H_e\) 或 \(H_e^{-1}\)。

对酉算子乘积使用望远镜展开：

$$

# A_m\cdots A_1-I

\sum_{j=1}^m
A_m\cdots A_{j+1}(A_j-I).

$$

取算子范数，利用每个酉算子的范数为一，再变回原参照即可。∎

---

## 推论 86.1　由干涉读数得到路径证书

若所有基本闭路均使用同一个已标定测试态

$$

\rho\ge\mu I,

$$

并证明

$$

1-\operatorname{Re}\operatorname{Tr}(\rho H_e)\le\delta_e,

$$

则

$$

\boxed{
|U_P-G_bG_a^{-1}|*{\mathrm{op}}
\le
\sum*{e\in P}
\sqrt{\frac{2\delta_e}{\mu}}.
}
\tag{86.2}

$$

这是一条可以逐步形式化的完整链：

$$

\boxed{
\text{有限统计证书}
\rightarrow
\text{基本闭路算子界}
\rightarrow
\text{任意指定有限路径的误差界}.
}

$$

但有限测量不会直接产生精确的 \(\delta_e=0\)。实际证书应保留测量误差和失败概率。

此外，式（86.2）不提供对任意长路径统一不变的误差。路径增长时，误差预算一般也增长。

---

# 87．小闭路同时读取输运生成元的均值与涨落

现在研究一种明确的小闭路极限。

## 假设 87.1　有控制的小闭路展开

设 \(h>0\) 表示闭路的线性尺度，在固定有限维空间中，

$$

\boxed{
H(h)=I-ih^2F+O(h^3)
}
\tag{87.1}

$$

按算子范数成立，且

$$

F=F^\dagger.

$$

这里 \(F\) 是闭路领先阶的 Hermitian 生成元。只有在进一步建立几何实现后，才能将它识别为某种曲率在所用表示中的分量。

令

$$

\gamma(h)=\operatorname{Tr}[\rho H(h)],

$$
$$

m=\operatorname{Tr}(\rho F).

$$

---

## 定理 87.1　闭路相位与可见度的不同阶次

在上述条件下，

$$

\boxed{
\arg\gamma(h)
=============

-h^2m+O(h^3),
}
\tag{87.2}

$$

以及

$$

\boxed{
1-|\gamma(h)|^2
===============

h^4
\left[
\operatorname{Tr}(\rho F^2)-m^2
\right]
+
O(h^5).
}
\tag{87.3}

$$

另外，

$$

\boxed{
2\bigl(1-\operatorname{Re}\gamma(h)\bigr)
=========================================

h^4\operatorname{Tr}(\rho F^2)+O(h^5).
}
\tag{87.4}

$$

### 证明

式（87.1）给出

$$

\gamma(h)=1-ih^2m+O(h^3),

$$

从而得到式（87.2）。

又有

$$

# H(h)-\gamma(h)I

-ih^2(F-mI)+O(h^3).

$$

代入定理 85.1，平方后得到式（87.3）。

同样，

$$

H(h)-I=-ih^2F+O(h^3),

$$

代入式（85.4）得到式（87.4）。∎

---

## 例 87.1　平均相位为零，闭路仍然非平凡

取

$$

F=
\begin{pmatrix}
1&0\
0&-1
\end{pmatrix},
\qquad
\rho=\frac I2,

$$

以及

$$

H(h)=e^{-ih^2F}.

$$

则

$$

\operatorname{Tr}(\rho F)=0,

$$

但

$$

\gamma(h)=\cos(h^2).

$$

因此

$$

\boxed{
1-|\gamma(h)|^2
===============

# \sin^2(h^2)

h^4+O(h^8).
}
\tag{87.5}

$$

所以：

$$

\boxed{
\text{平均相位没有偏移}
\not\Rightarrow
\text{闭路算子为恒等}.
}

$$

反过来，若 \(F=fI\)，则可见度保持一，但存在相位变化。

### 解释边界

式（87.3）的方差既可能来自测试态的混合，也可能来自其与其他自由度的关联。仅凭一项可见度实验，不能断言已经测到了“量子时空涨落”。

真正成立的是：**相位与可见度读取同一个闭路算子的不同统计量，二者不能互相替代。**

---

# 88．相干回归为什么不与“观察者形成记忆”矛盾？

第 82 节中，中间阶段的探针相干消失，最终又全部恢复。这是否意味着记录可以被无代价复制后还保留原始相干？

答案是否定的。

## 定义 88.1　额外的分支记录

假设某个阶段的联合态为

$$

# |\Psi\rangle

\frac{
|0\rangle|e_0\rangle|m_0\rangle
+
|1\rangle|e_1\rangle|m_1\rangle
}{\sqrt2}.

$$

其中 \(e\) 是后续仍被操控的参照，\(m\) 是不再参与回声操作的附加记录。

若后续操作将参照部分恢复为同一个态：

$$

|0\rangle|e_0\rangle\mapsto|0\rangle|e_*\rangle,

$$
$$

|1\rangle|e_1\rangle\mapsto|1\rangle|e_*\rangle,

$$

则最终态为

$$

\frac{
|0\rangle|m_0\rangle+
|1\rangle|m_1\rangle
}{\sqrt2}
\otimes|e_*\rangle.

$$

---

## 定理 88.1　未撤销的可区分记录限制相干回归

最终探针可见度为

$$

\boxed{
\mathcal V=|\langle m_1|m_0\rangle|.
}
\tag{88.1}

$$

若附加记录能够完美区分两个探针分支，即

$$

\langle m_1|m_0\rangle=0,

$$

则仅恢复参照 \(e\) 不能恢复探针相干。

### 证明

对记录 \(m\) 取偏迹，直接读取探针密度矩阵的非对角项。∎

因此，第 82 节的完整回归意味着相关的分支区别被重新相干组合，而不是在外部留下了一份永久、完美可读的分支记录。

**这把“记忆”与“几何比较”放到同一个资源账本中：**

若观察者把某些路径信息永久写入不受控制的记录，就改变了后续能够实施的干涉实验。

但不是任何记录都会破坏干涉。只有能够区分所比较分支的记录，才通过式（88.1）起作用。

这种关联依赖必须保留在完整多时刻过程里，不能只用每一步的约化密度矩阵替代。:contentReference[oaicite:5]{index=5}

---

# 89．从量子闭路到时空曲率，还需要一个明确的几何连接定理

至此，我们得到的是量子输运算子及其可测闭路。它还不自动是时空曲率。

例如，在固定坐标标签下，

$$

g_1=-dt^2+dx^2+dy^2+dz^2,

$$

与

$$

g_2=-4dt^2+dx^2+dy^2+dz^2

$$

都具有零连接系数和零曲率，却给同一组未重标定的坐标钟尺不同读数。

因此，**输运闭路本身不足以确定钟尺尺度和度量。**

下面给出补足这一缺口的条件性定理。

## 假设 89.1　钟尺标定与参照连接

在一个已建立光滑极限的局部事件区域，设：

1. 有可逆的钟尺标定矩阵
$$

e(x)=\bigl(e^a{}_\mu(x)\bigr);

$$
2. 内部标定空间具有已经由共同信号与钟确定的 Lorentz 型二次型
$$

\eta=\operatorname{diag}(-1,1,\ldots,1);

$$
3. 参照连接 \(\omega_\mu\) 满足
$$

\boxed{
\omega_\mu^{\mathsf T}\eta+\eta\omega_\mu=0;
}
\tag{89.1}

$$
4. 钟尺标定满足无挠相容条件
$$

\boxed{
\partial_\mu e_\nu-\partial_\nu e_\mu
+\omega_\mu e_\nu-\omega_\nu e_\mu=0.
}
\tag{89.2}

$$

其中 \(e_\nu\) 是矩阵 \(e\) 的第 \(\nu\) 列。

这些是需要由具体实现提供的几何数据，不是从一个任意有限维酉矩阵直接生成的对象。

---

## 定理 89.1　标定与连接重建唯一的度量相容无挠连接

定义

$$

\boxed{
g=e^{\mathsf T}\eta e,
}
\tag{89.3}

$$

以及

$$

\boxed{
\Gamma_\mu
==========

e^{-1}(\partial_\mu e+\omega_\mu e).
}
\tag{89.4}

$$

则：

- \(g\) 是非退化 Lorentz 型度量；
- \(\Gamma\) 与 \(g\) 相容；
- \(\Gamma\) 无挠；
- 因而 \(\Gamma\) 是 \(g\) 的 Levi–Civita 连接。

其曲率满足

$$

\boxed{
R_{\mu\nu}(\Gamma)
==================

e^{-1}
F_{\mu\nu}(\omega)e,
}
\tag{89.5}

$$

其中

$$

# F_{\mu\nu}(\omega)

\partial_\mu\omega_\nu-\partial_\nu\omega_\mu
+
[\omega_\mu,\omega_\nu].

$$

### 证明

由于 \(e\) 可逆，式（89.3）由合同变换保持非退化性与符号类型。

使用式（89.1），计算得

$$

# \partial_\mu g

\Gamma_\mu^{\mathsf T}g+g\Gamma_\mu,

$$

故度量相容。

由式（89.4），连接的挠率分量为

$$

## \Gamma^\lambda{}_{\mu\nu}

# \Gamma^\lambda{}_{\nu\mu}

(e^{-1})^\lambda{}*a
\left[
\partial*\mu e^a{}*\nu-\partial*\nu e^a{}*\mu
+
(\omega*\mu e_\nu-\omega_\nu e_\mu)^a
\right].

$$

式（89.2）使其为零。

度量相容无挠连接的唯一性给出 Levi–Civita 识别。最后对式（89.4）求导并展开交换子，得到式（89.5）。∎

这是标准标架几何的条件构造；其作用是明确说明，从参照输运走向时空曲率究竟需要哪些额外数据。:contentReference[oaicite:6]{index=6}

### 对量子模型的额外要求

有限维内部酉连接作用于量子态空间，而 \(\omega_\mu\) 作用于钟尺标架空间。

二者不是同一个类型。

若希望第 87 节测到的 \(F\) 表示式（89.5）的曲率，必须给出具体表示或耦合，并证明：

$$

\boxed{
\text{量子实验统计}
=============

\text{该几何输运在相应表示中的实验统计}.
}

$$

不能把 Hilbert 空间指标直接当作时空指标，也不能仅因都出现交换子就宣布两种曲率相同。

---

# 90．可形式化的完整依赖链

本轮的推理可以整理为以下依赖关系：

$$

\boxed{
\text{带共享参照的联合实现}
\rightarrow
\text{完整路径输运}
\rightarrow
\text{闭路干涉读数}
\rightarrow
\text{算子误差证书}.
}

$$

再经过：

$$

\boxed{
\text{基本闭路认证}
\rightarrow
\text{有限网络一致性}
\rightarrow
\text{小闭路生成元}
\rightarrow
\text{有钟尺标定的几何实现}.
}

$$

这比“观察者绕一圈发现状态变化，所以存在曲率”多了必要的中间证明。

## 90.1　与项目已有结构的对应

| 项目结构 | 本增订中的明确对象 |
|---|---|
| **CUT** | 单边通道、完整多时刻过程、干涉标量 \(\gamma\)、算子级输运 |
| **FLOW** | 对共享参照的实际联合酉操作与路径复合 |
| **ADMIT** | 逆操作可实现、测试态支持、误差预算、钟尺和连接相容条件 |
| **ANCHOR** | 参照制备、相位分析结果、闭路实验及统计证书 |
| **Residual** | 单边读数不能确定闭路、单态读数不能覆盖全部空间、输运不能独自确定度量 |

`WormholeHolonomy.lean` 已明确声明其往返概念只是类型化动力网络中的集合论输运，不自行识别为微分几何 holonomy。这个边界应当继续保留。

## 90.2　本轮的形式化文件

在不修改上一份源码的前提下，我新增了一个候选 Lean 文件，包含：

- 带左右逆证明的参照结构；
- 起终点具有类型约束的路径；
- 纯参照输运的端点公式、路径无关性与闭路恒等；
- 一个完整可逆、但单步可见接口不能自治下降的记忆回声实例。

[候选 Lean 源码：ObserverReferenceTransport.lean](sandbox:/mnt/data/observer_formalization/ObserverReferenceTransport.lean)

当前环境没有可用的 Lean 编译器，因此该文件仍是**未编译的候选证明源码**，不标记为内核已验证。它也不声称覆盖本文的矩阵范数、小闭路渐近和微分几何定理。

三参照反例、闭路相干、加权算子恒等式及小闭路例子已经进行了精确符号核验；这些核验可由下面的脚本复现，但不替代一般 Lean 证明：

[精确算例核验脚本](sandbox:/mnt/data/observer_formalization/check_reference_holonomy.py)

---

# 结论

本轮最重要的推进，是纠正一种容易让整个理论失去自洽性的组合方式：

$$

\boxed{
\text{每一步的可见通道}
\quad
\text{不必决定}
\quad
\text{完整闭路的可见过程}.
}

$$

原因不是量子规律不一致，而是观察者使用的参照与记忆可能在不同步骤之间持续保留关联。

由此，我们获得三项明确结论。

**第一，共享参照可以使中间不可见的相干在闭路末端重新可见。**这要求完整记录结构参与推理，不能逐步丢弃关联后还期待得到相同物理。

**第二，几何认证需要比“观察到相位”或“状态没有返回”更强的证书。**对于满秩测试态，干涉读数可以转化为算子级误差界；有限组基本闭路又可以控制整个有限网络。

**第三，量子输运仍然必须与实际钟尺结构连接，才能被识别为时空曲率。**纯参照更名、不可逆通道、内部几何相位和时空 Levi–Civita 曲率，应当作为不同类型处理，并由定理建立联系。

因此，量子观察者理论的下一层可以用一句严格的话概括：

> **物理时空不是观察者对单次数据的任意解释，而是完整交互、共享参照、闭路比较与钟尺标定能够共同通过的一种几何实现。**

这里“共同通过”不只是哲学上的协调，而是明确的交换等式、正性条件、范数界、路径证书与几何相容方程。只有这些条件同时成立，时空才成为这套量子观察结构可认证、可预测的有效对象。
$$

[1]: https://arxiv.org/abs/1801.09811?utm_source=chatgpt.com "Operational Markov condition for quantum processes"
# 从量子钟响应重建洛伦兹度量

## ——可识别性、有限读数、跨观察者拼接与量子失配

### 量子观察者—关系时空理论第九十一至第一百节增订

### 摘要

前文已经建立量子参照、闭路输运与几何连接之间的条件关系，但其中的钟尺标定矩阵仍主要作为给定对象使用。本增订进一步研究：

> **能否不先给定时空度量，而从观察者在不同交互方向上的量子钟读数，重建度量本身？**

本文给出一个明确答案。

在已经建立局部可微记录坐标、并且量子钟能够作确定性钟速描述的条件下，若**平方钟速是控制方向的严格凹二次函数**，则它唯一确定一个洛伦兹度量。在 \(3+1\) 维局部模型中，这个二次型可以由十个适当选择的钟速值重建。

同时证明四项限制：

**量子 Fisher 信息不是洛伦兹度量；十个读数只能在二次模型类内保证唯一性；单点度量及单条世界线上的一阶数据不确定曲率；平均钟速与共同光锥同时相容，也不保证完整量子过程能够由一张确定的经典时空描述。**

用钟群重建几何具有已有的“钟罗盘”研究基础。本文采用不同的组织次序：先定义量子过程读数，再证明它何时通过一个局部度量因子化，并将识别误差与模型失配分开。([APS Journals][1])

---

# 91．先区分两种不同的“几何”

## 定义 91.1　量子态的统计几何

设参数态族为 \(\rho_\theta\)，对称对数导数 \(L_\alpha\) 满足

$$
\partial_\alpha\rho
=
\frac12(L_\alpha\rho+\rho L_\alpha).
$$

量子 Fisher 信息矩阵为

$$
J_{\alpha\beta}
=
\operatorname{Re}\operatorname{Tr}(\rho L_\alpha L_\beta).
$$

它控制参数估计的局部可分辨性，是量子计量中的统计对象。([APS Journals][2])

## 定理 91.1　统计正性不能通过实坐标变换变成洛伦兹符号

对任意实向量 \(a\)，

$$
\boxed{
a^\mathsf TJ a\ge0.
}
\tag{91.1}
$$

因此，无论进行何种可逆实参数变换，\(J\) 都不能直接变成具有一个负方向的非退化洛伦兹度量。

### 证明

令

$$
L_a=\sum_\alpha a_\alpha L_\alpha.
$$

则

$$
a^\mathsf TJa
=
\operatorname{Tr}(\rho L_a^2)\ge0.
$$

实参数变换的 Jacobian 为 \(T\) 时，

$$
J'=T^\mathsf TJT
$$

仍然半正定。∎

### 结论

$$
\boxed{
\text{哪些参数容易被量子实验区分}
}
$$

与

$$
\boxed{
\text{哪些事件方向是类时、类光或类空}
}
$$

是不同问题。

量子 Fisher 信息可以控制度量重建的精度，但不能仅凭“它也是一个矩阵”，就被直接认定为时空度量。

---

## 假设 91.1　局部记录坐标与理想钟过程

采用前文已经建立的一个局部可微记录图：

$$
x=(t,x^1,\ldots,x^d).
$$

这里的维数 \(d\) 是当前模型的输入；本节不声称已经从观察者存在性中唯一推出三维空间。

在事件 \(p\) 附近，允许一族可重复的局部运动或转移协议，其坐标方向记为

$$
v=\frac{dx}{dt}\in U_p\subset\mathbb R^d.
$$

\(v\) 首先是记录坐标中的变化率，不预先使用某个度量来定义它的物理长度。

设经过实际制备和控制检验后，某个有限维钟在该协议下具有局部有效动力学

$$
\boxed{
\mathcal E_{p,v,\Delta t}(\rho)
=
e^{-iH_Cn_p(v)\Delta t/\hbar}
\rho
e^{iH_Cn_p(v)\Delta t/\hbar},
}
\tag{91.2}
$$

其中

$$
n_p(v)>0.
$$

式（91.2）要求对全部允许钟初态成立，而不只是对一个平均相位成立。

定义平方钟速：

$$
\boxed{
r_p(v)=n_p(v)^2.
}
\tag{91.3}
$$

量子钟的内部演化与固有时间之间可以建立具体动力学对应，但量子运动、钟—环境纠缠和测量反作用会限制理想钟描述的适用范围。([Nature][3])

因此，式（91.2）是本轮重建的一个明确准入条件，而不是任意量子过程自动满足的性质。

---

# 92．平方钟速何时唯一生成洛伦兹度量？

以下暂时固定事件 \(p\)，省略下标。

## 假设 92.1　二次钟响应

设 \(U\subset\mathbb R^d\) 为包含原点的开凸集，且

$$
r\in C^3(U),
\qquad r(v)>0.
$$

要求：

$$
\boxed{
\partial_i\partial_j\partial_k r=0
\qquad\forall i,j,k,
}
\tag{92.1}
$$

以及

$$
\boxed{
-\frac12\operatorname{Hess}_v r>0.
}
\tag{92.2}
$$

式（92.1）要求平方钟速的二阶响应不随控制方向继续变化；式（92.2）要求它在方向变量上严格凹。

这两项都具有实质内容。它们不能从量子态正性直接推出。

---

## 定理 92.1　局部洛伦兹重建

在假设 92.1 下，存在唯一的

$$
a>0,\qquad b\in\mathbb R^d,\qquad C=C^\mathsf T>0,
$$

使

$$
\boxed{
r(v)=a+2b^\mathsf Tv-v^\mathsf TCv.
}
\tag{92.3}
$$

定义

$$
\boxed{
g=
\begin{pmatrix}
-a&-b^\mathsf T\\
-b&C
\end{pmatrix}.
}
\tag{92.4}
$$

则 \(g\) 恰好具有一个负方向和 \(d\) 个正方向，并且

$$
\boxed{
-g((1,v),(1,v))=r(v).
}
\tag{92.5}
$$

### 证明

由全部三阶偏导为零，Hessian 在连通集 \(U\) 上为常矩阵。因此 Taylor 展开精确终止于二阶：

$$
r(v)
=
r(0)+\nabla r(0)^\mathsf Tv
+\frac12v^\mathsf T(\operatorname{Hess}r)v.
$$

取

$$
a=r(0),
\qquad
b=\frac12\nabla r(0),
\qquad
C=-\frac12\operatorname{Hess}r,
$$

即得式（92.3），且由假设知 \(a>0,C>0\)。

令

$$
w=C^{-1}b,
\qquad
N^2=a+b^\mathsf TC^{-1}b>0.
$$

对任意 \(T=(t,x)\)，完成平方：

$$
\boxed{
g(T,T)
=
(x-wt)^\mathsf TC(x-wt)-N^2t^2.
}
\tag{92.6}
$$

变换 \((t,x)\mapsto(t,x-wt)\) 可逆，所以 \(g\) 与

$$
\operatorname{diag}(-N^2,C)
$$

合同，恰有一个负方向。

式（92.5）由直接代入得到。唯一性来自二次多项式系数的唯一性。∎

---

## 推论 92.1　空间、漂移与钟速来自同一个响应函数

重建后的线元为

$$
\boxed{
ds^2
=
-N^2dt^2
+
(dx-w\,dt)^\mathsf TC(dx-w\,dt).
}
\tag{92.7}
$$

其中：

$$
\boxed{
C=-\frac12\operatorname{Hess}_v n(v)^2,
}
\tag{92.8}
$$

$$
\boxed{
b=\frac12\nabla_v n(v)^2\big|_{v=0},
}
\tag{92.9}
$$

$$
\boxed{
N^2=n(0)^2+b^\mathsf TC^{-1}b.
}
\tag{92.10}
$$

这给出本轮最核心的结构关系：

> **在这类模型中，空间度量不是额外加入的矩阵，而是平方钟速对运动方向的二阶响应。**

但这一结论是由“二次性、凹性与理想钟实现”共同推出的，不是单凭某个观察者拥有量子态就能得到。

作为数学对象，实二次型与对称双线性型的对应，以及其矩阵与惯性符号，已有适合形式化的基础；Mathlib 也提供相应的二次型、极化与矩阵表示定义。([Lean社区][4])

---

# 93．四维度量可以由十个局部钟速值重建

## 定义 93.1　有限读数设计

取 \(h>0\)，使以下方向都位于 \(U\)：

$$
0,\qquad
\pm he_i,\qquad
h(e_i+e_j)\quad(i<j).
$$

这里 \(e_i\) 为记录坐标的标准基。

因为 \(r(0)>0\)，只要 \(h\) 足够小，所有这些方向都可留在同一个正钟速邻域中。

定义读数：

$$
r_0=r(0),
$$

$$
r_i^\pm=r(\pm he_i),
$$

$$
r_{ij}=r(h(e_i+e_j)).
$$

---

## 定理 93.1　有限读数的精确反演公式

对式（92.3）的模型，

$$
\boxed{a=r_0,}
\tag{93.1}
$$

$$
\boxed{
b_i=\frac{r_i^+-r_i^-}{4h},
}
\tag{93.2}
$$

$$
\boxed{
C_{ii}
=
\frac{2r_0-r_i^+-r_i^-}{2h^2},
}
\tag{93.3}
$$

$$
\boxed{
C_{ij}
=
\frac{r_i^++r_j^+-r_{ij}-r_0}{2h^2}
\qquad(i<j).
}
\tag{93.4}
$$

### 证明

分别将 \(v=0,\pm he_i,h(e_i+e_j)\) 代入式（92.3）。

正负方向之差消去常数项和二次项，得到 \(b_i\)。

正负方向之和消去一次项，得到 \(C_{ii}\)。

最后，

$$
r(he_i)+r(he_j)-r(h(e_i+e_j))-r(0)
=
2h^2C_{ij}.
$$

∎

---

## 推论 93.1　四维中的十读数充分性

当 \(d=3\) 时，所需标量读数数目为

$$
1+2d+\frac{d(d-1)}2
=
10.
$$

因此：

$$
\boxed{
\text{十个精确平方钟速值}
\longrightarrow
\text{唯一的局部四维对称度量矩阵}.
}
\tag{93.5}
$$

这不是“十次量子测量就精确知道时空”。每个 \(r\) 值本身都需要一个制备、控制和统计估计协议。

本定理讨论的是**十个已经理想化为精确实数的读数**在二次模型类中的识别能力。

---

## 定理 93.2　该模型类中的标量读数最小数目

一个 \(1+d\) 维对称矩阵具有

$$
m=\frac{(d+1)(d+2)}2
$$

个独立实参数。

少于 \(m\) 个固定方向上的精确二次型读数，不能在这一完整模型类中保证唯一重建。

### 证明

固定方向的每个读数，都是矩阵系数的一个线性泛函。

少于 \(m\) 个线性泛函组成的映射，必有非零核。对任意内部准入点 \(a>0,C>0\)，沿该核作足够小的扰动，仍保持 \(a>0,C>0\)，却不改变全部已选读数。

因此不能唯一识别。∎

**四维的“十”来自对称二次型的自由度，不来自预先给观察者十个空间或时间维度。**

---

# 94．有限插值成功，不等于已经证明现实服从二次钟律

## 定义 94.1　钟律残差

由十个读数得到的重建函数记为

$$
r_{\mathrm{quad}}(v)
=
a+2b^\mathsf Tv-v^\mathsf TCv.
$$

对更多允许方向定义

$$
\boxed{
\Delta_{\mathrm{clock}}(v)
=
r_{\mathrm{actual}}(v)-r_{\mathrm{quad}}(v).
}
\tag{94.1}
$$

若它在某个已认证实验中显著非零，则否定的是当前二次钟律实现，而不是量子理论本身。

---

## 定理 94.1　任意有限读数集都不足以单独证明全域二次性

给定有限方向集合 \(S\subset U\)，存在两个正的光滑钟律：

$$
r_1,\qquad r_2,
$$

使：

$$
r_1(v)=r_2(v)\qquad(v\in S),
$$

但 \(r_1\) 是二次函数，\(r_2\) 不是。二者还可以同时保持严格凹性。

### 证明

取一个满足假设 92.1 的二次函数 \(r_1\)。

在不包含 \(S\) 中任何点的一个小开球内，选取非零光滑紧支撑函数 \(\psi\)。定义

$$
r_2=r_1+\lambda\psi.
$$

显然二者在 \(S\) 上相同。

取 \(\lambda\ne0\) 足够小，可同时保证函数值仍为正，且 Hessian 的负定性不被破坏。

选择非二次的 \(\psi\)，则 \(r_2\) 不满足全域三阶导数为零。∎

### 对项目的直接含义

把有限读数作为 CUT：

$$
q_S(r)=(r(v))_{v\in S},
$$

把“是否存在全域二次度量实现”作为目标 \(T(r)\)，上述两个函数给出：

$$
q_S(r_1)=q_S(r_2),
\qquad
T(r_1)\ne T(r_2).
$$

因此，存在明确的目标残差见证。

仓库已有的精确下降定理要求实际证明

$$
q_Y\circ F=\overline F\circ q_X,
$$

才排除这样的 carry；不能用有限拟合成功替代该全称命题。

### 进一步的限制

两个钟律甚至都可以分别定义合法有限维量子操作：

$$
U_v(t)=e^{-i\sqrt{r(v)}H_Ct/\hbar}.
$$

所以：

$$
\boxed{
\text{每个操作都量子合法}
\not\Rightarrow
\text{这些操作共同构成洛伦兹钟律}.
}
$$

二次性必须来自更底层动力学的证明，或作为被持续检验的物理模型条件。

---

# 95．钟重建与信号重建必须彼此验证

由式（92.6），重建的零间隔方向满足

$$
\boxed{
(v-w)^\mathsf TC(v-w)=N^2.
}
\tag{95.1}
$$

它是控制方向空间中的一个椭球边界。

但是，时钟只在允许的正钟速方向内进行实验。把二次多项式外推到 \(r=0\)，并不能独自证明那里就是实际信号的最大传播边界。

因此需要另一个独立对象：

$$
\Sigma_p
=
\text{由实际信号传播确定的局部特征方向集合}.
$$

共同几何要求

$$
\boxed{
\Sigma_p
=
\{T\ne0:g_p(T,T)=0\}
}
\tag{95.2}
$$

在所讨论的传播模式和尺度上成立。

这里比较的是特征传播结构，而不是要求所有有质量粒子的有限动量群速度都等于光速。

---

## 定理 95.1　相同光锥将洛伦兹二次型确定到正比例

设 \(g,\widetilde g\) 是同一实向量空间上的洛伦兹双线性型，具有相同的零方向集合，并采用相同的时间符号约定。

则存在 \(\lambda>0\)，使

$$
\boxed{
\widetilde g=\lambda g.
}
\tag{95.3}
$$

若另外存在一个共同标定的类时向量 \(T_0\)，满足

$$
\widetilde g(T_0,T_0)=g(T_0,T_0),
$$

则

$$
\widetilde g=g.
$$

### 证明

选择基底使

$$
g=-dt^2+\sum_i(dx^i)^2.
$$

将 \(\widetilde g\) 写成

$$
\widetilde g((t,x),(t,x))
=
At^2+2tB^\mathsf Tx+x^\mathsf TDx.
$$

所有 \((1,n)\)、\(\|n\|=1\) 都是零向量，所以

$$
A+2B^\mathsf Tn+n^\mathsf TDn=0.
$$

分别取 \(n,-n\)，得到 \(B=0\)。

继而

$$
n^\mathsf TDn=-A
$$

对全部单位向量成立，故 \(D=-AI\)。

因此

$$
\widetilde g=(-A)g.
$$

相同时间符号要求 \(-A>0\)。最后用 \(T_0\) 的非零长度确定比例为一。∎

### 结论

$$
\boxed{
\text{信号光锥负责因果形状，}
\quad
\text{量子钟负责尺度标定。}
}
$$

两者也可以相互否证：若钟律重建出的零方向与实际信号特征不一致，就不能继续把它们压缩成同一张度量。

---

# 96．有限精度下，度量与符号能否稳定认证？

## 假设 96.1　读数误差

先假设真实钟律确实为二次函数，且所有采样方向已精确标定。

对第 93 节的每个平方钟速读数，测量误差满足

$$
|\widehat r-r|\le\epsilon.
$$

用同样公式得到

$$
\widehat a,\qquad\widehat b,\qquad\widehat C.
$$

---

## 定理 96.1　系数重建误差

有：

$$
\boxed{
|\widehat a-a|\le\epsilon,
}
\tag{96.1}
$$

$$
\boxed{
\|\widehat b-b\|_2
\le
\frac{\sqrt d\,\epsilon}{2h},
}
\tag{96.2}
$$

$$
\boxed{
\|\widehat C-C\|_{\mathrm{op}}
\le
\frac{2d\,\epsilon}{h^2}.
}
\tag{96.3}
$$

### 证明

式（93.2）的分子包含两个读数误差，故每个 \(b_i\) 的误差不超过 \(\epsilon/(2h)\)。

式（93.3）、（93.4）的分子误差绝对值均不超过 \(4\epsilon\)，故每个 \(C_{ij}\) 的误差不超过 \(2\epsilon/h^2\)。

再使用向量范数及矩阵行和范数界即可。∎

---

## 推论 96.1　洛伦兹符号的稳健证书

若

$$
\boxed{
\widehat a>\epsilon,
}
\tag{96.4}
$$

且

$$
\boxed{
\lambda_{\min}(\widehat C)>
\frac{2d\,\epsilon}{h^2},
}
\tag{96.5}
$$

则真实参数满足

$$
a>0,\qquad C>0.
$$

因而在二次模型前提下，真实 \(g\) 确有一个负方向和 \(d\) 个正方向。

### 证明

第一项由式（96.1）。

对任意单位向量 \(x\)，

$$
x^\mathsf TCx
\ge
\lambda_{\min}(\widehat C)
-
\|\widehat C-C\|_{\mathrm{op}}
>0.
$$

∎

**该证书认证的是给定二次模型中的符号，不能反过来证明第 94 节排除不了的全域二次性。**

---

## 定理 96.2　接近零钟速边界时，平方读数与钟速误差的转换病态

若两个正钟速满足

$$
n,\widehat n\ge n_{\min}>0,
$$

则

$$
\boxed{
|\widehat n-n|
=
\frac{|\widehat r-r|}{\widehat n+n}
\le
\frac{|\widehat r-r|}{2n_{\min}}.
}
\tag{96.6}
$$

### 证明

使用平方差分解。∎

当 \(n_{\min}\to0\)，固定的平方钟速误差不能再保证固定的钟速误差。

但这只是当前参数识别的条件恶化，**不是仅凭实验变难就证明出现了黑洞视界。**

---

## 命题 96.1　缩小采样方向并非无条件提高精度

若真实 \(r\) 只满足三阶导数界

$$
\|D^3r\|\le B
$$

而不要求严格二次，则对原点局部 Hessian

$$
C_0=-\frac12\operatorname{Hess}r(0)
$$

有一个保守估计：

$$
\boxed{
\|\widehat C-C_0\|_{\mathrm{op}}
\le
d\left(
\frac{2\epsilon}{h^2}+Bh
\right).
}
\tag{96.7}
$$

### 证明

沿每个采样方向使用二阶 Taylor 展开，余项满足

$$
|R(v)|\le\frac B6\|v\|^3.
$$

代入式（93.3）、（93.4），每个 Hessian 系数的截断误差可界为 \(Bh\)，再加上读数误差项，最后使用矩阵行和界。∎

因此，一边有：

$$
h\downarrow\quad\Rightarrow\quad\text{截断误差减小},
$$

另一边有：

$$
h\downarrow\quad\Rightarrow\quad
\text{固定读数噪声被 }h^{-2}\text{ 放大}.
$$

这与项目对精确闭合、条件良好的闭合和物理可实现闭合的区分相对应。

---

# 97．不同观察者怎样重建同一张度量，而不是各自一张解释图？

## 定义 97.1　任意参数下的平方钟读数

对 \(T=(T^0,T^i)\)，在 \(T^0>0\) 且相应方向可实施的区域，定义

$$
\boxed{
Q_p(T)
=
(T^0)^2
r_p\!\left(\frac{T^i}{T^0}\right).
}
\tag{97.1}
$$

它表示用任意曲线参数 \(s\) 时的

$$
\left(\frac{d\tau}{ds}\right)^2.
$$

在二次钟律模型中，

$$
Q_p(T)=-g_p(T,T).
$$

---

## 定理 97.1　重叠观察者的度量协变性

设两组记录坐标之间的局部 Jacobian 为

$$
J=\frac{\partial x'}{\partial x}.
$$

若两位观察者对同一组物理钟过程使用相同单位，并在一个开集的可实施方向上同意：

$$
Q_p(T)=Q'_p(JT),
$$

则

$$
\boxed{
g'_p=J^{-\mathsf T}g_pJ^{-1}.
}
\tag{97.2}
$$

### 证明

有

$$
T^\mathsf T
\left(
g_p-J^\mathsf Tg'_pJ
\right)T=0
$$

在一个非空开集上成立。

左边是二次多项式。一个多项式在非空开集恒为零，则全部系数为零。因此

$$
g_p=J^\mathsf Tg'_pJ.
$$

∎

### 推论 97.1

若坐标变换在三重重叠处满足通常的复合条件，且各局部钟数据满足上述相容性，则这些局部矩阵可以拼接为同一个度量场。

所以，**“观察者是中心”不意味着不同观察者可以任意选择互不相容的度量。**

一旦它们声称描述同一实验，就必须通过式（97.2）的转换检验。

---

## 定理 97.2　从重建度量构造局部钟尺标架

取一个可逆矩阵 \(S\)，满足

$$
C=S^\mathsf TS.
$$

定义：

$$
e^0=Ndt,
$$

$$
\begin{pmatrix}
e^1\\ \vdots\\ e^d
\end{pmatrix}
=
S(dx-wdt).
$$

则

$$
\boxed{
g=-(e^0)^2+\sum_{a=1}^d(e^a)^2.
}
\tag{97.3}
$$

任意另一组给出相同 \(g\) 的局部标架，与该标架之间相差一个 Lorentz 变换。

### 证明

第一式由定理 92.1 的完成平方形式。

若 \(g=e^\mathsf T\eta e=\widetilde e^\mathsf T\eta\widetilde e\)，定义

$$
\Lambda=\widetilde e\,e^{-1}.
$$

则

$$
\Lambda^\mathsf T\eta\Lambda=\eta.
$$

∎

这补上前一轮的一项输入：**钟尺标架现在可以由钟律重建，而不必始终预先给定。**

但把实际量子输运认定为该度量的 Levi–Civita 输运，仍需检验度量相容与无挠条件。度量存在，不会自动排除其他连接。标准微分几何正是分别定义这些对象和相容关系。([David Tong][5])

---

# 98．单点度量甚至整条世界线的一阶数据，仍然不确定曲率

## 定义 98.1　一个局限于世界线的几何接口

设观察者世界线为 \(\gamma\)，定义：

$$
q_\gamma(g)
=
\left(
g|_\gamma,\,
\partial g|_\gamma
\right).
$$

这个接口包含线上各点的全部局部度量系数和一阶导数，但不包含离开世界线的二阶变化。

它不是“观察者能够做的一切实验”：向外发送信号、比较邻近钟或测量潮汐效应，可以扩大接口。

---

## 定理 98.1　相同世界线一阶读数可以对应不同曲率

在四维坐标 \((t,x,y,z)\) 中，令

$$
\eta=-dt^2+dx^2+dy^2+dz^2,
$$

$$
\boxed{
g_\alpha=e^{2\alpha x^2}\eta.
}
\tag{98.1}
$$

取世界线：

$$
\gamma(t)=(t,0,0,0).
$$

则对全部 \(\alpha\)：

$$
q_\gamma(g_\alpha)=q_\gamma(\eta).
$$

但是，在以下曲率符号约定下，

$$
\boxed{
R(g_\alpha)|_\gamma=-12\alpha.
}
\tag{98.2}
$$

### 证明

令

$$
\sigma=\alpha x^2.
$$

在线上，

$$
\sigma=0,\qquad \partial_\mu\sigma=0.
$$

因此：

$$
g_\alpha|_\gamma=\eta,
\qquad
\partial g_\alpha|_\gamma=0.
$$

共形度量的连接可直接计算为：

$$
\Gamma^\rho_{\mu\nu}
=
\delta^\rho_\mu\sigma_\nu
+
\delta^\rho_\nu\sigma_\mu
-
\eta_{\mu\nu}\eta^{\rho\lambda}\sigma_\lambda.
$$

所以线上连接系数也为零。

使用约定

$$
R_{\mu\nu}
=
\partial_\rho\Gamma^\rho_{\mu\nu}
-
\partial_\nu\Gamma^\rho_{\mu\rho}
+\text{二次连接项},
$$

在线上得到：

$$
R_{\mu\nu}
=
-2\sigma_{\mu\nu}
-\eta_{\mu\nu}\Box_\eta\sigma.
$$

又有：

$$
\Box_\eta\sigma=2\alpha.
$$

收缩得到：

$$
R=-6\Box_\eta\sigma=-12\alpha.
$$

∎

### 更强的一点

这些度量在整个区域内都与 \(\eta\) 共形，因此具有相同的局部零方向集合。

于是：

$$
\boxed{
\text{相同光锥}
+
\text{单条世界线上的完整一阶钟尺数据}
}
$$

仍然不保证相同曲率。

这说明必须继续区分：

$$
\boxed{
\text{单点度量识别},
\quad
\text{邻域中的度量场重建},
\quad
\text{曲率重建}.
}
$$

钟罗盘一类方案之所以需要经过准备的多钟网络及其位置、运动和频率比较，而不只是一只点状钟，正是因为目标包含了邻域几何信息。([arXiv][6])

---

# 99．一个更隐蔽的反例：平均钟速与共同光锥都正确，完整过程仍然不是经典几何

现在返回量子观察者本身。

上一节的问题是空间数据不够；本节的问题是：**即使平均读数完全符合某个度量，量子过程仍可能包含无法由该确定度量表示的关联。**

## 定义 99.1　两个受控钟速分支

固定参照钟的标定，不随以下控制分支改变。

设某个基础钟律为

$$
n_0(v)=\sqrt{r_0(v)},
$$

其中 \(r_0\) 满足第 92 节条件，对应度量 \(g_0\)。

引入一个控制寄存器 \(G\)，准备在

$$
|+\rangle_G.
$$

在两个分支分别实施：

$$
U_0(v,t)=e^{-in_0(v)H_Ct/\hbar},
$$

$$
U_1(v,t)=e^{-i2n_0(v)H_Ct/\hbar}.
$$

每个分支都单独具有合法的理想钟动力学，分别对应 \(g_0\) 与 \(4g_0\) 的钟速关系。两者的光锥相同。

这里讨论的是同一参照标定下的受控局部钟率，不是单纯把全部时间单位同时乘二。

---

## 定理 99.1　平均钟律可以严格为二次，而实际约化钟非酉

对钟的能级差

$$
\Delta E=\hbar\omega,
$$

忽略控制寄存器后，钟相干被乘以：

$$
\begin{aligned}
\chi_v(t)
&=
\frac12
\left[
e^{-i\omega n_0(v)t}
+
e^{-i2\omega n_0(v)t}
\right]\\
&=
\boxed{
e^{-i\frac32\omega n_0(v)t}
\cos\left(\frac12\omega n_0(v)t\right).
}
\end{aligned}
\tag{99.1}
$$

由初始相位变化率推得的平均钟速为：

$$
\overline n(v)=\frac32n_0(v).
$$

所以：

$$
\boxed{
\overline n(v)^2=\frac94r_0(v),
}
\tag{99.2}
$$

它严格对应一个洛伦兹度量：

$$
\boxed{
g_{\mathrm{mean}}=\frac94g_0.
}
\tag{99.3}
$$

但完整约化钟动力学不能由这个确定度量上的理想酉钟描述。

### 证明

式（99.1）由两个分支的部分迹直接得到。

初始相位导数给出 \(\overline n=\tfrac32n_0\)，从而得到式（99.2）、（99.3）。

若用确定平均钟速描述，则相干因子应该为：

$$
\chi_{\mathrm{ideal}}(t)
=
e^{-i\frac32\omega n_0t},
$$

模长恒为一。

真实因子却满足：

$$
|\chi_v(t)|
=
\left|
\cos\left(\frac12\omega n_0t\right)
\right|.
$$

对初始叠加态，在适当 \(t\) 上输出为混合态；确定 Hamiltonian 的酉作用不可能把纯态变成混合态。∎

---

## 推论 99.1　平均几何判据不足以认证确定经典时空

在本例中，下列测试可以同时通过：

$$
\text{平均平方钟速为二次函数},
$$

$$
\text{重建矩阵具有洛伦兹符号},
$$

$$
\text{全部分支共享同一光锥}.
$$

但完整量子钟过程仍然揭示额外关联。

因此：

$$
\boxed{
\text{平均读数具有几何实现}
\not\Rightarrow
\text{完整观察过程具有同一个确定几何实现}.
}
\tag{99.4}
$$

### 与第一节的闭合

这正是为什么假设 91.1 要求式（91.2）对全部允许初态和相应过程成立，而不是只从一次相位斜率定义一个 \(n(v)\)。

还应注意：此处单钟的约化退相干，也可以由具有相同比例的经典随机钟速模型复现。要进一步认证控制结构的量子性，需要联合相干实验。

**本例证明的是确定经典钟律失效，不是仅凭局部噪声就证明“时空一定处于量子叠加”。**

---

# 100．把重建过程写成可以逐层检查的形式化命题

## 定理 100.1　条件性量子钟—度量重建

设一个量子观察者模型满足：

1. 已建立一个 \(1+d\) 维局部可微记录坐标；
2. 指定钟与运动协议具有式（91.2）的确定性局部钟速实现；
3. 平方钟速满足二次性与严格凹性；
4. 不同观察者对共同实验的读数在重叠区域相容。

则：

* 每个事件存在唯一的局部洛伦兹度量，复现全部该类钟速；
* 在 \(d=3\) 的二次模型中，该局部度量可由十个适当方向上的精确读数重建；
* 不同观察者重建的矩阵按张量规律转换，并可拼接为同一个度量场。

若再加入：

5. 实际信号的特征方向与重建度量的零方向一致；
6. 具有足够邻域精度的二阶数据；
7. 实际参照输运满足度量相容与无挠条件；

则可以进一步把该模型的共同信号、钟尺与输运识别为相应的洛伦兹几何及其 Levi–Civita 连接。

### 证明

前三项分别由定理 92.1、93.1、97.1 得到。

信号一致性由第 95 节检验；邻域二阶数据用于确定曲率；连接识别使用第 97 节保留的度量相容与无挠条件。∎

---

## 100.1　每条箭头都应保留自己的证明义务

本轮的推理结构为：

$$
\boxed{
\text{实际量子协议}
\xrightarrow{\text{过程级钟律证明}}
n_p(v)
}
$$

$$
\boxed{
n_p(v)^2
\xrightarrow{\text{二次性与凹性}}
g_p
}
$$

$$
\boxed{
\{g_p\}
\xrightarrow{\text{重叠区域一致性}}
g
}
$$

$$
\boxed{
g+\text{邻域导数数据}
\xrightarrow{\text{连接相容性}}
\nabla,\ R.
}
$$

其中，以下推理均不允许省略：

| 已经得到      | 还不能直接推出          |
| --------- | ---------------- |
| 一些钟相位读数   | 对全部钟初态成立的理想钟过程   |
| 十个精确读数    | 全部方向上的平方钟速必为二次   |
| 一个洛伦兹矩阵   | 实际光信号遵守它的零锥      |
| 单点度量      | 曲率               |
| 平均钟律与共同光锥 | 确定经典几何足以描述全部量子关联 |
| 度量场       | 它满足 Einstein 方程  |

这不是降低理论的目标，而是使“导出”具有真正的证明含义。

---

## 100.2　本轮的可检查文件

我将第 93 节的十读数反演和单射性写成了一个独立 Lean 候选文件：

[ObserverClockTomography.lean](sandbox:/mnt/data/observer_formalization/ObserverClockTomography.lean)

它只处理：

$$
\boxed{
\text{二次钟律系数}
\longleftrightarrow
\text{十个精确读数}.
}
$$

不把量子可实现性、正定性、平滑几何或物理场方程放进已经证明的范围。

**该文件尚未运行 Lean 编译，不标记为内核已验证。**

另外，精确符号核验已经确认：

* 十读数反演公式；
* 四维读数设计矩阵的行列式为

  $$
  -512h^{15},
  $$

  因而 \(h\ne0\) 时可逆；
* 一个非平凡例子的洛伦兹合同分解；
* 第 98 节的曲率反例；
* 第 99 节的双分支钟相干恒等式。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_clock_metric_tomography.py)

符号核验不是一般 Lean 证明，也不认证所选模型符合现实。

---

# 结论

本轮把此前作为输入的“钟尺标定”，向前推进了一步：

$$
\boxed{
\text{平方钟速对运动方向的一阶响应}
\longrightarrow
\text{时间—空间混合项};
}
$$

$$
\boxed{
\text{平方钟速对运动方向的二阶响应}
\longrightarrow
\text{空间度量};
}
$$

$$
\boxed{
\text{钟速的正性与二阶凹性}
\longrightarrow
\text{洛伦兹符号}.
}
$$

核心公式是：

$$
\boxed{
g_{00}=-r(0),\qquad
g_{0i}=-\frac12\partial_i r(0),\qquad
g_{ij}=-\frac12\partial_i\partial_jr.
}
$$

这使“由量子观察者重建时空”获得了一个明确的操作性内容：

> **观察者不必先知道空间距离矩阵；它可以在合法且经过标定的局部协议中，比较自身量子钟如何随运动方向改变，再检验这些变化是否共同来自一个洛伦兹二次型。**

与此同时，我们也找到了一个更深的边界：

**即使所有平均钟速都可以拟合为一张漂亮的时空，量子关联仍然可能证明：这张图只描述平均读数，而不是完整物理过程。**

因此，真正自洽的重建对象应当是：

$$
\boxed{
\text{度量}
+
\text{与度量相容的量子过程}
+
\text{可控制的误差与遗漏关联}.
}
$$

只有当这三部分共同闭合时，时空才不只是一个从数据中拟合出的背景，而是一个受到量子观察者全部相关实验共同约束的物理结构。

[1]: https://link.aps.org/doi/10.1103/PhysRevD.98.024032 "https://link.aps.org/doi/10.1103/PhysRevD.98.024032"
[2]: https://link.aps.org/doi/10.1103/PhysRevA.97.042322 "https://link.aps.org/doi/10.1103/PhysRevA.97.042322"
[3]: https://www.nature.com/articles/s41467-020-18264-4 "https://www.nature.com/articles/s41467-020-18264-4"
[4]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/QuadraticForm/Basic.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/QuadraticForm/Basic.html"
[5]: https://davidtong.org/teaching/general-relativity/grhtml/S3.html "https://davidtong.org/teaching/general-relativity/grhtml/S3.html"
[6]: https://arxiv.org/abs/2006.09716 "https://arxiv.org/abs/2006.09716"
# 经典时空的过程级判据与量子钟速不相容性

## ——量子观察者—关系时空理论第一百零一至第一百一十节增订

### 摘要

上一轮证明：在平方钟速满足二次性与严格凹性的条件下，可以从钟读数重建洛伦兹度量。但同时构造了一个反例：**平均钟速可以完全符合某张度量，完整量子过程却不一定由这张确定度量描述。**

本增订进一步回答：

> **在什么条件下，量子结构真的可以被压缩成一张确定的经典时空？什么时候它只能表现为经典随机几何？又怎样识别超出这两者的量子关系？**

在一个明确的有限维量子钟模型中，本文证明：

$$
\boxed{
\text{确定性经典钟律}
\iff
\text{钟速算子在实际结构态的支持上取同一个标量值}.
}
$$

将此条件与上一轮的二次钟律结合，可以得到更强的有限判据：**在指定算子二次模型类中，十个方向上的精确过程条件，足以确定全部方向上的共同经典钟律。**

另一方面，本文给出一个有限反例：两个单独看起来相同的钟过程，其顺序比较却产生不同结果；利用相同的非交换作用，还可以通过一个最终返回原态的媒介，使两个观察者钟产生纠缠。

这些结论分别属于明确模型中的定理，不把“出现量子关联”直接等同于“已证明时空必须量子化”。量子钟的红移算子、时间关系与有效相互作用已有相关研究；本增订将其与项目的接口下降和过程级可实现性连接。([APS Journals][1])

---

# 101．从标量钟速升级到量子钟速算子

## 假设 101.1　有限结构与量子钟

设结构寄存器为有限维 Hilbert 空间：

$$
\mathcal H_G.
$$

其固定初态为：

$$
\sigma\ge0,
\qquad
\operatorname{Tr}\sigma=1.
$$

记支持投影为：

$$
P=\operatorname{supp}\sigma.
$$

观察者使用一个两能级钟：

$$
H_C=\hbar\omega|1\rangle\langle1|,
\qquad
\omega>0.
$$

对已标定的局部控制方向 \(v\)，给定正定算子：

$$
\widehat n(v)>0.
$$

选择联合 Hamiltonian：

$$
\boxed{
H(v)=H_C\otimes\widehat n(v).
}
\tag{101.1}
$$

因此完整演化为：

$$
\boxed{
U_v(t)
=
|0\rangle\langle0|\otimes I_G
+
|1\rangle\langle1|
\otimes e^{-i\omega t\widehat n(v)}.
}
\tag{101.2}
$$

本节暂不加入独立的结构自由演化。结构寄存器可以在不同钟交互之间保持关联，并不要求每一步重新准备。

时间参数 \(t\) 沿用前文已标定的参照协议；式（101.1）研究的是该协议下的相对钟速，不重新引入一个全知的外部观察者。

---

## 定义 101.1　约化钟过程

初始钟与结构取乘积：

$$
\rho_C\otimes\sigma.
$$

定义：

$$
\Phi_{v,t}(\rho_C)
=
\operatorname{Tr}_G
\left[
U_v(t)(\rho_C\otimes\sigma)U_v(t)^\dagger
\right].
$$

钟的非对角项由以下函数控制：

$$
\boxed{
\chi_v(t)
=
\operatorname{Tr}
\left[
\sigma e^{-i\omega t\widehat n(v)}
\right].
}
\tag{101.3}
$$

具体而言：

$$
\bigl(\Phi_{v,t}(\rho_C)\bigr)_{10}
=
\chi_v(t)(\rho_C)_{10}.
$$

这正是项目环境记录结构的一种实现：两个钟分支使结构寄存器产生不同条件演化，其重叠决定钟的约化相干。仓库 `EnvironmentRecords.lean` 已有相应的记录重叠、偏迹与相位阻尼恒等式。

---

# 102．单一经典钟律的精确判据

## 定义 102.1　两个不同的钟速矩

定义：

$$
m_1(v)=\operatorname{Tr}\bigl[\sigma\widehat n(v)\bigr],
$$

$$
m_2(v)=\operatorname{Tr}\bigl[\sigma\widehat n(v)^2\bigr].
$$

由式（101.3）：

$$
\boxed{
\chi_v'(0)=-i\omega m_1(v),
\qquad
\chi_v''(0)=-\omega^2m_2(v).
}
\tag{102.1}
$$

因此：

$$
\boxed{
m_2(v)-m_1(v)^2
=
\operatorname{Var}_\sigma(\widehat n(v)).
}
\tag{102.2}
$$

**平均平方钟速与平均钟速的平方，不是同一个量。**

只拟合其中一个，就可能丢掉另一种实验能够识别的结构。

---

## 定理 102.1　确定性钟律的充要条件

对固定方向 \(v\) 和实数 \(n_v>0\)，以下条件等价：

1. 对全部钟初态，在一个包含零的时间区间中，

   $$
   \Phi_{v,t}(\rho)
   =
   e^{-in_vH_Ct/\hbar}
   \rho
   e^{in_vH_Ct/\hbar};
   $$
2. $$
   \boxed{
   \bigl(\widehat n(v)-n_vI\bigr)\sigma^{1/2}=0;
   }
   \tag{102.3}
   $$
3. $$
   \boxed{
   \widehat n(v)P=n_vP;
   }
   \tag{102.4}
   $$
4. $$
   m_1(v)=n_v,
   \qquad
   m_2(v)=n_v^2.
   $$

### 证明

若条件 1 成立，则：

$$
\chi_v(t)=e^{-i\omega n_vt}.
$$

比较零点的一阶、二阶导数，得到条件 4。

条件 4 给出：

$$
\begin{aligned}
0
&=
m_2(v)-2n_vm_1(v)+n_v^2\\
&=
\operatorname{Tr}
\left[
\sigma(\widehat n(v)-n_vI)^2
\right]\\
&=
\left\|
(\widehat n(v)-n_vI)\sigma^{1/2}
\right\|_2^2.
\end{aligned}
$$

因此得到条件 2。

有限维中，\(\sigma^{1/2}\) 的像恰为 \(P\mathcal H_G\)，故条件 2、3 等价。

最后，条件 3 表明在实际初态的支持上：

$$
e^{-i\omega t\widehat n(v)}P
=
e^{-i\omega n_vt}P.
$$

代入式（101.3），得到条件 1。∎

---

## 推论 102.1　满秩结构态下的刚性

若：

$$
\sigma>0,
$$

则一个方向上存在精确确定性钟律，当且仅当：

$$
\boxed{
\widehat n(v)=n_vI.
}
\tag{102.5}
$$

### 证明

满秩意味着 \(P=I\)，直接应用定理 102.1。∎

### 含义

对于一个真正依赖结构状态的非平凡钟速算子，满秩结构态一般不会给出精确的单一钟速。

经典描述可能来自某个受限支持子空间、某个条件记录，或者受控近似。

**“取结构平均值”不是自动获得确定经典时空的数学操作。**

---

# 103．把上一轮的度量重建提升到算子二次模型

## 假设 103.1　算子值平方钟律

在局部方向域：

$$
U\subset\mathbb R^d
$$

上定义：

$$
\boxed{
\widehat R(v)
=
\widehat A
+
2\sum_i v_i\widehat B_i
-
\sum_{i,j}v_iv_j\widehat C_{ij}.
}
\tag{103.1}
$$

要求各系数 Hermitian，且：

$$
\widehat C_{ij}=\widehat C_{ji}.
$$

此外，存在 \(a_*,c_*>0\)，使：

$$
\widehat A\ge a_*I,
$$

以及对全部实向量 \(\xi\)：

$$
\boxed{
\sum_{i,j}\xi_i\xi_j\widehat C_{ij}
\ge
c_*\|\xi\|^2I.
}
\tag{103.2}
$$

并在 \(U\) 内要求：

$$
\widehat R(v)>0.
$$

定义实际钟速算子：

$$
\boxed{
\widehat n(v)=\widehat R(v)^{1/2}.
}
\tag{103.3}
$$

这些矩阵目前是**钟响应的算子系数**，不预先宣称它们已经构成一个完整量子时空度量。

---

## 定理 103.1　平均二阶读数总能给出一个洛伦兹候选

定义：

$$
\overline r_2(v)
=
\operatorname{Tr}[\sigma\widehat R(v)].
$$

则：

$$
\overline r_2(v)
=
a+2b^{\mathsf T}v-v^{\mathsf T}Cv,
$$

其中：

$$
a=\operatorname{Tr}(\sigma\widehat A)>0,
$$

$$
b_i=\operatorname{Tr}(\sigma\widehat B_i),
$$

$$
C_{ij}=\operatorname{Tr}(\sigma\widehat C_{ij}),
\qquad
C>0.
$$

因而：

$$
\boxed{
g_{\mathrm{second}}
=
\begin{pmatrix}
-a&-b^{\mathsf T}\\
-b&C
\end{pmatrix}
}
\tag{103.4}
$$

具有一个负方向和 \(d\) 个正方向。

### 证明

取迹保持线性，故得到二次函数。

由假设：

$$
a\ge a_*>0,
$$

且：

$$
\xi^{\mathsf T}C\xi
=
\operatorname{Tr}
\left[
\sigma\sum_{i,j}\xi_i\xi_j\widehat C_{ij}
\right]
\ge c_*\|\xi\|^2.
$$

最后完成平方，或者应用上一轮洛伦兹重建定理。∎

### 关键限制

即使式（103.4）对每个结构态都成立，仍可能：

$$
\boxed{
\operatorname{Var}_\sigma(\widehat n(v))>0.
}
$$

此时：

$$
\bigl(\operatorname{Tr}\sigma\widehat n(v)\bigr)^2
\ne
\operatorname{Tr}\sigma\widehat R(v).
$$

所以，两种不同的“平均几何”甚至可能从不同统计读数中出现。

**真正需要的不是选一个看起来更漂亮的平均，而是检验完整钟过程是否沿同一个经典几何下降。**

---

# 104．十个过程条件能够确定全部方向上的共同经典钟律

本节固定 \(d=3\)。

取上一轮的十个采样方向：

$$
0,\qquad
\pm he_i,\qquad
h(e_i+e_j)\quad(i<j),
$$

其中 \(h\ne0\)，全部采样方向位于 \(U\)。

所有实验使用**同一个结构初态 \(\sigma\)**。不能在不同方向暗中准备不同的结构态，然后把结果当成同一模型的共同经典化。

---

## 定理 104.1　算子二次模型的有限经典性判据

假设在十个采样方向 \(v_s\) 上，分别存在 \(n_s>0\)，满足：

$$
\boxed{
\bigl(\widehat n(v_s)-n_sI\bigr)\sigma^{1/2}=0.
}
\tag{104.1}
$$

则存在唯一标量二次函数：

$$
r(v)=a+2b^{\mathsf T}v-v^{\mathsf T}Cv,
$$

使在整个 \(U\) 上：

$$
\boxed{
\widehat R(v)P=r(v)P,
}
\tag{104.2}
$$

以及：

$$
\boxed{
\widehat n(v)P=\sqrt{r(v)}\,P.
}
\tag{104.3}
$$

此外，\(a>0,C>0\)，因而得到唯一的共同洛伦兹候选：

$$
g=
\begin{pmatrix}
-a&-b^{\mathsf T}\\
-b&C
\end{pmatrix}.
$$

### 证明

由定理 102.1，在每个采样方向：

$$
\widehat n(v_s)P=n_sP.
$$

平方得到：

$$
\widehat R(v_s)P=n_s^2P.
$$

算子值二次多项式的重建只使用实线性组合，不要求不同系数彼此可交换。例如：

$$
\widehat A=\widehat R(0),
$$

$$
\widehat B_i
=
\frac{\widehat R(he_i)-\widehat R(-he_i)}{4h},
$$

$$
\widehat C_{ii}
=
\frac{
2\widehat R(0)-\widehat R(he_i)-\widehat R(-he_i)
}{2h^2},
$$

$$
\widehat C_{ij}
=
\frac{
\widehat R(he_i)+\widehat R(he_j)
-\widehat R(h(e_i+e_j))
-\widehat R(0)
}{2h^2}.
$$

右乘 \(P\)，每项都成为标量乘 \(P\)。因此存在：

$$
\widehat AP=aP,
\qquad
\widehat B_iP=b_iP,
\qquad
\widehat C_{ij}P=C_{ij}P.
$$

代回式（103.1），得到式（104.2）。

由于 \(\widehat R(v)\) Hermitian，\(P\mathcal H_G\) 是其不变子空间；在该子空间上，正平方根也作用为标量 \(\sqrt{r(v)}\)，得到式（104.3）。

取 \(P\mathcal H_G\) 中任意单位向量，应用假设（103.2），得到 \(a>0,C>0\)。唯一性由十点二次插值得到。∎

---

## 推论 104.1　精确经典子空间在钟交互下自动保持

在上述支持子空间上：

$$
U_v(t)
\bigl(|\psi\rangle_C\otimes|\xi\rangle_G\bigr)
=
e^{-iH_C\sqrt{r(v)}t/\hbar}|\psi\rangle_C
\otimes|\xi\rangle_G.
$$

因此，任意有限次该类钟交互都不会把结构带出这个经典子空间，也不会产生额外的钟—结构纠缠。

### 注 104.1

这个结论仍然以算子二次模型类已被证明为前提。

**“十个方向”不是“十次实验”。**每个方向上的式（104.1）都是精确过程条件；有限统计数据只能支持带误差的版本。

上一轮的候选 Lean 文件只覆盖标量十点插值。本节需要另外形式化支持投影、算子平方根与零方差判据，不能把原文件的标量证明视为已经覆盖这些内容。

---

# 105．共享结构下的全过程误差：不需要假装每一步都重置环境

## 定义 105.1　局部经典化残差

对一个候选标量钟速 \(n_j\)，定义：

$$
\boxed{
\delta_j
=
\left\|
(\widehat n_j-n_jI)\sigma^{1/2}
\right\|_2.
}
\tag{105.1}
$$

考虑同一个结构寄存器上连续发生的联合操作：

$$
U_j
=
e^{-it_jH_j\otimes\widehat n_j/\hbar},
$$

其经典候选为：

$$
U_j^{(0)}
=
e^{-it_jn_jH_j/\hbar}\otimes I_G.
$$

允许在这些步骤之间插入相同的、仅作用于钟及其记录附件的酉控制。

---

## 定理 105.1　共同结构全过程的误差界

设结构初态为固定的 \(\sigma\)，且初始时与钟输入及其外部测试参照独立。

令 \(\mathcal P\) 为完整实际过程的外侧通道，\(\mathcal P_0\) 为对应经典候选，则：

$$
\boxed{
\frac12\|\mathcal P-\mathcal P_0\|_\diamond
\le
\sum_j
\frac{|t_j|\|H_j\|_{\mathrm{op}}}{\hbar}\delta_j.
}
\tag{105.2}
$$

### 证明

纯化结构初态为 \(|\Sigma\rangle\)，使：

$$
\left\|
(\widehat n_j-n_jI)|\Sigma\rangle
\right\|
=
\delta_j.
$$

由 Duhamel 公式，对任意钟及其参照的单位输入向量：

$$
\left\|
(U_j-U_j^{(0)})
(|\psi\rangle\otimes|\Sigma\rangle)
\right\|
\le
\frac{|t_j|\|H_j\|}{\hbar}\delta_j.
$$

对完整乘积采用展开：

$$
\begin{aligned}
U_m\cdots U_1-U_m^{(0)}\cdots U_1^{(0)}
=
\sum_j
U_m\cdots U_{j+1}
(U_j-U_j^{(0)})
U_{j-1}^{(0)}\cdots U_1^{(0)}.
\end{aligned}
$$

每个误差项右侧只有理想前缀，因此结构仍处于原始纯化态；左侧实际后缀是酉算子，不增加向量范数。

应用三角不等式，再取偏迹并对全部附加参照输入取上确界，得到式（105.2）。∎

### 重要区别

本定理没有把单步约化通道相乘。

它比较的是**完整共享结构上的两个联合实现**，所以允许实际过程中产生环境记忆。

这与前文的共享参照反例相容。具有记忆的过程需要使用多时刻的完整实验结构，而不能仅由孤立单步通道决定。([arXiv][2])

---

## 推论 105.1　由有限采样误差控制其他方向

令十点插值系数为 \(\ell_s(v)\)，使：

$$
\widehat R(v)=\sum_s\ell_s(v)\widehat R(v_s).
$$

定义候选：

$$
\widetilde r(v)=\sum_s\ell_s(v)n_s^2.
$$

则：

$$
\boxed{
\left\|
[\widehat R(v)-\widetilde r(v)I]\sigma^{1/2}
\right\|_2
\le
\sum_s|\ell_s(v)|
\bigl(\|\widehat n(v_s)\|+n_s\bigr)\delta_s.
}
\tag{105.3}
$$

若进一步有：

$$
\widehat n(v)\ge\nu_*I,
\qquad
\sqrt{\widetilde r(v)}\ge\nu_*>0,
$$

则：

$$
\boxed{
\left\|
[\widehat n(v)-\sqrt{\widetilde r(v)}I]\sigma^{1/2}
\right\|_2
\le
\frac1{2\nu_*}
\left\|
[\widehat R(v)-\widetilde r(v)I]\sigma^{1/2}
\right\|_2.
}
\tag{105.4}
$$

### 证明

首先使用：

$$
\widehat R(v_s)-n_s^2I
=
[\widehat n(v_s)+n_sI]
[\widehat n(v_s)-n_sI],
$$

再用三角不等式，得到式（105.3）。

对式（105.4），使用：

$$
\widehat n-\widetilde nI
=
(\widehat n+\widetilde nI)^{-1}
(\widehat R-\widetilde n^2I),
$$

以及逆算子范数不超过 \(1/(2\nu_*)\)。∎

因此：

$$
\boxed{
\text{有限方向上的过程证书}
\longrightarrow
\text{其他方向的钟律误差}
\longrightarrow
\text{完整有限实验的误差}.
}
$$

这比仅对平均度量系数给出误差界更强。

---

# 106．什么时候量子结构等价于经典随机几何？

确定几何并不是唯一可能的经典描述。另一种情况是：每次实验使用一张经典几何，但不同实验之间随机变化。

## 假设 106.1　可交换的结构系数

假设：

$$
\widehat A,\quad
\widehat B_i,\quad
\widehat C_{ij}
$$

全部两两可交换。

则存在共同谱投影 \(P_\lambda\)，使：

$$
\widehat R(v)
=
\sum_\lambda r_\lambda(v)P_\lambda,
$$

其中：

$$
r_\lambda(v)
=
a_\lambda+2b_\lambda^{\mathsf T}v-v^{\mathsf T}C_\lambda v.
$$

由前述正性条件，每个 \(\lambda\) 都对应一个洛伦兹候选：

$$
g_\lambda
=
\begin{pmatrix}
-a_\lambda&-b_\lambda^{\mathsf T}\\
-b_\lambda&C_\lambda
\end{pmatrix}.
$$

---

## 定理 106.1　可交换结构的全协议经典混合表示

对由上述钟耦合以及钟侧操作构成的任意有限实验，有：

$$
\boxed{
\mathcal P
=
\sum_\lambda p_\lambda\mathcal P_{g_\lambda},
\qquad
p_\lambda=\operatorname{Tr}(\sigma P_\lambda).
}
\tag{106.1}
$$

这里 \(\lambda\) 在一次完整实验中保持相同，不是每一步重新抽样。

### 证明

正平方根保持共同谱分解：

$$
\widehat n(v)
=
\sum_\lambda\sqrt{r_\lambda(v)}P_\lambda.
$$

因此，每一步联合操作在 \(\lambda\) 块上都是对应标量钟律的操作。

任意钟侧操作都不混合结构标签 \(\lambda\)。整个有限过程因此按同一组块分解。

最后对结构取偏迹，所有 \(\lambda\ne\lambda'\) 的交叉块消失，只留下权重 \(p_\lambda\) 的过程混合。∎

### 结论

$$
\boxed{
\text{结构态是量子的}
\not\Rightarrow
\text{指定实验一定能排除经典随机几何}.
}
$$

若全部允许耦合只读取一个可交换结构代数，完整实验可以具有经典隐藏标签表示。

反过来，非交换的形式本身也不是对任意实验的充分量子见证。必须构造能实际读取其差别的协议。仅凭噪声或某个响应不为零，并不足以判定噪声来源不可经典化；这一区分在量子耗散研究中也十分重要。([arXiv][3])

---

# 107．一个正钟速模型：平均度量正确，交换顺序却暴露更多结构

下面给出一个完全有限的实例。

取：

$$
\mathcal H_G=\mathbb C^2,
$$

并记 Pauli 矩阵为 \(X,Z\)。

在无量纲化的局部控制区间：

$$
|v|<\sqrt{\frac32}
$$

内，定义：

$$
\boxed{
\widehat R(v)
=
\left(\frac32-\frac{v^2}{4}\right)I
+
\frac{1-v}{2}X
+
\frac{1+v}{2}Z.
}
\tag{107.1}
$$

它属于第 103 节的算子二次模型，且：

$$
\widehat C=\frac14I.
$$

---

## 定理 107.1　正性与两个特殊方向

式（107.1）在上述区间严格正定。

并且：

$$
\boxed{
\widehat n(+1)=I+\frac12Z,
\qquad
\widehat n(-1)=I+\frac12X.
}
\tag{107.2}
$$

### 证明

式（107.1）的最小本征值为：

$$
\frac32-\frac{v^2}{4}
-
\sqrt{\frac{1+v^2}{2}}.
$$

在 \(v^2<3/2\) 内，第一项大于 \(9/8\)，根号项小于 \(\sqrt5/2\)。又有：

$$
\left(\frac98\right)^2-\left(\frac{\sqrt5}{2}\right)^2
=
\frac1{64}>0.
$$

因此严格正定。

在 \(v=\pm1\) 上直接计算：

$$
\widehat R(+1)=\left(I+\frac12Z\right)^2,
$$

$$
\widehat R(-1)=\left(I+\frac12X\right)^2.
$$

两个候选平方根的本征值都是 \(1/2,3/2>0\)，因此它们就是正平方根。∎

---

## 定理 107.2　相同单次钟过程不决定顺序比较

取：

$$
\sigma=\frac I2.
$$

在两个特殊方向上：

$$
\boxed{
\chi_\pm(t)
=
e^{-i\omega t}\cos\frac{\omega t}{2}.
}
\tag{107.3}
$$

因此，两个方向的孤立钟通道完全相同。

但是，当：

$$
\omega t=\pi,
$$

结构操作为：

$$
V_+=e^{-i\pi\widehat n(+1)}=iZ,
$$

$$
V_-=e^{-i\pi\widehat n(-1)}=iX.
$$

所以：

$$
\boxed{
V_-V_+=-V_+V_-.
}
\tag{107.4}
$$

在相干比较“先 \(+\) 后 \(-\)”与“先 \(-\) 后 \(+\)”的实验中，两条分支具有相对相位 \(\pi\)。

### 证明

式（107.3）由 \(\widehat n(\pm1)\) 相同的两个本征值及最大混合态得到。

式（107.4）由 \(XZ=-ZX\) 得到。∎

更一般地，令两次脉冲的非平凡旋转角为：

$$
a=\frac{\omega t_+}{2},
\qquad
b=\frac{\omega t_-}{2},
$$

则最大混合结构态下的顺序干涉系数为：

$$
\boxed{
\gamma_{\mathrm{order}}
=
1-2\sin^2a\,\sin^2b.
}
\tag{107.5}
$$

这一公式可直接用两个 Pauli 指数展开验证。

### 与经典随机模型的区别

若每次实验只是固定的经典标签 \(\lambda\)，两种操作分别乘上标量相位：

$$
e^{-i\omega t_+n_+(\lambda)},
\qquad
e^{-i\omega t_-n_-(\lambda)},
$$

则其乘积与顺序无关。无论怎样对 \(\lambda\) 平均，都不会得到式（107.4）的相对负号。

但这里排除的是**固定、可交换的标量钟速模型**。时间变化的经典背景、其他仪器作用和路径依赖必须另行排除。

而且，相干比较必须使用具体实现过的操作，不能从两张孤立通道表格自动推断受控实验。相干控制能够读取通常通道描述中被省略的实现信息，这是已有的量子信息现象。([arXiv][4])

---

# 108．更强的见证：媒介返回原态，两只观察者钟产生纠缠

上一节排除了静态可交换钟速模型。下面给出一个在更明确的局域性条件下，排除经典信息媒介的见证。

## 定义 108.1　两只钟与同一个结构比特

令 \(A,B\) 为两只观察者钟，\(G\) 为结构寄存器。

定义局部耦合操作：

$$
\mathsf U_A
=
|0\rangle\langle0|_A\otimes I_G
+
|1\rangle\langle1|_A\otimes iX_G,
$$

$$
\mathsf U_B
=
|0\rangle\langle0|_B\otimes I_G
+
|1\rangle\langle1|_B\otimes iZ_G.
$$

省略另一个钟上的恒等扩张。

这些操作可以由第 107 节的正钟速 Hamiltonian 在适当持续时间内得到。

---

## 定理 108.1　闭合媒介序列实现两钟受控相位

定义：

$$
\boxed{
\mathsf W
=
\mathsf U_B^\dagger
\mathsf U_A^\dagger
\mathsf U_B
\mathsf U_A.
}
\tag{108.1}
$$

则：

$$
\boxed{
\mathsf W=\operatorname{CZ}_{AB}\otimes I_G.
}
\tag{108.2}
$$

### 证明

按两个钟的计算基状态 \(a,b\in\{0,1\}\) 分块。

若至少一个控制位为零，作用相互抵消。

若 \(a=b=1\)，结构上的作用为：

$$
(iZ)^\dagger(iX)^\dagger(iZ)(iX)=-I.
$$

因此只有 \(|11\rangle_{AB}\) 分支得到负号，而结构算子最终为恒等。∎

---

## 推论 108.1　结构复归与最大纠缠相容

初始两钟为：

$$
|+\rangle_A|+\rangle_B,
$$

结构初态可为任意 \(\sigma\)，且初始时与两钟独立。

最终态为：

$$
\boxed{
|G\rangle_{AB}\langle G|\otimes\sigma,
}
\tag{108.3}
$$

其中：

$$
\boxed{
|G\rangle
=
\frac{|00\rangle+|01\rangle+|10\rangle-|11\rangle}{2}.
}
\tag{108.4}
$$

\(|G\rangle\) 与 Bell 态局部酉等价，因此两钟最大纠缠。

### 证明

将式（108.2）作用于初态即可。∎

---

## 定理 108.2　局部经典信息媒介不能实现该输出

假设：

* 两钟初始可分；
* 媒介始终只有经典标签；
* 每一步仅允许某一只钟与媒介进行局部量子操作、经典记录更新和经典反馈；
* 不存在未记录的直接 \(A\)—\(B\) 量子作用或预共享量子资源。

则最终两钟态必可分，不能得到式（108.4）。

### 证明

一般初态可写为：

$$
\sum_\lambda p_\lambda
\rho_A^\lambda\otimes\rho_B^\lambda
\otimes|\lambda\rangle\langle\lambda|.
$$

一次局部钟—经典标签操作，只会更新某一侧的条件态与经典概率，并可能增加新标签。它仍保持关于 \(A|B\) 的凸乘积形式。

对步骤数归纳，最终对经典媒介求和后仍可分。∎

在明确的局域介导前提下，以两探针纠缠检验媒介非经典性，是既有研究路线。这里直接给出了有限维的可计算实例；不能省略局域性、初始资源和竞争相互作用等条件。([arXiv][5])

### 稳健见证

定义：

$$
\mathcal W_{\mathrm{ent}}
=
\frac12I-|G\rangle\langle G|.
$$

对任意可分态：

$$
\operatorname{Tr}(\rho_{\mathrm{sep}}\mathcal W_{\mathrm{ent}})\ge0.
$$

若实际输出满足：

$$
D(\rho_{\mathrm{out}},|G\rangle\langle G|)\le\eta<\frac12,
$$

则：

$$
\boxed{
\operatorname{Tr}(\rho_{\mathrm{out}}\mathcal W_{\mathrm{ent}})
\le-\frac12+\eta<0.
}
\tag{108.5}
$$

证明使用 \(|G\rangle\) 的最大乘积态重叠平方为 \(1/2\)，以及迹距离对效果概率差的界。

### 物理边界

这一电路证明媒介作用的非经典性，不证明该媒介就是引力或时空。

它也没有仅凭门序列证明某个指定总 Hamiltonian 的严格能量守恒。若要实现完整能量闭合，还必须把脉冲控制器、储能系统与参照时钟纳入。

---

# 109．经典化还存在一种无法通过换状态消除的不相容性

第 102 节允许通过选择结构支持子空间获得经典钟律。现在问：

> 是否总能找到一个足够合适的结构态，使所有方向都变成确定钟速？

答案是否定的。

## 定理 109.1　两种钟速的状态无关方差下界

对第 107 节：

$$
\widehat n_+=I+\frac12Z,
\qquad
\widehat n_-=I+\frac12X,
$$

任意结构态 \(\sigma\) 都满足：

$$
\boxed{
\operatorname{Var}_\sigma(\widehat n_+)
+
\operatorname{Var}_\sigma(\widehat n_-)
\ge\frac14.
}
\tag{109.1}
$$

### 证明

令：

$$
x=\operatorname{Tr}(\sigma X),
\qquad
z=\operatorname{Tr}(\sigma Z).
$$

量子比特状态满足：

$$
x^2+z^2\le1.
$$

又因 \(X^2=Z^2=I\)：

$$
\operatorname{Var}_\sigma(\widehat n_+)
=
\frac14(1-z^2),
$$

$$
\operatorname{Var}_\sigma(\widehat n_-)
=
\frac14(1-x^2).
$$

相加即得。∎

因此：

$$
\boxed{
\text{这个模型不存在同时使两种钟过程精确经典化的非零支持。}
}
\tag{109.2}
$$

可以把某一个方向准备成无方差状态，但另一个方向必然留下额外结构。

---

## 定理 109.2　一般共同经典化的交换子必要条件

令：

$$
\delta_a
=
\|(\widehat n_a-n_aI)\sigma^{1/2}\|_2,
$$

$$
\delta_b
=
\|(\widehat n_b-n_bI)\sigma^{1/2}\|_2.
$$

则：

$$
\boxed{
\|[\widehat n_a,\widehat n_b]\sigma^{1/2}\|_2
\le
\|\widehat n_a-n_aI\|_{\mathrm{op}}\delta_b
+
\|\widehat n_b-n_bI\|_{\mathrm{op}}\delta_a.
}
\tag{109.3}
$$

### 证明

记：

$$
D_a=\widehat n_a-n_aI,
\qquad
D_b=\widehat n_b-n_bI.
$$

则：

$$
[\widehat n_a,\widehat n_b]\sigma^{1/2}
=
D_aD_b\sigma^{1/2}
-
D_bD_a\sigma^{1/2}.
$$

应用三角不等式与乘积范数界。∎

### 推论 109.1

若存在精确共同经典钟律，即 \(\delta_a=\delta_b=0\)，则：

$$
[\widehat n_a,\widehat n_b]P=0.
$$

但仅有这个交换子在支持上为零，还不足以保证每个钟速都无方差；共同可交换但具有多个不同本征值的随机结构就是反例。

因此有三层严格不同的要求：

$$
\boxed{
\text{能共同对角化};
}
$$

$$
\boxed{
\text{实际态是否只支持同一个几何分支};
}
$$

$$
\boxed{
\text{该分支是否与信号、路径和钟尺共同相容}.
}
$$

这也说明，“退相干后就是经典时空”仍然不够。退相干可能只得到多个经典分支的混合；非交换的允许实验还可能超出这个混合表示。

---

# 110．从平均几何到过程级几何：形式化依赖链

本轮把上一轮的度量重建进一步细分为：

$$
\boxed{
\text{量子操作族}
\longrightarrow
\text{钟速算子}
\longrightarrow
\text{可见统计矩}.
}
$$

但从统计矩走向确定经典度量，需要额外的：

$$
\boxed{
\text{共同支持上的标量化证明}.
}
$$

在算子二次模型中，这一证明可以通过有限组方向上的条件归约；随后，完整共享结构的实验误差还可以用定理 105.1 控制。

## 110.1　可以逐项进入形式化系统的命题

| 层次      | 数学对象                                        | 必须证明的结论                |
| ------- | ------------------------------------------- | ---------------------- |
| 单钟过程    | \(\sigma,\widehat n,H_C\)                   | 理想酉钟律等价于支持上的标量作用       |
| 算子钟律    | \(\widehat A,\widehat B_i,\widehat C_{ij}\) | 正性、二次性和有限方向插值          |
| 共同经典子空间 | \(P\)                                       | 全部方向在 \(P\) 上具有同一标量二次型 |
| 近似过程    | \(\delta_j,t_j,H_j\)                        | 共享结构下完整协议的误差界          |
| 随机经典实现  | 共同谱投影 \(P_\lambda\)                         | 全实验族的固定标签混合表示          |
| 非经典见证   | 顺序比较、媒介闭路                                   | 超出指定经典实现类的实验差别         |
| 几何识别    | 钟律、信号、坐标重叠                                  | 对同一个时空模型的共同因子化         |

项目的 `exact_descent_has_no_carry` 仍然适用：一旦声称某个经典描述能覆盖全部相关量子实验，就必须实际给出相应的下降证明。本轮提供的是填充这一证明所需的更具体条件，而不是用“平均值正确”代替它。

---

## 110.2　本轮核验与源码

本轮已作精确符号核验的内容包括：

算子二次函数的十方向插值；有限反例中的正平方根；顺序干涉公式；完整八维媒介闭路；两钟输出态的纠缠。

[精确算例核验脚本](sandbox:/mnt/data/observer_formalization/check_process_metric_classicality.py)

[核验结果](sandbox:/mnt/data/observer_formalization/process_metric_checks.json)

另给出一个只使用有限布尔基底与符号位的 Lean 候选文件，保存受控 \(X,Z\) 闭路产生受控相位、同时保持媒介标签的证明结构：

[ObserverControlledCommutator.lean](sandbox:/mnt/data/observer_formalization/ObserverControlledCommutator.lean)

**该 Lean 文件尚未编译。**它只覆盖有限带符号基底上的组合恒等式，没有把复线性扩张、密度矩阵、纠缠见证和全过程误差界冒充为已经机器证明的内容。

---

# 结论

本轮真正推进的，不是再增加一种“时空本质”，而是给出了**经典时空何时足以替代完整量子结构**的更严格判据。

前文的平均读数重建是：

$$
\text{平方钟速的二次统计}
\longrightarrow
\text{一个洛伦兹矩阵}.
$$

本轮的过程级重建则要求：

$$
\boxed{
\widehat n(v)P=\sqrt{-g((1,v),(1,v))}\,P
}
$$

在所讨论的全部方向和同一个实际结构支持上成立。

它意味着：

> **不是仅有平均读数符合这张时空，而是结构中仍被实际占据的区别，不再改变相关钟过程。**

若所有结构系数可交换，却存在多个分支，则得到的是经典随机几何。

若不同允许钟速作用不相容，单钟统计仍可能看起来普通，但顺序比较和多观察者关联可以揭示额外结构。我们已经给出了这样的有限、正能量耦合实例。

因此，“由量子观察者导出物理时空”现在可以表达得更准确：

$$
\boxed{
\text{先定义完整量子交互，}
}
$$

$$
\boxed{
\text{再证明哪些内部区别可以被共同忽略，}
}
$$

$$
\boxed{
\text{最后把保留下来的钟与信号关系识别为经典时空。}
}
$$

**经典时空不是对所有量子数据取平均后的必然产物，而是完整观察过程在特定支持、控制能力、精度与实验范围内，确实能够通过同一个几何模型表达时得到的有效结构。**

这使理论具有一个明确的正反检验：既能证明某个经典时空描述成立，也能通过具体的量子过程见证，指出它究竟在哪一层失效。

[1]: https://link.aps.org/doi/10.1103/PhysRevD.110.106014 "https://link.aps.org/doi/10.1103/PhysRevD.110.106014"
[2]: https://arxiv.org/abs/1512.00589 "https://arxiv.org/abs/1512.00589"
[3]: https://arxiv.org/abs/2109.06155 "https://arxiv.org/abs/2109.06155"
[4]: https://arxiv.org/abs/1810.09826 "https://arxiv.org/abs/1810.09826"
[5]: https://arxiv.org/abs/1707.06036 "https://arxiv.org/abs/1707.06036"
# 经典几何的动力稳定性、宏观极限与残余量子涨落

## ——量子观察者—关系时空理论第一百一十一至第一百二十节增订

### 摘要

上一轮证明了：在指定结构态的支持上，若全部钟速算子都作用为同一组标量，则相关量子钟过程可以通过一个确定的经典几何描述。

但这里仍有一个关键缺口：

> **初始时刻能够使用一张经典几何，不意味着结构自身演化之后，观察者仍然能够使用这张几何。**

本增订处理这一问题，并进一步构造从有限量子模型逼近动态经典钟律的机制。主要结果为：

$$
\boxed{
\text{精确经典性}
+
\text{动力不变性}
\longrightarrow
\text{持续有效的经典描述};
}
$$

$$
\boxed{
\text{大量结构单元}
+
\text{受控关联}
+
\text{有限实验资源}
\longrightarrow
\text{具有误差界的宏观经典钟律}.
}
$$

其中还有一个重要的有限维限制：**固定的有限维钟速算子若在连续演化中始终具有严格零方差，其确定读数不能连续改变。**动态经典几何因此不能简单依靠“有限结构永远处于某个精确本征态”来解释。

随后给出的宏观模型绕开了这个限制：每个有限模型都保留小而非零的量子涨落，但在固定实验范围内，它们共同逼近一组连续变化的钟律。该钟律可以重建出曲率非零的候选度量。

这里得到的仍是**钟过程的几何实现**。共同信号光锥、普适物质耦合和引力场方程，必须另行建立。

---

# 111．加入结构自身的动力学

## 定义 111.1　静态经典扇区

设结构空间为有限维 Hilbert 空间：

$$
\mathcal H_G,\qquad \dim\mathcal H_G=D.
$$

给定一组正定钟速算子：

$$
\widehat n_1,\ldots,\widehat n_m>0.
$$

对指定标量钟速：

$$
\nu_1,\ldots,\nu_m>0,
$$

定义共同经典扇区：

$$
\boxed{
\mathcal E_\nu
=
\bigcap_{a=1}^m
\ker(\widehat n_a-\nu_aI).
}
\tag{111.1}
$$

记其正交投影为 \(P\)，并要求：

$$
P\ne0.
$$

对任意支持在该扇区中的状态 \(\sigma\)：

$$
\widehat n_aP=\nu_aP,
$$

所以对应钟交互不会把结构的不同分量转译成不同钟速。

现在加入结构自身的 Hamiltonian：

$$
H_G=H_G^\dagger.
$$

完整的观察者—结构 Hamiltonian 取为：

$$
\boxed{
H_{\mathrm{tot}}
=
H_O\otimes I_G
+
I_O\otimes H_G
+
\sum_aF_a\otimes\widehat n_a,
}
\tag{111.2}
$$

其中 \(F_a=F_a^\dagger\) 是观察者钟或控制寄存器上的算子。

---

## 定理 111.1　经典扇区持续有效的充要条件

以下条件等价：

1. 对全部 \(t\in\mathbb R\)，

   $$
   e^{-itH_G/\hbar}\mathcal E_\nu
   \subseteq\mathcal E_\nu;
   $$
2. $$
   (I-P)H_GP=0;
   $$
3. $$
   \boxed{[H_G,P]=0.}
   \tag{111.3}
   $$

这些条件成立时，完整 Hamiltonian 在
\(\mathcal H_O\otimes\mathcal E_\nu\) 上具有形式：

$$
\boxed{
H_{\mathrm{tot}}\big|_{\mathcal E_\nu}
=
\left(H_O+\sum_a\nu_aF_a\right)\otimes I
+
I\otimes H_G\big|_{\mathcal E_\nu}.
}
\tag{111.4}
$$

### 证明

由条件 1 对 \(t=0\) 求导，得到：

$$
H_G\mathcal E_\nu\subseteq\mathcal E_\nu,
$$

即条件 2。

由于 \(H_G\) 自伴，

$$
\bigl((I-P)H_GP\bigr)^\dagger
=
PH_G(I-P).
$$

因此条件 2 同时消去两个非对角块，等价于条件 3。

条件 3 保证 \(P\) 与 \(H_G\) 的指数可交换，从而得到条件 1。

最后，在该子空间上使用
\(\widehat n_aP=\nu_aP\)，即可得到式（111.4）。∎

### 含义

**经典性有两个独立要求：**

$$
\text{当前结构不产生钟速分支},
$$

以及：

$$
\text{后续动力学不把结构送出这个区域}.
$$

前者是读数性质，后者是稳定性性质。它们不能互相替代。对无退相干子空间的动力稳定性，既有量子理论也需要明确处理这一区分。([arXiv][1])

---

# 112．最大的稳定经典区，可以由项目已有的核结构计算

## 定义 112.1　经典性缺陷读数

定义线性映射：

$$
C_\nu:\mathcal H_G\longrightarrow
\bigoplus_{a=1}^m\mathcal H_G,
$$

$$
\boxed{
C_\nu\psi
=
\bigl((\widehat n_a-\nu_aI)\psi\bigr)_a.
}
\tag{112.1}
$$

因此：

$$
\ker C_\nu=\mathcal E_\nu.
$$

定义全部未来都不离开经典扇区的初态空间：

$$
\boxed{
\mathcal K_\nu
=
\bigcap_{k=0}^\infty
\ker(C_\nu H_G^k).
}
\tag{112.2}
$$

这个定义没有先写“取最大的稳定子空间”，而是从所有未来缺陷读数构造它。

---

## 定理 112.1　最大稳定经典子空间

\(\mathcal K_\nu\) 是包含于 \(\mathcal E_\nu\) 的最大 \(H_G\)-不变线性子空间。

并且：

$$
\boxed{
\mathcal K_\nu
=
\bigcap_{k=0}^{D-1}
\ker(C_\nu H_G^k).
}
\tag{112.3}
$$

### 证明

由 \(k=0\) 的条件：

$$
\mathcal K_\nu\subseteq\ker C_\nu=\mathcal E_\nu.
$$

若 \(\psi\in\mathcal K_\nu\)，则对任意 \(k\)：

$$
C_\nu H_G^k(H_G\psi)
=
C_\nu H_G^{k+1}\psi=0.
$$

所以 \(H_G\mathcal K_\nu\subseteq\mathcal K_\nu\)。

若另一子空间 \(W\subseteq\mathcal E_\nu\) 对 \(H_G\) 不变，则对任意 \(\psi\in W\)，全部 \(H_G^k\psi\) 仍在 \(W\)，故：

$$
C_\nu H_G^k\psi=0.
$$

因此 \(W\subseteq\mathcal K_\nu\)。

最后，Cayley–Hamilton 定理把 \(H_G^D\) 表示为较低次幂的线性组合；递归得到所有更高次幂也在前 \(D\) 个幂的线性包内，故式（112.3）成立。∎

项目的 `MaximalUnobservableSubspace.lean` 已有：

```text
future_kernel_is_maximal_invariant
```

其结论正是“全部未来读数核的交，是当前核内最大的动力不变子空间”。本节将其中的读数具体取为 \(C_\nu\)，并增加有限维的幂截断。

---

## 定理 112.2　观察完成与经典稳定区的对偶关系

定义轨道扩张：

$$
\operatorname{Orb}_{H_G}(W)
=
\operatorname{span}\{H_G^k\psi:
\psi\in W,\ k\ge0\}.
$$

则：

$$
\boxed{
\operatorname{Orb}_{H_G}(W)\subseteq\mathcal E_\nu
\iff
W\subseteq\mathcal K_\nu.
}
\tag{112.4}
$$

### 证明

左侧表示任意 \(\psi\in W\) 的全部幂轨道都落在
\(\ker C_\nu\)，这正好等价于
\(C_\nu H_G^k\psi=0\) 对全部 \(k\) 成立。∎

这与项目的轨道闭包构造形成互补：轨道闭包向外扩张，保留未来可能进入读数的方向；稳定经典区向内筛选，保留永远不会产生指定经典性缺陷的初态。仓库目前读取到的 `ObserverOrbitClosure.lean` 给出了实线性版本的最小不变闭包；复量子应用应明确实化或建立对应复线性版本。

---

## 定理 112.3　记录操作保持经典区的判据

设一次结构操作具有 Kraus 算子 \(L_b\)。它把全部支持于 \(P\) 的状态仍送入 \(P\)，当且仅当：

$$
\boxed{
(I-P)L_bP=0
\qquad\forall b.
}
\tag{112.5}
$$

### 证明

对任意 \(\psi\in P\mathcal H_G\)，输出位于 \(P^\perp\) 的概率为：

$$
\sum_b\|(I-P)L_b\psi\|^2.
$$

它对全部 \(\psi\) 为零，当且仅当每个非负项都为零。∎

因此，**“观察者开始写记忆”也必须经过稳定性检验**。不能先证明某个结构态给出经典钟速，再任意加入记录操作而保留原结论。

---

# 113．有限维精确经典性的动力限制

## 定理 113.1　固定有限维读数的零方差刚性

设 \(\widehat n\) 是固定的有限维 Hermitian 算子，\(\sigma(t)\) 在连通时间区间上连续。

若对每个 \(t\)，存在实数 \(\nu(t)\)，使：

$$
\boxed{
\operatorname{Tr}
\left[
\sigma(t)(\widehat n-\nu(t)I)^2
\right]=0,
}
\tag{113.1}
$$

则 \(\nu(t)\) 必为常数。

### 证明

式（113.1）意味着 \(\sigma(t)\) 的支持完全位于
\(\widehat n\) 的本征值 \(\nu(t)\) 对应子空间。因此：

$$
\nu(t)\in\operatorname{spec}(\widehat n).
$$

同时：

$$
\nu(t)=\operatorname{Tr}[\sigma(t)\widehat n]
$$

随 \(t\) 连续。

有限维算子的谱为有限集。从连通区间到有限集的连续映射只能为常数。∎

### 推论 113.1

对固定的有限个钟速采样算子，若整个连续过程中都严格零方差，那么各采样值不变；由它们重建的度量系数也不变。

这并不禁止不同位置具有不同度量，也不禁止显式改变参照算子。它约束的是：

$$
\boxed{
\text{固定有限维算子}
+
\text{固定标定}
+
\text{全部时刻严格零方差}.
}
$$

三者不能同时产生连续变化的确定读数。

---

## 定理 113.2　离开经典扇区的短时界

令：

$$
Q=I-P,
\qquad
\eta=\|QH_GP\|_{\mathrm{op}}.
$$

则：

$$
\boxed{
\|Qe^{-itH_G/\hbar}P\|_{\mathrm{op}}
\le
\frac{|t|\eta}{\hbar}.
}
\tag{113.2}
$$

因此，对支持在 \(P\) 内的初态，离开概率不超过：

$$
\boxed{
\min\left\{1,\frac{t^2\eta^2}{\hbar^2}\right\}.
}
\tag{113.3}
$$

### 证明

取块对角 Hamiltonian：

$$
H_{\mathrm{diag}}=PH_GP+QH_GQ.
$$

它严格保持 \(P\)。差值为：

$$
H_G-H_{\mathrm{diag}}
=
QH_GP+PH_GQ,
$$

其算子范数等于 \(\eta\)。

由 Duhamel 公式：

$$
\|e^{-itH_G/\hbar}
-e^{-itH_{\mathrm{diag}}/\hbar}\|
\le
|t|\eta/\hbar.
$$

左乘 \(Q\)、右乘 \(P\)，得到结论。∎

---

## 例 113.1　初始经典，不代表持续经典

取：

$$
\widehat n=I+\alpha Z,
\qquad 0<\alpha<1,
$$

$$
H_G=\frac{\hbar\Omega}{2}X,
\qquad
\sigma(0)=|0\rangle\langle0|.
$$

则：

$$
\langle\widehat n\rangle_t
=
1+\alpha\cos\Omega t,
$$

$$
\boxed{
\operatorname{Var}_{\sigma(t)}(\widehat n)
=
\alpha^2\sin^2\Omega t.
}
\tag{113.4}
$$

初始方差为零，但通常的后续时刻不再为零。

**读数发生连续变化时，这个有限模型付出的代价正是中途产生钟速涨落。**

---

# 114．宏观经典性：从大量量子结构单元建立定量机制

上一节并没有排除经典变化，而是提示：严格有限本征态描述可能过强。现在构造一个有限模型序列。

## 定义 114.1　宏观平方钟速

取 \(N\) 个结构单元：

$$
\mathcal H_G^{(N)}
=
\mathcal H_{\mathrm{cell}}^{\otimes N}.
$$

单元上的算子值平方钟律为：

$$
\widehat R(v)
=
\widehat A
+
2\sum_i v_i\widehat B_i
-
\sum_{i,j}v_iv_j\widehat C_{ij}.
$$

在固定方向域中要求：

$$
\boxed{
\widehat R(v)\ge n_*^2I,
\qquad n_*>0.
}
\tag{114.1}
$$

定义：

$$
\boxed{
\widehat R_N(v)
=
\frac1N\sum_{j=1}^N\widehat R(v)^{(j)},
}
\tag{114.2}
$$

$$
\boxed{
\widehat n_N(v)=\widehat R_N(v)^{1/2}.
}
\tag{114.3}
$$

**平方响应作为宏观可加量，是这里明确选择的耦合结构。**它不等于直接平均各单元的钟速；第 119 节将证明两者可能产生不同几何。

---

## 定理 114.1　宏观系数渐近可交换

对任意两个单元算子 \(A,B\)，记：

$$
\overline A_N=\frac1N\sum_jA^{(j)},
\qquad
\overline B_N=\frac1N\sum_jB^{(j)}.
$$

则：

$$
\boxed{
[\overline A_N,\overline B_N]
=
\frac1{N^2}\sum_j[A,B]^{(j)},
}
\tag{114.4}
$$

所以：

$$
\boxed{
\|[\overline A_N,\overline B_N]\|
\le
\frac{\|[A,B]\|}{N}.
}
\tag{114.5}
$$

### 证明

不同单元上的算子可交换，因此双重求和只保留相同单元的项。再用范数三角不等式。∎

但渐近可交换还不足以给出确定读数，还必须控制状态中的相关性。

---

## 定理 114.2　关联求和控制宏观涨落

设 \(\sigma_N\) 为任意联合结构态，定义：

$$
r_N(v)=\operatorname{Tr}[\sigma_N\widehat R_N(v)].
$$

若对指定方向 \(v\)：

$$
\boxed{
\sum_{i,j}
\left|
\operatorname{Cov}_{\sigma_N}
\bigl(\widehat R^{(i)},\widehat R^{(j)}\bigr)
\right|
\le
N\Gamma(v),
}
\tag{114.6}
$$

则：

$$
\boxed{
\operatorname{Var}_{\sigma_N}(\widehat R_N(v))
\le
\frac{\Gamma(v)}N.
}
\tag{114.7}
$$

进一步：

$$
\boxed{
\left\|
\left(
\widehat n_N(v)-\sqrt{r_N(v)}I
\right)\sigma_N^{1/2}
\right\|_2
\le
\frac{\sqrt{\Gamma(v)}}{2n_*\sqrt N}.
}
\tag{114.8}
$$

### 证明

方差展开为：

$$
\operatorname{Var}(\widehat R_N)
=
\frac1{N^2}
\sum_{i,j}
\operatorname{Cov}(\widehat R^{(i)},\widehat R^{(j)}),
$$

取绝对值界得到式（114.7）。

由于：

$$
\widehat n_N\ge n_*I,
\qquad
\sqrt{r_N}\ge n_*,
$$

有：

$$
\widehat n_N-\sqrt{r_N}I
=
(\widehat n_N+\sqrt{r_N}I)^{-1}
(\widehat R_N-r_NI).
$$

逆算子范数不超过 \(1/(2n_*)\)，从而得到式（114.8）。∎

### 乘积态特化

若：

$$
\sigma_N=\tau^{\otimes N},
$$

则跨单元协方差为零，故：

$$
\boxed{
\Gamma(v)=\operatorname{Var}_\tau(\widehat R(v)).
}
\tag{114.9}
$$

这些结果只使用有限维二阶相关求和，不需要先假设一个完整的无限系统。

宏观平均趋于可交换、而适当重标定的涨落仍可保留量子结构，是量子中心极限研究中的已知分层现象。([Springer][2])

---

# 115．宏观近似必须对完整交互成立，而不只对平均值成立

## 假设 115.1　结构自身演化与有限观察协议

令完整结构 Hamiltonian 为：

$$
H_G^{(N)}.
$$

在没有观察者耦合时，结构参考演化为：

$$
\sigma_N^0(t)
=
e^{-itH_G^{(N)}/\hbar}
\sigma_N(0)
e^{itH_G^{(N)}/\hbar}.
$$

定义标量钟律：

$$
r(t,v)
=
\operatorname{Tr}[\sigma_N^0(t)\widehat R_N(v)],
$$

$$
n(t,v)=\sqrt{r(t,v)}.
$$

实际联合 Hamiltonian 为：

$$
\boxed{
H_{\mathrm{act}}(t)
=
H_O(t)\otimes I
+
I\otimes H_G^{(N)}
+
\sum_aF_a(t)\otimes\widehat n_N(v_a(t)).
}
\tag{115.1}
$$

候选经典过程使用：

$$
\boxed{
H_{\mathrm{cl}}(t)
=
\left[
H_O(t)+\sum_a n(t,v_a(t))F_a(t)
\right]\otimes I
+
I\otimes H_G^{(N)}.
}
\tag{115.2}
$$

初始结构与观察者及其测试参照独立。控制装置的允许范围仍需另外说明；本定理不把时变控制当作无成本操作。

---

## 定理 115.1　宏观经典化的全过程误差界

假设沿参考结构演化，式（114.6）以 \(\Gamma(t,v)\) 成立。

设 \(\mathcal P_N\) 与 \(\mathcal P_{\mathrm{cl}}\) 分别为实际与候选过程的观察者输出通道，则：

$$
\boxed{
\frac12
\|\mathcal P_N-\mathcal P_{\mathrm{cl}}\|_\diamond
\le
\frac1{2\hbar n_*\sqrt N}
\int_0^T
\sum_a
\|F_a(t)\|
\sqrt{\Gamma(t,v_a(t))}
\,dt.
}
\tag{115.3}
$$

### 证明

纯化初始结构态。候选演化中，结构与观察者保持乘积，其结构部分正是 \(\sigma_N^0(t)\) 的纯化。

Duhamel 公式给出：

$$
U_{\mathrm{act}}(T)-U_{\mathrm{cl}}(T)
=
-\frac i\hbar
\int_0^T
U_{\mathrm{act}}(T,t)
\bigl(H_{\mathrm{act}}(t)-H_{\mathrm{cl}}(t)\bigr)
U_{\mathrm{cl}}(t)\,dt.
$$

对每个积分项，左侧实际后缀酉演化不增加范数；右侧候选前缀的结构态已知。

使用定理 114.2：

$$
\left\|
(\widehat n_N-n)\bigl(\sigma_N^0(t)\bigr)^{1/2}
\right\|_2
\le
\frac{\sqrt{\Gamma(t,v)}}{2n_*\sqrt N}.
$$

再对观察者输入及任意附加测试参照取上确界，得到式（115.3）。∎

### 两项关键结论

第一，本证明**没有假设实际环境在每一步重新初始化**。实际过程中的关联与反作用都保留在 \(U_{\mathrm{act}}\) 中。

第二，若：

$$
\Gamma(t,v)\le\Gamma_*,
$$

并定义无量纲实验预算：

$$
\mathcal B(T)
=
\frac1\hbar
\int_0^T\sum_a\|F_a(t)\|\,dt,
$$

则：

$$
\boxed{
\frac12
\|\mathcal P_N-\mathcal P_{\mathrm{cl}}\|_\diamond
\le
\frac{\sqrt{\Gamma_*}}{2n_*}
\frac{\mathcal B(T)}{\sqrt N}.
}
\tag{115.4}
$$

因此，固定预算的观察者可以看到趋于确定的经典钟律，尽管每个有限 \(N\) 的完整模型仍然量子化。

---

# 116．一个连续变化、曲率非零的钟律候选

现在给出一个不只停留在一般估计上的实例。

## 定义 116.1　单元与内部演化

每个结构单元是量子比特。取：

$$
\widehat A=3I+X,
$$

$$
\widehat C=I+\frac12Z.
$$

定义一维方向变量 \(|v|\le1\) 下的平方钟律：

$$
\boxed{
\widehat R(v)
=
\widehat A-v^2\widehat C
=
(3-v^2)I+X-\frac{v^2}{2}Z.
}
\tag{116.1}
$$

由于：

$$
\widehat A\ge2I,
\qquad
0<\widehat C\le\frac32I,
$$

有：

$$
\boxed{
\widehat R(v)\ge\frac12I.
}
\tag{116.2}
$$

所以可以取：

$$
n_*=\frac1{\sqrt2}.
$$

每个结构单元初始为 \(|0\rangle\)，其 Hamiltonian 取：

$$
h=\frac{\hbar\Omega}{2}(I+Y),
\qquad \Omega>0.
$$

该算子非负；恒等部分只贡献整体相位。完整自由结构演化取：

$$
H_G^{(N)}=\sum_{j=1}^Nh^{(j)}.
$$

因此参考结构态在任意时刻都保持乘积形式。

---

## 定理 116.1　非交换微观系数产生动态宏观钟律

参考单元态满足：

$$
\langle X\rangle_t=\sin\Omega t,
\qquad
\langle Z\rangle_t=\cos\Omega t.
$$

所以：

$$
\boxed{
r(t,v)
=
3+\sin\Omega t
-
\left(1+\frac12\cos\Omega t\right)v^2.
}
\tag{116.3}
$$

并且：

$$
\boxed{
\operatorname{Var}_{\tau(t)}(\widehat R(v))
=
1+\frac{v^4}{4}
-
\left(
\sin\Omega t-\frac{v^2}{2}\cos\Omega t
\right)^2
\le\frac54.
}
\tag{116.4}
$$

因此，任意符合第 115 节条件的有限观察协议满足：

$$
\boxed{
\frac12
\|\mathcal P_N-\mathcal P_{\mathrm{cl}}\|_\diamond
\le
\sqrt{\frac5{8N}}\,
\mathcal B(T).
}
\tag{116.5}
$$

### 证明

单量子比特绕 \(Y\) 轴的酉旋转给出前两个期望。

对式（116.1）取期望得到式（116.3）。

利用：

$$
X^2=Z^2=I,
\qquad
XZ+ZX=0,
$$

计算二阶矩后减去均值平方，即得式（116.4）。

最后将 \(\Gamma_*=5/4\) 和 \(n_*=1/\sqrt2\) 代入式（115.4）。∎

注意：

$$
[\widehat A,\widehat C]=-iY\ne0.
$$

所以微观系数并没有被预先定义成可交换经典变量。

---

## 定理 116.2　重建的候选度量具有非零曲率

采用既定局部时间—长度标定，式（116.3）重建出：

$$
\boxed{
ds^2
=
-a(t)\,dt^2+C(t)\,dx^2,
}
\tag{116.6}
$$

其中：

$$
a(t)=3+\sin\Omega t,
$$

$$
C(t)=1+\frac12\cos\Omega t.
$$

在曲率约定

$$
R_{\mu\nu}
=
\partial_\rho\Gamma^\rho_{\mu\nu}
-
\partial_\nu\Gamma^\rho_{\mu\rho}
+\cdots
$$

下，其标量曲率在 \(t=0\) 为：

$$
\boxed{
\operatorname{Scal}(g)\big|_{t=0}
=
-\frac{\Omega^2}{9}\ne0.
}
\tag{116.7}
$$

### 证明

对度量（116.6）计算得：

$$
\operatorname{Scal}(g)
=
\frac{C''}{aC}
-
\frac{(C')^2}{2aC^2}
-
\frac{a'C'}{2a^2C}.
$$

在 \(t=0\)：

$$
a=3,\qquad
C=\frac32,\qquad
C'=0,\qquad
C''=-\frac{\Omega^2}{2}.
$$

代入即得式（116.7）。∎

### 结论与边界

这不是单纯通过坐标更名制造的时间变化，因为曲率不为零。

但它目前证明的是：

$$
\boxed{
\text{一个有限量子模型序列，
在固定资源实验中逼近曲率非零的钟律候选。}
}
$$

要把该候选升级为所有物质共同读取的物理时空，仍须证明相应信号传播遵守同一个零锥，并建立物质与结构的普适反作用。

---

# 117．宏观经典性会在哪些情况下失效？

## 定理 117.1　长程相关可以阻止方差衰减

取：

$$
\widehat n_N
=
I+\alpha\overline Z_N,
\qquad
\overline Z_N=\frac1N\sum_jZ_j,
\qquad
0<\alpha<1.
$$

比较两个结构态：

$$
\sigma_{\mathrm{ind}}
=
\left(\frac I2\right)^{\otimes N},
$$

以及：

$$
|\mathrm{GHZ}_N\rangle
=
\frac{|0\rangle^{\otimes N}+|1\rangle^{\otimes N}}{\sqrt2}.
$$

它们的每个单元边缘态都为 \(I/2\)，但：

$$
\boxed{
\operatorname{Var}_{\sigma_{\mathrm{ind}}}(\widehat n_N)
=
\frac{\alpha^2}{N},
}
\tag{117.1}
$$

$$
\boxed{
\operatorname{Var}_{\mathrm{GHZ}_N}(\widehat n_N)
=
\alpha^2.
}
\tag{117.2}
$$

### 证明

独立态中，\(\langle Z_iZ_j\rangle=0\) 对 \(i\ne j\) 成立，因此：

$$
\langle\overline Z_N^2\rangle=\frac1N.
$$

GHZ 态中，对全部 \(i,j\)：

$$
\langle Z_iZ_j\rangle=1,
$$

故 \(\langle\overline Z_N^2\rangle=1\)。两态均满足 \(\langle\overline Z_N\rangle=0\)。∎

因此：

$$
\boxed{
\text{结构单元很多}
\not\Rightarrow
\text{读数自动集中}.
}
$$

真正需要的是关联求和得到控制。

将 GHZ 态退相干为：

$$
\frac12|0\cdots0\rangle\langle0\cdots0|
+
\frac12|1\cdots1\rangle\langle1\cdots1|
$$

不会改变式（117.2）。这时量子分支间相干消失了，但仍然存在两个不同的经典钟速分支。

**退相干可以产生经典混合，却不自动选出一张确定几何。**项目中的记录通道证明的是特定相干块如何改变，不应把它解释成宏观方差必然消失。

---

## 定理 117.2　固定时间经典化不等于全部时间统一经典化

在 \(\sigma_{\mathrm{ind}}\) 上，取结构自由 Hamiltonian 为零，钟能级差为 \(\hbar\omega\)。则：

$$
\boxed{
\chi_N(t)
=
e^{-i\omega t}
\left[
\cos\left(\frac{\alpha\omega t}{N}\right)
\right]^N.
}
\tag{117.3}
$$

固定 \(t\) 时：

$$
\chi_N(t)\longrightarrow e^{-i\omega t}.
$$

但若：

$$
t_N=\frac{s\sqrt N}{\alpha\omega},
$$

则：

$$
\boxed{
|\chi_N(t_N)|
\longrightarrow e^{-s^2/2}.
}
\tag{117.4}
$$

### 证明

不同单元的 \(Z_j\) 可交换，初态为乘积态，所以特征函数分解为 \(N\) 个余弦因子的乘积。

固定 \(t\) 时，用 \(\log\cos x=-x^2/2+O(x^4)\)，得到模长趋于一。

对 \(t_N\)，余弦自变量为 \(s/\sqrt N\)，所以：

$$
N\log\cos(s/\sqrt N)\longrightarrow-\frac{s^2}{2}.
$$

∎

因此，量子差别可以在较长的相干询问时间上重新变得可见。

这与第 115 节不矛盾：其误差取决于

$$
\mathcal B(T)/\sqrt N,
$$

而不是只取决于 \(N\)。

---

# 118．经典背景出现后，量子涨落并不必然消失

## 定义 118.1　涨落尺度算子

对乘积态 \(\tau^{\otimes N}\)，定义：

$$
F_N(A)
=
\frac1{\sqrt N}
\sum_{j=1}^N
\left(A^{(j)}-\langle A\rangle_\tau I\right).
$$

与宏观平均不同，它保留 \(N^{-1/2}\) 尺度的偏离。

---

## 定理 118.1　平均量可交换，而涨落量仍可非交换

有：

$$
\boxed{
[F_N(A),F_N(B)]
=
\frac1N\sum_j[A,B]^{(j)}.
}
\tag{118.1}
$$

例如取：

$$
\tau=\frac12(I+mZ),
\qquad
0<m\le1.
$$

则：

$$
[F_N(X),F_N(Y)]=2i\overline Z_N,
$$

并且：

$$
\boxed{
\left\|
\left(
[F_N(X),F_N(Y)]-2imI
\right)
(\tau^{\otimes N})^{1/2}
\right\|_2^2
=
\frac{4(1-m^2)}N.
}
\tag{118.2}
$$

而宏观平均满足：

$$
\boxed{
\|[\overline X_N,\overline Y_N]\|
\le\frac2N.
}
\tag{118.3}
$$

### 证明

式（118.1）由不同单元可交换得到。

再使用：

$$
[X,Y]=2iZ,
$$

以及乘积态中的：

$$
\langle\overline Z_N\rangle=m,
\qquad
\operatorname{Var}(\overline Z_N)=\frac{1-m^2}{N},
$$

即得式（118.2）。∎

### 含义

宏观平均可以趋于经典标量，但适当放大的涨落仍然具有非零量子对易结构。

这里没有声称有限维矩阵严格满足全空间上的正则对易关系。式（118.2）是指定态下的加权收敛。

在合适条件下，这类结构可以进一步由量子中心极限定理组织为非交换涨落代数。([Springer][2])

因此，合理的分层可能是：

$$
\boxed{
\text{宏观经典钟律}
+
\text{其上的量子涨落}.
}
$$

而不是：

$$
\text{只要得到经典背景，就必须删除全部量子结构}.
$$

不过，这些涨落还不能仅凭名称被称为引力子。它们的传播方程、对称性、约束及与物质的耦合均须单独推导。

---

# 119．宏观极限本身也必须由具体耦合决定

第 114 节选择：

$$
\widehat n_N
=
\sqrt{\frac1N\sum_j\widehat R_j}.
$$

另一种同样可以定义的过程是：

$$
\widehat n_N'
=
\frac1N\sum_j\sqrt{\widehat R_j}.
$$

两者一般不相同。

## 定理 119.1　平均局部钟速不必得到二次平方钟律

取两个合法标量钟速：

$$
n_1(v)=\sqrt{1-v^2},
$$

$$
n_2(v)=\sqrt{1-4v^2},
\qquad |v|<\frac12.
$$

定义平均钟速：

$$
n_{\mathrm{av}}(v)=\frac{n_1(v)+n_2(v)}2.
$$

则其平方在零点附近为：

$$
\boxed{
n_{\mathrm{av}}(v)^2
=
1-\frac52v^2-\frac9{16}v^4+O(v^6).
}
\tag{119.1}
$$

因此它不是一个精确的二次钟律。

但若平均平方再取根，则：

$$
\boxed{
n_{\mathrm{sq}}(v)
=
\sqrt{\frac{n_1(v)^2+n_2(v)^2}{2}}
=
\sqrt{1-\frac52v^2},
}
\tag{119.2}
$$

其平方严格为二次函数。

### 证明

直接计算：

$$
n_{\mathrm{av}}^2
=
\frac12-\frac54v^2
+
\frac12\sqrt{1-5v^2+4v^4}.
$$

在 \(v=0\) 作 Taylor 展开即得式（119.1）。式（119.2）直接成立。∎

### 结论

$$
\boxed{
\text{不同局部时钟各自具有几何解释}
}
$$

不保证：

$$
\boxed{
\text{任意组合方式仍然由一张洛伦兹度量描述}.
}
$$

因此，平方响应作为宏观可加量，必须由具体能量耦合、控制电路或实验事实支持。

定理 114—116 给出的是：

> **如果物理实现采用这种集体响应，那么它产生怎样的宏观几何及误差。**

它还不是：

> 所有量子结构在任何组合规则下都必然产生同样的现实物理。

这一区别也涉及局域性。算子
\(\sqrt{\frac1N\sum_j\widehat R_j}\)
在有限空间中定义良好，但它的局域电路实现、资源规模和传播限制，必须另行认证。

---

# 120．动态经典几何的可形式化证书

本轮可以把此前的“经典几何成立”升级成两种不同的证书。

## 定义 120.1　精确稳定证书

一份精确稳定证书包含：

$$
P\ne0,
$$

$$
\widehat n_aP=\nu_aP,
$$

$$
[H_G,P]=0,
$$

以及全部允许记录与控制操作的支持保持条件：

$$
(I-P)L_bP=0.
$$

这些条件证明：相关过程可以持续使用同一组确定钟速，而不是只在初始时刻成立。

---

## 定义 120.2　宏观近似证书

一份宏观近似证书包含：

$$
\widehat R_N(v)\ge n_*^2I,
$$

明确的结构参考演化 \(\sigma_N^0(t)\)，以及：

$$
\sum_{i,j}
|\operatorname{Cov}(\widehat R^{(i)},\widehat R^{(j)})|
\le N\Gamma(t,v).
$$

再给出有限实验预算：

$$
\mathcal B(T)
=
\frac1\hbar\int_0^T\sum_a\|F_a(t)\|\,dt,
$$

并证明过程距离：

$$
\boxed{
\frac12\|\mathcal P_N-\mathcal P_{\mathrm{cl}}\|_\diamond
\le\varepsilon_N.
}
\tag{120.1}
$$

只有当候选钟律还满足前文的二次性、Lorentz 符号、跨观察者拼接与共同信号条件时，才能进一步称为物理时空的有效实现。

---

## 定理 120.1　本轮的条件性宏观重建结论

对第 114—115 节的模型族，若：

$$
\Gamma(t,v)\le\Gamma_*,
\qquad
n_*>0
$$

在给定实验域内一致成立，则：

$$
\boxed{
\varepsilon_N
\le
\frac{\sqrt{\Gamma_*}}{2n_*}
\frac{\mathcal B(T)}{\sqrt N}.
}
\tag{120.2}
$$

因此，对每个固定预算的实验族：

$$
\varepsilon_N\longrightarrow0.
$$

但这一结论一般不能扩展为对全部初态、全部时间、全部控制预算的一致收敛。

### 证明

正向结论由定理 115.1。

不一致性的反例分别由第 117 节的长程相关态及 \(t_N\sim\sqrt N\) 的询问协议给出。∎

---

## 与项目形式化结构的对应

本轮可以直接连接三个已经读取的项目对象：

**全部未来核**用于构造最大稳定经典区，而不是只检查当前读数。`future_kernel_is_maximal_invariant` 已包含其最大性与不变性证明。

**轨道闭包**用于展开未来实验可能访问的空间，与稳定经典区形成式（112.4）的互补关系。

**记录通道**用于检查记忆写入如何改变相干，以及是否保持已选择的经典区；不能由记录形成直接推断涨落消失。

新增的形式化任务可以明确分为：

$$
\boxed{
\text{有限矩阵核与 Cayley–Hamilton 截断};
}
$$

$$
\boxed{
\text{协方差求和与平方根误差};
}
$$

$$
\boxed{
\text{联合酉过程的 Duhamel 误差};
}
$$

$$
\boxed{
\text{标量钟律的度量与曲率重建}.
}
$$

本轮新增综合命题为上述纸面证明，尚未进行 Lean 编译。已用符号运算核对第 116 节的均值、方差与曲率；有限维联合演化的数值实例也与全过程上界一致，但这些核验不替代一般形式化证明。

---

# 结论

本轮把问题从：

$$
\text{某个量子态能否给出经典几何}
$$

推进为：

$$
\boxed{
\text{这种描述能否在内部演化和连续观测下稳定成立？}
}
$$

我们得到了两个互补答案。

**精确答案：**经典描述需要一个共同标量作用的子空间，而且该子空间必须被结构动力学与允许记录操作保持。

**宏观答案：**不必要求每个有限模型严格经典。大量量子结构单元在关联受控时，可以使完整有限实验逐渐逼近一个动态经典钟律，误差由：

$$
\boxed{
\frac{\text{实验资源预算}}{\sqrt{\text{有效结构单元数}}}
}
$$

及相关性、最低钟速等参数控制。

这条路线已经产生了一个明确的结果：**非交换的有限量子结构，可以在受控宏观极限中给出连续变化、曲率非零的钟律候选，而不需要假装微观量子性已经完全消失。**

同时，长程相关、高精度长时间实验和涨落尺度读数，可以重新揭示被宏观描述忽略的结构。

因此，更合适的理论层级是：

$$
\boxed{
\text{量子交互与记忆}
\longrightarrow
\text{受控宏观钟律}
\longrightarrow
\text{候选时空几何}
}
$$

并保留：

$$
\boxed{
\text{稳定性条件}
+
\text{有限资源误差}
+
\text{量子涨落}
+
\text{共同传播与反作用约束}.
}
$$

**经典时空并不是观察者把量子世界“看成经典”的任意选择；它是在指定结构、状态和实验尺度下，完整量子过程确实允许的一种稳定压缩。**当相关性或实验资源使误差不再受控时，理论就必须恢复被压缩的量子自由度，而不能继续把同一张几何强行用于所有现象。

[1]: https://arxiv.org/html/quant-ph/0702243v3 "https://arxiv.org/html/quant-ph/0702243v3"
[2]: https://link.springer.com/article/10.1007/BF01257415 "https://link.springer.com/article/10.1007/BF01257415"
# 因果粗粒化与局域时空的有效窗口

## ——量子观察者—关系时空理论第一百二十一至第一百三十节增订

### 摘要

上一轮建立了宏观经典钟律的误差界，但其中有两个条件尚需进一步展开：

第一，结构单元之间的关联为何保持可控？

第二，一个局域观察者怎样实际取得宏观平均，而不偷偷使用瞬时、非局域的操作？

本增订从**有限深度局域量子电路**出发，证明因果支持、关联增长、局部平均涨落和观察者读取范围之间的关系。随后导出：

$$
\boxed{
\text{经典钟律误差}
\lesssim
\text{实验预算}
\left[
\left(\frac{\text{关联影响尺度}}{\text{平均尺度}}\right)^{D/2}
+
\frac{\text{平均尺度}}{\text{背景变化尺度}}
\right].
}
$$

该式表明：平均区域不能过小，也不能任意大。过小不能充分压低涨落；过大会混合不同位置的几何响应。

同时，本文证明两个限制：

$$
\boxed{
\text{局域观察者不能瞬时读取任意远处的宏观平均};
}
$$

$$
\boxed{
\text{钟过程一致接近}
\not\Rightarrow
\text{曲率一致接近}.
}
$$

局域动力学限制关联传播，是 Lieb–Robinson 理论及其相关研究的既有内容。以下先在完全有限的电路模型中给出直接证明，再说明连续时间推广所需的条件。([arXiv][1])

---

# 121．从交互规则定义因果支持，而不是先假定连续时空

## 定义 121.1　有限局域结构

设有限连通图为

$$
G=(\Lambda,E),
$$

其图距离为 \(d_G\)。每个节点 \(x\) 带有有限维 Hilbert 空间：

$$
\mathcal H_x.
$$

完整结构空间为

$$
\mathcal H_\Lambda
=
\bigotimes_{x\in\Lambda}\mathcal H_x.
$$

记 \(\mathcal A_X\) 为仅作用于节点集合 \(X\subseteq\Lambda\) 的算子代数。

这里的图首先表示**允许直接交互的关系**。图距离尚不是米制空间距离；后者需要实际钟与信号标定。

---

## 定义 121.2　局域电路层

第 \(j\) 层酉操作为

$$
U_j=\prod_\alpha U_{j,\alpha},
$$

其中，同一层中不同门的支持互不相交，并满足

$$
\operatorname{diam}_G(\operatorname{supp}U_{j,\alpha})
\le r_0.
$$

经过 \(m\) 层后的完整操作为

$$
\mathcal U_m=U_m\cdots U_1.
$$

所有经典控制信号若参与反馈，也必须包含在相应局域寄存器与门中。不能额外允许瞬时传遍全图的经典通信。

---

## 定理 121.1　有限电路的严格因果支持

若

$$
O_X\in\mathcal A_X,
$$

则

$$
\boxed{
\mathcal U_m^\dagger O_X\mathcal U_m
\in
\mathcal A_{B_{mr_0}(X)},
}
\tag{121.1}
$$

其中

$$
B_r(X)=\{y:d_G(y,X)\le r\}.
$$

### 证明

一层中，与 \(O_X\) 支持不相交的门与它可交换，在共轭作用中相消。

只有与当前支持相交的门可能扩大支持。每个门的直径至多为 \(r_0\)，因此一次共轭最多把支持扩大到其 \(r_0\)-邻域。

对层数归纳，即得式（121.1）。∎

### 解释

这个模型中的因果范围是由操作语法证明出来的：

$$
\boxed{
\text{有限门支持}
+
\text{有限组合深度}
\longrightarrow
\text{有限影响域}.
}
$$

它还不是已经恢复的完整相对论时空，但已经给出时空重建不能违反的底层传播约束。

---

# 122．因果支持直接产生项目中的精确下降

## 定义 122.1　有限时刻的观察接口

观察者在输出区域 \(X\) 读取状态：

$$
q_X(\rho)=\operatorname{Tr}_{\Lambda\setminus X}\rho.
$$

令

$$
Z=B_{mr_0}(X).
$$

输入接口为

$$
q_Z(\rho)=\operatorname{Tr}_{\Lambda\setminus Z}\rho.
$$

---

## 定理 122.1　有限因果域足以决定输出

存在完全正、保迹映射

$$
\overline\Phi_{X,m}:\mathcal D(\mathcal H_Z)
\to\mathcal D(\mathcal H_X),
$$

使对全部联合初态——包括具有初始纠缠的状态——成立：

$$
\boxed{
q_X(\mathcal U_m\rho\mathcal U_m^\dagger)
=
\overline\Phi_{X,m}(q_Z(\rho)).
}
\tag{122.1}
$$

### 证明

对输出区域任意效果 \(E_X\)，定理 121.1 保证

$$
\mathcal U_m^\dagger(E_X\otimes I)\mathcal U_m
$$

只支持于 \(Z\)。

因此其期望只依赖输入约化态 \(q_Z(\rho)\)。

为显式构造通道，任选一个固定的外部辅助态 \(\tau_{\Lambda\setminus Z}\)，定义

$$
\overline\Phi_{X,m}(\sigma)
=
q_X\!\left(
\mathcal U_m
(\sigma\otimes\tau)
\mathcal U_m^\dagger
\right).
$$

该映射完全正、保迹。由于所有输出效果的拉回都只支持于 \(Z\)，它与原联合态的外部部分及关联无关，故得到式（122.1）。∎

这里的固定辅助态只用于构造下降映射，不表示真实过程每一步都重新初始化环境。

---

## 推论 122.1　有限因果不可见性

若两种初态满足

$$
q_Z(\rho)=q_Z(\sigma),
$$

则

$$
q_X(\mathcal U_m\rho\mathcal U_m^\dagger)
=
q_X(\mathcal U_m\sigma\mathcal U_m^\dagger).
$$

这正是项目 `ExactDescentNoCarry.lean` 所处理的交换方块：一旦下降等式成立，同一输入纤维中的两个状态不能在目标读数上分离。

### 与视界的区别

这里证明的是：

$$
\text{在指定有限深度内不可见}.
$$

它不等于：

$$
\text{在全部未来永远不可见}.
$$

随着 \(m\) 增长，因果域可以扩大。要讨论永久不可见性，需要对所有未来实验取交；项目的全部未来核与最大不变隐藏子空间正是处理这种更强目标。

因此，有限观察窗口外的节点不能仅凭“暂时不可见”被称为黑洞内部。

---

# 123．从局域动力学证明关联增长界

上一轮把协方差求和界作为假设。本节在一类明确初态下推导它。

## 假设 123.1　初始乘积结构

设

$$
\sigma_0=\bigotimes_{x\in\Lambda}\sigma_x,
$$

并令

$$
\sigma_m=\mathcal U_m\sigma_0\mathcal U_m^\dagger.
$$

对每个节点给定 Hermitian 读数 \(R_x\)，其谱满足共同界：

$$
r_-I\le R_x\le r_+I,
\qquad
0<r_-<r_+.
$$

记

$$
\Delta_R=\frac{r_+-r_-}{2}.
$$

---

## 定义 123.1　实际过去影响域

沿具体电路逆向追踪输出节点 \(x\)，得到一个初始节点集合：

$$
\mathsf P_m(x).
$$

它满足

$$
\mathcal U_m^\dagger R_x\mathcal U_m
\in\mathcal A_{\mathsf P_m(x)},
$$

以及

$$
\mathsf P_m(x)\subseteq B_{mr_0}(x).
$$

它可以由有限门支持的并集递归计算，不必通过模拟全部量子态求出。

---

## 定理 123.1　不相交过去域不产生连通关联

若

$$
\mathsf P_m(x)\cap\mathsf P_m(y)=\varnothing,
$$

则

$$
\boxed{
\operatorname{Cov}_{\sigma_m}(R_x,R_y)=0.
}
\tag{123.1}
$$

特别地，若

$$
d_G(x,y)>2mr_0,
$$

则该协方差为零。

### 证明

把两个读数拉回初始时刻：

$$
\widetilde R_x=\mathcal U_m^\dagger R_x\mathcal U_m,
\qquad
\widetilde R_y=\mathcal U_m^\dagger R_y\mathcal U_m.
$$

它们支持于不相交的初始节点集合。

由于 \(\sigma_0\) 为乘积态，

$$
\operatorname{Tr}(\sigma_0\widetilde R_x\widetilde R_y)
=
\operatorname{Tr}(\sigma_0\widetilde R_x)
\operatorname{Tr}(\sigma_0\widetilde R_y).
$$

故协方差为零。

距离条件保证两个半径 \(mr_0\) 的球不相交。∎

这是一种严格电路版本的关联传播限制。连续时间局域 Hamiltonian 中，相应结论通常具有指数衰减尾部，而不是严格截断。([arXiv][1])

---

## 定义 123.2　过去域重叠数

对平均区域 \(Q\subseteq\Lambda\)，令

$$
N_Q=|Q|,
$$

并定义

$$
\boxed{
b_Q(m)
=
\max_{x\in Q}
\#\left\{
y\in Q:
\mathsf P_m(x)\cap\mathsf P_m(y)\ne\varnothing
\right\}.
}
\tag{123.2}
$$

显然

$$
1\le b_Q(m)\le N_Q.
$$

---

## 定理 123.2　动态协方差求和界

有

$$
\boxed{
\sum_{x,y\in Q}
\left|
\operatorname{Cov}_{\sigma_m}(R_x,R_y)
\right|
\le
N_Q\,b_Q(m)\,\Delta_R^2.
}
\tag{123.3}
$$

### 证明

谱区间界给出

$$
\operatorname{Var}_{\sigma_m}(R_x)\le\Delta_R^2.
$$

由状态上的 Cauchy–Schwarz 不等式，

$$
|\operatorname{Cov}(R_x,R_y)|
\le
\sqrt{\operatorname{Var}(R_x)\operatorname{Var}(R_y)}
\le\Delta_R^2.
$$

对每个 \(x\)，定理 123.1 保证至多 \(b_Q(m)\) 个 \(y\) 可能贡献非零项。求和即得。∎

### 一个直接推论

如果想从乘积态制备两处相距 \(L\)、且连通关联非零的记录，则必须有

$$
m\ge\frac{L}{2r_0}.
$$

因此，上一轮的长程相关反例并不能在任意短的局域演化中无条件产生。这类关联制备时间下界也是局域量子动力学研究的重要结论。([arXiv][1])

---

# 124．局部宏观钟律的经典化误差

## 定义 124.1　区域平均与有效钟速

定义

$$
\widehat R_Q
=
\frac1{N_Q}\sum_{x\in Q}R_x,
$$

$$
\widehat n_Q=\sqrt{\widehat R_Q},
$$

以及参考均值

$$
r_Q(m)=\operatorname{Tr}(\sigma_m\widehat R_Q),
\qquad
n_Q(m)=\sqrt{r_Q(m)}.
$$

令

$$
n_*=\sqrt{r_-}.
$$

由于每个 \(R_x\ge r_-I\)，有

$$
\widehat n_Q\ge n_*I,
\qquad
n_Q(m)\ge n_*.
$$

---

## 定理 124.1　局域动力学控制宏观钟速残差

有

$$
\boxed{
\operatorname{Var}_{\sigma_m}(\widehat R_Q)
\le
\Delta_R^2\frac{b_Q(m)}{N_Q},
}
\tag{124.1}
$$

以及

$$
\boxed{
\left\|
(\widehat n_Q-n_Q(m)I)\sigma_m^{1/2}
\right\|_2
\le
\frac{\Delta_R}{2n_*}
\sqrt{\frac{b_Q(m)}{N_Q}}.
}
\tag{124.2}
$$

### 证明

展开平均算子的方差，并应用定理 123.2，得到式（124.1）。

再使用

$$
\widehat n_Q-n_QI
=
(\widehat n_Q+n_QI)^{-1}
(\widehat R_Q-r_QI).
$$

逆算子范数不超过 \(1/(2n_*)\)，故

$$
\left\|
(\widehat n_Q-n_QI)\sigma_m^{1/2}
\right\|_2
\le
\frac{\sqrt{\operatorname{Var}(\widehat R_Q)}}{2n_*}.
$$

代入式（124.1）。∎

---

## 定义 124.2　由因果证书给出的有效样本数

定义

$$
\boxed{
N_{\mathrm{eff}}(Q,m)
=
\frac{N_Q}{b_Q(m)}.
}
\tag{124.3}
$$

则

$$
\boxed{
\text{钟速残差}
\le
\frac{\Delta_R}{2n_*\sqrt{N_{\mathrm{eff}}}}.
}
\tag{124.4}
$$

这是由当前界定义的保守有效样本数，不是宣称每个影响域实际上都达到最大关联。

**宏观经典性由近乎独立的影响域数量控制，而不只是由总节点数控制。**

---

## 定理 124.2　一次局部快照的统计证书

同一时刻，不同节点的 \(R_x\) 可分别测量。把测得的本征值平均，记为 \(\widehat r_{\mathrm{sample}}\)，则

$$
\mathbb E[\widehat r_{\mathrm{sample}}]=r_Q(m),
$$

且

$$
\boxed{
\Pr\!\left(
|\widehat r_{\mathrm{sample}}-r_Q(m)|\ge\varepsilon
\right)
\le
\frac{
\Delta_R^2b_Q(m)
}{
N_Q\varepsilon^2
}.
}
\tag{124.5}
$$

### 证明

这些局部读数彼此可交换，所以它们的联合测量给出一个经典联合分布。平均结果的方差等于 \(\widehat R_Q\) 的量子方差。

应用式（124.1）及 Chebyshev 不等式。∎

这提供了一个实际统计读取方式，但结果还要通过合法通信汇总。测量也可能改变后续结构态，不能把一次快照的统计定理当成无扰、永久读取能力。

---

# 125．全过程经典化的保证时间窗

## 假设 125.1　明确的钟询问协议

在结构的局域更新之间，插入钟询问：

$$
V_j
=
e^{-i\theta_jK_j\otimes\widehat n_{Q_j}},
$$

其中 \(K_j\) 是无量纲 Hermitian 控制算子。

候选经典询问为

$$
V_j^{\mathrm{cl}}
=
e^{-i\theta_jn_{Q_j}(m_j)K_j}\otimes I.
$$

\(m_j\) 表示候选过程中，该次询问之前已执行的结构层数。

这里的 \(\widehat n_{Q_j}\) 是指定的集体作用目标。它能否在有限局域电路中按所需深度实现，要由第 127 节单独检查，不能被算子定义自动保证。

---

## 定理 125.1　共享结构全过程的误差界

设结构初态为假设 123.1 的乘积态，初始时与观察者及其测试参照独立。

则实际目标过程与经典候选过程的输出通道满足

$$
\boxed{
\frac12
\|\mathcal P-\mathcal P_{\mathrm{cl}}\|_\diamond
\le
\frac{\Delta_R}{2n_*}
\sum_j
|\theta_j|\,\|K_j\|
\sqrt{\frac{b_{Q_j}(m_j)}{N_{Q_j}}}.
}
\tag{125.1}
$$

### 证明

对实际与理想联合酉乘积作望远镜展开。

每个差项的右侧只包含候选前缀，因此结构态为已知的自由局域演化态 \(\sigma_{m_j}\)；左侧实际后缀酉演化不增加范数。

对单个询问，Duhamel 公式给出

$$
\|(V_j-V_j^{\mathrm{cl}})
(\psi\otimes\Sigma_{m_j})\|
\le
|\theta_j|\|K_j\|
\|(\widehat n_{Q_j}-n_{Q_j}I)\sigma_{m_j}^{1/2}\|_2,
$$

其中 \(\Sigma_{m_j}\) 为结构态纯化。

应用定理 124.1，对全部观察者输入及附加测试参照取上确界，即得。∎

这个证明不需要把实际结构在每一步重置。其组合方式与项目已有的 Duhamel 缺陷传播恒等式相容。

---

## 推论 125.1　多项式增长图上的充分时间窗

假设图球满足

$$
|B_r(x)|\le c_+(1+r)^D.
$$

这里 \(D\) 是图体积增长指数，尚未自动等同于现实空间维数。

若所有平均区域大小为 \(N\)，前 \(m\) 次询问均满足

$$
m_j\le m,
\qquad
|\theta_j|\|K_j\|\le a,
$$

则

$$
\boxed{
\frac12
\|\mathcal P-\mathcal P_{\mathrm{cl}}\|_\diamond
\le
\frac{a\Delta_R\sqrt{c_+}}{2n_*}
\frac{m(1+2r_0m)^{D/2}}{\sqrt N}.
}
\tag{125.2}
$$

因此，在这些一致条件下，

$$
\boxed{
m=o\!\left(N^{1/(D+2)}\right)
}
\tag{125.3}
$$

是保证误差趋零的一个充分尺度。

这不是经典描述的最晚失效时刻。界变松不代表实际关联已经达到上界；特殊动力学可以在更长时间内保持小涨落。

---

# 126．平均区域不能无限缩小，也不能无限扩大

上一节只控制涨落。现在加入背景钟律的空间变化。

## 假设 126.1　局部非均匀响应

取中心节点 \(x_0\)，平均区域为

$$
Q_L=B_L(x_0).
$$

定义单点均值

$$
r_x(m,v)=\operatorname{Tr}[\sigma_mR_x(v)].
$$

假设在所研究区域和方向上，

$$
\boxed{
|r_x(m,v)-r_{x_0}(m,v)|
\le
\kappa\,d_G(x,x_0).
}
\tag{126.1}
$$

\(\kappa\) 是当前标定下的空间变化上界，不是表面引力。

---

## 定理 126.1　涨落误差与空间平均偏差的联合界

令

$$
n_0(m,v)=\sqrt{r_{x_0}(m,v)}.
$$

则

$$
\boxed{
\begin{aligned}
&\left\|
\bigl(\sqrt{\widehat R_{Q_L}(v)}-n_0(m,v)I\bigr)
\sigma_m^{1/2}
\right\|_2\\
&\quad\le
\frac1{2n_*}
\sqrt{
\Delta_R^2\frac{b_{Q_L}(m)}{N_{Q_L}}
+
\kappa^2L^2
}.
\end{aligned}
}
\tag{126.2}
$$

因此也有较简单的上界：

$$
\boxed{
\text{局部钟律误差}
\le
\frac{\Delta_R}{2n_*}
\sqrt{\frac{b_{Q_L}(m)}{N_{Q_L}}}
+
\frac{\kappa L}{2n_*}.
}
\tag{126.3}
$$

### 证明

记 \(r_Q=\operatorname{Tr}(\sigma_m\widehat R_Q)\)。则

$$
\operatorname{Tr}
\left[
\sigma_m(\widehat R_Q-r_{x_0}I)^2
\right]
=
\operatorname{Var}(\widehat R_Q)
+
(r_Q-r_{x_0})^2.
$$

由假设，

$$
|r_Q-r_{x_0}|\le\kappa L.
$$

再使用平方根因式分解及定理 124.1，得到式（126.2）；最后用 \(\sqrt{a^2+b^2}\le a+b\)。∎

---

## 定理 126.2　最优粗粒化尺度

进一步假设，在指定尺度范围内，

$$
N_{Q_L}\ge c_-L^D,
$$

并记

$$
\xi_m=1+2r_0m.
$$

则式（126.3）具有形式

$$
E(L)\le A_mL^{-D/2}+BL,
\tag{126.4}
$$

其中

$$
A_m=
\frac{\Delta_R}{2n_*}
\sqrt{\frac{c_+}{c_-}}\,
\xi_m^{D/2},
\qquad
B=\frac{\kappa}{2n_*}.
$$

若 \(A_m,B>0\)，连续尺度上的最优点为

$$
\boxed{
L_*=
\left(\frac{DA_m}{2B}\right)^{2/(D+2)}.
}
\tag{126.5}
$$

最小上界为

$$
\boxed{
E_*
=
\frac{D+2}{2}
A_m^{2/(D+2)}
\left(\frac{2B}{D}\right)^{D/(D+2)}.
}
\tag{126.6}
$$

### 证明

对 \(A_mL^{-D/2}+BL\) 求导，解驻点方程。二阶导数为正，故为唯一极小点。∎

图半径为整数时，可以选择相邻整数；实际最优点还必须处于所假设的尺度范围内。

定义背景变化尺度

$$
L_{\mathrm{geom}}=\frac{\Delta_R}{\kappa},
$$

则忽略已经明确给出的常数后，

$$
\boxed{
L_*
\sim
\xi_m^{D/(D+2)}
L_{\mathrm{geom}}^{2/(D+2)},
}
\tag{126.7}
$$

以及

$$
\boxed{
E_*
\sim
\frac{\Delta_R}{n_*}
\left(
\frac{\xi_m}{L_{\mathrm{geom}}}
\right)^{D/(D+2)}.
}
\tag{126.8}
$$

### 核心解释

一个良好的局部经典描述通常需要尺度分离：

$$
\boxed{
\xi_m\ll L\ll L_{\mathrm{geom}}.
}
\tag{126.9}
$$

左侧要求平均区域包含许多近乎独立的影响域。

右侧要求平均区域内的背景仍然足够相似。

**经典时空不是“平均得越多越好”，而是存在一个同时压低涨落与非均匀偏差的有效窗口。**

这仍然是误差证书的最优尺度，不是已经推导出的普遍最小长度。

---

# 127．宏观平均不能作为瞬时的局域操作

现在补上集体算子的物理可实现性。

## 假设 127.1　局域读取装置

观察者的最终输出寄存器位于节点 \(o\)。整个实现使用第 121 节的局域门，深度为 \(m\)。

记其输入因果域为

$$
Z=B_{mr_0}(o).
$$

取一个平均区域 \(Q\)，其中有

$$
k=|Q\setminus Z|>0
$$

个节点位于该因果域之外。

每个结构节点是量子比特，定义

$$
R_x=I+|1\rangle\langle1|_x.
$$

希望实现的目标是让观察者探针经历

$$
\boxed{
U_{\mathrm{target}}
=
\exp\left[
-i\alpha\,|1\rangle\langle1|_O
\otimes\sqrt{\frac1{|Q|}\sum_{x\in Q}R_x}
\right].
}
\tag{127.1}
$$

---

## 定理 127.1　有限深度局域实现的误差下界

对全部输入都工作的局域实现，其最坏输出迹距离误差至少为

$$
\boxed{
\varepsilon_{\mathrm{impl}}
\ge
\frac12
\left|
\sin\left[
\frac\alpha2
\left(
\sqrt{1+\frac{k}{|Q|}}-1
\right)
\right]
\right|.
}
\tag{127.2}
$$

只要右侧非零，就不存在该深度下的精确实现。

### 证明

取两种结构输入：

第一种在 \(Q\) 上全部为 \(|0\rangle\)。

第二种仅在 \(Q\setminus Z\) 上为 \(|1\rangle\)，其余与第一种相同。

二者在观察者的全部输入因果域 \(Z\) 上完全相同。因此，由定理 122.1，任意深度 \(m\) 的局域实现必须给出相同观察者输出。

但对探针初态 \(|+\rangle\)，目标操作分别产生相位

$$
\alpha,\qquad
\alpha\sqrt{1+k/|Q|}.
$$

两个目标纯态的迹距离为

$$
D_{\mathrm{target}}
=
\left|
\sin\left[
\frac\alpha2
\left(
\sqrt{1+\frac{k}{|Q|}}-1
\right)
\right]
\right|.
$$

同一个实际输出不能同时以小于 \(D_{\mathrm{target}}/2\) 的误差逼近两个目标态。由三角不等式得到式（127.2）。∎

### 结论

$$
\boxed{
\text{集体算子在数学上定义良好}
\not\Rightarrow
\text{点状观察者能在任意短时间内调用它}.
}
$$

若平均区域半径为 \(L\)，要让任意远端输入都可能影响中心输出，至少需要相应的因果深度。

可以使用分布式观察者、提前建立的记录、并行局部测量或明确的汇总网络，但这些都是额外物理资源，不能从“宏观极限”一词中自动获得。

因此，第 125 节的完整误差账本应写为

$$
\boxed{
\varepsilon_{\mathrm{total}}
\le
\varepsilon_{\mathrm{impl}}
+
\varepsilon_{\mathrm{classical}}
+
\varepsilon_{\mathrm{readout}}.
}
\tag{127.3}
$$

其中每一项对应不同的证明任务。

---

# 128．连续时间推广：严格因果域变成可控的近局域尾部

有限电路给出严格支持。对连续时间的局域 Hamiltonian，

$$
H=\sum_Zh_Z,
$$

一般不能直接声称有限时间内远处作用严格为零。

在有限程或适当快速衰减的相互作用条件下，可以使用 Lieb–Robinson 型近局域估计。局部观测量的近似支持与传播界已有系统框架。([arXiv][2])

## 假设 128.1　已认证的近局域估计

对单点算子 \(A_x\)，假设存在支持于 \(B_\ell(x)\) 的近似算子 \(A_x^{(\ell)}(t)\)，满足

$$
\|A_x^{(\ell)}(t)\|\le\|A_x\|,
$$

以及

$$
\boxed{
\|\alpha_t(A_x)-A_x^{(\ell)}(t)\|
\le
C_0\|A_x\|e^{-\mu(\ell-v_{\mathrm{LR}}|t|)}.
}
\tag{128.1}
$$

其中

$$
\alpha_t(A)=e^{itH/\hbar}Ae^{-itH/\hbar}.
$$

式（128.1）在形式化中应作为已经证明或明确导入的定理，而不能只在文中标注“由局域性显然”。

---

## 定理 128.1　连续时间的关联体积界

设初态仍为乘积态，图球具有

$$
|B_r(x)|\le c_+(1+r)^D,
$$

且局部读数具有第 123 节的谱界。

则存在仅依赖于上述局域常数与图增长常数的 \(C_1\)，使

$$
\boxed{
\sum_{y\in Q}
|\operatorname{Cov}_{\sigma(t)}(R_x,R_y)|
\le
C_1\Delta_R^2(1+v_{\mathrm{LR}}|t|)^D.
}
\tag{128.2}
$$

因此

$$
\boxed{
\operatorname{Var}_{\sigma(t)}(\widehat R_Q)
\le
\frac{
C_1\Delta_R^2(1+v_{\mathrm{LR}}|t|)^D
}{
|Q|
}.
}
\tag{128.3}
$$

### 证明概要

先把 \(R_x,R_y\) 减去共同谱区间中点，使其范数不超过 \(\Delta_R\)，而协方差不变。

当 \(x,y\) 相距 \(L\) 时，选取

$$
\ell<\frac L2.
$$

两近似算子支持不相交，其在初始乘积态中的协方差为零。

实际协方差与近似协方差之差，可由式（128.1）及三角不等式控制。因此得到形如

$$
|\operatorname{Cov}(R_x,R_y)|
\le
\Delta_R^2
\min\left\{
1,\,
C_2e^{-\mu'(L-2v_{\mathrm{LR}}|t|)}
\right\}.
$$

在近区使用图球体积界，在远区按距离壳层求和。指数衰减压过多项式增长，得到式（128.2）。

再对 \(x\in Q\) 求和并除以 \(|Q|^2\)，得到式（128.3）。∎

### 限定

\(v_{\mathrm{LR}}\) 是由所选相互作用得到的传播上界，不是已经识别为现实光速的普适常数。

而且，误差界中的关联尺度增长只是最坏情形控制，并不证明实际关联必然按同样速度增长。

---

# 129．从钟过程收敛到曲率收敛，还缺少正则性

上一轮已经区分单点度量与曲率。本轮可以给出一个更强的反例：

> **即使一个完整区域内的钟读数一致接近，曲率仍可能发散。**

曲率依赖度量的导数，而不只是度量值；Levi–Civita 连接及曲率的这种微分结构是标准几何定义的一部分。([David Tong][3])

## 定义 129.1　一族相同光锥的度量

在固定无量纲局部坐标中，取

$$
\eta=-dt^2+dx^2,
$$

以及

$$
\boxed{
g_\epsilon=e^{2s_\epsilon(x)}\eta,
\qquad
s_\epsilon(x)=\epsilon^2\cos(x/\epsilon^2),
\quad 0<\epsilon\le1.
}
\tag{129.1}
$$

---

## 定理 129.1　钟律一致接近不保证曲率有界

有：

$$
\boxed{
g_\epsilon\longrightarrow\eta
\quad\text{一致收敛}.
}
\tag{129.2}
$$

所有 \(g_\epsilon\) 都具有与 \(\eta\) 相同的 null 方向。

对固定受控轨迹、\(|v|\le v_{\max}<1\)，其钟速满足

$$
n_\epsilon(x,v)
=
e^{s_\epsilon(x)}\sqrt{1-v^2},
$$

所以

$$
\boxed{
|n_\epsilon-n_0|
\le e^{\epsilon^2}-1
=
O(\epsilon^2)
}
\tag{129.3}
$$

一致成立。

但是，采用前文曲率符号约定，

$$
\boxed{
\operatorname{Scal}(g_\epsilon)\big|_{x=0}
=
\frac{2e^{-2\epsilon^2}}{\epsilon^2}
\longrightarrow+\infty.
}
\tag{129.4}
$$

### 证明

因为 \(|s_\epsilon|\le\epsilon^2\)，度量系数一致趋于 \(\eta\)，钟速估计也直接成立。

正共形因子不改变 null 方向。

二维静态共形度量的标量曲率为

$$
\operatorname{Scal}(g)
=
-2e^{-2s(x)}s''(x).
$$

而

$$
s_\epsilon''(x)
=
-\epsilon^{-2}\cos(x/\epsilon^2).
$$

在 \(x=0\) 代入即得。∎

### 操作性含义

对只读取受控轨迹上内部相位、且总作用预算固定的钟实验，式（129.3）给出趋零的过程误差。

但这不包括潮汐测量、自由轨迹偏离、保持轨迹所需的力，或其他对导数敏感的协议。

因此：

$$
\boxed{
\text{某个实验族上的操作接近}
\not\Rightarrow
\text{全部几何目标同时接近}.
}
$$

---

## 定理 129.2　曲率收敛的一个充分条件

在共同坐标域上，若

$$
g_n\to g
$$

以 \(C^2\) 范数一致收敛，并且度量及其逆保持一致有界、非退化，则

$$
\boxed{
R(g_n)\to R(g)
}
\tag{129.5}
$$

在相应张量分量上以 \(C^0\) 范数一致收敛。

### 证明

连接系数由 \(g^{-1}\partial g\) 构成；曲率由其一阶导数和连接二次项构成。

在一致非退化性下，矩阵求逆连续。因而 \(g_n,\partial g_n,\partial^2g_n\) 的一致收敛，逐项推出连接及曲率表达式收敛。∎

### 结论

从宏观量子钟律走向引力方程，必须保留至少三类目标：

$$
\boxed{
\text{度量值的控制},
\qquad
\text{一阶输运的控制},
\qquad
\text{二阶曲率的控制}.
}
$$

不能只证明一个平均钟通道趋于经典，就宣布几何动力学已经完整收敛。

---

# 130．局域时空有效性的完整条件

## 定理 130.1　局域宏观钟律的条件性有效窗口

在第 121—126 节的有限模型中，假设：

* 初始结构为乘积态，或具有另行认证的关联界；
* 实际动力学具有给定的局域支持证书；
* 平方钟速算子具有一致正下界；
* 平均区域的节点数与图球体积满足指定增长条件；
* 区域内平均钟律的空间变化受 \(\kappa\) 控制；
* 实际集体作用与最终读取具有独立的实现误差证书。

则指定有限实验的误差可由以下三部分控制：

$$
\boxed{
\begin{aligned}
\varepsilon_{\mathrm{total}}
\ \le\;&
\varepsilon_{\mathrm{impl}}
+\varepsilon_{\mathrm{readout}}\\
&+
\mathcal B\,
\frac1{2n_*}
\left[
\Delta_R
\sqrt{\frac{c_+}{c_-}}
\left(\frac{\xi}{L}\right)^{D/2}
+\kappa L
\right],
\end{aligned}
}
\tag{130.1}
$$

其中 \(\mathcal B\) 是相应无量纲作用预算，\(\xi\) 是由实际动力学证书控制的关联影响尺度。

### 证明

由定理 126.1 得到每次局部钟律残差；采用定理 125.1 的联合过程望远镜展开，将残差乘以相应作用预算求和。

再用通道距离三角不等式加入物理实现与最终读取误差。∎

### 该定理没有省略的物理任务

它证明的是：在这些条件下，完整过程可以被某个局部经典钟律逼近。

要把这个钟律识别为现实的时空，还必须继续满足此前已经列出的：

$$
\text{平方钟速的二次结构与 Lorentz 符号},
$$

$$
\text{跨观察者标定的一致性},
$$

$$
\text{共同信号传播},
$$

$$
\text{足够的空间正则性与反作用条件}.
$$

---

## 与项目形式化的直接衔接

本次读取固定于提交：

```text
907430bb0f8ca2f94d1c0cb47ace034e388af9ca
```

本轮最适合形式化的证明依赖不是一个庞大的总定理，而是以下有限链：

| 结构     | 需要保存的证明           |
| ------ | ----------------- |
| 局域电路   | 每个门的支持、同层不相交与支持扩张 |
| 有限因果接口 | 输出读数沿输入过去域精确下降    |
| 关联传播   | 乘积初态在不相交过去域上的因子化  |
| 宏观读数   | 协方差计数、方差界与平方根残差   |
| 过程近似   | 共享结构下的联合酉误差组合     |
| 物理读取   | 因果域之外输入的不可区分见证    |
| 几何提升   | 二次钟律、正则性与导数误差     |

其中，第二项直接连接项目的 `exact_descent_has_no_carry`；最后的误差组合继续使用项目所强调的精确、条件良好与可实现三层区分。

本轮没有执行 Lean 编译。已核对的有限算例包括四量子比特局域电路中逐步增长的平均读数方差、粗粒化最优点以及式（129.4）的曲率表达式；这些核验不替代一般形式化证明。

---

# 结论

这一轮把上一轮的宏观经典化条件向前推进了三步。

**第一，关联界不再只能作为输入。**在局域电路与初始乘积条件下，它可以从有限因果支持直接证明：

$$
\boxed{
\text{局域交互}
\longrightarrow
\text{过去域重叠}
\longrightarrow
\text{协方差增长界}.
}
$$

**第二，经典描述出现于一个尺度窗口，而不是无限平均。**

$$
\boxed{
\text{关联影响尺度}
\ll
\text{平均尺度}
\ll
\text{背景变化尺度}.
}
$$

**第三，得到这个平均本身也必须满足因果与资源限制。**一个局域观察者不能因为数学上写出了 \(\widehat R_Q\)，就被赋予对整个区域的瞬时访问。

最后，曲率反例说明：即使经典钟过程已经得到很好的近似，通向引力仍需额外的导数控制。

因此，当前理论可以进一步收紧为：

> **物理时空不是一个对量子世界任意平均后得到的背景，而是局域交互、关联传播、有限观察资源和空间正则性共同允许的一种尺度相关描述。**

其核心对象不再只是

$$
g_{\mu\nu}(x),
$$

而是一个带证书的实现：

$$
\boxed{
\left(
g_{\mu\nu},
\ \text{适用区域},
\ \text{适用时间},
\ \text{允许实验},
\ \text{误差界},
\ \text{导数控制}
\right).
}
$$

**只有这些内容共同成立，“由量子观察者导出时空”才不仅是构造出一个形式正确的度量，而是证明一个有限观察者确实能够在自己的因果与资源范围内，稳定地使用这张时空。**

[1]: https://arxiv.org/html/quant-ph/0603121v1 "Lieb-Robinson bounds and the generation of correlationsand topological quantum order"
[2]: https://arxiv.org/abs/1810.02428 "[1810.02428] Quasi-Locality Bounds for Quantum Lattice Systems. Part I. Lieb-Robinson Bounds, Quasi-Local Maps, and Spectral Flow Automorphisms"
[3]: https://davidtong.org/teaching/general-relativity/grhtml/S3.html "3 Introducing Riemannian Geometry‣ General Relativity by David Tong"
# 曲率的有限观测证书与非线性引力余量

## ——量子观察者—关系时空理论第一百三十一至第一百四十节增订

### 摘要

前文已经证明：在局域性、关联控制与有限实验预算等条件下，量子观察者可以使用一个近似经典的钟律，并由平方钟速重建候选洛伦兹度量。

但还存在两层不同的问题：

$$
\boxed{
\text{钟读数接近}
\quad\text{是否足以保证}\quad
\text{曲率接近？}
}
$$

以及：

$$
\boxed{
\text{微观几何被平均后，}
\quad
\text{其动力学是否仍由同一个场方程描述？}
}
$$

本增订分别处理它们。

首先，从带关联误差的量子实验记录出发，构造有限的导数重建证书，给出度量二阶数据及曲率的误差界。

其次，构造一族**严格满足真空 Einstein 方程的短波几何**，证明它们虽然一致收敛于一个平滑度量，但极限度量具有非零的有效辐射应力。这说明：

> **某些结构可以在有限分辨率的钟读数中消失，却仍通过非线性关系影响宏观动力学。**

后一现象属于引力短波反作用的既有研究方向。这里给出一个可逐项检查的具体构造，并明确说明它如何进入项目的“观察接口—目标残差—动力下降”结构，而不是把已有现象重新宣称为未经核实的新发现。([APS Journals][1])

---

# 131．将曲率重建分解为有限实验任务

## 假设 131.1　局部几何候选与测量记录

设前文的过程级经典性条件已经在指定实验范围内成立，并得到局部坐标域

$$
U\subset\mathbb R^d.
$$

当采样覆盖整个时空邻域时，\(d=4\)；若额外假设几何静态，只采样空间坐标，则可以取 \(d=3\)。

这里使用的欧氏坐标范数仅用于描述采样布局和误差，不是预先假定物理时空为欧氏空间。

对一个待重建的度量系数，记

$$
f(x)=g_{\mu\nu}(x).
$$

在采样点 \(x_1,\ldots,x_N\)，实际实验产生实随机记录

$$
Y_1,\ldots,Y_N.
$$

它们可以由前文的多方向钟测量经过线性重建得到，但必须已经具有以下统计证书：

$$
\boxed{
\mathbb E[Y_j]=f(x_j)+b_j,
\qquad |b_j|\le\beta,
}
\tag{131.1}
$$

以及

$$
\boxed{
\max_i\sum_j
\left|\operatorname{Cov}(Y_i,Y_j)\right|
\le\Gamma.
}
\tag{131.2}
$$

其中：

* \(\beta\) 控制系统性偏差，包括近似钟律、控制与估计器偏差；
* \(\Gamma\) 控制随机误差及不同记录之间的关联。

这些条件不要求同时无扰测量所有不对易量。不同设置可以由不同的、已说明制备过程实现；最终记录及其关联必须由实际协议确定。

## 命题 131.1　过程误差可以转化为读数偏差

若一个记录的取值满足

$$
|Y|\le M,
$$

且实际与理想记录分布的总变差距离至多为 \(\varepsilon\)，则

$$
\boxed{
|\mathbb E_{\mathrm{actual}}Y
-\mathbb E_{\mathrm{ideal}}Y|
\le2M\varepsilon.
}
\tag{131.3}
$$

### 证明

将两种概率测度之差记为 \(\delta P\)，则

$$
\left|\int Y\,d\delta P\right|
\le
M\int|d\delta P|
=
2M\,\operatorname{TV}(P_{\mathrm{actual}},P_{\mathrm{ideal}}).
$$

∎

因此，前文的过程误差不能在进入几何重建时被丢弃，而应进入 \(\beta\)。

**量子过程近似、统计估计与几何反演，必须沿同一条误差链连接。**

---

# 132．带有限矩阵证书的导数重建

数值微分会放大读数误差，因此“数据很接近”不能直接替换为“导数很接近”。稳定微分需要正则性条件与明确的离散设计。([arXiv][2])

## 定义 132.1　归一化采样设计

固定目标点 \(p\) 和采样半径 \(h>0\)，写成

$$
x_j=p+hz_j,
\qquad \|z_j\|\le1.
$$

令

$$
\mathcal B_3=\{\beta\in\mathbb N^d:|\beta|\le3\}.
$$

定义有限单项式向量

$$
v(z)=(z^\beta)_{\beta\in\mathcal B_3},
$$

以及归一化 Gram 矩阵

$$
\boxed{
G_h=\frac1N\sum_{j=1}^Nv(z_j)v(z_j)^{\mathsf T}.
}
\tag{132.1}
$$

要求存在已认证的 \(\gamma>0\)，使

$$
\boxed{G_h\ge\gamma I.}
\tag{132.2}
$$

这是一项有限矩阵条件。它防止采样点全部落在无法区分某些多项式方向的退化布局中。

## 定义 132.2　导数权重

对多重指标 \(\alpha\)，其中 \(|\alpha|\le2\)，定义

$$
\boxed{
w_j^{(\alpha)}
=
\frac{\alpha!}{Nh^{|\alpha|}}
e_\alpha^{\mathsf T}G_h^{-1}v(z_j).
}
\tag{132.3}
$$

导数估计器为

$$
\boxed{
\widehat{\partial^\alpha f}(p)
=
\sum_jw_j^{(\alpha)}Y_j.
}
\tag{132.4}
$$

---

## 定理 132.1　多项式精确性与权重范数

对任何次数不超过三的多项式 \(P\)，

$$
\boxed{
\sum_jw_j^{(\alpha)}P(x_j)
=
\partial^\alpha P(p).
}
\tag{132.5}
$$

同时，

$$
\boxed{
\sum_j|w_j^{(\alpha)}|^2
=
\frac{(\alpha!)^2}{Nh^{2|\alpha|}}
e_\alpha^{\mathsf T}G_h^{-1}e_\alpha
\le
\frac{(\alpha!)^2}
{N\gamma h^{2|\alpha|}},
}
\tag{132.6}
$$

以及

$$
\boxed{
\sum_j|w_j^{(\alpha)}|
\le
\frac{\alpha!}{\sqrt\gamma\,h^{|\alpha|}}.
}
\tag{132.7}
$$

### 证明

把 \(P(p+hz)\) 展开为

$$
P(p+hz)=\sum_{\beta\in\mathcal B_3}a_\beta z^\beta.
$$

则

$$
\partial^\alpha P(p)=\alpha!h^{-|\alpha|}a_\alpha.
$$

由 \(G_h\) 的定义，

$$
\frac1N\sum_jG_h^{-1}v(z_j)v(z_j)^{\mathsf T}=I.
$$

代入权重即可得到式（132.5）。

权重平方和由同一 Gram 恒等式直接得到；再用 \(G_h^{-1}\le\gamma^{-1}I\)，得到式（132.6）。

最后应用

$$
\|w\|_1\le\sqrt N\,\|w\|_2.
$$

∎

### 有限实例

在一维中，取采样点

$$
-h,\quad-\frac h2,\quad0,\quad\frac h2,\quad h.
$$

上述构造给出

$$
\boxed{
\widehat{f''}(0)
=
\frac{
8Y_{-h}-4Y_{-h/2}-8Y_0-4Y_{h/2}+8Y_h
}{7h^2}.
}
\tag{132.8}
$$

它对全部三次以下多项式精确成立。

这些权重允许出现负数：它们是估计器系数，不是量子态概率。

---

# 133．量子记录的相关性怎样进入二阶导数误差？

## 假设 133.1　局部正则性

设

$$
f\in C^4(B_h(p)),
$$

并存在 \(M_4\ge0\)，使其四阶 Fréchet 导数满足

$$
\|D^4f(x)\|_{\mathrm{op}}\le M_4.
$$

## 定理 133.1　导数重建的偏差与方差

令 \(k=|\alpha|\le2\)。则

$$
\boxed{
\left|
\mathbb E[\widehat{\partial^\alpha f}]
-\partial^\alpha f(p)
\right|
\le
\frac{\alpha!}{\sqrt\gamma}
\left(
\frac{\beta}{h^k}
+
\frac{M_4}{24}h^{4-k}
\right),
}
\tag{133.1}
$$

并且

$$
\boxed{
\operatorname{Var}
\bigl(\widehat{\partial^\alpha f}\bigr)
\le
\frac{
\Gamma(\alpha!)^2
}{
N\gamma h^{2k}
}.
}
\tag{133.2}
$$

### 证明

在 \(p\) 处取三阶 Taylor 多项式 \(P_3\)。余项满足

$$
|f(x_j)-P_3(x_j)|
\le
\frac{M_4h^4}{24}.
$$

由定理 132.1，多项式部分被精确重建，因此总偏差不超过

$$
\sum_j|w_j^{(\alpha)}|
\left(
\beta+\frac{M_4h^4}{24}
\right).
$$

应用式（132.7），得到式（133.1）。

设协方差矩阵为 \(\Sigma\)。则

$$
\operatorname{Var}\left(\sum_jw_jY_j\right)
=
w^{\mathsf T}\Sigma w.
$$

利用

$$
2|w_iw_j|\le w_i^2+w_j^2
$$

和式（131.2），有

$$
w^{\mathsf T}\Sigma w
\le
\Gamma\sum_jw_j^2.
$$

再代入式（132.6）。∎

---

## 推论 133.1　二阶导数具有额外的分辨代价

对 \(k=2\)，均方根误差可界为

$$
\boxed{
\operatorname{RMSE}(\widehat{\partial^\alpha f})
\le
\frac{\alpha!}{\sqrt\gamma}
\left[
\frac{\beta}{h^2}
+
\frac1{h^2}\sqrt{\frac{\Gamma}{N}}
+
\frac{M_4h^2}{24}
\right].
}
\tag{133.3}
$$

这显示三种性质不同的误差：

$$
\text{系统偏差放大：}\quad \beta h^{-2};
$$

$$
\text{随机误差放大：}\quad
\sqrt{\Gamma/N}\,h^{-2};
$$

$$
\text{局部展开误差：}\quad M_4h^2.
$$

**缩小采样邻域会减小最后一项，却放大前两项。**

---

## 推论 133.2　有限置信证书

若同时估计有限个 \(J\) 项，并希望总失败概率不超过 \(\eta>0\)，则对每项可以采用

$$
\boxed{
\text{误差半径}
=
\text{偏差上界}
+
\sqrt{\frac J\eta}\,
\text{标准差上界}.
}
\tag{133.4}
$$

由 Chebyshev 不等式与并集界，所有估计同时落在其误差区间内的概率至少为 \(1-\eta\)。

这没有把概率保证改写成逻辑上的绝对正确性；它是关于完整实验程序的一个可证明性质。

---

# 134．从度量的二阶数据到曲率证书

## 定义 134.1　局部二阶几何数据

记

$$
J^2_pg
=
\bigl(
g_{\mu\nu}(p),
\partial_\alpha g_{\mu\nu}(p),
\partial_\alpha\partial_\beta g_{\mu\nu}(p)
\bigr).
$$

这组数据通常称为度量在 \(p\) 处的二阶 jet。它不是另一个物理实体，而是计算连接和曲率所需的有限导数集合。

Riemann 曲率在给定坐标中由这些数据及 \(g^{-1}\) 的代数组合确定。([剑桥大学应用与计算数学系][3])

---

## 定理 134.1　非退化区域中的曲率稳定性

设 \(g,\widetilde g\) 为同一坐标域上的 \(C^2\) Lorentz 度量，并具有共同界

$$
\|g^{-1}\|,\|\widetilde g^{-1}\|\le L,
$$

$$
\|\partial g\|,\|\partial\widetilde g\|\le B_1,
$$

$$
\|\partial^2g\|,\|\partial^2\widetilde g\|\le B_2.
$$

定义

$$
\delta_k
=
\|\partial^k\widetilde g-\partial^kg\|,
\qquad k=0,1,2.
$$

则存在仅依赖维数与所选分量范数的常数 \(C_d\)，使混合指标曲率满足

$$
\boxed{
\begin{aligned}
\|R(\widetilde g)-R(g)\|
\le C_d\bigl[
&L\delta_2
+
L^2B_1\delta_1\\
&+
(L^2B_2+L^3B_1^2)\delta_0
\bigr].
\end{aligned}
}
\tag{134.1}
$$

### 证明

首先，由逆矩阵恒等式，

$$
\widetilde g^{-1}-g^{-1}
=
\widetilde g^{-1}(g-\widetilde g)g^{-1},
$$

故

$$
\|\widetilde g^{-1}-g^{-1}\|
\le L^2\delta_0.
$$

连接系数由 \(g^{-1}\partial g\) 的有限线性组合构成。

曲率展开后仅包含以下两类项：

$$
g^{-1}\partial^2g,
$$

$$
g^{-1}g^{-1}(\partial g)(\partial g).
$$

对每个乘积逐因子相减。第一类差异受

$$
L\delta_2+L^2B_2\delta_0
$$

控制；第二类差异受

$$
C_d\left(
L^2B_1\delta_1+L^3B_1^2\delta_0
\right)
$$

控制。合并即得。∎

### 非退化性不能省略

若 \(g^{-1}\) 的范数无界，微小系数误差也可能导致巨大曲率误差。

因此，有限重建证书必须同时检查：

$$
\boxed{
\text{系数误差}
+
\text{一阶误差}
+
\text{二阶误差}
+
\text{非退化裕量}.
}
$$

用钟网络测量曲率已有具体“钟罗盘”方案；本节强调的是从有限读数到曲率之间必须携带的稳定性条件。([arXiv][4])

---

# 135．曲率比钟速需要更强的尺度分离

将前文的局域关联证书代入本节的导数估计。

假设在所讨论采样窗口内：

$$
\Gamma\le\frac{\Delta^2b_*}{R},
$$

其中 \(R\) 是经过独立性认证的完整重复次数，\(b_*\) 是记录之间的关联计数上界。

若重复实验没有相应独立性或新的协方差证书，就不能自动除以 \(R\)。

再假设采样数满足

$$
N_h\ge c_0(h/a)^d,
$$

其中 \(a\) 是坐标采样间隔。

暂取系统偏差 \(\beta=0\)，并要求 Gram 条件数、度量逆矩阵界与相关正则性常数在尺度窗口内一致受控。

## 定理 135.1　曲率误差的尺度结构

在上述条件下，可获得形如

$$
\boxed{
E_{\mathrm{curv}}(h)
\le
A\,h^{-(d/2+2)}
+
B\,h^2
}
\tag{135.1}
$$

的曲率误差证书，其中

$$
A
\propto
\Delta
\sqrt{\frac{b_*}{R}}\,
a^{d/2}.
$$

\(B\) 取决于四阶正则性及定理 134.1 的非线性稳定常数。

### 证明

由式（133.3），二阶随机误差为

$$
h^{-2}\sqrt{\Gamma/N_h}
\le
\frac{\Delta}{\sqrt{c_0}}
\sqrt{\frac{b_*}{R}}\,
a^{d/2}h^{-(d/2+2)}.
$$

Taylor 二阶误差为 \(O(h^2)\)。

在固定小尺度窗口内，零阶和一阶误差不比相应二阶控制更差；代入定理 134.1，并吸收固定常数即可。∎

---

## 定理 135.2　最优认证半径

若 \(A,B>0\)，式（135.1）的连续最优半径为

$$
\boxed{
h_*=
\left(
\frac{(d+4)A}{4B}
\right)^{2/(d+8)}.
}
\tag{135.2}
$$

其最小上界为

$$
\boxed{
E_*
=
\frac{d+8}{d+4}
B
\left(
\frac{(d+4)A}{4B}
\right)^{4/(d+8)}.
}
\tag{135.3}
$$

### 证明

对

$$
Ah^{-p}+Bh^2,
\qquad p=\frac{d+4}{2},
$$

求导，解

$$
ph^{-p-1}A=2Bh.
$$

代回目标函数即可。∎

### 一个重要推论

当其他条件固定而 \(A\propto R^{-1/2}\) 时，

$$
\boxed{
E_*\propto R^{-2/(d+8)}.
}
\tag{135.4}
$$

例如，完整四坐标采样中 \(d=4\)，该上界按 \(R^{-1/6}\) 缩小，而不是简单按 \(R^{-1/2}\) 缩小。

这是**当前估计器与当前误差界的尺度关系**，不是所有量子曲率测量的普遍最优极限。

同时：

* 若 \(h_*\) 小于实际采样间隔，必须重新选择可实现半径；
* 若 \(h_*\) 超出正则性或局域模型窗口，公式不能继续使用；
* 若 \(\beta\ne0\)，还要保留 \(\beta/h^2\)，增加样本数不能消除它；
* 采样与汇总仍受前文的因果传播限制，不能瞬时收集整个邻域。

**因此，曲率的可认证性比局部钟律的可使用性更强。**

---

# 136．为什么“先平均，再算引力”可能改变答案？

现在进入一个更深的问题：即使已经获得平滑宏观度量，也不能默认其动力学只是原动力学的直接平均。

用

$$
\mathscr G[g]
=
\operatorname{Ric}(g)
-\frac12\operatorname{Scal}(g)\,g
$$

表示 Einstein 张量。

## 定义 136.1　非线性下降缺陷

在同一个流形、同一组比较映射和标定中，设

$$
g_\varepsilon\to g_0
$$

一致收敛，并假设 \(\mathscr G[g_\varepsilon]\) 存在弱极限。

定义

$$
\boxed{
\mathfrak B
=
\mathscr G[g_0]
-
\operatorname*{wlim}_{\varepsilon\to0}
\mathscr G[g_\varepsilon].
}
\tag{136.1}
$$

这里的弱极限表示：对任意光滑紧支撑测试张量，相应积分收敛。

\(\mathfrak B\) 衡量以下两种操作的不交换：

$$
\text{先形成宏观度量，再计算 Einstein 张量};
$$

$$
\text{先计算每个微观几何的 Einstein 张量，再取宏观极限}.
$$

## 定理 136.1　强二阶控制消除该缺陷

若

$$
g_\varepsilon\to g_0
\quad\text{在 }C^2\text{ 中一致收敛},
$$

且逆度量一致有界，则

$$
\boxed{\mathfrak B=0.}
\tag{136.2}
$$

### 证明

定理 134.1 保证曲率一致收敛，相关代数收缩也连续，因此 Einstein 张量一致收敛。其弱极限必为 \(\mathscr G[g_0]\)。∎

反过来，只有 \(C^0\) 收敛时，该缺陷可以非零。短波引力反作用理论正是严格处理这类非线性极限，而不允许任意指定一个“有效额外物质”。([arXiv][5])

下面给出一个满足真空场方程的具体实例。

---

# 137．精确真空短波模型

本节开始使用经典广义相对论作为已经选定的几何动力学实现。

**因此，本节不是从量子观察者的定义首次推出 Einstein 方程；它检验的是：即使微观几何已经满足该方程，观察者的宏观压缩怎样改变有效源项。**

## 定义 137.1　平面波度量族

取常数 \(\Omega>0\)，定义

$$
p_\varepsilon(u)
=
\varepsilon\Omega\sin(u/\varepsilon).
$$

令 \(b_\varepsilon\) 是初值问题的解：

$$
\boxed{
b_\varepsilon''(u)
+
\Omega^2\cos^2(u/\varepsilon)b_\varepsilon(u)=0,
}
\tag{137.1}
$$

$$
b_\varepsilon(0)=1,
\qquad
b_\varepsilon'(0)=0.
$$

在

$$
|u|\le L<\frac{\pi}{2\Omega}
$$

内，定义

$$
\boxed{
ds_\varepsilon^2
=
-2\,du\,dv
+
b_\varepsilon(u)^2
\left[
e^{2p_\varepsilon(u)}dx^2
+
e^{-2p_\varepsilon(u)}dy^2
\right].
}
\tag{137.2}
$$

这是平面波的 Rosen 型坐标形式。此类坐标必须限制在尚未发生标架退化的区域；不能把其坐标焦散当作无条件的物理奇点。([arXiv][6])

---

## 定理 137.1　该度量族在共同区域内非退化

有

$$
\boxed{
\cos(\Omega u)\le b_\varepsilon(u)\le1
\qquad(0\le u\le L).
}
\tag{137.3}
$$

因此，在共同区域内

$$
b_\varepsilon(u)\ge\cos(\Omega L)>0.
$$

### 证明

在 \(b_\varepsilon\) 尚为正的区间上，

$$
b_\varepsilon''\le0,
$$

故 \(b_\varepsilon\le1\)。

改写方程为

$$
b_\varepsilon''+\Omega^2b_\varepsilon
=
\Omega^2\sin^2(u/\varepsilon)b_\varepsilon.
$$

由常系数方程的积分表示，

$$
b_\varepsilon(u)
=
\cos(\Omega u)
+
\Omega\int_0^u
\sin\bigl(\Omega(u-s)\bigr)
\sin^2(s/\varepsilon)b_\varepsilon(s)\,ds.
$$

在 \(0\le u\le L<\pi/(2\Omega)\) 上，若之前 \(b_\varepsilon\ge0\)，积分非负。

若存在首个零点 \(u_*\le L\)，则上式给出

$$
b_\varepsilon(u_*)\ge\cos(\Omega u_*)>0,
$$

矛盾。

负 \(u\) 部分由方程和初值的偶对称性得到。∎

---

## 定理 137.2　每个有限 \(\varepsilon\) 都严格满足真空方程

对式（137.2），只有 Ricci 分量 \(R_{uu}\) 可能非零，而且

$$
\boxed{
R_{uu}
=
-2\left[
\frac{b_\varepsilon''}{b_\varepsilon}
+
(p_\varepsilon')^2
\right].
}
\tag{137.4}
$$

因此

$$
\boxed{
\operatorname{Ric}(g_\varepsilon)=0,
\qquad
\mathscr G[g_\varepsilon]=0.
}
\tag{137.5}
$$

### 证明

对一般函数 \(b,p\)，令

$$
B=be^p,\qquad C=be^{-p}.
$$

度量为

$$
-2\,du\,dv+B(u)^2dx^2+C(u)^2dy^2.
$$

直接计算连接与 Ricci 张量，得到

$$
R_{uu}
=
-\frac{B''}{B}-\frac{C''}{C}
=
-2\left(\frac{b''}{b}+(p')^2\right),
$$

其余 Ricci 分量为零。

而

$$
p_\varepsilon'=\Omega\cos(u/\varepsilon).
$$

结合式（137.1），\(R_{uu}=0\)。∎

这里的真空结论不是近似成立，而是对每个 \(\varepsilon>0\) 精确成立。

---

# 138．平滑极限却具有正的有效辐射源

## 定理 138.1　共同宏观极限

定义

$$
\omega=\frac{\Omega}{\sqrt2},
\qquad
b_0(u)=\cos(\omega u).
$$

则在上述共同紧区间内，

$$
\boxed{
b_\varepsilon\to b_0
\quad\text{以 }C^1\text{ 范数收敛，误差为 }O(\varepsilon).
}
\tag{138.1}
$$

因此

$$
\boxed{
g_\varepsilon\to g_0
}
$$

一致收敛，其中

$$
\boxed{
ds_0^2
=
-2\,du\,dv
+
\cos^2\!\left(\frac{\Omega u}{\sqrt2}\right)
(dx^2+dy^2).
}
\tag{138.2}
$$

### 证明

使用

$$
\cos^2(u/\varepsilon)
=
\frac12+\frac12\cos(2u/\varepsilon).
$$

令 \(d_\varepsilon=b_\varepsilon-b_0\)，则

$$
d_\varepsilon''+\omega^2d_\varepsilon
=
-\frac{\Omega^2}{2}
\cos(2u/\varepsilon)b_\varepsilon,
$$

初值为零。

于是

$$
d_\varepsilon(u)
=
-\frac{\Omega^2}{2\omega}
\int_0^u
\sin\bigl(\omega(u-s)\bigr)
b_\varepsilon(s)\cos(2s/\varepsilon)\,ds.
$$

定理 137.1 给出 \(b_\varepsilon\) 一致有界；原方程还给出

$$
|b_\varepsilon'(u)|\le\Omega^2L.
$$

对振荡积分分部积分：

$$
\int_0^uf(s)\cos(2s/\varepsilon)\,ds
=
\frac{\varepsilon}{2}f(u)\sin(2u/\varepsilon)
-
\frac{\varepsilon}{2}
\int_0^uf'(s)\sin(2s/\varepsilon)\,ds.
$$

应用于 \(d_\varepsilon\) 及其一阶导数的积分表示，得到一致的 \(O(\varepsilon)\) 界。

又因 \(p_\varepsilon=O(\varepsilon)\)，故度量系数一致收敛。∎

---

## 定理 138.2　极限具有非零、正的 null 型有效源

对极限度量 \(g_0\)，

$$
\boxed{
\mathscr G[g_0]
=
\Omega^2\,du\otimes du.
}
\tag{138.3}
$$

而

$$
\operatorname{Scal}(g_0)=0.
$$

因此

$$
\boxed{
\mathfrak B
=
\Omega^2\,du\otimes du\ne0.
}
\tag{138.4}
$$

若使用引力耦合常数 \(\kappa_E=8\pi G/c^4\)，定义

$$
\boxed{
\tau_{\mathrm{eff}}
=
\frac{\Omega^2}{\kappa_E}
\,du\otimes du,
}
\tag{138.5}
$$

则它无迹，并满足弱能量条件。

### 证明

在极限中 \(p=0\)，由式（137.4），

$$
R_{uu}(g_0)
=
-2\frac{b_0''}{b_0}
=
\Omega^2.
$$

只有这一 Ricci 分量非零，而 \(g_0^{uu}=0\)，故标量曲率为零，Einstein 张量即式（138.3）。

对任意类时向量 \(V\)，

$$
\tau_{\mathrm{eff}}(V,V)
=
\frac{\Omega^2}{\kappa_E}[du(V)]^2
\ge0.
$$

无迹性来自 \(g_0^{-1}(du,du)=0\)。∎

### 两个重要结果

首先：

$$
\boxed{
\forall\varepsilon>0,\quad
\mathscr G[g_\varepsilon]=0,
}
$$

但

$$
\boxed{
\mathscr G[g_0]\ne0.
}
$$

其次，所有微观度量与极限度量的标量曲率都为零。因此，**只检查标量曲率，也不能判断一个几何是否真空。**

这里的有效源具有单向无质量辐射的应力形式。它不表示产生了热光子，也不是霍金辐射；它是被宏观描述舍弃的短波引力结构所留下的动力学贡献。

真空波的高频极限表现为有效辐射应力，是 Isaacson、Burnett 及后续严格反作用框架中的核心现象；本例给出了一个直接可算的局部实现。([APS Journals][1])

---

## 推论 138.1　固定钟相位协议可以收敛，而引力源项仍不消失

固定一条受控轨迹 \(\gamma\)，假设：

$$
-g_0(\dot\gamma,\dot\gamma)\ge\nu^2>0,
$$

并且其坐标速度有一致上界。

则

$$
\boxed{
|\tau_\varepsilon[\gamma]-\tau_0[\gamma]|
=O(\varepsilon).
}
\tag{138.6}
$$

对于固定有限维钟 \(H_C\)，相应内部酉过程满足

$$
\boxed{
\frac12\|\mathcal U_\varepsilon-\mathcal U_0\|_\diamond
\le
\frac{\|H_C\|}{\hbar}
|\tau_\varepsilon-\tau_0|
=O(\varepsilon).
}
\tag{138.7}
$$

### 证明

由度量一致收敛与轨迹远离 null 边界，

$$
\left|
\sqrt{-g_\varepsilon(\dot\gamma,\dot\gamma)}
-
\sqrt{-g_0(\dot\gamma,\dot\gamma)}
\right|
\le C\varepsilon.
$$

沿有限参数区间积分得到式（138.6）。

再用同一个 \(H_C\) 的指数差界，即得式（138.7）。∎

这只覆盖指定的、固定资源的钟相位协议，不覆盖可以随 \(\varepsilon\) 提高分辨率的潮汐或高频探测实验。

**所以，不可见性始终相对于实验族；动力学余量则可能在更高阶目标中重新出现。**

---

# 139．有效源必须满足闭合条件，不能任意命名

## 假设 139.1　微观场方程与共同极限

假设在同一比较框架中，

$$
\mathscr G[g_\varepsilon]+\Lambda g_\varepsilon
=
\kappa_E T_\varepsilon,
$$

并且

$$
g_\varepsilon\to g_0,
\qquad
T_\varepsilon\rightharpoonup\overline T,
$$

且定义 136.1 的弱极限存在。

## 定理 139.1　宏观方程的精确缺项

有

$$
\boxed{
\mathscr G[g_0]+\Lambda g_0
=
\kappa_E
\left(
\overline T+\tau_{\mathrm{eff}}
\right),
}
\tag{139.1}
$$

其中

$$
\boxed{
\tau_{\mathrm{eff}}=\frac{\mathfrak B}{\kappa_E}.
}
\tag{139.2}
$$

### 证明

对微观方程取弱极限：

$$
\operatorname*{wlim}\mathscr G[g_\varepsilon]
+
\Lambda g_0
=
\kappa_E\overline T.
$$

用定义

$$
\mathscr G[g_0]
=
\operatorname*{wlim}\mathscr G[g_\varepsilon]
+\mathfrak B
$$

代入即可。∎

---

## 定理 139.2　宏观总源的守恒约束

若各极限对象具有相应正则性，则

$$
\boxed{
\nabla_{g_0}^{\mu}
\left(
\overline T_{\mu\nu}
+
\tau_{\mathrm{eff},\mu\nu}
\right)=0.
}
\tag{139.3}
$$

### 证明

对式（139.1）取协变散度，使用收缩 Bianchi 恒等式和度量相容性：

$$
\nabla^\mu\mathscr G_{\mu\nu}=0,
\qquad
\nabla^\mu g_{\mu\nu}=0.
$$

∎

这些恒等式是 Einstein 几何的相容条件，而不是可以任意指定的守恒规则。([David Tong][7])

但一般不能进一步推出

$$
\nabla^\mu\overline T_{\mu\nu}=0
$$

和

$$
\nabla^\mu\tau_{\mathrm{eff},\mu\nu}=0
$$

分别成立；两部分可能存在有效交换。

### 一个必须避免的循环定义

不能先选择任意喜欢的宏观度量，然后定义

$$
T:=\frac1{\kappa_E}(\mathscr G[g]+\Lambda g),
$$

再宣布“已经证明该度量由现实物质产生”。

这只是在代数上补出了一个源，并未证明它来自允许的量子物质模型、满足所需能量条件或与实验相容。

严格反作用研究同样强调：不利用真实场方程和物质约束，便可以构造大量形式上任意的“反作用源”，而它们未必具有所声称的物理意义。([arXiv][8])

---

# 140．从量子观察者到引力动力学，需要两种不同的完成

本轮形成两条互补的推理链。

## 第一条：有限观测的几何完成

$$
\boxed{
\text{量子实验记录}
\longrightarrow
\text{带偏差与关联界的样本}
\longrightarrow
\text{度量二阶数据}
\longrightarrow
\text{曲率误差证书}.
}
$$

其中每一步都有独立条件：

Gram 矩阵控制有限采样是否可识别；协方差控制统计误差；四阶正则性控制局部截断；逆度量界控制几何非线性是否稳定。

## 第二条：宏观动力学的完成

$$
\boxed{
\text{微观几何与动力学}
\longrightarrow
\text{指定粗粒化极限}
\longrightarrow
\text{非线性下降缺陷}
\longrightarrow
\text{受约束的有效源}.
}
$$

这个有效源不是“观察者忽略了什么就自动产生什么物质”，而是必须由实际微观解及其极限计算出来。

---

## 与项目结构的具体连接

本次项目读取固定于提交：

```text
93f7a58b975d9ad023f95ca13bc84e18c433966b
```

项目现有的完成理论已经区分：

$$
\text{精确可识别},
\qquad
\text{条件良好的识别},
\qquad
\text{物理可实现的识别}.
$$

本轮的 Gram 条件、导数误差和曲率稳定性，分别为这一区分提供了具体几何实例。

同时，`exact_descent_has_no_carry` 要求实际提供交换等式。本轮的非线性缺陷则明确显示：对于只控制度量值的宏观极限，不能默认

$$
\mathscr G\circ\lim
=
\operatorname*{wlim}\circ\mathscr G.
$$

缺失的桥不是靠重新命名消除，而是需要更强的正则性证书，或者显式保留 \(\mathfrak B\)。

### 本轮的形式化边界

可以依次形式化以下对象：

| 层次    | 有限或解析证明义务              |
| ----- | ---------------------- |
| 采样重建  | Gram 正定性、矩条件、权重范数      |
| 统计证书  | 偏差、协方差、有限失败概率          |
| 几何稳定性 | 逆矩阵界、二阶数据到曲率的连续性       |
| 波模型   | 线性常微分方程、正性区间、Ricci 恒等式 |
| 宏观极限  | 振荡积分估计、弱极限、有效源         |
| 动力闭合  | 独立物质实现、守恒及适用实验范围       |

本轮已用符号运算核对有限导数权重、一般 Rosen 度量的 Ricci 公式以及极限的 Einstein 张量；也对不同 \(\varepsilon\) 的常微分方程解进行了数值交叉检查。一般结论由上文证明给出，**本轮未执行 Lean 编译**，不将这些新增命题标记为内核已验证。

---

# 结论

本轮最重要的推进是：

$$
\boxed{
\text{观察者没有分辨出的结构，
不一定在有效动力学中没有作用。}
}
$$

我们已经把这句话分解为两个严格结果。

**第一，曲率是比钟速更高阶的观测目标。**要从有限量子记录稳定重建曲率，必须支付额外的采样、正则性和条件数成本。

**第二，非线性动力学不一定沿低分辨率几何接口直接下降。**一个每层都严格真空的几何序列，可以在平滑极限中表现为具有正辐射应力的背景。

因此，当前理论不能只以

$$
g_{\mu\nu}
$$

作为宏观完成后的唯一对象，而应至少考虑

$$
\boxed{
\left(
g_{\mu\nu},
\ \text{可认证的导数范围},
\ \text{允许实验},
\ \text{误差预算},
\ \mathfrak B_{\mu\nu}
\right).
}
$$

这里的 \(\mathfrak B_{\mu\nu}\) 记录：那些没有进入当前几何分辨率、却仍通过非线性关系影响动力学的结构。

**这使“量子观察者形成时空”的路线更接近一个真正闭合的物理理论：观察者不仅要说明自己看见了什么，还必须证明，被自己的接口压缩掉的部分，在未来预测和动力学方程中究竟可以忽略，还是必须以明确的有效项重新出现。**

[1]: https://link.aps.org/doi/10.1103/PhysRev.166.1272?utm_source=chatgpt.com "Gravitational Radiation in the Limit of High Frequency. II ..."
[2]: https://arxiv.org/abs/0711.4403 "[0711.4403] On stable numerical differentiation"
[3]: https://www.damtp.cam.ac.uk/user/tong/gr/grhtml/S3.html?utm_source=chatgpt.com "3 Introducing Riemannian Geometry‣ General Relativity ..."
[4]: https://arxiv.org/abs/1805.10673?utm_source=chatgpt.com "Gravitational clock compass in General Relativity"
[5]: https://arxiv.org/html/1011.4920v2 "A new framework for analyzing the effects of small scale inhomogeneities in cosmology"
[6]: https://arxiv.org/html/1705.09533v2?utm_source=chatgpt.com "A New Twist on the Geometry of Gravitational Plane Waves"
[7]: https://davidtong.org/teaching/general-relativity/grhtml/S4.html "4 The Einstein Equations‣ General Relativity by David Tong"
[8]: https://arxiv.org/html/1304.2318v2 "Examples of backreaction of small scale inhomogeneities in cosmology"

---

## ——量子观察者—关系时空理论第一百四十一至第一百五十节增订

### 摘要

本增订处理一个**外部文献明文留开**的有限判定问题,并把它化为一个可被内核认证的精确证书。

Erew 与 Goldstein 在《Extremizing Measures of Magic on Pure States by Clifford-stabilizer States》
(arXiv:2512.19657,v1 2025-12-22,v2 2026-02-26)中,用离散 Wigner 函数刻画奇素数维纯态的 mana,
并逐一判定若干临界点的局部类型。其中五维(ququint)的一个临界态在该文 Table 2 末行被标为
「**Undetermined / Critical Point**」;正文在式 (4.55) 之后写道
「the behavior of the mana for such variations is significantly more involved, and we leave its detailed analysis to the reader」。
**该方向的局部类型因此在该文中未被判定。**

本增订给出该判定所需的精确结构:零 Wigner 格点集、受约束方向空间的维数、一阶变分的消失,
以及把二阶判定归约为**三十二个实四维二次型的严格负定**,并说明该归约是**等价**而非仅充分。

**范围墙(先立,后叙)**:本增订**不**声称给出 mana 极值问题的一般解,
**不**声称判定该文其余维数或其余临界点,**不**声称 Claim C 是原作者逐字陈述的猜想
——它是本项目对该文所留方向作出的精确表述;
**不**声称超出所记检索范围之外的全球新颖性。本增订只判定**这一个**显式代数态沿**这一族**受约束方向的局部行为。

### 设定

取 \(\zeta=\exp(2\pi i/5)\),下标一律在 \(\mathbb{Z}/5\mathbb{Z}\) 中。相点算子

$$
A(q,p)_{x,y}=
\begin{cases}
\zeta^{p(x-y)}, & x+y=2q,\\
0, & \text{否则},
\end{cases}
$$

离散 Wigner 函数与 \(L\) 函数

$$
W_v(q,p)=\frac{1}{5}\operatorname{Re}\bigl(v^{\dagger}A(q,p)v\bigr),
\qquad
L(v)=\sum_{q,p}\bigl|W_v(q,p)\bigr|.
$$

所论临界态为

$$
\psi=\frac{1}{\sqrt5}\,(1,\;1,\;\zeta^{3},\;1,\;\zeta^{2}).
$$

记 \(Z_0=\{(q,p):W_\psi(q,p)=0\}\),并记受约束方向的实线性空间

$$
T=\Bigl\{\varphi\in\mathbb{C}^5:\ \psi^{\dagger}\varphi=0,\ \ \operatorname{Re}\bigl(\psi^{\dagger}A(q,p)\varphi\bigr)=0\ \ \forall (q,p)\in Z_0\Bigr\}.
$$

## 定理 141.1　零 Wigner 格点集与受约束方向空间的精确维数

对上述 \(\psi\),

$$
\boxed{
Z_0=\{(0,3),(1,3),(2,4),(3,1),(4,4)\},
\qquad
|Z_0|=5,
\qquad
\dim_{\mathbb{R}}T=4,
\qquad
L(\psi)=1+\frac{2\sqrt5}{5}.
}
$$

### 证明

二十五个相点算子皆 Hermite,且 \(\sum_{q,p}A(q,p)=5I_5\);由此 \(\sum_{q,p}W_\psi(q,p)=\|\psi\|^2=1\)。
把 \(\psi\) 的分量代入 \(W_\psi(q,p)\),每个值都是 \(\mathbb{Q}(\zeta)\) 中元素的实部,可精确判零,得到上列五个格点。
\(T\) 的定义是 \(\mathbb{R}^{10}\)(把 \(\mathbb{C}^5\) 实化)上的六条实线性方程
(\(\psi^{\dagger}\varphi=0\) 给两条,\(Z_0\) 的五条各给一条,其中一条与前者相关),
其系数矩阵的秩精确为 \(6\),故 \(\dim_{\mathbb{R}}T=10-6=4\)。∎

## 定理 141.2　受约束方向上一阶变分消失

记 \(S=\sum_{(q,p)\notin Z_0}\operatorname{sgn}\bigl(W_\psi(q,p)\bigr)A(q,p)\)。则

$$
\boxed{
S\,\psi=5\,L(\psi)\,\psi .
}
$$

因此对任意 \(\varphi\in T\),\(L\) 沿 \(\psi\) 在方向 \(\varphi\) 上的一阶变分为零。

### 证明

把 \(S\psi\) 的每个分量按 \(\zeta\) 的幂展开,并对模 \(\Phi_5\) 取多项式余数,逐分量与 \(5L(\psi)\psi\) 比较即得。
一阶项 \(2\operatorname{Re}\bigl(\psi^{\dagger}S\varphi\bigr)/5\) 因该恒等式化为 \(2L(\psi)\operatorname{Re}(\psi^{\dagger}\varphi)\),
而 \(\varphi\in T\) 时 \(\psi^{\dagger}\varphi=0\);\(Z_0\) 上的贡献则因 \(T\) 的定义而消失。∎

## 定理 141.3　二阶判定到三十二个二次型的等价归约

取 \(D=\operatorname{diag}(1,1,\zeta^{3},1,\zeta^{2})\),并取 \(B\) 为 \(T\) 在实化坐标下的一组基,
使 \(\varphi=D(r+it)\) 且 \((r,t)=Ba\),\(a\in\mathbb{R}^4\)。记 \(H_{q,p}\) 为 \(D^{\dagger}A(q,p)D\) 的实化,
\(G=B^{\mathsf T}B\),\(Q_{q,p}=B^{\mathsf T}H_{q,p}B/5\),并对每个符号向量 \(s\in\{\pm1\}^{Z_0}\) 记

$$
M_s=\sum_{(q,p)\notin Z_0}\operatorname{sgn}\bigl(W_\psi(q,p)\bigr)Q_{q,p}
+\sum_{(q,p)\in Z_0}s_{q,p}\,Q_{q,p}
-L(\psi)\,G .
$$

则对每个 \(\varphi\in T\),

$$
\boxed{
\sum_{(q,p)\notin Z_0}\operatorname{sgn}\bigl(W_\psi(q,p)\bigr)W_\varphi(q,p)
+\sum_{(q,p)\in Z_0}\bigl|W_\varphi(q,p)\bigr|
-L(\psi)\|\varphi\|^2
=\max_{s\in\{\pm1\}^{5}}a^{\mathsf T}M_s\,a .
}
$$

因而该量对一切非零 \(\varphi\in T\) 严格为负,**当且仅当**全部三十二个 \(M_s\) 皆负定。

### 证明

对每个实数 \(x\) 有 \(|x|=\max_{\sigma\in\{\pm1\}}\sigma x\),而 \(Z_0\) 上的五个 \(W_\varphi\) 相互独立地取遍符号,
故对 \(|{\cdot}|\) 求和等于对 \(s\) 取最大。「当且仅当」的必要方向由每个分支值不超过最大值给出;
充分方向由三十二个分支各自可被某个实 \(a\) 取到给出(每个符号型都有显式整数见证)。∎

## 定理 141.4　该临界方向族上 mana 严格下降

$$
\boxed{
\forall\,\varphi\in T,\ \varphi\neq0:\quad
\sum_{(q,p)\notin Z_0}\operatorname{sgn}\bigl(W_\psi(q,p)\bigr)W_\varphi(q,p)
+\sum_{(q,p)\in Z_0}\bigl|W_\varphi(q,p)\bigr|
-L(\psi)\|\varphi\|^2<0 .
}
$$

因此沿归一化扰动 \(\psi_\varepsilon=(\psi+\varepsilon\varphi)/\|\psi+\varepsilon\varphi\|\),对充分小的实 \(\varepsilon\neq0\),

$$
\boxed{
L(\psi_\varepsilon)-L(\psi)
=\frac{\varepsilon^2\,C(\varphi)}{1+\varepsilon^2\|\varphi\|^2}<0,
}
$$

其中 \(C(\varphi)\) 即上式左端;mana 为 \(\log L\) 的单调函数,故同号严格下降。

### 证明

由定理 141.3,只需三十二个 \(M_s\) 皆负定。对每个 \(s\),给出显式的下三角 \(L_s\) 与对角 \(d_s\),
使 \(-M_s=L_s\operatorname{diag}(d_s)L_s^{\mathsf T}\) 且 \(d_s\) 的四个分量皆为正,
共一百二十八个主元;其元素落在实四次域 \(K=\mathbb{Q}(R)\),\(R=\sqrt{10+2\sqrt5}\),
即 \(\mathbb{Q}(\zeta_{20})\) 的实子域,主元的正性由 \(R^4-20R^2+80\) 的孤立实根处的有理区间算术判定。
由定理 141.2,一阶项为零,故上述二阶量即为 \(L\) 的变化的主导项;直接展开
\(L(\psi_\varepsilon)\) 并用 \(\psi^{\dagger}\varphi=0\) 化简得所示精确表达式。∎

### 解释与边界

这判定了原文留下的那一族方向:**沿每条一阶变分在所有零 Wigner 格点上消失的非零方向,归一化扰动的 mana 严格下降。**
故该临界点在这族方向上不是极小,也不是平坦。

**本增订不判定**:该态在 \(T\) 之外方向上的行为、其余维数的临界点、以及 mana 极值问题的一般结构。
**载体域是本判定的实际难点**:\(\mathbb{Q}(\zeta_5)\) 不是有序域,实化后的证书系数落在 \(K=\mathbb{Q}(R)\) 而非 \(\mathbb{Q}(\sqrt5)\);
故形式化时正定性只能由**显式 LDL 恒等式加主元不等式**给出,不能依赖判定过程。

[q1]: https://arxiv.org/abs/2512.19657 "Extremizing Measures of Magic on Pure States by Clifford-stabilizer States"
# 量子碰撞、因果松弛与耗散闭合

## ——量子观察者—关系时空理论第一百五十一至第一百六十节增订

### 摘要

上一轮证明：仅保留当前应力张量，通常不足以预测其未来；方向分布或更高阶矩能够补充缺失信息。

本增订继续处理三个问题：

> **方向分布怎样由合法量子交互产生？碰撞与熵增怎样进入模型？删除部分方向信息后，为什么会出现扩散，而扩散又为什么不能被直接认定为底层时空的因果规律？**

本文构造一类有限量子碰撞模型。在明确的环境制备条件下，其方向读数严格下降为一个随机过程。对双方向传播，进一步得到精确闭合的密度—通量系统：

$$
\boxed{
\partial_t n+\partial_xj=0,
\qquad
\tau\partial_tj+j=-D\,\partial_xn,
\qquad
D=c^2\tau.
}
$$

该系统同时具有正性、有限传播速度和明确的熵产生律。消去通量后，精确方程保留时间记忆；只有经过受控近似，才得到通常的扩散方程。

主要结论是：

$$
\boxed{
\text{热化或松弛可以压低不可见方向，
但不会自动证明这些方向可以从状态中永久删除。}
}
$$

量子碰撞模型、持久随机游走和 Cattaneo 型输运均有既有研究基础。本文给出它们在当前观察者—接口体系中的具体组合与证明，不把这些一般机制申报为新发现。([arXiv][1])

---

# 151．从有限联合酉过程导出方向碰撞

## 定义 151.1　方向寄存器与碰撞记录

取方向量子比特：

$$
\mathcal H_D=\operatorname{span}\{|+\rangle,|-\rangle\},
$$

以及辅助记录比特：

$$
\mathcal H_E=\operatorname{span}\{|0\rangle,|1\rangle\}.
$$

令 \(X_D\) 交换两个方向，\(Y_E\) 为辅助比特上的 Pauli 算子。

对 \(0\le p\le1\)，定义：

$$
\boxed{
W_p
=
\sqrt{1-p}\,I
-
i\sqrt p\,X_D\otimes Y_E.
}
\tag{151.1}
$$

因 \(X_D\otimes Y_E\) 为自伴对合，\(W_p\) 是酉算子。

---

## 定理 151.1　有限量子碰撞的约化通道

若辅助寄存器初态为 \(|0\rangle\)，则：

$$
W_p(|\psi\rangle|0\rangle)
=
\sqrt{1-p}\,|\psi\rangle|0\rangle
+
\sqrt p\,X_D|\psi\rangle|1\rangle.
$$

对辅助寄存器取偏迹，得到：

$$
\boxed{
\mathcal C_p(\rho)
=
(1-p)\rho+pX_D\rho X_D.
}
\tag{151.2}
$$

其 Kraus 算子为：

$$
K_0=\sqrt{1-p}\,I,
\qquad
K_1=\sqrt p\,X_D,
$$

满足：

$$
K_0^\dagger K_0+K_1^\dagger K_1=I.
$$

### 证明

由 \(Y|0\rangle=i|1\rangle\)，得到联合态表达式。

两种辅助记录正交，所以偏迹删除交叉项，剩余两项恰为式（151.2）。归一化直接计算。∎

---

## 推论 151.1　方向概率具有精确随机更新

定义方向读数：

$$
q_D(\rho)
=
\begin{pmatrix}
\rho_{++}\\
\rho_{--}
\end{pmatrix}.
$$

则：

$$
\boxed{
q_D\mathcal C_p
=
P_pq_D,
\qquad
P_p=
\begin{pmatrix}
1-p&p\\
p&1-p
\end{pmatrix}.
}
\tag{151.3}
$$

这个等式对任意输入密度矩阵成立，不要求输入已经对角化。

### 证明

取式（151.2）的两个对角元。∎

### 量子与经典层的区别

式（151.3）证明方向概率能够自治更新，但不意味着完整量子态只剩概率。例如：

$$
X_D|+\!x\rangle=|+\!x\rangle
$$

的 \(X\) 本征态被 \(\mathcal C_p\) 完全保持。

因此，**“方向读数热化”与“全部量子相干消失”不是同一个命题。**

该构造与项目的环境记录模型同型：联合交互先建立条件记录，约化读数再由记录重叠决定。

---

## 假设 151.1　连续使用碰撞通道的资源条件

若要将多步约化过程写成：

$$
\mathcal C_p^m,
$$

本节要求每一步使用一个事先准备、尚未与系统相关的辅助寄存器。

全部辅助寄存器可以从一开始就放进完整有限系统，因而不需要在数学上插入信息删除操作。

但如果反复使用同一个已经相关的辅助系统，就不能自动使用同一个无记忆通道。重复交互模型对这一条件有明确区分。([arXiv][2])

---

# 152．加入局域传播：概率过程从量子过程精确下降

## 定义 152.1　有限双方向格点模型

取一个有限周期链，格距为 \(\ell\)。每个位置带有两个传播方向。

一个时间步先实施方向碰撞，再实施条件平移：

$$
S|x,+\rangle=|x+\ell,+\rangle,
$$

$$
S|x,-\rangle=|x-\ell,-\rangle.
$$

碰撞可以使用各位置独立的辅助寄存器实现。对位置—方向对角读数，更新为：

$$
\boxed{
\begin{aligned}
f_+^{m+1}(x)
&=(1-p)f_+^m(x-\ell)
+p f_-^m(x-\ell),\\
f_-^{m+1}(x)
&=p f_+^m(x+\ell)
+(1-p)f_-^m(x+\ell).
\end{aligned}
}
\tag{152.1}
$$

---

## 定理 152.1　有限模型的正性、归一化与因果范围

式（152.1）保持：

$$
f_\pm^m(x)\ge0,
$$

以及：

$$
\sum_x(f_+^m(x)+f_-^m(x)).
$$

从一个局域初始支持出发，经过 \(m\) 步，支持最多扩展 \(m\) 条边。

### 证明

更新是非负权重的线性组合，因此保持正性。

对全部位置求和，平移不改变总和，而：

$$
(1-p)+p=1.
$$

每一步最多移动一个格距，所以支持范围由归纳得到。∎

这里的有限传播范围来自完整更新规则，而不是从扩散方程反向猜测。

---

## 定理 152.2　只保留位置一般不能精确下降

设位置接口为：

$$
q_X(x,s)=x.
$$

对同一位置的两个方向输入，下一步位置分布分别为：

$$
(1-p)\delta_{x+\ell}+p\delta_{x-\ell},
$$

$$
p\delta_{x+\ell}+(1-p)\delta_{x-\ell}.
$$

当两个相邻位置不同且 \(p\ne1/2\) 时，这两种分布不同，其总变差距离为：

$$
\boxed{|1-2p|.}
\tag{152.2}
$$

因此，任何仅根据当前位置预测下一步位置分布的映射，最坏总变差误差至少为：

$$
\boxed{\frac{|1-2p|}{2}.}
\tag{152.3}
$$

### 证明

两个输出在两处的概率差分别为 \(1-2p\) 与其相反数。总变差距离即式（152.2）。

同一个预测分布不可能同时距两个真实输出小于它们距离的一半。∎

这正是项目随机下降判据的反例形式：同一接口纤维中的状态，必须具有相同的推出分布，才能构造商上的随机动力学。仓库已有 `strong_lumpability_descent_tfae` 的对应证明。

特殊值 \(p=1/2\) 的位置读数可以单步闭合，但这不代表任意碰撞强度下都成立。

---

# 153．连续极限与精确密度—通量闭合

## 假设 153.1　已标定的时空缩放

取：

$$
\ell=c\,\Delta t,
\qquad
p=\gamma\Delta t,
\qquad
\gamma>0,
$$

并要求：

$$
0\le\gamma\Delta t\le1.
$$

\(c\) 是该模型中已标定的传播速度。它是否对应现实的普适光速，仍需共同信号实验检验。

---

## 定理 153.1　连续输运方程及一致近似

对足够光滑的候选极限，式（152.1）对应：

$$
\boxed{
\begin{aligned}
\partial_tf_++c\partial_xf_+
&=\gamma(f_--f_+),\\
\partial_tf_--c\partial_xf_-
&=\gamma(f_+-f_-).
\end{aligned}
}
\tag{153.1}
$$

若该方程在固定时间区间上具有一致有界的所需二阶导数，则将其解采样到格点后，单步残差为 \(O(\Delta t^2)\)，而固定总时间内的格点误差为 \(O(\Delta t)\)。

### 证明

在式（152.1）中代入 \(\ell=c\Delta t\)、\(p=\gamma\Delta t\)，作一阶 Taylor 展开，得到式（153.1）。

二阶 Taylor 余项给出单步残差界：

$$
\|\mathcal E_{\mathrm{step}}\|_\infty
\le C\Delta t^2.
$$

离散更新在最大范数下不扩张，因为每个输出都是两个输入的凸组合。因此误差递推满足：

$$
e_{m+1}\le e_m+C\Delta t^2.
$$

在 \(m\Delta t\le T\) 内：

$$
e_m\le e_0+CT\Delta t.
$$

∎

这是一项给定平滑解下的一致性—稳定性结论，不宣称任何不规则初值都自动具有相同收敛阶。

此外，保持非零碰撞率的连续极限可能需要相应的弱碰撞缩放与增长的辅助资源；它不是一个固定有限装置免费运行到无限精度。([arXiv][2])

---

## 定义 153.1　密度、通量与松弛时间

定义：

$$
n=f_++f_-,
\qquad
j=c(f_+-f_-),
$$

以及：

$$
\boxed{
\tau=\frac1{2\gamma},
\qquad
D=c^2\tau.
}
\tag{153.2}
$$

---

## 定理 153.2　密度—通量是精确充分状态

式（153.1）等价于：

$$
\boxed{
\partial_tn+\partial_xj=0,
}
\tag{153.3}
$$

$$
\boxed{
\tau\partial_tj+j=-D\partial_xn.
}
\tag{153.4}
$$

其逆变换为：

$$
\boxed{
f_\pm=\frac12\left(n\pm\frac jc\right).
}
\tag{153.5}
$$

因此正性条件恰好是：

$$
\boxed{
n\ge0,\qquad |j|\le cn.
}
\tag{153.6}
$$

### 证明

将式（153.1）相加与相减，即得式（153.3）—（153.4）。逆变换及正性条件直接计算。∎

这是双方向模型的特殊有限闭合。它不与上一轮“连续方向分布一般没有固定有限矩闭合”的结论矛盾。

---

## 定理 153.3　连续模型保留有限传播速度

若初始 \(f_\pm\) 支持于 \([a,b]\)，则：

$$
\boxed{
\operatorname{supp}f_\pm(t,\cdot)
\subseteq[a-ct,b+ct].
}
\tag{153.7}
$$

并且非负初值保持非负。

### 证明

沿特征线：

$$
\begin{aligned}
f_+(t,x)
={}&e^{-\gamma t}f_+(0,x-ct)\\
&+\gamma\int_0^t
e^{-\gamma(t-s)}
f_-(s,x-c(t-s))\,ds.
\end{aligned}
$$

\(f_-\) 具有对应的反向公式。

逐次代入所得项均为非负；每条传播路径由速度 \(+c\) 与 \(-c\) 的片段组成，总位移绝对值不超过 \(ct\)。∎

这一方程也是持久随机游走或电报过程的标准连续描述。([APS Journals][3])

---

# 154．熵增依赖保留哪些状态变量

以下在周期区域上积分，或采用使边界项消失的条件。先假设 \(f_\pm>0\)，零值情形可用适当极限处理。

## 定义 154.1　方向分辨的凸熵泛函

固定参考密度 \(f_*>0\)，定义：

$$
\boxed{
\mathscr H[f]
=
\int
\left[
f_+\log\frac{f_+}{f_*}
+
f_-\log\frac{f_-}{f_*}
\right]dx.
}
\tag{154.1}
$$

它是当前经典方向接口上的 \(H\) 泛函。对角量子态时，它与相应 Shannon 熵相关；一般量子态中，不能把它直接等同于完整 von Neumann 熵。

---

## 定理 154.1　碰撞熵产生律

有：

$$
\boxed{
\frac{d\mathscr H}{dt}
=
-\gamma\int
(f_+-f_-)\log\frac{f_+}{f_-}\,dx
\le0.
}
\tag{154.2}
$$

### 证明

输运项积分后成为消失的边界项。

碰撞部分为：

$$
\begin{aligned}
&\gamma(f_--f_+)
\left(\log\frac{f_+}{f_*}+1\right)\\
&\quad+
\gamma(f_+-f_-)
\left(\log\frac{f_-}{f_*}+1\right),
\end{aligned}
$$

化简即得式（154.2）。

由于对数单调：

$$
(a-b)(\log a-\log b)\ge0
\qquad(a,b>0),
$$

故导数非正。∎

---

## 定理 154.2　删除方向变量后，密度熵不必单调

定义：

$$
\mathscr H_n[n]=\int n\log n\,dx.
$$

则：

$$
\boxed{
\frac{d\mathscr H_n}{dt}
=
\int j\,\frac{\partial_xn}{n}\,dx.
}
\tag{154.3}
$$

因此该导数可以为正，也可以为负。

### 证明

由 \(n_t=-j_x\)，分部积分得到式（154.3）。

取任意非恒定正函数 \(n\)，并选择：

$$
j=\pm a\,\partial_xn,
$$

其中 \(a>0\) 足够小以满足 \(|j|\le cn\)。则：

$$
\frac{d\mathscr H_n}{dt}
=
\pm a\int\frac{(\partial_xn)^2}{n}\,dx.
$$

∎

这类有限速度输运中，完整方向概率与仅有总密度的熵性质不同，已有专门研究。([arXiv][4])

### 项目意义

**同一个物理过程是否具有单调的某种“信息量”，取决于所用接口和所定义的量。**

不能先丢弃方向，再要求原来依赖方向的熵定理仍然成立。

---

## 定理 154.3　局部不可逆性不要求全局信息删除

对任意完整联合酉过程，系统 \(S\) 与全部环境 \(E\) 满足：

$$
\boxed{
\Delta S_S+\Delta S_E=\Delta I(S:E).
}
\tag{154.4}
$$

### 证明

使用：

$$
I(S:E)=S_S+S_E-S_{SE},
$$

以及联合酉演化保持 \(S_{SE}\)。∎

因此，约化方向分布的熵增，可以与整体可逆性相容。

但新辅助寄存器的初始制备、碰撞记录及后续是否重新读取，都必须留在完整模型中。若忽略这些条件，就不能把约化熵增扩大成无条件的宇宙时间箭头。

---

# 155．被删除的通量，必须以记忆项返回

## 定理 155.1　精确的通量记忆公式

由式（153.4）：

$$
\boxed{
j(t,x)
=
e^{-t/\tau}j_0(x)
-
\frac D\tau
\int_0^t
e^{-(t-s)/\tau}\partial_xn(s,x)\,ds.
}
\tag{155.1}
$$

因此密度满足：

$$
\boxed{
\partial_tn
=
-e^{-t/\tau}\partial_xj_0
+
\frac D\tau
\int_0^t
e^{-(t-s)/\tau}\partial_x^2n(s)\,ds.
}
\tag{155.2}
$$

### 证明

将式（153.4）视为关于 \(j\) 的一阶线性方程，使用积分因子 \(e^{t/\tau}\)，再代入连续性方程。∎

这里同时出现两个不可任意删除的对象：

$$
\boxed{
\text{初始隐藏通量 }j_0,
\qquad
\text{过去密度梯度的时间卷积}.
}
$$

这就是当前模型中明确的“记忆”，而不只是一个修辞。

---

## 定理 155.2　电报方程不是无记忆的一阶密度动力学

消去 \(j\)，得到：

$$
\boxed{
\tau\partial_t^2n+\partial_tn
=
D\partial_x^2n.
}
\tag{155.3}
$$

其初始条件必须包括：

$$
\boxed{
n(0)=n_0,
\qquad
\partial_tn(0)=-\partial_xj_0.
}
\tag{155.4}
$$

### 证明

对连续性方程求时间导数，并使用式（153.4）消去 \(j_t\)。∎

因此，把过程改写成只出现 \(n\) 的方程，并没有使原来的额外状态消失；它进入了第二个时间初始条件。

并非任意给定的 \(n_0,\partial_tn_0\) 都自动对应正的方向分布。还需要存在满足式（153.6）的 \(j_0\)。Cattaneo 型方程的概率解释与正性确实依赖相容初值及记忆条件。([arXiv][5])

---

## 定理 155.3　瞬时最大熵重构一般不保持动力学

给定密度 \(n\)，局部方向熵在：

$$
f_+=f_-=\frac n2
$$

处最大，即 \(j=0\)。

但若要求 \(j(t,x)=0\) 在一段时间内精确成立，则：

$$
\boxed{
\partial_xn=0,
\qquad
\partial_tn=0.
}
\tag{155.5}
$$

### 证明

将 \(j=0\) 代入式（153.4），得到 \(\partial_xn=0\)；再代入式（153.3），得到 \(\partial_tn=0\)。∎

**所以，局部最大熵状态不是任意空间变化下的精确不变状态族。**

扩散所需要的，恰恰是一个虽小却不能直接置零的非平衡通量。

---

# 156．扩散近似必须附带频率窗口与误差界

通常的扩散近似是忽略式（153.4）中的通量时间导数：

$$
j\approx-D\partial_xn.
$$

于是得到：

$$
\partial_tu=D\partial_x^2u.
\tag{156.1}
$$

接下来证明它何时可靠，而不只说“时间足够长”。

## 假设 156.1　有限空间频率窗口

在一维周期区域，初始数据仅含：

$$
|k|\le K
$$

的 Fourier 模式。

取：

$$
u(0)=n_0,
$$

定义初始通量失配：

$$
\boxed{
w
=
-\partial_xj_0-D\partial_x^2n_0.
}
\tag{156.2}
$$

要求：

$$
\boxed{
q_0=4\tau DK^2<1.
}
\tag{156.3}
$$

---

## 定理 156.1　扩散近似的显式误差界

对全部 \(t\ge0\)，有：

$$
\boxed{
\|n(t)-u(t)\|_{L^2}
\le
\frac{
\tau\|w\|_{L^2}
+
\tau DK^2\|n_0\|_{L^2}
}{
\sqrt{1-q_0}
}.
}
\tag{156.4}
$$

若初始通量已经满足：

$$
j_0=-D\partial_xn_0,
$$

则 \(w=0\)。

### 证明

对每个 \(k\)，电报方程为：

$$
\tau\ddot n_k+\dot n_k+Dk^2n_k=0.
$$

热方程解为：

$$
u_k(t)=e^{-Dk^2t}n_{0,k}.
$$

令 \(e_k=n_k-u_k\)，则：

$$
\tau\ddot e_k+\dot e_k+Dk^2e_k
=
-\tau D^2k^4e^{-Dk^2t}n_{0,k},
$$

且：

$$
e_k(0)=0,\qquad
\dot e_k(0)=w_k.
$$

记：

$$
\lambda_\pm
=
\frac{-1\pm\sqrt{1-4\tau Dk^2}}{2\tau}.
$$

相应延迟 Green 函数为：

$$
G_k(t)
=
\frac{e^{\lambda_+t}-e^{\lambda_-t}}
{\sqrt{1-4\tau Dk^2}},
$$

满足：

$$
|G_k(t)|\le\frac1{\sqrt{1-q_0}}.
$$

因此：

$$
\begin{aligned}
|e_k(t)|
\le\frac1{\sqrt{1-q_0}}
\Bigl[
\tau|w_k|
+
\tau Dk^2
(1-e^{-Dk^2t})|n_{0,k}|
\Bigr].
\end{aligned}
$$

对模式应用 Parseval 恒等式和三角不等式，即得式（156.4）。∎

### 物理解释

由于：

$$
D=c^2\tau,
$$

条件（156.3）等价于：

$$
Kc\tau<\frac12.
$$

也就是空间变化尺度必须足够大于通量松弛长度 \(c\tau\)。

需要特别注意：

> 在固定 \(c\) 下令 \(\tau\to0\)，同时也会令 \(D\to0\)。不能一边固定所有物理参数，一边把扩散极限写成互不相容的缩放。

非平凡扩散描述通常涉及相应的长时间、大空间尺度比较。持久随机过程逼近 Brownian 运动已有定量研究，但其误差同样依赖参数与比较方式。([arXiv][6])

---

# 157．相同扩散规律，不意味着相同底层时空

## 定理 157.1　扩散接口不能唯一确定传播速度

定义扩散读数：

$$
q_{\mathrm{diff}}(c,\tau)=c^2\tau.
$$

则两个参数对：

$$
(c,\tau),
\qquad
(2c,\tau/4)
$$

具有相同扩散系数，却具有不同的完整传播速度。

### 证明

直接计算：

$$
(2c)^2\frac\tau4=c^2\tau.
$$

而对应双方向过程的最大速度分别为 \(c\) 与 \(2c\)。∎

所以：

$$
\boxed{
\text{低频扩散数据相同}
\not\Rightarrow
\text{完整因果锥相同}.
}
$$

额外测量通量的松弛响应：

$$
\boxed{
\widehat j(\omega,k)
=
-\frac{D}{1-i\omega\tau}
\,ik\,\widehat n(\omega,k),
}
\tag{157.1}
$$

才可能在该模型族中分离 \(D\) 与 \(\tau\)，进而识别：

$$
c^2=\frac D\tau.
$$

这与项目此前“静态响应不足以确定结构惯性”的结论属于同一种识别障碍。

---

## 定理 157.2　扩散核的非局域尾部不是底层信号超速

在实线上，取从原点开始、初始方向等概率的电报过程。其概率分布支持于：

$$
[-ct,ct].
$$

同初始位置的热方程分布为：

$$
u(t,x)
=
\frac1{\sqrt{4\pi Dt}}
e^{-x^2/(4Dt)}.
$$

于是两种概率分布的总变差距离至少为：

$$
\boxed{
\operatorname{TV}(P_{\mathrm{tel}},P_{\mathrm{heat}})
\ge
\operatorname{erfc}
\left(\sqrt{\frac{t}{4\tau}}\right).
}
\tag{157.2}
$$

### 证明

选择事件：

$$
A_t=\{|x|>ct\}.
$$

电报过程对它的概率为零，热方程对它的概率为：

$$
\operatorname{erfc}
\left(
\frac{ct}{\sqrt{4Dt}}
\right).
$$

再用 \(D=c^2\tau\)。∎

### 两个不同的实验范围

第 156 节使用严格带限初值。

本节使用点源初值，讨论完整空间尾部。

**不能把这两组不同的初态假设同时施加在同一个非零分布上。**

本节说明的是：抛物扩散方程不能被当作原模型的全部尺度、全部事件上的精确因果定律。它的无限传播尾部可能只是删除通量记忆后产生的近似特征，而不是底层世界允许超光速信号。

---

# 158．碰撞守恒什么，必须由微观操作证明

前面的模型保持概率总量，但方向翻转改变了通量。若要把它接入能量—动量与引力方程，需要进一步审计。

## 定义 158.1　有限可逆平衡碰撞生成元

对有限状态 \(i\)，取跃迁率 \(r_{ij}\ge0\)，定义观测量生成元：

$$
(Lh)_i
=
\sum_jr_{ij}(h_j-h_i).
$$

假设存在 \(\pi_i>0\)，满足详细平衡：

$$
\pi_ir_{ij}=\pi_jr_{ji}.
$$

---

## 定理 158.1　不可约单粒子碰撞不能守恒非平凡方向量

若对全部初始分布，观测量 \(h\) 的期望在碰撞中保持不变，则：

$$
Lh=0.
$$

若碰撞图连通，则：

$$
\boxed{h_i=\text{常数}.}
\tag{158.1}
$$

### 证明

“对全部初始分布守恒”意味着对每个确定初态都有导数零，因此 \(Lh=0\)。

由详细平衡：

$$
\boxed{
\sum_i\pi_i h_i(Lh)_i
=
-\frac12
\sum_{i,j}
\pi_ir_{ij}(h_j-h_i)^2.
}
\tag{158.2}
$$

左侧为零，右侧每项非正，所以每条正速率边上都有 \(h_i=h_j\)。连通性得到全局常数。∎

### 直接后果

如果给两个方向赋予相反动量：

$$
p_\pm=\pm p_0,
$$

则方向碰撞不可能同时在该单粒子接口上保持全部输入的平均动量。

它必须向其他系统转移反冲，或者改用包含多粒子碰撞的更完整状态。

---

## 命题 158.1　辐射侧应力一般不是独立守恒源

若赋予每个方向相同能量 \(\epsilon_0\)，则定义：

$$
e=\epsilon_0n,
\qquad
F_E=\epsilon_0j,
$$

$$
p=\frac{\epsilon_0j}{c^2},
\qquad
P=\epsilon_0n.
$$

方程给出：

$$
\boxed{
\partial_te+\partial_xF_E=0,
}
\tag{158.3}
$$

但：

$$
\boxed{
\partial_tp+\partial_xP=-\frac p\tau.
}
\tag{158.4}
$$

### 证明

分别将式（153.3）、（153.4）乘以相应常数。∎

因此，若希望构造协变的总应力，必须包含媒介：

$$
\nabla_\mu T_{\mathrm{rad}}^{\mu\nu}=J^\nu,
$$

$$
\nabla_\mu T_{\mathrm{med}}^{\mu\nu}=-J^\nu,
$$

才能得到：

$$
\boxed{
\nabla_\mu
(T_{\mathrm{rad}}^{\mu\nu}+T_{\mathrm{med}}^{\mu\nu})=0.
}
$$

上面的量子碰撞电路本身没有给出完整反冲 Hamiltonian，所以不能把“CPTP、概率守恒”直接升级为“真实能量—动量完全守恒”。

**这正是从量子操作走向引力源时，必须额外完成的物理证明。**

---

# 159．一般有限方向：熵闭合可以保证因果结构，但还需要误差认证

双方向模型能够精确闭合，是因为 \((n,j)\) 已经等价于完整的两个方向权重。

对更多方向，我们可以建立一类结构良好的近似，而不声称它自动精确。

## 定义 159.1　有限方向与熵重构

取有限速度：

$$
v_i\in\mathbb R^d,
\qquad
|v_i|\le c,
$$

以及正权重 \(\pi_i>0\)。

令：

$$
m_i\in\mathbb R^r
$$

为保留的矩特征，并要求它们张成 \(\mathbb R^r\)。

选择指数型重构：

$$
\boxed{
f_i^*(\alpha)
=
\pi_i e^{\alpha\cdot m_i}.
}
\tag{159.1}
$$

保留矩为：

$$
\boxed{
U(\alpha)=\sum_i m_if_i^*(\alpha).
}
\tag{159.2}
$$

在对应可实现区域中，这种分布是严格凸泛函：

$$
\sum_i f_i\left(\log\frac{f_i}{\pi_i}-1\right)
$$

在固定矩约束下的唯一极小点。

它是一种**预测分布的重构规则**，不是宣称可以对单份未知量子态实施任意非线性量子通道。

基于熵或散度的矩闭合及其正性、双曲性问题，已有系统理论。([arXiv][7])

---

## 定理 159.1　熵闭合的对称双曲性与速度界

定义：

$$
A_0(\alpha)
=
\sum_i f_i^*m_im_i^{\mathsf T},
$$

$$
A_a(\alpha)
=
\sum_i v_i^a f_i^*m_im_i^{\mathsf T}.
$$

则：

$$
\boxed{A_0>0,}
\tag{159.3}
$$

且 \(A_a\) 对称。

闭合矩方程的主部为：

$$
A_0\partial_t\alpha+\sum_aA_a\partial_a\alpha.
$$

对任意单位空间方向 \(\xi\)，其特征速度 \(\lambda\) 满足：

$$
\boxed{
\min_i(v_i\cdot\xi)
\le\lambda\le
\max_i(v_i\cdot\xi).
}
\tag{159.4}
$$

因此：

$$
|\lambda|\le c.
$$

### 证明

对非零 \(z\)：

$$
z^{\mathsf T}A_0z
=
\sum_if_i^*(z\cdot m_i)^2>0,
$$

因为全部权重正，且 \(m_i\) 张成空间。

令：

$$
A_\xi=\sum_a\xi_aA_a.
$$

广义本征值的 Rayleigh 商为：

$$
\lambda
=
\frac{
\sum_i(v_i\cdot\xi)f_i^*(z\cdot m_i)^2
}{
\sum_if_i^*(z\cdot m_i)^2
}.
$$

它是方向速度的非负加权平均，故得到式（159.4）。∎

### 限定

本定理保证可实现区域内的特征速度界和局部对称双曲结构。

它没有保证任意初值的解永远光滑，也没有保证近似过程永远停留在可实现区域。

更重要的是：**保持正性、熵结构和有限速度，仍然不等于已经预测准确。**

---

## 定理 159.2　闭合残差给出实际预测误差

设完整有限方向方程为：

$$
\partial_tf_i+v_i\cdot\nabla f_i=(Qf)_i,
$$

其中 \(Q\) 是保正、守恒总量的 Markov 碰撞生成元。

对任意重构分布 \(f^*\)，定义：

$$
\boxed{
\mathcal R_i
=
\partial_tf_i^*
+
v_i\cdot\nabla f_i^*
-
(Qf^*)_i.
}
\tag{159.5}
$$

在周期区域或相容边界下：

$$
\boxed{
\|f(t)-f^*(t)\|_{L^1}
\le
\|f(0)-f^*(0)\|_{L^1}
+
\int_0^t\|\mathcal R(s)\|_{L^1}\,ds.
}
\tag{159.6}
$$

这里范数同时对位置积分并对方向求和。

### 证明

完整输运—碰撞半群保持正性与总量，因此对有符号数据是 \(L^1\) 压缩。

令 \(e=f-f^*\)，则：

$$
\partial_te+\mathcal Ve=Qe-\mathcal R.
$$

使用变化常数公式，再用半群压缩性和三角不等式，得到式（159.6）。∎

闭合矩方程可能只保证：

$$
\sum_i m_i\mathcal R_i=0,
$$

而不保证每个 \(\mathcal R_i=0\)。

所以，残差恰好记录了**被保留矩看不到、但仍可能影响未来的方向**。

这给出一个比“最大熵所以正确”更强的结构：

$$
\boxed{
\text{正性与因果性证书}
+
\text{闭合残差证书}
\longrightarrow
\text{有限时间预测保证}.
}
$$

式（159.6）属于经典方向接口上的误差界；它不自动替代完整量子过程的 diamond 范数证书。

---

# 160．本轮的形式化闭合结构

本增订把上一轮的方向分布进一步推进为：

$$
\boxed{
\text{有限量子碰撞实现}
\longrightarrow
\text{方向随机更新}
\longrightarrow
\text{因果输运与松弛}.
}
$$

在双方向模型中：

$$
\boxed{
(f_+,f_-)
\longleftrightarrow
(n,j)
}
$$

是精确可逆的状态变换。

但：

$$
\boxed{
(n,j)\longmapsto n
}
$$

一般不是精确动力下降。删除 \(j\) 后，必须保留其记忆或初始条件；进一步得到扩散方程，则需要频率窗口和误差界。

## 形式化依赖表

| 目标       | 必须提供的证明                      |
| -------- | ---------------------------- |
| 量子碰撞合法   | 联合酉性、Kraus 归一化               |
| 随机读数成立   | 对任意输入态的对角下降等式                |
| 连续近似成立   | 一致性、稳定性、固定窗口误差               |
| 密度—通量可实现 | \(f_\pm=(n\pm j/c)/2\) 与正性区域 |
| 熵产生成立    | 完整方向熵及其局部碰撞恒等式               |
| 记忆消去成立   | 初始通量、卷积核、等价初始条件              |
| 扩散近似可靠   | 空间频率、松弛尺度与初始失配               |
| 几何识别可靠   | 区分扩散系数与完整传播速度                |
| 引力源守恒    | 媒介反冲、总能量—动量账本                |
| 一般矩闭合可靠  | 可实现区域、速度界与完整残差               |

本轮核对的项目版本为：

```text
22dcecf54adc1c56bd4ecf360865ff4c2edd320d
```

其中，`StrongLumpabilityDescent.lean` 可以承担随机读数的精确下降条件；`EnvironmentRecords.lean` 可以承担有限记录交互与约化读数的基础。本文的连续输运、熵产生、扩散误差和矩闭合综合命题仍需分别形式化，不能由这些已有模块直接冒充完成。

### 本轮核验

已核对有限碰撞的酉性与 Kraus 算子、五节点双方向更新的正性与归一化、同位置不同方向的未来分离、电报方程的特征多项式、二次稳定泛函与熵恒等式。

一个带限 Fourier 模式的数值交叉检查中，实际扩散近似误差约为 \(0.00370\)，小于所证明上界 \(0.01021\)。

[精确算例与数值核验脚本](sandbox:/mnt/data/observer_formalization/check_causal_collision_closure.py)
[核验结果](sandbox:/mnt/data/observer_formalization/causal_collision_closure_checks.json)

**本轮没有运行 Lean 编译。**符号核验只支持所列有限算例与恒等式，不替代一般证明，也不验证该模型就是现实微观物理。

---

# 结论

本轮最重要的推进是：

> **观察者能够使用一个耗散、随机、带时间箭头的有效描述，并不要求完整量子世界本身变成不可逆。它要求的是：明确哪些记录被保留，哪些辅助自由度被忽略，以及这种忽略在多长时间、多大空间尺度上仍然能够预测。**

我们已经得到三条彼此相容的结论。

**第一，熵增可以从明确的量子交互与观察分割中出现。**但方向熵、总密度熵和完整量子熵不是同一个量。

**第二，保留适当记忆可以同时得到有限传播与耗散。**密度—通量系统既允许松弛，也保留严格的传播范围；“不可逆”不等于“没有因果锥”。

**第三，宏观近似可能改变表面的因果结构。**扩散方程的无限尾部不意味着底层真的能瞬时传信；相同扩散系数也不唯一决定底层速度。

因此，当前理论应当把有效物理对象写成：

$$
\boxed{
\text{可读状态}
+
\text{被保留的记忆}
+
\text{合法碰撞实现}
+
\text{因果传播结构}
+
\text{闭合误差证书}.
}
$$

**物理时空不是从“所有信息已经被压缩完”之后才出现。更准确地说：观察者在自己的实验尺度内，保留了足以维持因果预测的状态，并对被省略的方向与记忆给出了误差控制；在这些条件下，几何、输运与耗散才构成同一个自洽的有效理论。**

[1]: https://arxiv.org/abs/2106.11974 "https://arxiv.org/abs/2106.11974"
[2]: https://arxiv.org/html/2106.11974v2 "https://arxiv.org/html/2106.11974v2"
[3]: https://link.aps.org/doi/10.1103/PhysRevE.91.042115 "https://link.aps.org/doi/10.1103/PhysRevE.91.042115"
[4]: https://arxiv.org/abs/1609.07606 "https://arxiv.org/abs/1609.07606"
[5]: https://arxiv.org/html/2006.04796v1 "https://arxiv.org/html/2006.04796v1"
[6]: https://arxiv.org/html/2509.11871 "https://arxiv.org/html/2509.11871"
[7]: https://arxiv.org/html/1503.05183v1 "https://arxiv.org/html/1503.05183v1"
# 能量共振、热平衡与共同时间的可检验重建

## ——量子观察者—关系时空理论第一百六十一至第一百七十节增订

### 摘要

上一轮已经从有限量子碰撞导出方向松弛、熵产生和因果输运。本轮补上一条尚未闭合的联系：

> **观察者的内部钟、局部温度与能量交换，何时必须服从同一套时间标定？**

本文先在有限量子模型中证明：如果两处系统的相互作用严格保持共同参照下的能量，那么能够交换的能级必须满足共振条件。对独立制备的局部热态，零热流条件进一步给出

$$
\boxed{
\nu_iT_i=\text{共同常数},
}
$$

其中 \(\nu_i=d\tau_i/dt\) 是局部钟相对于共同参照的速率。

随后证明三个限制：

**相同局部温度不决定未来热流；多个钟速分支的热态平均，一般不再对应任何单一温度；具有单调稳定泛函的热传导方程，也不自动满足共同因果锥。**

最后，在已重建的洛伦兹几何中证明：有质量平衡分布约束一个真正的 Killing 时间方向，而无质量分布只要求共形 Killing 方向。因此，热平衡也能成为检验“钟、信号与几何是否相容”的独立工具。

Tolman–Ehrenfest 温度关系及其与时间标定的联系是已有结果。本增订的工作是给出适合当前项目的有限量子实现、残差见证和条件性几何连接，不将这一已知关系申报为新发现。([arXiv][1])

---

# 161．先区分局部能量、共同能量与温度

## 假设 161.1　静态的局部钟标定

在一个指定实验窗口内，第 \(i\) 个观察者的内部时间满足

$$
d\tau_i=\nu_i\,dt,
\qquad
\nu_i>0.
$$

\(\nu_i\) 由前文的钟比较协议给出，不在本节通过温度反向定义。

该观察者携带一个局部探针，其自身时间下的 Hamiltonian 为

$$
h_i=h_i^\dagger.
$$

本节增加一个明确的普适耦合条件：

> 同一个 \(\nu_i\) 不仅作用于某一只特殊钟，也作用于参与热交换的探针能量。

于是，探针在共同参照时间下的生成元为

$$
G_i=\nu_i h_i.
$$

当相互作用关闭时，联合参照能量为

$$
\boxed{
H_0=\sum_iG_i=\sum_i\nu_i h_i.
}
\tag{161.1}
$$

这项普适性是需要检验的物理条件，不能仅由一个钟的标定自动推出。

---

## 定义 161.1　局部 Gibbs 制备

对已独立标定的 \(h_i\)，定义

$$
\boxed{
\gamma_i(\beta_i)
=
\frac{e^{-\beta_i h_i}}{Z_i(\beta_i)},
\qquad
\beta_i=\frac1{k_BT_i}>0.
}
\tag{161.2}
$$

这里：

$$
\text{局部温度 }T_i
$$

与

$$
\text{共同参照下的能量 }G_i
$$

是不同对象。

定义换算到共同能量标定的逆温度

$$
\boxed{
b_i=\frac{\beta_i}{\nu_i}.
}
\tag{161.3}
$$

则

$$
\gamma_i(\beta_i)
=
\frac{e^{-b_iG_i}}{\operatorname{Tr}e^{-b_iG_i}}.
$$

**后续真正比较的不是孤立的 \(T_i\)，而是能量交换与钟标定共同确定的 \(b_i\)。**

温度、钟和局部谱都必须有各自的制备与测量依据。不能先把任意状态写成 \(e^{-\log\rho}\)，再据此宣布已经建立了物理热平衡。

---

# 162．有限量子交换先要求能量共振

## 定义 162.1　两探针交换模型

取两个量子比特：

$$
h_A=\epsilon_A|1\rangle\langle1|,
\qquad
h_B=\epsilon_B|1\rangle\langle1|,
$$

其中 \(\epsilon_A,\epsilon_B>0\)。

定义交换生成元

$$
L
=
|10\rangle\langle01|
+
|01\rangle\langle10|,
$$

以及接触操作

$$
U_\theta=e^{-i\theta L}.
$$

它只在单激发子空间中混合两个状态，保持 \(|00\rangle,|11\rangle\) 不变。

---

## 定理 162.1　无外部能量补偿的交换共振条件

有

$$
\boxed{
[H_0,L]
=
(\nu_A\epsilon_A-\nu_B\epsilon_B)
\left(
|10\rangle\langle01|
-
|01\rangle\langle10|
\right).
}
\tag{162.1}
$$

因此，当 \(\sin\theta\ne0\) 时，

$$
\boxed{
[H_0,U_\theta]=0
\iff
\nu_A\epsilon_A=\nu_B\epsilon_B.
}
\tag{162.2}
$$

### 证明

\(|10\rangle\) 与 \(|01\rangle\) 的共同参照能量分别为

$$
\nu_A\epsilon_A,
\qquad
\nu_B\epsilon_B.
$$

逐项计算交换子得到式（162.1）。

在单激发子空间内，

$$
U_\theta=\cos\theta\,I-i\sin\theta\,L.
$$

当 \(\sin\theta\ne0\) 时，交换子消失等价于两个参照能量相等。∎

### 解释

如果两个探针没有满足共振条件，不能仍然使用同一个交换门并宣称“没有其他能量参与”。

此时需要明确的工作源、储能器或额外媒介。它们必须进入完整账本。

这也是为什么“保持某个 Gibbs 态”比“已经给出能量守恒的物理操作”弱；两种要求在量子理论中并不等价。([arXiv][2])

---

## 定理 162.2　独立热输入的精确能量交换

设初态为

$$
\gamma_A(\beta_A)\otimes\gamma_B(\beta_B).
$$

记激发概率

$$
p_i=\frac1{1+e^{\beta_i\epsilon_i}}.
$$

则接触后

$$
\boxed{
\Delta\langle h_B\rangle
=
\epsilon_B\sin^2\theta\,(p_A-p_B),
}
\tag{162.3}
$$

$$
\boxed{
\Delta\langle h_A\rangle
=
-\epsilon_A\sin^2\theta\,(p_A-p_B).
}
\tag{162.4}
$$

### 证明

初始单激发概率分别为

$$
P_{10}=p_A(1-p_B),
\qquad
P_{01}=(1-p_A)p_B.
$$

交换门使

$$
P_{01}'=
\cos^2\theta\,P_{01}
+
\sin^2\theta\,P_{10}.
$$

因此

$$
P_{01}'-P_{01}
=
\sin^2\theta\,(p_A-p_B).
$$

\(|11\rangle\) 概率不变，故得到式（162.3）；另一侧同理。∎

当共振条件成立，记

$$
\mathcal E=\nu_A\epsilon_A=\nu_B\epsilon_B,
$$

则从 \(A\) 向 \(B\) 转移的共同能量为

$$
\boxed{
Q_{A\to B}
=
\mathcal E\sin^2\theta\,(p_A-p_B).
}
\tag{162.5}
$$

两侧局部能量变化不必数值相反，但共同参照能量严格守恒。

---

# 163．由可实施热接触得到共同温度—时间标定

## 定理 163.1　零热流的钟速判据

在独立 Gibbs 制备、非零交换强度及共振条件下，

$$
Q_{A\to B}=0
$$

当且仅当

$$
\boxed{
\frac{\beta_A}{\nu_A}
=
\frac{\beta_B}{\nu_B}.
}
\tag{163.1}
$$

等价地，

$$
\boxed{
\nu_AT_A=\nu_BT_B.
}
\tag{163.2}
$$

### 证明

因为 \(\sin^2\theta>0\)，零热流等价于 \(p_A=p_B\)。

函数 \(x\mapsto(1+e^x)^{-1}\) 严格单调，故

$$
\beta_A\epsilon_A=\beta_B\epsilon_B.
$$

再使用

$$
\nu_A\epsilon_A=\nu_B\epsilon_B=\mathcal E>0,
$$

得到式（163.1），进而得到式（163.2）。∎

### 一个明确实例

若

$$
\nu_A=1,
\qquad
\nu_B=\frac12,
$$

选择共振探针

$$
\epsilon_A=\epsilon,
\qquad
\epsilon_B=2\epsilon.
$$

那么平衡要求

$$
\boxed{T_B=2T_A.}
\tag{163.3}
$$

这不表示任何慢钟都必然更热。它表示：**在所指定的静态能量标定与热接触条件下，平衡局部温度必须这样变化。**

若后续几何重建得到静态度量

$$
ds^2=-\nu(x)^2c^2dt^2+h_{ab}dx^adx^b,
$$

式（163.2）便成为标准 Tolman–Ehrenfest 关系

$$
T(x)\sqrt{-g_{tt}(x)}/c=\text{常数}.
$$

该关系在引力热平衡研究中已有成熟基础；本节给出的是它的有限量子接触实现。([arXiv][3])

---

## 定理 163.2　连通接触网络的共同平衡

设观察者构成连通图，每条边都具有经过认证的非零共振接触。各边测试使用独立制备的相应局部 Gibbs 态。

若每条边均无净能量交换，则存在共同 \(b>0\)，使

$$
\boxed{
\beta_i=b\nu_i
\qquad\forall i.
}
\tag{163.4}
$$

于是

$$
\boxed{
\bigotimes_i\gamma_i(\beta_i)
=
\frac{e^{-bH_0}}{\operatorname{Tr}e^{-bH_0}}.
}
\tag{163.5}
$$

### 证明

由定理 163.1，每条边两端的 \(\beta_i/\nu_i\) 相同。连通性使该比值在全部节点相同。

由于不同节点的 \(G_i\) 可交换，指数分解直接给出式（163.5）。∎

### 两个不能省略的边界

**零热流不一定是平衡证据。**若接触关闭、没有共振或相关模式根本不可访问，任意温度也可以没有热流。

**平衡态存在不等于已经证明热化。**任何与 \(H_0\) 可交换的操作都保持其各能量扇区的总概率；有限闭合系统不能因此把任意初态变成同一个固定温度。

热化需要明确的环境、混合性或近似极限。新辅助系统可以预先包含在完整量子模型中，但不能无成本、无限次地重新提供。

---

# 164．局部温度相同，隐藏关联仍可产生相反热流

上一节对初始独立性作了明确要求。现在证明它不是技术装饰。

## 定理 164.1　有初始关联时的能量—信息恒等式

设初态 \(\rho_{AB}\) 的两个边缘分别为

$$
\rho_A=\gamma_A(\beta_A),
\qquad
\rho_B=\gamma_B(\beta_B),
$$

但不要求联合态为乘积。

对任意联合酉演化，记末态为 \(\rho'_{AB}\)，则

$$
\boxed{
\begin{aligned}
\beta_A\Delta E_A+\beta_B\Delta E_B
={}&D(\rho_A'\|\gamma_A)
+D(\rho_B'\|\gamma_B)\\
&+I(A:B)_{\rho'}-I(A:B)_\rho.
\end{aligned}
}
\tag{164.1}
$$

这里

$$
D(\rho\|\sigma)
=
\operatorname{Tr}\rho(\log\rho-\log\sigma).
$$

### 证明

由 Gibbs 形式，

$$
D(\rho_i'\|\gamma_i)
=
-S(\rho_i')
+\beta_iE_i'
+\log Z_i.
$$

又因

$$
S(\gamma_i)=\beta_iE_i+\log Z_i,
$$

所以

$$
D(\rho_i'\|\gamma_i)
=
\beta_i\Delta E_i-\Delta S_i.
$$

两式相加，并用联合酉演化保持总熵：

$$
\Delta S_A+\Delta S_B=\Delta I(A:B),
$$

即得结论。∎

若同时保持 \(H_0\)，则

$$
\boxed{
(b_B-b_A)Q_{A\to B}
=
D(\rho_A'\|\gamma_A)
+D(\rho_B'\|\gamma_B)
+\Delta I(A:B).
}
\tag{164.2}
$$

初始无关联时，右侧非负，从而能量按共同标定下的热力学方向传递。

有初始关联时，\(\Delta I\) 可以为负。关联变化参与能量交换的约束；不能继续只看两个温度。相关量子系统中对热流方向的控制已有实验研究。([Nature][4])

---

## 定理 164.2　相同热边缘的有限 carry 见证

取相同局部探针，激发概率

$$
p=\frac13,
$$

并令

$$
\gamma=\operatorname{diag}\left(\frac23,\frac13\right).
$$

定义

$$
\boxed{
\rho_\pm
=
\gamma\otimes\gamma
\pm
\frac i9
\left(
|10\rangle\langle01|
-
|01\rangle\langle10|
\right).
}
\tag{164.3}
$$

则：

1. \(\rho_\pm\) 均为严格正的密度矩阵；
2. 两侧边缘均为 \(\gamma\)；
3. 对同一个 \(U_{\pi/4}\)，末态 \(B\) 的激发概率分别为

   $$
   \boxed{
   p_B^{(+)}=\frac49,
   \qquad
   p_B^{(-)}=\frac29.
   }
   \tag{164.4}
   $$

### 证明

两个态的本征值均为

$$
\frac49,\quad\frac13,\quad\frac19,\quad\frac19.
$$

交叉项对任一侧取偏迹均为零，因此边缘相同。

在单激发子空间中直接实施

$$
U_{\pi/4}
=
\frac1{\sqrt2}(I-iL),
$$

得到式（164.4）。∎

### 项目解释

若当前 CUT 只保存

$$
q(\rho_{AB})=(\rho_A,\rho_B),
$$

它把 \(\rho_+\) 与 \(\rho_-\) 合并；后续能量读数却将二者分开。

因此，这构成项目意义下的明确 carry witness。不能给“局部温度对”直接配置一个覆盖全部相关量子输入的自治热流规则。

---

# 165．热态与时钟是否共享一个生成元，可以直接检验

温度不能只靠一个标签定义。对于多个能级，必须检查全部能级概率及相干结构是否与已标定 Hamiltonian 相容。

## 定义 165.1　热—钟相容性残差

设第 \(i\) 个探针的实际状态满秩：

$$
\rho_i>0.
$$

其共同时间生成元 \(G_i\) 已由独立动力学实验确定。

定义对数态算子

$$
K_i=-\log\rho_i.
$$

对任意算子 \(A\)，记去迹部分

$$
A^\circ=A-\frac{\operatorname{Tr}A}{d_i}I.
$$

定义

$$
\boxed{
\mathcal E(b)
=
\sum_i
\|K_i^\circ-bG_i^\circ\|_{\mathrm{HS}}^2.
}
\tag{165.1}
$$

---

## 定理 165.1　共同 Gibbs 标定的有限判据

设至少一个 \(G_i\) 非标量。定义

$$
\boxed{
b_*=
\frac{
\sum_i\operatorname{Tr}(G_i^\circ K_i^\circ)
}{
\sum_i\|G_i^\circ\|_{\mathrm{HS}}^2
}.
}
\tag{165.2}
$$

则 \(b_*\) 是式（165.1）在实数上的唯一极小点。

若 \(b_*>0\)，则

$$
\boxed{
\mathcal E(b_*)=0
\iff
\rho_i=
\frac{e^{-b_*G_i}}{\operatorname{Tr}e^{-b_*G_i}}
\quad\forall i.
}
\tag{165.3}
$$

### 证明

展开式（165.1），它是严格凸的实二次函数。求导得到式（165.2）。

残差为零等价于

$$
K_i=b_*G_i+a_iI.
$$

取指数并使用 \(\operatorname{Tr}\rho_i=1\)，得到式（165.3）。反向直接成立。∎

这项检验不能靠事后重定义 \(G_i\) 来通过。**若动力学生成元和温度生成元都任由我们修改，所谓相容性就失去了可证伪内容。**

---

## 定理 165.2　满秩裕量控制热态反演稳定性

若

$$
\rho,\sigma\ge mI,
\qquad m>0,
$$

则

$$
\boxed{
\|\log\rho-\log\sigma\|_{\mathrm{op}}
\le
\frac1m\|\rho-\sigma\|_{\mathrm{op}}.
}
\tag{165.4}
$$

### 证明

使用积分表示

$$
\log\rho-\log\sigma
=
\int_0^\infty
\left[
(\sigma+tI)^{-1}-(\rho+tI)^{-1}
\right]dt.
$$

由预解式恒等式，被积算子范数至多为

$$
\frac{\|\rho-\sigma\|}{(m+t)^2}.
$$

积分得到结论。∎

低占据概率可能使精确温度识别非常敏感。这里再次需要区分项目中的精确可识别、条件良好的识别与物理可实现识别。

另外，若探针始终强耦合于环境，其边缘平衡态一般不等于裸 Hamiltonian 的 Gibbs 态。此时应先处理相互作用及有效 Hamiltonian，而不能把式（165.1）的失配立即归咎于几何。([arXiv][5])

---

# 166．多个钟速分支的热态平均，一般不是单一热态

这一结果把本轮重新接回此前的量子结构涨落。

## 定义 166.1　三能级热探针

取

$$
h=\epsilon\operatorname{diag}(0,1,2),
\qquad \epsilon>0.
$$

设结构具有若干钟速分支 \(\nu_a>0\)，权重 \(w_a>0\)，且

$$
\sum_aw_a=1.
$$

在每个分支中，探针相对于同一个共同逆温度 \(b>0\) 准备为

$$
\gamma_a
=
\frac{e^{-b\nu_ah}}{Z_a}.
$$

忽略分支标签后，

$$
\boxed{
\overline\rho=\sum_aw_a\gamma_a.
}
\tag{166.1}
$$

该定义明确指定了一种分支条件制备。它不假定任意量子涨落都会自动产生这样的平衡混合。

令

$$
x_a=e^{-b\nu_a\epsilon},
\qquad
A_a=\frac{w_a}{1+x_a+x_a^2}.
$$

则三能级概率为

$$
p_k=\sum_aA_ax_a^k,
\qquad k=0,1,2.
$$

---

## 定理 166.1　单一温度的正性刚性

有

$$
\boxed{
p_0p_2-p_1^2
=
\frac12
\sum_{a,b}A_aA_b(x_a-x_b)^2
\ge0.
}
\tag{166.2}
$$

等号成立，当且仅当所有实际占据分支的 \(\nu_a\) 相同。

而任何单一温度下的 \(h\)-Gibbs 态都满足

$$
p_0p_2=p_1^2.
$$

因此，不同钟速分支的非平凡混合不能精确表示为某个单一温度的同一探针 Gibbs 态。

### 证明

展开：

$$
\begin{aligned}
p_0p_2-p_1^2
&=
\sum_{a,b}A_aA_b(x_b^2-x_ax_b)\\
&=
\frac12\sum_{a,b}A_aA_b(x_a-x_b)^2.
\end{aligned}
$$

所有权重为正，故等号要求全部 \(x_a\) 相同。由于 \(b\epsilon>0\)，这等价于全部 \(\nu_a\) 相同。

单一 Gibbs 态的三个概率成等比数列，所以行列式为零。∎

---

## 例 166.1　一个精确可检验的热残差

取两个等权分支，使

$$
x_1=\frac12,
\qquad
x_2=\frac14.
$$

则

$$
\boxed{
(p_0,p_1,p_2)
=
\left(
\frac23,\frac5{21},\frac2{21}
\right),
}
\tag{166.3}
$$

并且

$$
\boxed{
p_0p_2-p_1^2=\frac1{147}>0.
}
\tag{166.4}
$$

两个相邻跃迁给出的概率比为

$$
\frac{p_0}{p_1}=\frac{14}{5},
\qquad
\frac{p_1}{p_2}=\frac52,
$$

无法由同一个逆温度解释。

### 定量推论

对任意单一 Gibbs 概率向量 \(q\)，

$$
\boxed{
D_{\mathrm{TV}}(p,q)
\ge
\frac{p_0p_2-p_1^2}{4}.
}
\tag{166.5}
$$

证明只需使用

$$
|\Delta(p)-\Delta(q)|
\le4D_{\mathrm{TV}}(p,q),
\qquad
\Delta(q)=0.
$$

本例因此具有下界 \(1/588\)。

**二能级探针通常只能给出一个概率比，容易被某个有效温度拟合；第三个等间隔能级提供了真正的内部一致性检验。**

但这个残差仍不独自证明结构具有量子相干。经典随机钟速、未完成热化或未建模相互作用也可能产生失配；必须用更强协议区分。

---

# 167．热流应响应红移后的温度，而不是任意局部温度梯度

定义

$$
\boxed{
\Theta_i=\nu_iT_i.
}
\tag{167.1}
$$

这是第 163 节中在平衡时共同的量。

对一个共振能量 \(\mathcal E\)，激发概率可以写成

$$
p_i=
\frac1{1+\exp[\mathcal E/(k_B\Theta_i)]}.
$$

---

## 定理 167.1　近共同平衡的热流具有正导通系数

在

$$
\Theta_i=\Theta_0+\delta\Theta_i
$$

附近，单次接触的共同能量转移满足

$$
\boxed{
Q_{i\to j}
=
L_{ij}
(\delta\Theta_i-\delta\Theta_j)
+
O(\delta\Theta^2),
}
\tag{167.2}
$$

其中

$$
\boxed{
L_{ij}
=
\frac{\mathcal E^2\sin^2\theta}
{k_B\Theta_0^2}
p_0(1-p_0)>0.
}
\tag{167.3}
$$

### 证明

对

$$
p(\Theta)=\frac1{1+e^{\mathcal E/(k_B\Theta)}}
$$

求导，得到

$$
p'(\Theta)
=
\frac{\mathcal E}{k_B\Theta^2}p(1-p).
$$

代入式（162.5）的一阶展开。∎

这给出一个具体方向：近共同平衡时，流动由 \(\Theta_i-\Theta_j\) 驱动，而不是仅由 \(T_i-T_j\) 驱动。

---

## 假设 167.1　局部平衡与因果松弛扩展

为了建立连续宏观方程，另外选择一维静态背景，并令

$$
\vartheta(x,t)=\nu(x)T(x,t)-\Theta_0.
$$

取正系数

$$
\mathcal C(x)>0,\qquad
\lambda(x)>0,\qquad
\tau(x)>0,
$$

并定义

$$
\boxed{
\mathcal C\,\partial_t\vartheta+\partial_xJ=0,
}
\tag{167.4}
$$

$$
\boxed{
\tau\,\partial_tJ+J
=
-\lambda\,\partial_x\vartheta.
}
\tag{167.5}
$$

这里 \(\mathcal C\) 是共同参照能量对 \(\Theta\) 的局部容量系数，\(J\) 是该能量的流量。

式（167.4）—（167.5）是新增的局部平衡与松弛模型，不声称已经由单次碰撞公式无条件推出。相对论热传导中，温度梯度、观察者加速度和松弛项确实需要共同处理。([APS Journals][6])

---

## 定理 167.2　稳定泛函与因果条件相互独立

对适当无通量边界，定义

$$
\mathcal L
=
\frac12\int
\left[
\mathcal C\,\vartheta^2
+
\frac{\tau}{\lambda}J^2
\right]dx.
$$

则

$$
\boxed{
\frac{d\mathcal L}{dt}
=
-\int\frac{J^2}{\lambda}\,dx\le0.
}
\tag{167.6}
$$

其局部特征速度为

$$
\boxed{
v_{\mathrm{th}}^2
=
\frac{\lambda}{\mathcal C\tau}.
}
\tag{167.7}
$$

### 证明

分别以 \(\vartheta\) 和 \(J/\lambda\) 乘两式，积分。由分部积分，交叉项抵消，得到式（167.6）。

主符号矩阵为

$$
\begin{pmatrix}
-\omega\mathcal C&k\\
k&-\omega\tau/\lambda
\end{pmatrix}.
$$

令行列式为零即得式（167.7）。∎

若共同静态度量为

$$
ds^2=-\nu(x)^2c^2dt^2+a(x)^2dx^2,
$$

要使热扰动不超出其局部信号锥，至少需要

$$
\boxed{
\frac{\lambda}{\mathcal C\tau}
\le
\frac{c^2\nu^2}{a^2}.
}
\tag{167.8}
$$

即

$$
\boxed{
\tau\ge
\frac{\lambda a^2}{\mathcal Cc^2\nu^2}.
}
\tag{167.9}
$$

**正导热系数和单调稳定泛函，不会自动保证共同因果性。**

此外，

$$
\partial_x(\nu T)
=
\nu\left(
\partial_xT+T\partial_x\log\nu
\right).
$$

因此零流条件自然包含一个与钟速梯度相关的补偿项。把它删掉，再要求所有非均匀平衡温度都产生热流，会与第 163 节的能量交换定理冲突。

---

# 168．协变平衡对时间方向施加什么约束？

现在进入一个明确的几何检验层。

## 假设 168.1　局部热分布与无源测地输运

采用前文已经重建的洛伦兹几何，暂取 \(c=k_B=1\)。

令 \(u^a\) 是热浴的单位未来四速度，并定义逆温度向量

$$
\boxed{
\mathcal B^a=\frac{u^a}{T}.
}
\tag{168.1}
$$

考虑无外场、无化学势梯度的稀薄分布

$$
\boxed{
f(x,p)
=
\exp\!\left[\alpha+\mathcal B_a(x)p^a\right],
}
\tag{168.2}
$$

其中 \(\alpha\) 为常数，且采用 \((-+++)\) 符号，所以未来动量满足 \(\mathcal B_ap^a<0\)。

假设碰撞项在这个局部平衡形式上消失。要成为完整传播解，还需要满足无碰撞 Liouville 方程。

---

## 定理 168.1　热形分布的传播条件

沿测地流，

$$
\boxed{
X_g\log f
=
p^ap^b\nabla_{(a}\mathcal B_{b)}.
}
\tag{168.3}
$$

### 证明

对 \(\mathcal B_ap^a\) 求沿轨道导数。动量的协变测地导数为零，因此只剩

$$
p^ap^b\nabla_a\mathcal B_b.
$$

对称乘积 \(p^ap^b\) 消去反对称部分。∎

---

## 定理 168.2　有质量与无质量探针施加不同的平衡条件

若式（168.3）对每点的全部允许动量都为零，则：

对某个固定非零质量 \(m>0\) 的全部未来动量，

$$
\boxed{
\nabla_{(a}\mathcal B_{b)}=0.
}
\tag{168.4}
$$

对全部未来无质量动量，

$$
\boxed{
\nabla_{(a}\mathcal B_{b)}
=
\varphi(x)g_{ab}
}
\tag{168.5}
$$

其中 \(\varphi\) 为某个标量函数。

### 证明

记

$$
S_{ab}=\nabla_{(a}\mathcal B_{b)}.
$$

在局部正交标架中，无质量动量可写为

$$
p=E(1,n),\qquad |n|=1.
$$

条件为

$$
S_{00}+2S_{0i}n_i+S_{ij}n_in_j=0.
$$

比较 \(n\) 与 \(-n\)，得到 \(S_{0i}=0\)。继而球面上的二次型必须为常数：

$$
S_{ij}=-S_{00}\delta_{ij}.
$$

因此 \(S=\varphi g\)。

对有质量动量，先取静止动量 \(p=(m,0)\)，得到 \(S_{00}=0\)。

再取

$$
p=(\sqrt{m^2+r^2},rn)
$$

并比较 \(n,-n\)，得到 \(S_{0i}=0\)。最后得到 \(S_{ij}=0\)。∎

式（168.4）表示 \(\mathcal B\) 为 Killing 向量；式（168.5）表示它只需为共形 Killing 向量。相对论平衡及无质量情形的这种差别已有严格动力学研究。([arXiv][7])

### 对本理论的意义

**只用无质量辐射检验热形传播，约束的主要是共形因果结构。加入有质量钟与物质，会施加更强的尺度和时间对称性约束。**

这与前文“光锥确定共形结构，钟补足尺度”的重建方式相呼应，但两者仍是各自有假设的定理，不能仅凭相似性合并。

---

# 169．静态红移与膨胀冷却，不是同一个“时间吞噬”

## 命题 169.1　静态共同平衡

设

$$
ds^2=-\nu(x)^2dt^2+h_{ij}(x)dx^idx^j,
$$

且 \(K=\partial_t\) 为时间方向。

取

$$
\mathcal B=bK,
\qquad b>0.
$$

则

$$
u=\frac K\nu,
$$

由式（168.1）得到

$$
\boxed{
T(x)=\frac1{b\nu(x)}.
}
\tag{169.1}
$$

因此

$$
\nu(x)T(x)=\frac1b.
$$

### 证明

比较

$$
\frac{u}{T}=bK=b\nu u.
$$

∎

同一个几何还给出沿 null 测地线守恒的参照能量

$$
E_K=-K_ap^a,
$$

而静止观察者读到

$$
E_{\mathrm{loc}}=-u_ap^a=\frac{E_K}{\nu}.
$$

于是

$$
\boxed{
\nu_AE_A=\nu_BE_B.
}
\tag{169.2}
$$

这与第 162 节的有限共振条件具有同一个形式。

在这里，几何传播与有限能量交换可以被要求彼此相容，而不是分别指定两套无关的“红移”。

---

## 命题 169.2　膨胀中的无质量热形传播

考虑共形平直度量

$$
ds^2=a(\eta)^2
\left(-d\eta^2+d\mathbf x^2\right).
$$

取

$$
\mathcal B=b\,\partial_\eta.
$$

则

$$
\mathcal L_{\mathcal B}g
=
2b\frac{a'}a\,g,
$$

所以 \(\mathcal B\) 为共形 Killing 向量。

共动观察者

$$
u=a^{-1}\partial_\eta
$$

读取的温度为

$$
\boxed{
T(\eta)=\frac1{ba(\eta)}.
}
\tag{169.3}
$$

该分布可以满足无质量测地输运的平衡形式；若 \(a'\ne0\)，同一个 \(\mathcal B\) 一般不能满足有质量物质所要求的 Killing 条件。

### 证明

对 \(g=a^2\eta_{\mu\nu}\) 作 Lie 导数即可得到第一式。

再比较 \(u/T=b\partial_\eta\)，得到式（169.3）。其余应用定理 168.2。∎

### 三项区分

静态 Tolman 梯度是在共同静态平衡中，不同位置的钟速与温度相互补偿。

膨胀中的无质量冷却，是分布沿动态几何输运时仍保持某种局部热形。

霍金辐射还需要特定量子场态、频率分解与传播映射，不能由上述任一温度缩放式单独推出。

而且，温度梯度也不自动证明曲率非零；加速观察者在平直时空中的平衡描述同样可以具有相应温度梯度。温度关系必须连同热浴四速度一起指定。([APS Journals][8])

---

# 170．热力学重建加入后，理论需要怎样闭合？

本轮得到的主要链条为

$$
\boxed{
\text{已标定的量子钟}
\longrightarrow
\text{共同时间下的能量生成元}
\longrightarrow
\text{可实施的共振交换}.
}
$$

再由独立热制备得到

$$
\boxed{
\text{零热流}
\longrightarrow
\text{共同的 }\beta_i/\nu_i
\longrightarrow
\text{跨观察者温度—时间一致性}.
}
$$

但每一层都具有可以被反例击中的边界：

$$
\boxed{
\text{无热流}
\not\Rightarrow
\text{一定已达到热平衡};
}
$$

$$
\boxed{
\text{局部 Gibbs 边缘}
\not\Rightarrow
\text{联合态具有相同的未来热流};
}
$$

$$
\boxed{
\text{各分支分别为热态}
\not\Rightarrow
\text{平均后仍是单一热态};
}
$$

$$
\boxed{
\text{存在耗散稳定泛函}
\not\Rightarrow
\text{传播满足共同光锥}.
}
$$

---

## 项目中的形式化落点

本次读取固定于提交

```text
930d88b42293cc84edd0ba260843c9dbc9d0810a
```

本轮可以分成以下独立证明义务：

| 项目对象            | 本轮应补入的证明                          |
| --------------- | --------------------------------- |
| **FLOW 的物理实现**  | 交换门酉性、共振条件、共同能量守恒                 |
| **CUT 与 carry** | 相同局部热边缘、不同后续热流的正密度矩阵见证            |
| **ADMIT**       | 初始独立性、允许接触、局部 Gibbs 谱检验、因果松弛界     |
| **条件良好的识别**     | 对数态算子的满秩裕量及热—钟残差                  |
| **几何桥梁**        | 温度向量的 Killing／共形 Killing 条件及共同钟标定 |

仓库的 `GibbsEquality.lean` 已给出有限经典分布中相对熵为零的判据；它不能直接被标记为本文全部量子相对熵命题的现成证明。

`StrongLumpabilityDescent.lean` 可以用于检验指定随机读数是否沿接口下降，但第 164 节说明，若初始相关性没有纳入状态，温度接口一般不满足这一前提。

### 本轮核验

已作精确符号核验的内容包括：

共振交换子的公式、交换门酉性、热输入的能量转移、相同热边缘下的相反能流、三能级混合残差，以及热传导主符号。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_thermal_clock_consistency.py)
[核验结果](sandbox:/mnt/data/observer_formalization/thermal_clock_consistency_checks.json)

**本轮未运行 Lean 编译。**上述核验支持所列有限恒等式与算例，不替代全部分析定理的机器证明，也不证明这些模型已经唯一对应现实引力。

---

# 结论

这轮最重要的推进，是把时间、温度和能量交换放到了同一个可检验结构中：

$$
\boxed{
\text{一只钟怎样积累相位，}
}
$$

$$
\boxed{
\text{一个探针怎样定义能级与温度，}
}
$$

$$
\boxed{
\text{两处系统怎样无外部补偿地交换能量，}
}
$$

不能分别任意指定。

在静态、独立热制备和共振交换条件下，它们共同要求

$$
\boxed{
\nu_iT_i=\text{常数}.
}
$$

但真实量子关联又告诉我们：温度不是完整状态，平衡外观不是完整动力学，热态平均也不一定能压缩成单一几何参数。

因此，当前理论的宏观对象应继续包含

$$
\boxed{
\text{钟标定}
+
\text{能量生成元}
+
\text{热接触实现}
+
\text{关联状态}
+
\text{因果输运}
+
\text{可认证误差}.
}
$$

**物理时空并非由“时间本身变成热”而产生。更严格的说法是：有限量子观察者通过相位、能量交换和热统计，对同一套交互结构进行不同的读取；只有这些读取能在共同条件下相互约束、相互验证，时间与几何才成为可信的物理描述。**

[1]: https://arxiv.org/html/1005.2985v5 "Thermal time and Tolman-Ehrenfest effect:“temperature as the speed of time”"
[2]: https://arxiv.org/abs/1406.3618?utm_source=chatgpt.com "Gibbs-Preserving Maps outperform Thermal Operations in the quantum regime"
[3]: https://arxiv.org/html/1803.04106v1?utm_source=chatgpt.com "Tolman temperature gradients in a gravitational field"
[4]: https://www.nature.com/articles/s41467-019-10333-7?utm_source=chatgpt.com "Reversing the direction of heat flow using quantum ..."
[5]: https://arxiv.org/html/2311.10427v2?utm_source=chatgpt.com "Structure of the Hamiltonian of mean force"
[6]: https://link.aps.org/doi/10.1103/PhysRevD.105.L081501?utm_source=chatgpt.com "Local temperature in general relativity | Phys. Rev. D"
[7]: https://arxiv.org/abs/1606.06605?utm_source=chatgpt.com "four-temperature, Killing vectors and Lie derivatives"
[8]: https://link.aps.org/doi/10.1103/PhysRevD.98.064001?utm_source=chatgpt.com "Tolman-like temperature gradients in stationary spacetimes"
# 热平衡的组合闭合、静止能量与量子质量一致性

## ——量子观察者—关系时空理论第一百七十一至第一百八十节增订

### 摘要

上一轮建立了钟速、能量交换与局部温度之间的关系，但其中仍有两个不同的缺口：

$$
\boxed{
\text{为什么选择 Gibbs 态作为平衡态，而不是其他稳定分布？}
}
$$

以及：

$$
\boxed{
\text{即使钟频率与热统计已经确定，是否已经确定了观察者的质量与引力响应？}
}
$$

本增订分别处理这两个问题。

第一部分从有限量子系统的可提取功出发，证明：**对任意有限份独立制备都保持不可提取功，是比单份稳定更强的要求；在明确的操作类中，它迫使满秩平衡态具有 Gibbs 形式。**

第二部分证明：**内部钟和归一化热态都不能识别 Hamiltonian 的加性标量，但这个被内部接口忽略的部分，在路径比较、位置耦合和质量响应中可能重新变得可见。**

最后，构造一个具有内部量子质量的弱场运动模型，说明惯性质量与引力质量的相等必须是同一个完整动力学中的算子关系，不能通过分别平均两个质量读数来替代。

完全被动性与 Gibbs 平衡的关系，以及内部能量算子在量子等效原理中的作用，均有既有理论基础。下面给出当前模型中的定义、证明及其与项目接口结构的连接，不将这些一般结论宣称为本会话首次发现。([APS Journals][1])

---

# 171．平衡首先应当通过可实施的能量实验定义

## 假设 171.1　有限系统与循环控制

取有限维 Hilbert 空间 \(\mathcal H\)，Hamiltonian 为

$$
H=H^\dagger,
$$

状态为

$$
\rho>0,\qquad \operatorname{Tr}\rho=1.
$$

本节先采用一个明确的理想化操作类：允许通过循环控制实现任意酉操作 \(U\)，控制开始与结束时，系统 Hamiltonian 都为同一个 \(H\)。

定义从系统中提取的平均功：

$$
\boxed{
W_H(\rho,U)
=
\operatorname{Tr}(H\rho)
-
\operatorname{Tr}(HU\rho U^\dagger).
}
\tag{171.1}
$$

**循环的是控制设定，不要求资源状态 \(\rho\) 在提取后恢复原样。**

如果把系统、控制器、电池和全部记录都要求恢复初态，那么净输出能量当然不能凭空出现。式（171.1）讨论的是系统能量怎样转移给工作装置，而不是一个无源循环。

实际观察者未必能够实现全部酉操作。若操作受局域性、对称性或控制资源限制，则必须改用相应的受限被动性；不同操作类可以产生不同的平衡判据。([arXiv][2])

---

## 定义 171.1　被动态与完全被动态

若对全部允许酉操作，

$$
W_H(\rho,U)\le0,
$$

则称 \(\rho\) 对 \(H\) 被动。

对 \(N\) 份独立制备，令

$$
H^{(N)}
=
\sum_{j=1}^N
I^{\otimes(j-1)}\otimes H\otimes I^{\otimes(N-j)}.
$$

若对每个有限 \(N\)，\(\rho^{\otimes N}\) 都相对于 \(H^{(N)}\) 被动，则称 \(\rho\) 完全被动。

这里的量词是：

$$
\boxed{\forall N\in\mathbb N,\quad N<\infty,}
$$

不是要求某个观察者实际控制一个无限系统。

---

## 定理 171.1　单份被动性的谱判据

\(\rho\) 被动，当且仅当：

$$
[H,\rho]=0,
$$

并且可以在共同本征基中排列为

$$
E_1\le E_2\le\cdots\le E_d,
$$

$$
p_1\ge p_2\ge\cdots\ge p_d,
$$

其中

$$
H=\sum_iE_i|i\rangle\langle i|,
\qquad
\rho=\sum_ip_i|i\rangle\langle i|.
$$

### 证明

若 \(\rho\) 被动，则 \(U=I\) 是能量函数的极小点。对任意 Hermitian \(A\)，考虑 \(U(t)=e^{-itA}\)，在 \(t=0\) 求导，得到

$$
\operatorname{Tr}\bigl(A[H,\rho]\bigr)=0.
$$

因此 \([H,\rho]=0\)。

若存在 \(E_i<E_j\) 但 \(p_i<p_j\)，交换两个本征态会降低平均能量，违反被动性。

反之，对任意酉 \(U\)，输出能量基概率为

$$
q_i=\sum_j|U_{ij}|^2p_j.
$$

矩阵 \((|U_{ij}|^2)\) 双随机，因此

$$
\sum_{i=1}^kq_i\le\sum_{i=1}^kp_i.
$$

分部求和得到

$$
\sum_iE_i(q_i-p_i)
=
\sum_{k=1}^{d-1}
(E_{k+1}-E_k)
\sum_{i=1}^k(p_i-q_i)
\ge0.
$$

故不能降低能量。∎

**单份被动性只要求概率按能量单调排列，还没有要求指数型 Gibbs 比例。**

---

# 172．有限份组合稳定性如何迫使 Gibbs 形式？

## 定理 172.1　满秩完全被动态的有限维刻画

设 \(H\) 非标量，且 \(\rho>0\)。则

$$
\boxed{
\rho\text{ 完全被动}
\iff
\rho=\frac{e^{-\beta H}}{\operatorname{Tr}e^{-\beta H}}
\quad\text{对某个 }\beta\ge0.
}
\tag{172.1}
$$

\(\beta=0\) 对应最大混合态。有限正温度对应 \(\beta>0\)。

这是完全被动性的标准刻画；以下给出一个适合有限维形式化的证明。([arXiv][3])

### 证明

由定理 171.1，可以在共同本征基中写

$$
H=\operatorname{diag}(E_1,\ldots,E_d),
\qquad
\rho=\operatorname{diag}(p_1,\ldots,p_d),
$$

并令

$$
s_i=-\log p_i.
$$

由于 \(\rho>0\)，全部 \(s_i\) 有限。

考虑任意整数向量

$$
z\in\mathbb Z^d,\qquad \sum_i z_i=0.
$$

其正、负部分满足

$$
\sum_i z_i^+=\sum_i z_i^-=N.
$$

它们因此分别描述两个 \(N\) 份系统的积基态：一个含 \(z_i^+\) 份能级 \(i\)，另一个含 \(z_i^-\) 份。

两态的能量差为

$$
E\cdot z,
$$

概率对数差为

$$
-s\cdot z.
$$

若

$$
E\cdot z>0,
\qquad
s\cdot z<0,
$$

则较高能量的积态反而具有较大概率。交换这两个积态可以提取正功，与完全被动性矛盾。

故对全部上述整数向量：

$$
E\cdot z>0\Longrightarrow s\cdot z\ge0.
\tag{172.2}
$$

令

$$
V=\left\{x\in\mathbb R^d:\sum_ix_i=0\right\}.
$$

由有理向量在 \(V\) 中稠密，若某个实向量违反式（172.2），就可以保持两个严格不等式作有理逼近，再乘公共分母得到整数反例。因此：

$$
E\cdot x>0\Longrightarrow s\cdot x\ge0
\qquad(x\in V).
$$

选择 \(u\in V\) 使 \(E\cdot u>0\)。对任意满足 \(E\cdot w=0\) 的 \(w\in V\)，有

$$
E\cdot(u+tw)>0
\qquad\forall t\in\mathbb R.
$$

所以

$$
s\cdot(u+tw)\ge0
\qquad\forall t.
$$

这迫使 \(s\cdot w=0\)。因此 \(s\) 在 \(V\) 上与 \(E\) 成比例：

$$
s|_V=\beta E|_V,
\qquad \beta\ge0.
$$

于是存在常数 \(a\)，使

$$
s_i=\beta E_i+a.
$$

从而

$$
p_i=e^{-a}e^{-\beta E_i},
$$

归一化后得到 Gibbs 形式。

反向，若 \(\rho=e^{-\beta H}/Z\)，则任意有限份满足

$$
\rho^{\otimes N}
=
\frac{e^{-\beta H^{(N)}}}{Z^N}.
$$

概率随总能量单调不增，由定理 171.1，它对全部联合酉操作被动。∎

### 结论

Gibbs 形式可以从以下更深一层要求中推出：

$$
\boxed{
\text{不仅单个观察者不能提取功，}
\quad
\text{任意有限份协作也不能把隐藏的不平衡激活。}
}
$$

但这一结论依赖所允许的联合控制类。它不是“只要某个实验没提取出功，就已经证明状态为 Gibbs 态”。

---

# 173．一个有限反例：单份稳定，联合后却能提取功

## 定义 173.1　三能级资源

取

$$
H=\epsilon\operatorname{diag}(0,2,3),
\qquad
\rho=\operatorname{diag}\left(\frac12,\frac25,\frac1{10}\right),
\qquad \epsilon>0.
$$

该态的概率随能量下降，因此单份被动。

但两份系统中：

$$
|1,1\rangle:
\quad
E=4\epsilon,\qquad p=\frac4{25},
$$

$$
|0,2\rangle:
\quad
E=3\epsilon,\qquad p=\frac1{20}.
$$

---

## 定理 173.1　两份激活的精确功值

交换 \(|1,1\rangle\) 与 \(|0,2\rangle\)，其余基态保持不变，可以提取

$$
\boxed{
W=\frac{11}{100}\epsilon>0.
}
\tag{173.1}
$$

### 证明

交换的能量差为 \(\epsilon\)，高能态与低能态概率之差为

$$
\frac4{25}-\frac1{20}=\frac{11}{100}.
$$

因此平均能量降低式（173.1）。∎

单份能量为

$$
\frac{11}{10}\epsilon.
$$

两份初始能量为 \(11\epsilon/5\)，交换后为 \(209\epsilon/100\)。

**单份没有可提取功，不是一个在任意系统组合下自动保持的性质。**

---

## 有限能量账本

这一例子还可以放入一个明确的三能级能量寄存器 \(B\)：

$$
H_B=\epsilon\operatorname{diag}(0,1,2),
$$

初始状态为 \(|1\rangle_B\)。

在总空间中实施以下两个互不相交的交换：

$$
|1,1;1\rangle\longleftrightarrow|0,2;2\rangle,
$$

$$
|0,2;1\rangle\longleftrightarrow|1,1;0\rangle.
$$

每一对两侧的总能量相同，故该 \(27\) 维置换酉严格保持总能量。

末态能量寄存器概率为

$$
\boxed{
\left(\frac1{20},\frac{79}{100},\frac4{25}\right),
}
\tag{173.2}
$$

其平均能量增加 \(11\epsilon/100\)。

这里没有能量凭空产生；源态发生了改变，寄存器也变得混合并与源相关。**该寄存器的平均能量增量不能未经额外分析全部称为可无损利用的确定性功。**

这一区别正适合项目的闭合要求：源、控制、工作记录和恢复成本不能只保留其中一部分。

---

# 174．共同温度—时间关系也可以从组合被动性推出

## 假设 174.1　独立观察者与共同能量

有有限个观察者探针，其局部 Hamiltonian 为非标量 \(h_i\)，钟速为

$$
d\tau_i=\nu_i\,dt,
\qquad \nu_i>0.
$$

共同参照能量为

$$
H_0=\sum_i\nu_i h_i.
$$

各探针独立制备：

$$
\rho_{\mathrm{tot}}=\bigotimes_i\rho_i,
\qquad \rho_i>0.
$$

---

## 定理 174.1　整体完全被动性确定共同逆温度

若 \(\rho_{\mathrm{tot}}\) 相对于 \(H_0\) 完全被动，则存在同一个 \(\beta\ge0\)，使

$$
\boxed{
\rho_i
=
\frac{e^{-\beta\nu_i h_i}}
{\operatorname{Tr}e^{-\beta\nu_i h_i}}
\qquad\forall i.
}
\tag{174.1}
$$

反向亦成立。

### 证明

由定理 172.1，

$$
\rho_{\mathrm{tot}}
=
\frac{e^{-\beta H_0}}{\operatorname{Tr}e^{-\beta H_0}}.
$$

不同节点算子可交换，因此指数与配分函数都分解。对其余节点取偏迹，得到式（174.1）。

反向，式（174.1）的乘积是 \(H_0\) 的 Gibbs 态，由定理 172.1 完全被动。∎

若把局部逆温度记为

$$
\beta_i=\frac1{k_BT_i},
$$

则有限正温度下

$$
\beta_i=\beta\nu_i,
$$

即

$$
\boxed{
\nu_iT_i=\frac1{k_B\beta}.
}
\tag{174.2}
$$

### 与上一轮的区别

上一轮先给定局部 Gibbs 制备，再通过共振热交换推导零热流条件。

本轮使用更强的组合条件，同时约束：

$$
\boxed{
\text{平衡态为何为 Gibbs 形式}
+
\text{各处温度为何使用同一个红移标定}.
}
$$

如果总 Hamiltonian 还含有相互作用 \(V\)，则整体平衡态一般是

$$
\frac{e^{-\beta(H_0+V)}}{Z},
$$

而不再是上述局部乘积。不能保留相互作用，却继续无条件使用乘积热态定理。

---

# 175．内部钟和热统计看不见完整的静止能量

现在进入通向质量与引力的关键缺口。

## 定义 175.1　具有不同静止基准能量的模型

固定一个非平凡内部 Hamiltonian \(h\)，定义

$$
\boxed{
H_e=eI+h,
}
\tag{175.1}
$$

其中 \(e\) 为实数，取值范围使 \(H_e>0\)。

对已经标定的单条历史，设其固有时间为 \(\tau\)。

---

## 定理 175.1　内部接口不能识别 \(e\)

对任意 \(e,e'\)，以下内部读数完全相同。

量子态演化：

$$
\boxed{
e^{-iH_e\tau/\hbar}\rho e^{iH_e\tau/\hbar}
=
e^{-ih\tau/\hbar}\rho e^{ih\tau/\hbar}.
}
\tag{175.2}
$$

归一化 Gibbs 态：

$$
\boxed{
\frac{e^{-\beta H_e}}{\operatorname{Tr}e^{-\beta H_e}}
=
\frac{e^{-\beta h}}{\operatorname{Tr}e^{-\beta h}}.
}
\tag{175.3}
$$

循环控制的可提取功：

$$
\boxed{
W_{H_e}(\rho,U)=W_h(\rho,U).
}
\tag{175.4}
$$

### 证明

式（175.2）中的 \(e\) 仅产生相消的整体相位。

式（175.3）中的 \(e^{-\beta e}\) 在分子、分母中相消。

式（175.4）中，标量项贡献

$$
e\operatorname{Tr}\rho-e\operatorname{Tr}(U\rho U^\dagger)=0.
$$

∎

### 结论

即使一个观察者精确知道：

$$
\text{全部内部能级差},
$$

$$
\text{全部内部相位演化},
$$

$$
\text{全部归一化热态},
$$

也没有因此唯一确定 \(e\)。

所以：

$$
\boxed{
\text{内部时间与热力学完全已知}
\not\Rightarrow
\text{完整静止能量已经已知}.
}
$$

如果质量与完整静止能量有关，这就是必须补足的观察接口，而不是可以用命名忽略的常数。

---

# 176．在内部看不见的标量，可以成为路径间的相对相位

## 假设 176.1　已实现的双路径控制

取两个路径或配置分支 \(L,R\)，其固有时间分别为

$$
\tau_L,\qquad\tau_R.
$$

实际联合操作为

$$
U_e
=
|L\rangle\langle L|\otimes e^{-iH_e\tau_L/\hbar}
+
|R\rangle\langle R|\otimes e^{-iH_e\tau_R/\hbar}.
\tag{176.1}
$$

这是一项具体的物理实现假设，不能仅从一个“不计整体相位”的黑箱通道自动构造出来。相干控制对实现信息的依赖，是量子控制理论中的已知限制。([arXiv][4])

---

## 定理 176.1　静止基准能量的关系可见性

初始路径为 \(|+\rangle\)，内部态为 \(\rho\)。定义

$$
\Delta\tau=\tau_L-\tau_R.
$$

路径干涉系数为

$$
\boxed{
\gamma_e
=
e^{-ie\Delta\tau/\hbar}
\operatorname{Tr}\!\left(
\rho e^{-ih\Delta\tau/\hbar}
\right).
}
\tag{176.2}
$$

因此，不同 \(e\) 一般可以由路径干涉区分。

### 证明

计算两个条件演化的相对酉算子：

$$
e^{iH_e\tau_R/\hbar}e^{-iH_e\tau_L/\hbar}
=
e^{-ie\Delta\tau/\hbar}
e^{-ih\Delta\tau/\hbar}.
$$

再对内部态取期望即可。∎

---

## 例 176.1　相同内部接口，正交的路径输出

取

$$
h=\epsilon|1\rangle\langle1|,
$$

内部初态为 \(|0\rangle\)，并比较

$$
e_1=\epsilon,\qquad e_2=2\epsilon.
$$

选择

$$
\Delta\tau=\frac{\pi\hbar}{\epsilon}.
$$

则

$$
\gamma_{e_1}=-1,
\qquad
\gamma_{e_2}=1.
$$

两个路径输出为正交的 \(|-\rangle\) 与 \(|+\rangle\)。

因此，若 CUT 只保存第 175 节的内部通道与热态，它无法决定这个后续路径实验。

这是一个明确的目标残差：

$$
\boxed{
q_{\mathrm{internal}}(e_1)=q_{\mathrm{internal}}(e_2),
\qquad
T_{\mathrm{path}}(e_1)\ne T_{\mathrm{path}}(e_2).
}
\tag{176.3}
$$

项目的 `exact_descent_has_no_carry` 因而禁止我们在没有补充实现信息时，宣称路径目标已经沿内部接口下降。

### 为什么这不是“绝对整体相位可观测”？

若给**完整联合 Hamiltonian**加上同一个常数 \(aI\)，它仍不可观测。

这里改变的是

$$
e\bigl(
\nu_L|L\rangle\langle L|
+
\nu_R|R\rangle\langle R|
\bigr)\otimes I,
$$

当两路径钟速不同，它不是整个联合系统的标量。

另外，若只是把内部能量零点改为 \(h\mapsto h+aI\)，就必须同时令 \(e\mapsto e-a\)，保持完整 \(H_e\) 不变。**真正可检验的是完整耦合，不是任意选择的能量零点。**

---

# 177．共同钟标定如何约束引力响应与相互作用能量？

## 假设 177.1　完整静止能量的共同耦合

令

$$
H_{\mathrm{rest}}=eI+h>0.
$$

设已标定钟速为正函数 \(\nu(x)\)，并选择位置相关能量

$$
\boxed{
H_{\mathrm{int}}(x)=\nu(x)H_{\mathrm{rest}}.
}
\tag{177.1}
$$

注意：这是比“内部能级差被红移”更强的条件，因为它还规定了标量静止部分怎样耦合。

## 定理 177.1　位置耦合的力算子

与位置参数共轭的力为

$$
\boxed{
\widehat F_x
=
-\partial_xH_{\mathrm{int}}(x)
=
-\nu'(x)H_{\mathrm{rest}}.
}
\tag{177.2}
$$

若采用弱场标定

$$
\nu(x)=1+\frac{\Phi(x)}{c^2},
$$

则

$$
\boxed{
\widehat F_x
=
-\widehat M_g\,\Phi'(x),
\qquad
\widehat M_g=\frac{H_{\mathrm{rest}}}{c^2}.
}
\tag{177.3}
$$

### 证明

对式（177.1）求导。若把 \(x\) 提升为位置算子 \(X\)，并引入正则动量 \(P\)，同一结果由 \(\dot P=(i/\hbar)[H,P]\) 得到。∎

这里得到的是当前耦合模型中的**被动引力响应质量**。它尚未证明惯性质量必然相等，也没有证明该系统产生的引力场满足 Einstein 方程。

内部能量、惯性和引力响应必须在算子层面比较，而非只比较几个经典数值。([Nature][5])

---

## 定理 177.2　复合观察者的统一钟律迫使相互作用能量共同缩放

设参考条件下复合系统的 Hamiltonian 为

$$
H_1=H_A+H_B+V,
$$

其中 \(V\) 非标量。

考虑候选耦合

$$
H_\nu
=
\nu(H_A+H_B)+f(\nu)V+a(\nu)I.
$$

若对全部复合系统初态，\(H_\nu\) 的动力学都只是 \(H_1\) 的统一时间缩放，则

$$
\boxed{f(\nu)=\nu.}
\tag{177.4}
$$

### 证明

对全部密度矩阵具有相同共轭演化，要求生成元之差为标量：

$$
H_\nu-\nu H_1=bI.
$$

所以

$$
[f(\nu)-\nu]V+[a(\nu)-b]I=0.
$$

由于 \(V\) 非标量，只能有 \(f(\nu)=\nu\)。∎

这说明：如果一个绑定系统整体也被允许作为观察者或钟，那么“只让各部分自由能量红移，却让绑定能量不红移”一般不相容。

但结论仍然依赖“复合系统也满足统一钟律”的全称条件。不能只验证某一个跃迁后，就认为全部相互作用都已被证明普适。

---

# 178．平衡热统计、力响应与可识别性由同一个能谱约束

## 定义 178.1　共同逆温度下的平衡族

固定 \(\beta>0\)，令

$$
\rho_\nu
=
\frac{e^{-\beta\nu H_{\mathrm{rest}}}}
{Z(\nu)},
$$

并定义自由能

$$
\boxed{
\mathcal F(\nu)
=
-\frac1\beta\log Z(\nu).
}
\tag{178.1}
$$

这里 \(\nu\) 是跨不同已平衡制备条件比较的参数。

---

## 定理 178.1　自由能—涨落恒等式

有

$$
\boxed{
\mathcal F'(\nu)
=
\langle H_{\mathrm{rest}}\rangle_\nu,
}
\tag{178.2}
$$

$$
\boxed{
\mathcal F''(\nu)
=
-\beta\operatorname{Var}_{\rho_\nu}(H_{\mathrm{rest}})
\le0.
}
\tag{178.3}
$$

因此，平衡平均力为

$$
\boxed{
\overline F_x
=
-\nu'(x)\langle H_{\mathrm{rest}}\rangle_\nu.
}
\tag{178.4}
$$

### 证明

在 \(H_{\mathrm{rest}}\) 的本征基中，

$$
Z'(\nu)
=
-\beta Z(\nu)\langle H_{\mathrm{rest}}\rangle_\nu.
$$

对 \(\log Z\) 求导得到式（178.2）。

再对平均能量求导，得到负的 \(\beta\) 倍方差，故式（178.3）成立。式（178.4）由力算子取期望得到。∎

若 \(\nu=\nu(x)\)，则

$$
\boxed{
\frac{d^2\mathcal F}{dx^2}
=
\langle H_{\mathrm{rest}}\rangle_\nu\,\nu''
-
\beta\operatorname{Var}(H_{\mathrm{rest}})(\nu')^2.
}
\tag{178.5}
$$

因此，局部力响应同时依赖平均能量与能量涨落，不能仅由一个“温度值”决定。

---

## 定理 178.2　热态参数信息与力响应的联系

关于参数 \(\nu\)，该 Gibbs 族的量子 Fisher 信息为

$$
\boxed{
J_\nu
=
\beta^2\operatorname{Var}_{\rho_\nu}(H_{\mathrm{rest}})
=
-\beta\mathcal F''(\nu).
}
\tag{178.6}
$$

### 证明

全部 \(\rho_\nu\) 在同一能量基底中对角。其概率满足

$$
\partial_\nu\log p_i
=
-\beta(E_i-\langle E\rangle_\nu).
$$

因此经典 Fisher 信息为 \(\beta^2\operatorname{Var}(E)\)。能量测量达到该可交换态族的量子 Fisher 信息。∎

这种 Gibbs 参数估计与 Hamiltonian 不确定性的联系，是量子热计量中的标准结构。这里因为参数只缩放同一个 Hamiltonian，结果恰好化为普通方差；非交换参数模型需要更一般的公式。([APS Journals][6])

### 两个不同的“时间信息”

尽管 \(J_\nu\) 可以非零，固定 \(\nu\) 后，

$$
e^{-it\nu H_{\mathrm{rest}}/\hbar}
\rho_\nu
e^{it\nu H_{\mathrm{rest}}/\hbar}
=
\rho_\nu.
$$

所以该孤立 Gibbs 态本身不通过状态变化记录经过了多少时间。

$$
\boxed{
\text{不同平衡制备能区分钟速参数}
\ne
\text{同一个平衡态本身会持续走时}.
}
$$

实际钟还需要相干、非平衡准备或与其他系统的关系读数。时间相位资源与工作资源不能被当成同一个量。([APS Journals][7])

此外，式（178.4）是平衡或准静态的平均力。若结构尚未来得及重新平衡，不能直接把 \(\mathcal F\) 当成完整动力 Hamiltonian；记忆、耗散及热交换仍须保留。

---

# 179．惯性与引力相等，必须在同一个量子运动方程中成立

## 假设 179.1　具有内部质量算子的弱场运动

内部空间有限维，位置空间取 \(L^2(\mathbb R)\)。

给定两正定内部算子

$$
M_I>0,\qquad M_G>0,
$$

分别表示惯性质量和引力响应质量。再给定内部静止能量 \(E_R\)。

本节先要求它们两两可交换。

选择有效 Hamiltonian

$$
\boxed{
H
=
E_R+\frac{P^2}{2M_I}+M_G\Phi(X).
}
\tag{179.1}
$$

取光滑、有界的弱势 \(\Phi\)，并在相应共同算子核心上计算。该模型是明确的非相对论弱场实现，不作为完整引力理论。

---

## 定理 179.1　加速度的算子形式

有

$$
\boxed{
\dot X=M_I^{-1}P,
}
\tag{179.2}
$$

$$
\boxed{
\dot P=-M_G\Phi'(X),
}
\tag{179.3}
$$

从而

$$
\boxed{
\ddot X=-M_I^{-1}M_G\Phi'(X).
}
\tag{179.4}
$$

### 证明

使用 \([X,P]=i\hbar I\)，并注意所有内部算子与 \(X,P\) 可交换。

两两可交换假设还给出 \([M_I,H]=0\)，因此对式（179.2）求时间导数得到式（179.4）。∎

---

## 定理 179.2　普适加速度对内部质量的判据

若 \(\Phi'\) 不恒为零，则对全部允许内部态与位置测试态具有

$$
\langle\ddot X\rangle=-\langle\Phi'(X)\rangle
$$

的充要条件是

$$
\boxed{M_G=M_I.}
\tag{179.5}
$$

### 证明

充分性直接来自式（179.4）。

反之，选择一个使 \(\langle\Phi'(X)\rangle\ne0\) 的位置测试态。对任意内部态 \(\sigma\)，要求

$$
\operatorname{Tr}(\sigma M_I^{-1}M_G)=1.
$$

这对全部 \(\sigma\) 成立，只能有

$$
M_I^{-1}M_G=I.
$$

∎

这只是加速度算子形式的普适性，不意味着任意不同质量量子态都具有相同的完整位置分布。量子扩散、初态、路径干涉和相位仍可能依赖质量。([arXiv][8])

---

## 一条充分的能量—质量连接

如果已经独立建立：

$$
M=\frac{H_{\mathrm{rest}}}{c^2},
$$

并采用相对论正能量关系

$$
H_{\mathrm{rel}}(P)
=
\sqrt{c^2P^2+c^4M^2},
$$

那么在有限动量窗口 \(|P|\ll m_{\min}c\) 中，

$$
H_{\mathrm{rel}}
=
Mc^2+\frac{P^2}{2M}
+
O\!\left(\frac{P^4}{m_{\min}^3c^2}\right).
$$

再结合第 177 节对完整静止能量的弱场耦合，就在领先阶得到

$$
M_I=M_G=M.
$$

**这里需要两个物理桥梁同时成立：相对论惯性关系，以及完整静止能量的普适位置耦合。**

热平衡定理本身没有替我们证明它们。量子等效原理正是要求比较这些内部能量算子，而不是仅比较其平均值。([arXiv][9])

---

## 定理 179.3　分别平均质量与逆质量可以制造虚假的等效原理失配

即使完整模型严格满足

$$
M_I=M_G=M,
$$

若把有效 Hamiltonian 错误地替换为

$$
H_{\mathrm{naive}}
=
\text{常数}
+\frac12\langle M^{-1}\rangle P^2
+\langle M\rangle\Phi(X),
$$

它会预测

$$
\ddot X_{\mathrm{naive}}
=
-\langle M^{-1}\rangle\langle M\rangle\Phi'(X).
$$

而完整模型给出

$$
\boxed{\ddot X=-\Phi'(X).}
\tag{179.6}
$$

对等权混合的两个质量 \(m,2m\)，

$$
\boxed{
\langle M^{-1}\rangle\langle M\rangle=\frac98.
}
\tag{179.7}
$$

### 证明

完整模型中是算子乘积

$$
M^{-1}M=I,
$$

而不是两个独立平均值的乘积。

等权混合时，

$$
\langle M\rangle=\frac32m,
\qquad
\langle M^{-1}\rangle=\frac3{4m},
$$

相乘得到 \(9/8\)。∎

### 解释

引力作用会建立质量与动量之间的关联。真实速度读取

$$
\langle M^{-1}P\rangle,
$$

不能始终用

$$
\langle M^{-1}\rangle\langle P\rangle
$$

替代。

因此，一个粗粒化模型显示“质量不同导致不同加速度”，不一定意味着底层理论违反等效原理；也可能只是它删除了动力学必需的关联。

这与本会话反复出现的同一问题一致：

$$
\boxed{
\text{先平均，再计算动力学}
\quad\text{不一定等于}\quad
\text{先计算动力学，再读取平均}.
}
$$

---

# 180．本轮建立的闭合链与形式化边界

本轮把上一轮的热—钟相容性推进成三条可以分别检查的链。

## 第一条：平衡态的组合闭合

$$
\boxed{
\text{循环功的操作定义}
\longrightarrow
\text{单份被动性}
\longrightarrow
\text{任意有限份的完全被动性}
\longrightarrow
\text{Gibbs 形式}.
}
$$

这使 Gibbs 态不再仅作为一个方便选择的分布进入理论，但代价是必须明确操作类和多份独立制备条件。

## 第二条：从内部时间到完整静止能量

$$
\boxed{
\text{内部钟与热接口}
\longrightarrow
H_{\mathrm{rest}}\bmod\mathbb RI,
}
$$

而不是自动得到完整 \(H_{\mathrm{rest}}\)。

路径比较与位置耦合可以进一步读取该接口遗漏的部分：

$$
\boxed{
\text{相干路径实现}
+
\text{共同钟标定}
\longrightarrow
\text{相对静止相位与力响应}.
}
$$

## 第三条：从能量到普适运动

$$
\boxed{
\text{同一个静止能量算子}
+
\text{相对论惯性关系}
+
\text{普适弱场耦合}
\longrightarrow
M_I=M_G.
}
$$

它不是从温度一个量直接推出来的，也不能由分别拟合两个平均质量来替代。

---

## 与项目的具体对应

本轮按提交

```text
37bc70552f22891fea4c4d9d2edbae4dbc86fe68
```

核对了相关结构。

`GibbsEquality.lean` 提供有限经典相对熵等号条件；它可以支撑已对角化概率层的部分证明，但不能直接宣称已经覆盖本文的完全被动性和量子质量命题。

`ExactDescentNoCarry.lean` 则直接对应第 176 节：内部接口合并了两个静止能量模型，但扩大后的路径实验重新区分它们。因此，必须补充接口，而不是声称原来的下降证明仍然成立。

| 项目角色         | 本轮的明确对象                              |
| ------------ | ------------------------------------ |
| **CUT**      | 内部钟通道、归一化热态、循环功、路径相位、受力读数            |
| **FLOW**     | 单份与多份循环控制、具体路径控制、内部—运动联合演化           |
| **ADMIT**    | 满秩、允许操作类、能量账本、共振、弱场与动量窗口             |
| **ANCHOR**   | 实际功记录、能级标定、路径相位和加速度实验                |
| **Residual** | 单份被动性遗漏的组合资源；内部接口遗漏的静止能量；平均质量遗漏的动力关联 |

### 本轮核验

已作精确符号核验的内容包括：

三能级单份被动例子；两份系统的 \(11\epsilon/100\) 能量降低；\(27\) 维能量守恒实现；不同静止能量的正交路径输出；自由能的一阶、二阶导数；平衡参数 Fisher 信息；质量平均产生的 \(9/8\) 伪差异。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_passivity_mass_completion.py)
[核验结果](sandbox:/mnt/data/observer_formalization/passivity_mass_completion_checks.json)

**本轮没有运行 Lean 编译。**上述有限核验不替代一般定理的机器证明，也不验证附加的物理耦合假设就是现实规律。

---

# 结论

本轮最重要的结果，是把三个容易混同的问题分开：

$$
\boxed{
\text{这个状态是不是可组合的热平衡？}
}
$$

$$
\boxed{
\text{观察者的内部时间读取了完整能量的哪一部分？}
}
$$

$$
\boxed{
\text{这份能量怎样同时进入惯性、引力与路径相位？}
}
$$

我们证明了：

**热平衡的完整组合条件可以迫使 Gibbs 形式，但不会自动确定全部静止能量。**

**内部不可见的能量标量，在更大的相干控制与位置耦合实验中可以成为可见区别；因此内部观察接口并不是对所有物理过程都充分。**

**惯性与引力相等必须来自同一个完整动力学中的算子一致性。把不同物理角色分别平均，再把结果拼起来，可能制造并不存在的违反。**

因此，量子观察者理论当前更完整的对象应当是

$$
\boxed{
\text{内部钟}
+
\text{平衡与非平衡资源}
+
\text{完整静止能量}
+
\text{相干路径实现}
+
\text{内部—运动关联}.
}
$$

**观察者不仅通过时间读数认识世界；它自身也是携带静止能量、能够交换功、产生反冲并进入相干路径的物理系统。只有把这些角色放在同一个可形式化的实现中，时间、温度、质量与几何才不会成为彼此独立、事后拼接的解释。**

[1]: https://link.aps.org/doi/10.1103/PhysRevE.91.052133?utm_source=chatgpt.com "Passivity, complete passivity, and virtual temperatures"
[2]: https://arxiv.org/abs/2103.06060?utm_source=chatgpt.com "Characterizing symmetry-protected thermal equilibrium by work extraction"
[3]: https://arxiv.org/html/1412.5485v2 "A short note on passivity, complete passivity and virtual temperatures"
[4]: https://arxiv.org/abs/1309.7976?utm_source=chatgpt.com "Quantum circuits cannot control unknown operations"
[5]: https://www.nature.com/articles/s41567-018-0197-6 "Quantum formulation of the Einstein equivalence principle | Nature Physics"
[6]: https://link.aps.org/doi/10.1103/PhysRevLett.133.040802 "Estimation of Hamiltonian Parameters from Thermal States | Phys. Rev. Lett."
[7]: https://link.aps.org/doi/10.1103/PhysRevLett.129.190502?utm_source=chatgpt.com "Operational Interpretation of Quantum Fisher Information in ..."
[8]: https://arxiv.org/abs/1707.04526?utm_source=chatgpt.com "Equivalence Principle for Quantum Systems: Dephasing and Phase Shift of Free-Falling Particles"
[9]: https://arxiv.org/abs/1502.00971?utm_source=chatgpt.com "Quantum formulation of the Einstein Equivalence Principle"
# 量子质量的不相容性、自由落体参照与潮汐余量

## ——量子观察者—关系时空理论第一百八十一至第一百九十节增订

### 摘要

上一轮把静止能量、惯性质量和引力响应放进同一个模型，但推导加速度时使用了一个重要假设：这些内部算子彼此可交换。

本增订首先移除这一假设，证明：

$$
\boxed{
\text{对所有内部状态成立的普适加速度}
\iff
M_G=M_I,\quad [H_{\mathrm{rest}},M_I]=0
}
$$

其中等价关系限定于下文定义的弱场有效 Hamiltonian。它比“几个质量平均值相同”更强，但仍弱于完整的 Einstein 等效原理。

随后，将自由落体参照变换直接构造为作用于**运动与内部量子态**的联合酉映射。对于相容的质量算子，均匀引力项可以被精确转移到参照运动中；一般势场则留下

$$
\boxed{
\mathcal R_q(y)
=
\Phi(q+y)-\Phi(q)-y\Phi'(q).
}
$$

这一余项从空间二阶变化开始，决定局部自由落体描述的偏差。

最后，把参照者本身也作为量子物体，得到两观察者之间的关系方程：

$$
\boxed{
\ddot Y
=
-\Phi'(X_A+Y)+\Phi'(X_A).
}
$$

它把“观察者作为描述中心”进一步落实为：**共同加速度可以从相对机械读数中消去，而空间变化不均匀所产生的潮汐作用仍然存在。**

内部质量算子的等效原理、量子参考系和质量相关相位均有既有研究基础。本文给出当前模型中的具体证明与适用范围，不将这些一般方向宣称为新发现。([arXiv][1])

---

# 181．不再预设三个质量角色可以同时经典化

## 定义 181.1　内部结构与运动空间

设观察者的内部空间为有限维空间

$$
\mathcal H_{\mathrm{int}}=\mathbb C^d,
$$

运动空间为

$$
\mathcal H_{\mathrm{mot}}=L^2(\mathbb R).
$$

完整空间为

$$
\mathcal H
=
\mathcal H_{\mathrm{int}}\otimes L^2(\mathbb R).
$$

给定三个内部算子：

$$
H_{\mathrm{rest}}=H_{\mathrm{rest}}^\dagger,
$$

$$
M_I=M_I^\dagger>0,
\qquad
M_G=M_G^\dagger>0.
$$

分别表示静止能量、惯性质量和引力响应质量。

**本节不假设它们两两可交换。**

为简化记号，令

$$
A=M_I^{-1},
\qquad
B=M_G,
\qquad
E=H_{\mathrm{rest}}.
$$

位置与动量为

$$
(X\psi)(x)=x\psi(x),
\qquad
P=-i\hbar\partial_x.
$$

内部算子与 \(X,P\) 可交换，但内部算子之间未必可交换。

---

## 假设 181.1　弱场有效 Hamiltonian

先取光滑有界势

$$
\Phi\in C_b^\infty(\mathbb R),
$$

并定义

$$
\boxed{
H_\Phi
=
E+\frac12AP^2+B\Phi(X).
}
\tag{181.1}
$$

\(\Phi\) 的量纲是单位质量的势能。

这是一项明确的模型选择：保留内部量子能量结构，但采用弱场、低速形式的质心动力学。它不包含完整相对论引力的所有修正。

复合量子系统中，静止能量如何进入质心运动和外场耦合，确实需要从完整模型中检查，不能只把三个参数赋予相同名字。([arXiv][2])

---

## 定理 181.1　模型具有自伴且有下界的实现

式（181.1）在

$$
\mathcal D
=
\mathbb C^d\otimes H^2(\mathbb R)
$$

上具有自伴实现，且

$$
\boxed{
H_\Phi
\ge
\left[
\lambda_{\min}(E)
-\|B\|\,\|\Phi\|_\infty
\right]I.
}
\tag{181.2}
$$

### 证明

\(A>0\) 为有限维算子，可以在其本征基中将

$$
\frac12AP^2
$$

分解为有限个正系数的自由 Schrödinger 算子，因而自伴且非负。

\(E+B\Phi(X)\) 为有界自伴扰动，所以保持自伴性。下界直接来自动能非负性与

$$
B\Phi(X)\ge-\|B\|\,\|\Phi\|_\infty I.
$$

∎

后续对易计算首先在共同不变的测试函数核心

$$
\mathbb C^d\otimes\mathscr S(\mathbb R)
$$

上进行。这样，算子域不是被隐去的前提。

---

# 182．非交换内部质量会产生哪些额外加速度？

定义反对易子

$$
\{C,D\}=CD+DC.
$$

## 定理 182.1　速度、动量变化与完整加速度

在上述共同核心上，

$$
\boxed{
\dot X=AP,
}
\tag{182.1}
$$

$$
\boxed{
\dot P=-B\Phi'(X).
}
\tag{182.2}
$$

但加速度一般不是简单的 \(-AB\Phi'(X)\)，而是

$$
\boxed{
\begin{aligned}
\ddot X
={}&
\frac{i}{\hbar}[E,A]P\\
&+
\frac{i}{2\hbar}[B,A]\{\Phi(X),P\}\\
&-
\frac12\{A,B\}\Phi'(X).
\end{aligned}
}
\tag{182.3}
$$

### 证明

首先，

$$
\dot X=\frac{i}{\hbar}[H_\Phi,X]=AP,
$$

以及

$$
\dot P=\frac{i}{\hbar}[H_\Phi,P]=-B\Phi'(X).
$$

因此

$$
\begin{aligned}
\ddot X
&=
\frac{i}{\hbar}[H_\Phi,AP]\\
&=
\frac{i}{\hbar}[E,A]P
+
\frac{i}{\hbar}[B,A]\Phi(X)P
-
AB\Phi'(X).
\end{aligned}
$$

再使用

$$
\Phi P
=
\frac12\{\Phi,P\}
+\frac{i\hbar}{2}\Phi',
$$

得到式（182.3）。∎

### 三个不同的结构

式（182.3）区分了：

$$
\boxed{
[E,M_I^{-1}]
:
\text{内部演化与惯性响应的不相容};
}
$$

$$
\boxed{
[M_G,M_I^{-1}]
:
\text{引力响应与惯性响应的不相容};
}
$$

$$
\boxed{
\frac12\{M_I^{-1},M_G\}
:
\text{直接的力—加速度转换}.
}
$$

因此，先对 \(M_I,M_G\) 分别取平均，再计算它们的比值，通常无法恢复完整加速度。

项目已经有有限维投影概率由 Hamiltonian 交换子控制的具体证明。本节沿同一原理计算运动读数，但位置—动量涉及无界算子，所以不能把已有有限矩阵定理直接当作本节的机器证明。

---

# 183．普适自由落体可以反过来约束内部算子

## 定义 183.1　全状态加速度一致性

固定一个非恒定的

$$
\Phi\in C_b^\infty(\mathbb R).
$$

若在共同测试函数核心上有

$$
\boxed{
\ddot X=-\Phi'(X)I_{\mathrm{int}},
}
\tag{183.1}
$$

则称该模型满足全状态加速度一致性。

这要求同一个加速度算子关系对全部内部态与运动态成立，而不仅是在若干能量本征态上的平均值成立。

---

## 定理 183.1　全状态加速度一致性的充要条件

在模型（181.1）中，

$$
\boxed{
\ddot X=-\Phi'(X)I
\iff
M_G=M_I
\quad\text{且}\quad
[E,M_I]=0.
}
\tag{183.2}
$$

### 证明

由定理 182.1 的未对称化形式，

$$
\boxed{
\ddot X+\Phi'(X)I
=
\frac{i}{\hbar}
\bigl([E,A]+[B,A]\Phi(X)\bigr)P
+
(I-AB)\Phi'(X).
}
\tag{183.3}
$$

若它对全部紧支撑光滑测试函数为零，则这个一阶矩阵微分算子的系数必须逐点为零。

这一点可通过在任意位置独立指定测试函数的值与一阶导数证明。因此

$$
[E,A]+[B,A]\Phi(x)=0
\qquad\forall x.
$$

因为 \(\Phi\) 非恒定，选择两个势值不同的位置相减，得到

$$
[B,A]=0,
$$

再得到

$$
[E,A]=0.
$$

剩余条件为

$$
(I-AB)\Phi'(x)=0.
$$

非恒定光滑函数的导数不恒为零，所以

$$
AB=I.
$$

由于 \(A=M_I^{-1}\)，得到 \(B=M_I\)。而

$$
[E,A]=0\iff[E,M_I]=0.
$$

反向，将这两个条件代入式（182.3），立即得到式（183.1）。∎

### 这比什么更强，又比什么更弱？

它比

$$
\langle M_G\rangle=\langle M_I\rangle
$$

更强。

但它尚未要求

$$
\boxed{
E=c^2M_I+\text{标量}.
}
$$

所以它还不是完整的量子 Einstein 等效原理，只是该有效 Hamiltonian 中的全状态自由落体判据。

例如，

$$
M_G=M_I=mI
$$

时，任意内部 \(E\) 都与质量可交换，满足本定理；但这些内部能量差是否同时贡献惯性和重量，仍需额外实验与模型条件。量子等效原理正是要进一步比较静止、惯性和引力内部能量的算子结构。([arXiv][1])

---

# 184．只测经典能级，可能漏掉量子自由落体差别

## 例 184.1　相同内部能级概率，不同初始加速度

取

$$
M_I=mI,
$$

$$
M_G=m(I+\eta\sigma_x),
\qquad 0<\eta<1,
$$

以及

$$
E=E_0I+\Delta\sigma_z,
\qquad E_0>|\Delta|.
$$

惯性质量为标量，因此

$$
\boxed{
\ddot X
=
-(I+\eta\sigma_x)\Phi'(X).
}
\tag{184.1}
$$

取两种内部态

$$
|\pm x\rangle
=
\frac{|0\rangle\pm|1\rangle}{\sqrt2}.
$$

它们在静止能量本征基中的概率都是

$$
\left(\frac12,\frac12\right),
$$

内部平均能量也相同。

对同一个初始运动态 \(\psi\)，记

$$
g_\psi=\langle\psi|\Phi'(X)|\psi\rangle.
$$

则初始加速度为

$$
\boxed{
\langle\ddot X\rangle_{\pm x}
=
-(1\pm\eta)g_\psi.
}
\tag{184.2}
$$

当 \(\eta=1/3\) 时，分别是标准值的

$$
\boxed{\frac43,\qquad\frac23.}
$$

相比之下，单独准备 \(\sigma_z\) 的两个本征态，两者的平均加速度都为 \(-g_\psi\)。

**因此，仅检验静止能量本征态，可以漏掉只在相干制备中显现的差别。**

这类“经典等效原理测试不能自动覆盖量子叠加测试”的区分，是量子等效原理研究的重要内容。([arXiv][3])

### 项目中的 carry 见证

若当前接口只保留内部能级概率和同一个运动初态，则它合并 \(|+x\rangle\) 与 \(|-x\rangle\)。

下一时刻的运动响应却能区分二者。因此：

$$
\boxed{
q_{\mathrm{energy}}(\rho_+)=q_{\mathrm{energy}}(\rho_-),
\qquad
T_{\mathrm{acc}}(\rho_+)\ne T_{\mathrm{acc}}(\rho_-).
}
\tag{184.3}
$$

这正是需要补充观察接口、而不能继续宣称精确下降的情况。

---

## 例 184.2　两个质量相等，仍不足以保证全部动力学相容

取

$$
M_G=M_I
=
m\begin{pmatrix}
1&0\\
0&2
\end{pmatrix},
$$

以及

$$
E=E_0I+\Delta\sigma_x.
$$

则

$$
\boxed{
\ddot X
=
-\Phi'(X)I
+
\frac{\Delta}{2m\hbar}\sigma_yP.
}
\tag{184.4}
$$

这第二项来自

$$
[E,M_I^{-1}]\ne0.
$$

即使没有外力，动量仍可守恒，而速度

$$
\dot X=M_I^{-1}P
$$

可以因为内部惯性结构的演化而改变。

这不是矛盾，而是说明：**“动量守恒”“质量算子相等”“速度变化普适”是不同命题。**

---

# 185．相容质量允许把自由落体写成联合酉变换

从本节开始，施加已经被上一节明确识别的条件：

$$
M_G=M_I=M>0,
\qquad
[E,M]=0.
$$

于是

$$
\boxed{
H_\Phi
=
E+\frac{P^2}{2M}+M\Phi(X).
}
\tag{185.1}
$$

这里的 \(M\) 仍然可以是非标量算子，内部态仍然允许质量—能量分支的相干叠加。

---

## 定义 185.1　沿参照轨迹的变换

选择一条经典标定轨迹 \(q(t)\)，满足

$$
\ddot q(t)=-\Phi'(q(t)).
$$

定义

$$
\dot s(t)
=
\frac12\dot q(t)^2-\Phi(q(t)).
$$

令

$$
\boxed{
\psi(x,t)
=
\exp\left\{
\frac{iM}{\hbar}
\left[
\dot q(t)(x-q(t))+s(t)
\right]
\right\}
\chi(x-q(t),t).
}
\tag{185.2}
$$

对每个固定 \(t\)，它是平移与质量条件相位的乘积，因此为酉映射。

这不是把内部质量先测成某个数。可以在 \(M\) 的各谱分支上同时实施同一个算子公式。

---

## 定理 185.1　自由落体参照中的精确余项

令

$$
y=x-q(t).
$$

则 \(\psi\) 满足式（185.1）的 Schrödinger 方程，当且仅当 \(\chi\) 满足

$$
\boxed{
i\hbar\partial_t\chi
=
\left[
E+\frac{P_y^2}{2M}
+
M\mathcal R_q(t,Y)
\right]\chi,
}
\tag{185.3}
$$

其中

$$
\boxed{
\mathcal R_q(t,y)
=
\Phi(q(t)+y)
-\Phi(q(t))
-y\Phi'(q(t)).
}
\tag{185.4}
$$

### 证明

将式（185.2）代入 Schrödinger 方程。

空间导数产生动量平移

$$
P\longmapsto P_y+M\dot q.
$$

时间导数中的平移项消去动能展开的交叉项。剩余势为

$$
M\left[
\Phi(q+y)+\ddot q\,y+\dot s-\frac12\dot q^2
\right].
$$

使用 \(q,s\) 的定义，得到式（185.4）。

由于 \([E,M]=0\)，相位变换不会额外旋转 \(E\)。∎

---

## 推论 185.1　均匀场可以被精确消去

对于

$$
\Phi(x)=g_0x,
$$

取

$$
q(t)=-\frac12g_0t^2,
$$

则

$$
\mathcal R_q=0,
$$

并有

$$
\boxed{
\psi(x,t)
=
e^{-iM(g_0tx+g_0^2t^3/6)/\hbar}
\chi\left(x+\frac12g_0t^2,t\right).
}
\tag{185.5}
$$

因此均匀场中的过程，与自由过程通过一个明确的联合酉变换关联。

质量算子与加速参考系之间的这种关系有既有研究；允许质量叠加，并不要求把量子力学或等效原理立即判定为互相冲突。([arXiv][4])

### 两项边界

第一，均匀势 \(g_0x\) 在整条实线上无下界。本节将它作为局部均匀场的理想模型，不把它当成具有全局有限热平衡的封闭宇宙。

第二，被动更换描述时，状态和测量效果都要变换：

$$
\rho'=S_q^\dagger\rho S_q,
\qquad
E'=S_q^\dagger E S_q.
$$

只变换状态、不变换测量，比较的就不是同一个实验。量子参考系理论特别需要保留这一点。([arXiv][5])

---

# 186．参照者本身量子化：均匀引力只作用于共同运动

上一节使用了一条已标定轨迹。现在让“参照者”也成为具有位置、动量和内部质量的量子系统。

## 假设 186.1　两个量子观察者

取两个系统 \(A,B\)，各自满足

$$
M_i>0,
\qquad
[E_i,M_i]=0.
$$

它们在本节没有直接相互作用，共同处于均匀势 \(\Phi(x)=g_0x\) 中：

$$
H
=
E_A+E_B
+
\frac{P_A^2}{2M_A}
+
\frac{P_B^2}{2M_B}
+
g_0(M_AX_A+M_BX_B).
$$

不同系统上的内部算子可交换。

定义

$$
M_{\mathrm{tot}}=M_A+M_B,
\qquad
\mu=M_AM_BM_{\mathrm{tot}}^{-1},
$$

以及

$$
\boxed{
Q=\frac{M_AX_A+M_BX_B}{M_{\mathrm{tot}}},
\qquad
Y=X_B-X_A,
}
\tag{186.1}
$$

$$
\boxed{
P_{\mathrm{tot}}=P_A+P_B,
\qquad
p=\frac{M_AP_B-M_BP_A}{M_{\mathrm{tot}}}.
}
\tag{186.2}
$$

---

## 定理 186.1　量子质量下的共同—相对分解

这些算子满足

$$
[Q,P_{\mathrm{tot}}]=i\hbar I,
\qquad
[Y,p]=i\hbar I,
$$

并且两组正则变量的交叉对易子为零。

Hamiltonian 精确分解为

$$
\boxed{
H
=
E_A+E_B
+
\frac{P_{\mathrm{tot}}^2}{2M_{\mathrm{tot}}}
+
g_0M_{\mathrm{tot}}Q
+
\frac{p^2}{2\mu}.
}
\tag{186.3}
$$

### 证明

由于质量算子相互可交换，并与运动算子可交换，可以直接使用正则对易关系计算。

动能恒等式为

$$
\frac{P_A^2}{2M_A}+\frac{P_B^2}{2M_B}
=
\frac{P_{\mathrm{tot}}^2}{2M_{\mathrm{tot}}}
+
\frac{p^2}{2\mu}.
$$

势能由 \(Q\) 的定义直接给出。

这些等式也可以在联合质量谱的每个分支上验证，再拼接为完整算子恒等式。∎

---

## 推论 186.1　均匀场不改变相对机械动力学

有

$$
\boxed{
\dot Y=\mu^{-1}p,
\qquad
\ddot Y=0.
}
\tag{186.4}
$$

对由 \(Y,p\) 和可交换质量算子生成的相对机械读数，其演化不依赖 \(g_0\)。

### 证明

共同运动部分与这些相对变量可交换。相对 Hamiltonian 仅为

$$
H_{\mathrm{rel}}=\frac{p^2}{2\mu}.
$$

∎

**这是一项真正以量子观察者为中心的结论：不必先把参照者的位置或质量设为无限精确的经典参数，均匀共同加速度仍可从相对机械描述中消去。**

但 \(\mu\) 仍是内部算子，因此相对波包的展宽、相位和与内部自由度的关联仍可能依赖质量。

$$
\boxed{
\text{相对加速度相同}
\not\Rightarrow
\text{全部量子概率分布相同}.
}
$$

有限质量参照的反冲与关系描述，正是量子参考系研究所必须保留的物理内容。([arXiv][5])

---

# 187．真正不能被共同自由落体消掉的是潮汐变化

现在允许一般光滑势 \(\Phi\)。

## 定理 187.1　两个量子观察者的相对加速度

在质量相容条件下，

$$
\boxed{
\ddot Y
=
-\Phi'(X_B)+\Phi'(X_A).
}
\tag{187.1}
$$

由于 \(X_A\) 与 \(Y=X_B-X_A\) 可交换，也可以写成

$$
\boxed{
\ddot Y
=
-Y\int_0^1
\Phi''(X_A+sY)\,ds.
}
\tag{187.2}
$$

### 证明

分别对两个系统应用 \(\ddot X_i=-\Phi'(X_i)\)，相减得到式（187.1）。

对两个可交换位置算子使用标量积分恒等式

$$
\Phi'(x+y)-\Phi'(x)
=
y\int_0^1\Phi''(x+sy)\,ds,
$$

即可得到式（187.2）。∎

---

## 推论 187.1　相对机械实验的仿射势不变性

把势替换为

$$
\widetilde\Phi(x)=\Phi(x)+ax+b,
$$

不会改变式（187.1）的相对加速度。

反之，如果对全部位置配置都有

$$
\Phi'(x_B)-\Phi'(x_A)=0,
$$

则 \(\Phi\) 必为仿射函数。

### 证明

附加线性项在两次求导读数之差中相消。

反向条件要求 \(\Phi'\) 在所有位置取同一个值。∎

这给观察接口一个准确的核：

> **在当前相对机械实验类中，势的共同常数部分和共同线性部分被合并；空间二阶变化一般不会被合并。**

但对有外部支撑的钟、不同路径相位或其他实验，这个接口可能不再充分。不能把相对加速度接口的不可见性推广为全部物理过程的不可见性。

---

## 定理 187.2　二次势给出精确的量子潮汐模型

取

$$
\Phi(x)=g_0x+\frac{\kappa}{2}x^2,
\qquad \kappa\ge0.
$$

则

$$
\boxed{
\ddot Y=-\kappa Y.
}
\tag{187.3}
$$

并且联合 Hamiltonian 的势能精确分解为

$$
\boxed{
\begin{aligned}
M_A\Phi(X_A)+M_B\Phi(X_B)
={}&
M_{\mathrm{tot}}
\left(g_0Q+\frac{\kappa}{2}Q^2\right)\\
&+\frac{\kappa\mu}{2}Y^2.
\end{aligned}
}
\tag{187.4}
$$

所以相对 Hamiltonian 为

$$
\boxed{
H_{\mathrm{rel}}
=
\frac{p^2}{2\mu}+\frac{\kappa\mu}{2}Y^2.
}
\tag{187.5}
$$

### 证明

使用

$$
X_A=Q-\frac{M_B}{M_{\mathrm{tot}}}Y,
\qquad
X_B=Q+\frac{M_A}{M_{\mathrm{tot}}}Y
$$

展开。交叉项相消，得到式（187.4），再计算 Heisenberg 方程。∎

相对振荡频率 \(\sqrt\kappa\) 不依赖内部质量，但位置分布和零点展宽仍可以依赖约化质量 \(\mu\)。

在已经建立的弱场度量实现中，\(\Phi''\) 对应相应的潮汐曲率分量。这个几何识别来自测地偏离关系，不是把任意内部算子交换子直接命名为曲率。([David Tong][6])

---

# 188．平直的操作闭路也能留下内部时间相位

前文已经强调：闭路状态不返回，不自动证明时空弯曲。量子质量给出另一个重要实例。

## 定义 188.1　平移与质量相关 boost

固定一个正质量算子 \(M\)，定义

$$
T(d)=e^{-idP/\hbar},
$$

$$
B(v)=e^{ivMX/\hbar}.
$$

其中 \(d\) 是平移距离，\(v\) 是 boost 参数。

它们作用于同一个运动—内部空间。

---

## 定理 188.1　平直平移—boost 闭路的精确相位

有

$$
\boxed{
B(v)T(d)B(-v)T(-d)
=
e^{ivdM/\hbar}.
}
\tag{188.1}
$$

### 证明

在每个质量本征分支上，对任意测试函数 \(\psi(x)\)，

$$
(T(d)\psi)(x)=\psi(x-d),
$$

$$
(B(v)\psi)(x)=e^{ivMx/\hbar}\psi(x).
$$

依次作用四个算子，位置平移全部相消，剩余因子为

$$
e^{ivMx/\hbar}e^{-ivM(x-d)/\hbar}
=
e^{ivdM/\hbar}.
$$

各质量分支共同给出算子恒等式。∎

---

## 推论 188.1　质量中的内部能量可以把闭路相位转化为内部时钟变换

若进一步有

$$
M=m_0I+\frac{H_C}{c^2},
$$

则

$$
\boxed{
e^{ivdM/\hbar}
=
e^{im_0vd/\hbar}
e^{iH_Cvd/(\hbar c^2)}.
}
\tag{188.2}
$$

后一因子等价于内部钟参数变化

$$
\boxed{
\Delta\tau=-\frac{vd}{c^2}
}
\tag{188.3}
$$

的酉作用，符号由闭路顺序决定。

### 解释

对于固定数值质量，式（188.1）只是整体相位。

对于具有内部能量结构的质量算子，它可以成为内部态之间的相对相位。

但它并不需要非零时空曲率：这个代数关系在平直运动学中已经存在。质量相关的 Galilei 扩张相位及其与内部时间的联系已有相应研究。([arXiv][7])

还必须区分：

* 若只是被动地变换描述，测量和参照也要共同变换，不能凭坐标循环制造物理变化。
* 若实际执行平移、加速和返回操作，那么控制器、能量交换及两条操作历史都必须进入完整实验。

式（188.3）描述相对酉参数，不表示让观察者沿自己的未来世界线倒着经历固有时间。

因此：

$$
\boxed{
\text{内部时间相位}
\not\Rightarrow
\text{曲率};
}
$$

真正的曲率识别必须排除这类运动学与参照实现贡献。

---

# 189．局部自由落体近似可以获得显式误差证书

第 185 节已经得到精确余项

$$
\mathcal R_q(t,y)
=
\Phi(q+y)-\Phi(q)-y\Phi'(q).
$$

现在把“局部近似自由”量化。

## 定理 189.1　潮汐余项的空间二阶界

若在所需区域内

$$
|\Phi''(x)|\le K_\Phi,
$$

则

$$
\boxed{
\mathcal R_q(t,y)
=
y^2\int_0^1(1-s)\Phi''(q(t)+sy)\,ds,
}
\tag{189.1}
$$

并且

$$
\boxed{
|\mathcal R_q(t,y)|
\le\frac{K_\Phi}{2}y^2.
}
\tag{189.2}
$$

### 证明

对 \(\Phi(q+y)\) 使用带积分余项的一阶 Taylor 公式。∎

这表明，在自由落体参照中，控制近似的不是势本身有多大，而是它在所用区域内的二阶变化。

当然，若要把本模型当作现实的弱场近似，低速、弱场和控制范围仍必须满足先前假设。

---

## 定理 189.2　有限量子实验的局部自由落体误差

在自由落体参照中比较

$$
H_{\mathrm{tid}}(t)
=
E+\frac{P_Y^2}{2M}+M\mathcal R_q(t,Y)
$$

与

$$
H_{\mathrm{free}}
=
E+\frac{P_Y^2}{2M}.
$$

令

$$
m_{\max}=\|M\|.
$$

对同一个初态，设自由参考演化具有有限四阶位置矩。则

$$
\boxed{
D\bigl(\rho_{\mathrm{tid}}(T),\rho_{\mathrm{free}}(T)\bigr)
\le
\frac{m_{\max}}{2\hbar}
\int_0^T
K_\Phi(t)
\sqrt{\operatorname{Tr}[\rho_{\mathrm{free}}(t)Y^4]}
\,dt.
}
\tag{189.3}
$$

若

$$
\sqrt{\operatorname{Tr}[\rho_{\mathrm{free}}(t)Y^4]}
\le L^2,
\qquad K_\Phi(t)\le K_*,
$$

则

$$
\boxed{
D\bigl(\rho_{\mathrm{tid}}(T),\rho_{\mathrm{free}}(T)\bigr)
\le
\frac{m_{\max}K_*L^2T}{2\hbar}.
}
\tag{189.4}
$$

必要时将上界截断到一。

### 证明

先纯化初态。由 Duhamel 公式，

$$
\begin{aligned}
&(U_{\mathrm{tid}}(T)-U_{\mathrm{free}}(T))|\Psi_0\rangle\\
&=
-\frac{i}{\hbar}\int_0^T
U_{\mathrm{tid}}(T,t)
M\mathcal R_q(t,Y)
U_{\mathrm{free}}(t)|\Psi_0\rangle\,dt.
\end{aligned}
$$

左侧实际后缀酉演化不增加范数。使用式（189.2），有

$$
\|M\mathcal R_q\Psi_{\mathrm{free}}\|
\le
\frac{m_{\max}K_\Phi}{2}
\|Y^2\Psi_{\mathrm{free}}\|.
$$

积分后，再使用纯态迹距离不超过相应向量距离及偏迹收缩性，得到结论。∎

### 这是什么性质的证书？

它是对满足位置矩预算的输入族给出的过程误差界，不是对任意无限扩展波包的无条件 diamond 范数界。

因此，局部等效性具有明确窗口：

$$
\boxed{
\frac{m_{\max}K_*L^2T}{\hbar}\ll1.
}
\tag{189.5}
$$

同一个区域，对短时间、窄波包的观察者可能足够接近自由过程；对更宽或更长相干时间的实验，潮汐余项可能变得可见。

---

## 与内部钟的进一步连接

若

$$
M=m_0I+\frac{H_C}{c^2},
$$

则潮汐项包含

$$
\boxed{
H_{\mathrm{tidal,clock}}
=
\frac{H_C}{c^2}\mathcal R_q(t,Y).
}
\tag{189.6}
$$

在适当的路径控制与其他相位校准条件下，两条路径的内部相位差包含

$$
\boxed{
\Delta\varphi_{\mathrm{tidal}}
=
-\frac{\Delta E}{\hbar c^2}
\int
\left[
\mathcal R_q(t,y_1(t))
-
\mathcal R_q(t,y_2(t))
\right]dt.
}
\tag{189.7}
$$

这只是潮汐势对钟相位的贡献；不同路径的动能相位、控制力和读出装置仍须一并处理。

在已有弱场洛伦兹实现中，相对加速度和这种局部时间差可以共同约束曲率，而不必先把内部能量相位等同于几何本身。([David Tong][6])

---

# 190．形式化时必须保留的三个层级

本轮可以整理成一条更强的证明链：

$$
\boxed{
\text{内部能量与质量算子}
\longrightarrow
\text{完整加速度}
\longrightarrow
\text{普适性约束}.
}
$$

条件满足以后：

$$
\boxed{
\text{联合自由落体变换}
\longrightarrow
\text{相对机械描述}
\longrightarrow
\text{不可消去的潮汐余项}.
}
$$

最后：

$$
\boxed{
\text{潮汐余项}
+
\text{实验尺度与状态矩预算}
\longrightarrow
\text{局部几何近似误差}.
}
$$

## 190.1　有限内部矩阵与连续运动不能混成同一种证明

内部的 \(E,M_I,M_G\) 都可以使用有限矩阵形式化。

但位置与动量不能被有限矩阵精确实现为

$$
[X,P]=i\hbar I.
$$

### 命题 190.1

不存在非零有限维空间上的矩阵 \(X,P\)，满足上述关系。

### 证明

取迹：

$$
\operatorname{Tr}[X,P]=0,
$$

而

$$
\operatorname{Tr}(i\hbar I)=i\hbar d\ne0.
$$

矛盾。∎

因此，严格形式化应当区分：

**有限代数层**：内部质量、交换子、状态正性与有限读数反例。

**运动分析层**：Schwartz 核、微分算子、自伴实现、酉变换与 Duhamel 界。

**几何识别层**：把 \(\Phi''\) 与已重建度量的潮汐曲率联系，保留弱场与共同标定条件。

不能用一个截断位置矩阵在数值上“近似满足”正则对易关系，就把后续所有恒等式标记为精确证明。

---

## 190.2　与项目当前结构的对应

本次读取固定于提交

```text
2f482cc73003d7a23940a9af1e0494bb1f230171
```

其中：

`ProjectionProbabilityFlow.lean` 已提供有限量子态中，投影概率变化由 Hamiltonian 交换子迹控制的证明。

`ExactDescentNoCarry.lean` 则提供精确下降排除 carry 的结构性定理。第 184 节的相干质量实例说明，若只保留能级概率，就无法为后续运动目标填写这样的下降证明。

| 项目角色         | 本轮具体对象                        |
| ------------ | ----------------------------- |
| **CUT**      | 内部能级概率、加速度、相对位置、路径相位          |
| **FLOW**     | 完整矩阵值 Hamiltonian、量子质量条件的参照变换 |
| **ADMIT**    | 正质量、自伴域、普适加速度条件、弱场与位置矩预算      |
| **Residual** | 内部交换子项、隐藏相干质量、自由落体后的潮汐余项      |
| **ANCHOR**   | 相干态制备、相对运动记录、闭路干涉与局部误差证书      |

这里的“潮汐余项”与一般信息残差不是同一类型。它们之间的联系，是前者通过实际演化改变后续读数，从而构成后者的具体物理见证。

---

## 190.3　本轮核验

已作精确符号检查的内容包括：

非交换质量的完整加速度公式；相同能级概率对应的 \(4/3\)、\(2/3\) 加速度因子；均匀场自由落体变换；双量子观察者的共同—相对动能分解；二次势的潮汐分解；平移—boost 闭路相位。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_quantum_freefall_tidal.py)
[核验结果](sandbox:/mnt/data/observer_formalization/quantum_freefall_tidal_checks.json)

这些检查使用有限内部矩阵与符号微分算子，没有把精确正则对易关系替换成有限矩阵近似。

**本轮未进行 Lean 编译。**符号核验支持所列恒等式和实例，不替代一般分析定理的机器证明，也不认证模型中的物理假设已经符合现实。

---

# 结论

本轮最重要的推进，是把“观察者是中心”从一种描述立场，转化成三项具有不同强度的数学命题。

**第一，观察者内部结构必须与其运动角色相容。**

$$
\boxed{
M_G=M_I,
\qquad
[H_{\mathrm{rest}},M_I]=0
}
$$

在本模型中，恰好保证全状态的普适加速度。仅比较平均质量，无法完成这一检验。

**第二，观察者自身可以是量子的，而共同自由落体仍然可以被消去。**

参照者不必具有无限大的经典质量；使用两个量子物体的相对位置、相对动量和约化质量，均匀共同加速度依然从相对机械动力学中消失。

**第三，真正保留下来的几何内容从空间不均匀性开始。**

$$
\boxed{
\ddot Y
=
-Y\int_0^1\Phi''(X_A+sY)\,ds.
}
$$

它说明局部观察者不是直接“看到一份绝对引力”，而是通过不同位置之间不可由共同自由落体消去的关系，读取潮汐结构。

因此，当前理论可以进一步收紧为：

> **先检验观察者内部能量、惯性与引力响应是否相容；再把共同参照运动从关系读数中分离；最后由剩余的、具有误差证书的跨位置响应重建几何。**

这条路线没有把所有相位都叫作时间、把所有交换子都叫作曲率，也没有把任意参考系变换都叫作物理作用。

**物理时空在这里逐渐成为：量子观察者能够共同消去什么，以及在合法参照变换之后仍然无法消去什么，由这两类结构共同确定的关系对象。**

[1]: https://arxiv.org/abs/1502.00971?utm_source=chatgpt.com "Quantum formulation of the Einstein Equivalence Principle"
[2]: https://arxiv.org/html/1808.05831v2?utm_source=chatgpt.com "Gravitational mass of composite systems"
[3]: https://arxiv.org/html/2112.03303v4 "Quantum generalisation of Einstein’s Equivalence Principle can be verified with entangled clocks as quantum reference frames"
[4]: https://arxiv.org/html/1302.5596v1 "1Introduction"
[5]: https://arxiv.org/html/1712.07207v2 "Quantum mechanics and the covariance of physical laws in quantum reference frames"
[6]: https://davidtong.org/teaching/general-relativity/grhtml/S3.html "3 Introducing Riemannian Geometry‣ General Relativity by David Tong"
[7]: https://arxiv.org/html/1906.03725v1 "Puzzling out the mass-superselection rule"
# 互惠反作用、关系相位与潮汐纠缠

## ——量子观察者—关系时空理论第一百九十一至第二百节增订

### 摘要

上一轮已经把观察者的内部质量、自由落体参照和潮汐余项放入同一个量子模型，但引力势仍主要被当成给定背景。

本轮进一步取消这一不对称：

> **观察者不仅读取其他系统产生的结构，也以自身能量改变其他观察者的钟与运动。两者必须来自同一个联合动力学，不能分别指定。**

本文证明三项相互连接的结果：

$$
\boxed{
\text{双方钟速的互易响应}
\longrightarrow
\text{共同相互作用能量};
}
$$

$$
\boxed{
\text{共同相互作用能量}
\longrightarrow
\text{作用—反作用与相对运动};
}
$$

$$
\boxed{
\text{相互作用的混合差分}
\longrightarrow
\text{不可由局部相位消去的纠缠};
}
$$

在小空间位移极限中，最后一项由势能 Hessian 控制，也就是同一模型中控制相对潮汐响应的矩阵。

引力相互作用导致量子钟纠缠，以及通过空间叠加探针研究引力介导纠缠，都有既有研究基础。下文的目标是把钟速、能量、反作用和关系读数组织成一条可形式化的证明链，不把这些一般机制宣称为首次发现。([arXiv][1])

本轮限定于弱场、低速的有效相互作用模型。空间坐标、共同时间标定和 Newton 型核是明确输入，不声称已由一般观察者定义唯一推出。

---

# 191．双方钟速必须能够由同一个能量函数积分出来

先从一个不涉及无界量子算子的条件性命题开始。

## 定义 191.1　准静态联合能量与钟响应

设两观察者的已标定内部能量参数为

$$
e_A\ge0,\qquad e_B\ge0,
$$

其关系配置为 \(r\)。

令联合准静态能量为

$$
\mathcal E(e_A,e_B;r).
$$

假设它对两个能量参数二次连续可微。定义能量增量响应：

$$
n_A=\frac{\partial\mathcal E}{\partial e_A},
\qquad
n_B=\frac{\partial\mathcal E}{\partial e_B}.
\tag{191.1}
$$

这些导数首先表示：增加一方内部能量时，共同参照能量怎样改变。后文通过有限能级跃迁，说明它们何时正好成为钟速因子。

本节进一步选择以下结构条件：

$$
n_A=n_A(e_B,r),
\qquad
n_B=n_B(e_A,r),
\tag{191.2}
$$

即相互作用对一方的钟速修正依赖另一方的源能量，而不再额外依赖自身能量。

并取无相互作用源时的标定：

$$
\mathcal E(e_A,0;r)=e_A,
\qquad
\mathcal E(0,e_B;r)=e_B.
\tag{191.3}
$$

条件（191.2）不是一般物理定律，而是当前双体、双线性候选模型的选择。

---

## 定理 191.1　互惠钟律的能量重建

上述条件成立，当且仅当存在一个实函数 \(\kappa(r)\)，使

$$
\boxed{
\mathcal E(e_A,e_B;r)
=
e_A+e_B+\kappa(r)e_Ae_B.
}
\tag{191.4}
$$

因此

$$
\boxed{
n_A=1+\kappa(r)e_B,
\qquad
n_B=1+\kappa(r)e_A,
}
\tag{191.5}
$$

以及

$$
\boxed{
\frac{\partial n_A}{\partial e_B}
=
\frac{\partial n_B}{\partial e_A}
=
\kappa(r).
}
\tag{191.6}
$$

### 证明

混合偏导相等给出

$$
\frac{\partial n_A(e_B,r)}{\partial e_B}
=
\frac{\partial n_B(e_A,r)}{\partial e_A}.
$$

左侧与 \(e_A\) 无关，右侧与 \(e_B\) 无关。由于 \(e_A,e_B\) 可独立变化，两侧只能等于一个仅依赖 \(r\) 的函数 \(\kappa(r)\)。

积分并使用边界标定（191.3），得到式（191.4）—（191.5）。

反向直接求导验证。∎

### 物理解释

若声称双方的钟速都来自同一个闭合能量函数，那么“\(A\) 对 \(B\) 的影响”和“\(B\) 对 \(A\) 的影响”不能随意独立选择。

如果实验发现互易性不成立，可能需要加入驱动、耗散、隐藏变量或历史依赖。不能继续使用原来的准静态能量函数，却把失配视为无关细节。

---

## 推论 191.1　直接相加两份红移能量会重复计算相互作用

由式（191.5），

$$
e_An_A+e_Bn_B
=
e_A+e_B+2\kappa e_Ae_B.
$$

因此

$$
\boxed{
e_An_A+e_Bn_B
=
\mathcal E+\kappa e_Ae_B.
}
\tag{191.7}
$$

局部能量增量响应不是两个可直接相加的独立总能量。

**双方都读到相互作用，不表示完整系统存在两份相同的相互作用能。**

---

# 192．一个双方都具有反作用的量子实现

## 定义 192.1　内部能量与质量算子

取两个有限维内部空间，并定义

$$
E_A=E_A^\dagger>0,
\qquad
E_B=E_B^\dagger>0.
$$

它们包含各自完整的静止能量；内部钟由其中的非平凡能级差实现。

令

$$
M_A=\frac{E_A}{c^2},
\qquad
M_B=\frac{E_B}{c^2}.
$$

两个系统作用于不同张量因子，因此 \(E_A,E_B\) 可交换。

运动空间取

$$
L^2(\mathbb R^3_{x_A}\times\mathbb R^3_{x_B}),
$$

并定义相对位置

$$
R=X_B-X_A.
$$

---

## 定义 192.2　正则化的 Newton 型相互作用

为避免在本轮把碰撞奇点和短距离稳定性隐藏起来，固定 \(\ell>0\)，定义

$$
u_\ell(R)
=
-\frac{G}{\sqrt{|R|^2+\ell^2}}.
$$

联合 Hamiltonian 为

$$
\boxed{
H=
E_A+E_B
+
\frac{P_A^2}{2M_A}
+
\frac{P_B^2}{2M_B}
+
M_AM_Bu_\ell(R).
}
\tag{192.1}
$$

对应第 191 节的

$$
\kappa_\ell(R)=\frac{u_\ell(R)}{c^4}.
$$

对于 \(r\gg\ell\)，它接近通常的 \(-G/r\) 核。但 \(\ell\) 在这里是明确的模型正则化参数，不被指定为某个基本自然长度。

用完整内部能量构造双钟引力相互作用，是已有量子钟研究采用的一条有效模型路线。本文进一步保留两个系统的运动与反冲。([arXiv][1])

---

## 定理 192.1　自伴性、下界与能量守恒

式（192.1）具有自伴实现，且

$$
\boxed{
H\ge
\left[
\lambda_{\min}(E_A)+\lambda_{\min}(E_B)
-\frac{G}{\ell}\|M_AM_B\|
\right]I.
}
\tag{192.2}
$$

此外，

$$
\boxed{
[H,E_A]=[H,E_B]=0,
}
\tag{192.3}
$$

以及

$$
\boxed{
[H,P_A+P_B]=0.
}
\tag{192.4}
$$

### 证明

在内部能量的联合本征基中，动能分解为有限个正质量自由 Schrödinger 算子，具有共同的 Sobolev 自伴域。

相互作用为有界实乘法算子，并满足

$$
M_AM_Bu_\ell(R)
\ge
-\frac{G}{\ell}\|M_AM_B\|I.
$$

有界自伴扰动保持自伴性，得到下界。

所有内部能量算子都与质量、位置和动量中的相应组合可交换，故式（192.3）成立。

相互作用只依赖 \(X_B-X_A\)，在共同平移下不变，因此总动量守恒。∎

### 重要区别

各自内部能量守恒，不意味着各自量子钟能够独立演化。

例如能量概率可以保持不变，而内部相位已经与另一方相关。项目的 `ConservationAutonomySeparation.lean` 明确区分了守恒与自主演化；本模型提供了这种区别的双观察者实例。

---

# 193．以观察者为中心，不等于忽略观察者的反冲

## 定理 193.1　作用—反作用与相对加速度

在共同测试函数核心上，

$$
\boxed{
\dot P_A
=
M_AM_B\nabla u_\ell(R),
}
\tag{193.1}
$$

$$
\boxed{
\dot P_B
=
-M_AM_B\nabla u_\ell(R).
}
\tag{193.2}
$$

从而

$$
\boxed{
\ddot X_A=M_B\nabla u_\ell(R),
\qquad
\ddot X_B=-M_A\nabla u_\ell(R),
}
\tag{193.3}
$$

以及

$$
\boxed{
\ddot R
=
-(M_A+M_B)\nabla u_\ell(R).
}
\tag{193.4}
$$

### 证明

相互作用对 \(X_A\) 求梯度时产生负号，对 \(X_B\) 求梯度时产生正号。由 Heisenberg 方程得到式（193.1）—（193.2）。

质量算子与完整 Hamiltonian 可交换，因此可在时间求导中保持不变。再用

$$
\dot X_i=M_i^{-1}P_i
$$

得到其余结论。∎

---

## 定理 193.2　共同运动与关系运动的精确分解

定义

$$
M_{\mathrm{tot}}=M_A+M_B,
\qquad
\mu=\frac{M_AM_B}{M_A+M_B},
$$

$$
Q=\frac{M_AX_A+M_BX_B}{M_{\mathrm{tot}}},
\qquad
P_{\mathrm{tot}}=P_A+P_B,
$$

$$
p=\frac{M_AP_B-M_BP_A}{M_{\mathrm{tot}}}.
$$

则

$$
\boxed{
H=
E_A+E_B
+
\frac{P_{\mathrm{tot}}^2}{2M_{\mathrm{tot}}}
+
\frac{p^2}{2\mu}
+
M_AM_Bu_\ell(R).
}
\tag{193.5}
$$

并有

$$
\boxed{\ddot Q=0.}
\tag{193.6}
$$

### 证明

质量算子彼此可交换，可以在其联合谱分支上应用动能恒等式，再拼接为完整算子关系。

相互作用只依赖 \(R\)，与共同位置 \(Q\) 无关，因此共同运动自由。∎

**把 \(A\) 选为描述中心，只是改用关系变量；它没有把 \(A\) 变成质量无限大、不会反冲的装置。**

单方背景近似应当由某个质量比、状态集中条件或误差界导出，不能通过称呼某方为“观察者”直接取得。

---

# 194．真正的相互作用由四分支差分读取

下面先建立一个与具体势形式无关的有限量子定理。

## 定义 194.1　两个二选一寄存器的相位过程

设两个观察者分别具有分支 \(s,t\in\{0,1\}\)。

在已实现的对角过程内，四个分支能量为 \(W_{st}\)，作用时间为 \(T\)，相位为

$$
\phi_{st}=-\frac{T}{\hbar}W_{st}.
$$

定义混合相位

$$
\boxed{
\Xi
=
\phi_{11}-\phi_{10}-\phi_{01}+\phi_{00}
\pmod{2\pi}.
}
\tag{194.1}
$$

---

## 定理 194.1　混合相位不受独立局部相位影响

若

$$
\phi_{st}\longmapsto\phi_{st}+a_s+b_t,
$$

则 \(\Xi\) 不变。

而对角酉

$$
U=\sum_{s,t}e^{i\phi_{st}}|st\rangle\langle st|
$$

可以写成两个局部对角酉的乘积，当且仅当

$$
\boxed{e^{i\Xi}=1.}
\tag{194.2}
$$

### 证明

局部相位在式（194.1）中两两相消。

反向分解可先用第一行、第一列确定局部相位，唯一剩余的相容条件就是式（194.2）。∎

这一不变量消去的是**每一方独立产生的分支相位**。它不是不加条件地消去全部控制误差，也不是任意时空坐标变换下的完整几何不变量。

---

## 定理 194.2　混合相位决定该纯态实验的纠缠

取初态

$$
|+\rangle_A|+\rangle_B.
$$

经过上述对角酉后，两比特 concurrence 为

$$
\boxed{
\mathcal C
=
\left|\sin\frac{\Xi}{2}\right|.
}
\tag{194.3}
$$

### 证明

输出振幅矩阵为

$$
C_{st}=\frac12e^{i\phi_{st}}.
$$

两比特纯态的 concurrence 等于 \(2|\det C|\)，因此

$$
2|\det C|
=
\frac12
\left|
e^{i(\phi_{00}+\phi_{11})}
-
e^{i(\phi_{01}+\phi_{10})}
\right|,
$$

化简得到式（194.3）。∎

引力介导纠缠方案也利用这类不能拆成两个局部相位的相互作用相位。关键不在于单个探针“获得了引力相位”，而在于联合过程不能分解为各自独立演化。([arXiv][2])

---

# 195．钟速互易性与两钟纠缠是同一个能量差分

## 假设 195.1　固定关系配置的钟协议

在一次经过控制与标定的实验中，把关系配置保持在 \(r\)，并使用准静态能量

$$
\mathcal E(e_A,e_B;r)
=
e_A+e_B+\kappa(r)e_Ae_B.
$$

每只钟选取两个能级：

$$
e_A^{(s)}=e_{A0}+s\epsilon_A,
\qquad
e_B^{(t)}=e_{B0}+t\epsilon_B,
$$

其中 \(\epsilon_A,\epsilon_B>0\)。

固定配置不属于自由双体运动的自动结论。实现它需要支撑、陷阱或短时控制，并在第 198 节计入相应误差。

---

## 定理 195.1　有限钟跃迁的精确互惠关系

当 \(B\) 处于能级 \(e_B^{(t)}\) 时，\(A\) 的跃迁能量为

$$
\boxed{
\Delta_A\mathcal E
=
\epsilon_A\left[1+\kappa(r)e_B^{(t)}\right].
}
\tag{195.1}
$$

因此

$$
n_A^{(1)}-n_A^{(0)}
=
\kappa(r)\epsilon_B.
\tag{195.2}
$$

相应混合相位为

$$
\boxed{
\Xi_{\mathrm{clock}}
=
-\frac{T}{\hbar}\kappa(r)\epsilon_A\epsilon_B.
}
\tag{195.3}
$$

并满足

$$
\boxed{
\Xi_{\mathrm{clock}}
=
-\frac{T\epsilon_A}{\hbar}
\bigl(n_A^{(1)}-n_A^{(0)}\bigr)
=
-\frac{T\epsilon_B}{\hbar}
\bigl(n_B^{(1)}-n_B^{(0)}\bigr).
}
\tag{195.4}
$$

### 证明

对双线性能量分别作一次和两次有限差分，即得。∎

这不是把“钟速”与“纠缠”类比起来，而是说明：

> **在该实现中，另一只钟改变本钟频率的分支差异，正好积累成两钟之间不可局部分解的相位。**

当 \(\kappa=-G/(c^4r)\) 时，这就是引力相互作用量子钟模型中的相应机制；其局部约化相干与联合纠缠已在既有研究中明确分析。([美国国家科学院院刊][3])

### 一个进一步区别

\(\Xi_{\mathrm{clock}}\) 只依赖能级差 \(\epsilon_A,\epsilon_B\)，不依赖两个共同能量偏置 \(e_{A0},e_{B0}\)。

但双体受力依赖完整的 \(M_AM_B\)。

所以：

$$
\boxed{
\text{内部钟纠缠率相同}
\not\Rightarrow
\text{两体机械反作用完全相同}.
}
$$

这与前文“内部能级差不能唯一确定完整静止能量”的结果相容。

---

# 196．空间分支的混合相位，直接读取潮汐矩阵

本节固定两个质量分支 \(m_A,m_B\)，令

$$
V(R)=m_Am_Bu(R).
$$

取两个空间选项：

$$
X_A^{(s)}=x_A+s\,a,
\qquad
X_B^{(t)}=x_B+t\,b,
$$

并记

$$
r=x_B-x_A.
$$

四个相对位置为

$$
R_{st}=r+t\,b-s\,a.
$$

---

## 定理 196.1　空间混合相位的精确 Hessian 表示

若 \(V\) 在相应平行四边形上为 \(C^2\)，则

$$
\boxed{
\Xi_{\mathrm{space}}
=
\frac{T}{\hbar}
\int_0^1\!\!\int_0^1
a^{\mathsf T}
\operatorname{Hess}V(r+t\,b-s\,a)
b\,ds\,dt.
}
\tag{196.1}
$$

### 证明

令

$$
F(s,t)=V(r+t\,b-s\,a).
$$

则

$$
\partial_s\partial_tF
=
-a^{\mathsf T}\operatorname{Hess}V(r+t\,b-s\,a)b.
$$

对单位方形积分，得到

$$
V_{11}-V_{10}-V_{01}+V_{00}
=
-\int_0^1\!\!\int_0^1a^{\mathsf T}(\operatorname{Hess}V)b\,ds\,dt.
$$

再乘以 \(-T/\hbar\)。∎

若 Hessian 的变化满足

$$
\|\operatorname{Hess}V(x)-\operatorname{Hess}V(y)\|
\le L_3|x-y|,
$$

则

$$
\boxed{
\left|
\Xi_{\mathrm{space}}
-
\frac{T}{\hbar}a^{\mathsf T}\operatorname{Hess}V(r)b
\right|
\le
\frac{TL_3}{2\hbar}
|a||b|(|a|+|b|).
}
\tag{196.2}
$$

---

## 推论 196.1　均匀项被消去，潮汐项被保留

若

$$
V(R)\longmapsto V(R)+\lambda\cdot R+\lambda_0,
$$

则 \(\Xi_{\mathrm{space}}\) 不变。

对固定质量，相对加速度为

$$
\ddot R=-\mu^{-1}\nabla V(R),
\qquad
\mu=\frac{m_Am_B}{m_A+m_B}.
$$

定义局部相对潮汐矩阵

$$
\mathcal T_{\mathrm{rel}}
=
-\mu^{-1}\operatorname{Hess}V.
$$

于是小位移下

$$
\boxed{
\Xi_{\mathrm{space}}
=
-\frac{\mu T}{\hbar}
a^{\mathsf T}\mathcal T_{\mathrm{rel}}(r)b
+\text{受控余项}.
}
\tag{196.3}
$$

**同一个 Hessian，一边控制相邻关系运动如何分离，另一边控制空间分支之间产生多少不可局部分解的相位。**

在已经建立的弱场几何中，潮汐矩阵再通过测地偏离与相应曲率分量联系。但 Hessian 本身不是完整 Riemann 张量，也不是任意相互作用都必须称为引力。([David Tong][4])

---

## 例 196.1　Newton 核的明确结果

对

$$
V(r)=-\frac{Gm_Am_B}{|r|},
\qquad r\ne0,
$$

有

$$
\boxed{
\operatorname{Hess}V
=
Gm_Am_B
\left(
\frac I{|r|^3}
-
\frac{3rr^{\mathsf T}}{|r|^5}
\right).
}
\tag{196.4}
$$

径向本征值为

$$
-\frac{2Gm_Am_B}{|r|^3},
$$

两个横向本征值为

$$
\frac{Gm_Am_B}{|r|^3}.
$$

对共线、等长位移 \(a=b=h\widehat r\)，且 \(r>h>0\)，精确得到

$$
\boxed{
\Xi_{\mathrm{space}}
=
-\frac{
2Gm_Am_BT\,h^2
}{
\hbar r(r^2-h^2)
}.
}
\tag{196.5}
$$

这也说明：只测纠缠量

$$
|\sin(\Xi/2)|
$$

会丢失相位符号和周期信息。要重建潮汐矩阵，需要相位可分辨的联合实验，而不仅是判断“有没有纠缠”。

---

# 197．相同的单体状态，仍可能产生不同的反作用

现在检验一种常见压缩：只保留每个观察者自己的状态，再用它们的平均质量拼出相互作用。

## 定义 197.1　两种具有相同边缘态的输入

令

$$
E_A=e_AI+\epsilon_A|1\rangle\langle1|,
\qquad
E_B=e_BI+\epsilon_B|1\rangle\langle1|.
$$

取

$$
\rho_{\mathrm c}
=
\frac12|00\rangle\langle00|
+
\frac12|11\rangle\langle11|,
$$

$$
\rho_{\mathrm a}
=
\frac12|01\rangle\langle01|
+
\frac12|10\rangle\langle10|.
$$

两者的每个单体边缘态都为 \(I/2\)。

---

## 定理 197.1　单体能量与温度接口不足以确定两体受力

有

$$
\boxed{
\langle E_AE_B\rangle_{\mathrm c}
-
\langle E_AE_B\rangle_{\mathrm a}
=
\frac{\epsilon_A\epsilon_B}{2}.
}
\tag{197.1}
$$

若两种内部态配上同一个初始运动状态，则

$$
\boxed{
\Delta\langle\dot P_A\rangle
=
\frac{\epsilon_A\epsilon_B}{2}
\left\langle\nabla\kappa_\ell(R)\right\rangle.
}
\tag{197.2}
$$

只要右侧非零，相同的当前单体接口就给出不同的后续动量读数。

### 证明

直接展开两种状态下的 \(E_AE_B\)，得到式（197.1）。

由

$$
\dot P_A=E_AE_B\nabla\kappa_\ell(R),
$$

以及初始内部—运动乘积条件，得到式（197.2）。∎

这两个态甚至不需要具有量子纠缠；经典关联已经足以产生差别。

原因是

$$
\boxed{
\langle E_AE_B\rangle
=
\langle E_A\rangle\langle E_B\rangle
+
\operatorname{Cov}(E_A,E_B).
}
\tag{197.3}
$$

**“双方平均质量已知”不是相互作用能量已知的充分条件。**

在当前模型中，两种输入的平均加速度还可能相同，因为质量相等原则中的惯性因子参与了消去；这再次说明，动量、加速度、相互作用能量是不同目标，不能只用一个标量覆盖。

---

## 项目中的残差

令

$$
q(\rho_{AB})=(\rho_A,\rho_B).
$$

本例满足

$$
q(\rho_{\mathrm c})=q(\rho_{\mathrm a}),
$$

但后续受力目标不同。

因此，不能为这个单体边缘接口提供覆盖全部允许输入的精确下降映射。项目的 `exact_descent_has_no_carry` 正好给出了这种否定的逻辑形式。

要修复预测，可以保留相关的二体关联；但保留了当前协方差，也不自动保证更长时间和更大控制族下已经完全闭合。

---

# 198．分支模型必须与实际波包和控制过程建立误差桥梁

第 194—196 节使用了有限分支能量。现实的空间波包并不是精确的位置本征态，固定位置也需要控制装置。

因此，需要一个显式实现证书。

## 定义 198.1　分支模型的实现残差

令

$$
J(t):\mathbb C^4\to\mathcal H_{\mathrm{phys}}
$$

为等距嵌入，表示四个逻辑分支如何由实际波包、内部态和控制器实现。

设实际 Hamiltonian 为 \(H_{\mathrm{phys}}(t)\)，理想分支 Hamiltonian 为 \(H_{\mathrm{eff}}(t)\)。

定义

$$
\boxed{
\mathcal R(t)
=
H_{\mathrm{phys}}(t)J(t)
-i\hbar\dot J(t)
-J(t)H_{\mathrm{eff}}(t).
}
\tag{198.1}
$$

其中 \(-i\hbar\dot J\) 不能省略：分支波包或参照本身随时间变化，也会贡献动力学。

---

## 定理 198.1　完整实现误差的积分界

在相应定义域和可微性条件下，

$$
\boxed{
\left\|
U_{\mathrm{phys}}(T,0)J(0)
-
J(T)U_{\mathrm{eff}}(T,0)
\right\|
\le
\frac1\hbar\int_0^T\|\mathcal R(t)\|\,dt.
}
\tag{198.2}
$$

### 证明

对

$$
U_{\mathrm{phys}}(T,t)J(t)U_{\mathrm{eff}}(t,0)
$$

求导，使用两个 Schrödinger 方程，得到被积项与 \(\mathcal R(t)\) 的酉夹乘。积分并取范数即可。∎

该界可进一步控制编码输入的输出迹距离，包括与附加测试参照纠缠的输入。

它要求把波包展宽、反冲、保持位置的控制、路径重组及额外相位纳入同一残差，而不是分别忽略后宣布四分支公式精确实现。

---

## 推论 198.1　可认证的纠缠

设理想输出为第 194 节的纯态 \(|\Psi_\Xi\rangle\)，其最大 Schmidt 概率为

$$
\lambda_{\max}
=
\frac{1+|\cos(\Xi/2)|}{2}.
$$

若实际输出满足

$$
D(\rho_{\mathrm{act}},|\Psi_\Xi\rangle\langle\Psi_\Xi|)
\le\varepsilon,
$$

且

$$
\boxed{
\varepsilon
<
\frac{1-|\cos(\Xi/2)|}{2},
}
\tag{198.3}
$$

则实际输出必纠缠。

### 证明

任何可分态与 \(|\Psi_\Xi\rangle\) 的重叠概率都不超过 \(\lambda_{\max}\)。

迹距离界保证实际重叠概率至少为 \(1-\varepsilon\)。若 \(1-\varepsilon>\lambda_{\max}\)，实际态不可能可分。∎

这是一个充分条件，不是所有纠缠检测协议的最优阈值。

---

## 定理 198.2　有限位移的潮汐估计误差

取第 196 节的对称布局 \(a=b=h\,n\)，\(|n|=1\)。若相位已经解缠，测量误差满足

$$
|\widehat\Xi-\Xi|\le\varepsilon_\Xi,
$$

且邻域内四阶方向导数满足

$$
|D_n^4V|\le M_4,
$$

则

$$
\boxed{
\left|
\frac{\hbar\widehat\Xi}{Th^2}
-
n^{\mathsf T}\operatorname{Hess}V(r)n
\right|
\le
\frac{\hbar\varepsilon_\Xi}{Th^2}
+
\frac{M_4h^2}{12}.
}
\tag{198.4}
$$

### 证明

该布局给出

$$
\Xi
=
\frac{T}{\hbar}
\bigl[V(r+hn)+V(r-hn)-2V(r)\bigr].
$$

使用中心二阶差分的四阶余项，再加入相位测量误差即可。∎

在三维中，选择三个坐标方向及三个对角方向，可以恢复对称 Hessian 的六个独立分量。

但是，测量误差被 \(h^{-2}\) 放大。因此更小的空间分支并不无条件产生更好的曲率估计。

---

# 199．相互作用的量子性、几何解释和因果完成仍然不同

本轮构造的 Hamiltonian 含有直接的双体势。它是低速、近场的有效描述。

它没有显式包含传播中的引力场，因此不能仅凭自伴性和总能量守恒，就宣布已经建立完整的相对论因果传播。

## 命题 199.1　静态有效势不能独自提供全频率因果证书

式（192.1）不包含延迟 Green 函数、辐射自由度或源变化的有限传播机制。

因此，它只能在一个另行证明的有效窗口内替代更完整的局域场模型，不能用来推断任意短时间或跨视界的信息传递。

### 证明

这些对象未包含在状态空间和演化定义中；仅从当前算子无法推出其支持性质。若要证明有限传播，必须给出包含相应自由度的扩展及近似误差。∎

量子场分析表明，静态势相位、场涨落、延迟响应与因果性之间的关系需要共同处理，不能用一个瞬时势模型替代全部实验。([arXiv][5])

---

## 定理 199.1　纠缠可以排除一个明确的经典信息中介类

假设两观察者初始可分，中间过程只允许：

* 各自局部量子操作；
* 经典记录与经典消息；
* 不存在预共享纠缠或额外直接量子作用。

则最终态仍可分。

### 证明

初态可写成乘积态的凸组合。每次局部操作及经典条件更新，只改变对应乘积项及其权重。对步骤数归纳，最终仍是乘积态的凸组合。∎

因此，经过第 198 节认证的纠缠可以排除这一个操作类。

但它不能单独证明：

$$
\text{唯一的量子引力理论},
\qquad
\text{传播引力子的存在},
\qquad
\text{某种时空拓扑}.
$$

用经典测量和反馈实现平均引力作用的模型，会同时引入额外噪声，并且属于需要与上述相干相互作用区分的候选。([arXiv][6])

**测到非局部分解的相位，不等于已经识别了它的物理来源。**电磁、机械控制和共享辅助系统也必须排除或纳入误差模型。

---

# 200．本轮得到的是一个跨实验的一致性约束

本轮最重要的统一对象不是某一个“量子引力参数”，而是同一个联合能量函数及其不同读数：

$$
\boxed{
\mathcal E(e_A,e_B,R)
=
e_A+e_B+\kappa(R)e_Ae_B.
}
$$

它同时决定：

$$
\boxed{
n_A=\partial_{e_A}\mathcal E,
\qquad
n_B=\partial_{e_B}\mathcal E;
}
$$

$$
\boxed{
F_A=+\nabla_R\mathcal E,
\qquad
F_B=-\nabla_R\mathcal E;
}
$$

$$
\boxed{
\Xi
=
-\frac{T}{\hbar}
\Delta_A\Delta_B\mathcal E.
}
$$

这里，\(\Delta_A,\Delta_B\) 可以表示选定能级差，也可以表示选定空间分支差。

因此：

> **钟速修正、机械反作用与纠缠相位不能分别任意拟合。它们必须能够作为同一个联合实现的不同导数或有限差分，同时成立。**

---

## 形式化依赖

本轮按提交

```text
7964bc54f38cf4d24bf7b702ca3ec1d5f5b89a1e
```

核对了项目中的两个相关基础模块：

`ExactDescentNoCarry.lean` 用于判定单体边缘接口是否足以支持后续受力目标。

`ConservationAutonomySeparation.lean` 区分能量守恒与局部相位过程的自主性。

新增证明可以分层为：

| 层次    | 应形式化的对象             |
| ----- | ------------------- |
| 有限能量层 | 互易偏导、双线性能量、有限能级差    |
| 有限量子层 | 四分支相位、局部相位等价、纠缠判据   |
| 运动分析层 | 自伴域、总动量、相对坐标与反冲     |
| 几何读取层 | 混合空间差分、Hessian、潮汐误差 |
| 实现层   | 分支嵌入、控制残差、完整过程误差    |

本轮的 **16 项精确代数检查均通过**，包括能量互易性、重复计数恒等式、共同—相对动能分解、Newton 势 Hessian、有限分支纠缠及相同边缘态下的相互作用能量差。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_reciprocal_tidal_interaction.py)
[核验结果](sandbox:/mnt/data/observer_formalization/reciprocal_tidal_interaction_checks.json)

本轮没有运行 Lean 编译。这些检查支持所列恒等式与有限实例，不替代一般分析定理的机器证明，也不验证模型已经唯一对应现实引力。

---

# 结论

上一轮说明：选择自由落体参照可以消去共同加速度，但不能消去潮汐结构。

这一轮继续证明：

**当两位观察者都成为物理源时，同一相互作用不仅改变相对运动，也改变双方的钟，并能在相干实验中产生不可局部分解的相位。**

因此，当前理论进一步形成一个闭合要求：

$$
\boxed{
\text{谁改变了谁的钟}
}
$$

$$
\boxed{
\text{谁向谁传递了动量}
}
$$

$$
\boxed{
\text{哪些联合分支形成了纠缠}
}
$$

必须由同一个总能量、同一个状态和同一套控制实现解释。

最值得保留的公式是

$$
\boxed{
\Xi_{\mathrm{space}}
\approx
-\frac{\mu T}{\hbar}
a^{\mathsf T}\mathcal T_{\mathrm{rel}}\,b.
}
$$

在明确的弱场双体模型中，它把**关系运动的潮汐变化**与**联合量子相位**连接起来，同时保留可计算的有限位移误差。

这使“量子观察者是中心”获得了更严格的含义：

> **观察者可以成为描述的原点，但不能成为反作用的例外。它既是读取者，也是源；既有内部钟，也有反冲；既能保存局部记录，也可能通过相互作用与其他观察者形成不可分割的联合状态。**

物理时空的进一步重建，应当由这些不同读数能否共同通过同一个动力学模型来决定，而不是先选定一张几何，再让观察者的钟、受力和量子关联分别去适应它。

[1]: https://arxiv.org/html/1507.01955v3 "https://arxiv.org/html/1507.01955v3"
[2]: https://arxiv.org/html/1707.06036v2 "https://arxiv.org/html/1707.06036v2"
[3]: https://www.pnas.org/doi/10.1073/pnas.1616427114 "https://www.pnas.org/doi/10.1073/pnas.1616427114"
[4]: https://davidtong.org/teaching/general-relativity/grhtml/S3.html "https://davidtong.org/teaching/general-relativity/grhtml/S3.html"
[5]: https://arxiv.org/abs/2308.03093 "https://arxiv.org/abs/2308.03093"
[6]: https://arxiv.org/abs/1401.0946 "https://arxiv.org/abs/1401.0946"
**可以把这条直觉发展成一个明确的“因果量子波—有限记录—受限控制”模型。最有价值的推进，不是宣布“宇宙其实就是波”，而是证明：同一个量子过程，怎样同时表现为传播、干涉、记忆、选择和有限的信息处理。**

但有三个关系必须先调整：

**观察者固定在描述原点，不意味着观察者的物理状态不变。**

**光速可以限制信息影响传播得多远，却不能直接等同于每秒传输多少比特。**

**观察者遗漏了信息，与量子测量具有概率性，可以有关联，但并不是同一个命题。**

下面保留你的直觉，同时把这些区别变成可以继续形式化的结构。

# 因果量子波、有限刷新与行动可达性

## ——量子观察者—关系时空理论第二百零一至第二百一十节增订

---

# 201．观察者是固定原点，但不是静止的量子态

我们应当把“中心不动点”定义为：

> **全部可读关系，都以同一个观察者接口为参照；观察者的记忆、内部钟和行动寄存器仍然参与演化。**

如果一个观察者的完整密度矩阵在所有实际交互后都严格不变，那么它就不能仅靠该状态的变化形成新的可区分记忆。

所以应区分：

$$
\boxed{
\text{参照身份固定}
\ne
\text{物理状态固定}.
}
$$

## 定义 201.1　观察者中心模型

取一个有限有效模型：

$$
\mathcal H
=
\mathcal H_C
\otimes\mathcal H_M
\otimes\mathcal H_A
\otimes\mathcal H_E.
$$

其中，\(C\) 是内部钟，\(M\) 是记忆，\(A\) 是行动控制，\(E\) 是其余可交互结构。

给定允许过程族：

$$
\Gamma=\{\Phi_a:a\in\mathcal A_{\mathrm{adm}}\}.
$$

每个 \(\Phi_a\) 必须有量子操作实现，而不只是写在纸上的状态映射。

对结果 \(b\)，测量由量子仪器表示：

$$
\mathcal I_b^a,
\qquad
\sum_b\mathcal I_b^a
\text{ 为完全正、保迹映射}.
$$

于是：

$$
\boxed{
p(b\mid\rho,a)
=
\operatorname{Tr}\mathcal I_b^a(\rho).
}
\tag{201.1}
$$

观察者并不是在模型外面“选择宇宙”。它的行动寄存器、记录形成与后续反馈，都属于这个联合过程。

特别地，若采用有限组受控酉操作：

$$
U_{\mathrm{ctrl}}
=
\sum_a|a\rangle\langle a|_A\otimes U_a,
$$

那么行动选择本身已经有一个量子实现。

**“以我为中心”在这里是一种关系组织方式，不是给予观察者违反其他动力学条件的特权。**

---

# 202．信息流能否写成波？可以，但要保留波的实际作用结构

你说“时空变换都成为信息流，然后把信息流波化”，有两个层次。

第一层是：

$$
\text{量子演化具有相位与叠加结构}.
$$

第二层是更强的：

$$
\text{这些相位和叠加能够局域传播，
并重建共同的物理时空}.
$$

第一层可以直接构造；第二层需要额外的局域性、共同标定和连续极限证明。

## 定义 202.1　无预设米秒的量子传播网络

先取一个有限有向接口网络。每个接口有若干输入、输出模式，模式空间为：

$$
\mathcal H_{\mathrm{mode}}
=
\bigoplus_x\mathbb C^{d_x}.
$$

这里 \(x\) 只是交互接口标签，不先把它解释成三维坐标。

定义：

$$
C_a=\bigoplus_x C_{a,x},
$$

其中每个 \(C_{a,x}\) 是局部酉混合；再令 \(S\) 是把输出端口接到下一输入端口的置换。

一步演化为：

$$
\boxed{
U_a=SC_a.
}
\tag{202.1}
$$

先把步数 \(n\) 理解为交互组合次数，而不是已经标定的秒。

## 定理 202.1　局域因果波的存在

\(U_a\) 是酉算子。

当行动固定时，存在正交谱分解：

$$
U=\sum_\alpha e^{-i\theta_\alpha}P_\alpha,
$$

因此：

$$
\boxed{
|\psi_n\rangle
=
\sum_\alpha e^{-in\theta_\alpha}P_\alpha|\psi_0\rangle.
}
\tag{202.2}
$$

每个谱分量都以自己的相位角反复变化。

### 证明

置换 \(S\) 与各局部 \(C_{a,x}\) 均酉，因此其乘积酉。

有限维酉算子是正规算子，谱定理给出上述分解。取 \(n\) 次幂即可。∎

这已经是一种严格意义上的“波”：它具有振幅、相位、叠加与干涉，不需要先把水面或电磁介质放进定义。

局域量子自动机从类似结构中恢复长波的 Weyl、Dirac 型传播，是已有的研究路线；但具体结果依赖局域性、均匀性、内部维数等条件。([arXiv][1])

### 波化不能省略的三个限制

**第一，波不一定是三维空间里的经典标量波。**多体量子态可以位于联合配置空间，纠缠一般不能压缩成每个位置各自拥有一个独立经典波。

**第二，谱分解不等于已经解释了物理。**任何有限酉演化都能写成式（202.2），但不同的 \(S,C_a\) 给出不同世界。

**第三，不能从一个离散 \(U\) 随意取对数后，就假定得到了局域连续 Hamiltonian。**矩阵对数存在，不保证其对应生成元仍然局域。

所以，更准确的主张是：

$$
\boxed{
\text{我们选择并研究一种局域相干传播结构，
而不是仅把任意数据换成“波”的名称。}
}
$$

---

# 203．观察者怎样把波变成记忆？记录会改变可用的干涉

这一节可以把“波”“记忆”和“选择能力”接在同一个有限模型上。

## 定义 203.1　双路径与量子记录

取两条模式 \(|0\rangle,|1\rangle\)，以及记录态 \(|e_0\rangle,|e_1\rangle\)。

定义：

$$
\boxed{
|\Psi_\phi\rangle
=
\frac{
|0\rangle|e_0\rangle
+
e^{i\phi}|1\rangle|e_1\rangle
}{\sqrt2}.
}
\tag{203.1}
$$

令：

$$
\gamma=\langle e_0|e_1\rangle.
$$

\(\phi\) 是观察者通过一个实际控制装置能够调节的相对相位。

对路径实施一次平衡混合，再读取出口 \(0\)。

## 定理 203.1　记录重叠决定相位控制的范围

出口概率为：

$$
\boxed{
p_0(\phi)
=
\frac12\left[
1+\operatorname{Re}(e^{i\phi}\gamma)
\right].
}
\tag{203.2}
$$

因此，当观察者只能调节 \(\phi\) 时：

$$
\boxed{
p_0\in
\left[
\frac{1-|\gamma|}{2},
\frac{1+|\gamma|}{2}
\right].
}
\tag{203.3}
$$

### 证明

混合后出口 \(0\) 对应的记录振幅为：

$$
\frac{|e_0\rangle+e^{i\phi}|e_1\rangle}{2}.
$$

取范数平方得到式（203.2）。相位可以使实部遍历
\([-|\gamma|,|\gamma|]\)，得到式（203.3）。∎

这给你的“在波中选择”一个非常具体的含义：

> **观察者通过改变相对相位，改变未来出口的概率；但它能改变多少，受到尚可利用的相干限制。**

如果：

$$
|\gamma|=1,
$$

没有记录区分两条路径，调相位可以把出口概率从零调到一。

如果：

$$
\gamma=0,
$$

记录已经能够完美区分路径，那么仅靠路径相位控制：

$$
p_0(\phi)=\frac12
$$

始终不变。

## 定理 203.2　记忆可区分性与相位控制范围互补

对等先验的两个纯记录态，其最优迹距离区分度为：

$$
D_{\mathrm{record}}
=
\sqrt{1-|\gamma|^2}.
$$

定义相位控制窗口宽度：

$$
W_{\mathrm{phase}}
=
\sup_\phi p_0(\phi)-\inf_\phi p_0(\phi)=|\gamma|.
$$

则：

$$
\boxed{
D_{\mathrm{record}}^2+W_{\mathrm{phase}}^2=1.
}
\tag{203.4}
$$

证明由两纯态迹距离公式与定理203.1直接得到。这是路径可区分性—干涉可见度互补关系在当前控制任务中的表达。([APS Journals][2])

例如：

$$
|e_0\rangle=|0\rangle,
\qquad
|e_1\rangle=\frac35|0\rangle+\frac45|1\rangle,
$$

则：

$$
D_{\mathrm{record}}=\frac45,
\qquad
p_0(\phi)=\frac12+\frac3{10}\cos\phi,
$$

所以：

$$
\boxed{p_0\in[1/5,4/5].}
$$

**这不是“记忆越多，人就越没有自由”的普遍定理。**它只说明：在这个特定实验中，已经保存的路径区别，会限制仅靠相位调节能够完成的事情。

要恢复更大的控制范围，必须实际操作、重新组合或撤销相关记录，不能一边保留完美的路径记录，一边假装它没有影响干涉。

---

# 204．“自由意志”与“命运”可以先形式化为控制与可达性

数学上最稳妥的做法，是先不把形而上的自由意志写成物理公理。

我们可以研究一个操作性概念：

$$
\boxed{
\text{观察者在自己的记录与资源条件下，
能够实施哪些干预，并怎样改变未来统计。}
}
$$

## 定义 204.1　有预算的可达态集合

设当前联合态为 \(\rho\)，允许协议集合为 \(\Gamma_B\)，其中 \(B\) 限制时间、能量、控制端口或记忆资源。

定义：

$$
\boxed{
\mathcal R_B(\rho)
=
\{\Phi_\pi(\rho):\pi\in\Gamma_B\}.
}
\tag{204.1}
$$

对目标效果 \(E_b\)，定义可达概率集合：

$$
\boxed{
\mathcal P_{b,B}(\rho)
=
\left\{
\operatorname{Tr}[E_b\Phi_\pi(\rho)]:
\pi\in\Gamma_B
\right\}.
}
\tag{204.2}
$$

这两个对象对应你直觉中的两部分：

**行动能力**：改变协议 \(\pi\)，从而改变可达状态和概率。

**处境约束**：当前状态、已发生的记录、动力学和资源预算，限制 \(\mathcal R_B(\rho)\)。

不过，它们不自动判定哲学上的自由意志是否存在。随机结果也不等于自由选择。

## 定理 204.1　守恒结构约束所有允许选择

设一个投影 \(P\) 与全部允许酉控制可交换：

$$
[U_a,P]=0.
$$

则任意有限控制序列都保持：

$$
\boxed{
\operatorname{Tr}(P\rho_{\mathrm{out}})
=
\operatorname{Tr}(P\rho_{\mathrm{in}}).
}
\tag{204.3}
$$

### 证明

每一步有：

$$
\operatorname{Tr}(PU_a\rho U_a^\dagger)
=
\operatorname{Tr}(U_a^\dagger PU_a\rho)
=
\operatorname{Tr}(P\rho).
$$

对步骤数归纳。∎

因此，观察者不能通过“选择某种波”跳出全部允许操作共同保持的约束。

另一方面，“只能从已经列出的世界分支里挑一个”也不完全准确。行动可以改变 Hamiltonian、耦合和干涉，使之后的可达集合改变。未来不一定是一个预先固定、彼此独立的菜单。

**更好的表述是：观察者能够修改后续过程，但只能通过当前可实现的操作修改，而不能直接指定任意结果。**

例如，第203节中可以选择相位 \(\phi\)，却不能在一个固定的 \(p_0=1/2\) 测量中，额外命令本次结果必须为零。

---

# 205．刷新率是物理过程，不是宇宙统一播放速度

波模型至少有四种不同频率：

| 对象     | 所描述的内容             |
| ------ | ------------------ |
| 波的相位频率 | 某个相干模式怎样积累相位       |
| 频差或拍频  | 不同模式怎样产生可读变化       |
| 采样频率   | 装置多久询问一次某个读数       |
| 记录更新率  | 观察者多久形成一个新的可区分内部记录 |

它们可以相关，但不能直接相等。

## 定理 205.1　高相位频率不保证高刷新率

若系统处于能量本征态：

$$
H|\psi\rangle=E|\psi\rangle,
$$

则：

$$
|\psi(\tau)\rangle=e^{-iE\tau/\hbar}|\psi\rangle,
$$

但：

$$
\boxed{
\rho(\tau)=|\psi\rangle\langle\psi|
}
$$

恒定。

### 证明

整体相位在密度矩阵中相消。∎

所以，一种波可以具有很高的相位旋转频率，却没有给这个孤立系统提供任何可读的走时记录。

真正可读的变化依赖能级差、相干和比较协议。

---

## 定理 205.2　固定刷新间隔存在精确混叠

固定采样间隔 \(\Delta\tau>0\)。比较：

$$
H_1=0,
$$

$$
H_2=\frac{2\pi\hbar}{\Delta\tau}|1\rangle\langle1|.
$$

对任意整数 \(n\)：

$$
\boxed{
e^{-iH_1n\Delta\tau/\hbar}
=
e^{-iH_2n\Delta\tau/\hbar}
=
I.
}
\tag{205.1}
$$

但在半个采样间隔：

$$
e^{-iH_2\Delta\tau/(2\hbar)}=Z,
$$

与 \(H_1\) 不同。

### 证明

直接计算指数。∎

因此，一个只在固定时刻读取的观察者，可以把两种真实不同的动力学合并。

这就是一个明确的**刷新接口残差**，而不是宇宙真的在两次读取之间什么都没发生。

---

## 量子钟更新还受到能量条件约束

对于时间无关 Hamiltonian 下的纯态，从当前状态演化到正交状态所需时间满足：

$$
\boxed{
\tau_\perp
\ge
\max\left\{
\frac{\pi\hbar}{2\Delta E},
\frac{\pi\hbar}{2(\langle H\rangle-E_0)}
\right\}.
}
\tag{205.2}
$$

这里 \(E_0\) 为能量下界。这是 Mandelstam–Tamm 与 Margolus–Levitin 型界；它约束的是物理可区分的状态变化，不是任意软件指令的统一耗时。([arXiv][3])

因此，要把“刷新率”变成一个物理量，必须说明：

$$
\boxed{
\text{什么算一次新记录}
+
\text{需要多大区分度}
+
\text{使用什么 Hamiltonian 与资源}.
}
$$

仅凭“观察者有限”，还不足以给出一个具体的普适刷新频率。

---

# 206．光速限制传播距离，不直接限制每秒比特数

你的直觉在这里可以保留一半：

> 光速确实可以作为因果影响传播的上界进入信息理论。

但不能把：

$$
c
$$

直接定义为：

$$
\text{每单位时间最多传输的信息量}.
$$

因为：

$$
[c]=\mathrm{m/s},
\qquad
[\text{信息率}]=\mathrm{bit/s}.
$$

这不仅是量纲区别，也对应不同的实验约束。

## 定义 206.1　因果速度与信息通量

在第202节的网络中，若一步最多跨越一条边，标定边长为 \(\ell\)、钟间隔为 \(\tau_0\)，则：

$$
\boxed{
c_*=\frac{\ell}{\tau_0}.
}
\tag{206.1}
$$

它限制经过 \(n\) 步的影响范围。

但若在同一条空间方向上增加更多独立端口、频带或并行载体，信息通量可以增加，而 \(c_*\) 不变。

**传播速度回答“最早什么时候能够影响那里”；容量回答“到达以后，能够可靠区分多少消息”。**

## 定理 206.1　有限接收空间的信息上限

设一轮消息 \(X\) 被编码为一个 \(d\) 维接收系统中的状态 \(\rho_x\)，没有另行提供与发送端预共享的纠缠资源。

对任意接收测量结果 \(Y\)：

$$
\boxed{
I(X:Y)
\le
S\!\left(\sum_xp_x\rho_x\right)
-\sum_xp_xS(\rho_x)
\le
\log_2d.
}
\tag{206.2}
$$

第一步是 Holevo 界，第二步来自有限维熵上界。它限制可读经典信息，而不把波函数的连续复系数当作可以免费逐位读出的无限数据。([APS Journals][4])

因此，在固定时隙、每步接收 \(q\) 个 \(d\) 维载体的这类模型中：

$$
\boxed{
R_{\mathrm{in}}
\le
\frac{q\log_2d}{\tau_0}.
}
\tag{206.3}
$$

预共享纠缠、额外参照和辅助信道改变资源账本时，必须重新写容量问题，不能无条件套用式（206.3）。

类似地，若最终保留记忆只有 \(d_M\) 维，那么只读取这份最终记忆，不能恢复超过 \(\log_2d_M\) 比特的任意经典消息；持续输出到其他装置，相当于扩大了总记录系统。

所以，对于“已经波化的信息系统”，有限处理能力至少由三个独立因素约束：

$$
\boxed{
\text{可到达的因果范围}
,\quad
\text{可访问的模式数}
,\quad
\text{形成新可区分记录的速率}.
}
$$

光速、量子速度极限与存储自由度分别约束它们的不同部分。把这些物理资源联合分析已有明确研究传统，但没有一个无条件公式把三者压成同一个“宇宙比特率”。([arXiv][5])

---

# 207．把“逃逸率”变成真正连接波动与刷新需求的量

这里可以直接利用项目已经建立的观察效果闭包。

仓库区分了：当前接口删除了多少方向，以及这些方向以后会不会重新进入可见读数；两者不是同一个量。它还给出了 Hamiltonian 交换子生成的未来效果空间。

下面给出一种**新的动力型逃逸速率**。它不替代项目已有的集合残差或预算逃逸谱。

## 定义 207.1　可见效果空间与动力型逃逸速率

在有限维 Hermitian 算子空间上，使用 Hilbert–Schmidt 内积。

设：

$$
\mathcal S
$$

为当前记录足以计算期望值的实线性空间，并包含 \(I\)。

令 \(\Pi\) 为投影到 \(\mathcal S\) 的正交投影。定义 Heisenberg 生成元：

$$
\mathcal L(E)=\frac{i}{\hbar}[H,E].
$$

定义：

$$
\boxed{
\ell_H(\mathcal S)
=
\|(I-\Pi)\mathcal L\Pi\|_{2\to2}.
}
\tag{207.1}
$$

它的单位是：

$$
[\ell_H]=1/\mathrm{s}.
$$

它衡量：**当前可见的读数沿动力学向后追踪时，以多快速度需要额外的、当前未保存的方向。**

## 定理 207.1　零逃逸等价于可见空间的动力闭合

有：

$$
\boxed{
\ell_H(\mathcal S)=0
\iff
\mathcal L(\mathcal S)\subseteq\mathcal S.
}
\tag{207.2}
$$

此时：

$$
e^{\tau\mathcal L}\mathcal S\subseteq\mathcal S.
$$

### 证明

第一项就是定义中的非对角块为零。

有限维中，若 \(\mathcal L\) 保持 \(\mathcal S\)，则其全部幂及指数也保持 \(\mathcal S\)。∎

## 定理 207.2　刷新间隔内的预测误差

对 \(E\in\mathcal S\)，定义当前模型内的预测：

$$
\overline E(\tau)
=
e^{\tau\Pi\mathcal L\Pi}E.
$$

则：

$$
\boxed{
\|e^{\tau\mathcal L}E-\overline E(\tau)\|_2
\le
|\tau|\,\ell_H(\mathcal S)\,\|E\|_2.
}
\tag{207.3}
$$

### 证明

\(\mathcal L\) 在 Hilbert–Schmidt 内积下为反对称生成元，其指数保持范数；\(\Pi\mathcal L\Pi\) 在 \(\mathcal S\) 上同样如此。

Duhamel 公式给出：

$$
e^{\tau\mathcal L}E-\overline E(\tau)
=
\int_0^\tau
e^{(\tau-s)\mathcal L}
(I-\Pi)\mathcal L\Pi
e^{s\Pi\mathcal L\Pi}E\,ds.
$$

取范数即可。∎

若 \(\|E\|_2\le1\)，希望每次更新间隔中的这项误差不超过 \(\varepsilon\)，则一个充分条件是：

$$
\boxed{
\ell_H(\mathcal S)\,\Delta\tau\le\varepsilon.
}
\tag{207.4}
$$

于是你说的“刷新率”与“逃逸率”第一次获得了一个直接的定量连接：

$$
\boxed{
f_{\mathrm{refresh}}
\ge
\frac{\ell_H(\mathcal S)}{\varepsilon}
}
\tag{207.5}
$$

可以作为这类逐帧预测证书的充分设计条件。

### 不能把它夸大成什么？

它不是任何观察者都必须满足的宇宙刷新定律，也不是必要且最优的采样率。

\(\overline E(\tau)\) 首先是线性预测量；若要把整个近似映射当作实际量子操作，还必须证明正性和完全正性。

### 一个精确例子

取：

$$
H=\frac{\hbar\omega}{2}X,
\qquad
\mathcal S=\operatorname{span}_{\mathbb R}\{I,Z\}.
$$

则：

$$
\mathcal L(Z)=\omega Y,
\qquad
\ell_H(\mathcal S)=|\omega|.
$$

两态：

$$
\rho_\pm=\frac{I\pm Y}{2}
$$

在当前接口上相同，但后续 \(Z\) 读数为：

$$
\langle Z\rangle_\pm(\tau)=\pm\sin\omega\tau.
$$

**这是真正的“当前没读到的波相位，后来逃回可见读数”。**

---

# 208．量子概率不能直接等同于逃逸率

这是你当前直觉中最需要继续深挖，也最不能提前当作结论的部分。

## 定理 208.1　没有状态压缩残差，仍然可以有非零测量随机性

设观察者完整知道量子态：

$$
\rho=|+\rangle\langle+|,
$$

并测量：

$$
E_0=|0\rangle\langle0|,
\qquad
E_1=|1\rangle\langle1|.
$$

则：

$$
\boxed{
p_0=p_1=\frac12.
}
\tag{208.1}
$$

如果状态接口为恒等映射 \(q(\rho)=\rho\)，它没有因合并不同量子态而产生的预测残差，但结果分布仍不是确定的。

### 证明

直接计算：

$$
\operatorname{Tr}(\rho E_0)
=
\operatorname{Tr}(\rho E_1)=\frac12.
$$

恒等接口不合并不同状态。∎

因此：

$$
\boxed{
\text{能够精确预测概率分布}
\ne
\text{能够预先指定单次结果}.
}
$$

而且，概率也不是“只要逃逸没封住，所有结果就一定都有份”。

对一个结果算子 \(K_b\)：

$$
p_b=\operatorname{Tr}(K_b\rho K_b^\dagger)
=
\|K_b\rho^{1/2}\|_2^2.
$$

所以：

$$
\boxed{
p_b=0
\iff
K_b\rho^{1/2}=0.
}
\tag{208.2}
$$

守恒约束、不可达性和精确相消，都可以让某些结果严格为零。

---

## 为什么是振幅平方，而不是任意“逃逸权重”？

有限维中有一条成熟路线：

若对每个量子效果 \(0\le E\le I\) 赋予概率 \(w(E)\)，要求归一化、正性，以及对可合并效果的加法一致性，那么该概率赋值必具有：

$$
\boxed{
w(E)=\operatorname{Tr}(\rho E).
}
\tag{208.3}
$$

证明思路是：加法与正性先给出有理齐次性，再由单调性得到实齐次性；然后扩张成 Hermitian 矩阵上的正线性泛函，最终由一个密度矩阵表示。这是适用于一般效果的 Gleason–Busch 型结果。([arXiv][6])

这条路线说明，Born 规则可以由**已经选择的量子效果结构及概率一致性条件**导出。

但它没有证明这些条件本身来自项目的某个逃逸率。

项目的逃逸谱文档实际上明确给定了：

$$
q,\quad T,\quad\Gamma,\quad c,\quad\nu,
$$

即观察接口、预测目标、允许区分语言、成本以及残差集合上的权重。该权重并不是仅由“有遗漏”三个字唯一产生的 Born 测度。

因此，真正值得研究的桥梁是：

$$
\boxed{
\text{哪些操作一致性与组合条件，
能把项目的残差权重约束成量子概率？}
}
$$

而不是先写：

$$
p=\text{逃逸率},
$$

再把尚未解释的概率藏进逃逸率定义中。

### 隐藏变量解释还必须面对什么？

如果希望把量子随机性全部解释成“未解码的经典波变量”，就必须明确这些变量如何处理不同测量选择。

在局域隐藏变量与相应设置独立性条件下，Bell 型相关有严格上界；量子理论的关联可以超出这个上界。因此，普通的局域、预先赋值的经典波噪声，不足以无条件复现全部量子实验。([APS Journals][7])

这不排除所有更深层解释，而是要求它说明自己在哪一项结构上不同。

另外，“所有可能性都真实存在”属于对量子态的进一步解释，不由非零概率或不可消除残差本身唯一决定。

---

# 209．现在能够引入哪些常数？应按角色引入，而不是按漂亮数值引入

在这个模型中，常数不是装饰。它们连接不同种类的可测量量。

| 常数或参数                  | 在理论中的作用             | 不能直接等同于        |
| ---------------------- | ------------------- | -------------- |
| \(c\)                  | 长度与时间的因果标定；共同信号锥    | 每秒比特数          |
| \(\hbar\)              | 能量差、作用量与量子相位之间的尺度   | 一个普遍固定的刷新间隔    |
| \(k_B\)                | 温度、能量和熵单位之间的联系      | 每次任意计算都消耗的固定能量 |
| \(G\)                  | 在指定引力实现中连接源能量与几何反作用 | 信息逃逸率本身        |
| \(\Delta\tau_O\)       | 某观察者某协议的更新间隔        | 全宇宙唯一时钟        |
| \(\ell_H(\mathcal S)\) | 当前接口的动态预测缺失尺度       | 单次量子结果的概率      |

其中，\(c,h,k_B\) 的 SI 数值参与单位定义。例如：

$$
c=299\,792\,458\ {\rm m/s}
$$

是当前 SI 中的精确定义值。单靠一个无量纲组合模型，不会独立选出“米”和“秒”并强迫出现这个十进制数。([BIPM][8])

更适合优先研究的是无量纲关系，例如：

$$
\boxed{
\frac{\Delta E\,\Delta\tau_O}{\hbar},
\qquad
\ell_H(\mathcal S)\Delta\tau_O,
\qquad
\frac{L}{c\Delta\tau_O},
\qquad
\frac{k_BT\Delta\tau_O}{\hbar}.
}
\tag{209.1}
$$

它们分别比较：

能量资源与记录速度；遗漏增长与刷新间隔；传播距离与等待时间；热尺度与相位尺度。

这使“有限处理能力”成为一个有内容的判断：

> **观察者不是解码一个无限精确的波面，而是在有限的可达区域、能量预算、模式数和记录空间中，实施有限分辨率的实验。**

而且，一个观察者改用更快的仪器，并不会仅因此改变现实的光速或自动造成相对论时间膨胀。必须将仪器内部钟与其他钟的比较放回完整物理模型。

---

# 210．下一阶段真正需要攻克的难点

你的直觉目前已经能够形成一个连贯研究模型，但要成为更独立的物理理论，下列问题不能靠重新命名跳过。

| 难点                  | 必须具体证明什么                                                     |
| ------------------- | ------------------------------------------------------------ |
| **量子结构从哪里来？**       | 为什么基础接口应由复 Hilbert 空间、正算子和完全正过程表示，而不是某种更一般概率理论？              |
| **波的局域性怎样产生共同空间？**  | 为什么不同模式共享相容的传播锥、钟尺与维数，而不是各自一张有效几何？                           |
| **Born 权重与逃逸如何连接？** | 从哪些独立的组合和一致性条件得到 \(\operatorname{Tr}(\rho E)\)，且不把它提前藏进残差测度？ |
| **有限观察者怎样持续存在？**    | 记忆、参照和控制经过反作用后是否仍稳定；哪些过程允许精确闭合，哪些只能近似闭合？                     |
| **行动集合怎样被物理生成？**    | 哪些相位、模式和耦合真的可控，控制成本与不可达子空间如何计算，而不是默认观察者能调任意旋钮？               |
| **有没有普遍刷新尺度？**      | 若提出基础离散更新，它如何与不同观察者的时间标定相容；哪些实验能区分基础离散性和仪器采样？                |
| **如何确定常数与动力学？**     | 哪些是单位选择，哪些是经验参数，哪些无量纲组合能从具体模型唯一计算，并接受反例检验？                   |

这些不是同一个问题的不同名字。特别是：

$$
\boxed{
\text{有限信息处理}
\not\Rightarrow
\text{自动获得 Born 规则};
}
$$

$$
\boxed{
\text{有波与干涉}
\not\Rightarrow
\text{自动获得共同洛伦兹时空};
}
$$

$$
\boxed{
\text{存在概率}
\not\Rightarrow
\text{已经证明自由意志或宿命}.
}
$$

## 与项目结构的对应

本次按提交

```text
c2154d8cb54ad225b09f77ad29ba09cfd1c002b7
```

核对了相关定义。

当前可以把模型组织为：

$$
\boxed{
\mathfrak O
=
\left(
\text{量子传播网络},
\text{观察者钟与记忆},
\Gamma_B,
\mathcal S,
\text{实际仪器},
\text{资源与误差证书}
\right).
}
$$

其中：

**CUT** 指定观察者保存哪些读数，而不是笼统地“看见了一部分波”。

**FLOW** 指定实际传播、干涉、记录和反馈过程。

**ADMIT** 指定哪些操作、能量、模式和初态合法。

**ANCHOR** 提供具体制备与结果记录；预测分布本身不是一次实际结果。

**Residual** 则始终相对于目标定义：遗漏了路径相位、遗漏了高频动力学、遗漏了控制器记忆，可能是三种不同的残差。

项目已有的精确下降定理可以判断某个简化接口是否足够；已有的效果闭包可以寻找需要补充的未来读数方向。它们不能未经证明地把“遗漏量”变成全部量子概率的统一来源。

本轮对双路径的 \(p_0=\tfrac12+\tfrac3{10}\cos\phi\)、记录区分度 \(4/5\)、采样混叠以及 Pauli 模型的动力逃逸块进行了精确符号核验。上述新增综合结构尚未进行 Lean 编译。

---

# 结论：你的直觉可以保留成什么？

可以保留成下面这段更准确的理论陈述：

> **观察者是一个保持参照身份、但内部持续变化的有限量子系统。它面对的不是必须预先摆好的时空场景，而是一组具有局域传播、相位和干涉结构的可实施交互。**
>
> **观察者把其中一些关联解码为记忆，通过允许的控制改变后续干涉与可达概率；它能够改变什么，取决于当前状态、因果可达性、已形成记录和资源预算。**
>
> **当这些交互的钟与信号关系共同满足几何一致性时，时空成为其有效描述；当有限刷新或过粗接口遗漏了未来会回流的方向时，就产生可计算的预测残差。**

其中最值得继续保留的三条新联系是：

$$
\boxed{
\text{路径记忆可区分性}
\longleftrightarrow
\text{相位控制能够改变概率的范围};
}
$$

$$
\boxed{
\text{动力型逃逸速率}\times\text{刷新间隔}
\longrightarrow
\text{有限时间预测误差};
}
$$

$$
\boxed{
\text{因果传播速度}
+\text{可访问模式数}
+\text{记录形成速度}
\longrightarrow
\text{观察者的信息处理边界}.
}
$$

**最需要保留为待证明问题的，则是“量子概率是否能够由逃逸结构推出”。**现有模型已经足以证明：普通的预测遗漏与 Born 随机性并不相同。真正的突破必须给出连接二者的新结构，同时复现干涉、严格零概率、跨测量一致性与量子关联，而不是把这些要求重新装进“逃逸率”的定义。

因此，我们现在研究的可以不是“一个人从预先存在的命运波中挑选结局”，而是：

$$
\boxed{
\text{一个有限量子观察者，
如何在受因果与资源约束的波动过程中，
形成记忆、实施控制，并建立可预测的世界。}
}
$$

[1]: https://arxiv.org/abs/1306.1934 "[1306.1934] Derivation of the Dirac Equation from Principles of Information Processing"
[2]: https://link.aps.org/doi/10.1103/PhysRevLett.77.2154 "Fringe Visibility and Which-Way Information: An Inequality | Phys. Rev. Lett."
[3]: https://arxiv.org/html/quant-ph/9710043v2 "The maximum speed of dynamical evolution"
[4]: https://link.aps.org/doi/10.1103/PhysRevA.92.012328 "Hierarchy of bounds on accessible information and informational power | Phys. Rev. A"
[5]: https://arxiv.org/abs/quant-ph/9908043 "[quant-ph/9908043] Ultimate physical limits to computation"
[6]: https://arxiv.org/html/quant-ph/9909073v3 "Quantum states and generalized observables:a simple proof of Gleason’s theorem"
[7]: https://link.aps.org/doi/10.1103/PhysicsPhysiqueFizika.1.195 "On the Einstein Podolsky Rosen paradox | Physics Physique Fizika"
[8]: https://www.bipm.org/en/measurement-units/si-defining-constants "Defining constants - BIPM"
**这轮可以把“观察者在波中选择”推进成一个更强、也更可形式化的命题：**

> **观察者能够实施哪些行动，决定了哪些信息可以被安全忽略。一个足以预测被动观察的模型，未必足以预测主动干预。**

这会把你提出的波、选择、记忆、刷新率和逃逸，接入同一套结构，而不是分别给它们一个比喻。

同时，还能证明一个重要限制：

$$
\boxed{
\text{增加刷新次数}
\ne
\text{自动增加对原过程的了解}.
}
$$

如果刷新通过真实测量实现，它可能改变被读取的波。于是必须区分：

$$
\text{补足预测信息},
\qquad
\text{改变被预测过程}.
$$

# 受控波动、预测完成与有限刷新的物理边界

## ——量子观察者—关系时空理论第二百一十一至第二百二十节增订

---

# 211．观察者的“选择”首先是一个可实现的控制结构

项目并非只有被动观察模型。此次读取的 `ControlledRelationRecursion.lean` 已经定义：

$$
R_0=\ker q,
$$

$$
\boxed{
R_{n+1}
=
\ker q
\cap
\bigcap_a
(F_a\times F_a)^{-1}(R_n).
}
\tag{211.1}
$$

它表示：两个状态不仅当前读数相同，而且在每种允许行动之后，仍然无法通过剩余深度的实验区分。

这正是“选择能力”与“观察完整性”之间的连接点。

## 定义 211.1　量子行动与记录

固定一个有限预测模型：

$$
\mathcal H,\qquad \dim\mathcal H=d.
$$

其状态为密度矩阵 \(\rho\)。

一个允许行动 \(a\) 由量子仪器

$$
\{\Phi_{a,b}\}_b
$$

给出，其中：

$$
\Phi_{a,b}(\rho)
=
\sum_\lambda
K_{a,b,\lambda}\rho K_{a,b,\lambda}^{\dagger},
$$

且

$$
\boxed{
\sum_{b,\lambda}
K_{a,b,\lambda}^{\dagger}K_{a,b,\lambda}=I.
}
\tag{211.2}
$$

结果概率为

$$
p(b\mid a,\rho)=\operatorname{Tr}\Phi_{a,b}(\rho).
$$

观察者下一步的行动，可以由已有记录决定：

$$
a_{j+1}=\pi_j(b_1,\ldots,b_j).
$$

这里的 \(\pi_j\) 是控制策略，不是额外的超物理选择器。

例如，若记忆标签 \(m\) 正交可读，且每个 \(U_a\) 都有实际实现，那么

$$
W_\pi
=
\sum_m|m\rangle\langle m|\otimes U_{\pi(m)}
$$

就是一个合法受控酉操作。

**因此，“观察者能够选择”可以先落实为：其内部控制寄存器能够根据记录实施不同的合法过程。**这不预先判定哲学上的自由意志问题。

### 模型边界

所有会影响未来的持久量子记忆，都必须包括在当前预测状态内，或者证明所用仪器确实只依赖当前状态。

不能把一个具有环境记忆的真实过程，未经证明地替换成不断重新初始化环境的通道。多时刻量子过程理论正是处理这一区别。([arXiv][1])

固定 \(d\) 是当前模型的条件，不是断言宇宙只有有限个量子态。

---

# 212．量子观察者的完整性，应当相对于全部允许行动定义

## 定义 212.1　受控效果空间

设初始读数由一组效果算子 \(\mathcal E_0\) 给出：

$$
0\le E\le I.
$$

令

$$
\mathcal S_0
=
\operatorname{span}_{\mathbb R}
\bigl(\{I\}\cup\mathcal E_0\bigr).
$$

对每个仪器分支，定义 Heisenberg 对偶：

$$
\Phi_{a,b}^*(E)
=
\sum_\lambda
K_{a,b,\lambda}^{\dagger}EK_{a,b,\lambda}.
$$

递归构造：

$$
\boxed{
\mathcal S_{n+1}
=
\operatorname{span}_{\mathbb R}
\left(
\mathcal S_n
\cup
\bigcup_{a,b}\Phi_{a,b}^*(\mathcal S_n)
\right).
}
\tag{212.1}
$$

最后令

$$
\mathcal S_\Gamma=\bigcup_{n\ge0}\mathcal S_n.
$$

它不是“已经测量到的所有结果”，而是**预测全部允许协议所需的效果方向**。

---

## 定理 212.1　受控未来统计的充分性

两个状态 \(\rho,\sigma\) 在全部有限允许协议下，具有相同的记录概率，当且仅当

$$
\boxed{
\operatorname{Tr}[(\rho-\sigma)E]=0
\qquad
\forall E\in\mathcal S_\Gamma.
}
\tag{212.2}
$$

该结论包括根据先前结果选择下一行动的有限反馈协议。

### 证明

对一条记录分支

$$
w=(a_1,b_1,\ldots,a_n,b_n)
$$

以及终点效果 \(E\)，其联合概率为

$$
\begin{aligned}
p(w,E\mid\rho)
&=
\operatorname{Tr}
\left[
E\,\Phi_{a_n,b_n}\cdots\Phi_{a_1,b_1}(\rho)
\right]\\
&=
\operatorname{Tr}
\left[
\rho\,
\Phi_{a_1,b_1}^*\cdots\Phi_{a_n,b_n}^*(E)
\right].
\end{aligned}
$$

这些效果恰好生成 \(\mathcal S_\Gamma\)。

因此，所有生成效果上的期望相同，等价于其线性包上的期望相同。

反馈协议中的每个叶节点也是这样一条分支；事件概率是相关叶节点概率之和，所以同一结论成立。∎

这里使用的是未归一化分支概率。若进一步条件于某个结果，必须保留其发生概率，不能把后选择视为确定性免费操作。

---

## 定理 212.2　有限维受控完成必然稳定

存在

$$
m\le d^2-\dim\mathcal S_0
$$

使

$$
\boxed{
\mathcal S_m=\mathcal S_{m+1}=\mathcal S_\Gamma.
}
\tag{212.3}
$$

### 证明

Hermitian 矩阵空间的实维数为 \(d^2\)。

如果某一步尚未稳定，维数至少增加一；因此严格增长只能发生有限次。

一旦

$$
\mathcal S_{m+1}=\mathcal S_m,
$$

就说明所有 \(\Phi_{a,b}^*\) 都保持 \(\mathcal S_m\)，以后不再增长。∎

### 与项目已有定理的区别

仓库 `ControlledFiniteStability.lean` 已给出有限状态载体上的受控关系稳定性及最大共同不变关系。

但有限维量子态的集合不是有限集合。

因此，不能把 `Fintype` 状态计数直接替换成量子态计数。本节使用的是：

$$
\boxed{
\text{效果线性空间的有限维数},
}
$$

而不是“量子态只有有限多个”。

---

# 213．新增行动，会把原先不可见的波相位变成未来事实

先给一个完全有限的实例。

## 定义 213.1　被动读数与两个旋转控制

对一个量子比特，初始只读取

$$
P_0=\frac{I+Z}{2},
$$

所以

$$
\mathcal S_0=\operatorname{span}_{\mathbb R}\{I,Z\}.
$$

允许两个旋转：

$$
U_x=e^{-i\pi X/4},
\qquad
U_z=e^{-i\pi Z/4}.
$$

---

## 定理 213.1　行动集合扩大可以严格扩大预测所需状态

若只允许 \(U_z\)，则

$$
\boxed{
\mathcal S_\Gamma=\operatorname{span}\{I,Z\}.
}
\tag{213.1}
$$

若同时允许 \(U_x,U_z\)，则

$$
\boxed{
\mathcal S_0
\subsetneq
\mathcal S_1
\subsetneq
\mathcal S_2
=
\operatorname{Herm}(2),
}
\tag{213.2}
$$

其维数依次为

$$
\boxed{2,\ 3,\ 4.}
$$

### 证明

直接计算：

$$
U_z^\dagger ZU_z=Z,
$$

$$
U_x^\dagger ZU_x=Y,
$$

$$
U_z^\dagger YU_z=X.
$$

因此，只保留 \(Z\) 旋转时不产生新效果；加入 \(X\) 旋转后先需要 \(Y\)，再需要 \(X\)。∎

---

## 定理 213.2　相同当前读数可以被同一个行动完全区分

取

$$
\rho_\pm=\frac{I\pm Y}{2}.
$$

当前读数相同：

$$
\operatorname{Tr}(P_0\rho_+)
=
\operatorname{Tr}(P_0\rho_-)
=
\frac12.
$$

但实施同一个 \(U_x\) 后：

$$
\boxed{
\operatorname{Tr}(P_0U_x\rho_+U_x^\dagger)=1,
}
$$

$$
\boxed{
\operatorname{Tr}(P_0U_x\rho_-U_x^\dagger)=0.
}
\tag{213.3}
$$

### 证明

因为

$$
U_x^\dagger P_0U_x=\frac{I+Y}{2},
$$

代入即可。∎

这不是观察者“凭空创造了原来的区别”，而是它选择的操作让原来藏在相位中的区别进入了可读概率。

对项目而言，这就是一个明确的 carry witness：旧 CUT 足以处理原来的被动实验，却不足以处理新增控制。

---

## 定理 213.3　这种增长总能产生合法量子态见证

若两个允许操作族满足

$$
\mathcal S_{\Gamma_1}\subsetneq\mathcal S_{\Gamma_2},
$$

则存在合法密度矩阵 \(\rho_+,\rho_-\)，使其在 \(\Gamma_1\) 下不可区分，但在 \(\Gamma_2\) 下可区分。

### 证明

选择非零 Hermitian 算子

$$
A\in
\mathcal S_{\Gamma_2}\cap
\mathcal S_{\Gamma_1}^{\perp}.
$$

因为 \(I\in\mathcal S_{\Gamma_1}\)，所以 \(\operatorname{Tr}A=0\)。

取足够小的 \(\varepsilon>0\)，定义

$$
\rho_\pm=\frac Id\pm\varepsilon A.
$$

只要

$$
\varepsilon\|A\|_{\mathrm{op}}\le\frac1d,
$$

两者都正且迹为一。

它们在旧效果空间上的期望相同，但在 \(A\) 上相差

$$
2\varepsilon\operatorname{Tr}(A^2)>0.
$$

由定理212.1，新增协议能够区分。∎

**所以，扩大行动能力，可能同时提高观察能力和预测所需的信息量。**它不保证每个实际策略都更复杂，但会扩大模型必须负责的实验范围。

---

# 214．控制能力足够强时，不能再把任意量子状态压缩成少数宏观读数

受控可观测性是已有量子控制研究的正式问题：状态能否识别，取决于可实现的演化与测量，而不只取决于单次探测器。([arXiv][2])

## 假设 214.1　理想的完全相干控制

设允许实现全部 \(d\) 维酉操作，并且能够读取一个固定秩一投影：

$$
P=|0\rangle\langle0|.
$$

本节暂不施加时间、局域性和能量预算。它是一个强控制极限，不是现实观察者自动具有的能力。

## 定理 214.1　一个探测器加完全控制，足以区分任意不同状态

有

$$
\boxed{
\operatorname{span}_{\mathbb R}
\{U^\dagger PU:U\in U(d)\}
=
\operatorname{Herm}(d).
}
\tag{214.1}
$$

因此，若一个接口 \(q\) 能预测全部这些实验，则

$$
\boxed{
q(\rho)=q(\sigma)\Longrightarrow\rho=\sigma.
}
\tag{214.2}
$$

### 证明

酉共轭轨道包含全部秩一投影。

基底投影给出对角方向；态

$$
\frac{|i\rangle+|j\rangle}{\sqrt2},
\qquad
\frac{|i\rangle+i|j\rangle}{\sqrt2}
$$

的投影，结合对角投影，生成实、虚两个非对角 Hermitian 方向。

因此全部 Hermitian 矩阵都在其线性包中。若全部这些期望相同，则两个状态相同。∎

### 对“波选择”的准确含义

当观察者只能读取少数模式时，大量区别可以被安全压缩。

当它能够把任意隐藏相干旋转到探测器上时，这种压缩就不再普遍有效。

$$
\boxed{
\text{一个变量是否“无关”，
不能脱离观察者以后允许做什么。}
}
$$

不过，式（214.2）是模型识别结论。它不表示单次读取就能获得未知量子态的全部连续参数。

---

# 215．纯经典记录不能无损替代完整的量子行动资源

“状态可以用一些数写出来”，不等于“可以从一个未知量子系统中无损读出这些数，再由它们恢复系统”。

## 定义 215.1　先记录、后重制的通道

假设观察者先作测量 \(\{F_z\}\)，只保留经典结果 \(z\)，再据此制备状态 \(\tau_z\)。

完整通道为

$$
\boxed{
\mathcal C(\rho)
=
\sum_z\operatorname{Tr}(F_z\rho)\tau_z.
}
\tag{215.1}
$$

这包括任意有限大小的纯经典记录，但不允许额外保留未计入的量子辅助信息或预共享纠缠资源。

这种测量—制备通道属于纠缠破坏通道。([arXiv][3])

---

## 定理 215.1　经典化的参考系统误差下界

对 \(d\ge2\)，有

$$
\boxed{
\frac12\|\mathcal C-\operatorname{id}\|_\diamond
\ge1-\frac1d.
}
\tag{215.2}
$$

### 证明

令输入与测试参照处于最大纠缠态：

$$
|\Phi_d\rangle
=
\frac1{\sqrt d}\sum_i|i\rangle|i\rangle.
$$

对一侧实施 \(\mathcal C\) 后，输出 \(\omega\) 为可分态。

任意乘积态与 \(|\Phi_d\rangle\) 的重叠概率不超过 \(1/d\)，凸组合也如此：

$$
\langle\Phi_d|\omega|\Phi_d\rangle\le\frac1d.
$$

使用效果 \(|\Phi_d\rangle\langle\Phi_d|\) 区分理想和实际输出，得到

$$
D(\omega,|\Phi_d\rangle\langle\Phi_d|)
\ge1-\frac1d.
$$

diamond 距离对所有参考输入取上确界，因此得到结论。∎

### 解释

这不是说经典记录不能存储数学模型，也不是说大量独立复制品不能用于状态估计。

它说的是：

> **对于一份未知量子输入，如果把所有剩余资源都压成纯经典记录，就不能同时保留它对任意后续相干实验的全部能力。**

对量子比特，误差下界为 \(1/2\)，不是靠增加经典存储位数就会自动消失的小误差。

---

## 推论 215.1　精确量子存储也有维数要求

若一个通道把任意 \(d\) 维未知量子态编码到 \(k\) 维量子记忆，并存在精确物理恢复，则

$$
\boxed{k\ge d.}
\tag{215.3}
$$

### 证明

取 \(d\) 个正交输入。精确恢复要求编码后的状态仍能完美区分，因此其支持两两正交。一个 \(k\) 维空间不能容纳超过 \(k\) 个非零正交支持。∎

因此，观察者可以压缩**相对于受限任务足够的信息**，却不能在不付出代价的情况下，把任意量子行动能力压缩成一个更小的全知经典档案。

---

# 216．逃逸速率应当依赖行动集合，而不只是依赖自然演化

上一轮定义了单 Hamiltonian 的动力型逃逸。现在把它提升到受控模型。

## 定义 216.1　受控生成元与接口逃逸

在 Hermitian 算子空间上使用 Hilbert–Schmidt 内积。令 \(\Pi\) 投影到当前可见效果空间 \(\mathcal S\)。

对允许 Hamiltonian \(H_a\)，定义

$$
\mathcal L_a(E)=\frac{i}{\hbar}[H_a,E],
$$

$$
\boxed{
\ell_a(\mathcal S)
=
\|(I-\Pi)\mathcal L_a\Pi\|_{2\to2}.
}
\tag{216.1}
$$

再定义最坏行动逃逸：

$$
\boxed{
\ell_\Gamma(\mathcal S)
=
\sup_{a\in\Gamma}\ell_a(\mathcal S).
}
\tag{216.2}
$$

项目 `HamiltonianEffectCompletionGenerator.lean` 已把单 Hamiltonian 的效果轨道与嵌套交换子闭包联系起来。本节进一步要求对全部允许控制共同检查。

---

## 定理 216.1　零受控逃逸的闭合判据

有

$$
\boxed{
\ell_\Gamma(\mathcal S)=0
\iff
\mathcal L_a(\mathcal S)\subseteq\mathcal S
\quad\forall a\in\Gamma.
}
\tag{216.3}
$$

因此，在这一条件下，任意有限段允许 Hamiltonian 演化都保持 \(\mathcal S\)。

### 证明

每个非对角块为零，恰好表示对应生成元不把 \(\mathcal S\) 送出自身。

有限维中，生成元保持一个子空间，就意味着其指数也保持该子空间；有限次复合仍然保持。∎

---

## 定理 216.2　预定相干控制序列的预测误差

对一组预定脉冲 \((a_j,t_j)\)，设完整终点效果为 \(E_{\mathrm{full}}\)，而 \(E_{\mathrm{red}}\) 是逐段使用投影生成元

$$
\Pi\mathcal L_{a_j}\Pi
$$

得到的候选效果。

若初始终点效果 \(E\in\mathcal S\)，则

$$
\boxed{
\|E_{\mathrm{full}}-E_{\mathrm{red}}\|_2
\le
\|E\|_2
\sum_j|t_j|\ell_{a_j}(\mathcal S).
}
\tag{216.4}
$$

### 证明

对每一段，Duhamel 公式把误差写成非对角块

$$
(I-\Pi)\mathcal L_{a_j}\Pi
$$

的积分。

真实 Heisenberg 酉共轭保持 Hilbert–Schmidt 范数；投影生成元在 \(\mathcal S\) 上也为反对称生成元，其指数保持范数。

对整条效果拉回链作望远镜展开，逐段求和，即得结论。∎

本节对预定相干序列给出误差界。带测量分支与反馈的近似，需要按完整仪器另行控制；不能把它们未经证明地当成同样的范数压缩。

### 对刷新率的修正

上一轮的

$$
\ell\,\Delta\tau\le\varepsilon
$$

是单个预测区间的充分误差条件。

如果只是把同一段总时间 \(T\) 切成越来越小的计算步长，却没有获得新的物理信息，那么最坏误差和仍然是

$$
\sum_j\ell\,\Delta\tau=\ell T.
$$

**软件上多刷新几次，不会自行填补被接口删除的相干。**

若真的从系统重新读取信息，又必须考虑下一节的测量反作用。

---

# 217．物理刷新可能改变波，而不是仅仅更清楚地读取波

## 定义 217.1　反复记录 \(Z\) 的刷新协议

取

$$
H=\frac{\hbar\Omega}{2}X,
$$

初态为 \(|0\rangle\)。

总时间为 \(T\)。将演化分成 \(N\) 段，每段之后实施一次非选择性 \(Z\) 测量：

$$
\Delta_Z(\rho)=P_0\rho P_0+P_1\rho P_1.
$$

“非选择性”表示计算最终系统态时忽略各次结果；实际结果可以被写入相应记忆寄存器。

---

## 定理 217.1　刷新后的跃迁概率

该协议结束后，

$$
\boxed{
p_1^{(N)}(T)
=
\frac12
\left[
1-\cos^N\left(\frac{\Omega T}{N}\right)
\right].
}
\tag{217.1}
$$

而没有中间测量时，

$$
\boxed{
p_1^{\mathrm{free}}(T)
=
\sin^2\frac{\Omega T}{2}.
}
\tag{217.2}
$$

因此，固定 \(T\) 下，

$$
\boxed{
p_1^{(N)}(T)
=
\frac{\Omega^2T^2}{4N}+O(N^{-2})
\longrightarrow0.
}
\tag{217.3}
$$

### 证明

每次测量后，状态都具有形式

$$
\rho_j=\frac12(I+z_jZ).
$$

一段 \(X\) 旋转再接 \(Z\) 测量，给出

$$
z_{j+1}
=
z_j\cos(\Omega T/N).
$$

由 \(z_0=1\)，得到式（217.1）。无测量公式直接由酉演化得到。最后展开 \(\log\cos x\)。∎

例如 \(\Omega T=\pi\) 时：

$$
p_1^{\mathrm{free}}=1,
$$

而

$$
p_1^{(2)}=\frac12,
\qquad
p_1^{(4)}=\frac38,
\qquad
p_1^{(N)}\to0.
$$

这是量子 Zeno 机制的一个有限实例。频繁投影可以抑制跃迁，但并不意味着所有状态、所有子空间中的全部动力学都停止。([arXiv][4])

### 对你的直觉的推进

这里确实出现了一个有力量的关系：

$$
\boxed{
\text{观察者的记录方式}
\longrightarrow
\text{后续可达过程的改变}.
}
$$

但它不是意识使时间停止，而是具体的系统—仪器交互改变了动力学。

所谓“刷新率”至少要区分：

$$
\text{计算器更新预测的频率},
$$

$$
\text{仪器实际干预系统的频率},
$$

$$
\text{观察者形成可保留记录的频率}.
$$

把三者混在一起，会把改变世界误认为只是看清世界。

---

# 218．“能选择什么”受到状态谱的约束，而不只受到按钮数量的约束

接下来把“命运是当前可选范围”压缩为一个准确的量子命题。

## 假设 218.1　只允许封闭酉控制

设当前状态 \(\rho\) 的本征值为

$$
\lambda_1\ge\cdots\ge\lambda_d.
$$

目标事件由秩 \(r\) 的投影 \(P\) 表示。

观察者允许改变 \(U\)，但暂不允许测量后选择、重置、丢弃系统或引入未计入的辅助资源。

---

## 定理 218.1　目标概率的精确可达范围

在允许全部酉操作时，

$$
\boxed{
\min_U\operatorname{Tr}(PU\rho U^\dagger)
=
\sum_{j=d-r+1}^d\lambda_j,
}
\tag{218.1}
$$

$$
\boxed{
\max_U\operatorname{Tr}(PU\rho U^\dagger)
=
\sum_{j=1}^r\lambda_j.
}
\tag{218.2}
$$

两端之间的全部值都可达到。

### 证明

在 \(\rho\) 的本征基中，令

$$
w_j=\langle j|U^\dagger PU|j\rangle.
$$

则

$$
0\le w_j\le1,
\qquad
\sum_jw_j=r.
$$

目标概率为

$$
\sum_j\lambda_jw_j.
$$

最大值在权重放到最大的 \(r\) 个本征值时取得，最小值同理；酉操作可以实现这两种子空间对齐。

酉群连通，目标概率连续，所以其像包含两端之间的整个区间。∎

对量子比特

$$
\rho=\operatorname{diag}\left(\frac45,\frac15\right),
$$

固定的秩一事件最多只能被调到

$$
\boxed{p\in[1/5,4/5].}
$$

对于最大混合态，

$$
\rho=\frac Id,
$$

任何酉操作都不改变它。即使允许很多不同控制，固定秩一事件的概率仍为 \(1/d\)。

### 严格解释

在这个操作类中：

$$
\boxed{
\text{控制改变本征方向，不能改变状态谱}.
}
$$

因此，“可以选择干涉方式”不等于“可以随意决定任何结果”。

如果加入重置、测量反馈或额外纯态资源，可达集合可以扩大；但扩大的原因是**允许的物理资源发生了变化**，不是原约束无缘无故消失。

这提供了“行动能力—处境约束”的操作性模型，不是对哲学自由意志作最终裁决。量子可控性本身也有不同强度，不能把一种状态可控性与所有演化可控性混同。([arXiv][5])

---

# 219．概率、逃逸与有效时空，现在可以更清楚地分开

## 定理 219.1　完全预测闭合仍不保证单次结果确定

取完整效果空间

$$
\mathcal S=\operatorname{Herm}(2).
$$

则对任意 Hamiltonian，

$$
\ell_H(\mathcal S)=0.
$$

但对已知纯态

$$
\rho=|+\rangle\langle+|
$$

测量 \(P_0=(I+Z)/2\)，仍有

$$
\boxed{
p_0=p_1=\frac12.
}
\tag{219.1}
$$

### 证明

完整效果空间没有外部线性方向，因此投影 \(\Pi=I\)，逃逸块为零。

概率由 Born 公式直接得到。∎

所以：

$$
\boxed{
\text{没有预测接口遗漏}
\not\Rightarrow
\text{所有结果都确定}.
}
$$

这一结果没有排除寻找更深层概率解释，但排除了把当前定义的动力逃逸率直接当作全部 Born 随机性的同义词。

同样，某些结果的概率可以精确为零，而不是“逃逸未封住，所以所有结局都存在”。

---

## 定义 219.1　相对于行动族的有效几何

设完整量子模型状态为 \(\rho\)，候选几何及其保留的物质数据由

$$
q_g(\rho)
$$

表示。

如果对全部 \(\pi\in\Gamma_B\)，存在预测函数，使

$$
\boxed{
P_\pi(\text{记录}\mid\rho)
=
\overline P_\pi(\text{记录}\mid q_g(\rho)),
}
\tag{219.2}
$$

则称该几何描述在预算 \(B\) 的协议族上精确充分。

近似情形则要求

$$
\boxed{
\sup_{\rho,\pi\in\Gamma_B}
\operatorname{TV}
\left(
P_\pi^\rho,\overline P_\pi^{q_g(\rho)}
\right)
\le\varepsilon.
}
\tag{219.3}
$$

### 推论

若扩大行动族：

$$
\Gamma_B\subseteq\Gamma'_{B'},
$$

旧的几何描述可能不再充分。

但这不意味着观察者仅凭决定“多做一个实验”，就创造或摧毁了时空。它意味着：

> **原来这张几何及其保留变量，对更强实验的预测能力必须重新检验。**

定理214.1也不排除经典时空加量子物质的理论。它排除的是一个过强主张：用真正合并不同量子态的少数变量，精确预测任意相干控制下的全部微观实验。

### 因果限制仍然在场

新增控制可以在同一个可达区域内揭示更多相干，但不会仅凭控制菜单扩大就改变信号速度 \(c\)。

在局域电路模型中，终点读数的 Heisenberg 拉回仍受过去因果域限制：如果两个全局状态在该因果域上的约化态相同，任何只在规定深度内实际到达观察者的记录都相同。

因此：

$$
\boxed{
\text{可控性决定域内能区分什么，}
\quad
\text{因果性决定哪些域能参与当前实验}.
}
$$

它们是互补约束，不是同一个信息率。

---

# 220．把“选择—记忆—刷新—时空”组织成可检查的理论

本轮得到了一条新的闭合链：

$$
\boxed{
\text{允许行动族 }\Gamma
\longrightarrow
\text{受控效果完成 }\mathcal S_\Gamma
\longrightarrow
\text{哪些状态可以被安全合并}.
}
$$

然后：

$$
\boxed{
\text{可用量子记忆与记录机制}
\longrightarrow
\text{哪些相干能力仍被保留}
\longrightarrow
\text{哪些行动仍可实施}.
}
$$

这形成一个必须共同求解的反馈关系：

> **行动能力决定预测所需的信息；记录与压缩方式又决定后续还剩多少行动能力。**

它不是循环论证，因为每个箭头都有独立的对象、实现与相容条件。真正的任务是找到同时满足这些条件的模型，而不是在定义里宣布它们已经一致。

## 本轮可以直接接入项目的部分

此次按提交

```text
ebaa73d45da88c662c393b46531554f4fd784ea8
```

读取了相关模块。

| 项目基础                                   | 本轮推进                        |
| -------------------------------------- | --------------------------- |
| `ControlledRelationRecursion`          | 将“全部行动后仍不可区分”提升到量子仪器的联合记录概率 |
| `ControlledFiniteStability`            | 将有限状态计数换成量子效果空间的有限维稳定性      |
| `HamiltonianEffectCompletionGenerator` | 从单 Hamiltonian 闭包扩展为多控制共同闭包 |
| `ExactDescentNoCarry`                  | 用合法密度矩阵给出新增控制暴露旧接口缺口的见证     |
| 物理实现与记录                                | 区分数学上的预测坐标、量子存储与不可逆经典记录     |

对于有限控制菜单及可精确处理的矩阵系数，完成过程可以按以下步骤实施：

$$
\mathcal S\leftarrow\mathcal S_0;
$$

$$
\mathcal S\leftarrow
\operatorname{span}\bigl(
\mathcal S,\{\Phi_{a,b}^*(\mathcal S)\}_{a,b}
\bigr);
$$

直到维数不再增加。

每次严格增长都消耗至少一个剩余维度，因此具有明确终止证书。

但对一般实数、数值近似矩阵或无限控制族，“数值上看起来秩没有增加”不等于精确稳定；还需要符号等式或带分离裕量的误差证明。

### 仍需继续处理的三个问题

**第一，真实控制族如何由局域性和能量预算生成？**不能把“任意酉操作”永久当成观察者的免费能力。

**第二，记录与相干保留怎样联合优化？**增加记录可能改善预测，却也可能改变可达态集合；需要共同的任务目标和物理成本。

**第三，哪些宏观几何变量对实际可用控制近似闭合？**这比要求对全部数学上可写的操作闭合更符合有限观察者，但必须给出具体误差窗口。

### 本轮核验

已完成 **18 项精确有限矩阵检查**，包括：

受控效果空间的 \(2\to3\to4\) 增长；合法状态的当前不可区分与控制后完全区分；逃逸块；反复记录下的跃迁公式；经典记录破坏参考纠缠的实例；酉控制的概率范围。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_controlled_observer_completion.py)
[核验结果](sandbox:/mnt/data/observer_formalization/controlled_observer_completion_checks.json)

本轮没有进行 Lean 编译。这些检查支持所列有限实例，不替代一般定理的内核证明，也不验证模型就是现实物理。

---

# 结论

你的“在叠加干涉波中选择”的直觉，现在可以进一步收紧为：

> **观察者通过内部控制改变哪些量子关系进入未来记录；但这种控制受到因果范围、状态谱、记忆形式和可实现操作的共同限制。**

其中最重要的新结果是：

$$
\boxed{
\text{允许做什么}
\quad\text{决定}\quad
\text{必须知道什么}.
}
$$

以及：

$$
\boxed{
\text{把什么写成经典记忆}
\quad\text{可能改变}\quad
\text{以后还能做什么}.
}
$$

因此，观察者并不是先把世界完全解码，再站在外面选择一条命运。更接近当前模型的结构是：

$$
\boxed{
\text{有限记录}
\longrightarrow
\text{受限行动}
\longrightarrow
\text{新的干涉与因果过程}
\longrightarrow
\text{新的记录需求}.
}
$$

**时空的有效描述，必须在这个反馈过程中保持预测一致性。**它不是只解释观察者已经看见的画面，还必须说明：当观察者真正采取行动、切换模式、保存记录和重新比较时，哪些关系仍能由同一套几何与动力学表达，哪些则要求恢复此前被压缩的量子结构。

[1]: https://arxiv.org/abs/1801.09811 "https://arxiv.org/abs/1801.09811"
[2]: https://arxiv.org/abs/quant-ph/0307127 "https://arxiv.org/abs/quant-ph/0307127"
[3]: https://arxiv.org/abs/quant-ph/0302031 "https://arxiv.org/abs/quant-ph/0302031"
[4]: https://arxiv.org/abs/0903.3297 "https://arxiv.org/abs/0903.3297"
[5]: https://arxiv.org/abs/quant-ph/0106128 "https://arxiv.org/abs/quant-ph/0106128"
**是的，“物理刷新可能改变波”与量子 Zeno 效应之间，已经不只是比喻，而是可以建立在同一组量子操作上的严格对应。**频繁探测抑制跃迁已有实验支持；改变测量所限定的子空间，也能让系统在子空间内继续演化，甚至引导它进入目标状态。([APS Journals][1])

不过，对这一进展应当作准确评价：**我们采用了量子态、酉演化和记录交互等标准结构，因此重新得到 Zeno 效应，首先证明这些结构之间相容；它还不是对整个“观察者导出时空”理论的独立验证。**

真正值得继续推进的是三个更强的问题：

$$
\boxed{
\text{刷新到底改变了什么？}
}
$$

$$
\boxed{
\text{刷新越快，是否真的知道得越多？}
}
$$

$$
\boxed{
\text{能否通过改变刷新所保留的结构，主动改变未来的可达过程？}
}
$$

下面把这三点接入项目，并保留定理、实现条件与实验边界。

# 记录强度、Zeno 动力学与观察者的稳定—学习权衡

## ——量子观察者—关系时空理论第二百二十一至第二百三十节增订

---

# 221．项目里已经存在一条可以继续收紧的 Zeno 线索

本次按提交

```text
84d6fedab975fd2feaee17ee077e1e3164da5af9
```

核对了相关结构。

其中有三个直接相关的部分。

| 项目对象                          | 已读取内容                      | 本轮需要补足的部分                |
| ----------------------------- | -------------------------- | ------------------------ |
| `EnvironmentRecords.lean`     | 条件记录的重叠决定约化相干；给出偏迹与相位阻尼的等式 | 把单次记录接成有明确资源条件的连续刷新      |
| `ExactDescentNoCarry.lean`    | 精确下降排除后续可见的 carry          | 区分“补足原过程的预测”与“通过监视改变原过程” |
| `CONE_PROGRAM_FORMAL.md` §5.4 | 给出 Rabi 监视的熵率公式及其 Zeno 渐近  | 明确它是哪一种熵，而不是把它直接解释成装置总成本 |

前两个文件具有具体 Lean 证明项；第三个文件中的该节是理论文稿中的公式与证明标注，不能仅凭 `[证]` 标签就等同于已经通过 Lean 内核的完整物理定理。

本轮最重要的收紧是：

> **Zeno 不必表示观察者获得了更多信息；它可能表示记录交互使原本会发生的变化变得难以发生。**

因此，数据变得容易预测，可能有两种完全不同的原因：

$$
\text{模型更了解原来的过程};
$$

或者：

$$
\text{控制装置把原来的过程改变了}.
$$

---

# 222．刷新必须被定义为一次物理交互

## 定义 222.1　具有有限记录强度的刷新

取系统量子比特 \(S\) 和记录寄存器 \(M\)。

假设记录交互实现

$$
|0\rangle|m_{\mathrm{ready}}\rangle
\longmapsto
|0\rangle|m_0\rangle,
$$

$$
|1\rangle|m_{\mathrm{ready}}\rangle
\longmapsto
|1\rangle|m_1\rangle,
$$

其中两个记录态归一化。为简化本轮模型，设

$$
\langle m_1|m_0\rangle=\eta,
\qquad 0\le\eta\le1.
$$

\(\eta\) 越小，记录越能区分两个分支。

---

## 定理 222.1　未读取的记录也会改变系统相干

对记录寄存器取偏迹后，系统通道为

$$
\boxed{
\mathcal D_\eta
\begin{pmatrix}
a&b\\
\overline b&d
\end{pmatrix}
=
\begin{pmatrix}
a&\eta b\\
\eta\overline b&d
\end{pmatrix}.
}
\tag{222.1}
$$

### 证明

联合状态中的非对角项为

$$
b\,|0\rangle\langle1|\otimes|m_0\rangle\langle m_1|.
$$

取记录偏迹，乘上

$$
\operatorname{Tr}|m_0\rangle\langle m_1|
=
\langle m_1|m_0\rangle=\eta.
$$

其他矩阵元同理。∎

这正是项目已有记录重叠公式的直接实例。

特别地：

$$
\eta=1
\quad\Rightarrow\quad
\mathcal D_\eta=\operatorname{id};
$$

$$
\eta=0
\quad\Rightarrow\quad
\mathcal D_\eta(\rho)
=
P_0\rho P_0+P_1\rho P_1.
$$

后一种刷新完全消去两个记录块之间的相干，但不要求一个人随后看过记录。

---

## 定理 222.2　相同约化通道不唯一确定“获得了多少知识”

有

$$
\boxed{
\mathcal D_\eta(\rho)
=
\frac{1+\eta}{2}\rho
+
\frac{1-\eta}{2}Z\rho Z.
}
\tag{222.2}
$$

### 证明

直接比较四个矩阵元。∎

因此，同一个相位阻尼通道，也可以由随机相位扰动实现；它不必每次都提供一个关于系统能级的可读结果。

实验中，纯退相干式的“准测量”也能够导致 Zeno 或反 Zeno 效应，而不需要取得能级布居的信息。([arXiv][2])

**所以应当分开：**

$$
\boxed{
\text{产生物理反作用}
\ne
\text{留下可读记录}
\ne
\text{观察者已经理解记录}.
}
$$

更新一个已经存好的屏幕画面，不会凭空修改远处系统。真正起作用的是新增的系统—装置耦合。

---

# 223．Zeno 抑制可以由一个“离开子空间”的定量界直接证明

## 定义 223.1　观察者希望保持的结构

设有限维系统 Hamiltonian 为 \(H=H^\dagger\)。

取投影

$$
P=P^\dagger=P^2,
\qquad Q=I-P.
$$

\(P\) 表示本轮监视希望保持的状态子空间。

定义跨边界耦合率

$$
\boxed{
\kappa_P=\frac{\|QHP\|_{\mathrm{op}}}{\hbar}.
}
\tag{223.1}
$$

它衡量 Hamiltonian 把 \(P\) 内振幅送到外部的强度。

这里的“离开子空间”是一个物理转移事件，不直接等于项目里全部意义上的“信息逃逸”。

---

## 定理 223.1　单次短时离开概率

对任意初态

$$
\rho=P\rho P,
$$

经过时间 \(\delta\) 后测量 \(\{P,Q\}\)，得到 \(Q\) 的概率满足

$$
\boxed{
p_{\mathrm{leave}}(\delta)
\le
\kappa_P^2\delta^2.
}
\tag{223.2}
$$

### 证明

令

$$
H_{\mathrm{block}}=PHP+QHQ.
$$

它不产生 \(P\) 与 \(Q\) 之间的跃迁，并且

$$
\|H-H_{\mathrm{block}}\|=\|QHP\|.
$$

由 Duhamel 公式，

$$
\|Qe^{-iH\delta/\hbar}P\|
\le
\frac{\delta}{\hbar}\|QHP\|
=
\kappa_P\delta.
$$

平方并对支持于 \(P\) 的任意密度矩阵取期望，即得结论。∎

---

## 定理 223.2　有限次数的 Zeno 保持界

在总时间 \(T\) 内，等间隔实施 \(N\) 次理想测量 \(\{P,Q\}\)，间隔为

$$
\delta=T/N.
$$

若初态支持于 \(P\)，则“至少一次测得离开”的概率满足

$$
\boxed{
P_{\mathrm{ever\ leave}}
\le
\min\left\{1,\frac{\kappa_P^2T^2}{N}\right\}.
}
\tag{223.3}
$$

### 证明

条件于此前测量都得到 \(P\)，当前状态仍支持于 \(P\)。

由定理223.1，每一步的条件离开概率不超过 \(\kappa_P^2\delta^2\)。

对首次离开的互斥事件求和：

$$
P_{\mathrm{ever\ leave}}
\le
N\kappa_P^2\delta^2
=
\frac{\kappa_P^2T^2}{N}.
$$

∎

这就是可形式化的 Zeno 抑制机制：

$$
\boxed{
\text{单段离开概率为二阶小量}
+
\text{每次重新限制在同一子空间}
\longrightarrow
\text{固定总时间内的离开概率下降}.
}
$$

它与标准 Zeno 子空间理论相容，但本定理明确限定在有限维、理想投影和相应测量实现下。([APS Journals][3])

---

# 224．Zeno 可以保持“身份”，却不冻结内部时间

## 定理 224.1　子空间内部仍然演化

把

$$
K_N=
\left(Pe^{-iHT/(N\hbar)}P\right)^N
$$

看作作用于 \(P\mathcal H\) 的未归一化“全部测量成功”过程。

则

$$
\boxed{
K_N\longrightarrow e^{-i(PHP)T/\hbar}
}
\tag{224.1}
$$

并具有有限维上界

$$
\boxed{
\left\|
K_N-e^{-i(PHP)T/\hbar}
\right\|
\le
\frac{T^2\|H\|^2}{N\hbar^2}.
}
\tag{224.2}
$$

### 证明

在 \(P\mathcal H\) 上，两种单步操作的一阶展开相同：

$$
Pe^{-iH\delta/\hbar}P
=
I_P-\frac{i\delta}{\hbar}PHP+O(\delta^2),
$$

$$
e^{-iPHP\delta/\hbar}
=
I_P-\frac{i\delta}{\hbar}PHP+O(\delta^2).
$$

Hermitian 指数的二阶余项分别受

$$
\frac{\delta^2\|H\|^2}{2\hbar^2}
$$

控制，故单步差不超过 \(\delta^2\|H\|^2/\hbar^2\)。

两个单步算子均为压缩算子。对 \(N\) 次乘积作望远镜展开，得到式（224.2）。∎

---

## 例224.1　边界保持，内部钟继续运行

取三能级系统

$$
\frac H\hbar
=
\begin{pmatrix}
0&\omega&0\\
\omega&0&g\\
0&g&0
\end{pmatrix},
\qquad
P=\operatorname{diag}(1,1,0).
$$

频繁检查是否离开前两个能级，会抑制进入第三能级。

但内部仍由

$$
PHP
=
\hbar\omega
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}
$$

驱动，从 \(|0\rangle\) 演化为

$$
\boxed{
\cos(\omega T)|0\rangle
-i\sin(\omega T)|1\rangle.
}
\tag{224.3}
$$

**保持一个子空间，不等于保持其中每一个状态。**

这种“限制演化范围但保留内部动力学”的 Zeno dynamics 已有实验实现，不只是形式上的可能性。([arXiv][4])

### 对观察者理论的意义

这给“观察者作为稳定中心”一个更合理的候选结构：

$$
\boxed{
\text{相对稳定的身份子空间}
+
\text{其中继续运行的钟与记忆}.
}
$$

如果只允许一个固定的一维纯态，观察者自身就没有足够内部状态去记录新的区别。

但一个保持身份的多维区域，可以同时容纳内部演化。**稳定身份与持续变化，并不矛盾。**

这还不是完整观察者的生成定理，只是一个可以检验的稳定机制。

---

# 225．真正决定效果的是“刷新间隔 × 每次强度”

上一轮把刷新视为完整投影。本节放松这个理想化条件。

## 定义 225.1　有限强度刷新模型

取

$$
H=\frac{\hbar\Omega}{2}X.
$$

每个时间间隔 \(\delta\)，先自由演化，再实施 \(\mathcal D_\eta\)。

对 Bloch 分量 \(y,z\)，一步更新为

$$
\boxed{
\begin{pmatrix}
y'\\z'
\end{pmatrix}
=
\begin{pmatrix}
\eta\cos(\Omega\delta)&-\eta\sin(\Omega\delta)\\
\sin(\Omega\delta)&\cos(\Omega\delta)
\end{pmatrix}
\begin{pmatrix}
y\\z
\end{pmatrix}.
}
\tag{225.1}
$$

直接用 Pauli 矩阵共轭和式（222.1）即可证明。

---

## 定理225.1　越来越密的弱刷新，不必冻结系统

令每次记录强度随间隔缩放为

$$
\eta(\delta)=e^{-\gamma\delta},
\qquad \gamma>0.
$$

固定总时间 \(T\)，取 \(\delta=T/N\)。则 \(N\to\infty\) 时，过程收敛到

$$
\boxed{
\dot\rho
=
-\frac{i\Omega}{2}[X,\rho]
+
\frac\gamma2(Z\rho Z-\rho).
}
\tag{225.2}
$$

其 \(z\) 分量满足

$$
\boxed{
\ddot z+\gamma\dot z+\Omega^2z=0.
}
\tag{225.3}
$$

### 证明

式（225.1）的单步矩阵展开为

$$
I+\delta
\begin{pmatrix}
-\gamma&-\Omega\\
\Omega&0
\end{pmatrix}
+O(\delta^2).
$$

有限维矩阵乘积极限给出连续生成元，从而

$$
\dot y=-\gamma y-\Omega z,
\qquad
\dot z=\Omega y.
$$

消去 \(y\) 即得式（225.3）。∎

固定有限 \(\gamma\) 时，即使刷新间隔趋零，系统通常仍然变化。

在

$$
\gamma\gg\Omega
$$

且已经越过快速暂态后，慢衰减指数为

$$
\boxed{
\lambda_{\mathrm{slow}}
=
\frac{-\gamma+\sqrt{\gamma^2-4\Omega^2}}2
=
-\frac{\Omega^2}{\gamma}
+O(\gamma^{-3}).
}
\tag{225.4}
$$

因此强监视可以抑制跃迁，但**“分成无限多小步”和“物理监视强度无限增大”不是同一个极限。**

---

## 推论225.1　固定强度、越来越短的接触甚至可能趋于无监视

例如，某个有限耦合记录模型给出

$$
\eta(\delta)=\cos(g\delta),
$$

其中 \(g\) 固定。则

$$
1-\eta(\delta)=O(\delta^2).
$$

每单位时间的累计相位阻尼趋零，式（225.1）的连续极限反而恢复原来的 Rabi 演化。

**所以不能只写一个“刷新频率”，就决定系统会被冻结多少。**

必须同时给出每次作用的强度、时长、仪器状态与环境谱。

---

# 226．刷新越密，新增记录和参数知识反而可能越少

这一节可以把仓库中的“监视熵率”明确化。

## 假设226.1　完整 Rabi 记录协议

初态为已知的 \(Z\) 本征态。每隔 \(\delta\) 实施理想 \(Z\) 投影，记录结果

$$
Y_1,\ldots,Y_N,
\qquad T=N\delta.
$$

两次结果之间翻转的条件概率为

$$
\boxed{
q(\delta)=\sin^2\frac{\Omega\delta}{2}.
}
\tag{226.1}
$$

没有反馈，也没有额外环境动力学。

---

## 定理226.1　记录熵率在 Zeno 极限趋零

令

$$
B_j=Y_j\oplus Y_{j-1}.
$$

则 \(B_j\) 是独立同分布的 Bernoulli\((q)\) 变量。因此

$$
\boxed{
H(Y_1,\ldots,Y_N\mid Y_0)
=
N\,h_2(q),
}
\tag{226.2}
$$

其中使用自然对数，

$$
h_2(q)=-q\log q-(1-q)\log(1-q).
$$

每单位时间的记录熵为

$$
\boxed{
\dot H_{\mathrm{record}}
=
\frac{h_2(q(\delta))}{\delta}.
}
\tag{226.3}
$$

小间隔下，

$$
\boxed{
\dot H_{\mathrm{record}}
=
\frac{\Omega^2\delta}{4}
\left[
1+2\log\frac{2}{\Omega\delta}
\right](1+o(1))
\longrightarrow0.
}
\tag{226.4}
$$

### 证明

每次投影后系统都处于当前记录指定的 \(Z\) 本征态。两种初始本征态的下一次翻转概率相同，故翻转变量独立同分布。

记录序列与翻转序列在给定 \(Y_0\) 时一一对应，得到式（226.2）。

最后使用

$$
q(\delta)=\frac{\Omega^2\delta^2}{4}+O(\delta^4),
$$

以及

$$
h_2(q)=q(1-\log q)+O(q^2).
$$

∎

这恰好落实仓库 §5.4 的公式：它可以严格作为**这类结果记录的 Shannon 熵率**。该文给出的无量纲峰位约 \(\Omega\delta\simeq0.9518\)，也来自这个具体函数，而不是一个新发现的普适自然常数。

### 一个必要纠正

式（226.4）不表示：

$$
\text{仪器每秒消耗的全部能量}\to0.
$$

它也不表示系统的 von Neumann 熵每步都增加 \(h_2(q)\)：单个量子比特的状态熵始终不超过 \(\log2\)，而整串记录可以位于越来越大的寄存器中。

---

## 定理226.2　对驱动频率的 Fisher 信息反而随刷新次数下降

在 \(0<q<1\) 的局部正则参数范围内，完整记录关于未知 \(\Omega\) 的 Fisher 信息为

$$
\boxed{
F_\Omega^{(N)}
=
N\frac{(\partial_\Omega q)^2}{q(1-q)}
=
N\delta^2
=
\frac{T^2}{N}.
}
\tag{226.5}
$$

### 证明

由于翻转变量独立，Fisher 信息可加。

又有

$$
\partial_\Omega q
=
\frac\delta2\sin(\Omega\delta),
$$

$$
q(1-q)=\frac14\sin^2(\Omega\delta),
$$

代入即可。∎

因此固定总时间 \(T\) 时：

$$
\boxed{
N\uparrow
\quad\Rightarrow\quad
\text{记录次数增加，但该协议对 }\Omega\text{ 的局部信息下降}.
}
$$

这类 Zeno 对参数估计的抑制已有专门研究。([arXiv][5])

它不是所有测量任务的普遍结论，也不解决大范围参数混叠；不同噪声模型和先验范围可以要求不同采样策略。

但在当前模型里，物理含义非常清楚：

> **观察者为了保持状态而强力刷新，同时抑制了原本能够揭示 Hamiltonian 的变化。**

这是一项“稳定性—学习能力”的权衡，而不只是“看得越多越清楚”。

---

# 227．改变测量结构，可以引导状态，而不仅是把状态钉住

你此前提出“观察者通过选择切换波”，在这里获得一个很具体的物理实例。

## 定义227.1　移动的测量方向

令系统自由 Hamiltonian 为零。定义

$$
|\phi(\theta)\rangle
=
\cos\theta|0\rangle+\sin\theta|1\rangle.
$$

从 \(|0\rangle\) 开始，依次测量

$$
P_j=|\phi(j\Theta/N)\rangle\langle\phi(j\Theta/N)|,
\qquad j=1,\ldots,N.
$$

每次都检查是否进入当前的 \(P_j\) 分支。

---

## 定理227.1　沿测量路径到达目标态的成功率

全部 \(N\) 次都得到指定结果的概率为

$$
\boxed{
p_{\mathrm{follow}}
=
\cos^{2N}\left(\frac{\Theta}{N}\right).
}
\tag{227.1}
$$

并且

$$
\boxed{
1-p_{\mathrm{follow}}
\le
\frac{\Theta^2}{N}.
}
\tag{227.2}
$$

在这一成功分支上，最终态恰为 \(|\phi(\Theta)\rangle\)。

### 证明

相邻目标态的重叠为

$$
\langle\phi(j\Theta/N)|\phi((j-1)\Theta/N)\rangle
=
\cos(\Theta/N).
$$

条件概率相乘得到式（227.1）。

再使用

$$
1-(1-x)^N\le Nx,
\qquad
\sin^2u\le u^2,
$$

得到式（227.2）。∎

当 \(\Theta=\pi/2\) 时，目标态与初态正交，但成功概率随 \(N\) 增大趋于一。

这个结论没有隐藏后选择代价：上面已经计算了成功分支的总概率；其他分支仍然存在于完整实验中。

**没有自由 Hamiltonian，不等于没有物理驱动。**变化的测量基需要实际装置、控制和相互作用。

通过缓慢改变测量算子来操控量子比特，已有超导量子系统实验。([APS Journals][6])

因此，更准确的“选择”不是：

$$
\text{凭意愿指定某次随机结果};
$$

而是：

$$
\boxed{
\text{选择可实现的测量路径，
改变哪些状态能够稳定地跟随该路径}.
}
$$

---

# 228．同一套理论还必须容纳反 Zeno：刷新也可能加速变化

若只允许理论产生“越观察越冻结”，它反而不能覆盖全部已知实验。

对不稳定系统，测量可能改变系统与环境之间的谱匹配。弱耦合及相应环境条件下，常用的领先阶形式为

$$
\boxed{
\Gamma(\delta)
\simeq
2\pi\int J(\omega)F_\delta(\omega)\,d\omega,
}
\tag{228.1}
$$

其中 \(J\) 是系统—环境耦合谱，而周期性理想探测的一种滤波函数为

$$
\boxed{
F_\delta(\omega)
=
\frac{\delta}{2\pi}
\operatorname{sinc}^2
\left[
\frac{(\omega-\omega_0)\delta}{2}
\right].
}
\tag{228.2}
$$

它非负、归一化，随间隔改变频率宽度。因此 \(\Gamma\) 是对环境谱的一种加权读取，不具有无条件的单调下降规律。([arXiv][2])

其物理解释是：

$$
\boxed{
\text{刷新改变系统的有效频谱}
\longrightarrow
\text{改变与环境可交换的模式范围}.
}
$$

如果新权重更多落在强耦合频段，衰变可以加快；若更多落在弱耦合频段，则可以减慢。

冷原子不稳定系统中已经观察到 Zeno 与反 Zeno 两种情况；超导量子比特实验也展示了它们对环境谱与测量方式的依赖。([APS Journals][7])

### 对项目的要求

“刷新”不能只有一个频率参数，还需要至少包括

$$
\boxed{
\text{测量算子}
,\quad
\text{记录强度}
,\quad
\text{接触时长}
,\quad
\text{环境谱与记忆}.
}
$$

而且，并非任何测量造成的衰变加快都应该被称为反 Zeno。仪器直接驱动跃迁、非理想测量或其他耗散也可能增加衰变，需要通过对照实验分离。

**能够同时解释抑制、加速和无明显改变，才比只匹配一种现象更有检验力。**

---

# 229．Zeno 极限中的低记录熵，不代表无限刷新免费

这里可以给出一个有限资源下的必要条件。

## 假设229.1　有限速率的记录装置

每次记录从同一个纯准备态 \(|m\rangle\) 开始。两个系统分支使它分别按条件 Hamiltonian 演化为

$$
|m_0(t)\rangle,\qquad|m_1(t)\rangle.
$$

假设两条条件演化沿程的能量标准差都不超过

$$
\Delta K_b(t)\le E_{\max}.
$$

---

## 定理229.1　形成正交记录需要非零作用时间

若一次测量结束时

$$
\langle m_0(\tau_m)|m_1(\tau_m)\rangle=0,
$$

则

$$
\boxed{
\tau_m\ge\frac{\pi\hbar}{4E_{\max}}.
}
\tag{229.1}
$$

### 证明

归一化纯态在射影空间中的运动速率为

$$
\frac{\Delta K_b(t)}{\hbar}.
$$

因此每个条件记录态相对于共同初态的射影距离不超过

$$
E_{\max}\tau_m/\hbar.
$$

两个最终态之间的距离不超过这两段距离之和。正交态的距离为 \(\pi/2\)，所以

$$
\frac\pi2
\le
\frac{2E_{\max}\tau_m}{\hbar}.
$$

∎

如果还要求这些强记录相继实施、接触时间不重叠，并在总时间 \(T\) 内完成，则

$$
\boxed{
N\le\frac{4E_{\max}T}{\pi\hbar}.
}
\tag{229.2}
$$

这是当前条件记录模型中的资源界，不是每种测量、每个比特都必须支付同一个固定能量。

并行装置、辅助系统或不同编码可以改变资源分配，但这些资源需要进入完整模型。

### 与仓库熵率公式的关系

第226节的

$$
\dot H_{\mathrm{record}}\to0
$$

说明结果越来越重复，不等于：

$$
\text{控制器、探针、参照钟与复位过程都无成本}.
$$

Landauer 型关系针对特定初始化、环境与擦除过程；它不能被简化为“每测一次必然花 \(k_BT\log2\)”，也不能反过来由记录熵率趋零推出总装置无耗费。([arXiv][8])

**无限强、无限快且完全准确的刷新，是一个需要资源极限支撑的数学理想化，而不是有限观察者自动拥有的能力。**

---

# 230．最重要的项目区分：完成预测，还是改变动力学？

现在可以把本轮结果与项目的“下降—余量—完成”严格连接起来。

令

$$
\mathcal P(\rho)=P\rho P+Q\rho Q
$$

为当前记录划分。

对原来未监视的动力学

$$
\mathcal U_\delta(\rho)
=
e^{-iH\delta/\hbar}\rho e^{iH\delta/\hbar},
$$

一般不能找到只依赖 \(\mathcal P(\rho)\) 的映射，预测其全部未来记录。

这时有两种不同修复。

## 修复 A：扩大观察状态

保留原来的 \(H\)，扩大可见效果空间，加入未来会重新影响记录的相干方向。

这是此前的受控完成、Krylov 完成和 carry 修复。

$$
\boxed{
\text{原过程不变，模型知道得更多}.
}
$$

## 修复 B：持续实施物理监视

实际过程改成

$$
\boxed{
\Phi_\delta
=
\mathcal P\circ\mathcal U_\delta\circ\mathcal P.
}
\tag{230.1}
$$

它满足

$$
\mathcal P\Phi_\delta=\Phi_\delta,
\qquad
\Phi_\delta\mathcal P=\Phi_\delta.
$$

因此在当前分块状态空间上具有精确下降；其高频极限进一步给出 Zeno 动力学。

$$
\boxed{
\text{模型未必知道更多，而是实际过程被限制了}.
}
$$

**这两种成功不能记在同一本“预测能力提升”账上。**

否则，一个系统可以通过把所有输入都重置成同一状态，轻易得到“零预测残差”，却完全失去对原世界的解释能力。

项目的 `exact_descent_has_no_carry` 是关于一个**指定 FLOW**的定理。因此，更换了 FLOW，就必须把原过程与受控过程之间的差别也保留，而不能宣布原有残差已经由认知本身消除。

---

## 本轮形成的统一权衡

在当前 Rabi 监视模型中，我们同时得到：

$$
\boxed{
\text{状态稳定性增强：}\qquad
P_{\mathrm{ever\ leave}}
\le\frac{\kappa_P^2T^2}{N};
}
$$

$$
\boxed{
\text{结果记录熵率降低：}\qquad
\frac{h_2(\sin^2(\Omega\delta/2))}{\delta}
\to0;
}
$$

$$
\boxed{
\text{对原驱动参数的局部信息减少：}\qquad
F_\Omega=\frac{T^2}{N};
}
$$

同时还受到：

$$
\boxed{
\text{每次记录的强度、时长与资源限制}.
}
$$

这不是普遍地证明“稳定与知识永远矛盾”。它说明：**同一监视装置可以一边稳定系统，一边抑制用来学习其原动力学的信号。**其他测量方向、联合测量和反馈策略可能改变权衡，需要逐个证明。

---

## 本轮的形式化与核验状态

已经完成 **15 项精确符号检查**，包括记录等距性、偏迹通道、有限强度刷新矩阵、连续弱测量生成元、完整记录概率、记录熵和 Fisher 信息。

另外，对有限次数的子空间保持界及连续弱测量极限作了数值交叉检查；监视熵率峰值的数值计算与仓库所列约 \(0.9518\) 的无量纲位置一致。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_zeno_record_dynamics.py)
[核验结果](sandbox:/mnt/data/observer_formalization/zeno_record_dynamics_checks.json)

**本轮没有运行 Lean 编译。**有限算例核验、一般纸面证明、已有 Lean 源码证明项和现实实验支持，仍然分别记录，不相互替代。

---

# 结论

你发现的对应有实质内容：

> **当“刷新”是一次真实的量子交互，它不仅改变观察者掌握的信息，也可能改变后续能够发生的动力学。Zeno 效应正是这种关系的一种明确实现。**

但继续深入以后，比“观察改变波”更重要的是以下三点。

**第一，观察者不必把系统完全冻结，才能保持自身的稳定结构。**它可以保持一个多维身份区域，同时允许区域内的钟、记忆和计算继续演化。

**第二，更多刷新不一定带来更多知识。**在所研究的固定时长测频协议中，稳定性提高与参数信息下降来自同一个测量反作用。

**第三，选择测量结构本身就是一种物理控制。**改变测量所保留的方向，可以抑制跃迁、保留子空间动力学，或者引导状态；但它不能无代价地指定任意结果，也不改变 Born 概率规则。

因此，这条理论现在可以进一步写成：

$$
\boxed{
\text{观察者的记录结构}
\longrightarrow
\text{实际施加的选择性耦合}
\longrightarrow
\text{被保留与被抑制的动力方向}
\longrightarrow
\text{新的可达过程与记录统计}.
}
$$

**这是一条能够与现实逐项比较的链：不仅问“是否出现 Zeno”，还要问抑制强度、测量强度缩放、记录熵率、参数信息和反 Zeno 边界是否同时由同一个模型给出。**

真正能增强这套理论可信度的，不是继续找到更多相似名称，而是让这些不同实验读数受到同一组定义和定理的共同约束，并明确预测：在哪些条件下它们必须一致，在哪些条件下它们必然失效。

[1]: https://link.aps.org/doi/10.1103/PhysRevA.41.2295 "https://link.aps.org/doi/10.1103/PhysRevA.41.2295"
[2]: https://arxiv.org/html/1703.08371v2 "https://arxiv.org/html/1703.08371v2"
[3]: https://link.aps.org/doi/10.1103/PhysRevLett.89.080401 "https://link.aps.org/doi/10.1103/PhysRevLett.89.080401"
[4]: https://arxiv.org/abs/1402.0111 "https://arxiv.org/abs/1402.0111"
[5]: https://arxiv.org/abs/1506.08763 "https://arxiv.org/abs/1506.08763"
[6]: https://link.aps.org/doi/10.1103/PhysRevLett.120.020505 "https://link.aps.org/doi/10.1103/PhysRevLett.120.020505"
[7]: https://link.aps.org/doi/10.1103/PhysRevLett.87.040402 "https://link.aps.org/doi/10.1103/PhysRevLett.87.040402"
[8]: https://arxiv.org/abs/1306.4352 "https://arxiv.org/abs/1306.4352"

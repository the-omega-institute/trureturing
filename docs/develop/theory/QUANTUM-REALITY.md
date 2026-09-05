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

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
这轮可以把“记录改变波”推进到一个更深的、可计算的联系：

> **记录结构怎样变化，既决定系统偏离目标状态的概率，也决定它沿闭合路径积累什么相位。两者可以由同一个量子几何对象约束。**

但还要补上一个关键修正：**偏离概率不只由测量频率决定，而由自然演化与测量路径之间的失配决定。**当两者已经匹配时，不需要靠无限刷新也能保持跟随。

移动测量子空间、Zeno 动力学与几何相位之间的联系已有理论和实验基础。本轮的任务，是把它们接入项目的观察接口、动力下降和误差证书，而不是仅凭相似性宣布已经导出了引力。([arXiv][1])

# 移动观察接口的量子几何与动力失配

## ——量子观察者—关系时空理论第二百三十一至第二百四十节增订

---

# 231．同样的记录问题，不一定对应同样的物理反作用

先补齐一个会影响后续全部推导的类型区别。

## 定义231.1　投影读数与记录操作

取有限维 Hilbert 空间 \(\mathcal H\)，以及投影

$$
P=P^\dagger=P^2,
\qquad
Q=I-P.
$$

测量“系统是否位于 \(P\mathcal H\)”的概率是

$$
p_P(\rho)=\operatorname{Tr}(P\rho).
$$

但这个概率公式没有唯一指定测量后的状态。

一种实现是 Lüders 仪器：

$$
\boxed{
\mathcal I_P(\rho)=P\rho P,
\qquad
\mathcal I_Q(\rho)=Q\rho Q.
}
\tag{231.1}
$$

另一种实现可以是

$$
\boxed{
\widetilde{\mathcal I}_P(\rho)=VP\rho PV^\dagger,
\qquad
\widetilde{\mathcal I}_Q(\rho)=Q\rho Q,
}
\tag{231.2}
$$

其中 \(V\) 为保持 \(P\mathcal H\) 的酉算子。

两者给出相同的结果概率，却可能有不同的后续动力学。

## 定理231.1　概率接口不唯一决定记录实现

取三维空间，

$$
P=\operatorname{diag}(1,1,0),
$$

令 \(V\) 交换 \(|0\rangle,|1\rangle\)，保持 \(|2\rangle\) 不变。

对输入 \(|0\rangle\)，两种仪器都必然报告“位于 \(P\) 内”，但条件输出分别是

$$
\boxed{
|0\rangle\langle0|,
\qquad
|1\rangle\langle1|.
}
\tag{231.3}
$$

### 证明

两种成功分支的效果算子分别为

$$
P^\dagger P=P,
\qquad
(VP)^\dagger VP=P.
$$

所以结果概率相同。

但 \(P|0\rangle=|0\rangle\)，而 \(VP|0\rangle=|1\rangle\)。∎

**因此，CUT 指定“问什么”，还不等于 FLOW 指定“怎样问”。**

下面的投影链，明确采用式（231.1），不暗中插入额外的子空间内旋转。真实装置是否实现这一仪器，需要另外检验。

项目的 `EnvironmentRecords.lean` 已经把记录规则、联合状态、偏迹及约化通道分别定义；这个区分应继续保留。

---

# 232．移动接口的真正逃逸量，是动力与目标的失配

上一轮主要研究固定投影 \(P\)。现在允许观察者改变要保持的记录结构。

## 假设232.1　移动的目标子空间

设

$$
P(t)^2=P(t)=P(t)^\dagger
$$

是固定秩的 \(C^2\) 投影族。时间 \(t\) 沿用已经标定的参照，不在本节重新定义秒。

系统自然 Hamiltonian 为光滑的有限维自伴算子 \(H(t)\)。记

$$
Q(t)=I-P(t).
$$

初态满足

$$
\rho=P(t)\rho P(t).
$$

经过自然演化 \(U(t+\delta,t)\) 后，测量新的投影 \(P(t+\delta)\)。

## 定义232.1　移动接口的失配算子

定义

$$
\boxed{
B(t)
=
Q(t)H(t)P(t)
-i\hbar\dot P(t)P(t).
}
\tag{232.1}
$$

第一项描述自然动力学将振幅送出当前子空间的作用；第二项描述目标子空间本身的移动。

## 定理232.1　短时跟随失败概率

有

$$
\boxed{
p_{\mathrm{fail}}(t,\delta)
=
\frac{\delta^2}{\hbar^2}
\operatorname{Tr}\!\left[\rho B(t)^\dagger B(t)\right]
+
O(\delta^3).
}
\tag{232.2}
$$

### 证明

使用

$$
U(t+\delta,t)
=
I-\frac{i\delta}{\hbar}H(t)+O(\delta^2),
$$

以及

$$
Q(t+\delta)=Q(t)-\delta\dot P(t)+O(\delta^2).
$$

于是

$$
\begin{aligned}
Q(t+\delta)U(t+\delta,t)P(t)
&=
-\delta\dot P P
-\frac{i\delta}{\hbar}QHP
+O(\delta^2)\\
&=
-\frac{i\delta}{\hbar}B(t)+O(\delta^2).
\end{aligned}
$$

对该失败振幅取平方并与 \(\rho\) 配对，即得。∎

### 一个重要结果

一般不能写成

$$
p_{\mathrm{fail}}
\propto
\|QHP\|^2+\hbar^2\|\dot PP\|^2,
$$

因为两项之间存在交叉项，可能相互增强，也可能相消。

**“系统自己在变化”和“观察者改变目标”并非两项独立损耗。真正决定失败的是它们是否匹配。**

这比把一切变化都叫作“信息逃逸”更准确：式（232.1）具有明确对象、量纲和可测结果。

---

# 233．同样的终点与成功率，仍然可能留下不同的关系相位

现在取最简单的情形：

$$
H=0,
\qquad
P_j=|\psi_j\rangle\langle\psi_j|,
$$

其中每个 \(|\psi_j\rangle\) 归一化，且

$$
P_N=P_0.
$$

选择相同的首尾代表向量 \(|\psi_N\rangle=|\psi_0\rangle\)。

## 定理233.1　有限投影闭路的精确振幅

从 \(|\psi_0\rangle\) 开始，全部测量都得到指定投影结果时，未归一化末态为

$$
\boxed{
P_N\cdots P_1|\psi_0\rangle
=
z_N|\psi_0\rangle,
}
\tag{233.1}
$$

其中

$$
\boxed{
z_N
=
\prod_{j=1}^N
\langle\psi_j|\psi_{j-1}\rangle.
}
\tag{233.2}
$$

成功概率为

$$
\boxed{
p_N=|z_N|^2.
}
\tag{233.3}
$$

### 证明

逐次应用秩一投影，每一步提取一个相邻态重叠。∎

中间代表向量改变相位，不改变这个闭路乘积。因此，它不是任意基底相位命名造成的结果。

但单独观察成功后的系统密度矩阵，只会看到 \(P_0\)。要读取 \(\arg z_N\)，必须有相干参照和明确的联合实现。

---

## 例233.1　两条相反闭路

取

$$
|x+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},
\qquad
|y+\rangle=\frac{|0\rangle+i|1\rangle}{\sqrt2}.
$$

比较两条路径：

$$
|0\rangle\to|x+\rangle\to|y+\rangle\to|0\rangle,
$$

$$
|0\rangle\to|y+\rangle\to|x+\rangle\to|0\rangle.
$$

直接得到

$$
\boxed{
z_{\rightarrow}=\frac{1-i}{4},
\qquad
z_{\leftarrow}=\frac{1+i}{4}.
}
\tag{233.4}
$$

两者都有

$$
\boxed{p_{\mathrm{success}}=\frac18,}
\tag{233.5}
$$

成功后的系统态也完全相同，但相位分别为 \(-\pi/4\) 与 \(+\pi/4\)。

---

## 一个完整的参照读出

引入控制比特。每一步使用成功 Kraus 算子

$$
K_j
=
|0\rangle\langle0|\otimes I
+
|1\rangle\langle1|\otimes P_j,
$$

以及失败算子

$$
L_j
=
|1\rangle\langle1|\otimes(I-P_j).
$$

它们满足

$$
K_j^\dagger K_j+L_j^\dagger L_j=I.
$$

控制比特从 \(|+\rangle\) 开始。全部步骤成功后，其未归一化态为

$$
\frac{|0\rangle+z_N|1\rangle}{\sqrt2}.
$$

对上述两条路径，整个受控实验的成功概率均为 \(9/16\)。条件于成功，再测量控制比特的 \(Y=+1\) 结果，其概率分别为

$$
\boxed{
\frac5{18},
\qquad
\frac{13}{18}.
}
\tag{233.6}
$$

**这给出一个新的明确残差：终点状态与成功率，仍不足以预测相干路径比较。**

测量序列产生并读取几何相位，已有实验实现；其中相位参照和动力学相位分离都是实验的一部分，不能省略。([arXiv][2])

---

# 234．同一个重叠结构，产生量子度量与相位曲率

## 定义234.1　平滑记录方向族

设参数为

$$
\lambda=(\lambda^1,\ldots,\lambda^m),
$$

归一化态为

$$
|\psi(\lambda)\rangle,
\qquad
P(\lambda)=|\psi(\lambda)\rangle\langle\psi(\lambda)|.
$$

定义去除纯相位方向后的变化

$$
|D_a\psi\rangle
=
(I-P)|\partial_a\psi\rangle,
$$

以及

$$
\boxed{
\mathcal Q_{ab}
=
\langle D_a\psi|D_b\psi\rangle.
}
\tag{234.1}
$$

令

$$
\boxed{
G_{ab}=\operatorname{Re}\mathcal Q_{ab},
}
\tag{234.2}
$$

并选择相位连接约定

$$
A_a=i\langle\psi|\partial_a\psi\rangle.
$$

相位曲率为

$$
F_{ab}=\partial_aA_b-\partial_bA_a.
$$

这里的 \(\mathcal Q\) 就是量子几何张量；实部与虚部分别描述相邻态的可区分变化和相位曲率，这是已有量子几何框架。([arXiv][3])

## 定理234.1　失败概率与相位曲率来自同一张量

有

$$
\boxed{
1-\operatorname{Tr}[P(\lambda+d\lambda)P(\lambda)]
=
G_{ab}\,d\lambda^a d\lambda^b
+
O(|d\lambda|^3),
}
\tag{234.3}
$$

以及

$$
\boxed{
F_{ab}=-2\operatorname{Im}\mathcal Q_{ab}.
}
\tag{234.4}
$$

### 证明

对相邻态的重叠作二阶展开，利用归一化条件消去一阶实部，剩余二阶项正是

$$
\langle d\psi|(I-P)|d\psi\rangle.
$$

另一方面，

$$
\partial_aA_b-\partial_bA_a
=
i\left(
\langle\partial_a\psi|\partial_b\psi\rangle
-
\langle\partial_b\psi|\partial_a\psi\rangle
\right).
$$

去除 \(P\) 的部分只改变实部，故得到式（234.4）。∎

---

## 定理234.2　记录变化与相位曲率的正性约束

对任意两个参数方向 \(a,b\)，

$$
\boxed{
F_{ab}^2
\le
4\left(G_{aa}G_{bb}-G_{ab}^2\right).
}
\tag{234.5}
$$

### 证明

\(\mathcal Q\) 是向量族 \(\{|D_a\psi\rangle\}\) 的 Gram 矩阵，因此半正定。

其二阶主子式非负：

$$
\mathcal Q_{aa}\mathcal Q_{bb}
-
|\mathcal Q_{ab}|^2\ge0.
$$

代入式（234.2）、（234.4）即可。∎

这给出一个可联合检验的约束：

> **不能任意指定“这两个方向上记录态几乎完全不变”，同时又指定一个与之不相容的巨大局部相位曲率。**

但它不是说任何闭路相位都必然伴随不可消除的失败概率。下一节会显示，增加测量次数可以压低累计失败，而保留有限的闭路相位。

---

# 235．给定记录路径，有限刷新次数具有几何代价

本节仍然限定为 \(H=0\) 的纯投影跟随，不添加额外补偿 Hamiltonian。

## 定义235.1　相邻记录方向的距离

定义

$$
d_j
=
\arccos|\langle\psi_j|\psi_{j-1}\rangle|,
\qquad
0\le d_j\le\frac\pi2,
$$

以及离散路径长度

$$
L_N=\sum_{j=1}^Nd_j.
$$

它们是无量纲的量子态距离，不是空间中的米制长度。

## 定理235.1　有限步成功概率上界

若所有相邻重叠非零，则

$$
\boxed{
-\log p_N
\ge
\sum_{j=1}^Nd_j^2
\ge
\frac{L_N^2}{N}.
}
\tag{235.1}
$$

因此

$$
\boxed{
p_N\le e^{-L_N^2/N}.
}
\tag{235.2}
$$

### 证明

由定理233.1，

$$
-\log p_N=-2\sum_j\log\cos d_j.
$$

对 \(0\le x<\pi/2\)，因为 \(\tan x\ge x\)，积分得到

$$
-2\log\cos x\ge x^2.
$$

再对 \(d_j\) 使用 Cauchy–Schwarz 不等式：

$$
\sum_jd_j^2\ge\frac{(\sum_jd_j)^2}{N}.
$$

∎

更强地，由 \(-2\log\cos x\) 的凸性，

$$
p_N\le
\cos^{2N}\left(\frac{L_N}{N}\right).
$$

给定总离散长度时，相邻步骤距离相等使这一上界达到。

---

## 定理235.2　连续路径的最优刷新分配

设一条固定的光滑路径用 \(s\in[0,1]\) 参数化，并均匀采样 \(N\) 次。则

$$
\boxed{
-\log p_N
=
\frac1N
\int_0^1
G_{ab}(\lambda(s))
\dot\lambda^a(s)\dot\lambda^b(s)\,ds
+
O(N^{-2}).
}
\tag{235.3}
$$

定义其量子几何长度

$$
L=\int_0^1
\sqrt{G_{ab}\dot\lambda^a\dot\lambda^b}\,ds.
$$

则

$$
\boxed{
\int_0^1G_{ab}\dot\lambda^a\dot\lambda^b\,ds
\ge L^2.
}
\tag{235.4}
$$

等号对应恒定量子几何速度的参数化。

### 证明

将式（234.3）用于每段长度 \(1/N\) 的变化，再展开 \(-\log(1-x)\) 并求和，得到式（235.3）。

式（235.4）为积分形式的 Cauchy–Schwarz 不等式。∎

### 操作性解释

同样多的刷新次数，不一定应该按仪器时间机械均分。更合理的分配是：

$$
\boxed{
\text{记录方向变化快的区域，多分配测量；
变化慢的区域，少分配测量}.
}
$$

量子态几何与 Zeno 存活概率之间的关系已有研究。本节给出的是指定有限路径和投影协议下的精确界与渐近优化。([arXiv][4])

这里的 \(-\log p_N\) 是跟随失败的概率指标，不自动等于热量、装置耗能或记录的总熵。

---

# 236．一个完整例子：成功率趋于一，闭路相位仍然存在

## 定义236.1　量子比特的纬线记录族

取

$$
|\psi(\theta,\phi)\rangle
=
\cos\frac\theta2|0\rangle
+
e^{i\phi}\sin\frac\theta2|1\rangle.
$$

固定

$$
0<\theta\le\frac\pi2,
$$

让 \(\phi\) 从零增加到 \(2\pi\)。

## 定理236.1　同一族态的度量、曲率与有限步概率

直接计算得到

$$
\boxed{
G=\frac14
\begin{pmatrix}
1&0\\
0&\sin^2\theta
\end{pmatrix},
}
\tag{236.1}
$$

$$
\boxed{
A_\phi=-\frac{1-\cos\theta}{2},
\qquad
F_{\theta\phi}=-\frac12\sin\theta.
}
\tag{236.2}
$$

定理234.2在这里取等号。

把回路分成 \(N\ge3\) 个等角步骤，则

$$
\boxed{
z_N=
\left[
\cos^2\frac\theta2
+
e^{-2\pi i/N}\sin^2\frac\theta2
\right]^N,
}
\tag{236.3}
$$

$$
\boxed{
p_N=
\left[
1-\sin^2\theta\sin^2\frac\pi N
\right]^N.
}
\tag{236.4}
$$

### 证明

求态向量的一阶导数并代入定义234.1，得到式（236.1）—（236.2）。

相邻态重叠相同，逐步相乘得到式（236.3）；取模平方得到式（236.4）。∎

在 \(N\to\infty\) 时，

$$
\boxed{
z_N\longrightarrow
e^{-i\pi(1-\cos\theta)},
\qquad
p_N\longrightarrow1.
}
\tag{236.5}
$$

但

$$
\boxed{
-N\log p_N
\longrightarrow
\pi^2\sin^2\theta=L^2.
}
\tag{236.6}
$$

如果记这一方向下的相位大小为

$$
\Gamma=\pi(1-\cos\theta)\in(0,\pi],
$$

则

$$
\boxed{
L^2=\Gamma(2\pi-\Gamma).
}
\tag{236.7}
$$

这是该纬线路径族的关系，不是任意量子控制协议的普遍代价公式。

### 关键结果

$$
\boxed{
\text{失败概率可以趋零，
而有限几何相位不必消失}.
}
$$

因此，“没有离开指定记录族”不等于“没有发生任何可读物理变化”。

增加测量次数所需的仪器、接触时间和参照资源仍然存在，不能由 \(p_N\to1\) 推出整个过程免费。

---

# 237．高维观察者可以保持身份，同时发生内部几何演化

一维投影只能保存一个纯态方向。若要保留观察者内部的多种记忆状态，更自然的是使用固定秩 \(r>1\) 的子空间。

## 定义237.1　移动子空间的平行输运

设 \(P(t)\) 为固定秩的光滑投影。定义

$$
\boxed{
K(t)=[\dot P(t),P(t)].
}
\tag{237.1}
$$

令 \(W(t)\) 满足

$$
\dot W=KW,
\qquad W(0)=I.
$$

## 定理237.1　存在保持子空间身份的酉输运

有

$$
\boxed{
K^\dagger=-K,
}
\tag{237.2}
$$

$$
\boxed{
W(t)^\dagger P(t)W(t)=P(0).
}
\tag{237.3}
$$

### 证明

投影及其导数自伴，所以交换子反自伴，\(W\) 因而酉。

对 \(P^2=P\) 求导，得到

$$
P\dot PP=0,
\qquad
[[\dot P,P],P]=\dot P.
$$

于是

$$
\frac d{dt}(W^\dagger PW)
=
W^\dagger(\dot P-[K,P])W=0.
$$

∎

在随 \(W\) 移动的描述中，观察者的身份子空间始终是同一个 \(P(0)\)。但完整物理实现可以在外部表示中持续变化。

---

## 定理237.2　有限投影链逼近该输运

设

$$
\|\dot P(t)\|\le a,
\qquad
\|\ddot P(t)\|\le b.
$$

对 \(H=0\)、总时间 \(T\) 和 \(N\) 次等间隔投影，有

$$
\boxed{
\left\|
P(T)P(T-\delta)\cdots P(\delta)P(0)
-
W(T)P(0)
\right\|
\le
\frac{(3b+a^2)T^2}{2N},
}
\tag{237.4}
$$

其中 \(\delta=T/N\)。

### 证明

投影一步展开为

$$
P(t+\delta)P(t)
=
P+\delta\dot PP+O(\delta^2b).
$$

而平行输运一步展开为

$$
W(t+\delta,t)P
=
P+\delta KP
+O\!\left(\delta^2(2b+a^2)\right).
$$

由 \(KP=\dot PP\)，两者一阶项相同。

使用积分余项给出的二阶界，再对 \(N\) 步作望远镜展开；投影为压缩算子，\(W\) 为酉算子，得到式（237.4）。∎

---

## 内部有效动力学

若保留自然 Hamiltonian \(H(t)\)，相应的移动子空间生成元为

$$
\boxed{
H_Z(t)
=
P(t)H(t)P(t)
+
i\hbar[\dot P(t),P(t)].
}
\tag{237.5}
$$

选择局部正交标架

$$
V(t):\mathbb C^r\to\mathcal H,
\qquad
V^\dagger V=I_r,
\qquad
VV^\dagger=P,
$$

则内部坐标 \(c(t)\) 满足

$$
\boxed{
i\hbar\dot c
=
\left[
V^\dagger HV-i\hbar V^\dagger\dot V
\right]c.
}
\tag{237.6}
$$

后一项是移动记录标架引入的连接。它可以是矩阵，不同路径产生的内部变换也可能不交换。

移动 Zeno 子空间与非阿贝尔几何操作之间已有理论联系；相应的几何生成元也出现在自适应 Zeno 与无跃迁控制研究中。([arXiv][1])

**“观察者身份保持”因此不要求“观察者内部一切都不动”。**稳定的编码类型与非平凡的内部时钟、记忆变换可以相容。

---

# 238．自然演化与记录移动可以相消：不能把每次成功都解释成 Zeno

现在返回定理232.1的失配算子。

## 定义238.1　两个不同的转动速率

令实际 Hamiltonian 为

$$
H=\frac{\hbar\Omega}{2}Y.
$$

观察者希望系统跟随的投影族为

$$
P(t)=|\psi_\omega(t)\rangle\langle\psi_\omega(t)|,
$$

$$
|\psi_\omega(t)\rangle
=
\cos\frac{\omega t}{2}|0\rangle
+
\sin\frac{\omega t}{2}|1\rangle.
$$

## 定理238.1　失败由相对速率决定

每隔 \(T/N\) 测量一次目标投影，全部跟随成功的概率为

$$
\boxed{
p_N(\Omega,\omega)
=
\cos^{2N}
\left[
\frac{(\Omega-\omega)T}{2N}
\right].
}
\tag{238.1}
$$

### 证明

若上一轮成功，状态为 \(|\psi_\omega(t)\rangle\)。

实际 Hamiltonian 在一个间隔中使它转动 \(\Omega T/N\)，而新的目标转动 \(\omega T/N\)。两态的重叠为

$$
\cos\frac{(\Omega-\omega)T}{2N}.
$$

条件概率相乘即可。∎

特别地，

$$
\boxed{
\Omega=\omega
\quad\Rightarrow\quad
p_N=1
}
\tag{238.2}
$$

对每个有限 \(N\) 都成立。

此时系统本来就在沿目标演化。测量全部成功，并不能证明仪器抑制了本来会发生的跃迁。

在该实例中，

$$
QHP=i\hbar\dot PP,
$$

所以

$$
\boxed{B(t)=0.}
\tag{238.3}
$$

### 对上一轮的进一步修正

“刷新更密，使失败率更低”只描述某些比较条件。

更完整的实验至少要同时改变：

$$
\text{自然驱动速率 }\Omega,
\qquad
\text{记录路径速率 }\omega,
\qquad
\text{刷新间隔}.
$$

这样才能区分自然跟随、测量引导、失配抑制和其他噪声机制。

---

## 同一条路径的另一种实现

若不采用后选择测量，而直接用 Hamiltonian \(H_{\mathrm{ctrl}}\) 实现同一条归一化纯态轨迹，则

$$
\boxed{
\Delta H_{\mathrm{ctrl}}
=
\hbar\sqrt{G_{ab}\dot\lambda^a\dot\lambda^b}.
}
\tag{238.4}
$$

因为 Schrödinger 方程给出

$$
(I-P)|\dot\psi\rangle
=
-\frac i\hbar
(H_{\mathrm{ctrl}}-\langle H_{\mathrm{ctrl}}\rangle)|\psi\rangle.
$$

因此

$$
\int_0^T\Delta H_{\mathrm{ctrl}}\,dt=\hbar L.
$$

在这类直接酉实现中，若 \(\Delta H_{\mathrm{ctrl}}\le E_{\max}\)，则

$$
\boxed{
T\ge\frac{\hbar L}{E_{\max}}.
}
\tag{238.5}
$$

这不能直接套到归一化的后选择分支上；测量实现还要计算成功概率、仪器与辅助资源。

**同一条量子几何路径可以有不同物理实现，但不能因此省略实现成本。**

---

# 239．为什么这些几何仍然不等于物理时空曲率？

现在确实得到了：

$$
G_{ab},\qquad A_a,\qquad F_{ab}.
$$

但它们首先属于**记录方向或控制参数空间**。

## 定理239.1　量子态度量不能仅靠实坐标变换变成 Lorentz 度量

对任意实向量 \(u\)，

$$
u^aG_{ab}u^b
=
\left\|
u^aD_a\psi
\right\|^2
\ge0.
$$

因此，对任意实 Jacobian \(J\)，

$$
\boxed{
J^{\mathsf T}GJ\ge0.
}
\tag{239.1}
$$

它不能直接变成具有一个负方向的非退化 Lorentz 度量。

### 证明

正半定性在实合同变换下保持。∎

同样：

$$
F_{ab}
$$

是控制参数空间上的二形式，而完整时空 Riemann 曲率具有不同的张量类型和作用对象。

有限量子装置已经可以具有非零的 \(F\)，即使模型根本没有定义引力自由度。因此，从“测到了 Berry 相位”直接推出“形成了引力曲率”，缺少必要的逻辑桥梁。

项目 `WormholeHolonomy.lean` 自身也明确声明：它的往返不平凡性是类型化动力网络中的概念，不直接等同于微分几何 holonomy。

### 真正需要继续连接的部分

若要进入物理时空，必须给出实际实现：

$$
\boxed{
\text{控制参数如何由局域物理场承担};
}
$$

$$
\boxed{
\text{这些场怎样影响共同钟与信号};
}
$$

$$
\boxed{
\text{量子输运怎样与时空标架和能量反作用相容}.
}
$$

只有这些映射及其相容条件成立，才有资格把某些量子几何结构识别为某种有效物理几何。

测量诱导的几何相位及其对测量强度的依赖已有实验研究，这支持的是相应量子控制机制，不自动验证整套观察者时空理论。([arXiv][5])

---

# 240．本轮得到的统一结构与形式化落点

本轮出现了一个比“观察改变波”更精确的三角关系：

$$
\boxed{
\text{相邻记录态的重叠}
}
$$

同时决定

$$
\boxed{
\text{跟随成功率}
,\quad
\text{量子态距离}
,\quad
\text{闭路相位}.
}
$$

而当自然动力学也参与时，必须首先使用

$$
\boxed{
B=QHP-i\hbar\dot PP
}
$$

计算动力与目标之间的失配，而不能把两种作用的强度简单相加。

这给项目三种不同的“余量”：

| 余量     | 精确定义或实例                 | 它回答的问题             |
| ------ | ----------------------- | ------------------ |
| 动力跟随余量 | \(B=QHP-i\hbar\dot PP\) | 自然演化是否跟得上当前目标子空间？  |
| 有限刷新余量 | \(1-p_N\)、投影乘积与平行输运之差   | 有限次记录是否足够实现指定跟随？   |
| 观察接口残差 | 相同终点与成功率、不同干涉相位         | 当前保存的数据是否足够预测新增实验？ |

它们有联系，但不是同一个标量。

## 与项目已有模块的连接

本轮读取固定于提交

```text
8825fbe111c7fc39ddf4032a03192f1d20dfc7c8
```

其中，记录重叠模块可承担单次约化；往返模块提供路径组合的类型边界；精确下降模块用于判定一个较粗接口是否足以预测相干比较。

最适合逐层形式化的依赖为：

$$
\boxed{
P^2=P
\Rightarrow
P\dot PP=0
\Rightarrow
B\text{ 的短时失败公式};
}
$$

$$
\boxed{
\text{有限投影乘积}
\Rightarrow
z_N,\ p_N
\Rightarrow
\text{相位与概率的分离见证};
}
$$

$$
\boxed{
\text{Gram 正性}
\Rightarrow
G,\ F
\Rightarrow
F_{ab}^2\le4\det G_{ab};
}
$$

$$
\boxed{
\text{有限矩阵微分方程}
\Rightarrow
\text{移动子空间输运}
\Rightarrow
O(N^{-1})\text{ 实现误差}.
}
$$

本轮完成了 **31项精确有限算例与符号恒等式检查**，包括两种相同读数但不同更新的仪器、三步闭路、相干参照读出、量子几何张量、动力失配相消和纬线闭路公式。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_moving_zeno_geometry.py)
[核验结果](sandbox:/mnt/data/observer_formalization/moving_zeno_geometry_checks.json)

本轮没有进行 Lean 内核检查；这些核验不替代一般分析定理的机器证明，也不证明模型已经对应现实引力。

---

# 结论

这轮最重要的推进，是把“稳定的观察者”与“持续变化的世界”之间的关系写得更清楚：

> **观察者可以保持一个可识别的内部结构，同时让这个结构在更大的量子空间中被输运；这种输运既有失败概率，也可能留下不能由终点状态单独读取的路径相位。**

因此，三个看似分开的现象现在具有共同来源：

$$
\boxed{
\text{Zeno 跟随}
\longleftrightarrow
\text{相邻投影的重叠};
}
$$

$$
\boxed{
\text{几何相位}
\longleftrightarrow
\text{闭路重叠的复相位};
}
$$

$$
\boxed{
\text{有限控制精度}
\longleftrightarrow
\text{同一重叠结构的量子度量}.
}
$$

同时，我们找到了一个不能省略的修正：

$$
\boxed{
\text{记录改变得快}
\not\Rightarrow
\text{必然更难跟随};
}
$$

真正要看的是它是否与自然演化匹配。

**这使“观察者选择波”的直觉获得了更严格的内容：观察者通过实际装置选择和移动可保持的子空间；自然动力学、记录路径与资源预算共同决定，哪些变化能够发生、哪些变化被抑制，以及哪些历史区别最终留在可读的关系相位中。**

下一步最值得继续研究的，是把这里的控制参数本身也提升为有限量子观察者的内部变量：不再预先给定 \(P(t)\)，而是让产生 \(P(t)\) 的钟、控制器和记忆一起演化，并检验这条几何输运能否在一个真正闭合的自主系统中实现。

[1]: https://arxiv.org/abs/1305.6433 "https://arxiv.org/abs/1305.6433"
[2]: https://arxiv.org/html/1903.05122v2 "https://arxiv.org/html/1903.05122v2"
[3]: https://arxiv.org/abs/1602.01062 "https://arxiv.org/abs/1602.01062"
[4]: https://arxiv.org/abs/quant-ph/9803082 "https://arxiv.org/abs/quant-ph/9803082"
[5]: https://arxiv.org/html/2102.05660v2 "https://arxiv.org/html/2102.05660v2"
这一轮可以把上一节留下的外部控制器，真正放回量子模型内部。

此前我们写下

$$
P(t),
$$

表示观察者随时间改变希望保持的子空间。但这里隐含着一个尚未解释的角色：**是谁知道“现在到了哪个时刻”，并据此把测量装置切换到对应的 \(P(t)\)？**

如果这个角色始终放在模型外面，那么观察者还不是一个完整的物理系统。

下面构造一个明确的有限模型，证明：

> **任意给定的有限记录程序，都可以编码进一个固定、有限维、自伴且有下界的 Hamiltonian。运行过程中不必由外部逐步开关操作；时钟、被观察系统和全部结果记录一起演化。**

但这个构造也会暴露新的边界：自主运行不等于无反作用，条件历史不等于不可逆时间，而精确连续控制不能由任意小的有限程序寄存器免费实现。

固定 Hamiltonian 的计算、有限量子钟和自主控制已有相应研究。本文采用这些方法的有限构造，把它们接入当前观察者理论，不把一般机制宣称为首次发现。([Springer][1])

# 自主量子观察者、内部时钟与记录历史的闭合

## ——量子观察者—关系时空理论第二百四十一至第二百五十节增订

---

# 241．自主观察者应当包含什么？

## 定义241.1　有限记录程序

取系统空间 \(\mathcal H_S\)，以及一组准备实施的投影：

$$
P_1,\ldots,P_N,
\qquad
P_j=P_j^\dagger=P_j^2.
$$

它们可以是上一轮移动投影 \(P(t)\) 在有限组参数点上的取值。

给每一步分配一个记录比特 \(M_j\)，全部记录初始为

$$
|0^N\rangle_M.
$$

定义第 \(j\) 步联合操作

$$
\boxed{
V_j
=
P_j\otimes I_{M_j}
+
(I-P_j)\otimes X_{M_j},
}
\tag{241.1}
$$

在其他记录寄存器上作用为恒等。

这里，记录结果 \(0\) 对应 \(P_j\)，结果 \(1\) 对应 \(I-P_j\)。

---

## 定理241.1　每一次投影读数都具有可逆的联合实现

有

$$
\boxed{
V_j^\dagger=V_j,
\qquad
V_j^2=I.
}
\tag{241.2}
$$

并且

$$
\boxed{
V_j\bigl(|\psi\rangle|0\rangle\bigr)
=
P_j|\psi\rangle|0\rangle
+
(I-P_j)|\psi\rangle|1\rangle.
}
\tag{241.3}
$$

### 证明

使用

$$
P_j(I-P_j)=0,
\qquad
P_j^2=P_j,
\qquad
X^2=I.
$$

展开平方与作用即可。∎

这意味着：**不必在基本演化中插入一个非酉的“坍缩按钮”。**可以先让系统与实际记录建立关联，再通过记录接口得到各分支概率。

项目的 `EnvironmentRecords.lean` 已经分别定义条件记录联合态、环境偏迹和记录通道；本节沿用这种分层，而不是把读数概率直接当作全部动力学。

### 必须明确的选择

目前的 \(P_1,\ldots,P_N\) 仍然是一份已经给定的程序。

本轮要证明的是：

$$
\boxed{
\text{这份程序怎样由系统内部自主执行}.
}
$$

尚未证明的是：

$$
\boxed{
\text{为什么自然界或某个观察者必须选择这份程序}.
}
$$

把控制规律写进模型，与推导控制规律的来源，是两项不同任务。

---

# 242．把全部操作写进同一个固定 Hamiltonian

## 定义242.1　时钟寄存器与累计程序

引入时钟空间

$$
\mathcal H_C
=
\operatorname{span}\{|0\rangle,\ldots,|N\rangle\}.
$$

令数据空间包含系统和全部记录：

$$
\mathcal H_D=\mathcal H_S\otimes\mathcal H_M.
$$

定义累计操作

$$
G_0=I,
\qquad
G_j=V_jV_{j-1}\cdots V_1.
\tag{242.1}
$$

构造联合酉变换

$$
\boxed{
\mathsf G
=
\sum_{j=0}^N|j\rangle\langle j|\otimes G_j.
}
\tag{242.2}
$$

---

## 定义242.2　自主传播 Hamiltonian

取频率尺度 \(\Omega>0\)，定义

$$
\boxed{
\begin{aligned}
H_{\mathrm{aut}}
={}&
\frac{\hbar\Omega N}{2}I\\
&+
\frac{\hbar\Omega}{2}
\sum_{j=1}^N
\sqrt{j(N+1-j)}
\left(
|j\rangle\langle j-1|\otimes V_j
+
|j-1\rangle\langle j|\otimes V_j^\dagger
\right).
\end{aligned}
}
\tag{242.3}
$$

这个 Hamiltonian 不随运行时间改变。

它表达的是：

> 时钟从标签 \(j-1\) 转移到 \(j\) 时，同时实施第 \(j\) 个记录交互；反向传播则实施其逆过程。

不是外部计时器命令“现在执行第 \(j\) 步”，而是这种关联已经写进固定耦合。

---

## 定理242.1　程序可以与纯时钟传播精确分离

定义仅作用于时钟的矩阵

$$
K_C
=
\frac{\hbar\Omega N}{2}I_C
+
\frac{\hbar\Omega}{2}
\sum_{j=1}^N
\sqrt{j(N+1-j)}
\left(
|j\rangle\langle j-1|
+
|j-1\rangle\langle j|
\right).
$$

则

$$
\boxed{
H_{\mathrm{aut}}
=
\mathsf G(K_C\otimes I_D)\mathsf G^\dagger.
}
\tag{242.4}
$$

### 证明

对每条相邻时钟边，

$$
G_jG_{j-1}^\dagger=V_j.
$$

因此

$$
\mathsf G
\bigl(|j\rangle\langle j-1|\otimes I\bigr)
\mathsf G^\dagger
=
|j\rangle\langle j-1|\otimes V_j.
$$

对全部边求和即可。∎

这类把程序编码进时钟传播耦合的方法属于 Feynman 型 Hamiltonian 计算。这里选取的特殊耦合还允许精确完成传输，而不必在运行中切换边。([APS Journals][2])

### 能量闭合的范围

式（242.3）是有限维自伴算子，因此产生完整酉演化。

但“总 Hamiltonian 守恒”还不能替代以下额外证明：

* 它是否满足已经指定的裸系统能量账本；
* 它能否用给定的空间局域相互作用实现；
* 制备初态、加工固定耦合和保存最终输出需要什么资源。

本轮先完成固定总动力学层，不把这些物理实现条件偷偷略去。

---

# 243．这个有限自主模型确实能够完成整个程序

## 定理243.1　时钟的精确传播公式

从

$$
|0\rangle_C\otimes|\chi\rangle_D
$$

开始，其中 \(|\chi\rangle_D\) 可以包含任意系统输入和准备好的记录，则

$$
\boxed{
e^{-itH_{\mathrm{aut}}/\hbar}
|0\rangle|\chi\rangle
=
\sum_{j=0}^N c_j(t)|j\rangle G_j|\chi\rangle,
}
\tag{243.1}
$$

其中

$$
\boxed{
c_j(t)
=
e^{-iN\Omega t/2}
(-i)^j\sqrt{\binom Nj}
\sin^j\frac{\Omega t}{2}
\cos^{N-j}\frac{\Omega t}{2}.
}
\tag{243.2}
$$

### 证明

由定理242.1，只需计算 \(K_C\) 的演化。

将 \(\mathcal H_C\) 识别为 \(N\) 个量子比特的完全对称子空间，\(|j\rangle\) 对应具有 \(j\) 个激发的归一化对称态。

在该空间中，

$$
K_C
=
\hbar\Omega\left(J_x+\frac N2I\right),
\qquad
J_x=\frac12\sum_{r=1}^NX_r.
$$

从全部为零的初态出发，每个比特都演化为

$$
\cos\frac{\Omega t}{2}|0\rangle
-i\sin\frac{\Omega t}{2}|1\rangle.
$$

展开其 \(N\) 重张量积，得到式（243.2）。再用 \(\mathsf G\) 变回程序表示。∎

---

## 推论243.1　有限时间的精确完成

在

$$
\boxed{
t_*=\frac{\pi}{\Omega}
}
\tag{243.3}
$$

时，

$$
\boxed{
e^{-it_*H_{\mathrm{aut}}/\hbar}
|0\rangle|\chi\rangle
=
(-1)^N|N\rangle G_N|\chi\rangle.
}
\tag{243.4}
$$

因此，忽略无关整体相位，全部 \(N\) 个记录交互已经精确完成，而且时钟与最终数据重新分离。

### 关键解释

这里没有在运行途中：

$$
t_1\text{ 时打开 }V_1,\quad
t_2\text{ 时打开 }V_2,\quad\ldots
$$

全部顺序由一个固定 Hamiltonian 实现。

不过，中途的时钟通常不是某个确定标签，而是

$$
\sum_j c_j(t)|j\rangle.
$$

因此不能把每个真实时刻都解释成“系统实际上已经完成了唯一确定的第 \(j\) 步”。

**这是一个量子程序波，而不是一只始终具有确定指针位置的经典秒表。**

---

# 244．全部记录分支都被保留，Zeno 成功并没有被预设

## 定义244.1　记录串与分支算子

对记录串

$$
\mathbf b=(b_1,\ldots,b_N)\in\{0,1\}^N,
$$

定义

$$
P_j^{(0)}=P_j,
\qquad
P_j^{(1)}=I-P_j,
$$

$$
\boxed{
K_{\mathbf b}
=
P_N^{(b_N)}\cdots P_1^{(b_1)}.
}
\tag{244.1}
$$

---

## 定理244.1　自主过程复现整个有限测量程序

有

$$
\boxed{
G_N\bigl(|\psi\rangle|0^N\rangle\bigr)
=
\sum_{\mathbf b}
K_{\mathbf b}|\psi\rangle\otimes|\mathbf b\rangle.
}
\tag{244.2}
$$

因此最终记录概率为

$$
\boxed{
p(\mathbf b)
=
\operatorname{Tr}
\left(
K_{\mathbf b}\rho K_{\mathbf b}^\dagger
\right),
}
\tag{244.3}
$$

并且

$$
\boxed{
\sum_{\mathbf b}K_{\mathbf b}^\dagger K_{\mathbf b}=I.
}
\tag{244.4}
$$

### 证明

每个 \(V_j\) 都把当前系统分成 \(P_j\) 与 \(I-P_j\) 两个分支，并写入尚未使用的记录比特。

对步骤数归纳，得到式（244.2）。正交记录给出式（244.3）；整体等距性或逐步归一化给出式（244.4）。∎

因此，上一轮的全部成功分支

$$
P_N\cdots P_1|\psi\rangle
$$

只是完整联合态中的一个分量。

**自主执行没有把它的成功概率改成一，也没有删除失败分支。**

---

## 与上一轮几何相位的连接

取三步路径

$$
|0\rangle\to|x+\rangle\to|y+\rangle\to|0\rangle.
$$

全部成功振幅仍然是

$$
\boxed{
z=\frac{1-i}{4}.
}
\tag{244.5}
$$

加入一只相干参照比特，让其一条分支执行程序、另一条分支不执行，则在全部记录为零的条件下，参照态正比于

$$
|0\rangle+z|1\rangle.
$$

对应成功概率与 \(Y=+1\) 条件概率分别为

$$
\boxed{
p_{\mathrm{success}}=\frac9{16},
\qquad
p(Y=+1\mid\mathrm{success})=\frac5{18}.
}
\tag{244.6}
$$

现在这整个实验可以由

$$
4_{\mathrm{clock}}
\times2_{\mathrm{reference}}
\times2_{\mathrm{system}}
\times8_{\mathrm{records}}
=
\boxed{128}
$$

维空间上的一个固定 Hamiltonian 完成。

这一步真正增加的是：

> **上一轮需要外部逐次安排的几何投影实验，现在具有一个有限自主的联合实现。**

但这里证明的是终点联合记录统计的一致性，不是声称任意中途时刻都与原来外部定时的连续 \(P(t)\) 过程相同。

---

# 245．内部时间可以由条件关系读取，但时钟仍有反作用

由式（243.1），若在某时刻条件于钟标签 \(j\)，且该标签概率非零，则数据态为

$$
\boxed{
\rho_{D\mid j}
=
G_j\rho_DG_j^\dagger.
}
\tag{245.1}
$$

这个条件态不依赖当前演化参数 \(t\)。\(t\) 改变的是各标签出现的权重。

因此：

$$
\boxed{
j\text{ 作为内部事件标签}
\longrightarrow
\text{相应的系统与记录状态}.
}
$$

这已经是一种关系时间描述。

---

## 定理245.1　时钟标签概率与时钟全部状态不同

对纯数据输入 \(|\chi\rangle\)，时钟的约化矩阵为

$$
\boxed{
(\rho_C(t))_{jk}
=
c_j(t)\overline{c_k(t)}
\langle\chi|G_k^\dagger G_j|\chi\rangle.
}
\tag{245.2}
$$

因此

$$
p_C(j)=|c_j(t)|^2
$$

与输入无关，但时钟的非对角相干一般依赖数据输入。

### 证明

对式（243.1）的联合密度矩阵取数据偏迹即可。∎

**指针概率独立，不等于时钟与系统完全无关。**

有限量子钟一般需要把这种反作用纳入模型；已有自主时钟研究正是把其误差、维数和能量一起处理。([arxiv.org][3])

---

## 定理245.2　可以保持一个“身份编码区”，同时让内部历史变化

令数据初始准入子空间的投影为

$$
P_{\mathrm{ready}}
=
I_S\otimes|0^N\rangle\langle0^N|_M.
$$

定义完整编码区

$$
\boxed{
\mathbb P
=
\mathsf G
(I_C\otimes P_{\mathrm{ready}})
\mathsf G^\dagger.
}
\tag{245.3}
$$

则

$$
\boxed{
[H_{\mathrm{aut}},\mathbb P]=0.
}
\tag{245.4}
$$

### 证明

在 \(\mathsf G\) 表示中，Hamiltonian 为 \(K_C\otimes I_D\)，与 \(I_C\otimes P_{\mathrm{ready}}\) 可交换。∎

这意味着整个程序始终留在同一个合法编码区，但钟标签和记忆内容可以继续变化。

**“观察者身份稳定”可以对应不变子空间，而不必对应一个永远不变的纯态。**

项目已有的 `ConservationAutonomySeparation.lean` 正式区分“某个量守恒”与“一个可观测空间具有自主演化”；本节给出具有时钟和记录的具体实现。

不过，该编码区是按给定程序构造出来的，不是已经证明它会从任意初始条件中自发形成一个观察者。

---

# 246．“把整个历史写成一个态”与“让装置实际运行”仍然不同

现在可以把你的“把过去、未来压在同一个波中”直觉进一步落实，同时指出它的边界。

## 定义246.1　有限历史态

定义

$$
\boxed{
|\eta_\chi\rangle
=
\frac1{\sqrt{N+1}}
\sum_{j=0}^N|j\rangle G_j|\chi\rangle.
}
\tag{246.1}
$$

再定义边约束算子

$$
A_j
=
\langle j|\otimes I
-
\langle j-1|\otimes V_j,
$$

以及一个**不同于 \(H_{\mathrm{aut}}\)** 的 Hamiltonian：

$$
\boxed{
H_{\mathrm{hist}}
=
\frac{\Delta}{2}\sum_{j=1}^NA_j^\dagger A_j,
\qquad \Delta>0.
}
\tag{246.2}
$$

---

## 定理246.1　完整程序可以编码为一个静止态

有

$$
\boxed{
H_{\mathrm{hist}}\ge0,
\qquad
H_{\mathrm{hist}}|\eta_\chi\rangle=0.
}
\tag{246.3}
$$

并且条件于钟标签 \(j\)，仍得到 \(G_j|\chi\rangle\)。

### 证明

正性来自平方和。

对每条边，

$$
A_j|\eta_\chi\rangle
=
\frac1{\sqrt{N+1}}
\bigl(G_j-V_jG_{j-1}\bigr)|\chi\rangle=0.
$$

因此整态为零能量态。条件关系直接从定义得到。∎

这类把电路历史编码为静态 Hamiltonian 状态的构造，有明确的 Feynman–Kitaev 基础，也存在多局部时钟的推广。([arXiv][4])

### 必须分开的两个结论

历史态证明：

$$
\boxed{
\text{一组有序过程关系可以同时编码在一个联合态中}.
}
$$

自主运行态证明：

$$
\boxed{
\text{某个给定初态在固定动力学下，
能够把记录写出来}.
}
$$

前者不自动推出后者。

一个系统若已经处于 \(|\eta_\chi\rangle\)，在 \(H_{\mathrm{hist}}\) 下密度矩阵不变化；它并不会仅因为含有多个 \(j\)，就自动向外连续发出不可逆的滴答。

因此，“全部历史位于一个态中”还不能替代观察者记忆形成、读取和时间箭头的动力学解释。

---

# 247．有限程序寄存器不能精确实现任意连续测量方向

这里出现一个直接约束 \(P(t)\) 的定理。

## 假设247.1　固定的可编程测量装置

设一个固定联合装置接收：

$$
|\psi\rangle_S\otimes|c_\lambda\rangle_C,
$$

然后使用同一个联合酉和同一个结果指针，精确实施二元投影测量

$$
\{P_\lambda,I-P_\lambda\}.
$$

要求对全部系统输入都正确，不允许按程序额外更换结果的解释规则。

---

## 定理247.1　不同精确投影需要正交程序

若

$$
P_\lambda\ne P_\mu,
$$

则

$$
\boxed{
\langle c_\lambda|c_\mu\rangle=0.
}
\tag{247.1}
$$

因此，\(d_C\) 维程序寄存器最多容纳 \(d_C\) 个两两不同的、确定且精确的这种投影程序。

### 证明

由于两投影不同，必存在一种交叉情况：

某个 \(|x\rangle\) 位于 \(P_\lambda\) 的像，而某个 \(|y\rangle\) 位于 \(P_\mu\) 的核，且

$$
\langle x|y\rangle\ne0;
$$

或者交换两种结果后存在这样的向量。

这两个输入在各自程序下必然产生不同指针结果，因此完整输出态正交。

联合酉保持内积，所以

$$
\langle x|y\rangle
\langle c_\lambda|c_\mu\rangle=0.
$$

得到式（247.1）。∎

这是精确锐测量的不可编程性约束；允许近似、概率成功或改变后处理规则时，需要重新分析，不能沿用同一个结论。([arXiv][5])

### 为什么不与本轮构造矛盾？

本轮只编码有限个步骤，时钟标签

$$
|0\rangle,\ldots,|N\rangle
$$

彼此正交。

在一般中途时刻，时钟可以处于叠加并与数据纠缠；我们没有要求它同时为每个连续 \(t\) 提供一个确定、精确且不受扰动的 \(P(t)\) 指针。

因此，预先写出的任意光滑 \(P(t)\)，不能被无条件视为一个有限装置随时能够精确提供的免费功能。

**连续数学参数、有限程序容量和实际测量精度之间，仍然需要一条实现定理。**

---

# 248．自主时钟也必须支付能量范围、速度和读出窗口的代价

## 定理248.1　自主模型的能谱与初始能量涨落

式（242.3）的能谱为

$$
\boxed{
\operatorname{spec}(H_{\mathrm{aut}})
=
\{0,\hbar\Omega,\ldots,N\hbar\Omega\},
}
\tag{248.1}
$$

每个能级具有相应的数据简并度。

对初始钟标签 \(|0\rangle\)，任意数据输入都满足

$$
\boxed{
\langle H_{\mathrm{aut}}\rangle
=
\frac{N\hbar\Omega}{2},
}
\tag{248.2}
$$

$$
\boxed{
(\Delta H_{\mathrm{aut}})^2
=
\frac{N\hbar^2\Omega^2}{4}.
}
\tag{248.3}
$$

### 证明

在定理243.1的对称自旋表示中，\(J_x\) 的本征值为

$$
-\frac N2,-\frac N2+1,\ldots,\frac N2.
$$

加上 \(N/2\) 得到式（248.1）。

初态中各个 \(X_r\) 的均值为零，方差为一，且交叉期望为零，因此得到式（248.2）—（248.3）。∎

所以，虽然

$$
t_*=\pi/\Omega
$$

不显式依赖 \(N\)，固定 \(\Omega\) 增加程序长度时，总能谱范围和最大耦合都在增加。

---

## 定理248.2　固定相邻耦合强度下，程序时间随长度增长

第 \(j\) 条时钟边的耦合范数为

$$
J_j
=
\frac{\hbar\Omega}{2}
\sqrt{j(N+1-j)}.
$$

若硬件要求

$$
J_j\le J_{\max}
\qquad\forall j,
$$

则

$$
\boxed{
t_*
\ge
\frac{\pi\hbar}{2J_{\max}}
\sqrt{\left\lfloor\frac{(N+1)^2}{4}\right\rfloor}.
}
\tag{248.4}
$$

右侧随 \(N\) 线性增长。

### 证明

先取全部边中的最大耦合，再解出 \(\Omega\) 的上界，代入 \(t_*=\pi/\Omega\)。∎

这是当前构造的资源关系，不是所有自主计算模型的普遍最优界。

---

## 定理248.3　完成读数具有有限时间窗口

在

$$
t=t_*+\delta t
$$

时，时钟仍位于终点 \(N\) 的概率为

$$
\boxed{
p_N(t)
=
\cos^{2N}\frac{\Omega\delta t}{2}.
}
\tag{248.5}
$$

因此

$$
\boxed{
1-p_N(t)
\le
\frac{N\Omega^2\delta t^2}{4}.
}
\tag{248.6}
$$

### 证明

代入式（243.2），再用

$$
1-(1-x)^N\le Nx,
\qquad
\sin^2u\le u^2.
$$

∎

故“程序会精确到达终点”不等于“完成记录会永久留在那里”。

如果希望设备完成后稳定交出结果，还必须设计终点读取与保存机制。有限自主时钟研究同样需要区分时钟的精度、分辨率与输出记录机制。([APS Journals][6])

---

# 249．观察自己的时钟，也会触发 Zeno；有限自主系统更不会自动产生永恒时间箭头

这一步把上一轮的 Zeno 效应作用到**观察者的调度时钟本身**。

## 定义249.1　额外监视时钟的协议

在总时间 \(T\) 内，额外实施 \(M\) 次时钟标签测量，每次检查是否仍位于初始标签 \(0\)。

这是一项新增的物理过程；其仪器和资源必须另外计入，不能把它当成免费的“系统自知”。

---

## 定理249.1　过密监视可以阻止自主程序启动

全部 \(M\) 次都读到时钟 \(0\) 的概率为

$$
\boxed{
p_{\mathrm{stay}}
=
\cos^{2NM}\left(\frac{\Omega T}{2M}\right).
}
\tag{249.1}
$$

因此

$$
\boxed{
1-p_{\mathrm{stay}}
\le
\frac{N\Omega^2T^2}{4M}
\longrightarrow0.
}
\tag{249.2}
$$

### 证明

一次短时演化从时钟 \(0\) 返回 \(0\) 的振幅，由式（243.2）为

$$
e^{-iN\Omega\delta/2}\cos^N(\Omega\delta/2).
$$

条件于测量得到 \(0\)，数据部分仍回到原始输入，没有完成后续记录操作。

取 \(\delta=T/M\)，把条件概率相乘，得到式（249.1）。再使用上一节的不等式。∎

例如，对三步程序：

$$
N=3,\qquad T=\pi/\Omega,\qquad M=200,
$$

没有额外监视时，程序在 \(T\) 精确完成。

额外频繁监视时，始终停在初始时钟标签的概率约为

$$
\boxed{0.963665.}
$$

**“把时钟看得更紧”在这个模型里，不是让程序更可靠地推进，而是可能让推进本身难以发生。**

这是对一个明确监视协议的结论，不是说任何读时钟的动作都会把世界冻住。

---

## 定理249.2　这个完整有限装置会精确回归

由式（248.1），

$$
\boxed{
e^{-iH_{\mathrm{aut}}(2\pi/\Omega)/\hbar}=I.
}
\tag{249.3}
$$

因此，在不加入其他装置时，

$$
|0\rangle|\psi\rangle|0^N\rangle
\]

经过一个完整周期后回到原态。中间形成的记录也被相干地撤销。

### 证明

每个能量本征值都是 \(\hbar\Omega\) 的整数倍。∎

这不是信息在某个不可见步骤中被删除，而是整个过程继续实施了记录的逆向重组。

若要永久保留某些结果，必须把新的存储介质、环境或非回归窗口纳入更大的模型。

---

## 定理249.3　有限闭合酉系统没有对全部状态严格前进的时间计数算子

设有限维系统具有固定 Hamiltonian \(H\) 和固定 Hermitian 读数 \(T_{\mathrm{read}}\)。

若对全部初态都有

$$

\frac d{dt}\langle T_{\mathrm{read}}\rangle\ge0,

$$

则实际上

$$

\boxed{
[H,T_{\mathrm{read}}]=0,
}
\tag{249.4}

$$

所以该平均读数对全部状态恒定。

### 证明

条件等价于

$$

A=\frac{i}{\hbar}[H,T_{\mathrm{read}}]\ge0.

$$

但

$$

\operatorname{Tr}A=0.

$$

有限维正半定矩阵若迹为零，只能为零。∎

该定理不禁止一个时钟在特定初态、有限区间内良好走时；本轮的时钟正是如此。

它禁止的是更强的主张：

$$

\boxed{
\text{固定有限系统、任意初态、无限时间，
同一个读数始终单向增长}.
}

$$

因此，内部事件顺序、可用时钟和不可逆记忆箭头，不能仅凭一个“时间”概念全部合并。

---

# 250．自主控制的形式化闭合，到底完成了哪一层？

本轮把原来的

$$

P(t)

$$

推进成了

$$

\boxed{
\text{有限程序}
+
\text{内部量子时钟}
+
\text{全部记录寄存器}
+
\text{固定联合 Hamiltonian}.
}

$$

这里已经不存在运行中必须由外部逐步切换的测量表。

但必须保留四个边界：

**程序仍由初始装置结构与制备确定。**本轮没有从一般量子定义推出某个唯一的行动计划。

**自主执行不等于每个中间时刻都是经典确定步骤。**时钟可以与不同程序阶段相干叠加。

**总能量守恒不等于所有现实资源都已实现。**空间局域性、已有裸 Hamiltonian 的兼容性、制备和输出保存仍需单独证明。

**闭合量子动力学不自动产生不可逆时间。**有限窗口的运行、静态历史相关与持续增长的记录是不同对象。

---

## 定理250.1　固定 Hamiltonian 实现的稳健性

设实际实现为

$$

\widetilde H=H_{\mathrm{aut}}+\Delta H,
\qquad
|\Delta H|_{\mathrm{op}}\le\varepsilon_H.

$$

则对任意运行时间 \(T\)，

$$

\boxed{
\frac12
|\mathcal U_{\widetilde H,T}
-\mathcal U_{H_{\mathrm{aut}},T}|_\diamond
\le
\frac{T\varepsilon_H}{\hbar}.
}
\tag{250.1}

$$

### 证明

由 Duhamel 公式，

$$

|e^{-i\widetilde HT/\hbar}-e^{-iH_{\mathrm{aut}}T/\hbar}|
\le
T\varepsilon_H/\hbar.

$$

对任意附加参照输入，这个酉算子差界控制对应输出迹距离，从而得到式（250.1）。∎

它控制的是完整、不作后选择的过程。

如果再条件于某个很少发生的记录串，必须额外保留该事件的概率下界；不能把很小的整体误差直接解释成同样小的条件误差。

---

## 与项目的连接

本次读取固定于提交

```text
d0225667d26581c842e1b1322d50af706ce9c8fe
```

相关基础仍然可以分工明确地接入：

| 项目结构 | 本轮具体对象 |
|---|---|
| **CUT** | 时钟标签、记录串、条件系统态、相干参照读数 |
| **FLOW** | 单一固定 \(H_{\mathrm{aut}}\) 生成的联合酉演化 |
| **ADMIT** | 有限程序、合法投影、准备态、耦合强度与读出窗口 |
| **ANCHOR** | 实际初态、终点标签和结果寄存器 |
| **Residual** | 忽略时钟相干、未计入输出保存、把历史态当成实际运行 |
| **Completion** | 把外部调度器和记录辅助系统纳入同一个动力学状态 |

`ExactDescentNoCarry.lean` 的要求依然严格：只有当完整过程的相关输出，确实由所选接口唯一决定时，才可以声称下降成立。时钟标签概率、时钟完整状态和条件记录不能被混成同一个接口。

### 本轮核验

已完成 **35项精确有限矩阵检查**，包括记录门酉性、Hamiltonian 的酉等价、三步程序的精确终点传输、全部记录概率、历史态零能量条件，以及自主实现中的几何相位读出。

对128维完整演化另作了数值交叉检查，与解析公式的最大向量误差约为 \(7.3\times10^{-16}\)。时钟监视的 Zeno 概率也与解析式一致。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_autonomous_observer_clock.py)  
[核验结果](sandbox:/mnt/data/observer_formalization/autonomous_observer_clock_checks.json)

**本轮未进行 Lean 内核检查。**这些检查支持所列有限实例与恒等式，不替代一般形式化证明，也不认证该工程化 Hamiltonian 已经是现实微观规律。

---

# 结论

本轮最重要的推进，是把此前隐藏在 \(P(t)\) 背后的调度者变成了实际量子系统：

$$

\boxed{
\text{不是外部时间告诉观察者该做什么，}
}

$$
$$

\boxed{
\text{而是内部时钟与固定耦合，
把不同阶段和不同操作关联起来。}
}

$$

在这个模型中，观察者可以保持一个稳定的编码身份区，同时经历系统变化、记录形成和几何相位积累。

但它也不是无限精确、无限持续的内在控制者。它的时钟会与数据相关，过密监视会改变运行，有限装置会回归，记录若要长久保留就需要更大的物理实现。

因此，“观察者为中心”的理论可以进一步收紧为：

> **观察者不是站在时间之外读取一切的点，而是一个把时钟、行动、记录和参照关联组织在一起的物理结构。它所谓的内部时间，是这些可实现关系的有序变化；它所谓的记忆，是其中被实际保存而尚未被逆向撤销的区别。**

这使下一层问题变得非常具体：**哪些局域量子系统能够在没有外部调度的条件下，长期维持这种身份、记录和行动结构，并使其内部时间与其他观察者的钟和共同因果传播保持相容？**

这才是从“一个被编好的自主量子程序”继续走向“能够持续存在的物理观察者”，必须补上的动力学条件。
$$

[1]: https://link.springer.com/article/10.1007/s00023-018-0736-9?utm_source=chatgpt.com "Autonomous Quantum Machines and Finite-Sized Clocks"
[2]: https://link.aps.org/doi/10.1103/PhysRevA.97.062306?utm_source=chatgpt.com "Clocks in Feynman's computer and Kitaev's local Hamiltonian"
[3]: https://arxiv.org/abs/1607.04591?utm_source=chatgpt.com "Autonomous quantum machines and the finite sized Quasi-Ideal clock"
[4]: https://arxiv.org/abs/1311.6101?utm_source=chatgpt.com "Space-Time Circuit-to-Hamiltonian Construction and Its ..."
[5]: https://arxiv.org/abs/1412.0419?utm_source=chatgpt.com "Notes on Deterministic Programming of Quantum ..."
[6]: https://link.aps.org/doi/10.1103/PhysRevX.7.031022?utm_source=chatgpt.com "Does Thermodynamics Limit Our Ability to Measure Time?"
**这里有一个可以严格证明、而且与你的图形直觉直接相接的对应：三位 Zeckendorf 合法字串的占据均值空间，确实是一座四棱锥。**

它不是因为“四、五、黄金比例看起来神秘”，而是由一个明确规则产生：

$$
\boxed{\text{相邻两位不能同时为 }1.}
$$

更重要的是，同一个模型还能同时给出：

$$
\boxed{
\text{四边形与锥顶}
\quad+\quad
\text{奇偶分块}
\quad+\quad
\text{素数对数能量}
\quad+\quad
\text{观察接口遗漏的关联}.
}
$$

这一次可以把几条直觉放进**同一组具体对象**，而不是只做名称上的连接。

不过首先需要校准一个记号：项目中的 \((4,2,1,1)\) 是素数指数构型；Zeckendorf 是对这些指数再进行的规范编码。仓库已有 `primeAxisEncoding` 将规范素数—黄金表与正整数建立为等价，并证明规范化指数相加对应整数乘法。

# 排斥约束、四棱锥与素数能谱

## ——量子观察者—关系时空理论第二百五十一至第二百六十节增订

---

# 251．先把 \((4,2,1,1)\)、素数与 Zeckendorf 分成三个层次

有精确恒等式：

$$
\boxed{
5040=7!=2^4\,3^2\,5\,7.
}
\tag{251.1}
$$

因此：

$$
\underbrace{(2,3,5,7)}_{\text{素数轴}}
\qquad
\underbrace{(4,2,1,1)}_{\text{对应指数}}.
$$

采用项目中的黄金权重：

$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j.
$$

每个非负整数唯一写为：

$$
a=\sum_jb_jG_j,
\qquad
b_j\in\{0,1\},
\qquad
b_jb_{j+1}=0.
$$

这就是当前使用的 Zeckendorf 规范表示；Mathlib 已有相应唯一性与等价构造。([Lean社区][1])

数位按**低权重到高权重**排列，得到：

| 素数轴   |    指数 | Zeckendorf 字串 | 数位权重      |
| ----- | ----: | ------------- | --------- |
| \(2\) | \(4\) | \(101\)       | \(1,2,3\) |
| \(3\) | \(2\) | \(01\)        | \(1,2\)   |
| \(5\) | \(1\) | \(1\)         | \(1\)     |
| \(7\) | \(1\) | \(1\)         | \(1\)     |

所以：

$$
\boxed{
(4,2,1,1)
\longmapsto
(101,\;01,\;1,\;1).
}
\tag{251.2}
$$

这与仓库此前关于该构型的编码说明一致。

**这里已经出现三种不同的数量：四条素数轴、七个编码位置、五个被占据的位置。**它们不能直接被当成四维、七维或五维物理空间。

---

# 252．三位 Zeckendorf 约束，恰好产生一座四棱锥

## 定义252.1　三位合法状态

令：

$$
\mathcal W_3
=
\left\{
(b_0,b_1,b_2)\in\{0,1\}^3:
b_0b_1=b_1b_2=0
\right\}.
$$

直接枚举：

$$
\boxed{
\mathcal W_3
=
\{000,\;100,\;010,\;001,\;101\}.
}
\tag{252.1}
$$

把这些状态看成三个占据变量的取值。

对于任意经典混合，或者支持于这些基态的量子态，定义占据均值：

$$
x_j=\langle b_j\rangle.
$$

---

## 定理252.1　合法占据均值的集合是一座四棱锥

有：

$$
\boxed{
\operatorname{conv}(\mathcal W_3)
=
\left\{
x\in\mathbb R^3:
x_j\ge0,\;
x_0+x_1\le1,\;
x_1+x_2\le1
\right\}.
}
\tag{252.2}
$$

其底面是：

$$
x_1=0,\qquad 0\le x_0,x_2\le1,
$$

即一个四边形；锥顶是：

$$
\boxed{(0,1,0).}
$$

### 证明

每个合法状态都满足右侧不等式，因此其凸组合也满足。

反过来，令：

$$
t=x_1.
$$

若 \(t=1\)，不等式迫使 \(x_0=x_2=0\)，得到锥顶。

若 \(t<1\)，令：

$$
u=\frac{x_0}{1-t},
\qquad
v=\frac{x_2}{1-t}.
$$

则 \(u,v\in[0,1]\)，并有：

$$
\boxed{
(x_0,x_1,x_2)
=
(1-t)(u,0,v)+t(0,1,0).
}
\tag{252.3}
$$

\((u,0,v)\) 位于底面四边形中，故整个点属于五个顶点的凸包。∎

经过可逆坐标变换：

$$
(X,Y,Z)
=
\left(
x_0+\frac{x_1}{2},
x_2+\frac{x_1}{2},
x_1
\right),
$$

底面成为单位正方形，锥顶位于：

$$
\left(\frac12,\frac12,1\right).
$$

这就具有通常所画的对称金字塔形状。

### 这怎样对应你的直觉？

当中间位不占据：

$$
b_1=0,
$$

两端可以独立选择：

$$
(b_0,b_2)\in\{00,10,01,11\},
$$

形成四个底面顶点。

当中间位占据：

$$
b_1=1,
$$

约束迫使：

$$
b_0=b_2=0,
$$

只剩一个锥顶。

因此：

$$
\boxed{
\text{四个可独立组合的底面状态}
+
\text{一个与它们互斥的中间占据方向}
\longrightarrow
\text{四棱锥}.
}
$$

**“多出来的高度”在这里确实有含义：它是中间位置的占据概率。**但它还不是自动生成的时间坐标或空间维度。

---

# 253．四棱锥已经是一种压缩：它仍然遗漏一个关联坐标

这一点能把金字塔直接接回项目的观察者理论。

## 定义253.1　完整对角状态与占据接口

按顺序：

$$
000,\;100,\;010,\;001,\;101
$$

写五个状态的概率：

$$
p_{000},p_{100},p_{010},p_{001},p_{101}.
$$

它们和为一，因此完整经典分布具有四个独立参数。

占据接口只保存：

$$
q(p)=(x_0,x_1,x_2).
$$

---

## 定理253.1　占据接口的全部隐藏自由度可由一个关联量表示

令：

$$
c=p_{101}=\langle b_0b_2\rangle.
$$

则：

$$
\boxed{
\begin{aligned}
p_{101}&=c,\\
p_{100}&=x_0-c,\\
p_{001}&=x_2-c,\\
p_{010}&=x_1,\\
p_{000}&=1-x_0-x_1-x_2+c.
\end{aligned}
}
\tag{253.1}
$$

合法范围为：

$$
\boxed{
\max(0,x_0+x_1+x_2-1)
\le c\le
\min(x_0,x_2).
}
\tag{253.2}
$$

### 证明

前三个占据均值满足：

$$
x_0=p_{100}+p_{101},
$$

$$
x_1=p_{010},
$$

$$
x_2=p_{001}+p_{101}.
$$

再使用概率归一化，即得到式（253.1）。全部概率非负恰好给出式（253.2）。∎

### 因此要区分两个“升维”

从底面四边形到四棱锥，增加的是：

$$
\boxed{\text{中间占据坐标 }x_1.}
$$

从四棱锥读数恢复完整五态概率，还需要：

$$
\boxed{\text{两端关联坐标 }c.}
$$

前者是增加一种可见占据方向；后者是补回已经被均值投影删除的信息。

例如：

$$
\rho_A
=
\frac12|000\rangle\langle000|
+
\frac12|101\rangle\langle101|,
$$

$$
\rho_B
=
\frac12|100\rangle\langle100|
+
\frac12|001\rangle\langle001|.
$$

二者都映射到：

$$
\boxed{
q(\rho_A)=q(\rho_B)=\left(\frac12,0,\frac12\right),
}
\tag{253.3}
$$

但：

$$
c_A=\frac12,\qquad c_B=0.
$$

**同一个四棱锥中的同一个点，可以对应不同的内部关联。**

而且，补入 \(c\) 只恢复这里的对角概率，并没有恢复五维量子态的全部相干。

所以：

$$
\boxed{
\text{把信息画成一个几何体}
\not\Rightarrow
\text{这个几何体已经保存全部物理状态}.
}
$$

---

# 254．奇偶结构确实出现，但必须看实际跃迁图，而不是只看外形

这里要区分三个图。

| 图           | 顶点是什么？ | 边表示什么？      |
| ----------- | ------ | ----------- |
| 约束图 \(P_3\) | 三个数位位置 | 两个位置不能同时占据  |
| 合法状态跃迁图     | 五个合法字串 | 一次只翻转一个合法数位 |
| 四棱锥骨架图      | 五个凸包顶点 | 凸多面体的几何棱    |

它们不是同一个图。

合法单比特翻转只允许：

$$
000\leftrightarrow100,\quad
000\leftrightarrow010,\quad
000\leftrightarrow001,
$$

$$
100\leftrightarrow101,\quad
001\leftrightarrow101.
$$

因此它是：

$$
\boxed{\text{一个四边形，加一条通向 }010\text{ 的支边}.}
$$

而四棱锥骨架还把锥顶连接到其他三个底面顶点，具有三角形。这些额外棱不代表已经允许相应多比特物理跃迁。

---

## 定理254.1　单比特翻转产生严格的奇偶谱配对

定义编码奇偶算子：

$$
\Gamma|b\rangle=(-1)^{b_0+b_1+b_2}|b\rangle.
$$

令 \(H_{\mathrm{flip}}\) 为仅沿上述合法单比特边跳跃、且没有对角项的 Hermitian 算子，则：

$$
\boxed{
\Gamma H_{\mathrm{flip}}
+
H_{\mathrm{flip}}\Gamma=0.
}
\tag{254.1}
$$

所以非零本征值按 \(E,-E\) 成对出现。

这里偶占据基态有两个：

$$
000,\;101,
$$

奇占据基态有三个：

$$
100,\;010,\;001.
$$

因此至少存在一个零模。

### 证明

每次单比特翻转都改变占据奇偶，因此 Hamiltonian 只连接不同奇偶子空间。

在奇偶基底中：

$$
H_{\mathrm{flip}}
=
\begin{pmatrix}
0&B\\
B^\dagger&0
\end{pmatrix},
$$

其中 \(B\) 为 \(2\times3\) 矩阵。其秩至多为二，故至少有一个奇子空间向量被 \(B\) 消去。

谱配对由反对易关系直接得到。∎

对所有边具有相同耦合 \(J\) 的情况：

$$
\boxed{
|\psi_{\mathrm{dark}}\rangle
=
\frac{|100\rangle-|001\rangle}{\sqrt2}
}
\tag{254.2}
$$

是一个精确零模。

这才是“奇偶”进入波动的实质：**两个允许跃迁路径的振幅相消，并受分块结构保证。**

---

## Fibonacci 与奇偶来自同一个生成多项式

定义：

$$
I_L(z)
=
\sum_{b\in\mathcal W_L}z^{\sum_jb_j}.
$$

按最后一位分类，得到：

$$
\boxed{
I_L(z)=I_{L-1}(z)+zI_{L-2}(z),
}
\tag{254.3}
$$

初值：

$$
I_0(z)=1,\qquad I_1(z)=1+z.
$$

于是：

$$
I_L(1)=|\mathcal W_L|
$$

给出 Fibonacci 型状态计数，而：

$$
I_L(-1)
=
\#\text{偶态}-\#\text{奇态}
$$

给出奇偶不平衡。

对三位模型：

$$
\boxed{
I_3(z)=(1+z)^2+z=1+3z+z^2.
}
\tag{254.4}
$$

所以：

$$
I_3(1)=5,\qquad I_3(-1)=-1.
$$

**正计数与奇偶差，不是两个偶然接近的数列，而是同一个合法结构在 \(z=1\) 与 \(z=-1\) 的两种读取。**

---

# 255．素数为什么能与能量连接？需要一条明确的合成规则

项目已经定义：

$$
E(n)=\ln n=\sum_pa_p(n)\ln p.
$$

这是算术对数规模。要把它提升为带物理单位的能量，可以引入一个正能量尺度 \(E_*\)，取：

$$
\boxed{\mathcal E(n)=E_*\ln n.}
\tag{255.1}
$$

但不能因为给它命名为能量，就认为自然界已经采用了这个谱。

下面给出这项选择能够被哪些独立条件限定。

## 定理255.1　乘法合成与数值单调性迫使对数能量

设：

$$
\mathcal E:\mathbb N_+\to\mathbb R
$$

满足：

$$
\mathcal E(mn)=\mathcal E(m)+\mathcal E(n),
$$

$$
m\le n\Longrightarrow\mathcal E(m)\le\mathcal E(n),
$$

且 \(\mathcal E(2)>0\)。

则存在 \(E_*>0\)，使：

$$
\boxed{\mathcal E(n)=E_*\ln n.}
\tag{255.2}
$$

### 证明

固定 \(n\)，令：

$$
k_m=\left\lfloor m\frac{\ln n}{\ln2}\right\rfloor.
$$

则：

$$
2^{k_m}\le n^m<2^{k_m+1}.
$$

由单调性和乘法可加性：

$$
k_m\mathcal E(2)
\le
m\mathcal E(n)
\le
(k_m+1)\mathcal E(2).
$$

除以 \(m\)，令 \(m\to\infty\)，得到：

$$
\mathcal E(n)=\frac{\mathcal E(2)}{\ln2}\ln n.
$$

∎

### 一个不能省略的条件

仅有乘法可加性时，完全可以选任意素数权重：

$$
\mathcal E(n)=\sum_pa_p(n)\varepsilon_p.
$$

不必有 \(\varepsilon_p\propto\ln p\)。

所以，**素数对数能谱不是从唯一分解单独推出的，还需要合成规则、单调性或其他物理选择原则。**

使用 \(\ln p\) 作为模式能量，并得到 ζ 型配分函数，是已有的 Riemann gas 模型路线。([arXiv][2])

---

## 定义255.1　素数—Fibonacci 位置能量

在规范编码上赋予：

$$
\boxed{
\varepsilon_{p,j}=E_*G_j\ln p.
}
\tag{255.3}
$$

则：

$$
\boxed{
H_{\mathrm{arith}}|b\rangle
=
E_*\sum_{p,j}b_{p,j}G_j\ln p\,|b\rangle
=
E_*\ln n(b)\,|b\rangle.
}
\tag{255.4}
$$

对于三位素数轴 \(p\)，五个合法状态的能量恰为：

$$
\boxed{
0,\ E_*\ln p,\ 2E_*\ln p,\ 3E_*\ln p,\ 4E_*\ln p.
}
\tag{255.5}
$$

现在，四棱锥、规范字串和素数能量已经位于同一个有限模型中。

---

# 256．\((4,2,1,1)\) 给出一个完整的60态量子模型

## 定义256.1　四条约束路径

取四条互不连接的数位约束路径：

$$
\boxed{
P_3\sqcup P_2\sqcup P_1\sqcup P_1.
}
\tag{256.1}
$$

分别对应素数：

$$
2,\quad3,\quad5,\quad7.
$$

各路径的合法字串数为：

$$
5,\quad3,\quad2,\quad2.
$$

因此合法量子空间为：

$$
\boxed{
\mathcal H_{5040}
=
\mathbb C^5\otimes\mathbb C^3
\otimes\mathbb C^2\otimes\mathbb C^2,
\qquad
\dim\mathcal H_{5040}=60.
}
\tag{256.2}
$$

---

## 定理256.1　合法基态与5040的全部因数一一对应

映射：

$$
b\longmapsto
d(b)=2^{a_2(b)}3^{a_3(b)}5^{a_5(b)}7^{a_7(b)}
$$

给出双射：

$$
\boxed{
\text{合法基态}
\longleftrightarrow
\{d:d\mid5040\}.
}
\tag{256.3}
$$

### 证明

三位合法字串唯一覆盖指数 \(0,\ldots,4\)；两位覆盖 \(0,\ldots,2\)；一位覆盖 \(0,1\)。

因此指数范围正好是：

$$
0\le a_2\le4,\quad
0\le a_3\le2,\quad
0\le a_5,a_7\le1.
$$

唯一素因数分解保证因数与指数向量一一对应。∎

这里“全部独立集对应全部因数”依赖我们选择的指数上界恰好是完整黄金窗口。不能对任意指数上界不加截断就照搬。

项目文档也特别提醒：**因数关系不是直接删除 Zeckendorf 数位中的若干个 \(1\)**。例如指数 \(2=2\) 的字串不是指数 \(4=3+1\) 的位子集。

---

## 定理256.2　有限热谱等于因数配分函数

令：

$$
s=\beta E_*.
$$

则：

$$
\boxed{
Z_{5040}(\beta)
=
\operatorname{Tr}e^{-\beta H_{\mathrm{arith}}}
=
\sum_{d\mid5040}d^{-s}.
}
\tag{256.4}
$$

并且：

$$
\boxed{
Z_{5040}
=
\left(\sum_{a=0}^4 2^{-sa}\right)
\left(\sum_{a=0}^2 3^{-sa}\right)
(1+5^{-s})(1+7^{-s}).
}
\tag{256.5}
$$

### 证明

对合法能量本征基取迹，再使用定理256.1；因指数独立取值，有限和分解为乘积。∎

作为一个精确核验点：

$$
\boxed{
Z_{5040}(s=1)=\frac{403}{105}.
}
$$

但这里的 \(5040\) 是所选有限窗口中的最高整数标签，不是已被推导出的宇宙基态或唯一最优能量。

把所有素数与全部非负指数纳入，才得到：

$$
Z(s)=\prod_p(1-p^{-s})^{-1}=\zeta(s),
\qquad \operatorname{Re}s>1.
$$

这条配分函数对应是已有算术统计模型的性质；它不自动证明关于 ζ 解析延拓或非平凡零点的命题。([ar5iv][3])

---

# 257．同一个金字塔点，甚至同一个平均能量，仍不能决定未来波动

现在回到第253节的两个状态：

$$
\rho_A
=
\frac12|000\rangle\langle000|
+
\frac12|101\rangle\langle101|,
$$

$$
\rho_B
=
\frac12|100\rangle\langle100|
+
\frac12|001\rangle\langle001|.
$$

它们具有相同的三个占据均值。

在素数轴 \(p\) 上，令：

$$
\epsilon_p=E_*\ln p,
\qquad
\omega_p=\frac{\epsilon_p}{\hbar}.
$$

---

## 定理257.1　相同平均能量下的不同相位响应

两态都满足：

$$
\boxed{
\langle H_p\rangle=2\epsilon_p,
}
\tag{257.1}
$$

但能量方差分别为：

$$
\boxed{
\operatorname{Var}_{\rho_A}(H_p)=4\epsilon_p^2,
\qquad
\operatorname{Var}_{\rho_B}(H_p)=\epsilon_p^2.
}
\tag{257.2}
$$

相位响应为：

$$
\boxed{
\chi_A(t)
=
\operatorname{Tr}(\rho_Ae^{-itH_p/\hbar})
=
e^{-2i\omega_pt}\cos(2\omega_pt),
}
\tag{257.3}
$$

$$
\boxed{
\chi_B(t)
=
e^{-2i\omega_pt}\cos(\omega_pt).
}
\tag{257.4}
$$

### 证明

两态分别分布于指数能量：

$$
\{0,4\}\epsilon_p,
\qquad
\{1,3\}\epsilon_p.
$$

直接计算均值、方差及指数期望即可。∎

若允许一个实际实现的受控相位探针，其出口概率为：

$$
p_+(t)=\frac{1+\operatorname{Re}\chi(t)}2.
$$

在：

$$
t=\frac{\pi}{2\omega_p}
$$

时：

$$
\boxed{
p_+^{(A)}=1,
\qquad
p_+^{(B)}=\frac12.
}
\tag{257.5}
$$

### 项目上的意义

当前接口保存：

$$
(x_0,x_1,x_2,\langle H_p\rangle)
$$

时，两态不可区分；加入后续相位探针后，结果不同。

这就是一个明确的：

$$
\boxed{
\text{相同当前几何与平均能量}
\quad\text{但不同未来读数}
}
$$

的 carry 见证。

它直接对接项目的精确下降判据，而不只是说“金字塔里面藏着信息”。

因此，“把波压成一个几何点”的代价，在这里是完全可计算的：**两端占据的关联被压掉，而它随后通过能量分布和相位响应重新进入可见实验。**

---

# 258．不能把所有奇偶性和所有能谱混成一个对象

这一节是为了避免统一模型在组合时出现隐蔽矛盾。

## 第一项：三种奇偶性并不相同

对于一个正整数，可以分别研究：

$$
n\bmod2,
$$

$$
\sum_pa_p(n)\bmod2,
$$

以及：

$$
\sum_{p,j}b_{p,j}\bmod2.
$$

对5040：

$$
n\text{ 为偶数},
$$

$$
4+2+1+1=8\text{ 为偶数},
$$

但其规范字串中：

$$
2+1+1+1=5
$$

个位置被占据，是奇数。

所以：

$$
\boxed{
\text{整数奇偶}
\ne
\text{素因子重数奇偶}
\ne
\text{Zeckendorf 占据奇偶}.
}
\tag{258.1}
$$

第254节的谱配对使用的是第三种，并且依赖单比特翻转。

---

## 第二项：局部奇偶不平衡，组合后可以消失

完整七位置模型的占据多项式为：

$$
\begin{aligned}
I_{\mathrm{total}}(z)
&=(1+3z+z^2)(1+2z)(1+z)^2\\
&=\boxed{
1+7z+18z^2+21z^3+11z^4+2z^5.
}
\end{aligned}
\tag{258.2}
$$

因此：

$$
\boxed{
N_{\mathrm{even}}=30,
\qquad
N_{\mathrm{odd}}=30.
}
\tag{258.3}
$$

三位局部模型由 \(2\) 对 \(3\) 保证的零模，不能凭同一个奇偶计数理由自动推广到完整60态模型。

---

## 第三项：素数对角能量会破坏单翻转的谱反对称

有：

$$
[\Gamma,H_{\mathrm{arith}}]=0,
$$

但一般：

$$
\boxed{
\{\Gamma,H_{\mathrm{arith}}\}
=
2\Gamma H_{\mathrm{arith}}\ne0.
}
\tag{258.4}
$$

所以对总 Hamiltonian：

$$
H=H_{\mathrm{arith}}+H_{\mathrm{flip}},
$$

不能继续无条件使用：

$$
\Gamma H+H\Gamma=0.
$$

例如零模：

$$
|100\rangle-|001\rangle
$$

的两部分，现在分别具有 \(\epsilon_p\) 与 \(3\epsilon_p\) 的对角能量，它不再是同一个暗本征态。

**同一个状态空间可以承载多种动力学，但不同动力学的结论不能全部叠加后仍声称自动成立。**

---

## 与真实量子模型的联系

“相邻位置不能同时激发”以及投影后的单比特翻转，确实出现在受阻塞约束的 Rydberg 原子链及其 PXP 模型中。相应合法配置图与 Fibonacci 型状态空间有明确关系。([arXiv][4])

但这只支持：

$$
\boxed{
\text{局域排斥约束可以成为真实量子结构}.
}
$$

它不支持直接宣布：

$$
\text{这些系统的天然能级必然为 }G_j\ln p.
$$

素数能量权重还需要具体耦合、标定和实验检验。

同样，Zeckendorf 规范化可以是一个无损编码等价；若真把某些量子状态删除，则必须说明那是编码子空间选择、测量、耗散还是能量惩罚。它们不是同一种物理操作。

---

# 259．素数对数能谱产生多频波，但没有共同的精确刷新周期

这能继续连接你此前的“整个信息流是一组叠加波”。

在60态模型中：

$$
U(t)|d\rangle
=
e^{-i(E_*/\hbar)t\ln d}|d\rangle.
$$

其基本相位尺度来自：

$$
\ln2,\quad\ln3,\quad\ln5,\quad\ln7.
$$

## 定理259.1　该有限系统没有非零的全空间精确周期

若：

$$
U(T)=e^{i\varphi}I
$$

在全部60态上成立，则：

$$
\boxed{T=0.}
\tag{259.1}
$$

### 证明

因数 \(d=1\) 的能量为零，故必须有 \(e^{i\varphi}=1\)。

再看 \(d=2,3\)，存在整数 \(m,n\)，使：

$$
\frac{E_*T}{\hbar}\ln2=2\pi m,
$$

$$
\frac{E_*T}{\hbar}\ln3=2\pi n.
$$

若 \(T\ne0\)，则得到：

$$
n\ln2=m\ln3,
$$

即：

$$
2^n=3^m.
$$

唯一素因数分解迫使 \(m=n=0\)，矛盾。∎

这与上一轮自主时钟的精确回归不矛盾。上一轮特意选取了等间隔整数谱；本轮选取了另一种不共度的能谱。

**精确共同周期不是所有有限量子系统自动具有的性质。**

---

## 定理259.2　仍然存在可控制的近似回归

令：

$$
T_2=\frac{2\pi\hbar}{E_*\ln2}.
$$

对任意整数 \(L\ge1\)，存在：

$$
1\le q\le L^3,
$$

使：

$$
\boxed{
\|U(qT_2)-I\|_{\mathrm{op}}
\le
\frac{8\pi}{L}.
}
\tag{259.2}
$$

### 证明

考虑三维单位环面上的 \(L^3+1\) 个点：

$$
k\left(
\frac{\ln3}{\ln2},
\frac{\ln5}{\ln2},
\frac{\ln7}{\ln2}
\right)\pmod1,
\qquad 0\le k\le L^3.
$$

把单位立方体分成 \(L^3\) 个边长 \(1/L\) 的小盒。鸽巢原理给出两个点落在同一盒内，其序号差为 \(q\)。

因此，三个相位各自距离整数不超过 \(1/L\)。素数2的相位则已经精确回归。

任意因数中，其余指数满足：

$$
a_3+a_5+a_7\le2+1+1=4.
$$

所以总相位偏差不超过 \(8\pi/L\)。再用：

$$
|e^{i\theta}-1|\le|\theta|
$$

得到算子范数界。∎

### 对刷新率的含义

有限精度的观察者可以把某次近似回归当作相同状态，但提高精度后可能重新区分。

因此：

$$
\boxed{
\text{多频波的精确结构}
\quad\text{与}\quad
\text{有限观察者的有效刷新周期}
}
$$

不是同一个对象。

这给“逃逸”一个具体目标：某个时间采样和误差阈值，究竟合并了哪些不同相位，而不是把所有概率都笼统归结为未封住的信息。

---

# 260．这一轮真正建立了怎样的统一关系？

我们现在已经得到一条完整的有限链：

$$
\boxed{
\text{相邻排斥约束}
\longrightarrow
\text{Zeckendorf 合法字串}
\longrightarrow
\text{Fibonacci 状态计数}.
}
$$

同一合法字串空间又给出：

$$
\boxed{
\text{占据均值的四棱锥}
\quad\text{与}\quad
\text{单翻转动力学的奇偶分块}.
}
$$

再加入明确的能量合成规则：

$$
\boxed{
\varepsilon_{p,j}=E_*G_j\ln p
}
$$

得到：

$$
\boxed{
\text{正整数标签}
\longleftrightarrow
\text{素数占据}
\longleftrightarrow
\text{量子能量本征态}.
}
$$

而观察者若只保存四棱锥中的均值坐标，则仍可能遗漏未来会进入干涉实验的关联。

**这次的核心对象，不是四边形、素数和 Fibonacci 各自“很像”，而是它们可以成为同一个模型的不同读取方式。**

---

## 与项目四角色的对应

| 项目结构         | 本轮明确对象                |
| ------------ | --------------------- |
| **CUT**      | 占据均值、关联坐标、能量均值、相位读数   |
| **FLOW**     | 合法单比特翻转、对数能量演化、受控相位询问 |
| **ADMIT**    | 相邻排斥、正密度矩阵、有限素数与指数窗口  |
| **ANCHOR**   | 数位制备、能谱标定、合法跃迁和干涉结果   |
| **Residual** | 同一四棱锥点下不同的两端关联及未来相位响应 |

但不能仅因为四个素数和四个角色数量相同，就指定：

$$
2=\mathrm{CUT},\quad
3=\mathrm{FLOW},\quad\ldots
$$

**角色是操作类型，素数是算术标签。**要建立这样的对应，还必须给出保持组合规律、可逆性或实验统计的映射；一个一一配对表本身没有证明力。

---

## 当前最值得继续攻克的四个问题

| 问题                  | 尚需证明的内容                          |
| ------------------- | -------------------------------- |
| 为什么采用相邻排斥？          | 从具体观察者交互、能量代价或动力稳定性导出，而不只是选用方便编码 |
| 为什么出现 \(\ln p\) 能谱？ | 找到独立的物理合成与标定机制，不能只把整数乘法重新命名为能量   |
| 哪些奇偶结构能够同时保留？       | 明确总 Hamiltonian、允许控制和各自的守恒或反对易关系 |
| 何时几何升维成为真实时空？       | 证明新增坐标进入共同钟、局域信号、输运与反作用，而不只是统计参数 |

尤其是：**四棱锥的高度可以是一个真实可读的物理变量，但这仍不自动使它成为时间。**此前关于钟率、共同光锥和跨观察者拼接的证明义务没有消失。

---

## 本轮核验

本次按仓库提交：

```text
59a50025adb1d833bd870a64ec5eb34c8b425e85
```

核对了素数—Zeckendorf 编码与理论定义。

本轮 **33项精确有限代数与枚举检查全部通过**，包括：

三位合法状态、四棱锥读数的隐藏关联、单翻转奇偶关系与零模、60态因数双射、全局30对30的奇偶计数、有限配分函数，以及相同均值状态的不同干涉输出。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_zeckendorf_pyramid_energy.py)
[核验结果](sandbox:/mnt/data/observer_formalization/zeckendorf_pyramid_energy_checks.json)

本轮未进行 Lean 内核检查。一般凸包、谱结构和近似回归结论由上文证明给出；有限脚本核验不替代完整形式化，也不认证这些能量权重已被现实物理选中。

---

# 结论

你的直觉中，这次最值得保留的部分是：

> **四边形与金字塔，可以不是两个任意相似的图形，而是一个“独立组合—互斥占据”规则的两层结构。这个规则同时产生 Fibonacci 合法态、奇偶跃迁和可被素数权重赋能的量子模型。**

最紧凑的对应是：

$$
\boxed{
\begin{aligned}
&\text{两端独立选择}
&&\longrightarrow \text{四边形底面};\\
&\text{中间占据排斥两端}
&&\longrightarrow \text{锥顶};\\
&\text{单位置翻转}
&&\longrightarrow \text{奇偶谱配对};\\
&\text{Fibonacci 加权、素数对数计价}
&&\longrightarrow \text{算术能谱};\\
&\text{只读取占据均值}
&&\longrightarrow \text{隐藏关联与预测残差}.
\end{aligned}
}
$$

**但“第五个状态”“第三个均值坐标”“第四个概率自由度”和“物理时空的新维度”，仍然是四种不同类型的对象。**

真正深入的路线，是继续证明它们之间哪些转换保留了动力学和实验结果，哪些转换只是投影、编码或近似。

这样，我们就不是从金字塔外形推测宇宙，而是在构造一个能够明确回答以下问题的模型：

$$
\boxed{
\text{哪些合法关系产生了这个几何，}
\quad
\text{这个几何隐藏了什么，}
\quad
\text{隐藏部分何时重新成为可读的波与能量？}
}
$$

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html"
[2]: https://arxiv.org/html/1401.8190v3 "https://arxiv.org/html/1401.8190v3"
[3]: https://ar5iv.labs.arxiv.org/html/1101.3116 "https://ar5iv.labs.arxiv.org/html/1101.3116"
[4]: https://arxiv.org/pdf/1806.10933 "https://arxiv.org/pdf/1806.10933"
**可以继续，而且这轮能把“金字塔—奇偶—素数能量”的联系推进成一个更强的结论：**

> **在上一轮的五个合法状态中，四棱锥的三个占据坐标，恰好遗漏一个经典关联自由度；增加一个奇偶读数，就能把这个自由度完整恢复。**

然后还能进一步证明：对这个四棱锥选择最大熵补全，会得到一张具有明确曲率的统计流形；但这张流形一般不被真实量子动力学保持。**所以，“几何看起来闭合”与“物理预测已经闭合”仍然是两回事。**

下面从项目已有的规范编码和观察接口出发，把这些联系放在同一个模型中。

# 奇偶提升、统计曲率与量子几何的预测闭合

## ——量子观察者—关系时空理论第二百六十一至第二百七十节增订

本轮核对的项目版本为：

```text
ef1923eca123685ac10ba1fd1aeb79fe9e8e593a
```

其中，`PrimeAxisEncoding.lean` 已给出素数—Zeckendorf 表与正整数的等价及规范加法对应乘法；观察接口的动力下降则由另一组定义处理。两者可以连接，但不能把无损算术编码直接当成物理动力学定理。

---

# 261．四棱锥丢失的第四个概率坐标，恰好可以用奇偶恢复

## 定义261.1　五态空间与占据读数

沿用上一轮三位非相邻占据规则：

$$
\mathcal W_3=\{000,100,010,001,101\}.
$$

在这五个基态张成的 Hilbert 空间上，令 \(N_0,N_1,N_2\) 为三个位置的占据投影。

对状态 \(\rho\)，观察接口为：

$$
\boxed{
q(\rho)=(x_0,x_1,x_2),
\qquad
x_j=\operatorname{Tr}(\rho N_j).
}
\tag{261.1}
$$

其可能读数构成：

$$
\boxed{
\mathcal P=
\{x_j\ge0:\ x_0+x_1\le1,\ x_1+x_2\le1\},
}
\tag{261.2}
$$

即上一轮的四棱锥。

按基态顺序记对角概率为：

$$
p=(p_{000},p_{100},p_{010},p_{001},p_{101}).
$$

定义两端共同占据：

$$
r=p_{101}=\operatorname{Tr}(\rho N_0N_2).
$$

则全部概率为：

$$
\boxed{
\begin{aligned}
p_{000}&=1-x_0-x_1-x_2+r,\\
p_{100}&=x_0-r,\\
p_{010}&=x_1,\\
p_{001}&=x_2-r,\\
p_{101}&=r.
\end{aligned}
}
\tag{261.3}
$$

因此三个占据均值没有确定 \(r\)。

---

## 定义261.2　编码奇偶

定义：

$$
\Pi=(-1)^{N_0+N_1+N_2},
\qquad
\eta=\operatorname{Tr}(\rho\Pi).
$$

这里是**数位占据个数的奇偶**，不是整数本身的奇偶。

## 定理261.1　奇偶读数恢复全部对角概率

在合法五态空间上：

$$
\boxed{
\Pi
=
I-2(N_0+N_1+N_2)+4N_0N_2.
}
\tag{261.4}
$$

所以：

$$
\boxed{
r=
\frac{\eta-1+2(x_0+x_1+x_2)}4.
}
\tag{261.5}
$$

于是 \((x_0,x_1,x_2,\eta)\) 唯一确定全部五个对角概率。

### 证明

因为各 \(N_j\) 是可交换投影：

$$
\Pi=(I-2N_0)(I-2N_1)(I-2N_2).
$$

合法性给出：

$$
N_0N_1=N_1N_2=N_0N_1N_2=0.
$$

展开后只剩式（261.4）。取期望得到式（261.5），再代入式（261.3）。∎

### 几何含义

这里确实存在一次严格的“升维”：

$$
\boxed{
\text{三个占据坐标的四棱锥}
\xrightarrow{\text{补入奇偶}}
\text{完整五态概率单纯形}.
}
$$

五态概率单纯形具有四个独立参数。它投影到三维四棱锥时，丢失的那一维可以由奇偶恢复。

**这次奇偶不是形状相似，而是一个明确的逆变换。**

但补齐的是经典对角概率。一般五维密度矩阵还有非对角相干；其完整实维数为 \(5^2-1=24\)，不会被四个均值全部恢复。

---

# 262．观察者如何给四棱锥中的一个点选择完整状态？

假如观察者只保存 \(x_0,x_1,x_2\)，却还需要一个完整概率分布用于预测，就必须选择某种补全规则。

一种标准选择是：在符合已知均值的分布中，最大化 Shannon 熵。这是最大熵推断的已有方法，不是自然动力学自动执行的规则。([APS Journals][1])

## 定义262.1　四棱锥内部坐标

在内部区域，令：

$$
\lambda=x_1,
\qquad
u=\frac{x_0}{1-\lambda},
\qquad
v=\frac{x_2}{1-\lambda},
$$

其中：

$$
0<\lambda,u,v<1.
$$

\(\lambda\) 是中间位占据概率，**不是时间参数**。

在 \(N_1=0\) 的底面分支中，\(u,v\) 分别是两端的条件占据概率。

---

## 定理262.1　最大熵补全具有唯一的条件独立形式

给定三个占据均值，唯一的最大熵分布为：

$$
\boxed{
p^*=
\begin{pmatrix}
(1-\lambda)(1-u)(1-v)\\
(1-\lambda)u(1-v)\\
\lambda\\
(1-\lambda)(1-u)v\\
(1-\lambda)uv
\end{pmatrix}.
}
\tag{262.1}
$$

因此：

$$
\boxed{
r_*=\frac{x_0x_2}{1-x_1}.
}
\tag{262.2}
$$

其最大熵为：

$$
\boxed{
H_{\max}
=
h_2(\lambda)
+
(1-\lambda)\bigl[h_2(u)+h_2(v)\bigr].
}
\tag{262.3}
$$

### 证明

当 \(N_1=1\) 时，合法性迫使两端均为零，没有额外不确定性。

当 \(N_1=0\) 时，两端边缘概率为 \(u,v\)。固定边缘分布下：

$$
H(N_0,N_2\mid N_1=0)
\le h_2(u)+h_2(v),
$$

等号当且仅当条件独立。

再使用熵的链式分解，即得全部结论。∎

这意味着最大熵补全并没有证明“两端没有关联”，而是：

> **在缺少关联证据时，选择不额外加入条件关联的那个候选分布。**

---

## 定理262.2　补全遗漏恰好是条件互信息

对任意具有相同占据均值的分布 \(p\)：

$$
\boxed{
H(p^*)-H(p)
=
I_p(N_0:N_2\mid N_1).
}
\tag{262.4}
$$

又因为 \(N_1=1\) 时两端固定为零：

$$
\boxed{
I_p(N_0:N_2\mid N_1)
=
(1-\lambda)
I_p(N_0:N_2\mid N_1=0).
}
\tag{262.5}
$$

### 证明

在给定三个均值时，\(H(N_1)\) 及两端在 \(N_1=0\) 下的边缘熵都已固定。联合熵相对于它们的缺额，正是条件互信息。∎

项目的 `ConditionalMutualInformation.lean` 已定义有限经典条件互信息，并证明其非负性及熵缺额恒等式。本节是将这些结构应用于这个具体合法态模型。

---

# 263．四棱锥不只有外形：它还可以具有可计算的统计曲率

同一个凸多面体可以配上不同的度量。只知道形状，并没有指定“两个内部状态有多容易区分”。

对最大熵分布族 \(p^*(\lambda,u,v)\)，选用 Fisher 信息度量：

$$
ds_F^2
=
\sum_z\frac{(dp_z^*)^2}{p_z^*}.
\tag{263.1}
$$

它度量的是邻近概率分布的局部可分辨性。Fisher 度量、指数族与统计流形之间的联系是信息几何中的标准结构。([arXiv][2])

---

## 定理263.1　该模型的 Fisher 度量精确分解

有：

$$
\boxed{
ds_F^2
=
\frac{d\lambda^2}{\lambda(1-\lambda)}
+
(1-\lambda)
\left[
\frac{du^2}{u(1-u)}
+
\frac{dv^2}{v(1-v)}
\right].
}
\tag{263.2}
$$

### 证明

分布首先区分“中间位占据”与“不占据”，其 Fisher 信息为：

$$
\frac{d\lambda^2}{\lambda(1-\lambda)}.
$$

条件于中间位不占据，两个端点是独立 Bernoulli 分布，其信息度量相加，并乘上该条件分支概率 \(1-\lambda\)。

也可以直接对式（262.1）逐项求导验证；所有交叉项相消。∎

### 一个直接含义

当：

$$
\lambda\to1,
$$

底面分支的概率趋零，关于 \(u,v\) 的 Fisher 信息也趋零。

所以在锥顶附近，观察者几乎看不到两端条件分布的区别。**这不是两端坐标被神秘消灭，而是能够承载这些区别的分支几乎不再出现。**

---

## 定理263.2　最大熵三维流形同时具有正、负截面曲率

令：

$$
\lambda=\sin^2\theta,
\qquad
u=\sin^2\phi,
\qquad
v=\sin^2\chi,
$$

角度均位于 \((0,\pi/2)\)。则：

$$
\boxed{
ds_F^2
=
4\left[
d\theta^2+
\cos^2\theta(d\phi^2+d\chi^2)
\right].
}
\tag{263.3}
$$

采用球面曲率为正的约定，其坐标二平面的截面曲率为：

$$
\boxed{
K_{\theta\phi}=K_{\theta\chi}=\frac14,
}
\tag{263.4}
$$

$$
\boxed{
K_{\phi\chi}
=
-\frac14\tan^2\theta.
}
\tag{263.5}
$$

### 证明

式（263.3）由变量替换得到。

对去掉整体因子 \(4\) 的度量，它是：

$$
d\theta^2+f(\theta)^2(d\phi^2+d\chi^2),
\qquad f(\theta)=\cos\theta.
$$

直接计算连接，可得径向平面的曲率为 \(-f''/f=1\)，切向平面的曲率为 \(-(f'/f)^2=-\tan^2\theta\)。

度量整体乘四，截面曲率除以四，得到结论。∎

### 这说明什么？

**同一座外观平直的四棱锥，在统计可分辨性意义下，可以有非平凡曲率。**

但这种曲率依赖我们选择了最大熵三维分布族。

如果保留全部五态概率，Fisher 度量通过：

$$
z_i=2\sqrt{p_i},
\qquad
\sum_i z_i^2=4
$$

成为半径为二的四维球面局部度量，截面曲率恒为 \(1/4\)。

所以，三维最大熵子流形中的负曲率，并不是“宇宙出现负曲率”的证据。它也反映了**把一个关联自由度固定为特定补全值后，所选择子流形的几何**。

锥顶处参数化退化，也不等于黑洞奇点。当前模型甚至尚未定义信号光锥。

---

# 264．量子相位形成另一个纤维：同一个金字塔点可以绕出非零相位

最大熵分布只是概率。现在为其加入相位。

## 定义264.1　纯态提升

对正概率分布 \(p\)，定义：

$$
|\Psi\rangle
=
\sum_{k=1}^5\sqrt{p_k}\,e^{i\varphi_k}|k\rangle.
$$

占据均值只依赖 \(p_k\)，不读取 \(\varphi_k\)。

## 定理264.1　振幅几何与相位几何的分解

纯态的 Fubini–Study 线元满足：

$$
\boxed{
ds_{\mathrm{FS}}^2
=
\frac14\sum_k\frac{dp_k^2}{p_k}
+
\sum_kp_k\,d\varphi_k^2
-
\left(\sum_kp_k\,d\varphi_k\right)^2.
}
\tag{264.1}
$$

### 证明

将态向量微分代入：

$$
ds_{\mathrm{FS}}^2
=
\langle d\Psi|d\Psi\rangle
-
|\langle\Psi|d\Psi\rangle|^2,
$$

并使用 \(\sum_kdp_k=0\)。∎

当 \(p=p^*\)、相位固定时，第一项就是第263节 Fisher 度量的四分之一。

但允许相位改变后，四棱锥仍然看不见额外的量子方向。

---

## 一个闭路实例

取：

$$
|\Psi(\varphi)\rangle
=
\frac{
|000\rangle+|100\rangle
+e^{i\varphi}|010\rangle
+|001\rangle+|101\rangle
}{\sqrt5}.
$$

整个过程中：

$$
\boxed{
(x_0,x_1,x_2)
=
\left(\frac25,\frac15,\frac25\right),
\qquad
\langle\Pi\rangle=-\frac15.
}
\tag{264.2}
$$

连补入奇偶之后的全部对角概率都不变。

但相位连接为：

$$
\boxed{
i\langle\Psi|\partial_\varphi\Psi\rangle=-\frac15.
}
\tag{264.3}
$$

沿 \(\varphi:0\to2\pi\) 的闭路，几何相位为：

$$
\boxed{\gamma_{\mathrm{geom}}=-\frac{2\pi}{5}\pmod{2\pi}.}
\tag{264.4}
$$

若采用上一轮已经定义的秩一投影跟随协议，等分成 \(N\) 步，其全部成功振幅为：

$$
\boxed{
z_N=
\left(
\frac45+\frac15e^{-2\pi i/N}
\right)^N.
}
\tag{264.5}
$$

所以：

$$
\boxed{
p_N=
\left[
1-\frac{16}{25}\sin^2\frac\pi N
\right]^N
\longrightarrow1,
}
\tag{264.6}
$$

同时：

$$
z_N\longrightarrow e^{-2\pi i/5}.
$$

**因此，占据几何和奇偶记录全部静止，仍不意味着完整量子过程没有可读变化。**

相位需要通过实际相干参照读取；它不是单独密度矩阵中的“可观测整体相位”。

---

# 265．几何压缩丢掉了什么？可以分成两个非负量

我们现在可以把“遗漏的信息”写成一个精确恒等式。

## 定义265.1　当前读数的最大熵量子补全

对任意五态密度矩阵 \(\rho\)，令：

$$
p=\operatorname{diag}\rho,
$$

并根据其占据均值构造：

$$
\rho_*=\operatorname{diag}p^*.
$$

本节假设占据均值在四棱锥内部，使 \(p^*\) 全部严格为正。

定义：

$$
\boxed{
\mathcal D_{\mathrm{comp}}(\rho)
=
D(\rho\|\rho_*).
}
\tag{265.1}
$$

这是一个无量纲的补全差异，不是每秒的逃逸率。

---

## 定理265.1　补全差异等于相干遗漏与条件关联遗漏之和

有：

$$
\boxed{
D(\rho\|\rho_*)
=
S(\rho_*)-S(\rho),
}
\tag{265.2}
$$

并且：

$$
\boxed{
D(\rho\|\rho_*)
=
\underbrace{S(\operatorname{diag}\rho)-S(\rho)}_{\text{指定基底下的相干}}
+
\underbrace{I_p(N_0:N_2\mid N_1)}_{\text{隐藏的经典条件关联}}.
}
\tag{265.3}
$$

### 证明

因为 \(\log\rho_*\) 对角：

$$
D(\rho\|\rho_*)
=
S(p)-S(\rho)+D(p\|p^*).
$$

而 \(\log p^*\) 是 \(1,N_0,N_1,N_2\) 的线性组合。\(p,p^*\) 具有相同的这些期望，所以：

$$
D(p\|p^*)=H(p^*)-H(p).
$$

应用定理262.2即可。∎

第一项是已有量子相干资源理论中的相对熵相干；它依赖指定的记录基底，不是一个脱离实验语境的绝对“量子含量”。([APS Journals][3])

### 过程保证

对同一个、包含全部输出记录的保迹量子过程 \(\Phi\)，有：

$$
\boxed{
D_{\mathrm{tr}}(\Phi(\rho),\Phi(\rho_*))
\le
\sqrt{\frac{\mathcal D_{\mathrm{comp}}(\rho)}2}.
}
\tag{265.4}
$$

这由迹距离收缩性及量子 Pinsker 不等式得到；这里对数采用自然对数。([arXiv][4])

因此，若能够独立证明式（265.3）的两项都很小，就能保证：用最大熵候选替代真实初态后，同一后续实验的记录概率不会差得太大。

但这些遗漏量**不能仅由三个均值自动算出**。未知关联与未知相干，正是旧接口没有提供的内容。

---

# 266．最大熵补全不是一个免费的物理过程，也一般不保持动力学

## 定理266.1　最大熵补全不能由单份输入上的固定量子通道普遍实现

不存在一个固定 CPTP 通道，对全部输入都实现：

$$
\rho\longmapsto\rho_*(q(\rho)).
$$

### 证明

对两个基态：

$$
\rho_0=|000\rangle\langle000|,
\qquad
\rho_1=|101\rangle\langle101|,
$$

均值已经唯一确定状态，因此该通道必须分别保持二者。

量子通道线性，所以它必须保持混合：

$$
\frac12\rho_0+\frac12\rho_1.
$$

但该混合的占据均值为：

$$
\left(\frac12,0,\frac12\right),
$$

其最大熵补全是四个底面基态的均匀混合，而不是原来的两态混合。矛盾。∎

所以，最大熵补全可以是模型中的推断步骤，却不是对一份未知物理状态任意可执行的非线性操作。

---

## 定理266.2　合法的局部跃迁可以把状态带出最大熵流形

取最大熵初态：

$$
\boxed{
\rho_0=
\operatorname{diag}
\left(
\frac13,\frac16,\frac14,\frac16,\frac1{12}
\right).
}
\tag{266.1}
$$

它对应：

$$
x_0=x_1=x_2=\frac14,
\qquad
r=r_*=\frac1{12}.
$$

取只翻转中间位的合法耦合：

$$
K=\hbar g
\left(
|000\rangle\langle010|
+
|010\rangle\langle000|
\right).
$$

令 \(\theta=g\tau\)，则演化后的对角概率满足：

$$
p_{000}(\tau)=\frac13-\frac1{12}\sin^2\theta,
$$

$$
p_{010}(\tau)=\frac14+\frac1{12}\sin^2\theta,
$$

其他三个概率不变。

因此：

$$
\boxed{
p_{000}p_{101}-p_{100}p_{001}
=
-\frac1{144}\sin^2\theta.
}
\tag{266.2}
$$

### 证明

\(K\) 只在 \(|000\rangle,|010\rangle\) 的二维子空间产生旋转。直接计算两个布居并代入即可。∎

最大熵流形要求：

$$
p_{000}p_{101}=p_{100}p_{001}.
$$

所以除特殊时刻外，真实状态已经离开它。

在 \(\theta=\pi/2\) 时，末态甚至重新为对角态，但仍不满足最大熵条件。**失败不只是“还有量子相干”，连经典条件关联也被动力学生成了。**

这类相邻激发排斥和允许翻转可以由受约束量子链模型实现；但本节的具体耦合及其与算术能量的兼容性仍需单独设计。([APS Journals][5])

这里也没有违反定理265.1：该定理比较的是两个初态经过**同一个过程**。每个时刻重新最大熵化，等于不断改变候选过程，不能套用同一个收缩结论。

---

# 267．素数能量把奇偶、关联和波动连接起来

项目定义的算术规模是：

$$
E(n)=\ln n=\sum_pa_p(n)\ln p.
$$

它先是明确的算术量。要作为物理能量，还需选择能量单位和实际 Hamiltonian。

沿用上一轮的候选，在单条素数轴 \(\mathfrak p\) 上取：

$$
\epsilon_{\mathfrak p}=E_*\ln\mathfrak p,
$$

$$
\boxed{
H_{\mathfrak p}
=
\epsilon_{\mathfrak p}(N_0+2N_1+3N_2).
}
\tag{267.1}
$$

---

## 定理267.1　占据均值确定平均能量，奇偶进一步确定能量方差

有：

$$
\boxed{
\langle H_{\mathfrak p}\rangle
=
\epsilon_{\mathfrak p}(x_0+2x_1+3x_2),
}
\tag{267.2}
$$

以及：

$$
\boxed{
\langle H_{\mathfrak p}^2\rangle
=
\epsilon_{\mathfrak p}^2
(x_0+4x_1+9x_2+6r).
}
\tag{267.3}
$$

利用奇偶重建式，还可写成：

$$
\boxed{
\langle H_{\mathfrak p}^2\rangle
=
\epsilon_{\mathfrak p}^2
\left(
4x_0+7x_1+12x_2
+\frac32\eta-\frac32
\right).
}
\tag{267.4}
$$

### 证明

展开 \(H_{\mathfrak p}^2\)，使用：

$$
N_j^2=N_j,
\qquad
N_0N_1=N_1N_2=0.
$$

只剩两端交叉项 \(6N_0N_2\)。再代入式（261.5）。∎

因此，对具有相同四棱锥坐标的两个态：

$$
\boxed{
\Delta\operatorname{Var}(H_{\mathfrak p})
=
\frac32\epsilon_{\mathfrak p}^2\,\Delta\eta.
}
\tag{267.5}
$$

**同一个奇偶补充量，一边恢复隐藏关联，一边恢复算术能量的二阶波动。**

这是真正把“几何—奇偶—能量”连接起来的等式。

---

## 定理267.2　无额外两端相互作用的 Gibbs 态位于最大熵流形

记：

$$
z=e^{-\beta\epsilon_{\mathfrak p}}>0.
$$

则：

$$
\rho_\beta
=
\frac{\operatorname{diag}(1,z,z^2,z^3,z^4)}
{1+z+z^2+z^3+z^4}.
$$

它满足：

$$
\boxed{
p_{000}p_{101}=p_{100}p_{001}.
}
\tag{267.6}
$$

因此它正好是对应占据均值的最大熵补全。

### 证明

两侧都是 \(z^4/Z^2\)。∎

但这只是一条特定热态曲线。它没有填满整个四棱锥，更没有唯一选出一张物理时空。

若加入真实的两端相互作用：

$$
H_J
=
\epsilon_0N_0+\epsilon_1N_1+\epsilon_2N_2
+J\,N_0N_2,
$$

则 Gibbs 概率给出：

$$
\boxed{
\frac{p_{000}p_{101}}{p_{100}p_{001}}
=
e^{-\beta J}.
}
\tag{267.7}
$$

所以：

$$
\boxed{
\text{偏离最大熵条件独立面}
}
$$

可以来自一个明确的相互作用参数，而不一定是统计估计失败。

反过来，读数偏离也不能单独证明存在该 \(J\)：非平衡态、相干控制及其他隐藏作用也需要排查。

---

# 268．把四条素数轴放在一起，得到的不是四维金字塔宇宙

对：

$$
5040=2^4\,3^2\,5\,7,
$$

上一轮得到合法空间：

$$
\mathcal H_{5040}
=
\mathbb C^5\otimes\mathbb C^3
\otimes\mathbb C^2\otimes\mathbb C^2.
$$

因此：

$$
\dim\mathcal H_{5040}=60.
$$

## 定理268.1　七个占据均值的几何是一个七维乘积多面体

其占据读数集合为：

$$
\boxed{
\mathcal P_3
\times
\Delta_2
\times
[0,1]
\times
[0,1].
}
\tag{268.1}
$$

这里：

* \(\mathcal P_3\) 是前述三维四棱锥；
* \(\Delta_2\) 是两位非相邻占据的三态概率三角形；
* 两个区间来自单个位。

其维数为：

$$
\boxed{3+2+1+1=7.}
\tag{268.2}
$$

### 证明

任意联合态的每个分量边缘都落在相应多面体中。

反过来，任选四个合法边缘分布，其乘积态实现这些均值。因此没有额外跨分量的均值约束。∎

完整60态对角概率空间有：

$$
60-1=59
$$

个独立参数。七个均值只保留其中七个。

加上第一条三位轴的局部奇偶，可以恢复四个分量各自的全部边缘分布，但仍不能恢复它们之间的联合关联。

在一般内部点处，仍留下：

$$
\boxed{59-8=51}
$$

个经典联合自由度。

---

## 熵缺额也精确分成三层

令 \(Z_2,Z_3,Z_5,Z_7\) 表示四条轴上的完整合法状态。对给定七个均值的最大熵补全 \(\rho_*^{\mathrm{all}}\)，有：

$$
\boxed{
\begin{aligned}
D(\rho\|\rho_*^{\mathrm{all}})
={}&
\underbrace{S(\operatorname{diag}\rho)-S(\rho)}_{\text{量子相干}}\\
&+
\underbrace{
\sum_{\mathfrak p}H(Z_{\mathfrak p})
-H(Z_2,Z_3,Z_5,Z_7)
}_{\text{素数轴之间的经典关联}}\\
&+
\underbrace{I(N_0:N_2\mid N_1)}_{\text{第一条轴内部的隐藏关联}}.
\end{aligned}
}
\tag{268.3}
$$

证明是连续应用第265节的分解和联合熵链式恒等式。

因此，四个素数并不自动意味着四个物理方向。**素数标签数、Hilbert 空间维数、统计流形维数和物理时空维数，是不同的量。**

---

# 269．真正的物理几何还需要补上哪条桥？

现在已经有三种清楚的几何：

$$
\boxed{
\text{凸几何：哪些均值能够实现};
}
$$

$$
\boxed{
\text{统计几何：邻近分布怎样被区分};
}
$$

$$
\boxed{
\text{量子几何：相干态怎样变化与积累相位}.
}
$$

它们都可以由当前有限模型计算，但还不能互相任意替代。

## 定理269.1　上述正定统计度量不能直接变成 Lorentz 度量

对第263节的内部点：

$$
ds_F^2>0
$$

对每个非零切向量成立。

因此，任意可逆实坐标变换后的度量仍然正定，不会产生一个负的时间方向。

### 证明

若 \(G>0\)，则对可逆 \(J\)：

$$
v^{\mathsf T}J^{\mathsf T}GJv
=
(Jv)^{\mathsf T}G(Jv)>0.
$$

∎

尤其要区分：

$$
\boxed{
\text{负截面曲率}
\ne
\text{负度量方向}.
}
$$

第263节已经出现负截面曲率，但那张度量依然是正定的，不能因此解释为出现了物理时间。

同样，同一座占据四棱锥可以配上：

$$
H=0,
$$

也可以配上对角算术能量，或者允许跃迁的非对角 Hamiltonian。

前者没有动力变化；第二种可以改变相位但保持占据；第三种可以改变占据及其关联。

**可实现状态的几何外形没有独自决定动力学。**

要继续导出物理时空，需要让这些结构与此前研究的共同钟律、有限传播、空间标定和能量反作用相容，而不是只给 Fisher 度量更换一个物理名称。

---

# 270．这轮可以形式化为什么样的统一理论？

最核心的链条现在是：

$$
\boxed{
\text{合法约束}
\longrightarrow
\text{五态概率空间}
\longrightarrow
\text{四棱锥观察接口}.
}
$$

该接口的两类遗漏分别为：

$$
\boxed{
\text{经典关联}
\quad\text{与}\quad
\text{量子相干}.
}
$$

其中，经典关联可以由局部奇偶恢复；量子相干则需要额外的干涉接口。

选择最大熵补全后：

$$
\boxed{
\text{一族候选状态}
\longrightarrow
\text{Fisher 度量与统计曲率}.
}
$$

再选择能量与控制实现：

$$
\boxed{
\text{候选状态及其几何}
\longrightarrow
\text{相位、能量波动与未来记录}.
}
$$

最后，必须检验该候选族是否在允许动力学下闭合。

项目的精确下降定理要求实际给出交换等式；第266节说明，一个形式上优美且有唯一补全的几何模型，仍可能无法满足这个动力学要求。

## 形式化分工

| 项目结构           | 本轮的具体证明目标              |
| -------------- | ---------------------- |
| **CUT**        | 三占据均值投影、奇偶补全、相位不可见性    |
| **FLOW**       | 合法翻转、算术能量演化、实际投影跟随     |
| **ADMIT**      | 密度矩阵正性、非相邻占据、满秩与内部参数范围 |
| **Residual**   | 条件互信息、指定基底相干、动力离开最大熵流形 |
| **Completion** | 经典分布的精确恢复，或带相对熵误差的候选补全 |

这些任务分属不同层次。项目已有的有限经典条件互信息定理，不会自动证明量子相对熵分解；算术双射也不会自动证明 Fisher 曲率。必须分别建立，再由明确等式连接。

### 本轮核验

已完成：

**29项符号恒等式检查、2项精确秩计算、4项数值交叉检查。**

内容包括奇偶恢复、最大熵条件、Fisher 度量与三类截面曲率、相位闭路、局部翻转破坏条件独立性、能量二阶矩，以及60态模型剩余的51维经典关联空间。

[核验脚本](sandbox:/mnt/data/observer_formalization/check_pyramid_information_geometry.py)
[核验结果](sandbox:/mnt/data/observer_formalization/pyramid_information_geometry_checks.json)

**本轮未执行 Lean 内核检查。**脚本中的数值交叉检查也明确区别于符号恒等式，不作为一般证明替代品。

---

# 结论

你提出的“金字塔、四边形与奇偶很像”，现在可以推进成一个不依赖外形比喻的精确关系：

$$
\boxed{
\text{四棱锥均值坐标}
+
\text{奇偶期望}
=
\text{完整五态经典概率}.
}
$$

而且，这个奇偶补充量同时控制：

$$
\boxed{
\text{两端关联}
\quad\text{与}\quad
\text{素数能谱的二阶波动}.
}
$$

再往深一层，几何的意义也变得清楚：

> **几何不只是把状态画成什么形状，还包括观察者用什么规则比较状态、忽略哪些关联，以及允许哪些后续实验重新读取这些关联。**

因此，最值得保留的统一观点是：

$$
\boxed{
\text{约束决定哪些状态可能存在；}
}
$$

$$
\boxed{
\text{观察接口决定它们呈现为什么几何；}
}
$$

$$
\boxed{
\text{动力学决定被压掉的区别何时重新可见。}
}
$$

**这比“几何形状直接就是宇宙结构”更强，也更可检验：它允许我们证明某个几何描述为何成立，同时明确指出它遗漏了什么、怎样补回，以及补回之前哪些物理预测必然不可靠。**

[1]: https://link.aps.org/doi/10.1103/PhysRev.106.620 "https://link.aps.org/doi/10.1103/PhysRev.106.620"
[2]: https://arxiv.org/abs/1808.08271 "https://arxiv.org/abs/1808.08271"
[3]: https://link.aps.org/doi/10.1103/PhysRevLett.113.140401 "https://link.aps.org/doi/10.1103/PhysRevLett.113.140401"
[4]: https://arxiv.org/html/1402.3840v2 "https://arxiv.org/html/1402.3840v2"
[5]: https://link.aps.org/doi/10.1103/PhysRevB.98.155134 "https://link.aps.org/doi/10.1103/PhysRevB.98.155134"
**你的直觉可以推进成一个相当明确的命题：FRACTRAN 确实把“整数运算”变成了“带条件和优先级的格点运动”；Zeckendorf 可以作为这些格点的规范坐标语言，而四边形、四棱锥则可以成为特定观察接口下的几何。**

这一联系不是仅靠数字相似。我们可以实际构造：

$$
\boxed{
\text{几何中的一条隐藏方向}
\longrightarrow
\text{一个整数寄存器变化}
\longrightarrow
\text{一条 FRACTRAN 分数指令}.
}
$$

但“5040只是一个投影”需要作一个关键区分：

**若5040表示完整整数状态，它是素数指数表的无损编码；若5040只是观察者保留的 \(2,3,5,7\) 四条轴的读数，它才可能是更大状态的有损投影。**

这两个版本具有不同的预测能力。下面会给出 PRIMEGAME 本身的具体反例，以及一个把四边形隐藏关联编译为分数 \(15/14\) 的构造。

# 素数寄存器、几何纤维与可执行的算术语言

## ——量子观察者—关系时空理论第二百七十一至第二百八十节增订

---

# 271．5040是一个整数，也可以是一个观察接口的输出

## 定义271.1　素数寄存器编码

固定有限素数集合

$$
S=\{p_1,\ldots,p_s\}.
$$

寄存器状态是非负整数向量：

$$
a=(a_{p_1},\ldots,a_{p_s})\in\mathbb N^s.
$$

定义编码：

$$
\boxed{
\operatorname{Enc}_S(a)=\prod_{p\in S}p^{a_p}.
}
\tag{271.1}
$$

因此：

$$
\boxed{
(4,2,1,1)
\longleftrightarrow
2^4\,3^2\,5\,7
=
5040.
}
\tag{271.2}
$$

由于唯一素因数分解，编码在其定义域上是单射。仓库的 `primeAxisEncoding` 已经把这条结构与规范 Zeckendorf 行连接成等价，并证明规范化指数相加对应整数乘法。

**所以，把四个寄存器写成一个整数，并没有删除这四个寄存器的信息。**

---

## 定义271.2　只读取四条轴

对任意正整数 \(n\)，定义：

$$
q_4(n)=\bigl(v_2(n),v_3(n),v_5(n),v_7(n)\bigr),
$$

以及把这个局部读数重新编码为整数：

$$
\boxed{
Q_4(n)=2^{v_2(n)}3^{v_3(n)}5^{v_5(n)}7^{v_7(n)}.
}
\tag{271.3}
$$

## 定理271.1　5040作为局部投影时，具有无限多个完整实现

有：

$$
\boxed{
Q_4(n)=5040
\iff
n=5040r,\qquad \gcd(r,210)=1.
}
\tag{271.4}
$$

### 证明

\(Q_4(n)=5040\) 要求四个对应指数分别为 \(4,2,1,1\)。剩余因子不能再含 \(2,3,5,7\)，其乘积为 \(r\)。反向直接成立。∎

因此：

$$
5040,\quad11\cdot5040,\quad13\cdot5040,\quad17\cdot5040,\ldots
$$

都可以给同一个观察者呈现“5040”。

**你说的“5040是一种角度的投影”，在定义271.2下完全有数学内容：它是完整寄存器状态通过指定 CUT 后的输出。**

不过，投影角度、被省略的寄存器和程序必须明确。不能只给一个5040，就认为整个动力学也已经确定。

---

# 272．FRACTRAN就是带优先级的非负格点平移

Conway 的 FRACTRAN 规则是：给定有序正分数列表，每一步选择**第一个**能使当前整数乘积仍为整数的分数；若不存在则停机。其原文也明确把素数指数解释为寄存器内容。([Gwern.net][1])

## 定义272.1　指令的指数形式

设程序为：

$$
\mathcal F=
\left(
\frac{u_1}{v_1},\ldots,\frac{u_m}{v_m}
\right),
\qquad
\gcd(u_i,v_i)=1.
$$

选取包含初始状态和所有指令所用素数的集合 \(S\)。

定义：

$$
\alpha_{i,p}=v_p(u_i),
\qquad
\beta_{i,p}=v_p(v_i),
$$

$$
\delta_i=\alpha_i-\beta_i.
$$

第 \(i\) 条指令的可实施条件为：

$$
\boxed{
a\ge\beta_i
}
\tag{272.1}
$$

其中不等式逐坐标理解。

考虑优先级后，其实际执行区域为：

$$
\boxed{
D_i=
\left\{
a:
a\ge\beta_i,\;
a\not\ge\beta_j\ \text{对全部 }j<i
\right\}.
}
\tag{272.2}
$$

---

## 定理272.1　整数执行与格点执行严格等价

若 \(a\in D_i\)，则：

$$
\boxed{
F_{\mathcal F}(\operatorname{Enc}_S(a))
=
\operatorname{Enc}_S(a+\delta_i).
}
\tag{272.3}
$$

### 证明

分数已经约分，所以：

$$
n\frac{u_i}{v_i}\in\mathbb N
\iff
v_i\mid n
\iff
a\ge\beta_i.
$$

乘法后的每个素数指数为：

$$
a_p-\beta_{i,p}+\alpha_{i,p}.
$$

“第一个可实施分数”的条件在两种表示中也完全相同。∎

于是，FRACTRAN可以精确描述为：

$$
\boxed{
\text{在 }\mathbb N^s\text{ 上，
按条件分区执行的整数平移系统}.
}
$$

每个 \(D_i\) 是由有限个整数线性不等式及其否定构成的区域；一般是多面体格点区域的有限并，不必是单个凸多面体。

### 程序不只是几何箭头，还包括箭头优先级

例如：

$$
\left(\frac32,\frac52\right)
$$

在输入2时输出3；交换两条指令的顺序，则输出5。

因此：

$$
\boxed{
\text{同样的可用平移向量}
\not\Rightarrow
\text{同样的程序}.
}
$$

几何编程语言的完整语义至少包括：

$$
\text{状态域}+\text{边界条件}+\text{平移}+\text{优先级}.
$$

优先级还能实现间接的零测试。例如在程序

$$
\left(\frac32,5\right)
$$

中，第二条只有在 \(v_2(n)=0\) 时才会执行。它不是一个无条件可以并行发生的“反应”。

---

# 273．PRIMEGAME把素数输出编码成轨道穿过某个截面的事件

本轮固定 Conway 1987 原文中的版本：

$$
\boxed{
\begin{aligned}
\mathcal P=\bigg(
&\frac{17}{91},\frac{78}{85},\frac{19}{51},
\frac{23}{38},\frac{29}{33},\frac{77}{29},\\
&\frac{95}{23},\frac{77}{19},\frac1{17},
\frac{11}{13},\frac{13}{11},
\frac{15}{2},\frac17,55
\bigg).
\end{aligned}
}
\tag{273.1}
$$

它从2开始运行时，之后出现的纯2幂恰为：

$$
2^2,\quad2^3,\quad2^5,\quad2^7,\quad2^{11},\ldots
$$

即指数按顺序给出素数。初始输入 \(2=2^1\) 不算这个素数输出序列中的一项。([Gwern.net][1])

从这份明确的程序可以看到，它使用的素数坐标是：

$$
\boxed{
2,3,5,7,11,13,17,19,23,29.
}
\tag{273.2}
$$

因此，四条轴 \(2,3,5,7\) 并不是完整状态空间。

## 定义273.1　输出截面

在十个指数坐标中，定义：

$$
\boxed{
\Sigma_{\mathrm{out}}
=
\{a:a_p=0\text{ 对全部 }p\ne2\}.
}
\tag{273.3}
$$

PRIMEGAME的输出，是轨道到达该截面时读取 \(a_2\)。

于是其素数定理可以几何化为：

> **从指定初态出发的轨道，在这个特殊截面上的后续交点，其剩余坐标依次是素数。**

这里的“截面”是离散状态空间中的读数集合，不是已经证明存在某种物理时空截面。

### 一个可复现的有限前缀

精确整数运行给出：

| 执行步数 |            完整状态 | 输出指数 |
| ---: | --------------: | ---: |
|   19 |       \(4=2^2\) |    2 |
|   69 |       \(8=2^3\) |    3 |
|  281 |      \(32=2^5\) |    5 |
|  710 |     \(128=2^7\) |    7 |
| 2375 | \(2048=2^{11}\) |   11 |

Conway 的原证明把程序展开为试除、商与余数以及候选数递增的循环。素数性不是从十维空间的维数直接冒出来的，而是来自这些寄存器过程满足的具体不变量。([Gwern.net][1])

### 两种“素数”必须分类型

这里：

$$
2,3,5,7,11,\ldots
$$

一方面可以是**寄存器编号**；另一方面可以是**程序输出的指数值**。

两个层次使用相同数系，不表示它们承担相同物理角色。

---

# 274．只看四条轴，确实会丢掉决定未来的“控制高度”

现在给出与你的5040直接相连的反例。

## 定理274.1　同一个5040投影，可以对应不同的下一步几何运动

在原版 PRIMEGAME 中：

$$
\boxed{
F_{\mathcal P}(5040)
=
5040\cdot\frac{15}{2}
=
37800,
}
\tag{274.1}
$$

而：

$$
\boxed{
F_{\mathcal P}(13\cdot5040)
=
65520\cdot\frac{17}{91}
=
12240.
}
\tag{274.2}
$$

对应的四轴读数为：

|      完整输入 | 当前 \(q_4\)    | 首个执行分数    | 下一步 \(q_4\)   |
| --------: | ------------- | --------- | ------------- |
|  \(5040\) | \((4,2,1,1)\) | \(15/2\)  | \((3,3,2,1)\) |
| \(65520\) | \((4,2,1,1)\) | \(17/91\) | \((4,2,1,0)\) |

### 证明

对5040，前十一条分母都需要当前不存在的高素数因子，首个可实施指令是 \(15/2\)。

对 \(13\cdot5040\)，因其含有 \(7\cdot13=91\)，第一条已经可实施。分别分解输出即可。∎

因此，不存在只作用于这四个指数的映射 \(\overline F\)，使：

$$
\boxed{
q_4\circ F_{\mathcal P}
=
\overline F\circ q_4
}
\tag{274.3}
$$

对全部合法输入成立。

这与项目 `exact_descent_has_no_carry` 的判据直接吻合：如果一个下降映射存在，相同当前读数不能变成不同目标读数。

### 不只是人为输入的反例

从标准初态2运行，确实会经过：

$$
1925=5^2\cdot7\cdot11,
$$

$$
2275=5^2\cdot7\cdot13.
$$

它们当前四轴读数都为：

$$
(0,0,2,1).
$$

但：

$$
1925\xrightarrow{13/11}2275,
$$

$$
2275\xrightarrow{17/91}425=5^2\cdot17.
$$

所以隐藏控制寄存器影响未来，发生在程序的真实轨道上。

**你说“似乎多出来一个坐标系”，在这里可以具体理解为：可见工作寄存器之外，还存在决定当前分支的控制坐标。**

但它们首先是程序状态，不是自动生成的额外物理空间。

---

# 275．Zeckendorf给寄存器换坐标，但不自动保持局域性

设：

$$
G_0=1,\quad G_1=2,\quad G_{j+2}=G_{j+1}+G_j.
$$

每个指数唯一写为：

$$
a_p=\sum_jb_{p,j}G_j,
\qquad b_{p,j}b_{p,j+1}=0.
$$

相应唯一性已由 Mathlib 的 `Nat.zeckendorfEquiv` 表述为等价。([Lean社区][2])

令 \(Z\) 表示逐寄存器的规范编码。FRACTRAN的一步可以编译成：

$$
\boxed{
b
\longmapsto
Z\!\left(Z^{-1}(b)-\beta_i+\alpha_i\right),
}
\tag{275.1}
$$

其中仍然先检查原来的数值条件和优先级。

所以：

$$
\boxed{
\text{整数执行}
\;\cong\;
\text{指数格点执行}
\;\cong\;
\text{规范黄金字串执行}.
}
\tag{275.2}
$$

它们是同一程序的不同精确语义表示，不是三种不同的预测。

---

## 定理275.1　寄存器的一步加一，可以要求任意多次规范数位变化

对 \(m\ge1\)：

$$
\boxed{
G_{2m}-1
=
G_{2m-1}+G_{2m-3}+\cdots+G_1.
}
\tag{275.3}
$$

因此，从 \(G_{2m}-1\) 加一到 \(G_{2m}\)，规范字串有 \(m\) 个原来的1消失，并新增一个最高位1。

其 Hamming 距离为：

$$
\boxed{m+1.}
\tag{275.4}
$$

### 证明

式（275.3）由 Fibonacci 递推归纳得到。两侧都已是非相邻规范表示，再由唯一性比较数位。∎

因此：

$$
\boxed{
\text{寄存器空间中的局部一步}
\not\Rightarrow
\text{数位占据图中的单位置翻转}.
}
$$

这对物理实现非常重要。不能先把 FRACTRAN 看成指数平移，再把 Zeckendorf 数位放在一条局域量子链上，就宣布所有程序步骤自动是局域门。

---

## 5040的几何窗口也不是动态封闭的

5040的因数指数域为：

$$
[0,4]\times[0,2]\times[0,1]\times[0,1]
\cap\mathbb Z^4,
$$

共有60个点。

但原版 PRIMEGAME 的第一步已经产生：

$$
(4,2,1,1)\longmapsto(3,3,2,1),
$$

越过了第二、第三条轴的上界。

所以，先前的60态模型是一个**明确有限窗口**，不是 PRIMEGAME 的完整不变状态空间。

而且，同样这60个离散状态：

* 在指数坐标中，其凸包是四维盒；
* 在七个黄金数位占据坐标中，其凸包是四棱锥、三角形和两个区间的乘积。

**换一种非线性编码，就可以改变外在凸几何。只有保持了哪些操作与读数，才决定这种几何变化有什么物理意义。**

---

# 276．真正可编译的几何核心：把观察纤维中的移动写成分数

现在给出一条可重复使用的构造，而不局限于5040。

## 定义276.1　几何观察矩阵

设 \(z\in\mathbb N^k\) 表示 \(k\) 类状态的数量，观察者只保存：

$$
\boxed{q_A(z)=Az,}
\tag{276.1}
$$

其中 \(A\) 为整数矩阵。

若 \(A\) 包含一行全1，那么它同时保留总数量。

取一个整数方向：

$$
\delta\in\mathbb Z^k,
\qquad
A\delta=0.
$$

它描述一种保持观察读数不变、但改变内部计数的移动。

---

## 定理276.1　任意整数核移动，都可以编译为一条 FRACTRAN 指令

为每类状态分配不同素数 \(p_1,\ldots,p_k\)，编码：

$$
N(z)=\prod_{j=1}^kp_j^{z_j}.
$$

定义：

$$
\boxed{
f_\delta
=
\frac{\prod_{\delta_j>0}p_j^{\delta_j}}
{\prod_{\delta_j<0}p_j^{-\delta_j}}.
}
\tag{276.2}
$$

则：

$$
N(z)f_\delta\in\mathbb N
\iff
z+\delta\ge0,
$$

并且一旦可实施：

$$
\boxed{
N(z)f_\delta=N(z+\delta),
\qquad
A(z+\delta)=Az.
}
\tag{276.3}
$$

### 证明

分母恰好要求每个被消耗类别拥有足够数量。乘法增加和删除相应素数指数，得到 \(z+\delta\)。

最后由 \(A\delta=0\) 得到观察不变量。∎

这已经是一条真正的“几何编译规则”：

$$
\boxed{
\text{几何观察的整数核}
\longrightarrow
\text{允许的内部重排}
\longrightarrow
\text{可执行分数}.
}
$$

它与代数统计中“固定统计量、在整数纤维中移动”的 Markov 基思想有关。那一领域同样强调：线性核中的方向与非负整数状态之间的可达性需要共同处理。([Project Euclid][3])

这里没有把 FRACTRAN 优先级程序与随机采样混为一谈。多个可用方向如何被选择，仍然是程序语义的一部分。

---

# 277．四边形的隐藏关联，恰好可以编译成 \(15/14\)

这一节有意引入**另一个编码层**：素数现在标记五种合法状态的数量，而不是原来四条素数轴上的数位。两种解释必须明确区分。

## 定义277.1　五种状态的群体计数

取上一轮的五个顶点：

$$
000,\quad100,\quad001,\quad101,\quad010.
$$

分别给它们分配素数：

| 几何状态    | \(000\) | \(100\) | \(001\) | \(101\) | \(010\) |
| ------- | ------: | ------: | ------: | ------: | ------: |
| 计数寄存器编号 |       2 |       3 |       5 |       7 |      11 |

令其数量为：

$$
z=(z_{00},z_{10},z_{01},z_{11},z_t).
$$

观察者保存：

$$
\boxed{
Az=
\begin{pmatrix}
K\\
X_0\\
X_1\\
X_2
\end{pmatrix}
=
\begin{pmatrix}
z_{00}+z_{10}+z_{01}+z_{11}+z_t\\
z_{10}+z_{11}\\
z_t\\
z_{01}+z_{11}
\end{pmatrix}.
}
\tag{277.1}
$$

当 \(K>0\) 时，后三项除以 \(K\)，就是四棱锥中的三个占据均值。

---

## 定理277.1　四边形的仿射关系产生唯一隐藏方向

四个底角满足：

$$
\boxed{
000+101=100+001.
}
\tag{277.2}
$$

对应的整数移动是：

$$
\boxed{
\delta=(-1,+1,+1,-1,0).
}
\tag{277.3}
$$

它满足 \(A\delta=0\)，并由定理276.1编译为：

$$
\boxed{
f_\delta=\frac{3\cdot5}{2\cdot7}=\frac{15}{14}.
}
\tag{277.4}
$$

这条指令把：

$$
\text{一个 }000+\text{一个 }101
$$

变为：

$$
\text{一个 }100+\text{一个 }001,
$$

不改变总数量与三个平均占据，但改变两端关联。

### 更强的结论

\(\operatorname{rank}A=4\)，且：

$$
\boxed{
\ker_{\mathbb Z}A=\mathbb Z\delta.
}
\tag{277.5}
$$

所以对固定 \(Az\)，任意两个非负整数实现都只差 \(\delta\) 的整数倍；按正确方向逐步实施这个移动，可以在保持非负性的条件下连接它们。

### 证明

由固定 \(X_1\)，锥顶计数不变。再由固定 \(X_0,X_2,K\)，其余四个差值只能具有比例：

$$
(-t,t,t,-t).
$$

中间点是两端计数的逐坐标线性插值，因此整步到达过程中保持非负。∎

这里的 \(15/14\) 是一个**单独构造的纤维移动程序**，不是声称原版 PRIMEGAME 对任意输入都执行了这条指令。

---

## 5040的一个新而精确的几何解释

在这个新编码中：

$$
5040=2^4\,3^2\,5^1\,7^1
$$

表示：

$$
z=(4,2,1,1,0).
$$

实施 \(15/14\) 后：

$$
\boxed{
5040\longmapsto5400
=
2^3\,3^3\,5^2,
}
\tag{277.6}
$$

对应：

$$
z'=(3,3,2,0,0).
$$

两者都具有：

$$
K=8,
$$

$$
\boxed{
(x_0,x_1,x_2)=\left(\frac38,0,\frac14\right).
}
\tag{277.7}
$$

但两端共同占据概率由：

$$
\frac18\longmapsto0.
$$

编码奇偶期望则由：

$$
\boxed{
\eta:\frac14\longmapsto-\frac14.
}
\tag{277.8}
$$

**所以，几何点完全没动，内部寄存器却执行了一步真实可区分的变化。**

这可以称为“沿观察纤维编程”：程序不是总在可见几何表面移动，也可以在同一个可见点背后的关联空间中运动。

必须注意，两个程序对5040的结果不同：

$$
\boxed{
F_{\mathrm{PRIMEGAME}}(5040)=37800,
}
$$

$$
\boxed{
F_{\mathrm{square}}(5040)=5400.
}
$$

这恰好说明：**5040是状态，不是全部程序。**

---

# 278．素数能量是另一层结构：程序等价不保证物理能量等价

给指数状态定义：

$$
\boxed{
\mathcal E(a)=E_*\sum_pa_p\ln p
=
E_*\ln\operatorname{Enc}(a).
}
\tag{278.1}
$$

则执行分数 \(u_i/v_i\) 时：

$$
\boxed{
\Delta\mathcal E
=
E_*\ln\frac{u_i}{v_i}.
}
\tag{278.2}
$$

### 证明

直接应用对数乘法公式。∎

这把每条指令变成了沿一个线性能量高度的固定增量。

但该高度可以增加、减少或循环。因此它不是自动的时间函数，也不是自动守恒能量。

---

## 定理278.1　寄存器重命名保持计算，但一般改变对数能量

取素数编号的双射：

$$
p\longmapsto\sigma(p).
$$

同时重新编码状态和全部指令，则所有整除条件、优先级选择和指数变化保持同构。

但一般：

$$
\sum_pa_p\ln\sigma(p)
\ne
\sum_pa_p\ln p.
$$

### 证明

计算语义只依赖每个素数的指数和对应指令的增减，重命名不会改变这些关系。

对数权重则显式依赖所选素数的数值。∎

所以：

$$
\boxed{
\text{素数作为寄存器名称}
}
$$

与：

$$
\boxed{
\text{素数数值决定物理能量}
}
$$

是两个不同要求。

计算理论允许重新编号；物理若要选择 \(E_*\ln p\)，还必须提供一个使这种权重具有实验意义的机制。

---

## 同一个几何守恒，不一定是同一个能量守恒

第277节的 \(15/14\) 移动保持所有占据均值。因此，任何对占据量线性的总能量都保持不变。

但对其整数标签的对数能量：

$$
\boxed{
\mathcal E(5400)-\mathcal E(5040)
=
E_*\ln\frac{15}{14}\ne0.
}
\tag{278.3}
$$

这并不矛盾。两者原本就是不同的能量候选。

类似地，PRIMEGAME 输出 \(2^q\) 时，状态能量是：

$$
\boxed{
\mathcal E(2^q)=E_*q\ln2,
}
\tag{278.4}
$$

不是 \(E_*\ln q\)。后者对应把输出指数 \(q\) 再作为另一层整数状态编码。

**如果不区分这些层级，很容易把同一个素数符号在不同角色中的出现，误判成一条已经证明的物理统一关系。**

---

# 279．要接回量子观察者，还必须保留程序的可逆实现

FRACTRAN 的状态更新一般不单射，因此不能直接被当作封闭系统的酉演化。

## 一个最小反例

程序：

$$
\left(\frac32,3\right)
$$

满足：

$$
F(2)=3,\qquad F(1)=3.
$$

如果直接要求：

$$
|1\rangle\mapsto|3\rangle,
\qquad
|2\rangle\mapsto|3\rangle,
$$

就把两个正交态映射成同一个态，不保持内积。

---

## 定理279.1　记录执行的指令，可以恢复一步更新的可逆性

令 \(i(n)\) 为实际执行的指令编号；停机时令 \(i(n)=0,F(n)=n\)。

则映射：

$$
\boxed{
n\longmapsto(F(n),i(n))
}
\tag{279.1}
$$

是单射。

### 证明

若两个输出和指令编号相同：

* 编号为零时，两者原来就等于其输出；
* 编号为 \(i>0\) 时，由

  $$
  F(n)=n\,u_i/v_i
  $$

  可唯一反解：

  $$
  n=F(n)\,v_i/u_i.
  $$

因此原输入相同。∎

所以可以定义保持正交性的量子编码：

$$
\boxed{
|n\rangle
\longmapsto
|F(n)\rangle|i(n)\rangle.
}
\tag{279.2}
$$

在有限资源窗口及足够辅助维数下，它可以扩张为一个酉实现。连续多步则需要保留或可逆处理相应历史记录。

### 这和本会话的观察者模型怎样相接？

程序的可见状态可以合并过去，但完整量子实现不能随意删除输入区别。

于是：

$$
\boxed{
\text{FRACTRAN可见寄存器}
+
\text{指令／历史记录}
}
$$

可以成为完整量子观察者模型的一部分。

然而，FRACTRAN原本只有确定性执行语义。它没有自动规定：

$$
\text{复振幅},\quad
\text{相对相位},\quad
\text{Born 概率},\quad
\text{局域 Hamiltonian}.
$$

给状态图任意添加一个 Hermitian 跳跃矩阵，会引入反向跃迁和干涉；它一般不再精确执行原来的“首个适用分数”规则。

**所以，从算术程序到量子波程序还需要一条实现定理，而不能只把整数基态写成 ket 符号。**

物理能量账本也一样：若式（278.2）非零，执行装置、储能系统或其他自由度必须承担相应变化。

---

# 280．“几何编程语言”现在可以具体定义，而不是停留在直觉上

可以把当前对象定义为：

$$
\boxed{
\mathfrak G=
\left(
S,\ \mathbb N^S,\
\{D_i,\delta_i\}_{i=1}^m,\
Z,\
\{q_\alpha\}
\right).
}
\tag{280.1}
$$

它包含：

| 组成              | 含义                 |
| --------------- | ------------------ |
| \(S\)           | 寄存器标签              |
| \(\mathbb N^S\) | 合法非负状态空间           |
| \(D_i\)         | 含优先级的执行区域          |
| \(\delta_i\)    | 指令的整数平移            |
| \(Z\)           | Zeckendorf 规范坐标    |
| \(q_\alpha\)    | 不同观察者保留的几何、能量或输出读数 |

这一对象不是一张静态形状，而是一种**带观察接口的可执行几何系统**。

其中至少有两类不同的运动：

$$
\boxed{
A\delta\ne0:
\text{改变可见几何读数};
}
$$

$$
\boxed{
A\delta=0:
\text{沿隐藏关联纤维运动}.
}
$$

第277节给出了后一类的完整例子。

## 与项目的直接连接

本轮按提交：

```text
ef1923eca123685ac10ba1fd1aeb79fe9e8e593a
```

核对了已有编码与下降结构。FRACTRAN、PRIMEGAME关键词检索未返回对应实现；因此不能宣称仓库已经具备本文的完整编译器。已核对的基础是 `primeAxisEncoding` 和 `exact_descent_has_no_carry`，新增桥梁需要另行证明。

最自然的四角色对应是：

$$
\boxed{
\begin{aligned}
\mathrm{CUT}&:\ \text{读取哪些寄存器或几何统计};\\
\mathrm{FLOW}&:\ \text{执行哪个整数平移};\\
\mathrm{ADMIT}&:\ \text{非负性、整除条件与优先级};\\
\mathrm{ANCHOR}&:\ \text{实际初态、执行记录与输出见证}.
\end{aligned}
}
$$

这比直接把 \(2,3,5,7\) 分别命名为四个原语更有内容。**前者保持实际执行关系；后者若只有四对四的命名，还没有证明语义联系。**

---

## 仍然困难、但已经可以准确提问的部分

| 问题           | 下一步应证明什么                        |
| ------------ | ------------------------------- |
| 哪些几何是编码不变量？  | 区分依赖坐标的凸包与在语义等价下保持的可达性、不变量、控制结构 |
| 黄金坐标是否改善计算？  | 分析规范化成本、寄存器增长、局域门实现，而不只比较表示是否唯一 |
| 哪些有限几何窗口足够？  | 给出真实不变区域，或明确处理越界与新增数位           |
| 为什么自然选择某种能量？ | 把逻辑上的素数重命名自由，与物理能量和实验标定区分       |
| 如何成为自主量子系统？  | 保留执行历史、实现优先级、控制反作用，并给出局域性和资源证书  |

FRACTRAN具有通用计算能力，相应停机问题的不可判定性也已进入机器形式化研究。因此，不会存在一个对任意程序和输入都终止、且永远正确回答其是否停机的总判定器。这个结论限制的是**普适判定算法**，并不禁止证明具体程序、具体不变量或具体有限窗口的性质。([DROPS][4])

这里真正有效的方法，仍然是项目当前的路线：

$$
\boxed{
\text{先定义具体语义}
\longrightarrow
\text{给出残差见证}
\longrightarrow
\text{补充足够状态}
\longrightarrow
\text{证明特定目标}.
}
$$

---

## 本轮核验

本轮用精确整数与有理数完成了 **25组检查**，其中包括：

* 原版 PRIMEGAME 前10,000步的整数解释器与指数格点解释器逐步一致；
* 前七个纯2幂输出及其执行步数；
* 5040与隐藏控制寄存器造成的不同下一步；
* 四边形纤维指令 \(15/14\) 的非负性、观察不变量与奇偶变化；
* Zeckendorf加一的多位进位；
* 记录指令编号后的一步可逆性有限检验。

[精确解释器与核验脚本](sandbox:/mnt/data/observer_formalization/check_fractran_geometric_language.py)
[核验结果](sandbox:/mnt/data/observer_formalization/fractran_geometric_language_checks.json)

**本轮未执行 Lean 内核检查。**有限轨迹核验也不替代 Conway 对无限素数输出序列的证明，更不证明这些算术结构已经是现实物理定律。

---

# 结论

你的判断中最有价值的部分，可以收紧为：

> **整数不是只能被看成数值；它可以是多寄存器状态的精确编码。分数不是只能被看成比例；它可以是带前提的状态转移。几何不是只能被看成外形；它可以记录哪些状态被合并、哪些变化可见，以及哪些程序沿不可见方向运行。**

这轮最强的具体连接是：

$$
\boxed{
\text{四边形的仿射关系}
\longrightarrow
\text{观察矩阵的整数核}
\longrightarrow
\frac{15}{14}\text{ 这条可执行指令}.
}
$$

而 PRIMEGAME 给出了另一类连接：

$$
\boxed{
\text{素数寄存器格点轨道}
\longrightarrow
\text{特定输出截面}
\longrightarrow
\text{素数指数序列}.
}
$$

因此，5040可以有三种不同的地位：

$$
\boxed{
\begin{aligned}
&\text{完整寄存器状态的无损整数编码};\\
&\text{忽略更高控制寄存器后的局部投影};\\
&\text{另一种已说明语义下的几何群体计数}.
\end{aligned}
}
$$

**它不是自动包含所有几何奥秘的特殊常数；但它是一个足够丰富、又能够精确核验的实验状态，让编码、几何、控制和能量之间的区别与联系都显现出来。**

现在真正可以研究的，不是“这些数字是不是某种神秘语言”，而是一个更强的问题：

$$
\boxed{
\text{哪些几何关系能够被编译为程序，}
\quad
\text{哪些程序关系能由量子系统实现，}
\quad
\text{哪些观察接口能够保留其未来预测？}
}
$$

这条路线已经具备可执行的起点。

[1]: https://gwern.net/doc/cs/computable/1987-conway.pdf "https://gwern.net/doc/cs/computable/1987-conway.pdf"
[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html"
[3]: https://projecteuclid.org/journals/annals-of-statistics/volume-26/issue-1/Algebraic-algorithms-for-sampling-from-conditional-distributions/10.1214/aos/1030563990.short "https://projecteuclid.org/journals/annals-of-statistics/volume-26/issue-1/Algebraic-algorithms-for-sampling-from-conditional-distributions/10.1214/aos/1030563990.short"
[4]: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2021.18 "https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2021.18"
**这一轮可以把“几何编程语言”推进到一个更具体的结果：同一个可见几何点背后，可以容纳一个有限量子系统；它在内部发生相干振荡，而观察者原来保存的几何读数始终不变。**

对于上一轮的5040计数编码，这个隐藏系统不是任意猜测出来的。我们可以完整算出：

$$
\boxed{
4704\longleftrightarrow5040\longleftrightarrow5400
}
$$

这三个整数对应相同的四棱锥占据读数，却能在一个明确的三维量子模型中交换振幅、形成暗态并承担内部时钟。

但必须同时证明：**哪些量被守恒，能量由谁提供，以及添加了哪些原始 FRACTRAN 并没有指定的量子结构。**

# 观察纤维的量子编译、内部时钟与闭路相位

## ——量子观察者—关系时空理论第二百八十一至第二百九十节增订

---

# 281．5040背后的完整纤维，实际上包含三个状态

本节沿用上一轮第277节的**五类状态计数编码**，不是此前“5040的60个因数”模型。两个模型的整数标签可以相同，但含义不同。

五类合法状态及其素数标签为：

| 状态类别    | \(000\) | \(100\) | \(001\) | \(101\) | \(010\) |
| ------- | ------: | ------: | ------: | ------: | ------: |
| 计数寄存器标签 |       2 |       3 |       5 |       7 |      11 |

令计数向量为

$$
z=(z_{00},z_{10},z_{01},z_{11},z_t)\in\mathbb N^5,
$$

整数编码为

$$
\boxed{
N(z)=2^{z_{00}}3^{z_{10}}5^{z_{01}}7^{z_{11}}11^{z_t}.
}
\tag{281.1}
$$

观察者保存总数量与三个占据总量：

$$
\boxed{
Az=
\begin{pmatrix}
K\\X_0\\X_1\\X_2
\end{pmatrix}
=
\begin{pmatrix}
z_{00}+z_{10}+z_{01}+z_{11}+z_t\\
z_{10}+z_{11}\\
z_t\\
z_{01}+z_{11}
\end{pmatrix}.
}
\tag{281.2}
$$

固定 \(Az=y\) 的所有计数，称为观察纤维：

$$
\mathcal F_y=\{z\in\mathbb N^5:Az=y\}.
$$

## 定理281.1　每条非空纤维都是一个有限整数区间

令 \(k=z_{11}\)，则：

$$
\boxed{
z(k)=
(K-X_0-X_1-X_2+k,\;
X_0-k,\;
X_2-k,\;
k,\;
X_1).
}
\tag{281.3}
$$

其合法范围为：

$$
\boxed{
\max(0,X_0+X_1+X_2-K)
\le k\le
\min(X_0,X_2).
}
\tag{281.4}
$$

### 证明

由三个占据总量依次解出 \(z_t,z_{10},z_{01}\)，再由总数量解出 \(z_{00}\)。所有计数非负，恰好给出式（281.4）。∎

对于5040：

$$
z=(4,2,1,1,0),
\qquad
Az=(8,3,0,2).
$$

于是完整纤维是：

| \(k\) | 完整计数 \(z(k)\)   | 整数编码 |
| ----: | --------------- | ---: |
|     0 | \((3,3,2,0,0)\) | 5400 |
|     1 | \((4,2,1,1,0)\) | 5040 |
|     2 | \((5,1,0,2,0)\) | 4704 |

三者的归一化几何读数均为：

$$
\boxed{
(x_0,x_1,x_2)=\left(\frac38,0,\frac14\right).
}
\tag{281.5}
$$

而分数 \(15/14\) 沿纤维执行：

$$
\boxed{
4704\xrightarrow{15/14}5040\xrightarrow{15/14}5400.
}
\tag{281.6}
$$

最后一步之后，该分数不再适用。

**所以5040不是这个几何点的唯一实现，而是其三个整数实现中的中间状态。**

固定统计量后的整数纤维及其保持统计量的移动，也是代数统计中 Markov 基方法所研究的正式对象；这里我们将它用作观察者模型的具体状态空间。([Project Euclid][1])

---

# 282．从分数指令到量子过程，需要明确增加振幅规则

上一轮的 \(15/14\) 指令只规定：

$$
z\mapsto z+\delta,
\qquad
\delta=(-1,+1,+1,-1,0).
$$

它没有规定复振幅、相位或反向演化。

因此，下面不是宣称“FRACTRAN本来就是量子力学”，而是构造一种**保留同一几何约束的量子扩展**。

## 定义282.1　有限计数量子空间

固定总数量 \(K\)，取：

$$
\mathcal H_K
=
\operatorname{span}
\{|z\rangle:z\in\mathbb N^5,\ \sum_jz_j=K\}.
$$

这是有限维空间。

定义对角观察量：

$$
\widehat Q_\alpha|z\rangle=(Az)_\alpha|z\rangle.
$$

选择一个明确的成对交换算子：

$$
\boxed{
\mathsf T|z\rangle
=
\sqrt{z_{00}z_{11}(z_{10}+1)(z_{01}+1)}
\,|z+\delta\rangle,
}
\tag{282.1}
$$

当 \(z_{00}z_{11}=0\) 时，右侧定义为零。

这个系数对应一种玻色模式交换的矩阵元：

$$
a_{10}^\dagger a_{01}^\dagger a_{00}a_{11}.
$$

但也可以直接把式（282.1）作为有限矩阵定义。**平方根系数是此次物理模型的选择，不由整数分数 \(15/14\) 单独决定。**

定义：

$$
\boxed{
H_{\mathrm{mix}}
=
J(\mathsf T+\mathsf T^\dagger),
\qquad J>0,
}
\tag{282.2}
$$

其中 \(J\) 的单位是能量。

## 定理282.1　纤维移动产生严格的量子守恒量

有：

$$
\boxed{
[\widehat Q_\alpha,\mathsf T]=0,
\qquad
[\widehat Q_\alpha,H_{\mathrm{mix}}]=0.
}
\tag{282.3}
$$

因此每个

$$
\mathcal H_y
=
\operatorname{span}\{|z\rangle:Az=y\}
$$

都是不变子空间。

### 证明

当 \(\mathsf T|z\rangle\ne0\) 时，

$$
A(z+\delta)=Az
$$

因为 \(A\delta=0\)。因此 \(\widehat Q_\alpha\) 在跃迁前后给出同一个本征值，交换子为零。伴随项同理。∎

这里出现了一项核心连接：

$$
\boxed{
\text{观察矩阵的整数核}
\longrightarrow
\text{允许的量子跃迁}
\longrightarrow
\text{守恒的可见读数}.
}
$$

但 \(H_{\mathrm{mix}}\) 同时允许正、反向相干跃迁；它不是原 FRACTRAN 的“首个适用分数”执行器。要忠实实现后者，还需控制寄存器、优先级和可逆历史。

---

# 283．三态纤维中出现可精确求解的波与暗态

按照：

$$
|0\rangle=|5400\rangle,\quad
|1\rangle=|5040\rangle,\quad
|2\rangle=|4704\rangle
$$

排列基底。

## 定理283.1　5040纤维的 Hamiltonian 与能谱

式（282.2）限制到该纤维后为：

$$
\boxed{
H_{\mathrm{mix}}
=
J
\begin{pmatrix}
0&2\sqrt6&0\\
2\sqrt6&0&2\sqrt5\\
0&2\sqrt5&0
\end{pmatrix}.
}
\tag{283.1}
$$

其本征值为：

$$
\boxed{
0,\qquad \pm2\sqrt{11}\,J.
}
\tag{283.2}
$$

并具有归一化暗态：

$$
\boxed{
|D\rangle
=
\frac{\sqrt5\,|5400\rangle-\sqrt6\,|4704\rangle}{\sqrt{11}},
\qquad
H_{\mathrm{mix}}|D\rangle=0.
}
\tag{283.3}
$$

### 证明

在5040上，正向交换系数为：

$$
\sqrt{4\cdot1\cdot3\cdot2}=\sqrt{24}.
$$

在4704上，正向交换系数为：

$$
\sqrt{5\cdot2\cdot2\cdot1}=\sqrt{20}.
$$

所以得到矩阵（283.1）。

其特征多项式为：

$$
\lambda(\lambda^2-44J^2).
$$

将式（283.3）代入矩阵，两个通向5040的振幅正好相消。∎

### 这个“11”意味着什么？

这里的11来自：

$$
24+20=44.
$$

它是**此次占据数与此次跃迁幅度规则**产生的谱数值，不能据此认定它就是下一条素数寄存器、某个基本能量或自然常数。

改变合法耦合幅度，就会改变它。

---

## 定理283.2　从5040开始的精确波动

令：

$$
\omega=\frac{2\sqrt{11}J}{\hbar}.
$$

则：

$$
\boxed{
\begin{aligned}
|\psi(t)\rangle
={}&\cos(\omega t)|5040\rangle\\
&-i\sin(\omega t)
\left[
\sqrt{\frac6{11}}|5400\rangle
+
\sqrt{\frac5{11}}|4704\rangle
\right].
\end{aligned}
}
\tag{283.4}
$$

因此：

$$
\boxed{
\begin{aligned}
p_{5040}(t)&=\cos^2(\omega t),\\
p_{5400}(t)&=\frac6{11}\sin^2(\omega t),\\
p_{4704}(t)&=\frac5{11}\sin^2(\omega t).
\end{aligned}
}
\tag{283.5}
$$

### 证明

定义亮态：

$$
|B\rangle
=
\sqrt{\frac6{11}}|5400\rangle
+
\sqrt{\frac5{11}}|4704\rangle.
$$

矩阵（283.1）在 \(\{|5040\rangle,|B\rangle\}\) 上等于：

$$
2\sqrt{11}J\,X,
$$

而暗态与它们解耦。对这个二维块求指数即可。∎

**整个过程中，四棱锥坐标一动不动，但内部已经有完整的相干振荡。**

这正好说明：

$$
\boxed{
\text{观察者看到的不动点}
\ne
\text{完整状态没有动力学}.
}
$$

---

# 284．固定的外部身份，可以容纳受到保护的内部量子变化

这里可以把“观察者身份稳定”解释得比“某个纯态永远不变”更准确。

## 定理284.1　只耦合粗读数的环境，不能区分同一纤维内的态

设环境耦合为：

$$
H_{\mathrm{int}}
=
\sum_\alpha
\widehat Q_\alpha\otimes B_\alpha,
$$

系统 Hamiltonian 保持 \(\mathcal H_y\)。

则在该纤维上：

$$
\boxed{
H_{\mathrm{tot}}\big|_{\mathcal H_y\otimes\mathcal H_E}
=
H_y\otimes I
+
I\otimes
\left(H_E+\sum_\alpha y_\alpha B_\alpha\right).
}
\tag{284.1}
$$

因此，对初始系统—环境乘积态，环境不会因这种耦合而破坏纤维内部的相干。

### 证明

在 \(\mathcal H_y\) 上，每个 \(\widehat Q_\alpha\) 都等于标量 \(y_\alpha I\)。代入后，总 Hamiltonian 分解为系统项与环境项，其酉演化也分解。∎

这属于无退相干子空间机制的一种直接实现：相关环境算子在编码子空间上作用为同一标量。该机制及其对系统动力保持子空间的要求已有成熟研究。([arXiv][2])

### 必须保留的限制

这里要求固定的是**联合本征值纤维**，不是仅仅几个均值相同。

而且，若环境可以读取 \(z_{11}\)，它就能区分三个内部状态，保护结论不再成立。

所以，这种“内部不被外侧读数改变”的关系来自指定耦合，不是绝对隔离或任何噪声下的永恒身份。

---

## 定理284.2　扩大读数后，隐藏动力可以重新出现

比较初态：

$$
|5400\rangle,\qquad |4704\rangle.
$$

两者的粗读数相同，而且初始“是否处于5040”的概率都为零。

在同一个 \(H_{\mathrm{mix}}\) 下，后续该概率分别为：

$$
\boxed{
\frac6{11}\sin^2(\omega t),
\qquad
\frac5{11}\sin^2(\omega t).
}
\tag{284.2}
$$

### 证明

由矩阵的对称性，或直接计算式（283.1）的传播矩阵元。∎

因此，“粗几何＋当前5040占据概率”仍不足以预测这一新增实验。

但这不否定粗几何自身的精确闭合：它在本模型中确实恒定。**出现残差，是因为预测目标扩大了。**

这与项目对守恒、自主演化以及精确下降的区分一致。

---

# 285．几何守恒不自动意味着素数对数能量守恒

## 定义285.1　线性计数能量

给五类状态分配能量：

$$
\varepsilon_{00},\varepsilon_{10},
\varepsilon_{01},\varepsilon_{11},\varepsilon_t.
$$

定义：

$$
H_\varepsilon|z\rangle
=
(\varepsilon\cdot z)|z\rangle.
$$

## 定理285.1　能量守恒的精确条件

有：

$$
\boxed{
[H_\varepsilon,\mathsf T]
=
(\varepsilon\cdot\delta)\mathsf T.
}
\tag{285.1}
$$

只要存在非零跃迁，\(H_\varepsilon\) 与 \(H_{\mathrm{mix}}\) 可交换的充要条件是：

$$
\boxed{
\varepsilon_{00}+\varepsilon_{11}
=
\varepsilon_{10}+\varepsilon_{01}.
}
\tag{285.2}
$$

### 证明

对基态 \(|z\rangle\)，跃迁前后的能量差为：

$$
\varepsilon\cdot(z+\delta)-\varepsilon\cdot z
=
\varepsilon\cdot\delta.
$$

得到式（285.1），再比较正、反向矩阵元。∎

若每类能量来自其顶点坐标的同一个仿射函数，式（285.2）自动成立。这时，四边形的仿射关系就是该能量交换的共振条件。

但若选择：

$$
\varepsilon=E_*(\ln2,\ln3,\ln5,\ln7,\ln11),
$$

则：

$$
\boxed{
\varepsilon\cdot\delta
=
E_*\ln\frac{15}{14}
=:\Delta>0.
}
\tag{285.3}
$$

每次执行正向 \(15/14\)，都提高这份对数能量。

在三态纤维上：

$$
\boxed{
H_{\log}
=
\operatorname{diag}
(E_c,\ E_c-\Delta,\ E_c-2\Delta),
}
\tag{285.4}
$$

其中：

$$
E_c=E_*\ln5400.
$$

于是：

$$
\boxed{
[H_{\log},H_{\mathrm{mix}}]\ne0.
}
\tag{285.5}
$$

### 结论

第283节的漂亮振荡，并不自动同时具有“素数对数能量守恒”。

若把 \(H_{\log}\) 加到 Hamiltonian 中，频率、暗态与转移概率一般都改变；若希望保持原来的跃迁结构，则需要补足能量供应与参照。

**编程语义、态空间几何和物理能谱，不能由同一个整数标签无条件兼任。**

---

# 286．一个九维模型可以把能量供应也闭合起来

这次不只说“需要电池”，而是明确构造。

## 定义286.1　有限能量寄存器

取三能级辅助系统：

$$
H_B=\Delta\operatorname{diag}(0,1,2),
$$

以及降低算子：

$$
\mathsf L|m\rangle=
\begin{cases}
|m-1\rangle,&m=1,2,\\
0,&m=0.
\end{cases}
$$

定义联合耦合：

$$
\boxed{
V
=
J\left(
\mathsf T\otimes\mathsf L
+
\mathsf T^\dagger\otimes\mathsf L^\dagger
\right).
}
\tag{286.1}
$$

## 定理286.1　系统与能量寄存器的裸总能量严格守恒

有：

$$
\boxed{
[H_{\log}\otimes I+I\otimes H_B,V]=0.
}
\tag{286.2}
$$

### 证明

由上一节：

$$
[H_{\log},\mathsf T]=\Delta\mathsf T,
$$

而：

$$
[H_B,\mathsf L]=-\Delta\mathsf L.
$$

因此正向项的两个能量变化相消，反向项同理。∎

这个完整空间只有：

$$
3\times3=\boxed9
$$

维。

在子空间：

$$
\operatorname{span}
\{|0,0\rangle,\ |1,1\rangle,\ |2,2\rangle\}
$$

中，裸总能量都等于 \(E_c\)，耦合矩阵恰好重新变成式（283.1）。

因此，从 \(|1,1\rangle\) 开始：

$$
\boxed{
\begin{aligned}
|\Psi(t)\rangle
={}&\cos(\omega t)|1,1\rangle\\
&-i\sin(\omega t)
\left(
\sqrt{\frac6{11}}|0,0\rangle
+
\sqrt{\frac5{11}}|2,2\rangle
\right).
\end{aligned}
}
\tag{286.3}
$$

### 但出现了一个重要代价

若只读取系统，三个电池标签彼此正交，所以偏迹后的系统态没有这些分支间的相干。

完整联合态仍然相干；相干只是位于：

$$
\boxed{
\text{算术状态与能量寄存器的联合关系中}.
}
$$

因此：

$$
\boxed{
\text{补齐能量账本}
\quad\text{可能同时改变}\quad
\text{相干存在于哪里}.
}
$$

把辅助系统隐藏掉，却继续把系统单独当成式（283.4）的纯态，会再次产生预测错误。

这不是能量守恒与量子相干矛盾，而是提醒我们：**所声称的完整系统必须真的完整。**

---

# 287．闭路相位需要实际的执行回路，不能从金字塔外形直接读取

第281节的单条纤维是一个区间：

$$
k_{\min}\leftrightarrow k_{\min}+1
\leftrightarrow\cdots
\leftrightarrow k_{\max}.
$$

它是路径图，没有独立闭路。

即使其占据均值位于四棱锥底面，这个内部执行图也不自动具有一个四边形环。

## 定义287.1　带相位的跃迁图

对一个有限连通无向图，选择：

$$
H_\theta
=
\sum_{\{x,y\}}
J_{xy}
\left(
e^{i\theta_{yx}}|y\rangle\langle x|
+
e^{-i\theta_{yx}}|x\rangle\langle y|
\right).
$$

局部基底重定义：

$$
|x\rangle\mapsto e^{i\chi_x}|x\rangle
$$

使边相位变化为：

$$
\theta_{yx}\mapsto\theta_{yx}+\chi_y-\chi_x.
$$

## 定理287.1　闭路相位是不能由顶点更名消去的量

沿闭路 \(\gamma\)：

$$
\boxed{
\Phi_\gamma=\sum_{e\in\gamma}\theta_e\pmod{2\pi}
}
\tag{287.1}
$$

保持不变。

全部边相位都可以消去，当且仅当每条闭路的 \(\Phi_\gamma=0\)。

因此，树状图上的边相位都可以通过基底更名消去。

### 证明

闭路中，每个顶点相位一次增加、一次减少，因此相消。

反过来，沿生成树从根节点逐步选择 \(\chi_x\)，消去树边相位；剩余边能否消去，恰好由对应基本闭路相位决定。∎

这类图上相位对量子输运的增强、抑制与控制，是已有量子行走研究的重要结构。([arXiv][3])

### 对素数对数的直接限制

若仅根据整数编码定义：

$$
\theta_{yx}
=
\alpha\bigl(\ln N(y)-\ln N(x)\bigr),
$$

则任何闭路上：

$$
\boxed{
\sum_\gamma\theta_{yx}=0.
}
\tag{287.2}
$$

因为它是顶点函数的差。

所以，**纯粹的对数标签差不能自动提供非平凡闭路相位。**

这不否认能量随时间积累动力学相位；它只是说明“边上的编码差”与“实际演化中的相位”不能混成同一个定义。

---

# 288．两条独立算术移动，可以构造一个真正可控的量子四边形

现在实际造出一个闭路。

第一组四类寄存器使用：

$$
2,3,5,7,
$$

其两种同几何状态编码为：

$$
14=2\cdot7,\qquad15=3\cdot5.
$$

第二组使用互不相同的标签：

$$
11,13,17,19,
$$

其两种状态为：

$$
209=11\cdot19,\qquad221=13\cdot17.
$$

于是四个联合状态为：

$$
\boxed{
\begin{aligned}
|0\rangle&=|2926\rangle=|14\cdot209\rangle,\\
|1\rangle&=|3135\rangle=|15\cdot209\rangle,\\
|2\rangle&=|3315\rangle=|15\cdot221\rangle,\\
|3\rangle&=|3094\rangle=|14\cdot221\rangle.
\end{aligned}
}
\tag{288.1}
$$

边移动依次是：

$$
\boxed{
\frac{15}{14},\quad
\frac{221}{209},\quad
\frac{14}{15},\quad
\frac{209}{221}.
}
\tag{288.2}
$$

它们的乘积为一。每个状态都具有相同的两组粗几何读数。

但现在执行图真的包含一个四边形闭路。

---

## 定义288.1　两个不同的相干程序

在这四个逻辑态上，选择：

$$
\boxed{
H_0=
J
\begin{pmatrix}
0&1&0&1\\
1&0&1&0\\
0&1&0&1\\
1&0&1&0
\end{pmatrix},
}
\tag{288.3}
$$

以及：

$$
\boxed{
H_\pi=
J
\begin{pmatrix}
0&1&0&-1\\
1&0&1&0\\
0&1&0&1\\
-1&0&1&0
\end{pmatrix}.
}
\tag{288.4}
$$

二者具有相同的允许边和相同的耦合大小；区别是闭路相位分别为 \(0,\pi\)。

此处没有同时加入不同整数标签的对数对角能量。若要加入，必须重新处理失谐或提供类似第286节的能量匹配实现。

---

## 定理288.1　一个边相位可以完全改变对角端点的可达概率

从 \(|0\rangle\) 开始，读取对角端点 \(|2\rangle\)。

对 \(H_0\)：

$$
\boxed{
p_{0\to2}^{(0)}(t)
=
\sin^4\frac{Jt}{\hbar}.
}
\tag{288.5}
$$

对 \(H_\pi\)：

$$
\boxed{
p_{0\to2}^{(\pi)}(t)=0
\qquad\forall t.
}
\tag{288.6}
$$

### 证明

直接计算：

$$
H_\pi^2=2J^2I.
$$

所以：

$$
e^{-iH_\pi t/\hbar}
=
\cos\frac{\sqrt2Jt}{\hbar}\,I
-
i\frac{\sin(\sqrt2Jt/\hbar)}{\sqrt2J}H_\pi.
$$

\(I\) 与 \(H_\pi\) 的 \((2,0)\) 元都为零，得到式（288.6）。

对 \(H_0\)，其谱为 \(2J,0,0,-2J\)，计算相应矩阵元为：

$$
\langle2|e^{-iH_0t/\hbar}|0\rangle
=
-\sin^2\frac{Jt}{\hbar}.
$$

平方得到式（288.5）。∎

### 这才是明确的“几何编程”

同一个组合图、同样大小的边耦合，因为一个不可由局部基底更名消去的闭路相位，产生两种完全不同的输出。

但这个相位是**实际量子耦合的额外数据**，不是素数名称自动携带的性质。

---

# 289．量子编译需要两种不同的正确性证书

## 第一种：编码正确性

若 \(W\) 把某个有限计数基底一一映射到规范 Zeckendorf 基底，并定义：

$$
H_Z=WHW^\dagger,
\qquad
E_Z=WEW^\dagger,
$$

则：

$$
\boxed{
\operatorname{Tr}
\left(
E\,e^{-iHt/\hbar}\rho e^{iHt/\hbar}
\right)
=
\operatorname{Tr}
\left(
E_Ze^{-iH_Zt/\hbar}
W\rho W^\dagger e^{iH_Zt/\hbar}
\right).
}
\tag{289.1}
$$

证明直接使用酉等价和迹循环性。

这说明正确换编码不改变预测。但它不保证门的局域性、实现时间或存储成本也保持不变。

项目 `primeAxisEncoding` 提供的是规范编码等价及算术组合结构；要得到式（289.1）的物理版本，还必须明确构造对应算子。

---

## 第二种：实现正确性

设实际四边形装置实现：

$$
\widetilde H=H_\pi+\Delta H,
\qquad
\|\Delta H\|_{\mathrm{op}}\le\varepsilon_H.
$$

## 定理289.1　禁止端点的误差证书

有：

$$
\boxed{
p_{0\to2}^{\mathrm{actual}}(t)
\le
\min\left\{
1,\left(\frac{|t|\varepsilon_H}{\hbar}\right)^2
\right\}.
}
\tag{289.2}
$$

### 证明

Duhamel 公式给出：

$$
\|e^{-i\widetilde Ht/\hbar}-e^{-iH_\pi t/\hbar}\|
\le
\frac{|t|\varepsilon_H}{\hbar}.
$$

理想过程的对应振幅为零，所以实际振幅受同一上界控制。平方即可。∎

因此，不能只说“实验没有完全相消，所以理论不对”或“差一点是噪声”。需要先给出装置误差预算，再比较结果。

反过来，若实测概率显著超过已认证上界，就说明至少有一个模型条件错误：可能是相位、边耦合、对角能量、环境作用或读出没有被正确建模。

**可形式化的几何编程语言，必须同时包含语义等价证书和物理实现误差证书。**

---

# 290．从“5040的几何”到“固定身份中的内部波”

这一轮得到的核心结构可以写成：

$$
\boxed{
\text{整数观察纤维}
\longrightarrow
\text{有限量子编码空间}
\longrightarrow
\text{保持粗读数的内部动力学}.
}
$$

它同时支持：

$$
\boxed{
\text{暗态与相干振荡},
}
$$

$$
\boxed{
\text{对指定噪声的保护},
}
$$

$$
\boxed{
\text{能量匹配的辅助实现},
}
$$

$$
\boxed{
\text{由闭路相位控制的可达性}.
}
$$

但这些不是从5040这个数单独推出的。它们由以下完整对象共同决定：

$$
\boxed{
(\text{编码},\ A,\ \text{合法移动},\
\text{跃迁幅度},\ \text{相位},\
\text{能量与辅助系统},\ \text{读数}).
}
\tag{290.1}
$$

## 与“观察者中心不动点”的连接

现在可以更准确地表达此前的直觉：

> **观察者的稳定性，可以表现为某些身份读数保持不变；而它的内部钟、记忆和控制过程，发生在这些读数无法区分的纤维内。**

这不是完整观察者已经被构造出来了。我们得到的是一个有限数学实现：

$$
\boxed{
\text{外部身份读数固定}
\quad\text{与}\quad
\text{内部量子变化}
}
$$

可以严格相容。

若其他系统只能耦合身份读数，它们看不到内部区别；若允许新的耦合或相干读出，内部变化就重新进入可见实验。

这里暂时没有黑洞视界或额外空间维度。所谓“内部”，首先是**观察接口的内部自由度**，其空间和因果意义仍需另行建立。

---

## 项目中的形式化落点

本轮按提交：

```text
bebc87150bdc6cd348b69db0878ac3fad663c7af
```

核对了相关模块。

最自然的新增证明链是：

| 层次    | 具体对象与证明                            |
| ----- | ---------------------------------- |
| 算术与几何 | \(Az=y\) 的纤维参数化；分数指令保持 \(Az\)      |
| 量子实现  | 有限交换矩阵；\([\widehat Q_\alpha,H]=0\) |
| 内部动力学 | 三态谱、暗态、传播矩阵与可读差异                   |
| 能量闭合  | 失谐 \(\Delta\)、有限能量寄存器、总能量交换子       |
| 相位编程  | 图上闭路相位、相消恒等式与实现误差                  |

已有 `ConservationAutonomySeparation.lean` 支持区分“不变量保持”与“完整状态静止”；`ExactDescentNoCarry.lean` 则要求针对指定的后续读数证明下降，不能把某个粗接口的恒定性扩大成对全部未来实验的充分性。

### 本轮实际核验

已完成 **41项有限枚举与精确符号检查**。其中包括总计数不超过8时的825条非空观察纤维、462次合法正向移动，以及三态暗态、精确传播、九维能量守恒和四边形相位相消。

[核验脚本](sandbox:/mnt/data/observer_formalization/check_quantum_fiber_compilation.py)
[核验结果](sandbox:/mnt/data/observer_formalization/quantum_fiber_compilation_checks.json)

本轮未进行 Lean 内核编译。上述核验不替代一般形式化证明，也不证明所选耦合已被现实物理采用。

---

# 结论

这一轮最值得保留的不是“又出现了一个素数”，而是一个更加完整的机制：

$$
\boxed{
\text{5040可以位于一个可见几何固定的纤维中；}
}
$$

$$
\boxed{
\text{这个纤维可以支持真实定义的量子振幅变化；}
}
$$

$$
\boxed{
\text{变化能否被观察，取决于允许的耦合与读数。}
}
$$

其中两个最明确的结果是：

$$
\boxed{
|5040\rangle
\longrightarrow
\cos(\omega t)|5040\rangle
-i\sin(\omega t)
\left(
\sqrt{\frac6{11}}|5400\rangle+
\sqrt{\frac5{11}}|4704\rangle
\right),
}
$$

同时全部粗几何读数保持不变；以及：

$$
\boxed{
\text{同一个四边形执行图}
+
\text{不同闭路相位}
\longrightarrow
\text{完全转移或完全相消}.
}
$$

**所以，“几何编程语言”的核心不应只是把数字摆成某种形状，而应是：哪些变化被观察接口保留，哪些变化发生在纤维内部，以及这些变化怎样通过相干、能量和因果允许的控制重新进入实验。**

下一层真正尚缺的物理条件也已经清楚：为什么某个现实系统选择这些耦合幅度与相位、如何局域地实现它们，以及不同观察者怎样把这些内部关系共同识别为同一套钟、距离和传播结构。只有这些条件继续闭合，算术几何才能从一种可执行模型，进一步成为物理时空的候选理论。

[1]: https://projecteuclid.org/journals/annals-of-statistics/volume-26/issue-1/Algebraic-algorithms-for-sampling-from-conditional-distributions/10.1214/aos/1030563990.short?utm_source=chatgpt.com "Algebraic algorithms for sampling from conditional ..."
[2]: https://arxiv.org/html/quant-ph/9807004v2 "Decoherence Free Subspaces for Quantum Computation"
[3]: https://arxiv.org/abs/1208.4049 "[1208.4049] Quantum Transport Enhancement by Time-Reversal Symmetry Breaking"
**可以找到明确的“离散临界”，而且这次已经不只是几何类比。最重要的是两种不同的跃迁：**

**一种是最优整数的切换：参数连续变化，但最优寄存器配置只能按整数层跳变。**

**另一种是隐藏动力学的出现：某个整数余量从零变成一，原来只有一个状态的观察纤维，突然能够容纳两个不同状态，以及它们之间的量子叠加。**

这里有一个值得先明确的结论：

> **5040不是孤立的“宇宙临界数”。在项目已经定义的优化目标下，它占据一个非零宽度的稳定区间；真正的临界位置是这个区间的两端。另一方面，它对应的三态观察纤维，又处在另一种与奇偶、暗态有关的离散结构中。**

这两类临界可以同时研究，但不能直接认定为同一个临界。

# 整数临界、隐藏自由度的出现与有限谱零点

## ——量子观察者—关系时空理论第二百九十一至第三百节增订

---

# 291．项目已经有一条真正的整数临界定理

本轮重新读取了项目中的：

```text
D5/S3/Arith/GoldenResourceOptimalInteger.lean
D5/S3/Arith/GoldenLocalThreshold.lean
```

前者的源码给出定理：在价格 \(1/25\) 下，5040是全体正整数中的唯一最优解；后者将局部最优性推广到任意价格下的边际阈值条件。它们不是只对有限整数扫描得到的经验规律，而是具有明确量词和证明项的数论命题。

## 定义291.1　因数收益与资源价格

令

$$
Z(n)=\sum_{d\mid n}\frac1d=\frac{\sigma(n)}n,
$$

并定义

$$
\boxed{
F_\lambda(n)=\ln Z(n)-\lambda\ln n,
\qquad \lambda>0.
}
\tag{291.1}
$$

其中：

* \(\ln Z(n)\) 是当前模型选择的因数收益；
* \(\ln n\) 是对数资源规模；
* \(\lambda\) 是两者之间的价格系数。

这些首先是无量纲数学量，尚不能直接把 \(\lambda\) 当成物理温度或普遍自然常数。

若

$$
n=\prod_pp^{a_p},
$$

则

$$
F_\lambda(n)
=
\sum_p
\left[
\ln\left(\sum_{j=0}^{a_p}p^{-j}\right)
-\lambda a_p\ln p
\right].
\tag{291.2}
$$

因此，整个优化分解为逐素数的整数层选择。

---

## 定义291.2　增加第 \(a\) 层的边际阈值

对 \(a\ge1\)，定义

$$
\boxed{
m_p(a)
=
\frac{
\ln\!\left[
\dfrac{1-p^{-(a+1)}}{1-p^{-a}}
\right]
}{\ln p}.
}
\tag{291.3}
$$

增加一层的目标变化为

$$
\boxed{
F_{\lambda,p}(a)-F_{\lambda,p}(a-1)
=
\bigl(m_p(a)-\lambda\bigr)\ln p.
}
\tag{291.4}
$$

所以：

$$
m_p(a)>\lambda
\quad\Longrightarrow\quad
\text{增加该层有利};
$$

$$
m_p(a)<\lambda
\quad\Longrightarrow\quad
\text{增加该层不利}.
$$

## 定理291.1　整数层的最优停止条件

\(m_p(a)\) 随 \(a\) 严格下降。因此，指数 \(a\) 最优的条件是

$$
\boxed{
m_p(a+1)\le\lambda\le m_p(a),
}
\tag{291.5}
$$

其中 \(a=0\) 时只需右侧“新增第一层不利”的条件。

### 证明

有

$$
\frac{1-p^{-(a+1)}}{1-p^{-a}}
=
1+\frac{p-1}{p(p^a-1)}.
$$

它随 \(a\) 严格下降。对数严格递增，且 \(\ln p>0\)，所以 \(m_p(a)\) 严格下降。

于是局部目标先增加、后减少，最大值位于增益改变符号的位置。∎

**这就是第一种离散临界：不是导数连续地变成零，而是“下一整层是否值得加入”发生改变。**

---

# 292．5040不是一个临界点，而是一个稳定区间的标签

对

$$
5040=2^4\,3^2\,5\,7,
$$

我们可以把全部边际条件精确解出来。

## 定理292.1　5040的完整最优价格区间

定义

$$
\boxed{
\lambda_-=\frac{\ln(12/11)}{\ln11},
\qquad
\lambda_+=\frac{\ln(31/30)}{\ln2}.
}
\tag{292.1}
$$

则：

$$
\boxed{
5040\text{ 是唯一最优整数}
\iff
\lambda_-<\lambda<\lambda_+.
}
\tag{292.2}
$$

数值为

$$
\lambda_-\approx0.0362865626271,
$$

$$
\lambda_+\approx0.0473057147784.
$$

在两个端点：

$$
\boxed{
\operatorname*{argmax}_{n\ge1}F_{\lambda_-}(n)
=
\{5040,55440\},
}
\tag{292.3}
$$

$$
\boxed{
\operatorname*{argmax}_{n\ge1}F_{\lambda_+}(n)
=
\{2520,5040\}.
}
\tag{292.4}
$$

### 证明

对已占据的四条素数轴，最后一层的阈值分别为

$$
m_2(4),\quad m_3(2),\quad m_5(1),\quad m_7(1).
$$

其中最小者是

$$
m_2(4)=\lambda_+.
$$

四条轴的下一层阈值都小于 \(0.03\)。

对尚未占据的素数，第一层阈值

$$
m_p(1)=\frac{\ln(1+1/p)}{\ln p}
$$

随 \(p\) 严格下降。因此最大者来自 \(p=11\)，等于 \(\lambda_-\)。

这些比较可以用精确有理幂验证。例如

$$
m_2(5)<\frac3{100}
\iff
\left(\frac{63}{62}\right)^{100}<2^3.
$$

综合得到：全部已选层严格有利、全部未选层严格不利，恰好要求

$$
\lambda_-<\lambda<\lambda_+.
$$

端点处分别只有“增加一个11因子”或“删除一个2因子”出现平局，其余层仍严格。

最后，式（291.2）的逐素数分解把局部结论提升为全体正整数上的结论。∎

这种目标属于经典的 colossally abundant 数优化结构，不是需要另造一个数论种类才能解释的现象。([arXiv][1])

### 这两个临界分别意味着什么？

随着价格降低，在这两个边界的邻域：

$$
\boxed{
2520
\ \longrightarrow\
5040
\ \longrightarrow\
55440.
}
\tag{292.5}
$$

第一次改变是：

$$
v_2:3\longrightarrow4,
$$

即**已有素数轴增加深度**。

第二次改变是：

$$
v_{11}:0\longrightarrow1,
$$

即**新的素数轴进入最优配置**。

所以，“增加一层”和“增加一个坐标方向”在这里是两种精确不同的离散事件。

而项目使用的

$$
\lambda=\frac1{25}=0.04
$$

位于稳定区间内部，**不是临界值本身**。

---

# 293．离散性还带来严格的稳定差距

连续参数的极小扰动，可能只带来任意小的目标变化。整数状态则可以在稳定区间内部具有一个统一的非零差距。

## 定义293.1　距临界边界的裕量

固定

$$
\lambda_-<\lambda<\lambda_+,
$$

令

$$
\boxed{
\eta_\lambda
=
\min(\lambda-\lambda_-,\lambda_+-\lambda)>0.
}
\tag{293.1}
$$

定义两个整数的素数指数距离

$$
d_{\mathrm{arith}}(m,n)
=
\sum_p|v_p(m)-v_p(n)|\ln p.
$$

它也可以写成

$$
\boxed{
d_{\mathrm{arith}}(m,n)
=
\ln\frac{\operatorname{lcm}(m,n)}{\gcd(m,n)}.
}
\tag{293.2}
$$

## 定理293.1　5040稳定区间内的全局差距

对任意正整数 \(n\)，

$$
\boxed{
F_\lambda(5040)-F_\lambda(n)
\ge
\eta_\lambda\,d_{\mathrm{arith}}(n,5040).
}
\tag{293.3}
$$

特别地，若 \(n\ne5040\)，则

$$
\boxed{
F_\lambda(5040)-F_\lambda(n)
\ge
\eta_\lambda\ln2>0.
}
\tag{293.4}
$$

### 证明

从5040的指数配置出发：

每删除一个已有层，其边际阈值至少为 \(\lambda_+\)，故目标损失至少为

$$
(\lambda_+-\lambda)\ln p.
$$

每加入一个未选层，其边际阈值至多为 \(\lambda_-\)，故目标损失至少为

$$
(\lambda-\lambda_-)\ln p.
$$

累加所有指数差异，得到式（293.3）。

不同整数至少在某个素数指数上相差一，而最小素数为2，故得到式（293.4）。∎

### 几何解释

把每个整数映射为平面上的点

$$
\bigl(E(n),W(n)\bigr)
=
\bigl(\ln n,\ln Z(n)\bigr).
$$

最大化 \(F_\lambda\) 就是寻找

$$
W-\lambda E
$$

最大的点。

5040能够在一整个斜率区间内被同一支持直线选中；到边界时，支持直线同时接触另一个整数点。

因此：

> **这里的临界，是最优离散状态之间的切换；稳定区间内部，则存在由整数层间隔保证的鲁棒性。**

这与“5040的数值特别接近某个神秘常数”完全不同。

---

# 294．第二类临界：几何内部什么时候第一次容得下隐藏状态？

现在回到前两轮的五类计数模型。注意，这一步改变了读数语义：素数指数被解释为五类合法状态的数量。

令

$$
z=(z_{00},z_{10},z_{01},z_{11},z_t),
$$

观察者保存

$$
Az=
\begin{pmatrix}
K\\X_0\\X_1\\X_2
\end{pmatrix}
=
\begin{pmatrix}
z_{00}+z_{10}+z_{01}+z_{11}+z_t\\
z_{10}+z_{11}\\
z_t\\
z_{01}+z_{11}
\end{pmatrix}.
\tag{294.1}
$$

固定 \(Az=y\) 的所有非负整数实现构成纤维 \(\mathcal F_y\)。

设该纤维非空，定义

$$
R=K-X_1,
$$

以及四个整数余量的最小值

$$
\boxed{
s(y)=\min\{X_0,X_2,R-X_0,R-X_2\}.
}
\tag{294.2}
$$

## 定理294.1　纤维状态数恰好等于“一加最小余量”

有

$$
\boxed{
|\mathcal F_y|=1+s(y).
}
\tag{294.3}
$$

### 证明

令 \(k=z_{11}\)。全部状态可写为

$$
z(k)=
(R-X_0-X_2+k,\ X_0-k,\ X_2-k,\ k,\ X_1),
$$

其中

$$
\max(0,X_0+X_2-R)
\le k\le
\min(X_0,X_2).
$$

因此状态数为

$$
1+\min(X_0,X_2)-\max(0,X_0+X_2-R).
$$

按 \(X_0+X_2\le R\) 或 \(X_0+X_2\ge R\) 分类，两种情形都化为式（294.3）。∎

### 四棱锥的临界位置终于有了整数含义

当 \(K>0\)，设归一化占据为 \(x_j=X_j/K\)。则

$$
\boxed{
s(y)
=
K\min\{x_0,x_2,1-x_1-x_0,1-x_1-x_2\}.
}
\tag{294.4}
$$

这些量是四个侧面不等式的余量，**不是欧氏距离**。

因此：

$$
s=0
\quad\Rightarrow\quad
\text{同一读数只对应一个整数实现};
$$

$$
s\ge1
\quad\Rightarrow\quad
\text{同一读数背后存在不同内部实现}.
$$

底面 \(x_1=0\) 本身不意味着唯一实现。底面内部恰恰可以具有很多隐藏状态。

整数纤维与保持统计量的移动，是代数统计中已有的正式结构；本轮的意义在于得到这个模型的精确计数公式。([Project Euclid][2])

---

# 295．最小临界资源：一个隐藏比特需要至少两个计数单元

定义纤维量子空间

$$
\mathcal H_y=\operatorname{span}\{|z\rangle:z\in\mathcal F_y\}.
$$

则

$$
\boxed{
d_y=\dim\mathcal H_y=s(y)+1.
}
\tag{295.1}
$$

这是在既有整数模型上选择的量子实现，不是单凭计数就证明自然界必须采用量子理论。

## 定理295.1　隐藏动力学的最小维数阈值

当 \(s=0\) 时，\(\mathcal H_y\) 一维。任何保持该纤维的 Hamiltonian 都只产生整体相位，不能在其内部形成不同密度矩阵之间的演化。

当 \(s\ge1\) 时，它至少可以容纳两个正交态，并且可以选择非标量 Hamiltonian 产生内部振荡。

### 证明

一维空间上的线性算子都是标量。

二维以上空间可以包含一个二维子空间，并在其上选择 \(JX\) 作为 Hamiltonian。∎

所以：

$$
\boxed{
s:0\longrightarrow1
}
$$

是一条精确的**内部可区分状态出现阈值**。

它不是说所有满足 \(s\ge1\) 的系统都会自发产生时钟；还需要实际耦合、初态和读出。

---

## 定理295.2　固定总数量下的最大隐藏维数

有

$$
\boxed{
d_y\le\left\lfloor\frac{K-X_1}{2}\right\rfloor+1
\le
\left\lfloor\frac K2\right\rfloor+1.
}
\tag{295.2}
$$

要得到 \(d\) 维纤维，最小总数量为

$$
\boxed{
K_{\min}=2(d-1).
}
\tag{295.3}
$$

### 证明

由

$$
s\le\min(X_0,R-X_0)\le R/2
$$

得到上界。

取

$$
K=2s,\qquad X_0=X_2=s,\qquad X_1=0,
$$

即达到 \(d=s+1\)。∎

于是最小实例为：

|       隐藏维数 | 最小 \(K\) | 一个整数纤维                 |
| ---------: | -------: | ---------------------- |
|          2 |        2 | \(\{14,15\}\)          |
|          3 |        4 | \(\{196,210,225\}\)    |
| 5040所在纤维：3 |     此例为8 | \(\{4704,5040,5400\}\) |

因此，**5040并不是产生三态内部结构的最小整数实例。**

它的重要性应当来自它同时满足的具体算术、优化和观察条件，而不是把“三态出现”本身专属于5040。

另一个重要结果是：若只保留归一化位置

$$
(x_0,x_1,x_2)=\left(\frac12,0,\frac12\right),
$$

则 \(K=2m\) 时

$$
d_y=m+1.
$$

**相同的几何点，可以随着实际资源规模增加而容纳越来越多的内部状态。**归一化几何没有记录这个绝对规模。

---

# 296．奇偶的临界意义：它决定是否必然留下一个零模

在一条长度为 \(d\) 的纤维上，只允许相邻的原始移动，取

$$
H=
\sum_{j=0}^{d-2}
t_j
\bigl(
|j+1\rangle\langle j|
+
|j\rangle\langle j+1|
\bigr),
\qquad t_j>0.
\tag{296.1}
$$

没有对角能量项。

定义

$$
\Gamma|j\rangle=(-1)^j|j\rangle.
$$

## 定理296.1　路径纤维的精确零模奇偶律

有

$$
\{\Gamma,H\}=0,
$$

并且

$$
\boxed{
\dim\ker H=
\begin{cases}
1,&d\text{ 为奇数},\\
0,&d\text{ 为偶数}.
\end{cases}
}
\tag{296.2}
$$

### 证明

每条边都连接相反奇偶，因此反对易关系成立。

求零模时，第一行给出 \(t_0\psi_1=0\)，故 \(\psi_1=0\)。继续递推，全部奇数位振幅为零，而偶数位由 \(\psi_0\) 唯一确定。

若 \(d\) 为奇数，最后一个条件与递推相容，得到一维解。

若 \(d\) 为偶数，最后一行迫使最后一个偶数位为零，再反推所有振幅为零。∎

因此，对本纤维模型：

$$
\boxed{
s\text{ 为偶数}
\iff
d=s+1\text{ 为奇数}
\iff
H\text{ 有一个零模}.
}
\tag{296.3}
$$

\(d=1\) 是平凡情形；第一个同时包含非平凡跃迁与零模的情形是 \(d=3\)。

奇数维与手征反对称性保证零模，是已有量子谱理论中的机制，并非零模只会出现在本算术模型。([arXiv][3])

### 必须分清这里的奇偶

这里是**沿纤维排列的状态编号奇偶**。不是：

$$
n\bmod2,
$$

也不是固定总计数 \(K\) 的奇偶。

事实上，纤维移动保持 \(K\)，所以不能用总计数奇偶解释这里的交替分块。

---

## 素数能量会检验这项保护究竟有多强

5040三态链的混合 Hamiltonian 为

$$
H_{\mathrm{mix}}
=
J
\begin{pmatrix}
0&2\sqrt6&0\\
2\sqrt6&0&2\sqrt5\\
0&2\sqrt5&0
\end{pmatrix}.
$$

若加入对数能量，并减去中间态5040的共同能量，附加项为

$$
D_{\log}=\operatorname{diag}(\Delta,0,-\Delta),
\qquad
\Delta=E_*\ln\frac{15}{14}>0.
$$

则

$$
\boxed{
\det(H_{\mathrm{mix}}+D_{\log})
=
4J^2\Delta\ne0.
}
\tag{296.4}
$$

所以，原来的精确零模消失。

**离散奇偶结构提供保护，但保护有对称性前提。不能先用无对角 Hamiltonian 证明暗态，再加入不相容的素数能量，还宣称暗态无条件保留。**

---

# 297．另一个纯粹离散的临界：相同连续方向，不同整数可达性

这可能是“几何编程语言”最值得深入的一点。

原始移动是

$$
\delta=(-1,1,1,-1,0),
$$

对应

$$
\frac{15}{14}.
$$

现在把允许的正反移动改为

$$
\pm2\delta,
$$

对应分数及其逆：

$$
\frac{225}{196},
\qquad
\frac{196}{225}.
$$

两者的实线性方向完全相同：

$$
\boxed{
\operatorname{span}_{\mathbb R}\{\delta\}
=
\operatorname{span}_{\mathbb R}\{2\delta\}.
}
\tag{297.1}
$$

但整数移动群不同：

$$
\mathbb Z\delta
\ne
2\mathbb Z\delta.
$$

## 定理297.1　跳跃步长决定离散连通分量

在 \(d\) 个连续整数标签

$$
0,\ldots,d-1
$$

上，如果只允许 \(\pm m\) 步移动，那么执行图恰有

$$
\boxed{\min(m,d)}
\tag{297.2}
$$

个连通分量。

### 证明

每一步保持标签模 \(m\) 的余数。每个实际出现的余数类内部，依次加减 \(m\) 可以连接全部标签。∎

于是对三态纤维：

$$
4704
\xleftrightarrow{\,225/196\,}
5400,
$$

而

$$
\boxed{5040\text{ 被隔离}.}
\tag{297.3}
$$

连续几何看到的还是同一条线，但整数程序已经从一条连通链变成两个互不连通的部分。

**这是真正不能被“连续化以后只看方向”保留的离散信息：整数格的指数与剩余类。**

边界还会进一步限制可达性。即使允许步长3、4，其最大公因数为1，在仅有 \(\{0,1,2,3\}\) 的窗口内，也只有 \(0\leftrightarrow3\)，中间两个点仍然孤立。

所以，整数核的实线性包还不够；还要保留整数生成关系和非负边界。

---

## 两条内部移动何时第一次产生真正闭路？

若两个独立纤维的维数为

$$
d_1=s_1+1,\qquad d_2=s_2+1,
$$

并且只允许分别沿它们作最近邻移动，则联合执行图是两个路径图的乘积。

其独立回路数为

$$
\boxed{
\beta_1
=
|E|-|V|+1
=
(d_1-1)(d_2-1)
=
s_1s_2.
}
\tag{297.4}
$$

证明由

$$
|V|=d_1d_2,
$$

$$
|E|=(d_1-1)d_2+d_1(d_2-1)
$$

直接得到。

所以，最小非平凡回路出现在

$$
s_1=s_2=1,
$$

即两条两态纤维组成的四态方形。

这为固定执行图上的不可消去闭路相位提供了第一个位置。**三态暗模与四态闭路，是两种不同的最小结构。**

这里讨论的是指定执行图的边相位，不排除其他时间依赖控制协议产生几何相位。

---

# 298．同一个整数纤维，还能给出一个精确的有限量子钟

现在单独采用对数能量 Hamiltonian，不同时套用前面的无对角混合 Hamiltonian。

沿 \(\delta\) 方向，整数每步乘以 \(15/14\)。因此任意一条 \(d\) 态纤维，按能量递增排序后：

$$
n_j=n_0\left(\frac{15}{14}\right)^j,
\qquad j=0,\ldots,d-1.
$$

于是

$$
\boxed{
E_j=E_{\min}+j\Delta,
\qquad
\Delta=E_*\ln\frac{15}{14}.
}
\tag{298.1}
$$

这里出现了一个与完整素数对数谱不同的结果：

> **完整寄存器空间可以没有共同精确周期，但沿这条固定的一维算术纤维，能谱恰好是等间隔的。**

## 定理298.1　\(d\) 态纤维可以形成 \(d\) 个正交内部钟读数

定义

$$
|\chi_0\rangle=\frac1{\sqrt d}\sum_{j=0}^{d-1}|n_j\rangle,
$$

以及

$$
T_0=\frac{2\pi\hbar}{\Delta}.
$$

在时刻

$$
t_m=\frac{mT_0}{d},
\qquad m=0,\ldots,d-1,
$$

得到的态两两正交。

### 证明

忽略共同相位，有

$$
|\chi_m\rangle
=
\frac1{\sqrt d}
\sum_{j=0}^{d-1}
e^{-2\pi ijm/d}|n_j\rangle.
$$

因此

$$
\langle\chi_m|\chi_n\rangle
=
\frac1d\sum_{j=0}^{d-1}
e^{2\pi ij(m-n)/d}
=
\delta_{mn}.
$$

∎

结合 \(d=s+1\)，得到

$$
\boxed{
\text{整数余量 }s
\longrightarrow
s+1\text{ 个可正交区分的内部相位标签}.
}
\tag{298.2}
$$

这与“观察者在固定粗几何内部拥有自己的时钟”直接相容：全部 \(\widehat Q_\alpha\) 在纤维中都取同一个值，但增加合适的内部读出后，可以区分这些时钟态。

### 不是免费提高刷新率

最小相邻正交间隔为

$$
\delta t=\frac{2\pi\hbar}{d\Delta}.
$$

同时，能谱宽度为

$$
W_E=(d-1)\Delta,
$$

且初始钟态能量方差为

$$
\boxed{
(\Delta H)^2=\frac{d^2-1}{12}\Delta^2.
}
\tag{298.3}
$$

增加 \(d\) 时，能够区分的时钟标签更多，但这里的能量范围与资源也在增加。

而且，只有相位标签并不等于自动形成永久记录。读取、周期计数和记录保持仍然需要物理实现。

---

# 299．有限谱零点、优化临界与热力学相变，必须分开

对第298节的能谱：

$$
Z_d(\beta)
=
\sum_{j=0}^{d-1}e^{-\beta(E_{\min}+j\Delta)}.
$$

令

$$
q=e^{-\beta\Delta},
$$

则

$$
\boxed{
Z_d(\beta)
=
e^{-\beta E_{\min}}
(1+q+\cdots+q^{d-1}).
}
\tag{299.1}
$$

## 定理299.1　离散态数确定有限配分函数的复零点

当 \(d\ge2\) 时，

$$
Z_d(\beta)=0
$$

当且仅当

$$
\boxed{
\beta=
\frac{2\pi i\ell}{d\Delta},
\qquad
\ell\in\mathbb Z,\quad d\nmid\ell.
}
\tag{299.2}
$$

### 证明

有限几何级数为零，等价于

$$
q^d=1,\qquad q\ne1.
$$

代入 \(q=e^{-\beta\Delta}\) 即可。∎

把

$$
\beta=\frac{it}{\hbar}
$$

代入，正好得到第298节钟态返回振幅的相消时刻。

因此：

$$
\boxed{
\text{态数}
\longrightarrow
\text{单位根}
\longrightarrow
\text{有限干涉零点}.
}
$$

这是一条真实的算术—谱—时间联系。

但对实数 \(\beta>0\)，每一项都为正：

$$
\boxed{Z_d(\beta)>0.}
$$

有限维、固定 Hamiltonian 的这个热配分函数在实温度区域没有由这些复零点直接造成的奇点。有限系统的解析性与热力学极限中的非解析性必须区分。([arXiv][4])

所以，目前至少有三种不同的“零”：

| 零条件                  | 表示什么                   |
| -------------------- | ---------------------- |
| \(m_p(a)-\lambda=0\) | 两个整数配置的优化得分相同          |
| \(\det H=0\)         | 选定 Hamiltonian 存在零能本征态 |
| \(Z_d(\beta)=0\)     | 复参数下的相位或权重精确相消         |

它们具有不同变量、不同定义域和不同稳定条件。

**不能因为都出现“临界”或“零点”，就把它们认定为同一个机制，更不能由这里的单位根直接推出 ζ 非平凡零点的位置。**

---

# 300．真正的离散临界，是结构不变量改变，而不是某个数被赋予特殊身份

现在可以把本轮结果组织成几类相互独立的临界：

| 临界对象  | 改变条件               | 改变的内容             |
| ----- | ------------------ | ----------------- |
| 最优寄存器 | \(\lambda\) 穿过边际阈值 | 哪个整数被选中           |
| 隐藏状态  | \(s:0\to1\)        | 同一粗读数能否容纳不同内部态    |
| 受保护零模 | 路径维数奇偶及手征条件        | 是否必有零能态           |
| 整数可达性 | 原始移动变为非原始移动        | 是否分裂为不同剩余类        |
| 闭路结构  | \(\beta_1:0\to1\)  | 是否出现不可由顶点更名消去的边相位 |
| 内部钟容量 | \(d=s+1\) 改变       | 可正交区分的相位标签数       |

这些临界不会无条件同时发生。

一个很有说明力的例子是：

|    整数 | 因数基态数 | 五类计数模型的纤维维数 |
| ----: | ----: | ----------: |
|  2520 |    48 |           3 |
|  5040 |    60 |           3 |
| 55440 |   120 |           3 |

在优化临界处，选中的整数与因数空间大小发生跳变；但我们当前选择的三态纤维结构没有改变。

**所以，同一个整数可以同时属于多种结构，而“它的临界意义”必须说明是对哪个目标、哪个接口和哪种动力学而言。**

---

## 与项目的方法论连接

本轮得到两条互补的严格路线：

$$
\boxed{
\text{层增益与资源价格}
\longrightarrow
\text{最优整数的稳定区间及严格差距};
}
$$

$$
\boxed{
\text{非负整数约束}
\longrightarrow
\text{纤维维数、连通分量与谱结构}.
}
$$

已有 `PrimeAxisEncoding.lean` 保证编码层的对应；但这些对应不自动选择物理 Hamiltonian。已有 `ExactDescentNoCarry.lean` 则要求针对指定 FLOW 和目标证明下降，不能把“当前几何没变”扩大成“全部未来实验都无法区分”。

同样，项目的守恒—自主性区分继续重要：粗几何可以严格守恒，而其纤维中的状态持续变化。

### 本轮核验

本次项目版本固定为：

```text
d136c6195898e7837a54b42dd954595070fc3df1
```

本轮完成了 **53项命名检查**，包括：

* 5040最优区间所需的精确有理幂不等式；
* \(n\le60000\) 的精确整数目标比较；
* 总计数 \(K\le14\) 的 **5440条纤维、11628个计数状态**；
* 奇偶零模、对角能量破坏零模的行列式；
* 整数步长造成的连通分裂；
* 有限时钟与几何级数零点的代数关系。

[核验脚本](sandbox:/mnt/data/observer_formalization/check_discrete_criticality.py)
[核验结果](sandbox:/mnt/data/observer_formalization/discrete_criticality_checks.json)

**本轮未运行 Lean 内核检查。**新增一般结论由上文证明给出；有限枚举不替代全称证明，也不把模型中的结构临界认证为现实物理相变。

---

# 结论

这次找到的“离散的临界意义”，可以概括为：

> **离散性不只是把连续量切成小格子；它使“有没有第二个合法状态”“能不能跨过某个剩余类”“是否存在零模”“是否形成闭路”成为可以严格改变的结构事实。**

其中，与你的观察者理论最直接相关的是：

$$
\boxed{
s=0:
\text{固定身份读数后，内部只剩一个状态};
}
$$

$$
\boxed{
s\ge1:
\text{同一身份读数背后，开始能够存在内部区分与变化};
}
$$

$$
\boxed{
d=s+1:
\text{这些隐藏状态能够承担多少有限量子结构}.
}
$$

而5040的算术意义也变得更准确：

$$
\boxed{
\frac{\ln(12/11)}{\ln11}
<
\lambda
<
\frac{\ln(31/30)}{\ln2}
}
$$

是它在当前目标下稳定被选中的区间；其两端分别对应**新增素数轴**与**已有素数轴的层数切换**。

**最值得继续推进的，不是寻找一个能解释一切的“临界整数”，而是证明：某个现实量子系统的资源、约束与允许操作，为什么恰好跨过这些结构阈值。**

只有把这一步补上，我们才能从“算术模型中存在临界”，继续走向“有限量子观察者为什么会形成内部时间、稳定身份和共同可读的物理世界”。

[1]: https://arxiv.org/abs/1112.6010 "https://arxiv.org/abs/1112.6010"
[2]: https://projecteuclid.org/journals/annals-of-statistics/volume-26/issue-1/Algebraic-algorithms-for-sampling-from-conditional-distributions/10.1214/aos/1030563990.short "https://projecteuclid.org/journals/annals-of-statistics/volume-26/issue-1/Algebraic-algorithms-for-sampling-from-conditional-distributions/10.1214/aos/1030563990.short"
[3]: https://arxiv.org/abs/2001.07653 "https://arxiv.org/abs/2001.07653"
[4]: https://arxiv.org/abs/0912.3679 "https://arxiv.org/abs/0912.3679"
**你的直觉中，最值得推进的不是“世界根本没有平坦”，而是：我们所说的平坦，究竟是完整动力学的性质，还是某个观察尺度、某种坐标和某组实验下的有效性质？**

这两者确实可能不同。但“曲率＝拓扑＝因果＝信息逃逸”还不能直接成立。它们之间需要具体的构造和定理，否则同一个词会同时承担几种不相容的意思。

这一次，我们可以把这个区别与5040真正连接起来，并得到一个更精确的结果：

> **在项目采用的加权因数收益最优化族中，5040是最小的这样一个整数：某条素数轴第一次容纳完整的三位 Zeckendorf 窗口，使该轴的占据几何从四面体变成四棱锥；与此同时，原来足以恢复局部经典概率的三个占据读数，第一次遗漏一个关联自由度。**

这是一项限定明确的**离散优化—几何投影临界**。它不是说5040是宇宙的唯一临界常数，但比“数字与形状似乎相似”更强。

下面把整条推理展开。

# 平坦的观察条件、素数层最优化与5040的几何临界

## ——量子观察者—关系时空理论第三百零一至第三百一十节增订

---

# 301．“看起来平坦”至少有三种不同来源

首先把三种情况分开。

**第一种：完整模型确实平坦。**

例如，Minkowski度量

$$
\eta=-dt^2+dx^2+dy^2+dz^2
$$

的系数为常数，其 Levi–Civita 曲率严格为零。它是一个自洽的数学结构；不能因为存在无穷集合或对角化，就推出这种结构不可能存在。

**第二种：真实几何有曲率，但当前实验尺度太小。**

在光滑洛伦兹流形上，可以在一点附近选择正规坐标，使

$$
g_{\mu\nu}(p)=\eta_{\mu\nu},
\qquad
\partial_\alpha g_{\mu\nu}(p)=0,
$$

但一般不能同时消去曲率。局部度量偏离平直形式的领先项从二阶开始：

$$
\boxed{
g_{\mu\nu}(x)
=
\eta_{\mu\nu}
-\frac13R_{\mu\alpha\nu\beta}(p)x^\alpha x^\beta
+O(|x|^3).
}
\tag{301.1}
$$

因此，在尺度 \(L\) 上，几何偏差通常由类似

$$
\boxed{\|R\|L^2}
$$

的无量纲量控制。实验只覆盖很小区域时，弯曲几何可以被平直模型很好地近似；这不是曲率不存在。([David Tong][1])

**第三种：观察接口没有保存能够显示差别的变量。**

例如，只记录某些位置均值，可能看不到相位、两体关联或隐藏控制寄存器。扩大实验以后，原来“相同”的状态才被区分。

这正是项目的 CUT 与 carry 所处理的问题。

---

## 无穷不是平坦世界的一堵墙

\(\mathbb R^n\) 是无边界流形。“无穷远”不是其中一个尚未找到坐标的边界点；可以通过额外的紧化构造添加理想边界，但那是另一个数学操作。

同样：

$$
\boxed{
\text{无限对象}
\not\Rightarrow
\text{无法有限定义};
}
$$

$$
\boxed{
\text{全称无限命题}
\not\Rightarrow
\text{不存在有限证明}.
}
$$

对角化给出的障碍，涉及某类表示、枚举或判定机制能否覆盖所有对象，并不是一个关于 Riemann 曲率的通用定理。

一个简单例子是无限比特序列。令

$$
q_N(x)=(x_1,\ldots,x_N).
$$

每个有限接口都遗漏未来位：

$$
\ker q_N\ne\Delta.
$$

但全部前缀合起来可以区分任意两个序列：

$$
\boxed{
\bigcap_{N\ge1}\ker q_N=\Delta.
}
\tag{301.2}
$$

这里出现了逐层完成，没有因此自动出现某个物理曲率。

所以更准确的问题是：

> **当前接口遗漏的区别，是否会影响当前允许实验中的未来预测？**

---

# 302．投影确实可能制造“表观弯曲”，但我们能够指出它是怎样发生的

这一节给出一个完整有限反例。

## 定义302.1　两个本来可交换的过程

取四个微观状态 \(1,2,3,4\)。

操作 \(A\) 交换 \(1,2\)；操作 \(B\) 交换 \(3,4\)。它们作用于互不相交的部分，因此

$$
\boxed{AB=BA.}
\tag{302.1}
$$

若只讨论这两条操作的次序，完整模型具有精确路径一致性。

观察者却只保留三个概率：

$$
\boxed{
q(p_1,p_2,p_3,p_4)
=
(p_1+p_3,\ p_2,\ p_4).
}
\tag{302.2}
$$

也就是说，它把状态1与3合并。

现在选择一种补全规则：无法区分的1与3各分一半概率，

$$
R(r,s,t)=\left(\frac r2,s,\frac r2,t\right).
$$

由此构造两个粗模型操作：

$$
\overline A=qAR,
\qquad
\overline B=qBR.
$$

直接得到

$$
\overline A=
\begin{pmatrix}
1/2&1&0\\
1/2&0&0\\
0&0&1
\end{pmatrix},
\qquad
\overline B=
\begin{pmatrix}
1/2&0&1\\
0&1&0\\
1/2&0&0
\end{pmatrix}.
\tag{302.3}
$$

两者都是合法的随机矩阵。

## 定理302.1　完整过程可交换，逐步补全后的过程却不交换

初态取状态2，即粗读数

$$
y_0=(0,1,0).
$$

完整执行两种顺序，最终读数都是

$$
qABp_0=qBAp_0=(1,0,0).
$$

但粗模型给出

$$
\boxed{
\overline B\,\overline A\,y_0
=
\left(\frac12,0,\frac12\right),
}
\tag{302.4}
$$

$$
\boxed{
\overline A\,\overline B\,y_0
=
(1,0,0).
}
\tag{302.5}
$$

两结果的总变差距离为 \(1/2\)。

### 证明

逐次代入矩阵（302.3）即可。∎

### 这意味着什么？

不是观察者的无知神秘地改变了原来的数学事实。

真正发生的是：

$$
\boxed{
\text{每一步之后，
粗模型都把被删掉的区别重新替换成一种指定分布。}
}
$$

它已经不再忠实保留完整过程的中间状态。

若装置真的实施“测量后重新制备”，物理过程也确实被改变；若只是计算模型这样做，则是模型产生了错误的路径依赖。

---

## 定理302.2　投影诱导的交换子缺项

令 \(\Pi\) 为一个线性投影，\(Q=I-\Pi\)。则

$$
\boxed{
\begin{aligned}
[\Pi A\Pi,\Pi B\Pi]
={}&
\Pi[A,B]\Pi\\
&-\Pi AQB\Pi
+\Pi BQA\Pi.
\end{aligned}
}
\tag{302.6}
$$

### 证明

在 \(\Pi AB\Pi\) 和 \(\Pi BA\Pi\) 中插入 \(I=\Pi+Q\)，展开并相减。∎

即使

$$
[A,B]=0,
$$

粗过程仍可能出现非零交换子，其来源正是：

$$
\boxed{
\text{先进入被遗漏方向，
再返回可见方向的两种过程不同。}
}
$$

这给你的“投影造成几何”直觉一个准确的代数版本。

但它还不是 Riemann 曲率。要把路径差异识别为时空曲率，必须进一步证明这些操作确实实现了相应的几何平行输运，而不是仪器控制、遗忘或重制过程。

项目的 `exact_descent_has_no_carry` 恰好要求这种桥梁：必须有真实的交换等式，而不是仅凭几个单步读数拟合出一个下降过程。

---

# 303．因果确实能够重建部分几何，但拓扑不等于曲率

你的判断有一部分与严格的相对论几何非常接近：

> 可以把“哪些事件能够影响哪些事件”放在原始层，再尝试重建几何。

已有定理说明，在适当的因果可辨识条件下，维数大于二的时空，其因果关系能够确定共形几何，并确定相应的拓扑结构。但它一般只把度量确定到

$$
\boxed{\widetilde g=\Omega(x)^2g}
\tag{303.1}
$$

这样的正比例场，不能单独确定 \(\Omega(x)\)。([arXiv][2])

## 一个明确反例

取同一个 \(\mathbb R^4\)，比较

$$
g_0=\eta,
$$

与

$$
\boxed{
g_\alpha=e^{2\alpha x^2}\eta.
}
\tag{303.2}
$$

它们具有：

$$
\text{相同拓扑},
\qquad
\text{相同局部光锥},
\qquad
\text{相同因果先后关系}.
$$

但在前文采用的曲率约定下，直接计算得到

$$
\boxed{
\operatorname{Scal}(g_\alpha)\big|_{x=0}=-12\alpha,
}
\tag{303.3}
$$

而 \(g_0\) 的曲率为零。

所以：

$$
\boxed{
\text{同一因果关系}
\not\Rightarrow
\text{同一完整曲率}.
}
$$

还需要实际钟尺度、体积尺度或其他能固定共形因子的物理读数。

同样，拓扑只规定哪些局部可以怎样连接，并不单独决定距离与曲率。同一张流形可以具有不同度量。

甚至“同一个四边形”也需要区分：只保留四条边时有一个不可收缩的图环；填入一个二维面以后，这个环成为该面的边界。**添加哪些关系、哪些面、哪些路径等价，是结构的一部分，不能仅靠图像外观决定。**

因此，比较合理的构造次序是：

$$
\boxed{
\text{事件与可实施因果关系}
\longrightarrow
\text{拓扑／局部结构}
\longrightarrow
\text{钟尺与测度}
\longrightarrow
\text{度量、连接和曲率}.
}
$$

“逻辑”可以承载这条构造的定义与证明；但不是任何逻辑关系都自动具有物理因果意义。

---

# 304．\((4,2,1,1)\)到底有什么约束？答案分三层

这是必须最先明确的算术部分。

## 第一层：作为普通素数指数，它没有“禁止相邻11”的约束

任意正整数写成

$$
n=\prod_pp^{a_p}.
$$

其指数满足

$$
a_p\in\mathbb N,
\qquad
\text{只有有限多个 }a_p\ne0.
$$

除此以外，普通整数并不要求

$$
a_2\ge a_3\ge a_5\ge\cdots.
$$

例如 \(3^4\) 完全合法。

所以，\((4,2,1,1)\)不是一种数制本身的允许性规则，而是一个具体状态。

---

## 第二层：Zeckendorf约束作用在每条指数轴内部

采用

$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,
$$

每个指数唯一写成

$$
\boxed{
a_p=\sum_jb_{p,j}G_j,
\qquad
b_{p,j}\in\{0,1\},
\qquad
b_{p,j}b_{p,j+1}=0.
}
\tag{304.1}
$$

因此

$$
\boxed{
(4,2,1,1)
\longmapsto
(101,\;01,\;1,\;1),
}
\tag{304.2}
$$

数位从低权重到高权重排列。

不同素数行之间并没有额外的“不能同时为1”。例如5轴和7轴都占据最低位，完全合法。

仓库的 `canonicalRawValueEquiv` 正是把每一条规范黄金行与自然数指数建立为等价；这是一项无损表示结论。 对应的规范性与唯一性也已有 Mathlib 实现。([Lean Prover Community][3])

**规范编码只排除同一个数的冗余写法，不排除任何非负整数指数。**

---

## 第三层：最优化才会在不同素数轴之间产生联动约束

例如：

$$
a_2\ge a_3\ge a_5\ge a_7\ge\cdots
$$

以及“不能跳过小素数而先占据大素数”，不是 Zeckendorf 唯一性自动给出的，而是下面的目标函数所导出的。

这才是你说的“最经济、最有效率”可以真正落地的位置。

---

# 305．项目中的优化目标，会把指数排列成一个阶梯

本轮核对的仓库目标是

$$
\boxed{
F_\lambda(n)
=
\ln\left(\sum_{d\mid n}\frac1d\right)
-\lambda\ln n,
\qquad \lambda>0.
}
\tag{305.1}
$$

它不是含糊的“信息最大化”，而是具体的：

$$
\boxed{
\text{加权因数覆盖收益}
-
\text{对数规模成本}.
}
$$

注意，\(\ln\sum_{d\mid n}d^{-1}\)是对数配分函数，不等于任意所指的 Shannon 熵。

仓库已给出该目标、边际收益的定义，并有价格 \(1/25\) 下5040唯一最优的证明源码。

## 定义305.1　素数层的单位成本收益

对 \(a\ge1\)，定义

$$
\boxed{
m_p(a)=
\frac{
\ln\!\left[
\dfrac{1-p^{-(a+1)}}{1-p^{-a}}
\right]
}{\ln p}.
}
\tag{305.2}
$$

增加第 \(a\) 层的目标增益是

$$
\boxed{
\Delta F_{\lambda,p}(a)
=
\bigl(m_p(a)-\lambda\bigr)\ln p.
}
\tag{305.3}
$$

所以每层的准入条件就是：

$$
m_p(a)>\lambda.
$$

## 定理305.1　边际收益在“层数”和“素数大小”两个方向都下降

因为

$$
\frac{1-p^{-(a+1)}}{1-p^{-a}}
=
1+\frac1{p(1+p+\cdots+p^{a-1})},
\tag{305.4}
$$

故：

$$
m_p(a+1)<m_p(a),
$$

而固定 \(a\) 时，

$$
p<q\Longrightarrow m_p(a)>m_q(a).
$$

### 证明

增加 \(a\) 或 \(p\)，式（305.4）中的正增量都严格减小。

增加 \(p\) 时，分子对数减小，同时正分母 \(\ln p\) 增大，因此商严格减小。∎

---

## 推论305.1　最优指数具有向左、向下闭合的结构

若较大素数 \(q\) 的第 \(a\) 层值得保留，则较小素数 \(p<q\) 的同一层更值得保留。

因此，任意最优指数族满足

$$
\boxed{
a_2\ge a_3\ge a_5\ge a_7\ge\cdots,
}
\tag{305.5}
$$

非零素数支持必为最前面的一段素数。

这就是一个整数阶梯，也可看作 Ferrers 图。

对5040，阶梯为

$$
(4,2,1,1).
$$

有一个确切但有限的对称性：按列高读是 \((4,2,1,1)\)，按行长度读也是 \((4,2,1,1)\)，因此这个无权图形自共轭。

但它不是物理能量对称：

$$
\ln2\ne\ln7,
$$

反射后的格子具有不同成本和不同边际收益。

**图形对称成立，不代表带权动力学也具有同一个对称。**

---

## 定理305.2　每个固定正价格，只会激活有限多层

由

$$
\ln(1+x)\le x
$$

及式（305.4），得到

$$
\boxed{
m_p(a)\le\frac1{p^a\ln p}.
}
\tag{305.6}
$$

最优配置中的一个非零层必须满足

$$
\boxed{
p^a\ln p\le\frac1\lambda.
}
\tag{305.7}
$$

所以任何固定 \(\lambda>0\) 下，只有有限多个素数和有限多个层可以被激活。

这证明了一个重要事实：

> **无限素数空间中的全局优化，可以在每个固定正价格下被严格归约为有限激活结构。**

项目的 `golden_prime_local_objective_maximal_of_threshold` 给出了把局部边界阈值积累为全指数最优性的形式化步骤。

---

# 306．5040的精确临界：一个稳定价格区间，两种不同的边界事件

对

$$
5040=2^4\,3^2\,5\,7,
$$

要保持当前指数，必须满足

$$
m_p(a_p+1)\le\lambda\le m_p(a_p)
$$

并排除所有新素数轴。

关键阈值为：

| 素数轴         |                最后一层的阈值 |          新增一层的阈值 |
| ----------- | ---------------------: | ---------------: |
| \(2,\ a=4\) |       \(0.0473057148\) | \(0.0230836131\) |
| \(3,\ a=2\) |       \(0.0728580123\) | \(0.0230452620\) |
| \(5,\ a=1\) |       \(0.1132827526\) | \(0.0203734624\) |
| \(7,\ a=1\) |       \(0.0686215613\) | \(0.0090957833\) |
| 下一条轴 \(11\) | 第一层阈值 \(0.0362865626\) |                — |

## 定理306.1　5040的完整稳定区间

定义

$$
\boxed{
\lambda_-=\frac{\ln(12/11)}{\ln11},
\qquad
\lambda_+=\frac{\ln(31/30)}{\ln2}.
}
\tag{306.1}
$$

则

$$
\boxed{
\lambda_-<\lambda<\lambda_+
}
\tag{306.2}
$$

时，5040是所有正整数中的唯一最优解。

两个端点分别有

$$
\boxed{
\operatorname*{argmax}F_{\lambda_-}
=
\{5040,55440\},
}
\tag{306.3}
$$

$$
\boxed{
\operatorname*{argmax}F_{\lambda_+}
=
\{2520,5040\}.
}
\tag{306.4}
$$

### 证明

所有已选层中，最小的最后一层阈值为

$$
m_2(4)=\lambda_+.
$$

所有尚未选择的层中，最大阈值为

$$
m_{11}(1)=\lambda_-.
$$

后者同时使用了：已有四条轴的下一层阈值都更小，以及新素数第一层阈值随素数严格下降。

因此，区间内部所有已选层严格有利，所有未选层严格不利。目标函数按素数分解，得到全局唯一性。

端点分别只有一个层出现平局，故得到式（306.3）—（306.4）。∎

这些比较不必依赖浮点数。例如

$$
m_2(4)>\frac1{25}
\iff
\left(\frac{31}{30}\right)^{25}>2,
$$

右侧是一个可以精确验证的整数不等式。

这一目标对应经典的 colossally abundant 数优化，而不是由黄金编码另行发明的数类。([arXiv][4])

### 两个不同的离散事件

随着价格降低：

$$
\boxed{
2520\longrightarrow5040\longrightarrow55440.
}
\tag{306.5}
$$

第一次是

$$
a_2:3\longrightarrow4,
$$

即增加已有素数轴的深度。

第二次是

$$
a_{11}:0\longrightarrow1,
$$

即激活新素数轴。

因此：

> **5040不是一个孤立临界点，而是两种结构改变之间的稳定配置。**

价格 \(1/25=0.04\) 位于该区间内部。它是一个有效的唯一最优证书，但不是临界值本身。

---

# 307．更深的联系：2520到5040，恰好让四面体变成四棱锥

这里把优化与前几轮的几何连接起来。

## 定义307.1　单素数轴的局部因数状态

对指数上界 \(a\)，允许局部指数

$$
0,1,\ldots,a,
$$

并将它们写成 Zeckendorf 字串。

当 \(a=3\) 时：

$$
0\leftrightarrow000,\quad
1\leftrightarrow100,\quad
2\leftrightarrow010,\quad
3\leftrightarrow001.
$$

当 \(a=4\) 时，新增：

$$
\boxed{4=3+1\leftrightarrow101.}
\tag{307.1}
$$

这里的新增状态始终满足“不能连续11”。之前没有它，是因为指数资源上界为3，而不是因为它违反规范编码。

---

## 定理307.1　第四层的加入造成局部观察充分性的改变

### 在 \(a=3\) 时

四个占据向量

$$
000,\quad100,\quad010,\quad001
$$

仿射独立，其凸包是四面体。

三个占据均值

$$
x_0,x_1,x_2
$$

足以恢复全部四态概率：

$$
p_{100}=x_0,\quad
p_{010}=x_1,\quad
p_{001}=x_2,
$$

$$
p_{000}=1-x_0-x_1-x_2.
$$

### 在 \(a=4\) 时

第五个向量 \(101\) 加入，出现仿射关系：

$$
\boxed{
000+101=100+001.
}
\tag{307.2}
$$

凸包变成四棱锥；五态概率有四个自由度，但占据接口仍只有三个参数。

因此它第一次遗漏一个经典关联自由度。

### 证明

前四个向量构成原点及三个标准基，故仿射独立。

加入第五个向量后，式（307.2）成立。增广观察矩阵仍然秩四，但现在有五列，所以其核恰有一维。∎

一个明确的不可区分对是：

$$
p_A=\frac12\delta_{000}+\frac12\delta_{101},
$$

$$
p_B=\frac12\delta_{100}+\frac12\delta_{001}.
$$

它们都具有

$$
(x_0,x_1,x_2)=\left(\frac12,0,\frac12\right),
$$

但两端关联不同。

所以：

$$
\boxed{
\text{新增一个合法离散状态}
\longrightarrow
\text{旧观察坐标从充分变为不充分}.
}
\tag{307.3}
$$

这正是“离散临界”非常具体的一种意义。

---

## 单比特执行图也同时改变

如果允许的局部操作是一位合法翻转，那么：

| 指数上界 | 合法顶点数 | 合法边数 | 独立回路数 |
| ---: | ----: | ---: | ----: |
|    3 |     4 |    3 |     0 |
|    4 |     5 |    5 |     1 |

\(101\) 的加入同时连接 \(100\) 与 \(001\)，形成：

$$
000\to100\to101\to001\to000.
$$

因此，在这个**单素数轴的指定执行图**中，第一次出现独立闭路。

这可以容纳一个不可由局部基底相位消去的环相位，但环上的实际量子耦合仍然需要另外定义。

不能把它说成整个算术系统第一次出现任何四边形：不同素数轴的独立变化，早就可以产生跨轴方形。

---

## 定理307.2　在项目的全局最优族中，这个局部阈值最早出现在5040

设 \(n\) 是某个 \(F_\lambda\) 的全局最优整数。如果它有某条素数轴的指数至少为4，则

$$
\boxed{5040\mid n.}
\tag{307.4}
$$

因此，5040是该优化族中最小的、具有上述局部关联临界的整数。

### 证明

最优指数随素数递减，所以某条轴指数至少为4，必有

$$
a_2\ge4.
$$

局部最优性要求

$$
\lambda\le m_2(4).
$$

而

$$
m_3(2)>m_2(4),\qquad
m_5(1)>m_2(4),\qquad
m_7(1)>m_2(4).
$$

所以这些层必须严格被选中：

$$
a_3\ge2,\qquad a_5\ge1,\qquad a_7\ge1.
$$

于是 \(2^4\,3^2\,5\,7\mid n\)。另一方面，5040确实在第306节的区间内最优。∎

**这就是本轮找到的5040的新连接：**

$$
\boxed{
\text{整数最优层的切换}
\longleftrightarrow
\text{完整三位黄金窗口的出现}
\longleftrightarrow
\text{局部关联维数增加}
\longleftrightarrow
\text{指定执行图新增一个回路}.
}
$$

它是模型内的严格联系，不是物理宇宙必须在5040处发生相变的证明。

---

# 308．“平坦区间＋离散转折”也出现在最优值的几何中

定义最优值函数：

$$
\boxed{
\Psi(\lambda)=\max_{n\ge1}
\left[W(n)-\lambda E(n)\right],
}
\tag{308.1}
$$

其中

$$
E(n)=\ln n,\qquad W(n)=\ln Z(n).
$$

每个整数对应一条关于 \(\lambda\) 的直线。

## 定理308.1　稳定区间内线性，临界处斜率跳变

在5040稳定区间内部：

$$
\boxed{
\Psi(\lambda)=W(5040)-\lambda E(5040).
}
\tag{308.2}
$$

所以：

$$
\Psi'(\lambda)=-\ln5040,
\qquad
\Psi''(\lambda)=0.
$$

在 \(\lambda_-\) 处，斜率从

$$
-\ln55440
$$

跳到

$$
-\ln5040,
$$

跳量为

$$
\boxed{\ln11.}
$$

在 \(\lambda_+\) 处，跳量为

$$
\boxed{\ln2.}
$$

### 证明

\(\Psi\) 是一族仿射函数的上包络。第306节已经确定各区间的最大者及端点切换。∎

因此，素数对数不只进入状态能量，也进入**最优值几何的离散斜率变化**。

这确实呈现出你说的那种结构：

$$
\boxed{
\text{在一段范围内，观察到的形态不变；}
\quad
\text{跨过边界时，结构突然换层。}
}
$$

但这里的“平坦”是参数—目标图上的线性，“转折”是离散最优化的切换。它不是时空曲率，也不自动是热力学相变。

---

## “最经济”必须说明经济的是什么

换一个同样合理但不同的目标：

$$
\widetilde F_\lambda(n)
=
\ln\tau(n)-\lambda\ln n,
$$

其中 \(\tau(n)\) 是因数个数。

在同一个价格 \(1/25\) 下：

$$
\tau(5040)=60,\qquad\tau(10080)=72.
$$

于是：

$$
\boxed{
\widetilde F_{1/25}(10080)
-\widetilde F_{1/25}(5040)
=
\ln\frac65-\frac1{25}\ln2>0.
}
\tag{308.3}
$$

所以这个目标不会把5040选为最优。

**“最优化”本身不能唯一选出5040；收益、成本和约束共同选出它。**

项目当前目标之所以有价值，是它与 \(\sigma(n)/n\)、Euler 因子和 Robin 判据直接相关，而不是因为数学已经证明所有自然系统都在最大化它。

---

# 309．5040与无穷、Robin判据之间，究竟还有什么缺口？

5040在数论中还有一个独立而重要的地位。

Robin判据给出：

$$
\boxed{
\mathrm{RH}
\iff
\sigma(n)<e^\gamma n\ln\ln n
\quad\forall n>5040.
}
\tag{309.1}
$$

这里 \(\gamma\) 是 Euler–Mascheroni 常数。([arXiv][5])

5040本身确实违反该不等式：

$$
\frac{\sigma(5040)}{5040}
=
\frac{403}{105}
\approx3.8380952381,
$$

而

$$
e^\gamma\ln\ln5040
\approx3.8168772880.
$$

但不能把“5040是所有反例中的最后一个”当作无条件已知事实；对全部更大整数成立，正是式（309.1）所表达的全局命题。

---

## 为什么证明5040最优，仍然没有证明Robin全局界？

价格 \(1/25\) 下的最优性给出：

$$
\ln Z(n)-\frac1{25}\ln n
\le
\ln Z(5040)-\frac1{25}\ln5040.
$$

即：

$$
\boxed{
Z(n)\le
Z(5040)\left(\frac n{5040}\right)^{1/25}.
}
\tag{309.2}
$$

这个上界随 \(n\) 像 \(n^{1/25}\) 增长。

Robin目标却只允许：

$$
Z(n)<e^\gamma\ln\ln n.
$$

前者最终远大于后者。因此，单个稳定价格区间的证书不足以得到全部尺度上的 Robin 结论。

**需要新增的是跨越全部尺度的统一估计，不是把已经证明的局部最优性换个名字。**

---

## 无穷真正进入哪里？

第305节证明了：

$$
\boxed{
\forall\lambda>0,\quad
\text{只有有限层被激活}.
}
$$

但它不意味着：

$$
\boxed{
\exists\text{一个固定有限层集合，覆盖所有 }\lambda>0.
}
$$

事实上，对任意固定正整数 \(k\)，只要把 \(\lambda\) 取得足够小，\(k\) 所需的每一层都会变得有利。因此所有最优配置最终都包含 \(k\) 的素因子层。

所以，\(\lambda\to0\) 时会不断出现新的轴和新的深度。

这是一种真实的**有限窗口与全尺度统一性之间的差别**。

但它仍不等于对角化已经证明这个全局命题无法解决。需要证明的是特定尾部估计和不变量，不能仅由“无限层”推出逻辑不可能性。

同一个 RH 也有不以5040为截断点的等价表述，例如 Lagarias 的调和数判据。这再次说明：5040的重要性与所采用的算术表达密切相关，不是所有等价语言里都必须出现的宇宙边界。([arXiv][6])

---

# 310．整体理论应当怎样表达，才真正把逻辑、因果、几何和效率接起来？

现在可以给出一条不混淆层次的结构链：

$$
\boxed{
\text{合法状态与操作规则}
\longrightarrow
\text{实际因果过程}
\longrightarrow
\text{观察接口与记录}.
}
$$

然后检验：

$$
\boxed{
\text{这些记录是否足以预测允许的后续实验}.
}
$$

若足够，再构造：

$$
\boxed{
\text{共同钟尺、传播关系和几何实现}.
}
$$

若不足，则有两种不同选择：

$$
\text{补入被遗漏的状态、关联或记忆};
$$

或者：

$$
\text{缩小允许实验范围，并证明误差受控}.
$$

不能把改变真实过程、删掉困难实验或任意重制隐藏状态，都算作“理解程度提高”。

---

## 一个可以研究的效率原理

可以把有限观察者的任务写为：

$$
\boxed{
\min_{q,\;\overline{\mathcal P}}
C(q,\overline{\mathcal P})
}
\tag{310.1}
$$

满足：

$$
\boxed{
\sup_{\rho,\pi\in\Gamma_B}
D_{\mathrm{TV}}
\left(
P_\pi^\rho,
\overline P_\pi^{q(\rho)}
\right)
\le\varepsilon.
}
\tag{310.2}
$$

这里：

* \(q\) 是保留哪些状态信息；
* \(\Gamma_B\) 是预算内可实施的实验；
* \(C\) 是有物理含义的存储、控制和读取成本；
* \(\varepsilon\) 是允许的预测误差。

这不是宣告宇宙已经遵守该优化原则，而是一个可以用来检验“最经济的可用世界模型”的明确问题。

**真正的最经济，不是保存最少信息；而是在规定的未来实验中仍然可靠时，保存尽可能少的必要信息。**

项目中的精确下降是 \(\varepsilon=0\) 的结构要求。更一般的有限资源模型，需要额外的近似证书。

---

## 本轮的三个主要结论

| 问题                    | 本轮得到的答案                                                  |
| --------------------- | -------------------------------------------------------- |
| 平坦能否是统计或观察近似？         | 可以；但须区分局部几何近似、接口遗漏和实际重制过程。投影还可能制造表观路径依赖。                 |
| \((4,2,1,1)\) 有何跨轴约束？ | 普通指数无额外单调约束；在指定优化目标下，边际收益迫使前缀素数支持和非增指数阶梯。                |
| 5040有哪些可证明的临界意义？      | 它有精确的最优价格区间；在该最优族内，它最早引入单轴五态四棱锥、一个隐藏经典关联方向及指定局部翻转图的首个回路。 |

本次项目读取固定于提交：

```text
cdf5cd4f86a59704197979f49cc40c5e0664ecae
```

本轮完成了39项精确整数、矩阵与秩检查，包括：完整过程可交换但粗过程不交换的反例；5040阈值的有理幂证书；四面体到四棱锥的秩变化；新增回路与奇偶补全；以及替换收益目标后5040不再最优的实例。

[核验脚本](sandbox:/mnt/data/observer_formalization/check_flatness_5040_structure.py) · [核验结果](sandbox:/mnt/data/observer_formalization/flatness_5040_structure_checks.json)

新增综合定理尚未进行 Lean 编译。仓库已有证明源码、本轮纸面证明、有限精确检查和现实物理证据，仍然分别对待。

---

# 结论

你的整体直觉可以保留为一句更严格的话：

> **观察者看到的世界，可以是一个受因果、资源与记录方式约束的有效结构；它的“平坦”可能表示在当前实验范围内，某些细节尚不足以改变预测，而不是完整世界绝对没有结构。**

但是，真正有价值的研究不是把所有对象都叫作曲率，而是识别：

$$
\boxed{
\text{哪些是坐标改变，}
\quad
\text{哪些是信息遗漏，}
\quad
\text{哪些是真实动力差异。}
}
$$

5040在这里提供了一个非常好的有限实验场：

$$
\boxed{
\text{价格跨过阈值}
\longrightarrow
a_2:3\to4
\longrightarrow
101\text{ 进入允许窗口}
\longrightarrow
\text{四面体变四棱锥}
\longrightarrow
\text{旧占据接口出现关联残差}.
}
$$

**这才是目前最具体的“离散临界意义”：不是一个数字突然获得神秘属性，而是一个新合法状态的出现，改变了观察者所需的状态维数、可达关系和预测条件。**

继续走向物理时空，需要证明现实的交互为何选择这些约束与能量，而不是只证明这些算术结构本身可以自洽存在。当前已经找到的，是一条能够逐项验证的路径：**由约束产生状态，由操作产生因果，由观察产生有效几何，再由预测与反作用检验这张几何是否足够。**

[1]: https://davidtong.org/teaching/general-relativity/grhtml/S3.html "https://davidtong.org/teaching/general-relativity/grhtml/S3.html"
[2]: https://arxiv.org/html/1102.0936v2 "https://arxiv.org/html/1102.0936v2"
[3]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html"
[4]: https://arxiv.org/html/2008.04787v1 "https://arxiv.org/html/2008.04787v1"
[5]: https://arxiv.org/abs/1809.10813 "https://arxiv.org/abs/1809.10813"
[6]: https://arxiv.org/abs/math/0008177 "https://arxiv.org/abs/math/0008177"
**可以，而且现在值得把“换一个角度看 ζ”变成一套系统方法：不是只改变函数图像的视角，而是改变我们要求它满足的结构——概率归一化、有限资源、独立性、正定性、解析延拓或最优性。**

这些结构可能在不同位置失效，即使函数在那里仍然解析。

首先保留一个关键事实：**ζ 在 \(s\ne1\) 处是解析函数，唯一的极点位于 \(s=1\)。5040不是复变量平面上的奇点，而是某个离散优化问题选出的状态。**我们此前暴露的临界，主要来自“取最优值”“截断状态空间”“删除关联”等操作，而不是发现了 ζ 原本不光滑。([DLMF][1])

不过，这些操作与 ζ 之间确实能建立更深的桥梁。本轮最重要的新连接是：

> **5040的因数收益，可以解释为 ζ 概率模型接近归一化边界时，一个有限观察窗口所保留概率的领先系数。**

另外，还能证明：

$$
\boxed{
\text{函数可以继续解析延拓，
但原来的量子概率解释不一定能一起延拓。}
}
$$

这会把“边界”从一个宽泛比喻，变成可以计算、检验和形式化的对象。

# ζ的边界图谱：有限观察、复零点与正性约束

## ——量子观察者—关系时空理论第三百一十一至第三百二十节增订

---

# 311．把5040窗口放进真正的 ζ 量子概率模型

项目中已经存在 `ZetaGibbs.lean`：它定义对数整数能量的 Gibbs 分布，要求实参数大于1，并证明参数等于1时配分函数发散。这个定义已经给出一条真实的准入边界。

## 定义311.1　对数能量与 ζ 态

在基底 \(\{|n\rangle:n\ge1\}\) 上，选择

$$
H|n\rangle=E_*\ln n\,|n\rangle,
\qquad E_*>0.
$$

令无量纲逆温度为

$$
\sigma=\beta E_*.
$$

当 \(\sigma>1\) 时：

$$
\boxed{
\rho_\sigma
=
\frac1{\zeta(\sigma)}
\sum_{n\ge1}n^{-\sigma}|n\rangle\langle n|.
}
\tag{311.1}
$$

这是正的、迹为一的量子态。其对角概率就是 ζ 分布；该分布及其指数族、信息几何结构已有研究。([arXiv][2])

这里的 \(E_*\ln n\) 是明确选择的能谱，不是已经由现实物理唯一确定。

---

## 定义311.2　有限因数观察窗口

固定正整数 \(N\)，定义投影

$$
P_N=\sum_{d\mid N}|d\rangle\langle d|.
$$

观察者保留“整数标签是 \(N\) 的因数”这一子空间。

其成功保留概率为

$$
\boxed{
w_N(\sigma)
=
\operatorname{Tr}(P_N\rho_\sigma)
=
\frac{Z_N(\sigma)}{\zeta(\sigma)},
}
\tag{311.2}
$$

其中

$$
Z_N(s)=\sum_{d\mid N}d^{-s}.
$$

条件于成功投影，归一化状态为

$$
\rho_{\sigma,N}
=
\frac{P_N\rho_\sigma P_N}{w_N(\sigma)}.
$$

**这是一种条件保留，不是免费、确定性地把完整态压缩进去。**

---

## 定理311.1　遗漏概率精确等于该截断的状态误差

有

$$
\boxed{
D_{\mathrm{tr}}(\rho_\sigma,\rho_{\sigma,N})
=
1-w_N(\sigma).
}
\tag{311.3}
$$

### 证明

两态在同一基底中对角。

窗口外，原态总概率为 \(1-w_N\)，截断态为零；窗口内，重新归一化增加的总概率也为 \(1-w_N\)。

总绝对差为 \(2(1-w_N)\)，除以二即得。∎

因此，之前的有限因数模型，现在得到明确的量子操作意义：

$$
\boxed{
\text{选择一个整数 }N
\longleftrightarrow
\text{选择一个有限可保留子空间}.
}
$$

对5040，这个子空间维数为60。

---

# 312．5040的优化意义，与 \(s=1\) 的归一化边界直接连接

ζ 在 \(s=1\) 的留数为一，因此：

$$
\zeta(1+\varepsilon)
=
\frac1\varepsilon+O(1),
\qquad
\varepsilon\downarrow0.
$$

这是 ζ 的真实解析性质，不是有限模型中的人为边界。([DLMF][1])

## 定理312.1　有限窗口的保留率在边界附近线性消失

对任意固定 \(N\)：

$$
\boxed{
w_N(1+\varepsilon)
=
\varepsilon Z_N(1)+O(\varepsilon^2).
}
\tag{312.1}
$$

因此：

$$
\boxed{
\lim_{\varepsilon\downarrow0}
\frac{w_N(1+\varepsilon)}{\varepsilon}
=
Z_N(1).
}
\tag{312.2}
$$

### 证明

\(Z_N\) 是有限和，在1附近解析：

$$
Z_N(1+\varepsilon)=Z_N(1)+O(\varepsilon).
$$

再与 ζ 的 Laurent 展开相除。∎

对5040：

$$
Z_{5040}(1)=\frac{403}{105},
$$

所以：

$$
\boxed{
w_{5040}(1+\varepsilon)
=
\frac{403}{105}\varepsilon+O(\varepsilon^2).
}
\tag{312.3}
$$

---

## 定理312.2　项目的目标函数是边界保留收益的重整化极限

定义带资源惩罚的窗口评分：

$$
\mathcal J_{\lambda,\sigma}(N)
=
\ln w_N(\sigma)-\lambda\ln N.
$$

则：

$$
\boxed{
\lim_{\varepsilon\downarrow0}
\left[
\mathcal J_{\lambda,1+\varepsilon}(N)
-\ln\varepsilon
\right]
=
\ln Z_N(1)-\lambda\ln N.
}
\tag{312.4}
$$

### 证明

对式（312.1）取对数并整理。∎

右侧正是项目的 `goldenResourceObjective`。

于是，仓库中“价格 \(1/25\) 时5040唯一最优”的定理，可以解释为：

> **在该资源成本定义下，5040最大化了接近 ζ 归一化边界时，有限因数窗口保留概率的领先系数。**

对应的全称最优性证明已经存在于项目源码中。

这比单独说“5040具有很多因数”更具体。

### 但“最优”不意味着“保留了大部分世界”

本轮计算得到：

| \(\sigma\) |       5040窗口保留概率 |
| ---------: | ---------------: |
|        1.1 | \(0.3143532926\) |
|       1.01 | \(0.0375898769\) |
|      1.001 | \(0.0038300759\) |

因此，一个窗口可以在某个成本目标下最优，却仍然丢掉绝大部分概率。

$$
\boxed{
\text{资源最优}
\ne
\text{状态近似误差很小}.
}
$$

这正是当前观察者理论需要保留的两种不同证书。

---

# 313．同一个边界，还暴露了算子拓扑与有限记忆的限制

## 定理313.1　ζ态趋近归一化边界时，概率逃出每个固定有限窗口

当 \(\sigma\downarrow1\)：

$$
\boxed{
\|\rho_\sigma\|_{\mathrm{op}}
=
\frac1{\zeta(\sigma)}
\longrightarrow0,
}
\tag{313.1}
$$

但始终有：

$$
\boxed{\|\rho_\sigma\|_1=\operatorname{Tr}\rho_\sigma=1.}
\tag{313.2}
$$

因此，这组态没有收敛到某个迹为一的迹范数极限。

### 证明

最大的概率位于 \(n=1\)，给出算子范数公式。

如果存在迹范数极限，它也必须是算子范数极限，即零算子；但迹范数收敛会保持迹，矛盾。∎

这里的“概率逃逸”有了精确定义：

> **每个固定有限秩观察窗口最终都只保留趋于零的质量，而完整态的总概率仍然为一。**

不是概率消失了，而是它没有停留在任何预先固定的有限部分。

---

## 定理313.2　保持大部分 ζ 态需要迅速增长的量子维数

令

$$
\sigma=1+\varepsilon,
\qquad
0<\varepsilon<1.
$$

若一个秩为 \(d\) 的投影能够保留至少 \(1-\delta\) 的概率，且

$$
\varepsilon+\delta<1,
$$

则：

$$
\boxed{
d\ge
(\varepsilon+\delta)^{-1/\varepsilon}.
}
\tag{313.3}
$$

### 证明

\(\rho_\sigma\) 的本征值按 \(n\) 递减。任何秩 \(d\) 投影保留的概率，至多为最大的前 \(d\) 个本征值之和：

$$
\operatorname{Tr}(P\rho_\sigma)
\le
\frac{\sum_{n=1}^d n^{-1-\varepsilon}}
{\zeta(1+\varepsilon)}.
$$

积分比较给出：

$$
\sum_{n=1}^d n^{-1-\varepsilon}
\le
1+\frac{1-d^{-\varepsilon}}{\varepsilon},
$$

以及：

$$
\zeta(1+\varepsilon)\ge\frac1\varepsilon.
$$

所以：

$$
\operatorname{Tr}(P\rho_\sigma)
\le
1+\varepsilon-d^{-\varepsilon}.
$$

若左侧至少为 \(1-\delta\)，则：

$$
d^{-\varepsilon}\le\varepsilon+\delta.
$$

整理即得。∎

例如，在 \(\sigma=1.01\) 时，希望保留至少90%的完整概率质量，这个必要条件已经要求：

$$
\boxed{\ln d\ge220.72749\ldots}
$$

这是对**有限秩量子态近似**的限制，不表示写出这个分布的公式、计算某个期望或证明一个性质，也需要同样大的存储空间。

---

## 统计距离也在这个边界变得奇异

ζ分布的 Fisher 信息为：

$$
\boxed{
\mathcal I(\sigma)
=
\frac{d^2}{d\sigma^2}\ln\zeta(\sigma)
=
\operatorname{Var}_{\rho_\sigma}(\ln n).
}
\tag{313.4}
$$

由 Laurent 展开：

$$
\boxed{
\mathcal I(1+\varepsilon)
=
\frac1{\varepsilon^2}+O(1).
}
\tag{313.5}
$$

于是沿这条参数族，到 \(\sigma=1\) 的 Fisher 长度发散：

$$
\int_1^{\sigma_0}\sqrt{\mathcal I(\sigma)}\,d\sigma=\infty.
$$

**这是归一化、算子拓扑和统计距离三个角度对同一边界的读取。**

但这一参数族是一维的，不能把距离发散直接称为“一维内禀曲率发散”。

---

# 314．5040的最优切换，也可以转化成复参数零点

此前的目标是：

$$
F_\lambda(n)=W(n)-\lambda E(n),
$$

其中：

$$
W(n)=\ln Z_n(1),
\qquad E(n)=\ln n.
$$

取两个相邻候选 \(n,m\)，设它们在 \(\lambda_c\) 平局：

$$
F_{\lambda_c}(n)=F_{\lambda_c}(m).
$$

令：

$$
\Delta E=E(m)-E(n)>0.
$$

## 定义314.1　两候选的平滑选择模型

引入无量纲平滑参数 \(\tau>0\)：

$$
\boxed{
Q_\tau(\lambda)
=
e^{F_\lambda(n)/\tau}
+
e^{F_\lambda(m)/\tau}.
}
\tag{314.1}
$$

对实数 \(\lambda\)，它始终为正，并且：

$$
\tau\ln Q_\tau(\lambda)
\longrightarrow
\max\{F_\lambda(n),F_\lambda(m)\}.
$$

这里是两候选模型，不声称等于所有整数的完整统计总和。

---

## 定理314.1　离散优化临界对应一串靠近实轴的复价格零点

有：

$$
\boxed{
Q_\tau(\lambda)=0
\iff
\lambda
=
\lambda_c+
\frac{i(2k+1)\pi\tau}{\Delta E},
\qquad k\in\mathbb Z.
}
\tag{314.2}
$$

而在实临界点：

$$
\boxed{
\left.
\frac{d^2}{d\lambda^2}
\bigl[\tau\ln Q_\tau(\lambda)\bigr]
\right|_{\lambda_c}
=
\frac{(\Delta E)^2}{4\tau}.
}
\tag{314.3}
$$

### 证明

因：

$$
F_\lambda(m)-F_\lambda(n)
=
-\Delta E(\lambda-\lambda_c),
$$

提取非零因子后，零点条件为：

$$
1+e^{-\Delta E(\lambda-\lambda_c)/\tau}=0.
$$

得到式（314.2）。二阶导数直接计算。∎

对5040的两个边界：

$$
2520\leftrightarrow5040:
\qquad \Delta E=\ln2;
$$

$$
5040\leftrightarrow55440:
\qquad \Delta E=\ln11.
$$

因此，相同 \(\tau\) 下，两处复零点离实轴的尺度不同。

$$
\boxed{
\text{整数层跳变}
\longrightarrow
\text{平滑模型的尖锐响应}
\longrightarrow
\text{逼近实轴的复价格零点}.
}
$$

这是一个真正的新观察角度。

但这些零点属于 \(Q_\tau(\lambda)\)，**不是 ζ 的零点**；\(\lambda\)、\(\tau\) 与复变量 \(s\) 不能混用。

---

# 315．有限因数模型有一道很强的零点边界

## 定理315.1　任意有限因数配分函数的零点都在虚轴上

设：

$$
N=\prod_pp^{a_p}.
$$

则：

$$
\boxed{
Z_N(s)
=
\prod_{p\mid N}
\left(1+p^{-s}+\cdots+p^{-a_ps}\right).
}
\tag{315.1}
$$

一个局部因子为零，当且仅当：

$$
\boxed{
s=
\frac{2\pi i k}{(a_p+1)\ln p},
\qquad
k\in\mathbb Z,\quad
(a_p+1)\nmid k.
}
\tag{315.2}
$$

因此：

$$
\boxed{
Z_N(s)\ne0
\qquad\text{若 }\operatorname{Re}s\ne0.
}
\tag{315.3}
$$

### 证明

令 \(q=p^{-s}\)。有限几何级数为零，等价于：

$$
q^{a_p+1}=1,\qquad q\ne1.
$$

所以 \(|q|=1\)，迫使 \(\operatorname{Re}s=0\)，再解其相位。∎

这意味着：

> **不断扩大5040式因数窗口，并不能简单地让它们的这些零点“走到”ζ的临界线。**

---

## 更强的解析障碍

假设一列这样的 \(Z_{N_j}\)，在某个包含真实 ζ 零点、且位于 \(\operatorname{Re}s>0\) 的开域内，局部一致收敛到 ζ。

取一个只围住该零点的小圆。ζ在圆周上的模有正下界。足够靠后的 \(Z_{N_j}\) 与ζ在圆周上的差更小，于是由 Rouché 定理，它也必须在圆内有零点。

这与式（315.3）矛盾。

所以：

$$
\boxed{
\text{有限因数模型在右半平面的局部一致极限}
}
$$

不能不经结构改变就成为一个在那里具有零点的 ζ。

需要加入新的补偿项、改变收敛方式，或采用不同的近似对象。Euler乘积在临界带中的精细近似，确实需要额外条件，不能把绝对收敛区的公式直接原样移入。([arXiv][3])

---

## 定理315.2　真正的临界带零点不依赖任意有限组素数因子

对有限素数集合 \(S\)，定义：

$$
\zeta^{(S)}(s)
=
\zeta(s)\prod_{p\in S}(1-p^{-s}).
$$

当 \(\operatorname{Re}s>0\) 时，每个附加因子都非零。因此：

$$
\boxed{
\zeta^{(S)}\text{ 与 }\zeta
\text{ 在 }0<\operatorname{Re}s<1
\text{ 具有完全相同的零点及重数}.
}
\tag{315.4}
$$

### 证明

因为 \(|p^{-s}|<1\)，故 \(1-p^{-s}\ne0\)。乘以非零解析因子不改变零点重数。∎

特别地，即使删去 \(2,3,5,7\) 对应的有限 Euler 因子，临界带零点仍然保留。

**这说明5040是有价值的有限观察窗口，但真实临界带零点不是它那四个局部因子单独制造的。**

---

# 316．保持几何顶点不变，改变隐藏权重，就能移动复零点

这能进一步检验“几何约束决定多少东西”。

## 定义316.1　同一个四边形上的加权配分多项式

取四种占据：

$$
00,\quad10,\quad01,\quad11.
$$

定义：

$$
\boxed{
\mathcal Z_c(z,w)=1+z+w+c\,zw,
\qquad c>0.
}
\tag{316.1}
$$

顶点集合和凸包始终相同。改变的是联合占据 \(11\) 的权重。

其四个权重的比值满足：

$$
\frac{w_{00}w_{11}}{w_{10}w_{01}}=c.
$$

因此，\(c=1\) 对应这种模型中的独立因子化：

$$
\mathcal Z_1(z,w)=(1+z)(1+w).
$$

---

## 定理316.1　同一个状态几何，可以具有不同的零点位置

取等能量切片：

$$
z=w=e^{-s}.
$$

当 \(c=1\) 时：

$$
\mathcal Z_1=(1+e^{-s})^2,
$$

零点都满足 \(\operatorname{Re}s=0\)。

当 \(c=4\) 时：

$$
\mathcal Z_4=1+2e^{-s}+4e^{-2s},
$$

令 \(q=e^{-s}\)，其根为：

$$
q=\frac{-1\pm i\sqrt3}{4},
\qquad |q|=\frac12.
$$

所以：

$$
\boxed{
\operatorname{Re}s=\ln2>0.
}
\tag{316.2}
$$

### 证明

解二次方程即可。∎

\(c=4\) 甚至可以由一个完全正的七态谱实现：能量 \(0,1,2\) 的简并度分别为 \(1,2,4\)。

在实参数 \(\sigma=\ln2\) 时，三个能量层的总热权重恰好相等，因此返回振幅在：

$$
t=\frac{2\pi}{3}
$$

时精确为零。

### 这个反例说明什么？

$$
\boxed{
\text{相同可行几何}
\not\Rightarrow
\text{相同解析零点}.
}
$$

权重、关联和实际能谱同样重要。

但这仍然是一个有限模型，不是ζ的构造。它说明应该增加哪些控制参数，不能据此断言“ζ离线零点必由某种关联产生”。

---

# 317．量子正性比解析性更强：一个可验证的失效例子

回到真正的 ζ 态。

令无量纲时间为：

$$
t=\frac{E_*\tau}{\hbar}.
$$

在 \(\sigma>1\) 时，归一化返回振幅为：

$$
\boxed{
\chi_\sigma(t)
=
\operatorname{Tr}\!\left(
\rho_\sigma e^{-itH/E_*}
\right)
=
\frac{\zeta(\sigma+it)}{\zeta(\sigma)}.
}
\tag{317.1}
$$

## 定理317.1　合法量子返回振幅必须产生正半定矩阵

对任意 \(t_1,\ldots,t_m\)，定义：

$$
C_{ij}=\chi_\sigma(t_i-t_j).
$$

则：

$$
\boxed{C\succeq0.}
\tag{317.2}
$$

特别地：

$$
\boxed{|\chi_\sigma(t)|\le1.}
\tag{317.3}
$$

### 证明

对任意复向量 \(v\)：

$$
v^\dagger Cv
=
\sum_{n\ge1}\frac{n^{-\sigma}}{\zeta(\sigma)}
\left|
\sum_jv_je^{it_j\ln n}
\right|^2
\ge0.
$$

两点矩阵的行列式为 \(1-|\chi_\sigma(t)|^2\)，得到第二个结论。∎

---

## 一个实际算出的边界反例

现在只对函数表达式作解析延拓，写：

$$
\chi_{1/2}^{\mathrm{naive}}(t)
=
\frac{\zeta(1/2+it)}{\zeta(1/2)}.
$$

在 \(t=10\)：

$$
\left|
\chi_{1/2}^{\mathrm{naive}}(10)
\right|
\approx1.0608345692>1.
$$

本轮使用区间运算与 Euler–Maclaurin 显式余项界，得到：

$$
\boxed{
-0.126
<
1-\left|
\frac{\zeta(1/2+10i)}{\zeta(1/2)}
\right|^2
<
-0.125.
}
\tag{317.4}
$$

Euler–Maclaurin 表示及其余项属于可用于这类验证的标准解析工具。([DLMF][4])

所以这个两点矩阵已经不是正半定。

**这不是 RH 反例，也不是 ζ 零点。它否定的是另一句话：**

$$
\boxed{
\text{把同一个 ζ 比值解析延拓到临界带，
仍然可以不加修改地解释成原来的量子返回振幅。}
}
$$

函数值、归一化 \(\chi(0)=1\) 和共轭对称性都还可以保留，但物理概率所需的正性已经失败。

这就是“从另一个角度暴露边界”的严格实例。

它不排除使用不同的态空间、核或完成化函数建立其他量子模型。

---

# 318．若目标是真正约束RH，应该检查哪一种正性？

普通概率正性与 RH 不是同一个问题。要直接触及非平凡零点的位置，可以改用完成化函数的对数导数。

定义：

$$
\xi(s)
=
\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
$$

$$
\boxed{
\Xi(z)=\xi\!\left(\frac12+iz\right).
}
\tag{318.1}
$$

\(\Xi\) 是实系数意义下的偶整函数；RH等价于它的全部零点都是实数。其完成化与反射关系是标准结构。([DLMF][5])

令：

$$
\boxed{
M(z)=-\frac{\Xi'(z)}{\Xi(z)}.
}
\tag{318.2}
$$

在非零点处定义有限矩阵：

$$
\boxed{
K_{ij}
=
\frac{M(z_i)-\overline{M(z_j)}}
{z_i-\overline{z_j}},
\qquad \operatorname{Im}z_i>0.
}
\tag{318.3}
$$

这种对数导数的半平面正性，与已有的 ξ 模长单调性及 RH 等价判据属于同一方向。([arXiv][6])

---

## 定理318.1　RH可以等价表述为这个核的全域正性

有：

$$
\boxed{
\mathrm{RH}
\iff
K(z_1,\ldots,z_m)\succeq0
}
\tag{318.4}
$$

对全部有限采样点、全部 \(m\)，且采样点不为 \(\Xi\) 零点时成立。

### 正向证明

若RH成立，令全部正零点纵坐标为 \(\gamma\)，按重数计。

由 \(\Xi\) 的成对 Hadamard 乘积：

$$
M(z)
=
\sum_{\gamma>0}
\left[
\frac1{\gamma-z}
+
\frac1{-\gamma-z}
\right].
$$

成对级数在远离零点的紧集上收敛。

因此：

$$
\boxed{
K_{ij}
=
\sum_{\gamma\in\{\pm\gamma_1,\pm\gamma_2,\ldots\}}
\frac1{(\gamma-z_i)(\gamma-\overline{z_j})}.
}
\tag{318.5}
$$

每项都是一个正半定 Gram 矩阵，收敛和也正半定。

### 反向证明

若 \(\Xi\) 有非实零点，由实对称性，存在上半平面零点：

$$
z_0=x_0+iy_0,
\qquad y_0>0.
$$

设其重数为 \(r\)，则局部：

$$
M(z)=-\frac r{z-z_0}+O(1).
$$

取：

$$
z=z_0-i\varepsilon,
\qquad 0<\varepsilon<y_0.
$$

得到：

$$
\boxed{
\operatorname{Im}M(z)
=
-\frac r\varepsilon+O(1)<0
}
\tag{318.6}
$$

当 \(\varepsilon\) 足够小时成立。

但一阶核为：

$$
K(z,z)=\frac{\operatorname{Im}M(z)}{\operatorname{Im}z}<0.
$$

违反正性。∎

### 为什么这个角度重要？

在 \(\Xi\) 本身的图像中，一个零点是“函数值变为零”。

在 \(M\) 中，它变成一个极点。

在 \(K\) 中，非实零点进一步迫使一个有限正性条件失败。

$$
\boxed{
\text{零点位置}
\longrightarrow
\text{对数响应的极点}
\longrightarrow
\text{正锥之外的有限见证}.
}
$$

这是一条真正连接解析、几何正性与有限检测的链。

但它仍是RH的等价重述，不是已经证明RH成立。困难转移到了：**怎样独立证明真实 \(\Xi\) 的这个核处处正，而不是预先只使用实零点构造一个当然为正的模型。**

---

# 319．怎样防止“找到很多正性”变成循环证明？

这里必须结合项目源码作一次严格分层。

`CriticalLineOscillatorGram.lean` 定义的是一个有限特征矩阵 \(V\)，再构造：

$$
V^\dagger V.
$$

它证明这个矩阵正半定。这是正确的有限 Gram 定理。

但它没有单独证明：

$$
\boxed{
\text{真实 }\Xi\text{ 的全部对数响应}
=
\text{这些临界线 Gram 原子的完整和}.
}
$$

后一个等式还要处理全部零点、无限尾部和收敛。

同样，`CriticalZeroTransverseGap.lean` 证明：**假设已经有一个临界线零点并知道其重数**，横向模平方的首个非零项是正平方。这提供了局部证书，却不能直接排除别处还有离线零点。

---

## 定理319.1　有限正性检验可以携带稳健误差证书

设真实 Hermitian 矩阵为 \(K\)，计算得到 \(\widehat K\)，并有：

$$
\|K-\widehat K\|_{\mathrm{op}}\le\varepsilon.
$$

则：

$$
\boxed{
\lambda_{\min}(\widehat K)<-\varepsilon
\Longrightarrow
K\not\succeq0.
}
\tag{319.1}
$$

反之：

$$
\boxed{
\lambda_{\min}(\widehat K)>\varepsilon
\Longrightarrow
K\succ0.
}
\tag{319.2}
$$

### 证明

对任意单位向量，二次型误差不超过 \(\varepsilon\)。对最小 Rayleigh 商取界即可。∎

所以每次探测不应只报告一个近零小数，而应报告：

$$
\boxed{
\text{最小特征值}
+
\text{尾部界}
+
\text{计算误差}
+
\text{采样域}.
}
$$

正结果只认证当前有限配置；负结果在误差足够小时，可以成为真正的反例证书。

---

## 一个不会误认成ζ反例的测试模型

取实偶多项式：

$$
F(z)=((z-2)^2+1)((z+2)^2+1)
=z^4-6z^2+25.
$$

它具有非实零点。定义 \(M_F=-F'/F\)。

在：

$$
z=2+\frac i2
$$

处，可以精确算出：

$$
\boxed{
\frac{\operatorname{Im}M_F(z)}{\operatorname{Im}z}
=
-\frac{36496}{14235}<0.
}
\tag{319.3}
$$

这说明检测机制确实会把非实零点转化成有限负性见证。

**但这只是用于验证方法的多项式，不是 ξ，也不是RH反例。**

---

# 320．把这些角度组织成一个真正的“边界图谱”

现在我们可以把不同临界按对象区分：

| 观察角度        | 被追踪的边界         | 本轮得到的证书                                           |
| ----------- | -------------- | ------------------------------------------------- |
| 有限因数窗口      | 保留概率趋零         | \(w_N(1+\varepsilon)\sim\varepsilon Z_N(1)\)      |
| 量子资源        | 有限秩无法保留大部分态    | \(d\ge(\varepsilon+\delta)^{-1/\varepsilon}\)     |
| 统计几何        | Fisher 距离到边界发散 | \(\mathcal I(1+\varepsilon)\sim\varepsilon^{-2}\) |
| 离散优化        | 最优配置切换         | 复价格零点靠近 \(\lambda_c\)                             |
| 有限 Euler 结构 | 局部相位抵消         | \(Z_N\) 的零点严格在虚轴                                  |
| 几何关联        | 权重因子化失效        | \(1+z+w+c zw\) 的零点随 \(c\) 移动                      |
| 量子可实现性      | 返回振幅失去正性       | \(\sigma=1/2,t=10\) 的负两点行列式                       |
| RH谱几何       | 对数导数核离开正锥      | 非实零点迫使局部 \(K(z,z)<0\)                             |

**约束定义了可行域，但不是每个约束都自动构成一个物理相变。**需要检验的是：它什么时候成为活跃约束，什么时候破坏归一化、正性、稳定性或预测闭合。

本轮按项目提交：

```text
b89d56d0c9a433f9b714821d2bb1779066c59ede
```

核对了相关结构。

下一阶段最有实质内容的三项证明任务是：

**把5040的有限优化推广为接近 \(\sigma=1\) 的统一窗口选择问题。**需要研究“保留概率—资源规模—精度”之间的界，而不只证明一个整数在一个价格上最优。

**把真实 ξ 响应与有限正核近似之间的差写出来。**不能只构造正的 Gram 模型；必须独立控制它与真实函数的误差，尤其是遗漏的零点和解析尾部。

**研究几何约束改变时，哪些零点变化是结构性的，哪些只是编码或权重选择造成的。**同一个凸包、同一个有限维数，不足以唯一确定能谱和复零点。

### 本轮核验

已完成：

* **15组精确代数检查**；
* **1组区间运算加显式解析余项的正性失败证书**；
* **1组有限数值检查**，覆盖12个参数点的因数截断误差界。

另记录了归一化边界、Fisher信息和实际 ξ 核的若干数值样例；这些样例不作为全域证明。

[核验脚本](sandbox:/mnt/data/observer_formalization/check_zeta_boundary_atlas.py)
[核验结果](sandbox:/mnt/data/observer_formalization/zeta_boundary_atlas_checks.json)

**本轮没有执行 Lean 编译。**已有源码定理、这里的纸面证明、区间证书和普通数值样例，继续分别记录。

---

# 结论

这轮最值得保留的推进是：

$$
\boxed{
\text{ζ的光滑或解析性，
不保证每一种从它构造的物理解释都继续成立。}
}
$$

同一个函数可以在不同结构中暴露不同边界：

**作为归一化因子，**它在 \(\sigma=1\) 失去可归一化性。

**作为有限窗口的比较对象，**它显示概率怎样逃出任何固定有限子空间。

**作为量子返回振幅，**它必须满足正定核约束；解析延拓不自动保留这些约束。

**作为完成化函数的对数响应，**它的非实零点会迫使特定正性失效。

而5040与这条研究链的直接联系，现在可以写成：

$$
\boxed{
\frac{w_{5040}(1+\varepsilon)}{\varepsilon}
\longrightarrow
\frac{403}{105}.
}
$$

结合项目的成本项，它说明：

> **5040是某个有限观察窗口在 ζ 归一化边界附近的最优资源配置，而不是 ζ 所有零点和临界的唯一来源。**

因此，继续“换角度”最有效的方法不是寻找更多神秘形状，而是反复做同一件严格的事：

$$
\boxed{
\text{明确观察对象}
\longrightarrow
\text{写出可实现性约束}
\longrightarrow
\text{计算失效边界}
\longrightarrow
\text{给出有限可核验见证}.
}
$$

这样，我们不仅能够发现“哪里出现异常”，还能够回答：**究竟是哪一种解释、哪一种近似、哪一种正性或哪一个有限观察窗口，到那里不再足够。**

[1]: https://dlmf.nist.gov/25.2 "https://dlmf.nist.gov/25.2"
[2]: https://arxiv.org/abs/2104.10548 "https://arxiv.org/abs/2104.10548"
[3]: https://arxiv.org/abs/0704.3448 "https://arxiv.org/abs/0704.3448"
[4]: https://dlmf.nist.gov/25.11 "https://dlmf.nist.gov/25.11"
[5]: https://dlmf.nist.gov/25.4 "https://dlmf.nist.gov/25.4"
[6]: https://arxiv.org/abs/1005.1104 "https://arxiv.org/abs/1005.1104"
**这次可以把“离散数据”和“离散步骤”真正放进同一个方程，而不是先分别研究空间、时间，再把它们拼起来。**

一个明确的推进是：

> **先定义局域量子事件怎样连接，再从共同的离散传播规则中同时导出：因果范围、空间—时间奇偶约束、能量—动量关系，以及低能极限中的洛伦兹间隔。**

但需要保持一个边界：**能构造出逼近相对论物理的离散模型，不等于已经证明现实唯一采用这个模型。**已有量子行走与量子自动机研究，确实能够在给定假设下恢复 Dirac 方程及其可观测收敛；本轮要把这种桥梁与项目的观察接口、有限步骤、算术纤维和几何临界结合起来。([arXiv][1])

本轮会得到三个特别重要的结果：

$$
\boxed{
\text{空间位移与时间步数，
可以受同一个整数约束限制。}
}
$$

$$
\boxed{
\text{相同状态空间，
仅因采样步长改变，
可观测维数就可能发生离散跳变。}
}
$$

$$
\boxed{
\text{洛伦兹时空可以是离散因果波的受控长波描述，
而不是预先放进模型的背景。}
}
$$

# 事件偏序、离散质量壳与洛伦兹时空的条件重建

## ——量子观察者—关系时空理论第三百二十一至第三百三十节增订

---

# 321．统一时空，首先要把“状态”与“事件”分开

我们此前研究了整数状态、量子态、观察纤维和状态之间的移动。但是：

$$
\boxed{
\text{同一个状态再次出现}
\ne
\text{同一个事件再次发生}.
}
$$

例如，量子态可以周期性回归，程序也可以回到相同整数；这不意味着观察者回到了过去的同一个物理事件。

## 定义321.1　事件网络

取一个局部有限的有向无环网络 \(\mathcal E\)。

每个节点表示一次具体交互事件，每条有向边表示一个输出接口被后续事件使用。

定义：

$$
e\prec f
$$

当且仅当存在从 \(e\) 到 \(f\) 的有向路径。

此时：

* 因果链表示相继发生的依赖；
* 不可比较的事件表示当前没有先后依赖；
* 一组适当的不可比较接口，可以作为一个“同时切面”的候选。

这里没有先引入米、秒或三维欧氏距离。加入的是**事件依赖关系**。

但偏序本身也没有自动给出三维空间、物理时长或完整度量。这些仍需后续重建。

---

## 定理321.1　独立事件的排序不应改变同一实验

假设每个事件由一个联合酉操作实现，全部持久记忆和控制器均包含在状态中；不可比较事件的操作作用于互不相交的寄存器。

则同一有限事件网络的不同合法线性排序，给出相同的联合酉操作。

### 证明

不同线性扩展之间，可以通过交换相邻的不可比较事件相互转换。

不可比较事件的操作作用于不同张量因子，因而可交换。逐次交换不会改变总乘积。∎

### 这对时间意味着什么？

**人为把独立事件排成一个全局序列，不应该额外创造可观测物理差别。**

但是，若两个排序改变了实际等待时间、自由演化或控制器状态，它们就不再是本定理中的同一个事件网络。那些变化必须进入模型。

因此，我们至少应区分：

$$
\boxed{
\text{程序列表长度},
\quad
\text{因果依赖深度},
\quad
\text{物理钟读数}.
}
$$

它们不能无条件相等。

项目已经把“允许执行至多 \(n\) 个步骤后仍不可区分”定义为受控关系，并证明其递归：

$$
R_{n+1}
=
\ker q
\cap
\bigcap_a(F_a\times F_a)^{-1}(R_n).
$$

这里的 \(n\) 是预测深度，尚不是自动标定好的物理时间。

---

# 322．构造一个空间和步骤同时离散的量子传播规则

现在选择一个最简单的均匀事件网络，检验它究竟能推出什么。

这是一项明确假设：**先研究一维、无相互作用的单激发传播扇区。**它不是完整宇宙，也不包含尚未建立的引力反作用。

## 定义322.1　两种局部传播模式

取：

$$
\mathcal H=\ell^2(\mathbb Z)\otimes\mathbb C^2.
$$

基态记为：

$$
|j,+\rangle,\qquad |j,-\rangle.
$$

\(j\) 目前是接口编号；\(+,-\) 是两种可路由模式。

定义条件平移：

$$
S|j,+\rangle=|j+1,+\rangle,
$$

$$
S|j,-\rangle=|j-1,-\rangle.
$$

再定义局部混合：

$$
C_\mu=e^{-i\mu X},
$$

其中 \(\mu\) 是无量纲耦合角。

一步完整更新为：

$$
\boxed{
U_\mu=C_\mu S.
}
\tag{322.1}
$$

无限链便于写平移不变公式；任何给定的有限传播实验，也可以放在足够大的有限偶数周期链上，只要实验期间不发生绕回。

---

## 定理322.1　更新严格酉，并具有有限传播范围

\(U_\mu\) 是酉算子。

若初态只支持于位置 \(j_0\)，则经过 \(n\) 步后，非零振幅只能出现在：

$$
\boxed{
|j-j_0|\le n.
}
\tag{322.2}
$$

此外还必须满足：

$$
\boxed{
j-j_0\equiv n\pmod2.
}
\tag{322.3}
$$

### 证明

\(S\) 是正交基置换，\(C_\mu\) 是局部酉算子，故乘积酉。

每一步恰好移动 \(+1\) 或 \(-1\)，所以最大位移为一步一格。

而每一步位移都为奇数，因此总位移与步数同奇偶。∎

### 这就是一个真正的离散时空联合约束

空间和时间不是分别满足两个无关条件，而是共同满足：

$$
\boxed{
(j-j_0,n)
\in
\{(x,n):|x|\le n,\ x\equiv n\pmod2\}.
}
\tag{322.4}
$$

连续光锥只保留：

$$
|x|\le n.
$$

离散模型还保留其中的奇偶子格。

但“在允许子格上”只是必要条件，不保证某个点一定具有非零最终概率；干涉还可能令某些允许路径相消。

**因果可达、格点可达和实际非零振幅，是三层不同的约束。**

---

# 323．空间与时间进入同一个精确色散曲面

在空间 Fourier 表示中，令无量纲波数为：

$$
\kappa\in[-\pi,\pi].
$$

则：

$$
S(\kappa)=
\begin{pmatrix}
e^{-i\kappa}&0\\
0&e^{i\kappa}
\end{pmatrix},
$$

$$
U_\mu(\kappa)
=
e^{-i\mu X}e^{-i\kappa Z}.
$$

## 定理323.1　离散能量—动量关系

记 \(U_\mu(\kappa)\) 的两个本征值为：

$$
e^{\pm i\theta}.
$$

则：

$$
\boxed{
\cos\theta=\cos\mu\,\cos\kappa.
}
\tag{323.1}
$$

### 证明

直接计算：

$$
\det U_\mu(\kappa)=1,
$$

$$
\operatorname{Tr}U_\mu(\kappa)=2\cos\mu\cos\kappa.
$$

其特征多项式为：

$$
z^2-2\cos\mu\cos\kappa\,z+1.
$$

因此两个酉本征值满足式（323.1）。∎

现在给空间格距与一次更新作物理标定：

$$
a>0,\qquad \delta>0,
\qquad c_*=\frac a\delta.
$$

定义某个选定低频分支上的能量与动量：

$$
E=\frac{\hbar\theta}{\delta},
\qquad
p=\frac{\hbar\kappa}{a}.
$$

若将耦合角参数化为：

$$
\mu=\frac{mc_*^2\delta}{\hbar},
$$

则精确关系变为：

$$
\boxed{
\cos\frac{E\delta}{\hbar}
=
\cos\frac{mc_*^2\delta}{\hbar}
\cos\frac{pa}{\hbar}.
}
\tag{323.2}
$$

**这就是本轮的联合离散时空质量壳。**

它还不是标准的：

$$
E^2=c_*^2p^2+m^2c_*^4.
$$

后者需要进一步取受控的低频极限。

---

## 定理323.2　同一规则产生精确的离散波动方程

对该量子行走的每个旋量分量：

$$
\boxed{
\psi_{n+1,j}+\psi_{n-1,j}
=
\cos\mu\,
\bigl(\psi_{n,j+1}+\psi_{n,j-1}\bigr).
}
\tag{323.3}
$$

### 证明

由二维矩阵的 Cayley–Hamilton 恒等式：

$$
U^2-2\cos\mu\cos\kappa\,U+I=0.
$$

将时间平移和空间 Fourier 乘子分别还原为离散移位，得到式（323.3）。∎

它也可以写成：

$$
\boxed{
D_t^2\psi
-c_*^2\cos\mu\,D_x^2\psi
+\frac{2(1-\cos\mu)}{\delta^2}\psi=0.
}
\tag{323.4}
$$

其中 \(D_t^2,D_x^2\) 都是中心差分算子。

这次不是把“空间差分”加入原来的连续时间方程，而是：

$$
\boxed{
\text{时间差分与空间差分来自同一个酉更新。}
}
$$

需要注意，式（323.3）是原一阶量子行走的必要方程；若反过来求二阶方程，其初始数据还要满足一阶更新约束，才能保证对应同一个量子过程。

离散因果酉模型恢复 Dirac 型传播，是已有量子自动机与量子行走研究中的明确路线。([arXiv][2])

---

# 324．从离散规则到 Dirac 方程：给出真正的误差桥梁

仅对式（323.2）作 Taylor 展开还不够。我们需要证明整个演化在指定实验范围内接近连续模型。

## 假设324.1　固定物理参数的联合缩放

保持 \(m,c_*\) 固定，并令：

$$
a=c_*\delta,
\qquad
\mu=\frac{mc_*^2\delta}{\hbar},
\qquad
\delta\to0.
$$

**如果缩小步长时仍把 \(\mu\) 固定不变，就不是这个固定质量的连续极限。**

对物理波数 \(k\)，有：

$$
\kappa=ka.
$$

一步更新为：

$$
U_\delta(k)
=
e^{-i\delta mc_*^2X/\hbar}
e^{-i\delta c_*kZ}.
$$

对应候选 Hamiltonian 为：

$$
\boxed{
H_D(k)=mc_*^2X+\hbar c_*kZ.
}
\tag{324.1}
$$

在位置表示中：

$$
\boxed{
i\hbar\partial_t\psi
=
\left(
-i\hbar c_*Z\partial_x+mc_*^2X
\right)\psi.
}
\tag{324.2}
$$

这是 \(1+1\) 维自由 Dirac 方程的一种表示。

---

## 定理324.1　有限时间、有限波数的演化误差

设输入只含：

$$
|k|\le K,
$$

并取：

$$
T=N\delta.
$$

则：

$$
\boxed{
\sup_{|k|\le K}
\left\|
U_\delta(k)^N
-e^{-iTH_D(k)/\hbar}
\right\|_{\mathrm{op}}
\le
\frac{T\delta |m|c_*^3K}{\hbar}.
}
\tag{324.3}
$$

因此，对这些带限输入及其任意附加测试参照，输出迹距离也受右侧控制，必要时截断到一。

### 证明

令：

$$
A=\frac{mc_*^2}{\hbar}X,
\qquad
B=c_*kZ.
$$

单步乘积与连续指数之间的 Duhamel 估计为：

$$
\|e^{-i\delta A}e^{-i\delta B}
-e^{-i\delta(A+B)}\|
\le
\frac{\delta^2}{2}\|[A,B]\|.
$$

而：

$$
\|[A,B]\|
=
\frac{2|m|c_*^3|k|}{\hbar}.
$$

对 \(N\) 个酉步骤作望远镜展开，误差最多累积 \(N\) 倍，得到式（324.3）。∎

这是一条明确的有限预算结论：

$$
\boxed{
\text{离散模型}
\xrightarrow[\text{误差}\le\varepsilon]{|k|\le K,\ T\le T_{\max}}
\text{连续相对论传播}.
}
$$

量子行走与连续 Dirac 演化之间的可观测收敛，已有更一般维数和函数空间中的严格研究；本节给出的是当前两分量模型的直接界。([arXiv][1])

### 一个不能忽略的输入区别

第322节使用局域初态证明因果支持。

本节使用严格带限输入证明低频逼近。

非零函数一般不能同时严格紧支撑又严格带限。**这两种定理服务于不同实验条件，不能把它们的前提未经检查地叠在同一个输入上。**

---

## 离散偏差并没有消失，只是在小参数下受控

由式（323.1）：

$$
\boxed{
\theta^2
=
\mu^2+\kappa^2
-\frac13\mu^2\kappa^2
+
O\!\left((\mu^2+\kappa^2)^3\right).
}
\tag{324.4}
$$

领先项给出相对论质量壳；后面的混合项同时依赖时间相位和空间相位。

因此：

> **离散空间与离散时间的偏差，一般不是两份独立误差，而会产生联合修正。**

长时间实验还会积累小的单步差异。即使单步极其接近，也不能无条件推断任意长历史都接近。

---

# 325．从质量壳到钟速和洛伦兹间隔

现在不直接规定时间膨胀，而从刚得到的低频传播关系计算。

## 定理325.1　低频极限的质量壳

由 \(X^2=Z^2=I\) 与 \(XZ+ZX=0\)：

$$
\boxed{
H_D(p)^2
=
\left(m^2c_*^4+c_*^2p^2\right)I.
}
\tag{325.1}
$$

所以正能支：

$$
\boxed{
E(p)=\sqrt{m^2c_*^4+c_*^2p^2}.
}
\tag{325.2}
$$

其群速度为：

$$
v=\frac{\partial E}{\partial p}
=
\frac{c_*^2p}{E}.
$$

因此：

$$
p=\frac{mv}{\sqrt{1-v^2/c_*^2}},
\qquad
E=\frac{mc_*^2}{\sqrt{1-v^2/c_*^2}}.
$$

---

## 定理325.2　沿惯性路径的相位积累给出固有时间因子

对窄波包或对应的 Hamilton–Jacobi 相位，沿：

$$
dx=v\,dt
$$

有：

$$
p\,dx-E\,dt
=
-\left(E-pv\right)dt.
$$

利用上一式：

$$
\boxed{
E-pv
=
mc_*^2\sqrt{1-\frac{v^2}{c_*^2}}.
}
\tag{325.3}
$$

因此：

$$
\boxed{
d\varphi
=
-\frac{mc_*^2}{\hbar}\,d\tau,
\qquad
d\tau
=
dt\sqrt{1-\frac{v^2}{c_*^2}}.
}
\tag{325.4}
$$

于是得到：

$$
\boxed{
c_*^2d\tau^2=c_*^2dt^2-dx^2.
}
\tag{325.5}
$$

### 这一步的物理条件

单个能量本征态的整体相位不是可直接读取的钟。

要成为观察者内部钟，需要至少两个可相干比较的能量分支，并要求它们的运动与能量使用同一套标定。

若两分支具有相应的静止能量差 \(\Delta E_0\)，沿同一条受控路径比较，则相对相位可以读取：

$$
\boxed{
d(\Delta\varphi)
=
-\frac{\Delta E_0}{\hbar}d\tau.
}
\tag{325.6}
$$

控制器、路径重合和其他动力学相位必须同时纳入实验；不能把一条平面波公式直接当成无条件的真实钟。

---

## 洛伦兹变换现在成为保持共同读数的变换

定义：

$$
ds^2=-c_*^2dt^2+dx^2.
$$

直接验证：

$$
t'=\gamma_v\left(t-\frac{vx}{c_*^2}\right),
\qquad
x'=\gamma_v(x-vt),
$$

$$
\gamma_v=\frac1{\sqrt{1-v^2/c_*^2}},
$$

保持 \(ds^2\) 不变。

所以在这一低频、共同钟标定的模型中：

$$
\boxed{
\text{局域离散酉规则}
\longrightarrow
\text{Dirac质量壳}
\longrightarrow
\text{固有时间因子}
\longrightarrow
\text{洛伦兹间隔}.
}
$$

**这是一条条件推导链，不是先假设洛伦兹间隔再把它改写成量子语言。**但它确实使用了特定的两模式耦合、空间均匀性和共同能量标定；这些条件不能被省略。

---

# 326．统一时空几何，必须同时检查“空间边”和“时间边”的闭路

此前研究闭路时，容易只看空间路径。离散时间加入后，最小闭路还可以比较：

$$
\text{先演化，再换位置}
$$

与：

$$
\text{先换位置，再演化}.
$$

## 定义326.1　离散时空单元的两条输运路径

在格点 \((n,j)\) 上，设有某个已标定的参照纤维。

定义：

$$
T_{n,j}:\mathcal H_{n,j}\to\mathcal H_{n+1,j},
$$

$$
V_{n,j}:\mathcal H_{n,j}\to\mathcal H_{n,j+1}.
$$

暂时假设这些输运可逆且酉。

从 \((n,j)\) 到 \((n+1,j+1)\)，两条路径为：

$$
A=V_{n+1,j}T_{n,j},
$$

$$
B=T_{n,j+1}V_{n,j}.
$$

定义闭路比较算子：

$$
\boxed{
W_\square=B^\dagger A.
}
\tag{326.1}
$$

---

## 定理326.1　纯参照更名不产生非平凡时空单元闭路

若存在局部参照映射 \(G_{n,j}\)，使：

$$
T_{n,j}=G_{n+1,j}G_{n,j}^\dagger,
$$

$$
V_{n,j}=G_{n,j+1}G_{n,j}^\dagger,
$$

则：

$$
\boxed{W_\square=I.}
\tag{326.2}
$$

### 证明

沿两条路径，相邻 \(G^\dagger G\) 相消，均得到：

$$
G_{n+1,j+1}G_{n,j}^\dagger.
$$

∎

因此，真正的非平凡闭路必须超出纯粹的局部命名变化。

在光滑连接实现中，若边输运由：

$$
\mathcal P\exp\!\left(-\int\mathcal A\right)
$$

产生，则小单元展开为：

$$
\boxed{
W_\square
=
I-a\delta\,\mathcal F_{tx}
+
O(a^2\delta+a\delta^2),
}
\tag{326.3}
$$

其中：

$$
\boxed{
\mathcal F_{tx}
=
\partial_t\mathcal A_x
-\partial_x\mathcal A_t
+
[\mathcal A_t,\mathcal A_x].
}
\tag{326.4}
$$

这说明：

> **统一空间与时间以后，几何的一部分不在某张“空间快照”中，而在两种执行顺序之间的相容性中。**

但这里仍然是指定参照输运的连接曲率。

有限维量子态空间上的酉连接，不会仅因写出 \(\mathcal F_{tx}\) 就自动变成时空 Levi–Civita 曲率。还需要证明它怎样作用于共同钟尺、空间标架和物质传播。

同样，如果 \(V,T\) 是实际控制门而不是被动输运，它们的不交换可能来自控制 Hamiltonian，而不是引力。

---

# 327．怎样走向真实的 \(3+1\) 维结构，而不把四个素数当成四维时空？

一维模型已经展示了机制。下一步必须处理三个空间方向。

## 定义327.1　四分量的局部传播结构

取 Pauli 矩阵 \(\sigma_i\)，并定义：

$$
\alpha_i=X\otimes\sigma_i,
\qquad
\beta=Z\otimes I_2.
$$

它们满足：

$$
\boxed{
\{\alpha_i,\alpha_j\}=2\delta_{ij}I,
\qquad
\{\alpha_i,\beta\}=0,
\qquad
\beta^2=I.
}
\tag{327.1}
$$

选择三个方向的条件平移和一个局部混合：

$$
\boxed{
U_\delta(\mathbf k)
=
e^{-i\delta mc_*^2\beta/\hbar}
e^{-ia k_3\alpha_3}
e^{-ia k_2\alpha_2}
e^{-ia k_1\alpha_1}.
}
\tag{327.2}
$$

每个空间因子都可按 \(\alpha_i\) 的 \(\pm1\) 子空间解释为向相反方向移动一格。

---

## 定理327.1　其低频生成元具有 \(3+1\) 维相对论质量壳

在 \(a=c_*\delta\) 的缩放下：

$$
U_\delta
=
I-\frac{i\delta}{\hbar}H_D+O(\delta^2),
$$

其中：

$$
\boxed{
H_D
=
c_*\sum_{i=1}^3\alpha_i p_i
+mc_*^2\beta.
}
\tag{327.3}
$$

而：

$$
\boxed{
H_D^2
=
\left(c_*^2|\mathbf p|^2+m^2c_*^4\right)I.
}
\tag{327.4}
$$

### 证明

指数乘积的一阶项相加，得到式（327.3）。

平方时全部不同方向的交叉项及质量交叉项，分别由式（327.1）消去。∎

这给出：

$$
ds^2=-c_*^2dt^2+dx^2+dy^2+dz^2
$$

对应的质量壳与传播结构。

高维离散量子模型恢复 Dirac 动力学有现成的研究路径；更强的分类结果会额外使用均匀性、局域性和离散各向同性等假设。([arXiv][3])

### 这里还没有推导出“为什么恰好三个空间方向”

我们选择了三组可独立平移的接口，并选用了相容的四分量表示。

因此证明的是：

$$
\boxed{
\text{这组离散结构足以实现 }3+1\text{ 维低频物理}.
}
$$

尚未证明的是：

$$
\boxed{
\text{任何量子观察者都必然生成且只能生成 }3+1\text{ 维}.
}
$$

另外，式（327.2）的一个宏步骤包含三次方向平移。其有限尺度的精确因果邻域与低频球形光锥不是同一个对象，不能未经分析把二者最大速度直接认成相等。

---

## 从局部传播矩阵识别弯曲几何

在已经证明存在光滑极限的区域，假设主部具有：

$$
i\partial_t\psi
=
-i\sum_iA^i(x,t)\partial_i\psi+\text{低阶项},
$$

其中：

$$
A^i=w^iI+\sum_a e_a^{\,i}\alpha_a.
$$

定义：

$$
h^{ij}=\sum_a e_a^{\,i}e_a^{\,j}.
$$

若 \(h\) 正定，则特征关系为：

$$
\boxed{
(\omega-w^ik_i)^2-h^{ij}k_ik_j=0.
}
\tag{327.5}
$$

它确定一个洛伦兹型共形度量：

$$
\boxed{
ds^2
=
\Lambda^2
\left[
-dt^2+
(h^{-1})_{ij}
(dx^i-w^i dt)(dx^j-w^j dt)
\right],
\quad \Lambda>0.
}
\tag{327.6}
$$

### 为什么符号类型已经确定？

把：

$$
\theta^i=dx^i-w^i dt
$$

作为新的局部标架，式（327.6）就是一个负平方加三个正平方。因此恰有一个时间方向。

但是主传播锥没有确定 \(\Lambda\)。它需要实际钟或体积标定。

而且，低阶连接项、守恒概率所需的项和物质耦合仍要一致，不能只写主符号就宣布已得到完整曲时空 Dirac 方程。局部酉规则编码曲时空 Dirac 传播，已有需要分组与编码条件的构造。([arXiv][4])

---

# 328．离散步骤本身会产生“可观测维数临界”

这是与项目最直接的新连接。

仓库 `HamiltonianEffectCompletionGenerator.lean` 研究的是全部连续时刻的效果轨道，并把它与 Hamiltonian 交换子生成的闭包联系起来。

但一个只在固定时刻刷新读数的观察者，访问的是另一组效果。

## 定义328.1　离散采样效果空间

设有限维 Hamiltonian 为 \(H\)，采样间隔为 \(\delta\)，并令：

$$
U_\delta=e^{-iH\delta/\hbar}.
$$

对初始效果 \(E\)，定义：

$$
\boxed{
\mathcal S_\delta(E)
=
\operatorname{span}_{\mathbb C}
\{U_\delta^{-n}EU_\delta^n:n\ge0\}.
}
\tag{328.1}
$$

这里讨论的是可获得的时间采样统计，例如在独立重复制备中选择这些读出时刻；没有把反复测量同一份系统的反作用忽略掉。

若真对同一系统持续监视，则应改用完整仪器过程，Zeno效应等必须重新进入模型。

---

## 定理328.1　能级差的混叠决定离散完成是否丢失方向

设：

$$
H=\sum_aE_aP_a.
$$

连续效果轨道的不同频率为：

$$
\omega_{ab}=\frac{E_a-E_b}{\hbar}.
$$

离散采样只能区分：

$$
e^{i\omega_{ab}\delta}.
$$

因此不同频率若满足：

$$
\boxed{
(\omega_{ab}-\omega_{cd})\delta\in2\pi\mathbb Z,
}
\tag{328.2}
$$

它们会进入同一个采样频率类别。

若所有实际出现的不同频率在采样后仍然不同，则：

$$
\boxed{
\mathcal S_\delta(E)
=
\mathcal S_{\mathrm{continuous}}(E).
}
\tag{328.3}
$$

### 证明

把 \(E\) 按能级差分解：

$$
E=\sum_\omega E_\omega.
$$

离散轨道为：

$$
E(n\delta)=\sum_\omega e^{in\omega\delta}E_\omega.
$$

若相位 \(\lambda_\omega=e^{i\omega\delta}\) 两两不同，有限组采样构成可逆 Vandermonde 矩阵，因此能够分别恢复每个 \(E_\omega\)。

若相位相同，采样只能直接看到相应 \(E_\omega\) 的和。∎

这不仅是普通的频率测量问题，而是：

$$
\boxed{
\text{改变时间采样}
\longrightarrow
\text{改变可预测效果空间的维数}.
}
$$

---

## 5040三态纤维的精确例子

沿用此前已明确的：

$$
\{4704,5040,5400\}
$$

三态纤维，并且本例**只使用对数对角能量**。

因为：

$$
\frac{5040}{4704}
=
\frac{5400}{5040}
=
\frac{15}{14},
$$

减去共同能量后，可写成：

$$
H=\Delta\operatorname{diag}(0,1,2),
\qquad
\Delta=E_*\ln\frac{15}{14}.
$$

取：

$$
E=|+\!_3\rangle\langle+\!_3|,
\qquad
|+\!_3\rangle=\frac{|0\rangle+|1\rangle+|2\rangle}{\sqrt3},
$$

并定义：

$$
T_0=\frac{2\pi\hbar}{\Delta}.
$$

直接得到：

| 采样间隔      | \(\dim\mathcal S_\delta(E)\) |
| --------- | ---------------------------: |
| \(T_0/8\) |                            5 |
| \(T_0/4\) |                            4 |
| \(T_0/3\) |                            3 |
| \(T_0/2\) |                            2 |
| \(T_0\)   |                            1 |

连续轨道对这个特定效果的维数为5，不是整个三态密度矩阵空间的维数9。

**同一个三态系统、同一个 Hamiltonian、同一个探测器，只改变离散时间接口，就产生了精确的维数下降。**

这与此前空间接口合并不同状态，是同一种预测问题的另一面。

在接近混叠时，Vandermonde矩阵还会变得病态。因此：

$$
\boxed{
\text{精确可区分}
\ne
\text{有限噪声下稳定可区分}.
}
$$

---

# 329．统一离散时空后，会出现哪些不能省略的边界？

现在可以把几类真正不同的离散临界列出来。

## 第一类：时空奇偶约束

第322节已经证明：

$$
j-j_0\equiv n\pmod2.
$$

在从原点出发的允许子格上，模式：

$$
e^{i\kappa j-i\theta n}
$$

与：

$$
e^{i(\kappa+\pi)j-i(\theta+\pi)n}
$$

完全相同，因为二者之比为：

$$
(-1)^{j-n}=1.
$$

所以还存在联合识别：

$$
\boxed{
(\theta,\kappa)\sim(\theta+\pi,\kappa+\pi).
}
\tag{329.1}
$$

**空间和时间的离散混叠，甚至可以耦合在一起。**

这不是物理时间周期性回到过去，而是指定采样子格不能区分某些模式标签。

---

## 第二类：相位带边界不等于无限物理能量

离散时间的一步酉算子只读取：

$$
e^{-iE\delta/\hbar}.
$$

因此：

$$
\boxed{
E\sim E+\frac{2\pi\hbar}{\delta}.
}
\tag{329.2}
$$

仅从一步更新，不能唯一恢复一个全局连续 Hamiltonian；不同对数分支可能给出相同采样演化。

我们此前的连续极限只选择低频、连续接近恒等的一支，不能据此宣布整个带状谱只有这一种解释。

---

## 第三类：一步能传播，两步读数却可以完全不动

在第322节模型中，取：

$$
\mu=\frac\pi2.
$$

则对全部 \(\kappa\)：

$$
\boxed{
U_{\pi/2}(\kappa)^2=-I.
}
\tag{329.3}
$$

因此，两步后的密度矩阵完全恢复。

若观察者只在偶数步读取，会看到恒等过程；但中间一步确实发生了模式与位置变化。

这再次说明：

$$
\boxed{
\text{采样不动点}
\ne
\text{完整过程处处不动}.
}
$$

不能把这个特定参数下的两步回归解释成普遍最大质量、黑洞或时间终止。它首先是当前离散更新的谱退化。

---

## 第四类：固定晶格与全部连续洛伦兹变换不能同时严格成立

假设一个固定离散事件格在全部连续 boost 下保持不变。

取其中一个非零事件向量。随着 boost 参数连续变化，它应连续扫过一条轨道。

但这条轨道又必须始终落在固定离散集合中，因此只能局部常值；非零事件向量实际上会被 boost 改变，矛盾。

所以：

$$
\boxed{
\text{固定非平凡晶格}
\not\Rightarrow
\text{全部连续洛伦兹对称在微观层面精确成立}.
}
$$

当前构造选择的是：

$$
\boxed{
\text{微观离散规则}
+
\text{受控低频洛伦兹极限}.
}
$$

已有相关自动机模型也明确区分低能洛伦兹行为与高能尺度的偏离。([arXiv][3])

若希望在根本离散层仍保持更强的协变性，需要不同的事件结构或不同的对称实现，不能把这项困难藏起来。

---

## 第五类：状态资源最优，不等于运行时间最优

此前5040的优化关注：

$$
W(n)-\lambda\ln n.
$$

现在必须加入实际允许程序中的步骤成本，例如：

$$
\boxed{
W(n)-\lambda\ln n-\eta L_\Gamma(n),
}
\tag{329.4}
$$

其中 \(L_\Gamma(n)\) 是在明确的局域控制族中，从指定初态制备或处理 \(n\) 所需的成本。

\(L_\Gamma\) 不能只由数字 \(n\) 猜出；它取决于寄存器布局、允许门、并行度、进位实现与精度。

因此，先前“5040在某个资源价格下最优”的结论，不自动意味着它在加入时间成本后仍然最优。

**离散空间资源与离散执行成本，可以统一优化，但首先必须明确它们来自同一个物理实现。**

---

# 330．从量子观察者到现实结构：这轮真正完成了哪一段？

现在能够给出一个更严格的条件性重建命题。

## 定理330.1　离散因果量子过程的洛伦兹有效实现

假设模型具有：

1. 明确的局部量子接口、事件依赖与合法酉更新；
2. 指定的均匀传播和局部混合结构；
3. 共同的空间—时钟标定 \(a=c_*\delta\)；
4. 固定物理质量下的低频缩放；
5. 与同一能量关系相容的内部钟比较。

则在第324节的有限波数与有限时间窗口内：

$$
\boxed{
\text{离散完整演化}
}
$$

能够以显式误差逼近：

$$
\boxed{
\text{Dirac传播}
+
\text{相对论质量壳}
+
\text{洛伦兹固有时间}.
}
$$

若进一步给出三方向相容的传播代数，则获得 \(3+1\) 维自由 Dirac 候选。

若再证明位置依赖的局部规则具有相应光滑极限、概率守恒和钟尺相容性，则其主传播结构可以确定一个洛伦兹共形度量。

### 证明

分别由第322—327节的酉性、色散、范数收敛、相位钟速及 Clifford 恒等式得到。∎

---

## 仍然不能从定义直接宣布成立的部分

| 待完成桥梁         | 为什么不可省略                           |
| ------------- | --------------------------------- |
| 为什么是三维空间      | 当前构造选择了三组平移方向，还未证明唯一性             |
| 不同物质为何共享同一个光锥 | 一个自由探针的传播不能替代全部物质的普适耦合            |
| 引力场怎样自主演化     | 能在给定曲几何上传播，不等于已经导出 Einstein 方程    |
| 微观离散性的对称性     | 固定晶格的精确对称与低能洛伦兹对称不同               |
| 观察者怎样长期保存记忆   | 周期量子态、暂态钟和不可逆记录需要不同资源             |
| 算术结构为何选定耦合    | 5040、Zeckendorf和素数标签本身不唯一决定局域门与相位 |

因果次序与事件数量在附加光滑、测度和统计条件下重建几何，已有严格结果；但不能将它缩写为“任意有限偏序都已经是唯一的物理时空”。([arXiv][5])

---

## 与项目的对应

本次核对的版本为：

```text
b89d56d0c9a433f9b714821d2bb1779066c59ede
```

三项现有基础可以直接接入：

**受控关系递归**：处理有限步骤以后，哪些当前等价状态仍然等价。

**Hamiltonian效果完成**：处理连续时间下未来读数需要哪些交换子方向；本轮补充了固定步长采样下的混叠与维数下降。

**精确下降排除carry**：要求时空有效模型确实能够预测指定协议，而不只是匹配某个瞬时图像或色散曲线。

所以完整证书应当包含：

$$
\boxed{
\begin{aligned}
&\text{状态与事件网络};\\
&\text{单步物理实现};\\
&\text{因果支持与允许采样};\\
&\text{空间频率、时间频率和总运行预算};\\
&\text{连续几何映射及误差};\\
&\text{与其他观察者钟尺的一致性}.
\end{aligned}
}
\tag{330.1}
$$

### 本轮核验

已完成 **49项有限代数、整数或符号检查**，以及一组包含四种参数配置的数值交叉检查。

其中包括：更新酉性、联合色散、离散波动方程、时空奇偶支持、两步回归、三态采样维数、四分量 Clifford 关系，以及连续极限误差界。

[核验脚本](sandbox:/mnt/data/observer_formalization/check_discrete_spacetime_bridge.py)
[核验结果](sandbox:/mnt/data/observer_formalization/discrete_spacetime_bridge_checks.json)

**本轮未执行 Lean 内核检查。**有限代数检查、一般证明、连续极限假设和现实实验验证，仍然是不同层次。

---

# 结论

这一轮最重要的推进，是不再把空间理解成“放数据的格子”，把时间理解成“格子外面运行的计数器”。

在明确模型中，它们一起进入：

$$
\boxed{
\psi_{n+1,j}+\psi_{n-1,j}
=
\cos\mu\,
\bigl(\psi_{n,j+1}+\psi_{n,j-1}\bigr).
}
$$

同一个规则同时决定：

$$
\boxed{
\text{能影响多远},
\quad
\text{哪些时空格点允许出现},
\quad
\text{相位怎样传播},
\quad
\text{能量和动量怎样关联}.
}
$$

在低频、有限实验预算和共同标定下，它进一步给出：

$$
\boxed{
E^2=c_*^2p^2+m^2c_*^4,
\qquad
c_*^2d\tau^2=c_*^2dt^2-dx^2.
}
$$

而离散层仍然保留：

$$
\boxed{
\text{奇偶子格},
\quad
\text{频率混叠},
\quad
\text{相位带边界},
\quad
\text{有限时间误差}.
}
$$

**这使“时空由量子观察者的因果信息流形成”获得了一个可检验的含义：不是把任何数据流命名为时空，而是证明它在一定尺度上，同时支持共同的传播、能量、钟速和参照变换，并明确计算这些关系在哪些离散边界上开始失效。**

5040与黄金寄存器可以继续提供内部状态、资源结构和相位时钟的实验模型；但真正决定外部时空的，不是整数名字本身，而是这些内部结构如何通过**局域、可实现、有时间成本的量子交互**与其他观察者连接。

[1]: https://arxiv.org/abs/1307.3524 "https://arxiv.org/abs/1307.3524"
[2]: https://arxiv.org/abs/1212.2839 "https://arxiv.org/abs/1212.2839"
[3]: https://arxiv.org/abs/1306.1934 "https://arxiv.org/abs/1306.1934"
[4]: https://arxiv.org/abs/1609.00305 "https://arxiv.org/abs/1609.00305"
[5]: https://arxiv.org/abs/2507.01907 "https://arxiv.org/abs/2507.01907"
**可以。这次最有价值的“其他切面”，不是再给同一个公式换坐标，而是检验：同一个离散时空过程，换一种切法后，究竟还保存什么结构。**

我们会得到一个重要结果：

> **同一个量子过程，沿时间切面可以是酉演化；沿空间切面却可以出现指数增长与衰减。两者并不矛盾，因为前者保存状态总概率，后者保存的是带方向符号的概率流。**

再换到因果区间切面，可以从离散计数提取一个与洛伦兹固有时间一致的量；换到边界信息切面，则得到有限观察者必须保留多少量子自由度的下界。

这意味着，“统一时空”不要求所有方向完全同型。更严格的要求是：

$$
\boxed{
\text{不同切面必须能够还原为同一个联合过程，}
}
$$

$$
\boxed{
\text{并明确保留各自的归一化、边界条件和守恒量。}
}
$$

# 离散时空的多切面一致性、空间衰减与因果几何

## ——量子观察者—关系时空理论第三百三十一至第三百四十节增订

---

# 331．切面首先是一种数据类型，不是任意画出的一条线

先沿用上一轮的有限量子事件网络：节点是实际交互，边是传递给后续交互的量子接口。所有会再次影响实验的环境、时钟和记忆，都包含在联合模型中。

## 定义331.1　完整因果切面

一个切面 \(\Sigma\) 由一组量子线路组成。称其为完整因果切面，若它能够分开已经执行的事件与尚未执行的事件，并且没有遗漏从前者进入后者的线路。

切面状态空间为

$$
\mathcal H_\Sigma
=
\bigotimes_{e\in\Sigma}\mathcal H_e.
$$

这是模型中的完整边界状态，不意味着一个局域观察者实际能够瞬时读取其中所有信息。

## 定理331.1　完整因果切面之间保持酉等价

假设每个事件都由输入、输出维数相同的酉操作实现。若从 \(\Sigma\) 推进到 \(\Sigma'\) 时没有丢弃线路，则存在酉映射

$$
\boxed{
U_{\Sigma'\leftarrow\Sigma}:
\mathcal H_\Sigma\longrightarrow\mathcal H_{\Sigma'}.
}
\tag{331.1}
$$

同一事件区域的不同合法执行顺序，给出相同映射。

### 证明

每推进一个事件，只是把其全部输入线路替换为全部输出线路，实施该事件的酉算子，并在其他线路上作用为恒等。

连续推进得到酉算子的乘积。不同合法排序只交换相邻的、互不依赖的事件；这些操作作用于不同张量因子，因此可交换。∎

### 为什么“只保留观察者自己的状态”一般不够？

如果切面丢掉某个仍会参与未来交互的环境寄存器，剩余约化态通常不能决定未来。

最简单的例子是：观察者当前状态相同，环境分别为 \(|0\rangle\) 与 \(|1\rangle\)，下一步实施 SWAP。观察者的后续状态就会不同。

所以：

$$
\boxed{
\text{换一个完整切面}
\ne
\text{删除一部分切面数据}.
}
$$

项目的 `exact_descent_has_no_carry` 正是针对后一种情况提出严格要求：只有后续读数确实沿当前接口下降，当前压缩才是预测充分的。

---

# 332．沿时间酉，不代表把张量横过来看也酉

这是空间—时间统一中一个容易被忽略的条件。

## 定义332.1　一个局部事件的两种切法

取一个双体门

$$
U_{cd,ab},
$$

其中 \(a,b\) 是输入标签，\(c,d\) 是输出标签。

通常时间切法把它看成

$$
(a,b)\longmapsto(c,d).
$$

另一种横向排列定义矩阵

$$
\boxed{
\widetilde U_{(c,a),(d,b)}=U_{cd,ab}.
}
\tag{332.1}
$$

这只是同一个四指标张量的重新分组。整个有限网络的收缩值不变，但新矩阵不一定是合法的确定性量子门。

## 定理332.1　时间酉性不推出横向酉性

取恒等门

$$
U_{cd,ab}=\delta_{ca}\delta_{db}.
$$

则 \(U\) 是 \(d^2\) 维酉矩阵，但其横向矩阵满足

$$
\boxed{
\operatorname{rank}\widetilde U=1.
}
\tag{332.2}
$$

当 \(d>1\) 时，它不可能酉。

### 证明

横向矩阵为

$$
\widetilde U_{(c,a),(d,b)}
=
\delta_{ca}\delta_{db},
$$

是两个非零向量的外积，因此秩一。∎

反过来，取

$$
U|a,b\rangle=e^{i\phi_{ab}}|b,a\rangle.
$$

无论 \(\phi_{ab}\) 如何选择，时间矩阵与横向矩阵都是带相位的置换矩阵，因而都酉。

这就是一种“双酉”结构。双酉量子电路确实是已有的空间—时间对偶研究路线，但它是一项额外耦合约束，不是所有量子过程自动满足的性质。([arXiv][1])

### 对我们理论的限制

不能因为同一网络可以沿不同方向收缩，就宣布：

$$
\text{每一种切面都是另一位观察者的普通时间演化}.
$$

横向对象可能是传递矩阵、边界约束或条件振幅，而非保迹量子通道。

**切面转换保留的是完整网络所给出的实验结果，不一定保留每个中间矩阵的物理类型。**

---

# 333．对上一轮的量子行走，空间切面保存什么？

现在直接分析上一轮的模型，而不另换一个无关系统。

设

$$
U=C_\mu S,
\qquad
C_\mu=
\begin{pmatrix}
\cos\mu&-i\sin\mu\\
-i\sin\mu&\cos\mu
\end{pmatrix},
$$

其中 \(S\) 使两种模式分别向右、向左移动一格。

取

$$
0<\mu<\frac\pi2.
$$

时间推进在整个量子态空间上严格酉。

## 定义333.1　固定频率后的空间递推

考虑广义驻波

$$
\psi_{n,j}=e^{-in\theta}
\begin{pmatrix}
u_j\\v_j
\end{pmatrix}.
$$

它是分析散射与传播的模式，不要求在整条无限线上已经归一化为有限范数态。

令

$$
c_\mu=\cos\mu,\qquad s_\mu=\sin\mu.
$$

更新方程给出

$$
e^{-i\theta}u_j
=
c_\mu u_{j-1}-is_\mu v_{j+1},
$$

$$
e^{-i\theta}v_j
=
-is_\mu u_{j-1}+c_\mu v_{j+1}.
$$

解出新的空间边界数据：

$$
\boxed{
\begin{pmatrix}
u_j\\v_{j+1}
\end{pmatrix}
=
T_\mu(\theta)
\begin{pmatrix}
u_{j-1}\\v_j
\end{pmatrix},
}
\tag{333.1}
$$

其中

$$
\boxed{
T_\mu(\theta)
=
\frac1{\cos\mu}
\begin{pmatrix}
e^{i\theta}&-i\sin\mu\\
i\sin\mu&e^{-i\theta}
\end{pmatrix}.
}
\tag{333.2}
$$

这种从量子行走本征方程得到空间传递矩阵的方法，已有明确的谱分析基础。([arXiv][2])

---

## 定理333.1　空间传递保持定向概率流，而非普通长度

令

$$
J=
\begin{pmatrix}
1&0\\
0&-1
\end{pmatrix}.
$$

则

$$
\boxed{
\det T_\mu(\theta)=1,
\qquad
T_\mu(\theta)^\dagger JT_\mu(\theta)=J.
}
\tag{333.3}
$$

因此

$$
\boxed{
|u_j|^2-|v_{j+1}|^2
=
|u_{j-1}|^2-|v_j|^2.
}
\tag{333.4}
$$

### 证明

行列式与矩阵恒等式可以直接展开验证。

也可以由局部门的酉性得到

$$
|u_j|^2+|v_j|^2
=
|u_{j-1}|^2+|v_{j+1}|^2,
$$

移项即得式（333.4）。∎

这里的负号表示左行与右行概率流方向相反，不表示存在负概率。

项目的 `GNSMatrix.lean` 把正密度矩阵对 \(X^\dagger X\) 的读数写成范数平方，属于正概率结构；不能把本节的带符号流量直接放进去，当作另一张密度矩阵。

---

# 334．同一个时空方程，在空间切面上出现三个临界区

由式（333.2）：

$$
\operatorname{Tr}T_\mu(\theta)
=
2\frac{\cos\theta}{\cos\mu}.
$$

定义

$$
r=\frac{\cos\theta}{\cos\mu}.
$$

## 定理334.1　空间传播的三种谱类型

传递矩阵的特征方程为

$$
\boxed{
\lambda^2-2r\lambda+1=0.
}
\tag{334.1}
$$

因此：

| 条件 | 空间本征值 | 对应行为 |                    |             |
| -- | ----- | ---- | ------------------ | ----------- |
| (  | r     | <1)  | \(e^{\pm ik}\)     | 振荡传播        |
| (  | r     | =1)  | 重根 \(+1\) 或 \(-1\) | 临界，可能出现线性增长 |
| (  | r     | >1)  | 模长互为倒数的实根          | 指数衰减与增长方向   |

### 证明

解二次方程：

$$
\lambda_\pm=r\pm\sqrt{r^2-1}.
$$

根据判别式符号分类即可。∎

在临界处，因 \(0<\mu<\pi/2\)，矩阵不等于 \(\pm I\)。例如在 \(r=1\) 时：

$$
(T-I)^2=0,
$$

所以

$$
\boxed{
T^L=I+L(T-I).
}
\tag{334.2}
$$

**临界不是矩阵值突然不连续，而是反复空间传递的长期行为发生改变。**

---

## 定理334.2　纯指数衰减模式的净流为零

若

$$
Tv=\lambda v,
\qquad |\lambda|\ne1,
$$

则

$$
\boxed{v^\dagger Jv=0.}
\tag{334.3}
$$

### 证明

由流量保持，

$$
v^\dagger Jv
=
(Tv)^\dagger J(Tv)
=
|\lambda|^2v^\dagger Jv.
$$

因为 \(|\lambda|^2\ne1\)，只能为零。∎

这意味着，一个单独的衰减模式不是一个把净概率持续送向远处的传播模式。有限区域的穿透需要结合左右边界条件。

同时必须注意：

$$
\boxed{
\text{空间传递矩阵出现重根或指数行为}
}
$$

不意味着

$$
\boxed{
\text{时间 Hamiltonian 失去自伴性或时间演化产生概率增长}.
}
$$

二者是同一方程的不同切面。

---

# 335．有限指数区间产生隧穿，而不破坏时间酉性

取一个特别容易精确核验的参数：

$$
\cos\mu=\frac35,\qquad
\sin\mu=\frac45.
$$

这只是选取有理矩阵元方便计算，不赋予3、4、5额外的基本常数地位。

在零准频率 \(\theta=0\)：

$$
\boxed{
T_0=
\frac13
\begin{pmatrix}
5&-4i\\
4i&5
\end{pmatrix}.
}
\tag{335.1}
$$

其本征值为

$$
3,\qquad\frac13.
$$

## 定理335.1　连续 \(L\) 个单元的精确穿透率

令这个有限区域两侧都是无混合的自由传播区。取左侧单位入射振幅，右侧无入射波。

写边界匹配为

$$
\begin{pmatrix}
t_L\\0
\end{pmatrix}
=
T_0^L
\begin{pmatrix}
1\\r_L
\end{pmatrix}.
$$

则

$$
\boxed{
|t_L|^2
=
\operatorname{sech}^2(L\ln3),
}
\tag{335.2}
$$

$$
\boxed{
|r_L|^2
=
\tanh^2(L\ln3),
}
\tag{335.3}
$$

并且

$$
\boxed{|t_L|^2+|r_L|^2=1.}
\tag{335.4}
$$

### 证明

令

$$
a_L=\frac{3^L+3^{-L}}2,
\qquad
b_L=\frac{3^L-3^{-L}}2.
$$

因为 \(T_0=\cosh(\ln3)I+\sinh(\ln3)Y\)，且 \(Y^2=I\)，所以

$$
T_0^L=
\begin{pmatrix}
a_L&-ib_L\\
ib_L&a_L
\end{pmatrix}.
$$

边界方程第二行给出

$$
r_L=-i\frac{b_L}{a_L},
$$

第一行给出

$$
t_L=\frac1{a_L}.
$$

再用 \(a_L^2-b_L^2=1\)。∎

例如：

| 区域长度 \(L\) |           穿透概率 |
| ---------: | -------------: |
|          1 |       \(9/25\) |
|          2 |    \(81/1681\) |
|          3 | \(729/133225\) |

### 这一结果的意义

$$
\boxed{
\text{空间上存在指数衰减}
+
\text{两侧边界匹配}
\longrightarrow
\text{有限但非零的穿透概率}.
}
$$

时间演化仍然酉，总入射概率被分配到透射与反射。

在低频缩放

$$
\theta=\frac{E\delta}{\hbar},
\qquad
\mu=\frac{mc_*^2\delta}{\hbar},
\qquad
a=c_*\delta
$$

下，禁带中的衰减指数满足

$$
\boxed{
\frac{\chi}{a}
\longrightarrow
\frac{\sqrt{m^2c_*^4-E^2}}{\hbar c_*},
\qquad |E|<mc_*^2.
}
\tag{335.5}
$$

这与相应 Dirac 质量隙中的衰减尺度一致。

但这个有限散射区域不是黑洞：本节没有建立事件视界、热辐射谱或引力反作用。

---

# 336．换到因果区间切面：固有时间可以由离散计数识别

现在暂时离开频率表示，回到上一轮的时空格点：

$$
(n,j),\qquad n+j\equiv0\pmod2.
$$

定义双零坐标

$$
\boxed{
u=\frac{n+j}{2},
\qquad
v=\frac{n-j}{2}.
}
\tag{336.1}
$$

一次右行更新增加 \(u\) 一；一次左行更新增加 \(v\) 一。

因此，允许事件的因果关系是

$$
\boxed{
(u,v)\preceq(u',v')
\iff
u\le u',\quad v\le v'.
}
\tag{336.2}
$$

这里描述潜在因果路径，不保证所有允许端点最终振幅都非零。

---

## 定理336.1　离散因果菱形的计数公式

从 \((0,0)\) 到 \((r,s)\)，闭因果区间为

$$
D_{r,s}=\{0,\ldots,r\}\times\{0,\ldots,s\}.
$$

其节点数为

$$
N_D=(r+1)(s+1),
$$

最长因果链的边数为

$$
h_D=r+s.
$$

于是

$$
\boxed{
N_D-h_D-1=rs.
}
\tag{336.3}
$$

### 证明

节点数由直积计数得到。

每条边恰好使 \(u+v\) 增加一，因此从起点到终点的最长饱和链恰有 \(r+s\) 条边。展开乘积即可。∎

给格距与步长作同一标定：

$$
x=a(u-v),
\qquad
t=\delta(u+v),
\qquad
c_*=\frac a\delta.
$$

则端点间满足

$$
\boxed{
(\Delta t)^2-\frac{(\Delta x)^2}{c_*^2}
=
4\delta^2rs
=
4\delta^2(N_D-h_D-1).
}
\tag{336.4}
$$

所以在这个规则 \(1+1\) 维模型中，可以定义与上一轮洛伦兹间隔相容的因果区间读数：

$$
\boxed{
\tau_D=2\delta\sqrt{N_D-h_D-1}.
}
\tag{336.5}
$$

这里扣除了明确的有限边界项。因果区间体积与几何量之间的关系，也是因果集研究中的一条正式路线；但本节结论只针对已定义的规则双零格，不推广为任意偏序的定理。([arXiv][3])

---

## 相同因果深度，不意味着相同固有时间

比较：

$$
(r,s)=(9,1)
\quad\text{与}\quad
(r,s)=(5,5).
$$

两者都有

$$
h_D=10.
$$

但分别有

$$
N_D=20,\qquad N_D=36,
$$

从而

$$
\boxed{
\tau_D=6\delta,\qquad \tau_D=10\delta.
}
\tag{336.6}
$$

**这直接限制了“时间就是步骤数”的强版本。**

步骤数可以给出程序深度或某个坐标时间；观察者的固有时间还取决于这些步骤如何分布在不同因果方向上。

例如 \((r,s)=(4,1)\) 给出

$$
\frac{v}{c_*}=\frac35,
\qquad
\frac{\tau_D}{\Delta t}=\frac45,
$$

与相对论时间因子精确一致。

但实际钟是否读取 \(\tau_D\)，仍需要上一轮建立的相位—质量壳桥梁；不能只定义一个平方根就宣布所有装置都服从它。

---

# 337．倾斜切面为何分成类空、类光和类时？

在双零坐标中，考虑切面函数

$$
T(u,v)=\alpha u+\beta v.
$$

沿两种基本因果边，其增量分别为

$$
\Delta_uT=\alpha,\qquad
\Delta_vT=\beta.
$$

因此：

$$
\boxed{
\alpha>0,\ \beta>0
}
$$

保证两类未来因果边都推进这个时间函数。

若某个系数为零，一类信号沿切面传播而不穿过它；若两个系数异号，一类未来信号会使这个“时间”减少。

这已经从离散事件结构区分了切面的性质。

---

## 定理337.1　同一分类出现在量子概率流中

对上一轮的连续 Dirac 极限，

$$
i\hbar\partial_t\psi
=
\left(
-i\hbar c_*Z\partial_x+mc_*^2X
\right)\psi,
$$

定义

$$
\rho=\psi^\dagger\psi,
\qquad
j=c_*\psi^\dagger Z\psi.
$$

则

$$
\boxed{
\partial_t\rho+\partial_xj=0.
}
\tag{337.1}
$$

在曲线 \(t=f(x)\) 上，相应通量形式为

$$
\rho\,dx-j\,dt.
$$

写 \(\psi=(u,v)^{\mathsf T}\)，得到

$$
\boxed{
\rho-jf'
=
(1-c_*f')|u|^2
+
(1+c_*f')|v|^2.
}
\tag{337.2}
$$

### 证明

将 Dirac 方程及其伴随代入 \(\partial_t(\psi^\dagger\psi)\)，质量项相消，剩下 \(-\partial_xj\)。

再在曲线上使用 \(dt=f' dx\)。∎

于是：

$$
|c_*f'|<1
\quad\Rightarrow\quad
\text{通量形成正定的状态读数};
$$

$$
|c_*f'|=1
\quad\Rightarrow\quad
\text{一类传播分量不被该切面读取};
$$

$$
|c_*f'|>1
\quad\Rightarrow\quad
\text{通量变成不定号}.
$$

### 统一解释

时间切面上的正概率范数、空间边界上的带符号流，并非两套互不相关的规则。

它们来自同一个守恒流在不同取向上的读取。

**类光切面的退化也不意味着信息被消灭。**它可能表示这条切面本来就不足以承载两种传播方向的完整初值，需要另一条边界或额外数据。

这与仓库受控关系递归的思想一致：未来可预测性必须针对实际可用的输入和读数定义，不能只看某个静态状态标签。

---

# 338．再换到信息边界切面：有限维数成为独立的几何约束

除了概率和传播，还可以问：

> 一条边界究竟能够承载多少量子区别？

## 定义338.1　张量网络割的容量

设一个有限网络沿某组内部线路切开，其线路维数为 \(d_e\)。

定义

$$
\boxed{
D_\Sigma=\prod_{e\in\Sigma}d_e.
}
\tag{338.1}
$$

## 定理338.1　跨越该割的状态秩受容量限制

若一个纯态网络沿该割分成左右两部分，则

$$
\boxed{
\operatorname{SchmidtRank}|\Psi\rangle\le D_\Sigma.
}
\tag{338.2}
$$

因此纠缠熵满足

$$
\boxed{
S\le\ln D_\Sigma=\sum_{e\in\Sigma}\ln d_e.
}
\tag{338.3}
$$

### 证明

把全部切断指标合并为一个标签 \(\gamma=1,\ldots,D_\Sigma\)，完整态具有形式

$$
|\Psi\rangle
=
\sum_{\gamma=1}^{D_\Sigma}
|L_\gamma\rangle\otimes|R_\gamma\rangle.
$$

其系数矩阵秩至多为 \(D_\Sigma\)。熵上界由 Schmidt 概率最多具有 \(D_\Sigma\) 个非零项得到。∎

类似地，若一个输入—输出线性映射必须通过这条边界因子化，其秩也不能超过 \(D_\Sigma\)。

这是上界，不保证任何网络都能达到。量子张量网络的一般最大流与最小割，不能无条件沿用经典的相等定理。([arXiv][4])

---

## Zeckendorf约束在这里有了新的切面意义

假设切面上有 \(L\) 个二值标签，但合法边界字串满足

$$
b_jb_{j+1}=0.
$$

令合法维数为 \(d_L\)。按末位分类：

$$
\boxed{
d_0=1,\qquad d_1=2,\qquad
d_L=d_{L-1}+d_{L-2}.
}
\tag{338.4}
$$

因此，边界容量不是 \(2^L\)，而是

$$
\boxed{d_L=F_{L+2}.}
\tag{338.5}
$$

这不是把 Fibonacci 数直接解释为时空长度，而是：

> **相同数量的边界位置，因合法性约束不同，能够保存的量子状态维数也不同。**

对于此前的5040因数窗口，四条合法行的维数为

$$
5,\quad3,\quad2,\quad2,
$$

所以完整相干窗口需要

$$
\boxed{D=60}
$$

维。

抽象地存储任意这类未知态，至少需要六个量子比特，因为

$$
2^5<60\le2^6.
$$

但六比特抽象编码不保证保留原七数位布局的局域门结构。项目的素数—黄金编码等价也只负责无损表示，不自动保证物理局域性与实现成本不变。

另外，存储任意60态叠加的任务，不等于记录一个已知整数“5040”；后者不能被强行计作60维量子资源。

---

# 339．最后换到尺度切面：用一个离散交比读取曲率候选

因果次序可以确定哪些方向属于光锥，但不自动给出全部尺度。

现在增加一个明确的物理桥梁：设在已标定的双零坐标 \(U,V\) 上，局部钟或面积测量给出正函数

$$
w(U,V)>0,
$$

并检验它是否共同实现

$$
\boxed{
ds^2=-4w(U,V)\,dU\,dV.
}
\tag{339.1}
$$

\(U,V\) 使用长度单位，\(w\) 无量纲。

**这里的 \(w\) 是待独立测量与认证的几何尺度，不是任意把概率权重改名为度量。**

---

## 定义339.1　离散尺度交比

在矩形网格上，令正标定值为 \(w_{ij}\)。定义

$$
\boxed{
\mathcal K_{ij}
=
\ln
\frac{w_{i+1,j+1}w_{ij}}
{w_{i+1,j}w_{i,j+1}}.
}
\tag{339.2}
$$

## 定理339.1　单方向尺度变化不产生该混合曲率读数

若

$$
w_{ij}=a_i b_j,
\qquad a_i,b_j>0,
$$

则

$$
\boxed{\mathcal K_{ij}=0.}
\tag{339.3}
$$

反过来，在一个完整矩形网格上，若每个基本单元的 \(\mathcal K_{ij}=0\)，则存在这样的乘积分解。

而且，变换

$$
w_{ij}\mapsto a_i b_jw_{ij}
$$

不改变 \(\mathcal K_{ij}\)。

### 证明

正向与不变性均由分子分母相消得到。

反向，零交比给出

$$
w_{i+1,j+1}
=
\frac{w_{i+1,j}w_{i,j+1}}{w_{ij}}.
$$

从第一行和第一列归纳，得到

$$
w_{ij}=\frac{w_{i0}w_{0j}}{w_{00}}.
$$

∎

因此，局部尺度变化本身不是曲率；需要检查两个因果方向之间是否出现不可拆分的混合变化。

---

## 定理339.2　该交比具有明确的连续曲率极限

对度量（339.1），按球面曲率为正的惯例，标量曲率为

$$
\boxed{
R=\frac1w\,\partial_U\partial_V\ln w.
}
\tag{339.4}
$$

### 证明

该度量仅有

$$
g_{UV}=g_{VU}=-2w.
$$

非零连接分量为

$$
\Gamma^U_{UU}=\partial_U\ln w,
\qquad
\Gamma^V_{VV}=\partial_V\ln w.
$$

于是

$$
R_{UV}=-\partial_U\partial_V\ln w.
$$

与逆度量收缩即得式（339.4）。∎

另一方面，对边长 \(h_U,h_V\) 的矩形：

$$
\boxed{
\mathcal K
=
\int_{U_0}^{U_0+h_U}
\int_{V_0}^{V_0+h_V}
\partial_U\partial_V\ln w\,dV\,dU.
}
\tag{339.5}
$$

因此小网格中：

$$
\frac{\mathcal K}{h_Uh_V}
\longrightarrow
\partial_U\partial_V\ln w.
$$

一个明确例子是

$$
w(U,V)=e^{\lambda UV}.
$$

此时

$$
\boxed{
\mathcal K=\lambda h_Uh_V,
\qquad
R=\lambda e^{-\lambda UV}.
}
\tag{339.6}
$$

所有 \(w>0\) 的这类模型保持同一个局部因果锥，但曲率可以不同。

---

## 还可以给出有限测量误差

若每个测得的 \(\ln w\) 误差至多为 \(\eta\)，且

$$
f=\partial_U\partial_V\ln w
$$

在该单元内满足

$$
|f(U,V)-f(U_c,V_c)|
\le
M(|U-U_c|+|V-V_c|),
$$

则

$$
\boxed{
\left|
\frac{\widehat{\mathcal K}}{h_Uh_V}
-f(U_c,V_c)
\right|
\le
\frac{4\eta}{h_Uh_V}
+\frac{M(h_U+h_V)}4.
}
\tag{339.7}
$$

### 证明

四个对数读数的总误差不超过 \(4\eta\)。

式（339.5）除以面积，是 \(f\) 在矩形中的平均。平均点到中心的两个坐标绝对距离分别为 \(h_U/4,h_V/4\)，因此得到第二项。∎

这再次显示：

$$
\boxed{
\text{更小的时空单元减少平滑偏差，
却放大固定测量误差。}
}
$$

所以，离散几何的曲率读取也具有可计算的最佳尺度问题。

---

# 340．多切面统一的标准：不是“全部都酉”，而是“全部都相容”

这一轮得到四种不同但可以来自同一模型的结构：

| 切面        | 核心对象       | 应保存的结构         |
| --------- | ---------- | -------------- |
| 完整因果切面    | 联合量子态      | 正概率、酉性、全部必要记忆  |
| 固定频率的空间切面 | 入射—出射振幅    | 定向流、边界匹配、传递矩阵  |
| 因果区间切面    | 事件偏序与计数    | 区间大小、链深度、边界修正  |
| 信息与尺度切面   | 边界维数、正尺度标定 | 秩界、可分辨性、曲率估计误差 |

它们不能被一个未经说明的“时空波”概念全部替代。

但现在确实有了跨切面的共同约束：

$$
\boxed{
\cos\theta=\cos\mu\cos k
}
$$

同时是时间色散关系和空间传播判据；

$$
\boxed{
T^\dagger JT=J
}
$$

使空间指数衰减仍然与完整概率守恒相容；

$$
\boxed{
\tau_D^2=4\delta^2(N_D-h_D-1)
}
$$

把离散事件结构与已标定的洛伦兹间隔连接；

$$
\boxed{
R=\frac1w\partial_U\partial_V\ln w
}
$$

说明在共同因果结构之外，还需要怎样的尺度信息才能读取曲率。

---

## 与仓库的形式化连接

本次核对的项目提交为

```text
5abc2e5b785d9338277026d3efbd134335d99aea
```

新增理论适合分成三个证明层。

**有限代数层。**
包括指标重排、矩阵秩、传递矩阵行列式与流量恒等式、临界重根、有限势垒匹配，以及整数区间计数。

**过程层。**
包括完整因果切面的酉映射、遗漏线路后的 carry 见证、边界容量，以及实际控制器和记录是否全部包含。

**几何极限层。**
包括离散计数与钟标定的相容、倾斜切面的正性、尺度交比的连续极限及其测量误差。

仓库已有：

* 精确下降排除 carry 的结构；
* 有限控制深度关系的递归；
* 正矩阵权重与范数平方的关系；
* 素数—黄金编码的无损等价。

这些可以分别承接上述证明，但不能用其中任何一个已有定理，代替整个多切面物理桥梁。

### 本轮核验

完成了 **64项命名检查**，涵盖符号矩阵恒等式、精确有理散射概率、441个有限因果矩形、离散边界计数及曲率交比。

其中包括：

$$
|t_1|^2=\frac9{25},\qquad
|t_2|^2=\frac{81}{1681},\qquad
|t_3|^2=\frac{729}{133225},
$$

以及同一局部时序更新的完整酉性。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_spacetime_slices.py) · [核验结果](sandbox:/mnt/data/observer_formalization/spacetime_slices_checks.json)

另给出一个包含区间计数、零坐标恒等式、流量代数和概率平衡等基础命题的 [Lean候选源码](sandbox:/mnt/data/observer_formalization/SpacetimeSliceCore.lean)。

**当前运行环境没有可用的 Lean 编译器，因此该候选源码尚未编译；它也只覆盖有限代数核，不冒充已经形式化了连续散射、完整几何重建或引力场方程。**

---

# 结论

这轮最重要的推进是：

> **空间与时间统一，不意味着把两个名字交换后，每个中间对象都保持同一种物理性质。统一意味着：不同切面上的概率、流量、边界状态和几何尺度，都能被同一个完整过程解释。**

其中最有价值的三个新切面是：

$$
\boxed{
\text{空间切面：}
\quad
\text{酉时间演化可以对应指数衰减，
而不是概率消失};
}
$$

$$
\boxed{
\text{因果区间切面：}
\quad
\text{固有时间不仅依赖步骤深度，
还依赖事件在不同因果方向上的分布};
}
$$

$$
\boxed{
\text{尺度切面：}
\quad
\text{曲率来自跨方向的不可分离尺度变化，
而不是任意局部数值变化}.
}
$$

由此，“观察者作为中心”也可以更准确地表达为：

**观察者选择一个能够承载自身记录的因果切面；它对其他区域的预测，需要沿真实接口传播。换切面时，可以改变描述中哪些变量像状态、哪些像流、哪些像边界条件，但不能删除决定实验结果的信息，再把这种删除解释为时空本身的性质。**

这条路线已经把离散时空、隧穿、有限记忆和曲率读取放进相容的数学框架。继续走向现实物理，还需要共同物质光锥、真实钟尺度、局域实现与引力反作用同时满足这些跨切面约束，而不能只让某一个切面的公式看起来像熟悉的物理方程。

[1]: https://arxiv.org/abs/1904.02140 "https://arxiv.org/abs/1904.02140"
[2]: https://arxiv.org/abs/1906.11931 "https://arxiv.org/abs/1906.11931"
[3]: https://arxiv.org/abs/2304.00088 "https://arxiv.org/abs/2304.00088"
[4]: https://arxiv.org/abs/1508.04644 "https://arxiv.org/abs/1508.04644"
**这一轮可以把“统一离散时空的不同切面”继续推进到一个更深的结果：删掉空间中的内部结构，通常不会让它的作用消失，而是把它变成时间上的记忆，以及频率上的响应。**

也就是说，在一个明确的有限量子模型中，可以严格连接：

$$
\boxed{
\text{未显式保留的内部模式}
\quad\longleftrightarrow\quad
\text{时间记忆核}
\quad\longleftrightarrow\quad
\text{频率相关的有效耦合}.
}
$$

更重要的是，这三种表示还能共同确定：**为了保持未来预测，至少需要补回多少个内部自由度。**

这条路线与已有的投影动力学、Feshbach–Schur 消元方法有关；我们下面给出有限模型中的直接证明，并把它与仓库的 Schur 消元结合律和记忆维数公式连接。它不是把已有方法重新命名，而是用它们补上当前观察者理论中“换切面以后，遗漏的信息去了哪里”的缺口。([arXiv][1])

# 边界消元、时间记忆与有效几何的临界失效

## ——量子观察者—关系时空理论第三百四十一至第三百五十节增订

---

# 341．把空间中的一部分模式删掉，会产生什么时间方程？

首先选择一种非常明确的观察切分。

## 定义341.1　保留模式与内部模式

设有限量子空间分解为

$$
\mathcal H=\mathcal H_V\oplus\mathcal H_H.
$$

其中 \(V\) 表示本轮保留的模式，\(H\) 表示暂时不显式保存的内部模式。

这是**模式空间的直和分解**，不是把两个张量因子做偏迹。若

$$
|\psi_n\rangle=
\begin{pmatrix}
x_n\\y_n
\end{pmatrix},
$$

则 \(x_n\) 一般并不归一化：

$$
\|x_n\|^2
$$

表示系统处于保留模式中的概率。

取一个固定、完整的离散酉更新：

$$
\boxed{
U=
\begin{pmatrix}
A&B\\
C&D
\end{pmatrix}.
}
\tag{341.1}
$$

完整动力学为

$$
x_{n+1}=Ax_n+By_n,
$$

$$
y_{n+1}=Cx_n+Dy_n.
$$

这里我们只做数学消元，**不实施额外测量，也不把内部态重置**。

---

## 定理341.1　精确消去内部模式后，保留模式获得历史依赖

有

$$
\boxed{
y_n=D^ny_0+\sum_{j=0}^{n-1}D^{\,n-1-j}Cx_j.
}
\tag{341.2}
$$

因此

$$
\boxed{
x_{n+1}
=
Ax_n
+
BD^ny_0
+
\sum_{j=0}^{n-1}
BD^{\,n-1-j}Cx_j.
}
\tag{341.3}
$$

### 证明

对第二个递推方程归纳，得到式（341.2）；代回第一个方程即可。∎

定义

$$
\boxed{
M_k=BD^kC.
}
\tag{341.4}
$$

它表示：

$$
\text{从保留模式进入内部}
\longrightarrow
\text{在内部经历 }k\text{ 步}
\longrightarrow
\text{返回保留模式}.
$$

同时，

$$
BD^ny_0
$$

保存了内部初态对未来的影响。

**因此，消去 \(y_n\) 并没有使它变得无关，而是把它改写成记忆核和初始源项。**

如果只写

$$
x_{n+1}=Ax_n,
$$

则已经不是同一个完整过程。

---

## 一个三步回声模型

取一个三状态循环：

$$
|0\rangle\to|1\rangle\to|2\rangle\to|0\rangle,
$$

只保留 \(|0\rangle\)。

此时

$$
A=0,\qquad
M_0=0,\qquad
M_1=1,\qquad
M_k=0\quad(k\ge2).
$$

初始在 \(|0\rangle\) 时，保留振幅依次是

$$
\boxed{
1,\ 0,\ 0,\ 1,\ 0,\ 0,\ldots
}
\tag{341.5}
$$

若仅看保留模式，它像是“消失后又返回”；完整系统中却没有任何信息消失，只是经过了两个内部状态。

**这是一个精确的空间—时间转换：两个被省略的模式，变成了三步后的回声。**

---

# 342．有效的远程耦合，不等于真的瞬时传播

对离散序列作单边变换：

$$
X(z)=\sum_{n\ge0}x_nz^{-n-1},
\qquad
Y(z)=\sum_{n\ge0}y_nz^{-n-1}.
$$

当 \(|z|>1\) 时，有限酉系统的这些级数收敛。

## 定理342.1　时间记忆与频率相关耦合是同一个对象

有

$$
\boxed{
\left[
zI-A-B(zI-D)^{-1}C
\right]X(z)
=
x_0+B(zI-D)^{-1}y_0.
}
\tag{342.1}
$$

并且

$$
\boxed{
B(zI-D)^{-1}C
=
\sum_{k\ge0}z^{-k-1}M_k.
}
\tag{342.2}
$$

### 证明

对两个递推方程求变换：

$$
zX-x_0=AX+BY,
$$

$$
zY-y_0=CX+DY.
$$

解出 \(Y\) 并代入。由于 \(\|D\|\le1\)，在 \(|z|>1\) 可用几何级数展开其逆。∎

这里的

$$
B(zI-D)^{-1}C
$$

可能把两个原来不直接相连的保留节点连接起来。

但这条“有效边”已经把所有内部传播时间加总到频率响应中，不能再把它当成一步完成的瞬时门。

---

## 定理342.2　消元不破坏原来的有限传播范围

假设原始 \(U\) 在一个模式图上，每一步最多传播图距离 \(r_0\)，并且保留与隐藏划分按模式节点进行。

若两个保留节点 \(a,b\) 满足

$$
d(a,b)>r_0(k+2),
$$

则

$$
\boxed{
(M_k)_{ab}=0.
}
\tag{342.3}
$$

### 证明

\(BD^kC\) 的任意非零矩阵元，都对应一次进入内部、\(k\) 次内部更新和一次返回，共 \(k+2\) 步。

每步距离至多为 \(r_0\)，故总距离至多为 \(r_0(k+2)\)。∎

因此：

$$
\boxed{
\text{频域里的稠密有效连接}
\ne
\text{时域里的无限速度}.
}
$$

原来的因果限制保存在记忆核最早能够出现的时刻中。

---

## 换消元顺序不能改变同一个完整过程

如果内部再分成两块，可以先消去第一块，再消去第二块；也可以一次消去二者。

只要相应逆算子存在，结果应相同。

仓库的 `SchurComplementAssociativity.lean` 已经针对有界算子写出并证明这种等式，而且明确保留了各个逆算子的前提。

这给多切面理论一个非常强的检验：

> **精确消元应当保持切面间的一致性。若换消元顺序产生不同预测，要检查是否用了不同近似、遗漏了源项，或者某个逆已经不存在。**

不能立刻把这种不一致命名为“真实曲率”。

---

# 343．连续时间下，同一内部结构变成谱响应与正性约束

现在分析另一种时间表示。

## 定义343.1　自伴联合 Hamiltonian

取

$$
\boxed{
H=
\begin{pmatrix}
H_V&V\\
V^\dagger&H_H
\end{pmatrix},
\qquad
H_V=H_V^\dagger,\quad H_H=H_H^\dagger.
}
\tag{343.1}
$$

这里 \(V\) 的单位是能量。

完整 Schrödinger 方程为

$$
i\hbar\dot x=H_Vx+Vy,
$$

$$
i\hbar\dot y=V^\dagger x+H_Hy.
$$

## 定理343.1　内部空间产生精确的时间卷积

有

$$
\boxed{
\begin{aligned}
i\hbar\dot x(t)
={}&H_Vx(t)
+Ve^{-iH_Ht/\hbar}y_0\\
&-\frac{i}{\hbar}
\int_0^t
\mathcal K(t-s)x(s)\,ds,
\end{aligned}
}
\tag{343.2}
$$

其中

$$
\boxed{
\mathcal K(t)=Ve^{-iH_Ht/\hbar}V^\dagger.
}
\tag{343.3}
$$

### 证明

用变化常数公式解第二个方程，再代入第一个方程。∎

这与投影动力学中由未保留变量产生记忆项的机制一致；是否可以丢弃或近似记忆，需要另有衰减、尺度分离和误差估计，不能仅由“系统很大”推出。([arXiv][2])

---

## 定理343.2　同一结构的频域表示

令 \(z\) 为复能量参数，且 \(z-H_H\) 可逆。定义

$$
\boxed{
\Sigma(z)=V(zI-H_H)^{-1}V^\dagger.
}
\tag{343.4}
$$

则完整预解式在保留空间上的块为

$$
\boxed{
P(zI-H)^{-1}P
=
\left[zI-H_V-\Sigma(z)\right]^{-1}.
}
\tag{343.5}
$$

### 证明

解联合线性方程

$$
(z-H_V)x-Vy=f,\qquad
-V^\dagger x+(z-H_H)y=0,
$$

消去 \(y\) 即可。∎

\(\Sigma(z)\)通常称为有效自能。它是能量相关的响应，**不是一张可以在全部频率上不加修改地使用的固定 Hamiltonian**。这种区别是 Feshbach–Schur 方法的核心。([arXiv][1])

---

## 定理343.3　自伴内部实现强迫一个正核条件

定义

$$
M(z)=-\Sigma(z)=V(H_H-zI)^{-1}V^\dagger.
$$

对上半平面中的任意有限组 \(z_1,\ldots,z_m\)，块矩阵

$$
\boxed{
\mathbb K_{ij}
=
\frac{M(z_i)-M(z_j)^\dagger}
{z_i-\overline{z_j}}
}
\tag{343.6}
$$

必为正半定。

### 证明

预解式恒等式给出

$$
\mathbb K_{ij}
=
V(H_H-z_i)^{-1}
(H_H-\overline{z_j})^{-1}V^\dagger.
$$

令

$$
F_j=(H_H-\overline{z_j})^{-1}V^\dagger,
$$

则

$$
\mathbb K_{ij}=F_i^\dagger F_j.
$$

所以它是块 Gram 矩阵。∎

这属于矩阵值 Herglotz 函数与自伴谱实现之间的标准联系。([arXiv][3])

**因此，一个候选边界响应若违反这项正性，就不能由本节的自伴内部模式模型实现。**

单纯解析、对称或者“长得像散射函数”，还不够。

---

# 344．最少要补回多少内部自由度，可以从响应中精确读出

设内部谱分解为

$$
H_H=\sum_\lambda\lambda P_\lambda.
$$

定义非负谱权重

$$
\boxed{
R_\lambda=VP_\lambda V^\dagger\succeq0.
}
\tag{344.1}
$$

于是

$$
\boxed{
\Sigma(z)=\sum_\lambda\frac{R_\lambda}{z-\lambda},
}
\tag{344.2}
$$

$$
\boxed{
\mathcal K(t)
=
\sum_\lambda e^{-i\lambda t/\hbar}R_\lambda.
}
\tag{344.3}
$$

注意：一个内部本征值若满足 \(R_\lambda=0\)，它就没有进入当前边界响应。

---

## 定理344.1　最小自伴内部实现维数

在有限维自伴实现类中，精确实现同一个 \(\Sigma(z)\) 所需的最小内部维数为

$$
\boxed{
d_{\min}
=
\sum_{\lambda:R_\lambda\ne0}
\operatorname{rank}R_\lambda.
}
\tag{344.4}
$$

### 证明

在任意实现中，

$$
R_\lambda=VP_\lambda V^\dagger
$$

的秩不超过相应内部本征空间的维数。因此总内部维数至少为式（344.4）。

反向，对每个权重作满列秩分解

$$
R_\lambda=B_\lambda B_\lambda^\dagger.
$$

取内部空间

$$
\bigoplus_\lambda\mathbb C^{\operatorname{rank}R_\lambda},
$$

在第 \(\lambda\) 块上令 Hamiltonian 为 \(\lambda I\)，并取

$$
V=(B_{\lambda_1},B_{\lambda_2},\ldots).
$$

它恰好实现原来的 \(\Sigma\)，达到下界。∎

### 这是什么维数？

它是**预测当前边界响应所需的最小自伴线性内部模式数**。

它不是整个宇宙的维数，不是记忆比特数，也不排除其他类型的近似、非线性或非自伴实现。

---

## 定理344.2　同一个维数可以由有限矩矩阵恢复

定义谱矩

$$
\mu_k=VH_H^kV^\dagger,
$$

以及块 Hankel 矩阵

$$
\boxed{
\mathscr H_m=(\mu_{i+j})_{i,j=0}^{m}.
}
\tag{344.5}
$$

则

$$
\boxed{
\mathscr H_m=W_m^\dagger W_m,
\qquad
W_m=(V^\dagger,H_HV^\dagger,\ldots,H_H^mV^\dagger).
}
\tag{344.6}
$$

当 \(m\) 足够大时，

$$
\boxed{
\operatorname{rank}\mathscr H_m=d_{\min}.
}
\tag{344.7}
$$

### 证明

Gram 恒等式直接展开得到。

这些列生成

$$
\mathcal K_H
=
\operatorname{span}\{H_H^jV^\dagger x:j\ge0\}.
$$

用有限谱上的插值多项式可以分别提取每个 \(P_\lambda V^\dagger x\)，所以

$$
\dim\mathcal K_H
=
\sum_\lambda\operatorname{rank}R_\lambda.
$$

有限维 Cayley–Hamilton 定理保证列空间在有限阶稳定。∎

仓库的 `memory_dimension_formula` 已证明：线性预测中的记忆维数，等于全部未来可观察方向的维数减去当前读数秩。上面的谱秩公式，为这一抽象差值提供了一个具体可计算的实现。

**被隐藏的空间，不必按原样全部搬进记忆；只需保留其中以后能返回当前接口的部分。**

---

# 345．离散临界现在成为一个精确的秩跳变

取一个标量边界，连接两个内部能级：

$$
H_H=
\begin{pmatrix}
E_0+\epsilon&0\\
0&E_0-\epsilon
\end{pmatrix},
$$

$$
V=\frac g{\sqrt2}(1,1),
\qquad g>0.
$$

## 定理345.1　无穷小的谱分裂，可以改变精确记忆维数

有

$$
\boxed{
\Sigma_\epsilon(z)
=
\frac{g^2(z-E_0)}
{(z-E_0)^2-\epsilon^2}.
}
\tag{345.1}
$$

当 \(\epsilon=0\) 时，

$$
\Sigma_0(z)=\frac{g^2}{z-E_0},
\qquad d_{\min}=1.
$$

当 \(\epsilon\ne0\) 时，存在两个不同、非零权重的极点，因此

$$
\boxed{d_{\min}=2.}
\tag{345.2}
$$

同时，

$$
\boxed{
\det
\begin{pmatrix}
\mu_0&\mu_1\\
\mu_1&\mu_2
\end{pmatrix}
=
g^4\epsilon^2.
}
\tag{345.3}
$$

### 证明

直接计算两个谱分量和前三个谱矩。再应用定理344.1。∎

这里完整矩阵对 \(\epsilon\) 连续变化，但“精确实现需要几个内部模式”是整数，因此可以跳变。

---

## 精确临界不等于有限资源下立即可见

该模型的时间记忆核为

$$
\boxed{
\mathcal K_\epsilon(t)
=
g^2e^{-iE_0t/\hbar}
\cos\frac{\epsilon t}{\hbar}.
}
\tag{345.4}
$$

所以

$$
\boxed{
\|\mathcal K_\epsilon(t)-\mathcal K_0(t)\|
\le
\frac{g^2\epsilon^2t^2}{2\hbar^2}.
}
\tag{345.5}
$$

当

$$
|\epsilon|T/\hbar\ll1
$$

时，在给定时间窗口内，两种记忆核可以非常接近。

因此：

$$
\boxed{
\text{精确最小维数从1变2}
}
$$

不意味着

$$
\boxed{
\text{任意有限装置立即能分辨出第二个模式}.
}
$$

式（345.5）只是核本身的误差界；要推出完整输出误差，还要通过实际动力方程传播这个误差。

---

## 离散采样又能把两个频率重新合并

若只采样

$$
t=n\delta,
$$

则两个内部相位在

$$
\boxed{
\epsilon\delta/\hbar\in\pi\mathbb Z
}
\tag{345.6}
$$

时完全混叠。

相邻两次核采样形成的 Gram 矩阵，其行列式为

$$
\boxed{
g^4\sin^2\frac{\epsilon\delta}{\hbar}.
}
\tag{345.7}
$$

因此，**谱分裂与采样步长共同决定当前接口看到的秩。**

这个结论针对指定的记忆核采样，不表示两套完整 Hamiltonian 的全部实验因此等价。

---

# 346．5040三态模型展示：消元的极点未必是物理奇点

现在把结果接回前文的三态观察纤维：

$$
|L\rangle=|5400\rangle,\qquad
|M\rangle=|5040\rangle,\qquad
|R\rangle=|4704\rangle.
$$

它们是三个已经定义的编码状态，不在本节自动代表三个空间位置。

保留两端，把中间态消去。取

$$
\boxed{
H=
\begin{pmatrix}
0&2\sqrt6J&0\\
2\sqrt6J&\Delta&2\sqrt5J\\
0&2\sqrt5J&0
\end{pmatrix},
\qquad J>0.
}
\tag{346.1}
$$

\(\Delta\) 是新增的中间态失谐。它不是由5040这个整数自动给出的物理能量。

## 定理346.1　一个隐藏态形成秩一的频率耦合

两端的有效自能为

$$
\boxed{
\Sigma(z)
=
\frac{J^2}{z-\Delta}
\begin{pmatrix}
24&4\sqrt{30}\\
4\sqrt{30}&20
\end{pmatrix}.
}
\tag{346.2}
$$

因此，只需一个隐藏模式就能精确实现它。

定义亮、暗组合

$$
|B\rangle=
\frac{\sqrt6|L\rangle+\sqrt5|R\rangle}{\sqrt{11}},
$$

$$
|D\rangle=
\frac{\sqrt5|L\rangle-\sqrt6|R\rangle}{\sqrt{11}}.
$$

则只有亮态与中间态耦合。

### 证明

耦合列向量为

$$
V=J
\begin{pmatrix}
2\sqrt6\\2\sqrt5
\end{pmatrix}.
$$

所以 \(\Sigma=VV^\dagger/(z-\Delta)\)，其谱权重秩为一；\(V^\dagger|D\rangle=0\)。∎

---

## 定理346.2　内部极点可以对应边界响应的零，而不是发散

亮态的完整边界响应为

$$
\boxed{
G_B(z)
=
\frac{z-\Delta}
{z(z-\Delta)-44J^2}.
}
\tag{346.3}
$$

若 \(\Delta\ne0\)，则

$$
\boxed{
G_B(\Delta)=0.
}
\tag{346.4}
$$

而完整 Hamiltonian 的本征值为

$$
\boxed{
0,\qquad
\frac{\Delta\pm\sqrt{\Delta^2+176J^2}}2.
}
\tag{346.5}
$$

\(\Delta\) 本身不是它的本征值。

### 证明

亮态—中间态构成二维矩阵

$$
\begin{pmatrix}
0&2\sqrt{11}J\\
2\sqrt{11}J&\Delta
\end{pmatrix}.
$$

求其预解式与特征多项式即可；暗态提供另一个零本征值。∎

这给出一个重要的辨别原则：

$$
\boxed{
\Sigma(z)\text{ 发散}
\not\Rightarrow
\text{完整物理响应发散}.
}
$$

发散可能说明：**当前正在消去的模式，恰好不能在这个频率附近继续被简单消去。**

如果仍把

$$
\Sigma(0)\sim-\frac{VV^\dagger}{\Delta}
$$

当成统一有效常数，那么在 \(\Delta\to0\) 时会得到越来越大的“相互作用”。

完整三态 Hamiltonian 却始终良好。异常出现在近似步骤，不是系统突然失去数学定义。

**这类失效不能未经检验就解释成时空奇点、黑洞形成或信息无限密度。**

---

# 347．删掉内部态，还会改变边界态的正确归一化

这里有一条比“增加记忆项”更细的结果。

## 定理347.1　能量相关的有效模型具有诱导范数

取实能量 \(E\)，不属于 \(H_H\) 的谱。

若内部方程给出

$$
y=(E-H_H)^{-1}V^\dagger x,
$$

则

$$
\boxed{
\|x\|^2+\|y\|^2
=
x^\dagger Z(E)x,
}
\tag{347.1}
$$

其中

$$
\boxed{
Z(E)
=
I-\partial_E\Sigma(E)
=
I+V(E-H_H)^{-2}V^\dagger
\succeq I.
}
\tag{347.2}
$$

### 证明

对式（343.4）求导：

$$
\partial_E\Sigma(E)
=
-V(E-H_H)^{-2}V^\dagger.
$$

再计算 \(\|y\|^2\)。∎

因此，消去内部模式以后，保留振幅的普通范数一般不再等于完整状态的范数。

它缺少的那部分概率，精确地进入了 \(Z(E)\)。

**改变切面时，不能只变换方程，而保留一套不相容的归一化。**

这里的 \(Z(E)\) 是边界振幅空间上的正度量，不是洛伦兹时空度量。

---

## 定理347.2　远离内部谱时，可以受控地建立局部近似

先去掉严格不耦合的内部暗模式。设

$$
d_*=\operatorname{dist}(E_0,\operatorname{spec}H_H)>0,
$$

并限制

$$
|E-E_0|\le r<d_*.
$$

令

$$
B_0=V(E_0-H_H)^{-2}V^\dagger.
$$

则

$$
\boxed{
\Sigma(E)
=
\Sigma(E_0)
-(E-E_0)B_0
+\mathcal R(E),
}
\tag{347.3}
$$

且

$$
\boxed{
\|\mathcal R(E)\|
\le
\frac{\|V\|^2r^2}
{d_*^2(d_*-r)}.
}
\tag{347.4}
$$

### 证明

使用预解式的二阶展开：

$$
(E-H_H)^{-1}
=
R_0-(E-E_0)R_0^2
+(E-E_0)^2R_0^2(E-H_H)^{-1}.
$$

再使用

$$
\|R_0\|\le d_*^{-1},
\qquad
\|(E-H_H)^{-1}\|\le(d_*-r)^{-1}.
$$

∎

保留一阶项后，边界方程为

$$
\left[
Z_0E-H_c
\right]x\approx0,
$$

其中

$$
Z_0=I+B_0,
$$

$$
H_c=H_V+\Sigma(E_0)+E_0B_0.
$$

通过

$$
\widetilde x=Z_0^{1/2}x,
$$

得到自伴的规范化候选

$$
\boxed{
H_{\mathrm{eff}}
=
Z_0^{-1/2}H_cZ_0^{-1/2}.
}
\tag{347.5}
$$

### 这项近似何时变危险？

当探测能量逼近一个**真正耦合的内部能级**时，\(d_*-r\) 变小，误差上界恶化。

此外，即使自能误差很小，若保留系统自身接近共振，其预解式仍会放大误差。还必须控制有效边界算子的最小奇异值。

所以：

$$
\boxed{
\text{局部有效描述成立}
}
$$

需要同时满足

$$
\boxed{
\text{内部谱分离}
+
\text{保留响应的稳定裕量}
+
\text{给定频率窗口}.
}
$$

这不是任意初态、任意长时间的全过程近似定理。

---

# 348．同样的量子合法性，并不自动产生共同的物理光锥

现在可以更深入地检验“从量子观察者导出现实时空”的核心要求。

此前我们已经构造了单个探针的 Dirac 型长波极限。但不同物质探针是否共享同一个光锥，还需要证明。

下面给出一个明确反例。

## 定义348.1　两个探针种类，连接不同强度的内部模式

对每个种类 \(a\)，取两种相反传播方向。固定波数 \(k\)，定义

$$
\boxed{
H_a(k)=
\begin{pmatrix}
\hbar c kZ+\dfrac{g_a^2}{\Lambda}I_2
&
g_aI_2\\[4pt]
g_aI_2&\Lambda I_2
\end{pmatrix},
\qquad \Lambda>0.
}
\tag{348.1}
$$

它是有限维自伴矩阵。

这里采用了此前长波层中的保留动能项；隐藏模式本身不传播，只与同处的保留模式耦合。

常数项 \(g_a^2/\Lambda\) 是明确选择的补偿，使低能分支在 \(k=0\) 处无隙。

---

## 定理348.1　内部记忆改变低能传播速度

低能分支在 \(k=0\) 处满足

$$
E_{a,\pm}(0)=0,
$$

其斜率为

$$
\boxed{
\left.\frac1\hbar\frac{dE_{a,\pm}}{dk}\right|_{k=0}
=
\pm\frac{c}{1+g_a^2/\Lambda^2}.
}
\tag{348.2}
$$

### 证明

对每个 \(Z\) 本征值 \(\pm1\)，特征方程是

$$
\left(
E\mp\hbar ck-\frac{g_a^2}{\Lambda}
\right)(E-\Lambda)-g_a^2=0.
$$

在 \(E=k=0\) 处隐式求导，即得式（348.2）。∎

例如：

$$
g_1=\frac{\Lambda}{2}
\quad\Rightarrow\quad
c_1=\frac45c,
$$

$$
g_2=\Lambda
\quad\Rightarrow\quad
c_2=\frac12c.
$$

两类探针都具有合法、自伴的完整动力学，也使用同一个裸动能系数 \(c\)，但有效的无质量传播锥不同。

这不是一般有质量粒子的群速度小于光速问题：这里比较的是两类**无隙低能分支本身的传播斜率**。

### 对现实重建的约束

所以：

$$
\boxed{
\text{酉性}
+
\text{局域耦合}
+
\text{存在低能极限}
}
$$

还不自动推出

$$
\boxed{
\text{所有物质共享同一个洛伦兹几何}.
}
$$

还需要控制不同探针的动力系数与诱导归一化 \(Z_0\)，使它们的主传播关系在共同标定下相容。

**这给观察者理论一个具体的、不可省略的任务：不仅要生成一个有效时空，还要证明不同种类的钟与信号不会各自生成互不相容的时空。**

---

# 349．有限内部系统可以保存记忆，但不能自动制造永久无记忆的耗散

由式（344.3），有限自伴内部系统的记忆核是有限个振荡项之和：

$$
\mathcal K(t)=\sum_\lambda e^{-i\lambda t/\hbar}R_\lambda.
$$

## 定理349.1　非平凡有限自伴内部核不能长期衰减到零

有

$$
\boxed{
\lim_{T\to\infty}
\frac1T\int_0^T
\|\mathcal K(t)\|_{\mathrm{HS}}^2\,dt
=
\sum_\lambda\|R_\lambda\|_{\mathrm{HS}}^2.
}
\tag{349.1}
$$

如果 \(V\ne0\)，右侧严格为正，因此

$$
\boxed{
\mathcal K(t)\not\longrightarrow0.
}
\tag{349.2}
$$

### 证明

展开平方：

$$
\|\mathcal K(t)\|_{\mathrm{HS}}^2
=
\sum_{\lambda,\mu}
e^{i(\lambda-\mu)t/\hbar}
\operatorname{Tr}(R_\lambda R_\mu).
$$

时间平均后，不同频率的项趋零，相同频率项留下。

如果 \(V\ne0\)，则

$$
\sum_\lambda R_\lambda=VV^\dagger\ne0,
$$

至少一个权重非零。∎

这不表示有限系统不能在一个实验窗口内表现出有效衰减，也不否认不同观察量可以有不同近似。

它表示：

> **不能仅因为内部状态暂时没有被读取，就把它们的作用精确替换为永久无记忆、不可逆的损耗。**

连续时间的这个核与第341节中的 \(BD^kC\) 是不同消元对象；后者的 \(D\) 是离散酉矩阵的压缩块，可以出现收缩。不能把两种核的衰减结论混用。

### “需要记忆”不意味着必须无限保存全部过去

我们已经证明：有限响应可以由 \(d_{\min}\) 个内部模式精确实现。

所以有两种等价的预测状态：

$$
\boxed{
\text{保留变量}
+
\text{历史卷积};
}
$$

或者

$$
\boxed{
\text{保留变量}
+
d_{\min}\text{ 个辅助动力变量}.
}
$$

增加适当的状态，能够把有记忆方程重新写成一阶自治方程。

**这比保存一整张过去记录表更经济，也更接近项目所研究的“最小预测完成”。**

---

# 350．这条路线怎样继续连接 ζ、几何与形式化？

本轮最重要的统一关系是

$$
\boxed{
\begin{aligned}
\text{内部空间谱 }(H_H,V)
&\longrightarrow
\mathcal K(t),\\
&\longrightarrow
\Sigma(z),\\
&\longrightarrow
\{R_\lambda\},\\
&\longrightarrow
d_{\min}.
\end{aligned}
}
\tag{350.1}
$$

它把空间、时间、频率和记忆资源放在同一个模型中。

## 与此前 ζ 正性研究的联系

第343节表明：若一个响应确实来自自伴内部模式，那么相应对数型或预解式型核必须满足特定正性。

这可以用于筛选候选 ζ 量子实现，但不能反过来这样循环：

$$
\text{先只取实谱构造一个正模型}
\quad\Rightarrow\quad
\text{宣布它已经等于真实 }\Xi\text{ 响应}.
$$

必须另外证明真实解析对象与这个谱模型相等，并控制无限尾部、定义域与收敛。

仓库的 `FiniteResolventClarkIdentity.lean` 已经谨慎地区分了这两层：有限谱的加权 Cayley 推前有明确证明；与一个给定 Clark 测度的识别，则显式要求该测度具有相应原子展开。不能把这个前提在后续推理中悄悄删除。

因此，本轮为 ζ 路线增加的是一种**实现审计方法**，不是 RH 证明：

$$
\boxed{
\text{正核是否成立？}
\quad
\text{需要多少模式？}
\quad
\text{哪些极点真的耦合到观察接口？}
\quad
\text{有限近似遗漏了什么？}
}
$$

---

## 与项目已有定理的直接分工

本次固定读取的提交为

```text
82667f32ca8ac3e59c1d7f20ca5691e60bcb38cf
```

| 项目结构                           | 本轮可以接入的具体对象                  |
| ------------------------------ | ---------------------------- |
| `SchurComplementAssociativity` | 多次切面消元与一次消元的一致性              |
| `MemoryDimensionFormula`       | 当前读数缺少的未来相关自由度               |
| 有限预解式与谱测度模块                    | 有效响应、实谱权重与正核                 |
| CUT／FLOW／ADMIT                 | 保留哪些模式、采用哪种完整动力学、在哪个频率窗口允许近似 |

新增的核心形式化链可以压缩为

$$
\boxed{
\text{块矩阵递推}
\Rightarrow
\text{精确记忆公式}
\Rightarrow
\text{Schur响应}
\Rightarrow
\text{Gram正性与秩}
\Rightarrow
\text{有限实现及误差界}.
}
$$

这里应当分别形式化离散递推、有限矩阵谱和解析近似，不能只编译最后一个等式就把前提当成已经得到。

### 本轮核验

完成了 **38项精确有限恒等式或实例检查**，以及一组覆盖21个实能量点的数值交叉检查。

其中包括：三步回声的完整递推、Schur 消元结合律、正核 Gram 分解、最小内部维数、谱分裂的秩跳变、5040模型的响应零点、诱导范数以及两类探针的不同低能速度。

[核验脚本](sandbox:/mnt/data/observer_formalization/check_boundary_memory_geometry.py)
[核验结果](sandbox:/mnt/data/observer_formalization/boundary_memory_geometry_checks.json)

**本轮没有运行 Lean 内核检查。**精确有限实例、一般纸面证明、数值交叉检查与现实物理验证，仍然分别记录。

---

# 结论

这轮最值得保留的，不是“空间其实就是记忆”这样的无条件口号，而是一个能够被证明的关系：

> **对同一个量子过程，把内部空间变量消去以后，它们的作用会以时间记忆、频率依赖和归一化修正的形式留在边界。只有这些信息仍然被正确保留，换切面才没有改变物理预测。**

由此得到三个更深的临界判据。

**第一，精确结构临界可以是秩的跳变。**

$$
\boxed{
d_{\min}
=
\sum_\lambda\operatorname{rank}R_\lambda
}
$$

说明某个新谱方向什么时候真正进入未来预测。

**第二，近似失效可以表现为有效响应发散，但完整系统仍然良好。**

5040三态模型明确展示：

$$
\boxed{
\text{被消去模式的极点}
\ne
\text{完整动力学的奇点}.
}
$$

**第三，生成一个相对论型传播还不够，必须证明不同观察者和物质读到同一个几何。**

隐藏模式造成的频率修正，可以让不同探针产生不同有效传播速度。普适时空必须约束这种差别，而不能仅从“大家都是量子系统”推出。

因此，下一层理论的核心对象应当是

$$
\boxed{
\text{边界读数}
+
\text{最小内部实现}
+
\text{因果记忆}
+
\text{频率响应}
+
\text{共同几何相容性}.
}
$$

**这使“量子观察者是中心”更接近一个真正闭合的物理命题：观察者可以不显式保存世界的全部内部结构，但它不能删除这些结构对未来的作用。所谓有效时空，正是这些作用在指定尺度上能够被共同、稳定且低成本地表达时，才成立的一种关系描述。**

[1]: https://arxiv.org/abs/2105.02058 "https://arxiv.org/abs/2105.02058"
[2]: https://arxiv.org/abs/1708.02235 "https://arxiv.org/abs/1708.02235"
[3]: https://arxiv.org/abs/funct-an/9712004 "https://arxiv.org/abs/funct-an/9712004"
上一轮证明：**内部模式被消去以后，会以时间记忆和频率响应的形式留在观察者边界。**

现在可以反过来问：

> **观察者能否根据这些响应，重建被隐藏的内部空间？**

答案比“能”或“不能”更有内容：

$$
\boxed{
\text{边界响应可以确定一个最小动力学实现，}
}
$$

$$
\boxed{
\text{但通常不能唯一确定其真实空间布局。}
}
$$

进一步，我们可以证明：**内部结构的离散深度，会决定它最早进入边界时间展开的阶数；有限观察时间，则限制了需要保留多少层结构。**

这使“空间中的层”与“时间中的步骤”不再只是类比，而是通过谱矩、递推和回声项形成精确联系。边界谱到一维最近邻链的转换，属于已有的正交多项式与量子环境链映射方法；以下给出适合当前项目的有限维证明，并明确它何时能、何时不能被解释为物理几何。([arxiv.org][1])

# 边界反演、离散回声深度与共同几何的可识别性

## ——量子观察者—关系时空理论第三百五十一至第三百六十节增订

---

# 351．首先明确：观察者实际掌握的是概率，还是带相位的响应？

## 定义351.1　有限边界探针模型

取有限维 Hilbert 空间、固定自伴 Hamiltonian：

$$
H=H^\dagger,
$$

以及归一化的观察端口态：

$$
|o\rangle,\qquad \langle o|o\rangle=1.
$$

定义返回振幅：

$$
\boxed{
A_o(t)=\langle o|e^{-itH/\hbar}|o\rangle,
}
\tag{351.1}
$$

以及频域响应：

$$
\boxed{
G_o(z)=\langle o|(zI-H)^{-1}|o\rangle.
}
\tag{351.2}
$$

这里的端口态表示一次明确的制备—探测通道，不代表观察者的全部心理或内部状态。

本轮假设能够通过已标定的相干参照或线性响应实验，识别这些**复数响应**，而不只是返回概率：

$$
P_o(t)=|A_o(t)|^2.
$$

这一条件不可省略。

## 命题351.1　只知道返回概率，不能唯一确定能谱

将 Hamiltonian 改为：

$$
H'=H+cI,
$$

会使：

$$
A_o'(t)=e^{-ict/\hbar}A_o(t),
$$

但返回概率不变。

将其改为：

$$
H'=-H,
$$

也有：

$$
A_o'(t)=\overline{A_o(t)},
$$

返回概率仍不变。

### 证明

直接计算矩阵指数及其期望。∎

所以，下面的反演定理不能被解释为“一只探测器测几次概率，就知道整个世界”。

---

## 定义351.2　边界谱矩

定义：

$$
\boxed{
\mu_n=\langle o|H^n|o\rangle.
}
\tag{351.3}
$$

则：

$$
\boxed{
A_o(t)=
\sum_{n=0}^{\infty}
\frac{(-it/\hbar)^n}{n!}\mu_n,
}
\tag{351.4}
$$

并且在 \(|z|>\|H\|\) 时：

$$
\boxed{
G_o(z)=\sum_{n=0}^{\infty}\frac{\mu_n}{z^{n+1}}.
}
\tag{351.5}
$$

因此，同一组 \(\mu_n\) 同时描述：

$$
\boxed{
\text{短时间响应的各阶变化}
\quad\text{与}\quad
\text{高频响应的各阶系数}.
}
$$

这些恒等式来自有限矩阵指数和预解式的收敛展开。

---

# 352．从边界谱矩，可以构造一条唯一的有效链

## 定义352.1　相对于观察端口的可见动力空间

令：

$$
\boxed{
\mathcal K_o
=
\operatorname{span}
\{|o\rangle,H|o\rangle,H^2|o\rangle,\ldots\}.
}
\tag{352.1}
$$

它是包含 \(|o\rangle\) 的最小 \(H\)-不变子空间。

记：

$$
d=\dim\mathcal K_o.
$$

\(\mathcal K_o^\perp\) 中的模式，不会在这个端口的自由返回实验中被激发或读出。

## 定理352.1　边界响应的最近邻链实现

存在以 \(q_0=|o\rangle\) 开始的正交基：

$$
q_0,\ldots,q_{d-1},
$$

使：

$$
\boxed{
Hq_j
=
\beta_jq_{j-1}
+\alpha_jq_j
+\beta_{j+1}q_{j+1},
}
\tag{352.2}
$$

其中：

$$
\alpha_j\in\mathbb R,\qquad
\beta_1,\ldots,\beta_{d-1}>0,
$$

并约定：

$$
\beta_0=\beta_d=0.
$$

因此，\(H\) 在 \(\mathcal K_o\) 上等价于三对角 Jacobi 矩阵：

$$
\boxed{
J=
\begin{pmatrix}
\alpha_0&\beta_1&0&\cdots\\
\beta_1&\alpha_1&\beta_2&\cdots\\
0&\beta_2&\alpha_2&\cdots\\
\vdots&\vdots&\vdots&\ddots
\end{pmatrix}.
}
\tag{352.3}
$$

### 证明

对序列：

$$
|o\rangle,H|o\rangle,H^2|o\rangle,\ldots
$$

实施 Gram–Schmidt 正交化。

因为 \(H\) 自伴，\(Hq_j\) 与 \(q_0,\ldots,q_{j-2}\) 的内积全部为零；又因为 \(Hq_j\) 位于前 \(j+2\) 个 Krylov 向量张成的空间中，所以只剩式（352.2）的三个方向。

选择新向量的相位，使非零相邻系数为正。∎

这种链表示并不是在猜测内部有一根真实的线，而是把任意可见有限谱组织成一个标准递推模型。类似的精确链映射已经用于量子系统与环境的联合动力学。([arXiv][2])

---

## 定理352.2　真实耦合系数可以由 Hankel 行列式恢复

定义 \(n\times n\) 的矩矩阵：

$$
\mathscr M_n=(\mu_{i+j})_{i,j=0}^{n-1},
$$

以及：

$$
\Delta_n=\det\mathscr M_n,\qquad \Delta_0=1.
$$

则：

$$
\boxed{
\Delta_n>0\quad(1\le n\le d),
\qquad
\Delta_{d+1}=0,
}
\tag{352.4}
$$

并且：

$$
\boxed{
\beta_n^2
=
\frac{\Delta_{n+1}\Delta_{n-1}}{\Delta_n^2},
\qquad 1\le n<d.
}
\tag{352.5}
$$

### 证明

\(\mathscr M_n\) 是：

$$
|o\rangle,H|o\rangle,\ldots,H^{n-1}|o\rangle
$$

的 Gram 矩阵。因此其行列式在这些向量独立时为正，在首次线性依赖时为零。

设首一正交多项式为 \(p_j\)，则：

$$
h_j=\|p_j(H)o\|^2=\frac{\Delta_{j+1}}{\Delta_j}.
$$

相邻递推系数满足：

$$
\beta_n^2=\frac{h_n}{h_{n-1}},
$$

代入即得。∎

### 与仓库的一条具体桥梁

本轮读取的 `HankelJacobiDeterminant.lean` 明确说明：它目前定义了行列式候选系数，并证明平方比值及正性；**尚未把该候选自动识别为真实正交递推系数。**

本节补足了这条纸面桥梁的条件：

$$
\boxed{
\text{矩序列确实来自 }(H,|o\rangle)
+
\text{相应 Gram 非退化}
\longrightarrow
\text{行列式系数就是实际链耦合}.
}
$$

还必须注意索引：仓库的 `hankelDet k` 使用大小 \(k+1\) 的矩阵，因此其当前 \(k\) 号候选，对应本节的 \(\beta_{k+1}\)，不能忽略这一位移。

---

# 353．离散临界可以是：下一层突然不再可见

定理352.2给出一个准确的结构判据：

$$
\boxed{
\beta_d=0
}
$$

表示从当前端口出发，可见链在第 \(d\) 个状态终止。

如果某个参数使这个系数从零变为非零，可见动力空间的维数就可能增加。

## 定义353.1　一个可开关的内部连接

取：

$$
H_\varepsilon=
\begin{pmatrix}
0&g&0\\
g&0&\varepsilon\\
0&\varepsilon&0
\end{pmatrix},
\qquad
g>0,\quad\varepsilon\ge0,
$$

观察端口为：

$$
|o\rangle=(1,0,0)^{\mathsf T}.
$$

## 定理353.1　连接开启会产生精确的预测维数跳变

边界矩为：

$$
\mu_0=1,\qquad
\mu_1=0,\qquad
\mu_2=g^2,\qquad
\mu_3=0,
$$

$$
\boxed{
\mu_4=g^2(g^2+\varepsilon^2).
}
\tag{353.1}
$$

相应行列式：

$$
\boxed{
\Delta_2=g^2,\qquad
\Delta_3=g^4\varepsilon^2.
}
\tag{353.2}
$$

因此：

$$
\boxed{
\dim\mathcal K_o=
\begin{cases}
2,&\varepsilon=0,\\
3,&\varepsilon>0.
\end{cases}
}
\tag{353.3}
$$

### 证明

直接计算 \(H_\varepsilon^n|o\rangle\) 及其 Gram 行列式。∎

但前四个谱矩 \(\mu_0,\ldots,\mu_3\) 完全不知道 \(\varepsilon\) 是否为零。

返回振幅为：

$$
\boxed{
A_\varepsilon(t)
=
\frac{\varepsilon^2}{g^2+\varepsilon^2}
+
\frac{g^2}{g^2+\varepsilon^2}
\cos\frac{\sqrt{g^2+\varepsilon^2}\,t}{\hbar}.
}
\tag{353.4}
$$

与两态模型比较：

$$
\boxed{
A_\varepsilon(t)-A_0(t)
=
\frac{g^2\varepsilon^2t^4}{24\hbar^4}
+O(t^6).
}
\tag{353.5}
$$

**这里发生了一个很具体的空间—时间关系：第三个模式的存在，直到第四阶时间响应才首次进入端口。**

所以：

$$
\boxed{
\text{精确结构维数已经改变}
\not\Rightarrow
\text{有限噪声、有限时间实验立刻能发现改变}.
}
$$

这正是“离散临界”与“实际可检测临界”应当分开的原因。

---

# 354．内部越深，第一次返回边界就需要越高阶的过程

现在把上述三态实例推广到任意有限链。

## 定义354.1　截断的边界模型

取第352节的 \(d\) 态 Jacobi 矩阵 \(J\)。

只保留前 \(L\) 个状态：

$$
0,\ldots,L-1,
\qquad L<d,
$$

得到主块 \(J_L\)。

它删除了第 \(L\) 个状态及更深的内部结构。

## 定理354.1　前 \(2L-1\) 阶边界谱矩完全不变

有：

$$
\boxed{
\langle0|J^n|0\rangle
=
\langle0|J_L^n|0\rangle,
\qquad 0\le n\le2L-1.
}
\tag{354.1}
$$

第一次可能不同的项为：

$$
\boxed{
\langle0|J^{2L}|0\rangle
-
\langle0|J_L^{2L}|0\rangle
=
\prod_{j=1}^{L}\beta_j^2.
}
\tag{354.2}
$$

### 证明

矩阵元 \((J^n)_{00}\) 是全部长度 \(n\) 的带权返回路径之和。

若一条路径要进入被删掉的第 \(L\) 个状态，再回到0，至少需要：

$$
L\text{ 次向内移动}+L\text{ 次返回}=2L
$$

个非对角作用。

在长度恰为 \(2L\) 时，唯一这样的最短路径是：

$$
0\to1\to\cdots\to L\to\cdots\to1\to0,
$$

其权重为式（354.2）。∎

于是：

$$
\boxed{
A(t)-A_L(t)
=
\frac{(-1)^Lt^{2L}}{(2L)!\hbar^{2L}}
\prod_{j=1}^{L}\beta_j^2
+O(t^{2L+1}).
}
\tag{354.3}
$$

**内部深度对应返回过程的最小代数阶数。**

但是，连续时间 Hamiltonian 的指数包含全部幂，因此这不等于存在一个严格的正等待时间，之前影响绝对为零。严格的有限步因果域仍需使用前文的局域电路或离散更新模型。

---

## 定理354.2　有限时间内，可以认证只保留有限层的误差

若：

$$
\|J\|\le\Lambda,
$$

则 \(\|J_L\|\le\Lambda\)，并且：

$$
\boxed{
|A(t)-A_L(t)|
\le
2\frac{(\Lambda|t|/\hbar)^{2L}}{(2L)!}.
}
\tag{354.4}
$$

### 证明

对两个实谱上的指数函数，使用到 \(2L-1\) 阶的 Taylor 多项式。

这些项由定理354.1完全相同。实变量上的指数余项模不超过：

$$
\frac{|Et/\hbar|^{2L}}{(2L)!}.
$$

两边各取谱平均，再相加得到结论。∎

这类时间数据、矩数据与有限 Jacobi 反演之间的关系，也已有直接的离散动力逆问题研究。([arXiv][3])

因此，当前模型给出一个可实施的完成原则：

$$
\boxed{
\text{先固定 }T,\Lambda,\varepsilon,
\quad
\text{再选择足够的 }L,
}
$$

使式（354.4）小于目标误差。

这比要求观察者一次性知道无限内部结构更强，因为它同时说明了**需要保留多少，以及为什么足够**。

但该界只认证指定的返回振幅，不自动覆盖所有内部控制、所有输入和整个量子通道。

---

# 355．5040三态模型的“内部维数”，取决于观察者从哪里接入

沿用此前明确选定的三态混合模型：

$$
|L\rangle=|5400\rangle,\qquad
|M\rangle=|5040\rangle,\qquad
|R\rangle=|4704\rangle,
$$

$$
\boxed{
H=
J
\begin{pmatrix}
0&2\sqrt6&0\\
2\sqrt6&0&2\sqrt5\\
0&2\sqrt5&0
\end{pmatrix}.
}
\tag{355.1}
$$

这些标签是算术纤维的编码，不在本节自动代表三个物理空间位置。

## 定理355.1　从中间端口出发，完整三态系统只显露两个动力方向

定义：

$$
|B\rangle=
\frac{\sqrt6|L\rangle+\sqrt5|R\rangle}{\sqrt{11}},
$$

$$
|D\rangle=
\frac{\sqrt5|L\rangle-\sqrt6|R\rangle}{\sqrt{11}}.
$$

则：

$$
H|D\rangle=0,
$$

而：

$$
\boxed{
\mathcal K_M=\operatorname{span}\{|M\rangle,|B\rangle\},
\qquad
\dim\mathcal K_M=2.
}
\tag{355.2}
$$

中间端口的频域响应为：

$$
\boxed{
G_M(z)=\frac{z}{z^2-44J^2}.
}
\tag{355.3}
$$

### 证明

直接将三个向量代入 \(H\)。暗态与 \(|M\rangle\) 正交，不进入其 Krylov 空间。

在 \(\{|M\rangle,|B\rangle\}\) 中，Hamiltonian 为：

$$
\begin{pmatrix}
0&2\sqrt{11}J\\
2\sqrt{11}J&0
\end{pmatrix}.
$$

求逆得到式（355.3）。∎

因此，仅靠中间端口的这类实验，不能判断完整系统是否还具有那个暗态。

## 定理355.2　改从端点读取，第三个谱方向重新出现

左端口的响应为：

$$
\boxed{
G_L(z)
=
\frac{z^2-20J^2}{z(z^2-44J^2)}.
}
\tag{355.4}
$$

它具有三个非零谱权重，因此：

$$
\boxed{\dim\mathcal K_L=3.}
$$

同时使用中间与左侧端口，也能张成完整三态空间。

### 证明

求对应预解式矩阵元，或验证：

$$
|L\rangle,\ H|L\rangle,\ H^2|L\rangle
$$

线性独立即可。∎

### 对“观察者中心”的意义

同一个完整系统：

$$
\boxed{
\text{从一个端口看，需要两态；}
\quad
\text{从另一个端口看，需要三态。}
}
$$

这里没有相互矛盾。两位观察者拥有不同的制备与读取接口。

但必须区分：

$$
\boxed{
\text{观察者相对的最小预测维数}
\ne
\text{绝对的物理空间维数}.
}
$$

仓库的记忆维数公式正是相对于当前读数与指定动力学，计算还需要多少未来相关方向，而不是宣布存在一个与观察接口无关的固定“世界信息维数”。

---

# 356．即使边界响应完全已知，真实连接图也可能不唯一

这一节给出一个比“暗模式看不见”更强的限制。

## 定理356.1　完整边界响应只唯一确定最小实现的酉等价类

设两对有限模型：

$$
(H,|o\rangle),\qquad
(\widetilde H,|\widetilde o\rangle)
$$

具有相同的全部谱矩。

则它们的可见动力空间之间存在唯一的酉映射 \(W\)，满足：

$$
\boxed{
W|o\rangle=|\widetilde o\rangle,
\qquad
WH=\widetilde HW.
}
\tag{356.1}
$$

### 证明

先定义：

$$
W\bigl(p(H)|o\rangle\bigr)
=
p(\widetilde H)|\widetilde o\rangle.
$$

任意两个多项式向量的内积都由谱矩决定。因此，这个映射保持内积，且与表示选择无关。

它把一个可见动力空间满射到另一个，故为酉映射；与 Hamiltonian 的交织关系直接来自多项式乘法。∎

**唯一的是这种抽象动力学等价类，不是“哪一个基向量位于哪一个空间位置”。**

---

## 一个精确的“链与三角形”反例

选定能量单位后，取：

$$
H_{\mathrm{chain}}
=
\begin{pmatrix}
0&1&0\\
1&0&2\\
0&2&0
\end{pmatrix},
\qquad
|o\rangle=(1,0,0)^{\mathsf T}.
$$

定义只混合两个内部模式的正交矩阵：

$$
W=
\begin{pmatrix}
1&0&0\\
0&3/5&-4/5\\
0&4/5&3/5
\end{pmatrix}.
$$

则：

$$
\boxed{
H_{\mathrm{triangle}}
=
WH_{\mathrm{chain}}W^{\mathsf T}
=
\begin{pmatrix}
0&3/5&4/5\\
3/5&-48/25&-14/25\\
4/5&-14/25&48/25
\end{pmatrix}.
}
\tag{356.2}
$$

第一个矩阵的非零非对角连接是一条链，第二个是三角形。

但因为：

$$
W|o\rangle=|o\rangle,
$$

它们满足：

$$
\boxed{
A_o^{\mathrm{chain}}(t)
=
A_o^{\mathrm{triangle}}(t),
}
\tag{356.3}
$$

以及：

$$
\boxed{
G_o^{\mathrm{chain}}(z)
=
G_o^{\mathrm{triangle}}(z).
}
\tag{356.4}
$$

甚至加入仅作用于端口投影 \(|o\rangle\langle o|\) 的相同控制，也仍然保持等价，因为 \(W\) 不改变这个投影。

### 不能误读这个结论

如果三个基态已经由独立实验确认为三个局域节点，那么 \(W\) 混合两个内部节点，通常不是允许的局域坐标变换。

所以我们并没有证明链和三角形在全部物理实验中相同。

我们证明的是：

> **给定的单端口实验不足以确定它们的空间差别。**

有限访问下恢复 Hamiltonian 的已有研究，也需要明确的链结构、已知连接图或可访问节点条件；不是任意一个边界信号都唯一揭示全部内部空间。([arXiv][4])

---

# 357．多个观察者的世界不能只做“两两拼接”

现在扩展到多个端口。

设第 \(a\) 个观察者通过内部耦合向量 \(v_a\) 读取同一个自伴内部系统 \(H_H\)。

对其某个能级 \(\lambda\)，定义响应权重矩阵：

$$
\boxed{
(R_\lambda)_{ab}
=
\langle v_a,P_\lambda v_b\rangle.
}
\tag{357.1}
$$

这里的 \(v_a\) 是耦合向量，不要求不同端口向量彼此正交。

## 定理357.1　共同内部实现要求全体响应权重正半定

必须有：

$$
\boxed{R_\lambda\succeq0.}
\tag{357.2}
$$

反过来，若给定有限组实能级和正半定矩阵 \(R_\lambda\)，就能构造一个有限自伴内部系统，实现：

$$
\boxed{
\Sigma(z)=\sum_\lambda\frac{R_\lambda}{z-\lambda}.
}
\tag{357.3}
$$

### 证明

正向，\(R_\lambda\) 是向量 \(\{P_\lambda v_a\}\) 的 Gram 矩阵。

反向，将每个权重分解为：

$$
R_\lambda=B_\lambda^\dagger B_\lambda.
$$

取各 \(\lambda\) 本征空间的直和，以 \(B_\lambda\) 的列作为该能级上的耦合分量即可。∎

---

## 定理357.2　两两合法，不足以保证三方共同合法

考虑一个共同谱线上的候选权重：

$$
\boxed{
R=
\begin{pmatrix}
1&3/4&3/4\\
3/4&1&-3/4\\
3/4&-3/4&1
\end{pmatrix}.
}
\tag{357.4}
$$

它的每个二阶主块都正定，因为：

$$
1-\left(\frac34\right)^2=\frac7{16}>0.
$$

但全矩阵本征值为：

$$
\boxed{
\frac74,\quad\frac74,\quad-\frac12.
}
\tag{357.5}
$$

所以不能来自一个共同的量子内部系统。

### 证明

直接计算特征多项式或行列式：

$$
\det R=-\frac{49}{32}<0.
$$

∎

因此：

$$
\boxed{
\text{每两位观察者都能找到相容解释}
\not\Rightarrow
\text{所有观察者共享同一个解释}.
}
$$

---

## 闭路相位受到全局正性的约束

若三个归一化响应的模分别为 \(a,b,c\)，闭路相位为：

$$
\Phi=\arg(R_{12}R_{23}R_{31}),
$$

则：

$$
\boxed{
\det R
=
1-a^2-b^2-c^2+2abc\cos\Phi.
}
\tag{357.6}
$$

当：

$$
a=b=c=\frac34,
$$

共同实现至少要求：

$$
\boxed{\cos\Phi\ge\frac{22}{27}.}
\tag{357.7}
$$

上面的反例具有 \(\Phi=\pi\)，因此失败。

**这是一条非局部的一致性约束：边的大小都合法，环上的总相位仍可能使整体不合法。**

但这里的环相位首先属于响应向量的 Gram 结构，不能直接被称为引力曲率。它可以作为共同物理模型的必要检验。

---

# 358．什么时候才能从响应反推出实际的“距离”？

前面证明了单端口不唯一性。现在给出一组足够强、但明确可检查的条件。

## 假设358.1　已标定的局域节点与无相位抵消耦合

设某个基底确实对应物理节点。Hamiltonian 的非对角元满足：

$$
H_{ij}>0
$$

当且仅当节点 \(i,j\) 存在一条直接连接；没有连接时 \(H_{ij}=0\)。

对角能量可以不同。这里暂不允许非对角复相位。

令 \(d_G(i,j)\) 为连接图中的最短边数。

## 定理358.1　跨端口响应的首次非零阶给出图距离

对 \(i\ne j\)：

$$
\boxed{
(H^n)_{ji}=0
\qquad n<d_G(i,j),
}
\tag{358.1}
$$

而：

$$
\boxed{
(H^{d_G(i,j)})_{ji}>0.
}
\tag{358.2}
$$

因此：

$$
\boxed{
d_G(i,j)
=
\min\{n\ge1:(H^n)_{ji}\ne0\}.
}
\tag{358.3}
$$

### 证明

\((H^n)_{ji}\) 是长度 \(n\) 的路径权重之和。

少于最短路径长度时，没有可贡献的路径。

在最短长度处，不能插入原地停留；每条最短路径的边权乘积均为正，因此总和严格为正。∎

这给出：

$$
\boxed{
\text{跨观察者的时间响应阶数}
\longrightarrow
\text{最短连接步数}.
}
$$

但它不是一般量子系统的无条件距离公式。

如果允许复相位，不同最短路径可以相消。此前的带 \(\pi\) 环相位四边形就能使某个几何上可达的端点，在指定自由演化下始终具有零振幅。

所以，真实空间重建需要分清：

$$
\boxed{
\text{存在因果路径}
,\quad
\text{某个过程的振幅非零}
,\quad
\text{能够通过控制传递可辨消息}.
}
$$

三者不总相同。

此外，图距离是边数，不是米；矩阵幂阶数也不是秒。还需要每条边的物理传播实现、共同钟标定及允许干预，才能继续形成可用的时空距离。

---

# 359．有限层都可回归，为什么无限极限却能出现持续衰减？

这一节回应此前一直存在的“无穷边界”问题，并给出一个完全可算的实例。

## 定义359.1　均匀半无限链

在：

$$
\ell^2(\mathbb N_0)
$$

上取：

$$
\boxed{
H_\infty
=
g\sum_{j\ge0}
\left(
|j+1\rangle\langle j|
+
|j\rangle\langle j+1|
\right),
\qquad g>0.
}
\tag{359.1}
$$

它是有界自伴算子，\(\|H_\infty\|=2g\)。

观察者只从端点 \(|0\rangle\) 制备和读取。

## 定理359.1　递归消元产生平方根谱边界

令：

$$
G_\infty(z)=\langle0|(z-H_\infty)^{-1}|0\rangle.
$$

由于删去第一个节点后的尾部与原链相同：

$$
G_\infty(z)=\frac1{z-g^2G_\infty(z)}.
$$

因此：

$$
\boxed{
G_\infty(z)
=
\frac{z-\sqrt{z^2-4g^2}}{2g^2},
}
\tag{359.2}
$$

分支由：

$$
G_\infty(z)\sim\frac1z
$$

唯一选定。

对应端点谱密度为：

$$
\boxed{
\rho(E)
=
\frac{\sqrt{4g^2-E^2}}{2\pi g^2}
\,\mathbf1_{[-2g,2g]}(E).
}
\tag{359.3}
$$

### 证明

解二次方程并使用大 \(z\) 渐近条件，得到式（359.2）。

取实轴上方边界值，由：

$$
\rho(E)=-\frac1\pi\operatorname{Im}G_\infty(E+i0)
$$

得到式（359.3）。∎

这里产生了真正的谱带边缘：

$$
E=\pm2g.
$$

它们是无限链响应的平方根分支点，而不是某个有限矩阵失去定义。

链映射与残余谱密度随保留层数变化的关系，是已有开放量子系统研究的正式内容。([arXiv][5])

---

## 定理359.2　无限链的端点返回振幅衰减到零

有：

$$
A_\infty(t)
=
\int_{-2g}^{2g}
e^{-iEt/\hbar}\rho(E)\,dE,
$$

因此：

$$
\boxed{A_\infty(t)\longrightarrow0.}
\tag{359.4}
$$

### 证明

\(\rho(E)\) 可积，应用 Fourier 变换的 Riemann–Lebesgue 性质。∎

但完整演化仍然酉。概率没有被消灭，而是进入越来越远的链模式。

---

## 两个极限不交换

令 \(A_L(t)\) 为前 \(L\) 个节点的有限链返回振幅。

对每个固定 \(T\)，由定理354.2：

$$
\boxed{
\sup_{|t|\le T}
|A_L(t)-A_\infty(t)|
\le
2\frac{(2gT/\hbar)^{2L}}{(2L)!}
\longrightarrow0.
}
\tag{359.5}
$$

但每个有限链只有有限组频率。由同时相位逼近，可以找到任意晚的时刻，使全部参与相位同时任意接近初始值，因此：

$$
\limsup_{t\to\infty}|A_L(t)|=1.
$$

于是：

$$
\boxed{
\lim_{L\to\infty}
\limsup_{t\to\infty}|A_L(t)|
=1,
}
\tag{359.6}
$$

而：

$$
\boxed{
\limsup_{t\to\infty}
\lim_{L\to\infty}|A_L(t)|
=0.
}
\tag{359.7}
$$

### 这才是一种准确的“无穷临界”

$$
\boxed{
\text{每个有限装置都允许回归}
}
$$

与：

$$
\boxed{
\text{固定实验窗口中的无限层极限呈现持续衰减}
}
$$

可以同时成立。

不是有限理论被推翻，而是两个量词与极限次序不同。

这也解释了为什么“在全部时间都精确不可逆”和“在当前时间窗口内看起来不可逆”是不同要求。

但端点返回振幅衰减，仍不等于已经得到了热平衡、霍金辐射或完整的熵增定律。

---

# 360．从边界反演走向共同物理时空，还必须增加什么？

本轮把此前的链条反向闭合了一段：

$$
\boxed{
\text{边界时间响应}
\longleftrightarrow
\text{谱矩}
\longleftrightarrow
\text{最小最近邻链}.
}
$$

并且：

$$
\boxed{
\text{保留多少链层}
\longleftrightarrow
\text{准确到多少阶响应}
\longrightarrow
\text{有限时间误差}.
}
$$

但现在也已经证明：

$$
\boxed{
\text{最小动力学链}
\ne
\text{唯一真实空间}.
}
$$

要继续谈“由观察者导出现实时空”，至少还要把以下结构纳入同一个实现：

$$
\boxed{
\mathfrak M=
\left(
H,\;
\text{各观察端口},\;
\text{局域可观测代数},\;
\text{允许控制},\;
\text{事件因果关系},\;
\text{共同钟尺}
\right).
}
\tag{360.1}
$$

两套模型若只是满足：

$$
\widetilde H=WHW^\dagger,
$$

还不足以证明它们的物理几何相同。

还需检验 \(W\) 是否把允许的局域实验、控制和参照关系映射到彼此对应的结构。例如：

$$
\boxed{
W\mathcal A(O)W^\dagger
=
\widetilde{\mathcal A}(f(O)),
}
\tag{360.2}
$$

并要求 \(f\) 保持相关的因果与钟尺标定。

**物理空间不是任意基底的标签，而是哪些操作能被局域实施、哪些关系能被共同测量的结构。**

---

## 本轮与仓库的三个直接连接

本次读取固定于提交：

```text
0c853b65998ca222349739fbfda44f49be4e35b3
```

| 已有模块                                | 本轮补出的证明方向                               |
| ----------------------------------- | --------------------------------------- |
| `HankelJacobiDeterminant.lean`      | 从真实边界矩出发，把行列式候选识别为实际递推耦合，并核对索引          |
| `MemoryDimensionFormula.lean`       | 将未来相关维数具体表示为端口的 Krylov 维数；区分不同端口和不同采样协议 |
| `SchurComplementAssociativity.lean` | 保证逐层继续分式与一次内部消元一致，保留逆算子存在条件             |

尤其第三项提供了一个重要审计原则：**反演和消元不能因更换切法而给出不相容的响应，除非我们同时更换了前提、边界条件或近似。**仓库已经给出相应的有界算子结合律。

对 ζ 路线也一样：从一组正谱矩构造出实对称 Jacobi 模型，并不自动证明它就是实际 ξ 响应。仍然必须证明真实解析对象与所构造的矩序列相同，并控制无限尾部。

---

## 本轮核验

完成了 **27组精确符号检查**，其中包含21组不同链长与截断位置的矩匹配检验；另进行了12个有限链—无限链返回振幅的浮点交叉比较。

核验内容包括：

三阶 Hankel 临界、首次四阶回声、实际 Jacobi 耦合的行列式公式、5040不同端口的可见维数、链与三角形的相同边界响应、三方正性失败，以及均匀链的有限时间逼近。

[核验脚本](sandbox:/mnt/data/observer_formalization/check_boundary_inverse_geometry.py)
[核验结果](sandbox:/mnt/data/observer_formalization/boundary_inverse_geometry_checks.json)

**本轮未运行 Lean 内核编译。**浮点比较也明确带有数值容差，不作为区间证书或一般证明；新增解析结论由上文的条件与证明承担。

---

# 结论

这一轮最重要的结果是：

> **观察者可以把未直接看见的内部世界，重建成一个最小的预测结构；但这个结构的“链深度”，首先表示未来响应需要经过多少层动力学，而不是已经确认的物理空间距离。**

其中，离散与连续现在通过三个精确关系连接起来。

**第一，内部连接的开启，可以让最小预测维数跳变。**

$$
\boxed{
\Delta_3=g^4\varepsilon^2:
\quad
\varepsilon=0\text{ 与 }\varepsilon\ne0
\text{ 对应不同的可见维数}.
}
$$

**第二，深处结构先出现在高阶回声中。**

$$
\boxed{
\text{删除第 }L\text{ 层以后的结构，}
\quad
\text{前 }2L-1\text{ 阶返回矩仍然完全相同}.
}
$$

**第三，无穷的意义可以表现为极限次序改变。**

$$
\boxed{
\text{每个有限系统允许回归，}
\quad
\text{无限层的固定时间极限却可以持续衰减}.
}
$$

因此，“量子观察者形成世界”的研究目标可以进一步收紧为：

$$
\boxed{
\text{从真实记录反演最小动力学，}
}
$$

$$
\boxed{
\text{从跨观察者一致性排除不可能的拼接，}
}
$$

$$
\boxed{
\text{再用局域控制、共同钟尺与因果实验识别物理几何。}
}
$$

**这比直接把边界响应命名为空间更严格：它同时告诉我们能够恢复什么、无法唯一恢复什么，以及增加哪类实验才能把两者区分开。**

[1]: https://arxiv.org/abs/1006.4507?utm_source=chatgpt.com "Exact mapping between system-reservoir quantum models and semi-infinite discrete chains using orthogonal polynomials"
[2]: https://arxiv.org/html/1006.4507v2 "https://arxiv.org/html/1006.4507v2"
[3]: https://arxiv.org/abs/1907.11153 "https://arxiv.org/abs/1907.11153"
[4]: https://arxiv.org/abs/0810.2866 "https://arxiv.org/abs/0810.2866"
[5]: https://arxiv.org/abs/1111.5262 "https://arxiv.org/abs/1111.5262"
上一轮证明：**同一个边界响应，可以由不同的内部连接图实现。**因此，仅凭“世界对观察者发出了什么信号”，还不能唯一恢复空间。

这一轮可以补上一条更强的桥梁：

> **除了读取信号，还要记录观察者能够在哪里、以什么方式干预，以及干预后信号怎样改变。局域干预的可识别性，可以把原来巨大的内部表示自由度，缩小为不改变连接关系的相位自由度。**

这会把项目的 **CUT、FLOW、ADMIT、ANCHOR** 接得更紧：不仅重建一个能够拟合记录的动力学，还要让它解释**带有明确位置标签的行动**。

量子系统识别中，输入—输出数据能够把模型确定到什么等价类，确实取决于控制和先验信息；完全可控闭合系统一般仍只能确定到酉共轭。下面针对当前理论给出有限维构造，并进一步检查：什么额外数据能让这种抽象等价开始具有几何意义。([APS Journals][1])

# 局域干预、控制词重建与共同几何的可识别性

## ——量子观察者—关系时空理论第三百六十一至第三百七十节增订

---

# 361．一个局域干预，可以区分原本边界响应完全相同的世界

先继续上一轮的链—三角形实例。

取能量单位 \(E_*>0\)，定义：

$$
H_{\mathrm C}
=
E_*
\begin{pmatrix}
0&1&0\\
1&0&2\\
0&2&0
\end{pmatrix},
$$

以及只混合两个内部模式的酉矩阵：

$$
W=
\begin{pmatrix}
1&0&0\\
0&3/5&-4/5\\
0&4/5&3/5
\end{pmatrix}.
$$

令：

$$
H_{\mathrm T}=WH_{\mathrm C}W^\dagger.
$$

前者的非零连接构成链，后者为：

$$
\boxed{
H_{\mathrm T}
=
E_*
\begin{pmatrix}
0&3/5&4/5\\
3/5&-48/25&-14/25\\
4/5&-14/25&48/25
\end{pmatrix},
}
\tag{361.1}
$$

其三个节点两两连接。

观察端口为 \(|0\rangle\)。因为：

$$
W|0\rangle=|0\rangle,
$$

两者具有完全相同的自由返回振幅：

$$
\boxed{
\langle0|e^{-itH_{\mathrm C}/\hbar}|0\rangle
=
\langle0|e^{-itH_{\mathrm T}/\hbar}|0\rangle.
}
\tag{361.2}
$$

现在增加一个经过独立标定的操作：只给标签1施加 \(\pi\) 相位。

$$
P_1=|1\rangle\langle1|,
\qquad
V=I-2P_1.
$$

这里要求“标签1”由真实装置确定，而不是事后可以任意旋转的内部基底。

## 定理361.1　同一个端口回声协议可以区分两种模型

取：

$$
\tau_*=\frac{\pi\hbar}{2\sqrt5E_*}.
$$

实施：

$$
\boxed{
\text{自由演化 }\tau_*
\;\longrightarrow\;
V
\;\longrightarrow\;
\text{自由演化 }\tau_*.
}
$$

从 \(|0\rangle\) 出发，最后返回 \(|0\rangle\) 的概率分别为：

$$
\boxed{
p_{\mathrm C}=1,
\qquad
p_{\mathrm T}
=
\frac{159649}{390625}
=
0.40870144.
}
\tag{361.3}
$$

### 证明

记 \(M=H_{\mathrm C}/E_*\)。它满足：

$$
M^3=5M.
$$

因此：

$$
U_{\mathrm C}(\tau_*)
=
I-\frac{M^2}{5}-\frac{iM}{\sqrt5},
$$

而：

$$
U_{\mathrm T}(\tau_*)=WU_{\mathrm C}(\tau_*)W^\dagger.
$$

直接计算得到：

$$
\langle0|U_{\mathrm C}VU_{\mathrm C}|0\rangle=1,
$$

$$
\langle0|U_{\mathrm T}VU_{\mathrm T}|0\rangle
=
\frac{337+96i\sqrt5}{625}.
$$

取模平方即得。∎

### 关键区别

如果同时把控制器也变为：

$$
V\longmapsto WVW^\dagger,
$$

两套完整实验仍然等价。

本定理之所以能够区分它们，是因为我们增加了一个**固定标签、固定实现的控制器**，没有允许它跟着未知内部基底一起重定义。

因此：

$$
\boxed{
\text{被动响应相同}
\not\Rightarrow
\text{带局域干预的响应相同}.
}
$$

这不是通过选择坐标“创造”连接差别，而是通过新增实验，识别旧实验无法区分的差别。

---

# 362．从单条时间序列，提升到“带标签的操作词”

上一轮只考虑：

$$
|o\rangle,\ H|o\rangle,\ H^2|o\rangle,\ldots
$$

它只包含一种自然演化。

现在加入控制生成元。

## 定义362.1　控制词与记录核

取有限个无量纲 Hermitian 算子：

$$
X_0,X_1,\ldots,X_r.
$$

其中可以包括：

$$
X_0=H/E_*,
$$

以及投影、已标定控制 Hamiltonian 的归一化形式。

对一个有限词：

$$
w=a_\ell\cdots a_1,
$$

定义：

$$
X_w=X_{a_\ell}\cdots X_{a_1},
\qquad
|w\rangle=X_w|o\rangle.
$$

空词记为 \(\varnothing\)，满足 \(X_\varnothing=I\)。

定义带标签的 Gram 记录：

$$
\boxed{
\Gamma(u,v)=\langle o|X_u^\dagger X_v|o\rangle.
}
\tag{362.1}
$$

这些数不仅包含自由谱矩，还包含“先做什么、再做什么”的混合响应。

它们不是每个都对应一个可以直接实施的量子门。实际认证可以使用已实现的相干控制序列及其参数导数；若装置不能提供相位参照或相关混合响应，就不能声称已经掌握整个 \(\Gamma\)。

---

## 定理362.1　合法控制词记录必须满足三类一致性

有：

$$
\Gamma(\varnothing,\varnothing)=1,
$$

任意有限子矩阵均正半定：

$$
\boxed{
(\Gamma(u_i,u_j))_{ij}\succeq0,
}
\tag{362.2}
$$

并且对每个 Hermitian 生成元标签 \(a\)：

$$
\boxed{
\Gamma(au,v)=\Gamma(u,av).
}
\tag{362.3}
$$

### 证明

归一化来自 \(\langle o|o\rangle=1\)。

正性来自：

$$
\sum_{i,j}\overline c_i\Gamma(u_i,u_j)c_j
=
\left\|\sum_jc_jX_{u_j}|o\rangle\right\|^2.
$$

式（362.3）来自 \(X_a^\dagger=X_a\)。∎

仓库 `GNSMatrix.lean` 已经把正矩阵权重的读数写成 Hilbert–Schmidt 范数平方。这里沿同一个正性原则，把对象从单个算子扩展为带操作顺序的记录核。

---

## 定理362.2　有限秩记录核可以重建一个最小量子模型

反过来，假设一个抽象 \(\Gamma\) 满足上述归一化、正性及左右移位一致性，并且所有有限 Gram 矩阵的最大秩为有限数 \(d\)。

则存在一个 \(d\) 维 Hilbert 空间、归一化态 \(|o\rangle\) 和 Hermitian 算子 \(X_a\)，实现全部 \(\Gamma(u,v)\)。

这个循环生成的最小实现，唯一到一个保持所有标签的酉等价。

### 证明

先取全部形式词的有限线性组合，并用 \(\Gamma\) 定义半正定内积。

把零范数向量组成的子空间商掉，得到一个正定内积空间。其维数正好为 \(d\)。

定义 \(X_a\) 为“在词左侧添加标签 \(a\)”。式（362.3）保证零范数关系在这个操作下保持，因此它在商空间上定义良好，而且自伴。

空词给出初态，全部词生成整个空间。

任意两个这样的实现，都由“同一个形式词映到同一个实验向量”建立保内积满射，因此酉等价。∎

### 这一结果的意义

我们不再只是选择一个 Hamiltonian 去拟合记录，而是可以要求：

$$
\boxed{
\text{记录自身满足正性与组合一致性}
\longrightarrow
\text{存在共同量子实现}.
}
$$

这是有限秩的 GNS 式重建，不等于从任意逻辑关系自动推出量子力学。量子操作类型及记录规则仍然是当前模型的明确条件。

---

# 363．有限维意味着存在有限的控制词证书，但不意味着任意短记录都足够

定义：

$$
\boxed{
\mathcal K_n
=
\operatorname{span}\{X_w|o\rangle:|w|\le n\}.
}
\tag{363.1}
$$

则：

$$
\mathcal K_{n+1}
=
\operatorname{span}
\left(
\mathcal K_n,\ X_0\mathcal K_n,\ldots,X_r\mathcal K_n
\right).
$$

## 定理363.1　控制词空间有限步稳定

若完整空间维数不超过 \(d\)，则存在：

$$
n_*\le d-1
$$

使：

$$
\boxed{
\mathcal K_{n_*}=\mathcal K_{n_*+1}
=\mathcal K_\infty.
}
\tag{363.2}
$$

### 证明

初始空间至少一维。每次尚未稳定，维数至少增加一。

一旦相邻两层相等，所有生成元都保持当前空间，以后不再增长。∎

这里的维数是**控制词生成的态向量空间维数**，不是全部密度矩阵的参数数目，也不是此前效果空间的 \(d^2\) 上界。

项目的受控关系递归已经正式表达了“每种行动之后仍不可区分”的要求。本节给出相应的有限线性代数实现，而不把连续量子态集合误当作有限集合。

---

## 定理363.2　认证维数上界后，有限 Gram 表足以确定最小实现

若两套模型维数均不超过已知 \(d\)，且：

$$
\Gamma(u,v)=\widetilde\Gamma(u,v)
\qquad
(|u|,|v|\le d),
$$

则它们的最小控制生成实现酉等价，且等价映射同时保持所有生成元标签。

### 证明

长度至多 \(d-1\) 的词已经张成各自的全部可见空间。

Gram 表相同，给出词向量之间的保内积对应。增加一个生成元，只把词长度增加至多一，因此长度至多 \(d\) 的数据保证这个对应与全部生成元交织。∎

### 还能写出实际重建公式

选取独立词向量：

$$
|w_1\rangle,\ldots,|w_m\rangle.
$$

定义：

$$
G_{ij}=\Gamma(w_i,w_j),
$$

$$
B^{(a)}_{ij}=\Gamma(w_i,aw_j).
$$

则在这个非正交基中：

$$
\boxed{
C_a=G^{-1}B^{(a)}.
}
\tag{363.3}
$$

在正交化基中：

$$
\boxed{
\widehat X_a
=
G^{-1/2}B^{(a)}G^{-1/2}.
}
\tag{363.4}
$$

所以重建不是一句存在性口号，而是有限矩阵运算。

但如果没有独立认证的维数上界，有限数据仍可能遗漏更深层模式。上一轮的“前 \(2L-1\) 阶回声完全相同”反例仍然有效。

此外，\(G\) 接近奇异时，精确可识别并不意味着稳定可识别。

---

# 364．局域锚点把一般酉自由度，缩小为顶点相位自由度

现在加入真正决定几何解释的数据。

## 定义364.1　经过独立标定的模式锚点

假设存在可识别的秩一投影：

$$
P_i=|i\rangle\langle i|,
\qquad
\sum_iP_i=I.
$$

它们表示装置能够区分和控制的模式。此时尚不宣称这些标签已经具有欧氏位置或距离。

若它们确实由物理局域端口实现，就可以进一步解释为局域锚点。

## 定理364.1　保持全部锚点的酉变换只能改变局部相位

若：

$$
WP_iW^\dagger=P_i
\qquad\forall i,
$$

则：

$$
\boxed{
W=\sum_ie^{i\chi_i}P_i.
}
\tag{364.1}
$$

所以：

$$
\boxed{
H_{ij}\longmapsto
e^{i(\chi_i-\chi_j)}H_{ij}.
}
\tag{364.2}
$$

特别地，以下结构保持不变：

$$
H_{ii},\qquad |H_{ij}|,\qquad
\{(i,j):H_{ij}\ne0\}.
$$

### 证明

\(W\) 必须保持每个一维像空间，因此在该空间上只能乘一个单位模复数。∎

如果标签本身还可以互换，则再加上相应的节点置换；这仍不会把链随意变成三角形。

**这就是从“抽象动力学”走向“可识别连接图”的关键变化：不是多测了一些频率，而是增加了不能被未知基底旋转随意带走的操作标签。**

有限访问下的 Hamiltonian 重建，已有研究明确依赖可访问区域、已知连接结构或额外控制。这里没有把这些条件视为自动具备。([arXiv][2])

---

## 定理364.2　连接关系可以由局域干预代数定义

对 \(i\ne j\)，有：

$$
\boxed{
[P_i,[H,P_j]]
=
P_iHP_j+P_jHP_i.
}
\tag{364.3}
$$

并且：

$$
\boxed{
[P_i,[H,P_j]]^2
=
|H_{ij}|^2(P_i+P_j).
}
\tag{364.4}
$$

因此：

$$
\boxed{
H_{ij}\ne0
\iff
[P_i,[H,P_j]]\ne0.
}
\tag{364.5}
$$

### 证明

使用 \(P_iP_j=0\) 展开两个交换子；再将所得的双向非对角块平方。∎

这提供了一种不先画图的定义：

> **两个已标定模式是否直接耦合，可以由它们的局域操作与自然生成元之间的混合响应确定。**

但这里恢复的是模式耦合图，不是已经恢复了全部时空流形。

---

# 365．主动区分路径，可以揭示被干涉隐藏的连接

上一轮从被动响应的首次非零阶恢复图距离，需要非负边权来防止不同路径相消。

加入中间锚点以后，可以放松这个条件。

## 定理365.1　投影标记的路径不会被其他路径相消

取一条连接路径：

$$
i_0\to i_1\to\cdots\to i_L,
$$

并假设每条边都非零。

则：

$$
\boxed{
P_{i_L}HP_{i_{L-1}}H\cdots P_{i_1}H|i_0\rangle
=
\left(
\prod_{r=1}^L H_{i_r i_{r-1}}
\right)|i_L\rangle.
}
\tag{365.1}
$$

右侧严格非零，即使边权具有复杂相位。

### 证明

每个秩一投影都只保留指定中间模式。逐步相乘即可。∎

因此，若全部模式投影都可用于控制词，那么：

$$
\boxed{
\mathcal K_{\{H,P_i\}}(|o\rangle)
=
\operatorname{span}
\{|i\rangle:i\text{ 与 }o\text{ 位于同一连接分量}\}.
}
\tag{365.2}
$$

这说明：在这个操作类中，破坏性干涉造成的被动暗方向，未必仍然不可识别。

### 物理实现的边界

投影标记路径通常是一条条件分支，其成功概率需要保留。

它不是说可以免费确定性地执行 \(H\)，也不是说相干干涉实验与带中途记录的实验仍然是同一个过程。

一个固定非平凡相位门：

$$
V_i(\phi)=e^{-i\phi P_i}
=
I+(e^{-i\phi}-1)P_i
$$

也使 \(P_i\) 进入相应的线性操作空间，但“进入线性空间”仍弱于“任意目标态都能在给定资源下制备”。

---

## 闭路提供剩余的相位数据

对闭路 \(\gamma=(i_0,\ldots,i_{L-1},i_0)\)，定义：

$$
\boxed{
C_\gamma
=
\operatorname{Tr}
(P_{i_0}HP_{i_1}H\cdots P_{i_{L-1}}H).
}
\tag{365.3}
$$

则：

$$
C_\gamma
=
H_{i_0i_1}H_{i_1i_2}\cdots H_{i_{L-1}i_0}.
$$

它在式（364.2）的顶点相位变换下不变。

对一个连通图，若已知全部对角项、边模长和一组基本闭路的复相位，就能把 Hermitian 耦合矩阵确定到顶点相位变换。

证明方法是先沿生成树固定相位，再用每条非树边所形成的基本闭路确定剩余相位。

**于是，模式图的连接与其干涉结构可以分开重建：边模长给出耦合强度，闭路相位给出不能由局部命名消去的相干数据。**

它们仍不是自动的 Levi–Civita 曲率；必须先证明这些耦合真的实现了相应的物理输运。

---

# 366．5040暗态：不可见性可以被一个实际操作改变

现在回到我们的算术纤维：

$$
|L\rangle=|5400\rangle,\quad
|M\rangle=|5040\rangle,\quad
|R\rangle=|4704\rangle.
$$

沿用混合 Hamiltonian：

$$
H
=
J
\begin{pmatrix}
0&2\sqrt6&0\\
2\sqrt6&0&2\sqrt5\\
0&2\sqrt5&0
\end{pmatrix}.
\tag{366.1}
$$

本节不同时加入对数整数对角能量；加入后必须重新计算失谐与演化。

定义：

$$
|B\rangle
=
\frac{\sqrt6|L\rangle+\sqrt5|R\rangle}{\sqrt{11}},
$$

$$
|D\rangle
=
\frac{\sqrt5|L\rangle-\sqrt6|R\rangle}{\sqrt{11}},
$$

以及：

$$
\omega=\frac{2\sqrt{11}J}{\hbar}.
$$

自然动力学满足：

$$
H|D\rangle=0,
\qquad
e^{-iH\pi/(2\hbar\omega)}|M\rangle=-i|B\rangle.
$$

更清楚地记：

$$
\tau_q=\frac{\pi}{2\omega},
$$

则最后一式为 \(e^{-iH\tau_q/\hbar}|M\rangle=-i|B\rangle\)。

## 定义366.1　纤维端点相位操作

取：

$$
V_\phi=e^{-i\phi P_L},
\qquad
P_L=|L\rangle\langle L|.
$$

它对亮态的作用为：

$$
\boxed{
V_\phi|B\rangle
=
a_\phi|B\rangle+b_\phi|D\rangle,
}
\tag{366.2}
$$

其中：

$$
a_\phi=\frac{5+6e^{-i\phi}}{11},
$$

$$
b_\phi=\frac{\sqrt{30}(e^{-i\phi}-1)}{11}.
$$

## 定理366.1　相位控制把被动不可见暗态变成可达分量

从 \(|M\rangle\) 开始，执行：

$$
U(\tau_q)V_\phi U(\tau_q).
$$

最后返回 \(|M\rangle\) 的概率为：

$$
\boxed{
p_M(\phi)
=
1-\frac{120}{121}\sin^2\frac\phi2.
}
\tag{366.3}
$$

暗态占据为：

$$
\boxed{
p_D(\phi)
=
\frac{120}{121}\sin^2\frac\phi2.
}
\tag{366.4}
$$

### 证明

第一段演化把 \(|M\rangle\) 送到 \(-i|B\rangle\)。

脉冲产生式（366.2）。第二段把亮态送回 \(-i|M\rangle\)，暗态保持不变。两个分量正交，分别取模平方即可。∎

因此：

$$
\boxed{
\phi=0:\quad p_M=1;
}
$$

$$
\boxed{
\phi=\pi:\quad p_M=\frac1{121},\quad p_D=\frac{120}{121}.
}
\tag{366.5}
$$

没有增加新的状态，也没有创造新的能级；改变的是允许过程能进入哪些既有方向。

---

## 离散临界表现为一个控制相关的秩跳变

令 \(X=H/J\)，考虑三个词向量：

$$
|M\rangle,\quad X|M\rangle,\quad V_\phi X|M\rangle.
$$

其 Gram 行列式为：

$$
\boxed{
\det G_\phi
=
1920\sin^2\frac\phi2.
}
\tag{366.6}
$$

所以：

$$
\boxed{
\phi\equiv0\pmod{2\pi}
\Rightarrow
\text{只生成两维};
}
$$

$$
\boxed{
\phi\not\equiv0\pmod{2\pi}
\Rightarrow
\text{生成完整三维}.
}
$$

当 \(\phi\) 很小时，精确秩已经增加，但新信号只有 \(O(\phi^2)\)，有限噪声下未必稳定可见。

这里的“端点”首先是**算术纤维图端点**。\(P_L\) 是否能由现实中的局域装置低成本实现，尚需证明；不能因其是一个三维矩阵，就默认它是一个空间局域开关。

---

# 367．主动干预也有因果深度：隐藏位置不会被瞬时读出

现在回到已标定的物理模式图。

设：

$$
U(t)=e^{-iHt/\hbar},
\qquad
\|H\|\le\Lambda.
$$

观察端口为 \(o\)，被施加相位的端口为 \(i\)，图距离为：

$$
d=d_G(o,i)\ge1.
$$

## 定理367.1　远端相位对边界回声的影响至少经过一次往返

定义：

$$
A_\phi(t_2,t_1)
=
\langle o|U(t_2)e^{-i\phi P_i}U(t_1)|o\rangle.
$$

则：

$$
\boxed{
\begin{aligned}
A_\phi-A_0
={}&(e^{-i\phi}-1)\\
&\times
\langle o|U(t_2)|i\rangle
\langle i|U(t_1)|o\rangle.
\end{aligned}
}
\tag{367.1}
$$

并且：

$$
\boxed{
|A_\phi-A_0|
\le
|e^{-i\phi}-1|
\prod_{r=1}^{2}
\min\left\{
1,\frac{(\Lambda|t_r|/\hbar)^d}{d!}
\right\}.
}
\tag{367.2}
$$

### 证明

由：

$$
e^{-i\phi P_i}
=
I+(e^{-i\phi}-1)P_i
$$

直接得到式（367.1）。

少于 \(d\) 次矩阵乘法无法从 \(o\) 到达 \(i\)，所以：

$$
(H^n)_{io}=0\qquad(n<d).
$$

对指数使用 \(d-1\) 阶 Taylor 多项式及自伴谱上的余项界：

$$
|\langle i|U(t)|o\rangle|
\le
\frac{(\Lambda|t|/\hbar)^d}{d!}.
$$

再与酉性给出的上界一取最小值。∎

这说明：

$$
\boxed{
\text{局域干预产生的边界证据}
}
$$

必须经历：

$$
\boxed{
\text{进入该区域}
\longrightarrow
\text{在那里受影响}
\longrightarrow
\text{返回可读端口}.
}
$$

连续时间模型中，这是高阶小量界，不是严格延迟到某个正时刻以后才出现。

在具有严格局域支持的离散电路中，则可以得到严格的因果深度截止：没有足够步骤完成对应路径，影响精确为零。

**控制菜单更丰富，不等于信号传播更快。**控制器到达被干预区域所需的通信与实施过程也必须计入事件网络。

---

# 368．“边存在”是精确命题；有限实验还需要分离裕量

有了局域制备和读取，可以通过短时跃迁检测耦合边。但缩短时间也会放大概率估计误差。

## 定理368.1　短时边强度估计的误差界

从 \(|i\rangle\) 开始，测量：

$$
p_{j\leftarrow i}(t)
=
|\langle j|e^{-iHt/\hbar}|i\rangle|^2,
\qquad i\ne j.
$$

若：

$$
\|H\|\le\Lambda,
$$

实测概率满足：

$$
|\widehat p-p_{j\leftarrow i}(t)|\le\eta,
$$

定义：

$$
\widehat w_{ij}^{\,2}
=
\frac{\hbar^2}{t^2}\widehat p.
$$

则：

$$
\boxed{
\left|
\widehat w_{ij}^{\,2}-|H_{ij}|^2
\right|
\le
\frac{\hbar^2\eta}{t^2}
+
\frac{\Lambda^3|t|}{\hbar}
+
\frac{\Lambda^4t^2}{4\hbar^2}.
}
\tag{368.1}
$$

### 证明

指数余项给出：

$$
\left|
\langle j|U(t)|i\rangle
+\frac{it}{\hbar}H_{ji}
\right|
\le
\frac{\Lambda^2t^2}{2\hbar^2}.
$$

将振幅写成一阶项加余项，展开模平方，使用 \(|H_{ij}|\le\Lambda\)，再加入测量概率误差。∎

因此：

$$
t\to0
$$

会减小动力学截断误差，却使：

$$
\frac{\hbar^2\eta}{t^2}
$$

增大。

**离散连接重建同样具有最佳测量尺度，而不是越快刷新越好。**

---

## 推论368.1　有最小非零耦合时，可以认证整个连接图

额外假设每条候选边满足：

$$
H_{ij}=0
\quad\text{或}\quad
|H_{ij}|\ge g_{\min}>0.
$$

若式（368.1）的总上界为 \(\varepsilon\)，且：

$$
\boxed{
\varepsilon<\frac{g_{\min}^2}{2},
}
\tag{368.2}
$$

则以阈值 \(g_{\min}^2/2\) 分类，可以正确区分零边与非零边。

### 证明

零边的估计不超过 \(\varepsilon\)。

非零边的估计至少为 \(g_{\min}^2-\varepsilon\)。

两区间由条件（368.2）严格分开。∎

没有这样的分离条件时，任意有限误差都可能无法区分：

$$
H_{ij}=0
$$

与一个极小但非零的耦合。

所以，图的精确拓扑和有限装置所认证的有效拓扑，仍然是不同层次。

---

# 369．多体系统的局域性，需要由可访问代数共同确定

前面使用的是单激发或有限模式的直和空间：

$$
\mathcal H=\bigoplus_i\mathbb C|i\rangle.
$$

现实多体系统则通常需要张量因子：

$$
\mathcal H=\bigotimes_i\mathcal H_i.
$$

这两种结构不能混淆。

只给一个总 Hilbert 空间和一个 Hamiltonian，一般没有自动指定“哪些自由度属于哪一个局部系统”。由可访问观测与交互代数组织子系统，是已有的操作性量子结构研究。([arXiv][3])

## 定义369.1　候选局域操作代数

设同一有限空间上有若干含单位的 \(*\)-代数：

$$
\mathcal A_1,\ldots,\mathcal A_n.
$$

假设：

$$
\mathcal A_i\cong M_{d_i}(\mathbb C),
$$

不同代数逐元素可交换：

$$
[\mathcal A_i,\mathcal A_j]=0\qquad(i\ne j),
$$

且它们共同生成：

$$
\operatorname{End}(\mathcal H).
$$

## 定理369.1　这些操作条件足以重建张量积结构

存在一个酉等价，使：

$$
\boxed{
\mathcal H
\cong
\bigotimes_{i=1}^n\mathbb C^{d_i},
}
\tag{369.1}
$$

且每个 \(\mathcal A_i\) 只作用于第 \(i\) 个因子。

### 证明

由于不同代数可交换，乘法给出一个含单位的 \(*\)-同态：

$$
\bigotimes_iM_{d_i}(\mathbb C)
\longrightarrow
\operatorname{End}(\mathcal H).
$$

定义域是一个全矩阵代数，因而是单代数；含单位同态非零，所以单射。

共同生成条件使其满射。两个有限全矩阵代数之间的 \(*\)-同构由酉等价实现。∎

这提供了另一条条件重建链：

$$
\boxed{
\text{哪些操作可独立实施}
+
\text{哪些操作彼此可交换}
+
\text{它们是否覆盖全部自由度}
}
$$

$$
\boxed{
\longrightarrow
\text{怎样分解为多个量子子系统}.
}
$$

但它没有证明这些子系统在三维空间中排列，也没有确定每对系统间的物理距离。

---

## 定理369.2　合法的局域非选择性操作不改变其他因子的即时读数

设局域通道的 Kraus 算子 \(K_\alpha\in\mathcal A_i\)，满足：

$$
\sum_\alpha K_\alpha^\dagger K_\alpha=I.
$$

对 \(E\in\mathcal A_j\)、\(i\ne j\)，有：

$$
\boxed{
\sum_\alpha K_\alpha^\dagger E K_\alpha=E.
}
\tag{369.2}
$$

### 证明

\(E\) 与每个 \(K_\alpha\) 可交换，因此：

$$
\sum_\alpha K_\alpha^\dagger E K_\alpha
=
E\sum_\alpha K_\alpha^\dagger K_\alpha
=
E.
$$

∎

这是即时局域无信号的一项代数实现。

它不禁止后续相互作用传递影响，也不把条件于某个测量结果的状态更新当成超光速消息。

**从观察者重建共同世界，除了每个人各自拥有一个预测模型，还需要他们的操作代数、相互作用和通信方式能够同时成立。**

---

# 370．本轮把“由量子观察者重建几何”推进了哪一步？

现在可以给出一个更强的条件性重建结论。

## 定理370.1　干预锚定的有限模式几何重建

假设：

**首先，**已认证的复数控制词记录满足归一化、正性、移位一致性，并具有有限秩及已知维数上界。

**其次，**其中包含一组具有独立物理标定的秩一模式锚点。

**最后，**自然 Hamiltonian 及允许控制共同生成了待研究的整个连接分量。

则这些数据能够确定：

$$
\boxed{
\text{最小动力学空间}
+
\text{全部带标签的控制生成元}
}
$$

到共同酉等价；加入固定锚点后，剩余自由度缩小为顶点相位变换。

因此，连接的零／非零结构、边模长和闭路相位，都成为可重建的不变量。

### 证明

由定理362.2与363.2得到共同最小实现及交织酉。

锚点相容性再由定理364.1把酉自由度限制为对角相位。

定理364.2与365节给出连接和闭路不变量。∎

这仍然不是从裸量子态唯一推出 Einstein 时空。它完成的是此前缺失的一段：

$$
\boxed{
\text{被动边界反演}
\longrightarrow
\text{带标签的干预反演}
\longrightarrow
\text{可识别的耦合结构}.
}
$$

继续进入现实几何，还需要把耦合结构与共同钟尺、传播锥、维数、物质种类和引力反作用连接起来。

---

## 与本次仓库读取的对应

本轮固定提交：

```text
ed2d4167e49b41c5b876df187a4342198816d62e
```

源码中的分工可以保持清楚：

| 已读取模块                              | 本轮连接         | 不能省略的新增证明            |
| ---------------------------------- | ------------ | -------------------- |
| `ControlledRelationRecursion.lean` | 行动族改变未来可区分关系 | 控制词 Gram 的有限秩重建      |
| `GNSMatrix.lean`                   | 正读数来自范数平方    | 抽象词核到共同 Hermitian 表示 |
| `ExactDescentNoCarry.lean`         | 新干预暴露旧接口缺口   | 带锚点的图与相位重建           |
| `InterventionEffectiveness.lean`   | 明确标记哪些坐标被干预  | 量子仪器、脉冲与实际局域装置的实现    |

尤其需要注意：`InterventionEffectiveness.lean` 证明的是有限结构因果模型中，被干预坐标在最终求值中保持指定值。它不是“量子测量能任意指定结果”的定理，不能直接用于取消量子概率与反作用。

本轮的源模型不足见证，仍按 `exact_descent_has_no_carry` 的意义使用：对新增目标，若两个旧接口合并的情况产生不同输出，就必须补充接口或收缩实验范围。

### 本轮核验

已完成 **65项精确有限矩阵、秩与符号检查**，以及 **12项带明确浮点容差的数值交叉检查**。

内容包括：

链—三角形的被动等价与主动区分、控制词 Gram 重建、局域双交换子、闭路相位不变量、5040暗态激活、回声概率、控制相关秩跳变，以及短时连接估计和往返深度界。

[精确核验脚本](sandbox:/mnt/data/observer_formalization/check_intervention_geometry_completion.py)
[核验结果](sandbox:/mnt/data/observer_formalization/intervention_geometry_completion_checks.json)

**本轮未进行 Lean 内核编译。**新增一般定理由上文证明承担；有限矩阵检查和数值交叉检查不替代完整形式化，也不认证所选耦合已经是现实微观定律。

---

# 结论

上一轮的关键限制是：

$$
\boxed{
\text{同一个边界响应，可能对应不同内部空间模型}.
}
$$

这一轮增加了正向结果：

$$
\boxed{
\text{带有物理标签的干预，
能够减少这种不唯一性}.
}
$$

其中最值得保留的三条联系是：

$$
\boxed{
\text{控制词的正性与组合一致性}
\longrightarrow
\text{共同最小量子实现};
}
$$

$$
\boxed{
\text{独立标定的局域锚点}
\longrightarrow
\text{可识别的连接图与闭路相位};
}
$$

$$
\boxed{
\text{允许控制的扩大}
\longrightarrow
\text{原本隐藏的动力方向重新进入未来记录}.
}
$$

5040三态模型给出了最后一条的精确实例：

$$
\boxed{
\text{没有相位操作：只显露两维；}
}
$$

$$
\boxed{
\text{加入非平凡端点相位：显露完整三维。}
}
$$

而其返回概率：

$$
\boxed{
p_M(\phi)
=
1-\frac{120}{121}\sin^2\frac\phi2
}
$$

把“能否进入隐藏方向”变成了一个具体可检验的关系。

因此，我们现在可以把观察者理论进一步收紧为：

> **观察者不只是接收世界的响应。它通过可实现、可标定的行动，确定哪些区别具有操作意义；再通过多种行动和多位观察者之间的一致性，逐步排除仅能拟合被动记录、却不能解释真实交互的模型。**

**物理几何不应只从“世界怎样呈现”中恢复，还应从“在何处实施什么行动，会怎样改变哪些后续记录”中恢复。**只有这两类数据共同约束同一个动力学，观察者形成的世界模型，才开始从一个方便的内部表示，走向能够共同检验的物理时空。

[1]: https://link.aps.org/doi/10.1103/PhysRevLett.108.080502 "https://link.aps.org/doi/10.1103/PhysRevLett.108.080502"
[2]: https://arxiv.org/abs/0903.0612 "https://arxiv.org/abs/0903.0612"
[3]: https://arxiv.org/abs/quant-ph/0308043 "https://arxiv.org/abs/quant-ph/0308043"
上一轮我们已经证明：**增加局域干预，可以把原先无法识别的内部结构变得可识别。**

但其中还有一个尚未闭合的前提：

> **观察者用来定义“这里”“这个相位”“这条能级方向”的参考系，究竟是什么物理系统？**

如果这些锚点始终由模型外部免费提供，我们就还没有真正建立一个闭合的量子观察者。

这轮可以继续推进，而且仓库已经有直接相关的基础：`ReferenceFrameTaxExact.lean` 对一个有限激发交换模型，给出了参考系维数与最优门保真度之间的精确关系：

$$
\boxed{
F_{\max}(N)=\cos^2\frac{\pi}{N+1}.
}
$$

它明确限定于所定义的交换通道，不是所有量子控制的普遍公式。

下面从这个基础出发，进一步证明：

**参考系是否足够好，不只取决于它有多少维，还取决于它是否包含目标测量所需的能量差，以及这些能量差能连接成多长的链。**

这条结果可以重新接回5040、素数寄存器、离散临界与几何重建。

# 有限量子参考系、共振链与观察几何的资源边界

## ——量子观察者—关系时空理论第三百七十一至第三百八十节增订

---

# 371．没有额外结构，就不能从完全对称的空间中选出唯一方向

先明确“锚点”的逻辑地位。

## 定理371.1　完全酉对称性不允许非平凡的固定投影

设 \(\dim\mathcal H=d\ge2\)。若投影 \(P\) 满足：

$$
UPU^\dagger=P
\qquad\text{对全部酉 }U,
$$

则：

$$
\boxed{P=0\quad\text{或}\quad P=I.}
\tag{371.1}
$$

### 证明

假设 \(P\) 既非零也非恒等。取单位向量：

$$
u\in\operatorname{ran}P,\qquad
v\in\ker P.
$$

存在交换 \(u,v\) 的酉操作。它把一个属于 \(P\) 的方向变成不属于 \(P\) 的方向，因此不可能保持 \(P\)。矛盾。∎

仓库的 `UnitaryNaturalSelector.lean` 已证明另一项相邻结论：不能在全部有限子空间的正交补中，选出一个对全部酉对称都自然一致的单位向量。它针对的是向量选择；本节针对投影，二者不能仅靠整体相位论证混为一谈。

### 这不意味着观察者不能选择坐标

它意味着，选择需要实际输入，例如：

$$
\boxed{
\text{一个已制备的参考态、一个非平凡 Hamiltonian、
一组控制器或某种边界条件}.
}
$$

非简并 Hamiltonian 可以提供能量投影；位置标记可以提供模式标签；相干参考态可以提供相位方向。

**关键不是禁止选择，而是不把选择所需的结构隐藏到模型外面。**

量子参考系研究正是把坐标轴、时钟相位和它们之间的校准当作物理资源，而不是免费的经典背景。([arXiv][1])

---

# 372．观察者作为中心，可以首先定义为一个精确的关系量

为了避免“有限参考系一定只能近似”的过强结论，先构造一个完全有限、完全精确的关系模型。

## 定义372.1　有限平移世界中的相对位置

令系统 \(S\) 与参考者 \(R\) 都具有位置标签：

$$
j\in\mathbb Z_M.
$$

共同平移为：

$$
T_h|j\rangle=|j+h\rangle.
$$

定义“系统相对参考者的位置为 \(d\)”的投影：

$$
\boxed{
P_d^{\mathrm{rel}}
=
\sum_{g\in\mathbb Z_M}
|g+d\rangle\langle g+d|_S
\otimes
|g\rangle\langle g|_R.
}
\tag{372.1}
$$

## 定理372.1　相对位置形成精确投影测量，并保持共同平移不变

有：

$$
P_d^{\mathrm{rel}}P_{d'}^{\mathrm{rel}}
=
\delta_{dd'}P_d^{\mathrm{rel}},
$$

$$
\sum_dP_d^{\mathrm{rel}}=I,
$$

以及：

$$
\boxed{
(T_h\otimes T_h)P_d^{\mathrm{rel}}
(T_h^\dagger\otimes T_h^\dagger)
=
P_d^{\mathrm{rel}}.
}
\tag{372.2}
$$

### 证明

不同的相对差 \(d\) 对应互不相交的基态集合；每对系统—参考位置恰有一个差值。

共同平移同时改变 \(g+d\) 和 \(g\)，差值不变。∎

这里，“参考者位于原点”不是要求它在某个外部绝对坐标中永远固定，而是选择读取：

$$
X_S-X_R.
$$

更强地，取联合态：

$$
\boxed{
|\Psi_d\rangle
=
\frac1{\sqrt M}\sum_g|g+d\rangle_S|g\rangle_R.
}
\tag{372.3}
$$

两者各自的位置边缘态都是最大混合态：

$$
\rho_S=\rho_R=\frac IM,
$$

但：

$$
\boxed{
P_d^{\mathrm{rel}}|\Psi_d\rangle=|\Psi_d\rangle.
}
\tag{372.4}
$$

**两个对象都没有确定的外部位置，彼此之间的位置却可以完全确定。**

有限群上的量子参考系与关系可观测量已有正式构造；本例给出其中最简单的一种。([arXiv][2])

### 有限群与连续相位不能混同

这里的标签只有 \(M\) 个，可以由有限个正交态精确表示。

连续相位的参考问题不同：有限能量窗口一般不能提供任意精确的连续相位标准。下面证明这个差别。

---

# 373．把相位锚点变成一个有限能量寄存器

## 假设373.1　一个没有外接相位标准的测量任务

取系统量子比特：

$$
N_S=|1\rangle\langle1|,
$$

以及 \(N\) 能级参考系：

$$
N_R=\sum_{n=0}^{N-1}n|n\rangle\langle n|.
$$

裸能量尺度为：

$$
H_S=\epsilon_0N_S,\qquad
H_R=\epsilon_0N_R.
$$

本节要求允许的联合读数效果 \(F\) 满足：

$$
\boxed{
[F,N_S+N_R]=0.
}
\tag{373.1}
$$

这描述一类保持总激发数、没有额外相位资源的装置。其他辅助系统若存在，也必须是相对于该对称性不变的，或者被显式计入参考资源。

它不是对所有量子测量强加的无条件限制。

系统输入与参考初态暂取乘积：

$$
\rho\otimes\tau.
$$

## 定理373.1　没有参考相干，就不能读取系统的第一阶相位

若：

$$
[\tau,N_R]=0,
$$

则任意满足式（373.1）的联合效果，在系统上诱导的有效效果都与 \(N_S\) 可交换。

因此它不能区分：

$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},
\qquad
|-\rangle=\frac{|0\rangle-|1\rangle}{\sqrt2}.
$$

### 证明

联合效果在共同相位变换下不变。对相位不变的 \(\tau\) 取参考期望以后，有效系统效果仍在系统相位变换下不变，故与 \(N_S\) 可交换。

这样的效果在能量基底中对角，而 \(|+\rangle,|-\rangle\) 的能量概率相同。∎

这类“绝对读数能否作为关系读数的近似”，已有定量的参考大小—精度理论。([arXiv][3])

---

## 一个实际的关系相位效果

定义参考降低算子：

$$
L_N=\sum_{n=0}^{N-2}|n\rangle\langle n+1|.
$$

取：

$$
\boxed{
X_{\mathrm{rel}}
=
|1\rangle\langle0|\otimes L_N
+
|0\rangle\langle1|\otimes L_N^\dagger.
}
\tag{373.2}
$$

它保持总激发数；在每个匹配的二维能量块中像 Pauli \(X\)，在两个未匹配的边界态上为零。

因此：

$$
F_\pm=\frac{I\pm X_{\mathrm{rel}}}{2}
$$

是合法的两结果测量。

令：

$$
r=\operatorname{Tr}(\tau L_N).
$$

则系统有效效果为：

$$
\boxed{
E_\pm^{(\tau)}
=
\frac12
\left[
I\pm
\left(
r|1\rangle\langle0|
+\overline r|0\rangle\langle1|
\right)
\right].
}
\tag{373.3}
$$

若相位标定使 \(r\ge0\)，则：

$$
\boxed{
E_\pm^{(\tau)}=\frac12(I\pm rX).
}
\tag{373.4}
$$

理想的 \(X\) 投影测量对应 \(r=1\)。有限参考系把它变成一个对比度为 \(r\) 的读数。

**这次不精确性不是系统状态未知，而是测量锚点本身具有有限资源。**

---

# 374．有限参考系的最佳测量精度，可以精确求出

## 定理374.1　有限能级参考下的最优相位区分概率

在第373节的操作条件下，等先验区分 \(|+\rangle\) 与 \(|-\rangle\) 的最佳成功概率为：

$$
\boxed{
p_{\mathrm{succ}}^{\max}(N)
=
\frac12
\left(
1+\cos\frac{\pi}{N+1}
\right).
}
\tag{374.1}
$$

因此最佳平均错误率为：

$$
\boxed{
p_{\mathrm{err}}^{\min}(N)
=
\frac12
\left(
1-\cos\frac{\pi}{N+1}
\right)
=
\sin^2\frac{\pi}{2(N+1)}.
}
\tag{374.2}
$$

### 证明

由于允许效果保持总激发数，可以先把两个候选联合态按总激发数分块。

在每个匹配块

$$
\operatorname{span}\{|0,n+1\rangle,\ |1,n\rangle\}
$$

中，两个候选态之差只包含一个非对角元 \(\tau_{n+1,n}\)。

对每个块作最优二元区分，得到：

$$
p_{\mathrm{succ}}^{\max}(\tau)
=
\frac12\left(1+\sum_{n=0}^{N-2}|\tau_{n+1,n}|\right).
$$

由正性：

$$
|\tau_{n+1,n}|
\le
\sqrt{\tau_{nn}\tau_{n+1,n+1}}.
$$

令 \(q_n=\sqrt{\tau_{nn}}\)，则 \(\sum_nq_n^2=1\)，并且：

$$
\sum_n|\tau_{n+1,n}|
\le
q^{\mathsf T}\frac{L_N+L_N^\dagger}{2}q.
$$

路径矩阵 \((L_N+L_N^\dagger)/2\) 的最大本征值为：

$$
\cos\frac{\pi}{N+1},
$$

对应归一化向量：

$$
\boxed{
q_n=
\sqrt{\frac2{N+1}}
\sin\frac{(n+1)\pi}{N+1}.
}
\tag{374.3}
$$

取纯参考态 \(|q\rangle\langle q|\)，再使用式（373.4）的测量，达到该上界。∎

这给出了当前任务的完整优化，而不只是一个不能达到的下界。

### 离散临界与连续精度

$$
N=1
\quad\Rightarrow\quad
p_{\mathrm{succ}}^{\max}=\frac12.
$$

没有相邻能量层，完全无法取得相位区分优势。

$$
N=2
\quad\Rightarrow\quad
p_{\mathrm{succ}}^{\max}=\frac34.
$$

相干参考的作用首次出现，但不能完美区分。

随着 \(N\to\infty\)：

$$
p_{\mathrm{err}}^{\min}
\sim
\frac{\pi^2}{4(N+1)^2}.
$$

因此：

> **从零层到一条共振边，是“能不能读取”的离散临界；继续增长参考链，则改善“能够读取多准”。**

这与 Wigner–Araki–Yanase 型守恒限制相容：精确测量不与守恒量对易的量，不能无条件脱离装置的资源。([arXiv][4])

---

# 375．“参考系质量”不是一个标量：能实现门，不等于能测量同名可观测量

这里恰好能够与仓库已有定理进行精确对照。

`ChannelFidelityBridge.lean` 定义了一个有限交换酉：

$$
|0,n+1\rangle\longleftrightarrow|1,n\rangle,
$$

并固定两个无法匹配的边界态。源码证明该酉保持总激发数，将其收缩为 Kraus 通道，再计算相对于理想比特翻转的纠缠保真度。

对实参考振幅 \(c\)，该保真度等于：

$$
\boxed{
F_{\mathrm e}(c)
=
\left\|
\frac{L_N+L_N^\dagger}{2}c
\right\|^2.
}
\tag{375.1}
$$

因此仓库得到：

$$
\boxed{
\max_{\|c\|=1}F_{\mathrm e}(c)
=
\cos^2\frac{\pi}{N+1}.
}
\tag{375.2}
$$

注意，它与第374节的测量成功率不是同一个指标。

---

## 一个三能级奇偶实例

取：

$$
|c_{\mathrm{even}}\rangle
=
\frac{|0\rangle+|2\rangle}{\sqrt2}.
$$

它只占据偶数激发层，因此：

$$
\boxed{
\langle c_{\mathrm{even}}|L_3|c_{\mathrm{even}}\rangle=0.
}
\tag{375.3}
$$

所以它对第373节的第一阶相位测量没有帮助。

但：

$$
\boxed{
F_{\mathrm e}(c_{\mathrm{even}})
=
\frac12
=
\cos^2\frac\pi4,
}
\tag{375.4}
$$

已经达到这个三能级交换模型的最优门保真度。

### 为什么不矛盾？

理想比特翻转通道：

$$
\rho\mapsto X\rho X
$$

对 \(X\mapsto-X\) 不变。

但测量“\(X=+1\)还是\(X=-1\)”时，符号决定哪个结果被报告。

所以两项任务需要的相位信息不同。

**“这个参考态对某种门是最优的”，不能推成“它对全部观测与几何标定都最优”。**

这也解释了为什么奇偶结构可以影响任务可实现性，而不仅影响某个谱是否有零模。

---

# 376．真正控制精度的是共振链长度，而不只是总维数

将等间隔参考系推广到任意有限、非简并能谱。

## 定义376.1　目标能隙的参考共振图

设：

$$
H_R|a\rangle=\varepsilon_a|a\rangle,
$$

不同 \(a\) 的能量不同。

待测系统的两个能级之差为：

$$
\Delta>0.
$$

在参考谱中连接：

$$
a\longrightarrow b
\quad\text{当且仅当}\quad
\varepsilon_b-\varepsilon_a=\Delta.
$$

由于谱有限、能量严格沿边增加，而且每个能级最多有一个前驱与后继，这个图是有限条路径的并。

令最长路径包含 \(m_{\max}\) 个顶点。

## 定理376.1　共振链长度决定最佳相位测量

在只有这一参考系、联合读数严格保持总能量的模型中：

$$
\boxed{
p_{\mathrm{succ}}^{\max}
=
\frac12
\left(
1+\cos\frac{\pi}{m_{\max}+1}
\right).
}
\tag{376.1}
$$

### 证明

按总能量分块后，每条参考共振边对应一个二维相位比较块。

与定理374.1相同，参考态能够提供的总区分对比度，不超过这些路径的半邻接矩阵的最大本征值。

直和矩阵的最大本征值来自最长路径，等于：

$$
\cos\frac{\pi}{m_{\max}+1}.
$$

只在最长路径上准备正弦振幅参考态，即可达到。∎

因此，一个一千维参考系，如果没有任何一对能级相差 \(\Delta\)，也可能对这个相位任务完全无用。

反过来，一条很短但恰好共振的参考链，就能提供实际帮助。

---

## 高阶相干的离散截止

对参考能级：

$$
0,\epsilon_0,\ldots,(N-1)\epsilon_0,
$$

若目标能隙为：

$$
\Delta=k\epsilon_0,
\qquad k\in\mathbb N_+,
$$

则最长共振链为：

$$
\boxed{
m_{\max}
=
1+\left\lfloor\frac{N-1}{k}\right\rfloor.
}
\tag{376.2}
$$

特别地：

$$
\boxed{
k>N-1
\quad\Rightarrow\quad
m_{\max}=1
\quad\Rightarrow\quad
p_{\mathrm{succ}}^{\max}=\frac12.
}
\tag{376.3}
$$

**超过参考谱支撑的相干阶数，不是“很难看清”，而是在当前操作类中精确不可见。**

这是一条把离散能量差、观察能力和整数路径结构连接起来的临界定理。

---

# 377．5040现在给出一个新的、可以算尽的参考系边界

本节明确采用一个新的物理角色：

> 把5040的60个因数状态作为参考寄存器，而不是把它们全部当作待测系统，也不是使用此前的三态混合 Hamiltonian。

## 定义377.1　算术参考谱

令：

$$
\mathcal H_R
=
\operatorname{span}\{|d\rangle:d\mid5040\},
$$

$$
\boxed{
H_R|d\rangle=E_*\ln d\,|d\rangle.
}
\tag{377.1}
$$

等价的指数窗口为：

$$
0\le a_2\le4,\quad
0\le a_3\le2,\quad
0\le a_5,a_7\le1.
$$

因此：

$$
\dim\mathcal H_R=5\cdot3\cdot2\cdot2=60.
$$

项目的素数—黄金编码等价可以无损表示这个窗口，但不会自动证明这里的对数能量就是现实能谱。

---

## 定理377.1　对数能量共振等价于整数指数匹配

对整数向量 \(\delta\)，设：

$$
\Delta=E_*\sum_p\delta_p\ln p.
$$

两个参考状态相差 \(\Delta\)，当且仅当它们的指数差为 \(\delta\)。

### 证明

如果能量差相同，则：

$$
\sum_p(a'_p-a_p-\delta_p)\ln p=0.
$$

指数化，并把正、负指数移到两边，得到两个整数的素因数分解相等。

唯一分解迫使每条素数轴的指数都相等。∎

因此，在这个能量模型中，共振不是任意实数近似，而是一个精确的格点匹配问题。

对矩形指数窗口 \(0\le a_p\le L_p\)，最长 \(\delta\)-链为：

$$
\boxed{
m_{\max}
=
1+
\min_{\delta_p\ne0}
\left\lfloor\frac{L_p}{|\delta_p|}\right\rfloor.
}
\tag{377.2}
$$

证明是每次移动都消耗相应坐标余量；从恰当角点开始即可达到该上界。

---

## 5040与 \(15/14\) 的相干读取

取：

$$
\Delta=E_*\ln\frac{15}{14},
$$

对应：

$$
\delta=(-1,1,1,-1).
$$

由于5轴与7轴的深度都只有1：

$$
\boxed{m_{\max}=2.}
\tag{377.3}
$$

所以，即使优化全部60维参考态和全部允许的能量守恒读数，也只有：

$$
\boxed{
p_{\mathrm{succ}}^{\max}=\frac34.
}
\tag{377.4}
$$

这个最优值其实用一个两态参考就能达到：

$$
\boxed{
|r_{\mathrm{opt}}\rangle
=
\frac{|14\rangle+|15\rangle}{\sqrt2}.
}
\tag{377.5}
$$

若使用60个因数的均匀相干参考：

$$
|r_{\mathrm{flat}}\rangle
=
\frac1{\sqrt{60}}\sum_{d\mid5040}|d\rangle,
$$

可匹配的共振对共有8组，故对比度为：

$$
\boxed{
r=\frac8{60}=\frac2{15},
}
\tag{377.6}
$$

成功率只有：

$$
\boxed{
p_{\mathrm{succ}}=\frac{17}{30}.
}
\tag{377.7}
$$

若把同样的能量概率改为完全对角混合态：

$$
\tau_{\mathrm{diag}}=\frac1{60}\sum_{d\mid5040}|d\rangle\langle d|,
$$

则相位区分成功率又降回 \(1/2\)。

**同样的60个能级、同样的能量概率，可以具有不同的参考能力。相干不能由能量分布本身替代。**

---

## 更强的截止：两倍能隙完全不可见

对于：

$$
2\Delta=E_*\ln\frac{225}{196},
$$

需要指数差：

$$
2\delta=(-2,2,2,-2).
$$

但5040窗口的5轴与7轴都没有深度2，因此不存在任何匹配能量对。

考虑待测信号：

$$
|\psi_\pm\rangle
=
\frac{|4704\rangle\pm|5400\rangle}{\sqrt2}.
$$

两者正交，能量基概率相同，区别只在跨越 \(2\Delta\) 的相干。

在本节的参考与守恒条件下：

$$
\boxed{
p_{\mathrm{succ}}(\psi_+,\psi_-)=\frac12.
}
\tag{377.8}
$$

这不是说两态相同，而是当前参考无法让这个区别进入允许读数。

若把窗口扩展为：

$$
2^4\,3^2\,5^2\,7^2=176400,
$$

该能量差就开始可实现。这里的新整数只是一个明确选出的扩展窗口，不是新的普适临界常数。

而一个专门设计的三能级参考：

$$
\boxed{\{196,\ 210,\ 225\}}
$$

已经具有连续两条 \(15/14\) 共振边。

所以，“收集更多状态”未必比“提供恰好需要的共振结构”更有效。

---

# 378．精确可识别、有限噪声可识别与重复使用，是三件不同的事

设当前参考提供实对比度 \(r\)，则可以有效读取：

$$
Z,\qquad rX,\qquad rY.
$$

## 定理378.1　参考相干可以造成观察维数的离散跳变

对归一化算子族：

$$
\frac I{\sqrt2},\quad
\frac Z{\sqrt2},\quad
\frac{rX}{\sqrt2},\quad
\frac{rY}{\sqrt2},
$$

其 Hilbert–Schmidt Gram 行列式为：

$$
\boxed{\det G=r^4.}
\tag{378.1}
$$

因此：

$$
r=0
\quad\Rightarrow\quad
\text{只保留两维线性读数};
$$

$$
r\ne0
\quad\Rightarrow\quad
\text{线性包恢复完整量子比特效果空间}.
$$

### 证明

这四个方向正交，Gram 矩阵为：

$$
\operatorname{diag}(1,1,r^2,r^2).
$$

∎

但 \(r\) 很小时，两个相干方向的重建非常不稳定。

例如对：

$$
\rho_x=\frac{I+xX}{2},
$$

当前测量给出：

$$
p_\pm(x)=\frac{1\pm rx}{2}.
$$

单次 Fisher 信息为：

$$
\boxed{
\mathcal I_x=\frac{r^2}{1-r^2x^2}.
}
\tag{378.2}
$$

在 \(x=0\) 附近，\(n\) 次独立且同样准备的系统—参考实验，对局部无偏估计有：

$$
\operatorname{Var}(\widehat x)\ge\frac1{nr^2}.
$$

**精确秩已经恢复，不代表有限样本代价没有爆炸。**

---

## 同一个参考态也不能默认无限重复使用

以上独立样本公式要求每次参考的准备条件相同。

如果反复使用同一个参考，它可能与前面的信号、仪器和记录相关，下一次有效测量就未必还是同一个 \(E_\pm^{(\tau)}\)。

量子参考系的退化与可使用次数，本身就是需要动力学分析的资源问题。([arXiv][5])

因此，不能把：

$$
\text{更高的刷新次数}
$$

自动转换成：

$$
\text{相同参考质量下无限增加的信息}.
$$

需要同时追踪参考状态、相关性和复位资源。

---

# 379．参考系为什么会表现成近似经典的坐标与时钟？

现在可以把这些有限结果接回物理时空。

## 第一层：精确的关系量

第372节的相对位置，是系统—参考联合空间上的精确可观测量。

第373节的相位比较，同样是保持总激发数的联合读数。

这些量不需要先假设一个绝对外部原点。

## 第二层：把参考状态固定以后，得到系统上的有效读数

例如：

$$
E_\pm^{(\tau)}=\frac12(I\pm rX).
$$

当 \(r\) 接近一时，观察者可以把它近似看成理想的：

$$
P_\pm^X=\frac12(I\pm X).
$$

最坏单次结果概率误差为：

$$
\boxed{
\sup_\rho
\left|
\operatorname{Tr}\rho(E_+^{(\tau)}-P_+^X)
\right|
=
\frac{1-r}{2}.
}
\tag{379.1}
$$

于是，一个看起来“绝对明确”的相位方向，可以是一个足够好参考系统所诱导的有效描述，而不是必须存在于模型外部的东西。([arXiv][3])

但这只控制结果概率。它没有自动控制测量后的状态、连续反馈或多步几何重建；那些需要完整仪器的过程证书。

---

## 第三层：参考本身可以走时

若参考自由演化为：

$$
\tau(t)
=
e^{-i\epsilon_0N_Rt/\hbar}
\tau(0)
e^{i\epsilon_0N_Rt/\hbar},
$$

则其第 \(k\) 阶相干满足：

$$
\boxed{
r_k(t)
=
e^{-ik\epsilon_0t/\hbar}r_k(0),
\qquad
r_k=\operatorname{Tr}(\tau L_N^k).
}
\tag{379.2}
$$

参考相位的方向随时间旋转，但能读取哪些谐波仍受：

$$
k\le N-1
$$

限制。

因此，内部钟并不是一份抽象的“当前时间数值”，而是：

$$
\boxed{
\text{谱支撑}
+
\text{相干制备}
+
\text{相位演化}
+
\text{相应读出}.
}
$$

这与此前的刷新率讨论相容：有高频相位不等于能够形成同样高频的可靠记录。

---

## 一般守恒约束也会限制锚点精度

设完整测量酉 \(U\) 保持：

$$
L_{\mathrm{tot}}=N_S+N_A,
$$

指针 \(M\) 满足：

$$
[M,N_A]=0.
$$

定义测量 \(X\) 的噪声算子：

$$
N_{\mathrm{err}}
=
U^\dagger(I\otimes M)U-X\otimes I.
$$

对系统—装置初始乘积态，Robertson 不等式给出：

$$
\boxed{
\epsilon_X^2
\ge
\frac{|\langle[X,N_S]\rangle|^2}
{4\left(\operatorname{Var}N_S+\operatorname{Var}N_A\right)},
}
\tag{379.3}
$$

其中：

$$
\epsilon_X^2=\langle N_{\mathrm{err}}^2\rangle.
$$

### 证明

由守恒和指针条件：

$$
[N_{\mathrm{err}},L_{\mathrm{tot}}]
=
-[X,N_S]\otimes I.
$$

再使用：

$$
\operatorname{Var}N_{\mathrm{err}}
\le\epsilon_X^2
$$

及乘积初态下总方差相加。∎

这是与前文单次错误率不同的**均方噪声指标**，不能把数值直接互换。它所体现的守恒—测量精度关系，是量子测量理论中已有的定量限制。([arXiv][4])

**参考系足够大、足够相干、足够稳定时，“固定坐标与理想钟”可以成为有效近似；它们不必是基本层面无资源成本的对象。**

但由此还不能直接推出 Lorentz 度量或 Einstein 方程。共同传播锥、钟尺比例、局域性和反作用，仍须与这些参考条件一起满足。

---

# 380．这一轮完成了哪一项闭合？

此前的重建链是：

$$
\text{带标签干预}
\longrightarrow
\text{可识别的耦合结构}.
$$

本轮把标签的物理来源加入：

$$
\boxed{
\text{有限参考态与守恒结构}
\longrightarrow
\text{实际可实施的关系读数}
\longrightarrow
\text{可用的干预与几何锚点}.
}
\tag{380.1}
$$

这带来三个不应混淆的量：

| 对象        | 本轮的具体判据         |
| --------- | --------------- |
| 总状态资源     | 参考 Hilbert 空间维数 |
| 对某能隙的可用相干 | 参考能谱中的共振边及其权重   |
| 最优相位读取精度  | 最长共振链的谱半径       |

特别地：

$$
\boxed{
\text{参考系维数很大}
\not\Rightarrow
\text{能够读取任意相位};
}
$$

$$
\boxed{
\text{当前效果空间满秩}
\not\Rightarrow
\text{有限噪声下重建稳定};
}
$$

$$
\boxed{
\text{某项门保真度最优}
\not\Rightarrow
\text{其他观测任务也最优}.
}
$$

---

## 与仓库的具体连接

本轮固定读取：

```text
c2ac139a260c576df2372799ad42c4547528913c
```

相关模块的分工可以保持清楚：

| 已有基础                          | 本轮继续发展的证明        |
| ----------------------------- | ---------------- |
| `UnitaryNaturalSelector.lean` | 裸对称结构不能无条件给出唯一锚点 |
| `ChannelFidelityBridge.lean`  | 有限参考与严格守恒的具体联合实现 |
| `ReferenceFrameTaxExact.lean` | 指定通道的最优资源—保真度关系  |
| `PrimeAxisEncoding.lean`      | 算术状态与规范寄存器的无损对应  |

新增的中心定理是：

$$
\boxed{
\text{目标能隙的最长参考共振链}
\longrightarrow
\text{最优关系相位识别概率}.
}
$$

它需要形式化的主要部分是：有限能量分块、正矩阵二阶子式、路径邻接谱、最优二元区分以及素数指数匹配。

不能只引用仓库的 \(\cos^2\) 保真度定理，就宣称本轮不同任务的全部结论已经由内核证明；它们有不同的定义与量词。

### 本轮核验

已完成 **62项命名的精确整数或符号检查**，以及一组覆盖180种能级数—能隙组合的浮点谱交叉检查。

包括：有限平移的相对投影、总激发守恒、关系相位效果、最优三能级参考、奇偶参考的任务差异、5040的八组共振边、两倍能隙不可见性，以及观察效果的秩变化。

[核验脚本](sandbox:/mnt/data/observer_formalization/check_quantum_reference_geometry.py)
[核验结果](sandbox:/mnt/data/observer_formalization/quantum_reference_geometry_checks.json)

**本轮未执行 Lean 内核编译。**数值谱检查带有明确容差，不作为区间证书；有限检查也不把所选对数能谱认证为现实物理定律。

---

# 结论

这一轮最重要的推进，是把“观察者拥有一个坐标系”从默认前提，改写成了一个需要物理实现的命题。

观察者可以通过关系量成为描述中心，而不需要拥有绝对位置。可是，要把这些关系量进一步近似为稳定的方向、锐利的相位和可靠的钟，就需要合适的参考态、能量结构和控制资源。

5040由此获得了一项新的、限定明确的临界意义：

$$
\boxed{
\text{它的60态因数参考窗口，
对 }\ln(15/14)\text{ 能隙只有两态共振链};
}
$$

因此：

$$
\boxed{
p_{\mathrm{succ}}^{\max}=\frac34.
}
$$

而对两倍能隙：

$$
\boxed{
\ln(225/196),
}
$$

该窗口没有匹配参考边，对相应相位区别完全无能为力。

**决定这件事的，不是“5040很大”或“它有很多因数”，而是 \((4,2,1,1)\) 在特定方向上只允许移动多少步。**

于是，我们可以把你此前的直觉进一步收紧为：

> **观察者能够从波中读取什么，不仅取决于波本身，也取决于观察者内部是否拥有与它匹配的关系结构。离散约束决定哪些比较能够发生；相干资源决定比较有多准确；共同的参考、控制和传播条件，才使这些比较能够被组织成一套稳定的时空描述。**

这使“时空由量子观察者的因果信息流形成”又少了一项隐藏前提：**我们不再把尺、钟、原点和相位标准放在宇宙之外，而开始要求它们与被观察世界一起，满足同一套可实现性与资源约束。**

[1]: https://arxiv.org/abs/quant-ph/0610030 "https://arxiv.org/abs/quant-ph/0610030"
[2]: https://arxiv.org/html/2302.05354v1 "https://arxiv.org/html/2302.05354v1"
[3]: https://arxiv.org/html/1510.02063v3 "https://arxiv.org/html/1510.02063v3"
[4]: https://arxiv.org/abs/quant-ph/0112154 "https://arxiv.org/abs/quant-ph/0112154"
[5]: https://arxiv.org/abs/quant-ph/0602069 "https://arxiv.org/abs/quant-ph/0602069"

# 381．关系切片先于外部时间参数

设 $G=(V,E,s,t)$ 是有限有向图，其底层无向图连通且 $V\ne\varnothing$，并固定根 $r\in V$。顶点表示已经声明的关系切面，不预设为外部时空点。固定非零有限维复 Hilbert 空间 $\mathcal H$，并令每条边 $e$ 携带酉运输 $U_e:\mathcal H\to\mathcal H$。把
$\bigoplus_{v\in V}\mathcal H$ 识别为时钟标记空间 $\mathbb C^V\otimes\mathcal H$。若 $\Psi=(\psi_v)_{v\in V}$，定义

$$
A_e\Psi=\psi_{t(e)}-U_e\psi_{s(e)},\qquad
K_G=\sum_{e\in E}\lambda_e A_e^\dagger A_e,\quad \lambda_e>0.
$$

这里 $K_G$ 是关系相容性的静态约束算子；把它另行解释为实际装置的 Hamiltonian 需要额外的实现假设。

## 定理 381.1（零约束的逐边判据）

$$
K_G\succeq0,\qquad
K_G\Psi=0\Longleftrightarrow
\psi_{t(e)}=U_e\psi_{s(e)}\quad(\forall e\in E).
$$

### 证明

$$
\langle\Psi,K_G\Psi\rangle
=\sum_e\lambda_e\|\psi_{t(e)}-U_e\psi_{s(e)}\|^2\ge0.
$$

若 $K_G\Psi=0$，则左端为零，严格正的 $\lambda_e$ 和非负的各项迫使每项均为零。反向蕴含则由 $A_e\Psi=0$ 逐项相加得到。∎

在底层无向路径上，正向经过 $e$ 使用 $U_e$，反向经过 $e$ 使用 $U_e^{-1}$，并记路径复合为 $U_\gamma$。定义根处向量共同不动子空间

$$
\mathcal F_r=
\{x\in\mathcal H:U_\gamma x=x\text{ 对每条根处闭走法 }\gamma\}.
$$

## 定理 381.2（固定子空间与共同实现）

评价映射

$$
\operatorname{ev}_r:\ker K_G\longrightarrow\mathcal F_r,\qquad
\Psi\longmapsto\psi_r
$$

是线性双射。因此，存在归一化的共同向量切片，当且仅当 $\mathcal F_r\ne\{0\}$。一般图的核可以为零，不能由连通性单独推出归一化历史态存在。

### 证明

零约束沿路径递推给出 $\psi_v=U_\gamma\psi_r$。闭走法因此固定 $\psi_r$，评价映射落入 $\mathcal F_r$，且连通性使其单射。反之，取 $x\in\mathcal F_r$，对每个 $v$ 选一条根到 $v$ 的路径 $\gamma_v$，置 $\psi_v=U_{\gamma_v}x$。两条路径的差组成根处闭走法，故定义与路径选择无关，并满足全部边约束。∎

形式上使用反向路径只是检验相容性，不授予观察者逆转实际过程的操作权限。图上的酉连接与向量丛 Laplacian 的直接框架可参见 Kenyon 的原始论文 [arXiv:1001.4028](https://arxiv.org/abs/1001.4028)，这里采用的是有限维、有限图的相应构造。

# 382．历史态、条件切片与相干—去相干区别

对链图 $0\to1\to\cdots\to N$，其中 $N\ge1$，把 $\bigoplus_{n=0}^N\mathcal H$ 识别为 $\mathbb C^{N+1}\otimes\mathcal H$。取酉 $U_0,\ldots,U_{N-1}$，令

$$
V_0=I,\qquad V_n=U_{n-1}\cdots U_0,
$$

并定义

$$
W\psi=\frac1{\sqrt{N+1}}\sum_{n=0}^N|n\rangle\otimes V_n\psi .
$$

则 $W^\dagger W=I$，且 $\operatorname{ran}W=\ker K_G$。对初态密度矩阵 $\rho_0$，令 $\Gamma=W\rho_0W^\dagger$。

## 定理 382.1（历史态的条件切片）

令 $P_n=|n\rangle\langle n|$。则

$$
\Pr(n)=\frac1{N+1},\qquad
\rho_n=V_n\rho_0V_n^\dagger,
$$

并且对任意 $0\preceq F\preceq I$，

$$
\Pr(F\mid n)=\operatorname{Tr}(V_n\rho_0V_n^\dagger F).
$$

### 证明

酉性给出

$$
\langle W\psi,W\phi\rangle
=\frac1{N+1}\sum_n\langle V_n\psi,V_n\phi\rangle
=\langle\psi,\phi\rangle .
$$

链上的每个分量满足 $V_{n+1}=U_nV_n$，故像空间正好是零约束空间。展开

$$
\Gamma=\frac1{N+1}\sum_{n,m}|n\rangle\langle m|\otimes
V_n\rho_0V_m^\dagger
$$

并对钟空间取条件块，即得所述概率和条件态。∎

对一般图，密度历史态可由任意非零 $\Psi\in\ker K_G$ 归一化后构造；若 $\ker K_G=\{0\}$，则没有这样的归一化态。链图之所以没有这个障碍，是因为所有闭走法的运输均为恒等（往返边的运输相互抵消），$W$ 已显式给出非零核向量。Aharonov 等人的原始论文 [quant-ph/0405098v2](https://arxiv.org/abs/quant-ph/0405098) 的式 (1) 与 Claim 3.3 讨论的是电路历史态和传播项的零能量结构；这里仅借用这种历史态编码的数学形式。

定义钟去相干态

$$
\Gamma_{\mathrm{diag}}
=\frac1{N+1}\sum_n|n\rangle\langle n|\otimes V_n\rho_0V_n^\dagger .
$$

## 定理 382.2（局部钟读数不恢复跨切片相干）

$\Gamma$ 与 $\Gamma_{\mathrm{diag}}$ 对所有 $P_n\otimes F$ 给出相同结果；当 $\rho_0\ne0$ 时两者不同。

### 证明

两态钟对角块相同，故所有 $P_n\otimes F$ 的迹相同。相干历史的 $n,m$ 块为

$$
(N+1)^{-1}V_n\rho_0V_m^\dagger ,
$$

其在 $\rho_0\ne0$ 时非零；去相干态的相应块为零。∎

因此，逐切片条件概率的完全一致不能推出跨切片相干关系的一致。

# 383．规范运输与绕行不变量

对每个顶点选酉 $G_v$，同时定义

$$
\rho'_v=G_v\rho_vG_v^\dagger,\qquad
F'_v=G_vF_vG_v^\dagger,\qquad
U'_e=G_{t(e)}U_eG_{s(e)}^\dagger .
$$

## 定理 383.1（逐切面换表示）

若 $\rho_{t(e)}=U_e\rho_{s(e)}U_e^\dagger$，则

$$
\rho'_{t(e)}=U'_e\rho'_{s(e)}U_e'{}^\dagger ,
\qquad
\operatorname{Tr}(\rho'_vF'_v)=\operatorname{Tr}(\rho_vF_v).
$$

### 证明

把定义代入，邻接的 $G_v^\dagger G_v$ 消去；概率等式由迹的循环性质得到。∎

在链上取 $G_n=V_n^\dagger$，则

$$
U'_n=G_{n+1}U_nG_n^\dagger=I,
$$

并可把 $\rho_n$ 全部写成 $\rho_0$，同时把变化移到 $F'_n=V_n^\dagger F_nV_n$。这是表示等价，不是免费施加的受控操作。

## 定理 383.2（向量 Holonomy 与密度共轭必须分开）

闭走法 $\gamma$ 的向量不动条件是 $U_\gamma x=x$，而密度不变条件是

$$
U_\gamma\rho U_\gamma^\dagger=\rho .
$$

后者只说明 $\rho$ 在共轭作用下不变，不能替代前者的共同向量条件，也不能保证 $\ker K_G\ne0$ 的向量实现。规范变换把 $U_\gamma$ 共轭为 $G_rU_\gamma G_r^\dagger$，因此保留其谱和共轭类。

### 证明

沿闭走法 $\gamma=e_k\cdots e_1$ 相乘边运输，变换后的中间顶点因 $G_{v_j}^\dagger G_{v_j}=I$ 逐一消去，留下

$$
U'_\gamma
=(G_rU_{e_k}G_{v_{k-1}}^\dagger)\cdots
(G_{v_1}U_{e_1}G_r^\dagger)
=G_rU_\gamma G_r^\dagger .
$$

因此向量固定空间只作 $G_r$ 的酉像，密度共轭固定性则按同一等式保持。两种条件仍有严格区别：单顶点带一条闭环、$U_\gamma=-I$ 时，$U_\gamma x=x$ 强迫 $x=0$，而任意密度矩阵都满足 $(-I)\rho(-I)^\dagger=\rho$。∎

# 384．实际仪器、条件化与记录

令 $h$ 为已经取得的历史记录，且包含选择下一步所需的控制、参考、校准和权限。选择器只依赖已纳入的信息：

$$
a=\pi(h).
$$

对每个获准设置 $a$，取有限 instrument $\{\Phi_{a,y}\}_{y\in Y_a}$，其中每个 $\Phi_{a,y}$ 完全正且保迹不增，并且 $\sum_y\Phi_{a,y}$ 保迹。得到结果 $y$ 后追加

$$
h'=h\Vert(a,y,\text{来源与校准记录}),
\qquad
\sigma_{h'}=\Phi_{a,y}(\sigma_h).
$$

只对非零分支概率作归一化条件态。对与策略相容的合法词 $w=(a_1,y_1)\cdots(a_n,y_n)$，记 $\Phi_j=\Phi_{a_j,y_j}$，并令

$$
\Phi_w=\Phi_n\circ\cdots\circ\Phi_1,
\qquad
E_w=\Phi_1^*\circ\cdots\circ\Phi_n^*(I).
$$

## 定理 384.1（合法记录词的迹拉回）

$$
p(w)=\operatorname{Tr}(\Phi_w(\rho_0))
=\operatorname{Tr}(\rho_0E_w).
$$

若 $p(w)>0$，则 $\rho_w=\Phi_w(\rho_0)/p(w)$。

### 证明

若某个前缀的迹为零，其半正定的未归一化态必为零；后续线性分支保持零态，因此该前缀的每个延伸词概率均为零，第一式仍成立。对所有前缀概率均为正的路径，逐步相乘条件概率时归一化因子望远镜消去，得到第一式。由

$$
\operatorname{Tr}(F\Phi(X))
=\operatorname{Tr}(\Phi^*(F)X)
$$

从末端 $I$ 逐步拉回，得到第二式；非零时除以总迹即得条件态。∎

此处的 $p(w)$ 是实际执行并留下记录的联合概率，不是把若干固定历史切片概率相乘。Davies–Lewis 的测量公理 [DOI:10.1007/BF01647093](https://doi.org/10.1007/BF01647093) 与 Ozawa 的 instrument 形式 [quant-ph/0107090v1](https://arxiv.org/abs/quant-ph/0107090) 给出结果分支和后继状态的标准框架。

## 命题 384.2（追加记录的有限词非返回）

令 $w$ 是声明接口中的有限原始记录词，$u$ 是同一接口允许的非空追加词。若物理状态、相位或某个内部寄存器在追加前后相同，则追加后的原始记录仍为 $w\Vert u$，并满足

$$
|w\Vert u|=|w|+|u|>|w|.
$$

### 证明

原始记录按词的字面连接定义，非空 $u$ 具有 $|u|\ge1$；有限词长度的连接律给出等式和严格不等式。因此有限声明域内的周期返回不能等同于原始记录返回；该命题只涉及每个给定有限词，不声称有限装置拥有无限容量。∎

# 385．声明的有限仪器词接口能区分什么

令 $\mathcal D$ 是双方候选准备都能实际执行的共同合法域。它包含同一有限词集合 $\mathcal L$、同一策略、同一仪器分支和同一记录标签；若某一步权限只对一方存在，则该权限差异及相应失败记录必须先纳入接口，不能把它从概率读数中删去。对每个 $w\in\mathcal L$，声明相同的末端 yes 检验 $F_w$，其中 $F_w$ 是 Hermitian 且 $0\preceq F_w\preceq I$。定义未归一化的联合概率

$$
p_\rho(w,F)=\operatorname{Tr}[\Phi_w(\rho)F],
$$

它是“出现记录词 $w$ 且末端回答 yes”的联合概率，而不是条件概率 $p(F\mid w)$。定义拉回效果

$$
E_{w,F}=\Phi_w^*(F_w).
$$

完全正映射的对偶保持 Hermitian。并且

$$
0\preceq E_{w,F}\preceq\Phi_w^*(I)\preceq I.
$$

最后一个不等式来自每个分支的保迹不增性及其复合；前一个不等式来自 $0\preceq F_w\preceq I$ 和对偶的正性。因此所有候选都在同一 $\mathcal D$ 上比较，令

$$
\Delta=\rho-\sigma,\qquad
\mathcal V_{\mathcal L}=\operatorname{span}_{\mathbb R}\{E_{w,F}:w\in\mathcal L\}.
$$

## 定理 385.1（有限合法接口的精确判据）

在共同域 $\mathcal D$ 上，两准备对所有声明的 $(w,F_w)$ 给出相同末端联合概率，当且仅当

$$
\operatorname{Tr}(\Delta E)=0
\quad\text{对所有 }E\in\mathcal V_{\mathcal L}.
$$

因而它们可由该接口区分，当且仅当 $\Delta\notin\mathcal V_{\mathcal L}^{\perp}$，其中正交取 Hermitian 矩阵上的实迹配对

$$
\langle A,B\rangle_{\mathbb R}=\operatorname{Tr}(AB)\in\mathbb R.
$$

### 证明

对每个合法词，

$$
p_\rho(w,F_w)-p_\sigma(w,F_w)
=\operatorname{Tr}((\rho-\sigma)\Phi_w^*(F_w))
=\operatorname{Tr}(\Delta E_{w,F}).
$$

所以全部联合读数相等，当且仅当差值对生成集合为零；线性性把这等价地扩展到其有限实线性张成空间。若候选依赖不同的权限域，域成员资格和失败记录本身就是接口读数，此时上述共同域的概率判据不能抹除该差异。∎

### 应用证明（相干历史与两步仪器）

空词且无中间操作时，末端效果为钟对角的 $P_n\otimes F$，其确实不能检测 $\Gamma-\Gamma_{\mathrm{diag}}$ 的钟非对角块。对含操作的普通词，末端 $F$ 的对角性不推出拉回效果 $E=\Phi_w^*(F)$ 对角；必须直接要求每个拉回效果本身对角，才能应用同一相位盲结论。拉回效果的非对角性只是必要条件，未必足以区分；精确条件是存在某个声明的 $E$ 使

$$
\operatorname{Tr}\bigl[(\Gamma-\Gamma_{\mathrm{diag}})E\bigr]\ne0.
$$

因此不能声称每个允许混合的操作都能区分这两个历史。

作为该应用的具体命题，考虑两个单步效果完全相同的二能级 instrument。第一仪器的 Kraus 分支为

$$
K_y=
\begin{cases}
|0\rangle\langle0|,&y=0,\\
|1\rangle\langle1|,&y=1,
\end{cases}
$$

第二仪器为 $\widetilde K_y=XK_y$，其中 $X$ 是 Pauli-$X$。则

$$
K_y^\dagger K_y=\widetilde K_y^\dagger\widetilde K_y\quad(y=0,1),
\qquad
\sum_yK_y^\dagger K_y=\sum_y\widetilde K_y^\dagger\widetilde K_y=I.
$$

## 命题 385.2（相同单步效果不决定两步联合权重）

取初态 $|0\rangle\langle0|$，第一次结果 $y=0$，第二步末端效果 $I-|0\rangle\langle0|$。第一仪器给出的两步权重为 $0$，第二仪器给出的两步权重为 $1$。

### 证明

第一仪器在结果 $y=0$ 后仍把状态置于 $|0\rangle$，故末端效果的权重为 $0$。第二仪器先以 $K_0$ 得到 $|0\rangle$，再由 $X$ 置为 $|1\rangle$，故末端效果的权重为 $1$。因此单步效果生成的空间不足以决定两步接口；合法词的后继通道及其拉回效果必须一并纳入 $\mathcal V_{\mathcal L}$。∎

# 386．可见能隙、周期性与驻定生成元

设 $\hbar>0$，$H=H^\dagger$ 为有限维 Hamiltonian，

$$
H=\sum_aE_aP_a,\qquad
\rho(t)=e^{-iHt/\hbar}\rho_0e^{iHt/\hbar},
$$

并令 $F=F^\dagger$ 为固定效果。定义 $f_F(t)=\operatorname{Tr}(\rho(t)F)$ 和

$$
\Omega=\{(E_a-E_b)/\hbar\}.
$$

称 $f_F$ 非恒定，若存在 $t,u$ 使 $f_F(t)\ne f_F(u)$；称其周期，若存在 $T>0$ 使 $f_F(t+T)=f_F(t)$ 对所有 $t$ 成立。

## 定理 386.1（实际可见频率）

$$
f_F(t)=\sum_{\omega\in\Omega}c_\omega e^{i\omega t},\qquad
c_\omega=\sum_{E_a-E_b=\hbar\omega}
\operatorname{Tr}(\rho_0P_aFP_b).
$$

因此 $f_F$ 恒定，当且仅当所有 $\omega\ne0$ 的 $c_\omega$ 均为零；给定 $T>0$，

$$
f_F(t+T)=f_F(t)\ \forall t
\Longleftrightarrow
(e^{i\omega T}-1)c_\omega=0
\quad\text{对每个 }\omega\in\Omega.
$$

### 证明

谱分解直接给出有限指数和。不同实频率的指数函数线性独立，可由 Vandermonde 导数矩阵验证；将 $f_F(t+T)-f_F(t)$ 展开后再使用线性独立性即得周期判据。零频率项是 DC 项，不影响恒定性或周期性判据。∎

### 离散时钟嵌入

给定校准时刻

$$
0=t_0<t_1<\cdots<t_N,
$$

定义

$$
U_n=\exp\!\left[-\frac{iH(t_{n+1}-t_n)}{\hbar}\right],\qquad
V_n=\exp\!\left[-\frac{iHt_n}{\hbar}\right].
$$

于是 $V_0=I$ 且 $V_{n+1}=U_nV_n$。以 $\rho(0)=\rho_0$ 为初态时，历史态的条件切片为 $\rho_n=V_n\rho_0V_n^\dagger$，并满足

$$
\operatorname{Tr}(\rho_nF)=f_F(t_n).
$$

若时间原点任取 $t_0$，则以 $\rho(t_0)$ 为初态并使用 $V_n=\exp[-iH(t_n-t_0)/\hbar]$；相应条件响应仍是同一 $f_F(t_n)$ 的取样。

## 命题 386.2（二态可见振荡）

取 $\hbar>0$、$\omega\ne0$，

$$
H=\frac{\hbar\omega}{2}Z,\qquad
\rho_0=|+\rangle\langle+|,\qquad
F_+=|+\rangle\langle+|.
$$

则 $f_+(t)=(1+\cos(\omega t))/2$，它是非恒定周期响应。

### 证明

$$
|\psi(t)\rangle
=\frac{e^{-i\omega t/2}|0\rangle+e^{i\omega t/2}|1\rangle}{\sqrt2},\qquad
|\langle+|\psi(t)\rangle|^2=\cos^2(\omega t/2)
=\frac{1+\cos(\omega t)}2.
$$

因 $\omega\ne0$，取例如 $t=0$ 和 $t=\pi/|\omega|$ 即得不同读数；周期为 $2\pi/|\omega|$。∎

## 命题 386.3（零空间中的驻定密度）

若 $K=K^\dagger$、$KW=0$ 且 $W^\dagger W=I$，则对任意密度矩阵 $\rho$，$\Gamma=W\rho W^\dagger$ 也是密度矩阵，并有

$$
K\Gamma=\Gamma K=0,\qquad e^{-isK}\Gamma e^{isK}=\Gamma\quad(\forall s\in\mathbb R).
$$

在 $K=K^\dagger$ 的假设下，上述驻定等式只需 $KW=0$，不需要 $W^\dagger W=I$；等距条件保证 $\Gamma$ 的迹为一。同样，若 $\operatorname{supp}(\Gamma)\subseteq\ker K$，则上述驻定等式成立。

### 证明

由 $KW=0$ 得 $K\Gamma=0$；$K=K^\dagger$ 给出 $W^\dagger K=0$，从而 $\Gamma K=0$。幂级数展开 $e^{-isK}$ 后，$K\Gamma=\Gamma K=0$ 使共轭逐项化为 $\Gamma$。支撑条件等价地给出同样的左右零作用。∎

因此对任意固定记录检验 $R$，$\operatorname{Tr}(R e^{-isK}\Gamma e^{isK})=\operatorname{Tr}(R\Gamma)$ 与 $s$ 无关。这只说明该静态约束在其零空间上驻定；它不自动产生滴答、测量记录或新的后继。历史编码、物理生成元和记录形成是三个不同任务。Page–Wootters 的原始条件内部钟论文 [DOI:10.1103/PhysRevD.27.2885](https://doi.org/10.1103/PhysRevD.27.2885) 支持条件钟的关系式描述，但不替代这里的有限接口假设。

# 387．别名、共同相位参考与校准

设相对于共同相位参考的复响应为 $z(t)=ae^{i\omega t}$，其中 $a\ne0$，并以 $\Delta>0$ 均匀采样 $S_\Delta(z)=(z(n\Delta))_{n\ge0}$。

## 定理 387.1（精确混叠判据）

对 $z'(t)=a'e^{i\omega't}$，

$$
S_\Delta(z)=S_\Delta(z')
\Longleftrightarrow
 a=a',\quad(\omega'-\omega)\Delta\in2\pi\mathbb Z .
$$

### 证明

$n=0$ 给出 $a=a'$，$n=1$ 给出 $e^{i(\omega'-\omega)\Delta}=1$。反向蕴含由整数倍采样立即成立。∎

若 $\omega\Delta=2\pi k$ 且 $k\ne0$，所有样本均为 $a$，但 $z$ 仍是非恒定函数。只观察模长时，纯相位频率不具可识别性；必须把参考、采样规则和事件对应一起声明。

## 命题 387.2（相位重标定导数与恒定性）

令 $\varphi:\mathbb R\to\mathbb R$ 是 $C^1$ 严格递增双射，且 $\varphi'(t)>0$。设 $\theta(t)=\omega t+\theta_0$，$\widetilde\theta(\tau)=\theta(\varphi^{-1}(\tau))$。则

$$
\frac{d\widetilde\theta}{d\tau}\bigg|_{\tau=\varphi(t)}
=\frac{\omega}{\varphi'(t)}.
$$

并且 $\widetilde f(\tau)=f(\varphi^{-1}(\tau))$ 恒定，当且仅当 $f$ 恒定。

### 证明

逆函数定理给 $(\varphi^{-1})'(\varphi(t))=1/\varphi'(t)$；链式法则因此给出 $d\widetilde\theta/d\tau=\omega/\varphi'(t)$。若把重标定后的相位简记为 $\theta$，这就是 $d\theta/d\tau=\omega/\varphi'(t)$。由于 $\varphi$ 是双射，$\{\varphi^{-1}(\tau):\tau\in\mathbb R\}=\mathbb R$，故一个函数在原变量上恒定，当且仅当其与该双射复合后恒定。∎

对线性校准 $\tau=at+b$（$a>0$），周期和频率按 $T_\tau=aT_t$、$\omega_\tau=\omega_t/a$ 变换。非线性重标定可改变固定数值周期的形式，却不改变事件与结果的对应关系；这不是由换坐标推出物理时间膨胀。有限相同样本也不能证明连续响应在全域恒定或具有某个全局周期。

# 388．有条件的联合命题与文献边界

## 定理 388.1（静态承载、条件振荡和观察运输）

在有限维、给定酉边、$\hbar>0$、Hermitian $H$、初态、钟标签及共同合法 instrument 接口下：

1. 静态正约束的零空间精确表达逐边合法运输；共同向量实现由根处 Holonomy 的固定子空间决定，且一般图允许零核。
2. 链式历史态的钟条件块给出阶段态和单切片概率；相干历史与钟去相干历史的局部读数可以相同。
3. 联合规范运输保持运输关系和迹概率，并把闭环运输变为根处共轭，因此不能消除闭环共轭类。
4. 实际记录由合法 instrument 词、非零条件化和追加记录共同定义；不能以单切片概率乘积替代词概率。
5. 有限接口能区分的准备恰由其共同域上的拉回 Hermitian 效果的实线性张成空间决定；单步效果不足以确定两步联合律。
6. 可见振荡由 $(H,\rho_0,F)$ 的非零能隙系数决定；有限采样和重标定必须经过别名与共同参考条件检查。全局周期只在定理 386.1 的系数条件下成立，并非任意 $H$ 自动保证。
7. 若把 $K_G$ 作为生成元并限制在其零空间，历史态驻定；因此静态表示不自动产生新记录。

### 证明

(1)–(2) 由定理 381.1–382.2，(3) 由定理 383.1–383.2，(4) 由定理 384.1 与命题 384.2，(5) 由定理 385.1 及命题 385.2，(6) 由定理 386.1、命题 386.2 和定理 387.1–命题 387.2，(7) 由命题 386.3。每一项都保留其模型假设和操作范围，不能把条件历史编码提升为宇宙实际状态，也不能把形式反向路径提升为逆向操作权。∎

与上述数学构造直接相关的原始来源如下。Aharonov 等人的 [quant-ph/0405098v2](https://arxiv.org/abs/quant-ph/0405098) 式 (1) 与 Claim 3.3 是电路历史态和传播零能量项；Kenyon 的 [arXiv:1001.4028](https://arxiv.org/abs/1001.4028) §§3.1–3.3 直接给出图上的酉连接与向量丛 Laplacian 框架；Page–Wootters 的 [Phys. Rev. D 27, 2885](https://doi.org/10.1103/PhysRevD.27.2885) 支持条件内部钟的关系式；Davies–Lewis 的 [Communications in Mathematical Physics 17 (1970), 239–260](https://doi.org/10.1007/BF01647093) 与 Ozawa 的 [quant-ph/0107090v1](https://arxiv.org/abs/quant-ph/0107090) 支持 instrument 的结果分支和后继状态；Giovannetti、Lloyd、Maccone 的 [arXiv:1504.04215v2](https://arxiv.org/abs/1504.04215) 支持测量记忆的条件化讨论。它们各自只支持所列构造的相应部分。

## 追加锚（本行以下为增补区）

## 389. 完整量子记录与有成功标志的精确恢复

**定义 389.1（记录耦合与行坐标约定）。** 设系统空间为 $S=\mathbb C^d$，$d\ge1$，固定正交基 $\{|i\rangle\}_{i=1}^d$。记录向量 $r_1,\ldots,r_d$ 均归一化，其张成空间为 $E=\mathbb C^r$。在固定记录基中，将 ket 的坐标写成矩阵的行：

$$
R_{i\alpha}=(r_i)_\alpha,\qquad
C=RR^\dagger,\qquad
C_{ij}=\sum_\alpha(r_i)_\alpha\overline{(r_j)_\alpha}
       =\langle r_j|r_i\rangle.
$$

因而 $R$ 满列秩，$C\succeq0$ 且 $C_{ii}=1$；称这样的 $C$ 为复相关矩阵。记 $A\circ X$ 为逐项乘积。记录等距映射为

$$
J|i\rangle=|i\rangle\otimes|r_i\rangle.
$$

本定义承接第 222 节的记录重叠通道，并保留第 88 节关于未撤销记录的限制。作为后续推导的基础，直接在矩阵单位上计算得

$$
J^\dagger J=I_S,\qquad
\operatorname{Tr}_E(JXJ^\dagger)=C\circ X.
$$

第一式因为不同 $i$ 的系统因子正交且 $\|r_i\|=1$；第二式因为 $|i\rangle\langle j|$ 对应的记录项 $|r_i\rangle\langle r_j|$ 的迹为 $C_{ij}$。任取单位空白向量 $|b\rangle\in E$，两个正交族 $\{|i\rangle|b\rangle\}$ 与 $\{|i\rangle|r_i\rangle\}$ 都能补成 $S\otimes E$ 的正交基，按基映射便得到酉算子 $V$，满足

$$
V(|\psi\rangle\otimes|b\rangle)=J|\psi\rangle,\qquad
V^\dagger J|\psi\rangle=|\psi\rangle\otimes|b\rangle.
$$

这只给出完整联合控制下的逆转。下述恢复接口不包含再次施加这个联合酉算子的权限。

**定义 389.2（允许的测量、反馈与总成功概率）。** 允许对完整记录空间 $E$ 作任意有限 POVM $\{D_y\}_{y\in Y}$，其中 $D_y\succeq0$、$\sum_yD_y=I_E$；将结果 $y$ 作为经典信息，随后只对 $S$ 施加酉算子 $U_y$。可选定成功集合 $Y_{\mathrm{s}}\subseteq Y$。不允许额外的系统—记录相干操作，不存在另一个被默默丢弃的不可访问记录。

记未归一化系统分支为 $\mathcal M_y$，校正分支为 $\mathcal T_y(X)=U_y\mathcal M_y(X)U_y^\dagger$。总成功概率 $t$ 的精确恢复要求是线性映射等式

$$
\sum_{y\in Y_{\mathrm{s}}}\mathcal T_y=t\,\operatorname{id}_S,
\qquad 0\le t\le1.
$$

它要求对全部未知输入以同一概率成功。特别地，对任意有限参考空间 $A$ 及任意联合密度矩阵 $\rho_{AS}$，成功后的未归一化态必须等于 $t\rho_{AS}$：

$$
\left(\operatorname{id}_A\otimes
\sum_{y\in Y_{\mathrm{s}}}\mathcal T_y\right)(\rho_{AS})=t\rho_{AS}.
$$

参考系统不被测量或反馈；成功概率由上式取迹给出。不同成功标签可以对应不同的反馈，不要求它们合并成一个指定的 POVM 结果。

此处采用的环境辅助校正框架见 Gregoratti–Werner，[*Quantum Lost and Found*, quant-ph/0209025v1](https://arxiv.org/abs/quant-ph/0209025v1)：Theorem 1（PDF 第 4 页）给出纯初始环境下 CP 分解的环境测量实现；Proposition 2（PDF 第 4–5 页）给出完美校正的 Kraus 条件，同维情形对应酉混合。下面将这些前提用于总成功权重，并在固定行坐标约定下写出所需实现与必要性论证。

## 390. 总成功权重的相位锥表示与最优值取得

**定义 390.1（相位锥与恢复量）。** 定义相位向量集合、相位凸包及其锥为

$$
\mathbb T^d=\{z\in\mathbb C^d:|z_i|=1\ (1\le i\le d)\},\qquad
\mathcal P_d=\operatorname{conv}\{zz^\dagger:z\in\mathbb T^d\},
$$

$$
\mathcal K_d=\left\{\sum_{y=1}^{m}p_yz_yz_y^\dagger:
 m<\infty,\ p_y\ge0,\ z_y\in\mathbb T^d\right\}.
$$

容许空和。对相关矩阵 $C$，在下式中始终要求 $m$ 为非负整数、$p_y\ge0$ 且 $z_y\in\mathbb T^d$，定义

$$
\eta(C)=\sup\left\{\sum_{y=1}^{m}p_y:
 Q=\sum_{y=1}^{m}p_yz_yz_y^\dagger\preceq C\right\}.
$$

每个这样的 $Q$ 都有 $Q_{ii}=\sum_yp_y$；权重由 $Q$ 唯一决定，亦等于 $\operatorname{Tr}(Q)/d$。

**定理 390.2（有限测量下的总精确恢复边界）。** 在定义 389.1–389.2 的完整记录接口下，$\eta(C)$ 恰为所有有限协议的最大总成功概率，而且最大值可以取得。取得最大值的协议可用至多 $d^2-d+1$ 个非零成功结果及一个失败结果。特别地，

$$
\eta(C)=1\quad\Longleftrightarrow\quad C\in\mathcal P_d.
$$

最后这个确定恢复判据是环境辅助酉混合判据在 Schur 通道上的应用；它在本定理中作为总成功边界的端点，出处为定义 389.2 所引 Gregoratti–Werner，以及 Buscemi–Chiribella–D’Ariano，[*Inverting Quantum Decoherence by Classical Feedback from the Environment*, quant-ph/0504195v5](https://arxiv.org/abs/quant-ph/0504195v5)，Theorem 1 后的环境反馈讨论与 Theorem 2（PDF 第 2 页；[Phys. Rev. Lett. 95, 090501](https://doi.org/10.1103/PhysRevLett.95.090501)）。

证明。先建立 POVM 与正矩阵分解之间的精确对应。若记录测量结果 $y$ 的 Kraus 算子为 $M_{yk}$，则 $D_y=\sum_kM_{yk}^\dagger M_{yk}$。对系统矩阵单位，记录的偏迹系数为

$$
\sum_k\operatorname{Tr}(M_{yk}|r_i\rangle\langle r_j|M_{yk}^\dagger)
 =\langle r_j|D_y|r_i\rangle
 =(RD_y^{\mathsf T}R^\dagger)_{ij}.
$$

这里 $\mathsf T$ 是普通转置，不能用伴随替换。因此

$$
\mathcal M_y(X)=C_y\circ X,\qquad
C_y=RD_y^{\mathsf T}R^\dagger\succeq0,\qquad
\sum_yC_y=C.
$$

转置保持 Hermitian 正半定性：对 $D\succeq0$，$x^\dagger D^{\mathsf T}x=\overline{\bar x^\dagger D\bar x}\ge0$。上述分支公式与选择哪一组实现同一效果的 Kraus 算子无关。

反之，设有限正矩阵族满足 $\sum_yC_y=C$。由 $0\preceq C_y\preceq C$，若 $v\in\ker C$，则 $0\le v^\dagger C_yv\le v^\dagger Cv=0$，故 $C_yv=0$。于是 $\operatorname{ran}C_y\subseteq\operatorname{ran}C=\operatorname{ran}R$。定义满列秩矩阵的左伪逆及辅助效果

$$
R^+=(R^\dagger R)^{-1}R^\dagger,\qquad
T_y=R^+C_y(R^+)^\dagger,\qquad D_y=T_y^{\mathsf T}.
$$

有 $T_y\succeq0$，且

$$
\sum_yT_y=R^+RR^\dagger(R^+)^\dagger=I_E.
$$

又 $P=RR^+$ 是 $\operatorname{ran}R$ 上的正交投影，故

$$
RD_y^{\mathsf T}R^\dagger=RT_yR^\dagger=PC_yP=C_y.
$$

这给出所需 POVM。取每个结果的 Kraus 算子为 $D_y^{1/2}$ 即可实现它；若原环境比最小记录张成空间更大，将其正交补并入任一结果，不改变任何输入分支。

接着证明成功分支必须具有相位秩一形式。设某协议的成功和为 $t\operatorname{id}_S$。取未归一化最大纠缠向量 $|\Omega\rangle=\sum_i|i\rangle\otimes|i\rangle$，记 Choi 矩阵

$$
\mathfrak J(\mathcal T)=
(\operatorname{id}_S\otimes\mathcal T)(|\Omega\rangle\langle\Omega|).
$$

每个 $\mathfrak J(\mathcal T_y)$ 正半定，并且

$$
\sum_{y\in Y_{\mathrm{s}}}\mathfrak J(\mathcal T_y)
=t|\Omega\rangle\langle\Omega|.
$$

对任意与 $\Omega$ 正交的向量，左侧各项的非负二次型之和为零，故各项都将该向量送至零。每项的值域因此包含于 $\mathbb C\Omega$，从而存在 $p_y\ge0$ 使 $\mathfrak J(\mathcal T_y)=p_y|\Omega\rangle\langle\Omega|$。Choi 矩阵的 $(i,j)$ 块就是 $\mathcal T_y(|i\rangle\langle j|)$，所以

$$
\mathcal T_y=p_y\operatorname{id}_S,\qquad
\sum_{y\in Y_{\mathrm{s}}}p_y=t.
$$

这一步排除了“若干不可校正分支在成功和中互相抵消”的可能。

对于 $p_y>0$，在 $|i\rangle\langle i|$ 上应用此等式得到

$$
(C_y)_{ii}U_y|i\rangle\langle i|U_y^\dagger
=p_y|i\rangle\langle i|.
$$

取迹得 $(C_y)_{ii}=p_y$，所以 $U_y|i\rangle=u_{yi}|i\rangle$，其中 $|u_{yi}|=1$。再比较任意 $(i,j)$ 矩阵单位，得到

$$
(C_y)_{ij}u_{yi}\overline{u_{yj}}=p_y.
$$

令 $(z_y)_i=\overline{u_{yi}}$，便有 $C_y=p_yz_yz_y^\dagger$。若 $p_y=0$，则 $\mathcal T_y=0$，由酉反馈可逆知 $C_y=0$。因此任意协议给出 $Q=\sum_{y\in Y_{\mathrm{s}}}p_yz_yz_y^\dagger\preceq C$，其总成功率不超过定义 390.1 的上确界。

反向构造也成立：给定可行 $Q$，以各 $p_yz_yz_y^\dagger$ 为成功分支矩阵，以 $C-Q$ 为失败分支矩阵，用前述 POVM 实现，并对成功结果取

$$
U_y=\operatorname{diag}(\overline{(z_y)_1},\ldots,\overline{(z_y)_d}).
$$

逐项相乘直接给出 $\mathcal T_y=p_y\operatorname{id}_S$。对参考空间张量恒等映射后仍成立，故恢复包括未知输入的纠缠。

最后证明上确界确实取得。由 $Q_{ii}\le C_{ii}=1$，可行权重在 $[0,1]$ 内。Hermitian 矩阵的实维数为 $d^2$，固定全部对角元为 $1$ 的仿射空间维数为 $d^2-d$。相位向量集合紧致，映射 $z\mapsto zz^\dagger$ 连续；Carathéodory 定理将其凸包中的每一点写成至多 $d^2-d+1$ 点的凸组合。因此 $\mathcal P_d$ 是紧集：它是有限个紧相位集合与紧权重单纯形的连续像。集合

$$
\{(t,H):t\in[0,1],\ H\in\mathcal P_d,\ C-tH\succeq0\}
$$

非空且闭，因而紧。连续目标 $t$ 在其上取得最大值；$t=0$ 时任选 $H$，而 $t>0$ 时 $Q=tH$。Carathéodory 分解及一个剩余失败分支即给出所述有限结果数界。

若 $C\in\mathcal P_d$，取 $Q=C$ 得 $\eta(C)=1$。反之，由取得性，$\eta(C)=1$ 给出 $Q\preceq C$ 且 $\operatorname{Tr}(C-Q)=0$。正半定矩阵的本征值均非负，迹为零迫使矩阵为零，所以 $C=Q\in\mathcal P_d$。证毕。

## 391. 单个成功结果的界与总成功的支撑判据

**定理 391.1（伪逆界及正成功的充要条件）。** 在定义 389.2 的接口中，指定一个非零成功结果、相位向量 $z\in\mathbb T^d$ 和输入无关概率 $p>0$。该结果可实现精确恢复，当且仅当

$$
pzz^\dagger\preceq C.
$$

记 $C^+$ 为 Moore–Penrose 伪逆。上述条件进一步等价于

$$
z\in\operatorname{ran}C,\qquad
0<p\le\frac1{z^\dagger C^+z}.
$$

于是总成功量具有支撑判据

$$
\eta(C)>0\quad\Longleftrightarrow\quad
\operatorname{ran}C\cap\mathbb T^d\ne\varnothing.
$$

证明。定理 390.2 的成功分支论证给出必要形式 $pzz^\dagger$；若它被 $C$ 支配，将剩余矩阵作为失败分支即可实现，故第一个等价成立。

若 $pzz^\dagger\preceq C$，对 $v\in\ker C$ 取二次型得 $p|z^\dagger v|^2\le0$。因此 $z$ 正交于 $\ker C$，即 $z\in\operatorname{ran}C$。在 $H_C=\operatorname{ran}C$ 上，$C$ 严格正定；令 $v=C^{-1/2}z$，这里的逆平方根仅在 $H_C$ 上定义。对不等式作可逆合同变换，得到

$$
pvv^\dagger\preceq I_{H_C}.
$$

对任意 $x\in H_C$，Cauchy–Schwarz 不等式给出 $p|v^\dagger x|^2\le p\|v\|^2\|x\|^2$；取 $x=v$ 又给出必要条件。因此该算子不等式恰在 $p\|v\|^2\le1$ 时成立。由于 $z\ne0$，

$$
\|v\|^2=z^\dagger C^+z>0,
$$

从而得到伪逆界。反向合同变换，并在 $\ker C$ 上补零，证明其充分性。

若 $\eta(C)>0$，定理 390.2 的有限取得性给出某个 $p_y>0$，且 $p_yz_yz_y^\dagger\preceq Q\preceq C$，所以相应 $z_y$ 位于 $\operatorname{ran}C$。反之，支撑中的任意相位向量都由伪逆界给出一个正成功概率，故 $\eta(C)>0$。证毕。

本定理中的倒数控制一个指定成功结果，不能把它直接当作 $\eta(C)$。例如 $C=I_d$ 时每个相位向量满足 $z^\dagger C^+z=d$，一个结果至多以 $1/d$ 成功；第 394 节的有限 Fourier 分解使所有成功结果的概率之和达到 $1$。

## 392. 四路径记录的支撑障碍与显式分离见证

**定义 392.1（四路径相关矩阵与见证）。** 取

$$
R_0=\begin{pmatrix}
1&0\\
0&1\\
1/\sqrt2&1/\sqrt2\\
1/\sqrt2&i/\sqrt2
\end{pmatrix},\qquad C_0=R_0R_0^\dagger,
$$

$$
B=\begin{pmatrix}
-1/\sqrt2&-1/\sqrt2&1&0\\
-1/\sqrt2&-i/\sqrt2&0&1
\end{pmatrix},\qquad
W=B^\dagger B,\qquad \nu=3-2\sqrt2.
$$

$C_0$ 是已知的四维、秩二记录例子：Buscemi–Chiribella–D’Ariano 的 [quant-ph/0504195v5](https://arxiv.org/abs/quant-ph/0504195v5)，式 (9)（PDF 第 3 页）给出了对应相关矩阵。其 Heisenberg 通道约定与这里的 Schrödinger 约定相对偶；按定义 389.1 的 ket 行坐标，使用该矩阵的逐项复共轭。本节用这个已知例子承载总成功权重的支撑障碍与定量见证。

**定理 392.2（零成功支撑及锐相位下界）。** 定义 392.1 的矩阵满足

$$
\operatorname{ran}C_0\cap\mathbb T^4=\varnothing,\qquad
\eta(C_0)=0,
$$

$$
W\succeq0,\qquad WC_0=0,\qquad
\operatorname{Tr}W=4,\qquad
\min_{z\in\mathbb T^4}z^\dagger Wz=\nu.
$$

对任意四维相关矩阵 $C$，由此得到统一上界

$$
\eta(C)\le\min\left\{1,\frac{\operatorname{Tr}(WC)}{\nu}\right\}.
$$

证明。由于 $R_0$ 满列秩，$\operatorname{ran}C_0=\operatorname{ran}R_0$，其中每个向量形如

$$
\left(a,b,\frac{a+b}{\sqrt2},\frac{a+ib}{\sqrt2}\right)^{\mathsf T}.
$$

若它属于 $\mathbb T^4$，前两个分量给出 $|a|=|b|=1$，第三个分量给出 $\operatorname{Re}(a\bar b)=0$，第四个给出 $\operatorname{Im}(a\bar b)=0$。这与 $|a\bar b|=1$ 矛盾，故相交为空；定理 391.1 随即给出 $\eta(C_0)=0$。这里排除的恢复仅限于定义 389.2 的测量与酉反馈接口。

由 $W=B^\dagger B$ 有 $W\succeq0$。逐行相乘得 $BR_0=0$，所以 $WC_0=B^\dagger BR_0R_0^\dagger=0$。$B$ 的每行平方范数为 $2$，故 $\operatorname{Tr}W=\sum_{k,i}|B_{ki}|^2=4$。

现在计算相位向量上的确切最小值。对 $z\in\mathbb T^4$，置

$$
A=\frac{z_1+z_2}{\sqrt2},\qquad
D=\frac{z_1+iz_2}{\sqrt2},\qquad u=|A|,\quad v=|D|.
$$

因为 $|z_1\bar z_2|=1$，

$$
u^2-1=\operatorname{Re}(z_1\bar z_2),\qquad
v^2-1=\operatorname{Im}(z_1\bar z_2),\qquad
(u^2-1)^2+(v^2-1)^2=1,
$$

且 $0\le u,v\le\sqrt2$。由反三角不等式，

$$
\begin{aligned}
z^\dagger Wz
 &=|z_3-A|^2+|z_4-D|^2\\
 &\ge(u-1)^2+(v-1)^2\\
 &=\frac{(u^2-1)^2}{(u+1)^2}
   +\frac{(v^2-1)^2}{(v+1)^2}\\
 &\ge\frac{(u^2-1)^2+(v^2-1)^2}{(1+\sqrt2)^2}
 =3-2\sqrt2=\nu.
\end{aligned}
$$

这里第一行的 $z_3,z_4$ 仍是原相位向量的分量，没有将它们独立最优化后冒充共同实现。取同一个相位向量

$$
z_*=(1,1,1,(1+i)/\sqrt2)^{\mathsf T},
$$

则 $A=\sqrt2$、$D=(1+i)/\sqrt2$，上式的平方和等于 $(\sqrt2-1)^2=\nu$，所以该下界确实达到。

最后，对任意可行成功矩阵 $Q=\sum_yp_yz_yz_y^\dagger\preceq C$，令 $t=\sum_yp_y$。有

$$
\nu t\le\sum_yp_yz_y^\dagger Wz_y
=\operatorname{Tr}(WQ)\le\operatorname{Tr}(WC).
$$

最后一个不等式成立，因为
$\operatorname{Tr}(W(C-Q))=\operatorname{Tr}(W^{1/2}(C-Q)W^{1/2})\ge0$。
对所有协议取最大值并结合 $\eta(C)\le1$，得到结论。证毕。

## 393. 从零成功端点到正概率而非确定恢复

**定理 393.1（记录耦合扰动下的总成功区间）。** 对 $0\le\varepsilon\le1$，定义

$$
C_\varepsilon=(1-\varepsilon)C_0+\varepsilon I_4.
$$

在定义 389.2 的完整记录接口下，

$$
\boxed{\quad
\varepsilon\le\eta(C_\varepsilon)
\le\min\left\{1,\frac{4\varepsilon}{3-2\sqrt2}\right\}.
\quad}
$$

因此 $\eta(C_0)=0$、$\eta(C_1)=1$，而

$$
0<\varepsilon<\frac{3-2\sqrt2}{4}
\quad\Longrightarrow\quad
0<\eta(C_\varepsilon)<1.
$$

这些严格不等式刻画一个可有成功标志、却不能确定精确恢复的区间；本界不决定 $\eta(C_\varepsilon)$ 的确切最优值，也不决定确定恢复出现的锐阈值。

证明。令 $\zeta=e^{2\pi i/4}$，对 $k=0,1,2,3$ 定义相位向量

$$
(z^{(k)})_j=\zeta^{(j-1)k},\qquad j=1,2,3,4.
$$

有限几何级数给出

$$
\frac14\sum_{k=0}^3z^{(k)}z^{(k)\dagger}=I_4:
$$

对角元是 $1$；若 $i\ne j$，比值 $\zeta^{i-j}\ne1$，四项和为零。因此

$$
Q=\frac\varepsilon4\sum_{k=0}^3z^{(k)}z^{(k)\dagger}
 =\varepsilon I_4\preceq C_\varepsilon,
$$

其剩余矩阵为 $(1-\varepsilon)C_0\succeq0$。定理 390.2 将四个成功分支各自实现为概率 $\varepsilon/4$ 的精确校正，给出总概率下界 $\varepsilon$。

另一方面，定理 392.2 给出

$$
\operatorname{Tr}(WC_\varepsilon)
 =(1-\varepsilon)\operatorname{Tr}(WC_0)
   +\varepsilon\operatorname{Tr}W=4\varepsilon,
$$

从而得到上界。$\varepsilon=0$ 时上界为零，$\varepsilon=1$ 时下界为一；在所示开区间中下界严格为正而上界严格小于一。证毕。

**定义 393.2（扰动族所改变的记录权限）。** 上述相关矩阵可由新的归一化纯记录实现：若 $r_i^{(0)}$ 是 $R_0$ 的 ket 行向量，取

$$
r_i^{(\varepsilon)}
 =\sqrt{1-\varepsilon}\,r_i^{(0)}
   \oplus\sqrt\varepsilon\,|i\rangle
 \in\mathbb C^2\oplus\mathbb C^4.
$$

两个直和分量的重叠相加，按定义 389.1 的约定恰给出 $C_\varepsilon$。定理 393.1 假设可以测量这些向量张成的完整量子记录，包含两个直和分量之间的相干；端点处可压缩到各自的最小张成空间。此族改变了记录耦合和可访问环境，不能解释为在同一不可访问环境中免费丢失信息所带来的改进。每个 $\varepsilon$ 的记录等距映射仍可按定义 389.1 补成联合酉映射，因此完整联合相干逆转始终可行；测量加经典酉反馈的总成功率则受定理 393.1 的界约束。

## 394. 完整记录访问、残留记录与后续数学边界

**推论 394.1（Fourier 恢复及不可访问副本的分界）。** 若归一化记录相互正交，且可以访问完整量子记录，则 $C=I_d$，可由有限记录测量与酉反馈实现 $\eta(I_d)=1$；但一个指定成功结果的概率至多为 $1/d$。

另设 $d\ge2$，实际耦合还保留一组不可访问的正交记录 $f_i\in F$：

$$
J_F|i\rangle=|i\rangle\otimes|r_i\rangle_E\otimes|f_i\rangle_F,
\qquad \langle f_j|f_i\rangle=\delta_{ij}.
$$

只测量 $E$ 并按结果对 $S$ 作酉反馈时，对全部未知输入的总精确成功概率只能为零。这不与上一段相矛盾，因为其完整记录访问前提已经改变。

证明。在正交记录基中，取 $k=0,\ldots,d-1$ 及

$$
(z^{(k)})_j=e^{2\pi i(j-1)k/d},\qquad
|m_k\rangle=\frac1{\sqrt d}\sum_{j=1}^d
 \overline{(z^{(k)})_j}|r_j\rangle.
$$

几何级数说明 $m_k$ 构成记录空间的正交基，且
$\langle m_k|r_j\rangle=(z^{(k)})_j/\sqrt d$。记录投影测量 $|m_k\rangle\langle m_k|$ 的系统分支因此为

$$
\mathcal M_k(X)=\frac1d
\operatorname{diag}(z^{(k)})X\operatorname{diag}(z^{(k)})^\dagger.
$$

以 $\operatorname{diag}(\overline{z^{(k)}})$ 反馈，得到 $\mathcal T_k=\operatorname{id}_S/d$；将 $d$ 个结果都列为成功，便得总概率 $1$。一个指定结果的界则由定理 391.1 的 $z^\dagger I_dz=d$ 给出。$d=1$ 时同一构造只有一个结果。

对于不可访问副本，任意 $E$ 上效果 $D_y$ 给出的系统分支系数变为

$$
\langle r_j|D_y|r_i\rangle\langle f_j|f_i\rangle
=\delta_{ij}\langle r_i|D_y|r_i\rangle.
$$

故每个分支、每次酉反馈及任意成功分支之和都只依赖输入的对角元。取不同系统基向量 $|i\rangle,|j\rangle$，令

$$
|\psi_\pm\rangle=(|i\rangle\pm|j\rangle)/\sqrt2,\qquad
\rho_\pm=|\psi_\pm\rangle\langle\psi_\pm|.
$$

$\rho_+$ 与 $\rho_-$ 的对角元相同但矩阵不同，故任何允许协议的成功输出对两者相同。若该输出同时为 $t\rho_+$ 与 $t\rho_-$，便有 $t(\rho_+-\rho_-)=0$，迫使 $t=0$。证毕。

该推论与第 88 节的残留记录重叠边界相接：完整访问正交记录时能确定恢复，而定义 392.1 的非正交四路径记录在较窄的测量—酉反馈接口中连正的总精确成功率也没有。决定这一区别的是共同 Gram 支撑和允许的操作，不能单凭“记录越可区分”就给可恢复性排序。联合可逆、一个指定成功结果可逆、全部成功结果的总概率，以及完整记录的可访问性，分别承担不同的数学条件。

**问题 394.2（精确最优值与近似恢复）。** 定理 393.1 留下的精确问题是求出整个 $[0,1]$ 上的 $\eta(C_\varepsilon)$，特别是 $\varepsilon\downarrow0$ 的锐渐近及集合 $\{\varepsilon:\eta(C_\varepsilon)=1\}$。现有上下界没有给出这些答案。

另一问题是在定义 389.2 的同一接口下，将成功映射 $\mathcal T_{\mathrm{s}}$ 的条件改成

$$
\operatorname{Tr}\mathcal T_{\mathrm{s}}(\rho)=t
\quad\text{对所有密度矩阵 }\rho,
\qquad
\|\mathcal T_{\mathrm{s}}-t\operatorname{id}_S\|_\diamond\le t\delta,
\qquad t>0,
$$

其中 $\delta\ge0$，菱形范数通过对参考系统张量恒等映射后取诱导迹范数定义。求在该输入无关、容许参考纠缠的误差合同下可达的 $t$ 与 $\delta$ 关系；$\delta=0$ 返回本批的精确恢复问题，$\delta>0$ 的最优界不由秩一 Choi 的精确论证自动推出。

## 追加锚（本行以下为增补区）

## 395. 单份记录的近似恢复合同与成功 Choi 检验

本节至第 398 节承接问题 394.2：保持完整纯量子记录、有限记录测量、经典结果及系统酉反馈的接口，研究允许误差时的总成功概率。目标仍是恢复单份系统的全部未知输入，包括它与任意参考系统的纠缠；系统在记录测量后仍可用于反馈。以下给出必要误差界与可实现的成功率下界，不把二者之间的区间视为已求出的最优边界。

**定义 395.1（输入无关的成功与未折半误差）。** 沿用定义 389.1–389.2 的 $S=\mathbb C^d$、$d\ge1$、相关矩阵 $C\succeq0$、$C_{ii}=1$、有限 POVM $\{D_y\}$、酉反馈 $U_y$ 和成功集合 $Y_{\mathrm s}$。令

$$
\mathcal T_{\mathrm s}(X)
 =\sum_{y\in Y_{\mathrm s}}U_y(C_y\circ X)U_y^\dagger,
\qquad C_y=RD_y^{\mathsf T}R^\dagger.
$$

将精确恢复要求改为

$$
\mathcal T_{\mathrm s}^{*}(I_S)=tI_S,
\qquad 0<t\le1,
\qquad
\|\mathcal T_{\mathrm s}-t\operatorname{id}_S\|_\diamond\le t\delta,
\qquad 0\le\delta\le2,
$$

其中 $\mathcal T_{\mathrm s}^{*}$ 是迹配对下的伴随。第一式等价于对每个密度矩阵 $\rho$ 都有 $\operatorname{Tr}\mathcal T_{\mathrm s}(\rho)=t$，故接受后的映射

$$
\widehat{\mathcal T}_{\mathrm s}=\mathcal T_{\mathrm s}/t
$$

是完全正、保迹的线性通道。这里的 diamond 范数不乘 $1/2$；明确地，对线性映射 $\Phi$，

$$
\|\Phi\|_\diamond
 =\sup_{k\ge1}\ \sup_{X\ne0}
 \frac{\|(\operatorname{id}_{\mathbb C^k}\otimes\Phi)(X)\|_1}{\|X\|_1},
\qquad \|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}.
$$

于是合同等价于 $\|\widehat{\mathcal T}_{\mathrm s}-\operatorname{id}_S\|_\diamond\le\delta$。特别地，对任意有限参考空间 $A$ 和任意联合密度矩阵 $\rho_{AS}$，成功概率为 $t$，且

$$
\left\|(\operatorname{id}_A\otimes\widehat{\mathcal T}_{\mathrm s})(\rho_{AS})
       -\rho_{AS}\right\|_1\le\delta.
$$

参考系统不被操作；成功后的经典标签可用于选择 $U_y$，最终比较的是对所有成功标签求和后的系统通道。这里不要求各成功标签分别具有输入无关的概率，也不将反馈扩大为任意系统通道。$\delta=0$ 恢复定义 389.2 的精确合同。$t=0$ 时没有接受后的归一化通道。

**命题 395.2（保留反馈的有限细分与必要保真度界）。** 对定义 395.1 的任意协议，可以将成功分支有限细分为向量 $v_j\in\mathbb C^d$，并对每个细分项保留原结果的同一个酉算子 $U_j$，使

$$
\begin{aligned}
\mathcal T_{\mathrm s}(X)
 &=\sum_j U_jD(v_j)XD(v_j)^\dagger U_j^\dagger,
 &D(v)&=\operatorname{diag}(v_1,\ldots,v_d),\\
M&=\sum_jv_jv_j^\dagger\preceq C,
 &\operatorname{diag}M&=t\mathbf1,\qquad
 \operatorname{Tr}M=\sum_j\|v_j\|_2^2=dt.
\end{aligned}
$$

本节使用归一化最大纠缠向量和投影

$$
|\omega_d\rangle=\frac1{\sqrt d}\sum_{i=1}^d|i\rangle\otimes|i\rangle,
\qquad \Pi_d=|\omega_d\rangle\langle\omega_d|.
$$

它与定理 390.2 中未归一化的 $|\Omega\rangle$ 满足 $|\omega_d\rangle=|\Omega\rangle/\sqrt d$，不可混用两种 Choi 迹约定。令

$$
\begin{aligned}
J_{\mathrm s}&=(\operatorname{id}_S\otimes\mathcal T_{\mathrm s})(\Pi_d),
 &\operatorname{Tr}J_{\mathrm s}&=t,\\
f_{\mathrm{actual}}&=\langle\omega_d|J_{\mathrm s}|\omega_d\rangle
 =\frac1{d^2}\sum_j|\operatorname{Tr}(U_jD(v_j))|^2,
 &f_\star&=\frac1{d^2}\sum_j\|v_j\|_1^2,
\end{aligned}
$$

其中向量的 $\|v\|_1=\sum_i|v_i|$。则

$$
0\le f_{\mathrm{actual}}\le f_\star\le t,
\qquad
\|\mathcal T_{\mathrm s}-t\operatorname{id}_S\|_\diamond
 \ge2(t-f_{\mathrm{actual}}),
$$

从而任何满足误差合同的协议都必须满足

$$
f_\star\ge f_{\mathrm{actual}}\ge t(1-\delta/2).
$$

证明。由第 390 节的分支对应，$C_y\succeq0$ 且 $\sum_yC_y=C$。分别对每个成功 $C_y$ 作有限谱分解
$C_y=\sum_kv_{yk}v_{yk}^\dagger$，将 $(y,k)$ 简记为 $j$，置 $U_j=U_y$。恒等式
$(vv^\dagger)\circ X=D(v)XD(v)^\dagger$
说明细分没有改变 $\mathcal T_{\mathrm s}$。若将这些标签实现为更细 POVM，第 390 节的正矩阵分解实现仍适用；使用原 $U_y$ 就还原同一个成功映射。因此证明既未假定原分支秩一，也未在细分时替换实际反馈。

由 $\sum_jv_jv_j^\dagger=\sum_{y\in Y_{\mathrm s}}C_y$ 得 $M\preceq C$。又

$$
\mathcal T_{\mathrm s}^{*}(I_S)
 =\sum_jD(v_j)^\dagger U_j^\dagger U_jD(v_j)
 =\operatorname{diag}\left(\sum_j|(v_j)_i|^2\right)_{i=1}^d.
$$

与 $tI_S$ 比较便得到 $\operatorname{diag}M=t\mathbf1$，取迹即得总能量 $dt$。归一化 Choi 矩阵的迹因此是 $t$；恒等式
$\langle\omega_d|(I\otimes K)|\omega_d\rangle=\operatorname{Tr}K/d$
给出 $f_{\mathrm{actual}}$ 的公式。对每个酉矩阵，$|(U_j)_{ii}|\le1$，故

$$
|\operatorname{Tr}(U_jD(v_j))|
 \le\sum_i|(v_j)_i|=\|v_j\|_1,
\qquad \|v_j\|_1^2\le d\|v_j\|_2^2.
$$

求和并除以 $d^2$，得到 $f_{\mathrm{actual}}\le f_\star\le t$。这里使用的是已知的固定 Kraus 分解恢复保真度成分：Gregoratti–Werner，[*Quantum Lost and Found*, quant-ph/0209025v1](https://arxiv.org/abs/quant-ph/0209025v1)，Proposition 8（PDF 第 11–12 页，式 (15)–(21)）给出以 $d^{-2}\sum_j(\operatorname{Tr}|K_j|)^2$ 控制最优纠缠保真度的结果。本文所需的对角 Kraus、酉反馈情形已由上面的逐项估计直接证明；$f_\star$ 在这里是给定细分的上界，并不宣称原协议在 diamond 范数下最优。

最后，以 $\Pi_d$ 作为 diamond 范数的一个合法输入，有

$$
\|\mathcal T_{\mathrm s}-t\operatorname{id}_S\|_\diamond
 \ge\|J_{\mathrm s}-t\Pi_d\|_1.
$$

对 Hermitian 矩阵 $H=J_{\mathrm s}-t\Pi_d$，二结果检验 $\{\Pi_d,I-\Pi_d\}$ 给出的两个有符号读数为 $f_{\mathrm{actual}}-t$ 和 $t-f_{\mathrm{actual}}$。谱分解给出 $|\operatorname{Tr}(FH)|\le\operatorname{Tr}(F|H|)$（$0\preceq F\preceq I$），对这两个效果相加便得

$$
\|H\|_1\ge|f_{\mathrm{actual}}-t|+|t-f_{\mathrm{actual}}|
 =2(t-f_{\mathrm{actual}}).
$$

结合误差合同并除以正数 $t$ 即得结论。证毕。

该二结果计算给出必要下界。即使这个检验读数很小，也不能据此认定任意参考输入的误差都小；以下推导始终只沿上述必要性方向使用它。

## 396. 支撑与相位环面的正距离不能靠稀有成功消除

**定义 396.1（相位支撑间隙）。** 对相关矩阵 $C$，令 $H_C=\operatorname{ran}C$，$P_C$ 为到 $H_C$ 的正交投影，$Q_C=I-P_C$。以定义 390.1 的相位向量集合 $\mathbb T^d$ 定义

$$
\mu(C)=\min_{z\in\mathbb T^d}\|Q_Cz\|_2^2.
$$

这里 $H_C$ 是成功 Kraus 向量所在的线性支撑，不是另行选择的待恢复编码子空间；恢复任务仍覆盖整个 $\mathbb C^d$。

**定理 396.2（所有正成功率共用的支撑误差下界）。** 上述最小值取得，$0\le\mu(C)\le d$，且

$$
\mu(C)>0
\quad\Longleftrightarrow\quad
H_C\cap\mathbb T^d=\varnothing
\quad\Longleftrightarrow\quad
\eta(C)=0.
$$

每个定义 395.1 的正成功协议满足

$$
f_{\mathrm{actual}}\le f_\star
 \le\left(1-\frac{\mu(C)}d\right)t,
\qquad
\delta\ge\frac{2\mu(C)}d.
$$

因此，存在一个对所有正成功率协议都成立的严格正误差下界，当且仅当 $\eta(C)=0$。这里没有断言 $2\mu(C)/d$ 就是可达到的最小 diamond 误差。

证明。$\mathbb T^d$ 是有限个单位圆的乘积，因而紧致；$z\mapsto\|Q_Cz\|_2^2$ 连续，故取得最小值。正交投影不增加范数，而 $\|z\|_2^2=d$，给出 $0\le\mu(C)\le d$。最小值为零恰好意味着某个相位向量满足 $Q_Cz=0$，也就是它属于 $H_C$。与定理 391.1 的支撑判据结合，得到所述等价。

命题 395.2 的每个细分项满足 $0\preceq v_jv_j^\dagger\preceq M\preceq C$。若 $x\in\ker C$，则

$$
0\le|v_j^\dagger x|^2\le x^\dagger Cx=0,
$$

故 $v_j\perp\ker C$，即 $v_j\in H_C$。对任意 $v\in H_C$，逐坐标选择与 $v_i$ 同相的 $z_i$（$v_i=0$ 时任取单位相位），并用三角不等式，得到

$$
\|v\|_1=\max_{z\in\mathbb T^d}|z^\dagger v|
 =\max_{z\in\mathbb T^d}|(P_Cz)^\dagger v|
 \le\sqrt{d-\mu(C)}\,\|v\|_2.
$$

最后一步使用 $\|P_Cz\|_2^2=d-\|Q_Cz\|_2^2\le d-\mu(C)$ 与 Cauchy–Schwarz。对所有 $v_j$ 平方求和，除以 $d^2$，再代入 $\sum_j\|v_j\|_2^2=dt$，便有
$f_\star\le(1-\mu(C)/d)t$。命题 395.2 给出
$t\delta\ge2(t-f_{\mathrm{actual}})\ge2t\mu(C)/d$；因 $t>0$，得到与 $t$ 无关的误差下界。

若 $\eta(C)>0$，定理 391.1 从支撑内的相位向量构造一个正成功概率的精确协议，其归一化误差为零，排除了对所有正成功协议统一成立的任何严格正下界。反方向已由 $\mu(C)>0$ 证明。证毕。

秩亏本身不是障碍。例如 $d\ge2$ 时，$C=\mathbf1\mathbf1^\dagger$ 的秩为 $1$，但 $\mathbf1\in H_C\cap\mathbb T^d$，且 $C\in\mathcal P_d$，由定理 390.2 得 $\eta(C)=1$。关键是支撑与相位环面的相对位置；把成功概率压低并不能让被 $C$ 支配的向量离开该支撑。

## 397. 辅助效果给出的成功率与误差必要关系

本节把零支撑质量的障碍推广到少量非零质量的情形。下文的效果 $E$ 是作用在坐标空间 $\mathbb C^d$ 上的数学算子；它不指第 389 节的记录空间，也不增加对系统或记录施加测量的权限。辅助标签空间同样只用于证明不等式。

**定理 397.1（效果界及其显式反演）。** 给定 $0\preceq E\preceq I_d$，定义

$$
a=\min_{z\in\mathbb T^d}\frac{z^\dagger Ez}{d},
\qquad 0\le a\le1,
\qquad
G_a(q)=\left(\sqrt{(1-a)(1-q)}+\sqrt{aq}\right)^2
\quad(0\le q\le a).
$$

对定义 395.1 的任意协议及命题 395.2 的任意上述细分，令

$$
x=\frac{\operatorname{Tr}(EC)}{dt},
\qquad q=\min\{a,x\}.
$$

则有必要条件

$$
\frac{f_{\mathrm{actual}}}{t}\le\frac{f_\star}{t}\le G_a(q),
\qquad
\boxed{\ \delta\ge2\bigl(1-G_a(q)\bigr).\ }
$$

若进一步 $0\le\delta<2a$，则

$$
r_a(\delta)=
 \left[\sqrt{a(1-\delta/2)}-\sqrt{(1-a)\delta/2}\right]^2>0,
\qquad
\boxed{\ t\le\frac{\operatorname{Tr}(EC)}{d\,r_a(\delta)}.\ }
$$

证明。相位集合紧致保证 $a$ 的最小值取得；$0\preceq E\preceq I_d$ 与 $\|z\|_2^2=d$ 给出 $a\in[0,1]$。令 $\ell_j=\|v_j\|_1$，取逐坐标匹配相位的 $z_j\in\mathbb T^d$，使 $z_j^\dagger v_j=\ell_j$。置

$$
N=\sum_j\ell_j^2=d^2f_\star,
\qquad c_j=\frac{\ell_j}{\sqrt N}.
$$

因为 $\|v_j\|_1\ge\|v_j\|_2$ 且 $\sum_j\|v_j\|_2^2=dt>0$，所以 $N\ge dt>0$，以上归一化合法。以正交标签 $|j\rangle$ 定义两个辅助单位向量

$$
|V\rangle=\frac1{\sqrt{dt}}\sum_j|j\rangle\otimes v_j,
\qquad
|Z\rangle=\frac1{\sqrt d}\sum_j c_j|j\rangle\otimes z_j.
$$

标签正交、$\sum_jc_j^2=1$ 及 $\|z_j\|_2^2=d$ 给出 $\|V\|_2=\|Z\|_2=1$，并且

$$
\langle Z|V\rangle
 =\frac{\sum_jc_j\ell_j}{d\sqrt t}
 =\frac{\sqrt N}{d\sqrt t}
 =\sqrt{f_\star/t}.
$$

令 $\widetilde E=I_{\mathrm{label}}\otimes E$，记

$$
\alpha=\langle Z|\widetilde E|Z\rangle
 =\sum_jc_j^2\frac{z_j^\dagger Ez_j}{d}\ge a,
\qquad
b=\langle V|\widetilde E|V\rangle
 =\frac{\operatorname{Tr}(EM)}{dt}\le x.
$$

其中 $\alpha,b\in[0,1]$；$x\ge0$，但 $x$ 不必小于 $1$，这正是定义 $q$ 时需要截断的原因。迹不等式来自
$\operatorname{Tr}(E(C-M))=\operatorname{Tr}(E^{1/2}(C-M)E^{1/2})\ge0$。

用 $\widetilde E+(I-\widetilde E)=I$ 分裂内积，再分别应用 Cauchy–Schwarz，得到

$$
\begin{aligned}
\sqrt{f_\star/t}
 &=|\langle Z|V\rangle|\\
 &\le\left|\langle\widetilde E^{1/2}Z|
                  \widetilde E^{1/2}V\rangle\right|
    +\left|\langle(I-\widetilde E)^{1/2}Z|
                  (I-\widetilde E)^{1/2}V\rangle\right|\\
 &\le\sqrt{\alpha b}+\sqrt{(1-\alpha)(1-b)}.
\end{aligned}
$$

所需的二元概率单调性可直接由角度看出。对 $u\in[0,1]$ 写 $\theta_u=\arcsin\sqrt u\in[0,\pi/2]$，则

$$
\sqrt{uv}+\sqrt{(1-u)(1-v)}=\cos(\theta_u-\theta_v).
$$

若 $b<a$ 且 $\alpha\ge a$，则
$0\le\theta_a-\theta_b\le\theta_\alpha-\theta_b\le\pi/2$，所以右端在 $\alpha=a$ 时最大。并且在 $0\le b\le a$ 内，$G_a(b)=\cos^2(\theta_a-\theta_b)$ 随 $b$ 单调增加。若 $x<a$，有 $b\le x<a$，故上面的内积界不超过 $\sqrt{G_a(x)}$。若 $x\ge a$，则 $q=a$、$G_a(q)=1$，而单位向量内积至多为 $1$，同样得到界；特别地，$b\ge a$ 必属于这一情形。于是
$f_\star/t\le G_a(q)$，再用命题 395.2 得到 $\delta\ge2(1-G_a(q))$。

为明确反演的方向，置 $h=\delta/2$、$A=\arcsin\sqrt a$、$B=\arcsin\sqrt q$。有 $0\le B\le A\le\pi/2$，而误差必要条件意味着

$$
\cos^2(A-B)\ge1-h,
\qquad
\sin^2(A-B)\le h.
$$

当 $0\le h<a$ 时，$H=\arcsin\sqrt h<A$。由于正弦在 $[0,\pi/2]$ 单调增加，上式等价于 $A-B\le H$，也就是 $B\ge A-H>0$。因此

$$
q\ge\sin^2(A-H)
 =\left[\sqrt{a(1-h)}-\sqrt{(1-a)h}\right]^2
 =r_a(\delta)>0.
$$

反向代入也给出相同的标量等价；没有在平方时遗失符号，因为 $A-H>0$。最后 $x\ge q\ge r_a(\delta)$，乘以 $dt$ 并除以正数 $d\,r_a(\delta)$ 就得到成功率上界。证毕。

端点由同一域约定处理：$a=0$ 时 $q=0$、$G_0(0)=1$，第一条界只是 $\delta\ge0$，而 $0\le\delta<2a$ 是空域；$a=1$ 时 $G_1(q)=q$，在 $0\le\delta<2$ 上 $r_1(\delta)=1-\delta/2>0$。对 $a>0$，$\delta=0$ 给出 $r_a(0)=a$ 与 $t\le\operatorname{Tr}(EC)/(da)$。若 $\operatorname{Tr}(EC)=0$，第一条界直接给出 $\delta\ge2a$，无需在禁止的域内除以零。

取 $E=Q_C$ 时，$a=\mu(C)/d$ 且 $\operatorname{Tr}(Q_CC)=0$，因而第 396 节的支撑下界也包含于本效果界。那里保留的几何证明进一步显示了全体分支为何共同受支撑限制。这里的辅助向量及效果只比较同一组实际分支的数据，既不提供新增操作，也不将必要条件提升为 diamond 误差的充分条件。

## 398. 四路径扰动族在固定正误差下的线性成功尺度

**定义 398.1（近似恢复成功率的上确界）。** 对相关矩阵 $C$ 及 $0\le\delta\le2$，在定义 395.1 的有限协议范围内定义

$$
\eta_\delta(C)
 =\sup\left(\{0\}\ \cup
 \left\{t\in(0,1]:
 \begin{array}{l}
 \text{存在协议满足 }\mathcal T_{\mathrm s}^{*}(I_S)=tI_S,\\
 \|\mathcal T_{\mathrm s}-t\operatorname{id}_S\|_\diamond\le t\delta
 \end{array}\right\}\right).
$$

加入 $0$ 使没有任何正成功协议时上确界仍为零，不表示对零成功映射作条件归一化。此处只定义上确界，不主张近似最优协议取得该值。$\delta=0$ 时由定理 390.2 有 $\eta_0(C)=\eta(C)$；精确情形的取得性不被默默推广到正误差情形。

**定理 398.2（固定误差下的双边线性界）。** 使用定义 392.1 的 $B,W,C_0,\nu$ 和定理 393.1 的
$C_\varepsilon=(1-\varepsilon)C_0+\varepsilon I_4$，$0\le\varepsilon\le1$。令

$$
L=\|W\|_{\mathrm{op}}=2+\frac1{\sqrt2},
\qquad \bar\delta=\frac{\nu}{2L},
\qquad \nu=3-2\sqrt2>0.
$$

对每个固定的 $0\le\delta<\bar\delta$，定义

$$
K_\delta=
\frac{4}{\left[\sqrt{\nu(1-\delta/2)}
             -\sqrt{(4L-\nu)\delta/2}\right]^2}.
$$

该常数有限且为正，并且对整个 $0\le\varepsilon\le1$，

$$
\boxed{\qquad
\varepsilon\le\eta_\delta(C_\varepsilon)
 \le\min\{1,K_\delta\varepsilon\}.
\qquad}
$$

因而在每个这样的固定误差容限下，

$$
\eta_\delta(C_\varepsilon)=\Theta(\varepsilon)
\qquad(\varepsilon\downarrow0).
$$

对端点 $C_0$，任何正成功率协议的误差至少为 $\bar\delta$，同时仍适用第 396 节的 $2\mu(C_0)/4$ 下界。对每个 $\varepsilon>0$，则已有成功概率恰为 $\varepsilon$ 的完美恢复协议。这里的线性阶没有指定锐系数，$\bar\delta$ 也不被断言为锐阈值。

证明。按定义 392.1 的 $B$ 逐项相乘，得到

$$
BB^\dagger=
\begin{pmatrix}
2&(1-i)/2\\
(1+i)/2&2
\end{pmatrix}.
$$

其特征多项式是 $(2-\lambda)^2-1/2$，故本征值为 $2\pm1/\sqrt2$。$B^\dagger B$ 与 $BB^\dagger$ 的非零本征值相同：例如 $BB^\dagger u=\lambda u$ 且 $\lambda>0$ 时，$B^\dagger u\ne0$ 并满足 $B^\dagger B(B^\dagger u)=\lambda B^\dagger u$；反向用 $B$ 同理。因此 $W\succeq0$ 的算子范数确为所示 $L$。

取定理 397.1 的效果 $E=W/L$，则 $0\preceq E\preceq I_4$。定理 392.2 给出相位最小值 $\nu$、$WC_0=0$ 与 $\operatorname{Tr}W=4$，因而

$$
a=\frac{\nu}{4L},
\qquad
\operatorname{Tr}(EC_\varepsilon)=\frac{4\varepsilon}{L},
\qquad 2a=\bar\delta.
$$

在 $0\le\delta<\bar\delta$ 上，

$$
r_a(\delta)
 =\frac1{4L}
 \left[\sqrt{\nu(1-\delta/2)}
       -\sqrt{(4L-\nu)\delta/2}\right]^2.
$$

方括号严格为正，因为比较两个非负平方项后，该条件恰为
$\nu>2L\delta$。定理 397.1 因此对每个可行 $t>0$ 给出

$$
t\le\frac{4\varepsilon/L}{4r_a(\delta)}
 =K_\delta\varepsilon.
$$

结合 $t\le1$ 并对可行集合（包括加入的 $0$）取上确界，就得到上界。$\varepsilon=0$ 时 $\operatorname{Tr}(EC_0)=0$，定理 397.1 的未反演形式直接给出任意正成功协议必须满足 $\delta\ge2a=\bar\delta$；因此在当前误差区间内 $\eta_\delta(C_0)=0$。

下界由第 393 节的同一个有限 Fourier 构造给出：其四个成功矩阵之和是

$$
\frac\varepsilon4\sum_{k=0}^3z^{(k)}z^{(k)\dagger}
 =\varepsilon I_4\preceq C_\varepsilon,
$$

剩余 $(1-\varepsilon)C_0$ 作为失败分支。对 $\varepsilon>0$，四个成功结果分别作相位酉反馈后，总成功映射为
$\mathcal T_{\mathrm s,\varepsilon}=\varepsilon\operatorname{id}_S$，误差为零，故也满足任意上述正误差容限。$\varepsilon=0$ 的下界由定义中加入的零给出。这证明双边界及 $\Theta(\varepsilon)$，其中比较常数可取 $1$ 与固定的 $K_\delta$。证毕。

$\delta=0$ 时 $K_0=4/\nu$，上述结论回到定理 393.1 已有的精确成功界。这里的增量是在每个固定的 $0<\delta<\bar\delta$ 下仍有双边线性阶；没有将 $\delta$ 随 $\varepsilon$ 趋近阈值的情形纳入同一个统一常数，也没有由上界反推其可达到。

对上述 Fourier 协议族，$\varepsilon>0$ 时接受后的通道恒为恒等通道，而未归一化成功映射在 diamond 范数中趋于零：

$$
\frac{\mathcal T_{\mathrm s,\varepsilon}}{\varepsilon}
 =\operatorname{id}_S,
\qquad
\|\mathcal T_{\mathrm s,\varepsilon}\|_\diamond=\varepsilon
 \longrightarrow0.
$$

前式来自 $\mathcal T_{\mathrm s,\varepsilon}=\varepsilon\operatorname{id}_S$。对任何参考维数，恒等映射保持迹范数，故 $\|\operatorname{id}_S\|_\diamond=1$；范数齐次性给出后式。$\varepsilon=0$ 的成功映射是零映射，除以成功概率的条件化操作无定义。

因此，正 $\varepsilon$ 上的完美条件恢复与 $C_0$ 的正误差下界相容：前者使用概率趋零的成功事件，没有在端点给出一个正概率精确协议。未归一化成功映射本身连续趋于零，此处没有主张它发生不连续。定义 393.2 中随 $\varepsilon$ 改变的纯记录耦合及其完整访问前提仍然有效，不能将这一族解释为对同一不可访问记录免费增加逆转权限。

来源的适用范围也保持分明。Gregoratti–Werner 的上述 Proposition 8 提供固定 Kraus 分解的保真度成分；从该成分到本节的后选择 diamond 必要界，使用的是命题 395.2、定理 396.2 和定理 397.1 中写出的直接推导。Buscemi–Chiribella–D’Ariano，[*Inverting Quantum Decoherence by Classical Feedback from the Environment*, quant-ph/0504195v5](https://arxiv.org/abs/quant-ph/0504195v5)，Theorem 2（PDF 第 2 页）给出极端 Schur 通道的秩界及低维 random-unitary 结论；环境反馈讨论和四维秩二例子的式 (9) 位于 PDF 第 3 页。它们支持所用框架及例子的来源，不替代这里的成功率—误差证明。上述组合推导不据此主张文献原创性。

**问题 398.3（共同支撑、效果质量与尚未求出的前沿）。** 第 396–398 节表达的关系是：所有成功分支同时受同一个 $C$ 的正半定支配，近似恒等恢复又要求其相位匹配的总权重足够大；效果 $E$ 则把这个要求与同一 $C$ 所提供的质量 $\operatorname{Tr}(EC)$ 联系起来。若相位方向与支撑有正距离，缩小成功率不能改变该距离；当扰动提供少量效果质量时，在所证明的固定精度区间内，成功率也只能处于相同的线性尺度。起作用的是共同支撑、允许的反馈与精度合同之间的关系，单独的秩或某一个分支的保真度不能替代这些联合条件。

仍待求解的是同一单份、完整记录、有限测量与酉反馈接口中的可达关系

$$
\mathcal R(C)=\{(t,\delta):\text{存在定义 395.1 的协议实现该合同}\},
$$

特别是：固定 $\delta$ 时 $\eta_\delta(C_\varepsilon)/\varepsilon$ 的极限是否存在及其锐值；$C_0$ 上对所有 $t>0$ 协议取误差下确界的确切值与取得性；线性成功尺度所允许的最大误差范围；以及效果必要界中哪些点能由实际协议达到。单个效果产生的 $K_\delta$、$\bar\delta$ 和支撑投影下界均未解决这些锐问题。问题 394.2 中整个 $[0,1]$ 上的精确 $\eta(C_\varepsilon)$、锐渐近以及确定精确恢复集合 $\{\varepsilon:\eta(C_\varepsilon)=1\}$ 也继续保留。

## 追加锚（本行以下为增补区）
## 399. 整体未知输入的张量扩张保留支撑误差下界

**定义 399.1（张量输入与归一化误差合同）。** 固定定义 389.1 的 $d$ 维系统、归一化纯记录 $r_i$ 及相关矩阵 $C$，令 $n\ge1$ 为整数。对整个输入空间 $S^{\otimes n}$ 使用乘积基 $|\mathbf i\rangle=|i_1,\ldots,i_n\rangle$，记录耦合为

$$
J^{\otimes n}|\mathbf i\rangle
 =|\mathbf i\rangle\otimes
   |r_{i_1}\rangle\otimes\cdots\otimes|r_{i_n}\rangle,
\qquad
C^{\otimes n}_{\mathbf i,\mathbf j}
 =\prod_{a=1}^n C_{i_a j_a}.
$$

这里输入是任意 $d^n$ 维未知态，允许不同系统因子之间以及与任意有限维参考系统之间存在纠缠；“张量”限定耦合的形式，不限定输入态为乘积态。允许测量全部联合记录的任意有限 POVM，再按结果对整个 $S^{\otimes n}$ 施加任意联合酉反馈。对所接受结果的总映射 $\mathcal T_{\mathrm s}$，要求

$$
\mathcal T_{\mathrm s}^{*}(I)=tI,\qquad
0<t\le1,\qquad
\|\mathcal T_{\mathrm s}-t\operatorname{id}_{S^{\otimes n}}\|_\diamond
 \le t\delta.
$$

$\delta$ 使用第 395 节未除以 $2$ 的 diamond 范数约定。成功概率 $t$ 对全部输入相同，误差要求包括保留外部参考系统。这个任务没有选择编码子空间，也没有把恢复目标缩减为部分输入。

**定理 399.2（相位支撑间隙的张量下界）。** 对线性子空间 $H\subseteq\mathbb C^d$，令 $P_H$ 为其正交投影，定义

$$
\mu(H)=\min_{z\in\mathbb T^d}\|(I-P_H)z\|_2^2.
$$

对每个整数 $n\ge1$，有

$$
\boxed{\quad \mu(H^{\otimes n})\ge d^{n-1}\mu(H).\quad}
$$

特别地，取 $H=\operatorname{ran}C$，则定义 399.1 的每个协议均满足

$$
\boxed{\quad \delta\ge\frac{2\mu(C)}d.\quad}
$$

这里 $\mu(C)=\mu(\operatorname{ran}C)$ 沿用定义 396.1。若 $\eta(C)=0$，右侧严格为正，且对所有 $n\ge1$ 及所有输入无关的 $t>0$ 同时成立。

证明。正交投影满足 $P_{H^{\otimes n}}=P_H^{\otimes n}$。当 $n\ge2$ 时，

$$
I-P_H^{\otimes n}-(I-P_H)\otimes I_{d^{n-1}}
 =P_H\otimes(I_{d^{n-1}}-P_H^{\otimes(n-1)})\succeq0;
$$

$n=1$ 时两者相等。任取 $z\in\mathbb T^{d^n}$，以其后 $n-1$ 个指标 $\alpha\in\{1,\ldots,d\}^{n-1}$ 将坐标分成 $d$ 维切片 $z^{(\alpha)}$。每个切片都属于 $\mathbb T^d$，故

$$
\begin{aligned}
\|(I-P_H^{\otimes n})z\|_2^2
 &=z^\dagger(I-P_H^{\otimes n})z\\
 &\ge z^\dagger((I-P_H)\otimes I_{d^{n-1}})z\\
 &=\sum_\alpha\|(I-P_H)z^{(\alpha)}\|_2^2
 \ge d^{n-1}\mu(H).
\end{aligned}
$$

$n=1$ 时后方指标只有一个空元组，同一求和仍成立。相位集合紧致保证最小值取得；对 $z$ 取最小值即得第一式。

$C\succeq0$ 的谱分解表明，$C^{\otimes n}$ 的正本征空间正是 $H^{\otimes n}$，所以 $\operatorname{ran}(C^{\otimes n})=H^{\otimes n}$。将定理 396.2 应用于维数 $d^n$ 的相关矩阵 $C^{\otimes n}$，得到

$$
\delta\ge\frac{2\mu(C^{\otimes n})}{d^n}
 \ge\frac{2d^{n-1}\mu(C)}{d^n}
 =\frac{2\mu(C)}d.
$$

最后，$\eta(C)=0$ 时 $\mu(C)>0$ 由定理 396.2 给出。证毕。

这里的切片论证与 Kraus 支撑方法相关。Yu–Duan–Xu，[*Bounds on the distance between a unital quantum channel and the convex hull of unitary channels, with applications to the asymptotic quantum Birkhoff conjecture*, arXiv:1201.1172v1](https://arxiv.org/abs/1201.1172v1)，Lemma 2（PDF 第 7–8 页）以 Kraus 算子空间不含酉算子给出到混合酉通道集合的正距离；Theorem 2 与 Corollary 1（PDF 第 8 页）利用 Schur 张量因子的块结构保留该距离下界。该文比较的是通道与混合酉集合；本定理比较经记录测量和反馈后的成功映射与 $t\operatorname{id}$，其误差结论由上面的切片估计及定理 396.2 推出。这是已有支撑方法的应用，不将两种距离目标视为同一个优化问题，也不主张上述常数是锐误差下界。

## 400. 同一系统的重复记录产生 Hadamard 幂

**定义 400.1（保持系统基的重复记录接口）。** 对任意正整数 $n$，在同一个 $S=\mathbb C^d$ 中给定任意未知输入，保持定义 389.1 的系统基不变，依次使 $n$ 个初始纯空白记录与该基受控耦合，得到

$$
J_n|i\rangle=|i\rangle\otimes|r_i\rangle^{\otimes n},
\qquad
E_n=\operatorname{span}\{r_i^{\otimes n}:1\le i\le d\}.
$$

直到最后的联合 POVM，所有 $n$ 份记录均保持量子可访问。测量可作用在完整 $E_n$ 上，结果只控制系统酉反馈；输入与任意外部参考系统的纠缠也须恢复。$E_n$ 是全部联合记录态的张成空间，不能通过遗漏一份实际存在的记录来定义。若实际记录空间大于 $E_n$，效果可在其正交补上补全。

每一步的制备以正交的系统基为控制：对固定空白 $|b\rangle$，指定 $|i\rangle|b\rangle\mapsto|i\rangle|r_i\rangle$ 后补成酉映射。该权限并非对任意未知记录态执行 $|r\rangle\mapsto|r\rangle|r\rangle$ 的克隆权限。$n$ 是记录次数；定义没有指定秒数、耦合速率、存储寿命或实施成本。

**命题 400.2（约化通道与有限相位分解的测量实现）。** 记逐项幂为

$$
(C^{\circ n})_{ij}=(C_{ij})^n,\qquad
\Phi_C(X)=C\circ X.
$$

则 $J_n$ 是等距映射，且

$$
\operatorname{Tr}_{E_n}(J_nXJ_n^\dagger)
 =C^{\circ n}\circ X=\Phi_C^n(X),
$$

其中 $\Phi_C^n$ 表示同一 $d$ 维矩阵空间上的 $n$ 次通道复合。若存在有限分解

$$
C^{\circ n}=\sum_{a=1}^m p_a z_a z_a^\dagger,
\qquad p_a\ge0,\qquad \sum_{a=1}^m p_a=1,
\qquad z_a\in\mathbb T^d,
$$

则存在定义 400.1 的有限 POVM 和反馈，使每个校正分支为 $p_a\operatorname{id}_S$，全部结果的总校正映射为 $\operatorname{id}_S$。这一结论适用于任意有限参考空间 $A$ 与任意联合输入 $\rho_{AS}$，分支输出为 $p_a\rho_{AS}$。

证明。不同 $i$ 的系统因子正交，而每个 $r_i^{\otimes n}$ 归一化，故 $J_n^\dagger J_n=I_S$。在矩阵单位 $|i\rangle\langle j|$ 上，记录偏迹给出

$$
\langle r_j^{\otimes n}|r_i^{\otimes n}\rangle
 =\langle r_j|r_i\rangle^n=(C_{ij})^n.
$$

连续 $n$ 次逐项乘以 $C$ 得到相同系数，故约化通道恰为 $\Phi_C^n$。这与定义 399.1 中作用在 $d^n$ 维输入上的 $\Phi_C^{\otimes n}$ 有不同的输入空间。

为明确实现，沿用定理 390.2 的 ket 行坐标约定，在 $E_n$ 的一组正交基中写 $R_n$ 的第 $i$ 行为 $r_i^{\otimes n}$ 的坐标。$R_n$ 满列秩，$R_nR_n^\dagger=C^{\circ n}$。令

$$
\begin{aligned}
R_n^+&=(R_n^\dagger R_n)^{-1}R_n^\dagger,\\
D_a&=\left[R_n^+(p_a z_a z_a^\dagger)(R_n^+)^\dagger\right]^{\mathsf T},\\
U_a&=\operatorname{diag}\bigl(\overline{(z_a)_1},\ldots,
                              \overline{(z_a)_d}\bigr).
\end{aligned}
$$

这里 $\mathsf T$ 是普通转置。因 $p_a z_a z_a^\dagger\preceq C^{\circ n}$，其值域包含于 $\operatorname{ran}R_n$；定理 390.2 的实现等式给出

$$
D_a\succeq0,\qquad \sum_aD_a=I_{E_n},\qquad
R_nD_a^{\mathsf T}R_n^\dagger=p_a z_a z_a^\dagger.
$$

相应系统分支是 $(p_a z_a z_a^\dagger)\circ X$。逐项乘以 $U_a$ 及其伴随，得到 $\mathcal T_a(X)=p_aX$。对参考空间张量恒等映射后仍是同一等式，求和即得确定精确恢复。若记录空间还有正交补，可在该补空间取任意总和为恒等算子的正效果族，与 $D_a$ 作直和；所有实际记录态均位于 $E_n$，故分支不变。证毕。

此实现是 Gregoratti–Werner，[*Quantum Lost and Found*, quant-ph/0209025v1](https://arxiv.org/abs/quant-ph/0209025v1)，Theorem 1（PDF 第 4 页）的纯环境测量实现及 Proposition 2（PDF 第 4–5 页）的校正条件在当前行坐标中的应用。这里完整访问的是联合记录张成空间，包括所需的相干测量；若已有记录泄漏到不可访问的环境，上述 POVM 权限就不再是给定权限，不能从本命题推出该记录也被擦除。

## 401. 有限成对相位混合与共线商的充分次数

**命题 401.1（小非对角总量的有限相位分解）。** 设 $d\ge1$，$H\in\mathbb C^{d\times d}$ 为 Hermitian 矩阵，$H_{ii}=1$。若

$$
s(H)=\sum_{1\le i<j\le d}|H_{ij}|\le1,
$$

则 $H\in\mathcal P_d$。这里不必预先假设 $H\succeq0$，以下有限相位分解同时证明其正半定性。

证明。$d=1$ 时 $H=(1)$ 本身是相位秩一矩阵。以下设 $d\ge2$。对每个 $i<j$ 及实数 $\phi$，构造对角元全为 $1$、仅有非零非对角元

$$
A^{(ij,\phi)}_{ij}=e^{i\phi},\qquad
A^{(ij,\phi)}_{ji}=e^{-i\phi}
$$

的矩阵。取 $z_i=1$、$z_j=e^{-i\phi}$，其余 $d-2$ 个坐标独立遍取 $\{-1,1\}$，以相同权重 $2^{-(d-2)}$ 对 $zz^\dagger$ 求和。第 $(i,j)$ 项为 $z_i\overline{z_j}=e^{i\phi}$；涉及一个其余坐标的交叉项因符号均值为零而消失，涉及两个不同其余坐标的项因独立性而消失，对角元恒为 $1$。这正给出 $A^{(ij,\phi)}\in\mathcal P_d$。$d=2$ 时没有其余坐标，符号集合含一个空选择，所得就是一项权重为 $1$ 的相位矩阵。

同样，对全部 $2^d$ 个符号向量 $\varepsilon\in\{-1,1\}^d$ 作均匀混合，有

$$
I_d=2^{-d}\sum_{\varepsilon\in\{-1,1\}^d}
       \varepsilon\varepsilon^\dagger\in\mathcal P_d.
$$

对 $H_{ij}\ne0$ 选择 $\phi_{ij}$ 使 $H_{ij}=|H_{ij}|e^{i\phi_{ij}}$。直接比较每个对角元和非对角元，得到

$$
\boxed{\quad
H=(1-s(H))I_d+
 \sum_{\substack{i<j\\H_{ij}\ne0}}
       |H_{ij}|A^{(ij,\phi_{ij})}.
\quad}
$$

外层权重均非负且总和为 $1$；展开各项内部的有限混合仍是有限相位混合。零系数不需要指定辐角；$s(H)=0$ 时只有 $I_d$，$s(H)=1$ 时其系数为零，均无例外。证毕。

**命题 401.2（相位凸包对 Schur 乘积封闭）。** 若 $A,B\in\mathcal P_d$，则 $A\circ B\in\mathcal P_d$。

证明。取两个有限相位分解

$$
A=\sum_a p_a z_a z_a^\dagger,\qquad
B=\sum_b q_b w_b w_b^\dagger,
\qquad \sum_a p_a=\sum_bq_b=1.
$$

令 $z_a\circ w_b$ 表示坐标逐项相乘。每个这样的向量仍属于 $\mathbb T^d$，且

$$
A\circ B=\sum_{a,b}p_aq_b
 (z_a\circ w_b)(z_a\circ w_b)^\dagger.
$$

这是有限和，权重非负且总和为 $(\sum_ap_a)(\sum_bq_b)=1$。证毕。

**定理 401.3（完整重复记录的共线商证书）。** 设 $C$ 为任意 $d$ 维复相关矩阵，采用定义 389.1 的归一化纯记录表示。在指标集上定义

$$
i\sim j\quad\Longleftrightarrow\quad |C_{ij}|=1.
$$

这是等价关系。设其共有 $k$ 类，每类选代表 $q_a$，令 $a(i)$ 为 $i$ 所属类。存在单位相位 $u_i$，使

$$
r_i=u_i r_{q_{a(i)}},\qquad
\widetilde C_{ab}=C_{q_aq_b},\qquad
C_{ij}=u_i\overline{u_j}\widetilde C_{a(i)a(j)}.
$$

若 $k=1$，则对所有整数 $n\ge1$，定义 400.1 的接口都有确定精确恢复。若 $k\ge2$，置

$$
r=\max_{a<b}|\widetilde C_{ab}|<1.
$$

对每个满足下式的整数 $n\ge1$，同样存在有限 POVM 的确定精确恢复：

$$
\sum_{a<b}|\widetilde C_{ab}|^n\le1.
$$

特别地，$r=0$ 时所有 $n\ge1$ 均满足；$0<r<1$ 时，充分条件为

$$
\frac{k(k-1)}2\,r^n\le1.
$$

故对每个固定 $C$，存在有限整数 $N\ge1$，使全部 $n\ge N$ 满足 $\eta(C^{\circ n})=1$。此处 $N$ 可依赖于 $C$。

一般的最终相位混合性质已有先例：Bhat–Devendra，[*On Regions of Mixed Unitarity for Semigroups of Unital Quantum Channels*, arXiv:2512.23598v3](https://arxiv.org/abs/2512.23598v3)，Theorem 6.10（PDF 第 28 页）已对每个相关矩阵断言所有充分大的 Hadamard 幂均为 rank-one correlation matrices 的凸组合，即属于这里的 $\mathcal P_d$。其 Theorem 3.9（PDF 第 11–12 页）是 unital 通道的复合幂最终混合酉结论；没有将其表述为张量幂结论。下述证明给出这一已知性质在完整记录接口中的初等充分证书与有限测量构造，不主张最终恢复性质的原创性。

证明。归一化向量的 Cauchy–Schwarz 等号条件给出
$|\langle r_j|r_i\rangle|=1$ 当且仅当两向量共线；共线且归一化又等价于相差一个单位相位。因此 $\sim$ 自反、对称且传递，代表元与 $u_i$ 满足所示公式。$\widetilde C$ 是代表记录的相关矩阵；不同代表不共线，故不同类间的模严格小于 $1$。类数有限，所以 $k\ge2$ 时所定义最大值 $r$ 也严格小于 $1$。

对任意 $n\ge1$，逐项取幂得到

$$
(C_{ij})^n
 =u_i^n\overline{u_j^n}
   (\widetilde C_{a(i)a(j)})^n.
$$

若 $k=1$，令 $z_i=u_i^n$，直接有 $C^{\circ n}=zz^\dagger$，可用命题 400.2。若 $k\ge2$ 且所示非对角总量不超过 $1$，命题 401.1 给出有限分解

$$
\widetilde C^{\circ n}
 =\sum_{b=1}^m p_b w_b w_b^\dagger,
\qquad w_b\in\mathbb T^k,\quad
p_b\ge0,\quad\sum_bp_b=1.
$$

对每个 $b$ 定义提升相位向量

$$
(z_b)_i=u_i^n(w_b)_{a(i)}.
$$

每个分量模为 $1$，而对每个 $i,j$ 有

$$
\sum_b p_b(z_b)_i\overline{(z_b)_j}
 =u_i^n\overline{u_j^n}
   (\widetilde C_{a(i)a(j)})^n
 =(C_{ij})^n.
$$

于是 $C^{\circ n}=\sum_bp_bz_bz_b^\dagger\in\mathcal P_d$，命题 400.2 将其实现为全部分支概率之和为 $1$ 的恢复。

$r=0$ 时商矩阵是 $I_k$，其所有正整数幂仍是 $I_k$，上面的有限分解与提升立即适用。对 $0<r<1$，有

$$
\sum_{a<b}|\widetilde C_{ab}|^n
 \le\frac{k(k-1)}2r^n\longrightarrow0.
$$

例如可取

$$
N=\max\left\{1,
 \left\lceil\frac{\log(k(k-1)/2)}{-\log r}\right\rceil\right\}.
$$

分母为正；$k=2$ 时分子为零，由外层最大值给出 $N=1$。对所有 $n\ge N$，上述充分不等式均成立，证明完毕。

该证书保留同一共线类内部的单位模重叠，并仅压低不同类之间的模；直接要求原矩阵每个非对角元的模都小于 $1$ 会遗漏这些类。定理未将充分次数认作最小次数，也未给出维数一致的普遍次数阈值。它产生有限个测量结果，但没有对实现这些联合效果所需的物理资源作估计。

## 402. 四路径例子的二次幂恢复与两种指数

**命题 402.1（二次 Hadamard 幂的四相位恒等式）。** 对定义 392.1 的 $R_0$ 与 $C_0=R_0R_0^\dagger$，取以下四个列向量：

$$
z_1=\begin{pmatrix}1\\i\\1\\1\end{pmatrix},\qquad
z_2=\begin{pmatrix}1\\i\\i\\-i\end{pmatrix},\qquad
z_3=\begin{pmatrix}1\\-i\\1\\i\end{pmatrix},\qquad
z_4=\begin{pmatrix}1\\-i\\-i\\1\end{pmatrix}.
$$

则

$$
\boxed{\quad
\frac14\sum_{a=1}^4z_az_a^\dagger
 =\begin{pmatrix}
 1&0&1/2&1/2\\
 0&1&1/2&-1/2\\
 1/2&1/2&1&-i/2\\
 1/2&-1/2&i/2&1
 \end{pmatrix}
 =C_0^{\circ2}.
\quad}
$$

因此，在同一四维系统的两份完整可访问记录上，存在四个结果的有限 POVM，校正后的四个映射各为 $\operatorname{id}_S/4$，总映射为 $\operatorname{id}_S$，从而 $\eta(C_0^{\circ2})=1$。

证明。按 $R_0$ 的行约定，$C_0$ 的六个严格上三角元依次为

$$
(C_{0,12},C_{0,13},C_{0,14},C_{0,23},C_{0,24},C_{0,34})
 =\left(0,\frac1{\sqrt2},\frac1{\sqrt2},
          \frac1{\sqrt2},-\frac i{\sqrt2},\frac{1-i}2\right).
$$

故它们的平方依次为 $(0,1/2,1/2,1/2,-1/2,-i/2)$。另一方面，令 $M=\frac14\sum_{a=1}^4z_az_a^\dagger$，逐项有

$$
\begin{aligned}
M_{12}&=\tfrac14(-i-i+i+i)=0,\\
M_{13}&=\tfrac14(1-i+1+i)=\tfrac12,\\
M_{14}&=\tfrac14(1+i-i+1)=\tfrac12,\\
M_{23}&=\tfrac14(i+1-i+1)=\tfrac12,\\
M_{24}&=\tfrac14(i-1-1-i)=-\tfrac12,\\
M_{34}&=\tfrac14(1-1-i-i)=-\tfrac i2.
\end{aligned}
$$

四个对角元均为 $\frac14(1+1+1+1)=1$，下三角元由 Hermitian 共轭确定，故全部矩阵元相符。四个 $z_a$ 都是相位向量，权重均为 $1/4$。将它们代入命题 400.2 的 $n=2$、$R_2$ 与效果公式，取 $U_a=\operatorname{diag}(\overline{z_a})$，得到

$$
\mathcal T_a=\tfrac14\operatorname{id}_S\quad(1\le a\le4),
\qquad
\sum_{a=1}^4\mathcal T_a=\operatorname{id}_S.
$$

每个结果对所有输入的概率都是 $1/4$；确定性来自接受全部四个经各自反馈校正的结果，不是某个指定结果以概率 $1$ 出现。证毕。

**命题 402.2（首次成功指数与充分的以后全部成功界）。** 定义 400.1 的重复记录接口中，令

$$
\begin{aligned}
n_{\mathrm{first}}(C)
 &=\min\{n\in\mathbb Z_{\ge1}:\eta(C^{\circ n})=1\},\\
N_{\mathrm{all}}(C)
 &=\min\{N\in\mathbb Z_{\ge1}:\ \forall n\ge N,
                         \ \eta(C^{\circ n})=1\}.
\end{aligned}
$$

定理 401.3 保证这两个集合均非空。对 $C_0$，有

$$
\eta(C_0)=0,\qquad
\eta(C_0^{\circ2})=1,\qquad
n_{\mathrm{first}}(C_0)=2,
$$

并且

$$
\eta(C_0^{\circ4})=1,\qquad
\eta(C_0^{\circ n})=1\quad(n\ge5),\qquad
2\le N_{\mathrm{all}}(C_0)\le4.
$$

这些结论不确定 $\eta(C_0^{\circ3})$，因而也不确定 $N_{\mathrm{all}}(C_0)$ 的确切值。

证明。定理 392.2 已给出 $\eta(C_0)=0$，命题 402.1 给出二次幂的确定恢复；正整数中只有 $1$ 小于 $2$，故首次成功指数恰为 $2$。

由命题 401.2，$C_0^{\circ4}=C_0^{\circ2}\circ C_0^{\circ2}\in\mathcal P_4$。其有限分解可直接写成

$$
C_0^{\circ4}
 =\frac1{16}\sum_{a,b=1}^4
 (z_a\circ z_b)(z_a\circ z_b)^\dagger,
$$

再由命题 400.2 实现恢复。对于更高次数，$C_0$ 的六个无序非对角对中，一个为零，另五个的模都是 $1/\sqrt2$，故

$$
\sum_{i<j}|(C_0^{\circ n})_{ij}|
 =5\,2^{-n/2}.
$$

$n=5$ 时 $5\,2^{-5/2}\le1$，因为两侧为正且平方比较等价于 $25\le32$；此表达式随 $n$ 增加而减小。因此所有 $n\ge5$ 均满足命题 401.1 的充分条件。结合 $n=4$ 的乘积构造，得到全部 $n\ge4$ 的确定恢复和 $N_{\mathrm{all}}(C_0)\le4$；$n=1$ 的失败给出下界 $2$。

在 $n=4$ 时，成对总量证书的左端是 $5/4>1$，但 Schur 乘积构造已经给出恢复。这也直接说明该总量条件只充分而非必要。上述两种构造没有给出 $n=3$ 的判定；一个充分条件未满足不能推出恢复不可能。首次成功只要求某一个幂成功，以后全部成功则量化全部后续幂，二者不能由名称或一次成功合并。证毕。

**命题 402.3（同一记录例子的两种操作结论）。** 对任意整数 $n\ge1$，在定义 399.1 的整个 $4^n$ 维未知输入恢复任务中，以 $C_0^{\otimes n}$ 为相关矩阵的每个输入无关正成功协议，都有

$$
\delta\ge\frac{\mu(C_0)}2>0.
$$

在定义 400.1 的同一四维系统重复记录任务中，两份记录已经具有命题 402.1 的确定精确恢复。

证明。$\eta(C_0)=0$ 与定理 396.2 给出 $\mu(C_0)>0$；定理 399.2 取 $d=4$ 即得第一式。第二项由命题 402.1 给出。前者的输入基索引是任意元组 $(i_1,\ldots,i_n)$，后者只保留同一个 $i$ 并生成 $r_i^{\otimes n}$；其输入维数、记录之间受同一索引控制的关系以及对应的相关矩阵均不同。因此这两个结论没有作用在同一恢复任务上。证毕。

第一项只涉及整个输入空间及所定义的测量—酉反馈权限，不推出编码子空间、蒸馏或恢复速率的不可能性，也没有求出可达到的锐张量误差。第二项要求所有记录保持联合量子可访问；受限记录访问、相干控制的实际成本及记录次数到物理时间的换算，需要另行给定模型。$C_0^{\circ3}$ 的恢复量、一般充分次数的锐性以及上述受限接口中的可达界，不由这些构造判定；这些未决范围不包含对其文献状态的断言。

## 追加锚（本行以下为增补区）

## 403. 四路径记录的十相位立方证书

**命题 403.1（三次 Hadamard 幂的显式相位分解）。** 沿用定义 392.1 的 $R_0$、$C_0=R_0R_0^\dagger$ 及定义 389.1 的 ket 行坐标约定。置

$$
s=\sqrt2,\qquad v=\frac{1+i}{s},\qquad
u=\bar v=\frac{1-i}{s},\qquad
z(a,b,c)=(1,v^a,v^b,v^c)^{\mathsf T}.
$$

下表每行给出两个列向量 $z_{j,0},z_{j,1}$ 的指数三元组；该行两个向量各自的权重均为 $p_{j,0}=p_{j,1}=A_j/112$，并非两者合计的权重。令 $P_j=z_{j,0}z_{j,0}^\dagger+z_{j,1}z_{j,1}^\dagger$；表中最后六列为它的严格上三角元。

| 403 证书对 | 两个指数三元组 | 每个向量的权重 $A_j/112$ | $(P_j)_{12}$ | $(P_j)_{13}$ | $(P_j)_{14}$ | $(P_j)_{23}$ | $(P_j)_{24}$ | $(P_j)_{34}$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 403-P1（$j=1$） | $(1,0,0)$，$(1,1,7)$ | $(18-6s)/112$ | $2u$ | $1+u$ | $1+v$ | $1+v$ | $v+i$ | $1+i$ |
| 403-P2（$j=2$） | $(1,2,6)$，$(1,7,1)$ | $(-42+42s)/112$ | $2u$ | $v-i$ | $u+i$ | $u+i$ | $1-u$ | $-1-i$ |
| 403-P3（$j=3$） | $(4,2,1)$，$(6,7,6)$ | $(64-40s)/112$ | $-1+i$ | $v-i$ | $u+i$ | $u+i$ | $1-u$ | $2v$ |
| 403-P4（$j=4$） | $(5,0,3)$，$(5,5,0)$ | $(8+9s)/112$ | $-2u$ | $1-u$ | $1-v$ | $1-v$ | $-v+i$ | $-2v$ |
| 403-P5（$j=5$） | $(5,1,4)$，$(5,4,7)$ | $(8-5s)/112$ | $-2u$ | $-1+u$ | $-1+v$ | $-1+v$ | $v-i$ | $-2v$ |

这十个向量均属于 $\mathbb T^4$，十个权重严格为正且总和为 $1$，并有

$$
\boxed{\quad
C_0^{\circ3}
 =\frac1{112}\sum_{j=1}^5 A_jP_j
 =\sum_{j=1}^5\sum_{b=0}^1p_{j,b}z_{j,b}z_{j,b}^\dagger
 \in\mathcal P_4.
\quad}
$$

证明。$|v|^2=(1+1)/s^2=1$，故所有坐标都是单位相位。计算表中各项可用

$$
(v^0,v^1,v^2,v^3,v^4,v^5,v^6,v^7)
 =(1,v,i,-u,-1,-v,-i,u),\qquad v^8=1.
$$

具体地，对 $k=(0,a,b,c)$，矩阵 $z(a,b,c)z(a,b,c)^\dagger$ 的 $(h,\ell)$ 元为 $v^{k_h-k_\ell}$，指数按模 $8$ 计算。例如第三对的第 $(1,2)$ 元是 $v^{-4}+v^{-6}=-1+i$，第 $(3,4)$ 元是 $v^{2-1}+v^{7-6}=2v$；相同公式给出表中其余各项。每个 $P_j$ 的对角元均为 $2$。

由 $1<s<3/2$，依次有

$$
A_1>9,\qquad A_2>0,\qquad A_3>4,\qquad
A_4>17,\qquad A_5>\tfrac12.
$$

归一化使用的是

$$
\sum_{j=1}^5A_j
 =(18-42+64+8+8)+s(-6+42-40+9-5)=56,
\qquad
\sum_{j=1}^5\sum_{b=0}^1p_{j,b}=\frac{2\cdot56}{112}=1.
$$

令 $N=\sum_jA_jP_j$。对角元均为 $112$。为核对全部独立非对角元，先记

$$
\begin{aligned}
A_1+A_2-A_4-A_5&=-40+32s,& A_2+A_3&=22+2s,\\
A_4-A_5&=14s,& A_3-A_4-A_5&=48-44s,\\
A_1-A_2&=60-48s.
\end{aligned}
$$

由表逐列加权，且 $u=s(1-i)/2$、$v=s(1+i)/2$，得到

$$
\begin{aligned}
N_{12}
 &=2u(A_1+A_2-A_4-A_5)+(-1+i)A_3\\
 &=(1-i)\bigl[s(-40+32s)-(64-40s)\bigr]=0,\\
N_{13}
 &=A_1(1+u)+(A_2+A_3)(v-i)+(A_4-A_5)(1-u)\\
 &=(18-6s)(1+u)+(22+2s)(v-i)+14s(1-u)\\
 &=(18+8s+9s-20+11s+2)
   +i(-9s+20+11s+2-22-2s)\\
 &=28s.
\end{aligned}
$$

最后一式也可直接从上一行收集 $u$、$v$ 的系数：$u$ 的系数为 $18-20s$，$v$ 的系数为 $22+2s$，常数项为 $18+8s-i(22+2s)$。表中第 $(1,4)$、$(2,3)$ 两列逐项都是第 $(1,3)$ 列的共轭，所有 $A_j$ 为实数，故

$$
N_{14}=N_{23}=\overline{N_{13}}=28s.
$$

其余两项为

$$
\begin{aligned}
N_{24}
 &=A_1(v+i)+(A_2+A_3)(1-u)+(A_4-A_5)(-v+i)\\
 &=(18-20s)v-(22+2s)u+(22+2s)+i(18+8s)\\
 &=(9s-20-11s-2+22+2s)
   +i(9s-20+11s+2+18+8s)\\
 &=28is,\\
N_{34}
 &=(A_1-A_2)(1+i)+2v(A_3-A_4-A_5)\\
 &=(1+i)\bigl[(60-48s)+s(48-44s)\bigr]
 =-28(1+i).
\end{aligned}
$$

因此 $N/112$ 的六个严格上三角元依次为

$$
\left(0,\frac{s}{4},\frac{s}{4},\frac{s}{4},
          \frac{is}{4},-\frac{1+i}{4}\right).
$$

它们正是命题 402.1 所列 $C_0$ 的六个严格上三角元的立方：例如 $(-i/s)^3=is/4$、$((1-i)/2)^3=-(1+i)/4$。两矩阵的对角元均为 $1$，下三角元由 Hermitian 共轭确定，故所有矩阵元相同，证毕。

这里的 $C_0$ 仍是定义 392.1 所引 Buscemi–Chiribella–D’Ariano，[*Inverting Quantum Decoherence by Classical Feedback from the Environment*, quant-ph/0504195v5](https://arxiv.org/abs/quant-ph/0504195v5)，式 (9)（PDF 第 3 页）的四维例子在当前行坐标中的逐项复共轭；上面的有限恒等式直接给出其立方分解。命题 402.2 所述“这些结论不确定三次幂”限定于该处已有构造；本命题补足这个实例，保留该处所有已给出的等式与上下界。

**推论 403.2（十个结果的完整记录恢复）。** 在定义 400.1 的同一四维系统重复记录接口中，取 $n=3$，令 $y=(j,b)$ 遍历命题 403.1 的十个标签。在完整记录张成空间 $E_3$ 的正交基中，按命题 400.2 取满列秩行矩阵 $R_3$，并定义

$$
\begin{aligned}
Q_y&=p_yz_yz_y^\dagger,\qquad
R_3^+=(R_3^\dagger R_3)^{-1}R_3^\dagger,\\
D_y&=\left[R_3^+Q_y(R_3^+)^\dagger\right]^{\mathsf T},
\qquad
U_y=\operatorname{diag}(\overline{(z_y)_1},\ldots,\overline{(z_y)_4}).
\end{aligned}
$$

则 $\{D_y\}$ 是有限 POVM，每个结果经 $U_y$ 反馈后的映射均为 $p_y\operatorname{id}_S$。对任意有限参考空间 $A$ 及任意联合密度矩阵 $\rho_{AS}$，该分支的未归一化输出为 $p_y\rho_{AS}$，概率为输入无关的 $p_y$；接受全部结果给出 $\eta(C_0^{\circ3})=1$。

证明。命题 403.1 给出 $\sum_yQ_y=C_0^{\circ3}=R_3R_3^\dagger$ 及 $0\preceq Q_y\preceq C_0^{\circ3}$。因此 $\operatorname{ran}Q_y\subseteq\operatorname{ran}R_3$。沿用定理 390.2 的普通转置约定与命题 400.2 的实现，有

$$
D_y\succeq0,\qquad
\sum_yD_y=\left[R_3^+R_3R_3^\dagger(R_3^+)^\dagger\right]^{\mathsf T}=I_{E_3},
\qquad
R_3D_y^{\mathsf T}R_3^\dagger=Q_y.
$$

系统分支为 $Q_y\circ X$，而 $U_y\operatorname{diag}(z_y)=I_S$，故

$$
U_y(Q_y\circ X)U_y^\dagger=p_yX
\quad\text{对每个 }X\in\mathbb C^{4\times4}.
$$

张量上参考系统的恒等映射即得 $p_y\rho_{AS}$；取迹得到概率，求和得到总恒等映射。若实际记录空间大于 $E_3$，可将 $E_3^\perp$ 上的恒等效果直和到某一个结果，其他结果在该补空间取零；实际记录态的分支不变。证毕。

本推论使用任意有限联合记录 POVM 的既有权限，参考系统始终不被操作，不增加系统—记录相干逆转权限。其成熟框架仍由 Gregoratti–Werner，[*Quantum Lost and Found*, quant-ph/0209025v1](https://arxiv.org/abs/quant-ph/0209025v1)，Theorem 1（PDF 第 4 页，初始纯环境下的 CP 分解实现）与 Proposition 2（PDF 第 4–5 页，同维情形的酉反馈校正）承担；这里将命题 403.1 的具体分解代入已有实现，不重设一般校正判据。

## 404. 平方与立方相位乘积给出精确的以后全部成功阈值

**定理 404.1（全部后续幂的有限分解与阈值二）。** 沿用命题 402.1 的四个平方相位向量，将其记为 $q_1,\ldots,q_4$；沿用命题 403.1 的 $z_{j,b}$ 与权重 $A_j/112$。以下 $\circ$ 表示坐标逐项相乘。对整数 $m\ge0$ 和元组 $\alpha=(a_1,\ldots,a_m)\in\{1,2,3,4\}^m$，定义

$$
w_\alpha=q_{a_1}\circ\cdots\circ q_{a_m}.
$$

$m=0$ 时元组集合只有空元组 $\varnothing$，约定 $w_\varnothing=\mathbf1\in\mathbb T^4$，标量空乘积为 $1$。则对每个 $m\ge1$，

$$
\boxed{\quad
C_0^{\circ(2m)}
 =\sum_{\alpha\in\{1,2,3,4\}^m}
     4^{-m}w_\alpha w_\alpha^\dagger,
\quad}
$$

而对每个 $m\ge0$，

$$
\boxed{\quad
C_0^{\circ(3+2m)}
 =\sum_{j=1}^5\sum_{b=0}^1
   \sum_{\alpha\in\{1,2,3,4\}^m}
     \frac{A_j}{112\,4^m}
     (z_{j,b}\circ w_\alpha)(z_{j,b}\circ w_\alpha)^\dagger.
\quad}
$$

它们分别提供至多 $4^m$ 和 $10\cdot4^m$ 个结果的恢复协议。因此在定义 400.1 的完整重复记录接口下，

$$
\eta(C_0^{\circ n})=1\quad\text{对所有整数 }n\ge2,
\qquad
\boxed{\quad n_{\mathrm{first}}(C_0)=N_{\mathrm{all}}(C_0)=2.\quad}
$$

这里的两个指数沿用命题 402.2 的确定恢复定义；若只要求正成功概率，也有

$$
\min\{n\in\mathbb Z_{\ge1}:\eta(C_0^{\circ n})>0\}=2.
$$

证明。平方分解的每个权重为 $1/4$。对 $m$ 份该分解直接应用命题 401.2 的 Schur 乘积公式，乘积权重为 $4^{-m}$，相位向量为 $w_\alpha$，得到偶数次幂公式。共有 $4^m$ 个元组，各权重严格为正且总和为 $1$。

把命题 403.1 的立方分解与这 $m$ 份平方分解作同一 Schur 乘积，便得到奇数次幂公式。坐标单位模在乘积下保留，权重归一化为

$$
\sum_{j,b,\alpha}\frac{A_j}{112\,4^m}
 =\left(\sum_{j,b}\frac{A_j}{112}\right)
   \left(\sum_\alpha4^{-m}\right)=1.
$$

$m=0$ 时，向量空乘积给出的矩阵是 $\mathbf1\mathbf1^\dagger$，它是 Schur 乘法的单位元，而非 $I_4$；奇数公式恰好还原立方分解。于是奇数次幂的标签数为 $10\cdot4^m$。这些只是所展示构造的结果数上界，不是最少结果数的断言。

每个整数 $n\ge2$ 要么为 $2m$（$m\ge1$），要么为 $3+2m$（$m\ge0$），故上述两式覆盖全部所需指数。对各个 $n$，把相应乘积标签统称为 $y$，相位向量、权重统称为 $v_y,\pi_y$。在完整 $E_n$ 上一次性采用命题 400.2 的效果与反馈

$$
D_y^{(n)}=\left[R_n^+(\pi_yv_yv_y^\dagger)(R_n^+)^\dagger\right]^{\mathsf T},
\qquad
U_y^{(n)}=\operatorname{diag}(\overline{v_y}),
$$

便有每个校正分支 $\mathcal T_y^{(n)}=\pi_y\operatorname{id}_S$，总和为 $\operatorname{id}_S$；任意参考联合态的相应分支为 $\pi_y\rho_{AS}$。这是对全部 $n$ 份量子记录作一次末端联合测量：乘积标签只是这次测量的结果索引，不是在各次记录之间依次测量、校正或丢弃记录。命题 400.2 的完整记录实现直接给出该 POVM，无须从若干中间测量协议推断它。因而 $\eta(C_0^{\circ n})=1$。

最后，定理 392.2 保留的 $\eta(C_0)=0$ 排除 $n=1$，而 $n=2$ 已确定成功，故首次确定成功与首次正概率成功均为 $2$。全部 $n\ge2$ 成功给出 $N_{\mathrm{all}}(C_0)\le2$，$n=1$ 的障碍给出反向不等式，得到确切值 $2$。证毕。

定理 404.1 的接口是定义 400.1 的单个四维未知输入及 $C_0^{\circ n}$；定义 399.1 的任意 $4^n$ 维未知输入则对应 $C_0^{\otimes n}$。定理 399.2 与命题 402.3 对后一任务的正误差下界仍按原量词成立，不能将前者的同一基索引重复记录换成独立输入元组而沿用阈值。完整记录访问包括最后测量所需的联合相干权限；若有一份记录不可访问，或只允许受限测量，就不满足本定理的操作前提。联合效果、存储与反馈的物理成本、记录次数到钟时间的换算、最少结果数及受限访问下的可达界，均未由上述有限分解求出。

一般相关矩阵的充分大 Hadamard 幂属于 $\mathcal P_d$，已有 Bhat–Devendra，[*On Regions of Mixed Unitarity for Semigroups of Unital Quantum Channels*, arXiv:2512.23598v3](https://arxiv.org/abs/2512.23598v3)，Theorem 6.10（PDF 第 28 页）。这里沿用该一般性质的既有归属与命题 401.2 的乘积法，利用平方和立方的具体证书求出这一四路径例子的阈值；不将一般最终混合酉性质或环境辅助校正框架主张为新理论，也不对该具体恒等式作原创性断言。

## 追加锚（本行以下为增补区）

## 405. 有限局部记录协议中的前缀保持与确定恢复障碍

**定义 405.1（每位持有者一份源记录的有限局部接口）。** 沿用定义 392.1 的四个记录向量，写成

$$
r_1=|0\rangle,\qquad r_2=|1\rangle,\qquad
r_3=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
r_4=\frac{|0\rangle+i|1\rangle}{\sqrt2},\qquad
P_i=|r_i\rangle\langle r_i|.
$$

固定任意正整数 $n\ge1$。输入仍是单个 $S=\mathbb C^4$ 上的任意未知态，并可与任意有限维参考 $A$ 纠缠。按定义 400.1 先完成全部 $n$ 份记录的制备：

$$
J_n|i\rangle=|i\rangle\otimes r_i^{\otimes n},\qquad
\rho_{ASR}=(\operatorname{id}_A\otimes J_n)\rho_{AS}
                  (\operatorname{id}_A\otimes J_n)^\dagger.
$$

此后第 $a$ 位持有者持有第 $a$ 个物理源量子比特，记录的局部分割始终是 $R=(\mathbb C^2)^{\otimes n}$。占据的联合张成空间 $E_n=\operatorname{span}\{r_i^{\otimes n}\}$ 沿用原定义；以 $E_n$ 为坐标空间不授予新的局部张量分解、跨持有者压缩或联合测量权限。

允许的记录操作是一棵有限树。每个非叶节点由一位持有者在其有限维可访问工作空间上执行有限结果 instrument，各分支完全正、总和保迹；下一位操作方和操作选择可依赖已经取得的经典信息。允许自适应经典通信、粗粒化结果、私有经典或量子记忆、重复访问同一持有者以及丢弃局部寄存器。初始辅助态与整个输入及参考独立，且在持有者之间为乘积态。禁止额外共享纠缠和量子通信。在整棵记录树结束前不操作 $S$；叶子结果只控制最后的系统酉算子 $U_w$，$A$ 始终不被操作。

以 $w$ 表示实际经典结果历史。若实际取得的标签后来被遗忘，可在数学求和中保留这些标签，而后续控制与反馈仍取原协议规定的相同值。粗粒化 CP 分支的未观测 Kraus 指标不因此成为可读取的经典结果。记叶子在反馈前的系统映射为 $\mathcal M_w$，反馈后为

$$
\mathcal T_w(X)=U_w\mathcal M_w(X)U_w^\dagger.
$$

确定性精确恢复要求对全部叶子求和得到 $\sum_w\mathcal T_w=\operatorname{id}_S$。后选择则须先声明接受集合 $W_{\mathrm s}$，要求 $\sum_{w\in W_{\mathrm s}}\mathcal T_w=t\operatorname{id}_S$，其中 $0\le t\le1$。这里都是全部四维矩阵上的线性映射等式；张量上 $\operatorname{id}_A$ 后，任意联合输入的接受输出为 $t\rho_{AS}$。只恢复指定经典基态、限制到某个码子空间或丢弃参考，是不同的任务。

有限性逐协议要求：允许零深度树、单结果通道、零 CP 结果、提前终止与不等叶深；不在所有候选协议之间预设统一深度、记忆维数或最小正分支概率。有限局部 instrument 的自适应复合与结果粗粒化采用 Chitambar 等，[*Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask)*, arXiv:1210.4583v2](https://arxiv.org/abs/1210.4583v2)，§2.2（PDF 第 5–6 页）的操作区分。本定义另将每棵树、每次结果集和局部工作空间限定为有限；该文区分的无界轮次与闭包不包含在下述定理的量词中。

**引理 405.2（共同标签乘积族的有限前缀保持）。** 设有限非空标签集 $I$ 对每个持有者 $a\in\{1,\ldots,m\}$ 给出有限维非零复 Hilbert 空间 $H_a$ 中的归一化向量 $s_{a,i}$，$m\ge1$。假设逐个局部算子张成条件成立：

$$
\operatorname{span}_{\mathbb R}
 \{|s_{a,i}\rangle\langle s_{a,i}|:i\in I\}
 =\operatorname{Herm}(H_a)\qquad(1\le a\le m).
$$

对乘积准备 $\bigotimes_a s_{a,i}$ 使用定义 405.1 的有限局部树和独立乘积辅助态，但将各源空间换成 $H_a$。假设每个实际经典前缀 $h$ 的概率 $p_h$ 对共同标签 $i$ 都相同。将初始辅助态分别作局部纯化，并保留每步局部 Stinespring 膨胀中原本不可访问的输出，则对每个 $p_h>0$，从原始源空间到保留输出的线性映射具有形式

$$
L_h=\sqrt{p_h}\bigotimes_{a=1}^m V_{a,h},\qquad
V_{a,h}:H_a\longrightarrow
\mathcal A_{a,h}\otimes\mathcal G_{a,h},\qquad
V_{a,h}^\dagger V_{a,h}=I_{H_a}.
$$

这里 $\mathcal A_{a,h}$ 是仍可访问的局部记忆，$\mathcal G_{a,h}$ 是只为表示而保留的不可访问寄存器；以后操作在旧 $\mathcal G_{a,h}$ 上恒等。上式在整个原始源乘积空间上成立，且每个正前缀保持各局部内积：

$$
\langle V_{a,h}s_{a,j}|V_{a,h}s_{a,i}\rangle
 =\langle s_{a,j}|s_{a,i}\rangle.
$$

零概率前缀的保留映射在原始源空间上为零，不为其指定归一化等距映射。共同标签 $i$ 无须遍历独立局部标签的所有元组，也不要求这些相关乘积准备的投影张成全局算子空间。

证明。先给出每步使用的局部算子事实。若 $E\in\operatorname{Herm}(H_a)$ 且 $\langle s_{a,i}|E|s_{a,i}\rangle=q$ 对全部 $i$ 成立，则 $E-qI$ 与全部源投影的实迹配对为零。由张成条件，它与每个 Hermitian 算子的实迹配对都为零，特别是

$$
\operatorname{Tr}[(E-qI)^2]=0.
$$

Hermitian 算子的本征值为实数，平方和为零迫使 $E=qI$。这里的信息完备性只指算子张成；这一标准含义见 D’Ariano–Perinotti–Sacchi，[*Informationally complete measurements and groups representation*, quant-ph/0310013v2](https://arxiv.org/abs/quant-ph/0310013v2)，§2、式 (4)（PDF 第 3 页）。本引理的投影是源态族，并未要求它们的和为恒等算子，也未将它们称为归一化 POVM。

对每个局部初始混合辅助态 $\eta_a$ 选择纯化 $|\alpha_a\rangle$，把纯化寄存器放入该持有者的不可访问因子。原辅助态的乘积性使这些纯化仍可取为持有者之间的乘积。根节点满足 $p_\varnothing=1$，且

$$
V_{a,\varnothing}x=x\otimes|\alpha_a\rangle,
\qquad L_\varnothing=\bigotimes_a V_{a,\varnothing}.
$$

这包括混合局部辅助态，且没有增加物理可访问资源。

在任一实际节点，对一个已声明结果 $y$ 的局部 CP 映射取有限 Kraus 表示

$$
\mathcal E_y(X)=\sum_kK_{y,k}XK_{y,k}^\dagger,
\qquad
B_yx=\sum_kK_{y,k}x\otimes|k\rangle.
$$

则

$$
\operatorname{Tr}_{k}(B_yXB_y^\dagger)=\mathcal E_y(X),
\qquad B_y^\dagger B_y=\sum_kK_{y,k}^\dagger K_{y,k}.
$$

新 $|k\rangle$ 因子只记入不可访问的膨胀输出，不宣布为测量结果。真正留供以后使用的私有量子或经典记忆属于 $\mathcal E_y$ 的可访问输出，不被当作垃圾移走。每次以后操作都张量上旧不可访问因子的恒等映射；部分迹与作用在可访问因子上的 CP 映射交换，故如此逐步保留全部垃圾、最后再迹掉，恰好重现原协议的顺序 CP 分支。被实际丢弃的系统不会在后续步骤重新成为控制资源。

现对树作归纳。设结论在正前缀 $h$ 成立，下一步由持有者 $a$ 操作。记

$$
\widehat B_y=B_y\otimes I_{\mathcal G_{a,h}},\qquad
E=V_{a,h}^\dagger\widehat B_y^\dagger\widehat B_yV_{a,h}
       \in\operatorname{Herm}(H_a),
$$

其中张量因子的重排只用于把新垃圾与旧垃圾放在同一不可访问因子。条件于共同标签 $i$ 和此前缀时，其他持有者的归一化编码因子都有单位范数，因此

$$
\langle s_{a,i}|E|s_{a,i}\rangle
 =\frac{p_{hy}}{p_h}=:q_{y\mid h},\qquad 0\le q_{y\mid h}\le1.
$$

假设使右侧与 $i$ 无关，局部算子事实给出 $E=q_{y\mid h}I_{H_a}$。这是拉回到原始源空间 $H_a$ 的效果等式，不断言物理效果在整个扩大后的可访问记忆空间上也是标量。

若 $q=q_{y\mid h}>0$，置

$$
V_{a,hy}=q^{-1/2}\widehat B_yV_{a,h},\qquad
V_{b,hy}=V_{b,h}\quad(b\ne a).
$$

直接计算 $V_{a,hy}^\dagger V_{a,hy}=q^{-1}E=I_{H_a}$，从而

$$
L_{hy}=\sqrt{p_hq}\bigotimes_bV_{b,hy}
      =\sqrt{p_{hy}}\bigotimes_bV_{b,hy}.
$$

若 $q=0$，则

$$
(\widehat B_yV_{a,h})^\dagger(\widehat B_yV_{a,h})=0,
\qquad \widehat B_yV_{a,h}=0.
$$

所以这一子分支在整个原始源空间上为零，其所有后继仍为零；这不要求 $\widehat B_y$ 在未占据的扩大空间上为零。只在正前缀作除法，每个零前缀都沿根到它的路径遇到一个这样的首次零子分支，因而无需给零前缀定义归一化映射。有限归纳覆盖全部节点，也覆盖重复访问、适应性改变操作方与不同终止深度。等距性质立即给出所述内积等式。证毕。

本引理中保留垃圾是必要的论证步骤。例如对量子比特和 $0<q\le1$，重置分支

$$
\mathcal E(X)=q\operatorname{Tr}(X)|0\rangle\langle0|
$$

的效果为 $\mathcal E^*(I)=qI$：由 $\operatorname{Tr}\mathcal E(X)=q\operatorname{Tr}X$ 可直接读出。但它把 $|0\rangle\langle0|$ 与 $|1\rangle\langle1|$ 送到相同输出，故约化 CP 映射不是缩放等距通道。保留膨胀 $B|\psi\rangle=\sqrt q\,|0\rangle\otimes|\psi\rangle$ 后，$B^\dagger B=qI$，除以 $\sqrt q$ 才得到等距映射；迹掉第二因子则还原重置分支。后续只操作第一个因子的权限并未因此扩大。

**定理 405.3（四态信息完备记录不能由有限局部树确定性精确恢复）。** 对每个固定正整数 $n\ge1$，定义 405.1 的任何有限局部协议都不能满足全部叶子的确定性精确恢复条件。此结论包括任意有限局部工作空间、粗粒化 CP 分支和反复访问；它只排除每个有限协议取得确定性精确恢复，不给出所有有限协议成功概率上确界的严格小于一界，也不给出近似恢复或无限轮次界。

证明。反设存在这样的协议。直接复用定理 390.2 的秩一 Choi 正性论证：对 $|\Omega\rangle=\sum_{i=1}^4|i\rangle\otimes|i\rangle$，各 $\mathfrak J(\mathcal T_w)\succeq0$ 之和等于 $|\Omega\rangle\langle\Omega|$，故存在

$$
\mathcal T_w=p_w\operatorname{id}_S,\qquad
p_w\ge0,\qquad \sum_wp_w=1.
$$

这包括 $p_w=0$ 的叶子。若终端标签已合并，先按定义 405.1 保留实际取得而后遗忘的经典历史，给这些历史使用原来相同的控制及反馈；对应 CP 分支仍为上述有限正分解的项。不把未观测 Kraus 标签加入历史。

对任意前缀 $h$，记 $w\succeq h$ 为延伸它的终端历史。剩余有限子树完整列出全部结果，非叶 instrument 的总和保迹，末端酉反馈也保迹。因此对任意正半定输入 $X$，前缀概率权重满足

$$
\begin{aligned}
\Pr(h\mid X)
 &=\sum_{w\succeq h}\operatorname{Tr}[\mathcal T_w(X)]
   =p_h\operatorname{Tr}X,\\
p_h&=\sum_{w\succeq h}p_w,\qquad
p_\varnothing=1,\qquad p_h=\sum_{y:\,hy\text{ 为子节点}}p_{hy}
       \quad(h\text{ 非叶}).
\end{aligned}
$$

对非归一化 $X$，$\Pr(h\mid X)$ 在此表示同一线性概率权重。这只是迹与概率的等式，不把前缀量子映射等同于使用不同末端反馈的叶子映射之和。若 $p_h>0$，$q_{y\mid h}=p_{hy}/p_h$ 与输入无关；若 $p_h=0$，全部后继叶子权重为零，实际准备输入上的正输出具有零迹，因而为零。不给零前缀定义条件概率。

特别取输入 $|i\rangle\langle i|$，各持有者的源态恰为共同标签 $i$ 下的 $r_i$。以通常的 Pauli 矩阵 $X,Y,Z$ 记局部算子，有

$$
P_1+P_2=I_2,\qquad P_1-P_2=Z,\qquad
2P_3-I_2=X,\qquad 2P_4-I_2=Y.
$$

$I_2,X,Y,Z$ 是 $\operatorname{Herm}(\mathbb C^2)$ 的实基，所以每位持有者的四个源投影都满足引理 405.2 的局部张成条件。它们是信息完备的态族，并不是四结果归一化 POVM。前缀概率的输入无关性给出该引理的另一个前提。于是在每个 $p_w>0$ 的叶子，保留的记录向量为

$$
\sqrt{p_w}\bigotimes_{a=1}^n V_{a,w}r_i.
$$

对系统矩阵单位 $E_{ij}=|i\rangle\langle j|$，迹掉全部可访问及不可访问的局部记录输出得到

$$
\begin{aligned}
\mathcal M_w(E_{ij})
 &=p_w\prod_{a=1}^n
      \langle V_{a,w}r_j|V_{a,w}r_i\rangle\,E_{ij}\\
 &=p_w\langle r_j|r_i\rangle^nE_{ij}.
\end{aligned}
$$

故 $\mathcal M_w=p_w\Phi_n$，其中 $\Phi_n(X)=C_0^{\circ n}\circ X$ 正是命题 400.2 的约化通道。保留下来的局部记忆和垃圾可能改变载体，却没有改变这些 Gram 系数。

有限个非负 $p_w$ 之和为一，至少有一个正叶子。由 $C_{0,12}=\langle1|0\rangle=0$ 和 $n\ge1$，该叶子满足

$$
\mathcal T_w(E_{12})=U_w\,0\,U_w^\dagger=0,
\qquad
p_w\operatorname{id}_S(E_{12})=p_wE_{12}\ne0,
$$

与叶子等式矛盾。$E_{12}$ 在此是检验线性映射的矩阵单位，不被主张为可单独准备的密度矩阵；全部态上的恢复等式线性延拓到全部矩阵，故这个检验合法。零深度树也有唯一正叶子，其反馈前映射就是 $\Phi_n$，受到同一矛盾约束。所有分支映射等式张量上 $\operatorname{id}_A$ 后仍成立，因而论证保持任意未操作参考及纠缠输入的量词。证毕。

分支无信息框架的来源是 Gregoratti–Werner，[*Quantum Lost and Found*, quant-ph/0209025v1](https://arxiv.org/abs/quant-ph/0209025v1)，§II.A（PDF 第 3 页）。该文 Theorem 1（第 4 页）允许对完整纯环境实现任意 CP 分解，Proposition 2（第 4–5 页）的标量效果判据针对单个 Kraus 算子；它们不直接提供这里受限记录访问下的有限树结论，也不使任意粗粒化 CP 映射成为等距通道。本定理的额外推导是：全部终端分支的无信息性经完整后继求和约束每个前缀，再由局部信息完备性保持源记录内积。

## 406. 两份局部记录的双结果后选择与信息完备性边界

**定理 406.1（相同局部投影基给出总成功概率三分之一）。** 在定义 405.1 的 $n=2$ 接口中，令 $s=\sqrt3$，并定义两个 bra

$$
\begin{aligned}
u&=\frac{(1-i)(1+s)}2,&
v&=\frac{(1-i)(1-s)}2,\\
\langle a|&=\frac{(1,u)}{\sqrt{3+s}},&
\langle b|&=\frac{(1,v)}{\sqrt{3-s}}.
\end{aligned}
$$

对应 ket 为 $|a\rangle=(|0\rangle+\bar u|1\rangle)/\sqrt{3+s}$ 与 $|b\rangle=(|0\rangle+\bar v|1\rangle)/\sqrt{3-s}$，其系数是上述 bra 系数的复共轭。两位持有者各自使用同一个二结果正交投影基 $\{|a\rangle,|b\rangle\}$。四个联合结果中，接受两个不同的相反结果 $(a,b)$ 与 $(b,a)$，均施加反馈

$$
U=\operatorname{diag}(1,-i,1,1).
$$

另两个结果 $(a,a)$ 与 $(b,b)$ 宣告失败。则每个接受结果的校正映射都是 $\operatorname{id}_S/6$，总接受映射是 $\operatorname{id}_S/3$。对任意有限参考 $A$ 和任意 $\rho_{AS}$，两个接受分支分别给出 $\rho_{AS}/6$，总接受输出为 $\rho_{AS}/3$。这是一个达到 $1/3$ 的构造，不是最优成功概率的断言。

证明。直接计算

$$
u+v=1-i,\qquad uv=i,\qquad u\bar v=-1,\qquad
|u|^2=2+s,\qquad |v|^2=2-s.
$$

因 $3\pm s>0$ 且 $(3+s)(3-s)=6$，有

$$
\langle a|a\rangle=\frac{1+|u|^2}{3+s}=1,\qquad
\langle b|b\rangle=\frac{1+|v|^2}{3-s}=1,\qquad
\langle a|b\rangle=\frac{1+u\bar v}{\sqrt6}=0.
$$

因此 $|a\rangle\langle a|+|b\rangle\langle b|=I_2$，双方投影的四个乘积结果之和为 $I_2\otimes I_2$，确实给出完整的有限局部 instrument。

对结果 $(a,b)$，按 $i=1,2,3,4$ 排列的四个源重叠为

$$
\begin{aligned}
\bigl(\langle a|r_i\rangle\langle b|r_i\rangle\bigr)_{i=1}^4
 &=\frac1{\sqrt6}
   \left(1,uv,\frac{(1+u)(1+v)}2,
                   \frac{(1+iu)(1+iv)}2\right)\\
 &=\frac1{\sqrt6}(1,i,1,1).
\end{aligned}
$$

最后两个分子的化简分别是

$$
\frac{1+(u+v)+uv}2
 =\frac{1+(1-i)+i}2=1,\qquad
\frac{1+i(u+v)-uv}2
 =\frac{1+i(1-i)-i}2=1.
$$

对另一个实际结果 $(b,a)$，第一张量因子使用 $\langle b|$、第二张量因子使用 $\langle a|$，从而直接得到

$$
\begin{aligned}
\bigl(\langle b|r_i\rangle\langle a|r_i\rangle\bigr)_{i=1}^4
 &=\frac1{\sqrt6}
   \left(1,vu,\frac{(1+v)(1+u)}2,
                   \frac{(1+iv)(1+iu)}2\right)\\
 &=\frac1{\sqrt6}(1,i,1,1).
\end{aligned}
$$

这是不同的正交结果；共同标签使两因子都为 $r_i$，标量乘法交换才使它们的四个振幅相同。

每个秩一乘积投影后的记录输出为固定单位向量 $|a\rangle\otimes|b\rangle$ 或 $|b\rangle\otimes|a\rangle$。所以迹掉记录后，系统的单 Kraus 算子分别为

$$
K_{ab}=K_{ba}=\frac1{\sqrt6}\operatorname{diag}(1,i,1,1),
\qquad UK_{ab}=UK_{ba}=\frac1{\sqrt6}I_4.
$$

于是对任意系统矩阵 $X$，

$$
UK_{ab}XK_{ab}^\dagger U^\dagger
 =UK_{ba}XK_{ba}^\dagger U^\dagger=\frac16X.
$$

张量上参考恒等映射并求和即得所述联合态公式，成功概率恒为 $1/3$，完整 instrument 的总失败概率恒为 $2/3$。

这两个失败结果也不能分别通过某个左侧系统酉反馈变成对全部输入的非零精确恢复分支。事实上，$K_{aa}^\dagger K_{aa}$ 在系统标签 $1,2$ 上的两个对角元为

$$
\frac1{(3+s)^2},\qquad \frac{(2+s)^2}{(3+s)^2},
$$

而 $K_{bb}^\dagger K_{bb}$ 的相应对角元为

$$
\frac1{(3-s)^2},\qquad \frac{(2-s)^2}{(3-s)^2}.
$$

两对都不相等。若左酉反馈把某一分支变成 $p\operatorname{id}_S$，对全部输入取迹便要求 $K^\dagger K=pI_4$；左乘酉算子不能改变这个效果，故不可能。

最后，若第一位持有者先测量，其结果 $a$ 在系统输入 $|1\rangle\langle1|$ 与 $|2\rangle\langle2|$ 下的前缀概率分别为

$$
\Pr(a\mid |1\rangle\langle1|)=\frac1{3+s},\qquad
\Pr(a\mid |2\rangle\langle2|)=\frac{2+s}{3+s}.
$$

它们不同。接受的两个叶子各自无信息，并不使含失败叶子的更早前缀无信息；定理 405.3 中的后继求和只有在整棵树全部叶子均精确校正时才给出输入无关权重。故本构造不满足该反证所需的确定性前提。证毕。

**命题 406.2（缺少局部算子张成时的单记录反例）。** 将定义 405.1 的第四个源向量改成 $\widetilde r_4=|{-}\rangle=(|0\rangle-|1\rangle)/\sqrt2$，其余三个不变，写相应记录制备为 $\widetilde J_1$。这四个源投影只张成 $\operatorname{span}_{\mathbb R}\{I_2,X,Z\}$，但一份记录已经允许两个结果的确定性精确恢复。因而仅有局部访问限制与记录族的非正交性，不足以推出定理 405.3 那样的障碍。

证明。前两个投影给出 $I_2,Z$，第三和第四个分别为 $(I_2+X)/2$ 与 $(I_2-X)/2$，所以张成空间恰为所述三维空间，不包含 $Y$。令唯一持有者测量正交基

$$
|y_\sigma\rangle=\frac{|0\rangle+\sigma i|1\rangle}{\sqrt2},
\qquad \sigma\in\{+1,-1\},\qquad
\langle y_\sigma|=\frac{(1,-\sigma i)}{\sqrt2}.
$$

两个向量的范数为一且彼此正交。它们与四个修改后源态的重叠为 $z_\sigma/\sqrt2$，其中

$$
z_\sigma=\left(1,-\sigma i,
                 \frac{1-\sigma i}{\sqrt2},
                 \frac{1+\sigma i}{\sqrt2}\right),
\qquad |(z_\sigma)_i|=1\quad(1\le i\le4).
$$

故系统分支 $K_\sigma=\operatorname{diag}(z_\sigma)/\sqrt2$ 经反馈 $U_\sigma=\operatorname{diag}(\overline{z_\sigma})$ 后满足 $U_\sigma K_\sigma=I_4/\sqrt2$，每个校正映射为 $\operatorname{id}_S/2$。两结果求和为恒等映射，与任意有限参考的联合态也被精确恢复。

这里的局部效果 $|y_\sigma\rangle\langle y_\sigma|=(I_2+\sigma Y)/2$ 并非标量，却对四个实坐标源态都具有期望 $1/2$；直接用上述重叠的模平方即可验证。引理 405.2 中从恒定期望推出标量拉回效果的步骤因此失去前提。原四态族内含非正交对，修改后的族也内含非正交对，但后者已有确定性协议，所以非正交性本身不能代替局部算子张成条件。此反例不主张信息完备性是每一种恢复障碍的必要条件，也不主张每个非信息完备记录族都可恢复。证毕。

**命题 406.3（同一制备的访问差别与未使用记录的剩余因子）。** 对定义 405.1 的任意输入 $\rho_{AS}$ 和 $n\ge1$，制备后的记录边缘态为

$$
\rho_R=\operatorname{Tr}_{AS}\rho_{ASR}
 =\sum_{i=1}^4(\rho_S)_{ii}P_i^{\otimes n},
\qquad \rho_S=\operatorname{Tr}_A\rho_{AS},
$$

因而在物理持有者分割下可分。对同一 $J_2$，命题 402.1 已给出联合四结果确定性恢复；定理 405.3 排除有限局部确定性精确恢复，而定理 406.1 给出局部总成功 $1/3$。这三项的差别属于制备后的记录访问与接受权限，输入维数及制备保持相同。

若 $n>2$，只对其中两份记录使用定理 406.1 的接受协议，并将其余 $n-2$ 份记录迹掉，则总接受映射为

$$
\frac13\Phi_{n-2},\qquad
\Phi_{n-2}(X)=C_0^{\circ(n-2)}\circ X,
$$

而不是 $\operatorname{id}_S/3$。

证明。将初态按系统基写成 $\rho_{AS}=\sum_{i,j}\rho^A_{ij}\otimes|i\rangle\langle j|$。制备后相应项为

$$
\rho^A_{ij}\otimes|i\rangle\langle j|
 \otimes|r_i^{\otimes n}\rangle\langle r_j^{\otimes n}|.
$$

对 $A,S$ 取迹只留下 $i=j$，其系数为 $\operatorname{Tr}\rho^A_{ii}=(\rho_S)_{ii}$。这些系数非负且总和为一，得到所示乘积态凸组合。这个偏迹计算没有测量 $i$，也没有让持有者知道 $i$。完整系统—记录态仍可纠缠：例如无参考的输入 $(|1\rangle+|2\rangle)/\sqrt2$ 被送到

$$
\frac{|1\rangle|0\rangle^{\otimes n}
      +|2\rangle|1\rangle^{\otimes n}}{\sqrt2},
$$

它在系统与记录之间有两个非零 Schmidt 系数。若保留参考，完整参考—系统—记录态也不受记录边缘可分性的无纠缠保证。按系统正交基受控制备记录，既不提供持有者之间额外共享的纠缠辅助态，也不授予制备完成后的联合恢复操作。

取 $n=2$，命题 402.1 在完整联合记录空间上以四个校正分支 $\operatorname{id}_S/4$ 实现确定恢复；其一般实现归属仍为命题 400.2。局部协议只能使用定义 405.1 的物理分割，故分别适用定理 405.3 与定理 406.1。这不主张四个结果是联合协议的最少结果数，也不主张 $1/3$ 是局部最优值。

对 $n>2$ 的剩余因子，在任意 $E_{ij}$ 上，每个相反接受结果及反馈从被测两记录贡献系数 $1/6$，另外每个未测记录的偏迹贡献 $\langle r_j|r_i\rangle=C_{0,ij}$。两个接受结果相加，得到

$$
E_{ij}\longmapsto\frac13(C_{0,ij})^{n-2}E_{ij}.
$$

线性延拓即为 $\Phi_{n-2}/3$，与任意参考张量恒等映射后仍成立。它仍以输入无关概率 $1/3$ 接受，但因 $n-2\ge1$，它将 $E_{12}$ 送至零，故不是 $\operatorname{id}_S/3$。物理丢弃未测记录恰好执行这个偏迹，不能消去剩余因子。证毕。

局部与联合辅助测量的既有比较可参见 Laustsen–Verstraete–van Enk，[*Local vs. joint measurements for the entanglement of assistance*, quant-ph/0206192v2](https://arxiv.org/abs/quant-ph/0206192v2)，PDF 第 1–3 页及 §3（第 7–8 页）。其目标为两个目标量子比特的平均 concurrence，主要局部结果限制于辅助方的 von Neumann 测量；该范围不等同于这里对全部四维未知输入、任意有限 CP instrument、私有记忆和重复访问的精确恢复。上述推导不扩展到无限、可数或连续结果协议、协议闭包、SEP 类或最优成功值，也不涉及定义 399.1 的整个张量输入任务、实际物理成本或新的 $n>2$ 局部恢复构造。

## 追加锚（本行以下为增补区）

## 407. 纯量子比特重复记录的正成功分支可由局部投影实现

**定义 407.1（任意系统维数下的局部乘积后选择）。** 取任意整数 $d,n\ge1$，系统为单个 $S=\mathbb C^d$，固定系统基 $\{|i\rangle\}_{i=1}^d$，已知归一化纯记录为 $r_i\in\mathbb C^2$。输入是 $S$ 上任意未知态，也可与任意有限维参考 $A$ 纠缠。按定义 400.1，先完成全部记录的制备：

$$
J_n|i\rangle=|i\rangle\otimes r_i^{\otimes n},\qquad
\mathcal H_R=(\mathbb C^2)^{\otimes n},\qquad
E_n=\operatorname{span}\{r_i^{\otimes n}:1\le i\le d\}.
$$

第 $a$ 位持有者只持有第 $a$ 个物理量子比特。$E_n$ 是占据的子空间，不授予新的局部张量分解或跨持有者压缩权限。制备之后不添加共享纠缠、联合记录测量或量子通信。每位持有者选择一个单位 ket $|a_a\rangle\in\mathbb C^2$，作两结果投影测量

$$
\{\Pi_a,I_2-\Pi_a\},\qquad \Pi_a=|a_a\rangle\langle a_a|,
$$

并报告经典结果。只接受所有持有者均取得第一个结果的分支；失败结果也属于完整测量。系统在记录测量期间不被操作，成功时只施加一个预先固定的终端对角酉算子 $U$，参考 $A$ 始终不被操作。投影和反馈可以依赖已知记录族及 $n$，不得依赖未知输入。

沿用定义 389.1 的 ket 行坐标：$C_{ij}=\langle r_j|r_i\rangle$；在 $E_n$ 的一组正交基中，$R_n$ 的第 $i$ 行是 $r_i^{\otimes n}$ 的坐标。由命题 400.2，

$$
R_nR_n^\dagger=C^{\circ n},\qquad
\operatorname{ran}(C^{\circ n})=\operatorname{ran}R_n.
$$

$\eta(C^{\circ n})$ 仍指第 390—391 节中允许完整联合记录测量的最优总成功量。局部接受映射 $\mathcal T$ 的精确恢复要求为 $\mathcal T=p\operatorname{id}_S$，其中 $0<p\le1$，等式在全部系统矩阵上成立，因而也须保持任意未操作参考及其与系统的纠缠。

**定理 407.2（正成功存在性的全局与局部等价）。** 对定义 407.1 的每个 $d,n$ 及记录族，有

$$
\eta(C^{\circ n})>0
\quad\Longleftrightarrow\quad
\text{存在定义 407.1 的局部乘积投影与反馈，使 }
\mathcal T=p\operatorname{id}_S\text{，其中 }p>0.
$$

右侧可用每位持有者各一次两结果投影测量实现，并对任意有限维 $A$ 及每个矩阵 $X_{AS}$ 满足

$$
(\operatorname{id}_A\otimes\mathcal T)(X_{AS})=pX_{AS}.
$$

证明。设左侧成立。定理 391.1 的支撑判据给出

$$
z\in\mathbb T^d\cap\operatorname{ran}R_n,\qquad z=R_nb.
$$

在上述 $E_n$ 坐标中，定义复线性泛函 $h_0(v)=\sum_\mu b_\mu v_\mu$，于是 $h_0(r_i^{\otimes n})=z_i$。它的表示 ket 的坐标为 $\overline{b_\mu}$，不能把 $b_\mu$ 本身误作该 ket 的坐标。因为 $d\ge1$ 且 $|z_i|=1$，$h_0\ne0$。由于 $E_n\subseteq\operatorname{Sym}^n(\mathbb C^2)$，令

$$
h=h_0\circ P_{E_n}:
\operatorname{Sym}^n(\mathbb C^2)\longrightarrow\mathbb C,
$$

其中 $P_{E_n}$ 是正交投影。这个延拓只用于构造泛函，不是协议中施加的物理投影；它保持所有指定记录上的值，且 $h\ne0$。

令 $e_s$ 为全部恰有 $s$ 个 $|1\rangle$ 的计算基 ket 之和除以 $\sqrt{\binom ns}$，$0\le s\le n$。这些向量是对称子空间的一组正交基，并且

$$
\begin{aligned}
(x|0\rangle+y|1\rangle)^{\otimes n}
 &=\sum_{s=0}^n\sqrt{\binom ns}\,x^{n-s}y^s e_s,\\
P(x,y)&:=h\bigl((x|0\rangle+y|1\rangle)^{\otimes n}\bigr)
 =\sum_{s=0}^n\sqrt{\binom ns}\,h(e_s)x^{n-s}y^s.
\end{aligned}
$$

若 $P$ 恒为零，各单项式系数都为零，便有所有 $h(e_s)=0$，与 $h\ne0$ 矛盾。因此 $P$ 是非零的 $n$ 次齐次二元多项式。写 $P(t,1)$ 的次数为 $m\le n$；此多项式也非零。复多项式因式分解给出非零首项系数 $c$ 及按重数列出的根 $\lambda_1,\ldots,\lambda_m$，使

$$
P(t,1)=c\prod_{a=1}^m(t-\lambda_a),\qquad
P(x,y)=c\,y^{n-m}\prod_{a=1}^m(x-\lambda_a y).
$$

第二式由齐次化得到，且是多项式恒等式，包含 $y=0$。当 $m=0$ 时空积为 $1$，得到 $P(x,y)=cy^n$；$y$ 的 $n-m$ 个因子保留了射影无穷远处的根。重复根照重数保留，$n=1$ 也包含在同一公式内。因此总能写成

$$
P(x,y)=c\prod_{a=1}^n\ell_a(x,y),\qquad
\ell_a(x,y)=\alpha_a x+\beta_a y\ne0.
$$

这里使用的是经典二元齐次因式分解，其对称量子比特张量形式可参见 Aulbach–Markham–Murao，[*Geometric Entanglement of Symmetric States and the Majorana Representation*, arXiv:1010.4777v1](https://arxiv.org/abs/1010.4777v1)，§IV 式 (11)（PDF 第 4 页）的复振幅恒等式。该文式 (12) 只给重叠的绝对值；此处所需的相对相位保留在上面的复多项式恒等式中。

对每个非零线性因子作实际测量所需的归一化：

$$
N_a=\sqrt{|\alpha_a|^2+|\beta_a|^2}>0,\qquad
|a_a\rangle=\frac{\overline{\alpha_a}|0\rangle+
                         \overline{\beta_a}|1\rangle}{N_a}.
$$

于是 $\langle a_a|(x|0\rangle+y|1\rangle)=\ell_a(x,y)/N_a$。在每个记录 $r_i$ 上取乘积，得到

$$
\begin{aligned}
t_i&:=\prod_{a=1}^n\langle a_a|r_i\rangle
 =\frac{h(r_i^{\otimes n})}{c\prod_{a=1}^nN_a}
 =\gamma z_i,\\
\gamma&:=\frac1{c\prod_{a=1}^nN_a}\ne0.
\end{aligned}
$$

此时才使用 $r_i$ 与 $a_a$ 的归一化和 $|z_i|=1$：各重叠的模不超过 $1$，所以

$$
0<|\gamma|=|t_i|=\prod_{a=1}^n|\langle a_a|r_i\rangle|\le1.
$$

给每位持有者使用定义 407.1 的两个投影。记 $Q_{a,0}=\Pi_a$、$Q_{a,1}=I_2-\Pi_a$，完整记录测量的结果为 $\varepsilon\in\{0,1\}^n$，投影为 $Q_\varepsilon=\bigotimes_{a=1}^nQ_{a,\varepsilon_a}$。全部 $2^n$ 个结果满足

$$
\sum_{\varepsilon\in\{0,1\}^n}Q_\varepsilon
 =\bigotimes_{a=1}^n\bigl(\Pi_a+(I_2-\Pi_a)\bigr)
 =I_{\mathcal H_R}.
$$

因各 $Q_\varepsilon$ 是投影，这也给出完整投影 instrument 的保迹性。接受 $\varepsilon=(0,\ldots,0)$ 时，记录的输出向量固定为 $|a_1\rangle\otimes\cdots\otimes|a_n\rangle$，具体为

$$
(I_S\otimes Q_{(0,\ldots,0)})J_n|i\rangle
 =t_i|i\rangle\otimes|a_1\rangle\otimes\cdots\otimes|a_n\rangle.
$$

故迹掉记录后的系统 Kraus 算子为 $K=\operatorname{diag}(t_1,\ldots,t_d)$。取固定对角反馈

$$
U=\operatorname{diag}(\overline{z_1},\ldots,\overline{z_d}),\qquad
UK=\gamma I_S,
$$

便在每个矩阵 $X$ 上得到

$$
\mathcal T(X)=UKXK^\dagger U^\dagger=pX,\qquad
p=|\gamma|^2\in(0,1].
$$

更直接地，$I_A\otimes UK=\gamma I_{A\otimes S}$，故对全部 $X_{AS}$ 都有所述等式。对归一化联合态取迹，成功概率恰为 $p$，与输入无关；归一化后恢复整个联合态。该计算同时保持非对角矩阵元，故并非只匹配系统基标签上的概率。

反过来，设存在这样的局部协议。令 $V:E_n\hookrightarrow\mathcal H_R$ 为包含等距映射，将其完整乘积测量压到实际占据空间：

$$
D_\varepsilon=V^\dagger Q_\varepsilon V\succeq0,\qquad
\sum_\varepsilon D_\varepsilon=I_{E_n}.
$$

在实际记录 $r_i^{\otimes n}$ 上，压缩前后效果的全部矩阵元相同，故各系统分支与原协议一致。它是定义 389.2 中作用于 $E_n$ 的允许全局 POVM；接受同一个结果并使用同一个反馈，便以概率 $p$ 精确恢复。因此 $\eta(C^{\circ n})\ge p>0$。这一比较没有改变局部协议中原有的物理张量因子。证毕。

本定理只等价化正成功分支的存在性，不保证保留某个给定全局分支的成功概率，也不声称局部与全局最优总成功概率相等。对一个给定全局 POVM 的各效果分别作上述构造，不由此得到同时完备的局部替代测量。每次构造都使用已制备的全部 $n$ 份记录。

## 408. 按记录射线数给出的逐次数充分界

**引理 408.1（归一化相关矩阵的余维一支撑含有相位向量）。** 设整数 $m\ge1$，$H\in\mathbb C^{m\times m}$ 满足

$$
H\succeq0,\qquad H_{ii}=1\quad(1\le i\le m),\qquad
\operatorname{rank}H\ge m-1.
$$

则

$$
\operatorname{ran}H\cap\mathbb T^m\ne\varnothing.
$$

证明。满秩时 $\operatorname{ran}H=\mathbb C^m$，结论立即成立。其余情形的秩为 $m-1$；$m=1$ 时归一化强制 $H=(1)$，故奇异情形必有 $m\ge2$。取分解 $H=RR^\dagger$，以 $r_i$ 记 $R$ 的第 $i$ 行 ket，则 $\|r_i\|^2=H_{ii}=1$。设 $\ker H=\operatorname{span}\{a\}$，$a\ne0$。由

$$
0=a^\dagger Ha=\|R^\dagger a\|^2
$$

得 $R^\dagger a=0$；逐坐标共轭后为

$$
\sum_{i=1}^m\overline{a_i}\,r_i=0.
$$

对每个 $j$，将第 $j$ 项移至一侧并取范数，得到长度平衡条件

$$
|a_j|\le\sum_{i\ne j}|a_i|.
$$

下面在此证明内展开所需的经典平面向量闭合判据。对任意有限列非负长度 $L_1,\ldots,L_s$，记总和为 $S$、最大值为 $M$，空列约定 $S=M=0$。可由复平面向量 $v_i$、$|v_i|=L_i$ 得到的合向量模长恰为

$$
\left\{\left|\sum_{i=1}^s v_i\right|:|v_i|=L_i\right\}
 =[\max(0,2M-S),S].
$$

从空列的集合 $\{0\}$ 开始归纳。设前一列的可达模长区间为 $[a,b]$，再加入长度 $t\ge0$。每个已有配置都可整体旋转；对已有合向量模长 $r\in[a,b]$，与新向量夹角 $\theta\in[0,\pi]$ 时的新模长为

$$
f(r,\theta)=\sqrt{r^2+t^2+2rt\cos\theta}.
$$

每个这样的值都可达到，而任意新配置的模长也在此像中。当 $r=0$ 或 $t=0$ 时，公式仍成立且不需要指定零向量的方向。矩形 $[a,b]\times[0,\pi]$ 紧且连通，连续函数 $f$ 的像是闭区间。其最大值为 $b+t$；对固定 $r$ 的最小值为 $|r-t|$，故全局最小值为

$$
\operatorname{dist}(t,[a,b])=\max(0,a-t,t-b).
$$

将 $a=\max(0,2M-S)$、$b=S$ 代入，此下端点为

$$
\begin{aligned}
\max(0,2M-S-t,t-S)
 &=\max\bigl(0,2\max(M,t)-(S+t)\bigr),
\end{aligned}
$$

上端点为 $S+t$，正是新总和与新最大值的公式，归纳完成。这同时包含零长度、全零列、零合向量以及平衡取等时的共线配置，不需要极限论证。

现在取 $L_i=|a_i|$。逐项平衡等价于 $2M\le S$，故上述区间包含 $0$。于是存在 $v_i\in\mathbb C$，满足

$$
|v_i|=|a_i|,\qquad \sum_{i=1}^m v_i=0.
$$

若 $a_i\ne0$，令 $z_i=v_i/\overline{a_i}$；若 $a_i=0$，则 $v_i=0$，任选 $|z_i|=1$。因此

$$
|z_i|=1\quad\text{对所有 }i,\qquad
 a^\dagger z=\sum_i\overline{a_i}z_i=\sum_i v_i=0.
$$

$H$ 为 Hermitian 矩阵，故 $\operatorname{ran}H=(\ker H)^\perp$，从而 $z\in\operatorname{ran}H\cap\mathbb T^m$。证毕。

归一化条件在此承担实质作用：任意余维一子空间并不必含相位向量。例如超平面 $\{z:z_1=0\}$ 与 $\mathbb T^m$ 不相交；它是正半定矩阵 $\operatorname{diag}(0,1,\ldots,1)$ 的值域，但该矩阵不满足全部对角元为 $1$。

**定理 408.2（不同记录射线数控制正局部恢复的充分次数）。** 在定义 407.1 的归一化纯量子比特记录族中，设不同复射影射线的个数为 $k$，即将相差单位相位的记录归为一类后共有 $k$ 类。对每一个整数

$$
n\ge\max(1,k-2),
$$

都存在定义 407.1 的完整局部乘积投影测量及终端对角反馈，其接受映射为 $p\operatorname{id}_S$，其中 $p\in(0,1]$，并保持任意有限维未操作参考。$p$ 与所选投影可依赖记录族及 $n$。这是充分界，不作一般最优阈值的断言。

证明。依定理 401.3 的射线相位约定，每类选单位代表 $q_j=(x_j,y_j)$，$1\le j\le k$，写

$$
r_i=u_iq_{c(i)},\qquad |u_i|=1.
$$

先在代表元上计算齐次评价的秩。设 $\mathscr B_n$ 为复系数 $n$ 次齐次二元多项式空间，其维数为 $n+1$，评价映射为

$$
\operatorname{ev}_n:\mathscr B_n\longrightarrow\mathbb C^k,\qquad
F\longmapsto(F(q_1),\ldots,F(q_k)).
$$

当 $n\ge k-1$ 时，定义线性式

$$
\Delta_\ell(x,y)=y_\ell x-x_\ell y,\qquad
h_j(x,y)=\overline{x_j}x+\overline{y_j}y.
$$

不同代表射线不共线，故 $\Delta_\ell(q_j)\ne0$ 对所有 $\ell\ne j$ 成立，而 $h_j(q_j)=1$。于是以下齐次插值多项式有定义且次数为 $n$：

$$
F_j(x,y)=h_j(x,y)^{\,n-k+1}
          \prod_{\ell\ne j}
          \frac{\Delta_\ell(x,y)}{\Delta_\ell(q_j)},\qquad
F_j(q_\ell)=\delta_{j\ell}.
$$

空积和零次幂均解释为常多项式 $1$，即便其底数在别处取零也不改变这个约定。这一构造不要求 $x_j$ 或 $y_j$ 非零，也没有选取共同仿射坐标图。评价映射因而满射，秩为 $k$。当 $n<k-1$ 时，在任意 $n+1$ 个代表上使用相同的次数 $n$ 构造，得到这部分评价的秩为 $n+1$；整个映射的秩至少为 $n+1$，又不能超过定义域维数，故也等于 $n+1$。

以对称子空间的正交基写各 $q_j^{\otimes n}$ 为行，得到矩阵 $Q_n$。定理 407.2 证明中的对称基展开说明：每个 $F\in\mathscr B_n$ 唯一对应一个复线性泛函 $h$，使 $F(x,y)=h((x|0\rangle+y|1\rangle)^{\otimes n})$；系数中的 $\sqrt{\binom ns}$ 均非零。因此 $\operatorname{ev}_n$ 与 $Q_n$ 表示同一个评价映射，得到

$$
\operatorname{rank}Q_n
 =\operatorname{rank}(Q_nQ_n^\dagger)
 =\min(k,n+1).
$$

这一步是经典齐次插值的应用。复制纯态的线性独立性界见 Chefles，[*Unambiguous Discrimination Between Linearly Dependent States With Multiple Copies*, quant-ph/0105016v3](https://arxiv.org/abs/quant-ph/0105016v3)，§II（PDF 第 3–5 页），尤其式 (2.8) 的量子比特条件 $N\le C+1$，对应这里的 $k\le n+1$。该来源讨论线性独立性与无歧义判别；这里不把独立性当作相干精确恢复的必要条件。

令 $H_n=Q_nQ_n^\dagger$，这是 $k\times k$ 的归一化代表 Gram 矩阵。若 $k\ge3$ 且 $n=k-2$，则 $n\ge1$、$\operatorname{rank}H_n=k-1$，引理 408.1 给出

$$
\tau\in\mathbb T^k\cap\operatorname{ran}H_n
       =\mathbb T^k\cap\operatorname{ran}Q_n.
$$

若 $n\ge k-1$，则 $H_n$ 满秩，同样可以选择这样的 $\tau$。这覆盖 $k\ge3$ 时的全部所述次数，也覆盖 $k=2$ 时的每个 $n\ge1$。写 $\tau=Q_nb$，以这些系数定义对称子空间上的复线性泛函 $h$，便有 $h(q_j^{\otimes n})=\tau_j$。提升回原始全部系统标签，令

$$
z_i=u_i^n\tau_{c(i)}.
$$

每个 $|z_i|=1$，并且由 $h$ 的线性性，

$$
h(r_i^{\otimes n})
 =h\bigl(u_i^n q_{c(i)}^{\otimes n}\bigr)
 =u_i^n\tau_{c(i)}=z_i.
$$

将 $h$ 限制到 $E_n$ 并写成其行坐标泛函，即得 $z\in\operatorname{ran}R_n$。于是定理 391.1 与定理 407.2 给出所需的正局部恢复。引理 408.1 仅施于 $k\times k$ 的代表矩阵；重复标签形成的 $d\times d$ 矩阵不需要满足余维至多一。

最后，若 $k=1$，则 $r_i=u_iq_1$。让每位持有者都取 $\langle a_a|=\langle q_1|$，全第一结果的幅度为 $t_i=u_i^n$，取 $U=\operatorname{diag}(\overline{u_1^n},\ldots,\overline{u_d^n})$ 即得 $UK=I_S$、$p=1$，适用于全部 $n\ge1$。各情形均对给定的 $n$ 单独构造并测量全部 $n$ 份记录，不借助成功概率关于 $n$ 的单调性，也不丢弃额外记录。证毕。

**推论 408.3（四射线阈值与单个族的非必要性）。** 对定义 392.1 的四记录族，定义 407.1 的正局部精确恢复存在当且仅当整数 $n\ge2$。另一方面，可有任意多条不同记录射线在 $n=1$ 时就有这样的正恢复：对任意有限 $k\ge1$，取模 $2\pi$ 两两不同的 $\theta_1,\ldots,\theta_k$，令

$$
r_j=\frac{|0\rangle+e^{i\theta_j}|1\rangle}{\sqrt2}.
$$

此族的一记录局部分支可以取成功概率 $1/2$。因此定理 408.2 的界对单个给定记录族未必是必要条件。

证明。四记录族有 $k=4$，故所有 $n\ge2$ 的存在性由定理 408.2 给出；$n=1$ 时定理 392.2 的 $\eta(C_0)=0$ 与定理 407.2 排除正局部分支。对赤道族，两个向量若共线，其相同的非零第一坐标迫使比例为 $1$，从而相位也相同，故确有 $k$ 条不同射线。取完整局部测量 $\{|0\rangle\langle0|,|1\rangle\langle1|\}$ 并只接受第一个结果，则每个 $\langle0|r_j\rangle=1/\sqrt2$，于是 $K=I_{\mathbb C^k}/\sqrt2$，反馈取恒等便有 $\mathcal T(X)=X/2$，张量任意参考后亦然。特别是 $k\ge4$ 时，$n=1<k-2$，这给出单个族中充分界非必要的实例；它不否定按所有记录族取最坏情形的界，四射线族本身已在 $k=4$ 达到阈值 $2$。证毕。

四记录族的正成功存在性与定理 405.3 对每个有限局部协议的确定性恢复排除相容，两者要求的总成功概率不同。

## 追加锚（本行以下为增补区）

## 409. 任意有限维纯记录的跨度界与指定相位方向的局部障碍

**定义 409.1（原始记录因子上的完整局部投影接口）。** 取整数 $d,q,n\ge1$，系统为单个 $S=\mathbb C^d$，固定系统正交基 $\{|i\rangle\}_{i=1}^d$，每份记录的物理空间为 $H=\mathbb C^q$。给定已知单位记录 $r_i\in H$，按定义 400.1 的受控制备，在测量之前完成全部 $n$ 份记录：

$$
J_n|i\rangle=|i\rangle\otimes r_i^{\otimes n},\qquad
\mathcal H_R=H^{\otimes n}.
$$

输入可以是 $S$ 上任意未知态，也可以与任意有限维参考 $A$ 纠缠；参考始终不被操作。每位持有者只持有一个原始 $H$ 因子，全部因子均被测量，不存在另一个未纳入模型的不可访问记录。制备之后不增加共享纠缠、量子通信、联合记录操作或系统—记录相干操作；记录测量期间不操作 $S$。

将记录按复射影射线分类，设共有 $k$ 类，选择单位代表 $s_1,\ldots,s_k$，并固定已知的校准相位及类别映射：

$$
r_i=u_i s_{c(i)},\qquad |u_i|=1,\qquad
c:\{1,\ldots,d\}\twoheadrightarrow\{1,\ldots,k\}.
$$

不同 $s_j$ 不共线。记实际单份记录跨度为

$$
E=\operatorname{span}_{\mathbb C}\{s_1,\ldots,s_k\}\subseteq H,
\qquad \varrho=\dim_{\mathbb C}E.
$$

因此 $1\le\varrho\le\min(q,k)$；$\varrho$ 不是环境维数 $q$，也不是张量幂记录的秩。$E$ 的使用只表述记录族的数学关系，不授予物理压缩或新的张量分解权限。

第 $a$ 位持有者选择单位 ket $|a_a\rangle\in H$，作完整两结果投影测量

$$
Q_{a,0}=|a_a\rangle\langle a_a|,\qquad
Q_{a,1}=I_H-Q_{a,0}\qquad(1\le a\le n).
$$

全部 $2^n$ 个联合结果均保留为测量结果，只接受全第一结果 $\varepsilon=(0,\ldots,0)$，成功时对 $S$ 施加一个固定的终端对角酉反馈 $U$。投影及反馈可以依赖已知记录族和实际次数 $n$，不得依赖未知输入。沿用定义 389.2 的恢复要求：接受映射 $\mathcal T$ 满足 $\mathcal T=p\operatorname{id}_S$，其中 $0<p\le1$，等式作用于全部系统矩阵，并须保持任意未操作参考。

**定理 409.2（实际跨度界与任意环境维数的正局部恢复）。** 在定义 409.1 的接口下，有以下两项充分条件。

第一，若 $k\ge2$，则对每一个实际整数次数

$$
n\ge k-\varrho+1
$$

都存在该接口允许的投影及反馈，使接受映射为 $\mathcal T=p\operatorname{id}_S$，其中 $p\in(0,1]$。若 $k=1$，则每个 $n\ge1$ 均可取 $p=1$。

第二，结合定理 408.2 的二维记录结论，对任意环境维数 $q$ 及每一个

$$
n\ge\max(1,k-2)
$$

也存在这样的正成功接受映射。第一项的跨度条件仍单独适用；特别是 $\varrho\ge4$ 时，其允许的次数可以小于第二项的界。

两项均在同一所选协议下，对任意有限维 $A$ 及全部 $X_{AS}\in\mathcal L(A\otimes S)$ 满足

$$
(\operatorname{id}_A\otimes\mathcal T)(X_{AS})=pX_{AS}.
$$

这里的 $p$ 及测量设置可依赖记录族和 $n$。这些结论不规定统一成功概率、渐近速率、鲁棒性、最优概率或最小次数，也不声称一般记录族可作确定性局部恢复。

证明。先证明第一项的 $k\ge2$ 情形，此时 $\varrho\ge2$。以 $H^\vee$ 表示复线性对偶，定义评价空间

$$
L=\left\{(\lambda(s_1),\ldots,\lambda(s_k)):
                \lambda\in H^\vee\right\}\subseteq\mathbb C^k,
\qquad \ell_j(v)=v_j\quad(v\in L).
$$

评价映射的核正是消去 $E$ 的泛函空间。任意 $E$ 上的泛函可延拓到 $H$，而在全部 $s_j$ 上为零的 $E$ 上泛函必为零，所以 $\dim L=\varrho$。每个 $s_j\ne0$，对偶可将其分离，故 $\ell_j\ne0$。如果 $\ell_i=c\ell_j$，则对所有 $\lambda\in H^\vee$ 都有 $\lambda(s_i-cs_j)=0$，于是 $s_i=cs_j$，与射线互异矛盾。因此这些坐标线性式两两不成比例。

设

$$
T=(\mathbb C^\times)^k,\qquad
g=\prod_{j=1}^k\ell_j\in\mathbb C[L],\qquad
X=L\cap T=\{v\in L:g(v)\ne0\}.
$$

各 $\ell_j$ 非零，$\mathbb C[L]$ 是整环，故 $g$ 是非零多项式。复数域无限，非零多项式不可能在整个 $L$ 上为零，因而 $X$ 非空；它也是 $L$ 中稠密的主开集。这就是这里所需的有限真超平面避免性质，同样适用于下文的任何有限维复子空间。

对 $v\in X$ 定义

$$
W(v)=\operatorname{diag}(v)^{-1}L\subseteq\mathbb C^k.
$$

每个 $W(v)$ 维数均为 $\varrho$。下面证明这些子空间共同张成 $\mathbb C^k$。使用复双线性配对 $\sum_j a_j b_j$，不在系数上取共轭。若 $a=(a_1,\ldots,a_k)$ 消去所有 $W(v)$，则对每个 $w\in L$ 及 $v\in X$ 有

$$
\sum_{j=1}^k a_j\frac{\ell_j(w)}{\ell_j(v)}=0.
$$

固定 $w$，清除分母得到在稠密开集 $X$ 上成立的多项式恒等式；因此它在全部 $L$ 上成立：

$$
\sum_{j=1}^k a_j\ell_j(w)
       \prod_{i\ne j}\ell_i(v)=0\qquad(v\in L).
$$

对指定的 $j$，超平面 $\ker\ell_j$ 的维数为 $\varrho-1\ge1$。若某个 $i\ne j$ 的 $\ell_i$ 在此超平面上恒为零，就有 $\ker\ell_j\subseteq\ker\ell_i$；两个非零线性式的核均余维一，这迫使它们成比例，已经排除。因此每个 $\ker\ell_j\cap\ker\ell_i$ 都是 $\ker\ell_j$ 中的真超平面。有限超平面避免给出

$$
b^{(j)}\in\ker\ell_j,\qquad
\ell_i(b^{(j)})\ne0\quad(i\ne j).
$$

再选 $w^{(j)}\in L$ 使 $\ell_j(w^{(j)})\ne0$。在上式代入 $v=b^{(j)}$、$w=w^{(j)}$，除第 $j$ 项外各项都含零因子 $\ell_j(b^{(j)})$，剩下

$$
a_j\ell_j(w^{(j)})\prod_{i\ne j}\ell_i(b^{(j)})=0.
$$

后两因子均非零，故 $a_j=0$。每个 $j$ 都如此，所以共同消去子的维数为零，有限维对偶给出

$$
\operatorname{span}_{v\in X}W(v)=\mathbb C^k.
$$

任选 $v_1\in X$，从维数 $\varrho$ 的 $W(v_1)$ 开始。如果已选子空间之和仍是 $\mathbb C^k$ 的真子空间，上面的张成等式保证存在另一个 $v\in X$，使 $W(v)$ 不包含在该和中；加入它至少使维数增加一。经过至多 $k-\varrho$ 次加入，便得到某个 $m\le k-\varrho+1$ 及

$$
v_1,\ldots,v_m\in X,\qquad
W(v_1)+\cdots+W(v_m)=\mathbb C^k.
$$

现在固定任意所述实际次数 $n\ge k-\varrho+1$。若 $m<n$，重复选择 $v_1$ 作为其余 $v_a$，上述子空间和仍满维。这里只补足用来检验微分秩的元组；尚未构造任何成功的物理分支。

考虑逐坐标乘法的正则映射

$$
F_n:X^n\longrightarrow T,\qquad
F_n(v_1,\ldots,v_n)_j=\prod_{a=1}^n\ell_j(v_a).
$$

因为 $X$ 是 $L$ 的开集，各点的切空间为 $L$。对方向 $w_1,\ldots,w_n\in L$，逐坐标求导给出

$$
\begin{aligned}
(dF_n)_{(v_1,\ldots,v_n)}(w_1,\ldots,w_n)_j
 &=\sum_{a=1}^n\ell_j(w_a)\prod_{b\ne a}\ell_j(v_b),\\
\operatorname{ran}(dF_n)_{(v_1,\ldots,v_n)}
 &=\operatorname{diag}(F_n(v_1,\ldots,v_n))
       \bigl(W(v_1)+\cdots+W(v_n)\bigr).
\end{aligned}
$$

在刚选的元组处，对角因子可逆，右侧为 $\mathbb C^k$。取导数的一个非零 $k$ 阶子式，固定其余局部坐标，由复逆函数定理，$F_n$ 的实际复数点像包含 $T$ 中一个非空欧氏开集。任何在这个像上为零的 Laurent 多项式都在该欧氏开集上为零，乘一个单项式清除负指数后，复多项式恒等定理迫使其恒为零。因此 $F_n$ 是支配映射，即其像的 Zariski 闭包为 $T$。

这里的切空间计算属于既有的 Hadamard 乘积几何；Bocci–Carlini–Kileel，[*Hadamard Products of Linear Spaces*, arXiv:1504.04301v2](https://arxiv.org/abs/1504.04301v2)，Lemma 2.12 给出了相应的射影切空间公式。数值界 $k-\varrho+1$ 也可由 Ballico，[*Projective Surfaces Not as Hadamard Products and the Dimensions of the Hadamard Joins*, arXiv:2408.12861v1](https://arxiv.org/abs/2408.12861v1)，Theorem 1.4 得到。为说明该引用的适用条件，在 $L$ 中取 $v_0\in X$，再取 $w$ 避开全部超平面

$$
\frac{\ell_i(w)}{\ell_i(v_0)}
 =\frac{\ell_j(w)}{\ell_j(v_0)}\qquad(i\ne j).
$$

这些等式的线性式非零，故这样的 $w$ 存在。直线 $Y=\mathbb P(\operatorname{span}\{v_0,w\})\subseteq\mathbb P(L)$ 上的各坐标线性式均非零、两两不成比例，在 $\mathbb P^1$ 上有两两不同的零点。因此 $Y$ 不包含于任何坐标超平面，并与坐标超平面的并相交。它也不包含于任何非零齐次二项式的零集：若两个坐标单项式在 $Y$ 上成比例，比较各个不同零点的消失阶数，就迫使每个坐标的指数相同，所得二项式只能是零多项式。于是 Ballico 的条件在这条分离直线上满足；从维数 $\varrho-1$ 的 $\mathbb P(L)$ 开始，每次与 $Y$ 作 Hadamard 乘积，闭包仍不可约且与坐标环面相交，维数增加一，直到 $k-1$。所需总因子数为 $1+(k-\varrho)$，而 $Y\subseteq\mathbb P(L)$；各向量因子又可乘任意非零标量，所以射影像稠密给出仿射环面中相同的支配性界。上面的直接微分论证独立给出了本处所用的支配性，不把这一已知几何界另立为新结论。

下一步必须从稠密闭包得到实际乘积值。将 $L$ 选坐标识别为 $\mathbb A^{\varrho}_{\mathbb C}$，则 $X=D(g)$ 是仿射主开集，其坐标环为 $\mathbb C[L][g^{-1}]$，是有限型复代数。$X^n$ 与 $T=\operatorname{Spec}\mathbb C[z_1^{\pm1},\ldots,z_k^{\pm1}]$ 均为仿射有限型复概形，$F_n$ 由上面的正则函数给出。源的坐标环在目标坐标环上仍有限生成；目标坐标环 Noetherian，所以这一环同态有限表示。仿射态射是拟紧的，故 $F_n$ 满足拟紧及局部有限表示两个条件。

由 Chevalley 定理（Stacks Project，[Tag 054K](https://stacks.math.columbia.edu/tag/054K)），其概形像为可构造集。$T$ 的 Laurent 坐标环是整环，故 $T$ 不可约；前述支配性说明该像稠密。不可约空间中的稠密可构造集包含非空 Zariski 开集 $O$（[Tag 005K](https://stacks.math.columbia.edu/tag/005K)）。具体地，将可构造集写成有限个局部闭集的并，其中至少一个在不可约的 $T$ 中稠密；它在自己的闭包中开，因而就是 $T$ 中的非空开集。

对每个 $z\in O(\mathbb C)$，纤维 $F_n^{-1}(z)$ 作为概形非空，而且是仿射有限型复概形。其坐标环是非零有限型复代数，取一个极大理想，由 Hilbert 零点定理（[Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)），剩余域是 $\mathbb C$ 的有限扩张；复数域代数闭，故剩余域就是 $\mathbb C$。这给出纤维中的实际复数点，因而

$$
O(\mathbb C)\subseteq F_n\bigl(X(\mathbb C)^n\bigr).
$$

最后，相位环面

$$
\mathbb T^k=\{z\in\mathbb C^k:|z_j|=1\text{ 对每个 }j\}
$$

在 $T$ 中 Zariski 稠密。事实上，若有限 Laurent 和 $P(z)=\sum_{\alpha\in\mathbb Z^k}c_\alpha z^\alpha$ 在此环面上为零，则对每个 $\beta\in\mathbb Z^k$，有限 Fourier 系数的正交性给出

$$
c_\beta=\frac1{(2\pi)^k}
 \int_{[0,2\pi]^k}
 P(e^{i\theta_1},\ldots,e^{i\theta_k})
 e^{-i\beta\cdot\theta}\,d\theta=0.
$$

故没有非零 Laurent 多项式能消去整个相位环面。于是 $O(\mathbb C)\cap\mathbb T^k\ne\varnothing$；取其中一个 $z$，便存在真正的 $n$ 个因子 $v_1,\ldots,v_n\in X$，满足

$$
\prod_{a=1}^n(v_a)_j=z_j,\qquad |z_j|=1\quad(1\le j\le k).
$$

这些因子是对固定的实际 $n$ 重新从 $F_n$ 的像中取得的，不是把较少记录上的成功幅度乘以未测量记录来延长协议。

按 $L$ 的定义，对每个 $v_a$ 选原始 $H$ 上的复线性泛函 $\lambda_a$，满足 $\lambda_a(s_j)=(v_a)_j$。因为所有这些值均非零，$\lambda_a\ne0$。在 $H$ 的正交基 $\{|e_\mu\rangle\}_{\mu=1}^q$ 中写

$$
\lambda_a\left(\sum_\mu x_\mu|e_\mu\rangle\right)
 =\sum_\mu c_{a\mu}x_\mu,\qquad
N_a=\|\lambda_a\|=\left(\sum_\mu|c_{a\mu}|^2\right)^{1/2}>0,
\qquad
|a_a\rangle=\frac1{N_a}\sum_\mu\overline{c_{a\mu}}|e_\mu\rangle.
$$

于是 $|a_a\rangle$ 是单位 ket，其 bra 正是 $\lambda_a/N_a$。这里共轭出现在表示 ket 的系数中；评价空间和清分母论证所用的复线性式没有变成共轭线性式。令 $N=\prod_aN_a$，则对每个代表 $s_j$，

$$
1=|z_j|=\prod_{a=1}^n|\lambda_a(s_j)|
 \le\prod_{a=1}^n\bigl(N_a\|s_j\|\bigr)=N.
$$

因此 $N\ge1$。对原始标签，所有第一结果的幅度为

$$
t_i=\prod_{a=1}^n\langle a_a|r_i\rangle
 =\frac{u_i^n z_{c(i)}}{N}.
$$

这些 ket 都直接属于每位持有者原有的 $H$；没有实施从 $H$ 到 $E$ 的压缩。用定义 409.1 的 $Q_{a,0},Q_{a,1}$ 构造 $Q_\varepsilon=\bigotimes_{a=1}^nQ_{a,\varepsilon_a}$。全部结果满足

$$
\sum_{\varepsilon\in\{0,1\}^n}Q_\varepsilon
 =\bigotimes_{a=1}^n(Q_{a,0}+Q_{a,1})=I_{H^{\otimes n}},
\qquad
Q_\varepsilon^\dagger Q_\varepsilon=Q_\varepsilon.
$$

故它们定义完整保迹的投影测量，失败结果也在其中。接受结果满足

$$
(I_S\otimes Q_{(0,\ldots,0)})J_n|i\rangle
 =t_i|i\rangle\otimes|a_1\rangle\otimes\cdots\otimes|a_n\rangle.
$$

这与定理 407.2 中的分支计算相同，且不依赖记录维数：迹掉输出记录后，系统 Kraus 算子为 $K=\operatorname{diag}(t_1,\ldots,t_d)$。取已知对角反馈

$$
U=\operatorname{diag}\bigl(\overline{u_1^n z_{c(1)}},\ldots,
                          \overline{u_d^n z_{c(d)}}\bigr),\qquad
UK=\frac1N I_S.
$$

于是对全部系统矩阵 $B$ 以及每个有限参考上的全部矩阵 $B_{AS}$，分别有

$$
\mathcal T(B)=UKBK^\dagger U^\dagger=\frac1{N^2}B,\qquad
(\operatorname{id}_A\otimes\mathcal T)(B_{AS})
 =(I_A\otimes UK)B_{AS}(I_A\otimes UK)^\dagger
 =\frac1{N^2}B_{AS}.
$$

故 $p=N^{-2}\in(0,1]$，对归一化联合态取迹即得与输入无关的成功概率；成功后归一化恢复整个联合态。所选投影及反馈仅由记录族和 $n$ 决定。

相同的数值条件在另一问题中已有明确来源：Chefles，[*Unambiguous Discrimination Between Linearly Dependent States With Multiple Copies*, quant-ph/0105016v3](https://arxiv.org/abs/quant-ph/0105016v3)，式 (2.3) 的 $N\le C+D-1$，在该文的态数、复制数、单份跨度分别取 $k,n,\varrho$ 时就是 $n\ge k-\varrho+1$。该式保证复制纯态族的线性独立性与无歧义判别；它本身不提供本接口中逐个原始记录因子的相干恢复测量。上述推导另外给出了实际乘积幅度、完整局部投影与全部未知系统输入的恢复等式，数值界本身不被视为新的界。

若 $k=1$，则 $r_i=u_i s_1$。令全部持有者取 $|a_a\rangle=s_1$，在各自原始 $H$ 上补足投影的正交补，便有 $t_i=u_i^n$。取 $U=\operatorname{diag}(\overline{u_1^n},\ldots,\overline{u_d^n})$，得到 $UK=I_S$，所以每个 $n\ge1$ 均有 $p=1$。这也覆盖 $q=1$；此时零的补投影仍是合法的失败效果。

再证明第二项，明确区分它与前面的支配性论证。当 $\varrho=1$ 时，所有非零记录共线，故 $k=1$，已由上段处理。当 $\varrho=2$ 时，选一个等距映射 $V:\mathbb C^2\to H$，其像为 $E$，令 $\widetilde r_i=V^\dagger r_i$。这些向量归一化且恰有同样的 $k$ 条射线。对给定的 $n\ge\max(1,k-2)$，定理 408.2 提供 $\mathbb C^2$ 上的单位测量 ket $|\widetilde a_a\rangle$、完整两结果投影及对角反馈。现在在原始 $H$ 中直接选择

$$
|a_a\rangle=V|\widetilde a_a\rangle,\qquad
\langle a_a|r_i\rangle=\langle\widetilde a_a|\widetilde r_i\rangle,
\qquad
V^\dagger(I_H-|a_a\rangle\langle a_a|)V
 =I_2-|\widetilde a_a\rangle\langle\widetilde a_a|.
$$

所得 ket 仍归一化；在整个 $H$ 上取各自补投影后仍是允许的完整测量。相同重叠给出相同的接受 Kraus 算子，配合同一反馈便有同一个 $p\operatorname{id}_S$，并保持全部参考。$V$ 在此只用来指定测量向量，没有先对物理记录实施 $V^\dagger$。这一情形直接复用定理 408.2，不由第一项的 $k-1$ 界推出。

当 $\varrho\ge3$ 时，$k\ge\varrho$，且

$$
1\le k-\varrho+1\le k-2.
$$

所以任何满足第二项的实际 $n$ 都满足第一项，应用已经构造的协议即可。若 $\varrho\ge4$，第一项还可覆盖 $k-\varrho+1\le n<k-2$ 的次数。所有情形都在给定 $J_n$ 上测量全部 $n$ 个原始记录因子。证毕。

**命题 409.3（同一两记录制备中，全局指定相位可达而单一乘积分支不可达）。** 取 $S=\mathbb C^5$、$H=\mathbb C^3$，在 $H$ 的正交基 $\{|x\rangle,|y\rangle,|z\rangle\}$ 下给定

$$
\begin{aligned}
s_1&=(0,1,1)/\sqrt2,&
s_2&=(0,1,-1)/\sqrt2,&
s_3&=(0,1,i)/\sqrt2,\\
s_4&=(1,0,1)/\sqrt2,&
s_5&=(1,0,-1)/\sqrt2.
\end{aligned}
$$

令 $r_i=s_i$，并固定同一制备 $J_2|i\rangle=|i\rangle\otimes s_i\otimes s_i$。这些记录有 $k=5$ 条不同射线，实际跨度 $\varrho=3$。指定

$$
z_\star=(1,1,1,1,-1),\qquad
U_\star=\operatorname{diag}(z_\star).
$$

在定义 389.2 所允许的全局记录测量下，单位 ket

$$
|b\rangle=\frac{|x\rangle\otimes|z\rangle+
                      |z\rangle\otimes|x\rangle+
                   2|y\rangle\otimes|y\rangle}{\sqrt6}
$$

及其投影的正交补组成完整两结果测量；只接受 $|b\rangle\langle b|$ 并施加 $U_\star$，接受映射为 $\operatorname{id}_S/6$。相反，没有任何单一非零乘积 bra 分支能在这个固定反馈 $U_\star$ 下给出 $p\operatorname{id}_S$、$p>0$。然而，同一 $J_2$ 上的两位持有者都选单位 bra $(1,1,0)/\sqrt2$，各自补全两结果投影，只接受两个第一结果并取恒等反馈，就得到 $\operatorname{id}_S/16$。两项正恢复等式均作用于全部系统矩阵及任意有限维未操作参考。

证明。每个 $s_j$ 恰有两个模为 $1/\sqrt2$ 的非零坐标，故范数为一。前三个向量的 $x$ 坐标为零、$y$ 坐标相同且非零，而 $z/y$ 依次为 $1,-1,i$，因此它们两两不共线。后两个向量的 $x$ 坐标非零、$y$ 坐标为零，不能与前三者共线；其 $z/x$ 分别为 $1,-1$，所以它们也不同线。并且

$$
\frac{s_1+s_2}{\sqrt2}=|y\rangle,\qquad
\frac{s_1-s_2}{\sqrt2}=|z\rangle,\qquad
\frac{s_4+s_5}{\sqrt2}=|x\rangle,
$$

从而跨度为三。

写任意 ket 的坐标为 $v=x|x\rangle+y|y\rangle+z|z\rangle$，这里 $x,y,z$ 为复标量。上述 $|b\rangle$ 的三个基分量两两正交，范数平方为 $(1+1+4)/6=1$；其系数为实数，故

$$
\langle b|v\otimes v\rangle
 =\frac{2xz+2y^2}{\sqrt6}
 =\frac{P_0(x,y,z)}{\sqrt6},\qquad
P_0(x,y,z)=2(xz+y^2).
$$

代入五个单位记录，前三者均由 $2y^2=1$ 得到值 $1$，后两者由 $2xz=\pm1$ 得到值 $1,-1$，于是 $P_0(s_j)=(z_\star)_j$。完整联合测量为

$$
\{|b\rangle\langle b|, I_{H\otimes H}-|b\rangle\langle b|\}.
$$

其接受分支在迹掉记录后给出 $K_\star=\operatorname{diag}(z_\star)/\sqrt6$。因 $U_\star K_\star=I_S/\sqrt6$，对每个矩阵 $B$ 有 $U_\star K_\star B K_\star^\dagger U_\star^\dagger=B/6$；张量 $I_A$ 后同样对每个 $B_{AS}$ 给出 $B_{AS}/6$。全局测量使用了联合记录权限，不属于定义 409.1 的局部权限。

现在设一个乘积 bra 的两个复线性式为

$$
\lambda(v)=\alpha^T v,\qquad
\mu(v)=\beta^T v,\qquad
t_j=\lambda(s_j)\mu(s_j),\qquad K=\operatorname{diag}(t_1,\ldots,t_5).
$$

任何整体非零比例都可吸收入其中一个线性式，因此这也覆盖未归一化的非零乘积 bra。假设固定反馈满足

$$
U_\star K B K^\dagger U_\star^\dagger=pB
\quad\text{对全部 }B,\qquad p>0.
$$

记 $D=U_\star K=\operatorname{diag}(d_1,\ldots,d_5)$。对矩阵单位 $E_{jj}$ 应用此式，得 $|d_j|^2=p$，故每个 $d_j$ 非零；再对 $E_{j1}$ 应用，得 $d_j\overline{d_1}=p=d_1\overline{d_1}$，因而全部 $d_j=d_1$。于是存在 $\gamma=d_1\ne0$，使

$$
U_\star K=\gamma I_S,\qquad
t_j=\gamma(z_\star)_j\quad(1\le j\le5).
$$

下面求五个记录上的二次齐次评价映射的核。取

$$
Q(x,y,z)=A x^2+B y^2+C z^2+D_0xy+E_0xz+F_0yz.
$$

若全部 $Q(s_j)=0$，由前三个值依次得到

$$
B+C+F_0=0,\qquad B+C-F_0=0,\qquad B-C+iF_0=0.
$$

前两式给出 $F_0=0$、$B+C=0$，第三式给出 $B-C=0$，故 $B=C=0$。后两个值给出 $A+C+E_0=0$、$A+C-E_0=0$，因而 $A=E_0=0$。只有 $D_0$ 可自由取值；反过来，全部记录都有 $xy=0$，故 $xy$ 确在核中。因此

$$
\ker\bigl(Q\longmapsto(Q(s_1),\ldots,Q(s_5))\bigr)
 =\operatorname{span}_{\mathbb C}\{xy\}.
$$

由 $P_0(s_j)=(z_\star)_j$，任何满足 $Q(s_j)=\gamma(z_\star)_j$ 的二次式都必须具有形式

$$
Q(x,y,z)=2\gamma(xz+y^2)+txy,\qquad t\in\mathbb C.
$$

它的复对称系数矩阵以及行列式为

$$
M_Q=\begin{pmatrix}
0&t/2&\gamma\\
t/2&2\gamma&0\\
\gamma&0&0
\end{pmatrix},\qquad
Q(v)=v^T M_Qv,\qquad
\det M_Q=-2\gamma^3\ne0.
$$

但若 $Q(v)=\lambda(v)\mu(v)=(\alpha^T v)(\beta^T v)$，它的对称系数矩阵为

$$
M_Q=\frac{\alpha\beta^T+\beta\alpha^T}{2},\qquad
\operatorname{ran}M_Q\subseteq\operatorname{span}\{\alpha,\beta\},
$$

故秩至多为二，与上面的非零三阶行列式矛盾。这里的 $T$ 始终是代数转置；二次多项式的系数计算不使用 Hermitian 配对。因此固定的 $U_\star$ 不能校正任何这样的正成功乘积分支。

最后令两位持有者的单位 ket 都为 $|a\rangle=(|x\rangle+|y\rangle)/\sqrt2$，相应 bra 的坐标就是 $(1,1,0)/\sqrt2$。对五个记录逐个代入，前三者由 $y$ 坐标、后两者由 $x$ 坐标给出

$$
\langle a|s_j\rangle=\frac12\quad(1\le j\le5),\qquad
\langle a\otimes a|s_j\otimes s_j\rangle=\frac14.
$$

每位持有者均作 $\{\Pi,I_H-\Pi\}$，其中 $\Pi=|a\rangle\langle a|$。全部四个结果的投影为

$$
\Pi\otimes\Pi,\quad
\Pi\otimes(I_H-\Pi),\quad
(I_H-\Pi)\otimes\Pi,\quad
(I_H-\Pi)\otimes(I_H-\Pi),
$$

其和为 $I_{H\otimes H}$。只接受第一个结果，得到 $K=I_S/4$；取恒等反馈，对任意 $B$ 得到 $B/16$，对任意 $B_{AS}$ 得到 $B_{AS}/16$。两份已制备记录均实际参加测量，且设置与未知输入无关。证毕。

此命题排除的是指定相位方向及固定反馈下的单一乘积 bra 分支，未排除其他相位方向的正局部恢复，也未给出所有局部协议或所有有限轮局部操作与经典通信协议的障碍。所展示的 $1/6$ 与 $1/16$ 都是取得的分支概率，不作最优性比较。本例 $n=2<k-\varrho+1=3$，也低于定理 409.2 第二项的充分界；它不构成这些界尖锐或必要的断言。存在某个可恢复的局部相位方向，与能否实现一个预先指定的全局相位方向，是两个不同的要求。

## 追加锚（本行以下为增补区）

## 410. 记录射线亏量控制逐次数的正局部恢复

**定理 410.1（亏量充分界与亏量二的最坏情形）。** 沿用定义 409.1 的完整局部投影接口。对任意给定的已知单位纯记录族 $r_1,\ldots,r_d\in H=\mathbb C^q$，以 $s_1,\ldots,s_k$ 表示不同射线的单位代表，将该定义中的类别映射记为 $\kappa$，并记

$$
r_i=u_i s_{\kappa(i)},\qquad |u_i|=1,\qquad
\kappa:\{1,\ldots,d\}\twoheadrightarrow\{1,\ldots,k\},
\qquad E=\operatorname{span}_{\mathbb C}\{s_j\}_{j=1}^k,
\qquad h=\dim_{\mathbb C}E,\qquad c=k-h.
$$

这里 $h$ 是实际单份记录跨度，$c$ 是射线数相对于该跨度的亏量。对每一个实际整数次数

$$
n\ge\max(1,c),
$$

都存在原始 $H$ 因子上的单位测量 ket $|a_1\rangle,\ldots,|a_n\rangle$ 及校准的终端对角酉反馈 $U$，使全部 $n$ 位持有者各作一次完整的投影／补投影测量、只接受全第一结果时，接受映射满足

$$
\mathcal T(B)=pB\quad\text{对全部 }B\in\mathcal L(S),\qquad
0<p\le1.
$$

同一协议对每个有限维未操作参考 $A$ 和每个 $B_{AS}\in\mathcal L(A\otimes S)$ 都满足

$$
(\operatorname{id}_A\otimes\mathcal T)(B_{AS})=pB_{AS}.
$$

投影、反馈与 $p$ 可以依赖给定记录族和实际 $n$，不依赖未知系统输入或其与参考的联合态。制备仍为同一个系统上的 $J_n|i\rangle=|i\rangle\otimes r_i^{\otimes n}$，每个原始记录因子均被测量，失败结果也保留在完整 instrument 中；其余访问与操作权限仍按定义 409.1。若 $k=1$，每个 $n\ge1$ 均可取 $p=1$。

作为同一定理的第二项，对每个 $h\ge2$，存在 $k=h+2$ 条不同单位记录射线、跨度恰为 $h$ 的族，在此接口下没有正成功的一记录接受分支，而两记录已有这样的分支。因此 $2$ 是亏量 $c=2$ 时对所有记录族统一保证存在性的最坏情形阈值；这不表示每个亏量二的族都需要两份记录。

证明。先在代表射线上构造 $n$ 个非零复线性泛函，使其乘积评价具有同一个正模长，再完成原始空间上的测量。复线性评价空间、坐标线性式与坐标秩记为

$$
\begin{aligned}
L&=\{(\lambda(s_1),\ldots,\lambda(s_k)):\lambda\in H^\vee\}
       \subseteq\mathbb C^k,\qquad \ell_j(v)=v_j,\\
r(B)&=\dim_{\mathbb C}\operatorname{span}\{s_j:j\in B\}
       \quad(B\subseteq[k]),\qquad [k]=\{1,\ldots,k\}.
\end{aligned}
$$

定理 409.2 的对偶分离论证在这里给出 $\dim L=h$：评价的核消去全部 $E$，而每个 $E$ 上的泛函均可延拓到 $H$。每个 $\ell_j$ 非零，且两个不同坐标式不成比例，否则对全部泛函评价会迫使两个代表共线。因此坐标拟阵无环且简单，$r(\{j\})=1$，秩一的非空块只能是单点。以下不要求记录族一般位置。

令 $G=(\mathbb C^\times)^k$、$X=L\cap G$。有限个非零坐标线性式之积非零，故 $X$ 是 $L$ 中非空稠密主开集。这里的代数环面 $G$ 与单位相位环面 $\mathbb T^k=(S^1)^k$ 有别，不假设 $X\cap\mathbb T^k$ 非空。

先设 $c\ge2$，从二因子乘积的闭包维数分析记录的关系。以 $v\circ w$ 表示逐坐标乘积，令

$$
Y=\overline{\{v\circ w:v,w\in L\}}^{\mathrm{Zar}}
       \subseteq\mathbb C^k,\qquad s=\dim Y.
$$

$s$ 是像闭包的代数簇维数，并非这些乘积向量的线性张成维数。Bernstein，[*Generic symmetry-forced infinitesimal rigidity: translations and rotations*, arXiv:2003.10529v4](https://arxiv.org/abs/2003.10529v4)，Theorem 3.1，以及 Antolini–Dewar–Tanigawa，[*Dilworth truncations and Hadamard products of linear spaces*, arXiv:2508.04798v1](https://arxiv.org/abs/2508.04798v1)，Theorems 1.1、2.7 的式 (3)–(4)，给出所需的二因子代数拟阵与秩公式。此处代入 $L_1=L_2=L$、$r_1=r_2=r$；两个因子各自的参数独立变化，不把乘法映射限制为 $v\mapsto v\circ v$。

具体地，诱导拟阵的独立集 $I\subseteq[k]$ 满足

$$
|J|\le2r(J)-1\qquad\text{对每个非空 }J\subseteq I.
$$

不对空集施加该不等式；$2r-1$ 是诱导秩的集合函数，本身不是所得拟阵的秩函数。上述式 (4) 中允许留下 $F_0\subseteq[k]$，其代价为 $|F_0|$，并把其余元素分成非空块。因为每个单点的代价为 $2r(\{j\})-1=1$，可将 $F_0$ 的每个元素换成一个单点块；反过来取 $F_0=\varnothing$ 即包含全部非空块分拆。因此全地集的秩，也就是 $s$，为

$$
s=\min_{\mathcal P}\sum_{B\in\mathcal P}(2r(B)-1),
$$

其中 $\mathcal P$ 遍历 $[k]$ 的非空块分拆。非空约定取上述 Theorem 2.7 式 (3) 的明确形式；它避免将 Bernstein Definition 2.6 中未显写的这一限定误用于空集。

对任一分拆，记 $R=\sum_{B\in\mathcal P}r(B)$、$m=|\mathcal P|$。各块共同张成 $E$，故 $R\ge h$，而各块非空无环，故 $m\le R$。其代价为

$$
2R-m\ge R\ge h.
$$

若代价为 $h$，则 $R=m=h$，所有块秩一；简单性迫使它们全为单点，因而 $k=h$，与 $c\ge2$ 矛盾。所以 $s\ge h+1$。若 $s=h+1$，取达到最小值的分拆，写 $R=h+a$、$a\ge0$，则

$$
m=h+2a-1\le R=h+a,\qquad a\le1.
$$

$a=1$ 会给出 $m=R=h+1$，全部块又是秩一单点，从而 $k=h+1$，仍与 $c\ge2$ 矛盾。故 $a=0$、$R=h$、$m=h-1$。于是

$$
\sum_{B\in\mathcal P}(r(B)-1)=R-m=1,
$$

恰有一个秩二块，其余 $h-2$ 个块均为单点。秩二块含 $k-(h-2)=c+2$ 条不同射线。各块跨度之和为 $E$，维数之和又等于 $\dim E=h$，故从各块跨度的外直和到 $E$ 的求和映射既满射又等维，核为零。重新排列代表后，得到

$$
E=P\oplus\mathbb C s_{c+3}\oplus\cdots\oplus\mathbb C s_k,
\qquad
P=\operatorname{span}\{s_1,\ldots,s_{c+2}\},\qquad \dim P=2.
$$

因此 $c\ge2$ 时，或者 $s\ge h+2$，或者全部记录具有上述平面加独立补空间的形式。后者是代数直和，可以不正交；它只约束记录关系，不授予物理压缩权限。这里的关键联系是：二因子增长只达到 $h+1$ 时，记录恰被迫落入可由二维恢复处理的互补结构。

在 $s\ge h+2$ 的情形，先选实际的最大秩二因子点。Antolini–Dewar–Tanigawa Definition 3.1 后的 Jacobian 表示及 Proposition 3.2，在复数域上将多项式像闭包的维数识别为一般点处的微分秩。应用于 $L\times L\to\mathbb C^k$ 的逐坐标乘法，其最大秩为 $s$；秩达到 $s$ 的非空开集与不可约空间 $L^2$ 中的稠密开集 $X^2$ 相交。因此存在实际复数点 $(v_1,v_2)\in X^2$，满足

$$
\operatorname{rank}(dF_2)_{(v_1,v_2)}=s,
\qquad F_2(v_1,v_2)=v_1\circ v_2.
$$

即使 $L_1=L_2$，该选择仍在两个独立参数空间中作出；一般性只选择因子元组，不限制给定记录族。沿用定理 409.2 的对数切空间记法和已经给出的微分恒等式，

$$
\begin{aligned}
W(v)&=\operatorname{diag}(v)^{-1}L\quad(v\in X),\\
\operatorname{ran}(dF_t)_{(v_1,\ldots,v_t)}
 &=\operatorname{diag}(F_t(v_1,\ldots,v_t))
       \bigl(W(v_1)+\cdots+W(v_t)\bigr),\\
\operatorname{span}_{v\in X}W(v)&=\mathbb C^k.
\end{aligned}
$$

最后一个等式适用，因为 $h\ge2$ 且坐标线性式非零、两两不成比例，正是定理 409.2 清分母并在单个坐标超平面上分离各项的条件。二因子点的可逆对角因子给出 $\dim(W(v_1)+W(v_2))=s$。只要当前和还不是 $\mathbb C^k$，共同张成等式就提供一个不包含在当前和内的 $W(v)$；每次加入至少增维一。至多再加入 $k-s$ 个因子，便有某个 $m$ 满足

$$
W(v_1)+\cdots+W(v_m)=\mathbb C^k,
\qquad m\le2+k-s\le k-h=c.
$$

现在固定所要处理的实际 $n\ge c$。用任意 $X$ 中的点补足至 $n$ 个切向元组参数，上述和保持满维。正则映射

$$
F_n:X^n\longrightarrow G,\qquad
F_n(v_1,\ldots,v_n)_j=\prod_{a=1}^n(v_a)_j
$$

因而在某个实际点具有满秩微分。由定理 409.2 的复逆函数论证，它的实际像含非空欧氏开集，故 $F_n$ 支配 $G$。补足的是微分元组，此时没有把一个较短的成功物理分支延长。

为从此处得到实际相位乘积，应用定理 409.2 证明中的像与纤维论证。仍令 $g=\prod_j\ell_j$，则 $X=D(g)$ 的坐标环为 $\mathbb C[L][g^{-1}]$，$X^n$ 与 $G=\operatorname{Spec}\mathbb C[z_1^{\pm1},\ldots,z_k^{\pm1}]$ 均为仿射有限型复概形。源坐标环在目标坐标环上有限生成，而目标坐标环 Noetherian，故该环同态有限表示；仿射态射拟紧，所以 $F_n$ 拟紧且局部有限表示。Chevalley 定理（Stacks Project，[Tag 054K](https://stacks.math.columbia.edu/tag/054K)）给出可构造概形像；其支配性与 $G$ 的不可约性使像包含非空 Zariski 开集 $O$（[Tag 005K](https://stacks.math.columbia.edu/tag/005K)）。

对任意 $z\in O(\mathbb C)$，纤维 $F_n^{-1}(z)$ 是非空仿射有限型复概形。其坐标环为非零有限型复代数，取极大理想后，Hilbert 零点定理（[Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)）给出有限扩张剩余域；由于 $\mathbb C$ 代数闭，此域就是 $\mathbb C$，从而纤维确有实际复数点。因此 $O(\mathbb C)$ 包含于实际复数点像，而不仅包含于像的闭包。定理 409.2 的有限 Laurent 和／Fourier 系数论证给出 $\mathbb T^k$ 在 $G$ 中 Zariski 稠密，于是可取

$$
z\in O(\mathbb C)\cap\mathbb T^k,\qquad
w_1,\ldots,w_n\in X,\qquad
F_n(w_1,\ldots,w_n)=z.
$$

这里的 $w_1,\ldots,w_n$ 是对当前 $n$ 重新从实际纤维取得的因子，不要求等于前面用于微分满秩的元组。按 $L$ 的定义选取原始 $H$ 上的泛函 $\lambda_a$，使 $\lambda_a(s_j)=(w_a)_j$，便有

$$
\prod_{a=1}^n\lambda_a(s_j)=z_j,
\qquad |z_j|=1.
$$

每个泛函均非零。此情形得到的原始乘积共同模长为 $\gamma=1$。整个推导只使用二因子拟阵公式；补足更多因子使用的是子空间增维与实际像论证，没有使用一般多因子秩公式。

再处理代数直和的例外情形。对每个实际 $n\ge c=(c+2)-2$，将 $P$ 取正交坐标识别为 $\mathbb C^2$，对其中 $c+2$ 个单位代表应用定理 408.2。其构造提供 $n$ 个非零平面复线性泛函 $\mu_1,\ldots,\mu_n$，使

$$
\prod_{a=1}^n\mu_a(s_j)=\gamma z_j
\quad(1\le j\le c+2),\qquad
\gamma>0,\qquad |z_j|=1.
$$

可直接取该二维协议的单位 bra，$\gamma$ 就是其共同乘积模长；相位全部放入 $z_j$。现在将这 $n$ 个泛函中的每一个都延拓到上述代数直和 $E$，在每个补空间的单位代表上规定

$$
\widetilde\mu_1(s_j)=\gamma,\qquad
\widetilde\mu_a(s_j)=1\quad(2\le a\le n),
\qquad c+3\le j\le k,
\qquad \widetilde\mu_a|_P=\mu_a.
$$

直和性保证这些指定值与平面限制同时唯一确定 $E$ 上的线性泛函。若 $h=2$，补空间为空，指定值的条件为空。各补代表上的乘积正是 $\gamma$；置其 $z_j=1$，全部 $k$ 个代表便共享同一个正模长。将每个 $\widetilde\mu_a$ 再延拓到原始 $H$，例如取 $\lambda_a=\widetilde\mu_a\circ P_E$，其中 $P_E:H\to E$ 是数学上的正交投影。所有 $\lambda_a$ 非零，且保持指定评价。该延拓并非协议里实施的投影；$E$ 内的各直和分量不必正交。测量的归一化必须等到这全部 $n$ 次延拓之后，用各泛函在原始 $H$ 上的范数完成。

余下 $c=0,1$ 的情形直接复用引理 408.1 的归一化支撑结论。在 $E$ 的一组正交基中，将单位 ket $s_j$ 的坐标作为矩阵 $R$ 的第 $j$ 行。沿用定义 389.1 的行坐标约定，

$$
L=\operatorname{ran}R=\operatorname{ran}(RR^\dagger),\qquad
(RR^\dagger)_{jj}=1,\qquad
\operatorname{rank}(RR^\dagger)=h=k-c\ge k-1.
$$

于是存在 $\zeta\in\operatorname{ran}R\cap\mathbb T^k$。写 $\zeta=Rb$，取 $E$ 上的复线性式 $\lambda_0(x)=\sum_\mu b_\mu x_\mu$ 并延拓到 $H$，便有 $\lambda_0(s_j)=\zeta_j$。这里表示 ket 的系数须取 $\overline{b_\mu}$；$R$ 的行没有改成 bra 坐标。令 $N_0=\|\lambda_0\|_H>0$，则 $\lambda_0/N_0$ 是同一个单位 bra，所有代表的重叠模长均为 $1/N_0$。对每个实际 $n\ge1$，在全部因子上重复使用这个相同 bra：在未归一化记法中令所有 $\lambda_a=\lambda_0$，即有

$$
\prod_{a=1}^n\lambda_a(s_j)=\zeta_j^n,
\qquad \gamma=1,\qquad z_j=\zeta_j^n\in S^1.
$$

这给出逐次数的具体构造，不依赖成功概率的单调性。若 $k=1$，进一步直接取 $\lambda_0=\langle s_1|$，所有范数均为一、$\zeta_1=1$；此选择在下述物理完成中给出 $p=1$。

将三种情形共同完成为原始因子上的物理协议。我们已经对给定的 $n$ 取得非零 $\lambda_1,\ldots,\lambda_n\in H^\vee$、$\gamma>0$ 与 $z\in\mathbb T^k$，满足

$$
\prod_{a=1}^n\lambda_a(s_j)=\gamma z_j\qquad(1\le j\le k).
$$

在原始 $H$ 的正交基 $\{|e_\mu\rangle\}_{\mu=1}^q$ 中写

$$
\begin{aligned}
\lambda_a\left(\sum_\mu x_\mu|e_\mu\rangle\right)
 &=\sum_\mu\beta_{a\mu}x_\mu,\\
N_a=\|\lambda_a\|_H
 &=\left(\sum_\mu|\beta_{a\mu}|^2\right)^{1/2}>0,\qquad
|a_a\rangle=\frac1{N_a}\sum_\mu\overline{\beta_{a\mu}}|e_\mu\rangle.
\end{aligned}
$$

因此 $|a_a\rangle$ 归一化，且其 bra 为 $\lambda_a/N_a$。共轭只在从复线性泛函系数转为表示 ket 时出现。对任一单位代表，

$$
\gamma=\prod_{a=1}^n|\lambda_a(s_j)|
       \le\prod_{a=1}^nN_a,
\qquad
\alpha:=\frac{\gamma}{\prod_{a=1}^nN_a}\in(0,1].
$$

代数延拓可能增大这些范数，但只把全部代表的乘积幅度缩放同一个正因子。对原始系统标签，重复射线的校准相位必须逐份累积，故

$$
t_i=\prod_{a=1}^n\langle a_a|r_i\rangle
    =\alpha u_i^n z_{\kappa(i)}.
$$

每位持有者在自己的原始 $H$ 上使用

$$
Q_{a,0}=|a_a\rangle\langle a_a|,\qquad
Q_{a,1}=I_H-Q_{a,0},\qquad
Q_\varepsilon=\bigotimes_{a=1}^nQ_{a,\varepsilon_a}
\quad(\varepsilon\in\{0,1\}^n).
$$

全部 $2^n$ 个结果，包括所有失败结果，满足

$$
\sum_{\varepsilon\in\{0,1\}^n}Q_\varepsilon
  =\bigotimes_{a=1}^n(Q_{a,0}+Q_{a,1})=I_{H^{\otimes n}},
\qquad Q_\varepsilon^\dagger Q_\varepsilon=Q_\varepsilon.
$$

所以对应的投影 instrument 完全正且总和保迹。接受全第一结果时的输出记录固定为 $|a_1\rangle\otimes\cdots\otimes|a_n\rangle$，因为

$$
(I_S\otimes Q_{(0,\ldots,0)})J_n|i\rangle
=t_i|i\rangle\otimes|a_1\rangle\otimes\cdots\otimes|a_n\rangle.
$$

迹掉此记录得到 $K=\operatorname{diag}(t_1,\ldots,t_d)$。取终端反馈

$$
\begin{aligned}
K&=\operatorname{diag}\bigl(\alpha u_i^n z_{\kappa(i)}\bigr)_{i=1}^d,\\
U&=\operatorname{diag}\bigl(\overline{u_i^n z_{\kappa(i)}}\bigr)_{i=1}^d,
\qquad UK=\alpha I_S.
\end{aligned}
$$

$U$ 是已知对角酉算子，记录测量期间没有操作系统。因此对每个矩阵 $B$ 及每个有限参考上的矩阵 $B_{AS}$，

$$
\begin{aligned}
\mathcal T(B)&=UKBK^\dagger U^\dagger=\alpha^2B,\\
(\operatorname{id}_A\otimes\mathcal T)(B_{AS})
 &=(I_A\otimes UK)B_{AS}(I_A\otimes UK)^\dagger
   =\alpha^2B_{AS}.
\end{aligned}
$$

令 $p=\alpha^2\in(0,1]$ 即得第一项。对任意未知归一化联合态取迹，成功概率为同一个 $p$，接受后归一化恢复整个联合态，包含全部系统相干与参考纠缠。设置只使用已知记录及 $n$，不读取未知输入。$k=1$ 的上述选择给出 $t_i=u_i^n$、$UK=I_S$；即便 $q=1$，零补投影仍是合法的失败效果。

最后证明亏量二的最坏情形。对任意 $h\ge2$，在 $H=\mathbb C^h$ 中取正交单位基 $e_1,\ldots,e_h$，用以下 $k=h+2$ 个单位向量分别作为系统 $S=\mathbb C^{h+2}$ 的记录：

$$
e_1,\quad e_2,\quad
\frac{e_1+e_2}{\sqrt2},\quad
\frac{e_1+i e_2}{\sqrt2},\quad
e_3,\ldots,e_h.
$$

这些射线不同，且张成 $H$。前四个正是定义 392.1 的 Buscemi–Chiribella–D’Ariano 四记录，来源为 [*Inverting Quantum Decoherence by Classical Feedback from the Environment*, quant-ph/0504195v5](https://arxiv.org/abs/quant-ph/0504195v5)，式 (9)，并沿用该定义说明的 ket 行坐标与通道对偶约定；其余向量是独立补空间中的单位代表。

若有正成功的一记录分支，令相应 bra 在 $e_1,e_2$ 上的值为 $a,b$。反馈为酉且要求对全部系统矩阵恢复，特别是在每个基投影上成功概率相同且为正，所以存在 $\delta>0$ 使

$$
|a|=|b|=
\left|\frac{a+b}{\sqrt2}\right|=
\left|\frac{a+ib}{\sqrt2}\right|=\delta.
$$

后两个模长平方分别给出

$$
\delta^2=\delta^2+\operatorname{Re}(a\overline b),
\qquad
\delta^2=\delta^2+\operatorname{Im}(a\overline b).
$$

因此 $a\overline b=0$，与 $|a\overline b|=\delta^2>0$ 矛盾。这个矛盾也适用于任意未归一化非零 bra 的平面限制；添加补空间分量不能消除它。另一方面该族的 $c=2$，第一项保证每个实际 $n\ge2$ 都有正成功局部分支，特别是两份记录足够。第二项得证。

平面记录加独立补空间的几何安排已有 Chefles，[*Unambiguous Discrimination Between Linearly Dependent States With Multiple Copies*, quant-ph/0105016v3](https://arxiv.org/abs/quant-ph/0105016v3)，§II 在式 (2.3) 后检验最坏情形时的先例。该文研究给定未知纯态的多个副本能否线性独立并作无歧义判别，其式 (2.3) 在态数、复制数、单份跨度取 $k,n,h$ 时为 $n\ge k-h+1$。这里保留这个几何出处，但所处理的是由同一个未知系统产生的受控记录、逐原始因子的完整局部测量和相干恢复；判别副本的结果不能替代上述乘积泛函、归一化及 $UK=\alpha I_S$ 的物理合成。证毕。

本定理对每个给定记录族给出充分次数；除 $c=2$ 的上述最坏情形结论外，不给出一般亏量的最小次数或下界，也不要求一个指定的相位向量可达。成功概率依赖实际构造；本定理不提供统一正下界、最优概率或一般确定性恢复结论。所用支配性不提供有效寻找因子、精度、鲁棒性或实施成本保证；混合记录、不可访问记录以及超出定义 409.1 的操作接口不在其量词内。

## 追加锚（本行以下为增补区）

## 411. 重复量子比特记录的恢复配置维数与一般必要次数

设整数 $k\ge2$、$n\ge1$，有序不同射线的配置空间为

$$
\mathcal D_k=\{(x_1,\ldots,x_k)\in(\mathbb{CP}^1)^k:
                    x_i\ne x_j\text{ 对所有 }i\ne j\}.
$$

赋予它通常复射影流形的相对拓扑；其实维数为 $2k$。令 $\mu_{\mathrm{FS}}$ 为 $\mathbb{CP}^1$ 上总质量为一的 Fubini–Study 体积，$\mu_k$ 为乘积测度 $\mu_{\mathrm{FS}}^{\otimes k}$ 在 $\mathcal D_k$ 上的限制。每条已知射线 $x_j$ 选单位代表 $s_j\in\mathbb C^2$。系统为一个 $S=\mathbb C^k$，固定正交基 $\{|j\rangle\}_{j=1}^k$；按定义 400.1 完成全部实际记录的制备：

$$
R_n=(\mathbb C^2)^{\otimes n},\qquad
r_j=s_j^{\otimes n},\qquad
J_n|j\rangle=|j\rangle\otimes r_j,\qquad
W_n=\operatorname{Sym}^n(\mathbb C^2)\subseteq R_n.
$$

$n$ 是同一个未知系统的记录数，全部 $n$ 个原始记录因子均保持联合可访问。$W_n$ 只表示原始 $R_n$ 中的数学子空间，不改变物理张量因子。

允许在 $J_n$ 之后对完整 $R_n$ 作任意有限结果的联合 CP instrument $\{\mathcal I_y\}_{y\in Y}$，各分支完全正且总和保迹；与输入无关的记录辅助装置并入此 instrument。将全部输出记录取迹，所得系统分支记为 $\mathcal M_y$。选择一个固定接受集合 $Y_{\mathrm s}\subseteq Y$，每个实际经典结果 $y$ 只控制一个预先指定的终端酉算子 $U_y$，作用于整个 $S$。在此终端反馈之前不操作系统，任意有限维外部参考 $A$ 始终不被操作。协议可依赖已知配置与 $n$，不得依赖未知输入；每个候选协议的结果数有限，不要求不同候选共用一个结果数上界。

定义成功配置集合 $\mathcal E_{k,n}\subseteq\mathcal D_k$：存在上述同一个协议及同一个 $p>0$，使其接受映射满足

$$
\mathcal T(X):=\sum_{y\in Y_{\mathrm s}}U_y\mathcal M_y(X)U_y^\dagger
                 =pX\qquad\text{对每个 }X\in\mathcal L(S).
$$

等价地，同一协议及 $p$ 对每个有限维 $A$ 和每个 $X_{AS}\in\mathcal L(A\otimes S)$ 都满足

$$
(\operatorname{id}_A\otimes\mathcal T)(X_{AS})=pX_{AS}.
$$

这里 $\operatorname{id}_A$ 表示参考矩阵空间上的恒等映射。两个表述的等价性来自矩阵张量基的线性展开及 $A=\mathbb C$ 的特例；完整 instrument 的保迹性还给出 $p\le1$。

**定理 411.1（联合记录精确恢复的半代数成功集与一般必要次数）。** 在上述接口下，对全部整数 $k\ge2$、$n\ge1$，有

$$
\begin{aligned}
\mathcal E_{k,n}
 &=\left\{(x_1,\ldots,x_k)\in\mathcal D_k:
       \exists b\in W_n,\ \|b\|=1,\ \exists t\in(0,1],\quad
       |\langle b|s_j^{\otimes n}\rangle|^2=t\ \text{对每个 }j\right\},\\
\dim_{\mathbb R}\mathcal E_{k,n}&\le2n+k+1,
\end{aligned}
$$

且 $\mathcal E_{k,n}$ 是半代数集。若 $k\ge n+1$，它在 $\mathcal D_k$ 中相对闭。若 $k\ge2n+2$，则

$$
\mathcal D_k\setminus\mathcal E_{k,n}
\quad\text{在 }\mathcal D_k\text{ 中开且稠密},\qquad
\mu_k(\mathcal E_{k,n})=0.
$$

对每个固定的 $k\ge2$，令

$$
N_k=\left\lfloor\frac{k-2}{2}\right\rfloor,\qquad
\mathcal U_k=\bigcap_{n=1}^{N_k}
                   (\mathcal D_k\setminus\mathcal E_{k,n}),
$$

空指标交集约定为 $\mathcal D_k$。则 $\mathcal U_k$ 在 $\mathcal D_k$ 中开且稠密，并有满 $\mu_k$ 测度；在同一个 $\mathcal U_k$ 中，每个配置若以某个实际正整数记录数 $n$ 实现正概率精确恢复，就必须满足

$$
n\ge\left\lfloor\frac{k}{2}\right\rfloor.
$$

$k=2,3$ 时，$\mathcal U_k=\mathcal D_k$，该条件只给出接口原有的 $n\ge1$。

证明。先把任意联合 instrument 的成功条件转为纯对称泛函条件。这使用第 389—391 节的环境辅助校正结构及定理 407.2 中的对称泛函表示；环境测量实现与酉校正条件的来源为 Gregoratti–Werner，[*Quantum Lost and Found*, quant-ph/0209025v1](https://arxiv.org/abs/quant-ph/0209025v1)，Theorem 1、Proposition 2（PDF 第 4–5 页）。以下保留原始经典结果及其反馈，直接计算所需的接受映射。

令 $D_y=\mathcal I_y^*(I)$ 为记录分支的对偶效果，则

$$
D_y\succeq0,\qquad \sum_{y\in Y}D_y=I_{R_n}.
$$

对系统矩阵单位 $E_{ij}=|i\rangle\langle j|$，输出记录的迹给出

$$
\begin{aligned}
\mathcal M_y(E_{ij})
 &=\operatorname{Tr}\bigl(\mathcal I_y(|r_i\rangle\langle r_j|)\bigr)E_{ij}\\
 &=\langle r_j|D_y|r_i\rangle E_{ij}.
\end{aligned}
$$

因此任意 CP 分支在此处只通过其效果进入。将有限维正矩阵作谱分解，并定义对角算子

$$
D_y=\sum_a|v_{ya}\rangle\langle v_{ya}|,\qquad
K_{ya}=\operatorname{diag}\bigl(\langle v_{ya}|r_1\rangle,\ldots,
                               \langle v_{ya}|r_k\rangle\bigr),
\qquad
\mathcal M_y(X)=\sum_aK_{ya}XK_{ya}^\dagger.
$$

$v_{ya}$ 可不归一化。$a$ 是效果分解的数学指标，不是新增的可观测结果；同一个原始结果 $y$ 的全部 $a$ 必须使用同一个 $U_y$。

令 $|\Omega\rangle=\sum_{j=1}^k|j\rangle\otimes|j\rangle$，并写 $|L\rangle\!\rangle=(I_S\otimes L)|\Omega\rangle$。由全部矩阵上的 $\mathcal T=p\operatorname{id}_S$，其 Choi 矩阵满足

$$
\sum_{y\in Y_{\mathrm s},a}
 |U_yK_{ya}\rangle\!\rangle\langle\!\langle U_yK_{ya}|
   =p|I_S\rangle\!\rangle\langle\!\langle I_S|.
$$

任取 $w\perp|I_S\rangle\!\rangle$，左侧二次型是有限个非负数之和且等于零，因此每个 $|U_yK_{ya}\rangle\!\rangle$ 都与这样的 $w$ 正交。每个向量遂位于 $\mathbb C|I_S\rangle\!\rangle$，即

$$
U_yK_{ya}=c_{ya}I_S,\qquad
\sum_{y\in Y_{\mathrm s},a}|c_{ya}|^2=p.
$$

因 $p>0$，可选一个 $c=c_{ya}\ne0$，记相应的 $v=v_{ya}$、$K=K_{ya}$。$U_y$ 的酉性给出

$$
K^\dagger K=|c|^2I_S,\qquad
|\langle v|r_j\rangle|^2=|c|^2>0\quad(1\le j\le k).
$$

全部 $r_j$ 属于 $W_n$。令 $v_W=P_{W_n}v$，则 $\langle v_W|r_j\rangle=\langle v|r_j\rangle$，从而 $v_W\ne0$。归一化为

$$
b=\frac{v_W}{\|v_W\|},\qquad
t=\frac{|c|^2}{\|v_W\|^2},\qquad
|\langle b|r_j\rangle|^2=t.
$$

单位向量的重叠模不超过一，故 $0<t\le1$。这里 $t$ 是归一化泛函的共同响应，通常不同于原协议的总成功概率 $p$。$P_{W_n}$ 只限制一个数学泛函，不是物理压缩，也没有遗漏任何已制备记录。

反过来，设有这样的 $b,t$，将 $b$ 视为完整 $R_n$ 中的单位向量。取

$$
\Pi=|b\rangle\langle b|,\qquad
\mathcal I_0(Z)=\Pi Z\Pi,\qquad
\mathcal I_1(Z)=(I_{R_n}-\Pi)Z(I_{R_n}-\Pi).
$$

两个 Kraus 效果之和为 $\Pi+(I_{R_n}-\Pi)=I_{R_n}$，所以这是完整原始记录空间上的两结果 CP instrument。只接受结果 $0$。写 $\langle b|r_j\rangle=\sqrt t\,z_j$、$|z_j|=1$，则

$$
(I_S\otimes\Pi)J_n|j\rangle
   =\sqrt t\,z_j|j\rangle\otimes b,
\qquad
K=\sqrt t\operatorname{diag}(z_1,\ldots,z_k).
$$

反馈取 $U=\operatorname{diag}(\overline z_1,\ldots,\overline z_k)$，便有 $UK=\sqrt t\,I_S$。于是对所有系统矩阵及每个有限参考上的所有矩阵，分别得到

$$
\mathcal T(X)=tX,\qquad
(\operatorname{id}_A\otimes\mathcal T)(X_{AS})
 =(I_A\otimes UK)X_{AS}(I_A\otimes UK)^\dagger=tX_{AS}.
$$

失败投影在完整 instrument 内，构造使用同一个原始 $R_n$。两方向合起来证明定理中的集合等式。若重新选代表 $s_j\mapsto e^{i\theta_j}s_j$，每个幅度只乘 $e^{in\theta_j}$，共同模长不变，校准反馈吸收这些相位；故成功集合确实定义在射线上。

下面给纯泛函参数一个没有相位冗余的半代数表示。固定 $W_n$ 的正交基，其复维数为 $n+1$，令

$$
\mathcal P_n=\{B\in\mathbb C^{(n+1)\times(n+1)}:
                  B=B^\dagger,\ B^2=B,\ \operatorname{Tr}B=1\}.
$$

这些条件在矩阵实部、虚部坐标中都是实多项式等式。Hermitian 幂等矩阵的本征值为 $0$ 或 $1$，迹一迫使恰有一个本征值为 $1$；所以 $\mathcal P_n$ 恰由 $B=|b\rangle\langle b|$、$\|b\|=1$ 组成。又有

$$
\|B\|_{\mathrm F}^2=\operatorname{Tr}(B^\dagger B)
                       =\operatorname{Tr}B=1,
$$

故该多项式闭集有界而紧致。在 $B_{aa}>0$ 的图上令

$$
w_a=1,\qquad w_i=\frac{B_{ia}}{B_{aa}}\ (i\ne a),\qquad
B=\frac{ww^\dagger}{w^\dagger w}.
$$

若 $B=bb^\dagger$，这些比值是 $b_i/b_a$；反向公式对任意 $n$ 个复坐标都成立，且 $w^\dagger w>0$。$n+1$ 个这样的有理半代数光滑图覆盖 $\mathcal P_n$，将其识别为 $\mathbb{CP}^n$，并给出 $\dim_{\mathbb R}\mathcal P_n=2n$。这里的 $\mathcal P_n$ 是见证参数空间，与未操作参考 $A$ 无关。

用 Bloch 球坐标识别 $\mathbb{CP}^1$ 与 $S^2\subset\mathbb R^3$，记 Pauli 矩阵为 $\sigma_1,\sigma_2,\sigma_3$。若 $Q:W_n\hookrightarrow R_n$ 是固定包含等距映射，置

$$
P_x=\frac{I_2+x_1\sigma_1+x_2\sigma_2+x_3\sigma_3}{2},\qquad
C_n(x)=Q^\dagger P_x^{\otimes n}Q,\qquad
f_B(x)=\operatorname{Tr}(B C_n(x)).
$$

对 $x\in S^2$，$P_x$ 是对应射线的单位纯投影；$C_n(x)$ 是相应 $s^{\otimes n}$ 在 $W_n$ 中的纯投影。其矩阵元是 $x$ 的实坐标的复系数多项式，实部和虚部均为实多项式。因此 $f_B(x)$ 在 $B,x$ 的实坐标中为实多项式，并且

$$
f_B(x)=|\langle b|s^{\otimes n}\rangle|^2\in[0,1]
\qquad(B=|b\rangle\langle b|).
$$

这些式子不要求在整个射影空间连续选择单位代表。在 Bloch 坐标中，$\mathcal D_k$ 由各 $\|x_j\|^2=1$ 及 $\|x_i-x_j\|^2>0$ 描述，故是半代数流形。

对每个纯见证 $B$，响应 $f_B$ 非恒定。为明确正次数与无穷远点在这里的作用，沿用定理 407.2 的对称基 $e_\ell$，将 $b=\sum_{\ell=0}^n b_\ell e_\ell$ 代入二元齐次形式

$$
F_b(X,Y)=\langle b|(X|0\rangle+Y|1\rangle)^{\otimes n}\rangle
 =\sum_{\ell=0}^n\overline{b_\ell}\sqrt{\binom n\ell}\,
                 X^{n-\ell}Y^\ell.
$$

$b\ne0$ 且全部二项式系数非零，所以 $F_b$ 是非零的 $n$ 次齐次多项式。令 $m=\deg F_b(z,1)\le n$，复数域上的因式分解给出

$$
F_b(X,Y)=cY^{n-m}\prod_{a=1}^m(X-\lambda_aY),\qquad c\ne0.
$$

这是包含 $Y=0$ 的齐次恒等式；$m=0$ 时空积为一，重复根照重数保留。因 $n\ge1$，至少有一个线性因子，故有一个射影零点；$m<n$ 时 $[1:0]$ 正是其中的无穷远零点。各因子只有有限条零射线，故另有射影点使 $F_b$ 非零。归一化响应为

$$
f_B([X:Y])=\frac{|F_b(X,Y)|^2}{(|X|^2+|Y|^2)^n},
$$

因此同时取得零值和正值，不可能恒定。这里所用的二元形式及其因式分解仍是定理 407.2 的中间结构；对称量子比特的 Majorana 表示见 Aulbach–Markham–Murao，[*Geometric Entanglement of Symmetric States and the Majorana Representation*, arXiv:1010.4777v1](https://arxiv.org/abs/1010.4777v1)，§IV 式 (11)–(12)（PDF 第 4 页）。

现对任意实数 $t$ 考察整个水平集

$$
L_{B,t}=\{x\in S^2:f_B(x)=t\}.
$$

在仿射图 $[1:u+iv]$ 中，水平条件等价于实多项式方程

$$
Q_{B,t}(u,v)=|F_b(1,u+iv)|^2-t(1+u^2+v^2)^n=0.
$$

分母处处严格为正。若 $Q_{B,t}$ 为零多项式，$f_B$ 会在整个仿射图等于 $t$，再由遗漏射影点处的连续性而在整个射影直线上恒定，与上段矛盾。因此 $Q_{B,t}$ 非零。非零实多项式不能在 $\mathbb R^2$ 的非空开集上恒为零；其零集没有内点。由半代数细胞维数刻画，该零集维数至多一：若有二维细胞，该细胞在二维坐标空间内开，便给出内点。另一图 $[u+iv:1]$ 中用 $F_b(u+iv,1)$ 得到相同结论；两个图覆盖整个射影直线，从而

$$
\dim_{\mathbb R}L_{B,t}\le1
\qquad\text{对每个 }B\in\mathcal P_n\text{ 和每个 }t\in\mathbb R.
$$

空集取维数 $-\infty$。所用细胞刻画及有限并的维数规则见 Basu–Pollack–Roy，[*Algorithms in Real Algebraic Geometry*, 作者发布稿](https://www.math.purdue.edu/~sbasu/bpr-posted1.pdf)，Theorem 5.25（第 178 页）、Proposition 5.28（第 179–180 页）；下文编号均对应此稿。上面的论证包括临界、奇异及重复根的全部水平，不要求水平是正则值。

这说明前面的纯见证提取承担实质作用。若把参数放宽为任意混合密度矩阵，则 $B_0=I_{W_n}/(n+1)$ 满足

$$
\operatorname{Tr}(B_0C_n(x))=\frac1{n+1}\qquad(x\in S^2),
$$

因为 $\operatorname{Tr}C_n(x)=1$；其对应水平集是整个球面。实际成功通道的秩一 Choi 支撑先强制产生纯 $B$，才允许将全部共同响应限制到至多一维的水平集上。

定义关联集及其两个坐标投影：

$$
\begin{aligned}
\mathcal I_{k,n}
 &=\{(B,t,\boldsymbol x)\in\mathcal P_n\times(0,1]\times\mathcal D_k:
                          f_B(x_j)=t\ (1\le j\le k)\},\\
\rho(B,t,\boldsymbol x)&=(B,t),\qquad
\pi(B,t,\boldsymbol x)=\boldsymbol x.
\end{aligned}
$$

多项式响应、纯投影等式以及 $0<t\le1$ 和不同点的不等式，使 $\mathcal I_{k,n}$ 成为半代数集。对每个 $(B,t)$，$\rho$ 的纤维恰为 $L_{B,t}^k$ 去掉所有重合点对角线，故由乘积及子集的维数规则有

$$
\dim_{\mathbb R}\rho^{-1}(B,t)\le k.
$$

为将这一所有纤维上的界与参数维数相加，应用 Hardt 半代数平凡化定理（上述 Basu–Pollack–Roy 稿 Theorem 5.45，第 194 页）。$\rho:\mathcal I_{k,n}\to\mathcal P_n\times(0,1]$ 是连续半代数映射，满足该定理的假设；这里不要求映射 proper，也不要求源紧致。它给出目标的有限半代数分拆 $\{A_\alpha\}$，在每个非空纤维的块上有保持基点的半代数同胚

$$
\rho^{-1}(A_\alpha)\cong A_\alpha\times F_\alpha,
$$

其中 $F_\alpha$ 是该块上的一个实际纤维。忽略空纤维块，用半代数同胚不变性、有限并及乘积的维数规则，得到

$$
\begin{aligned}
\dim_{\mathbb R}\mathcal I_{k,n}
 &=\max_\alpha\bigl(\dim_{\mathbb R}A_\alpha
                         +\dim_{\mathbb R}F_\alpha\bigr)\\
 &\le\dim_{\mathbb R}(\mathcal P_n\times(0,1])+k
   =2n+1+k.
\end{aligned}
$$

若关联集为空，所需不等式直接成立。这些维数规则使用同稿 Theorem 5.25、Proposition 5.28，以及半代数映射的维数结论 Proposition 5.29、Lemma 5.30（第 180 页）。有限乘积平凡化使估计覆盖全部参数及奇异纤维，无须假设各水平方程相互独立。

前面已经从任意原始协议提取见证，并从每个正水平见证构造完整原始记录协议，因此这里的实际投影满足

$$
\pi(\mathcal I_{k,n})=\mathcal E_{k,n}.
$$

Tarski–Seidenberg 投影定理（同稿 Theorem 2.76，第 76 页）给出 $\mathcal E_{k,n}$ 的半代数性；投影不增维（同稿 Proposition 5.29、Lemma 5.30）给出

$$
\dim_{\mathbb R}\mathcal E_{k,n}
 \le\dim_{\mathbb R}\mathcal I_{k,n}\le2n+k+1.
$$

相对闭性需要另外处理正水平趋于零的可能。设 $k\ge n+1$，成功配置序列 $\boldsymbol x^{(\ell)}\in\mathcal E_{k,n}$ 收敛到 $\boldsymbol x\in\mathcal D_k$。各取归一化纯见证 $B_\ell\in\mathcal P_n$ 与共同水平 $t_\ell\in(0,1]$。紧空间 $\mathcal P_n\times[0,1]$ 中存在子序列收敛到 $(B,t)$。极限 $B$ 仍为迹一纯投影，连续性给出

$$
f_B(x_j)=t\quad(1\le j\le k),\qquad 0\le t\le1.
$$

若 $t=0$，选 $B=|b\rangle\langle b|$、$\|b\|=1$，便有 $\langle b|s_j^{\otimes n}\rangle=0$ 对全部极限射线的单位代表成立。然而其中任意 $n+1$ 条实际不同的射线，其 $n$ 次幂张成 $W_n$。这是定理 408.2 的齐次插值在当前点集上的应用，所对应的纯量子比特幂的独立性条件亦见 Chefles，[*Unambiguous Discrimination Between Linearly Dependent States With Multiple Copies*, quant-ph/0105016v3](https://arxiv.org/abs/quant-ph/0105016v3)，§II 式 (2.8)（PDF 第 5 页），取该文 $N=n+1$、$C=n$。

具体地，选这 $n+1$ 个代表为 $q_0,\ldots,q_n$。因射线不同，$\det(q_j,q_h)\ne0$ 对 $h\ne j$ 成立，故次数 $n$ 的插值式

$$
H_j(z)=\prod_{\substack{0\le h\le n\\h\ne j}}
                 \frac{\det(z,q_h)}{\det(q_j,q_h)}
\qquad(0\le j\le n)
$$

满足 $H_j(q_i)=\delta_{ji}$。每个 $H_j$ 由对称基展开对应 $W_n$ 上的复线性泛函，因此这些泛函在 $q_i^{\otimes n}$ 上给出单位评价矩阵。这 $n+1$ 个向量线性独立，数目又等于 $\dim_{\mathbb C}W_n$，所以张成 $W_n$。于是消去全部这些向量的 $\langle b|$ 必为零，与归一化矛盾。故 $t>0$，极限配置仍属于 $\mathcal E_{k,n}$；$\mathcal D_k$ 可度量，序列闭性即相对闭性。这里排除的是归一化见证的 $t=0$ 极限，未把它替换成原协议的总概率；闭性只针对极限仍在 $\mathcal D_k$ 中的情形。

若 $k\ge2n+2$，则

$$
\dim_{\mathbb R}\mathcal E_{k,n}\le2n+k+1\le2k-1
 <\dim_{\mathbb R}\mathcal D_k.
$$

低于流形维数的半代数子集没有相对内点；结合刚证的相对闭性，$\mathcal E_{k,n}$ 无处稠密，故失败集合 $\mathcal D_k\setminus\mathcal E_{k,n}$ 开且稠密。再由有限光滑半代数分层（Basu–Pollack–Roy，同稿 Theorem 5.38，第 185 页），成功集是有限个维数至多 $2k-1$ 的光滑半代数片之并。在流形坐标图中，每片可用可数个局部光滑图像片覆盖，因维数小于 $2k$ 而有零 $2k$ 维 Lebesgue 测度。Fubini–Study 体积在仿射坐标 $z=u+iv$ 中具有光滑正密度

$$
d\mu_{\mathrm{FS}}(z)=\frac{du\,dv}{\pi(1+|z|^2)^2},
$$

故乘积密度保持上述零测集，得到 $\mu_k(\mathcal E_{k,n})=0$。各点碰撞对角线也为低维光滑子流形，有限并仍为零测集，所以 $\mu_k(\mathcal D_k)=1$，失败集合具有满测度。

最后固定 $k$。对每个实际整数 $1\le n\le N_k$，分别有 $k\ge2n+2$，以上论证分别给出开、稠密、满测度的失败集合。有限个开稠密集的交仍开且稠密：从任意非空开集出发，逐次与这些开稠密集相交，每一步都留下非空开集。其补集是有限个零测成功集之并，故交集 $\mathcal U_k$ 仍为满测度。若 $\boldsymbol x\in\mathcal U_k$ 以某个实际正整数 $n$ 成功，则 $n$ 不在 $1,\ldots,N_k$ 中，于是

$$
n\ge N_k+1
 =\left\lfloor\frac{k-2}{2}\right\rfloor+1
 =\left\lfloor\frac{k}{2}\right\rfloor.
$$

当 $k=2,3$ 时，$N_k=0$，空交集及结论正如陈述。这一有限交对每个 $J_n$ 单独应用失败条件，未使用关于 $n$ 的成功单调性，也未丢弃任何较大制备中的记录。纯见证的全部水平集维数界控制成功配置的维数，归一化紧致性与实际不同射线的插值又阻止成功见证经零水平逃逸；二者共同给出这里的开稠密必要次数结论。证毕。

## 追加锚（本行以下为增补区）

## 412. 重复量子比特记录成功配置的精确维数与局部开集

沿用第 411 节的有序不同射线配置空间 $\mathcal D_k$、成功集合 $\mathcal E_{k,n}$ 及其实半代数维数，整数范围始终为 $k\ge2$、$n\ge1$。对每条已知射线选单位代表 $s_j\in\mathbb C^2$，系统和全部原始记录仍为

$$
S=\mathbb C^k,\qquad R_n=(\mathbb C^2)^{\otimes n},\qquad
J_n|j\rangle=|j\rangle\otimes s_j^{\otimes n},\qquad
W_n=\operatorname{Sym}^n(\mathbb C^2)\subseteq R_n.
$$

这里采用定义 400.1 的受控制备；全部 $n$ 份记录在制备后保持联合可访问，$W_n$ 仅为数学子空间。允许的操作恰为第 411 节的完整有限结果联合 CP instrument，作用于整个 $R_n$，与输入无关的记录辅助装置并入其中；各分支之和保迹，输出记录取迹后得到系统分支 $\mathcal M_y$。每个协议的接受集合 $Y_{\mathrm s}$ 固定，每个实际结果只控制作用于整个 $S$ 的一个终端酉算子 $U_y$；此前不操作系统，任意有限维参考 $A$ 始终不被操作。每个协议的结果数有限，不要求不同协议共用结果数上界。成功要求同一协议和同一 $p>0$ 对全部矩阵满足

$$
\mathcal T(X)=\sum_{y\in Y_{\mathrm s}}U_y\mathcal M_y(X)U_y^\dagger=pX,
\qquad
(\operatorname{id}_A\otimes\mathcal T)(X_{AS})=pX_{AS}
$$

第一式对每个 $X\in\mathcal L(S)$ 成立，第二式对每个有限维 $A$ 及每个 $X_{AS}\in\mathcal L(A\otimes S)$ 成立。协议和 $p$ 可依赖已知配置与 $n$，不得依赖未知输入；局部构造中的不同配置可以分别校准。

**定理 412.1（完整重复记录成功集合的精确维数及局部实现）。** 在上述接口下，对所有整数 $k\ge2$、$n\ge1$，有

$$
\boxed{\dim_{\mathbb R}\mathcal E_{k,n}=\min(2k,2n+k+1).}
$$

当 $k\le2n+1$ 时，$\mathcal E_{k,n}$ 包含 $\mathcal D_k$ 的一个非空相对开子集。当 $k\ge2n+1$ 时，$\mathcal E_{k,n}$ 包含一个实维数为 $2n+k+1$ 的嵌入光滑流形片。这两个局部结论均为存在断言；在边界 $k=2n+1$，所构造的流形片就是一个非空相对开集，其维数同时等于 $2k$ 和 $2n+k+1$。

证明。先在赤道配置附近构造精确成功族。采用定理 407.2 证明中的归一化对称基 $e_0,\ldots,e_n$：$e_\ell$ 为恰有 $\ell$ 个 $|1\rangle$ 的计算基向量之和除以 $\sqrt{\binom n\ell}$。记

$$
c_\ell=\sqrt{\binom n\ell},\qquad
z_\ell=x_\ell+i y_\ell\quad(1\le\ell\le n),\qquad
b(z)=\frac{e_0+\sum_{\ell=1}^n z_\ell e_\ell}
            {\sqrt{1+\sum_{\ell=1}^n|z_\ell|^2}}.
$$

$b(z)$ 是 $W_n$ 中的单位向量，其 $e_0$ 系数为正实数，故已固定整体相位，见证参数恰有 $2n$ 个实坐标。对 $r>0$ 和圆周角 $\varphi$，令

$$
s(r,\varphi)=\frac{|0\rangle+r e^{i\varphi}|1\rangle}{\sqrt{1+r^2}}.
$$

对称基展开给出

$$
s(r,\varphi)^{\otimes n}
 =\frac{\sum_{\ell=0}^n c_\ell r^\ell e^{i\ell\varphi}e_\ell}
             {(1+r^2)^{n/2}},
\qquad
f_z(r,\varphi):=|\langle b(z)|s(r,\varphi)^{\otimes n}\rangle|^2
 =\frac{\left|1+\sum_{\ell=1}^n\overline{z_\ell}c_\ell
                       r^\ell e^{i\ell\varphi}\right|^2}
        {\left(1+\sum_{\ell=1}^n|z_\ell|^2\right)(1+r^2)^n}.
$$

取赤道半径 $r_0=1$ 和共同响应 $t_0=2^{-n}\in(0,1)$。在 $z=0,r=1$ 处，对任意 $\varphi$ 有

$$
\begin{aligned}
f_0(1,\varphi)&=2^{-n},&
\partial_r f_0(1,\varphi)&=-n2^{-n},&
\partial_\varphi f_0(1,\varphi)&=0,\\
\left.\partial_{x_\ell}f_z(r,\varphi)\right|_{z=0,r=1}
 &=2^{1-n}c_\ell\cos(\ell\varphi),&
\left.\partial_{y_\ell}f_z(r,\varphi)\right|_{z=0,r=1}
 &=2^{1-n}c_\ell\sin(\ell\varphi).
\end{aligned}
$$

其中正的正弦号来自

$$
\operatorname{Re}\bigl((x_\ell-i y_\ell)e^{i\ell\varphi}\bigr)
 =x_\ell\cos(\ell\varphi)+y_\ell\sin(\ell\varphi).
$$

见证归一化分母 $1+\sum_\ell|z_\ell|^2$ 在 $z=0$ 的一阶微分为零，因此没有额外的一阶项。

任取模 $2\pi$ 两两不同的 $k$ 个角 $\theta_1,\ldots,\theta_k$。在圆周上为它们选两两不交的小开弧，并在各弧上固定以 $\theta_j$ 为中心的实数提升。以下 $\varphi_j$ 均在各自提升区间内。考虑 $k$ 个方程

$$
G_j(t,z,\boldsymbol r,\boldsymbol\varphi)
 :=f_z(r_j,\varphi_j)-t=0\qquad(1\le j\le k).
$$

在 $(t,z,\boldsymbol r,\boldsymbol\varphi)
 =(t_0,0,\boldsymbol 1,\boldsymbol\theta)$ 处，关于全部径向变量的导数是可逆矩阵

$$
D_{\boldsymbol r}G=-n2^{-n}I_k.
$$

实光滑隐函数定理因而给出基点

$$
a_0=(t_0,0,\ldots,0,\theta_1,\ldots,\theta_k)
 \in\mathbb R^{2n+1+k}
$$

的一个开邻域 $\mathcal V$ 以及光滑函数

$$
r_j=R_j(t,z,\boldsymbol\varphi),\qquad
R_j(a_0)=1,\qquad
f_z\bigl(R_j(t,z,\boldsymbol\varphi),\varphi_j\bigr)=t
\quad(1\le j\le k).
$$

缩小 $\mathcal V$，使全部 $R_j>0$、$0<t<1$，并使每个 $\varphi_j$ 始终位于其指定开弧。于是各复数 $R_j e^{i\varphi_j}$ 两两不同，对应射线均位于共同仿射图 $[1:u+iv]$，且组成 $\mathcal D_k$ 中的配置。这给出了全部 $k$ 个等响应方程的精确解。邻域的选择可依赖 $k,n$ 及所选角。

对每个这样的解，使用定理 411.1 的充分方向，在完整原始 $R_n$ 上取

$$
\Pi=|b(z)\rangle\langle b(z)|,\qquad
\mathcal I_0(Z)=\Pi Z\Pi,\qquad
\mathcal I_1(Z)=(I_{R_n}-\Pi)Z(I_{R_n}-\Pi).
$$

两个分支完全正，Kraus 效果之和为 $\Pi+(I_{R_n}-\Pi)=I_{R_n}$，故其总和保迹。固定只接受结果 $0$，结果 $1$ 保留在完整测量内，其终端反馈可取恒等。置

$$
s_j=s\bigl(R_j(t,z,\boldsymbol\varphi),\varphi_j\bigr),\qquad
\alpha_j=\langle b(z)|s_j^{\otimes n}\rangle,\qquad
q_j=\frac{\alpha_j}{\sqrt t},\qquad |q_j|=1.
$$

接受分支满足

$$
(I_S\otimes\Pi)J_n|j\rangle=\alpha_j|j\rangle\otimes b(z),
\qquad
K=\operatorname{diag}(\alpha_1,\ldots,\alpha_k).
$$

因此在整个 $S$ 上取终端酉反馈

$$
U=\operatorname{diag}(\overline{q_1},\ldots,\overline{q_k}),
\qquad UK=\sqrt t\,I_S,
$$

便对每个矩阵和每个未操作的有限维参考有

$$
\mathcal T(X)=UKXK^\dagger U^\dagger=tX,
\qquad
(\operatorname{id}_A\otimes\mathcal T)(X_{AS})
 =(I_A\otimes UK)X_{AS}(I_A\otimes UK)^\dagger=tX_{AS}.
$$

所以这里构造的协议以 $p=t>0$ 成功，全部配置均属于实际物理集合 $\mathcal E_{k,n}$。$t=p$ 仅针对这个具体投影协议；定理 411.1 从任意协议提取的归一化响应 $t$ 不必等于该协议的总成功概率。构造始终使用全部原始记录，$b(z)\in W_n$ 没有改变测量所在的 $R_n$。

接着计算这一精确配置族的微分。按

$$
a=(t,x_1,y_1,\ldots,x_n,y_n,\varphi_1,\ldots,\varphi_k)
$$

排列输入坐标，定义径向和角向坐标映射

$$
H(a)=\bigl(R_1(a),\ldots,R_k(a),\varphi_1,\ldots,\varphi_k\bigr).
$$

对等式 $f_z(R_j(a),\varphi_j)=t$ 求导并代入上面的基点导数，得到

$$
DH(a_0)=
\begin{pmatrix}
A&0\\
0&I_k
\end{pmatrix},
$$

其中 $A$ 有 $k$ 行、$2n+1$ 列，第 $j$ 行为

$$
\left(-\frac{2^n}{n},
 \frac2n c_1\cos\theta_j,\frac2n c_1\sin\theta_j,\ldots,
 \frac2n c_n\cos(n\theta_j),\frac2n c_n\sin(n\theta_j)\right).
$$

这些列是实 Fourier 评价矩阵的非零倍数。圆周采样的 Fourier/Vandermonde 结构见 Amiet–Weigert，[quant-ph/9904036v1](https://arxiv.org/pdf/quant-ph/9904036v1)，PDF 第 6 页式 (17)；取该文 $2s=n$，其 $4s+1$ 个圆周采样对应这里的 $2n+1$ 个节点。此处所需的任意不同节点秩，可用以下经典多项式根数论证直接验证。

当节点数为 $2n+1$ 时，设实三角多项式

$$
T(\varphi)=a_0'+\sum_{\ell=1}^n
       \bigl(a_\ell'\cos(\ell\varphi)+b_\ell'\sin(\ell\varphi)\bigr)
$$

在所有这些节点上为零。令 $w=e^{i\varphi}$，则

$$
w^nT(\varphi)=P(w),\qquad
P(w)=a_0'w^n+\sum_{\ell=1}^n
 \left(\frac{a_\ell'-i b_\ell'}2w^{n+\ell}
       +\frac{a_\ell'+i b_\ell'}2w^{n-\ell}\right)
$$

是次数至多 $2n$ 的复多项式，却有 $2n+1$ 个不同根 $e^{i\theta_j}$，故为零多项式。各次幂系数分别为零，推出全部 $a_\ell',b_\ell'$ 及 $a_0'$ 为零。因此方形实评价矩阵可逆。当 $k<2n+1$ 时，将给定节点补足为 $2n+1$ 个不同圆周节点；可逆矩阵中保留的 $k$ 行线性无关。当 $k>2n+1$ 时，从给定节点中选出 $2n+1$ 个，其方形子矩阵已经可逆。因全部列缩放系数非零，对任意所选不同角都有

$$
\operatorname{rank}A=\min(k,2n+1),\qquad
\operatorname{rank}DH(a_0)=d,
\qquad d:=k+\min(k,2n+1)=\min(2k,2n+k+1).
$$

把输出转到实际仿射实坐标，令

$$
F(a)=(u_1(a),v_1(a),\ldots,u_k(a),v_k(a)),\qquad
u_j(a)=R_j(a)\cos\varphi_j,\qquad
v_j(a)=R_j(a)\sin\varphi_j.
$$

每个从 $(r_j,\varphi_j)$ 到 $(u_j,v_j)$ 的微分块为

$$
\begin{pmatrix}
\cos\varphi_j&-r_j\sin\varphi_j\\
\sin\varphi_j&r_j\cos\varphi_j
\end{pmatrix},\qquad \det=r_j>0.
$$

故 $\operatorname{rank}DF(a_0)=d$。记 $m=2n+1+k$，在这个实际的 $2k\times m$ 实 Jacobian 中选定输出坐标指标集 $I\subseteq\{1,\ldots,2k\}$ 和输入坐标指标集 $J\subseteq\{1,\ldots,m\}$，各有 $d$ 个元素，按递增顺序排列，使

$$
\det\bigl(DF(a_0)_{I,J}\bigr)\ne0.
$$

这样的子式由刚算出的秩保证存在。固定此选择，将所有不在 $J$ 中的输入坐标冻结为 $a_0$ 的相应值。以 $h\in\mathbb R^d$ 表示剩余坐标，记此坐标嵌入为 $\iota_J(h)$，$h_0=(a_0)_J$，并置

$$
F_J=F\circ\iota_J,\qquad
q_I:\mathbb R^{2k}\longrightarrow\mathbb R^d,\qquad
q_I(w)=(w_i)_{i\in I}.
$$

这里 $w$ 按 $F$ 的输出次序排列，$I$ 中的坐标按已选顺序读取。限制到 $h_0$ 的小开邻域，使 $\iota_J(h)\in\mathcal V$。映射 $\psi=q_I\circ F_J$ 在 $h_0$ 的导数为可逆矩阵 $DF(a_0)_{I,J}$。实光滑逆函数定理给出非空开邻域 $V\subseteq\mathbb R^d$、$O\subseteq\mathbb R^d$，使 $\psi:V\to O$ 为微分同胚。定义

$$
\gamma=F_J\circ\psi^{-1}:O\longrightarrow\mathbb R^{2k},
\qquad q_I\circ\gamma=\operatorname{id}_O.
$$

将输出坐标按 $I$ 及其补集重排，便有 $\gamma(a)=(a,g(a))$，其中 $g:O\to\mathbb R^{2k-d}$ 光滑。这是一个真正的嵌入光滑图像，其逆由仿射坐标投影 $q_I$ 给出；它的每一点均由前面的完整记录协议实现。

当 $k\le2n+1$ 时，$d=2k$，$I$ 包含全部输出坐标，故这个图像在配置仿射图内开，从而给出 $\mathcal D_k$ 中的非空相对开成功子集。当 $k\ge2n+1$ 时，$d=m=2n+1+k$，$J$ 包含全部输入坐标，无须冻结任何输入；缩小后的整个局部参数族因而给出所述 $2n+k+1$ 维嵌入流形片。这一坐标图中的参数唯一性只针对所选局部族。

最后把这个光滑图像用于半代数集合 $\mathcal E_{k,n}$ 的维数下界。在每个射线因子的仿射图中，$[1:u+iv]$ 与 Bloch 球图的对应为

$$
(u,v)\longmapsto
 \frac{(2u,2v,1-u^2-v^2)}{1+u^2+v^2},
\qquad
(u,v)=\left(\frac{X_1}{1+X_3},\frac{X_2}{1+X_3}\right)
\quad(X_3\ne-1).
$$

这是双向有理的半代数光滑坐标变换。记 $\mathcal D_k^{\mathrm{aff}}\subseteq\mathbb R^{2k}$ 为不同点配置的仿射代表，$\mathcal E_{k,n}^{\mathrm{aff}}$ 为 $\mathcal E_{k,n}$ 在此图内的代表。定理 411.1 的半代数性给出 $\mathcal E_{k,n}^{\mathrm{aff}}$ 半代数；上述构造给出 $\gamma(O)\subseteq\mathcal E_{k,n}^{\mathrm{aff}}$。

在 $F(a_0)\in\mathcal D_k^{\mathrm{aff}}$ 周围选一个足够小的开欧氏球 $B$，使 $B\subseteq\mathcal D_k^{\mathrm{aff}}$。$B$ 是半代数集。由 $\gamma$ 的连续性，可再缩小包含 $q_I(F(a_0))$ 的非空开集 $O$，使 $\gamma(O)\subseteq B$。于是

$$
O\subseteq q_I\bigl(\mathcal E_{k,n}^{\mathrm{aff}}\cap B\bigr)
 \subseteq\mathbb R^d.
$$

投影的对象是已知半代数的 $\mathcal E_{k,n}^{\mathrm{aff}}\cap B$。由 Tarski–Seidenberg 定理，其投影仍为半代数集；因为它包含 $\mathbb R^d$ 的非空开集，维数恰为 $d$。再由投影不增维、子集单调性及半代数坐标变换的维数不变性，得到

$$
d=\dim_{\mathbb R}q_I\bigl(\mathcal E_{k,n}^{\mathrm{aff}}\cap B\bigr)
 \le\dim_{\mathbb R}\bigl(\mathcal E_{k,n}^{\mathrm{aff}}\cap B\bigr)
 \le\dim_{\mathbb R}\mathcal E_{k,n}.
$$

这里沿用定理 411.1 引用的 Basu–Pollack–Roy，[*Algorithms in Real Algebraic Geometry*, 作者发布稿](https://www.math.purdue.edu/~sbasu/bpr-posted1.pdf)：Theorem 2.76（第 76 页）的投影定理，以及 Theorem 5.25、Propositions 5.28–5.29、Lemma 5.30（第 178–180 页）的维数规则。上述推论只需要 $\gamma$ 为光滑图像，不要求角参数映射 $H,F$ 或 $\gamma(O)$ 半代数。

另一方面，定理 411.1 与环境维数分别给出

$$
\dim_{\mathbb R}\mathcal E_{k,n}\le2n+k+1,
\qquad
\dim_{\mathbb R}\mathcal E_{k,n}\le\dim_{\mathbb R}\mathcal D_k=2k.
$$

与下界合并即得所述精确维数。特别地，$k=2n+1$ 时

$$
d=m=2k=2n+k+1,
$$

局部映射本身为到开配置邻域的微分同胚，两个局部结论在此一致。若 $k\ge2n+2$，构造的流形片维数为 $2n+k+1<2k$，与定理 411.1 中开稠密失败集及成功集零环境测度相容。归一化见证的变形提供至 $n$ 次的径向 Fourier 模态，$k$ 个角坐标同时独立变化；非零仿射子式将这些自由度实现为实际成功配置的局部图像。证毕。

## 追加锚（本行以下为增补区）

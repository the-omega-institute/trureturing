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

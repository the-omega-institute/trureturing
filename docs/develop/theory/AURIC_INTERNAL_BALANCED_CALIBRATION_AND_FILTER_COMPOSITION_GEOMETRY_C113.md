**AURIC 量子关系研究续篇**

# 内部均衡校准 与滤波组合几何

**候选 C113：有限同向比较的饱和约束**

**核心结果**

固定一个成功效果，在一组有限且二阶均衡的内部输入上，平均同向读回强度达到其关系上界，当且仅当更新为平方根滤波。规范滤波的非交换接续进一步产生由历史顺序唯一确定的旋转；在 qubit 中，旋转轴正是两个滤片方向的叉积。

**版本与证据**

本稿承接用户提供的 v98 讨论，并按本轮核定仓库的 C112 接号为 C113；C113 是本轮候选编号。固定仓库基准：

`40e161f1b410721daad15d8ceaad34c3d7e19759`

该提交时间为 2026 年 11 月 3 日 17:14:18（新加坡时间）。读取的 C112 位于 V96 续篇的第 106–112 节，文件名中的 V96 不代表候选尚停留在 C96。

**证明范围**

有限维复量子对象上的纸笔理论；同时处理奇异效果、一般多 Kraus 分支、有限直和中心泄漏、误差界、顺序组合与三维几何。核心平均最优性与有限二阶设计方法已有成熟文献，本稿将其组织成项目的内部关系候选，不作原创优先权声明。仓库既有重建结果与本稿重新证明的结果分开标明。

2026 年 11 月 3 日

## 目录

- [1. 从最新仓库定位本轮问题](#section-1)
- [2. 有限内部关系与完整候选 C113](#section-2)
- [3. 主定理：有限平均关系唯一选出平方根更新](#section-3)
- [4. 有限校准在每个维数中都可明确构造](#section-4)
- [5. 按删除条件反推：每个条件到底排除了什么](#section-5)
- [6. 误差界、稀有成功与维数边界](#section-6)
- [7. 有限直和与中心泄漏](#section-7)
- [8. 二元关系怎样有限提升到三维](#section-8)
- [9. 两个规范滤片为何生成顺序旋转](#section-9)
- [10. 一个可逐式核验的双滤片例子](#section-10)
- [11. 更大的几何：正锥、双曲空间与交换子](#section-11)
- [12. 怎样从关系体系接回量子力学公理](#section-12)
- [13. 把校准、筛选与记录放进同一个静态整体](#section-13)
- [14. 完整白话描述与下一步精确问题](#section-14)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 从最新仓库定位本轮问题

固定提交的主卷第 33–49 节发展 C101–C103：对象的复矩阵表示、实际过程的完全正性、共同活动标尺；续篇第 106–112 节给 C112：在同一实际滤波族上，精确倒数补偿返回 R、半程拼接 H 与严格同向读数阈值共同选出平方根更新。原文也保留了全效果量词、实际过程供应及带噪边界 [1](#ref-repo-main)、[2](#ref-repo-cont)。

本轮的问题是：**能否只在一个给定滤片自己的有限内部校准关系上，选出它的更新规则，而不先要求实际倒数补偿及沿全效果平方链寻找有限见证？**

答案是可以，但需要另一种明确前提：有限输入的二阶均衡，以及一个精确的平均饱和关系。它与 C112 的假设安排不同，不能直接挪用 C112 或 C111 的误差常数。随后考察一个更深的组合问题：单个滤片规范，并不意味着它们的复合仍是规范正滤波；其中确定的旋转正是历史信息的一种载体。

**白话。**先问一个滤片本身有没有偷偷丢掉额外的相干细节，再问两片先后通过时留下了什么关系。第一问选出规范更新，第二问显露顺序与曲率。

<a id="section-2"></a>

## 2. 有限内部关系与完整候选 C113

### 定义 2.1（一个成功分支）

先在同一个有限维块 $H=\mathbb C^d$ 中工作。效果为 $0\le E\le I$，实际成功分支 $T:M_d\to M_d$ 完全正，并满足

<a id="eq-effect"></a>

$$
T^*(I)=E,\qquad
T(X)=\sum_{\mu=1}^m K_\mu X K_\mu^*,\qquad
\sum_\mu K_\mu^*K_\mu=E.
\tag{1}
$$

星号在映射上表示通常迹伴随。成功效果也可直接定义为 $E:=T^*(I)$；如果 $E$ 已有标签，式 [(1)](#eq-effect) 就是两种定义的一致性。

完全正性在项目中由 C102 的过程延伸关系承担，本轮不把它重复认领为新结论。所选滤波只是实际过程菜单的一部分，一般有噪量子通道无需满足下面的选择约束。

### 定义 2.2（有限二阶均衡校准）

取有限个秩一投影 $p_s=\lvert \psi_s\rangle\langle \psi_s\rvert$ 与正权 $w_s$，$\sum_sw_s=1$，满足

<a id="eq-design"></a>

$$
\sum_s w_s p_s\otimes p_s=\frac{I+\mathsf S}{d(d+1)},
\qquad \mathsf S(x\otimes y)=y\otimes x.
\tag{2}
$$

这称为加权复射影二阶设计。式 [(2)](#eq-design) 是校准关系的代数描述；实际试验只需逐次准备 $p_s$、通过同一个 $T$、二元读取 $p_s$。公式中的张量写法不要求把未知态复制两份。

定义两种同向读数

<a id="eq-readouts"></a>

$$
r_E(p)=\operatorname{Tr}[pT(p)],\qquad a_E(p)=\operatorname{Tr}(p\sqrt E),
\tag{3}
$$

以及平均值

<a id="eq-means"></a>

$$
R_{\mathscr D}(T)=\sum_sw_sr_E(p_s),\qquad
Q_{\mathscr D}(E)=\sum_sw_sa_E(p_s)^2.
\tag{4}
$$

$r_E$ 是成功并沿原方向读回的联合概率；$a_E$ 是对半深效果 $\sqrt E$ 的成功评价，其更新方式并未预设。平方 $a_E^2$ 是数的乘积。平均在成功条件化之前进行。

### 定义 2.3（候选 C113：有限均衡同向饱和）

保留 C101–C103 的实际对象与过程关系。对每个所选效果及其同一个实际成功分支，供应一组有限校准 [(2)](#eq-design) 及相关读口，要求

<a id="eq-c113"></a>

$$
\boxed{
R_{\mathscr D}(T)\ge Q_{\mathscr D}(E).
}\tag{C113}
$$

有限直和对象逐个输入简单块实施该关系，允许输出最初可能向其他块泄漏，具体见第 [7](#sec-directsum) 节。零效果不额外测试。

候选定义中没有写入 $T(X)=\sqrt E X\sqrt E$。后面将证明普遍上界反向成立，因此 C113 正好要求达到一个由效果和有限比较共同决定的上界。

**白话。**先规定这片滤片在各个方向留下多少。再用一组没有方向偏好的有限输入，比较“通过后还能沿原方向读回多少”和“由半深效果本身给出的比较值”。要求两者达到同一个界，就把额外的转动与额外的未读记录排除了。

<a id="section-3"></a>

## 3. 主定理：有限平均关系唯一选出平方根更新

### 定理 3.1（平均上界、等号与唯一性）

<a id="thm-main"></a>

在上述前提下，令 $A=\sqrt E$。则

<a id="eq-mean-r"></a>

$$
\begin{aligned}
R_{\mathscr D}(T)&=\frac{\operatorname{Tr} E+\sum_\mu|\operatorname{Tr} K_\mu|^2}{d(d+1)},
\end{aligned}
\tag{5}
$$

<a id="eq-mean-q"></a>

$$
\begin{aligned}
Q_{\mathscr D}(E)&=\frac{\operatorname{Tr} E+(\operatorname{Tr} A)^2}{d(d+1)},
\end{aligned}
\tag{6}
$$

<a id="eq-upper"></a>

$$
\begin{aligned}
R_{\mathscr D}(T)&\le Q_{\mathscr D}(E).
\end{aligned}
\tag{7}
$$

等号成立当且仅当

<a id="eq-luders"></a>

$$
\boxed{T(X)=A X A.}
\tag{8}
$$

因此 C113 与所选分支的平方根更新完全等价，包括奇异 $E$。

**证明。**
由二阶矩公式，对任意矩阵 $K$，

<a id="eq-moment"></a>

$$
\sum_s w_s|\langle \psi_s\rvert K\lvert \psi_s\rangle|^2
=\frac{\operatorname{Tr} K^*K+|\operatorname{Tr} K|^2}{d(d+1)}.
\tag{9}
$$

可直接把 $K\otimes K^*$ 与 [(2)](#eq-design) 配对，使用
$\operatorname{Tr}[(B\otimes C)\mathsf S]=\operatorname{Tr}(BC)$。代入各 Kraus 算子即得 [(5)](#eq-mean-r)；代入 $K=A$ 得 [(6)](#eq-mean-q)。

下面给不使用最小正谱值逆的等号证明。在 $A$ 的本征基中，设
$A e_j=\lambda_j e_j$，$\lambda_j\ge0$，并将各 Kraus 算子的第 $j$ 个对角元合成向量

$$
v_j=(\langle e_j\rvert K_\mu\lvert e_j\rangle)_{\mu=1}^m\in\mathbb C^m.
$$

正确成功效果给

$$
\|v_j\|^2\le\sum_\mu\|K_\mu e_j\|^2
=\langle e_j\rvert E\lvert e_j\rangle=\lambda_j^2.
$$

于是

<a id="eq-triangle"></a>

$$
\sum_\mu|\operatorname{Tr} K_\mu|^2
=\Big\|\sum_jv_j\Big\|^2
\le\Big(\sum_j\|v_j\|\Big)^2
\le\Big(\sum_j\lambda_j\Big)^2.
\tag{10}
$$

这证明上界。

若 $E\ne0$ 且等号成立，每个 $\|v_j\|=\lambda_j$，且所有非零 $v_j$ 沿同一个复向量的正向排列。因此存在单位向量 $c=(c_\mu)$，使 $v_j=\lambda_jc$。第一个不等式也处处饱和，故每个 $K_\mu e_j$ 没有 $e_j$ 以外的分量。于是

$$
K_\mu=c_\mu A,\qquad \sum_\mu|c_\mu|^2=1,
$$

从而 $T(X)=AXA$。若 $E=0$，[(1)](#eq-effect) 已迫使全部 Kraus 算子为零。反向代入 $T=\mathcal L_E$ 即得等号。

### 说明 3.2（数学归属与本稿工作）

固定测量下平方根更新的平均最优性、多 Kraus 证明及有限二阶设计连接，已有 Barnum 的定理与附录证明 [3](#ref-barnum)；平均操作保真度也见 Banaszek [4](#ref-banaszek)。本稿的新候选是把这些成熟结果组织为当前项目的有限内部定义约束，并明确其等号、泄漏、误差、组合与供应范围。这里不宣称发现了新的最小扰动原理。

### 推论 3.3（此前的规范滤波关系成为后果）

若相应效果与接续实际供应，则 C113 推出共同调暗、框架无关、迹互易、半程拼接及补偿返回：

$$
\mathcal L_{aE}=a\mathcal L_E,\qquad
\operatorname{Tr}[B\mathcal L_E(C)]=\operatorname{Tr}[C\mathcal L_E(B)],
\tag{11}
$$

$$
\mathcal L_E=\mathcal L_{\sqrt E}^{\,2},\qquad
\mathcal L_{E^\vee}\mathcal L_E(X)=q_E X\quad(X\in P_E M_dP_E),
\tag{12}
$$

其中 $P_E=\operatorname{supp} E$，$q_E$ 为最小正本征值，$E^\vee=q_E E^\dagger$。后一公式不自动供应实际补偿装置。

**证明。**
依次使用正平方根的标量齐次性、迹循环性、$\sqrt{\sqrt E}=E^{1/4}$ 及 $\sqrt{E^\vee}\sqrt E=\sqrt{q_E}P_E$。

<a id="section-4"></a>

## 4. 有限校准在每个维数中都可明确构造

### 定理 4.1（任意维数的显式有限设计）

<a id="thm-design"></a>

选正交基 $e_1,\ldots,e_d$。取 $d$ 个基射线，每个权重 $1/[d(d+1)]$；再取

$$
\psi_z=\frac{e_1+z_2e_2+\cdots+z_de_d}{\sqrt d},
\qquad z_j\in\{1,i,-1,-i\},
$$

每个权重 $d/[(d+1)4^{d-1}]$。这 $d+4^{d-1}$ 个带权射线满足 [(2)](#eq-design)，重复射线可以合并。

**证明。**
先让全部 $d$ 个相位独立均匀取四次单位根。除去共同相位不改变射线，所得分布等于固定第一个相位为一的上述分布。四阶矩中只有配对项保留，故平幅射线的均值为

$$
\mathbb E(p_z\otimes p_z)
=\frac{I+\mathsf S-\sum_j\lvert jj\rangle\langle jj\rvert}{d^2}.
$$

平幅部分总权重为 $d/(d+1)$，基射线部分总权重为 $1/(d+1)$；两者的 $\lvert jj\rangle\langle jj\rvert$ 修正正好抵消，得到 [(2)](#eq-design)。

对 $d=2$，正好得到六条 Pauli 方向，各权 $1/6$：

$$
\lvert 0\rangle,\lvert 1\rangle,\quad
\lvert \pm\rangle=\frac{\lvert 0\rangle\pm\lvert 1\rangle}{\sqrt2},\quad
\lvert \pm i\rangle=\frac{\lvert 0\rangle\pm i\lvert 1\rangle}{\sqrt2}.
$$

一般维数的构造只证明有限存在，不主张实验数最优；实际准备和读口仍须包含在模型的内部菜单中。对一个效果的有限刻画，也不等于用有限个效果标签认证整个无限效果族。

<a id="section-5"></a>

## 5. 按删除条件反推：每个条件到底排除了什么

### 例 5.1（只检验一个基底会丢掉相干）

令 $E=I_2$，比较恒等通道与去相干通道

$$
\mathcal Z(X)=p_0Xp_0+p_1Xp_1.
$$

在 $p_0,p_1$ 上同向读数都为一，因此一阶均衡基底检查无法区分二者。六方向均衡平均中，恒等通道得一，$\mathcal Z$ 得 $2/3$，其相干损失被看见。

### 例 5.2（单方向最优不是本候选）

取 $E=p_0$，输入 $p_+=\lvert +\rangle\langle +\rvert$。规范分支给 $\operatorname{Tr}[p_+\mathcal L_E(p_+)]=1/4$；同效果的重新准备分支

$$
T(X)=\lvert +\rangle\langle 0\rvert X\lvert 0\rangle\langle +\rvert
$$

却给 $1/2$。但它们在真正二阶设计上的平均分别是 $1/3$ 和 $1/4$。所以平方根滤波最大化的是指定均衡平均，不是对每个输入都逐点最大。

### 例 5.3（成功效果与同一实现都必须保留）

若标签写 $E=\lambda I$，$0<\lambda<1$，却允许实际过程取 $T=\operatorname{id}$，则平均不等式通过，成功效果却错误。若针对每个探针另换一个 $T_s(X)=\operatorname{Tr}(EX)p_s$，则每项读数也可被单独迎合；它们不是同一个被校准过程。候选的量词是同一个 $T$ 作用于整组校准。

### 例 5.4（只有正确概率不决定后态）

恒等与去相干通道的成功效果同为 $I$。因此全部成功概率相同，仍不决定成功后的相干内容。C113 正是补上所选滤波这部分结构。

**白话。**只看“通过了多少”会漏掉后态，只看一组互相正交的输入会漏掉相干，只看一个有利方向会偏袒某个过程。必须让同一个滤片面对一整组真正均衡的关系，才能把这些自由一起锁住。

<a id="section-6"></a>

## 6. 误差界、稀有成功与维数边界

### 定理 6.1（接近饱和控制整个过程）

<a id="thm-stability"></a>

令

$$
\delta=Q_{\mathscr D}(E)-R_{\mathscr D}(T)\ge0,
\quad D=d(d+1)\delta,\quad M=\|E\|.
$$

则

<a id="eq-robust"></a>

$$
\boxed{
\|T-\mathcal L_E\|_\diamond
\le\min\{2M,\ 2\sqrt{2M d(d+1)\delta}\}.
}
\tag{13}
$$

这里 $\|\Phi\|_\diamond=\sup_{n,X\ne0}\|(\Phi\otimes\operatorname{id}_{M_n})(X)\|_1/\|X\|_1$，包括任意数学参考系统。该界不含最小正本征值的倒数，不主张常数最优。

**证明。**
$E=0$ 时显然。令 $A=\sqrt E$，$P=\operatorname{supp} E$，$s=\operatorname{Tr} A$，$V_\mu=K_\mu A^\dagger$。则 $\sum_\mu V_\mu^*V_\mu=P$。设 $t_\mu=\operatorname{Tr} K_\mu$，$z=\sum_\mu|t_\mu|^2=s^2-D$。选择单位向量 $c$ 与 $t$ 同向；$t=0$ 时任取单位 $c$。加权平方差恒等式为

$$
\sum_\mu\|(V_\mu-c_\mu P)A^{1/2}\|_\mathrm{HS}^2
=2(s-\sqrt z).
$$

因此

$$
\begin{aligned}
\sum_\mu\|K_\mu-c_\mu A\|_\mathrm{HS}^2
&\le 2\|A\|(s-\sqrt z)\\
&=\frac{2\|A\|D}{s+\sqrt z}\le2D.
\end{aligned}
$$

将 $K_\mu$ 与 $c_\mu A$ 分别堆成 Stinespring 算子 $W,W_0$，两者算符范数都是 $\sqrt M$，且 $\|W-W_0\|\le\sqrt{2D}$。在任意参考扩张后，展开
$W XW^*-W_0XW_0^*$，再对环境取偏迹，可得

$$
\|T-\mathcal L_E\|_\diamond
\le(\|W\|+\|W_0\|)\|W-W_0\|
\le2\sqrt{2MD}.
$$

另由两个完全正分支的 diamond 范数均为 $M$，得到 $2M$ 上界。

### 命题 6.2（平方根误差阶与维数不能任意去除）

对 qubit，取 $E=I$、$T=\operatorname{Ad}_{e^{-itZ/2}}$，$|t|\le\pi$。则

$$
\delta=\frac23\sin^2(t/2),\qquad
\|T-\operatorname{id}\|_\diamond=2|\sin(t/2)|=\sqrt{6\delta}.
$$

因此一般不能把误差阶改成 $o(\sqrt\delta)$。另一方面，对 $d\ge2$，取
$U_d=\operatorname{diag}(-1,1,\ldots,1)$，有

$$
\|\operatorname{Ad}_{U_d}-\operatorname{id}\|_\diamond=2,
\qquad\delta_d=\frac{4(d-1)}{d(d+1)}\longrightarrow0.
$$

维数增长时的小平均缺陷不能单独控制最坏过程误差。

**证明。**
平均公式由 [(5)](#eq-mean-r) 直接计算。酉通道与恒等的 diamond 距离等于单位圆数值域距原点所给的 $2\sqrt{1-\nu^2}$：可将任意带参考纯输入的重叠写成 $\operatorname{Tr}(\rho U)$，极小化即得。qubit 两本征相位相差 $t$ 时 $\nu=|\cos(t/2)|$；$U_d$ 的两个相反相位可由等权叠加完全区分。

单次成功概率 $p=\operatorname{Tr}(\rho E)>0$ 在两种分支中相同，因此

$$
\left\|\frac{T(\rho)}p-\frac{\mathcal L_E(\rho)}p\right\|_1
\le\min\left\{2,\frac{\|T-\mathcal L_E\|_\diamond}{p}\right\}.
\tag{14}
$$

不能省去这里的 $p$。例如 $E_\epsilon=\operatorname{diag}(1,\epsilon^2)$、$T=\operatorname{Ad}_Z\mathcal L_E$，则平均缺陷 $2\epsilon/3\to0$，但输入

$$
\psi_\epsilon=\frac{\epsilon\lvert 0\rangle+\lvert 1\rangle}{\sqrt{1+\epsilon^2}}
$$

以概率 $2\epsilon^2/(1+\epsilon^2)$ 成功，两个成功后态分别为 $\lvert -\rangle$ 与 $\lvert +\rangle$，迹范数距离为二。

**白话。**有限平均读数几乎达到上界，就能控制整个未归一化过程的误差。极少发生的成功事件却会放大条件误差；维数很大时，平均也可能掩盖一小块方向上的大错误。这里两种边界都保留在公式里。

<a id="section-7"></a>

## 7. 有限直和与中心泄漏

<a id="sec-directsum"></a>

项目原对象为 $\mathcal A=\bigoplus_\alpha M_{d_\alpha}(\mathbb C)$。不能把不同中心扇区当成已允许相干叠加的一个纯态球；校准应逐个简单输入块进行。

令 $J:H_\alpha\to H_{\rm out}$ 为同一扇区的嵌入，分支在该输入块的矩形 Kraus 算子为 $K_\mu$，满足 $\sum K_\mu^*K_\mu=E_\alpha$。置 $B_\mu=J^*K_\mu$。同扇区平均读回为

$$
R_\alpha=\frac{\sum_\mu\|B_\mu\|_\mathrm{HS}^2+
\sum_\mu|\operatorname{Tr} B_\mu|^2}{d_\alpha(d_\alpha+1)}.
$$

与该块效果的比较值之差分解为

<a id="eq-leak"></a>

$$
\begin{aligned}
d_\alpha(d_\alpha+1)\delta_\alpha
={}&\underbrace{\operatorname{Tr} E_\alpha-\sum_\mu\|B_\mu\|_\mathrm{HS}^2}_{\ell_\alpha\ge0}
\\[-2mm]&+\underbrace{(\operatorname{Tr}\sqrt{E_\alpha})^2-
\sum_\mu|\operatorname{Tr} B_\mu|^2}_{h_\alpha\ge0}.
\end{aligned}
\tag{15}
$$

第一项是输出泄漏，第二项由前述迹 Cauchy–Schwarz 或对角向量证明非负。零缺陷使两项都为零：全部输出留在原扇区，且 $K_\mu=c_\mu J\sqrt{E_\alpha}$。因此逐块 C113 迫出全代数上的平方根更新，而没有预先假设中心不动。

误差证明中将 $V_\mu-c_\mu P$ 换成 $V_\mu-c_\mu JP$，并用
$s^2-z\le d_\alpha(d_\alpha+1)\delta_\alpha$，得到同样的块内界。直和输入没有跨中心相干，整映射的 diamond 距离为各输入块距离的最大值。

<a id="section-8"></a>

## 8. 二元关系怎样有限提升到三维

主证明中的每一条 Cauchy–Schwarz 关系都有一个准确的 Bloch 图景。令 $E\ne0$、$A=\sqrt E$、$s=\operatorname{Tr} A$、$V_\mu=K_\mu A^\dagger$，并定义

$$
b_\mu=\operatorname{Tr}(V_\mu A V_\mu^*),\qquad\sum_\mu b_\mu=s.
$$

对 $b_\mu>0$，在 Hilbert–Schmidt 内积空间中取两个单位向量

$$
u=\frac{A^{1/2}}{\sqrt s},\qquad
v_\mu=\frac{V_\mu A^{1/2}}{\sqrt{b_\mu}},\qquad
z_\mu=\langle u,v_\mu\rangle=\frac{\operatorname{Tr} K_\mu}{\sqrt{s b_\mu}}.
$$

归一化二元 Gram 矩阵为

$$
\Gamma_\mu=\frac12
\begin{pmatrix}1&z_\mu\\\overline z_\mu&1\end{pmatrix}
=\frac12(I+\mathbf g_\mu\cdot\boldsymbol\sigma),
\quad\mathbf g_\mu=(\Re z_\mu,-\Im z_\mu,0).
\tag{16}
$$

其正性等价于 $|\mathbf g_\mu|\le1$，且

$$
\boxed{
(\operatorname{Tr} A)^2-\sum_\mu|\operatorname{Tr} K_\mu|^2
=s\sum_\mu b_\mu(1-|\mathbf g_\mu|^2).
}
\tag{17}
$$

因此平均饱和使每个有权二元比较到达球面，即两个 Hilbert–Schmidt 向量平行。Kraus 表示中的相位自由被保留，CP 更新则唯一。

这与 v98 的正相干比较有联系，也有范围差别：CP 分支没有确定一个受控实现的全部相对相位。若要比较两种实现的相干相位，必须保留相应仪器、环境与记录结构。

### 说明 8.1（一族三维图景不等于整体只有三维）

这里每个二元 Gram 都是一个三维球内点。多个二元图景同时来自同一整体，仍需要共同的高维正性。矩阵

$$
G=\begin{pmatrix}1&-3/4&-3/4\\-3/4&1&-3/4\\-3/4&-3/4&1\end{pmatrix}
$$

的每个二阶主块都为正，但 $G(1,1,1)^T=-\tfrac12(1,1,1)^T$。所以两两合法不能代替共同 Gram 正性。C113 使用同一个 CP 过程及同一组二阶矩，恰保留了这种整体约束。

**白话。**每一条比较都可以放进一个小球。差额就是它离饱和边界还剩多少；所有带权差额同时归零，更新便被锁定。多个小球如何属于同一个整体，仍由同一个过程与共同正性来负责。

<a id="section-9"></a>

## 9. 两个规范滤片为何生成顺序旋转

### 定理 9.1（顺序滤波的唯一极分解）

<a id="thm-polar"></a>

设 $A=\sqrt E>0$、$B=\sqrt F>0$，$E,F\le I$。先 $E$ 后 $F$ 的成功算子为 $K=BA$，总成功效果为

$$
G=K^*K=AB^2A=\sqrt E F\sqrt E.
$$

有唯一分解

<a id="eq-polar"></a>

$$
\boxed{
BA=U_{F,E}\sqrt G,\qquad U_{F,E}=BA(AB^2A)^{-1/2}.
}
\tag{18}
$$

$U_{F,E}$ 酉，且以下条件等价：$AB=BA$；$U_{F,E}=I$；实际顺序分支等于 $\mathcal L_G$。

**证明。**
置 $C=\sqrt G$，则 $U^*U=C^{-1}K^*KC^{-1}=I$。若 $K=VD$、$V$ 酉且 $D>0$，由 $D^2=K^*K$ 得 $D=C$、$V=U$，故唯一。若 $A,B$ 交换，$BA$ 正；反向 $BA$ 正使 $BA=(BA)^*=AB$。

若两个单 Kraus 分支相同，则 $K=e^{i\phi}C$。因为 $\operatorname{Tr} BA>0$ 且 $\operatorname{Tr} C>0$，相位只能为一。由此得到全部等价。

两种过程具有同一成功概率 $\operatorname{Tr}(\rho G)$，但输出分别为 $UC\rho CU^*$ 与 $C\rho C$。若强行规定全部顺序组合也必须等于其总效果的规范滤波，就迫使全部所选正滤片两两交换。这会排除通常量子理论的不交换效果菜单。

奇异效果时仍有极分解，但唯一的是初始支持上的部分等距映射，不能把它扩大为唯一完整酉门。反转两片次序时，严格正情形的极酉部分变为 $U^*$。

### 9.1 qubit 中的点积、叉积与手性

写

$$
A=a_0I+\mathbf a\cdot\boldsymbol\sigma>0,\qquad
B=b_0I+\mathbf b\cdot\boldsymbol\sigma>0.
$$

定义

$$
c_0=a_0b_0+\mathbf a\cdot\mathbf b>0,
\quad\mathbf c=a_0\mathbf b+b_0\mathbf a,
\quad\mathbf d=\mathbf b\times\mathbf a.
$$

Pauli 乘法给 $BA=c_0I+(\mathbf c+i\mathbf d)\cdot\boldsymbol\sigma$。

### 定理 9.2（两个方向决定第三个旋转轴）

式 [(18)](#eq-polar) 的酉部分为

<a id="eq-qubit-u"></a>

$$
\boxed{
U_{F,E}=\frac{c_0I+i\mathbf d\cdot\boldsymbol\sigma}
{\sqrt{c_0^2+|\mathbf d|^2}}.
}
\tag{19}
$$

若 $\mathbf d\ne0$，Bloch 旋转角大小满足

$$
\tan\frac{|\Theta|}{2}
=\frac{|\mathbf b\times\mathbf a|}{a_0b_0+\mathbf a\cdot\mathbf b}.
$$

若 $U=e^{i\eta\widehat{\mathbf d}\cdot\boldsymbol\sigma}$，Bloch 旋转为绕 $\widehat{\mathbf d}$ 的角 $-2\eta$。

**证明。**
设 $L=\sqrt{c_0^2+|\mathbf d|^2}$。候选 $U$ 满足 $U^*U=I$、$\det U=1$。因 $\mathbf c\cdot\mathbf d=0$，直接计算

$$
U^*BA=LI+\frac{c_0\mathbf c+\mathbf d\times\mathbf c}{L}\cdot\boldsymbol\sigma.
$$

它自伴、迹为 $2L>0$，行列式为 $\det A\det B>0$，所以严格正。极分解唯一性给出公式。

**白话。**一个滤片按一个方向改变份量，另一个滤片按另一个方向改变份量。两个方向不共线时，它们的先后差别产生一个法向，这个法向正是旋转轴。每片都没有额外拧转，合起来却能留下顺序旋转；它由关系的组合确定。

<a id="section-10"></a>

## 10. 一个可逐式核验的双滤片例子

取

$$
A=\frac{3I+Z}{4}=\begin{pmatrix}1&0\\0&1/2\end{pmatrix},
\qquad B=\frac{3I+X}{4}=\frac14\begin{pmatrix}3&1\\1&3\end{pmatrix}.
$$

它们都是严格正收缩，分别为效果 $A^2,B^2$ 的规范滤片。直接计算

$$
\begin{aligned}
K=BA&=\frac18\begin{pmatrix}6&1\\2&3\end{pmatrix},
&G&=\frac1{32}\begin{pmatrix}20&6\\6&5\end{pmatrix},
\end{aligned}
\tag{20}
$$

$$
\begin{aligned}
C=\sqrt G&=\frac1{4\sqrt{82}}\begin{pmatrix}28&6\\6&13\end{pmatrix},
&U&=\frac1{\sqrt{82}}\begin{pmatrix}9&-1\\1&9\end{pmatrix}.
\end{aligned}
\tag{21}
$$

确有 $K=UC$。输入 $\lvert 0\rangle$ 时，两种过程的成功概率同为 $5/8$，成功后态分别为

$$
\psi_{\rm seq}=\frac{3\lvert 0\rangle+\lvert 1\rangle}{\sqrt{10}},\qquad
\psi_{\rm can}=\frac{14\lvert 0\rangle+3\lvert 1\rangle}{\sqrt{205}}.
$$

Bloch 向量为

$$
\mathbf r_{\rm seq}=(3/5,0,4/5),\qquad
\mathbf r_{\rm can}=(84/205,0,187/205).
$$

两者绕 $+y$ 相差角 $\Theta=2\arctan(1/9)$，迹距离为 $1/\sqrt{82}$。后续读取 $p_0$ 的条件概率分别是 $9/10$ 与 $196/205$。反转滤片次序使极酉变为 $U^*$，同一输入的成功概率变为 $37/64$。

```latex
\begin{tikzpicture}[>=Stealth,scale=1]
\begin{scope}[shift={(-3.6,0)}]
\draw[gray!45] (0,0) circle (1.45);
\draw[gray!25] (0,0) ellipse (1.45 and 0.4);
\draw[->,thick] (-1.8,0)--(1.8,0) node[right] {$x$};
\draw[->,thick] (0,-1.8)--(0,1.8) node[above] {$z$};
\draw[->,thick] (-0.95,-0.7)--(0.95,0.7) node[above right] {$y$};
\foreach \x/\y in {1.45/0,-1.45/0,0/1.45,0/-1.45,0.75/0.55,-0.75/-0.55}{\fill[teal!75!black] (\x,\y) circle (0.065);}
\node[align=center,text width=5.7cm] at (0,-2.4) {六个校准方向，各权 $1/6$\\球面投影示意};
\end{scope}
\begin{scope}[shift={(3.3,0)},scale=1.55]
\draw[gray!45] (0,0) circle(1);
\draw[->] (-1.15,0)--(1.22,0) node[right] {$x$};
\draw[->] (0,-1.15)--(0,1.2) node[above] {$z$};
\draw[->,very thick,teal!75!black] (0,0)--({84/205},{187/205});
\draw[->,very thick,orange!85!black] (0,0)--(0.6,0.8);
\fill[teal!75!black] ({84/205},{187/205}) circle(0.035);
\fill[orange!85!black] (0.6,0.8) circle(0.035);
\draw[->,thick] ({0.67*84/205},{0.67*187/205}) arc[start angle={atan2(187,84)},end angle={atan2(4,3)},radius=0.67];
\node[font=\small] at (0.43,0.53) {$\Theta$};
\node[teal!75!black,anchor=south east,font=\small] at ({84/205},{187/205}) {规范 $G$};
\node[orange!85!black,anchor=west,font=\small] at (0.62,0.8) {顺序 $BA$};
\node[align=center,text width=4cm,font=\small] at (0,-1.53) {同一效果 $G$，成功率 $5/8$\\两条输出射线不同};
\end{scope}
\end{tikzpicture}
```

**图 1。**有限均衡校准与顺序留下的旋转。右图圆弧只表示两条最终输出射线的角差，不宣称中间物理滤波轨迹是测地线。

<a id="section-11"></a>

## 11. 更大的几何：正锥、双曲空间与交换子

qubit 的任意自伴矩阵写为 $X=x_0I+\mathbf x\cdot\boldsymbol\sigma$，有

$$
\det X=x_0^2-|\mathbf x|^2,\qquad
X\ge0\iff x_0\ge|\mathbf x|.
$$

这就是未来 Lorentz 正锥。正矩阵中行列式为一的截面是

$$
x_0^2-|\mathbf x|^2=1,\quad x_0>0,
$$

即双曲三维空间 $\mathrm{SL}(2,\mathbb C)/\mathrm{SU}(2)$ 的一个模型。$\mathrm{SL}(2,\mathbb C)$ 的极分解对应 boost 与旋转分解，这一几何对应是成熟结果 [5](#ref-moretti)。

若 $\widehat A=e^{(\alpha/2)\mathbf n\cdot\boldsymbol\sigma}$，则 $X\mapsto\widehat A X\widehat A^*$ 为 boost。物理成功滤片取 $A=c\widehat A$，$0<c\le e^{-|\alpha|/2}$，保证 $A^2\le I$。输入 Bloch 向量 $\mathbf r$ 的成功概率和后态分别是

$$
\begin{aligned}
p&=c^2(\cosh\alpha+\sinh\alpha\,\mathbf n\cdot\mathbf r),
\end{aligned}
\tag{22}
$$

$$
\begin{aligned}
\mathbf r'&=\frac{\mathbf r+[(\cosh\alpha-1)\mathbf n\cdot\mathbf r+\sinh\alpha]\mathbf n}
{\cosh\alpha+\sinh\alpha\,\mathbf n\cdot\mathbf r}.
\end{aligned}
\tag{23}
$$

这解释了两个非共线正伸缩产生旋转。此处是 qubit 内容正锥的 Lorentz 几何，不能直接等同为物理时空或引力方程；双曲度量、Fubini–Study 度量与 Bures 度量也应分别识别。

### 命题 11.1（小步旋转的首个非零阶）

设 $X,Y\ge0$，$A_\epsilon=e^{-\epsilon X/2}$、$B_\epsilon=e^{-\epsilon Y/2}$。乘积的极酉部分满足

$$
\boxed{
U_\epsilon=I+\frac{\epsilon^2}{8}[Y,X]+O(\epsilon^3).
}
\tag{24}
$$

**证明。**
写 $K=I+\epsilon h+\epsilon^2k+O(\epsilon^3)$，其中
$h=-(X+Y)/2$，$k=(X^2+Y^2)/8+YX/4$。由 $h=h^*$ 得
$|K|=I+\epsilon h+\epsilon^2(k+k^*)/2+O(\epsilon^3)$，故
$K|K|^{-1}=I+\epsilon^2(k-k^*)/2+O(\epsilon^3)$，即结论。

若把几何阶数记为 $s=\epsilon^2$，可写

$$
H_{\rm geom}=\frac{i\hbar}{8}[Y,X],\qquad
U_\epsilon=I-\frac{is}{\hbar}H_{\rm geom}+O(s^{3/2}).
$$

这给自伴生成元形式，但不确定经验钟速或实际 Hamiltonian。若直接重复滤波并保持 $N\epsilon^2$ 不变，正衰减通常在 $N\epsilon$ 阶累积，成功率可能趋零。

若实际供应倒数补偿，则可精确分离条件旋转：$K=UC$，取 $0<c\le\lambda_{\min}(C)$，正收缩 $D=cC^{-1}$ 满足

$$
KD=cU.
$$

先补偿再通过原两片，联合成功分支为 $\rho\mapsto c^2U\rho U^*$，成功率为 $c^2$。成功率不能删去。

<a id="section-12"></a>

## 12. 怎样从关系体系接回量子力学公理

### 12.1 对象重建与本稿没有省略的前件

仓库 C101 从有限实正比较场 $(J,S,g,D)$ 出发：$S$ 对称、双线性、有单位，$g$ 正定且满足 Frobenius 恒等式，$D_a$ 为标签线性的导子。实际二元整体具有张量载体，并满足模块作用、保取值条件作用与完整导子律；每个同一实际整体还能接活动伙伴。由其原定理，得到有限经典或复矩阵直和及

$$
m(a,b)=S(a,b)-i\sqrt\lambda D_ab=ab.
$$

这是一组承重的结构前件，不能用“都在整体内”一句话替换。最小活动对象的实线性维数至少四，包含单位方向；Bloch 三维是迹一截面。

C102 要求同一个实际正过程接参考时，全部参考效果不变，全部系统效果仍绑定原过程，并可有限次继续延伸。仓库证明该延伸为 $\Phi\otimes\operatorname{id}$，积累足够参考矩阵容量后得到完全正性。C103 的准备、丢弃与有限路径继用同步相对标尺；具体动力学另需供应 [1](#ref-repo-main)。

### 12.2 态与 Born 形式

有限复矩阵代数上，每个正归一线性泛函唯一写成

$$
\omega(B)=\operatorname{Tr}(\rho B),\qquad\rho\ge0,\quad\operatorname{Tr}\rho=1.
$$

证明可在矩阵单位上定义 $\rho_{ji}=\omega(E_{ij})$，由对所有秩一正矩阵的评价非负得到 $\rho\ge0$。对效果 $E$，

$$
p(E)=\omega(E)=\operatorname{Tr}(\rho E).
$$

纯态与秩一效果给 $p(\phi\mid\psi)=|\langle \phi,\psi\rangle|^2$。更一般的含单位复 $C^*$ 代数通过 GNS 商空间

$$
\mathcal N_\omega=\{a:\omega(a^*a)=0\},\qquad
\langle [a],[b]\rangle=\omega(a^*b)
$$

得到表示与 $\Omega_\omega=[I]$，并有

$$
p(E)=\|\pi_\omega(E^{1/2})\Omega_\omega\|^2.
$$

这里推导的是正线性评价的平方范数表示，正线性概率评价本身仍是前件。

只有二元互补归一化并不足以推出 Born：在 qubit 球面取
$f(P_{\mathbf n})=(1+n_z^3)/2$，它连续且 $f(P_{\mathbf n})+f(P_{-\mathbf n})=1$，却不是任何密度矩阵的线性评价。顶点与赤道值会迫出 $\rho=\lvert 0\rangle\langle 0\rvert$，但 $n_z=1/2$ 时该规则给 $9/16$，Born 给 $3/4$。

### 12.3 测量、仪器与连续运动

C113 给所选滤波的完整条件更新

$$
\rho\longmapsto\frac{\sqrt E\rho\sqrt E}{\operatorname{Tr}(\rho E)}
\quad\text{当 }\operatorname{Tr}(\rho E)>0.
$$

投影效果 $E=P$ 即给 Lüders 更新。若一整个标签仪器已供应且各分支都是所选滤波，$\sum_kE_k=I$，则

$$
\rho\longmapsto\sum_k\sqrt{E_k}\rho\sqrt{E_k}
$$

为非选择性输出。一般仪器的 Kraus 更新仍可不同，效果不唯一决定所有可能仪器。

连续可逆动力学须另给同一个对象上的实际确定性、迹保持连续可逆群；在 Heisenberg 方向它是保单位群。C102 使映射与其逆都完全正，保单位性允许应用双向 Schwarz 不等式，从而迫出乘法保持，故为 $*$ 自同构。在有限矩阵块中，连续群不能置换离散中心，生成元为内导子。因此状态方向有

$$
\rho(t)=e^{-itH/\hbar}\rho(0)e^{itH/\hbar},\qquad
i\hbar\dot\psi=H\psi.
$$

时间参数、$H$ 的具体数值及中心能量零点不由 C113 单独确定。

### 12.4 不确定性、复合与纠缠

对自伴 $A,B$，中心化读出 $\Delta A=A-\omega(A)I$、$\Delta B=B-\omega(B)I$ 的 Gram 正性给

$$
\operatorname{Var}_\omega A\operatorname{Var}_\omega B
\ge|\omega(\Delta A\Delta B)|^2
\ge\frac14|\omega([A,B])|^2.
$$

已有实际空间边给标准张量乘法，整体态限制到子代数或偏迹给局部态；整体纯态可有局部混合，得到纠缠的标准结构。共同历史可参与形成纠缠，但“共享历史段”与纠缠并不等价：同一个历史也可以只产生乘积态或经典相关混合态。

| 量子结构 | 本理论中的来源与范围 |
|---|---|
| Hilbert／矩阵表示 | C101 的完整有限正比较与活动延伸合同；一般正源可用 GNS 表示。 |
| Born 规则 | 正归一线性态–效果评价的矩阵／平方范数表示。 |
| 完全正通道 | C102 的同一实际过程、参考固定与可继续延伸。 |
| 共同相对标尺 | C103 的内部经典点与实际准备、丢弃路径。 |
| 规范测量更新 | C113 的有限均衡同向饱和；仅刻画所选滤波族。 |
| 酉与 Schrödinger 形式 | 另供的连续实际可逆群，加上完全正可逆性。 |
| 独立复合与纠缠 | 已供应空间边的张量结构及共同态限制；不自动供应任意并置。 |
| 唯一整体纯源 | 沿用既有有限相容与逐效果分离证书，不能由滤波校准替代。 |
| 几何相位与顺序旋转 | 保留实际相干运输、记录和有序复合；本稿给正滤片的极酉分解。 |

<a id="section-13"></a>

## 13. 把校准、筛选与记录放进同一个静态整体

### 命题 13.1（一个显式内部纯态实现）

对任意满足 [(1)](#eq-effect) 的有限分支，定义等距映射

$$
J_T\psi=\sum_\mu K_\mu\psi\otimes\lvert {\rm s},\mu\rangle
+\sqrt{I-E}\,\psi\otimes\lvert \rm f\rangle,
$$

其中所有记录相互正交。另为半深效果读数选择一个有限实现

$$
J_h\psi=E^{1/4}\psi\otimes\lvert {\rm h},{\rm s}\rangle
+\sqrt{I-\sqrt E}\,\psi\otimes\lvert {\rm h},{\rm f}\rangle.
$$

这只用于整体实现的存在例，任何成功效果为 $\sqrt E$ 的等距记录实现均可替代它；主定理不以它的更新方式为前提。增加内部试验类型记录 $B$，则

$$
\boxed{
\lvert \Omega_{\rm cal}\rangle=\sum_s\sqrt{\frac{w_s}{2}}\lvert s\rangle_C\otimes
\bigl(\lvert 0\rangle_B J_T\lvert \psi_s\rangle+\lvert 1\rangle_B J_h\lvert \psi_s\rangle\bigr)
}
\tag{25}
$$

为一个固定的整体纯态。读取校准记录 $s$ 和试验类型：类型零再读成功及原方向，类型一读半深成功，即可恢复 C113 的两类读数。

**证明。**
$J_T^*J_T=\sum K_\mu^*K_\mu+I-E=I$，同样 $J_h^*J_h=I$。两种试验类型与校准标签正交，且 $\sum w_s=1$，所以整体归一。相应联合概率分别为 $w_sr_E(p_s)/2$ 与 $w_sa_E(p_s)/2$。数值平方和加权平均即可形成 C113。

若 C113 成立，成功部分化为

$$
\sqrt E\psi\otimes\sum_\mu c_\mu\lvert {\rm s},\mu\rangle.
$$

在所选成功分支内，没有再留下随输入方向变化的额外未读环境记录。保留的记录仍可包含成功／失败、校准标签与后续历史。

这个有限模型证明“装置、校准、概率、后态和记录属于同一整体”在数学上相容。它不唯一决定所有可能的整体纯态，也不将一个 CP 映射的唯一性扩大到全部受控实现相位的唯一性。

<a id="section-14"></a>

## 14. 完整白话描述与下一步精确问题

**本轮的完整白话表述：**
一份共同来源里已经包含内容、读口、滤片和记录。一个滤片首先规定每种内容能留下多少；用一组真正均衡的内部方向去比较，就能检查它是否还额外丢掉了相干细节。平均比较达到由效果决定的上界时，滤片只能按平方根改变各方向的份量，不能再夹带额外转动或随输入方向变化的额外未读记录。两块这样的滤片不交换时，先后顺序仍会留下确定的旋转。对最小二元量子块，两片给出两个方向，它们的叉积给出第三个方向，也就是旋转轴。交换次序，旋转反向。所有成功概率、内容变化、补偿和历史记录都能一起放进同一个不变的整体纯态。观察者看到的更新，是内部记录的条件内容；真实系统走哪条历史、钟速是多少、哪些操作实际可用，由整体中的其余具体关系继续确定。

本轮完成的是有限所选滤波及其组合几何的一个自足理论块。后续有三类明确问题：给定实际有限准备误差与读数统计，怎样得到可用证书；给定局域相互作用与成功率预算，哪些极酉旋转可有效实现；怎样把这些有限块与场的空间局域性、无限维极限及经验时钟接续。它们不由“关系全部内生”的解释自动解决。

<a id="references"></a>

## 参考文献

<a id="ref-repo-main"></a>

### [1]

 the-omega-institute/trureturing，固定提交：

`40e161f1b410721daad15d8ceaad34c3d7e19759`。

[《复合比较的有限变化见证、共同标定与量子生成》](https://github.com/the-omega-institute/trureturing/blob/40e161f1b410721daad15d8ceaad34c3d7e19759/docs/develop/theory/AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md)，重点 §§33–49、77–98。本稿核对的是所列相关依赖，不对全仓作整体认证。

<a id="ref-repo-cont"></a>

### [2]

 同一固定提交，
[《无参考滤波关系、完整参考更新与射线几何续篇》](https://github.com/the-omega-institute/trureturing/blob/40e161f1b410721daad15d8ceaad34c3d7e19759/docs/develop/theory/AURIC_COMPOSITE_COMPARISON_REFERENCE_FREE_FILTER_RELATIONS_V96_CONTINUATION.md)，§§106–112（C112）及 §§99–105（C111）。

<a id="ref-barnum"></a>

### [3]

 Howard Barnum, *Information-disturbance tradeoff in quantum measurement on the uniform ensemble and on the mutually unbiased bases*,
[arXiv:quant-ph/0205155v1](https://arxiv.org/abs/quant-ph/0205155v1) (2002). 尤其定理 5、8、附录 A 定理 12 与第 VIII 节。

<a id="ref-banaszek"></a>

### [4]

 Konrad Banaszek, *Fidelity Balance in Quantum Operations*, Phys. Rev. Lett. 86, 1366 (2001),
[arXiv:quant-ph/0003123](https://arxiv.org/abs/quant-ph/0003123).

<a id="ref-moretti"></a>

### [5]

 Valter Moretti, *The interplay of the polar decomposition theorem and the Lorentz group*,
[arXiv:math-ph/0211047v1](https://arxiv.org/abs/math-ph/0211047v1) (2002).

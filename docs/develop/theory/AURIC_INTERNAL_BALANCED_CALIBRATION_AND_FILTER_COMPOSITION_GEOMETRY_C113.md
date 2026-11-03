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

## 15. 有限均衡校准的正分支合同

### 定义 15.1（同一个正成功分支与固定读回）

输入仍为原简单块 $H=\mathbb C^d$，输出为原有限空间 $K$。固定已指定的等距嵌入 $J:H\to K$；同一块情形取 $K=H,J=I$。在直和对象中，$J$ 是原输入扇区在原输出中的同名嵌入，不把不同中心扇区补成可相干制备的纯态空间。

取正复线性映射与其通常迹成功效果

$$
T:\mathcal B(H)\longrightarrow\mathcal B(K),\qquad
T^\dagger(I_K)=E,\qquad 0\le E\le I_H.
\tag{15.1}
$$

这里不假设二正、完全正、Kraus 分解或任何实际参考延伸。输入、输出和成功效果均属于同一个 $T$，不得随校准标签更换分支。

保留定义 2.2 的同一有限正权复射影二阶设计 $\mathscr D=\{(w_s,p_s)\}$，并定义

$$
\begin{aligned}
R_{\mathscr D,J}(T)
 &=\sum_s w_s\operatorname{Tr}_K[Jp_sJ^\dagger T(p_s)],\\
Q_{\mathscr D}(E)
 &=\sum_s w_s\bigl(\operatorname{Tr}_H[p_s\sqrt E]\bigr)^2.
\end{aligned}
\tag{15.2}
$$

$Jp_sJ^\dagger$ 是指定的同向读口。一般矩形输出若没有这样的已指定读回对应，不在本合同内。这里的 $J$ 只规定原读口的对应，不供应新的物理嵌入、准备或参考系统。有限设计的矩等式仍是代数关系，不要求未知态的两个副本。

## 16. 本卷有限校准在仅保正时的精确端点

### 定理 16.1（正分支的平均上界与唯一饱和）

在定义 15.1 中，令 $A=\sqrt E$，则

$$
R_{\mathscr D,J}(T)\le Q_{\mathscr D}(E)
=\frac{\operatorname{Tr}E+(\operatorname{Tr}A)^2}{d(d+1)}.
\tag{16.1}
$$

等号成立当且仅当原分支本身满足

$$
\boxed{T(X)=JA X A J^\dagger\quad\text{对全部 }X\in\mathcal B(H).}
\tag{16.2}
$$

因此在原同一块上，有限饱和关系 $R_{\mathscr D}(T)\ge Q_{\mathscr D}(E)$ 已从正性及正确成功效果选出平方根更新；所选分支的完全正性成为结论。

**证明。** 先在同一正分支中取 $P=\operatorname{supp}E$，证明输入支撑关系

$$
T(X)=T(PXP)\qquad(X\in\mathcal B(H)).
\tag{16.3}
$$

特别地，$E=0$ 时 $T=0$。

对任意输出效果 $0\le B\le I_K$，正性给

$$
0\le T^\dagger(B)\le E.
$$

若 $0\le C\le E$，对 $v\in\ker E$ 有 $\langle v,Cv\rangle=0$，由正矩阵的平方根得到 $Cv=0$；故 $C=PCP$。因此

$$
\operatorname{Tr}[BT(X)]
=\operatorname{Tr}[T^\dagger(B)X]
=\operatorname{Tr}[BT(PXP)].
$$

效果张成输出自伴空间，复线性延拓得到 (16.3)。$E=0$ 时 $P=0$。这是同一正分支的数学支撑性质，证明中没有供给一个物理压缩或逆滤波。这里直接复用续篇定理 114.1 中由正确成功效果取得输入支撑的步骤。

再复用成熟的块正矩阵界：若 $G$ 自伴，且在每个积向量上取非负值，则

$$
0\le\operatorname{Tr}G,\qquad
\|G\|_{\mathrm{HS}}\le\operatorname{Tr}G.
\tag{16.4}
$$

这是 Gurvits–Barnum 可分球定理的对偶形式 [6](#ref-positive-gb)，在 Szarek–Werner–Życzkowski 的推论 3 后明确写成 $\operatorname{Tr}(G^2)\le(\operatorname{Tr}G)^2$ [7](#ref-positive-swz)。仓内已有同一不等式及秩一投影补的可分性 [8](#ref-positive-repo-gb)，这里直接应用。不同因子维数可数学补零到同维，块正性、迹与 Hilbert–Schmidt 范数均保持，故 (16.4) 也适用于矩形输入输出。不需把 $G$ 假设为正半定。

零效果由输入支撑关系 (16.3) 处理。设 $E\ne0$，在 $P H$ 中选本征基 $e_1,\ldots,e_r$，写

$$
Ae_i=a_i e_i,\qquad a_i>0,\qquad
f_i=Je_i,\qquad s=\sum_{i=1}^r a_i.
$$

把此基补成 $H$ 的正交基。采用输入因子在前的 Choi 约定

$$
C_T=\sum_{i,j=1}^{d}|e_i\rangle\langle e_j|
          \otimes T(|e_i\rangle\langle e_j|).
\tag{16.5}
$$

正复线性映射保持伴随，故 $C_T$ 自伴；并且

$$
\langle x\otimes y,C_T(x\otimes y)\rangle
=\langle y,T(|\bar x\rangle\langle\bar x|)y\rangle\ge0.
\tag{16.6}
$$

这里只得到块正性，没有使用或断言 Choi 正性。输入支撑关系 (16.3) 使 (16.5) 只有 $i,j\le r$ 的项。以下仍保留整个输出 $K$。

令

$$
\Omega_J=\sum_{i=1}^{d}e_i\otimes Je_i,
\qquad z=\langle\Omega_J,C_T\Omega_J\rangle,
\qquad P_J=JJ^\dagger.
$$

由设计等式在第一因子取转置，

$$
\sum_s w_s p_s^{\mathsf T}\otimes Jp_sJ^\dagger
=\frac{I_H\otimes P_J+|\Omega_J\rangle\langle\Omega_J|}{d(d+1)}.
$$

结合 $\operatorname{Tr}[C_T(p^{\mathsf T}\otimes JpJ^\dagger)]
=\operatorname{Tr}[JpJ^\dagger T(p)]$，得到不含 Kraus 的矩公式

$$
d(d+1)R_{\mathscr D,J}(T)
=\operatorname{Tr}[P_J T(I_H)]+z.
\tag{16.7}
$$

对 $A\otimes A$ 使用原设计等式，则

$$
d(d+1)Q_{\mathscr D}(E)=\operatorname{Tr}E+s^2.
\tag{16.8}
$$

在 $P H\otimes K$ 中定义数学重加权

$$
G=(A_P^{-1/2}\otimes I_K)C_T(A_P^{-1/2}\otimes I_K),
\qquad
v=\sum_{i=1}^r\sqrt{a_i}\,e_i\otimes f_i,
\tag{16.9}
$$

其中 $A_P$ 是 $A$ 在支撑上的限制。局部合同变换保持块正性，且正确成功效果给

$$
\begin{aligned}
\operatorname{Tr}G
 &=\sum_{i=1}^r a_i^{-1}\operatorname{Tr}T(|e_i\rangle\langle e_i|)
 =\sum_{i=1}^r a_i=s,\\
\|v\|^2&=s,\qquad z=\langle v,Gv\rangle.
\end{aligned}
\tag{16.10}
$$

对矩阵的普通 Hilbert–Schmidt Cauchy–Schwarz 不等式与成熟界 (16.4)，有

$$
z=\operatorname{Tr}[G|v\rangle\langle v|]
\le s\|G\|_{\mathrm{HS}}\le s^2.
\tag{16.11}
$$

这不是对正映射套用一般 Schwarz 不等式。另一方面，

$$
\ell=\operatorname{Tr}[(I_K-P_J)T(I_H)]\ge0,
\qquad \operatorname{Tr}T(I_H)=\operatorname{Tr}E.
$$

因此完整差额为

$$
\boxed{d(d+1)(Q-R)=\ell+(s^2-z),\qquad
\ell\ge0,\quad s^2-z\ge0.}
\tag{16.12}
$$

这里 $\ell$ 保留了原输出在指定读回空间之外的泄漏。

若 $Q=R$，则 $z=s^2$。注意 $\||v\rangle\langle v|\|_{\mathrm{HS}}=s$，由 (16.4) 直接得到

$$
\begin{aligned}
\|G-|v\rangle\langle v|\|_{\mathrm{HS}}^2
 &=\|G\|_{\mathrm{HS}}^2+s^2-2z\le0.
\end{aligned}
$$

故 $G=|v\rangle\langle v|$。撤去数学重加权，

$$
C_T=|a_J\rangle\langle a_J|,\qquad
a_J=\sum_{i=1}^r a_i e_i\otimes f_i.
\tag{16.13}
$$

逐个矩阵单位读取 (16.13)，得 $T(|e_i\rangle\langle e_j|)=a_i a_j|f_i\rangle\langle f_j|$；再由输入支撑得到全部 $X$ 上的 (16.2)。反向代入给 $\ell=0,z=s^2$，所以等号成立。

支撑秩一也可单独读出：若 $E=a^2|e\rangle\langle e|$，输入支撑关系 (16.3) 给 $T(X)=\langle e,Xe\rangle B$，其中 $B\ge0,\operatorname{Tr}B=a^2$。此时 $z=\langle Je,BJe\rangle\le a^2$；饱和迫使 $B=a^2|Je\rangle\langle Je|$。不存在遗漏的相位或支撑外分支。$\square$

定理 16.1 是本卷有限设计合同对成熟正锥界的应用。Barnum 定理 5、8 与附录 A 定理 12，以及 Banaszek 的操作保真度公式，已经给出以算子分解描述的量子操作平均最优性 [3](#ref-barnum)、[4](#ref-banaszek)；这里沿用其目标量与二阶矩对应。新增的源内推论是本卷选中分支的 CP 前件可由正性取代，并以相同数据取得等号唯一性；不把成熟球定理、其对偶或固定测量最小扰动另立为原创原理。

## 17. 饱和的有限正比较几何

### 命题 17.1（差额的积向量证书）

沿用定理 16.1 的非零支撑与基。定义数学重加权映射

$$
\Phi(Y)=T(A_P^{-1}Y A_P^{-1}),\qquad
Y\in\mathcal B(PH).
\tag{17.1}
$$

$\Phi$ 正且保迹，$T(X)=\Phi(AXA)$。这只是同一线性映射的输入坐标变换，不被认作菜单中另有的实际过程。写 $C_\Phi$ 为输入在前的 Choi 矩阵，并将 $f_1,\ldots,f_r$ 补成整个 $K$ 的正交基。令

$$
W=s A_P\otimes I_K-|a_J\rangle\langle a_J|.
\tag{17.2}
$$

对 $i<j$ 与 $\theta\in\{0,\pi/2,\pi,3\pi/2\}$，定义

$$
\begin{aligned}
x_{ij\theta}&=\sqrt{a_i}e_i+e^{i\theta}\sqrt{a_j}e_j,\\
y_{ij\theta}&=\sqrt{a_j}f_i-e^{-i\theta}\sqrt{a_i}f_j,\\
D_{ij}&=\frac14\sum_\theta
 |x_{ij\theta}\otimes y_{ij\theta}\rangle
 \langle x_{ij\theta}\otimes y_{ij\theta}|.
\end{aligned}
\tag{17.3}
$$

记 $|i,k\rangle=e_i\otimes f_k$。则有有限可分分解

$$
\begin{aligned}
W={}&\sum_{i<j}D_{ij}
 +\sum_{\substack{1\le i,j\le r\\i\ne j}}
       a_i(s-a_i)|i,j\rangle\langle i,j|\\
 &+\sum_{i=1}^r\sum_{k=r+1}^{\dim K}
       s a_i|i,k\rangle\langle i,k|,
\end{aligned}
\tag{17.4}
$$

并且

$$
\operatorname{Tr}(C_\Phi W)=s^2-z.
\tag{17.5}
$$

**证明。** 保迹性来自 $\operatorname{Tr}\Phi(Y)=\operatorname{Tr}(A_P^{-1}EA_P^{-1}Y)=\operatorname{Tr}Y$。四相位平均消去非零相位次数的项，余项准确为

$$
\begin{aligned}
D_{ij}={}&a_i a_j\bigl(
 |i,i\rangle\langle i,i|+|j,j\rangle\langle j,j|
 -|i,i\rangle\langle j,j|-|j,j\rangle\langle i,i|\bigr)\\
 &+a_i^2|i,j\rangle\langle i,j|
  +a_j^2|j,i\rangle\langle j,i|.
\end{aligned}
$$

累加后，$|i,i\rangle$ 的对角系数是 $a_i(s-a_i)$，$|i,j\rangle$ 在 $i\ne j$ 时先有 $a_i^2$，再由 (17.4) 的剩余项补至 $s a_i$；支撑像以外的全部输出系数由最后一项保留。这恰等于 (17.2)。所有剩余系数非负。保迹给 $\operatorname{Tr}[C_\Phi(A_P\otimes I_K)]=s$，而 $C_T=(A_P\otimes I_K)C_\Phi(A_P\otimes I_K)$，故 (17.5) 成立。

可分性也直接来自成熟结果：置

$$
\eta=s^{-1/2}\sum_i\sqrt{a_i}\,e_i\otimes f_i,\qquad
\|\eta\|=1.
$$

则 $W=(\sqrt{s}A_P^{1/2}\otimes I_K)
(I-|\eta\rangle\langle\eta|)
(\sqrt{s}A_P^{1/2}\otimes I_K)$，而秩一投影的补由 Gurvits–Barnum 球定理可分 [6](#ref-positive-gb)、[8](#ref-positive-repo-gb)。式 (17.4) 把此处所用的有限比较项具体展开，没有重新证明一般可分球。$\square$

### 推论 17.2（有限饱和锁住方向与相位）

在 $r>1$ 时，$s^2-z=0$ 使 (17.4) 与 $C_\Phi$ 的每个积项配对均为零。因此 $\Phi$ 固定每个基投影的指定像，以及每对基方向的四个加权相位探针：

$$
\begin{aligned}
\Phi(|e_i\rangle\langle e_i|)&=|f_i\rangle\langle f_i|,\\
\Phi(|\bar x_{ij\theta}\rangle\langle\bar x_{ij\theta}|)
 &=J|\bar x_{ij\theta}\rangle\langle\bar x_{ij\theta}|J^\dagger.
\end{aligned}
\tag{17.6}
$$

**证明。** 每个配对非负，因为 $C_\Phi$ 块正。$a_i(s-a_i)>0$，且 $s a_i>0$；故所有 $k\ne i$ 上的 $\langle f_k,\Phi(|e_i\rangle\langle e_i|)f_k\rangle$ 为零。输出正性与迹一迫使第一式成立。

令 $u=\bar x_{ij\theta}$。正性及
$0\le|u\rangle\langle u|\le(a_i+a_j)(|e_i\rangle\langle e_i|+|e_j\rangle\langle e_j|)$
使 $\Phi(|u\rangle\langle u|)$ 支持在 $\operatorname{span}\{f_i,f_j\}$。$D_{ij}$ 的零配对又给

$$
\langle y_{ij\theta},\Phi(|u\rangle\langle u|)y_{ij\theta}\rangle=0.
$$

在这个二维空间中，$y_{ij\theta}\perp Ju$。正性使 $y_{ij\theta}$ 属于输出的核；保迹给输出迹 $a_i+a_j=\|u\|^2$，所以输出正好是 $|Ju\rangle\langle Ju|$。$\theta=0,\pi$ 的差给两个矩阵单位的实组合，$\theta=\pi/2,3\pi/2$ 的差给其虚组合；连同基投影便张成全部矩阵单位。

这把同一分支的饱和解释为：正比较的有限差额不能互相抵消；基方向没有泄漏，两个相位分量也不能再丢失或翻转。重加权后 $\Phi(Y)=JYJ^\dagger$，所以在原正支持上没有额外的信息损失；$A$ 本身的减权与零支持仍保留。

同一几何也可在 (16.9) 中看见：迹为 $s$ 的块正截面包含在半径 $s$ 的 Hilbert–Schmidt 球内，饱和超平面 $\langle v,Gv\rangle=s^2$ 与此球恰在 $G=|v\rangle\langle v|$ 相切。因此有限关系选择一个确定的射线端点，随后才得到原分支的 CP。若另有本卷 §13 的 CP 记录实现，其所选成功环境记录随输入方向不变，直接沿用该节的端点解释。

$r=1$ 只需保留输出补空间的比较，$r=0$ 已由正确成功效果确定。式 (17.3) 的探针是证明中的数学向量；它们不必属于实际校准设计，不由门群的稠密性取得，也没有被追加到实际菜单。实际供应的仍只是原设计及定义 15.1 的读口。$\square$

## 18. 原有限直和与完整输出中心

### 定理 18.1（逐输入块饱和消除中心泄漏）

原对象为 $\mathcal A=\bigoplus_\alpha M_{d_\alpha}(\mathbb C)$，迹为通常迹之和。设同一原正复线性分支 $T:\mathcal A\to\mathcal A$ 满足 $T^\dagger(I)=E=(E_\alpha)_\alpha$。在每个原输入块供应定义 2.2 的有限设计，读回原同一输出块，得 $R_\alpha,Q_\alpha$。则

$$
R_\alpha\le Q_\alpha\quad\text{对每个 }\alpha.
\tag{18.1}
$$

全部非零效果块饱和，当且仅当

$$
\boxed{T(X)_\alpha=\sqrt{E_\alpha}X_\alpha\sqrt{E_\alpha}
\quad\text{对全部 }X\in\mathcal A.}
\tag{18.2}
$$

给各输入块固定正权 $c_\alpha>0$ 时，单一汇总关系
$\sum_\alpha c_\alpha R_\alpha\ge\sum_\alpha c_\alpha Q_\alpha$
也等价于 (18.2)。

**证明。** 数学上把原输出代数表示为 $K=\bigoplus_\beta\mathbb C^{d_\beta}$ 上的块对角矩阵。对输入块 $\alpha$，限制原 $T$ 得到正映射 $T_\alpha:M_{d_\alpha}\to\mathcal B(K)$，其完整成功效果为 $E_\alpha$。取原同名嵌入 $J_\alpha$，直接应用定理 16.1。输出其余各中心保留在 $K$ 中，并被 (16.12) 的泄漏项计入；支撑像以外的全部方向也保留在 (17.4) 中。因此等号迫使

$$
T_\alpha(X_\alpha)=J_\alpha\sqrt{E_\alpha}
 X_\alpha\sqrt{E_\alpha}J_\alpha^\dagger.
$$

零效果块由定理 16.1 证明中的输入支撑关系 (16.3) 为零。输入直和的线性分解给 (18.2)，没有引入跨中心相干输入。所有 $Q_\alpha-R_\alpha$ 非负，正权汇总为零等价于逐项为零。反向直接代入。$\square$

## 19. 所选滤波的后果与量子起源前件

在定义 15.1 或定理 18.1 的原供应中，用有限饱和关系选择每个指定滤片，则这些原分支完全正。由它们实际供应的有限接续及经典标签并列仍完全正；同一原对象上，若一组已供分支的效果之和为 $I$，则它们组成通常完全正保迹的标签仪器。

这些是所选合同变换的通常后果：所选分支已是 (16.2) 或 (18.2) 的合同变换，对任意数学参考，其放大仍正；复合与标签并列保留此性质。效果求和为 $I$ 给总迹保持。这里的放大是数学性质，不由证明新增实际参考对象或联合箭头。

### 推论 19.1（与已有正返回路线的对应）

在相应原供应均已给出的范围内，续篇 §§113–119 的正返回、半程及同向下界关系，和本附录的有限均衡饱和关系，都选出同一个平方根族。前一路线的端点直接复用续篇定理 116.1；本附录不以其实际倒数补偿、半程族或全效果量词为前件。

**证明。** 续篇定理 116.1 已给平方根族；代入本卷设计矩公式即可得到有限饱和。反向，定理 16.1 与 18.1 给平方根族，再仅对原来实际供应的效果和接续应用本卷推论 3.3。它们的供应前件不同，不能由一条数值等式推出另一条路线所需装置实际存在。$\square$

### 假设与适用边界 19.2

本附录的条件结论保留以下对象、概率和实际操作前件：

1. 原有限复矩阵直和、通常迹、同一复结构与相位参考；其来源可接原 C101，或在 C114 的完整共同复比较合同下讨论。
2. 正归一线性态—效果评价，或 C114.3 的准备等价与仿射概率合同；二阶设计、平方根效果及同向概率均在此已定义的模型中取值。
3. 对同一原分支的实际有限设计准备、指定读回和效果标定；数学上存在设计、态可在某一表示中写出或门词轨道稠密，均不替代这些实际供应。
4. 原唯一 $\omega$ 与门序列读出的解释保持其原有合同；本附录不增添复位、新 ready、反馈、独立副本或任意联合等距。

由定理 16.1 减少的独立前件仅是这些已校准所选分支的预设完全正性；若对同一分支仍预先保留 C102 或 C114.5 的完整参考合同，就不能再把其 CP 计作本附录取得的新结论。全菜单 CP 仍需覆盖全部实际箭头的合同；续篇命题 119.2 已给所选滤波全部标准而菜单仍含转置正箭头的模型，直接复用该边界。

实际有限校准如何由原生准备与完整历史取得、有限误差如何认证、全菜单如何供应及共同 $\omega$ 的物理解释，仍是各自的未决桥梁。本附录不从有限比较推出 Born、共同复结构、独立张量接口、时间标尺或 Hamiltonian。C114 的标准 PSD／Gram 重建不在这里重做；Buscemi 的全部联合等距量词也不被替换为某个固定允许门词半群。

本附录只取精确饱和。本卷定理 6.1 的 Kraus／Stinespring diamond 估计继续使用其原 CP 前件；不能仅凭本附录把该带噪结论套用于一般正分支。精确端点成立不构成对一般正映射的近似稳定性声明。

### [6] Gurvits–Barnum 正锥工具

<a id="ref-positive-gb"></a>

Leonid Gurvits and Howard Barnum, *Largest separable balls around the maximally mixed bipartite quantum state*, Phys. Rev. A **66**, 062311, DOI [10.1103/PhysRevA.66.062311](https://doi.org/10.1103/PhysRevA.66.062311)，[quant-ph/0204159v2](https://arxiv.org/html/quant-ph/0204159v2)，定理 1：自伴 $\Delta$ 满足 $\|\Delta\|_{\mathrm{HS}}\le1$ 时，$I+\Delta$ 可分。特别取 $\Delta=-|\eta\rangle\langle\eta|$，得到单位向量秩一投影的补可分。这里只复用其数学正锥结论。

### [7] 块正矩阵的对偶范数界

<a id="ref-positive-swz"></a>

Stanisław J. Szarek, Elisabeth Werner and Karol Życzkowski, *Geometry of sets of quantum maps: a generic positive map acting on a high-dimensional system is not completely positive*, J. Math. Phys. **49**, 032113, DOI [10.1063/1.2841325](https://doi.org/10.1063/1.2841325)，[arXiv:0710.1571v2](https://arxiv.org/html/0710.1571v2)，推论 3 后明确陈述块正矩阵满足 $\operatorname{Tr}(G^2)\le(\operatorname{Tr}G)^2$，并将它与可分球的对偶几何联系起来。

### [8] 仓内已有的成熟几何接口

<a id="ref-positive-repo-gb"></a>

固定源码 [GurvitsBarnumBall.lean](https://github.com/the-omega-institute/trureturing/blob/d5f7c3fd1d1e4fca459bafe6cbab5129bc1a9a90/D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.lean) 的 `frobSq_le_trace_sq_of_blockPositive` 与 `separableCone_one_sub_rankOne` 分别提供 (16.4) 和秩一投影补的可分性，前者已覆盖两因子维数不同的矩阵。源内应用是 (16.7)–(16.13) 的成功效果重加权及等号回接；这些公式的本附录证明为普通数学证明。

## 追加锚（本行以下为增补区）
## 20. 仅保正有限校准的近饱和与目标支撑泄漏

### 定义 20.1（同一正分支的误差坐标）

完整保留定义 15.1 的原 $H=\mathbb C^d$、有限输出 $K$、指定等距 $J$、同一个正复线性 $T$、正确效果 $T^\dagger(I_K)=E\in[0,I_H]$、实际精确有限射影二阶设计及其指定读回。令

$$
\begin{aligned}
A&=\sqrt E,& P&=\operatorname{supp}E,& r&=\operatorname{rank}E,& k&=\dim K,\\
M&=\|E\|_{\mathrm{op}},&t&=\operatorname{Tr}E,&s&=\operatorname{Tr}A,\\
L(X)&=JAXAJ^\dagger,&\delta&=Q_{\mathscr D}(E)-R_{\mathscr D,J}(T),&D&=d(d+1)\delta.
\end{aligned}
\tag{20.1}
$$

记 $\Pi=JJ^\dagger$、$F=JPJ^\dagger$、$F^\perp=I_K-F$，并定义

$$
\ell_0=\operatorname{Tr}[(I_K-\Pi)T(I_H)],\qquad
\lambda=\operatorname{Tr}[F^\perp T(I_H)].
\tag{20.2}
$$

$F$ 是目标平方根分支的输出支撑，不只是指定读回空间。恒等式

$$
F^\perp=(I_K-\Pi)+J(I_H-P)J^\dagger
\tag{20.3}
$$

使 $\lambda$ 同时计入 $JH$ 外以及 $J(\ker E)$ 内的全部方向。

对任意复线性映射，采用不带 $1/2$ 的范数约定

$$
\|\Phi\|_\diamond
=\sup_{n\ge1}\ \sup_{\|X\|_1=1}
\|(\Phi\otimes\operatorname{id}_{M_n})(X)\|_1.
\tag{20.4}
$$

内层包括任意复矩阵输入。此处参考因子属于数学范数的量词，不要求放大后的 $T$ 保正，也不表示实际供应了参考系统。

### 定理 20.2（无谱底的正分支稳定性与支撑秩界）

在定义 20.1 的全部原前件下，$D\ge0$，且

$$
\boxed{
\begin{aligned}
\|T-L\|_\diamond&\le B(E,d,k,D),\\
B(E,d,k,D)&:=\min\left\{
 t+M,\ \sqrt{2kMD},\ 2\sqrt{dMD},
 (\sqrt{2r}+3)\sqrt{MD}\right\}.
\end{aligned}}
\tag{20.5}
$$

$E=0$ 时 $T=L=0$。若 $E\ne0$，在定理 16.1 的支撑本征基中，沿用 (16.9) 的 $G,v$ 与 (16.10) 的 $z=\langle v,Gv\rangle$，令 $q=s^2-z$，则

$$
\boxed{
D=\ell_0+q,\quad \ell_0,q\ge0,\quad
\|C_T-C_L\|_{\mathrm{HS}}\le\sqrt{2Mq},\quad
\lambda\le\frac{\sqrt M}{s}q,\quad t\lambda\le Mq.
}
\tag{20.6}
$$

其中 Choi 矩阵采用 (16.5) 的输入因子在前、未归一化约定。还可保留较细的估计

$$
\|T-L\|_\diamond
\le\sqrt{2rMq}+2\sqrt{(t-\lambda)\lambda}+\lambda.
\tag{20.7}
$$

这些结论包括奇异效果、矩形输出和 $r=1$；最终误差界不含最小正本征值的倒数。常数与维数阶不主张最优。零缺口的端点仍是 $R=Q\Longleftrightarrow T=L$。

对任意通常输入态 $\rho\ge0$、$\operatorname{Tr}\rho=1$，若实际共同成功率 $p=\operatorname{Tr}(E\rho)>0$，则还有

$$
\left\|\frac{T(\rho)}p-\frac{L(\rho)}p\right\|_1
\le\min\left\{2,\frac{B(E,d,k,D)}p\right\}.
$$

$p=0$ 时不定义这些条件态。

**证明。** 首先直接复用 (16.3) 的输入支撑关系 $T(X)=T(PXP)$。若 $E=0$，则 $P=0$，全部结论成立。以下设 $E\ne0$，写 $Ae_i=a_ie_i$，其中 $i\le r$ 时 $a_i>0$，并令 $f_i=Je_i$。本征基只是证明坐标，不改变原设计或实际标签。

(16.9)–(16.12) 已给出

$$
\begin{gathered}
G=(A_P^{-1/2}\otimes I_K)C_T(A_P^{-1/2}\otimes I_K),\qquad
v=\sum_{i\le r}\sqrt{a_i}\,e_i\otimes f_i,\\
\operatorname{Tr}G=s,\qquad \|v\|^2=s,\qquad
z=\langle v,Gv\rangle,\qquad D=\ell_0+s^2-z.
\end{gathered}
\tag{20.8}
$$

$G$ 自伴且块正，未被假设为正半定。直接使用成熟的矩形块正界 (16.4)，即 [Gurvits–Barnum 定理 1 的对偶形式](#ref-positive-gb)及 [Szarek–Werner–Życzkowski 推论 3 后的范数界](#ref-positive-swz)，有 $\|G\|_{\mathrm{HS}}\le s$。故 $z\le s^2$，并且

$$
\begin{aligned}
\|G-|v\rangle\langle v|\|_{\mathrm{HS}}^2
 &=\|G\|_{\mathrm{HS}}^2+s^2-2z\le2q,\\
C_T-C_L
 &=(A_P^{1/2}\otimes I_K)
       (G-|v\rangle\langle v|)(A_P^{1/2}\otimes I_K).
\end{aligned}
\tag{20.9}
$$

由 $\|A_P^{1/2}\|_{\mathrm{op}}^2=\sqrt M$ 得 $\|C_T-C_L\|_{\mathrm{HS}}^2\le2Mq$。这一步只把支撑上的逆坐标乘回，未引入谱底损失。

接着控制完整目标支撑外的泄漏。在 $PH\otimes K$ 上令 $\widehat F=I_{PH}\otimes F$，并置

$$
G_F=\widehat F G\widehat F,\qquad
\nu=\operatorname{Tr}[(I-\widehat F)G].
$$

压缩到 $PH\otimes FK$ 及 $PH\otimes F^\perp K$ 均保留块正性。其迹是在积正交基上的非负对角项之和，故 $\nu\ge0$、$\operatorname{Tr}G_F=s-\nu\ge0$。若 $F^\perp K=0$，相应压缩及 $\nu$ 均为零。由于 $v\in PH\otimes FK$，再次对 $G_F$ 使用同一矩形块正界，得到

$$
z=\langle v,G_Fv\rangle
\le s\|G_F\|_{\mathrm{HS}}
\le s(s-\nu),\qquad q\ge s\nu.
\tag{20.10}
$$

把 $G$ 的输入对角块记为 $G_{ii}$。块正性使每个 $G_{ii}$ 都为正矩阵，因此

$$
\begin{aligned}
\lambda
 &=\sum_{i\le r}a_i\operatorname{Tr}[F^\perp G_{ii}]\\
 &\le\max_i a_i\sum_{i\le r}\operatorname{Tr}[F^\perp G_{ii}]
 =\sqrt M\,\nu
 \le\frac{\sqrt M}{s}q.
\end{aligned}
\tag{20.11}
$$

而 $t=\sum_i a_i^2\le\sqrt M\,s$，所以 $t\lambda\le Mq$。另由 $T(I_H)\ge0$ 得 $0\le\ell_0\le\lambda\le t$。这证明 (20.6)，同时说明 (20.11) 并未遗漏 $J(\ker E)$ 中的泄漏。

以下把这些坐标估计转成完整范数估计。所用迹范数、Schatten Hölder、奇异值分解与 Choi 系数工具均为成熟工具，参见 [Watrous，*The Theory of Quantum Information* 第 3 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf)；任意参考的系数矩阵论证也直接沿用 [V12 引理 7.1](AURIC_FINITE_RESOLUTION_AND_COMPLETE_RECURSIVE_OBSERVATION_THEORY_V12.md#71-归一化-choi-约定)。这里只在本证明中写出所需估计，不将它们另立为新增范数定理。

先设 $\Psi$ 是任意正复线性映射，其效果为 $E_\Psi=\Psi^\dagger(I)$。取输入正交基，令 $e_{ij}=|e_i\rangle\langle e_j|$、$b_i=\langle e_i,E_\Psi e_i\rangle$。对任意输出酉矩阵 $U=\sum_a\zeta_a Q_a$ 的谱分解，正矩阵 $B_a=\Psi^\dagger(Q_a)$ 满足 $\sum_aB_a=E_\Psi$，且

$$
\begin{aligned}
|\operatorname{Tr}[U\Psi(e_{ij})]|
 &\le\sum_a|\langle e_j,B_ae_i\rangle|\\
 &\le\sum_a\sqrt{\langle e_i,B_ae_i\rangle\langle e_j,B_ae_j\rangle}
 \le\sqrt{b_ib_j}.
\end{aligned}
$$

迹范数对酉矩阵的对偶性给 $\|\Psi(e_{ij})\|_1\le\sqrt{b_ib_j}$。这里用的是各 $B_a$ 的正矩阵不等式，没有对仅正映射使用二正 Schwarz 不等式。

任取有限参考 $Z$ 及单位向量 $u=\sum_i e_i\otimes u_i$、$w=\sum_j e_j\otimes w_j$，有

$$
\begin{aligned}
\|(\Psi\otimes\operatorname{id}_Z)(|u\rangle\langle w|)\|_1
 &\le\sum_{i,j}\sqrt{b_ib_j}\,\|u_i\|\,\|w_j\|\\
 &\le\operatorname{Tr}E_\Psi.
\end{aligned}
$$

最后一步分别对两组系数用 Cauchy–Schwarz。任意矩阵的奇异值分解和三角不等式遂给出

$$
\|\Psi\|_\diamond\le\operatorname{Tr}E_\Psi.
\tag{20.12}
$$

这不假设 $\Psi\otimes\operatorname{id}_Z$ 为正。

再对任意复线性 $\Phi$，定义系数矩阵 $U_ue_i=u_i$、$U_we_i=w_i$。两者 Hilbert–Schmidt 范数为一，算符范数至多一。交换输出与参考的张量次序后，逐项展开给出

$$
(\Phi\otimes\operatorname{id}_Z)(|u\rangle\langle w|)
\simeq(U_u\otimes I)C_\Phi(U_w^\dagger\otimes I).
\tag{20.13}
$$

符号 $\simeq$ 只表示固定的张量因子置换。若输出空间维数为 $m$，Schatten Hölder 给

$$
\begin{aligned}
\|(U_u\otimes I_m)C_\Phi(U_w^\dagger\otimes I_m)\|_1
 &\le\|U_u\otimes I_m\|_{\mathrm{HS}}
       \|C_\Phi(U_w^\dagger\otimes I_m)\|_{\mathrm{HS}}\\
 &\le\sqrt m\,\|C_\Phi\|_{\mathrm{HS}}.
\end{aligned}
$$

同样由奇异值分解，这对任意参考和全部矩阵输入成立。取 $\Phi=T-L$、$m=k$，即得 (20.5) 的 $\sqrt{2kMD}$ 项。另一方面，(20.12) 给 $\|T\|_\diamond\le t$，而左右乘子给 $\|L\|_\diamond=M$，上界由算符范数获得，最大效果本征向量达到该值。因此 $\|T-L\|_\diamond\le t+M$。

为保留不含 $k$ 的输入维数界，令 $\Phi=T-L$、$S_0(X)=(I_K-\Pi)T(X)(I_K-\Pi)$。$S_0$ 为正，(20.12) 给 $\|S_0\|_\diamond\le\ell_0$。在完整 Choi 空间中置 $\widehat\Pi=I_H\otimes\Pi$，并分解

$$
C_1=\widehat\Pi C_\Phi,\qquad
C_2=(I-\widehat\Pi)C_\Phi\widehat\Pi,\qquad
C_{\Phi-S_0}=C_1+C_2.
$$

两项的行支撑正交，故

$$
\|C_1\|_{\mathrm{HS}}^2+\|C_2\|_{\mathrm{HS}}^2
\le\|C_\Phi\|_{\mathrm{HS}}^2.
$$

$C_1$ 的左支撑和 $C_2$ 的右支撑分别落在 $H\otimes\Pi K$。在 (20.13) 中分别把左、右的 $I_K$ 换成 $\Pi$，使用 $\operatorname{rank}\Pi=d$，有

$$
\begin{aligned}
\|(U_u\otimes I_K)C_1(U_w^\dagger\otimes I_K)\|_1
 &\le\|U_u\otimes\Pi\|_{\mathrm{HS}}
      \|C_1(U_w^\dagger\otimes I_K)\|_{\mathrm{HS}}
 \le\sqrt d\,\|C_1\|_{\mathrm{HS}},\\
\|(U_u\otimes I_K)C_2(U_w^\dagger\otimes I_K)\|_1
 &\le\|(U_u\otimes I_K)C_2\|_{\mathrm{HS}}
      \|U_w^\dagger\otimes\Pi\|_{\mathrm{HS}}
 \le\sqrt d\,\|C_2\|_{\mathrm{HS}}.
\end{aligned}
$$

于是

$$
\|T-L\|_\diamond
\le\ell_0+\sqrt{2d}\,\|C_\Phi\|_{\mathrm{HS}}
\le\ell_0+2\sqrt{dM(D-\ell_0)}.
\tag{20.14}
$$

若 $0<D\le dM$，则

$$
2\sqrt{dMD}-2\sqrt{dM(D-\ell_0)}
=\frac{2\sqrt{dM}\,\ell_0}{\sqrt D+\sqrt{D-\ell_0}}
\ge\ell_0.
$$

故 (20.14) 至多 $2\sqrt{dMD}$。若 $D\ge dM$，则

$$
2\sqrt{dMD}\ge2dM\ge(d+1)M\ge t+M,
$$

由已证的迹上界取得同一结论。$D=0$ 时 (20.6) 使 (20.14) 为零。

最后利用目标支撑秩。分解原分支而不改变其输出：

$$
T-L=(FT(\cdot)F-L)
 +\bigl(FT(\cdot)F^\perp+F^\perp T(\cdot)F\bigr)
 +F^\perp T(\cdot)F^\perp.
\tag{20.15}
$$

第一项输出落在 $FK$，其 Choi 矩阵是 $C_T-C_L$ 的压缩，故 (20.13) 的 $m=r$ 估计给出 $\sqrt{2rMq}$。最后一项为正，由 (20.12) 得完整范数至多 $\lambda$。

中间项记为 $\mathcal O$。对每个 $b>0$，令

$$
W_b=bF+b^{-1}F^\perp,\qquad
\Psi_b(X)=W_bT(X)W_b.
$$

$\Psi_b$ 仍正，而

$$
\operatorname{Tr}\Psi_b(I_H)=b^2(t-\lambda)+b^{-2}\lambda.
$$

取输出酉矩阵 $Z_F=F-F^\perp$。映射 $\mathcal R(Y)=(Y-Z_FYZ_F)/2$ 的 diamond 范数至多一，因为它是两个等距酉共轭之差的一半。缩放在交叉块上相消，故 $\mathcal R\Psi_b=\mathcal O$。对每个参考和任意矩阵输入，范数次乘性及 (20.12) 给

$$
\|\mathcal O\|_\diamond
\le\inf_{b>0}\{b^2(t-\lambda)+b^{-2}\lambda\}
=2\sqrt{(t-\lambda)\lambda}.
\tag{20.16}
$$

当任一系数为零时取 $b\to0$ 或 $b\to\infty$，等式仍成立。这一论证只对未放大的 $\Psi_b$ 使用正性。

合并三项得到 (20.7)。由于 $\lambda\le t$、$t\lambda\le Mq$，有

$$
\begin{aligned}
\|T-L\|_\diamond
 &\le\sqrt{2rMq}+2\sqrt{t\lambda}+\lambda\\
 &\le(\sqrt{2r}+3)\sqrt{Mq}
 \le(\sqrt{2r}+3)\sqrt{MD}.
\end{aligned}
\tag{20.17}
$$

四个上界共同给出 (20.5)。零缺口迫使范数为零；反向将 $T=L$ 代入原设计读数即得 $R=Q$，与定理 16.1 一致。对所述通常态 $\rho$，两个正输出的迹都恰为 $p$；若 $p>0$，它们除以同一个 $p$ 后均为态，距离至多二，未归一化差由 (20.5) 控制，故条件态误差至多 $\min\{2,B(E,d,k,D)/p\}$。本卷第 6 节已有稀有成功例说明此分母不能普遍省去；这里不把仅正映射的参考放大输出当成态。$\square$

本定理中的块正范数工具及范数比较为上述成熟结果。正映射的迹范数估计、完整输出分块及 $2\sqrt{dMD}$ 界也见同卷的[正分支稳定性稿，§§20–23](https://github.com/the-omega-institute/trureturing/blob/5274eeb2b0da10d4b5cc913fbfd75e181b7828d8/docs/develop/theory/AURIC_INTERNAL_BALANCED_CALIBRATION_AND_FILTER_COMPOSITION_GEOMETRY_C113.md)。这里的源内新增推导是把加权接触缺口进一步用于目标支撑外的 (20.10)–(20.11)，并通过 $t\lambda\le Mq$ 与 (20.15)–(20.17) 取得支撑秩控制；迹上界 $t+M$、一般范数工具及已有输入维数界均作为已有工作复用。Barnum 与 Banaszek 的操作平均最优性仍按 [3](#ref-barnum)、[4](#ref-banaszek) 的原操作算子前件引用。

## 21. 同一有限设计下的非完全正边界

### 命题 21.1（支撑转置混合与完全正上限的失效）

固定定义 15.1 的同一设计、原输出 $K$ 与指定 $J$。设 $P$ 为输入上秩 $r\ge2$ 的正交投影，$0<a\le1$，$E=a^2P$。在 $PH$ 的固定正交基中取转置 $\mathsf T_P$，转置后的算子仍按零延拓视为 $H$ 上算子。对 $0<\varepsilon\le1$ 定义

$$
T_\varepsilon(X)
=a^2J\bigl((1-\varepsilon)PXP+\varepsilon\mathsf T_P(PXP)\bigr)J^\dagger.
\tag{21.1}
$$

这是具有同一效果 $E$ 的正复线性分支，满足 $\lambda=\ell_0=0$，并且

$$
Q=\frac{a^2r(r+1)}{d(d+1)},\qquad
D=a^2\varepsilon r(r-1),\qquad
\delta=\frac{a^2\varepsilon r(r-1)}{d(d+1)}\longrightarrow0.
\tag{21.2}
$$

每个 $\varepsilon>0$ 的 $T_\varepsilon$ 均非完全正。若 $r\ge3$，另有

$$
\|T_1-L\|_\diamond
\ge a^2\left(r+1-\frac2r\right)>2M,\qquad M=a^2.
\tag{21.3}
$$

因此正分支的任意小正缺陷不推出精确完全正性，定理 6.1 的 CP 上限 $2M$ 不能移用于全部正分支。

**证明。** 压缩与转置都保正，后接指定等距也保正；转置保迹，所以 $T_\varepsilon^\dagger(I_K)=a^2P$。全部输出落在 $JPH$，故两种泄漏均为零。写 $\Omega_{P,J}=\sum_{i\le r}e_i\otimes Je_i$，并把 $PH\otimes JPH$ 上的交换算子记为 $\mathsf S_{P,J}$，即 $\mathsf S_{P,J}(e_i\otimes Je_j)=e_j\otimes Je_i$。Choi 矩阵为

$$
C_{T_\varepsilon}
=a^2\bigl((1-\varepsilon)|\Omega_{P,J}\rangle\langle\Omega_{P,J}|
          +\varepsilon\mathsf S_{P,J}\bigr),
\tag{21.4}
$$

在该空间外为零。于是 $s=ar$、$t=a^2r$、

$$
z=a^2\bigl((1-\varepsilon)r^2+\varepsilon r\bigr).
$$

代入 (16.8) 与 (20.8) 即得 (21.2)，原有限设计没有被替换。反对称向量 $e_i\otimes Je_j-e_j\otimes Je_i$ 与 $\Omega_{P,J}$ 正交，是 (21.4) 本征值 $-a^2\varepsilon$ 的向量。因此 Choi 矩阵非正半定。完全正映射必有正半定 Choi 矩阵，故这些分支均非完全正。

对 $\varepsilon=1$，取参考维数 $r$ 的归一化最大纠缠投影作为数学范数测试输入。误差输出等距于

$$
\frac{a^2}{r}
 \bigl(\mathsf S_{P,J}-|\Omega_{P,J}\rangle\langle\Omega_{P,J}|\bigr).
$$

括号内沿 $\Omega_{P,J}$ 的本征值为 $1-r$，对称正交补上的本征值为一，反对称子空间上的本征值为负一；后二者维数分别为 $r(r+1)/2-1$ 和 $r(r-1)/2$。故其迹范数乘 $a^2/r$ 后为 $a^2(r+1-2/r)$，得到 (21.3)。这是 diamond 范数下界的数学证书，未声明原菜单实际供应了该参考输入。$\square$

此处转置的 Choi 非正性与全支撑模型为标准边界，也见上述同卷正分支稳定性稿；(21.1) 保留奇异效果与指定 $J$。平方根误差阶、维数依赖及稀有成功的下界直接复用本卷命题 6.2 及其后条件化例，不再作为新下界另行重述。其 CP 子类已包含于定理 20.2 的正分支类，故这些原有障碍仍适用；它们不确定 (20.5) 的最优常数或最优秩依赖。

## 22. 成功条件化与共同实现的适用域

### 定义 22.1（近饱和合同保留的前件与边界）

定理 20.2 的共同实现前件就是定义 15.1：有限复矩阵对象、通常迹与 Born 评价、全域复线性正性、同一原分支的精确成功效果、指定 $J$、实际精确有限二阶设计及读回。相对于定理 6.1 的预设 CP 路线，(20.5) 只需原分支的正性，并保留显式维数或支撑秩依赖；定理 6.1 的原界继续按其 CP 前件适用。(20.5) 控制到同一个 CP 平方根分支的距离，正缺陷时不取得原分支的精确 CP。支撑逆、输出分块、缩放与数学参考均只是证明操作，不供应新的准备、复位、反馈、独立副本或实际联合延伸。

若真实缺陷已有可靠上界 $0\le\delta\le\eta$，则可在 (20.5) 中用 $d(d+1)\eta$ 代替 $D$，因为右侧每项关于 $D$ 非减。效果、设计或指定读回本身漂移的合同须另给共同误差模型，不能把它们默认为此单一 $\delta$。零缺口只选择同一已校准分支；全菜单 CP 仍要求覆盖全部实际箭头，保留 19.2 及续篇命题 119.2 的菜单边界。

[C118 的有限闭环合同，§§140–149](AURIC_COMPOSITE_COMPARISON_REFERENCE_FREE_FILTER_RELATIONS_V96_CONTINUATION.md)使用每个固定返回的二十四项控制；其定理 146.1 与定义 146.2 的确定性误差只扰动读数，并保留精确映射与校准。这里给出的单分支正映射近饱和界，不单独构成该闭环协议的联合映射误差界，也不供应定义 148.2 所需的原生准备、共同历史和联合取得性。全部设计与读口的实际供应、有限误差认证及共同实现仍是独立前件。

本合同的量词不包含 FIB IX 同一历史的 JMMJM、原全网格目标或非零半程缺陷下的全效果固定返回 $H>0$ 问题，因而没有这些问题的结算结论。共同复结构、Born 形式、原唯一整体态 $\omega$、经验时间与原生全菜单的起源也不由 (20.5) 推出。这些适用边界沿用 19.2；(20.5) 增加的是原有限校准合同下的正分支近饱和控制。

## 追加锚（本行以下为增补区）

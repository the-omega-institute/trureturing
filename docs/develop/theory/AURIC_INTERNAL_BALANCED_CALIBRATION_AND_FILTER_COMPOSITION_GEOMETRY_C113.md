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

本定理中的块正范数工具及范数比较为上述成熟结果。正映射的迹范数估计、完整输出分块、$2\sqrt{dMD}$ 输入维数界及迹上界 $t+M$ 均作为既有推导复用，所需证明在本定理内完整给出。这里的源内新增推导是把加权接触缺口进一步用于目标支撑外的 (20.10)–(20.11)，并通过 $t\lambda\le Mq$ 与 (20.15)–(20.17) 取得支撑秩控制。Barnum 与 Banaszek 的操作平均最优性仍按 [3](#ref-barnum)、[4](#ref-banaszek) 的原操作算子前件引用。

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

此处转置的 Choi 非正性与全支撑模型沿用标准边界；(21.1) 保留奇异效果与指定 $J$。平方根误差阶、维数依赖及稀有成功的下界直接复用本卷命题 6.2 及其后条件化例，不再作为新下界另行重述。其 CP 子类已包含于定理 20.2 的正分支类，故这些原有障碍仍适用；它们不确定 (20.5) 的最优常数或最优秩依赖。

## 22. 成功条件化与共同实现的适用域

### 定义 22.1（近饱和合同保留的前件与边界）

定理 20.2 的共同实现前件就是定义 15.1：有限复矩阵对象、通常迹与 Born 评价、全域复线性正性、同一原分支的精确成功效果、指定 $J$、实际精确有限二阶设计及读回。相对于定理 6.1 的预设 CP 路线，(20.5) 只需原分支的正性，并保留显式维数或支撑秩依赖；定理 6.1 的原界继续按其 CP 前件适用。(20.5) 控制到同一个 CP 平方根分支的距离，正缺陷时不取得原分支的精确 CP。支撑逆、输出分块、缩放与数学参考均只是证明操作，不供应新的准备、复位、反馈、独立副本或实际联合延伸。

若真实缺陷已有可靠上界 $0\le\delta\le\eta$，则可在 (20.5) 中用 $d(d+1)\eta$ 代替 $D$，因为右侧每项关于 $D$ 非减。效果、设计或指定读回本身漂移的合同须另给共同误差模型，不能把它们默认为此单一 $\delta$。零缺口只选择同一已校准分支；全菜单 CP 仍要求覆盖全部实际箭头，保留 19.2 及续篇命题 119.2 的菜单边界。

[C118 的有限闭环合同，§§140–149](AURIC_COMPOSITE_COMPARISON_REFERENCE_FREE_FILTER_RELATIONS_V96_CONTINUATION.md)使用每个固定返回的二十四项控制；其定理 146.1 与定义 146.2 的确定性误差只扰动读数，并保留精确映射与校准。这里给出的单分支正映射近饱和界，不单独构成该闭环协议的联合映射误差界，也不供应定义 148.2 所需的原生准备、共同历史和联合取得性。全部设计与读口的实际供应、有限误差认证及共同实现仍是独立前件。

本合同的量词不包含 FIB IX 同一历史的 JMMJM、原全网格目标或非零半程缺陷下的全效果固定返回 $H>0$ 问题，因而没有这些问题的结算结论。共同复结构、Born 形式、原唯一整体态 $\omega$、经验时间与原生全菜单的起源也不由 (20.5) 推出。这些适用边界沿用 19.2；(20.5) 增加的是原有限校准合同下的正分支近饱和控制。

## 追加锚（本行以下为增补区）

## 23. 效果、准备与读回误差下的同一正分支

### 定义 23.1（共同分支与未条件化联合读数）

设 $H=\mathbb C^d$、$d\ge1$，$K$ 有限维，$J:H\to K$ 为指定等距。固定一族数学比较投影与权重
$\mathscr D=\{(w_s,p_s)\}_{s\in S}$，满足

$$
w_s\ge0,\quad \sum_sw_s=1,\quad
p_s^2=p_s=p_s^\dagger,\quad \operatorname{Tr}p_s=1,\quad
\sum_sw_sp_s\otimes p_s=\frac{I+\mathsf S}{d(d+1)},
\tag{23.1}
$$

其中 $\mathsf S$ 为 $H\otimes H$ 上的交换算子。比较投影的精确二阶矩是数学前件；实际准备可以不是这些投影。

同一实际分支由一个正复线性映射 $T:M(H)\to M(K)$ 表示，其实际效果与名义效果满足

$$
E=T^\dagger(I_K),\qquad 0\le E,E_0\le I_H,\qquad
\|E-E_0\|_{\mathrm{op}}\le\epsilon,\quad 0\le\epsilon\le1.
\tag{23.2}
$$

每个标签 $s$ 对应实际态 $\rho_s$ 和实际二元效果 $F_s$：

$$
\rho_s\ge0,\quad\operatorname{Tr}\rho_s=1,\quad
0\le F_s\le I_K,\qquad
G_s=Jp_sJ^\dagger,\quad q_s=\operatorname{Tr}T(\rho_s).
\tag{23.3}
$$

共同分支前件要求：在同一输入、输出和读回坐标中，标签 $s$、成功及读回接受的未条件化联合概率恰为

$$
\Pr(s,\mathrm{success},\mathrm{accept})
=w_s\operatorname{Tr}[F_sT(\rho_s)].
\tag{23.4}
$$

此处的 $T$ 对全部标签相同；若另有固定的记忆条件或历史索引，所有公式须在同一个条件或索引上成立。后续对任意输入调用该分支时，也使用这个 $T$。仅在校准时存在一个拟合映射，不是此共同分支前件。

给定非负数 $a,b,\nu$ 与实读数 $\widehat R$，假设同时成立

$$
\begin{aligned}
\frac12\sum_sw_s\|\rho_s-p_s\|_1&\le a,\\
\sum_sw_sq_s\|F_s-G_s\|_{\mathrm{op}}&\le b,\\
\left|\widehat R-\sum_sw_s\operatorname{Tr}[F_sT(\rho_s)]\right|&\le\nu.
\end{aligned}
\tag{23.5}
$$

读回误差按实际未条件化成功概率 $q_s$ 加权。若只给出逐标签上界
$q_s\le\bar q_s$、$\|F_s-G_s\|_{\mathrm{op}}\le b_s$，则 $b=\sum_sw_s\bar q_sb_s$ 是允许的预算；不需要将任何读数先除以 $q_s$。这些不等式若带随机性，以下结论只在它们共同成立的同一事件上适用，不从分别的边缘置信水平断言联合事件。

记

$$
\begin{aligned}
L_A(X)&=J\sqrt A\,X\sqrt A\,J^\dagger,\qquad 0\le A\le I_H,\\
Q(A)&=\sum_sw_s[\operatorname{Tr}(p_s\sqrt A)]^2
=\frac{\operatorname{Tr}A+(\operatorname{Tr}\sqrt A)^2}{d(d+1)},\\
R(T)&=\sum_sw_s\operatorname{Tr}[G_sT(p_s)],\\
\omega_d(\epsilon)&=\min\left\{1,\frac{\epsilon+2d\sqrt\epsilon}{d+1}\right\},\\
u&=Q(E_0)-\widehat R+a+b+\nu+\omega_d(\epsilon).
\end{aligned}
\tag{23.6}
$$

$R(T)$ 是同一个映射在数学比较设计上的评价，不将 $p_s$ 的精确实际供应加入 (23.3)。全文的 diamond 范数沿用 (20.4)，不带 $1/2$。

### 定理 23.2（共同误差预算与名义平方根分支）

在定义 23.1 的全部前件下，

$$
0\le Q(E)-R(T)\le u.
\tag{23.7}
$$

特别地，$u<0$ 与这些前件不相容。置 $D_*=d(d+1)u$、$k=\dim K$，并沿用 (20.5) 的函数 $B$，则

$$
\boxed{
\|T-L_{E_0}\|_\diamond
\le B(E,d,k,D_*)+2\sqrt\epsilon.
}
\tag{23.8}
$$

一个只需名义读数预算与维数的上界是

$$
\boxed{
\|T-L_{E_0}\|_\diamond\le\beta_0,
\qquad
\beta_0=\min\{d+1,\ 2\sqrt{dD_*}+2\sqrt\epsilon\}.
}
\tag{23.9}
$$

(23.8) 中的秩是实际 $\operatorname{rank}E$。不假设 $E$ 与 $E_0$ 有共同支撑，也不以 $\operatorname{rank}E_0$ 代替它。

进一步，设 $\tau,\tau_0$ 为普通输入态，$\|\tau-\tau_0\|_1\le\gamma$，令

$$
p=\operatorname{Tr}(E\tau),\qquad
q=\operatorname{Tr}(E_0\tau_0),\qquad M_0=\|E_0\|_{\mathrm{op}}.
$$

若 $\beta$ 是 (23.8) 或 (23.9) 给出的任一上界，置
$U=\beta+M_0\gamma$、$V=\epsilon+M_0\gamma/2$。则

$$
\|T(\tau)-L_{E_0}(\tau_0)\|_1\le U,
\qquad |p-q|\le\min\{U,V\}.
\tag{23.10}
$$

当且仅当两边成功率都为正时，所述两个归一化输出同时有定义；在 $p,q>0$ 下，

$$
\boxed{
\left\|\frac{T(\tau)}p-\frac{L_{E_0}(\tau_0)}q\right\|_1
\le\min\left\{2,\frac{U+\min\{U,V\}}{\max\{p,q\}}\right\}.
}
\tag{23.11}
$$

同一输入时可取 $\gamma=0$，得到 $\min\{2,(\beta+\epsilon)/\max\{p,q\}\}$。若仅知名义成功率 $q>V$，则 $p\ge q-V>0$，且 (23.11) 右侧还可上界为 $\min\{2,(U+V)/q\}$。

**证明。** 先比较实际联合读数与 $R(T)$。由于 $T$ 正且 $T^\dagger(I_K)=E\le I_H$，对每个标签有
$0\le T^\dagger(G_s)\le E\le I_H$。两个等迹态之差 $X=\rho_s-p_s$ 自伴且迹为零，故

$$
\left|\operatorname{Tr}[T^\dagger(G_s)X]\right|
\le\tfrac12\|X\|_1.
$$

这是效果与迹距离的成熟对偶估计，亦是 [Watrous，第 3 章定理 3.4](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf) 的二元态判别特例；它只对输入上的效果使用正性。同时，$T(\rho_s)\ge0$，所以

$$
\left|\operatorname{Tr}[(F_s-G_s)T(\rho_s)]\right|
\le q_s\|F_s-G_s\|_{\mathrm{op}}.
$$

在恒等式

$$
\operatorname{Tr}[F_sT(\rho_s)]-\operatorname{Tr}[G_sT(p_s)]
=\operatorname{Tr}[(F_s-G_s)T(\rho_s)]
 +\operatorname{Tr}[G_sT(\rho_s-p_s)]
$$

中取加权和，并用 (23.5)，得到

$$
|R(T)-\widehat R|\le a+b+\nu.
\tag{23.12}
$$

以下效果扰动只用成熟的正矩阵平方根单调性和 Schatten 乘子估计；为固定包括奇异效果的适用范围，将所需步骤写在本证明内。对正矩阵 $A$，谱演算给收敛的积分

$$
\sqrt A=\frac1\pi\int_0^\infty t^{-1/2}A(A+tI)^{-1}\,dt.
$$

对每个 $t>0$，$A(A+tI)^{-1}=I-t(A+tI)^{-1}$ 关于 $A\ge0$ 单调，因此平方根单调。若 $0\le A,B$、$\|A-B\|_{\mathrm{op}}\le\epsilon$，则

$$
\sqrt A\le\sqrt{B+\epsilon I}\le\sqrt B+\sqrt\epsilon I.
$$

后一不等式是 $B$ 的逐本征值标量不等式。交换 $A,B$ 后得到

$$
\|\sqrt A-\sqrt B\|_{\mathrm{op}}\le\sqrt\epsilon.
\tag{23.13}
$$

此处未交换两个不对易的矩阵，亦未使用正谱底。取 $A=E,B=E_0$，有

$$
\begin{aligned}
|\operatorname{Tr}E-\operatorname{Tr}E_0|&\le d\epsilon,\\
|\operatorname{Tr}\sqrt E-\operatorname{Tr}\sqrt{E_0}|&\le d\sqrt\epsilon,\\
\operatorname{Tr}\sqrt E+\operatorname{Tr}\sqrt{E_0}&\le2d.
\end{aligned}
$$

代入 $Q$ 的公式，并用 $0\le Q(E),Q(E_0)\le1$，得

$$
|Q(E)-Q(E_0)|\le\omega_d(\epsilon).
\tag{23.14}
$$

由同一正 $T$、实际效果 $E$、指定 $J$ 及 (23.1)，(16.8) 与 (20.8)–(20.17) 的代数推导适用于这里的比较评价 $R(T)$，给出

$$
\delta=Q(E)-R(T)\ge0,\qquad
\|T-L_E\|_\diamond\le B(E,d,k,d(d+1)\delta).
\tag{23.15}
$$

这些公式只要求比较投影的精确二阶矩；用它们评价同一 $T$ 并不声称实际准备已等于比较投影。原实际精确校准合同与这里的漂移合同通过 (23.12) 区分。由 (23.12)–(23.14)，有 $\delta\le u$，证得 (23.7)。$B$ 的各项对最后一个非负变量非减，故可用 $D_*$ 代入。

令 $A=\sqrt E$、$A_0=\sqrt{E_0}$。对每个有限参考及任意矩阵输入，展开

$$
AXA-A_0XA_0=(A-A_0)XA+A_0X(A-A_0).
$$

两边张量恒等映射后，Schatten 乘子估计和等距 $J$ 给

$$
\|L_E-L_{E_0}\|_\diamond
\le(\|A\|_{\mathrm{op}}+\|A_0\|_{\mathrm{op}})
       \|A-A_0\|_{\mathrm{op}}
\le2\sqrt\epsilon.
\tag{23.16}
$$

与 (23.15) 取三角不等式即得 (23.8)。(20.12) 又给
$\|T\|_\diamond\le\operatorname{Tr}E\le d$，而
$\|L_{E_0}\|_\diamond=M_0\le1$；(20.5) 中的输入维数项至多 $2\sqrt{dD_*}$。两种上界共同给出 (23.9)。成熟的平均平方根最优性仍按 [Barnum，第 IV、VIII 节](https://arxiv.org/html/quant-ph/0205155v1) 的操作算子前件引用；(23.12) 与正分支 (23.15) 的组合不被归给该 CP 最优性结论。

最后，对不同输入先插入 $L_{E_0}(\tau)$。其输入迹范数放大至多 $M_0$，故未归一化差至多 $U$。另一方面，

$$
p-q=\operatorname{Tr}[(E-E_0)\tau]
       +\operatorname{Tr}[E_0(\tau-\tau_0)],
$$

第一项绝对值至多 $\epsilon$；第二项因输入差迹为零、$0\le E_0\le M_0I$，绝对值至多 $M_0\gamma/2$。取迹还给 $|p-q|\le U$，证得 (23.10)。写 $X=T(\tau)\ge0$、$Y=L_{E_0}(\tau_0)\ge0$。当 $p,q>0$ 时，

$$
\left\|\frac Xp-\frac Yq\right\|_1
\le\frac{\|X-Y\|_1+|p-q|}{p},
\qquad
\left\|\frac Xp-\frac Yq\right\|_1
\le\frac{\|X-Y\|_1+|p-q|}{q}.
$$

取较小上界，并用两个态之间的距离至多二，即得 (23.11)。全证明只要求原分支正性；没有将 $T$ 的任意参考放大解释为正输出态。$\square$

## 24. 名义支撑的泄漏预算与共同证书的边界

### 定理 24.1（支撑变化下的名义秩控制）

保留定义 23.1 的全部前件与 $u,D_*$。令

$$
\begin{aligned}
P_0&=\operatorname{supp}E_0,&r_0&=\operatorname{rank}E_0,&P_0^\perp&=I_H-P_0,\\
E_c&=P_0EP_0,&T_c(X)&=T(P_0XP_0),\\
h&=\operatorname{Tr}(P_0^\perp E),&t_c&=\operatorname{Tr}(P_0E).
\end{aligned}
\tag{24.1}
$$

则有

$$
\begin{aligned}
0\le h&\le(d-r_0)\epsilon,\qquad 0\le t_c\le r_0,\\
\|T-T_c\|_\diamond
&\le g:=2\sqrt{t_ch}+h
\le g_0:=2\sqrt{r_0(d-r_0)\epsilon}+(d-r_0)\epsilon.
\end{aligned}
\tag{24.2}
$$

对 $D_c^*=d(d+1)(u+g_0)$，进一步有

$$
\|T-L_{E_0}\|_\diamond
\le g_0+B(E_c,d,k,D_c^*)+2\sqrt\epsilon
\le\beta_P,
\tag{24.3}
$$

其中完全显式的名义秩上界为

$$
\beta_P=g_0+(\sqrt{2r_0}+3)\sqrt{d(d+1)(u+g_0)}+2\sqrt\epsilon.
\tag{24.4}
$$

因此 $\min\{\beta_0,\beta_P\}$ 可代入 (23.10)–(23.11)。若 $r_0=0$，还可直接取 $\beta=d\epsilon$。

**证明。** 由 $P_0^\perp E_0=0$、$\|E-E_0\|_{\mathrm{op}}\le\epsilon$，有
$0\le P_0^\perp EP_0^\perp\le\epsilon P_0^\perp$，于是得到 $h$ 的上界；$E\le I_H$ 给 $t_c\le r_0$。

为控制输入支撑的交叉项，置 $Z=P_0-P_0^\perp$ 和

$$
\mathcal R(X)=P_0XP_0^\perp+P_0^\perp XP_0
             =\frac{X-ZXZ}{2}.
$$

酉共轭的 diamond 范数为一，故 $\|\mathcal R\|_\diamond\le1$。对每个 $b'>0$ 令

$$
W_{b'}=b'P_0+(b')^{-1}P_0^\perp,
\qquad \Psi_{b'}(X)=T(W_{b'}XW_{b'}).
$$

$\Psi_{b'}$ 是正映射；它不必迹不增。(20.12) 对任意正映射适用，因而

$$
\|\Psi_{b'}\|_\diamond
\le\operatorname{Tr}\Psi_{b'}(I_H)
=(b')^2t_c+(b')^{-2}h.
$$

由于 $W_{b'}\mathcal R(X)W_{b'}=\mathcal R(X)$，有
$T\mathcal R=\Psi_{b'}\mathcal R$。所以

$$
\|T\mathcal R\|_\diamond
\le\inf_{b'>0}\{(b')^2t_c+(b')^{-2}h\}
=2\sqrt{t_ch}.
\tag{24.5}
$$

任一系数为零时由极限取下确界。映射 $X\mapsto T(P_0^\perp XP_0^\perp)$ 仍正，其效果迹为 $h$，由 (20.12) 得 diamond 范数至多 $h$。在恒等分解

$$
T-T_c=T\mathcal R+T(P_0^\perp(\cdot)P_0^\perp)
$$

中合并两项，证得 (24.2)。这里的输入缩放只用于同一正映射的数学范数估计，没有增设 $T$ 的二正或完全正前件。

$T_c$ 的实际效果是 $E_c$，满足 $0\le E_c\le I_H$、$\operatorname{rank}E_c\le r_0$，且

$$
\|E_c-E_0\|_{\mathrm{op}}
=\|P_0(E-E_0)P_0\|_{\mathrm{op}}\le\epsilon.
$$

对每个比较投影，$\|T(p_s)-T_c(p_s)\|_1\le g_0$，而 $\|G_s\|_{\mathrm{op}}\le1$，故
$|R(T)-R(T_c)|\le g_0$。沿用 (23.12)、(23.14)，得到

$$
\begin{aligned}
0\le Q(E_c)-R(T_c)
&\le Q(E_0)-\widehat R+a+b+\nu+\omega_d(\epsilon)+g_0\\
&=u+g_0.
\end{aligned}
\tag{24.6}
$$

将 (20.8)–(20.17) 应用于数学压缩 $T_c$ 及同一比较设计，再以 (23.16) 比较 $L_{E_c}$ 与 $L_{E_0}$，给出

$$
\|T-L_{E_0}\|_\diamond
\le\|T-T_c\|_\diamond+\|T_c-L_{E_c}\|_\diamond
    +\|L_{E_c}-L_{E_0}\|_\diamond,
$$

即 (24.3)。在 $B$ 中取支撑秩项，使用 $\|E_c\|_{\mathrm{op}}\le1$ 与 $\operatorname{rank}E_c\le r_0$，即得 (24.4)。若 $E_0=0$，则 $E\le\epsilon I_H$，直接由 (20.12) 得 $\|T-L_{E_0}\|_\diamond=\|T\|_\diamond\le d\epsilon$。

任意小效果误差允许实际秩改变：例如 $E_0=\operatorname{diag}(1,0)$、$E=\operatorname{diag}(1,\epsilon)$，$0<\epsilon\le1$，满足 (23.2)，但秩分别为一和二。因此这里使用名义秩必须先经 (24.2) 与 (24.6) 支付输入泄漏及比较得分误差；不能在 (23.8) 中直接换秩。输入交叉块的缩放沿用 (20.16) 的正映射方法；新增的联系是把名义输入支撑误差同时接到得分预算和目标支撑秩界。$\square$

### 命题 24.2（分别精确的设计不能替代共同标签与同一过程）

在 $H=K=\mathbb C^2$、$J=I$、$E=E_0=I$ 下，即使实际准备与实际读回各自组成精确射影二阶设计，未条件化得分也可等于 $Q(I)=1$ 而同一实际分支距 $\operatorname{id}$ 的 diamond 距离为二。

**证明。** 取 Pauli 三轴的六个本征态投影 $p_{\alpha,\pm}=(I\pm\sigma_\alpha)/2$，各权重 $1/6$，其中 $\alpha=x,y,z$。由

$$
\sum_{\alpha,\pm}\frac16p_{\alpha,\pm}\otimes p_{\alpha,\pm}
=\frac14I\otimes I+\frac1{12}\sum_\alpha\sigma_\alpha\otimes\sigma_\alpha
=\frac{I+\mathsf S}{6}
$$

知它们是 (23.1) 的二阶设计。令 $Z=\sigma_z$，实际共同分支、准备和读回分别为

$$
T(X)=ZXZ,\qquad \rho_s=p_s,\qquad F_s=Zp_sZ.
$$

酉共轭保留二阶矩，故读回也自成精确设计；它在 $x,y$ 轴互换两个标签，在 $z$ 轴保留标签。每个实际联合读回项为
$\operatorname{Tr}[Zp_sZ\,T(p_s)]=1$，所以得分为一。可是 $T$ 将 $p_{x,+}$ 送到正交的 $p_{x,-}$，从而 $\|T-\operatorname{id}\|_\diamond\ge2$；两个通道之差的上界二使其恰为二。

在定义 23.1 的共同标签比较中，$a=0$、$q_s=1$，而四个 $x,y$ 轴读回的 $\|F_s-G_s\|_{\mathrm{op}}$ 都为一，另两个为零，所以可取且必须有 $b\ge2/3$。同一 $T$ 的比较评价为 $R(T)=1/3$，实际缺口为 $2/3$。两端分别为精确设计并不将这个配对误差变为零。

同一过程前件也不能由校准读数推出。仍用这些比较准备和读回，若校准调用为 $T_{\rm cal}=\operatorname{id}$、后续调用为 $T_{\rm use}=\operatorname{Ad}_Z$，校准时全部误差预算可为零，两个映射的效果也同为 $I$，后续误差仍为二。这个配对不满足 (23.4) 与后续调用共用一个 $T$ 的前件，故不是定理 23.2 的反例。$\square$

### 定义 24.3（普通分支、完整仪器与取得量词）

(23.1)–(23.5) 的共同误差合同固定一个正分支、同一标签配对、同一坐标与同一记忆条件。实际读回误差预算 $b$、实际效果误差 $\epsilon$、准备误差 $a$ 和读数误差 $\nu$ 是共同前件，不由 $\widehat R$ 的近饱和自行供应。将此合同赋给一族历史或分支，须对要求的每个索引成立；单一分支的存在不改成全族的一致控制。

实际 $T$ 若只正，(23.8) 与 (24.3) 中的参考仍是数学范数的量词；(23.11) 只对普通正输入态作条件化。实际含参考的联合输出若要作为态，须另给相应正延伸；实际完整仪器若以有限标签 CP 分支 $\{T_j\}$ 表示，须对每个真实分支给 CP 及共同完整记录空间，并要求 $\sum_jT_j$ 保迹。指定单个成功分支的合同不确定其余失败分支、后续条件更新或完整历史。全菜单边界仍用定义 19.2；近饱和不推出精确 CP 的障碍仍用命题 21.1。

成功条件态使用 (23.10) 中各自的 $p,q$。在一族输入上要有一致趋零的条件态误差，须另有足以控制 (23.11) 中比值的成功概率或相对误差合同；绝对误差趋零本身不供应它，稀有成功的原反例见第 6 节。名义支撑秩只能按定理 24.1 使用，不能把趋于零的泄漏当成支撑已经相同。

共同准备、效果与读回的取得量词是 (23.3)–(23.5) 的同一实际实现，不是分别存在的准备、效果和读回之积。比较二阶设计的存在、不等式的成立及实际对象的供应是不同前件。上述合同不含 FIB 原三时全 $64$ 坐标取得性，也不把行列式零闭包变为实际零点；它不补充 [C122 定理 5.8](AURIC_INTERNAL_BINARY_RECIPROCITY_AND_EXPLICIT_RECONNECTION_C122.md#thm-c122-implemented-certificate) 对实际确定性 CPTP 恢复及完整逆门误差的独立要求。

## 追加锚（本行以下为增补区）


## 25. 同一完整原仪器从忠实校准到活动记忆的定量提升

### 定义 25.1（原记录、联合装置与同时校准合同）

取非零有限维复 Hilbert 空间 $H,K,M$，$d=\dim H$；$M$ 是装置内部全部会影响以后调用的保留记忆，包括持续经典模式。矩阵代数记为 $\mathcal B(H)$，迹为通常未归一化迹。对复线性映射采用不除二的范数

$$
\|\Phi\|_\diamond
=\sup_{R,X\ne0}
\frac{\|(\Phi\otimes\operatorname{id}_R)(X)\|_1}{\|X\|_1},
\tag{25.1}
$$

其中 $R$ 遍历有限维复参考，$X$ 是整个输入与 $R$ 上的任意矩阵。$\|\cdot\|_1,\|\cdot\|_{\mathrm{op}},\|\cdot\|_{\mathrm{HS}}$ 分别为迹范数、算子范数和 Hilbert–Schmidt 范数。以下映射误差均在 (25.1) 的拓扑中；本节的有限矩阵空间上各范数拓扑等价，不据此更换数值预算。

固定一个实际完整仪器

$$
V_j:\mathcal B(H\otimes M)\longrightarrow\mathcal B(K\otimes M),
\qquad j\in\mathsf J,
\qquad \sum_jV_j\text{ 保迹},
\tag{25.2}
$$

$\mathsf J$ 是有限的**原可访问记录**集合，包含全部成功和失败记录；每个 $V_j$ 完全正。校准和每次所覆盖调用使用同一个 (25.2)，不只要求装置名称相同或系统边缘相同。内部不再返回的新环境可在每次调用中丢弃；以后会返回的环境须计入同一 $M$。装置切换、遗漏的持续环境和未计入的时变控制不属于这个固定联合映射前件。

校准实际采用与探针、外部参考及输出标签无关的乘积记忆准备 $\tau$，满足

$$
\operatorname{Tr}\tau=1,\qquad \tau\ge\lambda I_M,\qquad\lambda>0.
\tag{25.3}
$$

因此同一校准分支为 $T_j(X)=\operatorname{Tr}_M V_j(X\otimes\tau)$。给定非零矩形算子 $K_j:H\to K$，置

$$
\mathcal A_j=\operatorname{Ad}_{K_j},\qquad
\operatorname{Ad}_{K_j}(X)=K_jXK_j^*,\qquad
E_j=K_j^*K_j,\qquad
\sum_jE_j=I_H.
\tag{25.4}
$$

要求这些效果在自伴实向量空间中线性独立，并对**同一仪器的全部原记录同时**给定

$$
\|T_j-\mathcal A_j\|_\diamond\le\delta_j,
\qquad \delta_j\ge0.
\tag{25.5}
$$

(25.2)–(25.5) 均为显式前件。尤其是原联合仪器的 CP、忠实乘积准备、全部单 Kraus 目标以及效果独立性，不从近饱和或其他表示／供应结论推得。效果独立性蕴含 $|\mathsf J|\le d^2$；结构性零效果不满足这个前件。

选择任意自伴实对偶 $F_j$，并定义

$$
\begin{aligned}
\operatorname{Tr}(F_jE_\ell)&=\delta_{j\ell},&
\kappa_j&=\|F_j\|_1,\\
h_j&=\sqrt{d\delta_j/\lambda},&
e_j&=(2+h_j)h_j,\\
e&=\sum_je_j,&t_j&=\kappa_je.
\end{aligned}
\tag{25.6}
$$

对偶存在：实 Gram 矩阵 $G_{a b}=\operatorname{Tr}(E_aE_b)$ 正定，故可取 $F_j=\sum_a(G^{-1})_{ja}E_a$。对偶的选择影响条件数及预算，不改变原目标和标签。

### 定理 25.2（忠实校准与效果独立性共同控制原联合仪器）

在定义 25.1 下，若每个 $t_j<1$，则存在仅用于比较的记忆 CPTP 映射
$\widehat B_j:\mathcal B(M)\to\mathcal B(M)$，使两个完整旗标通道

$$
\begin{aligned}
\mathfrak V(X)&=\sum_j|j\rangle\langle j|\otimes V_j(X),\\
\mathfrak W(X)&=\sum_j|j\rangle\langle j|
 \otimes(\mathcal A_j\otimes\widehat B_j)(X)
\end{aligned}
\tag{25.7}
$$

具有共同类型 $\mathcal B(H\otimes M)\to\mathcal B(\mathbb C^{\mathsf J}\otimes K\otimes M)$，且

$$
\boxed{
\|\mathfrak V-\mathfrak W\|_\diamond\le\Delta
:=\min\left\{2,\sum_j\left[e_j+\|E_j\|_{\mathrm{op}}f(t_j)\right]\right\},
\qquad
f(t)=\frac{(\sqrt{1+t}+1)t}{1+\sqrt{1-t}}\quad(0\le t<1).
}
\tag{25.8}
$$

特别地，(25.8) 对任意与 $M$ 相关的输入及任意惰性参考统一成立；后续调用的记忆不必等于 $\tau$、不必乘积，也不复位。$\widehat B_j$ 的存在不授予任何记忆端口、装置替换或新合法接续。标签始终是 $j$，下证的环境／矩阵指标不是新增原记录。

**证明。** 先在每个固定原记录内部取有限 Stinespring 算子

$$
A_j:H\otimes M\longrightarrow K\otimes M\otimes Z_j,
\qquad V_j(X)=\operatorname{Tr}_{Z_j}A_jXA_j^*.
\tag{25.9}
$$

这是有限 CP 映射的成熟表示定理；[Watrous，定理 2.22](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf) 对非零映射给出 CP、正 Choi、Kraus 与 Stinespring 表示的等价性，零映射直接取零算子。由完整性，$A_j^*A_j=V_j^\dagger(I)\le I$，所以 $\|A_j\|_{\mathrm{op}}\le1$。这些算子不必等距。

将 $\tau$ 对角化为 $\sum_\mu p_\mu|\mu\rangle\langle\mu|$，$p_\mu\ge\lambda$。以 $a$ 标记输出 $M\otimes Z_j$ 的正交基，写

$$
A_{j,a\mu}=(I_K\otimes\langle a|)A_j(I_H\otimes|\mu\rangle):H\to K.
\tag{25.10}
$$

于是 $T_j$ 的一个数学 Kraus 表示为 $\{\sqrt{p_\mu}A_{j,a\mu}\}_{a,\mu}$。在 $\mathcal B(H,K)$ 的 Hilbert–Schmidt 空间内投影到 $K_j$ 所张成的一维复空间：

$$
\begin{aligned}
b_{j,a\mu}&=\frac{\operatorname{Tr}(K_j^*A_{j,a\mu})}{\operatorname{Tr}E_j},\\
C_{j,a\mu}&=A_{j,a\mu}-b_{j,a\mu}K_j,\\
B_j|\mu\rangle&=\sum_ab_{j,a\mu}|a\rangle,
\qquad B_j:M\to M\otimes Z_j,\\
L_j&=K_j\otimes B_j,
\qquad C_j=A_j-L_j.
\end{aligned}
\tag{25.11}
$$

$L_j$ 的输入、输出张量因子按 (25.9) 自然排列。$\operatorname{Tr}E_j>0$，所以这里没有对零目标作除法。

使用未归一化向量化 $|D\rangle\!\rangle=\sum_{r=1}^dD|r\rangle\otimes|r\rangle$，令 $J(\Phi)=(\Phi\otimes\operatorname{id}_H)(|I_H\rangle\!\rangle\langle\!\langle I_H|)$，以及

$$
Q_j=I_{K\otimes H}
-\frac{|K_j\rangle\!\rangle\langle\!\langle K_j|}{\operatorname{Tr}E_j}.
$$

$Q_j$ 是正交投影，且 $Q_jJ(\mathcal A_j)=0$。由 (25.5)，

$$
\|J(T_j)-J(\mathcal A_j)\|_1\le d\delta_j.
\tag{25.12}
$$

由于 $J(T_j)\ge0$，投影后的总质量为非负，并有

$$
\begin{aligned}
\lambda\|C_j\|_{\mathrm{HS}}^2
&\le\sum_{a,\mu}p_\mu\|C_{j,a\mu}\|_{\mathrm{HS}}^2\\
&=\operatorname{Tr}[Q_jJ(T_j)]\\
&=\operatorname{Tr}[Q_j(J(T_j)-J(\mathcal A_j))]
\le d\delta_j.
\end{aligned}
\tag{25.13}
$$

第一步使用全部输入记忆方向的 $p_\mu\ge\lambda$；等式使用向量化的 Hilbert–Schmidt 等距及 (25.11) 的正交投影。因此

$$
\|A_j-L_j\|_{\mathrm{op}}\le h_j,
\qquad \|L_j\|_{\mathrm{op}}\le1+h_j.
\tag{25.14}
$$

置 $\mathcal B_j(Y)=\operatorname{Tr}_{Z_j}B_jYB_j^*$，它此时仅为 CP 映射。对任意参考和任意矩阵，展开

$$
A_jXA_j^*-L_jXL_j^*
=(A_j-L_j)XA_j^*+L_jX(A_j-L_j)^*.
$$

Schatten 乘子不等式和环境偏迹的 diamond 范数一给

$$
\|V_j-\mathcal A_j\otimes\mathcal B_j\|_\diamond
\le(\|A_j\|_{\mathrm{op}}+\|L_j\|_{\mathrm{op}})
       \|A_j-L_j\|_{\mathrm{op}}
\le e_j.
\tag{25.15}
$$

这一步正是共同 Stinespring 算子的成熟上界方向，参见 [Kretschmann–Schlingemann–Werner，命题 3 及式 (14)](https://arxiv.org/pdf/0710.2495)：该文对 CP 映射及其共同表示使用 cb 算子范数；有限维取迹对偶即为这里的 diamond 范数。仓内 [V96 定理 60.1 的 (60.3)–(60.5)](AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96.md#60-两条有限误差读数控制全部效果与全部有限维数) 已复用同一估计。不在此假定任意选取的两个扩充已接近；(25.13) 是为原 $A_j$ 构造 $L_j$ 的具体依据。

下一步同时使用全部原分支的完整性，而非对每支另作保迹假定。令

$$
S_j=B_j^*B_j=\mathcal B_j^\dagger(I_M),
\qquad
D=\sum_jE_j\otimes(S_j-I_M).
$$

若 $\Phi$ 是自伴保持映射，则对任意单位向量 $v$，
$|\langle v,\Phi^\dagger(I)v\rangle|
=|\operatorname{Tr}\Phi(|v\rangle\langle v|)|\le\|\Phi\|_\diamond$。
将此应用于 (25.15) 的映射差并求和，由 $\sum_jV_j^\dagger(I)=I$ 和 $\sum_jE_j=I$ 得

$$
\|D\|_{\mathrm{op}}\le\sum_je_j=e.
\tag{25.16}
$$

在系统因子上用真实效果对偶提取，得到

$$
S_j-I_M=\operatorname{Tr}_H[(F_j\otimes I_M)D],
\qquad
\|S_j-I_M\|_{\mathrm{op}}\le\|F_j\|_1\|D\|_{\mathrm{op}}
\le t_j.
\tag{25.17}
$$

范数不等式可直接由 $F_j$ 的自伴谱分解验证：每个压缩
$(\langle u|\otimes I)D(|u\rangle\otimes I)$ 的算子范数至多 $\|D\|_{\mathrm{op}}$，谱系数绝对值之和为 $\|F_j\|_1$。这里不要求 $F_j$ 为正，也不忽略效果间的条件数。

由 $t_j<1$，$S_j\ge(1-t_j)I_M>0$。在数学比较中定义

$$
\widehat B_j^{\mathrm{St}}=B_jS_j^{-1/2},
\qquad
\widehat B_j(Y)=\operatorname{Tr}_{Z_j}
 \widehat B_j^{\mathrm{St}}Y(\widehat B_j^{\mathrm{St}})^*.
\tag{25.18}
$$

因为 $(\widehat B_j^{\mathrm{St}})^*\widehat B_j^{\mathrm{St}}=I_M$，$\widehat B_j$ CPTP。极分解 $B_j=\widehat B_j^{\mathrm{St}}S_j^{1/2}$ 给

$$
\begin{aligned}
\|B_j\|_{\mathrm{op}}&\le\sqrt{1+t_j},\\
\|B_j-\widehat B_j^{\mathrm{St}}\|_{\mathrm{op}}
&=\|S_j^{1/2}-I_M\|_{\mathrm{op}}\\
&\le\frac{t_j}{1+\sqrt{1-t_j}}.
\end{aligned}
\tag{25.19}
$$

最后一步由 $s\in[1-t_j,1+t_j]$ 上的
$|\sqrt s-1|=|s-1|/(1+\sqrt s)$ 逐谱值得出。再次使用 (25.15) 的共同扩充估计，

$$
\|\mathcal B_j-\widehat B_j\|_\diamond\le f(t_j),
\qquad
\|\mathcal A_j\otimes(\mathcal B_j-\widehat B_j)\|_\diamond
\le\|E_j\|_{\mathrm{op}}f(t_j).
\tag{25.20}
$$

后一式使用 $\|\operatorname{Ad}_{K_j}\|_\diamond=\|K_j\|_{\mathrm{op}}^2=\|E_j\|_{\mathrm{op}}$；上界由乘子估计，下界在最大本征向量的正输入上取到。

对 (25.15)、(25.20) 取三角不等式，再将同一 $j$ 的差放入正交旗标块。任意输入上的块对角迹范数是各块迹范数之和，故完整差的 diamond 范数至多 (25.8) 中的和。$\mathfrak V$ 是通道；$\widehat B_j$ 保迹且 $\sum_jE_j=I_H$，所以 $\mathfrak W$ 也为通道，其差的 diamond 范数至多二。这给出截断及全部参考量词。$\delta_j=0$ 对全部 $j$ 成立时，$h_j=e=t_j=0$，上述构造直接给逐原记录的精确 $V_j=\mathcal A_j\otimes\widehat B_j$。$\square$

### 推论 25.3（原合法有限协议的完整输出与共同成功事件）

保留定理 25.2 的全部前件。取一个已经供应的有限合法协议，每条历史至多调用 (25.2) 共 $N$ 次；外部控制器、准备、读回、失败处理与停止规则均已供应，且两份比较使用同一套控制器。每个控制器的完整动作 CPTP，按原经典历史作适应性选择，作用于可访问系统与外部活动记忆，并在私有 $M$ 上为恒等；其后续输入端与 $H$、输出端与 $K$ 按原合法接续匹配。所有以后还会操作的外部量子寄存器计入活动空间，只有始终不操作的寄存器作为参考。

每轮的域、陪域包含已记录历史、活动系统、控制器状态和同一私有 $M$；新增记录使它们可以逐轮改变。提前停止的历史进入共同吸收块，用恒等步骤补齐至 $N$ 个槽，而不产生新的原调用或原记录。完整历史空间可用长度至多 $N$ 的有限词所标记的直和。只给成功控制支而遗漏其失败补全，不满足此协议前件。

以 $\mathcal P_V,\mathcal P_W$ 表示将槽中 $\mathfrak V$ 分别取为 $\mathfrak V,\mathfrak W$ 的全协议通道，保留全部原记录、外部输出及私有 $M$。它们有同一输入、输出类型，且

$$
\|\mathcal P_V-\mathcal P_W\|_\diamond
\le\varepsilon_N:=\min\{2,N\Delta\}.
\tag{25.21}
$$

对任意共同初始联合态，允许 $M$ 与可访问输入及参考相关，丢弃比较过程的私有 $M$ 后，$\mathcal P_W$ 的原记录／外部输出恰等于以同一初始可访问边缘、同一控制器和名义**原记录仪器** $\{\mathcal A_j\}$ 运行所得。因此实际完整可访问输出距该名义输出的未减半迹范数至多 $\varepsilon_N$；接任意共同合法末端测量，其完整记录／读数分布的总变差至多 $\varepsilon_N/2$。

成功事件须为同一原历史空间上的同一个已指定事件，或者同一完整末端仪器中的同一个事件；输出类型、标签对应和事件选择不能在两份过程之间改变。设该事件的两份未归一化正输出为 $A,B$，各自实际概率为 $p=\operatorname{Tr}A$、$q=\operatorname{Tr}B$。则

$$
\|A-B\|_1\le\varepsilon_N,
\qquad |p-q|\le\varepsilon_N/2,
\tag{25.22}
$$

且仅在 $p,q>0$ 时同时定义的条件输出满足

$$
\boxed{
\left\|\frac A p-\frac B q\right\|_1
\le\min\left\{2,
\frac{\|A-B\|_1+|p-q|}{\max\{p,q\}}\right\}
\le\min\left\{2,\frac{\varepsilon_N}{\max\{p,q\}}\right\}.
}
\tag{25.23}
$$

若只知 $q>\varepsilon_N/2$，则 $p\ge q-\varepsilon_N/2>0$。若一边成功概率为零，不能给它定义归一化成功态；两边皆零时也不定义。没有正概率或相对误差合同，$\varepsilon_N\to0$ 不保证一族稀有事件的条件输出趋同。

**证明。** 这里复用 [Context Geometry 定理 12.2 的变类型式 (12.3a)、定义 12.4 与命题 12.5](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#12-可组合恢复连续缺陷与相对时钟)，以及其所引[量子历史卷 §72.1、§72.3](ContextualSpacetimeQuantum/072_098_HISTORY_AND_CAPACITY.md#72-仪器级历史误差参考系统与自适应读出)。在两份共同的逐轮类型间取编码为恒等、末端目标及解码为恒等，恢复预算为零；每个有调用的完整槽半 diamond 缺陷至多 $\Delta/2$。共同控制器的前后复合范数为一，停止块缺陷为零，故既有有限组合结论给 (25.21)。逐经典历史的控制是块对角的，其统一界由块权重求和；若实际允许历史相干操作，则须保留完整量子控制通道再应用 (25.8)，不能仅用经典分支最大值。这里并未将新的望远镜恒等式当作成果。

比较记忆可带任意相关性。对任意带外部寄存器的 $X$，保迹性逐块给出

$$
\operatorname{Tr}_M[(\mathcal A_j\otimes\widehat B_j
 \otimes\operatorname{id})(X)]
=(\mathcal A_j\otimes\operatorname{id})(\operatorname{Tr}_M X).
\tag{25.24}
$$

同一外部控制器也与 $\operatorname{Tr}_M$ 交织。由 (25.24) 对完整历史归纳，每个原词的未归一化外部输出等于名义原仪器的对应输出；所有中途成功和失败概率已包含在这些输出的迹中。此归纳没有把记忆归一化后重新代回，也没有删去失败记录。

对同一输入的两份完整输出，差自伴且迹为零；共同二结果事件读口给 $|p-q|\le\varepsilon_N/2$。保留事件与补事件，记补事件输出为 $A_c,B_c$。共同完整仪器的收缩性给

$$
\|A-B\|_1+\|A_c-B_c\|_1\le\varepsilon_N,
\qquad |p-q|=|\operatorname{Tr}(A_c-B_c)|\le\|A_c-B_c\|_1.
\tag{25.25}
$$

这证明 (25.22) 及 $\|A-B\|_1+|p-q|\le\varepsilon_N$。对 $p,q>0$，分别在分母 $p$ 和 $q$ 下展开条件态之差，得到分母为 $p$ 及 $q$ 的两条上界；取较小者并截断于二即得 (25.23)。这个较紧的最后一步使用共同完整事件的补事件预算，不把一般两个未归一化算子的迹差无条件除以二。$\square$

## 26. 原记录相关性与忠实准备的不可省略边界

### 命题 26.1（效果依赖允许精确单次校准与持续历史相关）

保留固定完整 CP 联合仪器、忠实乘积校准以及单 Kraus 目标，但删除效果独立性时，即使所有 $\delta_j=0$，原两次记录仍可不同于名义仪器的记录；成功因子和全部失败记录均可保持。这个反例否定在该删减类中由精确单次校准无条件推出 (25.8) 的零误差结论，不声称每个效果依赖的仪器都有此问题。

**证明。** 取 $H=K=\mathbb C^2$、$M=\mathbb C^2$，$P_b=|b\rangle\langle b|$，$\tau=I_M/2$，$0<a<1$。原标签为 $\mathsf J=\{s_0,s_1,f\}$；两个 $s_b$ 都为成功，$f$ 为完整失败。对每次调用使用同一个仪器

$$
\begin{aligned}
V_{s_b}(X)&=a(I_H\otimes P_b)X(I_H\otimes P_b),\\
V_f(X)&=(1-a)\sum_{b=0}^1(I_H\otimes P_b)X(I_H\otimes P_b).
\end{aligned}
\tag{26.1}
$$

各支 CP，其和是记忆去相干通道，故保迹。它始终保留隐藏比特，没有按调用次序换装置。忠实校准满足

$$
\begin{aligned}
T_{s_b}&=(a/2)\operatorname{id}_H=\operatorname{Ad}_{\sqrt{a/2}I_H},\\
T_f&=(1-a)\operatorname{id}_H=\operatorname{Ad}_{\sqrt{1-a}I_H},\\
E_{s_0}=E_{s_1}&=(a/2)I_H,\qquad E_f=(1-a)I_H.
\end{aligned}
\tag{26.2}
$$

因此所有校准误差为零，效果之和为单位，但效果线性依赖。令初态为任意系统态与 $\tau$ 的乘积，无外部中间操作。对原词 $w\in\{s_0,s_1,f\}^n$，记成功数为 $k$、失败数为 $r=n-k$。实际和名义完整词概率分别为

$$
\begin{aligned}
P_V(w)&=a^k(1-a)^r
\begin{cases}
1,&k=0,\\
1/2,&k\ge1\text{ 且全部成功标签相同},\\
0,&\text{其他情形},
\end{cases}\\
P_{\mathcal A}(w)&=(a/2)^k(1-a)^r.
\end{aligned}
\tag{26.3}
$$

系统未归一化输出就是各自概率乘同一系统输入态。这由隐藏比特的两值各占 $1/2$、各轮成功率均为 $a$、失败率均为 $1-a$ 直接相乘得到；失败支内的两个数学 Kraus 指标始终未变成原记录。

特别地，两次调用的四个全成功词中，实际 $s_0s_0,s_1s_1$ 各为 $a^2/2$，混合两个词各为零；名义四词各为 $a^2/4$。所有含一个成功的词 $s_bf,fs_b$ 在两边都为 $a(1-a)/2$，$ff$ 在两边都为 $(1-a)^2$。所以完整记录的未减半 $\ell^1$ 差为 $a^2$，总变差为 $a^2/2$。共同事件“两个调用均成功”在两边的概率都是 $a^2>0$；在这个实际分母上条件化，记录的未减半 $\ell^1$ 差为一。所有步的成功因子及完整失败概率均已支付。

若存在精确的 $V_{s_b}=\mathcal A_{s_b}\otimes\widehat B_{s_b}$ 且 $\widehat B_{s_b}$ 保迹，则两边的联合效果应分别为 $aI_H\otimes P_b$ 与 $(a/2)I_H\otimes I_M$，相互不等。因此不能以比较记忆的保迹性抹去这个原记录区别。保留 $a\downarrow0$ 时的 $a^2$ 可见稀有成功因子；$a=0$ 时共同全成功事件概率为零，条件记录不再有定义。$\square$

### 命题 26.2（非忠实准备可漏掉下一次会到达的记忆方向）

删除 (25.3) 的忠实下界后，即使单一原记录的效果独立、校准误差为零、联合仪器固定且完全正，从校准初态连续两次调用也不必保持名义系统历史。

**证明。** 取同样的二维 $H,K,M$，令 $Z=\operatorname{diag}(1,-1)$、$\tau=P_0$，只有一个原记录 $j$，目标 $K_j=I_H$、$E_j=I_H$。固定酉算子与完整单支仪器为

$$
U=I_H\otimes|1\rangle\langle0|+Z\otimes|0\rangle\langle1|,
\qquad V_j=\operatorname{Ad}_U.
\tag{26.4}
$$

两项的输入、输出记忆方向正交，故 $U^*U=UU^*=I$。对每个系统矩阵，$V_j(X\otimes P_0)=X\otimes P_1$，所以校准恰为恒等。可是下一次 $V_j(X\otimes P_1)=ZXZ\otimes P_0$；从 $|+\rangle\langle+|\otimes P_0$ 出发，两次实际系统输出为正交的 $|-\rangle\langle-|$，名义两次输出仍为 $|+\rangle\langle+|$，未减半距离为二。这里无装置切换或记忆复位；缺失的正是 (25.13) 对全部记忆列的控制。$\square$

## 27. 与既有供应、精确因子化和有限组合的逐项对应

### 定义 27.1（定量联系与成熟工具的归属）

本节的 repo-derived 综合是 (25.12)–(25.20) 的共同链：秩一目标的 Choi 正交剩余经忠实准备提升到**原联合装置全部输入方向**，完整仪器的效果对偶再分别控制记忆保迹缺陷，最后构造同标签比较 CPTP 记忆并保留显式 $d,\lambda,\kappa_j$ 和 $\|E_j\|_{\mathrm{op}}$。这条链给 (25.8)，而不是仅对已知的两份系统通道取三角不等式。所用投影、Stinespring 乘子上界和极分解本身均为成熟工具，不提出文献首发、穷尽检索或常数最优性主张。

精确因子化已有仓内供应：[FIB 相界卷引理 141.2](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md#1413-满秩附加态强制相干子系统运输) 从同一固定 Stinespring 实现、忠实附加态及精确逻辑恒等合同，用秩一 Choi 正性得到附加因子化和等距记忆运输。令本节只含一个标签、$K_j=I_H$、$\delta_j=0$，便回到这个机制的无编码特例；一般 $K_j$ 的秩一投影及零剩余也沿用同一机制。不能将这项精确机制重新计为本节成果。当前正误差链另需 (25.13) 的 $d\delta_j/\lambda$ 控制，以及由全部真实效果共同提取的 (25.17)；精确恒等供应不直接给这两项的预算。

有限组合也已有供应：C119 所在[无参考滤片关系卷推论 104.1](AURIC_COMPOSITE_COMPARISON_REFERENCE_FREE_FILTER_RELATIONS_V96_CONTINUATION.md#104-从关系约束回到量子力学接口) 给有限成功词的范数传播，并显式保留效果乘积；Context Geometry §11 的活动记忆历史及 §12.2、§12.4–12.5、量子历史卷 §72 已给完整通道和自适应协议的传播。推论 25.3 仅在 (25.8) 已经供应包含私有 $M$ 的完整槽误差后消费它们，半 diamond 预算为 $\Delta/2$。它没有从校准平均误差直接跳到逐历史保证。

[C122 定理 5.6–5.8](AURIC_INTERNAL_BINARY_RECIPROCITY_AND_EXPLICIT_RECONNECTION_C122.md#section-5) 的有限层析及 $e_0+\delta_{\rm tom}+\eta$ 控制已分开名义恢复、同一实际通道估计和实际确定性实现。其系统通道的层析预算本身不控制原扩充在其他记忆方向的作用；本节另外要求 (25.2)–(25.5)，并用 (25.13) 支付这种提升。上述三角界不作为这里的新定理。

### 定义 27.2（旧原菜单与本节目标的精确匹配条件）

C119 §§150–157 的原标签、A/B/C1/C2/C3 及完整原片段条件，尤其其定理 152.1，区分所选规范支、旧命名支、带成功因子的准备及完整失败记录。它们不自动给同一保留记忆上的 (25.2)、忠实乘积准备 (25.3) 或一组效果独立的原仪器 (25.4)。本节直接以这些对象为前件，不能用一个作用相同的新规范滤片替换旧仪器后声称完成校准。数学上将同一映射作分解也不开放原装置端口；这个边界与 [C120 命题 12.3](AURIC_COMPARISON_DYNAMICAL_CURVATURE_FINITE_FRAME_QUANTUM_V95.md#12-全有限直和满足族与身份保持的-f-删除模型) 的同映射分解边界相同。

[C123 及其 C124 续篇 §§10–17](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#10-c124整个原指针上的原子确定配对) 在 P/G/D、整个原指针的 AC、精确 $N_u$、X/Xs、全事件 R、原 F／遗忘／返回及指定合法接续下给精确端点供应；定义 17.3 明确保留误差鲁棒性、旧输出校准和任意仪器组装的独立缺口。即使其条件成立，也须另外建立本节的共同原联合仪器及校准前件，不能从精确端点存在反推 (25.5)，也不要求该供应一定包含 $M_2$ 对象。

本卷 (23.8) 或 (24.3) 的 $\beta_j$ 只有在其实际分支正是 $T_j=\operatorname{Tr}_M V_j(\cdot\otimes\tau)$、指定目标**恰为** $K_j=J_j\sqrt{E_{0,j}}$、共同标签／坐标／设计及误差合同对全部原 $j$ 同时成立时，才可用作这里的 $\delta_j$。同效果但不同 $J_j$、不同目标、不同记忆准备或不同校准装置不能代入；单一成功支的 $\beta$ 也不认证其余失败支。这里的原联合 CP 来自 (25.2)，不来自近饱和；命题 21.1 的近饱和不推出精确 CP 边界继续保留。

### 定义 27.3（条件强度、历史范围与经验边界）

效果独立性和忠实下界是定理 25.2 的充分条件；命题 26.1–26.2 证明在相应删减类中无条件推广会失败，不证明所有更大原签名都必须采用这组充分条件。效果依赖的记忆无关仪器也可以精确等于 (25.7) 的比较形式。$t_j<1$ 保证本构造的 $S_j$ 可逆；不满足它只表示这个数值证书未给出所述修正，不推出装置不可能接近名义目标。小 $\lambda$、病态效果对偶、较大 $d$ 和增长的 $N$ 均可使预算失去效用。

固定同一实际装置是实质前件；本卷命题 24.2 的校准恒等、后续 $\operatorname{Ad}_Z$ 切换不满足它。这里允许的变化发生在同一 $V_j$ 内部的活动记忆态，而不是在调用间无证更换 $V_j$。比较用 $\widehat B_j$ 无须成为原菜单成员；推论 25.3 比较的是已经合法的原协议与一份数学名义历史，不供应复位、未知逆门、任意新控制器、额外参考或替换硬件。

[GST，§6.1](https://arxiv.org/pdf/2009.07301v2) 将遗漏的内外语境变量、漂移和持续环境列为门集模型失配的来源；它讨论拟合和模型检验，不给由有限拟合推出无限未来平稳性的定理。本节也没有经验核验 (25.2)–(25.5)：给定这些关于同一原装置的数学前件后，对每个已合法的有限 $N$ 得到 (25.21)，不从有限数据认证无界未来仍用同一个联合映射。[C117 §16](AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md#16-受控终端字行到局部-lorentz-预测锥的桥) 的全部未来预测锥结论仍保留其无限假设；[FIB 边界几何附录 III 推论 141.3](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md#141-a-source-preserving-reflection-and-the-invariant-constrained-negative-vector) 的原保留端点条件性秩至多二结论既不被改回未解，也不被提升为原矩阵相等或三时全部 $64$ 坐标的取得。条件化只按 (25.22)–(25.23) 的实际正分母进行，本卷第 6 节的稀有成功边界不因完整通道误差较小而消失。

## 追加锚（本行以下为增补区）

## 28. 固定相关来源的三阶零泄漏与原联合细支

**定义 28.1（同源局部准备与完整原仪器）。** 设 $H=\mathbb C^d$、$d\ge1$，$M$ 为非零有限维复记忆空间。标签选择以前固定同一归一联合态 $\rho\in\mathcal B(H\otimes M)$，允许任意混合性和相关性。记

$$
\rho_M=\operatorname{Tr}_H\rho,\qquad
M_0=\operatorname{supp}\rho_M,\qquad I_0=I_{M_0}.
\tag{28.1}
$$

$\rho$ 的输入支撑包含于 $H\otimes M_0$：若 $m\in\ker\rho_M$，则 $\sum_i\langle e_i,m|\rho|e_i,m\rangle=0$，正性使 $\rho$ 消灭整个 $H\otimes\ker\rho_M$。以后把 $\rho$ 视为该输入子空间上的算子，但不将原输出记忆压回 $M_0$。

对每个秩一投影 $p=|z\rangle\langle z|$、$\|z\|=1$，已合法的原局部准备成功支恰为 $\operatorname{Ad}_{p}\otimes\operatorname{id}_M$；同一准备装置的全部原失败记录及其动作保留。其未归一化成功输出为

$$
\begin{aligned}
X_p&=(p\otimes I_M)\rho(p\otimes I_M)=p\otimes\sigma_p,\\
\sigma_p&=(\langle z|\otimes I_M)\rho(|z\rangle\otimes I_M)
=\operatorname{Tr}_H[(p\otimes I_M)\rho]\ge0,\\
\eta_p&=\operatorname{Tr}\sigma_p=\operatorname{Tr}(p\rho_H)\in[0,1].
\end{aligned}
\tag{28.2}
$$

$\sigma_p$ 与相位选择无关。$\eta_p=0$ 时 $X_p=0$，仍保留该标签，不定义其归一准备态。准备改变记忆条件态的关系由同一个 $\rho$ 决定，不用一族独立供应的乘积态代替；相关准备的这一对象区别参见 [Modi，arXiv:1011.6138v4](https://arxiv.org/pdf/1011.6138v4)。

原被调用装置固定为一份完整有限 CP 仪器

$$
\{V_j:\mathcal B(H\otimes M)\to\mathcal B(H\otimes M)\}_{j\in\mathsf J},
\qquad \sum_{j\in\mathsf J}V_j^{\dagger}(I_{H\otimes M})=I_{H\otimes M}.
\tag{28.3}
$$

$\mathsf J$ 是原实际细记录集合，含全部成功和失败；同一标签有多个数学 Kraus 算子时，不将这些指标提升为新原记录。选定非空 $\mathsf C\subseteq\mathsf J$，只对这些原支要求零泄漏。令 $\iota:H\otimes M_0\hookrightarrow H\otimes M$ 为原包含，并记 $V_{j,0}(Y)=V_j(\iota Y\iota^{\dagger})$。输出仍在完整 $H\otimes M$ 中。完全正的 Kraus 表示及完整性采用 [Watrous，TQI 第 2 章，定理 2.22、2.26](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf) 的有限维约定。

**假设 28.2（正权三阶设计上的精确未条件化零泄漏）。** 同一来源及同一仪器不随 $s$ 改变。已合法的有限准备节点 $\{(w_s,p_s)\}_{s\in S}$ 满足 $w_s>0$、$\sum_sw_s=1$，且

$$
\sum_sw_sp_s^{\otimes3}
=\int p^{\otimes3}\,d\mu(p)
=\frac{\Pi_{\rm sym}^{(3)}}{\binom{d+2}{3}}.
\tag{28.4}
$$

这里 $\mu$ 为归一复射影 Haar 测度，$\Pi_{\rm sym}^{(3)}$ 为三重对称投影。取偏迹同时给一阶、二阶矩。矩公式复用 [Scott，arXiv:quant-ph/0604049v6，引理 1](https://arxiv.org/pdf/quant-ph/0604049v6) 及 [Roy–Scott，arXiv:quant-ph/0703025v2，定义 2.1、式 (2.2)–(2.3)](https://arxiv.org/pdf/quant-ph/0703025v2)。$w_s$ 是数学求积权，不预设它等于原物理标签概率。

精确合同是

$$
\mathcal L:=\sum_sw_s\sum_{j\in\mathsf C}
\operatorname{Tr}\!\left[((I_H-p_s)\otimes I_M)V_j(X_{p_s})\right]=0.
\tag{28.5}
$$

所有项都是未条件化的非负质量；没有除以 $\eta_{p_s}$ 或分支成功率。泄漏式使用同一原联合映射的完整输出及系统补投影，不预设系统边缘的某个规范分解。

**定理 28.3（三阶合同迫使逐原细支在来源记忆支撑上因子化）。** 在定义 28.1 与设计条件 (28.4) 下，(28.5) 当且仅当对每个原 $j\in\mathsf C$ 存在 CP 映射 $\Psi_j:\mathcal B(M_0)\to\mathcal B(M)$，使

$$
\boxed{\quad V_{j,0}=\operatorname{id}_H\otimes\Psi_j.\quad}
\tag{28.6}
$$

等式对 $\mathcal B(H\otimes M_0)$ 的全部算子成立，保留完整返回记忆；对每个有限维惰性参考 $R$ 及每个 $Y\in\mathcal B(H\otimes M_0\otimes R)$，还成立

$$
(V_{j,0}\otimes\operatorname{id}_R)(Y)
=(\operatorname{id}_H\otimes\Psi_j\otimes\operatorname{id}_R)(Y).
\tag{28.7}
$$

其记忆效果满足

$$
G_j:=\Psi_j^{\dagger}(I_M)\ge0,\qquad
\sum_{j\in\mathsf C}G_j\le I_0.
\tag{28.8}
$$

若 $\mathsf C=\mathsf J$，最后一个不等式为等式。$\Psi_j$ 的输出可离开 $M_0$。结论不要求纯来源、联合满秩、已知最小本征值、满 steering 张成、乘积准备或效果独立；它也不约束未选失败支的动作，不把 (25.3)–(25.5) 的定量前件删除。

**证明。** 在输入支撑上取任意有限正分解

$$
\rho=\sum_a|v_a\rangle\langle v_a|,\qquad
v_a=\sum_{b=1}^de_b\otimes m_{ab},\qquad
\rho_M=\sum_{a,b}|m_{ab}\rangle\langle m_{ab}|.
\tag{28.9}
$$

谱权已经吸入 $v_a$；因此 $\operatorname{span}_{\mathbb C}\{m_{ab}\}=M_0$，但不要求任意一个 $v_a$ 有满 Schmidt 秩。

固定原 $j$ 的一个 Kraus 表示 $V_j(Z)=\sum_\alpha K_{j\alpha}ZK_{j\alpha}^{\dagger}$。对每个 $a,\alpha$ 及秩一 $p$ 置

$$
f_{j\alpha a}(p)
=\|((I_H-p)\otimes I_M)K_{j\alpha}(p\otimes I_M)v_a\|^2\ge0.
\tag{28.10}
$$

各项之和是 (28.5) 中对应 $j$ 的泄漏。由于 $p^2=p$，(28.10) 等于

$$
\begin{aligned}
&\langle v_a|(p\otimes I_M)K_{j\alpha}^{\dagger}K_{j\alpha}
       (p\otimes I_M)|v_a\rangle\\
&\quad-\langle v_a|(p\otimes I_M)K_{j\alpha}^{\dagger}
       (p\otimes I_M)K_{j\alpha}(p\otimes I_M)|v_a\rangle.
\end{aligned}
\tag{28.11}
$$

第一项是 $p$ 矩阵元的二次多项式，第二项为三次；所以三阶及其低阶矩已准确积分它，不需要四阶。由 (28.5) 的逐项非负性，$\sum_sw_sf_{j\alpha a}(p_s)=0$。用 (28.4) 得 $\int f_{j\alpha a}\,d\mu=0$。连续性及 Haar 测度的满支撑使 $f_{j\alpha a}(p)=0$ 对每个秩一 $p$ 成立：若某点严格正，则其一个开邻域有正积分，矛盾。

现在固定 $K=K_{j\alpha}$ 和 $a$，并写系统矩阵块

$$
K_{ri}=(\langle e_r|\otimes I_M)K(|e_i\rangle\otimes I_M).
$$

对任意非零 $z\in\mathbb C^d$，上述零式表示

$$
K\left(z\otimes\sum_b\overline z_bm_{ab}\right)\in z\otimes M.
\tag{28.12}
$$

单位向量的结论由齐次性推广到全部非零 $z$。令其第 $r$ 个输出记忆分量为
$F_r(z,\overline z)=\sum_{i,b}z_i\overline z_bK_{ri}m_{ab}$。
平行于 $z$ 给出全部向量值多项式恒等式

$$
z_tF_r(z,\overline z)-z_rF_t(z,\overline z)=0
\qquad(r,t=1,\ldots,d).
\tag{28.13}
$$

这些式在 $z=0$ 也为零。$z_i=x_i+iy_i$、$\overline z_i=x_i-iy_i$ 是 $2d$ 个多项式变量间的可逆复线性变换；在全部实 $(x,y)$ 上为零的复多项式系数全为零。因此可以把 $z,\overline z$ 当作独立变量，逐个提取 $\overline z_b$ 的系数，得到

$$
z_t\sum_iz_iK_{ri}m_{ab}
-z_r\sum_iz_iK_{ti}m_{ab}=0
\qquad\text{对全部 }z,r,t,b.
\tag{28.14}
$$

特别地，对每个 $a,b$，复线性映射
$L_{ab}:H\to H\otimes M$、$L_{ab}z=K(z\otimes m_{ab})$
满足 $L_{ab}z\in z\otimes M$。取 $z=e_i$ 得
$L_{ab}e_i=e_i\otimes n_i$；再取 $e_i+e_k$ 得 $n_i=n_k$。
故存在 $n_{ab}$ 使 $L_{ab}=I_H\otimes n_{ab}$。$d=1$ 时同一结论直接成立。

由此对每个 $m_{ab}$，全部非对角块 $K_{ri}m_{ab}$ 为零，全部对角块 $K_{ii}m_{ab}$ 相同。令 $B=K_{11}|_{M_0}:M_0\to M$；(28.9) 的张成性给

$$
K\iota=I_H\otimes B\quad\text{于整个 }H\otimes M_0.
\tag{28.15}
$$

这一步将同一来源中 $z$ 与 $\overline z$ 的关系提升为全部记忆列的约束，没有预设 $\{\sigma_p\}$ 张成所有记忆算子。对每个原 $j,\alpha$ 作此构造，定义

$$
\Psi_j(Z)=\sum_\alpha B_{j\alpha}ZB_{j\alpha}^{\dagger}.
\tag{28.16}
$$

它 CP；(28.15) 给 (28.6)，作为线性映射等式再张量恒等即给 (28.7)，不对参考与输入相关性加限制。原完整性给

$$
I_H\otimes\sum_{j\in\mathsf C,\alpha}B_{j\alpha}^{\dagger}B_{j\alpha}
=\iota^{\dagger}\left(\sum_{j\in\mathsf C,\alpha}
 K_{j\alpha}^{\dagger}K_{j\alpha}\right)\iota
\le I_H\otimes I_0,
\tag{28.17}
$$

从而得 (28.8)；选择全部原标签时用原完整性得等号。未选标签只在这个正补效果中出现，未被替换成另一份完成映射。反向由
$V_j(X_p)=p\otimes\Psi_j(\sigma_p)$ 直接使全部泄漏为零，包括 $\eta_p=0$ 的节点。$\square$

## 29. 同一来源的成功率识别与记忆效果方向

**定义 29.1（来源可见的实 Hermitian steering 空间）。** 沿用定义 28.1，在实 Hermitian 空间上定义

$$
\begin{aligned}
\mathcal S_\rho(A)&=\operatorname{Tr}_H[(A\otimes I_M)\rho],
\qquad A\in\operatorname{Herm}(H),\\
\mathcal W_\rho&=\mathcal S_\rho(\operatorname{Herm}(H))
\subseteq\operatorname{Herm}(M_0),\\
\mathcal W_\rho^\perp&=\{D\in\operatorname{Herm}(M_0):
 \operatorname{Tr}(DZ)=0\ (Z\in\mathcal W_\rho)\}.
\end{aligned}
\tag{29.1}
$$

内积为实 Hilbert–Schmidt 配对。$\mathcal S_\rho(p)=\sigma_p$；这里的 steering 指这一固定来源的算子关系，不附加任何新准备权限。

**定理 29.2（原细率的精确识别商与端点）。** 在定理 28.3 的前件下，对每个原 $j\in\mathsf C$，准备与该支的未条件化联合概率为

$$
q_{js}=\operatorname{Tr}V_j(X_{p_s})
=\operatorname{Tr}(G_j\sigma_{p_s}).
\tag{29.2}
$$

这些率精确决定 $G_j$ 在 $\mathcal W_\rho$ 上的实正交投影：两个候选效果 $G,G'$ 给同一全部设计率，当且仅当 $G-G'\in\mathcal W_\rho^\perp$。特别地，对任意指定实数 $t_j$，

$$
\boxed{\quad q_{js}=t_j\eta_{p_s}\ (s\in S)
\quad\Longleftrightarrow\quad
G_j-t_jI_0\in\mathcal W_\rho^\perp.\quad}
\tag{29.3}
$$

节点已经满足

$$
\operatorname{span}_{\mathbb R}\{\sigma_{p_s}:s\in S\}
=\mathcal W_\rho.
\tag{29.4}
$$

所以在同一来源上增加任意其他秩一标签，包括采用更高阶设计，不能扩大这个可见空间。若 $\mathcal W_\rho=\operatorname{Herm}(M_0)$，(29.3) 迫使 $G_j=t_jI_0$；否则内部值的标量率一般不迫使标量效果。对任意来源，若 (29.3) 成立，则 $t_j\in[0,1]$，且端点仍有

$$
t_j=0\Longrightarrow G_j=0,\ \Psi_j=0;\qquad
t_j=1\Longrightarrow G_j=I_0,\ \Psi_j\text{ 在输入域上保迹}.
\tag{29.5}
$$

对于原粗事件 $C\subseteq\mathsf C$，粗率 (29.3) 只约束 $G_C=\sum_{j\in C}G_j$，不能逐支推出它。即使率已唯一识别全部效果，也不唯一识别 $\Psi_j$ 的返回记忆动力学。

**证明。** (28.6) 及迹对偶给 (29.2)。设计的二阶矩给任意 $A=A^{\dagger}$ 的成熟恒等式

$$
\sum_sw_s[\operatorname{Tr}(Ap_s)]^2
=\frac{\operatorname{Tr}(A^2)+(\operatorname{Tr}A)^2}{d(d+1)}.
\tag{29.6}
$$

这是 (28.4) 的二阶偏迹与 $\Pi_{\rm sym}^{(2)}=(I+\mathsf F)/2$ 的直接收缩，所用设计矩仍为假设 28.2 所引 Scott、Roy–Scott 的结果。若 $A$ 与全部 $p_s$ 正交，则右端为零，故 $A=0$；因此这些节点张成 $\operatorname{Herm}(H)$。应用同一个实线性映射 $\mathcal S_\rho$ 即得 (29.4)。迹配对的零空间给效果差的充要条件，取 $G'=t_jI_0$ 得 (29.3)。其他秩一 $p$ 仍在同一个 $\operatorname{Herm}(H)$ 中，其 $\sigma_p$ 必在 $\mathcal W_\rho$ 中。

一阶设计矩还给

$$
\sum_sw_s\sigma_{p_s}=\rho_M/d,
\qquad \sum_sw_s\eta_{p_s}=1/d.
\tag{29.7}
$$

于是 (29.3) 给 $t_j=\operatorname{Tr}(G_j\rho_M)$。由 $0\le G_j\le I_0$ 及 $\rho_M$ 在自身支撑上的忠实性，$0\le t_j\le1$。$t_j=0$ 时
$\rho_M^{1/2}G_j\rho_M^{1/2}\ge0$ 且迹为零，故 $G_j=0$；(28.16) 中每个 $B_{j\alpha}^{\dagger}B_{j\alpha}$ 为零，从而 $\Psi_j=0$。$t_j=1$ 时同样对 $I_0-G_j$ 使用此论证，得 $G_j=I_0$。这里只使用有限维支撑上的严格正性，不要求一个已知数值本征值下界。

若 $\mathcal W_\rho$ 为真子空间，取非零 $D\in\mathcal W_\rho^\perp$。对任意 $0<t<1$，选 $0<|\epsilon|<\min\{t,1-t\}/\|D\|_{\rm op}$，则

$$
0<G=tI_0+\epsilon D<I_0.
\tag{29.8}
$$

因 $\rho_M\in\mathcal W_\rho$ 且忠实，非零标量矩阵不在 $\mathcal W_\rho^\perp$，所以 $D$ 和 $G$ 均非标量。将
$B=\iota_0\sqrt G$、$B_f=\iota_0\sqrt{I_0-G}$
作为 $M_0\to M$ 的两个数学算子，给出域上的完整 CP 记忆仪器；若 $M_0\ne M$，在 $M_0^\perp$ 上另取恒等失败 Kraus 算子、成功算子取零，就得到完整 $M$ 上的一份仪器。张量 $\operatorname{id}_H$ 后，它满足零泄漏及同一全部标量率，却有非标量成功效果。这是一个反模型的完整仪器定义，不是更改已给原装置的失败动作。命题 30.2 给带相关来源及原历史差别的具体实例。

满 steering 的一个充分来源是

$$
|v\rangle=\sum_{k=1}^r\sqrt{\lambda_k}|e_k\rangle\otimes|m_k\rangle,
\qquad \lambda_k>0,\quad M_0=\operatorname{span}\{m_k\}.
\tag{29.9}
$$

在这些基中 $\mathcal S_{|v\rangle\langle v|}(A)=D A_r^{\mathsf T}D$，$D=\operatorname{diag}(\sqrt{\lambda_k})$，$A_r$ 为 Schmidt 子空间的压缩。任意 Hermitian $r\times r$ 矩阵均可取作 $A_r$，且 $D$ 可逆，所以像为全部 $\operatorname{Herm}(M_0)$。纯满 Schmidt 来源的可识别性与 [D'Ariano–Lo Presti，arXiv:quant-ph/0211133v1，文中的纯态及混态 faithful 条件](https://arxiv.org/pdf/quant-ph/0211133v1) 相接；此处只消费线性像的判据，不把其单边通道层析结论等同于定理 28.3 的原联合支结论。

纯性并非必要。取 $H=M=\mathbb C^d$，$d\ge2$，以及固定真正混合来源

$$
\rho_c=c|\Phi_d\rangle\langle\Phi_d|+(1-c)I_{H\otimes M}/d^2,
\quad |\Phi_d\rangle=d^{-1/2}\sum_i|i,i\rangle,
\quad 0<c<1.
\tag{29.10}
$$

此时 $\mathcal S_{\rho_c}(A)=cA^{\mathsf T}/d+(1-c)(\operatorname{Tr}A)I_M/d^2$；在标量与无迹 Hermitian 子空间上分别可逆，故仍满 steering。相比之下，乘积来源 $\omega_H\otimes\tau_M$ 的可见像仅为 $\mathbb R\tau_M$，而定理 28.3 对它仍成立。

粗率的结论由将 (29.2) 在原标签上求和得到；这种粗／细区别沿用本卷命题 26.1 及 [C119 定理 152.2](AURIC_COMPOSITE_COMPARISON_REFERENCE_FREE_FILTER_RELATIONS_V96_CONTINUATION.md#152-原记录准备与有限校准的对应) 的原记录边界，不将粗 CP 支的某个 Kraus 表示当作原细菜单。

最后，即使给定 $G=tI_0$，记忆映射也可为 $\Psi=t\Theta$，其中 $\Theta$ 是任意从 $M_0$ 到 $M$ 的 CPTP 映射；补以另一个效果 $(1-t)I_0$ 的失败支就得域上的完整仪器。不同的 $\Theta$ 给相同全部成功率而可给不同返回记忆。故率识别的是效果，而非整个 CP 映射。$\square$

## 30. 设计阶数和不可见效果的完整原仪器反模型

**命题 30.1（正权二阶设计不能普遍代替三阶合同）。** 存在固定真正混合来源、忠实记忆边缘及完整双记录 CP 原仪器，使正权二阶设计上的全部所选未条件化泄漏为零，但所选原联合支在整个来源记忆支撑上不等于 $\operatorname{id}_H\otimes\Psi$。所有准备概率严格正，原失败支完整保留。

**证明。** 取 $H=Q=F=\mathbb C^2$、$M=Q\otimes F$，标签选择前的同一来源为

$$
\rho=|\Phi_2\rangle\langle\Phi_2|_{HQ}\otimes\tau_F,
\qquad \tau_F=I_F/2.
\tag{30.1}
$$

它秩二，$\rho_M=I_M/4$，所以 $M_0=M$。取四个单位向量

$$
z_1=|0\rangle,\qquad
z_{k+2}=3^{-1/2}|0\rangle+\sqrt{2/3}\,e^{2\pi i k/3}|1\rangle
\quad(k=0,1,2),
\qquad p_s=|z_s\rangle\langle z_s|,
\quad w_s=1/4.
\tag{30.2}
$$

这些 Bloch 向量 $r_s$ 满足 $\sum_sr_s=0$、$\sum_sr_sr_s^{\mathsf T}=(4/3)I_3$；代入 $p_s=(I+r_s\cdot\sigma)/2$ 得
$\frac14\sum_sp_s^{\otimes2}=\Pi_{\rm sym}^{(2)}/3$，故确为正权二阶设计。这个四面体设计本身是 Scott 所引成熟设计例子，不作为新构造。

在 $H\otimes Q$ 中置

$$
\nu=|00\rangle-\tfrac12|11\rangle,\qquad
K=\tfrac12|00\rangle\langle\nu|,\qquad
K^{\dagger}K=\tfrac14|\nu\rangle\langle\nu|,
\quad \|K\|_{\rm op}^2=5/16,
\qquad L=\sqrt{I_{H\otimes Q}-K^{\dagger}K}.
\tag{30.3}
$$

原标签恰为成功 $s$、失败 $f$，一次性固定

$$
V_s=\operatorname{Ad}_{K}\otimes\operatorname{id}_F,
\qquad V_f=\operatorname{Ad}_{L}\otimes\operatorname{id}_F.
\tag{30.4}
$$

$K^{\dagger}K+L^{\dagger}L=I$，故这是一份完整原仪器，$V_f$ 就是该反模型的实际失败动作，不是仅指定一个失败效果。

对任意纯 $p=|z\rangle\langle z|$，同一原局部准备给

$$
X_p=\tfrac12|z,\overline z\rangle\langle z,\overline z|_{HQ}\otimes\tau_F,
\qquad \eta_p=1/2.
\tag{30.5}
$$

由 $\langle\nu|z_s,\overline z_s\rangle=|z_{s,0}|^2-\tfrac12|z_{s,1}|^2$，四个值依次为 $1,0,0,0$。因此 $V_s(X_{p_1})=\frac18|00\rangle\langle00|\otimes\tau_F$，其系统在 $p_1$；其余三个节点的原成功支为零。四个未条件化泄漏均为零，但没有将零成功节点删去。各节点准备失败率为 $1/2$，准备后原仪器失败率为 $\eta_{p_s}-\operatorname{Tr}V_s(X_{p_s})$，故 $s=1$ 时为 $3/8$，其余为 $1/2$。

在另一个输入方向 $p=|1\rangle\langle1|$，$K|11\rangle=-|00\rangle/4$，所以

$$
V_s(X_p)=\tfrac1{32}|00\rangle\langle00|\otimes\tau_F,
\qquad
\operatorname{Tr}[((I_H-p)\otimes I_M)V_s(X_p)]=1/32>0.
\tag{30.6}
$$

若 $V_s=\operatorname{id}_H\otimes\Psi$，它对这个 $p\otimes\sigma_p$ 的输出仍应在系统方向 $p$，与 (30.6) 矛盾。故二阶合同在该一般类中不足。这个单一完整反模型不主张每个特定来源都需要三阶、不判任意非设计节点集的最小基数，也不给四阶必要性；定理 28.3 已给三阶充分。$\square$

**命题 30.2（真 steering 子空间隐藏非标量细效果及原历史差别）。** 存在同一固定相关来源及同一完整原仪器，使任意阶设计乃至全部秩一标签上的零泄漏与标量细成功率同时成立，但细效果非标量、下一次原记录率仍有记忆，并且联合因子化不推出所有相关输入上的标量系统边缘作用。

**证明。** 取 $H=M=\mathbb C^2$，在标签选择前固定

$$
\rho=\tfrac12(|00\rangle\langle00|+|11\rangle\langle11|),
\qquad M_0=M,\quad \rho_M=I_M/2,
\quad X=|0\rangle\langle1|+|1\rangle\langle0|.
\tag{30.7}
$$

对 $z=(z_0,z_1)$，原准备满足

$$
\sigma_p=\tfrac12\operatorname{diag}(|z_0|^2,|z_1|^2),
\quad \eta_p=1/2,
\quad \mathcal W_\rho=\operatorname{span}_{\mathbb R}\{I_M,Z\},
\quad X\in\mathcal W_\rho^\perp.
\tag{30.8}
$$

固定 $0<a<1$、$0<b<1$，原细记录为 $+, -, f$，前两个成功，$f$ 为失败。一次性固定记忆算子及原联合支

$$
\begin{aligned}
B_\pm&=\sqrt{a/2}\sqrt{I_M\pm bX},
& G_\pm&=\tfrac a2(I_M\pm bX),\\
B_f&=\sqrt{1-a}\,I_M,
& G_f&=(1-a)I_M,\\
V_j(Y)&=(I_H\otimes B_j)Y(I_H\otimes B_j^{\dagger})
&& (j\in\{+,-,f\}).
\end{aligned}
\tag{30.9}
$$

$G_++G_-+G_f=I_M$，所以所有成功与失败动作已给出且总和保迹；重复调用始终使用这一份仪器。每支精确因子化，故每个 $p$ 的所选泄漏均为零，而

$$
q_{\pm,p}=\tfrac a2\eta_p=a/4,\qquad
q_{f,p}=(1-a)\eta_p=(1-a)/2.
\tag{30.10}
$$

非标量 $G_\pm$ 的偏差 $\pm abX/2$ 完全不可见。用相同来源和准备，把 $b$ 取零所得的另一份完整仪器具有相同全部单次率；它只是用于比较的另一模型，每份模型内部的原装置均不切换。

现取该反模型中已合法的两次直接原调用，中间不复位、不再准备。以同一个原 $X_p=p\otimes\sigma_p$ 为未归一化起点；全部算子都是 $X$ 的函数，相互对易，且 $\operatorname{Tr}(X\sigma_p)=0$。故九个原两次词的联合质量精确为

$$
\begin{aligned}
Q_{++,p}=Q_{--,p}&=\eta_p\frac{a^2}{4}(1+b^2),\\
Q_{+-,p}=Q_{-+,p}&=\eta_p\frac{a^2}{4}(1-b^2),\\
Q_{\pm f,p}=Q_{f\pm,p}&=\eta_p\frac{a(1-a)}2,\\
Q_{ff,p}&=\eta_p(1-a)^2.
\end{aligned}
\tag{30.11}
$$

例如 $Q_{++,p}=\operatorname{Tr}(G_+^2\sigma_p)$，由
$G_+^2=\frac{a^2}{4}((1+b^2)I_M+2bX)$ 得第一式，其余同理。九项之和为 $\eta_p$，再加原准备失败质量 $1-\eta_p$ 得一。所有双成功词总质量为 $a^2\eta_p>0$，相同标签与不同标签的分配却随 $b$ 改变。特别地，已发生原准备及一次 $+$ 后，第二次 $+$ 的实际条件概率为 $a(1+b^2)/2$，而单次率为 $a/2$。没有将准备因子、任何失败或实际正条件分母消掉。本卷命题 26.1 已给粗／细历史区别；这里另以固定相关来源的 $\mathcal W_\rho^\perp$ 明确给出对全部标签都不可见的方向，并把它接到同一原历史的不同率。

联合因子化的另一边界直接在其已认证输入域上可见。取数学输入 $\Omega=|\Phi_2\rangle\langle\Phi_2|$，则

$$
\operatorname{Tr}_M V_+(\Omega)=\tfrac12G_+^{\mathsf T}
=\tfrac a4(I_H+bX),\quad
\operatorname{Tr}V_+(\Omega)=a/2>0,
\quad
\frac{\operatorname{Tr}_M V_+(\Omega)}{a/2}=\tfrac12(I_H+bX).
\tag{30.12}
$$

这不同于输入系统边缘 $I_H/2$。它不宣称原菜单实际能从 (30.7) 准备 $\Omega$；它反驳的是对 (28.6) 的全部相关输入量词所作的无条件标量边缘解释。原校准输入 $p\otimes\sigma_p$ 仍按定理 28.3 保持方向 $p$。$\square$

## 31. 原来源、原权限和继续调用的适用域

**定义 31.1（原历史权重与支持内接续合同）。** 一段实际原历史 $h$ 的发生概率为 $p_h>0$。在这段历史上应用定义 28.1 的校准关系，要求其标签选择以前的实际条件联合态就是同一 $\rho$，原被调用仪器就是同一 $\{V_j\}$；不以一个新初始化、复位或替换端口实现这一身份。设实际标签概率为 $\pi_s>0$、$\sum_s\pi_s=1$，原局部准备、读回及接续均已经合法。由 (28.2)、(29.2)，原联合质量为

$$
\begin{aligned}
P(h,s,\mathrm{prep\ success},j)
 &=p_h\pi_s\operatorname{Tr}(G_j\sigma_{p_s})
 &&(j\in\mathsf C),\\
P(h,s,\mathrm{prep\ failure})
 &=p_h\pi_s(1-\eta_{p_s}),\\
P(h,s,\mathrm{prep\ success},k)
 &=p_h\pi_s\operatorname{Tr}V_k(X_{p_s})
 &&(k\in\mathsf J\setminus\mathsf C).
\end{aligned}
\tag{31.1}
$$

原准备的多个失败细记录仍按各自原映射分配第二行的总质量。第三行也保留各个原失败动作；只对它们求和时才可写为
$p_h\pi_s(\eta_{p_s}-\sum_{j\in\mathsf C}q_{js})$。
$w_s$ 与 $\pi_s$ 的角色不同；(28.5) 的数学求积不供应按 $w_s$ 实际抽样的权限，也不将 $\eta_s=0$ 的节点变成可条件化准备。这保持 [C119 定理 152.1](AURIC_COMPOSITE_COMPARISON_REFERENCE_FREE_FILTER_RELATIONS_V96_CONTINUATION.md#152-原记录准备与有限校准的对应) 的原准备／原标签边界；其 $\pi_s\propto w_s/\eta_s$ 配方只有在每个分母严格正且该抽样原本合法时才适用。

任意后续原调用消费 (28.6) 时，要求其当时实际输入（含活动控制寄存器及惰性参考）支撑于系统输入端与 $M_0$ 的张量积，或另有已经证明的扩展域。一个充分的支持合同是：每个实际继续的已选记忆支满足

$$
\Psi_j(\mathcal B(M_0))\subseteq\mathcal B(M_0),
\tag{31.2}
$$

且全部实际中间动作保持这个输入域；$M_0=M$ 时无需额外记忆支撑闭合。输出允许离开 $M_0$ 的 (28.6) 本身不保证 (31.2)，本卷命题 26.2 的原支持逃逸反例直接适用，不重新计作这里的新反例。

若还要将每个细支解释为对任意相关输入都具有固定细记录率 $t_j$、且保留全部外部边缘的作用，则须有 $G_j=t_jI_0$。具体地，对任意附加活动系统和参考 $A$ 及任意域内算子 $Y$，这个条件恰给

$$
\operatorname{Tr}_M[(\operatorname{id}_H\otimes\Psi_j\otimes\operatorname{id}_A)(Y)]
=t_j\operatorname{Tr}_{M_0}Y.
\tag{31.3}
$$

迹对偶用任意外部效果 $F$ 配对，两边分别为
$\operatorname{Tr}[(F\otimes G_j)Y]$ 与
$\operatorname{Tr}[(F\otimes t_jI_0)Y]$，故 (31.3) 成立；反之取外部态与任意记忆态的乘积即迫使 $G_j=t_jI_0$。在实际分支概率严格正时才将输出归一化；$t_j=0$ 的支没有归一条件输出。定理 29.2 的满 steering 率条件足以给标量效果，命题 30.2 说明真子空间上的同样率条件不足。只知道某个粗效果标量，也只能消费对应粗事件的式 (31.3)。

有限历史的组合直接使用 [Context Geometry §§11–12](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#11-带记忆量子过程的表示历史概率与可访问关系)、[量子历史 §72.1、§72.3](ContextualSpacetimeQuantum/072_098_HISTORY_AND_CAPACITY.md#72-仪器级历史误差参考系统与自适应读出) 及本卷推论 25.3 的共同类型、同控制器和完整记录原则：先逐个核对实际调用域与细支合同，再在已经合法的有限协议内复合。需要继续的原失败支必须另有自己的动作与域合同；所选成功支的零泄漏不认证失败之后的系统作用。只有全部被消费的原支都有相应合同，才能给完整原历史输出作对应比较。既有有限组合结论不因 (28.6) 自动成为无限未来固定装置的保证。

**定义 31.2（两条校准桥的不同前件）。** 定理 25.2 的乘积准备、已知忠实下界和效果独立性消费非零误差，给逐原记录的定量近似及保迹比较记忆。定理 28.3 消费固定相关来源的精确三阶零式，只给来源记忆支撑上的精确 $\operatorname{id}_H\otimes\mathrm{CP}$；保迹性或固定细记录率另按定理 29.2、式 (31.3) 判定。它不是定理 25.2 的噪声版本，也不由精确零式给近零稳定常数。

[相界卷引理 141.2](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md#1413-满秩附加态强制相干子系统运输) 的忠实附加态／秩一 Choi 机制作为已有精确因子化供应保留；这里的不同关系是 (28.11) 的同源三阶积分和 (28.13)–(28.15) 的共轭变量系数分离，它在不要求 steering 满像时控制原输入支撑的全部记忆列。设计矩、Kraus 表示、纯满 Schmidt 层析条件均按各自所引先例使用，不将这些中间工具单列为新增结果。

[C122 定理 5.6–5.8](AURIC_INTERNAL_BINARY_RECIPROCITY_AND_EXPLICIT_RECONNECTION_C122.md#thm-c122-finite-tomography) 的系统通道层析及实际恢复证书仍需其自己的同通道、确定性实现与误差前件，不从 (29.2) 的率读数得到全 $\Psi_j$。FIB [定理 143.2 与命题 144.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md#143-joint-density-on-the-same-exact-rank-two-common-partitions) 的同见证全 $64$ 坐标逼近不供应这里的精确零式；[C123 §§18–20](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md#18-保留原返回尺度的指定-lorentz-比较群) 的原返回尺度及指定 $H^0$ 分类也不供应新的准备、仪器或合法操作。各结果的来源、量词和操作域分别保留。

## 追加锚（本行以下为增补区）

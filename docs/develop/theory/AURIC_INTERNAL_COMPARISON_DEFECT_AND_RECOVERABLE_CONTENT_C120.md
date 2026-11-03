**AURIC 量子关系研究续篇**

# 内部比较余量与可恢复内容

**候选 C120：全部二元余量由同一内部记录实现**

**本轮的核心关系**

一个观察者先把两段过程接起来再读出，与先分别读出再接起来，通常得到不同的比较。要求这些差额不能逐对随意指定，而必须同时成为同一个内部空间中的 Gram 比较：

$$
\boxed{\quad
\Phi(x^*y)=\Phi(x)^*\Phi(y)+R_\Phi(x)^*R_\Phi(y).
\quad}
$$

这里 $R_\Phi$ 对全部标签使用同一个线性实现。它表示当前读口没有保持的比较方向；数学表示的存在不等于这个观察者已经有权读出它。

**三个承重结论**

在明确声明的有限复矩阵接口中，这条兼容性约束等价于完全正读出。两段读出的比较余量有精确、非负的合成法则。某个来源代数能否完整恢复，则恰好取决于它是否与流向另一内部记录端的全部分支比较相交换：

$$
\mathfrak A\text{ 可恢复}
\quad\Longleftrightarrow\quad
[a,E_i^*E_j]=0\quad(a\in\mathfrak A).
$$

对量子比特，只要同一个通道保住 $Z$ 与 $X$ 两组正交态的完全可区分性，就已保住全部量子内容；若输入输出维数相同，通道必须为酉共轭。第三个 $Y$ 方向由同一乘法结构闭合。

**本轮范围**

这是一份可检验的有限量子理论候选与自足证明稿。它把一批已有定理组织成内部关系的同一表述，并补充有限证书、反例与适用边界；它不宣称这些经典定理首次被发现，也不宣称仅从“一切内生于 $\Omega$”便唯一推出自然界。

 仓库快照：`ef908d0914b7d1907fa25f59f02fcfad5275f42d`。

 提交时间：2026 年 11 月 3 日 14:41:08 UTC；本轮于 14:51 UTC 起核验。

 已核读相关新增理论段落与源码；本文给出纸笔证明，未执行 Lean 编译。

2026 年 11 月 3 日

## 目录

- [1. 从最新进展确定这一轮的问题](#section-1)
- [2. 把一步操作写成二元比较的余量](#section-2)
- [3. 顺序过程：余量的链式分解与可达支撑](#section-3)
- [4. 另一端记下了什么，决定这一端还能恢复什么](#section-4)
- [5. 有限几对二元读数，怎样锁定可逆量子门](#section-5)
- [6. 余量的三维截面与可读闭环相位](#section-6)
- [7. 从同一候选得到通常的有限量子力学](#section-7)
- [8. 两个观察者、反馈与整体内部的边界](#section-8)
- [9. 本轮结论、反例与下一步可检验目标](#section-9)
- [10. 有限量子原子的实关系选择：前提与完整证明](#section-10)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 从最新进展确定这一轮的问题

<a id="sec-c120-scope"></a>

### 1.1 仓库新增了什么，尚未证明什么

本轮固定仓库 `dev` 的不可变快照为封面所列 SHA。相对 C119 使用的 `2c2975d15e6a`，与本题直接相关的新增项是 14:28:03 UTC 合并的 PR 26117：四路径完整记录恢复续篇第二卷第 41 节 [1](#ref-repo-firstloss)。它在原有 $\operatorname{Dens}_2\times U(4)$ 模型里，保留同一个实际反馈 $U$，构造改变效果相干项的连续路径，严格保持原始缺陷 $g$，同时降低混合度并增加原始距离。其后推出已知值保持前缀内部的全局极小效果必须为秩一，并分析混合效果接触首个边界的后果。

这是一项*特定恢复优化模型*内的推进。正文第 41.7 节明确保留首次边界 $\alpha,\beta$ 的精确值、一般是否重合及全部端点等号情形为未决问题；也明确提醒，不能用已经假定前缀成立之后所得的纯性结论，倒过来证明前缀的位置。本文保持这一逻辑方向，不把新的局部比较读成原问题已解。

另两条与本轮衔接的基础是：仓库 C117 已将共同来源、局部复位、完整记录与观察者门序列写成数学对象 [2](#ref-repo-c117)；闭环三向回读续篇在已经给定有限复矩阵对象的前提下处理过程方向，并明确对象选择仍有额外桥接义务 [3](#ref-repo-orientation)。C109 的两个矩阵模块则在其统一方差前提下给出中心化及有限参考放大的界 [4](#ref-repo-centering)、[5](#ref-repo-bound)。它们的假设、理论文本与 Lean 源码的覆盖范围需要分别保留。

因此本轮推进的问题是：**一个过程究竟丢失了哪些比较？连续过程如何接续这些余量？一个指定输出究竟还能完整恢复哪一部分来源内容？**这比直接追求一个全知的 $\Omega$ 坐标更适合有限观察者。

### 1.2 先锁定类型，再压缩公理

本稿把 $\Omega$ 用作包含准备、过程、记录及其关系的整体结构名称；$\omega$ 表示某个归一化正读出状态。它们均不默认等于某个固定 Hilbert 空间中的纯态向量。对一个有限窗口，状态向量、算符、程序地址与实际记录也是不同类型；“内容等于地址”需要一个给定编码及其保真关系，不能抹去这些类型差异。

本轮的候选采用如下定义接口。它们是明示的选择条件，不因改称“定义”就失去筛选模型的作用。

1. **有限对象接口。**局部可操作内容是有限维复矩阵代数及其有限直和。独立复合使用共同复中心的可交换、生成性嵌入，允许角落与内部记录。附录 [10](#sec-local-core) 给出一个从实球形二元锥、非平凡方向关系与结合闭包选择 $M_2(\mathbb C)$ 的自足条件定理；这些条件不会由任意正关系核自动出现。

2. **概率接口。**效果 $0\le F\le I$ 是合法二结果测试之一。概率对互斥细分可加且对 $I$ 取值 $1$；若要恢复整个有限量子理论，量词覆盖全部效果，而非某个稀疏门菜单。

3. **过程接口。**确定性的完整读出以含幺复线性映射 $\Phi:\mathcal B\to\mathcal A$ 表示，方向从后端问题回拉到前端。经典分支和失败记录也包含在完整过程内。条件化的单一成功分支不是含幺过程。

4. **内部实现接口。**候选要求下述所有二元余量具有同一个内部 Gram 实现；有限记录扩充属于理论允许的整体。数学上构造出的实现与恢复，只有在相应准备和门确实被供应时，才是某位观察者可执行的协议。

### 定义 1.1（单候选 C120：内部比较余量的共同实现）

对每个合法完整读出 $\Phi:\mathcal B\to\mathcal A\subseteq\mathcal B(H)$，定义

$$
D_\Phi(x,y)=\Phi(x^*y)-\Phi(x)^*\Phi(y).
$$

要求存在同一个 Hilbert 空间 $\mathcal D_\Phi$ 以及同一个复线性映射
$R_\Phi:\mathcal B\to\mathcal B(H,\mathcal D_\Phi)$，使

<a id="eq-c120-candidate"></a>

$$
\boxed{D_\Phi(x,y)=R_\Phi(x)^*R_\Phi(y)\quad\text{对全部 }x,y.}
\tag{1}
$$

同一合法过程在限制、拼接与保留内部记录时必须使用一致的线性、乘法及概率语义。等价地，对每个有限族 $x_i$ 与可独立选择的输入向量 $\psi_i$，

$$
\sum_{i,j}\langle \psi_i,D_\Phi(x_i,x_j)\psi_j\rangle\ge0.
$$

 这是一条作用于二元关系的*共同兼容条件*，而不是为每一对另造一个余量。跨不同输入向量的算符块正性至关重要；固定同一个输入态后看到的标量 Gram 正性较弱。

### 定理 1.2（候选的可实现性与条件完备性）

上述候选有非平凡模型：全部有限复量子系统、效果、通道及有限内部记录构成一类这样的模型。在给定对象和概率接口后，候选的过程条件恰好选出所有含幺完全正映射；其对偶恰好为所有完全正保迹通道。若理论供应全部这些对象与过程，就得到标准有限量子运动学与一般测量理论。某个具体有限门菜单只得到其实际生成的子理论。

**证明。**
下一节由式 [(1)](#eq-c120-candidate) 构造 Choi 正矩阵、Kraus 算子与等距扩充；反向用扩充的正交余部给出同一 $R_\Phi$。第 [7](#sec-c120-qm) 节从效果概率的细分可加性得到密度矩阵和 Born 规则，并证明复合及理想测量的相应接口。每个有限通道都拥有有限 Kraus 表示，故全部有限对象组成的*类*对这些扩充闭合；并非一个固定维数的窗口能够容纳任意记录维数。

### 1.3 反过来检查：删去约束会发生什么

如果允许逐对编造余量，不要求一个共同正核，某个联合比较可能得到负平方；下一节给出具体反例。如果只检查固定三个标签，更大的有限参考仍可能检出负值。如果不保留失败记录，选取成功分支并重新归一化会产生非线性状态更新，不能拿它违反完整通道的合成定理。如果去掉复数对象的选择条件，经典随机理论和其他正序理论仍可自洽，因此“内部存在余量”本身并不独占复量子力学。

候选将*过程公理*压缩为一个二元兼容关系；它没有把所有数学与物理输入化为零。其优点是每一个仍然承重的输入都能定位：对象选择、效果供应、可接续过程、实际参考与时间结构各自承担什么结论，都可以反向删除并检验。

**白话。**先把两个动作接起来看，再把两个动作分别读出来接起来看，少掉的那部分必须也能在整体里找到一个共同的比较位置。不能这个对解释成一种丢失、另一个对又解释成互相矛盾的丢失。把这条要求对全部可接续关系同时执行，就得到量子通道的完整正性；再问它究竟留下了哪一套可以找回的关系。

<a id="section-2"></a>

## 2. 把一步操作写成二元比较的余量

<a id="sec-c120-defect"></a>

本章在已经建立的有限复矩阵代数上工作。复线性、乘法、伴随和单位仍是前件；本章要改写的是*操作的相容条件*，不声称从一个实二次式重新推出这些全部结构。记 $M_d=M_d(\mathbb C)$。采用 Heisenberg 方向

$$
\Phi:M_d\longrightarrow M_m,
 \qquad \Phi(I_d)=I_m.
$$

其对偶把输入态从 $\mathbb C^m$ 送到输出态 $\mathbb C^d$，由
$\operatorname{Tr}(\Phi_*(\rho)x)=\operatorname{Tr}(\rho\Phi(x))$ 定义。以下起初只假定 $\Phi$ 复线性、保单位，不预设保星或完全正。

### 定义 2.1（内部比较余量）

<a id="def-c120-defect"></a>

对两个输出问题 $x,y\in M_d$，定义

$$
D_\Phi(x,y):=\Phi(x^*y)-\Phi(x)^*\Phi(y),
 \qquad D_\Phi(x):=D_\Phi(x,x).
$$

称余量*完全为正*，若任意有限列 $x_1,\ldots,x_n$ 满足

<a id="eq-c120-complete-defect"></a>

$$
[D_\Phi(x_i,x_j)]_{i,j=1}^n\geq0.
\tag{2}
$$

这等价于对任意输入向量 $u_1,\ldots,u_n\in\mathbb C^m$，有
$\sum_{i,j}\langle u_i,D_\Phi(x_i,x_j)u_j\rangle\geq0$。

第一项先在输出端形成比较，再把它拉回输入端；第二项先分别拉回两个问题，再形成比较。式~[(2)](#eq-c120-complete-defect) 要求*两种顺序之差*在共同扩展中仍为正。它约束算符块，而不只是某一个参考态下的平均数。

### 定理 2.2（二元余量、有限证书与完全正操作）

<a id="thm-c120-defect-cp"></a>

上述复线性保单位映射的下列条件等价：

1. $D_\Phi$ 完全为正；

2. 只取固定的 $d$ 个矩阵 $e_i=E_{1i}$，已有
    $[D_\Phi(e_i,e_j)]_{i,j=1}^d\geq0$；

3. $C_\Phi:=[\Phi(E_{ij})]_{i,j=1}^d\geq0$；

4. $\Phi$ 完全正，即任意 $n$ 的 $\operatorname{id}_{M_n}\otimes\Phi$ 保正；

5. 存在有限多个 $K_\alpha:\mathbb C^m\to\mathbb C^d$，使
    $\Phi(x)=\sum_\alpha K_\alpha^*xK_\alpha$，且
    $\sum_\alpha K_\alpha^*K_\alpha=I_m$。

这些条件同时推出 $\Phi(x^*)=\Phi(x)^*$。因此，维度已知时，固定一个 $d\times d$ 算符余量矩阵就是有限证书。

**证明。**
条件 1 显然推出 2。由 $e_i^*e_j=E_{ij}$，有

$$
C_\Phi=[D_\Phi(e_i,e_j)]+[\Phi(e_i)^*\Phi(e_j)]\geq0,
$$

其中第二项是算符 Gram 矩阵，故 $2\Rightarrow3$。
若条件 3 成立，作有限秩分解

$$
C_\Phi=\sum_\alpha w_\alpha w_\alpha^*,
 \qquad w_\alpha=\sum_{i=1}^d\lvert i\rangle\otimes w_{\alpha i}.
$$

定义 $K_\alpha^*\lvert i\rangle=w_{\alpha i}$，则逐块比较给出
$\Phi(E_{ij})=\sum_\alpha K_\alpha^*E_{ij}K_\alpha$。
由复线性得到条件 5 的第一式，由保单位得到第二式。
每个放大的映射
$X\mapsto(I_n\otimes K_\alpha)^*X(I_n\otimes K_\alpha)$ 保正，故 $5\Rightarrow4$。
反之，对正矩阵
$[E_{ij}]=\lvert \Omega\rangle\langle \Omega\rvert$，其中
$\lvert \Omega\rangle=\sum_i\lvert i\rangle\otimes\lvert i\rangle$，施加第 $d$ 级放大即得 $4\Rightarrow3$。

最后令内部记录空间 $E$ 具有正交基 $\lvert \alpha\rangle$，定义

<a id="eq-c120-isometry"></a>

$$
Vu:=\sum_\alpha K_\alpha u\otimes\lvert \alpha\rangle,
 \qquad V^*V=I_m,
 \qquad \Phi(x)=V^*(x\otimes I_E)V.
\tag{3}
$$

设 $P=VV^*$，并定义余量向量算符

<a id="eq-c120-z-def"></a>

$$
Z_\Phi(x):=(I-P)(x\otimes I_E)V.
\tag{4}
$$

直接相乘得

<a id="eq-c120-z-gram"></a>

$$
D_\Phi(x,y)=Z_\Phi(x)^*Z_\Phi(y).
\tag{5}
$$

所以条件 5 推出 1。保星可由 Kraus 式直接读出；也可在条件 1 中取列 $(x,I)$：
$D_\Phi(I,I)=D_\Phi(I,x)=0$，正块矩阵迫使另一个非对角块
$D_\Phi(x,I)=\Phi(x^*)-\Phi(x)^*$ 也为零。

上述构造给出了有限维 Choi–Kraus 表示和 Stinespring 扩张的直接证明；这些结构的经典来源见文献~ [8](#ref-choi1974)、[9](#ref-choi1975)、[7](#ref-stinespring1955)。
这里 $E$ 是整体 $\Omega$ 内的记录载体。它的数学存在不等于给定实验装置已经具有全部控制资源。把全部有限余量规定为正，*与规定完全正具有相同数学内容*；这是一种二元关系表述，不是删除了这一实质条件。

### 说明 2.3（一般有限直和的版本）

<a id="rem-c120-finite-direct-sum"></a>

若定义域和值域分别为有限直和 $\mathcal B=\bigoplus_\alpha M_{d_\alpha}$、$\mathcal A=\bigoplus_\beta M_{m_\beta}$，完全余量正性仍等价于 UCP。
正块矩阵 $Y\in M_n(\mathcal B)$ 仍可写成 $R^*R$，下一段式~[(6)](#eq-c120-hierarchy) 的逐行 Gram 分解因而仍证明 $D_n\Rightarrow n$ 正；反向对 $(x_1,\ldots,x_n,I)$ 的块 Gram 应用完全正性，再对单位块取 Schur 补即可。
有限证书可在每个定义域中心块内分别取 $e_{\alpha i}=E^{(\alpha)}_{1i}$。对应余量块为正便使各 Choi 块为正；对每个值域分量分别分解，得到

$$
\Phi(b)_\beta
 =\sum_{\alpha,\ell}K_{\alpha\beta\ell}^*b_\alpha K_{\alpha\beta\ell},
 \qquad
 \sum_{\alpha,\ell}K_{\alpha\beta\ell}^*K_{\alpha\beta\ell}=I_{m_\beta}.
$$

把 $b_\alpha$ 放入直和表示 $\pi(b)$，便有 $\Phi(b)=V^*\pi(b)V$、$V^*V=I$；余量仍为 $((I-VV^*)\pi(x)V)^*((I-VV^*)\pi(y)V)$。后文为使可达支撑与维数直观，继续采用满矩阵空间记号。

**白话。**一个问题搬到输入端以后，还能不能与另一个问题保持原来的比较？把两种计算顺序相减，就得到余量。所有余量能够放进同一个正的比较表，等价于这一步可以在更大的内部记录空间里实现为保内积过程。记录仍在整体里面；我们只是暂时不读取它。

### 2.1 为何只检查三个问题仍可能漏掉矛盾

把“任意 $n$ 个问题的余量矩阵均正”记作 $D_n$ 条件。其与 $k$ 正性有如下关系：

<a id="eq-c120-hierarchy"></a>

$$
(n+1)\text{ 正}\ \Longrightarrow\ D_n
 \ \Longrightarrow\ n\text{ 正}.
\tag{6}
$$

第一箭头来自对 $(x_1,\ldots,x_n,I)$ 的正 Gram 矩阵施加 $(n+1)$ 级放大，再对右下角 $I$ 取 Schur 补。第二箭头也可直接证明：任意正块矩阵写成 $Y=R^*R$，则

$$
[\Phi(Y_{ij})]
 =\sum_k\bigl([D_\Phi(R_{ki},R_{kj})]
       +[\Phi(R_{ki})^*\Phi(R_{kj})]\bigr)\geq0.
$$

因此不能把 $D_n$ 与 $n$ 正性简单等同。在 $M_d$ 输入上，$D_d$ 已足够；定理~[2.2](#thm-c120-defect-cp) 甚至只需其中一个指定元组。输入维度不限时，则没有固定的三元上限。

### 例 2.4（每个固定输入下的标量 Gram 正仍不够）

<a id="ex-c120-scalar-not-block"></a>

在 $M_2$ 上取 $\Theta(A)=\tfrac34\operatorname{Tr}(A)I-\tfrac12A$。写
$A=\alpha I+T$、$\operatorname{Tr}(T)=0$，利用二阶矩阵恒等式
$T^*T+TT^*=\operatorname{Tr}(T^*T)I$，得

$$
D_\Theta(A)=\tfrac34\bigl(\operatorname{Tr}(T^*T)I-T^*T\bigr)
             =\tfrac34TT^*\geq0.
$$

因而每个固定 $u$ 的标量核
$\langle u,D_\Theta(x,y)u\rangle$ 都是正核：任意标量线性组合仍是
$\langle u,D_\Theta(\sum_i c_i x_i)u\rangle\geq0$。
可是其 Choi 矩阵为
$C_\Theta=\tfrac34I_4-\lvert \Omega_2\rangle\langle \Omega_2\rvert$，其中 $\Omega_2$ 归一化；它在 $\Omega_2$ 方向的特征值为 $-\tfrac14$。
所以该映射不满足 $D_2$ 条件。遗漏的是*各项可带不同输入向量*的共同块比较，不是某个固定输入下的标量 Cauchy–Schwarz 不等式。

### 例 2.5（所有三元检查通过，第四元出现负余量）

<a id="ex-c120-three-not-enough"></a>

在 $M_5$ 上取

$$
\Psi(X)=\frac{4\operatorname{Tr}(X)I_5-X}{19}.
$$

它保单位且为 $4$ 正。为证明后者，对任意 Schmidt 秩 $r\leq4$ 的向量 $v$，令
$\rho_A=\operatorname{Tr}_B\lvert v\rangle\langle v\rvert$。在其支撑上，
$\| (\rho_A^{-1/2}\otimes I)v\|^2=r$，故 Cauchy–Schwarz 不等式给出

$$
\lvert v\rangle\langle v\rvert\leq r\rho_A\otimes I
 \leq4\rho_A\otimes I.
$$

所以 $\operatorname{id}_{M_4}\otimes\Psi$ 保持每个秩一正矩阵为正，再由求和保持全部正矩阵。相反，对归一化的五维最大纠缠向量 $\Omega_5$，有

$$
\langle \Omega_5\rvert(\operatorname{id}_{M_5}\otimes\Psi)
 (\lvert \Omega_5\rangle\langle \Omega_5\rvert)\lvert \Omega_5\rangle
 =-\frac1{95}<0.
$$

因此该映射不是完全正，但由~[(6)](#eq-c120-hierarchy)，每个三元余量矩阵都正。

失败也能直接在余量中看到。以 $0,1,\ldots,4$ 编号，取
$x_i=E_{0i}$、$u_i=\lvert i\rangle$，$1\leq i\leq4$。逐项计算得

$$
D_\Psi(x_i,x_j)=\frac4{19}\delta_{ij}I_5
                    -\frac{20}{361}E_{ij},
 \qquad
 \sum_{i,j=1}^4\langle u_i,D_\Psi(x_i,x_j)u_j\rangle
 =\frac{16}{19}-\frac{320}{361}
 =-\frac{16}{361}.
$$

故 $D_4$ 已失败。三元几何能够显示一项必要关系，却不能替代任意更大内部记录上的相容条件。

**白话。**三个方向彼此看起来都能拼好，并不保证第四个方向还能接进来。维度知道以后，检查可以有限结束；维度还允许继续增长，就必须让同一条规则跟着扩展。这里漏掉的不是文字定义，而是一项明确算出来小于零的平方长度。

### 2.2 余量为零保持什么

### 定义 2.6（乘法域）

<a id="def-c120-md"></a>

对上述完全正保单位映射，定义

$$
\MD(\Phi):=\{x:D_\Phi(x)=0,\ D_\Phi(x^*)=0\}.
$$

### 命题 2.7（二元零余量的代数闭包）

<a id="prop-c120-md"></a>

对任意 $x$，下列条件等价：$x\in\MD(\Phi)$；
$[x\otimes I_E,VV^*]=0$；以及对所有 $y$，

$$
\Phi(xy)=\Phi(x)\Phi(y),\qquad
 \Phi(yx)=\Phi(y)\Phi(x).
$$

因此 $\MD(\Phi)$ 是保单位 $*$ 子代数，也是 $\Phi$ 保持乘法的最大此类子代数。自伴 $x$ 只需检查 $D_\Phi(x)=0$。

**证明。**
由~[(5)](#eq-c120-z-gram)，两个零余量等价于
$(I-P)(x\otimes I)P=(I-P)(x^*\otimes I)P=0$，即 $P$ 约化 $x\otimes I$。把 $P$ 插入两次压缩之间，即得两个乘法等式；反向取 $y=x^*$ 即得两个零余量。与固定投影交换的算符组成 $*$ 代数，故其原像亦然。任何保持乘法的 $*$ 子代数均满足两个平方等式，因而包含在该域中。

这里的“保持比较”尚不等于单射恢复：$\Phi|_{\MD(\Phi)}$ 可以具有非零核。恢复全部指定内容还须有忠实性、单射性或另行给定恢复映射。后文推论~[4.3](#cor-c120-md-recovery-image) 将精确证明：最大可恢复的*来源*代数是这个*输出*乘法域的像 $\Phi(\MD(\Phi))$。两个酉门也都可以具有零余量，即使它们与某个预期目标门不同；$D_\Phi$ 不是任意控制误差的统一度量，更不是脱离问题 $x,y$ 的抽象“信息总量”。

**白话。**两个平方都没有留下余量，意味着这个问题不仅自己保持长度，还能与所有其他问题按原来的顺序相乘。这样保住的问题自动组成一门小代数。但如果一个方向从来进不了当前接口，它也可能被整体压成零；要谈恢复，必须把可到达的范围说清楚。

<a id="section-3"></a>

## 3. 顺序过程：余量的链式分解与可达支撑

<a id="sec-c120-sequential"></a>

以下各系统与记录空间均为有限维。固定两个 Heisenberg 映射

$$
\Phi:B(H_B)\to B(H_A),\qquad
 \Psi:B(H_C)\to B(H_B).
$$

二者均满足上一章的比较条件。物理时间顺序是
$A\xrightarrow{\Phi_*}B\xrightarrow{\Psi_*}C$；末端问题则依次由 $\Psi$、$\Phi$ 拉回。

### 定理 3.1（精确的余量链法则）

<a id="thm-c120-chain"></a>

对任意末端问题 $x,y\in B(H_C)$，有

<a id="eq-c120-chain"></a>

$$
\boxed{D_{\Phi\circ\Psi}(x,y)
 =\Phi\bigl(D_\Psi(x,y)\bigr)
      +D_\Phi\bigl(\Psi(x),\Psi(y)\bigr).}
\tag{7}
$$

当 $y=x$ 时，右侧两项均正，因此总余量为零当且仅当这两项分别为零。

**证明。**
在 $\Phi(\Psi(x^*y))-\Phi(\Psi(x))^*\Phi(\Psi(y))$ 中加减
$\Phi(\Psi(x)^*\Psi(y))$ 即得恒等式。对角项的正性分别来自 $\Phi$ 保正和上一章的余量正性。两个正矩阵之和为零，逐输入向量取期望即知两者分别为零。

### 3.1 同一内部空间中的正交分解与三维提升

取内部记录等距实现

$$
V:H_A\to H_B\otimes E,\qquad
 W:H_B\to H_C\otimes F,
 \qquad T=(W\otimes I_E)V.
$$

于是 $T$ 实现 $\Phi\circ\Psi$。写 $L=W\otimes I_E$，并按上一章定义各 $Z$。

### 命题 3.2（两步余量沿正交方向出现）

<a id="prop-c120-orthogonal"></a>

有精确分解

<a id="eq-c120-two-leaks"></a>

$$
Z_{\Phi\circ\Psi}(x)
 =\underbrace{(Z_\Psi(x)\otimes I_E)V}_{Q_2(x)}
  +\underbrace{LZ_\Phi(\Psi(x))}_{Q_1(x)},
 \qquad Q_2(x)^*Q_1(y)=0
\tag{8}
$$

对任意 $x,y$ 成立。两项分别位于 $\operatorname{Ran}(L)^\perp$ 和 $\operatorname{Ran}(L)$。

**证明。**
由于 $T=LV$ 且 $L^*L=I$，

$$
I-TT^*=(I-LL^*)+L(I-VV^*)L^*.
$$

将其作用于 $(x\otimes I_{F\otimes E})LV$，并用
$L^*(x\otimes I)L=\Psi(x)\otimes I_E$，即得~[(8)](#eq-c120-two-leaks)。两个投影的像正交，故交叉内积为零。分别相乘得到
$Q_2(x)^*Q_2(y)=\Phi(D_\Psi(x,y))$ 和
$Q_1(x)^*Q_1(y)=D_\Phi(\Psi(x),\Psi(y))$，再次证明链法则。

这一分解给出准确的三维图像。固定一个单位输入向量 $u$ 和末端测试 $x$，令

$$
q_0=T(\Phi\circ\Psi)(x)u,\qquad
 q_1=Q_1(x)u,\qquad q_2=Q_2(x)u.
$$

三者两两正交，且

<a id="eq-c120-3d-lift"></a>

$$
(x\otimes I)Tu=q_0+q_1+q_2,
 \qquad
 \langle u,(\Phi\circ\Psi)(x^*x)u\rangle
 =\|q_0\|^2+\|q_1\|^2+\|q_2\|^2.
\tag{9}
$$

取非零 $q_j$ 的单位方向作为坐标轴，就是至多三维的实 Gram 提升。若 $x^*x=I$，三个长度组成的坐标
$(\|q_0\|,\|q_1\|,\|q_2\|)$ 落在单位球面的第一卦限；其中一项为零时退化到圆弧。它是*固定输入与固定测试的比较图*，不声称整个物理 Hilbert 空间只有三维。

```latex
\begin{tikzpicture}[scale=1.0,>=Stealth]
\coordinate (O) at (0,0);
\coordinate (A) at (2.7,0);
\coordinate (B) at (-1,-1.25);
\coordinate (C) at (0,2.15);
\coordinate (AB) at (1.7,-1.25);
\coordinate (AC) at (2.7,2.15);
\coordinate (BC) at (-1,.9);
\coordinate (S) at (1.7,.9);
\draw[->,gray!65] (O)--(3.8,0) node[right] {$q_0$ 方向};
\draw[->,gray!65] (O)--(-1.5,-1.9) node[below] {$q_1$ 方向};
\draw[->,gray!65] (O)--(0,2.85) node[above] {$q_2$ 方向};
\draw[very thick,teal!75!black,->] (O)--(A) node[midway,below] {保留};
\draw[very thick,blue!60!black,->] (O)--(B) node[midway,left] {第一步};
\draw[very thick,orange!80!black,->] (O)--(C) node[midway,left] {第二步};
\draw[dashed,gray!70] (A)--(AB)--(B) (A)--(AC)--(C) (B)--(BC)--(C);
\draw[dashed,gray!70] (AB)--(S)--(AC) (BC)--(S);
\draw[very thick,->] (O)--(S) node[above right] {$q_0+q_1+q_2$};
\fill (O) circle(1.5pt);
\node[align=left,anchor=west] at (4,.9) {$\|q_0+q_1+q_2\|^2$\\[3pt] $\quad=\|q_0\|^2+\|q_1\|^2+\|q_2\|^2$};
\end{tikzpicture}
```

**图 1。**同一输入与测试的三正交分量，画为平面投影。三个方向是完整过程中的保留及余量方向；它们不指定整个系统的维数。

这里的三维提升把顺序产生的两项余量放到严格正交的方向上。原二次式 $a^2+xab+b^2$ 在参数平面中的圆、椭圆及秩退化，另在第 [6](#sec-c120-geometry-phase) 节精确比较。

**白话。**一次比较没有保住的部分，不必被说成凭空消失。把完整记录留下来，就能把同一个测试向量分成三段：已经保留的部分、第一步的余量、第二步的余量。三段互相垂直，所以平方长度相加，无法用一段的负号抵消另一段。这个结论只谈比较余量；酉门之间的控制误差仍然可以相互纠正。

### 3.2 任意有限步的同一条关系

### 定理 3.3（多步链法则及正交来源）

<a id="thm-c120-multistep"></a>

设 $\Phi_j:B(H_j)\to B(H_{j-1})$，$1\leq j\leq N$，均完全正且保单位。记
$\Phi_{a:b}=\Phi_a\circ\cdots\circ\Phi_b$，空合成为恒等映射，
$x_j=\Phi_{j+1:N}(x)$、$y_j=\Phi_{j+1:N}(y)$。则

<a id="eq-c120-n-chain"></a>

$$
D_{\Phi_{1:N}}(x,y)
 =\sum_{j=1}^N\Phi_{1:j-1}
     \bigl(D_{\Phi_j}(x_j,y_j)\bigr).
\tag{10}
$$

在保留全部记录的同一等距实现中，右侧是来自 $N$ 个两两正交方向的 Gram 和。

**证明。**
恒等式由定理~[3.1](#thm-c120-chain) 归纳得到。为明确正交性，取
$V_j:H_{j-1}\to H_j\otimes E_j$，令
$R_0=\mathbb C$、$R_j=E_j\otimes\cdots\otimes E_1$，
$T_0=I$、$T_j=(V_j\otimes I_{R_{j-1}})T_{j-1}$。
把第 $j$ 时刻的全部系统与旧记录继续等距送到末端，记此尾部等距映射为
$S_j:H_j\otimes R_j\to H_N\otimes R_N$。于是
$S_N=I$、$S_0=T_N$，且
$S_{j-1}=S_j(V_j\otimes I_{R_{j-1}})$。

投影 $P_j=S_jS_j^*$ 满足
$P_0\leq P_1\leq\cdots\leq P_N=I$，故 $P_j-P_{j-1}$ 两两正交。定义

$$
Q_j(x):=(P_j-P_{j-1})(x\otimes I_{R_N})T_N
 =S_j\bigl(Z_{\Phi_j}(x_j)\otimes I_{R_{j-1}}\bigr)T_{j-1}.
$$

第二式由尾部压缩
$S_j^*(x\otimes I)S_j=x_j\otimes I_{R_j}$ 得到。因此
$Z_{\Phi_{1:N}}(x)=\sum_jQ_j(x)$，
$Q_i(x)^*Q_j(y)=0$（$i\ne j$），且
$Q_j(x)^*Q_j(y)=\Phi_{1:j-1}(D_{\Phi_j}(x_j,y_j))$，证毕。

**白话。**一串门再长，也不需要为每一级换一条公理。前面留下的记录继续保留，每加入一级，就多出一个与旧来源分开的余量方向。这里比较的是同一个末端问题逐级拉回后的结果，不能把各步不同的问题混为一谈。

### 3.3 总过程无余量，只约束实际能到达的支撑

### 引理 3.4（可达支撑与正算符的消失）

<a id="lem-c120-reachable"></a>

令 $\tau_A=I_A/\dim H_A$、$\sigma_B=\Phi_*(\tau_A)$，并令
$P_\Phi=\operatorname{supp}\sigma_B$。这是包含全部输出态 $\Phi_*(\rho)$ 支撑的最小投影。对任意 $b\geq0$，

<a id="eq-c120-support-zero"></a>

$$
\Phi(b)=0
 \quad\Longleftrightarrow\quad bP_\Phi=0
 \quad\Longleftrightarrow\quad b^{1/2}P_\Phi=0.
\tag{11}
$$

**证明。**
任意态满足 $\rho\leq(\dim H_A)\tau_A$，故
$\Phi_*(\rho)\leq(\dim H_A)\sigma_B$；而 $\sigma_B$ 本身就是一个输出，故支撑最小。
由 $\Phi(b)\geq0$ 及 $\tau_A$ 忠实，
$\Phi(b)=0\Longleftrightarrow\operatorname{Tr}(\tau_A\Phi(b))=0$。
对偶性把右侧改写为 $\operatorname{Tr}(\sigma_Bb)=0$。
在 $P_\Phi$ 上 $\sigma_B$ 严格正，因此此式等价于
$b^{1/2}P_\Phi=0$，亦等价于 $bP_\Phi=0$。

### 定理 3.5（乘法域复合的可达支撑判据）

<a id="thm-c120-support-md"></a>

对两步过程有

<a id="eq-c120-support-md"></a>

$$
\boxed{
 x\in\MD(\Phi\circ\Psi)
 \ \Longleftrightarrow\
 \begin{cases}
 \Psi(x)\in\MD(\Phi),\\
 D_\Psi(x)P_\Phi=0,\\
 D_\Psi(x^*)P_\Phi=0.
 \end{cases}}
\tag{12}
$$

若 $\Phi$ 在正元素上忠实，即 $b\geq0$ 且 $\Phi(b)=0$ 蕴含 $b=0$，则 $P_\Phi=I_B$，从而

<a id="eq-c120-faithful-md"></a>

$$
\MD(\Phi\circ\Psi)
 =\MD(\Psi)\cap\Psi^{-1}(\MD(\Phi)).
\tag{13}
$$

**证明。**
分别对 $x$ 与 $x^*$ 使用链法则。各正项必须为零：第一步的两项等价于
$\Psi(x)\in\MD(\Phi)$；第二步的两项由引理~[3.4](#lem-c120-reachable) 等价于所列支撑条件。逆向将这些零项代回即可。该引理同时说明正忠实性等价于 $P_\Phi=I_B$，因而给出最后一式。

多步版本不必强加每一步全局忠实。取 $\tau_0=I_{H_0}/\dim H_0$，令
$\sigma_{j-1}=(\Phi_{1:j-1})_*(\tau_0)$、$\Pi_{j-1}=\operatorname{supp}\sigma_{j-1}$；
这里 $\Pi_{j-1}$ 位于实际系统 $H_{j-1}$，区别于上述共同扩张空间中的嵌套投影 $P_j$。则

$$
x\in\MD(\Phi_{1:N})
 \Longleftrightarrow
 D_{\Phi_j}(x_j)\Pi_{j-1}
 =D_{\Phi_j}(x_j^*)\Pi_{j-1}=0
 \quad(1\leq j\leq N).
$$

这是~[(10)](#eq-c120-n-chain) 与引理~[3.4](#lem-c120-reachable) 的直接应用。

### 例 3.6（二维编码完全保真，第三个方向仍有余量）

<a id="ex-c120-unreachable-level"></a>

令 $V:\mathbb C^2\hookrightarrow\mathbb C^3$ 嵌入前两个坐标，定义

$$
\Phi:M_3\to M_2,\quad\Phi(b)=V^*bV,
 \qquad
 \Psi:M_2\to M_3,\quad\Psi(x)=x\oplus\tau_2(x),
 \quad\tau_2(x)=\operatorname{Tr}(x)/2.
$$

两映射均完全正保单位，且 $\Phi\circ\Psi=\operatorname{id}_{M_2}$。然而

$$
D_\Psi(x)=0_2\oplus
       \bigl(\tau_2(x^*x)-|\tau_2(x)|^2\bigr).
$$

取 $x=\operatorname{diag}(1,-1)$，余量为 $\operatorname{diag}(0,0,1)$，并不为零；取
$P_\Phi=\operatorname{diag}(1,1,0)$ 后却有 $D_\Psi(x)P_\Phi=0$。
事实上 $\MD(\Psi)=\mathbb C I_2$，因为
$\tau_2(x^*x)-|\tau_2(x)|^2=\tau_2((x-\tau_2(x)I)^*(x-\tau_2(x)I))$，忠实迹使其为零当且仅当 $x$ 为标量；但总过程的乘法域是整个 $M_2$。

物理时间顺序是先把量子比特编码到三维空间的前两维，再解码；解码器从未用到的第三维会产生混合输出。这没有损害代码内的恢复。另有
$\MD(\Phi)=M_2\oplus\mathbb C$，其中第三维投影被 $\Phi$ 压成零，亦展示乘法域本身不保证单射。

**白话。**全过程能恢复，不代表每一扇门在整个大空间里都没有余量。真正要求的是：余量不能落在实际会走到的方向上。三维例子里，信息始终在前两维走完，第三维即使有噪声也不参与这次过程。删去“可到达”这个限制，就会把正确的量子纠错误说成不可能。

### 3.4 有限精度与方差：可以量化到什么程度

### 命题 3.7（小总余量控制可达部分）

<a id="prop-c120-quantitative"></a>

若 $0\leq D_{\Phi\circ\Psi}(x)\leq\varepsilon I_A$，则

<a id="eq-c120-quant-a"></a>

$$
\begin{aligned}
0&\leq D_\Phi(\Psi(x))\leq\varepsilon I_A,
 &\operatorname{Tr}(\sigma_BD_\Psi(x))&\leq\varepsilon,
\end{aligned}
\tag{14}
$$

<a id="eq-c120-quant-b"></a>

$$
\begin{aligned}
\|D_\Psi(x)^{1/2}P_\Phi\|^2
 &=\|P_\Phi D_\Psi(x)P_\Phi\|
 \leq\frac{\varepsilon}{\lambda},&&
\end{aligned}
\tag{15}
$$

其中 $\lambda>0$ 是 $\sigma_B$ 在其支撑上的最小特征值。

**证明。**
链法则的两个正项各不超过总和。对
$\Phi(D_\Psi(x))\leq\varepsilon I_A$ 取 $\tau_A$ 平均，得~[(14)](#eq-c120-quant-a)。又
$\sigma_B\geq\lambda P_\Phi$，故
$\lambda\operatorname{Tr}(P_\Phi D_\Psi(x)P_\Phi)\leq\varepsilon$。
正矩阵的算符范数不超过其迹，给出~[(15)](#eq-c120-quant-b)。

该界只控制可达支撑上的作用。若要同时近似保持两个乘法方向，还须对 $x^*$ 给出同类界；仅凭这些估计，不能直接宣称整个映射已接近某个精确同态。很小的 $\lambda$ 也说明：极少进入的方向需要更精确的校准。式中的算符上界是对所有输入的控制，不能由一次样本的接近直接推出。

对自伴问题 $x$，余量还满足一个精确的方差分解。若
$\sigma=\Phi_*(\rho)$，定义
$\operatorname{Var}_\rho(a)=\operatorname{Tr}(\rho a^2)-(\operatorname{Tr}(\rho a))^2$，则

<a id="eq-c120-variance"></a>

$$
\operatorname{Var}_\sigma(x)
 =\operatorname{Var}_\rho(\Phi(x))+\operatorname{Tr}(\rho D_\Phi(x)).
\tag{16}
$$

证明只需展开两侧并使用对偶性。多步时对逐级拉回的 $x_j$ 求和，即得初始拉回问题的方差加上每一步的非负余量平均。这个结论并不说任意选择的同名观测量沿时间都具有单调方差。

以上均针对保留全部结果的线性、保单位操作。成功分支除以成功概率后的条件态更新通常非线性，不能直接套用这些公式；应先在整体内加入成功或失败记录，再分析完整操作。

**白话。**如果总余量只是很小，我们能给每一步真正可到达的余量一个明确上界；访问得越少的方向，上界越弱。方差也有同样的分账方式，但账目始终对应一个指定问题及其逐步拉回，不能被改写成没有对象的“宇宙信息增加或减少”。

<a id="section-4"></a>

## 4. 另一端记下了什么，决定这一端还能恢复什么

<a id="sec-c120-recoverable-content"></a>

本节只使用前文由统一比较余量条件得到的 UCP 读出及其有限内部等距实现，不再添加一条恢复公理。所证明的交换子判据属于已有的算符代数量子纠错理论；这里给出完整的有限构造，并明确它与比较余量零集合的关系。 [10](#ref-beny2007)

### 4.1 恢复的对象与完整内部过程

固定有限维非零空间 $\mathcal H,\mathcal K,\mathcal E$，以及

$$
V:\mathcal H\longrightarrow\mathcal K\otimes\mathcal E,
\qquad V^*V=I.
$$

按内部记录空间 $\mathcal E$ 的正交基展开，

<a id="eq-c120-record-kraus"></a>

$$
V=\sum_{i=1}^{m}E_i\otimes\lvert i\rangle,\qquad
E_i:\mathcal H\to\mathcal K,\qquad
\sum_iE_i^*E_i=I.
\tag{17}
$$

可见输出通道及其对偶为

$$
\mathcal N(\rho)=\operatorname{Tr}_{\mathcal E}(V\rho V^*)
=\sum_iE_i\rho E_i^*,
\qquad
\Phi(X)=\mathcal N^*(X)=\sum_iE_i^*XE_i.
$$

另一内部读口为补通道
$\mathcal N^c(\rho)=\operatorname{Tr}_{\mathcal K}(V\rho V^*)$。两个读口来自同一个 $V$，不是任取两个观察者模型后宣称它们互补。

### 定义 4.1（可恢复的来源代数）

<a id="def-c120-recovery"></a>

令 $\mathfrak A\subseteq\mathcal B(\mathcal H)$ 为含同一单位的有限维 $C^*$ 子代数。称它可从 $\mathcal K$ 输出完整恢复，如果存在 UCP 映射

$$
r:\mathfrak A\longrightarrow\mathcal B(\mathcal K),
\qquad
\Phi(r(a))=a\quad(a\in\mathfrak A).
$$

不预设 $r$ 保持乘法。等式必须在整个来源空间上成立，等价于对全部来源态正确恢复 $\mathfrak A$ 中每个效果的概率。

来源表示已经固定且忠实。若只保护物理空间中的码空间 $P\mathcal H_{\rm phys}$，就把它作为这里的 $\mathcal H$；此时下面的误差乘积须压缩为
$PE_i^*E_jP$，单位为 $P$。不能把码空间外的未知部分混入恢复量词。另一方面，本定义不要求选择任何满秩参考态，也不由单个参考下的期望相等代替算符等式。

### 4.2 恢复当且仅当内部记录比较与来源操作交换

### 定理 4.2（可恢复代数的二元记录判据）

<a id="thm-c120-recovery-commutant"></a>

在上述条件下，

<a id="eq-c120-recovery-commutant"></a>

$$
\mathfrak A\text{ 可恢复}
\quad\Longleftrightarrow\quad
[a,E_i^*E_j]=0
\quad(a\in\mathfrak A,\ i,j).
\tag{18}
$$

因此最大可恢复代数为

<a id="eq-c120-maximal-recovery"></a>

$$
\mathfrak A_{\rm rec}=\{E_i^*E_j:i,j\}'.
\tag{19}
$$

**证明。**
先证必要性。设恢复映射 $r$ 已存在。固定 $a\in\mathfrak A$，置 $X=r(a)$。对 $\Phi$ 与 $r$ 分别使用 Schwarz 不等式，得到

$$
a^*a=\Phi(X)^*\Phi(X)
\preceq\Phi(X^*X)
\preceq\Phi(r(a^*a))=a^*a.
$$

首尾相同，故比较余量为零。对当前内部等距，余量恰为

$$
\Phi(X^*X)-\Phi(X)^*\Phi(X)=Z_X^*Z_X,
\qquad
Z_X=(I-VV^*)(X\otimes I)V.
$$

所以 $Z_X=0$，从而
$(r(a)\otimes I)V=Va$。按记录基展开便有
$r(a)E_i=E_i a$。对 $a^*$ 作同样推导再取伴随，得到
$E_i^*r(a)=aE_i^*$。于是

$$
aE_i^*E_j=E_i^*r(a)E_j=E_i^*E_j a.
$$

这里使用的是二重 Schwarz 饱和，而不是预先假定 $r$ 是同态。

反向，假定所有交换关系成立。定义

$$
F:\mathcal H^{\oplus m}\to\mathcal K,\qquad
F(\psi_1,\ldots,\psi_m)=\sum_iE_i\psi_i,
\qquad
D=\operatorname{Ran} F.
$$

有限维保证 $D$ 闭合。记
$G=F^*F=[E_i^*E_j]_{ij}$、$\widetilde a=\operatorname{diag}(a,\ldots,a)$；
交换条件正好是 $[G,\widetilde a]=0$。在 $D$ 上定义

$$
r_0(a)F\xi=F\widetilde a\,\xi.
$$

因为 $G$ 与 $\widetilde a$ 交换，

$$
\|F\widetilde a\,\xi\|^2
=\|\widetilde aG^{1/2}\xi\|^2
\le\|a\|^2\|F\xi\|^2.
$$

所以 $F\xi=0$ 时右侧也为零，定义不依赖代表，且有界。
在生成 $D$ 的向量 $F\xi$ 上直接验证
$r_0(ab)=r_0(a)r_0(b)$、$r_0(I)=I_D$；又

$$
\langle F\xi,r_0(a)F\eta\rangle
=\langle \xi,G\widetilde a\eta\rangle
=\langle r_0(a^*)F\xi,F\eta\rangle,
$$

故 $r_0$ 是保单位 $*$-表示。

取 $\mathfrak A$ 上任意一个状态 $\tau$，定义

$$
r(a)=r_0(a)\oplus\tau(a)I_{D^\perp}
\quad\text{于 }\mathcal K=D\oplus D^\perp.
$$

这是 UCP 映射；若 $D=\mathcal K$，省去第二块。
由于 $r(a)E_i=E_i a$，

$$
\Phi(r(a))
=\sum_iE_i^*r(a)E_i
=\sum_iE_i^*E_i a=a.
$$

最后，式 [(19)](#eq-c120-maximal-recovery) 的右侧本身是含幺
$C^*$ 代数，故这个构造同时恢复整个最大代数。

支持外的 $\tau(a)I_{D^\perp}$ 保证 $r(I)=I_{\mathcal K}$，不能在需要归一化读出时遗漏。恢复还自动给出 $r$ 的忠实性：$r(a)=0$ 推出 $a=\Phi(r(a))=0$。

若需要一条输出为完整来源矩阵空间的 CPTP 恢复通道，可取有限迹条件期望
$\mathsf E_{\mathfrak A}:\mathcal B(\mathcal H)\to\mathfrak A$，令
$\mathcal R^*=r\circ\mathsf E_{\mathfrak A}$。这确实 UCP，且
$\mathcal N^*\mathcal R^*(a)=a$ 对全部 $a\in\mathfrak A$ 成立。
具体地，在分解
$\mathfrak A=\bigoplus_\alpha
(\mathcal B(\mathcal L_\alpha)\otimes I_{\mathcal G_\alpha})$ 下，
$\mathsf E_{\mathfrak A}$ 先删去扇区间块，再对每块的
$\mathcal G_\alpha$ 取归一化偏迹并张量回单位，因此完全正、保单位且固定 $\mathfrak A$。
这恢复的是所声明代数中的内容，不是自动恢复整个来源态；实际执行仍须供应对应操作。

### 4.3 余量零集合如何接到可恢复内容

### 推论 4.3（乘法域的来源像）

<a id="cor-c120-md-recovery-image"></a>

对于 $\Phi=\mathcal N^*$，

<a id="eq-c120-md-recovery-image"></a>

$$
\mathfrak A_{\rm rec}=\Phi\bigl(\MD(\Phi)\bigr).
\tag{20}
$$

其中

$$
\MD(\Phi)=
\{X:D_\Phi(X,X)=0,\ D_\Phi(X^*,X^*)=0\}.
$$

**证明。**
若 $X\in\MD(\Phi)$，两个零余量给出
$(X\otimes I)V=V\Phi(X)$ 及其伴随版本。
如前一证明，$a=\Phi(X)$ 因而与全部 $E_i^*E_j$ 交换。
反向，对每个 $a\in\mathfrak A_{\rm rec}$，恢复截面 $r$ 的二重
Schwarz 饱和保证 $r(a)\in\MD(\Phi)$，且 $\Phi(r(a))=a$。

这两者不能直接混称：$\MD(\Phi)$ 是*输出端*的无余量算符，
$\mathfrak A_{\rm rec}$ 是*来源端*能恢复的算符；中间必须经过
$\Phi$。恢复不要求原来的读出对所有算符都无噪声，只要求每个被保护的来源操作有一个正确的输出代表。

补读口满足

$$
(\mathcal N^c)^*(\lvert i\rangle\langle j\rvert)=E_i^*E_j.
$$

因此式 [(18)](#eq-c120-recovery-commutant) 也等价于

<a id="eq-c120-complement-commutant"></a>

$$
\operatorname{Ran}(\mathcal N^c)^*\subseteq\mathfrak A'.
\tag{21}
$$

被保护的操作，恰好与另一内部记录端所能拉回的全部比较相交换。
这一互补性是已知的可纠正与私有内容关系的有限代数形式。 [12](#ref-kretschmann2008)

### 4.4 满源量子内容：环境固定，输出只附加固定辅态

### 定理 4.4（完整量子恢复的结构）

<a id="thm-c120-full-recovery"></a>

对来源 $\mathcal H$，下列条件等价：

1. $\mathcal B(\mathcal H)$ 可恢复；

2. $E_i^*E_j=\alpha_{ij}I$，其中 $\alpha\succeq0$、$\operatorname{Tr}\alpha=1$；

3. 存在固定环境态 $\tau_{\mathcal E}$，使
   $\mathcal N^c(\rho)=\operatorname{Tr}(\rho)\tau_{\mathcal E}$；

4. 存在固定态 $\tau$ 及等距
   $W:\mathcal H\otimes\mathbb C^r\to\mathcal K$，使


   <a id="eq-c120-reversible-channel"></a>

   $$
   \mathcal N(\rho)=W(\rho\otimes\tau)W^*.
   \tag{22}
   $$

若 $\dim\mathcal H=\dim\mathcal K$，这些条件进一步等价于
$\mathcal N(\rho)=U\rho U^*$，其中 $U$ 酉。

**证明。**
满矩阵代数的交换子为 $\mathbb C I$，所以定理
[4.2](#thm-c120-recovery-commutant) 给出前两项等价。对单位向量 $u$，

$$
\sum_{ij}\bar z_i\alpha_{ij}z_j
=\left\|\sum_i z_iE_i u\right\|^2\ge0,
\qquad
\sum_i\alpha_{ii}=1.
$$

故 $\alpha$ 是正的归一化矩阵。另一方面，
$(\mathcal N^c)^*(B)$ 对每个 $B$ 都为标量，恰好意味着它等于
$\operatorname{Tr}(\tau_{\mathcal E}B)I$，即第三项；用记录矩阵单位也立即得到反向。

酉混合 Kraus 算子以对角化 $\alpha$，并删去零项，得到
$F_a^*F_b=p_a\delta_{ab}I$，其中 $p_a>0$、$\sum_ap_a=1$。
置 $W_a=F_a/\sqrt{p_a}$，则 $W_a^*W_b=\delta_{ab}I$。
因此

$$
W(\psi\otimes\lvert a\rangle)=W_a\psi,\qquad
\tau=\sum_ap_a\lvert a\rangle\langle a\rvert
$$

定义等距 $W$ 并给出式 [(22)](#eq-c120-reversible-channel)。
反向，取任意固定源态 $\rho_0$，则

$$
\mathcal R(X)=
\operatorname{Tr}_{\mathbb C^r}(W^*XW)
+\operatorname{Tr}[(I-WW^*)X]\,\rho_0
$$

完全正、保迹，且 $\mathcal R\mathcal N=\operatorname{id}$。
最后，若输入输出同维，等距 $W$ 强制 $r=1$；
此时 $W$ 为酉，得到结论。

第二项是满源版本的 Knill–Laflamme 条件。 [11](#ref-knill1997)
它也等价于一条二元振幅关系：

$$
\langle E_i u,E_jv\rangle=\alpha_{ij}\langle u,v\rangle
\quad(u,v\in\mathcal H).
$$

分支之间的比较只能分解成来源比较与固定记录比较的乘积。
输出维数较大时不能擅自删掉混合辅态 $\tau$：
$\rho\mapsto\rho\otimes\tau$ 完整可恢复，但在 $\tau$ 混合时不把纯态送到纯态。

满源情形还对任意输入–参考联合态给出

<a id="eq-c120-full-reference-decoupling"></a>

$$
(\operatorname{id}_R\otimes\mathcal N^c)(\rho_{R\mathcal H})
=\rho_R\otimes\tau_{\mathcal E}.
\tag{23}
$$

这由替换通道的线性形式直接推出，不需再假设输入与参考独立。

### 4.5 一般子代数允许中心与辅助部分留在记录中

在有限分解

$$
\mathcal H=\bigoplus_\alpha
(\mathcal L_\alpha\otimes\mathcal G_\alpha),\qquad
\mathfrak A=\bigoplus_\alpha
(\mathcal B(\mathcal L_\alpha)\otimes I_{\mathcal G_\alpha})
$$

下，其交换子为
$\mathfrak A'=\bigoplus_\alpha
(I_{\mathcal L_\alpha}\otimes\mathcal B(\mathcal G_\alpha))$。
所以一般恢复条件只要求补通道通过

$$
\rho\longmapsto
\bigoplus_\alpha
\operatorname{Tr}_{\mathcal L_\alpha}(P_\alpha\rho P_\alpha)
$$

因子化：每个环境效果的拉回都在上述交换子内，而这个交换子与辅助直和代数保单位 $*$ 同构，故得到该因子化的 UCP 对偶。
记录可以依赖中心标签 $\alpha$ 和 $\mathcal G_\alpha$，但不直接依赖被保护的
$\mathcal L_\alpha$ 变量。

不能把这句话扩大成任意输入下的统计独立。逻辑部分原本可以与中心或辅助部分相关，环境读取后者时仍会保留这种相关。只有满源情形才无条件得到式
[(23)](#eq-c120-full-reference-decoupling)。这一区别也使经典共同标签与受保护的非交换量子内容能够同时存在。

### 例 4.5（退相干、完全擦除与等距编码）

<a id="ex-c120-recovery-extremes"></a>

完全退相干取 $E_j=\lvert j\rangle\langle j\rvert$，故
$E_i^*E_j=\delta_{ij}\lvert i\rangle\langle i\rvert$；最大可恢复代数正好是该基中的对角代数。
若将这些投影换成高秩正交块，则每个块内的全部矩阵代数仍可恢复。

精确可恢复代数还可能不连续。令
$\mathcal N_p(\rho)=(1-p)\rho+pZ\rho Z$，$0\le p\le1/2$。
其两 Kraus 算子为 $\sqrt{1-p}\,I$、$\sqrt p\,Z$。
当 $p=0$ 时全部 $M_2(\mathbb C)$ 可恢复；任意 $p>0$ 时，非零交叉乘积
$\sqrt{p(1-p)}Z$ 已使最大可恢复代数降为对角代数。
虽然 $\langle +\rvert\mathcal N_p(\lvert +\rangle\langle +\rvert)\lvert +\rangle=1-p$ 可任意接近一，
它仍不是精确恢复的证书。

完全擦除取 $E_j=\lvert 0\rangle\langle j\rvert$，则
$\mathcal N(\rho)=\operatorname{Tr}(\rho)\lvert 0\rangle\langle 0\rvert$。
此时 $E_i^*E_j=\lvert i\rangle\langle j\rvert$ 生成全部来源矩阵代数，
所以只能恢复 $\mathbb C I$。

等距编码取单个 $E_1=U$、$U^*U=I$。误差乘积只有 $I$，
所以全部来源量子代数可恢复。

这些结论都相对于指定的来源、准备和输出划分。记录端仍在 $\Omega$ 内；局部忽略它是读口限制。判据不要求观察者看遍记录端，也不保证它已拥有检查全部交换关系的实际证书。

**白话。**一段内容能不能找回来，要看另一份记录记下了什么。若另一端只留下与来源无关的支路信息，来源的全部量子关系还能恢复；若它记住了来源在哪个方向，可恢复的内容就要与这份记录相容。共同标签可以留在两边。要保住一整套彼此不交换的量子关系，另一端就不能同时获得这套来源的独立信息。所有记录仍留在整体内，只是不同读口能取回的内容不同。

<a id="section-5"></a>

## 5. 有限几对二元读数，怎样锁定可逆量子门

<a id="sec-c120-binary-gate-certificate"></a>

上一节的恢复条件涉及全部来源操作。对一个已经满足本轮统一余量条件、因而具有 CPTP 表示的有限过程，可以进一步把完整可逆性的检查压成有限组正交纯态对。这是过程的证书，不是另加一条量子公理；复数结构、制备类型与 UCP 前件仍由前文承担。

### 5.1 输出不混淆，等价于全部分支交叉比较为零

### 引理 5.1（正交输出的分支展开）

<a id="lem-c120-output-orthogonality"></a>

设 $\mathcal N(\rho)=\sum_iE_i\rho E_i^*$。对单位向量 $u,v$，记
$P_u=\lvert u\rangle\langle u\rvert$。则

<a id="eq-c120-output-orthogonality"></a>

$$
\operatorname{Tr}\!\left[\mathcal N(P_u)\mathcal N(P_v)\right]
=\sum_{i,j}\left|\langle E_i u,E_jv\rangle\right|^2.
\tag{24}
$$

两输出态可被某个二元效果以概率一完全区分，当且仅当这个量为零。

**证明。**
展开两组秩一项并取迹即得等式。对正矩阵 $\rho,\sigma$，
$\operatorname{Tr}(\rho\sigma)=\|\rho^{1/2}\sigma^{1/2}\|_{\rm HS}^2$，
所以该值为零等价于两支撑正交，此时投影到 $\operatorname{supp}\rho$ 就能完全区分。
反向，若效果 $0\le F\le I$ 满足
$\operatorname{Tr}(\rho F)=1$、$\operatorname{Tr}(\sigma F)=0$，
则 $\rho$ 的支撑位于 $F$ 的本征值 $1$ 空间，
$\sigma$ 的支撑位于其核，故二者正交。

不同测试对可以使用不同的二元效果；并不要求存在一个同时区分所有被测非正交态的测量。条件也不是要求一次实测结果恰巧不同，而是要求已声明通道给出的两个输出支撑严格正交。

### 5.2 一个有限证书足以推出全部来源恢复

### 定理 5.2（基对与相干对的有限证书）

<a id="thm-c120-finite-binary-certificate"></a>

设 $d\ge2$，$\mathcal N:M_d(\mathbb C)\to M_k(\mathbb C)$ 为 CPTP 通道，
$e_1,\ldots,e_d$ 为已经校准的源正交基。只检查下列正交单位向量对：

$$
(e_r,e_s)\quad(1\le r<s\le d),
$$

$$
(u_j,v_j)
=\left(\frac{e_1+e_j}{\sqrt2},
       \frac{e_1-e_j}{\sqrt2}\right)
\quad(2\le j\le d).
$$

这些 $\binom d2+d-1$ 对的输出全部可完全区分，当且仅当整个来源
$M_d(\mathbb C)$ 可从输出恢复。因此通道必有

$$
\mathcal N(\rho)=W(\rho\otimes\tau)W^*
$$

的形式；若 $k=d$，它必为单位共轭。

**证明。**
对任意一对 Kraus 指标 $i,\ell$，记
$A_{i\ell}=E_i^*E_\ell$。第一组测试结合引理
[5.1](#lem-c120-output-orthogonality) 给出

$$
\langle e_r,A_{i\ell}e_s\rangle
=\langle E_i e_r,E_\ell e_s\rangle=0
\quad(r\ne s).
$$

反向次序也成立，因为两输出支撑的正交性是对称的。
所以每个 $A_{i\ell}$ 在这个基中对角，写为
$\operatorname{diag}(a_1,\ldots,a_d)$；此处对角元可为复数。

第二组测试给出

$$
0=\langle u_j,A_{i\ell}v_j\rangle
=\frac{a_1-a_j}{2}.
$$

于是所有对角元相同，故
$E_i^*E_\ell=\alpha_{i\ell}I$。
定理 [4.4](#thm-c120-full-recovery) 的构造立即给出完整恢复及所述结构。

反向，若 $\mathcal N(\rho)=W(\rho\otimes\tau)W^*$，
则对任意 $u\perp v$，

$$
\mathcal N(P_u)\mathcal N(P_v)
=W(P_uP_v\otimes\tau^2)W^*=0.
$$

所以全部正交纯态对都保持完全可区分性，当然包括所列有限证书。

正交保持与量子随机等距的结构联系是已有结果；Busch 的正交保持判据与结构定理给出了更一般的刻画。 [13](#ref-busch1999)
上面的有限清单直接用分支比较验证 Knill–Laflamme 标量条件，不需要先检验全部纯态或假定存在逆门。
它也不声称清单大小最优。

这里的“有限证书”指在已校准有限模型中核验这些精确关系。有限次有噪声采样本身不能证明概率严格为零，未知输出维数与未声明的门变化也不能被自动忽略。若只有误差界，需要另给定量稳定定理，不能把本节的精确结论直接套用。

### 5.3 单量子比特：两对读数怎样锁住第三个方向

当 $d=k=2$ 时，只需两对：

$$
\lvert 0\rangle,\lvert 1\rangle;\qquad
\lvert +\rangle=\frac{\lvert 0\rangle+\lvert 1\rangle}{\sqrt2},
\quad
\lvert -\rangle=\frac{\lvert 0\rangle-\lvert 1\rangle}{\sqrt2}.
$$

第一对是 $Z$ 的两极，第二对是 $X$ 的两极。
定理保证同一个通道已为 $\operatorname{Ad}_U$，而不是分别为两套读数拟合两条无关规则。

这个结论也可直接看见。第一对输出严格正交，在二维输出中必为
$\lvert f_0\rangle\langle f_0\rvert$、$\lvert f_1\rangle\langle f_1\rvert$。
每个 Kraus 分支因此形如

$$
E_i\lvert 0\rangle=a_i\lvert f_0\rangle,\qquad
E_i\lvert 1\rangle=b_i\lvert f_1\rangle,\qquad
\sum_i|a_i|^2=\sum_i|b_i|^2=1.
$$

令 $\gamma=\sum_i a_i\overline{b_i}$。在输出基 $f_0,f_1$ 中，

$$
\mathcal N(P_\pm)
=\frac12
\begin{pmatrix}1&\pm\gamma\\
\pm\overline\gamma&1\end{pmatrix},
\qquad
\operatorname{Tr}[\mathcal N(P_+)\mathcal N(P_-)]
=\frac{1-|\gamma|^2}{2}.
$$

第二对完全可区分，便强制 $|\gamma|=1$。
Cauchy–Schwarz 饱和使两组系数 $(a_i)$、$(b_i)$ 仅差一个固定相位；
因此每个 $E_i$ 都是同一个酉矩阵的标量倍数。
记录端不能留下区分两条来源分支的信息。

相位关系也随之确定。因为 $Y=iXZ$，同一个单位共轭必满足

<a id="eq-c120-zx-determine-y"></a>

$$
\mathcal N(Y)=i\,\mathcal N(X)\mathcal N(Z).
\tag{25}
$$

所以这两对二元证书锁住了第三方向的乘法关系。
若进一步校准 $\mathcal N(X)=X$、$\mathcal N(Z)=Z$，
就有 $\mathcal N(Y)=Y$，整个通道是恒等通道。
仅有完全可区分性时，输出坐标仍允许同一个整体酉旋转，不应宣称它已固定为原坐标。

### 例 5.3（只守一个基会丢掉相位）

<a id="ex-c120-one-basis-insufficient"></a>

退相干通道

$$
\Delta(\rho)=\tfrac12(\rho+Z\rho Z)
$$

完整保留 $\lvert 0\rangle,\lvert 1\rangle$ 的可区分性，却满足
$\Delta(P_+)=\Delta(P_-)=I/2$。
它保住一个经典基，不能通过第二对相干测试。

统一余量条件同样不可删。转置映射保持正性、迹及全部正交关系，
并固定 $X,Z$，却把 $Y$ 变成 $-Y$；
它不是完全正映射，不能作为本定理的通道。
例如它作用在 Bell 态的一端时，部分转置在反对称方向上的本征值为 $-1/2$。
因此式 [(25)](#eq-c120-zx-determine-y) 没有从两组实概率中无前提地产生复相位；
它使用了此前已经建立的同一复线性、完全正过程接口。

**白话。**先检查“零”和“一”经过门后还能不能分开，只能知道这个门没有混掉一个经典标签。再检查“相加”和“相减”还能不能分开，就把两条支路之间的相位也锁住了。对已经满足内部比较余量规则的单量子比特过程，这两对都保住，整个门就只能是同一次量子旋转；第三个方向不能再独自翻转或丢失。有限证书锁定的是同一个门的全部关系，不是用两份互不相干的读数表代替它。

<a id="section-6"></a>

## 6. 余量的三维截面与可读闭环相位

<a id="sec-c120-geometry-phase"></a>

本节是主候选的几何配套，不另加一套量子选择公理。它说明：固定输入后，内部比较余量怎样成为二元 Gram 球；若还要识别这些历史方向怎样接在一起，需要哪些实际可读的相位证据。射影等价与闭环不变量的数学框架已有标准结果 [15](#ref-chien2015)。

### 6.1 从余量核回到原来的二次式

设完全正含幺映射具有实现 $\Phi(X)=V^*\pi(X)V$、$V^*V=I$，定义

$$
R_X=(I-VV^*)\pi(X)V,\qquad
 D_\Phi(X,Y)=\Phi(X^*Y)-\Phi(X)^*\Phi(Y).
$$

直接相乘得到 $D_\Phi(X,Y)=R_X^*R_Y$。固定单位输入 $\psi$，令
$r_X=R_X\psi$，便得到标量余量核

<a id="eq-c120-residual-scalar-kernel"></a>

$$
k_\psi(X,Y)=\langle \psi,D_\Phi(X,Y)\psi\rangle=\langle r_X,r_Y\rangle.
\tag{26}
$$

若 $d_X=k_\psi(X,X)$、$d_Y=k_\psi(Y,Y)$、$z=k_\psi(X,Y)$，
且 $t=d_X+d_Y>0$，则

<a id="eq-c120-defect-bloch"></a>

$$
\frac1t\begin{pmatrix}d_X&z\\\bar z&d_Y\end{pmatrix}
 =\frac12(I+\boldsymbol s\cdot\boldsymbol\sigma),\qquad
 \boldsymbol s=\frac{(2\operatorname{Re}z,-2\operatorname{Im}z,d_X-d_Y)}{t},
 \quad\|\boldsymbol s\|\le1.
\tag{27}
$$

这是 $2\times2$ 正性给出的三维有限提升。它只比较固定输入下的两份余量；完整的算子块正性还要允许不同输入向量及内部参考，不能被这一标量截面替代。若 $d_X=0$，则 $r_X=0$，没有可归一化的相位方向。

回到两个*实系数* $a,b$。对单位比较向量 $u,v$，

<a id="eq-c120-original-quadratic"></a>

$$
\|au+bv\|^2=a^2+xab+b^2,
 \qquad x=2\operatorname{Re}\langle u,v\rangle\in[-2,2].
\tag{28}
$$

所以 $a^2+xab+b^2=1$ 在 $x=0$ 时是圆，$|x|<2$ 时一般为椭圆；
$x=2$ 时退化为 $(a+b)^2=1$，即两条平行直线。此时 $u=v$，二元 Gram 秩降为一。
$ab$ 在原变量上是双线性的；将数据提升为

$$
M(a,b)=\begin{pmatrix}a^2&ab\\ab&b^2\end{pmatrix},\qquad
 Q_x=\begin{pmatrix}1&x/2\\x/2&1\end{pmatrix},
$$

才有真正的线性读数 $a^2+xab+b^2=\operatorname{Tr}(Q_xM)$。$M$ 的三个实坐标同时受
$M\succeq0$、$\det M=0$ 约束。这正把“二元关系提升后可以线性读取”写成精确命题。
实系数的这个读数只含内积实部；虚部仍需要相位比较。

### 命题 6.1（三点回路读出有向体积）

<a id="prop-c120-bargmann-volume"></a>

若三个单位方向都位于同一二维复振幅空间，写
$P_j=(I+\boldsymbol n_j\cdot\boldsymbol\sigma)/2$，$\|\boldsymbol n_j\|=1$，则

<a id="eq-c120-triple-volume"></a>

$$
B_{123}:=\operatorname{Tr}(P_1P_2P_3)
 =\frac{1+\boldsymbol n_1\cdot\boldsymbol n_2+
 \boldsymbol n_2\cdot\boldsymbol n_3+\boldsymbol n_3\cdot\boldsymbol n_1
 +i\boldsymbol n_1\cdot(\boldsymbol n_2\times\boldsymbol n_3)}4.
\tag{29}
$$

**证明。**
使用 $(a\cdot\sigma)(b\cdot\sigma)=(a\cdot b)I+i(a\times b)\cdot\sigma$
及 $\operatorname{Tr} I=2$、$\operatorname{Tr}\sigma_j=0$，展开三个投影后取标量部分即可。

转移概率 $p_{ij}=\operatorname{Tr}(P_iP_j)=(1+\boldsymbol n_i\cdot\boldsymbol n_j)/2$
只给出点积；回路虚部还读出有向体积。例如方向 $z+,x+,y+$ 与
$z+,x+,y-$ 的两两概率均为 $1/2$，但 $B_{123}=(1\pm i)/4$。
这个符号相对于实际内部相位参考定义，不提供外部绝对取向。
式~[(29)](#eq-c120-triple-volume) 限于共同二维振幅空间；任意三个高维历史并不自动属于同一个 Bloch 球。

**白话。**原来的交叉项，确实能在提升后的关系坐标里变成线性读数；但 $x=2$ 表示两个方向合成同一条线，圆对应 $x=0$。再添第三个方向，概率给出彼此有多近，复闭环还给出绕行的取向。这些图形首先描述关系，不是在指定物理空间维数。

### 6.2 有锚时三点足够，无锚闭环可能留下自由

只考虑非零余量方向，或一般的单位历史方向 $u_0,\ldots,u_n$。约定内积第一变量共轭线性，并记

$$
g_{ij}=\langle u_i,u_j\rangle,\qquad p_{ij}=|g_{ij}|^2,\qquad
 B_{ijk}=g_{ij}g_{jk}g_{ki}.
$$

逐个改变代表向量的相位会改变 $g_{ij}$，却不改变 $p_{ij}$ 和 $B_{ijk}$。

### 定理 6.2（内部非正交锚的重构）

<a id="thm-c120-anchor-reconstruction"></a>

假设一个实际可用的锚方向 $u_0$ 满足 $p_{0i}>0$。若已知
$p_{0i}$ 及全部 $B_{0ij}$，则该射线族的 Gram 矩阵被确定到逐方向相位，
射线族在其张成空间中被确定到共同酉变换。具体地，在
$g_{0i}=\sqrt{p_{0i}}>0$ 的规范下，

<a id="eq-c120-anchor-formula"></a>

$$
g_{ij}=\frac{B_{0ij}}{\sqrt{p_{0i}p_{0j}}}.
\tag{30}
$$

若是从候选数据开始构造，还须检验所得矩阵的 Hermitian 性、单位对角及完整正性；该公式不把任意填入的三点数值变成合法态。

**证明。**
把每个 $u_i$ 乘以相位，使其与 $u_0$ 的内积为正实数；非零重叠保证可以这样做。
随后 $B_{0ij}=\sqrt{p_{0i}}g_{ij}\sqrt{p_{0j}}$，即得公式。
若两族向量有相同 Gram 矩阵，把相同线性组合送到另一族的相同组合，会保持范数及零关系，故给出它们张成空间间的酉同构。反向，任何正 Gram 矩阵可由其正平方根的列向量实现。

分母指出了可读性的边界：锚与某个方向正交时，此坐标失效；重叠很小时，测量误差会被放大。数学上可选择的锚，不等于装置已经供应了这样的参考。

一般支撑图以 $g_{ij}\ne0$ 为边。在每个连通分支选一棵生成树，可以逐顶点把树边相位设为零；每条非树边的相位则由它与树构成的基本闭环确定。因此，一组基本闭环足够恢复全部边相位。
三角回路足够的一个精确充分条件是：每个有向*整数循环*都能写成已知三角边界的整数和。此时将各边相位沿这些整数链相乘，内部边与反向边逐项抵消，便恢复任意闭环。
这里使用有向整数链的条件，不把任意一种模二循环生成说法直接替换为复相位结论。

### 例 6.3（全部三点相同，四点回路仍不同）

<a id="ex-c120-four-cycle"></a>

取 $0<r<1/2$，令

<a id="eq-c120-four-cycle-gram"></a>

$$
G_\varphi=\begin{pmatrix}
 1&r&0&r e^{-i\varphi}\\
 r&1&r&0\\
 0&r&1&r\\
 r e^{i\varphi}&0&r&1
 \end{pmatrix}.
\tag{31}
$$

由 $2|z_i z_j|\le|z_i|^2+|z_j|^2$，其二次型满足
$z^*G_\varphi z\ge(1-2r)\|z\|^2>0$，故每个 $\varphi$ 都有真实单位向量实现。
它们的全部两点概率相同；任意三个不同标签都包含一条零边，所以全部三点回路均为零。
但四点回路为 $g_{12}g_{23}g_{34}g_{41}=r^4e^{i\varphi}$，随 $\varphi$ 改变。
由于逐方向相位在闭环中抵消，这些射线族不能被同一组概率与三点数据识别为同一个对象。

**白话。**若每个方向都能与同一个内部锚比较，三点回路就能把整张有限关系图拼起来。若图中留着没有被三角形填上的环，仍可能藏着一个只绕完整圈才看见的相位。三点有时足够，有时不够，决定因素是已校验的比较网络。

### 6.3 闭环相位怎样成为实际记录

### 命题 6.4（受控循环读出）

<a id="prop-c120-readable-cycle"></a>

假设装置能独立重复准备三个单位方向，并供应已校准的控制比特、受控循环置换以及控制比特的相位读出。令

$$
W(x\otimes y\otimes z)=y\otimes z\otimes x,
 \qquad \Psi=u_1\otimes u_2\otimes u_3.
$$

控制比特从 $(\lvert 0\rangle+\lvert 1\rangle)/\sqrt2$ 出发，执行受控 $W$ 后，测量
$\lvert +_\theta\rangle=(\lvert 0\rangle+e^{i\theta}\lvert 1\rangle)/\sqrt2$，所得概率为

<a id="eq-c120-cycle-readout"></a>

$$
q_\theta=\frac{1+\operatorname{Re}(e^{-i\theta}B_{123})}{2}.
\tag{32}
$$

因此 $\operatorname{Re}B_{123}=2q_0-1$，
$\operatorname{Im}B_{123}=2q_{\pi/2}-1$。

**证明。**
张量内积直接给出 $\langle \Psi,W\Psi\rangle=g_{12}g_{23}g_{31}=B_{123}$。
投到 $\lvert +_\theta\rangle$ 后，未归一化振幅为
$(\Psi+e^{-i\theta}W\Psi)/2$；求其范数平方即得显示公式。

这是循环测试的一个直接形式 [16](#ref-oszmaniec2024)。所需的是可重复准备与相干控制接口，不是复制一个未知单次输入。若只顺序执行投影并统计成功，所得仅为若干转移概率的乘积，不会自动读出闭环虚部。抽象余量向量 $r_X$ 的存在，也不自动供应其制备、相干控制或环境读出。

历史细化同样有一个精确关系。对所有相邻重叠非零的闭路径，定义
$H=\prod g_{ij}/|g_{ij}|$。在边 $i\to j$ 中插入 $k$，且新增两条边也非零时，

$$
\frac{H_{\rm new}}{H_{\rm old}}
 =\frac{B_{ikj}}{|B_{ikj}|}.
$$

这由三个边因子直接相除得到；三点回路控制了一次细化怎样改变整体相位。
取连续历史极限仍须另给连续性与可读参考条件，有限正核本身没有提供时间参数。

最后须守住重构对象的类型。上述数据识别的是射线族，仍容许逐标签相位与共同酉变换；固定操作标签的复线性、乘法和合法续接关系必须另外核验。它也不识别整个过程 $\Phi$：例如不同酉共轭映射都满足 $D_\Phi=0$。
所以本节补充的是“怎样读出余量方向之间的关系”，完整可恢复内容仍由主候选的全输入比较余量与恢复条件决定。

**白话。**一个闭环相位可以被变成控制比特上的真实频率，但前提是相干参考和循环控制确实在内部可用。数学上的余量方向不会自动变成可操作的探针；认清方向之间的几何，也还没有认清产生这些方向的整个门序列。

<a id="section-7"></a>

## 7. 从同一候选得到通常的有限量子力学

<a id="sec-c120-qm"></a>

本节只使用已列出的对象、概率与过程接口。完全正性、Kraus 表示和内部等距过程已经由共同余量条件证明，无须在这里重新作为独立过程公理输入。对象选择及某个门是否实际可用，仍各有自己的前提。

### 7.1 状态也是一个读口：正关系、Hilbert 空间与 Born 规则

### 命题 7.1（从关系核构造振幅空间）

设历史标签集合 $S$ 带复核 $K$，满足所有有限矩阵 $[K(s_i,s_j)]\succeq0$。在有限形式和 $\sum c_s[s]$ 上定义

$$
\left\langle\sum c_s[s],\sum d_t[t]\right\rangle
 =\sum_{s,t}\overline{c_s}d_tK(s,t).
$$

商去零范数向量并完备化，得到 Hilbert 空间 $H_K$ 与向量 $v_s$，满足 $\langle v_s,v_t\rangle=K(s,t)$；以这些向量的闭线性包为全部空间时，该实现唯一到一个酉同构。

**证明。**
有限正性给出非负半内积。对 $u+t v$ 的范数平方使用判别式得到 Cauchy–Schwarz 不等式，所以零范数向量与全部向量正交，商内积良定义。若另一组 $w_s$ 有同一核，映射 $\sum c_sv_s\mapsto\sum c_sw_s$ 保持范数，因而良定义；稠密线性包上的等距延拓给出所述酉映射。

若历史来自有限 $*$-代数 $\mathcal A$，且 $K(a,b)=\omega(a^*b)$，则商空间还保留左作用 $\pi(a)[b]=[ab]$。在 $C^*$-对象中，$a^*a\le\|a\|^2I$ 保证此作用有界，单位向量 $\xi=[I]$ 满足 $\omega(a)=\langle \xi,\pi(a)\xi\rangle$。这就是有限 GNS 构造的具体形式。它重建某个状态的循环表示，不把 $\Omega$ 宣告为该单个向量，也不把满秩混合态的 $d^2$ 维 GNS 空间误当成 $M_d$ 的 $d$ 维不可约振幅空间。

### 定理 7.2（效果概率的 Born 表示）

在 $M_d(\mathbb C)$ 的所有效果上，若 $w(I)=1$、$w(F)\ge0$，且

$$
w(F+G)=w(F)+w(G)\qquad(F,G\ge0,\ F+G\le I),
$$

则存在唯一密度矩阵 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，使

$$
w(F)=\operatorname{Tr}(\rho F).
$$

反向每个密度矩阵给出这样的赋值。极端状态恰好是秩一投影，纯态间的射线测试概率为 $|\langle \phi,\psi\rangle|^2$。

**证明。**
细分可加性给 $w(F/n)=w(F)/n$，继而给有理尺度齐次性；正性给单调性。用有理数从两侧逼近 $t\in[0,1]$，即得 $w(tF)=t w(F)$，无须另假设连续。
对任意 $A\ge0$，取 $n$ 使 $A/n\le I$，定义 $f(A)=n w(A/n)$；齐次性保证不依赖 $n$。再定义 $f(A-B)=f(A)-f(B)$，利用正锥上的可加性验证其良定义，得到自伴部分上的实线性正泛函，再唯一复线性延拓。有限维迹配对给唯一 $\rho$；测试所有秩一投影保证 $\rho\ge0$，$f(I)=1$ 给迹归一化。
若 $\rho$ 至少有两个正本征值，可向两方向转移一个足够小权重，写成两不同状态的平均，故非极端。秩一态若是两正状态的平均，则其正交补在两态中均有零期望，强制两态都支撑于同一条射线，因而相同。

这是效果版 Gleason 论证的有限形式 [14](#ref-busch2003)。作为映射 $\omega:\mathcal A\to\mathbb C$，一个状态正是候选的标量终端读口；其比较余量为协方差核。复数域和全部效果的可加语义已经列入接口，不能称它们也由“归一化”独自推得。

### 7.2 观测、一般测量及状态更新

经典结果集合含 $m$ 个标签时，其代数为 $\mathbb C^m$。一个合法测量读口 $\Phi:\mathbb C^m\to M_d$ 由 $F_j=\Phi(e_j)$ 给出，满足

$$
F_j\succeq0,\qquad\sum_jF_j=I,\qquad
 p(j|\rho)=\operatorname{Tr}(\rho F_j).
$$

因此 POVM 是同一读口定义的交换输出特例。反向任意这样的效果族都给合法读口：若 $[c_{ij}]\in M_n(\mathbb C^m)$ 为正，则每个标签处的数值矩阵都正，故 $[\sum_j c_{ab}(j)F_j]$ 为正。

锐测量取彼此正交的投影 $P_j$，并给各结果一个实读数 $a_j$，便得到自伴算符 $A=\sum_j a_jP_j$，平均读数为 $\operatorname{Tr}(\rho A)$。反向，有限维自伴算符的谱分解给出这种锐测量。因此“可观测量由自伴算符表示”是效果与实读数的这一对应，而不是把每个一般测量都限制成投影测量。

若同时保留测量后的量子输出，则结果 $j$ 对应完全正分支

$$
\mathcal I_j(\rho)=\sum_rK_{jr}\rho K_{jr}^*,\qquad
 \sum_{j,r}K_{jr}^*K_{jr}=I.
$$

完整输出可以写成 $\bigoplus_j\mathcal I_j(\rho)$，它仍是一条通道。读到 $j$ 后的条件态为 $\mathcal I_j(\rho)/p_j$，前提是 $p_j>0$。这个归一化公式描述已取得记录后的条件化；它不声称选中分支本身仍是线性保迹过程。不同仪器可以给同一个 POVM，因而仅知道概率不能唯一决定扰动。

### 定理 7.3（理想锐读出为何给出 Lüders 更新）

设完全正分支 $\mathcal I$ 的效果是投影 $P$，即 $\operatorname{Tr}\mathcal I(\rho)=\operatorname{Tr}(P\rho)$。再要求对每个单位 $\psi\in\operatorname{Ran} P$，$\mathcal I(\lvert \psi\rangle\langle \psi\rvert)=\lvert \psi\rangle\langle \psi\rvert$。则

$$
\mathcal I(\rho)=P\rho P.
$$

**证明。**
写 $\mathcal I(\rho)=\sum_rK_r\rho K_r^*$。效果等式给 $\sum K_r^*K_r=P$，所以每个 $K_r$ 在 $\ker P$ 上为零。对 $\psi\in\operatorname{Ran} P$，一组正秩一项之和支撑于 $\mathbb C\psi$，迫使每个 $K_r\psi$ 均与 $\psi$ 共线。一个线性映射若保持子空间内每一条射线，就在该子空间上为标量：比较任意两个独立向量及其和即可。故 $K_r=c_rP$，且 $P\ne0$ 时 $\sum|c_r|^2=1$。代回即得结论；$P=0$ 时所有 $K_r=0$。

这里没有预设单 Kraus 算子。额外的理想性条件是“不改变该结果子空间内部的每条射线”；只要求结果可重复，还允许在子空间内作非平凡酉旋转，并不足以指定 Lüders 仪器。

### 7.3 复合系统、纠缠及可逆运动

### 命题 7.4（独立全矩阵部门的复合）

设 $M_d(\mathbb C)$、$M_m(\mathbb C)$ 以含幺复线性 $*$-嵌入进入同一个非零结合 $*$-代数；两个像彼此交换并生成该代数。则所生成代数为 $M_{dm}(\mathbb C)$。

**证明。**
映射 $a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 由交换性成为满射 $*$-同态。矩阵单位的张量乘积是 $M_{dm}$ 的矩阵单位，且 $M_{dm}$ 为单代数：任一非零双边理想中的非零矩阵元，通过左右矩阵单位可生成所有矩阵单位。因此该含幺非零同态的核为零。

“共同复中心、独立子代数、生成性”承担张量复合的输入。不是任意两个内部窗口都独立。由一个二元块反复独立复合得到 $M_{2^n}$，允许秩 $d$ 的角落即可得到任意 $M_d$。张量正态包含纠缠态；例如 Bell 态不能写成产品态的凸和，因为纯态若可凸分解，各分量必须沿同一射线，而该射线不是产品向量。

有限二元证书章节已经从候选的过程条件推得：一个同维过程若保住指定两类完全可区分关系，必须是酉共轭。完整振幅过程的等距性也由 Kraus 扩充直接得到，不另假设“波函数的每个分量必须线性演化”。

若进一步*供应一个*连续的完整酉群 $U(t+s)=U(t)U(s)$、$U(0)=I$，有限维下所有 $U(t)$ 交换且正规，可同时对角化。每个对角元是实加法群的连续单位模特征，故为 $e^{-i\omega_jt}$；由局部连续辐角和加法性可直接证明。于是存在自伴 $H$，

$$
U(t)=e^{-itH/\hbar},\qquad
 i\hbar\,\frac{d}{dt}\psi(t)=H\psi(t).
$$

时间参数、连续群的供应、具体 $H$ 与作用量单位 $\hbar$ 均没有由静态余量关系决定。静态内生关系与具体动力学选择不可互换。

### 7.4 两项直接可算的量子约束

### 命题 7.5（不确定关系来自二元正比较）

对自伴 $A,B$ 与任意状态 $\omega$，有

$$
\operatorname{Var}_\omega(A)\operatorname{Var}_\omega(B)
 \ge\left|\omega\bigl((A-\omega(A)I)(B-\omega(B)I)\bigr)\right|^2
 \ge\frac14|\omega([A,B])|^2.
$$

**证明。**
令 $X=A-\omega(A)I$、$Y=B-\omega(B)I$。状态的二元 Gram 矩阵
$\left(\begin{smallmatrix}\omega(X^2)&\omega(XY)\\\omega(YX)&\omega(Y^2)\end{smallmatrix}\right)$ 为正，行列式非负给出第一项。又 $\omega(YX)=\overline{\omega(XY)}$，所以 $2i\operatorname{Im}\omega(XY)=\omega([A,B])$，给出第二项。

### 命题 7.6（独立两端的 CHSH 约束）

若 $A_0,A_1$ 与 $B_0,B_1$ 分别为两独立量子部门的自伴反射，即平方均为 $I$，则

$$
S=A_0\otimes(B_0+B_1)+A_1\otimes(B_0-B_1)
 \quad\text{满足}\quad \|S\|\le2\sqrt2.
$$

该界在两个量子比特中可以达到。

**证明。**
直接展开得 $S^2=4I-[A_0,A_1]\otimes[B_0,B_1]$；每个交换子范数至多为 $2$，故 $\|S^2\|\le8$。取 $A_0=Z,A_1=X$、$B_0=(Z+X)/\sqrt2,B_1=(Z-X)/\sqrt2$，并在 Bell 态 $(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$ 上求期望，得到 $2\sqrt2$。若四个结果预先取定为局部数值 $\pm1$，同一表达式绝对值只能为 $2$；对这样的赋值作概率混合仍不超过 $2$。

这些是候选重构出的通常量子理论的约束，不是新的实验偏离预言。要声称不同于现有量子力学的物理预测，还须修改明确的结构输入并计算其可区分后果。

### 7.5 可复用的推导清单

| 通常的量子结构 | 本稿的推导入口 | 仍然承重的输入 |
|---|---|---|
| Hilbert 振幅与射线 | 全有限正核的商空间；$M_d$ 不可约模块 | 复对象选择、可叠加历史语义 |
| 密度矩阵、Born 规则 | 效果的正、归一化及细分可加 | 所有相关效果的同一赋值 |
| POVM 与仪器 | 交换结果代数与带记录的完全正分支 | 实际结果标签与门供应 |
| 完全正性及 Kraus 形式 | 同一算符值 Gram 余量；Choi 构造 | 全部必要有限参考兼容 |
| 张量复合及纠缠 | 共同复中心上的交换生成关系 | 独立性与复合供应 |
| 可逆门 | 有限正交态对证书、满代数恢复 | 同一完整通道、同维时为酉 |
| Lüders 更新 | 锐效果加每条内部射线不受扰动 | 理想测量条件 |
| Schrödinger 方程 | 连续完整酉群的谱分解 | 时间、群、$H$ 及单位选择 |

**白话。**状态是一种读口，测量是一种把问题送到结果标签的读口，运动也是一种把后面的问题回拉到前面的读口。要求这些读口的全部比较差能放进同一个内部空间，就把它们用同一条规则连起来了。要得到具体的物理世界，还必须说哪些对象、哪些复合、哪些钟和哪些门实际存在；这部分不会因为把公理改叫定义就自动消失。

<a id="section-8"></a>

## 8. 两个观察者、反馈与整体内部的边界

<a id="sec-c120-observers"></a>

### 8.1 自指起点与完整记录

### 命题 8.1（纯态复位必须把全部输入移往记录）

设等距过程 $V:H\to S\otimes E$ 对每个输入纯态都使 $S$ 的约化态为同一纯态 $\lvert s\rangle\langle s\rvert$。则存在等距 $W:H\to E$，使

$$
V\psi=s\otimes W\psi.
$$

因此 $\dim E\ge\dim H$。若无记录端、要求一个全局酉把所有输入变成同一个向量，除一维情形外不可能。

**证明。**
纯态约化为 $\lvert s\rangle\langle s\rvert$ 意味着 $V\psi$ 在 $s^\perp\otimes E$ 上没有分量。取 $W=(\langle s\rvert\otimes I)V$，便有显示分解；$V^*V=I$ 给 $W^*W=I$。全局酉必须保持任意两个输入之间的内积，不能把两个正交输入变成同一向量。

这给“从任意输入返回自指起点”一个合法的局部版本：观察者的指定寄存器返回固定状态，而输入关系转入 $\Omega$ 内其他记录。它不等于整个整体把不同内容擦成同一个内容。有限程序可以包含自身地址或实现自描述协议；这样的编码需要正交可读标签与实际解释器，不能由“地址就是内容”直接保证对任意未知量子态作复制或全局复位。仓库 C117 已明确区分这些情形 [2](#ref-repo-c117)。

### 8.2 观察者序列的差别究竟是什么

如果两位观察者分别以等距 $V_A,V_B$ 编码同一个已给定来源 $H$，而且保留全部记录，再引入任意第三个同源等距编码 $V_C$。支持上的比较

$$
T_{BA}=V_BV_A^*,\qquad T_{CB}T_{BA}=T_{CA}
$$

确实精确接续。这个等式只用 $V_B^*V_B=I$，并不要求两个门序列相同。它是*共同来源和编码已经被给定*后的结构结论，不等于某位观察者从当前记录就知道这些编码。

若只保留输出 $A$ 与 $B$，则应分别研究它们的过程 $\Phi_A,\Phi_B$、比较余量及来源端可恢复代数，而不能把局部过程都当作完整酉门。相位章给出的共同锚和循环读出，能在实际供应时识别有限射线族的相对结构；它仍不提供全知的跨观察者地址匹配。

### 命题 8.2（内证据认证仍是纤维上的常值条件）

设 $\mathcal M$ 为候选内部模型，$r:\mathcal M\to\mathcal R$ 是观察者可得记录，$T:\mathcal M\to\mathcal T$ 为所问内容。存在定义在 $r(\mathcal M)$ 上的 $f$ 使 $T=f\circ r$，当且仅当

$$
r(M)=r(M')\Longrightarrow T(M)=T(M').
$$

**证明。**
必要性代入即得。充分时对每个实际记录 $u$，取任一 $r(M)=u$ 的模型，令 $f(u)=T(M)$；纤维常值保证不依赖选择。

该判据与仓库恢复定理的语义对应一致 [6](#ref-repo-recovery)。它不给有限算法、误差率或采样成本。完整知道另一个观察者的忠实嵌入可以帮助认证交集，但不是认证一个已给定共同接口的必要条件。反过来，没有可区分剩余模型的读口，也就不能凭某个方便的统一表示宣称完整交集已知。

特别地，本稿的有限门证书意味着*有限种精确实验条件*足以决定结论，并不意味着每种只做有限次随机试验就能证明错误概率严格为零。若从频率估计，应保留统计区间，并将精确结论改成有证明的近似结论。

### 8.3 无抵消不等于禁止量子擦除或反馈

比较余量的非负合成法则针对已经指定的完整通道分解。如果后续允许重新取得先前丢开的环境寄存器，系统边界已经扩大，后续操作不再是旧局部通道后面的一条独立通道。此时可以相干地逆转原来的完整等距或酉过程，并不违反余量链法则。

若只保留部分结果，再按读到的标志反馈，必须将这个标志纳入过程的输入。按经典记录控制的一组通道组成一条从带标志直和代数出发的通道，仍满足候选；忘掉标志以后不能凭空沿用同一个恢复保证。若进一步挑选成功记录，需连同成功概率一起描述条件化。

对联合输出 $A\otimes B$ 的*同一个*过程，若两端都可恢复同一来源代数，则它必为交换代数。将联合通道扩充为 $V:H\to A\otimes B\otimes E$ 后，$B$ 是 $A$ 的补读口的一部分。由恢复定理及补通道判据可知：一端可恢复内容落在另一端全部拉回算符的交换子内，而另一端可恢复内容本身又落在其拉回范围内。共同内容因此与自身交换。若两个读口是不同的备选实验，或二者实际共享同一量子载体，则不适用这个独立双份记录结论。

### 8.4 与最新四路径几何的准确连接

一个归一化二元正效果写成

$$
F=\begin{pmatrix}p&z\\\bar z&1-p\end{pmatrix},\qquad
 |z|^2\le p(1-p).
$$

固定 $p$ 后，可变关系是复平面中的一个圆盘。若实际反馈确定的读出只依赖 $\operatorname{Re}(Cz)$，当 $C\ne0$ 时，固定这个值就截出圆盘的一条直线；当 $C=0$ 时，该读出完全不约束 $z$。因此内点通常仍有不同的可行相干完成；沿此直线移动可以改变 $|z|^2$，从而改变混合度 $2[p(1-p)-|z|^2]$，而保持该读出不变。仓库新第 41.3 节把这个几何写成保持实际反馈与 $g$、使原始距离增加 $\theta$ 的精确路径，并覆盖全部边界情形 [1](#ref-repo-firstloss)。

这支持的是“某个线性读口只约束部分关系”的判断。它不支持“没有线性关系时量子场就不存在”，也不支持“所有未读出的方向等同于可恢复信息”：恢复必须保住全部相关乘法及后续测试。这里本文的余量、最大可恢复代数与相位回路分别回答三个不同问题。

### 8.5 有限理论与量子场、标准模型之间

本稿完成的范围是有限复量子对象、通道、恢复、读出与复合的条件理论。要进入量子场，还需无限局部代数、连续空间或因果网络、正能量与相应表示等结构；要进入标准模型，还需具体规范群、物质表示、手征性、相互作用与参数的选择。它们都不由单个二元余量条件唯一决定。

此前“正负光子”的直觉需要保留物理区分：标准电磁理论中的光子是电中性、自共轭粒子，两个螺旋度不是正、负电荷的两种光子；场展开的产生、湮灭部分也不能直接当作两个独立观察者 [18](#ref-tongqed)、[19](#ref-fermilabphoton)。可以继续用内部产生与读出关系组织问题，但具体识别必须经过场的交换关系、表示与动力学检验。关于场与测量的标准接口，可参见 Fewster–Verch 的局域测量框架 [17](#ref-fewsterverch2018)。

**白话。**两个人可以沿不同门序列接近同一个来源，但他们各自知道多少，要看各自的记录是否足以排除其他可能。读口丢掉的关系仍可能留在整体的别处；重新拿到那份记录，就换了一个更大的可操作窗口。没有全知视角，要求我们把“数学上存在一个共同解释”和“这个观察者已经认证了它”分开写清楚。

<a id="section-9"></a>

## 9. 本轮结论、反例与下一步可检验目标

### 9.1 一条候选形成的理论骨架

本轮只提出候选 [(1)](#eq-c120-candidate)：**同一读口的全部二元比较余量，必须共同实现为整体内部的一个 Gram 核。**这条规则在明确对象接口后，同时控制状态、过程、参考、顺序读出与恢复。其几何是等距嵌入后的正交压缩；两个过程对应三个测试相关的正交分量；二元正矩阵的归一化截面是 Bloch 球；相位的有向接续由实际可读的闭环积刻画。

| 要防止的误推 | 本文给出的检验或反例 |
|---|---|
| 单个状态上余量非负就足够 | $M_2$ 的 Schwarz 非 CP 映射；不同参考向量会揭出负块 |
| 固定三元检查决定全部过程 | $M_5$ 的四正但非完全正例；三元余量通过而四元见证为负 |
| 零余量直接等于可恢复来源 | 必须由输出乘法域通过 $\Phi$ 映到来源端；不可达部分可在核中 |
| 只保住一个正交基就保住量子门 | 退相干保标签而损相位；再加星形连接的正负叠加态对才足够 |
| 概率与三点回路总能认出全部相位 | 正定四边形族的环通量仍自由；需要锚或足够的循环证据 |
| 所有不可读内容都永久丢失 | 扩大到内部环境记录会改变允许的过程分解与恢复问题 |
| 定义写在整体内就不再有选择前提 | 经典模型也有正协方差与链法则；复对象和实际供应仍须声明 |

### 9.2 怎样继续，而不以新命名代替证明

下一轮最明确的推进目标是把本稿的精确二元证书量化：若基态对及连接叠加态对的输出并非完全正交，而只有已认证的小重叠，能否由同一有限数据推出到某条可恢复通道的、保留任意参考的误差界？必须说明使用迹距离、算符范数还是 diamond 距离，并证明其维度依赖；不能把有限平均误差直接升级为全状态保证。

另一条后续目标是对象桥接：从项目真正供应的二元滤片与闭环读口，推导附录的非平凡方向条件和结合闭包是否成立。现有的内部比较余量定理解决了给定对象上的过程合法性；它不替这个桥接义务给出答案。若从实际协议发现违反附录条件的模型，应修改对象候选，并重新检查它能否满足实验约束。

本稿的经典数学来源包括 Stinespring 扩充、Choi 完全正判据、乘法域、算符代数量子纠错与射影框架的循环不变量。本文的工作是把它们以同一内部关系语言接起来，给出逐项可审查的有限推导与反例；未做穷尽的文献新颖性检索，也不赋予已有定理新的发现权。

### 9.3 完整白话总结

**白话。**把整体想成一张还没有被一个观察者全部读完的关系网。观察者每走一步，都把后面两段关系压回自己现在能使用的窗口。先接好再压回来，和先分别压回来再接好，会有一块差额。这个差额不能凭空写，它必须还能作为另一组方向的比较留在整体内部；所有对要放得进同一个空间。连续走两步，这两步遗漏的部分分层接续，不会靠符号相反就互相抹掉。某段内容能不能找回来，要看另一份记录有没有分辨出它的量子方向：如果只记住与输入无关的支路，全部量子关系还能恢复；如果记住了某个方向的标签，另一边能完整保留的关系就会受到限制。对最小的二元量子块，保住一组正反状态只保住一个方向，再保住一组横过来的正反状态，第三个方向就被同一个乘法关系带出来，同维门因此被锁成一个旋转式的酉过程。不同观察者可以沿不同路径做这些事；他们是否已经知道路径之间的关系，仍要由他们实际取得的共同参考和闭环记录来认证。这就是本轮从二元比较、三向闭合到完整有限量子过程的候选。

<a id="section-10"></a>

## 10. 有限量子原子的实关系选择：前提与完整证明

<a id="sec-local-core"></a>

本附录自足重述 C119 实球形二元块的局部选择步骤，说明主文复矩阵部门的来路。它不同于仓库新近使用 C116 编号的闭环三向回读候选。其范围是实球形二元正锥及下列动力标签条件；它没有证明这些条件由一般正核自动强制成立。这里由三方向乘积形成的中心单位记为 $\jmath$，以区别一般线性算子的符号。

### 10.1 实锥与规范对称变化

### 定义 10.1（二元比较块）

令 $W$ 为有限维实欧氏空间，$V=\mathbb R e\oplus W$、$e=(1,0)$。未归一化的正关系为

$$
C=\{(s,r):s\ge\|r\|\},\qquad
 \langle (s,r),(t,u)\rangle_E=st+r\cdot u.
$$

规范滤片是把 $e$ 送到给定严格正元 $x=(s,r)$ 的欧氏正定、自伴、双向保锥线性变换。双向保锥指变换及其逆都保持 $C$。

### 引理 10.2（规范滤片及其导数）

令 $\delta=\sqrt{s^2-\|r\|^2}>0$。唯一的规范滤片是

$$
P_x=\begin{pmatrix}
 s&r^{\mathsf T}\\
 r&\delta I+rr^{\mathsf T}/(s+\delta)
 \end{pmatrix}.
$$

其一阶响应定义对称乘法

$$
(\alpha,a)\circ(\beta,b)
 =\left.\frac{d}{dt}P_{e+t(\alpha,a)}(\beta,b)\right|_{0}
 =(\alpha\beta+a\cdot b,\alpha b+\beta a).
$$

特别地，$L_a(\beta,b)=(a\cdot b,\beta a)$。

**证明。**
写 $\eta=\operatorname{diag}(1,-I)$。保锥可逆变换 $T$ 保持锥边界，所以对所有单位 $n$，$Q(T(1,n))=0$。将 $T^{\mathsf T}\eta T$ 分块，比较 $n,-n$ 消去非对角块，再比较正交基与它们的二元和，得 $T^{\mathsf T}\eta T=c\eta$；$Te$ 在锥内部给 $c>0$。

若 $T=T^{\mathsf T}\succ0$ 且 $Te=x$，写其右下块为 $B$，便有 $c=\delta^2$、$B^2=\delta^2 I+rr^{\mathsf T}$。正定 $B$ 是右侧唯一正平方根，在 $r^\perp$ 上为 $\delta I$、在 $r$ 方向为 $s$，即显示公式。反过来，该公式的特征值为 $s\pm\|r\|$ 及 $\delta$，全为正；直接相乘验证 $P_x\eta P_x=\delta^2\eta$，且 $P_xe=x$，从而双向保锥。对 $s=1+t\alpha,r=ta$ 求导即得乘法。该乘法满足 Jordan 恒等式，因为 $L_{z^2}$ 是 $L_z$ 的线性组合；其平方锥恰为 $C$，可用互补幂等元 $p_\pm=(1,\pm n)/2$ 对正元分解并开平方验证。

这一构造仍承担球形正锥、欧氏标尺和规范滤片的定义。若赋予它物理实现，还要保留成功权重；双向保正滤片不等于确定性的可逆通道。

### 10.2 二元回路为何强制三维

### 定义 10.3（旁观方向条件）

每个实方向 $a$ 产生 $D_a\in\mathfrak{so}(W)$，$a\mapsto D_a$ 实线性，$D_a a=0$，且 $D\ne0$。要求对全部标签及其线性合成，

<a id="eq-c120-local-spectator"></a>

$$
\boxed{[D_a,D_b]z=0\quad(z\perp a,b).}
\tag{33}
$$

这是完整向量等式。只比较 $z\cdot[D_a,D_b]z$ 没有约束力，因为反对称算子的该自比较总是零。

### 定理 10.4（三维选择）

<a id="thm-c120-local-three"></a>

上述条件强制 $\dim W=3$，且存在 $\kappa>0$，使

<a id="eq-c120-local-loop"></a>

$$
\begin{aligned}
[D_a,D_b]&=-\kappa[L_a,L_b],
\end{aligned}
\tag{34}
$$

<a id="eq-c120-local-square"></a>

$$
\begin{aligned}
D_a^2x&=\kappa\bigl((a\cdot x)a-\|a\|^2x\bigr),
\end{aligned}
\tag{35}
$$

<a id="eq-c120-local-triple"></a>

$$
\begin{aligned}
D_aD_bx&=\kappa\bigl((a\cdot x)b-(a\cdot b)x\bigr),
\end{aligned}
\tag{36}
$$

<a id="eq-c120-local-bracket"></a>

$$
\begin{aligned}
D_{D_a b}&=[D_a,D_b].
\end{aligned}
\tag{37}
$$

按 $D$ 选择取向后，$D_ab=\sqrt\kappa\,a\times b$。

**证明。**
标签线性及 $D_aa=0$ 给 $D_ab=-D_ba$，故 $x\cdot D_ab$ 是交替三形式。令

$$
B(a,b)x=(b\cdot x)a-(a\cdot x)b=[L_a,L_b]x.
$$

交换子 $[D_a,D_b]$ 反对称。式 [(33)](#eq-c120-local-spectator) 使它在 $\operatorname{span}(a,b)^\perp$ 上为零，并保持 $\operatorname{span}(a,b)$；二维反对称算子只有一个方向，所以它是 $B(a,b)$ 的实倍数。

这个倍数不能逐对自由选。取正交基 $e_i$，写 $[D_{e_i},D_{e_j}]=\lambda_{ij}B(e_i,e_j)$。在二元合成标签

$$
a=\sum_i e_i,\qquad b=\sum_i\left(i-\frac{n+1}{2}\right)e_i
$$

上展开，其每个基对系数都是非零的 $j-i$。合成对也必须有一个共同平面比例，比较基系数便得全部 $\lambda_{ij}=\lambda$。双线性将它扩到任意 $a,b$。

将交换子等式作用于 $a$ 并使用反对称性，得

$$
\|D_ab\|^2=-\lambda\bigl(\|a\|^2\|b\|^2-(a\cdot b)^2\bigr).
$$

非平凡性排除 $\lambda=0$，故 $\lambda=-\kappa<0$，并得 [(35)](#eq-c120-local-square)。极化该平方式，加上交换子式，给 [(36)](#eq-c120-local-triple)；再由 $D_{D_ab}x=-D_xD_ab$ 得 [(37)](#eq-c120-local-bracket)。

取正交单位 $u,v$，令 $w=D_uv/\sqrt\kappa$。上式说明 $u,v,w$ 正交归一，且

$$
D_w=\sqrt\kappa(vu^{\mathsf T}-uv^{\mathsf T}),\qquad
 D_w^2=-\kappa(P_u+P_v).
$$

另一方面，式 [(35)](#eq-c120-local-square) 给 $D_w^2=\kappa(P_w-I)$。因此

$$
\boxed{I=P_u+P_v+P_w,}
$$

恰好三个方向覆盖整个 $W$。三维交替三形式只有一个尺度，范数式将其大小固定为 $\sqrt\kappa$；取向由其符号决定。

若去掉 $D\ne0$，任意维度都容许 $D=0$。若只查坐标对，模型 $W=\mathbb R^3\oplus\mathbb R$、$D_ab=(a'\times b',0)$ 会通过；但对 $a=e_1+e_4,b=e_2,z=e_1-e_4$，有 $z\perp a,b$ 而 $[D_a,D_b]z=e_2$。这说明必须检验合成标签。此规则只作用于二元球块，不能把它逐字施加到一般高维系统的全部自伴元。

### 10.3 三方向的有向体积成为内部复数

这里把候选中的“由该块生成的结合保星闭包”说精确：它是非零含幺实结合
$*$-代数 $\mathcal B$，带实线性映射 $\iota:V\to\mathcal B$，满足

$$
\iota(e)=1,\qquad \iota(x)^*=\iota(x),\qquad
 \frac{\iota(x)\iota(y)+\iota(y)\iota(x)}2=\iota(x\circ y),
$$

且 $\iota(V)$ 生成整个 $\mathcal B$。结合性、保星与生成性是这里明确保留的闭包条件；以下证明所有这样的非零闭包都给出同一个代数，不先假设它的维数。

作为实结合闭包的显式构造，用实数对构造 $\mathbb C_\jmath=\{s+\jmath t\}$，其中 $\jmath^2=-1$。记 $\mathcal A=\mathbb C_\jmath\oplus\mathbb C_\jmath^3$，在其上定义

<a id="eq-c120-local-product"></a>

$$
(\alpha,a)(\beta,b)
 =(\alpha\beta+a\cdot b,\alpha b+\beta a+\jmath(a\times b)).
\tag{38}
$$

这里的点积、叉积作复双线性延伸。

### 定理 10.5（内部复代数及最小振幅）

<a id="thm-c120-local-complex"></a>

式 [(38)](#eq-c120-local-product) 给出实八维结合 $*$-代数，伴随为逐分量复共轭，自伴部恰为原来的 $V$。对于正向正交基，

$$
e_ie_j+e_je_i=2\delta_{ij}1,
 \qquad \jmath=e_1e_2e_3,
 \qquad \jmath^2=-1.
$$

因此 $\jmath$ 实际属于三个实方向生成的闭包；该闭包是 $\operatorname{Cl}_{3,0}\cong M_2(\mathbb C)$，最小左理想为 $H\cong\mathbb C^2$。

**证明。**
由三线性，只需在三个实向量上核对结合律。两个括号方式的标量项相同，向量差为

$$
(a\cdot b)c-(b\cdot c)a-(a\times b)\times c+a\times(b\times c)=0,
$$

这是定理 [10.4](#thm-c120-local-three) 的三重积恒等式。共轭将 $\jmath$ 变号，交换向量次序也使叉积变号，故 $(xy)^*=y^*x^*$。直接计算得 $e_1e_2=\jmath e_3$，从而 $e_1e_2e_3=\jmath$，没有再添独立复方向。

映射

$$
\alpha1+z\cdot e\longmapsto
 \begin{pmatrix}\alpha+z_3&z_1-iz_2\\z_1+iz_2&\alpha-z_3\end{pmatrix}
$$

保持乘法与伴随，且每个复二阶矩阵唯一具有这种展开，所以是同构。

还须排除其他闭包把这个代数进一步压小。令 $\operatorname{Cl}_{3,0}$ 为由
$e_i^*=e_i$、$e_ie_j+e_je_i=2\delta_{ij}1$ 定义的含幺实结合 $*$-代数。
反交换关系把全部词约到
$1,e_1,e_2,e_3,e_1e_2,e_1e_3,e_2e_3,e_1e_2e_3$，故其维数至多为八。
上述显式模型由三个 $e_i$ 生成，且实维数为八，所以从这个定义代数到模型的满射必为同构。

任意容许闭包 $\mathcal B$ 的三个生成元也满足这些关系，因而是
$\operatorname{Cl}_{3,0}\cong M_2(\mathbb C)$ 的非零含幺商。$M_2(\mathbb C)$ 作为*实*代数仍然简单：
若双边理想含非零矩阵 $A$，选取非零条目 $a_{ij}$，则
$E_{pi}AE_{jq}=a_{ij}E_{pq}$ 属于该理想；再左乘 $(a_{ij}^{-1})I$，得到每个矩阵单位
$E_{pq}$。左乘 $iI$ 又得到全部 $iE_{pq}$，这些矩阵的实线性张成就是整个代数。
所以商映射的核只能为零或全体；非零含幺目标排除后者。
因此任意容许的生成闭包都与显式模型保星同构，不存在更小的非零商。

令 $p=(1+e_3)/2,q=e_1p$。左理想 $\mathcal A p$ 在中心 $\mathbb C_\jmath$ 上由 $p,q$ 张成，且对 $x=\alpha p+\beta q,y=\gamma p+\delta q$，

$$
x^*y=(\bar\alpha\gamma+\bar\beta\delta)p.
$$

这个系数给正定复内积。矩阵表示说明它是二维且为最小左理想，代数在其上忠实作用。

自伴元 $sI+r\cdot\sigma$ 的特征值是 $s\pm\|r\|$，所以构造后的矩阵正锥恰好恢复原来的 $C$。其归一化截面是三维球，极点是球面；概率与纯态的严格对应见第 [7](#sec-c120-qm) 节。

**白话。**先规定两份方向怎样比较，再比较沿它们前后运动的小回路。回路不能暗中推动和这两个方向都垂直的完整参考；对合成方向也这样要求，两个方向就会带出第三个，而且三个已经覆盖整个二元块。把三个方向按顺序相乘，会得到一个再乘自己就反号的内部关系，它承担复数的作用。这样的复结构有了明确来路；观察者的记录守恒接下来才有可用的物理振幅空间。

有限系统类还允许独立复合以及非零投影支持的角代数。由第 [7](#sec-c120-qm) 节的复合定理，$N$ 个二元原子给 $M_{2^N}(\mathbb C)$。对任意 $d\le2^N$，取秩 $d$ 的投影 $p$，角代数 $pM_{2^N}(\mathbb C)p$ 同构于 $M_d(\mathbb C)$，单位为 $p$。因此在这项系统闭包约定下，全部有限复量子系统均得到构造。支持限制与观察窗口的保单位嵌入是两类接口，不能把改变单位的角嵌入误作同一个共同来源接缝。

<a id="references"></a>

## 参考文献

<a id="ref-repo-firstloss"></a>

### [1]

The Omega Institute, *Four-path full-record recovery: mixed geometric comparison and local effect exclusion*, Continuation II, §41. 固定快照 `ef908d0914b7d1907fa25f59f02fcfad5275f42d`；新增段落合并于 2026-11-03 14:28:03 UTC。[不可变理论源码](https://github.com/the-omega-institute/trureturing/blob/ef908d0914b7d1907fa25f59f02fcfad5275f42d/docs/develop/theory/QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_II.md)。本文已核读第 40 节定义接口及第 41 节证明、未决义务。

<a id="ref-repo-c117"></a>

### [2]

The Omega Institute, *AURIC Common Source, Self-Reference and Observer Sequences C117*. 同一快照。[不可变 C117 源码](https://github.com/the-omega-institute/trureturing/blob/ef908d0914b7d1907fa25f59f02fcfad5275f42d/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)。

<a id="ref-repo-orientation"></a>

### [3]

The Omega Institute, *AURIC Composite Comparison Reference-Free Filter Relations V96 Continuation*, §§132–139，尤其 §138.2 的对象选择桥接义务。[不可变闭环续篇](https://github.com/the-omega-institute/trureturing/blob/ef908d0914b7d1907fa25f59f02fcfad5275f42d/docs/develop/theory/AURIC_COMPOSITE_COMPARISON_REFERENCE_FREE_FILTER_RELATIONS_V96_CONTINUATION.md)。该仓库 C116 编号指闭环取向文本，不与本研究旧稿局部实锥编号混同。

<a id="ref-repo-centering"></a>

### [4]

The Omega Institute, *UniformVarianceCentering.lean*. 主要定位：`hermitian_block_centering_and_gram_bound`。[不可变 Lean 源码](https://github.com/the-omega-institute/trureturing/blob/ef908d0914b7d1907fa25f59f02fcfad5275f42d/D5/S3/Quantum/Matrix/UniformVarianceCentering.lean)。本文核读相关声明，未执行编译。

<a id="ref-repo-bound"></a>

### [5]

The Omega Institute, *UniformVarianceTraceBound.lean*. 主要定位：`hermitian_unital_direct_sum_defect_trace_bound`。[不可变 Lean 源码](https://github.com/the-omega-institute/trureturing/blob/ef908d0914b7d1907fa25f59f02fcfad5275f42d/D5/S3/Quantum/Matrix/UniformVarianceTraceBound.lean)。

<a id="ref-repo-recovery"></a>

### [6]

The Omega Institute, *TargetRecoveryCriterion.lean*. `target_recovery_criterion` 及纤维碰撞判据。[不可变 Lean 源码](https://github.com/the-omega-institute/trureturing/blob/ef908d0914b7d1907fa25f59f02fcfad5275f42d/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)。全余域恢复函数的声明保留其非空前提；本文只在实际记录像上定义恢复。

<a id="ref-stinespring1955"></a>

### [7]

W. F. Stinespring, ``Positive functions on $C^*$-algebras'', *Proceedings of the American Mathematical Society* **6**(2), 211–216 (1955). [doi:10.1090/S0002-9939-1955-0069403-4](https://doi.org/10.1090/S0002-9939-1955-0069403-4)。扩充结构的经典来源；本文独立给出有限矩阵构造。

<a id="ref-choi1974"></a>

### [8]

M.-D. Choi, ``A Schwarz inequality for positive linear maps on $C^*$-algebras'', *Illinois Journal of Mathematics* **18**(4), 565–574 (1974). [doi:10.1215/ijm/1256051007](https://doi.org/10.1215/ijm/1256051007)。Schwarz 不等式及乘法域的经典来源；本文所用有限结论均附证明。

<a id="ref-choi1975"></a>

### [9]

M.-D. Choi, ``Completely positive linear maps on complex matrices'', *Linear Algebra and its Applications* **10**(3), 285–290 (1975). [doi:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。

<a id="ref-beny2007"></a>

### [10]

C. B\'eny, A. Kempf and D. W. Kribs, ``Quantum error correction of observables'', *Physical Review A* **76**, 042303 (2007). [arXiv:0705.1574](https://arxiv.org/abs/0705.1574)；[doi:10.1103/PhysRevA.76.042303](https://doi.org/10.1103/PhysRevA.76.042303)。重点对应 Theorem 9、Corollary 10 及 §IV。

<a id="ref-knill1997"></a>

### [11]

E. Knill and R. Laflamme, ``Theory of quantum error-correcting codes'', *Physical Review A* **55**, 900–911 (1997). [doi:10.1103/PhysRevA.55.900](https://doi.org/10.1103/PhysRevA.55.900)；作者预印本 [quant-ph/9604034](https://arxiv.org/abs/quant-ph/9604034)。期刊元数据以出版方条目为准。

<a id="ref-kretschmann2008"></a>

### [12]

D. Kretschmann, D. W. Kribs and R. W. Spekkens, ``Complementarity of private and correctable subsystems in quantum cryptography and error correction'', *Physical Review A* **78**, 032330 (2008). [arXiv:0711.3438](https://arxiv.org/abs/0711.3438)；[doi:10.1103/PhysRevA.78.032330](https://doi.org/10.1103/PhysRevA.78.032330)。

<a id="ref-busch1999"></a>

### [13]

P. Busch, ``Stochastic Isometries in Quantum Mechanics'', *Mathematical Physics, Analysis and Geometry* **2**, 83–106 (1999). 作者于 2013 年上传的原论文：[arXiv:1303.6624](https://arxiv.org/abs/1303.6624)；[doi:10.1023/A:1009822315406](https://doi.org/10.1023/A:1009822315406)。正随机等距、正交保持及其结构；本文的有限测试清单另附直接证明。

<a id="ref-busch2003"></a>

### [14]

P. Busch, ``Quantum states and generalized observables: a simple proof of Gleason's theorem'', *Physical Review Letters* **91**, 120403 (2003). [quant-ph/9909073](https://arxiv.org/abs/quant-ph/9909073)；[doi:10.1103/PhysRevLett.91.120403](https://doi.org/10.1103/PhysRevLett.91.120403)。

<a id="ref-chien2015"></a>

### [15]

T.-Y. Chien and S. Waldron, ``A characterization of projective unitary equivalence of finite frames and applications'', *SIAM Journal on Discrete Mathematics* **30**(2), 976–994 (2016). [doi:10.1137/15M1042140](https://doi.org/10.1137/15M1042140)；[已核读 2015 年作者稿](https://www.math.auckland.ac.nz/~waldron/Preprints/Tripleprods/tripleprods.pdf)。本文采用生成树基本环及有向整数循环的充分条件表述。

<a id="ref-oszmaniec2024"></a>

### [16]

M. Oszmaniec, D. J. Brod and E. F. Galvão, ``Measuring relational information between quantum states, and applications'', *New Journal of Physics* **26**, 013053 (2024). [arXiv:2109.10006](https://arxiv.org/abs/2109.10006)；[doi:10.1088/1367-2630/ad1a27](https://doi.org/10.1088/1367-2630/ad1a27)。关系不变量与循环测试。

<a id="ref-fewsterverch2018"></a>

### [17]

C. J. Fewster and R. Verch, ``Quantum fields and local measurements''. [arXiv:1810.06512](https://arxiv.org/abs/1810.06512)，v3 (2020)。重点对应系统–探针耦合、完全正诱导读出与因果顺序仪器合成。

<a id="ref-tongqed"></a>

### [18]

D. Tong, *Quantum Field Theory*, Chapter 6, ``Quantum Electrodynamics'', §§6.1–6.2. [作者课程原文](https://davidtong.org/pdfs/teaching/quantum-field-theory/qft6.pdf)。电磁场量子化与两个物理偏振自由度。

<a id="ref-fermilabphoton"></a>

### [19]

Fermilab, ``Charge, Spin and Mass of Fundamental Particles'', *Physics Questions People Ask Fermilab*. [机构原始答复](https://www.fnal.gov/pub/science/inquiring/questions/mass_information.html)。这里只用于光子无电荷与其反粒子相同的基本区分，不引用该历史页面的其他实验数值。

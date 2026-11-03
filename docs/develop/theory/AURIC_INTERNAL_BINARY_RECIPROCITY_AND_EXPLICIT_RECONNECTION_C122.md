AURIC 量子关系研究工作稿

# C122

**内部二元互易 与显式回接**

从同一参照的二元比较，到 Petz 规则、

有限三维提升、可恢复代数与可执行证书

**本轮唯一候选。**同一个内部参考准备、同一条实际过程所定义的二元比较，反向读取时交换两端，配对值保持不变。它在有限复量子部门唯一确定 Petz 回推，并把回接误差写成二元关系的可计算缺陷。

**本轮完成的推进。**将 C121 的“存在共同恢复”推进到一个指定的、显式的回推；证明它的组合规律、几何与恢复界；给出在明确门资源下的实现方法及有限数据误差预算。

**理论范围。**主文是有限量子对象内的条件重构。附录自足说明一种从实二元球块选择复量子原子的路径。对象选择、物理可用性与概率语义均明确列出；不把“内生”解释成无前提地排除所有其他理论。

2026 年 11 月 4 日（新加坡时间）

仓库固定快照 `fc2bf058b103a58ec9ef904e17faba66ba94e383`

提交时间：2026-11-04 00:43:35 SGT

可独立编译的完整 TeX 源码；使用 XeLaTeX


将参考状态 $\sigma$、过程 $\mathcal N$ 及其预测 $\tau=\mathcal N(\sigma)$ 视为同一内部记录的一部分，定义二元配对
$b_{\sigma,\mathcal N}(A,B)=\operatorname{Tr}[B\mathcal N(\sigma^{1/2}A\sigma^{1/2})]$。
要求反向配对交换两个效果后不变，唯一给出
$\mathcal N^\sharp_\sigma=\Gamma_\sigma\mathcal N^*\Gamma_\tau^{-1}$，
其中 $\Gamma_\sigma(X)=\sigma^{1/2}X\sigma^{1/2}$，逆只在预测支持上使用。
本文证明该规则的合法性、双反向性与组合性，严格区分“返回参考”与“恢复任意内容”。

加权坐标把往返过程化成 $T^*T$，因此其谱落在 $[0,1]$。
同一几何给出 $\chi^2_{1/2}$ 缺陷对显式 Petz 恢复误差的直接控制；
两个扰动沿同一读口的比较可在三维中精确实现。
最大混合参考下，往返残差是双交换子的负和，从而固定内容形成交换子代数，并得到全参考的 diamond 范数界。
结合单参考 Barnum–Knill 定理与 C121 的有限二元证书，可把存在性结果转化为指定 Petz 回推的误差证书。

实现部分给出滤片、逆扩张与一致幅度放大的精确条件，以及从有限二元层析到整体误差的维数显式预算。
最后列出 Born 规则、测量、完全正性、张量积、酉运动和 Schrödinger 方程各自的推导入口，并保留尚未由本轮候选确定的物理选择。

**白话。**把一份已经在内部准备好的参照送过一条过程，前后各问一个问题。回头读时仍然使用这份参照和这条过程，只把两个问题对调。要求两种读法对上，会选出一条确定的回推。回推能把参照送回去；能不能把别的内容也送回去，要看那些内容在途中还剩下多少可比较的关系。损失不再只是一句“看不见”，而能写成具体的差、几何长度和执行误差。

## 目录

- [1. 最新项目接点与本轮的一个候选](#section-1)
- [2. 同一个反向规则怎样组成更大的结构](#section-2)
- [3. 把存在性变成显式回接：保真度与全参考误差](#section-3)
- [4. 显式反向的几何：加权收缩、三维读口与稳定关系](#section-4)
- [5. 从数学回推到内部识别与实际供应](#section-5)
- [6. 候选与通常有限量子力学的完整推导接口](#section-6)
- [7. 反向检验：删除一项约束会发生什么](#section-7)
- [8. 两个观察者、顺序读出与整体内部的共同来源](#section-8)
- [9. 本轮完成的理论与最终白话](#section-9)
- [10. 有限量子原子的实关系选择：前提与完整证明](#section-10)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 最新项目接点与本轮的一个候选

<a id="sec-c122-candidate"></a>

### 1.1 固定仓库状态，保留其尚未完成的前件

本轮核对仓库 HEAD
`fc2bf058b103a58ec9ef904e17faba66ba94e383`，
提交时间为 2026-11-03 16:43:35 UTC。
最新合并推进了 FIB 共同读出分区的 §§136–140：
在同一原始过程及相同边际约束下构造实际分区，证明某些行列式值形成区间、
存在严格正值且零在闭包中，并把一个精确降秩结论写成带有明确负方向前件的条件定理。
原文最后明确保留了“闭包含零而尚无精确零”的可能性；
非零角字符上的负方向也不能直接替代所需的不变方向。
因此不能把这些结果转述为已经无条件解决全部原始秩问题或全部 64 个坐标同时达到目标。 [1](#ref-repo-fib)

这与本轮的接点是证明责任：
*同一个实际过程、它自己的终端因子、近似逼近、精确达到，必须分别说明。*
这不是声称 FIB 的热核分区已经导出量子 Petz 公式。

量子恢复目录中，本轮核读了参考回推与稳定性模块，
即 `ReferencePetzChannel.lean` 和
`CanonicalPetzStability.lean`；
也核读了加权谱坐标、Schwarz 恢复及有限 Kraus 可逆性模块的定义和定理陈述。
前者将支持上的 Petz 核用固定参考密度矩阵补全为通道，并证明恢复参考；
稳定性模块给出带支持谱参数的熵缺陷四次根界。
这些源码已有相关条件证明，不等于已从无结构的 $\Omega$ 唯一推出量子力学；
部分文件仍带有项目自己的工作或审计范围标记。
本稿未重新运行整个仓库的 Lean 编译。 [2](#ref-repo-petz)

### 1.2 对象层、记录层与本轮新增约束

我们把 $\Omega$ 作为整个关系系统的名称；有限观察窗口只使用其中明确供应的对象与操作。
主文先在有限全矩阵部门工作：

$$
\mathcal A=M_d(\mathbb C),\qquad
 \mathcal B=M_k(\mathbb C).
$$

状态为正归一化读口，效果为 $0\le A\le I$，过程为线性且在任意有限参考接续后仍保持正性的保迹映射。
这些条件的有限构造在第 [6](#sec-c122-qm) 节证明；
一种不先从复数起步的二元原子选择在附录 [10](#sec-local-core) 中证明。

### 定义 1.1（带内部参照的过程）

一个参考过程是 $(\sigma,\mathcal N,\tau)$，其中 $\sigma>0$、
$\operatorname{Tr}\sigma=1$、$\mathcal N$ 是实际指定的通道，且 $\tau=\mathcal N(\sigma)$。
输出对象限制到 $P\mathcal BP$，$P=\operatorname{supp}\tau$，因此 $\tau$ 在该对象上严格正。
参考状态是过程记录中已经供应的准备；不把它当作掌握整个 $\Omega$ 的外部全知分布。

限制支持不会漏掉由这个完整源产生的输出。
若 $\mathcal N(X)=\sum_iK_iXK_i^*$，$\sigma\ge mI>0$，
则 $\tau\ge m\sum_iK_iK_i^*$。
对 $\ker\tau$ 中的向量取期望，得到 $PK_i=K_i$；
所以 $\mathcal N(X)=P\mathcal N(X)P$，$\mathcal N^*(P)=I$。
若原来的 $\sigma$ 本身奇异，就先限制输入到其支持；对先验零权重的方向没有由下述规则唯一决定的回推。

### 定义 1.2（二元参照比较）

记 $\Gamma_\sigma(A)=\sigma^{1/2}A\sigma^{1/2}$。
前后两端的效果 $A,B$ 定义

<a id="eq-c122-pair"></a>

$$
b_{\sigma,\mathcal N}(A,B)
 =\operatorname{Tr}\!\left[B\,\mathcal N\!\left(\Gamma_\sigma(A)\right)\right].
\tag{1}
$$

它对每一端分别线性、取非负值，且
$b(I,I)=1$、$b(A,I)=\operatorname{Tr}(\sigma A)$、$b(I,B)=\operatorname{Tr}(\tau B)$。

### 定义 1.3（C122：内部参照的二元互易）

同一参考过程的反向读口 $\mathcal N^\sharp_\sigma$ 必须是一个共同的合法过程，并满足

<a id="eq-c122-reciprocity"></a>

$$
\boxed{\quad
 b_{\sigma,\mathcal N}(A,B)
 =b_{\tau,\mathcal N^\sharp_\sigma}(B,A)
 \quad\text{对全部效果 }A,B.
 \quad}
\tag{2}
$$

比较的两端可以交换，参考与实际过程不能在逐对检验时换掉。

这就是本轮唯一新增的候选约束。它约束两个定义之间的相容性；
“全部效果”的无限写法在有限维中可用两端效果空间的有限基逐项检验。
但用怎样的参照配对来描述一个物理实验仍有内容。
式 [(1)](#eq-c122-pair) 采用平衡平方根配对，不能把这一选择藏在“只是定义”四个字中。

### 1.3 唯一显式回推：完整有限证明

### 定理 1.4（二元互易唯一确定 Petz 回推）

<a id="thm-c122-petz-basic"></a>

在上述支持对象之间，式 [(2)](#eq-c122-reciprocity) 有唯一线性解：

<a id="eq-c122-petz"></a>

$$
\boxed{\quad
 \mathcal N^\sharp_\sigma(X)
 =\sigma^{1/2}\mathcal N^*
       \!\left(\tau^{-1/2}X\tau^{-1/2}\right)\sigma^{1/2}.
 \quad}
\tag{3}
$$

该解完全正、保迹，并且 $\mathcal N^\sharp_\sigma(\tau)=\sigma$。

**证明。**
将两侧以迹对偶重写：

$$
\operatorname{Tr}\!\left[A\,\Gamma_\sigma\mathcal N^*(B)\right]
 =\operatorname{Tr}\!\left[A\,\mathcal N^\sharp_\sigma\Gamma_\tau(B)\right].
$$

效果实线性张成全部自伴矩阵，进而复线性张成全部矩阵；
迹配对非退化，所以
$\mathcal N^\sharp_\sigma\Gamma_\tau=\Gamma_\sigma\mathcal N^*$。
在支持上 $\Gamma_\tau$ 可逆，立即得到唯一公式。

设 $\mathcal N$ 的 Kraus 算子为 $K_i$，令
$L_i=\sigma^{1/2}K_i^*\tau^{-1/2}$。
则回推为 $\sum_iL_iXL_i^*$，故对任意有限参考仍保持正性。
又

$$
\sum_iL_i^*L_i
 =\tau^{-1/2}\Bigl(\sum_iK_i\sigma K_i^*\Bigr)\tau^{-1/2}
 =P,
$$

这是输出支持对象的单位，所以保迹。
最后
$\mathcal N^\sharp_\sigma(\tau)=\sigma^{1/2}\mathcal N^*(P)\sigma^{1/2}=\sigma$。

式 [(3)](#eq-c122-petz) 是已知的 Petz 转置通道，本稿不主张其公式新颖。
这里的工作是把它作为本轮内部二元约束的唯一解，
与项目的实际支持、同一过程和有限证书要求接起来。 [3](#ref-petz1986)、[4](#ref-jencova2024)

若需要在原输出全空间上定义回推，可使用广义逆并补全：

<a id="eq-c122-completion"></a>

$$
\widehat{\mathcal N^\sharp_\sigma}(X)
 =\mathcal N^\sharp_\sigma(PXP)+\operatorname{Tr}[(I-P)X]\,\sigma.
\tag{4}
$$

这确实是 CPTP；第二项是检测支持外分量后重备参考。
它对 $\mathcal N$ 的全部输出与原回推相同。
支持外的选择不是互易关系所确定的；尤其不能把任意全空间补全都当成保持全部张量组合规律的同一个规则。

### 1.4 这个二元数值能怎样读到

在带有共轭参考副本的空间中，令

$$
\lvert \sqrt\sigma\rangle
 =(\sqrt\sigma\otimes I)\sum_i\lvert i\rangle\otimes\lvert \bar i\rangle.
$$

它已归一化。直接展开矩阵元得到

<a id="eq-c122-operational-pair"></a>

$$
b_{\sigma,\mathcal N}(A,B)
 =\operatorname{Tr}\!\left[
 (B\otimes A^{\mathsf T})
 (\mathcal N\otimes\operatorname{id})
 \lvert \sqrt\sigma\rangle\langle \sqrt\sigma\rvert
 \right].
\tag{5}
$$

因此，若该参考纯化与对应的两端效果已经供应，
这个数值就是一次联合二元读出的概率。
$A^{\mathsf T}$ 是共轭参考上的效果，不要求实现把任意未知状态转置的非法通道。

这种实验与“先在源上作 Lüders 测量 $A$，再送入 $\mathcal N$”有区别：
后者使用 $\sqrt A\,\sigma\sqrt A$，前者使用 $\sqrt\sigma A\sqrt\sigma$。
二者一般不相等。不能把它们的统计数据互相替换，
也不能由公式存在推出观察者已经拥有纯化、逆门和滤片。

### 1.5 平方根是否也能由更大的关系结构选出

2026 年 10 月 29 日提交的 Surace–Li–Buscemi 预印本，
在有限全矩阵代数、所有参考状态与所有通道这一既定对象类内证明：
若一个参考回推指派恢复参考，同时满足双反向、顺序组合、并行组合与酉逆相容，
它只能是 Petz 指派；平方根与混合仿射性由这些要求推出。
非满秩情形的唯一性限于对应支持。 [5](#ref-retrodiction2026)

本稿下一节自足证明 Petz 具有这些结构；
上述“所有可能指派的唯一性”使用该文的完整定理，本文不伪装为重新证明了它。
它给本轮候选一个更大的容器：
*带参考对象组成的过程范畴，其反向是一个与顺序、并行相容的对合。*
这一结果在量子对象已选定之后成立；经典 Bayes 反推也满足相应结构，所以它本身不是排除经典理论的量子起源证明。

**白话。**一个读口把参照中的一部分送出去，另一个读口在输出端问问题。要求回头问时，同一对问题仍然对得上，就不能随手挑一个“差不多的逆过程”；回推公式被两端关系锁住了。再看三步接续、两个独立过程并排运行、前后反转两次，它仍然接得上。这说明这个二元规则属于一个更大的过程结构，但没有说明所有世界只能选择量子这种对象。

<a id="section-2"></a>

## 2. 同一个反向规则怎样组成更大的结构

<a id="sec-c122-reverse-laws"></a>

沿用前章的二元加权互易规则，记

$$
\Gamma_\sigma(X)=\sigma^{1/2}X\sigma^{1/2},\qquad
 \tau=\mathcal N(\sigma),\qquad
 \mathcal P_{\sigma,\mathcal N}
 =\Gamma_\sigma\mathcal N^*\Gamma_\tau^{-1}.
$$

这里 $\sigma>0$，$\mathcal N$ 是有限维 CPTP 通道，所有逆均为支撑逆。
公式是已有的 Petz 反向，不是本文新发明 [3](#ref-petz1986)。本章研究这个*已确定的*反向怎样复合、何时恢复全部内容，以及有限误差下能给出什么全参考保证。

令 $P=\operatorname{supp}\tau$。由于 $\sigma>0$，每个 Kraus 算子 $E_i$ 都满足
$PE_i=E_i$，所以所有 $\mathcal N$ 输出都在 $P\mathcal B(K)P$ 中，且
$\mathcal N^*(PXP)=\mathcal N^*(X)$。原始 Petz 映射满足

$$
\operatorname{Tr}\mathcal P_{\sigma,\mathcal N}(X)=\operatorname{Tr}(PX),\qquad
 \mathcal P_{\sigma,\mathcal N}(\tau)=\sigma.
$$

因此它在可达支撑角代数 $P\mathcal B(K)P$ 上是 CPTP。以下四个结构定律统一在这些角代数上陈述：参考态在自身支撑上忠实，$\Gamma$ 可逆。

### 定理 2.1（反向的四个一致性定律）

<a id="thm-c122-four-laws"></a>

设 $\mathcal N:(H,\sigma)\to(K,\tau)$、
$\mathcal M:(K,\tau)\to(L,\omega)$ 保持所标定的参考态，则

<a id="eq-c122-involution"></a>

$$
\begin{aligned}
\mathcal P_{\tau,\mathcal P_{\sigma,\mathcal N}}
       &=\mathcal N,
\end{aligned}
\tag{6}
$$

<a id="eq-c122-sequence"></a>

$$
\begin{aligned}
\mathcal P_{\sigma,\mathcal M\mathcal N}
       &=\mathcal P_{\sigma,\mathcal N}\mathcal P_{\tau,\mathcal M},
\end{aligned}
\tag{7}
$$

<a id="eq-c122-parallel"></a>

$$
\begin{aligned}
\mathcal P_{\sigma_1\otimes\sigma_2,\mathcal N_1\otimes\mathcal N_2}
       &=\mathcal P_{\sigma_1,\mathcal N_1}\otimes
         \mathcal P_{\sigma_2,\mathcal N_2},
\end{aligned}
\tag{8}
$$

<a id="eq-c122-unitary-reverse"></a>

$$
\begin{aligned}
\mathcal P_{\sigma,\operatorname{Ad}_U}&=\operatorname{Ad}_{U^*}
       \quad\text{（$U$ 为酉）}.
\end{aligned}
\tag{9}
$$

**证明。**
每个 $\Gamma_\sigma$ 对 Hilbert–Schmidt 配对自伴随，因此

$$
\mathcal P_{\sigma,\mathcal N}^*
       =\Gamma_\tau^{-1}\mathcal N\Gamma_\sigma.
$$

再次反向即得
$\Gamma_\tau\mathcal P_{\sigma,\mathcal N}^*\Gamma_\sigma^{-1}
=\mathcal N$，证明第一式。第二式则直接来自

$$
\Gamma_\sigma\mathcal N^*\mathcal M^*\Gamma_\omega^{-1}
 =(\Gamma_\sigma\mathcal N^*\Gamma_\tau^{-1})
  (\Gamma_\tau\mathcal M^*\Gamma_\omega^{-1}).
$$

第三式使用 $\Gamma_{\sigma_1\otimes\sigma_2}
=\Gamma_{\sigma_1}\otimes\Gamma_{\sigma_2}$、张量积的伴随与支撑逆分解。
最后，$\tau=U\sigma U^*$ 给出
$\tau^{-1/2}=U\sigma^{-1/2}U^*$，代入 Petz 公式后所有权重抵消，只余 $U^*(\cdot)U$。

这些等式说明：一条边的反向与顺序、并行和再次反向相容。
式~[(6)](#eq-c122-involution) 说的是*反向规则再反一次得到原规则*；它没有把有损通道变成可逆通道。例如完全退相干满足自己的反向仍是自身，但往返仍会丢失非对角元。2026 年关于四项一致性刻画 Petz 反向的全局唯一性结果由前章单独引述 [5](#ref-retrodiction2026)；本定理仅直接验证该公式确实满足四项要求。

### 说明 2.2（支撑外补全不会自动保留全部结构）

可选一个全空间 CPTP 延伸

$$
\overline{\mathcal P}_{\sigma,\mathcal N}(X)
 =\mathcal P_{\sigma,\mathcal N}(X)+\operatorname{Tr}[(I-P)X]\sigma.
$$

它不改变任何 $\mathcal N$ 输出的恢复结果。原始映射的顺序反向在支撑逆写法下仍成立，因为中间出现的 $P$ 被 $\mathcal N^*$ 吸收。
若每一步均用各自参考态作上述补全，则顺序反向甚至在全环境空间上成立：末端支撑外的额外项经中间参考态返回 $\sigma$。

但这种全空间补全一般不保持并行。若第一个输入在合法支撑内、第二个输入在其支撑外，两个补全的张量积仍保留第一个因子的恢复结果；联合补全却把整份输入送到 $\sigma_1\otimes\sigma_2$。
所以四个定律的统一作用域是可达支撑角代数；任意环境填充不是这些定律所唯一决定的内容。

### 命题 2.3（零泄漏时，显式反向恢复全部来源）

<a id="prop-c122-exact-source"></a>

若 $\mathcal N$ 的补通道为常量替代，则对每个忠实参考态 $\sigma$ 都有

$$
\mathcal P_{\sigma,\mathcal N}\mathcal N=\operatorname{id}_H.
$$

在可达输出支撑上，该反向不依赖 $\sigma$。

**证明。**
常量补通道的矩阵元给出 $E_i^*E_j=\alpha_{ij}I$。
对正矩阵 $\alpha$ 对角化并旋转 Kraus 表示，可写成

$$
\mathcal N(X)=\sum_a\lambda_a U_aXU_a^*,\qquad
 U_a^*U_b=\delta_{ab}I,\qquad
 \lambda_a>0,\quad\sum_a\lambda_a=1.
$$

于是 $\tau=\sum_a\lambda_a U_a\sigma U_a^*$，正交支撑上的逆为
$\tau^{-1/2}=\sum_a\lambda_a^{-1/2}U_a\sigma^{-1/2}U_a^*$。
Petz 的第 $a$ 个 Kraus 算子因而恰为

$$
\sigma^{1/2}\sqrt{\lambda_a}\,U_a^*\tau^{-1/2}=U_a^*.
$$

故 $\mathcal P(X)=\sum_aU_a^*XU_a$，与 $\sigma$ 无关；与 $\mathcal N$ 复合得到 $\sum_a\lambda_a X=X$。这也保持任意参考，因为复合是整个矩阵代数上的恒等映射。

**白话。**先给每个有限来源一份内部参考，再沿已有通道把参考送出去，反向规则就被这两端的配对固定下来。两条路接起来，反向会按相反顺序接起来；两份独立内容并排放着，反向也能并排做。只有当遗漏的一边完全不区分输入时，这条明确的反向才把所有未知内容都原样找回。

<a id="section-3"></a>

## 3. 把存在性变成显式回接：保真度与全参考误差

<a id="sec-c122-explicit-guarantees"></a>

### 3.1 先固定保真度的平方约定

### 定义 3.1（平方纠缠保真度）

令 $\Psi_\rho=\lvert \psi_\rho\rangle\langle \psi_\rho\rvert$ 为 $\rho$ 的任一纯化。
对源到自身的通道 $\mathcal T$，定义

<a id="eq-c122-squared-fe"></a>

$$
F_e(\rho,\mathcal T)
 =\langle\psi_\rho|(\mathcal T\otimes\operatorname{id})(\Psi_\rho)|\psi_\rho\rangle
 =\sum_a|\operatorname{Tr}(\rho K_a)|^2,
\tag{10}
$$

其中 $K_a$ 为 $\mathcal T$ 的任一 Kraus 表示。
它是 C121 所用根保真度的*平方*，取值在 $[0,1]$。
diamond 距离仍采用不除二的约定，最大为 $2$。

式~[(10)](#eq-c122-squared-fe) 的第二个等号只需展开 Kraus 作用，并使用
$\langle\psi_\rho|(K_a\otimes I)|\psi_\rho\rangle=\operatorname{Tr}(\rho K_a)$。
下面的定理固定*已声明的参考态* $\sigma$，并未把未知输入偷换为恢复器的参数。

### 定理 3.2（单参考态 Barnum–Knill 界）

<a id="thm-c122-barnum-knill"></a>

对任意忠实 $\sigma$、通道 $\mathcal N$ 及任意 CPTP 恢复 $\mathcal R$，

<a id="eq-c122-barnum-knill"></a>

$$
F_e(\sigma,\mathcal P_{\sigma,\mathcal N}\mathcal N)
 \ge F_e(\sigma,\mathcal R\mathcal N)^2.
\tag{11}
$$

**证明。**
先把输出限制到 $\tau=\mathcal N(\sigma)$ 的支撑，故 $\sigma,\tau$ 都可逆。
取 $E_j$、$R_i$ 为噪声和任意恢复的 Kraus 算子。对有限矩阵
$X_{ij}=\operatorname{Tr}(\sigma R_iE_j)$ 作奇异值分解；分别酉旋转这两组 Kraus、必要时补零，可令 $X_{ij}=0$ 对所有 $i\ne j$ 成立。
这些旋转不改变 $\mathcal N,\mathcal R$ 或 Petz 通道。

定义辅助算子及 CP 映射

$$
B_i^*=\sigma^{-1/2}R_i\tau^{1/2},\qquad
 \mathcal B(X)=\sum_iB_iXB_i^*.
$$

于是 $R_i=\sigma^{1/2}B_i^*\tau^{-1/2}$，并由恢复的迹保持性得到

$$
\mathcal B(\sigma)
 =\tau^{1/2}\Bigl(\sum_iR_i^*R_i\Bigr)\tau^{1/2}=\tau.
$$

辅助 $\mathcal B$ 不必是迹保持的；这里只使用这一等式。
令

$$
Y_i=\tau^{-1/4}B_i\sigma^{3/4},\qquad
 Z_i=\tau^{-1/4}E_i\sigma^{3/4},\qquad
 a_i=\|Y_i\|_2^2,\quad b_i=\|Z_i\|_2^2.
$$

由迹的循环性及 $X$ 的对角化，

<a id="eq-c122-bk-two-schwarz"></a>

$$
\begin{aligned}
F_e(\sigma,\mathcal R\mathcal N)
 &=\sum_i|\operatorname{Tr}(Y_i^*Z_i)|^2
 \le\sum_i a_ib_i
 \le\sqrt{\sum_i a_i^2}\sqrt{\sum_i b_i^2}.
\end{aligned}
\tag{12}
$$

两次不等式分别是矩阵和向量的 Cauchy–Schwarz。

第一因子至多为 $1$。确实，$a_i=\operatorname{Tr}(\sigma R_iB_i)$，而对任意 $C$ 有
$|\operatorname{Tr}(\sigma C)|^2\le\operatorname{Tr}(C\sigma C^*)$，所以

$$
\begin{aligned}
\sum_i a_i^2
 &\le\sum_i\operatorname{Tr}(R_iB_i\sigma B_i^*R_i^*)\\
 &\le\sum_{i,j}\operatorname{Tr}(R_iB_j\sigma B_j^*R_i^*)
 =\operatorname{Tr}\mathcal R(\mathcal B(\sigma))=\operatorname{Tr}\tau=1.
\end{aligned}
$$

第二因子可以加入非负交叉项：

$$
\begin{aligned}
\sum_i b_i^2
 &\le\sum_{i,j}|\operatorname{Tr}(Z_i^*Z_j)|^2\\
 &=\sum_{i,j}|\operatorname{Tr}(\sigma^{3/2}E_i^*\tau^{-1/2}E_j)|^2
 =F_e(\sigma,\mathcal P_{\sigma,\mathcal N}\mathcal N).
\end{aligned}
$$

最后一步使用 Petz 的 Kraus 算子 $\sigma^{1/2}E_i^*\tau^{-1/2}$。
代回式~[(12)](#eq-c122-bk-two-schwarz) 并平方，得到结论。

这是已知近最优恢复定理的单状态形式 [6](#ref-barnum2026)。
原论文的多状态平均证明有一处错误，作者在 2026 年 1 月更新的 arXiv v2 中修复；新版末尾明确说明原证明已覆盖单状态纠缠保真度。本章使用上述独立的单状态证明，既不依赖旧的多状态推导，也不把根保真度和平方纠缠保真度混用。

**白话。**参考态是我们先选定的一把尺子。只要有任何修法能很好地保住这把尺子与它的参考记录之间的纠缠，公式直接给出的 Petz 修法就不会差太多。比较用的最优修法可以只存在于证明里；真正定义 Petz 修法时，只需要已有通道和那份已声明的参考。

### 3.2 均匀参考把残余变成双交换子的平方和

现在固定 $H=\mathbb C^d$、$d\ge2$ 及 $\pi=I_H/d$。
令 $B_N=\mathcal N(I_H)$，并记 $\mathcal T=\mathcal P_{\pi,\mathcal N}\mathcal N$。
支撑逆公式消去 $d$ 后，$\mathcal T$ 的 Kraus 算子为

<a id="eq-c122-paired-kraus"></a>

$$
K_{ij}=E_i^*B_N^{-1/2}E_j,
 \qquad K_{ji}=K_{ij}^*.
\tag{13}
$$

它是 CPTP，且保持 $\pi$，所以也是保单位的。

### 定义 3.3（可直接计算的回接缺陷）

$$
\beta_{ij}=\frac{\operatorname{Tr} K_{ij}}d,\qquad
 \Delta_{ij}=K_{ij}-\beta_{ij}I_H,\qquad
 D_{\mathrm K}=\sum_{i,j}\Delta_{ij}^*\Delta_{ij}\succeq0,
 \qquad p=F_e(\pi,\mathcal T)=\sum_{i,j}|\beta_{ij}|^2.
$$

### 定理 3.4（残余恒等式与固定代数）

<a id="thm-c122-dirichlet-defect"></a>

存在一组去迹 Hermitian 算子 $L_a$，满足 $D_{\mathrm K}=\sum_aL_a^2$，且

<a id="eq-c122-double-commutator"></a>

$$
\mathcal T(X)-X
 =\sum_aL_aXL_a-\tfrac12(D_{\mathrm K}X+XD_{\mathrm K})
 =-\tfrac12\sum_a[L_a,[L_a,X]].
\tag{14}
$$

特别地

<a id="eq-c122-dirichlet-energy"></a>

$$
\operatorname{Tr} D_{\mathrm K}=d(1-p),\qquad
 \operatorname{Tr}[X^*(I-\mathcal T)(X)]
 =\tfrac12\sum_a\|[L_a,X]\|_2^2,
\tag{15}
$$

并且

<a id="eq-c122-fixed-algebra"></a>

$$
\operatorname{Fix}(\mathcal T)
 =\{X:[L_a,X]=0\ \forall a\},
\tag{16}
$$

故其固定空间是一个有限维 $C^*$ 代数。

**证明。**
对于每对 $i<j$，把 $K_{ij},K_{ji}$ 酉混合为
$(K_{ij}+K_{ji})/\sqrt2$ 与 $i(K_{ij}-K_{ji})/\sqrt2$；再保留对角 $K_{ii}$，得到全为 Hermitian 的 Kraus 表示 $H_a$。
令 $\alpha_a=\operatorname{Tr} H_a/d\in\mathbb R$、$L_a=H_a-\alpha_aI$。
Kraus 酉混合保持 $\sum_aL_a^2=D_{\mathrm K}$ 及 $\sum_a\alpha_a^2=p$。
迹保持条件 $\sum_aH_a^2=I$ 展开为

$$
pI+2\sum_a\alpha_aL_a+D_{\mathrm K}=I.
$$

再展开 $\sum_aH_aXH_a-X$，把上式中的一次项代入，恰得式~[(14)](#eq-c122-double-commutator)。
取迹得到 $\operatorname{Tr} D_{\mathrm K}=d(1-p)$，因为所有 $L_a$ 去迹。
每个 $X\mapsto[L_a,X]$ 在 Hilbert–Schmidt 空间上自伴随，所以对双交换子取二次型得到式~[(15)](#eq-c122-dirichlet-energy)。
若 $\mathcal T(X)=X$，每个非负平方项都为零；反之，全部交换子为零时式~[(14)](#eq-c122-double-commutator) 给出 $\mathcal T(X)=X$。交换子代数封闭于乘法与伴随，得到最后结论。

这给出 ``关系的关系'' 的一个精确有限实例：$[L_a,X]$ 比较记录与残余，双交换子把这些比较重新汇总为往返损失。没有把这条算子恒等式解释为已经推导了物理时间；一般非均匀参考的固定*状态*空间也不能直接当作通常乘法下的代数，前后两种表示须按权重区分。

### 3.3 全参考 diamond 界不必再损失一个平方根

### 定理 3.5（显式缺陷的全参考上界）

<a id="thm-c122-diamond-defect"></a>

对上述均匀参考回接有

<a id="eq-c122-diamond-defect"></a>

$$
2(1-p)\le\|\mathcal T-\operatorname{id}_H\|_\diamond
 \le\min\{2,2\|D_{\mathrm K}\|_\infty\}
 \le\min\{2,2(d-1)(1-p)\}.
\tag{17}
$$

特别地，$d=2$ 时

<a id="eq-c122-qubit-exact-diamond"></a>

$$
\|\mathcal T-\operatorname{id}_2\|_\diamond=2(1-F_e(\pi,\mathcal T)).
\tag{18}
$$

**证明。**
令 $\Lambda(X)=\sum_aL_aXL_a$。对任意参考 $Q$ 和联合密度矩阵 $\rho$，
$(\Lambda\otimes\operatorname{id}_Q)(\rho)\succeq0$，所以其迹范数为
$\operatorname{Tr}[(D_{\mathrm K}\otimes I_Q)\rho]\le\|D_{\mathrm K}\|_\infty$。
另一方面 Schatten 乘积不等式给出

$$
\tfrac12\|(D_{\mathrm K}\otimes I_Q)\rho+\rho(D_{\mathrm K}\otimes I_Q)\|_1
 \le\|D_{\mathrm K}\|_\infty.
$$

对式~[(14)](#eq-c122-double-commutator) 使用三角不等式，就在*任意参考*上得到 $2\|D_{\mathrm K}\|_\infty$。

若 Hermitian $L$ 去迹，其特征值为 $\lambda_1,\ldots,\lambda_d$，则对任意 $r$，

$$
\lambda_r^2=\left(\sum_{s\ne r}\lambda_s\right)^2
 \le(d-1)\sum_{s\ne r}\lambda_s^2,
 \quad\text{故}\quad
 L^2\preceq\frac{d-1}{d}\operatorname{Tr}(L^2)I.
$$

对 $L_a$ 相加并用 $\operatorname{Tr} D_{\mathrm K}=d(1-p)$，得
$D_{\mathrm K}\preceq(d-1)(1-p)I$。
最后，用最大纠缠输入 $\Psi_\pi$ 及二元效果 $\Psi_\pi$ 检验输出，其成功概率差为 $1-p$，因此迹距离至少为 $2(1-p)$。$d=2$ 时上下界相等。

### 定理 3.6（从任意统一恢复到固定公式的统一恢复）

<a id="thm-c122-explicit-petz-linear"></a>

若存在 CPTP $\mathcal R$ 满足
$\|\mathcal R\mathcal N-\operatorname{id}_H\|_\diamond\le e$，$0\le e\le2$，则*预先固定*的 $\pi$-Petz 回接满足

<a id="eq-c122-explicit-linear-error"></a>

$$
\boxed{\quad
 \|\mathcal P_{\pi,\mathcal N}\mathcal N-\operatorname{id}_H\|_\diamond
 \le\min\{2,\,2(d-1)(e-e^2/4)\}.
 \quad}
\tag{19}
$$

公式不使用 $\mathcal R$，不依赖未知输入，且没有输出维数因子。

**证明。**
在最大纠缠输入上测试理想态投影，diamond 假设直接给出
$F_e(\pi,\mathcal R\mathcal N)\ge1-e/2$。
定理~[3.2](#thm-c122-barnum-knill) 因而给出
$p\ge(1-e/2)^2$。把 $1-p\le e-e^2/4$ 代入
定理~[3.5](#thm-c122-diamond-defect) 即得。

上述线性界来自均匀参考回接的 Hermitian Kraus 结构。一般通道的小平均保真度损失并不能直接得到同样的线性 diamond 界；相干残余可能产生平方根尺度。本节把结构条件及有限证明全部写出，不宣称这些常数最优或具有首创性。

Ng–Mandayam 的已知近最优界也依赖源维数：在其*最坏纯态平方保真度损失*约定下，

$$
\eta_P\le\eta_{\rm opt}
 \frac{(d+1)-\eta_{\rm opt}}{1+(d-1)\eta_{\rm opt}}.
$$

这是另一个误差指标，不能直接把它称为含纠缠参考的 diamond 界 [7](#ref-ng2010)。本节的式~[(19)](#eq-c122-explicit-linear-error) 通过单参考态定理与显式双交换子结构，单独证明了全参考结论。

**白话。**显式回接剩下的错误不是一个任意扭转。对均匀内部参考，它能够写成一组对称残余，每一项都问 ``这份内容与这项残余是否交换''。把不交换的平方加起来，就能直接限制最坏输入连同任何参考的误差。因此我们不只知道有办法找回来，还得到一条固定公式，以及这条公式会错多少的有限上界。

### 3.4 直接接回 C121 的有限二元证书

记 $\widehat{\mathcal N}$ 为同一等距实现的补通道。
先保留 C121 证明中的根保真度信息，不急于把它换成迹距离。

### 引理 3.7（固定参考态的补端到恢复桥梁）

<a id="lem-c122-decoupling-fe"></a>

若某个环境态 $\xi$ 满足
$\|\widehat{\mathcal N}-\mathcal S_\xi\|_\diamond\le\delta\le2$，则存在 CPTP $\mathcal R$，使

$$
F_e(\pi,\mathcal R\mathcal N)\ge(1-\delta/2)^2.
$$

**证明。**
记最大纠缠向量为 $\Omega_d$，实际等距为 $V:H\to E\otimes K$，并取 $\xi$ 的纯化 $\xi^{1/2}\in E\otimes F$。
两个单位纯化为

$$
v=(V\otimes I_H)\Omega_d,\qquad
 j=\Omega_d\otimes\xi^{1/2},
$$

其中 $j$ 的因子按 ``环境–参考'' 与 ``源–辅助'' 重排。
它们在环境–参考上的约化态 $a,b$ 满足
$\|a-b\|_1\le\delta$，且 $b=\xi\otimes\pi$。

先核两个有限矩阵事实。根保真度
$f(a,b)=\|\sqrt a\sqrt b\|_1$ 满足 $f(a,b)\ge1-\|a-b\|_1/2$：当 $a>0$ 时取

$$
G=a^{-1/2}(a^{1/2}ba^{1/2})^{1/2}a^{-1/2},\qquad GaG=b.
$$

在 $G$ 特征基中，测量概率满足 $q_i=\lambda_i^2p_i$，故
$\sum_i\sqrt{p_iq_i}=f(a,b)$，而
$1-\sum_i\sqrt{p_iq_i}\le\sum_i|p_i-q_i|/2\le\|a-b\|_1/2$。
奇异 $a$ 用满秩混合逼近。
其次，把 $v,j$ 写成纯化系数矩阵 $X,Y$，迹范数对偶与极分解给出

$$
\max_{\|A:K\to H\otimes F\|\le1}
 \operatorname{Re}\langle j,(I\otimes A)v\rangle
 =\|Y^*X\|_1=f(a,b).
$$

因而可选择达到最大值 $f(a,b)$ 的固定收缩 $A$，其重叠至少为 $1-\delta/2$。

任取固定源态 $\rho_0$，明确补成

$$
\mathcal R(X)=\operatorname{Tr}_F(AXA^*)
 +\operatorname{Tr}[(I_K-A^*A)X]\rho_0.
$$

两项为 CP，迹之和为 $\operatorname{Tr} X$。第一项的恢复输出在理想投影 $\Psi_\pi$ 上的概率，是对应环境–辅助向量的范数平方，至少为它与单位向量 $\xi^{1/2}$ 重叠的平方，即至少 $f(a,b)^2$；第二项只增加非负贡献。
故 $F_e(\pi,\mathcal R\mathcal N)\ge(1-\delta/2)^2$。
该 $\mathcal R$ 只按已固定的 $\pi$ 选择，不依赖以后实际输入。最终 Petz 的全参考保证由其显式缺陷定理给出，无需调用最坏态 minimax 对偶。

### 推论 3.8（补端误差直接给出显式全参考恢复）

<a id="cor-c122-decoupling-petz"></a>

在引理~[3.7](#lem-c122-decoupling-fe) 条件下，

<a id="eq-c122-decoupling-petz"></a>

$$
\boxed{\quad
 \|\mathcal P_{\pi,\mathcal N}\mathcal N-\operatorname{id}_H\|_\diamond
 \le\min\{2,\,2(d-1)[1-(1-\delta/2)^4]\}
 \le\min\{2,\,4(d-1)\delta\}.
 \quad}
\tag{20}
$$

**证明。**
引理给出一个 $\mathcal R$ 的平方纠缠保真度下界；Barnum–Knill 再平方一次，所以

$$
F_e(\pi,\mathcal P_{\pi,\mathcal N}\mathcal N)\ge(1-\delta/2)^4.
$$

应用定理~[3.5](#thm-c122-diamond-defect)。最后使用
$1-(1-x)^4\le4x$，$x=\delta/2\in[0,1]$。

### 引理 3.9（实际二元判别的完整有限证书）

<a id="lem-c122-binary-certificate"></a>

给定同一来源基 $e_1,\ldots,e_d$，对所有基对 $e_r,e_s$，以及 $d-1$ 对
$(e_1+e_j)/\sqrt2,(e_1-e_j)/\sqrt2$，各供应一个实际二元效果。
若每对的两个条件错误均不超过 $0\le\varepsilon\le1/2$，则存在内部环境态 $\xi$，使

<a id="eq-c122-binary-delta"></a>

$$
\|\widehat{\mathcal N}-\mathcal S_\xi\|_\diamond
 \le\delta:=\min\{2,\,2(d+1)\sqrt{\varepsilon(1-\varepsilon)}\}.
\tag{21}
$$

**证明。**
先看任意被比较的 $u,v$。设实际效果 $0\le F\le I_K$ 的错误为
$e_u=1-\operatorname{Tr}(F\mathcal N(P_u))$、$e_v=\operatorname{Tr}(F\mathcal N(P_v))$，其中 $P_u=\lvert u\rangle\langle u\rvert$。
把等距输出按可见端与环境排列，记 $v_u=Vu,v_v=Vv$。环境迹范数的酉对偶给出

$$
\|\widehat{\mathcal N}(\lvert u\rangle\langle v\rvert)\|_1
 =\max_{U_E\text{ 酉}}|\langle v_v,(I_K\otimes U_E)v_u\rangle|.
$$

在内积中插入 $F+(I-F)$，各项分别以 $F^{1/2}$ 和 $(I-F)^{1/2}$ 作用在两个向量上，再用 Cauchy–Schwarz。环境酉与这些效果交换，故

<a id="eq-c122-actual-binary-cross"></a>

$$
\|\widehat{\mathcal N}(\lvert u\rangle\langle v\rvert)\|_1
 \le\sqrt{(1-e_u)e_v}+\sqrt{e_u(1-e_v)}.
\tag{22}
$$

若 $e_u=\sin^2\alpha,e_v=\sin^2\beta$，右侧为 $\sin(\alpha+\beta)$。
在 $e_u,e_v\le\varepsilon\le1/2$ 下，$\alpha,\beta\le\arcsin\sqrt\varepsilon\le\pi/4$，所以每个交叉范数都不超过
$\eta=2\sqrt{\varepsilon(1-\varepsilon)}$。

记 $R_{rs}=\widehat{\mathcal N}(\lvert e_r\rangle\langle e_s\rvert)$。基对测试给出
$\|R_{rs}\|_1\le\eta$，$r\ne s$。对相加、相减对 $u=(e_1+e_j)/\sqrt2$、$v=(e_1-e_j)/\sqrt2$，令
$C_j=\widehat{\mathcal N}(\lvert u\rangle\langle v\rvert)$，则

$$
C_j=\tfrac12(R_{11}-R_{1j}+R_{j1}-R_{jj}),\qquad
 C_j+C_j^*=R_{11}-R_{jj}.
$$

故 $\|R_{jj}-R_{11}\|_1\le2\eta$。取 $\xi=R_{11}$。

最后取任意参考 $Q$ 和联合态
$\rho=\sum_{r,s}\lvert e_r\rangle\langle e_s\rvert\otimes\rho_{rs}$，令 $p_r=\operatorname{Tr}\rho_{rr}$。
把它纯化为 $\sum_re_r\otimes w_r$，其中 $w_r\in Q\otimes A$，则
$\rho_{rs}=\operatorname{Tr}_A\lvert w_r\rangle\langle w_s\rvert$、$\|w_r\|^2=p_r$。再次用迹范数酉对偶，

$$
\|\rho_{rs}\|_1
 =\max_{U_Q\text{ 酉}}|\langle w_s,(U_Q\otimes I_A)w_r\rangle|
 \le\sqrt{p_rp_s}.
$$

逐块展开通道差并取迹范数，便得到

$$
\|[(\widehat{\mathcal N}-\mathcal S_\xi)\otimes\operatorname{id}_Q](\rho)\|_1
 \le2\eta\sum_rp_r+\eta\sum_{r\ne s}\sqrt{p_rp_s}
 \le(d+1)\eta.
$$

这里 $\sum_rp_r=1$、$(\sum_r\sqrt{p_r})^2\le d$，从未要求参考与来源独立。
对全部有限参考输入态取上确界即得 diamond 上界，再用通道差的普遍界 $2$。

代入式~[(20)](#eq-c122-decoupling-petz)，得到特别直观的简界

<a id="eq-c122-binary-explicit"></a>

$$
\|\mathcal P_{\pi,\mathcal N}\mathcal N-\operatorname{id}_H\|_\diamond
 \le\min\{2,\,8(d^2-1)\sqrt{\varepsilon(1-\varepsilon)}\}.
\tag{23}
$$

使用 C121 非均匀相干图的谱证书时，只需把其更小的 $\delta$ 直接代入同一个公式。
式~[(23)](#eq-c122-binary-explicit) 是本证明提供的充分保证；其 $\sqrt\varepsilon$ 指数与维数常数不宣称最优。它与 C121 的维数无关 $\sqrt\delta$ 信息–扰动界不矛盾：此处明确使用固定源维数及特殊的 Petz 回接结构。

### 说明 3.10（何谓显式，何谓仍需供应）

Petz 公式只使用 $\sigma,\mathcal N,\mathcal N^*$ 及有限支撑谱运算；它不要求先知道未知输入，也不要求先求出某个最优恢复器。
但这不保证观察者的当前门菜单已经供应这些运算，或已供应通道的精确矩阵。特别是单独的 $\tau^{-1/2}$ 夹乘通常不是迹保持物理过程；合法的是完整的 CPTP 组合及其实现。
有限判别证书负责证明误差界，通道标定与电路供应负责执行公式，两种责任不能互相替代。

**白话。**先在这一端做有限次 ``这两个还能分开吗'' 的比较。若基态对和相加、相减对都分得足够清楚，另一端就不能暗中保留太多差别。接着不用为每个未知输入重新挑修法：固定均匀内部参考，用同一条加权反向公式把内容接回来。残余平方和把这套明确修法的误差压住，连它与其他内部记录的纠缠也一起计算。

<a id="section-4"></a>

## 4. 显式反向的几何：加权收缩、三维读口与稳定关系

<a id="sec-c122-weighted-geometry"></a>

本节固定一个已给定的内部参考态 $\sigma>0$、一个 CPTP 过程 $N$，并记 $\tau=N(\sigma)$。输出空间始终限制到 $\operatorname{supp}\tau$，故 $\tau>0$。这个限制保留整个前向过程：每个 $X\ge0$ 都满足 $X\le c\sigma$，因而 $0\le N(X)\le c\tau$；再由正矩阵线性生成全部矩阵，得到所有输出都在该支持内。参考态限定了比较的权重，不承担读取全部 $\Omega$ 的任务。

### 4.1 二元互易怎样成为一个正收缩

### 定义 4.1（加权比较空间）

定义正的 Hilbert–Schmidt 超算子

$$
\Gamma_\sigma(X)=\sigma^{1/2}X\sigma^{1/2},\qquad
 \Gamma_\sigma^t(X)=\sigma^{t/2}X\sigma^{t/2},
$$

以及矩阵之间的内积

$$
g_\sigma(X,Y)=\operatorname{Tr}\bigl(X^*\Gamma_\sigma^{-1}(Y)\bigr),
 \qquad \|X\|_\sigma^2=g_\sigma(X,X).
$$

令

<a id="eq-c122-geometry-operators"></a>

$$
P=\Gamma_\sigma N^*\Gamma_\tau^{-1},\qquad
 S=PN,\qquad
 T=\Gamma_\tau^{-1/2}N\Gamma_\sigma^{1/2}.
\tag{24}
$$

$N^*$ 表示通常迹配对的伴随，$T^\dagger$ 表示 Hilbert–Schmidt 空间的伴随。$P$ 是指定参考态下的 Petz 反向，$S$ 是一次前向后接同一反向的过程。

内积的双变量互易式为

<a id="eq-c122-weighted-reciprocity"></a>

$$
g_\tau(NX,Y)=g_\sigma(X,PY).
\tag{25}
$$

因此固定这个非退化配对后，$P$ 被唯一确定。它是量子通道：式~[(24)](#eq-c122-geometry-operators) 的三个因子完全正，且

$$
\operatorname{Tr} P(Y)=\operatorname{Tr}\bigl(\tau\tau^{-1/2}Y\tau^{-1/2}\bigr)=\operatorname{Tr} Y,
 \qquad P(\tau)=\sigma^{1/2}N^*(I)\sigma^{1/2}=\sigma.
$$

故 $S$ 也是通道，并满足 $S(\sigma)=\sigma$。

### 定理 4.2（加权收缩及非负回接谱）

<a id="thm-c122-weighted-contraction"></a>

在上述条件下，

<a id="eq-c122-positive-contraction"></a>

$$
\Gamma_\sigma^{-1/2}S\Gamma_\sigma^{1/2}=T^\dagger T,
 \qquad 0\le T^\dagger T\le I.
\tag{26}
$$

因此 $N$ 从 $g_\sigma$ 到 $g_\tau$ 收缩，$S$ 对 $g_\sigma$ 自伴且为正收缩，其全部特征值属于 $[0,1]$。

**证明。**
各 $\Gamma$ 对 Hilbert–Schmidt 内积自伴，故

$$
T^\dagger T=\Gamma_\sigma^{1/2}N^*\Gamma_\tau^{-1}N\Gamma_\sigma^{1/2}
 =\Gamma_\sigma^{-1/2}S\Gamma_\sigma^{1/2}\ge0.
$$

还需证明特征值不超过 $1$。$S$ 与这个正自伴算子相似，所以有非负实谱并可对角化。$S$ 保持取伴随；一个非零特征向量的 Hermitian 实部或虚部至少有一个非零，且具有同一实特征值。对任意 Hermitian $X=X_+-X_-$，正性与保迹性给出

$$
\|S(X)\|_1\le\operatorname{Tr} S(X_+)+\operatorname{Tr} S(X_-)=\|X\|_1.
$$

若 $S(X)=\lambda X$，便得 $\lambda\le1$。于是 $T^\dagger T\le I$，将 $x=\Gamma_\sigma^{-1/2}X$ 代入即可得到 $\|N(X)\|_\tau\le\|X\|_\sigma$。自伴性也可直接由

$$
g_\sigma(X,SY)=g_\tau(NX,NY)=g_\sigma(SX,Y)
$$

看出。

这里的比较属于 Petz 单调度量族，对应函数 $f_{\rm met}(t)=\sqrt t$，其 Morozova–Chentsov 系数为 $c(x,y)=1/\sqrt{xy}$；相应散度是 $\chi^2_{1/2}$~ [8](#ref-petz1996)、[9](#ref-hansen2011)。以上证明没有调用单调度量分类定理。单调性本身容许一族不同度量，平方根配对仍须由本候选的互易规定或另外明列的结构条件确定。最新反向唯一性工作采用所有参考和通道上的接续、并行、双重反向及酉逆条件来确定 Petz 规则~ [5](#ref-retrodiction2026)；这里证明的是采用该规则后的几何后果。

### 4.2 比较损失是一个 Gram 余量

令

$$
D=I-T^\dagger T,\qquad
 K_\sigma(X,Y)=g_\sigma(X,Y)-g_\tau(NX,NY).
$$

对任意有限组 $X_1,\ldots,X_m$，取 $x_i=\Gamma_\sigma^{-1/2}X_i$，有

<a id="eq-c122-defect-gram"></a>

$$
K_\sigma(X_i,X_j)=\langle D^{1/2}x_i,D^{1/2}x_j\rangle_{\rm HS}.
\tag{27}
$$

故 $[K_\sigma(X_i,X_j)]\ge0$，特别地

$$
|K_\sigma(X,Y)|^2\le K_\sigma(X,X)K_\sigma(Y,Y).
$$

这把“某一关系损失多少”与“两个损失之间如何相容”连在了一起。

更大的线性结构是一个显式等距提升：

<a id="eq-c122-orthogonal-lift"></a>

$$
Vx=Tx\oplus D^{1/2}x,\qquad V^\dagger V=I.
\tag{28}
$$

若 $v_j$ 是 $T^\dagger T$ 的单位特征向量，写 $\lambda_j=\cos^2\theta_j$，$0\le\theta_j\le\pi/2$，则该方向分成长度 $\cos\theta_j$ 的输出部分与长度 $\sin\theta_j$ 的正交余量；回接后保留的系数为 $\lambda_j$。$\lambda_j=1$ 的方向没有损失，$\lambda_j=0$ 的方向没有保留。$\sqrt\sigma$ 是白化后的参考方向，满足

$$
T\sqrt\sigma=\sqrt\tau,\qquad
 T^\dagger\sqrt\tau=\sqrt\sigma.
$$

迹为零的扰动与 $\sqrt\sigma$ 正交，故参考归一化方向与真正的态变化可以分别讨论。

式~[(28)](#eq-c122-orthogonal-lift) 是*矩阵比较空间*的正交提升。$D$ 的 Hilbert 空间正性不等于它把正矩阵映为正矩阵。例如 $\sigma=I/2$、$N$ 为完全退相干时，$P=N$、$S=N$，而

$$
(\operatorname{id}-S)(\lvert +\rangle\langle +\rvert)=\tfrac12 X
$$

有正、负两个特征值。因此不能自动把余量 $D^{1/2}x$ 认作一份物理环境态，也不能把该等距提升直接认作可执行的量子门。

### 4.3 同一个二元读口下，两份扰动有严格的三维提升

### 定理 4.3（两扰动、一读口的实三维 Gram 实现）

<a id="thm-c122-three-dimensional-readout"></a>

取两份 Hermitian、迹为零的扰动 $X_1,X_2$，以及同一个实际二元效果 $0\le F\le I$。设

$$
F_0=F-\operatorname{Tr}(\tau F)I,\qquad
 \beta=\|\Gamma_\tau^{1/2}(F_0)\|_2>0,
 \qquad b=\Gamma_\tau^{1/2}(F_0)/\beta.
$$

记 $x_i=\Gamma_\sigma^{-1/2}X_i$ 与

$$
a_i=\langle b,Tx_i\rangle_{\rm HS}=\frac{\operatorname{Tr}(FN(X_i))}{\beta}.
$$

存在 $v_0,v_1,v_2\in\mathbb R^3$，使

$$
\|v_0\|=1,\qquad v_0\cdot v_i=a_i,\qquad
 v_i\cdot v_j=g_\sigma(X_i,X_j)\quad(i,j=1,2).
$$

即一条坐标轴保留实际读出，另外至多两个坐标补齐两份扰动的全部二元 Gram 关系。

**证明。**
Hermitian 矩阵的 Hilbert–Schmidt 内积为实数，故以下在实 Hilbert 空间中进行。$\|b\|=1$ 且 $T$ 收缩，因此对任意实数 $c_1,c_2$，

$$
\left(\sum_i c_i a_i\right)^2
 \le\left\|T\sum_i c_i x_i\right\|_2^2
 \le\left\|\sum_i c_i x_i\right\|_2^2.
$$

所以二阶矩阵 $H_{ij}=\langle x_i,x_j\rangle-a_i a_j$ 半正定。取两个实二维向量 $z_i$ 使 $z_i\cdot z_j=H_{ij}$，再置

$$
v_0=(1,0,0),\qquad v_i=(a_i,z_i).
$$

这给出所需实现；$H$ 的平方根或 Cholesky 分解均可构造 $z_i$。读出等式来自 $\Gamma_\tau^{1/2}$ 的自伴性以及 $\operatorname{Tr} N(X_i)=0$。若 $\beta=0$，则 $F$ 是常数效果，两份扰动的读出均为零，可取 $a_i=0$ 作同样提升。

等价地，下面的三阶矩阵必为正：

$$
\begin{pmatrix}
 1&a_1&a_2\\
 a_1&\|x_1\|_2^2&\langle x_1,x_2\rangle\\
 a_2&\langle x_2,x_1\rangle&\|x_2\|_2^2
 \end{pmatrix}\ge0.
$$

这项“三维”指两个扰动与*一个标量读口*的有限关系。若要同时保留一个二维输出空间和一个二维正交余量空间，三维一般不够：取 $T=cI$，$0<c<1$，以及正交的 $x_1,x_2$，则 $Tx_1,Tx_2$ 与 $D^{1/2}x_1,D^{1/2}x_2$ 在直和空间中构成四个非零正交方向。完整提升仍由式~[(28)](#eq-c122-orthogonal-lift) 承担。实际实验还须供应相应准备与 $F$；一个数学扰动可以写成合法态的差，并不自行把该准备加入观察者菜单。

### 4.4 同一显式反向的恢复误差，由比较损失直接控制

### 引理 4.4（加权范数支配迹范数）

对任意矩阵 $Y$，有 $\|Y\|_1\le\|Y\|_\sigma$。

**证明。**
由迹范数的酉变分式及 Cauchy–Schwarz，

$$
|\operatorname{Tr}(U^*Y)|
 \le\|\Gamma_\sigma^{1/2}(U)\|_2
       \|\Gamma_\sigma^{-1/2}(Y)\|_2.
$$

而对酉矩阵 $U$，

$$
\|\Gamma_\sigma^{1/2}(U)\|_2^2
 =\operatorname{Tr}(\sigma^{1/2}U^*\sigma^{1/2}U)
 \le\|\sigma^{1/2}\|_2\|U^*\sigma^{1/2}U\|_2=1.
$$

取 $U$ 的上确界即得结论。

### 定理 4.5（Petz 的显式比较损失界）

<a id="thm-c122-chi-square-recovery"></a>

对任意 $X$，

<a id="eq-c122-chi-loss"></a>

$$
\|X-SX\|_\sigma^2
 \le\|X\|_\sigma^2-\|NX\|_\tau^2.
\tag{29}
$$

定义

$$
\chi^2_{1/2}(\rho\Vert\sigma)
 =\|\rho-\sigma\|_\sigma^2
 =\operatorname{Tr}(\rho\sigma^{-1/2}\rho\sigma^{-1/2})-1.
$$

则对每个输入态 $\rho$，同一个 $P$ 满足

<a id="eq-c122-explicit-state-recovery"></a>

$$
\boxed{\quad
 \|\rho-PN(\rho)\|_1^2
 \le\chi^2_{1/2}(\rho\Vert\sigma)
   -\chi^2_{1/2}(N\rho\Vert\tau).
 \quad}
\tag{30}
$$

右端为零，当且仅当 $PN(\rho)=\rho$。

**证明。**
令 $x=\Gamma_\sigma^{-1/2}X$。由于 $0\le D\le I$，有 $D^2\le D$，故

$$
\|X-SX\|_\sigma^2=\langle x,D^2x\rangle
 \le\langle x,Dx\rangle
 =\|X\|_\sigma^2-\|NX\|_\tau^2.
$$

代入 $X=\rho-\sigma$，使用 $S\sigma=\sigma$ 和前引理，得到式~[(30)](#eq-c122-explicit-state-recovery)。若右端为零，则 $D^{1/2}x=0$，故 $SX=X$；反之，$SX=X$ 意味着 $Dx=0$，损失为零。

这个结论给出一个指定映射的误差，而非只证明某个恢复器存在。它使用 $\chi^2_{1/2}$ 损失，没有把一般相对熵近等式自动配给未经旋转的 Petz 映射。

同样的证明包含内部相关性。对任意内部参考 $Z$ 及其满秩参考态 $\omega$，直接计算得

$$
P_{\sigma\otimes\omega,\,N\otimes\operatorname{id}_Z}
   =P_{\sigma,N}\otimes\operatorname{id}_Z.
$$

因此式~[(30)](#eq-c122-explicit-state-recovery) 对*任意联合输入态*也成立，只需把基准换成 $\sigma\otimes\omega$；输入本身可纠缠。这里的界依赖该输入的比较损失。要把它变成一个覆盖全部输入的 diamond 数值，仍须取相应最坏值，或使用第~[3](#sec-c122-explicit-guarantees) 节的有限证书与维数估计。

### 4.5 固定关系、代数与一个自然的 Markov 半群

### 定理 4.6（稳定关系的两个侧面）

<a id="thm-c122-fixed-algebra"></a>

令 $\Phi=S^*$。则

$$
\mathfrak F=\{A:\Phi(A)=A\}
$$

是通常矩阵乘法下的含幺 $C^*$ 子代数，而

<a id="eq-c122-state-observable-fix"></a>

$$
\operatorname{Fix}S=\Gamma_\sigma(\mathfrak F).
\tag{31}
$$

后一个空间一般不是通常乘法下的代数，甚至不包含 $I$。并且

$$
S^n\longrightarrow E,
$$

其中 $E$ 是投影到 $\operatorname{Fix}S$ 的 $g_\sigma$ 正交投影，同时为 CPTP；$E^*$ 是保持 $\sigma$ 期望值的条件期望，值域为 $\mathfrak F$。

**证明。**
$\Phi$ 完全正且含幺，并满足 $\operatorname{Tr}(\sigma\Phi(A))=\operatorname{Tr}(\sigma A)$。若 $A\in\mathfrak F$，Schwarz 余量

$$
Q=\Phi(A^*A)-A^*A\ge0
$$

具有 $\operatorname{Tr}(\sigma Q)=0$。因 $\sigma>0$，必须 $Q=0$；对 $A^*$ 同理。为明确乘法结论，取 $\Phi(B)=W^*(B\otimes I)W$ 的等距表示，则

$$
Q=W^*(A^*\otimes I)(I-WW^*)(A\otimes I)W.
$$

零余量给出 $(A\otimes I)W=WA$，并由 $A^*$ 的零余量得到 $W^*(A\otimes I)=AW^*$。于是对所有 $B$，

$$
\Phi(AB)=A\Phi(B),\qquad \Phi(BA)=\Phi(B)A.
$$

固定点因而对乘法、伴随闭合，并含 $I$，得到 $C^*$ 子代数。

由式~[(24)](#eq-c122-geometry-operators) 可核对 $S\Gamma_\sigma=\Gamma_\sigma S^*$，这立即证明式~[(31)](#eq-c122-state-observable-fix)。再由定理~[4.2](#thm-c122-weighted-contraction) 的完整谱分解，$S^n$ 在特征值 $1$ 上保持不变，在全部 $\lambda<1$ 上趋零，故极限是相应加权正交投影。CPTP 性在有限维极限下保持。其伴随 $E^*$ 含幺、完全正、固定整个 $\mathfrak F$，并具有值域 $\mathfrak F$。对 $E^*$ 重用刚才的零余量证明，得到

$$
E^*(AXB)=A E^*(X)B\quad(A,B\in\mathfrak F),
$$

即条件期望的双模关系；$E(\sigma)=\sigma$ 给出参考态保持。

例如 $S(X)=\operatorname{Tr}(X)\sigma$ 的固定空间是 $\mathbb C\sigma$。若 $\sigma$ 满秩且非均匀，$\sigma^2$ 不与 $\sigma$ 成比例，所以这个状态固定空间不具通常乘法闭包；其可观测量固定代数却是 $\mathbb C I$。此外，固定空间是*所选参考态下*的恢复空间，不能直接改称 $N$ 在所有参考和恢复选择下的最大可恢复内容。取完全 $Z$ 退相干与 $\sigma=(I+rX)/2$，$0<r<1$，直接计算得

$$
S:\ (x,y,z)\longmapsto
       \bigl(r,0,\sqrt{1-r^2}\,z\bigr).
$$

此时唯一固定态为 $\sigma$，尽管 $N$ 本身保持全部 $Z$ 对角态。

还有一个不需另加物理公理的更大结构：

<a id="eq-c122-markov-semigroup"></a>

$$
\mathcal Q_t=e^{t(S-\operatorname{id})}
   =e^{-t}\sum_{n=0}^{\infty}\frac{t^n}{n!}S^n,
 \qquad t\ge0.
\tag{32}
$$

右端是通道的概率混合，故为 CPTP 半群，并保持 $\sigma$。每个谱方向以速率 $1-\lambda_j$ 衰减，极限仍为 $E$。在可观测量侧，$\mathcal Q_t^*$ 对 KMS 配对

$$
\langle A,B\rangle_{\sigma,\mathrm{KMS}}
   =\operatorname{Tr}(A^*\sigma^{1/2}B\sigma^{1/2})
$$

自伴，这由 $S\Gamma_\sigma=\Gamma_\sigma S^*$ 直接推出。于是比较余量成为一个非负耗散二次型，零方向组成稳定关系代数。最大混合参考下的双交换子表达与全参考误差界见定理~[3.4](#thm-c122-dirichlet-defect)、[3.5](#thm-c122-diamond-defect)；这里没有把一般非均匀参考的状态固定空间误认成同一个普通矩阵代数。

### 4.6 两个 qubit 实例：轴向压缩与非含幺的参考搬移

本小节 $X,Y,Z$ 表示 Pauli 矩阵。先取 $\sigma=I/2$。对扰动 $H=(xX+yY+zZ)/2$，有 $\|H\|_\sigma^2=x^2+y^2+z^2$，故这个*固定参考下*的扰动空间具有普通三维欧氏几何。

**例一：随机相位翻转。**

令 $N_p(\rho)=(1-p)\rho+pZ\rho Z$，$0\le p\le1$。它保持最大混合参考，且 $N_p^*=N_p$，于是

$$
P=N_p,\qquad
 N_p:\ (x,y,z)\mapsto((1-2p)x,(1-2p)y,z),
$$

$$
S=N_p^2:\ (x,y,z)\mapsto((1-2p)^2x,(1-2p)^2y,z).
$$

当 $0<p<1$，可观测量固定代数为 $\operatorname{span}\{I,Z\}$；在端点 $p=0,1$，前向过程为酉过程，$S=\operatorname{id}$。$p>1/2$ 时前向映射有负的横向特征值，回接谱仍非负。定理~[4.2](#thm-c122-weighted-contraction) 的正谱结论属于 $S$，并未声称所有量子通道自身都有正谱。

**例二：振幅阻尼。**

取 $0\le\gamma<1$，前向 Kraus 矩阵为

$$
K_0=\operatorname{diag}(1,\sqrt{1-\gamma}),\qquad
 K_1=\sqrt\gamma\,\lvert 0\rangle\langle 1\rvert.
$$

于是

$$
N_\gamma:(x,y,z)\mapsto
   \bigl(\sqrt{1-\gamma}\,x,\sqrt{1-\gamma}\,y,
             \gamma+(1-\gamma)z\bigr),
 \qquad \tau=\operatorname{diag}\left(\frac{1+\gamma}2,\frac{1-\gamma}2\right).
$$

代入 $L_a=\sigma^{1/2}K_a^*\tau^{-1/2}$，Petz 反向的 Kraus 矩阵为

$$
L_0=\operatorname{diag}\left(\frac1{\sqrt{1+\gamma}},1\right),\qquad
 L_1=\sqrt{\frac\gamma{1+\gamma}}\,\lvert 1\rangle\langle 0\rvert.
$$

它们满足 $\sum_aL_a^*L_a=I$，直接相乘得到

$$
P:(x,y,z)\mapsto
   \left(\frac{x}{\sqrt{1+\gamma}},\frac{y}{\sqrt{1+\gamma}},
                \frac{z-\gamma}{1+\gamma}\right).
$$

因此参考态被送回原处，而一次完整回接为

<a id="eq-c122-amplitude-ellipsoid"></a>

$$
S:(x,y,z)\mapsto(ax,ay,a^2z),\qquad
 a=\sqrt{\frac{1-\gamma}{1+\gamma}}.
\tag{33}
$$

例如 $\gamma=1/2$ 时，前向 Bloch 椭球中心在 $z=1/2$，轴长为 $(1/\sqrt2,1/\sqrt2,1/2)$；回接后的椭球中心回到原点，轴长变成 $(1/\sqrt3,1/\sqrt3,1/3)$。Petz 反向是合法的参考态反查，一般不会放大已丢失的区别。

<a id="fig-c122-amplitude"></a>

```latex
\begin{tikzpicture}[scale=2.45]
 \draw[->,gray] (-1.15,0)--(1.2,0) node[right] {$x$};
 \draw[->,gray] (0,-1.13)--(0,1.18) node[above] {$z$};
 \draw[gray,dashed] (0,0) circle[radius=1];
 \draw[teal!80!black,very thick] (0,0.5) ellipse[x radius=0.70710678,y radius=0.5];
 \draw[orange!85!black,very thick] (0,0) ellipse[x radius=0.57735027,y radius=0.33333333];
 \fill[teal!80!black] (0,0.5) circle[radius=0.018];
 \fill[orange!85!black] (0,0) circle[radius=0.018];
 \node[anchor=west,font=\small] at (1.32,0.82) {虚线：原态球截面};
 \node[anchor=west,font=\small,text=teal!80!black] at (1.32,0.50) {前向：中心移到 $z=1/2$};
 \node[anchor=west,font=\small,text=orange!85!black] at (1.32,0.18) {回接：中心回到 $0$};
 \node[anchor=west,font=\small] at (1.32,-0.17) {横向半轴：$1/\sqrt3$};
 \node[anchor=west,font=\small] at (1.32,-0.46) {纵向半轴：$1/3$};
 \node[anchor=west,font=\small] at (1.32,-0.83) {参考返回，区别仍有压缩。};
\end{tikzpicture}
```

**图 1。**振幅阻尼 $\gamma=1/2$ 的 $y=0$ 精确截面。
蓝绿色为前向输出集合，橙色为同一均匀参考的 Petz 回接输出集合。
这是 Bloch 坐标中的态集合图；加权收缩的长度还须使用各自参考的度量。

这里必须同步搬移度量。对输出的迹零扰动 $(uX+vY+wZ)/2$，逐项计算矩阵元给出

<a id="eq-c122-qubit-weighted-metric"></a>

$$
\left\|\frac{uX+vY+wZ}{2}\right\|_\tau^2
 =\frac{u^2+v^2}{\sqrt{1-\gamma^2}}
   +\frac{w^2}{1-\gamma^2}.
\tag{34}
$$

在输入、输出各自的加权正交坐标中，$T$ 的三个扰动奇异值因而为 $(\sqrt a,\sqrt a,a)$，其平方正是式~[(33)](#eq-c122-amplitude-ellipsoid) 的回接谱。不能在输出仍沿用输入最大混合态的权重，再声称得到了同一收缩几何。

若参考随状态变化，令 $\sigma_r=(I+rZ)/2$，上述度量的径向系数是 $(1-r^2)^{-1}$，横向系数是 $(1-r^2)^{-1/2}$。它与 C121 的 Bures 度量不同，不能沿用那一章的半径 $1/2$ 上半球结论。本节的简单几何是*固定参考之间的椭球收缩与正交余量*。

### 4.7 这个几何保留什么，尚未确定什么

$S$ 保留了前向过程的损失强度，却不包含其全部方向信息。若 $N(\rho)=U\rho U^*$，则 $P(\rho)=U^*\rho U$、$S=\operatorname{id}$，无论 $U$ 的旋转或相位是多少。白化映射的极分解 $T=U_T(T^\dagger T)^{1/2}$ 把方向因子与收缩因子分开；仅知道 $S$ 的谱不能确定 $U_T$。因此回接几何没有单独推出原门序列、Hamiltonian 或复杂场论的动力学。

**白话。**先把观察者已经持有的一份参考内容放在原处，再用它来衡量两份变化有多大、彼此怎样相关。前向读出把这些变化压短；同一个参考又把反向规则固定下来，所以回接不必临时猜输入是什么。每个方向都能分成“保留下来的长度”和“没有保留下来的长度”，两者按平方相加。只看两份变化和一个实际读口时，一条轴记录读数，另外两条轴就能把剩余关系补齐，形成严格的三维图形。反复回接，能稳定保存的关系留下来，其余方向逐渐衰减；留下来的可观测关系还能组成一个代数。但这幅图衡量的是比较与损失：图中的余量不是自动生成的一颗环境粒子，所有门的相位也没有被它单独确定。内生反向在这里落实为由同一参考和同一过程算出的一个具体映射，以及它对每份内容都必须遵守的同一组关系。

<a id="section-5"></a>

## 5. 从数学回推到内部识别与实际供应

<a id="sec-c122-operational"></a>

本节把三个问题分别落实：回推公式是否由已有读数确定；哪些实际门能执行它；校准和编译误差怎样进入最终保证。记前文由加权互易确定的 Petz 回推为

$$
\mathcal P_{\sigma,\mathcal N}(X)
 =\sigma^{1/2}\mathcal N^*(\tau^{-1/2}X\tau^{-1/2})\sigma^{1/2},
 \qquad \tau=\mathcal N(\sigma),\quad P=\operatorname{supp}\tau.
$$

这里 $\sigma$ 是源 $H$ 上归一化的忠实态；$\tau^{-1/2}$ 在 $P$ 上取逆，在 $P^\perp$ 上为零。回推在 $P\mathcal B(K)P$ 上保迹。只讨论一个较小源支持时，先将 $H$ 限制到该支持。

### 5.1 两个参照态没有确定一条逆门

### 例 5.1（同一输入、输出参照，仍有不同回推）

<a id="ex-c122-reference-insufficient"></a>

取 $H=K=\mathbb C^2$，$\sigma=I/2$，比较
$\mathcal N_0=\operatorname{id}$ 与 $\mathcal N_1=\operatorname{Ad}_Z$。
二者都有 $\tau=I/2$，但对应回推分别是 $\operatorname{id}$ 与 $\operatorname{Ad}_Z$。
只读取 $\sigma,\tau$ 的规则必须对二者作出同一选择 $\mathcal R$。由于

$$
\|\operatorname{id}-\operatorname{Ad}_Z\|_\diamond=2,
 \qquad
 \|\mathcal R\operatorname{Ad}_Z-\operatorname{id}\|_\diamond
 =\|\mathcal R-\operatorname{Ad}_Z\|_\diamond,
$$

三角不等式迫使

$$
\max_{j=0,1}\|\mathcal R\mathcal N_j-\operatorname{id}\|_\diamond\ge1.
$$

第一式可用输入 $\lvert +\rangle=(\lvert 0\rangle+\lvert 1\rangle)/\sqrt2$ 验证：两输出正交。
因此，参照态相同不等于通道已被识别；还需内部标定的交叉读数或完整门资料。

这里的标定不要求外部坐标系。它要求所用准备、效果与门在*同一套内部关系*中有已给定的矩阵表示，且以后实际调用遵守这套表示。知道一个矩阵、供应它的成功滤片、供应该滤片的完整酉实现及逆门，是不同的资源陈述。

### 5.2 有明确成功旗的 Petz 电路

### 定义 5.2（本节实际门资源）

给定并供应同一个完整酉

$$
U:H\otimes E_0\longrightarrow K\otimes E,\qquad m=\dim E,
$$

及其逆门 $U^*$、原初始化态 $\lvert 0\rangle\in E_0$、对该初始化支持的投影和输出解码。其中

$$
\mathcal N(X)=\operatorname{Tr}_E\bigl[U(X\otimes\lvert 0\rangle\langle 0\rvert)U^*\bigr].
$$

不同维数通过共同有限载体中的已声明编码处理；若以上张量分解不便使用，可用已供应的初始化等距 $J:H\to K\otimes E$ 及投影 $JJ^*$ 表达同一操作。
另供应最大混合辅助态 $I_E/m$，以及两个带成功旗的滤片

$$
A_\tau=c\tau^{-1/2},\qquad A_\sigma=\sigma^{1/2},
 \qquad 0<c^2\le\lambda_{\min}^{+}(\tau).
$$

两者均为收缩，所以对应合法的迹不增 CP 支路。这里 $\tau$ 必须来自上述*同一个实际* $U$ 所定义的 $\mathcal N(\sigma)$。

### 定理 5.3（成功概率与未知输入无关的回推支路）

<a id="thm-c122-heralded-petz"></a>

在上述资源下，按以下顺序操作：先施加 $A_\tau$；附加 $I_E/m$ 后运行 $U^*$，只接受 $E_0$ 返回 $\lvert 0\rangle$ 的分支；最后施加 $A_\sigma$。全部成功的支路恰为

<a id="eq-c122-petz-success-map"></a>

$$
\mathcal S_{\rm succ}(X)
 =\frac{c^2}{m}\,\mathcal P_{\sigma,\mathcal N}(X).
\tag{35}
$$

对任意 $P$ 支持的归一化输入，成功概率均为

<a id="eq-c122-constant-success"></a>

$$
p=\frac{c^2}{m}.
\tag{36}
$$

结论包括输入与任意参考的纠缠；成功后归一化的联合通道为
$\mathcal P_{\sigma,\mathcal N}\otimes\operatorname{id}$。

**证明。**
令
$K_a=(I_K\otimes\langle a\rvert)U(I_H\otimes\lvert 0\rangle)$。
逆门加初始化投影作用于 $Y\otimes I_E/m$ 的成功映射为

$$
\frac1m(I_H\otimes\langle 0\rvert)U^*(Y\otimes I_E)U(I_H\otimes\lvert 0\rangle)
 =\frac1m\sum_aK_a^*YK_a=\frac1m\mathcal N^*(Y).
$$

夹上两个滤片后，成功支路的 Kraus 算子为

$$
M_a=\frac c{\sqrt m}\sigma^{1/2}K_a^*\tau^{-1/2}.
$$

因此得到式 [(35)](#eq-c122-petz-success-map)，并且

$$
\sum_aM_a^*M_a
 =\frac{c^2}{m}\tau^{-1/2}\mathcal N(\sigma)\tau^{-1/2}
 =pP.
$$

该算符等式直接给出所有 $P$ 支持输入的同一成功率，在张量参考后仍成立。
又因 $\sigma\ge\mu I_H$ 对某个 $\mu>0$ 成立，
$\tau\ge\mu\mathcal N(I_H)$。任意源态的输出都支持于 $P$，所以实际向前过程的输出满足本定理的支持承诺。

这条逆酉、辅助态与滤片的路线是已知 Petz 实现算法的精确有限版本；相应的近似矩阵函数和放大算法见 Gily
'en 等 [10](#ref-gilyen2022)。本节给出其供应前件和归一化证明，不将此电路称为新算法。

若取 $c^2=\lambda_{\min}^{+}(\tau)$，单次成功率为
$\lambda_{\min}^{+}(\tau)/m$。这已经显示最小正谱值的资源作用；它不是协议无关的最优代价下界。有限次数的概率抽样也不能自行证明某个特征值*恰好为零*。精确支持、正谱下界和滤片精度必须有明示证书，或转而在一个已知的名义模型中构造全空间通道。

**白话。**先按输出参照重新加权，再沿同一完整门倒走，检查是否回到原来的初始化记录，最后按输入参照加权。三步合起来的成功机会对所有未知内容都一样，所以成功没有额外挑选某种输入。但失败仍然是一次真实结果，不能因为公式能归一化，就把失败从操作成本里删掉。

### 5.3 怎样把同一成功支路提升为确定性通道

先明确额外资源：将 $I_E/m$ 以一个*受控的纯化*供应，保留所有滤片与投影的成功、失败记录，不在中途丢弃。还须供应这整个相干电路 $C$、逆电路 $C^*$、初始化子空间反射、成功旗子空间反射，以及下面使用的已知辅助硬币旋转。仅有破坏性测量接口不蕴含这些资源。

### 定理 5.4（整个源空间的同角度确定性放大）

<a id="thm-c122-coherent-amplification"></a>

设 $J:S\to\mathcal L$ 为初始化等距，$C$ 为共同有限空间 $\mathcal L$ 上的已供应酉，$\Pi_g$ 为成功投影。若

$$
A=\Pi_gCJ,\qquad A^*A=pI_S,\qquad 0<p\le1,
$$

并供应上述反射、逆电路及辅助旋转，则存在一个有限电路，对*全部*未知输入和参考确定性实现成功等距
$W=A/\sqrt p$。它调用 $C$ 或 $C^*$ 的次数为 $O(p^{-1/2})$，不需要反射关于未知输入态本身。

**证明。**
$p=1$ 时已有 $CJ=W$。设 $0<p<1$，定义

$$
B=\frac{(I-\Pi_g)CJ}{\sqrt{1-p}},\qquad
 \theta=\arcsin\sqrt p.
$$

有 $W^*W=B^*B=I_S$、$W^*B=0$，以及

$$
CJ=\sin\theta\,W+\cos\theta\,B.
$$

所以 $\operatorname{Ran} W\oplus\operatorname{Ran} B$ 自然等同于 $\mathbb C^2\otimes S$。
在这*整个*空间上，$\Pi_g$ 与 $CJJ^*C^*$ 的分块矩阵分别为

$$
\begin{pmatrix}I&0\\0&0\end{pmatrix},\qquad
 \begin{pmatrix}
 \sin^2\theta\,I&\sin\theta\cos\theta\,I\\
 \sin\theta\cos\theta\,I&\cos^2\theta\,I
 \end{pmatrix}.
$$

因此同一个两反射操作

$$
Q=(2CJJ^*C^*-I)(I-2\Pi_g)
$$

在该空间上的作用为

$$
Q=\begin{pmatrix}\cos2\theta&\sin2\theta\\
 -\sin2\theta&\cos2\theta\end{pmatrix}\otimes I_S.
$$

于是对所有整数 $n\ge0$ 都有算符等式

<a id="eq-c122-uniform-rotation"></a>

$$
Q^nCJ=\sin((2n+1)\theta)W+\cos((2n+1)\theta)B.
\tag{37}
$$

这不是为每个输入另挑一个二维平面上的操作；整个 $S$ 的每个方向承受同一个旋转矩阵。

为达到精确成功而不越过目标，取

$$
n=\left\lceil\frac{\pi}{4\arcsin\sqrt p}-\frac12\right\rceil,
 \qquad p'=\sin^2\!\frac{\pi}{4n+2}\le p.
$$

附加一个独立、已知的量子硬币，其成功概率为 $p'/p$，将旧成功旗与硬币成功一起作为新成功条件。新成功等距仍是 $W$，只多一个固定硬币标签；成功率变为 $p'$。对这个增大的电路使用式 [(37)](#eq-c122-uniform-rotation)，有
$(2n+1)\arcsin\sqrt{p'}=\pi/2$，故 $n$ 次反射后失败分量严格为零。
调用原电路及逆电路共 $2n+1=O(p^{-1/2})$ 次。
全部等式都是定义于 $S$ 的线性算符等式，张量任意 $I_Z$ 后仍成立；最后忘掉成功等距的环境，即执行同一个目标通道。

这种已知成功率的衰减与精确放大属于标准振幅放大方法 [11](#ref-bhmt2002)；上面特意保留整个源空间，说明为何它能操作未知且可能纠缠的输入。对定理 [5.3](#thm-c122-heralded-petz)，所需调用数为

$$
O(\sqrt m/c)=O\!\left(\sqrt{m/\lambda_{\min}^{+}(\tau)}\right)
$$

（右式取最大允许 $c$）。此数尚未计入滤片、反射及辅助态本身的编译代价。
精确电路假设硬币角度和各门已精确供应；有限离散门菜单通常给出近似编译，误差必须计入后面的实施证书。

### 命题 5.5（失败旗不自动允许重试）

<a id="prop-c122-no-free-retry"></a>

常量成功率和成功支路 $p\mathcal P$ 不蕴含失败后能保留原来的未知输入。若另外供应每个失败支路的共同恢复，使其回到原输入，才可合法重复；此时重复 $r$ 次后的残余失败率为 $(1-p)^r$，期望尝试次数为 $1/p$。

**证明。**
成功映射 $p\mathcal P$ 与失败映射
$(1-p)\operatorname{Tr}(\cdot)\omega_0$ 可组成合法仪器。失败旗虽然可见，失败状态却已擦除全部输入，不能共同还原两个正交态。这否定了无附加条件的重试。
反之，若每个失败支路 $\mathcal F_j$ 都有已供应的纠正 $\mathcal D_j$，满足
$\mathcal D_j\mathcal F_j=q_j\operatorname{id}_S$、$\sum_jq_j=1-p$，则每次失败后整个未知输入及参考确实返回，条件成功率仍为 $p$。几何分布给出所述概率和期望。

即使具备这种反馈，有限 $r$ 次也仍有失败分支。末尾用一个固定通道补全，则得到距目标至多 $2(1-p)^r$ 的确定性通道；无限重试只给几乎必然最终成功，不给有限最坏运行次数。

**白话。**要让成功支路变成每次都能执行的通道，有两条有条件的路：完整保留各条支路，沿同一组反射把成功幅度转满；或者证明每一次失败都能把原内容还回去，再重试。第一条需要完整相干控制，第二条需要失败恢复。单独一个成功标记，两种资源都没有自动送给我们。

### 5.4 有限内部读数怎样识别整条通道

以下准备与效果的线性关系均在同一内部标定中给定。源基为 $e_1,\ldots,e_d$，准备以下 $d^2$ 个纯态投影：

$$
P_r=\lvert e_r\rangle\langle e_r\rvert,\quad
 P^+_{rs}=\frac{\lvert e_r+e_s\rangle\langle e_r+e_s\rvert}2,\quad
 P^{+i}_{rs}=\frac{\lvert e_r+ie_s\rangle\langle e_r+ie_s\rvert}2
 \quad(r<s).
$$

在 $k$ 维输出端，用同样构造的 $k^2$ 个投影 $F_b$ 分别作为二元效果。实验需要的是这些实际准备和读口；它们可以各有对应的读数实验，不要求一份输出同时接受所有不相容测量。

### 定理 5.6（有限读数的显式 diamond 误差界）

<a id="thm-c122-finite-tomography"></a>

设真实过程 $\mathcal N$ 与名义过程 $\mathcal N_0$ 均为从 $M_d$ 到 $M_k$ 的 CPTP 映射。若对全部上述准备 $P_a$、效果 $F_b$，有

$$
\left|\operatorname{Tr}\bigl(F_b[\mathcal N(P_a)-\mathcal N_0(P_a)]\bigr)\right|
 \le\nu,
$$

则令 $\beta_k=k\sqrt{8k-7}\,\nu$，有

<a id="eq-c122-tomography-diamond"></a>

$$
\|\mathcal N-\mathcal N_0\|_\diamond
 \le\delta_{\rm tom}:=
 \min\{2,[1+(2+\sqrt2)(d-1)]\beta_k\}.
\tag{38}
$$

特别地，精确读数完全相同就确定同一条通道。该结论覆盖全部纠缠参考，不是仅对所测试的纯态成立。

**证明。**
记 $\Delta=\mathcal N-\mathcal N_0$。固定一个已列准备，写
$Y=\Delta(P_a)=Y^*$。对角投影给 $|Y_{jj}|\le\nu$；两个平衡投影分别给

$$
|\operatorname{Re} Y_{j\ell}|\le2\nu,\qquad
 |\operatorname{Im} Y_{j\ell}|\le2\nu\quad(j\ne\ell).
$$

例如 $\operatorname{Tr}(F^+_{j\ell}Y)=(Y_{jj}+Y_{\ell\ell})/2+\operatorname{Re} Y_{j\ell}$，而 $+i$ 效果将最后一项换成 $-\operatorname{Im} Y_{j\ell}$。于是

$$
\|Y\|_2^2\le[k+8k(k-1)]\nu^2,
 \qquad \|Y\|_1\le\sqrt k\,\|Y\|_2\le\beta_k.
$$

源端矩阵单位可以显式重构：对 $r<s$，

$$
E_{rs}=P^+_{rs}+iP^{+i}_{rs}
          -\frac{1+i}{2}(P_r+P_s).
$$

所以 $\|\Delta(E_{rr})\|_1\le\beta_k$，并且
$\|\Delta(E_{rs})\|_1\le(2+\sqrt2)\beta_k$ 对所有 $r\ne s$ 成立；下三角用保持伴随性处理。

取任意参考 $Z$ 与联合态 $\rho=\sum_{r,s}E_{rs}\otimes\rho_{rs}$。
记 $p_r=\operatorname{Tr}\rho_{rr}$。由正平方根分块，$\rho_{rs}=A_rA_s^*$，故
$\|\rho_{rs}\|_1\le\|A_r\|_2\|A_s\|_2=\sqrt{p_rp_s}$。
因此

$$
\begin{aligned}
\|(\Delta\otimes\operatorname{id}_Z)(\rho)\|_1
 &\le\beta_k\sum_rp_r
 +(2+\sqrt2)\beta_k\sum_{r\ne s}\sqrt{p_rp_s}\\
 &\le[1+(2+\sqrt2)(d-1)]\beta_k,
\end{aligned}
$$

其中 $\sum_r\sqrt{p_r}\le\sqrt d$。参考维数从未受限。
任意算子输入先用
$\frac12\left(\begin{smallmatrix}0&X\\X^*&0\end{smallmatrix}\right)$
作不改变迹范数的 Hermitian 化，再分解正、负部分，即把全参考态界提升为 diamond 范数界。两个通道之差另有普遍上界 $2$，完成证明。

### 推论 5.7（有限抽样与 CPTP 拟合）

若同一固定过程的每个准备–效果组合独立重复 $s$ 次，记
$M=d^2k^2$，则全部频率同时距真实概率不超过 $\epsilon$ 的概率至少为
$1-2M e^{-2s\epsilon^2}$。在此事件中，任何对这些频率拟合误差也不超过 $\epsilon$ 的 CPTP 模型 $\mathcal N_0$，均可在上一定理中取 $\nu=2\epsilon$。

**证明。**
对 Bernoulli 变量 $X$，函数
$h(t)=\log\mathbb E e^{t(X-\mathbb EX)}$ 满足 $h(0)=h'(0)=0$、$h''(t)\le1/4$，故 $h(t)\le t^2/8$。指数 Markov 界取 $t=4\epsilon$，得到单侧频率偏差概率至多 $e^{-2s\epsilon^2}$。对两侧与全部 $M$ 个组合取并集界，再用真实概率、频率和拟合概率之间的三角不等式即可。

拟合可以写成有限 Choi 矩阵的正性、保迹与读数区间约束；置信事件中真实通道是一个可行点。这里已声明真实过程 CPTP，并没有用有限读数替代完整参考相容。准备和效果若另有校准误差，须先加入读数区间；若通道在实验过程中改变，也不再满足本定理的同一过程前提。这份常数是易验证的充分界，不声称样本或维数代价最优。

### 5.5 把模型误差和实际编译接到共同恢复

为避免支持变化造成未定义操作，名义 Petz 回推可在整个输出空间上补全为

$$
\mathcal R_0(X)=\mathcal P_{\sigma,\mathcal N_0}(X)
       +\operatorname{Tr}[(I-P_0)X]\rho_*,\qquad
 P_0=\operatorname{supp}\mathcal N_0(\sigma),
$$

其中 $\rho_*$ 是固定源态。它是全空间 CPTP 映射。其在名义向前输出上的误差
$e_0=\|\mathcal R_0\mathcal N_0-\operatorname{id}\|_\diamond$
须由前文*针对指定 Petz 回推*的定理或另行验证取得，不能把“某个恢复器存在”的界直接赋给它。

### 定理 5.8（一份可实施的总误差证书）

<a id="thm-c122-implemented-certificate"></a>

若

$$
\|\mathcal N-\mathcal N_0\|_\diamond\le\delta_{\rm tom},\qquad
 \|\widetilde{\mathcal R}-\mathcal R_0\|_\diamond\le\eta,
$$

其中 $\widetilde{\mathcal R}$ 是*实际确定性* CPTP 实现，则

<a id="eq-c122-total-operational-error"></a>

$$
\boxed{\quad
 \|\widetilde{\mathcal R}\mathcal N-\operatorname{id}\|_\diamond
 \le\min\{2,e_0+\delta_{\rm tom}+\eta\}.
 \quad}
\tag{39}
$$

**证明。**
在差中插入 $\mathcal R_0\mathcal N$ 和 $\mathcal R_0\mathcal N_0$。
CPTP 前后复合收缩 diamond 范数，再用三角不等式，即得所述三项之和；该范数已经包含任意参考。

第二项不能兼任第三项。若滤片使用估计的 $\tau_0$，却仍运行未知实际 $U^*$，一般不再有
$\sum_aM_a^*M_a=pP$，所以不能按名义 $p$ 宣布精确放大成立。可以从已识别的名义 Kraus 数据编译整个 $\mathcal R_0$；也可以对所调用的完整逆门、滤片和反射另外供应误差证书。普通通道层析不自动认证其某个指定酉扩充在未初始化方向上的作用。

例如，共同辅助空间中的理想和实际等距若满足
$\|W-\widetilde W\|_\infty\le\xi$，则逐项展开
$WXW^*-\widetilde WX\widetilde W^*$ 并取部分迹，给实现通道的 diamond 误差至多 $2\xi$。若整个酉电路由门误差 $\xi_j$ 的有限门串构成，望远镜展开给
$\xi\le\sum_j\xi_j$，于是可取 $\eta\le2\sum_j\xi_j$。
所有失败处理也必须纳入这个确定性实现；不能只对接受样本报告 $\eta$。

**白话。**先用一套内部标定的有限准备和读口，把门本身辨认到一个明确误差内；再依据同一参照构造回推，把成功率、失败支路、完整逆门和编译精度逐项兑现。最后，名义门本来还剩多少恢复误差，加上门识别误差，再加实际执行误差，就是对全部未知内容和参考的共同保证。参照让“怎样回推”有了定义，完整记录与实际控制则决定这条回路能否真正走通。

<a id="section-6"></a>

## 6. 候选与通常有限量子力学的完整推导接口

<a id="sec-c122-qm"></a>

本节明确列出通常有限量子力学各条规则的推导入口。C122 的二元互易给出参考回推；它单独并不强迫对象必须非交换。要重构整个有限量子理论，还要消费附录的对象选择，以及本节列出的概率、参考、复合与可逆运动条件。以下证明全部在本稿中给出，不把这些条件隐写成互易公式的后果。

### 6.1 状态也是一个读口：正关系、Hilbert 空间与 Born 规则

### 命题 6.1（从关系核构造振幅空间）

设历史标签集合 $S$ 带复核 $K$，满足所有有限矩阵 $[K(s_i,s_j)]\succeq0$。在有限形式和 $\sum c_s[s]$ 上定义

$$
\left\langle\sum c_s[s],\sum d_t[t]\right\rangle
 =\sum_{s,t}\overline{c_s}d_tK(s,t).
$$

商去零范数向量并完备化，得到 Hilbert 空间 $H_K$ 与向量 $v_s$，满足 $\langle v_s,v_t\rangle=K(s,t)$；以这些向量的闭线性包为全部空间时，该实现唯一到一个酉同构。

**证明。**
有限正性给出非负半内积。对 $u+t v$ 的范数平方使用判别式得到 Cauchy–Schwarz 不等式，所以零范数向量与全部向量正交，商内积良定义。若另一组 $w_s$ 有同一核，映射 $\sum c_sv_s\mapsto\sum c_sw_s$ 保持范数，因而良定义；稠密线性包上的等距延拓给出所述酉映射。

若历史来自有限 $*$-代数 $\mathcal A$，$\omega$ 为正归一化泛函，且 $K(a,b)=\omega(a^*b)$，则商空间还保留左作用 $\pi(a)[b]=[ab]$。在 $C^*$-对象中，$a^*a\le\|a\|^2I$ 保证此作用有界，单位向量 $\xi=[I]$ 满足 $\omega(a)=\langle \xi,\pi(a)\xi\rangle$。这就是有限 GNS 构造的具体形式。它重建某个状态的循环表示，不把 $\Omega$ 宣告为该单个向量，也不把满秩混合态的 $d^2$ 维 GNS 空间误当成 $M_d$ 的 $d$ 维不可约振幅空间。

### 定理 6.2（效果概率的 Born 表示）

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

这是效果版 Gleason 论证的有限形式 [14](#ref-busch2003)。作为映射 $\omega:\mathcal A\to\mathbb C$，一个状态正是候选的标量终端读口；其二元比较核是 $K(a,b)=\omega(a^*b)$。复数域和全部效果的可加语义已经列入接口，不能称它们也由“归一化”独自推得。

### 6.2 观测、一般测量及状态更新

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

### 定理 6.3（理想锐读出为何给出 Lüders 更新）

设完全正分支 $\mathcal I$ 的效果是投影 $P$，即 $\operatorname{Tr}\mathcal I(\rho)=\operatorname{Tr}(P\rho)$。再要求对每个单位 $\psi\in\operatorname{Ran} P$，$\mathcal I(\lvert \psi\rangle\langle \psi\rvert)=\lvert \psi\rangle\langle \psi\rvert$。则

$$
\mathcal I(\rho)=P\rho P.
$$

**证明。**
写 $\mathcal I(\rho)=\sum_rK_r\rho K_r^*$。效果等式给 $\sum K_r^*K_r=P$，所以每个 $K_r$ 在 $\ker P$ 上为零。对 $\psi\in\operatorname{Ran} P$，一组正秩一项之和支撑于 $\mathbb C\psi$，迫使每个 $K_r\psi$ 均与 $\psi$ 共线。一个线性映射若保持子空间内每一条射线，就在该子空间上为标量：比较任意两个独立向量及其和即可。故 $K_r=c_rP$，且 $P\ne0$ 时 $\sum|c_r|^2=1$。代回即得结论；$P=0$ 时所有 $K_r=0$。

这里没有预设单 Kraus 算子。额外的理想性条件是“不改变该结果子空间内部的每条射线”；只要求结果可重复，还允许在子空间内作非平凡酉旋转，并不足以指定 Lüders 仪器。

### 6.3 复合系统、纠缠及可逆运动

### 命题 6.4（独立全矩阵部门的复合）

设 $M_d(\mathbb C)$、$M_m(\mathbb C)$ 以含幺复线性 $*$-嵌入进入同一个非零结合 $*$-代数；两个像彼此交换并生成该代数。则所生成代数为 $M_{dm}(\mathbb C)$。

**证明。**
映射 $a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 由交换性成为满射 $*$-同态。矩阵单位的张量乘积是 $M_{dm}$ 的矩阵单位，且 $M_{dm}$ 为单代数：任一非零双边理想中的非零矩阵元，通过左右矩阵单位可生成所有矩阵单位。因此该含幺非零同态的核为零。

“共同复中心、独立子代数、生成性”承担张量复合的输入。不是任意两个内部窗口都独立。由一个二元块反复独立复合得到 $M_{2^n}$，允许秩 $d$ 的角落即可得到任意 $M_d$。张量正态包含纠缠态；例如 Bell 态不能写成产品态的凸和，因为纯态若可凸分解，各分量必须沿同一射线，而该射线不是产品向量。

在下一小节，完整参考相容给出 Kraus 与等距表示；同维的双向合法可逆过程进一步成为酉共轭。任意 Petz 回推不保证具有这样的双向恢复性质。

若进一步*供应一个*连续的完整酉群 $U(t+s)=U(t)U(s)$、$U(0)=I$，有限维下所有 $U(t)$ 交换且正规，可同时对角化。每个对角元是实加法群的连续单位模特征，故为 $e^{-i\omega_jt}$；由局部连续辐角和加法性可直接证明。于是存在自伴 $H$，

$$
U(t)=e^{-itH/\hbar},\qquad
 i\hbar\,\frac{d}{dt}\psi(t)=H\psi(t).
$$

时间参数、连续群的供应、具体 $H$ 与作用量单位 $\hbar$ 均没有由静态比较关系决定。静态内生关系与具体动力学选择不可互换。

### 6.4 完整参考相容、Kraus 表示及酉运动

### 定理 6.5（内部参考的相容性给出完整扩张）

<a id="thm-c122-kraus"></a>

设 $N:M_d(\mathbb C)\to M_k(\mathbb C)$ 复线性、保迹。对全部有限参考，
$(N\otimes\operatorname{id})(X)\ge0$ 当 $X\ge0$，当且仅当

$$
N(X)=\sum_a K_aXK_a^*,\qquad \sum_aK_a^*K_a=I.
$$

这也等价于存在有限记录空间 $E$ 及等距
$V:H\to K\otimes E$，使 $N(X)=\operatorname{Tr}_E(VXV^*)$。

**证明。**
取 $\lvert \Gamma\rangle=\sum_re_r\otimes e_r$。完整参考相容给正矩阵

$$
C_N=(\operatorname{id}_d\otimes N)\lvert \Gamma\rangle\langle \Gamma\rvert
 =\sum_{r,s}\lvert r\rangle\langle s\rvert\otimes N(\lvert r\rangle\langle s\rvert)\ge0.
$$

谱分解 $C_N=\sum_aw_aw_a^*$，写
$w_a=\sum_re_r\otimes K_ae_r$。
比较矩阵块即得 Kraus 公式；迹对偶给归一化。
反向，每项联合夹乘 $(K_a\otimes I)X(K_a^*\otimes I)$ 都为正。
定义 $V\psi=\sum_aK_a\psi\otimes\lvert a\rangle$，
归一化给 $V^*V=I$，偏迹给 $N$；反向把等距在记录基下展开即可。

这是有限 Choi–Stinespring 构造。 [12](#ref-choi1975)、[13](#ref-stinespring1955)
它的输入是完整参考相容，不是普通单系统二元概率正性。
转置 $\Theta(X)=X^{\mathsf T}$ 保持单系统正性及迹，
但

$$
(\Theta\otimes\operatorname{id})\lvert \Phi^+\rangle\langle \Phi^+\rvert=\tfrac12\mathsf{Swap}
$$

在反对称向量上有本征值 $-1/2$，所以不合法。
它说明即使单系统比较与某些回推几何都成立，也不能删除联合参考条件。

### 定理 6.6（同维双向合法可逆过程是酉共轭）

若 $N,R:M_d(\mathbb C)\to M_d(\mathbb C)$ 均为通道，且 $RN=\operatorname{id}$，
则存在酉 $U$，$N(X)=UXU^*$、$R(X)=U^*XU$。

**证明。**
同维有限线性空间上的左逆也是双向逆，故 $NR=\operatorname{id}$。
令 $\Phi=N^*$、$\Psi=R^*$，都是保单位完全正映射。
Kraus 等距表示给 Schwarz 不等式
$\Phi(A^*A)\ge\Phi(A)^*\Phi(A)$；
再施加 $\Psi$ 并对 $\Psi$ 使用同一不等式，可得

$$
A^*A\ge\Psi(\Phi(A)^*\Phi(A))
 \ge\Psi(\Phi(A))^*\Psi(\Phi(A))=A^*A.
$$

因为 $\Psi$ 可逆，原 Schwarz 余量为零。
将 $A+tB$ 代入并分别比较实、虚交叉项，得
$\Phi(A^*B)=\Phi(A)^*\Phi(B)$。
所以 $\Phi$ 是含幺 $*$-自同构。

取矩阵单位 $E_{ij}$。$\Phi(E_{ii})$ 是两两正交且总和为 $I$ 的最小投影；
它们秩均为一。取各自单位像向量 $u_i$，
$\Phi(E_{ij})$ 的初始及终止空间给
$\Phi(E_{ij})=c_{ij}\lvert u_i\rangle\langle u_j\rvert$，
乘法与伴随给 $c_{ij}c_{jl}=c_{il}$、$c_{ji}=\bar c_{ij}$、
$|c_{ij}|=1$。调整 $u_i$ 的相位可使全部 $c_{ij}=1$，
得到 $\Phi=\operatorname{Ad}_W$。取迹伴随即得 $N=\operatorname{Ad}_{W^*}$。

因此，在已经供应连续可逆时间参数的条件下，前面的指数形式和
Schrödinger 方程成立。一般有损过程的 Petz 双反向性
$(N^\sharp)^\sharp=N$ 则是*反推指派的对合*，
不等于 $N^\sharp N=\operatorname{id}$；不能用前者替代本定理的假设。

### 6.5 两项直接可算的量子约束

### 命题 6.7（不确定关系来自二元正比较）

对自伴 $A,B$ 与任意状态 $\omega$，有

$$
\operatorname{Var}_\omega(A)\operatorname{Var}_\omega(B)
 \ge\left|\omega\bigl((A-\omega(A)I)(B-\omega(B)I)\bigr)\right|^2
 \ge\frac14|\omega([A,B])|^2.
$$

**证明。**
令 $X=A-\omega(A)I$、$Y=B-\omega(B)I$。状态的二元 Gram 矩阵
$\left(\begin{smallmatrix}\omega(X^2)&\omega(XY)\\\omega(YX)&\omega(Y^2)\end{smallmatrix}\right)$ 为正，行列式非负给出第一项。又 $\omega(YX)=\overline{\omega(XY)}$，所以 $2i\operatorname{Im}\omega(XY)=\omega([A,B])$，给出第二项。

### 命题 6.8（独立两端的 CHSH 约束）

若 $A_0,A_1$ 与 $B_0,B_1$ 分别为两独立量子部门的自伴反射，即平方均为 $I$，则

$$
S=A_0\otimes(B_0+B_1)+A_1\otimes(B_0-B_1)
 \quad\text{满足}\quad \|S\|\le2\sqrt2.
$$

该界在两个量子比特中可以达到。

**证明。**
直接展开得 $S^2=4I-[A_0,A_1]\otimes[B_0,B_1]$；每个交换子范数至多为 $2$，故 $\|S^2\|\le8$。取 $A_0=Z,A_1=X$、$B_0=(Z+X)/\sqrt2,B_1=(Z-X)/\sqrt2$，并在 Bell 态 $(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$ 上求期望，得到 $2\sqrt2$。若四个结果预先取定为局部数值 $\pm1$，同一表达式绝对值只能为 $2$；对这样的赋值作概率混合仍不超过 $2$。

这些是本稿明列结构条件所重构的通常量子理论的约束，不是新的实验偏离预言。要声称不同于现有量子力学的物理预测，还须修改明确的结构输入并计算其可区分后果。

### 6.6 可复用的推导清单

| 通常的量子结构 | 本稿的推导入口 | 仍然承重的输入 |
|---|---|---|
| Hilbert 振幅与射线 | 全有限正核的商空间；$M_d$ 不可约模块 | 复对象选择、可叠加历史语义 |
| 密度矩阵、Born 规则 | 效果的正、归一化及细分可加 | 所有相关效果的同一赋值 |
| POVM 与仪器 | 交换结果代数与带记录的完全正分支 | 实际结果标签与门供应 |
| 完全正性及 Kraus 形式 | 本节的参考相容与有限 Choi 构造 | 全部必要有限参考兼容 |
| 张量复合及纠缠 | 共同复中心上的交换生成关系 | 独立性与复合供应 |
| 可逆门 | 双向合法可逆性、全矩阵自同构 | 同一完整通道、同维时为酉 |
| Lüders 更新 | 锐效果加每条内部射线不受扰动 | 理想测量条件 |
| Schrödinger 方程 | 连续完整酉群的谱分解 | 时间、群、$H$ 及单位选择 |

**白话。**状态是一种读口，测量是一种把问题送到结果标签的读口，运动也是一种把后面的问题回拉到前面的读口。要求同一来源的全部比较在参考接续后仍合法，再要求内部参照的二元比较能相互对读，就把概率、完整记录和参考回推接进同一套定义。要得到具体的物理世界，还必须说哪些对象、哪些复合、哪些钟和哪些门实际存在；这部分不会因为把公理改叫定义就自动消失。

<a id="section-7"></a>

## 7. 反向检验：删除一项约束会发生什么

<a id="sec-c122-countermodels"></a>

本轮候选有明确作用域。最有用的检验不是给它一个更宏大的名字，
而是逐项构造删除模型，看看哪一种关系首先失效。

### 例 7.1（只要求返回参考，不能选定回推）

令 $\sigma=\tau=I/d$、$\mathcal N=\operatorname{id}$。恒等回推和替代回推
$\mathcal R_0(X)=\operatorname{Tr}(X)I/d$ 都满足 $\mathcal R(\tau)=\sigma$。
取 $A=B$ 为秩一投影，真正的前向配对为 $1/d$，
替代回推的反向配对为 $1/d^2$。
因此“能把自己的起点找回来”没有保住二元互易。

### 例 7.2（完整二元互易仍不等于所有内容可恢复）

令 $\mathcal N(X)=\operatorname{Tr}(X)\tau$，其中 $\tau$ 忠实。
对任意忠实 $\sigma$，Petz 回推为
$\mathcal N^\sharp_\sigma(X)=\operatorname{Tr}(X)\sigma$。
它完全满足本轮互易和参考恢复，却把所有输入都送成同一个状态。
这说明互易规定的是相容反查；全源恢复还必须有保留内容的证据。

### 例 7.3（更换参考会更换“没有读到的部分”怎样被填补）

对二阶完全 $Z$ 退相干 $N$，均匀参考 $\pi=I/2$ 给
$P_{\pi,N}=N$，保住全部对角态。
换成 $\sigma=(I+rX)/2$、$0<r<1$，则同一个 $N$ 的回接为
$(x,y,z)\mapsto(r,0,\sqrt{1-r^2}\,z)$。
已知的参考相干被重新准备，其他方向按新权重处理。
因此逐对偷偷改参照，会把不同反查规则混成一个并不存在的共同恢复。

### 例 7.4（经典世界也是二元互易规则的模型）

设有限状态标签 $i,j$，严格正先验 $s_i$，随机通道 $n(j|i)$，
以及预测 $t_j=\sum_i n(j|i)s_i>0$。
把效果取作 $0\le a_i,b_j\le1$，二元比较为

$$
b(a,b)=\sum_{i,j}s_i\,a_i\,n(j|i)\,b_j.
$$

交换两端仍保留同一配对，唯一给出

$$
n^\sharp(i|j)=\frac{s_i n(j|i)}{t_j}.
$$

这就是经典 Bayes 反查；它返回先验、可顺序和并行组合、反查两次返回原通道。
全部乘法仍然交换，并没有量子干涉或量子纠缠。

所以“全部在 $\Omega$ 内”加二元互易，并不逻辑蕴含必须出现非交换复量子理论。
附录的实球形原子、非平凡方向回路、结合保星闭包，
以及共同复中心上的独立复合，承担对象选择。
把这些要求写成内部定义之间的约束，可以消除外部裁判的角色，
却不会消除模型选择本身。

| 删除或混淆的条件 | 明确后果 |
|---|---|
| 只有参考返回，无二元互易 | 恒等与重置同样返回参考，回推不唯一。 |
| 只有普通正性，无联合参考相容 | 转置通过单系统正性，却在 Bell 参考上产生负方向。 |
| 有互易，无内容保留证书 | 替代通道具有合法反查，仍丢掉全部未知输入。 |
| 只有源、输出参考，无交叉标定 | $\operatorname{id}$ 与 $\operatorname{Ad}_Z$ 数据相同，逆门不同。 |
| 只有成功旗，无相干控制或失败恢复 | 失败可以擦除输入，不能免费重复未知态。 |
| 有三维局部 Gram 图，无全局接续条件 | 只能实现所声明的有限比较，不能宣称三维容纳全部过程。 |
| 有内生性与组合性，无非交换对象选择 | 完整经典 Bayes 模型仍然存在。 |

**白话。**倒过来看，问题就很具体：只回到同一个起点，会不会把别的内容全抹掉？会。只看输入和输出的参照，能不能知道门怎样扭过来？不能。每一对分别选一份参照，能不能拼成同一个回路？也未必。新规则锁住的是同一来源、同一参照、同一条过程的二元对读；恢复多少内容，还要由这些内容实际保留了哪些关系来决定。

<a id="section-8"></a>

## 8. 两个观察者、顺序读出与整体内部的共同来源

<a id="sec-c122-observers"></a>

### 8.1 显式反向如何给出观察者之间的转换

### 命题 8.1（已认证共同来源的三角关系）

<a id="prop-c122-observer-transport"></a>

设已经在内部认证同一有限源 $H$、同一参考 $\sigma$，
以及各观察者的 CPTP 编码 $N_j:H\to K_j$（$j=A,B,C$）。
对 $j=A,B$，取指定的 Petz 回推 $P_j=P_{\sigma,N_j}$，并设
$\|P_jN_j-\operatorname{id}_H\|_\diamond\le e_j$。
统一定义 $T_{ji}=N_jP_i$（$i=A,B$，$j=A,B,C$），则

$$
\begin{aligned}
\|T_{BA}N_A-N_B\|_\diamond&\le e_A,
\end{aligned}
\tag{40}
$$

$$
\begin{aligned}
\|T_{CB}T_{BA}-T_{CA}\|_\diamond&\le e_B,
\end{aligned}
\tag{41}
$$

$$
\begin{aligned}
\|T_{AB}T_{BA}N_A-N_A\|_\diamond&\le\min\{2,e_A+e_B\}.
\end{aligned}
\tag{42}
$$

映射在各自可达支持上定义，或统一采用全空间 CPTP 补全。

**证明。**
前两个差分别展开为

$$
N_B(P_AN_A-\operatorname{id}),\qquad
 N_C(P_BN_B-\operatorname{id})P_A.
$$

第三式在 $N_AP_BN_BP_AN_A$ 中依次把
$P_BN_B$、$P_AN_A$ 换成恒等。
CPTP 前后复合收缩 diamond 距离，故三角不等式给出全部结论。

这里的三元结构与三维 Gram 提升不同：
它比较三位观察者之间两条转换路径，路径差由中间观察者的恢复误差控制。
在精确源内容上形成交换三角形，而不是宣称观察者空间中每一份私人记录都被覆盖。
通常 $T_{AA}\ne\operatorname{id}_{K_A}$；可保证的是
$T_{AA}N_A=N_A$ 的精确或近似版本。

### 命题 8.2（顺序读取的显式反向与误差累积）

给定参考相容链
$(H_0,\sigma_0)\xrightarrow{N_1}\cdots\xrightarrow{N_n}(H_n,\sigma_n)$，
令 $P_j=P_{\sigma_{j-1},N_j}$。则整链的 Petz 回推恰为
$P_1\cdots P_n$。
若每步 $\|P_jN_j-\operatorname{id}_{H_{j-1}}\|_\diamond\le e_j$，则

$$
\|P_1\cdots P_n N_n\cdots N_1-\operatorname{id}_{H_0}\|_\diamond
 \le\min\{2,\sum_j e_j\}.
$$

**证明。**
公式来自顺序互易。误差通过把最内层 $P_nN_n$ 换为恒等开始，
逐层望远镜展开；其余 CPTP 因子不能放大每一项。

不同起点不保证两个观察者的门词完全不同，也不保证它们必然趋近同一纯态。
相同量子通道可有许多不同门分解；不同门词也可能只差整体相位或辅助记录。
若两个状态承受同一酉序列，其迹距始终不变，
所以不存在由共同酉演化把全部不同输入压向一个共同吸引态的过程。
“逼近同一整体”须明确是扩大可读代数、逼近某个态，还是提高共同恢复精度。

### 8.2 没有全知观察者，能否认证交集

### 命题 8.3（内部记录的可认证性）

设 $\mathfrak M$ 是与内部规则相容的模型族，
$r(M)$ 为观察者记录，$q(M)$ 为希望确定的目标。
存在只依赖记录的函数 $f$，使 $q=f\circ r$，
当且仅当

$$
r(M)=r(M')\Longrightarrow q(M)=q(M').
$$

**证明。**
必要性由代入得到。反向，在记录像中对每个 $u$，
取任一 $r(M)=u$ 的模型并定义 $f(u)=q(M)$；
条件恰好保证这个定义与选择无关。

所以有限记录通常不能确定与另一观察者的*全部*交集。
但“必须完整包含对方才知道任何交集”过强：
双方可以持有一个已认证的共同经典寄存器 $X$，各自又有对方不知道的私人部门。
他们能认证 $X$，却没有任何一方完整包含另一方。
命题 [8.1](#prop-c122-observer-transport) 消费的正是这样的已认证有限共同来源；
它不利用转换公式凭空证明来源同一。

### 命题 8.4（相容有限窗口的共同状态）

给定递增含幺 $C^*$ 代数 $\mathcal A_1\subset\mathcal A_2\subset\cdots$，
以及相容状态 $\omega_{n+1}|_{\mathcal A_n}=\omega_n$，
则在 $\overline{\bigcup_n\mathcal A_n}$ 上存在唯一状态 $\omega$
延拓全部 $\omega_n$。

**证明。**
在并集上按所属窗口定义 $\omega(a)=\omega_n(a)$，
相容性保证良定义、线性、正性和归一化。
状态的 Cauchy–Schwarz 不等式给
$|\omega(a)|^2\le\omega(a^*a)\le\|a\|^2$，
因此唯一连续延拓到范数完备化，正性与单位值也被保留。

两条共尾的窗口链若限制自同一组相容数据，就给出同一个延拓状态。
这为“顺序投影、逼近共同整体”给出一种严格解释；
共尾性、相容性与内部可达性仍需要证据。
整体关系系统 $\Omega$ 与其上的一个状态泛函 $\omega$ 是不同类型的对象，
不能未经定义把二者写成同一个有限维波函数。

### 8.3 自指起点的局部复位与内容地址

### 命题 8.5（纯复位寄存器必将来源移到别处）

若等距 $V:H\to S\otimes E$ 对全部纯输入的 $S$ 约化态恒为
$\lvert s\rangle\langle s\rvert$，则存在等距 $W:H\to E$，使
$V\psi=s\otimes W\psi$。

**证明。**
纯约化态说明 $V$ 的全部像在 $\mathbb C s\otimes E$ 内。
令 $W=(\langle s\rvert\otimes I)V$ 即得分解；
$V^*V=I$ 给 $W^*W=I$。

因此自指观察者的一个寄存器可以回到相同起点，
而未知内容被转入同一整体中的其他记录。
若没有其他记录，却要求一个全局酉门把任意两个正交态送成同一态，
内积保持立即矛盾。
内容地址可以编码经典门描述与自描述协议；它不能把任意未知量子态的复制变为合法门。

### 8.4 原来的二次式与量子场直觉如何落地

对实数 $a,b$，

$$
a^2+xab+b^2=
 (a,b)\begin{pmatrix}1&x/2\\x/2&1\end{pmatrix}\binom ab.
$$

等于 $1$ 的曲线在 $x=0$ 时是圆；
$|x|<2$ 时是椭圆；
$x=2$ 时为 $(a+b)^2=1$，即两条平行直线。
$ab$ 是双线性项。
若 $u,v$ 是单位关系向量，则

$$
\|au+bv\|^2=a^2+b^2+2ab\operatorname{Re}\langle u,v\rangle.
$$

交叉项读取两方向之间的关系。
提升为 $M=(a,b)^{\mathsf T}(a,b)$ 后，整个式子是对 $M$ 的线性迹读取。
因此可以保留的画面是：*振幅上的二次关系，成为状态关系空间中的线性读数。*
本轮再把这种读取提升到带参考的矩阵比较几何。

场论中，方差
$\omega(A^2)-\omega(A)^2$ 描述状态对可观测量的二阶关系，
并不以实际已经发生读出为前提。
局域系统与探针的耦合可以诱导完全正读口和条件仪器，
这是把观察者放回物理系统内部的已有严格路径。 [15](#ref-fewsterverch2018)
但电子场与光子场的区分需要各自的场代数、时空表示和动力学。
光子中性且与其反粒子相同，两个物理偏振或正负频率项不能等同于
带正、负电荷的两种光子。 [16](#ref-tongqed)、[17](#ref-fermilabphoton)

有限矩阵不能精确满足 $[a,a^*]=I$，因为取迹会得到 $0=d$。
所以玻色场的产生、湮灭结构需要相应无限维表示与定义域；
局域因果性、能量条件、规范群、物质表示及相互作用也没有被 C122 的有限互易唯一决定。
本稿完成的是一个有限关系理论及其量子接口，没有完成标准模型的唯一重构。

**白话。**两个观察者各走自己的路，能比较的是内部已经认证的共同片段。对这块片段，先用自己的明确回推把内容找回，再换成对方的编码，三个人之间的路径误差也能算出来。不断扩大相容窗口，可以严格得到一个共同状态；不能只因都在整体里，就认定任意两条门串会汇成同一纯态。自指起点可以局部重现，内容则必须留在整体的其他关系里。

<a id="section-9"></a>

## 9. 本轮完成的理论与最终白话

<a id="sec-c122-synthesis"></a>

本轮形成的有限理论有四层：对象与概率接口确定哪些关系可称为量子关系；
二元互易唯一给出参考回推；
加权谱与残余交换子确定它保留的内容及误差；
标定、成功支路和完整控制决定它怎样实际执行。
四层在同一内部过程体系中连接，每个前件都有可指认的角色。

本轮不新增区别于通常量子力学的实验预测。
Petz 公式、近最优恢复、单调度量与幅度放大均属于已有理论；
文中把所需有限证明写全，并将其组织为一个可审查的候选。
新近的全局唯一性文献仅作为更大结构的外部定理引用。
有限误差常数是本文证明链的充分上界，没有声称最优或首创。

**白话。**整体里的一位观察者，先拿自己已经准备好的一份内容作参照，把它沿一条实际过程送出去。前后各有一个问题：一边问这份内容怎样分成两种可能，另一边问送出后还能读到什么。回头读的时候，仍然用同一份参照、同一条过程，只把两个问题的位置交换；要求两种读法相合，就把反推固定成了一条具体公式。它把参照送回原处，但其他内容能回来多少，要看途中是否还保住它们彼此可比较的关系。两份变化沿一个读口投下一条线，另外两个方向就能把这两份变化的关系补全；扩展到全部关系时，这幅图成为加权的椭球收缩。没有损失的方向留下来，能彼此接续成稳定的代数；有损失的方向则留下可计算的残余。两个观察者只要认证了同一片内容，就能靠各自的回推换一种表达，不必先站到整体之外。这样，公理落成了内部定义之间的一项相容要求；但哪些对象和门真的存在，仍然要由其他明确的关系条件和记录来承担，不能靠把它们改叫定义就一笔勾销。

<a id="section-10"></a>

## 10. 有限量子原子的实关系选择：前提与完整证明

<a id="sec-local-core"></a>

本附录自足重述前轮实球形二元块的局部选择步骤，说明主文复矩阵部门的一种来路。它是继承的对象接口，不是本轮另提一个候选。其范围是实球形二元正锥及下列动力标签条件；它没有证明这些条件由一般正核自动强制成立。这里由三方向乘积形成的中心单位记为 $\jmath$，以区别一般线性算子的符号。

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

<a id="eq-c122-local-spectator"></a>

$$
\boxed{[D_a,D_b]z=0\quad(z\perp a,b).}
\tag{43}
$$

这是完整向量等式。只比较 $z\cdot[D_a,D_b]z$ 没有约束力，因为反对称算子的该自比较总是零。

### 定理 10.4（三维选择）

<a id="thm-c122-local-three"></a>

上述条件强制 $\dim W=3$，且存在 $\kappa>0$，使

<a id="eq-c122-local-loop"></a>

$$
\begin{aligned}
[D_a,D_b]&=-\kappa[L_a,L_b],
\end{aligned}
\tag{44}
$$

<a id="eq-c122-local-square"></a>

$$
\begin{aligned}
D_a^2x&=\kappa\bigl((a\cdot x)a-\|a\|^2x\bigr),
\end{aligned}
\tag{45}
$$

<a id="eq-c122-local-triple"></a>

$$
\begin{aligned}
D_aD_bx&=\kappa\bigl((a\cdot x)b-(a\cdot b)x\bigr),
\end{aligned}
\tag{46}
$$

<a id="eq-c122-local-bracket"></a>

$$
\begin{aligned}
D_{D_a b}&=[D_a,D_b].
\end{aligned}
\tag{47}
$$

按 $D$ 选择取向后，$D_ab=\sqrt\kappa\,a\times b$。

**证明。**
标签线性及 $D_aa=0$ 给 $D_ab=-D_ba$，故 $x\cdot D_ab$ 是交替三形式。令

$$
B(a,b)x=(b\cdot x)a-(a\cdot x)b=[L_a,L_b]x.
$$

交换子 $[D_a,D_b]$ 反对称。式 [(43)](#eq-c122-local-spectator) 使它在 $\operatorname{span}(a,b)^\perp$ 上为零，并保持 $\operatorname{span}(a,b)$；二维反对称算子只有一个方向，所以它是 $B(a,b)$ 的实倍数。

这个倍数不能逐对自由选。取正交基 $e_i$，写 $[D_{e_i},D_{e_j}]=\lambda_{ij}B(e_i,e_j)$。在二元合成标签

$$
a=\sum_i e_i,\qquad b=\sum_i\left(i-\frac{n+1}{2}\right)e_i
$$

上展开，其每个基对系数都是非零的 $j-i$。合成对也必须有一个共同平面比例，比较基系数便得全部 $\lambda_{ij}=\lambda$。双线性将它扩到任意 $a,b$。

将交换子等式作用于 $a$ 并使用反对称性，得

$$
\|D_ab\|^2=-\lambda\bigl(\|a\|^2\|b\|^2-(a\cdot b)^2\bigr).
$$

非平凡性排除 $\lambda=0$，故 $\lambda=-\kappa<0$，并得 [(45)](#eq-c122-local-square)。极化该平方式，加上交换子式，给 [(46)](#eq-c122-local-triple)；再由 $D_{D_ab}x=-D_xD_ab$ 得 [(47)](#eq-c122-local-bracket)。

取正交单位 $u,v$，令 $w=D_uv/\sqrt\kappa$。上式说明 $u,v,w$ 正交归一，且

$$
D_w=\sqrt\kappa(vu^{\mathsf T}-uv^{\mathsf T}),\qquad
 D_w^2=-\kappa(P_u+P_v).
$$

另一方面，式 [(45)](#eq-c122-local-square) 给 $D_w^2=\kappa(P_w-I)$。因此

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

<a id="eq-c122-local-product"></a>

$$
(\alpha,a)(\beta,b)
 =(\alpha\beta+a\cdot b,\alpha b+\beta a+\jmath(a\times b)).
\tag{48}
$$

这里的点积、叉积作复双线性延伸。

### 定理 10.5（内部复代数及最小振幅）

<a id="thm-c122-local-complex"></a>

式 [(48)](#eq-c122-local-product) 给出实八维结合 $*$-代数，伴随为逐分量复共轭，自伴部恰为原来的 $V$。对于正向正交基，

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

这是定理 [10.4](#thm-c122-local-three) 的三重积恒等式。共轭将 $\jmath$ 变号，交换向量次序也使叉积变号，故 $(xy)^*=y^*x^*$。直接计算得 $e_1e_2=\jmath e_3$，从而 $e_1e_2e_3=\jmath$，没有再添独立复方向。

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

自伴元 $sI+r\cdot\sigma$ 的特征值是 $s\pm\|r\|$，所以构造后的矩阵正锥恰好恢复原来的 $C$。其归一化截面是三维球，极点是球面；概率与纯态的严格对应见第 [6](#sec-c122-qm) 节。

**白话。**先规定两份方向怎样比较，再比较沿它们前后运动的小回路。回路不能暗中推动和这两个方向都垂直的完整参考；对合成方向也这样要求，两个方向就会带出第三个，而且三个已经覆盖整个二元块。把三个方向按顺序相乘，会得到一个再乘自己就反号的内部关系，它承担复数的作用。这样的复结构有了明确来路；观察者的记录守恒接下来才有可用的物理振幅空间。

有限系统类还允许独立复合以及非零投影支持的角代数。由第 [6](#sec-c122-qm) 节的复合定理，$N$ 个二元原子给 $M_{2^N}(\mathbb C)$。对任意 $d\le2^N$，取秩 $d$ 的投影 $p$，角代数 $pM_{2^N}(\mathbb C)p$ 同构于 $M_d(\mathbb C)$，单位为 $p$。因此在这项系统闭包约定下，全部有限复量子系统均得到构造。支持限制与观察窗口的保单位嵌入是两类接口，不能把改变单位的角嵌入误作同一个共同来源接缝。

<a id="references"></a>

## 参考文献

<a id="ref-repo-fib"></a>

### [1]

The Omega Institute, *FIB Atom Recursive Holographic Boundary Geometry,
Continuation III, Appendix III*, §§136–140.
固定提交 `fc2bf058b103a58ec9ef904e17faba66ba94e383`，
2026-11-03 16:43:35 UTC。
[不可变理论源码](https://github.com/the-omega-institute/trureturing/blob/fc2bf058b103a58ec9ef904e17faba66ba94e383/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md)。
本稿核读实际共同分区、终端因子、确定性路径、行列式区间与 §140 的未完成前件；
没有把条件降秩路线改写成无条件结论。

<a id="ref-repo-petz"></a>

### [2]

The Omega Institute，同一固定提交中的量子恢复源码：
[ReferencePetzChannel.lean](https://github.com/the-omega-institute/trureturing/blob/fc2bf058b103a58ec9ef904e17faba66ba94e383/D5/S3/Quantum/Recovery/ReferencePetzChannel.lean)，
[CanonicalPetzStability.lean](https://github.com/the-omega-institute/trureturing/blob/fc2bf058b103a58ec9ef904e17faba66ba94e383/D5/S3/Quantum/Recovery/CanonicalPetzStability.lean)，
[PetzPhysicalWeightedCoordinates.lean](https://github.com/the-omega-institute/trureturing/blob/fc2bf058b103a58ec9ef904e17faba66ba94e383/D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.lean)，
[PetzSchwarzRecovery.lean](https://github.com/the-omega-institute/trureturing/blob/fc2bf058b103a58ec9ef904e17faba66ba94e383/D5/S3/Quantum/Recovery/PetzSchwarzRecovery.lean)，
[FiniteKrausReversibility.lean](https://github.com/the-omega-institute/trureturing/blob/fc2bf058b103a58ec9ef904e17faba66ba94e383/D5/S3/Quantum/Recovery/FiniteKrausReversibility.lean)。
特别定位：`completed_reference_petz_channel`、
`supported_entropy_defect_fixed_petz_trace_stability`、
`scalar_products_construct_left_inverse`。
本稿核读源码及其前提，未重新执行整个 Lean 构建或项目审计。

<a id="ref-petz1986"></a>

### [3]

D. Petz, “Sufficient subalgebras and the relative entropy of states of a von Neumann algebra”,
*Communications in Mathematical Physics* **105**, 123–131 (1986).
[doi:10.1007/BF01212345](https://doi.org/10.1007/BF01212345)。
另见 D. Petz, “Sufficiency of channels over von Neumann algebras”,
*Quarterly Journal of Mathematics* **39**(1), 97–108 (1988),
[doi:10.1093/qmath/39.1.97](https://doi.org/10.1093/qmath/39.1.97)。

<a id="ref-jencova2024"></a>

### [4]

A. Jen
v{c}ov
'a, “Recoverability of quantum channels via hypothesis testing”,
*Letters in Mathematical Physics* **114**, 31 (2024).
[doi:10.1007/s11005-024-01775-2](https://link.springer.com/article/10.1007/s11005-024-01775-2)。
§2.3 给出加权配对中的 Petz 伴随与参考返回；本稿不把一般恢复保证无条件改配给未旋转的 Petz。

<a id="ref-retrodiction2026"></a>

### [5]

J. Surace, C. Li and F. Buscemi,
“Inevitability of the Petz transpose map”,
[arXiv:2610.40158v1](https://arxiv.org/html/2610.40158v1)，
2026 年 10 月 29 日提交的预印本。
Theorem 1 在全部有限全矩阵参考对象上，由对合、顺序、并行及酉逆条件唯一刻画 Petz 指派；
本文只引用其全局唯一性，不将其视为无量子对象前提的量子起源定理。

<a id="ref-barnum2026"></a>

### [6]

H. Barnum and E. Knill,
“Reversing quantum dynamics with near-optimal quantum and classical fidelity”,
*Journal of Mathematical Physics* **43**, 2097–2106 (2002)；
[arXiv:quant-ph/0004088v2](https://arxiv.org/pdf/quant-ph/0004088v2)，
2026 年 1 月 18 日修订。
新版 Theorem 3 及文末修订说明修复多状态平均证明；
本文给出的单参考态证明独立写全。原论文
[doi:10.1063/1.1459754](https://doi.org/10.1063/1.1459754)。

<a id="ref-ng2010"></a>

### [7]

H. K. Ng and P. Mandayam,
“A simple approach to approximate quantum error correction based on the transpose channel”,
*Physical Review A* **81**, 062342 (2010).
[arXiv:0909.0931v2](https://arxiv.org/pdf/0909.0931v2)；
[doi:10.1103/PhysRevA.81.062342](https://doi.org/10.1103/PhysRevA.81.062342)。
本文引用 Theorem 3/Corollary 4 的误差指标时明确采用其最坏纯态平方保真度损失，
不把该指标替换为 diamond 距离。

<a id="ref-petz1996"></a>

### [8]

D. Petz, “Monotone metrics on matrix spaces”,
*Linear Algebra and its Applications* **244**, 81–96 (1996).
[doi:10.1016/0024-3795(94)00211-8](https://doi.org/10.1016/0024-3795(94)00211-8)。
本文采用 $f(t)=\sqrt t$ 的一项具体度量，并直接证明所需收缩，不依赖完整分类。

<a id="ref-hansen2011"></a>

### [9]

F. Hansen, “Convexity of quantum $\chi^2$-divergence”,
[arXiv:1102.2989v2](https://arxiv.org/pdf/1102.2989v2) (2011).
第 2–3 页给出单调度量函数及 $\chi^2_\alpha$ 定义；
$\alpha=1/2$ 对应本稿的平方根权重。

<a id="ref-gilyen2022"></a>

### [10]

A. Gily
'en, S. Lloyd, I. Marvian, Y. Quek and M. M. Wilde,
“Quantum algorithm for Petz recovery channels and pretty good measurements”,
*Physical Review Letters* **128**, 220502 (2022).
[arXiv:2006.16924v2](https://arxiv.org/html/2006.16924v2)；
[doi:10.1103/PhysRevLett.128.220502](https://doi.org/10.1103/PhysRevLett.128.220502)。
逆完整实现、参考滤片与相干放大均须有明确访问资源。

<a id="ref-bhmt2002"></a>

### [11]

G. Brassard, P. H{
o}yer, M. Mosca and A. Tapp,
“Quantum Amplitude Amplification and Estimation”,
*Contemporary Mathematics* **305**, 53–74 (2002).
[arXiv:quant-ph/0005055](https://arxiv.org/abs/quant-ph/0005055)。
本稿重证已知成功率情形的衰减与精确放大，并明确其在整个未知源空间上的作用。

<a id="ref-choi1975"></a>

### [12]

M.-D. Choi, “Completely positive linear maps on complex matrices”,
*Linear Algebra and its Applications* **10**(3), 285–290 (1975).
[doi:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。

<a id="ref-stinespring1955"></a>

### [13]

W. F. Stinespring, “Positive functions on $C^*$-algebras”,
*Proceedings of the American Mathematical Society* **6**(2), 211–216 (1955).
[doi:10.1090/S0002-9939-1955-0069403-4](https://doi.org/10.1090/S0002-9939-1955-0069403-4)。
本文只需正文给出的有限矩阵构造。

<a id="ref-busch2003"></a>

### [14]

P. Busch, “Quantum states and generalized observables: a simple proof of Gleason's theorem”,
*Physical Review Letters* **91**, 120403 (2003).
[arXiv:quant-ph/9909073v3](https://arxiv.org/abs/quant-ph/9909073v3)。
本文效果可加证明包含 qubit；赋值域是全部效果，而不只是锐投影。

<a id="ref-fewsterverch2018"></a>

### [15]

C. J. Fewster and R. Verch, “Quantum fields and local measurements”,
[arXiv:1810.06512v3](https://arxiv.org/abs/1810.06512v3) (2020).
内部系统–探针耦合、完全正诱导读口、条件仪器及因果顺序接续。

<a id="ref-tongqed"></a>

### [16]

D. Tong, *Quantum Field Theory*, Chapter 6, “Quantum Electrodynamics”.
[作者课程原文](https://davidtong.org/pdfs/teaching/quantum-field-theory/qft6.pdf)。
电磁场的规范结构、量子化与两个物理偏振。

<a id="ref-fermilabphoton"></a>

### [17]

Fermilab, “Charge, Spin and Mass of Fundamental Particles”,
*Physics Questions People Ask Fermilab*.
[机构原始答复](https://www.fnal.gov/pub/science/inquiring/questions/mass_information.html)。
仅用于光子中性、自共轭的基本区分，不采用该历史页面的其他实验数字。

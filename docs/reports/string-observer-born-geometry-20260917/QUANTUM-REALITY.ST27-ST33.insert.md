
---

<a id="string-observer-recovery-record-holonomy"></a>

# 可恢复漏出、带记录的几何运输与全局通道

## 接续 ST0–ST26 的增订 ST27–ST33

**范围。** 本增订固定有限维、正定内积的复 Hilbert 空间和确定的实验权限。ST27–ST31给出矩阵与通道证明；ST32给出一个球面子丛和全局 CPTP 编码的显式构造。所有通道等式允许张量任意不参与控制的有限参考系统。概率不依赖未知逻辑输入，除非明确写出相反情况。钻石距离一律采用一半钻石范数的约定，不做后选择。

**来源与证明状态。** 正交 syndrome 恢复和 Knill–Laflamme 条件是既有纠错理论；读取环境标签后纠正随机酉噪声也有既有文献。本增订把它们接到ST19的漏出、ST15的路径连接和ST23的全局图障碍上，并推导有损经典记录下的精确误差公式。没有全球新颖性主张。伴随两个 Lean 文件提供8个公开声明的候选证明体，不含 `sorry`，但本轮没有 Lean/lake 可执行环境，未编译、未准入。特别是钻石范数最优性、CPTP 扩展及 Chern 数均未被这8个声明完整形式化。

基线：`dev@79bbae415ffa954c8145cc83110b5c5dab149fdd`；延续PR #8340已有ST0–ST26。候选 Lean 工具链目标为仓库当次读取的 `leanprover/lean4:v4.33.0`。仓内 `FiniteKrausInstrumentBornMarginal` 提供真实 Kraus/Born 边缘公式；`FutureStatisticsEquivalence` 给出未来算子系统的不可区分性判据。它们没有自动证明本增订的恢复与全局通道结论。

## ST27．离开一个固定编码空间，不等于逻辑信息已经不可恢复

### 定义 ST27.1：正交错误副本

设逻辑空间为 $V=\mathbb C^d$，物理输出为 $\mathcal H=\mathbb C^n$，$d\ge1$。取有限非空索引集 $J$ 和矩阵 $S_j:V\to\mathcal H$，满足

$$
S_j^\dagger S_k=\delta_{jk}I_V.
\tag{ST27.1}
$$

令 $P=\sum_jS_jS_j^\dagger$。直接相乘得 $P=P^\dagger=P^2$。因此$n\ge d|J|$；这些索引是逻辑信息的正交副本标签，也称错误综合征（syndrome）。它们不是逻辑输入的复制：一次实际状态只占据一个联合编码，并未产生独立的未知态副本。

对任意 syndrome 密度矩阵 $\sigma$，定义

$$
\mathcal N_\sigma(\rho)
=\sum_{j,k}\sigma_{jk}S_j\rho S_k^\dagger.
\tag{ST27.2}
$$

对固定复位密度态 $\tau$，定义完整恢复

$$
\mathcal D(X)
=\sum_jS_j^\dagger X S_j+
\operatorname{tr}[(I-P)X]\tau.
\tag{ST27.3}
$$

### 定理 ST27.2：相干 syndrome 的精确恢复

$\mathcal N_\sigma$ 与 $\mathcal D$ 均为 CPTP，而且

$$
\boxed{\mathcal D\mathcal N_\sigma=\mathrm{id}_V.}
\tag{ST27.4}
$$

恢复不要求读取 $\sigma$，也不要求它在指定标签基下对角。

**证明。** 定义等距$J_0:V\otimes\mathbb C^{|J|}\to\mathcal H$为$J_0(v\otimes|j\rangle)=S_jv$。式(ST27.1)保证等距性，故$\mathcal N_\sigma(\rho)=J_0(\rho\otimes\sigma)J_0^\dagger$完全正且保迹。

恢复第一项由Kraus矩阵$S_j^\dagger$构造。第二项是正效果$I-P$后制备$\tau$的映射，故也完全正。两部分的迹相加为$\operatorname{tr}X$。

对任意$\sigma,\rho$矩阵（此处甚至不需正性），

$$
\sum_iS_i^\dagger\mathcal N_\sigma(\rho)S_i
=\sum_{i,j,k}\sigma_{jk}\delta_{ij}\delta_{ki}\rho
=\operatorname{tr}(\sigma)\rho.
$$

$\mathcal N_\sigma$的输出支持在$P$内，故复位项为零。密度态的迹为一，得到结论。这个代数恒等式是伴随`OrthogonalSyndromeDecoding.lean`的主候选声明。∎

### 例 ST27.3：漏出参数为一但恢复误差为零

取$\mathcal H=V\otimes\mathbb C^2$，旧编码$S_0v=v\otimes|0\rangle$，噪声实际把它送到$S_1v=v\otimes|1\rangle$。相对于旧投影$P_0=S_0S_0^\dagger$，ST19意义的漏出为$\lambda=1$。然而丢弃第二因子就精确恢复$\rho$。

所以ST20对“压回旧空间并复位”的误差上界，没有声称是所有恢复方法的最优下界。能否恢复，取决于被允许访问的输出系统和 syndrome 信息。如果这些自由度实际不可访问，则不能使用这里的恢复器。[ST27-KL][ST27-EA]

## ST28．保留结果记录的恢复条件

### 命题 ST28.1：带公开结果的 Knill–Laflamme 条件

设原输入已经限制到逻辑空间，仪器分支为

$$
\mathcal I_a(\rho)=\sum_\ell E_{a\ell}\rho E_{a\ell}^\dagger,
\qquad \sum_{a,\ell}E_{a\ell}^\dagger E_{a\ell}=I.
$$

允许恢复器读取结果$a$。固定常数$p_a\ge0$、$\sum_ap_a=1$。存在逐结果CPTP恢复$\mathcal R_a$满足

$$
\mathcal R_a\mathcal I_a(\rho)=p_a\rho\quad\forall\rho
\tag{ST28.1}
$$

当且仅当对每个$a$存在半正定标量矩阵$c^{(a)}$，使

$$
\boxed{E_{a\ell}^\dagger E_{ak}=c^{(a)}_{\ell k}I,\qquad
\operatorname{tr}c^{(a)}=p_a.}
\tag{ST28.2}
$$

公开标签$a$之间不需交叉条件。如果$a$被删除、恢复器只能看到无标签通道，标准条件必须检查所有$(a,\ell),(b,k)$交叉项。这是对经典纠错条件的带记录应用。[ST27-KL]

**证明。** 充分性：对$c^{(a)}$酉对角化，同时作Kraus基变换，得到$F_{aj}^\dagger F_{ak}=d_{aj}\delta_{jk}I$。$d_{aj}>0$时令$S_{aj}=F_{aj}/\sqrt{d_{aj}}$，零权重算子本身为零。ST27的解码对$\sum_jd_{aj}S_{aj}\rho S_{aj}^\dagger$给出$p_a\rho$，并可在补空间CPTP扩展。$p_a=0$时该分支恒为零。

必要性：写恢复Kraus为$R_{at}$。复合通道$p_a\mathrm{id}$的Choi矩阵秩至多一，故每个$R_{at}E_{a\ell}=z_{at\ell}I$（零分支也成立）。利用恢复保迹，

$$
E_{a\ell}^\dagger E_{ak}
=\sum_tE_{a\ell}^\dagger R_{at}^\dagger R_{at}E_{ak}
=\left(\sum_t\overline{z_{at\ell}}z_{atk}\right)I.
$$

括号构成Gram矩阵，故半正定；分支迹给出$p_a$。∎

这里的$p_a$不依赖未知逻辑态。如果某公开结果携带未知态的信息，同时要求每个结果后都恢复完整未知态，需要单独满足无信息无扰动条件，不能由“已知结果”自动获得。

## ST29．恢复器需要保存路径上的逻辑作用

### 定理 ST29.1：不同 syndrome 的已知运输可以精确补偿

令$V_j$是逻辑酉矩阵，可以表示指定闭路的holonomy，或包含动力学相位的已知完整逻辑演化。取

$$
\widetilde S_j=S_jV_j.
$$

则$\widetilde S_j^\dagger\widetilde S_k=\delta_{jk}I$。采用$\widetilde S_j$构造的ST27解码精确恢复全部逻辑态。

但如果噪声syndrome已去相干、概率为$p_j$，且使用未补偿运输的旧解码$S_j^\dagger$，则得到

$$
\boxed{\Phi(\rho)=\sum_jp_jV_j\rho V_j^\dagger.}
\tag{ST29.1}
$$

**证明。** 先计算正交性，再代入ST27。对于对角$\sigma$，旧解码消去不同标签之间的块，仅保留上述各个逻辑作用。∎

### 命题 ST29.2：无标签混合何时仍为一个酉演化？

若$p_j>0$的分支均作用在相同有限逻辑空间，则$\Phi=\operatorname{Ad}_V$当且仅当每个受支持分支满足$V_j=e^{i\alpha_j}V$。

**证明。** 若相差相位，共轭通道相同。反向利用Choi矩阵：$\Phi$的Choi矩阵是$\sum_jp_j|V_j\rangle\!\rangle\langle\!\langle V_j|$，酉通道的Choi矩阵秩一。正权重排除非共线向量，故$V_j=c_jV$；酉性给出$|c_j|=1$。∎

这说明瞬时可纠正性和整条路径的恢复是不同问题。连接变化产生的syndrome相关逻辑作用必须保留或补偿。Lanka、Garcia-Nila、Brun在2026年3月的预印本中利用连续测量记录识别瞬时syndrome并途中调整holonomic路径，提供了直接相邻的物理实现方向。本文没有复现该文的连续测量动力学或容错阈值。[ST27-Steering]

## ST30．syndrome记录不完整时的精确最优误差

### 假设 ST30.1：相位型路径与有损经典记录

逻辑空间为一个量子比特。分支$j$以输入无关概率$p_j$出现，并实施

$$
V_j=\operatorname{diag}(z_j,1),\qquad |z_j|=1.
$$

记录器只输出$r$，其条件概率为$T(r|j)$，$\sum_rT(r|j)=1$。一切额外syndrome量子自由度此时已被删除。可访问通道为

$$
\mathcal M_T(\rho)=\sum_r|r\rangle\langle r|\otimes
\sum_jp_jT(r|j)V_j\rho V_j^\dagger.
\tag{ST30.1}
$$

定义

$$
q_r=\sum_jp_jT(r|j),\qquad
c_r=\sum_jp_jT(r|j)z_j,\qquad
s_T=\sum_r|c_r|\le1.
\tag{ST30.2}
$$

允许任意作用在“记录+量子比特”上的确定性CPTP恢复，最终输出一个量子比特；目标是恢复恒等通道，不要求输出原记录。不知道$T,p,z$时的估计成本另行处理。

### 定理 ST30.2：带粗记录的最优恢复公式

有

$$
\boxed{
\inf_{\mathcal R\ {\mathrm{CPTP}}}
\frac12\|\mathcal R\mathcal M_T-\mathrm{id}\|_\diamond
=\frac{1-s_T}{2}
=\frac12\left(1-\sum_r\left|\sum_jp_jT(r|j)z_j\right|\right).
}
\tag{ST30.3}
$$

**证明：可达到的上界。** $c_r\ne0$时，根据记录施加$W_r=\operatorname{diag}(\overline c_r/|c_r|,1)$；$c_r=0$时任选相位。分支的对角元原来乘$q_r$，非对角元乘$c_r$，补偿后非对角元乘$|c_r|$。删除$r$得到

$$
\mathcal D_{s_T}(\rho)=
\begin{pmatrix}\rho_{00}&s_T\rho_{01}\\s_T\rho_{10}&\rho_{11}\end{pmatrix}
=(1-e)\rho+eZ\rho Z,
\quad e=(1-s_T)/2.
$$

三角不等式和通道钻石范数为一给出半钻石距离至多$e$。输入$|+\rangle$时$Z|+\rangle=|-\rangle$，两态正交，迹距离为$e$，所以这个上界本身精确。

**证明：任意恢复的下界。** 对输入$\rho_\pm=|\pm\rangle\langle\pm|$，$\mathcal M_T(\rho_+)-\mathcal M_T(\rho_-)$的第$r$块为

$$
\begin{pmatrix}0&c_r\\\overline c_r&0\end{pmatrix},
$$

迹距离因此恰为$s_T$。若某恢复与恒等通道的半钻石距离为$e'$，则每个$\rho_\pm$的恢复误差至多$e'$。迹距离三角不等式及CPTP收缩性给出

$$
1=D(\rho_+,\rho_-)\le2e'+s_T.
$$

故$e'\ge(1-s_T)/2$。上下界相等，得到结论。∎

这个证明与允许的参考系统相容：下界只需无参考的两态见证，上界是通道钻石范数界。环境辅助纠错和相位阻尼恢复有既有研究；本节给出此规定记录模型下的显式优化与证明，不以有限检索宣称首次得到相同公式。[ST27-EA][ST27-BO]

### 推论 ST30.3：精确恢复的最小确定性记录

$e_*=0$当且仅当对于每个$q_r>0$的记录，所有$p_jT(r|j)>0$的$z_j$都相同。证明为复数三角不等式的取等条件。

若记录是确定性函数$r=f(j)$，精确恢复至少需要与正概率分支中不同$z_j$的数量一样多的记录值，按相同$z_j$分类即可达到。这是规定分支模型和权限下的记录数下界，不是普适量子存储维数定理。

### 推论 ST30.4：记录粗化只能降低可恢复性

记录再经过随机粗化$Q(s|r)$时，$c'_s=\sum_rQ(s|r)c_r$。故

$$
\sum_s|c'_s|\le\sum_r|c_r|,
\qquad e_*'\ge e_*.
\tag{ST30.4}
$$

同样的底层演化，仅改变可访问记录，就可能改变最优恢复误差。

### 例 ST30.5：一个记录比特可以决定能否完全恢复

取$p_0=p_1=1/2$、$z_0=1,z_1=-1$。保留完整$j$时$s_T=1$、$e_*=0$；完全忘记$j$时$c=0$、$e_*=1/2$。每个分支自身都是可逆酉演化，损失来自恢复前删除了区分这两个分支的信息。

一般两分支取$z_0=u,z_1=v$、概率$1-p,p$，则

$$
\boxed{1-| (1-p)u+pv |^2=p(1-p)|u-v|^2.}
\tag{ST30.5}
$$

这条精确代数式及$0<p<1$时的单位可见度判据，是`TwoSyndromePhaseDefect.lean`的候选形式化范围。它未在Lean中证明(ST30.3)的完整优化。

## ST31．有限记录分辨率与后续实验预算

### 定理 ST31.1：相位分箱给出二次精度界

将单位圆分为$K\ge2$个等宽相位箱，每箱只保存箱号。对箱中心相位$\vartheta_r$，每个所属相位距它不超过$\delta=\pi/K\le\pi/2$，所以

$$
\operatorname{Re}(e^{-i\vartheta_r}c_r)\ge q_r\cos\delta.
$$

从而

$$
\boxed{e_*\le\frac{1-\cos(\pi/K)}2\le\frac{\pi^2}{4K^2}.}
\tag{ST31.1}
$$

**证明。** 对箱内各分支按正权重求和，利用$|c_r|$大于实部；再对$r$求和并用$1-\cos x\le x^2/2$。∎

这是一个由明确分箱构造实现的统一上界；它没有声称该分箱对所有分布最优。它允许非均匀分支概率和空箱。相位谱、分箱权限及校准成本仍是明确输入。

### 命题 ST31.2：带误差的syndrome解码与记录损失可合并

设实际一段过程$\widetilde{\mathcal M}$在同一输入/输出载体上，与ST30模型相距

$$
\frac12\|\widetilde{\mathcal M}-\mathcal M_T\|_\diamond\le\epsilon.
$$

采用ST30的恢复，得到

$$
\frac12\|\mathcal R\widetilde{\mathcal M}-\mathrm{id}\|_\diamond
\le\epsilon+e_*.
\tag{ST31.2}
$$

证明是通道后复合的收缩性与三角不等式。有限轮经典自适应实验可逐段替换，安全总预算为

$$
\min\{1,\sum_j\sup_h(\epsilon_j(h)+e_{*,j}(h))\}.
$$

这需要每段模型、恢复和历史条件均明确，并且有效起点确实是对应逻辑编码。不能在丢失全部syndrome后继续把未获知的$j$用作控制输入。

## ST32．全局向量框的拓扑障碍，不排除全局CPTP编码

ST23排除了非零第一Chern数子丛的单一全局等距框。本节给出一个严格的能力区别：全局通道可以存在，即使全局纯态向量框不存在。

### 定理 ST32.1：恒定能隙下的全局可恢复通道

取参数$\boldsymbol n\in S^2$和秩一投影

$$
p(\boldsymbol n)=\tfrac12(I+\boldsymbol n\cdot\boldsymbol\sigma),
\qquad
P(\boldsymbol n)=p(\boldsymbol n)\otimes I_2.
$$

物理Hamiltonian取$H(\boldsymbol n)=\Delta(\boldsymbol n\cdot\boldsymbol\sigma)\otimes I_2$，$\Delta>0$。正能级子空间$E$秩二、物理能隙恒为$2\Delta$，按ST25的连接与定向规范其第一Chern数是$-2$。因此不存在全局连续等距$U:S^2\to\operatorname{Mat}_{4\times2}(\mathbb C)$以像$E_{\boldsymbol n}$作为编码。

然而，下列通道全局光滑且精确可恢复：

$$
\boxed{\mathcal E_{\boldsymbol n}(\rho)=p(\boldsymbol n)\otimes\rho,
\qquad\mathcal D=\operatorname{Tr}_{\rm first},
\qquad\mathcal D\mathcal E_{\boldsymbol n}=\mathrm{id}.}
\tag{ST32.1}
$$

**证明。** 局部纯态框为ST25的$u_N,u_S$。对$E$取$U_N=u_N\otimes I_2$、$U_S=u_S\otimes I_2$，连接为原线丛连接乘$I_2$，曲率迹为原来的两倍，故$C_1=-2$。ST23证明全局等距框不存在。

另一方面，$p$是全局光滑矩阵。编码有全局光滑Kraus家族

$$
K_a(\boldsymbol n)v=(p(\boldsymbol n)|a\rangle)\otimes v,\qquad a=0,1.
$$

它们满足$\sum_aK_a^\dagger K_a=\operatorname{tr}(p^2)I=I$，且$\sum_aK_a\rho K_a^\dagger=p^2\otimes\rho=p\otimes\rho$。偏迹是CPTP且$\operatorname{tr}p=1$，所以复合为恒等。∎

该例没有构造全局单Kraus纯态框。局部的Kraus族可以在参数空间混合，编码通道本身却是全局光滑的。每点制备$p(\boldsymbol n)$需要物理装置及该参数的访问权；定理没有宣称参数未知时可免费制备。

### 命题 ST32.2：一个标量线丛扭转可对受限逻辑实验不可见

对任意线丛$L$，$\operatorname{End}(L\otimes\mathbb C^d)$有规范的全局矩阵代数描述，因为局部框过渡$e^{i\alpha}I_d$的共轭作用为恒等。乘在全部逻辑分量上的同一相位，不改变密度态或普通CPTP过程。

若实验进一步允许两条参数路径的相干叠加，并保留可比较的路径参考，相对标量holonomy可以重新成为可测量量。这时实验语言已经扩大，不能沿用前一个受限可观测等价。ST32并不否定Berry相位或ST23的向量框障碍；它精确区分了向量表示、密度通道和含路径参考的实验。

## ST33．与相对论、弦有效理论及形式化源的连接

本增订得到三个不同的判据：离开旧编码子空间的几何漏出；在给定访问权限下能否恢复未知逻辑态；把整个参数路径连同记录与参考保留下来时能否恢复逻辑演化。三者不相互自动等同。

Lanka等2026年预印本使“记录syndrome并调整几何路径”成为直接的物理研究入口。[ST27-Steering] Lacambra等2026年4月预印本用量子参考系讨论Abelian格点规范理论中的Gauss-law codes和vacuum codes，提供“规范约束与可纠错逻辑子系统”相邻而具体的输入；本卷尚未将其所有模型形式化。[ST27-Gauss]

接入弦场论时，应先指定物理正内积空间、允许操作和有效模型，之后才适用这些恢复定理。BV一致性保留规范恒等式，不能替代syndrome可访问性。这里的参数曲率仍没有被同一化为时空Einstein曲率，也没有导出Newton常数。

**候选形式化覆盖。**

`D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding.lean`：公开5个声明，证明真实矩阵和构造的syndrome编码/解码恒等式，以及逐syndrome酉运输后的恢复。它对任意矩阵成立，物理CP延拓仍由ST27普通证明承担。

`D5/S3/Quantum/Recovery/TwoSyndromePhaseDefect.lean`：公开3个声明，证明两相位可见度缺陷、非零权重时单位可见度与相位相等的等价，以及相反相位例子。

两个同名Scribe与Blueprint阅读稿逐项列出声明和边界。数学最优性、参考系统上的通道范数、全局丛与Chern数只在正文中证明，不能据候选Lean的局部覆盖把整章称为kernel-verified。

## ST27–ST33 参考文献

[ST27-KL]: https://doi.org/10.1103/PhysRevA.55.900 "E. Knill and R. Laflamme, Theory of Quantum Error-Correcting Codes; Phys. Rev. A 55, 900 (1997), DOI 10.1103/PhysRevA.55.900. Classical correction conditions and syndrome factorization."
[ST27-BO]: https://arxiv.org/abs/0907.5391 "C. Beny and O. Oreshkov, General Conditions for Approximate Quantum Error Correction and Near-Optimal Recovery Channels, Phys. Rev. Lett. 104, 120501 (2010). Complementary-channel optimization is background, not a substitute for the direct proof in ST30."
[ST27-EA]: https://arxiv.org/abs/1110.4806 "B. Trendelkamp-Schroer, J. Helm and W. T. Strunz, Environment-Assisted Error Correction of Single-Qubit Phase Damping, Phys. Rev. A 84, 062314 (2011). Prior phase-damping/environment-assisted correction mechanism and mixed-environment caveats."
[ST27-Steering]: https://arxiv.org/html/2603.02552v1 "A. Lanka, J. Garcia-Nila and T. A. Brun, Steering paths mid-flight for fault-tolerance in measurement-based holonomic gates, arXiv:2603.02552v1 (3 March 2026), especially III.1–III.4. Preprint status retained."
[ST27-Gauss]: https://arxiv.org/abs/2604.06087 "J. P. Lacambra, A. Chatwin-Davies, M. Honda and P. A. Hoehn, Gauss law codes and vacuum codes from lattice gauge theories, arXiv:2604.06087 (April 2026). Abstract-level scope checked; not an input to the finite matrix proofs."
[ST27-Subbundle]: https://arxiv.org/abs/2503.17163 "M. A. Oancea, T. B. Mieling and G. Palumbo, Quantum geometric tensors from sub-bundle geometry, Quantum 10, 1965 (2026). General ambient/sub-bundle geometry belongs to the cited work."

---

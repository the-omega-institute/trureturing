# 旧比较不动，新历史续添

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

AURIC 量子关系研究

从二元日志核重建量子正关系

C129

新历史先接上旧记录能表达的部分；

还没有表达出来的部分，只补一条正交余边。

$$
\boxed{K_{Lh}=\begin{pmatrix}
 G&Gc\\ c^*G&c^*Gc+|r|^2
 \end{pmatrix},\qquad G=K_L.}
$$

从空表开始，每个有限比较表都允许这样的续写。
不先给历史向量空间、内积、正单位或微移中心。复数值二元比较和同一原始标签域仍是前件；Hilbert 空间由相容的有限关系构造。

日志的先后、独立关系的增长、三角相位的定向分别证明。在酉或等距描述下，完整过程保留输入区别；这不等于每个局部日志寄存器只能递增。

固定源码：`8e15c484cf57`
提交时点：2026-11-04 16:25:41，Asia/Singapore
对应 2026-11-04 08:25:41 UTC

自包含工作稿：定义、定理、证明、反例与几何

## 摘要与回溯位置

本轮沿 C128 的互补微移判据继续回溯。上一轮预先给复向量空间和半双线性比较，再由一中心的非负实余量选择 Hermitian 正性；这轮只先给历史标签集合 $X$ 与固定二元比较 $K:X\times X\to\mathbb C$。唯一候选要求：每次向有限列表 $L$ 加入一个标签 $h$，新表都能保留旧块 $G=K_L$，并写成封面的一条续写式。系数 $c,r$ 可以依赖本次有限上下文，不改动任何已经指定的比较值。

该式从空表归纳给所有有限表的 Hermitian 正性；反向，含零和奇异边界的 Schur 补证明每个正表都有这样的续写。自由复线性包络随后才被构造，零差取商和完成给最小 Hilbert 表示，并在保持历史标签时唯一到酉等价。由它恢复 C128 的二次比较、矩阵过程的完全正性以及带明确接口的通常量子规则。

简化发生在原语层：不再预给向量空间、半双线性形式、中心或局部尺度。数学选择内容仍是正型核；$|r|^2$ 将正性写在续写因子中，没有从纯前缀顺序推出复数或正性。一般物理操作的复线性、实际相干控制、完整记录归一化、独立复合和时间接口仍须另行认证。本轮不主张 Schur 补或正核表示的文献首创。

在保留式追加合同下，日志长度严格增，不要求独立方向严格增。新的比较元最多贡献一个正交方向，零余量表示已有关系的重写；一次真实事件却可能解开多个方向。嵌套可见空间重建后，固定问题的已知比较核可以按正平方增长；这不能换成归一密度态的 Loewner 单增。序向本身也不选空间手性：同次序的 $K$ 与 $\bar K$ 都满足候选，三角积的虚部却相反。

本轮新 HEAD 相对 C128 只增加五个 Bajnok–Beatty 文件，没有新增量子或日志定理。本文明确使用当前快照中既有的日志卷、C117 有限 Gram 拼接及观察窗口定理；新的推进是把正关系的起点退到原始二元比较续写。

| 项目 | C128 | C129 |
|---|---|---|
| 最初对象 | 复历史空间及半双线性形式 | 历史标签及二元比较表 |
| 核心关系 | 对向微移的实非负余量 | 旧块加新历史的平方余项 |
| 中心与小尺度 | 用于表述候选 | 均不需要 |
| 历史向量与内积 | 部分预给，部分恢复 | 从正核包络构造 |
| 正性信息 | 非负实轴 | 续写中的模平方因子 |
| 观察者方向 | 中心无关 | 保留旧比较的有限域包含 |
| 手性 | 不由余量选出 | 三元环可承载，正性不选符号 |

## 目录

- [1. 源码定位与日志单调的准确含义](#section-1)
- [2. 唯一候选：旧比较保留，新历史只添一个余量](#section-2)
- [3. 日志增长、比较窗口与有限失败见证](#section-3)
- [4. 二元续写的三维图与定向环](#section-4)
- [5. 从续写核恢复有限量子规则](#section-5)
- [6. 内生性、原关系与可证边界](#section-6)
- [7. 本轮唯一候选与完整白话](#section-7)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 源码定位与日志单调的准确含义

<a id="sec-c129-source"></a>

本轮一次性固定默认分支的 `8e15c484cf5786fe69fef0627fd84a63cfeb5942`，提交时点为 2026-11-04 16:25:41（Asia/Singapore）。它的第一父提交恰为 C128 的 `1764a0c7f33b`。实际整提交仅新增 Bajnok–Beatty 平方位移阈值分布的五个文件，共 1218 行；理论、量子及概念动力学子树均未变化。因此以下是*新核对快照中的既有成果*，不能称为此次 HEAD 新增量子定理 [1](#ref-repo-c129-pin)。

### 1.1 项目已经区分先后、手性与记录损失

日志卷第 144 节对完整实际事件 $e=(a,y,\kappa)$ 给单射编码及实际回读条件，再定义

$$
\mathcal H(\varepsilon)=\alpha,\qquad
 \mathcal H(he)=\langle\mathcal H(h),Ee\rangle.
$$

自由树的根分解唯一，因此前缀可追回，追加深度严格递增。未执行动作与未取得结果不能填成历史；有限树也不能无损编码任意不可数域的精确读数。
第 144.6 节同时明确：左投影删除末事件在数学上存在，没有证明物理删除或对象逆变换不可能 [2](#ref-repo-c129-log)。

第 143.2 节给可逆更新 $(u,v)\mapsto(v,u+v)$，有序面积却满足

$$
\omega_O(v,u+v)=-\omega_O(u,v).
$$

逆为 $(v,w)\mapsto(w-v,v)$。因此面积反号不要求信息丢失；动作先后、几何手性和记录损失是不同关系。
C128 的 $\Delta_a(tz)=2t^2Q(z)$ 也在 $t\mapsto-t$ 下不变，故不能从它单独读出时间箭头或空间左右手。

### 1.2 完整追加增长，有限记忆可以丢失

固定同一候选域，已保存关系集 $\mathcal R\subseteq\mathcal R'$ 时，

$$
\operatorname{Mod}(\mathcal R')\subseteq\operatorname{Mod}(\mathcal R).
$$

若新增关系已由旧关系蕴含，相容集合不变。这个序关系不需要概率或量子结构；经典日志也满足它。

对有限来源 $W$ 与真正保留全部旧记录的 $R'=(R,Y)$，链式法则给

$$
\begin{aligned}
H(R')-H(R)&=H(Y\mid R)\\
 &=I(W;Y\mid R)+H(Y\mid W,R).
\end{aligned}
$$

记录熵的增加含有来源信息和噪声两部分。只有无噪声条件下，它才恰等于平均来源未知量的下降；单次实际报告的后验熵仍可上升。
若有限状态更新为 $M'=F(M,Y)$，对固定任务变量 $Z=h(W)$ 有

$$
I(Z;M')-I(Z;M)
 =I(Z;Y\mid M)-I(Z;M,Y\mid M').
$$

新取得的任务信息减去更新丢弃的任务信息，可以为负。这些是日志卷第 192 节的同域记账，不是封闭系统熵的普遍增长律 [2](#ref-repo-c129-log)。

### 命题 1.1（闭合可逆过程可以清空冗余日志）

对两个比特的封闭系统，受控非门满足

$$
U_{\rm CNOT}\lvert x\rangle _S\lvert x\rangle _L=\lvert x\rangle _S\lvert 0\rangle _L,
 \qquad x=0,1.
$$

日志寄存器 $L$ 变为空白，全局两个输入的可区分性仍被保留。

**证明。**
定义 $U_{\rm CNOT}\lvert x,y\rangle =\lvert x,y\oplus x\rangle $，它置换正交基且自身为逆，所以是酉算符。对 $y=x$ 得所示式，输出仍由 $S$ 区分。这也对关联子空间的相干叠加线性成立。

可逆计算通过回算清理历史已有经典来源 [6](#ref-bennett1973)。观察者不再记得某事，不构成“该事不可能发生”的逻辑矛盾。能从整体恢复什么，还取决于保留的控制、动力学和访问权限，不能由局部空白直接判断。

### 1.3 本轮向前件之前回溯

C117 定理 7.14 已给*两份预先为正的* Gram 数据的全部正拼接，含奇异支持与收缩参数；它还明确要求原词积、单位及独立性合同同时保留，不能任意挑一个正完成冒充原物理来源。
第 9 节则先给同一正状态的 Hilbert 比较空间及嵌套读口，才得到平方创新和残余下降 [3](#ref-repo-c129-c117)。

本轮把这个方向倒过来：从固定的原始二元核开始，用一条有限续写公式选出正关系，再构造 Hilbert 比较空间及嵌套投影。*完整日志单调本身不推出这条公式*；这正是唯一新增的候选兼容条件。Schur 补、Gram 分解及正核表示属于成熟数学，本文给出直接证明并保留来源 [4](#ref-aronszajn1950)、[5](#ref-albert1969)。

**白话。**如果旧记录确实留下了，新记录当然有一个先后方向；但多写一行不一定多知道一件事，擦掉一份冗余副本也不等于整体信息凭空消失。本轮真正约束的是比较怎样续上：旧关系不挪动，新历史能从旧关系接上的部分先接上，剩下的只能成为一份独立余量。

<a id="section-2"></a>

## 2. 唯一候选：旧比较保留，新历史只添一个余量

<a id="sec-c129-kernel"></a>

本轮从历史的集合与二元比较开始，不预先给物理态向量空间。复数仍是比较值的标量域；递归律中的复系数首先是有限比较表的代数系数。

### 定义 2.1（原始历史核与有限日志）

设 $X$ 为已声明的历史集合，$K:X\times X\to\mathbb C$ 为固定二元表，暂不预设共轭对称性或正性。有限日志 $L=(h_1,\ldots,h_n)$ 的表为 $G_L=[K(h_i,h_j)]$。追加 $h$ 时，旧主块仍为同一 $G_L$；这只规定条目身份，尚不保证比较合法。

这里 $L$ 是历史比较的有限索引表，不把互不相容测量的未执行结果填入同一条实际事件档案。实际应用须保留标签的来源、类型及比较取得条件；核的全有限量词也不意味着观察者已经读到了全域。

### 定义 2.2（C129：回读相容的单余量续写）

从空表开始，对每个有限列表 $L$ 与每个新历史 $h\in X$，存在 $c\in\mathbb C^n,r\in\mathbb C$，使

<a id="eq-c129-candidate"></a>

$$
\boxed{G_{L+h}=\begin{pmatrix}
 G_L&G_Lc\\ c^*G_L&c^*G_Lc+|r|^2
 \end{pmatrix}.}
\tag{1}
$$

其中 $|r|^2=\bar r r$。空表情形就是 $K(h,h)=|r|^2$。日志可含重复历史；该条件没有要求每次 $r\ne0$，也没有预先供应正单位。

### 定理 2.3（续写律与全部有限正性）

<a id="thm-c129-kernel-psd"></a>

C129 等价于：$K(k,h)=\overline{K(h,k)}$，且每张有限表 $G_L$ 正半定。只要每个有限历史集合都包含于一条从空表开始的已认证扩展链，同样足够；仅认证一个未覆盖全部声明历史的日志不够。

**证明。**
令 $T=\left(\begin{smallmatrix}I&c\\0&1\end{smallmatrix}\right)$。递归等式为

$$
G_{L+h}=T^*\begin{pmatrix}G_L&0\\0&|r|^2\end{pmatrix}T.
$$

从空表归纳，每张表均 Hermitian 正半定。对共同更大表取主块即可覆盖有限子集，也得到核的共轭对称性。

反之，设新表为 $B=\left(\begin{smallmatrix}G&b\\b^*&q\end{smallmatrix}\right)\succeq0$。对任意 $u\in\operatorname{ker} G$，在向量 $(tu,1)$ 上评价，得到
$2\Re(\bar t\,u^*b)+q\ge0$ 对所有复数 $t$ 成立，故 $u^*b=0$。有限维中于是 $b\in\operatorname{Ran} G$。取 $c=G^+b$，其中 $G^+$ 为 Moore–Penrose 逆；在 $(-c,1)$ 上评价得

$$
s:=q-c^*Gc=q-b^*G^+b\ge0.
$$

选任意 $r$ 满足 $|r|^2=s$，就得到式 [(1)](#eq-c129-candidate)。这也覆盖 $G=0$、$s=0$ 和所有奇异旧表。

**奇异边界不能省掉。**

若仅检查 $q-b^*G^+b\ge0$，会把 $G=[0],b=1,q=1$ 错判为通过；实际新表 $\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$ 不正。候选的同一个块等式同时保留 $b\in\operatorname{Ran} G$、新行与新列的共轭关系以及非负余量，不能只摘出最后一项。

### 定理 2.4（从二元核构造内积与最小表示）

<a id="thm-c129-kernel-hilbert"></a>

满足 C129 的核具有表示 $\iota:X\to\mathcal H$，使
$K(h,k)=\langle\iota(h),\iota(k)\rangle$，且 $\operatorname{span}\iota(X)$ 稠密。这样的最小表示在保持每个历史标签的意义下酉等价。

**证明。**
先*构造*自由复线性包络 $\mathcal F=\mathbb C^{(X)}$，其元素只有有限支撑。在其中定义

$$
\Gamma(f,g)=\sum_{h,k}\overline{f(h)}K(h,k)g(k).
$$

每次求和落在一张有限正表中，所以 $Q(f)=\Gamma(f,f)\ge0$，而半双线性由有限和的定义成立。若 $Q(f)=0$，对 $f+tg$ 的正性选相位与任意小的 $t$，便得 $\Gamma(f,g)=0$；故零集合 $\mathcal N$ 恰为根空间，商 $\mathcal F/\mathcal N$ 的内积良定义且正定。取完成并令 $\iota(h)=[\delta_h]$，即得表示。

两个最小表示间，将 $\sum_h a_h\iota_1(h)$ 送到 $\sum_h a_h\iota_2(h)$。两边的平方范数均由同一 $K$ 给出，故映射良定义且等距；稠密性使其唯一延伸为酉算符。零核给零空间，也包含在内。

**C128 在构造之后恢复。**

在得到的自由包络及商空间中，半双线性展开给

$$
Q(a+tz)+Q(a-tz)-2Q(a)=2|t|^2Q(z)\in\mathbb R_{\ge0}.
$$

所以一中心的互补微移条件成为后果。反向，若已有 C128 的历史空间与比较形式，将任意原历史标签送入该空间所得的核为正，定理 [2.3](#thm-c129-kernel-psd) 再给递归续写律。后续若完整记录供应 $Q(e)=1$，也恢复 C127 的单位不可双零分解：$e=a+b$ 时，$Q(a),Q(b)$ 不可能同时为零，因为零向量类相加仍为零。

**这一步的简化与保留。**

输入从已给的向量空间、半双线性比较及微移量词，缩到历史集合、一张二元表和一次追加公式；数学线性空间随后由定义构造。正性没有凭空消失：它被写进 $|r|^2$ 与回读相容性，整条律仍等价正型核。复标量及共轭、全部有限上下文及固定条目的身份仍承重。形式线性包络也不自动供应实际相干制备、全部复系数控制、原仪器或复合系统。

**白话。**先把历史一个个记下来。新历史和旧日志之间已有的比较，必须能由旧日志的一份影子同时解释；解释完后，只允许剩下一个自己的余量。旧影子可有多种坐标写法，但不能产生不同的比较。把这条续写关系反复接起来，正内积才出现；不用先把所有历史宣布成量子态向量。

<a id="section-3"></a>

## 3. 日志增长、比较窗口与有限失败见证

<a id="sec-c129-windows"></a>

### 命题 3.1（旧影子唯一，维数只增零或一）

<a id="prop-c129-innovation"></a>

在定理 [2.4](#thm-c129-kernel-hilbert) 的表示中，令
$\mathcal H_L=\operatorname{span}\{\iota(h_i):1\le i\le n\}$。一次合法追加给

$$
\iota(h)=\sum_i c_i\iota(h_i)+\eta,
 \qquad \eta\perp\mathcal H_L,\qquad\|\eta\|^2=|r|^2,
 \qquad \operatorname{rank} G_{L+h}=\operatorname{rank} G_L+\mathbf1_{r\ne0}.
$$

旧影子和 $|r|^2$ 唯一；$c$ 可差一个 $\operatorname{ker} G_L$ 元素，$r$ 的相位则不由核决定。

**证明。**
块式给 $\langle\iota(h_j),\eta\rangle=0$，展开平方范数给 $\|\eta\|^2=|r|^2$。所以旧影子就是正交投影，因而唯一；两个系数解之差由 $G_L$ 消去，所表示的向量为零。正交直和给秩公式，也可由前节可逆合同矩阵 $T$ 直接得到。

追加标签因此不等于每次增加一个独立维数。重复历史可取 $r=0$；即使日志继续增长，所选比较也可能没有新可分辨方向。选择 $r\ge0$ 仅是新坐标的相位规范，不能据此宣布选出了空间手性。

### 3.1 两种矩阵增长不能混同

原始 Gram 表的增长是添加新行列，保留旧主块。将旧表填零到同样大小以后，差却未必正：

$$
\underbrace{\begin{pmatrix}1&1\\1&1\end{pmatrix}}_{\text{合法新表}}
 -\underbrace{\begin{pmatrix}1&0\\0&0\end{pmatrix}}_{\text{旧表填零}}
 =\begin{pmatrix}0&1\\1&1\end{pmatrix}\not\succeq0.
$$

此例 $r=0$，只是新历史已有旧影子。只有先扣除该影子，才留下正交的平方余量。

另一种增长发生在*固定历史集合*上：在同一 Hilbert 表示中取嵌套窗口及其正交投影 $P_n$，定义

$$
K^{(n)}(h,k)=\langle P_n\iota(h),P_n\iota(k)\rangle.
$$

由于 $P_{n+1}-P_n$ 为正交投影，

$$
K^{(n+1)}(h,k)-K^{(n)}(h,k)
 =\langle(P_{n+1}-P_n)\iota(h),(P_{n+1}-P_n)\iota(k)\rangle
$$

才是正型核增量。这里旧历史的*当前可见比较*可以增加；它不同于改写过去保存的条目，也不同于原表填零之差。

固定对角为一的相关核若具有正增量，其增量零对角迫使整表不变。日志增长不能直接写成归一比较表的这种单调性。

### 3.2 可以证明的窗口收敛

### 定理 3.2（给定目标的正交残差）

<a id="thm-c129-window-limit"></a>

若闭子空间满足 $\mathcal H_n\subseteq\mathcal H_{n+1}$，$P_n$ 为对应正交投影，且 $\mathcal H_\infty=\overline{\bigcup_n\mathcal H_n}$，则对每个固定 $v\in\mathcal H$，

$$
P_nv\longrightarrow P_\infty v,\qquad
 \|v-P_nv\|^2=\|v-P_mv\|^2+\|(P_m-P_n)v\|^2\quad(m\ge n).
$$

两个观察者的窗口极限对该 $v$ 相同，当且仅当 $P_\infty^Av=P_\infty^Bv$；两者均恢复 $v$，当且仅当 $v\in\mathcal H_\infty^A\cap\mathcal H_\infty^B$。

**证明。**
两残差项正交，故有平方恒等式。令 $w=P_\infty v$；对任意误差，选足够大窗口中的 $w_N$ 逼近 $w$，则 $n\ge N$ 时
$\|w-P_nw\|\le\|w-w_N\|$。又 $P_n(v-w)=0$，故得强收敛。两个观察者的结论直接由各自极限及投影的固定点空间得到。

前提是同一核、已给的相容窗口及固定目标。它不自动给出未知交集、唯一整体态 $\omega$、归一后条件态收敛或实际门序列收敛。无限维中即使每个固定向量都收敛，也可始终有 $\|I-P_n\|=1$，所以不存在相同的全目标有限误差保证。

这些比较投影也不是已证明的物理 CP 过程。例如 $M_2$ 的 Hilbert–Schmidt 正交投影 $\Pi(X)=(X+X^T)/2$，其 Choi 表在反对称单位向量上取值 $-1/2$，故不 CP：恒等通道的 Choi 项在该向量上为零，转置的交换算符项为 $-1$。从窗口几何进入实际量子仪器，仍须过程接口。

### 3.3 有限失败证书与全旧日志的必要性

若旧表已正而新行不是新列的共轭，二元表已违约。若新列 $b\notin\operatorname{Ran} G$，取 $u$ 为 $b$ 在 $\operatorname{ker} G$ 上的非零分量；对新表的向量 $(-u,t)$，实小 $t>0$ 给
$-2t\|u\|^2+t^2q<0$（非实 $q$ 已另行违约）。若 $b=Gc$ 而 $s=q-c^*Gc<0$，则 $(-c,1)$ 直接给负值 $s$。这些都是声明有限表内的否定见证；实际检验还须原条目、相位和误差认证。

仅检查所有两原子主表仍不够。取三阶表对角为一，非对角均为 $-3/5$。所有两阶主表正定；然而第三条相对旧两条的列为 $b=(-3/5,-3/5)^T$，解得 $c=(-3/2,-3/2)^T$，所以

$$
q-b^*G^+b=1-\frac95=-\frac45<0.
$$

因此，候选中的两个元是*完整旧日志与新历史*。旧日志内部可以含很多原子关系；逐对检查不能替代对同一完整旧表的相容续写。

**白话。**日志可以多记一条，而可分辨的方向没有增加。真正的新方向，是扣掉旧影子以后还留下的那一部分。不断扩充读口时，给定目标的未读残差可以按平方逐步分解；能读到哪里，取决于这些读口最终覆盖哪里。这个过程有追加的先后，却不会自动把所有观察者带到同一个已知终点。

<a id="section-4"></a>

## 4. 二元续写的三维图与定向环

<a id="sec-c129-geometry"></a>

### 4.1 旧方向、投影与新余量

先取一个旧标签 $u$ 与一个新标签 $h$，写

$$
B=\begin{pmatrix}p&b\\\bar b&q\end{pmatrix},
 \qquad p=K(u,u),\quad b=K(u,h),\quad q=K(h,h).
$$

前节的续写律已给 $B\succeq0$；这里不另加几何公理。

### 命题 4.1（二元续写的三维截面）

若 $p>0$，续写恰要求

<a id="eq-c129-paraboloid"></a>

$$
\delta=q-\frac{|b|^2}{p}\ge0,
 \qquad x=\frac{\Re b}{\sqrt p},\quad y=\frac{\Im b}{\sqrt p},
 \qquad q=x^2+y^2+\delta.
\tag{2}
$$

故三维坐标 $(x,y,q)$ 的允许区域是抛物面 $q=x^2+y^2$ 及其上方。
若 $p=0$，必须 $b=0,q\ge0$，不能使用除以 $p$ 的图。

**证明。**
$p>0$ 时，二阶正性等价于 $pq\ge|b|^2$。在构造出的内积空间中，可取

$$
v_u=\sqrt p\,e_1,\qquad
 v_h=\frac b{\sqrt p}e_1+\sqrt\delta\,e_2,
 \qquad e_1\perp e_2,
$$

得到所需比较及直角分解；$\delta=0$ 时省去第二方向。
$p=0$ 时，行列式 $-|b|^2$ 非负迫使 $b=0$，再由对角非负得结论。

<a id="fig-c129-extension-geometry"></a>

```latex
\begin{tikzpicture}[font=\small,>=Latex]
 \path[use as bounding box] (-0.60,-0.85) rectangle (10.70,2.68);
 \node at (1.25,2.42) {旧投影与正交余量};
 \coordinate (O) at (0,0);
 \coordinate (P) at (2.20,0);
 \coordinate (H) at (2.20,1.45);
 \draw[teal!75!black,very thick] (O)--(P)--(H)--cycle;
 \draw[black!55] (2.01,0)--(2.01,0.19)--(2.20,0.19);
 \fill[teal!75!black] (O) circle (1.5pt);
 \fill[teal!75!black] (P) circle (1.5pt);
 \fill[teal!75!black] (H) circle (1.5pt);
 \node[below] at (1.10,0) {$|b|/\sqrt p$};
 \node[right] at (2.20,0.74) {$\sqrt\delta$};
 \node[above left] at (1.10,0.73) {$\sqrt q$};
 \node at (1.25,-0.67) {$q=|b|^2/p+\delta$};

 \node at (8.40,2.42) {三维允许区域};
 \begin{scope}[xshift=8.40cm,
   x={(0.72cm,-0.27cm)},y={(0.72cm,0.27cm)},z={(0cm,0.58cm)}]
  \draw[black!15,dashed] (-1,-1,0)--(1,-1,0)--(1,1,0)--(-1,1,0)--cycle;
  \foreach \v in {-1,-0.5,0,0.5,1}{
   \draw[teal!55!black,line width=0.35pt,domain=-1:1,samples=41,variable=\t]
    plot ({\t},{\v},{\t*\t+\v*\v});
   \draw[teal!55!black,line width=0.35pt,domain=-1:1,samples=41,variable=\t]
    plot ({\v},{\t},{\v*\v+\t*\t});
  }
  \draw[black!40,->] (-1.2,0,0)--(1.4,0,0) node[below right] {$x$};
  \draw[black!40,->] (0,-1.2,0)--(0,1.4,0) node[above right] {$y$};
  \draw[black!40,->] (0,0,0)--(0,0,3.45) node[right] {$q$};
  \draw[orange!85!black,very thick,->] (0.30,0.20,0.13)--(0.30,0.20,2.60);
  \fill[orange!85!black] (0.30,0.20,0.13) circle (1.6pt);
  \fill[orange!85!black] (0.30,0.20,2.60) circle (1.6pt);
  \node[right,fill=white,inner sep=1pt] at (0.30,0.20,2.10) {$\delta\ge0$};
 \end{scope}
 \node at (8.40,-0.67) {$q\ge x^2+y^2$};
\end{tikzpicture}
```

**图 1。**左图边长取比较量的平方根；右图纵坐标是自比较，竖差为 $\delta$。三维坐标描述关系表，不预设物理空间。

边界 $\delta=0$ 表示新向量已在旧方向中；$\delta>0$ 才增加一个独立方向。
一般旧表要检查全部旧方向的联合关系，不能只逐个套用二阶图。
取 $\sqrt\delta\ge0$ 是新残差轴的相位选择；将该轴乘以 $-1$ 或任意单位相位，不改变比较表。因此这个正号尚未指定空间手性。

### 4.2 最小复闭环：关系的关系

### 命题 4.2（三元环与共轭对称）

对同一正核的三个标签，定义

$$
\mathcal B_{123}=K_{12}K_{23}K_{31}.
$$

它在各标签独立重相位及循环换标下不变；交换任意两个标签，或将整个核复共轭，都会使它变为 $\overline{\mathcal B_{123}}$。
整个复共轭核仍按同一标签顺序满足续写律。

**证明。**
重相位给 $K'_{ij}=e^{i(\theta_j-\theta_i)}K_{ij}$，三个相位因子相乘为一。
Hermitian 性给 $K_{ji}=\overline{K_{ij}}$，从而反序环为原环的共轭。
将续写块式逐项共轭，并将系数 $c$ 换为 $\bar c$，平方余量保持不变；因此所有原前缀仍合法。

两点闭环 $K_{12}K_{21}=|K_{12}|^2$ 是实数，三点是可能留下复定向的最短闭环。
对于归一纯态，它是三顶点 Bargmann 不变量 [7](#ref-bargmann1999)。
只有 $\mathcal B_{123}\ne0$ 时才定义其相位；沿非正交顶点的自由测地线闭环，所引文献的几何相位约定为 $-\arg\mathcal B_{123}$。
若重叠图有零边，三元环未必检测全部相位，不能据此省去更长闭环。

### 命题 4.3（qubit 的三元定向）

对归一纯 qubit 态，写 $P_i=(I+\mathbf r_i\cdot\boldsymbol\sigma)/2$，则

<a id="eq-c129-bargmann-qubit"></a>

$$
\mathcal B_{123}=\operatorname{Tr}(P_1P_2P_3)
 =\frac{1+\mathbf r_1\cdot\mathbf r_2+\mathbf r_2\cdot\mathbf r_3
 +\mathbf r_3\cdot\mathbf r_1
 +i\,\mathbf r_1\cdot(\mathbf r_2\times\mathbf r_3)}4.
\tag{3}
$$

**证明。**
使用 $(\mathbf a\cdot\sigma)(\mathbf b\cdot\sigma)
=(\mathbf a\cdot\mathbf b)I+i(\mathbf a\times\mathbf b)\cdot\sigma$，展开并取迹；非标量 Pauli 项迹为零，得到公式。

取同一顺序的三态

$$
v_1=\lvert 0\rangle ,\qquad v_2=\frac{\lvert 0\rangle +\lvert 1\rangle }{\sqrt2},\qquad
 v_3^{\pm}=\frac{\lvert 0\rangle \pm i\lvert 1\rangle }{\sqrt2}.
$$

两张 Gram 表都满足全部续写，分别给 $\mathcal B_{123}^{\pm}=(1\pm i)/4$。
第三态已在前两态的复张成空间内，故该步新增正交余量为零，三元环仍有相反虚部。
新事件标签、新独立方向和新可读相位不是同一个计数。
这说明候选允许定向关系存在，却不强制所有关系选择同一符号；把 Bloch 定向接到实际空间手性还需相应标定与实现。

### 4.3 前缀序不能误读为归一态单调

### 命题 4.4（归一正锥中的可比态）

若密度矩阵 $\rho'\succeq\rho$ 且二者迹都为一，则 $\rho'=\rho$。

**证明。**
$\rho'-\rho$ 为迹零正矩阵，全部特征值非负且和为零，故矩阵为零。

所以本轮保存的是旧比较主块与原标签；它不要求时间演化的密度态在同一正锥中不断增大。

**白话。**每添一个比较对象，先把它与旧关系能对上的部分接回去，再留下一个垂直余量；余量为零，也可能有一个新的事件标签。图上允许点在碗面或碗面上方。追加次序由前缀标出，左右定向则要看关系绕一圈以后留下的相位；把全部相位反过来，档案仍能按原顺序继续。因此，记录的先后与几何的左右各有自己的内部证据。

<a id="section-5"></a>

## 5. 从续写核恢复有限量子规则

<a id="sec-c129-quantum"></a>

正核先给比较空间。要接回原过程，须使用它实际对应的乘法、复线性、记录与联合接口；自由表的任意正完成不能替代这些关系。以下给一套有限复矩阵理论的条件性闭合，标准表示与概率定理有成熟来源 [8](#ref-watrous2018)、[9](#ref-busch2003)。

### 5.1 一条有限来源列表选择完全正过程

### 定义 5.1（事件的原始核）

取 $d,m\ge1$。对仅给复线性的 $\Phi:M_d(\mathbb C)\to M_m(\mathbb C)$，以 $(a,u)\in M_d\times\mathbb C^m$ 为原始历史标签，定义

$$
K_\Phi((a,u),(b,v))=\langle u,\Phi(a^*b)v\rangle.
$$

不预设 $\Phi$ 保伴随、正、完全正或归一化。

### 定理 5.2（有限续写与 CP）

<a id="thm-c129-cp"></a>

固定一来源行 $p$。以下等价：

1. 核 $K_\Phi$ 满足 C129；

2. 对有限列表 $((E_{pi},e_\mu))_{i,\mu}$，从空表依次续写全部 $dm$ 个标签时，每步满足候选；

3. $\Phi$ 完全正。

成立后 $\Phi$ 自动保伴随，且存在 $d\times m$ 矩阵 $A_\alpha$，使

$$
\Phi(x)=\sum_\alpha A_\alpha^*xA_\alpha.
$$

**证明。**
该列表的比较表第 $((i,\mu),(j,\nu))$ 项为
$\langle e_\mu,\Phi(E_{ij})e_\nu\rangle$，即 Choi 表 $C_\Phi=[\Phi(E_{ij})]$。
由续写定理，(2) 恰要求 $C_\Phi\succeq0$。
将其分解为 $\sum_\alpha w_\alpha w_\alpha^*$，写
$w_\alpha=\sum_i e_i\otimes A_\alpha^*e_i$，比较各块即得 Kraus 式；它的每一级矩阵放大都将正矩阵送到正矩阵，所以给 (3)。
CP 反向作用于任意正块表 $[a_i^*a_j]$，再用向量族评价，得到

$$
\sum_{ij}\bar z_i K_\Phi((a_i,u_i),(a_j,u_j))z_j\ge0.
$$

于是全核正，续写定理给 (1)；(1) 显然给 (2)。

在核商空间上令 $\pi(x)[a,u]=[xa,u]$。它保零差，因为
$\langle\pi(x)h,k\rangle=\langle h,\pi(x^*)k\rangle$。
取 $b=(\|x\|^2I-x^*x)^{1/2}$，有
$\|x\|^2Q(h)-Q(\pi(x)h)=Q(\pi(b)h)\ge0$，故有界。
核公式也保证 $Vu=[I,u]$ 对 $u$ 线性，直接得到

$$
\Phi(x)=V^*\pi(x)V.
$$

这里 $V$ 不必等距；单位效果未归一时不能补出等距结论。零映射使用零比较空间及空 Kraus 和，也满足本轮候选。

### 5.2 完整记录、Born 与读后态

### 命题 5.3（原记录的归一化）

若原事件族 $\Phi_j:M_{d_j}\to M_m$ 各满足候选，并另有完整记录约束 $\sum_j\Phi_j(I)=I$，则态方向过程

$$
\mathcal T_j(\rho)=\sum_\alpha A_{j\alpha}\rho A_{j\alpha}^*,
 \qquad \sum_{j,\alpha}A_{j\alpha}^*A_{j\alpha}=I
$$

构成完整 CP 仪器。各支迹不增，总输出保迹。

**证明。**
令 $E_j=\Phi_j(I)=\sum_\alpha A_{j\alpha}^*A_{j\alpha}\ge0$，则
$I-E_j=\sum_{k\ne j}E_k\ge0$。迹循环给 $\operatorname{Tr}\mathcal T_j(\rho)=\operatorname{Tr}(\rho E_j)$，即得支迹界与总保迹。

概率本身需要一致的效果评价。对全部 $0\le E\le I$ 给 $p(E)\ge0$，满足 $p(I)=1$，且 $E+F\le I$ 时 $p(E+F)=p(E)+p(F)$；同一效果在不同完整测试中赋同值。

### 定理 5.4（效果评价与纯态）

该评价唯一为 $p(E)=\operatorname{Tr}(\rho E)$，其中 $\rho\ge0,\operatorname{Tr}\rho=1$。
密度态的极点恰是秩一态；对归一纯态与秩一投影有 $p=|\langle\varphi,\psi\rangle|^2$。

**证明。**
可加性给有理齐次性，非负性给单调性，有理夹逼给实齐次性。对 $B\ge0$，以 $s>0,s\ge\|B\|$ 定义 $f(B)=s\,p(B/s)$，它与 $s$ 无关且在正锥可加。由正负分解延伸为 Hermitian 空间上的实线性泛函；有限迹配对给唯一 Hermitian $\rho$，正性与归一分别给 $\rho\ge0$ 和迹一。
秩至少二时可反向微调两个正谱权，得非平凡凸分解；秩一态的正分解只能支持同一射线，故它是极点。对两个秩一矩阵直接相乘取迹，即得 Born 平方律。相同纯态的归一向量只差整体相位。

该全效果版本包括二维 [9](#ref-busch2003)。候选未自动供应全部物理效果。
原支有 $p_j=\operatorname{Tr}(\rho E_j)$；仅当 $p_j>0$ 时定义 $\rho_j=\mathcal T_j(\rho)/p_j$。
若同空间支效果为投影 $P$，且保持 $\operatorname{Ran} P$ 内每条纯射线，则得到 Lüders 更新：$P=0$ 时所有 Kraus 项为零；$P\ne0$ 时效果先给 $A_\alpha(I-P)=0$，射线保持使每个 $A_\alpha v$ 与 $v$ 共线。对基向量及两两和应用，得 $A_\alpha=c_\alpha P$。效果给 $\sum|c_\alpha|^2=1$，故 $\mathcal T(\rho)=P\rho P$。仅有结果可重复性不排除结果子空间内的旋转。

### 5.3 可观测量、不确定界与独立复合

有限锐测量由正交投影 $\sum_iP_i=I$ 和实结果 $a_i$ 给自伴算符 $A=\sum_i a_iP_i$，反向由有限谱分解得到。其期望为 $\operatorname{Tr}(\rho A)$。
对自伴 $A,B$ 中心化为 $A_0,B_0$，在算符历史上用
$\Gamma_\rho(X,Y)=\operatorname{Tr}(\rho X^*Y)$。二元 Gram 行列式非负给

$$
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)
 \ge |\operatorname{Tr}(\rho A_0B_0)|^2
 \ge\tfrac14|\operatorname{Tr}(\rho[A,B])|^2.
$$

第二步保留复数的虚部。具体位置、动量及交换常数并非核续写选出。

若 $M_d,M_m$ 保单位保星地嵌入同一非零联合代数，两像交换并共同生成，则
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 是满的保单位星同态。定义域 $M_d\otimes M_m\cong M_{dm}$ 简单：非零理想经矩阵单位左右相乘即含全部矩阵单位。故核为零，给张量联合。
CP 串接与并接的 Kraus 族分别为 $B_\beta A_\alpha$ 与 $A_\alpha\otimes B_\beta$。完整局部保迹过程不改变另一侧边缘，因为其伴随把 $I\otimes E$ 送回 $I\otimes E$。条件于特定结果时，边缘可变，所选标签的信息不能丢去。

### 命题 5.5（共同内部参照限制单侧复反射）

在已给二比特联合接口中，矩阵转置 $\Theta(X)=X^T$ 不能作为保持全部内部参照正性的局部过程。

**证明。**
取 $\lvert \Omega_2\rangle =(\lvert 00\rangle +\lvert 11\rangle )/\sqrt2$。直接展开得

$$
(\operatorname{id}\otimes\Theta)(\lvert \Omega_2\rangle \langle \Omega_2\rvert )=\tfrac12F,
 \qquad F\lvert ij\rangle =\lvert ji\rangle .
$$

它在反对称单位向量 $(\lvert 01\rangle -\lvert 10\rangle )/\sqrt2$ 上的自比较为 $-1/2$，所以违反正性和核续写。

在 qubit 坐标中，转置使 Bloch 的 $y$ 分量反号。因而在同一联合与参照接口下，这种单侧反射不能作为对全部联合输入有效的局部过程；被动换坐标并同步改写比较约定不受此结论排除。这不否定整个关系模型 $K\mapsto\bar K$ 的相容性，也不证明整体共轭是一个可执行量子门，更没有把 Bloch 反射直接认作物理空间宇称。

### 5.4 可逆、时间及物理接口

### 命题 5.6（同维可逆过程与时间群）

同维 CPTP 过程若有 CPTP 左逆，则为酉共轭。若再给连续一参数 CPTP 群，则存在自伴 $H$，使

$$
\mathcal T_t(\rho)=e^{-itH/\hbar}\rho e^{itH/\hbar},
 \qquad i\hbar\dot\rho=[H,\rho].
$$

**证明。**
两过程的 Kraus 族记为 $A_i,B_j$。恒等通道 Choi 秩一给 $B_jA_i=c_{ji}I$。
对一个非零 $A_i$，逆过程保迹保证至少一个乘积非零；同维使相应 $B_j$ 可逆，从而所有 $A_i$ 共线。合并成一个 $A$ 后，保迹给 $A^*A=I$，方阵即酉。
有限维连续群写为 $e^{t\mathcal L}$；酉共轭性使生成元为保星导子。取 $D=\sum_k\mathcal L(E_{k1})E_{1k}$，导子律给 $[D,E_{ij}]=\mathcal L(E_{ij})$；保星性使 $D+D^*$ 为中心。换成反自伴部分并写成 $-iH/\hbar$，得到公式。

选定纯态相位代表后有 $i\hbar\dot\psi=H\psi$。具体钟、生成元与 $\hbar$ 标定并非原始核给出的事实。内积、正过程、完整概率、独立联合与时间的来源必须逐层对应。

| 通常规则 | 本轮推导与保留条件 |
|---|---|
| Hilbert 与叠加 | 正核的自由复包络及零差商；实际叠加仍须原控制接口。 |
| CP 与过程表示 | 指定复线性矩阵事件的来源核；有限 Choi 列表续写。 |
| 概率与仪器 | 全效果一致可加评价；原完整记录归一化。 |
| 测量更新 | 已给 CP 仪器；逐射线保持时才选出 Lüders。 |
| 复合与局部性 | 交换且共同生成的独立子代数；完整局部保迹。 |
| 酉与时间 | 同维 CPTP 左逆；连续群和另行标定的物理时钟。 |

**白话。**比较表能一条条接下去，先给出可以共同放置历史的内积空间。原过程若按自己的乘法产生这张表，续写条件就选择完全正过程；完整记录随后给概率的一份一，一致的效果赋值给 Born 规则。可逆、独立和时间各自是整体内部另一类关系，必须说明如何接到这张表上，不能由“日志在增长”直接跳过去。

<a id="section-6"></a>

## 6. 内生性、原关系与可证边界

<a id="sec-c129-scope"></a>

### 6.1 数学包络不替代原来的相干操作

若原标签已声明一个操作关系 $h_3=\alpha h_1+\beta h_2$，要让它在构造空间中保持，必须有

$$
K(k,h_3)=\alpha K(k,h_1)+\beta K(k,h_2)\quad\text{对全部声明的 }k.
$$

此时差向量与稠密张成空间正交，故确为零；反向显然。
因此，原词积、复线性、单位、独立性和控制身份可锁成核条目之间的具体约束，但不能仅凭正核假定它们成立。

一个简单反例是以复数为原标签，取 $K(a,b)=|a|^2|b|^2$。它是秩一正核，满足全部续写；其最小表示可取 $\iota(a)=|a|^2$，却有 $\iota(ia)=\iota(a)$，一般不等于 $i\iota(a)$。正核构造了复线性包络，没有证明原标签上名叫“乘 $i$”的操作已成为相位门。

### 6.2 日志身份与比较等价必须同时保存

核映射 $\iota$ 不必单射。两个不同事件或门序列可能有同一比较向量；把它们在比较空间中合并，不许可删除原档案、权限、标定或未来仍需的过程身份。若要把“内容就是地址”解释为一一对应，必须另外证明所用核分离那些地址。
数学上的有限列表可以换序；正核与续写律对任何枚举次序都成立。因此实际前缀与执行协议供应记录序向，候选没有从 $K$ 自身挑出唯一时间箭头。

这里保留的是原事件记录与模型中固定的真实比较；有噪声的估计值可以随着新增证据修正，修正过程本身应留有来源。候选没有要求错误估计永不更新，也没有把一次改估等同于抹掉旧事件。

两个观察者在已认证共同子域上能对照核值，不要求一方先包含另一方全部结构。尚未认证的交叉值和完整交集仍然未知。局部表各自为正也不自动给出唯一全局核；已有交叉关系不能为了找到一个正完成而改写。C117 定理 7.14 的自由 Gram 拼接与原过程合同正是在这里分开 [3](#ref-repo-c129-c117)。

在已给正状态的 GNS 表示里，若每个窗口都含单位历史，其源向量 $\xi=[I]$ 从一开始就在每个窗口中，因而 $P_n\xi=\xi$。增长的是可比较的问题与关系，不是源向量本身；不能把窗口增长直接写成整体量子态在演化 [3](#ref-repo-c129-c117)。

无限多标签可映入有限维空间，表示许多关系线性相关；这不代表有限维物理记忆能保存任意多个*可无误区分*的完整经典日志。若 $N$ 个日志由彼此正交的纯记录态表示，$D$ 维空间中的非零正交向量至多 $D$ 个，故 $N\le D$。把无限归档作为模型条件，需要相应容量与访问资源。

### 6.3 有限否定与实际证据

精确有限表可以通过不共轭、像空间违约或负 Schur 余量否定候选；但未读全域不能由一张合格表认证。接近奇异的旧表会放大预测系数，不能把数值伪逆的微小余量直接当作已标定的实验结论。
例如 $G=[\epsilon],b=\sqrt\epsilon,q=1/2$ 在 $\epsilon>0$ 时余量为 $-1/2$；原表却在 $\epsilon\downarrow0$ 时趋于合法的 $\operatorname{diag}(0,1/2)$，此时余量为 $1/2$。余量坐标跨奇异边界不连续，须同时报告原条目误差、支撑判定和所用尺度。

本轮没有从前缀偏序选出复数域，也没有从正核唯一选出量子场、粒子谱、时空手性或作用量。经典记录模型同样可以给出正核；进入通常量子理论还用了已列明的复矩阵、完整记录和实际相干接口。本稿给出一个完整的条件候选与证明，不主张全球最小公理、文献首次发现或已确认的新物理定律。

把“满足续写式的内部关系系统”作为定义是数学选择；断言实际物理关系属于这个类，仍是需要原始读出与实验支持的命题。将公理改写成定义间的相容约束，使承重条件清楚，并不使这个物理断言自动成立。

<a id="section-7"></a>

## 7. 本轮唯一候选与完整白话

<a id="sec-c129-final"></a>

给定原始历史集合与固定复数值二元比较，唯一新增约束是式 [(1)](#eq-c129-candidate)：从空表开始，所有有限续写都能保住旧比较，把新历史接成旧影子加一个平方余项。它的闭环为

$$
\text{原始二元核的单余量续写}
 \Longleftrightarrow\text{全部有限表为正}
 \Longleftrightarrow\text{最小 Hilbert 比较表示}.
$$

矩阵过程接口再将它接到 CP；完整记录和其余关系接到通常量子规则。没有重复设立“日志熵单增”或“宇宙绝对手性”作为第二候选。

### 本轮完整白话

**白话。**观察者先留住已经取得的记录，再把新历史接到它们后面。旧历史之间的比较不能为了接上新东西而改写。新历史与旧记录有联系，就先找出旧记录中能同时解释这些联系的那份影子；扣掉影子，还没有被表达出来的部分，只能补成一条垂直余边。余边可以为零，所以多一条日志不一定多一个独立方向。这样一条条接下去，内积空间才形成，平方读数与完全正过程随后出现；我们不用先宣布每段历史已经是一根量子态向量。二元图里，这就是一条旧边、一条余边和它们合成的直角三角形；连同相位画成三维，则新读数只能在碗面上或碗面上方。前缀告诉观察者哪条记录先留下，关系绕一圈的相位才告诉它有没有有向差异；两者可以都存在，却不能仅凭“向前记”确定空间的左右。不同观察者能够拼接的，是他们已有证据对应上的关系；能逼近哪些问题，取决于实际读口覆盖哪里。所有比较、记录和参照仍在整体内部，本轮把约束退到最早的一步：新历史可以续添，旧关系必须保住，尚未解释的部分只作为自己的余量加入。

<a id="references"></a>

## 参考文献

<a id="ref-repo-c129-pin"></a>

### [1]

The Omega Institute, *trureturing*, immutable commit
[8e15c484cf5786fe69fef0627fd84a63cfeb5942](https://github.com/the-omega-institute/trureturing/commit/8e15c484cf5786fe69fef0627fd84a63cfeb5942)。
2026-11-04 08:25:41 UTC；PR #26418，Bajnok–Beatty 平方位移阈值分布。
第一父提交为 C128 pin；全部实际增量只有五个相关有限群文件。本文登记该增量，不认证其数学证明。

<a id="ref-repo-c129-log"></a>

### [2]

The Omega Institute, *AURIC FIB History Records Time Arrow*。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/8e15c484cf5786fe69fef0627fd84a63cfeb5942/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md)。
本文核读并使用第 142–144、146、191–194 节的定义、证明与边界；不将全文下载或该范围外的既有 FIB 单射依赖称为本轮完整重审。
前缀增长保留单射事件码与实际回读合同；第 146 节先给正权内积；第 192 节区分来源信息、噪声与有限记忆损失。

<a id="ref-repo-c129-c117"></a>

### [3]

The Omega Institute, *AURIC Common Source Self Reference and Observer Sequences C117*。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/8e15c484cf5786fe69fef0627fd84a63cfeb5942/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)。
本文核读定理 7.14、相关比较接口及第 9–11 节。自由 Gram 拼接须另保原词积、单位及独立性；窗口增长以同一正态与嵌套可读域为前件；三角运输相位及其实际参考条件均保留。

<a id="ref-aronszajn1950"></a>

### [4]

N. Aronszajn, “Theory of reproducing kernels”,
*Transactions of the American Mathematical Society* **68**(3), 337–404 (1950).
[原始论文扫描件](https://pages.stat.wisc.edu/~wahba/stat860public/pdf2/aronszajn.pdf)；
[doi:10.1090/S0002-9947-1950-0051437-7](https://doi.org/10.1090/S0002-9947-1950-0051437-7)。
Part I, §2 的正核与 Hilbert 表示；本文给所需商空间构造的直接证明，不主张该经典对应为新结果。

<a id="ref-albert1969"></a>

### [5]

A. Albert, “Conditions for positive and nonnegative definiteness in terms of pseudoinverses”,
*SIAM Journal on Applied Mathematics* **17**(2), 434–440 (1969).
[doi:10.1137/0117041](https://doi.org/10.1137/0117041)。
奇异分块正性与伪逆判据的文献定位；本文的值域条件及 Schur 余量等价由正文独立证明，不声称已重审该论文全文。

<a id="ref-bennett1973"></a>

### [6]

C. H. Bennett, “Logical reversibility of computation”,
*IBM Journal of Research and Development* **17**(6), 525–532 (1973).
[原始论文扫描件](https://worrydream.com/refs/Bennett_1973_-_Logical_Reversibility_of_Computation.pdf)；
[doi:10.1147/rd.176.0525](https://doi.org/10.1147/rd.176.0525)。
原文的逆序回算清理中间历史、保留输入与输出，支持局部日志缩减不等于全局区别消失。本文的两比特例由 CNOT 定义直接验证。

<a id="ref-bargmann1999"></a>

### [7]

E. M. Rabei, Arvind, N. Mukunda and R. Simon,
“Bargmann invariants and geometric phases: A generalized connection”,
*Physical Review A* **60**, 3397 (1999).
[arXiv:quant-ph/9907080](https://arxiv.org/pdf/quant-ph/9907080)。
式 (2.8)–(2.9) 给循环内积、投影迹及非零重叠条件下的 $-\arg\mathcal B$ 约定。正文直接证明三元共轭规律与 Pauli 展开；不把 Bloch 定向直接认作物理空间宇称。

<a id="ref-watrous2018"></a>

### [8]

J. Watrous, *The Theory of Quantum Information*, Cambridge University Press (2018).
[作者公开第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，Theorem 2.22。
有限 Choi、Kraus、Stinespring 等价；正文给一来源有限核表的完整推导及实际过程接口。

<a id="ref-busch2003"></a>

### [9]

P. Busch, “Quantum states and generalized observables: a simple proof of Gleason's theorem”,
*Physical Review Letters* **91**, 120403 (2003).
[arXiv:quant-ph/9909073](https://arxiv.org/pdf/quant-ph/9909073)。
完整效果归一可加评价的 Born 表示，包括二维。该评价前件没有由日志长度或核续写独自推出。

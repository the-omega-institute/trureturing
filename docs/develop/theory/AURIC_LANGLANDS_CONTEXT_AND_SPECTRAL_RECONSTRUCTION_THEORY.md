# AURIC–Langlands 语境与谱重构理论

合法未来、有限谱代数、辛边界与 Hecke 接口的定义和证明。

> **范围。** 本卷是纯理论 Markdown 正文，只新增一个理论来源文件，不新增 `.tex`、PDF、Lean、Blueprint、消化记录或实验材料。普通线性代数、表示论和变分论证在文中给出证明；Tannaka、Riemann–Hilbert、几何 Satake 和几何朗兰兹的使用位置明确标为外部输入。本卷没有声称整卷已经通过 Lean 编译。
>
> **来源边界。** 本稿对应提交 `2d7d995ea59799e2e68c0e6d6b13da9ed5eebf89` 的公开理论与源声明，并沿用其前置理论卷所声明的合同。项目输入、普通数学推导和外部定理不互相冒充。涉及复制、联合测量、控制门、谱局部系统和 Hecke 对象的资源条件分别记录。
>
> **读法。** 数学块使用 GitHub 支持的双美元分隔符；“定理”“命题”“引理”“推论”段落是可独立引用的数学声明。任何模型可实现性都只在它的来源、端口、时钟、权限和精度条件下成立。

## 摘要

本卷延续有限预测商、五模式实观测、关系丛与朗兰兹接口，处理三类新增问题。有限权限和合法门词如何决定可取得的未来闭包？十八维代数承载、真实终端碰撞和任意块端口响应能产生哪些严格的重构与障碍？怎样从明确的边界模型构造谱局部系统，同时保留中心、实形式、归一化和实现资源？

主要结果是：许可自动机的全状态传播与有限稳定界；语境盲核的最大张量理想性质；刚性纤维函子的维数保持和亚归一化完全正操作的对偶障碍；有限谱代数中终端原始元的迹矩阵重构；真实终端碰撞的一参数延拓及异常层限制；异源实联合观察的图分类和正性截断；Schur 响应的组合、微分和扰动公式；树端口行列式的热带四点证书；四个二通道转移块在 $\operatorname{Sp}_4$ 中的 Zariski 稠密性；原始外幂给出的五维正交输运与中心核；曲面局部系统、提升的 $H^1(X,\mu_2)$ 分类和 Hecke 自然性；以及固定 Green 模型的精确相对型临界值。

这些结论不把读取能力当作控制能力，不把 Zariski 稠密性当作范数逼近或物理可执行性，不把五维投影当作保留四维中心数据，也不把一个具名外部定理的存在性当作本项目的 Lean 证明。尚未解决的同基独立双碰撞、原生控制块的共同实现、带分歧 Hecke 范畴和统一成本界在末节列出。

## 1. 模型、来源与证明责任

### 1.1 四种数据

**定义 1.1（模型的四种数据）。** 一个本文模型至少声明

$$
\mathfrak M=(\mathsf X,\mathsf P,\mathsf O,\mathsf R).
$$

其中，$\mathsf X$ 是完整来源与持久状态，$\mathsf P$ 是带时钟、权限及组合规则的合法操作，$\mathsf O$ 是可调用读数，$\mathsf R$ 是额外参考、制备、联合控制和数值精度资源。两个命题只有在四种数据一致，或给出明确转换映射时，才可以组合。

同一符号在不同合同中的含义不自动相同。原生有序对象的带标签并行复制、来源允许重新独立制备的 $\rho^{\otimes k}$、以及从一份未知态制造另一份相同态，是三种不同操作。本文后两者不由第一种自动供应，且不把第三种当作免费操作。

### 1.2 输入层、推导层与外部接口

本文直接使用的项目输入包括原始终端 $M$ 的实际碰撞文档、奇异响应排除文档、边界几何续篇、变系数 Green 稳定性文档、关系观察文档、有限合法门词 Blueprint，以及原生联合未来记忆的 Lean 声明。它们提供具体来源、守卫条件和已声明接口；本文只在相同条件下引用这些输入，不把读取声明改写成新形式化证明。

外部输入包括有限 étale 代数的标准结构、向量丛的 clutching 分类、Tannaka 重构、正则奇 Riemann–Hilbert、$\operatorname{Sp}_4$ 与 $\operatorname{SO}_5$ 的表示论、几何 Satake 和无分歧几何朗兰兹的本征对象存在性。几何朗兰兹部分要求特征零、光滑射影曲线、标准归一化和不可约的非抛物水平参数；四穿孔或关系球面构造不能自动继承无分歧结论。

## 2. 合法未来与任务记忆

### 2.1 许可语言的效应闭包

**定义 2.1（许可语言的效应空间）。** 令 $E$ 为 $d$ 维实向量空间，$U\subseteq E$ 为 $r$ 维终端效应空间，$A_a\in\operatorname{End}(E)$ 为有限字母表 $\Sigma$ 上的作用。给定无空步的有限确定部分自动机 $(Q,\Sigma,\delta,q_0,F)$；若 $\delta(q,a)$ 未定义，该步没有执行事件。对时间顺序门词 $w=a_1\cdots a_k$，采用 Heisenberg 约定 $A_w=A_{a_1}\cdots A_{a_k}$。令

$$
U_q^{(0)}=
\begin{cases}
U,&q\in F,\\
0,&q\notin F,
\end{cases}
\qquad
U_q^{(n+1)}=U_q^{(n)}+\sum_{\delta(q,a)=q'}A_aU_{q'}^{(n)}.
$$

只在接受终端读取；若中间前缀也读取，应把相应位置加入终端合同。

**定理 2.2（全状态传播与合法未来界）。** $U_q^{(n)}$ 恰由从 $q$ 出发、长度至多 $n$ 的接受门词拉回的终端效应张成。所有空间同时稳定的步数不超过

$$
B=|Q|d-|F|r.
$$

一旦所有 $q$ 同时满足 $U_q^{(n+1)}=U_q^{(n)}$，就永久稳定。因此起点的完整合法未来空间为 $U_{q_0}^{(B)}$。

**证明。** 长度零的接受词给出初始化。任意非空接受词唯一分解为首字母 $a$ 与从 $\delta(q,a)$ 出发的接受尾词；$A_{aw}=A_aA_w$ 给出递推，归纳即得第一项。各空间单调增加，初始维数和为 $|F|r$，最大为 $|Q|d$。每次尚未同时稳定的迭代至少使一个空间严格增维，维数和至少增加一；若同时稳定，再代入同一个递推算子即保持不变。因此至多 $B$ 次严格增加。$□$

**例 2.3（起点平台掩盖任意长延迟）。** 取 $E=\mathbb R,U=\mathbb R$，每个门作用为恒等，自动机是一条长度 $L$ 的链 $q_0\to q_1\to\cdots\to q_L$，仅 $q_L$ 接受。则 $U_{q_0}^{(n)}=0$ 对所有 $n<L$，而 $U_{q_0}^{(L)}=\mathbb R$。连续若干步观察到起点没有增维，并不能省略剩余权限状态。

**命题 2.4（未来类的记忆下界）。** 设完整状态集的合法未来等价类共有 $N$ 个。若有限记忆 $m:\mathsf X\to M$ 满足：同一记忆值能重建合法性和所有声明的未来回复，则 $|\operatorname{im}m|\ge N$，从而 $|M|\ge N$。

**证明。** 若 $m(x)=m(y)$，同一解码器在每个声明的合法未来上给出相同结果，故 $x,y$ 同类。因此每个已实现记忆值只属于一个未来类，并且给出 $\operatorname{im}m$ 到全部未来类的满射。$□$

项目的 `native_joint_future_memory_lower_bound` 在其专用 `Source`、`futureReplies` 与十一类分类下实例化了此命题。若进一步规定用固定长度二进制串编码全部 11 个已实现记忆状态，至少需要 4 位；这不是任意来源或任意任务都需要 4 位的断言。

### 2.2 真实空间谓词与锁存

在一个完整兼容域 $\mathcal D$ 上，项目定义

$$
\sigma(P)=\mathbf1_{\{P_{12}>1/16\}},\qquad \theta=-17027/10.
$$

同一原始七步路径以 $M$ 结束，且所有完整世界满足 $\sigma(P(W))=\mathbf1_{\{m(W)\ge\theta\}}$。两支的末端区间为

$$
\begin{aligned}
m(W_-)&\in[-1705.04831638,-1704.83443702],\\
m(W_+)&\in[-1700.57340993,-1700.35474402].
\end{aligned}
$$

**推论 2.5（来源不变的读数误差容限）。** 若另行取得的数值读数满足

$$
|\widetilde m-m(W)|<2.12659007,
$$

则同一阈值仍正确取得 $\sigma(P(W))$。这个二值任务的最小已实现锁存状态数为 2。

**证明。** 两区间与阈值的间隔分别至少为 $2.13443702$ 和 $2.12659007$，所以所述扰动不能跨过阈值。来源域同时含有空间谓词为 0 和 1 的世界，故一个可反复正确回复的锁存必须区分至少两个状态；直接保留取得的位已经足够。$□$

这个误差保证是额外的数值接口条件。它没有给出仪器分辨率成本，也没有消除原始来源、完整增益、固定漂移、七次调用及安装权利。二状态任务锁存与保留全部未来的十一类记忆属于不同任务。

## 3. 语境闭包与张量结构

### 3.1 最大相容盲核

**定义 3.1（语境盲核）。** 设 $\mathcal C$ 是已声明许可张量操作子范畴的 $k$-线性化，包含相应权限和对象类型，并具有对称幺半结构。每个态射空间指定测试 $\mathcal O(X,Y)\subseteq\operatorname{Hom}(X,Y)^*$，并令

$$
N(X,Y)=\bigcap_{\lambda\in\mathcal O(X,Y)}\ker\lambda.
$$

单孔语境 $C[-]$ 由许可的固定态射前后复合、左右张量及范畴约束生成，而且对孔内变量线性。假设这些语境在所声明子范畴内对上述操作封闭。定义

$$
I_{\mathrm{ctx}}(X,Y)=
\{f:\lambda(C[f])=0\ \text{对全部许可语境和最终测试}\}.
$$

**定理 3.2（最大相容盲核）。** $I_{\mathrm{ctx}}$ 是包含于 $N$ 的最大张量态射理想。因此 $\mathcal C/I_{\mathrm{ctx}}$ 继承线性对称幺半结构。

**证明。** 它是线性泛函核的交，故是子空间。对其元素前后复合或与固定态射张量，再加任意外层语境，仍是许可语境，故测试为零。恒等语境说明 $I_{\mathrm{ctx}}\subseteq N$。若张量理想 $J\subseteq N$，则每个语境把 $J$ 送入对应的 $J$，所以所有最终测试均消去 $J$，即 $J\subseteq I_{\mathrm{ctx}}$。理想性质保证复合和张量在商中良定义。$□$

增加可调用语境时，应取在所有新语境下仍不可见的最大理想；简单取包含旧盲核的最小张量理想可能误删原来可测的信息。

**例 3.3（实部分投影不保持张量信息）。** 写密度矩阵 $\rho=S+iA$，其中 $S^{\mathsf T}=S$、$A^{\mathsf T}=-A$。实单体效应只读到 $S$，而

$$
\operatorname{Re}(\rho\otimes\rho)=S\otimes S-A\otimes A.
$$

取 $\rho=I_2/2+iaJ_{12}$、$0<|a|<1/2$，并与 $I_2/2$ 比较。单体实统计相同，二体实联合统计可以不同。独立重制备和联合测量若未取得，就不能将此二体语境加入操作包。映射 $\rho\mapsto\rho^{\otimes2}$ 本身不是线性单孔语境，也不是可免费调用的复制通道。

### 3.2 纤维函子与张量理想

**定理 3.4（纤维函子的维数刚性）。** 若 $F:\operatorname{Rep}_{\mathbb C}(G)\to\operatorname{Vect}_{\mathbb C}$ 为 $\mathbb C$-线性强对称幺半函子，则 $\dim F(V)=\dim V$。任何满射 $\omega(V)\twoheadrightarrow F(V)$ 都是同构。

**证明。** 强对称幺半函子保持求值、余求值、交换与单位，因而保持范畴迹。在有限维表示范畴中

$$
\operatorname{tr}(\operatorname{id}_V)=(\dim V)\operatorname{id}_{\mathbf1}.
$$

线性保证单位上的标量不变，故 $\dim F(V)=\dim V$。同维空间之间的满射必为同构。$□$

**定理 3.5（半单表示范畴中的张量理想）。** 若 $G$ 为复约化代数群，则 $\operatorname{Rep}(G)$ 的张量态射理想只有零理想和全部态射。

**证明。** 若理想含非零 $f:V\to W$，由半单性可选简单表示 $S$ 与 $a:S\to V,b:W\to S$，经非零标量归一化使 $bfa=\operatorname{id}_S$。再张量 $\operatorname{id}_{S^*}$ 并取迹，理想中含 $(\dim S)\operatorname{id}_{\mathbf1}$。特征零使其可除，故含 $\operatorname{id}_{\mathbf1}$，继而包含每个 $\operatorname{id}_X$ 与所有态射。$□$

五模式中的 $25\to15$ 实部分投影可以是等变线性映射，却不能充当上述全范畴的维数压缩纤维函子。这里的商是态射理想商，不排除表示限制函子、张量子范畴或具有不同语义的商。

### 3.3 亚归一化操作的对偶障碍

**定理 3.6（亚归一化完全正操作的对偶障碍）。** 在非零有限维 Hilbert 空间和完全正、迹不增加映射组成的幺半范畴中，可对偶对象只有一维对象。这里的“对偶”要求余求值、求值和确定性蛇形复合都在该合同内合法。

**证明。** 若 $H$ 有对偶 $K$，余求值给出 $\omega_{HK}\ge0$、$\operatorname{tr}\omega\le1$，求值给出效应 $0\le E\le I$。蛇形复合把密度矩阵 $\rho$ 送到 $F(\rho)$。把末端效应 $E$ 与补效应 $I-E$ 的输出相加，得到固定的 $\omega_H$，故 $0\le F(\rho)\le\omega_H$。蛇形恒等式要求 $F=\operatorname{id}$，所以每个纯态投影 $P$ 都满足 $P\le\omega_H$。又 $\operatorname{tr}\omega_H\le1=\operatorname{tr}P$，故 $\omega_H=P$。当 $\dim H>1$ 时可选两个不同纯态，矛盾。一维对象的标准单位杯帽满足要求。$□$

这阻止把刚性表示范畴忠实、强对称幺半地实现为全部合法概率分支。包含全部 CP 映射且改变归一化合同的 CPM 构造属于另一语境，不能混用本定理。

## 4. 结构表示与实际源参数

### 4.1 十四维表示的交错平方

**定理 4.1（可见十四维表示的交错平方）。** 令 $V=\mathbb C^5$，$W=\operatorname{Sym}^2_0(V)$，用对称无迹矩阵实现。映射

$$
\kappa:\Lambda^2W\longrightarrow\mathfrak{so}_5,
\qquad
\kappa(S\wedge T)=[S,T]
$$

是 $\operatorname{SO}_5(\mathbb C)$-等变满射，并有

$$
\Lambda^2W\simeq\mathfrak{so}_5\oplus K_{81}.
$$

**证明。** $[S,T]^{\mathsf T}=-[S,T]$，且交换两输入变号，所以映射有定义。共同共轭与交换子相容，给出等变性。对 $i\ne j$，取 $S=E_{ii}-E_{jj}$、$T=E_{ij}+E_{ji}$，则

$$
[S,T]=2(E_{ij}-E_{ji}),
$$

这些元素张成 $\mathfrak{so}_5$，故满射。半单性给出分裂，且核维数为 $\binom{14}{2}-10=81$。$□$

这里的映射只重建伴随表示的类型和结构方向；固定一个 $S$ 仍不能决定源态的 $A$。本文不把 $K_{81}$ 的不可约性作为已证内容。

**定理 4.2（异源二次关系与伴随通道）。** 对两个独立制备的五模式来源 $\rho=S+iA$、$\sigma=T+iB$，若单体实层析与完整实联合层析均已获得，则恰可读出 $S,T,A\otimes B$。此外

$$
\ell:\Lambda^2\mathfrak{so}_5\longrightarrow\mathfrak{so}_5,
\qquad
A\wedge B\longmapsto[A,B]
$$

先在实李代数上为等变满射，复化后为 $\operatorname{SO}_5(\mathbb C)$-等变满射，核维数为 $35$。

**证明。** 联合实部分为 $S\otimes T-A\otimes B$；偏迹恢复 $S,T$，因此其余项给出 $A\otimes B$，反向也决定所有声明统计。交换子交错且等变；对互异 $i,j,k$，矩阵单位计算给 $[J_{ik},J_{kj}]=J_{ij}$，故满射。核维数为 $\binom{10}{2}-10=35$，并由半单性分裂。$□$

在下式中记 $V_5=V=\mathbb C^5$ 为标准五维表示，并记 $W_{14}=\operatorname{Sym}^2_0(V_5)$；这些符号只表示表示论对象，不表示可独立制备的物理资源。

结合对称平方分解，得到一个不要求两个三十五维核不可约的分解

$$
\mathfrak{so}_5\otimes\mathfrak{so}_5
\simeq\mathbf1\oplus V_5\oplus\mathfrak{so}_5\oplus W_{14}
\oplus K_{35}^{+}\oplus K_{35}^{-}.
$$

**命题 4.3（读出交换子不等于制备相位参考）。** 设五模式输入族对同时复共轭封闭，且其中某点 $[A,B]\ne0$。固定 $c\in\mathbb R\setminus\{0\}$，并假设下式在族内处处是合法密度矩阵。不存在一个固定的实 Kraus 确定性通道，在该族上都输出

$$
\frac{I_5}{5}+ic[A,B]
$$

作为归一化输出。

**证明。** 实 Kraus 通道满足 $\Phi(\bar X)=\overline{\Phi(X)}$。同时复共轭使 $(A,B)\mapsto(-A,-B)$，但 $[-A,-B]=[A,B]$。目标公式因而不变，通道协变性却要求输出变为 $I_5/5-ic[A,B]$，与非零交换子矛盾。$□$

偶阶相关量可以被完整测定，但数值并不自动成为可调用的非实量子资源。

## 5. 联合语境图与参考资源

### 5.1 异源联合观察图

**定义 5.1（异源联合观察图）。** 令 $\mathcal G=(\mathcal V,\mathcal E)$ 为有限连通无自环图，至少有两个顶点。顶点 $v$ 供应 $\rho_v=S_v+iA_v$，并假定 $A_v\ne0$。单体实层析及每条边上的独立异源制备与完整实联合层析均已另行获得，因此数据恰为 $S_v$ 和 $A_u\otimes A_v$，其中 $uv\in\mathcal E$。没有列出的联合制备不自动合法。

**定理 5.2（图的二分性分类）。** 另一组合法状态 $S_v+iB_v$ 给出同样数据，当且仅当

$$
B_v=t_vA_v,\qquad t_v\in\mathbb R^\times,\qquad t_ut_v=1\quad(uv\in\mathcal E),
$$

并满足各状态的正性条件。因此，非二分图仅剩同时复共轭的全局 $\pm$ 歧义；若二分图 $\mathcal V=\mathcal V_+\sqcup\mathcal V_-$，则

$$
 t_v=t\quad(v\in\mathcal V_+),\qquad
 t_v=t^{-1}\quad(v\in\mathcal V_-).
$$

一个已校准非零锚点使所有参数唯一；任一顶点的同源二份统计使连续尺度缩为全局 $\pm$。

**证明。** 若 $x\otimes y=x'\otimes y'\ne0$，选取在 $x$ 上非零的线性泛函，对等式一侧收缩可知 $y'$ 与 $y$ 共线，代回得到 $x'=tx$、$y'=t^{-1}y$。逐边使用这一事实并利用连通性，得到所有 $t_v$。沿路径比例交替为 $t,t^{-1}$；存在奇环时 $t=t^{-1}$，故 $t=\pm1$。无奇环时两侧交替恰给全部解。锚点固定 $t_v=1$；自张量固定 $t_v^2=1$。反向代入即可验证。$□$

**推论 5.3（正性截断与幅度稳定性）。** 若 $S_v\succ0$，令

$$
\kappa_v=\|S_v^{-1/2}(iA_v)S_v^{-1/2}\|_{\mathrm{op}}.
$$

二分图可行尺度恰满足

$$
\max_{v\in\mathcal V_-}\kappa_v\le |t|
\le\min_{v\in\mathcal V_+}\kappa_v^{-1}.
$$

若原状态均正定，则 $t=1$ 附近确有连续歧义。令 $r_v=\|A_v\|_F$，$y_{uv}=\log\|A_u\otimes A_v\|_F$，$x_v=\log r_v$，并令 $M_{\mathcal G}$ 每条边对应行在两个端点取 1，则 $y=M_{\mathcal G}x$，且

$$
M_{\mathcal G}^{\mathsf T}M_{\mathcal G}=D_{\mathcal G}+A_{\mathcal G}.
$$

在非二分情形，最小二乘重构满足

$$
\|\Delta x\|_2\le
\frac{\|\Delta y\|_2}
{\sqrt{\lambda_{\min}(D_{\mathcal G}+A_{\mathcal G})}}.
$$

**证明。** 实反对称矩阵 $S_v^{-1/2}A_vS_v^{-1/2}$ 乘 $i$ 后的谱成 $\pm$ 对，所以正性恰为 $|t_v|\kappa_v\le1$，代入定理即得区间。Frobenius 范数在纯张量上相乘，给出对数线性系统。逐行计算得到无符号图 Laplace 矩阵；其核由 $x_u+x_v=0$ 定义，奇环和连通性使核为零，二分时核为两侧取相反常数的一维空间。非二分时，伪逆范数是最小奇异值的倒数，给出误差界。$□$

该界只控制幅度的对数重构；完整方向的条件数以及实际层析样本成本仍需另行分析。

### 5.2 精确非实控制的参考条件

**定理 5.4（精确非实幺正的参考条件）。** 给定已知参考态 $\sigma$ 与固定数据维数 $d\ge2$，允许任意实 CPTP 处理器、实辅助态和丢弃，并要求对所有数据输入精确、确定性地实现已给定幺正通道。以下条件等价：

1. 能实现某个不与实正交矩阵成比例的幺正 $U$；
2. $\operatorname{supp}\sigma\perp\operatorname{supp}\bar\sigma$；
3. $\operatorname{tr}(\sigma\bar\sigma)=0$；
4. 能精确制备 $r=|+i\rangle\langle+i|$，其中 $|+i\rangle=(1,i)/\sqrt2$；
5. 能实现任意已给定幺正矩阵的通道。

这里允许按已知 $U$ 设计处理器，不是把未知黑盒升级为受控门。

**证明。** 实处理器若以程序 $\sigma$ 实现 $\operatorname{Ad}_U$，则以 $\bar\sigma$ 实现 $\operatorname{Ad}_{\bar U}$。将两个程序分解为支持内纯态。幺正通道的 Choi 矩阵秩一，所以带正权混合中的每个纯程序也实现同一个幺正通道。若两个支持不正交，可选非正交程序 $s,t$。共同 Stinespring 等距给

$$
\psi\otimes s\mapsto U\psi\otimes e_s,
\qquad
\psi\otimes t\mapsto\bar U\psi\otimes e_t.
$$

环境向量与 $\psi$ 无关：先对数据基向量使用输出纯性，再对两基向量叠加使用线性性。保持内积于是要求

$$
\langle s,t\rangle I=\langle e_s,e_t\rangle U^\dagger\bar U.
$$

左端非零，故 $U^\dagger\bar U$ 为标量；调整整体相位使 $U$ 实，矛盾。这证明必要性。正半定矩阵的迹积为零等价于支持正交，故 2 与 3 等价。

若 $S=\operatorname{supp}\sigma\perp\bar S$，选 $S$ 的正交基 $s_j=(a_j+ib_j)/\sqrt2$。由 $\langle s_j,s_k\rangle=\delta_{jk}$ 和 $s_j^{\mathsf T}s_k=0$，实向量组 $\{a_j,b_j\}$ 正交归一。实 Kraus 算子

$$
K_j=|0\rangle\langle a_j|+|1\rangle\langle b_j|
$$

满足 $K_js_k=\delta_{jk}|+i\rangle$，且 $\sum_jK_j^{\mathsf T}K_j$ 是 $S\oplus\bar S$ 上的投影。在正交补添加送至 $|0\rangle$ 的算子，即补成 CPTP 映射，把 $\sigma$ 送到 $r$。最后写 $U=X+iY$，令

$$
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix},
\qquad
\mathcal R(U)=X\otimes I+Y\otimes J.
$$

$\mathcal R(U)$ 实正交且 $\mathcal R(U)(\psi\otimes|+i\rangle)=U\psi\otimes|+i\rangle$，故能实现全部已知幺正。其余蕴含显然。$□$

**推论 5.5（有限混合参考的精确控制障碍）。** 取 $\sigma_\theta=(I+\theta Y)/2$、$Y=\begin{psmallmatrix}0&-i\\i&0\end{psmallmatrix}$、$0<\theta<1$。它可作为完备实联合读出参考，但任意有限 $n$ 份 $\sigma_\theta^{\otimes n}$ 都不能精确、确定性地实现真正非实幺正。

**证明。** 其虚部非零，故联合读出参考收缩公式可逆；另一方面

$$
\operatorname{tr}(\sigma_\theta\bar\sigma_\theta)=(1-\theta^2)/2>0.
$$

张量 $n$ 份后的迹积是此数的 $n$ 次幂，仍为正，应用定理 5.4。$□$

## 6. 终端原始元与有限谱代数

### 6.1 判别式重构

**定义 6.1（有限谱代数）。** 设 $k$ 为特征零域，$\mathcal A$ 为 $n$ 维有限 étale $k$-代数。对 $z\in\mathcal A$，记

$$
\mu_z(a)=za,\quad Q_z(Y)=\det(YI-\mu_z),\quad
\delta_z=\operatorname{disc}Q_z,\quad
\operatorname{Tr}_{\mathcal A/k}(a)=\operatorname{tr}(\mu_a).
$$

有限 étale 性保证扩至代数闭包后为 $n$ 个点的函数代数。

**定理 6.2（终端原始元与迹矩阵公式）。** 若 $\delta_z\ne0$，则 $\mathcal A=k[z]$，$1,z,\ldots,z^{n-1}$ 构成一组基。对任意 $f\in\mathcal A$，令 $0\le i,j<n$，

$$
H_{ij}=\operatorname{Tr}_{\mathcal A/k}(z^{i+j}),\qquad
b_i=\operatorname{Tr}_{\mathcal A/k}(fz^i).
$$

则

$$
\det H=\delta_z,\qquad
c=H^{-1}b,\qquad
f=\sum_{j=0}^{n-1}c_jz^j.
$$

系数唯一，且构造不需要选择谱根。这里采用判别式与 Vandermonde 平方一致的符号约定。

**证明。** 扩域后 $\mathcal A\otimes\bar k\simeq\bar k^n$。设 $z$ 的坐标为 $z_1,\ldots,z_n$；$Q_z(Y)=\prod_\nu(Y-z_\nu)$。判别式非零使它们互异，Vandermonde 矩阵 $V_{\nu j}=z_\nu^j$ 可逆，因而各幂成基。又 $H=V^{\mathsf T}V$，故 $\det H=(\det V)^2=\delta_z$。若 $\mathbf f$ 为 $f$ 的谱坐标，则 $b=V^{\mathsf T}\mathbf f$，$Hc=b$ 等价于 $Vc=\mathbf f$。所有条目原已在 $k$ 中，故系数属于 $k$ 且唯一。$□$

项目在局部化后使用

$$
 k=\mathbb Q(p,v),\qquad
 \mathcal A_k=k[x]/(\widehat R),\quad \deg\widehat R=18,
$$

并有两个终端元素 $A_R,M_R$，实际世界处的值为原始第七个 $J,M$ 读数。坏因子 $B$ 保留次数下降、重复根、失败逆元和零漂移等异常层，判别式分子记作 $P_J,P_M$。在 $p\ne24$、$BP_M\ne0$ 的开集上，

$$
A_R=\sum_{j=0}^{17}c_j(p,v)M_R^j.
$$

同一局部化代数中的其他读数也有同样表达。该式是同一完整世界的备选响应预测公式；它不等于在禁止复制和复位的标本上同时执行第七个 $J$ 与第七个 $M$，也不能把没有保留的历史记录当作免费输入。

**命题 6.3（重构的条件数）。** 在一个固定复数或实数专门化处，设 $Hc=b$，扰动后 $(H+\Delta H)(c+\Delta c)=b+\Delta b$。若 $\|H^{-1}\Delta H\|<1$，则

$$
\|\Delta c\|
\le
\frac{\|H^{-1}\|}{1-\|H^{-1}\Delta H\|}
\bigl(\|\Delta b\|+\|\Delta H\|\|c\|\bigr).
$$

因此判别式非零只给可逆性，不给统一稳定性。

**证明。** 相减后

$$
\Delta c=(I+H^{-1}\Delta H)^{-1}H^{-1}(\Delta b-\Delta Hc)。
$$

使用 Neumann 级数范数界即可。具体例子 $\mathcal A=\mathbb R^2$、$z=(0,\epsilon)$、$f=(0,1)$ 满足 $f=z/\epsilon$，且

$$
H=\begin{pmatrix}2&\epsilon\\\epsilon&\epsilon^2\end{pmatrix},
\qquad
\det H=\epsilon^2;
$$

当 $\epsilon\to0$ 时预测系数无界。$□$

### 6.2 有限承载的单值化

**命题 6.4（有限承载的单值化）。** 适当局部化后，上述十八维代数给出复基底开集 $U$ 上的十八层有限 étale 覆盖。限制在一条光滑连通曲线 $C\to U$ 上，解析单值表示为

$$
\pi_1(C)\longrightarrow S_{18}.
$$

复合

$$
\pi\longmapsto\operatorname{diag}(P_\pi,\operatorname{sgn}\pi)
$$

得到一个 $\operatorname{SO}_{19}(\mathbb C)$ 局部系统。其单值有限，并可在次数至多 $18!$ 的有限 étale 覆盖上全部平凡化。

**证明。** 有限 étale 覆盖在复解析拓扑中局部为十八张互不相交的图，沿环路延拓只置换图层，故给出置换表示。置换矩阵正交，且 $\det P_\pi\operatorname{sgn}\pi=1$，所以复合落入 $\operatorname{SO}_{19}$。单值核对应的覆盖次数为单值像的阶，至多 $|S_{18}|=18!$，在该覆盖上的单值恒等。$□$

十八层是代数候选承载；只有满足完整逆构造和严格实守卫的点才是实际来源。它不是五模式量子态的维数，也没有自然给出 $\operatorname{SO}_5$ 的稠密单值。若所选曲线非紧，紧化处的分歧数据必须保留；若选择 $\operatorname{SO}_{19}$ 为谱群，其对偶为 $\operatorname{Sp}_{18}$，所用 Hecke 存在性条件必须重新核查。

## 7. 真实碰撞对的一参数延拓

保留项目中完整原始世界 $W(r,b)=(P(r,b),g_{r,b},d_{r,b})$。其中 $g$ 是同一个次数不超过三的非零多项式，$d$ 是该世界的固定漂移。源文给出有理解析读数 $p,v,m,a$，在 $\lambda _0=2/5$ 处构造唯一精确零点，并严格保证 $0<r<1$、$b>0$、全部分母非零、$p\ne24$、$r_1>\lambda _0$ 和 $a(W_2)<a(W_3)$。

**定义 7.1（参数化实际碰撞方程）。** 设

$$
F_\lambda(b_0,r_1,b_1)=
\begin{pmatrix}
 p(\lambda,b_0)-p(r_1,b_1)\\
 v(\lambda,b_0)-v(r_1,b_1)\\
 m(\lambda,b_0)-m(r_1,b_1)
\end{pmatrix}.
$$

项目在有理盒 $X$ 和有理矩阵 $C_0$ 上证明

$$
\sup_{x\in X}\|I-C_0D_xF_{\lambda _0}(x)\|_\infty
\le576\cdot10^{-32}<1,
$$

以及严格自映射和全部来源守卫。

**定理 7.2（完整原始碰撞族）。** 存在 $\epsilon>0$ 与唯一局部实解析函数 $x(\lambda)=(b_0(\lambda),r_1(\lambda),b_1(\lambda))$，使 $F_\lambda(x(\lambda))=0$，并经过项目精确零点。定义

$$
W_2(\lambda)=W(\lambda,b_0(\lambda)),
\qquad
W_3(\lambda)=W(r_1(\lambda),b_1(\lambda)),
$$

以及 $p(\lambda)=p(\lambda,b_0(\lambda))$、$v(\lambda)=v(\lambda,b_0(\lambda))$。则

$$
W_2(\lambda)\ne W_3(\lambda),\quad
W_2,W_3\in C(p(\lambda),v(\lambda)),\quad p(\lambda)\ne24,
$$

并且

$$
 m(W_2)=m(W_3),\qquad a(W_2)<a(W_3).
$$

足够接近 $2/5$ 的每个有理 $\lambda$ 给出实代数的全部世界参数和增益系数。

**证明。** 所给范数界使 $C_0D_xF_{\lambda _0}(x_*)$ 可逆，因此雅可比可逆。有理映射在守卫域内解析，实解析隐函数定理给出唯一分支，且

$$
 x'(\lambda)=-(D_xF_\lambda(x(\lambda)))^{-1}\partial_\lambda F_\lambda(x(\lambda)).
$$

所有严格不等式由连续性在小区间保持。原有理构造持续保证每个世界的前五个原始读数；三条新方程分别保持共同 $p,v,m$。因此两个世界仍使用各自完整增益和固定漂移，而非只匹配有限伪造样本。

在 $\lambda _0$ 处，收缩和自映射都有严格余量；紧盒上的连续性使其在小参数区间内一致保持。对有理 $\lambda$，清除始终非零的分母，盒内唯一零点成为由有理多项式及有理不等式定义的半代数单点。实闭域消去或投影到每个坐标说明其坐标为实代数数；有理函数构造的其余量亦然。$□$

**推论 7.3（碰撞族不能任意跳出代数异常层）。** 沿足够小的连通参数区间，至少有下列一个恒等式处处成立：

$$
B(p(\lambda),v(\lambda))\equiv0,
\qquad\text{或}\qquad
P_M(p(\lambda),v(\lambda))\equiv0.
$$

**证明。** 项目的全平面必要覆盖给出 $D_M\subseteq\{B=0\}\cup\{P_M=0\}$，故两个解析函数的乘积恒零。若第一个不恒零，它在某个开子区间非零，第二个就在该区间恒零，再由解析恒等原理在整个连通区间恒零。$□$

这不证明基点 $(p(\lambda),v(\lambda))$ 非常值，也不产生同基的独立 $J$ 碰撞对。原目标的四个完整世界和两对内不等式仍需全部满足。

## 8. 边界响应的组合与热带障碍

### 8.1 Schur 消元

**定义 8.1（边界二次型）。** 把实对称矩阵写成

$$
Q=\begin{pmatrix}A&B\\B^{\mathsf T}&K\end{pmatrix},
\qquad K>0,
$$

第一组为完整保留端口，第二组为内点。定义

$$
S(Q)=A-BK^{-1}B^{\mathsf T},
\qquad
L_Q=\begin{pmatrix}I\\-K^{-1}B^{\mathsf T}\end{pmatrix}.
$$

也可取 $Q=H-zI$，只要求 $K$ 可逆来定义代数响应；最小化和正定扰动另需 $K>0$。

**定理 8.2（组合、微分与扰动）。** 边界响应满足

$$
 u^{\mathsf T}S(Q)u
 =\min_v (u,v)^{\mathsf T}Q(u,v).
$$

联合被消内块正定时，任意分阶段消元与一次消元相同。对可微矩阵路径，若始终 $K(t)>0$，则

$$
\frac{d}{dt}S(Q(t))=L_{Q(t)}^{\mathsf T}\dot Q(t)L_{Q(t)}.
$$

若两个端点的内块 $K_j\ge\kappa I$、$\|B_j\|\le M$，则

$$
\|S(Q_1)-S(Q_0)\|
\le\left(1+\frac{M^2}{\kappa^2}\right)\|Q_1-Q_0\|.
$$

**证明。** 配方给出

$$
(u,v)^{\mathsf T}Q(u,v)
=u^{\mathsf T}S(Q)u+
(v+K^{-1}B^{\mathsf T}u)^{\mathsf T}K(v+K^{-1}B^{\mathsf T}u).
$$

唯一极小点为 $v=-K^{-1}B^{\mathsf T}u$。对同一严格凸内点函数逐组最小化等于联合最小化，证明结合律。用 $\frac d{dt}K^{-1}=-K^{-1}\dot K K^{-1}$ 微分 $S$，得到四项，恰为 $L_Q^{\mathsf T}\dot QL_Q$。沿两端点的直线路径仍有 $K(t)\ge\kappa I$、$\|B(t)\|\le M$，且 $\|L_{Q(t)}\|^2\le1+M^2/\kappa^2$；积分即得误差界。$□$

### 8.2 Lagrangian 拼接

**定理 8.3（Lagrangian 边界拼接）。** 在端口空间 $V_B\oplus V_B^*$ 上取辛形式

$$
\omega((u,p),(v,q))=q(u)-p(v).
$$

响应图 $\mathcal L_Q=\{(u,S(Q)u):u\in V_B\}$ 是 Lagrangian 子空间。把两个网络沿公共端口 $C$ 拼接，要求电势相等、两侧电流和为零；若待消公共块可逆，则拼接后的响应等于组合关系所得的响应。正定时此操作同时等于能量的逐组最小化。

**证明。** $S(Q)$ 对称，故其图上的 $\omega$ 为零，且图维数为总辛维数的一半。拼接前两个边界二次型相加，公共变量只保留一份。对公共变量的驻值方程正是两侧电流和为零。公共待消块可逆时驻值解唯一，代回得到相应 Schur 补；这与先解每侧内点再解公共端口、或直接组合两侧关系所得方程相同。若公共待消块正定，再应用定理 8.2。$□$

边界关系的范畴化有成熟先例，但本文使用的是显示的有限维二次型和驻值公式，不把可逆关系当成量子概率通道。消元矩阵在谱参数的正则区域有定义，跨内部极点时须保留关系或重新选图。

### 8.3 四点律与热带证书

项目边界几何定理适用于有限树上每点完整 $\mathbb R^r$ 纤维、任意实边块和任意对称对角块，仅要求消去内块正定。固定其他保留端口接地，令 $W_{ij}=-S(Q)_{ij}$、$d_{ij}=|\det W_{ij}|$，则

$$
\min\{d_{ab}d_{cd},d_{ac}d_{bd},d_{ad}d_{bc}\}
$$

至少取得两次。行列式使用全部奇异值的乘积，不能替换为单个块的算子范数。

**定理 8.4（热带化、换基与误差证书）。** 假设涉及的六个 $d_{ij}>0$，令 $w_{ij}=\log d_{ij}$。则每个四元组满足

$$
\min\{w_{ab}+w_{cd},w_{ac}+w_{bd},w_{ad}+w_{bc}\}
$$

至少取得两次。这是秩二热带 Grassmann 关系。在局部可逆端口换基 $G_i$ 下，$w_{ij}$ 加上 $\log|\det G_i|+\log|\det G_j|$，三个配对和同加一个量，故条件保持。

若测得六个对数值 $\widehat w_{ij}$，其三个配对和排序为 $s_1\le s_2\le s_3$，任何合法树数据满足

$$
\max_{i<j}|w_{ij}-\widehat w_{ij}|
\ge\frac{s_2-s_1}{4}.
$$

对单独这一四点条件，该界可达到。

**证明。** 取对数保持次序，并把乘积变为和，得到热带关系。合同换基给 $W'_{ij}=G_i^{\mathsf T}W_{ij}G_j$，取行列式即得加法。若每条边误差至多 $\epsilon$，每个配对和误差至多 $2\epsilon$；要消除最小和与第二小和的间隔，必须 $s_2-s_1\le4\epsilon$。反之，把最小配对的两个坐标各增加 $(s_2-s_1)/4$，第二小配对的两个坐标各减少同样数量，另外两个坐标不动，就使前两和相等且不大于第三和，证明单个四点条件的达到性。$□$

多于四个端口时，逐四点达到不保证存在共同的全局树响应。零行列式没有有限对数，仍属于原始四点律的边界而不属于本对数定理。一般可逆换基保持关系，但不保持原单位下的算子范数误差。

**推论 8.5（输入误差不能消除全部树障碍）。** 对循环目标 $S(u,v)\otimes I_r$、$u>v\ge0$，合法树响应有 $\delta_{\mathrm{off}}\ge(u-v)/2$。设 $Q_0$ 来自项目树模型，$Q_1$ 与其使用同一端口及内点分块。若源矩阵扰动满足定理 8.2 的共同间隔条件且 $\|Q_1-Q_0\|\le\epsilon$，则

$$
\delta_{\mathrm{off}}(S(Q_1))
\ge\frac{u-v}{2}-\left(1+\frac{M^2}{\kappa^2}\right)\epsilon.
$$

**证明。** 每个块的范数不超过整个矩阵的算子范数；对每块应用三角不等式，再使用项目下界与 Schur 扰动界。$□$

## 9. 二通道边界到五维正交输运

### 9.1 可逆转移合同

**定义 9.1（二通道转移合同）。** 每个端点保留完整 $\mathbb R^2$，同一固定谱参数下的两端口响应为

$$
S_D=\begin{pmatrix}-D&I_2\\I_2&0\end{pmatrix},
\qquad D=D^{\mathsf T}.
$$

输入电流取向内负号，输出取向外正号：$p_{\mathrm{in}}=-q_{\mathrm{left}}$、$p_{\mathrm{out}}=q_{\mathrm{right}}$。于是

$$
\begin{pmatrix}u_{\mathrm{out}}\\p_{\mathrm{out}}\end{pmatrix}
=T(D)\begin{pmatrix}u_{\mathrm{in}}\\p_{\mathrm{in}}\end{pmatrix},
\qquad
T(D)=\begin{pmatrix}D&-I_2\\I_2&0\end{pmatrix}.
$$

这也是递推 $u_{n+1}=D_nu_n-u_{n-1}$ 的状态转移。四个块若要作为操作使用，必须在同一参数下独立可调用，并允许任意有限重复组合。

$S_D$ 可由两个顶点、边块 $I_2$、对角块 $-D,0$ 的二次型实现；所以它属于任意对称块边界模型。它不自动属于原生固定单位权来源轨道，也不把非正定二次型宣称为被动能量。

**定理 9.2（四个块的 Zariski 稠密性）。** 令

$$
D_0=0,\qquad D_1=E_{11},\qquad D_2=E_{22},\qquad D_3=E_{12}+E_{21}.
$$

每个 $T(D_j)$ 保持标准辛形式

$$
J_4=\begin{pmatrix}0&I_2\\-I_2&0\end{pmatrix}.
$$

它们生成的群在 $\operatorname{Sp}_4(\mathbb C)$ 中 Zariski 稠密。若全部正向门词都许可，其正向半群也 Zariski 稠密。

**证明。** 直接计算 $T(D)^{\mathsf T}J_4T(D)=J_4$。记 $T_0=T(0)$，则 $T_0^4=I$，并且

$$
T(D)T_0^{-1}=U(D)=\begin{pmatrix}I&D\\0&I\end{pmatrix},
\qquad
T_0U(D)T_0^{-1}=\begin{pmatrix}I&0\\-D&I\end{pmatrix}.
$$

$U(D)^n=U(nD)$。一个多项式若在所有正整数 $n$ 处消失，就在参数直线上恒零，故闭包包含每个 $D_j$ 方向的全部复一参数上下幺幂群。三个非零 $D_j$ 张成全部对称二阶矩阵，所以 Lie 代数包含

$$
X_B=\begin{pmatrix}0&B\\0&0\end{pmatrix},\qquad
Y_C=\begin{pmatrix}0&0\\C&0\end{pmatrix}
\quad(B,C\text{ 对称}).
$$

它们的括号为 $\operatorname{diag}(BC,-CB)$。对称矩阵乘积张成 $M_2$：取一个因子为 $I$ 得全部对称矩阵，取 $B=E_{11}$ 或 $E_{22}$、$C=E_{12}+E_{21}$ 得 $E_{12},E_{21}$。因此得到全部

$$
\begin{pmatrix}A&B\\C&-A^{\mathsf T}\end{pmatrix},
$$

即 $\mathfrak{sp}_4$。$\operatorname{Sp}_4(\mathbb C)$ 连通，闭子群具有完整 Lie 代数即为全群。

正向半群中已经含 $T_0^{-1}=T_0^3$ 以及上述 $U(D_j)$ 的全部正整数幂；其闭包对乘法封闭，并包含整个一参数群。因此同一论证给出全 $\operatorname{Sp}_4$。$□$

这些显式矩阵为整数矩阵，其实际生成群在实矩阵的通常拓扑中离散。因此 Zariski 稠密性不等于可在算子范数下逼近任意实辛矩阵，更不等于已经实现任意量子控制。若权限只允许有限长度门词，本文也不把有限执行集合称为稠密。

### 9.2 原始外幂与中心核

**定义 9.3（五维原始外幂）。** 令 $U=\mathbb R^4$ 有辛基 $e_1,f_1,e_2,f_2$，

$$
\Omega=e_1\wedge f_1+e_2\wedge f_2,
\qquad
\nu=e_1\wedge f_1\wedge e_2\wedge f_2.
$$

令

$$
V_5=\{\alpha\in\Lambda^2U:\alpha\wedge\Omega=0\},
\qquad
q(\alpha,\beta)\nu=-\alpha\wedge\beta.
$$

对 $\operatorname{Sp}_4$ 元素，$\Omega$ 是由辛形式反演得到的不变二向量。

**定理 9.4（辛四维到正交五维）。** $V_5$ 维数为 5，$q$ 非退化，实符号为 $(3,2)$。原始外幂作用给出

$$
\varpi:\operatorname{Sp}_4(\mathbb R)\longrightarrow\operatorname{SO}(3,2),
\qquad
\ker\varpi=\{\pm I_4\}.
$$

复化后 $\varpi:\operatorname{Sp}_4(\mathbb C)\twoheadrightarrow\operatorname{SO}_5(\mathbb C)$ 满射。

**证明。** $\Omega\wedge\Omega=2\nu$，故 $\Lambda^2U=\mathbb R\Omega\oplus V_5$。用基

$$
 e_1\wedge f_1-e_2\wedge f_2,\quad
 e_1\wedge e_2,\ f_1\wedge f_2,\quad
 e_1\wedge f_2,\ e_2\wedge f_1
$$

计算：第一项的 $q$ 值为 2，其余四项构成两组非退化双曲平面，故符号为 $(3,2)$。辛作用保持 $\Omega,\nu$ 和楔积，故保持 $q$；而 $\det(\Lambda^2g)=(\det g)^3=1$，在 $\mathbb R\Omega$ 上为恒等，所以五维行列式也是 1。

若五维作用为恒等，则全部 $\Lambda^2U$ 上作用恒等。于是每个二维平面均保持；固定一条直线，取所有包含它的二维平面的交，可知每条直线保持。故 $g$ 是标量，且外平方恒等要求标量为 $\pm1$。反向显然，复数上同理。核有限，所以导出 Lie 映射单射；两边 Lie 维数同为 10，故为同构。复 $\operatorname{SO}_5$ 连通，像含单位邻域，从而满射。$□$

实形式是非紧的 $\operatorname{SO}(3,2)$，不是紧的 $\operatorname{SO}(5)$。二者复化后使用同一个 $\operatorname{SO}_5(\mathbb C)$，但物理范数、可执行操作和概率解释不同。所有中心信息在进入五维表示时已发生一次明确的二重压缩。

## 10. 中心提升与具体 Hecke 接口

### 10.1 路径、门和表示态射

**命题 10.1（群胚完备化的条件）。** 设 $\mathcal P$ 是由门和关系生成的路径范畴。线性输运 $T:\mathcal P\to\operatorname{Vect}$ 延拓到把指定门全部形式倒置的群胚，当且仅当这些门的矩阵均可逆。延拓在给定识别下唯一。若 $V$ 是 $G$ 的忠实表示，则门矩阵 $\rho_V(g)$ 是 $\operatorname{Rep}(G)$ 中的态射，当且仅当 $g\in Z(G)$。

**证明。** 函子必须保持逆，故可逆性必要；反之把每个形式逆送到矩阵逆，原关系和逆关系均保持，给出唯一延拓。第二项中，等变性恰要求 $\rho_V(g)\rho_V(h)=\rho_V(h)\rho_V(g)$ 对所有 $h$ 成立，忠实性把它等价为 $gh=hg$。$□$

实验门应放在路径输运或纤维函子的张量自同构中；表示态射则是与全部群作用相容的结构映射。线性逆也不自动是合法仪器逆。例如

$$
D_p(X)=pX+(1-p)\operatorname{tr}(X)I/d,\qquad 0<p<1,
$$

虽可逆，却把纯态逆送为 $p^{-1}P-(1-p)I/(pd)$，在正交方向上有负特征值。

### 10.2 曲面局部系统

**定义 10.2（附加的底曲面选择）。** 选一条光滑连通、射影复曲线 $X$，genus 为 4，固定基点和标准生成元

$$
\pi_1(X)=\left\langle a_0,b_0,\ldots,a_3,b_3:
\prod_{j=0}^3[a_j,b_j]=1\right\rangle.
$$

令 $\widetilde\rho(a_j)=T(D_j)$、$\widetilde\rho(b_j)=I_4$，并令 $\rho=\varpi\circ\widetilde\rho$。这是另行选定的曲面模型，不把它识别为原项目关系球面。

**外部定理 10.3（几何 Satake 与无分歧几何朗兰兹）。** 令 $G$ 为连通约化复代数群，$\check G$ 为其朗兰兹对偶群。采用特征零、光滑射影复曲线和标准半密度归一化。几何 Satake 给出对称张量等价

$$
\operatorname{Rep}(\check G)\simeq\operatorname{Sat}_G.
$$

在不可约、没有真抛物水平约化的 $\check G$ 局部系统 $E$ 上，已证明的无分歧几何朗兰兹接口提供非零 Hecke 本征对象 $\mathcal F_E$，以及对表示、态射、张量和多点融合相容的同构

$$
\varepsilon_R:H_R(\mathcal F_E)\xrightarrow{\sim}E_R\boxtimes\mathcal F_E.
$$

本文在特征零的 de Rham $\mathrm{D}\text{-}\mathrm{mod}$（等价地，在相应的 D-mod 范畴）语境中使用这一接口；改用 ℓ-adic 或其他系数范畴时，必须重新声明系数和本征对象定义。这是具名文献的外部输入，并非本文或 Lean 的证明；其系数、曲线、归一化和分歧范围必须保持在上述条件内。

**定理 10.4（从边界输运产生不可约谱对象）。** $\widetilde\rho$ 和 $\rho$ 都是良定义表示，分别在 $\operatorname{Sp}_4(\mathbb C)$ 和 $\operatorname{SO}_5(\mathbb C)$ 中 Zariski 稠密。由 $\rho$ 得到的平坦 $\operatorname{SO}_5(\mathbb C)$ 主局部系统 $E$ 不存在到任何真抛物子群的水平约化；这里约化须保持连接，而不是底层主丛的任意约化。

**证明。** 所有 $b_j$ 的像为单位，所以每个交换子像为单位，曲面关系成立。定理 9.2 给出第一种稠密性，定理 9.4 的满射把它送到第二种。表示构造平坦主丛 $(\widetilde X\times\operatorname{SO}_5(\mathbb C))/\pi_1(X)$。若它约化到真抛物子群，其单值共轭后落入该闭真子群，与稠密性矛盾。在射影复曲线上，用 Riemann–Hilbert 与代数化得到相应代数平坦主丛；这一代数化步骤调用外部定理 10.3 所列的正则接口。$□$

**定理 10.5（提升的二值数据）。** 固定上述 $\rho$、一个提升 $\widetilde\rho$、五维识别和 genus-4 曲面。所有 $\operatorname{Sp}_4$ 提升表示的集合，以及带给定五维识别的提升主局部系统同构类，构成

$$
\operatorname{Hom}(\pi_1(X),\mu_2)=H^1(X,\mu_2)
$$

的挠集。因此恰有 $2^8=256$ 个提升同构类。提升群胚的每个对象仍有 $\mu_2$ 自同构，故该群胚不是离散的 256 点集合。来自 $\operatorname{Rep}(\operatorname{SO}_5)$ 的全部张量表示均不能区分这些提升；四维标准 $\operatorname{Sp}_4$ 表示不属于由五维表示生成的中心平凡张量子范畴。

**证明。** 若 $\widetilde\rho'$ 是另一提升，逐点之比落在中心 $\mu_2$，写作 $\widetilde\rho'(\gamma)=\chi(\gamma)\widetilde\rho(\gamma)$。中心性和表示乘法律给 $\chi(\gamma\eta)=\chi(\gamma)\chi(\eta)$。反之任意此类特征都给提升，且作用自由传递。genus 4 曲面的阿贝尔化是 $\mathbb Z^8$，故有 $2^8$ 个特征。

若两个提升在保持给定五维识别下同构，投影后的共轭元须中心化稠密 $\rho$；$\operatorname{SO}_5$ 中心平凡，故该元的提升属于 $\mu_2$，共轭不改变提升。所有从 $\operatorname{SO}_5$ 拉回的表示上，$-I_4$ 作用为恒等，所以扭转 $\chi$ 不影响它们。此性质在张量、对偶、子对象和商下保持，而四维标准表示上 $-I_4$ 作用为负恒等，故该表示不能由五维中心平凡对象生成。$□$

**定理 10.6（Hecke 自然性）。** 在前述二通道块合同、独立门调用和曲面选择下，取 $G=\operatorname{Sp}_4$、$\check G=\operatorname{SO}_5$。则定理 10.4 的 $E$ 在外部定理 10.3 的范围内有非零 Hecke 本征对象。显式映射

$$
\kappa:\Lambda^2W_{14}\twoheadrightarrow\mathfrak{so}_5,
\qquad
\ell:\Lambda^2\mathfrak{so}_5\twoheadrightarrow\mathfrak{so}_5
$$

均产生平行局部系统态射以及 Hecke 态射，并满足

$$
\varepsilon_{R'}\circ H_\phi(\mathcal F_E)
=(\phi_E\boxtimes\operatorname{id})\circ\varepsilon_R
\qquad(\phi=\kappa,\ell).
$$

此外 $\operatorname{Sat}_G(\mathfrak{so}_5)$ 是卷积张量结构中的 Lie 代数对象。

**证明。** 稠密性已核对外部定理的不可约性假设，故得到 $\mathcal F_E$。等变映射在平坦局部平凡化之间与转移函数交换，所以拼成平行态射。Satake 为对称张量函子，将交错平方和相关态射送入卷积范畴。本征结构对态射的自然性正是显示的等式。矩阵交换子的交错性与 Jacobi 恒等式通过张量函子保持。$□$

**定理 10.7（非零本征对象不能丢弃整个非零表示通道）。** 设某点的 Hecke 作用与一个非零本征对象 $\mathcal F$ 满足上述自然性。则每个非零表示态射 $\phi:R\to R'$ 都满足 $H_{\phi,x}(\mathcal F)\ne0$。若 Hecke 作用及本征结构下降到某个线性商范畴，且 $\mathcal F$ 的像仍非零，同样的结论在商中成立。

**证明。** 纤维函子忠实，故 $\phi_x$ 是非零线性映射。在基下选一个非零矩阵系数 $c$。若 $\phi_x\otimes\operatorname{id}_{\mathcal F}=0$，前后复合相应坐标注入与投影，得到 $c\operatorname{id}_{\mathcal F}=0$，故 $\mathcal F=0$，矛盾。商中仍有同一本征同构和非零对象，重复论证。$□$

这些结论建立的是特定线性边界模型到谱局部系统和 Hecke 结构的连接；它没有把所有原生观察仪器送进忠实强张量函子。定理 3.2 和 3.6 正说明了限定接口的必要性。

## 11. Green 稳定性的精确变分边界

### 11.1 固定模型

**定义 11.1（固定模型和临界相对系数）。** 固定项目双墙模型的柱体、实际相位环面、源点 $o$、光滑正密度 $\rho$、光滑正定水平协方差 $A$、同一 killed 热半群时钟及完整单位源 Green 场。在 $L^2(\mu)$ 中记自由闭型和原型域为 $T,\mathcal F$，Green 势型为 $V\ge0$，并令

$$
q_g=T-gV.
$$

项目给出

$$
V[f]\le KT[f]+B\|f\|^2
$$

及归一化集中序列 $f_s$，其中 $T[f_s]\to\infty$、$\liminf V[f_s]/T[f_s]\ge D_v/E_v>0$。这里 $0<K<\infty$、$0\le B<\infty$、$0<E_v,D_v<\infty$。定义

$$
a_*=\inf\{a\ge0:\ \exists b\ge0,
V[f]\le aT[f]+b\|f\|^2\quad\forall f\in\mathcal F\},
\qquad
 g_c=a_*^{-1}.
$$

**定理 11.2（固定模型的精确相区）。** $0<a_*<\infty$ 且

$$
\frac1K\le g_c\le\frac{E_v}{D_v}.
$$

对 $0<g<g_c$，$q_g$ 在原型域 $\mathcal F$ 上闭、半有界，移位型范数与自由型范数等价，预解紧，归一化最低值达到。对 $g>g_c$，

$$
\inf_{\|f\|=1,\ f\in\mathcal F}q_g[f]=-\infty.
$$

在 $g=g_c$，不可能同时半有界并在原型域 $\mathcal F$ 上闭。

**证明。** 粗相对界给 $a_*\le K$。沿集中序列将任意合法相对界除以 $T[f_s]$，低阶项趋零，故 $a\ge D_v/E_v$，得到正性与上下界。

若 $g<g_c$，可选 $a_*<a<1/g$ 与对应 $b$。于是

$$
(1-ga)T[f]+\|f\|^2
\le q_g[f]+(gb+1)\|f\|^2
\le T[f]+(gb+1)\|f\|^2.
$$

中间正定型的范数与完备自由型范数等价，故原域上闭且半有界。自由型域的紧嵌入由固定模型提供；等价范数保持该性质，故预解紧。归一化极小序列在型范数中有界，取弱收敛子列并用紧嵌入得到强 $L^2$ 收敛，其极限仍归一化；移位闭型的弱下半连续性给最低值达到。

若 $g>g_c$ 而 $q_g\ge-C\|\cdot\|^2$，则 $V\le g^{-1}T+(C/g)\|\cdot\|^2$，与 $g^{-1}<a_*$ 矛盾。二次齐次性使不半有界等价于所述归一化下确界为负无穷。

最后假设 $q_{g_c}$ 半有界且在 $\mathcal F$ 上闭。选 $c$ 足够大，使 $\|f\|_q^2=q_{g_c}[f]+c\|f\|^2$ 成为 Hilbert 范数。因 $V\ge0$，从自由型 Hilbert 范数到此范数的恒等映射连续且双射。开映射定理使其逆连续，故可取 $0<\epsilon<1$ 使

$$
q_{g_c}[f]+c\|f\|^2\ge\epsilon(T[f]+\|f\|^2).
$$

整理给

$$
V\le(1-\epsilon)a_*T+((c-\epsilon)/g_c)\|f\|^2,
$$

必要时把低阶系数增为非负，即与 $a_*$ 的下确界定义矛盾。$□$

**推论 11.3（高能量表征）。**

$$
a_*=
\lim_{R\to\infty}
\sup_{\substack{\|f\|=1\\T[f]\ge R}}
\frac{V[f]}{T[f]}.
$$

**证明。** 集中序列使尾集非空；上确界随 $R$ 不增，粗界保证极限有限。每个合法相对界在高能量极限中给出上界 $a$，所以右端不超过 $a_*$。反之若 $a$ 大于右端，足够高能量处有 $V\le aT$；低能量归一化部分由粗界 $V\le KR+B$ 控制。齐次化给全域相对界，令 $a$ 降至极限即可。$□$

**定理 11.4（协方差与密度缩放）。** 保持源点、底域和单位源归一化不变，对常数 $c,d>0$ 有

$$
\boxed{g_c(cA,d\rho)=c^2d\,g_c(A,\rho).}
$$

因此没有不对密度与协方差归一化的全模型统一正稳定阈值。

**证明。** 新测度为 $\mu'=d\mu$，微分算子 $L'=cL$。相对于新测度的热核为 $p'_t(x,y)=d^{-1}p_{ct}(x,y)$，完整 Green 场因此为 $\Gamma'=(cd)^{-1}\Gamma$。从而 $T'=cd\,T$、$V'=c^{-1}V$，并有

$$
q'_g=cd\left(T-\frac{g}{c^2d}V\right).
$$

原型域集合不变，相区在正倍数下保持，给出缩放律。令 $c\downarrow0$ 即排除所述统一阈值。$□$

这里给出的是固定模型的变分分界，并没有计算某个具体模型的闭式临界常数。临界点可能半有界、可能需要扩大闭型域；单墙和无墙模型的崩塌结论仍须按项目原文的独立合同使用（见来源 5 的定理 3.1）。体积指数、记忆类数和表示维数来自不同定义，不能因数字相等而互相替代。

## 12. 组合结论与下一阶段义务

**定理 12.1（本稿的组合主定理）。** 在各节声明的原始来源、许可语言和资源条件下，以下结论可以同时成立：

1. 对有限维 $V$、$\mathcal O\subseteq V^*$ 和不变的线性分支 $T_a$，合法未来由全权限状态的有限传播计算；任务锁存与全部未来记忆具有各自的下界。
2. 原始终端 $M$ 在局部化且 $\delta_{M_R}\ne0$ 的开集上生成十八维谱代数；项目守卫 $p\ne24$、$BP_M\ne0$ 用作该非退化条件的声明充分条件，而新取得的真实碰撞族被约束在显式异常层。
3. 联合语境可以恢复旧商遗漏的信息；若要保留张量组合，必须使用最大相容盲核，不能将非零表示通道作为刚性张量理想直接删除。
4. 固定块边界的 Schur 拼接产生 Lagrangian 关系；在独立可调用的二通道、四种显式块和曲面选择条件下，构造 Zariski 稠密的五维正交谱局部系统。
5. 在外部定理 10.3 的光滑射影特征零、不可约、无分歧归一化范围内，所得局部系统提供 Hecke 本征对象；表示态射的自然性通过 Satake 接口传递。
6. 五维投影保留全部 $\operatorname{SO}_5$ 系数态射，却遗漏八个独立中心二值参数；相位参考的读取能力不自动提供精确非实控制。
7. 固定 Green 模型的稳定区由自身的 $g_c$ 控制，常数缩放 $A\mapsto cA$、$\rho\mapsto d\rho$ 时临界值乘以 $c^2d$；一般模型变化仍需另行估计。

**证明。** 分别应用定理 2.2、命题 2.4、推论 2.5、定理 3.2、3.4、3.6、4.1、4.2、5.2、5.4、6.2、7.2、8.2、8.3、8.4、9.2、9.4、10.4、10.5、10.6、10.7 和 11.2、11.4。每个连接使用已显示的对象、映射和合同；没有把不同模型的资源、谱参数、时钟或外部定理的适用范围直接等同。$□$

本卷建立的是一条具体的边界输运到 Hecke 的条件构造，以及它与观察压缩、谱代数和稳定性之间的约束。下一阶段的数学义务是：

1. 在项目原生固定来源轨道中，构造或排除四个二通道边界块的共同实现，并逐项保留时钟、端口、度量、概率与调用权限。
2. 对同基独立双碰撞，实际给出四个完整世界，或在 $\{B=0\}\cup\{P_J=P_M=0\}$ 上完成所有异常层的全域排除。
3. 若使用关系球面或非紧谱曲线，声明穿孔、局部单值、层级结构和相应分歧 Hecke 范畴；本文的射影 genus-4 选择不消除这些义务。
4. 若要求计算或物理可执行性，证明迹矩阵条件数、参考供应、联合测量和成功率的成本界。有限维可定义与群的 Zariski 稠密都没有提供这些成本界。

## 参考文献与来源

1. trureturing，固定提交 `2d7d995ea59799e2e68c0e6d6b13da9ed5eebf89`，[An exact unequal-diagonal pair for the original terminal M response](https://github.com/the-omega-institute/trureturing/blob/2d7d995ea59799e2e68c0e6d6b13da9ed5eebf89/docs/develop/theory/FIB_STRICT_REAL_UNEQUAL_DIAGONAL_ACTUAL_M_PAIR.md)，定理 1.3、引理 4.2、定理 4.3、§6、§8。
2. trureturing，同一固定提交，[FIB Singular Response Children Exclusion](https://github.com/the-omega-institute/trureturing/blob/2d7d995ea59799e2e68c0e6d6b13da9ed5eebf89/docs/develop/theory/FIB_SINGULAR_RESPONSE_CHILDREN_EXCLUSION.md)，§§10–11。
3. trureturing，同一固定提交，[FIB Boundary Geometry Continuation X](https://github.com/the-omega-institute/trureturing/blob/2d7d995ea59799e2e68c0e6d6b13da9ed5eebf89/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_X.md)，定义 263.1、定理 263.2–263.3。
4. trureturing，同一固定提交，[Native variable-coefficient Green stability](https://github.com/the-omega-institute/trureturing/blob/2d7d995ea59799e2e68c0e6d6b13da9ed5eebf89/docs/develop/theory/FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md)，定义 1.1–1.2、命题 4.2、定理 5.1、6.1、7.1。
5. trureturing，同一固定提交，[Native two-control Green attraction, critical stability and periodic binding](https://github.com/the-omega-institute/trureturing/blob/2d7d995ea59799e2e68c0e6d6b13da9ed5eebf89/docs/develop/theory/FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md)，定义 1.2–1.3、定理 3.1；用于单墙与无墙的未正则化点场崩塌输入。
6. trureturing，同一固定提交，[Recursive Relational Observation Future Response Sufficiency](https://github.com/the-omega-institute/trureturing/blob/2d7d995ea59799e2e68c0e6d6b13da9ed5eebf89/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md)，§§51–55。
7. trureturing，同一固定提交，[FiniteWordReachability Blueprint](https://github.com/the-omega-institute/trureturing/blob/2d7d995ea59799e2e68c0e6d6b13da9ed5eebf89/Blueprint/D5/S3/Observer/LinearMemory/FiniteWordReachability.md)；相应 Lean 模块为 `D5/S3/Observer/LinearMemory/FiniteWordReachability`。
8. trureturing，同一固定提交，[NativeJointFutureMemoryLowerBound.lean](https://github.com/the-omega-institute/trureturing/blob/2d7d995ea59799e2e68c0e6d6b13da9ed5eebf89/D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureMemoryLowerBound.lean)。
9. M. Bastug, M. Petreczky, R. Wisniewski, J. Leth, *Model Reduction of Linear Switched Systems by Restricting Discrete Dynamics*, [arXiv:1409.1444v2](https://arxiv.org/abs/1409.1444v2), 2014。
10. M. Fliess, *Sur divers produits de séries formelles*, Bull. Soc. Math. France 102 (1974), 181–191, [原文](https://www.numdam.org/item/10.24033/bsmf.1777.pdf)。
11. P. Deligne and J. S. Milne, *Tannakian Categories*, [2022 修订版](https://jmilne.org/math/xnotes/tc2022.pdf)。
12. P. Selinger, *Dagger Compact Closed Categories and Completely Positive Maps*, ENTCS 170 (2007), 139–163, [doi](https://doi.org/10.1016/j.entcs.2006.12.018)。
13. Y. Nakayama, Y. Takeuchi, S. Akibue, *Uniqueness of imaginarity-assisted exact transformation from real orthogonal operations to arbitrary unitary operations*, [arXiv:2603.11812v2](https://arxiv.org/abs/2603.11812v2), 定理 1。
14. M. A. Nielsen and I. L. Chuang, *Programmable quantum gate arrays*, [arXiv:quant-ph/9703032](https://arxiv.org/abs/quant-ph/9703032), *Phys. Rev. Lett.* 79 (1997), 321。
15. The Stacks Project，[Tag 00U3](https://stacks.math.columbia.edu/tag/00U3)，有限 étale 代数。
16. J. C. Baez and B. Fong, *A Compositional Framework for Passive Linear Networks*, [arXiv:1504.05625](https://arxiv.org/abs/1504.05625), *Theory Appl. Categ.* 33 (2018), 1158–1222。
17. D. Speyer and B. Sturmfels, *The Tropical Grassmannian*, [arXiv:math/0304218](https://arxiv.org/abs/math/0304218), *Adv. Geom.* 4 (2004), 389–411。
18. P. Deligne, *Équations différentielles à points singuliers réguliers*, LNM 163, [IAS 页面与勘误](https://publications.ias.edu/node/355), 1970。
19. I. Mirković and K. Vilonen, *Geometric Langlands duality and representations of algebraic groups over commutative rings*, [arXiv:math/0401222v5](https://arxiv.org/abs/math/0401222v5)。
20. D. Gaitsgory and S. Raskin, *Proof of the geometric Langlands conjecture I: construction of the functor*, [arXiv:2405.03599](https://arxiv.org/abs/2405.03599)，§6.1。
21. D. Gaitsgory and S. Raskin, *Proof of the geometric Langlands conjecture V: the multiplicity one theorem*, [arXiv:2409.09856v3](https://arxiv.org/abs/2409.09856v3)。
22. G. Teschl, *Mathematical Methods in Quantum Mechanics*, [作者公开书稿](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf)。

## 符号与量词核对

| 符号或断言 | 适用范围 |
|---|---|
| $N,K_A$ | 固定有限维线性来源、既有全部输出分支和新增末端读口；不暗含新控制。 |
| $A,B$ | 异源二拷贝中 $A$、$B$ 是两个虚部；控制矩阵写作 $A_1,A_2,A_3$。 |
| $A^{\odot2}$ 与 $A^2$ | 前者为对称二次张量，后者为矩阵乘法。 |
| 完整实联合统计 | 足够多设置的概率律数据，不等于一次实验样本。 |
| $T_{\mathrm{flat}}$ | 使推出主丛存在某个平坦联络的普遍商，不保证指定几何连接平坦。 |
| $\mathbf1\oplus14\oplus5\oplus35$ | 表示论的等变分解，不表示四份独立物理资源。 |
| 全局水平参考 | 要求单值不变的张量；基点制备的参考不必满足此条件。 |
| 无分歧/带分歧 | 外部几何朗兰兹输入限于无分歧范围；四穿孔构造只建立带奇点局部系统及其分歧性质。 |
| Zariski 稠密 | 只说明代数闭包意义下的生成，不是范数逼近、样本成本或物理可执行性。 |
| $g_c$ | 只属于定义 11.1 固定的密度、协方差、源点和 Green 归一化。 |

## 追加锚（本行以下为增补区）

# 递归关系观察：正交对的边缘保持与过程恢复

## 1. 完整原来源与产品准备前提

**定义 1.1（原排除球与关联）。** 沿用 [QuantumIX116.1、116.10][QIX] 的完整原域：$V$ 是非零有限维实空间，$C\subset V$ 是闭、尖、生成凸锥，线性泛函 $u$ 在 $C\setminus\{0\}$ 上严格正。保留整个紧基、全部纯点及全部原效应

$$
K=C\cap\{u=1\},\qquad
\mathcal P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*}.
$$

对每个 $p\in\mathcal P$，令

$$
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\}.
$$

以下原来源应用明确假设 $\mathsf Q_1$：每个完整 $D_p$ 都仿射同构于闭三球，且其中存在一条直径，其两端被同一张原全域效应读成一、零。效应和端点可以依赖 $p$；量词覆盖全部原纯点及每个完整球。记 $c_p$ 为球的唯一对称中心，并置

$$
\begin{aligned}
\mathcal I&=\{(p,q)\in\mathcal P^2:q\in\partial_{\rm rel}D_p\},\\
a_p(q)&=2c_p-q,\\
\sigma(p,q)&=(q,p),\qquad
\tau(p,q)=(p,a_p(q)),\qquad
\mathcal R_{\mathcal I}=\sigma\circ\tau.
\end{aligned}
$$

这些是 [IX116.9][QIX] 的同一原关联和原对合。这里不以裸 EB3 代替 $\mathsf Q_1$；[IX118.8、118.13][QIX] 关于忠实球标签、关联投影开放性与稳定零见证的等价条件，是该完整原域的其他条件静态入口。本卷的来源应用固定使用 $\mathsf Q_1$。

**定义 1.2（同原表示与指定消费者）。** 直接使用 [IX116.17—116.18][QIX] 所给的同锥、同单位实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\longrightarrow V,\qquad
\Phi(\operatorname{Herm}_+(\mathbb C^3))=C,\qquad
u\Phi=\operatorname{Tr}.
$$

它同时识别整个 $K$ 与全部三阶密度矩阵、整个 $\mathcal P$ 与全部复秩一投影，以及整个 $\mathcal E$ 与全部 $0\preceq M\preceq I$，评价为 $f_M(\Phi\rho)=\operatorname{Tr}(M\rho)$；全部有限原效应分解对应全部有限数学 POVM。对任意原关联 $(p,q)\in\mathcal I$，置

$$
P=\Phi^{-1}(p),\qquad Q=\Phi^{-1}(q),\qquad R=I-P-Q.
$$

于是 $P,Q,R$ 是两两正交的秩一投影，且

$$
c_p=\Phi\left(\frac{I-P}{2}\right),\qquad
a_p(q)=\Phi(R).
$$

反过来，每个有序复正交秩一对 $(P,Q)$ 都来自这样的原关联。消费者 $\tau$ 保留原 $p$，请求特定的 $a_p(q)$，故在下述双份产品接口上，它请求的输出恰为 $P\otimes R$。

**假设 1.3（实际供给的两种接口）。** 另给相互识别的寄存器 $H_A,H_B,H_C\cong H=\mathbb C^3$ 及其通常复张量积。考虑在同一原关联上索引的两种产品准备合同

$$
\mathrm E_2(p,q)=P_A\otimes Q_B,\qquad
\mathrm E_3(p,q)=P_A\otimes Q_B\otimes R_C,\qquad
\operatorname{Tr}_C\mathrm E_3=\mathrm E_2.
$$

选用哪种合同，就须实际供给该合同的未知态样本与产品准备。静态映射 $\Phi$ 本身不准备这些样本，不供给纠缠、控制、仪器或当前取得权限。

双份过程是一张固定的复线性完全正保迹映射

$$
\mathcal N:\mathcal L(H_A\otimes H_B)\longrightarrow
                 \mathcal L(H_A\otimes H_B).
$$

它可联合处理两个寄存器；不预设局域性、协变性或幺正性。只允许与准备无关的固定辅助态、随机性及固定自适应仪器，它们均可吸收到 $\mathcal N$。不额外传入旗标的经典描述、依赖准备的框架或程序、第三份样本或依赖准备的酉算子 oracle。若有仪器记录，成功、失败各分支全部计入忽略记录后的通道，不选择成功分支再归一。精确保留要求是无条件的

$$
\operatorname{Tr}_B\mathcal N(P\otimes Q)=P
\quad\text{对所有复秩一投影 }P,Q\text{ 满足 }PQ=0.
\tag{1.1}
$$

定理 2.1 只需要这一矩阵过程前提，不依赖原排除球的重构证明。

## 2. 全复正交对承诺的刚性

**定理 2.1（受限乘积输入迫使全局 Kraus 因子化）。** 设 $H=\mathbb C^3$，固定 CPTP 通道 $\mathcal N:\mathcal L(H\otimes H)\to\mathcal L(H\otimes H)$ 满足 (1.1)。则任取其有限 Kraus 表示

$$
\mathcal N(X)=\sum_a K_aXK_a^\dagger,
$$

都有 $K_a=I\otimes A_a$，其中 $\sum_aA_a^\dagger A_a=I$。因此存在 qutrit CPTP 通道 $\Lambda$，使

$$
\mathcal N=\operatorname{id}_A\otimes\Lambda_B
\quad\text{在整个复矩阵代数上成立},\qquad
\Lambda(T)=\sum_aA_aTA_a^\dagger.
\tag{2.1}
$$

结论包括承诺族以外的矩阵与纠缠输入；假设只涉及全部有序复正交秩一投影对。

证明。先复用有限维 Kraus 表示及正性逐项消失的标准支撑论证；不扰动问题的通常框架参见 [Koashi—Imoto，§II 式 (2)—(3)][KI]。对单位向量 $v\perp w$，由 (1.1) 得

$$
0=\operatorname{Tr}\!\left[((I-|v\rangle\langle v|)\otimes I)
       \mathcal N(|v\otimes w\rangle\langle v\otimes w|)\right]
 =\sum_a\left\|((I-|v\rangle\langle v|)\otimes I)K_a(v\otimes w)\right\|^2.
$$

每项非负，故对每个 $a$ 都有

$$
K_a(v\otimes w)\in\mathbb Cv\otimes H.
\tag{2.2}
$$

缩放使 (2.2) 对任意非零正交 $v,w$ 成立。固定其中一个 $K=K_a$；下面直接从这个受限支撑条件推出其全矩阵结构。

任取正交归一基 $e_1,e_2,e_3$。当 $i\ne j$ 时，写

$$
K(e_i\otimes e_j)=e_i\otimes a_{ij}.
$$

固定 $j$，让 $i,k$ 为其余两个指标。将 (2.2) 用于 $(e_i+e_k)\otimes e_j$，比较第一寄存器的 $e_i,e_k$ 分量，得 $a_{ij}=a_{kj}$，记共同值为 $a_j$。另记 $D_i=K(e_i\otimes e_i)$。

对不同 $i,j$ 及任意 $z\in\mathbb C$，取

$$
v=e_i+ze_j,\qquad w=-\bar z e_i+e_j.
$$

按第一变量共轭线性的内积，$v^\dagger w=-\bar z+\bar z=0$。所以

$$
-\bar zD_i+e_i\otimes a_j-|z|^2e_j\otimes a_i+zD_j
       \in\mathbb C(e_i+ze_j)\otimes H.
\tag{2.3}
$$

让 $k$ 是第三个指标，记 $(D_i)_k=(\langle e_k|\otimes I)D_i$。投影 (2.3) 的第一寄存器到 $e_k$，得

$$
-\bar z(D_i)_k+z(D_j)_k=0.
$$

分别取 $z=1$ 与 $z=\mathrm i$，即得 $(D_i)_k=(D_j)_k=0$。对每个 $i$ 及每个 $k\ne i$，均可选剩下的 $j$，故

$$
D_i=e_i\otimes b_i
$$

对某个 $b_i\in H$ 成立。这一步使用不同复射线间的相对相位，并未把全局相位当作可观察输入。

代回 (2.3)，其 $e_i$ 分量为 $a_j-\bar z b_i$，$e_j$ 分量为 $zb_j-|z|^2a_i$。后者必须是前者的 $z$ 倍，因此

$$
|z|^2(b_i-a_i)+z(b_j-a_j)=0.
$$

取 $z=1,-1$，得到 $b_i=a_i$、$b_j=a_j$。定义复线性算子 $A e_j=a_j$，则九个基张量上均有

$$
K(e_i\otimes e_j)=e_i\otimes Ae_j,
$$

故 $K=I\otimes A$ 在整个向量空间上成立。对每个 Kraus 算子分别应用该论证，再由保迹性

$$
I\otimes I=\sum_aK_a^\dagger K_a
          =I\otimes\sum_aA_a^\dagger A_a
$$

得到 (2.1)。证明中的基只是坐标选择，输入承诺没有限制到某个固定基。

[Koashi—Imoto][KI] 的固定辅助态不扰动问题、[Mayer—Knill，定理 1][MK] 的整纯态保持条件，以及仓内 [ProbeComponentRigidity][PCR] 的全部密度输入概率保持条件，均不直接给出 (1.1) 到 (2.1) 的这一步：此处可访问的第二输入随第一输入变化，最初只保持第一边缘。[产品密度态保持分类，定理 1][PROD] 和 [纯产品态保持分类，定理 3.2][PURE] 也分别要求全部产品密度输入、全部纯产品输入上的保持。上面的复相位论证承担了受限正交承诺到全代数因子化的推导，未将这些更强前提预放入假设。证毕。

## 3. 平均保真度与 universal-NOT 的定量应用

**推论 3.1（指定第三射线的最坏目标重叠）。** 记 $\mathfrak F$ 为全部有序复正交秩一对 $(P,Q)$，$R=I-P-Q$。在满足 (1.1) 的所有联合 CPTP 通道中，定义

$$
s_{\mathcal N}(P,Q)
 =\operatorname{Tr}\!\left[(P\otimes R)\mathcal N(P\otimes Q)\right].
\tag{3.1}
$$

将定理 2.1 接上复 Haar 平均保真度和已知 universal-NOT 通道，得到

$$
\max_{\mathcal N\text{ 满足 }(1.1)}\;
\inf_{(P,Q)\in\mathfrak F}s_{\mathcal N}(P,Q)=\frac38.
\tag{3.2}
$$

最大值由一张固定通道在每个承诺输入上同时达到。分数 (3.1) 是目标投影的重叠；若另给相应验证测量，它是该测试的接受概率，不是带成功标志的精确输出成功概率。特别地，不存在对全部 $\mathfrak F$ 精确输出 $P\otimes R$ 的固定 CPTP 通道，也不存在从 $P\otimes Q$ 精确输出 $P\otimes Q\otimes R$ 的固定 CPTP 通道。

证明。定理 2.1 将 (3.1) 化为 $\operatorname{Tr}(R\Lambda(Q))$。在同一个 Haar 分布的有序正交归一标架中取 $(P,Q,R)$。给定 $Q$，$R$ 在 $Q^\perp$ 内均匀，故

$$
\mathbb E[R\mid Q]=\frac{I-Q}{2},\qquad
\inf_{\mathfrak F}s_{\mathcal N}
\le\mathbb E\,s_{\mathcal N}
=\frac{1-F_{\rm av}(\Lambda)}2,
\quad
F_{\rm av}(\Lambda)=\int\operatorname{Tr}(Q\Lambda(Q))\,dQ.
\tag{3.3}
$$

这里 $dQ$ 是归一化的复 Haar 测度，两个投影始终来自同一个标架。写 $Q=|q\rangle\langle q|$、$\|q\|=1$，复用标准二阶矩 $\int Q\otimes Q\,dQ=(I+S)/12$，其中 $S$ 是两份 $H$ 的交换，得到

$$
\begin{aligned}
F_{\rm av}(\Lambda)
&=\sum_a\int|\langle q,A_aq\rangle|^2\,dq\\
&=\frac{\sum_a\operatorname{Tr}(A_a^\dagger A_a)
             +\sum_a|\operatorname{Tr}A_a|^2}{12}
 =\frac{3+\sum_a|\operatorname{Tr}A_a|^2}{12}
 \ge\frac14.
\end{aligned}
\tag{3.4}
$$

这正是 [Nielsen，式 (3)][NIELSEN] 引用的平均保真度关系 $F_{\rm av}=(3F_e+1)/4$，其中 $F_e=\sum_a|\operatorname{Tr}A_a|^2/9\ge0$；其参考系统保持不动，不能将它误认为随准备变化的输入 $Q$。由 (3.3)—(3.4) 得所有允许通道的上界 $3/8$，没有假定协变性、幺正性或某种特殊 Kraus 族。

取等直接复用 [Rungta 等，§II.D 式 (2.29)—(2.32)、(2.37)][NOT] 的无转置 universal-NOT 端点，再用通常的 Weyl 共轭恒等式写出它的 Kraus 表示。在任意固定坐标基 $e_j$（$j\in\mathbb Z/3\mathbb Z$）中，令

$$
\omega=e^{2\pi\mathrm i/3},\qquad Xe_j=e_{j+1},\qquad
Ze_j=\omega^je_j,\qquad W_{ab}=X^aZ^b.
$$

八个非恒等 Weyl 算子 $W_{ab}/\sqrt8$ 的伴随乘积之和为 $I$；对任意矩阵 $T$，先用 $Z$ 去掉非对角项再用 $X$ 循环移位，给出已知恒等式

$$
\sum_{a,b=0}^2W_{ab}TW_{ab}^\dagger=3\operatorname{Tr}(T)I.
$$

因而这些 Kraus 算子给出 CPTP 通道

$$
\Lambda_*(T)=\frac{3\operatorname{Tr}(T)I-T}{8},\qquad
\mathcal N_*=\operatorname{id}\otimes\Lambda_*.
\tag{3.5}
$$

对每个承诺对，$RQ=0$，所以

$$
\operatorname{Tr}(R\Lambda_*(Q))=\frac38.
$$

该坐标实现不限制未知输入的基。它是已知通道在当前目标分数上的应用；理想归一反演 $(I-Q)/2$ 是混合的正交补，不选择依赖于 $P,Q$ 的特定射线 $R$。[Werner—Holevo，式 (6)—(7)][WH] 的 $(\operatorname{Tr}(T)I-T^{\mathsf T})/2$ 含固定基转置，与 (3.5) 不同。事实上，$\Lambda_*(Q)$ 在 $Q$ 方向的本征值为 $1/4$、在 $Q^\perp$ 上为 $3/8$，是满秩混态；其重叠 $3/8$ 本身没有提供逐次精确制得 $R$ 的事件或成功标志。

若恒有 $\mathcal N(P\otimes Q)=P\otimes R$，则 (3.1) 恒为一，与 (3.2) 矛盾。若有 $\Gamma:AB\to ABC$ 恒输出完整产品 $P\otimes Q\otimes R$，丢弃其中间输出并将末输出识别为第二寄存器，便得到前一种通道，同样矛盾。所有失败分支仍包含在 CPTP 总映射中；这里不对归一化后选择、近似第一边缘保持或其他编码作推断。证毕。

## 4. 原关联消费者与表示边界

**应用 4.1（同一原旗标的两份与三份合同）。** 在定义 1.1—1.2 的完整原域及假设 1.3 的实际产品接口下，双份合同 $\mathrm E_2$ 的交换消费者 $\sigma$ 由固定寄存器交换实现，但其 $\tau$ 消费者不能由一张固定 CPTP 通道精确实现；在无条件保留第一边缘的合同下，它的最佳保证目标重叠恰为 $3/8$。若另已供给 $\mathrm E_3$ 和寄存器交换控制，则已有的交换操作实现全部有限关联字。后一充分合同使用已经存在的第三样本。

证明。令 $S_{AB}$ 为交换前两个寄存器的固定酉算子，$\operatorname{Ad}_S(Y)=SYS^\dagger$。熟知的张量因子交换恒等式直接给

$$
\operatorname{Ad}_{S_{AB}}\mathrm E_2=\mathrm E_2\circ\sigma.
$$

另一方面，定义 1.2 将原消费者的目标准确识别为

$$
\mathrm E_2(\tau(p,q))=P\otimes R.
$$

原关联覆盖全部 $\mathfrak F$，故定理 2.1 和推论 3.1 适用。这里排除的是该源索引、该产品编码、该无侧输入过程类中的精确消费者，不是原关联对合的集合存在性。

在更强的三份准备合同上，固定交换的已有恒等式为

$$
\operatorname{Ad}_{S_{AB}}\mathrm E_3=\mathrm E_3\circ\sigma,
\qquad
\operatorname{Ad}_{S_{BC}}\mathrm E_3=\mathrm E_3\circ\tau.
\tag{4.1}
$$

每次交换后第三寄存器仍是前两个投影的正交补。故 (4.1) 按复合逐次用于每个有限字，包括 $\mathcal R_{\mathcal I}=\sigma\tau$ 的迭代；允许的经典控制可以选择下一次交换。此处只复用因子置换及 [IX116.9、116.17][QIX] 的原关联作用，不另给新的 $S_3$ 内容，也没有从双份输入产生第三样本。

同一个静态旗标和完整经典矩阵描述都确定 $R=I-P-Q$，而丢弃第三寄存器也确实把 $\mathrm E_3$ 降为 $\mathrm E_2$。反方向要求的是实际准备缺失的态并保留指定第一态；该要求已被上述双份过程界排除。若另准许旗标描述、依赖准备的程序或更强准备菜单，就改变了假设 1.3，不能继续套用这一排除。两种产品编码的比较不证明跨编码、程序、仪器、控制或资源模型的通用最少样本数；三份准备、控制及同时持有的全部资源仍须计费，不从静态重构取得总资源优势。

此处消费者严格是 Quantum116 的 $\tau$，不是 Native/AA 的某个待执行原动作。要将关系解释接回后者，仍须另给实际 $\xi/\beta$ 准备、根、父节点、共享带和来源身份与产品合同的对应，不能把 Fibonacci 的 $\alpha,\beta$ 按名称识别为 $\sigma,\tau$。原任务要求一个与未来无关的有限安装覆盖全部普通有限自适应 $\mathrm{Rho}/\mathrm{Left}(v)/\mathrm{Right}(v)$ 调度、任意非空有限原操作数、独立收到的非递减守卫、finish、模式 $10/00/11$ 及真实接受与拒绝的区别；这些量词均未被 $\mathcal I$ 代替。

同样，全部达到的 post-EnableCapture、prehalt 原始切口，包括 busy、ACK、parser、partial-support 内部及紧接 ENTER 的空帧，和每个有限嵌套或重复请求森林，仍要求在所欠动作之前通过自身合法流量立即取得，包括真实 buffered IN；四份独立产生和取得的完整 body、分离的 INPUT/STACK、完整记录及当前权限均须另行供给。所选完整收到的 body 还须实际驱动向同一待执行原消费者的一次返回，保持 Park、Handback、Stop、INITIAL、ACK、token 规则及吸收 halt。原部分对象、backing、连接、来源、同次运行的全部费用向量与同时峰值都保留。这里的矩阵合同没有给出这些对应、取得、返回或费用比较，因此只形成指定量子关联消费者的条件限制，不结算更广的互恢复目标。证毕。

**假设 4.2（三元读数的另一接口）。** [QuantumIX117.1—117.2][QIX] 使用同一个 $\operatorname{Herm}_d(\mathbb C)$ 中三套有标签的完整正交秩一框架 $E=(E_i),F=(F_j),G=(G_k)$，并要求

$$
q(E_i,F_1)>0,\quad q(E_i,G_1)>0,\quad
q(F_j,G_1)>0,\quad q(F_1,G_k)>0,
\qquad q(U,V)=\operatorname{Tr}(UV).
$$

其锚片三元统计在这些前提下重构该有限框架族到共同酉共轭，并有相应实 Jordan 闭包判据。三套完整框架不是一个关联旗标的三个正交样本；将 $P,Q,R$ 重复或重排成三套框架不能满足上述正锚条件。

[IX117.5][QIX] 另已给出产品准备 $U\otimes V\otimes W$、控制系统、相干受控循环、校准相位参考及 Born 读回这些前提下取得 $\operatorname{Re}\operatorname{Tr}(UVW)$ 的已知合同；定向虚部还依赖循环与相位约定。这些准备和控制都是额外给定的。对本卷的正交三态，$\operatorname{Tr}(PQR)=0$；(4.1) 不产生其非零锚数据，已有三元读回也不从 $\mathrm E_2$ 取得缺失的 $R$。同理，IX118 的条件静态重构不增加本卷的产品准备、CP 仪器、当前权限或时间合同；实际复合、全旁观者正性、同族仪器及记录、逐输入预算、条件归一、原钟与连续动态仍保留 [VIII113.11][QVIII] 和 [IX116.23、118.9][QIX] 的独立前提。

[QIX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "QuantumIX116.1、116.9—116.10、116.17—116.18、116.22—116.23；117.1—117.2、117.5；118.8、118.13、118.9。"
[QVIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "QuantumVIII113.11：同源实际复合、操作、仪器、记录与时间合同。"
[KI]: https://arxiv.org/pdf/quant-ph/0101144v2 "Koashi and Imoto, Operations that do not disturb partially known quantum states；§II (2)—(3)，§VII Theorem 5 (112)—(113)。"
[MK]: https://arxiv.org/pdf/1805.04491v1 "Mayer and Knill, Quantum Process Fidelity Bounds from Sets of Input States；Theorem 1。"
[PCR]: ../../../D5/S3/Quantum/Reduction/ProbeComponentRigidity.lean "probability_preserving_kraus_commute、kraus_scalar_on_component、connected_probability_preserving_identity：全部密度输入上的概率保持前提。"
[PROD]: https://arxiv.org/pdf/1409.5994 "When quantum channel preserves product states；Theorem 1。"
[PURE]: https://arxiv.org/pdf/1210.2155 "Linear maps preserving separability of pure states；Theorem 3.2。"
[NIELSEN]: https://arxiv.org/pdf/quant-ph/0205035v2 "Nielsen, A simple formula for the average gate fidelity of a quantum dynamical operation；(1)—(3)，归一化 Haar 平均与平均／纠缠保真度关系。"
[NOT]: https://arxiv.org/pdf/quant-ph/0102040v2 "Rungta et al., Universal state inversion and concurrence in arbitrary dimensions；§II.D (2.29)—(2.32)、(2.37)，§III (3.1)—(3.2)。"
[WH]: https://arxiv.org/pdf/quant-ph/0203003v1 "Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels；§II (6)—(7)，含转置的通道。"

## 追加锚（本行以下为增补区）

## 5. 同一双份消费者的受控扰动合同

**定义 5.1（逐输入迹距离与联合目标）。** 保留定义 1.1—1.2 的全部原域与 $\mathsf Q_1$：原闭尖生成锥、严格正单位、整个紧基、全部纯点、全部原效应，以及每个完整排除球上的量词均不改变。同锥、同单位的 $\Phi$ 及其纯点、效应和关联对应仍是 [IX116.17—116.18][QIX] 的对应，不以裸 EB3 或忠实标签前提代替它。矩阵部分固定 $H=\mathbb C^3$、假设 1.3 的已识别寄存器及

$$
\mathfrak F=\{(P,Q):P,Q\text{ 为复秩一投影},\ PQ=0\},
\qquad R=I-P-Q.
$$

输入仍是实际供给的一个未知产品样本 $P_A\otimes Q_B=\mathrm E_2(p,q)$，指定目标仍是原 Quantum116 消费者的 $\mathrm E_2(\tau(p,q))=P_A\otimes R_B$。竞争过程仍是一张与 $(P,Q)$ 无关、定义于整个矩阵代数的固定复线性 CPTP 通道 $\mathcal N:AB\to AB$；只吸收与准备无关的辅助态、随机性和固定自适应仪器。不输入依赖准备的描述、框架、程序或 oracle，不给第三样本。仪器全部分支计入无条件通道，不作成功分支选择或再归一。

用下列有误差合同替代 (1.1) 的精确保留要求：

$$
\begin{aligned}
\rho_A^{\mathcal N}(P,Q)&=\operatorname{Tr}_B\mathcal N(P\otimes Q),\\
d_{\mathcal N}(P,Q)&=\frac12\|\rho_A^{\mathcal N}(P,Q)-P\|_1,\\
D(\mathcal N)&=\sup_{(P,Q)\in\mathfrak F}d_{\mathcal N}(P,Q),\\
s_{\mathcal N}(P,Q)&=\operatorname{Tr}[(P\otimes R)\mathcal N(P\otimes Q)],\\
F(\varepsilon)&=\max_{\mathcal N\ {\rm CPTP},\ D(\mathcal N)\le\varepsilon}
                 \inf_{(P,Q)\in\mathfrak F}s_{\mathcal N}(P,Q),
\qquad 0\le\varepsilon\le1.
\end{aligned}
\tag{5.1}
$$

迹距离的效应变分公式给出

$$
d_{\mathcal N}(P,Q)=\max_{0\preceq M\preceq I}
 \left|\operatorname{Tr}[M(\rho_A^{\mathcal N}(P,Q)-P)]\right|.
\tag{5.2}
$$

所以预算约束覆盖每个承诺输入和全部第一寄存器效应。$s_{\mathcal N}$ 是同一个联合目标投影的重叠；若另供给该验证测量，它是测试接受概率，不是带标志的精确制备成功概率。这里没有以第一寄存器平均保真度或某个单输出分数替代联合目标。[Banaszek，式 (4)—(5)][BALANCE] 的单输入操作／经典估计均值，以及 [Fiurášek—Iblisdir—Massar—Cerf，式 (4)、(15)][ORTHOCLONE] 的正交 qubit 输入单克隆均值，分别使用不同的输入、消费者和分数。

以下横线表示同一个 Haar 有序正交标架 $(P,Q,R)$ 的归一化平均。另置

$$
\ell_{\mathcal N}(P,Q)=1-\operatorname{Tr}[(P\otimes I)\mathcal N(P\otimes Q)],
\qquad
G(\varepsilon)=\max_{\mathcal N\ {\rm CPTP},\ \bar\ell_{\mathcal N}\le\varepsilon}
                    \bar s_{\mathcal N}.
\tag{5.3}
$$

$\ell$ 是第一输出离开 $P$ 的概率，尚未将它等同于一般通道的迹距离。

**定理 5.2（Haar 约束与最坏保证的双向等价）。** 对全部 $0\le\varepsilon\le1$，

$$
F(\varepsilon)=G(\varepsilon).
\tag{5.4}
$$

两个最大值都存在，而且可由满足

$$
\mathcal N( (U\otimes U)Y(U\otimes U)^\dagger)
 =(U\otimes U)\mathcal N(Y)(U\otimes U)^\dagger
\quad(U\in U(3))
\tag{5.5}
$$

的通道达到。对这样的通道，$s$、$\ell$ 和 $d$ 在 $\mathfrak F$ 上恒定，并有 $d=\ell$。

证明。对任意通道，(5.2) 中取效应 $P$ 得 $0\le\ell_{\mathcal N}\le d_{\mathcal N}$。于是 $D(\mathcal N)\le\varepsilon$ 蕴含 $\bar\ell_{\mathcal N}\le\varepsilon$，同时 $\inf s_{\mathcal N}\le\bar s_{\mathcal N}$；故 $F\le G$。

反向任取 $G$ 的可行通道，记 $V_U=U\otimes U$，并取固定的群平均

$$
\widetilde{\mathcal N}(Y)=\int_{U(3)}
 V_U^\dagger\mathcal N(V_UYV_U^\dagger)V_U\,dU.
\tag{5.6}
$$

这是固定 CPTP 通道，平均分布不依赖未知输入；有限维下亦可用有限凸组合表示这个平均通道。Haar 不变性给出 (5.5)。由于 $U(3)$ 在全部有序复正交射线对上传递，直接代入积分可得，对每个 $(P,Q)$，

$$
s_{\widetilde{\mathcal N}}(P,Q)=\bar s_{\mathcal N},
\qquad
\ell_{\widetilde{\mathcal N}}(P,Q)=\bar\ell_{\mathcal N}.
\tag{5.7}
$$

取参考标架 $P=|0\rangle\langle0|$、$Q=|1\rangle\langle1|$、$R=|2\rangle\langle2|$。对三个射线分别加任意相位的对角酉算子固定输入密度矩阵。协变性使第一输出边缘与所有这些酉算子对易，故

$$
\rho_A^{\widetilde{\mathcal N}}=aP+bQ+cR,
\qquad a,b,c\ge0,\quad a+b+c=1.
$$

因此 $d=(|a-1|+b+c)/2=b+c=\ell$。该等式经协变性覆盖全部 $\mathfrak F$，所以 $D(\widetilde{\mathcal N})=\bar\ell_{\mathcal N}\le\varepsilon$，且其最坏分数为 $\bar s_{\mathcal N}$。这证明 $G\le F$，没有预先把最坏迹距离任务改成平均任务。

在未归一化 Choi 坐标下，CPTP 集为 $J\succeq0$、$\operatorname{Tr}_{\rm out}J=I_{\rm in}$ 的紧集；$\mathfrak F$ 亦紧。迹距离和分数连续，其关于紧参数集的最大、最小仍连续。两个可行集闭且非空，故最大值存在。群平均保持 $\bar s$ 与 $\bar\ell$，上述反向构造也给出协变最优者。Choi 的正性、部分迹约束及线性平均分数是标准工具，参见 [Fiurášek，§II 式 (3)—(8)、§III 式 (16)—(19)][CPMAP]；这里的双向等价还使用了本承诺族的传递性和稳定子计算。证毕。

**定理 5.3（局部最优系数及全误差上界）。** 对定义 5.1 的同一合同，

$$
F(0)=\frac38,
\qquad
F(\varepsilon)=\frac38+\sqrt{\frac{17}{112}}\sqrt\varepsilon+O(\varepsilon)
\quad(\varepsilon\downarrow0).
\tag{5.8}
$$

特别地，

$$
\lim_{\varepsilon\downarrow0}
 \frac{F(\varepsilon)-3/8}{\sqrt\varepsilon}
 =\sqrt{\frac{17}{112}}=\frac{\sqrt{119}}{28}.
\tag{5.9}
$$

在整个 $0\le\varepsilon\le1$ 上还成立

$$
F(\varepsilon)\le
\min\left\{1,
\frac{\bigl(\sqrt{17\varepsilon/42}
       +\sqrt{3/2+17\varepsilon/42}\bigr)^2}{4}
+\frac{20}{7}\varepsilon\right\}.
\tag{5.10}
$$

式 (5.10) 是非锐的有限误差上界。定理 8.2—9.2 的固定八 Kraus 通道在每个承诺输入上达到 (5.8) 的同一首项系数，其自身展开为

$$
s=\frac38+\frac{\sqrt{119}}{28}\sqrt\varepsilon
             -\frac{1157}{2856}\varepsilon+O(\varepsilon^{3/2}).
\tag{5.11}
$$

式 (5.11) 的二阶系数只属于这族通道，不断言为 $F$ 的最优系数。

证明。$D=0$ 与 (1.1) 完全等价，故定理 2.1 给出整个代数上的 $\mathcal N=\operatorname{id}\otimes\Lambda$，推论 3.1 给出 $F(0)=3/8$，端点直接复用 (3.5) 及 [Rungta 等，§II.D][NOT]。有误差情形的全扇区上界由定理 6.2、7.1—7.2 推出；同系数下界、(5.11) 及误差参数的局部可逆性由定理 8.2、9.1—9.2 推出。其上下估计夹出 (5.8)—(5.9)。以下给出这些推导。证毕。

## 6. 完整协变分解与伴随块的泄漏形式

**定义 6.1（Choi 坐标与四个嵌入）。** 固定一个与输入无关的基。输出寄存器记为 $A,B$，Choi 的共轭输入寄存器记为 $C,D$；横杠在本节以后也用于矩阵的逐项共轭，积分上的横线仍表示 (5.3) 的平均。向量化约定为

$$
|K\rangle\!\rangle=\sum_{a,b,c,d}K_{ab,cd}|a,b,c,d\rangle,
\qquad
J_{\mathcal N}=\sum_\nu|K_\nu\rangle\!\rangle\langle\!\langle K_\nu|.
\tag{6.1}
$$

于是 $\operatorname{Tr}_{AB}J_{\mathcal N}=I_{CD}$，且对任意输入 $X$、输出效应 $Y$，

$$
\operatorname{Tr}[Y\mathcal N(X)]
 =\operatorname{Tr}[J_{\mathcal N}(Y\otimes X^{\mathsf T})].
\tag{6.2}
$$

这是 [CPMAP，式 (3)—(8)、(16)—(19)][CPMAP] 的通常正 Choi／Kraus 表示，采用输出在前的次序，不另作归一化。

令 $S$ 为 $H\otimes H$ 上的交换，取全部无迹复矩阵空间的一组 Hilbert—Schmidt 正交归一基 $T_1,\ldots,T_8$。这组基不必由 Hermitian 矩阵组成。记

$$
\begin{aligned}
E_0(T)&=I\otimes T,&E_1(T)&=T\otimes I,\\
E_2(T)&=(I\otimes T)S,&E_3(T)&=(T\otimes I)S.
\end{aligned}
\tag{6.3}
$$

它们都把 $T\mapsto UTU^\dagger$ 交织为 $K\mapsto V_UKV_U^\dagger$。正交归一性的完整性恒等式为

$$
\sum_{a=1}^8(T_a)_{ij}\overline{(T_a)_{kl}}
 =\delta_{ik}\delta_{jl}-\frac13\delta_{ij}\delta_{kl},
\qquad
\sum_aT_a^\dagger T_a=\sum_aT_aT_a^\dagger=\frac83I.
\tag{6.4}
$$

**定理 6.2（全部复重数块及伴随块估计）。** 每个满足 (5.5) 的 CPTP 通道都有正 Choi 分解

$$
J=J_{\bf1}+J_{\bf8}+J_{\rm rest},
\qquad
J_{\rm rest}=\lambda_{10}\Pi_{10}
 +\lambda_{\overline{10}}\Pi_{\overline{10}}+\lambda_{27}\Pi_{27},
\quad \lambda_\mu\ge0,
\tag{6.5}
$$

其中等型分解完整地为

$$
\operatorname{End}(H\otimes H)
 \cong 2\cdot{\bf1}\ \oplus\ 4\cdot{\bf8}\ \oplus\ {\bf10}
             \ \oplus\ \overline{\bf10}\ \oplus\ {\bf27}.
\tag{6.6}
$$

$\Pi_\mu$ 是相应不可约子空间的正交投影。标量块允许 $I,S$ 间的任意复正重数矩阵；伴随块允许四个 (6.3) 间的任意复正重数矩阵。因此可以分别选 Kraus 族 $a_rI+b_rS$ 及

$$
K_{r,a}=x_rE_0(T_a)+y_rE_1(T_a)+z_rE_2(T_a)+w_rE_3(T_a),
\qquad x_r,y_r,z_r,w_r\in\mathbb C.
\tag{6.7}
$$

系数只受整个 $J$ 的保迹约束，不假定它们实数、对角或秩一。对参考输入 $|01\rangle$ 和目标 $|02\rangle$，设

$$
X=\sum_r|x_r|^2,\qquad v_r=(y_r,z_r,w_r)^{\mathsf T},\qquad
\mathsf Q=\begin{pmatrix}
2&1&0\\
1&8/3&-1/3\\
0&-1/3&5/3
\end{pmatrix}.
\tag{6.8}
$$

伴随块贡献的分数和泄漏恰为

$$
s_{\bf8}=X,\qquad
\delta_{\bf8}=\sum_r v_r^\dagger\mathsf Qv_r,
\tag{6.9}
$$

且总保迹性蕴含

$$
X-\frac38\le
 \operatorname{Re}\sum_r\overline{x_r}\left(\frac{y_r}{4}-\frac{3w_r}{4}\right)
 \le\sqrt{\frac{17}{42}X\delta_{\bf8}}.
\tag{6.10}
$$

证明。由向量化约定，(5.5) 等价于

$$
[J,V_U\otimes\bar V_U]=0\qquad(U\in U(3));
$$

这里 $V_U\otimes\bar V_U$ 在算子空间上的作用就是 $K\mapsto V_UKV_U^\dagger$。先作这个表示的完整分解。对 $SU(3)$，

$$
H\otimes H=\operatorname{Sym}^2H\oplus\bigwedge^2H
            ={\bf6}\oplus\overline{\bf3}.
$$

通常的张量对称化、收缩和 Young 分解给出

$$
\begin{aligned}
\operatorname{End}({\bf6})&={\bf1}\oplus{\bf8}\oplus{\bf27},\\
\operatorname{End}(\overline{\bf3})&={\bf1}\oplus{\bf8},\\
\operatorname{Hom}(\overline{\bf3},{\bf6})
 &={\bf6}\otimes{\bf3}=\operatorname{Sym}^3H\oplus{\bf8}
   ={\bf10}\oplus{\bf8},\\
\operatorname{Hom}({\bf6},\overline{\bf3})
 &=\overline{\bf10}\oplus{\bf8}.
\end{aligned}
\tag{6.11}
$$

具体地，${\bf6}\otimes\overline{\bf6}$ 的标量、一次无迹收缩和完全无迹部分的最高权分别是 $(0,0),(1,1),(2,2)$；$\operatorname{Sym}^2H\otimes H$ 的全对称部分与 Young 形 $(2,1)$ 的最高权分别是 $(3,0),(1,1)$。标准维数式 $\dim(a,b)=(a+1)(b+1)(a+b+2)/2$ 分别给出 $1,8,27,10,8$。故 (6.11) 的维数总和为 $2+32+10+10+27=81$，没有剩余扇区。对 $U(3)$，${\bf10},\overline{\bf10}$ 的记号带有使中心作用平凡的行列式扭转；其 $SU(3)$ 限制及互不等价性不变。

这是标准 Schur 分块的应用，Schur 与群平均方法参见 [Harrow，定理 5、命题 6][HAAR]，量子通道中的正 Choi 和 Schur 平均应用参见 [Fiurášek—Filip—Cerf，式 (5)—(10)][ASYM]。这里须保留本问题的全部重数。标量空间由 $I,S$ 张成，其 Gram 矩阵是 $\left(\begin{smallmatrix}9&3\\3&9\end{smallmatrix}\right)$。对无迹矩阵 $T,U$，(6.3) 的 Hilbert—Schmidt 内积满足

$$
\operatorname{Tr}[E_i(T)^\dagger E_j(U)]
 =\mathsf G_{ij}\operatorname{Tr}(T^\dagger U),
\qquad
\mathsf G=\begin{pmatrix}
3&0&1&1\\
0&3&1&1\\
1&1&3&0\\
1&1&0&3
\end{pmatrix}.
\tag{6.12}
$$

$\mathsf G$ 的本征值为 $5,3,3,1$。四个嵌入因而独立，恰好填满四份伴随空间；它们并非正交坐标。

令 $\mathcal B:\mathbb C^4\otimes\mathbb C^8\to\mathcal H_{\bf8}$ 将标准基送到 $|E_i(T_a)\rangle\!\rangle$。则 $\mathcal B^\dagger\mathcal B=\mathsf G\otimes I_8$，且 $\mathcal B$ 可逆。Schur 引理及正性给出

$$
J_{\bf8}=\mathcal B(\mathsf C\otimes I_8)\mathcal B^\dagger
 =\sum_{i,j=0}^3\mathsf C_{ij}
       \sum_{a=1}^8|E_i(T_a)\rangle\!\rangle\langle\!\langle E_j(T_a)|,
\qquad \mathsf C=\mathsf C^\dagger\succeq0.
\tag{6.13}
$$

这里正性是可逆合同变换下的正性，不能把 $\mathsf G$ 当成单位阵，也不能将 $\mathsf C$ 限为实矩阵。任意复正矩阵的分解 $\mathsf C=\sum_r c_rc_r^\dagger$ 给出 (6.7)。对标量块作同样的二维可逆合同变换。具体地，记 $B_0=I,B_1=S$，则

$$
J_{\bf1}=\sum_{i,j=0}^1\mathsf C^{(0)}_{ij}
 |B_i\rangle\!\rangle\langle\!\langle B_j|,
\qquad \mathsf C^{(0)}=(\mathsf C^{(0)})^\dagger\succeq0.
$$

所以任意复 Hermitian 正重数矩阵及全部 $I,S$ 相干都已保留。其余三种表示的重数为一，故为 (6.5)；互不等价扇区间没有 Choi 交叉项。反过来，这些正块的和只要满足 $\operatorname{Tr}_{AB}J=I_{CD}$ 就给出一个协变 CPTP 通道，不能省略这条整体约束。

下面计算伴随块。四个输出向量依次是

$$
\begin{aligned}
b_{0,a}&=|0\rangle\otimes T_a|1\rangle,&
b_{1,a}&=T_a|0\rangle\otimes|1\rangle,\\
b_{2,a}&=|1\rangle\otimes T_a|0\rangle,&
b_{3,a}&=T_a|1\rangle\otimes|0\rangle.
\end{aligned}
\tag{6.14}
$$

目标振幅仅来自 $b_{0,a}$，为 $(T_a)_{21}$，其模平方之和由 (6.4) 等于一。故 $s_{\bf8}=X$。再次用 (6.4) 求内积和，以及在第一寄存器投影到 $I-|0\rangle\langle0|$ 后的内积和，得到两个完整的 Hermitian 形式

$$
\sum_a(\langle b_{i,a},b_{j,a}\rangle)_{ij}
 =\mathsf H=\begin{pmatrix}
8/3&-1/3&0&1\\
-1/3&8/3&1&0\\
0&1&8/3&-1/3\\
1&0&-1/3&8/3
\end{pmatrix},
\qquad
\sum_a(\langle b_{i,a},[(I-P)\otimes I]b_{j,a}\rangle)_{ij}
 =\begin{pmatrix}0&0\\0&\mathsf Q\end{pmatrix}.
\tag{6.15}
$$

因此这些等式对全部复系数成立，而不限于实参数方向。伴随块的总输出迹为

$$
\frac83X+2\operatorname{Re}\sum_r\overline{x_r}(w_r-y_r/3)+q_0,
\qquad
q_0=\sum_{r,a}\|y_rb_{1,a}+z_rb_{2,a}+w_rb_{3,a}\|^2\ge0.
\tag{6.16}
$$

其余各正 Choi 块在这个输入上亦贡献非负输出迹。全通道的迹为一，于是 (6.16) 蕴含 (6.10) 的第一个不等式，没有舍弃可相消的扇区交叉项。

$\mathsf Q$ 的顺序主子式为 $2,13/3,7$，故严格正定。置 $h=(1/4,0,-3/4)^{\mathsf T}$，直接求解得

$$
\mathsf Q^{-1}h=\left(\frac4{21},-\frac{11}{84},-\frac{10}{21}\right)^{\mathsf T},
\qquad h^\dagger\mathsf Q^{-1}h=\frac{17}{42}.
\tag{6.17}
$$

在 $\mathsf Q$ 内积中应用复 Cauchy—Schwarz，再对 $r$ 求和，即有

$$
\left|\sum_r\overline{x_r}h^\dagger v_r\right|
 \le\sqrt{\sum_r|x_r|^2}
       \sqrt{(h^\dagger\mathsf Q^{-1}h)\sum_rv_r^\dagger\mathsf Qv_r}.
$$

这给出 (6.10) 的第二个不等式。证毕。

## 7. Haar 泄漏谱与全部扇区的上界

**定理 7.1（正交对承诺的泄漏算子及其完整谱）。** 在 (6.1) 的次序下，定义

$$
\begin{aligned}
\mathscr D&=\int (I-P)_A\otimes I_B\otimes\bar P_C\otimes\bar Q_D\,d(P,Q),\\
\mathscr T&=\int P_A\otimes R_B\otimes\bar P_C\otimes\bar Q_D\,d(P,Q).
\end{aligned}
\tag{7.1}
$$

则 $\bar\ell_{\mathcal N}=\operatorname{Tr}(J_{\mathcal N}\mathscr D)$，$\bar s_{\mathcal N}=\operatorname{Tr}(J_{\mathcal N}\mathscr T)$。将旁观输出 $B$ 移到最前后，$\mathscr D=I_B\otimes D_0$，其中在 $A,C,D$ 次序下

$$
D_0=\frac12\int (I-P)_A\otimes\bar P_C\otimes(I-\bar P)_D\,dP.
\tag{7.2}
$$

令 $F_{CD}$ 交换 $C,D$，以下简记为 $F_c$；令

$$
|\Omega\rangle_{AC}=\sum_{j=0}^2|j,j\rangle,
\qquad E=|\Omega\rangle\langle\Omega|_{AC}\otimes I_D,
\qquad E'=F_cEF_c.
$$

则

$$
120D_0=11I-4F_c-4E+E'+EF_c+F_cE.
\tag{7.3}
$$

$D_0$ 的谱为 $0,1/8,7/120$，重数分别为 $3,9,15$；$\mathscr D$ 的对应重数为 $9,27,45$。特别地，

$$
\ker\mathscr D=\{|I_A\otimes B\rangle\!\rangle:B\in\operatorname{End}(H)\}.
\tag{7.4}
$$

这个核只有一份标量和一份伴随表示。因此在 (6.5) 的全部剩余扇区上

$$
\mathscr D\big|_{\mathcal H_{10}\oplus\mathcal H_{\overline{10}}\oplus\mathcal H_{27}}
 \succeq\frac7{120}I.
\tag{7.5}
$$

证明。给定 $P$，同一标架内 $Q$ 在 $P^\perp$ 上均匀，故 $\mathbb E[Q\mid P]=(I-P)/2$，这先给出 (7.2)。下面只复用归一化复 Haar 矩公式 [Harrow，命题 6 式 (7)][HAAR]：

$$
\int P^{\otimes n}\,dP
 =\frac{\sum_{\pi\in S_n}U_\pi}{3\cdot4\cdots(3+n-1)}.
\tag{7.6}
$$

对二阶矩作适当的共轭或部分转置，分别得到 $(I+F_c)/12$ 和 $(I+E)/12$；三阶矩先整体共轭，再在 $A$ 因子部分转置，得到

$$
\int P_A\otimes\bar P_C\otimes\bar P_D\,dP
 =\frac{I+F_c+E+E'+EF_c+F_cE}{60}.
\tag{7.7}
$$

展开 (7.2) 的四项，便有

$$
D_0=\frac12\left[
 \frac I3-\frac{I+F_c}{12}-\frac{I+E}{12}
 +\frac{I+F_c+E+E'+EF_c+F_cE}{60}\right],
$$

即 (7.3)。这里的部分转置仅用于矩恒等式的代数计算，不是允许通道中的物理操作。

为完整求谱，对 $v\in H$ 记

$$
k(v)=|\Omega\rangle_{AC}\otimes v_D,
\qquad l(v)=F_ck(v).
$$

这些映射满足

$$
k^\dagger k=l^\dagger l=3I,
\qquad k^\dagger l=I.
\tag{7.8}
$$

所以 $\mathcal W=\operatorname{ran}k+\operatorname{ran}l$ 是六维空间。由定义有 $F_ck=l$、$F_cl=k$、$Ek=3k$、$El=k$、$E'k=l$、$E'l=3l$，代入 (7.3) 得

$$
D_0k(v)=0,
\qquad D_0l(v)=\frac{3l(v)-k(v)}{24}.
\tag{7.9}
$$

于是 $\operatorname{ran}k$ 是三维零空间，$\{l(v)-k(v)/3:v\in H\}$ 是与它正交的三维 $1/8$ 本征空间。

$F_c$ 保持 $\mathcal W$ 及 $\mathcal W^\perp$。后者上 $E=E'=0$，并且 $EF_c=F_cE=0$，故 $D_0=(11I-4F_c)/120$。整个 $A,C,D$ 空间上 $F_c=+1,-1$ 的维数分别为 $3\cdot6=18$、$3\cdot3=9$；$\mathcal W$ 内 $k+l$ 和 $k-l$ 分别占去三维。因此 $\mathcal W^\perp$ 的正、负交换空间维数为 $15,6$，给出 $7/120$ 的十五重数和 $1/8$ 的另六重数。连同 (7.9)，这穷尽全部二十七维；亦有 $\operatorname{Tr}D_0=2$。

乘上三维旁观因子 $B$ 后即得 $\mathscr D$ 的重数。在 $A,B,C,D$ 次序中，$|I_A\otimes B\rangle\!\rangle$ 恰好是 $|\Omega\rangle_{AC}$ 与任意 $B,D$ 向量的张量积，故谱计算给出 (7.4)，不只有核的包含关系。共轭作用在这个核上就是 $B\mapsto UBU^\dagger$，故分解为 ${\bf1}\oplus{\bf8}$。所有 $10,\overline{10},27$ 扇区都与核正交，而全部正本征值至少为 $7/120$，所以 (7.5) 覆盖它们全部。证毕。

**定理 7.2（全部协变通道的统一估计）。** 定理 5.3 的上界 (5.10) 成立；其右侧第二项的局部展开为

$$
\frac38+\frac{\sqrt{119}}{28}\sqrt\varepsilon
          +\frac{257}{84}\varepsilon+O(\varepsilon^{3/2}).
\tag{7.10}
$$

证明。由定理 5.2，只需考虑协变通道，但仍保留 (6.5) 的每个正块。先逐点用 $0\preceq P\otimes R\preceq I_{AB}$，张量乘上正输入因子再平均，得到

$$
0\preceq\mathscr T\preceq I_{AB}\otimes M_{CD},
\qquad
M=\int\bar P\otimes\bar Q\,d(P,Q)
 =\frac12\left[\frac I3-\frac{I+S_{CD}}{12}\right]
 =\frac{I-S_{CD}/3}{8}.
\tag{7.11}
$$

$M$ 在六维对称输入空间上的本征值为 $1/12$，在三维反对称空间上为 $1/6$，故 $\mathscr T\preceq I/6$。令 $\delta_{\rm rest}=\operatorname{Tr}(J_{\rm rest}\mathscr D)$、$s_{\rm rest}=\operatorname{Tr}(J_{\rm rest}\mathscr T)$。由 (7.5) 及 (7.11)，

$$
\delta_{\rm rest}\ge\frac7{120}\operatorname{Tr}J_{\rm rest},
\qquad
s_{\rm rest}\le\frac16\operatorname{Tr}J_{\rm rest}
                  \le\frac{20}{7}\delta_{\rm rest}.
\tag{7.12}
$$

标准 Choi 谱上界的使用参见 [CPMAP，式 (15)][CPMAP]；本处的常数还使用了 (7.3)—(7.5) 的承诺特定泄漏谱。

任何标量 Kraus 算子 $aI+bS$ 把 $|01\rangle$ 送到 $a|01\rangle+b|10\rangle$，其 $|02\rangle$ 振幅为零。故任意复标量重数块的目标分数均为零。伴随分数由 (6.9) 为 $X$，没有扇区间交叉项。总泄漏 $\delta=\operatorname{Tr}(J\mathscr D)\le\varepsilon$ 是各正块泄漏之和，于是

$$
\bar s\le X+\frac{20}{7}\varepsilon,
\qquad
X-\frac38\le\sqrt{\frac{17}{42}X\varepsilon}.
\tag{7.13}
$$

令 $z=\sqrt X\ge0$、$a=\sqrt{17\varepsilon/42}$。第二式直接变成 $z^2-az-3/8\le0$，从而

$$
X\le\frac{(a+\sqrt{a^2+3/2})^2}{4}.
$$

这个解法对 $X<3/8$ 同样有效，不对符号未定的不等式贸然平方。与 $\bar s\le1$ 合并即得 (5.10)。展开该根式，$\sqrt\varepsilon$ 系数为 $\sqrt{17/112}$，一次项为 $17/84+20/7=257/84$，得到 (7.10)。对其余扇区及整体保迹的估计只用于上界，不声称有限误差时同时取等。证毕。

## 8. 全代数保迹的有理八 Kraus 通道族

**定义 8.1（固定的有理变形）。** 使用定义 6.1 的任意固定无迹正交归一基及交换 $S$。对 $0\le t\le1/1000$，置

$$
u_t=16t,\qquad v_t=-11t,\qquad
w_t=\frac{-40t+176t^2}{1-95t},
\tag{8.1}
$$

以下涉及此族的公式简写 $u=u_t,v=v_t,w=w_t$。令

$$
\begin{aligned}
L_a(t)&=E_0(T_a)+uE_1(T_a)+vE_2(T_a)+wE_3(T_a),\\
A(t)&=\frac83(1+u^2+v^2+w^2)+2w-\frac23wv-\frac23u+2uv,\\
f(t)&=1-224t+14502t^2-98336t^3+2196121t^4,\\
K_a(t)&=A(t)^{-1/2}L_a(t),\qquad
\mathcal N_t(Y)=\sum_{a=1}^8K_a(t)YK_a(t)^\dagger.
\end{aligned}
\tag{8.2}
$$

通道只依赖固定的 $t$ 和基，不依赖未知的 $(P,Q)$。$u_t$ 是变形参数，与定义 1.1 的原单位泛函 $u$ 无关。

**定理 8.2（所述区间上的正性、全保迹与协变性）。** 对全部 $0\le t\le1/1000$，(8.2) 定义整个 $\mathcal L(H\otimes H)$ 上的 CPTP 通道，并满足 (5.5)。其正归一化为

$$
A(t)=\frac{8f(t)}{3(1-95t)^2}>0.
\tag{8.3}
$$

在 $t=0$ 它恰好是 (3.5) 的 $\operatorname{id}\otimes\Lambda_*$。

证明。由 (6.4)，在整个 $H\otimes H$ 上有下列算子矩阵恒等式，其中第 $i,j$ 项是 $\sum_aE_i(T_a)^\dagger E_j(T_a)$：

$$
\begin{pmatrix}
\frac83I&S-\frac13I&\frac83S&I-\frac13S\\
S-\frac13I&\frac83I&I-\frac13S&\frac83S\\
\frac83S&I-\frac13S&\frac83I&S-\frac13I\\
I-\frac13S&\frac83S&S-\frac13I&\frac83I
\end{pmatrix}.
\tag{8.4}
$$

例如，$\sum_aT_a\otimes T_a^\dagger=S-I/3$ 由 (6.4) 逐项得出；再右乘 $S$ 即给出 $I-S/3$，其余项使用 $S^2=I$ 及两条伴随乘积完整性恒等式。这不是仅在承诺输入上检查迹。

对任意实 $u,v,w$，(8.4) 给出

$$
\sum_aL_a^\dagger L_a=A I+\beta S,
\qquad
\beta=\frac23(-w+8wu+3wv+3u+8v-uv).
\tag{8.5}
$$

当 $1-8u-3v\ne0$ 时，使交换项严格消失的解为

$$
w=\frac{3u+8v-uv}{1-8u-3v}.
\tag{8.6}
$$

代入 $u=16t,v=-11t$，分母恰为 $1-95t$，得到 (8.1)；所以 $\beta$ 在整个参数区间恒为零，而非只在一阶为零。代入 $A$ 并通分得到 (8.3)。区间上

$$
1-95t\ge\frac{905}{1000}>0,
\qquad
f(t)\ge1-\frac{224}{1000}-\frac{98336}{10^9}
       =\frac{24246927}{31250000}>0.
\tag{8.7}
$$

其中只舍去了非负的二次和四次项。因此 $A^{-1/2}$ 有定义，(8.5) 给出 $\sum_aK_a^\dagger K_a=I$。Kraus 形式给出完全正性，这个算子恒等式给出全代数保迹性，包括承诺族外输入及带参考系统的使用；表示原理复用 [CPMAP，§III][CPMAP]。

任意 $U$ 的共轭在无迹矩阵空间上是酉变换，故存在酉矩阵 $D(U)$ 使 $UT_aU^\dagger=\sum_bD(U)_{ba}T_b$。四个 $E_i$ 都按同一个 $D(U)$ 变换，因为 $S$ 与 $U\otimes U$ 对易。于是整族 $L_a$、$K_a$ 同样只作一个 Kraus 指标的酉变换，求和后得到 (5.5)。这不需要输入相关的基或控制。

最后 $t=0$ 时 $A=8/3$、$L_a=I\otimes T_a$。由 (6.4) 的另一个等价式 $\sum_aT_aYT_a^\dagger=\operatorname{Tr}(Y)I-Y/3$，第二因子通道是

$$
\frac38\sum_aT_aYT_a^\dagger
 =\frac{3\operatorname{Tr}(Y)I-Y}{8}=\Lambda_*(Y).
$$

这就是已知无转置 universal-NOT 端点 [NOT，式 (2.37)][NOT] 在本问题中的原应用，不另作为新反演定理。证毕。

## 9. 精确扰动、误差反解与首项取等

**定理 9.1（通道族的实际边缘与联合分数）。** 对每个 $0\le t\le1/1000$ 和每个 $(P,Q)\in\mathfrak F$，(8.2) 的第一输出为

$$
\rho_A^{\mathcal N_t}(P,Q)=\frac{a_0P+a_1Q+a_2R}{A},
\tag{9.1}
$$

其中

$$
\begin{aligned}
a_0&=\frac83-\frac23u+\frac23u^2+2w+w^2,\\
a_1&=u^2+2uv+\frac83v^2-\frac23vw+\frac23w^2,\\
a_2&=u^2+w^2.
\end{aligned}
\tag{9.2}
$$

这些量非负且 $a_0+a_1+a_2=A$。实际迹距离和联合分数恰为

$$
\begin{aligned}
D(\mathcal N_t)=d_{\mathcal N_t}(P,Q)
 &=\varepsilon(t)=\frac{9t^2(119-3584t+178545t^2)}{f(t)},\\
s_{\mathcal N_t}(P,Q)&=s(t)=\frac{3(1-95t)^2}{8f(t)}.
\end{aligned}
\tag{9.3}
$$

证明。在参考对 $|01\rangle$ 上，未归一化输出为 $\sum_a|L_a01\rangle\langle L_a01|$。由 (6.14) 及 (6.4) 对第二输出作部分迹，三个对角项正是 (9.2)；非对角项为零。也可先用定理 8.2 的协变性与参考对的独立相位稳定子消去非对角项，再逐项计算对角项。它们是正算子的对角元，故非负；求和给出 (8.2) 中的 $A$。因此迹距离不是仅被泄漏估计，而是精确等于

$$
\frac{|a_0/A-1|+a_1/A+a_2/A}{2}
 =\frac{a_1+a_2}{A}
 =\frac{(u,v,w)\mathsf Q(u,v,w)^{\mathsf T}}{A}.
\tag{9.4}
$$

另一方面，$|02\rangle$ 的未归一化目标振幅平方和仅来自 $E_0$，由 (6.4) 恰为一，故联合分数是 $1/A$。代入 (8.1)、(8.3) 并通分，即得到 (9.3)。协变性把参考对的这个精确计算搬到每个有序复正交对，故它们同时是最坏迹距离与最坏分数，而非平均或特定实标架上的数值。证毕。

**定理 9.2（局部反解、匹配系数与二阶边界）。** $\varepsilon(t)$ 在 $[0,1/1000]$ 上严格递增。故每个 $0\le\varepsilon\le\varepsilon(1/1000)$ 都有唯一的该族参数，使实际最坏扰动等于 $\varepsilon$，且该通道的分数满足 (5.11)。结合 (5.10)，它给出 (5.8)—(5.9)，但不确定 $F$ 的最优二阶系数。

证明。由 (9.3) 的有理式在零点展开，得

$$
\begin{aligned}
\varepsilon(t)&=1071t^2+207648t^3+32588415t^4+O(t^5),\\
s(t)&=\frac38+\frac{51}{4}t+\frac{6417}{8}t^2
                         +\frac{63303}{2}t^3+O(t^4).
\end{aligned}
\tag{9.5}
$$

为覆盖所述整个区间，直接微分得到

$$
\varepsilon'(t)=\frac{18t\,g(t)}{f(t)^2},
\quad
\begin{aligned}
g(t)={}&119-18704t+1159906t^2-80127712t^3\\
       &+2327921191t^4-4843251728t^5.
\end{aligned}
\tag{9.6}
$$

在该区间，

$$
g(t)\ge119-\frac{18704}{1000}-\frac{80127712}{10^9}
                    -\frac{4843251728}{10^{15}}
       =\frac{6263491715296767}{62500000000000}>100.
\tag{9.7}
$$

由 (8.7)，$f>0$，故 $\varepsilon'(t)>0$ 对 $t>0$ 成立。连续性和 $\varepsilon(0)=0$ 给出整个误差区间上的存在唯一性。

虽然 $\varepsilon'(0)=0$，可以对有符号平方根参数应用通常的解析反函数定理。具体地，在零点邻域定义实解析函数

$$
r(t)=3t\sqrt{\frac{119-3584t+178545t^2}{f(t)}}.
\tag{9.8}
$$

根号内在零点为正，故可取正的解析支；$r'(0)=\sqrt{1071}>0$，而 $t\ge0$ 时 $r(t)=\sqrt{\varepsilon(t)}$。因此 $r$ 有解析局部逆。令 $q=\sqrt\varepsilon$，(9.5) 给出

$$
t=\frac{q}{\sqrt{1071}}
       -\frac{207648}{2\cdot1071^2}q^2+O(q^3).
\tag{9.9}
$$

代回 $s(t)$，首项和次项分别为

$$
\frac{51}{4\sqrt{1071}}=\frac{\sqrt{119}}{28},
\qquad
\frac{6417}{8\cdot1071}
 -\frac{(51/4)207648}{2\cdot1071^2}=-\frac{1157}{2856}.
\tag{9.10}
$$

这证明 (5.11) 对每个足够小的实际预算成立，而非只对一列参数成立。

首项取等的几何方向也直接由 (6.17) 看出：

$$
(u,v,w)=t(16,-11,-40)+O(t^2),
\quad
(16,-11,-40)^{\mathsf T}=84\mathsf Q^{-1}h,
\quad
(16,-11,-40)\mathsf Q(16,-11,-40)^{\mathsf T}=2856.
\tag{9.11}
$$

它使伴随块的对偶范数估计在首阶取等，(8.6) 则把该方向修正为严格保迹的有理族。于是 $F(\varepsilon)\ge s(t(\sqrt\varepsilon))$ 与 (7.10) 具有相同的 $\sqrt\varepsilon$ 系数，双方余项均为 $O(\varepsilon)$，推出 (5.8)—(5.9)。上下界的一次项不同，不能由此把 $-1157/2856$ 或 $257/84$ 指认为最优二阶系数；精确有限误差前沿、全局最优通道及最优二阶项仍待确定。证毕。

**定理 9.3（一个严格正扰动的精确取值）。** 参数 $t=1/1000$ 的固定通道在每个承诺输入上同时具有

$$
D(\mathcal N_{1/1000})=\frac{1040350905}{790405860121},
\qquad
s_{\mathcal N_{1/1000}}=\frac{307134375000}{790405860121}>\frac38.
\tag{9.12}
$$

证明。将 $t=1/1000$ 代入 (9.3) 并约分即得两式。严格不等式等价于

$$
8\cdot307134375000-3\cdot790405860121=85857419637>0.
$$

其保迹性和全部分支的无条件计数由定理 8.2 保证。这个取值证明同一未知双份合同内可同时达到严格改善，不附加精确第三态的成功标志。证毕。

## 10. 原关联的有误差应用与保留的操作前提

**定理 10.1（同原 $\tau$ 的单步受控保证）。** 在定义 1.1—1.2 的完整 $\mathsf Q_1$ 原域、同锥同单位 $\Phi$ 对应及假设 1.3 的实际 $\mathrm E_2$ 产品准备下，若允许的改变恰为 (5.1) 的第一边缘最坏迹距离预算，则原 Quantum116 消费者 $\tau$ 的最佳保证联合目标重叠就是 $F(\varepsilon)$，并满足定理 5.3。这个结论不增加 $\mathrm E_3$ 准备，不给出近似输出上的精确关联字作用，也不蕴含应用 4.1 中另外的 Native/AA 来源、操作、授权、返回和全部切口合同。

证明。原关联与 $\mathfrak F$ 的双向对应、目标 $\mathrm E_2(\tau(p,q))=P\otimes R$ 已由定义 1.2 给定；这里两者及同一产品输入均未改变。整个原效应区间与全部矩阵效应相对应，故 (5.2) 的第一输出效应概率误差也在原对应下逐项解释。定理 5.2—9.2 因而直接给出该消费者的单步最坏保证。

该对应本身不准备 $P\otimes Q$，也不供应所需的固定辅助系统、通道控制或验证测量；实际准备、控制、物理实现与全部资源费用仍是独立前提。联合重叠只评价目标测试，不产生可辨识的精确 $P\otimes R$ 输出分支。对于 $\varepsilon>0$ 的构造，输出通常不再是承诺的精确正交产品，因此 (4.1) 对精确 $\mathrm E_3$ 的逐字复合证明不能直接应用于这些近似输出；本定理没有提供相应的迭代误差合同或精确有限字恢复。

Quantum116 的 $\sigma,\tau$ 与 Fibonacci 的 $\alpha,\beta$ 没有由此取得操作认同。Native/AA 的实际原来源、同一待执行消费者、当前授权、取得与返回，以及全部切口、有限请求森林、记录、backing 和费用前提，完整保留应用 4.1 的范围；本定理不提供量子到 Native 的新对应。它也不比较跨编码的最少样本、全局最少关系或总资源优势。证毕。

[CPMAP]: https://arxiv.org/html/quant-ph/0105124 "Jaromír Fiurášek, Extremal equation for optimal completely-positive maps；§II (3)—(8)、(15)，§III (16)—(19)：正 Choi、保迹、线性平均分数、谱上界及 Kraus 表示。"
[HAAR]: https://arxiv.org/html/1308.6595v1 "Aram W. Harrow, The Church of the Symmetric Subspace；Theorem 5、Proposition 6 (7)：复对称张量空间、Schur 引理与归一化复 Haar 矩。"
[ASYM]: https://arxiv.org/html/quant-ph/0505212v1 "Jaromír Fiurášek, Radim Filip and Nicolas J. Cerf, Highly asymmetric quantum cloning in arbitrary dimension；(5)—(10)：正 Choi、偏迹约束及 Schur 平均方法；其克隆目标不同于本卷。"
[BALANCE]: https://arxiv.org/pdf/quant-ph/0003123v2 "Konrad Banaszek, Fidelity balance in quantum operations；(4)—(5)：单输入操作与经典估计的 Haar 平均分数。"
[ORTHOCLONE]: https://arxiv.org/pdf/quant-ph/0110016v1 "Jaromír Fiurášek, Sofyan Iblisdir, Serge Massar and Nicolas J. Cerf, Quantum cloning of orthogonal qubits；(4)、(15)—(16)：正交 qubit 输入与单克隆平均保真度。"

## 追加锚（本行以下为增补区）

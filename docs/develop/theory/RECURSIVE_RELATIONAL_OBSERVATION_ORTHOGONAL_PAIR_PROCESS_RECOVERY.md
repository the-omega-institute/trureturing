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

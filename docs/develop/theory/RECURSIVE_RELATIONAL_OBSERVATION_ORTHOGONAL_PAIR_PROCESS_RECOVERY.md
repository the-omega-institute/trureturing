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

## 11. 同一双份输入的经典历史与精确返回合同

**定义 11.1（经典历史返回类）。** 保留定义 5.1 的整个复承诺域 $\mathfrak F$、同一未知输入 $P_A\otimes Q_B$、指定目标 $P_A\otimes R_B$，以及同一最坏第一边缘迹距离 $D(\mathcal N)$。原来源应用仍要求定义 1.1—1.2 的完整 $\mathsf Q_1$、同锥同单位 $\Phi$ 和假设 1.3 的实际 $\mathrm E_2$ 准备。没有传入 $(P,Q)$ 的描述、依赖准备的程序、额外未知样本或成功后选择。

令 $\mathsf C$ 为非空有限或可数经典结果集。固定仪器的每个结果可以是一条完整有限经典历史；其一般 CP 分支记为 $\mathcal M_c:\mathcal L(AB)\to\mathcal L(AB)$，不假定一个结果只有一个 Kraus 算子。写

$$
\mathcal M(X)=\bigoplus_{c\in\mathsf C}\mathcal M_c(X)
 =\sum_{c\in\mathsf C}\mathcal M_c(X)\otimes|c\rangle\langle c|,
\qquad
\mathcal N(X)=\sum_c\mathcal M_c(X).
\tag{11.1}
$$

要求 $\mathcal N$ 是整个九维输入代数上的 CPTP 通道。可数情形采用通常的可数可加仪器：正输入的和在迹范数中收敛，其他输入由线性延拓。第一种写法把输出视为九维迹类空间的 $\ell^1$ 直和；第二种是同一经典输出的块对角表示。这里的 $\mathsf C$ 不包含未建模的连续模拟结果。

返回操作可访问的全部保留量子输出恰为 $AB$，另可读取经典 $c$。允许丢弃不可访问的环境；不允许在返回时另取保存了输入信息的相干量子工作区。与准备无关的新辅助态、随机性和自适应控制可以包含在操作中，但其实际供给和费用仍须另付。

称该仪器具有精确工作寄存器返回，若有固定 CPTP 操作 $\mathcal D$ 从这个经典—量子输出到 $AB$，使

$$
\mathcal D\mathcal M(P\otimes Q)=P\otimes Q
\quad\text{对每个 }(P,Q)\in\mathfrak F.
\tag{11.2}
$$

这里允许任意记录条件化校正，不要求它是另一次固定 $\tau$ 调用。故 (11.2) 是原完整返回的必要放宽：它只要求工作寄存器，尚未要求原记录、控制状态、权限、所欠动作和资源也返回。定义

$$
F_{\rm ret}(\varepsilon)=
\sup\left\{\inf_{\mathfrak F}s_{\mathcal N}(P,Q):
 D(\mathcal N)\le\varepsilon,\ (\mathcal M,\mathcal D)
 \text{ 满足 }(11.1)\text{—}(11.2)\right\},
\qquad 0\le\varepsilon\le1.
\tag{11.3}
$$

不预设这个上确界取到，也不把分数解释成带标志的精确输出概率。

**命题 11.2（复用承诺刚性与经典校正判据）。** 若 (11.2) 成立，则

$$
\mathcal D\mathcal M=\operatorname{id}_{AB}
\quad\text{在整个矩阵代数上成立}.
\tag{11.4}
$$

而且存在与输入无关的 $p_c\ge0$、$\sum_cp_c=1$，使每个非零分支均为

$$
\mathcal M_c(X)=p_cU_cXU_c^\dagger,
\qquad U_c\in U(9).
\tag{11.5}
$$

因此 $\mathcal N$ 是混合酉通道，特别地 $\mathcal N(I_9)=I_9$。这一步是本卷定理 2.1 与成熟精确校正结构的应用，不是新的校正判据；保单位性仅为必要条件。

证明。置 $\mathcal T=\mathcal D\mathcal M$。虽然中间历史可以可数，$\mathcal T$ 的输入、输出都只有九维，且为 CPTP。由 (11.2)，它满足 (1.1)；定理 2.1 直接给出全局 $\mathcal T=\operatorname{id}_A\otimes\Lambda_B$。每个秩一 $Q$ 都有某个正交 $P$，所以 (11.2) 又给出 $\Lambda(Q)=Q$。秩一投影实张成全部 Hermitian 矩阵，再复线性张成全部矩阵，故 $\Lambda=\operatorname{id}$，得到 (11.4)。这里没有假定正交产品承诺本身线性张成整个两份代数。全局通道恒等也保留任意未触碰参考系统的相关。

把 $\mathcal D$ 限制到第 $c$ 个经典输入块，得到九维 CPTP 通道 $\mathcal D_c(Y)=\mathcal D(Y\otimes|c\rangle\langle c|)$。未归一化 Choi 矩阵满足

$$
\sum_cJ_{\mathcal D_c\mathcal M_c}
 =J_{\operatorname{id}}=|I_9\rangle\!\rangle\langle\!\langle I_9|.
\tag{11.6}
$$

左边各项为正。右边秩一，故每项的支撑都在 $\mathbb C|I_9\rangle\!\rangle$ 内：对其正交补向量，各项非负二次型之和为零；正性再使交叉分量为零。因此 $\mathcal D_c\mathcal M_c=p_c\operatorname{id}$，$p_c\ge0$，且 $\sum_cp_c=1$。可数时这个正矩阵和在迹范数中收敛，其总迹为九，同样的逐项支撑论证仍成立，不必把有限维结构定理直接用于无限维历史空间。

由 $\mathcal D_c$ 保迹，对所有正 $X$ 有 $\operatorname{Tr}\mathcal M_c(X)=p_c\operatorname{Tr}X$。所以结果概率与输入无关，$p_c=0$ 的分支为零；若 $p_c>0$，则 $\mathcal M_c/p_c$ 是九维 CPTP 通道，且具有 CPTP 左逆 $\mathcal D_c$。直接应用 [Nayak—Sen，定理 2.1][CRNS] 的输入、输出同维情形，它必须是酉共轭，得到 (11.5)。这也是 [Gregoratti—Werner，命题 2、§II.3.1][CRGW] 的整码经典辅助校正结构在本问题中的形式。最后逐项求和得到混合酉和保单位性。整个论证从一般 CP 分支出发，没有预置纯分支或单 Kraus 结果。证毕。

**例 11.3（已有零扰动端点的返回校准）。** 类 (11.3) 非空，而且

$$
F_{\rm ret}(0)=\frac38,\qquad
F_{\rm ret}(\varepsilon)\ge\frac38\quad(0\le\varepsilon\le1).
\tag{11.7}
$$

证明。直接使用 (3.5) 的八个非恒等 qutrit Weyl，等概率施加 $I_A\otimes W_{ab}$ 并保留其八值经典标签。忽略标签正是 $\mathcal N_*$，$D=0$ 且每个目标重叠为 $3/8$。若另给标签条件化的逆控制，施加 $I_A\otimes W_{ab}^\dagger$ 即在全部输入上返回。也可只用同一正向门：这些固定 Weyl 满足 $W_{ab}^3=I$，故再调用两次 $W_{ab}$ 给出相同校正。这个存在性校准复用既有 Weyl 混合和经典校正工具；实际采样器、三比特标签、全部执行记录、初始门和两次校正门、两个寄存器及控制器均须供给并计费。上界由 $F_{\rm ret}(0)\le F(0)=3/8$ 给出；同一实例对所有非负预算可行。它不提供正扰动时的最优返回族。证毕。

## 12. 全复重数与全部剩余扇区的保单位约束

本节沿用定义 6.1 的向量化、$S$、$T_a$、四个 $E_i$，以及定理 6.2 的完整 $2\cdot\mathbf1+4\cdot\mathbf8+\mathbf{10}+\overline{\mathbf{10}}+\mathbf{27}$ 分解。所有复正重数矩阵与三个剩余扇区都保留。对各正 Choi 块对应的 CP 映射 $\mathcal N_\alpha$，定义

$$
\Delta_\alpha=\mathcal N_\alpha(I_9)-\mathcal N_\alpha^*(I_9).
\tag{12.1}
$$

星号在这里是 Hilbert—Schmidt 对偶。单个块无需保迹；整个通道保迹时，$\sum_\alpha\Delta_\alpha=\mathcal N(I_9)-I_9$。

**引理 12.1（伴随块的完整缺陷公式）。** 对 (6.7) 的任意复系数与任意重数分解，

$$
\Delta_{\mathbf8}
 =2\operatorname{Re}\sum_r
  (\overline{x_r}-\overline{y_r})(z_r-w_r)(I_9-3S).
\tag{12.2}
$$

任意标量块的 $\Delta_{\mathbf1}$ 为零。

证明。记 (8.4) 的第 $i,j$ 项为 $M_{ij}=\sum_aE_i(T_a)^\dagger E_j(T_a)$。这些算子都是 $I_9,S$ 的实线性组合，且 $M_{ij}=M_{ji}$。由 $S^2=I_9$ 和交换恒等式，

$$
E_0(T)^\dagger=E_0(T^\dagger),\quad
E_1(T)^\dagger=E_1(T^\dagger),\quad
E_2(T)^\dagger=E_3(T^\dagger),\quad
E_3(T)^\dagger=E_2(T^\dagger).
\tag{12.3}
$$

取共轭转置后的 $T_a$ 仍是一组无迹正交归一基，故完整性恒等式 (6.4) 不变。令 $\pi$ 交换指标 $2,3$ 而固定 $0,1$，则 $\sum_aE_i(T_a)E_j(T_a)^\dagger=M_{\pi(i),\pi(j)}$。将 (8.4) 代入，全部十六个系数同时给出

$$
\left(\sum_a[E_i(T_a)E_j(T_a)^\dagger
                    -E_j(T_a)^\dagger E_i(T_a)]\right)_{ij}
 =\begin{pmatrix}
0&0&1&-1\\
0&0&-1&1\\
1&-1&0&0\\
-1&1&0&0
\end{pmatrix}(I_9-3S).
\tag{12.4}
$$

例如第 $0,2$ 项为 $I_9-S/3-(8/3)S=I_9-3S$；第 $1,2$ 项为其负，其余项由表给出。用 $c_r=(x_r,y_r,z_r,w_r)$，把 (12.4) 乘上 $c_{r,i}\overline{c_{r,j}}$ 并求和，即得 (12.2)。这是完整复半双线性形式，不要求系数实数，也不要求重数矩阵秩一。标量 Kraus $aI_9+bS$ 与自身伴随对易，故每项 $KK^\dagger-K^\dagger K$ 为零；任意复标量重数块亦如此。证毕。

**引理 12.2（剩余扇区的缺陷与泄漏）。** 对全部剩余正块之和，存在实数 $a_{\rm rest}$，使

$$
\Delta_{\rm rest}=a_{\rm rest}(I_9-3S),\qquad
|a_{\rm rest}|\le\frac1{12}\operatorname{Tr}J_{\rm rest}
                 \le\frac{10}{7}\delta_{\rm rest},\qquad
s_{\rm rest}\le\frac{20}{7}\delta_{\rm rest}.
\tag{12.5}
$$

证明。每个等型正块本身协变，所以 $\mathcal N_{\rm rest}(I_9)$ 与 $\mathcal N_{\rm rest}^*(I_9)$ 都与所有 $U\otimes U$ 对易。其差为 Hermitian，且迹为零；两份张量表示的交换子代数由 $I_9,S$ 张成。因此差必须为实数倍的 $I_9-3S$，因为 $\operatorname{Tr}I_9=9$、$\operatorname{Tr}S=3$。

令 $A=\mathcal N_{\rm rest}(I_9)$、$B=\mathcal N_{\rm rest}^*(I_9)$。它们均为正，且各自迹等于 $\operatorname{Tr}J_{\rm rest}$。由 $\|S\|_{\rm op}=1$，

$$
|\operatorname{Tr}[S(A-B)]|
 \le\operatorname{Tr}A+\operatorname{Tr}B
 =2\operatorname{Tr}J_{\rm rest},\qquad
\operatorname{Tr}[S(I_9-3S)]=-24.
\tag{12.6}
$$

这给出第一个不等式。定理 7.1 的完整泄漏谱在 $\mathbf{10},\overline{\mathbf{10}},\mathbf{27}$ 上给 $\mathscr D\succeq(7/120)I$；而 (7.11) 给 $0\preceq\mathscr T\preceq I/6$。直接复用这些已证算子界，得到 $\operatorname{Tr}J_{\rm rest}\le(120/7)\delta_{\rm rest}$ 和 $s_{\rm rest}\le\operatorname{Tr}J_{\rm rest}/6$，即 (12.5)。没有删去任何剩余扇区，也没有假定这些界可同时取等。证毕。

## 13. 任意保单位通道的统一上界

**定理 13.1（全复、全扇区的保单位界）。** 置

$$
k=\frac{83}{304},\qquad c=\frac{87}{133},\qquad
U(\varepsilon)=\min\left\{1,
\frac{20}{7}\varepsilon+
\frac{\left(\sqrt{k\varepsilon}
 +\sqrt{3/2+(k+4c)\varepsilon}\right)^2}{4}\right\}.
\tag{13.1}
$$

对任意保单位 CPTP 通道 $\mathcal N:\mathcal L(AB)\to\mathcal L(AB)$，若 $D(\mathcal N)\le\varepsilon$，$0\le\varepsilon\le1$，则

$$
\inf_{(P,Q)\in\mathfrak F}s_{\mathcal N}(P,Q)\le U(\varepsilon).
\tag{13.2}
$$

因而经典历史精确返回类满足 $F_{\rm ret}(\varepsilon)\le U(\varepsilon)$。这是必要的非锐上界，不是混合酉实现判据或可达前沿。

证明。先只为证明上界作 (5.6) 的 $U\otimes U$ Haar 平均。平均通道 $\widetilde{\mathcal N}$ 仍为 CPTP 且保单位；由 (5.7) 及其稳定子证明，

$$
s_{\widetilde{\mathcal N}}(P,Q)=\bar s_{\mathcal N}
 \ge\inf_{\mathfrak F}s_{\mathcal N},\qquad
D(\widetilde{\mathcal N})=\delta=\bar\ell_{\mathcal N}
 \le D(\mathcal N)\le\varepsilon.
\tag{13.3}
$$

所以只需对协变保单位通道的恒定分数证明界。这里不要求平均后的通道保留任何已实现的返回合同，也不由这个解析积分供应实际 Haar 采样器。

对平均通道使用定理 6.2 的全部正块，仍记 $X=\sum_r|x_r|^2$、$v_r=(y_r,z_r,w_r)^{\mathsf T}$ 和 (6.8) 的 $\mathsf Q$。由 (6.9)、(6.10) 及 (12.5)，

$$
\begin{aligned}
\delta&=\delta_{\mathbf1}+\delta_{\mathbf8}+\delta_{\rm rest},
 &\delta_\alpha&\ge0,\\
\delta_{\mathbf8}&=\sum_rv_r^\dagger\mathsf Qv_r,
 &s&=X+s_{\rm rest}\le X+\frac{20}{7}\delta_{\rm rest},\\
X-\frac38&\le\operatorname{Re}\sum_r\overline{x_r}h^\dagger v_r,
 &h&=(1/4,0,-3/4)^{\mathsf T}.
\end{aligned}
\tag{13.4}
$$

保单位性现在增加一个原上界中没有使用的限制。由 $\Delta_{\mathbf1}=0$、(12.2)、(12.5) 及总缺陷为零，

$$
\left|\operatorname{Re}\sum_r\overline{x_r}(z_r-w_r)\right|
 \le\sum_r|y_r|\,|z_r-w_r|+\frac57\delta_{\rm rest}.
\tag{13.5}
$$

对于任意复 $y,z,w$，三角不等式及两次 $2ab\le a^2+b^2$ 给出

$$
|y|\,|z-w|\le |y|(|z|+|w|)
 \le |y|^2+\frac{|z|^2+|w|^2}{2}
 \le\|(y,z,w)\|^2.
\tag{13.6}
$$

而 $\mathsf Q$ 严格正定，且

$$
\mathsf Q^{-1}=\frac1{21}
 \begin{pmatrix}13&-5&-1\\-5&10&2\\-1&2&13\end{pmatrix},
\qquad \operatorname{Tr}\mathsf Q^{-1}=\frac{12}{7}.
\tag{13.7}
$$

正矩阵的最大本征值不超过其迹，所以 $\|v\|^2\le(12/7)v^\dagger\mathsf Qv$。将其代入 (13.5)，并用各块泄漏非负，得到

$$
\left|\operatorname{Re}\sum_r\overline{x_r}(z_r-w_r)\right|
 \le\frac{12}{7}\delta_{\mathbf8}+\frac57\delta_{\rm rest}
 \le\frac{12}{7}\varepsilon.
\tag{13.8}
$$

令

$$
e=(0,1,-1)^{\mathsf T},\qquad
\lambda=\frac{29}{76},\qquad
h'=h-\lambda e=(1/4,-29/76,-7/19)^{\mathsf T}.
\tag{13.9}
$$

直接乘 (13.7) 可得

$$
(h')^\dagger\mathsf Q^{-1}e=0,\qquad
(h')^\dagger\mathsf Q^{-1}h'=\frac{83}{304}=k,
\qquad \lambda\frac{12}{7}=\frac{87}{133}=c.
\tag{13.10}
$$

把 (13.4) 的 $h$ 分解成 $h'+\lambda e$。在 $\mathsf Q$ 内积中对所有重数指标一起应用复 Cauchy—Schwarz，再使用 (13.8)，得到

$$
\begin{aligned}
X-\frac38
&\le\left|\sum_r\overline{x_r}(h')^\dagger v_r\right|
 +\lambda\left|\operatorname{Re}\sum_r\overline{x_r}e^\dagger v_r\right|\\
&\le\sqrt{kX\delta_{\mathbf8}}+c\varepsilon
 \le\sqrt{kX\varepsilon}+c\varepsilon.
\end{aligned}
\tag{13.11}
$$

置 $z=\sqrt X\ge0$。它满足 $z^2-\sqrt{k\varepsilon}\,z-(3/8+c\varepsilon)\le0$，故

$$
X\le\frac{\left(\sqrt{k\varepsilon}
       +\sqrt{3/2+(k+4c)\varepsilon}\right)^2}{4}.
\tag{13.12}
$$

这里直接解二次不等式，没有把符号未定的 $X-3/8-c\varepsilon$ 平方。再用 (13.4) 的 $s\le X+(20/7)\varepsilon$ 和 $s\le1$，即得 (13.1)—(13.2)。命题 11.2 将全部返回兼容仪器的忽略记录通道包含在这个保单位类中，取上确界得到 $F_{\rm ret}\le U$。证毕。

## 14. 与无返回约束首项的严格分离

**推论 14.1（经典精确返回的首项损失）。** 经典历史返回类满足

$$
\limsup_{\varepsilon\downarrow0}
 \frac{F_{\rm ret}(\varepsilon)-3/8}{\sqrt\varepsilon}
 \le\sqrt{\frac{249}{2432}}
 <\sqrt{\frac{17}{112}}.
\tag{14.1}
$$

因此不可能以满足 (11.2) 的一族仪器达到定理 5.3 的无返回约束最优首项。此结论不确定 $F_{\rm ret}$ 的首项是否存在或取等。

证明。令 $B(\varepsilon)$ 为 (13.1) 中截断到一以前的根式上界。因 $B(0)=3/8<1$，零点邻域内 $U=B$。在 $q=\sqrt\varepsilon$ 中展开通常的正根号，得到

$$
U(\varepsilon)=\frac38+
 \sqrt{\frac{3k}{8}}\sqrt\varepsilon
 +\left(\frac{k}{2}+c+\frac{20}{7}\right)\varepsilon
 +O(\varepsilon^{3/2})
 =\frac38+\sqrt{\frac{249}{2432}}\sqrt\varepsilon
 +\frac{15525}{4256}\varepsilon+O(\varepsilon^{3/2}).
\tag{14.2}
$$

定理 13.1 给出 $F_{\rm ret}\le U$，例 11.3 给出相同零点值，故有 (14.1) 的非严格部分。两个正首项系数的平方差为

$$
\frac{17}{112}-\frac{249}{2432}=\frac{841}{17024}>0.
\tag{14.3}
$$

其值分别约为 $0.3895968612$ 和 $0.3199763560$；严格比较由有理数 (14.3) 承担。定理 5.3 已证明前者是原无返回约束 $F$ 的首项，故两类在足够小正预算下严格分离。没有把非锐有限误差上界的一次项指认为最优返回系数。证毕。

## 15. 已有正参数通道族的非保单位见证

**推论 15.1（整个正参数区间都不容经典精确返回）。** 对定义 8.1 的同一通道族，全部 $0<t\le1/1000$ 满足

$$
\mathcal N_t(I_9)-I_9=a(t)(I_9-3S),\qquad
a(t)=\frac{3t(1-16t)(1-95t)(29+869t)}{4f(t)}>0.
\tag{15.1}
$$

所以任何以 $\mathcal N_t$ 为忽略记录通道、仅保留 $AB$ 和有限或可数经典历史的仪器，都不存在满足 (11.2) 的 CPTP 校正。这覆盖任意经典结果细化、一般 CP 分支和任意后续校正，强于只检查 $\mathcal N_t^2$ 是否恒等。

证明。该族只有伴随块，(8.3) 已给全代数保迹。把 $x=A(t)^{-1/2}$、$y=u_tA(t)^{-1/2}$、$z=v_tA(t)^{-1/2}$、$w=w_tA(t)^{-1/2}$ 代入 (12.2)，得到缺陷系数

$$
a(t)=\frac{2(1-u_t)(v_t-w_t)}{A(t)},\qquad
v_t-w_t=\frac{t(29+869t)}{1-95t}.
\tag{15.2}
$$

使用 (8.3) 的 $A(t)=8f(t)/(3(1-95t)^2)$ 即化成 (15.1)。在所述正区间，$1-16t\ge984/1000>0$、$1-95t\ge905/1000>0$、$29+869t>0$，且复用 (8.7)，

$$
f(t)\ge\frac{24246927}{31250000}>0.
\tag{15.3}
$$

故 $a(t)>0$；$I_9-3S\ne0$，所以通道不保单位。若有任意上述仪器及校正，命题 11.2 将迫使同一个 $\mathcal N_t$ 保单位，矛盾。$t=0$ 的缺陷为零，且已有例 11.3 的返回校准；它没有被排除。这里新增的是既有通道族的返回障碍应用，不把有理通道构造或成熟校正判据再计为新成果。证毕。

## 16. 完整第一步输出的目标效应后果

**推论 16.1（同一原输入上的完整输出距离）。** 对每个满足 (11.1)—(11.2)、$D(\mathcal N)\le\varepsilon$ 的仪器，存在一个原承诺对 $(P,Q)\in\mathfrak F$，使它的实际完整第一步输出 $\Xi=\mathcal M(P\otimes Q)$ 与每个满足 $\operatorname{Tr}_{\mathsf C}\Omega=P\otimes R$ 的理想归一化联合输出 $\Omega$ 均满足

$$
\frac12\|\Xi-\Omega\|_1
 \ge\max\{0,1-U(\varepsilon)\}.
\tag{16.1}
$$

同一个承诺对对全部这些理想历史输出同时有效；不要求它们具有相同的经典标签分布。

证明。忽略记录后的 $\mathcal N$ 是有限维通道，所以 $s_{\mathcal N}(P,Q)$ 在紧集 $\mathfrak F$ 上连续并取得最小值。由命题 11.2 和定理 13.1，选取最小值点使 $s_{\mathcal N}(P,Q)\le U(\varepsilon)$。在完整输出上使用有界效应

$$
E_{P,Q}=(P\otimes R)\otimes I_{\mathsf C},\qquad
\operatorname{Tr}(E_{P,Q}\Xi)=s_{\mathcal N}(P,Q),\qquad
\operatorname{Tr}(E_{P,Q}\Omega)=1.
\tag{16.2}
$$

迹距离的效应变分界给 $\|\Xi-\Omega\|_1/2\ge1-s_{\mathcal N}(P,Q)\ge1-U(\varepsilon)$，再与非负性合并。可数经典输出仍是迹类态，$E_{P,Q}$ 是范数一的块对角效应，同一迹对偶界适用。也可先对历史作部分迹，再用迹距离在该通道下不增加得到同一结论。这个单个效应已约束完整输出，不把小第一边缘扰动误读成小联合恢复误差；目标重叠仍不是带成功标志的精确制备概率。证毕。

## 17. 原消费者、成熟工具与未决桥

**应用 17.1（同原 $\tau^2$ 返回腿的必要条件）。** 在定义 1.1—1.3 的完整实际接口下，定理 13.1、推论 14.1、15.1 和 16.1 都针对同一个未知 $\mathrm E_2(p,q)$ 及同一个 $\mathrm E_2(\tau(p,q))$ 目标。若一次候选 $\tau$ 仪器后还要求仅凭其 $AB$ 和经典历史精确恢复原工作寄存器，则必须满足这些限制。证明只用定义 1.2 的双向原关联对应，把 $P,Q,R$ 沿同一个 $\Phi$ 解释；原态、效应、单位和目标均未更换。

这样的任意 CPTP 返回已比第二次固定 $\tau$ 更宽，故推论 15.1 排除相应经典返回路线。但 (11.2) 不等于原完整操作返回，定理 13.1 也只利用它的必要保单位后果。保单位通道一般不都是混合酉，[Gregoratti—Werner，§II.3.1][CRGW] 已明确给出这一边界；本卷不由保单位性断言存在可执行的校正，也不声称 $U$ 锐、可取等，或已求得正误差的 $F_{\rm ret}$。

执行一次 $\tau$ 再执行返回，具有两个实际干预、其中间输出、记录及费用。即使最终 $AB$ 精确相等，也没有把这些记录和资源变成空字的历史。先在纸面约简关联字、只执行端点，不能供应被省略的中间 body、在线回应或切口取得。当前没有构造一套在实际非承诺输出及记录条件化未来上共同定义的物理 $\sigma,\tau$，使 $\tau^2$、$\sigma^2$、$(\sigma\tau)^3$ 连同所有中间输出和完整返回语义成立。应用 4.1 已有的 $\mathrm E_3$ 寄存器置换有限字作用继续成立；它使用已供给的第三样本，不能作为这个 $\mathrm E_2$ 缺口的免费解法。

本障碍只针对精确返回。近似返回误差与扰动、历史之间的定量折衷尚未证明。若另保留可访问的相干量子环境，命题 11.2 的同维分支论证不再适用；本结果没有排除这种模型。那时须实际给出该环境的准备、维数、保存、访问、逆控制、校准和全部费用，Stinespring 等式本身不供应这些能力或当前权限。有限或可数经典历史以外的结果模型也未包含在本定理中。

**原任务边界。** 原来源的合法域、守卫、接受与执行后拒绝、全部回应和记录、谱系、当前授权、控制、backing、原终止消费者及 Handback／Stop／INITIAL、AA／ACK／token／吸收 halt 和下一入口语义仍按应用 4.1、定理 10.1 保留。四份独立实际取得、所选完整收到的 body 驱动同一 owed consumer、全部实际流量与同次运行的费用向量及同时峰值，都未由矩阵返回合同供应。采样、标签保存和通信、门、辅助系统、设备、程序、验证与返回的实际费用不能以数学可逆性删除。Quantum116 的 $\sigma,\tau$ 与 Fibonacci 的 $\alpha,\beta$ 没有因本结果取得来源或操作认同，也没有得到总资源优势或全局最简关系结论。

已有 [ATOMIC_SUPPLIER_SUBSTITUTION II，定理 65.3、70.2、75.4][CRJR] 在增广 $J_r$ 的完整真实入口、封闭 writer／输入、门、当前权限、各请求切口的独立 wake、材料和进展前提下，已经条件性证明全部声明切口、每个有限有序请求森林及原 owed-action 返回；这些结论继续复用，不重新归为全未决。未增广或物理来源、更细 primitive 内部、广泛实际 $\alpha/\beta$ 到原消费者的桥及全局最小性仍有各自义务。该卷所引 GENERAL15.5／18.4、RG13.3 的既有受限 cross-entry／inherited original-Q 结果也保持原范围，不能笼统说全部 cross-entry 核都未解。这里没有推进其外的 changed／new-row Q、较广 mixed interiors 或 full terminal-task kernel。

静态几何、单位费用连续性、共同正方向和有限份复合的条件结果仍只在各自前提下使用；本返回界不支付实际产品准备、一般 completion-added 态的同时准备、未付的 $3+3$ 产品、同族仪器或物理时间合同。第一步的一个量子必要障碍不结算更广的原来源互恢复目标。

**文献与内容归属。** 定理 2.1 的承诺刚性、定理 5.2 的群平均、定理 6.2 的全部复重数、定理 7.1—7.2 的泄漏谱与剩余块估计、定理 5.3 的无返回首项和定义 8.1 的有理族都是本卷既有供应。Choi 正性、Schur 分解、Cauchy—Schwarz、迹距离效应界与同维 CPTP 左逆结构均是成熟工具。经典辅助整输入校正应归于 [Gregoratti—Werner，命题 2、§II.3.1][CRGW]，同维左逆结构直接取 [Nayak—Sen，定理 2.1][CRNS]；仓内 [MINIMAL_RECORD_DILATIONS，定理 2.2、假设 2.3][CRMR] 已在另一固定源上应用前者，并保留实际测量、反馈和逆控制条件。

本卷新增的数学关系是：在相同 $\mathrm E_2/\tau$ 目标下，用 (12.2) 的保单位缺陷约束原伴随相干，结合全部剩余扇区取得 (13.1) 的统一界及 (14.1) 的严格首项分离；(15.1) 是既有族的具体不返回后果，(16.1) 是同一目标效应给出的完整输出后果。它们是 repository-new 的源内综合推导，不把成熟判据、零扰动校准或已有通道改名作为新意。这里给出普通数学证明，不宣称 Lean／kernel 核验、物理实现认证或全球原创；全球文献优先性未验证。

[CRGW]: https://arxiv.org/html/quant-ph/0209025v1 "Matteo Gregoratti and Reinhard F. Werner, Quantum Lost and Found；Proposition 2、§II.3.1：经典环境辅助的整量子信息校正、缩放等距、同维混合酉，以及保单位一般不充分。"
[CRNS]: https://arxiv.org/html/quant-ph/0605041v4 "Ashwin Nayak and Pranab Sen, Invertible Quantum Operations and Perfect Encryption of Quantum States；Theorem 2.1：有 CPTP 左逆的有限维 CPTP 映射结构，输入输出同维时为酉共轭。"
[CRMR]: RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md "Theorem 2.2、Assumption 2.3：指定五模式源上的经典反馈整输入／参考恢复及实际资源条件。"
[CRJR]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_SUPPLIER_SUBSTITUTION_II.md "Theorems 65.3、70.2、75.4：增广 Jr 的源内完整重建、全部有限有序森林／owed-action 返回与更大任务边界。"

## 追加锚（本行以下为增补区）

## 18. 同原双误差经典返回合同

**定义 18.1（第一步与返回腿的两个预算）。** 完整保留定义 1.1—1.2 的 $\mathsf Q_1$、同锥同单位 $\Phi$、全部原纯点与效应及原关联的双向对应，并使用假设 1.3 实际供给的同一个未知 $\mathrm E_2(p,q)=P_A\otimes Q_B$。矩阵输入域仍是全部复正交秩一对 $\mathfrak F$，$R=I-P-Q$，第一步指定目标仍是 $P_A\otimes R_B=\mathrm E_2(\tau(p,q))$。以下不改变第一步的 $D(\mathcal N)$、$s_{\mathcal N}$ 或允许的过程类。

取定义 11.1 的实际有限或可数经典仪器 $\mathcal M=(\mathcal M_c)_{c\in\mathsf C}$，其中每个 $\mathcal M_c$ 是一般 CP 分支，$\mathcal N=\sum_c\mathcal M_c$ 在整个九维矩阵代数上 CPTP。第一步完整输出仍是 $\bigoplus_c\mathcal M_c(\rho)$。返回只读取这个实际 $c$ 和保留的 $AB$，对每个 $c$ 使用一张固定、与未知准备无关的 CPTP 校正 $\mathcal D_c:AB\to AB$。置

$$
\begin{aligned}
\mathcal T&=\sum_c\mathcal D_c\circ\mathcal M_c,\\
E(\mathcal M,\mathcal D)&=\sup_{(P,Q)\in\mathfrak F}
 \frac12\|\mathcal T(P\otimes Q)-P\otimes Q\|_1,\\
F_{\rm ret}(\varepsilon,\eta)&=\sup\left\{
 \inf_{\mathfrak F}s_{\mathcal N}(P,Q):
 D(\mathcal N)\le\varepsilon,\ E(\mathcal M,\mathcal D)\le\eta\right\},
 \qquad 0\le\varepsilon,\eta\le1.
\end{aligned}
\tag{18.1}
$$

上确界遍历上述同一仪器和校正，不预设取到；$\mathcal N$ 与 $\mathcal T$ 必须来自同一次仪器，不能分别挑选。全部成功、失败和拒绝分支均包含在和中，不条件归一或后选择；每个结果可包含完整实际经典历史。可数和采用 (11.1) 的迹范数可加性。没有额外未知样本、旗标描述、依赖准备的程序或保存输入信息的可访问相干环境。新辅助态和控制只允许与准备无关，并保留其实际供给及费用条件。

由定义，$F_{\rm ret}(\varepsilon,0)$ 恰为 (11.3) 的 $F_{\rm ret}(\varepsilon)$。即使 $\eta=0$，这个合同也只返回工作寄存器；$\eta>0$ 是辅助的近似问题，不满足原精确返回承诺。

为区分寄存器与保留记录的误差，另记

$$
\begin{aligned}
p_c(\rho)&=\operatorname{Tr}\mathcal M_c(\rho),\qquad
\mathcal T^\sharp(\rho)=\bigoplus_c\mathcal D_c\mathcal M_c(\rho),\\
E_{\rm CQ}(\mathcal M,\mathcal D)&=
 \sup_{\rho=P\otimes Q,\ (P,Q)\in\mathfrak F}
 \frac12\sum_c\|\mathcal D_c\mathcal M_c(\rho)-p_c(\rho)\rho\|_1.
\end{aligned}
\tag{18.2}
$$

这里比较的理想记录具有同一个实际概率 $p_c(\rho)$；它不是删除记录，也不是原控制器、档案或权限的返回合同。$E$ 评价 $\mathcal T^\sharp$ 丢弃记录后的 $AB$。

**约定 18.2（范数、Choi 与保真度）。** $\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$，$\|X\|_{\rm op}$ 是算子范数；所有态距离均带 $1/2$。沿用 (6.1) 的未归一化 Choi 约定：对任意九维 CPTP 通道 $\mathcal T$，

$$
\begin{aligned}
|I_9\rangle\!\rangle&=\sum_{j=1}^9|j,j\rangle,
&\langle\!\langle I_9|I_9\rangle\!\rangle&=9,\\
\Pi_I&=|I_9\rangle\!\rangle\langle\!\langle I_9|/9,
&\operatorname{Tr}J_{\mathcal T}&=9,\\
F_e(\mathcal T)&=\frac{\operatorname{Tr}(J_{\mathcal T}\Pi_I)}9
 =\frac{\langle\!\langle I_9|J_{\mathcal T}|I_9\rangle\!\rangle}{81},
&u(\mathcal N)&=\frac12\|\mathcal N(I_9/9)-I_9/9\|_1.
\end{aligned}
\tag{18.3}
$$

$F_e$ 是归一化最大纠缠态与其通道输出的重叠，即平方的纠缠保真度，不是根保真度。态之间的根保真度记为

$$
f_{\rm r}(\rho,\sigma)=\operatorname{Tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho}.
\tag{18.4}
$$

$F_e$ 与第一步的 $s_{\mathcal N}$ 是不同量。Choi 参考系统和以下 Haar 平均仅用于证明，不要求实际供给纠缠探针、参考系统或连续结果仪器。

## 19. 承诺泄漏提升与必要近似保单位性

**定理 19.1（同一实际经典返回的定量障碍）。** 对定义 18.1 的每个仪器和校正，不要求协变性，均有

$$
\begin{aligned}
1-F_e(\mathcal T)&\le
 \min\left\{1,\frac{80}{21}E(\mathcal M,\mathcal D)\right\},\\
u(\mathcal N)^2&\le1-F_e(\mathcal T)
 \le\frac{80}{21}E(\mathcal M,\mathcal D).
\end{aligned}
\tag{19.1}
$$

因此 $E\le\eta$ 必须满足

$$
u(\mathcal N)\le r(\eta),\qquad
r(\eta)=\sqrt{\min\{1,80\eta/21\}}.
\tag{19.2}
$$

常数不声称锐；这不是从近似保单位性构造校正的充分判据。

证明。先把原承诺上的联合返回误差提升到过程重叠。令 $\mathscr L_A=\mathscr D$ 为 (7.1) 的原泄漏算子，令 $W=S_{AB}\otimes S_{CD}$，并置

$$
\mathscr L_B=W\mathscr L_AW^\dagger
 =\int I_A\otimes(I-Q)_B\otimes\bar P_C\otimes\bar Q_D\,d(P,Q).
\tag{19.3}
$$

第二个等号使用同一归一化复 Haar 旗标分布在 $(P,Q)\mapsto(Q,P)$ 下不变。这两个算子没有除以九。由定理 7.1 的完整谱，置 $g=7/120$，有

$$
\mathscr L_A\succeq g(I-\Pi_A),\qquad
\mathscr L_B\succeq g(I-\Pi_B),
\tag{19.4}
$$

其中 $\Pi_A$ 投影到向量化的 $I_A\otimes\operatorname{End}(H_B)$，$\Pi_B$ 投影到 $\operatorname{End}(H_A)\otimes I_B$。将因子重排为 $AC,BD$，它们明确为

$$
\Pi_A=\frac{|\Omega_3\rangle\langle\Omega_3|_{AC}}3\otimes I_{BD},
\qquad
\Pi_B=I_{AC}\otimes\frac{|\Omega_3\rangle\langle\Omega_3|_{BD}}3,
\qquad |\Omega_3\rangle=\sum_{j=0}^2|j,j\rangle.
\tag{19.5}
$$

故两投影对易，交为 $\Pi_A\Pi_B=\Pi_I$。特别地，

$$
2I-\Pi_A-\Pi_B-(I-\Pi_I)
 =(I-\Pi_A)(I-\Pi_B)\succeq0,
\qquad
\mathscr L_A+\mathscr L_B\succeq g(I-\Pi_I).
\tag{19.6}
$$

对每个原输入 $\rho=P\otimes Q$，两个输出效应 $(I-P)\otimes I$ 和 $I\otimes(I-Q)$ 在 $\rho$ 上期望均为零，在 $\mathcal T(\rho)$ 上的期望各自不超过 $\|\mathcal T(\rho)-\rho\|_1/2\le E$。用 (6.2) 平均，再以 $J_{\mathcal T}\succeq0$ 测试 (19.6)，得到

$$
9g(1-F_e(\mathcal T))
 =g\operatorname{Tr}[J_{\mathcal T}(I-\Pi_I)]
 \le\operatorname{Tr}[J_{\mathcal T}(\mathscr L_A+\mathscr L_B)]
 \le2E.
\tag{19.7}
$$

由于 $9g=21/40$，得到第一个界；$0\le F_e\le1$ 给出截断。假设仍只在全部原正交产品上，不预置全输入或带参考的准确性。

接着使用成熟经典反馈不等式，但保持实际粗记录。对每个九维 CP 分支取有限 Kraus 族 $K_{ca}$，对其实际校正取有限 Kraus 族 $R_{cb}$。于是

$$
F_e(\mathcal T)=\frac1{81}\sum_{c,a,b}
 |\operatorname{Tr}(R_{cb}K_{ca})|^2.
\tag{19.8}
$$

对每个 $K_{ca}=U_{ca}H_{ca}$，$H_{ca}=|K_{ca}|\succeq0$，将方阵的极分解部分等距延伸为酉 $U_{ca}$。以下是 [Gregoratti—Werner，§IV.A 命题 4，式 (17)—(21)][ARRGW04] 的逐算子 Hilbert—Schmidt Cauchy—Schwarz 步骤；同一结果亦见其 [《Quantum Lost and Found》§V 命题 8，式 (15)—(21)][ARRGW02]：

$$
\begin{aligned}
\sum_b|\operatorname{Tr}(R_{cb}U_{ca}H_{ca})|^2
&\le(\operatorname{Tr}H_{ca})
 \sum_b\operatorname{Tr}\!\left[
 H_{ca}^{1/2}U_{ca}^\dagger R_{cb}^\dagger R_{cb}U_{ca}H_{ca}^{1/2}\right]\\
&=(\operatorname{Tr}H_{ca})^2.
\end{aligned}
\tag{19.9}
$$

最后一步只用 $\sum_bR_{cb}^\dagger R_{cb}=I$。同一个 $\mathcal D_c$ 作用于每个隐藏 $a$；$a$ 不是新取得的记录。由 $\sum_{c,a}\operatorname{Tr}K_{ca}^\dagger K_{ca}=9$ 和 $(\operatorname{Tr}H)^2\le9\operatorname{Tr}H^2$，

$$
F_e(\mathcal T)\le\mathcal A:=\frac1{81}
 \sum_{c,a}(\operatorname{Tr}|K_{ca}|)^2\le1.
\tag{19.10}
$$

不对粗记录主张上界可达，也不由代数 Kraus 细化授予环境测量权限。

忽略零 $K_\alpha$，其中 $\alpha=(c,a)$，并置

$$
q_\alpha=\frac{\operatorname{Tr}K_\alpha^\dagger K_\alpha}{9},
\qquad
\sigma_\alpha=\frac{K_\alpha K_\alpha^\dagger}{9q_\alpha}.
\tag{19.11}
$$

这些是数学权重和归一化态，满足 $\sum_\alpha q_\alpha=1$、$\mathcal N(I_9/9)=\sum_\alpha q_\alpha\sigma_\alpha$，且

$$
f_{\rm r}(\sigma_\alpha,I_9/9)^2
 =\frac{(\operatorname{Tr}|K_\alpha|)^2}{81q_\alpha},
\qquad
\sum_\alpha q_\alpha f_{\rm r}(\sigma_\alpha,I_9/9)^2=\mathcal A.
\tag{19.12}
$$

这里根保真度恰好平方一次。对归一化态使用 [Fuchs—van de Graaf，命题 4 式 (24)、定理 1 式 (46)][ARRFVG] 的成熟不等式，再用迹范数凸性和加权 Cauchy—Schwarz，得到

$$
\begin{aligned}
u(\mathcal N)
&\le\sum_\alpha q_\alpha\frac12\|\sigma_\alpha-I_9/9\|_1\\
&\le\sum_\alpha q_\alpha\sqrt{1-f_{\rm r}(\sigma_\alpha,I_9/9)^2}
 \le\sqrt{1-\mathcal A}\le\sqrt{1-F_e(\mathcal T)}.
\end{aligned}
\tag{19.13}
$$

这给出 (19.1)。$u\le1$ 因两端都是态，故有 (19.2)。

可数情形中，每个分支及校正仍只有有限个 Kraus 算子，其并集可数。正输入分支和按合同在迹范数中收敛；保迹校正不改变每项的正迹，故校正和亦收敛。$J_{\mathcal T}$ 的正项和总迹为九，故也在迹范数中收敛。(19.8)—(19.12) 的标量和均非负，$\sum q_\alpha=1$；先对有限部分和应用 Cauchy—Schwarz，再取单调极限即可得到 (19.13)。没有把有限维反馈定理直接套到无限维记录空间，也没有使隐藏 Kraus 标签可观察。证毕。

## 20. 两个误差共同约束原目标分数

**定理 20.1（全复、全扇区的近似返回上界）。** 令

$$
\begin{aligned}
k&=\frac{83}{304},\qquad c=\frac{87}{133},\qquad
\beta=\frac{87}{608},\\
B(\varepsilon,\eta)&=\frac{20}{7}\varepsilon+
 \frac{\left(\sqrt{k\varepsilon}+
 \sqrt{3/2+(k+4c)\varepsilon+(87/152)r(\eta)}\right)^2}{4}.
\end{aligned}
\tag{20.1}
$$

则定义 18.1 的整个类满足

$$
F_{\rm ret}(\varepsilon,\eta)
 \le\min\{F(\varepsilon),1,B(\varepsilon,\eta)\}.
\tag{20.2}
$$

可用 (5.10) 的显式右端 $B_{\rm free}(\varepsilon)$ 代替 $F(\varepsilon)$，得到完全显式的 $\min\{B_{\rm free}(\varepsilon),B(\varepsilon,\eta)\}$。这是必要非锐上界。

证明。任取同一个可行 $\mathcal M,\mathcal D$，先由定理 19.1 得 $u(\mathcal N)\le r(\eta)$。仅对忽略记录通道作 (5.6) 的解析 $U\otimes U$ 平均。由 (5.7)、(13.3)，其恒定分数至少为原最坏分数，扰动不超过 $\varepsilon$。又因 $\mathcal N(I_9)-I_9$ 在平均中作酉共轭，迹范数凸性给出

$$
u(\widetilde{\mathcal N})\le u(\mathcal N)\le r(\eta).
\tag{20.3}
$$

这里不构造平均后的返回仪器，不把 Haar 积分当成实际连续记录。

协变性使 $\widetilde{\mathcal N}(I_9)-I_9$ 属于 $I_9,S$ 的实线性包，保迹性使其迹为零。因此存在实数 $a$，使

$$
\widetilde{\mathcal N}(I_9)-I_9=a(I_9-3S),
\qquad u(\widetilde{\mathcal N})=\frac43|a|,
\qquad |a|\le\frac34r(\eta).
\tag{20.4}
$$

第二式来自 $S=+1,-1$ 的重数为六、三，故 $I_9-3S$ 的本征值为 $-2,4$，迹范数为 $24$；这里 $u$ 的分母为 $18$。

保留 (6.5) 的所有正块、全部复重数及整体保迹。使用 (13.4) 的 $X,v_r,\delta_{\mathbf8},\delta_{\rm rest}$，令

$$
D_x=\operatorname{Re}\sum_r\overline{x_r}(z_r-w_r),
\qquad Y=\operatorname{Re}\sum_r\overline{y_r}(z_r-w_r).
\tag{20.5}
$$

由 (12.2)、(12.5) 及标量块缺陷为零，总缺陷恒等式为

$$
a=2(D_x-Y)+a_{\rm rest}.
\tag{20.6}
$$

于是复用 (13.6)—(13.7) 的 $|y||z-w|\le\|v\|^2\le(12/7)v^\dagger\mathsf Qv$，得到

$$
\begin{aligned}
|D_x|&\le\sum_r|y_r||z_r-w_r|
       +\frac12|a_{\rm rest}|+\frac12|a|\\
&\le\frac{12}{7}\delta_{\mathbf8}
       +\frac57\delta_{\rm rest}+\frac38r(\eta)
 \le\frac{12}{7}\varepsilon+\frac38r(\eta).
\end{aligned}
\tag{20.7}
$$

这里剩余扇区的缺陷没有删去；标量泄漏亦非负，故 $\delta_{\mathbf8}+\delta_{\rm rest}\le\varepsilon$。

继续直接使用 (13.9)—(13.10) 的

$$
e=(0,1,-1)^{\mathsf T},\qquad
\lambda=\frac{29}{76},\qquad h'=h-\lambda e,
\qquad (h')^\dagger\mathsf Q^{-1}h'=k.
\tag{20.8}
$$

由 (13.4) 的总迹估计，对所有复重数指标一起作 $\mathsf Q$ 内积的 Cauchy—Schwarz，得到

$$
\begin{aligned}
X-\frac38
&\le\left|\sum_r\overline{x_r}(h')^\dagger v_r\right|+\lambda|D_x|\\
&\le\sqrt{kX\delta_{\mathbf8}}+
 \lambda\left(\frac{12}{7}\varepsilon+\frac38r(\eta)\right)\\
&\le\sqrt{kX\varepsilon}+c\varepsilon+\beta r(\eta),
\qquad s\le X+\frac{20}{7}\varepsilon.
\end{aligned}
\tag{20.9}
$$

常数对应为 $\lambda(12/7)=c$、$\lambda(3/8)=\beta$。令 $z=\sqrt X\ge0$，直接解

$$
z^2-\sqrt{k\varepsilon}\,z-\left(\frac38+c\varepsilon+\beta r(\eta)\right)\le0.
\tag{20.10}
$$

其正根给出 (20.1)，判别式中的 $4\beta=87/152$。整个推导不对符号未定的表达式平方。原最坏分数不超过这个平均分数，故逐仪器得到 $B$；另有同一第一步的 $F(\varepsilon)$ 和一的独立上界，取上确界即得 (20.2)。证毕。

## 21. 精确端点、小误差尺度与完整第一步输出

**推论 21.1（原精确界的延续及严格首项分离）。** 定义 18.1 满足

$$
\begin{aligned}
F_{\rm ret}(\varepsilon,0)&=F_{\rm ret}(\varepsilon),\qquad
\min\{1,B(\varepsilon,0)\}=U(\varepsilon),\\
F_{\rm ret}(0,\eta)&=\frac38,\qquad
F_{\rm ret}(\varepsilon,\eta)\ge\frac38.
\end{aligned}
\tag{21.1}
$$

若 $\eta(\varepsilon)=o(\varepsilon)$，则

$$
\limsup_{\varepsilon\downarrow0}
 \frac{F_{\rm ret}(\varepsilon,\eta(\varepsilon))-3/8}{\sqrt\varepsilon}
 \le\sqrt{\frac{249}{2432}}
 <\sqrt{\frac{17}{112}}.
\tag{21.2}
$$

这是上界，不断言返回类存在首项极限、取到该系数或已经求出最优前沿。

证明。第一行直接比较 (18.1)、(11.3)、(20.1)、(13.1)。例 11.3 的实际 Weyl 端点在所有非负预算下仍可行，而 $F_{\rm ret}(0,\eta)\le F(0)=3/8$，得到第二行。对于同时趋零的 $\varepsilon,\eta$，把正根式写成

$$
\begin{aligned}
B(\varepsilon,\eta)
={}&\frac38+\beta r(\eta)
 +\left(c+\frac{k}{2}+\frac{20}{7}\right)\varepsilon\\
&+\frac{\sqrt{k\varepsilon}}2
 \sqrt{3/2+(k+4c)\varepsilon+4\beta r(\eta)}\\
={}&\frac38+\sqrt{\frac{249}{2432}}\sqrt\varepsilon
 +\beta r(\eta)+O\!\left(\varepsilon+\sqrt\varepsilon\,r(\eta)\right).
\end{aligned}
\tag{21.3}
$$

第二个等号用根号在严格正数 $3/2$ 附近的有界导数，且 $3k/8=249/2432$。当 $\eta=o(\varepsilon)$ 时，$r(\eta)=o(\sqrt\varepsilon)$；代入定理 20.1 即得 (21.2)。两个正系数的平方差仍为 (14.3) 的 $841/17024>0$。条件 $\eta=o(\varepsilon)$ 在这里是充分条件，没有断言必要或最优。证毕。

**推论 21.2（近似返回仪器的完整第一步距离）。** 记

$$
B_{\rm all}(\varepsilon,\eta)
 =\min\{B_{\rm free}(\varepsilon),B(\varepsilon,\eta)\}.
\tag{21.4}
$$

每个定义 18.1 的可行实际仪器都有一个原承诺对 $(P,Q)$，使第一步完整输出 $\Xi=\mathcal M(P\otimes Q)$ 对每个满足 $\operatorname{Tr}_{\mathsf C}\Omega=P\otimes R$ 的理想归一化联合输出同时满足

$$
\frac12\|\Xi-\Omega\|_1\ge
 \max\{0,1-B_{\rm all}(\varepsilon,\eta)\}.
\tag{21.5}
$$

证明。有限维 $\mathcal N$ 的连续分数在紧 $\mathfrak F$ 上取得最小值；定理 20.1 的逐仪器界及 (5.10) 使该值不超过 $B_{\rm all}$。在这个固定最小点，(16.2) 的同一个效应 $(P\otimes R)\otimes I_{\mathsf C}$ 在所有这些 $\Omega$ 上期望为一，在 $\Xi$ 上期望为 $s_{\mathcal N}(P,Q)$。迹距离效应界给出 (21.5)；可数经典输出是迹类直和，范数一的块对角效应仍适用。这个结论涉及第一步，不能用返回后的 $AB$ 误差替代。证毕。

## 22. 未改通道族的双边返回误差与实际 Weyl 仪器

**定理 22.1（同一 $\mathcal N_t$ 上的匹配阶）。** 保留定义 8.1 的整个有理通道族，不改变其 $\varepsilon(t)$、$s(t)$ 或输入、目标。令 $e_*(t)$ 为在全部允许的有限或可数经典仪器及其允许校正中、忽略记录通道恰为 $\mathcal N_t$ 时的 $E$ 的下确界。对 $0<t\le1/1000$，

$$
\frac7{15}a(t)^2\le e_*(t)\le\chi(t)
 :=\frac{t^2(67-2741t)^2}{f(t)}
 \le\min\left\{\frac92\varepsilon(t),12800t^2\right\},
\tag{22.1}
$$

其中 $a(t)$ 为 (15.1) 的同一个正缺陷系数。下界覆盖每个实际 CP 仪器及任意允许校正，不要求隐藏 Kraus 标签可访问；上界由下述指定的实际八结果 Weyl 仪器及其极分解校正达到一个不超过该界的误差，不对所有实现主张充分性。特别地，

$$
e_*(t)=\Theta(t^2)=\Theta(\varepsilon(t))\quad(t\downarrow0),
\qquad
\frac{(7/15)a(t)^2}{\varepsilon(t)}\longrightarrow\frac{841}{4080}.
\tag{22.2}
$$

最后的比值仅属于已证下界，不是最优返回系数。

证明。首先，由 (15.1) 和 $\|I_9-3S\|_1=24$，$u(\mathcal N_t)=4a(t)/3$。定理 19.1 对同一个 $\mathcal N_t$ 的每个实际仪器和校正给出

$$
E(\mathcal M,\mathcal D)\ge\frac{21}{80}u(\mathcal N_t)^2
 =\frac7{15}a(t)^2.
\tag{22.3}
$$

$a(t)>0$ 的整个区间及正分母已由 (15.1)—(15.3) 证明，不需更换正参数族。

为给出充分构造，明确指定实际结果 $j=(a,b)\in(\mathbb Z/3\mathbb Z)^2\setminus\{(0,0)\}$。使用 (3.5) 的固定 qutrit Weyl $W_j=X^aZ^b$，取 $T_j=W_j/\sqrt3$，将它们代入原 (8.2) 的 $L_j(t),K_j(t)$，实际仪器是

$$
\mathcal M_j^{\rm W}(Y)=K_j(t)YK_j(t)^\dagger,
\qquad j\text{ 是实际保留的八值记录}.
\tag{22.4}
$$

这些 $T_j$ 无迹且 Hilbert—Schmidt 正交归一。若另一个原定义所用基为 $T'_j=\sum_kV_{jk}T_k$，$V$ 酉，则四个 $E_i$ 的线性性给出 $K'_j=\sum_kV_{jk}K_k$，而

$$
\sum_jK'_jYK_j'^\dagger=\sum_kK_kYK_k^\dagger.
\tag{22.5}
$$

所以忽略记录后恰是同一个已发表 $\mathcal N_t$。但是逐结果 CP 分支、记录及可用反馈可随基改变；(22.5) 不是重配一套固定装置的授权，不使每个实现都具有本构造的校正。

下面直接估计最坏迹距离，不从平均保真度推断它。记

$$
d_t=1-95t,\qquad r_t=\frac1{\sqrt{3A(t)}},\qquad
b_t=|u_t|+|v_t|+|w_t|.
\tag{22.6}
$$

此处 $r_t$ 与 (19.2) 的 $r(\eta)$ 不同。原公式给出 $d_t\ge905/1000$，$u_t\ge0$、$v_t\le0$、$w_t\le0$，因此

$$
b_t=27t+\frac{40t-176t^2}{d_t}
 =\frac{t(67-2741t)}{d_t}
 \le\frac{67}{905}<1.
\tag{22.7}
$$

每个 $W_j$ 和 $S$ 都酉，故由四个 $E_i$ 的算子范数，

$$
\|K_j(t)-r_t(I\otimes W_j)\|_{\rm op}\le r_tb_t.
\tag{22.8}
$$

对任意单位向量应用三角不等式及其反向式，所有奇异值均在 $[r_t(1-b_t),r_t(1+b_t)]$ 内。由于 $A(t)>0$、$b_t<1$，每个 $K_j(t)$ 可逆，其极分解

$$
K_j(t)=U_j(t)H_j(t),\qquad H_j(t)=|K_j(t)|
\tag{22.9}
$$

具有同一九维空间上的酉 $U_j(t)$，并有

$$
\|H_j(t)-r_tI_9\|_{\rm op}\le r_tb_t.
\tag{22.10}
$$

选择实际记录条件化校正

$$
\mathcal D_j^{\rm pol}(Y)=U_j(t)^\dagger YU_j(t),\qquad
\mathcal T_{\rm pol}(Y)=\sum_jH_j(t)YH_j(t).
\tag{22.11}
$$

该成熟极分解反馈见 [ARRGW04，式 (19)—(20)][ARRGW04]；固定 $t$ 后所有控制均与未知 $P,Q$ 无关。正参数时结果概率无需均匀或与输入无关。

由原全代数保迹性 $\sum_jH_j^2=I_9$，对任意矩阵 $Y$ 有精确恒等式

$$
\mathcal T_{\rm pol}(Y)-Y
 =-\frac12\sum_j[H_j,[H_j,Y]]
 =-\frac12\sum_j[Z_j,[Z_j,Y]],
\quad Z_j=H_j-r_tI_9.
\tag{22.12}
$$

事实上，展开双重交换子并使用 $\sum_jH_j^2=I_9$ 即得第一个等号，减去标量不改变交换子给出第二个。对任意态 $\rho$，由 $\|AXB\|_1\le\|A\|_{\rm op}\|X\|_1\|B\|_{\rm op}$，

$$
\|[Z,[Z,\rho]]\|_1
 =\|Z^2\rho-2Z\rho Z+\rho Z^2\|_1
 \le4\|Z\|_{\rm op}^2.
\tag{22.13}
$$

于是 (22.10)—(22.13) 统一给出

$$
\begin{aligned}
\frac12\|\mathcal T_{\rm pol}(\rho)-\rho\|_1
&\le\sum_{j=1}^8\|Z_j\|_{\rm op}^2
 \le8r_t^2b_t^2\\
&=\frac8{3A(t)}\frac{t^2(67-2741t)^2}{d_t^2}
 =\frac{t^2(67-2741t)^2}{f(t)}=\chi(t).
\end{aligned}
\tag{22.14}
$$

最后一步只代入原 $A(t)=8f(t)/(3d_t^2)$。这个估计对全部九维态成立，因而包括整个复承诺族；不假定校正后通道协变。

为得到区间上的显式比较，使用 (9.3)、(8.7) 及 $67-2741t>0$：

$$
\begin{aligned}
\frac{\chi(t)}{\varepsilon(t)}
 &=\frac{(67-2741t)^2}{9(119-3584t+178545t^2)}\\
 &\le\frac{4489}{9(119-3584/1000)}
 =\frac{561125}{129843}<\frac92,\\
\frac{\chi(t)}{t^2}
 &\le\frac{4489\cdot31250000}{24246927}<12800.
\end{aligned}
\tag{22.15}
$$

所有分母均严格正。因此 (22.1) 成立。原有理式还给出

$$
a(t)=\frac{87}{4}t+O(t^2),\qquad
\varepsilon(t)=1071t^2+O(t^3),\qquad
\frac{(7/15)(87/4)^2}{1071}=\frac{841}{4080}>0.
\tag{22.16}
$$

这证明 (22.2) 的正下阶；上阶由 (22.14) 或 (22.15) 给出。$t=0$ 时 $K_j(0)=I\otimes W_j/\sqrt8$，校正后为恒等通道，与例 11.3 相同。

记录仍可以完整保留。为给出其准确误差含义，对任意原纯输入 $\rho$，令 $\omega_c=\mathcal D_c\mathcal M_c(\rho)$，$p_c=\operatorname{Tr}\omega_c$。忽略 $p_c=0$ 项，对 $\omega_c/p_c$ 与纯态 $\rho$ 使用 (18.4) 和 Fuchs—van de Graaf，再作加权 Cauchy—Schwarz，得到

$$
\begin{aligned}
\frac12\sum_c\|\omega_c-p_c\rho\|_1
&\le\sum_cp_c\sqrt{1-\operatorname{Tr}(\rho\omega_c)/p_c}\\
&\le\sqrt{1-\operatorname{Tr}(\rho\mathcal T(\rho))}
 \le\sqrt{\frac12\|\mathcal T(\rho)-\rho\|_1}.
\end{aligned}
\tag{22.17}
$$

最后一步是效应 $\rho$ 的变分界。反方向由丢弃记录的迹距离收缩性给出；取上确界即得一般的 $E\le E_{\rm CQ}\le\sqrt E$。因而本指定构造还满足 $E_{\rm CQ}\le\sqrt{\chi(t)}$，但这只给 $O(t)$，不能把 (22.1) 的 $O(t^2)$ 寄存器保证写成完整 CQ 保证或每个归一化稀有分支的保证。可数时同样由非负部分和取极限。

最后，(9.3) 的第一步和分数在校正之前评价，始终未改。定理 9.2 给出严格递增的实际 $\varepsilon(t)$ 及原无返回首项，而 (22.15) 给出一个 $E=O(\varepsilon(t))$ 的真实记录仪器。故“$E\to0$”本身不能推出 (21.2) 的严格首项损失；返回误差相对于第一步扰动的速率有实质作用。这里只给同一族的非锐匹配阶，没有求 $e_*(t)$ 的首项系数、最坏分支最优校正或双误差前沿。证毕。

## 23. 同原持续使用的条件应用与操作边界

**应用 23.1（工作寄存器返回支付的关系）。** 在定义 1.1—1.3 的完整原来源及实际 $\mathrm E_2$ 接口下，定理 19.1—22.1 的对象均沿同一个 $\Phi$ 对应同一个未知原关联和同一个 Quantum116 的 $\tau$ 目标。其必要关系是：原第一步具有的非保单位缺陷，必须由实际经典返回腿支付至少二次的寄存器误差；在未改的 $\mathcal N_t$ 上，这个误差与其第一边缘扰动具有同阶的上下界。定理 22.1 的充分合同具体要求实际供给 (22.4) 的八结果仪器、保留并交付其真实标签，以及固定 $t$ 的 (22.11) 逆控制。它不是仅从忽略记录的 $\mathcal N_t$ 推出的装置无关可恢复性。

证明。定义 1.2 的双向对应恰好覆盖全部 $\mathfrak F$，指定目标仍是 $P\otimes R$；(18.1) 的返回目标仍是同一个 $P\otimes Q$。因此这些定理的全部量词、误差和消费者可在同一原关联上解释，不需要另一个源、额外样本或准备建议。下界对每个实际允许仪器成立，上界明确给出其中一个；它们的共同对象是同一个已发表通道，而不是把两个不同通道的可达性质拼接。

此条件应用只给出了 §17 近似返回问题的上述定量部分。$D(\mathcal N)$、第一步完整输出、$E$ 和 $E_{\rm CQ}$ 具有不同合同，推论 21.2 及 (22.17) 保留其区别。即使最终 $AB$ 精确返回，实际第一步、反馈、记录、流量和所耗资源也没有消失；正 $E$ 更不是原精确承诺的履行。没有由此构造在全部实际非承诺输出和记录条件化未来上共同定义的 $\sigma,\tau$ 操作，也没有给出其有限字的全部中间输出、$\tau^2,\sigma^2,(\sigma\tau)^3$ 及完整返回语义。应用 4.1 的实际 $\mathrm E_3$ 置换合同继续成立，使用的是另已供给的第三样本，不能移作本合同的免费资源。

完整原来源的合法域、原守卫、接受与执行后拒绝、全部回应、记录、控制状态、谱系、backing 和当前 source-bound 权限均保留；原 Handback／Stop／INITIAL、AA／ACK／token／吸收 halt、下一入口和所欠动作语义没有由 $AB$ 接近性恢复。四份独立实际取得的完整 body、INPUT／STACK 分离，以及所选完整收到的 body 实际驱动同一 owed consumer 的返回，仍须各自合法供应。Quantum116 的对合没有被认作 Native／AA／Fibonacci 的实际生成元；同名、可编码性和末态统计不能给出这一桥。

已有 [增广 $J_r$ 的定理 65.3、70.2、75.4][CRJR] 在真实完整入口、封闭 writer／输入、门、当前权限、每个请求切口的独立实际 wake、材料和进展前提下，已给出其全部声明切口、每个有限有序请求森林及原 owed-action 返回。这些条件结果继续使用；本附加合同不重新开放它们已证明的域。未增广或物理来源、更细 primitive 内部及广泛实际 $\alpha/\beta$ 到原消费者的桥仍有各自义务。GENERAL15.5／18.4 和 RG13.3 的既有受限 cross-entry／inherited original-Q 结果亦保留其范围；这里不提供其外的 changed／new-row Q、较广 mixed interiors 或 full terminal-task kernel。

同样，[有限份共同源定理 123.2 及证明（六）][ARRPREFIX] 已给出任意总次数上每个 $\min(a,b)\le2$ 的产品和完整五份前缀；其式 (123.18) 的 $C_3\otimes_{\min}C_3\subseteq C_6$、一般补全新增态的同时准备与实际取得没有被此返回构造支付。固定间隙紧致性仍是存在性关系，不是当前操作权限或实际制备。

上述充分合同还必须供给并计入：实际产品准备、全部正向门及辅助系统、测量、标签存储与通信、反馈与校准、执行记录、保留的两个寄存器、程序与 backing、验证和返回，以及同次运行的全部费用向量和同时峰值。八值末标签可编码为三比特，不等于完整控制器、历史或总存储只有三比特；可数标签的必要界也不给有限熵或统一比特预算。解析 Haar 平均、Kraus 细化与 Choi 参考都不供给这些资源。这里不证明全局最少关系、最少内存、最少样本或总资源优势。证毕。

本附加推导的 repository-new 内容是同一正交对承诺的双边缘泄漏提升、一般实际经典分支下的近似保单位障碍、全复全扇区的双误差目标界，以及未改有理族的双边返回误差估计。定理 7.1 的谱、§12—13 的扇区恒等式、§8—9 的通道与分数和 §15 的缺陷均为既有供应。Gregoratti—Werner 的反馈／极分解工具及 Fuchs—van de Graaf 的根保真度不等式只作为这些新关系的中间步骤；没有将成熟结果另命名为新增数学内容。这里给出普通数学证明，不宣称 Lean／kernel 核验、物理实现认证或全球文献优先性；全球原创性未验证。

[ARRGW04]: https://arxiv.org/pdf/quant-ph/0403092v1 "Matteo Gregoratti and Reinhard F. Werner, On quantum error-correction by classical feedback in discrete time；v1，p.7 末通道保真度定义，§IV.A Single-step channel，Proposition 4，(17)—(21)，p.8；这里只用任意有限维的单步结论，不用 qubit 多步 Proposition 5。"
[ARRGW02]: https://arxiv.org/pdf/quant-ph/0209025v1 "Matteo Gregoratti and Reinhard F. Werner, Quantum Lost and Found；v1，§V，Proposition 8，(15)—(21)，pp.11—12；§II.C.1，Proposition 2，pp.4—5 为既有精确校正边界。"
[ARRFVG]: https://arxiv.org/pdf/quant-ph/9712042v2 "Christopher A. Fuchs and Jeroen van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States；v2，§4.3 Proposition 4，(24)，p.13：根保真度；Theorem 1，(46)，p.17：半迹距离与根保真度平方的界。"
[ARRPREFIX]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "Theorem 123.2，证明（六）—（七），(123.16)—(123.18)：同一共同源的完整五份前缀、任意 min(a,b)<=2 产品，以及第一个未付的 3+3 产品。"

## 追加锚（本行以下为增补区）

## 24. 固定原来源上的环境坐标与占用支撑

本节至 §29 固定定义 8.1 的一个点 $t_\star=1/1000$，记 $\mathcal N_\star=\mathcal N_{t_\star}$。所研究的是这张已经给定的九维通道的扩展与精确返回，不是另选一张具有相同目标分数的通道。原来源解释完整保留定义 1.1—1.3：闭尖生成锥、严格正单位、每个原纯点的完整排除球与原全域效应所满足的 $\mathsf Q_1$，同锥同单位的实线性双射 $\Phi$，以及实际供给的同一个未知 $\mathrm E_2(p,q)=P_A\otimes Q_B$。承诺族仍为

$$
\mathfrak F=\{(P,Q):P,Q\text{ 为 }\mathbb C^3\text{ 上的秩一投影},\ PQ=0\},
\qquad R=I-P-Q.
\tag{24.1}
$$

它覆盖全部有序复正交对，不限制到实向量或固定坐标框架。第一步消费者仍请求 $\mathrm E_2(\tau(p,q))=P_A\otimes R_B$；返回腿请求同一个原输入 $P_A\otimes Q_B$。由 (9.12)，第一步本身的保证仍恰为

$$
D(\mathcal N_\star)=\frac{1040350905}{790405860121}>0,
\qquad
s_{\mathcal N_\star}(P,Q)=\frac{307134375000}{790405860121}>\frac38.
\tag{24.2}
$$

这里的 $s$ 是目标投影重叠，不是精确制得 $P\otimes R$ 的有标志成功概率。以下扩展均须在整个 $M_9(\mathbb C)$ 上具有原 $\mathcal N_\star$ 边缘，包括承诺族以外的矩阵。

**定义 24.1（供整数证书使用的复无迹基）。** 所有矩阵指标从零开始；$E_{ab}$ 是三阶矩阵单位。令

$$
\begin{aligned}
(B_0,\ldots,B_7)
 &=\bigl(E_{01},E_{02},E_{10},E_{12},E_{20},E_{21},
       \operatorname{diag}(1,-1,0),\operatorname{diag}(1,1,-2)\bigr),\\
(g_0,\ldots,g_7)&=(1,1,1,1,1,1,2,6),\qquad
T_i=B_i/\sqrt{g_i}.
\end{aligned}
\tag{24.3}
$$

每个 $T_i$ 无迹，且 $\operatorname{Tr}(T_i^\dagger T_j)=\delta_{ij}$。六个非对角矩阵单位与两个对角无迹矩阵正交，后两者的平方范数分别为二、六，故 (24.3) 是整个八维复无迹矩阵空间的 Hilbert—Schmidt 正交归一基。它不是 Hermitian 基；定义 6.1、8.1 本来就允许这种复基。

在本节以下，$S$ 仍是 $H_A\otimes H_B$ 的交换。由原 (8.1)—(8.3)，参数及归一化的精确值为

$$
u_\star=\frac2{125},\qquad
v_\star=-\frac{11}{1000},\qquad
w_\star=-\frac{4978}{113125},\qquad
A_\star=\frac{790405860121}{307134375000}>0.
\tag{24.4}
$$

置 $q=905000$，定义实整数矩阵

$$
\begin{aligned}
H_i={}&905000(I\otimes B_i)+14480(B_i\otimes I)\\
     &-9955(I\otimes B_i)S-39824(B_i\otimes I)S,\\
K_i&=\frac{H_i}{q\sqrt{A_\star g_i}},\qquad 0\le i<8.
\end{aligned}
\tag{24.5}
$$

因为 $q(1,u_\star,v_\star,w_\star)=(905000,14480,-9955,-39824)$，这里的 $K_i$ 正是将 (24.3) 代入原定义 8.1 得到的 Kraus 算子；未改来源、参数或通道。

**引理 24.2（归一化、最小环境与实际占用）。** 在 (24.5) 的坐标下，

$$
\begin{aligned}
\sum_{i=0}^7\frac{H_i^{\mathsf T}H_i}{g_i}
 &=A_\star q^2 I_9,
& A_\star q^2&=\frac{6323246880968}{3},\\
\operatorname{Tr}(H_i^{\mathsf T}H_j)
 &=\delta_{ij}\frac98 A_\star q^2 g_i,
&\operatorname{Tr}(K_i^\dagger K_j)&=\frac98\delta_{ij}.
\end{aligned}
\tag{24.6}
$$

因此 $\sum_iK_i^\dagger K_i=I_9$，八个 $K_i$ 线性独立。令 $E=\mathbb C^8$，以 $|i\rangle$ 为其标准基，并置

$$
V:H_A\otimes H_B\longrightarrow H_A\otimes H_B\otimes E,
\qquad V\psi=\sum_iK_i\psi\otimes|i\rangle.
\tag{24.7}
$$

则 $V^\dagger V=I_9$，$\operatorname{Tr}_E(VXV^\dagger)=\mathcal N_\star(X)$，且 $E$ 是最小 Kraus 环境。互补通道 $\mathcal N_\star^c(X)=\operatorname{Tr}_{AB}(VXV^\dagger)$ 满足

$$
\mathcal N_\star^c(I_9/9)=I_8/8.
\tag{24.8}
$$

原承诺族的环境输出的共同占用支撑也是整个 $E$，不是添入了未使用坐标的八维空间。

证明。第一条算子恒等式直接是 (8.4)—(8.6) 在 (24.4) 的代入；交换项严格为零。为同时检查 Gram 归一化，用 (6.12) 的完整嵌入 Gram 矩阵 $\mathsf G$，置 $c=(1,u_\star,v_\star,w_\star)^{\mathsf T}$，则

$$
\begin{aligned}
\operatorname{Tr}[L(T)^\dagger L(U)]
 &=(c^{\mathsf T}\mathsf Gc)\operatorname{Tr}(T^\dagger U),\\
c^{\mathsf T}\mathsf Gc
 &=3(1+u_\star^2+v_\star^2+w_\star^2)
      +2(1+u_\star)(v_\star+w_\star)
  =\frac98 A_\star,
\end{aligned}
\tag{24.9}
$$

其中 $L(T)$ 表示原 (8.2) 的同一线性嵌入。把 (24.3)—(24.4) 代入即得 (24.6)；$H_i$ 为实矩阵，故其转置就是伴随。非零对角 Gram 给出 Kraus 独立性和 Choi 秩八，继而给出最小性。互补输出的 $i,j$ 元是 $\operatorname{Tr}(XK_j^\dagger K_i)$，由 (24.6) 得 (24.8)。

还须检查承诺自身确实使用全部环境。由原 (7.11) 的同一 Haar 正交标架平均，或先条件于 $P$ 再用 $\mathbb E[Q\mid P]=(I-P)/2$，有

$$
\bar\rho_{\mathfrak F}
 :=\int P\otimes Q\,d(P,Q)=\frac{3I_9-S}{24}.
\tag{24.10}
$$

其在交换对称、反对称空间的本征值分别为 $1/12,1/6$，所以忠实。完全正性和 (24.8) 给出

$$
\mathcal N_\star^c(\bar\rho_{\mathfrak F})
 \succeq\frac1{12}\mathcal N_\star^c(I_9)
 =\frac3{32}I_8>0.
\tag{24.11}
$$

若一个环境方向对全部承诺输出都为零，它对这个平均也为零，与 (24.11) 矛盾。这个平均仅用于证明支撑，不要求实际供给混合样本、额外副本、连续测量或 Haar 采样器。证毕。

## 25. 六十四个原 Kraus 乘积的整数证书

**定理 25.1（固定点的完整乘积独立性）。** 对 (24.5) 的同一八个 $K_i$，六十四个矩阵

$$
\{K_i^\dagger K_j:0\le i,j<8\}
\tag{25.1}
$$

在 $M_9(\mathbb C)$ 中复线性独立。

证明。以下给出全部整数矩阵、子式行集和非零余数，使结论不依赖浮点秩阈值。按张量顺序 $r=3a+b$、$s=3c+d$，其中 $0\le a,b,c,d<3$，(24.5) 的逐元式是

$$
(H_i)_{3a+b,3c+d}
 =905000\delta_{ac}(B_i)_{bd}
  +14480(B_i)_{ac}\delta_{bd}
  -9955\delta_{ad}(B_i)_{bc}
  -39824(B_i)_{ad}\delta_{bc}.
\tag{25.2}
$$

由它定义一个 $81\times64$ 整数矩阵 $M$：

$$
M_{9r+s,\,8i+j}
 =(H_i^{\mathsf T}H_j)_{r,s}
 =\sum_{k=0}^8(H_i)_{k,r}(H_j)_{k,s},
\qquad 0\le r,s<9,\quad 0\le i,j<8.
\tag{25.3}
$$

所有行、列均按零起始指标递增排列。删去且只删去以下十七行：

$$
\mathcal O=\{12,13,14,27,29,60,61,62,68,69,70,71,74,77,78,79,80\}.
\tag{25.4}
$$

令 $\mathcal R=\{0,\ldots,80\}\setminus\mathcal O$ 按递增顺序排列，$D=M_{\mathcal R,\{0,\ldots,63\}}$。这是完全确定的 $64\times64$ 整数矩阵，其行列式有下列精确余数：

| 模数 $p$ | $\det D\pmod p$ |
| --- | --- |
| $1000003$ | $373375$ |
| $1000033$ | $164048$ |

余数采用 (25.2)—(25.4) 的行列次序，计入行交换的行列式符号。为明确这张有限证书的求值规则，可在各素域 $\mathbb F_p$ 内使用以下消元递推；这里给的是矩阵恒等式的有限求值，不引入额外程序或实验前提。初值 $D^{[0]}=D\bmod p$、$\epsilon=1$；在 $k=0,\ldots,63$，取满足 $r\ge k$ 且 $D^{[k]}_{r,k}\ne0$ 的最小 $r$，交换第 $r,k$ 行，若 $r\ne k$ 则改变 $\epsilon$ 的符号。记交换后的矩阵为 $C$，$z_k=C_{k,k}$，对 $r>k$ 同时作

$$
D^{[k+1]}_{r,s}
 =C_{r,s}-C_{r,k}z_k^{-1}C_{k,s}\quad(s\ge k),
\qquad
D^{[k+1]}_{r,s}=C_{r,s}\quad(r\le k\text{ 或 }s<k).
\tag{25.5}
$$

此处第二式与第一式的定义区域不交叠；每步的上方行保持不变。两个模数下每一步都有非零主元，最后均取 $\epsilon\prod_{k=0}^{63}z_k\bmod p$，所得恰为表中的余数。行相减不改变行列式，换行给出 $\epsilon$，所以递推计算的就是原 $\det D$ 的余数。第一项已经足以推出整数 $\det D\ne0$，第二项是同一整数子式的另一个精确校验。这里使用的模数、矩阵元、行集和余数均为整数数据；不以行列式的数值大小、近似误差或奇异值阈值代替非零性。

因此 $M$ 在整数的分式域及 $\mathbb C$ 上均列满秩。按 (24.5)，从 $H_i^{\mathsf T}H_j$ 到 $K_i^\dagger K_j$ 只将第 $8i+j$ 列乘以

$$
\frac1{q^2A_\star\sqrt{g_i g_j}}\ne0.
\tag{25.6}
$$

可逆的列缩放不改列独立性，得到 (25.1)。证毕。

**推论 25.2（标量原像与环境效应）。** 定义复线性映射

$$
\begin{aligned}
\beta:M_8(\mathbb C)&\longrightarrow M_9(\mathbb C),\\
\beta(Z)&=\sum_{i,j=0}^7Z_{ij}K_i^\dagger K_j
          =V^\dagger(I_9\otimes Z)V.
\end{aligned}
\tag{25.7}
$$

则 $\beta$ 单射，$\beta(I_8)=I_9$，且

$$
\beta^{-1}(\mathbb C I_9)=\mathbb C I_8.
\tag{25.8}
$$

特别地，对环境效应 $0\preceq F\preceq I_8$，

$$
\beta(F)=pI_9
\quad\Longleftrightarrow\quad
F=pI_8,\qquad 0\le p\le1.
\tag{25.9}
$$

证明。定理 25.1 就是 (25.7) 的六十四列独立性。全代数保迹给 $\beta(I_8)=I_9$。若 $\beta(Z)=zI_9$，则 $\beta(Z-zI_8)=0$，单射性给 $Z=zI_8$；反向直接代入。对效应再用序约束，即得 (25.9)。按 (24.7) 的环境坐标，矩阵元是 $\langle i|Z|j\rangle=Z_{ij}$，所以 (25.7) 无须额外转置。其统计意义为

$$
\operatorname{Tr}[F\mathcal N_\star^c(\rho)]
 =\operatorname{Tr}[\rho\beta(F)].
\tag{25.10}
$$

证毕。

六十四个伴随 Kraus 乘积独立也是成熟的 Choi 极端通道判据所用的条件，见 [Watrous，定理 2.31（Choi），(2.174)—(2.175)][RRCCHOI]。因此它还可按该判据识别 $\mathcal N_\star$ 为 CPTP 凸集的极端点。判据和这种一般推论属于既有工具；这里承担后续证明的新源内事实，是 (25.2)—(25.6) 对这张实际 $\mathcal N_\star$ 的具体求值，而不是提出新的极端性或校正判据。

## 26. 任意声明经典分支的全边缘扩展

**定义 26.1（可访问载体、独立准备与精确返回）。** 令 $\mathsf C$ 是非空有限或可数的实际经典结果集。每个 $c$ 可以包含一条完整的有限经典历史及全部可读取经典副本。返回前可访问的相干输出是原 $AB$ 及 $M_c$；$M_c$ 必须合计除 $AB$ 外的每一个保留相干载体，包括量子工作区、相干指针、通信载体和已与输入相关的解码器记忆。不能把这些载体改称控制器、程序或测量附件而漏计。

$M_c$ 允许为非零有限维或可分 Hilbert 空间；有限资源结论针对其中的有限维分支。无限维时使用迹类算子及正常 CP 映射的通常可数 Kraus 表示。实际 CP 分支记为

$$
\Psi_c:M_9(\mathbb C)\longrightarrow
 \mathcal T(H_A\otimes H_B\otimes M_c),\qquad
\Psi(X)=\bigoplus_{c\in\mathsf C}\Psi_c(X),
\tag{26.1}
$$

其中 $\mathcal T$ 表示迹类空间。分支可含任意多个隐藏 Kraus 算子，不能预置为纯分支。规定对每个正输入，分支和按迹范数可数可加，且

$$
\sum_{c\in\mathsf C}\operatorname{Tr}_{M_c}\Psi_c(X)
 =\mathcal N_\star(X)\qquad\text{对每个 }X\in M_9(\mathbb C).
\tag{26.2}
$$

这条全代数边缘等式是合同本身；只在一组观察值、一个平均态或较小的准备集上相等不够。它使 $\Psi$ 保迹。所有成功、失败、拒绝和零概率分支都列入仪器；不选择成功结果再归一。

全部初始辅助准备可为固定的独立混合态，允许独立随机性及固定自适应控制，但不得依赖未知 $(P,Q)$。每个丢弃输出、未保留的相干指针、不可访问的经典副本及不可访问的准备纯化均被迹去，归入 CP 分支的隐藏 Kraus 指标。独立混合态的某个数学纯化不因此成为解码器的输入。没有额外未知样本、源相关建议、旗标描述、输入相关程序、依赖准备的 oracle，也不允许从未触碰的参考系统取回信息。

对每个实际 $c$，返回可用一张固定 CPTP 映射

$$
\mathcal D_c:\mathcal T(H_A\otimes H_B\otimes M_c)
                 \longrightarrow M_9(\mathbb C).
\tag{26.3}
$$

它可以联合处理所列载体、读取 $c$，并使用实际供给的、与准备无关的新辅助态。精确工作寄存器返回要求

$$
\mathcal T_{\rm ret}:=\sum_c\mathcal D_c\Psi_c,
\qquad
\mathcal T_{\rm ret}(P\otimes Q)=P\otimes Q
\quad\text{对每个 }(P,Q)\in\mathfrak F.
\tag{26.4}
$$

这仍只是原完整操作返回的必要放宽。它未要求原记录、控制状态、谱系、backing、权限、所欠动作或全部资源返回。

**定理 26.2（每个扩展都经原占用环境因子化）。** 每个满足 (26.1)—(26.2) 的扩展都有有限或可数算子族 $A_{ca}:E\to M_c$，使

$$
\begin{aligned}
\Lambda_c(Z)&=\sum_aA_{ca}ZA_{ca}^\dagger,
&\Lambda(Z)&=\bigoplus_c\Lambda_c(Z),\\
\sum_{c,a}A_{ca}^\dagger A_{ca}&=I_8,
&\Psi_c(X)&=(\operatorname{id}_{AB}\otimes\Lambda_c)(VXV^\dagger).
\end{aligned}
\tag{26.5}
$$

所以 $\Lambda$ 是从原最小环境 $E$ 到实际声明输出的 CPTP 通道。这是从任意实际 CP 扩展推出的因子化，不是假设实际装置先准备了一个可访问的纯 Stinespring 环境。

证明。取 $\Psi_c$ 的 Kraus 算子 $L_{ca}:\mathbb C^9\to\mathbb C^9\otimes M_c$。在 $M_c$ 的正交归一基 $|m\rangle$ 中展开

$$
L_{ca,m}=(I_9\otimes\langle m|)L_{ca}.
$$

由 (26.2) 及 (6.1) 的向量化，有限维 Choi 矩阵满足

$$
J_{\mathcal N_\star}
 =\sum_{c,a,m}|L_{ca,m}\rangle\!\rangle
                  \langle\!\langle L_{ca,m}|
 =\sum_{i=0}^7|K_i\rangle\!\rangle\langle\!\langle K_i|.
\tag{26.6}
$$

对右侧支撑的任意正交向量，左侧各非负二次型之和为零，故每个分量都与该向量正交。因此

$$
L_{ca,m}\in\operatorname{span}_{\mathbb C}\{K_0,\ldots,K_7\}.
\tag{26.7}
$$

这是通常 Choi 正支撑论证；同一支撑工具亦见 [RRCCHOI，Lemma 2.30 及定理 2.31 的证明][RRCCHOI]。由引理 24.2 的独立性，可唯一写成 $L_{ca,m}=\sum_i a_{ca,mi}K_i$。定义 $A_{ca}|i\rangle=\sum_m a_{ca,mi}|m\rangle$。这些向量确实平方可和，因为

$$
\|L_{ca}\|_{\rm HS}^2
 =\sum_m\|L_{ca,m}\|_{\rm HS}^2
 =\frac98\sum_{m,i}|a_{ca,mi}|^2
 =\frac98\operatorname{Tr}(A_{ca}^\dagger A_{ca}).
\tag{26.8}
$$

故 $A_{ca}$ 是从有限维 $E$ 出发的有界算子，并有

$$
L_{ca}=(I_9\otimes A_{ca})V.
\tag{26.9}
$$

对全部 $c,a$ 求和，由 (26.2) 在 $I_9/9$ 上的总迹为一，得到

$$
1=\sum_{c,a}\frac{\|L_{ca}\|_{\rm HS}^2}{9}
 =\frac18\sum_{c,a}\operatorname{Tr}(A_{ca}^\dagger A_{ca}).
\tag{26.10}
$$

所以正算子和 $G=\sum_{c,a}A_{ca}^\dagger A_{ca}$ 在八维空间上按迹范数收敛。原扩展保迹及 (26.9) 给出

$$
I_9=\sum_{c,a}L_{ca}^\dagger L_{ca}
    =V^\dagger(I_9\otimes G)V=\beta(G).
\tag{26.11}
$$

推论 25.2 于是给 $G=I_8$。将 (26.9) 代回分支 Kraus 和，得到 (26.5)。

可数情形不需将有限维定理直接套到无限历史上。(26.6) 的正项和总迹为九，所以在有限维 Choi 空间按迹范数收敛；(26.8)—(26.10) 又控制环境 Kraus 和的总质量。对正输入，各输出部分和单调且迹有界，故按迹范数收敛；一般输入写成四个正算子的线性组合。

混合准备的吸收也可直接写明。设实际独立辅助态为 $\eta=\sum_\ell h_\ell|\ell\rangle\langle\ell|$，$h_\ell\ge0$、$\sum_\ell h_\ell=1$；将第 $c$ 分支在包括其余丢弃输出的空间 $F$ 上写成固定线性扩张 $W_c$，则

$$
\Psi_c(X)=\operatorname{Tr}_F[W_c(X\otimes\eta)W_c^\dagger],
\qquad
L_{c,\ell f}=\sqrt{h_\ell}
 (I_{ABM_c}\otimes\langle f|)W_c(I_9\otimes|\ell\rangle).
$$

这里 $|f\rangle$ 遍历 $F$ 的正交归一基；实际多步控制及不可访问副本均可包含在这个 CP 扩张中。因而独立混合准备的谱指标、不可访问纯化和其他丢弃输出，只增加隐藏 Kraus 指标。证明所用的 $a,m$ 是分解坐标，未把它们另行测出或交付给返回操作；$\mathcal D_c$ 仍只读取原来可访问的 $AB,M_c,c$。证毕。

## 27. 精确原承诺返回等价于完整环境可逆性

**定理 27.1（同源返回的环境判据）。** 对定义 26.1 的任意扩展，取定理 26.2 的实际环境通道 $\Lambda$。以下三条件等价：

1. 存在 (26.3) 的标签条件化 CPTP 返回，使 (26.4) 对整个原复承诺族成立。
2. $\Lambda$ 在整个 $M_8(\mathbb C)$ 上有 CPTP 左逆。
3. 每个实际经典分支的所有隐藏误差乘积均为标量，即存在标量矩阵 $\lambda_c=(\lambda_{c,ab})$，使

$$
A_{ca}^\dagger A_{cb}=\lambda_{c,ab}I_8
\quad\text{对全部 }c,a,b.
\tag{27.1}
$$

若成立，原返回通道必为整个 $M_9(\mathbb C)$ 上的恒等映射；还有 $p_c\ge0$、$\sum_cp_c=1$，使每个分支的返回恰为 $\mathcal D_c\Psi_c(X)=p_cX$。条件 (27.1) 是全空间 Knill—Laflamme 条件，不只是每个分支效应之和为标量。

证明。先证条件一推出条件三。$\mathcal T_{\rm ret}$ 是有限维输入输出的 CPTP 通道，即使中间载体和经典标签可数亦然。精确返回使它满足原 (1.1) 的第一边缘保持。复用定理 2.1，得到整个代数上的

$$
\mathcal T_{\rm ret}=\operatorname{id}_A\otimes\mathcal L_B
\tag{27.2}
$$

及某张 qutrit CPTP 通道 $\mathcal L$。任意秩一 $Q$ 都可配一个正交秩一 $P$，由 (26.4) 得 $\mathcal L(Q)=Q$。秩一投影张成 Hermitian 空间，再复线性延拓，得 $\mathcal L=\operatorname{id}$，所以

$$
\mathcal T_{\rm ret}=\operatorname{id}_{M_9}.
\tag{27.3}
$$

这正是命题 11.2 已有的承诺到恒等映射的归约，不假定正交产品投影本身张成 $M_9$。所应用定理 2.1 的对象是返回复合 $\mathcal T_{\rm ret}$；由 (24.2)，有正扰动的第一步 $\mathcal N_\star$ 并不满足 (1.1)，不能把它代入该刚性定理。

取返回 $\mathcal D_c$ 的 Kraus 算子 $B_{cu}:\mathbb C^9\otimes M_c\to\mathbb C^9$。恒等通道的 Choi 矩阵秩一，故 (27.3) 给出

$$
\sum_{c,u,a}|B_{cu}L_{ca}\rangle\!\rangle
                   \langle\!\langle B_{cu}L_{ca}|
 =|I_9\rangle\!\rangle\langle\!\langle I_9|,
\qquad
B_{cu}L_{ca}=r_{cua}I_9.
\tag{27.4}
$$

每一项的标量性来自正项的秩一支撑，不预先假设实际分支是等距或单 Kraus。仓内 [KrausLeftInverseNecessity 的 identity_kraus_scalar、left_inverse_error_products][RRCKRAUS] 给出了相应有限 Kraus 代数事实；这里还显式处理一般 CP 表示和可数和，不由读取这些源码冒领新的 Lean 核验。

返回保迹，$\sum_uB_{cu}^\dagger B_{cu}=I$，故对同一 $c$ 的任意 $a,b$，

$$
\begin{aligned}
L_{ca}^\dagger L_{cb}
 &=\sum_u(B_{cu}L_{ca})^\dagger(B_{cu}L_{cb})\\
 &=\left(\sum_u\overline{r_{cua}}r_{cub}\right)I_9
  =\lambda_{c,ab}I_9.
\end{aligned}
\tag{27.5}
$$

再由 (26.9) 及推论 25.2，

$$
\beta(A_{ca}^\dagger A_{cb})=\lambda_{c,ab}I_9
\quad\Longrightarrow\quad
A_{ca}^\dagger A_{cb}=\lambda_{c,ab}I_8.
\tag{27.6}
$$

这一步用到了具体整数证书：一般的保迹性、Kraus 秩八或能够保留整个环境，都不能代替此处的标量原像结论。

记 $\iota_c:M_c\to\bigoplus_dM_d$ 为包含映射。环境通道的 Kraus 算子是 $E_{ca}=\iota_cA_{ca}$，故其完整误差条件为

$$
E_{ca}^\dagger E_{db}
 =\begin{cases}
   \lambda_{c,ab}I_8,&c=d,\\
   0,&c\ne d.
  \end{cases}
\tag{27.7}
$$

经典块之间的零乘积与同块的全部交叉项同样保留。(27.7) 正是 [Knill—Laflamme，定理 3.2，(19)—(20)][RRCKL] 在整个 $E$ 作码空间时的条件。

为完整给出条件三推出条件二的恢复，也明确其可数版本，先固定 $c$。由 (27.1)，

$$
\lambda_{c,ab}=\frac18\operatorname{Tr}(A_{ca}^\dagger A_{cb}),
\qquad
\lambda_c\succeq0,
\qquad
p_c:=\operatorname{Tr}\lambda_c=\sum_a\lambda_{c,aa},
\qquad
\sum_cp_c=1.
\tag{27.8}
$$

正性来自任意有限系数族 $z_a$ 的

$$
\sum_{a,b}\bar z_a\lambda_{c,ab}z_b
 =\frac18\operatorname{Tr}\left[
   \left(\sum_a z_aA_{ca}\right)^\dagger
   \left(\sum_b z_bA_{cb}\right)\right]\ge0.
$$

若指标可数，(26.10) 使其成为迹类正 Gram 算子。有限维酉对角化，或这个迹类正算子的谱分解，给出一个包含零本征空间的正交归一基变换 $U_c$，使 $U_c^\dagger\lambda_cU_c$ 对角。令

$$
C_{c\mu}=\sum_a(U_c)_{a\mu}A_{ca}.
$$

酉性给出 $\sum_\mu(U_c)_{a\mu}\overline{(U_c)_{b\mu}}=\delta_{ab}$，故 Kraus 和仍为同一 CP 分支；而 (27.1) 给出新 Kraus 乘积正是该对角 Gram 的相应元素乘以 $I_8$。去掉零本征值后，得到

$$
\Lambda_c(Z)=\sum_\mu C_{c\mu}ZC_{c\mu}^\dagger,
\qquad
C_{c\mu}^\dagger C_{c\nu}
 =s_{c\mu}\delta_{\mu\nu}I_8,
\qquad s_{c\mu}>0,\quad\sum_\mu s_{c\mu}=p_c.
\tag{27.9}
$$

零本征值所给的零 Kraus 算子已去掉。可数混合在 Hilbert—Schmidt 范数下收敛，因为 $\sum_a\|A_{ca}\|_{\rm HS}^2=8p_c$。置 $W_{c\mu}=C_{c\mu}/\sqrt{s_{c\mu}}$，则

$$
W_{c\mu}^\dagger W_{c\nu}=\delta_{\mu\nu}I_8,
\qquad
\Pi_c=\sum_\mu W_{c\mu}W_{c\mu}^\dagger\preceq I_{M_c}.
\tag{27.10}
$$

这些等距映射的像两两正交，故 $\Pi_c$ 为投影；可数时是强收敛的正交投影和。任选固定八维密度矩阵 $\omega_8$，定义

$$
\mathcal R_c(Y)
 =\sum_\mu W_{c\mu}^\dagger YW_{c\mu}
   +\operatorname{Tr}[(I_{M_c}-\Pi_c)Y]\omega_8.
\tag{27.11}
$$

这是 CPTP 映射：各项完全正，第一项的迹是 $\operatorname{Tr}(\Pi_cY)$，补项补足总迹。若 $p_c=0$，则全部 $A_{ca}=0$，可直接取 $\mathcal R_c(Y)=\operatorname{Tr}(Y)\omega_8$。由 (27.9)—(27.10)，对所有 $Z$ 有

$$
\mathcal R_c\Lambda_c(Z)=p_cZ.
\tag{27.12}
$$

因此 $\mathcal R(\bigoplus_cY_c)=\sum_c\mathcal R_c(Y_c)$ 是 CPTP，且 $\mathcal R\Lambda=\operatorname{id}_{M_8}$。这是标准 Knill—Laflamme 恢复的全空间写法；等距像外补一个固定态以使操作保迹，也与 [Gregoratti—Werner，命题 2 及 (7)][CRGW] 相同。

最后证条件二推出条件一。复用等距嵌入的通常左逆：任选固定九维密度矩阵 $\omega_9$，令

$$
\mathcal R_V(Y)=V^\dagger YV
    +\operatorname{Tr}[(I_{72}-VV^\dagger)Y]\omega_9.
\tag{27.13}
$$

它是 CPTP，且 $\mathcal R_V(VXV^\dagger)=X$。将环境左逆限制于第 $c$ 块得 CPTP 的 $\mathcal R|_c$，并取

$$
\mathcal D_c
 =\mathcal R_V\circ(\operatorname{id}_{AB}\otimes\mathcal R|_c).
\tag{27.14}
$$

由 (26.5) 和 $\mathcal R\Lambda=\operatorname{id}$，其总返回为恒等。这证明数学存在性的充分方向；实际执行还须提供 (27.14) 的访问及控制。对于 (27.11) 给出的左逆，(27.12) 直接给 $\mathcal D_c\Psi_c=p_c\operatorname{id}$。任意其他满足条件一的实际返回也有相同结论：由 (27.4) 对固定 $c$ 求和，得到正数倍恒等通道，返回保迹再将这个数识别为 (27.8) 的 $p_c$。

以上所有可数和都有明确收敛依据。原返回在正输入上不改变各项的迹，故其和在迹范数中收敛；(27.4) 的 Choi 正项和总迹为九。由其对角项，$\sum_u|r_{cua}|^2<\infty$，于是 (27.5) 的交叉标量和由 Cauchy—Schwarz 绝对收敛；返回保迹的强算子和夹在有限秩 $L_{ca}^\dagger,L_{cb}$ 之间，给出所写等式。(27.9)—(27.12) 的正项由 $\sum s_{c\mu}=p_c$ 控制；对任意正迹类输入的恢复和亦由总迹控制。故不需要无限维历史上的有限维逆定理，也没有遗漏零分支或只恢复一个后选择结果。证毕。

## 28. 同源相干载体下界、经典记录限制与匹配上界

**推论 28.1（每个非零分支至少保留八维相干侧载体）。** 在定义 26.1 的合同下，若精确返回存在，则每个非零实际经典分支 $c$ 都满足

$$
\dim M_c\ge8.
\tag{28.1}
$$

特别地，即使经典结果任意多、允许任意细化历史，也不能以经典标签代替这八维相干侧载体。维数计数排除原九维 $AB$，只计该分支中其余所有保留相干载体的联合空间。

证明。若 $\Psi_c\ne0$，(26.8)—(26.10) 蕴含至少一个 $A_{ca}\ne0$。由定理 27.1，

$$
A_{ca}^\dagger A_{ca}=\lambda_{c,aa}I_8,
\qquad
\lambda_{c,aa}=\|A_{ca}\|_{\rm HS}^2/8>0.
\tag{28.2}
$$

所以 $A_{ca}$ 的秩为八，其像包含在 $M_c$，得到 (28.1)。若整个分支的 $p_c=0$，则各 $A_{ca}=0$、各 $L_{ca}=0$、$\Psi_c=0$；零分支是在证明其为零后才不受维数要求。对每个非零有限维分支，这是一条八维的有限资源下界；无限维分支也不会提供更小的有限载体。证明并未将各分支的资源平均后再取下界。证毕。

**推论 28.2（实际环境读出的效应必须为标量）。** 若精确返回存在，则每个实际分支的环境效应及概率为

$$
F_c:=\Lambda_c^*(I_{M_c})=\sum_aA_{ca}^\dagger A_{ca}
     =p_cI_8,
\qquad
\operatorname{Tr}\Psi_c(\rho)=p_c
\tag{28.3}
$$

对每个九维归一化输入均成立；$\sum_cp_c=1$。返回后保留的经典标签可以具有状态 $\bigoplus_cp_c\rho$，这只说明标签与返回的工作寄存器独立，不等于原历史消失或原控制器复位。

证明。(28.3) 由 (27.1)、(27.8) 求对角和得到；也可将 $\operatorname{Tr}\Psi_c(\rho)=\operatorname{Tr}[\rho\beta(F_c)]$ 与逐分支返回 $p_c\rho$ 合并，再用 (25.9)。因此对占用环境实施不可逆经典读出时，任一非标量效应都与本合同的精确返回不相容。这里限制的是实际 CP 扩展对应的效应，不是任意重命名的潜在环境结果。证毕。

**例 28.3（标量效应不是充分条件）。** 只擦除环境的单分支通道

$$
\Lambda(Z)=\operatorname{Tr}(Z)|0\rangle\langle0|,
\qquad M=\mathbb C,
\qquad A_i=|0\rangle\langle i|\quad(0\le i<8)
\tag{28.4}
$$

具有效应 $\sum_iA_i^\dagger A_i=I_8$，故分支概率完全独立于输入。然而 $A_i^\dagger A_j=|i\rangle\langle j|$ 不满足完整标量乘积条件，$\Lambda$ 也把所有归一化环境态送到同一态，故没有左逆。其扩展只给 $\mathcal N_\star$ 及一个固定侧态，不能精确返回。即使把这个固定态嵌入八维 $M$，仍然不可逆；单独达到维数八也不是给定仪器的充分校正检验。

**命题 28.4（已测 Weyl 分支不等于相干上界）。** 保留 (22.4) 的实际八结果 Weyl 仪器，而非只保留其忽略记录的通道。其环境坐标中的每个分支效应为秩一投影，故该实际仪器不容许本节的精确返回。另一方面，保留整个八维相干环境给出同一 $\mathcal N_\star$ 的匹配数学上界。

证明。在 Weyl Kraus 坐标下令 $V_{\rm W}=\sum_jK_j^{\rm W}\otimes|j\rangle$。(22.4) 正是对环境作 $|j\rangle\langle j|$ 读出后的实际 $AB$ 分支。若允许给这些既定 $AB$ 分支附加任意声明侧输出，则定理 26.2 给出的对应效应仍须满足

$$
\beta_{\rm W}(F_j)=(K_j^{\rm W})^\dagger K_j^{\rm W}
                  =\beta_{\rm W}(|j\rangle\langle j|).
\tag{28.5}
$$

(24.3) 的基与 Weyl 基之间的酉变换只酉共轭环境坐标，因而保持乘积独立性、$\beta$ 的单射性及效应的秩；由 (28.5)，$F_j=|j\rangle\langle j|$。它在全部占用的 $\mathbb C^8$ 上非标量，与 (28.3) 矛盾。因此不能在保持这些实际测量结果和 CP 分支的同时，把装置追认成一套可精确返回的相干仪器。这与 §22 已有的非零近似返回保证相容。

匹配上界直接复用完整 Kraus 环境的标准等距扩展：取单个经典结果，$M=E$、$\Lambda=\operatorname{id}_{M_8}$，则

$$
\Psi(X)=VXV^\dagger,
\qquad
\operatorname{Tr}_M\Psi(X)=\mathcal N_\star(X),
\qquad
\mathcal R_V\Psi(X)=X.
\tag{28.6}
$$

$\dim M=8$，(27.13) 给出固定 CPTP 左逆。这是等距嵌入已有的恢复事实，亦是 [Gregoratti—Werner，(7)][CRGW] 的单等距情形；八维全环境保留及其逆是复用的上界见证，不是新的通用反演构造。有限维等距还可延伸为在已给纯辅助态上的酉操作，但这种数学延伸不供应任何实际门。

因此八维只在定义 26.1 的数学扩展类中尖锐：下界由本源的 (25.1) 经 (27.6) 得到，上界由 (28.6) 达到。忽略记录后通道相同，不使 (22.4) 与 (28.6) 成为同一实际仪器；把已经不可逆记录的标签改写为相干控制会改变合同。证毕。

## 29. 原消费者的使用范围、归属与未付接口

**应用 29.1（同一个原返回腿的资源必要条件）。** 在定义 1.1—1.3 的完整 $\mathsf Q_1/\Phi/\mathrm E_2$ 解释与定义 26.1 的全部扩展、访问和准备合同下，对同一未知原关联先使用 $\mathcal N_\star$，再要求精确恢复 $\mathrm E_2(p,q)$，当且仅当相应的整个占用环境处理 $\Lambda$ 可逆；每个非零有限维实际分支都须保留至少八维的联合相干侧载体。八维在该数学扩展类中可达。

证明。原关联与 (24.1) 的全部复正交对双向对应，第一步及返回目标没有换源或换消费者，故定理 26.2—27.1 和推论 28.1 直接适用。所需的首次全 $M_9$ 边缘仍是原通道，而 (24.2) 的分数和扰动仍在返回之前评价。所说“当且仅当”是 CPTP 操作的数学存在性，不把逆操作的实际供给包含在结论中。证毕。

精确总返回是全 $M_9$ 恒等，因此在张量上也保持任意未触碰参考系统及其相关；这来自 (27.3)，没有把该参考系统交给解码器。模型也未隐藏额外未知样本、源相关建议或相干侧载体。若另给这样的输入，就不再是定义 26.1 的扩展类。与准备无关的新辅助态可供解码器使用，但已与未知输入相关的任何保留量子载体都必须计入 $M_c$，不能在下界之外免费加入。

(28.6) 恢复的是原 $P\otimes Q$，不是在保留另一份独立的期望 $P\otimes R$ 的同时返回未知原输入。第一步 $\mathcal N_\star(P\otimes Q)$ 原本就只具有 (24.2) 的目标重叠，并非该精确目标产品。若还要求独立目标副本、逐次回应、验证结果或另一个未返回载体，必须声明相应输出和合法供给；本结果没有构造这种更强任务。

维数八计的是每个实际分支中除 $AB$ 和经典结果以外的联合相干侧空间。它不等于总内存、控制器大小、熵、保留历史长度、物理存储、初始准备资源、关系总数或其他来源上的内存最小值。它不提供总资源优势，也不以有限或可数标签的存在推出有限熵、统一比特预算或无限次使用的统一有限费用。[MINIMAL_RECORD_DILATIONS][CRMR] 的五模式源及其指定运输和读出任务不同，不能把该源的最小值搬到本源。

数学上存在逆映射及八维上界，不供应实际相干保存、门、测量、通信、访问、逆控制、校准、当前授权、复位或资源费用。一般混合环境实现的可校正性仍依赖实际耦合，正如 [Gregoratti—Werner，§VI Mixed Environments][RRCCOUPLING] 所强调的；定理 26.2 吸收独立混合准备和不可访问纯化，是为了必要性没有漏洞，不是任意给定混合装置的充分恢复方案。实际实现须逐项供给并计入同次运行的产品准备、所有辅助系统和保留载体、正向与逆向门、完整记录、标签存储与交付、反馈、程序与 backing、验证、通信、返回与复位，以及全部费用向量和同时峰值。一般相位综合、QSP 或区间 SOS 的数学结果，未给出到本源 $V$、$\mathcal R_c$、$\mathcal R_V$ 的精确操作映射时，不构成这里的实际逆控制。

工作寄存器恒等仍只是原完整操作返回的必要放宽。实际发生的第一步、环境处理、读取、反馈与资源消耗没有随末态相等而消失；原合法域、守卫、接受与执行后拒绝、全部回应和记录、控制状态、来源身份与谱系、backing、当前权限、所欠动作、Handback／Stop／INITIAL、AA／ACK／token／吸收 halt 及下一入口仍各自保留。四份独立实际取得的完整 body、INPUT／STACK 的分离，以及选中完整收到的 body 驱动同一原消费者的返回，没有由一条 $AB$ 恒等式获得。这里的返回不构造一般非承诺输出上共同定义的物理 $\sigma,\tau$，也不供应其全部有限字的中间输出、关系恒等式和完整返回。

已有 [增广 $J_r$ 的定理 65.3、70.2、75.4][CRJR] 在真实完整入口、封闭 writer／输入、门、当前权限、每个请求切口的独立实际 wake、材料与进展前提下，已经证明全部声明切口、每个有限有序请求森林和原 owed-action 返回。这些条件域继续作为已解决结果复用。未增广或物理来源、更细 primitive 内部，以及广泛实际 $\alpha/\beta$ 到 Native／AA／Fibonacci 原消费者的桥，仍须各自供应，不能把量子对合按名称认同为其生成元。GENERAL15.5／18.4、RG13.3 已有的受限 cross-entry／inherited original-Q 结论也保留原范围；本节没有扩展到其外的 changed／new-row Q、较广 mixed interiors 或完整 terminal-task kernel。§23 所保留的共同源准备、首个未付 $3+3$ 产品、一般 completion-added 态的同时准备与实际取得、同族仪器及物理时间合同，均未由本资源定理支付。

本附加结果只认证 $t_\star=1/1000$。不从一个非零子式推广参数分类，不给其他 $t$ 的资源结论，不给连续结果仪器、近似相干资源折衷、源相关初始化、物理实现、全局最小性或完整持续互恢复目标的完成结论。§18—23 的经典近似返回及 §15 的经典精确障碍继续在其原范围成立；这里增加的是固定点上更强的相干扩展限制。

**文献与内容归属。** 定理 2.1 的原复承诺刚性、命题 11.2 的精确返回归约、§6 的复无迹嵌入、§8 的全代数通道、§9 的原消费者分数与 §15、§18—23 的经典返回结果均直接复用。Choi 正支撑、秩一恒等通道的 Kraus 标量性、Choi 极端性、Knill—Laflamme 标量误差乘积条件、等距像外补项和 CPTP 左逆结构是成熟工具；分别见 [RRCCHOI][RRCCHOI]、[RRCKRAUS][RRCKRAUS]、[RRCKL][RRCKL]、[CRGW][CRGW] 和 [Nayak—Sen，定理 2.1][CRNS]。Nayak—Sen 的固定、可为混合态的独立辅助态正规形与 (27.9)—(27.11) 一致，但不替代任意实际 CP 扩展的 (26.6)—(26.11) 或本源的整数证书。

这里新增的源内承重关系是：在未改的 $\mathcal N_{1/1000}$ 上具体证明全部六十四个乘积独立，确定完整标量原像，再将任何声明的精确原承诺返回传递为全部八维占用环境的可逆性和逐非零分支的相干维数下界。完整环境的逆及其八维上界仅作复用见证。正文给出普通数学证明和精确有限整数证据，不宣称 Lean／kernel 核验、构建或 CI 认证。与既有源内结果和所引文献的区别不等于全球优先性；全球原创性未认证。

[RRCCHOI]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf "John Watrous, The Theory of Quantum Information，Chapter 2，Lemma 2.30、Theorem 2.31 (Choi)，(2.174)—(2.175)：正支撑与伴随 Kraus 乘积独立的极端通道判据。"
[RRCKL]: https://arxiv.org/html/quant-ph/9604034 "Emanuel Knill and Raymond Laflamme, A Theory of Quantum Error-Correcting Codes，Theorem 3.2，(19)—(20)：码上标量误差乘积条件及恢复。"
[RRCKRAUS]: ../../../D5/S3/Quantum/Recovery/KrausLeftInverseNecessity.lean "identity_kraus_scalar、left_inverse_error_products：有限 Kraus 恒等通道标量性及左逆的误差乘积必要条件；源码引用不表示本附加结果已形式化。"
[RRCCOUPLING]: https://arxiv.org/html/quant-ph/0209025 "Matteo Gregoratti and Reinhard F. Werner, Quantum Lost and Found，§II.3.1 Proposition 2、(7)，§VI Mixed Environments：条件等距分支逆及混合环境的实际耦合边界。"

## 追加锚（本行以下为增补区）

## 30. 同原承诺返回误差与加权相干侧维数

**定义 30.1（完整扩展合同下的有限误差）。** 固定原定义 8.1、§24 的同一通道 $\mathcal N_\star=\mathcal N_{1/1000}$，并完整保留定义 1.1—1.3 的 $\mathsf Q_1/\Phi/\mathrm E_2$ 来源、全部原纯点和效应、独立产品准备及全部有序复正交秩一对 $\mathfrak F$。第一步的指定消费者目标仍为 $P\otimes(I-P-Q)$，返回目标仍为同一个未知原输入 $\rho=P\otimes Q$。

使用定义 26.1 的整个扩展与访问类：$\mathsf C$ 是非空有限或可数的实际经典结果集；每个 $M_c$ 是非零有限维或可分 Hilbert 空间。实际正常 CP 分支和固定 CPTP 返回为

$$
\begin{aligned}
\Psi_c &:M_9(\mathbb C)\longrightarrow
                 \mathcal T(\mathbb C^9\otimes M_c),\\
\sum_c\operatorname{Tr}_{M_c}\Psi_c(X)&=\mathcal N_\star(X)
                 \quad\text{对每个 }X\in M_9(\mathbb C),\\
\mathcal D_c&:\mathcal T(\mathbb C^9\otimes M_c)
                 \longrightarrow M_9(\mathbb C),\qquad
\mathcal T=\sum_c\mathcal D_c\Psi_c.
\end{aligned}
\tag{30.1}
$$

正输入的分支和按迹范数可数可加。成功、失败、拒绝及全部稀有分支均留在和中，不后选择或条件归一。实际 $c$ 可包含完整有限历史；隐藏 Kraus 指标、不可访问记录、丢弃输出和独立混合准备的不可访问纯化不交给返回操作。$\mathcal D_c$ 只使用原 $AB$、声明的 $M_c$、实际 $c$ 以及实际供给的独立辅助态，不能读取未知准备、额外未知样本、输入相关建议或未触碰参考系统。所有初始辅助态、独立随机性和固定自适应控制均与未知 $(P,Q)$ 无关。

$M_c$ 合计除原 $AB$ 外每一个保留的、可能与输入相关的相干载体，包括工作区、相干指针、通信、控制器、程序及解码器记忆；分开放置或改称附件不改变联合计数。无限维可分侧输出及任意多个隐藏 Kraus 算子仍属于合同。

记 $d_c=\dim M_c$，无限维可分情形写 $d_c=\infty$，定义

$$
\begin{aligned}
E&=\sup_{(P,Q)\in\mathfrak F}
       \frac12\|\mathcal T(P\otimes Q)-P\otimes Q\|_1,\\
q_c&=\operatorname{Tr}\Psi_c(I_9/9),\\
h(d)&=\max\{1/d-1/8,0\}\quad(1\le d<\infty),
\qquad h(\infty)=0.
\end{aligned}
\tag{30.2}
$$

$q_c$ 是同一实际扩展在数学参考态 $I_9/9$ 上的诊断概率，$q_c\ge0$、$\sum_cq_c=1$。它不被假定为任意实际承诺输入的分支概率，也不要求实际准备 $I_9/9$。$E$ 只度量返回后的原 $AB$，不是完整操作返回误差。

**定理 30.2（原返回误差限制欠维相干分支的概率质量）。** 对定义 30.1 的每一个实际扩展及每一组实际固定返回，均有

$$
\boxed{\displaystyle
E\ \ge\ \frac1{1549800}\sum_{c\in\mathsf C}q_c\,h(d_c).}
\tag{30.3}
$$

右侧按全部实际经典结果求和，允许同时含有限维和无限维分支。结论约束原 $AB$ 仍可访问时的联合相干侧维数；不把 $AB$ 计入 $d_c$，也不以完整输入的存储维数界替代侧载体界。若改用 $h_{\rm old}(d)=\max\{(8-d)/d,0\}$、$h_{\rm old}(\infty)=0$，同一式的系数为 $1/12398400$，因为 $h_{\rm old}=8h$。

证明使用 §31 的原源归一化证书，并在 §32 给出任意粗记录、矩形 Kraus 算子和可数和的推导。

## 31. 原环境效应映射的定量条件证书

**命题 31.1（全部复方向上的源内强制界）。** 使用 (24.3)—(24.7)、(25.7) 的原矩阵 $K_i,V,\beta$。对每个 $Z\in M_8(\mathbb C)$，

$$
\|\beta(Z)\|_{\rm HS}^2\ge\frac1{80360}\|Z\|_{\rm HS}^2,
\qquad
\beta(I_8)=I_9,\qquad
\operatorname{Tr}\beta(Z)=\frac98\operatorname{Tr}Z.
\tag{31.1}
$$

证明。后两式直接复用 (24.6)、推论 25.2。以下给出首式所需的精确有限有理证书，保留原源而不引入数值奇异值阈值。令

$$
q=905000,\qquad
A_\star=\frac{790405860121}{307134375000},\qquad
 a_0=A_\star q^2=\frac{6323246880968}{3},
\tag{31.2}
$$

并按 (24.3) 取

$$
\begin{aligned}
(B_0,\ldots,B_7)&=(E_{01},E_{02},E_{10},E_{12},E_{20},E_{21},
                 \operatorname{diag}(1,-1,0),\operatorname{diag}(1,1,-2)),\\
(g_0,\ldots,g_7)&=(1,1,1,1,1,1,2,6).
\end{aligned}
\tag{31.3}
$$

原整数矩阵完全由

$$
(H_i)_{3a+b,3c+d}
 =905000\delta_{ac}(B_i)_{bd}
  +14480(B_i)_{ac}\delta_{bd}
  -9955\delta_{ad}(B_i)_{bc}
  -39824(B_i)_{ad}\delta_{bc}
\tag{31.4}
$$

确定，其中 $0\le a,b,c,d<3$。它等于原 (24.5) 的张量式，$K_i=H_i/\sqrt{a_0g_i}$；$H_i$ 实整数，因此转置就是伴随。归一化是原 (24.6)，即

$$
\sum_iH_i^{\mathsf T}H_i/g_i=a_0I_9,
\qquad
\operatorname{Tr}(H_i^{\mathsf T}H_j)
       =\delta_{ij}(9/8)a_0g_i.
\tag{31.5}
$$

按零起始行列序定义

$$
\begin{aligned}
M_{9r+s,\,8i+j}&=(H_i^{\mathsf T}H_j)_{r,s},
       &&0\le r,s<9,\quad0\le i,j<8,\\
\Gamma&=M^{\mathsf T}M,
&\Delta_g&=\operatorname{diag}_{8i+j}(g_i g_j).
\end{aligned}
\tag{31.6}
$$

这是 (25.3) 的同一个 $81\times64$ 整数矩阵，不是其选取的方形子式。令 $G_\beta$ 为六十四列 $\beta(E_{ij})=K_i^\dagger K_j$ 的 Hilbert—Schmidt Gram 矩阵，其中 $E_{ij}$ 此处是八阶矩阵单位。则

$$
\begin{aligned}
(G_\beta)_{8i+j,8k+\ell}
 &=\operatorname{Tr}[(K_i^\dagger K_j)^\dagger K_k^\dagger K_\ell],\\
G_\beta&=a_0^{-2}\Delta_g^{-1/2}\Gamma\Delta_g^{-1/2},\\
\operatorname{Tr}(G_\beta^{-1})
 &=a_0^2\operatorname{Tr}(\Delta_g\Gamma^{-1}).
\end{aligned}
\tag{31.7}
$$

定理 25.1 已证明列满秩，故 $\Gamma,G_\beta$ 正定。下表列出 $\Gamma$ 的非零项图的全部连通分量；每个集合内部按递增顺序，列号为 $8i+j$。同一行中每个分量有相同的加权逆迹 $R_C=a_0^2\operatorname{Tr}[(\Delta_g)_C\Gamma_C^{-1}]$。

| 分量族 | 全部列集合 $C$ | 每个分量的 $R_C$ |
| --- | --- | --- |
| $\mathcal C_{10}$ | $\{0,9,18,27,36,45,54,55,62,63\}$ | $R_{10}$ |
| $\mathcal C_6$ | $\{1,34,46,47,51,59\}$；$\{5,14,15,26,52,60\}$；$\{6,7,11,44,50,58\}$；$\{8,20,30,31,53,61\}$；$\{19,38,39,40,49,57\}$；$\{22,23,25,37,48,56\}$ | $R_6$ |
| $\mathcal C_1$ | $\{2\}$；$\{12\}$；$\{16\}$；$\{29\}$；$\{33\}$；$\{43\}$ | $R_1$ |
| $\mathcal C_2$ | $\{3,42\}$；$\{4,10\}$；$\{13,28\}$；$\{17,32\}$；$\{21,24\}$；$\{35,41\}$ | $R_2$ |

各集合互不相交且合为 $\{0,\ldots,63\}$；不同集合间的 $\Gamma$ 元素由 (31.4)—(31.6) 为零。加权逆迹的精确值为

$$
\begin{aligned}
R_{10}&=\frac{427619839702822500240810082579541996543589775926707123600772881561780589811}
 {45439616019121643165313516097948319078960968752463468297933589445120000},\\
R_6&=\frac{452991846557141111480792104503570207820179804739168890044555696622689192179}
 {68159424028682464747970274146922478618441453128695202446900384167680000},\\
R_1&=\frac{624741423713617818134641}{289442691639595929600},\\
R_2&=\frac{5372666586699133783584992389464322441}{1778817562497383210014988413440000}.
\end{aligned}
\tag{31.8}
$$

为确定这些有理数的有限求值，可对每个递增排列的 $C=\{k_0,\ldots,k_{m-1}\}$ 使用如下等价的正定消元恒等式。令 $\Gamma_C=\ell\operatorname{diag}(p_r)\ell^{\mathsf T}$，其中 $\ell$ 为单位下三角矩阵，依次定义

$$
\begin{aligned}
p_r&=(\Gamma_C)_{rr}-\sum_{v<r}\ell_{rv}^2p_v,\\
\ell_{sr}&=\frac{(\Gamma_C)_{sr}-\sum_{v<r}\ell_{sv}p_v\ell_{rv}}{p_r}
                      &&(s>r),\\
N_{rr}&=1,\qquad
N_{sr}=-\sum_{v=r}^{s-1}\ell_{sv}N_{vr}
                      &&(s>r),
\qquad N=\ell^{-1}.
\end{aligned}
\tag{31.9}
$$

正定性保证每个 $p_r>0$；所有量均为有理数。于是，若 $k_r=8i_r+j_r$，

$$
R_C=a_0^2\sum_{r=0}^{m-1}g_{i_r}g_{j_r}
                    \sum_{s=r}^{m-1}\frac{N_{sr}^2}{p_s}.
\tag{31.10}
$$

(31.9) 来自逐列比较 $\Gamma_C=\ell\operatorname{diag}(p)\ell^{\mathsf T}$，而 (31.10) 来自 $\Gamma_C^{-1}=N^{\mathsf T}\operatorname{diag}(p^{-1})N$。这给出了仅由原矩阵定义复算 (31.8) 的有理递推，无须外部逆矩阵或精度前提。十九个分量的总和为

$$
\begin{aligned}
\operatorname{Tr}(G_\beta^{-1})
 &=R_{10}+6R_6+6R_1+6R_2\\
 &=\frac{81144884955567687588129297292217278607694624384679201090456284627716165783}
 {1009769244869369848118078135509962646199132638943632628842968654336000},\\
80360-\operatorname{Tr}(G_\beta^{-1})
 &=\frac{171562134873406639461677363319640867674480831116963364676434724794217}
 {1009769244869369848118078135509962646199132638943632628842968654336000}>0.
\end{aligned}
\tag{31.11}
$$

特别地，逆迹严格介于 $80359$ 与 $80360$ 之间。正矩阵 $G_\beta^{-1}$ 的最大本征值不超过其迹，故 $G_\beta\succeq I_{64}/80360$。对任意复系数 $z_{8i+j}=Z_{ij}$，

$$
\|\beta(Z)\|_{\rm HS}^2=z^\dagger G_\beta z
 \ge\|z\|^2/80360=\|Z\|_{\rm HS}^2/80360.
\tag{31.12}
$$

矩阵单位在完整复 Hilbert—Schmidt 空间中正交归一；列矩阵恰好实并不把结论限制到实系数或 Hermitian 子空间。$\beta(Z)=V^\dagger(I_9\otimes Z)V$ 使用的就是 $Z_{ij}$，没有转置。证毕。

## 32. 加权关系的证明：隐藏分解、实际粗记录与全部质量

定理 30.2 的证明。对实际扩展直接复用定理 26.2，而不假设装置另供可访问的纯环境。取其有限或可数隐藏 Kraus 表示

$$
\begin{aligned}
L_{ca}&=(I_9\otimes A_{ca})V,
&\Psi_c(X)&=\sum_aL_{ca}XL_{ca}^\dagger,\\
\sum_{c,a}A_{ca}^\dagger A_{ca}&=I_8,
&L_{ca}^\dagger L_{ca}&=\beta(A_{ca}^\dagger A_{ca}).
\end{aligned}
\tag{32.1}
$$

隐藏的 $a$ 仅为数学分解。令

$$
X_{ca}=A_{ca}^\dagger A_{ca},\qquad
w_{ca}=\operatorname{Tr}X_{ca}/8.
\tag{32.2}
$$

由 (31.1)、(32.1) 和定义 30.1，

$$
\sum_{c,a}w_{ca}=1,\qquad
\sum_aw_{ca}=\sum_a\operatorname{Tr}(L_{ca}^\dagger L_{ca})/9
 =\operatorname{Tr}\Psi_c(I_9/9)=q_c.
\tag{32.3}
$$

$w_{ca}=0$ 时正性给 $X_{ca}=0$，进而 $A_{ca}=L_{ca}=0$；只在作此识别后略去对应零项。若 $w_{ca}>0$，定义有限维密度矩阵

$$
\sigma_{ca}=\frac{X_{ca}}{8w_{ca}}\in M_8(\mathbb C),\qquad
\tau_{ca}=\frac{\beta(X_{ca})}{9w_{ca}}
          =\frac89\beta(\sigma_{ca})\in M_9(\mathbb C).
\tag{32.4}
$$

即使 $M_c$ 无限维，这两个归一化矩阵仍分别在八、九维空间中；不在无限维输出上应用有限维态不等式。

若 $d_c<\infty$，则 $\operatorname{rank}\sigma_{ca}\le\min\{d_c,8\}$。对其非零本征值使用普通 Cauchy—Schwarz 的秩／纯度界，得到

$$
\|\sigma_{ca}-I_8/8\|_{\rm HS}^2
 =\operatorname{Tr}(\sigma_{ca}^2)-1/8\ge h(d_c).
\tag{32.5}
$$

当 $d_c\ge8$ 或 $d_c=\infty$ 时使用非负性，仍得到同一式。由 $\beta(I_8)=I_9$ 和 (31.1)，

$$
\begin{aligned}
\tau_{ca}-I_9/9&=\frac89\beta(\sigma_{ca}-I_8/8),\\
\|\tau_{ca}-I_9/9\|_{\rm HS}^2
 &\ge\frac{64}{81\cdot80360}h(d_c).
\end{aligned}
\tag{32.6}
$$

对这两个九维归一化态，使用 [Fuchs—van de Graaf，定理 1，式 (46)][ARRFVG] 的成熟界 $\|\tau-\omega\|_1/2\le\sqrt{1-f_{\rm r}(\tau,\omega)^2}$，再用 $\|Y\|_1\ge\|Y\|_{\rm HS}$，得

$$
1-f_{\rm r}(\tau_{ca},I_9/9)^2
 \ge\frac14\|\tau_{ca}-I_9/9\|_1^2
 \ge\frac{16}{81\cdot80360}h(d_c).
\tag{32.7}
$$

这里 $f_{\rm r}$ 沿用 (18.4) 的根保真度，平方只取一次。

现在固定实际返回 $\mathcal D_c$，取其 Kraus 算子 $B_{cu}:\mathbb C^9\otimes M_c\to\mathbb C^9$，满足 $\sum_uB_{cu}^\dagger B_{cu}=I$，可数时为强算子收敛。对同一 $c$ 的全部隐藏 $a$ 使用同一组 $B_{cu}$，没有将 $a$ 加入可读经典记录。

对一个 $L=L_{ca}$ 作极分解 $L=WH$，其中 $H=\sqrt{L^\dagger L}\in M_9$，$W:\mathbb C^9\to\mathbb C^9\otimes M_c$ 是极分解的部分等距，$W^\dagger W=\operatorname{supp}H$。Hilbert—Schmidt Cauchy—Schwarz 在九维空间中给出

$$
\begin{aligned}
|\operatorname{Tr}(B_{cu}L)|^2
 &=|\operatorname{Tr}(H^{1/2}B_{cu}WH^{1/2})|^2\\
 &\le\operatorname{Tr}H\;
  \operatorname{Tr}(H^{1/2}W^\dagger B_{cu}^\dagger B_{cu}WH^{1/2}),\\
\sum_u|\operatorname{Tr}(B_{cu}L)|^2
 &\le(\operatorname{Tr}H)^2.
\end{aligned}
\tag{32.8}
$$

求和时强完备关系被夹在有限秩算子之间，右侧的第二因子之和恰为 $\operatorname{Tr}[H^{1/2}(\operatorname{supp}H)H^{1/2}]=\operatorname{Tr}H$。因此奇异 $L$、矩形 $L$ 和无限维可分输出均包含；无需把 $W$ 延伸成一个额外可用的等距操作。

(32.8) 是 [Gregoratti—Werner，命题 4，式 (17)—(21)][ARRGW04] 的反馈迹界所用的极分解／Cauchy—Schwarz 步骤；这里显式给出矩形和粗记录的应用。只取任意实际返回的上界，不使用隐藏标签条件化的最优解码器，也不声称这个上界可由现有粗记录达到。

复合返回的 Kraus 算子是九阶矩阵 $B_{cu}L_{ca}$。以 (18.3) 的未归一化 Choi 约定，(32.4)、(32.8) 给出

$$
\begin{aligned}
F_e(\mathcal T)
 &=\frac1{81}\sum_{c,a,u}|\operatorname{Tr}(B_{cu}L_{ca})|^2\\
 &\le\frac1{81}\sum_{c,a}
                (\operatorname{Tr}\sqrt{L_{ca}^\dagger L_{ca}})^2\\
 &=\sum_{c,a}w_{ca}f_{\rm r}(\tau_{ca},I_9/9)^2.
\end{aligned}
\tag{32.9}
$$

最后一个等号使用 $L_{ca}^\dagger L_{ca}=9w_{ca}\tau_{ca}$ 和 $f_{\rm r}(\tau,I_9/9)=\operatorname{Tr}\sqrt\tau/3$。把 (32.3)、(32.7) 接入，得到

$$
1-F_e(\mathcal T)
 \ge\sum_{c,a}w_{ca}[1-f_{\rm r}(\tau_{ca},I_9/9)^2]
 \ge\frac{16}{81\cdot80360}\sum_cq_c h(d_c).
\tag{32.10}
$$

剩下的接口是原承诺误差到 Choi 重叠的提升，直接复用 (19.3)—(19.7) 的第一部分。它只要求最终 $\mathcal T:M_9\to M_9$ 为 CPTP，与中间是否保留相干输出无关。具体地，原双边缘 Haar 泄漏算子满足

$$
\mathscr L_A+\mathscr L_B\succeq\frac7{120}(I-\Pi_I),
\qquad \operatorname{Tr}J_{\mathcal T}=9.
\tag{32.11}
$$

$7/120$ 是定理 7.1 的既有谱隙；两核投影对易且交为 $\Pi_I$，正是 (19.5)—(19.6)。每个原 $P\otimes Q$ 上的两个边缘泄漏效应各不超过 $E$，因此

$$
9\frac7{120}(1-F_e(\mathcal T))\le2E,
\qquad E\ge\frac{21}{80}(1-F_e(\mathcal T)).
\tag{32.12}
$$

这里没有先假设整输入或带参考的准确性，也没有使用 (19.9)—(19.13) 仅适用于经典侧信息的近似保单位推导。将 (32.10) 代入 (32.12)，精确算术为

$$
\frac{21}{80}\frac{16}{81\cdot80360}
 =\frac1{1549800},
\tag{32.13}
$$

得到 (30.3)。

为明确全部可数极限，原 (26.8)—(26.10) 保证

$$
\sum_{c,a}\|L_{ca}\|_{\rm HS}^2=9,\qquad
\sum_{c,a}\operatorname{Tr}X_{ca}=8.
\tag{32.14}
$$

各 $\mathbb C^9\otimes M_c$ 可分，正常 CP 返回 $\mathcal D_c$ 因而有可数 Kraus 表示。其强完备和夹在有限秩 $L_{ca}$ 之间，在九维输入上按迹收敛；每个正输入的复合输出正项和保持全部原迹。复合 Choi 正项和总迹为九，因此 (32.9) 是同一实际 CPTP 通道的 Choi 恒等式。所有权重、平方迹和保真度项均非负，可先对有限部分和应用 (32.8)，再按单调收敛求和。由 $\sum w_{ca}=1$ 才可写 $1-\sum w_{ca}f_{\rm r}^2=\sum w_{ca}(1-f_{\rm r}^2)$。无限维侧分支只在 $h$ 中贡献零，其完整权重仍在这些质量恒等式中；没有把截断后的仪器称为保迹通道，没有丢弃尾部或把不可访问纯化送回解码器。证毕。

## 33. 欠维质量、实际输入概率与保留记录

**推论 33.1（七维及以下的全部质量界）。** 在定理 30.2 的完整合同下，令 $B=\{c:d_c\le7\}$。则

$$
\sum_{c\in B}q_c\le\min\{1,86788800E\}.
\tag{33.1}
$$

若每个非零实际分支都满足 $d_c\le7$，则

$$
E\ge\frac1{86788800}.
\tag{33.2}
$$

对每个原承诺 $\rho=P\otimes Q$，其实际欠维分支概率满足

$$
\sum_{c\in B}\operatorname{Tr}\Psi_c(\rho)
 \le\min\{1,781099200E\}.
\tag{33.3}
$$

证明。$1\le d\le7$ 时 $h(d)\ge h(7)=1/56$，且 $1549800\cdot56=86788800$，由 (30.3) 得 (33.1)。若 $q_c=0$，由 (32.3) 及正性该 CP 分支为零；所以第二种情形的 $B$ 含有全部质量，给出 (33.2)。任意九维密度矩阵均满足 $0\preceq\rho\preceq I_9$，正映射保序，故

$$
\operatorname{Tr}\Psi_c(\rho)
 \le\operatorname{Tr}\Psi_c(I_9)=9q_c.
\tag{33.4}
$$

求和并用总实际概率为一、$9\cdot86788800=781099200$ 得 (33.3)。这个保序步骤事实上适用于任意九维密度输入，不假定诊断概率等于承诺输入概率。可数时在非负部分和上取极限。证毕。

**推论 33.2（同一实际记录的必要界与条件误差）。** 定义

$$
\begin{aligned}
p_c(\rho)&=\operatorname{Tr}\Psi_c(\rho),\\
E_{\rm CQ}&=\sup_{\rho=P\otimes Q,\ (P,Q)\in\mathfrak F}
 \frac12\sum_c\|\mathcal D_c\Psi_c(\rho)-p_c(\rho)\rho\|_1.
\end{aligned}
\tag{33.5}
$$

理想 CQ 态使用全部同一实际 $c$ 及其实际概率。则

$$
E\le E_{\rm CQ}\le\sqrt E,\qquad
E_{\rm CQ}\ge\frac1{1549800}\sum_cq_c h(d_c).
\tag{33.6}
$$

若 $E_{\rm CQ}\le\eta$，对每个原承诺输入及每个 $p_c(\rho)>0$，归一化返回分支误差满足

$$
\frac12\left\|\frac{\mathcal D_c\Psi_c(\rho)}{p_c(\rho)}-\rho\right\|_1
 \le\min\{1,\eta/p_c(\rho)\}.
\tag{33.7}
$$

证明。$\mathcal D_c$ 保迹，所以 (33.5) 的各输出块迹为 $p_c(\rho)$；$\rho$ 是纯态。直接应用 (22.17) 的纯输入分块推导，它只使用这些事实，不依赖中间侧输出维数或隐藏 Kraus 数目。其加权 Cauchy—Schwarz 对可数非负和同样有效。丢弃记录的迹距离收缩性给反向 $E\le E_{\rm CQ}$；与 (30.3) 合并得到必要界。每个未归一化块的半迹距离不超过全部块之和 $\eta$，除以其真实正概率，并与归一化态距离不超过一合并，得到 (33.7)。该式没有无概率下限的统一稀有分支保证，也不把一个 $O(E)$ 的 $AB$ 上界提升为 $O(E)$ 的 CQ 上界。证毕。

## 34. 正误差不推出逐非零分支八维

**命题 34.1（独立稀有分支的边界）。** 在定义 30.1 的同一数学扩展类中，存在一个非零一维相干侧分支，同时 $E$ 和同一实际记录的 $E_{\rm CQ}$ 均可任意小而严格正。因此推论 28.1 的逐非零分支八维结论不能不加限定地延伸到正的无条件误差。

证明。任选 $0<r<1$，声明一个独立于输入的实际二值硬币结果 $g,b$，取

$$
\begin{aligned}
M_g&=\mathbb C^8,&\Psi_g(X)&=(1-r)VXV^\dagger,\\
M_b&=\mathbb C,&\Psi_b(X)&=r\mathcal N_\star(X).
\end{aligned}
\tag{34.1}
$$

一维侧空间作自然识别。两分支忽略侧输出后的和在整个 $M_9$ 上恰为 $\mathcal N_\star$，故满足原全边缘合同；$q_g=1-r$、$q_b=r$。对 $g$ 使用已有 (27.13) 的固定 CPTP 等距左逆 $\mathcal R_V$，对 $b$ 使用原 $AB$ 上的恒等通道。这给出

$$
\mathcal T=(1-r)\operatorname{id}+r\mathcal N_\star.
\tag{34.2}
$$

令

$$
e_{\mathcal N}=\sup_{(P,Q)\in\mathfrak F}
     \frac12\|\mathcal N_\star(P\otimes Q)-P\otimes Q\|_1.
\tag{34.3}
$$

由迹距离在部分迹下收缩及 (24.2)，

$$
0<\frac{1040350905}{790405860121}
  =D(\mathcal N_\star)\le e_{\mathcal N}\le1.
\tag{34.4}
$$

(34.2) 的 $AB$ 差恰为 $r(\mathcal N_\star(\rho)-\rho)$；同一实际 CQ 比较的 $g$ 块差为零、$b$ 块差就是这个矩阵。因此

$$
E=E_{\rm CQ}=r e_{\mathcal N}>0,\qquad
E,E_{\rm CQ}\longrightarrow0\quad(r\longrightarrow0^+).
\tag{34.5}
$$

$b$ 的归一化条件返回误差仍为固定的 $e_{\mathcal N}$，并未趋零。定理 30.2 对这个例子的右侧为 $7r/12398400$，正确地按真实稀有概率计费。该例只说明逐分支断言的边界；八维分支和同时峰值仍保留。它是所声明数学扩展类中的一套独立硬币扩展，不把已测 Weyl 仪器改称相干仪器，不提供某一既定实际混合装置的新访问或物理供应。证毕。

## 35. 原返回腿的适用范围与数学归属

**命题 35.1（同原消费者上的必要关系）。** 在定义 1.1—1.3 的完整 $\mathsf Q_1/\Phi/\mathrm E_2$ 解释和定义 30.1 的整个扩展合同下，对同一未知原关联先使用 $\mathcal N_\star$，再用所声明的实际 $AB,M_c,c$ 近似返回原 $\mathrm E_2(p,q)$，必满足 (30.3)、(33.1)—(33.3) 和 (33.6)。这是一条辅助工作寄存器返回的必要关系；它不供应原完整操作返回的充分条件。

证明。定义 1.2 将全部原关联与全部复正交对双向对应，故没有更换原样本、第一步 $P\otimes(I-P-Q)$ 消费者目标或返回的 $P\otimes Q$。全 $M_9$ 边缘仍为原 $\mathcal N_\star$，其第一步扰动和目标重叠仍按 (24.2) 在返回之前评价。定理 30.2 及两个推论因此适用。

$A_{ca}$、隐藏指标、矩阵单位、Gram 逆、Haar 平均、Choi 参考和 $I_9/9$ 权重均为证明坐标，不供给实际测量、参考系统访问、额外未知副本、源相关建议、准备权、相干化已测旗标或解码器门。可数经典记录不自动具有有限熵、有限历史长度或统一比特预算。只要存在输入相关的保留相干侧载体，就必须按其联合空间计入 $M_c$，而非仅计某个被命名为环境的子系统。

必要性在 $d_c\ge8$ 时给该项零，并不推出该分支或整套装置可校正；例 28.3 已说明足够的名义维数仍可承载不可逆扩展。定理没有匹配的二至七维构造、锐误差前沿或特定粗仪器的 CQ 最优值。§18—23 的经典返回保证、§27—28 的精确判据及八维端点继续在原范围使用；(34.1) 只是这些已有工具给出的边界例，不作为新的反演构造。

费用与操作边界完整沿用 §23、§29：实际产品准备、全部独立辅助系统和丢弃系统、保留载体、正反向门、测量和反馈、完整标签与记录的存储和通信、控制与校准、程序和 backing、验证、当前授权、返回与复位，仍计入同次运行的全部费用向量与同时峰值。侧空间维数不等于总内存、熵、物理存储或完整控制器成本；这里没有物理可用性、总费用优势或全局最小性结论。

原合法域、守卫、接受与执行后拒绝、全部回应和记录、来源身份与谱系、控制状态、rights、backing、当前 source-bound 权限、所欠动作、Handback／Stop／INITIAL、AA／ACK／token／吸收 halt 和下一入口语义均保留。$AB$ 或同一实际记录的 CQ 接近性没有恢复这些对象，也没有在返回未知原输入的同时保留一份独立精确的 $P\otimes R$。本关系不构造一般非承诺中间态上的共同 $\sigma,\tau$，不供给全部有限字的在线中间输出或完整操作返回。

四份独立实际取得的完整 body、INPUT／STACK 分离、所选完整收到的 body 驱动同一原 owed consumer，以及广泛 Native／AA／Fibonacci 操作对应继续要求各自的真实来源与操作桥。已有 [增广 $J_r$ 的定理 65.3、70.2、75.4][CRJR] 在完整实际入口、封闭 writer／输入、门、当前权限、每个请求切口的独立实际 wake、材料与进展前提下，已经解决全部声明切口、每个有限有序请求森林及原 owed-action 返回；这些条件域不被重新列为未解。未增广或物理来源、更细 primitive 内部和更广供应桥仍保留原义务。GENERAL15.5／18.4、RG13.3 的既有受限 cross-entry／inherited original-Q 结论仍成立；其外的 changed／new-row Q、较广 mixed interiors 和完整 terminal-task kernel 没有由本定理解决。§23、§29 的共同源准备、未付 $3+3$ 产品、一般 completion-added 态的同时准备和实际取得、同族仪器及物理时间合同也均保留。证毕。

**数学归属约定 35.2。** (30.3) 是 repo-derived 的固定源有限误差加权关系：原源的 $\beta$ 条件界将欠维 Kraus 效应的秩／纯度缺口传给任何实际粗记录解码器的纠缠保真度，再经原完整复承诺的双边缘泄漏提升，限制欠维分支的实际诊断质量。常数证书是这条关系的一个前提，既有精确八维端点、经典一维障碍及完整环境左逆均不另计新内容。

§24—26 的源归一化、完整乘积独立性和任意实际扩展因子化，§7、§19 的谱隙及承诺到过程桥，§22 的纯输入 CQ 比较，以及 §27—28 的等距左逆与精确边界均直接复用。一般秩／纯度界、正矩阵 Gram 估计、Choi 表示和单调收敛是标准线性代数与算子工具。[Gregoratti—Werner，命题 4，式 (17)—(21)][ARRGW04] 提供成熟反馈迹界；(32.8) 明确补足此处矩形、奇异和无限可分侧输出的应用，而不继承隐藏结果可读或反馈最优性。[Fuchs—van de Graaf，定理 1，式 (46)][ARRFVG] 提供归一化九维态上的距离／根保真度界。

[Bény—Oreshkov，定理 1、推论 2—3][WRCBO] 的近似纠错与互补通道条件，以及 [Kretschmann—Schlingemann—Werner，定理 3，式 (32)][WRCKSW] 的信息—扰动关系是一般背景；其整输入最坏纠缠保真度或完全范数前提不由原承诺上的 $E$ 直接给出。本证明使用的是本卷已有的精确承诺泄漏桥，并具体计算原 $\beta$ 的条件界，不把这些一般判据重述为新的校正定理。实际耦合和访问仍依 [Gregoratti—Werner，§VI Mixed Environments][RRCCOUPLING] 区分；忽略侧输出后的同一边缘不使不同实际仪器互换。

这里的数学范围限于 $t_\star=1/1000$、有限或可数实际经典结果及上述完整扩展类；连续结果、其他参数上的统一分类、锐折衷、更广的操作实现和持续互恢复的全目标仍没有本关系给出的结论。普通数学推导与精确有理证书不构成新的形式化声明；本关系的仓内推导归属也不宣称全球文献优先性。

[WRCBO]: https://arxiv.org/html/0907.5391v1 "Cédric Bény and Ognyan Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels，Theorem 1、Corollaries 2—3：最坏纠缠保真度下的互补通道条件。"
[WRCKSW]: https://arxiv.org/html/quant-ph/0605009v1 "Dennis Kretschmann, Dirk Schlingemann and Reinhard F. Werner, The Information-Disturbance Tradeoff and the Continuity of Stinespring Representation，Theorem 3、(32)：完全范数的信息—扰动界。"

## 追加锚（本行以下为增补区）

# 递归关系观察：生成签名与同档案任务取得

本卷区分生成项、任务行为商、动态摘要和实际取得记录，并在 KBonacci 的同一个已付混合尾档案上给出全部可取得目标分割、联合任务的切口条件及原 INITIAL 来源的消费者。FIB 生成签名和一般纤维因子化只作既有供应；具体取得结论使用所声明的 KBonacci 读者，不把两个来源的操作或费用互相移植。

## 1. 同一个已付混合尾档案

**定义 1.1（固定实际来源与目标）。** 全章使用 [KBonacci INITIAL 费用卷固定版本](https://github.com/the-omega-institute/trureturing/blob/e271e8c9d490b299979f17661411302360adb4c6/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md)定义68.1的域，并加 $h\ge2$：

$$
3\le m<k<2m,\qquad T=k+1,\qquad
\gcd(m,T)=1,\qquad h=k-m\ge2.
\tag{AA.1}
$$

于是 $2\le h\le m-2$，两个原字母表都含全部 $m$ 位块。成功记录为 $(v,\theta,s)$，$v\in\mathbb F_2$、$\theta\in\mathbb Z/T\mathbb Z$、$0\le s<k$。匹配权重与逐位转移为

$$
c_i=\mathbf1_{\{0,T-1\}}(i\bmod T),\qquad
\delta_0(v,\theta,s)=(v,\theta+1,0),
$$
$$
\delta_1(v,\theta,s)=
\begin{cases}
(v\oplus c_\theta,\theta+1,s+1),&s+1<k,\\
\bot,&s+1=k,
\end{cases}
\qquad \delta_b(\bot)=\bot.
\tag{AA.2}
$$

初读免费供应 $v$ 或 $\bot$。以后每次动作恰为一个完整 $m$ 位块，付费一；只在块末读取标量或 $\bot$，中间拒绝时刻不可见，拒绝后的剩余位仍属于这次付费块。INITIAL 指实验开始时的不可变目标记录，不随当前记录更新。控制器只能依自己取得的有序动作／端点回复档案选择动作、停止和输出；没有 reset、copy、外借分支记录、隐含初始时钟或中间位读口。

固定一个初值 $v$，实际付费发出根块 $1^m$，条件化到成功且差值为一的那份档案。其全部 INITIAL 候选用

$$
Q_v=\{0,m\}\times\{0,\ldots,h-1\}
\tag{AA.3}
$$

索引：$(j,s)$ 的 INITIAL 是 $(v,-j,s)$，当前记录为 $(v\oplus1,-j+m,s+m)$。所有候选具有同一已付根档案。目标 $F:Q_v\to Y$ 取 INITIAL 标签，$\Delta_v(F)$ 是在这份档案后取得它的最小额外最坏完整块费；无统一有限正确续接时记为 $+\infty$。可适应选择，也可只要求本档案上的一个预设后缀；下述值在两者下相同。

这里每个候选都来自原共同历史先验。具体地，选

$$
\ell\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,
\qquad \ell\ge s+2,\qquad
d=\bigoplus_{i=\ell-s}^{\ell-1}c_i.
$$

原合法历史 $(v\oplus d)0^{\ell-s-1}1^s$ 同时实现该 INITIAL 值、相位和尾；再追加同一个根块就实现（AA.3）的已付档案。来源历史长度不作为免费观察。这直接使用原卷式（1.3）的联合见证。

**定义 1.2（目标的可行切口集）。** 对 $0\le r<h$，令

$$
H_r=\{0,m\}\times\{h-r,\ldots,h-1\},\qquad
L_{j,r}=\{j\}\times\{0,\ldots,h-r-1\}.
$$

记 $\mathcal P_r$ 为 $H_r,L_{0,r},L_{m,r}$ 中全部非空集合组成的分割。特别 $\mathcal P_0$ 有两个相位胞，$r\ge1$ 时 $\mathcal P_r$ 有三个胞。定义

$$
\mathcal C_F=\{r\in\{0,\ldots,h-1\}:
F\text{ 在 }\mathcal P_r\text{ 的每个胞上恒定}\}.
\tag{AA.4}
$$

式（AA.4）就是原卷式（68.3）的切口条件，分别要求共同高尾带恒定、两个低相位带各自恒定。原定理68.2给出

$$
\Delta_v(F)=
\begin{cases}
0,&F\text{ 恒定},\\
1,&F\text{ 非恒定且 }\mathcal C_F\ne\varnothing,\\
+\infty,&\mathcal C_F=\varnothing,
\end{cases}
\tag{AA.5}
$$

且非恒定目标至多有一个可行切口。每个可行 $r$ 的一块实现为

$$
B_r=
\begin{cases}
0^{h+1}1\,0^{m-h-2},&r=0,\\
1^r0^{m-r},&1\le r<h.
\end{cases}
\tag{AA.6}
$$

这些是既有准确费用和动作供应；其无穷分支依据所有首动作的首零损失，不是有限深度搜索未命中。

## 2. 同档案联合切口与全部可取得分割

**推论 2.1（同档案联合任务的准确费用）。** 在定义1.1的同一个 $Q_v$ 和同一已付档案上，给任意 $F:Q_v\to Y$、$G:Q_v\to Z$，有

$$
\mathcal C_{(F,G)}=\mathcal C_F\cap\mathcal C_G.
\tag{AA.7}
$$

若 $\Delta_v(F)=\Delta_v(G)=1$，记其唯一切口为 $r_F,r_G$，则

$$
\Delta_v(F,G)=
\begin{cases}
1,&r_F=r_G,\\
+\infty,&r_F\ne r_G.
\end{cases}
\tag{AA.8}
$$

证明。在每个固定胞上，二元组恒定当且仅当两个分量各自恒定，故（AA.7）成立；这是恒定性的直接应用。联合目标非恒定，原定理68.2遂给（AA.8）。切口相同时同一个真实块 $B_r$ 提供联合目标所需的端点区别；每个分量的解码均使用该源自己的初值、根端点和新端点。切口不同时，（AA.5）的全首动作障碍排除一切有限适应续接，不能先取得一个目标再从已破坏的 INITIAL 重做另一个实验。证毕。

**命题 2.2（完整分割分类与精确数目）。** 在 $Q_v$ 上按输出标签重命名认同目标，亦即只计其非空纤维分割。可取得分割恰为某个 $\mathcal P_r$ 的粗化。其总数为

$$
1+(\operatorname{Bell}(2)-1)
 +(h-1)(\operatorname{Bell}(3)-1)=4h-2.
\tag{AA.9}
$$

以更细的分割为较大的细化序中，全部极大可取得分割恰为 $\mathcal P_0,\ldots,\mathcal P_{h-1}$；它们两两不可比，因 $h\ge2$ 而不存在最细可取得分割。这里“最细”表示细于所有可取得分割。

证明。一个目标在 $\mathcal P_r$ 的各胞上恒定，等价于它的纤维分割是 $\mathcal P_r$ 的粗化。（AA.5）给两向分类，常值目标是所有 $\mathcal P_r$ 共有的单胞粗化。每个非恒定可取得目标的切口唯一，因此各 $\mathcal P_r$ 的非平凡粗化互不重复。两个非空胞有 $\operatorname{Bell}(2)=2$ 个分割，三个有 $\operatorname{Bell}(3)=5$ 个；先计共有单胞，再计其余粗化，得到（AA.9）。

若 $\mathcal P_r$ 细于 $\mathcal P_t$，则以 $\mathcal P_t$ 的胞为标签的非恒定目标同时具有切口 $r,t$；唯一性给 $r=t$，故两两不可比。任一可取得分割均粗于一个 $\mathcal P_r$，而每个 $\mathcal P_r$ 本身可取得，故它们恰为全部极大元。有至少两个不可比极大元时，不可能存在一个可取得分割同时细于它们。证毕。

“分别可取得但联合不可取得”及“没有最细可取得分割”的一般现象已由 [KBonacci 不可逆取得卷定理7.2与7.5](https://github.com/the-omega-institute/trureturing/blob/e271e8c9d490b299979f17661411302360adb4c6/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md)供应。这里的具体应用是同一已付混合尾档案的完整切口分类及 $4h-2$ 计数。经典分割计数、纤维交集和上述一般现象不另作为新成果。

## 3. 四个共同档案候选与全 INITIAL 消费者

**命题 3.1（同一根档案上的两个不相容任务）。** 取 $k=6,m=4,T=7,h=2$，固定任意一个免费初值 $v$。根块 $1111$ 已经付费，四个候选为

$$
Q_v=\{(0,0),(0,1),(4,0),(4,1)\}.
$$

定义

$$
F(j,s)=\mathbf1_{\{j=4\}},\qquad G(j,s)=s.
\tag{AA.10}
$$

这两个目标各自的额外最优费用为一，联合目标的额外费用为 $+\infty$；全部目标分割恰六个可取得、九个不可取得。

证明。$F$ 的唯一切口为零，$G$ 的唯一切口为一。由（AA.6），额外一块 $0001$ 取得 $F$，额外一块 $1000$ 取得 $G$；两者分别最优。$0001$ 清尾后对相位零给差值一、相位四给差值零，所以 $F$ 为该差值的补位。$1000$ 在 $s=1$ 时拒绝，在 $s=0$ 时成功，因此 $G$ 由块末拒绝位给出。目标始终取原 $s$，不是清零后的当前尾。

联合 $(F,G)$ 在四个来源上全部不同，却无法由任意有限续接取得。直接核对所有首动作：若首位为零，同一相位的 $s=0,1$ 都在首零处合并，丢失 $G$；若首位为一，两相位的 $s=1$ 都在第一位进入同一吸收拒绝，丢失 $F$。中间拒绝时刻不可观察，两条被合并的来源在整个后续控制器上保持同一档案和停止输出。联合目标非恒定，零动作停止也失败。因此该无穷费用证明覆盖全部16个完整块及任意后续深度，没有枚举截止。

四个 INITIAL 来源确实来自原历史域：在定义1.1的见证中，$j=0$ 取 $\ell=28$，$j=4$ 取 $\ell=24$，分别配 $s=0,1$ 和所需首位。两种长度均是完整块倍数、满足相位同余；追加 $1111$ 后四者的免费初值与根端点都相同。每次反例比较各在一个固定真实源上运行同一控制器，不拼接来自不同来源的回复。

本例有 $\operatorname{Bell}(4)=15$ 个全部目标分割，命题2.2给其中恰六个可取得、九个不可取得。六个是单胞分割、$\mathcal P_0$，以及 $\mathcal P_1$ 的三个两胞粗化和三胞分割本身。这个计数按标签重命名认同，未数控制器或源码。证毕。

**推论 3.2（原完整 INITIAL 域上的分别二块与联合无穷）。** 保持命题3.1参数，现取原完整域

$$
Q=\{\bot\}\cup
\{(v,-j,s):v\in\mathbb F_2, j\in\mathbb Z/7\mathbb Z, 0\le s<6\}.
$$

对 $A=F,G$ 分别选择互异新标签 $R_A,C_A$，均不在 $A[Q_v]$ 中，并给初始 $\bot$ 一个独立标签 $L_A$。两个完整 INITIAL 目标精确定义为

$$
\widehat A(\bot)=L_A,\qquad
\widehat A(v,-j,s)=
\begin{cases}
R_A,&s\ge2,\\
A(j,s),&s<2,\ j\in\{0,4\},\\
C_A,&s<2,\ j\notin\{0,4\}.
\end{cases}
\tag{AA.11}
$$

两初值使用同一张 $A$ 表。对原卷定义1.3的适应费用 $C_{\rm ad}$ 和单个 GLOBAL 预设流费用 $C_{\rm pre}$，有

$$
C_{\rm ad}(\widehat F)=C_{\rm pre}(\widehat F)=2,
\qquad
C_{\rm ad}(\widehat G)=C_{\rm pre}(\widehat G)=2,
$$
$$
C_{\rm ad}(\widehat F,\widehat G)
=C_{\rm pre}(\widehat F,\widehat G)=+\infty.
\tag{AA.12}
$$

证明。式（AA.11）是原推论68.3的精确消费者：对每个目标，两个免费值档案的表相同。该推论迫使首块为 $1111$；其理由也可在同一 INITIAL 相位零的尾零与尾二上直接核对：两目标的各自标签为 $A(0,0)$ 和新标签 $R_A$，所以不能免费停止。任意含零根的领先一串长度至多三，这两个尾均存活到首零并在该处合并，此后永远同档案，故这种根不可能正确。只剩全一根。

全一根的拒绝支返回 $R_A$，成功零差支返回 $C_A$，成功一差支正是命题3.1。因而单目标分别使用一个 GLOBAL 流 $1111\mid0001$ 和 $1111\mid1000$，按档案提前停止或在第二个块末返回；每个目标都有真实来源发出两块，且正差支非恒定给出匹配下界。初始 $\bot$ 免费返回 $L_A$。

任一联合正确控制器投影其输出即为 $\widehat F$ 的正确控制器，所以其根也被迫是 $1111$。在任一正差档案上，命题3.1已经排除联合任务的全部首续接动作，故任何适应控制器都失败；更受限的 GLOBAL 控制器也失败。每条比较历史保留同一源与其完整实际档案。证毕。

这与原推论68.3的两个免费值档案需要不同预设后缀的障碍有别：式（AA.12）中每个单目标在两免费值上都能使用同一后缀，失败已发生在固定一个 $v$ 的同一付费档案内，且适应续接也失败。

## 4. 供应、任务恢复与范围

**数学引文 4.1（来源与证据等级）。** 本卷是 `repo-derived` 的普通数学应用，不主张全球原创。一般商与同余、分割计数、已有非联合取得现象均按其供应复用；承重的具体应用是（AA.7）–（AA.12）的同档案切口、全部分割数与原 INITIAL 消费者。

| 供应 | 本卷的直接用途与保留边界 |
| --- | --- |
| [KBonacci INITIAL 费用卷](https://github.com/the-omega-institute/trureturing/blob/e271e8c9d490b299979f17661411302360adb4c6/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md)，定义1.1–1.3、定义68.1、定理68.2、推论68.3 | 同一实际历史、不可变 INITIAL、完整块末读出、吸收拒绝、全首动作切口必要性、唯一切口、一块实现及强制根的全源提升。 |
| [KBonacci 不可逆取得卷](https://github.com/the-omega-institute/trureturing/blob/e271e8c9d490b299979f17661411302360adb4c6/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md)，定理7.2、7.5 | 分别取得不蕴含联合取得、一般最细可取得分割障碍及其原参数域；不把这些现象重记为本卷新定理。 |
| [过程几何卷](https://github.com/the-omega-institute/trureturing/blob/e271e8c9d490b299979f17661411302360adb4c6/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)，第43–44章 | 任务充分性与无冗余、实际像下降、源更新与已付记录的区别；不为 KBonacci 提供树复制、重置或额外读口。 |
| [联合矩卷](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md)，定理36.4、第43–47章 | FIB 来源为有序配对树，替换满足 $\rho\alpha=\beta$、$\rho\beta=\langle\beta,\alpha\rangle$ 并逐子树作用；仅配对须两个叶种子，配对加 $\rho$ 一个 $\alpha$ 即足够，仅 $\rho$ 无有限生成集。此既有签名比较不授未知源编辑权限。矩容量、声明族逆、条件输出位数与实际取得分开，参数守卫保持原样。 |
| [有限起点预测记忆卷](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_START_PREDICTIVE_MEMORY.md)，第1、2、6–9章 | 已取得历史上的未来律、静态编码与在线更新、状态名字与全部成本的区别；五模随机源不是本卷不可逆块读者。 |

**范围 4.2（记录因子化不供给取得权限）。** 在同一个实际域上，两个已经给定的读出静态地满足 $\ker(\eta_1,\eta_2)=\ker\eta_1\cap\ker\eta_2$；这个恒等式没有构造取得两个读出的历史。固定一个实际控制器 $\Pi$，其终端完整档案映射记为 $a_\Pi$。取得目标 $F$ 要求存在解码 $D$ 使 $F=D\circ a_\Pi$，即 $\ker a_\Pi\subseteq\ker F$；这是既有实际像因子化。两个不同控制器分别满足该式，并不供应一条同时实现两份档案的历史。推论2.1给出这里何时存在同一控制器，命题3.1给出不存在时的永久合并对。

要从目标反向恢复完整取得档案，还须 $\ker F\subseteq\ker a_\Pi$；通常动作与记录可含任务冗余，故不能自动要求核相等。要把压缩档案用作动态观察状态，还须已声明动作的合法性、输出、记录更新和后继在其纤维上下降。种子闭包、任务核、动态状态与取得记录由这些明确的条件相接，没有彼此无条件同一的结论。

上述费用只计同一实际源上发出的完整块，不给记录、控制器、计算、保存寿命、物理时间或能量定价。$4h-2$ 只计（AA.1）及（AA.3）这个已取得域的分割，不替代任意相关先验或全部 $k,m$ 的最优费用。原词和过去档案恢复、跨分辨率实际像、FIB 与 KBonacci 的同源操作运输，以及空间、时间、边界和记忆的完整互恢复均需额外合同；本卷没有建立这些桥。

## 追加锚（本行以下为增补区）

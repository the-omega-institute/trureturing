# Recursive relational observation: joint-kernel towers and the minimal predictive core

本卷把有限深度联合核塔、档案 law 残余、完整未来行为商和四种表示运输接到同一个
最小预测边界上。它回答的是一个表示问题：在声明的测试族内，观察者为了决定所有
允许的未来响应，至少需要保留哪一个关系商。

全文只讨论带类型的经典实际来源、有限前缀闭合测试和有限或可数的离散输出。它是
理论推导，不新增 Lean 声明，不把逆极限完成解释成物理时空，也不把数学上的商或
law 表当作观察者已经取得的输入。与 [统一联合律桥](RECURSIVE_RELATIONAL_OBSERVATION_UNIFIED_JOINT_LAW_BRIDGE.md)
和 [联合核线程实现](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_THREAD_REALIZATION.md)
的符号保持一致。

## 1. 有限测试与完整未来行为商

固定带接口类型的实际来源

$$
Z=\bigsqcup_{\tau\in I}Z_\tau .
$$

令 $\mathscr T_{\le n}$ 是深度至多 $n$ 的有限自适应测试族。测试保留完整有序
转录：事件、成功或拒绝、失败终端、实际记录、权限和后继类型。假设测试族对
有限前缀和声明的合法自适应串接封闭，并且

$$
\mathscr T_{\le n}\subseteq\mathscr T_{\le n+1},\qquad
\mathscr T=\bigcup_{n\ge0}\mathscr T_{\le n}.
$$

对 $z,u\in Z_\tau$ 定义档案 law 残余

$$
z\,A_n^{\mathrm{law}}\,u
\iff
\forall E\in\mathscr T_{\le n},\quad
\operatorname{Law}_z(E)=\operatorname{Law}_u(E).
\tag{MPC.1}
$$

完整未来行为关系定义为

$$
z\sim_{\mathscr T}u
\iff
\forall E\in\mathscr T,\quad
\operatorname{Law}_z(E)=\operatorname{Law}_u(E).
\tag{MPC.2}
$$

这里的等式是同一类型上完整转录 law 的等式，不是某个成功读数或总概率的边缘
等式。

**命题 1.1（有限残余的极限刻画）。** 在上述前缀穷尽条件下，

$$
\boxed{
A_\infty^{\mathrm{law}}
:=\bigcap_{n\ge0}A_n^{\mathrm{law}}
=\sim_{\mathscr T}.
}
\tag{MPC.3}
$$

**证明。** 若 $(z,u)$ 属于左侧，则对任意 $E\in\mathscr T$，由
$\mathscr T=\bigcup_n\mathscr T_{\le n}$ 可取 $n$ 使 $E\in\mathscr T_{\le n}$，
于是两边的 law 相同。反之，若两边对所有 $E\in\mathscr T$ 的 law 相同，则对
每个固定 $n$ 的所有 $E\in\mathscr T_{\le n}$ 都相同，故属于每个
$A_n^{\mathrm{law}}$。$\square$

若目标不是有限测试本身，而是一个无限转录 law，则还需声明输出空间的 sigma
代数由有限柱集生成，并使用有限柱边缘唯一决定 law 的条件。没有这个条件时，
(MPC.3) 只说明所有声明的有限实验相同，不自动说明某个更大的无限对象相同。

## 2. law 商塔与真实来源像

每个 $A_n^{\mathrm{law}}$ 都是保持类型的等价关系。定义

$$
C_n^A=Z/A_n^{\mathrm{law}},
\qquad
a_n:Z\longrightarrow C_n^A,\quad a_n(z)=[z]_{A_n^{\mathrm{law}}}.
$$

由于 $A_{n+1}^{\mathrm{law}}\subseteq A_n^{\mathrm{law}}$，有 bonding 映射

$$
s_n:C_{n+1}^A\longrightarrow C_n^A,
\qquad
s_n([z]_{A_{n+1}^{\mathrm{law}}})
=[z]_{A_n^{\mathrm{law}}},
\tag{MPC.4}
$$

且 $s_n a_{n+1}=a_n$。令

$$
L_A=\varprojlim C_n^A
$$

为 law 完成空间，并定义

$$
\theta:C_{\mathscr T}\longrightarrow L_A,
\qquad
C_{\mathscr T}:=Z/\sim_{\mathscr T},
\qquad
\theta([z]_{\sim_{\mathscr T}})
=(a_0(z),a_1(z),\ldots).
\tag{MPC.5}
$$

令 $B_A=\theta[C_{\mathscr T}]$，称为真实 law 来源像。

**定理 2.1（最小预测商的完成分裂）。** 在命题 1.1 的条件下，$\theta$ 是单射，
并且

$$
C_{\mathscr T}\cong B_A.
\tag{MPC.6}
$$

此外，$\theta$ 满射当且仅当每个相容 law 线程

$$
t=(t_n)_{n\ge0}\in L_A
$$

都存在 $z\in Z$ 使 $a_n(z)=t_n$ 对所有 $n$ 成立。

**证明。** 若 $\theta([z])=\theta([u])$，则 $a_n(z)=a_n(u)$ 对所有 $n$，
即 $z\,A_n^{\mathrm{law}}\,u$ 对所有 $n$。由 (MPC.3) 得
$z\sim_{\mathscr T}u$，所以 $\theta$ 单射。像的定义给出 (MPC.6)。满射的定义
正是每个线程具有同一个来源代表元。$\square$

因此，$L_A$ 不是自动的实际状态空间。它包含全部满足有限层 bonding 方程的
数学线程；$B_A$ 才是由实际来源产生的线程。完成性与可分性是两个不同条件：

令 $\pi_{\mathscr T}:Z\to C_{\mathscr T}$ 为商投影，并置

$$
\eta_A:=\theta\circ\pi_{\mathscr T}:Z\to L_A.
$$

则

$$
\bigcap_n A_n^{\mathrm{law}}=\Delta_Z
\quad\Longleftrightarrow\quad
\eta_A\text{ 是单射},
\tag{MPC.7}
$$

而

$$
B_A=L_A
\quad\Longleftrightarrow\quad
\text{所有相容 law 线程都有实际来源实现}.
\tag{MPC.8}
$$

## 3. 与联合核塔的精确比较

沿用联合核线程卷的

$$
Q_n=Z/K_n,
\qquad
L_K=\varprojlim Q_n,
\qquad
\eta_K(z)=([z]_{K_n})_n,
\qquad
B_K=\eta_K[Z].
$$

假设

$$
\boxed{
K_n\subseteq A_n^{\mathrm{law}}\qquad(n\ge0).
}
\tag{MPC.9}
$$

这是联合核细化给出的安全方向；随机情形不能把它改写成无条件相等。

由 (MPC.9) 定义有限层商映射

$$
\phi_n:Q_n\longrightarrow C_n^A,
\qquad
\phi_n([z]_{K_n})=[z]_{A_n^{\mathrm{law}}}.
\tag{MPC.10}
$$

它是良定义且满射，并满足

$$
s_n\phi_{n+1}=\phi_np_n.
\tag{MPC.11}
$$

因此逐坐标得到逆极限映射

$$
\Phi:L_K\longrightarrow L_A,
\qquad
\Phi((x_n)_n)=(\phi_n(x_n))_n.
\tag{MPC.12}
$$

记 $q_\infty:Z\to C_{\mathscr T}$ 为完整未来行为商的规范投影。则

$$
\Phi\circ\eta_K=\theta\circ q_\infty,
\qquad
\boxed{\Phi[B_K]=B_A.}
\tag{MPC.13}
$$

这里的第二个等式只比较真实来源像；它不声称 $\Phi$ 把所有完成线程都提升为
真实来源。

**定理 3.1（有限商比较的三种强度）。**

1. 若对所有 $n$ 都有 $K_n=A_n^{\mathrm{law}}$，则每个 $\phi_n$ 是保持类型的
   双射，$\Phi$ 是双射，且 $L_K\cong L_A$、$B_K\cong B_A$。
2. 若仅有 (MPC.9)，则 $\Phi$ 一般只保留真实像并可能合并不同的 $K$-线程；
   它不必单射。
3. 在仅有 (MPC.9) 时，$\Phi$ 满射的充分必要条件是：每个
   $t\in L_A$ 都存在相容提升 $(x_n)_n\in L_K$，使
   $\phi_n(x_n)=t_n$ 对所有 $n$ 成立。

**证明。** 第一项由逐层双射及其自然性得到。第二项中若
$K_n\subsetneq A_n^{\mathrm{law}}$，同一 law 类可包含多个 $K_n$ 类，故
$\phi_n$ 可能非单射；其逐层非单射可在极限中保留。第三项正是 (MPC.12) 的
满射定义。$\square$

有限层满射不能单独推出极限满射。等价地，对每个 $t\in L_A$ 令

$$
H_n(t)=\phi_n^{-1}(t_n).
$$

除了 $H_n(t)\ne\varnothing$，可以要求下列相容提升条件作为保证全局提升的充分条件

$$
p_n[H_{n+1}(t)]=H_n(t)\qquad(n\ge0),
\tag{MPC.14}
$$

或直接采用紧乘积中的非空闭有限交性质、Mittag--Leffler 条件等足以保证非空
逆极限的假设。逐层“有代表元”与全局“有相容代表元”是两个不同命题；(MPC.14)
是一个易检查的充分条件，不是相容 lift 存在的必要条件。

## 4. 最小预测核心与四种状态视图

令四个状态视图为保持接口类型的映射；每个 $Y_i$ 都是带同一接口类型标记的析取。

$$
e_i:Z\longrightarrow Y_i,
\qquad
i\in\{\mathrm{space},\mathrm{time},\mathrm{boundary},\mathrm{memory}\}.
$$

这里的 time 可以是完整时间记录；若只保留交换型累计量，它还需额外满足
相应的 cocycle 条件。定义最小预测核心

$$
C_{\mathscr T}=Z/\sim_{\mathscr T}.
$$

### 4.1 动态充分视图

称 $e_i$ 对测试族 $\mathscr T$ 动态充分，是指存在保持类型的更新
$\bar T_a$、合法域 $\bar D_a$ 和完整输出核 $\bar J_a$，使得：

1. 合法性、拒绝、事件、完整记录和后继都在 $e_i$ 的纤维上不变；
2. selector 只读取 $e_i$ 的值、已取得档案和声明权限；
3. 每个允许动作都满足相应的核交换式；
4. 对所有有限自适应测试，视图上的 transcript law 等于来源上的 transcript law
   的推送。

这四条把“视图有一个当前数值”提升为“视图有自己的可组合过程”。

**定理 4.1（四视图的最小恢复判据）。**

若每个 $e_i$ 动态充分，则：

1. 当
   \[
   \ker e_i=\sim_{\mathscr T}\qquad\text{对所有 }i
   \tag{MPC.15}
   \]
   时，存在唯一保持类型的双射
   \[
   \bar e_i:C_{\mathscr T}\xrightarrow{\;\cong\;}\operatorname{im}(e_i),
   \qquad
   \bar e_i([z])=e_i(z).
   \tag{MPC.16}
   \]
   因而四个状态视图两两唯一可恢复，且
   \[
   \chi_{ji}=\bar e_j\circ\bar e_i^{-1}
   \tag{MPC.17}
   \]
   满足 $\chi_{ki}=\chi_{kj}\circ\chi_{ji}$。
2. 当
   \[
   \ker e_i\subseteq\sim_{\mathscr T},
   \tag{MPC.18}
   \]
   时，存在唯一满射
   \[
   d_i:\operatorname{im}(e_i)\twoheadrightarrow C_{\mathscr T},
   \qquad d_i(e_i(z))=[z].
   \tag{MPC.19}
   \]
   该视图可能保留任务无关的额外细节，但它仍能恢复最小预测核心。

**证明。** (MPC.15) 下，$\bar e_i$ 良定义、单射且由像定义满射，故为双射；
(MPC.17) 是唯一运输。若 (MPC.18)，相同视图值必有相同完整未来 law，所以
(MPC.19) 良定义且满射。$\square$

若某个视图不满足动态充分性，并且

$$
\sim_{\mathscr T}\subsetneq\ker e_i,
\tag{MPC.20}
$$

则它把未来可区分的来源合并，不能承载无损的最小预测更新；仅对视图值作后处理
不能补回已合并的区别。这是动态充分性的失败诊断，不与定理 4.1 的前提并列。

(MPC.15) 是“状态层互相恢复”的准确含义。它不要求 $C_{\mathscr T}$ 等于
逆极限 $L_A$；若存在虚拟 law 线程，运输可先在真实像 $B_A$ 上成立，再在
完成空间上额外声明延拓。

### 4.2 有限层视图和 bonding 自然性

若每层有视图

$$
e_{i,n}:Q_n\longrightarrow Y_{i,n}
$$

并且满足

$$
\delta_{i,n}e_{i,n+1}=e_{i,n}p_n,
\tag{MPC.21}
$$

同时有 $K_n\subseteq A_n^{\mathrm{law}}$，则可直接在 $Q_n$ 上定义诱导关系

$$
x\,\bar A_n\,y
\iff
\exists z,u\in Z:\ q_n(z)=x,\ q_n(u)=y,\ z\,A_n^{\mathrm{law}}\,u.
$$

由于 $A_n^{\mathrm{law}}$ 是等价关系且包含 $K_n$，这个定义与代表元选择无关。
若还要让联合更新 law、selector、权限和记录在该关系上下降，则需另加联合核的
lumpability 与 bonding 自然性；那是动力学运输条件，不是定义 $\bar A_n$ 的前提。
于是可在每层使用 (MPC.15) 的相应 law 残余版本。若四个视图满足
$\ker e_{i,n}=\bar A_n$ 对所有 $i$，且完整联合核、selector、档案和权限更新都沿
$\chi_{ji,n}$ 运输，则它们给出 JKT 所要求的自然图册。逐层双射而不满足
(MPC.21)，不能定义逆极限上的视图运输；只运输一个边缘读数，也不能保持
自适应策略树。

## 5. 完成空间中的虚拟预测线程

law 完成空间 $L_A$ 可能严格大于真实像 $B_A$。在把
$A_n^{\mathrm{law}}$ 取为联合核线程卷整数窗口观察所对应的 law 残余，并在该
实例中把这些有限窗口读数声明为完整测试时，有限窗口的全零线程对每个有限层都出现，但没有一个实际整数在所有窗口上同时为零。
因此该实例中存在

$$
\omega\in L_A\setminus B_A.
\tag{MPC.22}
$$

这个 $\omega$ 可以在完成空间上接受形式延拓更新，但没有实际来源代表元。它
也不是观察者自动可以读写的状态。若视图运输只在 $L_A$ 上陈述而不检查实际像
集中性，便会把完成点误当成现实来源。

这给出三层边界：

$$
\text{数学 law 完成 }L_A
\supseteq
\text{真实来源像 }B_A
\supseteq
\text{有限 acquisition 可读子集}.
\tag{MPC.23}
$$

每个包含都可能严格。最小预测商 $C_{\mathscr T}$ 与 $B_A$ 同构，但不必与
$L_A$ 同构，也不等于观察者当前已经存储的档案。

## 6. 预测状态不自动恢复执行历史

定理 4.1 只讨论来源配置的未来行为，不自动恢复到达该配置的有序路径。把
完整未来行为商的类型和合法边写成一个 typed residual graph $G$，以合法具名
操作为边，以可拼接的有序路径为态射，可得到路径范畴 $\operatorname{Path}(G)$。
对象层的双射 $\chi_{ji}$ 只有在同时给出保持源、靶、类型、具名操作和完整
边记录的边映射 $\widehat\chi_{ji}$ 时，才提升为路径范函子：

$$
\widehat\chi_{ji}(uv)=\widehat\chi_{ji}(u)\,\widehat\chi_{ji}(v),
\qquad
\widehat\chi_{ji}(\varepsilon_v)=\varepsilon_{\chi_{ji}(v)}.
\tag{MPC.23a}
$$

空间或边界视图通常先给出对象映射，时间视图给出路径上的 cocycle，记忆视图
给出有序转录。若缺少 $\widehat\chi_{ji}$，四视图仍可能在状态层互相恢复，却
不能声称它们运输了同一组执行路径。

设 $\mathcal P$ 是从固定根出发的合法有限路径，令

$$
F_0(w)=\bigl(\operatorname{end}(w),\tau_r(w)\bigr),
$$

其中 $\tau_r$ 是从固定根出发、下降到残余图的交换型加法 cocycle。若再有记忆视图
$m:\mathcal P\to M$，则联合历史读出为

$$
F(w)=\bigl(\operatorname{end}(w),\tau_r(w),m(w)\bigr).
\tag{MPC.24}
$$

约定 $\ker m$ 表示 $m$ 值相等所定义的路径关系。于是，在实际路径像上，历史能够被恢复的充要条件是

$$
\boxed{
\ker F_0\cap\ker m=\Delta_{\mathcal P}.
}
\tag{MPC.25}
$$

这是状态充分性之外的另一层条件。

已有的 typed residual cocycle 重构判据给出一个直接障碍：在有限强连通残余图
中，若某个回返点 $z$ 有两个满足 $uw\ne wu$ 的有序回返块（例如它们的首个具名边
不同），取根 $r$ 到 $z$ 的任一合法前缀 $p$，则 $puw$ 与 $pwu$ 都属于 $\mathcal P$，并且

$$
\tau_r(puw)=\tau_r(p)+\tau_z(u)+\tau_z(w)
=\tau_r(p)+\tau_z(w)+\tau_z(u)=\tau_r(pwu).
$$

因此 $puw$ 与 $pwu$ 具有相同终点和相同累计时间；若记忆只保留终点、时间或
它们的可交换函数，(MPC.25) 失败。在有限强连通图、每条边持续量严格为正且时间是实数加法 cocycle 的范围内，
单一有向命名环是终点加时间能够在全部有限路径上注入的既有判据。这个结论来自
[typed residual cocycle reconstruction](RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md)，
本卷只把它接到最小预测核心，不重复其完整证明。

最小的历史补充不是再增加一个任意标量，而是至少切开联合读出
$F_0$ 的碰撞类。若要恢复完整具名路径，记忆必须保留非交换的路径证书，或
一个在每个 $F_0$ 纤维上单射的编码。于是：

$$
\boxed{
\text{状态层四视图互相恢复}
\;\not\Rightarrow\;
\text{路径层四视图互相恢复}.
}
\tag{MPC.26}
$$

## 7. 统一桥的结论范围

在前缀穷尽、law 由完整有限转录决定、联合核细化满足
$K_n\subseteq A_n^{\mathrm{law}}$、视图满足动态充分性和 bonding naturality 的
条件下，可以按以下强度使用本卷：

1. $A_\infty^{\mathrm{law}}$ 是声明测试族的最小未来行为关系；
2. $C_{\mathscr T}=Z/A_\infty^{\mathrm{law}}$ 是最小预测核心；
3. $L_A$ 是其有限 law 阶段的数学完成，$B_A$ 是实际来源像；
4. $K_n=A_n^{\mathrm{law}}$ 时，JKT 的联合核塔就是最小预测塔；
5. 仅有 $K_n\subseteq A_n^{\mathrm{law}}$ 时，得到自然商映射
   $\Phi:L_K\to L_A$，但必须另证相容 lift 才能声称完成层满射；
6. 四个状态视图只有在 (MPC.15) 下才彼此唯一恢复；
7. 路径顺序还需 (MPC.25)，不能由状态商、累计时间或边界数值自动推出。

这些结论区分了四个常被混淆的问题：未来行为可识别、数学线程可完成、真实
来源可实现、观察者实际可取得。它们可以在同一个关系整体中同时研究，但没有
一个单独的熵值或坐标数能替代这些关系条件。

## 8. 限制

本卷没有证明一般不可数输出的测度延拓，没有处理量子通道或无限资源，也没有
把最小预测核心实现成固定有限存储。若测试族不前缀穷尽，(MPC.3) 只能对已声明
测试成立；若输出 law 不是由有限柱决定，需补充 sigma 代数和测度唯一性；若
selector、权限或记录读取隐藏了来源变量，则动态充分性失败。逆极限中的虚拟
线程只能作为数学完成点，不能据此提出物理对象或物理时空定律。

## 追加锚（本行以下为增补区）

## 9. 有限配置的同源取得合同

**定义 9.1（单次新增配置模型）。** 固定有限的具名事件集合 $E$ 和非空族
$\mathcal F\subseteq\mathcal P(E)$。每个 $C\in\mathcal F$ 都是允许的初始配置；
不另给初始大小、可达根或隐藏的入口限制。动作名就是 $e\in E$，其合法性和后继为

$$
\operatorname{En}(C)=\{e\in E\setminus C:C\cup\{e\}\in\mathcal F\},
\qquad
C\xrightarrow{e}C\cup\{e\}\quad(e\in\operatorname{En}(C)).
\tag{MPC.27}
$$

定义操作汇点族和非汇点族

$$
T=\{C\in\mathcal F:\operatorname{En}(C)=\varnothing\},
\qquad N=\mathcal F\setminus T.
\tag{MPC.28}
$$

这里只按单个事件的实际合法新增定义汇点；$\mathcal F$ 不必是下闭族、理想族或
从某个根逐步可达的族。来源在一次运行中只通过 (MPC.27) 改变，没有未记录的
来源切换或自主更新。

**定义 9.2（已安装读出和取得协议）。** 已安装的确定性平稳读出为
$r:\mathcal F\to Q$，有效符号集为 $Q_r=r(\mathcal F)$，其码表与
$(E,\mathcal F)$ 均为已知。入口时实际读出 $q_0=r(C_0)$；每次成功动作之后
实际读出 $q_j=r(C_j)$。配置不变时重读给出相同符号。观察者初始化与隐藏的
$C_0$ 无关，其后只能依据本次运行实际获得的交替记录

$$
h_j=(q_0,e_1,q_1,\ldots,e_j,q_j)
\tag{MPC.29}
$$

进行确定性决定：请求一个具名事件，或停止并返回一个声称的当前配置
$D\in\mathcal F$。内部存储和计算允许依赖已知模型、码表及这份记录，不允许
依赖与隐藏来源相关的时钟、建议或预存档案。每个决定须经有限计算给出。
禁止请求非法动作，也不提供拒绝探测、启用菜单查询、重置、来源副本或额外读数。
因此成功动作的标签是观察者自己请求并保留的标签，不是额外的来源输出。

称 $r$ **支持有限同源配置取得**，若存在一个这样的协议，使得对每个
$C_0\in\mathcal F$，本次实际运行的每个请求均合法，并在有限次成功新增后停止，
返回的 $D$ 恰等于停止时的实际配置。允许在已识别的非汇点提前停止；不要求把
每次运行推进到汇点。这里取得的是停止时的配置，初始配置的恢复由定理 11.1
给出，不包含入口以前的有序历史。

合法自适应识别的先例见
[van den Bos–Vaandrager，定义 9、16 及定理 6.1](https://arxiv.org/html/1907.11034v2)。
这些条目中的共同合法输入与识别图属于固定系统的识别问题；上述合同另行固定了
全部可初始进入的配置、单次新增、实际平稳读出和禁止非法请求的观察资源。
[Nonlinear Recut Memory，定理 6.4](RECURSIVE_RELATIONAL_OBSERVATION_NONLINEAR_RECUT_MEMORY.md#6-same-source-initialization-retention-and-safe-acquisition)
的纯成功标签回声合同没有这里的逐次 $r(C_j)$ 输出，故不能把安装读出当作免费
增加到那个合同中的输入。

## 10. 固定读出的取得判据与安装符号数

**定理 10.1（固定读出的有限取得判据；repo-derived）。** 在定义 9.1–9.2 下，
对任意给定 $r$，以下三项等价：

1. $r$ 支持有限同源配置取得，允许协议使用全部实际历史。
2. 每个非空非单元纤维 $B_q=r^{-1}(q)$ 都满足

   $$
   \bigcap_{C\in B_q}\operatorname{En}(C)\ne\varnothing.
   \tag{MPC.30}
   $$

3. 每个 $t\in T$ 的纤维恰为 $\{t\}$，而且对每个不含汇点的非空纤维，
   都有 (MPC.30)。

满足这些条件时，有一个下一动作只依赖当前读数的协议：在单元纤维立即解码并
停止，在其余纤维执行预选的共同启用事件。它对初始配置 $C_0$ 至多执行
$|E|-|C_0|$ 次成功新增。

**证明。** 先证必要性。取入口读数相同的非单元纤维 $B_q$。所有其中配置都可能
是实际初态，且观察者初始化相同。在第一次成功动作以前，没有别的来源相关输入。
所以有限的内部计算、重读和停止决定在这些初态上相同。若停止，返回的同一配置
不可能同时等于两个不同初态；若永不作出动作或停止，则违反有限终止。因此必须
请求同一个首事件 $e$。对每个 $C\in B_q$ 的安全性要求
$e\in\operatorname{En}(C)$，得到 (MPC.30)。这一步只约束首个决定，没有假设
一般协议会丢弃过去的记录。

若第二项成立，含汇点的纤维不能是非单元纤维；不含汇点的单元纤维自身的启用集
非空，故第三项成立。第三项也立即蕴含第二项。

对充分性，在每个非单元纤维选取一个共同事件 $a(q)$。这一步使用已有的
[DeterministicSafePolicyExistence，`deterministic_safe_policy_exists_iff`](../../../D5/S3/ConceptDynamics/Agency/DeterministicSafePolicyExistence.lean)
所表达的安全选择原则：状态取这些纤维中的配置，合法动作取
$\operatorname{En}(C)$，读出取 $r$ 的限制。该原则本身并非这里的新增结论。
在单元纤维停止并返回它的唯一配置；否则请求 $a(q)$，成功后读取新的 $r$。

每次所请求事件对实际配置合法，并且严格增加配置大小。因此非负整数
$|E|-|C|$ 每次减少一，不能无限继续。若协议尚未停止而实际配置已成为汇点，
第三项又保证其读数纤维是单元纤维，所以下次决定必停止。于是协议在所述次数内
正确停止，包括零步停止。$\square$

**定义 10.2（取得符号数和启用击中数）。** 在同一个固定模型上，只优化已安装
平稳读出的有效值域大小，定义

$$
\begin{aligned}
m(E,\mathcal F)
 &=\min\{|r(\mathcal F)|:r\text{ 满足定义 9.2 的取得要求}\},\\
\tau(E,\mathcal F)
 &=\min\{|H|:H\subseteq E,\quad
       H\cap\operatorname{En}(C)\ne\varnothing\ \text{对每个 }C\in N\}.
\end{aligned}
\tag{MPC.31}
$$

第一个最小值量化所有具有已知码表并已安装的确定性平稳读出，可任取其符号载体。
恒等读出可在入口停止，故可行类非空。第二个最小值也存在，因为 $E$ 击中每个
非空启用集；当 $N=\varnothing$ 时取 $H=\varnothing$，约定 $\tau=0$。

这一计数只计算 $|r(\mathcal F)|$，不计算传感器准备、模型或码表、保留的命令、
计算、总存储或物理时间。它不把一个尚未提供的读出算成观察者已经具有的端口，
也不规定如何从给定的较粗端口制造所优化的读出。

**定理 10.3（安装读出范围的精确最小值；repo-derived）。** 对每个定义 9.1 的
有限非空配置族，

$$
\boxed{m(E,\mathcal F)=|T|+\tau(E,\mathcal F).}
\tag{MPC.32}
$$

右侧既是所有可取得读出的下界，也由一个具有已知码表的平稳读出达到。

**证明。** 设 $r$ 可取得，$k=|r(\mathcal F)|$。由定理 10.1，每个汇点占据一个
独享的符号，共 $|T|$ 个。其余 $k-|T|$ 个非空纤维全部由非汇点组成，且各有
共同启用事件；单元非汇点纤维同样如此。从每个这样的纤维选取一个事件，并令
$H_r$ 为所有选出事件组成的集合。每个 $C\in N$ 都位于其中一个纤维，所以

$$
H_r\cap\operatorname{En}(C)\ne\varnothing,
\qquad
\tau\le |H_r|\le k-|T|.
\tag{MPC.33}
$$

从而 $k\ge |T|+\tau$，包括允许在非汇点单元纤维提前停止的读出。

反过来，选一个最小击中集 $H$。对每个 $C\in N$ 选
$f(C)\in H\cap\operatorname{En}(C)$，以两个互不相交的标签族定义

$$
r_H(C)=
\begin{cases}
(0,C),&C\in T,\\
(1,f(C)),&C\in N.
\end{cases}
\tag{MPC.34}
$$

汇点标签独享，标记为 $(1,e)$ 的每个配置都启用 $e$，故定理 10.1 保证取得。
其有效值域至多为 $|T|+|H|=|T|+\tau$。已证下界强制此数取等，因此该构造达到
最小值。若 $N=\varnothing$，第二分支没有自变量，构造就是对全部汇点的直接
编码，结论仍成立。$\square$

安全观察字母表与共同动作分区的一般等价已经由
[MinimumSafeObservationAlphabet，`supports_deterministic_safe_policy_iff_safe_compatible_partition` 和 `minimum_safe_observation_alphabet`](../../../D5/S3/ConceptDynamics/Agency/MinimumSafeObservationAlphabet.lean)
给出。这里复用该分区原则；(MPC.32) 的额外内容是本模型的可停止取得任务、
有限新增秩和启用超边击中数的组合计算。自动机极小性的另一已有结果是
[Kostolanyi，定理 4.16](https://arxiv.org/html/2303.10631v3)：正半环上的 trim
bideterministic 加权自动机是极小的。那个状态数极小性结论不承担这里对固定
$(E,\mathcal F)$ 的安装读出范围优化；一般的终态分离也不作为本节的独立新定理。

## 11. 已取得终点、保留新增与顺序的边界

**定理 11.1（同次运行的初态恢复；repo-derived）。** 设 $r$ 满足定理 10.1，
固定一个满足定义 9.2 的确定性取得协议 $\Pi$。对每个初态 $C_0$，记其实际
停止配置为 $D_\Pi(C_0)$，实际成功事件词为
$w_\Pi(C_0)=e_1\cdots e_k$，保留事件集合为
$A_\Pi(C_0)=\{e_1,\ldots,e_k\}$。则

$$
\begin{aligned}
D_\Pi(C_0)&=C_0\mathbin{\dot\cup}A_\Pi(C_0),\\
C_0&=D_\Pi(C_0)\setminus A_\Pi(C_0),\\
k=|A_\Pi(C_0)|&=|D_\Pi(C_0)|-|C_0|\le |E|-|C_0|.
\end{aligned}
\tag{MPC.35}
$$

因此，在实际像

$$
\mathcal I_\Pi
 =\{(D_\Pi(C),A_\Pi(C)):C\in\mathcal F\}
\tag{MPC.36}
$$

上，初态与“已取得终点、保留事件集合”互相恢复。若把全部实际交替记录与停止
答案记为 $h_\Pi(C)$，则 $\mathcal F$、$\mathcal I_\Pi$ 和
$\{h_\Pi(C):C\in\mathcal F\}$ 也两两双射；这些双射只针对固定的
$(E,\mathcal F,r,\Pi)$ 的实际像。

**证明。** 令 $A_j=\{e_1,\ldots,e_j\}$。在零步时
$C_0=C_0\mathbin{\dot\cup}\varnothing$。若
$C_j=C_0\mathbin{\dot\cup}A_j$，合法性给出 $e_{j+1}\notin C_j$，所以它既不在
初态中，也未出现于过去的成功事件。新增之后
$C_{j+1}=C_0\mathbin{\dot\cup}A_{j+1}$。归纳至停止得到分解、无重复性及所有
计数等式。这个界事实上适用于模型内的每条合法有限执行。

协议返回的 $D_\Pi(C_0)$ 已经取得，命令集合 $A_\Pi(C_0)$ 则可以从本次实际
成功命令保留，所以差集给出初态，无需重置来源。逆映射在 $\mathcal I_\Pi$ 上
明确为 $(D,A)\mapsto D\setminus A$，故初态到该像的映射是双射。

从给定初态出发，已知平稳读出和固定确定性协议唯一决定初始读数、每次请求、
后继读数和停止答案。于是初态决定完整记录；反向从完整记录取停止答案和成功
命令集合，再用差集恢复初态。对实际像点先恢复初态，再按已知模型与协议作数学
重演，即得原有记录。这是函数的求值关系，不是向实际来源申请另一份副本或再次
执行试验。$\square$

上述动作选择可以像定理 10.1 的构造那样只读当前符号；整个初态恢复过程仍须
保留 $A_j$ 或等价信息，并使用已取得的终点。动作选择器的这种无历史依赖性质
不把完整恢复协议变成只存当前符号的过程。

**命题 11.2（固定协议之外的精确顺序界与交换反例）。** 对任意一族合法有限执行
$\mathcal L=\{(C_0,w)\}$，令 $D$ 为执行终点、$A$ 为词中事件集合。读出记录由
$C_0,w,r$ 确定。终点加事件集合能在 $\mathcal L$ 上恢复完整执行，当且仅当

$$
\forall C\in\mathcal F\ \forall A\subseteq E,\qquad
\#\{w:(C,w)\in\mathcal L,\ \operatorname{set}(w)=A\}\le1.
\tag{MPC.37}
$$

这一条件对固定取得协议的实际执行族成立，对全部合法执行族则可以失败。
特别地，令 $E=\{a,b\}$、$\mathcal F=\mathcal P(E)$、初态为
$\varnothing$，则 $ab$ 和 $ba$ 两条合法执行的终点、保留集合和步数均为

$$
(D,A,k)=(\{a,b\},\{a,b\},2),
\tag{MPC.38}
$$

而有序执行不同。对任意取值于交换幺半群的事件权重 $v$，累计量
$\sum_{e\in A}v(e)$ 也相同。

**证明。** (MPC.35) 的执行分解使 $(D,A)$ 先确定初态 $C=D\setminus A$。
在此初态上若 (MPC.37) 成立，就有唯一允许的事件顺序，后继配置与各次读数随之
确定。若它失败，两条不同的允许词有同一初态和事件集合，故也有同一终点，不能
由 $(D,A)$ 区分。固定协议的取得记录由初态唯一决定，故满足该条件；这个限定
不能推广到未固定控制选择的合法路径族。在 (MPC.38) 中两次新增均合法，词首
分别为 $a,b$，且集合并与交换型求和均不保留这个区别。$\square$

这正是在本模型中使用第 6 节历史核判据的范围：保留新增集合恢复初态，不自动
恢复自由的有序路径；定理 11.1 的顺序恢复还使用了已知的固定确定性协议。
入口以前的路径不属于 $w_\Pi$，即使入口配置已恢复，也没有因此取得它的过去。

## 12. 完整有限偏序理想族的精确值

**定理 12.1（有限因果切片的安装符号数；repo-derived）。** 设 $P$ 是有限偏序，
$n=|P|$。取 $E=P$，$\mathcal F=\operatorname{Down}(P)$ 为包括空集在内的全部
下闭子集。使用定义 9.1 的动作，并允许每个下闭子集作为未知初态，则

$$
\operatorname{En}(C)=\operatorname{Min}(P\setminus C),
\qquad T=\{P\},\qquad \tau=n,\qquad m=n+1.
\tag{MPC.39}
$$

结论包括 $n=0$：此时 $\mathcal F=\{\varnothing\}$，只需且必须有一个有效符号。

**证明。** 对 $e\notin C$，$C\cup\{e\}$ 下闭恰好要求 $e$ 的每个严格前驱已在
$C$ 中，这又等价于 $e$ 是补集的极小元。每个非空有限补集有极小元，所以唯一
汇点是 $P$，而 $P$ 本身的启用集为空。

为证击中数下界，对每个 $e\in P$ 定义

$$
C_e=P\setminus\mathord{\uparrow}e,
\qquad
\mathord{\uparrow}e=\{x\in P:e\le x\}.
\tag{MPC.40}
$$

$C_e$ 下闭：若 $x\in C_e$ 且 $y\le x$，则 $e\le y$ 会推出 $e\le x$，矛盾。
其补集 $\mathord{\uparrow}e$ 的唯一极小元是 $e$，所以
$\operatorname{En}(C_e)=\{e\}$。每个击中集都必须含有每个 $e$，故
$\tau\ge n$；取 $H=P$ 得反向不等式。由定理 10.3 得 $m=n+1$。
当 $P=\varnothing$，没有 $C_e$ 的约束，$N=\varnothing$、$\tau=0$，同一公式
给出 $m=1$。$\square$

这里的因果切片参数对应为：$P$ 是有限个事件**出现**及其前驱偏序，$C$ 是已发生
的下闭事件集，具名动作 $e$ 是一次新的出现，合法性是新鲜性加全部严格前驱已
发生，后继是 $C\cup\{e\}$；无冲突约束、重复出现或未记录自主事件。
事件配置和启用关系的先例见
[Winskel，Event Structures](https://www.cl.cam.ac.uk/~gw104/Winskel1987_Chapter_EventStructures.pdf)。
在仓内对应中，
[EnabledPathSwapConnectivity](../../../D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.lean)
的 `Enabled` 与上述合法性相同，`Exec` 对应相同具名新增路径；其 `result` 已给出
有限理想间的执行、线性扩张与合法相邻交换。
[ConfigurationPathTransport](../../../D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.lean)
中把 `compatible` 取为恒真，即得这里的下闭配置；其 `configurationIdealIso`、
`exec_exists_iff_subset` 和 `finite_history_clocks` 分别供应已有的理想完成、
执行存在性和路径计数关系。这些配置与路径结论在此复用；(MPC.39) 计算的是在
全部下闭初态未知时额外安装的平稳读出符号数，不是事件生成元数、路径记忆数或
物理时钟数。任意删减理想族或加入来源动作后，须重新计算实际启用集，不能直接
沿用 $n+1$。

## 13. 两个有限失配反例

**命题 13.1（最优基数不保证给定读出可取得）。** 令
$E=\{a,b\}$、$\mathcal F=\mathcal P(E)$。此模型的最优符号数为 $3$，但下表
的给定读出 $r_{\mathrm{bad}}$ 有三个有效符号且不支持取得。表中的
$r_{\mathrm{good}}$ 则达到最优值。

| 配置 $C$ | $\operatorname{En}(C)$ | $r_{\mathrm{bad}}(C)$ | $r_{\mathrm{good}}(C)$ |
| --- | --- | --- | --- |
| $\varnothing$ | $\{a,b\}$ | $u$ | $a$ |
| $\{a\}$ | $\{b\}$ | $v$ | $b$ |
| $\{b\}$ | $\{a\}$ | $w$ | $a$ |
| $\{a,b\}$ | $\varnothing$ | $u$ | $\ast$ |

**证明。** 这是两点反链的全部理想族，故定理 12.1 给出 $m=3$。坏读出的
$u$ 纤维是 $\{\varnothing,\{a,b\}\}$，没有共同启用事件。以该符号为入口既
不能安全请求事件，也不能正确返回两个不同配置，所以定理 10.1 排除取得。
好读出的 $a$ 纤维中两配置都启用 $a$，其余纤维单元，故可取得且恰有三个有效
符号。这也说明知道一个最优基数，不能替代检查给定码表的纤维。$\square$

**命题 13.2（操作汇点不同于包含极大配置）。** 在一般的定义 9.1 中，每个包含
极大配置都是操作汇点，反向不成立。特别地，取
$E=\{a,b\}$、$\mathcal F=\{\varnothing,\{a,b\}\}$，则

$$
T=\mathcal F,\qquad N=\varnothing,\qquad \tau=0,\qquad m=2,
\tag{MPC.41}
$$

而包含极大配置只有 $\{a,b\}$。

**证明。** 合法单次新增会产生一个严格更大的族内配置，所以包含极大者没有合法
新增。此例中两个单元集均不在 $\mathcal F$ 内，故从空集不能合法新增；满集
也无新鲜事件。两个配置都是汇点，虽有严格包含关系。初态可能是任一汇点，所以
读出必须区分两者；直接分别编码即可，给出 (MPC.41)。$\square$

## 14. 来源实例化与动态恢复的适用合同

**假设 14.1（从实际来源到有限配置的接口）。** 对一个待应用的实际来源，固定
允许比较与运行的完整状态集 $S$ 及非空实际初态集 $S_0\subseteq S$。来源、纪元、
参考和权限所需字段均属于状态或固定合同。若要恢复该完整状态，须给出单射
$\iota:S\hookrightarrow\mathcal F$，其在实际像上的逆码表以及每个事件 $e$ 对应的实际具名动作
$\widehat e$ 均为观察者已知，并满足

$$
\begin{aligned}
\widehat e\text{ 在 }s\text{ 合法}
 &\iff e\in\operatorname{En}(\iota(s)),\\
\iota(\widehat T_e(s))&=\iota(s)\cup\{e\}
 \quad\text{在合法域上},\\
\widehat r(s)&=r(\iota(s)).
\end{aligned}
\tag{MPC.42}
$$

动作后继留在 $S$ 中，事件名可由实际成功记录忠实保留；$\widehat r$ 是入口和
每次成功后确实可读的平稳端口。观察者还须满足定义 9.2 的初始化与输入限制，
运行中保持同一来源，不用未记录的更新、时钟或建议补充读数。
本接口合同不要求读出支持取得；常值实际读出也可满足 (MPC.42)，接口符合性
本身不保证成功取得。

若实际任务只恢复配置而非完整来源，则可以改用非单射 $\iota$，但此时结论只
关于 $\iota(s)$。若实际初态像 $\iota(S_0)$ 严格小于 $\mathcal F$，则定理 10.3 关于
**全部** $\mathcal F$ 初态的下界不自动成为该受限入口任务的下界。

**命题 14.2（条件运输及其缺项）。** 在假设 14.1 的单射合同下，若 $r$ 满足
定理 10.1 的等价条件，并固定一个相应的定义 9.2 取得协议，则该协议可逐步
运输为同次实际来源运行，并取得停止状态 $s_k$；同时由已取得的
$D=\iota(s_k)$ 与保留集合 $A$ 恢复初始状态

$$
s_0=\iota^{-1}(D\setminus A).
\tag{MPC.43}
$$

若 $\iota(S_0)=\mathcal F$，且入口时无额外来源信息，则每个满足此合同且支持
有限同源取得的实际已安装读出至少需要 $|T|+\tau$ 个有效符号；这里要求存在
同一个协议，在定义 9.2 的信息限制下，对每个 $s_0\in S_0$ 均安全、正确且
有限终止地取得停止状态。保留实际成功新增集合 $A$ 时，这等价于同样要求下的
初态恢复：由 $D=\iota(s_0)\mathbin{\dot\cup}A$，两种答案通过差集和并集互换。
若另外确有一个 (MPC.34) 的最优读出由实际可读的 $\widehat r=r_H\circ\iota$ 实现，则此下界
也在实际来源上达到。安装读出的数学构造不推出任何端口的实现或制造方法。

**证明。** 固定上述取得协议，入口读数按 (MPC.42) 相同。若已经沿同一记录
运行至 $s$，配置协议选择的事件在 $\iota(s)$ 合法，故实际动作合法，且后继映到
所需新增配置；实际下一读数也相同。归纳运输每个决定、停止及步数界。停止时取得 $D$，由单射可
解码 $s_k$。定理 11.1 保证 $D\setminus A=\iota(s_0)$，所以 (MPC.43) 在实际
像上有定义。对下界所量化的每个实际读出，取其对所有 $s_0\in S_0$ 成功的
安全有限取得协议。$\iota(S_0)=\mathcal F$ 且无额外入口信息时，每个配置都
对应一个实际可能初态；把实际读出及这个协议沿双射反向运输，就得到定义 9.2
的取得协议，且有效符号数不变，故定理 10.3 给出下界。若最优读出另已满足实际端口
合同，则其取得构造按上述归纳运输，给出达到下界的实际协议。$\square$

假设中的端口等式是独立的数据。如果观察者已有的端口为 $p:S\to V$，要仅靠
该端口后处理得到所需的 $\widehat r$，还须有一个在实际像上定义的函数 $f$ 使
$\widehat r=f\circ p$，即 $\ker p\subseteq\ker\widehat r$。例如在命题 13.1
的模型中，常值端口无法经后处理产生任何三值最优读出。安装读出范围的最优值
没有补上这个实现条件。

FIB 的 $\alpha,\beta$ 生成记号本身没有指定 (MPC.42) 的嵌入、保持合法域的
动作对应或实际传感端口。把本节用于任意这样的来源，必须另外提供这些数据；
事件出现集 $E$ 也不能仅由两个生成记号替代。
[Process Geometry，第 33–43 节](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md#33-根标记历史的端点核与展开图拼接)
的实际来源、取得码、路径和视图接口保留各自条件，不能由 (MPC.32) 填入未给出的
来源实例或读出。这里的 $r$ 只需为取得策略提供安全下一步，不要求每个其他动作
的合法性和后继都在 $r$ 的纤维上不变。因此它不自动满足第 4 节的动态充分视图
条件；本模型的初态恢复与固定协议记录双射不蕴含四视图等价或物理表达的等价。

## 追加锚（本行以下为增补区）

## 15. 安全取得对自主来源摘要的刚性

**定义 15.1（保留读出的共同合法稳定摘要）。** 固定定义 9.1–9.2 的同一个
$(E,\mathcal F,r)$。来源摘要是映射 $s:\mathcal F\to V$。称它保留读出并在
共同合法事件下稳定，是指存在 $\rho:s(\mathcal F)\to Q_r$，使

$$
\begin{aligned}
r&=\rho\circ s,\\
s(C)=s(D),\quad e\in\operatorname{En}(C)\cap\operatorname{En}(D)
&\Longrightarrow s(C\cup\{e\})=s(D\cup\{e\}).
\end{aligned}
\tag{MPC.44}
$$

第二行只要求同一个事件在两个代表都合法时有相同后继摘要，没有假设
$\operatorname{En}(C)=\operatorname{En}(D)$。它使合法后继摘要可由旧摘要与事件名
确定，而不以新传感符号为额外输入；它本身没有给摘要赋予判断全部合法域的能力。
这里的 $s(C)$ 是来源状态的数学摘要，不假定观察者能从入口的 $r(C)$ 取得它。

**定理 15.2（单次新增来源的取得刚性；repo-derived）。** 在定义 9.1–9.2
不变的合同下，若 $r$ 支持对每个 $C_0\in\mathcal F$ 的有限同源当前配置取得，
则每个满足 (MPC.44) 的 $s$ 都是单射。因此，这类来源摘要的精确最小有效值域
大小为 $|\mathcal F|$，即使没有预先要求摘要保留完整合法域。

**证明。** 固定一个对全部初态安全、正确且有限终止的取得协议。设
$s(C)=s(D)$，分别把 $C,D$ 作为入口配置。入口读数相同。若截至某步的实际记录
相同，协议具有同一停止决定或请求同一事件；请求时，两个初态都在协议的安全性
量词内，故该事件在两个当前配置共同合法。(MPC.44) 给出相同后继摘要，继而给出
相同的新读数。因此两次运行一直具有相同实际记录与摘要。由在 $C$ 上的有限终止，
两次运行在同一步停止并返回同一配置 $U$；正确性使两个实际终点都为 $U$。

记这份共同记录中的成功事件集合为 $A$。直接使用定理 11.1 的单次新增分解，

$$
U=C\mathbin{\dot\cup}A=D\mathbin{\dot\cup}A,
\qquad C=U\setminus A=D.
\tag{MPC.45}
$$

故 $s$ 单射。恒等摘要 $s(C)=C$ 保留 $r$，也满足共同合法稳定性，达到所述
基数。这个证明没有调用某个事件仅在一边合法时的响应，没有使用拒绝探测，也不
需要统一的运行步数上界。$\square$

安全策略的纤维选择原则由第 10 节引用的
[DeterministicSafePolicyExistence](../../../D5/S3/ConceptDynamics/Agency/DeterministicSafePolicyExistence.lean)
和 [MinimumSafeObservationAlphabet](../../../D5/S3/ConceptDynamics/Agency/MinimumSafeObservationAlphabet.lean)
供应；这里额外使用的是实际取得协议与 (MPC.45) 的可消去性。一般的更新加记录
可逆判据已有
[ExactRollbackInjectivityCriterion，`exact_rollback_iff_joint_record_injective`](../../../D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion.lean)。
上述推导不是另立一般逆定理，而是证明这一来源上任何保留可取得读出的共同合法
稳定摘要都已经分离配置。

**命题 15.3（刚性假设的三个有限界限）。** 下列三个弱化都不保证定理 15.2。

1. 保持有限配置和单次新增，但只要求对一个真子初态族取得。
2. 允许向已经含有该事件的配置再次执行同名插入。
3. 不要求摘要保留读出。

**证明。** 对第一项，取 $E=\{a,b\}$、$\mathcal F=\mathcal P(E)$，令
$r(C)=s(C)=\mathbf1_{\{b\in C\}}$，只允许
$\mathcal I=\{\varnothing,\{b\}\}$ 作为入口。读数在 $\mathcal I$ 上已精确
解码当前配置，故零步取得成功；$s$ 在全部 $\mathcal F$ 上却非单射。共同合法的
$a$ 不改变 $s$，共同合法的 $b$ 都把 $s$ 变成一，故共同合法稳定性成立。
特别地，$\varnothing$ 与 $\{a\}$ 的摘要相同，但 $a$ 只在前者合法。
若将全部 $\mathcal F$ 恢复为可能初态，则读数一的纤维含汇点 $E$ 和
$\{b\}$，不能取得。这同时展示了共同合法稳定性与完整合法域下降的差别。

对第二项，取 $E=\{a\}$、两个配置 $\varnothing,\{a\}$，改为允许在两者上
执行 $a$，后继都为 $\{a\}$。常值读出与常值摘要稳定；统一执行一次 $a$ 后
返回 $\{a\}$，便对全部初态安全地取得当前配置。两个初态被同一动作合并，
所以 (MPC.45) 的差集恢复失效。协议本身只执行一次动作，仍不能挽救结论；关键
是事件对当前配置的新鲜性及由此得到的共同词可消去性，而不只是限制协议长度。
相反，若某个其他模型的共同合法词作用确实可消去，同一证明仍可适用，重复操作
这一名称本身并不构成反例。

对第三项，在任意含两个配置的定义 9.1 模型中取恒等读出、常值摘要。入口即可
取得配置，常值摘要在共同合法事件下稳定，但没有保留这个读出。$\square$

## 16. 最小缺失端口的实际前缀与自足边界

**定义 16.1（独立事件、最小缺失符号与安全前缀）。** 固定整数 $m\ge0$，令
$E=[m]=\{1,\ldots,m\}$、$\mathcal F=\mathcal P(E)$，事件间无因果约束。
这里的线性次序只是固定的具名事件查询次序。把饱和符号记作 $\top=m+1$，安装

$$
r(C)=\min\bigl((E\setminus C)\cup\{\top\}\bigr).
\tag{MPC.46}
$$

每个配置仍是可能初态。令 $\mathcal H_m$ 为从这些入口通过均匀安全请求产生的
全部实际有限交替前缀，包括零动作前缀；均匀安全指所请求事件在与已有完整记录
相容的每个当前配置上都合法。允许在任意前缀停止，停止不追加事件。一个前缀
$h=(q_0,e_1,q_1,\ldots,e_k,q_k)$ 的相容来源关系定义为

$$
\mathcal R_h=\{(C_0,C_k):\text{从初态 }C_0\text{ 的同次合法执行产生 }h\}.
\tag{MPC.47}
$$

关系中的初态和终点来自同一执行；两个投影的自由乘积不是这个关系。这里只保留
入口以后的成功动作和实际读数。$(E,r)$ 及来源接口身份固定，变化的隐藏配置不是
给观察者的输入。对一组初态同时安全的策略概念沿用定义 9.2；事件作为具名出现
及配置的先例沿用第 12 节引用的
[Winskel，Event Structures](https://www.cl.cam.ac.uk/~gw104/Winskel1987_Chapter_EventStructures.pdf)。

**定理 16.2（安全前缀的实际关系正规形；repo-derived）。** 对每个
$h\in\mathcal H_m$，设 $t=q_k$、$A=\{e_1,\ldots,e_k\}$，并令

$$
L_t=\{i\in E:i<t\},\qquad U_t=\{i\in E:i>t\}.
\tag{MPC.48}
$$

则有 $A\subseteq L_t$，前缀的成功事件严格递增，且

$$
\mathcal R_h
=\{((L_t\setminus A)\cup X,\ L_t\cup X):X\subseteq U_t\}.
\tag{MPC.49}
$$

若 $t\le m$，唯一均匀安全的下一事件是 $t$；执行后每个
$u\in\{t+1,\ldots,m+1\}$ 都是某个相容实际来源的新读数。若 $t=\top$，
没有合法事件。反过来，每个 $1\le t\le m+1$ 和 $A\subseteq L_t$ 都恰好
给出一个实际前缀，其读数序列是 $A\cup\{t\}$ 的递增排列，每个成功动作等于
它之前的读数。因此

$$
\mathcal H_m\ \cong\ \{(A,t):1\le t\le m+1,\ A\subseteq L_t\},
\qquad |\mathcal H_m|=\sum_{t=1}^{m+1}2^{t-1}=2^{m+1}-1.
\tag{MPC.50}
$$

**证明。** 零动作前缀的读数为 $t$ 时，初态和当前配置相同，恰为
$L_t\cup X$，其中 $X\subseteq U_t$；若 $t\le m$，事件 $t$ 不在配置内。
故 (MPC.49) 在 $A=\varnothing$ 时成立。

假设 (MPC.49) 成立且 $t\le m$。所有相容当前配置都含 $L_t$，都不含 $t$；
对任意 $i>t$，其中既有含 $i$ 的配置，也有不含 $i$ 的配置。故共同合法事件
恰为 $t$。成功插入 $t$ 后，若新读数为 $u>t$，旧 $X$ 必须在 $t$ 与 $u$
之间全部占据、在 $u\le m$ 时不含 $u$，而大于 $u$ 的部分仍任意。于是新初态
和当前配置恰为

$$
\bigl((L_u\setminus(A\cup\{t\}))\cup Y,\ L_u\cup Y\bigr),
\qquad Y\subseteq U_u.
\tag{MPC.51}
$$

每个允许的 $u$ 都能这样选择 $X$ 得到。饱和时 $L_{\top}=E$、
$U_{\top}=\varnothing$，唯一当前配置为 $E$，没有合法新增。归纳给出全部关系
公式、唯一安全动作和递增性。反向，给定 $A\subseteq L_t$，取初态
$L_t\setminus A$，依次插入 $A$ 的递增排列，便产生所称前缀；所有这些请求
都是刚证出的共同安全动作。任取 $X\subseteq U_t$ 不改变此前的读数，所以
(MPC.49) 中每对配置都实际实现。读数序列和动作序列又被 $(A,t)$ 唯一确定，
证明双射及计数，包括 $m=0$ 的单个零动作饱和前缀。$\square$

**定义 16.3（自足的取得边界合同）。** 对定义 16.1 的完整前缀族，一个边界
由映射 $b:\mathcal H_m\to B$、固定初始化 $J:Q_r\to B$、读出解码
$\rho:B\to Q_r$、事件菜单 $\mathsf{Safe}:B\to\mathcal P(E)$、更新
$U:B\times E\times Q_r\rightharpoonup B$ 及饱和解码器 $D$ 组成，要求：

1. $b((q_0))=J(q_0)$ 且 $\rho(b(h))$ 等于 $h$ 的当前读数。
2. $\mathsf{Safe}(b(h))$ 恰为 $\mathcal R_h$ 的所有当前配置共同合法的事件集。
3. 对每个该菜单内的 $e$ 和每个实际可能的新读数 $q'$，更新有定义且
   $b(h,e,q')=U(b(h),e,q')$；更新只能使用旧边界、实际成功事件名及新取得符号。
4. 当 $\rho(b(h))=\top$ 时，$D(b(h))=C_0$ 对每个产生 $h$ 的实际初态成立。

所有未来决定及恢复所能读取的持久来源信息均经 $b(h)$；完整旧档案、步数、
控制模式和旧读数若另存且可读，也属于这个联合边界，不能作为免费辅助输入。
模型、码表与事件次序固定且已知。计数对象是全部已取得前缀上的
$|b(\mathcal H_m)|$，包含其保留的当前读数；不把瞬时新输入、计算步骤或程序
长度等同于这个状态类数。这个合同支持全部均匀安全续接，不只选定某个初态或
删去不便的响应分支。它只要求饱和时恢复入口配置，不预设能恢复完整前缀。

**定理 16.4（自足边界的精确前缀代价；repo-derived）。** 定义 16.3 中的
边界必在 $\mathcal H_m$ 上单射，其精确最小有效值域为

$$
\boxed{\min_b |b(\mathcal H_m)|=2^{m+1}-1.}
\tag{MPC.52}
$$

此值由仅保留实际读过的不同符号集合达到；边界更新使用新取得的符号，不是
定义 15.1 那种不获新符号的来源摘要更新。

**证明。** 先证下界。若两个前缀边界相同，由读出解码，它们有同一当前读数
$t$。用定理 16.2 写为 $(A,t)$ 与 $(A',t)$。若 $t=\top$，饱和解码器分别
须返回 $E\setminus A$ 与 $E\setminus A'$，故 $A=A'$。

若 $t\le m$，分别选取 (MPC.49) 中的 $X=U_t$。两个前缀都具有这样的实际
初态，分别为 $E\setminus(A\cup\{t\})$ 和
$E\setminus(A'\cup\{t\})$。下一事件 $t$ 在两个前缀上均匀安全，并在这两个
实际来源上产生相同的新符号 $\top$。边界更新收到相同三项输入
$(b,t,\top)$，故给出相同饱和边界。解码正确性于是迫使
$A\cup\{t\}=A'\cup\{t\}$；由 $A,A'\subseteq L_t$ 消去 $t$，得 $A=A'$。
故边界单射，(MPC.50) 给出下界。这里的共同新符号是每条完整实际前缀真正允许
的响应，不是从分别可达的边缘中虚构同一续接。

为达到下界，取所有非空 $S\subseteq[m+1]$ 为边界值。初始化为 $S=\{q_0\}$，
读数为 $\max S$。若 $t=\max S\le m$，菜单是 $\{t\}$；收到实际成功事件
$e=t$ 和新符号 $u>t$ 后设

$$
U(S,t,u)=S\cup\{u\}.
\tag{MPC.53}
$$

饱和时菜单为空，且

$$
D(S)=E\setminus(S\setminus\{\top\})\qquad(\max S=\top).
\tag{MPC.54}
$$

由定理 16.2，始终有 $S=A\cup\{t\}$，旧的当前缺失符号 $t$ 在下一步成为
成功新增事件。因此这些更新只保留实际获得的数据，菜单与饱和解码均正确。
每个非空 $S$ 都由 (MPC.50) 的一个前缀实现，达到下界。$\square$

下界使用的“相同存储经相同可读续接不能返回不同答案”是成熟的自动机区分续接
方法；合法自适应识别及其注入分裂条件见
[van den Bos–Vaandrager，定义 9、16、引理 11 和定理 6.1](https://arxiv.org/html/1907.11034v2)。
这几个条目不直接计算 (MPC.52)。本节的额外内容是最小缺失端口的实际前缀族、
只用共同安全事件的饱和分离证人，以及自足访问合同下的精确达到构造。
[ControlledBehaviorUniversality，`controlled_behavior_universal_property`](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean)
供应总确定动作系统的行为商极小性，不能把其总动作假设直接用于本节部分合法的
动作与新符号输入。上述普通数学推导不以一般商极小性本身作为新增结论。

## 17. 取得记录、来源关系与空间恢复的精确差别

**定理 17.1（实际前缀的关系恢复及其空间盲区；repo-derived）。** 在定义
16.1 的同一来源接口上，以下三个实际像与定理 16.4 的达到边界两两互相恢复：
完整交替前缀 $h$；事件的具名来源分类；同次执行的初态—当前配置关系
$\mathcal R_h$。来源分类具体是 $E$ 的有序四分区

$$
\begin{aligned}
P_h&=L_t\setminus A &&\text{已知入口时已有},\\
A_h&=A &&\text{本次成功新增},\\
N_h&=\{t\}\cap E &&\text{当前已知缺失},\\
W_h&=U_t &&\text{仍未确定}.
\end{aligned}
\tag{MPC.55}
$$

每个保持读出、续接和饱和恢复的自足边界也能恢复这些实际前缀对象。反之，
这些对象不总能确定实际初态或当前空间配置：当 $1\le t\le m$ 时，关系中恰有
$2^{m-t}$ 个初态和同样多个当前配置；当 $t=\top$ 时两者均唯一。因此精确
空间恢复恰在 $U_t=\varnothing$ 时成立，包括 $t=m$ 的未饱和情形。

**证明。** 由前缀取 $A,t$ 得分类、(MPC.49) 和 $S=A\cup\{t\}$。由 $S$
先取 $t=\max S$、$A=S\setminus\{t\}$，再将 $A\cup\{t\}$ 递增排列。
将最后一项之前的每个符号同时作为其后的成功事件，就唯一重建完整交替前缀。
这是由共同安全性强制的顺序，不是把一般无序新增集合当作自由路径的逆码；
命题 11.2 的 $ab/ba$ 反例依然适用于其他允许路径族。

由分类取 $A=A_h$；若 $N_h$ 非空则 $t$ 为其唯一元素，否则 $t=\top$。
在该实际分类像上，$N_h=\varnothing$ 也给 $W_h=\varnothing$，不会出现一个
未确定尾部而没有当前缺失符号的虚构分类。于是分类恢复 $(A,t)$。

关系 (MPC.49) 非空。对其中任一对 $(C,D)$，由互不相交分解有

$$
D\setminus C=A,\qquad r(D)=t.
\tag{MPC.56}
$$

这些值不依赖选取哪一对，故整个关系作为集合也确定 $(A,t)$。这一逆码使用的是
由已取得前缀算出的可能来源关系，不是把其中的隐藏实际点 $(C_0,C_k)$ 授予
观察者。定理 16.4 已证明每个合格边界在这个有限前缀像上单射，故在自己的实际
像上也有唯一逆码，进而恢复上述对象。

最后，(MPC.49) 中的 $X\subseteq U_t$ 每取一个值，都有一个实际初态产生同一
完整前缀，且两个投影都随 $X$ 单射变化。当 $t\le m$ 时 $|U_t|=m-t$，得到
所列精确数目；当 $t=\top$ 时尾部为空。若尾部非空，取其中一个事件 $i$，
$X=\varnothing$ 和 $X=\{i\}$ 就是同读数、同成功历史、同边界却不同当前
配置和初态的两个实际实现。尾部为空时两投影确实唯一。$\square$

本定理的关系对象保留了具名事件、取得前后的位置和仍可变化的来源，不把一个
三字段重命名当作四视图定理：时间记录是实际有序交替前缀，来源分类是具名事件
的取得分区，边界是可更新的取得记录；空间在证据不足时只恢复为 (MPC.49) 的
相容配置关系，尚非其中某个实际配置。恢复关系不等于选择关系中的隐藏实际点。
这种实际像和访问范围区分复用
[Process Geometry，第 19、35、40–43 节](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)
的来源、端点取得和策略可见性条件，不把全部形式路径响应当作实际可取得输入。

**命题 17.2（三种精确基数与较弱压缩的失败）。** 对 (MPC.46) 的同一个固定
有限来源，三个不同任务的最小有效值域分别为

$$
\begin{array}{c|c}
\text{任务}&\text{有效值域大小}\\\hline
\text{支持安全取得的已安装平稳读出}&m+1\\
\text{保留该读出、共同合法稳定的来源摘要}&2^m\\
\text{定义 16.3 的自足取得边界}&2^{m+1}-1.
\end{array}
\tag{MPC.57}
$$

其中第一行由第 12 节供应，后两行不是它的另一种记号。当前读数不能一般作为
自主来源摘要；当前配置、当前读数加成功次数也不能一般作为自足取得边界。

**证明。** 定理 12.1 对 $m$ 点反链给第一行最优值。(MPC.46) 恰有 $m+1$
个有效符号，每个非饱和纤维共同启用其读数事件，所以由定理 10.1 达到这个值。
定理 15.2 和恒等来源摘要给第二行，定理 16.4 给第三行。$m=0$ 时三值皆一；
$m=1$ 时后两值分别为二和三，$m\ge2$ 时三行严格递增。

取 $m=2$。配置 $\varnothing$ 与 $\{2\}$ 的当前读数都是一，共同合法的事件
$1$ 之后，读数却分别为二与 $\top=3$。所以当前读数的三个值足以指导安全
取得，却不满足自主更新的 (MPC.44)。新取得符号正是边界更新不能省去的输入。

再取初态 $\{2\}$ 与 $\{1\}$。各自执行唯一安全首事件后，实际前缀分别为
$(1,1,\top)$ 和 $(2,2,\top)$。当前配置同为 $E$，当前读数同为 $\top$，
成功次数同为一，初态却不同。因此这些较弱读出均不能承担饱和初态恢复。
仅存当前配置在全部 $2^m$ 个饱和运行上都给同一个值 $E$，也不保留该任务的
来源区别。$\square$

**命题 17.3（外置可读档案改变的是访问合同）。** 若完整实际前缀始终作为外置
档案可读，则存在无需另外保留来源相关持久工作状态的安全饱和与初态恢复方法。
因此 (MPC.52) 不是对这种合同的额外工作状态下界。

**证明。** 每次决定读取档案末符号 $t$，若未饱和便请求事件 $t$，将实际新
响应追加到档案。饱和时从档案取成功事件集合 $A$，返回 $E\setminus A$。
定理 16.2 和 (MPC.54) 保证安全与正确。这个方法允许不受上述类数计数约束的
临时计算；其来源相关持久数据正是外置档案本身。若把所有可读持久信息重新合入
一个自足边界，档案的实际前缀像又有 (MPC.50) 的大小，与下界一致。
这与 [Nonlinear Recut Memory，第 3.4、6 节](RECURSIVE_RELATIONAL_OBSERVATION_NONLINEAR_RECUT_MEMORY.md)
的可消去来源、已取得初始化与纯回声输出区分相容；本节没有把其纯回声合同替换
成免费安装 (MPC.46) 的合同。$\square$

**定义 17.4（原来源的待证接合条件）。** 将本节有限结果用于未知 law、未知
cut 的原始 FIB 来源，所需接合仍是第 14 节的实际来源接口：由同一实际来源取得
并认证配置编码，保留来源与纪元身份，给出保持新鲜性、合法域和后继的具名动作
对应，并实现入口及每次成功后确实可读的 (MPC.46)。若身份本身可变且是恢复
目标，须把身份纳入配置编码或联合边界；固定接口的上述基数不计额外身份类数。
不同的 law、cut 或单次新增事件表不能按同一读数拼成一个实际来源。

这些数据尚未由本节的有限构造给出；一般阶 $d$ 的多项式总取得与原始
$K_d$ 的精确规范化也不属于 (MPC.52) 的结论。完整未来菜单、权限、实际档案与
吸收失败的共同取得要求仍保留
[Original Control Finite Handoff Boundaries，第 13 节](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_FINITE_HANDOFF_BOUNDARIES.md)
的范围。即使有限模型的入口配置已恢复，其入口以前的有序历史也没有进入
$\mathcal H_m$，不能由本节的互恢复关系推出。这里刻画的是一个已安装有限
端口中实际取得边界的精确关系与代价，不能据此断言原来源的空间、时间、边界和
记忆已经全部互相恢复。

## 追加锚（本行以下为增补区）

## 18. 已安装偏序端口的同次来源区间

**定义 18.1（线性扩张读序与全部安全前缀）。** 固定有限具名偏序
$P=([n],\le_P)$，$n\ge0$，使自然标号次序为一个线性扩张，即
$x<_P y$ 蕴含 $x<y$。每个 $C\in\operatorname{Down}(P)$ 都是允许的未知初态；
动作仍为新鲜且全部严格前驱已经发生的单次新增。固定已安装的平稳端口

$$
r(C)=\min\bigl(([n]\setminus C)\cup\{\top\}\bigr),
\qquad \top=n+1.
\tag{MPC.58}
$$

来源、初始化、实际输入和档案访问条件沿用定义 9.2、16.1、16.3，只把反链换成
这个偏序。记 $\mathcal H(P)$ 为包括零动作前缀在内的全部均匀安全实际前缀；
每次请求须在与此前完整记录相容的每个当前理想上合法，不只在选定的真实点上
合法。完整记录仍为 $h=(q_0,e_1,q_1,\ldots,e_k,q_k)$，其同次来源关系仍按
(MPC.47) 定义。置

$$
\begin{aligned}
A_h&=\{e_1,\ldots,e_k\}, &t_h&=q_k,\\
L_t&=\{i\in[n]:i<t\},
&\operatorname{Pred}(e)&=\{x:x<_P e\},\\
\mathord{\uparrow}A&=\{x:\exists a\in A,\ a\le_P x\},
&\mathord{\uparrow}\top&=\varnothing,\\
I(A,t)&=L_t\setminus A,
&J(A,t)&=L_t\cup A,\\
M(A,t)&=P\setminus
  (\mathord{\uparrow}A\cup\mathord{\uparrow}t).
\end{aligned}
\tag{MPC.59}
$$

对 $t\in[n]$，$\mathord{\uparrow}t$ 包含 $t$ 自身；$L_{\top}=P$。
$A$ 只记录本次已经支付并成功执行的事件，不能解释为入口前的全部发生历史。
本节与下文的区间、可达像、取得边界计数及反例是这个固定接口上的
`repo-derived` 综合推导。理想与合法执行的中间结构沿用第 12 节的来源，
不把一般理想表示或路径交换重新计作新增结论。

**定理 18.2（精确联合区间与全部安全菜单）。** 对每个 $h\in\mathcal H(P)$，
写 $A=A_h,t=t_h,I=I(A,t),J=J(A,t),M=M(A,t)$，则 $I,J,M$ 都是理想，
$I\subseteq M$，且 $t\notin A$。其同次初态—当前关系恰为

$$
\boxed{
\mathcal R_h=
 \{(C,C\cup A): C\in\operatorname{Down}(P),\ I\subseteq C\subseteq M\}.
}
\tag{MPC.60}
$$

其当前配置投影也恰为理想区间

$$
\operatorname{pr}_2\mathcal R_h
 =\{D\in\operatorname{Down}(P):J\subseteq D\subseteq M\cup A\}.
\tag{MPC.61}
$$

特别地，$J$ 和 $M\cup A$ 是确实相容于整条 $h$ 的当前配置。全部均匀安全
下一事件为

$$
\boxed{
\mathsf{Safe}(h)
 =\{e\in P\setminus(M\cup A):\operatorname{Pred}(e)\subseteq J\}.
}
\tag{MPC.62}
$$

若 $t\le n$，则 $t$ 总在菜单中。任何其他菜单事件 $e$ 均满足 $e>t$，并在
执行后保持读数 $t$；执行事件 $t$ 后读数严格增大。

证明。零动作读数为 $t$ 恰表示入口理想包含 $L_t$ 而不含 $t$。理想性把后者
扩为不含 $\mathord{\uparrow}t$，故 (MPC.60) 在 $A=\varnothing$ 时成立。
假设该式已经对一个实际前缀成立。所有相容初态都与 $A$ 不交，故其最小当前
配置是 $I\cup A=J$，最大当前配置是 $M\cup A$。新鲜性须在最大者上成立，
所有前驱已发生须在最小者上成立，正好得到 (MPC.62)。

$L_t$ 是理想，且所有 $t$ 的严格前驱均在 $L_t$，所以 $t\le n$ 时确实安全。
小于 $t$ 的标签已经发生，不能再次新增。若 $e>t$ 安全，它不能在
$\mathord{\uparrow}t$ 中，否则缺失的 $t$ 是尚未发生的严格前驱；因此
$e\in\mathord{\uparrow}A$。在此情形，新增 $e$ 不改变当前最小缺失标签，且
$\mathord{\uparrow}(A\cup\{e\})=\mathord{\uparrow}A$。
于是 $I,M$ 不变，所有旧相容初态仍产生新读数 $t$，得到下一步的 (MPC.60)。

若安全事件是 $e=t$，令实际新读数为 $u>t$、$A'=A\cup\{t\}$。
同一初态必须含有 $L_u\setminus A'$，而不含任何 $A'$ 中的事件，也不含
$u\le n$。对理想而言，这些条件恰为

$$
L_u\setminus A'\subseteq C\subseteq
P\setminus(\mathord{\uparrow}A'\cup\mathord{\uparrow}u).
\tag{MPC.63}
$$

它们也蕴含旧区间的条件：旧 $A$ 和旧缺失标签 $t$ 已包含在 $A'$ 的排除条件中，
旧下界包含在新下界中。故每个满足 (MPC.63) 的理想都产生整个旧记录及这次
实际回复，而非仅产生同一终点读数。反向条件由新读数及新鲜性已经得到，
归纳证明 (MPC.60)。

下界 $I$ 的理想性也可直接看出：一个已知入口时存在的事件，其前驱不可能是
入口时缺失而在本次新增的事件。$J$ 在安全新增下保持理想，读数跳跃只再并入
理想 $L_u$。$M$ 是上闭集之补，故为理想。实际来源使区间非空。

对 (MPC.61)，从 (MPC.60) 取并集得到一个方向。反向，若理想 $D$ 位于所示
区间，则 $C=D\setminus A$ 包含 $I$ 且包含于 $M$。若 $x\in C$ 的前驱
$y$ 在 $A$ 中，则 $x\in\mathord{\uparrow}A$，与 $x\in M$ 矛盾；故
$C$ 本身是理想。于是 $(C,D)$ 属于 (MPC.60)。特别地两端理想都有同次来源
实现，完成归纳中所用的极值论证。$\square$

**定理 18.3（可达条件、来源不确定性与实际点恢复）。** 一对
$A\subseteq P,\ 1\le t\le n+1$ 来自某个 $h\in\mathcal H(P)$，当且仅当

$$
\begin{gathered}
t\notin A,\qquad
L_t\setminus A\in\operatorname{Down}(P),\qquad
L_t\cup A\in\operatorname{Down}(P),\\
\operatorname{Min}_P(A)\subseteq L_t.
\end{gathered}
\tag{MPC.64}
$$

最后一项等价于 $A\subseteq\mathord{\uparrow}(A\cap L_t)$。
在这个可达像上，$(A,t)$ 与整个关系 $\mathcal R_h$ 两两互相恢复。
初态投影、当前投影的精确大小都为

$$
|\operatorname{Down}(M\setminus I)|,
\tag{MPC.65}
$$

其中差集取诱导偏序；实际初态与实际当前配置可由完整已获前缀唯一恢复的充要
条件同为 $I=M$。

证明。定理 18.2 给出前三项。取 $A$ 的一个偏序极小元 $a$，考察它被执行前的
实际记录。若它不是当时的最小缺失标签，由 (MPC.62) 的证明，它位于某个此前
已插入事件的上方，违反 $a$ 在最终 $A$ 中极小。因此它曾作为当前缺失标签被
执行，此后读数严格增大，故 $a<t$。有限性给出最后两种写法的等价。

反向，假设 (MPC.64)。理想 $I=L_t\setminus A$ 不含 $A$ 或 $t$，因此也不含
它们的任何后继，即 $I\subseteq M$。从实际入口 $C_0=I$ 出发，先按自然标签
递增顺序插入 $A\cap L_t$。每次所插入者正是当时的最小缺失标签，所以均匀
安全。若 $t\le n$，此时读数为 $t$。再按自然标签递增顺序插入 $A\setminus L_t$。
其中每个事件均有一个已插入的 $A\cap L_t$ 中的祖先，所以由新鲜性与理想性
可知它在每个相容初态中缺失；它的严格前驱属于理想 $L_t\cup A$，且标号更小，
故已全部发生。因而这些请求也均匀安全，并保持读数 $t$。$t=\top$ 时没有这个
第二阶段。这样确实到达 $(A,t)$。所有位于 $[I,M]$ 的初态只在 $t$ 以上的
未插入事件处有差别，不改变这个构造的任何读数，故所需区间内的所有对均来自
完整实际前缀。

从关系中任一对 $(C,D)$ 都能取回 $D\setminus C=A$ 和 $r(D)=t$；关系非空，
这些值对选取的对无关。反向由 (MPC.60) 求关系，证明互恢复。

标准理想区间对应在这里具体为

$$
X\in\operatorname{Down}(M\setminus I)
\longmapsto (I\cup X,\ I\cup A\cup X).
\tag{MPC.66}
$$

$I,M$ 都是理想，所以这确实枚举 (MPC.60)，并在两个投影上都是单射。
若 $I=M$，只余一个实际点；若 $I\ne M$，取 $X=\varnothing$ 与
$X=M\setminus I$，得到同一完整前缀的两个不同初态和两个不同当前配置。
因此恢复可能来源关系没有自动选择其中的隐藏实际点。$\square$

## 19. 续接稳定的任务边界与共同当前分离

**定义 19.1（全安全续接的入口恢复边界）。** 在定义 18.1 的固定接口上，
边界合同沿用定义 16.3：从入口实际读数初始化，解码当前读数与完整的均匀安全
菜单，对每个菜单事件和每个确实可能的新读数，以
$U(b(h),e,q')$ 更新，并在饱和时准确恢复本次运行的入口理想。
所有以后可读的来源相关持久信息均经 $b$；若旧档案、控制状态、步数或原始种子
可读，它们也属于联合保留信息。新传感符号是更新的实际输入，不是旧边界已经
包含的值。合同没有要求由旧边界预测全部可能新符号，更没有假定一个隐藏来源
分布或要求预测其 law。

**定理 19.2（联合关系边界及共同当前分离判据）。** 在定义 19.1 下，
$(A_h,t_h)$ 是一个合格边界。其初始化、更新和饱和解码可取

$$
\begin{aligned}
J_0(q)&=(\varnothing,q),\\
U((A,t),e,u)&=(A\cup\{e\},u),\\
D(A,\top)&=P\setminus A,
\end{aligned}
\tag{MPC.67}
$$

菜单由 (MPC.62) 求出。另一方面，对任意两个完整实际前缀 $h,g$，若
$A_h\ne A_g$ 且

$$
\operatorname{pr}_2\mathcal R_h\cap
\operatorname{pr}_2\mathcal R_g\ne\varnothing,
\tag{MPC.68}
$$

则每个合格边界都满足 $b(h)\ne b(g)$。
不同当前读数或不同完整安全菜单也必被每个合格边界区分。

证明。定理 18.2 保证读数和菜单只依赖 $(A,t)$。更新使用实际成功事件及新
读数，所以 (MPC.67) 在所有实际分支上成立。饱和时当前配置恰为 $P$，由单次
新增分解，入口为 $P\setminus A$。这不要求事先取得入口，给出达到构造。

为证分离，取 (MPC.68) 中的一个共同当前理想 $D$。必须使用两条关系中的实际
配对：它们分别是 $(D\setminus A_h,D)\in\mathcal R_h$ 和
$(D\setminus A_g,D)\in\mathcal R_g$。这使各自完整旧记录和同一当前配置
同时相容，所需入口理想不同。若 $D=P$，饱和解码已直接区分它们。

若 $D\ne P$，在两条完整记录之后，每次都请求实际当前读数所名指的事件。
定理 18.2 保证这在各自整条记录的每个相容来源上均匀安全，而非仅在选出的
$D$ 上合法。两次实际来源从同一个当前 $D$ 出发，受同一动作影响后仍相同，
因此逐次收到同一个实际新读数，有限次后共同达到 $P$。
若旧边界相同，更新在每一步收到相同的 $(b,e,q')$，终端边界也相同，却须返回
两个不同入口，矛盾。这里共同续接的存在由同一实际当前点和逐步安全性给出，
没有把两个分别可能的边缘响应拼成一条虚构共同历史。
读数和菜单的最后断言直接由解码要求得到。$\square$

这个判据复用合法区分续接的成熟方法。
[van den Bos–Vaandrager，定义 9、16、引理 11、定理 6.1](https://arxiv.org/html/1907.11034v2)
要求测试输入在相关候选状态上合法并覆盖所允许的输出；引理 11 与定理 6.1
另有所有不同状态对均不相容的前提。这里直接证明所用的同次来源见证与共同
安全续接，不把那个额外前提或其完整识别算法当作本接口已满足的条件。
(MPC.68) 是分离的充分条件，不是任意偏序上边界不可合并的完整判据。

## 20. 一条链与一个独立事件的精确代价

**定义 20.1（固定安装次序的链族）。** 固定 $m\ge2$，在 $[m]$ 上取链

$$
\Gamma=(1<_P3<_P4<_P\cdots<_P m)
\tag{MPC.69}
$$

及与整条链独立的事件 $2$；$m=2$ 时链仅含 $1$。端口的安装读序固定为
$1,2,3,\ldots,m$，不是控制器可重排的动作。记链长为 $m-1$，其长度 $j$
的前缀为 $\Gamma_j$，$\Gamma_0=\varnothing$，
$\Gamma_j=\{1\}\cup\{3,\ldots,j+1\}$ 对 $1\le j\le m-1$。
继续允许每个理想作为入口，量化全部均匀安全实际前缀。

**定理 20.2（全续接最小边界与固定策略前缀）。** 对定义 20.1 的同一个接口，
定义 19.1 的自足边界精确最小有效值域为

$$
\boxed{N_m=m^2+2m-1.}
\tag{MPC.70}
$$

此值由 $(A,t)$ 达到。若另固定策略为每一步只请求最小缺失标签 $t$，则其全部
实际前缀数恰为

$$
\boxed{F_m=m^2+m+1,\qquad N_m-F_m=m-2.}
\tag{MPC.71}
$$

后者是策略受限的前缀数，不能替代全安全续接合同中的 $N_m$。

证明。先由 (MPC.64) 分类全部可达对。

| 当前读数 | 可达 $A$ | 可达对数 |
| --- | --- | --- |
| $t=1$ | $A=\varnothing$ | $1$ |
| $t=2$ | $A=\varnothing$ 或 $A=\Gamma_j,\ 1\le j\le m-1$ | $m$ |
| $3\le t\le m+1$ | $A=L_t\setminus I,\ I\in\operatorname{Down}(P|_{L_t})$ | $2(t-1)$ |

第一行因为没有标号小于一的极小新增事件。第二行的新增事件若非空，必须从
$1$ 开始并构成链前缀；$2$ 仍缺失。第三行中，任何标号不小于 $t$ 的链事件
都有尚未发生的 $t$ 作为前驱，所以不能属于 $A$。$L_t$ 恰由长度 $t-2$ 的
链与独立的 $2$ 组成，理想数为 $2(t-1)$。这些情形也都满足 (MPC.64)，
因此每一项都由实际安全记录达到。求和得

$$
1+m+\sum_{t=3}^{m+1}2(t-1)=m^2+2m-1.
\tag{MPC.72}
$$

定理 19.2 的构造给出这个大小的边界上界。

为证所有合格边界的下界，取不同可达对的任意代表前缀。不同 $t$ 必须分开。
相同 $t\ge3$ 时，$L_t$ 是两条关系共同具有的实际当前配置，且不同 $A$ 给
不同入口 $L_t\setminus A$。定理 19.2 分离它们，$t=\top$ 时也由终端
解码直接分离。

剩下 $t=2$。对 $A=\Gamma_j,\ 1\le j<m-1$，实际当前配置唯一为
$\Gamma_j$，菜单恰为 $\{2,c_{j+1}\}$，其中 $c_{j+1}$ 是下一链事件。
这些菜单彼此不同，也不同于 $A=\varnothing$ 或 $A=\Gamma_{m-1}$ 的
菜单 $\{2\}$。最后这两个可达对虽有相同菜单，却都允许实际当前配置
$\Gamma_{m-1}$：前者可有入口 $\Gamma_{m-1}$，后者入口为
$\varnothing$。共同插入 $2$ 后立即饱和，入口答案不同，故仍被定理 19.2
分离。这也覆盖 $m=2$ 没有中间 $j$ 的边界情形。因而全部 (MPC.72) 个可达
对均须占据不同边界值，证明精确最小值。

对只请求 $t$ 的固定策略，动作标签严格递增，所以 $A\subseteq L_t$。
在第二行只剩 $A=\varnothing$ 或 $\{1\}$；其他两行不变，因为定理 18.3
对 $A\subseteq L_t$ 的达到构造只使用最小缺失事件。
每个这样的对唯一决定其递增动作词和全部读数。因此前缀数为

$$
1+2+\sum_{t=3}^{m+1}2(t-1)=m^2+m+1.
\tag{MPC.73}
$$

$m>2$ 时删去的 $m-2$ 个对，正是 $t=2$ 下在独立事件 $2$ 以前已插入
至少两个链事件的实际安全前缀。它们的存在来自原合同所允许的动作，不能因选择
了一个方便策略而从全续接任务中删除。$\square$

**定理 20.3（全部历史与尖锐的顺序补充）。** 定义 20.1 的全部实际交替前缀数为

$$
\boxed{H_m=N_m+\frac{(m-1)(m-2)}2.}
\tag{MPC.74}
$$

若要从 $(A,t)$ 加一个可更新的补充符号恢复完整前缀，补充字母表的精确最小
大小为 $m-1$。以固定长度二进制编码表示该补充，需且足够
$\lceil\log_2(m-1)\rceil$ 位；这是条件补充，不是总存储界。
若联合边界本身必须恢复完整前缀，其精确最小实际值域为 $H_m$。

证明。在 $t=1$、$t=2$ 的可达对中，动作只可能沿链顺序发生，记录唯一。
对 $t\ge3$，初态由 (MPC.60) 唯一为 $I=L_t\setminus A$。
若初态已经包含 $2$，剩余新增事件都在链上，顺序唯一。若初态不含 $2$ 却
含 $1$，则入口读数为二，零动作关系的共同菜单只有 $\{2\}$，所以必须先
插入 $2$，其余链事件顺序仍唯一。

只有 $I=\varnothing$，即 $A=L_t$，可以有多条前缀。先插入 $1$ 后，链的
尚未发生部分全部已知缺失，而 $2$ 独立，故可以在插入 $j$ 个链事件后再插入
$2$，其中

$$
1\le j\le t-2.
\tag{MPC.75}
$$

准确动作词是
$c_1\cdots c_j\,2\,c_{j+1}\cdots c_{t-2}$，其中 $c_i$ 按链序排列。
此前链事件后读数均为二；插入二以后读数按剩余链顺序推进。
所有这些请求均匀安全，且没有其他合法交织，因为链内顺序固定。
故此可达对恰有 $t-2$ 条记录，而不是一个抽象交换类中的未证安全排列。
对全部 $t$ 求额外记录数，得

$$
\sum_{t=3}^{m+1}((t-2)-1)=\frac{(m-1)(m-2)}2,
\tag{MPC.76}
$$

证明 (MPC.74)。

饱和可达对 $(P,\top)$ 有 $m-1$ 条不同实际历史，任何补充字母表须区分它们，
给出下界。为达到此界，取补充值 $z\in\{1,\ldots,m-1\}$，入口为一。
当实际动作为 $2$ 且旧 $A$ 含 $1$ 时，令

$$
z'=|A\cap\Gamma|;
\tag{MPC.77}
$$

其他动作保持 $z$。该更新只用旧边界和实际事件，不用外部步数或免费时钟。
在所有有歧义的可达对上，$z$ 正是 (MPC.75) 的 $j$；在其他对上记录原已
唯一。故 $(A,t,z)$ 精确恢复动作词，继而恢复读数，达到补充字母表下界。
其联合实际像恰有 $H_m$ 个值，给出完整历史边界的达到；任何能恢复完整前缀
的边界必须在 $\mathcal H(P)$ 上单射，给出相同下界。
$m=2$ 时 $N_m=F_m=H_m=7$，补充只有一个符号，无需额外二进制位。$\square$

## 21. 新读数分离的合法合并

**定理 21.1（不同联合关系的可合并边界反例）。** 取 $P=[5]$，严格关系由

$$
1<_P5,\qquad 2<_P4<_P5
\tag{MPC.78}
$$

及传递性生成，$3$ 与其余事件独立，端口仍按 $1,2,3,4,5$ 读取，
$\top=6$。这个模型有 $45$ 个可达 $(A,t)$ 值，却存在恰有 $44$ 个有效值的
定义 19.1 边界。因此最小任务边界可以严格小于精确联合关系载体；$44$ 这里只是
达到的上界，不是已确定的最小值。

证明。考察两条完整实际前缀

$$
\begin{aligned}
h&=(1,1,3), & (A_h,t_h)&=(\{1\},3),\\
g&=(2,2,3,4,3,5,3), &(A_g,t_g)&=(\{2,4,5\},3).
\end{aligned}
\tag{MPC.79}
$$

由 (MPC.60) 直接得到

$$
\begin{aligned}
\mathcal R_h
 &=\{(\{2\},\{1,2\}),(\{2,4\},\{1,2,4\})\},\\
\mathcal R_g
 &=\{(\{1\},\{1,2,4,5\})\}.
\end{aligned}
\tag{MPC.80}
$$

$h$ 的第一请求一在整个入口读数一的纤维上安全。$g$ 的入口读数二先允许请求
二，读数三以后新增的二使四已知入口缺失且前驱已满足，所以四安全；随后五的
全部前驱一、二、四均已发生，而且五因二原先缺失而入口缺失，所以五也安全。
这逐步认证了整条 $g$，没有以其末端的一点合法性替代全部旧记录的均匀安全性。

两条前缀的当前读数都是三，完整安全菜单也都是 $\{3\}$。实际插入三后，
$h$ 的两条同次来源对分别给新读数四、五，而 $g$ 的唯一对给新读数六：

$$
\{u:(h,3,u)\text{ 实际可能}\}=\{4,5\},\qquad
\{u:(g,3,u)\text{ 实际可能}\}=\{6\}.
\tag{MPC.81}
$$

从定理 19.2 的边界开始，只把 (MPC.79) 中的两个值认同，商映射记为 $\phi$。
其读数与菜单相同，故都可在该合并值上解码。对更新定义

$$
U_b(\phi(A,t),e,u)=\phi(A\cup\{e\},u)
\quad\text{对每个实际允许的输入三元组}.
\tag{MPC.82}
$$

唯一有两个代表的旧值只有 (MPC.79) 的一对；它们唯一可请求的事件都是三，
实际新符号集合又不交，所以每个输入三元组至多从其中一个代表产生，更新无冲突。
其他旧值各有唯一代表，即使其更新目标被合并，仍有唯一像。
入口通过 $q\mapsto\phi(\varnothing,q)$ 初始化，两个合并值都非饱和，所有
饱和值仍分别按 $P\setminus A$ 解码。于是所得边界对全部实际安全历史满足
初始化、完整菜单、实际响应更新及饱和入口恢复，而不能从合并值恢复 (MPC.80)
的哪一个关系。

为精确计算被商的载体，用 (MPC.64) 按读数分组：

| $t$ | $1$ | $2$ | $3$ | $4$ | $5$ | $6$ |
| --- | --- | --- | --- | --- | --- | --- |
| 可达 $(A,t)$ 数 | $1$ | $2$ | $8$ | $8$ | $12$ | $14$ |

$t=1,2$ 分别给 $A=\varnothing$，以及 $A=\varnothing$ 或 $\{1\}$。
$t=3$ 时低标签部分 $A\cap\{1,2\}$ 任意，若没有高标签新增有四种；若新增
四，则须已经新增二，有两种；若新增四、五，同样须已经新增二，有两种。
不能只新增五而不含四，因为 $L_3\cup A$ 须为理想。合得八种。
$t=4$ 时不能含五，低标签一、二、三任意，故八种。
$t=5$ 时 $L_5$ 只有关系二小于四及独立的一、三，理想数为
$3\cdot2^2=12$。$t=6$ 时，不含五的入口理想有十二种，含五的须含一、二、四，
仅三可选，再有两种，合为十四种。各项都由可达条件认证，故总数为四十五，
恰好合并一对后有效值数为四十四。

这里并未保持“仅由旧边界确定下一回复集合”这一额外性质；(MPC.81) 正好显示
它不成立。新实际读数在需要时提供了被丢弃的区别。因此该合并不是第 1 节完整
未来 law 行为商的等价类，也不证明响应支持相等。两条当前配置投影不交，亦不
触犯定理 19.2 的共同当前分离判据。$\square$

[Larrauri–Bloem，第 5 节、引理 3、定理 4](https://arxiv.org/html/2105.10292v2)
在其观察机器中只比较共同已定义输入词上的输出；其相容关系不必传递，极小实现
由闭相容覆盖描述。该成熟背景说明部分输入域为何容许这样的任务合并；
(MPC.79)–(MPC.82) 则直接证明本接口的具体合并。不在没有给出保持入口、输出、
部分域及目标的完整编码时，把该文的一般极小化算法或复杂度结论移用到这里。

## 22. 顺序恢复、原始控制输入与平稳端点

**定理 22.1（关系恢复时间记录的精确条件）。** 对任意定义 18.1 的固定接口，
完整交替前缀可由 $(A,t)$ 在全部 $\mathcal H(P)$ 上恢复，当且仅当每个可达
前缀的均匀安全菜单至多含一个事件。
对一条实际前缀，若 $A_j=\{e_1,\ldots,e_j\}$，则每个旧读数都有精确重演式

$$
q_j=\min\bigl((A\setminus A_j)\cup\{t\}\bigr),
\qquad 0\le j\le |A|.
\tag{MPC.83}
$$

证明。本次尚未执行的 $A\setminus A_j$ 中的事件入口时均缺失，$t\le n$
也始终缺失；所有比最终 $t$ 小而不属于 $A$ 的事件入口时已经存在。
所以当前最小缺失事件恰是 (MPC.83)；$t=\top$ 时同式处理已饱和情形。

若某前缀 $h$ 有两个不同安全事件 $e,f$，它们在每个相容当前理想中都缺失且
全部前驱已发生，故互不为前驱。执行其中一个不会破坏另一个的新鲜性或前驱
条件。即使按新的实际读数缩小了相容来源族，另一个仍在全部剩余来源上安全。
在 $\mathcal R_h$ 中选取同一个实际对 $(C,D)$，分别实际执行 $ef$ 和 $fe$，
得到两条不同均匀安全前缀，最终新增集都为 $A_h\cup\{e,f\}$，当前理想都为
$D\cup\{e,f\}$，最终读数也相同。因此 $(A,t)$ 无法恢复顺序。

反向，若两个前缀具有相同最终 $(A,t)$，则长度同为 $|A|$。
(MPC.83) 使它们的入口读数相同；在共同的动作前缀之后，全部已获读数也相同。
若动作词第一次不同，该共同实际前缀便具有两个安全下一事件，与假设矛盾。
故动作词和全部读数相同，证明可恢复。$\square$

法律路径与线性扩张的交换结构由
[EnabledPathSwapConnectivity 的 `result`](../../../D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.lean)
供应；词对独立相邻字母交换取商的成熟框架见
[Abbes–Mairesse，第 1、3 节](https://arxiv.org/html/1506.02455v1)。
这里的额外条件是基于实际完整观察纤维的均匀安全菜单，而非只凭偏序不相交就
宣称两个命令都可取得。定理 20.3 对 (MPC.69) 精确计算了这些安全交换所丢的
顺序；$m=3$ 时，从同一空入口发生的 $123$ 与 $132$ 已给出最小实例。

**定理 22.2（固定策略与实际原始种子的重演）。** 固定一个已知确定性策略
$\Pi$；若策略使用随机带，则将原始可见且来源无关的完整种子 $U$ 固定后视为
确定性策略。只在该固定策略与原始种子生成的实际前缀像上，
$(U,h)$ 与 $(U,A_h,t_h)$ 两两互相恢复。不用种子的确定性策略可省去 $U$。
该重演不取得新来源回复，也不恢复进入接口以前的历史。

证明。从 $h$ 取新增集和末读数是正向映射。反向给定实际像中的 $(u,A,t)$，
令 $k=|A|$、$A_0=\varnothing$，先用 (MPC.83) 求入口读数。
依据已知 $\Pi$、原始 $u$ 及已重建记录逐次求出下一个请求，再用 (MPC.83)
求下一读数，直到重建 $k$ 个成功动作。实际像条件保证策略不会提前停止，所求
请求确在尚未执行的 $A$ 中，且所有步骤都是原记录。有限归纳给出唯一逆映射。
这是已知函数与已经取得数据的求值，不是对来源执行重置、制造副本或重做实验。

$u$ 不能由事后另选的种子替代，也不能把存活条件下改变后的种子分布当作原始
随机带。若 $U$ 在以后仍可读，它就是联合保留信息，不能从自足存储账目中扣除。
在不限制策略的完整前缀族上，定理 20.3 的多条历史仍存在；将它们限制到某个
固定控制器的实际像改变了恢复问题的输入条件。$\square$

原始控制输入的对应先例是
[Terminal Event Experiment，定理 1.3、2.3](https://github.com/the-omega-institute/trureturing/blob/d2b0ee6e958cf646530d3476088494e349570b46/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TERMINAL_EVENT_EXPERIMENT.md)：
在其 PG27 同源两臂模型、固定已知等待策略及原始可见种子 $U$ 下，完整终止档案
与 $(U,X_0,R)$ 互恢复，$(U,T)$ 也恢复档案，且有逐路径恒等式
$T=2R+2X_0+1-B$。那里的原始种子、首次标记终止及标记前全零回复是明确假设。
本节的 (MPC.83) 处理多个中间符号、部分合法菜单及非饱和前缀；没有把 PG27 的
$R$、后验或跨策略 law 运输认作这里的配置，也没有据此产生同一实际来源上的
未查询边或端口实例。

**定理 22.3（平稳读数和当前端点不能替代任务记忆）。** 在定义 20.1 中，
$m\ge3$ 时存在一次均匀安全新增前后读数不变、当前配置和完整安全菜单却变化
的实际前缀。即使同时已恢复实际入口与当前配置，也一般不能恢复执行顺序。
在饱和端点，剩余来源读数与菜单本身不保留本次入口区别。

证明。从空入口先插入一，得到 $(A,t)=(\{1\},2)$，当前配置为 $\{1\}$，
菜单含二和三。再实际插入三，读数仍为二，当前配置为 $\{1,3\}$，菜单改为
$\{2,4\}$，$m=3$ 时改为 $\{2\}$。故只保留平稳读数没有保留当前配置、
安全菜单或已经发生的时序事件。

同一空入口下的 $123$ 与 $132$ 在 $m\ge3$ 都均匀安全；其新增集、实际当前
配置、入口和末读数分别相同，动作顺序却不同。对 $m>3$，可在两者后追加相同
剩余链词直至饱和，区别仍只在先前顺序。

最后，每个入口理想都可以通过只请求当前缺失事件到达 $P$。这些饱和历史的
当前配置同为 $P$，菜单同为空，平稳重读同为 $\top$；所需入口答案却随
$P\setminus A$ 改变。因此源端点的剩余读数不承担入口任务，已保留档案或边界
承担的是另一个指定目标。完整未来预测若允许读取这些档案，须把其可见性纳入
测试族；若只允许源端点的剩余读数，不能要求其预测商自动恢复过去。本接口没有
授权非法请求或拒绝探测，不能为强化预测任务而免费添加这些动作。$\square$

## 23. 原来源运输条件与结论域

**假设 23.1（保持原任务的实际接口运输）。** 将定理 18.2–22.3 用于别的实际
来源，仍须给出第 14 节那种同一来源与纪元上的配置编码、逆码表、动作合法域、
新鲜后继及实际安装读出。全部理想未知入口的下界还要求实际入口像覆盖这里的
全部理想。若只编码来源的一个任务商，恢复结论也只关于该商；若来源身份、
权限、档案或控制输入可变且属于目标，须纳入联合状态和可访问边界。
(MPC.58) 的线性扩张次序是传感安装的一部分，没有授予重排控制。

**定理 23.2（只读树的来源单独编码障碍）。** 对
[Joint Moment Fibers，约定 36.1](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md)
的同一不可变有序树 $T$ 及地址读动作，任何只依赖树的配置编码 $\iota(T)$ 都
不能把一次实际只读查询对应为本卷的新鲜单次新增动作。

证明。该合同的查询不改变树。若其对应事件为 $e$，保持后继的要求将给出

$$
\iota(T)=\iota(T)\cup\{e\},
\qquad e\notin\iota(T),
\tag{MPC.84}
$$

两式矛盾。这个障碍只针对以不变的树本身作为全部动态状态的对应；树与实际新增
档案组成的联合状态可以变化，但要使用它仍须证明全部动作、入口、读出和目标
的对应，不能仅以这种状态可以命名就取得 (MPC.58) 的端口。
$\alpha,\beta$ 的生成记号也没有指定那些数据。$\square$

**约定 23.3（供应对应与未闭合目标）。** 新鲜前驱启用关系对应
`EnabledPathSwapConnectivity.Enabled`，有序新增对应其 `Exec`；
[ConfigurationPathTransport](../../../D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.lean)
在无冲突条件下的 `configurationIdealIso`、`exec_exists_iff_subset` 与
`finite_history_clocks` 供应理想、路径存在和路径计数的既有中间结构。
一般更新加记录的可逆条件由
[ExactRollbackInjectivityCriterion](../../../D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion.lean)
的 `exact_rollback_iff_joint_record_injective` 供应。
[ControlledBehaviorUniversality](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean)
的 `controlled_behavior_universal_property` 针对总确定输入更新及完整读出保持，
不能省去这里实际新符号的输入或强制部分响应域相等。
这些供应不包含 (MPC.60)、(MPC.64)、链族三个精确基数、顺序补充或五事件合并
的本接口计算；本节使用它们的结构，新增的是实际来源区间与具体取得任务之间
的推导，不作全球优先权判断。

空间恢复在本卷指同次初态—当前关系及其单点条件，时间恢复指实际取得的有序
前缀，边界与记忆则按定义 19.1 的目标和访问合同区分；没有把四个同名坐标自动
认作四种物理表达。$N_m,F_m,H_m$ 计算实际可达类数，补充字母表是在已给
$(A,t)$ 下的条件大小，不等于总位数、物理体积、CPU、传感准备、编码、输出或
实际历时费用。外置可读完整档案仍按命题 17.3 计入全部保留信息。

未知 law、未知 cut 的原始 FIB 任务，一般阶 $d$ 的多项式 TOTAL 取得及原始
$K_d$ 的精确规范化仍保留其原量词、动作、来源身份和目标；上述固定有限安装
没有给出它们的算法或认证。
[Original Control Finite Handoff Boundaries，第 13 节](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_FINITE_HANDOFF_BOUNDARIES.md)
所需的共同实际来源、完整菜单、旧档案可见性、控制输入以及存活、拒绝、吸收
失败后继的联合取得与可执行更新仍须分别提供。一个可计算的有限来源区间和一个
达到的有限任务边界，不能替代这些原来源义务。

## 追加锚（本行以下为增补区）

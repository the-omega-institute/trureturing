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

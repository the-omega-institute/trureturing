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

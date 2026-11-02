# 情境时空算术的量子扩展：参考系统、历史与控制

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](001_016_FOUNDATIONS_AND_RECORDS.md) · [续卷](033_051_CLASSICAL_AND_QUANTUM_STORAGE.md)


<a id="entry-73"></a>

## 追加锚（新终端）

<a id="section-17"></a>

## 17. 无量子记忆的全历史乘积界达到

**定义 17.1（实二能级历史反馈协议）。** 固定有限阶段数 $N\ge1$ 和参数 $\beta_t\in[0,1]$，令

$$
a_t=\sqrt{1-\beta_t},\qquad b_t=\sqrt{\beta_t},
\qquad s_0=1,\qquad s_k=\prod_{t=1}^k a_t.
$$

系统为 $S=\mathbb C^2$，指针投影为 $P_z=|z\rangle\langle z|$，$z\in\{0,1\}$。不设置可访问量子记忆。第 $t$ 步使用一个新鲜二能级记录，其单位条件向量为

$$
e_{t,0}=a_t|0\rangle+b_t|1\rangle,
\qquad e_{t,1}=b_t|0\rangle+a_t|1\rangle.
$$

条件写入之后在记录的计算基上读取，实际仪器的两个 Kraus 算子是

$$
K_{t,z}=a_tP_z+b_tP_{1-z}.
$$

它们满足 $\sum_zK_{t,z}^\dagger K_{t,z}=I_S$，对指针制备 $P_x$ 的正确结果概率为 $a_t^2=1-\beta_t$。理想比较仪器的结果算子为 $P_z$。这复用第 16.4 条的记录族与第 16.2 条的 Lüders 比较，但采用下述无量子记忆控制类。

对每个已存历史 $h\in\{0,1\}^{t-1}$，在第 $t$ 次写入前施加一个预先确定的实正交矩阵 $U_{t,h}\in O(2)$；它也是合法的系统酉。实际和理想过程使用同一个控制表 $h\mapsto U_{t,h}$，各自按自身已经存储的历史调用。其未归一化结果更新分别为

$$
\mathcal A_{t,h,z}(\rho)
=K_{t,z}U_{t,h}\rho U_{t,h}^\dagger K_{t,z}^\dagger,
\qquad
\mathcal B_{t,h,z}(\rho)
=P_zU_{t,h}\rho U_{t,h}^\dagger P_z.
$$

所有结果都保存在经典历史寄存器 $H_k=Z_1\cdots Z_k$，不改写旧结果、不后选择；量子记录余系统被丢弃且不再耦合。记经过前 $k$ 步的带全部历史输出通道为

$$
\mathcal H_{{\rm actual},k}^{U},
\qquad
\mathcal H_{{\rm ideal},k}^{U}:
\mathcal L(S)\longrightarrow\mathcal L(H_k\otimes S).
$$

控制表一经确定，这些都是对任意输入定义的线性 CPTP 通道。下述达到见证使用两过程相同的固定输入 $P_0$，且不携带参考系统；通道的 diamond 范数仍按通常定义允许有限参考。

**定理 17.2（一个实量子比特及经典反馈同时达到全部前缀界）。** 对定义 17.1 的任意有限 $N$ 和任意 $(\beta_t)_{t=1}^N$，存在一个控制表 $U$，使每个 $1\le k\le N$ 都满足

$$
\begin{aligned}
\frac12\left\|
\mathcal H_{{\rm actual},k}^{U}(P_0)
-\mathcal H_{{\rm ideal},k}^{U}(P_0)
\right\|_1
&=\frac12\left\|
\mathcal H_{{\rm actual},k}^{U}
-\mathcal H_{{\rm ideal},k}^{U}
\right\|_\diamond\\
&=\sqrt{1-s_k^2}
=\sqrt{1-\prod_{t=1}^k(1-\beta_t)}.
\end{aligned}
$$

因此第 16.3 条的乘积常数在这个无可访问量子记忆的实二能级控制子类中仍不能普遍减小；达到不需要静止纠缠参考。控制表可以在实验前按完整有限历史树计算，运行时只读取已存历史。

证明。 对每个历史 $h$，同时递归计算两个实的未归一化分支向量 $\psi_h,\phi_h\in\mathbb R^2$。它们分别表示固定见证输入 $P_0$ 在实际和理想过程中的分支，初值为

$$
\psi_\varnothing=\phi_\varnothing=|0\rangle.
$$

在深度 $k=|h|$，记

$$
p_h=\|\psi_h\|^2,\qquad
q_h=\|\phi_h\|^2,\qquad
c_h=\phi_h^{\mathsf T}\psi_h.
$$

我们逐层构造共同控制，使每个历史都满足

$$
2c_h=s_k(p_h+q_h).
$$

初始两向量相同且范数为一，故该关系在空历史成立。所有 $s_k$ 非负，因此这同时保证 $c_h\ge0$。

固定深度 $t-1$ 的一个历史，暂写 $\psi=\psi_h$、$\phi=\phi_h$、$p=p_h$、$q=q_h$、$c=c_h$、$s=s_{t-1}$、$a=a_t$、$b=b_t$。定义实对称矩阵

$$
X_h
=\psi\phi^{\mathsf T}+\phi\psi^{\mathsf T}
-s\bigl[(a^2-b^2)\psi\psi^{\mathsf T}
+\phi\phi^{\mathsf T}\bigr]
-sb^2pI_2.
$$

由 $a^2+b^2=1$ 和归纳关系，其迹为

$$
\operatorname{tr}X_h
=2c-s\bigl[(a^2-b^2)p+q\bigr]-2sb^2p
=2c-s(p+q)=0.
$$

若 $X_h=0$，取标准实正交基为 $r_0,r_1$。若 $X_h\ne0$，实对称谱定理给出正交归一的特征向量 $v_+,v_-$，特征值分别为 $\lambda,-\lambda$，其中 $\lambda>0$。令

$$
r_0=\frac{v_++v_-}{\sqrt2},
\qquad
r_1=\frac{v_+-v_-}{\sqrt2}.
$$

它们正交归一，而且两种情形都满足

$$
r_z^{\mathsf T}X_hr_z=0\qquad(z=0,1).
$$

选择共同系统酉 $U_{t,h}$ 的第 $z$ 行为 $r_z^{\mathsf T}$。将历史 $h$ 后附结果 $z$ 记为 $hz$，递归定义

$$
\psi_{hz}=K_{t,z}U_{t,h}\psi_h,
\qquad
\phi_{hz}=P_zU_{t,h}\phi_h.
$$

设 $u_z=r_z^{\mathsf T}\psi$、$v_z=r_z^{\mathsf T}\phi$。直接计算两个分支的范数与内积，得到

$$
p_{hz}=b^2p+(a^2-b^2)u_z^2,
\qquad
q_{hz}=v_z^2,
\qquad
c_{hz}=a u_zv_z.
$$

而 $r_z^{\mathsf T}X_hr_z=0$ 正好等价于

$$
2u_zv_z
=s\bigl[b^2p+(a^2-b^2)u_z^2+v_z^2\bigr]
=s(p_{hz}+q_{hz}).
$$

两边乘以 $a$，便得到下一层所需关系

$$
2c_{hz}=as(p_{hz}+q_{hz})
=s_t(p_{hz}+q_{hz}).
$$

这里没有除以 $a,s,p,q$，也没有对分支向量作归一化，所以 $\beta_t=0$、$\beta_t=1$ 和任一模型中的零概率历史都包含在构造内。每个结点选择一次实正交基，沿有限历史树递归，便得到定义在全部历史上的共同控制表。

由实际 Kraus 完备关系及理想投影完备关系，每个结点都有

$$
\sum_{z=0}^1p_{hz}=p_h,
\qquad
\sum_{z=0}^1q_{hz}=q_h.
$$

因此在任意深度 $k$，两族分支权重各自满足 $\sum_{|h|=k}p_h=\sum_{|h|=k}q_h=1$，实际和理想全输出为

$$
\rho_k=\sum_{|h|=k}|h\rangle\langle h|\otimes
|\psi_h\rangle\langle\psi_h|,
\qquad
\sigma_k=\sum_{|h|=k}|h\rangle\langle h|\otimes
|\phi_h\rangle\langle\phi_h|.
$$

对两个未归一化纯态，标准的秩一差值公式给出

$$
\left\|
|\psi_h\rangle\langle\psi_h|
-|\phi_h\rangle\langle\phi_h|
\right\|_1
=\sqrt{(p_h+q_h)^2-4c_h^2}.
$$

该式也可直接由二阶矩阵的迹 $p_h-q_h$、行列式 $c_h^2-p_hq_h\le0$ 及两个特征值得到，涵盖零向量与共线情形。代入已保持的关系，右端变为 $(p_h+q_h)\sqrt{1-s_k^2}$。不同经典历史块的迹范数相加，故

$$
\frac12\|\rho_k-\sigma_k\|_1
=\frac12\sum_{|h|=k}(p_h+q_h)\sqrt{1-s_k^2}
=\sqrt{1-s_k^2}.
$$

这由固定、无参考的输入 $P_0$ 给出两个通道的半 diamond 距离下界；第 16.3 条适用于该共同反馈策略，给出相同的参考系统一致上界。因此通道距离也等于所列值。构造中的同一个有限控制表保持每层关系，所以各前缀同时达到。证毕。

Acín 等，*Physical Review A* **71**，032338（2005），[§III.B、式 (19)–(20)](https://arxiv.org/abs/quant-ph/0410097v2)，证明了对两个已知纯态的 $N$ 个相同副本作适应逐份测量可达到联合 Helstrom 界，可作为适应判别的背景。该副本任务不同于本定理固定 $K_{t,z}$ 与 $P_z$ 仪器的历史比较，且本章条件记录的重叠是 $\langle e_{t,1},e_{t,0}\rangle=2a_tb_t$；本定理的达到结论由上述实谱基递推证明。

上述控制表使用指定模型、参数和固定见证输入，在实验前计算两族候选分支。运行中不测量未知量子态来选择控制，也不查询正在执行的是实际仪器还是理想仪器；两种实验始终使用同一个函数 $h\mapsto U_{t,h}$。对别的输入，该固定表仍定义合法通道，而定理 16.3 仍提供统一上界。

第 16.4 条用可访问量子记忆及 SWAP 给出达到构造，并没有断言量子记忆是必要条件。本定理把达到构造放进更小的控制类：一个系统量子比特、经典历史及预先计算的实酉反馈。它不限制经典历史或控制表的存储量，也不声称无反馈协议都能达到。

这里最大化的是实际仪器与理想仪器的完整历史差异，用来确定仅依据 $(\beta_t)$ 所能保证的最坏常数。它不是保持某个指针标签的最优策略；标签持久性仍需第 16.5 条的转移条件，不能由本定理的误差达到推出。

<a id="entry-75"></a>

## 追加锚（新终端）

<a id="section-18"></a>

## 18. 只读取经典历史时的精确两步边界

**定义 18.1（丢弃系统后的经典历史误差）。** 沿用定义 17.1 的二标签记录族，但允许各历史分支的共同系统控制为任意酉矩阵 $U_{t,h}\in U(2)$。系统初态 $\rho$ 可以是任意二阶密度矩阵；输入不携带参考系统，过程不使用可访问辅助量子记忆。保留全部经典历史 $H_N$，最终丢弃系统，只比较历史分布。所有记录单元仍新鲜准备，读取后的量子余系统不再耦合，不后选择。

对有限阶段数 $N\ge1$ 和参数 $\boldsymbol\beta=(\beta_1,\ldots,\beta_N)\in[0,1]^N$，实际结果算子与理想结果算子分别为

$$
K_{t,z}=\sqrt{1-\beta_t}P_z+\sqrt{\beta_t}P_{1-z},
\qquad P_z,\qquad z\in\{0,1\}.
$$

实际与理想过程使用同一个共同控制表 $U$，各自按已有历史调用它。记其经典路径分布为 $p_{\rho,U}^{\rm actual}$ 与 $p_{\rho,U}^{\rm ideal}$，定义

$$
T_N(\boldsymbol\beta)
=\sup_{\rho,U}
\operatorname{TV}\!\left(p_{\rho,U}^{\rm actual},p_{\rho,U}^{\rm ideal}\right),
\qquad
\operatorname{TV}(p,q)=\frac12\sum_h|p(h)-q(h)|.
$$

本章不保留量子参考，因而该目标不直接等同于允许输出参考的 diamond 范数优化。定理 16.3 的全输出界仍给出本目标的上界，但丢弃系统可能严格减小最优值。本章的最优值始终限定于无输入或输出参考的纯经典分布任务，不推出任意固定协议的量子参考均无增益。

**定理 18.2（两步纯经典历史误差的精确最优值）。** 取 $N=2$，$\beta_1=e$、$\beta_2=f$，其中 $e,f\in[0,1/2]$。则

$$
T_2(e,f)
=\max\left\{
 e+f-ef,\ \sqrt{f^2+(1-2f)e}
\right\}.
$$

第一项由指针初态 $P_0$ 与恒等控制达到；第二项由平衡纯初态 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ 及按第一结果选择的末次测量基达到。所有最优值均可使用实正交系统控制实现。

两种策略的平方值差为

$$
f^2+(1-2f)e-(e+f-ef)^2
=e\bigl[1-4f+2f^2-(1-f)^2e\bigr].
$$

该因子式决定在给定 $e,f$ 下哪种达到策略给出较大的历史差异；等于零时两种策略都达到最优值。

证明。 第一共同酉可吸收入初态。对任一固定控制表，经典概率差线性依赖 $\rho$，总变差是其凸函数；将混态作纯态凸分解可知，其值不超过其中某个纯态的值。因此可以只优化纯输入。写作

$$
|\psi\rangle=\sqrt t|0\rangle+e^{i\theta}\sqrt{1-t}|1\rangle,
\qquad 0\le t\le1.
$$

令 $D=\operatorname{diag}(1,e^{i\theta})$。第一步的实际算子与理想投影均与 $D$ 交换；把输入换为相位为零的向量，并把每个第二步共同控制 $U_z$ 换成 $U_zD$，便保留所有经典路径概率。因此可以令 $\theta=0$。

给定第一结果 $z$，记实际和理想未归一化分支向量为

$$
\psi_z=K_{1,z}\psi,
\qquad
\phi_z=P_z\psi,
\qquad
p_z=\|\psi_z\|^2,
\qquad q_z=\|\phi_z\|^2.
$$

于是 $q_0=t$、$q_1=1-t$，并且

$$
p_z=e+(1-2e)q_z,
\qquad
|\langle\phi_z,\psi_z\rangle|^2=(1-e)q_z^2.
$$

令 $d=1-2f\ge0$。第二步共同控制 $U_z$ 之后，结果 $w$ 的实际与理想联合路径概率之差为

$$
\langle w|U_zY_zU_z^\dagger|w\rangle,
\qquad
Y_z=d|\psi_z\rangle\langle\psi_z|
-|\phi_z\rangle\langle\phi_z|+fp_zI_2.
$$

这是因为 $K_{2,w}^\dagger K_{2,w}=fI_2+dP_w$。两个 $Y_z$ 为 Hermitian 矩阵；其迹为 $p_z-q_z$，一般不为零。对任意 Hermitian 矩阵，任意基中的对角元绝对值之和不超过迹范数，在特征基中达到。两个历史分支可以分别选择 $U_z$，所以对固定 $t$ 的精确优化为

$$
\frac12\sum_{z=0}^1\|Y_z\|_1.
$$

输入已取实数，故 $Y_z$ 为实对称矩阵，所需特征基及控制均可选为实的。

令 $r=|2t-1|\in[0,1]$，定义

$$
A=f^2+de,\qquad
B=2f(f+de),\qquad
C=f^2-d^2e(1-e).
$$

对一个二阶 Hermitian 矩阵，迹范数等于其迹绝对值和特征值间距的较大者。这里 $|\operatorname{tr}Y_z|=er$；直接计算特征值间距的平方，两个分支依次给出 $A+Br+Cr^2$ 和 $A-Br+Cr^2$，其中分支次序不影响其和。因而

$$
T_2(e,f)=\max_{0\le r\le1}F(r),
$$

$$
F(r)=\frac12\left[
\max\{er,\sqrt{A+Br+Cr^2}\}
+\max\{er,\sqrt{A-Br+Cr^2}\}
\right].
$$

为核对间距公式，可对 $q=q_z$ 写 $p=e+(1-2e)q$。矩阵 $d|\psi_z\rangle\langle\psi_z|-|\phi_z\rangle\langle\phi_z|$ 加上标量矩阵不改变特征值间距，该间距平方为

$$
(dp+q)^2-4d(1-e)q^2.
$$

代入 $q=(1\pm r)/2$ 即得到上述两个二次式。因此它们在所用区间内均非负。

下面直接证明最大值在 $r=0$ 或 $r=1$ 取得。记

$$
L=e+f-ef,\qquad M=\max\{\sqrt A,L\}.
$$

端点满足

$$
F(0)=\sqrt A,
\qquad
\sqrt{A+B+C}=2f+de,
\qquad
\sqrt{A-B+C}=de,
\qquad F(1)=L.
$$

此外，有 $B\ge0$、$C\le A$，以及

$$
4AC-B^2=-4d^3e^2(1-e)\le0.
$$

置 $u=\sqrt{A+Br+Cr^2}$、$v=\sqrt{A-Br+Cr^2}$，则 $u\ge v$。两个最大值的和可写成

$$
F(r)=\max\left\{er,\frac{er+u}{2},\frac{u+v}{2}\right\}.
$$

第一项不超过 $e\le L\le M$。对第三项，由 $C\le A$ 及 $0\le r\le1$，有 $A-Cr^2\ge0$；同时

$$
(A-Cr^2)^2-
\bigl[(A+Cr^2)^2-B^2r^2\bigr]
=(B^2-4AC)r^2\ge0.
$$

根号中的量等于 $u^2v^2\ge0$，因此 $uv\le A-Cr^2$。由此

$$
\left(\frac{u+v}{2}\right)^2
=\frac{A+Cr^2+uv}{2}\le A,
$$

故第三项也不超过 $\sqrt A\le M$。

对第二项，$2M-er\ge0$。定义

$$
Q(r)=(2M-er)^2-(A+Br+Cr^2)
=4M^2-A-(4Me+B)r+(e^2-C)r^2.
$$

有 $Q(0)=4M^2-A\ge3A$。又因为 $M\ge L=(e+2f+de)/2$，

$$
Q(1)=(2M-e)^2-(2f+de)^2\ge0.
$$

最后，在 $e,f\in[0,1/2]$ 上，

$$
A-(e^2-C)
=2f\bigl[e(1-2e)+f(1-2e+2e^2)\bigr]\ge0.
$$

所以 $e^2-C\le A$。将二次式与其端点连接，得到

$$
\begin{aligned}
Q(r)
&=(1-r)Q(0)+rQ(1)-(e^2-C)r(1-r)\\
&\ge(1-r)3A-Ar(1-r)
=A(1-r)(3-r)\ge0.
\end{aligned}
$$

于是 $u\le2M-er$，第二项也不超过 $M$。结合三个分支，$F(r)\le M$ 对整个闭区间成立；这里没有除以参数或根式，包含所有端点与零根情形。

两种达到策略分别实现两个端点。取初态 $P_0$、全部控制为恒等，则系统始终为 $P_0$，理想历史确定为 $00$，实际得到 $00$ 的概率为 $(1-e)(1-f)$，故总变差为 $L$。

取 $t=1/2$、初态 $|+\rangle$ 时，令 $g=f+de$、$h=d\sqrt{e(1-e)}$，上述两矩阵为

$$
Y_0=\frac12\begin{pmatrix}-g&h\\h&g\end{pmatrix},
\qquad
Y_1=\frac12\begin{pmatrix}g&h\\h&-g\end{pmatrix},
\qquad g^2+h^2=A.
$$

它们各有特征值 $\pm\sqrt A/2$。对每个第一结果 $z$ 选择使 $Y_z$ 对角的共同实控制 $U_z$，便达到 $F(0)=\sqrt A$；$A=0$ 时任取控制即可。该控制表只依赖模型参数与第一结果，实验前即可确定。选取两种策略中较大的一种即得结论；陈述中的策略分界因子式由 $A-L^2$ 直接展开得到。证毕。

**命题 18.3（完全随机读出与末次完美读出的任意有限历史边界）。** 在定义 18.1 的同一纯经典观察类中，有以下两个精确边界。

若全部 $\beta_t=1/2$，则

$$
T_N(1/2,\ldots,1/2)=1-2^{-N}.
$$

若 $\beta_N=0$，其余 $\beta_t\in[0,1]$ 任意，则

$$
T_N(\beta_1,\ldots,\beta_{N-1},0)
=\sqrt{1-\prod_{t=1}^{N-1}(1-\beta_t)}.
$$

空乘积取一，因此第二式在 $N=1$ 时为零。

证明。 第一种情形中，$K_{t,z}=I_2/\sqrt2$，所以任何条件输入及控制下的两个实际结果概率都为 $1/2$。实际全部 $2^N$ 条历史均匀分布，与任意理想概率分布 $q$ 的总变差不超过 $1-2^{-N}$。具体地，令 $m=2^N$，有

$$
\operatorname{TV}(\operatorname{Unif}_m,q)
=1-\sum_h\min\{1/m,q(h)\}\le1-1/m,
$$

因为至少存在一个 $q(h)\ge1/m$。取初态 $P_0$ 和恒等控制使理想历史确定为 $0^N$，便达到该界。

第二种情形中，定理 16.3 对前 $N-1$ 步的全部历史及系统输出给出右端上界。最后一步的共同控制及共同完美测量是同一个 CPTP 后处理，丢弃系统并保留其结果不增加该距离，故此界也控制最终纯经典分布。

为达到它，若 $N\ge2$，采用定理 17.2 对前 $N-1$ 步给出的固定输入 $P_0$ 与共同控制表。对每个旧历史 $h$，记两个未归一化条件系统态之差为

$$
D_h=|\psi_h\rangle\langle\psi_h|-|\phi_h\rangle\langle\phi_h|.
$$

在最后一步，按历史选择同一个系统酉，将 $D_h$ 的特征基送到指针基，再使用 $\beta_N=0$ 的完美指针读出。该末次读取的两个概率差就是 $D_h$ 的两个特征值，因此对最后结果求绝对值之和得到 $\|D_h\|_1$。再对旧历史求和，最后纯经典总变差恰为前缀联合迹距离，即定理 17.2 已达到的右端。零矩阵分支任取测量基，不需要对历史概率归一化。$N=1$ 时实际与理想仪器完全相同，直接得到零。

上述第一式在 $N=2$ 时给出 $T_2(1/2,1/2)=3/4$，与定理 18.2 一致，而定理 17.2 的历史加系统输出最优误差是 $\sqrt3/2$；同一记录精度在不同保留输出上具有不同的最坏边界。第二式的达到构造则把此前留在活动系统中的条件态差异转成经典历史概率差。证毕。

<a id="entry-77"></a>

## 追加锚（新终端）

<a id="section-19"></a>

## 19. 经典历史延续的三参数最优递推

**定义 19.1（未归一化分支对的延续代价）。** 沿用定义 18.1 的纯经典历史观察任务：一个活动系统量子比特、任意共同历史控制酉 $U\in U(2)$、新鲜对称非破坏记录、全部结果存储为经典，最后丢弃系统。输入和输出均不保留参考，过程不使用可访问辅助量子记忆。每次记录的实际结果算子为

$$
K_{\beta,z}=\sqrt{1-\beta}P_z+\sqrt\beta P_{1-z},
\qquad z\in\{0,1\},\qquad\beta\in[0,1],
$$

理想结果算子为 $P_z$。两过程使用同一个历史控制表，读取后的量子环境不再耦合，不后选择。

在一个已存历史后，给定两个未归一化候选分支向量 $\psi,\phi\in\mathbb C^2$。因为每个结果只有一个 Kraus 算子，纯初态及按结果更新始终给出这种向量对。定义

$$
p=\|\psi\|^2,\qquad q=\|\phi\|^2,
\qquad k=|\langle\phi,\psi\rangle|^2,
$$

以及三参数域

$$
\mathcal G=\{(p,q,k)\in\mathbb R^3:
 p,q\ge0,\ 0\le k\le pq\}.
$$

分支权重不重新归一化，允许 $p=0$ 或 $q=0$。给定有限剩余参数列 $\boldsymbol\beta=(\beta_1,\ldots,\beta_n)$，从该分支对继续执行共同控制及两种记录仪器，记末端延续历史 $w\in\{0,1\}^n$ 的未归一化向量为 $\psi_w,\phi_w$。延续代价是

$$
\sup_U\sum_{w\in\{0,1\}^n}
\left|\|\psi_w\|^2-\|\phi_w\|^2\right|.
$$

这里不乘 $1/2$，并保留原分支的两个权重。下述定理证明此代价只依赖 $(p,q,k)$，记为 $V_{\boldsymbol\beta}(p,q,k)$。

**定理 19.2（完整酉取向域与精确有限 Bellman 递推）。** 定义 19.1 的延续代价在 $\mathcal G$ 上良定义。对每个 $(p,q,k)\in\mathcal G$，令

$$
\begin{aligned}
\mathcal F(p,q,k)=\bigl\{(u,v)\in[0,p]\times[0,q]:\;&
[k-uv-(p-u)(q-v)]^2\\
&\le4uv(p-u)(q-v)\bigr\}.
\end{aligned}
$$

它非空且紧，恰好等于对同一个共同酉 $U\in U(2)$ 取值时的可达强度对

$$
u=|\langle0|U\psi\rangle|^2,
\qquad v=|\langle0|U\phi\rangle|^2.
$$

对下一步参数 $\beta\in[0,1]$ 和 $(u,v)\in\mathcal F(p,q,k)$，定义后继三元组

$$
\begin{aligned}
G_0^\beta(p,q,k;u,v)
&=\bigl(\beta p+(1-2\beta)u,\ v,\ (1-\beta)uv\bigr),\\
G_1^\beta(p,q,k;u,v)
&=\bigl(\beta p+(1-2\beta)(p-u),\ q-v,\\
&\hspace{5em}(1-\beta)(p-u)(q-v)\bigr).
\end{aligned}
$$

它们都属于 $\mathcal G$。空参数列与一般有限递推满足

$$
V_\varnothing(p,q,k)=|p-q|,
$$

$$
\begin{aligned}
V_{(\beta,\boldsymbol\gamma)}(p,q,k)
=\max_{(u,v)\in\mathcal F(p,q,k)}
\bigl[&V_{\boldsymbol\gamma}(G_0^\beta(p,q,k;u,v))\\
+&V_{\boldsymbol\gamma}(G_1^\beta(p,q,k;u,v))\bigr].
\end{aligned}
$$

所有有限步控制最大值都达到。对固定长度 $n$，$V_{\boldsymbol\beta}(p,q,k)$ 连续依赖 $(\boldsymbol\beta,p,q,k)\in[0,1]^n\times\mathcal G$，包括零分支和秩亏边界。

只剩一步时，有完整参数域上的闭式

$$
V_{(\beta)}(p,q,k)
=\max\left\{|p-q|,
\sqrt{\bigl((1-2\beta)p+q\bigr)^2-4(1-2\beta)k}
\right\}.
$$

定义 18.1 的原始归一化任务因而满足

$$
T_N(\beta_1,\ldots,\beta_N)
=\frac12V_{(\beta_1,\ldots,\beta_N)}(1,1,1).
$$

证明。 先说明三参数确实足以确定未来最优代价。两个向量分别乘整体相位不改变其密度算子，也不改变任何给定后续协议的路径概率。可以选择这些相位，使内积为非负实数 $\sqrt k$；若内积为零，相位任取。此时按列 $(\psi,\phi)$ 的 Gram 矩阵为

$$
G(p,q,k)=\begin{pmatrix}p&\sqrt k\\\sqrt k&q\end{pmatrix}.
$$

$\mathcal G$ 的条件恰使该矩阵正半定，它的正平方根两列就实现任意给定的三元组。

若两对向量有同一个 Gram 矩阵，则按对应向量定义其张成空间之间的线性映射。这个定义良好：任意线性组合的范数平方由同一 Gram 矩阵给出，故初始组合为零时目标组合也为零。它保持内积，两个张成空间维数相等，再为正交补选择对应正交基，就得到整个 $\mathbb C^2$ 上的共同酉。这包含秩二、秩一和零维张成空间。

因此具有相同 $(p,q,k)$ 的两对候选向量，经各自无关的整体相位调整后，可由同一个系统酉相互转换。将该酉与下一步共同控制复合，给出两个控制集合之间的双射，未来最优代价相等；没有剩余步骤时两者都只给出 $|p-q|$。所以 $V$ 良定义。

下面证明 $\mathcal F$ 的取向刻画。固定共同酉并在其输出基中写两向量，内积分成两个坐标贡献，模长分别为

$$
\ell_0=\sqrt{uv},
\qquad \ell_1=\sqrt{(p-u)(q-v)}.
$$

这两个复数之和的模必须等于 $\sqrt k$，故三角不等式给出

$$
|\ell_0-\ell_1|\le\sqrt k\le\ell_0+\ell_1.
$$

平方后，这等价于

$$
|k-\ell_0^2-\ell_1^2|\le2\ell_0\ell_1,
$$

再次平方即为 $\mathcal F$ 的多项式条件。

反过来，设 $(u,v)$ 满足该条件。若 $\ell_0\ell_1>0$，则

$$
\left|\frac{k-\ell_0^2-\ell_1^2}{2\ell_0\ell_1}\right|\le1,
$$

所以可以选择两个复相位，使模长为 $\ell_0,\ell_1$ 的两数之和具有模 $\sqrt k$。若至少一个模长为零，多项式条件强制 $k=\ell_0^2+\ell_1^2$，任意相对相位即可。特别地，二者均为零时必有 $k=0$。

据此构造坐标向量

$$
\psi'=\begin{pmatrix}\sqrt u\\\sqrt{p-u}\end{pmatrix},
\qquad
\phi'=\begin{pmatrix}\sqrt v\,e^{-i\alpha_0}\\
\sqrt{q-v}\,e^{-i\alpha_1}\end{pmatrix},
$$

使 $|\langle\phi',\psi'\rangle|^2=k$。再给 $\phi'$ 乘一个整体相位，可使其 Gram 矩阵与已调整相位的初始向量对完全相同，而强度 $u,v$ 不变。上述共同酉扩张于是将初始对同时送到这对坐标向量。若初始向量先调整过整体相位，将这些无关相位还原也不改变最终坐标强度。因此同一个合法 $U$ 实现所指定 $(u,v)$。

这证明可行域既没有遗漏共同酉，也没有允许两候选态独立旋转。取任意共同酉可知可行域非空；多项式条件定义闭集，且包含在有界矩形中，所以它紧。一般内部可行点依赖复相对相位，不能在此证明中未经论证地把 $U(2)$ 缩成实正交群。

对选定 $(u,v)$，实际结果零与理想结果零的更新向量为 $K_{\beta,0}U\psi$ 和 $P_0U\phi$。它们的范数平方分别为

$$
p_0=(1-\beta)u+\beta(p-u)
=\beta p+(1-2\beta)u,
\qquad q_0=v.
$$

内积只含第零坐标，因此其平方模为 $k_0=(1-\beta)uv$。结果一同理给出 $G_1^\beta$。这些参数非负，且

$$
p_0q_0-k_0=\beta(p-u)v\ge0,
\qquad
p_1q_1-k_1=\beta u(q-v)\ge0.
$$

所以两个后继确实仍在 $\mathcal G$，并满足

$$
p_0+p_1=p,\qquad q_0+q_1=q.
$$

这也解释了 $\beta>1/2$ 时 $1-2\beta$ 为负不造成困难：每个实际分支权重仍是 $u,p-u$ 的非负线性组合。更新没有除以分支权重，参数端点及零概率分支直接保留。

对任何第一步共同酉，已存结果零和一后的控制表可以各自独立指定，两个分支对绝对差异总和的贡献相加。后继代价只取决于已经计算的三元组，故任何延续策略的代价不超过递推右端的相应值。反过来，先实现任意可行 $(u,v)$，再在两个已存结果分支分别采用最优后继策略，就实现它们的和；共同酉取向的完整刻画因此给出所列 Bellman 递推。

为同时证明最大值和连续性，不需要假设随参数移动的可行域有额外正则性。选择 $G(p,q,k)^{1/2}$ 的两列作为规范候选向量。正平方根在正半定矩阵锥上连续，所以该代表在整个 $\mathcal G$ 上连续，包括零矩阵和秩一边界。

给定有限剩余长度 $n$，全部控制表属于固定紧空间

$$
\mathcal U_n
=\prod_{t=1}^{n}\prod_{h\in\{0,1\}^{t-1}}U(2).
$$

空长度时取单点空间。对这个空间中的每个控制表，分支向量由有限次矩阵乘法构成，$K_{\beta,z}$ 连续依赖 $\beta\in[0,1]$，最终绝对差异之和连续依赖规范向量、参数列及控制。紧控制空间上的最大值达到；同一固定紧空间上的连续参数化最大值函数也连续。因此 $V$ 具有所述连续性，且在每个有限历史节点可以选取最优后继策略。再由后继三元组的连续性和 $\mathcal F$ 的紧性，递推右端的最大值也达到。

只有一步时，令 $d_\beta=1-2\beta$ 并定义

$$
Y_\beta
=d_\beta|\psi\rangle\langle\psi|
-|\phi\rangle\langle\phi|+\beta pI_2.
$$

两个末次经典结果的权重差是 $UY_\beta U^\dagger$ 的两个对角元。其绝对值和不超过 $\|Y_\beta\|_1$，由共同酉选择特征基即可达到。矩阵的迹为 $p-q$，一般不为零；去掉标量部分不改变特征值间距，而间距平方为

$$
(d_\beta p+q)^2-4d_\beta k.
$$

二阶 Hermitian 矩阵的迹范数等于迹绝对值与特征值间距两者的最大值，得到所列单步公式。若 $d_\beta\ge0$，根式内由 $k\le pq$ 得到下界 $(d_\beta p-q)^2\ge0$；若 $d_\beta<0$，它是平方项加 $4|d_\beta|k$。因此该式覆盖全部 $\beta\in[0,1]$，以及 $p=0$、$q=0$、$k=0$ 等退化情形。

最后，对原始任务中的固定控制表，经典总变差是共同输入密度矩阵的凸函数；任意混态的值不超过其某个纯态分量的值，所以优化时纯输入足够。两个模型从同一个归一化纯态开始，三参数均为 $(1,1,1)$，其初始取向由第一步共同酉吸收。延续代价没有 $1/2$ 因子，恢复这个因子即得 $T_N=V_{\boldsymbol\beta}(1,1,1)/2$。证毕。

本定理给出有限历史最优值的精确连续递推，不把任意长度的最优值宣称为已有闭式，也不保证该递推的数值求解或经典控制表具有固定复杂度。三元组描述的是同一旧历史上的两个未归一化候选系统态；所有旧历史仍被保留并可供后续控制使用。

**命题 19.3（累计读取误差不能直接替代前两步）。** 令

$$
E=1-(1-\beta_1)(1-\beta_2).
$$

断言 $T_3(\beta_1,\beta_2,\beta_3)=T_2(E,\beta_3)$ 即使在 $E,\beta_3\in[0,1/2]$ 时也不成立。具体地，取三个参数均为 $1/10$，有合法的共同控制策略达到

$$
T_3(1/10,1/10,1/10)
\ge\frac3{20}+\frac{3\sqrt5}{25}
>\frac{9\sqrt5}{50}
=T_2(19/100,1/10).
$$

这里给出可达到的三步下界，它严格超过两步替代值；不宣称该下界是三步全局最优值。

证明。 取初态 $|+\rangle$、第一控制为恒等，第二步按第一结果选择

$$
U_{2,0}=\frac1{\sqrt5}\begin{pmatrix}1&2\\-2&1\end{pmatrix},
\qquad
U_{2,1}=\frac1{\sqrt5}\begin{pmatrix}2&1\\-1&2\end{pmatrix}.
$$

两个矩阵都是实正交酉。前两步后，按已存历史 $ij$ 索引的实际与理想未归一化向量分别为

$$
\begin{array}{c|c|c}
ij&\psi_{ij}&\phi_{ij}\\\hline
00&(3,-1)^{\mathsf T}/(2\sqrt{10})&(1,0)^{\mathsf T}/\sqrt{10}\\
01&(1,-3)^{\mathsf T}/(2\sqrt{10})&(0,-2)^{\mathsf T}/\sqrt{10}\\
10&(3,1)^{\mathsf T}/(2\sqrt{10})&(1,0)^{\mathsf T}/\sqrt{10}\\
11&(1,3)^{\mathsf T}/(2\sqrt{10})&(0,2)^{\mathsf T}/\sqrt{10}.
\end{array}
$$

这些向量由定义 18.1 的两步更新直接给出。例如第一结果为零时，实际第一步向量是 $(3,1)^{\mathsf T}/\sqrt{20}$，经 $U_{2,0}$ 变为 $(1,-1)^{\mathsf T}/2$，再乘两个第二步对角 Kraus 算子即得到 $\psi_{00},\psi_{01}$。理想第一步向量为 $(1,0)^{\mathsf T}/\sqrt2$，经同一控制和相应投影得到所列 $\phi_{00},\phi_{01}$；第一结果为一时计算相同。

实际四分支的权重均为 $1/4$；理想权重在 $j=0$ 时为 $1/10$，在 $j=1$ 时为 $2/5$。最后一步的差值矩阵为

$$
Y_{ij}=\frac45\psi_{ij}\psi_{ij}^{\mathsf T}
-\phi_{ij}\phi_{ij}^{\mathsf T}
+\frac1{10}\|\psi_{ij}\|^2I_2.
$$

直接相乘得

$$
Y_{00}=\frac1{200}\begin{pmatrix}21&-12\\-12&9\end{pmatrix},
\qquad
Y_{10}=\frac1{200}\begin{pmatrix}21&12\\12&9\end{pmatrix},
$$

$$
Y_{01}=\frac1{200}\begin{pmatrix}9&-12\\-12&-39\end{pmatrix},
\qquad
Y_{11}=\frac1{200}\begin{pmatrix}9&12\\12&-39\end{pmatrix}.
$$

按已存 $ij$ 选择共同末次实酉，将 $Y_{ij}$ 的特征基送到计算基。由定理 19.2 的单步证明，最后两个概率差是其两个特征值。$j=0$ 的矩阵正定，迹范数为其迹 $3/20$；$j=1$ 的矩阵行列式为负，迹范数为特征值间距 $3\sqrt5/25$。所以该策略的完整经典历史总变差为

$$
\frac12\sum_{i,j}\|Y_{ij}\|_1
=\frac3{20}+\frac{3\sqrt5}{25}.
$$

另一方面，$E=19/100$，定理 18.2 给出

$$
T_2(19/100,1/10)
=\max\left\{\frac{271}{1000},\frac{9\sqrt5}{50}\right\}
=\frac{9\sqrt5}{50}.
$$

两值的差为

$$
\frac3{20}-\frac{3\sqrt5}{50}
=\frac{3(5-2\sqrt5)}{100}>0,
$$

其中严格不等式由 $25>20$ 得到。控制表只依赖已存历史及固定模型参数，两实验始终使用同一个表，因此是定义 18.1 允许的策略，反驳所列替代断言。证毕。

在该例前两步后的实际权重都是 $p=1/4$，理想权重却分成 $q=1/10$ 与 $q=2/5$，对应平方重叠分别为 $k=9/400$ 与 $k=9/100$。后续读取分别使用这些已存历史上的候选三元组；累计标量 $E$ 不保留它们的分支权重与重叠结构。本章仍只处理丢弃最终系统、没有输入或输出参考的经典路径总变差任务。

<a id="entry-79"></a>

## 追加锚（新终端）

<a id="section-20"></a>

## 20. 实反馈的充分性与最终量子输出的价值

**定理 20.1（任意有限经典历史的实反馈达到与一维递推）。** 沿用定义 19.1 的候选分支对、参数域 $\mathcal G$ 和延续代价 $V_{\boldsymbol\beta}$。对任意有限参数列 $\boldsymbol\beta\in[0,1]^n$ 以及任意实候选向量 $\psi,\phi\in\mathbb R^2$，完整 $U(2)$ 共同历史控制的最大值都由一个全部控制属于 $O(2)$ 的反馈表达到。向量可以未归一化、为零、正交或共线；不增加可访问量子记忆或参考系统。

对 $(p,q,k)\in\mathcal G$ 且 $p>0$，定义

$$
v_\pm(u)=
\frac{\left[\sqrt{ku}\pm\sqrt{(pq-k)(p-u)}\right]^2}{p^2},
\qquad 0\le u\le p.
$$

使用定理 19.2 的后继映射 $G_0^\beta,G_1^\beta$，完整复取向域上的 Bellman 递推可以精确缩为

$$
\begin{aligned}
V_{(\beta,\boldsymbol\gamma)}(p,q,k)
&=\max_{\substack{0\le u\le p\\\sigma\in\{-,+\}}}
\bigl[
V_{\boldsymbol\gamma}
\bigl(G_0^\beta(p,q,k;u,v_\sigma(u))\bigr)\\
&\hspace{8em}
+V_{\boldsymbol\gamma}
\bigl(G_1^\beta(p,q,k;u,v_\sigma(u))\bigr)
\bigr].
\end{aligned}
$$

每个节点只需优化一个实区间及两个符号，最大值达到。空参数列仍取 $V_\varnothing(p,q,k)=|p-q|$，零权重边界为

$$
V_{\boldsymbol\beta}(0,q,0)=q,
\qquad
V_{\boldsymbol\beta}(p,0,0)=p.
$$

因此定义 18.1 的原始任务

$$
T_N(\boldsymbol\beta)
=\frac12V_{\boldsymbol\beta}(1,1,1)
$$

也可以用实纯初态和全实共同反馈表达到。

这一结论限定于所给仪器族及最终只读取经典历史的目标。它给出存在一个最优实控制表，不要求复制任意给定复控制表的全部叶分布，也不意味着每个边界取向都最优。一维递推仍保留三参数分支状态和全部已存历史，没有把任意长度的最优值化为闭式，也不保证控制树的规模具有统一效率界。

证明。 首先证明递推所需要的一条权重方向凸性。固定有限尾列 $\boldsymbol\gamma$、$P\ge0$ 和 $c\in[0,P]$，取

$$
\psi_c=\begin{pmatrix}\sqrt c\\\sqrt{P-c}\end{pmatrix},
\qquad
\phi_s=\sqrt s\,|0\rangle,
\qquad s\ge0.
$$

该向量对的三参数是 $(P,s,cs)$。对一个固定的完整共同控制表 $\pi$，令 $A_w^\pi,B_w^\pi$ 分别是末端历史 $w$ 上实际与理想的分支算子乘积，并记

$$
a_w^\pi=\|A_w^\pi\psi_c\|^2,
\qquad
b_w^\pi=\|B_w^\pi|0\rangle\|^2.
$$

固定表的代价就是

$$
J_\pi(s)=\sum_w|a_w^\pi-sb_w^\pi|.
$$

每项都是仿射函数的绝对值，故 $J_\pi$ 关于 $s$ 凸。控制表在所有可能历史上都有定义，包括零概率历史；所有 $s$ 使用同一个控制表空间，虽然实现最优值的表可以随 $s$ 变化。因此对 $s,t\ge0$、$\lambda\in[0,1]$，有

$$
\begin{aligned}
&V_{\boldsymbol\gamma}
\bigl(P,\lambda s+(1-\lambda)t,
c[\lambda s+(1-\lambda)t]\bigr)\\
&\quad=\sup_\pi J_\pi(\lambda s+(1-\lambda)t)\\
&\quad\le\lambda\sup_\pi J_\pi(s)
+(1-\lambda)\sup_\pi J_\pi(t).
\end{aligned}
$$

于是 $s\mapsto V_{\boldsymbol\gamma}(P,s,cs)$ 凸。总分支权重守恒还给出 $J_\pi(s)\le P+s$，所以这些上确界有限；空尾列及 $P=c=0$ 也包括在内。这只建立所列方向的凸性，没有假设 $V$ 关于 $(p,q,k)$ 联合凸。

接着确定共同酉可行域在固定 $u$ 时的完整切片。设 $p>0$。对一个实候选对，先用同一个实正交变换把 $\psi$ 送到 $\sqrt p|0\rangle$，再利用 $\phi$ 的无关整体符号和第二坐标的基反射，得到代表

$$
\psi=\begin{pmatrix}\sqrt p\\0\end{pmatrix},
\qquad
\phi=\begin{pmatrix}\sqrt{k/p}\\\sqrt{q-k/p}\end{pmatrix}.
$$

整体符号不改变候选密度算子或路径概率，这里不把它当作只对一个候选施加的物理控制。上述规范式也为每个 $p>0$ 的合法三元组提供实代表；由定理 19.2 的共同酉不变性，其完整复可行域就是该三元组的 $\mathcal F(p,q,k)$。

固定实际第零坐标强度 $u\in[0,p]$。任何共同复酉的第一行在去掉无关行相位后，都可以写成

$$
r_\theta=
\left(\sqrt{u/p},\ e^{i\theta}\sqrt{(p-u)/p}\right).
$$

在 $u=0$ 或 $u=p$ 时，消失坐标的相位任取。理想第零坐标强度为

$$
v(\theta)=
\frac{ku+(pq-k)(p-u)
+2\sqrt{k(pq-k)u(p-u)}\cos\theta}{p^2}.
$$

任意单位复行向量都可以补成一个酉矩阵，因此定理 19.2 的完整可行域在此 $u$ 上恰为闭区间

$$
\{v:(u,v)\in\mathcal F(p,q,k)\}
=[v_-(u),v_+(u)].
$$

区间内部由不同的 $\cos\theta$ 取得，两个端点则由实正交矩阵

$$
R_\pm(u)=
\begin{pmatrix}
\sqrt{u/p}&\pm\sqrt{(p-u)/p}\\
\mp\sqrt{(p-u)/p}&\sqrt{u/p}
\end{pmatrix}
$$

取得。由于根号项非负，$v_-(u)\le v_+(u)$；又因为它们是范数平方为 $q$ 的向量经酉变换后的一个坐标强度，所以两者均在 $[0,q]$ 中。把 $R_\pm(u)$ 与前述共同实基变换复合，就得到作用于原始实候选对的合法实控制。还原 $\phi$ 的整体符号不会改变强度，输出向量仍然为实。

若 $q=0$、$k=0$、$k=pq$，或 $u$ 为区间端点，上式中相应交叉项为零，闭区间退化成单点，公式直接适用。若 $p=0$，则 $u=k=0$，可行切片为 $[0,q]$，实旋转同样能够把实向量 $\phi$ 的第零坐标强度取成 $0$ 或 $q$。

现在固定第一步参数 $\beta\in[0,1]$ 和 $u$，记

$$
\begin{aligned}
\mathsf p_0&=(1-\beta)u+\beta(p-u),
&c_0&=(1-\beta)u,\\
\mathsf p_1&=(1-\beta)(p-u)+\beta u,
&c_1&=(1-\beta)(p-u).
\end{aligned}
$$

这些量不随 $v$ 变化，并满足

$$
\mathsf p_0-c_0=\beta(p-u)\ge0,
\qquad
\mathsf p_1-c_1=\beta u\ge0.
$$

该 $u$ 上的 Bellman 目标为

$$
F_u(v)=V_{\boldsymbol\gamma}(\mathsf p_0,v,c_0v)
+V_{\boldsymbol\gamma}(\mathsf p_1,q-v,c_1(q-v)).
$$

已经证明的权重方向凸性分别用于 $c_0\le \mathsf p_0$ 和 $c_1\le \mathsf p_1$；第二项再与仿射映射 $v\mapsto q-v$ 复合，仍然凸。因此 $F_u$ 在 $[0,q]$ 上凸。任意可行 $v$ 都满足

$$
F_u(v)\le
\max\{F_u(v_-(u)),F_u(v_+(u))\}.
$$

区间非退化时，这是把 $v$ 写成两端点凸组合后的凸性不等式；区间退化时直接相等。故在保持同一个实际强度 $u$ 的条件下，可以用一个实可达端点代替复内部点，并且不降低最优延续代价。结合定理 19.2 的完整递推，即得所陈述的一维双符号递推。最大值由该定理的连续性和 $[0,p]\times\{-,+\}$ 的紧性达到。

最后对剩余长度归纳，证明整个最优控制表可以为实。空尾列代价为 $|p-q|$，无需控制。若 $p=0$，实际所有分支权重为零，任意控制表的代价都是理想总权重 $q$；同理 $q=0$ 时恒为 $p$。这也证明所列零权重边界。

对非零实际候选，取一个达到 Bellman 最大值的第一步 $(u,v)$，用上述不减值端点替换后，它仍然达到完整最大值。用实共同控制实现该端点；由于实际 $K_{\beta,z}$ 与理想 $P_z$ 都是实矩阵，两种结果后的候选对仍然为实。在每个已存结果分支，归纳假设给出达到完整复控制延续值的实尾表。两个尾表可以按不同的已存结果分别指定，与第一步组合后就成为全实最优反馈表。

该选择只使用固定候选模型、参数及已存历史，两实验始终调用同一张表。证明没有进行分支归一化，也没有除以 $\beta$ 或 $1-\beta$，因此零子分支和 $\beta=0,1$ 均被覆盖。取共同实初态 $|0\rangle$，再用定理 19.2 的 $T_N=V_{\boldsymbol\beta}(1,1,1)/2$，得到原始任务的实达到结论。证毕。

**定理 20.2（最终量子输出的显式访问差距与等号分类）。** 在定义 18.1 的同一无量子记忆、无输入输出参考的控制类中，固定 $N\ge1$ 和 $\beta_t\in[0,1]$，令

$$
f=\beta_N,
\qquad
s=\prod_{t=1}^{N-1}\sqrt{1-\beta_t},
\qquad
E=1-s^2,
$$

其中空积为一。再定义

$$
U(E,f)=\frac{f+\sqrt{f^2+4(1-f)E}}2,
\qquad
\delta_N=\sqrt{1-(1-f)s^2}.
$$

若最终保留全部历史和活动量子比特 $H_N\otimes S$，则最优输出迹距离为 $\delta_N$：上界由定理 16.3 给出，定理 17.2 用实反馈和无参考的共同输入达到。若最终丢弃活动系统，只比较经典历史，则有统一上界

$$
T_N(\beta_1,\ldots,\beta_N)\le U(E,f).
$$

若所有 $\beta_t<1$ 且末次 $0<f<1$，则 $s>0$，并且

$$
T_N\le U(E,f)<\delta_N,
\qquad
\delta_N-T_N
\ge\frac{f(1-f)s^2}{2(2-f)}>0.
$$

在完整参数域上，两个观察任务最优值相等的条件恰为

$$
T_N(\beta_1,\ldots,\beta_N)=\delta_N
\quad\Longleftrightarrow\quad
\bigl[\beta_N=0\ \text{或存在 }t\le N\text{ 使 }\beta_t=1\bigr].
$$

证明。 固定共同历史控制表。经典总变差是共同输入密度矩阵的凸函数，所以证明输入无关的上界时纯输入足够。取共同单位初态，在末次控制之前，对长度为 $N-1$ 的旧历史 $h$，记实际与理想的未归一化分支向量为 $\psi_h,\phi_h$。

第 $t$ 次实际与理想结果算子满足

$$
\sum_{z=0}^1P_zK_{\beta_t,z}
=\sqrt{1-\beta_t}\,I_2.
$$

因此，设该节点调用的共同控制为 $W_h$，便有

$$
\sum_z
\langle P_zW_h\phi_h,K_{\beta_t,z}W_h\psi_h\rangle
=\sqrt{1-\beta_t}\langle\phi_h,\psi_h\rangle.
$$

从共同初态的内积一开始，逐层对所有历史求和，得到

$$
\sum_{|h|=N-1}\langle\phi_h,\psi_h\rangle=s.
$$

这只约束全部历史上的内积之和，不要求每个分支内积单独为实或非负。$N=1$ 时只有空历史，该等式就是初态内积一。

对最后共同控制 $W_h$，定义两种候选前缀若都接受完美指针读取时的经典分布

$$
P(h,z)=|\langle z|W_h\psi_h\rangle|^2,
\qquad
Q(h,z)=|\langle z|W_h\phi_h\rangle|^2.
$$

这里 $P$ 是用于比较的分布，未声称该完美读取已经在实际过程中执行；$Q$ 则恰好是理想全历史分布。两者总质量均为一。它们的 Bhattacharyya 重叠满足

$$
\begin{aligned}
B(P,Q)
&:=\sum_{h,z}\sqrt{P(h,z)Q(h,z)}\\
&\ge\left|\sum_{h,z}
\overline{\langle z|W_h\phi_h\rangle}
\langle z|W_h\psi_h\rangle\right|\\
&=\left|\sum_h\langle\phi_h,\psi_h\rangle\right|=s.
\end{aligned}
$$

实际末次仪器的结果效应为

$$
K_{f,z}^\dagger K_{f,z}
=(1-f)P_z+fP_{1-z}.
$$

所以实际全历史分布 $R$ 精确满足

$$
R(h,z)=(1-f)P(h,z)+fP(h,1-z).
$$

令 $\tau(h,z)=(h,1-z)$，则对任意经典事件 $A$，

$$
\begin{aligned}
R(A)-Q(A)
&=(1-f)P(A)+fP(\tau(A))-Q(A)\\
&\le f+(1-f)P(A)-Q(A).
\end{aligned}
$$

记 $a=1-f$。向量 $aP-Q$ 的元素之和为 $-f$，故其正部之和为

$$
\max_A\bigl[aP(A)-Q(A)\bigr]
=\frac{\|aP-Q\|_1-f}{2}.
$$

概率分布的总变差等于正事件差的最大值，因此

$$
\operatorname{TV}(R,Q)
\le\frac{f+\|aP-Q\|_1}{2}.
$$

对每个坐标分解平方差，再用 Cauchy--Schwarz 不等式，得到

$$
\begin{aligned}
\|aP-Q\|_1
&=\sum_{h,z}
\left|\sqrt{aP(h,z)}-\sqrt{Q(h,z)}\right|
\left(\sqrt{aP(h,z)}+\sqrt{Q(h,z)}\right)\\
&\le\sqrt{\bigl(a+1-2\sqrt a\,B(P,Q)\bigr)
\bigl(a+1+2\sqrt a\,B(P,Q)\bigr)}\\
&=\sqrt{(a+1)^2-4aB(P,Q)^2}\\
&\le\sqrt{(2-f)^2-4(1-f)s^2}\\
&=\sqrt{f^2+4(1-f)E}.
\end{aligned}
$$

于是每个固定策略和纯输入的代价都不超过 $U(E,f)$。对混合输入用同一策略下的凸性，再对全部共同策略取上确界，得到 $T_N\le U(E,f)$。推导使用完整 $U(2)$ 控制表，因此该界不依赖先将控制限制为实。

现设 $s>0$ 且 $0<f<1$，简记 $U=U(E,f)$。它满足二次等式

$$
U^2-fU=(1-f)(1-s^2).
$$

由于 $s>0$，定义中的根式严格小于 $2-f$，所以 $0<U<1$。直接相减得到

$$
\delta_N^2-U^2=f(1-U)>0,
$$

因而 $U<\delta_N$。进一步，由同一个二次等式可得

$$
(1-U)(1+U-f)=(1-f)s^2,
$$

于是

$$
\begin{aligned}
\delta_N-U
&=\frac{f(1-f)s^2}
{(\delta_N+U)(1+U-f)}\\
&\ge\frac{f(1-f)s^2}{2(2-f)}>0.
\end{aligned}
$$

这里两个分母因子均正，并且 $\delta_N,U\le1$。结合 $T_N\le U$，即得所述统一正差距。

还需确定其余参数边界。若末次 $f=0$，则 $U(E,0)=\sqrt E=\delta_N$，命题 18.3 的最终完美读取构造达到这一值，故 $T_N=\delta_N$。

若存在某个 $\beta_t=1$，则 $\delta_N=1$。取指针初态 $|0\rangle$，并在每个历史节点都用恒等控制。因为所有结果算子在指针基中对角，实际非零分支向量始终沿 $|0\rangle$ 方向；理想历史恒为全零，而在所选阶段 $t$，实际结果必为一。因此两种全历史分布的支撑不交，经典总变差达到一。这也包括末次 $f=1$。

反过来，若末次参数不为零且没有参数等于一，则所有 $\beta_t<1$，同时 $0<f<1$，恰好属于已经证明的严格差距条件。因此其最优值不相等。参数域已被这几种情况穷尽，得到所陈述的充要分类。

当 $N=1$ 时，$s=1$、$E=0$，上界给出 $U(0,f)=f$，由指针初态达到，因而一次经典结果的最优差异为 $f$；保留最终量子输出时则为 $\sqrt f$。一般有限步中，$E$ 只用于本定理的统一上界，没有取代第 19 章的分支三参数递推；命题 19.3 所排除的累计标量替代仍然不成立。证毕。

<a id="entry-81"></a>

## 追加锚（新终端）

<a id="section-21"></a>

## 21. 惰性参考对两步经典历史辨识的严格增益

**定义 21.1（仅在输入和最终观察时使用的参考）。** 沿用定义 18.1 的二标签记录仪器与共同系统控制表，但允许初始活动系统 $S=\mathbb C^2$ 与一个有限维参考系统 $R$ 处于联合态 $\omega_{SR}$。每个过程内控制只作用于 $S$，只依赖已经存储的经典历史，实际与理想过程始终使用同一个表。所有记录单元新鲜准备，量子记录余系统读取后不再耦合，不后选择；没有另一个可访问辅助量子记忆，也不在过程内对 $R$ 施加操作或与它耦合。

经过 $N$ 步后丢弃活动系统 $S$，保留完整经典历史 $H_N$ 和惰性参考 $R$，允许最终联合测量 $H_N R$。对固定控制表 $U$，记从初始系统到经典历史的两个通道为

$$
\mathcal C_{\mathrm{actual},N}^U,
\qquad
\mathcal C_{\mathrm{ideal},N}^U:
\mathcal L(S)\longrightarrow\mathcal L(H_N).
$$

定义该访问范围中的最优差异为

$$
\begin{aligned}
T_N^{\mathrm{ref}}(\boldsymbol\beta)
&=\sup_{U,R,\omega_{SR}}
\frac12\left\|
\left[
\bigl(\mathcal C_{\mathrm{actual},N}^U
-\mathcal C_{\mathrm{ideal},N}^U\bigr)
\otimes\operatorname{id}_R
\right](\omega_{SR})
\right\|_1\\
&=\sup_U\frac12\left\|
\mathcal C_{\mathrm{actual},N}^U
-\mathcal C_{\mathrm{ideal},N}^U
\right\|_\diamond.
\end{aligned}
$$

输入上确界取两实验共同使用的归一化联合密度矩阵，参考维数可以是任意有限值。第二行是通道辨识中允许输入参考的半 diamond 距离。取平凡参考即可恢复定义 18.1 的观察类，因此 $T_N\le T_N^{\mathrm{ref}}$；下条给出该包含关系导致严格差异的两步见证。

**命题 21.2（一个惰性参考量子比特的显式两步优势）。** 取

$$
e=\beta_1=\frac12,
\qquad
f=\beta_2=\frac15.
$$

在定义 21.1 的任务中，使用一个参考量子比特，准备共同初态

$$
|\Psi\rangle_{SR}
=\frac12|00\rangle+\frac{\sqrt3}{2}|11\rangle,
\qquad
\rho_S=\operatorname{diag}\left(\frac14,\frac34\right),
$$

其中第一个张量因子是活动系统。第一共同控制取恒等；第一结果为 $i$ 时，第二共同系统控制取

$$
U_{2,0}=H
=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},
\qquad
U_{2,1}=X
=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

该策略在最终 $H_2R$ 输出上达到

$$
\frac{13+\sqrt{127}}{40}.
$$

因而

$$
T_2^{\mathrm{ref}}(1/2,1/5)
\ge\frac{13+\sqrt{127}}{40}
>\frac35
=T_2(1/2,1/5).
$$

这是指定策略的可达下界，不宣称已经求出 $T_2^{\mathrm{ref}}$ 的精确最优值。所有系统控制都为实正交矩阵；参考从初始制备到最终测量之间始终接受恒等操作。

证明。 令 $P_j=|j\rangle\langle j|$。由于 $e=1/2$，实际第一步的两个 Kraus 算子均为 $I_2/\sqrt2$，理想第一步算子则为 $P_i$。在 $f=1/5$ 时，实际末次结果效应为

$$
K_{2,j}^\dagger K_{2,j}
=\frac45P_j+\frac15P_{1-j}.
$$

因此对历史 $ij$，实际与理想的初始系统效应分别为

$$
E_{ij}^{\mathrm{actual}}
=\frac12U_{2,i}^\dagger
\left(\frac45P_j+\frac15P_{1-j}\right)U_{2,i},
$$

$$
E_{ij}^{\mathrm{ideal}}
=P_iU_{2,i}^\dagger P_jU_{2,i}P_i.
$$

记 $M_{ij}=E_{ij}^{\mathrm{actual}}-E_{ij}^{\mathrm{ideal}}$，代入 $H$ 和 $X$ 得到

$$
M_{00}=\frac1{20}\begin{pmatrix}-5&3\\3&5\end{pmatrix},
\qquad
M_{01}=\frac1{20}\begin{pmatrix}-5&-3\\-3&5\end{pmatrix},
$$

$$
M_{10}=\operatorname{diag}\left(\frac1{10},-\frac35\right),
\qquad
M_{11}=\operatorname{diag}\left(\frac25,\frac1{10}\right).
$$

例如，$H^\dagger P_0H$ 的每个矩阵元均为 $1/2$，而 $P_0H^\dagger P_0HP_0=P_0/2$，所以相减后得到 $M_{00}$。其余三式使用互补投影及 $X^\dagger P_0X=P_1$。四个差效应之和为零，与两种历史分布均归一化一致。

对所选 Schmidt 初态，系统效应 $E$ 对应的未归一化参考输出为

$$
\sqrt{\rho_S}\,E^{\mathsf T}\sqrt{\rho_S}.
$$

这是因为该参考矩阵的 $(a,b)$ 元为

$$
\sqrt{(\rho_S)_{aa}(\rho_S)_{bb}}\,
\langle b|E|a\rangle,
$$

可由初态在 $|a\rangle_S|a\rangle_R$ 基中的展开直接求出。因此两个最终 $H_2R$ 输出之差是按历史分块的 Hermitian 算子

$$
\Delta_{H_2R}
=\sum_{i,j}|ij\rangle\langle ij|\otimes D_{ij},
\qquad
D_{ij}=\sqrt{\rho_S}\,M_{ij}^{\mathsf T}\sqrt{\rho_S}.
$$

使用 $\sqrt{\rho_S}=\operatorname{diag}(1/2,\sqrt3/2)$，四个参考差块明确为

$$
D_{00}=\frac1{80}\begin{pmatrix}-5&3\sqrt3\\3\sqrt3&15\end{pmatrix},
\qquad
D_{01}=\frac1{80}\begin{pmatrix}-5&-3\sqrt3\\-3\sqrt3&15\end{pmatrix},
$$

$$
D_{10}=\operatorname{diag}\left(\frac1{40},-\frac9{20}\right),
\qquad
D_{11}=\operatorname{diag}\left(\frac1{10},\frac3{40}\right).
$$

前两个矩阵的迹均为 $1/8$，行列式均为 $-51/3200$，所以两个特征值异号。各自的迹范数等于特征值间距：

$$
\|D_{00}\|_1=\|D_{01}\|_1
=\sqrt{\frac1{64}+\frac{204}{3200}}
=\frac{\sqrt{127}}{40}.
$$

另外两个对角块给出

$$
\|D_{10}\|_1=\frac{19}{40},
\qquad
\|D_{11}\|_1=\frac7{40}.
$$

由于不同经典历史对应正交块，整体迹范数是各块迹范数之和，故

$$
\frac12\|\Delta_{H_2R}\|_1
=\frac12\sum_{i,j}\|D_{ij}\|_1
=\frac{13+\sqrt{127}}{40}.
$$

最终观察者可以先读取历史 $ij$，再在参考上测量对应 $D_{ij}$ 的正负谱子空间，以达到该可区分性。该测量只发生在两个记录步骤之后，没有对参考施加过程内控制，也没有丢弃任何历史。

另一方面，定理 18.2 已经优化全部无参考输入和共同系统控制，给出

$$
T_2(1/2,1/5)
=\max\left\{\frac35,\sqrt{\frac{17}{50}}\right\}
=\frac35,
$$

其中 $9/25=18/50>17/50$。所构造参考策略相对此完整无参考最优值的增量为

$$
\frac{13+\sqrt{127}}{40}-\frac35
=\frac{\sqrt{127}-11}{40}>0,
$$

严格不等式由 $127>121$ 得到。这证明了被动保留的初始纠缠参考可以提高该两步任务的最优值。证毕。

<a id="entry-83"></a>

## 追加锚（新终端）

<a id="section-22"></a>

## 22. 一个可操作记忆比特的精确最优值与经典达到边界

**定义 22.1（丢弃活动系统而保留可操作记忆）。** 沿用定义 17.1 的二结果仪器族。活动系统 $S=\mathbb C^2$，参数 $\beta_t\in[0,1]$，实际与理想结果算子分别为

$$
K_{t,z}=\sqrt{1-\beta_t}\,P_z+\sqrt{\beta_t}\,P_{1-z},
\qquad P_z=|z\rangle\langle z|,
\qquad z\in\{0,1\}.
$$

允许一个任意非零有限维可操作量子记忆 $M$。每次仪器之前，可以根据全部已存经典历史，在 $S\otimes M$ 上调用预先指定的共同 CPTP 控制；实际和理想实验调用同一张控制表。仪器只作用于 $S$，每次读取的经典结果追加到 $H_t$，旧历史保持不变。已丢弃的控制余系统或仪器余系统不再耦合，无后选择。末次仪器之后丢弃 $S$，输出为 $H_N\otimes M$。

固定 $M$ 和共同控制表 $\Pi$ 后，这定义实际与理想通道

$$
\mathcal C_{{\rm A},N}^{\Pi},\mathcal C_{{\rm J},N}^{\Pi}:
\mathcal L(S\otimes M)\longrightarrow\mathcal L(H_N\otimes M).
$$

记无参考共同输入的最优输出差异为

$$
T_N^{\rm mem}(\boldsymbol\beta)
=\sup_{\substack{1\le\dim M<\infty,\,\Pi\\
\rho\ge0,\,\operatorname{tr}\rho=1}}
\frac12\left\|
\mathcal C_{{\rm A},N}^{\Pi}(\rho)
-\mathcal C_{{\rm J},N}^{\Pi}(\rho)
\right\|_1.
$$

输入 $\rho$ 位于 $S\otimes M$。对固定通道还可以使用惰性参考 $R$ 定义 diamond 距离，此时控制不作用于 $R$，最终同时保留 $R$。$M$ 允许与活动系统耦合；这一访问权限不同于仅保留一个始终不可操作的参考系统。

**定理 22.2（精确记忆最优值及一次 SWAP 的达到）。** 对定义 22.1 的任意有限 $N\ge1$ 和完整参数域 $\beta_t\in[0,1]$，令

$$
f=\beta_N,\qquad a=1-f,\qquad
s=\prod_{t=1}^{N-1}\sqrt{1-\beta_t},\qquad E=1-s^2,
$$

其中空积为一。使用第 20.2 条的函数

$$
U(E,f)=\frac{f+\sqrt{f^2+4(1-f)E}}2
=\frac{f+\sqrt{(a+1)^2-4as^2}}2,
$$

有

$$
T_N^{\rm mem}(\boldsymbol\beta)=U(E,f).
$$

更强地，每个固定有限维记忆及共同控制表都满足

$$
\frac12\left\|
\mathcal C_{{\rm A},N}^{\Pi}
-\mathcal C_{{\rm J},N}^{\Pi}
\right\|_\diamond\le U(E,f).
$$

一个初态为 $|0\rangle$ 的记忆量子比特即可达到等号：前 $N-1$ 步完全不操作记忆，只在活动比特上执行共同实反馈；末次仪器前把 $S$ 与 $M$ 作一次 SWAP。达到使用共同输入 $|0\rangle_S|0\rangle_M$，无需惰性参考。该结论给出此仪器族及保留输出的精确最优值，不断言每个参数选择都比无记忆经典历史任务更优。

证明。先证明对任意记忆和参考一致的上界。给共同输入作纯化，并给实际、理想实验中的共同 CPTP 控制使用同一个 Stinespring 等距。每次仪器使用结果标签及其丢弃副本，实际、理想两种等距的交叉算子为

$$
\sum_zP_zK_{t,z}=\sqrt{1-\beta_t}\,I_S.
$$

共同历史控制保持完整纯化的内积，每次仪器则将其乘以所示标量。经过前 $N-1$ 次仪器及末次共同控制后，全部保留与纯化寄存器上的两个单位向量可以取为 $|A\rangle,|J\rangle$，满足

$$
\langle J|A\rangle=s.
$$

纯化中保留的丢弃寄存器只用于分析，不允许重新接回协议；惰性参考也始终不参与控制。

在两候选上都假设末次作完美指针读取并丢弃 $S$，得到归一化经典量子态 $\mathsf P,\mathsf Q$，其空间为 $H_N\otimes M\otimes R$。它们是 $|A\rangle,|J\rangle$ 经同一通道的输出，而 $\mathsf Q$ 正好是理想最终态。对 Hermitian 算子的迹范数收缩及秩一差值公式给出

$$
\begin{aligned}
\|a\mathsf P-\mathsf Q\|_1
&\le\|a|A\rangle\langle A|-|J\rangle\langle J|\|_1\\
&=\sqrt{(a+1)^2-4a|\langle J|A\rangle|^2}\\
&=\sqrt{(a+1)^2-4as^2}.
\end{aligned}
$$

令 $\tau$ 只翻转最后一个经典结果位，保持旧历史、记忆和参考不动。对末次仪器前任意历史块 $\omega_h$，实际结果 $z$ 的记忆参考块为

$$
\begin{aligned}
&\operatorname{Tr}_S\bigl[
(K_{N,z}\otimes I)\omega_h(K_{N,z}\otimes I)
\bigr]\\
&\qquad=a\langle z|\omega_h|z\rangle
+f\langle1-z|\omega_h|1-z\rangle.
\end{aligned}
$$

两指针之间的交叉项在部分迹后为零，故实际最终态严格满足

$$
\mathsf R=a\mathsf P+f\tau(\mathsf P).
$$

因为 $\tau(\mathsf P)$ 是迹范数为一的密度矩阵，

$$
\begin{aligned}
\frac12\|\mathsf R-\mathsf Q\|_1
&\le\frac12\bigl(\|a\mathsf P-\mathsf Q\|_1+f\bigr)\\
&\le U(E,f).
\end{aligned}
$$

这对任意共同输入及参考一致，因而也是所述半 diamond 上界。

为构造达到，把定理 17.2 的零对角递推用于不等初始权重。前缀中不操作记忆，实际与理想物理分支向量记为 $x_h,y_h$，初态均为 $|0\rangle$。只在控制表计算中引入

$$
\psi_h=\sqrt a\,x_h,\qquad\phi_h=y_h,
$$

并定义

$$
\begin{aligned}
p_h&=\|\psi_h\|^2,&q_h&=\|\phi_h\|^2,
&c_h&=\phi_h^{\mathsf T}\psi_h,\\
r_k&=\frac{2\sqrt a}{a+1}
\prod_{t=1}^k\sqrt{1-\beta_t}.
\end{aligned}
$$

逐层构造共同实控制，使每个深度 $k$ 的历史满足

$$
2c_h=r_k(p_h+q_h).
$$

初始 $p=a,q=1,c=\sqrt a$，故关系成立。分母 $a+1$ 总为正，而且 $0\le r_k\le1$。

固定一个深度 $t-1$ 的节点，暂略历史下标，写 $\alpha=\sqrt{1-\beta_t}$、$b=\sqrt{\beta_t}$、$r=r_{t-1}$。定义实对称矩阵

$$
X=\psi\phi^{\mathsf T}+\phi\psi^{\mathsf T}
-r\bigl[(\alpha^2-b^2)\psi\psi^{\mathsf T}
+\phi\phi^{\mathsf T}\bigr]-rb^2pI_2.
$$

由归纳关系及 $\alpha^2+b^2=1$，

$$
\operatorname{tr}X
=2c-r[(\alpha^2-b^2)p+q]-2rb^2p
=2c-r(p+q)=0.
$$

按定理 17.2 的实对称谱基构造，取正交归一的 $v_0,v_1$ 使 $v_z^{\mathsf T}Xv_z=0$，并以 $v_z^{\mathsf T}$ 为共同控制矩阵的第 $z$ 行。$X=0$ 时任取实正交基。令 $u_z=v_z^{\mathsf T}\psi$、$w_z=v_z^{\mathsf T}\phi$，子分支满足

$$
p_{hz}=b^2p+(\alpha^2-b^2)u_z^2,
\qquad q_{hz}=w_z^2,
\qquad c_{hz}=\alpha u_zw_z.
$$

零对角关系等价于 $2u_zw_z=r(p_{hz}+q_{hz})$，两边乘以 $\alpha$ 即得

$$
2c_{hz}=r_t(p_{hz}+q_{hz}).
$$

这个递推没有除以 $a,\alpha,b,p,q$，所以零向量、零概率历史及 $\beta_t=0,1$ 都包括在内。$a=0$ 时加权实际向量全为零，但物理实际向量仍按同一个控制表定义；加权只用于选择控制，不要求从零向量反演物理分支。仪器完备性给出每层总权重 $\sum_hp_h=a$、$\sum_hq_h=1$。

令 $\rho_A,\rho_J$ 是前 $N-1$ 步的历史加活动系统输出。逐历史使用秩一差值公式，得到

$$
\begin{aligned}
\|a\rho_A-\rho_J\|_1
&=\sum_{|h|=N-1}\sqrt{(p_h+q_h)^2-4c_h^2}\\
&=\sum_{|h|=N-1}(p_h+q_h)\sqrt{1-r_{N-1}^2}\\
&=\sqrt{(a+1)^2-4as^2}.
\end{aligned}
$$

最后把活动比特与尚未参与、初态为 $|0\rangle$ 的记忆比特 $M$ 作 SWAP。前缀候选量子态进入记忆，两实验中的活动系统都成为 $|0\rangle$。末次实际结果零、一的概率为 $a,f$，理想结果恒为零。识别 SWAP 前后的比特空间，最终输出差关于末次经典结果的两个直和块恰为

$$
(a\rho_A-\rho_J)\ \oplus\ f\rho_A.
$$

所以最终迹距离为

$$
\frac12\bigl(\|a\rho_A-\rho_J\|_1+f\bigr)=U(E,f).
$$

无参考纯输入已达到参考一致上界，故该固定控制表的半 diamond 距离也达到同一值。$N=1$ 时前缀为空，结果为 $f$；$f=0$ 时为 $\sqrt{1-s^2}$；$f=1$ 或某个前缀参数为一时为一。有限反馈表按模型参数与已存历史预先计算，两实验始终使用同一表。证毕。

**定理 22.3（无记忆经典历史的等号分类）。** 令 $T_N$ 仍表示定义 18.1 的原始任务：单活动量子比特、全部共同历史依赖 $U(2)$ 控制、无可操作记忆、无输入参考，末端只保留经典历史。对完整参数域 $\beta_t\in[0,1]$，$N=1$ 时总有

$$
T_1=U(0,f)=f.
$$

对 $N\ge2$，有充要分类

$$
T_N=U(E,f)
\quad\Longleftrightarrow\quad
\left[
\beta_{N-1}=0\ \text{或}\ \beta_N=0
\ \text{或存在 }t\le N\text{ 使 }\beta_t=1
\right].
$$

因此，若 $N\ge2$、$0<\beta_N<1$、所有 $\beta_t<1$ 且 $\beta_{N-1}>0$，则

$$
T_N<U(E,f)=T_N^{\rm mem}.
$$

这里比较的是两个控制与访问任务各自优化后的值。严格情形中一个可操作记忆比特足以取得增益；所列等号边界则无需该记忆。该分类不确定只允许惰性参考而禁止系统参考耦合的最优值。

证明。第 20.2 条给出 $T_N\le U(E,f)$。$N=1$ 时，指针初态达到 $f=U(0,f)$。若 $f=0$，命题 18.3 的最终完美读取达到 $\sqrt E=U(E,0)$。若某个 $\beta_t=1$，取指针初态和恒等控制，实际与理想历史支撑不交，达到 $1=U(E,f)$。

设 $N\ge2$ 且 $\beta_{N-1}=0$。对前 $N-2$ 步使用定理 22.2 证明中的加权实反馈，得到历史加活动系统态 $\rho_A,\rho_J$，满足

$$
\|a\rho_A-\rho_J\|_1
=\sqrt{(a+1)^2-4as^2}.
$$

倒数第二步参数为零，所以 $s$ 与前 $N-2$ 步的重叠乘积相同。对每个长度 $N-2$ 的历史 $g$，将 Hermitian 块

$$
D_g=a|x_g\rangle\langle x_g|-|y_g\rangle\langle y_g|
$$

的特征基通过共同系统酉送入指针基，随后作倒数第二次完美读取。若该步后的两种经典分布为 $p_h,q_h$，逐块读取特征值给出

$$
\sum_h|ap_h-q_h|=\|a\rho_A-\rho_J\|_1.
$$

读取结果 $y$ 后，两实验中非零系统分支都沿已知指针 $|y\rangle$。按该经典结果使用 $X^y$ 把它送到 $|0\rangle$，其中 $X|0\rangle=|1\rangle$、$X|1\rangle=|0\rangle$。再执行末次仪器，末次结果零、一上的实际分布分别为 $ap_h,fp_h$，理想分布为 $q_h,0$，故

$$
\operatorname{TV}
=\frac12\sum_h\bigl(|ap_h-q_h|+fp_h\bigr)
=U(E,f).
$$

该方案完全不使用量子记忆，零概率历史任意指定控制。$N=2$ 时前缀为空，上述构造仍成立。

剩下证明必要性。设 $N\ge2$、$0<f<1$、所有参数小于一且 $\beta_{N-1}>0$。于是 $a>0$、$s>0$，并有 $0<\beta_{N-1}<1$。若 $T_N=U(E,f)$，由定理 19.2 的纯输入归约和有限控制树紧性，存在纯初态及共同控制表真正达到此值。

固定该策略，在末次控制前，对每个长度 $N-1$ 的历史 $h$ 记未归一化候选向量为 $x_h,y_h$，末次控制为 $W_h$。定义

$$
P(h,z)=|\langle z|W_hx_h\rangle|^2,
\qquad
Q(h,z)=|\langle z|W_hy_h\rangle|^2.
$$

实际最终分布是 $R=aP+f\tau P$，其中 $\tau$ 翻转末次结果。第 20.2 条的内积递推与三角不等式给出

$$
\sum_h\langle y_h,x_h\rangle=s,
\qquad
B(P,Q):=\sum_{h,z}\sqrt{P(h,z)Q(h,z)}\ge s.
$$

上界可以写为

$$
\begin{aligned}
2\operatorname{TV}(R,Q)
&=\|aP-Q+f\tau P\|_1\\
&\le\|aP-Q\|_1+f\\
&\le\sqrt{(a+1)^2-4aB(P,Q)^2}+f\\
&\le\sqrt{(a+1)^2-4as^2}+f=2U(E,f).
\end{aligned}
$$

达到最终界强制每一步等号。因为 $a,s>0$，最后一步等号强制 $B(P,Q)=s$。

考察加权 Cauchy--Schwarz 步骤。对坐标 $i=(h,z)$，令

$$
u_i=|\sqrt{aP_i}-\sqrt{Q_i}|,
\qquad v_i=\sqrt{aP_i}+\sqrt{Q_i}.
$$

等号要求存在 $\lambda\ge0$ 使所有坐标满足 $u_i=\lambda v_i$，其中

$$
\lambda^2
=\frac{a+1-2\sqrt a\,B(P,Q)}
{a+1+2\sqrt a\,B(P,Q)}<1.
$$

分母正，而 $a>0$、$B(P,Q)=s>0$。若某坐标 $P_i,Q_i$ 恰有一个为零，则 $u_i=v_i>0$，与 $\lambda<1$ 矛盾。因此 $P,Q$ 逐坐标具有相同支撑。

因为 $\sum_i(aP_i-Q_i)=-f<0$，存在负坐标 $(h,z)$，使 $d_i=aP_i-Q_i<0$。第一个迹范数三角等号逐坐标要求

$$
P(h,1-z)=0.
$$

否则负数 $d_i$ 与严格正的 $fP(h,1-z)$ 相加会使三角不等式严格。由相同支撑，$Q(h,1-z)=0$；该负坐标自身则有 $P(h,z),Q(h,z)>0$。所以末次控制后的两候选向量都是同一指针 $|z\rangle$ 的非零倍数，控制前的 $x_h,y_h$ 也非零且共线。

写 $h=g\ell$，其中 $\ell$ 为倒数第二次结果。令倒数第二次控制后的父候选为

$$
\xi=U_{N-1,g}x_g,
\qquad \eta=U_{N-1,g}y_g,
$$

并记 $\alpha=\sqrt{1-\beta_{N-1}}>0$、$b=\sqrt{\beta_{N-1}}>0$。于是

$$
x_{g\ell}=(\alpha P_\ell+bP_{1-\ell})\xi,
\qquad y_{g\ell}=P_\ell\eta.
$$

$y_{g\ell}$ 非零并沿 $|\ell\rangle$，共线性强制实际向量也沿该指针。由于 $\alpha,b>0$，这迫使 $\xi$ 非零并沿 $|\ell\rangle$。因此兄弟历史 $h'=g(1-\ell)$ 的实际向量

$$
x_{h'}=(\alpha P_{1-\ell}+bP_\ell)\xi=b\xi
$$

非零且沿 $|\ell\rangle$。如果理想向量 $y_{h'}=P_{1-\ell}\eta$ 为零，该历史下 $Q$ 的两个末次坐标都为零，而 $P$ 至少一个为正，违反相同支撑。故 $y_{h'}$ 非零并沿 $|1-\ell\rangle$，从而

$$
\langle y_{h'},x_{h'}\rangle=0.
$$

但相同支撑和非零分支权重又强制

$$
B_{h'}:=\sum_z\sqrt{P(h',z)Q(h',z)}>0.
$$

对每个历史都有 $B_h\ge|\langle y_h,x_h\rangle|$，对 $h'$ 严格。因此

$$
B(P,Q)=\sum_hB_h
>\sum_h|\langle y_h,x_h\rangle|
\ge\left|\sum_h\langle y_h,x_h\rangle\right|=s,
$$

与等号所需 $B(P,Q)=s$ 矛盾。没有策略达到 $U(E,f)$，而原任务的最优值确实达到，所以 $T_N<U(E,f)$。参数域已经穷尽，得到所述分类。证毕。

<a id="entry-85"></a>

## 追加锚（新终端）

<a id="section-23"></a>

## 23. 惰性参考的实参数归约与记忆权限分离

**定理 23.1（两步惰性参考任务的有限实参数最大值）。** 在定义 21.1 的两步任务中，令 $e=\beta_1,f=\beta_2\in[0,1]$。任意有限参考维数、共同混合输入及复系统酉控制的上确界，可以由一个参考量子比特、实系数纯输入、第一控制恒等及两个实正交末次控制达到。

更明确地，定义紧参数域

$$
\mathcal D_{\mathbb R}^+
=\left\{
\rho(t,w)=\begin{pmatrix}t&w\\w&1-t\end{pmatrix}:
0\le t\le1,\quad 0\le w\le\sqrt{t(1-t)}
\right\}.
$$

记第一步的实际 Kraus 算子为

$$
K_i=\sqrt{1-e}\,P_i+\sqrt e\,P_{1-i},
\qquad i\in\{0,1\}.
$$

对每个第一结果 $i$，独立取 $u_i\in[0,1]$ 及 $\eta_i\in\{-1,1\}$，并定义互补实秩一投影

$$
Q_{i0}=
\begin{pmatrix}
u_i&\eta_i\sqrt{u_i(1-u_i)}\\
\eta_i\sqrt{u_i(1-u_i)}&1-u_i
\end{pmatrix},
\qquad Q_{i1}=I_2-Q_{i0}.
$$

两个实验对应的初始系统差效应为

$$
M_{ij}=K_i\bigl[fI_2+(1-2f)Q_{ij}\bigr]K_i-P_iQ_{ij}P_i.
$$

对二阶 Hermitian 矩阵 $M$ 和任意二阶密度矩阵 $\rho$，定义

$$
\mathfrak n_\rho(M)=
\begin{cases}
\sqrt{[\operatorname{tr}(\rho M)]^2-4\det(\rho)\det(M)},&\det(M)<0,\\
|\operatorname{tr}(\rho M)|,&\det(M)\ge0.
\end{cases}
$$

则精确最优值为

$$
T_2^{\mathrm{ref}}(e,f)
=\frac12
\max_{\substack{\rho\in\mathcal D_{\mathbb R}^+\\
u_0,u_1\in[0,1],\ \eta_0,\eta_1\in\{-1,1\}}}
\sum_{i,j=0}^1\mathfrak n_\rho(M_{ij}).
$$

该式仍是四个连续实参数及两个符号的有限最大化，并未把 $T_2^{\mathrm{ref}}$ 求成参数 $e,f$ 的显式函数。实控制充分性在本条仅针对两步、末端丢弃活动系统的参考任务；不将其外推到任意长度的参考反馈协议。

证明。固定控制表时，最终差算子的迹范数关于共同输入密度矩阵是凸函数。将任意混合输入分解成纯态，其中至少一个纯态分量的值不小于该混合输入。因此优化纯输入足够。活动系统为二维，每个纯输入的 Schmidt 秩不超过二；参考全程不被操作，其 Schmidt 支撑可等距压缩进 $\mathbb C^2$，且输出迹范数不变。秩一支撑补一个零坐标即可使用同一参考空间。

将第一共同酉吸收到自由选择的输入中，第一控制可取恒等。归一化两比特纯态的单位球面与两张末次酉矩阵的 $U(2)^2$ 均紧，输出迹范数连续，故任意有限参考的上确界已在这个有限参数空间达到。

令 $\rho$ 为纯输入的系统边缘态。具有相同 $\rho$ 的纯化之间只差参考上的等距，因而给出相同输出迹范数。可以选取规范纯化

$$
|\Psi_\rho\rangle
=\sum_{a,b=0}^1(\sqrt\rho)_{ab}|a\rangle_S|b\rangle_R.
$$

对初始系统效应 $E$，对应的参考输出为

$$
\bigl(\sqrt\rho\,E\sqrt\rho\bigr)^{\mathsf T}.
$$

这是从纯化系数求部分迹所得；转置保持迹范数。因此，对任意共同末次酉 $U_i$，令 $Q_{ij}=U_i^\dagger P_jU_i$，并按陈述定义 $M_{ij}$，最终差异为

$$
\frac12\sum_{i,j}
\left\|\sqrt\rho\,M_{ij}\sqrt\rho\right\|_1.
$$

该表达式仅依赖末次酉的两个互补测量效应。原因是末端已丢弃活动系统，参考块只取决于结果效应；末次系统向量的额外相位不再进入输出。

对任意二阶 Hermitian $M$，矩阵 $A=\sqrt\rho M\sqrt\rho$ 的迹和行列式分别是 $\operatorname{tr}(\rho M)$ 和 $\det(\rho)\det(M)$。若 $\det(M)<0$ 且 $\rho$ 满秩，$A$ 两特征值异号，迹范数为特征值间距，即 $\mathfrak n_\rho(M)$ 的第一式。若此时 $\rho$ 秩亏，$A$ 至多秩一，同一公式退为 $|\operatorname{tr}A|$。若 $\det(M)\ge0$，二阶 Hermitian 矩阵 $M$ 为半正定或半负定，合同变换保持这一性质，故迹范数为绝对迹。于是全部退化情形也满足

$$
\left\|\sqrt\rho\,M\sqrt\rho\right\|_1
=\mathfrak n_\rho(M).
$$

由于 $K_i$ 和 $P_i$ 都是对角矩阵，可以同时作

$$
\rho\longmapsto D\rho D^\dagger,
\qquad Q_{ij}\longmapsto DQ_{ij}D^\dagger,
$$

其中 $D$ 为任意对角酉。这时 $M_{ij}\mapsto DM_{ij}D^\dagger$，合同矩阵的迹范数不变。选择一个 $D$，可使系统边缘态的非对角元为非负实数；原非对角元为零时无需选择相位。因此可以限制 $\rho\in\mathcal D_{\mathbb R}^+$。

固定这样的 $\rho$，再固定第一结果 $i$ 及末次第零投影的对角元 $u$。其一般复形式为

$$
Q_{i0}(\phi)=
\begin{pmatrix}
u&\sqrt{u(1-u)}e^{-i\phi}\\
\sqrt{u(1-u)}e^{i\phi}&1-u
\end{pmatrix},
\qquad Q_{i1}(\phi)=I_2-Q_{i0}(\phi).
$$

当 $u=0$ 或 $u=1$ 时已经是实矩阵。对任意 $u\in[0,1]$，每个差效应 $M_{ij}(\phi)$ 的对角元都不依赖 $\phi$，非对角元则是一个固定实系数乘以 $e^{\pm i\phi}$。因此 $\det M_{ij}(\phi)$ 不随 $\phi$ 改变，而

$$
\operatorname{tr}\bigl(\rho M_{ij}(\phi)\bigr)
=A_{ij}+B_{ij}\cos\phi
$$

具有固定实系数 $A_{ij},B_{ij}$。

若该固定行列式为负，令 $c_{ij}=-4\det(\rho)\det(M_{ij})\ge0$，相应迹范数作为 $x=\cos\phi$ 的函数为

$$
\sqrt{(A_{ij}+B_{ij}x)^2+c_{ij}}.
$$

它是二维向量 $(A_{ij}+B_{ij}x,\sqrt{c_{ij}})$ 的 Euclidean 范数，故为凸函数。若行列式非负，迹范数为 $|A_{ij}+B_{ij}x|$，也为凸函数。因此固定 $i$ 的两个结果范数之和在 $[-1,1]$ 上为凸函数，至少一个端点 $x=1$ 或 $x=-1$ 的值不小于任何给定内部点。取 $\phi=0$ 或 $\phi=\pi$ 即可将该分支替换为实投影而不降低总目标。

两个第一结果的末次控制可以独立选择，所以对 $i=0,1$ 分别替换即可。陈述中的实投影由下面的实正交矩阵实现：

$$
U_i=
\begin{pmatrix}
\sqrt{u_i}&\eta_i\sqrt{1-u_i}\\
-\eta_i\sqrt{1-u_i}&\sqrt{u_i}
\end{pmatrix},
\qquad U_i^{\mathsf T}P_jU_i=Q_{ij}.
$$

实对称正半定 $\rho$ 的正平方根也为实矩阵，故所选规范纯化具有实系数。由此，每个复策略均有值不小于它的实参数策略。反方向，所列参数都定义合法输入与共同控制。两类上确界相同，而右侧紧参数域上的目标等于连续的迹范数之和，确有最大值。这证明了所述归约与精确有限最大化式。证毕。

**定理 23.2（惰性参考与可操作记忆的严格分离）。** 沿用定义 21.1 的惰性参考任务和定义 22.1 的可操作记忆任务。对任意 $0<e,f<1$，有

$$
T_2^{\mathrm{ref}}(e,f)
<T_2^{\mathrm{mem}}(e,f)
=U(e,f)
=\frac{f+\sqrt{f^2+4(1-f)e}}2.
$$

在完整参数域 $(e,f)\in[0,1]^2$ 上，两种最优值相等的条件恰为

$$
T_2^{\mathrm{ref}}(e,f)=T_2^{\mathrm{mem}}(e,f)
\quad\Longleftrightarrow\quad
\bigl[e\in\{0,1\}\ \text{或}\ f\in\{0,1\}\bigr].
$$

这是两个访问范围各自优化后的严格分离及等号分类，不给出内域 $T_2^{\mathrm{ref}}(e,f)$ 的精确公式，也不提供显式的正差距常数。

证明。 第 23.1 条已经将惰性参考优化归约到参考量子比特上的纯联合输入及紧的有限控制参数域，并证明最优值达到。第一共同系统酉可以吸收入自由选择的联合初态。下面的严格性论证允许任意复纯输入和两个末次共同酉 $U_0,U_1\in U(2)$，不另外假设控制或输入为实。

固定 $0<e,f<1$，记

$$
a=1-f,
\qquad \alpha=\sqrt{1-e}>0,
\qquad b=\sqrt e>0.
$$

若纯联合初态的系统边缘态秩为一，则该初态为乘积态。由于过程内不操作参考，参考在每个历史上保持同一个固定张量因子；最终迹距离等于一个合法无参考协议的经典总变差。定理 22.3 在 $\beta_1=e$、$\beta_2=f$ 均严格介于零和一之间时给出 $T_2(e,f)<U(e,f)$，故秩一初态不能达到可操作记忆的最优值。

剩下处理系统边缘态满秩的纯初态。写成

$$
|\Psi\rangle_{SR}
=|0\rangle\otimes x+|1\rangle\otimes y,
\qquad \|x\|^2+\|y\|^2=1,
$$

其中参考向量 $x,y\in\mathbb C^2$ 线性无关。令 $r_0=x$、$r_1=y$，以及 $q_i=\|r_i\|^2$，则 $0<q_i<1$。

实际第一步在结果 $i$ 上的算子是 $K_{1,i}=\alpha P_i+bP_{1-i}$，理想算子是 $P_i$。令实际首支向量为

$$
\xi_i=(K_{1,i}\otimes I_R)|\Psi\rangle
=\alpha|i\rangle\otimes r_i
+b|1-i\rangle\otimes r_{1-i},
\qquad
p_i=\|\xi_i\|^2=\alpha^2q_i+b^2(1-q_i).
$$

于是 $p_0+p_1=1$。在第一历史 $i$ 上、尚未执行最后控制时，加权实际与理想的 $SR$ 差块是

$$
Z_i=a|\xi_i\rangle\langle\xi_i|
-|i\rangle\langle i|\otimes|r_i\rangle\langle r_i|.
$$

理想未归一化向量 $|i\rangle\otimes r_i$ 与 $\xi_i$ 的内积为 $\alpha q_i$，所以秩一差值公式给出

$$
L_i:=\|Z_i\|_1
=\sqrt{(ap_i+q_i)^2-4a\alpha^2q_i^2}.
$$

实二维向量 $(L_i,2\sqrt a\,\alpha q_i)$ 的欧氏范数是 $ap_i+q_i$。对这两个向量使用三角不等式，有

$$
(L_0+L_1)^2+4a\alpha^2(q_0+q_1)^2
\le\bigl[a(p_0+p_1)+q_0+q_1\bigr]^2.
$$

代入两种总权重均为一及 $\alpha^2=1-e$，得到

$$
L_0+L_1\le\sqrt{(a+1)^2-4a(1-e)}.
$$

固定第一结果 $i$，在其末次控制 $U_i$ 之后定义两个参考向量

$$
v_j=(\langle j|U_i\otimes I_R)\xi_i,
\qquad j\in\{0,1\}.
$$

因为 $x,y$ 线性无关、$\alpha,b>0$ 且 $U_i$ 可逆，$v_0,v_1$ 也线性无关。逆酉关系给出

$$
\alpha r_i=\sum_{j=0}^1\overline{(U_i)_{ji}}\,v_j.
$$

分别改变 $v_j$ 的代表相位，不改变其秩一投影。可据此把上式写成

$$
r'_i:=\alpha r_i=c_0v_0+c_1v_1,
\qquad c_j=|(U_i)_{ji}|\ge0,
\qquad c_0^2+c_1^2=1.
$$

这只是向量代表的选择，不是对参考施加操作。在这些代表中，理想最终参考块为 $(c_j^2/\alpha^2)|r'_i\rangle\langle r'_i|$，实际最终参考块为

$$
a|v_j\rangle\langle v_j|
+f|v_{1-j}\rangle\langle v_{1-j}|.
$$

记

$$
B_{ij}=a|v_j\rangle\langle v_j|
-\frac{c_j^2}{\alpha^2}|r'_i\rangle\langle r'_i|,
\qquad
F_{ij}=B_{ij}+f|v_{1-j}\rangle\langle v_{1-j}|.
$$

$F_{ij}$ 正是最终历史 $ij$ 上的实际减理想参考差块。$B_{ij}$ 则由 $Z_i$ 经过共同末次系统酉、完美指针读取以及丢弃系统得到，故迹范数收缩给出

$$
\sum_j\|B_{ij}\|_1\le L_i.
$$

对实际末次噪声项使用三角不等式，得到

$$
\|F_{ij}\|_1
\le\|B_{ij}\|_1+f\|v_{1-j}\|^2.
$$

每个 $i$ 上都有 $\|v_0\|^2+\|v_1\|^2=p_i$，而 $p_0+p_1=1$，所以对全部历史求和可得

$$
\begin{aligned}
\sum_{i,j}\|F_{ij}\|_1
&\le\sum_{i,j}\|B_{ij}\|_1+f\\
&\le L_0+L_1+f\\
&\le\sqrt{(a+1)^2-4a(1-e)}+f=2U(e,f).
\end{aligned}
$$

只需证明对满秩初态，这条链至少有一步严格。以下只考察第一历史 $i=0$ 就足够。

若该历史的末次控制满足 $c_0c_1=0$，将两个末次结果互换后可记为 $c_0=1,c_1=0$。这时 $v_0=\alpha r_i$，另一个向量 $v_1$ 与 $b r_{1-i}$ 只差一个整体相位。令 $q=q_i$，有

$$
B_{i0}=(a\alpha^2-1)|r_i\rangle\langle r_i|,
\qquad
B_{i1}=ab^2|r_{1-i}\rangle\langle r_{1-i}|.
$$

记 $A_*=a\alpha^2q$、$B_*=ab^2(1-q)$。由于 $a\alpha^2<1$，完美读取后的加权块迹范数之和为

$$
J_i:=\|B_{i0}\|_1+\|B_{i1}\|_1
=q-A_*+B_*.
$$

此时 $L_i^2=(A_*+B_*+q)^2-4A_*q$，直接相减得到

$$
L_i^2-J_i^2
=4A_*B_*
=4a^2(1-e)e\,q(1-q)>0.
$$

因此 $J_i<L_i$，这个历史上的迹范数收缩已经严格，整体最终值也严格小于 $U(e,f)$。

现在设 $c=c_0>0$、$d=c_1>0$，并简记 $r=r'_i=cv_0+dv_1$。两个比较矩阵为

$$
B_0=a|v_0\rangle\langle v_0|
-\frac{c^2}{\alpha^2}|r\rangle\langle r|,
\qquad
B_1=a|v_1\rangle\langle v_1|
-\frac{d^2}{\alpha^2}|r\rangle\langle r|.
$$

令

$$
A=\|v_0\|^2,
\qquad B=\|v_1\|^2,
\qquad C=\langle v_0,v_1\rangle.
$$

线性无关性给出 $AB-|C|^2>0$，并且

$$
\det B_0=\det B_1
=-\frac{a}{\alpha^2}c^2d^2(AB-|C|^2)<0.
$$

因此 $B_0,B_1$ 都是可逆不定 Hermitian 矩阵。

下面使用迹范数三角等号的一条直接后果。设 $D$ 是可逆不定的二阶 Hermitian 矩阵，$\kappa>0$。若

$$
\|D+\kappa|v\rangle\langle v|\|_1
=\|D\|_1+\kappa\|v\|^2,
$$

则 $v$ 必须属于 $D$ 的正谱子空间。为核对这一点，取实现左端迹范数对偶最大值的 Hermitian 收缩算子 $S$，即 $-I\le S\le I$。等号要求

$$
\operatorname{tr}(SD)=\|D\|_1,
\qquad
\langle v,Sv\rangle=\|v\|^2.
$$

在 $D$ 的特征基中，非零正、负特征值迫使 $S$ 的两个对角元分别为 $1,-1$，收缩条件再迫使非对角元为零。因此 $S=\operatorname{sign}(D)$，而第二个等号表示 $v$ 的负谱投影为零。这里没有使用迹范数的严格凸性。

假设同一第一历史中的两个三角不等式都取等。因为 $f>0$，上述后果分别要求

$$
B_0v_1=\lambda_0v_1,
\qquad
B_1v_0=\lambda_1v_0,
\qquad \lambda_0,\lambda_1>0.
$$

在独立基 $v_0,v_1$ 中展开。第一式沿 $v_1$ 的系数、第二式沿 $v_0$ 的系数分别为

$$
\lambda_0=-\frac{c^2d}{\alpha^2}(cC+dB),
\qquad
\lambda_1=-\frac{cd^2}{\alpha^2}(cA+d\overline C).
$$

这些系数为实且非负，迫使 $C$ 为实数，并且

$$
C\le-\frac dcB,
\qquad
C\le-\frac cdA.
$$

所以 $|C|^2\ge AB$，与独立向量的严格 Cauchy--Schwarz 不等式矛盾。两个末次结果的三角不等式不能同时取等，因而这个第一历史已经给出严格损失，最终值仍严格小于 $U(e,f)$。

每个纯两比特初态的系统边缘态秩只能是一或二。秩一情形由无参考严格界排除；满秩情形的末次控制则被上述 $c_0c_1=0$ 与 $c_0c_1>0$ 两类穷尽。因此每个纯初态及控制表的值都严格小于 $U(e,f)$。再使用第 23.1 条的最优值达到性，便得到优化后的 $T_2^{\mathrm{ref}}(e,f)<U(e,f)$。定理 22.2 已给出 $T_2^{\mathrm{mem}}=U$，从而得到两个访问范围在参数方形内域的严格分离。

最后核对四条边界。若 $e=0$，指针初态与恒等控制给出实际全零历史概率 $1-f$、理想全零历史概率一，所以无参考差异达到 $f=U(0,f)$。若 $f=0$，命题 18.3 的末次完美读取构造达到 $\sqrt e=U(e,0)$。若 $e=1$ 或 $f=1$，指针初态与恒等控制使两种经典历史支撑不交，达到 $1=U(e,f)$。这些方案都不需要参考或可操作记忆，结合定理 22.2 的统一上界，四条边界上的两个最优值相等。参数域被内域与四条边界穷尽，得到所述充要分类。证毕。

<a id="entry-87"></a>

## 追加锚（新终端）

<a id="section-24"></a>

## 24. 任意有限历史下惰性参考与可操作记忆的完整等号分类

**定理 24.1（两种访问权限的有限历史等号分类）。** 沿用定义 21.1 的惰性参考任务与定义 22.1 的可操作记忆任务。前者允许初始 $SR$ 纠缠，过程内仅使用依赖已存经典历史的共同系统控制 $U\in U(2)$，不操作参考、不与参考耦合，最终丢弃活动系统并输出 $H_NR$；后者允许任意有限维记忆和共同 $SM$ CPTP 控制，最终丢弃活动系统并输出 $H_NM$。对任意有限 $N\ge1$ 和参数 $\beta_t\in[0,1]$，令

$$
f=\beta_N,
\qquad a=1-f,
\qquad s=\prod_{t=1}^{N-1}\sqrt{1-\beta_t},
\qquad E=1-s^2,
$$

其中空积为一，并令

$$
U(E,f)=\frac{f+\sqrt{(a+1)^2-4as^2}}2.
$$

总有

$$
T_N^{\mathrm{ref}}(\boldsymbol\beta)
\le T_N^{\mathrm{mem}}(\boldsymbol\beta)=U(E,f).
$$

当 $N=1$ 时，两者都等于 $f$。当 $N\ge2$ 时，完整等号分类为

$$
\begin{aligned}
&T_N^{\mathrm{ref}}(\boldsymbol\beta)
=T_N^{\mathrm{mem}}(\boldsymbol\beta)=U(E,f)\\
&\quad\Longleftrightarrow\quad
\left[
\beta_{N-1}=0\ \text{或}\ \beta_N=0
\ \text{或存在 }t\in\{1,\ldots,N\}\text{ 使 }\beta_t=1
\right].
\end{aligned}
$$

因此，所有参数均小于一、且最后两项均为正时，惰性参考的最优值严格低于可操作记忆的最优值；更早位置的零参数不改变这个严格性结论。本定理比较上述两个指定控制类，不给出严格区域内惰性参考最优值的显式公式或统一正差距常数。

证明。定理 22.2 给出记忆任务的精确值及包含惰性参考的共同 CPTP 控制上界。无参考系统幺正任务包含于惰性参考任务，惰性参考任务又可作为不操作记忆的特殊协议，故

$$
T_N\le T_N^{\mathrm{ref}}\le T_N^{\mathrm{mem}}=U(E,f).
$$

$N=1$ 时，指针初态达到 $f=U(0,f)$。当 $N\ge2$ 且所列三个条件之一成立时，定理 22.3 的无参考构造已经达到 $U(E,f)$，从而以上夹逼给出充分性。

为证明必要性，以下固定 $N\ge2$，并假设

$$
0\le\beta_t<1\quad(1\le t\le N),
\qquad \beta_{N-1}>0,
\qquad \beta_N>0.
$$

于是 $a,f,s$ 均为正。先将任意有限参考的上确界化为达到的有限维最大值。对固定控制表，输出迹距离关于共同输入密度矩阵凸，故任意混合输入的某个纯态分量不比它差。活动系统为二维，纯输入的 Schmidt 秩至多为二；参考全程不被操作，其 Schmidt 支撑可等距识别为参考量子比特的子空间，输出迹范数不变。秩一时补一个零坐标即可。因此纯两比特联合输入已经包含原上确界。

对固定有限 $N$，全部共同系统控制表属于有限个 $U(2)$ 的直积，一个矩阵对应历史树中的一个控制节点。这个空间与归一化两比特纯态的单位球面均紧，最终输出迹范数连续，故 $T_N^{\mathrm{ref}}$ 的最大值达到。

如果纯输入的系统边缘态秩为一，初态便是乘积态。参考在全部历史上始终是同一个固定因子，最终差异等于相应无参考协议的经典历史差异。定理 22.3 在当前参数条件下给出 $T_N<U(E,f)$。所以只需排除系统边缘态满秩的纯输入及控制表达到上界的可能性。

先处理所有参数均非零的情形，此时全部 $\beta_t\in(0,1)$。固定系统边缘态满秩的纯初态和共同系统控制表。对每个长度 $N-1$ 的旧历史 $h$，记实际与理想的未归一化 $SR$ 分支向量为 $\xi_h,\eta_h$，并令

$$
p_h=\|\xi_h\|^2,
\qquad q_h=\|\eta_h\|^2,
\qquad \gamma_h=\langle\eta_h,\xi_h\rangle.
$$

因为 $0<\beta_t<1$，实际每个 $K_{t,z}$ 都可逆，共同系统酉也可逆。局部可逆算子的有限乘积保持 Schmidt 秩，故每个实际前缀分支 $\xi_h$ 都具有 Schmidt 秩二，特别地 $p_h>0$。理想前缀至少经历了一次秩一系统投影，因此

$$
\eta_h=|i_h\rangle\otimes r_h,
\qquad i_h=h_{N-1},
$$

其中参考向量 $r_h$ 可以为零。

对每步的同一历史控制，实际与理想仪器满足

$$
\sum_zP_zK_{t,z}=\sqrt{1-\beta_t}\,I_S.
$$

共同系统酉保持分支内积，因而从相同初态的内积一开始，逐步对全部历史求和得到

$$
\sum_h\gamma_h=s>0.
$$

同时仪器完备性给出 $\sum_hp_h=\sum_hq_h=1$。内积求和式没有要求每个 $\gamma_h$ 单独为实或非负，但它保证存在一个历史 $h_*$ 满足 $\gamma_{h_*}\ne0$；于是该历史的理想向量也非零。

令末次仪器前的加权差块为

$$
Z_h=a|\xi_h\rangle\langle\xi_h|
-|\eta_h\rangle\langle\eta_h|.
$$

秩一差值公式给出

$$
L_h:=\|Z_h\|_1
=\sqrt{(ap_h+q_h)^2-4a|\gamma_h|^2}.
$$

二维实向量 $(L_h,2\sqrt a\,|\gamma_h|)$ 的范数是 $ap_h+q_h$。对全部历史使用欧氏三角不等式，再用复数三角不等式，得到

$$
\begin{aligned}
\left(\sum_hL_h\right)^2
&\le(a+1)^2-4a\left(\sum_h|\gamma_h|\right)^2\\
&\le(a+1)^2-4as^2.
\end{aligned}
$$

固定历史 $h$，令其末次共同控制为 $W_h$，并定义

$$
v_{h,j}=(\langle j|W_h\otimes I_R)\xi_h,
\qquad
c_{h,j}=|\langle j|W_h|i_h\rangle|,
\qquad j\in\{0,1\}.
$$

有 $c_{h,0}^2+c_{h,1}^2=1$，而两个参考向量 $v_{h,0},v_{h,1}$ 线性无关。这是因为 $\xi_h$ 的 Schmidt 秩为二，末次系统酉保持该秩。两向量范数平方之和为 $p_h$。

实际和理想最终参考块之差为

$$
F_{h,j}=a|v_{h,j}\rangle\langle v_{h,j}|
+f|v_{h,1-j}\rangle\langle v_{h,1-j}|
-c_{h,j}^2|r_h\rangle\langle r_h|.
$$

记其中不含末次翻转项的比较块为

$$
B_{h,j}=a|v_{h,j}\rangle\langle v_{h,j}|
-c_{h,j}^2|r_h\rangle\langle r_h|.
$$

这两个 $B_{h,j}$ 正是 $Z_h$ 经共同末次系统酉、假想完美指针读取和丢弃系统后的输出块，故

$$
\sum_j\|B_{h,j}\|_1\le L_h.
$$

再对末次翻转项使用迹范数三角不等式，得到

$$
\begin{aligned}
\sum_{h,j}\|F_{h,j}\|_1
&\le\sum_{h,j}\|B_{h,j}\|_1
+f\sum_hp_h\\
&\le\sum_hL_h+f\\
&\le\sqrt{(a+1)^2-4as^2}+f=2U(E,f).
\end{aligned}
$$

下面只考察已经选出的 $h_*$，并省略该历史下标。记 $r=r_{h_*}\ne0$、$v_j=v_{h_*,j}$、$c_j=c_{h_*,j}$。只要在这个历史上证明收缩或三角不等式中的一步严格，整体最终值就严格低于 $U(E,f)$。

先设 $c_0c_1=0$。互换末次结果后可取 $c_0=1,c_1=0$；理想控制后向量是 $|0\rangle\otimes r$，差一个无关整体相位。令

$$
p_0=\|v_0\|^2,
\qquad p_1=\|v_1\|^2,
\qquad q=\|r\|^2,
\qquad k=|\langle r,v_0\rangle|^2.
$$

线性无关性给出 $p_1>0$；共同酉保持完整分支内积，因此 $k=|\gamma_{h_*}|^2>0$。于是

$$
L_{h_*}^2=\bigl[a(p_0+p_1)+q\bigr]^2-4ak,
$$

而假想完美读取后的加权迹范数之和为

$$
J:=\|B_{h_*,0}\|_1+\|B_{h_*,1}\|_1
=\sqrt{(ap_0+q)^2-4ak}+ap_1.
$$

直接相减得到

$$
L_{h_*}^2-J^2
=2ap_1\left[ap_0+q
-\sqrt{(ap_0+q)^2-4ak}\right]>0.
$$

根式为实数，因为 $k\le p_0q$；方括号严格为正，因为 $a,k>0$。因此 $J<L_{h_*}$，该历史的迹范数收缩严格。

现设 $c_0,c_1>0$。由于 $v_0,v_1$ 是参考空间的一组基，存在复系数 $\ell,m$ 使

$$
r=\ell v_0+mv_1.
$$

这里的展开系数不要求与系统控制幅度 $c_0,c_1$ 相同。两类系数将分开保留。当 $\ell,m$ 同时非零时，先独立选择 $v_0,v_1$ 的代表相位，使这两个展开系数均为正实数；这不改变参考投影或目标值。若有一个系数为零，则不必改动相位。在相应代表下统一记

$$
A=\|v_0\|^2,
\qquad B=\|v_1\|^2,
\qquad C=\langle v_0,v_1\rangle,
\qquad AB-|C|^2>0.
$$

使用第 23.2 条证明中的迹范数等号后果：若二阶 Hermitian 矩阵 $D$ 可逆且不定、$\kappa>0$，则

$$
\|D+\kappa|v\rangle\langle v|\|_1
=\|D\|_1+\kappa\|v\|^2
$$

要求 $v$ 属于 $D$ 的正谱子空间。其理由是取实现左端的 Hermitian 对偶收缩算子；等号迫使它同时实现 $D$ 的迹范数和正项的迹，而 $D$ 可逆不定时前一个条件唯一决定该算子为 $\operatorname{sign}(D)$。

如果 $\ell,m$ 都非零，按照已选代表有 $\ell,m>0$。两个比较块

$$
B_0=a|v_0\rangle\langle v_0|-c_0^2|r\rangle\langle r|,
\qquad
B_1=a|v_1\rangle\langle v_1|-c_1^2|r\rangle\langle r|
$$

满足

$$
\det B_0=-ac_0^2m^2(AB-|C|^2)<0,
\qquad
\det B_1=-ac_1^2\ell^2(AB-|C|^2)<0.
$$

若两个末次结果的三角不等式同时取等，$f>0$ 和上述等号后果要求

$$
B_0v_1=\lambda_0v_1,
\qquad B_1v_0=\lambda_1v_0,
\qquad \lambda_0,\lambda_1>0.
$$

在独立基 $v_0,v_1$ 中比较系数，得到

$$
\lambda_0=-c_0^2m(\ell C+mB),
\qquad
\lambda_1=-c_1^2\ell(\ell A+m\overline C).
$$

这些特征值为实且非负，迫使 $C$ 为实数，并满足

$$
C\le-\frac m\ell B,
\qquad
C\le-\frac\ell m A.
$$

所以 $|C|^2\ge AB$，与向量独立性矛盾。因此两个三角不等式不能同时取等。

还需处理展开系数为零的情况。若 $\ell=0$，则 $m\ne0$，$r=mv_1$，并且

$$
B_0=a|v_0\rangle\langle v_0|
-c_0^2|m|^2|v_1\rangle\langle v_1|
$$

是可逆不定矩阵。若其三角不等式取等，$v_1$ 必为 $B_0$ 的正特征向量。然而

$$
B_0v_1=aCv_0-c_0^2|m|^2\|v_1\|^2v_1.
$$

独立性与 $a>0$ 先迫使 $C=0$，随后对应特征值等于 $-c_0^2|m|^2\|v_1\|^2<0$，矛盾。若 $m=0$，对 $B_1$ 和 $v_0$ 使用同一计算，也得到严格三角不等式。因为 $r\ne0$，两个系数不会同时为零。这穷尽了 $c_0,c_1>0$ 的全部情况。

因此，所有参数均非零时，每个满秩纯输入和控制表都有某一步严格不等式，不能达到 $U(E,f)$。

还需处理存在更早零参数的情形。选取一个 $k\le N-2$ 使 $\beta_k=0$。这一步实际和理想结果算子均为秩一投影 $P_z$，所以每个非零历史分支在这一步之后都成为 $S$ 与 $R$ 的乘积向量。后续所有算子仅作用于系统，乘积结构一直保持；实际与理想分支的参考因子可以不同。特别地，倒数第二步之前的每个父历史已经具有这种乘积结构。

反设某个纯输入及控制表达到 $U(E,f)$。对每个长度 $N-1$ 的历史 $h$，把末次共同控制之前的实际、理想分支写成

$$
\xi_h=x_h\otimes r_h^{\mathrm A},
\qquad
\eta_h=y_h\otimes r_h^{\mathrm J},
$$

允许因子未归一化或为零。令末次共同系统控制为 $W_h$。在两候选上都假想使用完美末次指针读取，所得未归一化纯参考向量是

$$
u_{h,j}=\langle j|W_hx_h\rangle\,r_h^{\mathrm A},
\qquad
v_{h,j}=\langle j|W_hy_h\rangle\,r_h^{\mathrm J}.
$$

这里的 $u_{h,j}$ 是假想完美读取的实际候选参考向量，不是带有末次错误的最终参考态。用 $i=(h,j)$ 简记最终经典坐标，并设

$$
P_i=\|u_i\|^2,
\qquad Q_i=\|v_i\|^2,
\qquad \delta_i=\langle v_i,u_i\rangle.
$$

共同末次控制及假想完美读取保持内积总和。由前缀交叉算子恒等式与仪器完备性，仍有

$$
\sum_i P_i=\sum_i Q_i=1,
\qquad \sum_i\delta_i=s>0.
$$

定义

$$
D_i=a|u_i\rangle\langle u_i|-|v_i\rangle\langle v_i|,
\qquad
L_i=\|D_i\|_1
=\sqrt{(aP_i+Q_i)^2-4a|\delta_i|^2},
\qquad
C=\sum_i|\delta_i|\ge s.
$$

真正的最终实际、理想差块则是

$$
D_{h,j}+f|u_{h,1-j}\rangle\langle u_{h,1-j}|.
$$

对本协议最终半迹距离 $T$，迹范数三角不等式和欧氏三角不等式给出

$$
\begin{aligned}
2T
&\le\sum_iL_i+f\\
&\le\sqrt{(a+1)^2-4aC^2}+f\\
&\le\sqrt{(a+1)^2-4as^2}+f=2U(E,f).
\end{aligned}
$$

在假设的达到情形下，每一步都必须取等。因为 $a>0$、$s>0$，根式关于 $C$ 严格递减，故 $C=s$。同时，向量 $(L_i,2\sqrt a\,|\delta_i|)$ 的范数为 $aP_i+Q_i$，欧氏三角不等式取等迫使所有非零向量同向。因此对每个活坐标，即 $P_i+Q_i>0$ 的坐标，精确有

$$
|\delta_i|=\frac{s(aP_i+Q_i)}{a+1}>0.
$$

于是 $P_i>0$ 当且仅当 $Q_i>0$，而且每个活坐标的两个参考向量都非零、内积非零。这里相同的是最终经典坐标上的非零质量支撑，不要求参考向量平行，也不要求它们的秩一密度算子具有相同支撑。

另一方面，

$$
\sum_i\operatorname{tr}D_i=a-1=-f<0.
$$

所以存在一个坐标 $(h,j)$ 满足 $\operatorname{tr}D_{h,j}<0$。它是活坐标，故其 $u=u_{h,j}$、$v=v_{h,j}$ 都非零且 $\langle v,u\rangle\ne0$。乘积结构保证 $u_{h,1-j}$ 与 $u$ 平行。下面证明它必须为零。

如果 $u,v$ 线性无关，$D=a|u\rangle\langle u|-|v\rangle\langle v|$ 在二维参考空间上可逆不定。若 $u_{h,1-j}\ne0$，末次迹范数三角不等式取等要求该噪声向量属于 $D$ 的正谱子空间，因而要求 $u$ 是 $D$ 的特征向量。但

$$
Du=a\|u\|^2u-\langle v,u\rangle v
$$

并不与 $u$ 平行，因为内积非零且两向量独立，矛盾。如果 $u,v$ 平行，负迹条件使 $D$ 成为非零负半定秩一算子。任何沿同一方向的非零正算子与它相加，标量三角不等式都严格，同样矛盾。因此 $u_{h,1-j}=0$。经典坐标非零质量支撑相同又给出 $v_{h,1-j}=0$。

选中坐标的 $u_{h,j},v_{h,j}$ 均非零，所以经过 $W_h$ 后，实际和理想的系统因子都指向同一个指针 $|j\rangle$。共同系统酉可逆，故控制之前的两个系统因子平行。这一步没有断言完整 $SR$ 分支向量平行。

将该历史写为 $h=g\ell$，其中 $\ell$ 是倒数第二次结果。因为完美读取已经在深度 $k\le N-2$ 发生，父历史 $g$ 的两候选均为乘积态。把倒数第二次共同控制后的系统因子分别记作 $x,y$，并保留各自非零的参考因子。令

$$
\alpha=\sqrt{1-\beta_{N-1}}>0,
\qquad b=\sqrt{\beta_{N-1}}>0.
$$

选中理想子分支非零，其系统因子为 $P_\ell y$，指向 $|\ell\rangle$；选中实际子分支系统因子与它平行。因此

$$
(\alpha P_\ell+bP_{1-\ell})x
\ \parallel\ |\ell\rangle,
$$

且左端非零。由于 $\alpha,b>0$，比较两个指针分量得到 $x$ 非零且指向 $|\ell\rangle$。

考察兄弟历史 $h'=g(1-\ell)$。其实际系统因子为

$$
(\alpha P_{1-\ell}+bP_\ell)x=bx\ne0,
$$

仍指向 $|\ell\rangle$。若兄弟理想子分支为零，则其两个最终假想完美读取坐标均有 $Q_i=0$，而实际分支非零保证至少一个坐标有 $P_i>0$，违反非零质量支撑相同。故兄弟理想分支也非零，系统因子 $P_{1-\ell}y$ 指向另一个指针。两候选在这个兄弟历史上的完整分支内积因系统正交而为零。因此，无论其末次共同控制如何，

$$
\sum_j\delta_{h',j}=0.
$$

兄弟历史的实际分支非零，至少一个最终坐标是活坐标；该坐标的 $\delta$ 非零。于是

$$
\sum_j|\delta_{h',j}|>0
=\left|\sum_j\delta_{h',j}\right|.
$$

对其他历史使用复数三角不等式，便得到

$$
\begin{aligned}
C=\sum_{h,j}|\delta_{h,j}|
&>\sum_h\left|\sum_j\delta_{h,j}\right|\\
&\ge\left|\sum_{h,j}\delta_{h,j}\right|=s,
\end{aligned}
$$

与达到所必需的 $C=s$ 矛盾。这排除了更早存在完美读取时达到上界的可能性。

当前参数条件下，秩一输入、所有参数非零时的满秩输入、以及更早存在零参数时的满秩输入已被穷尽。所有纯输入及共同系统幺正控制表都不能达到 $U(E,f)$，而紧性保证惰性参考任务的最大值确实达到，因此

$$
T_N^{\mathrm{ref}}(\boldsymbol\beta)<U(E,f)
=T_N^{\mathrm{mem}}(\boldsymbol\beta).
$$

这给出所列等号条件的必要性，并与充分性合成完整分类。证毕。

<a id="entry-89"></a>

## 追加锚（新终端）

<a id="section-25"></a>

## 25. 两步惰性参考任务中系统 CPTP 控制的完整归约

**定义 25.1（无可操作记忆的两步系统 CPTP 控制）。** 在定义 21.1 的两步任务中，令 $e=\beta_1\in[0,1]$、$f=\beta_2\in[0,1]$。保持任意有限维惰性参考 $R$、两候选共同联合输入和最终输出 $H_2R$ 的约定，只把系统控制从共同历史依赖 $U(2)$ 扩大为共同历史依赖的系统 CPTP 映射。第一控制无历史可用，第二控制只依赖已存第一结果；实际与理想过程使用同一张控制表。控制只作用于活动系统 $S=\mathbb C^2$，可以丢弃余系统，但这些余系统不再被访问或重新耦合。没有另一个可操作量子记忆，不操作参考、不与参考耦合，不后选择，末次仪器之后丢弃活动系统。对所有允许的共同输入、共同控制表和有限参考取最优半迹距离，记为 $T_2^{\mathrm{ref,CPTP}}(e,f)$；定义 21.1 的原系统幺正任务仍记作 $T_2^{\mathrm{ref}}(e,f)$。

**定理 25.2（两步 CPTP 归约、高末次错误率精确值及最小记忆维数）。** 对定义 25.1 的完整参数域，有

$$
T_2^{\mathrm{ref,CPTP}}(e,f)
=T_2^{\mathrm{ref}}(e,f).
$$

当 $0\le f\le\tfrac12$ 时，对任意固定共同输入和共同 CPTP 控制表，吸收第一控制后的共同输入作为新初态，再逐个第一历史选择依赖该输入的共同系统幺正替换，即可使最终半迹距离不减。当 $\tfrac12\le f\le1$ 时，两类任务都有精确值

$$
T_2^{\mathrm{ref,CPTP}}(e,f)
=T_2^{\mathrm{ref}}(e,f)
=e+f-ef.
$$

后一数值无需参考，指针初态和两步恒等控制即可达到。

进一步，在定义 22.1 的两步可操作记忆任务中，仍允许任意共同 $SM$ CPTP 控制，并允许额外任意有限维惰性参考 $R$，最终保留 $H_2MR$。以达到定理 22.2 的最优值 $U(e,f)$ 为目标，所需非零可操作记忆 $M$ 的最小维数恰为

$$
d_{\min}(e,f)=
\begin{cases}
2,&0<e<1\ \text{且}\ 0<f<1,\\
1,&e\in\{0,1\}\ \text{或}\ f\in\{0,1\}.
\end{cases}
$$

结论限定于两步及上述访问权限、控制类和保留输出，不把一般多步任务的控制类或最小记忆维数等同，也不求 $f<\tfrac12$ 时原惰性参考最优值的闭式。

证明。记 $a=1-f$、$\alpha=\sqrt{1-e}$、$b=\sqrt e$，并令

$$
P_i=|i\rangle\langle i|,
\qquad K_i=\alpha P_i+bP_{1-i},
\qquad i\in\{0,1\}.
$$

第一共同系统 CPTP 控制对任意共同联合输入 $\omega_{SR}$ 的输出仍是一个允许的共同联合态。由于初态自由选择，把这个输出直接作为新初态，并把第一控制改为恒等，不改变后续两个候选输出。因此只需考虑第一控制恒等的协议，且不必限制输入为纯态或参考维数。

固定第一历史 $i$，记其末次共同系统 CPTP 控制为 $\Lambda_i$。因为末次仪器之后丢弃活动系统，这个控制对最终参考块的作用只通过效应算子

$$
E_i=\Lambda_i^*(P_0),
\qquad 0\le E_i\le I,
\qquad \Lambda_i^*(P_1)=I-E_i
$$

体现。这里星号表示 Heisenberg 对偶。实际末次结果 $0$ 的效应为 $fI+(a-f)E_i$，结果 $1$ 的效应为 $aI+(f-a)E_i$；理想末次的两个效应为 $E_i,I-E_i$。这来自

$$
K_{2,0}^\dagger K_{2,0}=aP_0+fP_1,
\qquad
K_{2,1}^\dagger K_{2,1}=aP_1+fP_0
$$

及 $\Lambda_i^*(I)=I$。

对固定共同输入和第一历史，两个最终参考差块关于 $E_i$ 都是仿射函数，故它们迹范数之和 $G_i(E_i)$ 是凸函数。任意二阶效应算子都可以写成

$$
E_i=\lambda_{\min}I
+(\lambda_{\max}-\lambda_{\min})Q
+(1-\lambda_{\max})0,
\qquad
0\le\lambda_{\min}\le\lambda_{\max}\le1,
$$

其中 $Q$ 是秩一正交投影；重特征值时任选 $Q$。这是 $I,Q,0$ 的凸组合。因此存在一个 $E_i'\in\{I,Q,0\}$，使 $G_i(E_i')\ge G_i(E_i)$。秩一投影 $Q$ 可写成 $V_i^\dagger P_0V_i$，由一个共同系统幺正 $V_i$ 实现；效应 $I$ 与 $0$ 分别由把系统重置为 $|0\rangle$ 与 $|1\rangle$ 的 CPTP 映射实现。

先设 $f\le\tfrac12$，于是 $a\ge f$。下面证明两个常值效应都可由系统幺正控制支配。对当前第一历史 $i$，定义输入的两个对角参考块

$$
X=\langle i|\omega_{SR}|i\rangle,
\qquad Y=\langle1-i|\omega_{SR}|1-i\rangle.
$$

它们可以为零，且都半正定。第一步后，实际候选的参考边缘块为 $(1-e)X+eY$，理想候选的参考块为 $X$。定义 Hermitian 算子

$$
D=[a(1-e)-1]X.
$$

若末次效应 $E_i=I$，两个最终参考差块分别为

$$
D+aeY,
\qquad f(1-e)X+feY.
$$

第二块半正定，故对应迹范数之和为

$$
G_i(I)=\|D+aeY\|_1
+f(1-e)\operatorname{tr}X+fe\operatorname{tr}Y.
$$

改用指针投影效应 $E_i=P_i$，两个最终参考差块则为

$$
D+feY,
\qquad f(1-e)X+aeY,
$$

从而

$$
G_i(P_i)=\|D+feY\|_1
+f(1-e)\operatorname{tr}X+ae\operatorname{tr}Y.
$$

因为 $(a-f)eY$ 半正定，迹范数三角不等式给出

$$
\|D+aeY\|_1
\le\|D+feY\|_1+(a-f)e\operatorname{tr}Y.
$$

代入即得 $G_i(I)\le G_i(P_i)$。常值效应 $E_i=0$ 只把 $E_i=I$ 的两个末次结果交换，因此 $G_i(0)=G_i(I)$，同样被一个指针投影效应支配。

由此，任意效应先取不劣的 $I,Q,0$ 之一，再把常值效应替换为不劣的指针投影，最终总能取到一个不劣的秩一投影。两个第一历史的控制可独立选取，最终经典历史块的迹范数相加，所以逐历史替换使完整输出半迹距离不减。所有替换都作用于系统，保持同一个共同输入和惰性参考。结合第一控制的吸收，任意系统 CPTP 协议均被一个合法系统幺正协议支配，故

$$
T_2^{\mathrm{ref,CPTP}}(e,f)
\le T_2^{\mathrm{ref}}(e,f)
\qquad(0\le f\le\tfrac12).
$$

反向不等式来自控制类包含，低参数区间的等式成立。

现设 $f\ge\tfrac12$，于是 $a\le f$。仍把第一控制吸收到输入中，并记当前第一历史上两个末次理想效应为

$$
E_{i,0}=E_i,
\qquad E_{i,1}=I-E_i.
$$

整个两步过程对初始系统的实际、理想历史效应分别为

$$
A_{ij}=K_i\bigl[fI+(a-f)E_{i,j}\bigr]K_i,
\qquad
J_{ij}=P_iE_{i,j}P_i.
$$

因为 $0\le E_{i,j}\le I$，有

$$
fI+(a-f)E_{i,j}\ge aI,
\qquad 0\le J_{ij}\le P_i.
$$

设 $c=a(1-e)$。逐个历史的算子序给出

$$
A_{ij}\ge aK_i^2
=a(1-e)P_i+aeP_{1-i}
\ge cP_i\ge cJ_{ij}.
$$

实际、理想历史效应各自构成 POVM，故

$$
A_{ij}-cJ_{ij}\ge0,
\qquad
\sum_{i,j}(A_{ij}-cJ_{ij})=(1-c)I.
$$

这里 $c\le\tfrac12$，所以 $1-c>0$。因此

$$
C_{ij}=\frac{A_{ij}-cJ_{ij}}{1-c}
$$

也是一组 POVM。记三个相应的量子到经典通道为 $\mathcal A,\mathcal J,\mathcal C$，逐效应恒等式给出真正的通道凸分解

$$
\mathcal A=c\mathcal J+(1-c)\mathcal C.
$$

对任意有限惰性参考和任意共同联合输入，$\mathcal C\otimes\operatorname{id}_R$ 与 $\mathcal J\otimes\operatorname{id}_R$ 的输出都是密度矩阵，两者迹距离至多为一。因此

$$
\frac12\left\|
\bigl[(\mathcal A-\mathcal J)\otimes\operatorname{id}_R\bigr](\omega_{SR})
\right\|_1
\le1-c=e+f-ef.
$$

这个界对任意末次系统 CPTP 控制和共同输入成立。

取无参考初态 $|0\rangle$，第一控制和两个末次历史控制均为恒等。实际与理想候选的系统在每个非零历史上都保持指针 $|0\rangle$。理想历史必为 $00$；实际历史为 $00$ 的概率是 $(1-e)(1-f)=c$。因此最终经典历史的总变差恰为 $1-c=e+f-ef$，已经由原系统幺正任务达到。结合上界与控制类包含，高参数区间的精确值以及两类任务的等式均成立。两段在 $f=\tfrac12$ 相容，并穷尽完整参数域。

最后证明所述最小记忆维数。$\dim M=1$ 时，$SM$ 上的任意共同 CPTP 控制正是系统共同 CPTP 控制，任意额外惰性参考也正是定义 25.1 允许的输入及最终参考。因此该维数下的最优值等于本定理已经确定的 $T_2^{\mathrm{ref}}(e,f)$。当 $e,f\in(0,1)$ 时，定理 23.2（亦为定理 24.1 的两步情形）给出

$$
T_2^{\mathrm{ref}}(e,f)<U(e,f),
$$

故一维可操作记忆不足以达到目标，即使允许任意额外惰性参考也不例外。定理 22.2 的一个记忆量子比特及末次一次 SWAP 已经达到 $U(e,f)$，所以二维足够，内域的最小维数为二。

若 $e\in\{0,1\}$ 或 $f\in\{0,1\}$，定理 22.3 的两步边界构造在无参考、无可操作记忆的系统幺正任务中已达到 $U(e,f)$。它可在 $\dim M=1$ 的任务中原样实现，而记忆维数按定义必须为正，所以四边的最小维数为一。这完成全部结论。证毕。

<a id="entry-91"></a>

## 追加锚（新终端）

<a id="section-26"></a>

## 26. 高末次错误率公式向三步推广的精确反例

**定理 26.1（三步共同幺正反馈超过简单成功概率界）。** 在定义 18.1 的无参考、无可操作记忆任务中，取

$$
N=3,
\qquad \beta_1=\beta_2=\frac1{10},
\qquad \beta_3=\frac12.
$$

存在共同初态 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ 和共同历史依赖实正交系统控制表，使最终三位经典历史的实际、理想总变差恰为

$$
T(\Pi)=\frac14+\frac{\sqrt{13}}{10}.
$$

因此，该参数下原无参考最优值满足

$$
T_3\!\left(\frac1{10},\frac1{10},\frac12\right)
\ge\frac14+\frac{\sqrt{13}}{10}
>\frac{119}{200}
=1-\prod_{t=1}^3(1-\beta_t).
$$

这个反例否定把定理 25.2 的两步高末次错误率公式推广为任意有限步数的等式或上界 $1-\prod_t(1-\beta_t)$，即使仍有 $\beta_N\ge\tfrac12$。本例在共同系统幺正类内实现，不证明 CPTP 控制比幺正控制更优，也不主张达到可操作记忆上界；所有参数都在定理 24.1 的严格区域中。

证明。第一共同控制取恒等。令

$$
P_i=|i\rangle\langle i|,
\qquad
K_i=\frac3{\sqrt{10}}P_i+\frac1{\sqrt{10}}P_{1-i},
\qquad i\in\{0,1\},
$$

它们分别是前两步共同使用的理想、实际结果算子。第一结果为 $i$ 时，记实际、理想未归一化系统向量为

$$
x_i=K_i|+\rangle,
\qquad y_i=P_i|+\rangle.
$$

定义实对称矩阵

$$
D_i=\frac1{20}\|x_i\|^2I
+\frac25|x_i\rangle\langle x_i|
-|y_i\rangle\langle y_i|.
$$

第二共同控制 $U_i\in O(2)$ 取为 $D_i$ 的一个正交本征基，即令 $U_iD_iU_i^{\mathsf T}$ 为对角矩阵。本征值的排列任意，控制表在实验之前由上述固定矩阵确定，实际与理想过程始终使用同一个 $U_i$。

设前两位历史是 $ij$，其实际、理想概率分别为

$$
p_{ij}=\|K_jU_ix_i\|^2,
\qquad q_{ij}=\|P_jU_iy_i\|^2.
$$

因为

$$
K_j^\dagger K_j=\frac1{10}I+\frac45P_j,
$$

有

$$
\begin{aligned}
\frac12p_{ij}-q_{ij}
&=\frac1{20}\|x_i\|^2
+\frac25|\langle j|U_ix_i\rangle|^2
-|\langle j|U_iy_i\rangle|^2\\
&=\langle j|U_iD_iU_i^{\mathsf T}|j\rangle.
\end{aligned}
$$

按本征基选择控制，便得到

$$
\sum_j\left|\frac12p_{ij}-q_{ij}\right|=\|D_i\|_1.
$$

第三共同控制取 $W_{ij}=X^j$，其中 $X|0\rangle=|1\rangle$、$X|1\rangle=|0\rangle$。每个非零理想前缀分支在第二次读取后都指向 $|j\rangle$，因此这个控制使理想末次结果恒为零。实际末次参数为 $\beta_3=\tfrac12$，两个结果算子都为 $I/\sqrt2$，无论分支系统态如何，两个末次结果的条件概率均为一半。故三位最终历史 $ijk$ 的概率满足

$$
p_{ij0}=p_{ij1}=\frac12p_{ij},
\qquad q_{ij0}=q_{ij},
\qquad q_{ij1}=0.
$$

使用 $\sum_{i,j}p_{ij}=1$，该协议的最终总变差为

$$
\begin{aligned}
T(\Pi)
&=\frac12\sum_{i,j}
\left(\left|\frac12p_{ij}-q_{ij}\right|
+\frac12p_{ij}\right)\\
&=\frac14+\frac12\sum_i\|D_i\|_1.
\end{aligned}
$$

这里的末次读数归约只用实际末次均匀读取以及共同控制使理想末次结果确定；它把本例的输出距离转化为两个具体加权差矩阵的迹范数。

直接代入初态得到

$$
x_0=\frac1{\sqrt{20}}\begin{pmatrix}3\\1\end{pmatrix},
\qquad y_0=\frac1{\sqrt2}\begin{pmatrix}1\\0\end{pmatrix},
\qquad x_1=Xx_0,
\qquad y_1=Xy_0.
$$

所以

$$
D_0=\frac1{200}
\begin{pmatrix}-59&12\\12&9\end{pmatrix},
\qquad D_1=XD_0X.
$$

两个矩阵的本征值都是

$$
\lambda_\pm=-\frac18\pm\frac{\sqrt{13}}{20}.
$$

一正一负，因而

$$
\|D_0\|_1=\|D_1\|_1=\frac{\sqrt{13}}{10},
\qquad
T(\Pi)=\frac14+\frac{\sqrt{13}}{10}.
$$

另一方面，简单成功概率表达式是

$$
1-\prod_{t=1}^3(1-\beta_t)
=1-\frac9{10}\frac9{10}\frac12
=\frac{119}{200}.
$$

两者之差为

$$
\frac14+\frac{\sqrt{13}}{10}-\frac{119}{200}
=\frac{20\sqrt{13}-69}{200}>0,
$$

因为 $20^2\cdot13=5200>4761=69^2$。这给出精确的严格反例。

定理 22.2 在本参数下的记忆最优值为

$$
U\!\left(\frac{19}{100},\frac12\right)
=\frac14+\frac{3\sqrt7}{20},
$$

而本构造严格低于它，因为 $2\sqrt{13}<3\sqrt7$ 等价于 $52<63$。本例超过的是被推广的简单成功概率表达式，与定理 24.1 的访问权限严格分离相容。证毕。

<a id="entry-93"></a>

## 追加锚（新终端）

<a id="section-27"></a>

## 27. 任意有限历史的末次 CPTP 控制分类与加权前缀目标

**定义 27.1（任意有限历史的系统 CPTP 控制与惰性参考）。** 对任意有限 $N\ge1$ 和参数 $\boldsymbol\beta\in[0,1]^N$，沿用定义 25.1 的系统 CPTP 控制访问权限，推广为 $N$ 次读取。活动系统为 $S=\mathbb C^2$，允许任意有限维惰性参考 $R$ 和两候选共同使用的归一化联合输入。每次仪器之前，只根据已经存储的经典历史，在 $S$ 上施加共同 CPTP 控制；实际与理想过程使用同一张控制表。控制余系统一旦丢弃，就不再被访问或重新耦合；没有可操作量子记忆，不操作参考、不与参考耦合，不后选择。第 $t$ 次实际、理想结果算子仍为

$$
K_{t,z}=\sqrt{1-\beta_t}\,P_z+\sqrt{\beta_t}\,P_{1-z},
\qquad P_z=|z\rangle\langle z|,
\qquad z\in\{0,1\}.
$$

末次仪器之后丢弃 $S$，输出 $H_NR$。对所有允许的共同输入、共同系统 CPTP 控制表和有限参考取最优半迹距离，记作 $T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)$。

**定理 27.2（末次控制的完整分段归约）。** 对定义 27.1 的 $N\ge2$，令 $f=\beta_N$、$a=1-f$。固定共同输入和前 $N-1$ 步的共同控制表。对每个长度 $N-1$ 的历史 $h$，记末次控制之前实际、理想未归一化分支态为 $\rho_h^{\mathrm A},\rho_h^{\mathrm J}$，并令

$$
X_h=\operatorname{Tr}_S\rho_h^{\mathrm A},
\qquad Q_h=\operatorname{Tr}_S\rho_h^{\mathrm J}.
$$

当 $0\le f\le\tfrac12$ 时，任意末次共同系统 CPTP 控制都可逐历史替换为一个共同系统幺正控制，使最终半迹距离不减。替换可依赖已固定的输入和前缀分支态。

当 $\tfrac12\le f\le1$ 时，对这个固定前缀，末次共同系统重置

$$
\mathcal R_0(\sigma)=|0\rangle\langle0|\operatorname{tr}\sigma
$$

已经最优；相应最优半迹距离恰为

$$
\frac12\sum_h\left(\|aX_h-Q_h\|_1+f\operatorname{tr}X_h\right).
$$

因而在高末次错误率区间，有精确表达

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)
=\frac f2+\frac12\sup_{\text{共同输入、有限参考及前缀共同 CPTP 控制}}
\sum_{h\in\{0,1\}^{N-1}}\|aX_h-Q_h\|_1.
$$

右端前缀使用给定的前 $N-1$ 个仪器参数，包含所有共同输入和前 $N-1$ 次系统控制；其控制余系统仍不可再访问。$N=1$ 时另有 $T_1^{\mathrm{ref,CPTP}}(\beta_1)=\beta_1$。本定理只归约末次控制，不把此前的系统 CPTP 控制等同于幺正控制；高错误率表达仍保留对完整前缀的优化，不将它化为简单成功概率乘积。

证明。理想过程在倒数第二次仪器后刚经历秩一指针投影。无论共同输入是否混合、参考维数为何、此前系统 CPTP 控制怎样选择，每个理想分支都满足

$$
\rho_h^{\mathrm J}=P_{i_h}\otimes Q_h,
\qquad i_h=h_{N-1}.
$$

零分支也包含在内。两候选仪器和控制均保持总迹，所以

$$
X_h,Q_h\ge0,
\qquad \sum_h\operatorname{tr}X_h
=\sum_h\operatorname{tr}Q_h=1.
$$

固定一个历史，暂时省略下标 $h$，把 $i_h$ 记为 $i$、实际分支记为 $\rho$。若末次系统控制为 $\Lambda$，令

$$
E=\Lambda^*(P_0),
\qquad 0\le E\le I.
$$

末次丢弃系统之后，实际两个参考块只依赖效应 $fI+(a-f)E$ 与 $aI+(f-a)E$，理想两个参考块则为 $uQ,(1-u)Q$，其中

$$
u=\langle i|E|i\rangle\in[0,1].
$$

因此，固定前缀分支后，两个参考差块关于 $E$ 是仿射函数，它们迹范数之和 $G(E)$ 是凸函数。任意二阶效应都可按其特征值分解为

$$
E=\lambda_{\min}I
+(\lambda_{\max}-\lambda_{\min})\Pi
+(1-\lambda_{\max})0,
\qquad 0\le\lambda_{\min}\le\lambda_{\max}\le1,
$$

其中 $\Pi$ 为秩一正交投影；重特征值时可任选。故 $I,\Pi,0$ 之中至少一个效应的目标不小于 $G(E)$。秩一效应可由系统幺正实现，而 $I,0$ 分别由重置到两个指针实现。

先处理 $f\le\tfrac12$，即 $a\ge f$。在当前理想指针基下，定义实际分支的两个参考对角块

$$
Y=\langle i|\rho|i\rangle,
\qquad Z=\langle1-i|\rho|1-i\rangle,
\qquad Y,Z\ge0,
\qquad Y+Z=X.
$$

令 $D=aY-Q$。常值效应 $E=I$ 的两个参考差块为

$$
D+aZ,
\qquad fY+fZ,
$$

故

$$
G(I)=\|D+aZ\|_1+f\operatorname{tr}Y+f\operatorname{tr}Z.
$$

指针投影效应 $E=P_i$ 的两个参考差块为

$$
D+fZ,
\qquad fY+aZ,
$$

故

$$
G(P_i)=\|D+fZ\|_1+f\operatorname{tr}Y+a\operatorname{tr}Z.
$$

因为 $(a-f)Z$ 半正定，

$$
\|D+aZ\|_1
\le\|D+fZ\|_1+(a-f)\operatorname{tr}Z,
$$

代入即得 $G(I)\le G(P_i)$。效应 $E=0$ 只交换常值效应 $I$ 的两个结果，因此 $G(0)=G(I)$，也被指针投影支配。结合凸分解，任意末次效应都可替换为一个不劣的秩一投影。这些投影在每个历史上分别选择，由共同系统幺正实现；历史块的迹范数相加，所以整体目标不减。证明没有要求实际分支与理想分支的参考因子相同，也没有把替换断言为对所有输入同时成立的通道支配。

现处理 $f\ge\tfrac12$，即 $a\le f$。记任意末次控制之后的实际联合分支为

$$
\sigma=(\Lambda\otimes\operatorname{id}_R)(\rho),
\qquad Y_j=\langle j|\sigma|j\rangle.
$$

系统 CPTP 控制保持参考边缘，因此 $Y_0+Y_1=X$。实际末次两个参考块为

$$
A_0=aY_0+fY_1,
\qquad A_1=fY_0+aY_1.
$$

它们满足

$$
A_0+A_1=X,
\qquad A_0\ge aX,
\qquad A_1\ge aX.
$$

理想两个参考块仍为 $uQ,(1-u)Q$，$u\in[0,1]$。固定当前 $A_0,A_1$，函数

$$
g(v)=\|A_0-vQ\|_1+\|A_1-(1-v)Q\|_1
$$

关于 $v\in[0,1]$ 凸，所以 $g(u)\le\max\{g(0),g(1)\}$。这里两个端点只用于数学上界，不要求它们与固定的 $A_0,A_1$ 来自同一个可实现控制。

对 $v=1$，令 $B=A_0-aX\ge0$。迹范数三角不等式与 $A_1\ge0$ 给出

$$
\begin{aligned}
g(1)
&=\|A_0-Q\|_1+\operatorname{tr}A_1\\
&\le\|aX-Q\|_1+\operatorname{tr}B+\operatorname{tr}A_1\\
&=\|aX-Q\|_1+f\operatorname{tr}X.
\end{aligned}
$$

最后一步使用 $B+A_1=X-aX=fX$。交换 $A_0,A_1$，同样得到 $g(0)$ 不超过这个值。因此，任何末次系统 CPTP 控制的当前历史贡献均不超过

$$
\|aX-Q\|_1+f\operatorname{tr}X.
$$

共同重置 $\mathcal R_0$ 把实际联合分支送到 $P_0\otimes X$，把理想联合分支送到 $P_0\otimes Q$。它的实际末次参考块是 $aX,fX$，理想末次参考块是 $Q,0$，恰好达到所示上界。这一构造可以在所有历史上同时采用。因此固定前缀的最优值就是定理中的块范数之和；再用 $\sum_h\operatorname{tr}X_h=1$ 并对所有允许前缀取上确界，得到精确加权前缀表达。这里不需要证明参考维数归约或最优前缀达到。

在共同边界 $f=\tfrac12$，实际末次参考块始终是 $X/2,X/2$。把理想指针 $|i\rangle$ 幺正地送到 $|0\rangle$，就与重置产生相同的最终参考块，因此两种归约相容。

最后，$N=1$ 没有先前的理想指针投影，不能对任意固定输入套用上述分支乘积论证。此时把唯一共同 CPTP 控制的输出吸收为自由共同输入；定理 22.2 的参考一致上界给出 $T_1^{\mathrm{ref,CPTP}}\le U(0,\beta_1)=\beta_1$。指针输入与恒等控制已达到 $\beta_1$，所以所述单步值成立。这完成全部有限步数的相应结论。证毕。

<a id="entry-95"></a>

## 追加锚（新终端）

<a id="section-28"></a>

## 28. 连续高错误率尾段的精确消去与成功概率公式

**定义 28.1（共同系统 CPTP 前缀的加权参考差异）。** 固定定义 27.1 的前缀参数 $\beta_1,\ldots,\beta_k$，其中 $k\ge1$。对每个允许的共同输入、有限维惰性参考和前 $k$ 次共同系统 CPTP 控制，在第 $k$ 次仪器后对活动系统取部分迹，记历史 $h\in\{0,1\}^k$ 的实际、理想未归一化参考块为 $X_h,Q_h$。这些部分迹只定义前缀的参考读数；续接时仍保留活动系统。对 $c\in[0,1]$，定义

$$
W_k(c)=\sup_{\text{共同输入、有限参考及前 }k\text{ 次共同 CPTP 控制}}
\sum_{h\in\{0,1\}^k}\|cX_h-Q_h\|_1.
$$

参数前缀由下标所指的给定仪器确定，记号中省略；两候选使用共同输入与控制表，控制余系统仍不可再访问，参考始终不可操作。系数 $c$ 只用于比较输出，不改变实际仪器或物理输入的归一化。

**定理 28.2（高错误率尾段的加权消去及全高尾段闭式）。** 对任意有限 $N\ge k\ge1$，假设

$$
\beta_t\ge\frac12
\qquad(k+1\le t\le N),
\qquad
C=\prod_{t=k+1}^N(1-\beta_t),
$$

其中空积为一。则定义 27.1 的最优值精确满足

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)
=\frac{1-C}{2}+\frac12W_k(C).
$$

对每个固定的前 $k$ 步协议，尾段所有共同控制都取为重置到 $|0\rangle$，已经达到该固定前缀的最优续接值；前缀的全局优化仍按定义取上确界。

单步加权值在全部 $\beta_1,c\in[0,1]$ 上为

$$
W_1(c)=1+c-2c(1-\beta_1).
$$

因此，只要每个 $t=2,\ldots,N$ 都满足 $\beta_t\ge\tfrac12$，便有完整精确值

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)
=1-\prod_{t=1}^N(1-\beta_t).
$$

它由无参考指针输入 $|0\rangle$ 和全部恒等系统控制达到。所需条件覆盖整个被消去尾段；只知道最后一个参数至少为一半时，仍须保留较长前缀的 $W_k(C)$，不能据此套用单步公式。本结论不比较一般中间 CPTP 控制与系统幺正控制的最优值。

证明。首先把定理 27.2 的高末次错误率论证用于加权实际块。设 $j\ge2$、$\beta_j\ge\tfrac12$，记 $b=\beta_j$、$d=1-b$，并固定前 $j-1$ 步的协议。对一个旧历史，实际分支记为 $\rho$，参考边缘为 $X$；理想分支为 $P_i\otimes Q$。此乘积结构来自第 $j-1$ 次理想指针读取，对混合输入和任意此前共同系统 CPTP 控制同样成立。

对任意第 $j$ 次共同系统 CPTP 控制，记实际两个输出参考块为 $A_0,A_1$。如第 27.2 条，它们满足

$$
A_0+A_1=X,
\qquad A_0,A_1\ge dX,
$$

理想两个输出参考块为 $uQ,(1-u)Q$，其中 $u\in[0,1]$。在当前加权目标中，实际块变为 $cA_0,cA_1$。固定这些块，对理想系数使用凸性，得到

$$
\begin{aligned}
&\|cA_0-uQ\|_1+\|cA_1-(1-u)Q\|_1\\
&\quad\le\max\left\{
\|cA_0-Q\|_1+c\operatorname{tr}A_1,
\ c\operatorname{tr}A_0+\|cA_1-Q\|_1
\right\}.
\end{aligned}
$$

因为 $c\ge0$，有 $c(A_0-dX)\ge0$。迹范数三角不等式给出

$$
\begin{aligned}
\|cA_0-Q\|_1+c\operatorname{tr}A_1
&\le\|cdX-Q\|_1
+c\operatorname{tr}(A_0-dX)+c\operatorname{tr}A_1\\
&=\|cdX-Q\|_1+cb\operatorname{tr}X.
\end{aligned}
$$

另一个端点同理。共同重置到 $|0\rangle$ 时，实际两块为 $dX,bX$，理想两块为 $Q,0$，恰好达到这个界。整个推导没有除以 $c$，所以也覆盖 $c=0$；加权只是把实际正块乘以非负标量，不要求它们仍是归一化态。

对全部旧历史相加，物理实际分支的总迹始终满足 $\sum_h\operatorname{tr}X_h=1$，从而第 $j$ 步的固定前缀最优加权值为

$$
cb+\sum_h\|cdX_h-Q_h\|_1.
$$

再对全部允许的共同前缀取上确界，得到精确递推

$$
W_j(c)=c\beta_j+W_{j-1}\bigl(c(1-\beta_j)\bigr)
\qquad(j\ge2,\ \beta_j\ge\tfrac12).
$$

上界对任意第 $j$ 次控制成立，达到由重置给出；这两方向保证是等式。对固定更早前缀也可重复同一论证，因此无需先假定最优前缀达到。

现在对定理中的尾段反向应用递推。设

$$
c_j=\prod_{t=j+1}^N(1-\beta_t)
\qquad(k\le j\le N).
$$

于是 $c_N=1$、$c_k=C$，且对 $j=k+1,\ldots,N$ 有

$$
c_{j-1}=c_j(1-\beta_j),
\qquad c_j\beta_j=c_j-c_{j-1}.
$$

由于定义直接给出 $2T_N^{\mathrm{ref,CPTP}}=W_N(1)$，逐步消去尾段并对常数项望远镜求和，得到

$$
\begin{aligned}
2T_N^{\mathrm{ref,CPTP}}
=W_N(1)
&=\sum_{j=k+1}^Nc_j\beta_j+W_k(c_k)\\
&=1-C+W_k(C).
\end{aligned}
$$

空尾段时求和为零，这个式子仍成立。对每个固定前缀，逐步达到使用尾段每次共同重置。也可直接核对：实际尾段的全零记录概率为 $C$，其余记录的总概率为 $1-C$，每种尾段记录都只把同一参考块 $X_h$ 乘以对应标量；理想尾段确定全零，参考块为 $Q_h$。故该固定前缀的最优续接半迹距离为

$$
\frac12\sum_h\left(\|CX_h-Q_h\|_1
+(1-C)\operatorname{tr}X_h\right),
$$

与递推所得表达一致。

还需计算单步加权值。第一共同系统 CPTP 控制的输出可吸收为自由共同输入 $\omega_{SR}$。令

$$
Z_i=\langle i|\omega_{SR}|i\rangle,
\qquad Z_i\ge0,
\qquad \operatorname{tr}Z_0+\operatorname{tr}Z_1=1.
$$

一次实际、理想仪器之后，参考块分别为 $(1-\beta_1)Z_i+\beta_1Z_{1-i}$ 与 $Z_i$。加权差块是

$$
[c(1-\beta_1)-1]Z_i+c\beta_1Z_{1-i}.
$$

由于 $0\le c\le1$，两个所需系数 $1-c(1-\beta_1)$ 与 $c\beta_1$ 都非负。逐块三角不等式给出

$$
\begin{aligned}
&\sum_i\bigl\|[c(1-\beta_1)-1]Z_i+c\beta_1Z_{1-i}\bigr\|_1\\
&\quad\le\bigl[1-c(1-\beta_1)\bigr]
\sum_i\operatorname{tr}Z_i
+c\beta_1\sum_i\operatorname{tr}Z_{1-i}\\
&\quad=1+c-2c(1-\beta_1).
\end{aligned}
$$

无参考指针输入 $|0\rangle$ 与恒等控制使两个结果的加权差分别为 $c(1-\beta_1)-1$ 和 $c\beta_1$，一非正、一非负，恰好达到上界。这证明全部参数域上的单步公式。

当每个 $t\ge2$ 都满足高错误率条件时，取 $k=1$，代入 $W_1(C)$ 即得

$$
T_N^{\mathrm{ref,CPTP}}
=\frac{1-C}{2}
+\frac{1+C-2C(1-\beta_1)}2
=1-\prod_{t=1}^N(1-\beta_t).
$$

这个值也由全部恒等控制及初态 $|0\rangle$ 达到：理想记录确定全零，实际记录全零的概率恰为成功概率乘积，系统在所有非零分支上一直保持同一个指针。$N=1$ 时高尾段条件为空，所得数值就是 $\beta_1$，与单步结论一致。

第 26.1 条的参数 $\beta_1=\beta_2=\tfrac1{10}$、$\beta_3=\tfrac12$ 只允许在这里取 $k=2$ 消去最后一步，留下 $W_2(1/2)$；第二步不满足继续消去到单步所需的高错误率条件。因此本定理的成功概率公式不适用于那个反例。证毕。

<a id="entry-97"></a>

## 追加锚（新终端）

<a id="section-29"></a>

## 29. 加权两步参考差异的 Pauli 协变放宽与解析上界

**定义 29.1（两步加权目标与保留活动系统的放宽）。** 在定义 28.1 的两步任务中，显式写出参数

$$
W_2(c;e,g),
\qquad 0\le c,e\le1,\quad 0\le g\le\frac12,
$$

其中 $e=\beta_1$、$g=\beta_2$。共同输入、惰性参考、共同历史依赖系统 CPTP 控制和末端部分迹的约定均不变。令

$$
a=1-g,\qquad z=1-2g,
\qquad K_i=\sqrt{1-e}\,P_i+\sqrt e\,P_{1-i}.
$$

定义系统退极化通道

$$
\mathcal D_g(\sigma)=z\sigma+g\operatorname{tr}(\sigma)I_S.
$$

由于 $\mathcal D_g$ 是恒等通道与完全退极化通道 $\sigma\mapsto\operatorname{tr}(\sigma)I_S/2$ 按权重 $1-2g,2g$ 的混合，它是 CPTP 映射。它满足任意系统幺正 $U$ 下的协变性

$$
\mathcal D_g(U\sigma U^\dagger)
=U\mathcal D_g(\sigma)U^\dagger.
$$

以 $H_1$ 存储第一次结果，定义两个从 $S$ 到 $H_1S$ 的通道

$$
\mathcal A_{e,g}(\sigma)
=\bigoplus_{i=0}^1\mathcal D_g(K_i\sigma K_i),
\qquad
\mathcal J_e(\sigma)
=\bigoplus_{i=0}^1P_i\sigma P_i,
$$

以及 Hermitian 保持线性映射

$$
\mathcal F_c=c\mathcal A_{e,g}-\mathcal J_e.
$$

记保留 $H_1S$ 并允许惰性参考的加权差异为

$$
\mathcal B(c;e,g)
=\sup_{\substack{1\le\dim R<\infty\\
\omega_{SR}\ge0,\ \operatorname{tr}\omega_{SR}=1}}
\left\|(\mathcal F_c\otimes\operatorname{id}_R)(\omega_{SR})\right\|_1.
$$

这里以保留 $H_1S$ 的固定通道定义放宽目标；其与原任务的关系由下述共同后处理建立，$\mathcal F_c$ 不再包含对控制表的优化。系数 $c$ 不是物理通道的成功概率，也不改变输入归一化。

**定理 29.2（两步解析上界、严格改进与精确参数区间）。** 对定义 29.1 的全部参数域，令

$$
B(c;e,g)
=cg+\sqrt{
\bigl[1-c(1-g)(1-2e)\bigr]^2
+4c^2(1-2g)^2e(1-e)}.
$$

则

$$
W_2(c;e,g)\le\mathcal B(c;e,g)=B(c;e,g).
$$

放宽目标 $\mathcal B$ 的上确界由一个参考量子比特和 Bell 输入

$$
|\Phi\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2}
$$

达到；这不声称原目标 $W_2$ 达到 $B$。若另记

$$
A(c;e,g)
=cg+\sqrt{\bigl[1-c(1-g)\bigr]^2+4c(1-g)e},
$$

则在全部参数域有 $B\le A$，且

$$
c>0,\quad 0<e<1,\quad 0<g\le\frac12
\quad\Longrightarrow\quad B<A.
$$

在精确参数 $c=7/20$、$e=3/10$、$g=1/10$ 上，有

$$
\frac{\sqrt{534}}{25}
\le W_2\left(\frac7{20};\frac3{10},\frac1{10}\right)
\le\frac7{200}+\frac{\sqrt{207433}}{500}.
$$

结合定理 28.2，这给出相应三步任务的精确区间

$$
\frac{13}{40}+\frac{\sqrt{534}}{50}
\le T_3^{\mathrm{ref,CPTP}}
\left(\frac3{10},\frac1{10},\frac{13}{20}\right)
\le\frac{137}{400}+\frac{\sqrt{207433}}{1000}.
$$

证明。先证明任意允许的两步协议都被 $\mathcal B$ 控制。第一共同系统 CPTP 控制的输出可吸收为自由共同输入。末次控制的低错误率幺正归约也适用于当前加权目标：在定理 27.2 的逐历史证明中，将实际未归一化分支 $\rho$ 换成 $c\rho$，保留理想分支 $P_i\otimes Q$。该证明只使用实际块的半正定性、效应的凸分解与迹范数三角不等式，没有使用分支归一化。具体地，以

$$
Y=c\langle i|\rho|i\rangle,
\qquad Z=c\langle1-i|\rho|1-i\rangle,
\qquad D=aY-Q
$$

代入，仍有

$$
\|D+aZ\|_1\le\|D+gZ\|_1+(a-g)\operatorname{tr}Z.
$$

因此两个常值效应被指针投影支配，任意末次共同 CPTP 控制均可换成一个使当前加权目标不减的共同系统幺正。该替换针对固定输入逐历史选择，允许依赖这一输入。

对第一历史 $i$，把其末次共同幺正记作 $U_i$。在任意联合分支 $\rho_{SR}$ 上，第二次实际仪器产生的第 $j$ 个参考块为

$$
a\langle j|U_i\rho_{SR}U_i^\dagger|j\rangle
+g\langle1-j|U_i\rho_{SR}U_i^\dagger|1-j\rangle.
$$

这恰好等于先施加 $\mathcal D_g\otimes\operatorname{id}_R$，再施加 $U_i$ 并作完美指针读取所得的参考块；交叉项在系统部分迹后为零。理想候选同样在其第一分支上施加 $U_i$ 并完美读取。因此，原两步输出的加权差异由

$$
(\mathcal F_c\otimes\operatorname{id}_R)(\omega_{SR})
$$

经同一个依赖 $H_1$ 的 CPTP 后处理得到：调用 $U_i$、完美读取第二结果并丢弃 $S$。Hermitian 算子的迹范数在这一后处理下收缩，所以每个原协议的值不超过 $\mathcal B$，从而 $W_2\le\mathcal B$。

下面直接证明 $\mathcal B$ 的 Bell 达到性。令 $X,Z$ 是系统 Pauli 矩阵，$X_H$ 交换历史基 $|0\rangle,|1\rangle$。从

$$
K_iZ=ZK_i,\qquad P_iZ=ZP_i,
\qquad K_iX=XK_{1-i},\qquad P_iX=XP_{1-i}
$$

及 $\mathcal D_g$ 的协变性，得到

$$
\begin{aligned}
\mathcal F_c(Z\sigma Z)
&=(I_H\otimes Z)\mathcal F_c(\sigma)(I_H\otimes Z),\\
\mathcal F_c(X\sigma X)
&=(X_H\otimes X)\mathcal F_c(\sigma)(X_H\otimes X).
\end{aligned}
$$

故对于四个系统 Pauli 算子 $V_p\in\{I,X,Z,XZ\}$，各存在输出幺正 $\widetilde V_p$，使 $\mathcal F_c(V_p\sigma V_p^\dagger)=\widetilde V_p\mathcal F_c(\sigma)\widetilde V_p^\dagger$。

任取有限参考和归一化纯输入 $|\psi\rangle_{SR}$，以四维辅助参考 $F$ 构造

$$
|\Omega\rangle_{SRF}
=\frac12\sum_{p=0}^3
(V_p\otimes I_R)|\psi\rangle_{SR}\otimes|p\rangle_F.
$$

这个向量归一化。若 $\rho_S=\operatorname{Tr}_R|\psi\rangle\langle\psi|$，则

$$
\operatorname{Tr}_{RF}|\Omega\rangle\langle\Omega|
=\frac14\sum_pV_p\rho_SV_p^\dagger=\frac{I_S}{2}.
$$

把 $\mathcal F_c$ 作用于 $S$，再对 $F$ 去相干，所得 Hermitian 算子是四个块的直和。每块为

$$
\frac14(\widetilde V_p\otimes I_R)
(\mathcal F_c\otimes\operatorname{id}_R)
(|\psi\rangle\langle\psi|)
(\widetilde V_p^\dagger\otimes I_R).
$$

块迹范数相加与幺正不变性表明，去相干后的总迹范数恰等于原输入 $|\psi\rangle$ 的目标值。去相干是 CPTP 映射，所以去相干前、即输入 $|\Omega\rangle$ 的目标值不小于原值。

另一方面，$|\Omega\rangle$ 是系统边缘为 $I_S/2$ 的纯态。其两个参考系数正交且模长均为 $1/\sqrt2$，故存在等距 $V:\mathbb C^2\to R\otimes F$，使

$$
|\Omega\rangle=(I_S\otimes V)|\Phi\rangle.
$$

映射只作用于 $S$，参考等距不改变输出迹范数，因此 $|\Omega\rangle$ 的值等于 Bell 输入的值。Bell 输入于是支配所有有限参考纯输入。对混合输入按纯态分解使用迹范数凸性，结论仍成立。Bell 输入本身可行，所以 $\mathcal B$ 的上确界确实由它达到。辅助标记 $F$ 仅用于这项放宽目标的证明，未被放回原协议作为可操作记忆。

计算 Bell 输出。第一历史 $i$ 的实际、理想向量分别为

$$
|x_i\rangle
=\frac{\sqrt{1-e}|ii\rangle+\sqrt e|1-i,1-i\rangle}{\sqrt2},
\qquad
|y_i\rangle=\frac{|ii\rangle}{\sqrt2}.
$$

该历史的放宽差块是

$$
c z|x_i\rangle\langle x_i|
+cg I_S\otimes\operatorname{Tr}_S|x_i\rangle\langle x_i|
-|y_i\rangle\langle y_i|.
$$

在子空间 $\operatorname{span}\{|ii\rangle,|1-i,1-i\rangle\}$ 上，它的矩阵为

$$
M=\frac12
\begin{pmatrix}
ca(1-e)-1&cz\sqrt{e(1-e)}\\
cz\sqrt{e(1-e)}&cae
\end{pmatrix}.
$$

另外两个正交方向的特征值是 $cg(1-e)/2$ 与 $cge/2$，均非负。注意

$$
\det M
=\frac{ce}{4}\bigl[cg(2-3g)(1-e)-(1-g)\bigr]\le0.
$$

事实上，括号内的负号由

$$
(1-g)-cg(2-3g)(1-e)
\ge1-3g+3g^2
=3\left(g-\frac12\right)^2+\frac14>0
$$

保证。因而 $ce>0$ 时 $M$ 的两特征值异号；$ce=0$ 时同一迹范数公式以连续性或直接计算成立。两特征值的间距给出

$$
\|M\|_1
=\frac12\sqrt{[1-ca(1-2e)]^2+4c^2z^2e(1-e)}.
$$

每个第一历史的块范数为 $cg/2+\|M\|_1$，两历史的表达相同，相加得到 $\mathcal B=B$。

比较两个解析表达，直接展开得

$$
\begin{aligned}
(B-cg)^2
&=(1-ca)^2+4cae
-4c^2g(2-3g)e(1-e)\\
&=(A-cg)^2-4c^2g(2-3g)e(1-e).
\end{aligned}
$$

两个平方根均非负，减去的项在完整参数域非负，在陈述的严格域为正。因此 $B\le A$，并得到所述严格不等式。

最后给出精确区间中的可实现下界。取无参考共同输入 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$、第一控制恒等。令 $x_i=K_i|+\rangle$、$y_i=P_i|+\rangle$，并定义系统 Hermitian 矩阵

$$
D_i=cg\|x_i\|^2I_S+czx_ix_i^\dagger-y_iy_i^\dagger.
$$

选择每个第一历史的共同末次幺正 $U_i$，使 $U_iD_iU_i^\dagger$ 对角。其第二结果 $j$ 的加权实际概率减理想概率恰为该矩阵的第 $j$ 个对角元。因此这个合法协议的目标值为 $\sum_i\|D_i\|_1$。

在指定参数上，直接得到

$$
D_0=\frac1{2000}
\begin{pmatrix}
-769&28\sqrt{21}\\
28\sqrt{21}&119
\end{pmatrix},
\qquad D_1=XD_0X.
$$

$D_0$ 的行列式为负，其两特征值间距为

$$
\sqrt{\left(\frac{-888}{2000}\right)^2
+4\left(\frac{28\sqrt{21}}{2000}\right)^2}
=\frac{\sqrt{534}}{50}.
$$

两历史相加得到 $\sqrt{534}/25$ 的可实现下界；它来自明确输入与共同控制，不依赖数值搜索。上界则将相同参数代入 $B$，使用

$$
cg=\frac7{200},
\qquad
[1-ca(1-2e)]^2+4c^2z^2e(1-e)=\frac{207433}{250000}.
$$

三步参数的高错误率末段为 $\beta_3=13/20$。定理 28.2 给出 $T_3^{\mathrm{ref,CPTP}}=13/40+W_2(7/20;3/10,1/10)/2$，代入两端即得最后一个区间。证毕。

<a id="entry-99"></a>

## 追加锚（新终端）

<a id="section-30"></a>

## 30. 无参考加权两步目标的有限闭式与三步精确值

**定义 30.1（无参考的加权两步经典历史差异）。** 在定义 28.1 中把参考维数限制为一，并显式记第一、第二仪器参数为 $e,g$。共同系统 CPTP 控制的余系统不可再访问，无可操作记忆，无后选择，最终只保留两位经典历史。对所有共同输入和共同系统控制，记实际、理想历史概率为 $p_{ij},q_{ij}$，并定义

$$
W_2^{\mathrm{cl}}(c;e,g)
=\sup\sum_{i,j\in\{0,1\}}|cp_{ij}-q_{ij}|,
\qquad c,e\in[0,1],\quad g\in[0,1/2].
$$

系数 $c$ 仅为输出比较权重。无参考三步系统 CPTP 任务的最优半迹距离记作 $T_3^{\mathrm{cl,CPTP}}$；定义 18.1 原无参考系统幺正任务的最优值仍记作 $T_3$。

**定理 30.2（有限显式候选及三步无参考精确值）。** 在定义 30.1 的完整参数域，令

$$
d=c(1-2g),\qquad r=1-2e,\qquad v=1-cr,
$$

并定义端点与对称候选

$$
P=1+c-2c(1-e)(1-g),
\qquad B=\sqrt{(1-d)^2+4de}.
$$

若 $d=0$ 或 $e\in\{0,1\}$，则

$$
W_2^{\mathrm{cl}}(c;e,g)=P.
$$

这包含 $c=0$ 时的值一、$e=0$ 时的 $1-d$、$e=1$ 时的 $1+c$，以及 $g=1/2$ 时的 $1+ce$。这些情形不使用下述可能退化的分母。

在其余情形 $d>0$、$0<e<1$，令

$$
q_2=1-2d+d^2r^2,
\qquad q_1=2de(1+dr),
\qquad q_0=d^2e^2,
$$

$$
\eta=v+\frac{2q_2+q_1}{2[1-d(1-e)]}.
$$

若 $\eta\ge0$，精确值为

$$
W_2^{\mathrm{cl}}(c;e,g)=\max\{P,B\}.
$$

若 $\eta<0$，则必有 $q_2<0$。定义

$$
h=-q_2>0,
\qquad m=\frac{q_1}{2h},
\qquad \kappa=q_0+\frac{q_1^2}{4h}>0,
$$

$$
M=c(1-e)-1+vm+
\sqrt{\frac{\kappa(h+v^2)}h}.
$$

此时精确值为

$$
W_2^{\mathrm{cl}}(c;e,g)=\max\{P,B,M\}.
$$

第三个候选来自一个交叉项的唯一内部驻点，不需要对连续参数再作优化。上述每个最终最大值都可由纯共同输入、第一控制恒等及两个实正交末次共同控制达到，故这里的系统 CPTP 最优值也等于系统幺正类的最优值。公式没有额外断言第三候选总能被前两个排除。

对任意 $f\in[1/2,1]$，相应无参考系统 CPTP 三步值为

$$
T_3^{\mathrm{cl,CPTP}}(e,g,f)
=\frac f2+\frac12W_2^{\mathrm{cl}}(1-f;e,g).
$$

在 $f=1/2$ 的共同边界，原无参考系统幺正任务也满足

$$
T_3(e,g,1/2)
=\frac14+\frac12W_2^{\mathrm{cl}}(1/2;e,g).
$$

特别地，第 26.1 条的可达下界在这个原无参考任务中已经是精确最优值：

$$
T_3(1/10,1/10,1/2)
=\frac14+\frac{\sqrt{13}}{10}.
$$

这个升级只针对无参考任务，不把该数值宣告为惰性参考任务或可操作记忆任务的最优值。

证明。第一共同系统 CPTP 控制的输出可以吸收为自由共同输入。第二控制的加权幺正归约由定理 27.2 的低错误率证明得到：只需把实际分支乘以非负系数 $c$，其半正定性、效应凸分解和指针投影三角不等式均保持。因此，对每个固定输入，第二控制可取为两个共同系统幺正。

对固定幺正控制表，目标关于共同输入密度矩阵凸，故某个纯态分量的目标不低于混合输入。纯输入的相对相位可写成系统对角幺正；这个幺正与第一步的全部实际、理想结果算子交换，可以吸收到两个第二控制中。因此只需考虑

$$
|\psi_t\rangle=\sqrt t\,|0\rangle+\sqrt{1-t}\,|1\rangle,
\qquad t\in[0,1],
$$

并取第一控制恒等。记

$$
K_i=\sqrt{1-e}\,P_i+\sqrt e\,P_{1-i},
\qquad x_i=K_i|\psi_t\rangle,
\qquad y_i=P_i|\psi_t\rangle.
$$

在第一历史 $i$ 上，定义实对称矩阵

$$
D_i(t)=cg\|x_i\|^2I+d|x_i\rangle\langle x_i|-|y_i\rangle\langle y_i|.
$$

若第二控制为 $U_i$，则该历史的第二结果 $j$ 满足

$$
cp_{ij}-q_{ij}
=\langle j|U_iD_i(t)U_i^\dagger|j\rangle.
$$

对角元绝对值之和不超过 Hermitian 矩阵的迹范数；选择 $D_i(t)$ 的实正交本征基则达到等号。所以固定 $t$ 的最优值是

$$
F(t)=\|D_0(t)\|_1+\|D_1(t)\|_1,
\qquad W_2^{\mathrm{cl}}=\max_{0\le t\le1}F(t).
$$

这里最大值存在，因为 $F$ 连续。交换两个系统指针给出 $D_1(t)=XD_0(1-t)X$。令

$$
p(t)=e+rt,
\qquad L(t)=cp(t)-t=ce-vt,
\qquad R(t)=\sqrt{q_2t^2+q_1t+q_0}.
$$

$D_0(t)$ 的迹为 $L(t)$，两个本征值的间距为 $R(t)$。具体地，间距平方等于

$$
[de+(1-d)t]^2+4d^2e(1-e)t(1-t),
$$

展开就是上述 $q_2,q_1,q_0$。同时，$D_0(t)$ 在方向 $|1\rangle$ 上的二次型为

$$
cg\,p(t)+de(1-t)\ge0,
$$

所以其较大本征值非负。这保证 $-L(t)\le R(t)$，由二阶 Hermitian 矩阵的迹范数公式得到

$$
\|D_0(t)\|_1=\max\{L(t),R(t)\},
$$

从而

$$
F(t)=\max\{L(t),R(t)\}
+\max\{L(1-t),R(1-t)\}.
$$

先处理退化情形。若 $d=0$，则 $R(t)=t$；若 $e=0$，则 $R(t)=(1-d)t$；若 $e=1$，则 $R(t)=d+(1-d)t$。这些情形中的 $L,R$ 都是仿射函数，故 $F$ 凸。又有 $F(t)=F(1-t)$，所以最大值由 $t=0$ 或 $t=1$ 达到。直接代入得 $F(0)=P$，证明全部所列边界值，也避免了端点根为零时的求导。

以下设 $d>0$、$0<e<1$。此时 $R(t)>0$，并且

$$
4q_2q_0-q_1^2=-16d^3e^2(1-e)<0.
$$

因此

$$
R''(t)=\frac{4q_2q_0-q_1^2}{4R(t)^3}<0,
$$

即 $R$ 严格凹。把 $F$ 中的两个最大值展开成四种和，便有

$$
\begin{aligned}
F(t)=\max\{&L(t)+L(1-t),\ R(t)+R(1-t),\\
&L(t)+R(1-t),\ R(t)+L(1-t)\}.
\end{aligned}
$$

第一项恒为 $c-1\le0$。第二项由凹性在 $t=1/2$ 达到最大值

$$
2R(1/2)=\sqrt{(1-d)^2+4de}=B.
$$

两个交叉项在 $t\mapsto1-t$ 下互换，故具有相同最大值。令 $u=1-t$，则其中一个是

$$
L(t)+R(1-t)=L(1)+vu+R(u),
\qquad L(1)=c(1-e)-1.
$$

于是问题精确化为

$$
W_2^{\mathrm{cl}}
=\max\left\{B,\ L(1)+\max_{0\le u\le1}H(u)\right\},
\qquad H(u)=R(u)+vu.
$$

这一步只是有限最大值的分配，没有把两个函数各自凹误认为它们的逐点最大值仍凹。

$H$ 严格凹，且

$$
H'(0)=1+dr+v>0,
\qquad
H'(1)=v+\frac{2q_2+q_1}{2[1-d(1-e)]}=\eta.
$$

分母严格为正，因为 $1-d(1-e)\ge e>0$。若 $\eta\ge0$，严格凹性使 $H$ 在整个区间上不减，最大值取在 $u=1$。相应交叉值为

$$
L(1)+H(1)=ce+R(1)=P,
$$

于是 $W_2^{\mathrm{cl}}=\max\{P,B\}$，也包括 $\eta=0$ 的端点驻点。

若 $\eta<0$，则 $H'$ 从正变负且严格递减，存在唯一内部最大点。由于 $q_1>0$，$q_2\ge0$ 会使 $R'$ 全程为正，故此时必须有 $q_2<0$。按陈述中的 $h,m,\kappa$ 完成平方，得到

$$
R(u)=\sqrt{\kappa-h(u-m)^2}.
$$

方程 $H'(u)=0$ 的唯一适当符号解是

$$
u_*=m+v\sqrt{\frac{\kappa}{h(h+v^2)}}\in(0,1).
$$

代入得

$$
\max_{0\le u\le1}H(u)
=vm+\sqrt{\frac{\kappa(h+v^2)}h}.
$$

所以交叉项最大值为 $M$。因为这个内部最大值严格高于端点值，$M>P$；保留端点候选仍可统一写成 $W_2^{\mathrm{cl}}=\max\{P,B,M\}$。

这些公式也给出达到控制。端点候选取 $t=0$，对称候选取 $t=1/2$；若第三候选为最终最大项，取 $t=1-u_*$。在最后一种情况下，$F(1-u_*)\ge M$，而已证全局上界就是 $M$，因此该输入确实达到最优。随后在两个第一历史上分别用 $D_i(t)$ 的实正交本征基作第二共同控制。这完成有限闭式及幺正达到的证明；不需要再判断第三候选是否总被其他候选支配。

把定理 28.2 的同一加权尾段论证限制到平凡参考，便得到任何 $f\ge1/2$ 下的三步系统 CPTP 等式

$$
T_3^{\mathrm{cl,CPTP}}(e,g,f)
=\frac f2+\frac12W_2^{\mathrm{cl}}(1-f;e,g).
$$

在 $f=1/2$ 时，定理 27.2 已说明末次重置可以用把理想前缀指针送到 $|0\rangle$ 的系统幺正替代，而本定理已用系统幺正实现前两步加权最优值。因此整个三步值由原无参考系统幺正协议达到；控制类包含给出反向界，从而原 $T_3$ 也满足陈述中的精确式。

最后代入 $c=1/2$、$e=g=1/10$，得到

$$
d=\frac25,\quad r=\frac45,\quad v=\frac35,
\qquad q_2=\frac{189}{625},\quad q_1=\frac{66}{625},\quad q_0=\frac1{625},
$$

$$
\eta=\frac{231}{200}>0,
\qquad P=\frac{69}{100},
\qquad B=\frac{\sqrt{13}}5>P.
$$

因此 $W_2^{\mathrm{cl}}(1/2;1/10,1/10)=\sqrt{13}/5$，进而

$$
T_3(1/10,1/10,1/2)
=\frac14+\frac{\sqrt{13}}{10}.
$$

这把第 26.1 条同一无参考幺正构造的可达下界提升为该任务的精确值，且没有扩大其参考或记忆访问权限。证毕。

<a id="entry-101"></a>

## 追加锚（新终端）

<a id="section-31"></a>

## 31. 高末次错误率下任意 CPTP 控制的记忆等号分类

**定理 31.1（任意有限前缀的加权上界）。** 令 $W_j(c)$ 为定义 28.1 的共同系统 CPTP 前缀目标，允许任意有限维惰性参考，没有可操作量子记忆。对任意有限 $j\ge1$、$c\in[0,1]$ 和仪器参数 $\beta_1,\ldots,\beta_j\in[0,1]$，记

$$
b=\beta_j,\qquad a=1-b,
\qquad s=\prod_{t=1}^{j-1}\sqrt{1-\beta_t},
$$

其中空积为一。则

$$
W_j(c)
\le cb+\sqrt{(1+ca)^2-4ca s^2}.
$$

这个界同时适用于任意共同输入、有限参考和全部共同历史依赖系统 CPTP 控制；它不要求前缀幺正，也不声称一般参数下达到该加权上界。

证明。当 $j=1$ 时，定理 28.2 的单步计算给出

$$
W_1(c)=1+c-2c(1-b)=cb+1-ca.
$$

由于 $0\le ca\le1$，这等于 $cb+\sqrt{(1+ca)^2-4ca}$，证明空前缀情形。

以下设 $j\ge2$，固定任意共同输入、有限参考和共同 CPTP 控制表。给共同输入作纯化；每个共同控制使用同一个 Stinespring 等距实现，并在分析中保留其余系统。对不同旧历史使用的等距按历史作共同受控调用。控制余系统始终不重新接入协议；保留它们只是为了表示完整纯化，计算物理输出时仍将它们取部分迹。

以 $B_t$ 存储本次新结果、$E_t$ 存储其丢弃副本，一次仪器可以由如下两种等距表示：

$$
V_{{\rm A},t}=\sum_{z=0}^1
|z\rangle_{B_t}|z\rangle_{E_t}\otimes K_{t,z},
\qquad
V_{{\rm J},t}=\sum_{z=0}^1
|z\rangle_{B_t}|z\rangle_{E_t}\otimes P_z.
$$

旧历史寄存器在此不变，$E_t$ 在物理协议中被丢弃。交叉算子满足

$$
V_{{\rm J},t}^\dagger V_{{\rm A},t}
=\sum_zP_zK_{t,z}
=\sqrt{1-\beta_t}\,I_S.
$$

共同受控等距保持完整纯化的内积，每个仪器则将该内积乘以上述标量。因此，经过前 $j-1$ 次仪器及第 $j$ 次共同 CPTP 控制后，完整纯化中的两候选可取为归一化向量 $|A\rangle,|J\rangle$，满足

$$
\langle J|A\rangle=s.
$$

惰性参考不参与控制。共同输入的纯化寄存器、控制余系统及历史副本只属于分析空间，不增加原协议的访问权限。

在两候选上都假设最后作完美指针读取，存储最后一位历史并丢弃活动系统和全部分析余系统。所得归一化经典量子态记为 $\mathsf P,\mathsf Q$，输出空间是 $H_jR$。它们来自 $|A\rangle,|J\rangle$ 经同一个 CPTP 映射，其中 $\mathsf Q$ 正好是理想最终输出。令 $\tau$ 仅翻转最后一位经典结果，保持旧历史和参考不动。

对第 $j$ 次控制后的任意实际联合历史分支 $\omega_h$，最后实际结果 $z$ 的参考块为

$$
\begin{aligned}
&\operatorname{Tr}_S\bigl[
(K_{j,z}\otimes I_R)\omega_h(K_{j,z}\otimes I_R)
\bigr]\\
&\qquad=a\langle z|\omega_h|z\rangle
+b\langle1-z|\omega_h|1-z\rangle.
\end{aligned}
$$

两个指针间的交叉项在系统部分迹后为零，所以实际最终态严格等于

$$
\mathsf R=a\mathsf P+b\tau(\mathsf P).
$$

这里没有限制最后共同控制的形式。于是

$$
\begin{aligned}
\|c\mathsf R-\mathsf Q\|_1
&=\|ca\mathsf P-\mathsf Q+cb\tau(\mathsf P)\|_1\\
&\le\|ca\mathsf P-\mathsf Q\|_1+cb\\
&\le\bigl\|ca|A\rangle\langle A|-|J\rangle\langle J|\bigr\|_1+cb\\
&=\sqrt{(1+ca)^2-4ca|\langle J|A\rangle|^2}+cb\\
&=\sqrt{(1+ca)^2-4ca s^2}+cb.
\end{aligned}
$$

第一项估计使用迹范数三角不等式及 $\|\tau(\mathsf P)\|_1=1$；第二项使用共同 CPTP 输出映射对 Hermitian 算子的迹范数收缩；最后使用两个加权秩一算子之差的迹范数公式。该公式也覆盖 $ca=0$，整个论证没有除以权重或分支概率。

物理输出对历史分块，因此 $\|c\mathsf R-\mathsf Q\|_1=\sum_h\|cX_h-Q_h\|_1$。上界不依赖共同输入、参考维数或共同控制表，对所有允许协议取上确界即得结论。证毕。

**定理 31.2（高末次错误率的完整等号域与最小可操作记忆）。** 对定义 27.1 的任意有限 $N\ge2$，假设最后参数

$$
f=\beta_N\in[1/2,1].
$$

记

$$
c=1-f,\qquad b=\beta_{N-1},\qquad a=1-b,
\qquad s=\prod_{t=1}^{N-2}\sqrt{1-\beta_t},
\qquad E=1-as^2.
$$

令 $U(E,f)$ 为定理 22.2 的可操作记忆最优值。在没有可操作记忆、允许任意有限惰性参考及所有共同历史依赖系统 CPTP 控制时，有完整等号分类

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)=U(E,f)
\quad\Longleftrightarrow\quad
\beta_{N-1}=0
\ \text{或}\ 
\exists t\in\{1,\ldots,N\},\ \beta_t=1.
$$

进一步定义

$$
r=\sqrt{(1+ca)^2-4ca s^2},
\qquad A=cb+r,
\qquad C=\sqrt{(1+c)^2-4ca s^2}.
$$

则

$$
T_N^{\mathrm{ref,CPTP}}\le\frac{f+A}{2}
\le\frac{f+C}{2}=U(E,f).
$$

在其余参数域，即 $b>0$ 且所有 $\beta_t<1$ 时，这个上界给出显式严格差距

$$
U(E,f)-T_N^{\mathrm{ref,CPTP}}
\ge\frac{cb(1+ca-r)}{C+A}>0.
$$

考虑定义 22.1 的可操作记忆任务，允许任意共同 $SM$ CPTP 控制和额外任意有限维惰性参考 $R$，最终输出 $H_NMR$。以达到 $U(E,f)$ 为目标，所需非零可操作记忆 $M$ 的最小维数为

$$
d_{\min}(\boldsymbol\beta)=
\begin{cases}
1,&\beta_{N-1}=0\ \text{或存在 }t\text{ 使 }\beta_t=1,\\
2,&\beta_{N-1}>0\ \text{且全部 }\beta_t<1.
\end{cases}
$$

当 $N=1$ 时，在完整参数域另有 $T_1^{\mathrm{ref,CPTP}}(\beta_1)=U(0,\beta_1)=\beta_1$，且 $d_{\min}=1$。本条多步等号分类和最小记忆结论限定于 $f\ge1/2$，不判定 $f<1/2$ 下任意中间系统 CPTP 控制的等号域。

证明。定理 27.2 对高末次错误率给出精确前缀表达

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)
=\frac f2+\frac12W_{N-1}(c).
$$

对这个任意 CPTP 前缀应用定理 31.1，得到 $W_{N-1}(c)\le cb+r=A$。这一步覆盖混合共同输入、任意有限参考及全部此前系统 CPTP 控制，不需要把中间控制替换为幺正。

由 $E=1-as^2$ 和 $f=1-c$，可操作记忆值中的平方根满足

$$
f^2+4(1-f)E
=(1+c)^2-4ca s^2=C^2,
$$

故 $U(E,f)=(f+C)/2$。直接展开得

$$
\begin{aligned}
C^2-A^2
&=(1+c)^2-(1+ca)^2-c^2b^2-2cbr\\
&=2cb(1+ca-r).
\end{aligned}
$$

所有系数非负，且 $r\le1+ca$，所以 $C^2\ge A^2$；由于 $C,A\ge0$，得到 $A\le C$。

设 $b>0$ 且全部 $\beta_t<1$。由于 $f<1$，有 $c>0$；由于 $b<1$，有 $a>0$；此前每个参数也小于一，故 $s>0$。因此

$$
(1+ca)^2-r^2=4ca s^2>0,
$$

从而 $1+ca-r>0$。这使 $C^2-A^2>0$，即 $A<C$。此外 $C\ge1-c=f\ge1/2$，所以 $C+A>0$，且

$$
\begin{aligned}
U(E,f)-T_N^{\mathrm{ref,CPTP}}
&\ge\frac{C-A}{2}\\
&=\frac{C^2-A^2}{2(C+A)}\\
&=\frac{cb(1+ca-r)}{C+A}>0.
\end{aligned}
$$

这是一条对所有允许协议统一成立的严格界，无需证明最优前缀达到。前面若有参数等于零，仍有 $s>0$，因此它们不被遗漏。

反过来，若存在某个 $\beta_t=1$，取无参考指针初态 $|0\rangle$ 和所有控制恒等。理想历史确定全零，而实际在该时刻必输出一，因此两种完整历史支撑不交，半迹距离为一。此时 $U(E,f)=1$，所以无需参考或可操作记忆即达到等号。

若 $\beta_{N-1}=0$，定理 22.3 已给出无参考、共同系统幺正控制达到 $U(E,f)$ 的构造。该协议包含于当前允许类中；结合统一上界，再次得到等号。这两个条件的补集恰为 $b>0$ 且全部 $\beta_t<1$，其严格不等式已证，故等号分类完整。

最后确定记忆维数。$\dim M=1$ 时，对 $SM$ 的共同 CPTP 控制恰退化为系统 CPTP 控制，额外惰性参考和最终保留的 $R$ 完全对应 $T_N^{\mathrm{ref,CPTP}}$。在严格域，统一差距排除 $\dim M=1$ 达到 $U$。另一方面，定理 22.2 已用一个初始为 $|0\rangle$ 的记忆量子比特、末次前的一次 SWAP 和此前共同实反馈达到 $U$，不需要惰性参考，所以 $\dim M=2$ 足够。在等号域，上述无参考构造以 $\dim M=1$ 已经达到；非零记忆空间的维数不能更小，得到所述最小维数。

$N=1$ 的共同系统 CPTP 控制可吸收为自由共同输入，定理 27.2 的单步值为 $\beta_1$；指针输入已经达到定理 22.2 的 $U(0,\beta_1)=\beta_1$。因此单步所需最小记忆维数为一，且不需要高错误率假设。证毕。

<a id="entry-103"></a>

## 追加锚（新终端）

<a id="section-32"></a>

## 32. 低末次错误率下任意 CPTP 控制的严格记忆差距

**定理 32.1（低末次错误率的完整 CPTP 等号分类）。** 对定义 27.1 的任意有限 $N\ge2$，设

$$
0<f=\beta_N<\frac12,
\qquad a=1-f,
\qquad s=\prod_{t=1}^{N-1}\sqrt{1-\beta_t},
\qquad E=1-s^2.
$$

允许任意有限维惰性参考、共同联合输入和全部共同历史依赖系统 CPTP 控制，没有可操作量子记忆，最终丢弃活动系统。则

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)=U(E,f)
\quad\Longleftrightarrow\quad
\beta_{N-1}=0
\quad\text{或}\quad
\exists t\in\{1,\ldots,N\},\ \beta_t=1,
$$

其中 $U(E,f)$ 是定理 22.2 的可操作记忆最优值。特别地，若 $\beta_{N-1}>0$ 且全部 $\beta_t<1$，则

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)<U(E,f).
$$

这里的严格性覆盖任意中间系统 CPTP 控制；它不把这些控制逐一等同于系统幺正控制。结合第 31 章和末次完美读取的边界，等号条件与第 24 章的系统幺正参考任务一致。

证明。先说明优化域的有限维归约与最大值存在性。第一共同系统 CPTP 控制的输出可以吸收为自由共同输入，并把第一控制取为恒等。固定余下共同控制表，最终差异的迹范数关于共同输入密度矩阵凸。因此，任意混合输入都有一个纯态分量，其目标不低于混合输入。这里选择的是另一个允许的共同输入，没有对仪器结果作后选择。

活动系统为二维，纯输入的 Schmidt 秩至多为二。参考始终不被操作，故其 Schmidt 支撑可等距压缩到 $\mathbb C^2$，保持所有系统控制及最终迹范数不变；秩一情形补一个零坐标即可。因此全体有限参考的上确界等于参考固定为一个量子比特、共同输入为归一化纯态、第一控制恒等时的上确界。

每个系统 CPTP 映射的 Choi 矩阵满足正半定与固定输出部分迹条件，构成有限维紧集。固定有限 $N$ 的历史树只有有限个控制节点，全部共同控制表属于这些紧集的有限乘积。归一化两比特纯态的单位球面也紧，而有限步输出及其迹范数连续。因此 $T_N^{\mathrm{ref,CPTP}}$ 的最大值在上述有限维域中达到。

若 $\beta_{N-1}=0$ 或存在某个 $\beta_t=1$，定理 22.3 的无参考系统幺正构造已经达到 $U(E,f)$。它属于当前允许类，结合定理 22.2 的参考一致上界，即得等号的充分性。

以下设 $\beta_{N-1}>0$ 且全部 $\beta_t<1$，所以

$$
a>0,\qquad f>0,\qquad s>0,
\qquad 0<\beta_{N-1}<1.
$$

反设某个允许协议达到 $U(E,f)$。按上述归约，可取共同纯输入、参考维数至多二及第一控制恒等。定理 27.2 对低末次错误率允许逐历史把最后的共同 CPTP 控制换成系统幺正，使目标不减。由于所有协议仍受 $U(E,f)$ 上界约束，替换后也达到等号。记最后的共同系统幺正为 $W_h$，此前的系统 CPTP 控制仍完全任意。

对前 $N-1$ 步使用共同受控 Stinespring 纯化，保留控制余系统及仪器的历史副本，仅在分析中使用这些寄存器。物理协议仍将它们丢弃且不重新访问。对每个长度 $N-1$ 的历史 $h$，把末次幺正之前的完整纯化分支记为

$$
|x_h\rangle,|y_h\rangle\in S\otimes R\otimes\mathcal E,
$$

其中 $\mathcal E$ 包含所有分析余系统；不同分支可补齐为同一个有限维空间。令

$$
p_h=\|x_h\|^2,\qquad q_h=\|y_h\|^2,
\qquad \delta_h=\langle y_h,x_h\rangle,
$$

$$
\rho_h^{\rm A}=\operatorname{Tr}_{\mathcal E}|x_h\rangle\langle x_h|,
\qquad
\rho_h^{\rm J}=\operatorname{Tr}_{\mathcal E}|y_h\rangle\langle y_h|.
$$

共同受控等距保持完整内积，每次实际、理想仪器的交叉算子为 $\sum_zP_zK_{t,z}=\sqrt{1-\beta_t}I$。因此

$$
\sum_hp_h=\sum_hq_h=1,
\qquad \sum_h\delta_h=s.
$$

理想过程第一次读取后，每个非零物理分支已成为系统指针与纯参考向量的乘积。后续控制只作用于系统，不能改变该分支的纯参考因子；每次理想读取再把系统投影到秩一指针。所以末次控制之前

$$
\rho_h^{\rm J}=|\eta_h\rangle\langle\eta_h|,
\qquad
\eta_h=|i_h\rangle\otimes r_h,
\qquad i_h=h_{N-1},
$$

允许 $\eta_h=0$。这项纯性来自纯共同输入与理想秩一仪器，不要求中间系统控制幺正。

令

$$
G_h=\|a\rho_h^{\rm A}-\rho_h^{\rm J}\|_1,
\qquad
L_h=\sqrt{(ap_h+q_h)^2-4a|\delta_h|^2},
\qquad \Gamma=\sum_h|\delta_h|.
$$

$L_h$ 是完整纯化上两个加权秩一算子之差的迹范数，因此部分迹收缩给出 $G_h\le L_h$。最后实际读取等于完美读取结果按权重 $a,f$ 保留或翻转；对共同末次幺正和完美读取使用迹范数收缩，再对翻转正项使用三角不等式，得到

$$
\begin{aligned}
2T_N^{\mathrm{ref,CPTP}}
&\le\sum_hG_h+f\\
&\le\sum_hL_h+f\\
&\le\sqrt{(a+1)^2-4a\Gamma^2}+f\\
&\le\sqrt{(a+1)^2-4as^2}+f=2U(E,f).
\end{aligned}
$$

第三步的理由是二维实向量 $(L_h,2\sqrt a|\delta_h|)$ 的范数为 $ap_h+q_h$，对这些向量应用欧氏三角不等式；第四步使用 $\Gamma\ge|\sum_h\delta_h|=s$。

在假设的达到情形中，以上每一步都必须取等。因为 $a,s>0$，最后一步强制 $\Gamma=s$。欧氏三角不等式的等号又要求全部非零向量同向，故每个活历史，即 $p_h+q_h>0$ 的历史，都满足

$$
|\delta_h|=\frac{s(ap_h+q_h)}{a+1}>0.
$$

特别地，每个活历史都有 $p_h,q_h>0$。有限项不等式 $G_h\le L_h$ 也必须逐项取等。

下面把这项环境部分迹等号转为物理纯性。固定一个活历史，省略下标。理想物理分支为纯态，故完整理想向量可分解为

$$
y=\eta\otimes e,
\qquad \|e\|=1,
\qquad \|\eta\|^2=q.
$$

把实际向量按同一个环境方向正交分解为

$$
x=\xi_0\otimes e+x_\perp,
\qquad
(I_{SR}\otimes\langle e|)x_\perp=0.
$$

令 $p_0=\|\xi_0\|^2$、$p_1=\|x_\perp\|^2$，则 $p=p_0+p_1$、$\delta=\langle\eta,\xi_0\rangle\ne0$，并有

$$
\rho^{\rm A}=|\xi_0\rangle\langle\xi_0|+\rho_\perp,
\qquad \rho_\perp\ge0,
\qquad \operatorname{tr}\rho_\perp=p_1.
$$

定义

$$
L_0=\sqrt{(ap_0+q)^2-4a|\delta|^2}.
$$

三角不等式给出 $G\le L_0+ap_1$，而直接相减得到

$$
\begin{aligned}
L^2-(L_0+ap_1)^2
&=2ap_1\bigl[ap_0+q-L_0\bigr].
\end{aligned}
$$

因为 $a>0$ 且 $\delta\ne0$，方括号严格为正。如果 $p_1>0$，便有 $G<L$，与逐历史的部分迹等号矛盾。因此 $p_1=0$。恢复下标后，每个活历史都可写为

$$
x_h=\xi_h\otimes e_h,
\qquad y_h=\eta_h\otimes e_h,
\qquad \|e_h\|=1.
$$

于是实际物理分支也纯，并且

$$
\rho_h^{\rm A}=|\xi_h\rangle\langle\xi_h|,
\qquad \delta_h=\langle\eta_h,\xi_h\rangle\ne0.
$$

这没有宣称中间 CPTP 控制可逆；它只是达到假设迫使末次前缀的两候选完整纯化共用同一个环境方向。

接着使用第 24 章证明中的单分支末次严格估计。其准确前提是：实际物理向量 $\xi$ 具有 Schmidt 秩二，理想物理向量为非零 $|i\rangle\otimes r$，二者内积非零，$a,f>0$，末次控制是共同系统幺正。该局部估计不要求更早的控制幺正。下面在当前变量中展开其两种情形，以核对这些前提和结论的对应。

假设某个活历史的 $\xi_h$ 具有 Schmidt 秩二。省略该历史下标，定义

$$
v_j=(\langle j|W\otimes I_R)\xi,
\qquad c_j=|\langle j|W|i\rangle|,
\qquad j=0,1.
$$

则 $v_0,v_1$ 线性无关，且 $c_0^2+c_1^2=1$。定义完美读取比较块及实际最终差块

$$
B_j=a|v_j\rangle\langle v_j|-c_j^2|r\rangle\langle r|,
\qquad
F_j=B_j+f|v_{1-j}\rangle\langle v_{1-j}|.
$$

若 $c_0c_1=0$，交换末次标签后可取 $c_0=1,c_1=0$。令 $p_j=\|v_j\|^2$、$q=\|r\|^2$、$k=|\langle r,v_0\rangle|^2$。Schmidt 秩二给出 $p_1>0$，共同幺正保持内积给出 $k=|\delta_h|^2>0$。完美读取后的范数和为

$$
J=\sqrt{(ap_0+q)^2-4ak}+ap_1.
$$

当前物理加权差块的范数为 $G_h=L_h$，并满足

$$
G_h^2-J^2
=2ap_1\left[ap_0+q-\sqrt{(ap_0+q)^2-4ak}\right]>0.
$$

所以完美读取已经严格收缩，不能取等。

若 $c_0,c_1>0$，参考空间至多二维，而 $v_0,v_1$ 独立，故存在复系数 $\ell,m$，使

$$
r=\ell v_0+mv_1.
$$

这两个展开系数独立于控制幅度 $c_0,c_1$。若 $\ell,m$ 均非零，可选择 $v_0,v_1$ 的代表相位使 $\ell,m>0$；这不改变任何参考投影或比较块。记

$$
A=\|v_0\|^2,\qquad B=\|v_1\|^2,
\qquad C=\langle v_0,v_1\rangle,
\qquad AB-|C|^2>0.
$$

此时

$$
\det B_0=-ac_0^2m^2(AB-|C|^2)<0,
\qquad
\det B_1=-ac_1^2\ell^2(AB-|C|^2)<0.
$$

第 24 章所用的迹范数等号事实是：对可逆不定 Hermitian 矩阵 $D$，若向它加一个非零正秩一算子仍在三角不等式中取等，则该正算子的向量必须属于 $D$ 的正谱子空间。这来自迹范数的 Hermitian 对偶收缩算子；可逆性使取到 $D$ 范数的算子唯一为 $\operatorname{sign}(D)$。

若两个 $F_j$ 的正噪声三角不等式都取等，就必须有

$$
B_0v_1=\lambda_0v_1,\qquad
B_1v_0=\lambda_1v_0,
\qquad \lambda_0,\lambda_1>0.
$$

在独立基 $v_0,v_1$ 中比较系数，得到

$$
\lambda_0=-c_0^2m(\ell C+mB),
\qquad
\lambda_1=-c_1^2\ell(\ell A+m\overline C).
$$

两式的实正性迫使 $C$ 为实数，且

$$
C\le-\frac m\ell B,
\qquad C\le-\frac\ell m A.
$$

这推出 $|C|^2\ge AB$，与向量独立性矛盾。

若 $\ell=0$，则 $r=mv_1$ 且 $m\ne0$。此时 $B_0$ 可逆不定，而

$$
B_0v_1=aCv_0-c_0^2|m|^2Bv_1.
$$

让 $v_1$ 成为它的正特征向量，先要求 $C=0$，随后又得到负特征值 $-c_0^2|m|^2B$，矛盾。$m=0$ 的情形对 $B_1,v_0$ 对称。由于 $r\ne0$，两系数不会同时为零。因此 $c_0,c_1>0$ 时至少一个正噪声三角不等式严格。

两种控制情形都给出

$$
\sum_j\|F_j\|_1<G_h+fp_h.
$$

这会使总目标严格小于 $U(E,f)$，与达到假设矛盾。因此，所有活历史中的实际纯物理向量都只能具有 Schmidt 秩一，即可以写成

$$
\xi_h=x_h^{S}\otimes r_h^{\rm A},
\qquad
\eta_h=y_h^{S}\otimes r_h^{\rm J},
$$

其中理想系统因子 $y_h^S$ 沿指针 $|i_h\rangle$。这里参考因子 $r_h^{\rm A},r_h^{\rm J}$ 可以不同。

最后处理这些纯乘积分支。对共同末次幺正后的假想完美读取，定义纯参考向量

$$
u_{h,j}=\langle j|W_hx_h^S\rangle r_h^{\rm A},
\qquad
v_{h,j}=\langle j|W_hy_h^S\rangle r_h^{\rm J}.
$$

以 $k=(h,j)$ 简记最终经典坐标，并令

$$
P_k=\|u_k\|^2,\qquad Q_k=\|v_k\|^2,
\qquad \gamma_k=\langle v_k,u_k\rangle.
$$

由于前缀的环境方向已逐历史相同，并且末次幺正与完美读取保持内积总和，

$$
\sum_kP_k=\sum_kQ_k=1,
\qquad
\sum_k\gamma_k=\sum_h\delta_h=s.
$$

记

$$
D_k=a|u_k\rangle\langle u_k|-|v_k\rangle\langle v_k|,
\qquad
\ell_k=\|D_k\|_1
=\sqrt{(aP_k+Q_k)^2-4a|\gamma_k|^2}.
$$

实际最终差块为 $D_{h,j}+f|u_{h,1-j}\rangle\langle u_{h,1-j}|$。对最终坐标重复正噪声三角不等式、欧氏三角不等式及复数三角不等式，得到

$$
\begin{aligned}
2T_N^{\mathrm{ref,CPTP}}
&\le\sum_k\ell_k+f\\
&\le\sqrt{(a+1)^2-4a\left(\sum_k|\gamma_k|\right)^2}+f\\
&\le\sqrt{(a+1)^2-4as^2}+f=2U(E,f).
\end{aligned}
$$

达到假设再次强制全部等号。因而每个活坐标 $P_k+Q_k>0$ 都满足

$$
|\gamma_k|=\frac{s(aP_k+Q_k)}{a+1}>0.
$$

所以 $P_k>0$ 当且仅当 $Q_k>0$，且活坐标上的两个参考向量内积非零。这是经典坐标的非零质量支撑相同，不要求两参考向量平行。

另一方面，

$$
\sum_k\operatorname{tr}D_k=a-1=-f<0.
$$

因此存在一个坐标 $(h,j)$ 满足 $\operatorname{tr}D_{h,j}<0$。该坐标活跃，故 $u=u_{h,j}$、$v=v_{h,j}$ 都非零，且 $\langle v,u\rangle\ne0$。实际前缀的乘积结构保证 $u_{h,1-j}$ 与 $u$ 平行。

若 $u,v$ 线性无关，则 $D=a|u\rangle\langle u|-|v\rangle\langle v|$ 在二维参考空间上可逆不定。如果 $u_{h,1-j}\ne0$，正噪声三角等号就要求 $u$ 为 $D$ 的正特征向量。然而

$$
Du=a\|u\|^2u-\langle v,u\rangle v
$$

不与 $u$ 平行，因为内积非零且 $u,v$ 独立，矛盾。若 $u,v$ 平行，负迹条件使 $D$ 成为非零负半定秩一算子；任何沿同方向的非零正噪声都会使标量三角不等式严格。因此两种情形都要求

$$
u_{h,1-j}=0.
$$

非零质量支撑相同再给出 $v_{h,1-j}=0$。选中坐标的两参考向量均非零，所以共同末次幺正之后的两个系统因子都沿 $|j\rangle$。共同系统幺正可逆，故控制之前的实际系统因子与理想系统因子平行，即实际物理分支的系统支撑为 $P_{i_h}$。

把选中历史写成 $h=g\ell$，其中 $\ell=i_h$ 是倒数第二次结果。令 $\sigma_g^{\rm A}$ 为倒数第二次共同 CPTP 控制之后、该仪器之前的实际物理 $SR$ 分支。其结果算子

$$
K_\ell=\sqrt{1-\beta_{N-1}}\,P_\ell
+\sqrt{\beta_{N-1}}\,P_{1-\ell}
$$

可逆，并满足

$$
\rho_h^{\rm A}=(K_\ell\otimes I_R)
\sigma_g^{\rm A}(K_\ell\otimes I_R).
$$

选中实际分支非零、纯且系统沿 $|\ell\rangle$。只反演这个仪器结果算子，得到

$$
\sigma_g^{\rm A}
=\frac{1}{1-\beta_{N-1}}\rho_h^{\rm A}.
$$

因此该父分支也是纯乘积，系统仍沿同一指针。这一步没有反演或限制此前的 CPTP 控制。

考察兄弟历史 $h'=g(1-\ell)$。实际分支为

$$
\rho_{h'}^{\rm A}
=\frac{\beta_{N-1}}{1-\beta_{N-1}}\rho_h^{\rm A}\ne0,
$$

系统支撑仍为 $P_\ell$。理想兄弟分支如果为零，则其完整纯化与实际分支的内积为零；如果非零，则理想秩一读取使其系统支撑为 $P_{1-\ell}$，同样与实际系统支撑正交。因此无论哪一种情况，都有

$$
\delta_{h'}=\langle y_{h'},x_{h'}\rangle=0.
$$

但实际兄弟分支非零，使 $h'$ 成为活历史，违反前缀等号条件对每个活历史给出的 $|\delta_{h'}|>0$。矛盾。

这排除了当前参数条件下任何达到 $U(E,f)$ 的协议。前面已经证明允许类的最大值存在，故其最优值严格小于 $U(E,f)$。与充分性结合，得到完整低末次错误率等号分类。证毕。

**推论 32.2（全部参数域的 CPTP 等号分类与最小记忆维数）。** 对任意有限 $N\ge2$ 和全部参数 $\beta_t\in[0,1]$，令

$$
f=\beta_N,
\qquad E=1-\prod_{t=1}^{N-1}(1-\beta_t).
$$

在定义 27.1 的系统 CPTP 与惰性参考任务中，完整等号条件为

$$
\begin{aligned}
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)=U(E,f)
\quad\Longleftrightarrow\quad
&\beta_N=0\ \text{或}\ \beta_{N-1}=0\\
&\text{或存在 }t\in\{1,\ldots,N\}\text{ 使 }\beta_t=1.
\end{aligned}
$$

考虑允许任意共同 $SM$ CPTP 控制、额外任意有限维惰性参考 $R$、最终保留 $H_NMR$ 的可操作记忆任务。以达到定理 22.2 的 $U(E,f)$ 为目标，所需非零记忆 $M$ 的最小维数恰为

$$
d_{\min}(\boldsymbol\beta)=
\begin{cases}
1,&\beta_N=0\ \text{或}\ \beta_{N-1}=0\ \text{或某个 }\beta_t=1,\\
2,&\beta_N>0,\ \beta_{N-1}>0\ \text{且全部 }\beta_t<1.
\end{cases}
$$

当 $N=1$ 时，在全部参数域有 $T_1^{\mathrm{ref,CPTP}}(\beta_1)=U(0,\beta_1)=\beta_1$，且 $d_{\min}=1$。这些结论分类的是达到可操作记忆最优值所需的记忆维数，不断言任意中间系统 CPTP 控制与系统幺正控制的一般最优值相等。

证明。$f=0$ 时，定理 22.3 的无参考共同系统幺正构造已经达到 $U(E,0)$，并由定理 22.2 的上界确定等号。$0<f<1/2$ 时应用定理 32.1；$1/2\le f\le1$ 时应用定理 31.2。三个互不重叠的参数范围穷尽 $f\in[0,1]$，给出所述完整等号条件。

当 $\dim M=1$ 时，共同 $SM$ CPTP 控制就是系统 CPTP 控制，任意额外惰性参考与最终输出恰对应 $T_N^{\mathrm{ref,CPTP}}$。因此，在等号条件的补集上，严格不等式排除了维数一的记忆达到 $U$。定理 22.2 用一个初始为 $|0\rangle$ 的可操作记忆量子比特、末次前的一次 SWAP 及此前共同实反馈达到 $U$，不需要额外参考，所以维数二足够。在等号域，定理 22.3 的无参考系统幺正构造已以维数一达到；非零记忆的维数不能小于一。单步值由定理 27.2 与定理 22.2 给出，指针输入以维数一的记忆达到。这证明全部维数结论。证毕。

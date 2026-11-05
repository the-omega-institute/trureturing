# FIB 二阶关系完成·量子信道续卷：最优 NOT 与干净记录

本卷承接[二阶关系完成原卷](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)，收录 v9 的量子信道增补 §§118–119；保留本分支的原节号与命题编号。它与既有[混合循环观测续卷](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION_CONTINUATION.md)是不同主题分支，两卷各自的 §§118–119 须以卷名区分。

下文定理 69.2、定义 109.1、定理 109.2 均指二阶关系完成原卷。量子载体、共同记录与可执行 oracle 是显式合同；内容为普通数学证明，未新增 Lean 或硬件验证。

<a id="v9-not"></a>

## 118. 未知单份 qubit 的最优 NOT 与一般维数校正

本节消费定理 69.2 的完全正障碍，不重命名为另一种“取反”。基位翻转
$X$、效果补集 $I-E$、相干反射 $I-2P$、已可执行门的逆 $U^\dagger$，
以及未知纯态的正交化是不同任务。整体负号不改密度矩阵，子空间负号可为相对相位；
$X|+\rangle=|+\rangle$ 已说明固定 $X$ 不是普适正交化。
若 $|\psi\rangle=a|0\rangle+b|1\rangle$，正交向量可取
$-\bar b|0\rangle+\bar a|1\rangle$，其中的共轭不能删去。

**定理 118.1（确定单份普适 NOT 的 worst-case 保真度为 $2/3$）。**
对所有 qubit CPTP 映射 $\Phi$ 定义目标重叠

$$
F_{\min}(\Phi)=\inf_{\|\psi\|=1}
 \operatorname{tr}[(I_2-\rho_\psi)\Phi(\rho_\psi)],
\qquad \rho_\psi=|\psi\rangle\langle\psi|.
$$

则 $\sup_\Phi F_{\min}(\Phi)=2/3$，由

$$
\Phi_*(M)=\frac{2\operatorname{tr}(M)I_2-M}{3}
 =\frac{XMX+YMY+ZMZ}{3}
$$

达到；右式的 $X,Y,Z$ 为 Pauli 矩阵。
这是一个输入份数为一、输出份数为一、无先验纯态信息的确定任务。

**证明。** 用归一化 Haar 测度取
$\widetilde\Phi(M)=\int_{SU(2)}U^\dagger\Phi(UMU^\dagger)U\,dU$。
对每个 $\psi$，其目标重叠是原通道在 $U\psi$ 上的重叠的平均，故不小于
$F_{\min}(\Phi)$。此 twirl 仍为 CPTP，且与所有 $SU(2)$ 共轭交换。
Bloch 仿射表示中的平移向量必须被全部三维旋转固定，故为零；线性部分与全部旋转交换，
故为标量 $\lambda I_3$。因此

$$
\widetilde\Phi(M)=D_\lambda(M)
 =\lambda M+(1-\lambda)\operatorname{tr}(M)I_2/2.
$$

约定单位 Bell 向量 $|\Omega_2\rangle=(|00\rangle+|11\rangle)/\sqrt2$，
归一化 Choi 为
$C_\lambda=\lambda|\Omega_2\rangle\langle\Omega_2|+(1-\lambda)I_4/4$。
其 Bell 方向特征值为 $(1+3\lambda)/4$，正交三方向为 $(1-\lambda)/4$，
故 CP 当且仅当 $-1/3\le\lambda\le1$。
纯输入的正交目标重叠为 $(1-\lambda)/2\le2/3$。
于是原通道的 worst-case 值也不能超过 $2/3$。
取 $\lambda=-1/3$，Pauli 共轭平均给上述 $\Phi_*$，对每个纯输入均达到 $2/3$。∎

此结论的外部归属是 Bužek–Hillery–Werner，
[*Optimal Manipulations with Qubits: Universal NOT Gate*, quant-ph/9901053](https://arxiv.org/abs/quant-ph/9901053)。
其摘要的 $(N+1)/(N+2)$ 在 $N=1$ 给 $2/3$；这里的单输入证明独立给出该常数。
这是纯态目标重叠的优化，不是把不完全正的理想 NOT 当成有物理联合参考扩展的信道。
可实现的 $\Phi_*$ 自身当然对任意参考完全正。

**命题 118.2（一般 $d$ 的单位 Bell Choi 负特征值）。**
对 $d\ge2$，定义迹保持正映射

$$
\mathcal N_d(M)=\frac{\operatorname{tr}(M)I_d-M}{d-1},\qquad
|\Omega_d\rangle=d^{-1/2}\sum_{j=1}^d|j,j\rangle.
$$

则

$$
(\mathcal N_d\otimes\operatorname{id})(|\Omega_d\rangle\langle\Omega_d|)
 =\frac{I_{d^2}/d-|\Omega_d\rangle\langle\Omega_d|}{d-1}.
$$

Bell 方向的特征值是 $-1/d$，其余方向为 $1/[d(d-1)]$。

**证明与归一化校正。** Bell 方向直接计算为
$(1/d-1)/(d-1)=-1/d$。因此上面这个映射的负特征值确实是 $-1/d$；
不能将它更正为 $-1/[d(d-1)]$，后者只在 $d=2$ 与它相等。
若把算子 $I_{d^2}/d-|\Omega_d\rangle\langle\Omega_d|$ 的负值
误写成 $-1/d$，则在 $d>2$ 错误。该未除以 $d-1$ 的算子负值为
$-(d-1)/d$。两者都非正。对正输入，$\operatorname{tr}(M)I_d-M\succeq0$，
并且分母使迹保持，故所述正但非 CP 性成立。
对纯态，输出为其 $(d-1)$ 维正交补上的均匀态；$d=3$ 时不是一个唯一纯射线。∎

<a id="v9-clean-record"></a>

## 119. 带置换相位的纯记录消费者与参考稳定误差

沿用定义 109.1 的索引次序：内积第一项共轭线性，退相干因子写成
$G_{xy}=\langle\eta_y,\eta_x\rangle$，不是其共轭。
下面是定理 109.2 在已有目标置换上的消费者。

**定理 119.1（酉性与指定相位是两个判据）。**
给有限正交基 $\{|x\rangle\}$、其置换 $f$、实相位 $\phi_x$ 及单位纯记录
$\eta_x$。给定同一个等距实现

$$
V|x\rangle=e^{i\phi_x}|f(x)\rangle\otimes|\eta_x\rangle,
\qquad F_\phi|x\rangle=e^{i\phi_x}|f(x)\rangle.
$$

则其约化通道满足

$$
\Phi(|x\rangle\langle y|)
 =e^{i(\phi_x-\phi_y)}G_{xy}|f(x)\rangle\langle f(y)|.
$$

$\Phi$ 是某个酉通道，当且仅当 $\operatorname{rank}G=1$。
这等价于存在单位记录 $\eta$ 与相位 $\vartheta_x$，使
$\eta_x=e^{i\vartheta_x}\eta$；此时系统酉门的相位为
$\phi_x+\vartheta_x$。对于已经指定的目标 $F_\phi$，则

$$
\Phi=\operatorname{Ad}_{F_\phi}\quad\Longleftrightarrow\quad
G_{xy}=1\quad\text{对所有 }x,y.
$$

**证明。** 对矩阵单位取环境偏迹得到公式。
$G$ 的秩等于这些环境向量张成的维数（也见定理 109.2），秩一当且仅当全部共线，
于是联合输出可直接分离为所述带修正相位的系统酉门和同一个环境向量。
反过来若约化通道为酉，每个 $(|x\rangle+|y\rangle)/\sqrt2$ 的约化输出纯度为一。
其二维密度块的行列式为 $(1-|G_{xy}|^2)/4$，故每对记录内积模为一。
Cauchy–Schwarz 等号给全部记录共线。
最后比较全部矩阵单位与 $\operatorname{Ad}_{F_\phi}$ 即得全一判据。∎

例如 $\eta_0=\eta,\eta_1=-\eta$ 的环境纯密度完全相同，却给系统额外的 $Z$。
因此“没有可区分的环境密度”不足以认定已经实现某个指定相位的门。
不相关的各次实现也不能只凭各自纯密度拼出这个共同 Gram 矩阵。

**推论 119.2（一致向量误差没有维数损失）。**
若同一环境中存在一个单位 $\eta$，使
$\sup_x\|\eta_x-\eta\|\le\varepsilon$，则

$$
\|V-(F_\phi\otimes|\eta\rangle)\|_{\rm op}\le\varepsilon,
\qquad
\|\Phi-\operatorname{Ad}_{F_\phi}\|_\diamond\le2\varepsilon.
$$

这里 diamond 范数不除以二，误差对任意未触动外部参考有效。

**证明。** 将带参考的单位输入写成 $\sum_x|x\rangle r_x$，其中
$\sum_x\|r_x\|^2=1$。差输出范数的平方为
$\sum_x\|r_x\|^2\|\eta_x-\eta\|^2\le\varepsilon^2$，因为不同 $f(x)$ 正交。
两个单位等距输出的纯密度之迹范数差至多其向量距离的二倍；偏迹收缩且混合输入可凸分解。
允许任意参考取上确界便得通道界。该证明不把各记录独立选相位后再比较；
若只在调整 $\vartheta_x$ 后接近，比较的目标也须同时调整系统相位。∎

**相位 kickback 的合同。** 对可执行的干净可逆 oracle
$O_f|x,c\rangle=|x,c\oplus f(x)\rangle$，另供目标位 $| -\rangle$ 时，
$O_f(|x\rangle| -\rangle)=(-1)^{f(x)}|x\rangle| -\rangle$。
于是 AND 给 $CZ$，NAND 给 $-CZ$，NOR 给
$D_{00}=I-2|00\rangle\langle00|$。整体负号只在未额外受控的酉通道中抵消；
这并未从布尔图或一般有丢弃记录的 NAND 输出通道构造出 oracle。
相关的信道球见[相干重建 §37](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md#v9-nand)，
实际记录与完整返回见[Waves VI §§112–113](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md#v9-labels)。

# AURIC FIB ATOM 相干重构续卷：NAND 信道、反射与完整门合同

本卷承接[相干重构原卷](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)，收录 v9 增补的 §§37–41；保持各节及命题编号，原卷相应锚点继续提供入口。

载体、编码、相位、记录及控制权限均沿正文显式合同。下文所称原卷 §§7–8 指相干重构原卷；本卷内部的 §§37–41 互相引用保持原意。全部内容为普通数学证明，未新增 Lean 或硬件验证。

<a id="v9-nand"></a>

## 37. v9 门合同、可逆 NAND 与完整确定信道球

本节至 §41 是普通数学消费者：指定复 Hilbert 载体、张量接口、编码等距
$J$、允许的门及其放置、辅助制备、完整记录处理与误差范数都是合同输入。
原卷 §8 的原生控制、单参考编译器及仪器稳定性定理仍由原有 owner 供应。
“通用”须分别说明：有限维 $PU(d)$ 中稠密、每个目标都有精确有限字，或已知
$m$ 位源电路 $C$ 的可扩展实现 $V_CJ_m=J_mC$。最后一个恒等式含干净辅助位，
并可张量任意未触动参考；单看某个计算基输入的真值表不足以替代它。

有限个固定角度门在有限个位置上的全部有限字只有可数个，不能精确覆盖不可数的
$PU(2^m)$。任意实角度控制的精确结论与有限固定门集的任意精度逼近不是同一断言。
普通 $\operatorname{Ad}_U$ 中可忽略整体相位；把未知黑盒变为受控门时，相位会变成相对相位，
故不据此免费附加 coherent control。单一门*类型*在多条线上的放置和一只固定位置矩阵的幂也不同。

**命题 37.1（保留输入的可逆 NAND）。** 令 $f(a,b)=1\oplus ab$。三位门

$$
N|a,b,c\rangle=|a,b,c\oplus f(a,b)\rangle=X_cCCX|a,b,c\rangle
$$

为置换酉且 $N^2=I$；$c=0$ 时输出 NAND 并保留输入。

证明。$X_c$ 与受 $ab$ 控制的目标翻转交换，且各自平方为一；或直接在每个固定
$(a,b)$ 的两态目标块上计算。四维输入到二维输出的裸 NAND 不可能是酉同构。
纯可逆布尔置换只有实的 $0,1$ 矩阵，不自行提供任意复相位。
若线性等距将 $|0\rangle|0\rangle,|1\rangle|0\rangle$ 分别送到
$|00\rangle,|11\rangle$，则它将 $|+\rangle|0\rangle$ 送到
$(|00\rangle+|11\rangle)/\sqrt2$，而非 $|+\rangle|+\rangle$，故不能复制所有未知态。∎

**定理 37.2（NAND 真值表的全部 CPTP 扩展）。**
按输入顺序 $\mathcal J=(00,01,10)$、$b=11$ 和输出顺序 $(0,1)$。
全部满足

$$
\Phi(|j\rangle\langle j|)=|1\rangle\langle1|\ (j\in\mathcal J),\qquad
\Phi(|b\rangle\langle b|)=|0\rangle\langle0|
$$

的 CPTP 映射 $M_4\to M_2$，唯一由闭单位球
$z=(z_j)\in\mathbb C^3,\ \|z\|\le1$ 参数化为

$$
\Phi_z(X)=
\begin{pmatrix}
 X_{bb}&\sum_j\overline{z_j}X_{bj}\\
 \sum_j z_jX_{jb}&\sum_jX_{jj}
\end{pmatrix}.
\tag{37.1}
$$

**证明。** 取一个 Stinespring 等距 $V$。纯约化输出迫使
$V|j\rangle=|1\rangle e_j$、$V|b\rangle=|0\rangle f$，其中记录归一化。
$V^\dagger V=I$ 给 $e_j$ 两两正交；不同系统输出已使 $b$ 列与它们正交，
不要求 $f\perp e_j$。内积第一项共轭线性，置
$z_j=\langle f,e_j\rangle$，Bessel 不等式给 $\sum_j|z_j|^2\le1$。
对每个矩阵单位取环境迹，得到 (37.1)，故无其他自由参数且参数唯一。
反之，取四个正交环境基 $e_j,e_4$ 并设

$$
f=\sum_j\overline{z_j}e_j+\sqrt{1-\|z\|^2}\,e_4.
$$

上面的 $V$ 列仍正交且归一化，故为等距；偏迹实现 (37.1)，是 CPTP。
这也证明边界 $\|z\|=1$ 可删去未用的第四环境维。∎

**推论 37.3（码相干、entanglement breaking 与最小 Kraus 秩）。**
令 $r=\|z\|$。若 $r>0$，定义

$$
|u\rangle=r^{-1}\sum_j\overline{z_j}|j\rangle,
\qquad \mathcal C_z=\operatorname{span}\{|u\rangle,|b\rangle\}.
$$

在此二级码上，$\Phi_z$ 是逻辑位翻转再作相干因子为 $r$ 的退相干：

$$
\Phi_z(|u\rangle\langle u|)=|1\rangle\langle1|,\quad
\Phi_z(|b\rangle\langle b|)=|0\rangle\langle0|,\quad
\Phi_z(|u\rangle\langle b|)=r|1\rangle\langle0|.
$$

它当且仅当 $z=0$ 为 entanglement breaking（EB）。其 Choi 秩、最小 Kraus 数、
纯初始环境的最小 Stinespring 维数都是

$$
\begin{cases}4,&r<1,\\3,&r=1.\end{cases}
$$

特别地，三维最小环境实现必有一个完美可传输的码 qubit。

**证明。** 对 (37.1) 代入码的矩阵单位得到三个公式；$r=1$ 时
$V|u\rangle=|1\rangle f$、$V|b\rangle=|0\rangle f$，记录完全一致。
$z=0$ 时通道先测量 $\{|b\rangle\langle b|,I-|b\rangle\langle b|\}$ 再制备
$|0\rangle$ 或 $|1\rangle$，故为 EB。
$r>0$ 时在码与一个参考 qubit 上输入
$(|u,0\rangle+|b,1\rangle)/\sqrt2$。输出的偏转置在
$\operatorname{span}\{|0,0\rangle,|1,1\rangle\}$ 中有特征值 $\pm r/2$，
另两非零特征值为 $1/2,1/2$，所以仍有纠缠，不是 EB。

标准环境 Gram 矩阵（元素为 $\langle g_a,g_b\rangle$）为

$$
G_{\rm env}=\begin{pmatrix}I_3&\bar z\\z^{\mathsf T}&1\end{pmatrix}.
$$

Schur 补为 $1-r^2$，故其秩在内点为四、球面为三。
未归一化 Choi 采用输入在前的约定
$C_\Phi=\sum_{a,c}|a\rangle\langle c|\otimes\Phi(|a\rangle\langle c|)$。
在正交标记 $|j\rangle|1\rangle,|b\rangle|0\rangle$ 张成的四维子空间上，
其矩阵是 $G_{\rm env}^{\mathsf T}$，其余方向为零，故秩相同。
Choi 的正谱分解把各向量 reshape 成 Kraus 算子，给秩个 Kraus；
反向任意 $k$ 个 Kraus 的 Choi 是 $k$ 个秩一向量外积之和，故至少需该秩。
把 Kraus 标签作纯环境基给最小等距维数，完成证明。∎

这些是同一个真值表容许的所有未知输入信道，不是裸布尔图天然选中了某个 $z$。
完美码的制备依赖已标定的 $z$；四维到二维通道不因保留一个码 qubit 而成为全输入可逆。
[SECOND §119](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION_QUANTUM_CHANNEL_CONTINUATION.md#v9-clean-record)
给另行供应干净 oracle 时的 NAND/NOR 相位 kickback；
[Selection §28](AURIC_FIB_ATOM_SELECTION_CALCULUS.md#v9-pp)
给裸 $\Sigma$ 的经典 pp 障碍，二者不可混称。

<a id="v9-reflections"></a>

## 38. 固定反射的稠密范围与目标依赖的反射分解

**定理 38.1（一只固定门、两只固定 involution 的限制）。**
$d\ge2$ 时，一只固定 $U\in U(d)$ 的幂闭包不可能给整个 $PU(d)$。
两只任意固定酉 involution $R^2=S^2=I$ 的投影群闭包也不可能给整个 $PU(d)$。

证明。循环群闭包仍为交换群，因交换子连续；$PU(d)$ 非交换。
对第二个断言，以 $T=RS$，关系 $RTR=T^{-1}$ 将每个词约成
$T^n$ 或 $RT^n$。置 $K=\overline{\langle T\rangle}$，全闭包是 $K\cup RK$。
在投影群中仍有同样结构。若覆盖连通的 $PU(d)$，闭交换子群 $K$ 的指数至多二。
若指数二，另一闭陪集使 $K$ 同时开；连通性迫使它等于全群，与非交换性矛盾。
指数一也直接矛盾。∎

例如 $\langle u,v\rangle=\cos\theta$、$0<\theta<\pi/2$ 时，
$R_u=I-2|u\rangle\langle u|$，积 $R_vR_u$ 在 $(u,(v-\cos\theta u)/\sin\theta)$
基下是角 $2\theta$ 的实旋转，在其正交补为恒等；
$\theta/\pi$ 无理只令其幂稠密覆盖这一圆，并不覆盖一般酉群。
这些结论不限制同一门类型在不同线对上的多个放置。

**命题 38.2（三只固定 qubit involution 足够稠密）。**
取 $\alpha/\pi$ 无理，并固定

$$
R_0=Z,\quad R_1=\cos\alpha Z+\sin\alpha X,\quad
R_2=\cos\alpha Z+\sin\alpha Y.
$$

三者自伴、平方为一，所生成群在 $PU(2)$ 中稠密。

证明。Pauli 反交换给 involution 性，且
$R_1R_0=e^{-i\alpha Y}$、$R_2R_0=e^{i\alpha X}$。
无理角的整数倍在圆上稠密，故闭包含全部连续 $X,Y$ 旋转。
Euler 分解给 $SU(2)$，因此投影闭包为 $PU(2)$。∎

由定理 38.1，“三”只是在固定单 qubit、固定位置、无额外控制／辅助资源、
以 involution 为生成元的*稠密*通用合同中的最小数；可数有限字不精确覆盖全部门。
若另供各数据 qubit 上的这些门和连通线路上的可放置 $CZ$，
局部逼近加既有局部门／CNOT 电路分解给通常多 qubit 逼近通用性。
这是额外的放置与纠缠资源，不由三只单 qubit 门推出。

**定理 38.3（每个 $SU(d)$ 目标至多 $2(d-1)$ 个秩一反射）。**
$d\ge2$ 时，每个 $U\in SU(d)$ 可精确写成至多 $2(d-1)$ 个
$R_w=I-2|w\rangle\langle w|$ 的积，但反射方向依赖目标。

证明。酉对角化 $U=V\operatorname{diag}(e^{i\theta_1},\ldots,e^{i\theta_d})V^\dagger$，
选 $\theta_d=-\sum_{j<d}\theta_j$ 模 $2\pi$。在每个 $(j,d)$ 平面置

$$
u_j=(e_j+e_d)/\sqrt2,\qquad
v_j=(e_j+e^{i\theta_j}e_d)/\sqrt2.
$$

直接乘二维矩阵得到
$R_{u_j}R_{v_j}=\operatorname{diag}(e^{i\theta_j},e^{-i\theta_j})$，
并在该平面外为恒等。这些乘积均对角，故全部相乘得到目标对角矩阵。
用 $V$ 共轭每个反射即得所需分解；零角的成对反射可省略。∎

对于普通酉通道可先选一个 $SU(d)$ 代表；一般矩阵整体相位须另记。
这里的“可编程”是另供任意目标依赖反射方向的理想接口，不是固定未知量子程序态驱动的
通用处理器构造，也没有从有限图、布尔 NAND 或一个固定反射导出这个连续资源。

<a id="v9-native-bus"></a>

## 39. 原生返回供应、控制菜单与另供的共享记录总线

**原生供应的准确消费。** 原卷 §8.1 的 $H_1,H_2,H_3$ 是 Hamiltonian，门为
$R_j(t)=e^{-itH_j}$；五条耦合边不等于金字塔的全部几何棱。
[Legal Gates §13.1](FIB_LEGAL_GATES_STATE_MACHINES_AND_SHOR_READOUT.md#13-a-clean-encoded-circuit-compiler-inside-the-existing-legal-pulse-model)
已经证明 $J_2|ab\rangle=|a0b\rangle$ 下

$$
D=R_2(\pi),\quad DJ_2=J_2D_{00},\quad
D_{00}=\operatorname{diag}(-1,1,1,1),\quad
S=R_3(\pi/2)R_1(\pi/2),\quad S^\dagger DSJ_2=J_2CZ.
$$

码逻辑顺序为 $(00,01,10,11)$，对应物理模式 $(0,3,1,13)$。
$S$ 在码上为 $-X\otimes X$；分隔位可在中途激发但精确返回。
这些是全码等距恒等式，故包括外部参考；不是删除空分支。
$D$ 在额外合法态 $|010\rangle$ 上为负一，不能把四维码矩阵当成全五维恒等式。
$D_{00}|++\rangle$ 的二维系数矩阵秩为二，确为纠缠态。

单一固定 $H_1+H_2+H_3$ 的等待不等于独立寻址。
原卷 §8.3 已给任意实角度的三控制精确群 $D_5SO(5)D_5^\dagger$，
$D_5=\operatorname{diag}(1,i,i,i,1)$；原卷 §8.6 已给另供
$S_*=e^{i\pi P_{13}/2}$ 后的精确 $SU(4)\oplus1$、$SU(5)$ 与
$\{V\in U(5):\det V\in\{1,i,-1,-i\}\}$。
这些是现有供应而非本节的新发现；固定 $S_*$ 的四次幂为一，不等于免费的连续相位源。
仅在码上有局部 $X$ 旋转与 $CZ$ 时，换基
$D_C=\operatorname{diag}(1,i,i,1)$ 使它们同时为实正交矩阵：
对两个 $-iX$ 生成元直接共轭得实反对称矩阵，$CZ$ 仍为实对角。
所以“能纠缠”本身不提供全部复控制。
完整五维菜单与[单 Y 地址的可扩展码编译器](FIB_LEGAL_GATES_SINGLE_REFERENCE_AND_CERTIFIED_READOUT.md#3-a-constructive-polynomial-compiler-with-one-second-quadrature-address)
是不同资源合同，后者的 $7,21,42$ 常数与精确成本仍由该 supplier 承担。

**定理 39.1（另行供应共同相干 bus 的反射相位）。**
在不同数据系统上给投影 $Q_A,R_B$，另供同一个 bus qubit 上可调用的条件门

$$
A=C_{Q_A}(X)=(I-Q_A)\otimes I+Q_A\otimes X,\qquad
B=C_{R_B}(Z)=(I-R_B)\otimes I+R_B\otimes Z.
$$

省略旁观数据的恒等张量因子。则在整个数据加 bus 空间，

$$
ABAB=(I_{AB}-2Q_A\otimes R_B)\otimes I_{\rm bus}.
\tag{39.1}
$$

bus 可以未知，且可与数据或任意外部参考纠缠；仍精确恢复。
若 bus 另初始化为 $|0\rangle$，则三次字 $ABA$ 已在这个制备切片实现同一个数据门并返回 bus。

**证明。** $Q_A$ 和 $R_B$ 作用于不同数据因子，联合谱扇区由 $q,r\in\{0,1\}$ 标记。
在每扇区，四次字作用为 $X^qZ^rX^qZ^r=(-1)^{qr}I$；
把谱投影求和即得全空间算子恒等式 (39.1)，自动兼容所有参考与纠缠。
在制备 bus $|0\rangle$ 的切片，$X^qZ^rX^q|0\rangle=(-1)^{qr}|0\rangle$，给三次结论。
若 $Q_A,R_B$ 均非零且非恒等，在各自核与像中选单位向量；
两者等权叠加的系数矩阵经数据门后为
$\tfrac12\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$，秩二，故门能纠缠。∎

这不是全局最少调用次数定理。共同可相干访问的 bus 与条件反射是显式新增资源，
并不由任意 Stinespring 扩张或实际仪器的全维补全推出。
[Waves VI §113](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md#v9-full-completion)
反而说明忠实全十维补全不可能保持整个原六维码记录空间。
本节的 bus 恒等式没有改写那个原返回合同。

<a id="v9-instrument-return"></a>

## 40. 坐标返回为什么不等于实际仪器逆

这里直接消费[Original Control Instrument Stability 定理 12.1](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md#12-scalar-triangular-controls-and-survival)，
不把已有三角反例另算新结果。给 $0<c<1/2$、$a=c/2$、$t\in[0,1]$，该定理以

$$
\begin{aligned}
C_n(t)&=\frac c2\sum_{j=0}^{n-1}\max(0,\min(t-j/n,(j+1)/n-t)),\\
k_n(t)&=a-C_n(t)/(2-t),\\
h_c[k]&=\max(k',0)/k+\max(-k',0)/(c-k),\quad
S_c[k](t)=\exp\left(-\int_0^t h_c[k](u)\,du\right)
\end{aligned}
$$

给出每个 $n\ge1$ 的原生控制，且同时有

$$
k_n(0)=k_n(1)=a,\quad \|k_n-a\|_\infty\le c/(4n),\quad
\int_0^1|k_n'|\le3c/4,\quad
\int_0^1|k_n'|^2\le9c^2/16,
$$

但 $S_c[k_n](t)=1-t/2$，而等待 $k=a$ 的生存率恒为一。
源定理 (ST.8) 在上升／下降 tent 腿上分别给
$k_n'=-(c-k_n)/(2-t)$ 与 $k_n'=k_n/(2-t)$，
所以其*实际* hazard 在角点外为 $1/(2-t)$，积分解释了固定的终端差 $1/2$。
这同时保留端点、趋于零的一致坐标误差、有界长度与平方速度作用；
分段数为 $2n$，没有跨 $n$ 的共同分段上限，作用也不是已标定物理能量。

因此这些坐标条件不足以推出同一个仪器的返回是逆、成功率趋一或记录可擦除。
这与 §39 的全码酉等距返回不矛盾：后者是直接的算子恒等式，
前者只控制坐标轨迹而真实损失仍被完整仪器保留。
静态描述同样保留操作次序；原卷命题 8.7 的
$[H_1,H_2]=E_{12}-E_{21}$ 及两种顺序分别到 $-i|2\rangle,-i|1\rangle$
仍是原供应，[单参考 §8](FIB_LEGAL_GATES_SINGLE_REFERENCE_AND_CERTIFIED_READOUT.md#v9-word-error)
给有序编译字的误差与最终泄漏消费者，不把“没有外时钟”改写为干预交换。

<a id="v9-synthesis"></a>

## 41. 完整十五组的源对应与资源限定综合

本表固定 v9 全部科学条款的去向。现有供应与新消费者分列，避免把已证编译／控制结论
重复申报，也不让不同载体或记录合同相互替代。项目前提的比较点是
`4e8c143bd4606f91c57edda1e5215345432406e2`；本增补不依赖稿件中的文件数或提交数。

| 组 | 完整条款与现有供应 | 本次有效增量或结论边界 |
| --- | --- | --- |
| 1 | 门协议、稠密／精确／可扩展合同；原卷 §§7–8、Legal Gates §§11–13 | §37 的载体、编码、放置、辅助、记录、参考、可数性与黑盒相位合同 |
| 2 | 五模式与非空 NOR；[Selection §19](AURIC_FIB_ATOM_SELECTION_CALCULUS.md#十九共享端口删减二元分类与有限任务适配) | Selection §28 的裸模板 AND 封闭 pp 障碍；保留非空附加资源与成功／失败概率 |
| 3 | 可逆布尔 oracle 与 CPTP 表示；原卷 §7 | §37 的完整 NAND 球、共轭约定、码 qubit、EB 当且仅当零、秩 $4/3$ |
| 4 | 完美未知态 NOT 非 CP；[SECOND §69](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md#69-四种取反与完全正边界) | [SECOND §118](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION_QUANTUM_CHANNEL_CONTINUATION.md#v9-not) 的最优 $2/3$；一般 $d$ 单位 Bell 负值为 $-1/d$，见其直接计算，不能改为 $-1/[d(d-1)]$ |
| 5 | 固定字与可控反射不同 | §38 的一／两生成元障碍、三只固定 qubit involution 稠密性、目标依赖的 $2(d-1)$ 精确分解 |
| 6 | 原生合法性、分隔位返回与五脉冲 CZ；Legal Gates §13.1 | §39 按逻辑／物理顺序消费原等距恒等式；不作空分支后选择，不混淆码与全五维 |
| 7 | [Single Reference §§1–3](FIB_LEGAL_GATES_SINGLE_REFERENCE_AND_CERTIFIED_READOUT.md#3-a-constructive-polynomial-compiler-with-one-second-quadrature-address) 的 $CY=7$、$SWAP=21$、成本 (3.2) 与 $O(mG)$ 编译 | 保留原供应：路由量子态后反路由，单一固定 Y 数据地址，任意实角度及外部参考；只相对已知源电路计费 |
| 8 | Legal Gates §11.1 的 $A=Z_{\rm par}K$；Single Reference §3.2 | [Single Reference §7](FIB_LEGAL_GATES_SINGLE_REFERENCE_AND_CERTIFIED_READOUT.md#v9-antiunitary) 对随机、反馈、正概率后选择给状态距离 $\ge1/2$；确定通道给 half-diamond $\ge1/2$ |
| 9 | 原卷 §§8.3、8.6 的精确 $SO(5)$／$SU(5)$ 与固定相位行列式群 | §39 保留独立控制与额外 $S_*$ 资源，解释仅有纠缠仍可在实帧内；不移植为同一可扩展接口 |
| 10 | 原卷 §8.7 的次序反例；编译器全码恒等式 | Single Reference §8：算子误差 $\sum\epsilon_j$、unhalved diamond $2\sum\epsilon_j$、参考稳定最终泄漏 $(\sum\epsilon_j)^2$ |
| 11 | [Waves VI §72.1](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md#72-原对象完整联合分布与比较域) 的实际 $K_j,A_j,U,W,\xi,e,f$ | [Waves VI §112](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md#v9-labels) 的擦除不可恢复界及带标签随机酉字；不推可选标签、逆门或 qutrit 通用 |
| 12 | SECOND §109 的共同 Schur 记录正性与秩 | [SECOND §119](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION_QUANTUM_CHANNEL_CONTINUATION.md#v9-clean-record) 的置换／纯记录相位判据：某酉 iff rank $G=1$，指定目标 iff 全 $G_{xy}=1$；一致记录向量误差给 diamond $2\epsilon$ |
| 13 | Waves VI §§106–107 的全五输入、十维完整返回，所有历史与终端结果 | [Waves VI §113](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md#v9-full-completion) 对每个忠实补全给至少二维全泄漏子空间；不把六维制备切片当全输入门 |
| 14 | 共享相干记录不是原仪器自动供应 | §39.1 在明确另供的条件 $X/Z$ bus 上给四调用全空间恒等式、未知／纠缠 bus 恢复及制备切片三调用；无最少调用主张 |
| 15 | Instrument Stability §12.1 的完整三角反例；原生返回与可扩展编译供应 | §40 直接消费该反例；本节综合保留全部资源、静态次序与有限观察者权限，不导出基础公理或硬件 |

**可扩展结论的准确形式。** 供应合法无相邻 $11$ 载体
$\mathcal K_n$（$\dim\mathcal K_n=F_{n+2}$，$d_0=1,d_1=2$）、
$J_m|b_1\ldots b_m\rangle=|b_1\,0\,b_2\ldots0\,b_m\rangle$、
每个位置独立寻址的可调实角度 $X$ 脉冲及其逆、一个固定数据位置的 Y 象限、
准备为零的分隔位、有限有序端口和计算基读出。
对给定源电路 $C$（$R_x,R_y,CZ$ 基），Single Reference 定理 3.1 给

$$
V_CJ_m=J_mC,\qquad
L\le G_x+\sum_\ell(42|q_\ell-q_*|+1)
 +\sum_e(42(|a_e-b_e|-1)+5)=O(mG).
$$

全部辅助分隔位与布局在每个编译块结束恢复，且恒等式兼容任意参考。
Euler 局部门及 CNOT 分解沿原供应给已知量子电路的通用实现；
有限角度门集则须另付近似成本，误差沿 Single Reference §8 累积。
这里不声称有效合成一个任意无结构、指数多参数的目标矩阵，也不声称容错阈值。
观察者是持有上述编码、相位参考、完整记录和有限访问菜单的协议使用者；
静态表示没有抹去端口次序。这些有限理想模型不导出复 Hilbert／Born／物理时间公理，
不证明控制装置已实验实现，不作本体论或新历史优先权主张，也没有新增 Lean 或 PDF 验证。

**公开来源及实际归属。** 以下论文的 arXiv 元数据／摘要可核对所列范围；本增补的有限证明
不以未取得的全文段落为前提。

- A. Barenco，[quant-ph/9505016](https://arxiv.org/abs/quant-ph/9505016)，
  *A Universal Two--Bit Gate for Quantum Computation*：摘要明确为单一二输入二输出门的复本组成网络。
  此处只作多位置门网络的背景，不把某个辅助初始化细节归给未经核对的段落；辅助合同已在本节明供。
- A. Barenco et al.，[quant-ph/9503016](https://arxiv.org/abs/quant-ph/9503016)，
  *Elementary gates for quantum computation*：全部单 qubit $U(2)$ 门与两位 XOR 的有限电路分解，
  是原生编译器沿用的标准源接口，不是任意矩阵都有多项式短描述的主张。
- V. Bužek、M. Hillery、R. Werner，[quant-ph/9901053](https://arxiv.org/abs/quant-ph/9901053)，
  *Optimal Manipulations with Qubits: Universal NOT Gate*：未知态 NOT 不可精确实现及近似；
  SECOND §118 在单份任务中独立证明 $2/3$。
- J.-L. Brylinski、R. Brylinski，[quant-ph/0108062](https://arxiv.org/abs/quant-ph/0108062)，
  *Universal quantum gates*：全部局部 qudit 门加一个非 primitive（能将某积态变纠缠）两体门的通用性；
  不去掉其局部门前提。本卷用已有局部门／CNOT 供应而非仅凭“有纠缠”推出控制。
- T. Rudolph、L. Grover，[quant-ph/0210187](https://arxiv.org/abs/quant-ph/0210187)，
  *A 2 rebit gate universal for quantum computing*：改用实振幅编码可模拟量子计算，
  不反驳标准 $J_m$、全零输入与给定菜单下的反酉状态下界。

## 追加锚（本行以下为增补区）

<a id="v10-fib-kernel-rigidity"></a>

## 42. 实际全树来源核的 0/1 刚性与非正交边界

本节固定实际来源域，而不把它改写成关联字、有限切片或单一轨道。令
$T$ 是 $\alpha,\beta$ 上全部非空有限自由有序二叉树；$\langle s,t\rangle$
是保留左右次序的内部节点，并令

$$
\rho(\alpha)=\beta,
\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,
\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle .
$$

这正是 [Genealogical Fiber Transport](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.md)
和 [Source Transport Centralizer](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.md)
所使用的自由有序树与替换。唯一可读性给出构造子的单射性；后者的中心化定理还给出
$\rho$ 的单射性。下面的 $K:T\times T\to\mathbb C$ 是一个明列模型输入，满足

$$
\begin{aligned}
&K(t,s)=\overline{K(s,t)},
&&\sum_{j,k=1}^{m}\overline{c_j}c_kK(t_j,t_k)\ge0,
&&K(t,t)=1,\\
&K(\rho s,\rho t)=K(s,t),
&&K(\langle s,t\rangle,\langle u,v\rangle)=K(s,u)K(t,v).
\end{aligned}
\tag{42.1}
$$

第二行的两个等式分别对所有来源对和所有来源四元组成立；最后一个等式包括全部构造交叉项，
不是只对相同标签或相同树形成立的局部规则。正性、归一化、全比较的 $\rho$ 保留和精确乘法
都是模型输入，不由裸不确定性、信息守恒或 Read/Apply/Stop 过程推出。

**引理 42.1（只在 alpha 轨道上的二次替换恒等式）。** 对
$u_n=\rho^n\alpha$ 有

$$
\rho^2u_n=\langle\rho u_n,u_n\rangle .
\tag{42.2}
$$

**证明。** $n=0$ 时这是定义。若式 (42.2) 对 $u_n$ 成立，对两边再施加 $\rho$，
并使用 $\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle$，便得到对 $u_{n+1}$ 的式子。
这里没有把 (42.2) 当作任意 $u\in T$ 的恒等式；它只在已分类的 $\alpha$ 轨道上使用。∎

**定理 42.2（实际全树来源的精确 0/1 刚性）。** 若只保留 (42.1) 中的 Hermitian
条件、全比较 $\rho$ 保留和全部四元组的精确乘法，则对任意 $s,t\in T$，

$$
K(s,t)\in\{0,1\}.
\tag{42.3}
$$

因此定理的 0/1 结论本身不消费正性、归一化或 faithfulness；这些条件仍是原核模型的独立输入，
在下述 Hilbert 解释和忠实特例中才被消费。

**证明。** 先置
$f_n(u):=K(\alpha,\rho^n u)$，并令 $a_n=f_n(\alpha)$。由 (42.1) 的 $\rho$ 保留两次、
(42.2) 及精确乘法，

$$
\begin{aligned}
a_n
 &=K(\rho^2\alpha,\rho^{n+2}\alpha)\\
 &=K(\langle\beta,\alpha\rangle,
       \langle\rho^{n+1}\alpha,\rho^n\alpha\rangle)\\
 &=K(\beta,\rho^{n+1}\alpha)K(\alpha,\rho^n\alpha)
 =a_n^2.
\end{aligned}
$$

复数方程 $z=z^2$ 只有 $z=0,1$ 两个解，故每个 $a_n$ 都在这两个值中。因为
$\beta=\rho\alpha$，有 $f_n(\beta)=a_{n+1}$。若 $s,t\in T$，再次用两次 $\rho$ 保留、
$\rho^2\alpha=\langle\beta,\alpha\rangle$ 和精确乘法，得到递推式

$$
f_n(\langle s,t\rangle)
 =K(\beta,\rho^{n+2}s)K(\alpha,\rho^{n+2}t)
 =f_{n+1}(s)f_{n+2}(t).
\tag{42.4}
$$

对 $u$ 的自由树结构作归纳，(42.4) 与两个叶子的结论给出
$f_n(u)\in\{0,1\}$ 对所有 $n,u$ 成立。因此
$K(\alpha,u)=f_0(u)\in\{0,1\}$。

还需处理首项为 $\beta$ 的比较。对叶子，Hermitian 性、$\beta=\rho\alpha$ 和上面的结论给出
$K(\beta,\alpha),K(\beta,\beta)\in\{0,1\}$。对 $u=\langle s,t\rangle$，轨道恒等式 (42.2)
（用于 $\beta=\rho\alpha$）和两次 $\rho$ 保留给出

$$
\begin{aligned}
K(\beta,\langle s,t\rangle)
 &=K(\langle\rho\beta,\beta\rangle,
       \langle\rho^2s,\rho^2t\rangle)\\
 &=K(\rho\beta,\rho^2s)K(\beta,\rho^2t)\\
 &=K(\alpha,s)K(\alpha,\rho t)
 =f_0(s)f_1(t)\in\{0,1\}.
\end{aligned}
\tag{42.5}
$$

最后对 $s,t$ 的总节点数作强归纳。若首项是叶子，已由 (42.4) 和 (42.5) 处理；若两者
都是内部节点，精确乘法把比较化为两个严格更小的比较；若首项是内部节点而末项是叶子，
Hermitian 性把它化为已处理的叶子首项并取共轭。$0,1$ 在共轭和乘法下闭合，故得到 (42.3)。∎

**推论 42.3（忠实核必为 delta 核）。** 在完整输入 (42.1) 下，若核的 GNS/核商表示
$\eta:T\to H_K$ 对来源标签忠实，即 $\eta(s)=\eta(t)$ 蕴含 $s=t$，则

$$
K(s,t)=\delta_{s,t}
\qquad(s,t\in T).
\tag{42.6}
$$

**证明。** 正性和 Hermitian 性按本卷 §§6、15.2 的核商构造给出
$K(s,t)=\langle\eta(s),\eta(t)\rangle$，而归一化给 $\|\eta(s)\|=1$。由定理 42.2，
$K(s,t)$ 只能为 $0$ 或 $1$。若它为 $1$，则

$$
\|\eta(s)-\eta(t)\|^2=2-K(s,t)-K(t,s)=0,
$$

所以忠实性迫使 $s=t$；反向由归一化得到 $K(s,s)=1$。∎

**命题 42.4（精确乘法撤去后的全域边界）。** 保留全树 $T$、$\rho$、Hermitian 性、正性和
归一化，但不要求精确乘法。则对任意 $c\in[0,1]$

$$
K_c(s,t):=c+(1-c)\delta_{s,t}
\tag{42.7}
$$

是一个全域核，且保持 $\rho$。$c=0$ 给 delta 核，$c=1$ 给全 $1$ 核；当
$0<c<1$ 且取 $s\ne u,t\ne v$ 时，

$$
K_c(\langle s,t\rangle,\langle u,v\rangle)=c
\ne c^2=K_c(s,u)K_c(t,v),
$$

所以 (42.7) 正好显示取消精确构造乘法后出现的非正交连续边界。
两个端点都仍满足精确乘法：delta 核使用构造子的单射性，全 $1$ 核使用 $1=1\cdot1$；
全 $1$ 核不忠实。

**证明。** $\rho$ 的单射性给 $\delta_{\rho s,\rho t}=\delta_{s,t}$。任意有限 Gram 矩阵可写成
$cJ+(1-c)G_\delta$，其中 $J$ 是全 $1$ 矩阵，$G_\delta$ 是标准基向量的 Gram 矩阵；
两者半正定，故 (42.7) 半正定，且 Hermitian、对角归一。最后的四元组取值直接代入，
并在两个子比较都不相同时得到 $c\ne c^2$。当 $0<c<1$ 时，
$\eta_c(s)=\sqrt c\,e_0+\sqrt{1-c}\,e_s$ 在
$\mathbb C e_0\oplus\ell^2(T)$ 中给出 (42.7) 的忠实 Gram 表示；
所以这确实是忠实的非正交边界，而不是标签被合并的伪例。∎

**关系模型的边界。** (42.3) 约束的是明列来源核的数值。$\alpha,\beta$ 首先是树中的
语法标签；来源相位是将 Hilbert 代表改作 $\eta(t)\mapsto e^{i\theta_t}\eta(t)$ 的规范选择，
不由标签本身或 (42.1) 产生物理相位。Hilbert 数学叠加只表示核商中的有限复线性组合；它不授予
原生制备这些组合的装置。原生制备权限、可用观察效果和共同参考都须另列；Born 规则、仪器
分支、系统组合以及物理时钟的起源也不由这个 no-go 推出。一般不可克隆边界已经由原卷定理
10.4 供应，本节不重复它，也不把 (42.3) 当作完整量子起源。

**来源与适用范围。** 全树定义、$\rho$ 的递归和 $\rho$ 的单射性复用上述两个实际 D5/Blueprint
来源；其现有结论没有覆盖本节的核刚性。核商、全部有限零关系下降、Hilbert 完成和 GNS 中间
机制复用原卷 §§6、15.2、26.2 及其中列出的 Predictive Memory、Watrous、Weber--Li--Voigt
和 Fewster--Rejzner 来源；一般不可克隆复用原卷定理 10.4。对仓内这些来源和相邻成熟文献的
有限核对未找到全实际来源树的精确 0/1 供应，因此本节标为 repo-derived 的新接合，既不声称
原创性，也不声称穷尽搜索。若要恢复忠实非正交来源，最小实质改变是撤去或改写 (42.1) 的
精确构造乘法，或改动来源组合/运输使 (42.4) 的因子化不再成立；仅删除 faithfulness、PSD
或把 Read/Apply/Stop 重新命名，都不会解除定理 42.2 的代数约束。这一条件性 no-go
不否定改变关系合同后的通常量子实现。

## 追加锚（本行以下为增补区）

## 43. 全树来源核的精确刚性不具有复数值的一致近似延拓

**定义 43.1（全域误差与所问的一致模）。** 沿用 §42 的整个自由有序二叉树代数
$T$，不施加结合律、不截断树高，也不合并来源。叶标签 $\alpha\ne\beta$，构造子为
$\langle s,t\rangle$，运输仍严格取

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

记 $\delta_{s,t}=\mathbf1_{\{s=t\}}$。对 $\varepsilon>0$，令
$\mathcal C_\varepsilon$ 是所有 $K:T\times T\to\mathbb C$ 中满足下列条件的核：
Hermitian 性、对角归一化、全部有限 Gram 矩阵半正定、精确运输不变性、忠实性，以及
全四元组的绝对乘法缺陷界。明确地，条件是

$$
\begin{aligned}
K(t,s)&=\overline{K(s,t)},&K(t,t)&=1,\\
\sum_{j,k=1}^{M}\overline{c_j}c_kK(t_j,t_k)&\ge0,
&K(\rho s,\rho t)&=K(s,t),\\
K(s,t)=1&\Longleftrightarrow s=t,
&\sup_{s,t,u,v\in T}|D_K(s,t,u,v)|&\le\varepsilon,\\
D_K(s,t,u,v)&:=K(\langle s,t\rangle,\langle u,v\rangle)-K(s,u)K(t,v).
\end{aligned}
\tag{43.1}
$$

正性中的 $M\ge1$ 任意，$t_1,\ldots,t_M$ 可以重复，$c_j\in\mathbb C$ 任意；
正性不只指某些诊断树列。这里仅把 §42 的精确乘法改为误差界，其余条件保持精确。
所问的一致模是一个 $\omega:(0,\infty)\to[0,\infty)$，满足
$\lim_{\varepsilon\downarrow0}\omega(\varepsilon)=0$，且

$$
\forall\varepsilon>0\ \forall K\in\mathcal C_\varepsilon,\qquad
\sup_{s,t\in T}\min\{|K(s,t)|,|K(s,t)-1|\}\le\omega(\varepsilon).
\tag{43.2}
$$

式 (43.2) 测量实际复核值到 $\{0,1\}$ 的距离，不先取模，也不先作来源依赖的重相位。

**定理 43.2（不变量积累给出的一致模反例及其规范边界）。** 定义

$$
\begin{aligned}
b(s,t)&:=\delta_{s,t},&q(\alpha)&=q(\beta)=0,\\
q(\langle s,t\rangle)&:=q(s)+q(t)+b(s,t).
\end{aligned}
\tag{43.3}
$$

因而 $q:T\to\mathbb N$ 计数左右直接子树相等的内部节点。对每个整数 $n\ge1$，取

$$
\begin{aligned}
m_n&=5n,&r_n&=\frac1{5n},&h_n&=\frac\pi{5n},&a_n&=1-r_n,\\
z_n(t)&=e^{ih_nq(t)},&P_n(s,t)&=\overline{z_n(s)}z_n(t),\\
K_n(s,t)&=a_nP_n(s,t)+r_n\delta_{s,t},&\varepsilon_n&=\frac1n.
\end{aligned}
\tag{43.4}
$$

这些函数定义在全部 $T$ 上，且 $q(\rho t)=q(t)$。每个 $K_n$ 都属于
$\mathcal C_{\varepsilon_n}$，并有更具体的全域界

$$
\sup_{s,t,u,v\in T}|D_{K_n}(s,t,u,v)|
\le\left(1-\frac1{5n}\right)\frac{\pi+1}{5n}<\frac1n.
\tag{43.5}
$$

令 $C=\langle\alpha,\alpha\rangle$，$w_0=\beta$，
$w_{k+1}=\langle w_k,C\rangle$。则

$$
q(w_k)=k,\qquad K_n(\alpha,w_{5n})=-a_n,
\qquad
\min\{|K_n(\alpha,w_{5n})|,|K_n(\alpha,w_{5n})-1|\}
=a_n\ge\frac45>\frac12.
\tag{43.6}
$$

所以 (43.2) 的一致模不存在。与此同时，这一反例族有以下精确边界：对每个固定来源对
$K_n(s,t)\to1$，对每个固定有限来源集合该收敛一致；其模长与模长平方在全域上一致趋于 $1$；
把 Gram 代表 $\eta_n(t)$ 改为 $\overline{z_n(t)}\eta_n(t)$ 后，核恰好变为 §42.4
已经给出的 $K_c$，其中 $c=a_n$。

**证明。** 首先复用实际来源运输的单射性：[Source Transport Centralizer 的
`source_transport_centralizer`](../../../D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean)
的第三个合取项适用于 $F=\rho$，因为该 $F$ 保持构造子且与自身交换。
这里的来源对应是 [Genealogical Fiber Transport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean)
中的 $\mathrm{Source}=\mathrm{FreeMagma}(\mathrm{Bool})$，
$\alpha=\mathrm{of}(\mathrm{true})$、$\beta=\mathrm{of}(\mathrm{false})$，
$\rho=\mathrm{substitution}$。不把该全域结论换成单轨道结论。

对树作结构归纳。两个叶情形分别给出
$q(\rho\alpha)=q(\beta)=0$ 和
$q(\rho\beta)=q(\langle\beta,\alpha\rangle)=0$；后者使用 $\beta\ne\alpha$。
内部节点情形使用归纳假设与运输单射性，得到

$$
\begin{aligned}
q(\rho\langle s,t\rangle)
&=q(\rho s)+q(\rho t)+\mathbf1_{\{\rho s=\rho t\}}\\
&=q(s)+q(t)+\mathbf1_{\{s=t\}}=q(\langle s,t\rangle).
\end{aligned}
\tag{43.7}
$$

归纳覆盖所有有限树，未对树高或叶数取统一上限。$q$ 本身不单射；这不改变来源域，
而且 (43.4) 的 delta 项仍分离每一对不同来源。

固定 $n$，简记 $r=r_n$、$h=h_n$、$a=1-r$、$z=z_n$、$P=P_n$、$K=K_n$。
有 $0<r\le1/5$、$a>0$ 和 $|z(t)|=1$，所以 $K$ Hermitian 且 $K(t,t)=a+r=1$。
若 $F$ 是任意有限树列 $t_1,\ldots,t_M$ 中不同树的集合，则

$$
\sum_{j,k=1}^{M}\overline{c_j}c_kK(t_j,t_k)
=a\left|\sum_{j=1}^{M}c_jz(t_j)\right|^2
+r\sum_{x\in F}\left|\sum_{j:t_j=x}c_j\right|^2\ge0.
\tag{43.8}
$$

该恒等式也包含重复标签，故给出全部所需正性。这是通常的 Gram 正性计算，作为本构造的
中间步骤使用，不另作新正性结论。取内积对第一个变量共轭线性，显式实现为

$$
\eta_n(t)=\sqrt{a_n}\,z_n(t)e_0+\sqrt{r_n}\,e_t
\quad\hbox{于}\quad \mathbb Ce_0\oplus\ell^2(T),
\qquad K_n(s,t)=\langle\eta_n(s),\eta_n(t)\rangle.
\tag{43.9}
$$

不同 $t$ 的非零 $e_t$ 分量保证此归一 Gram 映射单射；也可直接由
$s\ne t\Rightarrow|K(s,t)|=a<1$ 得到 $K(s,t)=1\Longleftrightarrow s=t$。
式 (43.7) 保持 $P$，运输单射性保持 delta 项，所以 $K(\rho s,\rho t)=K(s,t)$ 精确成立。

现取任意四棵树 $s,t,u,v$，允许它们之间有任意相等关系。置

$$
A=P(s,u),\quad B=P(t,v),\quad d=\delta_{s,u},\quad e=\delta_{t,v},
\quad E=e^{ih(b(u,v)-b(s,t))}.
$$

式 (43.3) 给出 $P(\langle s,t\rangle,\langle u,v\rangle)=ABE$；
自由有序构造子的单射性给出
$\delta_{\langle s,t\rangle,\langle u,v\rangle}=de$。因此直接展开为

$$
\begin{aligned}
D_K(s,t,u,v)
&=aABE+rde-(aA+rd)(aB+re)\\
&=aAB(E-1)+ra(A-d)(B-e).
\end{aligned}
\tag{43.10}
$$

这里 $|AB|=1$。若 $d=1$ 则 $A=1$，故 $A-d=0$；若 $d=0$ 则
$|A-d|=|A|=1$。于是总有 $|A-d|\le1$，同理 $|B-e|\le1$。
又 $b(u,v)-b(s,t)\in\{-1,0,1\}$，由
$|e^{ix}-1|\le|x|$ 得到 $|E-1|\le h$。故

$$
|D_K(s,t,u,v)|\le a(h+r)
=\left(1-\frac1{5n}\right)\frac{\pi+1}{5n}<\frac1n,
$$

最后使用 $\pi<4$。这个估计与四棵树的大小无关，因而得到 (43.5)，并完成
$K_n\in\mathcal C_{1/n}$ 的全部条件。它们并非精确乘法核：取
$(s,t,u,v)=(\alpha,\beta,\beta,\alpha)$，有 $A=B=E=1$、$d=e=0$，
故 $D_K=ra>0$。因此不与定理 42.2 的精确刚性冲突。

再验证移动见证。$q(C)=1$；$w_0$ 是叶，与 $C$ 不同，而每个 $w_k$（$k\ge1$）
的右子树是 $C$，$C$ 的右子树却是 $\alpha$。由 $C\ne\alpha$ 和自由构造子的
唯一可读性，对所有 $k\ge0$ 都有 $w_k\ne C$。于是

$$
q(w_{k+1})=q(w_k)+q(C)+b(w_k,C)=q(w_k)+1,
\qquad q(w_0)=0.
$$

归纳得 $q(w_k)=k$。由于 $\alpha\ne w_{5n}$，
$P_n(\alpha,w_{5n})=e^{ih_n5n}=e^{i\pi}=-1$，故核值是 $-a_n$。
它到 $0$ 和 $1$ 的距离分别为 $a_n$ 和 $1+a_n$，这证明 (43.6)。如果 (43.2)
成立，就有 $\omega(1/n)\ge4/5$ 对所有 $n\ge1$ 成立，与趋零要求矛盾。
这里必须让来源对随 $n$ 移动；对一个预先固定的有限树列作检查不能代替该量词。

最后计算相位规范与极限。对任意固定 $s,t$，$q(t)-q(s)$ 是固定的有限整数，并且

$$
|K_n(s,t)-1|
\le r_n+h_n|q(t)-q(s)|\longrightarrow0.
\tag{43.11}
$$

有限集合上 $|q(t)-q(s)|$ 有固定最大值，故其上的收敛一致。逐对极限是非忠实的全 $1$ 核；
每个 $K_n$ 的忠实性未给出与 $n$ 无关的分离尺度。反之，移动见证满足
$h_n(q(w_{5n})-q(\alpha))=\pi$，所以 (43.11) 不能在全 $T$ 上变成趋零界。

在 (43.9) 中令 $\widetilde\eta_n(t)=\overline{z_n(t)}\eta_n(t)$。
按同一内积约定，其核严格满足

$$
\begin{aligned}
\widetilde K_n(s,t)
&=z_n(s)\overline{z_n(t)}K_n(s,t)
=\overline{P_n(s,t)}K_n(s,t)\\
&=a_n+r_n\delta_{s,t}=K_{a_n}(s,t).
\end{aligned}
\tag{43.12}
$$

最后一步在 delta 非零时使用 $P_n(t,t)=1$。这恰是命题 42.4 的既有族，
不是另一个新 $K_c$ 构造。此处重相位保持归一化、正性、忠实性和精确运输不变性，
其全四元组缺陷还能直接写为

$$
D_{\widetilde K_n}(s,t,u,v)
=r_na_n(1-\delta_{s,u})(1-\delta_{t,v}).
\tag{43.13}
$$

不过 (43.12) 改变了 (43.2) 所测试的复核值；一般的来源依赖重相位也不保证保持
构造乘法或原误差界。允许先作这种规范选择，就换成了另一稳定性问题。

对原族本身，所有来源对都精确满足

$$
\begin{aligned}
|K_n(s,t)|&=a_n+r_n\delta_{s,t},\\
|K_n(s,t)|^2&=a_n^2+(1-a_n^2)\delta_{s,t},\\
\sup_{s,t\in T}\bigl||K_n(s,t)|-1\bigr|&=r_n\longrightarrow0,\\
\sup_{s,t\in T}\bigl||K_n(s,t)|^2-1\bigr|&=2r_n-r_n^2\longrightarrow0.
\end{aligned}
\tag{43.14}
$$

上确界等号由任意不同的来源对取得。因此本族不反驳以模长、模长平方或允许上述相位规范
表述的稳定性，也不证明这些其他问题对所有核成立。机制是无界的运输不变量 $q$ 把每次
构造至多 $h_n$ 的相位误差积累为移动树对上的有限相角，同时 delta 项维持全来源忠实性。∎

定理 43.2 的数学来源与归属如下：自由全树及其运输单射性复用上述来源，精确刚性与
$K_c$ 复用 §42，Gram 正性与 Hilbert 表示复用原卷 §§6、15.2、26.2 的既有机制。
本条承重内容是 $q$、全四元组缺陷恒等式及移动见证的来源特定接合，归为 repo-derived。
有限比对范围是本卷、原卷、相邻的 Probability Phase Transport and Holonomy 两卷、
Boundary Transport Fibers and Loop Closure 卷，以及 FibonacciAtomic 的实际树运输来源；
在该范围的相等子树与一致稳定性精确词组比对中未找到这一完整反例族，不声称全库无重复。
文献范围限于 arXiv 的 quasimorphism 与 binary trees 联合查询，以及 Baker、Lawrence、
Zorzitto 的 *The stability of the equation f(x+y)=f(x)f(y)*，
[DOI 10.1090/S0002-9939-1979-0524294-6](https://doi.org/10.1090/S0002-9939-1979-0524294-6)。
前者无命中，后者原文不可访问，故后者只作相邻文献指向，不借用其定理或假定其适用于自由树。
这组有限范围不支持原创性或优先权断言。

**假设 43.3（从 Gram 数学到物理资源的解释条件）。** 本节的相位首先是复 Hilbert 代表的
数学相位。若要把这些对象解释为物理资源，须另行给出来源对应的原生制备、可制备叠加的范围、
可观测效果与仪器、组合规则、共同的操作相位参考，以及动力学与物理时钟的实现桥梁。
将平方重叠解释为概率还须独立的测量与 Born 对应。式 (43.1) 并未包含这些结构，
故定理 43.2 的结论只否定所列复值一致模；它既不给出这些实现桥梁，也不解决量子起源。

## 追加锚（本行以下为增补区）

## 44. 相等子树的位置集与模长、平方模长的全域不稳定性

**定义 44.1（保留位置的相等子树记录）。** 来源域、运输和核类严格沿用定义 43.1 的
整个 $T$、$\rho$ 和 $\mathcal C_\varepsilon$。令 $\mathcal A=\{0,1\}^*$，空地址为
$\epsilon$，$jB=\{jp:p\in B\}$。定义有限集

$$
\begin{aligned}
S(\alpha)&=S(\beta)=\varnothing,\\
S(\langle s,t\rangle)
&=R(s,t)\sqcup0S(s)\sqcup1S(t),\\
R(s,t)&=\begin{cases}\{\epsilon\},&s=t,\\\varnothing,&s\ne t,\end{cases}\\
d(s,u)&=|S(s)\mathbin\triangle S(u)|.
\end{aligned}
\tag{44.1}
$$

地址 $0$ 指左子树，$1$ 指右子树；$S(t)$ 恰为直接左右子树相等的内部节点地址集。
$\sqcup$ 表示地址区域不交。这里没有按 $S$ 的取值合并来源标签。

**命题 44.2（位置不变量与配对的精确距离分解）。** 对全部 $t\in T$，

$$
|S(t)|=q(t),\qquad S(\rho t)=S(t),
\tag{44.2}
$$

其中 $q$ 是 (43.3) 的原有计数。$d$ 是 $T$ 上的伪度量，而且对任意
$s,t,u,v\in T$ 有

$$
d(\langle s,t\rangle,\langle u,v\rangle)
=d(s,u)+d(t,v)+|\delta_{s,t}-\delta_{u,v}|.
\tag{44.3}
$$

**证明。** 三个地址区域 $\{\epsilon\},0\mathcal A,1\mathcal A$ 两两不交，
故 (44.1) 的基数递推正是 (43.3)，结构归纳给 $|S|=q$。
复用 §42 所列实际自由树运输的单射性，$\rho s=\rho t$ 当且仅当 $s=t$。
两个叶子的像分别为 $\beta$ 和 $\langle\beta,\alpha\rangle$；后者的两个子树不等，
所以两个像的 $S$ 都为空。内部节点使用运输保持构造子、上述相等关系及两个归纳假设，
逐一保留 (44.1) 的三个区域，得到 $S(\rho t)=S(t)$。

有限集的对称差非负、对称，且对角为空。包含关系
$X\triangle Z\subseteq(X\triangle Y)\cup(Y\triangle Z)$ 给三角不等式，故 $d$ 为伪度量。
它不必分离来源，例如 $S(\alpha)=S(\beta)$。对两个配对树在三个不交地址区域分别取
对称差，根地址的贡献为 $|\delta_{s,t}-\delta_{u,v}|$，子地址的贡献分别为
$d(s,u),d(t,v)$，这就证明 (44.3)。∎

**定理 44.3（位置核的忠实全域实现与统一缺陷）。** 对 $h>0$ 定义
$P_h(s,u)=e^{-hd(s,u)}$。对每个整数 $n\ge1$，令

$$
h_n=r_n=\frac1{5n},\qquad a_n=1-r_n,\qquad
L_n(s,u)=a_nP_{h_n}(s,u)+r_n\delta_{s,u}.
\tag{44.4}
$$

每个 $L_n$ 在整个 $T$ 上满足定义 43.1 的全部精确侧条件，并且

$$
\sup_{s,t,u,v\in T}|D_{L_n}(s,t,u,v)|
\le a_n(1-e^{-h_n}+r_n)
\le\frac{2a_n}{5n}<\frac1n.
\tag{44.5}
$$

特别地 $L_n\in\mathcal C_{1/n}$，且 $s\ne u$ 时 $0<L_n(s,u)\le a_n<1$。

**证明。** 记 $\operatorname{Fin}(\mathcal A)$ 为所有有限地址子集。
在单一复 Hilbert 空间 $H_0=\ell^2(\operatorname{Fin}(\mathcal A))$ 中取标准正交基 $e_B$，
并对每棵实际来源树定义有限支撑向量

$$
v_h(t)=e^{-h|S(t)|}
 \sum_{B\subseteq S(t)}(e^{2h}-1)^{|B|/2}e_B.
\tag{44.6}
$$

内积对第一项共轭线性。令 $I=S(s)\cap S(u)$，有限二项展开直接给

$$
\begin{aligned}
\langle v_h(s),v_h(u)\rangle
&=e^{-h(|S(s)|+|S(u)|)}\sum_{B\subseteq I}(e^{2h}-1)^{|B|}\\
&=e^{-h(|S(s)|+|S(u)|-2|I|)}=P_h(s,u).
\end{aligned}
\tag{44.7}
$$

取 $s=u$ 得范数一。在与 $n$ 无关的 $H=H_0\oplus\ell^2(T)$ 中，

$$
\eta_n(t)=\sqrt{a_n}\,v_{h_n}(t)\oplus\sqrt{r_n}\,e_t
\tag{44.8}
$$

是 $L_n$ 的归一 Gram 实现。任意 $M\ge1$、可重复的来源列 $t_1,\ldots,t_M$、
任意复数 $c_1,\ldots,c_M$ 均满足

$$
\begin{aligned}
\sum_{i,j=1}^M\overline{c_i}c_jL_n(t_i,t_j)
&=a_n\left\|\sum_i c_i v_{h_n}(t_i)\right\|^2
 +r_n\sum_{x\in\{t_1,\ldots,t_M\}}
       \left|\sum_{i:t_i=x}c_i\right|^2\ge0.
\end{aligned}
\tag{44.9}
$$

所以正性包括所有重复标签的复 Gram 测试，不只是实系数或互异树测试。
式 (44.7) 给实对称性和对角归一化；(44.2) 保持 $P_h$，运输单射性保持 delta 项，
故 $L_n(\rho s,\rho u)=L_n(s,u)$ 精确成立。$r_n>0$ 使 (44.8) 分离所有实际来源；
直接看核也有 $L_n(s,u)=1\Longleftrightarrow s=u$。特征 $S$ 的碰撞没有改变来源域。

固定 $n$ 并简写 $a,r,h,P,L$。对任意四棵树置

$$
A=P(s,u),\quad B=P(t,v),\quad d_0=\delta_{s,u},\quad e_0=\delta_{t,v},
\quad c=|\delta_{s,t}-\delta_{u,v}|,\quad E=e^{-hc}.
$$

式 (44.3) 给 $P(\langle s,t\rangle,\langle u,v\rangle)=ABE$，
构造子单射性给对应 delta 为 $d_0e_0$。由 $a+r=1$，逐项展开得精确恒等式

$$
\begin{aligned}
D_L(s,t,u,v)
&=aABE+rd_0e_0-(aA+rd_0)(aB+re_0)\\
&=aAB(E-1)+ra(A-d_0)(B-e_0).
\end{aligned}
\tag{44.10}
$$

这里 $0<A,B\le1$，$c\in\{0,1\}$；$d_0=1$ 时 $A=1$，否则
$0<A-d_0\le1$，所以总有 $|A-d_0|\le1$，同理 $|B-e_0|\le1$。
故 $|D_L|\le a(1-e^{-h})+ra\le a(h+r)$，证明 (44.5)。
整个推导未限制四树的相等关系、形状、深度或叶数。

指数 Hamming 核的正性与张量 Gram 正性是标准中间供应；(44.6)–(44.9) 直接完成所需计算。
本定理使用的新接合是实际树位置不变量、忠实来源提升和无树高限制的 (44.10)，
复用 §43 的计数及缺陷展开，不把一般正性机制另列为新结果。∎

**定理 44.4（移动来源对、任意重相位与零闭路边界）。** 不存在趋零的一致模，能够对
所有 $K\in\mathcal C_\varepsilon$ 控制下列任一量：

$$
\sup_{s,u\in T}\operatorname{dist}(|K(s,u)|,\{0,1\}),\qquad
\sup_{s,u\in T}\operatorname{dist}(|K(s,u)|^2,\{0,1\}).
\tag{44.11}
$$

具体取 §43 的实际树 $C=\langle\alpha,\alpha\rangle$、$w_0=\beta$、
$w_{k+1}=\langle w_k,C\rangle$，则

$$
\begin{aligned}
S(w_k)&=\{0^j1:0\le j<k\},\\
x_n:=L_n(\alpha,w_{5n})&=a_n/e,\\
\frac14<x_n<\frac12,\qquad
\operatorname{dist}(x_n,\{0,1\})&=x_n>\frac14,\\
\operatorname{dist}(x_n^2,\{0,1\})&=x_n^2>\frac1{16}.
\end{aligned}
\tag{44.12}
$$

任意实数 $\theta$ 还满足

$$
\min\{|e^{i\theta}x_n|,|e^{i\theta}x_n-1|\}=x_n>\frac14.
\tag{44.13}
$$

每个固定来源对有 $L_n(s,u)\to1$，每个固定有限来源集合上收敛一致；极限核不忠实。
每个有限 $n$ 的核不满足精确乘法。所有 $L_n$ 的有限闭合 Bargmann 积均为正实数，
闭路相位恒为零，即使作任意顶点重相位也如此。

**证明。** $S(C)=\{\epsilon\}$。$w_0$ 是叶，$k\ge1$ 时 $w_k$ 的右子树为 $C$，
而 $C$ 的右子树为 $\alpha\ne C$，故全部 $w_k\ne C$。
递推根地址从不进入 $S$，因此
$S(w_{k+1})=0S(w_k)\sqcup\{1\}$，归纳得到 (44.12) 第一式。
$S(\alpha)=\varnothing$ 且 $\alpha\ne w_{5n}$，故核值为 $a_ne^{-h_n5n}=a_n/e$。
由 $4/5\le a_n<1$ 和 $2<e<3$，

$$
x_n\ge\frac4{5e}>\frac4{15}>\frac14,\qquad
x_n<\frac1e<\frac12,\qquad
\frac1{16}<\frac{16}{225}<\frac{16}{25e^2}\le x_n^2<\frac14.
$$

两个最近端点都是零，给 (44.12)。若 (44.11) 中任何一致模存在，代入
$\varepsilon=1/n$ 和定理 44.3 的同一全域核，就迫使其在 $1/n$ 处分别大于
$1/4$ 或 $1/16$，与趋零矛盾。见证来源随 $n$ 增长，这不是固定有限切片结论。
任何 $\{0,1\}$ 值精确核的一致逼近都会蕴含相应端点距离界，因而也受到此反例限制。

反三角不等式给 $|e^{i\theta}x_n-1|\ge1-x_n>x_n$，证明 (44.13)。
任意来源依赖的顶点重相位在该见证对上只改变 $\theta$，所以连允许所有这种选择也不能
消去这一复值端点距离。此处的缺陷事件始终是原始 $L_n\in\mathcal C_{1/n}$；
没有假定任意重相位仍保持运输或同一缺陷界。

固定 $s,u$ 时 $d(s,u)$ 有限，$e^{-d(s,u)/(5n)}\to1$，且 $a_n\to1,r_n\to0$。
固定有限集合上取有限个距离的最大值即可得一致收敛。全 $1$ 极限合并全部 Gram 代表，
故不忠实。另一方面，在实际四元组 $(\alpha,\beta,\beta,\alpha)$ 上，
$A=B=E=1,d_0=e_0=0$，(44.10) 给 $D_{L_n}=r_na_n>0$；
因此 §42 的精确刚性原封适用，不被近似反例推翻。

每个核项严格为正，故任意有限环 $t_0,t_1,\ldots,t_m=t_0$ 的
$\prod_{j=0}^{m-1}L_n(t_j,t_{j+1})$ 为正实数。在
$\eta(t)\mapsto e^{i\chi_t}\eta(t)$ 下，边因子乘
$e^{i(\chi_{t_{j+1}}-\chi_{t_j})}$，闭环中相消。因此本族的模长不稳定性不提供
非零规范不变闭路相位；这与 §43 原秩一相位族的可移除相位也须区分。∎

## 追加锚（本行以下为增补区）

## 45. 位置与子树奇偶的复核：消失缺陷下不消失的闭路相位

**定义 45.1（同一位置集的奇偶着色）。** 仍用全部 $T$、原有 $\rho$ 和 (43.3) 的 $q$。
对每个地址 $p\in\mathcal A$ 定义 $\lambda_t(p)\in\{0,1,2\}$：若 $p$ 是 $t$ 中
内部节点 $\langle u,u\rangle$ 的地址，$q(u)$ 为偶数时取 $1$，奇数时取 $2$；
其余地址一律取 $0$，包括不存在的地址、叶和不等子树节点。记

$$
S_j(t)=\{p:\lambda_t(p)=j\}\quad(j=1,2),\qquad
S(t)=S_1(t)\sqcup S_2(t).
\tag{45.1}
$$

因此非零着色支撑就是定义 44.1 的位置集，不引入另一个来源商。
对一对树的新增根标签，记

$$
\ell(s,t)=
\begin{cases}
0,&s\ne t,\\
1,&s=t\text{ 且 }q(s)\text{ 为偶数},\\
2,&s=t\text{ 且 }q(s)\text{ 为奇数}.
\end{cases}
\tag{45.2}
$$

**假设 45.2（另供的复局部 Gram 选择）。** 在 $\mathbb C^2$ 中给定正交单位向量
$e_0,e_1$，内积第一项共轭线性，且对 $0<h<1$ 取 $b=1-h$ 和

$$
z_0=e_0,\qquad z_1=\sqrt b\,e_0+\sqrt h\,e_1,
\qquad z_2=\sqrt b\,e_0+i\sqrt h\,e_1.
\tag{45.3}
$$

这些向量、复标量域及其中的 $i$ 都是给定的模型选择，不由树名或奇偶递推推出。
记 $G_h(j,k)=\langle z_j,z_k\rangle$，定义全来源核

$$
P_h^{\mathrm c}(s,t)=\prod_{p\in\mathcal A}
 G_h(\lambda_s(p),\lambda_t(p)).
\tag{45.4}
$$

非单位因子只在有限集 $S(s)\cup S(t)$ 中出现，故乘积定义无穷序列的选择无关。

**定理 45.3（着色的来源对应、全局复 Gram 实现与统一缺陷）。** 对所有实际来源树，

$$
\lambda_{\rho t}(p)=\lambda_t(p)\quad(p\in\mathcal A).
\tag{45.5}
$$

整个 $\lambda_t$ 已由 $S(t)$ 决定：对每个 $p\in S(t)$，着色的奇偶数恰是

$$
\bigl|\{w\in\mathcal A:p0w\in S(t)\}\bigr|\pmod2.
\tag{45.6}
$$

对每个整数 $n\ge1$，令

$$
k_n=5n,\qquad h_n=r_n=\frac1{k_n},\qquad
b_n=a_n=1-\frac1{k_n},\qquad
K_n^{\mathrm c}=a_nP_{h_n}^{\mathrm c}+r_n\delta.
\tag{45.7}
$$

则 $K_n^{\mathrm c}$ 满足定义 43.1 的所有精确侧条件，并且

$$
\sup_{s,t,u,v\in T}|D_{K_n^{\mathrm c}}(s,t,u,v)|
\le a_n(2h_n+r_n)=\frac{3a_n}{5n}<\frac1n.
\tag{45.8}
$$

这里包括任意重复来源标签和任意复系数的 Gram 正性，且有单一载体上的归一化、
有限支撑、忠实来源提升。

**证明。** 若 $p$ 上的子树为 $\langle u,u\rangle$，则 $p0w\in S(t)$ 当且仅当
$w\in S(u)$，故 (45.6) 的基数为 $|S(u)|=q(u)$。这对所有 $p\in S(t)$ 同时成立；
不在 $S(t)$ 中的地址必标零，因而 $S(t)$ 确定整个着色场。此对应只恢复所定义的标签，
不选择 (45.3) 的复向量，也不从位置集产生 $i$。

对 $t$ 作结构归纳证明 (45.5)。叶 $\alpha$ 的像仍是叶，$\beta$ 的像
$\langle\beta,\alpha\rangle$ 只新增一个不等子树根，其标签为零。
内部节点使用 $\rho$ 单射保留子树相等性，使用 (43.7) 保留相等子树的 $q$ 奇偶，
再由归纳假设保留左右两个地址场。新增根和两个子场分别相同，覆盖全部地址。
也可从 (44.2) 与 (45.6) 直接得到同一结论。

局部向量给出的矩阵为

$$
G_h=
\begin{pmatrix}
1&\sqrt b&\sqrt b\\
\sqrt b&1&b+ih\\
\sqrt b&b-ih&1
\end{pmatrix}.
\tag{45.9}
$$

各向量范数一，所以 $|G_h(j,k)|\le1$。
又 $1-\sqrt b=h/(1+\sqrt b)\le h$，
$|(b\pm ih)-1|=\sqrt2h$，故所有 $j,k$ 都满足

$$
|G_h(j,k)-1|\le\sqrt2h\le2h.
\tag{45.10}
$$

在与 §44 相同的 $H_0=\ell^2(\operatorname{Fin}(\mathcal A))$ 中定义

$$
V_h(t)=b^{|S(t)|/2}\sum_{B\subseteq S(t)}
 \left(\frac h b\right)^{|B|/2}
 i^{|B\cap S_2(t)|}e_B.
\tag{45.11}
$$

每个向量有有限支撑，而且
$\|V_h(t)\|^2=b^{|S(t)|}(1+h/b)^{|S(t)|}=1$。
为核对内积，不需假定一个抽象无限张量积：在有限集
$U=S(s)\cup S(t)$ 上展开 (45.11)。每个地址不选入 $B$ 时，对标签非零的每一侧贡献
$\sqrt b$；选入时，该侧贡献 $\sqrt h$ 并在标签 $2$ 时贡献 $i$，第一侧取共轭。
两侧都为零时只有不选项，贡献一。逐地址的两项和正是 (45.9) 中的对应项。
有限分配律遂给

$$
\langle V_h(s),V_h(t)\rangle
=\prod_{p\in U}G_h(\lambda_s(p),\lambda_t(p))
=P_h^{\mathrm c}(s,t).
\tag{45.12}
$$

这是通常局部 Gram 张量正性的直接展开，作为本来源构造的中间供应使用。
在同一 $H=H_0\oplus\ell^2(T)$ 中，忠实提升为

$$
\eta_n^{\mathrm c}(t)=\sqrt{a_n}\,V_{h_n}(t)\oplus\sqrt{r_n}\,e_t.
\tag{45.13}
$$

它归一化且实现 $K_n^{\mathrm c}$。任意 $M\ge1$、任意可重复的 $t_i\in T$ 及
任意 $c_i\in\mathbb C$，严格有

$$
\sum_{i,j=1}^M\overline{c_i}c_jK_n^{\mathrm c}(t_i,t_j)
=a_n\left\|\sum_i c_iV_{h_n}(t_i)\right\|^2
 +r_n\sum_{x\in\{t_1,\ldots,t_M\}}
       \left|\sum_{i:t_i=x}c_i\right|^2\ge0.
\tag{45.14}
$$

Hermitian 性随 Gram 表示成立；$s\ne t$ 时
$|K_n^{\mathrm c}(s,t)|=a_n|P_{h_n}^{\mathrm c}(s,t)|\le a_n<1$，
故 $K_n^{\mathrm c}(s,t)=1$ 当且仅当 $s=t$。
非零 $e_t$ 分量也直接给 (45.13) 的单射性。式 (45.5) 保持 $P_h^{\mathrm c}$，
运输单射性保持 delta，所以全部来源对的运输不变性精确成立。

对任意四棵树，配对后的地址分成根、$0\mathcal A$、$1\mathcal A$，因此

$$
P_h^{\mathrm c}(\langle s,t\rangle,\langle u,v\rangle)
=P_h^{\mathrm c}(s,u)P_h^{\mathrm c}(t,v)
 G_h(\ell(s,t),\ell(u,v)).
\tag{45.15}
$$

该式不要求四树互异或同形。简记 $a,r,h,P^{\mathrm c},K^{\mathrm c}$ 并置
$A=P^{\mathrm c}(s,u)$、$B=P^{\mathrm c}(t,v)$、$d=\delta_{s,u}$、
$e=\delta_{t,v}$、$G=G_h(\ell(s,t),\ell(u,v))$。与 (44.10) 相同的代数展开给

$$
D_{K^{\mathrm c}}(s,t,u,v)
=aAB(G-1)+ra(A-d)(B-e).
\tag{45.16}
$$

这是复数恒等式。$|A|,|B|\le1$；$d=1$ 时 $A=1$，$d=0$ 时
$|A-d|=|A|\le1$，故总有 $|A-d|\le1$，同理 $|B-e|\le1$。
结合 (45.10) 得 $|D_{K^{\mathrm c}}|\le a(2h+r)$，对整个 $T^4$ 取上确界给 (45.8)。
更紧的同一估计为 $a(\sqrt2h+r)$；两者均不依赖树高。

本定理的来源特定内容是相等子树的逐址奇偶对应及其全域运输、(45.15) 与 (45.16)；
一般 Gram 正性沿用原卷 §§6、15.2、26.2，不作为新的正性定理。∎

**定理 45.4（实际移动三源的非零 Bargmann 相位与一致非零模长）。** 定义实际树

$$
C_0=\langle\alpha,\beta\rangle,\qquad
C_1=\langle\alpha,\alpha\rangle,\qquad
C_2=\langle C_1,C_1\rangle,
\qquad
W_{j,0}=\beta,\quad W_{j,m+1}=\langle W_{j,m},C_j\rangle.
\tag{45.17}
$$

对 $k=5n$，三棵 $W_{0,k},W_{1,k},W_{2,k}$ 两两不同。有向闭路积为

$$
\begin{aligned}
\mathcal B_n
&=K_n^{\mathrm c}(W_{0,k},W_{1,k})
 K_n^{\mathrm c}(W_{1,k},W_{2,k})
 K_n^{\mathrm c}(W_{2,k},W_{0,k})\\
&=a_n^3\bigl[b_n^3(b_n+ih_n)\bigr]^{5n}.
\end{aligned}
\tag{45.18}
$$

其主辐角及模长满足

$$
1<\theta_n:=\arg\mathcal B_n
=5n\arctan\frac1{5n-1}<\frac54<\pi,
\qquad
|\mathcal B_n|\ge\left(\frac45\right)^{23}>0.
\tag{45.19}
$$

任意顶点重相位保持 $\mathcal B_n$；反转环方向则取共轭。因此这不是可用顶点相位
消去的边相角，而是在统一缺陷趋零的同一全域核族中不趋零的闭路相位。

**证明。** 三棵装饰树的计数为 $q(C_0)=0,q(C_1)=1,q(C_2)=3$。
它们的非零场依次为空、$\{\epsilon:1\}$、$\{\epsilon:2,0:1,1:1\}$。
$W_{j,0}$ 是叶，不能等于内部树 $C_j$。若 $m\ge1$ 而 $W_{j,m}=C_j$，比较右子树
会迫使 $C_j$ 等于自身的真右子树，与有限树节点数矛盾。因此每个梳脊根的左右子树不等，
标签都是零。由递推，装饰场出现在地址块 $0^d1\mathcal A$，$0\le d<m$；
这些词 $0^d1$ 两两前缀不可比，地址块不交。

故对所有 $m\ge0$ 和 $j,l\in\{0,1,2\}$，

$$
q(W_{j,m})=m q(C_j),\qquad
P_h^{\mathrm c}(W_{j,m},W_{l,m})
=\bigl[P_h^{\mathrm c}(C_j,C_l)\bigr]^m.
\tag{45.20}
$$

$m\ge1$ 时右子树 $C_j$ 两两不同，便给三棵梳树两两不同；也可由计数 $0,m,3m$ 分离。
对装饰树的有限地址直接应用 (45.9)，得到

$$
\begin{aligned}
P_h^{\mathrm c}(C_0,C_1)&=\sqrt b,\\
P_h^{\mathrm c}(C_1,C_2)&=b(b+ih),\\
P_h^{\mathrm c}(C_2,C_0)&=b^{3/2}.
\end{aligned}
\tag{45.21}
$$

第二式中根的贡献为 $b+ih$，地址 $0,1$ 各贡献 $\sqrt b$。
三式的积为 $b^3(b+ih)$。在互异的三棵 $W_{j,k}$ 上 delta 项均消失，
(45.20) 遂给 (45.18)。

令 $x=1/(k-1)>0$。积分 $\arctan x=\int_0^x(1+t^2)^{-1}dt$ 给严格界
$x/(1+x^2)<\arctan x<x$。因此对 $k\ge5$，

$$
1<\frac{k(k-1)}{(k-1)^2+1}
<k\arctan\frac1{k-1}
<\frac{k}{k-1}\le\frac54.
\tag{45.22}
$$

这个总相角已经在 $(0,\pi)$ 中，故就是主辐角，没有模 $2\pi$ 的绕回。
特别地
$|\mathcal B_n/|\mathcal B_n|-1|=2\sin(\theta_n/2)>2\sin(1/2)$。

由于 $a=b=1-1/k$，$|b+ih|\ge b$，

$$
|\mathcal B_n|
=b^{3k+3}(b^2+h^2)^{k/2}\ge b^{4k+3}.
\tag{45.23}
$$

为给出解析的一致下界，对实数 $y>1$ 微分：

$$
\frac{d}{dy}\bigl[y\log(1-1/y)\bigr]
=\frac1{y-1}-\log\left(1+\frac1{y-1}\right)>0,
$$

最后一步由 $\log(1+u)<u$。故 $k\ge5$ 时
$(1-1/k)^k\ge(4/5)^5$，而 $b^3\ge(4/5)^3$，所以
$b^{4k+3}=(b^k)^4b^3\ge(4/5)^{23}$，证明 (45.19)。

按同一内积约定，$\eta(t)\mapsto e^{i\chi_t}\eta(t)$ 使核变为
$e^{i(\chi_t-\chi_s)}K(s,t)$。沿三条边的指数和为零，闭路积精确不变；
Hermitian 性使反向积为共轭。这是通常 Bargmann 规范不变机制的直接应用。
非零闭路相位还排除将整个见证三元组同时变为实 Gram 数据的可能性：
若三条边都为实数，其积也为实数，与 (45.19) 矛盾。

标准 Bargmann 积及其关系信息背景复用
[Hidden Relations §§9–11、27.1、27.5](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)，
以及其中引用的 Oszmaniec、Brod、Galvão，
[*Measuring relational information between quantum states, and applications*](https://arxiv.org/abs/2109.10006v1)。
此处的规范相消已直接证明，不借用文献的实验比较权限。
新的承重接合是 (45.17) 的实际三源、(45.18) 的精确积及同时成立的全域缺陷界和
(45.19)，不把一般复 Gram 数据或非实 Bargmann 积本身作为新原则，也不作优先权主张。∎

**命题 45.5（固定来源极限、精确刚性与两族的区别）。** 对固定 $s,t\in T$，令
$M(s,t)=|S(s)\cup S(t)|$，则

$$
|K_n^{\mathrm c}(s,t)-1|\le2h_nM(s,t)+r_n\longrightarrow0.
\tag{45.24}
$$

收敛在每个固定有限来源集合上一致；逐对极限仍是非忠实的全 $1$ 核。
每个有限 $n$ 的 $K_n^{\mathrm c}$ 均不满足精确乘法。固定三源的闭路积趋于一，
而定理 45.4 的移动三源有 $\mathcal B_n\to e^{-4+i}$。
(45.19) 只对所列移动闭路给正下界，没有全来源两两重叠的统一正下界。
§44 的实模长族仍是零闭路相位族，不能用本节的结论回改它。

**证明。** 对有限乘积作望远镜展开；各因子模长至多一且满足 (45.10)，故
$|P_{h_n}^{\mathrm c}(s,t)-1|\le2h_nM(s,t)$。
又 $K_n^{\mathrm c}-1=a_n(P_{h_n}^{\mathrm c}-1)+r_n(\delta-1)$，即得 (45.24)。
有限集合上 $M$ 有有限最大值，得一致收敛；不同来源在全 $1$ 极限中的代表相同。
在四元组 $(\alpha,\beta,\beta,\alpha)$ 上，四棵叶及两个不等子树根的场都为空，
所以 $A=B=G=1,d=e=0$，(45.16) 给 $D_{K_n^{\mathrm c}}=r_na_n>0$。
因此定理 42.2 所要求的精确乘法条件并不成立。

固定三源的三条边各趋一，故积趋一。对于移动环，令 $k=5n$；在一的邻域取连续复对数，
则由 (45.18) 有

$$
\log\mathcal B_n
=(3k+3)\log(1-1/k)+k\log\bigl(1+(-1+i)/k\bigr)
\longrightarrow-3+(-1+i)=-4+i,
\tag{45.25}
$$

其中使用 $\log(1+z)=z+O(|z|^2)$；这也可由该对数在零点的导数一得到。
指数连续性给所称极限，移动见证的复杂度随 $n$ 增长，因而不与固定来源收敛冲突。
反之，固定 $n$ 并让 $m\to\infty$，(45.20)–(45.21) 给

$$
|K_n^{\mathrm c}(W_{0,m},W_{1,m})|=a_nb_n^{m/2}\longrightarrow0
\quad(m\ge1).
\tag{45.26}
$$

所以所证一致下界是一个移动闭路的下界，不能提升为全部来源对的下界。
§44 每项严格为正，其闭路积始终为正实数；本节则通过 (45.3) 的另供复局部选择，
在由同一 $S$ 决定的着色上得到非实闭路积。信息记录的确定性对应并不强制两种 Gram
选择相同，也不把原实核族变成复闭路族。∎

**假设 45.6（数学关系与原生物理解释的接口）。** 若将上述核或闭路积用于物理解释，
另须给出实际来源的原生制备映射、可制备相干组合的范围、允许的效果或仪器、共同操作
相位参考与相位敏感比较、其精度和资源成本，以及物理系统组合、动力学和时钟的对应。
将模长平方解释为概率还须独立的 Born 与测量标定。
树地址索引的 Hilbert 张量坐标不自动是可独立组合的物理子系统；运输不变的 Gram
表示不自动是一扇原生可调用的物理门。假设 45.2 的两个非平凡局部向量及其 $i$ 仍是
模型输入，(45.6) 的奇偶可恢复性不消去这些输入。
因此 §§44–45 给出的是所列全来源核的数学不稳定性与规范不变闭路结构，
没有由裸 FIB 标签推出复数域、相干制备、Born 规则或量子起源；这些接口条件仍须另行建立。

## 追加锚（本行以下为增补区）

## 46. 全树复核模的实 Gram 完成与统一缺陷

沿用 §§42–45 的整个 $T=\mathrm{FreeMagma}(\mathrm{Bool})$，不取商、不限树高、
不只取单条轨道。运输仍严格为 $\rho(\alpha)=\beta$、
$\rho(\beta)=\langle\beta,\alpha\rangle$、
$\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle$。
下面的取模正性由这个明确来源族的局部完成证明；不宣称任意正定核逐项取模仍正定。

**定义 46.1（逐址的实局部完成）。** 对 $0<h<1$ 置 $b=1-h$，并令

$$
c=\sqrt{b^2+h^2},\qquad
\gamma=\frac{c-b}{\sqrt h},\qquad
\varphi=\sqrt{h-\gamma^2}.
\tag{46.1}
$$

由 $b<c<b+h=1$ 得 $0<\gamma<\sqrt h$，所以 $\varphi>0$。在实三维空间取
正交单位基 $e_0,e_1,e_2$，定义

$$
u_0=e_0,\qquad
u_1=\sqrt b\,e_0+\sqrt h\,e_1,\qquad
u_2=\sqrt b\,e_0+\gamma e_1+\varphi e_2.
\tag{46.2}
$$

三个向量都是单位向量，且其 Gram 矩阵为

$$
H_h=
\begin{pmatrix}
1&\sqrt b&\sqrt b\\
\sqrt b&1&c\\
\sqrt b&c&1
\end{pmatrix}.
\tag{46.3}
$$

事实上 $\langle u_1,u_2\rangle=b+\sqrt h\,\gamma=c$。由 (45.9)，

$$
H_h(j,l)=\left|G_h(j,l)\right|\qquad(j,l\in\{0,1,2\}).
\tag{46.4}
$$

令 $\mathsf E$ 为所有有限支撑映射 $\sigma:\mathcal A\to\{0,1,2\}$ 的集合，
并以 $e_\sigma$ 为 $\ell^2(\mathsf E;\mathbb R)$ 的标准基。若
$u_j=\sum_{q=0}^2u_{j,q}e_q$，对每棵树定义有限支撑向量

$$
U_h(t)=
\sum_{\substack{\sigma:\mathcal A\to\{0,1,2\}\\
                 \sigma(p)=0\ (p\notin S(t))}}
\left(\prod_{p\in S(t)}u_{\lambda_t(p),\sigma(p)}\right)e_\sigma.
\tag{46.5}
$$

至多有 $3^{|S(t)|}$ 个非零坐标。有限分配律和 (46.3) 给出

$$
\|U_h(t)\|=1,\qquad
Q_h(s,t):=\langle U_h(s),U_h(t)\rangle
 =\prod_{p\in\mathcal A}H_h(\lambda_s(p),\lambda_t(p))
 =\left|P_h^{\mathrm c}(s,t)\right|.
\tag{46.6}
$$

最后一个等式可逐因子取模，因为所有 $H_h(j,l)$ 都是非负实数。这个构造只使用
每棵树的有限位置集；它不要求一个抽象的无限张量积，也不把地址坐标宣称为物理子系统。

**定理 46.2（全来源的正实模核）。** 对 $n\ge1$ 令

$$
h_n=r_n=\frac1{5n},\qquad a_n=b_n=1-h_n,\qquad
R_n(s,t)=a_nQ_{h_n}(s,t)+r_n\delta_{s,t}.
\tag{46.7}
$$

则 $R_n$ 是全 $T$ 上的归一化实 Gram 核，并且

$$
R_n(s,t)=\left|K_n^{\mathrm c}(s,t)\right|
\qquad(s,t\in T).
\tag{46.8}
$$

它保持 $\rho$，对不同来源满足 $0<R_n(s,t)\le a_n<1$，且所有重复标签的复
Gram 测试均非负。存在一个与 $n$ 无关的实 Hilbert 空间
$\mathcal H_R=\ell^2(\mathsf E;\mathbb R)\oplus\ell^2(T;\mathbb R)$ 及单位向量

$$
\eta_n^R(t)=\sqrt{a_n}\,U_{h_n}(t)\oplus\sqrt{r_n}\,e_t
\tag{46.9}
$$

实现该核。对所有 $s,t,u,v\in T$，若
$D_{R_n}(s,t,u,v):=R_n(\langle s,t\rangle,\langle u,v\rangle)
-R_n(s,u)R_n(t,v)$，则

$$
\sup_{T^4}|D_{R_n}|\le a_n(h_n+r_n)=\frac{2a_n}{5n}<\frac1n.
\tag{46.10}
$$

**证明。** 由 (45.5) 和 (46.6)，$Q_h(\rho s,\rho t)=Q_h(s,t)$。对任意
可重复的 $t_1,\ldots,t_M$ 和 $c_1,\ldots,c_M\in\mathbb C$，把实空间复
化后有

$$
\sum_{i,j}\overline{c_i}c_jR_n(t_i,t_j)
=a_n\left\|\sum_i c_iU_{h_n}(t_i)\right\|^2
 +r_n\sum_{x\in\{t_i\}}
       \left|\sum_{i:t_i=x}c_i\right|^2\ge0.
\tag{46.11}
$$

这同时证明正性、重复标签的处理、归一化和 (46.9) 的 Gram 表示。
对 $s\ne t$，两核的 delta 项都为零，故
$|K_n^{\mathrm c}(s,t)|=a_n|P_{h_n}^{\mathrm c}(s,t)|=a_nQ_{h_n}(s,t)$；
对 $s=t$，两边都为 $1$，证明 (46.8)。所有局部因子严格为正且只有有限个非单位因子，
故 $Q_h(s,t)>0$。实对称性给 Hermitian 性，运输由 (45.5) 和 $\rho$ 的单射性保持。
delta 分量给出来源标签的忠实性；因此 (46.8) 也给出 $R_n(s,t)=1$ 当且仅当 $s=t$。

对四棵树置

$$
A=Q_h(s,u),\quad B=Q_h(t,v),\quad d=\delta_{s,u},\quad e=\delta_{t,v},
\quad C=H_h(\ell(s,t),\ell(u,v)).
$$

地址分解与 (45.15) 同样给出 $Q_h(\langle s,t\rangle,\langle u,v\rangle)=ABC$，
而构造子的单射性给出对应 delta 为 $de$。于是有精确恒等式

$$
D_{R_n}=a_nAB(C-1)+r_na_n(A-d)(B-e).
\tag{46.12}
$$

因为 $1-\sqrt b\le h$ 且 $1-c\le h$，故 $|C-1|\le h$。又
$0\le A,B\le1$，且 $d=1$ 时 $A=1$、$d=0$ 时 $|A-d|=A$，所以
$|A-d|,|B-e|\le1$。式 (46.10) 随即成立。∎

## 47. 破坏性重置菜单的完整记录等价

**定义 47.1（分别供给的破坏性查询）。** 固定 $n$。复模型使用 (45.13) 的
复 Hilbert 载体 $\mathcal H_{\mathrm c}$；实模核模型使用 (46.9) 的实空间的复化
$\mathcal H_{R,\mathbb C}=\mathcal H_R\otimes_{\mathbb R}\mathbb C$，其源向量仍有全实坐标。
记对应源向量为 $v_t^{\mathrm c}=\eta_n^{\mathrm c}(t)$ 与 $v_t^R=\eta_n^R(t)$。
以下密度算子及 CP 映射都在这些复 Hilbert 空间上定义；实模型的所用制备及仪器
保持实坐标子理论。这一步只统一数学记号，不由实 Gram 数据推断物理复标量。

在每个载体中另取正交单位失败标记 $|\mathrm{fail}\rangle$，置
$\widetilde H_{\mathrm c}=\mathcal H_{\mathrm c}\oplus\mathbb C|\mathrm{fail}\rangle$、
$\widetilde H_R=\mathcal H_{R,\mathbb C}\oplus\mathbb C|\mathrm{fail}\rangle$ 以及
$\widetilde P_t^X=|v_t^X\rangle\langle v_t^X|\oplus0$。对迹类算子 $Y$，查询 $t$ 的两支为

$$
\begin{aligned}
J_{t,X}^{+}(Y)&=\widetilde P_t^X Y\widetilde P_t^X,\\
J_{t,X}^{-}(Y)&=\operatorname{Tr}\!\left[(I-\widetilde P_t^X)Y\right]
 |\mathrm{fail}\rangle\langle\mathrm{fail}|,\qquad X\in\{\mathrm c,R\}.
\end{aligned}
\tag{47.1}
$$

正支是单 Kraus CP 映射，负支是正效果后制备固定态的 CP 映射；两支迹和为
$\operatorname{Tr}Y$。这在可分无限维载体也成立：若 $E=I-\widetilde P_t^X$，
取任意可数正交基 $f_j$，则负支的 Kraus 算子可取
$|\mathrm{fail}\rangle\langle f_j|\sqrt E$，其和在正迹类输入上按迹范数收敛。
失败标记在继续查询时吸收。协议约定负结果随即 Stop，正结果可继续或 Stop；
Stop 不改变系统并保留质量。这里的两个菜单分别供给，均不由 Gram 实现或五模原生菜单自动提供。

**定理 47.2（对应源制备的完整破坏性记录等价）。** 根输入明确限于同一标签 $s_0$
的对应制备 $|v_{s_0}^X\rangle\langle v_{s_0}^X|$。也可用同一个经典分布选择并记录
$s_0$，但不允许由此引入相干叠加。使用相同的可测经典策略：查询标签或 Stop 只依赖
此前完整经典记录和输入无关的随机种子。每个固定种子选出的决策树有限、每条叶终止，
但不同种子或协议之间不要求共同深度界。则两个模型的完整原始记录概率律相同，
包括零质量历史、终端负支、全部 Stop 和经典随机化信息，不作后选择。

具体地，若一个尚未终止的前缀质量为 $m$、当前源标签为 $s$、查询为 $t$，则

$$
\begin{aligned}
m_+&=m\,|K_n^{\mathrm c}(s,t)|^2=m\,R_n(s,t)^2,\\
m_-&=m\bigl(1-|K_n^{\mathrm c}(s,t)|^2\bigr)
     =m\bigl(1-R_n(s,t)^2\bigr).
\end{aligned}
\tag{47.2}
$$

正质量正支的归一化密度为 $|v_t^X\rangle\langle v_t^X|$，负支为失败标记；
零质量支只保留零算子，不定义其条件态。结论只关于这些对应制备与菜单，
不关于任意相干输入、任意效果、系统输出态相同、量子参考扩展或独立复合系统。

**证明。** 先固定全部经典选择，包括可能选择的根标签。有限树根质量为 $1$；
(47.1) 给 (47.2)，正支恢复对应的下一源标签，负支终止，Stop 保留前缀质量。
逐前缀对未归一质量归纳即得所有叶质量相同；迹保持和有限终止使每棵树的叶质量和为 $1$。
不从零历史取条件概率。

对任意独立种子概率空间 $(\Omega,\mu)$，要求所选标签、树、终止规则及分支概率可测。
所有有限标签/正负/Stop 字构成可数记录集 $\mathscr R$；将不属于某棵树的记录质量设为零。
记给定种子时记录 $a$ 的质量为 $p_{X,\omega}(a)$。上面的有限乘积递推给出可测函数，且
对每个 $\omega$ 有 $p_{\mathrm c,\omega}(a)=p_{R,\omega}(a)$ 及
$\sum_a p_{X,\omega}(a)=1$。因此对每个可测 $B\subseteq\Omega$，

$$
\Pr_X(\omega\in B,\ a)=\int_B p_{X,\omega}(a)\,d\mu(\omega),\qquad
\sum_{a\in\mathscr R}\int_\Omega p_{X,\omega}(a)\,d\mu(\omega)=1.
\tag{47.3}
$$

第二式由 Tonelli 定理，不需共同深度界。第一式给两模型相同的种子与记录联合律，
遗忘种子或对记录作同一可测经典处理仍相同。非原子种子按此积分，不能对单点种子的
概率求和。此证明直接使用实际无限载体上的分支概率；不借有限维 Choi 矩阵替代它。∎

一般 Gram 实现、效果与更新的区别及完整分支质量计算分别复用
[原卷 §§6、7.7、19、35.1](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)。
本节把它们应用于 (46.8) 的全来源对应，不提出新的仪器表示或概率积分定理。

## 48. 保留拒绝的相干记录差异

**定理 48.1（移动三源的保留拒绝间隙）。** 在定义 47.1 的对应载体上，对 $k=5n$ 使用 (45.17) 的三棵源
$W_{0,k},W_{1,k},W_{2,k}$。在每个模型 $X\in\{\mathrm c,R\}$ 中置
$P_j^X=|v_{W_{j,k}}^X\rangle\langle v_{W_{j,k}}^X|$。
首先明确制备 $Y_{0,X}=|v_{W_{0,k}}^X\rangle\langle v_{W_{0,k}}^X|$，质量为 $1$，
再施加另行供给的、保留负支的
Lüders 二元仪器

$$
L_{1,X}^{+}(Y)=P_1^XYP_1^X,\qquad
L_{1,X}^{-}(Y)=(I-P_1^X)Y(I-P_1^X),
\tag{48.1}
$$

第一步在各自的源载体上施加；第二步将其输出自然嵌入定义 47.1 的带失败标记空间，
以 $\widetilde P_{W_{2,k}}^X$ 作破坏性查询，记录正负，最后对每条记录 Stop。
等价地，可从开始就在扩张空间上使用 $P_j^X\oplus0$，且 $I$ 取扩张空间的恒等算子。
初态没有失败标记分量，两种写法的四条记录律一致。若
$x=|K_n^{\mathrm c}(W_{1,k},W_{0,k})|^2$、
$y=|K_n^{\mathrm c}(W_{2,k},W_{1,k})|^2$、
$z=|K_n^{\mathrm c}(W_{2,k},W_{0,k})|^2$，则复模型完整四记录律按
$(++,+-,-+,--)$ 排列为

$$
\begin{aligned}
(p(++),p(+-),p(-+),p(--))
=\bigl(&xy,\ x(1-y),\ z+xy-2\operatorname{Re}\mathcal B_n,\\
       &1-x-z-xy+2\operatorname{Re}\mathcal B_n\bigr).
\end{aligned}
\tag{48.2}
$$

实模型将其中的 $\operatorname{Re}\mathcal B_n$ 替换为 $|\mathcal B_n|$。因此

$$
p_{\mathrm c}(-,+)-p_R(-,+)
=2\bigl(|\mathcal B_n|-\operatorname{Re}\mathcal B_n\bigr)
=2|\mathcal B_n|(1-\cos\theta_n)
\ge \Delta_*:=2\left(\frac45\right)^{23}(1-\cos1)>0.
\tag{48.3}
$$

**证明。** 负后正分支的未归一振幅为

$$
P_2^X(I-P_1^X)v_{W_{0,k}}^X,
$$

故其质量为 $|K_{20}-K_{21}K_{10}|^2$；这里 $K_{ij}=\langle v_{W_{i,k}},v_{W_{j,k}}\rangle$，并且不除以
第一次负支的质量。对复模型，Hermitian 性把交叉项写成
$\mathcal B_n=K_{01}K_{12}K_{20}$，所以负后正质量是
$z+xy-2\operatorname{Re}\mathcal B_n$。实模型的三条边分别是复边的模，闭路积为
$|\mathcal B_n|$，得到 (48.2) 和 (48.3)。式 (45.19) 给
$\theta_n\in(1,5/4)\subset(0,\pi)$ 与
$|\mathcal B_n|\ge(4/5)^{23}$；在该区间 $1-\cos\theta_n\ge1-\cos1$。
前两项的和为 $x$；后两项的和为 $1-x$，来自未归一的第一负支。
各项均非负：第二次查询的正支为投影范数平方，负支为其补效果的平方范数
（等于破坏性负支的迹）。四项和为 $1$，每项均含最终 Stop；零质量项也保留。
两模型的完整律之差为 $(0,0,\Delta_n,-\Delta_n)$，其中 $\Delta_n$ 是 (48.3) 的左边，
故这是未归一原始概率的差异，没有选取成功子样本。∎

共轭整个复模型会把 $\mathcal B_n$ 换成其共轭，但 (48.3) 只读取 $\cos\theta_n$，
因此不决定相位方向。对所列制备及整个菜单同时共轭保持所有原始概率。
标准的 doubled-realification

$$
F(A)=\begin{pmatrix}\operatorname{Re}A&-\operatorname{Im}A\\
\operatorname{Im}A&\operatorname{Re}A\end{pmatrix}
\tag{48.4}
$$

满足 $F(AB)=F(A)F(B)$、$F(A^*)=F(A)^T$。对应规则是实密度
$\rho_{\mathbb R}=F(\rho)/2$、效果 $E_{\mathbb R}=F(E)$、Kraus 算子 $F(A_j)$。
因为对迹类 $B$ 有 $\operatorname{Tr}_{\mathbb R}F(B)=2\operatorname{Re}\operatorname{Tr}_{\mathbb C}B$，
密度迹为 $1$ 且效果概率与每条分支质量保持；$\sum_jA_j^*A_j=I$ 也被保持。
对有限秩算子 $\operatorname{rank}_{\mathbb R}F(A)=2\operatorname{rank}_{\mathbb C}A$，
所以复秩一源纯态变成实秩二密度，复秩一投影变成实秩二投影。
这不是 (46.9) 的实秩一源射线模型；它允许更大的实载体模拟复菜单。
在上述可分无限空间也可按实部、虚部作同一实化；正迹类密度仍按 $1/2$ 缩放。
因此本比较不排除更大的实模拟，也不选择物理复标量。
Lüders 保留负支是额外的仪器资源；在下节五模菜单中，读完全部模式再把四个负标签
作经典合并也不会保留四维块内的相干性。

## 49. 五模原生菜单的相干拒绝障碍

本节固定[原卷定义 20.1、35.1](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)
的实际矩阵及模式对应。按顺序
$(0,1,2,3,13)\leftrightarrow(N,2,3,5,25)$，$H=\mathbb C^5$ 的单位正交基为
$(e_N,e_2,e_3,e_5,e_{25})$，且

$$
K=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix},\qquad
D=\operatorname{diag}(1,i,i,i,1).
\tag{49.0}
$$

这里 $K$ 是五模生成元，不是 §§46–48 的来源核；$D$ 只改变坐标，不增加控制权限。

**定理 49.1（全有限原生协议的 half-diamond 下界）。** 原生协议只有等待
$U(t)=\exp(-itK)$、$t\ge0$，完整五结果秩一读出
$J_s(Y)=P_sYP_s$、$P_s=|e_s\rangle\langle e_s|$，Stop，有限历史反馈及
输入无关的经典随机化。不许量子旁路、额外 ancilla、reset 或新的粗粒度仪器。
一个未知系统输入只进入一次；初始控制资料与它独立。每个固定种子所选的决策树有限、
每条叶均 Stop 并保留全部读取标签、控制及终端质量；协议族与种子之间不要求共同深度界。
任意种子概率空间 $(\Omega,\mu)$ 均要求树选择、分支 CP 映射和终端后处理可测。
有限树的分支迹和为输入迹，故平均完整仪器也归一化。

为取得下界，可在同一 $H$ 上把等待扩大为任意系统酉控制：扩大类包含原生类，
下面对扩大类的下界因而适用于原生类。这不授予实际菜单那些酉门。

取任意非零真投影 $P$，令 $Q=I-P$ 且 $\operatorname{rank}Q=r\ge2$。目标旗标信道为

$$
\Lambda(Y)=PYP\otimes|+\rangle\langle+|
       +QYQ\otimes|-\rangle\langle-|.
\tag{49.1}
$$

任一上述协议的完整记录经任意经典二值后处理并保留系统输出，得到旗标信道 $\Gamma$。
二值后处理是完整记录的可测随机函数；其额外随机性也可并入独立种子，不丢弃任何记录。
比较范数定义在全部复输入及任意未触动的数学参考扩展上，系统输出与二值旗标一并保留。
这定义一种数学信道距离，不宣称原生菜单可制备纠缠参考或执行联合效果。则

$$
\frac12\|\Gamma-\Lambda\|_\diamond
\ge \max\left\{w,(1-w)\frac{r-1}{r}\right\}
\ge\frac{r-1}{2r-1},
\tag{49.2}
$$

其中 $w$ 是被标为负的、在首次量子读出前即终止的路径总质量。对实际五模的单模式
$P$ 有 $r=4$，所以 half-diamond 距离至少为 $3/7$（未除以二的 diamond 距离至少为
$6/7$）。

**证明。** 记 $M_-$ 为 $\Gamma$ 的负支子信道。按终端路径是否包含首次量子读出
分解为

$$
M_-=N_-+E_-.
\tag{49.3}
$$

无读出负路径只含输入无关的经典选择和系统酉，因此在离散情形
$N_-(Y)=\sum_jp_jV_jYV_j^*$，其中 $p_j\ge0$ 且 $\sum_jp_j=w$。对非原子种子，
将所有经典选择及负标签随机化并入种子后，同一式写成子概率积分

$$
N_-(Y)=\int V_\omega YV_\omega^*\,d\nu(\omega),
\qquad \nu(\Omega)=w.
\tag{49.4}
$$

无读出时没有输入相关的量子分支，故 $\nu$ 与未知输入无关，且
$N_-^*(I)=wI$。若 $w>0$，单位酉共轭映射构成有限维紧集，其凸包紧；
所以积分 $N_-/w$ 也有有限凸组合表示。不需要把连续种子当作原子求和。

对固定种子的任一含读出终端路径，其 Kraus 算子具有
$V_mP_{s_m}\cdots V_1P_{s_1}V_0$ 的形式（将相邻酉合并），至少含一个秩一投影，
故秩至多一，包括零算子情形。这正是
[静态相融纤维命题 44](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)
已用的首读/终端秩机制；这里复用它，不复证一个新的通用首读定理。
秩一算子写成 $|a\rangle\langle b|$ 时，其在任意正的系统—参考输入上的输出为
$|a\rangle\langle a|$ 乘一个正的参考算子，因此可分离。
固定种子下所有含读出负叶的有限和给 CP 的 $E_{-,\omega}$。

在此实际有限维 $H$ 上，平均定义为 CP 映射的 Bochner 积分
$E_-=\int E_{-,\omega}\,d\mu(\omega)$。
各被积映射是迹不增的，故其 Choi 矩阵可积；有限维可分离正锥闭且凸，
所以积分的 Choi 矩阵仍可分离，$E_-$ 是 entanglement-breaking（对未归一子信道亦即
其每个参考输出可分离）。有限维闭锥及紧凸包结论仅用于本节的 $\mathbb C^5$，
不用来替代 §47 的无限载体概率律。由于 $M_-$ 是子信道，

$$
0\le E_-^*(I)\le(1-w)I.
\tag{49.5}
$$

先取单位向量 $\psi\in\operatorname{ran}P$。目标的负概率为零，而协议的负概率
$\operatorname{Tr}M_-(|\psi\rangle\langle\psi|)\ge w$。在负旗标上作二值效果测量，
得到 half-diamond 距离至少为 $w$。

再取 $Q$ 的正交基 $q_1,\ldots,q_r$，并让外部参考系带有基
$f_1,\ldots,f_r$，置

$$
|\Phi_Q\rangle=\frac1{\sqrt r}\sum_{i=1}^rq_i\otimes f_i.
$$

目标在负旗标下输出该纯态，概率为 $1$。协议的未归一负输出写成
$\sigma_-=((M_-\otimes\operatorname{id})(|\Phi_Q\rangle\langle\Phi_Q|))$。
无读出部分在 $|\Phi_Q\rangle$ 上的重叠为

$$
\int\left|\langle\Phi_Q|(V_\omega\otimes I)|\Phi_Q\rangle\right|^2d\nu(\omega)\le w.
\tag{49.6}
$$

读出部分是正的可分离算子，迹由 (49.5) 至多为 $1-w$。对任意正的可分离算子
$\sigma$，标准 Schmidt 重叠界给出

$$
\langle\Phi_Q|\sigma|\Phi_Q\rangle\le\frac{\operatorname{Tr}\sigma}{r}.
\tag{49.7}
$$

具体地，对任意乘积向量 $a\otimes b$，Cauchy–Schwarz 给
$|\langle\Phi_Q,a\otimes b\rangle|^2\le\|Qa\|^2\|b\|^2/r
\le\|a\|^2\|b\|^2/r$；再对正的可分离和逐项相加并取闭包，即得 (49.7)。
它适用于未归一算子及 $5\times r$ 的矩形载体，无须把系统限制后重新归一化。
因此

$$
\langle\Phi_Q|\sigma_-|\Phi_Q\rangle
\le w+\frac{1-w}{r}.
$$

用负旗标与 $|\Phi_Q\rangle\langle\Phi_Q|$ 的联合投影（按系统、旗标、参考的顺序放置）比较两完整输出，
得到 half-diamond 距离至少为 $(1-w)(1-1/r)$。合并两个见证即得第一项。对
$w\in[0,1]$，两项的最大值在
$w=(r-1)/(2r-1)$ 处达到其最小可能值，给出第二项。∎

两个见证都输入迹一密度，且 $\Gamma$、$\Lambda$ 都是完整 CPTP 信道。
因此输出差是迹零 Hermitian 算子，对任何 $0\le E\le I$ 都有
$|\operatorname{Tr}E(\rho-\sigma)|\le\|\rho-\sigma\|_1/2$，
这正是上述概率差给 half-diamond 下界的归一化依据；$\sigma_-$ 本身始终不除以负概率。

中间供应的标准归属为 Horodecki–Shor–Ruskai，
[quant-ph/0302031v2，定理 4(A–D)](https://arxiv.org/html/quant-ph/0302031v2)
的秩一 Kraus、可分离 Choi 与 EB 对应，以及 Terhal–Horodecki，
[*Schmidt number for density matrices*，引理 1](https://arxiv.org/html/quant-ph/9911117v2)
的 Schmidt-number-$k$ 最大纠缠重叠界；这里取 $k=1$，并按上面的投影与正缩放用于矩形、
未归一情形。完整有限协议的共同菜单另见
[近似单份量子边界定义 1.1–1.2](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md)。
本节的承重接合是实际五模菜单的无读出/EB 分解与两个见证联合给出的 (49.2)，
不提出一般 EB、Schmidt 界或范数判别的新定理，不作穷尽检索或优先权主张。

这个下界是对所列原生菜单的资源障碍，不是最优性或可达到性定理，也不提供 Bell
效果、外部参考制备或额外相干记录。特别地，它与 §§46–48 的源射线模型不在同一
载体上；原生五模协议不能被默认为实现源核的破坏性或 Lüders 仪器。

## 50. 两个载体的秩边界与联合结论

对 $R_n$ 的任意 $m$ 个互异来源 $t_1,\ldots,t_m$，其 Gram 矩阵满足

$$
\bigl[R_n(t_i,t_j)\bigr]_{i,j=1}^m
=a_n\bigl[Q_{h_n}(t_i,t_j)\bigr]_{i,j=1}^m+r_nI_m
\succeq r_nI_m.
\tag{50.1}
$$

因为 $r_n>0$，任意非零 $c\in\mathbb C^m$ 的 Gram 二次型至少为
$r_n\|c\|^2>0$，故矩阵秩恰为 $m$。对 $K_n^{\mathrm c}$，由 (45.14) 同样有
$[K_n^{\mathrm c}(t_i,t_j)]\succeq r_nI_m$，结论相同。
由于 $m$ 任意，源核的单一全局载体含有无界的有限独立秩，不能由保持全部 Gram
内积的映射放入 $\mathbb C^5$。有限见证集当然可在其有限向量张成空间中实现，
其维数就是该有限 Gram 的秩，互异 $m$ 源时为 $m$；例如三源见证本身可在三维中表示，
但 $m>5$ 时已不能保持同一 Gram 放入五维。这是 delta 提升的直接秩后果，
不另提出一个通用维数定理，也不是排除全部量子模型或更大编码的物理 no-go。
有限见证的数学实现不提供原生制备、控制门或统一的制备成本。

因此 §§46–48 的结论是：对应源射线制备与所列菜单可在全来源标签上有相同的全部破坏性原始记录律，而在明确
保留拒绝的仪器下由移动闭环的 $\cos\theta_n$ 产生统一可见差异；§49 则独立说明，
实际五模的完整秩一读出菜单无法把四维拒绝子空间以小于 $3/7$ 的 half-diamond
误差保留下来。二者共同推进的是量子起源接口中的“记录等价—拒绝相干性”分界，
并没有把两个载体、制备权限、仪器合同、物理复标量、独立组合或 Born 对应连接起来。
若要把两条结论用于同一物理实验，还须另给来源到实际制备的映射、有限见证上的内积对应、
完整仪器及系统输出的对应和 Born 标定；只匹配单次效果概率不够。若要使用参考或组合系统，
还须证明相应扩展及独立组合合同。全来源 Gram 保持的 $\mathbb C^5$ 对应已由 (50.1) 排除，
但替代编码、较大载体或不同允许菜单仍须分别研究。$\rho$ 不变性不自动供应运输门，
全域概率间隙不自动供应原生制备或它的成本。更广的量子起源目标仍未解决。
移动见证随 $n$ 变化；固定 $n$ 时

$$
R_n(W_{0,m},W_{1,m})=a_nb_n^{m/2}\longrightarrow0\qquad(m\to\infty),
\tag{50.2}
$$

故 (48.3) 不是固定标签或统一制备资源成本的下界。相位整体共轭保留所有记录概率，
而更大的实倍增载体仍可表达复菜单；这些边界均不由源标签本身消除。

## 追加锚（本行以下为增补区）

## 51. 实际源嫁接与独立乘积的不同输入合同

**定义 51.1（完整输入与仅由状态决定的处理器）。** 固定 $n\ge1$，写
$a=b=1-1/(5n)$、$h=r=1/(5n)$。$X\in\{\mathrm c,R\}$ 分别表示
(45.13)、(46.9) 的源实现，$v_t^X=\eta_n^X(t)$，$\pi_t^X=|v_t^X\rangle\langle v_t^X|$；
实实现按定义 47.1 复化。以下两个输入族和目标族分别为

$$
\begin{aligned}
\text{构造：}&\quad \pi_s^X\otimes\pi_t^X\longmapsto\pi_{\langle s,t\rangle}^X,\\
\text{分解：}&\quad \pi_{\langle s,t\rangle}^X\longmapsto\pi_s^X\otimes\pi_t^X.
\end{aligned}
\tag{51.1}
$$

这里的独立张量制备是另行供应的操作前提。树的两个孩子、向量 (45.11) 的地址坐标、
源构造子 $\langle s,t\rangle$ 都不自动供应这个前提。同标签的两个独立输入也不是从一个
未知输入克隆得到的。

处理器的完整输入包括量子系统、所有可访问的制备记录、控制器记忆、时间或长度读数、
源相关辅助系统及其他旁路。若这些资料合记为 $G_{s,t}$，实际输入应写为
$\Omega_{s,t}$，而不能只写 (51.1) 的约化态。例如无额外相关时，构造输入为
$\pi_s^X\otimes\pi_t^X\otimes G_{s,t}$；对纯的 $G_{s,t}=|g_{s,t}\rangle\langle g_{s,t}|$，
其 Gram 内积还含 $\langle g_{s,t},g_{u,v}\rangle$。
原树路线中的 $s,t,\langle s,t\rangle$、地址场、子树奇偶和由实际制备产生的完整历史，
凡能被处理器读取者都属于这些源相关资料；核定义本身没有指定一个把它们交给物理处理器的服务。
完整源端语法记录与只交付一个编码态是两个不同输入合同。
下文“仅由状态决定”专指所有可访问辅助资料均为一个固定的、与未知来源无关的态，
允许其依赖已公开的 $n$ 和所请求的操作，却不依赖 $s,t$。选择未知来源的外部原始记录可以保留，
但不作为该处理器的可读输入；若处理器能读它，就必须把它列入 $G_{s,t}$。
特别地，正交的完整树标签是源相关输入，不是固定 ancilla。

确定性处理器是一条对所列输入共同作用的 CPTP 通道。精确带成功旗标的处理器是一套
迹和保持的 CP 仪器：成功支输出指定纯态，两个测试输入的成功概率相同为 $p$；所有失败支、
其记录和 Stop 均保留，失败总概率为 $1-p$。允许细分成功或失败记录、有限反馈和输入无关
随机化，比较时包含其诱导的完整仪器。若制备本身带失败旗标，完整律还须保留制备失败；
下文的 $p$ 针对明确供应的迹一输入。对质量 $q_i$ 的实际进入分支，成功质量为 $q_ip$，
不能把未进入质量 $1-q_i$ 删除，也不能用源相关的制备记录冒充固定输入。

**定理 51.2（两种方向的实际反例与精确成功成本）。** 对每个有限 $n\ge1$ 和两种 $X$，
(51.1) 的构造、分解都不存在全来源确定性仅由状态决定的处理器。更精确地：

1. 在构造限制 $(s,t)\in\{(\alpha,\alpha),(\beta,\alpha)\}$ 上，最优相等成功概率为

$$
p_{\rm con}(n)=\frac{1-a}{1-a\sqrt b}<1,
\qquad \lim_{n\to\infty}p_{\rm con}(n)=\frac23.
\tag{51.2}
$$

2. 在分解限制 $(s,t)\in\{(\alpha,\beta),(\beta,\alpha)\}$ 上，最优相等成功概率为

$$
p_{\rm dec}(n)=\frac{1-a}{1-a^2}=\frac1{1+a}<1,
\qquad \lim_{n\to\infty}p_{\rm dec}(n)=\frac12.
\tag{51.3}
$$

“最优”在此只量化各自的两个输入，允许任意数学 CP 仪器；它不是全来源共同可达到性，
也不是原生五模菜单的可达到性。任何全来源、等成功的仪器都须服从这些限制上的相应上界。

证明。叶 $\alpha,\beta$ 的着色场均为空且标签不同，所以两种核都给重叠 $a$。
构造的两个乘积输入的重叠是 $a$；目标 $\langle\alpha,\alpha\rangle$ 的根着色为 $1$，
$\langle\beta,\alpha\rangle$ 的场为空。由 (45.9)、(46.3) 得目标重叠 $a\sqrt b$。
分解的两个输入 $\langle\alpha,\beta\rangle,\langle\beta,\alpha\rangle$ 场均为空，
重叠为 $a$，而两个目标乘积的重叠为 $a^2$。所有这些数均为正实数。

这里消费 Chefles–Jozsa–Winter，
[*On the existence of physical transformations between sets of quantum states*，
quant-ph/0307227v1，定理 2–3](https://arxiv.org/html/quant-ph/0307227v1)
的纯族和带旗标 Gram 条件。所需二输入情形可直接计算：设输入单位向量内积为
$c$，目标内积为 $d$，其中 $0\le d<c<1$。成功纯输出的环境向量内积记为 $g$；
把全部失败记录、系统及环境一起保留后的归一失败向量内积记为 $f$。
等距扩张和正交旗标给

$$
c=p\,d\,g+(1-p)f,\qquad |g|\le1,\quad |f|\le1,
\qquad c\le pd+1-p.
\tag{51.4}
$$

端点 $p=0,1$ 用对应非空分支解释，无须给零支定义归一态。
因此 $p\le(1-c)/(1-d)<1$。在这个上界处，取共同成功环境、共同失败向量 $F$，令

$$
u_i\longmapsto\sqrt p\,w_i\otimes|\mathrm{success}\rangle
 +\sqrt{1-p}\,F\otimes|\mathrm{failure}\rangle\quad(i=0,1).
\tag{51.5}
$$

两边 Gram 相同，故在二输入张成空间上定义等距，扩张后给完整仪器；每支终止并保留
其旗标。它证明二输入达到性，未指定其他源的像。固定混合 ancilla 可先纯化到同一固定
辅助态，不能改善 (51.4)。代入 $(c,d)=(a,a\sqrt b)$ 和 $(a,a^2)$ 得两式。
令 $h=1/(5n)$，则 $1-(1-h)^{3/2}\sim3h/2$，给第一极限；第二极限直接由 $a\to1$。
任一全来源确定性通道也应在相应二输入限制上有 $p=1$，所以均被排除。∎

**命题 51.3（源标签、环境信息与小缺陷的界限）。** 定理 51.2 不禁止在完整树语法上
计算构造子，也不禁止在另供目标态制备服务下读取正交标签后重制备。它排除的是定义 51.1
的固定辅助输入合同。小的核乘法缺陷 (45.8)、(46.10) 本身不提供成功趋一的精确
构造／分解，也不等同于近似通道的误差界。

证明。若完整可读标签为 $|s,t\rangle$，不同来源输入的 Gram 内积为零；定理 51.2
计算的输入内积不再适用。测标签后调用另供的制备，数学上可给所需输出，但该服务及
源标签均在完整合同中增加资源。反之，固定辅助态不改输入内积，所以同一定理仍适用。
两项缺陷上界随 $n$ 消失，而 (51.2)、(51.3) 的极限严格小于一；这是精确带旗标转换
的反例。它不计算允许有误差时的最优成功率，也不把成功概率损失称为态距离。∎

## 52. 实际单孔上下文对根态表示的定量约束

**定义 52.1（只有一个未知孔的上下文）。** 令

$$
A_0=\alpha,\quad A_{j+1}=\langle A_j,A_j\rangle,\qquad
F_0[x]=x,\quad F_{j+1}[x]=\langle F_j[x],A_j\rangle.
\tag{52.1}
$$

$F_j$ 只有一个孔，已知右侧树不依赖未知 $x$，且 $F_j[\alpha]=A_j$。
记 $B_j=F_j[\beta]$。$A_j,B_j$ 均有 $2^j$ 个叶、$2^{j+1}-1$ 个总节点；
上下文的孔外固定部分有 $2^j-1$ 个叶。$j$ 是孔深度，不是展开后的树大小。
这里请求的根到上下文操作是
$\pi_\alpha^X\mapsto\pi_{A_j}^X$、$\pi_\beta^X\mapsto\pi_{B_j}^X$，
而不是取得原树标签后的语法运算。

**定理 52.2（单孔族的态距离与原始事件界）。** 对全部 $j\ge0$、$n\ge1$ 和两种 $X$，

$$
K_n^X(A_j,B_j)=a b^{j/2}.
\tag{52.2}
$$

任意仅由状态决定的共同 CPTP 处理器 $\Phi_j$，若输出在各自目标载体上，记
$D(\rho,\sigma)=\|\rho-\sigma\|_1/2$，则其二输入最坏态误差满足

$$
\max_{t\in\{\alpha,\beta\}}
D\bigl(\Phi_j(\pi_t^X),\pi_{F_j[t]}^X\bigr)
\ge \frac{\sqrt{1-a^2b^j}-\sqrt{1-a^2}}2.
\tag{52.3}
$$

在目标输出后使用定义 47.1 的 $A_j$ 破坏性查询，完整两记录为
$(+,\mathrm{Stop})$、$(-,\mathrm{Stop})$。只要求这一事件概率的两输入最坏误差 $e_j$
也必须满足

$$
e_j\ge\frac12\bigl[1-a^2b^j-\sqrt{1-a^2}\bigr]_+,
\qquad [u]_+=\max\{u,0\}.
\tag{52.4}
$$

特别在 $n=1,j=3$，这是实际八叶上下文，正事件的目标概率分别为
$1$、$1024/3125$，所以

$$
e_3\ge\frac12\left(\frac{2101}{3125}-\frac35\right)
=\frac{113}{3125}>0.
\tag{52.5}
$$

证明。$A_j,B_j$ 只在最左叶不同，故不同且有上述节点数。沿左脊比较：$A_j$ 的各个
内部节点都有相等子树，颜色非零；$B_j$ 左脊上的左右子树不同，颜色为零；其余地址上
子树完全相同。恰有 $j$ 个不同着色地址，各自的局部内积在两模型中都是 $\sqrt b$。
delta 项为零，(45.4)、(46.6) 给 (52.2)，$j=0$ 也成立。

两个单位纯态的距离为 $\sqrt{1-|\langle u,v\rangle|^2}$：在两向量张成空间中，
差密度的两个非零特征值为 $\pm\sqrt{1-|\langle u,v\rangle|^2}$。
共同 CPTP 通道的距离收缩，加上两个目标误差的三角不等式，给

$$
\sqrt{1-a^2b^j}
\le D(\pi_{A_j}^X,\Phi_j(\pi_\alpha^X))
 +\sqrt{1-a^2}
 +D(\Phi_j(\pi_\beta^X),\pi_{B_j}^X),
\tag{52.6}
$$

即 (52.3)。目标正事件差为 $1-a^2b^j$；实际输出在同一个效果上的概率差至多为
输入距离 $\sqrt{1-a^2}$。用两侧事件误差包住这个差得 (52.4)。在 $a=b=4/5$ 时，
$a^2b^3=1024/3125$，输入距离为 $3/5$，得到 (52.5)。负事件质量是正事件的补数，
故两条完整记录同时被比较，没有删掉任何失败质量。
距离收缩及效果判别是成熟中间工具，参见
[Watrous，*The Theory of Quantum Information*，第 3 章，定理 3.4、推论 3.40](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf)；
源特定部分是 (52.1) 的合法单孔族及其精确地址差异。∎

**推论 52.3（两个极限的资源口径）。** 固定 $n$ 而 $j\to\infty$ 时，(52.3) 的右端趋于
$\bigl(1-\sqrt{1-a^2}\bigr)/2>0$。若取 $j=5n$ 并令 $n\to\infty$，它趋于
$\sqrt{1-e^{-1}}/2>0$。这些是共同通道的必要误差下界，不是最优达到性。
第二个极限使用 $2^{5n}$ 叶的移动上下文；不能据此声称固定大小、固定来源或统一
制备成本下仍有同样放大。

证明。第一式由 $b^j\to0$；第二式由
$a^2b^{5n}\to e^{-1}$ 和 $a\to1$。节点数由定义 52.1 直接给出。∎

## 53. 独立局域实现的相对共轭自由度

**假设 53.1（另供的双系统与整个局域菜单）。** 对两个可分别指定的尺度 $n,m\ge1$，
供应 $\widetilde H_n\otimes\widetilde H_m$ 及独立制备
$\pi_s^{\mathrm c,n}\otimes\pi_t^{\mathrm c,m}$；每个局域空间带定义 47.1 的失败标记。
这不是把 $\langle s,t\rangle$ 的源态认作这个乘积。固定 (45.11)、(45.13) 的坐标实基，
第二空间的坐标共轭记为 $C$，$\bar Y=CYC$。

比较两种模型：同向模型使用 $v_t^{\mathrm c,m}$ 及局域仪器 $\mathcal J_{a|u}$；
反向模型使用 $Cv_t^{\mathrm c,m}$ 及整个对应菜单

$$
\overline{\mathcal J}_{a|u}(Y)
=C\mathcal J_{a|u}(CYC)C.
\tag{53.1}
$$

若一支有 Kraus 算子 $M_{a,\ell}$，对应支为 $CM_{a,\ell}C$；它是复线性算子，
故对应映射仍为 CP。包括失败、Stop、任何另供的局域 Lüders 或等待仪器在内，
全部局域菜单都按此对应；不能只共轭制备而保留不对应的相位敏感仪器。

允许有限的局域仪器树、经典消息和历史反馈；每个固定随机种子下树有限、每条叶均 Stop，
没有共同深度上界要求。种子与输入系统独立，策略、记录和分支映射可测。
原始记录保留所有局域标签、结果、消息、随机选择和 Stop；局域失败按其菜单终止该侧，
不抹掉另一侧的记录。这里没有联合量子仪器、量子通信或共享纠缠辅助态。
共轭是两个模型之间的对应，不是一扇可执行的反酉门。

**定理 53.2（完整有限局域记录不能定相对方向）。** 在假设 53.1 下，同向与反向模型
对任意所述策略的完整原始记录有相同联合概率律，包括零质量历史、失败和 Stop。
这尤其适用于实际移动三源
$u_j=v_{W_{j,5n}}^{\mathrm c,n}$、$w_j=v_{W_{j,5m}}^{\mathrm c,m}$，$j=0,1,2$，
以及各自的定义 47.1 破坏性菜单。

证明。先固定随机种子。给定一个完整历史，初始未归一态是乘积；一条局域 CP 分支
只作用一侧，故每个尚存前缀仍是正算子的乘积 $A\otimes B$。
反向模型对应前缀为 $A\otimes\bar B$：第一侧操作不变，第二侧由 (53.1) 逐步保持对应。
经典选择在两侧模型的同一个记录上相同，Stop 不改质量。由于
$\operatorname{Tr}\bar B=\operatorname{Tr}B$ 对正迹类算子成立，每个前缀及叶的质量相同。
若质量为零，两者都保留零算子，不取条件态。多 Kraus 支和局域失败重制备也服从同一对应。

对可测种子空间 $(\Omega,\mu)$，用有限树中各分支的自然数编号形成可数的结果骨架字 $r$，
记其固定种子质量为 $p_\omega(r)$；不用的叶置零。具体控制参数、消息和 Stop 位置是
$(\omega,r)$ 的同一可测函数，可取连续值，不假定完整控制记录集可数。每个种子下两模型逐骨架相等且
$\sum_rp_\omega(r)=1$，故对任意可测 $B\subseteq\Omega$，

$$
\Pr(\omega\in B,r)=\int_Bp_\omega(r)\,d\mu(\omega),
\qquad \sum_r\int_\Omega p_\omega(r)\,d\mu(\omega)=1.
\tag{53.2}
$$

Tonelli 定理给归一化，不需共同树深界；再由同一可测记录函数推前，得到完整控制记录的相等。
同一可测经典后处理也保持相等。
这里把 §47 的完整记录论证用于另供的两个独立载体，未把局域对应提升为联合仪器对应。∎

## 54. 实际两尺度三源的八记录联合律

**假设 54.1（额外的联合相干拒绝仪器）。** 沿用假设 53.1 的独立制备，记
$w_j^{+}=w_j$、$w_j^{-}=Cw_j$，$\varepsilon\in\{+,-\}$ 表示第二局域实现方向。
初态为 $\Psi_0^\varepsilon=u_0\otimes w_0^\varepsilon$。在对应模型中另供

$$
\begin{aligned}
P_j^\varepsilon&=|u_j\rangle\langle u_j|\otimes
 |w_j^\varepsilon\rangle\langle w_j^\varepsilon|,\\
Q_1^\varepsilon&=I-P_1^\varepsilon,\\
\mathcal L_+^\varepsilon(Y)&=P_1^\varepsilon YP_1^\varepsilon,
&\mathcal L_-^\varepsilon(Y)&=Q_1^\varepsilon YQ_1^\varepsilon.
\end{aligned}
\tag{54.1}
$$

这些投影在局域失败空间上按零延拓，$I$ 是完整双系统空间的恒等。
先记录联合旗标 $\sigma$，再在第一侧使用 $u_2$ 的定义 47.1 破坏性查询，
在第二侧使用 $w_2^\varepsilon$ 的对应查询，分别记录 $\tau,\upsilon$。
两次局域查询在每个联合旗标下都执行；第一侧失败仅使第一侧 Stop，不取消第二次查询。
全部局域失败标记、两个结果和最终 Stop 均保留。因此完整终端字有八种
$(\sigma,\tau,\mathrm{Stop}_A,\upsilon,\mathrm{Stop}_B,\mathrm{Stop})$，不是四种；
以下用 $(\sigma,\tau,\upsilon)$ 简记其中固定的 Stop 和由正负结果确定的失败标记。
联合负支 (54.1) 是额外供应，不能由 $P_1^\varepsilon$ 的乘积形式推出。

**定理 54.2（完整原始律、相对方向间隙及其退化）。** 对尺度 $l\in\{n,m\}$，令
$k_l=5l$，并记实际三源的

$$
\begin{aligned}
x_l&=|\langle v_{W_{1,k_l}},v_{W_{0,k_l}}\rangle|^2
     =a_l^2b_l^{k_l},\\
y_l&=|\langle v_{W_{2,k_l}},v_{W_{1,k_l}}\rangle|^2
     =a_l^2b_l^{2k_l}(b_l^2+h_l^2)^{k_l},\\
z_l&=|\langle v_{W_{2,k_l}},v_{W_{0,k_l}}\rangle|^2
     =a_l^2b_l^{3k_l},\\
B_l&=\mathcal B_l=a_l^3[b_l^3(b_l+ih_l)]^{k_l}.
\end{aligned}
\tag{54.2}
$$

向量均取各自尺度，内积第一项共轭线性。令
$x=x_n,y=y_n,z=z_n$、$x'=x_m,y'=y_m,z'=z_m$、$X=xx'$，
$B=B_n$，同向模型取 $D=B_m$，反向模型取 $D=\overline{B_m}$。
则八记录完整律为下表，各行末尾都有 Stop：

| $(\sigma,\tau,\upsilon)$ | 未归一原始概率 |
| --- | --- |
| $(+,+,+)$ | $Xyy'$ |
| $(+,+,-)$ | $Xy(1-y')$ |
| $(+,-,+)$ | $X(1-y)y'$ |
| $(+,-,-)$ | $X(1-y)(1-y')$ |
| $(-,+,+)$ | $zz'+Xyy'-2\operatorname{Re}(BD)$ |
| $(-,+,-)$ | $z(1-z')+Xy(1-y')-2\operatorname{Re}[B(x'-D)]$ |
| $(-,-,+)$ | $(1-z)z'+X(1-y)y'-2\operatorname{Re}[(x-B)D]$ |
| $(-,-,-)$ | $(1-z)(1-z')+X(1-y)(1-y')-2\operatorname{Re}[(x-B)(x'-D)]$ |

各项非负，前四项和为 $X$，后四项和为 $1-X$，总和为一。两方向律的差在前四项为零，
在后四项按表中顺序为 $(\delta_{n,m},-\delta_{n,m},-\delta_{n,m},\delta_{n,m})$，其中

$$
\begin{aligned}
\delta_{n,m}
&=p_{+}(-,+,+)-p_{-}(-,+,+)
 =4\operatorname{Im}B_n\operatorname{Im}B_m\\
&\ge4\left(\frac45\right)^{46}\sin^2 1>0,\qquad
\lim_{\substack{n\to\infty\\m\to\infty}}\delta_{n,m}
 =4e^{-8}\sin^2 1.
\end{aligned}
\tag{54.3}
$$

结论同时包含相同尺度 $n=m$ 和任意不同尺度 $n\ne m$。完整记录的总变差距离为
$2\delta_{n,m}$。若遗忘任何一侧的局域结果，只保留 $\sigma$ 与另一侧结果，则所得
四记录边缘律在两方向下相同。

证明。记 $c=\langle u_1,u_0\rangle$、$d=\langle w_1^\varepsilon,w_0^\varepsilon\rangle$。
联合正支向量为 $cd\,u_1\otimes w_1^\varepsilon$，给前四项。
联合负支向量为

$$
\Xi^\varepsilon=u_0\otimes w_0^\varepsilon
 -cd\,u_1\otimes w_1^\varepsilon.
\tag{54.4}
$$

令局域效果 $E_+=|u_2\rangle\langle u_2|$、$E_-=I-E_+$，第二侧对应为 $E'_\pm$。
破坏性仪器的迹效果就是它们，故负后两查询的质量为
$\langle\Xi^\varepsilon,(E_\tau\otimes E'_\upsilon)\Xi^\varepsilon\rangle$。
定义局域的三个数列

$$
\begin{array}{c|cc}
 &+&-\\ \hline
q_\tau&z&1-z\\
t_\tau&y&1-y\\
\kappa_\tau&B&x-B
\end{array}
\qquad
\begin{array}{c|cc}
 &+&-\\ \hline
q'_\upsilon&z'&1-z'\\
t'_\upsilon&y'&1-y'\\
\kappa'_\upsilon&D&x'-D.
\end{array}
\tag{54.5}
$$

由闭路积的方向约定，
$c\langle u_0,E_+u_1\rangle=\overline B$，而对补效果该数为 $x-\overline B$；
第二侧分别为 $\overline D,x'-\overline D$。
展开 (54.4) 的二次型即得统一公式

$$
p(+,\tau,\upsilon)=X t_\tau t'_\upsilon,\qquad
p(-,\tau,\upsilon)=q_\tau q'_\upsilon
 +Xt_\tau t'_\upsilon-2\operatorname{Re}(\kappa_\tau\kappa'_\upsilon).
\tag{54.6}
$$

这是表中全部八项。每项是正效果上的二次型，故非负；
$\sum q=\sum t=1$、$\sum\kappa=x$ 及其第二侧对应式给两个旗标质量
$X$ 与 $1+X-2X=1-X$。计算始终使用未归一向量；零历史、零质量正负支均保留，
不定义零支条件态。式 (54.2) 由 (45.20)–(45.21) 和 delta 项在互异三源上的消失给出。

写 $B=p+iq$、$B_m=s+it$，则
$\operatorname{Re}(BB_m)-\operatorname{Re}(B\overline{B_m})=-2qt$，
给 (54.3) 的第一式。补效果的 $\kappa_-$ 虚部反号，所以差呈所列交错排列。
绝对值之和为 $4\delta_{n,m}$，得到总变差距离；沿任一局域结果求和则相消。
由 (45.19)，$1<\arg B_l<5/4<\pi/2$，且
$|B_l|\ge(4/5)^{23}$，所以 $\operatorname{Im}B_l\ge(4/5)^{23}\sin1>0$。
由 (45.25) 的 $B_l\to e^{-4+i}$ 得双尺度极限。∎

**命题 54.3（全共轭、实闭路与局部四记录的边界）。** 表 (54.6) 对任意两个归一化
局域三元组都成立，包括重复、正交或零重叠情形。全体制备及仪器同时共轭保持八条概率；
只有相对共轭被 (54.3) 比较。若任一局域闭路积实，则两相对方向的完整八记录律相同。
若 $X=0$，联合正旗标全部为零；若 $X=1$，联合负旗标全部为零，两者均无条件化例外。

证明。推导 (54.4)–(54.6) 只用单位范数、投影和有限展开，不用重叠非零。
全共轭把每个 $\kappa_\tau\kappa'_\upsilon$ 取共轭，实部保持。
相对差恰由两虚部之积给出，故任一闭路积实即为零。$X=0,1$ 时由非负性和对应
旗标总质量立即得全支为零，不需要除以 $X$ 或 $1-X$。
例如只保留第一局域结果的四记录为

$$
\bigl(Xy,\ X(1-y),\ z+Xy-2x'\operatorname{Re}B,\
1-z+X(1-y)-2x'\operatorname{Re}(x-B)\bigr),
\tag{54.7}
$$

其中排列为 $(+,+),(+,-),(-,+),(-,-)$。它不依赖第二闭路的虚部，不能代替八记录律。
实际移动三源的 $0<x_l<1$、$\operatorname{Im}B_l>0$ 由 (54.2)、(45.19) 给出，
所以不落在这些退化情形。∎

## 55. 联合拒绝所要求的输出与替代编码

**定理 55.1（实际乘积输入的正质量纠缠拒绝支）。** 在假设 54.1 的实际乘积输入上，
联合拒绝的概率是 $q=1-x_nx_m>0$，其归一输出
$|\Xi^\varepsilon\rangle\langle\Xi^\varepsilon|/q$ 的 Schmidt 秩恰为二。
因此，只有局域 CP 仪器、经典协调、局域辅助态而无共享纠缠或量子通信的菜单，
不能在此输入上实现 (54.1) 的完整系统输出仪器。这个结论不等于禁止匹配其二值效果统计。

证明。$0<x_n,x_m<1$，故两侧的第零、第一个源向量分别线性独立，且 $cd\ne0$。
在正交基中写
$u_1=e_0$、$u_0=ce_0+\sqrt{1-x}\,e_1$，
$w_1^\varepsilon=f_0$、$w_0^\varepsilon=df_0+\sqrt{1-x'}\,f_1$。
在对应的 $2\times2$ 子空间中，(54.4) 的系数矩阵是

$$
M=\begin{pmatrix}
0&c\sqrt{1-x'}\\
d\sqrt{1-x}&\sqrt{(1-x)(1-x')}
\end{pmatrix},\qquad
\det M=-cd\sqrt{(1-x)(1-x')}\ne0.
\tag{55.1}
$$

所以 Schmidt 秩为二，范数平方由正交投影为 $q=1-xx'$。
每个局域协调历史在乘积输入上输出正的乘积算子，多 Kraus 和未读出的经典随机性
只给其可分离和。再在两侧分别投影到目标的二维局域支撑仍保持可分离性，
而该有限维可分离锥闭且凸，概率积分也在其中。
因此任何正质量局域后选择支的归一输出可分离，不可能等于该纠缠纯态。
此处不把共同共轭对应当作反酉操作，也不用外部纠缠参考来制造输入。∎

**命题 55.2（相同二值效果并非相同拒绝仪器）。** 令
$P_A=|u_1\rangle\langle u_1|$、$P_B=|w_1^\varepsilon\rangle\langle w_1^\varepsilon|$，
$Q_A=I-P_A,Q_B=I-P_B$。两侧分别作完整局域投影并保留四种结果时，
把“都正”作为二值正、其余作为二值负，可在任意输入上匹配
(54.1) 的二值概率。但负支的系统输出一般不同。

证明。三个负结果的效果之和为

$$
Q_A\otimes P_B+P_A\otimes Q_B+Q_A\otimes Q_B
=I-P_A\otimes P_B.
\tag{55.2}
$$

因此完整四记录经明确的二值后处理给相同旗标概率，原四记录仍可保留。
相应负输出是三个正交投影分支的非相干和，而 (54.1) 的负输出是它们先相加后
夹乘输入，含不同负子空间间的交叉项。在定理 55.1 的乘积输入上，前者为可分离态，
后者为纠缠纯态，故二者不同。后续两次破坏性查询会再破坏系统相干性，
只保留终端记录的测试与保留联合负支系统输出的仪器要求也必须分开。∎

**定理 55.3（固定中心测试的独立实标签模拟）。** 固定有限非空的第一、第二局域制备
标签集 $I,J$，固定尺度、方向及假设 54.1 的中心操作与后续查询。
记完整八记录为 $r$，其对独立制备 $(i,j)$ 的概率为 $p(r|i,j)$。
存在保持两源独立制备的实数、乃至对角经典实现，精确复现这个完整记录表。

证明。整个顺序测试可作为中心节点上的八结果 POVM：若
$R_+=P_1^\varepsilon$、$R_-=I-P_1^\varepsilon$，则

$$
H_{\sigma\tau\upsilon}
=R_\sigma(E_\tau\otimes E'_\upsilon)R_\sigma\succeq0,
\qquad \sum_{\sigma,\tau,\upsilon}H_{\sigma\tau\upsilon}=I.
\tag{55.3}
$$

其 Born 表即 $p(r|i,j)$，已包含全部失败和 Stop。
在实空间 $\mathbb R^I\otimes\mathbb R^J$ 中分别独立制备 $|i\rangle$、$|j\rangle$，
令中心效果为

$$
M_r=\sum_{i\in I,j\in J}p(r|i,j)|i,j\rangle\langle i,j|.
\tag{55.4}
$$

所有系数非负且逐 $(i,j)$ 求和为一，所以 $\{M_r\}$ 是实对角 POVM，
$\langle i,j|M_r|i,j\rangle=p(r|i,j)$。可以用经典抽样输出该三位记录及 Stop；
它精确匹配联合记录，并非只匹配一个成功率。
这是 Renou 等，
[*Quantum theory based on real numbers can be experimentally falsified*，
2101.10873v2，附录 D，式 (4)–(6)](https://arxiv.org/html/2101.10873v2)
的独立有限制备至中心节点模拟，在本八记录测试上的直接应用。
它改变源编码，把不同标签编码成正交实向量，不保持 (45.13) 的源 Gram、混合态仿射关系
或 (54.1) 的条件系统输出；故不与定理 51.2、55.1 冲突。
对有限多中心测试设置也可逐设置定义相应 POVM；这不供应保持空间分离局域菜单的网络模拟。∎

## 56. 来源、组合与物理重建的条件接口

**定义 56.1（源特定推论与成熟供应）。** §§51–55 的源特定推论为：
(51.1) 的两个真实源限制及其不同精确转换成本；(52.1) 的单孔上下文、指数树大小与
(52.3)–(52.5)；实际两尺度 (45.17) 在另供独立张量制备下的完整记录对应、
(54.2) 的参数接合、八记录律及一致相对方向间隙；实际乘积输入的纠缠拒绝支。
这些是所列来源上的条件综合推导，不主张纯态转换、迹距离、Bargmann 不变量、
局域共轭对应或实模拟本身的新颖性，也不作穷尽文献优先权主张。

原卷定理 10.4 已给未知态不可克隆及无扰动记录边界；命题 24.2 与 §27 已区分
共同表示、可调用仪器、跨描述比较与物理相干供应。§§45–50 的全源核、移动三源、
破坏性记录等价、单系统拒绝差异及全源秩障碍在这里直接复用。
[结构取得与谱扩展 §§4–5](AURIC_LANGLANDS_STRUCTURE_ACQUISITION_AND_SPECTRAL_EXTENSION_THEORY.md)
的二拷贝共轭商和相位参考结果量化的分别是指定全实联合效果及另供参考，
不替代这里的具体源到乘积对应。
[相位运输续卷 §12](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY_CONTINUATION.md)
的同密度重心操作障碍也不自动给树源构造子的转换成本。

成熟中间工具按各证明的精确范围使用：Chefles–Jozsa–Winter 的有限纯族／旗标 Gram 条件，
Watrous 的迹距离收缩和效果判别，以及 Renou 附录 D 的正交标签模拟。
Bargmann 环积的定义与规范不变性沿用 (45.18) 及
[Oszmaniec–Brod–Galvão，2109.10006v1，式 (1)](https://arxiv.org/html/2109.10006v1)，
不借其 cycle test 免费供应本源上的联合仪器。
[McKague–Mosca–Gisin，0810.1923v1，§§II.1、II.3](https://arxiv.org/html/0810.1923v1)
的实化及分布式相位辅助编码也不等于分别对两独立源作普通实化后仍自动保持全部联合菜单。
尤其 (48.4) 的全局实化不能直接认作两个独立局域实化的张量乘积。

**假设 56.2（原生实现与可证伪合同）。** 若把上述条件数学用于实际量子起源重建，
须分别供应并保持以下对应。

1. **来源与完整输入。** 每个可用源标签对应何种原生制备及全部原始记录，哪些辅助
   资料可读，哪些失败质量进入下一步。核中的 delta 提升是向量坐标，不是可无扰动读取的
   正交源标签服务。源相关记录如被供应，须重算完整输入而非沿用仅由状态决定的界。
2. **独立组合。** 实际独立重复制备、子系统分解、张量输入和保留系统输出的对应；
   源嫁接、树地址分解与独立量子乘积分别有自己的合同。
3. **仪器与比较。** 全局相位参考、所列完整局域菜单、联合拒绝映射及其分支输出，
   以及后续局域查询。仅符合 (55.2) 的二值效果不足以满足这个合同；
   只匹配一个终端记录表也不足以认证指定源编码和输出仪器。
4. **概率与动力学。** Born 标定、允许的相干制备、控制精度、时钟和动力学的物理对应。
   复局部向量 (45.3) 是模型输入，独立张量制备和 CP／投影仪器也是前提，
   不从 FIB 语法或信息守恒直觉单独推出。

在这些条件下，可证伪的数学合同分别为：无源相关辅助的二输入转换不可有超过
(51.2)、(51.3) 的相等精确成功率；根到八叶上下文的共同处理器不可把 (52.5) 的两输入
原始事件误差同时降至界下；全局域对应菜单必须有定理 53.2 的逐记录相等；
额外联合仪器必须满足八记录律，而保留其拒绝系统输出还须满足定理 55.1。
若物理读数违反某个合同，须检验完整输入、编码、仪器、独立性和概率对应中哪一项失效；
不能由违反这些条件定理直接判定源本体或标量域。

移动三源的叶数为 $1+2k_l,1+2k_l,1+4k_l$，$k_l=5l$；两个尺度可以不同。
(54.3) 的统一间隙依赖这些移动标签，不给固定标签或统一原生取得成本。
单孔放大的 $2^{5n}$ 叶成本与这些线性增长的梳树成本也不同。
完整源族的秩仍按 (50.1) 无界，有限三源的张成空间和实际五模载体 $\mathbb C^5$
仍须分别处理；§49 的五模原生障碍不能在未证载体对应时直接移作本双系统仪器的界。

Renou 附录 E 的实量子网络排除要求其纠缠双源、三方结构、中心测量及外侧局域设置，
正如[预测波第五卷假设 61.2](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_V.md)
所限定；本中心固定记录测试不供应那些网络条件，且已有定理 55.3 的实模拟。
这里确定的是“源构造—独立乘积—保留联合拒绝”三个接口的不同数学义务。
从这些条件推论到复结构的原生来源、Born／测量原则、可操作组合与动力学的闭合仍是
未解决的问题；相对方向的可见性不等于绝对共轭方向的选择，也不等于完整量子起源。

## 追加锚（本行以下为增补区）

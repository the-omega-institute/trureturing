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

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

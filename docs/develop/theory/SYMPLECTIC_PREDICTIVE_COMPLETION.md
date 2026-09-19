# 统一预测几何：动力学、热恢复、量子与电磁

> `generic-v1` 理论正文。本文是本研究线的唯一继续增补主卷。原分卷路径保留为章节跳转入口。已知文献构件、仓库推导、数值检错和 Lean 证明身份分别记录；本卷没有配套的完整 Lean 证明项，不产生冻结或开放问题结算身份。

**版本：** v2.0，2026-09-20。合编来源为 #8891 的四份理论正文与 #8899 的《预测充分性、热力学恢复与隐藏纤维复杂度》。重复定义和重复证明在这里合并，原结果的前件、结论、证明方法与反例在相应章节保留；后续新增结果在末尾追加锚下递增编号。

## 阅读入口与共同问题

| 章节 | 研究对象 | 要回答的问题 |
|---|---|---|
| [1](#sec-flow) | 生成元、余切提升、量子与耗散结构 | 一个演化规律怎样作用于状态、梯度、概率与振幅？ |
| [2](#sec-predictive) | 辛预测完成与 Gibbs 分解 | 哪些观测足以形成自治状态，什么几何与热结构随之保留？ |
| [3](#sec-windows) | 时间窗与全部导数层 | 有限时间和噪声下，哪些状态方向真正可恢复？ |
| [4](#sec-normal) | 正规算子连续幂帧 | 一个正时间窗上的稳定恢复能否传到任意正时间窗？ |
| [5](#sec-correlation) | 热相关、隐藏记忆及数据证书 | 从边界相关数据能认证多少遗漏状态与预测误差？ |
| [6](#sec-thermal) | 完整量子代数、热恢复和复杂度 | 完美预测还缺少什么，才能恢复热态或高效计算？ |
| [7](#sec-em) | Lorentz 曲率、磁场与可辨识性 | 电磁耦合怎样改变观测能力，哪些参数仍不可辨识？ |
| [8](#sec-unified-results) | 本次合编后的综合推论 | 隐藏热信息、总信息、恢复风险与磁耦合如何共同变化？ |
| [9](#sec-sources) | 原结果迁移、引用与证明边界 | 各结论依赖哪些来源，哪些工作仍未完成？ |

共同数据是状态空间、演化生成元、观测映射、参考概率或热态、允许实验和误差度量。预测充分性、热恢复充分性、计算可达性分别判断。相同数值或形式不代替对象映射与假设核对。

实矩阵转置记为 $T$，复伴随记为 $\dagger$；所有对数为自然对数。$\|\cdot\|$ 为欧氏算子范数，$\|\cdot\|_1$ 为不含二分之一的迹范数。标准 Poisson 矩阵
$$
J=\begin{pmatrix}0&I\\-I&0\end{pmatrix}
$$
配合辛约定 $\omega(u,v)=u^TJv$、$\iota_{X_H}\omega=dH$，给出 $X_H=J\nabla H$。一般可逆反对称 Poisson 矩阵 $J_r$ 对应的辛形式矩阵为 $-J_r^{-1}$。符号 $M$、$G$ 等仅在所在章节定义，不把不同载体的缺陷当成同一个物理量。数学上的所有等价关系均限于所列载体。

<a id="sec-flow"></a>
## 1. 同一生成元的状态、梯度、概率与振幅

### 1.1 余切 Hamilton 提升与伴随配对

**定理 1.1。** 对 $C^2$ 向量场 $f_\theta:\mathbb R^d\to\mathbb R^d$，在局部流 $\Phi_t$ 存在且对变量、参数可微的区间，函数
$$
\mathcal H_\theta(x,p)=p^Tf_\theta(x)
$$
生成
$$
\dot x=f_\theta(x),\qquad \dot p=-Df_\theta(x)^Tp,
\qquad
\widetilde\Phi_t(x,p)=(\Phi_t(x),D\Phi_t(x)^{-T}p).
$$
这个提升保持典范一形式 $p^Tdx$，因而保持辛形式。若 $\dot{\delta x}=Df_\theta(x)\delta x$，则 $p^T\delta x$ 守恒。

**证明。** 分别对 $p,x$ 求偏导得到两条方程。$D\Phi_t$ 满足变分方程，逆转置的导数给出伴随方程。拉回一形式得到 $(D\Phi_t^{-T}p)^TD\Phi_tdx=p^Tdx$；对 $p^T\delta x$ 求导时两项相消。证毕。

终端损失 $\ell(x(T))$ 对应 $p(T)=\nabla\ell(x(T))$。初态与损失无显式参数依赖时，参数变分 $s$ 满足 $\dot s=Df_\theta s+\partial_\theta f_\theta\,\delta\theta$，因此
$$
\nabla_\theta\ell=\int_0^T(\partial_\theta f_\theta)^Tp(t)dt.
$$
其他情形加入初态拉回或显式偏导。对微分同胚离散层 $F$，$(x,p)\mapsto(F(x),DF(x)^{-T}p)$ 同样保持一形式；反向读为 $p_k=DF(x_k)^Tp_{k+1}$。非可逆层仍可拉回协向量，但不再自动定义同维辛微分同胚。这些构件属于余切提升、伴随法和 Neural ODE 的既有理论 [SS16, CRBD18]。

例：$\dot x=-ax$ 提升为 $\mathcal H=-axp$、$\dot p=ap$。压缩与对偶伸长保持完整面积；该构造本身没有改善数值条件数的保证。当前位置和一个点上的切线也不决定完整规律，例如 $\dot x=1$ 与 $\dot x=1+x$ 在 $x=0$ 有相同初始速度。

### 1.2 半密度的酉表示

**定理 1.2。** 光滑完整向量场在 $\mathbb R^d$ 上生成流时，
$$
(U_t\psi)(x)=|\det D\Phi_{-t}(x)|^{1/2}\psi(\Phi_{-t}(x))
$$
是 $L^2(dx)$ 上的强连续酉群。在紧支光滑测试函数上，其生成微分表达式为
$$
\partial_t\psi=-f\cdot\nabla\psi-\tfrac12(\operatorname{div}f)\psi,
\qquad
\widehat{\mathcal H}_f=-i\hbar(f\cdot\nabla+\tfrac12\operatorname{div}f).
$$
它满足
$$
\partial_t|\psi|^2+\operatorname{div}(f|\psi|^2)=0,
\qquad
\widehat{\mathcal H}_f=\tfrac12\sum_j(f_j\widehat p_j+\widehat p_jf_j),
\quad\widehat p_j=-i\hbar\partial_j.
$$

**证明。** 换元 $y=\Phi_{-t}(x)$ 时 Jacobian 抵消，给出等距性；链式法则给出群律。小时间内紧支集的流像位于共同紧集，由控制收敛及稠密性得强连续。微分流和 Jacobian 得到生成表达式。振幅方程与其复共轭相加给出输运式，乘积求导给出对称排序。自伴生成元由酉群确定，不能仅用形式对称性代替自伴性。证毕。

这是广义 Koopman–von Neumann 表示 [J20]。原始经典读数 $a(x)$ 仍是相互对易的乘法算子；一般量子可观测代数另行指定。

### 1.3 量子实化与虚时间下降

**定理 1.3。** 取 $\hbar=1$，令 $\widehat H=A_0+iB_0$ Hermitian，$A_0^T=A_0$、$B_0^T=-B_0$，$\psi=(q+ip)/\sqrt2$。Schrödinger 方程等价于
$$
\dot z=JS_{\widehat H}z,
\quad S_{\widehat H}=\begin{pmatrix}A_0&-B_0\\B_0&A_0\end{pmatrix},
\quad JS_{\widehat H}=\begin{pmatrix}B_0&A_0\\-A_0&B_0\end{pmatrix}.
$$
该流同时保持欧氏内积与辛形式。对归一化态的能量 $E=\langle\widehat H\rangle$，虚时间方程 $\partial_\tau\psi=-(\widehat H-E)\psi$ 保持范数，且
$$
\partial_\tau E=-2\operatorname{Var}_\psi(\widehat H)\le0.
$$

**证明。** 分离实虚部得到矩阵，其生成元反对称且 Hamilton；求内积与辛配对导数即得保持律。虚时间范数导数为零，能量导数为 $-2(\langle\widehat H^2\rangle-E^2)$。证毕。

射影实时间方向是 $-i(\widehat H-E)\psi$，与下降方向由复结构连接；归一化并模去整体相位给出 Kähler 纯态空间 [AS97, McA19]。本节 $S_{\widehat H}$ 不必正定，第 2 节的正定假设另行承担。

### 1.4 耗散、端口与热参考

对光滑储能 $V$，模型
$$
\dot z=(J-R)\nabla V+Bu,\quad J^T=-J,\ R\succeq0,
\quad y=B^T\nabla V
$$
满足 $\dot V=-\nabla V^TR\nabla V+y^Tu$。反对称性负责这项能量平衡；一般变量 Poisson 结构还须满足 Jacobi。封闭 GENERIC 模型 $\dot z=L\nabla E+M\nabla S$，在 $L^T=-L$、$M\succeq0$、$L\nabla S=0$、$M\nabla E=0$ 下满足 $\dot E=0$、$\dot S=\nabla S^TM\nabla S\ge0$，均由链式法则得到 [G97, VSM02]。

**定理 1.4（被动隐藏记忆）。** 设
$$
\dot x=(J_x-R_x)e-Ch+Bu,\quad
\dot h=C^Te+(J_h-R_h)h,\qquad e=\nabla V_x(x),
$$
其中矩阵固定、$J$ 反对称、$R$ 半正定。总储能 $V_x+|h|^2/2$ 的导数为 $-e^TR_xe-h^TR_hh+e^TBu$。消去 $h$ 后，记忆核为
$$
K(t)=Ce^{tA_h}C^T,\quad A_h=J_h-R_h,
$$
且保留项包括 $-Ce^{tA_h}h_0$ 与 $-\int_0^tK(t-s)e(s)ds$。其 Laplace 响应在 $\operatorname{Re}s>0$ 正实：若 $w=(sI-A_h)^{-1}C^Tv$，则
$$
\operatorname{Re}(v^\dagger\widehat K(s)v)
=(\operatorname{Re}s)\|w\|^2+w^\dagger R_hw\ge0.
$$

**证明。** 交叉功率 $-e^TCh+h^TC^Te$ 抵消。变参数公式给出消元；由 $A_h+A_h^T=-2R_h$ 计算 resolvent 二次型实部得到最后一式。证毕。

例：$A_h=\left(\begin{smallmatrix}-\gamma&\omega\\-\omega&-\gamma\end{smallmatrix}\right)$、$C=(g,0)$ 给出 $K(t)=g^2e^{-\gamma t}\cos\omega t$；正实性允许时域核变号。隐藏热浴加噪声 $\sqrt{2\beta^{-1}R_h}dW$，平稳协方差 $\beta^{-1}I$ 解 Lyapunov 方程，消元随机力协方差为 $\beta^{-1}K(t-s)$，$t\ge s$。可见耗散也需配套热噪声 [L16]。

若 $R_h\succeq\alpha I>0$、$U^TU=I$、$P_U=UU^T$，压缩 $A_r=U^TA_hU,C_r=CU$ 保持被动性。令 $\epsilon_0=\|(I-P_U)C^T\|$、$\epsilon_1=\|(I-P_U)A_hU\|$。对两半群的差使用 Duhamel，得到
$$
\|K(t)-K_r(t)\|\le\|C\|e^{-\alpha t}
(\epsilon_0+t\epsilon_1\|U^TC^T\|),
$$
$$
\int_0^\infty\|K-K_r\|dt\le
\|C\|(\epsilon_0/\alpha+\epsilon_1\|U^TC^T\|/\alpha^2)=:\epsilon_K.
$$
可见线性耗散 $R_x\succeq\zeta I>0$、直接输入、零初态时，两个 resolvent 的范数至多 $1/\zeta$，逆算子恒等式给出 $\|G-G_r\|_{H^\infty}\le\epsilon_K/\zeta^2$ 及对应 $L^2$ 输出误差。这些界不含未知模型的辨识误差。

量子有限维 Markov 生成元可使用 GKSL 形式；完全正性是额外结构 [L76]。例如 Bloch 收缩率 $(1,1,3)$ 虽保持 Bloch 球，其归一 Choi 特征值 $(1-2e^{-t}+e^{-3t})/4$ 在小正时间为负。Gibbs 不变的 CPTP 演化使相对熵收缩，而 $F(\rho)-F(\gamma_\beta)=\beta^{-1}D(\rho\Vert\gamma_\beta)$。满足相应详细平衡的类还有非交换梯度流表述 [CM17]。电路的双边对称化涨落耗散关系 $S_{VV}^{\rm sym}(\omega)=\hbar\omega\coth(\beta\hbar\omega/2)\operatorname{Re}Z(\omega)$ 给出一个实验接口 [C10]，不能与单边谱系数混用。

<a id="sec-predictive"></a>
## 2. 预测完成、辛约化与热分解

### 2.1 最小连续线性预测商

固定 $S=S^T\succ0$、$A=JS$、$H=z^TSz/2$、读数 $b=Cz$。定义
$$
W_0=\operatorname{im}C^T,\quad W_{k+1}=W_k+A^TW_k,
\quad W=\operatorname{span}\{(A^T)^kW_0:k\ge0\}.
$$
Cayley–Hamilton 给出 $W=W_{2n-1}$。取满行秩 $O$ 使其行空间为 $W$；$C=0$ 时单独取零维平凡商。

**定理 2.1。** 对全部 $t\ge0$ 有 $Ce^{At}z=Ce^{At}z'$，当且仅当 $Oz=Oz'$。存在唯一 $K$ 及某个 $D_0$ 使 $OA=KO,C=D_0O$。任何能决定全部未来读数的线性编码 $Rz$ 均满足 $\operatorname{rank}R\ge\operatorname{rank}O$。

**证明。** 相同未来在零时刻的各阶导数相同，即 $CA^k(z-z')=0$；反向由指数级数。行空间定义给出与 $O$ 的等价。闭包不变性给出 $K$，满行秩给出唯一性。充分的 $R$ 有 $\ker R\subseteq\ker O$，由秩公式得最小性。证毕。

这是一般观察商、无 carry 条件与未来词完成在连续线性载体上的实现；相关仓库接口见第 9 节。维数下界不针对任意不连续集合编码。

### 2.2 自动辛配对、最小能量提升及嵌套一致性

**定理 2.2。** 配对 $a^TJb$ 在 $W$ 上非退化。因此 $r=\dim W$ 为偶数，$J_r=OJO^T$ 可逆。令
$$
P=OS^{-1}O^T,\quad L=S^{-1}O^TP^{-1},\quad N=I-LO.
$$
则
$$
K=J_rP^{-1},\quad OL=I,\quad AL=LK,\quad AN=NA,
\quad NJO^T=0,\quad L^TJL=-J_r^{-1},
$$
$$
H_r(y)=\tfrac12y^TP^{-1}y=\min_{Oz=y}H(z),\qquad
H(z)=H_r(Oz)+\tfrac12(Nz)^TS(Nz).
$$
极小提升唯一，为 $Ly$。

**证明。** 若非零 $a\in W$ 与全部 $W$ 配对为零，由 $A^Ta\in W$ 应有 $a^TJA^Ta=0$，但该值为 $(Ja)^TS(Ja)>0$，矛盾。奇数阶反对称矩阵行列式为零，故维数偶。

满行秩给出 $P\succ0$。由 $AS^{-1}=J$ 得 $KP=J_r$。又 $L^TS=P^{-1}O$，故 $L^TSN=0$；每个约束纤维唯一写成 $Ly+w,Ow=0$，完成平方得极小值和能量分解。恒等式 $AS^{-1}+S^{-1}A^T=0$ 与 $KP+PK^T=0$ 给出
$$
LK=-S^{-1}O^TK^TP^{-1}=-S^{-1}A^TO^TP^{-1}=JO^TP^{-1}=AL.
$$
因此 $AN=NA$，并由 $JO^T=LJ_r$ 得 $NJO^T=0$。左乘 $L^TJ$ 得 $L^TJLJ_r=-I$，即辛提升公式。证毕。

若再用满行秩 $D$ 约化，且 $DK=K_2D$，则直接观测 $O_2=DO$ 与分步约化给出相同的
$$
P_2=DPD^T,\quad J_2=DJ_rD^T,\quad K_2=J_2P_2^{-1},
\quad L_2=PD^TP_2^{-1},\quad LL_2=S^{-1}O_2^TP_2^{-1}.
$$
证明是 $O_2A=K_2O_2$ 后应用同一构造并逐项相乘。它同时追踪能量与状态提升，和 Schur 消元次序接口相容。

去掉正定性时，$H=qp$ 给出 $\dot q=q,\dot p=-p$，一维 $q$ 已自治，故自动辛结论不再成立。

### 2.3 同一分解的 Gibbs、条件恢复与正则量子版本

取 $R$ 为 $\ker O$ 的欧氏正交基矩阵，$C_h=R^TSR$，$u=R^TNz$。坐标 $z=Ly+Ru$ 可逆。由第 2.2 节，$\dot y=Ky$、$\dot u=A_hu$，其中 $AR=RA_h$。

**定理 2.3。** Gibbs 概率在这些坐标中精确分解为
$$
\gamma_r\otimes\gamma_h,
\quad\gamma_r=N(0,\beta^{-1}P),\quad
\gamma_h=N(0,\beta^{-1}C_h^{-1}).
$$
Lebesgue 配分函数为
$$
Z=\kappa Z_rZ_h,\quad\kappa=|\det[L\ R]|,
\quad Z_r=(2\pi/\beta)^{r/2}\sqrt{\det P},
\quad Z_h=(2\pi/\beta)^{(2n-r)/2}/\sqrt{\det C_h}.
$$
两因子各由自身流保持。若 $D(\mu\Vert\pi_\beta)<\infty$，$\nu$ 为 $y$ 边缘，则恢复 $\mathcal R\nu=\nu\otimes\gamma_h$ 满足
$$
D(\mu\Vert\pi_\beta)-D(\nu\Vert\gamma_r)
=\int D(\mu(\cdot|y)\Vert\gamma_h)d\nu(y)
=D(\mu\Vert\mathcal R\nu).
$$
这是给定可见边缘的唯一最小超额自由能提升；该缺陷沿本节解耦可逆流守恒。

**证明。** 交叉能量为零，常数 Jacobian 在归一概率中抵消，在配分函数中保留。两块生成元分别满足协方差不变方程。条件密度比拆成边缘密度比与条件密度比，积分给出 KL 链式等式；非负性与零值条件给出唯一性。完整流和边缘流都可逆并保留对应参考，相对熵各自守恒。证毕。

**定理 2.4。** 有限个正则量子模式，采用 Schrödinger 表示、Weyl 对称二次量子化及共同 Schwartz 域。$\widehat y=O\widehat z$ 满足
$$
[\widehat y_i,\widehat y_j]=i\hbar(J_r)_{ij}I,
\qquad \partial_t\widehat y=K\widehat y.
$$
可见 Weyl 子代数不变，约化 Hamilton 算子是 $\widehat y^TP^{-1}\widehat y/2$。存在与预测子空间相容的正则坐标及 metaplectic 酉实现，使
$$
\widehat H=\widehat H_r\otimes I+I\otimes\widehat H_h,
\quad \gamma_\beta=\gamma_{r,\beta}\otimes\gamma_{h,\beta},
\quad Z_\beta=Z_{r,\beta}Z_{h,\beta}.
$$
各正定块的配分函数为 $\prod_j[2\sinh(\beta\hbar\omega_j/2)]^{-1}$。有限二阶矩态还满足 $\Sigma_r=O\Sigma O^T$ 和 $\Sigma_r+i\hbar J_r/2\succeq0$，该条件由约化流保持。

**证明。** CCR 对二次对称乘积的交换子给出 $\partial_t\widehat z=JS\widehat z$，再用 $OA=KO$。$NJO^T=0$ 使隐藏与可见线性算子对易。$\operatorname{im}L$ 与 $\ker O$ 辛正交，各自非退化；在两块选 Darboux 基，能量交叉项仍为零。有限模 metaplectic 协变性和 Williamson 对角化给出两个张量因子与振子谱；几何级数证明热迹收敛。对 $X=\sum_jc_j(\widehat y_j-\langle\widehat y_j\rangle)$ 用 $\langle X^\dagger X\rangle\ge0$ 得不确定性式；$KJ_r+J_rK^T=0$ 保证其合同保持。证毕。[W12, ZGPG18, ZLDP23]

有限模不等于有限 Hilbert 维数；有限维矩阵不能承担非零常数 CCR。均值闭合不认领一般量子态的完整恢复。

### 2.4 有限误差的预测与辛结构余量

现在只要求 $O$ 满行秩，不假设闭合，仍定义 $P,J_r,K$。令
$$
\epsilon=\|P^{-1/2}(OA-KO)S^{-1/2}\|,
\quad Q=P^{-1/2}OS^{-1/2},\quad
\Omega=S^{1/2}JS^{1/2},\quad D=Q\Omega Q^T.
$$
**定理 2.5。** 对 $t\ge0$，
$$
\|Oe^{At}z_0-e^{Kt}Oz_0\|_{P^{-1}}
\le t\epsilon\|z_0\|_S.
$$
若 $\omega_*:=\sigma_{\min}(\Omega)>\epsilon$，则
$$
\sigma_{\min}(D)\ge\sqrt{\omega_*^2-\epsilon^2}>0.
$$
因而潜状态维数为偶数。奇数维的任何 $O$ 必有 $\epsilon\ge\omega_*$。

**证明。** $A^TS+SA=0$ 与 $K^TP^{-1}+P^{-1}K=0$ 给出两边能量范数等距。误差满足 $\dot e=Ke+(OA-KO)e^{At}z_0,e(0)=0$，Duhamel 积分给第一式。$QQ^T=I$，$\Pi=Q^TQ$，且
$$
\epsilon=\|(I-\Pi)\Omega Q^T\|.
$$
对单位 $v$ 正交分解
$$
\|\Omega Q^Tv\|^2=\|Dv\|^2+\|(I-\Pi)\Omega Q^Tv\|^2
$$
即得第二式；奇数阶反对称 $D$ 有核。证毕。

四维 $S=I$、$Q=\left(\begin{smallmatrix}1&0&0&0\\0&4/5&3/5&0\end{smallmatrix}\right)$ 给 $\epsilon=4/5,\sigma_{\min}(D)=3/5,\omega_*=1$，精确取等。单行 $Q=(1,0,0,0)$ 给奇数维等号。给定矩阵的界不包括辨识误差。

### 2.5 非线性条件与可重建算例

对满射次浸没 $\Phi$，两个独立条件
$$
D\Phi J\nabla H=J_r\nabla h\circ\Phi,
\qquad D\Phi J D\Phi^T=J_r
$$
分别保证自治预测与 Poisson 配对保持。第一式由链式法则，第二式代入 $\nabla(a\circ\Phi)^TJ\nabla(b\circ\Phi)$ 得括号相容。它们没有从重建精度自动成立 [BGH23]。

非线性反例：在去掉原点的谐振平面，$\Phi(q,p)=(q+ip)/\sqrt{q^2+p^2}\in S^1$ 满足 $\Phi(z_t)=e^{-it}\Phi(z_0)$。相位是自治的一维预测状态，一维流形没有非退化二形式。

保留原六维有理算例：
$$
B_s=\begin{pmatrix}1&2&0\\2&-1&1\\0&1&2\end{pmatrix},
\quad T_s=\begin{pmatrix}I&B_s\\0&I\end{pmatrix},
\quad S_0=\operatorname{diag}(1,4,9,1,1,1),
$$
$$
S=T_s^{-T}S_0T_s^{-1},\quad
C=(1,1,0,0,0,0)T_s^{-1},\quad
O=\operatorname{rows}(C,CA,CA^2,CA^3).
$$
有 $T_s^TJT_s=J$、$CA^4=-4C-5CA^2$，且
$$
OJO^T=\begin{pmatrix}0&2&0&-5\\-2&0&5&0\\0&-5&0&17\\5&0&-17&0\end{pmatrix},
\qquad\det(OJO^T)=81.
$$
因此闭包维数为四；第 2.2 节的全部矩阵可在有理数域重建。

<a id="sec-windows"></a>
## 3. 时间窗、噪声与整个信息谱

### 3.1 一个窗口强迫有限稳定导数深度

令非零实或复 Hilbert 空间上的 $B,C$ 有界，$b=\max(1,\|B\|),c=\|C\|$，定义
$$
(\mathcal T_Tx)(t)=Ce^{tB}x,\quad
 a(T)=\inf_{\|x\|=1}\|\mathcal T_Tx\|_{L^2(0,T)}^2,
\quad\mu_N=\inf_{\|x\|=1}\sum_{k=0}^N\|CB^kx\|^2.
$$
**定理 3.1。** 对 $p_N(t;x)=\sum_{k=0}^Nt^kCB^kx/k!$，
$$
\|\mathcal T_Tx-p_N\|_{L^2}\le R_N(T)\|x\|,
\quad R_N(T)=\frac{ce^{bT}b^{N+1}T^{N+3/2}}{(N+1)!\sqrt{2N+3}}.
$$
若 $a(T_0)\ge a_0>0$，取使 $R_N(T_0)\le\sqrt{a_0}/2$ 的 $N$，则
$$
\mu_N\ge\frac{a_0}{4L_N(T_0)^2},
\quad L_N(T_0)^2=\sum_{k=0}^N\frac{T_0^{2k+1}}{(2k+1)(k!)^2}.
$$
这样的有限 $N$ 总存在。

**证明。** 指数级数余项至多 $ce^{bt}(bt)^{N+1}/(N+1)!$，平方积分给 $R_N$。固定 $T_0$ 时阶乘使其趋零。三角不等式给 $\|p_N\|\ge\sqrt{a_0}\|x\|/2$；对多项式有限和用 Cauchy–Schwarz 并积分，给出 $\|p_N\|^2\le L_N^2\sum_k\|CB^kx\|^2$。证毕。

若开始只给可数传感向量 $g_j$ 的积分上界 $M_0$，不预设完整分析算子有界：对有限集合 $F$ 比较常值轨迹 $C_Fx$ 与 $C_Fe^{tB}x$。取 $d=\min(T_0,\log(3/2)/b)$，二者算子差至多 $\sqrt d\|C_F\|/2$，而动态轨迹范数至多 $\sqrt{M_0}$。故 $\|C_F\|^2\le4M_0/d$，对有限和取极限得到初始 Bessel 性。

### 3.2 任意正窗、匹配幂次和最坏噪声

令 $H_N=(1/(i+j+1))_{0\le i,j\le N}$、$\lambda_N=\lambda_{\min}(H_N)>0$。若 $\mu_N\ge\mu>0$，设
$$
d_N=\sqrt{\lambda_N\mu}/N!,\quad
r_N=ce^bb^{N+1}/((N+1)!\sqrt{2N+3}),
$$
$$
\tau_N=\min(1,d_N/(2r_N)),\quad
\alpha_N=\lambda_N\mu/(4(N!)^2).
$$
则
$$
a(T)\ge\alpha_N\min(T,\tau_N)^{2N+1}>0.
$$
**证明。** 对 $t=Ts$ 的向量值多项式应用有限 Hilbert Gram 下界，得 $\|p_N\|^2\ge d_N^2T^{2N+1}\|x\|^2$，$T\le1$。余项至多 $r_NT^{N+3/2}\|x\|$；$T\le\tau_N$ 时不超过主项一半。较长时间用非负积分单调性。证毕。

于是存在一个稳定正窗、存在有限 $\mu_N>0$、全部正窗稳定三者等价。最小稳定深度 $m=\min\{N:\mu_N>0\}$ 有限时，
$$
a(T)=\Theta(T^{2m+1}).
$$
下界如上。上界由 $m\ge1$ 时 $\mu_{m-1}=0$ 的单位近核向量列，把低阶 Taylor 项送零，余项给出
$$
a(T)\le\frac{c^2e^{2b}b^{2m}}{(m!)^2(2m+1)}T^{2m+1},\quad T\le1.
$$
$m=0$ 用直接上界。这个证明也适用于无限维的统一稳定深度。

$L^2$ 加性噪声预算为 $\delta$、状态无先验限制时，所有重建器的最优最坏误差恰为 $\delta/\sqrt{a(T)}$。Moore–Penrose 左逆达到上界；反向取近似最弱单位方向 $v$，状态 $\pm\delta v/\|\mathcal T_Tv\|$ 各配相反噪声产生同一零数据，得下界。

取归一多项式 $\ell_0,\ldots,\ell_N$，有限积分矩
$$
(\mathcal M_Tx)_k=T^{-1/2}\int_0^T\ell_k(t/T)Ce^{tB}xdt
$$
保留以上短窗下界，噪声总范数不增加。证明是投影保持 $p_N$，投影余项收缩。数值求积误差另计，不需要高阶噪声差分。

### 3.3 全部分层、行列式与积分矩首项

有限维可观测 $(C,B)$ 中，令
$$
V_j=\bigcap_{k<j}\ker(CB^k),\quad
E_j=V_j\cap V_{j+1}^\perp,\quad d_j=\dim E_j,
\quad V_0=\mathbb R^d.
$$
令 $m$ 为 $V_{m+1}=0$ 的最小值，$D_T|_{E_j}=T^{j+1/2}I$。定义
$$
G_T=\int_0^Te^{tB^T}C^TCe^{tB}dt,
\quad \mathcal P(s)x=\sum_{j=0}^m\frac{s^j}{j!}CB^jx_j,
\quad M_*=\int_0^1\mathcal P(s)^T\mathcal P(s)ds.
$$
**定理 3.2。** $M_*\succ0$，且
$$
D_T^{-1}G_TD_T^{-1}=M_*+O(T),
\qquad\det G_T=T^{\sum_j(2j+1)d_j}(\det M_*+O(T)).
$$
每层有 $d_j$ 个排序特征值为 $\Theta(T^{2j+1})$。有限正交积分矩的 Gram 矩阵具有相同缩放极限和行列式首项。

**证明。** 对 $x_j\in E_j$，低于 $j$ 阶的导数为零，故 $\sqrt TCe^{TsB}D_T^{-1}x=\mathcal P(s)x+O(T)\|x\|$，在 $[0,1]$ 一致。若多项式的平方积分为零，每个系数 $CB^jx_j=0$；结合 $x_j\in V_j\cap V_{j+1}^\perp$ 得 $x_j=0$。于是极限正定，上下 Loewner 界及 Courant–Fischer 给整个谱幂次，行列式给首项。多项式投影保留极限，故积分矩亦然。证毕。

全谱幂次已有可控 Gramian 的对偶理论 [SJP15]；这里保留显式极限矩阵供热信息计算。

标量输出且 $m=d-1$、$V=\operatorname{rows}(C,CB,\ldots,CB^m/m!)$ 可逆时，
$$
\lim_{T\downarrow0}\frac{a(T)}{T^{2m+1}}
=\frac1{(H_m^{-1})_{mm}\|V^{-1}e_m\|^2}.
$$
证明：令 $D'_T=\operatorname{diag}(1,T,\ldots,T^m)$，$Ce^{TsB}V^{-1}(D'_T)^{-1}\to(1,s,\ldots,s^m)$，于是 $G_T=TV^TD'_TH(T)D'_TV,H(T)\to H_m$。缩放逆矩阵趋于 $(H_m^{-1})_{mm}(V^{-1}e_m)(V^{-1}e_m)^T$，取最大特征值。

### 3.4 Gaussian 信息、能量风险和恢复阈值

从轨迹像的正交积分坐标得到有限矩阵 $L_T$，使 $L_T^TL_T=G_T$。取 $X\sim N(0,\beta^{-1}I)$，数据 $Y=L_TX+\sigma\xi$，其中 $\xi$ 独立标准 Gaussian。这里噪声方差是每个归一积分坐标的方差，没有把白噪声当普通 $L^2$ 随机函数。

**定理 3.3。**
$$
\Sigma_T=(\beta I+\sigma^{-2}G_T)^{-1},\quad
\widehat X=\sigma^{-2}\Sigma_TL_T^TY,
$$
$$
I_T=\tfrac12\log\det(I+G_T/(\beta\sigma^2)),
\quad \mathcal R_T=\inf_{\widehat x}\mathbb E\tfrac12\|X-\widehat x(Y)\|^2
=\tfrac12\operatorname{tr}\Sigma_T.
$$
对于 $\mathcal F(p)=\mathbb E_p\|X\|^2/2-\beta^{-1}h(p)$，
$$
\mathbb E_Y[\mathcal F(p_{X|Y})-\mathcal F(p_X)]=\beta^{-1}I_T.
$$
若 $B^T=-B$，已知动力学下的未来最优能量风险仍为 $\mathcal R_T$。

**证明。** 先验与似然完成平方给后验；条件期望的正交性给风险。Gaussian 熵差给行列式。平均条件能量等于先验能量，条件熵差等于互信息，给自由能身份。正交流保持误差范数，且条件期望随已知线性映射交换。证毕。[SD14]

这是条件概率描述的自由能泛函，不直接等于实验已经耗散的热量。实测、反馈、擦除协议另定。

若 $\sigma^2=T^\alpha$，则
$$
I_T=\tfrac12\sum_jd_j(\alpha-2j-1)_+\log(1/T)+O(1).
$$
避开阈值 $\alpha=2j+1$ 时，$\mathcal R_T\to(2\beta)^{-1}\sum_{2j+1>\alpha}d_j$。全部风险趋零当且仅当 $\sigma^2=o(T^{2m+1})$。这些式子由各特征值逐项代入后验和互信息得到；阈值处不能只凭幂次给通用常数。固定噪声时 $I_T=T\operatorname{tr}(C^TC)/(2\beta\sigma^2)+O(T^2)$，首阶信息不识别深层方向。

### 3.5 两振子和采样时钟

取 $B=\operatorname{diag}(J_2,2J_2)$，$C_{\rm sum}=(1,0,1,0)$ 或分别读两个位置。前者深度 $m=3$，后者 $m=1$，并有
$$
a_{\rm sum}(T)\sim T^7/14000,\quad
\det G_{\rm sum}(T)\sim T^{16}/2688000,
$$
$$
a_{\rm sep}(T)\sim T^3/12,\quad
\det G_{\rm sep}(T)\sim T^8/36.
$$
常数来自 $(H_3^{-1})_{33}=2800$、$V^{-1}e_3=(0,2,0,-1)^T$、$\det V=3/2$、$\det H_3=1/6048000$；分别观测的频率块最小特征值为 $(T-|\sin\omega T|/\omega)/2$，行列式为 $(T^2-\sin^2(\omega T)/\omega^2)/4$。

二者 $\operatorname{tr}C^TC=2$，固定噪声首阶信息相同；噪声 $T^4$ 时，信息对数系数分别为 2 和 4，风险极限分别为 $1/\beta$ 和零。原高精度样本：$T=.1$ 时两种 $a(T)$ 为 $7.14507890954\times10^{-12}$ 与 $8.32916765859\times10^{-5}$；$T=.01$ 时为 $7.14287936503\times10^{-19}$ 与 $8.33329166677\times10^{-8}$。

**定理 3.4（时钟的共同闭包）。** 离散 $F=e^{\Delta A}$ 的观测闭包包含于连续闭包。若 $A$ 可对角化，且不同特征值的 $e^{\Delta\lambda}$ 不碰撞，则两闭包相同。对正定 Hamilton $A$，两正间隔之比无理时，混合词闭包
$$
\operatorname{span}\{(F_1^T)^k(F_2^T)^\ell W_0:k,\ell\ge0\}
$$
等于连续闭包。

**证明。** 连续不变空间对指数不变。单时钟无碰撞时，有限谱插值得 $A=p(F)$；两时钟时，不同纯虚频率不能同时具有相同相位对，否则频差给出两间隔的有理比。有限谱上的二元插值得 $A=p(F_1,F_2)$；可取实系数。故反向不变性成立。证毕。

单振子以周期采样只见恒定位置，离散闭包可降为一维。两条独立序列也不能代替混合词：令 $a=2\pi/\Delta_1,b=2\pi/\Delta_2$，函数
$$
g(t)=\cos((\omega+a+b)t)-\cos((\omega+a)t)
-\cos((\omega+b)t)+\cos(\omega t)
$$
在两个采样栅格均为零，但 $g''(0)=-2ab\ne0$。四个正定独立振子即可实现。精确无理比去混叠不提供有限噪声的统一条件数。

### 3.6 无界生成元的适用边界

圆周 $\mathbb R/2\mathbb Z$ 上平移群 $U_tf(s)=f(s+t)$，观察算子为乘以 $1_{[0,1]}$。Fubini 给 $\int_0^2\|CU_tf\|^2dt=\|f\|^2$，但 $T<1$ 时支撑于 $(1+T,2)$ 的非零函数在整个短窗不可见。其无界生成元不满足第 3.1 节的有界前件。仅有酉性不能删除最小观测时间。

<a id="sec-normal"></a>
## 4. 正规连续幂帧的时间窗不变性

本章保留 #8891 的具名问题证明稿，不把合编当成独立审定或新的问题结算。[AHP19, Conjecture 5.6] 及 [ACKM26, Conjecture 2] 提出从可逆自伴到 normal reductive 的推广。本章命题覆盖全部有界正规算子，不要求有界逆或 reductive 性。这里的存在性下界不附带第 3 节针对有界生成元的统一有限导数幂次。

### 4.1 精确陈述与解析族

令 $A$ 为非零复 Hilbert 空间上的有界正规算子，$g_j$ 为可数族。按 $\ell(\lambda)=\log|\lambda|+i\operatorname{Arg}\lambda$、$\operatorname{Arg}\lambda\in[-\pi,\pi)$ 定义谱幂，零谱点在 $t>0$ 取零。记
$$
\mathcal E_T(x)=\sum_j\int_0^T|\langle x,A^tg_j\rangle|^2dt.
$$
**定理 4.1。** 若一个有限 $T_0>0$ 上有 $a_0\|x\|^2\le\mathcal E_{T_0}(x)\le M_0\|x\|^2$，$a_0>0$，则每个有限 $T>0$ 上都有正的上下帧界。

内积对第一变量线性。令 $E_A$ 为谱测度、$r_A=\max(1,\|A\|)$，在 $\operatorname{Re}z>0$ 取
$$
R_z=\int_{\lambda\ne0}e^{z\overline{\ell(\lambda)}}dE_A(\lambda),
\quad R_0=I,
\quad V_v=\int_{\lambda\ne0}e^{iv\overline{\ell(\lambda)}}dE_A(\lambda)+E_A(\{0\}).
$$
则 $R_t=(A^t)^*$、$\|R_t\|\le r_A^t$、$\|V_v\|\le e^{\pi|v|}$，并有 $R_{u+iv}=R_uV_v$、$R_{s+u}=R_uR_s$，$u>0,s\ge0$。

$R_z$ 算子范数全纯：在 $\operatorname{Re}z\ge\varepsilon>0$ 的紧邻域，各阶乘子导数由 $\rho^{\operatorname{Re}z}(|\log\rho|+\pi)^ke^{\pi|\operatorname{Im}z|}$ 一致控制，并在 $\rho\downarrow0$ 时趋零；用较大紧邻域的二阶余项控制谱上确界差商。该证明不在零时刻对无界 $\log A$ 求算子范数导数。

### 4.2 初始分析映射可以无界的局部观测控制

对有限 $F$ 令 $C_Fx=(\langle x,g_j\rangle)_{j\in F}$。只使用原积分上界，取 $z_0=u_0+iv_0$、$\rho=\min(u_0/2,T_0/4)$、$s=\max(0,u_0-T_0/2)$，则
$$
\|C_FR_{z_0}x\|^2\le
\frac{2M_0}{\pi\rho}r_A^{2s}e^{2\pi(|v_0|+\rho)}\|x\|^2.
$$
**证明。** 全纯有限向量函数的范数平方次调和，在半径 $\rho$ 圆盘用面积平均。圆盘位于 $[s,s+T_0]\times[v_0-\rho,v_0+\rho]$。固定虚部时，半群律把实轴积分化为对初态 $R_sV_vx$ 的原窗口观测，至多 $M_0r_A^{2s}e^{2\pi|v|}\|x\|^2$。再积虚部得结论。证毕。

常数在右半平面的每个紧集上可统一，且独立于有限 $F$。对平方和单调取极限，完整正时间分析映射 $\mathcal C(z)x=(\langle R_zx,g_j\rangle)_j$ 属于 $\ell^2$ 并局部一致有界。

### 4.3 解析传播与主证明

标量全纯函数列若在右半平面局部一致有界，且在一个内部实区间的平方积分趋零，则在每个紧集一致趋零。证明是 Cauchy 估计、Arzelà–Ascoli 和紧集穷竭选出局部一致收敛子列；极限在该区间为零，由恒等定理全为零；每个子列都如此，故原列亦如此。

若单位有界 $x_n$ 的 $\int_0^T\|\mathcal C(t)x_n\|^2dt\to0$，则其完整系数范数在每个紧集一致趋零。否则选择违例点 $z_n$、有限 $F_n$ 和单位测试向量 $v_n$，使 $|\langle C_{F_n}R_{z_n}x_n,v_n\rangle|$ 保持正下界；这些标量全纯函数有上一节统一界，在 $[T/4,T/2]$ 的积分趋零，与标量传播矛盾。没有使用无限维值域的错误 Montel 紧性。

较长窗口的上界用 $N=\lceil T/T_0\rceil$ 分块可取 $M_T=M_0\sum_{k=0}^{N-1}r_A^{2kT_0}$。$T\ge T_0$ 的下界直接来自单调性。若 $0<T<T_0$ 的下界失败，取单位 $x_n$ 使 $\mathcal E_T(x_n)\to0$，置 $d=T/2$；前述传播使 $\sup_{[d,T_0]}\|\mathcal C(t)x_n\|\to0$。于是
$$
\mathcal E_{T_0}(x_n)\le\mathcal E_T(x_n)
+(T_0-d)\sup_{[d,T_0]}\|\mathcal C(t)x_n\|^2\to0,
$$
与 $a_0$ 矛盾。定理 4.1 得证。

若 $A$ 有非零核，正时间读数在核上全零，主假设已排除它；零仍可为连续谱点。负实谱上只用 $(A^t)^*$，不能偷换为同主值分支的 $(A^*)^t$。

### 4.4 有界对数特例与零谱聚集实例

$A$ 有有界逆时，$Q=(\log|z|+i\operatorname{Arg}z)(A)$ 是有界 Borel 演算，不要求谱邻域有全纯对数，且 $A^t=e^{tQ}$。第 3.1 节的 Bessel 引理与任意正窗定理立即给出可逆特例。

在 $\ell^2(\mathbb N_{\ge1})$ 上取 $Ae_n=e^{-n}e_n$、$g_n=\sqrt{2n}e_n$，则
$$
\mathcal E_T(x)=\sum_{n\ge1}(1-e^{-2nT})|x_n|^2,
\quad a(T)=1-e^{-2T},\quad M(T)=1.
$$
初始族非 Bessel，$A^{-1}$ 无界，但所有正窗均稳定。该实例由逐坐标积分得到。

<a id="sec-correlation"></a>
## 5. 热相关、隐藏记忆和有限数据证书

### 5.1 从相关曲率读取闭包缺陷

正定二次系统中取 Gibbs 初态 $z_0\sim N(0,\beta^{-1}S^{-1})$，$y_t=Oz_t$，$O$ 满行秩。令
$$
C(t)=\mathbb E[y_ty_0^T],\quad
F(t)=C(0)^{-1/2}C(t)C(0)^{-1/2}.
$$
第 2 节坐标给 $F(t)=Qe^{t\Omega}Q^T$、$QQ^T=I$、$\Omega^T=-\Omega$。因此 $F(0)=I,F(-t)=F(t)^T,\|F(t)\|\le1$。这是假定的平稳 Gibbs 初态，不推出单条轨迹遍历性。

**定理 5.1。** 令 $\Pi=Q^TQ$、$D=F'(0)$，则
$$
M:=D^2-F''(0)=((I-\Pi)\Omega Q^T)^T((I-\Pi)\Omega Q^T)\succeq0,
\quad \epsilon^2=\|M\|.
$$
$M=0$ 等价于精确闭包。未白化的表达为
$$
M=C(0)^{-1/2}[C'(0)C(0)^{-1}C'(0)-C''(0)]C(0)^{-1/2}.
$$
**证明。** $F''(0)=Q\Omega^2Q^T$，用 $\Omega^T=-\Omega$ 展开右侧 Gram 得 $D^2-Q\Omega^2Q^T$。零 Gram 等价于不变子空间，转回坐标即 $OA=KO$。证毕。

### 5.2 记忆、随机力与当前状态预测风险

取 $V$ 使 $\binom QV$ 正交，$\xi_0=\sqrt\beta S^{1/2}z_0\sim N(0,I)$，$u=Q\xi,v=V\xi$。设 $B_h=V\Omega Q^T,E_h=V\Omega V^T$。则
$$
\dot u=Du-B_h^Tv,\quad\dot v=B_hu+E_hv.
$$
变参数消元给
$$
\dot u(t)=Du(t)-\int_0^t\Lambda(t-s)u(s)ds+\eta(t),
\quad\Lambda(t)=B_h^Te^{tE_h}B_h,
\quad\eta(t)=-B_h^Te^{tE_h}v_0.
$$
独立标准高斯 $u_0,v_0$ 及 $E_h$ 反对称给出
$$
\mathbb E\eta(t)\eta(s)^T=\Lambda(t-s),\quad
\Lambda(0)=M,\quad\|\Lambda(t)\|\le\|M\|.
$$
乘以 $u_0^T$ 取期望，得 $F'=DF-\Lambda*F$。再一次 Duhamel 与三角域积分得到
$$
\|F(t)-e^{tD}\|\le\tfrac12t^2\|M\|.
$$
这是条件均值的界，不能替代任意隐藏初态的 $O(\epsilon t)$ 轨迹界。有限封闭系统的记忆可不衰减 [M65, M65C, LL26, LL25]。

**定理 5.2。** 对任意可测平方可积 $f(u_0)$，
$$
\mathbb E\|u_t-f(u_0)\|^2=\operatorname{tr}G_t+
\mathbb E\|F(t)u_0-f(u_0)\|^2,
\quad G_t=I-F(t)F(t)^T.
$$
故最小风险为 $\operatorname{tr}G_t=t^2\operatorname{tr}M+O(t^4)$。

**证明。** 分解初态 $\xi_0=Q^Tu_0+V^Tv_0$，得到条件均值 $F(t)u_0$ 和协方差 $Qe^{t\Omega}(I-\Pi)e^{-t\Omega}Q^T=G_t$。条件期望正交性给风险分解。矩阵 Taylor 首项为 $t^2M+O(t^3)$，而迹 $r-\|F(t)\|_F^2$ 是偶函数，故迹余项从四阶开始。证毕。

这是当前输入和 Gibbs 先验下所有预测器的共同下限。增加历史或传感器会改变条件化对象。

### 5.3 从相关导数恢复必要状态秩

块矩阵
$$
\mathcal H_m=[(-1)^iF^{(i+j)}(0)]_{i,j=0}^m
$$
等于 $[Q^T,\Omega Q^T,\ldots,\Omega^mQ^T]^T[Q^T,\Omega Q^T,\ldots,\Omega^mQ^T]$。每个块由反对称性直接核对，故其秩就是相应预测闭包维数。特别地
$$
\mathcal H_1=\begin{pmatrix}I&D\\-D&-F''(0)\end{pmatrix},
\qquad\operatorname{rank}\mathcal H_1=r+\operatorname{rank}M,
$$
因为消去首块后的 Schur 补为 $M$。这只给第一轮增加的方向，最终维数须继续补全；有限精度应使用谱余量而非精确秩。

### 5.4 一个有限延迟的偏差与最优误差阶

已知 $\|\Omega\|\le b$，定义
$$
W_h=\frac{2I-F(h)F(h)^T-F(h)^TF(h)}{2h^2}.
$$
**定理 5.3。** $W_h\succeq0$。若 $\|\widehat F_h-F(h)\|\le\delta$，则
$$
\|\widehat W_h-M\|\le
\eta(h,\delta):=\tfrac23b^4h^2+(2\delta+\delta^2)/h^2.
$$
大于 $\eta$ 的估计特征值个数是 $\operatorname{rank}M$ 的可靠下界。

**证明。** $F$ 收缩给出半正定性。对 $P_t=F(t)F(t)^T$，有 $P''_0=-2M$ 和 $\|P_t^{(4)}\|\le16b^4$；双向 Taylor 给 $2b^4h^2/3$。每个乘积的数据扰动至多 $2\delta+\delta^2$。对称特征值的极小极大表述给最后结论。证毕。

该上界在 $h_*^4=3(2\delta+\delta^2)/(2b^4)$ 处最小。带宽不可省：$\omega h=2\pi$ 的振子有 $F(h)=1,W_h=0$，但 $M=\omega^2$。

**定理 5.4。** 只给一个标量延迟值 $d$、$|d-F(h)|\le\delta$，$F(0)=1$ 已知，模型为频率在 $[1,3]$ 内的有限正定振子，允许 $0<h\le h_0$ 且 $h_0$ 固定充分小。估计 $M=-F''(0)$ 的最优最坏误差为 $\Theta(\sqrt\delta)$。

**证明。** 上界取 $b=3,h\asymp\delta^{1/4}$。下界第一组为 $F_a(t)=\cos2t$ 与 $F_b(t)=(1-p_h)\cos t+p_h\cos3t$，其中 $p_h=(\cos h-\cos2h)/(\cos h-\cos3h)$。充分小 $h$ 时权重合法、延迟完全相同，而曲率差为 $5h^2/4+O(h^4)$。第二组 $F_x(t)=\cos(\sqrt x t)$，$x_0=4,x_1=4+4\delta/h^2$，$\delta\le h^2$；由 $|\partial_xF_x(h)|\le h^2/2$，中点数据同时相容，曲率风险至少 $2\delta/h^2$。$\delta>h^2$ 时取 $x_1=8$ 得常数风险。合并 $h^2$ 与 $\delta/h^2$ 的下界即得平方根阶。证毕。

这是单延迟信息模型的下限，不外推到多延迟或额外谱先验。

### 5.5 白化、有限样本和误差传播

设 $C_0\succ0$，相对估计误差为
$$
\|C_0^{-1/2}(\widehat C_0-C_0)C_0^{-1/2}\|\le\rho<1,
\quad\|C_0^{-1/2}(\widehat C_h-C_h)C_0^{-1/2}\|\le\nu.
$$
则存在正交 $U$，使
$$
\|U^T\widehat C_0^{-1/2}\widehat C_h\widehat C_0^{-1/2}U-F(h)\|
\le(\rho+\nu)/(1-\rho).
$$
证明：对 $L=\widehat C_0^{-1/2}C_0^{1/2}$ 作右极分解 $L=UR$，$R=(I+E_0)^{-1/2}$。对齐估计为 $R(F+E_h)R$；用谱界 $\|R\|\le(1-\rho)^{-1/2}$ 展开误差。范数和特征值证书不需要另行恢复 $U$。

$N$ 次独立零均值 Gibbs 配对样本、未中心化协方差估计下，取 $0<\alpha<1$、$\kappa=2\sqrt{r(r+1)/(N\alpha)}<1$。以至少 $1-\alpha$ 的概率可用 $\rho=\nu=\kappa$，从而相关误差预算 $\delta_N=2\kappa/(1-\kappa)$。证明：真白化联合协方差 $\Gamma=\left(\begin{smallmatrix}I&F^T\\F&I\end{smallmatrix}\right)$ 满足 $\|\Gamma\|\le2,\operatorname{tr}\Gamma=2r$，Gaussian 四阶矩给
$$
\mathbb E\|\widehat\Gamma-\Gamma\|_F^2
=((\operatorname{tr}\Gamma)^2+\operatorname{tr}\Gamma^2)/N
\le4r(r+1)/N.
$$
Markov 不等式和块范数得到预算。这是保守充分界；固定 $r,\alpha$ 时组合给 $h\asymp N^{-1/8}$、曲率半径 $O(N^{-1/4})$，不是最优样本复杂度认领。相邻时间样本不自动独立，未知均值、测量噪声和相关采样另定。

令
$$
\widehat D_h=(\widehat F_h-\widehat F_h^T)/(2h),
\quad\gamma=b^3h^2/6+\delta/h,
\quad M_+=\max(0,\lambda_{\max}\widehat W_h+\eta).
$$
中心差分给 $\|\widehat D_h-D\|\le\gamma$，两反对称生成元的 Duhamel 比较给
$$
\|F(t)-e^{t\widehat D_h}\|\le\tfrac12M_+t^2+\gamma t,
$$
$$
\mathbb E\|u_t-e^{t\widehat D_h}u_0\|^2
\le\operatorname{tr}G_t+r(\tfrac12M_+t^2+\gamma t)^2.
$$
若 $\sigma_{\min}(\widehat D_h)>\gamma$，则真实配对非退化；若另知 $M_+<\omega_*^2$，定理 2.5 给更具体的辛余量。有限精度近零值不证明精确闭合。

### 5.6 Kubo 相关与同一矩阵几何

有限正则量子模式、正定 Weyl 二次 $\widehat H=\widehat z^TS\widehat z/2$ 的 Gibbs 态下，定义
$$
C^K_{ij}(t)=\beta^{-1}\int_0^\beta
\operatorname{Tr}[\rho_\beta e^{s\widehat H}\widehat y_i(t)e^{-s\widehat H}\widehat y_j]ds.
$$
则
$$
C^K(t)=\beta^{-1}Oe^{At}S^{-1}O^T.
$$
**证明。** 线性源 $\widehat H_f=\widehat H-f^T\widehat z$ 经 Weyl 位移完成平方，$Z(f)=Z(0)\exp(\beta f^TS^{-1}f/2)$。Duhamel 二阶导数为 $\beta^2C_z^K(0)$，与 Hessian $\beta S^{-1}$ 比较，再用 Heisenberg 线性演化。正定二次热迹与线性源导数有限；可先在共同 Schwartz 域计算再热迹延拓。证毕。[H14]

Kubo 相关与经典 Gibbs 相关同形，但普通单模对称位置方差为 $\hbar\coth(\beta\hbar\omega/2)/(2\omega)$，Kubo 方差为 $1/(\beta\omega^2)$。经典条件概率风险和独立 Gaussian 样本保证不自动成为量子测量结论。

保留两模相关算例：$\Omega=\operatorname{diag}(J_2,2J_2)$、$Q=\left(\begin{smallmatrix}1&0&0&0\\0&3/5&4/5&0\end{smallmatrix}\right)$ 给 $D=3J_2/5,M=\operatorname{diag}(16/25,64/25)$，首轮闭包四维。$t=.1,.25,.5$ 的当前读数最小均方风险分别为 $0.0316905865,0.1881986417,0.6264800864$。$b=2,\delta=.001$ 时，延迟 $.01,.05,.1,.2,.5$ 的证书半径分别为 $20.0110667,.8270667,.3067667,.4766917,2.6746707$；中间延迟能认证方向而两端可能不能。零认证数不表示零真实缺陷。

<a id="sec-thermal"></a>
## 6. 完整观测代数、热恢复与计算复杂度

本章吸收 #8899 第 3–4 节；其辛/Gibbs 分解和全谱 Gaussian 结果已经分别并入第 2、3 节。量子部分现在取有限维子系统 $\mathbb C^d\otimes\mathbb C^e$，$d,e\ge2$，$\hbar=1$，不与正则无限维模式混用。

### 6.1 有限 Weyl 证书与相互作用

对 Hermitian $H$ 定义
$$
h_0=\operatorname{Tr}H/(de),\quad
H_A=e^{-1}\operatorname{Tr}_BH-h_0I_A,\quad H_B=d^{-1}\operatorname{Tr}_AH,
$$
$$
H_0=H_A\otimes I+I\otimes H_B,\quad V=H-H_0,
\quad\mathbb E_A(X)=e^{-1}\operatorname{Tr}_B(X)\otimes I.
$$
因此 $\operatorname{Tr}_AV=\operatorname{Tr}_BV=0$。取 $d$ 维 Weyl 族 $W_{ab}=X^aZ^b$，定义 $R_{ab}=(\operatorname{id}-\mathbb E_A)[H,W_{ab}\otimes I]$，$\delta(H)=\max\|R_{ab}\|$，$\|M\|_{2,n}^2=\operatorname{Tr}M^\dagger M/(de)$。

**定理 6.1。**
$$
R_{ab}=[V,W_{ab}\otimes I],\quad
\|V\|\le\delta(H)\le2\|V\|,
\quad\frac1{2d^2}\sum_{a,b}\|R_{ab}\|_{2,n}^2=\|V\|_{2,n}^2.
$$
完整可见矩阵代数对 $[H,\cdot]$ 闭合，当且仅当 $V=0$，亦当且仅当 $\delta(H)=0$。

**证明。** 条件期望的双模性质与 $\mathbb E_A(V)=0$ 给第一式。对矩阵单位求有限几何和，Weyl twirl 为 $d^{-2}\sum(W\otimes I)V(W^\dagger\otimes I)=d^{-1}I\otimes\operatorname{Tr}_AV=0$。故 $V=d^{-2}\sum R_{ab}(W_{ab}^\dagger\otimes I)$，给左界，交换子范数给右界。展开平方后两个平方项各为 $\|V\|_{2,n}^2$，平均交叉项为零。Weyl 族张成整个可见矩阵代数，得到闭合等价。证毕。

有限证书不自动具有多项式于量子比特数的测量成本。

### 6.2 同一证书的预测、自由能和恢复界

令 $U_t=e^{-itH}$、$f_\beta(H)=-\beta^{-1}\log\operatorname{Tr}e^{-\beta H}$、$\gamma_H=e^{-\beta H}/Z_H$、$G_H(\rho)=\beta^{-1}D(\rho\Vert\gamma_H)$。

**定理 6.2。** 对包括相关初态在内的任意联合态，
$$
\|\operatorname{Tr}_B(U_t\rho U_t^\dagger)-e^{-itH_A}\rho_Ae^{itH_A}\|_1
\le\min(2,2|t|\delta(H)),
$$
$$
|f_\beta(H)-f_\beta(H_0)|\le\delta(H),
\qquad |G_H(\rho)-G_{H_0}(\rho)|\le2\delta(H).
$$
**证明。** Duhamel 给 $\|U_t-U_t^0\|\le|t|\|V\|$，插入中间项给态迹距离至多两倍，偏迹收缩。特征值扰动 $|\lambda_j(H)-\lambda_j(H_0)|\le\|V\|$ 给配分函数比在 $e^{\pm\beta\|V\|}$ 内。最后用 $G_H=\operatorname{Tr}\rho H-\beta^{-1}S(\rho)-f_\beta(H)$。没有假设一般矩阵指数算子单调。证毕。

**定理 6.3。** 记 $\gamma_A,\gamma_B$ 为局部 Gibbs 态，恢复 $\mathcal R\rho_A=\rho_A\otimes\gamma_B$。则
$$
D(\rho\Vert\gamma_A\otimes\gamma_B)-D(\rho_A\Vert\gamma_A)
=I(A:B)_\rho+D(\rho_B\Vert\gamma_B)
=D(\rho\Vert\mathcal R\rho_A).
$$
零缺陷等价于恢复精确，$V=0$ 时缺陷守恒。一般情况下令 $\Delta_H=G_H(\rho)-\beta^{-1}D(\rho_A\Vert\gamma_A)$，则
$$
|\Delta_H-\beta^{-1}D(\rho\Vert\mathcal R\rho_A)|\le2\delta(H),
$$
$$
\|\rho-\mathcal R\rho_A\|_1
\le\min\{2,\sqrt{2\beta(\Delta_H+2\delta(H))}\}.
$$
**证明。** 展开张量对数与熵即得等式。若 $\rho_A$ 奇异，正性保证 $\operatorname{supp}\rho\subseteq\operatorname{supp}\rho_A\otimes\mathcal H_B$：对应核方向的非负对角项总和为零，故该子空间被联合正算子消去。可在支持上合法展开。非负性给恢复刻画；局部酉保持边缘、联合熵与参考，给守恒。用定理 6.2 比较 $G_H$，再用自然对数下量子 Pinsker $\|\rho-\sigma\|_1^2\le2D(\rho\Vert\sigma)$，得两界并保证根号内非负。证毕。[MR17]

$V\ne0$ 时 $\Delta_H$ 本身不被断言为非负数据处理缺陷。

### 6.3 少量读数闭合的反例

$H=Z\otimes Z$ 中 $\operatorname{span}\{I,Z\}\otimes I$ 闭合，但 $V=H,\delta=2$。$|+\rangle\langle+|\otimes|0\rangle\langle0|$ 与隐藏态 $|1\rangle$ 的版本有相同可见初态，之后可见因子分别按 $e^{-itZ}$ 与 $e^{itZ}$ 旋转；$t=\pi/4$ 的 $Y$ 期望相反，$Z$ 读数却始终相同。热态
$$
\gamma_H=\tfrac14(I-\tanh\beta\,Z\otimes Z)
$$
具有混合局部边缘而非乘积联合态。这区分不变线性观测空间与完整子系统代数。

### 6.4 完美预测留下的热风险和精确计数

允许任意有限轮局部于 $A$ 的量子仪器、等待及自适应分支，输出只含可见记录。若 $H=H_A\otimes I_B$、初态 $\rho_A\otimes\sigma_B$，归纳每一轮可见分支概率，全部数据与 $\sigma_B$ 无关。目标
$$
\theta(\sigma_B)=\beta^{-1}(\log e-S(\sigma_B))
$$
的最优最坏期望绝对风险恰为 $\log e/(2\beta)$：纯态与最大混合态给同一数据及目标区间两端，三角不等式给半区间下界，恒输出中点达到。

对 $n$ 变量、$m$ 子句的 3CNF，取违反子句的对角投影 $\Pi_j$，
$$
H_F=(n+1)\sum_j\Pi_j,\quad
H=|1\rangle\langle1|_A\otimes I+I\otimes H_F,
\quad\beta=\log2.
$$
令 $N_k$ 为违反 $k$ 子句的赋值数，则 $Z_F=\sum_kN_k2^{-(n+1)k}$，$0\le Z_F-N_0\le1/2$，可见 $Z_A=3/2$，故
$$
\#\mathrm{SAT}(F)=\left\lfloor\frac23Z_H\right\rfloor.
$$
公共分母和分子的位数为多项式，投影至多三局域且相互对易，系数可用多项式个单位项替代。可见泄漏严格为零，仍携带精确计数困难。恢复公式使用隐藏 Gibbs 态不提供高效制备算法。此归约不承担固定格点、每点总强度或衰减前件，也没有证明固定精度自由能近似同样困难；它不属于正定二次 Gaussian 族 [GL11, ZP25, S25]。

<a id="sec-em"></a>
## 7. 电磁曲率、热响应与磁场设计

### 7.1 最小耦合、Jacobi 与场约束

带符号电荷 $e$、质量 $m>0$，光滑势给作用量
$$
L=m|\dot r|^2/2+eA\cdot\dot r-e\phi-U,
\quad p=m\dot r+eA,
\quad H=|p-eA|^2/(2m)+e\phi+U.
$$
Euler–Lagrange 的矢势偏导差给
$$
m\ddot r=-\nabla U+e(E+\dot r\times B),
\quad E=-\nabla\phi-\partial_tA,\quad B=\nabla\times A.
$$
规范变换使 $L$ 增加全导数 $ed\chi/dt$。磁功率为零，物质能量导数为 $e\dot r\cdot E$。

在静态动力学动量 $\pi=mv$ 中，令 $\mathcal B_{ij}=\varepsilon_{ijk}B_k$，即 $\mathcal Bv=v\times B$，Poisson 矩阵为
$$
J_B=\begin{pmatrix}0&I\\-I&e\mathcal B\end{pmatrix}.
$$
其坐标括号为 $\{r_i,\pi_j\}=\delta_{ij}$、$\{\pi_i,\pi_j\}=e\varepsilon_{ijk}B_k$。三个动量的 Jacobiator 为 $-e\nabla\cdot B$，其余坐标组合为零；一般函数的 Jacobiator 由坐标张量与一阶导数组合，因此 $e\ne0$ 时 Jacobi 当且仅当无散。处处可逆，辛形式
$$
\omega_B=\sum_i dr_i\wedge d\pi_i-\frac e2\sum_{ij}\mathcal B_{ij}dr_i\wedge dr_j
$$
的外微分正是 $-e(\nabla\cdot B)dr_1\wedge dr_2\wedge dr_3$。

时空一形式 $a=A\cdot dr-\phi dt$ 的曲率 $\mathcal F=da$，由 $d^2=0$ 得 $\nabla\cdot B=0$ 和 $\partial_tB+\nabla\times E=0$；逆向势的存在先是局部 Poincaré 引理，全局需拓扑条件。源方程还需要场作用量、度量和电流 [Tong, GEMPIC]。

### 7.2 场能、量子交换子与全局相位

无源真空横向规范、周期或充分衰减边界下，$\Pi=-\epsilon_0E_T$，
$$
H_{\rm EM}=\int(|\Pi|^2/(2\epsilon_0)+|\nabla\times A_T|^2/(2\mu_0))dr
$$
的变分导数给 Maxwell 演化。一般有源有限域能量律为
$$
\frac d{dt}\int_\Omega(\epsilon_0|E|^2/2+|B|^2/(2\mu_0))dr
=-\int_{\partial\Omega}(E\times B)/\mu_0\cdot n\,dS-\int_\Omega j\cdot E\,dr.
$$
它由两条旋度方程点乘并使用散度恒等式得到，边界项不能丢弃。

共同光滑测试域上，$\widehat\pi_i=-i\hbar\partial_i-eA_i$ 满足
$$
[\widehat r_i,\widehat\pi_j]=i\hbar\delta_{ij}I,
\qquad[\widehat\pi_i,\widehat\pi_j]=ie\hbar\varepsilon_{ijk}B_k.
$$
微分交换子消去二阶项即得；规范与 $\psi\mapsto e^{ie\chi/\hbar}\psi$ 相容。半径 $R$ 的通量环，局部 $B=0$ 仍可有 holonomy $e^{ie\Phi/\hbar}$，能谱
$$
E_n=\frac{\hbar^2}{2mR^2}(n-e\Phi/(2\pi\hbar))^2.
$$
对常切向势的 Fourier 模直接求平方即得 [AB59]。局部 Lorentz 场不决定全部全局量子相位。

### 7.3 恒温磁耦合和摩擦的相关分离

假设存在性、光滑性、可积性及分部积分无边界余项。静态 $B$、常数对称 $\Gamma\succeq0$ 下，
$$
dr=\pi\,dt/m,
\quad d\pi=(-\nabla U+e\mathcal B\pi/m-\Gamma\pi/m)dt
+\sqrt{2\beta^{-1}\Gamma}\,dW.
$$
Gibbs 密度 $g_\beta\propto e^{-\beta(|\pi|^2/(2m)+U)}$ 不变，且
$$
\frac d{dt}D(\rho\Vert g_\beta)
=-\beta^{-1}\int\rho\,\nabla_\pi\log(\rho/g_\beta)^T\Gamma
\nabla_\pi\log(\rho/g_\beta)\le0.
$$
证明：Hamilton–Lorentz 漂移无散并与能量梯度正交，摩擦扩散写为 $\beta^{-1}\nabla_\pi\cdot[\Gamma\rho\nabla_\pi\log(\rho/g_\beta)]$；分部积分。固定磁场不自动具有普通详细平衡，物理时间反演也翻转磁场；变温或消惯性另有条件 [Bir17]。

常数磁场、平衡初态下，$K_v(t)=\beta m\mathbb E[v_tv_0^T]$ 满足
$$
K_v'(0+)=(e\mathcal B-\Gamma)/m.
$$
位置速度独立、速度零均值使势力交叉项为零，噪声增量与初态无关，直接用生成元求导得到。因此反对称部分读取磁耦合，对称部分读取摩擦；这一式允许非二次势。

### 7.4 一个可校准的带电振子

固定 $U=m\omega_0^2(x^2+y^2)/2$，$c=eB_0/m$ 为带符号回旋频率，取 $\xi=(\omega_0x,\omega_0y,v_x,v_y)$，则
$$
\dot\xi=\Omega_c\xi,
\quad\Omega_c=\begin{pmatrix}0&0&\omega_0&0\\0&0&0&\omega_0\\-\omega_0&0&0&c\\0&-\omega_0&-c&0\end{pmatrix}.
$$
$\Omega_c$ 反对称，能量 $m|\xi|^2/2$ 守恒，Gibbs 协方差 $(\beta m)^{-1}I$ 与 $c$ 无关。正则 Lebesgue 配分函数 $Z_{\rm cl}=(2\pi)^2/(\beta^2\omega_0^2)$，未除相空间量子归一因子。

特征多项式为 $\lambda^4+(2\omega_0^2+c^2)\lambda^2+\omega_0^4$，正频率
$$
\omega_\pm=\sqrt{\omega_0^2+c^2/4}\pm c/2,
\quad\omega_+\omega_- =\omega_0^2.
$$
对称规范的二次量子 Hamiltonian 是频率 $\sqrt{\omega_0^2+c^2/4}$ 的各向同性振子减 $cL_z/2$。圆偏振算子对角化给 Fock–Darwin 谱 $E_{n_+,n_-}=\hbar\omega_+(n_++1/2)+\hbar\omega_-(n_-+1/2)$，因而
$$
Z_q=[4\sinh(\beta\hbar\omega_+/2)\sinh(\beta\hbar\omega_-/2)]^{-1}.
$$
高温首项与 $Z_{\rm cl}/(2\pi\hbar)^2$ 一致。$c=\omega_0$ 时频率比为 $\varphi,\varphi^{-1}$，这是参数实例，不是普遍黄金常数 [LFO90]。

### 7.5 磁激活、短窗常数和有限最优场

读数 $y=C\xi$、$C=(1,0,0,0)$，参数已知。导数观测矩阵为
$$
\mathcal O=\begin{pmatrix}1&0&0&0\\0&0&\omega_0&0\\-\omega_0^2&0&0&c\omega_0\\0&-c\omega_0^2&-\omega_0(c^2+\omega_0^2)&0\end{pmatrix},
\quad\det\mathcal O=-c^2\omega_0^4.
$$
$c=0$ 时闭包二维，$c\ne0$ 时四维且每个正窗稳定；恢复为
$$
\xi_1=y,\quad\xi_3=y'/\omega_0,\quad
\xi_4=(y''+\omega_0^2y)/(c\omega_0),
\quad\xi_2=-[y'''+(c^2+\omega_0^2)y']/(c\omega_0^2).
$$
矩阵可逆与解析性排除非零不可见初态，有限维紧性给正 Gram 下界。对固定 $c\ne0$，由第 3.3 节 $V^{-1}e_3=(0,-6/(c\omega_0^2),0,0)^T$ 得
$$
a_c(T)\sim\omega_0^4c^2T^7/100800.
$$
它是固定参数短窗极限，不能把 $c\to\infty$ 一并代入。

对每个固定 $T>0$，$a_c(T)$ 连续且
$$
a_0(T)=0,\qquad0\le a_c(T)\le
\frac{\omega_0^2T}{\omega_0^2+c^2/4}.
$$
证明上界时取单位初态 $e_3$，复位置 $X=\xi_1+i\xi_2$ 满足
$$
X(t)=\frac{\omega_0}{i(\omega_++\omega_-)}(e^{i\omega_-t}-e^{-i\omega_+t}).
$$
其模长平方的上界积分即得。两端 $c\to0,\infty$ 都趋零，而非零处为正，因此 $c>0$ 上取得有限非零全局最大值；不主张唯一性。这个设计目标是最弱方向恢复，不等于第 8 节的总互信息。

### 7.6 已知状态模型与未知场参数必须分开

令 $f_c(t)=Ce^{t\Omega_c}C^T$，$R=\operatorname{diag}(1,-1,1,-1)$。由于 $R\Omega_cR=\Omega_{-c}$、$CR=C$、Gibbs 初态在反射下不变，整个单通道被动平衡路径分布在 $c$ 与 $-c$ 下完全相同。等先验符号判别的错误率至少 $1/2$。这是参数不可辨识，不冲突于参数已知时的初态可观测性。

直接计算得到
$$
f_c''(0)=-\omega_0^2,\quad f_c^{(4)}(0)=\omega_0^2(\omega_0^2+c^2).
$$
第一轮缺陷与磁场无关，四阶信息可恢复 $|c|$。两个位置的定向交叉相关满足 $F_{pp,c}^{(3)}(0)=-c\omega_0^2J_2$，两个速度满足 $F_{vv,c}'(0)=cJ_2$，可以区分方向。额外受控初态也能改变观测等价类。

学习势 $A_\theta,\phi_\theta,U_\theta$ 并用旋度和梯度生成场，能在光滑局部图内保持齐次 Maxwell 约束；源、材料、边界和全局 holonomy 仍需另外约束。仓库 `GoldenLorentzUpdate` 的不定二次型命名不承担这里的电磁力证明。

### 7.7 Tesla 与实际能流

tesla 是 $B$ 的 SI 单位，$1\,\mathrm T=1\,\mathrm{Wb/m^2}=1\,\mathrm{N/(A\,m)}$ [NIST]。Tesla 的 US381968A 专利用错相交流产生旋转磁极。理想两相模型 $B(t)=B_0(\cos\nu t\,e_x+\sin\nu t\,e_y)$ 幅值固定而方向旋转；它将相位与旋转结构变成机电耦合。输入电功、场能、机械功和损耗必须平衡 [Tesla1888]。

<a id="sec-unified-results"></a>
## 8. 合编后的新推论：同一耦合的热信息、总信息和磁设计

本章由第 3 节 Gaussian 实验、第 5 节相关缺陷和 #8899 的条件 KL 恢复身份共同推导。固定有限维 $\xi_0\sim N(0,I_n)$、$\dot\xi=\Omega\xi$、$\Omega^T=-\Omega$，$Q\in\mathbb R^{r\times n}$ 满行正交。取 $V$ 使 $\binom QV$ 正交，$u=Q\xi_0,v=V\xi_0$ 独立标准 Gaussian。这里温度已吸收进坐标；物理自由能缺陷需再乘 $\beta^{-1}$。

固定 $T>0$，$\mathcal O_T\xi(t)=Qe^{t\Omega}\xi$。在其有限维轨迹像上取正交积分坐标，用同一 $s>0$ 表示每个积分坐标的噪声方差：
$$
Y=L_T\xi_0+\sqrt s\,\varepsilon,
\quad L_T^TL_T=G_T:=\int_0^Te^{-t\Omega}Q^TQe^{t\Omega}dt.
$$
令 $L_u=L_TQ^T,L_v=L_TV^T$。这个实验可以用有限充分积分坐标表述；比较不同已校准设计时可用它们轨迹像的共同有限维和空间，额外纯噪声坐标不改变信息。

### 8.1 隐藏热恢复缺陷就是条件信息

**定理 8.1。** 令 $\mu_Y$ 为完整后验，$\nu_Y$ 为其当前可见变量 $u$ 的边缘，$\gamma_v=N(0,I_{n-r})$。用恢复 $\mathcal R\nu_Y=\nu_Y\otimes\gamma_v$，则平均热恢复缺陷
$$
\boxed{\Delta_T:=\mathbb E_YD(\mu_Y\Vert\nu_Y\otimes\gamma_v)
=I(v;Y\mid u)
=\tfrac12\log\det(I_{n-r}+L_v^TL_v/s).}
$$
它也等于 $I(\xi_0;Y)-I(u;Y)$。固定 $s$ 时，令 $M$ 为第 5.1 节同一相关曲率，
$$
\boxed{\Delta_T=\frac{T^3}{6s}\operatorname{tr}M+O(T^5).}
$$
对任意 $T>0$，$\Delta_T=0$ 当且仅当当前子空间精确闭合。

**证明。** KL 链式恒等式与 $u,v$ 的先验独立性给
$$
\Delta_T=h(v)-h(v|u,Y)=I(v;Y|u).
$$
条件在 $u$ 上时，数据减去 $L_uu$ 即为 $L_vv+\sqrt s\varepsilon$，Gaussian 熵差给行列式。链式互信息给另一表达。

$L_v^TL_v=\int_0^T V e^{-t\Omega}Q^TQe^{t\Omega}V^Tdt$，其范数为 $O(T^3)$。其迹等于 $\int_0^T\operatorname{tr}(I-F(t)F(t)^T)dt$，第 5.2 节给 $T^3\operatorname{tr}M/3+O(T^5)$。对 logdet 展开，平方余项为 $O(T^6)$，得到公式。零行列式信息等价于 $Qe^{t\Omega}V^T=0$ 在整个窗口成立；其导数使隐藏耦合为零，反向由不变子空间成立。证毕。

这把可观测曲率、隐藏热恢复和历史信息放在同一个实现中。较大的 $\Delta_T$ 表示后验已经包含更多不能仅用当前边缘加平衡隐藏态复原的信息，不能将它误读为算法损失更大或真实耗热更多。非 Gibbs 先验时，第 2.3、6.3 节还有隐藏非平衡与相关性项，不能仅用本式替代。

### 8.2 固定观测预算下的总信息及最优能量风险

设 $\Pi=Q^TQ$。比较基线是同一传感器持续测一个不再旋转的子空间，Gram 为 $T\Pi$，信息与风险为
$$
I_{\rm fixed}=\tfrac r2\log(1+T/s),\quad
R_{\rm fixed}=\tfrac12(n-r+r/(1+T/s)).
$$
**定理 8.2。** 对任意反对称 $\Omega$，
$$
\frac r2\log(1+T/s)\le I_T\le
\frac n2\log(1+rT/(ns)),
$$
$$
\frac{n}{2(1+rT/(ns))}\le R_T\le
\tfrac12(n-r+r/(1+T/s)).
$$
左信息界或右风险界取等，当且仅当 $M=0$。对固定 $s>0$，
$$
\boxed{I_T-I_{\rm fixed}=\frac{T^4}{24s^2}\operatorname{tr}M+O(T^5),}
$$
$$
\boxed{R_{\rm fixed}-R_T=\frac{T^4}{12s^2}\operatorname{tr}M+O(T^5).}
$$

**证明。** $P_t=e^{-t\Omega}\Pi e^{t\Omega}$ 是秩 $r$ 正交投影，故 $0\preceq G_T\preceq TI$、$\operatorname{tr}G_T=rT$。对每个特征值在 $[0,T]$ 使用严格凹函数 $\log(1+x/s)$ 的弦下界，以及严格凸函数 $(1+x/s)^{-1}$ 的弦上界，求和得对应端点界；Jensen 给另一端界。

端点取等要求 $G_T$ 的特征值仅为零或 $T$。由
$$
rT^2-\operatorname{tr}G_T^2
=\tfrac12\int_0^T\int_0^T\|P_t-P_u\|_F^2dtdu
$$
知这当且仅当所有 $P_t$ 相同，即 $[\Omega,\Pi]=0$，等价于 $M=0$。

又
$$
\operatorname{tr}G_T^2=\int_0^T\int_0^T\|F(t-u)\|_F^2dtdu
=rT^2-\tfrac16\operatorname{tr}M\,T^4+O(T^6).
$$
这里 $\int\int(t-u)^2=T^4/6$。对 $k\ge3$，$G_T/T=\Pi+(T/2)[\Pi,\Omega]+O(T^2)$；对迹幂的一阶项为零，因此 $\operatorname{tr}G_T^k=rT^k+O(T^{k+2})$。分别展开 $\tfrac12\operatorname{tr}\log(I+G_T/s)$ 和 $\tfrac12\operatorname{tr}(I+G_T/s)^{-1}$，最早差异来自平方项，得到两个四阶常数。证毕。

与定理 8.1 合并可见：隐藏条件信息以三阶出现，而总信息相对固定子空间的净增益以四阶出现。信息既向隐藏方向重新分配，也影响当前可见边缘的精度；不能把条件信息全部当作净增益。该结论在指定 Gaussian 观测中证明，不从一般 I-MMSE 关系自动移植到任意场或量子测量 [GSV05]。

### 8.3 磁场可观测性与总信息的反向偏好

在第 7.4 节磁振子中，用热归一初态 $N(0,I_4)$、$Q=(1,0,0,0)$ 和相同积分噪声方差 $s$。定义 $I_c(T),R_c(T)$ 为第 3.4 节的信息及全状态能量风险。所有生成元、频率和状态范数均固定，$T\downarrow0$。

**定理 8.3。** 固定 $c\ne0$、$s>0$，
$$
\boxed{I_c(T)-I_0(T)=-\frac{\omega_0^2c^2}{720s^2}T^6+O(T^7),}
$$
$$
\boxed{R_c(T)-R_0(T)=\frac{\omega_0^2c^2}{360s^2}T^6+O(T^7).}
$$
因此充分短的固定噪声窗口中，非零磁场虽然把精确预测闭包从二维提升到四维，却给出较低总信息和较高平均全状态风险。

**证明。** 单通道相关满足
$$
f_c(t)=1-\tfrac12\omega_0^2t^2
+\tfrac1{24}\omega_0^2(\omega_0^2+c^2)t^4+O(t^6).
$$
故 $f_c(t)^2-f_0(t)^2=\omega_0^2c^2t^4/12+O(t^6)$。对两个时间积分，$\int_0^T\int_0^T(t-u)^4dtdu=T^6/15$，于是
$$
\operatorname{tr}G_{c,T}^2-\operatorname{tr}G_{0,T}^2
=\omega_0^2c^2T^6/180+O(T^8).
$$
迹的一次项都精确等于 $T$。因为传感器秩一，$k$ 次迹幂可写成 $k$ 个时间积分中的环乘积 $\prod_j f_c(t_j-t_{j+1})$；单个相关差从四阶出现，故 $k\ge3$ 的差为 $O(T^{k+4})$。logdet 与逆矩阵的级数最早差异来自平方项，其系数分别为 $-1/(4s^2)$ 和 $1/(2s^2)$，得到结论。证毕。

这与定理 8.2 不矛盾：零磁场仍有位置到速度的振动信息传输，已经不是固定子空间基线。比较不同磁场不满足耦合强弱的单调信息定理。

**推论 8.4（改变噪声日程会反转设计偏好）。** 若改取 $s=T^8$，固定 $c\ne0$，则
$$
I_c(T)=8\log(1/T)+O(1),\quad R_c(T)\to0,
$$
$$
I_0(T)=6\log(1/T)+O(1),\quad R_0(T)\to1.
$$
**证明。** 非零磁场的四层指数为 $1,3,5,7$；零磁场只存在 $1,3$ 两个可见层，另两维永远不被观测。把这些指数代入第 3.4 节，得信息系数与标准 Gaussian 先验下的风险极限。证毕。

因此“有没有完整预测状态”“给定噪声下信息有多少”“最弱方向恢复多稳”是不同设计目标。先指定目标和噪声尺度，才能比较传感器或磁场；不能把单个信息指标当作所有目标的排序。

### 8.4 本次可重复检错

本章附属程序以符号矩阵级数核验六阶信息和风险系数，使用 85 位精度 block exponential 计算 Gramian；随机有限例验证投影信息界、风险界及条件 KL/互信息恒等式。它只检验有限实例与代数，不替代一般证明。

在 $\omega_0=c=s=1$、$T=.003$ 时，实际计算
$$
I_1-I_0=-1.0094685016119447432\times10^{-18},
\quad R_1-R_0=2.0159176546122207828\times10^{-18}.
$$
与各自六阶首项的比值为 $0.9970059275$ 与 $0.9955148912$，符号方向均吻合。这个小量使用高精度计算，普通双精度不足以在该时间窗可靠分辨。数值不是硬件实验，未训练或比较神经网络。

<a id="sec-sources"></a>
## 9. 原结果迁移、来源和未完成义务

### 9.1 统一迁移表

| 原正文 | 在本主卷的对应位置 |
|---|---|
| `SYMPLECTIC_PREDICTIVE_COMPLETION.md` v1 §1–3 | §1.1–1.3 |
| 同卷 §4–8、§10–11 | §2.1–2.5 |
| 同卷 §9 | §3.5 |
| `PREDICTIVE_OBSERVABILITY_TIME_WINDOWS.md` §1–8、§10 | §3.1–3.6，相关余量在 §2.4 |
| 同卷 §12–20 | §5.1–5.6 |
| `NORMAL_POWER_FRAME_TIME_INVARIANCE.md` | §4 的完整证明与实例 |
| `ELECTROMAGNETIC_PREDICTIVE_GEOMETRY.md` | §7 |
| #8899 `PREDICTIVE_THERMODYNAMIC_SUFFICIENCY.md` §2 | §2.3 |
| #8899 §3–4 | §6 |
| #8899 §5–6 | §3.3–3.5 |
| 本次共同推导 | §8 |

来源快照：#8891 `8d58dc56d0e6283e725054b5a25c6d5ce8104cc6`，#8899 `e300b5df71f5ce08d857e8f2000a9e495813cdaf`。这次是对尚在 PR 中的正文作合编，不修改已冻结 Lean 或机器账本。旧正文可由 Git 历史恢复；旧文件名只提供主卷跳转，后续数学内容仅在主卷追加。

### 9.2 仓库接口

`FORMAL_DYNAMICAL_INTERFACE_RESIDUALS.md` 给一般目标商和 carry 障碍。

`D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateCanonicalMinimality.lean` 给有限状态的预测等价与唯一商更新；它不直接证明连续空间维数下界。

`D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.lean` 和 `AnalyticFlowGeneration.lean` 给有限矩阵的观测轨道与交换子闭包；正则模式部分另有无限维算子域。

`D5/S3/Weil/ZetaLinear/SchurComplementAssociativity.lean` 给逆算子前件下的消元结合性。`D5/S3/Observer/Hankel/HoKalmanPerturbation.lean` 给观测逆裕量及后验线性求解误差；本卷未把它们冒认为全部新增理论已形式化。

### 9.3 参考文献

[SS16] J. M. Sanz-Serna. *Symplectic Runge–Kutta Schemes for Adjoint Equations, Automatic Differentiation, Optimal Control, and More*. SIAM Review 58(1), 3–33 (2016). DOI: https://doi.org/10.1137/151002769.

[CRBD18] R. T. Q. Chen et al. *Neural Ordinary Differential Equations*. NeurIPS 2018. https://arxiv.org/abs/1806.07366.

[J20] I. Joseph. *Koopman–von Neumann approach to quantum simulation of nonlinear classical dynamics*. Physical Review Research 2, 043102 (2020). https://doi.org/10.1103/PhysRevResearch.2.043102.

[AS97] A. Ashtekar, T. A. Schilling. *Geometrical Formulation of Quantum Mechanics*. https://arxiv.org/abs/gr-qc/9706069.

[McA19] S. McArdle et al. *Variational ansatz-based quantum simulation of imaginary time evolution*. npj Quantum Information 5, 75 (2019). https://doi.org/10.1038/s41534-019-0187-2.

[G97] M. Grmela, H. C. Öttinger. *Dynamics and thermodynamics of complex fluids. I. Development of a general formalism*. Physical Review E 56, 6620 (1997). https://doi.org/10.1103/PhysRevE.56.6620.

[VSM02] A. van der Schaft, B. Maschke. *Hamiltonian formulation of distributed-parameter systems with boundary energy flow*. Journal of Geometry and Physics 42 (2002), 166–194. https://doi.org/10.1016/S0393-0440(01)00083-3.

[L16] H. Lei, N. A. Baker, X. Li. *Data-driven parameterization of the generalized Langevin equation*. https://arxiv.org/abs/1606.02596.

[L76] G. Lindblad. *On the generators of quantum dynamical semigroups*. Communications in Mathematical Physics 48, 119–130 (1976). https://doi.org/10.1007/BF01608499.

[CM17] E. A. Carlen, J. Maas. *Gradient flow and entropy inequalities for quantum Markov semigroups with detailed balance*. https://arxiv.org/abs/1609.01254.

[C10] A. A. Clerk et al. *Introduction to Quantum Noise, Measurement, and Amplification*. https://arxiv.org/abs/0810.4729.

[W12] C. Weedbrook et al. *Gaussian Quantum Information*. Reviews of Modern Physics 84, 621–669 (2012). https://arxiv.org/abs/1110.3234. 使用 Williamson、正则酉及张量热分解。

[ZGPG18] G. Zhang, S. Grivopoulos, I. R. Petersen, J. E. Gough. *The Kalman Decomposition for Linear Quantum Systems*. IEEE TAC 63, 331–346 (2018). https://arxiv.org/abs/1606.05719v4.

[ZLDP23] G. Zhang, J. Li, Z. Dong, I. R. Petersen. *The Quantum Kalman Decomposition: A Gramian Matrix Approach*. https://arxiv.org/abs/2312.16082v1.

[BGH23] P. Buchfink, S. Glas, B. Haasdonk. *Symplectic Model Reduction of Hamiltonian Systems on Nonlinear Manifolds and Approximation with Weakly Symplectic Autoencoder*. https://doi.org/10.1137/21M1466657.

[AHP19] A. Aldroubi, L. X. Huang, A. Petrosyan. *Frames induced by the action of continuous powers of an operator*. JMAA 478(2), 1059–1084 (2019). https://arxiv.org/abs/1801.10103; https://doi.org/10.1016/j.jmaa.2019.05.066. 使用其幂分支及 Conjecture 5.6。

[ACKM26] A. Aldroubi, C. Cabrelli, I. Krishtal, U. Molter. *Dynamical Sampling: A Survey*. https://arxiv.org/abs/2511.10769v3; https://doi.org/10.1007/s44007-026-00215-y. Conjecture 2 为本研究线原问题来源；本文不将合编当作独立确认问题状态。

[DMM21] R. Díaz Martín, I. Medri, U. Molter. *Continuous and discrete dynamical sampling*. https://arxiv.org/abs/2006.08046; https://doi.org/10.1016/j.jmaa.2021.125060. 既有连续/离散关系不认领为新增结果。

[SJP15] E. Schmerling, L. Janson, M. Pavone. *Optimal Sampling-Based Motion Planning under Differential Constraints: the Drift Case with Linear Affine Dynamics*. CDC 2015，2574–2581. https://pmc.ncbi.nlm.nih.gov/articles/PMC4795843/; https://doi.org/10.1109/CDC.2015.7402604. 全谱小时间 Gramian 幂次已有该文的可控对偶结果。

[SD14] Y. Subasi, M. Demirekler. *Quantitative measure of observability for linear stochastic systems*. Automatica 50(6), 1669–1674 (2014). https://doi.org/10.1016/j.automatica.2014.04.008. 互信息可观测性是既有概念。

[GSV05] D. Guo, S. Shamai, S. Verdú. *Mutual Information and Minimum Mean-square Error in Gaussian Channels*. IEEE Transactions on Information Theory 51(4), 1261–1282 (2005). https://arxiv.org/abs/cs/0412108; https://doi.org/10.1109/TIT.2005.844072. 本文第 8 节直接计算指定 Gaussian 实验，未将一般 I-MMSE 换成任意潜变量或量子测量的断言。

[M65] H. Mori. *Transport, Collective Motion, and Brownian Motion*. https://doi.org/10.1143/PTP.33.423.

[M65C] H. Mori. *A Continued-Fraction Representation of the Time-Correlation Functions*. https://doi.org/10.1143/PTP.34.399.

[LL26] Q. Lang, J. Lu. *Learning Memory Kernels in Generalized Langevin Equations*. SIAM Journal on Mathematics of Data Science 8(1), 141–166 (2026). https://doi.org/10.1137/24M1651101.

[LL25] Q. Lang, J. Lu. *Error Analysis of Generalized Langevin Equations with Approximated Memory Kernels*. https://arxiv.org/abs/2512.10256. 其白噪声与衰减假设不自动适用于有限封闭热初态。

[H14] A. Horikoshi. *External Source Method for Kubo-Transformed Quantum Correlation Functions*. https://arxiv.org/abs/1401.0983.

[MR17] A. Müller-Hermes, D. Reeb. *Monotonicity of the Quantum Relative Entropy Under Positive Maps*. https://arxiv.org/abs/1512.06117. 用于测量数据处理和 Pinsker 的既有前置。

[GL11] A. García-Sáez, J. I. Latorre. *An exact tensor network for the 3SAT problem*. https://arxiv.org/abs/1105.3201. 计数背景；本文另外给出固定温度的对角 Hamilton 归约。

[ZP25] H. Zhao, Y. Zhang, J. Preskill. *Learning to erase quantum states: thermodynamic implications of quantum learning theory*. https://arxiv.org/abs/2504.07341. 其密码学前件不被替换成已证的 P/NP 分离。

[S25] S. O. Scalet et al. *Classical Estimation of the Free Energy and Quantum Gibbs Sampling from the Markov Entropy Decomposition*. https://arxiv.org/abs/2504.17405. 有效相互作用衰减、边缘估计和恢复算法的前件不由一个全局二分的零泄漏自动推出。

[PV25] S. Pérez-Vieites et al. *Online Bayesian Experimental Design for Partially Observed Dynamical Systems*. https://arxiv.org/abs/2511.04403. 贝叶斯设计背景，本卷未运行该文算法。

[Tong] D. Tong. Dynamics、Quantum Field Theory 与 General Relativity 原始讲义：https://www.damtp.cam.ac.uk/user/tong/dynamics/dynhtml/S4.html ; https://www.damtp.cam.ac.uk/user/tong/qft/qfthtml/S6.html ; https://www.damtp.cam.ac.uk/user/tong/gr/grhtml/S2.html . 最小耦合、场作用量与曲率是既有物理构件。

[GEMPIC] M. Kraus et al. *GEMPIC: Geometric ElectroMagnetic Particle-In-Cell Methods*. https://arxiv.org/abs/1609.03053.

[AB59] Y. Aharonov, D. Bohm. *Significance of Electromagnetic Potentials in the Quantum Theory*. Physical Review 115, 485 (1959). https://doi.org/10.1103/PhysRev.115.485.

[LFO90] X. L. Li, G. W. Ford, R. F. O'Connell. *Magnetic-field effects on the motion of a charged particle in a harmonic potential*. Physical Review A 42, 4519 (1990). https://doi.org/10.1103/PhysRevA.42.4519.

[Bir17] J. Birrell. *Entropy Anomaly in Langevin-Kramers Dynamics with a Temperature Gradient, Matrix Drag, and Magnetic Field*. https://arxiv.org/abs/1709.06981.

[NIST] NIST Guide to the SI, Chapter 4, derived SI units. https://www.nist.gov/pml/special-publication-811/nist-guide-si-chapter-4-two-classes-si-units-and-si-prefixes.

[Tesla1888] N. Tesla. US381968A, *Electro-magnetic motor*. https://patents.google.com/patent/US381968A/en.

原检索还引用 [GP26] E. A. Gallardo-Gutiérrez, J. R. Partington, https://arxiv.org/abs/2605.29671；[KP26] I. A. Krishtal, G. E. Pfander, https://arxiv.org/abs/2606.20848；[KM26] I. A. Krishtal, B. Miller, https://arxiv.org/abs/2607.18491。相关已发表反例作为外部来源，不计为本研究的额外猜想结算。

### 9.4 证明状态与研究边界

全部新增一般结论是带前件的纸面推导。本次有符号代数和 85 位精度的有限实例检错，没有独立模型或同行审定、Lean kernel 验证、canonical ingest、Scribe 发射或 CI 验证。数值不能证明全称或极限命题。既有文献构件与 repo-derived 组合均不自动确立全球首创。

仍独立的义务包括：非线性预测商的全局存在和非退化性；相关轨迹而非独立制备的有限样本预算；未知生成元与传感器联合辨识；实际量子测量的反作用、噪声及可取得性；无限场论的边界和无界生成元条件；正定二次模型外的热恢复与有效复杂度。每个义务继续追加在本主卷，不另开同一研究线的重复伴卷。

## 追加锚（后续内容在本行以下使用新编号）

<a id="sec-nonlinear-closure"></a>
## 10. 非线性预测闭包：表达误差、隐藏涨落与热条件恢复

**增订范围（2026-09-20）。** 本章将第 5 节的相关曲率和第 8 节的热条件信息推进到非线性、非 Gaussian 的确定性平稳演化。旧章正定二次/Gaussian 结论保持原前件；本章分别声明生成元域、光滑性、条件密度及有界性。条件期望投影、力匹配分解和平均力势是既有构件 [KHKP15, LTPL23, ASDN22, GS21, PCR26]。新增的是在同一观察下连接相关缺陷、真正的预测下限、二阶条件响应和热恢复系数的证明链与显式非线性磁模型。这里不认领新的外部具名猜想解答或全局优先权。

### 10.1 两种投影下的相关缺陷

设完整流 $\Phi_t$ 保持概率 $\mu$，在实 $L^2(\mu)$ 上诱导强连续酉群 $\mathsf U_t f=f\circ\Phi_t$，生成元记 $\mathscr L$。向量观测 $u$ 的各分量属于 $\operatorname{Dom}\mathscr L^2$，并且 $\mathbb E u=0$、$\mathbb E uu^T=I_r$。所有范数和期望均使用这个固定参考；一般非退化协方差可以先作固定白化。定义
\[
F(t)=\mathbb E[(\mathsf U_tu)u^T],\quad D=F'(0),\quad v=\mathscr Lu,
\quad b(u)=\mathbb E[v\mid u],\quad r_u=v-b(u),
\]
\[
N=\mathbb E[r_ur_u^T],\qquad
E_{\rm expr}=\mathbb E[(b(u)-Du)(b(u)-Du)^T].
\]
$\mathsf P f=\mathbb E[f\mid u]$ 是到全部当前观测可测函数的正交投影。到 $u$ 各分量线性跨度的投影通常更小。

**定理 10.1（相关曲率的非线性分解）。**
\[
D^T=-D,\quad F''(0)=-\mathbb E[vv^T],\qquad
\boxed{M:=D^2-F''(0)=N+E_{\rm expr}\succeq0.}
\]
对任意平方可积当前漂移拟合器 $g(u)$，
\[
\mathbb E\|v-g(u)\|^2=\operatorname{tr}N+\mathbb E\|b(u)-g(u)\|^2.
\]
固定 $t$，最佳线性预测为 $F(t)u$，最佳任意可测预测为 $\mathsf P\mathsf U_tu$，两者的风险差恰为 $\|\mathsf P\mathsf U_tu-F(t)u\|_{L^2}^2$。

**证明。** 生成元的反对称性给 $D_{ij}=-D_{ji}$ 及 $\langle\mathscr L^2u_i,u_j\rangle=-\langle\mathscr Lu_i,\mathscr Lu_j\rangle$。展开 $\mathbb E[(v-Du)(v-Du)^T]$ 得 $\mathbb E[vv^T]+D^2$。再写 $v-Du=r_u+(b(u)-Du)$，由 $\mathbb E[r_u\mid u]=0$ 使交叉矩阵为零。其余风险等式都是同一正交分解。证毕。

$E_{\rm expr}$ 衡量当前变量已足够表达、但线性函数没有利用的非线性部分；$N$ 衡量给定当前变量后仍存在的速度不确定性。第 5 节的线性 Gaussian 情况有 $b(u)=Du$，故 $E_{\rm expr}=0$、$M=N$。一般非线性系统不能直接把 $M$ 全部当作信息缺失。回归误差只给 $\operatorname{tr}N$ 的上界，除非额外控制了回归近似误差。

### 10.2 真正的短时间 Bayes 下限和精确闭合

令 $n_u=\operatorname{tr}N$、$c_2=\|\mathscr L^2u\|_{L^2}$。风险使用平方欧氏误差，不含二分之一。

**定理 10.2（条件隐藏方差的有限时间保证）。** 设
\[
\mathcal R_*(t)=\inf_f\mathbb E\|\mathsf U_tu-f(u)\|^2.
\]
则对 $t\ge0$，
\[
\boxed{\left|\sqrt{\mathcal R_*(t)}-t\sqrt{n_u}\right|\le\tfrac12t^2c_2,}
\quad
\mathcal R_*(t)=t^2n_u+O(t^3).
\]
最佳线性风险的首项为 $t^2\operatorname{tr}M$，线性与非线性最佳风险之差为 $t^2\operatorname{tr}E_{\rm expr}+O(t^3)$。

**证明。** 酉群的两次积分 Taylor 公式在 $L^2$ 中给
\[
\mathsf U_tu=u+tv+R_t,\qquad\|R_t\|_{L^2}\le t^2c_2/2.
\]
对两边作用 $I-\mathsf P$，得到最优残差 $tr_u+(I-\mathsf P)R_t$；投影收缩和范数反三角不等式给有限时间界。换成线性投影得对应线性风险；或者对两个最优预测之差作同一 Taylor 展开。证毕。

若再假设状态空间为光滑流形、$\mu$ 对每个非空开集赋正质量、$u$ 为光滑观察映射，且 $b$ 存在局部 Lipschitz 版本、$\mathscr Lu-b(u)$ 连续，则 $N=0$ 当且仅当观察沿整个流按 $\dot u=b(u)$ 精确自治（限制在相应解存在区间）。证明：$N=0$ 先给几乎处处零残差，连续性和满支撑将其升级为处处；链式法则及 ODE 唯一性给全部未来。反向由自治方程求零时导数。不满足这些正则性时，仅将 $N=0$ 报作参考概率下的瞬时闭合。

### 10.3 热分布与隐藏方差共同确定二阶记忆响应

本节不要求观测白化。设观测的边缘具有正 $C^1$ 密度 $\rho(u)$，$b$ 为 $C^1$，并有足够可积性使下列弱分部积分成立。令
\[
\mathcal C(u)=\mathbb E[r_ur_u^T\mid u],\qquad
k_i(u)=\rho(u)^{-1}\sum_j\partial_{u_j}[\rho(u)\mathcal C_{ij}(u)].
\]
假定 $r_u\in\operatorname{Dom}\mathscr L$，相关条件期望与 $k$ 属于 $L^2$。

**定理 10.3（条件涨落的局部响应恒等式）。**
\[
\boxed{\mathbb E[\mathscr Lr_u\mid u]=k(u),\qquad
\mathbb E[\mathscr L^2u\mid u]=Db(u)b(u)+k(u).}
\]
同时 $\nabla_u\cdot(\rho b)=0$。当 $\rho\propto e^{-\beta\mathcal A(u)}$ 时，
\[
k_i=\sum_j\partial_{u_j}\mathcal C_{ij}
-\beta\sum_j\mathcal C_{ij}\partial_{u_j}\mathcal A.
\]

**证明。** 对紧支光滑标量 $\psi(u)$，生成元反对称性给
\[
\mathbb E[\psi\mathscr Lr_i]
=-\mathbb E[(\mathscr L\psi)r_i]
=-\mathbb E\sum_j(\partial_j\psi)v_jr_i
=-\int\rho\sum_j(\partial_j\psi)\mathcal C_{ij}\,du.
\]
最后一步用条件零均值消掉 $b_jr_i$，分部积分得到 $k_i$。再对 $\mathscr Lu=b(u)+r_u$ 求生成元，条件平均给 $Db\,b+k$。对任意 $\psi$，平稳性给 $\mathbb E\mathscr L\psi=\int\rho b\cdot\nabla\psi=0$，即边缘连续方程。证毕。

因此只演化平均漂移 $b$ 可以保持正确的静态边缘，同时漏掉条件均值的二阶项。令 $u\in\operatorname{Dom}\mathscr L^3$、$c_3=\|\mathscr L^3u\|_{L^2}$，定义
\[
g_{2,t}(u)=u+tb(u)+\tfrac12t^2[Db(u)b(u)+k(u)].
\]
三次积分 Taylor 公式和条件期望收缩给
\[
\boxed{\|\mathbb E[u_t\mid u]-g_{2,t}(u)\|_{L^2}\le t^3c_3/6,}
\]
\[
\mathbb E\|u_t-g_{2,t}(u)\|^2-\mathcal R_*(t)\le t^6c_3^2/36.
\]
这是局部条件均值预测器的保证；不宣称截断更新是辛积分器，也不把它迭代为已经证明长期稳定的 Markov 动力学。$k$ 是二阶投影响应，不能单凭它恢复全部非线性记忆核。

### 10.4 非线性平均力势、磁耦合与精确闭合的条件

取单位质量、Cartesian 分块位置 $q=(x,y)$ 和机械动量 $p=(p_x,p_y)$，光滑势 $U(x,y)$。常数带电磁耦合矩阵 $\mathcal B$ 反对称，电荷已吸收入系数；其分块记为 $\mathcal B_{xx},\mathcal B_{xy}$。Hamilton–Lorentz 方程为
\[
\dot q=p,\qquad\dot p=-\nabla U(q)+\mathcal Bp.
\]
假定完整 Gibbs 分布可归一、满支撑，势与其相关导数允许积分下微分。观察 $u=(x,p_x)$，定义平均力势
\[
A_\beta(x)=-\beta^{-1}\log\int e^{-\beta U(x,y)}dy.
\]

**定理 10.4（同一观测的平均力与隐藏协方差）。**
\[
b(x,p_x)=(p_x,-\nabla A_\beta(x)+\mathcal B_{xx}p_x),
\]
\[
\boxed{\mathcal C_{p_xp_x}(x,p_x)
=\operatorname{Cov}(\nabla_xU\mid x)
+\beta^{-1}\mathcal B_{xy}\mathcal B_{xy}^T,}
\]
其余位置及交叉块为零。并有
\[
\boxed{\nabla^2A_\beta(x)
=\mathbb E[\nabla_x^2U\mid x]
-\beta\operatorname{Cov}(\nabla_xU\mid x).}
\]
在连通乘积位置域与以上光滑满支撑条件下，$N=0$ 当且仅当 $\mathcal B_{xy}=0$ 且 $U(x,y)=U_1(x)+U_2(y)$。此时当前观察精确自治。

**证明。** Gibbs 机械动量是独立于位置的 $N(0,\beta^{-1}I)$，条件均值直接给 $b$。未知势力的中心化残差与 $\mathcal B_{xy}p_y$ 独立，条件协方差相加得到第二式。对配分积分先求一次导数给平均力，再求一次给 Hessian–协方差身份。

若平均协方差迹为零，两项正半定矩阵均为零，先有 $\mathcal B_{xy}=0$。条件势力方差为零、条件满支撑和连续性说明 $\nabla_xU$ 与 $y$ 无关；在连通 $x$ 域沿路径积分，得到势的加性分离。反向直接代回方程。证毕。

产品 Gibbs 分布本身不排除跨子系统磁耦合。势能耦合与 Poisson 配对耦合在这个条件中分别出现。一般非线性反应坐标有额外 Jacobian 与几何项，不能把 Cartesian 公式原样套用；一般量子条件期望也不自动具有这里的经典协方差解释。

### 10.5 静态热分布完全相同的一族非线性反例

取平面磁系统
\[
H=\tfrac12(p_x^2+p_y^2)+\tfrac14x^4+\tfrac\kappa2(y-a x^2)^2,
\quad\kappa>0,\quad c\in\mathbb R,
\]
\[
\dot x=p_x,\quad\dot y=p_y,\quad
\dot p_x=-x^3+2\kappa ax(y-a x^2)+cp_y,
\quad\dot p_y=-\kappa(y-a x^2)-cp_x.
\]
势能子水平集紧，能量守恒给完整光滑流；Gibbs 分布有全部所需多项式矩。记 $z=y-a x^2$，则 $x,p_x,z,p_y$ 在 Gibbs 参考下相互独立，$z\sim N(0,(\beta\kappa)^{-1})$。

**命题 10.5（相同平均力、不同预测下限）。** 所有 $a,c$ 的可见 Gibbs 密度均为
\[
\rho(x,p_x)\propto\exp[-\beta(x^4/4+p_x^2/2)],
\quad A_\beta(x)=x^4/4+\text{常数},
\quad b=(p_x,-x^3).
\]
但
\[
\mathcal C_{p_xp_x}=4\kappa a^2x^2/\beta+c^2/\beta,
\quad k=(0,-(4\kappa a^2x^2+c^2)p_x).
\]
令 $v_\beta=\mathbb E x^2=2\beta^{-1/2}\Gamma(3/4)/\Gamma(1/4)$，用白化观察 $u=(x/\sqrt{v_\beta},\sqrt\beta p_x)$，则
\[
\boxed{N=\operatorname{diag}(0,4\kappa a^2v_\beta+c^2),}
\qquad
\boxed{E_{\rm expr}=\operatorname{diag}(0,3v_\beta-1/(\beta v_\beta)).}
\]
因此当前状态的真正短时风险系数随 $a,c$ 改变，而所有静态可见热统计与平均力相同。

**证明。** 坐标变换 $y=z+a x^2$ 的 Jacobian 为一；积分掉 Gaussian $z,p_y$ 给边缘。残差为 $2\kappa axz+cp_y$，用条件 Gaussian 二阶矩得到协方差，代入定理 10.3 得 $k$。Gibbs 分部积分给 $\mathbb E x^4=1/\beta$、$\mathbb E x^6=3v_\beta/\beta$。因此白化线性投影的频率为 $1/\sqrt{\beta v_\beta}$，其表达残差平方均值为 $\beta\mathbb E x^6-1/(\beta v_\beta)$；与隐藏项分别组成上述两块。证毕。

特别地，$a=c=0$ 时当前两个变量已经完全自治，所有未来可精确预测，然而 $M=E_{\rm expr}\ne0$。$\beta=1$ 时非零值约为 $0.5485971606075344$。它是非线性漂移的线性拟合误差，不是遗漏状态证据。这个反例阻止把第 5 节的 Gaussian 特例无条件外推。

此外，非线性情形的 $\operatorname{rank}N$ 仅计量独立的残差函数方向，不能直接当作隐藏坐标数。一个隐藏标量 $w$ 的两个函数 $(w,w^2-\mathbb Ew^2)$ 就可以具有秩二协方差；这里不继承线性 Gramian 的状态维数下界。

### 10.6 条件配对实验和有限延迟认证

给定同一 $u$，独立抽取完整初态 $Z,Z'$ 的条件参考分布，并分别演化。定义 $d_h(Z)=[u(\Phi_h Z)-u(Z)]/h$，$N_h=\mathbb E\operatorname{Cov}(d_h\mid u)$。

**定理 10.6（不依赖回归器的配对证书）。**
\[
N=\tfrac12\mathbb E[(v(Z)-v(Z'))(v(Z)-v(Z'))^T],
\]
\[
N_h=\frac1{2h^2}\mathbb E[(u(\Phi_hZ)-u(\Phi_hZ'))(u(\Phi_hZ)-u(\Phi_hZ'))^T],
\]
\[
\left|\sqrt{\operatorname{tr}N_h}-\sqrt{n_u}\right|\le hc_2/2,
\quad\|N_h-N\|\le h\sqrt{n_u}c_2+h^2c_2^2/4.
\]

**证明。** 条件独立且同条件均值的两个随机向量，其差的条件外积期望是协方差两倍。对有限差分使用定理 10.2 的 Taylor 余项后再作条件中心化，$L^2$ 差至多 $hc_2/2$；范数反三角不等式和外积差的 Cauchy–Schwarz 给两条误差界。证毕。

若另有 $\|\mathscr Lu\|_\infty\le K_1$、$\|\mathscr L^2u\|_\infty\le K_2$，取 $m$ 组彼此独立的上述配对，样本平方差的一半除以 $h^2$ 的平均记为 $\widehat n_h$。每项在 $[0,2K_1^2]$；Hoeffding 给至少 $1-\alpha$ 的概率下
\[
|\widehat n_h-n_u|\le hK_1K_2+h^2K_2^2/4
+K_1^2\sqrt{2\log(2/\alpha)/m}.
\]
这是一种指定的条件重复制备或条件微观采样实验。普通相邻轨迹点不会自动满足同一当前读数及条件独立性。导数无界的第 10.5 节 Gibbs 例可以用 $L^2$ 偏差界，却不能直接使用这里的有界 Hoeffding 预算；传感器噪声也须另计。

### 10.7 非 Gaussian 热恢复的三阶信息系数

本节使用同一不变参考 $\mu$ 的正则条件分布 $\mu(dZ\mid u)$，不要求可见和隐藏先验独立。假设观测的一、二阶生成元导数分别本质有界于 $K_1,K_2$，并保留 $L^2$ 前件。取独立 $\varepsilon\sim N(0,I_r)$、固定噪声方差 $s>0$，使用一个单位 $L^2(0,T)$ 范数的时间权重：
\[
Y_T=S_T(Z)+\sqrt s\,\varepsilon,\qquad
S_T(Z)=\frac{\sqrt3}{T^{3/2}}\int_0^T t\,u(\Phi_t Z)dt.
\]
该实验仅有 $r$ 个积分读数。令完整后验为 $\mu_{Y_T}$、当前观察的后验边缘为 $\nu_{Y_T}$，恢复时沿当前纤维使用原条件热参考：$\mathcal R\nu=\nu(du)\mu(dZ\mid u)$。

**定理 10.7（条件热恢复的非线性延拓）。**
\[
\Delta_T:=\mathbb E D(\mu_{Y_T}\Vert\mathcal R\nu_{Y_T})
=I(Z;Y_T\mid u),
\qquad
\boxed{\Delta_T=\frac{T^3}{6s}n_u+O(T^4).}
\]
一个显式余项为
\[
\left|\Delta_T-\frac{T^3}{6s}n_u\right|
\le\frac{T^4\sqrt{n_u}K_2}{8s}
+\frac{3T^5K_2^2}{128s}
+\frac{8K_1^4T^6}{9s^2}
 \exp\!\left(\frac{4K_1^2T^3}{3s}\right).
\]

**证明。** 对先验和后验作条件密度比分解，得到平均条件 KL 等于条件互信息；这不使用乘积先验。积分 Taylor 给
\[
S_T=\tfrac{\sqrt3}2T^{1/2}u+\tfrac1{\sqrt3}T^{3/2}v+R_T^S,
\quad\|R_T^S\|_{L^2}\le\tfrac{\sqrt3}8T^{5/2}K_2.
\]
条件中心化后 $X_T=S_T-\mathbb E[S_T\mid u]$ 满足
\[
\left|\mathbb E\|X_T\|^2-\tfrac13T^3n_u\right|
\le\tfrac14T^4\sqrt{n_u}K_2+\tfrac3{64}T^5K_2^2.
\]
同时逐点速度界给 $\|X_T\|\le 2K_1T^{3/2}/\sqrt3$。

以给定 $u$ 的均值加噪声 Gaussian 为比较参考，KL 链式恒等式给
\[
I(Z;Y_T\mid u)
=\frac{\mathbb E\|X_T\|^2}{2s}
-\mathbb E_uD(P_{X_T+\sqrt s\varepsilon\mid u}\Vert N(0,sI)).
\]
对条件独立复制 $X_T'$，Gaussian 似然比积分给
\[
\chi^2(P_{X_T+\sqrt s\varepsilon\mid u}\Vert N(0,sI))
=\mathbb E[e^{X_T\cdot X_T'/s}\mid u]-1.
\]
条件中心化令线性项为零。若 $a_T=4K_1^2T^3/(3s)$，则剩余至多 $a_T^2e^{a_T}/2$，因为 $|X_T\cdot X_T'/s|\le a_T$；再用 $D\le\log(1+\chi^2)\le\chi^2$。与方差余项合并即得结论。证毕。

因此第 8 节的 Gaussian 三阶热信息系数在这里由真正条件隐藏方差 $N$ 接管，表达误差 $E_{\rm expr}$ 不进入该首项。物理自由能尺度仍需乘 $\beta^{-1}$；这是条件概率恢复量，没有指定真实测量与擦除的耗热协议。第 10.5 节的无界多项式例不直接满足本定理的有界余项前件，不能仅因存在全部矩就自动使用该显式常数。

### 10.8 本次算例、算法接口和边界

第 10.5 节取 $\beta=\kappa=1,a=0.5,c=0.7$，精确 Gibbs 矩给
\[
\operatorname{tr}N=1.1659782400672847,\quad
\operatorname{tr}E_{\rm expr}=0.5485971606075344,\quad
\operatorname{tr}M=1.7145754006748191.
\]
使用可见位置的 60 点积分、其余变量的 Gaussian 10 点乘积积分，条件均值在每个固定可见初态上对隐藏变量积分；轨迹以向量化 RK4 演化，并作步长减半核对。所得风险如下，未将求积当作一般证明。

| 时间 | 任意当前状态预测器的 Bayes 风险估计 | 风险除以时间平方 | 一阶条件 Taylor 的超额风险 | 二阶条件 Taylor 的超额风险 |
|---:|---:|---:|---:|---:|
| 0.01 | 0.0001165806795134 | 1.1658067951 | 5.4719164e-8 | 8.0631174e-12 |
| 0.02 | 0.0004661171019559 | 1.1652927549 | 8.7523442e-7 | 5.1587306e-10 |
| 0.04 | 0.0018611856074090 | 1.1632410046 | 1.3986353e-5 | 3.2973320e-8 |

二阶预测器只缩小超出 Bayes 下限的部分，不消除当前观测留下的风险。它需要学习或估计 $b(u)$、条件协方差 $\mathcal C(u)$ 和边缘 score $\nabla\log\rho(u)$，再按定理 10.3 构造二阶项；所有估计误差仍需另行传播。单独拟合更大的 $b_\theta$ 不提供条件隐藏信息，单独增加记忆结构也不证明长时可恢复。

本次脚本实际通过 55 项符号、矩积分和有限轨迹检查，涵盖能量与参考分布、相关缺陷分解、平均力 Hessian、条件响应、配对协方差以及局部风险界。另以一个有界的平稳相位/双速度模型，70 位精度核验定理 10.7 的非 Gaussian 信息首项和 Gaussian 混合的 chi-square 界；该检错模型使用指定不变概率，并非平滑满支撑 Gibbs 密度，不能承担第 10.4 节的势分离结论。没有独立同行或异模型审定、Lean kernel、Scribe、canonical ingest、CI、硬件实验或神经网络 benchmark。

### 10.9 本章来源和归属

[KHKP15] E. Kalligiannaki, V. Harmandaris, M. A. Katsoulakis, P. Plechac. *The geometry of generalized force matching in coarse-graining and related information metrics*. arXiv:1504.02152. 条件期望投影、力匹配与热力学积分的既有基础；本章 Cartesian 平均力导数直接从条件配分积分推导。

[LTPL23] Y. T. Lin, Y. Tian, D. Perez, D. Livescu. *Regression-Based Projection for Learning Mori–Zwanzig Operators*. SIAM Journal on Applied Dynamical Systems (2023), DOI 10.1137/22M1506146; arXiv:2205.05135. 线性和非线性回归投影连接 Mori 与 Zwanzig 的已有方法。本章不将投影选择或误差正交分解本身认领为新算法。

[ASDN22] C. Ayaz, L. Scalfi, B. A. Dalton, R. R. Netz. *Generalized Langevin equation with a nonlinear potential of mean force and nonlinear memory friction from a hybrid projection scheme*. Physical Review E 105, 054138 (2022), DOI 10.1103/PhysRevE.105.054138. 平均力势与非线性记忆的已有组合。

[GS21] F. Glatzel, T. Schilling. *The Interplay between Memory and Potentials of Mean Force: A Discussion on the Structure of Equations of Motion for Coarse Grained Observables*. Europhysics Letters 136, 36001 (2021); arXiv:2107.01111. 其对非线性平均力、简单记忆和涨落耗散组合的限制，是本章只给局部条件响应而不擅自闭合全时记忆的文献边界。

[PCR26] A. Park, S. Chennakesavalu, G. M. Rotskoff. *Scaling transferable coarse-graining with mean force matching*. Journal of Chemical Physics 164, 244117 (2026), DOI 10.1063/5.0329526; arXiv:2602.14531. 使用其条件均值力与瞬时投影力噪声的区分，不据其非线性坐标形式推导本章结果，也不将该文实验性能认领为本项目读数。

本章补齐第 9.4 节中“非线性观察下哪些误差真正来自隐藏状态”的一部分义务。全局最小非线性预测状态的构造、有限历史所需长度、实际 noisy sensor 的联合置信保证，以及量子非对易条件恢复的对应仍需分别证明。

<a id="sec-memory-consistency"></a>
## 11. 历史闭合与多步相容性：残差相关、有限记忆和辛记忆坐标

**范围与来源。** 本章继续同一观察下的非线性预测问题。第 10 节将当前变量的表达误差与真实条件隐藏方差分开；本章研究后者如何阻碍单步模型的多步复用，以及历史怎样补回这种信息。条件期望投影与记忆来自 [CHK02, LTPL23]；残差协方差检验采用 [SP20] 的既有统计结构；延迟可辨识与稳定性的区别与 [YR11, EYWR18] 对照。下列带常数的组合、指定磁模型的可逆记忆图及反例均按正文推导，不认领这些基础理论的首创或新的具名开放问题解决。

### 11.1 条件预测算子的组合缺陷与过去、未来的残差相关

沿用第 10 节保持概率的完整流。令 $\mathcal H=L^2(\mu)$，$\mathsf U_t$ 为 Koopman 酉群，生成元为 $\mathscr L$；$\mathsf P f=\mathbb E[f\mid u]$、$\mathsf Q=I-\mathsf P$。这里 $\mathsf Q$ 是函数空间投影，不是第 5 节的观测矩阵。将当前可见函数空间 $\mathcal H_u=\operatorname{Ran}\mathsf P$ 与其在完整空间中的提升等同，定义
\[
 \mathsf T_t=\mathsf P\mathsf U_t\mathsf P\big|_{\mathcal H_u}.
\]
每个 $\mathsf T_t$ 单独保持正性、常数和可见参考概率，并是 $L^2$ 压缩算子。一般不满足时间齐次 Markov 半群的组合律。

**定理 11.1（有限延迟的精确组合身份）。** 对任意实 $t,s$，
\[
 \mathsf T_{t+s}-\mathsf T_t\mathsf T_s
 =\mathsf P\mathsf U_t\mathsf Q\mathsf U_s\mathsf P.
\]
取实 $f=\varphi(u)\in\operatorname{Dom}\mathscr L^2$，令
\[
 r_f=\mathsf Q\mathscr Lf,\quad n_f=\|r_f\|_2^2,
 \quad c_f=\|\mathscr L^2f\|_2,
 \quad d_f(h)=\langle f,(\mathsf T_{2h}-\mathsf T_h^2)f\rangle.
\]
则
\[
 \boxed{d_f(h)=\mathbb E\operatorname{Cov}
       (\varphi(u_{-h}),\varphi(u_h)\mid u_0),}
\]
\[
 \boxed{|d_f(h)+h^2n_f|
       \le h^3\sqrt{n_f}\,c_f+h^4c_f^2/4,\qquad h\ge0.}
\]
另外有精确正算子身份
\[
 I-\mathsf T_{-h}\mathsf T_h
 =(\mathsf Q\mathsf U_h\mathsf P)^*
   (\mathsf Q\mathsf U_h\mathsf P)\succeq0.
\]

**证明。** 在 $\mathsf U_t\mathsf U_s$ 中插入 $I=\mathsf P+\mathsf Q$ 得第一式。由酉性，
\[
 d_f(h)=\langle\mathsf Q\mathsf U_{-h}f,
                    \mathsf Q\mathsf U_h f\rangle.
\]
两项正是过去、未来读数相对当前观察的条件中心化残差，给出协方差身份。积分 Taylor 公式给
\[
 \mathsf Q\mathsf U_{\pm h}f=\pm h r_f+e_\pm,
 \quad\|e_\pm\|_2\le h^2c_f/2.
\]
展开内积并应用 Cauchy–Schwarz 得余项。最后在
$\mathsf P\mathsf U_{-h}\mathsf U_h\mathsf P=I_{\mathcal H_u}$
中插入两投影即得正算子身份。证毕。

若 $\varphi$ 光滑且满足所需域条件，第 10 节的条件协方差给
\[
 n_f=\int \nabla\varphi(u)^T\mathcal C(u)\nabla\varphi(u)\rho(u)\,du.
\]
因此不同观测函数的双线性短时组合缺陷是
$-\int\nabla\psi^T\mathcal C\nabla\varphi\,\rho$。在第 10.3 节的分部积分条件下，其弱算子为
\[
 \mathcal D_{\mathcal C}\varphi
 =\rho^{-1}\nabla\cdot(\rho\mathcal C\nabla\varphi),
 \qquad \langle\varphi,\mathcal D_{\mathcal C}\varphi\rangle_\rho=-n_f.
\]
这同时连接热条件响应和非 Markov 组合缺陷。上述展开是固定测试函数上的强/弱陈述，不是无界生成元的统一算子范数 Taylor 展开。

### 11.2 一个时间齐次模型无法同时消掉两个延迟的误差

**推论 11.2（两延迟的相容性下界）。** 令 $\mathsf S_t$ 为 $\mathcal H_u$ 上任意压缩半群，记
$e_j=\|\mathsf T_{jh}-\mathsf S_{jh}\|_{\mathrm{op}}$，$j=1,2$。对非零 $f$ 有
\[
 \boxed{\max(e_1,e_2)\ge
 \frac{[h^2n_f-h^3\sqrt{n_f}c_f-h^4c_f^2/4]_+}
 {3\|f\|_2^2}.}
\]
尤其 $n_f>0$ 时，精确的当前状态转移族不能是时间齐次 Markov 半群。

**证明。** 用 $\mathsf S_{2h}=\mathsf S_h^2$、两族范数至多一，得到
\[
 \|\mathsf T_{2h}-\mathsf T_h^2\|
 \le e_2+2e_1\le3\max(e_1,e_2).
\]
用测试函数的二次型下界及定理 11.1 即得。证毕。

这里比较的是同一状态、同一参考下的转移算子，覆盖保持该参考的时间齐次 Markov 模型。它没有否定带附加记忆状态、显式时间/年龄变量、变时间尺度极限的模型，也没有把任意非线性条件均值函数的复合直接等同于转移核的复合。

**例 11.3（精确单步，错误的细步长极限）。** 标准 Gaussian 初态的谐振子满足 $q_t=\cos t\,q_0+\sin t\,p_0$。精确一步条件核是
\[
 q_{k+1}=\cos h\,q_k+\sin h\,\eta_k,
 \quad \eta_k\ \text{独立标准 Gaussian}.
\]
重复这个核相当于每步重新按条件热参考抽取隐藏动量；其均值因子是 $(\cos h)^n$，条件方差是 $1-(\cos h)^{2n}$。固定 $t=nh$、令 $n\to\infty$ 时，二者趋于 $1,0$。真实因子却是 $\cos t,\sin^2t$。两种实验都保持静态 Gaussian 边缘，但连续保留同一隐藏状态与每步重置隐藏状态不是同一实验。更小数值步长不会修复被重复重置的记忆。

对光滑确定性微观模型，可见条件增量协方差以 $t^2\mathcal C$ 起始。具有固定非零扩散张量的 Itô 模型则以 $t\,a(u)$ 起始；二者不能在这个短时尺度直接等同。扩散近似可以在另行证明的时间尺度分离极限或较粗时间分辨率成立。

### 11.3 独立检验数据上的残差相关证书

令 $g_\pm(u)=\mathbb E[\varphi(u_{\pm h})\mid u_0=u]$，以独立训练数据得到固定函数 $\widehat g_\pm$，满足可核验或另行假设的 $L^2$ 预算
$\|\widehat g_\pm-g_\pm\|_2\le\varepsilon_\pm$。

**命题 11.4（回归误差以乘积进入记忆证书）。** 定义总体残差乘积
\[
 \widetilde d_h=\mathbb E[
 (\varphi(u_{-h})-\widehat g_-(u_0))
 (\varphi(u_h)-\widehat g_+(u_0))].
\]
则
\[
 \boxed{\widetilde d_h-d_f(h)
 =\mathbb E[(g_--\widehat g_-)(g_+-\widehat g_+)],
 \quad |\widetilde d_h-d_f(h)|\le\varepsilon_-\varepsilon_+.}
\]
若 $|\varphi|\le B$、两拟合器裁剪到 $[-B,B]$，并使用 $m$ 组与训练独立且彼此独立的平稳三时刻样本，样本平均 $\widehat d_h$ 以至少 $1-\alpha$ 的概率满足
\[
 |\widehat d_h-d_f(h)|\le
 \varepsilon_-\varepsilon_+
 +4B^2\sqrt{2\log(2/\alpha)/m}=:a_m.
\]
因此 $\widehat d_h+a_m<0$ 认证一个非零组合缺陷，且
\[
 \left|-\widehat d_h/h^2-n_f\right|
 \le h\sqrt{n_f}c_f+h^2c_f^2/4+a_m/h^2.
\]

**证明。** 每个真实条件残差与任何当前可测函数正交，展开乘积后两个一阶回归误差项为零；剩下误差乘积，Cauchy–Schwarz 得界。每个样本乘积在 $[-4B^2,4B^2]$，Hoeffding 给采样预算，再合并定理 11.1。证毕。

这是 [SP20] 的广义残差协方差结构在本动力学目标上的定量应用。回归预算并非由训练损失自动提供；一条轨迹中重叠三元组也不满足这里的独立检验样本条件。负值是充分的记忆证据，未显著偏离零不能证明 Markov 性。不能据这个有前件证书宣称存在无假设、普遍有效的条件独立检验 [SP20, HPLDGS25]。

### 11.4 一次历史读数怎样降低真实预测风险

本节观测 $u$ 可以为向量，$u\in\operatorname{Dom}\mathscr L^2$，令 $c_2=\|\mathscr L^2u\|_2$。风险不含二分之一。当前 $u_0$ 精确已知，新增一个过去读数 $u_{-h}$，$h>0$，记信息集合 $\mathcal A_h=\sigma(u_0,u_{-h})$。

**定理 11.5（一个过去点的有限时间保证）。**
\[
 \mathbb E\operatorname{tr}\operatorname{Cov}(\mathscr Lu\mid\mathcal A_h)
 \le h^2c_2^2/4,
\]
\[
 \boxed{\inf_f\mathbb E\|u_t-f(u_0,u_{-h})\|^2
       \le \tfrac14t^2(t+h)^2c_2^2.}
\]
若过去读数改成 $u_{-h}+e$，$\|e\|_{L^2}\le\delta$，则
\[
 \boxed{\sqrt{\mathcal R_{h,\delta}(t)}
 \le t(hc_2/2+\delta/h)+t^2c_2/2.}
\]
该界不要求误差 $e$ 与状态独立。右侧中关于 $h$ 的两项在 $h=\sqrt{2\delta/c_2}$ 时最小，若这个延迟在允许范围内且 $c_2,\delta>0$。

**证明。** 可由信息集合计算的后向差商
$d_h=(u_0-u_{-h})/h$ 满足
$\|d_h-\mathscr Lu\|_2\le hc_2/2$。
条件期望是最优平方逼近，因此给第一式。未来 Taylor 余项至多 $t^2c_2/2$，对其作条件中心化后收缩，再用三角不等式得风险界。带误差差商至多再增加 $\delta/h$，同理可得。极小点由求导得到。证毕。

当 $h$ 与预测跨度 $t$ 同阶时，无噪声上界为 $O(t^4)$；要从这条预算继续保证四阶风险，需要过去测量的均方根误差 $\delta=O(t^2)$。这不是对所有模型的必要噪声条件。最优条件风险随信息增加不增，但具体拟合器或这个保守上界不自动具有相同改进幅度。

**命题 11.6（完整导数历史的分层风险）。** 令
$J_k=(u,\mathscr Lu,\ldots,\mathscr L^ku)$，$\mathsf P_k=\mathbb E[\cdot\mid J_k]$，并假设 $u\in\operatorname{Dom}\mathscr L^{k+2}$。置
$n_k=\|(I-\mathsf P_k)\mathscr L^{k+1}u\|_2^2$。则
\[
 \left|\sqrt{\inf_f\mathbb E\|u_t-f(J_k)\|^2}
 -\frac{t^{k+1}}{(k+1)!}\sqrt{n_k}\right|
 \le\frac{t^{k+2}}{(k+2)!}\|\mathscr L^{k+2}u\|_2.
\]
证明：积分 Taylor 展开中前 $k$ 阶全部是 $J_k$ 可测函数，作 $I-\mathsf P_k$ 投影即得。导数历史是理想信息，带噪延迟需单独预算，不能只据此宣称 Takens 式稳定嵌入。

### 11.5 四阶历史收益的可重建 Gaussian 实例

取四维标准 Gaussian 初态，$\Omega=\operatorname{diag}(J_2,2J_2)$，观测 $u=(q_1+q_2)/\sqrt2$，则
$f(t)=\mathbb E[u_tu_0]=(\cos t+\cos2t)/2$。当前风险为 $1-f(t)^2$。过去读数有独立 Gaussian 噪声方差 $\sigma^2$ 时，精确风险是
\[
 \mathcal R_{h,\sigma}(t)=1-
 \begin{pmatrix}f(t)&f(t+h)\end{pmatrix}
 \begin{pmatrix}1&f(h)\\f(h)&1+\sigma^2\end{pmatrix}^{-1}
 \binom{f(t)}{f(t+h)}.
\]
这是 Gaussian 条件协方差的直接 Schur 补。当 $h=t\downarrow0$，
\[
 \mathcal R_0(t)\sim\tfrac52t^2,\qquad
 \mathcal R_{t,0}(t)\sim\tfrac94t^4,\qquad
 \mathcal R_{t,\sigma}(t)\sim\tfrac{13}4t^4\quad(\sigma^2=t^4).
\]
将余弦 Taylor 级数代入上述有限矩阵式即得常数。这表明定理 11.5 的四阶收益在允许模型中确实出现，但一个历史点尚未恢复四维完整状态。

### 11.6 非线性磁模型的精确记忆坐标与奇异边界

回到第 10.5 节，记 $p=p_x$、$z=y-a x^2$、$w=p_y$。定义两个动态记忆坐标
\[
 r=\dot p+x^3=2\kappa axz+cw,\quad
 \chi=4\kappa a^2x^2+c^2,
\]
\[
 s=\dot r+\chi p
   =\kappa(2ap-c)z+2\kappa axw.
\]
于是
\[
 \binom r s=A(x,p)\binom z w,\quad
 A=\begin{pmatrix}2\kappa ax&c\\\kappa(2ap-c)&2\kappa ax\end{pmatrix},
 \quad \Delta=\det A=\kappa(4\kappa a^2x^2-2acp+c^2).
\]

**定理 11.7（四维记忆图的精确闭合与几何保持）。** 在 $\Delta\ne0$ 的开集上，$(x,p,r,s)$ 与完整状态光滑等价。将 $(z,w)^T=A^{-1}(r,s)^T$ 代入
\[
 \dot x=p,\quad \dot p=-x^3+r,\quad \dot r=s-\chi p,
\]
\[
 \dot s=2\kappa a(-x^3+r-\kappa x)z
       +\kappa(4ap-c)w-4\kappa a^2xp^2
\]
得到精确自治记忆模型。其推前 Poisson 矩阵 $J_{\rm mem}=D\Psi J_{\rm old}D\Psi^T$ 满足 Jacobi，且
\[
 \boxed{\det J_{\rm mem}=\Delta^2>0.}
\]
推前 Gibbs 密度为
\[
 \rho_{\rm mem}(x,p,r,s)\propto
 \frac{\exp[-\beta H(x,p,z(x,p,r,s),w(x,p,r,s))]}{|\Delta(x,p)|}.
\]

**证明。** 记忆方程由原多项式向量场逐项求导。映射对 $(z,w)$ 的 Jacobian 是 $A$，完整 Jacobian 为块下三角，故行列式为 $\Delta$，显式逆给图上的光滑等价。原 $(x,p,z,w)$ 坐标中的 Poisson 矩阵为
\[
 J_{\rm old}=\begin{pmatrix}
 0&1&0&0\\-1&0&2ax&c\\0&-2ax&0&1\\0&-c&-1&0
 \end{pmatrix},\quad \det J_{\rm old}=1.
\]
它来自合法磁 Poisson 矩阵的坐标变换。微分同胚推前保持括号与 Jacobi，行列式为 $\Delta^2$。Gibbs 公式保留逆 Jacobian 的绝对值。证毕。

一个记忆量 $r$ 一般不够：在 $\Delta\ne0$ 的点，固定 $x,p,r$ 仍可改变 $s$，从而改变 $\dot r$。这个模型的瞬时隐藏力协方差只有一个非零方向，仍需要两个独立记忆坐标才能在上述图上恢复全部动力学。它具体说明协方差秩与隐藏坐标维数不同。

**命题 11.8（几乎处处可恢复不保证全局噪声稳定）。** 若 $ac\ne0$，$\Delta=0$ 是 Gibbs 概率为零的超曲面，但对任意独立、均值零、协方差 $\sigma^2I_2$ 的记忆测量误差，$\sigma>0$，直接反演 $A^{-1}$ 的无条件均方误差无限大。这里当前 $x,p$ 被精确知道；该结论针对直接反演器，不针对所有正则化或 Bayes 估计器。

**证明。** 固定 $x$，奇异点为
$p_*=(4\kappa a^2x^2+c^2)/(2ac)$，且
$\Delta=-2\kappa ac(p-p_*)$。
Gibbs 中 $p$ 是全实支撑的 Gaussian。$2\times2$ 逆矩阵的 Frobenius 范数满足
$\|A^{-1}\|_F^2=\|A\|_F^2/\Delta^2\ge c^2/\Delta^2$，故其条件期望在 $p_*$ 邻域发散。直接反演的条件风险为 $\sigma^2\|A^{-1}\|_F^2$，再积分得到结论。证毕。

在守护区 $|\Delta|\ge d_0>0$、$\|A\|_F\le K_A$，记忆误差 $\eta$ 则给出
$\|\widehat{(z,w)}-(z,w)\|\le K_A\|\eta\|/d_0$。
显式奇异纤维：$\kappa=1,a=1/2,c=7/10,x=1,p=149/70$ 下，隐藏状态 $(z,w)=(0,0)$ 与 $(-7/10,1)$ 给相同 $r=s=0$，但 $\dot s$ 相差 $347/70$。因此这个图在奇异面不能继续被当作完整状态；额外更高导数、另一观测图或直接传感器需要独立处理。

### 11.7 从有限历史实现记忆图的一个误差预算

假设当前 $x_0,p_0$ 精确，过去 $p_{-h},p_{-2h}$ 各有绝对误差至多 $\varepsilon$，且轨迹段上 $|p'''|\le K_3$。定义
\[
 \widehat p'=(3p_0-4\widehat p_{-h}+\widehat p_{-2h})/(2h),
 \quad\widehat p''=(p_0-2\widehat p_{-h}+\widehat p_{-2h})/h^2,
\]
\[
 \widehat r=\widehat p'+x_0^3,\quad
 \widehat s=\widehat p''+(3x_0^2+\chi_0)p_0.
\]
Taylor 余项及二阶差分的双积分表达给出保守界
\[
 |\widehat r-r|\le K_3h^2+5\varepsilon/(2h),\quad
 |\widehat s-s|\le K_3h+3\varepsilon/h^2.
\]
乘以上节 $\|A\|_F/|\Delta|$ 的逆增益，得到隐藏状态恢复误差。这个指定模板可用 $h\asymp\varepsilon^{1/3}$ 平衡第二条预算；不宣称这一阶对任意高阶模板或采样设计最优。该段只处理有限历史恢复，不把导数观测当作无噪声现成输入。

### 11.8 同一个组合障碍的有限量子实例

有限维可见/隐藏系统上，用归一 Hilbert–Schmidt 内积，$\mathsf U_tX=e^{itH}Xe^{-itH}$、$\mathscr LX=i[H,X]$，以及正交条件期望
$\mathsf P X=e^{-1}\operatorname{Tr}_B(X)\otimes I_B$，其中 $e=\dim\mathcal H_B$。归一迹参考不变，所以定理 11.1 的全部投影恒等式与两延迟误差下界成立。每个约化 $\mathsf T_t$ 都是完全正、保幺算子，但不自动组成半群。

取 $H=Z\otimes Z$、隐藏初态 $I/2$。直接计算得到
\[
 \mathsf T_t(X)=\cos(2t)X,\quad
 (\mathsf T_{2h}-\mathsf T_h^2)X=-\sin^2(2h)X,
 \quad\|\mathsf Q\mathscr L(X\otimes I)\|_{2,n}^2=4.
\]
重复刷新隐藏系统时，$n$ 步的因子为 $\cos(2t/n)^n\to1$；不刷新时是 $\cos2t$。这与经典热动量刷新具有同一压缩算子机制。它是有限量子系统、无限温度参考下的明确定理实例，不把量子测量记录当作经典无扰动历史，也不将一般有限温相关态的条件期望默认为正交偏迹。

### 11.9 实际检错、文献定位与剩余义务

本轮程序通过 90 项符号或有限实例检查。四维双模模型的 80 位精度风险为：

| $t=h$ | 只知当前值 | 再知一个无噪过去值 | 过去噪声方差为 $t^4$ |
|---:|---:|---:|---:|
| 0.1 | 0.0247738899185762 | 0.000222629097589697 | 0.000321332038309279 |
| 0.03 | 0.00224816133612076 | 0.00000182076474901187 | 0.00000262981724051655 |
| 0.01 | 0.000249977292642337 | 0.0000000224976188537009 | 0.0000000324963188828699 |

非线性记忆图与完整模型在 $[0,0.2]$ 的合成轨迹比较中，最大状态差约 $2.30\times10^{-13}$；该轨迹的最小 $|\Delta|$ 约为 $0.73353$，没有穿越奇异面。固定有界相位模型的 200000 个独立检验三元组，残差统计约为 $-0.0594110$，包括给定回归误差的总半径约 $0.0248945$，认证非零记忆。该非 Gaussian 相位例使用指定不变概率，不承担非线性磁 Gibbs 图的假设。

[CHK02] A. J. Chorin, O. H. Hald, R. Kupferman. *Optimal prediction with memory*. Physica D 166, 239–257 (2002). DOI: 10.1016/S0167-2789(02)00446-3. 条件期望和保留未解变量记忆是已有理论，本章的复合缺陷来自同一标准投影代数。

[SP20] R. D. Shah, J. Peters. *The hardness of conditional independence testing and the generalised covariance measure*. Annals of Statistics 48(3), 1514–1538 (2020). DOI: 10.1214/19-AOS1857; arXiv:1804.07203. 使用残差协方差及回归误差乘积的既有方法，保留其条件独立检验不可能性边界。

[YR11] H. L. Yap, C. J. Rozell. *Stable Takens' Embeddings for Linear Dynamical Systems*. IEEE Transactions on Signal Processing 59(10), 4781–4794 (2011). DOI: 10.1109/TSP.2011.2160629; arXiv:1010.5938. 稳定性比一一对应更强，本章没有把它的线性充分条件原样用于非线性磁模型。

[EYWR18] A. Eftekhari, H. L. Yap, M. B. Wakin, C. J. Rozell. *Stabilizing Embedology: Geometry-Preserving Delay-Coordinate Maps*. Physical Review E 97, 022222 (2018). DOI: 10.1103/PhysRevE.97.022222; arXiv:1609.06347. 使用几何稳定延迟嵌入作为已有背景，没有认领一般 Takens 扩展。

[HPLDGS25] Z. He, R. Pogodin, Y. Li, N. Deka, A. Gretton, D. J. Sutherland. *On the Hardness of Conditional Independence Testing In Practice*. arXiv:2512.14000 (2025). 摘要明确强调条件均值嵌入误差和条件核选择，本章不据此假定回归误差已受控。

[LTPL23] 与 [PCR26] 的出处见第 10.9 节。前者区分回归 Mori–Zwanzig 记忆与直接延迟嵌入，后者的均值力目标以热力学一致性为评价重点；本章不把减少训练标签噪声当成删除真实动态记忆的理由。2026 年预印本 arXiv:2608.14001 的摘要另提出非均匀采样的广义 Vandermonde 秩猜想；本轮未取得其完整原文，未核定精确量词或结算状态，不将任何本章结果登记为该猜想的解答。

所有一般结论仍是纸面证明；数值与符号检查只用于检错。没有独立同行或异模型审定、Lean kernel、Scribe、canonical ingest、CI、硬件实验或神经网络 benchmark。下一层未解义务是：回归与相关轨迹的联合误差预算、跨奇异记忆图的稳定选择、可实现的量子测量历史，以及非线性长期预测中有限记忆截断的统一界。后续继续在本主卷追加。

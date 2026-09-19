# 辛预测完成：余切提升、量子闭包与采样可辨识性

**版本：** v1.0，2026-09-20。

**证明层级：** 本卷给出定义、条件明确的纸面证明、反例和可重建的代数算例。本文定理尚未由本卷配套的 Lean 证明项闭合；文中已有 Lean 声明仅作为各自陈述范围内的接口，不赋予本卷定理机器验证状态。余切提升、伴随方程、Koopman–von Neumann 表示、几何量子力学和结构保持降阶均有既有文献；本卷不作优先权主张。

## 0. 对象、约定与理论关系

本卷研究以下问题：给定演化规律与初始观测，为了预测其全部未来而补全的状态，何时自动具有辛结构；该结构怎样同时组织前向演化、伴随梯度、概率输运和量子观测。

一般观察商与 carry 的定义沿用 [动力接口余量卷](FORMAL_DYNAMICAL_INTERFACE_RESIDUALS.md) 第 1–4 节。本卷的主要额外假设是有限维、正定二次 Hamilton 函数和线性观测；这些假设使一般预测商具有可计算的非退化配对和最小能量提升。

默认列向量、实矩阵转置为 $T$、复矩阵伴随为 $\dagger$。标准 Poisson 矩阵与辛形式取

$$
J=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix},
\qquad \omega(u,v)=u^TJv,
\qquad \iota_{X_H}\omega=dH,
$$

所以 $X_H=J\nabla H$。对一般可逆反对称 Poisson 矩阵 $J_r$，对应辛形式的矩阵为 $-J_r^{-1}$。$\|v\|_M=(v^TMv)^{1/2}$ 只在 $M\succ0$ 时使用。

训练参数、演化时间和物理解释分别指定；同一数学变换可以有不同实现。下文每个等价关系均给出其对象与保持的结构。

## 1. 向量场的余切提升与目标敏感度

### 定理 1.1（前向流与伴随流的共同 Hamilton 函数）

设 $f_\theta:\mathbb R^d\to\mathbb R^d$ 为 $C^2$ 向量场，$\Phi_t$ 为其局部流。所有公式限制在流和导数存在的区间。定义

$$
\mathcal H_\theta(x,p)=p^Tf_\theta(x)
\quad\text{于 }T^*\mathbb R^d.
$$

则 Hamilton 方程为

$$
\dot x=f_\theta(x),\qquad
\dot p=-Df_\theta(x)^Tp,
$$

其流为

$$
\widetilde\Phi_t(x,p)
=\bigl(\Phi_t(x),D\Phi_t(x)^{-T}p\bigr).
$$

该流保持典范一形式 $\alpha=p^Tdx$，因此保持 $\omega=-d\alpha$。

**证明。** 对 $\mathcal H$ 分别求 $p$ 与 $x$ 的偏导即得方程。变分矩阵 $M(t)=D\Phi_t(x)$ 满足 $\dot M=Df_\theta(x(t))M$，故 $M^{-T}p$ 满足伴随方程。拉回一形式时有

$$
(M^{-T}p)^T M\,dx=p^Tdx.
$$

于是 $\widetilde\Phi_t^*\alpha=\alpha$，外微分给出辛形式保持。$\square$

### 推论 1.2（扰动与目标敏感度的配对守恒）

若 $\dot{\delta x}=Df_\theta(x)\delta x$，则

$$
\frac d{dt}(p^T\delta x)=0.
$$

给定 $C^1$ 终端损失 $\ell(x(T))$，令 $p(T)=\nabla\ell(x(T))$，则

$$
p(t)=D\Phi_{T-t}(x(t))^Tp(T).
$$

若初态与 $\theta$ 无关、损失无显式参数依赖，并且流对参数可微，则

$$
\nabla_\theta\ell(x(T))
=\int_0^T (\partial_\theta f_\theta(x(t)))^Tp(t)\,dt.
$$

**证明。** 第一式由乘积求导使两项抵消。参数变分 $s$ 满足 $\dot s=Df_\theta s+(\partial_\theta f_\theta)\delta\theta$、$s(0)=0$；积分 $d(p^Ts)/dt=p^T(\partial_\theta f_\theta)\delta\theta$ 即得梯度公式。$\square$

这与连续伴随和自动微分的既有理论相接 [SS16, CRBD18]。初态或损失显式依赖参数时，分别加上初态拉回项或显式偏导项。

### 命题 1.3（离散拉回与可逆性条件）

若 $F$ 为微分同胚，则

$$
(x,p)\mapsto\bigl(F(x),DF(x)^{-T}p\bigr)
$$

保持典范一形式。反向写成 $p_k=DF(x_k)^Tp_{k+1}$，恰为链式法则的协向量拉回。

**证明。** 与定理 1.1 的一形式计算相同。非可逆映射仍允许协向量拉回，但逆转置公式不再定义同维辛微分同胚。$\square$

**例。** $\dot x=-ax$ 的提升为 $\mathcal H=-axp$、$\dot p=ap$；$x$ 的收缩与 $p$ 的伸长保持面积。此构造本身不提供数值条件数改善。

## 2. 相同向量场的振幅表示

### 定理 2.1（完整流的半密度酉表示）

设光滑向量场 $f$ 在 $\mathbb R^d$ 上生成完整微分同胚流。于 $L^2(\mathbb R^d,dx)$ 定义

$$
(U_t\psi)(x)=|\det D\Phi_{-t}(x)|^{1/2}\psi(\Phi_{-t}(x)).
$$

则 $U_t$ 构成强连续酉群。在 $C_c^\infty$ 测试函数上，生成微分表达式为

$$
\left.\frac d{dt}U_t\psi\right|_{t=0}
=-f\cdot\nabla\psi-\tfrac12(\operatorname{div}f)\psi.
$$

相应 Schrödinger 形式是

$$
i\hbar\partial_t\psi=\widehat{\mathcal H}_f\psi,
\qquad
\widehat{\mathcal H}_f
=-i\hbar\bigl(f\cdot\nabla+\tfrac12\operatorname{div}f\bigr).
$$

**证明。** 以 $y=\Phi_{-t}(x)$ 换元，Jacobian 正好抵消，得到 $\|U_t\psi\|_2=\|\psi\|_2$。流复合律与 Jacobian 链式法则给出群性质。对紧支光滑函数，在充分小时间区间内，支集的流像落在共同紧集内；光滑性和控制收敛给出强连续性。再由稠密性与等距性推广到 $L^2$。在零时刻微分流与 Jacobian，即得生成表达式。自伴生成元由这个强连续酉群确定；这里不把形式对称性单独当作自伴性证明。$\square$

### 推论 2.2（概率输运与对称排序）

上述演化满足

$$
\partial_t|\psi|^2+\operatorname{div}(f|\psi|^2)=0.
$$

且令 $\widehat p_j=-i\hbar\partial_j$，有

$$
\widehat{\mathcal H}_f
=\tfrac12\sum_j(f_j\widehat p_j+\widehat p_jf_j).
$$

**证明。** 将振幅演化式与其复共轭相加，得到密度方程；对称排序式由乘积求导展开。$\square$

这给出同一个向量场在轨迹、余切、密度和振幅上的相容作用，属于广义 Koopman–von Neumann 表示 [J20]。原始读数 $a(x)$ 仍由相互对易的乘法算子表示；一般量子模型还须指定其可观测代数。

## 3. 有限维量子态的实辛表示与下降流

### 定理 3.1（Hermitian 演化的实化）

本节取 $\hbar=1$。令 $\widehat H=A_0+iB_0$ 为 Hermitian 矩阵，其中 $A_0^T=A_0$、$B_0^T=-B_0$，写 $\psi=(q+ip)/\sqrt2$。则 $i\dot\psi=\widehat H\psi$ 等价于

$$
\frac d{dt}\binom qp
=\begin{pmatrix}B_0&A_0\\-A_0&B_0\end{pmatrix}\binom qp
=J S_{\widehat H}\binom qp,
\qquad
S_{\widehat H}=\begin{pmatrix}A_0&-B_0\\B_0&A_0\end{pmatrix}.
$$

$S_{\widehat H}$ 对称，$JS_{\widehat H}$ 反对称；故流同时保持辛形式和欧氏内积。

**证明。** 分离 Schrödinger 方程的实部与虚部得矩阵公式。转置逐块计算得到两条对称性。对流的内积与辛配对求导，分别由 $G^T+G=0$ 和 $G^TJ+JG=0$ 得到守恒，其中 $G=JS_{\widehat H}$。$\square$

归一化态除去整体相位后得到复射影空间，其 Kähler 结构给出通常量子力学的几何表达 [AS97]。此处的 $S_{\widehat H}$ 无须正定；第 4–9 节的正定假设另行声明。

### 定理 3.2（归一化虚时间的能量下降）

设 $\|\psi\|=1$、$E(\psi)=\langle\psi,\widehat H\psi\rangle$。方程

$$
\partial_\tau\psi=-(\widehat H-E)\psi
$$

保持归一化，并满足

$$
\partial_\tau E
=-2\bigl(\langle\widehat H^2\rangle-E^2\bigr)\le0.
$$

射影实时间方向为 $-i(\widehat H-E)\psi$；两种方向由复结构相连。

**证明。** 对范数平方求导得 $-2(\langle\widehat H\rangle-E)=0$。对期望值求导并使用 Hermitian 性，得到所述方差。方差非负由 $\| (\widehat H-E)\psi\|^2\ge0$。$\square$

梯度的数值尺度依赖所选射影度量约定。虚时间变分优化的既有算法见 [McA19]。

## 4. 正定二次系统的规范预测商

本节起固定 $n\ge1$、$S=S^T\succ0$，定义

$$
H(z)=\tfrac12z^TSz,\qquad A=JS,\qquad \dot z=Az,
\qquad b=Cz.
$$

$C$ 是给定线性观测，不预先假定其可观测。定义协向量闭包

$$
W_0=\operatorname{im}C^T,\qquad
W_{k+1}=W_k+A^TW_k,\qquad
W=\operatorname{span}\{(A^T)^kc:c\in W_0,\ k\ge0\}.
$$

由 Cayley–Hamilton，$W=W_{2n-1}$。设 $r=\dim W$，取满行秩 $O\in\mathbb R^{r\times2n}$ 使 $\operatorname{im}O^T=W$。$C=0$ 时取零维平凡商；以下涉及逆矩阵的非平凡陈述取 $r>0$。

### 定理 4.1（未来等价与最小线性预测状态）

对任意 $z,z'$，以下等价：

$$
Ce^{At}z=Ce^{At}z'\quad(\forall t\ge0),
\qquad
CA^k(z-z')=0\quad(\forall k\ge0),
\qquad
Oz=Oz'.
$$

存在唯一 $K\in\mathbb R^{r\times r}$ 满足 $OA=KO$，并存在 $D$ 使 $C=DO$。所以 $y=Oz$ 满足自治方程 $\dot y=Ky$，且原观测为 $b=Dy$。

若另一线性编码 $Rz$ 能决定所有 $Ce^{At}z$，则 $\operatorname{rank}R\ge r$。

**证明。** 相同未来读数在零点的所有右导数相同，得到第二式。反向由矩阵指数级数成立。第二与第三式由 $W$ 定义等价。$A^TW\subseteq W$ 保证 $OA$ 的每一行可由 $O$ 表达；$O$ 满行秩给出 $K$ 唯一性。$W_0\subseteq W$ 给出 $C=DO$。任何充分的 $R$ 必须满足 $\ker R\subseteq\ker O$，故由秩与零空间维数公式得下界。$\square$

于是 $W$ 是算子 $V\mapsto W_0+A^TV$ 的最小不动点。最小性指全部连续未来读数及线性编码类；任意不连续集合编码不包含在维数下界中。

## 5. 预测闭包自动继承非退化辛配对

### 定理 5.1（正定预测闭包的非退化性）

在第 4 节假设下，双线性配对 $\sigma(a,b)=a^TJb$ 在 $W$ 上非退化。因此 $r$ 为偶数，且

$$
J_r=OJO^T
$$

可逆。

**证明。** 假设非零 $a\in W$ 位于限制配对的根空间。由 $A^Ta\in W$，有 $a^TJA^Ta=0$。但 $A^T=-SJ$，从而

$$
a^TJA^Ta=-a^TJSJa=(Ja)^TS(Ja)>0,
$$

其中使用 $J$ 可逆及 $S\succ0$，矛盾。故配对非退化。可逆反对称实矩阵只能为偶数阶：奇数阶时 $\det J_r=\det(-J_r^T)=-\det J_r$。$\square$

### 反例 5.2（去掉正定性后的一维预测商）

令 $H(q,p)=qp$。则 $\dot q=q$、$\dot p=-p$，仅保留 $q$ 就得到一维自治预测状态，而其 Poisson 配对退化。因此定理 5.1 的正定性不可直接删除。

## 6. 最小能量、辛提升与逐层约化的一致性

### 定理 6.1（约化 Hamilton 函数等于纤维最小能量）

在第 4 节假设下，令

$$
P=OS^{-1}O^T\succ0,\qquad
L=S^{-1}O^TP^{-1},\qquad
N=I-LO.
$$

则

$$
K=J_rP^{-1},\qquad
H_r(y)=\tfrac12y^TP^{-1}y
=\min_{Oz=y}\tfrac12z^TSz.
$$

极小点唯一，为 $Ly$。并有

$$
OL=I_r,\quad ON=0,\quad L^TSN=0,
$$

$$
H(z)=H_r(Oz)+\tfrac12(Nz)^TS(Nz).
$$

**证明。** 满行秩与正定性给出 $P\succ0$。由 $OA=KO$ 与 $AS^{-1}=J$，

$$
KP=OAS^{-1}O^T=J_r.
$$

其余代数关系由 $L,N$ 的定义得到，特别是 $L^TS=P^{-1}O$，故 $L^TSN=0$。每个 $Oz=y$ 的状态唯一写成 $z=Ly+w$、$Ow=0$；展开能量得

$$
\tfrac12z^TSz=\tfrac12y^TP^{-1}y+\tfrac12w^TSw.
$$

正定性给出唯一极小点与结论。$\square$

### 定理 6.2（最小能量提升与动力学、辛配对相容）

上述矩阵进一步满足

$$
AL=LK,\qquad AN=NA,\qquad NJO^T=0,
$$

$$
L^TJL=-J_r^{-1}.
$$

因此最小能量提升与流交换；隐藏余量不影响可见 Poisson 读数，且提升保持第 0 节约定下的辛形式。

**证明。** 先有

$$
AS^{-1}+S^{-1}A^T=0,\qquad KP+PK^T=0.
$$

第二式推出 $P^{-1}K=-K^TP^{-1}$。所以

$$
LK=-S^{-1}O^TK^TP^{-1}
=-S^{-1}A^TO^TP^{-1}
=JO^TP^{-1}=AL.
$$

结合 $OA=KO$ 得 $AN=NA$。又由 $AL=LK$ 及 $K=J_rP^{-1}$，得 $JO^T=LJ_r$，于是

$$
NJO^T=(I-LO)LJ_r=0.
$$

最后将 $JO^T=LJ_r$ 左乘 $L^TJ$：

$$
L^TJLJ_r=L^TJJ O^T=-L^TO^T=-I_r.
$$

右乘 $J_r^{-1}$ 即得辛形式公式。$\square$

### 定理 6.3（嵌套预测约化的一致性）

设 $D$ 满行秩，且 $DK=K_2D$。第二层观测为 $v=Dy$，其直接观测矩阵是 $O_2=DO$。令

$$
P_2=DPD^T,\qquad J_2=DJ_rD^T,\qquad
L_2=PD^TP_2^{-1}.
$$

则两层约化与直接约化给出相同的 $P_2,J_2,K_2$，且

$$
K_2=J_2P_2^{-1},\qquad
LL_2=S^{-1}O_2^TP_2^{-1}.
$$

**证明。** $O_2A=DKO=K_2O_2$，因此 $O_2$ 的行空间是完整系统的一个不变观测空间。定理 5.1 的证明适用于任何这样的空间，故 $J_2$ 非退化。代入定义有

$$
O_2S^{-1}O_2^T=DPD^T,\qquad O_2JO_2^T=DJ_rD^T.
$$

$K_2P_2=DKPD^T=DJ_rD^T$；提升公式由 $P^{-1}P=I_r$ 直接消去。$\square$

该命题把预测完成的分层与能量约化置于同一个相容系统中。其消元次序问题与仓库的 Schur 消元接口相接，具体状态提升由这里的矩阵公式给出。

## 7. 二次量子观测使用同一闭包

### 定理 7.1（相同观测矩阵的 CCR 与 Heisenberg 闭合）

考虑有限个正则量子模式，在 Schrödinger 表示及共同不变 Schwartz 域上取算子列 $\widehat z$，满足

$$
[\widehat z_i,\widehat z_j]=i\hbar J_{ij}I.
$$

令 $\widehat H=\tfrac12\widehat z^TS\widehat z$ 为 Weyl 对称二次算子，$S\succ0$。沿用第 4–6 节的 $O,P,J_r,K,L,N$。则

$$
\widehat y=O\widehat z,\qquad
[\widehat y_i,\widehat y_j]=i\hbar(J_r)_{ij}I,
$$

$$
\partial_t\widehat y=K\widehat y=J_rP^{-1}\widehat y.
$$

约化二次 Hamilton 算子为

$$
\widehat H_r=\tfrac12\widehat y^TP^{-1}\widehat y.
$$

**证明。** CCR 对二次对称乘积给出 $\partial_t\widehat z=(i/\hbar)[\widehat H,\widehat z]=JS\widehat z$。线性组合的交换子由 $OJO^T$ 给出，动力学由 $OA=KO$ 闭合。有效 Hamilton 算子的同一交换子计算产生 $J_rP^{-1}\widehat y$。$\square$

进一步，$NJO^T=0$ 给出 $N\widehat z$ 与每个 $\widehat y_i$ 对易。定理 6.1 的对称二次能量分解因而也在共同域上成立。对相应 Weyl 算子代数，演化的线性标签始终留在 $W$ 中，故可见子代数保持不变。量子 Kalman 分解的相关文献为 [ZGPG18, ZLDP23]。

### 推论 7.2（协方差的不确定性约束）

对具有有限二阶矩的态，令 $\Sigma$ 为对称协方差。约化协方差满足

$$
\Sigma_r=O\Sigma O^T,\qquad
\Sigma_r+\tfrac{i\hbar}{2}J_r\succeq0.
$$

该约束由约化流保持。

**证明。** 对任意复系数 $c$，算子 $X=\sum_jc_j(\widehat y_j-\langle\widehat y_j\rangle)$ 满足 $\langle X^\dagger X\rangle\ge0$，展开即得半正定式。又 $KJ_r+J_rK^T=0$，所以 $e^{Kt}J_re^{K^Tt}=J_r$。协方差和不确定性矩阵均按这个实可逆流作合同变换，保持半正定性。$\square$

这里有限的是正则模式数，每个模式的 Hilbert 空间仍为无限维；有限维矩阵不能满足非零常数的完整 CCR，因为交换子的迹为零。本节证明子代数的动力学闭合，不从均值与协方差认领任意量子态的完整恢复。

## 8. 不完全闭包的预测误差预算

### 定理 8.1（闭包残差的线性时间界）

保留 $S\succ0$、$A=JS$，现在只要求 $O$ 满行秩，不要求其行空间不变。定义

$$
P=OS^{-1}O^T,\quad J_r=OJO^T,\quad K=J_rP^{-1},
\quad E_{\mathrm{cl}}=OA-KO,
$$

$$
\epsilon_{\mathrm{cl}}
=\|P^{-1/2}E_{\mathrm{cl}}S^{-1/2}\|_2.
$$

则对全部 $z_0$ 与 $t\ge0$，

$$
\boxed{\|Oe^{At}z_0-e^{Kt}Oz_0\|_{P^{-1}}
\le t\,\epsilon_{\mathrm{cl}}\|z_0\|_S.}
$$

即使 $J_r$ 退化，该估计仍成立；$J_r$ 可逆时约化系统具有非退化辛形式。

**证明。** 由于

$$
A^TS+SA=0,\qquad K^TP^{-1}+P^{-1}K=0,
$$

原流和约化流在各自能量范数中等距。误差 $e(t)=Oe^{At}z_0-e^{Kt}Oz_0$ 满足

$$
\dot e=Ke+E_{\mathrm{cl}}e^{At}z_0,\qquad e(0)=0.
$$

Duhamel 公式给出

$$
e(t)=\int_0^t e^{K(t-s)}E_{\mathrm{cl}}e^{As}z_0\,ds.
$$

对积分逐项使用两边的等距性及诱导算子范数，得结论。$\square$

该界针对给定 $A,S,O$；由数据估计这些对象时，必须另外计算辨识误差。它也不直接覆盖非线性模型的有限时间误差。

## 9. 观察时钟、联合更新与混叠

### 命题 9.1（单时钟的精确闭包条件）

令 $F=e^{\Delta A}$、$\Delta>0$。离散观测闭包总包含于连续观测闭包。若 $A$ 在复数域可对角化，且 $\lambda\mapsto e^{\Delta\lambda}$ 在不同特征值上单射，则两者相同。

**证明。** 有限维不变空间对矩阵指数保持不变，给出第一方向。无碰撞时，对有限集合 $e^{\Delta\lambda}$ 作 Lagrange 插值，得到多项式 $p$ 满足 $p(e^{\Delta\lambda})=\lambda$；可对角化性给出 $A=p(F)$。矩阵均实，取该多项式与其系数共轭的平均可使系数实。因此任何 $F^T$ 不变空间也对 $A^T$ 不变，得到反向包含。$\square$

**反例。** $H=(q^2+p^2)/2$、观测 $q$ 的连续闭包为二维；$\Delta=2\pi$ 时 $F=I$，采样预测只需一维。这不与定理 5.1 冲突，因为离散闭包不再要求对 $A^T$ 闭合。

### 定理 9.2（两种无理比间隔的共同闭包）

令 $A=JS$、$S\succ0$，$\Delta_1,\Delta_2>0$，且 $\Delta_2/\Delta_1$ 无理。设 $F_j=e^{\Delta_jA}$，定义

$$
W_{12}=\operatorname{span}\{(F_1^T)^k(F_2^T)^\ell c:
 c\in W_0,\ k,\ell\ge0\}.
$$

则 $W_{12}=W$。

**证明。** $A$ 相似于实反对称矩阵 $S^{1/2}JS^{1/2}$，因此可对角化且具有有限纯虚谱。若两个不同频率 $\omega,\omega'$ 的相位对相同，则

$$
(\omega-\omega')\Delta_j=2\pi m_j\quad(j=1,2)
$$

且 $m_1,m_2$ 为非零整数，于是 $\Delta_2/\Delta_1=m_2/m_1$，矛盾。

因此有限谱上的相位对两两不同。对每个谱点，逐一选择能够区分它与其他点的一个坐标，乘起相应的一元线性因子，可构造在该点为 1、其余点为 0 的二元多项式。线性组合得到 $p$ 满足

$$
A=p(F_1,F_2).
$$

取系数共轭平均可令 $p$ 为实系数。故共同更新闭包对 $A^T$ 不变；连续闭包又对两个指数不变，得到相等。$\square$

本定理需要混合词，即观测时间 $k\Delta_1+\ell\Delta_2$ 所定义的联合更新闭包。无理比可以选黄金比，也可以选其他无理数。精确谱分离不提供统一有限噪声条件数。

### 反例 9.3（两条独立采样序列不足以替代共同闭包）

令 $\alpha=2\pi/\Delta_1$、$\beta=2\pi/\Delta_2$、$\omega_0>0$，且两个间隔之比无理。定义

$$
g(t)=\cos((\omega_0+\alpha+\beta)t)
-\cos((\omega_0+\alpha)t)
-\cos((\omega_0+\beta)t)+\cos(\omega_0t).
$$

则对全部非负整数 $k,\ell$，

$$
g(k\Delta_1)=g(\ell\Delta_2)=0,
\qquad g''(0)=-2\alpha\beta\ne0.
$$

所以两条独立采样序列都无法把 $g$ 与零轨迹区分。

**证明。** 对第一条序列，$\alpha k\Delta_1=2\pi k$，余弦项成对抵消；第二条由 $\beta\ell\Delta_2=2\pi\ell$ 同理。二阶导数直接展开得非零值。它是四个不同正频率的实线性组合，可由四个独立正定振子 $H_j=(p_j^2+\nu_j^2q_j^2)/2$、零初始动量及相应的 $\pm1$ 初始位置实现；观测取 $\sum_jq_j$。$\square$

本反例位于正定 Hamilton 系统内部，明确区分 $W_{12}$ 与两条独立序列各自闭包的线性和。

## 10. 非线性观测的闭合条件及其边界

### 命题 10.1（非线性预测与 Poisson 配对的相容条件）

令 $\Phi:U\subset\mathbb R^{2n}\to V\subset\mathbb R^r$ 为光滑满射次浸没，$J_r$ 为常数可逆反对称矩阵。若

$$
D\Phi(z)J\nabla H(z)=J_r\nabla h(\Phi(z)),
$$

$$
D\Phi(z)J D\Phi(z)^T=J_r,
$$

则 $y=\Phi(z)$ 的演化在潜空间中精确闭合，并且 $\Phi$ 是对所指定 Poisson 括号的映射：对任意光滑 $a,b$，

$$
\{a\circ\Phi,b\circ\Phi\}_J
=\{a,b\}_{J_r}\circ\Phi.
$$

**证明。** 演化式由链式法则得到。括号式由

$$
\nabla(a\circ\Phi)^TJ\nabla(b\circ\Phi)
=(\nabla a)^TD\Phi J D\Phi^T\nabla b
$$

及第二个假设得到。$\square$

两项分别约束动力学因子化与配对保持。符号上的重建精度不自动给出这两个条件。对非线性流形的结构保持约化已有 [BGH23]；此处把目标相对的预测闭合作为独立条件明确列出。

### 反例 10.2（非线性预测最小性不自动给出偶数维）

在去掉原点的平面上取 $H=(q^2+p^2)/2$。观测 $\Phi(q,p)=(q+ip)/\sqrt{q^2+p^2}\in S^1$。则

$$
\Phi(z(t))=e^{-it}\Phi(z(0)).
$$

因此相位是一个一维流形上的自治预测状态，且当前相位包含在目标族中。它不可能具有非退化二形式，因为一维切空间上的交替二形式恒为零。

**证明。** Hamilton 方程为 $\dot q=p$、$\dot p=-q$，故 $q+ip$ 乘以 $e^{-it}$，而模长守恒。维数结论由交替性得到。$\square$

所以第 5 节的自动辛结论须同时保留线性观测与正定二次生成元的范围。一般非线性扩展必须另证配对非退化、全局相容性与所需误差界。

## 11. 可重建的有理代数算例

取 $n=3$，令

$$
B=\begin{pmatrix}1&2&0\\2&-1&1\\0&1&2\end{pmatrix},\qquad
T=\begin{pmatrix}I_3&B\\0&I_3\end{pmatrix},
$$

$$
S_0=\operatorname{diag}(1,4,9,1,1,1),\qquad
S=T^{-T}S_0T^{-1},\qquad A=JS,
$$

$$
C=(1,1,0,0,0,0)T^{-1},\qquad
O=\begin{pmatrix}C\\CA\\CA^2\\CA^3\end{pmatrix}.
$$

$B$ 对称，所以 $T^TJT=J$；$S_0\succ0$ 给出 $S\succ0$。由于初始读数只涉及频率 1 与 2 的两个振子，直接相乘得

$$
CA^4=-4C-5CA^2,
$$

且

$$
J_r=OJO^T
=\begin{pmatrix}
0&2&0&-5\\
-2&0&5&0\\
0&-5&0&17\\
5&0&-17&0
\end{pmatrix},
\qquad \det J_r=81.
$$

由非零行列式可知 $\operatorname{rank}O=4$，闭包严格小于六维完整状态。用第 6 节定义构造 $P,K,L,N$，即可在有理数域中直接核验 $OA=KO$、$OL=I_4$、$AL=LK$、$NJO^T=0$ 和能量分解。该算例检验符号与坐标变换；一般结论由前述证明承担。

## 12. 与仓库既有接口的对应

[动力接口余量卷](FORMAL_DYNAMICAL_INTERFACE_RESIDUALS.md) 提供一般未来观测商和下降障碍的定义。本卷定理 4.1 是连续线性载体上的显式构造，定理 5.1 以正定性补上其辛非退化结构。

[`LocalCertificateCanonicalMinimality.lean`](../../../D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateCanonicalMinimality.lean) 中的 `local_certificate_canonical_minimality` 处理有限状态的预测等价、唯一商更新和状态数最小性。本卷的秩最小性是在不同载体上给出的证明，不把有限状态声明直接当作连续维数定理。

[`HamiltonianEffectCompletionGenerator.lean`](../../../D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator.lean) 中的 `hamiltonian_effect_completion_generator` 把有限矩阵观测轨道跨度与交换子幂闭包连接。第 7 节改用正则模式的线性观测与 CCR，其共同结构是生成元作用下的最小观测闭包；两者的 Hilbert 空间与算子域条件分别保留。

[`SchurComplementAssociativity.lean`](../../../D5/S3/Weil/ZetaLinear/SchurComplementAssociativity.lean) 处理具有逆算子见证的分步与一次消元一致性；本卷定理 6.3 同时追踪具体观测、能量矩阵和状态提升。

## 13. 参考文献与使用范围

[SS16] J. M. Sanz-Serna. *Symplectic Runge–Kutta Schemes for Adjoint Equations, Automatic Differentiation, Optimal Control, and More*. SIAM Review 58(1), 3–33, 2016. DOI: [10.1137/151002769](https://doi.org/10.1137/151002769). 用于伴随配对与辛积分的既有背景。

[CRBD18] R. T. Q. Chen, Y. Rubanova, J. Bettencourt, D. Duvenaud. *Neural Ordinary Differential Equations*. NeurIPS 2018. [arXiv:1806.07366](https://arxiv.org/abs/1806.07366). 用于参数化连续演化与伴随训练的背景，不据此认领本卷误差界覆盖数值求解器误差。

[J20] I. Joseph. *Koopman–von Neumann approach to quantum simulation of nonlinear classical dynamics*. Physical Review Research 2, 043102, 2020. DOI: [10.1103/PhysRevResearch.2.043102](https://doi.org/10.1103/PhysRevResearch.2.043102). 用于非 Hamilton 向量场的振幅表示；本卷不据此推断计算加速。

[AS97] A. Ashtekar, T. A. Schilling. *Geometrical Formulation of Quantum Mechanics*. [arXiv:gr-qc/9706069](https://arxiv.org/abs/gr-qc/9706069), 1997. 用于射影量子态空间的 Kähler 表述。

[McA19] S. McArdle et al. *Variational ansatz-based quantum simulation of imaginary time evolution*. npj Quantum Information 5, 75, 2019. DOI: [10.1038/s41534-019-0187-2](https://doi.org/10.1038/s41534-019-0187-2). 用于虚时间变分优化的背景。

[ZGPG18] G. Zhang, S. Grivopoulos, I. R. Petersen, J. E. Gough. *The Kalman Decomposition for Linear Quantum Systems*. IEEE Transactions on Automatic Control 63, 331–346, 2018. [arXiv:1606.05719v4](https://arxiv.org/abs/1606.05719v4); DOI: [10.1109/TAC.2017.2713343](https://doi.org/10.1109/TAC.2017.2713343). 用于量子可观测分解与允许坐标变换的既有范围。

[ZLDP23] G. Zhang, J. Li, Z. Dong, I. R. Petersen. *The Quantum Kalman Decomposition: A Gramian Matrix Approach*. [arXiv:2312.16082v1](https://arxiv.org/abs/2312.16082v1), 2023. 用于以 Gramian 描述量子子空间和辛坐标分解的背景。

[BGH23] P. Buchfink, S. Glas, B. Haasdonk. *Symplectic Model Reduction of Hamiltonian Systems on Nonlinear Manifolds and Approximation with Weakly Symplectic Autoencoder*. SIAM Journal on Scientific Computing, 2023. DOI: [10.1137/21M1466657](https://doi.org/10.1137/21M1466657). 用于非线性辛流形降阶与误差估计的既有路线；本卷的非线性条件不构成该领域的首次方法声明。

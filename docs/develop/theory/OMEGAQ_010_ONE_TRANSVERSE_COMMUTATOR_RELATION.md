# 一种横向顺序差：完整关系的三维刚性与量子表示

## 1. 完整预测窗口与内生比较

**定义 1.1（完整原前端）。** 在同一原签名 $\Omega$ 内固定一个归一来源。$x_a$ 是该来源经原总可逆控制 $a$ 后的完整未来概率行；共同未来保留所有合法终端请求、结果、失败、可读旧记录以及影响后续合法性的区别。原身份、端口、记录和合法性不取预测商；没有原定义的请求不以人为概率补齐。假设共同未来上的接续含空词、复合封闭、有同菜单内准确统计逆，并在全未来线性关系上良定。置

$$
V=\operatorname{span}_{\mathbb R}\{x_a\},\qquad
u(x_a)=1,\qquad W=\ker u=\operatorname{span}\{x_a-x_b\}.
$$

假设 $V$ 有限维且 $W\ne0$。此有限性是完整响应空间的条件，不从有限门数、有限标签或三维方向图推出。接续的矩阵闭包记为 $H$。定义

$$
c=\int_H hx_\epsilon\,dh,\qquad e=x_\epsilon-c,\qquad
G=H|_W,\qquad\mathfrak g=\operatorname{Lie}(G).
$$

以下仅消费这个前端所给出的有限实空间、紧有效 $G\subset GL(W)$、非零 $e$ 及 $W=\operatorname{span}(Ge)$。生成元首先属于原控制的数学闭包，不自动是可准确调用的连续设备。原概率前端和同一循环来源取自 [OmegaQ-009 定义 2.1、引理 2.2](https://github.com/the-omega-institute/trureturing/blob/85a80900fe528b1d85ca8b34e3d792fd4c19196c/docs/develop/theory/OMEGAQ_009_SINGLE_AXIS_SANDWICH_RIGIDITY.md#2-定义完整原窗口来源与二元夹持)。

**定义 1.2（复用的规范比较）。** 记 $n=\dim W$，采用 [OmegaQ-005 定义 2.3、引理 2.4](https://github.com/the-omega-institute/trureturing/blob/85a80900fe528b1d85ca8b34e3d792fd4c19196c/docs/develop/theory/OMEGAQ_005_ZERO_RESPONSE_COPLANARITY.md) 的原轨道协方差：

$$
C:W^*\longrightarrow W,\qquad
C\ell=\int_G\ell(ge)ge\,dg,\qquad
q(v,w)=\frac1n(C^{-1}v)(w).
\tag{1.1}
$$

定义 1.1 所引的前端引理给 $V=\mathbb Rc\oplus W$ 与紧有效的循环表示；上述协方差引理给 $C$ 可逆、$q$ 正定对称且 $G$-不变、$q(e,e)=1$。

## 2. 唯一候选：顺序差的横向响应只余一种

**定义 2.1（原导出关系与完整横向响应）。** 置

$$
\mathfrak h=[\mathfrak g,\mathfrak g]
=\operatorname{span}\{KL-LK:K,L\in\mathfrak g\},\qquad
E=e^{\perp_q}.
$$

对 $v,w\in E$，定义二元关系值

$$
\mathcal B_e(v,w)\in\mathfrak h^*,\qquad
\mathcal B_e(v,w)(K)=q(v,Kw).
\tag{2.1}
$$

它记录同一对横向内容在全部原顺序差下的响应。因为 $K$ 对 $q$ 斜对称，$\mathcal B_e$ 交替。等价地置

$$
\mathcal C_e:\mathfrak h\to\mathfrak{so}(E,q),\qquad
\mathcal C_e(K)=P_EK|_E.
\tag{2.2}
$$

有限维对偶性给 $\operatorname{rank}\mathcal C_e=\dim\operatorname{span}\mathcal B_e(E,E)$。$\mathfrak h$ 是原 Lie 闭包唯一确定的理想，不是另挑的控制菜单。

**假设 2.2（候选 $\Omega Q$-010）。**

$$
\boxed{\dim\operatorname{span}\{\mathcal B_e(v,w):v,w\in E\}=1.}
\tag{Q10}
$$

即 $\operatorname{rank}\mathcal C_e=1$。准确的一维同时要求非零与唯一；“至多一维”是另一条条件。全部核、秩与算子作用均在完整 $W$ 中解释。

**定义 2.3（比较口径）。** OmegaQ-009 的入口是存在 $A\in\mathfrak g$，满足 $\ker A=\mathbb Re$ 与 $\operatorname{rank}(K\mapsto AKA)=1$。候选 Q10 不指定 $A$，不另要求其完整核；直接展开的原算子词由三次 $AKA$ 换成二次 $KL-LK$。减少的是特选存在见证、显式条件项和词次数；没有另立假设独立性的比较标准。展开后须掌握全部 $(K,L)\in\mathfrak g^2$，并未减少完整方向域，也未断言总计算成本降低或模型类严格扩大。

## 3. 一条响应如何锁住完整三维

**定理 3.1（导出关系的单点刚性）。** 在定义 1.1 的前端中，Q10 当且仅当

$$
\boxed{\dim W=3,\qquad
\mathfrak g=\mathfrak h=\mathfrak{so}(W,q).}
\tag{3.1}
$$

此时 $G^\circ=SO(W,q)$，完整群为 $SO(W,q)$ 或 $O(W,q)$。

证明。所有原生成元都对 $q$ 斜对称。在 $\mathfrak g$ 上取正定型

$$
B(K,L)=-\operatorname{Tr}_W(KL).
$$

迹循环性给 $B([X,Y],Z)=B(X,[Y,Z])$，因而

$$
\mathfrak h^{\perp_B}=\mathfrak z(\mathfrak g),\qquad
\mathfrak g=\mathfrak z(\mathfrak g)\oplus^{\perp_B}\mathfrak h.
\tag{3.2}
$$

若 $Z$ 在 $\mathfrak h$ 的中心，它也与 $\mathfrak z(\mathfrak g)$ 交换，故 $Z\in\mathfrak h\cap\mathfrak z(\mathfrak g)=0$。所以 $\mathfrak h$ 中心为零。非零的此类紧型代数至少三维：$B([X,Y],Z)$ 是交替三形式；在维数不超过二时它为零，正定性遂使括号为零，与非零中心零矛盾。

相对于 $W=\mathbb Re\oplus E$，每个 $K\in\mathfrak h$ 唯一写成

$$
K=\begin{pmatrix}0&-v^\flat\\v&D\end{pmatrix},\qquad
v=Ke,\quad D=\mathcal C_e(K),\quad v^\flat(z)=q(v,z).
$$

因此零响应核恰由

$$
X_vz=q(e,z)v-q(v,z)e
\tag{3.3}
$$

组成。令 $U=\{v\in E:X_v\in\mathfrak h\}$、$k=\dim U$。评价 $X_v\mapsto X_ve=v$ 给 $U\cong\ker\mathcal C_e$，所以 Q10 给 $\dim\mathfrak h=k+1$。

对 $v,w\in U$，原 Lie 闭合保证 $[X_v,X_w]\in\mathfrak h$。直接计算得它固定 $e$，且在 $E$ 上为

$$
[X_v,X_w]z=q(v,z)w-q(w,z)v.
\tag{3.4}
$$

这些算子给出 $\Lambda^2U\to\operatorname{im}\mathcal C_e$ 的单射：在 $U$ 的正交基中，每个基楔恰作用于其独立坐标二平面。故 $\binom{k}{2}\le1$，从而 $k\le2$、$\dim\mathfrak h\le3$。Q10 排除零代数，前面的中心零结论迫使 $k=2$、$\dim\mathfrak h=3$。

取 $U$ 的基 $v,w$，令 $S=\operatorname{span}\{e,v,w\}$。三个独立算子 $X_v,X_w,[X_v,X_w]$ 张成 $\mathfrak h$；它们恰为 $S$ 上全部斜算子，并在 $S^\perp$ 为零。特别地

$$
S=\sum_{K\in\mathfrak h}\operatorname{im}K.
\tag{3.5}
$$

此时仅得三维活动支撑，尚未删除其余方向。每个 $g\in G$ 共轭保持导出理想，故由 (3.5) 保持 $S$；这也覆盖不连通分支。因为 $e\in S$，完整循环性给 $W=\operatorname{span}(Ge)\subseteq S$。所以 $W=S$。夹在 $\mathfrak h\subseteq\mathfrak g\subseteq\mathfrak{so}(W,q)$ 的两端均三维，故全部相等。

群的单位分支因此为 $SO(W,q)$；它在 $O(W,q)$ 中指数为二，完整 $G$ 只有所列两种。反向，在三维标准作用中，压缩像恰为二维平面 $E$ 的全部斜算子，其维数为一；导出代数也是全部 $\mathfrak{so}(3)$，故 Q10 成立。∎

## 4. 不用额外比较选择的关系与秩二禁区

**定理 4.1（无度量核、维数包络与比较独立性）。** 对任意有限维紧有效实表示及非零 $e$，以任一满足 $q(e,e)=1$ 的不变正内积定义 (2.2)。则

$$
\mathcal L_e:=\{K\in\mathfrak h:
\operatorname{im}K\subseteq\operatorname{span}\{e,Ke\}\}
=\ker\mathcal C_e
=\{0\}\cup\{K\in\mathfrak h:\operatorname{rank}K=2,\ e\in\operatorname{im}K\}.
\tag{4.1}
$$

特别地 $\mathcal L_e$ 是线性空间，$r=\operatorname{codim}_{\mathfrak h}\mathcal L_e=\operatorname{rank}\mathcal C_e$ 不依赖不变内积的选择。若 $k=\dim\mathcal L_e$，则

$$
\binom{k}{2}\le r,\qquad
\dim\mathfrak h\le r+
\left\lfloor\frac{1+\sqrt{1+8r}}2\right\rfloor,
\qquad r=0\ \Longleftrightarrow\ \mathfrak h=0.
\tag{4.2}
$$

证明。零压缩的块式恰为 (3.3)，非零时其像为 $\operatorname{span}\{e,v\}$。反之，若斜算子的像包含于 $\operatorname{span}\{e,Ke\}$ 且 $Ke=0$，其像至多一维，斜对称性使它为零。若 $Ke\ne0$，像恰为包含 $e$ 的二平面，斜对称性又迫使它为 $X_{Ke}$。任意秩二斜算子的像是其活动平面；若该平面包含 $e$，同一论证适用。这证明 (4.1)，其第一项完全由原算子与来源定义，所以余维与比较无关。

(3.4) 给一般 $\Lambda^2U$ 单射，得第一个不等式；解关于 $k$ 的二次不等式给第二式。若 $r=0$，则 $\dim\mathfrak h=k\le1$；中心零使 $\mathfrak h=0$。反向直接成立。∎

**定理 4.2（秩二不存在）。** 在定理 4.1 的范围内，$r\ne2$；此结论不要求来源循环。

证明。假设 $r=2$。由 (4.2)，$k\le2$，所以 $2\le\dim\mathfrak h\le4$。维数二已被中心零排除。维数四也不可能：在四维正内积空间中，交替三形式 $\tau(X,Y,Z)=B([X,Y],Z)$ 唯一写成 $\iota_z\mathrm{vol}$。若 $z=0$，括号为零；若 $z\ne0$，$\tau(z,X,Y)=0$ 对所有 $X,Y$ 成立，使 $z$ 为非零中心元。均矛盾。因此 $\dim\mathfrak h=3$、$k=1$。

取非零核元 $A_0=X_v$，其秩为二。三维的非零不变交替三形式是体积形式的倍数；选择并共同缩放一组正交基，可得 $A$ 与 $A_0$ 平行，且

$$
[A,B]=C,\qquad[B,C]=A,\qquad[C,A]=B.
\tag{4.3}
$$

令 $L=\operatorname{im}A$、$Z=\ker A$，在 $L$ 的正交基中写

$$
A=\begin{pmatrix}aJ&0\\0&0\end{pmatrix},\quad
B=\begin{pmatrix}bJ&T\\-T^{\mathsf T}&R\end{pmatrix},\quad
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad a>0.
$$

由 $[A,[A,B]]=-B$ 逐块得到 $b=0$、$R=0$、$(a^2-1)T=0$。$B\ne0$ 使 $T\ne0$，故 $a=1$。再由 $[B,[A,B]]=A$ 得

$$
\operatorname{tr}(TT^{\mathsf T})=1,\qquad T^{\mathsf T}JT=0.
\tag{4.4}
$$

第二式说 $\operatorname{im}T$ 是二维非退化交替型的全零子空间，故其维数至多一；第一式使其恰为一。令 $S=L\oplus\operatorname{im}T^{\mathsf T}$。于是 $A,B,C$ 在 $S^\perp$ 为零，并在三平面 $S$ 上张成全部斜算子。由于 $A$ 来自非零核元，$e\in\operatorname{im}A\subset S$。对 $e^\perp$ 的压缩像便只是在 $S\cap e^\perp$ 上的旋转线，秩为一，与 $r=2$ 矛盾。∎

**定理 4.3（秩三允许任意大完整空间）。** 对每个整数 $m\ge2$，存在紧有效、完整来源循环的表示，满足 $r=3$、$\dim W=3m$。

证明。取 $W=(\mathbb R^3)^m$，令 $G$ 是所有 $\operatorname{diag}(\varepsilon_1R,\ldots,\varepsilon_mR)$ 的矩阵群，其中 $R\in SO(3)$、各 $\varepsilon_j\in\{\pm1\}$。取 $e=(u,\ldots,u)$、$u\ne0$。独立符号的轨道线性组合分离每块，再由旋转张成每个三维块，故来源循环。导出代数是三个参数的对角 $\mathfrak{so}(3)$。每个非零元的秩为 $2m\ge4$，所以 (4.1) 给 $\mathcal L_e=0$、$r=3$。取轨道上的线性读口 $p(\pm\mid x,m)=\tfrac12(1\pm\langle m,x\rangle/\|e\|)$、$\|m\|=1$，可给出分离全部方向的有界归一概率前端。∎

## 5. 反向检验：每个保留条件排除了什么

**定理 5.1（高维、交换与隐藏方向反事实）。** 完整紧循环前端本身不推出 Q10；把“恰一”改成“至多一”，或删除循环性，都不能推出完整三维。

证明。$SO(n)$ 标准作用配 $e=e_n$ 的导出压缩秩为 $(n-1)(n-2)/2$，所以 $n=4,5$ 分别给三和六。$SO(2)^m$ 在 $(\mathbb R^2)^m$ 的直积作用配每块非零的来源有完整循环性，却有 $\mathfrak h=0$、$r=0$ 和任意偶数维。若令 $SO(3)$ 只作用于 $W=\mathbb R^3\oplus F$ 的第一项，并取 $e$ 在第一项，便有 $r=1$ 而完整维数为 $3+\dim F$；这准确违反循环性。前两类均可用定理 4.3 的有界线性读口方式实现概率前端。∎

**定理 5.2（只看方向标签与一次括号的假阳性）。** 截掉原响应方向，或在取括号后不继续原 Lie 闭合，可以把不满足 Q10 的模型误判为满足。

证明。取 $W=\mathbb R^3\oplus\mathbb R^2$、$G=SO(3)\times SO(2)$、$e=(u,v)$ 且两分量非零。来源循环，$\mathfrak h=\mathfrak{so}(3)\oplus0$。其非零算子的像不包含 $e$，故 (4.1) 给真实 $r=3$；若删除后两维，则报告 $r=1$。

再约定 $J_{ij}e_i=e_j,J_{ij}e_j=-e_i$。在五维取 $e=e_5$、$A=J_{12}$、$B=J_{23}+J_{34}+J_{45}$。仅最初二元跨度的一次括号给 $[A,B]=-J_{13}$，其横向像一维。但 $[A,[A,B]]=-J_{23}$，从而可提取 $J_{23}$；$[J_{23},B-J_{23}]=-J_{24}$，继而提取 $J_{34}$ 及 $J_{45}$。这些相邻转动生成全部 $\mathfrak{so}(5)$，真实 $r=6$。∎

**定理 5.3（非紧的无度量反模型）。** 离开紧表示范围，(4.1) 第一项的余维一条件不能推出三维。

证明。对任意 $n\ge4$，取 $W=\mathbb R^n$、$Ne_i=e_{i-1}$、$Ne_1=0$、$D=\operatorname{diag}(n-1,n-2,\ldots,0)$，有 $[D,N]=N$。闭连通群 $G=\{\exp(tN)\exp(sD):s,t\in\mathbb R\}$ 有效且非紧。对 $e=e_n$，多项式轨道 $\exp(tN)e$ 张成 $W$，但 $\mathfrak h=\mathbb RN$、$\mathcal L_e=0$，故余维为一。该模型退出了有界概率前端：有限循环有界轨道与准确群逆会使矩阵和逆矩阵一致有界，进而恢复紧闭包。它不是保留全部原概率条件而只删除紧性的模型。∎

**定理 5.4（实际连续器件不随闭包出现）。** 有满足 Q10 的原逆闭合控制群，不含任何非平凡连续单参数子群。

证明。取两根不同坐标轴上全部有理倍 $2\pi$ 的旋转，令 $\Gamma=\langle R_x(2\pi t),R_y(2\pi t):t\in\mathbb Q\rangle$，这是可数群。每个轴的完整圆群均在其闭包内，两圆群生成 $SO(3)$，故数学闭包满足 Q10。原群可数；非平凡连续单参数子群在矩阵群中不可数，所以它不可能在原菜单内。∎

## 6. 从返回量到球面与复数

**定理 6.1（返回系数、曲率与共同三维结构）。** Q10 下令 $T=\mathfrak h e=e^{\perp_q}$。对每个 $v\in T$，存在唯一 $X_v\in\mathcal L_e$ 使 $X_ve=v$，并且

$$
\beta(v,w)e=-X_vw,
\quad \beta(v,w)=q(v,w),
\quad [[X_v,X_w],X_z]
=X_{\beta(v,z)w-\beta(w,z)v}.
\tag{6.1}
$$

因此两步返回量给正比较，顺序差给单位球面曲率；归一闭包轨道是 $Ge=S_q^2\cong SO(3)/SO(2)$。同一秩一关系传播至每个单位来源点。

证明。定理 3.1 中 $\dim U=2$，故 $U=T$；(3.3) 给唯一性和返回公式，(3.4) 再与 $X_z$ 取括号给最后一式。对称空间约定 $R(v,w)z=-[[X_v,X_w],X_z]e$ 给

$$
R(v,w)z=\beta(w,z)v-\beta(v,z)w,
$$

所以每个正交单位二平面的截面曲率为一。完整 $SO(3)$ 作用给轨道及传播。所有不变正比较只差比例，$q(e,e)=1$ 固定之，故返回定义没有额外比较选择。

此返回结构的局部量子表示在同一证明内复用标准 Clifford–Pauli 构造，具体推导见 [OmegaQ-008 §8](https://github.com/the-omega-institute/trureturing/blob/85a80900fe528b1d85ca8b34e3d792fd4c19196c/docs/develop/theory/OMEGAQ_008_ONE_POINT_FIRST_ORDER_RECIPROCITY.md#8-复数复二维振幅与原-born-概率)。在 $J=\mathbb R\oplus W$ 上定义乘法

$$
(t,x)\circ(s,y)=(ts+q(x,y),\ ty+sx)
\tag{6.2}
$$

其标准构造给出与 $\operatorname{Herm}_2(\mathbb C)$ 同构的实 Jordan 代数。任选一个取向，以 $x\times y$ 表示相应叉积，令 $\delta_{(t,x)}(s,y)=(0,x\times y)$。则

$$
\delta_a a=0,\qquad
[\delta_a,\delta_b]=-[L_a,L_b],\qquad
\operatorname{Der}(J)=\mathfrak{so}(W,q).
\tag{6.3}
$$

具体地，复用标准 Clifford–Pauli 构造作中间步骤：$xy+yx=2q(x,y)1$ 的实 Clifford 代数在三维有实维数八。对正向正交基，$\jmath=e_1e_2e_3$ 中心、$\jmath^2=-1$。将 $e_i$ 送到 Pauli 矩阵 $\sigma_i$，八元基送到 $I,\sigma_i,iI,i\sigma_i$，故得到 $\mathrm{Cl}_{3,0}\cong M_2(\mathbb C)$，并将 (6.2) 送到对称矩阵乘法。这里是构造出的代数表示；四元数乘法的经典背景参见 [Baez, The Octonions, §2.1](https://math.ucr.edu/home/baez/octonions/node4.html) 及 [OmegaQ-009 §§7–9](https://github.com/the-omega-institute/trureturing/blob/85a80900fe528b1d85ca8b34e3d792fd4c19196c/docs/develop/theory/OMEGAQ_009_SINGLE_AXIS_SANDWICH_RIGIDITY.md)。

三维向量恒等式给 (6.3) 的前两式。任意 Jordan 导子消灭单位；将其作用于 $(0,x)^2=q(x,x)1$，先得其标量分量为零，再极化得向量部分斜对称。反向每个斜算子都是导子，故得最后一式。取向反转使 $\jmath\mapsto-\jmath$，所以复表示确定到共轭；完整 $O(3)$ 不选择绝对手性。∎

## 7. 全部原读数的 Born 表示与来源半径

**定义 7.1（完整有限接口）。** 在局部表示之外，若要承接全部有限复量子系统，另要求所消费的实际对象具有以下同一原接口：共同复中心；局部含幺 $*$-嵌入、交换且乘积张成的联合矩阵代数；全部指定联合正锥恰为同一联合矩阵代数的完整标准半正定锥；对每个输入块 $M_d$ 的原分支，供应可合法旁接的实际完整矩阵参考 $M_r$，其中 $r\ge d$；所有原分支在同一实线性 Hermitian 表示中下降，其唯一复线性延拓与该参考恒等映射的张量作用在完整联合标准正锥上保正。完整装置保留输出、失败、细记录、遗忘、具名返回及全部合法有限历史。对连续动力学另给实际连续确定可逆单参数过程与参数时钟。对理想投影更新另要求支撑内全部态不扰动。这些是实现与相容前件，不由 Q10 单独产生。

**定理 7.2（同一完整空间内更多准备的外半径校准）。** 在定义 1.1 的前端满足 Q10 时，另设 $\mathscr S\subset\{u=1\}\subset V$ 是包含定义 1.1 原行的全部指定归一准备；其完整坐标仍在 $[0,1]$，原可逆接续保持其闭凸包。对每个原结果评价，写 $f(tc+r)=\alpha_f t+q(b_f,r)$。则存在 $R\ge1$，使

$$
\overline{\operatorname{conv}}(\mathscr S-c)=RB_q,
\quad
\Phi_R(tc+r)=\tfrac12(tI+(r/R)\cdot\sigma),
\quad E_f^{(R)}=\alpha_f I+R b_f\cdot\sigma
\tag{7.3}
$$

给全部指定准备和原读口的忠实 Born 表示。原来源的像为 $\tfrac12(I+(e/R)\cdot\sigma)$，仅在 $R=1$ 时为纯态。

若还供应定义 7.1 中相应的实际接口，则这一概率表示接入下表的标准有限量子表述；每行只消费所列前件。

| 量子表述 | Q10 供应的结构与相应原条件 |
| --- | --- |
| 复 Hilbert 空间、纯态射线 | 定理 6.1 的标准代数构造给局部 $\mathbb C^2$，定理 7.2 给实际概率表示；实际更高对象和相干参考由原接口供应。 |
| Born 与混合态 | 原评价的 (7.2)/(7.3)；全数学标准正锥上的归一正泛函是密度矩阵，全部数学态是否实际可准备另列。 |
| 复合张量积 | 同一复中心、交换的含幺 $*$-嵌入及乘积张成，给 $M_m\otimes_{\mathbb C}M_n\cong M_{mn}$。 |
| 一般仪器 | 对每个输入块 $M_d$，实际旁接 $M_r$、$r\ge d$，其完整联合标准正锥上的保正性给 CP/Kraus；每支 TNI 与完整结果和 TP 由原质量关系给出。 |
| 理想投影更新 | CP、投影效果及全部支撑态不扰动给 $\rho\mapsto P\rho P$；成功后才按实际概率条件化。 |
| 薛定谔形式 | 同一简单块上的连续 CPTP 群且逆 CP，给 $\dot\rho=-i[H,\rho]/\hbar$；原时钟与作用量单位须标定。 |

证明。先对来源轨道复用 [OmegaQ-009 §7 的 Born 构造](https://github.com/the-omega-institute/trureturing/blob/85a80900fe528b1d85ca8b34e3d792fd4c19196c/docs/develop/theory/OMEGAQ_009_SINGLE_AXIS_SANDWICH_RIGIDITY.md#7-简单几何与原-born-概率)：对定义 1.1 的全部原行，置可逆线性表示

$$
\Phi(tc+r)=\tfrac12(tI+r\cdot\sigma),\qquad r\in W,
\tag{7.1}
$$

将每个原行送到迹一正矩阵，将每个原终端结果评价 $f$ 送到唯一 $0\le E_f\le I$，满足

$$
f(x)=\operatorname{Tr}(\Phi(x)E_f).
\tag{7.2}
$$

每个完整原菜单的全部结果（含原失败分支）给 $\sum_fE_f=I$。全部统计区别保留。

定理 3.1 给 $\overline{\operatorname{conv}}\{x_a-c\}=B_q$，因为原轨道在 $Ge=S_q^2$ 中稠密。写 $f(tc+r)=\alpha_ft+q(b_f,r)$。$f$ 在全部原行取值于 $[0,1]$，连续仿射性使它在整个球也如此，故

$$
\|b_f\|_q\le\min(\alpha_f,1-\alpha_f).
$$

取 $E_f=\alpha_fI+b_f\cdot\sigma$，其两个特征值为 $\alpha_f\pm\|b_f\|$，所以是效果。Pauli 的迹乘法给 (7.2)。完整菜单和等于 $u$，由非退化配对得效果和为 $I$；不能先删去失败再重新归一。$\Phi$ 在四实维上为同构，故不合并任何完整响应区别。

有限组实际分离坐标把全部概率有界性变成 $V$ 的有界性，故闭凸包紧。原接续保持与取逆给闭包 $SO(3)$ 的不变性。取最大半径 $R$；最大半径向量的全旋转轨道之凸包是 $RB_q$，而最大性给反向包含。原 $e$ 在其中且归一长为一，故 $R\ge1$。效果条件改为 $R\|b_f\|\le\min(\alpha_f,1-\alpha_f)$，其余同上面的来源轨道构造。

定理 3.1 与 6.1 给局部表示，以上证明完成原 Born 概率及半径校准。以下复用 [OmegaQ-009 §9 的有限矩阵推导](https://github.com/the-omega-institute/trureturing/blob/85a80900fe528b1d85ca8b34e3d792fd4c19196c/docs/develop/theory/OMEGAQ_009_SINGLE_AXIS_SANDWICH_RIGIDITY.md#9-完整有限量子理论定义定理与接口)，列出其承重步骤以固定条件。

迹配对将正泛函唯一写成 $\operatorname{Tr}(\rho\,\cdot)$；在全部秩一投影非负等价于 $\rho\ge0$，单位评价给 $\operatorname{Tr}\rho=1$。谱分解给自伴观测量及其投影概率。联合映射 $a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 是满射含幺 $*$-同态；源 $M_{mn}$ 单，故核为零。这使用实际联合前件，而非只看局部边缘。

对输入维数 $d$，完整矩阵参考维数至少 $d$ 时，Choi 矩阵 $(\mathcal E\otimes\operatorname{id})(|\Gamma\rangle\langle\Gamma|)$ 为正；谱分解并重排向量得 $\mathcal E(\rho)=\sum_\mu K_\mu\rho K_\mu^*$。迹不增与归一分别等价于 $\sum K_\mu^*K_\mu\le I$ 和完整结果上的总和等于 $I$。这是标准 Choi–Kraus 中间步骤，参见 [Watrous, The Theory of Quantum Information, Theorem 2.22](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)。$V\psi=\sum_{k,\mu}K_{k\mu}\psi\otimes|k,\mu\rangle$ 给数学等距扩张；补正交基可延成酉。数学环境指标不因此成为原可读记录。

若分支效果为投影 $P$，则每个 Kraus 算子满足 $K_\mu=K_\mu P$。支撑内每个纯态不扰动使各 $K_\mu\psi$ 与 $\psi$ 共线；对两个独立向量及其和用线性，得 $K_\mu=c_\mu P$，故分支恰为 $P\rho P$。零投影与秩一情形也包含。仅可重复不够，支撑内退相干给反例。

连续可逆 CPTP 群的 Heisenberg 对偶及其逆均为 UCP。两次 Schwarz 不等式相夹迫使取等，极化给乘法保持，故每个为 $*$-自同构。其生成元是内 $*$-导子；在矩阵单位上令 $B=\sum_i\delta(E_{i1})E_{1i}$，得 $\delta(a)=[B,a]$。去掉中心实部后 $B$ 斜自伴，写成 $iH/\hbar$ 即得薛定谔形式。有限中心不能被连续群非平凡置换，故直和逐块适用。

这些步骤也给有限矩阵完成中的无信号性、非交换不确定性与纠缠：完整局部 TP 由 Kraus 完整性保持远端约化态；迹正配对的 Cauchy–Schwarz 给方差乘积界；实际联合标准锥若包含 Bell 投影便有 $2\sqrt2$ 的 CHSH 值。实际供应相应联合锥是此处的前件。有限角与直和在数学上产生所有 $\bigoplus_sM_{d_s}(\mathbb C)$，不因此新增实际对象。

∎

**定义 7.3（纯态边界与操作范围）。** 数学球边界的 $P_n=\tfrac12(I+n\cdot\sigma)$ 是秩一投影，并有 $\operatorname{Tr}(P_nP_m)=(1+q(n,m))/2=\cos^2(\theta/2)$。它给 $S^2\cong\mathbb{CP}^1$ 与单位振幅的 $U(1)$ 相位纤维。定理 7.2 中原轨道情形的来源仅相对于其自身可逆轨道凸完成成为边界点；更多原准备须使用定理 7.2 的假设和半径。数学闭球、纯投影和全部 POVM 的存在，不等于每个元素均有实际原准备或原设备。

## 8. 单体判据的不充分性与原协变桥

**定理 8.3（单体几何不选择参考、更新或时钟）。** Q10 的单体结果不足以单独指定一般 CP 仪器、Lüders 更新或实际连续时钟。

证明。完整 $O(3)$ 的一个反射由转置表示，它保单体正性，却把 Bell 态一侧转置为 $\tfrac12\operatorname{Swap}$，其中有特征值 $-1/2$；单体前件未禁止这个群。对同一 POVM，$\mathcal I_j(\rho)=\operatorname{Tr}(E_j\rho)\tau_j$ 随任意输出态 $\tau_j$ 给相同结果概率，所以 Born 读数不选更新。定理 5.4 又说明 Lie 闭包不供应实际完整单参数器件。∎

**定义 8.4（与原 C128 的准确边界）。** [C123–C128 原卷 §§41–44](https://github.com/the-omega-institute/trureturing/blob/85a80900fe528b1d85ca8b34e3d792fd4c19196c/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md) 的 Z 与 SC 只已给出原交替双导子 $F_A(a,b)=D^A_ab$。其完整协变缺陷

$$
\mathcal C_A(K;a,b)=KF_A(a,b)-F_A(Ka,b)-F_A(a,Kb)
\tag{8.1}
$$

在每个原对象、实际联合与原 $K$ 上消失，仍是原候选的未决桥。定理 6.1 中构造的 $\delta$ 不能替换原 $D^A$，局部三维表示也不能代替全部对象上的证明。原中心、经典块及只有 $3^k$ 简单块而没有实际 $M_2$ 的满足族继续保留。数学 $\mathbb C^2$ 表示不等于原对象类别已供应实际 qubit。

## 9. 来源、选择问题与完整直观解释

**定义 9.1（来源与承重范围）。** 定理 3.1 的原导出理想单点压缩判据、定理 4.1 的无度量核与维数包络、定理 4.2 的秩二排除、定理 4.3 的无界维数族，是此处自证的仓内关系推导；不以有限检索断言历史优先权。Haar 比较、紧 Lie 代数的中心分解、Clifford–Pauli、球面和有限矩阵量子理论是成熟中间工具。相关文献的准确作用为：

| 来源 | 消费范围 |
| --- | --- |
| [Masanes–Müller–Pérez-García–Augusiak, arXiv:1111.4060v4, §II Theorem 1](https://arxiv.org/html/1111.4060v4) | 已给球形单系统、球面传递群及联合产品概率约束后的相互作用选择；不供应本卷完整 $W$ 三维性的证明。 |
| [de la Torre–Masanes–Short–Müller, arXiv:1110.5482, Theorem 2](https://arxiv.org/html/1110.5482) | 局部层析、相同的实际 qubit 以及连续可逆相互作用下的整体量子理论；“相同”还覆盖任意副本与置换合法性，不能以抽象局部矩阵表示替代。 |
| [Baez, The Octonions, §2.1](https://math.ucr.edu/home/baez/octonions/node4.html) | 四元数乘法的经典来源；本卷的 Pauli 复表示由定理 6.1 证明中的基像构造给出，不据叉积的存在单独宣称三维。 |
| [Watrous, The Theory of Quantum Information, §2.2 Theorem 2.22](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf) | 已有完整矩阵输入、输出及参考时的 CP、Choi 与 Kraus 等价。 |
| [OmegaQ-008](https://github.com/the-omega-institute/trureturing/blob/85a80900fe528b1d85ca8b34e3d792fd4c19196c/docs/develop/theory/OMEGAQ_008_ONE_POINT_FIRST_ORDER_RECIPROCITY.md)、[OmegaQ-009](https://github.com/the-omega-institute/trureturing/blob/85a80900fe528b1d85ca8b34e3d792fd4c19196c/docs/develop/theory/OMEGAQ_009_SINGLE_AXIS_SANDWICH_RIGIDITY.md) | 同一完整前端、旧三维选择准则及其后端量子接口；此处改变选择关系并自证新的秩谱后果，不重复计入经典消费者。 |

**定义 9.2（内生性与仍缺的选择律）。** 此候选的对象按 $\Omega\mapsto(W,G,e)\mapsto\mathfrak h\mapsto\mathcal L_e$ 定义，Q10 只约束这些定义之间的余维。约束对象都在整体内生，不蕴含所有整体都满足余维一；定理 4.3、5.1 已给其他值。尚缺的是：为什么实际原关系选择最小非零横向顺序差，而不取零或更高秩。定义“满足 Q10 的窗口”是合法分类，不是实际选择律的证明。准确秩也没有被小残差或有限抽样替代；无限维、无界算子、连续位置动量与场论仍需独立极限条件。

**定义 9.3（完整白话）。** 把完整系统想成一只保留全部旧痕迹的陀螺：失败、记录以及以后还能做什么，都不能擦掉。先选一个真实起点，再在原控制闭包的连续几何中，比较两次微小作用交换先后会留下什么；闭包中的方向不自动是可准确调用的器件。新候选只说，这些顺序差在起点横向只剩一种非零的独立响应。它没有先规定三维：若横向还有第三个独立方向，不同方向两两交换便会造出更多独立转法；若横向不到两个，又撑不起非交换。于是恰好两个横向方向，加上起点轴，形成三维活动空间；原来源能张成完整窗口，才进一步排除藏在旁边的其余方向。两步作用返回起点的多少，给出长度和夹角；交换先后的差，给出球面的弯曲。球面的纯边界点可表示成两个复振幅；本来源完整窗口的全部原行和读数则以密度矩阵及效果保持原值写成 Born 概率。若在同一完整空间内加入更多准备，且原可逆接续保持其闭凸包，就须按最外半径重新校准；这时原起点也可以是混合态。更多系统能否真实拼接、哪些测量能调用、记录怎样返回和时间如何标定，继续由同一个原系统的接口决定。仍须解释的是：为什么实际关系恰好选择这一种横向顺序差。

## 追加锚（本行以下为增补区）

## 10. 同范围协变桥的接入

**定义 10.1（原关系的全对象接回）。** 本卷定义 8.4 中的协变缺陷，在 [C123–C128 原卷定理 57.2、58.2](AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md) 的同一全事件 R 背景、Z 与 SC 下，对每个原对象和实际联合均为零。其证明使用原交替双导子的高秩斜延拓与实际乘积准备，始终保持原 $D$；不从本卷构造的 $\delta$ 回填。加上原 S 后，原全范围 C128 接回 C124 的有限量子结构及各自有条件的过程供应。这一接入不把 Q10 单体前件提升为完整 C128，也不生成实际 qubit、额外参考或连续时钟。

## 追加锚（本行以下为增补区）

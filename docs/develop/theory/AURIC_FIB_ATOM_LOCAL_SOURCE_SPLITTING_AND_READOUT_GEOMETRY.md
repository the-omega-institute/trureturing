# Auric FIB–ATOM：局部源分裂与读出几何

## 1. 固定局部载体与输入、输出标签

**定义 1.1（三个位置的合法支持）。** 位置索引为 $1,2,3$，合法支持集合为

$$
\Sigma=\{\varnothing,\{1\},\{2\},\{3\},\{1,3\}\}.
$$

以 $s_0,s_1,s_2,s_3,s_{13}$ 依次指称这五个不同状态。输入支持的集合记号不把 $\{1,3\}$ 拆成两个重复元素。输出标签映射另行定义为

$$
F(s_0)=[],\quad F(s_1)=[2],\quad F(s_2)=[3],\quad
F(s_3)=[5],\quad F(s_{13})=[2,5].
$$

这些输出是有限列表；$[2,5]$ 不是一个新 Fibonacci 数，也不是输入位置标签。本文的概率坐标始终按 $(0,1,2,3,13)$ 排列。

**定义 1.2（状态函数与概率载体）。** 令

$$
x(s_I)=\mathbf1_{1\in I},\qquad z(s_I)=\mathbf1_{2\in I},\qquad
y(s_I)=\mathbf1_{3\in I}.
$$

函数恒等式 $xz=zy=0$ 表示相邻排斥；$xy$ 不是零函数，它恰是 $s_{13}$ 的指示函数。状态载体、概率单纯形与质量零空间分别为

$$
\begin{aligned}
H&=\mathbb R^\Sigma\cong\mathbb R^5,\\
\mathcal D&=\{p\in H:p_I\ge0,\ \sum_Ip_I=1\},\\
T&=\{v\in H:\sum_Iv_I=0\}.
\end{aligned}
$$

$T$ 是 $\mathcal D$ 的仿射包络的平移空间，维数为四。记 $e_I$ 为 $H$ 的坐标基。为区别载体 $H$ 与向量读出，后者写为 $\mathsf H:\Sigma\to V$，其中 $V$ 是固定有限维实向量空间。

**定义 1.3（一阶观察及其导数）。** 定义线性延拓

$$
Q:H\longrightarrow\mathbb R^3,\qquad
Q(v)=(v_1+v_{13},v_2,v_3+v_{13}).
$$

概率观察是 $P=Q|_{\mathcal D}$，值的顺序为 $(X,Z,Y)$。在归一化变化空间上的导数记为 $DP=Q|_T$。联合坐标为 $\kappa(p)=p_{13}=\mathbb E_p[xy]$。此处 $DP$ 的定义域是 $T$，不能在核的计算中省略它。

## 2. 固定一阶数据的可行纤维

**数学引文 2.1（既有五态纤维）。** 复用[基础公式卷第四节的数学引文 4.2](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)及[局部时钟核卷 Q1](AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md)。基础卷按输出标签命名坐标 $2,3,5,25$；这里将它们依次改记为输入支持 $1,2,3,13$，并将均值排列为 $(X,Z,Y)$。在本记号下，所需前置是

$$
\begin{aligned}
p_\kappa&=(1-X-Z-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),\\
\ell&=\max(0,X+Z+Y-1),\qquad u=\min(X,Y).
\end{aligned}
$$

对 $b=(X,Z,Y)$，纤维 $\mathcal F_b=\{p\in\mathcal D:P(p)=b\}$ 非空的准确条件是

$$
Z\ge0,\qquad 0\le X,Y\le1-Z.
$$

此时 $\mathcal F_b=\{p_\kappa:\ell\le\kappa\le u\}$。宽度为 $u-\ell$；$u>\ell$ 称为非退化纤维，$u=\ell$ 为单点纤维。这里复用的是全部非负约束下的闭区间，不是允许任意实数 $\kappa$ 的仿射直线。

**数学引文 2.2（归一化隐藏方向）。** 同一前置给出

$$
d=(1,-1,0,-1,1),\qquad
N:=\ker(DP)=\mathbb Rd,\qquad
p_\kappa-p_{\kappa'}=(\kappa-\kappa')d.
$$

若将定义域改成整个 $H$，则 $\ker Q=\operatorname{span}\{e_0,d\}$，维数为二：$Q$ 的三行独立，且不读取空状态质量。质量零约束去掉独立的 $e_0$ 方向，才得到一维的 $N$。等价做法是在 $H$ 上增加质量行 $v\mapsto\sum_Iv_I$。

**约定 2.3（实际制备域）。** 若可取得的概率律仅属于 $\mathcal C\subseteq\mathcal D$，则实际固定观察纤维为 $\mathcal C\cap\mathcal F_b$，实际差异集为

$$
D_{\mathcal C,b}=\{p-q:p,q\in\mathcal C\cap\mathcal F_b\}.
$$

线性空间 $N$ 不声明每个形式方向都有实际制备。以下关于整条 $\mathcal F_b$ 的结论使用整个数学单纯形；限制制备域时，应把相应量词限制到 $\mathcal C$。

## 3. 源、局部参数与边界可行性

**定义 3.1（局部参数路径）。** 令 $J$ 为实区间，$p:J\to\mathcal D$ 为可微路径。$\lambda\in J$ 是曲线或操作族的参数；定义

$$
v(\lambda)=\frac{dp}{d\lambda}(\lambda),\qquad
\dot b=DP(v),\qquad \dot\kappa=v_{13}.
$$

参数的命名不指定普遍物理时间。改变参数 $\lambda=\phi(\eta)$ 时，源和所有沿路径的响应都乘以 $\phi'(\eta)$；允许反向参数化时，响应符号也随之改变。微分比较默认保持状态标签、观察者和读出函数固定，改变它们时采用第五、十一节的明确修正。

**定义 3.2（单侧可行锥与双侧方向）。** 对 $p\in\mathcal D$，定义

$$
\begin{aligned}
C_p&=\{v\in T:p_I=0\Rightarrow v_I\ge0\},\\
B_p&=\{v\in T:p_I=0\Rightarrow v_I=0\}.
\end{aligned}
$$

$C_p$ 刻画从 $p$ 出发的右侧一阶可行变化。$B_p$ 刻画以 $p$ 为参数内点的双侧可微概率路径的可能导数。它们与仿射包络变化空间 $T$ 是三个不同对象。

**定理 3.3（五态源的实际局部定义域）。** 对任意 $p\in\mathcal D$、$v\in T$，存在 $\varepsilon>0$ 使 $p+tv\in\mathcal D$ 对 $0\le t<\varepsilon$ 成立，当且仅当 $v\in C_p$。存在这样的双侧直线路径，当且仅当 $v\in B_p$。任意双侧可微概率路径在内点的导数属于 $B_p$。

证明。质量约束由 $v\in T$ 保持。在零坐标上，右侧非负恰要求 $v_I\ge0$；双侧非负恰要求 $v_I=0$。对有限个正坐标，取足够小的 $\varepsilon$ 就能保持非负。一般双侧可微路径的零坐标函数在内点达到局部最小值，导数为零。反向蕴含由上述直线路径实现。这里用的是单纯形的线性不等式，不把任意带符号 $v\in T$ 视为立即可执行的概率操作。∎

**定理 3.4（固定纤维上的单侧与双侧源）。** 设 $\mathcal F_b$ 非空。若 $u>\ell$，则在 $\ell<\kappa<u$ 的相对内点，$ad$ 对任意实 $a$ 都是双侧可行方向；在 $\kappa=\ell$ 处单侧可行恰要求 $a\ge0$，在 $\kappa=u$ 处恰要求 $a\le0$。纤维端点的双侧可微路径导数只能为零。若 $u=\ell$，纤维内没有非零可行方向。

证明。由数学引文 2.1，$p_\kappa+tad=p_{\kappa+ta}$。所有结论因此归结为参数是否留在闭区间 $[\ell,u]$ 中。端点处双侧可微 $\kappa(\lambda)$ 的导数为零；允许二阶进入纤维，例如 $\kappa(\lambda)=\ell+c\lambda^2$，并不改变这个一阶结论。相对内点可以满足 $Z=0$，此时状态 $s_2$ 的概率始终为零，而 $d_2=0$，所以仍可沿 $d$ 的两个符号移动。∎

## 4. 明确截面、规范分裂与截面自由度

**定义 4.1（零联合坐标截面）。** 对按 $(\dot X,\dot Z,\dot Y)$ 排列的 $b'\in\mathbb R^3$，定义

$$
L(b')=(-\dot X-\dot Z-\dot Y,\ \dot X,\ \dot Z,\ \dot Y,\ 0).
$$

这是线性映射 $L:\mathbb R^3\to T$，且 $DP\circ L=I_{\mathbb R^3}$。定义水平子空间 $T_{\mathrm{hor}}=\operatorname{im}L\subseteq T$。$\operatorname{im}(DP)=\mathbb R^3$ 是底空间，不能将它当作 $T$ 中的水平源子空间。此处没有指定度量，水平分裂也不声称是正交分裂。

**定理 4.2（五态源的规范分裂）。** 每个 $v\in T$ 在所指定截面 $L$ 下具有唯一分解

$$
v=L(DP(v))+v_{13}d,\qquad T=\operatorname{im}L\oplus\mathbb Rd.
$$

因此对定义 3.1 的路径，规范隐藏系数确为实际联合坐标导数 $\dot\kappa=v_{13}$。

证明。写 $DP(v)=(v_1+v_{13},v_2,v_3+v_{13})$，将其代入 $L$。由 $\sum_Iv_I=0$，差 $v-L(DP(v))$ 的五个分量依次为 $v_{13},-v_{13},0,-v_{13},v_{13}$。$L$ 的第五分量为零，而 $d$ 的第五分量为一，所以交空间为零，分解唯一。一般线性截面的直和机制是成熟线性代数；这里使用的是具体 FIB 坐标与这个明确的截面，参见 Axler [《Linear Algebra Done Right》第四版](https://linear.axler.net/LADR4e.pdf)第三章的核、像与商空间。∎

**定理 4.3（截面变化与隐藏系数变换）。** 每个线性右截面 $L'$ 都且只能写为

$$
L'=L+d\ell_0,\qquad \ell_0:\mathbb R^3\to\mathbb R\text{ 为线性泛函}.
$$

在此截面下，源的隐藏系数为

$$
a'=v_{13}-\ell_0(DP(v)),\qquad v=L'(DP(v))+a'd.
$$

只有 $DP(v)=0$ 时，源 $v=v_{13}d$ 及其系数才不依赖截面。

证明。$DP(L'-L)=0$，故 $L'-L$ 的像落在 $N=\mathbb Rd$；取第五坐标得到唯一的 $\ell_0$。代回分解即得系数变换。取 $DP(v)=0$ 后截面修正项消失。这里的唯一性相对于已选 $L$ 或 $L'$，不是任意代表之间的不变性。∎

**命题 4.4（任意代表不能定义实际 $\dot\kappa$）。** 取 $v=e_1-e_0=L(1,0,0)$，并取 $\ell_0(b')=\dot X$。则 $v_{13}=0$，但相对于 $L'=L+d\ell_0$ 的隐藏系数为 $-1$。

证明。$DP(v)=(1,0,0)$，所以 $L'(DP(v))=v+d$，而 $v=(v+d)-d$。在全支撑基点附近，$p+tv$ 是实际双侧概率路径，其联合坐标导数为零。这一导数没有随截面变成 $-1$；改变的是分裂中的系数。∎

**命题 4.5（可行总源的两个分量可以分别不可行）。** 在 $p=e_{13}$ 处，$v=e_1-e_{13}$ 是右侧可行源；它的规范水平分量与隐藏分量都不属于 $C_p$。

证明。$p+tv=(1-t)e_{13}+te_1$ 对 $0\le t\le1$ 可行。另一方面，

$$
DP(v)=(0,0,-1),\qquad L(DP(v))=e_0-e_3,\qquad v_{13}d=-d.
$$

水平分量在零坐标 $s_3$ 上为负，隐藏分量在零坐标 $s_0$ 上为负。它们相加才得到实际可行变化。因此直和分裂是代数分解；把两个分量当成可分别执行的干预，还须逐一验证可行性和操作实现。∎

## 5. 固定读出、移动读出与微分的含义

**定义 5.1（标量与向量状态统计）。** 对固定函数 $K:\Sigma\to\mathbb R$、$\mathsf H:\Sigma\to V$，令

$$
\tau_K(p)=\sum_Ip_IK(s_I),\qquad h_{\mathsf H}(p)=\sum_Ip_I\mathsf H(s_I).
$$

它们分别是标量与向量值状态统计。记 $\langle K,v\rangle=\sum_IK(s_I)v_I$，向量配对类似。定义读出的四角差

$$
\begin{aligned}
\Delta_{13}K&=K(s_{13})-K(s_1)-K(s_3)+K(s_0),\\
\Delta_{13}\mathsf H&=\mathsf H(s_{13})-\mathsf H(s_1)-\mathsf H(s_3)+\mathsf H(s_0).
\end{aligned}
$$

四角差是读出对 $d$ 的线性响应，复用[对称 seam 与 Fibonacci 层级卷 Q7、Q10 及第二部分第五节](AURIC_FIB_ATOM_SYMMETRIC_SEAM_PATH_DEFECT_AND_FIBONACCI_HIERARCHY.md)的质量零配对。向量差要求所有值在同一个 $V$ 中；没有给出线性载体时，不能直接平均抽象几何对象。

**定理 5.2（局部源读出的固定与移动链式法则）。** 对可微概率路径和固定读出，规范分裂给出

$$
\begin{aligned}
\dot\tau_K&=\langle K,L(\dot b)\rangle+\dot\kappa\,\Delta_{13}K,\\
\dot h_{\mathsf H}&=\langle\mathsf H,L(\dot b)\rangle+\dot\kappa\,\Delta_{13}\mathsf H.
\end{aligned}
$$

若 $K_\lambda$ 和 $\mathsf H_\lambda$ 在固定标签及固定值空间上可微，则完整公式为

$$
\begin{aligned}
\frac{d}{d\lambda}\tau_{K_\lambda}(p_\lambda)
 &=\langle K_\lambda,L(\dot b)\rangle
   +\dot\kappa\,\Delta_{13}K_\lambda+\langle\dot K_\lambda,p_\lambda\rangle,\\
\frac{d}{d\lambda}h_{\mathsf H_\lambda}(p_\lambda)
 &=\langle\mathsf H_\lambda,L(\dot b)\rangle
   +\dot\kappa\,\Delta_{13}\mathsf H_\lambda
   +\langle\dot{\mathsf H}_\lambda,p_\lambda\rangle.
\end{aligned}
$$

证明。有限求和的乘积法则给出读出变化项与概率变化项；对后一项使用定理 4.2 和四角配对。有限维链式法则是此处的标准前置，不构成新的微积分定理。特别地，固定概率律而移动读出可以产生非零响应，其来源是 $\dot K$ 或 $\dot{\mathsf H}$，不能归入 $\dot p$。∎

**命题 5.3（状态统计的积分不自动是流逝时间）。** 对分段 $C^1$ 路径和固定 $K$，

$$
\int_{\lambda_0}^{\lambda_1}\langle K,\dot p_\lambda\rangle\,d\lambda
=\tau_K(p_{\lambda_1})-\tau_K(p_{\lambda_0}).
$$

该积分可以为负；闭合概率路径上的积分为零，即使路径并非常值。

证明。应用实值微积分基本定理。具体取 $\bar p=(1/5,1/5,1/5,1/5,1/5)$、$0<\varepsilon<1/5$，令

$$
p_\lambda=\bar p+\varepsilon\sin\lambda\,d,\qquad K=xy,\qquad 0\le\lambda\le2\pi.
$$

这是一条固定 $P$ 的全支撑闭合路径，$\tau_K(p_\lambda)=1/5+\varepsilon\sin\lambda$，导数为 $\varepsilon\cos\lambda$，在部分区间严格为负，整圈积分为零。即使 $K\ge0$，它的期望沿路径也不必递增。这个反例排除把该响应自动解释为非负累计时间的推断。∎

**假设 5.4（等待和路径时钟的额外数据）。** 若要建立实际等待模型，应另给状态条件概率核 $W_I$，其值域包含非负等待量及明确的停止、无返回或无限等待标记。只有所有相关均值有限时，才可定义 $K(s_I)=\int t\,W_I(dt)$，并解释 $\tau_K$ 为该次等待的混合均值。多步累计量 $C(\gamma)=\sum_jt_j\ge0$ 还要求同一历史的联合等待、输出和后继律。

此假设引用[局部时钟核卷 Q5–Q7、Q10](AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md)的有限均值及共同历史条件。非负 $C$、加性路径增量和状态均值导数是不同的数学对象；命题 5.3 既不提供等待核，也不否定另有经校准的物理时钟。

## 6. 隐藏贡献、总响应与同源双读出

**定义 6.1（相对于截面的响应分量）。** 在规范截面 $L$ 下，记 $a=v_{13}$，定义

$$
\begin{aligned}
r_{K,\mathrm{hor}}&=\langle K,L(DP(v))\rangle,&
r_{K,\mathrm{hid}}&=a\Delta_{13}K,\\
r_{\mathsf H,\mathrm{hor}}&=\langle\mathsf H,L(DP(v))\rangle,&
r_{\mathsf H,\mathrm{hid}}&=a\Delta_{13}\mathsf H.
\end{aligned}
$$

对固定读出，总响应为两个分量之和。对移动读出，还须加入定理 5.2 的移动项。改用 $L'=L+d\ell_0$ 后，水平响应增加 $\ell_0(DP(v))\Delta_{13}K$，隐藏响应减少同一量；向量公式相同，总响应不变。

**定理 6.2（非零隐藏贡献与实际总变化的区分）。** 在固定读出、指定截面与实际可行源下，标量隐藏贡献非零当且仅当 $a\ne0$ 且 $\Delta_{13}K\ne0$；向量隐藏贡献非零当且仅当 $a\ne0$ 且 $\Delta_{13}\mathsf H\ne0$。这些条件不推出总响应非零。

证明。前两项使用实数域及实向量空间中的标量乘法。为验证最后一项，取全支撑基点附近的源 $v=e_{13}-e_0$，并取 $K=x-xy$。此时

$$
DP(v)=(1,0,1),\quad L(DP(v))=(-2,1,0,1,0),\quad a=1,
$$

$$
\Delta_{13}K=-1,\qquad
r_{K,\mathrm{hor}}=1,\qquad r_{K,\mathrm{hid}}=-1,\qquad
\langle K,v\rangle=0.
$$

实际路径 $p_t=\bar p+tv$ 对足够小的正负 $t$ 均可行，且 $K$ 的期望不变。只有已知水平基线、固定 $P$，或另有分离干预，才能从总响应扣出所声明的隐藏贡献。∎

**定义 6.3（单源联合响应映射）。** 若 $\mathsf H$ 与 $K$ 作用于同一初始律和同一源，固定模型的隐藏响应为

$$
S:\mathbb R\longrightarrow V\oplus\mathbb R,\qquad
S(a)=a(\Delta_{13}\mathsf H,\Delta_{13}K).
$$

此处向量与标量形成有类型的有序对。$\Delta_{13}\mathsf H=\Delta_{13}K$ 在一般 $V$ 上没有类型意义；比较它们必须给出 $V\to\mathbb R$ 的比较映射、量纲及校准约定。

**定理 6.4（五态同源响应的秩与比较范围）。** $S$ 的秩至多为一，且当响应对不为零时恰为一。若 $\Delta_{13}\mathsf H\ne0$，则在已知响应线 $\mathbb R\Delta_{13}\mathsf H$ 上有唯一线性泛函

$$
\psi(a\Delta_{13}\mathsf H)=a\Delta_{13}K.
$$

它满足 $\psi(r_{\mathsf H,\mathrm{hid}})=r_{K,\mathrm{hid}}$。这不推出整个状态统计之间的 $\tau_K=\psi\circ h_{\mathsf H}$，也不选择 $V$ 全空间上的唯一延拓。

证明。$S$ 的像由一个响应对张成。非零向量 $\Delta_{13}\mathsf H$ 使其倍数的系数唯一，所以 $\psi$ 良定义。选择响应线的补空间可以延拓 $\psi$，但当 $\dim V>1$ 时补空间上的取值通常任意。状态统计另含常数和水平项。具体取 $V=\mathbb R$、$\mathsf H=xy$、$K=x$：$\psi=0$，但 $h_{\mathsf H}=\kappa$、$\tau_K=X$，后者可随 $X$ 改变，不能由 $\kappa$ 单独决定。当 $V$ 本身就是响应线时延拓无需选择，仍不消除这个水平项障碍。∎

**命题 6.5（未知源幅度与未知灵敏度的混淆）。** 只观察隐藏响应对 $a(u,c)$，而 $a$、$u\in V$、$c\in\mathbb R$ 都未知时，不能唯一识别源幅度及灵敏度。

证明。对每个非零实 $r$，参数 $(ra,u/r,c/r)$ 产生相同响应对。即使要求 $a>0$，仍有任意 $r>0$ 的混淆。非零总变化还可能包含水平与移动读出项。反演 $a$ 需要已知或经校准的非零响应、所选截面和相应基线；同源性本身没有提供这些数据。∎

## 7. 单个读口的精确能力与取得边界

**定理 7.1（非退化五态纤维上的单读口分离）。** 固定可行 $b$、固定已知 $K$，并假设 $u>\ell$。则 $p\mapsto\tau_K(p)$ 在整条 $\mathcal F_b$ 上单射，当且仅当 $\Delta_{13}K\ne0$。取任意可行基点 $\kappa_0\in[\ell,u]$，此时

$$
\tau_K(p_\kappa)=\tau_K(p_{\kappa_0})+(\kappa-\kappa_0)\Delta_{13}K,
$$

$$
\kappa=\kappa_0+
\frac{\tau_K(p_\kappa)-\tau_K(p_{\kappa_0})}{\Delta_{13}K}.
$$

证明。使用数学引文 2.2 的差分和四角配对。非零斜率分离任意两个不同 $\kappa$；零斜率则整条非退化纤维恒值。使用可行基点避免把可能不可行的 $\kappa=0$ 对应物误认作概率制备。此为[局部时钟核卷 Q1–Q4](AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md)的固定核逆式在标量读口上的应用。∎

**约定 7.2（退化与观测对象）。** 若 $u=\ell$，$P$ 已确定整条单点纤维，额外读口可以为常数。定理 7.1 的“一个读口”指同一来源的精确总体期望；它不是一次样本、未知响应模型的反演，也不是在没有 $P$ 时识别整个四维概率单纯形。向量读口或输出律读口的相应条件是其在 $d$ 上的响应非零，但同样要求固定模型及精确读出。

**命题 7.3（单读口误差与一次样本的反例）。** 在定理 7.1 的固定精确 $b$、基线和灵敏度下，若期望估计误差至多为 $\epsilon$，则未截断的逆式误差至多为

$$
|\widehat\kappa-\kappa|\le\frac{\epsilon}{|\Delta_{13}K|}.
$$

然而，一个非零读口的单次样本仍可来自不同纤维点。

证明。相减逆式即得误差界。取 $K=xy$、$X=Y=1/2$、$Z=0$，并取 $\kappa=1/8$ 或 $1/4$。一次 $K$ 观测为 Bernoulli 样本，两种律都以正概率产生零，也都以正概率产生一，所以单个输出不能确定参数。该误差界不支付 $P$ 的噪声、基线与灵敏度的校准误差；非零斜率也没有统一正下界。实际可取得的读口、重复制备、样本依赖及求逆算法资源需要分别指定。∎

## 8. 较长窗口的源响应张量与联合秩

**数学引文 8.1（既有 Fibonacci 层级）。** 对 $n$ 个位置，令 $\Sigma_n$ 为路径的不相邻支持，$H_n=\mathbb R^{\Sigma_n}$、$T_n=\{v:\sum_Iv_I=0\}$。复用[对称 seam 与 Fibonacci 层级卷 Q7–Q10、第二部分第三、四、七节](AURIC_FIB_ATOM_SYMMETRIC_SEAM_PATH_DEFECT_AND_FIBONACCI_HIERARCHY.md)的独立集计数、单项式基与质量增广核维数：

$$
|\Sigma_n|=\operatorname{Fib}_{n+2},\qquad
h_{n,1}=\operatorname{Fib}_{n+2}-n-1.
$$

这里 $\operatorname{Fib}_0=0,\operatorname{Fib}_1=1$，$n$ 是位置数。前三个非零例子为 $h_{3,1}=1$、$h_{4,1}=3$、$h_{5,1}=7$。这些是全局线性隐藏维数；边界纤维及限制制备域仍可更小。计数和高阶单项式维数是此处的既有前置，不再作为新的计数定理。

**定义 8.2（所选隐藏基的响应列）。** 对合法 $A\subseteq\{1,\ldots,n\}$，定义

$$
d_A=\sum_{B\subseteq A}(-1)^{|A|-|B|}e_B.
$$

前置的包含关系反演给出 $\langle x_C,d_A\rangle=\mathbf1_{C=A}$。所以只固定质量和一阶矩时，$\{d_A:|A|\ge2\}$ 是 $N_1\subseteq T_n$ 的基；固定所有至多 $r$ 阶矩时，余下基为 $|A|>r$。对共同源上的线性读出 $R:H_n\to W$，令

$$
\mathcal S_R=(R(d_A))_{A\in\mathcal B},\qquad
R\left(\sum_{A\in\mathcal B}a_Ad_A\right)=\sum_{A\in\mathcal B}a_AR(d_A),
$$

其中 $\mathcal B$ 是所选隐藏基的索引集。若 $W=\mathbb R^m$，这些列组成响应矩阵；对向量或测度值读出，它们组成同一值空间内的线性列族。源系数与响应列的配对可称为源响应张量，但需要保留两端的载体和基。

**定理 8.3（FIB 多源的联合分离条件）。** 设 $N\subseteq T_n$ 是维数 $h$ 的隐藏子空间，$R=(R_1,\ldots,R_m)$ 为 $m$ 个固定标量读口。它分离 $N$ 内全部形式源，当且仅当 $\operatorname{rank}(R|_N)=h$，因此要求 $m\ge h$。若实际纤维含一个全支撑律，且其仿射差异空间为 $N$，同一条件也等价于该整条概率纤维上的精确读出单射。

证明。以标准秩–零化度定理为前置，源分离等价于 $N\cap\ker R=\{0\}$。若核中存在非零 $v$，全支撑基点附近的小扰动 $p+tv$ 可行，并产生不同律、相同读出。反之，任何两个纤维点的差在 $N$ 中，零核保证其相等。边界或受限制备域的准确条件是 $D_{\mathcal C,b}\cap\ker R=\{0\}$；不能无条件用全空间秩替代。更换隐藏基 $d'_B=\sum_AC_{AB}d_A$ 时，响应矩阵右乘可逆矩阵 $C$，列和系数随之改变而联合秩不变。∎

**命题 8.4（两个非零隐藏列的相消及补充读口）。** 在四个位置的八态模型中，考虑二维隐藏子空间 $N_*=\operatorname{span}\{d_{13},d_{14}\}$。读口 $f=x_1x_3+x_1x_4$ 在两个基方向上都非零，却不能分离 $N_*$。添加 $g=x_1x_3-x_1x_4$ 后可以分离 $N_*$。

证明。由定义 8.2，

$$
R_f(d_{13})=R_f(d_{14})=1,\qquad
R_f(d_{13}-d_{14})=0.
$$

差方向为 $d_{13}-d_{14}=e_4-e_3+e_{13}-e_{14}$。在均匀八态律附近，乘以任意 $0<|t|<1/8$ 给实际不可区分的不同概率律。添加第二读口后的响应矩阵为

$$
\begin{pmatrix}1&1\\1&-1\end{pmatrix},
$$

其行列式为 $-2$。这只补齐所声明的二维子空间；四位置的一阶隐藏空间还有 $d_{24}$，在整个三维隐藏空间上仍须检验第三方向。前一个读口的相消机制与层级卷 Q10 的同源 Bernoulli 核例一致，不把“每列非零”误作“列族独立”。∎

**定义 8.5（五位置的三阶残余源）。** 五个位置的 $\Sigma_5$ 有十三个状态：空支持、五个单点、六个二点支持 $13,14,15,24,25,35$，以及三点支持 $135$。这里不是“五个状态的窗口”。既有层级给出一阶隐藏维数七；再固定全部二点矩后，仅剩三阶方向

$$
d_{135}=-e_0+e_1+e_3+e_5-e_{13}-e_{15}-e_{35}+e_{135}.
$$

它对所有至多二阶单项式配对为零，对 $x_1x_3x_5$ 配对为一。对读口 $f$ 的源响应为

$$
R_f(d_{135})=\sum_{B\subseteq\{1,3,5\}}(-1)^{3-|B|}f(s_B).
$$

因此一个对该三阶方向非零的标量读口只在全部低阶矩已固定、残余纤维非退化时补齐这个最后方向；它不能凭同样一个数补齐先前七维的全部一阶隐藏源。

## 9. 完整未来记录必须来自共同初始源

**假设 9.1（完整记录合同）。** 固定初始载体 $H$、初始状态标签和已知操作模型。令 $\mathcal W$ 包含空词、合同中的全部合法有限操作词，以及需要时的合法观察依赖策略。每个 $w\in\mathcal W$ 指定共同记录空间 $(E_w,\mathcal E_w)$，及从初态 $s_I$ 出发的完整记录概率律 $\Gamma_{w,I}$。记录保留实际输出、分支概率及合同要求的等待、拒绝、停止和未完成标记；不能只保留终点。

合法性须对同一比较域有共同意义。可采用在全部可能状态上共同启用的动作，或将拒绝明确编码为输出的总化合同。观察依赖策略在同一已取得历史上选择同一动作，不能按未观测真态选择不同动作。不同长度的记录若声称属于同一过程，须有截断投影及相容性。此处消费[局部时钟核卷 Q6、Q9–Q10](AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md)及[层级卷 Q11](AURIC_FIB_ATOM_SYMMETRIC_SEAM_PATH_DEFECT_AND_FIBONACCI_HIERARCHY.md)的合同。

**定义 9.2（共同初始载体上的线性全历史映射）。** 令 $\mathcal M(E_w)$ 为有限带符号测度的实向量空间，定义

$$
A_w:H\longrightarrow\mathcal M(E_w),\qquad
A_w(q)=\sum_Iq_I\Gamma_{w,I}.
$$

这是对初始质量的线性映射，对 $p\in\mathcal D$ 给出精确完整记录律。对事件 $B\in\mathcal E_w$，$q\mapsto A_w(q)(B)$ 是标量线性测试。任意实值加权测试给期望，只有事件或声明的概率测试直接给概率。

**定义 9.3（输出分支的线性实现）。** 在列概率约定下，一步输出子核 $M_{a,o}$ 将当前带符号质量映到后继载体。对完整分支 $r=(o_1,\ldots,o_k)$，保留联合质量

$$
\mu_r=M_{a_k,o_k}\cdots M_{a_1,o_1}q,\qquad
\Pr_q(r)=\mathbf1^{\mathsf T}\mu_r.
$$

每个合法动作的全部输出子核之和保持总质量；停止或拒绝须包含在输出中，或另行明确次概率语义。将每条分支及其质量保留，才得到定义 9.2 的全历史映射。仅用平均转移后的末态读数，需要先证明过去记录能从该末态恢复，否则不能替代 $A_w$。

**命题 9.4（末态与条件均值不足以替代全记录）。** 若先输出 $xy$ 的值，再将内部状态重置为 $s_0$，则所有末态律相同，而完整记录可以区分固定 $P$ 的非退化纤维。只报告“输出一条件下的值为一”也不能保存这种区分。

证明。输出一的无条件概率为 $\kappa$，输出零的概率为 $1-\kappa$；重置不改变已发出的输出。这复用局部时钟核卷 Q12 的输出后重置构造。条件均值等于一时已除掉分支质量 $\kappa$。一般后选择 $B$ 的条件记录为 $A_w(p)(\cdot\cap B)/A_w(p)(B)$，只有分母正时定义，而且对 $p$ 不再线性；遗漏该分母会遗漏可识别信息。∎

## 10. 源的未来可见性与有限见证

**定义 10.1（质量零与初始隐藏方向上的未来盲核）。** 在假设 9.1 下，定义

$$
\begin{aligned}
K_m&=T\cap\bigcap_{w\in\mathcal W,\ |w|\le m}\ker A_w,&
K_\infty&=T\cap\bigcap_{w\in\mathcal W}\ker A_w,\\
N_m&=N\cap K_m,&N_\infty&=N\cap K_\infty.
\end{aligned}
$$

这些核比较的是共同初始源的差异。$N$ 已施加初始 $P$，故 $N_m$ 是仍对所声明未来记录盲的初始隐藏方向。$K_{m+1}\subseteq K_m$、$N_{m+1}\subseteq N_m$；包含关系依靠记录族累积，不声称每个新步骤都严格缩小。

**定理 10.2（五态局部源的全记录识别）。** 对同一合同中的 $p,q\in\mathcal D$，其全部有限完整记录律相同，当且仅当 $p-q\in K_\infty$。若另有 $P(p)=P(q)$，准确条件为 $p-q\in N_\infty$。在非退化固定五态纤维上，未来族分离整条纤维，当且仅当存在合法 $w$ 使 $A_w(d)\ne0$。

证明。各记录差为 $A_w(p)-A_w(q)=A_w(p-q)$；归一化给 $p-q\in T$。加上初始 $P$ 时，差属于 $N$。五态的同纤维差是 $(\kappa-\kappa')d$，一个非零响应即可分离所有不同参数；所有响应为零时则整条非退化纤维不可分。这里识别精确律族，不识别单条随机历史。若过程在共同标准 Borel 路径空间上且可测结构由有限柱集生成，既有 $\pi$–$\lambda$ 测度唯一性前置还将“所有相容有限记录律相同”提升为“整个路径律相同”，见局部时钟核卷 Q7。∎

**约定 10.3（全概率域与受限域的准确判据）。** 全单纯形包含全支撑基点，所以其全部律的未来识别等价于 $K_\infty=\{0\}$；固定 $P$ 的全局识别等价于 $N_\infty=\{0\}$。实际域 $\mathcal C$ 上则分别检验

$$
(\mathcal C-\mathcal C)\cap K_\infty=\{0\},\qquad
D_{\mathcal C,b}\cap N_\infty=\{0\}.
$$

只比较质量一的概率律时，不必要求整个 $H$ 上的公共核为零。若全记录映射保持并读取质量，质量行本身已被观察，ambient 判据可以与质量零判据对应；没有该行或质量合同，就应明确使用 $T$ 或实际差异集，而不能默换定义域。

**定理 10.4（固定有限源的有限见证与无统一任意路径截止）。** 对固定合同、有限维 $N$ 及全历史映射族，存在至多 $\dim N$ 个合法有限记录映射，其在 $N$ 上的公共核恰为 $N_\infty$。因而该合同有一个有限的见证长度上界。但只知道共同初始载体有限维，不能推出适用于所有任意路径合同的统一长度上界。

证明。以有限维子空间降链为标准前置。从 $N$ 开始，若当前交核严格大于 $N_\infty$，取其中不属于 $N_\infty$ 的向量。某个 $A_w$ 不湮灭它，加入该映射使维数至少下降一。至多 $\dim N$ 次后达到公共核。每个选中的词有限长，取其长度的最大值即得固定合同的有限见证。

为检验量词，任取整数 $D\ge0$，给出相容路径核：从初态 $s_I$ 出发，前 $D$ 个输出为零，第 $D+1$ 个输出为 $xy(s_I)$，以后为零。共同初始载体仍为五维，前 $D$ 步对 $d$ 的响应为零，第 $D+1$ 步才响应。$D$ 可以任意大，故不存在仅由初始五维给出的统一截止。实现这个延迟须有外部阶段、计数记忆或相应扩大的动态载体；它不是固定五态自治仪器的反例。

若另有固定完整 $D_0$ 维线性仪器、固定生成算子族和末端测试空间，则算子闭包稳定化可给维数相关的更强 horizon，复用局部时钟核卷 Q11。任意历史核没有那个递推不变性，仅出现一次 $N_m=N_{m+1}$ 不能认证永久稳定。∎

**定义 10.5（改变取得核与改变初始律的桥梁）。** 对固定 $p$ 而变化的历史核族 $\Gamma_{w,I,\lambda}$，事件读出变化为

$$
\frac{d}{d\lambda}A_{w,\lambda}(p)(B)
=\sum_Ip_I\frac{d}{d\lambda}\Gamma_{w,I,\lambda}(B),
$$

其中假设每个事件概率可微。它不是固定 $A_w$ 下的初始源响应 $A_w(\dot p)$。若要统一两者，需给扩大源载体、包含核参数的状态、固定联合读出以及从实际模型到该载体的映射。没有这个桥梁，取得核盲方向与 $N\subseteq T$ 的概率源方向只能分别讨论；层级卷 Q6、Q10–Q11 已限定两类模型的差别。

## 11. 观察者指标、固定运输与局部源综合

**假设 11.1（跨载体比较的运输）。** 对每个观察者 $\omega$，先固定其状态标签、归一化域、局部参数及读出值空间 $V_\omega$。若这些载体沿参数变化，必须指定可微平凡化或共同源运输。一个有限维线性合同可写为

$$
J_{\omega,\lambda}:H_*\to H_\omega,\qquad
p_{\omega,\lambda}=J_{\omega,\lambda}q_\lambda,
$$

其中 $J$ 非负且保持质量，$q_\lambda$ 是共同初始载体上的概率路径。若向量值空间也变化，另给到固定比较空间的线性识别，并把该识别并入读出。运输、状态选择与读出均须对应同一实际来源；仅有同名标签或数值相等不提供该合同。

**定理 11.2（运输下的源与读出链式法则）。** 在假设 11.1 的固定值空间表示中，设读出算子为 $\widehat K_{\omega,\lambda}:H_\omega\to\mathbb R$，则

$$
\begin{aligned}
v_\omega&=\dot J_{\omega,\lambda}q_\lambda
             +J_{\omega,\lambda}\dot q_\lambda,\\
\frac{d}{d\lambda}\bigl(\widehat K_{\omega,\lambda}J_{\omega,\lambda}q_\lambda\bigr)
 &=\dot{\widehat K}_{\omega,\lambda}J_{\omega,\lambda}q_\lambda
   +\widehat K_{\omega,\lambda}\dot J_{\omega,\lambda}q_\lambda
   +\widehat K_{\omega,\lambda}J_{\omega,\lambda}\dot q_\lambda.
\end{aligned}
$$

向量读出具有同样的有类型公式。若 $J$ 和读出都固定，只有共同源变化项；若运输或读出变化，则其导数不能遗漏。

证明。有限维算子乘积法则给出三项。质量保持使 $v_\omega$ 属于质量零空间。非单射运输可以合并共同源差异，故不能反向推断被合并信息仍可恢复；不同观察者的隐藏核是否对应，还须检验其观察映射与运输的交换关系。∎

**定理 11.3（观察者相对的五态局部源几何综合）。** 固定一个观察者 $\omega$ 的五态模型、截面 $L_\omega$、共同初始来源及完整记录合同。设路径在实际概率域内可微，向量读出 $\mathsf H_\omega$ 与标量读出 $K_\omega$ 固定，或按定理 5.2 和 11.2 给出移动项。则其局部源几何由下列共同关系确定：

$$
\begin{aligned}
\dot p_\omega
 &=L_\omega(\dot X_\omega,\dot Z_\omega,\dot Y_\omega)
   +\dot\kappa_\omega d_\omega,\\
\dot h_\omega
 &=\langle\mathsf H_\omega,L_\omega(\dot b_\omega)\rangle
   +\dot\kappa_\omega\Delta_{13}\mathsf H_\omega
   +\langle\dot{\mathsf H}_\omega,p_\omega\rangle,\\
\dot\tau_\omega
 &=\langle K_\omega,L_\omega(\dot b_\omega)\rangle
   +\dot\kappa_\omega\Delta_{13}K_\omega
   +\langle\dot K_\omega,p_\omega\rangle,\\
N_{\omega,\infty}
 &=\ker(DP_\omega)\cap\bigcap_{w\text{ 合法}}\ker A_{\omega,w}.
\end{aligned}
$$

固定读出时，移动项为零；移动读出时，应按其实际导数保留这些项。更换 $L_\omega$ 时，隐藏系数按定理 4.3 变化而总响应不变。将实际总源称为纯隐藏源，需要 $DP_\omega(\dot p_\omega)=0$，此时总源本身为 $\dot\kappa_\omega d_\omega$；一般源的规范隐藏分量只是相对于 $L_\omega$ 的组成部分。它能否单独执行仍由 $C_{p_\omega}$、$B_{p_\omega}$ 及实际操作合同决定。

对固定 $P_\omega$ 的非退化纤维，一个非零已知线性响应分离其精确律；多维隐藏源须检验整个联合响应的秩。未来可见性使用同一初始源上的完整记录 $A_{\omega,w}$，而不是忽略分支质量的末态摘要。对受限制备域，识别判据还须限制到实际差异集。

证明。第一行由定理 4.2，第二、三行由定理 5.2；变动载体时先用定理 11.2 拉回共同表示。边界可行性由定理 3.3–3.4，分量及相消边界由定理 4.5、6.2，联合秩由定理 6.4、8.3，未来识别由定理 10.2–10.4。这些关系组合的是同一来源、同一参数与明确运输下的结果，不能把不同制备、不同未知核或未配对读数拼成一个源。

本综合是局部模型的应用性数学推导，不把成熟线性代数、有限概率混合、包含关系反演或测度唯一性认作新一般定理。$\tau_\omega$ 的状态统计含义由定义 5.1 给出；实际等待和路径累计须满足假设 5.4。赋予 $h_\omega$ 空间意义、赋予 $\tau_\omega$ 物理时间单位，或将两个响应解释为引力，需要额外的物理载体、动力学、仪器及校准映射。同源秩一关系没有认证这些实现，也不推出所有全局对象或全局时间都不存在。∎

## 追加锚（本行以下为增补区）

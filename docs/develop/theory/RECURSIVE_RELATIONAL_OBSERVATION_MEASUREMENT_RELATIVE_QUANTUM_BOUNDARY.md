# 递归关系观察：实际等待读出下的近似单份量子边界

## 1. 五模式来源、实际仪器与共同端口

**假设 1.1（独立量子制备与指定行走）。** 固定复 Hilbert 空间 $\mathcal H=\mathbb C^5$，单位正交基依次为

$$
(e_N,e_2,e_3,e_5,e_{25}),\qquad
\mathsf S=\{N,2,3,5,25\},\qquad \Pi_s=e_se_s^\dagger.
$$

允许的输入是全部密度算子 $\mathcal D(\mathcal H)=\{\varrho\ge0:\operatorname{tr}\varrho=1\}$。这项制备假设独立于原生 $\alpha/\beta$ 有序树；标签 $N$ 表示范数一的模式向量，不是零向量、未读或停止。复用 [AURIC 第 61、63、73 章](https://github.com/the-omega-institute/trureturing/blob/bcf8bc4317eb78b19f2d0f5076318bf3dc5a3324/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md) 的同一矩阵

$$
K=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix},\qquad U(t)=\exp(-itK),\quad t\ge0.
$$

**定义 1.2（实际有限协议）。** 一次模式读使用完整的五结果秩一 Lüders 仪器

$$
\mathcal J_s(X)=\Pi_sX\Pi_s\qquad(s\in\mathsf S).
$$

协议只能选择非负等待 $U(t)$、这一模式读以及 Stop；选择依赖实际保留的记录和控制状态。每个协议有有限深度，协议族遍历所有有限深度。完整保留历史包括取得的结果、所选控制和停止记录。若允许经典随机控制，其随机资源与输入无关，且两次比较使用同一随机策略。初始控制资料与未知输入无关；它没有原输入、参考纠缠或其他量子载体。隐藏 Kraus 指标不是可读记录。

不增加独立模式相位、任意酉、任意 Hermitian 效果或同效果的其他仪器；没有拷贝、复位、数量口、概率理想读出或隐藏侧信道。由一次模式读的结果组成事件，只是该完整读的经典后处理，不是额外的粗块 Lüders 仪器。

**定义 1.3（预先固定的有限 flag 端口与误差）。** 对 $q\in\{1,2,3,4,5\}$，记 $\mathfrak C_q$ 为所有如下复合通道 $T$ 的集合：存在有限集合 $F$ 及固定 CPTP 映射

$$
\operatorname{Enc}:M_5(\mathbb C)\longrightarrow
\bigoplus_{f\in F}M_q(\mathbb C),\qquad
\operatorname{Dec}\bigl((Y_f)_{f\in F}\bigr)
=\sum_{f\in F}\operatorname{Dec}_f(Y_f),\qquad
T=\operatorname{Dec}\circ\operatorname{Enc},
$$

其中每个 $\operatorname{Dec}_f:M_q\to M_5$ 在整个 flag 块上 CPTP。编解码器先于未来协议固定，不能依赖未知输入或随后选择的协议。全部量子信息通过此端口；不另存原输入，没有预共享纠缠或其他量子旁路。经典 flag 有限且在此量子端口准则中免费；它由解码器使用，解码后不作为附加的输入相关资料提供给未来策略。

记 $P_\varrho^\pi$ 为同一策略 $\pi$ 在输入 $\varrho$ 上的完整保留历史分布，令

$$
\begin{aligned}
e(T)&=\sup_{\varrho\in\mathcal D(\mathcal H)}
\sup_{\pi\text{ 为实际有限协议}}
\operatorname{TV}(P_\varrho^\pi,P_{T(\varrho)}^\pi),\\
\varepsilon_q&=\inf_{T\in\mathfrak C_q}e(T).
\end{aligned}
$$

离散分布的 $\operatorname{TV}$ 是 $\ell^1$ 距离的一半；含可测随机控制时取相应概率测度的全变差距离。这里仅在协议开始前替换一次输入，后续实际仪器与策略相同。CPTP 仍要求对任意未触及参考的关联输入物理合法；所定义的性能只测试系统实际菜单的历史分布，没有增加联合参考测量。

**约定 1.4（被动实帧与既有精确结论）。** 复用 AURIC 第 65.2–65.3、79.1–79.4 条，置

$$
\begin{gathered}
D=\operatorname{diag}(1,i,i,i,1),\qquad
A=-iD^\dagger KD=
\begin{pmatrix}
0&1&1&1&0\\
-1&0&0&0&-1\\
-1&0&0&0&0\\
-1&0&0&0&-1\\
0&1&0&1&0
\end{pmatrix},\\
O(t)=D^\dagger U(t)D=\exp(tA),\qquad
Q_s(t)=O(t)^T\Pi_sO(t),\qquad
E_s(t)=U(t)^\dagger\Pi_sU(t)=DQ_s(t)D^\dagger.
\end{gathered}
$$

$A$ 实反对称，$O(t)$ 实正交，$Q_s(t)$ 为实秩一正交投影。对复矩阵 $X$，其转置 $X^T$ 始终指这个固定实帧中的转置；$X^\dagger$ 指伴随。映射 $T^\dagger$ 则指迹配对对偶，满足 $\operatorname{tr}(ET(X))=\operatorname{tr}(T^\dagger(E)X)$。通道在此帧中写为

$$
\widehat T(X)=D^\dagger T(DXD^\dagger)D.
$$

$D$ 只作数学坐标识别，未成为未来菜单的一项控制。

既有精确效果张成是 $D\operatorname{Sym}_5(\mathbb R)D^\dagger$，实维数十五。其非负等待右导数证书的累积秩为 $5,9,12,14,15$，指定十五列行列式为 $-72$；右导数用于证明张成，不是额外可执行效果。精确保留全部输入的全部实际历史，因而保持全部实对称期望。对实单位 $v$，输入与期望测试取 $vv^T$，输出正性和迹一使 $\widehat T(vv^T)=vv^T$。在任意 Kraus 表示中，各 Kraus 算子于是将每个实 $v$ 送到它自己的直线；取标准基及两两之和使每个算子为标量恒等，故 $T=\mathrm{id}_5$。端口复合的各 Kraus 秩不超过 $q$，非零标量恒等的秩为五，给既有精确成本 $q\ge5$。

对角菜单的五维张成与精确 $q=1$、另加独立相位菜单的二十五维张成与精确 $q=5$，属于 AURIC 第 79.4 条的其他菜单。以下近似量度始终使用定义 1.2，不以这些比较菜单替换它，也不将十五个预测坐标认作物理端口维数。

## 2. 秩一首读与全部有限历史的相同量度

**定理 2.1（一次初态比较的首读恒等式）。** 在假设 1.1、定义 1.2 下，对任意两个复密度算子 $\varrho,\sigma$，

$$
\sup_\pi\operatorname{TV}(P_\varrho^\pi,P_\sigma^\pi)
=\sup_{t\ge0}\frac12\sum_{s\in\mathsf S}
\left|\operatorname{tr}\bigl(E_s(t)(\varrho-\sigma)\bigr)\right|.
\tag{2.1}
$$

因此，对任意固定 CPTP 通道 $T$，

$$
\begin{aligned}
e(T)
&=\sup_{\substack{\varrho\in\mathcal D(\mathcal H)\\t\ge0}}\frac12\sum_s
\left|\operatorname{tr}\bigl(E_s(t)(\varrho-T(\varrho))\bigr)\right|\\
&=\sup_{t\ge0}\max_{J\subseteq\mathsf S}
\left\|E_J(t)-T^\dagger(E_J(t))\right\|_{\mathrm{op}},
\qquad E_J(t)=\sum_{s\in J}E_s(t).
\end{aligned}
\tag{2.2}
$$

每个有限等待、一次完整模式读和 Stop 已实现右侧对应的分布比较。增加有限自适应深度不增加这个一次初态替换的误差要求。

证明。先固定确定策略与初始控制状态。首读之前没有输入相关结果；等待沿这个共同前缀确定，并因使用同一生成元而合成一个 $U(t)$，$t\ge0$。若在首读前 Stop，记录分布与输入无关，两次比较的 TV 为零。

否则首读的结果概率为

$$
p_s=\operatorname{tr}(E_s(t)\varrho),\qquad
p'_s=\operatorname{tr}(E_s(t)\sigma).
$$

秩一性给未归一化输出

$$
\Pi_sU(t)\varrho U(t)^\dagger\Pi_s=p_s\Pi_s,
\qquad
\Pi_sU(t)\sigma U(t)^\dagger\Pi_s=p'_s\Pi_s.
$$

从状态 $\Pi_s$ 及这个结果后的共同控制资料运行同一有限策略，定义其后缀概率核 $L_s$。这个核不依赖原输入，包含后续所有等待、读、记录更新与 Stop；有限深度保证其总质量为一。它也定义在原输入下零概率的分支上，那里只乘零，不需要作条件概率除法。

若完整历史保留首结果，则每个历史块 $(s,h)$ 的概率分别为 $p_sL_s(h)$、$p'_sL_s(h)$，故

$$
\frac12\sum_{s,h}|p_s-p'_s|L_s(h)
=\frac12\sum_s|p_s-p'_s|.
$$

若实际记录再遗忘或合并结果，它是这个分布的共同随机后处理。由三角不等式及 $\sum_hL_s(h)=1$，后处理只能减小 TV。这也覆盖有限控制状态中不再保留首结果的选择器：用于计算概率的后缀仍可按首结果分块，最终记录是这些块的共同像。

允许输入无关随机控制时，可先固定其独立随机资源，应用上述结论，再按相同混合律积分。无读分支给零差异，其余分支的 TV 不超过右侧的时间上确界；即使记录了随机控制，积分上界仍成立。反向取确定协议“等待 $t$、完整模式读、保留结果、Stop”，便得到该时间的五结果 TV，证明式 (2.1)。

两概率向量之差总和为零，其 TV 等于 $\max_J|\sum_{s\in J}(p_s-p'_s)|$。代入 $\sigma=T(\varrho)$，并使用 Hermitian 算子 $H$ 的

$$
\sup_{\varrho\in\mathcal D(\mathcal H)}
|\operatorname{tr}(H\varrho)|=\|H\|_{\mathrm{op}},
$$

即得式 (2.2)；等号由绝对特征值最大的纯特征态取得。这里只使用一次实际完整读的结果事件 $E_J(t)$。

这个量度并不等于全态迹距离。例如在 $D$ 帧中取

$$
\psi_\pm=(e_N\pm i e_2)/\sqrt2,\qquad
\varrho_\pm=D\psi_\pm\psi_\pm^\dagger D^\dagger.
$$

二者正交，迹距离为一；帧中密度差为纯虚反对称矩阵，与每个实对称 $Q_s(t)$ 的迹配对为零。由式 (2.1)，它们在全部实际有限历史下的 TV 上确界为零。因此效果张成的线性等式不能被用作近似量度的等式，更强的迹距离或联合参考量度的 minimax 常数也不能据此移入 $\varepsilon_q$。$\square$

## 3. 具有有限 flag 的共同上界通道

**定理 3.1（实投影端口及其达到的菜单误差）。** 对每个 $q\in\{1,2,3,4,5\}$，存在定义 1.3 中的固定编解码器，$q<5$ 时可取 $|F|\le120$，使其帧中复合通道为

$$
\widehat T_q(X)=\alpha_qX+\beta_qX^T+
\beta_q\operatorname{tr}(X)I_5,
\qquad
\alpha_q=\frac{6q-2}{28},\quad
\beta_q=\frac{5-q}{28}.
\tag{3.1}
$$

它遍历全部复密度输入及全部实际有限协议的最坏误差恰为

$$
e(T_q)=\frac{5-q}{7}.
\tag{3.2}
$$

$q=5$ 时取单一 flag 与恒等编解码。式 (3.2) 是这个通道达到的误差，不断言它在实际菜单中最优。

证明。在 $D$ 帧中，令 $P$ 为实秩 $q$ 正交投影，按正交共轭的不变概率分布取平均，先定义数学映射

$$
\Theta_q(X)=\frac5q\mathbb E[PXP].
\tag{3.3}
$$

每个夹乘在任意参考扩张上完全正，平均亦完全正。正交不变性与 $\operatorname{tr}P=q$ 给 $\mathbb E P=(q/5)I_5$；因 $P^2=P$，式 (3.3) 保迹。随后将这个平均精确换成有限个固定分支，不把连续随机标签作为端口。

其第二矩可直接求得。坐标独立符号翻转消去每个有奇数次指标出现的项；坐标置换使剩余项只由

$$
u=\mathbb E[P_{ii}^2],\qquad
a=\mathbb E[P_{ii}P_{jj}],\qquad
b=\mathbb E[P_{ij}^2]\quad(i\ne j)
$$

决定。在 $i,j$ 坐标平面作 $45$ 度正交旋转，新的对角元为 $(P_{ii}+P_{jj}+2P_{ij})/2$；交叉奇项消去，得 $u=(2u+2a+4b)/4$，即 $u=a+2b$。因此完整张量为

$$
\mathbb E[P_{ij}P_{kl}]
=a\delta_{ij}\delta_{kl}
+b(\delta_{ik}\delta_{jl}+\delta_{il}\delta_{jk}).
$$

对 $(\operatorname{tr}P)^2=q^2$ 与 $\operatorname{tr}(P^2)=q$ 分别缩并，得

$$
25a+10b=q^2,\qquad5a+30b=q,
\qquad
a=\frac{q(6q-2)}{140},\quad
b=\frac{q(5-q)}{140}.
$$

逐项缩并 $PXP$ 给式 (3.1)。其对任意复 $X$ 成立；这里的转置项只是一个完全正组合的表达式，未把转置本身称为物理通道。

为得到有限分支，把实对称 $P$ 视为十五维实向量空间 $\operatorname{Sym}_5(\mathbb R)$ 中的向量。矩阵

$$
Z(P)=\frac{|\operatorname{vec}P\rangle
\langle\operatorname{vec}P|}{q}
$$

是该十五维空间上的实对称迹一矩阵，位于仿射维数至多 $15\cdot16/2-1=119$ 的空间。所有秩 $q$ 正交投影构成紧集，故这些 $Z(P)$ 也构成紧集。有限维 Carathéodory 定理使其凸包中每一点可由至多 120 项表示；由紧集的 120 重积及紧单纯形的连续像，该凸包紧而闭。平均 $\mathbb E Z(P)$ 属于这个凸包，因为有限和逼近其积分。因此有固定投影 $P_f$ 与权重 $w_f\ge0$，$\sum_fw_f=1$，$|F|\le120$，满足

$$
\sum_fw_fZ(P_f)=\mathbb E Z(P).
\tag{3.4}
$$

这一步复用有限维凸表示定理，而不是给未知输入无限精度经典描述。向量化的外积是夹乘映射的 Choi 矩阵，式 (3.4) 给第二矩及通道完全相同；缩并指标并用 $P_f^2=P_f$，还给

$$
\sum_fw_fP_f=\frac q5I_5.
$$

选实列的等距映射 $V_f:\mathbb C^q\to\mathbb C^5$，$V_fV_f^\dagger=P_f$、$V_f^\dagger V_f=I_q$。在原坐标中定义

$$
\begin{aligned}
B_f&=\sqrt{5w_f/q}\,V_f^\dagger D^\dagger,\qquad R_f=DV_f,\\
\operatorname{Enc}_f(X)&=B_fXB_f^\dagger,\qquad
\operatorname{Dec}_f(Y)=R_fYR_f^\dagger.
\end{aligned}
\tag{3.5}
$$

有 $\sum_fB_f^\dagger B_f=I_5$，总编码 CPTP；$R_f^\dagger R_f=I_q$ 使每个解码器在整个 $M_q$ 上 CPTP。其复合为 $T_q(X)=D\Theta_q(D^\dagger XD)D^\dagger$，全部量子信息通过 $q$ 维块；没有保留原输入或额外量子通路。投影、权重与这些矩阵均在输入及未来协议之前固定。它们属于所声明的任意 CPTP 存储合同，未把正交共轭或 $D$ 加入后续行走菜单。

每个实际 $Q_s(t)$ 实对称且迹一，故对任意复密度 $X$，$\operatorname{tr}(Q_s(t)X^T)=\operatorname{tr}(Q_s(t)X)$。若原首读分布为 $p$，经通道后为

$$
p'_s=\lambda_qp_s+\beta_q,\qquad
\lambda_q=\alpha_q+\beta_q=\frac{5q+3}{28},\qquad
\beta_q=\frac{1-\lambda_q}{5}.
$$

令 $u_5=(1/5,\ldots,1/5)$，则

$$
\operatorname{TV}(p,p')=(1-\lambda_q)
\operatorname{TV}(p,u_5)
\le(1-\lambda_q)\frac45=\frac{5-q}{7}.
$$

任意概率向量是五个点质量的凸组合，TV 凸性及每个点质量距 $u_5$ 为 $4/5$ 给所用不等式。取 $t=0$、输入 $\Pi_s$，原分布就是点质量，达到等号。定理 2.1 将同一上界扩到所有有限深度。$q=5$ 时式 (3.1) 为恒等，单一 flag 即可。$\square$

## 4. 同一等待轨道的加权观察谱

**定理 4.1（实际模式的加权平均谱）。** 在约定 1.4 的实帧中，取按 $(N,2,3,5,25)$ 排列的权重

$$
(w_s)=(0,1/5,0,1/5,3/5),\qquad a_s=5w_s.
$$

在复矩阵空间上使用 Hilbert–Schmidt 内积 $\langle X,Y\rangle_{\mathrm{HS}}=\operatorname{tr}(X^\dagger Y)$。以下 Cesàro 极限存在：

$$
\mathcal M(X)=\lim_{L\to\infty}\frac1L
\int_0^L\sum_sa_s\operatorname{tr}(Q_s(t)X)Q_s(t)\,dt.
\tag{4.1}
$$

它正、自伴随且 $\mathcal M(I_5)=I_5$；在 $I_5$ 的 Hilbert–Schmidt 正交补上的最大特征值为 $33/68$。因而对任意复矩阵 $C$，

$$
\langle C,\mathcal M(C)\rangle_{\mathrm{HS}}
\le\frac{33}{68}\|C\|_{\mathrm{HS}}^2
+\frac{35}{68}\frac{|\operatorname{tr}C|^2}{5}.
\tag{4.2}
$$

式 (4.1) 是同一实际等待轨道的数学平均，不是一个无限协议或额外相位控制。

证明。只为计算而将坐标分成 $(N,25)$ 与 $(2,3,5)$，得

$$
A=\begin{pmatrix}0&B\\-B^T&0\end{pmatrix},\qquad
B=\begin{pmatrix}1&1&1\\1&0&1\end{pmatrix},\qquad
BB^T=\begin{pmatrix}3&2\\2&2\end{pmatrix}.
$$

置 $r=\sqrt{17}$，$\omega_\pm^2=(5\pm r)/2$。若 $u_\pm$ 是 $BB^T$ 的单位正交特征向量，则 $v_\pm=B^Tu_\pm/\omega_\pm$ 是对应单位右奇异向量。于是有两条正交实旋转平面 $L_\pm=\operatorname{span}\{u_\pm,v_\pm\}$，频率分别为 $\omega_\pm$，以及固定暗线

$$
L_0=\mathbb R z,\qquad z=(e_2-e_5)/\sqrt2.
$$

记这些子空间的正交投影为 $R_0,R_+,R_-$，秩依次为 $1,2,2$。因为

$$
\frac{\omega_+^2}{\omega_-^2}=\frac{21+5\sqrt{17}}4
$$

无理，$\omega_+/\omega_-$ 也无理。对任何非零整数对 $(m,n)$，$c=m\omega_++n\omega_-\ne0$，而

$$
\frac1L\int_0^Le^{ict}\,dt=\frac{e^{icL}-1}{icL}\longrightarrow0.
$$

式 (4.1) 的每个矩阵项是两个旋转角的有限 Fourier 多项式，因此其非负时间 Cesàro 平均恰为两个角各自均匀积分的平均。该等式只求原轨道上的极限，未授予独立选择两角的操作。

设 $r_{sj}=\|R_je_s\|^2$。左部的谱投影为

$$
G_+=\frac{BB^T-\omega_-^2I_2}{r},\qquad G_-=I_2-G_+;
$$

右部的两个平面投影分别为 $B^TG_\pm B/\omega_\pm^2$，剩余投影为 $zz^T$。将 $B$ 的三列 $(1,1)^T,(1,0)^T,(1,1)^T$ 代入，即得完整平方长度表：

$$
\begin{array}{c|ccc}
s&r_{s0}&r_{s+}&r_{s-}\\\hline
N&0&(1+1/r)/2&(1-1/r)/2\\
2&1/2&(1+3/r)/4&(1-3/r)/4\\
3&0&(1-3/r)/2&(1+3/r)/2\\
5&1/2&(1+3/r)/4&(1-3/r)/4\\
25&0&(1-1/r)/2&(1+1/r)/2
\end{array}
\tag{4.3}
$$

按所选 $a_s=(0,1,0,1,3)$ 求和，得到

$$
\sum_sa_sr_{s0}=1,\qquad
\sum_sa_sr_{s+}=\sum_sa_sr_{s-}=2.
\tag{4.4}
$$

旋转平均后每个平面分量为 $r_{s\pm}R_\pm/2$，暗线分量为 $r_{s0}R_0$。所以 $\sum_sa_s\overline{Q_s}=I_5$，即 $\mathcal M(I_5)=I_5$；等价地，该加权纯输入族的平均态为 $I_5/5$。

二阶长度和记为 $S_{ij}=\sum_sa_sr_{si}r_{sj}$。表 (4.3) 给

$$
\begin{gathered}
S_{00}=\frac12,\quad
S_{0+}=\frac{1+3/r}{4},\quad S_{0-}=\frac{1-3/r}{4},\\
S_{++}=\frac{67}{68}-\frac{3}{4r},\quad
S_{--}=\frac{67}{68}+\frac{3}{4r},\quad
S_{+-}=\frac{13}{17}.
\end{gathered}
\tag{4.5}
$$

例如

$$
\begin{aligned}
S_{++}
&=2\left(\frac{r+3}{4r}\right)^2
+3\left(\frac{r-1}{2r}\right)^2
=\frac{7r^2-6r+15}{8r^2}
=\frac{67}{68}-\frac{3}{4r},\\
S_{+-}
&=2\frac{r^2-9}{16r^2}+3\frac{r^2-1}{4r^2}
=\frac{13}{17}.
\end{aligned}
$$

正性及自伴随性来自每个积分项是带非负权的 Hilbert–Schmidt 秩一算子。以下给出整个谱，包含任意复 Kraus 矩阵会用到的全部方向。

在实对称矩阵空间的旋转不变部分，取正交单位基

$$
H_0=R_0,\qquad H_+=R_+/\sqrt2,\qquad H_-=R_-/\sqrt2.
$$

$Q_s$ 的零频率坐标为 $(r_{s0},r_{s+}/\sqrt2,r_{s-}/\sqrt2)$，故此三维块的矩阵为

$$
M_0=\begin{pmatrix}
1/2&(1+3/r)/(4\sqrt2)&(1-3/r)/(4\sqrt2)\\
(1+3/r)/(4\sqrt2)&67/136-3/(8r)&13/34\\
(1-3/r)/(4\sqrt2)&13/34&67/136+3/(8r)
\end{pmatrix}.
$$

单位恒等方向的坐标为 $(1,\sqrt2,\sqrt2)/\sqrt5$，特征值为一。其正交补取

$$
u=(0,1,-1)/\sqrt2,\qquad
v=(-2,1/\sqrt2,1/\sqrt2)/\sqrt5.
$$

由上述矩阵乘法，该补空间块为

$$
\begin{pmatrix}
15/136&-15/(8\sqrt{85})\\
-15/(8\sqrt{85})&3/8
\end{pmatrix}.
\tag{4.6}
$$

其迹为 $33/68$，行列式为

$$
\frac{45}{1088}-\frac{225}{64\cdot85}=0,
$$

所以另外两个特征值为零及 $33/68$。

其他实对称方向分成六个二维旋转子空间：暗线与两平面的交叉项，两个平面内的无迹对称项，以及两平面的角和、角差交叉项。频率分别为

$$
\omega_+,\ \omega_-,\ 2\omega_+,\ 2\omega_-,\
\omega_++\omega_-,\ \omega_+-\omega_-.
$$

它们的整数频率对彼此不同，也不互为相反数；无理频率比使不同块的交叉平均为零。可直接从平方长度求各块的平均外积：在二维旋转空间中，一个旋转向量的外积平均为其平方长度的一半乘单位。

具体地，将 $O(t)^Te_s$ 在三个子空间上的分量写作 $x_0,x_+,x_-$。暗线与某平面的对称交叉矩阵 $x_0x_\pm^T+x_\pm x_0^T$ 的平方 Hilbert–Schmidt 范数为 $2r_{s0}r_{s\pm}$；对应平均特征值为 $S_{0\pm}$。平面内 $x_\pm x_\pm^T$ 减去 $(r_{s\pm}/2)R_\pm$ 后的平方范数为 $r_{s\pm}^2/2$，故平均特征值为 $S_{\pm\pm}/4$。

两平面的对称交叉块平方范数为 $2r_{s+}r_{s-}$。取两平面单位基 $u_+,v_+$ 与 $u_-,v_-$，令 $F(a,b)=(ab^T+ba^T)/\sqrt2$。以下两对分别张成角差与角和空间：

$$
\begin{gathered}
\frac{F(u_+,u_-)+F(v_+,v_-)}{\sqrt2},\qquad
\frac{F(v_+,u_-)-F(u_+,v_-)}{\sqrt2},\\
\frac{F(u_+,u_-)-F(v_+,v_-)}{\sqrt2},\qquad
\frac{F(v_+,u_-)+F(u_+,v_-)}{\sqrt2}.
\end{gathered}
$$

若两平面分量的极角为 $\theta_+,\theta_-$，它们在这两对上的坐标长度均为 $\sqrt{r_{s+}r_{s-}}$，角分别为 $\theta_+-\theta_-$ 和 $\theta_++\theta_-$。因此两个二维块的平均特征值均为 $S_{+-}/2$。这也验证了交叉范数的等分，无须对起始向量额外假设。

由式 (4.5)，六块的特征值依次为

$$
\frac{1+3/r}{4},\quad\frac{1-3/r}{4},\quad
\frac{67}{272}-\frac{3}{16r},\quad
\frac{67}{272}+\frac{3}{16r},\quad
\frac{13}{34},\quad\frac{13}{34},
\tag{4.7}
$$

各有重数二。三维不变块加这十二维穷尽实对称空间。对复转置反对称矩阵 $X^T=-X$，$\operatorname{tr}(Q_s(t)X)=0$，所以其十维复子空间上 $\mathcal M=0$。将实对称空间复化不改变以上谱；两部分正交并穷尽二十五维复矩阵空间。

式 (4.7) 中最大的暗线交叉值不超过 $33/68$，等价于 $16r\ge51$，由 $256\cdot17>51^2$ 得到。较大的平面内值小于 $67/272+3/64<33/68$，因为 $r>4$；$13/34<33/68$。故恒等方向之外最大特征值确为 $33/68$。

最后写 $C=(\operatorname{tr}C/5)I_5+C_0$，$\operatorname{tr}C_0=0$。恒等方向的平方范数为 $|\operatorname{tr}C|^2/5$，且 $\mathcal M$ 在两正交部分间没有交叉项。对 $C_0$ 用上述谱界即得式 (4.2)，包含任意复 $C$，未假设它实、Hermitian 或可逆。$\square$

## 5. 全输入、全有限 flag 的量子端口误差界

**定理 5.1（实际菜单的统一误差区间）。** 在假设 1.1 及定义 1.2–1.3 的全部合同下，对 $q\in\{1,2,3,4,5\}$，

$$
\boxed{\frac{7(5-q)}{68}\le\varepsilon_q\le\frac{5-q}{7}}.
\tag{5.1}
$$

$\varepsilon_5=0$；$q<5$ 时不论免费有限 flag 数目多大，误差均有严格正下界。对任意 $T\in\mathfrak C_q$ 及任意 $\delta>0$，存在有限 $t\ge0$、$s\in\{2,5,25\}$ 及合法纯输入 $E_s(t)$，使确定协议“等待 $t$、完整模式读、Stop”的 TV 大于 $7(5-q)/68-\delta$。上界由定理 3.1 的一个共同有限 flag 通道达到，其误差恰为上界。

复用有限 flag 的 Kraus/Choi 约化，定义 $\varepsilon_q$ 的下确界实际上由某个通道取得，且取得者可用至多 $625$ 个 flag 表示；这个存在性并不判定它的精确误差值。

证明。先明确使用的端口类。有限维 CPTP 映射具有有限矩形 Kraus 表示；写编码算子为 $B_{f,a}:\mathbb C^5\to\mathbb C^q$，块解码算子为 $R_{f,b}:\mathbb C^q\to\mathbb C^5$。则复合有有限 Kraus 族

$$
C_{f,b,a}=R_{f,b}B_{f,a},\qquad
\operatorname{rank}C_{f,b,a}\le q,\qquad
\sum_{f,b,a}C_{f,b,a}^\dagger C_{f,b,a}=I_5.
\tag{5.2}
$$

这个秩限制不假设 flag 与输入独立；只要求量子信息确实经过所声明的 $q$ 维块。

反向，若 $T(X)=\sum_iC_iXC_i^\dagger$、$\operatorname{rank}C_i\le q$ 且 $\sum_iC_i^\dagger C_i=I_5$，选等距 $V_i:\mathbb C^q\to\mathbb C^5$，其像含 $\operatorname{ran}C_i$，不足 $q$ 时以正交向量补齐。令编码分支算子 $B_i=V_i^\dagger C_i$，解码为 $Y\mapsto V_iYV_i^\dagger$。有 $V_iB_i=C_i$ 及 $\sum_iB_i^\dagger B_i=I_5$，每个整个块的解码 CPTP。这说明 $\mathfrak C_q$ 恰为存在秩不超过 $q$ 的有限 Kraus 分解的通道类。

该对应是测量相对压缩的既有工具：参见 Bluhm–Rauber–Wolf，[*Quantum Compression Relative to a Set of Measurements*, arXiv:1708.04898v4，定义 4.1、引理 5.2–5.3](https://arxiv.org/html/1708.04898v4)。其共同 CPTP 编解码、全部密度输入与 $M_q\otimes\mathbb C^{|F|}$ 资源对应这里的整个块解码；不是随未来测量设置改换解码器的模拟问题。以下定量下界另外使用本菜单的定理 4.1，而不是文献中的未指定正稳定常数。

将式 (5.2) 的 Kraus 算子共轭到 $D$ 帧，仍记为 $C_i$。保迹给

$$
\sum_i\|C_i\|_{\mathrm{HS}}^2=5.
$$

奇异值分解及 Cauchy–Schwarz 给每个秩不超过 $q$ 的复矩阵

$$
|\operatorname{tr}C_i|
\le\|C_i\|_1\le\sqrt q\,\|C_i\|_{\mathrm{HS}},
\qquad
\sum_i|\operatorname{tr}C_i|^2\le5q.
\tag{5.3}
$$

第一不等式可由 $C_i=\sum_{k=1}^{r_i}\sigma_k u_kv_k^\dagger$ 的
$\operatorname{tr}C_i=\sum_k\sigma_k v_k^\dagger u_k$ 及 $|v_k^\dagger u_k|\le1$ 直接得到；第二不等式只对最多 $q$ 个非零奇异值求和。

对每个有限 $t$ 与模式 $s$，取帧中输入 $Q_s(t)$，物理输入为 $DQ_s(t)D^\dagger=E_s(t)$。实际等待 $t$ 后读模式，未替换输入以概率一给 $s$。替换后给该结果的概率是

$$
f_s(t)=\operatorname{tr}\bigl(Q_s(t)\widehat T(Q_s(t))\bigr)
=\sum_i|\operatorname{tr}(Q_s(t)C_i)|^2.
$$

故这个实际协议的 TV 恰为 $1-f_s(t)$，非负且不超过 $e(T)$。这些纯输入合法是因为假设 1.1 遍历全部密度态；选择输入 $E_s(t)$ 并未给策略逆等待门或读未知态的能力。

用 $w_s=a_s/5$ 求加权平均生存概率。定理 4.1 及式 (5.3) 给

$$
\begin{aligned}
S&=\lim_{L\to\infty}\frac1L\int_0^L
\sum_sw_sf_s(t)\,dt
=\frac15\sum_i\langle C_i,\mathcal M(C_i)\rangle_{\mathrm{HS}}\\
&\le\frac15\sum_i
\left[\frac{33}{68}\|C_i\|_{\mathrm{HS}}^2
+\frac{35}{68}\frac{|\operatorname{tr}C_i|^2}{5}\right]
\le\frac{33}{68}+\frac{35}{68}\frac q5.
\end{aligned}
$$

因此

$$
e(T)\ge1-S\ge\frac{35}{68}\left(1-\frac q5\right)
=\frac{7(5-q)}{68}.
\tag{5.4}
$$

这是任意合法有限 Kraus 数及任意有限 flag 数的统一界，没有实 Kraus、unital 性或协变假设。若每个有限 $t$ 及 $s\in\{2,5,25\}$ 都满足 $1-f_s(t)\le7(5-q)/68-\delta$，其每个有限时间加权平均也满足同一界，和式 (5.4) 的平均极限矛盾。所以存在陈述中的有限见证。平均仅用于证明：每项见证使用一份输入和一次预定实际实验，不需物理时间平均、概率理想读出或无限历史。

取所有 $T$ 的下确界得式 (5.1) 的下界。定理 3.1 与定理 2.1 给上界；$q=5$ 的恒等通道给零。

最后说明复用的 $625$ flag 饱和及取得性质。令

$$
\Omega=\frac1{\sqrt5}\sum_{s\in\mathsf S}e_s\otimes e_s,
\qquad J_T=(T\otimes\mathrm{id})(\Omega\Omega^\dagger)
=\frac15\sum_i|\operatorname{vec}C_i\rangle
\langle\operatorname{vec}C_i|.
$$

向量化的 Schmidt 秩恰为矩阵秩。于是上述端口类也等价于归一化 Choi 态有 Schmidt number 不超过 $q$；其纯态分解反向向量化恢复同一 Kraus 族，保迹边缘为 $I_5/5$。这一标准对应亦见 Terhal–Horodecki，[*A Schmidt number for density matrices*, arXiv:quant-ph/9911117，定义 1及命题 1](https://arxiv.org/abs/quant-ph/9911117)，及所引 Bluhm–Rauber–Wolf 引理 5.2。

Schmidt 秩不超过 $q$ 的单位向量由 $(q+1)$ 阶子式为零定义，故其纯投影构成紧集。它们处在 $25\times25$ Hermitian 迹一矩阵的 $624$ 维实仿射空间内。Carathéodory 使每个凸组合可缩到至多 $625$ 项；该凸包紧。相交保迹边缘的闭条件，所得 Choi 集仍紧。缩项不改变 $J_T$，因而不改变整个 $T$；按前面的等距分解，每一项可对应一个完整 CPTP 解码的 flag。这就是既有 $5^4=625$ 上限在本合同下的使用。

由定理 2.1 及实际测量的迹距离收缩，对任意两个通道有

$$
|e(T)-e(T')|
\le\sup_{\varrho\in\mathcal D(\mathcal H)}
\frac12\|T(\varrho)-T'(\varrho)\|_1.
$$

测量收缩可直接从 Hermitian 差的正负部分推出：对每个效果 $Q_s$，绝对迹配对不超过其与两正部分之和的迹配对，求和用 $\sum_sQ_s=I_5$。有限维通道系数收敛使右端一致趋零，故 $e$ 连续，在这个紧类上取得最小值。这是复用的有限支持与紧性论证；严格定量间隙来自式 (5.4)，并非由紧性单独给出。$\square$

**约定 5.2（端口选择与未决精确值）。** 定理 5.1 的五个区间为

| 端口 $q$ | 必要误差下界 | 所构造共同通道的误差 |
| --- | --- | --- |
| $1$ | $7/17$ | $4/7$ |
| $2$ | $21/68$ | $3/7$ |
| $3$ | $7/34$ | $2/7$ |
| $4$ | $7/68$ | $1/7$ |
| $5$ | $0$ | $0$ |

若要求误差至多 $\eta$，当 $\eta<7(5-q)/68$ 时端口 $q$ 不可能；当 $\eta\ge(5-q)/7$ 时这个端口有上述充分构造。特别地，$\eta<7/68$ 迫使 $q=5$，而 $q=5$ 精确可行。下界端点相等不由严格不可能条件排除。$q=1,2,3,4$ 的精确 $\varepsilon_q$ 及最优通道仍为未决问题；有限支持取得并未使两端常数相同，也没有证明正交平均通道对这个较小的一参数实际菜单最优。

连续数学等待与所有有限深度是这里的信息比较量词。有限个 flag 及固定 CPTP 矩阵不自动给出有限位系数、等待时钟、自治控制器、编解码合成、制备取得、存储寿命或物理时间的成本。若对这些资源另计费，须另给表示及取得合同；它们未进入本卷的 $q$ 准则。原生树的制备与量子载体之间的桥梁、空间与运输解释也未由这一端口比较供应。线性预测坐标、实际效果集合、生成代数、物理量子端口和取得成本仍是不同对象。

## 追加锚（本行以下为增补区）

## 6. A fixed nonlinear boundary on an independently prepared source

**Definition 6.1 (fixed frame, lawful source and task).** In this section
and §§7–11, fix $H=\mathbb C^5$ with real orthonormal frame
$e_1,\ldots,e_5$, Euclidean metric and orientation
$e_1\wedge\cdots\wedge e_5$. Put $J_{ij}=E_{ij}-E_{ji}$. The source domain is

$$
\mathcal L=\{(S,A):S^T=S,\ \operatorname{tr}S=1,\ A^T=-A,
\quad S,A\in M_5(\mathbb R),\quad S+iA\succeq0\}.
\tag{6.1}
$$

A comparison with common $S$ ranges over every $A,B$ allowed by (6.1),
including singular states. Its target is
$\mathcal G(S,A)=(S,\{A,-A\})$. Thus the only identification is complex
conjugation in this frame; neither orthogonal conjugacy nor equality of
spectra is an identification. The two-form convention is
$a_A=\sum_{i<j}A_{ij}e_i\wedge e_j$. In particular,
$a_A(u,v)=u^TAv$ after metric identification, and
$\iota_u a_A=-(Au)^\flat$.

Use precisely the quadratic map of
[AURIC–Langlands, Definition 6.1 and §15](AURIC_LANGLANDS_STRUCTURE_ACQUISITION_AND_SPECTRAL_EXTENSION_THEORY.md):

$$
\begin{aligned}
q(A)&=\left(-\tfrac12\operatorname{tr}(A^2),
 -A^2+\tfrac15\operatorname{tr}(A^2)I,
 *_5(a_A\wedge a_A)\right),\\
K(A)&=-A^2,\qquad b(A)=*_5(a_A\wedge a_A).
\end{aligned}
\tag{6.2}
$$

Writing $q=(\sigma,\gamma,b)$ gives
$K=\gamma+(2\sigma/5)I$, $\sigma=\operatorname{tr}K/2$ and
$\gamma=K-(\operatorname{tr}K/5)I$. Consequently $(K,b)$ is an invertible
linear recoding of the published boundary. All normalizations and Hodge
orientations in what follows refer to (6.2).

**Assumption 6.2 (alternative preparation and control interfaces).** One
stationary preparation service, with fixed preparation binding $\xi$,
supplies a fresh specimen in the same unknown state $\rho=S+iA$ on each
request. Conditional on this fixed source parameter, every finite list of
requests has product state $\rho^{\otimes n}$. Separate instrument calls
act on the requested specimens with separately initialized environments.
There is no common hidden random choice replacing this product-channel
requirement. The public frame, calibration and initial classical controller
state are independent of the unknown source.

The directional interface supplies the instruments of Definition 8.1;
the depth interface instead supplies the single instrument of Theorem 9.1.
Each also supplies the specific single-copy and joint binary instruments
of Definition 10.1, finite scheduling, preparation/setting bindings, and
writable, subsequently readable classical records. These are explicit
additional capabilities. A request returns an actual specimen or an
actual outcome, never an exact probability. Environments discarded by a
call are inaccessible. No nonreal reference, source-dependent selector,
cloning operation or hidden Kraus label is supplied.

These assumptions define alternatives to the wait/read/Stop menu in
Definition 1.2. They do not implement new operations in that old menu or
alter its initialization. Likewise they supply no interpretation of these
controls as native $\alpha/\beta$ constructors.

**Definition 6.3 (distinct observations).** The mode relation
$\mathcal G$ exposes symmetric correlations and the imaginary coupling
two-form up to simultaneous sign. The boundary observation is the
probability law of a specified detector and its visible flags. Ordered
response observations expose these laws after actual specified control
words. In the depth interface those words contain zero, one or two
successful applications of the same filter. The retained observation of a
finite run is its actually written setting/outcome word, together with its
source binding and readable backing. Its empirical frequencies are an
extraction from that word. These definitions do not identify the word with
its law, or the mode carrier with physical space, or operation count with
physical duration.

The results below concern this fixed boundary's closure and recovery of
$\mathcal G$. AURIC–Langlands Theorem 4.2 already classifies complete real
two-copy statistics by $\mathcal G$; Proposition 6.3 already supplies full
quadratic-tensor recovery when all its effects are callable. Its §15
already supplies a strictly lawful collision for $q$. Theorems 7.1, 8.2
and 9.1 concern the additional filtering relations for this restricted
boundary, rather than new proofs of those supplier results.

## 7. Exactly which invertible real filters preserve the boundary

**Theorem 7.1 (universal single-Kraus closure).** Let $F\in M_5(\mathbb R)$
be invertible with $F^TF\preceq I$. Complete its success branch by the real
binary instrument

$$
\rho\longmapsto F\rho F^T\quad\hbox{or}\quad L\rho L^T,
\qquad L=(I-F^TF)^{1/2}.
\tag{7.1}
$$

For every lawful input the success probability is
$p=\operatorname{tr}(FSF^T)>0$, with normalized successor

$$
S_F=FSF^T/p,\qquad A_F=FAF^T/p.
\tag{7.2}
$$

The following universal property holds if and only if $F^TF=cI$ for some
$0<c\le1$: for every $(S,A),(S,B)\in\mathcal L$ with $q(A)=q(B)$,
the success probabilities and compressed successors
$(S_F,q(A_F))$, $(S_F,q(B_F))$ agree. In the conformal case the complete
binary instrument also closes on $(S,q(A))$, with zero-probability
branches retained as impossible branches and no normalized successor
assigned to them. If $F$ is nonconformal, failure of success-branch
closure has witnesses with the common $S=I/5$ and strictly positive
source states.

Proof. The real Kraus operators in (7.1) have adjoint-square sum $I$.
Real symmetric matrices pair to zero in trace with real skew matrices,
so branch probabilities depend on $S$. Invertibility gives
$p\ge\lambda_{\min}(F^TF)>0$.

If $F^TF=cI$, write $F=\sqrt c\,O$, $O\in O(5)$. Then $p=c$ and
$(S_F,A_F)=(OSO^T,OAO^T)$. In the original frame,

$$
K(OAO^T)=OK(A)O^T,\qquad
b(OAO^T)=\det(O)\,O b(A).
\tag{7.3}
$$

The second formula includes reflections: the Hodge star changes with
orientation. Both formulas follow directly from the matrix and exterior
operations in (6.2). They preserve equality of boundary values without
identifying states under $O$. The other Kraus operator is
$\sqrt{1-c}\,I$. Its positive-probability successor equals the input;
when $c=1$ it is the zero branch.

For necessity take a real singular-value decomposition
$F=U\operatorname{diag}(f_1,\ldots,f_5)V^T$ and put $h_i=f_i^2>0$.
Choose any four right-singular directions and number them first. On their
coordinate four-plane put

$$
C_1=J_{12}+J_{34},\quad C_2=J_{13}-J_{24},\quad
C_3=J_{14}+J_{23}.
\tag{7.4}
$$

All three squares are $-P$, where $P$ projects onto this plane, and all
three two-form squares are $2e_{1234}$. For $0<\lambda<1/5$, the matrices
$A_r=\lambda VC_rV^T$ therefore have equal $q$ and give lawful strictly
positive states $I/5+iA_r$. Indeed their eigenvalues are
$1/5-\lambda,1/5-\lambda,1/5+\lambda,1/5+\lambda,1/5$.
This uses the published collision pattern as a family of actual inputs.

Their common success probability is $p=\sum_i h_i/5$, and their real
successors agree. In the left-singular frame the diagonals of
$K(FA_rF^T)/\lambda^2$ are, respectively,

$$
\begin{aligned}
&(h_1h_2,h_1h_2,h_3h_4,h_3h_4,0),\\
&(h_1h_3,h_2h_4,h_1h_3,h_2h_4,0),\\
&(h_1h_4,h_2h_3,h_2h_3,h_1h_4,0).
\end{aligned}
\tag{7.5}
$$

All off-diagonal entries vanish. Equality of the first two rows forces
$h_2=h_3$ and $h_1=h_4$. Equality with the third then forces all four
$h_i$ equal. Universal closure applies to every choice of four directions,
so all five $h_i$ must be equal. Conversely, if they are not all equal,
choose four containing unequal values; a pair among (7.4) has unequal
successor $K$, hence unequal successor $q$. Division by the common $p^2$
cannot remove this difference. This is a lawful witness, not an inference
from the dimension of the ambient tensor kernel. $\square$

The quantifier in Theorem 7.1 ranges over all common-$S$ comparisons in
(6.1). It asserts no necessity on an arbitrary smaller face at one fixed
$S$, or for singular filters or general multiple-Kraus branches.

## 8. Directional responses and the support-dependent recovery threshold

**Definition 8.1 (directional instrument and response).** Fix $0<t<1$,
$c_t=1-t^2$, and a finite catalogue $\mathcal V$ of real unit vectors.
For each $v\in\mathcal V$ supply the two visibly labelled Kraus branches

$$
D_v=I+(t-1)vv^T,\qquad L_v=\sqrt{c_t}\,vv^T.
\tag{8.1}
$$

They form a trace-preserving instrument. Its success probability and
imaginary successor are

$$
p_v=1-c_t v^TSv\ge t^2,\qquad A_v=D_vAD_v/p_v.
\tag{8.2}
$$

A failure of positive probability leaves the real pure state $vv^T$.
A zero-probability failure has no conditional state. Fix a public
orthonormal frame of $v^\perp$ for each supplied direction; it can be
chosen from projections of the fixed coordinate frame. With $P_v=I-vv^T$
let $R_v(A)$ be the symmetric operator on $v^\perp$ given by

$$
R_v(A)=\left.P_vK(D_vAD_v)P_v\right|_{v^\perp}.
\tag{8.3}
$$

It has ten entries. It is the corresponding success readout multiplied
by $p_v^2$, not the unnormalized imaginary part silently identified with
the normalized one. Define the exact response datum

$$
\mathcal D_{\mathcal V}(S,A)
=(S,K(A),b(A),(R_v(A))_{v\in\mathcal V}).
\tag{8.4}
$$

Definition 10.1 realizes these entries as expectations of actual
flagged experiments, without an exact-probability request.

**Theorem 8.2 (exact directional criterion).** Fix any real symmetric
$S\succeq0$ of trace one, let $U=\operatorname{im}S$, and $d=\dim U$.
On the entire lawful set $\{A:(S,A)\in\mathcal L\}$, (8.4) separates
$\mathcal G$ if and only if one of the following holds:

$$
\begin{array}{c|c}
d\le3&\text{no additional condition},\\
d=4& P_Uv\ne0\text{ for at least one }v\in\mathcal V,\\
d=5& \dim\operatorname{span}\mathcal V\ge2.
\end{array}
\tag{8.5}
$$

Here separation means that equal data are equivalent to $B=A$ or $B=-A$.
An inverse on the actual image is constructive in exact real arithmetic.
The fixed source-independent choice $\mathcal V=(e_1,e_2)$ works for
every lawful $S$. Within this family the minimum number of effective
directions is respectively zero, one and two in the three rows of (8.5).
Choosing the one direction for a rank-four support presupposes knowing
that support; the universal two-direction schedule makes no such choice.
When (8.5) fails, even all terminal $q$ responses after finite words in
these same directional instruments fail to separate the lawful witnesses.

Proof. First $A$ is supported on $U$. For a real $x\in\ker S$,
$x^*(S+iA)x=0$. Positivity implies $(S+iA)x=0$, for instance by its
positive square root, hence $Ax=0$. Skewness then gives
$\operatorname{im}A\subseteq U$.

Here is the spectral and Hodge calculation used in both recovery
constructions. The real symmetric matrix $K=-A^2=A^TA$ is positive
semidefinite, has kernel $\ker A$, and commutes with $A$. On a positive
$\mu$-eigenspace, $A/\sqrt\mu$ is an orthogonal skew map with square
$-I$. A unit vector and its image span an invariant orthonormal two-plane;
skewness preserves the orthogonal complement. Repeating this argument
shows that every positive eigenspace has even dimension. In dimension
five, the possibilities are rank zero, rank two, rank four with two
distinct positive eigenvalues, and rank four with one positive eigenvalue.
This is the classical skew spectral decomposition, obtained here from
the real symmetric spectral theorem.

Rank zero gives $A=0$. At rank two, $K$ fixes the only nonzero two-plane
and its magnitude, so only the common sign remains. At rank four with
distinct eigenvalues $\mu_1,\mu_2$, it fixes two orthogonal two-planes
and the two magnitudes. Choosing frames for those planes gives four sign
pairs. Their nonzero wedge square, hence $b$, fixes the product of the
two signs, leaving exactly the common sign. Those frames are calculation
choices in the same fixed coordinates, not new state equivalences.

The remaining case is

$$
K=\lambda^2P_W,\qquad \lambda>0,\quad\dim W=4.
\tag{8.6}
$$

Then $\|a_A\|^2=2\lambda^2$ and $\|b(A)\|=2\lambda^2$.
Put $n=b(A)/(2\lambda^2)$ and orient $W=n^\perp$ so that its volume
satisfies $*_5\operatorname{vol}_W=n$. The form $a_A$ is self-dual on
this oriented four-plane: if $a_A=a_++a_-$ is its Hodge decomposition,
its norm and wedge square give

$$
\|a_+\|^2+\|a_-\|^2=2\lambda^2,
\qquad \|a_+\|^2-\|a_-\|^2=2\lambda^2.
\tag{8.7}
$$

Thus $a_-=0$. This is the classical oriented orthogonal-complex-structure
fiber; see Salamon–Viaclovsky,
[*Orthogonal complex structures on domains in* $\mathbb R^4$,
§2.4, Propositions 2.1–2.2](https://arxiv.org/html/0704.3422v2).
Only this finite-dimensional algebra is used, not integrability or a
twistor-space realization theorem.

The additional response has a particularly direct interpretation. Let
$w=Av$, so $w\perp v$. Since $D_v^2=I-c_tvv^T$ and
$Avv^TA=-ww^T$,

$$
D_v^{-1}K(D_vAD_v)D_v^{-1}
=-AD_v^2A=K-c_tww^T.
\tag{8.8}
$$

Extend $R_v$ by zero on $\mathbb Rv$, denoting the extension by
$\widehat R_v$. Compression of (8.8) yields the original column relation

$$
G_v:=\frac{P_vKP_v-\widehat R_v}{c_t}=(Av)(Av)^T.
\tag{8.9}
$$

Thus ten controlled square entries suffice for a direction; the other
square entries and all controlled $b$ entries are unnecessary here.

If two candidates in (8.6) have the same $q$ and the same nonzero $G_v$,
their vectors $Av,Bv$ agree up to sign. Change the common sign of $B$
to make them agree, and put $u=P_Wv$, $w=Au=Bu\ne0$. They agree on
$L=\operatorname{span}(u,w)$ because both send $w$ to $-\lambda^2u$.
Skewness makes $M=W\cap L^\perp$ invariant for both. Their restrictions
to this remaining two-plane have magnitude $\lambda$ and only two sign
choices. Equality of the nonzero wedge square fixes that last sign, so
$A=B$ after the alignment.

This also gives an explicit inverse. Extract a nonzero $G_v=ww^T$ by
choosing its first positive diagonal entry $G_{kk}$ and taking
$w=G_ve_k/\sqrt{G_{kk}}$. Set $u=P_Wv$. On $L$ use

$$
A_L=\frac{wu^T-uw^T}{\|u\|^2}.
\tag{8.10}
$$

It sends $u$ to $w$ and $w$ to $-\lambda^2u$. On $M$ choose the
magnitude-$\lambda$ skew block whose wedge with this block gives the
known $b$. Exactly one sign works. Reversing $w$ reverses the whole
answer. In the other rank strata choose plane frames by ordered
coordinate projections and Gram–Schmidt, and use $b$ to fix the relative
sign when two planes are present. More explicitly, the two squared
magnitudes, including an omitted zero when the rank is two, are the roots
of

$$
x^2-\tfrac12\operatorname{tr}(K)x+\tfrac14\|b\|^2=0.
\tag{8.11}
$$

For distinct positive roots $\mu_i,\mu_j$, the corresponding projector
is $K(K-\mu_jI)/(\mu_i(\mu_i-\mu_j))$. At rank two it is
$K/\mu_i$; in (8.6) it is $K/\lambda^2$. Thus this reconstruction
requires only finitely many exact arithmetic operations, comparisons,
square roots and the indicated finite linear algebra. Every permitted
choice gives the same orbit.

For $d\le3$ the support bound leaves only ranks zero and two. For $d=4$
an unresolved rank-four map has $W=U$, so a direction with $P_Uv\ne0$
has $Av\ne0$. For $d=5$, the kernel in (8.6) is a line; it cannot
contain two independent directions. This proves sufficiency in (8.5).

For necessity, if $d=4$ and every direction annihilates $U$, take $W=U$.
If $d=5$ and the catalogue spans at most a line, take a four-plane
$W$ perpendicular to that span. Choose orthonormal $f_1,\ldots,f_4$ in
$W$ and write $J^f_{ij}=f_if_j^T-f_jf_i^T$. With

$$
A=\lambda(J^f_{12}+J^f_{34}),\qquad
B=\lambda(J^f_{13}-J^f_{24}),
\tag{8.12}
$$

both squares are $-\lambda^2P_W$, both wedge squares are
$2\lambda^2f_1\wedge f_2\wedge f_3\wedge f_4$, and $B\ne\pm A$.
Let $\mu>0$ be the least eigenvalue of $S|_U$ and choose
$0<\lambda<\mu$. On $U$ both states are bounded below by
$(\mu-\lambda)I$, and on $U^\perp$ they vanish. They are lawful even
on the semidefinite support face under consideration. Each catalogue
$v$ lies in $W^\perp$, so $Av=Bv=0$ and $D_vAD_v=A$, $D_vBD_v=B$.
Thus their directional data coincide.

For a word of success branches the unnormalized imaginary parts remain
$A,B$ and their real parts remain common. Normalization multiplies both
by the same scalar. A positive-probability failure makes both states the
same real state $vv^T$. Every later real branch then agrees. Branch
probabilities at each step depend only on the common real part; zero
branches occur together. Induction proves the stated all-word failure
for this restricted response family. No amount of repeating those blind
directions replaces a direction which meets $W$. $\square$

## 9. Three depths of one calibrated filter

**Theorem 9.1 (simple-spectrum depth recovery).** Supply the real binary
instrument with success Kraus operator

$$
F=\operatorname{diag}(1,2,3,4,5)/6,
\qquad L=(I-F^2)^{1/2},\qquad G=F^2.
\tag{9.1}
$$

For every lawful source, the datum

$$
\mathcal T_F(S,A)=
\bigl(S,K(A),b(A),K(FAF),K(F^2AF^2)\bigr)
\tag{9.2}
$$

determines exactly $\mathcal G(S,A)$. The assertion holds algebraically
for every real skew $A$, with no rank, purity or spectral genericity
restriction on the source. Only the supplied filter has simple spectrum.
The twenty base quadratic entries and fifteen square entries at each
later depth suffice; later $b$ entries are unnecessary. The inverse is
constructive by spectral decomposition and a homogeneous linear system
in three unknowns on the repeated rank-four stratum.

Proof. For any invertible symmetric $F$ the data in (9.2) determine

$$
\begin{aligned}
N_0&=A^2=-K(A),\\
N_1&=-F^{-1}K(FAF)F^{-1}=AGA,\\
N_2&=-F^{-2}K(F^2AF^2)F^{-2}=AG^2A.
\end{aligned}
\tag{9.3}
$$

The rank-zero, rank-two and distinct rank-four cases are already resolved
by $K,b$ in the proof of Theorem 8.2. Consider the remaining case (8.6)
for two equal-data candidates. On the same oriented $W$, write
$J=A/\lambda$, $J'=B/\lambda$. In an oriented orthonormal frame of $W$
the self-dual skew space has the basis

$$
I_1=J_{12}+J_{34},\quad I_2=J_{13}-J_{24},\quad
I_3=J_{14}+J_{23}.
\tag{9.4}
$$

Multiplying these displayed matrices gives $I_r^2=-I$ and
$I_rI_s+I_sI_r=0$ for $r\ne s$. In particular, every
$Z=\sum z_rI_r$ satisfies $Z^2=-(\sum z_r^2)I$.
Both $J,J'$ have unit coefficient vectors. If $J'\ne\pm J$, their
coefficient inner product $c$ has $|c|<1$. The orthogonal map
$C=J^{-1}J'=-JJ'$ satisfies

$$
C+C^T=2cI,\qquad C=cI+D,\qquad D^T=-D,
\quad D^2=-(1-c^2)I.
\tag{9.5}
$$

It has no real eigenvector: for $Cx=rx$ with real nonzero $x$,
the symmetric part gives $r=c$, whence $Dx=0$, contradicting (9.5).

Let $P=P_W$, $n=b/(2\lambda^2)$, and define operators on $W$ by

$$
H=PGP|_W,\qquad H_2=PG^2P|_W,\qquad v=PGn.
\tag{9.6}
$$

Equality of $N_1$ gives $JHJ=J'HJ'$, equivalently equality of
conjugation by $J$ and $J'$. Thus $C$ commutes with $H$. Equality of
$N_2$ similarly makes it commute with $H_2$. Since $I=P+nn^T$,

$$
H_2=H^2+vv^T.
\tag{9.7}
$$

If $v\ne0$, commutation with $vv^T$ preserves the real line
$\mathbb Rv$, impossible by (9.5). If $v=0$, $n$ is an eigenvector of
$G$ and $W$ is $G$-invariant. The restriction $H$ then has four distinct
real eigenvalues because the five eigenvalues of $G$ in (9.1) are
distinct. Commutation with $H$ preserves each real eigenline, again
impossible. Therefore $J'=\pm J$. This proves injectivity on every
stratum. Quadraticity gives its reverse implication.

For the inverse in the remaining stratum, compute $W,\lambda,n,H,H_2$
and $N_1,N_2$ from the data. Put $L_r=-N_r|_W/\lambda^2$ for $r=1,2$.
Solve, in the three-dimensional space (9.4),

$$
ZH=L_1Z,\qquad ZH_2=L_2Z.
\tag{9.8}
$$

The true $J$ is a solution. Every nonzero solution has
$Z^2=-r^2I$ with $r=(\sum z_i^2)^{1/2}>0$. Its normalization $J''=Z/r$
has the same square, the same Hodge chirality and the same conjugations
of $H,H_2$ as $J$. Hence $\lambda J''$ has all the original data.
The proved injectivity forces $J''=\pm J$, so the solution space of
(9.8) is precisely a line. Either normalization returns the required
orbit. Outside this stratum use the plane reconstruction in Theorem 8.2.
No choice of an unknown-state eigenvector is an experimental control.
No distinctness of pairwise products of filter eigenvalues is needed.
$\square$

**Definition 9.2 (actual depth branches).** To realize depth $j=0,1,2$,
apply (9.1) successively on a fresh specimen, stopping that specimen's
chain at its first failure. Its all-success branch has

$$
p_j=\operatorname{tr}(F^{2j}S)>0,\qquad
\rho_j=F^j\rho F^j/p_j,\qquad
A_j=F^jAF^j/p_j.
\tag{9.9}
$$

Here $p_0=1$ and $p_j\ge6^{-2j}$. Conditional on two independent
specimens both reaching this branch their state is
$\rho_j\otimes\rho_j$, and the branch probability is $p_j^2$.
Consequently

$$
p_j^2K(A_j)=K(F^jAF^j),\qquad
p_j^2b(A_j)=b(F^jAF^j).
\tag{9.10}
$$

These are homogeneity identities, not an identification of success with
certainty. Every failure prefix is retained. Its branch operator and its
probability are those of the displayed instrument; it is never replaced
by a fresh successful specimen without charging another preparation.

The directional interface resolves the remaining fiber with a nonzero
$Av$ relation. The depth interface instead resolves it through the two
compressions in (9.6) and their difference (9.7). Their controls are
independently specified: two rank-one attenuation directions versus
repeated use of a simple-spectrum filter. These are different resource
coordinates, not numerical names for space or time, and neither theorem
asserts that one interface dominates the other.

## 10. Actual joint effects, finite records and same-run charges

**Definition 10.1 (direct quadratic detectors).** Index the ten skew
coordinates by $e=(i,j)$, $i<j$, and put $Y_e=iJ_{ij}$. For each required
quadratic coordinate $f$ expand
$f(A)=\sum_{e\le h}c^f_{eh}A_eA_h$ in a fixed order. Define

$$
\begin{aligned}
H_f&=\tfrac18\sum_{e\le h}c^f_{eh}
 (Y_e\otimes Y_h+Y_h\otimes Y_e),\\
M_f&=1+\tfrac14\sum_{e\le h}|c^f_{eh}|,\qquad
E_f^\pm=\tfrac12(I_{25}\pm H_f/M_f).
\end{aligned}
\tag{10.1}
$$

These are explicit real symmetric matrices. Although a single $Y_e$ is
imaginary, each tensor product in (10.1) is real. Since $\|Y_e\|\le1$,
$\|H_f\|<M_f$, so $E_f^\pm$ are positive definite complementary effects.
Their positive real square roots give the two real Kraus operators of a
terminal instrument on the joint carrier. Its branch state before discard
is the actual normalized congruence by that square root whenever the
branch probability is positive. Both measured registers are then discarded;
only their declared classical record is retained. No five-mode coordinate
is assigned to this possibly correlated twenty-five-dimensional branch.

For any subnormalized $\tau=T+iC$ with real symmetric $T$ and real skew
$C$, direct trace multiplication, as in AURIC–Langlands Proposition 6.3,
gives

$$
\operatorname{tr}(Y_e\tau)=2C_e,\qquad
\operatorname{tr}(H_f\tau^{\otimes2})=f(C).
\tag{10.2}
$$

Thus individual imaginary observables need not be callable to implement
the real joint effects. Supplying only local real measurements would not
supply (10.1).

On a pair attempt execute each specimen's filter chain independently,
even if the other specimen fails. Record both chains. Measure (10.1)
only if both reach the required success depth; otherwise discard both
specimens after recording their prefixes. Let $Z_f=+1$ or $-1$ on the two
terminal detector outcomes and $Z_f=0$ on a failed attempt. Equations
(10.2) and the unnormalized branch state imply exactly

$$
M_f\mathbb E Z_f=f(F^jAF^j)
\tag{10.3}
$$

for the depth interface. For a directional attempt replace $F^j$ by
$D_v$. Without filtering it is $f(A)$. This extracts the unnormalized
quadratic coordinate directly from the complete flag/outcome law. It
neither divides by an empirical success frequency nor queries an exact
success probability. All zero branches remain entries of mass zero;
no conditional division is performed on them.

For $S$ use the fifteen binary single-copy settings
$P_i=e_ie_i^T$ and $P_{ij}=(e_i+e_j)(e_i+e_j)^T/2$. Their real
square-root instruments are terminal and followed by discard. Their laws
satisfy

$$
S_{ii}=p(P_i),\qquad
S_{ij}=p(P_{ij})-\tfrac12\{p(P_i)+p(P_j)\}.
\tag{10.4}
$$

These are separate settings, not simultaneous outcomes of one projective
measurement. The single-copy panel and every pair panel use the same
source binding $\xi$.

**Proposition 10.2 (complete panel laws and concrete finite schedules).**
In the directional interface take $t=1/2$ and
$\mathcal V=(e_1,e_2)$. Use all fifteen entries of $K$ and five entries
of $b$ on unfiltered pairs, and only the ten $K$ entries avoiding index
$j$ after the $e_j$ filter, for $j=1,2$. The laws of these forty pair
configurations and fifteen single-copy settings determine, and are
determined by, $\mathcal D_{\mathcal V}$. In the depth interface use the
twenty base entries and all fifteen $K$ entries at each of depths one and
two, plus the same single-copy panel. These fifty pair configurations
and fifteen single-copy settings determine, and are determined by,
$\mathcal T_F$. The two panel-law images are constructively equivalent
to $\mathcal G$ and therefore to each other on their actual images.

For a fixed positive integer $N$, execute $N$ independent attempts of
each listed configuration in a fixed public order, with no retry rule.
The following charges refer to this one actual run:

$$
\begin{array}{c|c|c}
&\text{directional schedule}&\text{depth schedule}\\ \hline
\text{source preparations}&95N&115N\\
\text{single-copy detector calls}&15N&15N\\
\text{local filter calls}&40N&60N+U_1\le90N\\
\text{joint detector calls}&20N+C_D\le40N&20N+C_T\le50N\\
\text{padded outcome-record bits}&95N&155N
\end{array}
\tag{10.5}
$$

Here $C_D$ counts actual double-success directional attempts among the
$20N$ filtered pair attempts. $C_T$ counts actual double-success-at-depth
attempts among the $30N$ nonzero-depth pair attempts. $U_1$ counts first
successes of individual specimens among the $30N$ specimens assigned to
depth two; each such success permits exactly one additional filter call.
Failures are charged and retained in every row.

Proof. Equations (10.3)–(10.4) recover the claimed tuples. Conversely,
Theorems 8.2 and 9.1 recover the original $\mathcal G$, from which the
specified real instruments compute their complete laws by trace. This
also proves the reverse law correspondence, including failure flags.
It does not require a probability oracle in the finite schedule. If
$\mathsf E_D,\mathsf E_T$ encode the orbit as the respective response
data and $\mathsf I_D,\mathsf I_T$ are the proved inverses, then

$$
\mathsf R_{D\to T}=\mathsf E_T\mathsf I_D,
\qquad \mathsf R_{T\to D}=\mathsf E_D\mathsf I_T.
\tag{10.6}
$$

Each composite returns the other datum of that same source orbit, and
reverse composites are identities on the actual images. The same holds
for the complete panel laws through the trace and expectation maps.
This is not an inverse between unrelated ensembles.

For the first column of (10.5) there are $15N$ single specimens and
$40N$ pair attempts, hence $95N$ preparations. Exactly $20N$ of those
pairs each receive two filter calls. The $20N$ unfiltered pairs always
receive a joint detector, and only double successes do so in the other
pairs. Retain one outcome bit per single or unfiltered-pair attempt and
three per filtered attempt: the two flags and a detector bit, padded
by zero when no detector occurred. The result is
$15N+20N+3(20N)=95N$ outcome bits.

For the second column there are $50N$ pairs. Depth-one pairs require
$30N$ filter calls. Depth-two pairs require $30N$ first calls and $U_1$
second calls. Each depth-two chain has the three possible prefixes
failure, success-then-failure, success-then-success; two bits encode it.
Two such prefixes and one padded detector bit cost five bits per pair.
Thus the outcome word has
$15N+20N+3(15N)+5(15N)=155N$ bits. No unattempted call is recorded as a
failure, and no unused detector bit is interpreted as an outcome.
$\square$

**Definition 10.3 (what the charges include).** The bit rows in (10.5)
count outcome payload in its fixed order. The public schedule also
requires its retained source/frame/calibration binding, the value $N$,
program and setting descriptions, counters, backing, allocation and
actual reads/writes. Distinct preparation occurrences are bound to their
positions and pair roles. These further resources are additional to
(10.5). Retaining the padded word preserves the executed order; retaining
only outcome counts loses that order.

For these coordinate choices there are twenty joint detector designs,
fifteen single-copy designs and either two directional instruments or
one calibrated filter instrument. There are respectively forty or fifty
joint measurement/control configurations. A direction, a configuration,
a detector call, a sample, a hardware generator, elementary gate count,
physical duration and energy are different cost coordinates. In
particular (10.5) is neither a hardware decomposition nor a lower bound
on samples or memory. No Pareto comparison is inferred from it.

**Proposition 10.4 (finite records do not supply the exact inverse).**
For either fixed schedule in Proposition 10.2, no decoder of its finite
record, even with additional source-independent classical randomness,
is almost surely exactly correct for every source orbit in (6.1).
The expectation identities nevertheless give unbiased finite estimates
of the listed quadratic coordinates.

Proof. For every strictly positive $\rho$, both outcomes of each
single-copy projector setting have positive probability. In the
directional schedule both filter flags have positive probability; the
success Kraus operator is invertible and the failure state is real. In
the depth schedule $F$ and $L$ are invertible, so every allowed failure
prefix and all-success prefix has positive probability. The terminal
joint effects are positive definite by (10.1). Therefore every record
allowed by either fixed padded grammar has positive probability under
every strictly positive source. For example $I/5$ and
$I/5+iJ_{12}/10$ have distinct orbits and the same possible finite
records. At any such record an exactly correct decoder would have to
return each of two different orbits with conditional probability one.
Extra source-independent randomness cannot satisfy both requirements.
This proves the statement for these schedules, without a universal
impossibility claim about other acquisition models.

For a quadratic setting the random variables $Z_f$ in its $N$ attempts
are independent, take values in $[-1,1]$, and satisfy (10.3). Thus
$M_fN^{-1}\sum Z_f$ is unbiased with variance at most $M_f^2/N$.
For single-copy probabilities the variance is at most $1/(4N)$.
These elementary sampling facts describe finite records; they do not
perform the inverse's exact rank tests, supply exact zero probabilities,
or bound the error of a numerically decoded orbit. $\square$

The exact inverses in §§8–9 act on genuine image values, with exact real
comparisons, square roots and finite linear algebra. Arbitrary exact real
values need not have finite digital descriptions. Applying those formulas
to finite estimates is a separate numerical problem: estimates can lie
off the lawful image, and the repeated-spectrum branches require their
own precision and conditioning analysis. No exact finite acquisition,
uniform numerical error guarantee or installed numerical decoder follows
from the algebraic inverses or from (10.5).

## 11. Real continuations, callable use and the preserved scope

**Definition 11.1 (declared continuation task).** Fix a known classical
controller/record state $m$. Its available menus and permissions are
supplied functions of $m$, not advice selecting an action from an
unobserved signed state. A finite real continuation uses specified
finite real-Kraus instruments, specified real ancillary states, and
policies depending only on actual acquired records and source-independent
randomness. Fresh calls to the service have the independence of
Assumption 6.2. Classical responses retain chosen controls, visible
outcomes, stopping and preparation/resource labels. For operations
confined to one retained five-mode register, its mathematical successor
coordinate is its conjugation orbit together with the actual updated $m$.
It is not the raw signed density matrix. A retained joint register can have a
larger correlated carrier; its orbit must be carried on that carrier.
All source registers and their successors use one common conjugation
choice. Taking separate sign quotients of retained registers and fresh
source copies can discard their relative distinction and is not an
allowed replacement for the joint description.

**Proposition 11.2 (same-source transport and route agreement).** Given
an exact datum $\mathcal D_{(e_1,e_2)}$ or $\mathcal T_F$ and the actual
$m$, every supplied real instrument on a retained five-mode register has
determined branch probabilities and determined same-type successor data
on every positive-probability branch. Zero branches are determined as
zero, without a normalized successor. Recovery, instrument composition,
and the conversions (10.6) commute on their actual lawful images.
The recovered source orbit also determines the complete classical laws
of every declared finite real continuation of Definition 11.1. When the
comparison experiment class includes the diagnostic panels, equality of
all its laws is equivalent to equality of either complete panel law.
The continuation-law assertion starts from the preparation service and
the declared real initialization. At an intermediate cut, joint
predictions use either the source datum and the actually retained
executed branch map, or the simultaneous-conjugation orbit of the full
current joint state and the original service parameter. A single marginal
orbit or a source label alone does not supply
correlations with other retained systems or fresh source copies.

Proof. Recover $\mathcal G$ by the appropriate inverse. For a branch
$\Phi_b(X)=\sum_rK_{br}XK_{br}^T$, write

$$
\begin{aligned}
S_b&=\sum_rK_{br}SK_{br}^T,\qquad
A_b=\sum_rK_{br}AK_{br}^T,\qquad p_b=\operatorname{tr}S_b,\\
\rho_b&=S_b/p_b+iA_b/p_b\quad(p_b>0).
\end{aligned}
\tag{11.1}
$$

All $K_{br}$ are real and their full adjoint-square sum is $I$.
Replacing $A$ by $-A$ leaves $p_b$ unchanged and reverses $A_b$ only.
Thus the successor's response datum is independent of the chosen sign.
If $p_b=0$, the positive unnormalized branch has trace zero and equals
the zero matrix; no conditional state is defined. The memory update is
the specified update of that actual visible branch and $m$.

Both routes around a recovery/update square compute (11.1) for the same
source representative and then forget exactly its common sign. Applying
two branches successively gives their actual CP composition, with the
same product of conditional probabilities. Re-encoding at an intermediate
cut therefore does not change a later result on that same register.
When combining it with other systems, the common-source joint
description specified above is used. Together with (10.6) this proves
route agreement on the declared continuation domain.

For a reached record $m$, a retained executed real branch map
$\Psi_m$ computes the current joint state from the actual requested
$\rho^{\otimes n}$ and declared real initialization, divided by that
record's positive probability. Thus one source representative fixes the
relative signs of that joint state and every fresh source copy. Its
conjugate representative conjugates them all at once. This explains the
additional cut condition without inferring a branch map from a marginal.

More generally every real branch obeys
$\Phi_b(\bar X)=\overline{\Phi_b(X)}$. Real effects have equal trace
probabilities on conjugate inputs. Independent copies and specified real
ancillas preserve simultaneous conjugation; the same holds for any
retained joint state on its full carrier. At each acquired classical
record the two comparisons select the same next policy and have the
same probabilities and conjugate positive-probability successors.
Induction over the finite continuation tree proves equality of complete
classical laws, including termination and resource labels. Conversely,
a class containing the panels contains a separating law by Proposition
10.2, so law equality forces the same source orbit. $\square$

This transport is a concrete use of the existing conjugation
classification and fiber-descent principle, not a new abstract quotient
theorem. Relevant repository suppliers include
[RealCopyConjugation](../../../D5/S3/Quantum/Fibers/RealCopyConjugation.lean)
and its [owning Scribe](../../../Blueprint/D5/S3/Quantum/Fibers/RealCopyConjugation.scribe.cs),
[DynamicsDescent](../../../D5/S0/Rewriting/Quotients/DynamicsDescent.lean),
[DynamicsResidualQuotient](../../../D5/S3/QuantumStates/DynamicsResidualQuotient.lean),
[AllFutureStatisticsSufficiency](../../../D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency.lean)
and [QuotientResidualTransport](../../../D5/S3/Quantum/Fibers/QuotientResidualTransport.lean).
Their linear/quotient conclusions do not by themselves establish (8.9)
or the simple-spectrum argument (9.5)–(9.7).

**Definition 11.3 (conditions for executed later use).** A later call
using an orbit description requires an actually acquired, source-bound
representation at its promised precision, retained readable backing,
installed decoding/arithmetic and continuation instructions, workspace,
and current authorization to execute them. The actual record $m$ is
also required; it is not recoverable from $\mathcal G$. A finite sample
word supplies its recorded outcomes, not exact law input. An exact-data
promise must state its encoding and acquisition separately. These
conditions are independent of existence of the mathematical inverse.
They retain the distinction between representation, delivery and
callability in
[Native Structural Storage Atlas, §§7 and 9](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md)
and [Native Paid View Conversion, §§1, 3 and 7](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md).
No new callable-storage theorem is asserted here.

The real-Kraus framework is the established one in Wu et al.,
[*Operational Resource Theory of Imaginarity*](https://arxiv.org/html/2007.14847v2).
The geometry in (8.6)–(8.7) is classical, as cited in the proof.
Generalized quadratic phase retrieval, including fixed-family injectivity
criteria and generic measurement theorems, is treated by Wang–Xu,
[*Generalized phase retrieval: measurement number, matrix recovery and
beyond*, Theorems 2.1 and 4.1](https://arxiv.org/html/1605.08034v3).
Known-dynamics tomography has different feasibility and almost-all-POVM
hypotheses; see Kech,
[*Dynamical Quantum Tomography*, §§III–IV](https://arxiv.org/html/1605.06786v2).
These are intermediate frameworks and comparisons, not suppliers of an
unverified assertion about this fixed $q$. The source-specific synthesis
proved here is its universal conformal-filter criterion, the all-support
directional criterion, and the three-depth recovery relation. No claim
of global literature originality is needed for these proofs.

If all complete two-copy effects of AURIC–Langlands Proposition 6.3 are
already callable, their existing full-tensor recovery remains sufficient;
one can use that result directly. The restricted-interface gain here is
that a supplied $q$-detector family, supplemented by the declared controls,
separates its lost distinctions without first granting all fifty-five
quadratic-coordinate detectors. It is not greater identification power
than full tensor data. The calibrated nonreal-reference theorem in its
§5 remains a different interface, which can remove the final conjugation
ambiguity. No such reference is generated here. Its representation
splitting and conditional Hecke naturality in §§6–7 are unchanged and
supply no experiment-to-geometric-realization functor for these controls.

The conclusions recover source laws for the declared real-operation
continuation class, not an actual realized past. Neither the directional
nor the depth result recovers finite retained memory from a probability
law, or physical space/time from the fixed mode indices and control
words. The original fixed-$G_{gc}$, original-$Q$, parked-consumer and
unchanged-initialization obligations remain in their original domains.
The original-root late-target, $M_1(D)$, sharp-$\lambda$ and all-size
acquisition/certification questions are not altered. No generation or
installation of the present preparations, filters, joint detectors or
receiver by native $\alpha/\beta$ operations has been proved. These
remaining bridges are separate from the closure and recovery theorems.

## 追加锚（本行以下为增补区）

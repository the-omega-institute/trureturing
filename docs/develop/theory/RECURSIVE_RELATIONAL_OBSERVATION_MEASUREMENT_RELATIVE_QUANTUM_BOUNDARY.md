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

## 12. Necessary acquisition budget for a supplied coherent consumer

**Definition 12.1 (original acquisition and the prediction cut).** Fix an
integer $k\ge20$, put $r=k^2$, and in the fixed real frame of Definition
6.1 set

$$
Y=iJ_{12},\qquad \rho_\theta=I_5/5+\theta Y,
\qquad \theta\in\{0,2/k\}.
\tag{12.1}
$$

One value of $\theta$ is fixed throughout the actual run. The service of
Assumption 6.2 supplies stationary independent copies of that same state,
with the same preparation binding $\xi$ for acquisition and continuation.
The public inputs $k,N$, frame, calibration, initial controller, programs,
reference and auxiliary resources, advice, permissions and binding labels
are source-independent. More precisely, their initial joint state or law
is the same under both hypotheses. For every finite list of $n$ source
requests, the initial resources and those inputs have joint state
$\omega_{\mathrm{init}}\otimes\rho_\theta^{\otimes n}$, with one
common $\omega_{\mathrm{init}}$ (including classical random resources).
Further metadata is generated only by common rules from these resources
and the recorded experiments. A binding authenticates
occurrences of this service; it supplies no information about $\theta$.
The only source-dependent resources available at the prediction cut are
the classical records specified below.

Choose either of the two schedules in Proposition 10.2 and a positive
integer $N$. Execute exactly $N$ attempts per configuration in its fixed
public order, without retries or additional source observations. Let $W$
be the complete classical record: all single-copy outcomes, both filter
chains of each pair, every failure prefix, all actual detector outcomes,
the prescribed padding, setting/order/occurrence labels and readable
source/frame/calibration backing. Both members of a pair execute their
own prescribed chain even if the other fails. Every training source
register, its successor and every source-dependent quantum environment
is discarded at the end of its attempt, including failed attempts.
No such quantum system links two attempts or survives to prediction.
No nonreal reference or hidden Kraus label is supplied, as in Assumption
6.2. The number of pair attempts is

$$
m=40N\quad\hbox{(directional)},\qquad
m=50N\quad\hbox{(depth)}.
\tag{12.2}
$$

A predictor is any common measurable randomized function of $W$ and the
public inputs, with real output $\widehat p$. Equivalently it is a
source-independent probability kernel from this record to $\mathbb R$.
Allowing arbitrary classical processing strengthens the observer for a
necessary bound; it grants neither an installed algorithm nor free
processing, storage or arithmetic. Prediction occurs before the future
source calls of Definition 12.3 and uses no additional acquisition.

**Theorem 12.2 (complete original records and pair information).** Under
Definition 12.1, let $P_\theta$ be the law of the entire retained classical
record. With $\operatorname{TV}(P,Q)=\tfrac12\sum_w|P(w)-Q(w)|$ on a
finite record alphabet, and $\operatorname{TV}(P,Q)=
\sup_B|P(B)-Q(B)|$ over measurable events for general record measures,
one has

$$
\operatorname{TV}(P_0,P_{2/k})
\le\frac12\sqrt{(1+1600/r^2)^m-1}.
\tag{12.3}
$$

Every common randomized postprocessing obeys the same bound. In
particular the bound concerns the complete flagged word, rather than
only frequencies or successful pairs.

Proof. First express each original pair attempt as a complete real
POVM on its two unfiltered inputs. At depth $j$, the possible local
prefix operators are $F^j$ for all successes and $LF^\ell$ for a first
failure after $\ell$ successes, $0\le\ell<j$. At depth zero the only
operator is $I$. Their adjoint-square sum is $I$, by successive
completeness of (9.1). For a directional chain the two operators are
$D_v,L_v$ of (8.1), with the same completeness property. Denote a local
prefix operator by $B_\alpha$ and its all-success prefix by $s$.
For configuration $c$ using detector $f$, its record effects are

$$
\begin{aligned}
Q_{c,(s,s,o)}
 &= (B_s\otimes B_s)^T E_f^o(B_s\otimes B_s),
 &&o\in\{+,-\},\\
Q_{c,(\alpha,\beta,0)}
 &=B_\alpha^TB_\alpha\otimes B_\beta^TB_\beta,
 &&(\alpha,\beta)\ne(s,s).
\end{aligned}
\tag{12.4}
$$

The last label is padding, not a detector outcome. All these effects
are positive and real symmetric. Summing the first line over $o$ gives
the same product effect as for any other prefix pair; summing over
prefixes gives $I_{25}$. Thus (12.4) retains both actual chains and
every failure, including impossible words with zero effect. It is the
POVM of the actual protocol, with no conditional division or free
replacement of failed specimens.

Put $S_0=I_5/5$ and introduce, only for the probability calculation,

$$
\begin{aligned}
\sigma_\theta
 &=\tfrac12\bigl(\rho_\theta^{\otimes2}
                    +\rho_{-\theta}^{\otimes2}\bigr)\\
 &=I_{25}/25+\theta^2Y\otimes Y.
\end{aligned}
\tag{12.5}
$$

Here $\rho_{-\theta}=\overline{\rho_\theta}$ is also lawful. Indeed $Y$
has eigenvalues $y=(1,-1,0,0,0)$, so the eigenvalues of $\rho_\theta$
are $1/5+\theta,1/5-\theta,1/5,1/5,1/5$, all strictly positive for
$|\theta|\le1/10$. For every real symmetric $Q$, the term
$\theta(Y\otimes I+I\otimes Y)/5$ in the tensor-square expansion has
zero trace pairing with $Q$: it is imaginary and has skew transpose.
Consequently

$$
\Pr_\theta(w\mid c)
=\operatorname{tr}(Q_{c,w}\rho_\theta^{\otimes2})
=\operatorname{tr}(Q_{c,w}\sigma_\theta).
\tag{12.6}
$$

This applies to the full effects (12.4), not just the terminal detector.
Each single-copy real effect likewise has probability
$\operatorname{tr}(PS_0)$ independent of $\theta$.

For an explicit classical representation of (12.6), choose once an
orthonormal eigenbasis $u_a$ of $Y$, independent of $\theta$, and define
on its twenty-five ordered pair labels

$$
q_\theta(a,b)=1/25+\theta^2y_ay_b,\qquad
K_c(w\mid a,b)
=\langle u_a\otimes u_b,Q_{c,w}(u_a\otimes u_b)\rangle.
\tag{12.7}
$$

The $q_\theta$ are the eigenvalue laws of $\sigma_\theta$. Each $K_c$
is a probability kernel independent of $\theta$, by positivity and
completeness of (12.4), and $q_\theta K_c$ is exactly the actual
configuration law. These spectral labels and kernels are a mathematical
simulation; the observer is not given the labels, a measurement of $Y$
or a new preparation procedure.

The reused symmetric-mixture calculation has the following exact
parameter correspondence. Each spectral factor is in the two nonzero
$Y$ directions with probability $2/5$, independent of the signed
parameter. Conditional on both factors being there, their symmetrized
sign law is the symmetric binomial supplier with $B=2$, $z=5\theta$
and $|z|\le1/2$; its ordered likelihood is $1+z^2s_1s_2$. Its positive-sign count has
exactly the law $p_z(2,\cdot)$ of
[SymmetricBinomialChiSquare](../../../D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.lean),
with [owning Scribe](../../../Blueprint/D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.scribe.cs).
The likelihood is constant on each count fiber, so passing to the count
preserves its second moment. The supplier's defect is $z^4$ when $B=2$.
All other spectral masks have unchanged law. Their contribution is zero,
whereas the both-active mask has weight $4/25$. Thus the pair defect is
$(4/25)(5\theta)^4=100\theta^4$. Directly, with
$\chi^2(q\Vert q_0)=\sum(q-q_0)^2/q_0$, the same correspondence reads

$$
\chi^2(q_\theta\Vert q_0)
=25\theta^4\sum_{a,b}y_a^2y_b^2
=100\theta^4,
\qquad \sum_a y_a^2=2.
\tag{12.8}
$$

By the iid service and terminal discard, the joint law of the $m$ pair
records is the product of the $m$ respective $q_\theta K_c$ laws.
The single-copy records have a common independent law. Consequently the
entire record, including its common metadata rules, is a common
postprocessing of $q_\theta^{\otimes m}$ with source-independent
randomness. Conditional on the auxiliary spectral labels, the kernels
in (12.7) do not change under the two hypotheses.

For completeness, the standard second-moment and testing suppliers
apply here as follows. The product likelihood $\Lambda$ has mean one
under $q_0^{\otimes m}$ and

$$
\mathbb E_0\Lambda^2=(1+100\theta^4)^m.
\tag{12.9}
$$

This is the product second-moment rule used in AURIC–Langlands
Theorem 3.5. For any common output kernel $K$, summing absolute
differences and using $\sum_wK(w\mid x)=1$ gives
$\operatorname{TV}(qK,q_0K)\le\operatorname{TV}(q,q_0)$.
The same proof uses integration for random metadata. Cauchy–Schwarz
under the strictly positive $q_0^{\otimes m}$ gives

$$
\operatorname{TV}(q_\theta^{\otimes m},q_0^{\otimes m})
=\tfrac12\mathbb E_0|\Lambda-1|
\le\tfrac12\sqrt{\mathbb E_0\Lambda^2-1}.
\tag{12.10}
$$

Insert $\theta=2/k$, so $100\theta^4=1600/r^2$, to obtain (12.3).
Appending any common randomized predictor is another such kernel.

The independent pair symmetrizations in this proof replace only the
laws of already terminal real experiments. They do not replace the
actual stationary source by a service that refreshes a hidden sign on
each call. No independently chosen signs are assigned to the future
copies. Without terminal discard the inter-attempt quantum carrier
would have to be included, and the present product-record reduction
would not establish (12.3). $\square$

**Definition 12.3 (separately supplied real continuation).** In addition
to the original acquisition interface, supply, at the relevant controller
state, the public integer $k$, current permission, $r=k^2$ fresh calls
to the same stationary service, their joint carrier $H^{\otimes r}$,
and the calibrated terminal binary instrument with Kraus operators
$E_k,I-E_k$, where

$$
T_r=\sum_{j=1}^rY^{(j)},\qquad
E_k=\mathbf1_{[4k^2,\infty)}(T_r^2).
\tag{12.11}
$$

Here $Y^{(j)}$ acts as $Y$ on factor $j$ and as the identity on every
other factor. The event of interest is its $E_k$ outcome, with probability
$p_{\theta,k}=\operatorname{tr}(E_k\rho_\theta^{\otimes r})$.
The full binary outcome is recorded and all $r$ measured registers are
then discarded. Before that discard a positive-probability branch has
its actual state $E_k\rho_\theta^{\otimes r}E_k/p_{\theta,k}$ or the
corresponding complement expression. A zero branch has zero mass and
no conditional state. This continuation specification is independent
of the unknown $\theta$; any information supplied with its calibration
or authorization is subject to Definition 12.1's independence rule.

Availability of this instrument is an additional contract, including
its size, joint control, storage, calibration, instructions, readable
backing and permission. It is not inferred from membership in Definition
11.1's mathematical class or compiled from the forty or fifty original
pair configurations. The following proposition proves the real-matrix
membership of this specified instrument, separately from its availability.

**Proposition 12.4 (the supplied consumer separates the two sources).**
The instrument in Definition 12.3 has real Kraus operators and is
trace-preserving. For every integer $k\ge20$,

$$
p_{0,k}\le\frac1{10},\qquad
p_{2/k,k}\ge\frac9{10},\qquad
p_{2/k,k}-p_{0,k}\ge\frac45.
\tag{12.12}
$$

Its probabilities are unchanged if the one source parameter is
simultaneously conjugated on all factors.

Proof. $Y$ and $T_r$ are Hermitian and purely imaginary, with
$\overline{T_r}=-T_r$. Hence $T_r^2$ is real symmetric and positive
semidefinite. The real spectral theorem makes its spectral projection
$E_k$ real symmetric, with $E_k^2=E_k$. Thus $E_k,I-E_k$ are real
Kraus operators whose adjoint squares sum to $I$. Simultaneous
conjugation preserves this real effect's trace probability; equivalently
it changes $T_r$ to $-T_r$ and leaves the event unchanged.

To calculate that probability, diagonalize $Y$ mathematically. Under
$\rho_\theta^{\otimes r}$ the spectral values $X_1,\ldots,X_r$ are
independent, each with

$$
\Pr_\theta(X=1)=1/5+\theta,\qquad
\Pr_\theta(X=-1)=1/5-\theta,\qquad
\Pr_\theta(X=0)=3/5.
\tag{12.13}
$$

Thus $p_{\theta,k}=\Pr_\theta(|\sum_jX_j|\ge2k)$,
$\mathbb E_\theta X=2\theta$ and
$\operatorname{Var}_\theta X=2/5-4\theta^2$. These are product-state
probabilities of the declared real joint event; individual measurements
of the nonreal $Y$ are not an allowed acquisition step.
At $\theta=0$ the sum has mean zero and variance $2k^2/5$.
Chebyshev's inequality therefore gives $p_{0,k}\le1/10$.
At $\theta=2/k$ its mean is $4k$ and its variance is
$2k^2/5-16\le2k^2/5$. The complement of the event has
$|\sum_jX_j|<2k$, which implies
$|\sum_jX_j-4k|>2k$. The same inequality bounds its probability
by $1/10$, proving (12.12). The sum-variance and Chebyshev steps are
standard finite-probability suppliers; for example their pinned
upstream statements are
[`IndepFun.variance_sum` and `meas_ge_le_variance_div_sq`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Moments/Variance.lean).
All variables here are bounded and all denominators $2k$ are positive.
$\square$

The real-Kraus convention is the established one in Wu et al.,
[*Resource theory of imaginarity: quantification and state conversion*,
§III, the real-Kraus definition](https://arxiv.org/abs/2103.01805v1).
Only its basis-dependent operation definition and real completion
principle are used; the realness and probability separation of (12.11)
are established above. The sign condition is joint: changing all
$\rho_\theta$ to $\rho_{-\theta}$ preserves the event, whereas
independently choosing conjugation representatives for different
factors need not preserve a joint law. The actual continuation uses
the same fixed representative as acquisition, as required in §11.

**Theorem 12.5 (necessary original-panel budget for this consumer).**
For every integer $k\ge20$, every positive integer $N$, either original
schedule of Definition 12.1, every $0<\delta<1/2$, and every predictor
allowed there, suppose that, before any continuation acquisition,

$$
\Pr_\theta\bigl(|\widehat p-p_{\theta,k}|\le1/5\bigr)
\ge1-\delta\qquad\text{for each }\theta\in\{0,2/k\}.
\tag{12.14}
$$

Then its number $m$ of pair attempts necessarily satisfies

$$
\boxed{
m\ge
\frac{\log(1+4(1-2\delta)^2)}{\log(1+1600/r^2)}
\ge\frac{r^2}{1600}\log(1+4(1-2\delta)^2).
}
\tag{12.15}
$$

All logarithms are natural. At confidence $3/4$, that is $\delta=1/4$,
this gives respectively

$$
\boxed{
N\ge\frac{r^2\log2}{64000}\quad\text{(directional)},\qquad
N\ge\frac{r^2\log2}{80000}\quad\text{(depth)}.
}
\tag{12.16}
$$

Integer budgets obey the ceilings of these bounds and, more strongly,
$N\ge\lceil\log(1+4(1-2\delta)^2)/
(c\log(1+1600/r^2))\rceil$, where $c=40$ or $50$.

Proof. Test the two source hypotheses by reporting $2/k$ precisely
when $\widehat p>1/2$. By (12.12), an error of at most $1/5$ places
$\widehat p\le3/10$ under zero and $\widehat p\ge7/10$ under $2/k$.
Therefore each testing error is at most $\delta$.
The standard two-point testing inequality, supplied by
[LeCam, `le_cam_two_point_sum`](../../../D5/S3/Estimation/LeCam.lean)
and its [owning Scribe](../../../Blueprint/D5/S3/Estimation/LeCam.scribe.cs),
requires $\operatorname{TV}(P_0,P_{2/k})\ge1-2\delta$.
This also covers random predictors: if $a(w)\in[0,1]$ is their
conditional probability of reporting $2/k$, their error sum is
$1-\sum_w(P_{2/k}(w)-P_0(w))a(w)\ge1-\operatorname{TV}(P_0,P_{2/k})$.
This is the same testing supplier applied to a randomized decision,
with integration if common metadata is continuous.

Combine this requirement with (12.3). Both sides are nonnegative,
so squaring gives
$(1+1600/r^2)^m\ge1+4(1-2\delta)^2$.
The denominator in (12.15) is strictly positive. Taking logarithms
proves its first inequality, and $\log(1+x)\le x$ for $x\ge0$
proves its second. Substituting $\delta=1/4$ and (12.2) gives
(12.16); integrality gives the stated ceilings. $\square$

The acquisition and, if performed once after prediction, continuation
charges belong to that same run. Adding Definition 12.3 to (10.5)
gives

$$
\begin{array}{c|c|c}
 &\text{directional}&\text{depth}\\ \hline
\text{source preparations}&95N+r&115N+r\\
\text{single-copy detector calls}&15N&15N\\
\text{local filter calls}&40N&60N+U_1\le90N\\
\text{original joint detector calls}&20N+C_D\le40N&20N+C_T\le50N\\
\text{additional }r\text{-register detector calls}&1&1\\
\text{outcome payload bits}&95N+1&155N+1
\end{array}
\tag{12.17}
$$

Here $U_1,C_D,C_T$ retain exactly their actual-run definitions in
Proposition 10.2. The preparation row follows by adding the $r$ fresh
requests; the extra call and bit are the one complete binary
continuation. All acquisition failures remain charged. The continuation
requires a carrier for $r$ jointly available five-mode inputs, of
Hilbert-space dimension $5^r$. Its hardware realization, workspace,
backing, calibration, instruction descriptions, counters, permission,
record reads/writes and prediction-output encoding add resources beyond
these rows. The prediction cut itself precedes those $r$ future
requests; promising them is not acquiring their outcomes in advance.
No relation between this call count and elementary gates, physical
duration, energy or a total implementation cost is assumed.

The coefficients in (12.16) express necessary bounds for two different
fixed schedules. Their ratio does not prove that either schedule is
more efficient, that a bound is attained, or that the constants are
optimal. The dependence on $\delta$ in (12.15) is the stated testing
consequence, not a confidence-optimal characterization. In particular,
it stays bounded as $\delta$ tends to zero. No upper bound is inferred.

**Corollary 12.6 (fixed acquisition cannot cover all supplied sizes).**
There is no family of predictors satisfying (12.14) with $\delta=1/4$
for every integer $k\ge20$ under these original schedules, no additional
acquisition before prediction, and a common finite upper bound $M$ on
the number of acquisition pair attempts. This remains true if the
predictor and the public choice of schedule and $N$ depend on $k$.
A common finite upper bound on training preparations also rules out
such a family.

Proof. Theorem 12.5 requires
$m\ge k^4\log2/1600$, which exceeds any fixed $M$ for some integer
$k$. Each pair attempt uses two preparations, so a finite preparation
bound implies a finite pair-attempt bound. $\square$

This corollary quantifies over both unknown sources for each supplied
size. It does not assert failure for every fixed source, a fixed
consumer, or training budgets increasing with $k$. It concerns
prediction of one specified event with a two-source promise. It neither
certifies all events simultaneously nor prohibits further sampling of
the same service. The actual information-bearing record has many bits;
the obstruction is its statistical relation to this consumer, not the
finiteness of a program or a bound on all possible memory.

Attribution and scope of Theorems 12.2 and 12.5. The contribution is the
correspondence (12.4)–(12.8) for the original complete flagged
acquisition and (12.11)–(12.13) for a particular same-source real
continuation, yielding the horizon-dependent necessary budget (12.15).
This is a repository-derived synthesis. Symmetric-mixture cancellation,
product second moments, total-variation contraction, two-point testing
and Chebyshev's inequality are reused ingredients, not new statistical
principles or a global originality claim.
[Phase Boundary §267](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md#267-唯一混合来源在完整重置接口上的八次方副本预算)
compares access to its fixed input/reference states $\Omega_j$ and
complete reset outputs $\sigma_j$, with budgets $h^{-2}$ and $h^{-8}$.
Those states and reset channels are not the five-mode preparations and
pair filters (12.4).
[Its §283](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md#283-有限共同相位块的最优重置副本预算与径向信息)
supplies the symmetric-binomial mechanism with block length $B$ and
bias $z$, then a complete-block adaptive reset budget. Here its
second-moment ingredient is used only with $B=2,z=5\theta$, conditional
on the both-active spectral mask of weight $4/25$. There is no refreshed
Haar phase, complete-block charging rule or transfer of its adaptive
upper/lower bounds to this schedule. The spectral simulation is not an
acquired program in either setting.

[AURIC–Langlands](AURIC_LANGLANDS_STRUCTURE_ACQUISITION_AND_SPECTRAL_EXTENSION_THEORY.md),
Theorem 3.5, already supplies logarithmic budget inversion from a
likelihood second moment, while Theorem 4.2 and Proposition 6.3 give
conjugation classification and full quadratic-tensor acquisition at the
level of laws. Its Proposition 4.4 supplies stability for the full tensor,
not this original record's numerical inverse. Its calibrated nonreal
reference in §5 is a different supplied resource. Its representation
splitting and conditional Hecke naturality in §§6–7 introduce no
implementation of (12.11). The private `real_trace_pairing`,
`statistics_iff_real` and `two_copy_classification`, together with public
`real_copy_classification`, in
[RealCopyConjugation](../../../D5/S3/Quantum/Fibers/RealCopyConjugation.lean)
and its [owning Scribe](../../../Blueprint/D5/S3/Quantum/Fibers/RealCopyConjugation.scribe.cs)
already express the real-statistics/conjugation suppliers; they assert
no acquired-record budget for this consumer.

Zhuang, [*On stability of generalized phase retrieval and generalized affine
phase retrieval*, §2, Theorem 2.3](https://doi.org/10.1186/s13660-019-1968-z),
gives the bi-Lipschitz estimate for a phase-retrievable real quadratic
map $M_A$ in the metric $\|x+y\|\|x-y\|$. That stability supplier does
not specify the finite sampling law, conditioning margins or an
executable numerical decoder for the present filtered panels. The
law/record distinction and lawful-output requirements also remain as
in [Recovery Geometry §§1–3](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md).
No new inverse-stability or sufficient all-source sampling theorem is
asserted here.

The [Native Structural Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md),
Theorems 6.2 and 7.3 and §9, transports complete actual native
representations and distinguishes their mathematical inverses from
receiver acquisition. [Native Paid View Conversion](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md),
Assumption 1.2 and §7, instead uses its declared fixed-height entrance
and added installation/conversion services. Their complete-history and
callable-conversion tasks are not this stochastic source's terminal
record prediction task. The added result here is an explicit necessary
budget between the latter record and a supplied later real event;
it neither replaces those native constructions nor derives the present
source, joint carrier or detector from them.

In particular, Proposition 10.4's exact-decoding obstruction remains
unchanged; it uses common support, whereas (12.15) quantifies approximate
prediction at a growing supplied size. Proposition 10.2 and §11 still
supply determination from exact panel laws: recover the same source
orbit and evaluate $\operatorname{tr}(E_k\rho^{\otimes r})$ using one
common representative. The two exact-law recovery routes agree by
(10.6) and Proposition 11.2, and the real event removes their one common
sign choice. Theorem 12.5 adds a necessary acquisition condition for
that task; it supplies neither an inverse from one finite word nor an
installed, calibrated and authorized implementation of the exact-law
calculation.

The fixed-$N$ hypotheses do not cover arbitrary adaptive configurations,
retry schemes or stopping-time/expected-budget contracts. Surviving
source-dependent quantum memory, new source-dependent advice, extra
observations or a nonreal reference change the acquisition interface.
No finite arithmetic or calibration-robust guarantee follows from the
ideal matrices. Mathematical realness of $E_k$ does not generate it
from the original menu or from native $\alpha/\beta$ constructors.
Mode correlations, ordered control responses, boundary laws and the
actual retained word keep their independent meanings in Definition 6.3;
these results do not recover physical space or time, a realized past,
or retained memory from a probability law. The fixed-$G_{gc}$,
original-$Q$, parked-consumer, unchanged-initialization, original-root
late-target, $M_1(D)$ and sharp-$\lambda$ obligations, and the all-size
positive acquisition/certification bridges retain their original scopes.
The joint four-expression recovery problem remains separate from this
necessary budget for a supplied family of continuations.

## 追加锚（本行以下为增补区）

## 13. An evaluated inverse certificate for the original fifty means

The setting in this section is the depth interface of Assumption 6.2,
with exactly the fixed frame, orientation, $F,L$ and detectors of
Definitions 6.1, 9.2 and 10.1. The source remains every $(S,A)$ in
$\mathcal L$. The certificate is algebraic on the larger space of all
real skew matrices; it requires no rank or spectral restriction on a
source. Section 12's necessary budget for a separately supplied coherent
consumer and the inverse certificate here concern different conclusions.

**Definition 13.1 (coordinates, polarization and fixed normalization).**
Order the ten edges as $(12,13,14,15,23,24,25,34,35,45)$.
For $u\in\mathbb R^{10}$ let $U(u)$ be the skew matrix whose ordered
upper entries are $u$, and write $u_{ik}=U(u)_{ik}$ also when $i>k$.
For a skew matrix set

$$
a(A)=(A_{ik})_{i<k},\qquad
\|A\|_{\mathrm{sk}}=\|a(A)\|_2=\|A\|_{\mathrm F}/\sqrt2.
\tag{13.1}
$$

For a symmetric matrix put
$\|T\|_{\triangle,2}^2=\sum_{i\le k}T_{ik}^2$.
This coordinate norm differs from its Frobenius norm. All vectors of
fifty means have the ordinary Euclidean norm. For a homogeneous
quadratic map $f$ use
$\operatorname{pol}f(u,v)=(f(u+v)-f(u-v))/4$.
Put $h_i=i^2/36$, $F_j=F^j$, $G_j=F^{2j}$, and define

$$
\begin{aligned}
C_j(u,v)&=-\tfrac12F_j\bigl(U(u)G_jU(v)+U(v)G_jU(u)\bigr)F_j,
&&j=0,1,2,\\
d(u,v)&=\operatorname{pol}(b\circ U)(u,v),\\
\Phi_F(u,v)&=\bigl((C_0)_{ik}:i\le k;\ d;
                         (C_1)_{ik}:i\le k;\ (C_2)_{ik}:i\le k\bigr).
\end{aligned}
\tag{13.2}
$$

There are $15+5+15+15=50$ coordinates. In particular,
$C_j(u,u)=K(F^jU(u)F^j)$.
For the four indices $a<b<c<d$ complementary to $r$, the orientation
in Definition 6.1 gives

$$
\begin{aligned}
b_r(U(u))&=2(-1)^{r-1}
 (u_{ab}u_{cd}-u_{ac}u_{bd}+u_{ad}u_{bc}),\\
d_r(u,v)&=(-1)^{r-1}
 (u_{ab}v_{cd}+v_{ab}u_{cd}-u_{ac}v_{bd}-v_{ac}u_{bd}
                         +u_{ad}v_{bc}+v_{ad}u_{bc}).
\end{aligned}
\tag{13.3}
$$

Let $Q_F(A)$ be the original fifty means $\mathbb E Z_f$ in (10.3),
in the order of (13.2), and let
$B_F=\operatorname{pol}(Q_F\circ U)$.
At depth $j$ its coordinate is
$M_f^{-1}\operatorname{pol}(A\mapsto f(F^jAF^j))$.
Here $M_f$ is computed from the base polynomial, before filtering:

| Base coordinate $f$ | Sum of absolute base coefficients | $M_f$ in (10.1) |
| --- | ---: | ---: |
| $K_{ii}=\sum_{\ell\ne i}A_{i\ell}^2$ | $4$ | $2$ |
| $K_{ik}=-\sum_{\ell\notin\{i,k\}}A_{i\ell}A_{\ell k}$, $i<k$ | $3$ | $7/4$ |
| $b_r$ in (13.3) | $6$ | $5/2$ |

The same detector and the same $M_f$ are used at every depth.
Thus $\Phi_F=D_M B_F$ for the diagonal matrix of these fifty base
normalizations, and
$\|\Phi_F(u,v)\|_2\le(5/2)\|B_F(u,v)\|_2$.
No full-tensor effect or depth-dependent rescaling is supplied.

**Lemma 13.2 (homogeneous five-vertex estimate).** For distinct indices
define

$$
x_{ik\ell}=u_{i\ell}v_{\ell k}+v_{i\ell}u_{\ell k},
\qquad z_{i\ell}=u_{i\ell}v_{i\ell}=z_{\ell i}.
\tag{13.4}
$$

If $\eta\ge0$ bounds the absolute values of every $x_{ik\ell}$,
every $z_{i\ell}$ and every $d_r(u,v)$, then

$$
\|u\|_2\|v\|_2\le100\eta.
\tag{13.5}
$$

Proof. If either vector vanishes the assertion holds. Otherwise divide
the two vectors by their norms and divide $\eta$ by their norm product.
Bilinearity reduces the proof to $\|u\|_2=\|v\|_2=1$.
Choose an edge $p=\{a,b\}$, $a<b$, on which
$\alpha=|u_{ab}|=\max_e|u_e|$. Then
$\alpha\ge1/\sqrt{10}$ and $|v_{ab}|\le\eta/\alpha$.

For every $c\notin\{a,b\}$ the two available equations are

$$
x_{bca}=-(u_{ab}v_{ac}+v_{ab}u_{ac}),\qquad
x_{acb}=u_{ab}v_{bc}+v_{ab}u_{bc}.
\tag{13.6}
$$

Ordered entries in these formulas automatically include the signs when
$c<a$ or $c<b$. Since every $|u_e|\le\alpha$, each of the six edges
meeting $p$ other than $p$ satisfies

$$
|v_e|\le\frac{\eta+|v_{ab}|\alpha}{\alpha}
       \le\frac{2\eta}{\alpha}.
\tag{13.7}
$$

For a disjoint edge $\{c,d\}$ let $r$ be the fifth vertex.
After multiplication by its orientation sign, (13.3) contains
$u_{ab}v_{cd}+v_{ab}u_{cd}$ and four other products. Each of those
four products has a $v$ edge meeting $p$ other than $p$, so its absolute
value is at most $\alpha(2\eta/\alpha)=2\eta$.
The term $v_{ab}u_{cd}$ has absolute value at most $\eta$.
Consequently

$$
\alpha|v_{cd}|\le\eta+\eta+4(2\eta)=10\eta.
\tag{13.8}
$$

All ten coordinates of $v$ are now at most $10\eta/\alpha$ in absolute
value, including $p$. Therefore
$1=\|v\|_2\le10\sqrt{10}\eta/\alpha\le100\eta$.
Undoing the normalization proves (13.5). The classification into the
chosen edge, its six neighbors and its three disjoint edges exhausts
all ten edges. $\square$

**Lemma 13.3 (explicit inversion of the original filtered moments).**
For every real $u,v$,

$$
\|u\|_2\|v\|_2\le16124313600\,\|\Phi_F(u,v)\|_2.
\tag{13.9}
$$

Proof. Put $\Delta=\|\Phi_F(u,v)\|_2$; each coordinate of (13.2)
has absolute value at most $\Delta$.
Every two distinct $h_i$ differ by at least $1/12$, and
$0<h_i<1$. For $i\ne k$ the three off-diagonal moments are

$$
y_j^{ik}=-\frac{2(C_j)_{ik}}{(i/6)^j(k/6)^j}
     =\sum_{\ell\notin\{i,k\}}h_\ell^j x_{ik\ell},
\qquad j=0,1,2.
\tag{13.10}
$$

The denominators used here are at least $6^{-4}$, so
$|y_j^{ik}|\le2592\Delta$. For the remaining three indices $r,s,t$,
subtracting $(h_s+h_t)y_1^{ik}$ from
$y_2^{ik}+h_sh_ty_0^{ik}$ cancels the $s,t$ terms. Hence

$$
x_{ikr}=
\frac{h_sh_t y_0^{ik}-(h_s+h_t)y_1^{ik}+y_2^{ik}}
     {(h_r-h_s)(h_r-h_t)},\qquad
|x_{ikr}|\le144\cdot4\cdot2592\Delta=1492992\Delta.
\tag{13.11}
$$

This formula applies to each of the three choices of $r$ and to every
ordered off-diagonal entry; symmetry of $C_j$ supplies either order.

The diagonal moments give all fifteen numbers

$$
t_{ij}=\frac{(C_j)_{ii}}{(i/6)^{2j}}
       =\sum_{\ell\ne i}h_\ell^j z_{i\ell},\qquad
|t_{ij}|\le1296\Delta,\qquad j=0,1,2.
\tag{13.12}
$$

Here is an explicit inversion using these moments, without an unknown
conditioning constant. To recover any edge $\{a,b\}$ choose any third
vertex $c$, and let $r,s$ be the remaining two vertices. For
$i\in\{a,b,c\}$ put

$$
w_i=(h_i-h_r)(h_i-h_s),\qquad
R_i=t_{i2}-(h_r+h_s)t_{i1}+h_rh_s t_{i0}.
\tag{13.13}
$$

The polynomial $(X-h_r)(X-h_s)$ vanishes at $h_r,h_s$. Substitution
in (13.12) therefore gives the three exact equations

$$
R_a=w_bz_{ab}+w_cz_{ac},\qquad
R_b=w_az_{ab}+w_cz_{bc},\qquad
R_c=w_az_{ac}+w_bz_{bc}.
\tag{13.14}
$$

Multiply these equations by $w_a,w_b,w_c$, respectively, and add the
first two minus the third. The $z_{ac},z_{bc}$ terms cancel, proving

$$
z_{ab}=\frac{w_aR_a+w_bR_b-w_cR_c}{2w_aw_b}.
\tag{13.15}
$$

Every $1/144\le|w_i|\le1$, and (13.12) gives
$|R_i|\le(1+2+1)1296\Delta=5184\Delta$. Thus for every edge

$$
|z_{ab}|\le\frac32\,144^2\,5184\Delta=161243136\Delta.
\tag{13.16}
$$

Finally $|d_r|\le\Delta$. Since $1492992<161243136$, all the
hypotheses of Lemma 13.2 hold with $\eta=161243136\Delta$.
Its factor $100$ gives (13.9), including when $\Delta=0$.
Every denominator above depends only on the five fixed filter entries;
no division by a source coordinate, eigenvalue or spectral gap occurs
in this moment inversion. $\square$

**Theorem 13.4 (evaluated detector-normalized certificate).** The
polarization of the original fifty means satisfies

$$
\boxed{
\|B_F(u,v)\|_2\ge c_F\|u\|_2\|v\|_2,
\qquad c_F=\frac1{40310784000}>0,
\qquad u,v\in\mathbb R^{10}.
}
\tag{13.17}
$$

Proof. Combine (13.9) with
$\|\Phi_F\|_2\le(5/2)\|B_F\|_2$ from Definition 13.1 and the exact
identity $(5/2)16124313600=40310784000$. $\square$

For correspondence with the general suppliers, write the $\nu$th
coordinate of $Q_F\circ U$ as $u^T R_\nu u$. Each $R_\nu$ is the real
symmetric $10\times10$ coefficient matrix, with half the mixed
coefficient in each off-diagonal position. Then
$B_F(u,v)_\nu=u^T R_\nu v$. There are exactly fifty such matrices,
and their entries include the base $M_f^{-1}$ at every depth.
Wang–Xu, [*Generalized phase retrieval*, Theorem 2.1](https://arxiv.org/html/1605.08034v3),
equates real quadratic phase retrieval with nonsingularity of this
bilinear map. Its hypotheses hold here by Theorem 9.1 on all real skew
matrices. Zhuang, [*On stability of generalized phase retrieval and
generalized affine phase retrieval*, Lemma 2.1, Theorem 2.3 and
(2.3)](https://link.springer.com/article/10.1186/s13660-019-1968-z),
supplies the general positive frame bound and product-distance stability.
Those results apply to real symmetric coefficient matrices without a
positive-semidefiniteness requirement; the square-root measurement
results later in that paper have extra hypotheses and are not used.
The number $c_F^2$ is an evaluated lower choice for its squared frame
bound $a_0$. The source-specific contribution here is the bound
(13.17), obtained from the original moments by (13.6)–(13.16), rather
than a new general phase-retrieval or compactness theorem.

## 14. Residual-qualified precision and the complete finite record

**Proposition 14.1 (orbit ambiguity and arbitrary off-image readouts).**
For real skew $A,B$ put

$$
d_\pm(A,B)=\min\{\|A-B\|_{\mathrm{sk}},\|A+B\|_{\mathrm{sk}}\},
\qquad
D_\pm(A,B)=\max\{\|A-B\|_{\mathrm{sk}},\|A+B\|_{\mathrm{sk}}\}.
\tag{14.1}
$$

With $K_F=c_F^{-1}=40310784000$, one has

$$
d_\pm D_\pm\le K_F\|Q_F(A)-Q_F(B)\|_2.
\tag{14.2}
$$

More explicitly, let $(S,A),(T,B)\in\mathcal L$, and let
$y\in\mathbb R^{50}$ and a real symmetric $\widehat S$ be arbitrary
readouts, not necessarily in the lawful image. Suppose known bounds are

$$
\begin{aligned}
\|Q_F(A)-y\|_2&\le\varepsilon_Q,&
\|Q_F(B)-y\|_2&\le r_Q,\\
\|S-\widehat S\|_{\mathrm F}&\le\varepsilon_S,&
\|T-\widehat S\|_{\mathrm F}&\le r_S.
\end{aligned}
\tag{14.3}
$$

All four bounds are nonnegative. Then

$$
\begin{aligned}
d_\pm D_\pm&\le40310784000(\varepsilon_Q+r_Q),\\
d_\pm&\le\sqrt{40310784000(\varepsilon_Q+r_Q)},\\
\|S-T\|_{\mathrm F}&\le\varepsilon_S+r_S,\\
\min_{\sigma\in\{-1,1\}}
\|(S+iA)-(T+i\sigma B)\|_{\mathrm F}
&\le\sqrt{(\varepsilon_S+r_S)^2+
                     80621568000(\varepsilon_Q+r_Q)}.
\end{aligned}
\tag{14.4}
$$

If $D_\pm\ge r>0$, the second line may be replaced by the linear
bound $d_\pm\le40310784000(\varepsilon_Q+r_Q)/r$.
Any two lawful candidates whose quadratic residuals about the same $y$
are at most $\varepsilon_Q$ obey
$d_\pm D_\pm\le80621568000\varepsilon_Q$.

Proof. The product-distance implication is Zhuang's Theorem 2.3/(2.3)
with the evaluated lower bound (13.17). In the present conventions its
polarization identity is exactly

$$
Q_F(A)-Q_F(B)=B_F(a(A)-a(B),a(A)+a(B)).
\tag{14.5}
$$

Thus its distance product is $d_\pm D_\pm$, with no extra factor.
The triangle inequality gives the first and third lines of (14.4).
Since $D_\pm\ge d_\pm$, the first line bounds $d_\pm^2$.
Finally the squared complex Frobenius norm is
$\|S-T\|_{\mathrm F}^2+2\|A-\sigma B\|_{\mathrm{sk}}^2$;
minimize over the one common sign. Division by the declared positive
$r$ gives the local bound. The two-candidate assertion uses the same
triangle inequality. $\square$

In particular the global bound has a square root in readout error;
it covers $A=0$, singular densities and repeated-spectrum strata.
A lower bound on $D_\pm$ is a separate condition, not a genericity
assumption silently imposed on this global statement. The readout
premises do not construct a lawful candidate. A finite-arithmetic
residual certificate must include its evaluation error in $r_Q,r_S$;
substituting unbounded numerical residual approximations would not
verify (14.3).

**Proposition 14.2 (confidence radii for the original complete schedule).**
Fix a positive integer $N$ and $0<\delta<1$. Use exactly the depth schedule of
Proposition 10.2: $N$ independent attempts for each of the fifty pair
configurations and each of the fifteen single-copy settings, in the
fixed public order, with no retries. Retain both filter chains and all
failed prefixes. Put

$$
L_\delta=\log(130/\delta),\qquad
\tau_{\rm pair}=\sqrt{2L_\delta/N},\qquad
\tau_{\rm single}=\sqrt{L_\delta/(2N)}.
\tag{14.6}
$$

Let $\overline q$ be the fifty averages of the actual variables
$Z_f\in\{-1,0,1\}$ in Definition 10.1. Let $\overline p$ be the fifteen
averages of the single-copy indicators, and form $S_N$ by applying
(10.4) to those fifteen averages. For each fixed lawful source, with
probability at least $1-\delta$ simultaneously,

$$
\begin{aligned}
\|\overline q-Q_F(A)\|_\infty&\le\tau_{\rm pair},&
\|\overline q-Q_F(A)\|_2&\le10\sqrt{L_\delta/N},\\
\|\overline p-p(S)\|_\infty&\le\tau_{\rm single},&
\|S_N-S\|_{\triangle,2}&\le3\sqrt5\,\tau_{\rm single},\\
&&\|S_N-S\|_{\mathrm F}&\le\sqrt{85}\,\tau_{\rm single}.
\end{aligned}
\tag{14.7}
$$

Here $p(S)$ denotes precisely the fifteen probabilities in (10.4).
The confidence level is uniform over the lawful domain in the sense
that the same constants work for every fixed source; it is not a
simultaneous coupling of runs from different sources.

For actual arithmetic outputs $y\in\mathbb R^{50}$ and real symmetric
$\widehat S$, suppose certified nonnegative tolerances $a_Q,a_S$ satisfy
$\|y-\overline q\|_2\le a_Q$ and
$\|\widehat S-S_N\|_{\mathrm F}\le a_S$.
On the same event the source-error inputs in (14.3) may be taken as

$$
\varepsilon_Q=a_Q+10\sqrt{L_\delta/N},\qquad
\varepsilon_S=a_S+\sqrt{85}\,\tau_{\rm single}.
\tag{14.8}
$$

There is also the symmetric coordinate bound
$\|\widehat S-S\|_{\triangle,2}\le a_S+3\sqrt5\tau_{\rm single}$.
Consequently every lawful candidate with certified residuals $r_Q,r_S$
obeys (14.4), with these explicit values. The statement is simultaneous
over such candidates, including candidates selected after reading the
record; no further union bound over candidates is required.

Proof. Conditional on the fixed source, Assumption 6.2 and the
independent instrument initialization give independent attempts within
each configuration. Every pair variable uses the denominator $N$ of
all attempts. It equals zero on a failed prefix and has expectation
$f(F^jAF^j)/M_f$ by (10.3). Thus it estimates $Q_F(A)$ directly,
without multiplying by a newly chosen normalization or dividing by
success counts.

The bounded-independent-variable Hoeffding inequality gives, for $t>0$,
the actual two-sided tails

$$
\Pr(|\overline q_\nu-Q_F(A)_\nu|\ge t)
 \le2\exp(-Nt^2/2),\qquad
\Pr(|\overline p_\ell-p(S)_\ell|\ge t)
 \le2\exp(-2Nt^2).
\tag{14.9}
$$

The first range has length two, and the second range has length one.
The standard supplier is Hoeffding,
[*Probability Inequalities for Sums of Bounded Random Variables*,
Theorem 2](https://doi.org/10.1080/01621459.1963.10500830),
applied with those ranges. At the respective radii in (14.6) both
right sides are $2e^{-L_\delta}=\delta/65$.
A union bound over $50+15=65$ settings gives the claimed event.
In particular the pair radius is twice the single radius.

On that event, the fifty-dimensional Euclidean error is at most
$\sqrt{50}\tau_{\rm pair}=10\sqrt{L_\delta/N}$.
Each diagonal entry of $S_N$ has error at most $\tau_{\rm single}$.
By (10.4), each of its ten off-diagonal entries has error at most
$\tau_{\rm single}+\tfrac12(2\tau_{\rm single})
=2\tau_{\rm single}$.
The two squared norm bounds are therefore
$5\tau_{\rm single}^2+10(2\tau_{\rm single})^2=45\tau_{\rm single}^2$
and
$5\tau_{\rm single}^2+20(2\tau_{\rm single})^2=85\tau_{\rm single}^2$.
Adding the separate arithmetic tolerances proves (14.8), using
$\|T\|_{\triangle,2}\le\|T\|_{\mathrm F}$ for the coordinate version.
Proposition 14.1 is deterministic on this event and hence applies to
every qualifying candidate. $\square$

**Corollary 14.3 (nonempty confidence regions and charged precision).**
Under Proposition 14.2 define the set of lawful candidates

$$
\mathcal C=
\{(T,B)\in\mathcal L:
 \|Q_F(B)-y\|_2\le\varepsilon_Q,
 \|T-\widehat S\|_{\mathrm F}\le\varepsilon_S\}.
\tag{14.10}
$$

With probability at least $1-\delta$ it contains the true source, and
every two of its elements obey

$$
d_\pm(A,B)\le\sqrt{80621568000\varepsilon_Q},\qquad
\|S-T\|_{\mathrm F}\le2\varepsilon_S.
\tag{14.11}
$$

For prescribed skew-coordinate ambiguity $h>0$ and symmetric Frobenius
ambiguity $g>0$, suppose
$a_Q<h^2/80621568000$ and $a_S<g/2$.
It suffices to choose the positive integer $N$ with

$$
N\ge\max\left\{
\frac{100L_\delta}{(h^2/80621568000-a_Q)^2},\quad
\frac{85L_\delta}{2(g/2-a_S)^2}
\right\}.
\tag{14.12}
$$

Every such region has the ambiguities at most $h,g$ on that event.
The complete acquisition charges for this $N$ are

$$
\begin{array}{c|c}
\text{source preparations}&115N\\
\text{single-copy detector calls}&15N\\
\text{local filter calls}&60N+U_1\le90N\\
\text{joint detector calls}&20N+C_T\le50N\\
\text{padded outcome-record bits}&155N.
\end{array}
\tag{14.13}
$$

The variables $U_1,C_T$ have exactly their actual-run meanings in
Proposition 10.2. All preparations and actual calls on failed prefixes
are charged. Both specimens execute their prescribed chain even if
the other fails; an unexecuted detector is only padded.

Proof. On the event (14.7), (14.8) puts $(S,A)$ in $\mathcal C$.
For any two candidates in this set the triangle inequality bounds their
quadratic-mean difference by $2\varepsilon_Q$, and their symmetric
difference by $2\varepsilon_S$. Apply (14.2) and $d_\pm^2\le d_\pm D_\pm$
to obtain (14.11). Inequality (14.12) makes
$\varepsilon_Q\le h^2/80621568000$ and
$\varepsilon_S\le g/2$, which proves the precision assertion.

There are $50N$ pairs and $15N$ single specimens, giving $115N$
preparations. The $15N$ depth-one pairs use $30N$ local filter calls;
the depth-two pairs use $30N$ first calls and $U_1$ second calls.
There are $20N$ unfiltered joint detector calls and $C_T$ filtered
double-success calls. The payload is
$15N+20N+3(15N)+5(15N)=155N$ bits. This is exactly (10.5), without
free successful replacement. $\square$

The region (14.10) is a set-valued precision assertion, not an installed
point-output orbit decoder. For an arbitrary off-image readout outside
the confidence event it can be empty. Certifying a candidate's lawfulness,
finding one, evaluating residual bounds with finite arithmetic, and
proving a bound on that computation's time and workspace remain separate
tasks. The arithmetic tolerances in (14.8) are declared premises, not
an uncharged algorithm. At zero arithmetic tolerance the displayed
sufficient pair-precision budget scales as $h^{-4}$; no claim of sharp
risk or resource optimality follows. There is no exact recovery of
continuous parameters from a fixed finite record, in accordance with
Proposition 10.4.

The outcome payload in (14.13) retains order and failures. Its reads and
writes, extraction of counts, source/frame/calibration backing, schedule
and program descriptions, counters, allocation, arithmetic-output
encoding, workspace and actual permissions require the further
resources in Definition 10.3. The rows give neither elementary gate
counts nor physical time or energy. Section 12's separately supplied
coherent continuation is not executed or charged in this acquisition
result; its necessary lower bound remains in its original prediction
task. The present upper certificate does not assert an efficient
predictor for that task or a matching lower bound.

Attribution and scope. The evaluated number (13.17), the moment
relations (13.10)–(13.16) and their consumer (14.4), (14.8)–(14.13)
are a repository-derived synthesis for the fixed fifty means and the
same lawful source. Nonsingular-polarization and product-distance
stability are the published Wang–Xu and Zhuang suppliers cited above;
bounded independent concentration is Hoeffding's inequality. These
ingredients are not new general theorems or a claim of global
literature originality. The certificate adds no observations or
permissions, no nonreal reference, no source-dependent selector and no
free post-selection. It uses the additional preparation/control
service in Assumption 6.2, without implementing it in the old
wait/read/Stop menu or by native $\alpha/\beta$ constructors. Physical
Euclidean dimension, full joint prediction, lawful off-image decoding
with proved arithmetic cost, fixed-record sharp risk and the remaining
native acquisition/certification bridges retain their separate scopes.
No Lean verification or physical realization is asserted.

## 追加锚（本行以下为增补区）

## 15. A total rational Gram decoder for the original complete record

**Definition 15.1 (record input, precision and output task).** Keep the
entire lawful domain $\mathcal L$ of (6.1), the ideal stationary
independent preparation service of Assumption 6.2, and precisely the depth
instrument, terminal instruments and fixed schedule of Definitions 9.2,
10.1 and Proposition 10.2. In particular the filter is
$F=\operatorname{diag}(1,2,3,4,5)/6$, the base detector normalizations are
those in Definition 13.1 at every depth, and there is no calibration error
in these matrices. Let $N\ge1$ be an integer. A grammatical record is any
word of the original depth schedule's padded grammar, with its fifteen
single-copy blocks and fifty pair blocks of $N$ attempts each, in their
public order. It includes both chains of each pair, every actual failure
prefix and every actual detector outcome. The source/frame/calibration
binding and occurrence labels retain their meanings in Definitions 10.3
and 12.1. They are not numerical advice about the source.

For definiteness, a detector outcome bit $o$ means $2o-1$. A depth-one
chain uses flag $0$ for failure and $1$ for success. A depth-two chain
uses $00,10,11$ for first failure, success then failure, and two successes,
respectively. The pair's detector bit is zero padding unless both chains
succeed. These codes merely give the three-bit and five-bit payloads of
(10.5); padding is never interpreted as an attempted measurement. At depth
zero there is only the detector bit. A single-copy bit is the indicator
of its projector outcome. Grammatical words need not be likely, or even
have positive probability under a particular singular source.

For pair configuration $\nu$ let $w_\nu$ be its sum of the variables
$Z_f$ in Definition 10.1, including zero for every failed attempt. For
single-copy setting $P_i$ or $P_{ij}$ let $c_i,c_{ij}$ count its indicators.
Define the exact rational extractions

$$
\begin{aligned}
y_\nu&=w_\nu/N,\\
s_{ii}&=2c_i,&
s_{ij}&=2c_{ij}-c_i-c_j\quad(i<j),&s_{ji}&=s_{ij},\\
\widehat S&=(s_{ij}/(2N))_{i,j=1}^5.
\end{aligned}
\tag{15.1}
$$

Thus $y=\overline q$ and $\widehat S=S_N$ of Proposition 14.2. Each
pair mean has denominator $N$ of all attempts, regardless of the number
of successes. Counting does not replace the retained ordered word by a
count-only record for other tasks.

The additional public precision input is an integer $b\ge3$, independent
of the unknown source, and $m=2^b$. An output is a rational density
$\widehat\rho=T+iB$ in the same fixed frame, interpreted as the source-orbit
description $(T,\{B,-B\})$. For comparison with $\rho=S+iA$ use

$$
\mathfrak d(\rho,\widehat\rho)
=\min_{\sigma\in\{-1,1\}}
  \|S+iA-(T+i\sigma B)\|_{\mathrm F}.
\tag{15.2}
$$

Only this one common conjugation sign is forgotten. Orthogonal changes
of frame, independent signs for different registers, and equality of
spectra are not additional identifications.

**Definition 15.2 (finite bank and exact minimum rule).** In the fixed
row-major order of the real and imaginary entries, enumerate all
$5\times5$ Gaussian-integer matrices $X=(r_{ik}+it_{ik})$ with
$r_{ik},t_{ik}\in\{-m,\ldots,m\}$, omitting the zero matrix. Use
lexicographic order in these fifty integers. Set

$$
\begin{aligned}
U_{X,ik}&=\sum_{\ell=1}^5
 (r_{i\ell}r_{k\ell}+t_{i\ell}t_{k\ell}),\\
V_{X,ik}&=\sum_{\ell=1}^5
 (t_{i\ell}r_{k\ell}-r_{i\ell}t_{k\ell}),\\
D_X&=\sum_{i,\ell}(r_{i\ell}^2+t_{i\ell}^2),\\
\rho_X&=XX^\dagger/D_X=T_X+iB_X,
\qquad T_X=U_X/D_X,\quad B_X=V_X/D_X.
\end{aligned}
\tag{15.3}
$$

For the original normalized map $Q_F$ of Definition 13.1, minimize the
rational squared residual

$$
J_X=\|T_X-\widehat S\|_{\mathrm F}^2
       +\|Q_F(B_X)-y\|_2^2
\tag{15.4}
$$

over this finite bank, keeping the first candidate in a tie. The decoder
$\mathsf{Dec}_b(W)$ returns its $D_X$, fifteen upper-triangular entries of
$U_X$, and ten strictly upper-triangular entries of $V_X$. Symmetry and
skew symmetry fill the other entries. No reduction to lowest terms is
required. This is a rational matrix description, with denominator $D_X$,
and not a program to prepare that state. A single Gram candidate supplies
both $T_X$ and $B_X$, so their positive compatibility is enforced jointly
throughout the search. Its residual uses precisely the fifteen single
extractions and fifty original pair means.

Here is an integer specification of the comparisons in (15.4). Put

$$
C=70\,6^8,\qquad
P_\nu(v)=C\,Q_F(U(v))_\nu\quad(1\le\nu\le50),
\tag{15.5}
$$

where $U(v)$ is the skew-coordinate map of Definition 13.1. These are
fixed homogeneous degree-two integer polynomials, as verified in
Theorem 15.5. For a candidate abbreviate $D=D_X$, $U=U_X$, $V=V_X$, and
use $P_\nu(V)$ to mean evaluation on its ten upper skew entries. Compute

$$
\begin{aligned}
E_X&=2CND^2,\\
\alpha_{ik}&=CD(2NU_{ik}-Ds_{ik}),\\
\beta_\nu&=2\{NP_\nu(V)-CD^2w_\nu\},\\
H_X&=\sum_i\alpha_{ii}^2
        +2\sum_{i<k}\alpha_{ik}^2+\sum_{\nu=1}^{50}\beta_\nu^2.
\end{aligned}
\tag{15.6}
$$

Then $J_X=H_X/E_X^2$. A new candidate replaces the stored one exactly
when $H_X E_{\rm stored}^2<H_{\rm stored}E_X^2$. All denominators are
positive integers. Enumeration, this integer inequality and the fixed
tie rule completely specify the selection; no exact-real comparison,
feasibility oracle or unspecified minimizer is part of the algorithm.

**Theorem 15.3 (lawful total output and uniform deterministic error).**
For every $N\ge1$, $b\ge3$ and grammatical finite record $W$, the decoder
of Definition 15.2 terminates and returns $(T,B)\in\mathcal L$ with
rational entries. For every lawful source $(S,A)$ and all nonnegative
numbers $e_S,e_Q$ for which that record satisfies

$$
\|S-\widehat S\|_{\mathrm F}\le e_S,
\qquad \|Q_F(A)-y\|_2\le e_Q,
\tag{15.7}
$$

put

$$
e=(e_S^2+e_Q^2)^{1/2},\qquad
\nu=2e+512\,2^{-b},\qquad K_F=40310784000.
\tag{15.8}
$$

Its actual output satisfies

$$
\begin{aligned}
\bigl(\|T-\widehat S\|_{\mathrm F}^2
       +\|Q_F(B)-y\|_2^2\bigr)^{1/2}
 &\le e+512\,2^{-b},\\
\|S-T\|_{\mathrm F}&\le\nu,\\
d_\pm(A,B)D_\pm(A,B)&\le K_F\nu,\\
d_\pm(A,B)&\le\sqrt{K_F\nu},\\
\mathfrak d(S+iA,T+iB)&\le\sqrt{\nu^2+2K_F\nu}.
\end{aligned}
\tag{15.9}
$$

These are deterministic implications for every such record, including
records outside any confidence event. There is no lower bound on a
source eigenvalue, on $\|A\|_{\rm sk}$ or on a spectral gap. In
particular real sources $A=0$, all singular faces, and repeated-spectrum
sources are included.

Proof. Each nonzero $X$ has $1\le D_X\le50m^2$ and
$XX^\dagger\succeq0$, with trace $D_X$. Its real and imaginary parts
are symmetric and skew, respectively. This proves lawfulness and
rationality directly, without testing principal minors. The bank has
exactly $(2m+1)^{50}-1$ indexed candidates; duplicates as density matrices
cause no difficulty. There is a nonzero candidate, for example a single
entry equal to one. Hence a complete finite scan with the tie rule
returns one lawful candidate on every grammatical word. No statistical
premise is needed for this conclusion.

We next give two estimates used to control this particular scan. The
normalized Gram representation and rounding used in the first estimate
are standard finite-dimensional tools; they are intermediate steps, not
an additional general tomography theorem. Given any lawful
$\rho=S+iA$, let $R=\rho^{1/2}$. The finite Hermitian spectral theorem
gives $R R^\dagger=\rho$ and $\|R\|_{\mathrm F}=1$, even when $\rho$
is singular. Each real and imaginary entry of $R$ lies in $[-1,1]$.
Round the fifty real coordinates of $mR$ to nearest integers in
$[-m,m]$, obtaining a bank matrix $X$, and put $Y=X/m$. Then

$$
\eta:=\|Y-R\|_{\mathrm F}
   \le\frac{\sqrt{50}}{2m}\le\frac4m\le\frac12.
\tag{15.10}
$$

Thus $Y\ne0$. With $Z=Y/\|Y\|_{\mathrm F}$, the reverse triangle
inequality gives

$$
\|Z-R\|_{\mathrm F}
 \le\|Z-Y\|_{\mathrm F}+\|Y-R\|_{\mathrm F}
 =|1-\|Y\|_{\mathrm F}|+\eta\le2\eta.
$$

For matrices $P,Q$, the inequality
$\|PQ\|_{\mathrm F}\le\|P\|_{\mathrm F}\|Q\|_{\mathrm{op}}$
follows by summing squared row norms, and the version with the two norms
interchanged follows by adjoints. Apply these inequalities to
$ZZ^\dagger-RR^\dagger=(Z-R)Z^\dagger+R(Z^\dagger-R^\dagger)$.
Both $Z,R$ have operator norm at most one. Consequently this bank
candidate obeys

$$
\|\rho_X-\rho\|_{\mathrm F}
=\|ZZ^\dagger-RR^\dagger\|_{\mathrm F}
\le2\|Z-R\|_{\mathrm F}\le4\eta\le16/m.
\tag{15.11}
$$

The square root and rounding in this argument exhibit a near candidate
for the proof. The decoder never receives $R$, computes it, or selects
the displayed candidate using source access.

For the second estimate define
$\mathcal O(\rho)=(\operatorname{Re}\rho,Q_F(\operatorname{Im}\rho))$
with squared norm equal to the sum of squared Frobenius and Euclidean
norms. For original pair configuration $\nu$ at depth $j$, the expectation
of its complete-attempt variable is

$$
\mathbb E_\rho Z_\nu
 =\operatorname{tr}(D_\nu\rho^{\otimes2}),\qquad
D_\nu=(F^j\otimes F^j)(H_f/M_f)(F^j\otimes F^j).
\tag{15.12}
$$

This is (10.3), with zero on failures. The effects are those of (10.1),
so $D_\nu$ is Hermitian and $\|D_\nu\|_{\mathrm{op}}\le1$.
For a Hermitian $\Delta=\sum_a\lambda_a u_au_a^\dagger$ and such a
contraction, $|\operatorname{tr}(D_\nu\Delta)|\le\sum_a|\lambda_a|
=\|\Delta\|_1$. The eigenvalues of a tensor product of Hermitian
matrices are their pairwise products; in particular
$\|\Delta\otimes\sigma\|_1=\|\Delta\|_1$ for a density $\sigma$.
The identity

$$
\rho^{\otimes2}-\sigma^{\otimes2}
=(\rho-\sigma)\otimes\rho+\sigma\otimes(\rho-\sigma)
$$

and the trace-norm triangle inequality therefore bound each coordinate
difference in (15.12) by $2\|\rho-\sigma\|_1$. Cauchy--Schwarz on
the five real eigenvalues of $\rho-\sigma$ bounds this by
$2\sqrt5\|\rho-\sigma\|_{\mathrm F}$. Also
$\|\operatorname{Re}(\rho-\sigma)\|_{\mathrm F}
\le\|\rho-\sigma\|_{\mathrm F}$. There are exactly fifty pair
coordinates, whence

$$
\|\mathcal O(\rho)-\mathcal O(\sigma)\|
\le\sqrt{1+50(2\sqrt5)^2}\,\|\rho-\sigma\|_{\mathrm F}
=\sqrt{1001}\,\|\rho-\sigma\|_{\mathrm F}
\le32\|\rho-\sigma\|_{\mathrm F}.
\tag{15.13}
$$

This estimate concerns only the supplied complete-attempt means. It
introduces no new measured observable.

Combine (15.11) and (15.13). For the true source there exists a bank
candidate with observation distance at most $512/m$. The data point
$(\widehat S,y)$ is at distance at most $e$ from its true observation
by (15.7). The triangle inequality makes that candidate's residual at
most $e+512/m$. The exact minimum rule makes the chosen candidate's
residual no larger, proving the first line of (15.9). A second triangle
inequality gives

$$
\|\mathcal O(S+iA)-\mathcal O(T+iB)\|\le2e+512/m=\nu.
\tag{15.14}
$$

Each component is at most $\nu$. Apply the already proved original-map
inequality (14.2) to its quadratic component to obtain
$d_\pm D_\pm\le K_F\nu$. Since $D_\pm\ge d_\pm$, this bounds
$d_\pm^2$. Finally the squared error after the better one common sign
is $\|S-T\|_{\mathrm F}^2+2d_\pm^2$, which proves the last line.
Every use of the inverse certificate is within its stated all-skew
domain; no exact inverse branch, rank decision or conditioning margin
was substituted for finite arithmetic. $\square$

**Definition 15.4 (classical execution and separate storage accounts).**
The execution model is a deterministic multitape Turing machine over a
fixed finite alphabet. One transition reads or writes a bounded number
of bits and moves each tape head by at most one cell. Integers are in
signed binary; addition, multiplication and comparison are performed by
bit arithmetic, not unit-cost operations on unbounded words. The fixed
program contains the fifty polynomials (15.5), the original schedule
parser, and fixed matrix dimensions. It has no source-dependent advice.

The retained input tape contains the complete original padded word,
$N$, $b$, and a finite metadata string of length $B_0\ge0$ giving its
source/frame/calibration and occurrence bindings. Implicit occurrence
positions and the fixed schedule are represented by their public program;
any explicitly supplied further labels are included in this string.
Lengths and integers have self-delimiting binary encodings. The input is
readable and is not overwritten. Its existing allocation and backing are
charged separately. The output tape is write-only and its allocation is
also separate. The metadata and its length are copied to the output so
that the matrix remains attached to the same binding; this copy does
not authenticate or regenerate the preparation service. Additional
workspace includes the counters, matrices, best-candidate description,
integer arithmetic scratch, finite control and numerical head/address
cursors. It does not include the retained input or emitted output.

For an explicit matrix encoding, prefix $b$ by the Elias gamma code of
$b+1$: if $k$ has binary length $a$, its gamma code is $a-1$ zeros
followed by the $a$ binary digits, of length $2a-1$. Then write $D_X$
in $2b+6$ bits, and each of the twenty-five independent real numerators
in one sign bit and $2b+4$ magnitude bits. The meanings of these fields
are fixed by Definition 15.2. A gamma code of $B_0+1$ followed by its
$B_0$ metadata bits supplies the separate binding copy. Leading zero
padding in the fixed-width fields is allowed.

**Theorem 15.5 (bit time, workspace and output of the specified scan).**
Let

$$
\begin{aligned}
n&=\lceil\log_2(N+1)\rceil,\qquad
\ell_0=\lceil\log_2(B_0+2)\rceil,\\
w&=b+n+\ell_0+64,\qquad
G_b=(2^{b+1}+1)^{50}-1.
\end{aligned}
\tag{15.15}
$$

The decoder has an implementation in Definition 15.4's bit model with
worst-case bounds

$$
\begin{aligned}
\text{bit time}&=O\bigl((B_0+155N+G_b+1)w^2\bigr),\\
\text{additional workspace}&=O(w)\text{ bits},\\
\text{matrix-description output}&\le60b+200\text{ bits},\\
\text{total output with copied binding}
 &\le B_0+2\ell_0+60b+210\text{ bits}.
\end{aligned}
\tag{15.16}
$$

The constants in the two $O$ bounds are absolute for one fixed machine
implementing this algorithm. They are independent of the source, its
rank or eigenvalues, the record, $N,b,B_0$, and its data errors.
The retained input occupies

$$
155N+B_0+O\bigl(n+\log(b+1)+\ell_0\bigr)\text{ bits},
\tag{15.17}
$$

in addition to the fixed program and its readable backing. Its size is
not included in the additional-workspace bound.

Proof. First verify that (15.5)--(15.6) require integer operations only.
At depth $j\le2$, the $(i,k)$ entry of $F^jU(v)F^j$ is
$i^jk^jv_{ik}/6^{2j}$. Every coefficient of its $K$ entries has
denominator dividing $6^{4j}$. The normalized diagonal and off-diagonal
$K$ entries multiply these coefficients by $1/2$ and $4/7$,
respectively. At depth zero the five normalized $b$ entries have
coefficients $4/5$ times the three oriented monomials in (13.3).
Consequently all fifty coefficient denominators divide $70\,6^8=C$.
This uses exactly the base $M_f$ of Definition 13.1, including at depths
one and two. Thus the fifty $P_\nu$ are explicit integer polynomials
with finitely many fixed coefficients. They can be formed once from
(13.2)--(13.3), without any data-dependent compilation.

Homogeneity gives
$Q_F(B_X)_\nu=P_\nu(V_X)/(CD_X^2)$. Multiplying the symmetric and
quadratic residuals in (15.4) by $E_X=2CND_X^2$ gives exactly
$\alpha_{ik}$ and $\beta_\nu$ in (15.6). The factor two on off-diagonal
squares is precisely the Frobenius norm of a symmetric matrix. This
proves $J_X=H_X/E_X^2$ and the integer cross-comparison rule. In
particular residual evaluation and selection have zero rounding error.

A single sequential pass through the padded record, decoding each
constant-length attempt and checking its grammar, obtains all fifty
$w_\nu$ and fifteen counts. Each is at most $N$ in absolute value;
$|s_{ik}|\le2N$. A fixed number of $O(n)$-bit registers and block
counters suffices. Updating even by a full binary scan costs $O(n+1)$
bit transitions per attempt. Streaming the metadata copy and parsing
its length need no buffer of length $B_0$. Binary length counters and
explicit input/output cursors fit in $O(w)$ bits. Allowing $O(w^2)$
transitions per input bit covers these operations, parsing, and the
initial construction of the $b+1$-bit integer $2^b$.

Enumerate the fifty bounded integers by an odometer, with fifty
$O(b+1)$-bit fields. Incrementing or carrying costs $O(b+1)$ per field,
and there are a fixed fifty fields. Termination is detected at their
maximum tuple; no list of candidates or counter of length $G_b$ is
stored. Skip the all-zero tuple by an integer zero test. Each other
iteration forms (15.3), evaluates the fixed quadratic polynomials,
forms (15.6), and compares one candidate with the stored best. The
number of integer additions and multiplications in this iteration is
bounded by an absolute constant because all matrix and panel dimensions
are fixed.

For completeness, the widths do not hide growth during that scan.
The bounds

$$
1\le D_X\le50\,2^{2b},\qquad
|U_{X,ik}|,|V_{X,ik}|\le10\,2^{2b}
\tag{15.18}
$$

follow by counting the fifty squares and the ten products per entry.
Thus these integers have $2b+O(1)$ bits. Each $P_\nu(V_X)$ has
$4b+O(1)$ bits. Each $E_X,\alpha_{ik},\beta_\nu$ has at most
$n+4b+O(1)$ bits; $H_X$ has at most $2n+8b+O(1)$ bits. The comparison
products have at most $4n+16b+O(1)$ bits. All constants here depend
only on the displayed fixed coefficients. Storing only the current
candidate, the best tuple and its score, the counts, and a fixed number
of arithmetic scratch registers therefore costs $O(w)$ bits. These
registers are overwritten at each iteration; expression evaluation is
of fixed depth.

On binary tapes, adding or comparing $q$-bit integers takes $O(q)$
transitions and $O(q)$ scratch space. School multiplication forms the
sum of at most $q$ shifted rows, each of length at most $2q$, giving
$O(q^2)$ transitions and $O(q)$ space; a tape scan between the fixed
number of registers adds at most the same order. Hence each candidate
costs $O(w^2)$ bit transitions and $O(w)$ additional space. There are
exactly $G_b$ nonzero candidates. Adding the input pass and final
matrix formation proves the first two lines of (15.16). Numerical
cursors, including addresses into the retained input and copied
metadata, have length $O(n+\ell_0+b+1)$ and are covered by this same
space bound.

By (15.18), the fixed-width output fields of Definition 15.4 fit. Their
length, including the gamma prefix for $b+1$, is

$$
(2\lfloor\log_2(b+1)\rfloor+1)
 +(2b+6)+25(2b+5)
 =52b+132+2\lfloor\log_2(b+1)\rfloor
 \le60b+200.
\tag{15.19}
$$

The metadata prefix and copy add at most $2\ell_0+1+B_0$ bits, which
is within (15.16). Writing these bits is included in the time bound.
The analogous input prefix lengths give (15.17). No retained copy of
the word, the grid or the metadata was charged as scratch. Conversely
(15.17) explicitly retains the original word and backing rather than
claiming that $O(w)$ bits suffice for the whole observer. $\square$

## 16. Finite-record confidence for the rational point output

**Theorem 16.1 (uniform confidence consequence for the original record).**
For every fixed lawful source, every positive integer $N$, every
integer $b\ge3$ and $0<\delta<1$, execute the original complete depth
schedule once and apply $\mathsf{Dec}_b$ to its record. Put

$$
L_\delta=\log(130/\delta),\qquad
\nu_{N,b,\delta}=24\sqrt{L_\delta/N}+512\,2^{-b}.
\tag{16.1}
$$

With probability at least $1-\delta$, the returned lawful rational
$(T,B)$ obeys

$$
\begin{aligned}
\|S-T\|_{\mathrm F}&\le\nu_{N,b,\delta},\\
d_\pm(A,B)&\le\sqrt{K_F\nu_{N,b,\delta}},\\
\mathfrak d(S+iA,T+iB)
 &\le\sqrt{\nu_{N,b,\delta}^2+2K_F\nu_{N,b,\delta}}.
\end{aligned}
\tag{16.2}
$$

The same constants work for every source in the original full domain.
Output remains lawful and the scan still terminates on the complementary
event. The confidence assertion neither removes improbable records nor
conditions on filter success.

Proof. Proposition 14.2 applies to exactly the extractions (15.1), with
no arithmetic tolerance: they are rational counts evaluated exactly.
Its one common event of probability at least $1-\delta$ gives

$$
e_Q=10\sqrt{L_\delta/N},\qquad
e_S=\sqrt{85/2}\sqrt{L_\delta/N}.
$$

Therefore $e\le\sqrt{285/2}\sqrt{L_\delta/N}
\le12\sqrt{L_\delta/N}$. Theorem 15.3 and monotonicity of its
nonnegative bounds give (16.2). Selection after reading the record
needs no candidate union bound, since Theorem 15.3 is deterministic
on this event. The independence and ranges needed for the reused
concentration are exactly the independent attempts of Assumption 6.2,
$Z_\nu\in[-1,1]$ including failures, and single indicators in $[0,1]$.
Hoeffding's Theorem 2, (2.6), applied also to the negatives, gives
$2e^{-Nt^2/2}$ and $2e^{-2Nt^2}$ for their two-sided tails; summing
at the radii of (14.6) over fifty plus fifteen settings gives $\delta$.
This use of the original bounded-variable theorem has no dependence
on its unresolved footnote exponent. $\square$

**Corollary 16.2 (integer precision prescription and the same-run bill).**
Write $K_F=40310784000$ and $A_*=2K_F+1=80621568001$. For arbitrary
integers $s\ge0$ and $d\ge1$, choose the source-independent integers

$$
b=47+2s,\qquad
N=2304(d+8)A_*^2\,2^{4s}.
\tag{16.3}
$$

The original acquisition followed by the decoder then returns a lawful
rational density with

$$
\Pr_\rho\!\left\{
 \mathfrak d(\rho,\mathsf{Dec}_b(W))\le2^{-s}\right\}
 \ge1-2^{-d}
\quad\text{for every fixed lawful }\rho.
\tag{16.4}
$$

There is no exact-real operation in this parameter prescription.
For this one run the acquisition charges remain

$$
\begin{array}{c|c}
\text{source preparations}&115N\\
\text{single-copy detector calls}&15N\\
\text{local filter calls}&60N+U_1\le90N\\
\text{joint detector calls}&20N+C_T\le50N\\
\text{retained padded outcome bits}&155N
\end{array}
\tag{16.5}
$$

The decoder adds one forward pass through these payload bits,
the metadata/header access and binding copy, and the bit time, workspace
and output of (15.16), which charge all bit reads and writes. It requests
no further source specimens or instruments. Storage of the complete
record, its actual readable backing
and the output remains additional to arithmetic workspace. The counts
$U_1,C_T$ are those of the same actual run, not expected counts or
counts from a successful replacement run.

Proof. Put $v=2^{-2s}/A_*\le1$ and $\delta=2^{-d}$. The elementary
inequalities $\exp(1)>2$ and $130<2^8$ give
$L_\delta=\log130+d\log2\le d+8$. Substitution of (16.3) gives

$$
24\sqrt{L_\delta/N}\le v/2.
$$

Also $A_*<2^{37}$, so
$2^b=2^{47+2s}\ge1024A_*2^{2s}=1024/v$ and
$512\,2^{-b}\le v/2$. Thus $\nu_{N,b,\delta}\le v$.
Since $v\le1$,

$$
v^2+2K_Fv\le(1+2K_F)v=A_*v=2^{-2s}.
$$

Theorem 16.1 proves (16.4). The integers (16.3) are obtained by binary
addition, multiplication by fixed integers and shifts. Their construction
uses $O((s+\log(d+1)+1)^2)$ bit time and
$O(s+\log(d+1)+1)$ scratch bits with school arithmetic; those costs
are contained in (15.16) for these $N,b$. The precision and confidence
integers are public inputs, not advice from a source oracle.

The row counts in (16.5) follow from the original schedule: fifty pairs
and fifteen singles per repetition, both first chains at depth two even
when the other fails, a second local call precisely on each first
success counted by $U_1$, and a terminal joint call precisely for each
filtered double success counted by $C_T$ in addition to the twenty
unfiltered configurations. The padding count is
$15N+20N+3(15N)+5(15N)=155N$. The extraction in (15.1) scans these
bits once and all later candidates use only the stored counts. This
proves the stated addition to, rather than substitution for, the
original same-run bill. $\square$

Theorems 15.3 and 15.5 supply the candidate-and-arithmetic conclusion
left separate in §14: a specified total finite search, positive
semidefinite trace-one rational output on every grammatical word, exact residual
comparisons, and proved bit time, extra workspace and output length.
Theorem 16.1 connects that specific point output to the actual complete
record's confidence event. Its analytic inverse ingredient is exactly
Theorem 13.4 and Proposition 14.1, with the original fifty normalized
means; its concentration ingredient is exactly Proposition 14.2.
The returned point need not belong to the confidence region (14.10)
with its original radii. Its guarantee is instead (15.9) and (16.2),
which include the paid finite-bank approximation. No nonemptiness test
for that region is invoked.

Attribution for these statements. Normalized Gram factorization,
finite nets, finite minimum search, binary school arithmetic and bounded
independent concentration are established methods. Wang--Xu,
[*Generalized phase retrieval*, Theorem 2.1](https://arxiv.org/html/1605.08034v3),
and Zhuang,
[*On stability of generalized phase retrieval and generalized affine
phase retrieval*, Theorem 2.3](https://doi.org/10.1186/s13660-019-1968-z),
are the general injectivity and product-distance suppliers already
specialized in §§13--14. Hoeffding,
[*Probability Inequalities for Sums of Bounded Random Variables*,
Theorem 2](https://doi.org/10.1080/01621459.1963.10500830),
is the concentration supplier. The contribution here is a
repository-derived construction for this particular record and lawful
image: the fixed integer polynomials with denominator $70\,6^8$,
normalized rational bank and exact score (15.6), all-source error and
finite execution bounds, and their common-record confidence consequence.
This does not claim a new general phase-retrieval principle, global
literature originality, optimal constants, or measured implementation
speed. The exhaustive bank's exponent fifty is an upper construction,
not a minimal dimension or complexity assertion.

The output's meaning is the approximate source orbit in (15.2).
Proposition 10.4's obstruction to exact finite recovery is unchanged.
No source-dependent quantum register survives this acquisition, and
$T+iB$ describes neither the actual realized past nor an actual joint
successor at a later cut. Section 11's requirements on a common source
representative, retained executed branch maps, full joint carriers and
current controller state still govern later use. In particular the
matrix description supplies neither state preparation nor an installed,
calibrated, authorized callable continuation. Its backing and arithmetic
resources must actually be supplied to execute the mathematical
machine. The confidence consequence assumes the ideal instruments and
stationary independence above. Changes in calibration or preparation
require separate probability bounds establishing (15.7); the deterministic
implication of Theorem 15.3 still applies whenever those inequalities
hold. Unreadable backing falls outside the execution model.

Section 12's separately supplied coherent-consumer event, its size
parameter and necessary acquisition budget retain their distinct task.
No uniform accuracy for that consumer over all sizes, joint-state
reconstruction, or efficient consumer evaluation follows from (16.4).
Likewise the native installation and four-view recovery obligations of
§11 remain separate. The independent preparation and measurement
interfaces here are not generated by the tree syntax or the integer
linear operation completeness of
[FARG §§1--4 and 19](FIBONACCI_ATOMIC_RELATION_GENERATION.md).
No full $\alpha/\beta$ generation, physical space/time identification,
or recovery of actual retained memory from a probability law is
licensed. The earlier fixed-$G_{gc}$, original-$Q$, parked-consumer,
unchanged-initialization, original-root late-target, $M_1(D)$ and
sharp-$\lambda$ questions keep their original scopes. These are
ordinary on-paper mathematical results, without a claim of Lean
verification or physical realization.

## 追加锚（本行以下为增补区）

## 17. Fixed real-filter drift for the original nominal decoder

**Definition 17.1 (unchanged detectors and fixed real drift).** Use the
lawful sources, fixed frame and orientation of Definition 6.1 and the
skew coordinates $a(A)$, map $U$ and norms of Definition 13.1. Write
$\beta(A)=b(A)=*_5(a_A\wedge a_A)$ for the five Hodge coordinates;
$K(A)=-A^2$. For any real contraction $H\in M_5(\mathbb R)$ set
$A_j^H=H^jA(H^j)^T$ and define $Q_H(A)\in\mathbb R^{50}$ by

$$
Q_H(A)=\left(
 \left(\frac{K(A)_{ik}}{M_{ik}}\right)_{i\le k},
 \left(\frac{\beta(A)_r}{5/2}\right)_{r=1}^5,
 \left(\frac{K(A_1^H)_{ik}}{M_{ik}}\right)_{i\le k},
 \left(\frac{K(A_2^H)_{ik}}{M_{ik}}\right)_{i\le k}
 \right),\qquad
M_{ii}=2,\quad M_{ik}=7/4\ (i<k).
\tag{17.1}
$$

Thus the depths are exactly $0,1,2$, with twenty coordinates at depth
zero and fifteen at each later depth. These are the base detector
normalizations of (10.1) and Definition 13.1, including at nonzero
depth. Put

$$
\mathsf B_H(u,v)=\tfrac14\{Q_H(U(u+v))-Q_H(U(u-v))\},\qquad
F=\operatorname{diag}(1,2,3,4,5)/6,
$$

$$
\gamma=c_F=\frac1{40310784000},\qquad
K_0=K_F=\gamma^{-1},\qquad
\mathcal C=\frac{16\sqrt{10}}7.
\tag{17.2}
$$

The nominal certificate is exactly Theorem 13.4:
$\|\mathsf B_F(u,v)\|_2\ge\gamma\|u\|_2\|v\|_2$.
The equivalent real quadratic coefficient matrices are those at the end
of §13, with dimension ten, fifty outputs and squared lower frame bound
$\gamma^2$. Their general nonsingular-polarization and product-distance
suppliers are Wang--Xu,
[*Generalized phase retrieval*, Theorem 2.1](https://arxiv.org/html/1605.08034v3),
and Zhuang,
[*On stability of generalized phase retrieval and generalized affine
phase retrieval*, Theorem 2.3, (2.3)](https://doi.org/10.1186/s13660-019-1968-z).

Fix $\eta\ge0$. Throughout every attempt and every depth of the actual
schedule, the success Kraus operator is one and the same real
contraction $\widetilde F$, with
$\|\widetilde F-F\|_{\mathrm{op}}\le\eta$; its failure Kraus operator
is $\widetilde L=(I-\widetilde F^T\widetilde F)^{1/2}$.
Preparations remain stationary independent copies of the fixed
$\rho=S+iA$, instruments have independent initial environments, and
the fifteen single-copy instruments and twenty base joint detector
designs remain those of Definition 10.1. The schedule and complete
record grammar remain those of Definitions 10.1 and 15.1. Both chains
are executed independently even if the other member fails; all failure
prefixes are retained, and the denominator of every mean is $N$, the
number of all attempts. No invertibility or strictly positive success
probability is imposed on $\widetilde F$. An all-success branch is used
only in its unnormalized form
$\widetilde F^j\rho(\widetilde F^j)^T$. A zero-probability branch has
zero mass and requires no conditional state.

The public number $\eta$ and this fixed-drift assumption are supplied
calibration premises. They include neither an estimator of the drift
nor an acquisition of its certified bound. The decoder is exactly
$\mathsf{Dec}_b$ of Definition 15.2, using the nominal $Q_F$ and its
fixed integer polynomials; it receives no matrix $\widetilde F$.

**Theorem 17.2 (radius and perturbation of this detector certificate).**
Every lawful $S+iA$ has $r_A=\|a(A)\|_2\le1/2$, and this radius is
attained by a pure source. For all real $u,v\in\mathbb R^{10}$, the
fixed-drift model satisfies

$$
\|\mathsf B_{\widetilde F}(u,v)-\mathsf B_F(u,v)\|_2
 \le\mathcal C\eta\|u\|_2\|v\|_2,
\tag{17.3}
$$

$$
\|\mathsf B_{\widetilde F}(u,v)\|_2
 \ge(\gamma-\mathcal C\eta)\|u\|_2\|v\|_2.
\tag{17.4}
$$

Consequently, if $\eta<\gamma/\mathcal C$, the actual map
$Q_{\widetilde F}$ is injective on all real skew matrices modulo one
common sign and obeys

$$
d_\pm(A,B)D_\pm(A,B)
 \le\frac{\|Q_{\widetilde F}(A)-Q_{\widetilde F}(B)\|_2}
 {\gamma-\mathcal C\eta}.
\tag{17.5}
$$

Here $d_\pm,D_\pm$ are exactly (14.1). The positive-radius hypothesis
in (17.5) is a sufficient condition for this actual-map certificate;
it is not a necessary calibration threshold.

Proof. Since $\rho$ and $\overline\rho$ are positive semidefinite,
$\operatorname{tr}(\rho\overline\rho)\ge0$ (write the trace as that
of $\rho^{1/2}\overline\rho\rho^{1/2}$). Also
$\operatorname{tr}\rho^2\le(\operatorname{tr}\rho)^2=1$.
Expanding the two traces gives

$$
2\|A\|_{\mathrm F}^2
 =\operatorname{tr}\rho^2-\operatorname{tr}(\rho\overline\rho)
 \le1,\qquad \|A\|_{\mathrm F}^2=2\|a(A)\|_2^2.
\tag{17.6}
$$

For $\psi=(e_1+ie_2)/\sqrt2$, the density $\psi\psi^\dagger$ has
$A_{12}=-1/2$ as its only nonzero upper skew entry, proving sharpness.

A real skew matrix has two nonnegative singular-value pairs and one
zero singular value. Thus
$\|U(u)\|_{\mathrm{op}}\le\|u\|_2$ and
$\|U(u)\|_{\mathrm F}=\sqrt2\|u\|_2$. The contraction-power
identity, valid without commutativity, is

$$
\widetilde F^j-F^j
 =\sum_{k=0}^{j-1}\widetilde F^{j-1-k}(\widetilde F-F)F^k,
\qquad \|\widetilde F^j-F^j\|_{\mathrm{op}}\le j\eta.
\tag{17.7}
$$

Write $A_j(u)=F^jU(u)(F^j)^T$ and
$\widetilde A_j(u)=\widetilde F^jU(u)(\widetilde F^j)^T$.
Splitting the difference into its left-factor and right-factor changes
and using contraction of both powers gives

$$
\begin{aligned}
\|\widetilde A_j(u)-A_j(u)\|_{\mathrm{op}}
 &\le2j\eta\|u\|_2,\\
\|\widetilde A_j(u)-A_j(u)\|_{\mathrm F}
 &\le2\sqrt2j\eta\|u\|_2.
\end{aligned}
\tag{17.8}
$$

The polarization of $K$ on skew matrices is
$\mathsf K(C,D)=-(CD+DC)/2$. Its depth-$j$ difference splits as

$$
\mathsf K(\widetilde A_j(u)-A_j(u),\widetilde A_j(v))
 +\mathsf K(A_j(u),\widetilde A_j(v)-A_j(v)).
$$

The inequalities $\|CD\|_{\mathrm F}\le
\|C\|_{\mathrm{op}}\|D\|_{\mathrm F}$ and their right-multiplication
versions bound each summand by
$2\sqrt2j\eta\|u\|_2\|v\|_2$. Hence their sum has Frobenius norm
at most $4\sqrt2j\eta\|u\|_2\|v\|_2$.
Upper-triangular coordinate norm is no greater than Frobenius norm,
and the largest inverse base $K$ divisor is $4/7$. All depth-zero
coordinates, including $\beta$, are unchanged. Combining just the
nonzero-depth blocks in Euclidean norm gives

$$
\tfrac47\,4\sqrt2\sqrt{1^2+2^2}
 =\frac{16\sqrt{10}}7=\mathcal C,
$$

which proves (17.3). The triangle inequality with Theorem 13.4 proves
(17.4). Finally
$Q_H(A)-Q_H(B)=\mathsf B_H(a(A)-a(B),a(A)+a(B))$ for every $H$.
Its two input norms have product $d_\pm D_\pm$. Dividing (17.4) by
its strictly positive coefficient proves (17.5), and equal outputs
then force $A=B$ or $A=-B$. The only invoked inverse result is the
existing nominal certificate; the perturbation calculation above
concerns the particular depth blocks (17.1). $\square$

**Theorem 17.3 (linear drift error for the same rational decoder).**
For every fixed lawful source, integer $N\ge1$, integer $b\ge3$,
$0<\delta<1$ and fixed drift as in Definition 17.1, execute the original
schedule once with the actual instrument and apply the nominal
$\mathsf{Dec}_b$. Its output $T+iB$ is lawful on every grammatical
record. With probability at least $1-\delta$, put

$$
E=24\sqrt{\frac{\log(130/\delta)}N}+512\,2^{-b},
\qquad r_A=\|a(A)\|_2.
\tag{17.9}
$$

The following inequalities hold simultaneously:

$$
\begin{aligned}
\|S-T\|_{\mathrm F}&\le E+2\mathcal C\eta r_A^2,\\
d_\pm(A,B)D_\pm(A,B)&\le K_0E+2K_0\mathcal C\eta r_A^2,\\
d_\pm(A,B)&\le\sqrt{K_0E}+2K_0\mathcal C\eta r_A,\\
\mathfrak d(S+iA,T+iB)
 &\le\sqrt{(E+2\mathcal C\eta r_A^2)^2
            +2(\sqrt{K_0E}+2K_0\mathcal C\eta r_A)^2}\\
 &\le\sqrt{(E+\mathcal C\eta/2)^2
            +2(\sqrt{K_0E}+K_0\mathcal C\eta)^2}.
\end{aligned}
\tag{17.10}
$$

No restriction $\eta<\gamma/\mathcal C$ is required in this theorem.
The bound includes $A=0$, singular sources and repeated spectra.
At fixed confidence its global error order is
$O(N^{-1/4}+2^{-b/2}+\eta)$, with constants depending on the fixed
certificate. It concerns the common-conjugation orbit metric (15.2),
not an actual state preparation or a callable continuation.

Proof. For each actual pair attempt the subnormalized all-success
input is $\tau=\widetilde F^j\rho(\widetilde F^j)^T$. Equation (10.2)
therefore gives $\mathbb E Z_\nu=Q_{\widetilde F}(A)_\nu$,
including when that branch has probability zero. Failure attempts have
$Z_\nu=0$. Single-copy means remain the fifteen probabilities of $S$.
Thus the bounded-independent-variable argument of Proposition 14.2
applies to these actual means, with the same fifty variables of range
length two and fifteen variables of range length one. In particular,
writing $s_N=\sqrt{\log(130/\delta)/N}$, the exact count extractions
(15.1) satisfy, on one event of probability at least $1-\delta$,

$$
\|y-Q_{\widetilde F}(A)\|_2\le10s_N,\qquad
\|\widehat S-S\|_{\mathrm F}\le\sqrt{85/2}\,s_N.
\tag{17.11}
$$

The concentration supplier is Hoeffding,
[*Probability Inequalities for Sums of Bounded Random Variables*,
Theorem 2, (2.6)](https://doi.org/10.1080/01621459.1963.10500830),
with the two-sided tails and $65$-setting union bound of (14.9).
No success-conditioned sample count is used.

Taking $u=v=a(A)$ in (17.3) gives
$\|Q_{\widetilde F}(A)-Q_F(A)\|_2\le\mathcal C\eta r_A^2$.
Consequently the same record has nominal joint error

$$
\begin{aligned}
e&=\left(\|\widehat S-S\|_{\mathrm F}^2
                 +\|y-Q_F(A)\|_2^2\right)^{1/2}\\
 &\le\sqrt{100+85/2}\,s_N+\mathcal C\eta r_A^2
 \le12s_N+\mathcal C\eta r_A^2.
\end{aligned}
\tag{17.12}
$$

Apply the deterministic Theorem 15.3 to the nominal decoder, using
$\nu=2e+512\,2^{-b}\le E+2\mathcal C\eta r_A^2$.
Its symmetric and product-distance conclusions are the first two lines
of (17.10). This application uses Theorem 13.4 for $Q_F$, not (17.5).
It therefore imposes no positive-radius condition on the actual map.

For the linear drift term set $a=a(A)$, $c=a(B)$, $d=d_\pm(A,B)$,
$D=D_\pm(A,B)$ and $t=\sqrt{K_0E}$. The parallelogram identity gives

$$
D^2\ge\tfrac12(\|a-c\|_2^2+\|a+c\|_2^2)
 =r_A^2+\|c\|_2^2,\qquad D\ge\max\{d,r_A\}.
\tag{17.13}
$$

If $D<t$, then $d<t$. If $D\ge t$ and $D>0$, division of the
product bound by $D$ gives

$$
d\le\frac{K_0E}{D}
       +\frac{2K_0\mathcal C\eta r_A^2}{D}
 \le t+2K_0\mathcal C\eta r_A.
\tag{17.14}
$$

For $D=0$ one has $d=r_A=0$, so the conclusion also holds.
Finally $\mathfrak d^2=\|S-T\|_{\mathrm F}^2+2d^2$ by (15.2),
and $r_A\le1/2$ by (17.6), proving the last two lines of (17.10).
Using (17.13) before coarsening the radius is essential: taking only a
square-root inverse of a source-independent mean bias would give a
weaker calibration term. $\square$

**Corollary 17.4 (complete resource contract of the drift consumer).**
In Theorem 17.3 take the classical bit model, readable input and
write-only output tapes, signed-binary arithmetic and self-delimiting
encodings of Definition 15.4. Let $B_0$ be the length of its metadata
string, including any explicitly represented source, frame, calibration
and occurrence labels. With the exact parameter correspondence

$$
n=\lceil\log_2(N+1)\rceil,\qquad
\ell_0=\lceil\log_2(B_0+2)\rceil,\qquad
w=b+n+\ell_0+64,\qquad
G_b=(2^{b+1}+1)^{50}-1,
\tag{17.15}
$$

the same actual acquisition and nominal scan have the bounds

$$
\begin{array}{c|c}
\text{setting attempts}&65N=15N+50N\\
\text{pair attempts}&50N\\
\text{source preparations}&115N\\
\text{single-copy detector calls}&15N\\
\text{local filter calls}&60N+U_1\le90N\\
\text{joint detector calls}&20N+C_T\le50N\\
\text{retained padded outcome bits}&155N
\end{array}
\tag{17.16}
$$

$$
\begin{aligned}
\text{nominal scan bit time}
 &=O((B_0+155N+G_b+1)w^2),\\
\text{additional arithmetic workspace}&=O(w)\text{ bits},\\
\text{matrix-description output}&\le60b+200\text{ bits},\\
\text{total output including binding copy}
 &\le B_0+2\ell_0+60b+210\text{ bits},\\
\text{separately retained input}
 &=155N+B_0+O(n+\log(b+1)+\ell_0)\text{ bits}.
\end{aligned}
\tag{17.17}
$$

The fixed program and its readable backing, allocation of input/output
and actual permissions remain separate resources. Metadata is copied,
not authenticated or reconstructed, by the scan. Descriptions and
calibration of the actual instruments and acquisition of a certified
$\eta$ are additional supplied resources. The rows do not convert
calls or bit transitions into elementary gates, physical time or energy.

Proof. Proposition 10.2's counting applies to the identical schedule
with the actual instrument: $U_1$ counts first successes among the
$30N$ individual specimens at depth two, and $C_T$ counts double
successes at the prescribed depth among the $30N$ filtered pairs.
There are $30N$ depth-one calls, $30N$ first depth-two calls and $U_1$
second calls. The $20N$ unfiltered pairs always use their detector;
the others do so exactly on the $C_T$ double successes. Two-bit
prefixes at depth two and one-bit flags at depth one give payload
$15N+20N+3(15N)+5(15N)=155N$. This includes all failures and the
padding for unexecuted detectors, with no free replacement.

For computation, the program is literally Definition 15.2. It extracts
(15.1) in one forward record pass, scans the $G_b$ nonzero Gaussian
integer matrices, and uses the integer polynomials with denominator
$C=70\,6^8$ and exact score cross-comparisons (15.5)--(15.6).
Neither these polynomials nor the bank are changed to depend on
$\widetilde F$. Hence Theorem 15.5 applies with exactly (17.15), on
every grammatical actual record. It supplies (17.17), counting all bit
reads and writes, odometer enumeration, score arithmetic, the stored
best candidate and the binding copy. In particular the bounds are
independent of $\eta$ and of the success counts. Input backing and
emitted output are excluded from its additional-workspace account,
exactly as in (15.16)--(15.17); the ordered record is retained even
though the scan subsequently uses just its counts.

For an explicit sufficient prescription take $0<h\le1$,
$0<\delta\le1/4$ and

$$
N\ge(768K_0)^2h^{-4}\log(130/\delta),\qquad
2^{-b}\le\frac{h^2}{16384K_0},\qquad
\eta\le\frac{h}{4K_0\mathcal C}.
$$

Then $E\le h^2/(16K_0)$, so (17.10) gives $d_\pm\le h/2$
and $\|S-T\|_{\mathrm F}\le3h/(16K_0)\le3h/16$.
Thus $\mathfrak d^2\le(9/256+1/2)h^2<h^2$. Taking the least
admissible integer $N$ and dyadic precision $b$ gives
$N=O(h^{-4}\log(1/\delta))$, $2^{-b}=O(h^2)$ and the sufficient
calibration order $\eta=O(h)$, since
$\log(130/\delta)=O(\log(1/\delta))$ uniformly for $\delta\le1/4$.
These are sufficient prescriptions for this certificate. The bank
exponent fifty and the displayed resource coordinates remain unchanged;
this proves neither efficient decoding nor a necessary calibration law
for other estimation or self-calibration procedures. $\square$

## 18. Adaptive terminal real-pair acquisition and precision-confidence order

**Definition 18.1 (experiment class and full classical history).** Fix
an integer $m\ge0$ and a stationary independent preparation service for an unknown lawful
$\rho\in\mathcal D(\mathbb C^5)$ in the frame of Definition 6.1.
A controller may select a finite-outcome POVM on one or two fresh copies
as a measurable function of all past classical observations and common
randomness. Each single-copy total effect on the unfiltered input is a
real symmetric positive matrix, summing to $I_5$; each pair total effect
is real symmetric positive, summing to $I_{25}$. This includes real
filtering followed by terminal measurement when every local prefix and
failure is recorded as part of the complete outcome. Source-dependent
postselection or advice is not supplied.

The controller seed, all common random draws used, settings, source-call
positions, both chain prefixes, detector outcomes, failures, decisions
to stop and any randomized output belong to the classical history.
Their initial law and all randomization rules are the same for all
sources. Any auxiliary starting state is source-independent, and its
induced input POVM must satisfy the preceding realness condition.
After each attempt all source registers, their successors and every
source-dependent quantum environment are discarded. No
source-dependent quantum system passes between attempts. Only classical
history informs later actions. Each run stops after a finite history;
there are at most $m$ pair attempts on every run. Arbitrarily many
single-copy insertions are allowed subject to this finite-history
condition. Pair budget is charged per attempted pair, including failures,
not per successful detector call or as an expected stopping time.

The optimization class grants mathematical choice of these finite real
POVMs and common classical processing. Their actual installation,
calibration, record backing and processing are additional operational
resources; class membership supplies no such implementation. The
original ideal depth protocol is a member, with $m=50N$ and the extra
resource contract (16.5), (15.16)--(15.17). The coherent $r$-copy
consumer of Definition 12.3 and experiments retaining source-dependent
quantum memory between attempts are outside this class.

**Theorem 18.2 (conditional real-pair information bound).** Let
$Y=iJ_{12}$, $\rho_\theta=I_5/5+\theta Y$, $0\le\theta\le1/10$,
and let $P_\theta$ be the complete classical-history law for any common
experiment of Definition 18.1. At each fixed history $h$ preceding a
pair, its conditional record law is $q_\theta K_h$, where $K_h$ is a
source-independent classical probability kernel and

$$
q_\theta(a,b)=\frac1{25}+\theta^2y_ay_b,
\qquad y=(1,-1,0,0,0),\quad 1\le a,b\le5.
\tag{18.1}
$$

The single-pair defect is $\chi^2(q_\theta\Vert q_0)=100\theta^4$.
For the complete stopped histories, with likelihood
$L_m=dP_\theta/dP_0$ after padding unused pair slots,

$$
\begin{aligned}
\mathbb E_0L_m^2
 =1+\chi^2(P_\theta\Vert P_0)&\le(1+100\theta^4)^m,\\
D_{\mathrm{KL}}(P_\theta\Vert P_0)
 &\le m\log(1+100\theta^4),\\
\operatorname{TV}(P_\theta,P_0)
 &\le\tfrac12\sqrt{(1+100\theta^4)^m-1}.
\end{aligned}
\tag{18.2}
$$

Here $\chi^2(P\Vert Q)=\int(dP/dQ-1)^2dQ$, logarithms are natural,
and total variation has the half-$L^1$ convention of Theorem 12.2.
The estimates include settings, failures, finite stopping, all common
randomness and any common randomized postprocessing.

Proof. The source eigenvalues $1/5\pm\theta,1/5,1/5,1/5$ are
strictly positive. Conditional on the same classical history (including
the controller seed), fresh inputs still have state
$\rho_\theta^{\otimes2}$. For a chosen complete real pair effect
$Q_{h,z}$, the odd term in this tensor square is purely imaginary
with skew transpose, so its trace pairing with $Q_{h,z}$ vanishes.
The exact supplier calculation (12.4)--(12.8) therefore applies at
this history:

$$
\operatorname{tr}(Q_{h,z}\rho_\theta^{\otimes2})
 =\operatorname{tr}(Q_{h,z}\sigma_\theta),\qquad
\sigma_\theta=I_{25}/25+\theta^2Y\otimes Y.
\tag{18.3}
$$

In a fixed eigenbasis $u_a$ of $Y$, set

$$
K_h(z\mid a,b)=
\langle u_a\otimes u_b,Q_{h,z}(u_a\otimes u_b)\rangle.
\tag{18.4}
$$

Positivity and completeness make this a probability kernel, giving
(18.1). It depends on the same supplied policy and the fixed history,
not on the unknown parameter. The labels $(a,b)$ are a mathematical
probability representation, not available outcomes or nonreal controls.
Directly,

$$
\chi^2(q_\theta\Vert q_0)
 =25\theta^4\sum_{a,b}y_a^2y_b^2=100\theta^4.
\tag{18.5}
$$

This is Theorem 12.2's existing defect, with its symmetric-binomial
correspondence $B=2$, $z=5\theta$ and both-active weight $4/25$.
The actual service has one fixed $\theta$ throughout: (18.3) does not
replace it by a fresh random choice of conjugation sign on each call.

Under $q_0K_h$, the observed likelihood factor $\ell_h$ is the
conditional expectation of the spectral likelihood
$R(a,b)=q_\theta(a,b)/q_0(a,b)$ given the output. Jensen gives

$$
\mathbb E_0(\ell_h\mid h)=1,\qquad
\mathbb E_0(\ell_h^2\mid h)\le1+100\theta^4.
\tag{18.6}
$$

These are the ordinary data-processing steps for order-two divergence;
see van Erven--Harremoës,
[*Rényi Divergence and Kullback--Leibler Divergence*,
Theorems 1 and 9, Example 2](https://arxiv.org/html/1206.2459v2).
Single-copy real effects have probability
$\operatorname{tr}(PI_5/5)$ and hence likelihood factor one.
The seed and subsequent random draws also have factor one conditional
on their past, and settings and stopping decisions use the same
classical policy at the same history.

To accommodate an unbounded but finite number of single-copy
insertions, group their full records and intervening common draws
into the block before the first pair, and then the block after each
pair until the next pair or stop. Conditional on the preceding history,
a block containing only these single-copy actions and common draws has
a source-independent law, even when its length is random: each finite
path has the same successive kernels, and the finite paths have total
mass one by the stopping assumption. The initial such block has a
common law. A later block consists of the current real pair followed
by a common classical kernel, and therefore still satisfies (18.6).
This accounts for every recorded single-copy action and every stop
decision, without assuming a uniform bound on their number.

After stopping, append a fixed, source-independent dummy symbol at
each remaining pair slot up to $m$. The stopped history is recovered
by deleting dummy slots, and the padding is determined by that history;
no information is lost or added. Let $\mathcal H_t$ include the seed
and the full first $t$ blocks, and $L_t$ their likelihood. Then

$$
L_t=L_{t-1}\ell_t,\qquad
\mathbb E_0(L_t^2\mid\mathcal H_{t-1})
 \le(1+100\theta^4)L_{t-1}^2.
\tag{18.7}
$$

Iterating $m$ times from $L_0=1$ proves the first line of (18.2).
All likelihood factors lie in $[3/4,5/4]$, since the spectral factors
do and $25\theta^2\le1/4$; dummy factors equal one. Thus the final
log likelihood is integrable, including with a continuous seed and
random finite block lengths. For one conditional block, Jensen also gives

$$
D(p_h\Vert p_{0,h})=\mathbb E_{p_h}\log\ell_h
 \le\log\mathbb E_{p_h}\ell_h
 =\log\mathbb E_{p_{0,h}}\ell_h^2
 \le\log(1+100\theta^4).
\tag{18.8}
$$

This is the order-one/order-two comparison in van Erven--Harremoës,
Theorem 3, with $D_2=\log(1+\chi^2)$.
The product identity for $L_m$ and conditional expectation give the
relative-entropy chain rule here as
$D(P_\theta\Vert P_0)=\sum_{t=1}^m
\mathbb E_\theta[D(p_{\mathcal H_{t-1}}\Vert
p_{0,\mathcal H_{t-1}})]$. Equation (18.8) proves its bound.
Finally Cauchy--Schwarz gives
$\operatorname{TV}=\tfrac12\mathbb E_0|L_m-1|
\le\tfrac12\sqrt{\mathbb E_0L_m^2-1}$.
The proof explicitly uses terminal discard: a surviving
source-dependent quantum carrier would not be part of the common
classical kernels just constructed. $\square$

**Proposition 18.3 (attainable information on this two-point family).**
For the family in Theorem 18.2, the one-pair chi-square bound is attained
by a three-outcome real projective measurement. Its one-pair relative
entropy is exactly

$$
\kappa(\theta)=\frac2{25}
 \{(1+a)\log(1+a)+(1-a)\log(1-a)\},\qquad a=25\theta^2,
\tag{18.9}
$$

which is also the maximum one-pair relative entropy over all allowed
real POVMs for comparison with $\theta=0$. Independent repetition of
this measurement $m$ times attains
$\mathbb E_0L_m^2=(1+100\theta^4)^m$ and
$D(P_\theta\Vert P_0)=m\kappa(\theta)$.
These are properties of the selected subfamily, not optimal constants
for estimating all lawful state orbits.

Proof. Put $Z=Y\otimes Y$ and $K=Y^2\otimes Y^2$. Both are real
symmetric, $Z^2=K$, $K^2=K$ and $KZ=Z$. Therefore

$$
Q_+=(K+Z)/2,\qquad Q_-=(K-Z)/2,\qquad Q_0=I-K
\tag{18.10}
$$

are mutually orthogonal real projections summing to $I_{25}$.
They have ranks $2,2,21$, and $Z$ acts as $+1,-1,0$ on their ranges.
The projection Kraus operators are real, so terminal measurement and
discard is a legal attempt of Definition 18.1. By (18.3) its
probabilities are

$$
p_\theta(+)=2/25+2\theta^2,\qquad
p_\theta(-)=2/25-2\theta^2,\qquad p_\theta(0)=21/25.
\tag{18.11}
$$

Thus $\chi^2(p_\theta\Vert p_0)
=2(2\theta^2)^2/(2/25)=100\theta^4$, and direct substitution gives
(18.9). The spectral likelihood (18.1) is constant on the three
sets $y_ay_b=1,-1,0$, so this aggregation preserves both divergences
of $q_\theta$ relative to $q_0$. Every other real POVM is a kernel
of that spectral law by (18.4), and data processing bounds its
relative entropy by the same value. Independent attempts multiply
second moments and add relative entropies, proving the asserted
repetition formulas. This exact calculation supplies no uniform
state-estimation risk constant or efficient all-state decoder. $\square$

**Theorem 18.4 (precision-confidence lower bound in this experiment class).**
Fix $0<h\le1/40$ and $0<\delta\le1/4$. If a common randomized
estimator in Definition 18.1 returns a density-orbit description within
$\mathfrak d$-distance $h$ with probability at least $1-\delta$ for
every lawful source, its uniform pair budget satisfies

$$
\begin{aligned}
m&\ge
\frac{\max\{\log(1+4(1-2\delta)^2),\ \log(1/(4\delta))\}}
 {\log(1+25600h^4)}\\
 &\ge\frac{\log(1/\delta)}{102400h^4}.
\end{aligned}
\tag{18.12}
$$

The conclusion already follows if success is required only for
$\rho_0$ and $\rho_{4h}$.

Proof. Set $\theta=4h\le1/10$. The two source orbits have distance
$\sqrt2\theta>2h$. The metric (15.2) is the quotient metric by the
isometric common-conjugation action; its triangle inequality follows
by composing the two sign choices and applying the Frobenius triangle
inequality. Hence the two closed $h$-balls are disjoint. A test that
selects $\rho_\theta$ when the estimate lies in its $h$-ball has
both errors at most $\delta$. The two-point testing supplier used
in Theorem 12.5 therefore gives
$\operatorname{TV}(P_\theta,P_0)\ge1-2\delta$, also for randomized
estimators with the seed included. Combining with (18.2) proves the
first numerator term in (18.12).

For the confidence dependence let
$\alpha=\int\sqrt{dP_\theta\,dP_0}$ be the affinity. Jensen under
$P_\theta$ gives

$$
\alpha=\mathbb E_\theta L_m^{-1/2}
 \ge\exp\{-D(P_\theta\Vert P_0)/2\}.
$$

For densities $p,q$ with respect to one dominating measure,
Cauchy--Schwarz on
$|p-q|=|\sqrt p-\sqrt q|(\sqrt p+\sqrt q)$ gives
$\operatorname{TV}\le\sqrt{1-\alpha^2}$. Thus any test has error
sum at least

$$
1-\operatorname{TV}\ge1-\sqrt{1-\alpha^2}
 \ge\alpha^2/2\ge\tfrac12e^{-D(P_\theta\Vert P_0)}.
\tag{18.13}
$$

These are classical affinity and testing inequalities, not additional
state-measurement assumptions. Equivalently the affinity step is
$D_{1/2}=-2\log\alpha\le D_1$, the order comparison in
van Erven--Harremoës, Theorem 3. Since the two errors sum to at most
$2\delta$, (18.13) and (18.2) yield
$m\log(1+100\theta^4)\ge\log(1/(4\delta))$.
Now $100(4h)^4=25600h^4$, proving the first line of (18.12).

Finally $\log(1+x)\le x$. If $1/16\le\delta\le1/4$, the first
numerator term is at least $\log2\ge\tfrac14\log(1/\delta)$.
If $0<\delta<1/16$, the second is at least
$\tfrac12\log(1/\delta)$. Division by $25600h^4$ proves the
uniform second line. Integer budgets obey the ceilings of these
bounds. $\square$

**Corollary 18.5 (matching pair-budget order, with its operational scope).**
Under ideal calibration and stationary independent preparations let
$m_*(h,\delta)$ be the minimum uniform pair budget among the
experiments of Definition 18.1 achieving $\mathfrak d$-error at most
$h$ and failure probability at most $\delta$ for every lawful source.
For $0<h\le1/40$, $0<\delta\le1/4$,

$$
m_*(h,\delta)=\Theta(h^{-4}\log(1/\delta)),
\tag{18.14}
$$

with constants independent of $h,\delta$. This is statistical
pair-budget optimality in this exact terminal-discard real experiment
class. The constants are not asserted optimal; neither are decoding
time, total storage or drift calibration optimized. No assertion about
a quantum-memory experiment class follows.

Proof. The lower bound is Theorem 18.4. For the upper bound use the
existing original fixed protocol and nominal rational decoder of
Corollary 16.2, with the precise correspondence

$$
s=\lceil\log_2(1/h)\rceil,\qquad
 d=\lceil\log_2(1/\delta)\rceil,\qquad A_*=2K_0+1,
$$

$$
b=47+2s,\qquad N=2304(d+8)A_*^2\,2^{4s},\qquad m=50N.
\tag{18.15}
$$

That supplier gives output error at most $2^{-s}\le h$ except with
probability $2^{-d}\le\delta$. Its fixed experiments are complete
real pair POVMs including failed chains, with no source-dependent
quantum carrier surviving attempts, and its $15N$ single-copy
observations are allowed insertions. Hence it belongs to exactly the
class optimized here. Since $2^s<2/h$ and
$d\le\log_2(1/\delta)+1$, one has

$$
50N<1843200 A_*^2h^{-4}
 \{\log_2(1/\delta)+9\}
 =O(h^{-4}\log(1/\delta))
$$

uniformly on the stated confidence range. Its full acquisition and
classical costs remain (16.5), (15.16)--(15.17), equivalently
(17.15)--(17.17) with ideal drift. In particular the exhaustive bank
is retained rather than replaced by an unproved efficient optimizer.
Nonreal effects, coherent access to more than two fresh copies in one
attempt, surviving source-dependent quantum memory, or new
source-dependent starting resources invalidate the conditional
reduction (18.3)--(18.7) and define a different optimization problem.
The separate all-size continuation and native acquisition interfaces
of §§11--12 retain their own contracts. $\square$

## 追加锚（本行以下为增补区）

## 19. Calibrated-filter classification: domain and intermediate ingredients

Let $E=\mathbb R^5$ have its fixed Euclidean metric and orientation.
For a real skew matrix $A$, write
$$
 a_A=\sum_{i<j}A_{ij}e_i\wedge e_j,\qquad
 K(A)=-A^2,\qquad b(A)=*_5(a_A\wedge a_A).
$$
Fix an invertible real $F$ with $F^TF\preceq I$. Set
$$
 A_j=F^jA(F^T)^j,\qquad G_j=(F^T)^jF^j,\qquad G=G_1.
$$
The datum at depth $d$ is precisely
$$
 (S,K(A),b(A),K(A_1),\ldots,K(A_d)).
$$
Its lawful domain consists of all real symmetric trace-one $S$ and real
skew $A$ with $S+iA\succeq0$. The target identifies $A$ with $-A$,
and makes no other identification. The number $n(F)$ is the least
successful depth, or infinity when there is no successful finite depth.

The proof uses the base-fiber classification in the proof of
Theorem 8.2, (8.6)–(8.7), and the quaternionic identities
(9.4)–(9.5) in the proof of Theorem 9.1, with the following correspondence.

* The only non-sign fiber of $(K,b)$ occurs at rank four with
  $K=\lambda^2P_W$. Its elements are the magnitude-$\lambda$
  orthogonal complex structures of one chirality on the same oriented
  four-plane $W$.
* In an oriented orthonormal basis of that four-plane their three
  coefficient matrices are
  $$
  I_1=J_{12}+J_{34},\quad I_2=J_{13}-J_{24},\quad
  I_3=J_{14}+J_{23}.
  $$
  They square to $-I_W$ and pairwise anticommute by (9.4).
* Rank zero, rank two and rank four with unequal positive squared
  singular values are already separated up to sign by $(K,b)$.
* Theorem 8.2, (8.12), supplies lawful depth-zero non-sign
  collisions. Theorem 9.1 supplies recovery through depth
  two for $F_0=\operatorname{diag}(1,2,3,4,5)/6$, on all real skew
  matrices and all lawful source supports.

The orthogonal-complex-structure/isotropic-subspace correspondence is
classical; see Salamon–Viaclovsky,
[Orthogonal complex structures on domains in $\mathbb R^4$,
Section 2.4, Propositions 2.1–2.2](https://arxiv.org/html/0704.3422v2).
Only its finite-dimensional linear algebra is used here.
The compression existence result used below is Fan–Pall,
[Imbedding Conditions for Hermitian and Normal Matrices, Theorem 1
and the real-symmetric observation at the end of Section 2](https://doi.org/10.4153/CJM-1957-036-1).
The explicit small-dimensional quadratic-form calculations appearing in
the classification are intermediate classical linear algebra.

The evaluated filter classification in Theorem 24.1 comprises spectral strata, finite transition structures, exact
depth values, all infinity cases, and lawful sharpness witnesses.
The classification explicitly constructs eigenspaces of the known
calibration, at most eight point vertices or four parametrized
families, Gram matrices of order three, at most sixteen exceptional
point vertices, and bounded finite matrix sums. It leaves no injectivity test, collision
quantifier, optimization over sources, or intersection with a
rank-constrained observation kernel to be resolved. Different finite
graphs define the remaining structural strata of $F$.

The formulas use ideal exact arithmetic, comparisons, square roots and
spectral decomposition, as do the exact-law inverses in Theorems 8.2 and 9.1. They make
no finite digital representation or finite-sample exactness promise.

All changes of basis below are calculations in the fixed frame. They
are neither additional controls nor additional identifications of
sources.

## 20. From collisions to isotropic-plane orbits

Put $E_{\mathbb C}=\mathbb C^5$, and use the complex bilinear form
$$
 B(x,y)=x^Ty,
$$
not the Hermitian form, to define isotropy. Complex conjugation always
refers to the fixed real frame. Let $\mathscr Q$ be the set of
two-dimensional complex subspaces $U\subset E_{\mathbb C}$ satisfying
$B|_{U\times U}=0$. Define
$$
 \mathscr S_G
 =\{U\in\mathscr Q:x^TGy=0\text{ for all }x,y\in U\}.
 \tag{20.1}
$$
This set will be explicitly eliminated in Sections 22–24.

**Lemma 20.1 (isotropic-orbit equivalence).**
For any integer $d\ge0$, a lawful common-$S$ non-sign collision
through depth $d$ exists if and only if there is $U\in\mathscr Q$
such that $F^jU\in\mathscr Q$ for $0\le j\le d$.
For $d\ge1$, this is equivalent to
$$
 U,FU,\ldots,F^{d-1}U\in\mathscr S_G.
 \tag{20.2}
$$
Whenever such a plane exists, there is a collision with the common
$S=I_5/5$ and both source states strictly positive.

Proof.
First, a plane $U\in\mathscr Q$ satisfies $U\cap\overline U=0$.
Indeed, if $z$ belongs to that intersection, both $z,\overline z$
belong to $U$, so $0=B(z,\overline z)=\|z\|^2$.
Choose a Hermitian orthonormal basis of $U$. Its real and imaginary
parts, multiplied by $\sqrt2$, give a real orthonormal four-frame
$f_1,f_2,f_3,f_4$ with
$$
 U=\operatorname{span}_{\mathbb C}
       \{f_1+if_2,\ f_3+if_4\}.
$$
To verify the orthogonality assertion, apply both bilinear isotropy
and Hermitian orthogonality to the two basis vectors: their sum and
difference give all four vanishing real cross inner products.

Write
$$
 \zeta=(f_1+if_2)\wedge(f_3+if_4)=a_X+i a_Y,
$$
so
$$
 X=J^f_{13}-J^f_{24},\qquad
 Y=J^f_{14}+J^f_{23}.
 \tag{20.3}
$$
These are two of the supplied quaternionic matrices. Consequently
$$
 X^2=Y^2=-P_W,\quad XY+YX=0,\quad
 a_X^2=a_Y^2=2f_{1234},\qquad W=\operatorname{span}_{\mathbb R}f_i.
 \tag{20.4}
$$
Here a square of a two-form means its exterior square.
The same conclusions, with a common positive magnitude, hold for
the real and imaginary parts of any nonzero simple two-form spanning
$\Lambda^2U$. In fact its scalar multiplier is some
$\alpha+i\beta$; the new real and imaginary parts are
$\alpha X-\beta Y,\ \beta X+\alpha Y$. Equation (20.4) proves equality
of their matrix squares and their exterior squares.

If $F^jU$ is isotropic, apply this observation to
$\Lambda^2(F^j)\zeta$. The real and imaginary skew matrices are
$F^jX(F^T)^j$ and $F^jY(F^T)^j$. Thus $A=\epsilon X$ and
$B=\epsilon Y$ have equal $K$ at every required depth and equal
base $b$, while $B\ne\pm A$. For $0<\epsilon<1/5$, the states
$I_5/5+i\epsilon X$ and $I_5/5+i\epsilon Y$ are strictly positive:
their eigenvalues are $1/5$, and $1/5\pm\epsilon$, each latter
value twice. This proves the forward construction on the original
lawful domain.

Conversely, take any non-sign collision $A,B$. The supplied
base-fiber classification gives $A=\lambda I(a)$,
$B=\lambda I(b)$ on one $W$, where $a,b\in\mathbb R^3$ are unit
and $c=a\cdot b$ satisfies $|c|<1$. Put
$$
 X=A,\qquad Y=(B-cA)/\sqrt{1-c^2}.
$$
Then $X,Y$ anticommute, have the same scalar square on $W$, and
have the same chirality. In a real orthonormal four-frame they have
the form $\lambda I_2,\lambda I_3$. This can also be checked without
a transitivity claim: for a unit $f_1\in W$, set
$$
 f_3=-Xf_1/\lambda,\quad f_4=-Yf_1/\lambda,\quad
 f_2=XYf_1/\lambda^2.
$$
The anticommutation identities give the required orthonormal frame
and the displayed matrices. Hence $a_X+i a_Y$ is simple and spans
an isotropic plane $U$.

Exterior square equality is transported by every real congruence:
$$
 a_{A_j}\wedge a_{A_j}
   =\Lambda^4(F^j)(a_A\wedge a_A).
$$
Thus $A_j,B_j$ have equal $b$ as well as their assumed equal $K$;
they remain non-sign because $F$ is invertible. They belong to
another repeated rank-four fiber. The coefficient inner product at
that fiber is still $c$, since
$$
 a_A\wedge a_B=c\,a_A\wedge a_A
$$
is transported by the same invertible $\Lambda^4(F^j)$.
It follows that $X_j=A_j$ and
$Y_j=(B_j-cA_j)/\sqrt{1-c^2}$ again have equal scalar squares and
anticommute. Therefore $\Lambda^2(F^j)(a_X+i a_Y)$ spans an
isotropic plane, necessarily $F^jU$.

Finally, $FU$ is isotropic precisely when
$B(Fx,Fy)=x^TGy$ vanishes on $U$. This proves (20.2). $\square$

**Lemma 20.2 (compression version and universal lower bound).**
For $U\in\mathscr Q$, let $W$ be the real four-plane whose
complexification is $U\oplus\overline U$, and let $J$ be the real
orthogonal complex structure on $W$ with $+i$-eigenspace $U$.
Then
$$
 U\in\mathscr S_G
 \quad\Longleftrightarrow\quad
 [P_WG|_W,J]=0.
 \tag{20.5}
$$
The set $\mathscr S_G$ is nonempty for every positive definite
real symmetric $G$. In particular $n(F)\ge2$ for every admissible
$F$.

Proof.
For a real symmetric $H=P_WG|_W$, vanishing of its complex bilinear
form on $U$ is equivalent to
$H(U)\subset U$, using the bilinear pairing between $U$ and
$\overline U$. Reality gives preservation of $\overline U$, too.
These two preservation statements are exactly commutation with $J$.

Order the eigenvalues of $G$, with multiplicity, as
$g_1\le\cdots\le g_5$. Fan–Pall's real-symmetric compression theorem
applies because
$$
 (g_2,g_2,g_4,g_4)
$$
interlaces $(g_1,\ldots,g_5)$. It supplies a real four-plane
compression with that spectrum. Choose an orthogonal complex
structure on each even-dimensional eigenspace of the compression.
It commutes with the compression, proving nonemptiness by (20.5).
Lemma 20.1 then supplies a lawful depth-one non-sign collision.
The depth-zero obstruction is (8.12).
$\square$

## 21. Explicit quadratic-form families and finite intersection rules

This section specifies all auxiliary operations used in the
classification. They involve known calibration subspaces only.

Let $H\subset E_{\mathbb C}$ be a four-dimensional hyperplane.

If $B|_H$ is nondegenerate, choose a Witt basis
$p_1,p_2,q_1,q_2$, with
$$
 B(p_i,p_j)=B(q_i,q_j)=0,\qquad B(p_i,q_j)=\delta_{ij}.
$$
Use the following two families of isotropic two-planes in $H$:
$$
\begin{split}
 C_{\mathrm e}(t)
 &=\operatorname{span}\{p_1+tq_2,\ p_2-tq_1\},
      &&t\in\mathbb C,\\
 C_{\mathrm e}(\infty)&=\operatorname{span}\{q_1,q_2\},\\
 C_{\mathrm o}([\alpha:\beta])
 &=\operatorname{span}
       \{\alpha p_1+\beta p_2,\ -\beta q_1+\alpha q_2\},
      &&[\alpha:\beta]\in\mathbb {CP}^1.
\end{split}
 \tag{21.1}
$$
If $B|_H$ has rank three, write its radical as $\mathbb Cr$;
choose $p,q,s$ in a complementary three-space with
$B(p,q)=B(s,s)=1$ and all other pairings zero.
Use the following family:
$$
 \begin{split}
 C(t)&=\operatorname{span}\{r,\ p+ts-t^2q/2\},
       &&t\in\mathbb C,\\
 C(\infty)&=\operatorname{span}\{r,q\}.
 \end{split}
 \tag{21.2}
$$
Such bases can be obtained by diagonalizing the nonsingular quotient
form by congruence and taking complex square roots; no existence oracle is needed.

Here is an evaluated rule for the only intersections needed later.
If $H'\ne H''$ are hyperplanes, put $M=H'\cap H''$, choose any
basis of this known three-space, and evaluate its $3$-by-$3$
Gram matrix for $B$. Its isotropic two-planes are exactly:
$$
\begin{array}{c|l}
 \operatorname{rank}(B|_M)&\text{complete list}\\ \hline
 3&\text{none},\\
 2& R\oplus L_1,\ R\oplus L_2,\\
 1& R.
\end{array}
 \tag{21.3}
$$
In the rank-two row $R=\operatorname{rad}(B|_M)$ has dimension one,
and $L_1,L_2$ lift the two null lines of the nondegenerate
two-dimensional quotient. These lines are obtained by factoring
one quadratic polynomial. In the rank-one row $R$ has dimension
two. Rank zero cannot occur.

To verify (21.3), pass to the nondegenerate quotient by the radical.
An isotropic subspace in a nondegenerate space is contained in its
orthogonal complement, so its dimension is at most half the ambient
dimension. This gives the three rows and forces containment of the
radical when needed. Rank zero would be a three-dimensional isotropic
subspace of the nondegenerate five-space, which is impossible.
Thus (21.3) produces actual finite lists, rather than leaving an
isotropic-subspace feasibility problem open.

## 22. Strata with all eigenvalue multiplicities at most two

Let the ordered eigenvalues of $G$ be $g_1,\ldots,g_5$, and put
$$
 \alpha=g_2,\qquad\beta=g_4.
$$
In this section $\alpha<\beta$. Let $T$ be the subset of
$\{\alpha,\beta\}$ consisting of simple eigenvalues of $G$.
Let $R$ be the set of simple eigenvalues not in $T$. Define
$$
 Q(z)=\prod_{t\in T}(z-t),\qquad
 P(z)=\prod_{r\in R}(z-r),\qquad
 w_r=\frac{Q(r)}{P'(r)}.
 \tag{22.1}
$$
Here $|R|=k\in\{1,2,3\}$, $|T|=k-1$. The values $w_r$ are
strictly positive and sum to one. Choose a real unit eigenvector
$v_r$ for each simple eigenvalue. List the real normal lines
$$
 \mathbb Rn,\qquad
 n=\sum_{r\in R}\epsilon_r\sqrt{w_r}\,v_r,\quad
 \epsilon_r\in\{1,-1\},
 \tag{22.2}
$$
counting a line only once. There are $2^{k-1}$ of them.

For each line let $W=n^\perp$ and form the known compression
$H=P_WG|_W$. Its $\alpha$- and $\beta$-eigenspaces are two-planes.
Choose real orthonormal bases $u_1,u_2$ and $v_1,v_2$ for these
two eigenspaces. List the four complex planes
$$
 U_{\epsilon,\delta}
 =\operatorname{span}_{\mathbb C}
      \{u_1+i\epsilon u_2,\ v_1+i\delta v_2\},
 \qquad \epsilon,\delta\in\{1,-1\}.
 \tag{22.3}
$$
Take conjugate pairs as vertices: $[U]=\{U,\overline U\}$.
There are exactly
$$
 N=2^k=
 \begin{cases}
 8&\text{multiplicities }1+1+1+1+1,\\
 4&\text{multiplicities }2+1+1+1,\\
 2&\text{multiplicities }2+2+1
 \end{cases}
 \tag{22.4}
$$
vertices.

Put an edge $[U]\longrightarrow[V]$ exactly when
$FU=V$ or $FU=\overline V$. This is a test of equality of
explicit two-planes. For example, it is evaluated by the vanishing
of the $3$-by-$3$ minors of their joined basis matrices.
Let $M$ be the resulting $N$-by-$N$ zero-one adjacency matrix.

**Proposition 22.1 (evaluated point stratum).**
If $M^N\ne0$, then $n(F)=\infty$.
Otherwise
$$
 n(F)=2+\max\{j:0\le j\le N-1,\ M^j\ne0\}.
 \tag{22.5}
$$
In particular the maximum finite answers in these three rows are
bounded by $9,5,3$, respectively. These bounds are not asserted to
be attained in every row.

Proof.
For an orthogonal complex structure $J$ on a real four-plane,
every real symmetric operator commuting with $J$ has even
eigenvalue multiplicities. Interlacing therefore forces the
compression eigenvalues to be $(\alpha,\alpha,\beta,\beta)$.
If an eigenspace of $G$ of multiplicity two had a nonzero
component of the normal $n$, the compressed eigenspace at that
eigenvalue would have dimension exactly one. Indeed
$(G-tI)x=c n$, projected to that eigenspace, forces $c=0$.
This is impossible for the paired compression. Thus $n$ is
orthogonal to every double eigenspace. The same argument makes
$n$ orthogonal to each simple eigenvector in $T$, since that
eigenvalue must have multiplicity two after compression.

Consequently $n$ is supported on the eigenlines in $R$.
The remaining compression has characteristic polynomial
$$
 \sum_{r\in R}n_r^2\prod_{\substack{s\in R\\s\ne r}}(z-s).
 \tag{22.6}
$$
This identity follows by the cofactor formula for compression to
$n^\perp$, or by the resolvent identity
$n^T(zI-G)^{-1}n=\sum_r n_r^2/(z-r)$.
It must equal $Q(z)$. Evaluation at $z=r$ gives (22.1).
The values in $R$ and $T$ strictly interlace, so each $w_r>0$;
the leading coefficient gives their sum as one.
Conversely those weights give exactly the required compression.
This proves (22.2), including all repeated-eigenvalue placements.

An orthogonal complex structure commuting with this compression
must restrict to a positive or negative quarter-turn on each of
its two real eigenspaces. These are exactly (22.3). Thus the list
is precisely $\mathscr S_G$, modulo conjugation, not a superset.

The graph has at most one outgoing and at most one incoming edge
at each vertex, because $F$ is real and invertible. Lemma 20.1
says that a collision through depth $d\ge1$ exists precisely when
an orbit occupies graph vertices for $d$ consecutive steps.
A directed cycle gives an orbit of arbitrary length and hence
infinity. A finite graph has a directed cycle if and only if
$M^N\ne0$. If there is no cycle, the largest number of occupied
vertices is $1+\max\{j:M^j\ne0\}$. The next depth is the first
successful depth, giving (22.5).

A starting vertex on a longest path supplies, by (20.3), a strictly
lawful non-sign witness at every smaller depth. This proves exact
minimality as well as sufficiency. $\square$

## 23. Strata with an eigenvalue of multiplicity at least three

The scalar case is set aside until Theorem 24.1.
Let $a$ be the eigenvalue of multiplicity at least three.

If the multiplicities are $4+1$, let $v$ span the other
eigenline and use the single complex hyperplane
$$
 H_1=\{x:v^Tx=0\}.
 \tag{23.1}
$$
If they are $3+2$ or $3+1+1$, choose a real orthonormal basis
$v,w$ for the other two-dimensional spectral space, with eigenvalues
$b,c$, allowing $b=c$. Choose complex square roots
$\rho^2=b-a$, $\sigma^2=c-a$, and put
$$
 H_\pm=\ker\ell_\pm,\qquad
 \ell_\pm(x)=\rho\,v^Tx\ \pm i\sigma\,w^Tx.
 \tag{23.2}
$$
Both coefficients are nonzero. Square-root choices only interchange
labels.

Use the complete families (21.1) or (21.2) in these hyperplanes.
Call the resulting disjoint families $C_1,\ldots,C_r$.
The full spectral table is
$$
\begin{array}{c|c|c|c}
 \text{multiplicities}&\text{hyperplanes}&
          \operatorname{rank}(B|_H)&r\\ \hline
 4+1&1&4&2\\
 3+2&2&3&2\\
 3+1+1&2&4&4.
\end{array}
 \tag{23.3}
$$
In the last row, all positions of the triple eigenvalue are included.
If $a$ is between $b,c$, the two hyperplanes in (23.2) are real
hyperplanes after multiplying their defining forms by scalars.
If $a$ is an extreme eigenvalue, they are a conjugate nonreal pair.
The construction and rules below apply to both.

The following finite construction eliminates all parameters of
these families.

1. **Whole-family transitions.** For $C_i$ spanning $H$, form
   $FH$. If this is one of the hyperplanes (23.1)–(23.2), the image
   $FC_i$ is exactly one family $C_j$. Put a whole-family edge
   $i\to j$. Identify $j$ by the image of any displayed parameter
   value and the membership rule proved below in Proposition 23.1.
   If $FH$ is not a listed hyperplane, put no whole-family edge.

2. **Finite exits which remain in the list.** For a family $C_i$
   with no whole-family edge, compute a finite set $B_i$ as follows.
   For each listed target hyperplane $H'$, form the known
   three-space $FH\cap H'$. Apply all rows of (21.3). Keep just the
   listed isotropic planes $V$ belonging to the known image family
   $FC_i$, and put $F^{-1}V$ in $B_i$.
   In a nondegenerate $FH$, this membership is tested by even
   intersection dimension with one known plane of $FC_i$.
   In a rank-three $FH$ there is just one family.
   Thus $B_i$ has at most four explicitly listed points.

Let $A$ be the $r$-by-$r$ adjacency matrix of whole-family edges.
If $A^r\ne0$, the answer is infinity. In the remaining rules assume
$A^r=0$, and evaluate
$$
 \ell=\sum_{j=0}^{r-1}A^j\mathbf 1.
 \tag{23.4}
$$
Thus $\ell_i$ is a positive integer. Follow the unique whole-family
chain from $i$ to its end $e(i)$, which has no whole-family edge.
Set
$$
 P_i=F^{-(\ell_i-1)}B_{e(i)}\subset C_i,\qquad
 P=\coprod_i P_i,\qquad N=|P|\le16.
 \tag{23.5}
$$
Every item of (23.5) is a known two-plane; the coproduct is disjoint.

If $N>0$, give $P$ the edges $p\to q$ exactly when $Fp=q$;
let $M$ be their $N$-by-$N$ adjacency matrix.
For every $p\in P$, $Fp$ belongs to exactly one listed family.
If $M^N\ne0$, the answer is infinity.
If $M^N=0$, define a vector $\tau$ indexed by $P$:
$$
 \tau_p=
 \begin{cases}
 1,&Fp\in P,\\
 1+\ell_i,&Fp\in C_i\setminus P_i.
 \end{cases}
 \qquad
 h=\sum_{j=0}^{N-1}M^j\tau .
 \tag{23.6}
$$
All matrix powers and sums in (23.4)–(23.6) have the displayed fixed
finite bounds. If $P$ is empty, omit $M,\tau,h$.

**Proposition 23.1 (evaluated family stratum).**
In the three spectral rows (23.3), the complete answer is:
$$
 n(F)=
 \begin{cases}
 \infty,&A^r\ne0,\\
 \infty,&A^r=0,\ N>0,\ M^N\ne0,\\
 1+\max_i\ell_i,&A^r=0,\ N=0,\\
 1+\max\{\max_i\ell_i,\ \max_{p\in P}h_p\},
    &A^r=0,\ N>0,\ M^N=0.
 \end{cases}
 \tag{23.7}
$$
Every finite value in (23.7) is the exact least depth.

Proof.
The family calculations used in this filter classification are as follows.
For the nondegenerate families (21.1), the primary antecedent is
Salamon–Viaclovsky,
[Orthogonal complex structures on domains in $\mathbb R^4$,
Section 2.4, Proposition 2.1](https://arxiv.org/html/0704.3422v2#S2.SS4).
With $p_i=dz_i/\sqrt2$ and $q_i=d\bar z_i/\sqrt2$, their oriented
family is $C_{\mathrm e}(-\xi_{12}/\xi_0)$, including infinity;
the form-preserving exchange $p_2\leftrightarrow q_2$ gives
$C_{\mathrm o}$.

The lists (21.1)–(21.2) are exhaustive and injectively parametrized.
Each family spans its ambient hyperplane. In the nondegenerate case,
two isotropic planes $V,V'$ belong to the same family if and only if
$\dim_{\mathbb C}(V\cap V')$ is even.
Every conformal isomorphism of these quadratic hyperplanes maps a whole
family bijectively to a whole family.

For (21.1), an isotropic two-plane transverse to
$Q=\operatorname{span}(q_1,q_2)$ is the graph of a skew
$2$-by-$2$ matrix, giving $C_{\mathrm e}(t)$.
A plane meeting $Q$ in dimension two is $Q$.
For intersection dimension one, orthogonality to that line forces
the projected line in $\operatorname{span}(p_1,p_2)$; the remaining
self-pairing removes the extra component modulo the line in $Q$.
This gives exactly $C_{\mathrm o}([\alpha:\beta])$.
The displayed bases show injectivity, show that distinct planes in
one family meet in dimension zero, and show that a plane from each
of the two families meets in dimension one.

For rank three, the nondegenerate quotient of $H$ by its radical
has dimension three and isotropic subspaces of dimension at most one.
Every isotropic two-plane therefore contains $r$, and its quotient
is a null line. In the basis $p,q,s$, all null lines are
$[1:-t^2/2:t]$, together with $[0:1:0]$. This is (21.2).
The explicit formulas show that each family spans $H$.
A conformal isomorphism preserves isotropy and intersection dimensions;
the preceding exhaustive lists then show that it sends each family
onto one of the target families.

For $4+1$, the equation $x^T(G-aI)x=0$ on an isotropic
two-plane forces that plane into (23.1).
For the other rows,
$$
 x^T(G-aI)x=\ell_+(x)\ell_-(x).
$$
A product of two linear forms vanishes identically on a complex
vector space only if one factor vanishes identically. Therefore
$$
 \mathscr S_G=\coprod_{i=1}^r C_i.
 \tag{23.8}
$$
The hyperplane (23.1) is nondegenerate. In (23.2), the square of its
normal is $b-c$; hence its rank is three precisely when $b=c$,
and otherwise four. The intersection $H_+\cap H_-$ is the
complexification of the real three-dimensional $a$-eigenspace.
It is nondegenerate and contains no isotropic two-plane. The two
lists of families are therefore disjoint. The preceding family
calculations prove the other assertions of (23.3) and (23.8).

For $x,y$ in any listed $H$,
$$
 B(Fx,Fy)=x^TGy=aB(x,y).
 \tag{23.9}
$$
Thus $F:H\to FH$ is a conformal isomorphism of quadratic
four-spaces; the rank of the restricted form is preserved.
It sends $C_i$ bijectively to a complete family in $FH$.
If $FH$ is a listed hyperplane this is exactly a whole-family
transition. Conversely every family spans its hyperplane, so an
equality $FC_i=C_j$ forces $FH$ to be the hyperplane of $C_j$.

If $FH$ is not listed, an image plane lying in a listed target
hyperplane must belong to the isotropic-plane list of
$FH\cap H'$. Rule (21.3) gives every such plane, and the explicit
family membership rule gives exactly those in $FC_i$.
Consequently $B_i$ is precisely
$$
 \{p\in C_i:Fp\in\mathscr S_G\},
 \tag{23.10}
$$
now as a computed list of at most four planes. There is no
positive-dimensional unprocessed intersection.

A cycle of whole-family edges gives an orbit remaining in (23.8)
forever, for any initial point of that cycle. It therefore gives
infinity by Lemma 20.1. Such a cycle exists exactly when $A^r\ne0$.

Assume there is no such cycle. The unique whole-family chain from
$C_i$ occupies exactly $\ell_i$ families, and its final map is
$F^{\ell_i-1}:C_i\to C_{e(i)}$, a bijection.
A point in $C_i\setminus P_i$ stays in $\mathscr S_G$ for exactly
$\ell_i$ consecutive positions before its next image leaves
$\mathscr S_G$. A point in $P_i$ passes that exit.
In particular, $Fp\in\mathscr S_G$ for every $p\in P$, as used
in (23.6). There are at most four points in each $P_i$, which
proves $N\le16$.

An infinite orbit must pass from exceptional point to exceptional
point: outside $P$ only its known finite whole-family tail
remains. Thus it is infinite exactly when the finite point graph
has a cycle, equivalently $M^N\ne0$.
When there is no cycle, let $h_p$ count the number of consecutive
positions in $\mathscr S_G$ starting at $p$. It satisfies
$$
 h_p=
 \begin{cases}
 1+h_{Fp},&Fp\in P,\\
 1+\ell_i,&Fp\in C_i\setminus P_i.
 \end{cases}
$$
This is $h=\tau+Mh$. Nilpotence gives exactly (23.6).
The largest possible number of positions in $\mathscr S_G$ is
therefore the maximum in (23.7). Lemma 20.1 says that the first
successful depth is one more than this number.

This maximum is attained, not just bounded. A point height is
attained at that explicit point. A generic height $\ell_i$ is
attained by a point of $C_i\setminus P_i$: at most four parameter
values are excluded, so one of the five finite parameter
values $0,1,2,3,4$ is available, using $[1:t]$ as the affine
parameter for $C_{\mathrm o}$. Applying (20.3) supplies strictly
positive common-$I_5/5$ witnesses at the last failing depth, and
therefore at all smaller depths. This proves exact minimality.
$\square$

## 24. Complete classification, exception strata and sharpness

**Theorem 24.1 (every-filter classification).**
For every real invertible contractive $5$-by-$5$ filter $F$,
form $G=F^TF$. Exactly one row of the following table applies:
$$
\begin{array}{c|l}
 \text{spectral multiplicities of }G&\text{value of }n(F)\\ \hline
 5&\infty\\
 4+1&\text{the evaluated formula (23.7), with }r=2\\
 3+2&\text{the evaluated formula (23.7), with }r=2\\
 3+1+1&\text{the evaluated formula (23.7), with }r=4\\
 2+2+1&\text{the evaluated formula (22.5), with }N=2\\
 2+1+1+1&\text{the evaluated formula (22.5), with }N=4\\
 1+1+1+1+1&\text{the evaluated formula (22.5), with }N=8.
\end{array}
 \tag{24.1}
$$
In the point rows, the infinity alternative is $M^N\ne0$.
In the family rows, both infinity alternatives in (23.7) apply.
Repeated eigenvalues in every possible spectral order, real and
nonreal hyperplanes, all Gram ranks in (21.3), empty exceptional sets,
and all directed-cycle and acyclic transition patterns are included.

The formulas define a finite structural stratification of the
calibration $F$: spectral multiplicities; equality or inequality
of the displayed known hyperplanes; ranks of the displayed
three-dimensional Gram forms; explicit plane membership and
equality; and finite zero-one transition matrices.
On each such stratum the formula assigns an integer or infinity
by bounded finite sums and maxima. No unknown source or detector
kernel is an input to this stratification.

For every finite answer $d=n(F)$, separation holds algebraically
for all real skew matrices and hence for all lawful common-$S$
pairs, including every singular support face. A strictly lawful
non-sign common-$I_5/5$ collision exists through depth $d-1$.
For every infinity answer, one strictly lawful non-sign
common-$I_5/5$ pair has equal data at all finite depths.

Proof.
The seven rows exhaust the partitions of five. In the scalar row,
$F=\sqrt c\,O$ with $O$ real orthogonal. Orthogonal congruence
transports the supplied base collisions without separating them;
equivalently every isotropic plane remains isotropic.
This is also the conformal case of Theorem 7.1.

For maximum multiplicity at most two, Proposition 22.1 evaluates
$\mathscr S_G$ and every orbit in it. For all remaining nonscalar
rows, Proposition 23.1 does so. Lemma 20.1 converts the resulting
finite heights and infinite orbits into precisely the required
collision and separation statements. Its necessity starts with
any possible non-sign collision, so no source rank or source
support is omitted.

In the infinity cases choose an explicit point on a point cycle,
or any displayed parameter value on a whole-family cycle.
Its infinite orbit supplies, by the fixed pair construction (20.3),
one pair working at all depths simultaneously. In the finite
cases use the maximizing points already specified in the
propositions. Scaling their two skews by any $0<\epsilon<1/5$
makes both source states strictly positive. These are exact
sharpness witnesses, not formal differences outside the lawful
domain. $\square$

**Corollary 24.2 (no larger finite-depth tail).**
Every finite $n(F)$ is at most fourteen.

Proof.
The linear operator $T:X\mapsto F^TXF$ acts on the
fifteen-dimensional real space of symmetric $5$-by-$5$ matrices,
and $G_j=T^jI$. Cayley–Hamilton puts every $G_j$ in the span of
$G_0,\ldots,G_{14}$. The depth-$j$ square data, after invertible
outer congruence, are $-AG_jA$. Equality through depth fourteen
therefore implies equality at every later depth.
Thus failure at depth fourteen is infinity; any finite least depth
is at most fourteen. This is an auxiliary nonsharp horizon, not
the classification or the method for evaluating the least depth.
$\square$

## 25. Explicit closed subcases and an actual nonnormal depth-three family

**Corollary 25.1 (complete real-normal subcase).**
Suppose $F$ is real normal. Let $m_1,\ldots,m_t$ be the
multiplicities of the distinct eigenvalues of $G=F^TF$.
Then
$$
 n(F)=
 \begin{cases}
 \infty,&\text{exactly one }m_i\text{ is odd},\\
 2,&\text{at least three }m_i\text{ are odd}.
 \end{cases}
 \tag{25.1}
$$
In particular $n(F_0)=2$ for the filter $F_0$ in (9.1).

Proof.
Normality gives $G_j=G^j$.
Suppose a non-sign collision survives through depth two.
The quaternionic argument (9.4)–(9.6) in the proof of
Theorem 9.1, or (20.5) applied to the corresponding pair, gives an
orthogonal complex structure $J$ on $W=n^\perp$ commuting with
$$
 H=P_WG|_W,\qquad H_2=P_WG^2|_W.
$$
With $v=P_WGn$, the compression identity (9.7) is
$H_2=H^2+vv^T$. Hence $J$ commutes with $vv^T$.
A nonzero rank-one symmetric operator cannot commute with an
orthogonal complex structure, since its range would be a
one-dimensional invariant real subspace. Thus $v=0$, so $n$
is an eigenvector of $G$.
The multiplicities of $G|_W$ must all be even. This happens
precisely when deleting one dimension from one eigenspace makes
all multiplicities even, that is, exactly one original
multiplicity is odd.

Conversely, when exactly one multiplicity is odd, choose $n$
in that eigenspace. Every eigenspace of $G|_W$ has even
dimension. Choose an orthogonal complex structure on each.
It commutes with all $G^j|_W$, giving one all-depth collision
by Lemma 20.1 and (20.5).
If there are at least three odd multiplicities no depth-two
collision exists, and Lemma 20.2 makes the least depth exactly two.
The Gram matrix $F_0^TF_0=F_0^2$ has five simple eigenvalues.
Its supplied upper bound is therefore sharp. $\square$

**Corollary 25.2 (closed $4+1$ subcase).**
Let $G=aI+(b-a)vv^T$, with $v$ unit, $a,b>0$, $a\ne b$.
Write the positive polar decomposition $F=OD$, $D=\sqrt G$.
Then
$$
 n(F)=
 \begin{cases}
 \infty,&O(\mathbb Rv)=\mathbb Rv,\\
 2,&O(\mathbb Rv)\ne\mathbb Rv.
 \end{cases}
 \tag{25.2}
$$

Proof.
In this case $\mathscr S_G$ consists of all isotropic two-planes
inside $H=v^\perp_{\mathbb C}$.
The map $D$ preserves $H$ and is scalar there, so $FH=OH$.
If $OH=H$, all points in those families remain in them forever.
Otherwise $H\cap OH$ is the complexification of a positive
definite real three-space. It has no isotropic two-plane, so no
point can remain in $\mathscr S_G$ for two consecutive positions.
Lemma 20.1 and the universal depth-one obstruction prove (25.2).
$\square$

**Proposition 25.3 (a nonnormal family with exact depth three).**
Choose $0<a,b\le1$, $a\ne b$.
Let $\pi=(1\ 4)(2\ 5\ 3)$, let $Oe_i=e_{\pi(i)}$, and put
$$
 F=O\,\operatorname{diag}(\sqrt a,\sqrt a,\sqrt a,\sqrt b,\sqrt b).
 \tag{25.3}
$$
Then $F$ is invertible, contractive and nonnormal, and $n(F)=3$.
For any $0<\epsilon<1/5$, the explicit lawful pair
$$
 S=I_5/5,\quad
 A=\epsilon(J_{14}-J_{25}),\qquad
 B=\epsilon(J_{15}+J_{24})
 \tag{25.4}
$$
has equal data through depth two and unequal data at depth three.

Proof.
The first three Gram matrices are
$$
\begin{split}
 G_1&=\operatorname{diag}(a,a,a,b,b),\\
 G_2&=abI+a(a-b)e_3e_3^T,\\
 G_3&=a^2bI+ab(b-a)e_4e_4^T.
\end{split}
 \tag{25.5}
$$
These follow by multiplying the weights along the displayed
permutation cycles.

Any collision through depth two supplies $W=n^\perp,J$ with
both compressed $G_1,G_2$ commuting with $J$.
The rank-one part of $G_2$ forces $P_We_3=0$, by the
rank-one argument in Corollary 25.1. Thus $W=e_3^\perp$.
On this $W$, $G_2$ is scalar and $G_1$ has the paired
eigenspaces $\operatorname{span}(e_1,e_2)$ and
$\operatorname{span}(e_4,e_5)$.
There are commuting orthogonal complex structures, so depth-two
collisions do exist.
The rank-one part of $G_3|_W$ is nonzero, and cannot commute
with any such complex structure. Hence no collision survives
through depth three.

For the stated pair, the four-plane is
$\operatorname{span}(e_1,e_2,e_4,e_5)$, and $A/\epsilon,B/\epsilon$
are $I_2,I_3$ in that four-frame. Their common
$b$ is $2\epsilon^2e_3$, their common $K$ is
$\epsilon^2P_W$, and (25.5) gives equal pulled-back square data
at depths one and two. At depth three the rank-one contribution
is proportional to $Ae_4(Ae_4)^T$ versus
$Be_4(Be_4)^T$, namely $\epsilon^2e_1e_1^T$ versus
$\epsilon^2e_2e_2^T$, and is unequal.
The states are strictly positive as in Lemma 20.1.
Finally $O$ moves spectral subspaces of the nonscalar diagonal
$D^2$, so $FF^T\ne F^TF$.
This proves all assertions. $\square$

**Proposition 25.4 (simple Gram spectrum does not imply finite recovery).**
The rational filter
$$
 F=\frac15
 \begin{pmatrix}
 1&0&0&0&1\\
 0&1&0&0&0\\
 0&0&2&0&1\\
 0&0&0&2&0\\
 0&0&0&0&3
 \end{pmatrix}
 \tag{25.6}
$$
is invertible and strictly contractive, its Gram matrix has five
distinct eigenvalues, and $n(F)=\infty$.
One all-depth lawful non-sign pair is
$$
 S=I_5/5,\quad A=\epsilon(J_{13}-J_{24}),\quad
 B=\epsilon(J_{14}+J_{23}),\qquad 0<\epsilon<1/5.
 \tag{25.7}
$$

Proof.
The squared Frobenius norm of the unscaled matrix is $21$;
hence $\|F\|_{\mathrm{op}}\le\sqrt{21}/5<1$.
Its determinant is nonzero. The vectors $e_2,e_4$ are eigenvectors
of $25F^TF$ with eigenvalues $1,4$. On
$\operatorname{span}(e_1,e_3,e_5)$ its matrix is
$$
 T=\begin{pmatrix}1&0&1\\0&4&2\\1&2&11\end{pmatrix}.
$$
This positive definite matrix has no eigenvalue $1$ or $4$.
Its other eigenvalues are the zeros of
$$
 11-z-\frac1{1-z}-\frac4{4-z}.
$$
This expression is strictly decreasing on each interval between
its poles. Its one-sided limits give exactly one zero in each
of $(-\infty,1),(1,4),(4,\infty)$; positive definiteness places
the first in $(0,1)$. Thus all five Gram eigenvalues are distinct.

The real four-plane $W=e_5^\perp$ is $F$-invariant, with
$F|_W=\operatorname{diag}(1,1,2,2)/5$.
Every nonzero entry of the two skews in (25.7) joins the first
two-plane to the second two-plane. Therefore
$$
 F^jA(F^T)^j=(2/25)^jA,\qquad
 F^jB(F^T)^j=(2/25)^jB
$$
for every $j\ge0$.
The supplied quaternionic identities give equal base $K,b$,
so these remain equal at every depth. The pair is strictly lawful
and non-sign. This proves infinity despite the simple Gram
spectrum. $\square$

## 26. Original instrument correspondence and source boundaries

**Proposition 26.1 (unchanged lawful detector contract).**
The classification of Theorem 24.1 is the classification for the
original all-success-prefix instruments and detectors, with no
extra controls or later $b$-measurements.

Proof.
The all-success branch has success probability
$$
 p_j=\operatorname{tr}(F^jS(F^T)^j)>0,
$$
and normalized imaginary part $A_j/p_j$. Invertibility of $F$
and trace one of $S\succeq0$, which follows from lawfulness,
give positivity of $p_j$, including
singular $S$. Homogeneity gives
$p_j^2K(A_j/p_j)=K(A_j)$.
The direct real two-copy detectors of Definition 10.1
therefore supply exactly these unnormalized square coordinates,
with their original base detector normalizations and visible
failure flags. The base detectors supply precisely $K(A),b(A)$.
Every branch flag probability depends on the common real part
only; the local chains have the same flag laws for a common-$S$
pair. Thus equality of these coordinates is precisely equality
of the stipulated detector laws on their lawful image.

All inverse matrices, eigenvectors, complex planes and graph
calculations in the proof are arithmetic on the known calibration
or exact laws. None is an additional experimental setting.
The completion failure operator remains
$(I-F^TF)^{1/2}$, actual failed preparations remain failures,
and no repeat-until-success replacement is made.
The result concerns exact laws and least successful-filter depth,
not almost-sure exact recovery from a finite record. $\square$

Proposition 10.2 and the depth column of (10.5) use the
filter $F_0$ in (9.1). Corollary 25.1 proves that the existing $F_0$
depth-two bound is its least possible depth for this detector
architecture. It does not alter the already supplied $115N$
preparations or $155N$ padded bits, and no cost saving or
sample/hardware optimality is asserted.

The following primary results are distinguished from the
classification above.

* Aldroubi–Krishtal–Tang,
  [Phaseless reconstruction from space-time samples,
  Proposition 3.1, Theorem 3.2 and Remark 3.5](https://arxiv.org/html/1706.05360v1),
  concern orbit-generated scalar magnitude measurements, penthouse
  local complementarity and, for sufficiency, iteration regularity.
  A scalar functional $|\langle F^jx,\phi\rangle|$ is not one of
  the present full square-matrix responses of a skew two-form.
  No implication from iteration regularity, or its failure, is
  used in Theorem 24.1.
* Wang–Xu,
  [Generalized phase retrieval: measurement number, matrix recovery
  and beyond, Theorems 2.1 and 4.1](https://arxiv.org/html/1605.08034v3),
  supply general real quadratic phase-retrieval criteria and generic
  measurement results. The skew coordinates do give quadratic
  measurements, but their criterion by itself is an unevaluated
  measurement-family criterion; their generic matrices are not this
  fixed all-prefix detector family. Those hypotheses do not evaluate
  the spectral and finite-transition structures above.
* Kech,
  [Dynamical Quantum Tomography, Theorems III.3 and IV.1](https://arxiv.org/html/1605.06786v2),
  assumes feasible unitary or feasible invertible simple-spectrum
  CPTP dynamics and concludes completeness for almost all POVMs
  satisfying dimension inequalities. The success branch here is
  generally trace-decreasing, and the detector family is fixed.
  These hypotheses and quantifiers do not supply Theorem 24.1.
* Fan–Pall supplies compression existence and interlacing, used
  exactly with the real spectra $g_1,\ldots,g_5$ and
  $(g_2,g_2,g_4,g_4)$. It does not supply the transition
  classification or least depths.
* Salamon–Viaclovsky supplies the classical finite-dimensional
  isotropic/orthogonal-complex-structure fiber correspondence.
  No integrability, global twistor realization or physical
  instrument-to-Hecke correspondence is assumed or proved here.

## 追加锚（本行以下为增补区）

## 等待读出递归续卷

**约定。** 固定来源及逐轮等待读出的边缘、完整历史与资源条件见 [同主题续卷 I 的等待读出递归 1](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY_CONTINUATION_I.md#等待读出递归-1-同一仪器的边缘稳定完整历史与持续变标)。

## 追加锚（本行以下为增补区）

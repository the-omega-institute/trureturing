# AURIC FIB 显式切换擦除时域

> 本卷是五窗口独立变参数遗忘的中文伴卷，采用普通 `generic-v1` 结构。完整全复输入 CPTP 类的每个非半参数实际词，在十四次完整更新后严格收缩；固定紧参数集另给一致的移动重置率。下文是可错、未执行的条件性符号数学，不是形式内核、测试、实验或独立批准。所有使用的有限端点、复相位及零分支均在正文内展开，文末保留空追加锚。

## 1. 实际模型与显式结论

**定义 1.1（完整逐字母类与允许操作）。** 保留空间为 $H=\mathbb C^5$，正交基 $e_0,\ldots,e_4$ 依次对应 $(000,100,010,001,101)$。对 $0<\eta<1$，记 $r=1-\eta$，置

$$
Q_\eta=\begin{pmatrix}
r&0&0&\eta&0\\
r&0&0&\eta&0\\
0&r&0&0&\eta\\
0&0&1&0&0\\
0&0&1&0&0
\end{pmatrix}.
\tag{1.1}
$$

行指标是输入，列指标是输出。$\mathcal L_\eta$ 包含所有复线性 CPTP 映射 $\Phi:M_5(\mathbb C)\to M_5(\mathbb C)$，其满足

$$
\operatorname{diag}\Phi(X)=Q_\eta^{\mathsf T}\operatorname{diag}X
\qquad\text{对每个复矩阵 }X.
\tag{1.2}
$$

特别包含所有有序非厄米矩阵单位，不能只检查五个基态。每个字母的环境向量须在该字母的一个共同环境内同时实现，不能独立拼接不相容的重叠。

实际调度事先指定，$\eta_j$ 可独立改变，$\Phi_j\in\mathcal L_{\eta_j}$。$\Phi_j$ 将时间 $j-1$ 送到时间 $j$，并记

$$
T_{b:a}=\Phi_b\circ\cdots\circ\Phi_a,\qquad
T_n=T_{n:1},\qquad T_0=\operatorname{id},\qquad r_j=1-\eta_j.
\tag{1.3}
$$

调度不依赖输入标签、测量结果或反馈。每步使用新鲜环境并立即丢弃，只保留一个 $H$；无环境、可访问分支、综合征、输入副本或输入相关历史的跨步保留，无途中恢复。有限外部参考只是不受作用的范数检验，不增加可用保留数据。对角规范和支持坐标只是证明表示。

**定义 1.2（迹系数与移动重置）。** 迹范数不除以二。置

$$
\begin{aligned}
\mathcal H_0&=\{Y=Y^\dagger:\operatorname{Tr}Y=0\},\\
\delta(T)&=\max_{Y\in\mathcal H_0,\ \|Y\|_1=1}\|T(Y)\|_1,\\
\mathcal R_\sigma(X)&=\sigma\operatorname{Tr}X,\\
\|L\|_\diamond&=\sup_{m\ge1,\ Z\ne0}
 \frac{\|(L\otimes\operatorname{id}_m)(Z)\|_1}{\|Z\|_1}.
\end{aligned}
\tag{1.4}
$$

$Z$ 是任意复矩阵。密度均指正、迹一矩阵。支持上的严格正性不等于全空间忠实性。

**定理 1.3（十四次完整更新的普遍严格时域）。** 对每个实际长度十四词，若每个 $\eta_j\in(0,1)\setminus\{1/2\}$，则

$$
\delta(T_{14})<1.
\tag{1.5}
$$

整数 $N_0=14$ 不依赖参数值、紧集、Gram、输入对或共同平稳密度；不要求两个见证轨迹人口相同。不声称十四最小。第 3 至 8 节给出完全有限证明。

**定理 1.4（紧集率与全复参考界）。** 对任意非空紧 $K\subset(0,1)\setminus\{1/2\}$，定义固定长度最大值

$$
q_K=\max_{\eta_j\in K,\ \Phi_j\in\mathcal L_{\eta_j}}
       \delta(\Phi_{14}\cdots\Phi_1).
\tag{1.6}
$$

则 $0<q_K<1$。每个实际词、每个连续子词、每个种子密度 $\tau$ 满足

$$
\begin{aligned}
\delta(T_{b:a})&\le q_K^{\lfloor(b-a+1)/14\rfloor},\\
\|T_n-\mathcal R_{T_n(\tau)}\|_\diamond
 &\le\min\{2,10q_K^{\lfloor n/14\rfloor}\}.
\end{aligned}
\tag{1.7}
$$

对任意有限参考及任意复 $Z$，第二式等价地给出

$$
\|(T_n\otimes\operatorname{id})(Z)
  -T_n(\tau)\otimes\operatorname{Tr}_H Z\|_1
\le\min\{2,10q_K^{\lfloor n/14\rfloor}\}\|Z\|_1.
\tag{1.8}
$$

实际重置密度随词、时间和种子改变。固定长度优化不是任意紧集表示上的有效算法；显式时域也不是整个非紧参数域上的统一正收缩间隙。第 9 至 11 节证明这些区别。

## 2. 全复合法性、共同环境与实际效应

**引理 2.1（八条边的精确接口）。** 内积对第一变量共轭线性。记 $z=e_2$。每个实际字母都有等距 dilation

$$
\begin{aligned}
Ve_i&=\sqrt r\,e_0\otimes\alpha_i
          +\sqrt\eta\,e_3\otimes\beta_i\quad(i=0,1),\\
Ve_2&=\sqrt r\,e_1\otimes\gamma_0
          +\sqrt\eta\,e_4\otimes\gamma_1,\\
Ve_3&=z\otimes\delta_0,\qquad Ve_4=z\otimes\delta_1,
\end{aligned}
\tag{2.1}
$$

其中八个向量在同一个环境内，均单位，且

$$
\alpha_0\perp\alpha_1,\qquad
\beta_0\perp\beta_1,\qquad
\delta_0\perp\delta_1.
\tag{2.2}
$$

除此以外只有共同 Gram 正性约束。反之每个这样的实际向量列都给出 $\mathcal L_\eta$ 中一个字母。最小环境维数等于 Choi 秩，在二至八之间。

证明。采用输出在前、未归一化的 Choi

$$
J=\sum_{ii'}\Phi(|e_i\rangle\langle e_{i'}|)
                      \otimes|e_i\rangle\langle e_{i'}|.
$$

全复条件 (1.2) 逐个固定所有同输出输入块：

$$
J\ge0,\qquad J_{jj}=\operatorname{diag}_i(Q_\eta)_{ij}.
\tag{2.3}
$$

块之和是 $I_5$，所以偏输出迹给 TP，$\operatorname{Tr}J=5$。正 Choi 的外积分解逆向量化给 Kraus；反向向量化 Kraus 给正 Choi。这是所需有限维 Choi–Stinespring 对应。

正矩阵满足 $|J_{ab}|^2\le J_{aa}J_{bb}$，所以零对角元消去整行整列，只剩 (2.1) 的八条正边。写 $Ve_i=\sum_j e_j\otimes e_{ji}$，则

$$
J_{(j,i),(k,l)}=\langle e_{kl},e_{ji}\rangle,
\qquad
\langle e_{ji'},e_{ji}\rangle=\delta_{ii'}Q_{ij}.
\tag{2.4}
$$

除去正权重即得单位向量和三个正交对。反之各列范数为一，异列的同输出内积被这些对消去，故 $V$ 等距；对全部有序矩阵单位作环境迹，正好得到 (1.2)。

更明确地，令

$$
\begin{aligned}
f&=(\alpha_0,\alpha_1,\beta_0,\beta_1,
       \gamma_0,\gamma_1,\delta_0,\delta_1),\\
\mathcal E&=((0,0),(0,1),(3,0),(3,1),(1,2),(4,2),(2,3),(2,4)),\\
w&=(\sqrt r,\sqrt r,\sqrt\eta,\sqrt\eta,
       \sqrt r,\sqrt\eta,1,1),\qquad G_{ab}=\langle f_a,f_b\rangle.
\end{aligned}
$$

活动 Choi 块为 $\operatorname{diag}(w)\overline G\operatorname{diag}(w)$，其条目是 $w_aw_bG_{ba}$，不是未经共轭的 Gram；规定零为一基下标 $G_{12}=G_{34}=G_{78}=0$。共同张成至多八维，正交对要求至少二维；权重全正，所以 Gram 秩与 Choi 秩相同。$\square$

**引理 2.2（人口、重置扇区与三步正效应）。** 置

$$
\mathsf A=\operatorname{span}\{e_0,e_1\},\quad
\mathsf D=\operatorname{span}\{e_3,e_4\},\quad
\mathsf L=\operatorname{span}\{e_0,e_1,e_2\},\quad
E_i=|e_i\rangle\langle e_i|.
$$

每个实际连续词在所有复矩阵上满足

$$
\operatorname{diag}T_{b:a}(X)
 =Q_{\eta_b}^{\mathsf T}\cdots Q_{\eta_a}^{\mathsf T}\operatorname{diag}X.
\tag{2.5}
$$

单步的完整效应是

$$
\begin{aligned}
\Phi_j^\dagger(E_0)&=r_jP_{\mathsf A},&
\Phi_j^\dagger(E_1)&=r_jE_2,&
\Phi_j^\dagger(E_2)&=P_{\mathsf D},\\
\Phi_j^\dagger(E_3)&=\eta_jP_{\mathsf A},&
\Phi_j^\dagger(E_4)&=\eta_jE_2.
\end{aligned}
\tag{2.6}
$$

$\Phi_j(X)=\operatorname{Tr}(X)E_2$ 对支持于 $\mathsf D$ 的复矩阵成立。三个按时间先后排列的实际字母还满足

$$
(\Phi_{j+2}\Phi_{j+1}\Phi_j)^\dagger(E_2)
 =\eta_{j+1}(r_jP_{\mathsf L}+P_{\mathsf D})>0.
\tag{2.7}
$$

证明。将 (1.2) 用于每个实际中间复矩阵即得迭代；迹配对得到五个效应。正输入支持于 $\mathsf D$ 时输出对角只可能在坐标二非零，正性消去其他行列，保迹确定系数；复线性张成给整个该扇区代数的式子。三步反向拉回依次为

$$
E_2\longmapsto P_{\mathsf D}
 \longmapsto\eta_{j+1}P_{\mathsf L}
 \longmapsto\eta_{j+1}(r_jP_{\mathsf L}+P_{\mathsf D}).
$$

最后一步用了 $\Phi_j^\dagger(P_{\mathsf L})=r_jP_{\mathsf L}+P_{\mathsf D}$。两个特征值 $\eta_{j+1}r_j$ 与 $\eta_{j+1}$ 均正。这是效应恒等式，不是 CP 重置下界。$\square$

## 3. 同一有限词上的实际正交对

**引理 3.1（有限取等见证）。** CPTP 的系数满足 $0\le\delta(T)\le1$，连续，且 $\delta(ST)\le\delta(S)\delta(T)$。另有

$$
\delta(T)=\tfrac12\max_{\rho,\sigma\text{ 密度}}
                   \|T(\rho)-T(\sigma)\|_1.
\tag{3.1}
$$

若一个实际长度 $N$ 词的系数为一，则有一对正交纯输入，其实际前缀输出 $\rho_t,\sigma_t$ 在每个端点 $0\le t\le N$ 都支持正交。

证明。厄米 Jordan 分解 $Y=Y_+-Y_-$ 和正保迹性给 $\|T(Y)\|_1\le\operatorname{Tr}Y_++\operatorname{Tr}Y_-=\|Y\|_1$。映射保持 $\mathcal H_0$，所以有次乘性；固定有限维空间的诱导范数连续。非零无迹厄米矩阵写为 $Y=s(\rho_+-\rho_-)$，$s=\|Y\|_1/2$，其中两个密度是归一化且正交的 Jordan 部分。这给 (3.1) 的一向；另一向用 $\|\rho-\sigma\|_1\le2$。相关球面和密度空间紧，最大值达到。

正矩阵 $A,B$ 满足 $\|A-B\|_1=\operatorname{Tr}A+\operatorname{Tr}B$ 当且仅当支持正交。为证必要性，取 $A-B$ 的正谱投影 $P$；迹范数等号强制 $\operatorname{Tr}(PA)=\operatorname{Tr}A$、$\operatorname{Tr}(PB)=0$，正性使两个支持分居 $P$ 和 $I-P$。充分性由正交直和直接得到。

系数一的最大化 Jordan 密度因此有正交输出。将两输入各自谱分解；正和的核是各正项核的交，故每个正权纯项的输出支持都包含于所属总输出支持。从两边各取一个纯项，得到输出正交的纯输入对。收缩性迫使输入距离也为二，所以它们正交。最终距离二，且所有前缀与后缀 CPTP 均收缩，每个中间距离只能同为二。全程只有这一个词和这两个实际递推轨迹，没有拼接最大化词。$\square$

**引理 3.2（分别四步正人口）。** 每个内部参数实际四步人口乘积的所有条目均严格正。因此上述轨迹在 $t\ge4$ 各有

$$
p_{t,i}=(\rho_t)_{ii}>0,\qquad
q_{t,i}=(\sigma_t)_{ii}>0\quad(0\le i\le4).
\tag{3.2}
$$

证明。共同图是合法三位窗口 $abc\to bcd$。任意起始窗口到目标合法窗口 $ijk$，依次追加 $(0,i,j,k)$，便是一条四步合法路径：第一个零与任意旧末位相容，之后的 $0i$ 相容，末两边由目标合法性保证。每条非强制边用该时刻自己的正参数或其正补数，强制边概率一，故这条实际路径权重正，矩阵条目也正。用最后四步作用于任一概率人口即得 (3.2)。$p_t$ 与 $q_t$ 始终分别传播，未令它们相等；这里不需要紧集、统一人口下界或无限中点抽取。$\square$

## 4. 秩谓词和两条纯轨迹的有限上限

**引理 4.1（支持运输与单向谓词）。** 若 $S=\operatorname{supp}\rho$、$S'=\operatorname{supp}\Phi(\rho)$，则每个实际 Kraus 都将 $S$ 送入 $S'$，即 $VS\subseteq S'\otimes\mathcal E$。在正人口端点区间，目标为纯态必使源为纯态；所以每条轨迹的“秩至少二”谓词分别只能由假变真。

证明。对 $y\perp S'$，

$$
0=\langle y,\Phi(\rho)y\rangle
  =\sum_\mu\|\rho^{1/2}K_\mu^\dagger y\|^2.
$$

每项为零，$\rho$ 在自己的支持上可逆，所以得到运输。若 $S'=\mathbb C\psi'$，则 $Vx=\psi'\otimes Wx$ 对 $x\in S$ 成立，$W$ 等距。坐标一给

$$
\sqrt r\,x_2\gamma_0=\psi'_1Wx.
\tag{4.1}
$$

$\psi'_1\ne0$ 由该目标自己的正人口保证。左侧线性映射秩至多一，右侧秩 $\dim S$，因此源亦为线。本结论不主张其他精确秩单调。$\square$

**引理 4.2（两纯块至多三个端点）。** 四个连续正人口端点不可能两条轨迹都纯。

证明。每步写 $V\psi=\psi'\otimes c$、$V\varphi=\varphi'\otimes d$，向量均单位。坐标一给 $c,d$ 都是该字母同一个 $\gamma_0$ 的相位倍数：对第一条用 $|\psi'_1|^2=r|\psi_2|^2$，对第二条独立用 $|\varphi'_1|^2=r|\varphi_2|^2$，分别保证比例模长一。这里没有共同人口假设。

吸收这两个相位到正交目标对，$V$ 在源二维平面上等于一个系统等距张量同一单位环境向量。因此通道在整个该二维复矩阵代数上是单个等距共轭，包含两个有序交叉项。三个实际限制合成为一个从初始二维平面到 $H$ 的等距 $U$。于是三步拉回 $E_2$ 的压缩应为 $U^\dagger E_2U$，秩至多一；但 (2.7) 在任何二维平面的压缩严格正、秩二，矛盾。不需要四端点以外的前驱或后继。$\square$

**引理 4.3（非终端总秩五的排除）。** 两个源正交支持若为 $2+3$ 或 $3+2$，且下一端点两个支持仍混，则不可能。

证明。源穷尽 $H$，运输给每个扇区的全输入交织

$$
VP_{S_a}=(P_{S'_a}\otimes I)V.
\tag{4.2}
$$

选二维源扇区，令 $z'_a=P_{S'_a}z$。其目标坐标二为正，故 $z'_a\ne0$。应用于 $e_3,e_4$ 得

$$
VP_{S_a}e_3=z'_a\otimes\delta_0,\qquad
VP_{S_a}e_4=z'_a\otimes\delta_1.
\tag{4.3}
$$

两像非零且正交，等距性使两个源投影独立并张成二维源。因此源扇区所有输出的系统部分均在 $\mathbb Cz'_a$，其实际目标只能秩一，与目标混矛盾。交换标签覆盖 $3+2$。该论证要求一个实际后继，不能排除区间最后一个端点的总秩五。$\square$

## 5. 两混块：全输入压缩与源参数迹矛盾

**引理 5.1（$2+2$ 步骤的 U/V 压缩）。** 一个正人口步骤若源和目标都为 $2+2$，其目标合支持 $R'$ 为四维，而且该通道的整个输入输出都压入 $R'$。对该步参数 $\eta$、$r=1-\eta$，恰有以下一种形态：

$$
\begin{aligned}
\mathrm U:\quad&R'=\operatorname{span}\{u',e_1,z,e_4\},
 &u'&=\sqrt r\,e_0+\omega\sqrt\eta\,e_3,\\
\mathrm V:\quad&R'=\operatorname{span}\{e_0,e_3,v',z\},
 &v'&=\sqrt r\,e_1+\omega\sqrt\eta\,e_4,
\end{aligned}
\qquad |\omega|=1.
\tag{5.1}
$$

U 型强制当前参数 $\eta=1/2$。

证明。取源合支持 $R$ 和目标合支持 $R'$ 的单位法向量 $\tau,\tau'$。支持运输给全输入环境值行

$$
(\langle\tau'|\otimes I)V=\xi\langle\tau|.
\tag{5.2}
$$

列三、四给 $\overline{\tau'_2}\delta_0=\overline{\tau_3}\xi$ 与 $\overline{\tau'_2}\delta_1=\overline{\tau_4}\xi$。正交 $\delta$ 强制 $\tau'_2=0$；若 $\xi\ne0$，则 $\tau_3=\tau_4=0$，所以 $\mathsf D\subset R$。交织 (4.2) 虽只在 $R$ 上有效，此时已能作用于 $e_3,e_4$；对任一二维扇区重复 (4.3)，用其自己的正目标坐标二，便强迫秩一目标，矛盾。因此 $\xi=0$，整个输入压入 $R'$。

剩余法向量方程为

$$
\begin{aligned}
\sqrt r\,\overline{\tau'_0}\alpha_i
 +\sqrt\eta\,\overline{\tau'_3}\beta_i&=0\quad(i=0,1),\\
\sqrt r\,\overline{\tau'_1}\gamma_0
 +\sqrt\eta\,\overline{\tau'_4}\gamma_1&=0.
\end{aligned}
\tag{5.3}
$$

每对系数一个非零必使另一非零，因权重正且向量单位。第一对非零时，对应 $\beta_i$ 与 $\alpha_i$ 有同一单位相位关系，将 $(0,3)$ 平面压成 $u'$；第二对将 $(1,4)$ 平面压成 $v'$。法向量单位且其指标二分量为零，至少有一对非零。两对都非零会使整个输出维数至多三，与实际两目标密度之和秩四矛盾。因此恰有一对；实际四维合支持就等于 (5.1) 显示的空间。

为排除非半参数 U，限制到任一源、目标二维扇区，得到 CPTP 映射 $F$。记 $F_j=P_SE_jP_S$、$F'_j=P_{S'}E_jP_{S'}$，所有所用效应非零由所属密度自身正人口保证。完整效应给

$$
F^\dagger(F'_1)=rF_2,\qquad F^\dagger(F'_4)=\eta F_2.
\tag{5.4}
$$

若目标两个投影向量独立，则 $F'_1+F'_4\ge\epsilon I_{S'}$ 对某 $\epsilon>0$ 成立。正且保持单位元的伴随使其像正定，但像为秩一 $F_2$，矛盾。因此两个非零效应比例，(5.4) 确定 $F'_1=(r/\eta)F'_4$。U 型中 $e_1,e_4\in R'$，对两个正交目标扇区求迹相加得

$$
\sum_a\|P_{S'_a}e_1\|^2
 =\frac r\eta\sum_a\|P_{S'_a}e_4\|^2,
\qquad 1=\frac r\eta.
$$

这是投影范数之和，不是两个密度人口的相等；故 $\eta=1/2$。这里只使用伴随保持单位元，未假设 Schrödinger 限制保持单位元。$\square$

**引理 5.2（两个连续 V 目标的不可能性）。** 非半参数下，三个连续端点都为 $2+2$ 不可能。

证明。对两个更新应用引理 5.1，两个目标都为 V。因此第二个更新有 V 源和 V 目标。写源为

$$
R=\operatorname{span}\{e_0,e_3,v,z\},\qquad
v=\sqrt{1-\theta}\,e_1+\nu\sqrt\theta\,e_4,
\quad |\nu|=1.
\tag{5.5}
$$

$\theta$ 是生成源的前一步参数，不是当前参数。目标对应线记为单位 $v'$。当前实际等距满足

$$
Vz=v'\otimes\gamma,\qquad Ve_3=z\otimes\delta_0,
\qquad \Phi^\dagger(|v'\rangle\langle v'|)=E_2.
\tag{5.6}
$$

第一式来自当前全输入 V 压缩，$\gamma$ 单位；最后一式因为只有输入列二含该输出线，且该列完全落在该线。

固定一个二维扇区，源、目标投影为 $P,P'$，置

$$
b=Pe_3,\quad c=Pz,\quad v_0=Pv,\quad
c'=P'z,\quad v'_0=P'v'.
$$

$e_3,z$ 的投影由本扇区正人口非零；$P_Re_1=\sqrt{1-\theta}\,v$ 及目标对应式使 $v_0,v'_0$ 非零。交织在 $R$ 上作用于 $e_3,z$，得

$$
Vb=c'\otimes\delta_0,\qquad Vc=v'_0\otimes\gamma,
\qquad \|b\|^2=\|c'\|^2,\quad \|c\|^2=\|v'_0\|^2>0.
\tag{5.7}
$$

扇区 CPTP 映射 $F$ 的完整压缩效应为

$$
F^\dagger(|v'_0\rangle\langle v'_0|)=|c\rangle\langle c|.
\tag{5.8}
$$

除以已证明相同的正平方范数，得到目标秩一投影 $P_1$ 被伴随送到源秩一投影 $Q_1$。密度 $F(Q_1)$ 对 $P_1$ 的期望为一，故等于 $P_1$；密度 $F(I-Q_1)$ 期望为零，二维目标使其等于 $I-P_1$。因此 $F(I)=I$，伴随 $F^\dagger$ 也保迹。本处先证等范数与二维性，不对任意秩一效应直接作此推断。

再压缩 $\Phi^\dagger(E_2)=E_3+E_4$。由源 V 结构，$PE_4P=\theta|v_0\rangle\langle v_0|$，相位在外积中消去，故

$$
F^\dagger(|c'\rangle\langle c'|)
 =|b\rangle\langle b|+\theta|v_0\rangle\langle v_0|.
\tag{5.9}
$$

求迹，用伴随保迹和 (5.7)，得 $\|c'\|^2=\|c'\|^2+\theta\|v_0\|^2$，与 $\theta>0$、$v_0\ne0$ 矛盾。两个密度的人口从未相等化。$\square$

**推论 5.3（两混块至多三个端点）。** 一个全为两混的连续正人口块，最多三个端点，其最后一个允许 $2+3$ 或 $3+2$。

证明。正交混支持在五维只能为 $2+2$、$2+3$ 或 $3+2$。引理 4.3 使每个有两混后继的源端点都必须 $2+2$。若块有四端点，其前三个源都有两混后继，故都为 $2+2$，引理 5.2 已矛盾。论证保留末端总秩五的可能性，没有向区间外索取一步。$\square$

## 6. 纯混块的有限移动几何

**引理 6.1（只用纯轨迹人口的分解）。** 在正人口端点块 $[a,b]$ 上，设一条轨迹纯、另一条混，且纯标签不变。记纯人口 $p_t$，伴侣人口 $q_t$ 和支持 $S_t$。可只作证明坐标选择使

$$
\psi_t=(\sqrt{p_{t,0}},\ldots,\sqrt{p_{t,4}})^{\mathsf T},
\qquad S_t\perp\psi_t.
\tag{6.1}
$$

对 $a\le t\le b$，置 $A_t=p_{t,0}+p_{t,1}$、$B_t=p_{t,2}$、$M_t=p_{t,3}+p_{t,4}$。对有块内前驱的 $a+1\le t\le b$，另置

$$
\alpha_t=\frac{p_{t,1}}{A_t}=\frac{p_{t,4}}{M_t}\in(0,1).
\tag{6.2}
$$

则 $M_t/A_t=\eta_t/r_t$。为免与块端点 $a$ 混淆，条件比例在本卷记为 $\alpha_t$。定义

$$
\begin{aligned}
h_A(x)&=\sqrt{1-x}\,e_0+\sqrt x\,e_1,&
l_A(x)&=\sqrt x\,e_0-\sqrt{1-x}\,e_1,\\
h_D(x)&=\sqrt{1-x}\,e_3+\sqrt x\,e_4,&
l_D(x)&=\sqrt x\,e_3-\sqrt{1-x}\,e_4,\\
u_y&=\sqrt{1-y}\,e_0+\sqrt y\,e_3,&
v_y&=\sqrt{1-y}\,e_1+\sqrt y\,e_4.
\end{aligned}
\tag{6.3}
$$

对 $a+1\le t\le b-1$ 的实际纯到纯步骤，$V_t$ 表示 $\Phi_{t+1}$ 的实际等距。有同一环境内单位 $c_t$ 和单位 $f_t,g_t,d_t\perp c_t$，使

$$
\begin{aligned}
\alpha_0&=\sqrt{1-\alpha_t}\,c_t+\sqrt{\alpha_t}\,f_t,&
\alpha_1&=\sqrt{\alpha_t}\,c_t-\sqrt{1-\alpha_t}\,f_t,\\
\beta_0&=\sqrt{1-\alpha_t}\,c_t+\sqrt{\alpha_t}\,g_t,&
\beta_1&=\sqrt{\alpha_t}\,c_t-\sqrt{1-\alpha_t}\,g_t,\\
\delta_0&=\sqrt{1-\alpha_t}\,c_t+\sqrt{\alpha_t}\,d_t,&
\delta_1&=\sqrt{\alpha_t}\,c_t-\sqrt{1-\alpha_t}\,d_t,\\
\gamma_0&=\gamma_1=c_t.
\end{aligned}
\tag{6.4}
$$

环境边向量左侧省略时间指标。对 $x_A=\langle l_A(\alpha_t),x\rangle$、$x_D=\langle l_D(\alpha_t),x\rangle$，有

$$
\begin{aligned}
K_t&=|u_{\eta_{t+1}}\rangle\langle h_A(\alpha_t)|
 +|v_{\eta_{t+1}}\rangle\langle z|
 +|z\rangle\langle h_D(\alpha_t)|,\\
W_tx&=x_A(\sqrt{r_{t+1}}e_0\otimes f_t
          +\sqrt{\eta_{t+1}}e_3\otimes g_t)+x_Dz\otimes d_t,\\
V_tx&=K_tx\otimes c_t+W_tx,\\
K_tS_t&\subseteq S_{t+1},\qquad
W_tS_t\subseteq S_{t+1}\otimes\mathcal E_t.
\end{aligned}
\tag{6.5}
$$

证明。正人口使原纯向量所有坐标非零；逐时刻取对角酉 $D_t$ 将其变成 (6.1)，并将通道表示变成

$$
\widetilde\Phi_{t+1}
 =\operatorname{Ad}_{D_{t+1}}\circ\Phi_{t+1}
                  \circ\operatorname{Ad}_{D_t^\dagger}.
$$

输入、输出对角不变，所以全复条件及参数不变，CPTP 性保持。任一有限乘积中的内部酉严格望远镜消去，只剩两端对角酉；秩、距离、正交不变。伴侣仍有自己不同的 $q_t$。这是坐标表示，未给物理调度增加免费相位操作。

纯人口实际递推为

$$
\begin{aligned}
p_{t,0}&=r_tA_{t-1},&p_{t,1}&=r_tB_{t-1},&p_{t,2}&=M_{t-1},\\
p_{t,3}&=\eta_tA_{t-1},&p_{t,4}&=\eta_tB_{t-1}.
\end{aligned}
\tag{6.6}
$$

前驱 $t-1$ 在块内。正性给 (6.2)，两个比例都等于 $B_{t-1}/(A_{t-1}+B_{t-1})$，质量比为 $\eta_t/r_t$。因而

$$
\psi_t=\sqrt{A_t}h_A(\alpha_t)+\sqrt{B_t}z+\sqrt{M_t}h_D(\alpha_t).
\tag{6.7}
$$

纯像给 $V_t\psi_t=\psi_{t+1}\otimes c_t$。坐标一、四的正幅度分别由 (6.6) 相等，除去后得两个 $\gamma$ 都为 $c_t$。坐标零、三、二分别给三对正交单位向量的同一个组合

$$
\sqrt{1-\alpha_t}\alpha_0+\sqrt{\alpha_t}\alpha_1=c_t,
$$

以及将 $\alpha$ 对换成 $\beta$ 对、$\delta$ 对的两式。每对的正交组合定义 $f_t,g_t,d_t$，均单位且正交于 $c_t$，反解得 (6.4)。没有规定三者间重叠。

代回等距即得 (6.5)。$K_t$ 的三条输入及三条输出各自正交归一，所以是初始空间 $H_+(\alpha_t)=\operatorname{span}\{h_A(\alpha_t),z,h_D(\alpha_t)\}$ 上的部分等距；实际人口关系使 $K_t\psi_t=\psi_{t+1}$、$K_t^\dagger\psi_{t+1}=\psi_t$。将实际支持运输分别投影到环境 $c_t$ 及其正交补，得到最后两个包含式。所有 $K_t$ 真正时变，未作 $K_tS_t\subseteq S_t$ 或固定谱的假设。$\square$

**引理 6.2（有前驱和后继的三个内部条件）。** 对每个 $a+1\le t\le b-1$，伴侣支持恰为二维，并满足

$$
S_t\subset R_t^V\cap\psi_t^\perp,\qquad
R_t^V=\operatorname{span}\{e_0,e_3,v_{\eta_t},z\}.
\tag{6.8}
$$

泛函 $x_A$ 在 $S_t$ 上不恒零。存在复数 $\zeta_t$，使

$$
\begin{aligned}
r_{t+1}f_t+\eta_{t+1}g_t&=\zeta_td_t,\quad |\zeta_t|\le1,\\
x_D&=-\sqrt{r_t/\eta_t}\,\zeta_tx_A\quad(x\in S_t),\\
L_t&=\sqrt{r_t}\,\zeta_t\langle l_A(\alpha_t)|
       +\sqrt{\eta_t}\langle l_D(\alpha_t)|,\qquad L_tS_t=0.
\end{aligned}
\tag{6.9}
$$

构造 $L_t$ 不要求伴侣目标 $S_{t+1}$ 为二维。

证明。前一步纯到纯，在正坐标规范下将坐标一、四分别写为 $\sqrt{r_t}\,\psi_{t-1,2}\gamma_0=\psi_{t,1}c$ 与 $\sqrt{\eta_t}\,\psi_{t-1,2}\gamma_1=\psi_{t,4}c$。实际人口律使两式的正标量因子分别相等，故 $\gamma_0=\gamma_1=c$。这对进入首个内部端点的 $a\to a+1$ 也成立，无须在 $a$ 定义条件比例或索取更早纯步骤。因此前一步整个输出在 $R_t^V$；伴侣与纯线正交，秩至多三。后一步将 $W_tS_t$ 的系统部分投影到 $\psi_{t+1}$，由 (6.6) 得实际环境值行

$$
\ell_t(x)=\sqrt{A_t}(r_{t+1}f_t+\eta_{t+1}g_t)x_A
                +\sqrt{M_t}d_tx_D=0\quad(x\in S_t).
\tag{6.10}
$$

该行亦消去 $\psi_t$，但

$$
\ell_t(e_3)=\sqrt{M_t}\sqrt{\alpha_t}\,d_t\ne0.
\tag{6.11}
$$

若 $S_t$ 三维，它与纯线便张成四维 $R_t^V$，使该行消去其中的 $e_3$，矛盾。混态性给下界二，所以秩恰二。

若 $x_A$ 在 $S_t$ 恒零，(6.10) 和非零单位 $d_t$ 使 $x_D$ 恒零，故 $S_t\subset H_+(\alpha_t)$。写 $x=Xh_A+Yz+Th_D$，属于 $R_t^V$ 等价于 $x_4=\sqrt{\eta_t/r_t}\,x_1$，因 $\alpha_t>0$，又等价于 $T=\sqrt{\eta_t/r_t}\,X$。因此

$$
H_+(\alpha_t)\cap R_t^V
=\operatorname{span}\{z,h_A(\alpha_t)+\sqrt{\eta_t/r_t}h_D(\alpha_t)\}.
\tag{6.12}
$$

这是包含非零 $\psi_t$ 的二维空间，与 $\psi_t^\perp$ 交只有一维，不能容纳二维 $S_t$。这先证了可选择 $x\in S_t$ 使 $x_A\ne0$。

对该选择在 (6.10) 定义 $\zeta_t=-\sqrt{M_t/A_t}\,x_D/x_A$，得到第一向量等式。代回所有 $x\in S_t$ 的行，利用 $M_t/A_t=\eta_t/r_t$ 得第二式。三角不等式给 $|\zeta_t|\le r_{t+1}+\eta_{t+1}=1$，再整理得消去行 $L_t$。系数是 $\zeta_t$ 本身，不能擅自共轭；没有除以 $\zeta_t$。后一步只需与纯目标正交，因此其伴侣目标可以秩三。$\square$

**引理 6.3（目标二维时的实际共线环境）。** 对 $a+1\le t\le b-2$，有单位复相位 $\beta_t$，使

$$
\begin{aligned}
g_t&=\beta_tf_t,\qquad
|\zeta_t|=|r_{t+1}+\eta_{t+1}\beta_t|,\\
w_t&=\sqrt{r_{t+1}}e_0+\sqrt{\eta_{t+1}}\beta_te_3
 -\sqrt{r_t/\eta_t}(r_{t+1}+\eta_{t+1}\beta_t)z
 \in S_{t+1}\setminus\{0\}.
\end{aligned}
\tag{6.13}
$$

若下一纯步骤存在，$K_{t+1}w_t\in S_{t+2}$。

证明。目标 $S_{t+1}$ 也是引理 6.2 的内部支持，所以二维。在 $W_t$ 中代入 (6.9)，对已证存在的非零 $x_A$ 除一次，实际运输给

$$
\begin{aligned}
F_t={}&\sqrt{r_{t+1}}e_0\otimes f_t
 +\sqrt{\eta_{t+1}}e_3\otimes g_t\\
 &-\sqrt{r_t/\eta_t}\,z\otimes(r_{t+1}f_t+\eta_{t+1}g_t)
 \in S_{t+1}\otimes\mathcal E_t.
\end{aligned}
\tag{6.14}
$$

若 $f_t,g_t$ 独立，取其张成空间上的两个对偶环境线性泛函，便得

$$
\sqrt{r_{t+1}}e_0-\sqrt{r_t/\eta_t}r_{t+1}z,
\qquad
\sqrt{\eta_{t+1}}e_3-\sqrt{r_t/\eta_t}\eta_{t+1}z
\tag{6.15}
$$

都在 $S_{t+1}$。它们独立，必张成整个二维支持，但坐标一、四都恒零，与伴侣自己的 $q_{t+1,1},q_{t+1,4}>0$ 矛盾。没有在此代入纯轨迹的人口。

所以单位环境向量必共线，$g_t=\beta_tf_t$。取 (6.9) 的范数即得模长等式，包括组合为零的分支；(6.14) 因式分解为 $w_t\otimes f_t$。$w_t$ 坐标零为 $\sqrt{r_{t+1}}>0$，故非零。下一实际部分等距的支持包含式给最后一句。没有除以 $r_{t+1}+\eta_{t+1}\beta_t$。$\square$

## 7. 五端点纯混矛盾及全部复零分支

**引理 7.1（纯混块至多四个端点）。** 若所有参数非半，五个连续正人口端点不可能保持同一条纯轨迹、另一条混轨迹。

证明。设端点为 $a,a+1,a+2,a+3,a+4$，置 $t=a+1$。引理 6.2 在 $t,t+1,t+2$ 给三个二维内部支持及 $L_t,L_{t+1},L_{t+2}$；引理 6.3 给 $\beta_t,w_t,\beta_{t+1},w_{t+1}$。步骤 $t+1\to t+2$ 另给 $K_{t+1}w_t\in S_{t+2}$。最后端点 $t+3=a+4$ 只用于 $L_{t+2}$ 所需的出边纯目标，其伴侣无需二维。

先将 $w_t$ 代入 $L_{t+1}$。两个消去坐标分别为

$$
\langle l_A(\alpha_{t+1}),w_t\rangle
 =\sqrt{\alpha_{t+1}r_{t+1}},\qquad
\langle l_D(\alpha_{t+1}),w_t\rangle
 =\sqrt{\alpha_{t+1}\eta_{t+1}}\beta_t.
$$

$z$ 项对两者均零，故

$$
0=\sqrt{\alpha_{t+1}}
   (r_{t+1}\zeta_{t+1}+\eta_{t+1}\beta_t),\qquad
\zeta_{t+1}=-\frac{\eta_{t+1}}{r_{t+1}}\beta_t.
\tag{7.1}
$$

除数正且 $|\zeta_{t+1}|\le1$，于是先得 $\eta_{t+1}\le1/2$；这由轨迹推出，未限制原参数集在同一侧。

简写

$$
b_0=\eta_{t+1},\quad s=1-b_0,\quad c=\eta_{t+2},\quad
R=\sqrt{r_t/\eta_t},\quad u=\alpha_{t+1},\quad v=\alpha_{t+2}.
\tag{7.2}
$$

$R>0$、$u,v\in(0,1)$。按三个实际输入坐标作用 $K_{t+1}$，完整向量为

$$
K_{t+1}w_t
 =\sqrt{(1-u)s}\,u_c
   -R(s+b_0\beta_t)v_c
   +\sqrt{(1-u)b_0}\,\beta_tz.
\tag{7.3}
$$

定义复数

$$
H_0=\sqrt{v(1-u)s}+\sqrt{1-v}\,R(s+b_0\beta_t).
\tag{7.4}
$$

由 $u_c,v_c$ 的坐标逐项得到

$$
\begin{aligned}
\langle l_A(v),K_{t+1}w_t\rangle
 &=\sqrt{1-c}\bigl(\sqrt{v(1-u)s}
           +\sqrt{1-v}R(s+b_0\beta_t)\bigr)=\sqrt{1-c}H_0,\\
\langle l_D(v),K_{t+1}w_t\rangle
 &=\sqrt c\bigl(\sqrt{v(1-u)s}
           +\sqrt{1-v}R(s+b_0\beta_t)\bigr)=\sqrt cH_0.
\end{aligned}
\tag{7.5}
$$

这里最后的 $z$ 项不贡献两条行。实际消去关系遂为

$$
0=L_{t+2}(K_{t+1}w_t)=((1-c)\zeta_{t+2}+c)H_0.
\tag{7.6}
$$

先前已证 $b_0\le1/2$，因此

$$
\operatorname{Re}(s+b_0\beta_t)\ge s-b_0\ge0,
\qquad \operatorname{Re}H_0\ge\sqrt{v(1-u)s}>0.
\tag{7.7}
$$

这先证 $H_0\ne0$，包括 $b_0=1/2,\beta_t=-1$ 的零组合分支。现在合法除以 $H_0$、$1-c>0$，得 $\zeta_{t+2}=-c/(1-c)$。

另将 $w_{t+1}$ 代入同一个 $L_{t+2}$，按 (7.1) 的两个坐标展开，得 $\zeta_{t+2}=-(c/(1-c))\beta_{t+1}$。因 $c>0$，比较得 $\beta_{t+1}=1$。引理 6.3 的模长关系在源时间 $t+1$ 使用下一参数 $c$，所以

$$
|\zeta_{t+1}|=|(1-c)+c\beta_{t+1}|=1.
\tag{7.8}
$$

而 (7.1) 给同一模长为 $b_0/s$，故 $b_0=s=1/2$，即 $\eta_{t+1}=1/2$，与假设矛盾。

所用除数只有事先证明非零的 $x_A$、正人口质量与参数因子、以及事先证明非零的 $H_0$；未除以 $\zeta$、$s+b_0\beta_t$、未证非零的支持向量个别坐标或环境重叠。任意单位复相位均已包含。较长纯混块包含这样一个五端点子块，故最多四端点。$\square$

**约定 7.2（有限端点的完整依赖）。** 下表明确每个矛盾实际消耗的源、目标和出边；表中端点全有各自正人口。

| 类型 | 被排除的端点段 | 所需实际依赖 | 可容许的末端情况 | 最大端点数 |
| --- | --- | --- | --- | --- |
| 两纯 | $a,\ldots,a+3$ | 三次实际纯到纯更新；各自人口关系使环境因子同相位线；三步正效应 | 无须区间外前驱或出边 | 三 |
| 纯混 | $a,\ldots,a+4$，$t=a+1$ | $a\to t$ 给入边 V 范围；$t,t+1,t+2$ 均有入边及出边，故二维且有消去行；$t+1,t+2$ 目标二维给 $\beta_t,\beta_{t+1}$；$t+1\to t+2$ 运送 $K_{t+1}w_t$ | $t+2\to a+4$ 只给最后消去行的纯目标；$S_{a+4}$ 可秩三；不需 $a$ 之前或 $a+4$ 之后的步骤 | 四 |
| 两混 | $a,\ldots,a+3$ | 三个源都有两混后继，排除源总秩五；前三个端点都是 $2+2$；前两次更新给 V 到 V 的迹矛盾 | 真实末端可为 $2+3$ 或 $3+2$，已计入 | 三 |

## 8. 十四时域的有限计数证明

**定理 8.1（非半参数的实际普遍时域）。** 定理 1.3 成立。

证明。反设某长度十四实际词 $\delta(T_{14})=1$。引理 3.1 给同一词上每个前缀支持正交的实际轨迹对；引理 3.2 分别给端点 $4,5,\ldots,14$ 的正人口。

在这段上，两条轨迹的秩至少二谓词分别非减，故端点按顺序至多分成两纯、纯混、两混三个连续块。块可为空，两谓词同时改变可跳过中块；若有中块，纯标签不能交换，因为已混的那条不能再变纯。未假设精确秩二、三、四单调。

引理 4.2、7.1、推论 5.3 分别给容量三、四、三端点，总共最多十端点；而 $4$ 至 $14$ 包含十一端点，矛盾。因 $\delta\le1$，即得 $\delta(T_{14})<1$。任何更长词可分出首十四步，后缀系数至多一，因此亦严格小于一；任意连续十四子词有相同结论。

整个证明没有紧集假设、人口相等化、无限中点提取、秩过极限或量子特征值统一间隙。四步正人口只是进入有限支持论证，不是四步量子收缩断言。$\square$

## 9. 固定长度优化、正下界与所有子词

**引理 9.1（紧致性使严格性成为紧集间隙）。** (1.6) 的最大值存在且小于一。

证明。联合字母空间

$$
\mathfrak F_K=\{(\eta,J):\eta\in K,\ J\ge0,
  \ J_{jj}=\operatorname{diag}_i(Q_\eta)_{ij}\}
\tag{9.1}
$$

在固定有限维空间中闭；每个正 $J$ 的迹均为五，所以有界，故紧。它包含该参数下所有实际完整通道，不要求跨时间辨认环境。长度十四的笛卡儿积紧，有限复合和 $\delta$ 连续，最大值达到。定理 8.1 对这个实际最大化词也严格，所以 $q_K<1$。这里仅用固定有限长度紧致性，未使用无限轨迹抽取。$\square$

**引理 9.2（每个实际词的严格正标量模式）。** 所有内部参数词，即使含半参数，均有

$$
\delta(T_n)\ge\prod_{j=1}^n\eta_j>0\qquad(n\ge1).
\tag{9.2}
$$

因此非空 $K$ 的 $q_K>0$。

证明。完整效应给 $\Phi_j^\dagger(P_{\mathsf D})=\eta_j(I-P_{\mathsf D})$。无迹输入的 $P_{\mathsf D}$ 期望每步乘 $-\eta_j$。取 $Y=E_3-E_0$，范数二且 $\operatorname{Tr}(P_{\mathsf D}Y)=1$，沿实际词归纳得

$$
\operatorname{Tr}(P_{\mathsf D}T_n(Y))=(-1)^n\prod_{j=1}^n\eta_j.
$$

无迹厄米 $Z$ 满足

$$
|\operatorname{Tr}(P_{\mathsf D}Z)|
=|\operatorname{Tr}((P_{\mathsf D}-I/2)Z)|\le\tfrac12\|Z\|_1.
$$

应用到 $T_n(Y)$ 后除以 $\|Y\|_1=2$ 即得 (9.2)。非空 $K$ 至少有合法词，例如任一参数的对角测量准备通道 $X\mapsto\sum_{ij}Q_{ij}X_{ii}E_j$，故最大值正。$\square$

**推论 9.3（十四分块）。** 对固定紧 $K$ 的每个实际连续子词，有 (1.7) 第一式，并且

$$
\|T_n(\rho)-T_n(\sigma)\|_1
\le q_K^{\lfloor n/14\rfloor}\|\rho-\sigma\|_1.
\tag{9.3}
$$

证明。按实际先后分成完整十四步块及不足十四的余块；每个整块系数至多 $q_K$，余块至多一，次乘性即得。连续子词仍由同一联合类组成；密度差在 $\mathcal H_0$，给第二式。没有通过分别最优的不同词拼出一个实际乘积。$\square$

## 10. 任意有限参考、任意复输入的移动重置

**引理 10.1（因子十和上限二）。** 对任意 CPTP $T$、种子密度 $\tau$ 与重置密度 $\sigma$，

$$
\delta(T)\le\|T-\mathcal R_\sigma\|_\diamond,
\qquad
\|T-\mathcal R_{T(\tau)}\|_\diamond\le\min\{2,10\delta(T)\}.
\tag{10.1}
$$

证明。重置消去所有 $\mathcal H_0$，所以第一式直接成立。令 $L=T-\mathcal R_{T(\tau)}$。对对角矩阵单位，$L(E_{ii})=T(E_{ii}-\tau)$，括号无迹厄米、范数至多二，故 $\|L(E_{ii})\|_1\le2\delta(T)$。对 $i\ne j$，

$$
E_{ij}=\frac{E_{ij}+E_{ji}}2+i\frac{E_{ij}-E_{ji}}{2i},
$$

两厄米项均无迹、范数一，故仍有 $\|L(E_{ij})\|_1\le2\delta(T)$。

对任意有限参考的任意复 $Z=\sum_{ij}E_{ij}\otimes Z_{ij}$，取完整复 SVD

$$
Z=\sum_\ell s_\ell|u_\ell\rangle\langle v_\ell|,
\qquad s_\ell\ge0,\quad\|u_\ell\|=\|v_\ell\|=1.
$$

按五个系统指标将单位奇异向量分块为 $u_{\ell i},v_{\ell j}$。秩一块的迹范数为两向量范数之积，所以三角不等式、两次 Cauchy–Schwarz 给

$$
\begin{aligned}
\sum_{ij}\|Z_{ij}\|_1
&\le\sum_\ell s_\ell
  \left(\sum_i\|u_{\ell i}\|\right)
  \left(\sum_j\|v_{\ell j}\|\right)\\
&\le5\sum_\ell s_\ell=5\|Z\|_1.
\end{aligned}
\tag{10.2}
$$

利用张量迹范数乘法性，再取三角不等式，

$$
\|(L\otimes\operatorname{id})(Z)\|_1
 \le\sum_{ij}\|L(E_{ij})\|_1\|Z_{ij}\|_1
 \le10\delta(T)\|Z\|_1.
\tag{10.3}
$$

常数无参考维数依赖，十未称最优。

为证明对任意复输入的上限二，在任意放大维数取 CPTP 通道的伴随 $\Theta$，它 unital 且 CP。将其二阶放大用于正块

$$
\begin{pmatrix}Y^\dagger Y&Y^\dagger\\Y&I\end{pmatrix},
$$

Schur 补给 $\Theta(Y)^\dagger\Theta(Y)\le\Theta(Y^\dagger Y)\le\|Y\|_\infty^2I$。因此放大伴随收缩算子范数；迹范数对偶使放大原通道对任意复矩阵完全收缩。两个通道的差 diamond 范数至多二；$\mathcal R_{T(\tau)}$ 是 CPTP，所以与 (10.3) 合取即得上界。

放大重置恰为 $T(\tau)\otimes\operatorname{Tr}_H Z$，保迹保证参考边缘不变，未从总迹为零误推出偏迹为零。代入推论 9.3 即得 (1.7)–(1.8)，完成定理 1.4。$\square$

## 11. 半参数、连续合法族及非紧间隙边界

**命题 11.1（完整合法的连续 $C_\eta$ 族）。** 令 $u_\eta,v_\eta$ 如 (6.3)，定义

$$
\begin{aligned}
A_0(\eta)&=|u_\eta\rangle\langle e_0|
  +\frac1{\sqrt2}|v_\eta\rangle\langle e_2|
  +|z\rangle\langle e_4|,\\
A_1(\eta)&=|u_\eta\rangle\langle e_1|
  +\frac1{\sqrt2}|v_\eta\rangle\langle e_2|
  +|z\rangle\langle e_3|,\\
C_\eta(X)&=\sum_{i=0}^1 A_i(\eta)XA_i(\eta)^\dagger.
\end{aligned}
\tag{11.1}
$$

则 $C_\eta\in\mathcal L_\eta$，随参数连续，最小环境维数二。

证明。$u_\eta,v_\eta,z$ 正交归一，所以

$$
A_0^\dagger A_0=E_0+E_2/2+E_4,\qquad
A_1^\dagger A_1=E_1+E_2/2+E_3,
$$

和为 $I$，给 CPTP。三个方向的计算基支持互不交叠，交叉外积对角全零；对每个复 $X$ 的输出对角为

$$
(r(X_{00}+X_{11}),\ rX_{22},\ X_{33}+X_{44},\
 \eta(X_{00}+X_{11}),\ \eta X_{22})^{\mathsf T},
\tag{11.2}
$$

正是 (1.2)。同一个二维环境的正交基 $f_0,f_1$ 给八向量列

$$
(f_0,f_1,f_0,f_1,(f_0+f_1)/\sqrt2,(f_0+f_1)/\sqrt2,f_1,f_0).
$$

所以所有复重叠同时合法、Gram 秩二，亦给最小环境维数。Kraus 对参数连续，因而通道及固定有限幂连续。$\square$

**命题 11.2（半参数的经典位与无普遍正间隙）。** 在 $\eta=1/2$ 存在合法通道永久保留正交经典位；对每个固定有限 $n$，

$$
\sup_{\eta\in(0,1)\setminus\{1/2\}}\delta(C_\eta^n)=1.
\tag{11.3}
$$

所以定理 1.3 的普遍严格性不能提升为整个开参数域的普遍正间隙。

证明。半参数时记 $u=u_{1/2}$、$v=v_{1/2}$、$R_0=\operatorname{span}\{u,v,z\}$，并置

$$
s_0=(u+v+z)/\sqrt3,\qquad
P=|s_0\rangle\langle s_0|,\qquad M=(P_{R_0}-P)/2.
\tag{11.4}
$$

它们正、迹一、支持正交。两个 Kraus 在 $R_0$ 上分别是 $1/\sqrt2$ 乘置换 $U_0,U_1$，其在有序基 $(u,v,z)$ 上作用为

$$
U_0(u,v,z)=(u,z,v),\qquad U_1(u,v,z)=(z,u,v).
$$

都固定 $s_0$ 并保持其正交补，所以 $C_{1/2}(P)=P$、$C_{1/2}(M)=M$。距离永远为二，末端测量 $\{P,I-P\}$ 可读出经典标签。这不宣称保留复量子位。

对每个先固定的有限 $n$，连续性给

$$
\|C_\eta^n(P)-C_\eta^n(M)\|_1\longrightarrow2
\qquad(\eta\to1/2).
\tag{11.5}
$$

由系数至多一及 (3.1) 得 (11.3)。对任意重置密度 $\sigma$，三角不等式又给

$$
\max\{\|C_\eta^n(P)-\sigma\|_1,
        \|C_\eta^n(M)-\sigma\|_1\}
 \ge\tfrac12\|C_\eta^n(P)-C_\eta^n(M)\|_1.
\tag{11.6}
$$

所以任何在半参数有聚点的参数集，即使排除半参数本身，所有合法常参数词到最佳重置的 diamond 误差之上确界，在每个有限 $n$ 仍至少一；不可能有统一趋零界。未交换时间与参数极限，也未否定单个离半参数通道的遗忘。

独立地，(9.2) 对常参数词给 $\delta\ge\eta^n$，固定 $n$ 时当 $\eta\to1$ 亦趋一。这是另一端点速率阻碍，未给接近零的非紧参数集分类。$\square$

**推论 11.3（紧参数集的尖锐二分）。** 对任意非空紧 $K\subset(0,1)$，全部实际允许词一致遗忘当且仅当 $1/2\notin K$。

证明。不含半参数时定理 1.4 的系数和移动重置上界趋零；若含半参数，则允许固定重复 $C_{1/2}$，由命题 11.2 保留距离二。量词允许只选 $K$ 中一个参数，不要求访问所有元素；因此不分类被强制交错使用半参数和非半参数的另一个调度合同。$\square$

## 12. 周期实际密度轨道与常数取得边界

**推论 12.1（周期调度的唯一吸引轨道）。** 对任何有限周期 $\ell$ 的非半参数实际调度，存在唯一周期密度轨道 $\sigma_j=\Phi_j(\sigma_{j-1})$、$\sigma_\ell=\sigma_0$，以其有限参数集 $K$ 使用同一个十四分块完全吸引界。基本周期可更小，不要求各相位有同一密度或人口。

证明。令 $F=\Phi_\ell\cdots\Phi_1$。任一种子轨道的 $m$ 项 Cesàro 均值 $\omega_m$ 有 $\|F(\omega_m)-\omega_m\|_1\le2/m$；密度空间紧，收敛子列给固定密度 $\sigma_0$。若两个固定密度不同，其差在 $F^m$ 下不变，但定理 1.4 将其范数界为 $q_K^{\lfloor m\ell/14\rfloor}$ 乘原范数，趋零，矛盾。逐相位定义便得唯一闭轨道；取种子 $\sigma_0$，实际 $T_n(\sigma_0)=\sigma_{n\bmod\ell}$，(1.8) 给任意复参考的相位吸引。

该轨道人口满足实际周期递推，并在每个相位严格正，因为可沿闭轨道先走足够整周期，再用最后四步。经典周期人口也唯一：令 $W$ 为一周期人口矩阵，取足够整数 $m$ 使 $m\ell\ge4$，则 $W^m$ 各条目严格正。取其最小条目 $\mu>0$ 和 $0<\epsilon<1$ 使 $\epsilon/5\le\mu$，写 $W^m=\epsilon U+(1-\epsilon)R$，$U$ 每行五点均匀、$R$ 行随机。零和行在其下严格收缩，两个固定周期人口之差只能零。周期相位只是公开控制，不增加保留时钟寄存器。$\square$

**约定 12.2（有效率仍需另求）。** $q_K$ 是长度固定十四的紧优化，未提供针对任意紧集描述的可认证计算算法、表示、成员判定、模数、精度或复杂度保证。即使给定

$$
\kappa=\min_{\eta\in K}\min\{\eta,1-\eta\}>0,\qquad
 d=\min_{\eta\in K}|\eta-1/2|>0,
$$

这里也未给 $q_K$ 的有效上界公式。精确支持矛盾不能替代近取等的定量分析，不允许假设非零量子特征值有统一正下界。时域长度固定为十四；有效间隙、最优长度、最优率和最优前因子仍未求得。

若另已取得可用且可认证的上界 $0<q_K<1$，对 $0<\epsilon<2$，

$$
n=14\left\lceil\frac{\log(10/\epsilon)}{-\log q_K}\right\rceil
\tag{12.1}
$$

次完整更新足以使显示的 diamond 界至多 $\epsilon$，因为其整块数使 $10q_K^{\lfloor n/14\rfloor}\le\epsilon$。这是取得常数之后的应用计数，不是取得常数的算法或总成本。

## 13. 来源、参数、许可和成本的逐项对应

**约定 13.1（来源归属与新增范围）。** 直接数学来源为给定的《AURIC FIB 五窗口一致切换遗忘》文本；其嵌入来源仅作为归属标识，不表示外部版本认证。一般工具和本模型的具体代数分别列出。

| 来源定位 | 本卷的精确对应与保留条件 |
| --- | --- |
| 给定主卷定义 1.1–1.2、引理 2.1–2.2 | 同一个 $H$、同一个全部有序复输入人口律；本卷第 2 节重建共同八向量、反序共轭 Choi、TP、实际三步正效应。每个字母只有自己的共同环境。 |
| 主卷引理 2.3 | 只取四位追加路径，分别证明 $p_t,q_t$ 正；普遍十四时域不用紧集 Doeblin 常数或人口合流。 |
| 主卷引理 3.1 与 3.2 | 复用有限取等见证的标准 Jordan 方法；不使用 3.2 的无限中点和共同人口轨迹。 |
| 主卷第 4–6 节 | 运输、两纯效应矛盾、总秩五、U/V 压缩与 V 迹代数的结构来源；本卷按各扇区自己的正人口证明非零，U 中求和是投影范数，V 中系数用前一步源参数。有限块显式保留末端例外。 |
| 主卷第 7–8 节 | 纯线的移动比例、环境行和两次消去求值的直接结构来源。本卷只用纯轨迹 $p_t$，其条件比例 $a_t$ 在本卷记作 $\alpha_t$；伴侣 $q_t$ 保持不同。五个有限端点替代无限尾部的前后步骤供应。 |
| 主卷第 9、11 节 | 正标量模式、复 SVD 放大、移动重置、周期轨道及连续 $C_\eta$ 族均复用其数学方法，并在本卷列全所需证明；隐式 $N_K$ 被有限秩块论证替换成十四，不作为证明前提。 |
| 标准 Choi–Stinespring 表示、支持正性及投影方法 | 只用本卷明列的正 Choi 分解、支持运输、二维投影到投影和等范数条件。不是一般秩一效应自动给双随机性。 |
| 标准 Dobrushin 系数、有限维紧致性、Cesàro 和 SVD | 用于系数次乘、固定十四优化、周期固定密度及任意复参考放大；不据为新工具。 |
| 主卷所列 QM、HG、固定参数稿及其参考文献 | 是所给文本的归属标识，不增加已读取来源。固定参数平稳人口、同质精确码或同质长度界均未用于本卷更强的变参数十四时域。 |

相对于给定主卷，本卷新增的结果是允许见证人口不同的有限阻塞、完整端点预算及显式普遍时域。模型、一般工具、连续半参数反例和支持代数的结构来源均已归属；这不是全球优先权或独立文献查新结论。主卷给出的标准文献标识包括 Choi 的 *Completely positive linear maps on complex matrices*，Stinespring 的 *Positive Functions on C*-Algebras*，Gaubert–Qu 的 *Dobrushin’s Ergodicity Coefficient for Markov Operators on Cones*，Szehr–Wolf 的 *Perturbation Bounds for Quantum Markov Processes and their Fixed Points*，以及 Burgarth 等的 *Ergodic and Mixing Quantum Channels in Finite Dimensions*；这里只使用并展开上述有限维数学内容。

**约定 13.2（每个数学对象的操作许可）。** 本卷的证明表示不额外授权物理步骤。

| 对象或步骤 | 数学用途与实际许可 |
| --- | --- |
| 每时刻 $D_t$ | 只使纯轨迹坐标正，内部相位在词表示中消去；不作为免费途中控制或恢复。 |
| $K_t,W_t,L_t$、支持投影、环境对偶泛函 | 只分析同一实际 dilation 和支持，不是额外可实施分支、筛选测量或条件通道。 |
| 实际共同 Gram | 一个字母八个环境向量联合可实现；不能用不同实现的最优重叠拼装字母。 |
| 两条见证轨迹 | 从同一有限词的系数一假设导出；两个标签选择后不改变词。 |
| 有限参考 | 只测试完全范数，不受作用，不可作为保留输入数据访问。 |
| 移动重置 | 用于比较范数的实际 $T_n(\tau)$；未要求实现额外重置，未假设共同平稳密度。 |
| 半参数经典读出 | 固定合法 $C_{1/2}$ 的末端两结果投影测量；没有途中读出。 |

**约定 13.3（更新、表示和控制分账）。** 以下计数不折算为未给出的物理或总价格。

| 项目 | 完整计数或准确边界 |
| --- | --- |
| 擦除时域 | 十四次完整允许更新。一般 $n$ 步有 $n$ 次新鲜环境相互作用并丢弃。 |
| 保留数据 | 始终一个 $\mathbb C^5$；没有额外输入副本、综合征、环境记录或输入相关历史。 |
| 单步环境 | 最小维数二至八，随字母变化；环境不跨步累计保留。 |
| 形式 Kraus 词 | 长度 $n$ 的形式展开至多 $8^n$ 项，不是可观察、可选择或保留的分支。 |
| 字母表示 | 完整 $8\times8$ 复 Hermitian Gram 或八边 Choi 块；完整 Choi 与超算子均 $25\times25$，系数作用在实维二十四的无迹厄米空间。 |
| 参数与控制 | 每个 $\eta_j$、实际字母及公开调度在标签前指定；有限参数集仍需程序选字母，无限调度可需无界公开描述。 |
| 实数和合成 | 未给任意实参数、Gram 的有限精确表示、硬件精确合成、控制误差或容错成本。 |
| $q_K$ | 一个固定十四因子优化；未运行优化，未给任意紧集上的求值或认证复杂度。 |
| 误差应用数 | (12.1) 以另已取得的可用 $q_K$ 为条件，只计算完整更新数，不计取得常数的代价。 |
| 参考范数 | 因子十独立于任意有限参考维数；不授权增加保留数据。 |

完整更新次数、矩阵尺寸和公共控制资源不是硬件门数、物理时间、本征窗口次数、全部计算、全程序价格或总存储上界。不存在由规范选择免费生成实际控制、精确实数或优化常数的结论。

## 14. 结论的精确范围

**约定 14.1（已给数学与未决边界）。** 普遍结论是每个有限十四词点态严格，紧集结论才是同一 $q_K<1$ 的一致率。各十四块的系数分别小于一，并不足以证明任意非紧无限调度的系数乘积趋零；本卷不作这种遗忘宣告，也未分类接近端点的全部非紧参数集。

人口正性不推出量子密度全空间忠实性，不是 CP 重置 minorization；支持精确秩证明不提供近取等的特征值间隙。两个见证人口不同不是需要消除的误差；纯轨迹比率只构造其规范和消去行，伴侣只在需要处提供自己的正坐标。

一般非周期输出不必收敛到一个密度，也不要求所有字母有共同平稳密度或人口。周期情形的唯一吸引轨道仅在第 12 节条件下成立。半参数反方向只证明完整类中有保留经典位的合法选择，不分类所有半参数字母或被强制混合半参数与非半参数的调度。

没有新增精确码时域、纠缠破坏指数、容量、有限 NPT、量子记忆或尖锐十四时域断言。端点参数、反馈、环境或分支访问、途中纠正、额外输入相关历史、更大保留空间和未知相位读出属于其他合同。经典窗口标签本身不提供任意源到 CPTP、Hamiltonian、场论或物理实现的桥梁。

全部证明均为未执行符号数学；没有数值计算、公式执行、实验、数学测试、构建、Lean/D5/Blueprint 或渲染核验。字节身份和 JSON 合法性不验证数学。本卷不提供独立批准、形式内核、外部来源认证、全球新颖性、物理、经验机器学习、总资源或持续目标完成证书。

## 追加锚（本行以下为增补区）

## 15. 可求和扰动下的一条永久可读调度

**引理 15.1（连续合法族的完全范数模数）。** 对命题 11.1 的同一族 $C_\eta$，记 $C=C_{1/2}$。当 $\eta\in[1/4,3/4]$ 时，

$$
\|C_\eta-C\|_\diamond\le2\sqrt2\,|\eta-1/2|.
\tag{15.1}
$$

证明。在同一个二维环境取 $V_\eta x=\sum_{a=0}^1 A_a(\eta)x\otimes f_a$。$V_\eta-V_{1/2}$ 只有输入列 $0,1,2$ 可能非零；前两列分别为 $(u_\eta-u)\otimes f_0$、$(u_\eta-u)\otimes f_1$，第三列为 $(v_\eta-v)\otimes(f_0+f_1)/\sqrt2$。三列两两正交且范数相同，故

$$
\|V_\eta-V_{1/2}\|_{\mathrm{op}}^2
=\left(\sqrt{1-\eta}-\frac1{\sqrt2}\right)^2
+\left(\sqrt\eta-\frac1{\sqrt2}\right)^2.
$$

平方根函数在 $[1/4,3/4]$ 上的导数绝对值至多一，所以该算子范数至多 $\sqrt2|\eta-1/2|$。对任意有限参考和任意复矩阵 $X$，把等距共轭之差展开为

$$
(V_\eta-V_{1/2})XV_\eta^\dagger
+V_{1/2}X(V_\eta-V_{1/2})^\dagger,
$$

其中各等距均张量参考恒等。左右乘法的迹范数界及环境偏迹的完全迹范数收缩使结果至多 $2\|V_\eta-V_{1/2}\|_{\mathrm{op}}\|X\|_1$。取上确界即得 (15.1)。此为共同 dilation 的标准连续性估计在该族上的直接计算，不假设新鲜环境可以跨步访问。$\square$

**定理 15.2（每个十四窗口严格而一位信息永久可读）。** 对每个 $0<\zeta<1$，存在一条事先固定、与输入标签无关的无限合法调度，使每个连续十四步子词的迹系数严格小于一，但对命题 11.2 的同一对正交密度 $P,M$，每个 $n\ge0$ 都有

$$
\|T_n(P)-T_n(M)\|_1\ge2-\zeta.
\tag{15.2}
$$

同一个终端测量 $\{P,I-P\}$ 在每个终点的两类错误各不超过 $\zeta/4$。各终点是同一调度的截断实验，不在中间执行该测量。

证明。取单一序列

$$
\eta_j=\frac12+\frac{\zeta}{4\sqrt2}\,2^{-j},\qquad
\Phi_j=C_{\eta_j},\qquad j\ge1.
\tag{15.3}
$$

所有参数位于 $[1/4,3/4]$ 内且非半，命题 11.1 保证每个字母属于其完整类。故定理 1.3 适用于每个连续十四步子词。另一方面，对任意 $n\ge1$，在同一实际词上望远镜展开

$$
T_n-C^n=\sum_{j=1}^n
C_{\eta_n}\cdots C_{\eta_{j+1}}
(C_{\eta_j}-C)C^{j-1}.
$$

空后缀为恒等。每个 CPTP 的钻石范数为一，故引理 15.1 给

$$
\|T_n-C^n\|_\diamond
\le\sum_{j=1}^n2\sqrt2|\eta_j-1/2|
=\frac\zeta2(1-2^{-n})=:b_n.
\tag{15.4}
$$

命题 11.2 给 $C^n(P)=P$、$C^n(M)=M$。因此两输出分别在迹范数 $b_n$ 内接近 $P,M$，从而

$$
\|T_n(P)-T_n(M)\|_1\ge2-2b_n\ge2-\zeta.
$$

对无迹厄米误差 $X$ 和效果 $0\le E\le I$，Jordan 分解给 $|\operatorname{Tr}(EX)|\le\|X\|_1/2$。分别应用于 $T_n(P)-P$ 与 $T_n(M)-M$，固定测量的两类错误均至多 $b_n/2\le\zeta/4$。$n=0$ 时错误为零。$\square$

**定义 15.3（计数控制的自治提升）。** 令可数控制寄存器的正交基为 $|j\rangle$，$j\ge0$。置

$$
L_a=\sum_{j\ge0}A_a(\eta_{j+1})\otimes|j+1\rangle\langle j|,
\qquad a=0,1.
$$

这些算子有界，且 $\sum_a L_a^\dagger L_a=I$：不同 $j$ 的移位输出正交，命题 11.1 的效应和逐块为恒等。因此它们给出一个时间齐次 CPTP 规则；在输入 $\rho\otimes|j\rangle\langle j|$ 上恰产生

$$
C_{\eta_{j+1}}(\rho)\otimes|j+1\rangle\langle j+1|.
$$

从控制态零出发，每个有限前缀实现 (15.3)。此提升使用无界计数空间和所列精确控制系数；它没有给出有限精度或有界资源实现。定理 15.2 的严格系数只针对预定调度下的五维系统子词，不针对含可读计数器的联合通道。

**推论 15.4（正局部收缩与累计条件）。** 置 $\tau(T)=-\ln\delta(T)$，约定 $-\ln0=+\infty$。引理 3.1 给 $\tau(ST)\ge\tau(S)+\tau(T)$。定理 15.2 的单条调度却满足

$$
\delta(T_n)\ge1-\zeta/2,
\qquad
\tau(T_n)\le-\ln(1-\zeta/2)
\quad(n\ge0).
\tag{15.5}
$$

对一般合法无限调度，令 $q_k=\delta(T_{14k:14k-13})$。若 $\sum_{k\ge1}(1-q_k)=\infty$，则 $\delta(T_n)\to0$。

证明。式 (15.2) 和引理 3.1 的距离表达式给 (15.5)。一般调度中，若某个 $q_k=0$，后续完整前缀系数均为零。否则用 $\ln q_k\le-(1-q_k)$ 和次乘性，

$$
\delta(T_{14m})\le\prod_{k=1}^m q_k
\le\exp\left[-\sum_{k=1}^m(1-q_k)\right]\longrightarrow0.
$$

不足十四步的后缀也收缩，故全部 $n$ 的系数趋零。这个累计条件只是充分条件；未将乘积上界认作等号或一般必要条件。对定理 15.2 的调度，反过来由 $1-\zeta/2\le\delta(T_{14m})\le\prod_{k\le m}q_k$ 可知这些严格正的分块损失之和有限。$\square$

**约定 15.5（归属与量词）。** 望远镜扰动、Dobrushin 系数的次乘性和无限乘积判据是标准方法；量子迹系数及过程扰动的背景见 O. Szehr 与 M. M. Wolf，*Perturbation Bounds for Quantum Markov Processes and their Fixed Points*，[arXiv:1210.1171](https://arxiv.org/abs/1210.1171)，第 II、IV 节。这里并未借用该文的混合或唯一平稳态假设：$C$ 有两固定密度，(15.4) 直接由共同 dilation 和同一词展开证明。repo-derived 内容是将本卷的合法连续族与十四时域接成 (15.3) 这一条无限反例；不同于命题 11.2 对每个有限 $n$ 分别选参数。量词为每个目标 $\zeta$ 选择一条调度，再对全部终点成立，不是一条固定调度同时实现全部 $\zeta$。保持的是近乎无误差的经典二元读出，不是未知量子位恢复。

## 16. 相对于全部合法未来的预测商

**定义 16.1（固定参数下的未来菜单）。** 固定 $0<\eta<1$。允许任意非空有限词 $\Phi_m\cdots\Phi_1$，每个 $\Phi_j\in\mathcal L_\eta$，末端允许任意效果 $0\le E\le I$。不保留环境记录，不作途中反馈，不允许零步读出。密度 $\rho\sim_\eta\sigma$ 表示这个菜单中每个实验的概率均相同。这是对全部可选通道的等价关系，不是只重复某个固定字母的等价关系。

**定理 16.2（精确共同核与可见维数）。** 记 $\mathsf D=\operatorname{span}\{e_3,e_4\}$。则

$$
\bigcap_{\Phi\in\mathcal L_\eta}\ker\Phi
=\{X=P_{\mathsf D}XP_{\mathsf D}:\operatorname{Tr}X=0\},
\tag{16.1}
$$

从而

$$
\rho\sim_\eta\sigma
\quad\Longleftrightarrow\quad
\rho-\sigma=P_{\mathsf D}(\rho-\sigma)P_{\mathsf D}.
\tag{16.2}
$$

复线性算子商维数为 $22$，归一化密度商的实仿射维数为 $21$。

证明。引理 2.2 说明每个字母把支持在 $\mathsf D$ 内的 $X$ 映为 $\operatorname{Tr}(X)E_2$，故 (16.1) 的右侧包含于共同核。

反向设 $X$ 在共同核。用引理 2.1 的八条边和权重，$G=I_8$ 是合法共同 Gram。对任意输入指标 $i,k$，只要至少一个不在 $\{3,4\}$，可以取不同输出 $j\in S_i,l\in S_k$，其中

$$
S_0=S_1=\{0,3\},\quad S_2=\{1,4\},\quad
S_3=S_4=\{2\}.
$$

当 $i=k$ 时，同一输入的两条不同输出边亦可这样选择。令相应边为 $a=(j,i),b=(l,k)$，取 $0<|t|<1$，置

$$
G_t=I_8+tE_{ab}+\overline tE_{ba}.
$$

这个 Hermitian 矩阵的相关二维块特征值是 $1\pm|t|$，故正定，单位对角不变。因 $j\ne l$，它不改变任何强制的同输出正交条目，所以引理 2.1 给出一个共同环境中的实际合法字母 $\Phi_t$。以 $\Phi_0$ 表示 $I_8$ 的字母，反序共轭 Gram 公式给

$$
(\Phi_t-\Phi_0)(X)
=w_aw_b\bigl(\overline tX_{ik}E_{jl}+tX_{ki}E_{lj}\bigr).
$$

两输出矩阵单位不同且权重正；共同核条件遂迫使 $X_{ik}=X_{ki}=0$，包括 $i=k$ 的情形。因此只剩 $\mathsf D$ 块。人口律再给 $X_{33}+X_{44}=0$，证明 (16.1)。

对两密度之差，若所有效果在所有单步之后都相同，效果分离 Hermitian 矩阵，故差在 (16.1) 中；反向则第一步已消去它，所有更长词也不可见，得到 (16.2)。无迹二乘二复块维数三，从 $\dim_{\mathbb C}M_5=25$ 减去三得到 $22$。Hermitian 归一化仿射空间实维数二十四，其不可见实子空间维数三；满秩密度附近有全部方向，故商的仿射维数为二十一。$\square$

**推论 16.3（改变末端读口的维数）。** 同样要求至少一次更新，若只允许计算基人口效果，则预测节点恰由

$$
\bigl(\operatorname{Tr}(P_{\mathsf A}\rho),\rho_{22},
\operatorname{Tr}(P_{\mathsf D}\rho)\bigr)
$$

决定，归一化后实仿射维数二。若允许更新前立即作任意效果测量，则节点为完整密度，实仿射维数二十四。

证明。人口律使单步全部人口只依赖所列三个数，且由输出坐标 $0,1,2$ 及 $r>0$ 恢复它们；以后的人口仍按同一矩阵递推。三数非负、和为一，且各顶点可由输入基态实现，故维数二。允许零步任意效果时，效果直接分离任意两个不同密度，故无非零不可见方向。$\square$

**约定 16.4（模型综合的范围）。** 一般预测商原则已有《[静态相融纤维理论](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)》第 4 节；本节 repo-derived 内容是对本卷完整八边共同 Gram 类计算其精确共同核与三个读口的维数，不提出新的通用商空间原则。式 (16.1) 使用整个合法类的可选择性，不能转给一个任意固定仪器，也不保证未知节点的有限实验取得、认证或低成本编码。

## 追加锚（本行以下为增补区）

# AURIC：有限基态校准、保留读与全域节点的内生恢复

## 1. 同一个来源上的有限校准与二元约束

**定义 1.1（完整来源与固定操作域）。** 原数学源固定为提交 46927cc328c58a872092e1d1c3bf102e48fa0426 的[续卷 II][II]、[续卷 III][III]和[续卷 V][V]。沿用 II77、100、121 及 III138.1、145.1、157.1 的同一个对象：

$$
\begin{gathered}
E=\{q\subseteq\{1,\ldots,9\}:q\text{ 不含相邻整数}\},\qquad
\mathcal K=\mathbb C^E=V_{12}^{\mathbf1},\qquad |E|=89,\\
b_k(q)=\mathbf1_{k\in q},\qquad
b_{-1}b_0=10,\qquad b_{10}b_{11}b_{12}=010,\\
H=V_8^{\mathbf1},\quad \dim_{\mathbb C}H=13,\qquad
J:H\otimes\mathbb C^2\longrightarrow\mathcal K,\qquad
\mathcal C=\operatorname{ran}J,\quad
\dim_{\mathbb C}\mathcal C=26,\quad \dim_{\mathbb C}\mathcal C^\perp=63.
\end{gathered}
\tag{1.1}
$$

$e_q$ 表示配置 $q$ 的标准基向量。唯一实际 ready 仍为 $e_{\rm r}=R_0v=J(v,0)$，其中 $v=e_{00100}$。记
$\mathsf W_{11}=\{0,\ldots,10\}^{<\infty}$、
$\mathsf W=\{0,\ldots,6\}^{<\infty}$，
$\chi_a=K_ae_{\rm r}$，字按调用次序连接，$K_{aj}=K_jK_a$。实际程序仍只有原 $\mathsf T(a)$ 与 $\mathsf R(a,f)$：前者执行 $a$ 后用旧终端，后者执行 $a$，读取并保留 $b_9$，执行不依赖读取结果的外生 $f\in\mathsf W$，再用同一旧终端。所有字有限而无统一长度截断。

$M_i$ 是 $b_9=i$ 的坐标投影，$i=0,1$；$N_w$ 是旧十位 $(b_{-1},\ldots,b_8)=w$ 的坐标投影，$w\in\Omega_{10}=\{0,1\}^{10}$。全部 $1024$ 标签保留，无合法路径的标签为零投影。原实际调用、真实细档案、时间、失败、拒绝、停止、告警以及取得和误差合同均保留原范围；$\mathcal C^\perp$ 不作为失败删去。以下全向量量词是数学函数的定义域，不增加实际准备、读口、反馈、辅助载体或连续控制。

**定义 1.2（原十一完整门与全部原分量）。** 严格采用 III (157.2) 的矩阵和边界：

$$
\begin{gathered}
\varphi=(1+\sqrt5)/2,\qquad x=\varphi^{-1},\qquad y=\sqrt x,\qquad
x+x^2=1,\qquad \alpha=3\pi/5,\qquad \zeta=e^{i\alpha},\\
Q_*=\begin{pmatrix}x&xy\\xy&x^2\end{pmatrix},\qquad
\mathcal P_j=n_{j-1}n_{j+1}
 +(1-n_{j-1})(1-n_{j+1})(Q_*)_{b_j},\\
H_j=-\alpha(I+\mathcal P_j),\qquad
U_j(t)=e^{-itH_j},\qquad
K_j=U_j(1)=\zeta[I+(\zeta-1)\mathcal P_j],\qquad 0\le j\le10.
\end{gathered}
\tag{1.2}
$$

$n_k$ 是位占据投影，固定外位按字面代入。令 $\mathscr B_j$ 为原 $H_j$ 支撑图的全部连通分量，含所有单点。具体地，$1\le j\le9$、两邻位均为零时，固定其它位、翻转第 $j$ 位的两条路径组成活动对；至少一个邻位占据时中心位只能为零，形成阻塞单点。两邻位都占据或恰一占据时，单点上的 $\mathcal P_j$ 分别为 $1$ 或 $0$。边界地址有 $\mathcal P_0=n_1$、$\mathcal P_{10}=n_9$，各自的全部 $89$ 个单点仍在 $\mathscr B_j$ 内。分量不按完整门的谱重数重新划分。

**定义 1.3（不预付节点的有限校准裸类）。** 置
$X=\mathbb P(\mathcal K)=\mathbb{CP}^{88}$，
$\Delta(E)=\{p:p_q\ge0,\ \sum_qp_q=1\}$。
$\mathscr C_{\rm cal}$ 由同一个连续映射 $\Pi:X\to\Delta(E)$ 组成，其在非零向量上的同名提升满足

$$
\begin{gathered}
\Pi_q(\lambda z)=\Pi_q(z)
\quad(q\in E,\ z\ne0,\ \lambda\in\mathbb C\setminus\{0\}),\\
\Pi_q(e_r)=\delta_{qr}\quad(q,r\in E),\\
\sum_{q\in B}\Pi_q(K_jz)=\sum_{q\in B}\Pi_q(z)
\quad(z\ne0,\ 0\le j\le10,\ B\in\mathscr B_j).
\end{gathered}
\tag{1.3}
$$

这里仅在 $89$ 条基态射线上作确定性校准；这些是密度函数在有限射线上的数学取值条件，不增加从唯一 ready 精确制备各 $e_r$ 的权限。不要求任何一般输入上的 $z_q=0\Rightarrow\Pi_q(z)=0$，连整记录扇区的零质量也不预设。不另加内部 $t$ 方程、可微性、有限多项式次数、径向性、可分性、PSD、严格正性或 Born 公式。

作为精确比较，$\mathscr C_{\rm node}$ 表示把 (1.3) 的有限基态校准换成全域逐坐标节点条件、其余条件完全相同的类；它就是[续卷 VIII][VIII] 定义 1.3 的端点类，不是含全部内部时刻方程的旧 $\mathscr C_{\rm nat}$。

**定义 1.4（原实际保留读关系）。** 对同一个未知 $\Pi$ 定义

$$
E_i=\{q:b_9(q)=i\},\qquad
m_i(z)=\sum_{q\in E_i}\Pi_q(z),\qquad
t_i(z)=\frac{\|M_i z\|^2}{\|z\|^2}.
\tag{1.4}
$$

关系 $\mathrm R$ 严格为 III (173.2) 的原实际量词：

$$
\Pi_q(\chi_a)=m_i(\chi_a)\Pi_q(M_i\chi_a)
\quad(a\in\mathsf W_{11},\ i=0,1,\ q\in E_i).
\tag{1.5}
$$

当 $M_i\chi_a=0$ 时右端置零，不评价 $\Pi(0)$。$m_i$ 从同一个 $\Pi$ 求和，既不是另选的记录律，也不是预付的平方质量。这里的二元对象是整体射线与其同一记录投影射线；端点关系的二元对象则是 $([z],[K_jz])$。它们共同约束一张密度映射在相连对象上的取值，不允许为每条边、每个分量或读前读后另选函数。数学 R 与实际报告的条件概率含义仍由 §5 的独立合同连接。

## 2. 从有限校准传播支撑，再恢复全部细节点

**引理 2.1（不使用 R 的整块支撑传播）。** 对每个 $\Pi\in\mathscr C_{\rm cal}$、每个 $z\ne0$ 和 $i\in\{0,1\}$，令
$Q=n_1$，
$q_Q(z)=\sum_{b_1(r)=1}\Pi_r(z)$。则

$$
\begin{gathered}
M_i z=0\ \Longrightarrow\ m_i(z)=0,\qquad
z\in M_i\mathcal K\setminus\{0\}\ \Longrightarrow\ m_i(z)=1,\\
z\in\ker Q\setminus\{0\}\ \Longrightarrow\ q_Q(z)=0,\qquad
z\in\operatorname{ran}Q\setminus\{0\}\ \Longrightarrow\ q_Q(z)=1.
\end{gathered}
\tag{2.1}
$$

另将全部路径分成

$$
\begin{aligned}
\mathsf A&=\{q:b_8=b_9=0\},&|\mathsf A|&=34,\\
\mathsf B&=\{q:b_8=1,b_9=0\},&|\mathsf B|&=21,\\
\mathsf C&=\{q:b_9=1\},&|\mathsf C|&=34.
\end{aligned}
\tag{2.2}
$$

对任意非零 $w\in\mathbb C^{\mathsf B}$ 和任意 $r\in\mathsf A$，还有
$\Pi_r(0,w,0)=0$。这些结论不假设全域细节点。

**证明。** 地址 $0,\ldots,8$ 的每个原分量都留在某个 $E_i$ 内；地址 $2,\ldots,10$ 的每个原分量都留在 $b_1$ 的某个值内。因此端点式逐分量求和给

$$
m_i(K_jz)=m_i(z)\ (0\le j\le8),\qquad
q_Q(K_jz)=q_Q(z)\ (2\le j\le10).
\tag{2.3}
$$

连续性将逐字不变性传到相应算子闭包。直接消费 III (144.9)、(144.11) 的共同块群：

$$
\begin{aligned}
SU(M_0\mathcal K)\times SU(M_1\mathcal K)
&\subseteq\overline{\{K_g:g\in\{0,\ldots,8\}^{<\infty}\}},\\
SU(\ker Q)\times SU(\operatorname{ran}Q)
&\subseteq\overline{\{K_h:h\in\{2,\ldots,10\}^{<\infty}\}}.
\end{aligned}
\tag{2.4}
$$

两边块维数均为 $55,34$。这是同一个全矩阵上的乘积群包含，保留块间相位所需的共同实现；不是将两个分别稠密的射影像拼接。每个 $SU(d)$、$d\ge2$ 在单位向量球面上传递：酉补全后可在目标的正交方向调整行列式，保持目标向量及其相位。故 $m_i$ 在每个纯记录块的射影空间上常值。任一块内基向量的校准确定其为 $0$ 或 $1$，给前两式。对 $q_Q$ 及第二个乘积群同理，得到后两式。非负性进一步给：输入在一个记录块内时，所有块外坐标的 $\Pi_q$ 逐项为零。

最后处理 (2.2) 中的尾块。令
$p_{\mathsf A}(z)=\sum_{r\in\mathsf A}\Pi_r(z)$。
原地址 $0,\ldots,6$ 的全部分量保持字面尾 $(b_7,b_8,b_9)$，因而保持 $\mathsf A$，$p_{\mathsf A}$ 对这些字不变。$\mathsf B$ 正好是 III151.1 的完整尾 $010$ 块。III (151.3) 给其限制的射影闭包为 $PU(21)$，故 $p_{\mathsf A}$ 限制到 $\mathbb P(\mathbb C^{\mathsf B})$ 后为常数；任一 $\mathsf B$ 基向量的校准给该常数为零。有限个非负项之和为零，遂对每个 $r\in\mathsf A$ 都有 $\Pi_r(0,w,0)=0$。

这里仅将输入限制到一个不变尾块，再使用同一个字在该块上的限制。III151 的三个 $21$ 维同型块始终同步作用，两个 $13$ 维块也同步；没有独立控制旁观副本。块外权重的零值来自校准传播及非负性，不来自未给的细节点。∎

**定理 2.2（无节点前件下的完整选择）。** 对每个 $\Pi\in\mathscr C_{\rm cal}$，

$$
\boxed{\quad
\mathrm R\quad\Longleftrightarrow\quad
\Pi_q(z)=\frac{|z_q|^2}{\|z\|^2}
\quad(z\in\mathcal K\setminus\{0\},\ q\in E).
\quad}
\tag{2.5}
$$

特别地，全部记录支撑及全部逐坐标节点都是结论。

**证明。** 先设原实际 R 成立。固定 $i\in\{0,1\}$ 和 $q\in E_i$，在 $M_i z\ne0$ 处置
$L_{i,q}(z)=m_i(z)\Pi_q(M_i z)$，在零投影处置零。非零分支连续；若趋于零投影，引理 2.1 已给极限处 $m_i=0$，而

$$
0\le L_{i,q}(z)\le m_i(z).
\tag{2.6}
$$

故此零延拓在整个射影空间连续。直接消费 III (144.12) 的同一 ready 射线稠密性
$\overline{\{[\chi_a]:a\in\mathsf W_{11}\}}=X$，
将实际 R 延拓为

$$
\Pi_q(z)=L_{i,q}(z)\quad(z\ne0,\ q\in E_i).
\tag{2.7}
$$

乘积的零投影连续性至此才得到证明；没有评价 $\Pi(0)$。稠密性连接数学函数恒等式，不把极限射线列为新增实际准备。

接着复用 III144、III173.5–173.9 的粗函数方法，并重新供应其中原先由节点给出的全部输入。由 (2.3)、(2.4)，$q_Q$ 在固定
$s=\|Qz\|^2/\|z\|^2$ 的纤维上常值。取一个 $\ker Q$ 基方向和一个 $\operatorname{ran}Q$ 基方向作连续截面，得到连续 $G:[0,1]\to[0,1]$，使

$$
q_Q(z)=G\!\left(\frac{\|Qz\|^2}{\|z\|^2}\right),\qquad
G(0)=0,\quad G(1)=1.
\tag{2.8}
$$

端值由引理 2.1 得到。共同特殊酉作用能够分别匹配两个非零块的向量相位，因而此径向性没有先行删去相对相位。

把 (2.7) 在 $b_1=1$ 上求和；引理 2.1 已使 $\Pi(M_i z)$ 支持在 $E_i$ 内，故

$$
q_Q(z)=\sum_{i:M_i z\ne0}m_i(z)q_Q(M_i z).
\tag{2.9}
$$

固定单位 $z$，令 $t=\|M_0z\|^2\in(0,1)$、$m=m_0(z)$。III (144.16) 的四个交空间维数，按 $M_0,M_1$ 为行、$\ker Q,\operatorname{ran}Q$ 为列，是

$$
\begin{pmatrix}34&21\\21&13\end{pmatrix}.
\tag{2.10}
$$

每个记录块内的 $Q$ 像与核都非零，所以可为两个条件单位向量同时选取任意 $Q$ 质量 $r_0,r_1\in[0,1]$。使用 (2.4) 的同一个 $M$ 块乘积群，将两个向量送到这些目标；该作用保持 $m,t$。在 (2.9) 中代入这一个共同作用并取连续极限，得到

$$
G(tr_0+(1-t)r_1)=mG(r_0)+(1-m)G(r_1).
\tag{2.11}
$$

这里两条件质量属于同一个共同实现，不是分别可达值的拼接。取 $(r_0,r_1)=(1,0),(0,1)$，有
$m=G(t)$、$1-m=G(1-t)$。全域 (2.7) 已得，故 $t$ 可任取内部值；在 $t=1/2$ 先得 $G(1/2)=1/2$，再由 (2.11) 得中点等式。III (144.19) 的二进有理插值和连续性给 $G(s)=s$。$t=0,1$ 已由引理 2.1 处理。因此

$$
m_i(z)=t_i(z)\quad(i=0,1,\ z\ne0).
\tag{2.12}
$$

现在定义辅助函数

$$
F_q(z)=
\begin{cases}
\|z\|^2\Pi_q(z),&z\ne0,\\
0,&z=0.
\end{cases}
\qquad
F_q(\lambda z)=|\lambda|^2F_q(z).
\tag{2.13}
$$

它连续、非负，且 $0\le F_q(z)\le\|z\|^2$，所以零点连续；齐次式对零标量也成立。这是 $F_q(0)$ 的定义，不是 $\Pi(0)$ 的定义。(2.7)、(2.12) 和基态校准给

$$
F_q(z)=F_q(M_i z)\quad(q\in E_i,\ z\in\mathcal K),\qquad
F_q(e_s)=\delta_{qs}\quad(q,s\in E).
\tag{2.14}
$$

以下所有零向量代换都只作用于 $F$。按 (2.2) 写 $z=(u,w,v)$，翻转第九位识别 $\mathbb C^{\mathsf A}$ 与 $\mathbb C^{\mathsf C}$。置

$$
T=\begin{pmatrix}a&b\\b&d\end{pmatrix}
=I+(\zeta-1)Q_*.
\tag{2.15}
$$

原矩阵给 $T$ 酉、$|b|^2=x$、$|a|^2=|d|^2=x^2$，特别 $b\ne0$；这些是 III (173.13)、(173.18) 在 $t=1$ 的值。地址九的完整作用为

$$
\zeta^{-1}K_9(u,w,v)=(au+bv,\ w,\ bu+dv).
\tag{2.16}
$$

固定任一活动对 $r\in\mathsf A$、$r^+=r\cup\{9\}\in\mathsf C$，令
$f_0(u,w)=F_r(u,w,0)$、
$f_1(v)=F_{r^+}(0,0,v)$。
原活动对端点守恒、酉性及 (2.14) 给

$$
f_0(au+bv,w)+f_1(bu+dv)=f_0(u,w)+f_1(v).
\tag{2.17}
$$

引理 2.1 的尾块结论给 $f_0(0,w)=0$，包括由 (2.13) 定义的 $w=0$。在 (2.17) 取 $u=0$，用复二齐次性，得

$$
f_0(bv,w)=(1-|d|^2)f_1(v)=|b|^2f_1(v)=f_1(bv).
\tag{2.18}
$$

$b\ne0$，所以 $f_0(u,w)=f_1(u)=:f_r(u)$。这个连续非负、复二齐次函数满足

$$
f_r(au+bv)+f_r(bu+dv)=f_r(u)+f_r(v),\qquad
f_r(e_s)=\delta_{rs}\quad(s\in\mathsf A).
\tag{2.19}
$$

第二式是有限基轴校准；尚未断言任意 $u_r=0$ 上的零值。

直接复用 VIII (2.14)–(2.17) 中不使用节点的端点函数接口。具体地，令 $S_f(u,v)=f_r(u)+f_r(v)$；(2.19) 使它在 $T$、$T^{-1}=T^*$ 下不变，复二齐次性又使它在两个自变量各自的标量相位下不变。故它在

$$
W_\theta=T^*\operatorname{diag}(e^{i\theta},1)T,\qquad
|(W_\theta)_{12}|^2=4x^3\sin^2(\theta/2)
\tag{2.20}
$$

下不变。后一式由 $\overline a b+\overline b d=0$ 得到。$x^3=\sqrt5-2$ 给 $4x^3>1/2$，故可取数学参数 $\theta$ 使右端等于 $1/2$。此时 $W_\theta$ 四项模长均为 $1/\sqrt2$；左右对角单位相位将它化为 Hadamard 矩阵，所有这些相位均由同一齐次性消去。因此

$$
f_r(u+v)+f_r(u-v)=2f_r(u)+2f_r(v).
\tag{2.21}
$$

这只是全域函数恒等式的自变量代换。$\operatorname{diag}(e^{i\theta},1)$ 和 $W_\theta$ 不被声明为原实际门，没有增加任意相位控制，也没有使用任何内部平衡脉冲。

与 VIII (2.18) 的全超平面节点用法不同，这里逐条使用有限基轴的零值。对任意 $s\in\mathsf A\setminus\{r\}$、$\lambda\in\mathbb C$，令 $h=\lambda e_s$，由校准和齐次性有 $f_r(h)=0$。对任意 $u$，(2.21) 使
$g_n=f_r(u+nh)$、$n\in\mathbb Z$ 满足
$g_{n+1}+g_{n-1}=2g_n$。其一阶差恒定，而双向非负迫使公差为零；故 $f_r(u+h)=f_r(u)$。逐个取 $h=-u_se_s$ 消去其余 $33$ 个坐标，最终得到

$$
f_r(u)=f_r(u_re_r)=|u_r|^2.
\tag{2.22}
$$

于是所有 $q\in\mathsf A\cup\mathsf C$ 均已满足 $F_q(z)=|z_q|^2$，其全部细节点也随之推出。

还剩 $q\in\mathsf B$。每个这样的点都是地址九的原阻塞单点；(2.14)、(2.16) 和该单点的端点守恒给

$$
F_q(au+bv,w,0)=F_q(u,w,0).
\tag{2.23}
$$

取 $u=0$，让 $v$ 任意变化，由 $b\ne0$ 得
$F_q(z)=g_q(w)$，且 $g_q(0)=F_q(0)=0$。
这个零值来自已证明的外部自变量独立性，没有使用节点。

合法性使每个 $q\in\mathsf B$ 都有 $b_7=b_9=0$。地址八把它与
$q^-=q\setminus\{8\}\in\mathsf A$ 配成原活动对。令
$\delta_q(z)=F_q(z)-|z_q|^2$。原对和端点守恒与参考平方对和守恒相减，已知 $\delta_{q^-}=0$，故

$$
\delta_q(K_8z)=\delta_q(z).
\tag{2.24}
$$

全部 $\mathsf B$ 点与
$\mathsf D=\{q:b_7=b_8=b_9=0\}\subset\mathsf A$
的 $21$ 点按翻转第八位配对，仍用同一个 $T$。给定非零 $w\in\mathbb C^{\mathsf B}$，取输入的 $\mathsf D$ 坐标为 $-(d/b)w$、$\mathsf B$ 坐标为 $w$、其余为零。地址八后整个 $\mathsf B$ 向量成为
$\zeta(b(-(d/b)w)+dw)=0$。
输出向量非零，但其 $F_q=g_q(0)=0$、平方坐标也为零，故输出处 $\delta_q=0$。由 (2.24) 得 $g_q(w)=|w_q|^2$。$w=0$ 已由 $g_q(0)=0$ 处理。三个块穷尽 $89$ 个坐标，正向得证。

反向令 $\Pi_q(z)=|z_q|^2/\|z\|^2$。它连续、复射线不变、非负归一，并满足所有基态校准。每个原分量的坐标投影与相应 $H_j$ 对易，故该分量平方范数及总范数在 $K_j$ 下不变，包括所有阻塞单点和边界地址全部单点。非零投影时，对 $q\in E_i$，

$$
t_i(z)\frac{|z_q|^2}{\|M_i z\|^2}
=\frac{|z_q|^2}{\|z\|^2}.
\tag{2.25}
$$

零投影时两侧均为零。因此 Born 属于 $\mathscr C_{\rm cal}$，满足全域 R，特别满足全部原实际 $\chi_a$ 上的 R。∎

## 3. 裸类严格扩大与成功类保持相同

**定义 3.1（仅在负号奇位扇区取最小值的固定密度）。** 直接复用 III164.1–164.2 的奇位扇区数据。置

$$
\begin{gathered}
O=\{1,3,5,7,9\},\quad S=\{s:s\subseteq O\},\quad
S_-=\{s\in S:|s|\text{ 为奇数}\},\\
A_s=\{j\in\{2,4,6,8\}:j-1,j+1\notin s\},\quad m_s=|A_s|,\\
R_s=\sum_{r\subseteq A_s}|s\cup r\rangle\langle s\cup r|,\qquad
w_s=\sum_{r\subseteq A_s}x^{m_s-|r|}(-y)^{|r|}e_{s\cup r},\qquad
\kappa_s=x^{m_s},\\
a_s(z)=\langle w_s,z\rangle,\qquad v_s(z)=R_sz-a_s(z)w_s,\qquad
c_q=\begin{cases}(-1)^{|q|},&q\in S,\\0,&q\notin S.\end{cases}
\end{gathered}
\tag{3.1}
$$

内积对第二变量线性。对全部 $z\ne0$ 固定同一个公式

$$
\begin{gathered}
h_-(z)=\frac1{\|z\|^2}
\min_{s\in S_-}\bigl[\kappa_s|a_s(z)|-\|v_s(z)\|\bigr]_+^2,\qquad
[u]_+=\max\{u,0\},\\
\Pi^*_q(z)=\frac{|z_q|^2}{\|z\|^2}+\frac12c_qh_-(z).
\end{gathered}
\tag{3.2}
$$

与 III (164.10) 的全 $32$ 扇区最小值不同，这里只对 $16$ 个负号扇区取最小值。既不随输入另选密度，也不随门、程序或分量另选公式。

**定理 3.2（严格裸包含及精确保留读缺陷）。** 上式的同一个全域固定密度满足

$$
\Pi^*\in\mathscr C_{\rm cal}\setminus\mathscr C_{\rm node}.
\tag{3.3}
$$

因此

$$
\mathscr C_{\rm node}\subsetneq\mathscr C_{\rm cal},\qquad
\{\Pi\in\mathscr C_{\rm node}:\mathrm R\}
=\{\Pi\in\mathscr C_{\rm cal}:\mathrm R\}
=\{\Pi^{\rm B}\}.
\tag{3.4}
$$

$\Pi^*$ 不满足原实际 R。

**证明。** 先逐项验证裸类前件。每条合法配置唯一写为 $s\cup r$，其中 $s\subseteq O$、$r\subseteq A_s$，故各 $R_s$ 为互相正交、总和为单位的坐标投影。由 $x^2+y^2=1$，

$$
\|w_s\|^2=(x^2+y^2)^{m_s}=1,\qquad
\langle e_s,w_s\rangle=\kappa_s>0.
\tag{3.5}
$$

不同 $w_s$ 支撑互斥，因而正交归一。III (164.13) 的同一逆三角估计逐 $s\in S_-$ 给

$$
z_s=\kappa_sa_s(z)+\langle e_s,v_s(z)\rangle,\qquad
0\le[\kappa_s|a_s(z)|-\|v_s(z)\|]_+\le|z_s|.
\tag{3.6}
$$

故 $0\le h_-(z)\le |z_s|^2/\|z\|^2$ 对每个负号坐标 $s\in S_-$ 成立。负号输出至少为相应平方质量的一半；正号输出增加，$S$ 外输出不变。所有输出非负。又
$\sum_{q\in E}c_q=(1-1)^5=0$，所以总和为一；无需另证各输出上界，非负归一已给上界一。

有限个连续函数的最小值连续。$a_s(\lambda z)=\lambda a_s(z)$、$v_s(\lambda z)=\lambda v_s(z)$，故分子、分母同乘 $|\lambda|^2$，$h_-$ 及 $\Pi^*$ 对所有非零复缩放不变，并按商拓扑下降到整个 $X$ 上连续。它们在所有非零部分支撑输入均有定义。

对任一基向量 $e_r$，仅有一个 $R_s$ 扇区可能非零。$S_-$ 有 $16$ 个元素，选一个不同的负号扇区，则该扇区 $a_s=v_s=0$，故 $h_-(e_r)=0$。因此全部 $q,r\in E$ 的基态校准成立。

再逐类验证全部端点。参考平方密度的分量守恒由原分量投影与 $H_j$ 对易直接得到。对偶地址 $j=0,2,4,6,8,10$，III164.2 给 $R_s$ 与 $H_j$ 对易，且 $w_s$ 是同一个 $H_j$ 的特征向量，因此 $|a_s|,\|v_s\|,\|z\|$ 在 $K_j$ 下不变。于是 $h_-(K_jz)=h_-(z)$。每个原分量 $B$ 的修正和为
$\frac12h_-(z)\sum_{q\in B}c_q$，从而不变；这包括地址零、十的全部单点。

对奇地址 $j=1,3,5,7,9$，若原分量交 $S$，其中配置的偶位全零，两个邻位均零；原分量恰为
$\{s,s\mathbin{\triangle}\{j\}\}\subset S$，两个 $c$ 值相反。其修正和恒为零，不需要 $h_-$ 对该奇地址不变。其余分量不交 $S$，修正也恒零，包括全部阻塞单点。十一地址及全部原分量至此穷尽，(1.3) 的所有全域端点等式同时成立。这里复用的是 III164.2 的精确不变数据，不把内部时刻控制作为新权限。

给出具体节点违反。令

$$
z_-=\frac14\sum_{s\in S_-}w_s,\qquad
\|z_-\|=1,\qquad (z_-)_\varnothing=0.
\tag{3.7}
$$

各负号扇区上 $a_s(z_-)=1/4$、$v_s(z_-)=0$，故

$$
h_-(z_-)=\frac1{16}\min_{s\in S_-}\kappa_s^2>0,\qquad
\Pi^*_\varnothing(z_-)=\frac12h_-(z_-)>0.
\tag{3.8}
$$

空配置的幅度为零而权重为正，严格证明 $\Pi^*\notin\mathscr C_{\rm node}$。另一方面，全域节点加非负归一在每个 $e_r$ 上强迫除 $r$ 外各输出为零、$r$ 输出为一，故 $\mathscr C_{\rm node}\subseteq\mathscr C_{\rm cal}$，结合此见证即得严格性。加 R 后的类等式由定理 2.2 及 Born 自身的节点得到。

最后独立指出这个密度的 R 缺陷，避免将它误作定理 2.2 的反例。对每个 $i$，

$$
\sum_{q\in E_i}c_q=(-1)^i(1-1)^4=0,\qquad m_i^*(z)=t_i(z).
\tag{3.9}
$$

$M_0z_-$ 与 $M_1z_-$ 都非零：分别有不含 $9$ 和含 $9$ 的负号扇区。每个投影都删去另一记录值的至少一个负号扇区，故
$h_-(M_i z_-)=0$。
又 $(M_0z_-)_\varnothing=0$，所以 $q=\varnothing,i=0$ 的全域缺陷为

$$
\Pi^*_\varnothing(z_-)
-m_0^*(z_-)\Pi^*_\varnothing(M_0z_-)
=\frac12h_-(z_-)>0.
\tag{3.10}
$$

由于 $m_i^*=t_i$，对应乘积在零投影处由 $0\le L\le t_i$ 连续延拓；因此这个缺陷是整个 $X$ 上的连续函数。正值的开邻域与 III (144.12) 的同一 ready 稠密轨道相交，得到某个实际有限 $\chi_a$ 上的 R 违反。这里给存在的有限字，不给统一字长或有限样本认证界。∎

## 4. 前件减少及反事实的准确范围

**命题 4.1（删 R 或删端点均失去相应选择）。** 在原完整载体上，以下两个不同的固定密度分别见证两个删除命题。

删除 R、保留整个 $\mathscr C_{\rm cal}$ 时，定义 3.1 的 $\Pi^*$ 仍合法而非 Born，且违反一个细节点。甚至保留全部细节点而删除 R，III164.4 的原固定 $\Pi^{(1/2)}$ 仍是合法非 Born 密度；其全支撑偏差由 III (164.17)–(164.18) 给出。这后一结果直接引用原证明，不构成新的反密度。

删除端点、保留连续性、复射线不变、非负归一、全部基态校准和全域 R 时，另一个固定密度

$$
\Pi_q^{[4]}(z)=\frac{|z_q|^4}{\sum_{r\in E}|z_r|^4}
\tag{4.1}
$$

合法而非 Born；它不满足全部原端点。

**证明。** 第一项由定理 3.2 及直接引用的 III164.4 得到。第二项是 VIII4.1 已有的删除端点反事实：投影分母的消去直接给全域 R，零投影时两侧为零。为固定原关系的失守点，取 $z=e_\varnothing+e_{\{8\}}$，地址九原对 $\{\varnothing,\{9\}\}$ 的质量起初为 $1/2$；该门后按 (2.15)–(2.16)，此对质量为

$$
\frac{x^4+x^2}{1+x^4+x^2}<\frac12,
\tag{4.2}
$$

因为 $x^4<x$、$x^2+x=1$。因此它没有暗中保留端点前件。两个密度分别反驳两个删除命题，不把它们的性质拼成一个满足全部前件的反例。∎

**定义 4.2（减少的前件与仍保留的结构）。** 相对 VIII2.1，这里的改变只有：以 $89$ 条基态射线的确定性校准替代所有输入、所有坐标的节点族，仍使用原完整门端点和原实际 R。定理 3.2 证明这是裸类的严格扩大；定理 2.2 证明 R 成功类保持同一个单点，节点不再承担输入角色。尾块群传播、有限基轴消元以及 $g_q(0)=0$ 分别替代旧细化证明中三个不同的节点用途。

连续性仍用于闭包不变性、零投影乘积和粗函数插值；非负归一用于块支撑及双向等差消元；复缩放不变用于二齐次性和端点函数的相位代换。全部原单点、原活动对、两个共同块群、七地址尾块与唯一 ready 稠密性仍承重。没有证明任意删地址、删分量、删连续性或少于 $89$ 个基态校准时的完整分类，也没有证明这一组充分条件绝对最少。数学前件变弱不直接给实际取得、重复次数或认证成本下降。

## 5. 同源实际条件律与原量子预测的消费者

**定义 5.1（数学 R 接回实际读取的独立合同）。** 固定任一 $\Pi\in\mathscr C_{\rm cal}$，直接采用 III174.1–174.2 的区分。对每个原 $\mathsf R(a,f)$，在同一个普通因果概率空间上，若另供实际可读过去 $\mathcal G_-$ 的条件配置律

$$
\Pr(Q_-=q\mid\mathcal G_-)=\Pi_q(\chi_a),
\tag{5.1}
$$

以及字面报告 $I=b_9(Q_-)$、配置保留 $Q_+=Q_-$、实际纯后继 $[M_I\chi_a]$，则正质量分支上的普通 Bayes 公式给

$$
\Pr(Q_+=q\mid\mathcal G_-,I=i)
=\frac{\mathbf1_{E_i}(q)\Pi_q(\chi_a)}{m_i(\chi_a)}.
\tag{5.2}
$$

引理 2.1 已给投影态的整记录块支撑及零投影质量，因此此即时后验等于同一个 $\Pi(M_i\chi_a)$，恰好等价于原 R。这里不需要先付细节点。零质量分支不指定条件态；零投影不评价 $\Pi(0)$。

若实际读后过去更细，仍须另供

$$
\Pr(Q_+=q\mid\mathcal G_+)=\Pi_q(M_I\chi_a),\qquad
\mathcal G_+\supseteq\mathcal G_-\vee\sigma(I).
\tag{5.3}
$$

塔性质使它推出即时相容性；仅有数学 R 不反向供应真实细档案上的 (5.3)。原档案按 III (145.4) 的标准 Borel 因果核保留，核只依赖已发生的可读过去和实际请求，不改变向量或配置，使用独立新种子；发射时点、次数与缺席也不能泄露额外隐藏配置或跳时。其它档案必须独立证明同样充分性。

**推论 5.2（有限校准前件下的原记录与旧标签预测）。** 设 $\Pi\in\mathscr C_{\rm cal}$ 且原实际 R 成立。另供定义 5.1 的同源实际接口、每个原调用接缝和真实细档案上的同密度条件充分性、共同因果配置过程存在、原纯投影更新及旧终端字面报告
$W=(b_{-1},\ldots,b_8)(Q)$。则在原理想零失败范围中，对全部
$a\in\mathsf W_{11}$、$f\in\mathsf W$、$i=0,1$、$w\in\Omega_{10}$，

$$
\begin{aligned}
\Pr_{\mathsf T(a)}(w)&=\|N_w\chi_a\|^2,\\
\Pr_{\mathsf R(a,f)}(I=i)&=\|M_i\chi_a\|^2,\\
\Pr_{\mathsf R(a,f)}(i,w)&=\|N_wK_fM_i\chi_a\|^2.
\end{aligned}
\tag{5.4}
$$

**证明。** 定理 2.2 先给完整配置 Born；再按 III174、VIII5.2 的既有条件消费者逐标签归组。第一式由终端配置律推前，第二式由原记录归组；正质量 $i$ 分支实际后继为 $M_i\chi_a/\sqrt{t_i}$，终端条件质量为 $\|N_wK_fM_i\chi_a\|^2/t_i$，乘记录质量 $t_i$ 即得第三式。零质量块整体取零，不评价条件态。

若 $B$ 为记录后、终端前全部实际细档案的可测事件，在已给的细档案充分性下，正质量分支的实际归一核为 $\nu_{a,i,f}$，则仍按原核得到

$$
\Pr_{\mathsf R(a,f)}(i,B,w)
=\nu_{a,i,f}(B)\|N_wK_fM_i\chi_a\|^2.
\tag{5.5}
$$

分阶段档案逐次使用各自真实条件核，终端后的档案另接其给定可读过去的核；零质量块不指定 $\nu$。核的数值和不同程序的真实调用记录没有被选择定理等同。对全部档案积分后，II (121.2) 的既有矩阵事件签名给原两类程序的相应 Born 事件律。全部 $1024$ 标签及完整结果空间保留，失败、拒绝、停止和告警在此理想范围内为零质量，未作成功后选择。∎

**定义 5.3（有限取得、误差与物理未得桥）。** II100.2–100.3 的资源仍为原十三维系统、四个附加 $\tau$ 的真空 ready、完整 $89$ 维载体、四个新增前地址、固定取得字、原计算记录仪器和整个旧终端。其 Born 比较模型及原相干误差合同中，$\delta=\varepsilon_A+\varepsilon_T$ 给向量误差至多 $\delta$、完整记录—终端 TV 至多 $\delta$、代码补空间质量至多 $\delta^2$；$\delta<\sqrt b$、$b=\min_i r_i$ 时，记录分支为正且归一射线误差至多 $2\delta/\sqrt{r_i}$。对原全部 $p,f$ 的量词不变；原正向调用上界仍是 $|p|+|f|+9L_A+9sL_T$，长度逐精度有限，没有统一数值或复杂度结论。

II101、104–106、111–113、117–118 的可靠性、概率匹配和有限供应各在原域承担；有噪初始化和全部调用误差须加入共同累计预算。实际报告、后继、终端、档案、失败、拒绝、停止和告警均留在完整误差账中，不由数学端点等式获得其实现保证。可靠重复准备、抽样、置信和有限认证也须另供。

复 Hilbert 载体、内积、相位规范、十一精确矩阵、连续同射线规则、有限基态校准、端点关系和 R 的实际成立性仍是模型输入。所减少的是节点前件，不是这些输入的经验来源。过程存在、内部率和路径、驱动及滤过也未由密度选择确定；III177–182、190–194 与 V 的过程结论仍保留各自自主律、正活动、最小性、共同未来核或逆纤维前件。本结果不推导任意 POVM、任意 CP 仪器、混态仿射、独立张量复合、物理时钟或全部动力学；唯一 $\Omega$ 的名称不替代这些实现桥。

## 6. 三实坐标数学截面与完整射影几何

**命题 6.1（两个方向的球面截面及全维纤维）。** 固定任一原九号活动对 $r,r^+$，仅作数学截面取
$z=\beta e_r+\gamma e_{r^+}$、$|\beta|^2+|\gamma|^2=1$。令

$$
X=2\operatorname{Re}(\overline\beta\gamma),\quad
Y=2\operatorname{Im}(\overline\beta\gamma),\quad
Z=|\beta|^2-|\gamma|^2.
\tag{6.1}
$$

则 $X^2+Y^2+Z^2=1$。在定理 2.2 的条件下，两配置权重为 $(1+Z)/2,(1-Z)/2$；相对相位仍由 $X,Y$ 表示。原 $Q_*$ 的球轴为
$n=(2xy,0,x-x^2)$、$|n|=1$。这是全域内一个 $\mathbb{CP}^1$ 的三实坐标表示，截面实维为二，整个 $X=\mathbb{CP}^{88}$ 的实维为 $176$。

令 $t=t_0=\|M_0z\|^2/\|z\|^2$。固定 $0<t<1$ 的完整射影纤维为

$$
\mathcal O_t=
\left(\sqrt t\,S^{109}\times\sqrt{1-t}\,S^{67}\right)/U(1)_{\rm diagonal}.
\tag{6.2}
$$

它实维为 $175$；再加质量参数才得到 $176$。端点精确为

$$
\mathcal O_0=\mathbb P(M_1\mathcal K)=\mathbb{CP}^{33},\qquad
\mathcal O_1=\mathbb P(M_0\mathcal K)=\mathbb{CP}^{54}.
\tag{6.3}
$$

**证明。** 展开 (6.1) 得球面恒等式，定理 2.2 给两权重。$4x^3+(x-x^2)^2=(x+x^2)^2=1$ 给轴长；$Q_*=(I+n\cdot\sigma)/2$ 是原二维投影的标准表示。原完整门限制到该截面为相应固定酉转动。

全域中 $\dim_{\mathbb C}M_0\mathcal K=55$、$\dim_{\mathbb C}M_1\mathcal K=34$。固定 $t$ 后，单位代表的两块分别在所示两个球面上；射影化仅商去同一个整体相位，故得到 (6.2)，相对相位不被商掉。$t=0$ 只余第二块，$t=1$ 只余第一块，给 (6.3)。共同块群在这些纤维上传递的接口正是 III144；这里不另建物理控制。

细化证明使用同一载体的另一个 $34/21/34$ 分解，尾块工具使用原 $21/21/13/21/13$ 分解。它们没有删去 $63$ 维代码补空间，也没有把同型旁观块改成独立因子。球面、全域纤维和函数自变量的相位代换各有不同对象，均不把实际系统缩为三维。∎

**定义 6.2（候选约束的完整白话）。** 仍是同一个八十九维装置、同一个起点、原来的十一种前操作、七种后操作和全部记录。先只校准八十九个单独基态：如果输入确是某一个配置基态，就确定地给它全部权重；不再预先规定所有叠加态中“幅度为零就必须零权重”。要求每做完一个原完整门，该门原来能相互连接的每一组配置的总权重守恒，连被阻塞的单点也算在内；再要求读出并保留原记录时，读前某配置的权重，等于记录这一边的总权重乘以同一规则给出的投影后权重。两个关系始终约束同一套规则。已有共同作用先把基态校准传播到整个记录块和一个二十一维尾块，堵住这些块外的权重漏出；九号门再将成对细方向接成同一个函数，完整门的端点关系迫使这个函数满足平行四边形恒等式。每根基轴上有限的零值因此足够逐一排除其它方向，八号门最后固定九号门阻塞的二十一个点。于是全部权重只能是幅度平方，所有零幅度的零权重也一起成为结论。确有另一套固定连续规则保留全部基态校准和全部原门分量，却在一个零幅度配置上给正权重；它失败的正是完整保留读相容性。这说明减少节点前件有真实内容。球面只画两个方向，整个装置、相对相位、代码补空间、档案、失败和取得费用都还在；数学上选出唯一权重后，仍须另接同一实际过程、字面报告、纯更新和细档案充分性，才能得到原程序的实际概率。

## 7. 数学引文、新增范围与未决条件

**定义 7.1（源特定增量与成熟工具的归属）。** 本卷的 repo-derived 增量是：引理 2.1 从有限基态校准传播所需整块支撑，定理 2.2 用有限基轴校准恢复全部细节点并完成原 R 的充要选择，以及定义 3.1、定理 3.2 的负号扇区固定密度和严格裸包含。一般群轨道不变函数、连续延拓、非负等差消元、条件概率和 Bloch 几何均只作为这些新推导的中间步骤，不另列为新的经典定理，不申报全球原创。

正式数学引文及其精确用途如下。

| 来源 | 消费范围与前提边界 |
| --- | --- |
| [固定 II][II] §§77、100、117–118、121；[固定 V][V] §1 | 原路径载体、唯一 ready、$J,M_i,N_w$、全部标签及原取得、档案和误差范围。V 的平方最小率与恢复结论不作本密度选择的前件。 |
| [固定 III][III] (144.8)–(144.12)、(144.16)、(144.19)，III173.5–173.9 | 共同 $55/34$ 块群、ready 射线稠密性、交空间及粗函数接口。引理 2.1 重新供应粗支撑，未直接套用含节点的完整选择定理。 |
| 固定 III151.1–151.2，特别 (151.3)–(151.4) | 原尾 $010$ 的 $PU(21)$ 投影传递性；一个 $21$ 维和一个 $13$ 维限制的联合闭包。三个 $21$ 维副本及两个 $13$ 维副本始终同步，不给旁观块独立控制。 |
| [Freedman–Larsen–Wang][FLW]，Theorem 0.1，§2 Definitions 1–2、Lemma 2.1 | literature-attested：$r\ge5,r\ne6,10,n\ge3$ 时 Jones 直和闭像包含各可容许扇区 $SU$ 的乘积。本源用 $r=5$、$n=8,10,12$，形状依次为 $[5,3],[4,4]$；$[6,4],[5,5]$；$[6,6]$，行差均不超过 $3$。III144、151 已核同规范路径对应，共同标量由模十有限指数子群处理，逆字母用 $K_j^{-1}=K_j^9$ 表为正向字。只复用这条成熟桥，不使用原文 §6 的印刷矩阵替换本源规范。 |
| 固定 III157.1–157.2、164.1–164.4、173.10–173.24；[VIII][VIII] (2.14)–(2.17) | 原全部分量、奇位扇区不变数据、固定九号端点及纯函数平衡桥。VIII2.1 的主定理仍含节点，VIII (2.13)、(2.18)、(2.20) 的节点步骤均不直接套用；本卷分别给新桥。 |
| 固定 III174–176；VIII §5 | 直接复用同源实际条件律、保留报告及细档案充分性的区分；报告语法与纯后继名称不自动供应条件充分性。 |
| [Busch][Busch]，正文 (P1)–(P3) 及其 Theorem | literature-attested 的对照框架：在全部效果上给正、归一、可加的广义概率测度，从而得到密度算子。本卷没有给未知响应在全部效果上的可加延拓，故不直接套用该定理，也不把本源固定菜单的结果说成任意 POVM 的推导。 |

**定义 7.2（相关正式结果的不同前件及开放边界）。** [公开 VII][VII] 研究实际前缀对的局部连续关系与单事件插读，保留其完整操作模型中的终端前件；[公开 VI][VI] §9 和[公开 III195][IIIcurrent] 分别在既有终端／纯更新模型和全码记录校准条件下刻画记录质量。它们不供应这里未知全 $89$ 坐标密度的细节点。VIII 的端点选择保留全节点，III177.2、III179 的自主律路线保留自己的节点、正性与动力学前件，均没有作为无节点入口。III157–166 的多项式及全连续反密度，III190–194 的生成元逆问题也各保留原范围。

本卷的精确无节点选择与裸类严格性已由上述纸面证明给出；不由定向数学引文宣称全部最新理论或全球文献排重完成。近似 R 的统一稳定界、统一检测字长、有限样本认证，以及继续删减校准、地址或分量的最小条件仍未解决。实际来源为何满足有限校准、连续性、端点关系与同密度充分性，复结构、组合、时间和完整动力学怎样取得，仍是须另供条件或继续研究的桥。数学唯一性、可定义性、实际可取得性和可靠认证是不同命题。

[II]: https://github.com/the-omega-institute/trureturing/blob/46927cc328c58a872092e1d1c3bf102e48fa0426/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md
[III]: https://github.com/the-omega-institute/trureturing/blob/46927cc328c58a872092e1d1c3bf102e48fa0426/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md
[V]: https://github.com/the-omega-institute/trureturing/blob/46927cc328c58a872092e1d1c3bf102e48fa0426/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_V.md
[VI]: https://github.com/the-omega-institute/trureturing/blob/f47ba12c91744e87f89f05ef1db7df1f6ddd9f95/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_VI.md
[VII]: https://github.com/the-omega-institute/trureturing/blob/f47ba12c91744e87f89f05ef1db7df1f6ddd9f95/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_VII.md
[VIII]: https://github.com/the-omega-institute/trureturing/blob/d9631873d125955c8434f12e8695256148a72857/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_VIII.md
[IIIcurrent]: https://github.com/the-omega-institute/trureturing/blob/f47ba12c91744e87f89f05ef1db7df1f6ddd9f95/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md#195-原生守恒的码锚校准与一次删址反例
[FLW]: https://arxiv.org/html/math/0103200v1
[Busch]: https://arxiv.org/html/quant-ph/9909073v3

## 追加锚（本行以下为增补区）

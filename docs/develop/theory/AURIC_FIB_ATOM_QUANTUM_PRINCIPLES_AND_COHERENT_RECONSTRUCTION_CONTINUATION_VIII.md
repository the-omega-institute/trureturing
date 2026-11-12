# AURIC：完整原生门端点与保留读的八十九坐标密度选择

## 1. 固定来源、完整密度域与二元关系

**定义 1.1（源与新增命题的范围）。** 本卷的原数学源为提交 `46927cc328c58a872092e1d1c3bf102e48fa0426` 的[续卷 II][II46927]、[续卷 III][III46927]及[续卷 V][V46927]。沿用 III138.1、145.1、157.1 的同一个对象：

$$
\begin{gathered}
E=\{q\subseteq\{1,\ldots,9\}:q\text{ 不含相邻整数}\},\qquad
\mathcal K=\mathbb C^E,\quad |E|=89,\\
b_k(q)=\mathbf1_{k\in q},\qquad
b_{-1}b_0=10,\quad b_{10}b_{11}b_{12}=010,\\
H=V_8^{\mathbf1},\quad \dim H=13,\qquad
J:H\otimes\mathbb C^2\longrightarrow\mathcal K,\\
\mathcal C=\operatorname{ran}J,\quad \dim\mathcal C=26,\quad
\dim\mathcal C^\perp=63,\qquad
R_0\psi=J(\psi,0),\quad v=e_{00100}.
\end{gathered}
\tag{1.1}
$$

实际来源只有 $R_0v$。记 $\mathsf W_{11}=\{0,\ldots,10\}^{<\infty}$、$\mathsf W=\{0,\ldots,6\}^{<\infty}$，$\chi_a=K_aR_0v$；按实际先后连接，$K_{aj}=K_jK_a$。程序仅为原 $\mathsf T(a)$ 和 $\mathsf R(a,f)$：前者执行 $a$ 后用旧终端；后者执行 $a$、读取并保留 $b_9$、执行不依赖该结果的外生 $f\in\mathsf W$，再用旧终端。全部实际调用、时间、细档案及失败坐标保留。$M_i$ 是 $b_9=i$ 的投影，$N_w$ 是旧十位 $(b_{-1},\ldots,b_8)=w$ 的投影，$w\in\Omega_{10}=\{0,1\}^{10}$；无合法路径的标签仍取零投影。所有 $1024$ 标签及整个 $63$ 维补空间均在域内。

III173.2 已在全时密度类中证明保留读关系与全部坐标平方律等价。该证明的粗质量部分 (173.4)–(173.9) 只需完整门；细坐标部分 (173.15)–(173.19) 使用 (173.18) 供应的非整数内部平衡时刻。本卷新增的是删除这个全时前件后的源特定加强，以及新旧裸类严格不同的固定密度见证。III144 的群桥、粗函数推导，III164 的奇偶扇区工具，经典条件概率和二次几何均直接复用。

[当前正式 III195][IIIbase] 从全码记录校准和记录守恒推出粗记录质量；[续卷 VI][VIbase] §§1–8 处理两个固定字，§9 则在已给全标签终端 Born 的操作模型中删除记录前件。它们没有以下未知 $89$ 坐标密度的端点分类前件与结论。III157–166 的多项式分类及全时反密度、III177–182 的自主率／全时等变族、III190–194 的生成元逆纤维也各保留自己的前件；这里不把那些结果重报为新结论。

**定义 1.2（原矩阵与原分量）。** 全部十一地址严格采用 III (157.2)：

$$
\begin{gathered}
\varphi=(1+\sqrt5)/2,\quad x=\varphi^{-1},\quad y=\sqrt x,\quad
x+x^2=1,\quad \alpha=3\pi/5,\quad\zeta=e^{i\alpha},\\
Q_* =\begin{pmatrix}x&xy\\xy&x^2\end{pmatrix},\qquad
\mathcal P_j=n_{j-1}n_{j+1}
 +(1-n_{j-1})(1-n_{j+1})(Q_*)_{b_j},\\
H_j=-\alpha(I+\mathcal P_j),\qquad
U_j(t)=e^{-itH_j},\qquad
K_j=U_j(1)=\zeta[I+(\zeta-1)\mathcal P_j].
\end{gathered}
\tag{1.2}
$$

这里 $n_k$ 是位占据投影，固定外位按字面代入。$\mathscr B_j$ 始终是原 $H_j$ 支撑图的全部连通分量。III157.2 的支撑描述为：$1\le j\le9$ 且两邻位均为零时，固定其它位、翻转中心位所得两点为一分量；至少一个邻位占据时，中心只能为零，是阻塞单点。两邻位都占据或恰一占据时，单点上的 $\mathcal P_j$ 分别为 $1$ 或 $0$。两个边界地址有 $\mathcal P_0=n_1$、$\mathcal P_{10}=n_9$，各有全部 $89$ 个单点分量。这些分量不由 $K_j$ 的偶然谱重数重新划分。

**定义 1.3（端点裸类）。** 令 $X=\mathbb P(\mathcal K)=\mathbb{CP}^{88}$。$\mathscr C_{\rm end}$ 由同一个连续映射 $\Pi:X\to\Delta(E)$ 组成，其向量提升满足

$$
\begin{gathered}
\Pi_q(\lambda z)=\Pi_q(z)\quad(\lambda\in\mathbb C\setminus\{0\}),\qquad
z_q=0\ \Longrightarrow\ \Pi_q(z)=0,\\
\sum_{q\in B}\Pi_q(K_jz)=\sum_{q\in B}\Pi_q(z)
\quad(z\ne0,\ j=0,\ldots,10,\ B\in\mathscr B_j).
\end{gathered}
\tag{1.3}
$$

$\Delta(E)$ 指逐坐标非负且总和为一。没有可微性、有限次数、径向性、可分性、未知算子正性、节点外严格正性或内部 $t$ 方程。旧 $\mathscr C_{\rm nat}$ 是在相同域、节点和概率条件上，把 (1.3) 最后一行换成 III (157.3) 的全部 $t\in[0,1]$。

**定义 1.4（同一密度的实际保留读关系）。** 记

$$
E_i=\{q:b_9(q)=i\},\qquad
m_i(z)=\sum_{q\in E_i}\Pi_q(z),\qquad
t_i(z)=\frac{\|M_i z\|^2}{\|z\|^2}.
\tag{1.4}
$$

$\mathrm R$ 严格为 III (173.2)：

$$
\Pi_q(\chi_a)=m_i(\chi_a)\Pi_q(M_i\chi_a)
\quad(a\in\mathsf W_{11},\ i=0,1,\ q\in E_i).
\tag{1.5}
$$

$M_i\chi_a=0$ 时右端为零，不定义 $\Pi(0)$。它约束的是整体密度与同一记录投影后密度之间的二元条件关系，不是两个独立选出的边缘；$m_i$ 也从同一个 $\Pi$ 求和，不能另供一份 Born 记录权重。数学式 (1.5) 本身尚不赋予 $m_i$ 实际报告概率的含义。记录、保留配置、纯投影后继与可读历史充分性的连接见 §5。

## 2. 从完整端点恢复全部细坐标

**定理 2.1（端点与原实际 R 的完整选择）。** 对每个 $\Pi\in\mathscr C_{\rm end}$，有

$$
\mathrm R\quad\Longleftrightarrow\quad
\Pi_q(z)=\Pi_q^{\rm B}(z):=\frac{|z_q|^2}{\|z\|^2}
\quad(q\in E,\ z\ne0).
\tag{2.1}
$$

正向推导只使用 (1.3) 的完整门端点、(1.5)、连续性及 III144 已有的源矩阵结论；不输入任何旧内部时刻分量方程。所有相位、零投影、部分支撑和阻塞单点均包含在结论内。

**证明。** 首先直接复用 III (173.4) 的延拓方法。对固定 $i,q\in E_i$，令

$$
L_{iq}(z)=m_i(z)\Pi_q(M_i z)\quad(M_i z\ne0),\qquad
L_{iq}(z)=0\quad(M_i z=0).
$$

非零分支连续；趋于零投影时，节点给极限处 $m_i=0$，而 $0\le L_{iq}\le m_i$，故整个射影域上连续。III (144.12) 给

$$
\overline{\{[\chi_a]:a\in\mathsf W_{11}\}}=X.
\tag{2.2}
$$

因此 (1.5) 在所有 $z\ne0$ 上成立。这里延拓的是连续函数恒等式，不增加实际准备。

粗质量沿用 III (173.5)–(173.9) 对 III144.3 的消费，列明全部输入。令 $Q=n_1$，$q_A(z)=\sum_{b_1(q)=1}\Pi_q(z)$。因为 $j\le8$ 的每个原分量留在一个 $E_i$ 内，$j\ge2$ 的每个原分量留在一个 $b_1$ 扇区内，端点式 (1.3) 与刚取得的全域 R 给

$$
\begin{aligned}
m_i(K_jz)&=m_i(z) &&(0\le j\le8),\\
q_A(K_jz)&=q_A(z) &&(2\le j\le10),\\
q_A(z)&=\sum_{i:M_i z\ne0}m_i(z)q_A(M_i z).
\end{aligned}
\tag{2.3}
$$

节点与归一化使 $q_A$ 在 $\ker Q$ 为零、在 $\operatorname{ran}Q$ 为一。III (144.9)、(144.11) 已供应同一字作用的两个乘积群

$$
\begin{aligned}
SU(M_0\mathcal K)\times SU(M_1\mathcal K)
&\subseteq\overline{\{K_g:g\in\{0,\ldots,8\}^{<\infty}\}},\\
SU(\ker Q)\times SU(\operatorname{ran}Q)
&\subseteq\overline{\{K_h:h\in\{2,\ldots,10\}^{<\infty}\}}.
\end{aligned}
\tag{2.4}
$$

连续不变性及第二个乘积群的逐向量传递性给 $q_A(z)=G(\|Qz\|^2/\|z\|^2)$，其中 $G$ 连续、$G(0)=0,G(1)=1$。这包括两个非零块的相对相位，不能用两个分别射影的像来替代 (2.4)。在单位输入的 $t=\|M_0z\|^2\in(0,1)$ 纤维中，第一个乘积群保持 $m=m_0(z)$；III (144.16) 的四交空间维数

$$
\begin{array}{c|cc}
 & I-Q & Q\\\hline
M_0&34&21\\
M_1&21&13
\end{array}
$$

使两个条件 $Q$ 质量可同时趋于任意 $r_0,r_1\in[0,1]$。因此 (2.3) 最后一式正好给旧函数方程

$$
G(tr_0+(1-t)r_1)=mG(r_0)+(1-m)G(r_1).
\tag{2.5}
$$

取 $(r_0,r_1)=(1,0),(0,1)$ 得 $m=G(t)$、$1-m=G(1-t)$。再取 $t=1/2$，即得 $G(1/2)=1/2$ 与中点方程；复用 III (144.19) 后的二进有理插值与连续性，$G(s)=s$。$t=0,1$ 则直接由节点和归一化处理。故

$$
m_i(z)=t_i(z)\quad(z\ne0).
\tag{2.6}
$$

至此只用了端点式；没有使用假设 138.2 的终端概率或档案充分性。

如 III (173.10)，在全部向量上引入辅助函数

$$
F_q(z)=\|z\|^2\Pi_q(z)\quad(z\ne0),\qquad F_q(0)=0.
\tag{2.7}
$$

$0\le F_q(z)\le\|z\|^2$，所以零点连续；它满足 $F_q(\lambda z)=|\lambda|^2F_q(z)$。全域 R 与 (2.6) 给

$$
F_q(z)=F_q(M_i z)\quad(q\in E_i),\qquad F_q(e_q)=1.
\tag{2.8}
$$

零投影处由节点得第一式；第二式由基向量处其它输出全为零及归一化得出。这只给 $F_q(0)$，仍未定义 $\Pi(0)$。

沿用 III (173.12) 的坐标分解

$$
\begin{aligned}
\mathsf A&=\{b_8=b_9=0\},&|\mathsf A|&=34,\\
\mathsf B&=\{b_8=1,b_9=0\},&|\mathsf B|&=21,\\
\mathsf C&=\{b_9=1\},&|\mathsf C|&=34.
\end{aligned}
\tag{2.9}
$$

翻转第九位识别 $\mathsf A$ 与 $\mathsf C$，写 $z=(u,w,v)$。这里只固定端点块

$$
T=I+(\zeta-1)Q_*=
\begin{pmatrix}A&B\\B&D\end{pmatrix},\quad
A=1+(\zeta-1)x,\quad B=(\zeta-1)xy,\quad D=1+(\zeta-1)x^2.
\tag{2.10}
$$

它酉，且 $|B|^2=x$、$|A|^2=|D|^2=x^2$，特别 $B\ne0$。这些是 III (173.13)、(173.18) 在 $t=1$ 的精确值；也可由 $|\zeta-1|^2=4\sin^2(3\pi/10)$ 及 $x+x^2=1$ 直接取得。地址九作用为

$$
\zeta^{-1}K_9(u,w,v)=(Au+Bv,\ w,\ Bu+Dv).
\tag{2.11}
$$

$\mathsf B$ 中每个点为 $\mathcal P_9=0$ 的阻塞单点；另外 $34$ 对恰是原活动分量。

固定任一原配对 $r\in\mathsf A$、$r^+=r\cup\{9\}\in\mathsf C$，令

$$
f_0(u,w)=F_r(u,w,0),\qquad f_1(v)=F_{r^+}(0,0,v).
$$

由 (2.8)、地址九这个分量的端点守恒和 $|\zeta|=1$，

$$
f_0(Au+Bv,w)+f_1(Bu+Dv)=f_0(u,w)+f_1(v).
\tag{2.12}
$$

取 $u=0$。节点给 $f_0(0,w)=0$，二齐次性给

$$
f_0(Bv,w)=(1-|D|^2)f_1(v)=|B|^2f_1(v)=f_1(Bv).
\tag{2.13}
$$

因 $B\ne0$，$Bv$ 遍历整个 $\mathbb C^{34}$，故 $f_0(u,w)=f_1(u)$。记此共同函数为 $f$；它非负、复二齐次，在第 $r$ 坐标为零时为零，且 $f(e_r)=1$。式 (2.12) 变成

$$
f(Au+Bv)+f(Bu+Dv)=f(u)+f(v).
\tag{2.14}
$$

下面从这个固定端点恒等式推出精确中点，补足所需细坐标桥。令 $S_f(u,v)=f(u)+f(v)$。式 (2.14) 意味着 $S_f(T(u,v))=S_f(u,v)$；对任意输入作代换即也有 $T^{-1}=T^*$ 下的不变性。复二齐次性还使 $S_f$ 在任意 $D_\phi=\operatorname{diag}(e^{i\phi},1)$ 下不变。因此它在

$$
W_\phi=T^*D_\phi T
\tag{2.15}
$$

下不变。列正交给 $\overline A B+\overline B D=0$，故

$$
(W_\phi)_{12}=\overline A B(e^{i\phi}-1),\qquad
|(W_\phi)_{12}|^2=4x^3\sin^2(\phi/2).
\tag{2.16}
$$

由 $x^3=\sqrt5-2$ 及 $\sqrt5>17/8$，有 $4x^3>1/2$。于是存在 $\phi\in(0,\pi)$ 使 $\sin^2(\phi/2)=1/(8x^3)$。这个 $W_\phi$ 酉且四项模长均为 $1/\sqrt2$。在左右分别乘对角单位相位，可先把第一行调成 $(1,1)/\sqrt2$；行正交再把第二行调成 $(1,-1)/\sqrt2$。这些相位均由 $f$ 的二齐次性消去，因而得到

$$
f(u+v)+f(u-v)=2f(u)+2f(v).
\tag{2.17}
$$

这里的 $D_\phi$ 是两个函数自变量的标量相位代换，$W_\phi$ 是由既有函数恒等式导出的数学组合；没有声称它们是原装置的一段可执行控制，也没有使用 $U_9(t)$ 的任何内部不变性。精确平衡来自 (2.14) 与二齐次性，而不是旧 (173.18) 的内部 $t_*$。

现在复用 III (173.19)–(173.20) 的非负中点论证。若 $h_r=0$，节点给 $f(h)=0$。对固定 $u$，$g_n=f(u+nh)$、$n\in\mathbb Z$ 满足 $g_{n+1}+g_{n-1}=2g_n$，所以是一条等差数列；两向非负迫使公差为零。故 $f(u+h)=f(u)$。取 $h=-u+u_re_r$，得

$$
f(u)=f(u_re_r)=|u_r|^2.
\tag{2.18}
$$

每一对独立重复此论证，就得到所有 $q\in\mathsf A\cup\mathsf C$ 的 $F_q(z)=|z_q|^2$。未假设 $f$ 是二次型，也未把其它 $33$ 个坐标或其相位先行删去。

余下 $q\in\mathsf B$。由 (2.8)、(2.11) 及地址九每一个阻塞单点的端点守恒，

$$
F_q(Au+Bv,w,0)=F_q(u,w,0).
\tag{2.19}
$$

取 $u=0$、让 $v$ 任意变化，得 $F_q(z)=g_q(w)$。对这样的 $q$，合法性迫使 $b_7=b_9=0$，地址八把它与 $q^-=q\setminus\{8\}\in\mathsf A$ 配成原活动对。置 $\delta_q(z)=F_q(z)-|z_q|^2$。这对的端点守恒、参考平方对和守恒及已得 $\delta_{q^-}=0$ 给

$$
\delta_q(K_8z)=\delta_q(z).
\tag{2.20}
$$

令 $\mathsf D=\{b_7=b_8=b_9=0\}\subseteq\mathsf A$，与全部 $21$ 个 $\mathsf B$ 点按翻转第八位配对。给定任意 $w\in\mathbb C^{\mathsf B}$，取输入的 $\mathsf D$ 坐标为 $-(D/B)w$、$\mathsf B$ 坐标为 $w$、其余为零。地址八仍用同一端点 $T$，故输出的整个 $\mathsf B$ 向量为 $\zeta(B(-D/B)w+Dw)=0$。由节点，输出处 $\delta_q=0$；由 (2.20) 及 $F_q=g_q(w)$，得到 $g_q(w)=|w_q|^2$，包括 $w=0$。三个块穷尽全部 $89$ 坐标。所有代换都在全向量数学域中，不需要实际制备这些输入。

反向直接复用 III157.2 的参考分量不变性：每个原 $P_B$ 与相应 $H_j$ 对易，$K_j$ 酉，故分量及总平方范数不变。$\Pi^{\rm B}$ 连续、射线不变、非负归一且满足节点，因此属于 $\mathscr C_{\rm end}$。$M_i z\ne0$ 时

$$
t_i(z)\frac{|z_q|^2}{\|M_i z\|^2}=\frac{|z_q|^2}{\|z\|^2}\quad(q\in E_i);
$$

零投影时按零乘积处理。所以它满足全域 R，特别满足全部实际有限前字上的 R。∎

## 3. 一个固定全域密度证明裸类严格扩大

**定义 3.1（有限偶端点轨道上的节点上界）。** 复用 III164.1–164.3 的奇位集合及符号：

$$
\begin{gathered}
O=\{1,3,5,7,9\},\quad S=\{s:s\subseteq O\},\quad
J_{\rm ev}=\{0,2,4,6,8,10\},\\
c_q=\begin{cases}(-1)^{|q|},&q\in S,\\0,&q\notin S.\end{cases}
\end{gathered}
\tag{3.1}
$$

所有偶地址矩阵互相对易：它们只改变不同的偶中心位，控制只依赖不改变的奇位；边界 $n_1,n_9$ 亦如此。每个 $\mathcal P_j$ 为投影且 $\zeta^{10}=1$，故 $K_j^{10}=I$。于是

$$
\mathcal G_{\rm ev}=
\left\{\prod_{j\in J_{\rm ev}}K_j^{m_j}:m_j\in\{0,\ldots,9\}\right\}
\tag{3.2}
$$

是一个固定有限酉群，包含恒等元。定义同一个全域函数及密度

$$
h_{\rm end}(z)=\min_{g\in\mathcal G_{\rm ev},\ s\in S}
\frac{|(gz)_s|^2}{\|z\|^2},\qquad
\widehat\Pi_q(z)=\frac{|z_q|^2}{\|z\|^2}+\frac12c_qh_{\rm end}(z).
\tag{3.3}
$$

这不是随输入、程序或地址改选的密度；有限最小值中的全部矩阵已由原十一端点固定。

**定理 3.2（严格包含与一条确定的旧内部关系失效）。** 式 (3.3) 满足

$$
\widehat\Pi\in\mathscr C_{\rm end}\setminus\mathscr C_{\rm nat},\qquad
\mathscr C_{\rm nat}\subsetneq\mathscr C_{\rm end}.
\tag{3.4}
$$

失效可固定为地址 $2$、原分量 $B_* =\{\varnothing,\{2\}\}$ 及内部时刻 $\tau=\sqrt2/2$。加入原 R 后，两类的成功密度完全相同：

$$
\{\Pi\in\mathscr C_{\rm nat}:\mathrm R\}
=\{\Pi\in\mathscr C_{\rm end}:\mathrm R\}
=\{\Pi^{\rm B}\}.
\tag{3.5}
$$

**证明。** 因恒等元在群内，对每个 $s\in S$ 都有 $0\le h_{\rm end}(z)\le |z_s|^2/\|z\|^2$。故 $\widehat\Pi_q\ge\tfrac12|z_q|^2/\|z\|^2$，并且满足节点。又 $\sum_qc_q=(1-1)^5=0$，所以总和为一。有限最小值连续，非零复缩放对每一项均无影响，因而密度定义在整个 $X$。不作节点除法或全支撑限制。

右乘任一偶地址 $K_j$ 置换 $\mathcal G_{\rm ev}$，所以 $h_{\rm end}(K_jz)=h_{\rm end}(z)$。任一原偶地址分量，无论单点或二点，其修正和为 $\tfrac12h_{\rm end}\sum_{q\in B}c_q$，端点不变。特别覆盖边界地址零、十的全部单点。

若 $j$ 为奇地址，每个交 $S$ 的原分量都是 $\{s,s\mathbin\triangle\{j\}\}\subset S$；两个邻位都是零，固定外邻位 $b_0=b_{10}=0$ 亦包括在内。两个 $c$ 相反，修正对和恒为零。其它活动对或阻塞单点不交 $S$，其修正也为零。因此全部奇地址分量同样满足端点式，无需假设 $h_{\rm end}$ 在奇地址下不变。加上参考平方分量恒等式，得到全部十一地址、全部原分量的 (1.3)。

以下给出同一密度的明确严格性输入。沿用 III (164.3) 的实际载体内单位向量

$$
\begin{gathered}
A_s=\{j\in\{2,4,6,8\}:j-1,j+1\notin s\},\quad m_s=|A_s|,\\
w_s=\sum_{r\subseteq A_s}x^{m_s-|r|}(-y)^{|r|}|s\cup r\rangle,\qquad
\kappa_s=x^{m_s}>0.
\end{gathered}
\tag{3.6}
$$

这些向量支撑在互不相交的奇位扇区中，覆盖全部 $E$；$\|w_s\|=1$，$\langle s|w_s\rangle=\kappa_s$。III164.2 已证明它们是全部偶地址的共同特征向量，包括两类阻塞单点及两个边界；这些事实直接复用。

令 $T_t=I+(e^{i\alpha t}-1)Q_*$，并固定

$$
\begin{gathered}
\tau=\sqrt2/2,\qquad
\eta=T_{-\tau}\binom01=\binom{\eta_0}{\eta_1},\\
v_\tau=\sum_{r\subseteq\{4,6,8\}}
x^{3-|r|}(-y)^{|r|}
\bigl(\eta_0|r\rangle+\eta_1|\{2\}\cup r\rangle\bigr),\\
z_\tau=\frac1{\sqrt{32}}\left(v_\tau+\sum_{s\in S\setminus\{\varnothing\}}w_s\right).
\end{gathered}
\tag{3.7}
$$

$v_\tau$ 位于空奇位扇区，是单位向量：$\|\eta\|=1$，其余三个二坐标系数各有平方和 $x^2+y^2=1$。所以 $\|z_\tau\|=1$。这只是原 $89$ 坐标的显式和式，不是新物理张量源。

对 $g=\prod K_j^{m_j}\in\mathcal G_{\rm ev}$，当 $s\ne\varnothing$ 时，共同特征向量性质给

$$
|(gz_\tau)_s|=\kappa_s/\sqrt{32}>0.
\tag{3.8}
$$

空扇区内，地址 $4,6,8$ 对各自 $(x,-y)$ 系数的投影为零，边界投影也为零；仅地址 $2$ 改变 $\eta$。略去模长为一的共同相位，$T_1^{m_2}T_{-\tau}=T_{m_2-\tau}$，故

$$
|(gz_\tau)_\varnothing|
=\frac{x^3xy}{\sqrt{32}}
\left|e^{i\alpha(m_2-\tau)}-1\right|>0.
\tag{3.9}
$$

若最后的模为零，则 $m_2-\tau=10k/3$，与 $\tau$ 无理矛盾。式 (3.8)–(3.9) 覆盖有限最小值中每一项，所以 $h_{\rm end}(z_\tau)>0$。特别 $\widehat\Pi_\varnothing(z_\tau)>\Pi^{\rm B}_\varnothing(z_\tau)$。

反之，$U_2(\tau)$ 在空扇区把 $\eta$ 变成共同相位乘 $(0,1)^{\mathsf T}$，其它奇扇区不会进入空扇区，因此

$$
(U_2(\tau)z_\tau)_\varnothing=0,\qquad
h_{\rm end}(U_2(\tau)z_\tau)=0.
\tag{3.10}
$$

第二式只需取最小值中的 $g=I,s=\varnothing$。原 $B_*$ 是地址二的活动分量，且 $\sum_{q\in B_*}c_q=1$。参考平方对和在整个 $U_2(t)$ 下不变，于是

$$
\sum_{q\in B_*}\widehat\Pi_q(U_2(\tau)z_\tau)
-\sum_{q\in B_*}\widehat\Pi_q(z_\tau)
=-\frac12h_{\rm end}(z_\tau)<0.
\tag{3.11}
$$

这违反一条旧 (157.3)，证明严格性。这里使用内部演化只是检验旧类成员身份，不在定理 2.1 中把它当作新类前件。旧类包含于新类由取 $t=1$ 直接得到；(3.5) 则由定理 2.1、Born 属于旧类及 III173.2 得出。∎

## 4. 逐项反事实及前件强弱

**命题 4.1（删除关系与有限限制的后果）。** 下列反事实均保持相应条目中明确保留的同一载体与函数；它们不声称所有充分前件逐项逻辑独立。

1. 删除 R，即使恢复全部旧内部方程，也不能选择 Born：III164.4、165.2 的固定非 Born 密度已属于旧 $\mathscr C_{\rm nat}$。新 (3.3) 还表明，删除内部方程确实扩大裸类；但不能据它声称 R 下也有非 Born 密度。
2. 保留全域 R 而删除全部端点分量方程，同样不能选择 Born。例如 $\Pi_q^{[2]}(z)=|z_q|^4/\sum_r|z_r|^4$ 连续、射线不变、非负归一、满足节点与全域 R，却不是 Born。
3. 将 R 的全部实际前字量词换成任意预先固定的有限集合，即使保留全部端点方程，仍不能选择 Born。可以给出一个对该有限集合固定、对所有端点统一合法的非 Born 密度。
4. 删除旧内部方程、保留端点及原完整 R，不改变成功密度，正是 (3.5)；减少的是一组数学约束，不是门调用、独立信息、样本或实际来源费用的下降。

**证明。** 第一、四项分别由上述既有反例与定理 3.2。第二项的 R 是幂和在记录块上的普通归一化分解。它确实违反本源端点：取 $z=e_\varnothing+e_{\{8\}}$，地址九的活动对 $B_9=\{\varnothing,\{9\}\}$ 在输入的质量为 $1/2$，在输出的质量为

$$
\frac{x^4+x^2}{1+x^4+x^2}<\frac12,
\tag{4.1}
$$

因为 $x^4+x^2=(x^2+x)^2-2x^3=1-2x^3<1$；坐标 $\{8\}$ 是原阻塞单点。故这个反例未偷保留端点合同。

对第三项，设有限前字集合为 $F$，取有限射线集合 $T_F$，包含全部 $[\chi_a]$ 及其非零 $[M_i\chi_a]$，再取其在 $\mathcal G_{\rm ev}$ 下的全部像。为 $\xi\in T_F$ 任取单位代表，置

$$
d_F(z)=\prod_{[\xi]\in T_F}
\left(1-\frac{|\langle\xi,z\rangle|^2}{\|z\|^2}\right),\qquad
h_F(z)=h_{\rm end}(z)d_F(z).
\tag{4.2}
$$

空乘积取一。$0\le d_F\le1$，它连续、射线不变，并因 $T_F$ 被群置换而在全部偶端点下不变。将 (3.3) 的 $h_{\rm end}$ 换成 $h_F$，定义与全分量证明完全适用。在所列实际输入和投影处修正均为零，因此有限集合上的 R 成立。由 (3.8)–(3.9)，$h_{\rm end}>0$ 的集合含非空开集；删去有限射线后仍有点，且这些点的每个乘积因子严格为正。所以新密度仍非 Born。这是一项每个有限集合对应一个固定密度的存在结论，不是让同一密度随运行更改。∎

**定义 4.2（不能从反事实额外冒出的结论）。** 连续性在 (2.2) 的全域延拓、(2.4) 的闭包不变性及粗函数插值处承重；非负性和归一化供应有界乘积、节点分支及 (2.18) 的两向等差论证；复缩放不变性供应二齐次性和 (2.15) 的相位恒等式；细节点供应去背景步骤。若删除其中一项，本定理不再提供相应推导，本卷不把“此证明不再适用”说成该删减类中已存在反例或已证不能唯一。

原单点没有被端点量词自动消去：地址九的全部 $21$ 个阻塞单点用于 (2.19)，地址八的对应活动对用于 (2.20)。不保留这些方程就不能引用本卷的完整细坐标结论。本卷未分类任意删地址／删分量子集，亦未声称所用地址模式绝对最少。地址零至八和二至十的端点由 (2.3) 供应两个已有群桥，地址九、八再完成细化；没有以新定义的支撑替代原图。

式 (3.3)、(4.2) 是裸数学密度，不是满足原完整实际过程合同的非 Born 实现。定理 2.1 反而说明它们必在某个原实际有限前字违反 R。具体说，若所有这样的残差都为零，由连续延拓与定理 2.1 就会是 Born，与其正修正矛盾；因此至少一个实际前字有非零残差。这不给共同字长、有效寻字程序或统一正间隙。

## 5. 原记录、旧终端与完整档案的条件消费者

**定义 5.1（把数学密度接到同一实际来源的合同）。** 直接采用 III174.1–174.2 的分工。对每个原实际 $\mathsf R(a,f)$，若另供读取前可读过去 $\mathcal G_-$ 上的条件律

$$
\Pr(Q_-=q\mid\mathcal G_-)=\Pi_q(\chi_a),
\tag{5.1}
$$

并且字面报告 $I=b_9(Q_-)$、保留 $Q_+=Q_-$、实际纯后继为 $[M_I\chi_a]$，则普通 Bayes 公式在正质量分支给

$$
\Pr(Q_+=q\mid\mathcal G_-,I=i)
=\frac{\mathbf1_{E_i}(q)\Pi_q(\chi_a)}{m_i(\chi_a)}.
\tag{5.2}
$$

所以 R 恰是这个即时条件律等于同一个 $\Pi_q(M_i\chi_a)$ 的条件。若读后过去更细，另需

$$
\Pr(Q_+=q\mid\mathcal G_+)=\Pi_q(M_I\chi_a),\qquad
\mathcal G_+\supseteq\mathcal G_-\vee\sigma(I).
\tag{5.3}
$$

条件期望的塔性质使 (5.3) 推出 (5.2) 的同密度相容性；反向仅有 R 不供应额外档案上的 (5.3)。若 $m_i=0$，不指定该条件分支；若 $M_i\chi_a=0$，节点已给 $m_i=0$，不取零向量上的密度或纯后继。这包括非零投影而实际质量为零的未占据分支。

完整过程还须另供每个原有限调用段的共同因果配置核及其存在性、接缝条件密度充分性，或直接供应整个实际可读历史上的同密度条件律。端点分量等式只给必要质量关系，不构造这个过程，更不选择内部路径或率。额外档案若采用 III (145.4)，其标准 Borel 因果核只依赖已发生的可读过去和实际请求，不改变向量或配置，用独立新种子产生；发射时点、次数与缺席也不能泄露隐藏配置或跳时。否则必须独立证明相同条件充分性。相同纯向量名称、相同硬件地址及信息保留均不能替代这些合同。

**命题 5.2（给定过程充分性后的原预测）。** 设定理 2.1 的全部数学前件成立，并另供定义 5.1 的同源读取合同、所有原调用接缝上的同密度条件充分性、原纯更新及旧终端字面报告 $W=(b_{-1},\ldots,b_8)(Q)$。则在原零失败理想范围中，对全部 $a\in\mathsf W_{11},f\in\mathsf W,w\in\Omega_{10}$，

$$
\begin{aligned}
\Pr_{\mathsf T(a)}(w)&=\|N_w\chi_a\|^2,\\
\Pr_{\mathsf R(a,f)}(I=i)&=\|M_i\chi_a\|^2,\\
\Pr_{\mathsf R(a,f)}(i,w)&=\|N_wK_fM_i\chi_a\|^2.
\end{aligned}
\tag{5.4}
$$

这些是该实际接口下的结论，未将终端 Born 或记录 Born 预付给密度选择定理。

**证明。** 定理 2.1 给全部坐标的平方密度。终端按 $W(Q)$ 归组即给第一式，记录按 $b_9(Q)$ 归组给第二式。正质量 $i$ 分支在实际纯更新后为 $M_i\chi_a/\sqrt{t_i}$；后续 $f$ 仍是原七地址字，由接缝条件充分性，终端条件概率为 $\|N_wK_fM_i\chi_a\|^2/t_i$。乘第二式给第三式。$t_i=0$ 时完整块为零，两边都不评价条件态。

若 $B$ 为全部终端前细档案的可测事件，在已经供应的档案条件充分性下，正质量分支的实际归一核记为 $\nu_{a,i,f}$，则同一推导给

$$
\Pr_{\mathsf R(a,f)}(i,B,w)
=\nu_{a,i,f}(B)\|N_wK_fM_i\chi_a\|^2.
\tag{5.5}
$$

分阶段档案按其真实条件核逐次积分；终端后的档案再接其给定 $(i,w)$ 等可读过去的真实核。零质量块整体取零，不指定 $\nu$。$\mathsf T$ 的档案同理使用自己的真实核。核的数值没有被密度选择确定；不同程序的确定调用记录也没有被识别。式 (5.5) 不把一般可测档案拆成必须正质量的原子。

对全部档案积分并按旧标签求和，II (121.2) 的既有矩阵签名于是给 $\Pr_{\mathsf P}(A)=\langle v,E(\mathsf P,A)v\rangle$，其中 $\mathsf P$ 仅遍历原两类程序，事件 $A$ 是不额外查询细档案的原终端或记录—终端事件。含档案事件仍使用各自核。无合法路径的旧标签为零，所有失败、拒绝、停止和额外告警仍是完整结果空间中的零质量坐标；没有成功后选择。∎

**定义 5.3（取得、误差及尚未供应的来源）。** 本卷保留 II100.3 的整个资源账：原十三维系统、四个附加 $\tau$ 的真空 ready 接口、$89$ 维完整载体、四个新增前地址、取得字、原计算记录仪器及旧十位终端，不删去初始化、调用、读器或档案费用。II100.2 的有限取得在其原 Born 比较模型和相干误差合同下，仍是 $\delta=\varepsilon_A+\varepsilon_T$，向量误差至多 $\delta$，完整记录—终端 TV 至多 $\delta$，代码补空间质量至多 $\delta^2$；$\delta<\sqrt b$（$b=\min_i r_i$）时各记录分支均为正，归一射线误差至多 $2\delta/\sqrt{r_i}$。这些界对原全部 $p,f$ 保持原量词。正向调用数仍按 II (100.7) 为 $|p|+|f|+9L_A+9sL_T$ 的相应上界，各长度逐精度有限，无统一数值或编译复杂度结论。

II101、104–106、111–113、117–118 的其它旧有限供应及误差合同仍各在原域内承担：实际初始化和全部调用的累计相干误差、实际报告／后继与终端的匹配、失败、拒绝、停止及告警质量必须留在完整误差预算中。数学端点分类不证明这些合同，也不把零失败理想式外推到非零失败后删支归一的模型。频数使用还需可靠重复准备、抽样与置信合同；本卷不给有限认证或鲁棒近似版的统一模。

复 Hilbert 载体、内积、相位规范、原十一精确矩阵、连续同射线密度及原 R 的实际来源仍是独立输入。过程存在、内部率和路径、驱动及滤过、纯更新与档案充分性都须另供；III177–182 或 III190–194 只有在保留其自主律、正活动、最小性或逆纤维前件时才能消费。本卷没有从密度选择推得混态仿射、任意 POVM、任意 CP 仪器、独立张量复合、物理时钟或全部动力学，也没有从唯一 $\Omega$ 的名称推得这些数学／经验接口。

## 6. 二元截面、整体几何与完整白话

**命题 6.1（保留全维数的三实坐标截面）。** 固定任一地址九活动对 $r,r^+$，仅作为数学截面取 $z=ae_r+be_{r^+}$、$|a|^2+|b|^2=1$。定义

$$
X=2\operatorname{Re}(\overline a b),\quad
Y=2\operatorname{Im}(\overline a b),\quad
Z=|a|^2-|b|^2.
\tag{6.1}
$$

则 $X^2+Y^2+Z^2=1$。在定理 2.1 的条件下，此截面的两配置质量为 $(1+Z)/2,(1-Z)/2$；原块 $Q_*=(I+n\cdot\sigma)/2$ 的轴为 $n=(2xy,0,x-x^2)$、$|n|=1$。这只是整个 $\mathbb{CP}^{88}$ 中一条 $\mathbb{CP}^1$ 的三实坐标表示；纯态截面本身实维为二，整个射影域实维仍为 $176$。

**证明。** 展开平方得球面恒等式；两质量由定理 2.1 限制到这个截面得到。$4x^3+(x-x^2)^2=(x+x^2)^2=1$ 给轴的单位长度。端点块是该球面上的固定酉转动，二元关系既涉及相对相位也涉及两坐标质量，不是只保留一条经典赔率。

整体中，$M_0\mathcal K$ 和 $M_1\mathcal K$ 的复维分别为 $55,34$。复用 III144、III195.5 已有的共同块几何，固定 $0<t=t_0<1$ 的单位输入射影纤维是

$$
\left(\sqrt t\,S^{109}\times\sqrt{1-t}\,S^{67}\right)/U(1)_{\rm diagonal},
\tag{6.2}
$$

其两端分别为 $\mathbb{CP}^{54}$、$\mathbb{CP}^{33}$。内部纤维实维 $175$，再加质量参数的一维才是全域实维 $176$。仅商去同一个整体相位，相对相位仍在。共同块作用的商坐标为区间 $t$；不是两个射影空间的乘积，也不是整个系统变成一只二能级对象。

细化所用 (2.9) 的 $34/21/34$ 是同一载体的另一坐标分解：$T$ 同步作用于 $34$ 对，另有 $21$ 个阻塞方向；(2.15) 是同一函数在两个向量自变量上的关系，并非原实际轨道中新增的连续旋钮。因此三坐标图景、全域闭包、数学代换与实际控制轨道各有不同对象，不能互换。∎

**定义 6.2（候选关系的完整白话）。** 始终保留同一个八十九维装置、同一个 ready、原来的十一种前操作、七种后操作和全部旧记录。先允许一套未知但连续的配置权重规则：它对同一射线给同一答案，所有权重非负且总和为一，某个配置的幅度为零时它的权重也必须为零。每做完一个原完整门，只要求该门原来能相互连接的每一组配置的总权重不变，连被阻塞的单点也不能漏掉；不再逐个要求门内每个未读时刻的方程。再要求在同一个 ready 的每一条有限实际前字后，读出并保留原记录时，读前某配置的权重等于这条记录的总权重乘以同一规则在投影后给它的条件权重，零投影整块按零处理。已有的共同矩阵作用和连续性先把两边的记录总量固定为平方长度。随后，九号完整门让成对配置交换幅度，保留读关系使两个条件方向服从同一二齐次函数；把这个端点恒等式作合法的相位代换就能推出精确平衡关系，迫使每个细坐标也取平方。被九号阻塞的二十一个点先靠单点守恒去掉外部背景，再由八号原配对固定。于是全部八十九坐标只能是 Born，任意相位和零坐标都包括在内。确有另一套固定连续权重对所有完整端点合法、却在二号门的一个内部时刻失守，所以裸端点要求严格更弱；它不能同时满足上述完整保留读关系。这个球面图只展示两个方向，不缩掉六十三维代码补空间，不增添制备或读口。最后，只有另供同一实际配置过程、字面报告与纯更新，以及对真实细档案仍成立的条件充分性，数学权重才给出原记录和旧终端的概率；取得、失败、精度、档案和来源合同仍需完整保留。

## 7. 数学来源与未决边界

**定义 7.1（复用与新增的精确对应）。** 本卷承重增量属 `repo-derived`：定理 2.1 中从固定非平衡端点式 (2.14) 到细坐标的 (2.15)–(2.20)，以及定理 3.2 的固定有限偶端点密度与旧内部方程严格分离。命题 4.1 的反事实属于相同源域的条件边界。一般连续延拓、酉矩阵相位归一、非负中点函数、有限群不变化、Bayes 公式及 Bloch 几何都只在证明内部使用，不作新的经典工具或全球原创性声明。

| 正式来源 | 具体消费与条件边界 |
| --- | --- |
| [固定 II][II46927] §§77、100、117–118、121 | 原路径／表对应、$J,R_0v,M_i,N_w$、全部标签、取得资源与误差、有限事件签名。数学签名不预先给实际概率；所有原 $p,f$ 量词保留。 |
| [固定 III][III46927] (144.8)–(144.12)、(144.16)、(173.4)–(173.9) | 直接复用共同乘积群、同一 ready 射线密度及粗函数证明，不重新证明或申报它们。原参数为 $(k,r,n)=(2,5,10)$ 的 $[6,4],[5,5]$ 和 $(2,5,12)$ 的 $[6,6]$，两扇区／全扇区维数为 $55,34/89$。 |
| [Freedman–Larsen–Wang，math/0103200v1 全文][FLW]，Theorem 0.1，§2 Lemma 2.1、Definitions 1–2 | `literature-attested`：$r\ge5,r\ne6,10,n\ge3$ 时 Jones 直和闭像包含各可容许扇区的 $SU$ 乘积。这里 $r=5$、行差 $2,0,0\le r-k=3$；使用全可容许表和共同规范。III144 已把该原文接到源矩阵，共同标量 $e^{\pi i/5}$ 通过模十有限指数子群消去，逆字母由 $K_j^{-1}=K_j^9$ 换成正向字。只分别稠密的两个射影像不足以替代这个供应；不使用该文 §6 的融合矩阵作替代规范。 |
| 固定 III (157.1)–(157.3)、(157.12)、(173.10)–(173.24) | 全部原矩阵、单点与活动对，以及二齐次／节点消元工具。旧 (173.15) 是全时式，旧 (173.18) 的内部平衡不作本卷前件；本卷只取其 $t=1$ 数值并独立推出 (2.17)。 |
| 固定 III164.1–164.4、165.2、166.3 | 复用奇位扇区、$c_q,w_s$ 及旧非 Born 裸密度边界；(3.3) 的有限偶端点最小值和 (3.7)–(3.11) 的严格性是不同的新构造，不把旧反例本身重报为新增。 |
| 固定 III174.1–174.2、145.2；续卷 V §§1、10–12 | 复用实际条件律、报告／后继／档案分工。当前配置恢复、最小路径或指定仪器消费者仍需各自原前件，不由端点密度刻画供应。 |
| [当前 III195][IIIbase]、[续卷 VI][VIbase] §§1–9；固定 III177–182、190–194 | 分别处理有终端／校准前件的记录选择、自主局部动力学选择和给定平方过程的生成元逆问题；不与本卷的未知全坐标端点密度分类交换前件。 |

**定义 7.2（保留的未决问题）。** 本卷不判无连续性或任意删分量子类的完整分类，不给定量近似 R 的统一稳定界，也不供应物理来源为何满足同密度充分性及端点关系。实际控制可取得性、完整失败律、相位与复结构、独立联合资源、时间及动力学来源仍各有未证桥梁。定理 2.1 是在明确数学域内的充要选择，定理 3.2 是裸类严格包含；两者均不把数学可定义、实际可取得及可靠认证认作同一结论。

[II46927]: https://github.com/the-omega-institute/trureturing/blob/46927cc328c58a872092e1d1c3bf102e48fa0426/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md
[III46927]: https://github.com/the-omega-institute/trureturing/blob/46927cc328c58a872092e1d1c3bf102e48fa0426/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md
[V46927]: https://github.com/the-omega-institute/trureturing/blob/46927cc328c58a872092e1d1c3bf102e48fa0426/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_V.md
[IIIbase]: https://github.com/the-omega-institute/trureturing/blob/d158ce0a2dd34b10820f86aa88a733beee42c423/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md#195-原生守恒的码锚校准与一次删址反例
[VIbase]: https://github.com/the-omega-institute/trureturing/blob/d158ce0a2dd34b10820f86aa88a733beee42c423/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_VI.md
[FLW]: https://arxiv.org/html/math/0103200v1

## 追加锚（本行以下为增补区）


## 8. 有限扰动的实际载体、全未来效应与校准排除

### 8.1 原实际载体与完整未来加性类

**定义 8.1（原始合同、两种程序和完整未来行）。** 固定同一个唯一 $\Omega$、原生
$89$ 维复载体 $\mathcal K=V_{12}^{\mathbf 1}$、$26+63$ 的代码／补空间分解、唯一
ready $e_0$、全部 $1024$ 个旧 $\pi$-fiber 标签、原十一地址前操作与原七地址后操作。
原有限时序字按实际调用先后相乘；$K_{af}=K_fK_a$。原 support、calibration、
历史、records、archives、zero、failure、Return、实际 event permissions、source／
process、资源、时间和 units 合同均按其原字面保留。本节只研究指定终端边缘的
加性数学类，不增加 preparation、measurement、control、port、copy 或 resource。

令

$$
\mathsf W_{11}=\{0,\ldots,10\}^{<\infty},\qquad
\mathsf W_7=\{0,\ldots,6\}^{<\infty},\qquad
\Lambda=\{0,1\}^{10},\qquad \chi_a=K_ae_0 .
$$

$P_a=\chi_a\chi_a^*/\|\chi_a\|^2$ 是原纯矩阵点。$N_w$ 是原旧标签
$w\in\Lambda$ 的投影，$\sum_wN_w=I$；其中 $34$ 个秩二、$21$ 个秩一、
$969$ 个为零，零标签始终保留。记

$$
\begin{aligned}
\mathcal D_{89}&=\{\rho\succeq0:\operatorname {Tr}\rho=1\},\qquad
I_{\rm fut}=\{\star\}\sqcup(\mathsf W_{11}\times\Lambda),\\
Q(X)&=\left(\operatorname {Tr}X,
 \left(\operatorname {Tr}(N_wK_fXK_f^*)\right)_{f\in\mathsf W_{11},\,w\in\Lambda}\right)
 \in\ell^\infty(I_{\rm fut},\mathbb R),\quad X\in\operatorname {Herm}_{89}.
\end{aligned}
\tag{8.1}
$$

这里 $Q$ 从一开始就包含全部原十一地址预终端未来，不是只有当前 $1024$ 个
标签的测量。当前 Born 边缘只是 $Q(X)_{\epsilon,w}$；$\star$ 是归一化坐标。
在行空间上使用包含全部未来坐标的上确界范数。$Q$ 的数学域不表示这些矩阵
均可实际制备。

取原 finite reduction 的一个非空 reachable component $R$，记 ready 类为
$r_*$。原字在 $R$ 上的有限像生成置换群 $G$，在 $R$ 上传递，且
$r_a=g_ar_*$、$g_{af}=g_fg_a$。给定任意归一化当前噪声

$$
 m:R\longrightarrow\Delta_{1024},\qquad
 m(r)=(m_w(r))_w,\qquad m_w(r)\ge0,\quad\sum_wm_w(r)=1 .
\tag{8.2}
$$

不对 $m$ 加等变、单射或仿射独立条件。在 $0<\eta<1$ 时加性终端类为

$$
 p_w(a)=(1-\eta)\operatorname {Tr}(N_wP_a)+\eta m_w(r_a).
\tag{8.3}
$$

对每个 $f\in\mathsf W_{11}$，同一实际程序 $\mathsf T(af)$ 的读数为

$$
 p_{f,w}(a):=p_w(af)
 =(1-\eta)\operatorname {Tr}(N_wK_fP_aK_f^*)+\eta m_w(g_fr_a).
\tag{8.3a}
$$

另一个原程序 $\mathsf R(a,h)$ 仍是执行 $a$、读取并保留 $b_9$、再执行
与该结果无关的原 $h\in\mathsf W_7$，最后用旧终端。它保留原 $M_i$ 分支、
记录和全部原合同；(8.3a) 不给出或替换这个带中途记录的联合律。同一个
$h\in\mathsf W_7$ 在 $\mathsf T(ah)$ 中没有中途记录，两个程序不能等同。
特别是原七地址 $K_h$ 和 $N_w$ 都与 $M_i$ 对易，故只保留七地址的共轭效应
看不见两个 record sectors 之间的相干项；本节不把它们当作 (8.1) 的替代。
十一地址在本节只用于原已合法的预终端域，不增加记录后控制。

第二项只依赖原 finite reduction，不是新的 source。若另要求原 fine-zero
support 合同，还须对每个实际 $a,w$ 要求
$\operatorname {Tr}(N_wP_a)=0\Rightarrow m_w(r_a)=0$；归一化不自动供应它。
其余 source/process、记录及失败合同也不由这个终端类自动推出。

**假设 8.2（实际作用与有限纤维）。** 原十一地址 projective action 的闭包为
$PU(89)$。为同时保留原作用与原 finite reduction，令

$$
\Gamma=\langle([K_j],g_j):0\le j\le10\rangle\ \le PU(89)\times G,
\qquad H=\ker(\Gamma\longrightarrow G),\qquad
\mathcal F_r=\{P_a:r_a=r\}.
$$

第二投影满射，故 $H$ 有限指数。这里使用两种作用的共同群像，不要求 finite
reduction 能从 projective matrix 的标量相位商单独读出。原实际字仍只有有限
正向十一地址；群、闭包和 $H$ 只用于证明，未取得连续物理控制。

定义完整噪声列及其凸包

$$
\begin{aligned}
t_r&=\left(1,(m_w(g_fr))_{f\in\mathsf W_{11},\,w\in\Lambda}\right),\\
T_0&=\{t_r:r\in R\},\qquad T=\operatorname {conv}T_0,\qquad
q=|T_0|,\qquad \bar t=q^{-1}\sum_{t\in T_0}t,\\
W_T&=\operatorname {span}_{\mathbb R}(T-\bar t).
\end{aligned}
\tag{8.4}
$$

只有完整列相同才在 $T_0$ 中去重。当前 $m(r)=m(s)$ 不表示 $t_r=t_s$；
当前值之间的仿射关系也不表示完整列有该关系。由于 $G$ 有限且每个 $g\in G$
都有原有限字代表，$t_r$ 等价于有限列 $(1,(m_w(gr))_{g,w})$。这只是同一行的
无损有限坐标表示，不是另选一组 profiles。

在与 $Q$ 完全相同的坐标域中置

$$
\Phi(\rho,t)=(1-\eta)Q(\rho)+\eta t,\qquad
K=\Phi(\mathcal D_{89}\times T),\qquad
V=\operatorname {span}_{\mathbb R}K,\qquad u(z)=z(\star).
\tag{8.5}
$$

实际完整行为 $z_a=(1,(p_{f,w}(a))_{f,w})=\Phi(P_a,t_{r_a})$。
$K$ 是这些指定终端行的数学完成基，不是另一个 source，也不是包含
$\mathsf R$ 联合律的替代 state space。对所有 $z\in V$，每个固定 $f$ 都满足
$\sum_wz(f,w)=u(z)$。

### 8.2 密集纤维和实际 body 的精确识别

**命题 8.3（有限指数核和密集纤维）。** 在假设 8.2 下，$H$ 的第一投影在
$PU(89)$ 中稠密，原正向有限字中 $g_h=1_G$ 的那些字的 projective image
也稠密。因此对每个 $r\in R$，$\overline{\mathcal F_r}=\mathbb {CP}^{88}$。

**证明。** 设 $L$ 为 $H$ 的第一投影的闭包。$\Gamma$ 的有限余类分解在第一
投影及闭包后给出 $PU(89)$ 是有限个 $L$ 余类之并。因此闭子群 $L$ 有限指数，
从而开；$PU(89)$ 连通，故 $L=PU(89)$。

还须回到实际正向字。令 $S$ 为 $([K_a],g_a)$ 的正向字幺半群。紧群中每个
元素 $b$ 的逆属于其非负幂的闭包：有限阶时直接取幂；无限阶时由紧性取正幂
趋于单位，再将指数减一得到趋于 $b^{-1}$ 的非负幂。因此 $\overline S$
包含每个生成元的逆，$\overline S=\overline\Gamma$。对 $h\in H$，可用
实际正向字逼近这个 pair；由于第二因子 $G$ 离散，逼近字的有限像最终恰为
$1_G$。结合第一段，实际 kernel 字的 projective image 稠密。

取一个到达 $r$ 的实际 $a_r$，在其后接上述 kernel 字，仍落在 $r$，而
$P_{a_rh}=K_hP_{a_r}K_h^*$ 的闭包为全部秩一投影。这证明每个实际 fiber
稠密，而没有把闭包元素或逆的极限变成物理按钮。∎

**命题 8.4（统一全未来的实际行闭包）。** 在 (8.1) 的全未来上确界范数下，

$$
\overline{\{z_a:a\in\mathsf W_{11}\}}
 =\{\Phi(P,t):P\text{ rank one},\ t\in T_0\},
\tag{8.6}
$$

且

$$
\overline{\operatorname {conv}\{z_a:a\in\mathsf W_{11}\}}
 =\Phi(\mathcal D_{89}\times T)=K.
\tag{8.7}
$$

$K$ 紧，$V$ 有限维且恰为实际行的实线性张成。

**证明。** 对任意 Hermitian $X$，$\|Q(X)\|_\infty\le\|X\|_1$，因为
$0\le N_w\le I$ 且每个 $K_f$ 酉；归一化坐标也满足同一界。所以固定一个
$r$ 时，$P\mapsto\Phi(P,t_r)$ 在所有未来上一致连续。命题 8.3 给出 (8.6)
的正向包含；反向包含由有限个 $r$ 和秩一投影域的紧性给出。

$Q(\operatorname {Herm}_{89})+\operatorname {span}T_0$ 有限维，故全未来坐标
虽无限，所有行已在同一个有限维闭子空间内。$\mathcal D_{89}\times T$ 紧，
$\Phi$ 连续，故 $K$ 紧。若 $\rho=\sum_i\mu_iP_i$ 是谱分解、
$t=\sum_j\lambda_jt_{r_j}$，则
$\Phi(\rho,t)=\sum_{i,j}\mu_i\lambda_j\Phi(P_i,t_{r_j})$。
每项都在 (8.6) 的实际行闭包内，得 (8.7)；反向由 $K$ 闭凸。有限维中实际行
张成的线性空间闭，遂等于 $V$。这些凸组合都是数学完成，不取得物理混合资源。∎

**命题 8.5（完整行的无 confounding 与未来闭合）。** 令
$H_0=\{X\in\operatorname {Herm}_{89}:\operatorname {Tr}X=0\}$。则
$Q|_{H_0}$ 单射，且

$$
Q(H_0)\cap W_T=\{0\}.
\tag{8.8}
$$

对任意密度矩阵 $\rho,\rho'$，有

$$
\sup_{f\in\mathsf W_{11},\,w\in\Lambda}
 \left|\operatorname {Tr}\!\left(N_wK_f(\rho-\rho')K_f^*\right)\right|
 \le\|\rho-\rho'\|_1.
\tag{8.9}
$$

$\Phi$ 在 $\mathcal D_{89}\times T$ 上仿射单射，全部实际未来评价均为同一
有限维 $V$ 上的连续线性函数。

**证明。** 对实际有限字 $h$ 定义行移位
$(S_hz)(\star)=z(\star)$、$(S_hz)(f,w)=z(hf,w)$。实际次序给

$$
S_hQ(X)=Q(K_hXK_h^*),\qquad S_ht_r=t_{g_hr}.
$$

当 $g_h=1_G$ 时，$S_h$ 逐点固定 $T_0$，因而逐点固定 $W_T$。若
$Q(X)\in W_T$、$X\in H_0$，则这些实际 kernel 字满足
$Q(K_hXK_h^*)=Q(X)$。取空未来和一个原 rank-one $N_{w_0}$，命题 8.3 的
kernel 密度及连续性给

$$
\operatorname {Tr}(N_{w_0}UXU^*)=\operatorname {Tr}(N_{w_0}X)
\qquad(U\in PU(89)).
$$

所有秩一投影都是 $U^*N_{w_0}U$，故 $X$ 的每个单位向量二次型值相同，
$X$ 为标量；迹零迫使 $X=0$。这同时证明 (8.8) 和 $Q|_{H_0}$ 的单射性
（零行也属于 $W_T$）。含迹坐标的 $Q$ 在全部 Hermitian 空间上也单射。
若 $\Phi(\rho,t)=\Phi(\rho',t')$，差分属于 (8.8) 的交，故两因子均相同。

同一迹范数界给 (8.9)，并给
$\|\Phi(\rho,t)-\Phi(\rho',t')\|_\infty
\le(1-\eta)\|\rho-\rho'\|_1+\eta\|t-t'\|_\infty$。
每个 $S_h$ 将 $K$ 送到 $K$，因而将 $V$ 送到 $V$；所有未来坐标都是这个
完整行的评价。命题 8.4 的闭包因此是统一全未来闭包，不只是逐坐标或当前菜单
的闭包。这里没有对记录后七地址载体作单射性断言。∎

### 8.3 精确 rank、纯点和完整 profiles 的退化

**定义 8.6（同一完整 profile 的 rank）。** 定义有限矩阵

$$
\mathsf B:\mathbb R^{R}\longrightarrow
 \mathbb R\times\mathbb R^{G\times\Lambda},\qquad
\mathsf B(c)=\left(\sum_rc_r,
 \left(\sum_rc_rm_w(gr)\right)_{g,w}\right),\qquad
 d_T=\operatorname {rank}\mathsf B-1 .
\tag{8.10}
$$

有限列到 (8.4) 的完整行由 $(g_f,w)$ 重复坐标嵌入给出；每个 $g$ 有实际字
代表，所以该嵌入单射。因而 $d_T=\dim W_T=\dim\operatorname {aff}T$。
重复完整 profile 恰给重复列，所有仿射关系由下文 (8.14) 给出。
当前 $m(r)$ 的重复或依赖不在这里被误删。完整列的重复和仿射依赖均允许，
不把 $d_T$ 默认成 $|R|-1$ 或 $q-1$。

**定理 8.7（实际 body 的 rank 和纯点）。** 在 $0<\eta<1$ 下，

$$
\dim_{\mathbb R}\operatorname {aff}K=7920+d_T,
\qquad \dim_{\mathbb R}V=7921+d_T.
\tag{8.11}
$$

$K$ 的纯点恰为

$$
\Phi(P,v),\qquad P^2=P=P^*,\quad\operatorname {rank}P=1,\quad v\in T_0.
\tag{8.12}
$$

所有 distinct 完整 profiles 都是 exposed 顶点。$q=1$ 时 $d_T=0$；$q>1$ 时

$$
1\le d_T\le q-1,
\tag{8.13}
$$

不要求 $d_T=q-1$，重复的 $r$ 也不必删除。

**证明。** 先核对完整 profiles 的作用。若 $k\in G$，在有限坐标中
$t_{kr}(g,w)=t_r(gk,w)$，即右平移只是置换 $G\times\Lambda$ 坐标。因此
$t_r=t_s$ 蕴涵 $t_{kr}=t_{ks}$，完整列的每个线性或仿射关系也被平移保留。
这给出 distinct $T_0$ 上的传递作用，没有要求当前映射 $m$ 等变。

在有限坐标上取通常 Euclidean 内积。此作用保持 $\bar t$ 和
$\|t-\bar t\|$。对固定 $v\in T_0$，泛函
$t\mapsto\langle v-\bar t,t-\bar t\rangle$ 在 $T_0$ 中的唯一最大点是 $v$：
等范数和 Cauchy--Schwarz 的等号条件排除其它 distinct 点。故每个 $v$ exposed。
$q=1$ 时结论直接成立。

$\dim H_0=89^2-1=7920$，而命题 8.5 给

$$
\operatorname {aff}K-\operatorname {aff}K
 =(1-\eta)Q(H_0)\oplus\eta W_T.
$$

由定义 8.6 得仿射维数，再因 $u=1$ 于 $K$、$u=0$ 于差空间，增加一维得到
(8.11)。仿射单射 $\Phi$ 将 Cartesian product 的极点恰送到极点。
$\mathcal D_{89}$ 的极点是秩一投影，$T$ 的极点刚证明恰为 $T_0$，故得
(8.12)。若一因子不极端，其非平凡凸分解经单射给出非平凡分解；若两因子均
极端，每个正权分解项的两个因子都相同。这也直接证明纯点刻画的两个方向。
最后，矩阵 $\mathsf B$ 的列关系恰为

$$
\sum_rc_r=0,\qquad \sum_rc_rm_w(gr)=0\quad(\forall g\in G,w\in\Lambda).
\tag{8.14}
$$

因此 $d_T$ 计入全部依赖，(8.13) 包含所有退化情形。∎

### 8.4 整个 proper effect interval 和最小确认

**命题 8.8（全 effects 的唯一 gauge）。** $C=\operatorname {cone}K$ 是
$V$ 中的闭、尖、生成锥，$u$ 在 $C\setminus\{0\}$ 上严格正。$K$ 上每个
仿射函数都唯一线性延拓到 $V$，并有唯一表达

$$
F(\Phi(\rho,t))=c+\operatorname {Tr}(A\rho)+\ell(t-\bar t),
\qquad \operatorname {Tr}A=0,
\tag{8.15}
$$

其中 $A$ 为 Hermitian，$\ell\in W_T^*$。令

$$
\ell_-:=\min_{t\in T}\ell(t-\bar t),\qquad
\ell_+:=\max_{t\in T}\ell(t-\bar t).
$$

则 $F$ 属于整个数学 proper interval $[0,u]$，即在全部 $K$ 上 $0\le F\le1$，
当且仅当

$$
 c+\lambda_{\min}(A)+\ell_-\ge0,\qquad
 c+\lambda_{\max}(A)+\ell_+\le1 .
\tag{8.16}
$$

**证明。** $K$ 紧且 $u=1$。若 $s_nk_n$ 收敛（$s_n\ge0,k_n\in K$），则
$s_n=u(s_nk_n)$ 也收敛；$s_n\to0$ 时有界 $k_n$ 给零极限，否则由紧性
给仍在 $C$ 的极限。这证明闭性；
$u$ 的严格正性给尖性，$V=\operatorname {span}K$ 给生成性。归一化超平面
不经过原点且张成 $V$，故仿射函数恰有上述线性延拓。

(8.8) 的直和给出 (8.15)；$\operatorname {Tr}A=0$ 将标量部分吸收到 $c$，
两因子的满仿射张成给唯一性。独立改变 $\rho,t$ 时，最小值恰为
$c+\lambda_{\min}(A)+\ell_-$，最大值恰为
$c+\lambda_{\max}(A)+\ell_+$；在谱极向量和 profile 顶点上可以同时达到。
故 (8.16) 没有遗漏任何 proper effect，也没有引入物理测试菜单。∎

对纯点 $p=\Phi(P,v)$，定义

$$
\mathcal F_p=\{F\in[0,u]:F(p)=1\},\qquad
T_p(x)=\min_{F\in\mathcal F_p}F(x),
\tag{8.17}
$$

以及

$$
\kappa_v(t)=\min\{k(t):k\text{ affine},\ 0\le k\le1\text{ on }T,\ k(v)=1\}.
\tag{8.18}
$$

这些最小值均达到。事实上 proper 仿射函数在一个有限仿射基上的值有界，
所以全 proper interval 是有限维闭有界集；确认条件给其非空闭子集。
同一论证适用于 $T$。

**定理 8.9（完整混态域的最小确认和比较）。** 对任意
$\rho\in\mathcal D_{89}$、$t\in T$，

$$
T_{\Phi(P,v)}(\Phi(\rho,t))
 =\min\{\operatorname {Tr}(P\rho),\ \kappa_v(t)\}.
\tag{8.19}
$$

特别是对任意纯 $s=\Phi(Q,s_T)$，
$T_p(s)=\min\{\operatorname {Tr}(PQ),\kappa_v(s_T)\}$；对反向比较，
$T_s(p)=\min\{\operatorname {Tr}(PQ),\kappa_{s_T}(v)\}$。
任意有限混合 $\sum_i\lambda_i\Phi(\rho_i,t_i)$ 的比较值也由 (8.19) 取得，
其两个输入恰为 $\sum_i\lambda_i\rho_i$ 和 $\sum_i\lambda_it_i$。
重复 profiles、全部仿射依赖、混态 $\rho$ 和混合 $t$ 都在这些量词内。

**证明。** 量子-only confirmer $q_P(\rho)=\operatorname {Tr}(P\rho)$ 和达到
(8.18) 的 profile-only confirmer 都在整个 (8.16) 区间内，故右端为上界。
反向取任意 $F\in\mathcal F_p$，令
$a(\rho)=F(\Phi(\rho,v))$、$b(t)=F(\Phi(P,t))$。Cartesian affine identity 为

$$
F(\Phi(\rho,t))=a(\rho)+b(t)-1.
\tag{8.20}
$$

置 $\alpha=\min a$、$\beta=\min b$，则 $0\le\alpha,\beta\le1$，
$\alpha+\beta\ge1$，且 $a(P)=b(v)=1$。代表 $a$ 的 Hermitian 矩阵在 $P$
上有本征值一，其余谱至少为 $\alpha$，所以

$$
 a(\rho)\ge\alpha+(1-\alpha)\operatorname {Tr}(P\rho),\qquad
 b(t)\ge\beta+(1-\beta)\kappa_v(t).
\tag{8.21}
$$

第二式在 $\beta<1$ 时由 $(b-\beta)/(1-\beta)$ 是 proper confirmer 得到；
$\beta=1$ 时 $b=1$，同式仍成立。令 $x=\operatorname {Tr}(P\rho)$、
$y=\kappa_v(t)$。若 $x\le y$，代入 (8.20) 得
$F(\Phi(\rho,t))-x\ge(\alpha+\beta-1)(1-x)\ge0$；若 $y\le x$，交换两项
得到相同的 $y$ 下界。故所有确认者都不小于右端，component confirmers
达到它。纯点、反向和有限混合的各式由同一公式直接代入，没有假定 profile
转移数互反，也没有把任意混态余项缩为纯态。∎

### 8.5 混态零 gluing、完整比较和 sharp midpoint

**定义 8.10（混态 zeroGluing）。** 对具有全 proper interval 的完成基 $K$，
称其满足 zeroGluing，若对每个纯参照 $p$ 和任意两个混态点 $x,y\in K$，

$$
\begin{gathered}
\bigl(\exists F_x\in\mathcal F_p:F_x(x)=0\bigr)\ \land
\bigl(\exists F_y\in\mathcal F_p:F_y(y)=0\bigr)\\
\Longrightarrow\quad
\exists F\in\mathcal F_p:\ F(x)=F(y)=0.
\end{gathered}
$$

前件称为 separately excludable。由非负性及最小值达到性，结论等价于
$T_p((x+y)/2)=0$；前件等价于 $T_p(x)=T_p(y)=0$。
归纳后同一性质适用于任意有限个分别可排除的混态点。这是数学 effect 性质，
不是 source 新增的物理操作。

**命题 8.11（精确分类与普遍 sharp bound）。** 对 $0<\eta<1$ 的本加性类，

$$
\mathrm {zeroGluing}\quad\Longleftrightarrow\quad
T\text{ 是 singleton}\quad\Longleftrightarrow\quad m\text{ 在 }R\text{ 上恒定}.
\tag{8.22}
$$

对每个纯 $p$ 和任意混态 $x,y\in K$，只要 $T_p(x)=T_p(y)=0$，均有
$T_p((x+y)/2)\le1/2$。若 $T$ 非 singleton，则对每个纯 $p=\Phi(P,v)$，
此上界在一对纯点上达到，所以也是全部上述混态对的最大值。

此外，原完整 fixed-half comparison

$$
T_p\!\left(\frac{s+x}{2}\right)=\frac{T_s(p)+T_p(x)}2
\quad(p,s\text{ pure},\ x\in K)
$$

在本类中成立当且仅当 $T$ 是 singleton。

**证明。** 先证明普遍上界，它不需要乘积结构。若分别可排除，取
$F_x\in\mathcal F_p$、$F_x(x)=0$，则
$T_p((x+y)/2)\le F_x(y)/2\le1/2$。这量化任意混态 $x,y$，不声称每一对
都达到该值；若有共同零确认者，其中点值就是零。

若 $T$ 是 singleton，(8.19) 为 $T_p(\Phi(\rho,t))=\operatorname {Tr}(P\rho)$。
分别为零的任意混态点都由同一个 $q_P$ 置零，故 zeroGluing 成立；迹配对的
对称性和线性也给出完整 fixed-half comparison。

若 $T$ 非 singleton，命题 8.7 的 exposed 泛函在 $v$ 上唯一最大；减去其在
$T$ 上的最小值并归一化，得到 proper profile confirmer $h$，满足
$h(v)=1,h(s_T)=0$，其中 $s_T\in T_0$ 是一个最小顶点。取秩一 $Q\perp P$，置

$$
 x=\Phi(Q,v),\quad y=\Phi(P,s_T),\quad z=\Phi(Q,s_T).
\tag{8.23}
$$

这四个角属于同一个实际完成基，且 $x+y=p+z$。$q_P(x)=0$，$h(y)=0$，
所以 $x,y$ 分别可排除。对任意 $F\in\mathcal F_p$，只在此矩形上使用
$F(x)+F(y)=1+F(z)\ge1$，得到中点下界 $1/2$。
$q_P$ 在该中点上等于 $1/2$，故

$$
T_p\!\left(\frac{x+y}{2}\right)=\frac12.
\tag{8.24}
$$

这与普遍上界合在一起证明最大值和达到性，并否定 zeroGluing。
$1-h$ 确认 $y$ 且在 $p$ 上为零，故 $T_y(p)=0$。将纯 $s=y$ 和纯余项 $x$
代入完整 fixed-half comparison，其右端为零而左端为 $1/2$，故该比较也失败。
最后，$m$ 恒定显然给 singleton 完整列；反向若全部 $t_r$ 相同，取空未来
坐标便得全部 $m(r)$ 相同。∎

### 8.6 current-ready 与全未来 ready-return

**定义 8.12（两种 ready-return）。** 令 $a_*=\epsilon$ 是原 unique ready
空字，$P_*=P_{a_*}$。CR 和 UF 都量化每一列实际有限字 $(a_n)$：

$$
P_{a_n}\to P_*\quad\Longrightarrow\quad
p(a_n)\longrightarrow p(a_*)\qquad\text{(CR: current terminal only)},
\tag{8.25}
$$

以及

$$
P_{a_n}\to P_*\quad\Longrightarrow\quad
\sup_{f\in\mathsf W_{11}}\|p_f(a_n)-p_f(a_*)\|_\infty\longrightarrow0
\qquad\text{(UF)}.
\tag{8.26}
$$

其中 $p_f$ 是原预终端 $\mathsf T(af)$ 的全部旧标签向量，未来按十一地址、
原时序量化。$\mathsf R(a,h)$ 的记录后七地址域保持独立；UF 不授予它任何
额外 future。两种条件都不要求任意数学 $\rho$ 可实际制备。

**定理 8.13（当前 ready、全未来和 singleton 完整 profiles）。** 在
$0<\eta<1$ 和假设 8.2 下，

$$
\mathrm {CR}\quad\Longleftrightarrow\quad\mathrm {UF}
\quad\Longleftrightarrow\quad |T_0|=1
\quad\Longleftrightarrow\quad m\text{ 恒定}.
\tag{8.27}
$$

**证明。** 固定任意 $r\in R$，由命题 8.3 可取同一 fiber 的实际
$a_n^{(r)}$，使 $P_{a_n^{(r)}}\to P_*$。若 CR 成立，(8.3) 的 Born 项趋于
ready Born 项，噪声项恒为 $m(r)$，而极限必须等于 ready 的当前行。
$\eta>0$ 给 $m(r)=m(r_*)$。所有 $r$ 都成立，故 $m$ 恒定。

若 $m$ 恒定，每个原十一地址 future 的噪声项都相消，(8.9) 给

$$
\sup_{f\in\mathsf W_{11},\,w\in\Lambda}|p_{f,w}(a)-p_{f,w}(b)|
 \le(1-\eta)\|P_a-P_b\|_1.
\tag{8.28}
$$

故有 UF；取空 future 得 CR。singleton 完整列与 $m$ 恒定的等价已在
命题 8.11 的空未来论证中给出。∎

**推论 8.14（继承 CR 的原 actual-sequence calibration 排除）。** 在定理
8.13 的条件下，另保留 CR（或等价地直接假定 $m(r)\equiv c$），再保留原
ready 精确 label calibration 及原 actual code-sequence calibration，则
$0<\eta<1$ 的本类没有同时满足这些 contracts 的成员。ready 校准强制

$$
 c=\delta_{1000100010},
\tag{8.29}
$$

而原合同中趋于 $J(e_{10100}\otimes|0\rangle)=e_{101000100}$ 的实际校准
序列强制

$$
 c=\delta_{1010100010}.
\tag{8.30}
$$

两个旧标签不同；无需 exact coordinate reachability，也不假定 full-terminal
Born theorem。对 $\eta=1$ 的常量分支，同一矛盾仍成立。

**证明。** CR 由定理 8.13 供应常量 $c$。原 ready 为 $e_{001000100}$，其
旧标签是 $1000100010$。在 (8.3) 中，ready Born 边缘和原精确校准边缘都为
这个 delta，故 $\eta>0$ 给 (8.29)。沿原合同的上述实际校准序列，Born 边缘
由矩阵连续性趋于第二个 delta，而实际边缘由校准合同趋于同一个第二 delta；
噪声仍为同一 $c$，故得到 (8.30)。这使用的是原实际序列合同，不是从稠密性
推断所有极限都已取得校准。

可选的另一充分前件是：同一实际粗响应有共同连续延拓，并在原合同指定的
$Q_A=\sum_{b_1(w)=1}N_w$ 零、一 anchors 上分别取零、一。实际射线稠密使
共同连续延拓唯一；常量分支的延拓为
$(1-\eta)\operatorname {Tr}(Q_A P)+\eta c_A$，其中
$c_A=\sum_{b_1(w)=1}c_w$，故这两个 anchors 分别迫使 $c_A=0,c_A=1$。
这些是另行保留的共同 anchor 合同，不是任意 off-orbit 赋值，也不是本节
新增的实际校准许可。∎

### 8.7 fine-zero-only 的剩余问题与两个端点

**命题 8.15（常量分支只保留 fine-zero 的精确残余）。** 在 $\eta>0$ 和
$m(r)\equiv c$ 下（内点类可由 CR 取得此条件），若不采用推论 8.14 的序列
校准而只加原 fine-zero support contract，则该 contract 等价于

$$
\operatorname {supp}(c)\subseteq
 \bigcap_{a\in\mathsf W_{11}}\{w:N_wK_ae_0\ne0\}.
\tag{8.31}
$$

空字给 $c=\delta_{1000100010}$。排除此唯一候选仍须建立一个实际合法有限字
$a$ 满足

$$
N_{1000100010}K_ae_0=0.
\tag{8.32}
$$

本节没有建立 (8.32)；稠密性只给近似，不能代替 exact zero。故省略序列校准
和上述可选 anchors 时，这个 fine-zero-only 问题保持 open。不假定常量分支
的一般 support-only response residual 也没有被本节分类。

**证明。** 若某实际 $a,w$ 的 Born 项为零且 $c_w>0$，则 (8.3) 给
$p_w(a)>0$，违反 fine-zero。反向，(8.31) 恰保证每个实际 Born 零标签的
$c_w$ 为零，故加性行也为零。空字只有 ready 标签非零，所以归一化给唯一
候选 delta；该候选违反 (8.31) 当且仅当存在 (8.32)。∎

**定理 8.16（两个 eta endpoints）。** 保持 (8.1)、(8.4) 的同一完整未来域，
将 (8.5) 限制到端点，则：

1. $\eta=0$ 时，$K=Q(\mathcal D_{89})$，$m$ 完全不可见，
$\dim\operatorname {aff}K=7920$、$\dim V=7921$。纯点恰为 $Q(P)$；整个
proper interval 为 $F(Q(\rho))=\operatorname {Tr}(E\rho)$、$0\le E\le I$。
$T_{Q(P)}(Q(\rho))=\operatorname {Tr}(P\rho)$，zeroGluing 和完整比较均成立，
CR、UF 自动成立，不限制 $m$。

2. $\eta=1$ 时，$K=T$，$\dim\operatorname {aff}K=d_T$、$\dim V=d_T+1$，
纯点恰为 $T_0$，全 proper interval 是 $T$ 上全部 $[0,1]$ 值仿射函数，
最小确认为 $\kappa_v(t)$。CR、UF 和 $m$ 恒定仍等价，但几何上没有 quantum
factor。若完整 profile body 是 simplex，则可在非恒定 $m$ 下满足
zeroGluing 和完整比较。普遍中点上界 $1/2$ 对该端点仍成立；非单点时必有
quantum rectangle 达到 $1/2$ 的内点结论不延伸到此端点。

**证明。** 命题 8.5 已证明完整 $Q$ 在 Hermitian 空间单射；故第一端点确为
全部密度基的线性像，而不是当前对角测量的商。迹配对给全 effects；若
$0\le E\le I$ 且 $\operatorname {Tr}(EP)=1$，则 $EP=P$，两块间项为零，
因而 $E\succeq P$，$E=P$ 达到最小确认。其余量子结论和全未来回返的
迹范数界随之成立。

第二端点只剩同一完整列的有限凸包；定义 8.6 和命题 8.7 给维数和顶点。
定理 8.13 的 CR 固定-fiber 论证只需 $\eta>0$，恒定 profile 的 UF 则在这里
差值直接为零，故该等价仍成立。若 $T$ 为 simplex，顶点 $v$ 的重心坐标
$\lambda_v(t)$ 是最小 proper confirmer：其它顶点上的值均非负，故任何确认者
逐点不小于 $\lambda_v$。同一个 $\lambda_v$ 能合并全部零，顶点之间的比较为
Kronecker delta，仿射性给全部混态的完整比较。命题 8.11 的一般上界只用
properness，仍适用，但该 simplex 的所有分别可排除对都有中点值零。
两个端点分别 annihilate 另一个因子，所以 (8.11) 的内点直和 rank 不可沿用。∎

### 8.8 来源 credit、适用边界与原量子起源目标

**定义 8.17（结果身份和复用边界）。** 本节的实际增量是 `repo-derived`
的完整有限-fiber additive-body synthesis：命题 8.3 的实际密集纤维、
命题 8.4–8.5 的统一全未来载体及无 confounding、定理 8.7 的 $7921+d_T$
rank、命题 8.8 和定理 8.9 的 entire proper interval 与完整混态比较式、
命题 8.11 的 zeroGluing 分类及 universal sharp $1/2$，以及定理 8.13 和
推论 8.14 的 current-ready／full-future／actual-sequence calibration map。
它不把下列成熟结果重报为本节原创：

| 来源 | 本节的精确消费 | 未消费的桥 |
| --- | --- | --- |
| 本卷 §§1–7 与 native III150、VII §§9、10、13 | 原 $\Omega$、$89$ 维矩阵、原标签、ready、有限字、十一地址预终端全 future、完整 proper comparison 与最小 confirmation 记号 | 七地址记录后接口及其 source/process 合同不由终端 body 替换 |
| Freedman--Larsen--Wang, [math/0103200v1, Theorem 0.1][FLW8] 及原 native 矩阵应用 | 原 $r=5,n=12$ Jones 作用的 projective 密度；有限指数和紧群闭包为证明内标准工具 | 不供应 physical preparation、native control acquisition 或 arbitrary-state cloning |
| Müller--Ududec, [*The structure of reversible computation determines the self-duality of quantum theory*][MU8]；Barnum--Müller--Ududec, [1403.4147v4, Theorem 16][BMU8] | finite-dimensional cone/effect language 与既有 least-confirmation/projectivity 桥的文献背景；本节乘积计算直接在声明的矩阵类内进行 | 不由这些引文把 AURIC source 变成 unrestricted Born/Hilbert uniqueness |
| dev105 的 least-confirmation/projectivity 结果 | 作为既有条件 supply 复用其适用范围 | $W\to G$ 与 $W+G\to$ global PL3 未供应 |
| dev103 的 $S2+$ one common-basis coherent fork | 作为更大 hierarchy 链的条件入口保留 | 不取得 native preparations，也不证明 rank89 是 rank3 或 physical three-space |

**定理 8.18（边界声明）。** 本节的 Born summand、native complex density、
原作用和有限 reduction 都是类的前件。因而本节不证明 unrestricted Born/Hilbert
uniqueness，不推导 complex amplitudes、native gates、Hilbert/density structure
或 Born term 的量子起源，也不声称 source acquisition、physical controls、完整
仪器、joint archives、reference/copy acquisition、Hamiltonian、$\hbar$、units、
全 source/process adoption 或 general response laws。rank89 仍是原载体维数；
它不等于 abstract rank3，也不等于 physical three-space。

若把本节接回更大的 quantum-origin 目标，仍须另行满足实际 event saturation、
同源 instruments and records、joint archives/histories、reference/copy、related
resource compatibility、zero/failure/Return、conditional future processes、
physical clock 以及所有原 control permissions。数学 factors、effects、corners、
closures 和 positive maps 不能供应这些 permissions。非加性、history-dependent、
任意 support-preserving response laws 也未被本节分类；fine-zero-only 的精确问题
正是命题 8.15 所留的 open 边界。上述定理及证明是纸面数学，不是 Lean kernel
核验或物理实现；整个原量子起源目标仍未完成。∎

[FLW8]: https://arxiv.org/html/math/0103200v1
[MU8]: ../../../Library/QuantumStates/mullerududec2012selfduality.md
[BMU8]: https://arxiv.org/html/1403.4147v4

## 追加锚（本行以下为增补区）

## 9. 全效应有限区分容量、联合未来秩与零合并的 Born 选择

### 9.1 同一实际未来的两个像商

**定义 9.1（射线响应、像锥、容量与秩）。** 令 $n\ge3$，
$X=\mathbb {CP}^{n-1}$，把射线写为迹一秩一投影 $P$，令 $G=PU(n)$。
给定非空有限标签集 $\Lambda$ 和连续实函数

$$
q_w:X\longrightarrow[0,1],\qquad \sum_{w\in\Lambda}q_w(P)=1.
\tag{9.1}
$$

实际未来是一个固定有限字母表上的全部有限正向时序字 $\mathsf W$，包含空字。
其已给矩阵满足 $K_{af}=K_fK_a$；记 $g_fP=K_fPK_f^*$，并假定
$\{[K_f]:f\in\mathsf W\}$ 在 $G$ 中稠密。固定一个纯 ready $P_e$，
$P_a=K_aP_eK_a^*$，其实际准备轨道于是也稠密。这里只讨论同一个无中途读取
终端接口；数学群闭包没有增加实际字或控制权限。

置

$$
\begin{aligned}
I&=\{\star\}\sqcup(\mathsf W\times\Lambda),\qquad
B=\ell^\infty(I,\mathbb R),\\
\Phi(P)&=\bigl(1,(q_w(g_fP))_{f,w}\bigr),\qquad u(z)=z(\star),\\
J\mu&=\left(\mu(X),\left(\int_Xq_w(g_fP)\,d\mu(P)\right)_{f,w}\right).
\end{aligned}
\tag{9.2}
$$

$M(X)$ 是全部有限实符号正则 Borel 测度，$M_{\rm fin}(X)$ 是有限支撑者。
两种模型分别取以下真正的像，而不预设 $J$ 单射：

$$
\begin{array}{c|ccc}
a&V_a&C_a&K_a\\\hline
\mathrm{alg}&J M_{\rm fin}(X)&J M_{{\rm fin},+}(X)&
J\operatorname {Prob}_{\rm fin}(X)\\
\mathrm{meas}&J M(X)&J M_+(X)&J\operatorname {Prob}(X).
\end{array}
\tag{9.3}
$$

因而 $V_{\rm alg}=\operatorname {span}_{\mathbb R}\Phi(X)$、
$K_{\rm alg}=\operatorname {conv}\Phi(X)$；这里的 convex hull 只取有限组合。
Jordan 分解给 $V_a=\operatorname {span}_{\mathbb R}C_a$。正代表的每个坐标
非负，故 $C_a$ 尖；正代表若总质量为零就是零，所以 $u$ 在非零正元上严格正，
$K_a=C_a\cap\{u=1\}$。锥是 (9.3) 的生成／正测度像锥，不能换成较大的
逐坐标非负行锥。

在每个模型中，整个 proper effect interval 定义为

$$
\mathcal E_a=[0,u]_a
=\{e\in\operatorname {Hom}_{\mathbb R}(V_a,\mathbb R):
e(C_a)\ge0,\ (u-e)(C_a)\ge0\}.
\tag{9.4}
$$

此处不附加行范数连续性。一个有限测量是正线性泛函的有限族，其和为 $u$。
定义 $\operatorname {Cap}(K_a)$ 为可由**同一个**有限测量完美区分的归一状态数的
上确界：允许任意混态 $x_1,\ldots,x_m\in K_a$，要求正效果
$e_1,\ldots,e_m,e_0$ 满足

$$
\sum_{i=0}^me_i=u,\qquad e_i(x_j)=\delta_{ij}\quad(1\le i,j\le m).
\tag{9.5}
$$

$e_0$ 是允许的正余项；它可为零，也可合入一个选定结果。
该容量不同于 native II78–84 中称为 predictive capacity 的线性秩。
后者在这里始终记为

$$
r_{\rm fut}=\sup_{A,F\text{ finite}}
\operatorname {rank}_{\mathbb R}
\bigl(q_w(g_fP_a)\bigr)_{a\in A,\,(f,w)\in F}
\in\mathbb N\cup\{\infty\}.
\tag{9.6}
$$

星列已由任意固定 future 的全部标签之和给出，不另增加一个常数维。
零、常数及重复标签都保留；每个 future 都仍是实际正向字。

### 9.2 有限容量与有限活跃次数的完整等价

**定理 9.2（两个像商上的容量—秩定理）。** 采用定义 9.1。令
$\mathcal H_k^{\mathbb C}$ 为球面上双次数 $(k,k)$ 的复调和多项式下降到 $X$
后的空间，$\mathcal H_k$ 为其实值实型，$E_k$ 为相应正交投影。记

$$
S=\{k\ge1:\exists w,\ E_kq_w\ne0\},\qquad
d_k=\binom{n+k-1}{k}^{\!2}-\binom{n+k-2}{k-1}^{\!2}.
\tag{9.7}
$$

对 $a=\mathrm{alg},\mathrm{meas}$ 分别有

$$
\operatorname {Cap}(K_a)<\infty
\quad\Longleftrightarrow\quad r_{\rm fut}<\infty
\quad\Longleftrightarrow\quad \dim_{\mathbb R}V_a<\infty
\quad\Longleftrightarrow\quad |S|<\infty.
\tag{9.8}
$$

有限分支的准确值为

$$
r_{\rm fut}=\dim V_{\rm alg}=\dim V_{\rm meas}
=1+\sum_{k\in S}d_k=:r,
\qquad \operatorname {Cap}(K_a)\le r.
\tag{9.9}
$$

$S=\varnothing$ 时两个归一基均为 singleton，秩与容量均为一。
$S$ 无限时，无论活跃次数多么稀疏，每个有限 distinct 射线集的 profiles 都是
distinct 极点，并被 (9.5) 的一个共同测量完美区分。这一结论不要求
$J:M(X)\to B$ 单射，也不声称一般容量等于秩或在选择 Born 前容量至多 $n$。

证明。先给出对无限次数及符号测度所需的谱论细节，再连接实际矩阵秩。

在 $X$ 上取归一不变测度 $\nu$。它有全支撑：任一非空开集的群平移覆盖
紧 $X$，有限子覆盖与不变性排除该开集质量为零。沿球面商拉回，
$L^2(X,\mathbb C)$ 恰为 $L^2(S^{2n-1},\mathbb C)$ 的相位不变部分。
Moretti–Pastorello [Theorem 5(a)–(c)][MP9] 的双次数分解、不可约性和互不等价性
表明，相位权 $p-q$ 为零的部分恰给

$$
L^2(X,\mathbb C)=\widehat{\bigoplus}_{k\ge0}\mathcal H_k^{\mathbb C}.
\tag{9.10}
$$

中心在每个 balanced 分量上平凡，故它们是互不等价的不可约 $PU(n)$ 模块；
最高权为 $(k,0,\ldots,0,k)$。共轭保持每个 balanced 分量，其固定空间
$\mathcal H_k$ 的复化就是 $\mathcal H_k^{\mathbb C}$。非零真不变实子空间若存在，
复化便违反复不可约性。因此这是不可约实型，实维等于复维，不乘二。

维数直接复用 native [II78.3 的 (78.7)–(78.8)][II9C] 的一般多项式论证：
令 $N_k=\binom{n+k-1}{k}$，双次数 $(k,k)$ 的 Hermitian 系数空间实维为
$N_k^2$，系数到球面限制单射，乘 $\|z\|^2$ 纳入低次数。
Fischer／对称幂分解给此空间为 $\bigoplus_{j=0}^k\mathcal H_j$，故
$\dim\mathcal H_0=1$、$\dim\mathcal H_k=N_k^2-N_{k-1}^2=d_k$。
此处把 II 的参数 $13$ 换为声明中的 $n$，只消费其表示论方法及
[Masanes–Galley–Müller Appendix A Lemmas 5、7][MGM9]；没有搬用 II 的原十三维来源。
连续 $q_w$ 的原始无限调和级数在此只保证 $L^2$ 收敛。

为避免把 $L^2$ 等式误用于奇异测度，令 $U_gh(P)=h(g^{-1}P)$。
这是 $C(X)$ 上强连续的等距作用，且 $U_hU_g=U_{hg}$。若 $D_k$ 为
$\mathcal H_k^{\mathbb C}$ 上的酉表示，$\chi_k=\operatorname {Tr}D_k$，则

$$
E_kh=d_k\int_G\overline{\chi_k(g)}\,U_gh\,dg.
\tag{9.11}
$$

对连续 $h$，这是 $C(X)$ 中的积分，因被积函数在紧群上范数连续。
归一化因子来自 Schur 正交式

$$
\int_G\overline{D_k(g)_{ab}}D_\ell(g)_{cd}\,dg
=\frac{\delta_{k\ell}\delta_{ac}\delta_{bd}}{d_k}.
\tag{9.12}
$$

该式也可由对两个不可约酉模块间的线性映射作 Haar 平均、应用 Schur 引理，
再取迹固定标量得到。对 $a=b$ 求和说明 (9.11) 在第 $k$ 分量是恒等，
在其它分量为零；有界性和 (9.10) 将它延拓到 $L^2$。连续积分代表与有限维
调和代表几乎处处相等，二者连续且 $\nu$ 全支撑，故处处相等。
实型使投影保持实函数。这是 [MP Proposition 9][MP9] 的投影在本域中的准确使用。
特别地，$E_kq_w$ 先只落在**一致闭**轨道张成内，尚不必在代数列张成内。

记 $\overline{\mathcal F}$ 为 $1$ 与全部 $U_gq_w$ 的一致闭实张成。
每个活跃 $E_kq_w$ 的群轨道由不可约性张成整个 $\mathcal H_k$，所以

$$
\overline{\mathcal F}
=\overline{\mathbb R1\oplus\bigoplus_{k\in S}\mathcal H_k}^{\,\|\cdot\|_\infty}
=\{h\in C(X,\mathbb R):E_\ell h=0\ (\ell\ge1,\ell\notin S)\}.
\tag{9.13}
$$

这里第二个等式可不用原始级数的一致收敛证明。取非负、积分一、支撑趋于单位
的连续 Haar 近似单位 $a$，则 $\int a(g)U_gh\,dg\to h$ 一致。
有限矩阵系数的代数含常数、在共轭下封闭、乘积仍是张量表示的系数，并由
$PU(n)$ 的忠实 adjoint 表示分离点；Stone–Weierstrass 使其在 $C(G)$ 中稠密。
用有限系数多项式 $t$ 在 $L^1$ 中逼近 $a$ 时，积分误差至多
$\|t-a\|_1\|h\|_\infty$。Schur 正交式使 $\int t(g)U_gh\,dg$ 只含有限个
球面不可约分量，而且不会产生 $h$ 没有的分量。这先是 $L^2$ 恒等式，再由
连续性成为逐点恒等式；必要时取实部。所以相应有限调和和一致逼近 $h$，
给出 (9.13)。实际 $g_f$ 稠密及一致连续性说明实际列也有相同的闭张成。
这只是合适的求和逼近，不宣称未经加权的无限级数逐点或一致收敛。

现在设 $J\mu=0$，其中 $\mu$ 是任意有限实符号正则测度。
$L_\mu(h)=\int h\,d\mu$ 是 $C(X,\mathbb R)$ 的有界泛函，复线性延拓后仍满足
$|L_\mu(h)|\le\|\mu\|_{\rm TV}\|h\|_\infty$。
函数 $g\mapsto\int q_w(gP)\,d\mu(P)$ 连续，在全部实际 $g_f$ 上为零，故在
整个 $G$ 为零。因此 $L_\mu$ 消去每个 $U_gq_w$。将其穿过 (9.11) 的连续积分，
对任意 $h\in G$ 得

$$
L_\mu(U_hE_kq_w)
=d_k\int_G\overline{\chi_k(g)}L_\mu(U_{hg}q_w)\,dg=0.
\tag{9.14}
$$

积分交换也由有限界
$d_k^2\|q_w\|_\infty\|\mu\|_{\rm TV}$ 直接保证。若 $k\in S$，选一个非零投影，
其轨道实张成 $\mathcal H_k$，所以 $\mu$ 消去整个 $\mathcal H_k$ 及其复化。
此结论包括奇异、diffuse 和正负相减测度；没有把测度当作 $L^2$ 向量，
也没有将测度积分与无限调和和交换。

取 $\mathcal H_k^{\mathbb C}$ 的 $L^2(\nu)$ 正交基 $Y_1,\ldots,Y_{d_k}$。
其再生核及归一核为

$$
R_k(P,Q)=\sum_{b=1}^{d_k}\overline{Y_b(P)}Y_b(Q),\qquad
Z_k(P,Q)=\frac{R_k(P,Q)}{d_k}
=\frac{P_k^{(n-2,0)}(2\operatorname {Tr}(PQ)-1)}{P_k^{(n-2,0)}(1)}.
\tag{9.15}
$$

对角值群不变，积分为 $d_k$，故 $R_k(P,P)=d_k$。
Jacobi 识别来自 [Koornwinder §3、(3.2)][K9]：其复环境维数 $q=n$、次数为
这里的 $k$，再除以对角值。因而 $Z_k$ 实值，在任一变量中属于第 $k$ 分量，
$Z_k(P,P)=1$，基和的 Cauchy–Schwarz 不等式给全域 $|Z_k(P,Q)|\le1$。

令 $\alpha=n-2\ge1$。对固定 $0<\operatorname {Tr}(PQ)<1$，
[DLMF 18.15.4_5][D9I] 的固定参数 Darboux 公式，在
$-1<2\operatorname {Tr}(PQ)-1<1$ 的内部给分子 $O(k^{-1/2})$。
[DLMF Table 18.6.1][D9E] 给

$$
P_k^{(\alpha,0)}(1)=\binom{k+\alpha}{\alpha},\qquad
P_k^{(\alpha,0)}(-1)=(-1)^k.
\tag{9.16}
$$

所以内部归一核为 $O(k^{-\alpha-1/2})\to0$；正交射线则必须另用端点式，得到
$Z_k(P,Q)=(-1)^k/\binom{k+\alpha}{\alpha}\to0$。
相同射线的核始终为一。内部估计没有越过端点使用，故

$$
Z_k(P,Q)\longrightarrow\mathbf1_{\{P\}}(Q)\qquad(k\to\infty).
\tag{9.17}
$$

若 $S$ 无限，取任意趋于无穷的活跃子序列 $k_j\in S$。(9.14) 使
$\int Z_{k_j}(P,Q)\,d\mu(Q)=0$。对有限测度 $|\mu|$ 应用支配收敛，得到

$$
J\mu=0,\quad |S|=\infty\quad\Longrightarrow\quad
\mu(\{P\})=0\quad(P\in X).
\tag{9.18}
$$

这里无限活跃是不可删的前件；常数响应下 $\delta_P-\delta_Q$ 就属于核。
(9.18) 只恢复 singleton masses，不恢复全部 diffuse 测度。
例如若某个正次数 $\ell$ 不活跃，任取非零实 $h\in\mathcal H_\ell$，
则 $h\nu$ 是非零 diffuse 符号核测度：总质量为零，且与每个实际平移的响应
由调和正交性配对为零。无限 $S$ 允许这种缺项，也不必包含某个尾部的所有次数。

仍在无限分支，对两个像商分别定义

$$
e_P(J\mu)=\mu(\{P\}).
\tag{9.19}
$$

(9.18) 保证换代表不改变值，故这是商上的实线性泛函。
正代表满足 $0\le\mu(\{P\})\le\mu(X)$，所以 $e_P\in\mathcal E_a$。
对 distinct $P_1,\ldots,P_m$，
$e_0=u-\sum_i e_{P_i}$ 在正代表上非负，给出同一个 (9.5) 测量；
$e_{P_i}(\Phi(P_j))=\delta_{ij}$，余项在所列点为零，在其它纯 profile 上为一。
因此任意有限这样的集合共同可区分，并线性独立。
若某概率测度代表 $\Phi(P)$，将其与 $\delta_P$ 相减后用 (9.18)，其在 $P$
的质量必为一，故该代表就是 $\delta_P$。任意把 $\Phi(P)$ 分解为两个归一
像状态的非平凡凸组合，取两者正概率代表后也只能得到 $\delta_P$，所以两者
都等于 $\Phi(P)$。这同时证明两个模型中这些 profiles 的 distinct 性和极端性。

最后核对实际 rank，而不比较无限 Hamel 基数。令

$$
\mathcal F_{\rm act}
=\operatorname {span}_{\mathbb R}\{1,q_w\circ g_f:f\in\mathsf W,w\in\Lambda\}
\subset C(X,\mathbb R).
\tag{9.20}
$$

native II78.3 的评价论证在此逐项使用同一个 dense ready 轨道和 actual futures：
有限个线性独立函数限制到 $\{P_a\}$ 后仍独立；其评价向量必张成对应 Euclidean
空间，否则某个非零线性组合在稠密集上消失，继而处处消失。因此可选有限个
实际行给非奇异评价矩阵。独立函数若为列的有限组合，选入所有参与的实际列，
仍得到至少同样的有限子矩阵秩。反向，任何有限子矩阵秩都受函数空间维数约束。
故 (9.6) 有限恰当且仅当 $\mathcal F_{\rm act}$ 有限维，有限时维数就是它。

有限维时，全部点评价张成 $\mathcal F_{\rm act}^*$：共同消去它们的函数只有零。
坐标把 $V_{\rm alg}$ 与这个对偶识别；对测度积分得到的对偶元素仍在同一个
有限维像内，所以 $V_{\rm meas}=V_{\rm alg}$。反过来，任一行空间有限维就约束
其坐标函数空间有限维。若 $S$ 有限，(9.10) 及连续性给逐点的有限恒等式
$q_w=E_0q_w+\sum_{k\in S}E_kq_w$，所以列空间包含在
$\mathbb R1\oplus\bigoplus_{k\in S}\mathcal H_k$ 内。
它现已有限维，因而一致闭；密度纳入全部数学群平移，(9.11) 及不可约性又纳入
每个活跃分量。故两空间恰相等，给 (9.9)。若 $S$ 无限，上述共同区分表已给
任意大的独立行集；等价地 (9.11) 使一致闭列张成含任意多完整分量，故不可能
有有限维列空间。这给各空间及有限子矩阵 rank 同时为無穷，但不宣称它们的
无限 Hamel 维数相等。

若一个共同测量区分任意混态 $x_1,\ldots,x_m$，对
$\sum_jc_jx_j=0$ 应用其 $e_i$ 得 $c_i=0$，所以 $m\le\dim V_a$。
有限分支由此给 (9.9) 的容量上界；无限分支的 singleton 测量给无穷容量。
$S=\varnothing$ 时所有 $q_w=c_w$，所有归一行相同，秩一且容量一。
这证明两种像商上的全部等价。∎

### 9.3 范数完成与不连续全效应的边界

**定理 9.3（概率像的凸完成及无限分支的严格区别）。** 在定义 9.1 中，

$$
K_{\rm meas}=\overline{\operatorname {conv}\Phi(X)}^{\,\|\cdot\|_\infty},\qquad
\overline{V_{\rm alg}}^{\,\|\cdot\|_\infty}
=\overline{V_{\rm meas}}^{\,\|\cdot\|_\infty}=:B_0.
\tag{9.21}
$$

$K_{\rm meas}$ 范数紧。若 $S$ 无限，则
$K_{\rm alg}\subsetneq K_{\rm meas}$、$V_{\rm alg}\subsetneq V_{\rm meas}$，
而 (9.19) 的效果在行范数下不连续。在 $V_{\rm meas}$ 上甚至存在不同全效应，
它们在每个纯 profile 上的限制相同。故 (9.21) 不将正则测度像空间宣称为它的
Banach 完成，也不将全代数对偶换成行连续对偶。

证明。紧 $G\times X$ 上有限个 $q_w(gP)$ 一致连续，故 $P\mapsto\Phi(P)$
在全未来上确界范数中连续。对任意固定符号测度，各坐标积分随 $g$ 连续；
实际 $g_f$ 稠密，所以实际 future 上确界等于全群上确界。
函数族

$$
\mathcal Q=\{1\}\cup\{q_w\circ g:g\in G,w\in\Lambda\}
\subset C(X)
\tag{9.22}
$$

是紧的，因为它是有限个紧群的范数连续像之并。
若 $\mu_\beta\to\mu$ 在概率测度的 weak-* 拓扑中收敛，取 $\mathcal Q$ 的有限
$\varepsilon$ 网 $h_1,\ldots,h_N$，有

$$
\|J\mu_\beta-J\mu\|_\infty
\le\max_j\left|\int h_j\,d(\mu_\beta-\mu)\right|+2\varepsilon.
\tag{9.23}
$$

先令 $\beta$ 趋于极限再令 $\varepsilon\downarrow0$，证明 weak-* 到行范数的
连续性，而不只是逐坐标连续。概率测度集 weak-* 紧，故其像紧且闭凸，包含
$\Phi(X)$。反向，用有限小开覆盖的 Borel 分割，将各块概率质量放到该块一点；
$\Phi$ 的一致连续性使所得有限原子重心在行范数中任意接近原重心。
连续且紧的 $\Phi$ 值域可分，所以这里也确实存在 $B$ 中的 Bochner 积分。
因此得到第一式。对符号测度的正、负部分分别作相同近似，得到第二式。

不变概率 $\nu$ 无原子：传递性使各 singleton 质量相同，任意大的有限点集迫使
该共同质量为零。若无限 $S$ 下有 $J\nu=J\eta$、$\eta$ 为有限符号原子测度，
(9.18) 迫使 $\eta$ 的每个原子质量为零，故 $\eta=0$，与归一化坐标矛盾。
这同时给出两处严格包含。取 $Q_j\ne P$、$Q_j\to P$，则
$\Phi(Q_j)\to\Phi(P)$ 范数收敛，但 $e_P$ 的值从零跳到一，故不连续。

进一步定义总原子质量泛函

$$
A(J\mu)=\sum_{Q\in X}\mu(\{Q\}).
\tag{9.24}
$$

有限符号测度只有可数个非零原子，且该和绝对收敛、绝对值至多总变差。
(9.18) 保证它与代表无关；有限个测度相加时对其原子集的可数并求和，说明它
实线性。对正代表有 $0\le A\le u$，所以 $A,u$ 都是 $V_{\rm meas}$ 的全效应。
它们在每个 $\Phi(P)$ 上都等于一，但在 $J\nu$ 上分别为零和一。
等价地，非零 proper effect $u-A$ 消去全部纯 profiles，却不消去 diffuse 重心。
这不与 $V_{\rm alg}$ 上纯限制决定线性泛函矛盾，因为后者由纯行**代数张成**；
$V_{\rm meas}$ 只有闭张成关系。数学全效应的定义在无限分支确实容许这种
行不连续性。∎

### 9.4 有限分支的同域、同锥与最小值

**定理 9.4（有限容量后的精确域匹配）。** 若定理 9.2 的任一等价有限条件成立，
则

$$
\begin{gathered}
V_{\rm alg}=V_{\rm meas}=B_0=:V,\qquad
K_{\rm alg}=K_{\rm meas}=\operatorname {conv}\Phi(X)=:K,\\
C_{\rm alg}=C_{\rm meas}=\operatorname {cone}K=:C,
\qquad \mathcal E_{\rm alg}=\mathcal E_{\rm meas}=[0,u].
\end{gathered}
\tag{9.25}
$$

这里 $K$ 紧、$C$ 闭尖生成，$u$ 在非零正元上严格正。
实际 ready 行的实张成也是 $V$，其闭凸包为 $K$，闭生成锥为 $C$。
所有 distinct 轨道 profiles 都是 exposed 极点，且 $\operatorname {ext}K=\Phi(X)$。
对任意归一 $p,x\in K$，定义

$$
\mathcal F_p=\{e\in[0,u]:e(p)=1\},\qquad
T_p(x)=\min_{e\in\mathcal F_p}e(x).
\tag{9.26}
$$

这个最小值达到，包含下文要求的全部混态参数。

证明。定理 9.2 已给有限维的共同像空间。紧 $\Phi(X)$ 的仿射维数至多 $r-1$；
Carathéodory 定理使每个凸组合至多需要 $r$ 项，故其凸包紧。
与 (9.21) 合用即得共同 $K$，再取正倍和张成得 (9.25)。若 $t_jk_j$ 收敛，
$t_j=u(t_jk_j)$ 收敛；$t_j\to0$ 时由 $K$ 有界得零极限，否则由紧性取到
仍在锥内的极限，故 $C$ 闭。尖性和生成性已在定义 9.1 得出。
实际准备轨道稠密，$\Phi$ 范数连续，所以实际行的闭包是 $\Phi(X)$；有限维
线性子空间闭，故实际行张成正好是 $V$。这也说明只从实际行定义的有限 rank
没有被悄悄加强为另一完成域的 rank。

经坐标拉回，$V^*$ 与有限空间 $\mathcal F_{\rm act}$ 识别：坐标泛函分离 $V$，
有限维使它们张成整个对偶，其拉回像恰为 (9.20)。有限维闭性及实际密度使此
空间在全 $G$ 拉回下不变。对偶作用 $L_g$ 因此满足
$L_g\Phi(P)=\Phi(gP)$，保持 $C,K,u$，连续且可逆。
平均一个内积得到不变内积，各 $\Phi(P)$ 的范数相同。
固定 profile $p$ 的高度 $z\mapsto\langle p,z\rangle$ 在轨道上的唯一最大向量是
$p$，由等范数的 Cauchy–Schwarz 等号条件可知；有限凸组合将唯一性传到 $K$。
反向，$K$ 的极点有有限轨道凸表示，极性迫使全部正权项等于该点。
这也处理 profile 映射尚未证明忠实的情形及 singleton 情形。

最后从 $K$ 取 $V$ 的一组基。每个 proper effect 在这些基向量上的值都在
$[0,1]$，所以 $[0,u]$ 在有限维对偶中有界；定义不等式又使它闭，故紧。
$\mathcal F_p$ 含 $u$ 且是闭子集，所以非空紧。评价连续，故 (9.26) 达到。
效果集的一致有界性还给 $T_p$ 连续且 Lipschitz；它是非负函数的下包络。
这些事实只为同域比较提供数学基础，不给实际准备或效果执行。∎

## 追加锚（本行以下为增补区）

# 量子起源 XIX：qubit 共同圆尺与乘积零面

本卷承接 [XVIII：半转、准备与全域效应](QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md)。下文240、250编号均指该卷，260编号指本卷；[固定前文](https://github.com/the-omega-institute/trureturing/blob/be7bffe8eb6ceabc04bc172939b87cbfce7c8875/docs/develop/theory/QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md)给240的实际面、切方向和qutrit接口，以及250.1的强全有限背景与共同尺定义。

范围是原局部实维数四时的完整候选及所用普通条件证明；过程、设备与极限条件见260.8。

## 260. 原四维局部系统的共同圆尺与乘积零面重建

**定义 260.0（矩阵记号）。** $H_d=\operatorname{Herm}_d(\mathbb C)$，$\operatorname{PSD}_d$ 是其正半定锥；$\mathcal D(S)$ 是复子空间 $S$ 上迹一 PSD 矩阵的全体，$\mathcal D_d=\mathcal D(\mathbb C^d)$。$P_v=vv^*/\|v\|^2$ 表示非零向量的归一秩一投影；跃迁公式中的 $v,w$ 均取单位向量。$\operatorname{Ad}_U(X)=UXU^*$，$T_i$ 是指定乘积基中第 $i$ 因子的转置，$\oplus$ 用于线性直和，$\mathbin{\oplus}$ 用于转置位时表示模二相加。

**定义 260.1（限定原维数的全有限候选）。** 取250.1的完整强实背景，并限定原局部空间 $\dim_{\mathbb R}V=4$。具体地，对每个有限 $N\ge0$ 保留整个 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成锥 $C_N$、严格正乘积单位 $u_N=u^{\otimes N}$、紧底 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$、完整效应 $\mathcal E_N=[0,u_N]_{C_N^*}$ 及全部有限单位分解；零层为 $(\mathbb R,\mathbb R_+,1)$。原乘积配对分离整个联合空间，重括号是规范恒等，全部位置置换及其逆为正，单位丢弃为正。对所有有限 $a,b\ge0$，在两块的全部原正输入和全部原正泛函上要求

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}\subseteq C_a\otimes_{\max}C_b.
\tag{260.1}
$$

这不是只到三层的截断背景。$F_N(A)$ 表示最小实际面，$B_N(p,q)=F_N(p,q)$。候选只在**整个原 $K_3$** 要求 L2 和存在正定型 $g_3$ 满足250.1的 $\mathsf A_2(g_3)$：任意不同原纯点生成的整个实际面都是三球，且这些球在同一 $g_3$ 的限制下为圆球。量词包括全部纠缠纯点；不同球的中心和半径均可不同。除原维数四及上述强背景外，不另加 TC、TF9、NC、正面投影、物理旋转、CP 操作、标准联合锥、共同半径、自对偶齐性、Jordan 结构、谱性或任意面效应的同预算延拓。

**定理 260.2（原局部维数四时的完整双向候选）。** 在260.1的强全有限背景及 $\dim_{\mathbb R}V=4$ 下，下列等价：整个原 $K_3$ 满足 L2 及某把共同圆尺 $\mathsf A_2(g_3)$；存在同一个保单位实线性同构 $\theta:V\to\operatorname{Herm}_2(\mathbb C)$，使所有有限 $N\ge0$ 同时满足

$$
\theta^{\otimes N}(C_N)=\operatorname{PSD}_{2^N},\qquad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}.
\tag{260.2}
$$

结论包含全部原混态、纯态、效应和原配对；$N=0$ 取恒等。以下260.3—260.7支付正向证明，反向用 Hilbert–Schmidt 尺。所有结论均为相对于明确列出的成熟拓扑及已发表纸面供应的普通条件数学；此维数限定始终属于主张，不推出一般原维数的 $\mathsf A_2\Rightarrow\mathrm{TC}$。

**引理 260.3（共同尺下仿射维数至多十的外三角）。** 在240.1的任意有限维原域中假设 L2 与 $\mathsf A_2(g)$。固定 $B=B(a,b)$、$S=P\cap B\simeq S^2$、$p\in P\setminus B$，令 $F=F(p,a,b)$。平移 $p$ 为零，沿用240.2的 $U,d,D,E_y,H,N$，并定义

$$
r=\dim\operatorname{span}N,\qquad
L=\bigcap_{\ell\in N}\ker\ell\subset U,\qquad \dim L=d-r.
\tag{260.3}
$$

若 $d\le10$，则 $d=8$、$r=4$、$\dim H=4$，$F$ 的原纯点恰为全部 $B(p,y)$、$y\in S$ 的纯壳之并，且 $H=E_a\oplus E_b$。特别地，该外三角满足 TC。本引理是待用的推论，不是260.1的候选输入。

证明。（一）实际面、支撑和所有纯点的切向。精确复用240.2：有限实际面 $J=K\cap\operatorname{aff}J$，因而闭且紧；$J=\operatorname{conv}(P\cap J)$，$\operatorname{ext}J=P\cap J$。后一个结论也可直接从 $K$ 的有限极点分解看出：面内点的每个正权分量都在该面，不要求 $P$ 闭。该定理给 $\dim D=4$、限制 $N\to\operatorname{Aff}(B)_+$ 满射和 $d\ge8$。其中支撑是在真面 $B(p,y)$ 的相对内部取得，限制到 $B$ 为正倍数的 $1-\widehat y\cdot z$；这些射线生成完整四维 Lorentz 锥，未假设零面已等于该球。

令 $M=\operatorname{span}N$。限制满射给 $r\ge4$、$D\cap L=0$。还需加强切向的量词：对任意 $q\in P\cap F\setminus\{p\}$ 及 $\ell\in N$，$\ell$ 在 $p$ 为最小；沿实际球 $B(p,q)$ 的壳经过 $p$ 的任意双侧光滑曲线求导，得

$$
\tau_p(q)\subseteq L,\qquad H\subseteq L,\qquad D\cap H=0.
\tag{260.4}
$$

这对扇外原纯点同样成立。精确复用 XII引理159.5 [B260]：不同实际二点球的齐次实张成只交于零或共同纯射线。其方向在 $\ker u$，而 $u(p)=1$，故通过 $p$ 的不同球连整个方向空间都交于零，切二维平面当然也交于零。对不同 $y,z\in S$，$B(p,y)\ne B(p,z)$，否则共同球含 $B(y,z)=B$，严格凸球的非单点面只能为自身，与 $p\notin B$ 矛盾。因此 $E_y\cap E_z=0$，$\dim H\ge4$，并有 $\dim H\le d-r$。

（二）离对角线的实际圆球连续性。设 $a_i\to a,b_i\to b$ 都是原纯点，$a\ne b$。实际圆三球 $B(a_i,b_i)$ 均在紧 $K$ 内，故中心、半径有界；其三维方向位于紧 Grassmann 流形。任意子列都有中心、半径、方向同时收敛的子列，极限为含于闭 $K$ 的圆三球 $B'$；半径至少 $\|a-b\|_g/2>0$，且不同 $a,b$ 在其壳上。中点 $m=(a+b)/2\in\operatorname{ri}B'$；从 $m$ 向 $B'$ 任意点反向延长线段，面性质给 $B'\subseteq F_K(m)=B(a,b)$。两球仿射维数同为三，故仿射空间相同。

在同一 Euclidean 三空间，若半径 $r'$、中心 $c'$ 的球含于半径 $r$、中心 $c$ 的球，则 $\|c-c'\|+r'\le r$。内球某壳点也在外壳时，三角不等式须取等号；若中心不同，该点只能是中心连线的一个指定端点；若中心相同，公共壳点迫使半径相同。故不相等的嵌套圆球至多有一个公共壳点。这里有 $a,b$ 两点，迫使 $B'=B(a,b)$。所有子列极限唯一，证明中心、半径和方向连续；切平面由球方向及中心到端点的径向连续决定。因此 $y\mapsto E_y$ 在固定紧 $S$ 上连续。此论证只使用端点极限本身仍为不同原纯点，不使用整个 $P$ 的紧性。

（三）五维中的带符号饱和。先证明一个所需拓扑事实。若连续族 $E_y\subset\mathbb R^5$、$y\in S^2$ 都是二维线性平面，且 $y\ne z$ 时 $E_y\cap E_z=0$，则不存在另一个二维平面同时避开全部 $E_y$。把 Grassmann 流形的秩二实 tautological 丛拉回 $S^2$；因 $S^2$ 单连通，该丛可定向。其单位圆丛 $T$ 是紧、连通、无边界的可定向三维流形。评价

$$
j:T\longrightarrow S^4,\qquad j(y,v)=v
\tag{260.5}
$$

因交为零而单射，故是到紧像 $A$ 的同胚。$A$ 非空、局部可缩，$H^3(A;\mathbb Z)=\mathbb Z$；它是 $S^4$ 的真子集，否则这与 $H^3(S^4;\mathbb Z)=0$ 矛盾。按连续定向及内积逐纤维选正 quarter-turn $J$，$(y,v)\mapsto(y,\cos t\,v+\sin t\,Jv)$、$0\le t\le\pi$ 给恒等到纤维负号的同伦。因此环境对径 $\tau(v)=-v$ 限制到 $A$ 后在 $H^3$ 上为恒等。

此处准确使用 Hatcher [A260] 推论3.45的 Alexander 对偶及定理3.44的相对 cap／直极限构造。其适用条件正是紧、局部可缩、非空真子集，不要求局部平坦或光滑嵌入。令

$$
\mathcal D:H^3(A;\mathbb Z)\xrightarrow{\ \cong\ }
\widetilde H_0(S^4\setminus A;\mathbb Z).
\tag{260.6}
$$

开补集局部道路连通，故右端为 $\mathbb Z$ 表明恰有两个连通分支。符号不能省略：cap 自然性 $f_*(c\cap f^*\phi)=f_*c\cap\phi$ 连同自然连接映射，以及 $\tau_*[S^4]=-[S^4]$，给

$$
\tau_*\mathcal D\bigl((\tau|_A)^*\alpha\bigr)=-\mathcal D(\alpha).
\tag{260.7}
$$

这是由环境基本类推出的等式，不是向书中另借一个无符号自然性断言。因 $(\tau|_A)^*=1$，$\tau$ 在补集的约化零阶同调上为 $-1$，从而交换两个分支。若另有二维平面 $E$ 与全部 $E_y$ 零交，其单位圆就在补集中，是连通且对径不变的集合；它须在一个分支内，却又被 $\tau$ 送入另一个分支，矛盾。没有使用 Euler 数的预设。

（四）当 $d-r\le5$ 时先得纯扇穷尽。把 $L$ 线性嵌入 $\mathbb R^5$，对连续、两两零交的 $E_y$ 应用（三）。若 $q\in P\cap F$ 不在任何 $B(p,y)$ 的纯壳，$q\ne p$，且 $B(p,q)$ 与每个扇球不同；否则 $q$ 作为原纯点就在那个球壳。由（一），它的整个二维切平面在 $L$，并与全部 $E_y$ 零交，违反（三）。反向包含由扇球是 $F$ 内的实际面及其极点就是原纯点直接得到。因此

$$
P\cap F=\bigcup_{y\in S}\operatorname{ext}B(p,y).
\tag{260.8}
$$

（五）纯扇穷尽通过两颗交叉球迫使 TC。现在只假设(260.8)。扇球方向为 $\mathbb Ry\oplus E_y$，故有限纯生成给 $U=D\oplus H$。令 $Q:D\oplus H\to D$ 为沿 $H$ 的投影，$I(x)=x/\|x\|_g^2$。扇球中心 $c_y$ 满足 $g(c_y,E_y)=0$；壳方程及 $y$ 也在壳上给

$$
\|x\|_g^2=2g(c_y,x),\qquad
Qx=\frac{\|x\|_g^2}{\|y\|_g^2}\,y,\qquad
I\bigl(\operatorname{ext}B(p,y)\setminus\{0\}\bigr)=s_y+E_y,
\quad s_y=I(y).
\tag{260.9}
$$

最后一个等式也直接由 $2g(c_y,Ix)=1$ 得到，反向代回 $I$ 即可。$I(S)$ 是圆二球面 $S'\subset D$：一般圆球面 $x=c+w,\ w\in W,\|w\|^2=R^2$ 的反演满足 $k\|z\|^2-2g(c,z)+1=0$、$P_{W^\perp}z=P_{W^\perp}c\,\|z\|^2$，其中 $k=\|c\|^2-R^2$；消元并完成平方给圆球面或仿射平面。原球面不含零且紧，排除平面。这里 $p\notin\operatorname{aff}B$ 已由240.2支付。

取不同 $s_0,s_1\in S'$、$y_i=I(s_i)$ 及 $E_{y_1}$ 的实基 $v_1,v_2$。点 $q_j=I(s_1+v_j)$ 是扇内原纯点。实际交叉球 $B(y_0,q_j)$ 不含 $p$：若含，则它等于 $B(p,y_0)$，又与不同的 $B(p,y_1)$ 共享 $p,q_j$，违反159.5。故其反演壳 $\Sigma_j$ 为圆二球面，且由(260.8)—(260.9)，$Q\Sigma_j\subset S'$，并含不同的 $s_0,s_1$。

把源球面参数化为 $m+Mt$、$\|t\|=1$，目标中心、半径记为 $c',R'$。恒等式 $\|m-c'+Mt\|^2=R'^2$ 对全部单位 $t$ 成立，比较 $t,-t$ 及二次型给 $M^*(m-c')=0$、$M^*M=\lambda I$。非恒定性给 $\lambda>0$，故秩三；其像是目标方向三空间，于是 $m=c'$，且像遍历整个目标球面。应用于 $Q|_{\Sigma_j}$，其仿射延拓是三维方向间的同构。因此 $\Sigma_j$ 是图

$$
s\longmapsto s+h_j(s),\qquad
h_j(s)=A_j(s-s_0)\in E_{I(s)},\quad
h_j(s_0)=0,\quad h_j(s_1)=v_j.
\tag{260.10}
$$

为简记写 $E_s=E_{I(s)}$。由（二）的连续性，在 $s_0$ 沿球面取差商，得 $A_j(T_{s_0}S')\subset E_{s_0}$。弦 $s_1-s_0$ 横截该切平面，故 $\operatorname{im}A_j\subset W_0=E_{s_0}\oplus E_{s_1}$。若非零实组合 $h=\alpha h_1+\beta h_2$ 在某 $s\ne s_0$ 为零，其线性部分 $A$ 消去 $n=s-s_0$。对关于通过 $c'$、法向为 $n$ 的中心超平面的球面反射，配对点 $t,t'$ 满足 $t-t'\in\mathbb Rn$，因而 $h(t)=h(t')$。离固定大圆时 $t\ne t'$，这个值同时在零交的 $E_t,E_{t'}$ 内，只能为零。由稠密性与连续性，$h$ 处处为零；但 $h(s_1)=\alpha v_1+\beta v_2\ne0$，矛盾。

因此 $h_1(s),h_2(s)$ 对每个 $s\ne s_0$ 张成 $E_s$，都在 $W_0$；$E_{s_0}$ 本就在其中，故 $H=W_0$、$\dim H=4$。任意两个不同端点的切平面同样零交并张成 $H$，特别是 $H=E_a\oplus E_b$。于是 $U=D\oplus H$ 给 $d=8$；$H\subset L$ 及 $r\ge4$ 给 $r=4$。交叉壳落在扇内并非额外前件，而是(260.8)和实际面的原纯性给出的。

（六）处理 $r=4,d\le10$ 的分支，不预设(260.8)。限制 $R:M\to\operatorname{Aff}(B)$ 是四维线性同构，且把 $N$ 恰送到 $\operatorname{Aff}(B)_+$。其转置定义满射 $Q_0:U\to\operatorname{Aff}(B)^*$，满足 $Q_0(F-p)$ 在对偶 Lorentz 锥内、$Q_0(y-p)=\operatorname{ev}_y$。令 $\ell_y$ 为 $f_y(z)=1-\widehat y\cdot z$ 的唯一提升，$G_y=\{x\in F:\ell_y(x-p)=0\}$。对偶 Lorentz 零面为 $\mathbb R_+\operatorname{ev}_y$，所以

$$
B(p,y)\subseteq G_y,\qquad
\dim\operatorname{aff}G_y\le\dim\ker Q_0+1=d-3\le7.
\tag{260.11}
$$

若严格包含，有限原纯分解给 $q\in P\cap G_y\setminus B(p,y)$；实际外三角 $F(p,y,q)\subseteq G_y$，却由240.2仿射维数至少八，矛盾。因此 $G_y=B(p,y)$。对任意 $q\in P\cap F\setminus\{p\}$，球 $B(p,q)$ 是 $F$ 的真面；在其相对内部支撑，给非零 $\ell\in N$ 消去 $q-p$。$R\ell$ 是非零正 Lorentz 泛函，因此 $Q_0(q-p)$ 在对偶边界。它不能为零，否则 $q$ 同时属于所有 $G_y=B(p,y)$，而任取不同 $y,z$ 的两球交仅为 $p$。非零边界向量在某唯一极射线 $\mathbb R_+\operatorname{ev}_y$，从而 $q\in G_y$。得到(260.8)，再用（五）得 $d=8,r=4$ 和 TC。

（七）最后，$r\ge4$。若 $r=4$ 用（六）；若 $r\ge5$ 且 $d\le10$，则 $d-r\le5$，用（四）、（五）仍得 $d=8,r=4$，排除此分支。特别地 $d=10,r=\dim H=5$ 不可能。引理证毕。$\square$

**命题 260.4（分类前的实际低层面与原 qubit 坐标）。** 在260.1下，整个 $K_2,K_1$ 继承 L2 与共同圆尺，且存在保单位同构 $\theta:V\to H_2=\operatorname{Herm}_2(\mathbb C)$ 把 $C_1$ 送到 $\operatorname{PSD}_2$；这里尚未对 $C_2,C_3$ 作矩阵正性判断。

证明。最大界和闭锥双极性给正条件态：对 $z\in C_{a+b}$、$f\in C_a^*$，$(f\otimes\operatorname{id})z\in C_b$。若归一 $z$ 的 $b$ 边缘是原纯点 $p$，则对 $0\le f\le u_a$，条件态在 $[0,p]$ 中，故为 $\lambda_f p$。正泛函张成局部对偶，乘积配对分离联合空间，所以 $z=x\otimes p$；丢弃给 $x\in K_a$。最小界给反向包含。于是纯边缘纤维正是整个实际纯旁观面 $K_a\otimes p$，产品纯点亦为原纯点。

面内极点就是其包含的原极点，面内生成的二点面也就是原二点面，故 L2 限制到该实际面。$x\mapsto x\otimes p$ 为保单位线性单射，共同尺沿它拉回仍正定并把全部实际球变为圆球，故 $\mathsf A_2$ 同样下降。先取 $a=2,b=1$，再取 $a=b=1$，依次得到整个 $K_2,K_1$ 的条件。

$K_1$ 仿射维数三，至少有两不同纯点。其实际二点三球已有整个仿射维数；有限维凸体的真面维数严格较小，所以它就是 $K_1$。取一个仿射球坐标 $x\mapsto r(x)\in\overline{\mathbb B}^3$，令 $\theta(x)=(I+r(x)\cdot\sigma)/2$ 于归一底，再沿锥作保迹线性延拓。因底仿射满维，这是 $V\to H_2$ 的同构；Pauli 特征值 $(1\pm\|r\|)/2$ 给所述序对应。此后固定这一个初始 $\theta$，全部张量坐标都来自它。$\square$

**命题 260.5（完整两份重建，保留相对转置备选）。** 在 $H_2\otimes_{\mathbb R}H_2=H_4$ 的初始 $\theta\otimes\theta$ 坐标中，整个原 $C_2$ 为 $\operatorname{PSD}_4$ 或 $T_1\operatorname{PSD}_4$，其中 $T_i$ 为固定基中第 $i$ 因子的转置。证明只使用此两份域的最小／最大界、实际 L2 和共同尺。

证明。（一）一个乘积零角包含实际完整 qutrit。最小／最大界给可分正锥 $\subseteq C_2\subseteq$ block-positive 锥。所有局部秩一效应乘积都是原正泛函且为正收缩：$u\otimes u-e\otimes f=(u-e)\otimes f+u\otimes(u-f)\ge0$。记 $p_{ij}=P_{|ij\rangle}$，取实际暴露零面

$$
Z=\{X\in K_2:\langle11|X|11\rangle=0\}.
\tag{260.12}
$$

对 block-positive $X$，固定任一局部向量的条件 $2\times2$ 矩阵为 PSD。其 $11$ 对角为零，迫使 $X_{11,01}=X_{11,10}=0$。连同实约束 $X_{11,11}=0$，共五个独立实线性约束，故 $\dim\operatorname{span}Z\le11$、$\operatorname{affdim}Z\le10$。三个产品点 $p_{00},p_{01},p_{10}$ 是原纯点；它们的实际面 $F$ 在 $Z$ 内。行球 $B(p_{00},p_{01})$ 恰为260.4的纯旁观面，$p_{10}$ 不在其中。任何含这三点的实际球都须含这个非单点行面，严格凸性使其等于行球，矛盾。因此是外三角，260.3给 $\operatorname{affdim}F=8$。

现在只把 $F$ 当作自身齐次张成上的整个锥，给其**内禀**完整正对偶区间。它继承 L2；其任意三点实际面维数至多八，所以满足240.1的 TF9。精确应用240.5于这个原域及生成 $F$ 的外三角，得到保迹序同构 $\Phi:H_3\to\operatorname{span}F$、$\Phi(\mathcal D_3)=F$。未断言 $Z=F$，也未延拓任意 $F$ 效应到联合原菜单。

（二）正乘积效应决定正确的 Schur 配对。令 $w_0,w_1,w_2$ 为三个产品纯点的 qutrit 纯提升。四个对角产品效应的拉回 $E_{ij}$ 为 PSD；$E_{11}=0$，其余三个和为 $I$，且在三个提升上的取值为 Kronecker delta。正收缩期望为一或零分别给 $E_iw_i=w_i$、$E_iw_j=0$，所以三个 $w_i$ 互相正交。以它们为基后，$E_{00}=P_0,E_{01}=P_1,E_{10}=P_2$。

实际行、列面识别 $\Phi$ 在 $01$、$02$ 支持上的作用。固定两极的 Bloch 球仿射自同构在横向平面是一个相位乘以恒等或复共轭；独立调整基向量1、2的相位可消掉两个相位。记行的共轭位为 $r$，列的共轭位为 $c$。对任意局部单位向量 $x,y$，置 $X_0=x_0\overline{x_1},X_1=\overline{X_0}$、$Y_0=y_0\overline{y_1},Y_1=\overline{Y_0}$。正拉回 $M=\Phi^*(P_x\otimes P_y)$ 满足

$$
\begin{gathered}
(M_{00},M_{11},M_{22})=(|x_0y_0|^2,|x_0y_1|^2,|x_1y_0|^2),\\
M_{01}=|x_0|^2Y_r,\qquad M_{02}=|y_0|^2X_c,\\
M_{12}=\frac{M_{10}M_{02}}{M_{00}}=X_c\overline{Y_r}\quad(M_{00}>0).
\end{gathered}
\tag{260.13}
$$

前两个主子式为零；以 $M_{00}$ 作 Schur 补，补矩阵 PSD 且对角为零，故非对角亦为零，给最后一式。分子中的 $|x_0|^2|y_0|^2$ 完全消掉，不留下非线性分母；$x_0y_0=0$ 的情形由连续性补齐。令 $J:H_3\to H_4$ 为 $S_0=\operatorname{span}_{\mathbb C}\{|00\rangle,|01\rangle,|10\rangle\}$ 的标准支持嵌入，这些恰是 $T_1^cT_2^rJ$ 的伴随配对。秩一 PSD 矩阵实张成每个 Hermitian 因子，故其乘积效应张成整个十六维对偶，所有配对相等遂给

$$
\Phi=T_1^cT_2^rJ,\qquad
F=T_1^{\delta}\mathcal D(S_0),\qquad\delta=c\mathbin{\oplus}r.
\tag{260.14}
$$

全转置保 $\mathcal D(S_0)$，所以集合只有两类。特别注意：行位 $r$ 作用在物理因子2，列位 $c$ 作用在物理因子1。

（三）以闭而不交的覆盖固定所有乘积框架的方向。参数 $g=(U,V)$ 遍历连通 $U(2)\times U(2)$，定义

$$
D_0(g)=\operatorname{Ad}_{U\otimes V}\mathcal D(S_0),\qquad
D_1(g)=T_1\operatorname{Ad}_{\overline U\otimes V}\mathcal D(S_0)
=\operatorname{Ad}_{U\otimes V}T_1\mathcal D(S_0).
\tag{260.15}
$$

这里只作数学坐标变换，未假设这些局域旋转对未知原锥为正。两候选含同一三个框架产品点及其平均 $\rho_g$；$\rho_g$ 在两者中均为相对内部点。（二）逐框架应用，给实际生成面恰为其中一个。定义 $A_i=\{g:D_i(g)\subset K_2\}$。对每个固定 $\rho\in\mathcal D_3$ 候选像连续，$K_2$ 闭，故 $A_i$ 闭；两者覆盖参数空间。

若某框架同时在两集内，实际面 $F_g$ 等于一个候选，又含另一个候选的相对内部点 $\rho_g$。从该点在另一个候选内反向延长任意线段，面性质迫使另一候选全在 $F_g$。这不可能：标准框架中 $\operatorname{span}D_0$ 含 $01$—$10$ 的实、虚两个方向而不含 $00$—$11$ 两方向；$\operatorname{span}D_1$ 恰交换这两组。两张成均九维而不同，任一共同局域共轭保留此差别，不能相互包含。因此闭覆盖不交，连通性迫使一个方向处处成立。这不需要实际面映射连续。

（四）全部标准纯点及实际标准二支持球。若固定方向为1，暂对整个坐标施加 $T_1$；迹、产品最大／最小界、实际面和拉回的共同尺都保留。此暂定坐标中，每个产品向量的正交补都承载实际完整标准 $\mathcal D_3$。任意 $\psi\in\mathbb C^2\otimes\mathbb C^2$ 都正交某非零产品向量：固定非零第一因子，第二因子取所得线性泛函的核。因此每个 $P_\psi$ 是这些实际 qutrit 面的极点，从而是原纯点；谱分解给整个标准 PSD 底包含于 $K_2$。

还需证明标准二支持球是**实际**球。这个论证适用于任意矩阵维数：已知全部标准秩一态是原纯点且整个 PSD 底在 $K$ 内，取不同标准纯点 $p,q$，$S=\operatorname{span}_{\mathbb C}\{\psi,\phi\}$。$m=(p+q)/2$ 在 $\mathcal D(S)$ 相对内部；对其任意 $\rho$ 可取小 $\epsilon>0$ 写 $m=\epsilon\rho+(1-\epsilon)\sigma$、$\sigma\in\mathcal D(S)$。因 $m\in B(p,q)$ 且 $B(p,q)$ 为面，得到 $\mathcal D(S)\subset B(p,q)$。二者仿射维数都是三，且 $\mathcal D(S)$ 每个边界点都是原纯点。若后者严格更大，从前者内部点向多出的点作射线，就把前者某边界点放在后者相对内部，违反极性。因此 $B(p,q)=\mathcal D(S)$。未比较半径，也未要求这两个点共同正交一个产品向量。

（五）排除额外原纯点的通用 $2\times b$ 论证。设 $b\ge2$，已取得全部标准秩一原纯点及上述实际标准球，并有产品效应正性。固定一个标准 Schmidt 秩二点 $p=P_\psi$，在数学 Schmidt 基中写 $\psi=\alpha|00\rangle+\beta|11\rangle$、$\alpha,\beta>0$、$\alpha^2+\beta^2=1$。对任意复 $t$ 和 $y=(y_1,\ldots,y_{b-1})$，向量

$$
v=(1,t)\otimes(-\beta t y_1,\alpha y_1,y_2,\ldots,y_{b-1})\perp\psi
\tag{260.16}
$$

是产品向量。在 $\psi^\perp$ 的基 $|01\rangle,\ \beta|00\rangle-\alpha|11\rangle,\ |10\rangle,\ |0k\rangle,|1k\rangle$、$2\le k\le b-1$ 中，它的坐标为 $\alpha y_1,-ty_1,-\beta t^2y_1,y_k,ty_k$。它们是不同单项式 $m_i=t^r y_k$ 的非零倍数：$k=1$ 时 $r=0,1,2$，其余 $k$ 时 $r=0,1$。所有有序乘积 $\overline{m_i}m_j=\overline t^{\,r_i}t^{r_j}\overline y_{k_i}y_{k_j}$ 都是不同的形式单项式。独立的全纯、反全纯变量与实、虚坐标之间为可逆复线性变换；多项式在所有实坐标上为零，故各系数为零。因此若 Hermitian 形式 $A$ 对所有这些 $v$ 满足 $v^*Av=0$，则每个矩阵系数都为零。由非退化实迹配对，得到的是完整算子张成，而非仅向量张成：

$$
\operatorname{span}_{\mathbb R}\{P_v:v\text{ 为产品向量},\ v\perp\psi\}
=\operatorname{Herm}(\psi^\perp).
\tag{260.17}
$$

此处非零 $v$ 可归一化，不改变张成；$b=2$ 时可令 $y_1=1$，三个单项式就是 $1,t,t^2$。

若 $q$ 是额外原纯点，不假设它为 PSD，令 $E=\tau_p(q)$。每个归一产品效应 $P_v$ 在原 $K$ 非负且在 $p$ 为零，沿实际 $B(p,q)$ 的双侧壳曲线求导得 $\operatorname{Tr}(P_vX)=0$、$X\in E$。(260.17)给 $\Pi_{\psi^\perp}X\Pi_{\psi^\perp}=0$，再用 $\operatorname{Tr}X=0$ 得

$$
E\subset H_p=\{\psi z^*+z\psi^*:z\perp\psi\}.
\tag{260.18}
$$

只需取一个非零 $X\in E$，对应 $z\ne0$。已是实际面的标准球 $\mathcal D(\operatorname{span}_{\mathbb C}\{\psi,z\})$ 的切平面 $E_z$ 含这个 $X$。故 $E\cap E_z\ne0$；159.5迫使两颗实际球相同，进而 $q$ 在标准 $\mathcal D_2$ 内。它作为原纯点是这个面的极点，只能为秩一标准态，矛盾。这里没有声称整个 $E$ 都在某一个 $E_z$ 内。

对本命题取 $b=2$，排除了全部额外原纯点；紧凸底的有限极点分解遂给整个 $C_2=\operatorname{PSD}_4$。撤销（四）的暂时 $T_1$，得到原初始坐标中的两个备选，命题证毕。$\square$

**命题 260.6（任意 $2\times b$ 的实际压缩和完整重建）。** 设 $C\subset H_2\otimes_{\mathbb R}H_b$ 为闭尖生成锥，单位为迹，满足两标准局部 PSD 因子的最小／最大界，整个归一底有实际 L2 与共同圆尺。对任意有限 $b\ge2$，整个 $C$ 恰为 $\operatorname{PSD}_{2b}$ 或 $T_1\operatorname{PSD}_{2b}$。$b=1$ 时最小、最大界相同，直接给 $\operatorname{PSD}_2$。

证明。（一）条件支持使整个二支持压缩成为实际 $2\times2$ 域。令 $M_B=\operatorname{Tr}_A$，$S\subset\mathbb C^b$ 为复二维空间，取

$$
F_S=\{z\in K:M_Bz\in\mathcal D(S)\},\qquad
L_S=H_2\otimes_{\mathbb R}\operatorname{Herm}(S).
\tag{260.19}
$$

边缘为正、$\mathcal D(S)$ 是 PSD 实际面，故 $F_S$ 是实际面；它也等于正泛函 $z\mapsto\operatorname{Tr}((I\otimes P_{S^\perp})z)$ 的零面。但仅有一个零读数尚不足以消去联合交叉支持。对面锥内 $z$ 和每个 $A\succeq0$，条件态 $\sigma_A=\operatorname{Tr}_A((A\otimes I)z)$ 为 PSD。取 $A\preceq cI$，又有

$$
0\preceq\sigma_A\preceq cM_Bz.
\tag{260.20}
$$

右端支持在 $S$，故 $\sigma_A$ 也支持在 $S$；这由正矩阵在零对角方向整行整列为零立即得到。正 $A$ 张成 $H_2$，用其条件态展开联合张量，得 $z\in L_S$，包括全部交叉支持系数消失。反向，$z\in C\cap L_S$ 的正边缘必支持于 $S$。于是该实际面锥准确为 $C\cap L_S$。

支持于 $S$ 的正产品由最小界属于此锥，实张成整个十六维 $L_S$。内禀最大界通过任意 $A\succeq0$ 和 $Q\succeq0$ 于 $S$ 测试：把 $Q$ 用包含映射 $J$ 送为全局正矩阵 $JQJ^*$，即可使用原最大界。故完整压缩域有标准两因子的内禀 min/max、迹单位、实际 L2 及限制的共同尺。内禀正对偶还满足 $\left(C\cap L_S\right)^*_{L_S}=\overline{\operatorname{res}_{L_S}C^*}$，这是有限维双极性的锥恒等式，不是任意联合面效应的同预算延拓。260.5的全部证明可在此域应用，给整个 $F_S$ 为标准 $\mathcal D_4$ 或 $T_1\mathcal D_4$。

（二）以复 Stiefel 空间固定方向。参数取连通的正交二框架空间 $V_2(\mathbb C^b)=U(b)/U(b-2)$；$b=2$ 时为 $U(2)$。令 $D_J$ 为 $\mathbb C^2\otimes\operatorname{ran}J$ 上的标准密度体，两个候选为 $D_J,T_1D_J$，转置始终作用在固定第一因子。候选依框架连续，故在闭 $K$ 中的包含集为闭集；（一）给二者覆盖参数空间。若同一框架同时属于两个包含集，两个候选都在实际边缘支持面 $F_J$ 内，而（一）已把整个 $F_J$ 分类为其中一个，迫使另一个包含在它内。这不可能：在此 $2\times2$ 支持中，Bell 投影 $P_\Omega$ 的部分转置有特征值 $-1/2$，所以 $T_1P_\Omega\notin D_J$；同理 $P_\Omega\notin T_1D_J$。于是闭覆盖不交，连通性给一个全局方向。

（三）若必要暂施全局 $T_1$，所有实际压缩面现为标准 PSD。$2\times b$ 中每个向量的 Schmidt 秩至多二，故都在某个 $\mathbb C^2\otimes S$ 内；秩一时把支持扩为二维即可。因此全部标准秩一态均是原纯点，谱分解给整个标准 PSD 底包含于 $K$。260.5（四）给任意两标准纯点的实际标准二支持球，即使这对点不在同一个压缩面内也成立。260.5（五）的完整 Hermitian 产品零投影张成及一个非零切交点，随后排除每个额外原纯点。有限原纯生成给整个 $C=\operatorname{PSD}_{2b}$，撤销暂时转置即得第二备选。$\square$

**命题 260.7（三条边的奇偶接合、固定坐标传播及反向）。** 在260.1的原维数四背景中，260.4的同一个初始 $\theta$ 已把 $C_1,C_2,C_3$ 同时送到标准 PSD；继而(260.2)对所有有限层成立。反之(260.2)给整个 $K_3$ 的实际 L2 和某把共同圆尺。

证明。先在未改变的 $\theta^{\otimes2}$ 坐标写 $C_2=T_1^\delta\operatorname{PSD}_4$。选 $\beta=T^{\epsilon_1}\otimes T^{\epsilon_2}$、$\epsilon_1\oplus\epsilon_2=\delta$，把此两份锥送到 $\operatorname{PSD}_4$。现在仅为分类 $1|2$，以 $\theta\otimes(\beta\theta^{\otimes2})$ 作三份坐标。260.6取 $b=4$；原两块 min/max、整个 $K_3$ 的 L2 与共同尺恰是其前件，故三份锥为 PSD 或第一块转置的 PSD。也可写为两块转置位 $\eta,\nu$，因两块同时全转置保 PSD。

撤销 $\beta$，回到始终未改的初始 $\theta^{\otimes3}$，得到

$$
C_3=(T^{e_1}\otimes T^{e_2}\otimes T^{e_3})\operatorname{PSD}_8,
\qquad(e_1,e_2,e_3)=(\eta,\epsilon_1\oplus\nu,\epsilon_2\oplus\nu).
\tag{260.21}
$$

这里为简记以同一坐标名 $C_3$ 表示其像。任意一条 $ij$ 边的丢弃像都是整个原 $C_2$：正丢弃给包含，任取原两份正态张量一个归一单态，再用原正置换放到指定位置，给满射。对(260.21)求偏迹，其像按 $e_i\oplus e_j$ 是标准或部分转置 PSD；这两个锥由 Bell 的负特征值区分。因此三条边同时要求

$$
e_1\oplus e_2=e_1\oplus e_3=e_2\oplus e_3=\delta.
\tag{260.22}
$$

三式异或左端为零，右端为 $\delta$，故 $\delta=0$；三个 $e_i$ 全相等，共同全转置保 $\operatorname{PSD}_8$。这证明**同一个初始** $\theta$ 的标准 $C_1,C_2,C_3$，没有在入口假设标准 $C_2$，也没有另外假设局域旋转为原正映射。

精确进入 [F260] 的 XIII命题161.4：这里固定 $n=2$、$\theta:V\to H_2$，低层结论正是其(161.14)，260.1的全部有限背景正是(161.1)—(161.3)，故得到同一个 $\theta$ 的所有有限层。所消费的是分类后尾部，不是161.5的额外几何入口，也不从三边缘本身推断高阶 PSD。

为明确供应范围，161.4调用 [V260] 的 VII102.6—102.10及(102.30)后的两锥包含：102.6在全部原相关输入上以最大界和双极性切片；102.7由标准 $C_2$ 的 Bell 杯帽、蛇式、原最小界与切片得到原全旁观 Choi 判据；102.8取得局域酉及正逆；102.9把两个标准 $C_3$ 资源的乘积放进原 $C_6$，正 Bell 帽收缩给原 $C_4$ 的纠缠门 Choi 元素；102.10用 Harrow [H260] 推论2的**精确有限**普适性，容许不等分组维数。产品纯态沿所得正自同构运输给 PSD $\subseteq C_N$；产品正效应沿正逆运输测试任意向量二次型给 $C_N\subseteq$ PSD。两步都在固定乘积坐标内，含任意原相关输入。不借 S3 或 B1—B3，不用稠密性代替精确生成，也不把资源后选择过程称为确定性物理门。零层仍为给定标量锥。

反向在标准层级取 $g_3(X,Y)=\operatorname{Tr}(XY)$ 于迹零实空间，再由 $\theta^{\otimes3}$ 拉回。两不同纯态的实际面为其复二维支持上的完整 $\mathcal D_2$；中心 $\Pi_S/2$，在此尺下半径 $1/\sqrt2$，因为 $\operatorname{Tr}((P-\Pi_S/2)^2)=1/2$。所以整个 $K_3$ 满足 L2 与 $\mathsf A_2$。本反向只断言存在合适尺，不要求每把正定尺都适用。定理260.2随之成立。$\square$

**推论 260.8（完整静态字典与带前件的过程、时间）。** 在260.1的原维数四背景和260.2任一等价条件下，记 $\Theta_N=\theta^{\otimes N}$、$d_N=2^N$。同一坐标给下表；涉及过程、时间和设备的条目保留各行的额外前件。

| 原对象或额外前件 | 同一坐标中的对应 |
| --- | --- |
| 全部归一原态、原纯点、凸混合 | 全部密度矩阵 $\rho\succeq0,\operatorname{Tr}\rho=1$；全部秩一 $P_v$，纯域 $\mathbb{CP}^{d_N-1}$；原混合为矩阵凸混合，谱分解为正交纯态概率分解 |
| 全部原效应、配对及有限单位分解 | 全部 $0\preceq E\preceq I$；$e_E(x)=\operatorname{Tr}(E\Theta_Nx)$；全部数学 POVM $E_j\succeq0,\sum_jE_j=I$，Born 概率 $p_j=\operatorname{Tr}(E_j\rho)$ |
| 原确认菜单及零邻关系 | $e(P_v)=1$ 恰对应 $E=P_v+B$、$0\preceq B\preceq I-P_v$、$B=(I-P_v)B(I-P_v)$；最小确认者 $P_v$，$T_{p_v}(x)=\operatorname{Tr}(P_v\Theta_Nx)$，零邻点生成实际支持面 $\mathcal D(v^\perp)$ |
| 单份和实际小面几何 | $\rho=(I+r\cdot\sigma)/2$、$\|r\|\le1$；二支持球 $\mathcal D_2$ 的纯壳 $S^2$，外三角 $\mathcal D_3$ 的纯域 $\mathbb{CP}^2$；仿射维数分别三、八，齐次维数四、九 |
| 纯态间的量子几何 | $\operatorname{Tr}(P_vP_w)=|v^*w|^2$；HS 距离平方 $2(1-|v^*w|^2)$；取通常归一约定的 Fubini–Study 距离 $\arccos|v^*w|$ |
| 所有有限复合、原产品、置换、重括号和丢弃 | 标准复 Hilbert 张量积上的整个联合 PSD、原迹配对及偏迹；纯纠缠是 Schmidt 秩大于一，混态可分体是产品密度体的凸包 |
| 实线性 $L:W_a\to W_b$，另要求对每个有限 $M\ge0$ 的整个原锥 $L\otimes\operatorname{id}_{W_M}\ge0$ | $\Phi=\Theta_bL\Theta_a^{-1}$ 的唯一复线性延拓为 CP；等价于 $J(\Phi)\succeq0$ 及有限矩形 Kraus 表示 $\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^*$ |
| 上行再给全正输入的质量约束 $u_bL\le u_a$ 或等号 | 分别为 TNI、TP，即 $\sum_\alpha K_\alpha^*K_\alpha\preceq I$ 或等于 $I$；以未归一 Bell 向量定义 Choi 时等价于 $\operatorname{Tr}_{\rm out}J\preceq I$ 或等于 $I$ |
| 有限分支 $L_j$ 各全旁观正，另给总预算 $u_b\sum_jL_j=u_a$ | 数学仪器：$\rho_j=\Phi_j(\rho)$、$p_j=\operatorname{Tr}\rho_j$；仅 $p_j>0$ 时条件态为 $\rho_j/p_j$。各支 TNI 不替代总和预算 |
| 同层正线性分支另有投影效应 $A$，且在整个 certain-yes 支持的每个纯态逐点中性 | 唯一锐更新 $\Phi(X)=AXA$；仅有锐效应或可重复性不替代该中性前件 |
| 另给连续可逆、保锥保单位的同层实一参数群 | 酉共轭动力学，$\dot\rho=-i[H_{\rm gen},\rho]$；纯态择相位后 $i\dot\psi=H_{\rm gen}\psi$。生成元可加标量；物理钟、能量及 $H_{\rm phys}=\hbar H_{\rm gen}$ 的标定另给 |
| 数学菜单到实际设备，或无限／近似极限 | 事件饱和、记录、接线、可用操作及仪器实现须另给；无限系统须指定连接映射、相容态、拓扑完备化及所需 normal 延拓；近似公理须另有稳定性、范数、误差与资源界 |

证明。260.2给整个原锥和单位，逆对偶给全部原菜单与配对，不经任意面效应延拓。正收缩在 $v$ 的期望为一迫使 $Ev=v$，给确认菜单的分块式；$B=0$ 达到所有输入的 minimum，故原零邻与矩阵正交一致，NC 在这里是结论。支持面、谱分解、Pauli 和射影几何均在已取得的整个矩阵锥中计算，未倒作候选前件。

过程、仪器、锐中性和指定连续群精确复用 [F260] 的 XIII161.6—161.10及其161.7.1。取 $d=2^a,e=2^b$；辅助幂 $2^M$ 可容纳任何给定有限辅助维数，标准嵌入和压缩把全部原旁观正性变成通常 CP，反向由 CP 保全部 PSD 输入。只有单系统正性不能得到 CP。各支及总和分别检查预算；正输出迹为零时输出就是零，不规定归一条件态。相关旁观输入 $Z$ 的分支为 $(\operatorname{id}\otimes\Phi_j)(Z)$，概率仍取整个分支输出的迹。数学正自同构、CP 可容许性和物理设备可实现性是不同陈述，后两者各自保留表中前件。连续群是另给的时间作用，并未从静态圆尺选出 Hamiltonian、实际钟或能量标度。$\square$

**命题 260.9（限定结论的归属与完整白话图景）。** 260.3的低维支撑—带符号饱和—交叉球反演接合、260.5—260.6的实际乘积零面完整重建，以及260.7的三边奇偶接合，是此处的 repo-derived 普通推导。成熟中间工具直接使用，不申领为新定理：有限维极点分解、相对内部与支撑、Lorentz 锥、Grassmann／圆丛、Alexander 对偶及 cap 自然性、Schur 补、Schmidt 分解和标准矩阵支持面。实际面闭性、支撑满射和八维下界精确来自240.2，qutrit 接口来自240.5，任意不同球的张成交集来自 [B260] 的159.5，全有限固定坐标尾部及过程字典来自 [F260]。没有 Lean／kernel 核验或全球优先性主张。

证明与物理图景。把单个两态系统想成一个实心方向球：球内是混合准备，壳上是纯准备。候选先不把联合准备叫作密度矩阵，只要求在**整个三份准备体**里，任意两种纯准备生成的实际面仍是三维圆球，而且所有这种小球可用同一把正定尺测量；这包括任意纠缠准备，而非只检查产品准备。原局部维数四先使单份球就是完整 Bloch 球。一个产品结果读数为零，在两份联合体里给至多十维的实际约束；低维引理通过连续切平面、带方向符号的对偶和两颗交叉球，把其中外三角迫成八维完整 qutrit。

产品读数的正性随后把这个 qutrit 的三个相干方向拼起来；Schur 补留下的只有标准方向或一个因子转置。方向不是假定的物理旋转，而由连通框架空间上的两个闭而不交的候选覆盖固定。每条标准纯射线都进入一个实际 qutrit 面，接着完整产品零投影张成禁止再藏入一个额外纯点。对 $2\times b$，所有条件态受边缘支持控制，使每个二支持压缩是整个实际面，再沿连通二框架把方向接合。最后同一种原 $C_2$ 同时出现在三份的三条边上；三个相对转置位绕三角相加必须为零，所以各边不能都扭转，初始单份坐标便贯穿 $C_1,C_2,C_3$。全部有限最小／最大界与精确161.4尾部才把它传到任意有限复制数。

这在**原局部维数四及完整强全有限背景**中，给候选“整个 $K_3$ 的实际 L2 加一把共同圆尺”与全有限复 qubit 层级的等价，故 TC、TF9、NC 是重建后的性质，不是此限定候选的另加前件。它不把一般原维数的粘合问题判成已解或已反驳，也不声称相对于所有公理系统减少了独立公理数。已发表240与250的更一般维数结论仍按各自前件成立。静态结果给 Born、全部数学 POVM、纠缠和偏迹；所有旁观者下的正性才给 CP，预算才给仪器，逐点中性才给锐更新，另给的连续群才给数学时间演化。设备实现、物理钟、$\hbar$、无限系统及近似误差都保留自己的桥梁，不能由球的形状冒领。$\square$

[B260]: https://github.com/the-omega-institute/trureturing/blob/6a50b8f5bb4f5bf8b46d270a2bca1ccc4a3e3f85/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md "XII引理159.5：只以实际 L2 为前件的任意不同二点球张成交集。"
[A260]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Hatcher, Algebraic Topology：印刷页240—241的 cap-product 自然性；定理3.44（页254—255）及推论3.45（页255—256）的紧局部可缩子集 Alexander 对偶，容许 wild embedding。"
[F260]: https://github.com/the-omega-institute/trureturing/blob/34f5761ee1ccff84afa44f5a906002b13409b7b7/docs/develop/theory/QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md "XIII(161.1)—(161.3)、固定同一theta的(161.14)、命题161.4及161.6—161.10和161.7.1的条件字典。"
[V260]: https://github.com/the-omega-institute/trureturing/blob/f5a6211e591351e1a2bdeea0165c2ef29ad21b48/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "VII102.6—102.10及(102.30)后的两锥包含；只消费分类后全有限尾部。"
[H260]: https://arxiv.org/abs/0806.0631v1 "Harrow, Exact universality from any entangling gate without inverses, Corollary 2：含不等分组维数的精确有限生成，非仅稠密。"

## 追加锚（本行以下为增补区）

## 270. 支撑内三标签、实际矩形与任意原维数的共同圆尺

**定义 270.1（完整强背景中的一个关系条件）。** 本节完整保留250.1：原 $V$ 是任意有限实空间，$\dim_{\mathbb R}V>1$；每个有限 $N\ge0$ 的整个载体为 $W_N=V^{\otimes_{\mathbb R}N}$，有闭尖生成锥 $C_N$、严格正乘积单位 $u_N$、整个紧底 $K_N$、全部原纯点 $P_N$、完整正对偶与效应区间 $[0,u_N]$ 和全部有限单位分解。零层为标量正锥，原乘积配对分离全部联合空间，规范重括号为恒等，全部位置置换及其逆、单位丢弃均正；每个有限分块 $a|b$ 均满足(250.1)的完整最小／最大界，包括任意原相关输入。记 $H_d=\operatorname{Herm}_d(\mathbb C)$；$P_v=vv^*/\|v\|^2$，$\mathcal D(S)$、$\operatorname{PSD}(S)$ 分别为复支持 $S$ 上的整个密度体与正锥。

唯一附加关系条件记为 $\mathsf R_3$：在**整个原 $K_3$** 上，存在一个正定实对称型 $g_3$ 于 $\ker u_3$，使每对不同 $p,q\in P_3$ 的整个最小实际面满足

$$
B_3(p,q)=c_{pq}+\{v\in D_{pq}:g_3(v,v)\le r_{pq}^2\},\qquad
\dim D_{pq}=3,\quad r_{pq}>0,
\tag{270.1}
$$

且 $P_3\cap B_3(p,q)$ 恰为其整个球面。这就是实际 L2 加存在一把共同圆尺 $\mathsf A_2$；量词包括全部纠缠纯点，中心和半径可逐球改变。不另加 TC、TF9、NC、ZP、FI、谱性、正面投影、标准 $C_1,C_2$、共同半径、物理旋转或任意面效应的全局正延拓。几何只在原三物理复制上要求，附加正资源则使用未截断的全有限背景。

本节的普通条件供应为260.2的完整 qubit 层级、260.5—260.6的整个实际 $2\times b$ 分类、240.2与240.5的实际面接口、XIII160.4的 TC 商、XIII161.3中分类后的产品正规形，以及XIII164.11的精确全有限尾部；各供应只按其明示前件使用。260.2的原局部维数四限制保留：它只应用于下面诱导出的四维实际二元支持，不应用于整个未知 $V$。这里扩展的是260以外的任意原维数，不改动260的限定命题，也不把253的 CB、ZP、FI 当作本候选的输入。

**引理 270.2（实际支持、内禀双界与局部 qubit 资源）。** $\mathsf R_3$ 下，原 $K_1,K_2$ 继承实际 L2 和正定共同尺。每个原实际二点面 $B\subset K_1$ 的 $S_B=\operatorname{span}_{\mathbb R}\operatorname{cone}B$ 为四维；令

$$
C_N^B=C_N\cap S_B^{\otimes N},\qquad u_N^B=u_N|_{S_B^{\otimes N}}.
\tag{270.2}
$$

这些整个支持锥组成满足260.1的完整强全有限四维层级，故260.2给其同一局部 qubit 坐标下的全部有限 PSD。更一般地，已经识别的任意两个实际支持块继承其**内禀**最小／最大界；总物理复制数不超过三时也继承原共同尺与 L2。

证明。由最大界及闭锥双极性，对 $z\in C_{a+b}$、$f\in C_a^*$，条件态 $(f\otimes\operatorname{id})z\in C_b$。若 $z\in K_{a+b}$ 的第二边缘为纯 $p$，则每个 $0\le f\le u_a$ 的条件态满足 $0\le(f\otimes\operatorname{id})z\le p$，因而是 $p$ 的非负倍数。完整效应张成 $W_a^*$，产品配对分离，遂有 $z=x\otimes p$。极边缘的逆像是实际面；反向由最小界给出。因此 $K_a\otimes p$ 是整个实际纯旁观面，产品纯点是原纯点。沿这一个面嵌入拉回 $g_3$，依次得到正定 $g_2,g_1$；面内生成面就是原生成面，故 L2 与圆度下降。

对 $z\in C_N$，要求每条单腿边缘位于 $\operatorname{cone}B$。以其余腿的任意 proper 效应条件化，该腿条件态被其边缘支配，故仍在这个面锥。其余腿的正泛函张成完整对偶，遂使 $z$ 在该腿上属于 $S_B$；对各腿重复得 $z\in S_B^{\otimes N}$。反向，载体已在该张量支撑内的正态，其正边缘属于 $C_1\cap S_B=\operatorname{cone}B$。所以(270.2)恰是这些实际边缘面的共同逆像，是整个实际面锥。纯产品实张成载体，故它生成；闭尖性、严格正单位、置换及丢弃全部限制下来。

在任意支持载体 $L$ 上，有限维双极性给

$$
(C\cap L)^*_{L}=\overline{\operatorname{res}_{L}C^*}.
\tag{270.3}
$$

原正简单张量给内禀最小界；对两块内禀正泛函，分别用(270.3)中的原正限制序列逼近，在支持输入上取配对极限，给内禀最大界。这里不要求逼近序列保持同一个 proper 预算，也不声称每个面效应有同预算全局延拓。支持层级的三复制底是原 $K_3$ 的实际面，故继承全部实际二点球和正定限制尺。$B$ 为三球，$\dim S_B=4$，恰好支付260.2的原维数前件。两个不同支持或不等物理块的边缘面用同一条件态支配与对偶闭包论证即可；只有其总复制数不超过三时才调用原几何。$\square$

**引理 270.3（只在已知支持测试的 Bell 压缩）。** 设标签块占 $k$ 个原物理复制，$D$ 是该块中的标准实际面，$E\subset D$ 是复二维支持。假设整个实际 $D\otimes E$ 与 $E\otimes E$ 支持面在相容坐标中标准。对任意 $r$ 复制的旁观块 $R$ 和任意 $Z\in C_{r+k}$，只要标签边缘 $\rho_D$ 支持于 $D$，则标签上的代数压缩

$$
\mathcal Q_E:\ X\longmapsto P_EXP_E
\tag{270.4}
$$

连同恒等旁观者，输出原正态，且质量满足

$$
u_{r+k}(\operatorname{id}_R\otimes\mathcal Q_E)Z
=\operatorname{Tr}(P_E\rho_D)\le\operatorname{Tr}\rho_D=u_{r+k}(Z).
\tag{270.5}
$$

任意支持内 $0\preceq A\preceq I_D$ 的标签单腿读出，也在该支持限制域上给正、迹不增的原旁观输出；所有这些陈述包含任意额外相关原旁观者。

证明。附加 $E_aE_b$ 上的归一 Bell 态 $P_\Omega$，$\Omega=(|00\rangle+|11\rangle)/\sqrt2$；只在已知实际支持 $D E_a$ 上取 Bell 投影 $H=P_\Omega$，在 $D\ominus E$ 块为零。这里 $H$ 是该支持上的 proper 效应，不给它任何环境延拓。

令 $R'=R E_b$ 为**整个保留旁观者**，包括保留 Bell 半边，取任意 $0\le f\le u_{R'}$ 的原效应。全有限原最大界给被收缩块 $D E_a$ 上的条件态 $\sigma_f$，并给原序中的支配

$$
0\le\sigma_f\le (u_{R'}\otimes\operatorname{id}_{D E_a})(Z\otimes P_\Omega)
=\rho_D\otimes I_E/2.
\tag{270.6}
$$

其边缘被支持边缘支配，故引理270.2把它放进**整个**实际 $D\otimes E$ 面；该面已知标准，所以 $0\le\operatorname{Tr}(H\sigma_f)$。对每个正原泛函，先以严格正单位缩放进 proper 区间即可使用此结论。完整 $C_{R'}^*$ 的测试及双极性因此将收缩输出放进原 $C_{r+k}$，不是仅把它放进产品最大锥。

在参考、输出 Bell 同一基的线性张量坐标中，直接收缩矩阵单位给

$$
(\operatorname{id}_{R E_b}\otimes H)(Z\otimes P_\Omega)
=\tfrac14(\operatorname{id}_R\otimes\mathcal Q_E)Z.
\tag{270.7}
$$

未乘四的 Bell 分支质量为 $\tfrac14\operatorname{Tr}(P_E\rho_D)\le u_{r+k}(Z)/4$；其补读出 $I-H$ 同样在支持内为正。乘四只用于锥正性；最终压缩的迹由其原边缘直接计算为(270.5)，故确为 TNI。没有把 Bell 分支乘四后的事件成功率假定为原事件；结论是支持域上代数压缩的正性和单位预算。单腿标签读出则对每个原旁观泛函先取 $D$ 上正条件态，再与 $A,I_D-A$ 配对，分别给输出和补输出的正性。

当 $D$ 取自一个局部 qubit 的两复制支持时，$k=2$，$D\otimes E$ 和 Bell 资源由引理270.2的完整 qubit 层级供应。对一复制目标 $r=1$，几何域为 $r+k=3$，但上述同时附加两标签半边的正资源可暂占 $r+3k=7$ 个物理复制；这只使用全有限正性，未对 $K_7$ 或 $K_4$ 加几何。未来 $r=2,k=1$ 的应用须先取得一复制实际 qutrit 及其 $D\otimes E$ 标准性。$\square$

**引理 270.4（最小平均面、三个标签与九维计数）。** 设目标块占 $r$ 份，标签块占 $k$ 份，$r+k\le3$。设 $D$ 含三个正交标签 $e_i=P_{|i\rangle}$，$i=1,2,3$，并满足引理270.3对每个二维标签支持的资源前件。对任意目标外三角，即不同纯点 $p_1,p_2,p_3$ 并非同处一个实际二点球，令

$$
z_i=p_i\otimes e_i,\qquad F=F_{r+k}(z_1,z_2,z_3),\qquad
\sigma=\tfrac13(z_1+z_2+z_3).
\tag{270.8}
$$

则 $\sigma\in\operatorname{ri}F$，每个 $X\in\operatorname{cone}F$ 被某个 $t\sum_i z_i$ 支配；$F$ 的齐次实维数恰为九，且 $F$ 本身为完整 qutrit 面。

证明。包含 $\sigma$ 的任意实际面，由三个严格正权重必须包含每个 $z_i$；反之含三点的面含平均。因此 $F=F(\sigma)$。有限维点的最小面可显式写成

$$
F(\sigma)=\{y\in K:\ \sigma=\lambda y+(1-\lambda)w
\text{ 对某 }w\in K,\ 0<\lambda<1\}.
\tag{270.9}
$$

右端是含 $\sigma$ 的面：凸性通过减小各自正系数取得共同系数；若其中一点在一条开线段上，代入表示即把两端也收入该集合。取其仿射张成中的有限仿射基点，分别反向延长至仍在 $K$ 的点；这些有限线段的凸包在 $\sigma$ 周围含一个相对邻域。因此 $\sigma\in\operatorname{ri}F$。任意 $y\in F$ 由反向延长得 $\sigma+\varepsilon(\sigma-y)\in F$，于是 $y\le(1+\varepsilon)\sigma/\varepsilon$；齐次化给所述支配。这不是任意大面中平均的相对内部主张。

标签边缘支持在 $\operatorname{span}_{\mathbb C}\{|1\rangle,|2\rangle,|3\rangle\}$，由条件支配，整个 $X$ 的载体在 $W_r\otimes H_3$。对标签 $E_{ij}=\operatorname{span}_{\mathbb C}\{|i\rangle,|j\rangle\}$ 作(270.4)，给

$$
0\le X^{ij}:=(\operatorname{id}\otimes\mathcal Q_{E_{ij}})X
\le t(z_i+z_j),\qquad X^{ij}\in\operatorname{cone}B(z_i,z_j).
\tag{270.10}
$$

后一个结论是实际面的序遗传性。单标签读出同样使 $X_{ii}$ 为 $p_i$ 的非负倍数。每个四维齐次球支撑 $\operatorname{span}B(z_i,z_j)$ 包含两个独立对角方向 $z_i,z_j$；投到其交叉块的像至多二维。因此 $X$ 的三个对角块总共至多三维，每条边的交叉块至多二维，给

$$
\dim_{\mathbb R}\operatorname{span}F\le3+2+2+2=9.
\tag{270.11}
$$

计数先对正 $X$ 作出，再由正锥张成延拓；没有把非正交叉块误称为一个正态。

还需三个 $z_i$ 的实际外部性。$\mathcal D(E_{12})$ 是标准标签 $D$ 的实际面，面传递性使它也是整个原标签底的实际面。标签边缘正映射的该面逆像包含 $z_1,z_2$ 却不含 $z_3$，所以最小实际 $B(z_1,z_2)$ 排除 $z_3$。任何含三点的二点球若含 $B(z_1,z_2)$，因三球严格凸而必须就是它，亦不可能。这个论证只用一个**实际面逆像**，不延拓标签效应。

现在仅把 $F$ 自身视作240.1的原域，单位及完整效应取其内禀值。它是紧实际面，继承所有实际 L2；在其九维齐次载体中任意三点面当然满足全称 TF9。240.2先给这个外三角仿射维数至少八，(270.11)给至多八；240.5遂给整个 $F$ 的保迹序同构

$$
\Phi:H_3\overset\sim\longrightarrow\operatorname{span}F,
\qquad \Phi(\mathcal D_3)=F.
\tag{270.12}
$$

不对环境目标或原 $K_3$ 断言 TF9。$\square$

**引理 270.5（三标签去标的边忠实性与严格正质量）。** 在270.4中，可选择(270.12)使 $\Phi(P_i)=z_i$。取标签 $|+\rangle=(|1\rangle+|2\rangle+|3\rangle)/\sqrt3$ 的支持内读出，定义

$$
h=(\operatorname{id}\otimes\langle+|\,\cdot\,|+\rangle)\Phi:H_3\to W_r,
\qquad T=h^*u_r.
\tag{270.13}
$$

则 $h\ge0$、$h(P_i)=p_i/3$，每个坐标二维支持的像锥恰为整个 $\operatorname{cone}B_r(p_i,p_j)$，限制为线性序同构；并且 $T\succ0$。

证明。标签对角读出在 $F$ 上是内禀 proper 效应 $m_i$，$\sum_i m_i=u_F$。在(270.12)下，三个 $z_j$ 的纯提升 $w_j$ 满足 $w_j^*(\Phi^*m_i)w_j=\delta_{ij}$。正收缩的期望为一或零分别迫使 $(\Phi^*m_i)w_i=w_i$、$(\Phi^*m_i)w_j=0$；自伴性使 $w_i\perp w_j$。它们构成 qutrit 正交基，故可取 $w_i=|i\rangle$。这里先由内禀 POVM 证明正交性，才称其为坐标轴。

$\Phi\mathcal D(E_{ij})=B(z_i,z_j)$。目标实际二元支持 $B_r(p_i,p_j)$ 与标签二元支持 $E_{ij}$ 的整个联合边缘面占至多三物理份；引理270.2给内禀 min/max 和圆度，260.5分类它为标准或单因子部分转置。标准分支中 $z_i,z_j$ 对应 $v_i\otimes|i\rangle,v_j\otimes|j\rangle$，两个目标向量 $v_i,v_j$ 独立。去标把其跨度合同地送到 $v_i/\sqrt3,v_j/\sqrt3$，所以给到整个目标实际二元锥的序同构。部分转置分支可选在标签因子；标签基与 $|+\rangle$ 均实，故其读出相同，结论仍成立。没有假定这些各边的 qubit 坐标已全局同步。

$h\ge0$ 给 $T\succeq0$。对每个完整原 $0\le f\le u_r$，有 $0\preceq h^*f\preceq T$，所以 $\ker T\subseteq\ker(h^*f)$。proper 效应实张成 $W_r^*$，于是对所有 $X\in H_3$，

$$
h(X)=h(P_TXP_T),\qquad P_T=\text{支持 }T\text{ 的正交投影}.
\tag{270.14}
$$

令 $\bar h$ 为 $h$ 在 $\operatorname{Herm}(\operatorname{supp}T)$ 上的限制。边像四维排除 $\operatorname{rank}T\le1$。若 $\operatorname{rank}T=2$，对每个坐标边令 $A_{ij}=P_T|_{E_{ij}}$。若 $\operatorname{rank}A_{ij}\le1$，则 $h(H(E_{ij}))=\bar h(A_{ij}H(E_{ij})A_{ij}^*)$ 至多一维，与边忠实性矛盾。所以 $A_{ij}$ 是二维间的可逆映射，进而

$$
h(\operatorname{PSD}_3)=\bar h(\operatorname{PSD}(\operatorname{supp}T))
=h(\operatorname{PSD}(E_{ij}))=\operatorname{cone}B_r(p_i,p_j).
\tag{270.15}
$$

第三点 $p_k$ 也在左侧，违反目标外三角。故 $\operatorname{rank}T=3$，即 $T\succ0$。$\square$

**命题 270.6（全部纯像、任意直线与目标 TC）。** 270.5的

$$
G(X)=h(T^{-1/2}XT^{-1/2})
\tag{270.16}
$$

为正、迹保持且线性单射；全部源秩一态映为原纯点，任意源复二维支持忠实地满到对应的整个实际二元球。因此目标块满足每个外三角的 TC；不要求 $G(\mathcal D_3)$ 等于目标外三角的整个实际面。

证明。先对 $h$ 证明秩一非零纯像。质量为 $\psi^*T\psi>0$。源向量只有一或两个非零坐标时由270.5的轴与边直接成立；三坐标皆非零时，令 $\chi_{ij}=\psi_i|i\rangle+\psi_j|j\rangle$，令 $q_{ij}$ 为 $h(\chi_{ij}\chi_{ij}^*)$ 的归一化纯像。每个 $q_{ij}\in B_r(p_i,p_j)$，与外部 $p_k$ 不同；由 $\psi=\chi_{ij}+\psi_k|k\rangle$ 得某个有限 $c>0$ 的源序支配

$$
\psi\psi^*\preceq c(\chi_{ij}\chi_{ij}^*+P_k).
\tag{270.17}
$$

所以归一像 $x$ 同时属于三个实际球 $B_r(q_{12},p_3)$、$B_r(q_{13},p_2)$、$B_r(q_{23},p_1)$。若 $x$ 混合，它是每颗严格凸三球的相对内部点；实际面的相对内部相交就意味着面相同。这一颗共同球便含全部 $p_i$，矛盾。于是 $x$ 纯。正定合同置换全部源秩一射线，故 $G$ 也具有全部纯像。

考察任意源二维支持 $S$。若两个纯像 $p,q$ 不同，其源秩一矩阵之和在 $S$ 上严格正，支配 $\operatorname{PSD}(S)$ 中每个元素；正性与实际面性质使 $G\mathcal D(S)\subseteq B_r(p,q)$。在两边标准仿射球坐标中写 $s\mapsto b+As$。整个单位球面的像是原纯点，故

$$
\|b+As\|^2=1\quad(\|s\|=1),\qquad
A^{\mathsf T}b=0,\quad A^{\mathsf T}A=\lambda I_3.
\tag{270.18}
$$

非恒定给 $\lambda>0$、$\operatorname{rank}A=3$，故 $b=0,\lambda=1$；因此此支持是忠实且满的。这里非恒定性先于纯标签单射得到，未循环使用后者。

若某二维支持 $S$ 的全部纯像恒为 $p$，取 $v\notin S$ 且像为 $q\ne p$；存在这种 $q$，因为三个轴经过合同后的像仍包含外三角。对每个 $y\in S$ 的非零向量，源线 $\operatorname{span}_{\mathbb C}\{v,y\}$ 非恒定，故其像都在同一个 $B_r(p,q)$。每个源向量写成 $a v+y$，于是全部纯像都在该球，仍违反外三角。因此没有塌缩线；任意两个不同源纯射线在其共同源线上，纯标签遂全局单射。

若 $0\ne X\in\ker G$，迹保持给 $\operatorname{Tr}X=0$。源矩阵谱分解 $X=X_+-X_-$，两者迹相同且正、支持正交；三维源中至少一侧秩一。该侧的归一像是原纯点，另一侧的谱混合只能由这个同一个纯像组成；纯标签单射与正负支持正交矛盾。因此 $G$ 线性单射。这使用源矩阵谱分解，不预设原目标谱性。

$G$ 中 $p_i$ 的提升射线为 $[T^{1/2}|i\rangle]$，三者独立但一般不正交。对外三角重新记这三条提升为 $[v],[a],[b]$，取 $v$ 单位。任意 $y\in P_r\cap B_r(p_2,p_3)$ 的唯一源提升在 $\operatorname{span}_{\mathbb C}\{a,b\}$，写作 $y'=\alpha a+\beta b$。源线壳在 $P_v$ 的切方向为

$$
\{zv^*+vz^*:z\in\mathbb C(I-P_v)y'\},\qquad
(I-P_v)y'=\alpha(I-P_v)a+\beta(I-P_v)b.
\tag{270.19}
$$

因 $G$ 对每条源线都是到整个实际球的仿射同构，其线性微分把这些方向恰送到实际球切方向。因此 $\tau_{r,p_1}(y)\subseteq\tau_{r,p_1}(p_2)+\tau_{r,p_1}(p_3)$。若无外三角，TC 全称式为空；若存在，则上述证明对每个外三角独立成立。坐标为零、源任意两点像相等的潜在分支、以及非正交提升均已处理。$\square$

**推论 270.7（TC1 与端点重叠的精确范围）。** $\mathsf R_3$ 蕴含整个原 $K_1$ 的 TC。每颗共同尺圆球自身还有对称的内禀重叠：不同纯点 $p,q$ 的实际球记为 $B$，中心 $c_B$、半径 $r_B$，定义

$$
\omega_B(p,q)=\tfrac12\left(1+\frac{g(p-c_B,q-c_B)}{r_B^2}\right).
\tag{270.20}
$$

则 $\omega_B(p,q)=\omega_B(q,p)$，且 $0\le\omega_B\le1$；相等端点的值定义为一。这是同一面内交换端点的 reciprocity，排核前不把它等同于全原菜单的 minimum。

证明。取任一原实际 qubit 支持 $B$；其存在由 $\dim V>1$ 及 L2 给出。270.2在它的两复制标准 $\operatorname{PSD}_4$ 中提供三维标签支持 $D$，其全部 $D\otimes E$ 与 Bell 资源也在这个已知的完整 qubit 层级。令目标 $r=1$、标签 $k=2$，270.3—270.6遂对每个目标外三角支付 TC1；几何始终只用三份。内禀重叠的对称性与界直接来自对称内积和 Cauchy–Schwarz，不涉及任何仪器。

仅有端点 reciprocity 不足以重建：经典全有限层级 $C_N=\mathbb R_+^{d^N}$、乘积求和单位及完整菜单，$d\ge2$，其纯目标 minimum 在纯点间为 Kronecker delta，双向相等；但二点面是线段而非三球。仪器次序也不由 reciprocity 固定：对 qubit 的 $P=P_0,Q=P_+$，Lüders yes 分支满足 $\operatorname{Tr}(PQ)=1/2$，而在输入 $P$ 上 $\operatorname{Tr}(Q(PPP)Q)=1/2$、$\operatorname{Tr}(P(QPQ)P)=1/4$。这是两段不同历史，不能从交换端点推成两个仪器复合可交换。$\square$

**命题 270.8（全局商以前的实际矩形标准性）。** TC1 后精确应用XIII160.4，得到 $n\ge2$ 及同一个实线性满射

$$
\pi:H_n\to V,\quad \pi(\operatorname{PSD}_n)=C_1,\quad u\pi=\operatorname{Tr},
\tag{270.21}
$$

全部复射影纯标签与全部原纯点双射，且每个二维支持限制为到整个实际二元球的序同构。此时不假定 $\pi$ 全局单射，也不引入 $C_2$ 的矩阵商。对任意复二维 $S,T\subset\mathbb C^n$，原 $K_2$ 中两边缘分别在 $\pi\mathcal D(S)$、$\pi\mathcal D(T)$ 的整个实际面，恰为

$$
(\pi\otimes\pi)\mathcal D(S\otimes T).
\tag{270.22}
$$

证明。270.2的条件支配使该面载体恰为 $\pi(H(S))\otimes\pi(H(T))$，十六维；$\pi$ 在每个因子四维支持上单射，故此处张量坐标忠实。它继承内禀 min/max、全部实际 L2 和 $g_2$，260.5给整个面为标准或单因子部分转置 PSD4。

两个候选的定义与局部正交基无关：换基的局部酉可在全 PSD 候选内吸收；在转置候选中用共轭酉吸收。它们随 $(S,T)\in\operatorname{Gr}_2(\mathbb C^n)^2$ 连续。用固定环境转置 $t_n$ 写转置候选时准确为 $(\pi\otimes\pi)(t_n\otimes\operatorname{id})\mathcal D(\bar S\otimes T)$，所以输出仍在同一原 $S,T$ 支持内。两个候选在闭 $K_2$ 中的包含集为闭集，且覆盖这个连通参数空间。若二者同时被包含，整个实际面的二选一分类迫使一者包含另一者；十六维忠实坐标中的 Bell 部分转置负特征值 $-1/2$ 排除它。故闭覆盖不交，一个方向处处固定。

对自支持 $S=T$，诱导实际 qubit 层级由260.2标准。其 qubit 坐标与 $\pi|_{H(S)}$ 相差一个保迹序自同构，即酉或酉后全转置；同一个变换作用两份，保持标准 PSD4。因此自矩形在(270.21)的同一坐标中就是标准，连通性迫使所有矩形标准。此处没有使用全局 $\Gamma_2$、产品 Wigner 正规形或预设标准 $C_2$。$\square$

**命题 270.9（只用有限实际矩形的任意核排除）。** (270.21)必为单射。因此 $\theta=\pi^{-1}$ 在整个原一复制载体上给 $\theta(C_1)=\operatorname{PSD}_n$、$u=\operatorname{Tr}\theta$。

证明。在 $\mathcal W=H_{n^2,0}$ 上直接用**原**张量映射 $\pi\otimes\pi$ 拉回 $g_2$，定义

$$
b(X,Y)=g_2((\pi\otimes\pi)X,(\pi\otimes\pi)Y),\quad
q(X)=b(X,X)\ge0,\quad
\operatorname{rad}b=\{X:b(X,Y)=0\ (Y\in\mathcal W)\}.
\tag{270.23}
$$

若 $0\ne H\in\ker\pi$，则 $\operatorname{Tr}H=0$，且 $H\otimes H_n+H_n\otimes H\subseteq\operatorname{rad}b$。同时在每个**已知标准实际矩形内**的二维支持 $U$ 上，实际面传递性和 $\mathsf A_2(g_2)$ 给 $q(X)=\lambda_U\operatorname{Tr}(X^2)$，$X\in H_0(U)$，$\lambda_U>0$。不同支持的比例不必相等。

取 $H$ 特征基，写 $H=H_+-H_-$、$I_+=\{i:h_i>0\}$、$I_-=\{j:h_j<0\}$，$p=|I_+|,q_-=|I_-|$。换基只是把同一个 $\pi$ 预合成酉合同；270.8对全部支持成立，故保持全部已付实际矩形。令 $b_{\mathbb C}$ 为 $b$ 到 $\mathfrak{sl}_{n^2}(\mathbb C)$ 的复双线性延拓，定义真正非负的半范数

$$
\|Z\|_b^2=b_{\mathbb C}(Z,Z^*)
=q(\operatorname{Re}Z)+q(\operatorname{Im}Z)\ge0,
\quad \operatorname{Re}Z=(Z+Z^*)/2,\quad
\operatorname{Im}Z=(Z-Z^*)/(2i).
\tag{270.24}
$$

这里不把 $b_{\mathbb C}(Z,Z)$ 说成非负。取 $i,k\in I_+$、$j,l\in I_-$，置 $a=(i,k),b_0=(i,l),c_0=(j,k),d=(j,l)$，$E_{xy}=|e_x\rangle\langle e_y|$，并明确取

$$
\begin{aligned}
M_{ij}^{kl}&=b_{\mathbb C}(E_{ab_0},E_{dc_0}),&
N_{kl}^{ij}&=b_{\mathbb C}(E_{ac_0},E_{db_0}),\\
J_{ts}&=|e_a+t e_d\rangle\langle e_{b_0}+s e_{c_0}|\\
&=E_{ab_0}+sE_{ac_0}+tE_{db_0}+stE_{dc_0},&s,t&\in\{1,-1\}.
\end{aligned}
\tag{270.25}
$$

左右向量正交，均有平方范数二；其二维支持 $U_{ts}$ 在实际矩形 $\operatorname{span}\{e_i,e_j\}\otimes\operatorname{span}\{e_k,e_l\}$ 内。故其两根 Hermitian Pauli 方向 $\operatorname{Re}J_{ts},\operatorname{Im}J_{ts}$ 等长且正交，给 $b_{\mathbb C}(J_{ts},J_{ts})=0$。精确消费XVIII(220.22)—(220.24)的有限计算：

$$
\sum_{s,t=\pm1}st\,b_{\mathbb C}(J_{ts},J_{ts})
=8(M_{ij}^{kl}+N_{kl}^{ij})=0.
\tag{270.26}
$$

四次展开仅消去每个支持自身的比例，没有调用(220.19)对所有环境二维支持的前件。令 $w_{ij}=h_i|h_j|>0$。由于 $H\otimes E_{lk}$、$E_{ji}\otimes H$ 在复化根空间，两侧分别允许把配对第二项的 $H_+$ 换为 $H_-$，于是同一有限关系给

$$
\begin{aligned}
\|H_+\otimes E_{kl}\|_b^2&=\sum_{i\in I_+,j\in I_-}w_{ij}M_{ij}^{kl},\\
\|E_{ij}\otimes H_+\|_b^2&=\sum_{k\in I_+,l\in I_-}w_{kl}N_{kl}^{ij},\\
0&=\sum_{k\in I_+,l\in I_-}w_{kl}\|H_+\otimes E_{kl}\|_b^2
 +\sum_{i\in I_+,j\in I_-}w_{ij}\|E_{ij}\otimes H_+\|_b^2.
\end{aligned}
\tag{270.27}
$$

所有配对矩阵均迹零，包括含 $H_+$ 的非对角张量；零谱指标从不进入权重。所有半范数非负、权重严格正，故其每个实部与虚部都在 $\operatorname{rad}b$。这只用至多 $4(pq_-)^2$ 个明确的实际二维支持，未要求 $\ker\pi$ 一维。

特别地对 $k\in I_+,l\in I_-$，令 $S_{kl}=E_{kl}+E_{lk}$，有 $H_+\otimes S_{kl}\in\operatorname{rad}b$。但其原像

$$
(\pi\otimes\pi)(H_+\otimes S_{kl})=\pi(H_+)\otimes\pi(S_{kl})\ne0
\tag{270.28}
$$

是原 $\ker u_2$ 中非零方向：$u\pi(H_+)=\operatorname{Tr}H_+>0$，而 $\pi(S_{kl})\ne0$ 由该二维支持忠实性给出。$g_2$ 正定与根空间结论矛盾。故不存在非零 $H$，$\pi$ 单射。$\square$

**命题 270.10（先得一复制 qutrit，再得 TC2）。** 若270.9给出的 $n=2$，260.2已直接给整个原全有限结论。若 $n\ge3$，整个原 $K_2$ 满足 TC，且不需要四物理复制的几何。

证明。现在才有整个一复制 $C_1$ 的矩阵序同构，可在其中取一个标准实际 qutrit 支持 $D$。任意 $E\subset D$ 的二维支持与 $D$ 的整个实际两块面，由270.2继承 min/max 与两复制几何；260.6以 $b=3$ 分类它为标准或单因子部分转置。其 $E\otimes E$ 子矩形由270.8标准，Bell 负特征值排除转置，故 $D\otimes E$ 在同一一复制坐标中标准。

因而270.3—270.6可取 $r=2,k=1$：目标是未知的整个 $K_2$，标签是一复制 $D$；每条目标实际二元支持与一条标签边总共三份，260.5支付其边读出所需标准／PT二选一。Bell 正性调用已标准的 $D\otimes E$ 及 $E\otimes E$，任意附加资源只用全有限正性。于是每个两复制目标外三角都有 TC2。若原 $V$ 尚未排核，不能预先取这个一复制 $D$；这一步的顺序是实质前件。$\square$

**命题 270.11（全部纯产品提升、秩穷尽与完整 C2）。** 在 $n\ge3$ 分支，TC2 与XIII160.4给

$$
\Pi:H_d\twoheadrightarrow W_2,\qquad
\Pi(\operatorname{PSD}_d)=C_2,\quad u_2\Pi=\operatorname{Tr},
\tag{270.29}
$$

全部源纯标签双射到全部原纯点，每个二维支持忠实地满到实际二元球。实际上 $d=n^2$、$\Pi$ 双射，且原来的同一个 $\theta=\pi^{-1}$ 已满足

$$
\theta^{\otimes2}(C_2)=\operatorname{PSD}_{n^2}.
\tag{270.30}
$$

证明。记 $p_x=\pi(P_x)$。提升产品正交基点 $p_{e_i}\otimes p_{e_j}$ 为单位向量 $v_{ij}\in\mathbb C^d$ 的纯标签。原一复制已完整矩阵化。任意局部 proper $e,f$ 的产品由最大界为正，且 $u_2-e\otimes f=(u-e)\otimes u+e\otimes(u-f)\ge0$，所以产品基效应 $e_i\otimes e_j$ 为原 proper 效应；其 $\Pi$ 拉回是 $0\preceq A_{ij}\preceq I_d$，在相应提升上值一，其余上值零。因而 $A_{ij}v_{ij}=v_{ij}$、$A_{ij}v_{kl}=0$ 对 $(i,j)\ne(k,l)$，自伴性给 $v_{ij}\perp v_{kl}$。置

$$
L=\operatorname{span}_{\mathbb C}\{v_{ij}:0\le i,j<n\},\qquad \dim_{\mathbb C}L=n^2.
\tag{270.31}
$$

证明**全部**纯产品提升在 $L$ 内，无须选相位。固定 $j$，若 $x$ 只有一个基分量，提升已在 $\operatorname{span}_i v_{ij}$；按非零分量个数归纳，写 $x=x'+a e_i$。一复制 $p_x$ 属于实际 $B(p_{x'},p_{e_i})$，纯旁观嵌入把它送到两端产品的整个实际二元面。$\Pi$ 的二维支持忠实性和纯标签双射于是使其提升在两端提升的复线性跨度中。这归纳给全部 $p_x\otimes p_{e_j}$ 的提升在 $L$；固定任意这样的 $x$，对第二因子同样归纳，给全部 $p_x\otimes p_y$ 的提升在 $L$。用的是实际纯旁观二元面，未用乘积相位正规形。

任取两因子的局部正交基，其 $n^2$ 个产品提升都在 $L$，并由对应产品效应的同一 $0/1$ 论证构成 $L$ 的正交基。任意秩一产品效应可纳入这样一个基菜单；其拉回在该基上恰有一个值一、其余为零，正性及补正性迫使它在 $L$ 上就是该一维投影，因而约化 $L$。秩一投影实张成各局部 Hermitian 对偶，全部产品效应遂实张成整个 $W_2^*$，所以每个原泛函的 $\Pi$ 拉回都约化 $L$。

若有 $0\ne w\in L^\perp$，取 $0\ne z\in L$。$[z+w]$、$[z-w]$ 不同，且两者范数相同；所有约化 $L$ 的 Hermitian 算子对其归一秩一投影读数相同。因此所有原泛函都给相同的 $\Pi$ 像，违反全部纯标签单射。故 $L^\perp=0$，$d=n^2$；$\dim W_2=(\dim V)^2=n^4=d^2$ 与满射性遂给 $\Pi$ 双射。

此后才调用XIII161.3中(161.15)之后的**产品正规形供应**，而不调用其更强的三复制几何入口。代入类型 $(n,n;n^2)$，状态产品为 $M=\Pi^{-1}(\pi\otimes\pi)$，效应产品在逆对偶迹坐标中为 $N$。原 min/max 给两者对全部正局部输入的正性；原配对、单位给

$$
\operatorname{Tr}(M(X,Y)N(A,B))=\operatorname{Tr}(XA)\operatorname{Tr}(YB),
\qquad N(I,I)=I.
\tag{270.32}
$$

原张量坐标给单射、分离和全部实空间张成，完整局部／目标矩阵锥及维数均已支付。该条件正规形给一个固定输出酉和两个固定输入转置位；输出酉可吸收进整个目标 PSD，所以在原 $\theta\otimes\theta$ 坐标中

$$
\theta^{\otimes2}C_2=(t_n^{\epsilon_1}\otimes t_n^{\epsilon_2})\operatorname{PSD}_{n^2}.
\tag{270.33}
$$

270.8的标准自 qubit 矩形排除 $\epsilon_1\ne\epsilon_2$；相同两位是恒等或整个矩阵转置，均保 PSD，得(270.30)。这一供应源为161.3所引的 Xu–Zheng–Fošner 产品保持定理及其原配对桥，不把它算作新的分类定理。$\square$

**定理 270.12（任意原维数的完整双向候选）。** 在270.1的强全有限背景，并相对于该定义明列的普通条件供应，有

$$
\mathsf R_3\quad\Longleftrightarrow\quad
\exists n\ge2\ \exists\theta:V\overset\sim\longrightarrow H_n:
\quad \theta^{\otimes N}C_N=\operatorname{PSD}_{n^N},\quad
u_N=\operatorname{Tr}\circ\theta^{\otimes N}\quad(\forall N\ge0).
\tag{270.34}
$$

右侧是同一原局部坐标的整个有限锥，不是逐层另选坐标或仅识别纯产品。无需把整个 $K_3$ 的 TC 另作输入。

证明。270.2—270.9先给一复制完整 PSD。$n=2$ 时引理270.2的整个原空间已为四维，直接用260.2完成。$n\ge3$ 时270.10—270.11给同一个 $\theta$ 的完整 $C_1,C_2$。

现在对原 $2|1$ 切分固定第三腿的一个标准二维支持 $E$，第一块用**整个**已分类 $C_2=\operatorname{PSD}_{n^2}$。该边缘支持面是实际面，载体恰为 $H_{n^2}\otimes H(E)$，有内禀完整 min/max、迹单位、三复制 L2 和共同尺。260.6代入 $b=n^2$（以原正置换交换两块），给整个面为标准 PSD 或 qubit 因子部分转置 PSD。固定第一条数据腿为纯态，第二数据腿和第三腿的 $E\otimes E$ 自矩形由(270.30)标准；转置分支会使该矩形为 PT，Bell 负特征值排除它。因此这个**整个不等块支持面**标准。

取第三腿 $E=\operatorname{span}\{|0\rangle,|1\rangle\}$。同一 $\theta^{\otimes3}$ 坐标中的该面含归一实际 dyad

$$
\frac{\tau_n\tau_n^*}{n+1},\qquad
\tau_n=\sum_{i=0}^{n-1}|ii0\rangle+|011\rangle
=|I_n\rangle\!\rangle|0\rangle+|E_{10}\rangle\!\rangle|1\rangle,
\quad \|\tau_n\|^2=n+1.
\tag{270.35}
$$

这里精确沿用164.2的 $|A\rangle\!\rangle=\sum_i|i\rangle\otimes A|i\rangle$，故 $E_{10}=|1\rangle\langle0|$ 的向量化是 $|01\rangle$；不存在一次额外的转置约定。锥齐次性给未归一 $\tau_n\tau_n^*\in\theta^{\otimes3}C_3$。

精确匹配XIII164.1：其 $V=H_n$ 是现有 $\theta V$，各 $W_N$ 是这个同一原实张量坐标，单位为迹，$C_1,C_2$ 标准；闭尖生成性、严格正单位、完整所有层菜单、全部有限分块 min/max、正置换与正逆及规范重括号，都原样来自270.1而随同一个 $\theta$ 运输。尚未预付任何更高层 PSD、CP 或全局控制。于是(270.35)恰为164.11第3项，直接消费其 $(3\Rightarrow4)$，得全部有限层等式。所用尾部是164.10的六种子／十八腿有限预算、164.9与VII102.10的原全旁观有限字归纳及 [H260] 的精确异维普适性；没有对这些辅助高层锥加几何，也不重证或替换它们的长证明。

反向在标准层级中取 $g_3(x,y)=\operatorname{Tr}(\theta^{\otimes3}x\,\theta^{\otimes3}y)$ 于迹零空间。两不同纯射线生成其复二维支持上的整个 $\mathcal D_2$；中心 $P_S/2$、HS 半径 $1/\sqrt2$，原纯点恰为整个球面，所以满足270.1。只断言存在此尺，不断言给定的任意正定尺都可用。$\square$

**推论 270.13（同一坐标中的完整静态与条件过程字典）。** 在270.12任一等价条件下，记 $\Theta_N=\theta^{\otimes N}$、$D_N=n^N$。以下字典是250.4、260.8及XIII161.6—161.10在参数 $d=n^a,e=n^b$ 下的整锥后应用；操作行各自保留所列前件。

| 原对象或另给前件 | 同一坐标中的完整对应 |
| --- | --- |
| 全部原归一态、纯态、凸混合 | 全部 $\rho\succeq0,\operatorname{Tr}\rho=1$；全部秩一 $P_v$、纯域 $\mathbb {CP}^{D_N-1}$；原混合就是凸混合，矩阵谱分解成为原态的正交纯态分解 |
| 全部原效应、配对、有限单位分解 | 全部 $0\preceq E\preceq I$；$e_E(x)=\operatorname{Tr}(E\Theta_Nx)$；所有有限 POVM $\{E_j\}$，$\sum_jE_j=I$；PVM 为正交投影的单位分解；$p_j=\operatorname{Tr}(E_j\rho)$ |
| 全部纯目标确认者及对任意混输入的 minimum | $E=P_v+B$，$B=(I-P_v)B(I-P_v)$、$0\preceq B\preceq I-P_v$；最小确认效应 $P_v$，$T_{N,p_v}(x)=\operatorname{Tr}(P_v\Theta_Nx)$；零邻面为 $\mathcal D(v^\perp)$ |
| 实际面和纯几何 | 支持面 $\mathcal D(S)$；二支持球与三支持 qutrit；$|v^*w|^2$ 为重叠，HS 距离平方 $2(1-|v^*w|^2)$，通常 Fubini–Study 距离 $\arccos|v^*w|$ |
| 原产品、所有有限联合态、置换、重括号与丢弃 | 标准复 Hilbert 张量积上的整个联合 PSD；迹配对、交换和偏迹；纯纠缠为给定切分的 Schmidt 秩大于一，混态可分体为产品密度体凸包 |
| 实线性 $L:W_a\to W_b$，另要求每个有限 $M\ge0$ 上的整个原输入满足 $L\otimes\operatorname{id}_{W_M}\ge0$ | $\Phi=\Theta_bL\Theta_a^{-1}$ 的唯一复线性延拓为 CP，等价于 $J(\Phi)\succeq0$ 及有限矩形 Kraus 和 $\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^*$ |
| 上行再要求所有正输入上 $u_bL\le u_a$ 或等号 | 分别为 TNI 或 TP，$\sum_\alpha K_\alpha^*K_\alpha\preceq I$ 或 $=I$；这是整输入预算，不是 Choi 总迹预算 |
| 有限分支 $L_j$ 各全旁观正，另有总预算 $u_b\sum_jL_j=u_a$ | 数学仪器；$\rho_j=\Phi_j(\rho)$、$p_j=\operatorname{Tr}\rho_j$，仅 $p_j>0$ 时条件态为 $\rho_j/p_j$；各支 TNI 不能替代总和预算 |
| 同层正分支具有投影效应 $A$，且在整个 certain-yes 支持的每个纯态逐点中性 | 唯一锐更新 $\Phi(X)=AXA$；投影效应或可重复性本身不代付逐点中性 |
| 另给同层连续可逆、保锥保单位实一参数群 | 酉共轭动力学 $\dot\rho=-i[H_{\rm gen},\rho]$，纯态择相位后 $i\dot\psi=H_{\rm gen}\psi$；生成元可加标量 |
| 数学菜单的实际设备实现、物理时间或无限／近似极限 | 事件饱和、记录、接线和仪器实现另给；实际钟、能量及 $H_{\rm phys}=\hbar H_{\rm gen}$ 另标定；无限系统的连接映射、相容态、完备化和 normal 延拓，以及近似稳定性、范数、误差和资源界均须自己的前件 |

证明。整锥和单位的双射，其逆对偶给完整原菜单，故 Born 式是原配对的精确坐标式。正收缩在 $v$ 上期望一迫使 $Ev=v$，给确认者分块；取 $B=0$ 同时达到所有混输入的 minimum，NC 与完整正交零邻在此成为结论。静态条目不使用任意面效应的环境延拓。

过程条目使用XIII161.7、161.7.1、161.9—161.10的整锥后证明，参数恰为 $d=n^a,e=n^b$；$n\ge2$ 的辅助幂可容纳任意有限辅助维数，标准嵌入及压缩给通常 CP，反向由 Kraus 和保全部 PSD 输入。单系统正性不足以支付这个量词。相关旁观输入的分支为 $(\operatorname{id}\otimes\Phi_j)(Z)$，仍以整个输出迹给概率；正输出迹零就为零，不指定其归一态。总仪器预算为 $\sum_{j,\alpha}K_{j,\alpha}^*K_{j,\alpha}=I$。逐点锐中性才调用161.7.1；指定连续群才调用161.10，静态尺不选实际 Hamiltonian 或时间单位。数学正映射、原全旁观正性和设备可实现性保持各自的量词。$\square$

**命题 270.14（普通条件综合的来源、范围与图景）。** 270.3—270.6的支持内三标签拼接，以及270.8—270.12在实际矩形和全有限尾部间的综合，是此处的 repo-derived 普通推导。有限维最小面与相对内部、闭锥双极性、正矩阵零块、Grassmannian 连通性和谱分解是成熟工具。小面分类精确消费[240.2、240.5][F270]及本卷260；TC 到统一商消费[XIII160.4][T270]及其中 [SV160, Theorem 2.4] 的 Hermitian Veronesean cap 分类，未独立宣称新的 cap 分类。四矩形只消费[F270的(220.22)—(220.24)][F270]，其实际拥有卷为XVIII。分类后的产品正规形来自XIII161.3所引用的 [P270]，精确有限传播来自XIII164.11及其原列文献；[H260] 的 Harrow 推论2属于成熟文献工具。这些纸面供应均保留条件含义，本节的结论始终是相对于所列供应的普通条件数学，不申领全球文献优先性或形式化认证。

证明与图景。先在一个真实两态面中取得完整 qubit 资源，把三种目标准备各挂一盏正交标签灯。所有 Bell 测试只照已知实际标签支撑，并对连保留 Bell 半边在内的整个旁观者测试，所以擦掉标签时不会借用不存在的全局正效应。三盏灯的对角块只有三维，三条边各只有两个相干方向，最小面因此只有 qutrit 的九个齐次方向。去标后的一个混合像若同时躲进三颗实际球的内部，会迫使三颗球成为同一个面并吞掉外部第三点；这使全部纯线保持纯且忠实，支付切方向闭合。

矩形随后把未知大空间的核变成一个非零 Pauli 方向的零长度：四个带符号式给系数八，正权半范数和只能逐项为零，而原共同尺不容许非零方向零长。先排一复制核，才取得一复制 qutrit 作两复制目标的标签；再用全部纯产品提升和全部产品效应穷尽整个两复制体。最后只在三份内取得明确相干线 $\tau_n$，把它交给已有的精确全有限传播；共同的原局部坐标遂贯穿所有有限复制。

因此本节将260的原维数四范围扩展到任意有限原维数 $>1$，但始终继承250.1的强全有限背景，并相对于明确列出的普通条件供应。它不以ZP证明TC，不以253的维数选择替代矩形排核，不宣称全局最少公理或无条件物理实现。端点交换只是同一关系的对称；两个有序仪器的状态更新仍有各自前件。$\square$

[F270]: QUANTUM_ORIGIN_HALF_TURN_PREPARATION_AND_GLOBAL_EFFECTS_XVIII.md "XVIII240.1—240.5、250.1与250.4；220.22—220.24的有限四矩形关系。"
[T270]: QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md "XIII160.4的TC商；161.3分类后的产品正规形；164.1、164.10—164.11；161.6—161.10的条件字典。"
[P270]: https://github.com/the-omega-institute/trureturing/blob/f5a6211e591351e1a2bdeea0165c2ef29ad21b48/Library/QuantumStates/barnumhilgert2019spectral.md "Conditional normal-form theorem and proof：Xu–Zheng–Fošner 产品保持供应；此处仅在整层矩阵分类后使用。"

## 追加锚（本行以下为增补区）

# AURIC 区间原响应与移动投影的全域运输

## 1. 同一完整原域、全部原关系与已付接口

**定义 1.1（完整区间模型）。** 记 $I=[0,1]$，固定整数 $n\ge3$，取

$$
M=C(I,M_n(\mathbb C)),\quad E=M_{\rm sa}=C(I,H_n(\mathbb C)),\quad
u(t)=I_n,\quad C=M_+,\quad N(a)=\sup_{t\in I}\|a(t)\|,
\qquad S(a,b)=a\circ b=(ab+ba)/2.
\tag{1.1}
$$

这里是全部连续截面，既非局部常值域，也非稠密真子域。保留同一原 $\Omega/\mathrm{native}$ 的全部原正实线性评价 $\gamma\in\mathcal P$，准确要求

$$
a\in C\iff(\forall\gamma\in\mathcal P)\ \gamma(a)\ge0,
\qquad [\gamma(a)=0\ (\forall\gamma)]\Longrightarrow a=0,
\qquad m_\gamma=\gamma(u)\ge0.
\tag{1.2}
$$

零、不等、次归一及原有非正常评价均不删除。不将数学正泛函或数学向量加入实际准备族。$D:E^2\to E$ 是同一份未知总映射；仅由值域成员资格知道每个固定输出是连续截面，不假定输入连续、可测、分别可加、齐次、协变、中央局部、商下降或任何完成延拓。

**定义 1.2（完整原条件 $\mathsf H_I(D)$）。** 对每个实际 $a,b\in E$、每份原评价以及两种次序，保留 A1/P2 的 Hermitian 二表

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(b\circ a)-i\gamma D(b,a)&\gamma(b^2)
\end{pmatrix}\succeq0.
\tag{1.3}
$$

A2 保留每个实际相加三表 $(a+b,a,b)$ 及全部排列的实部在整个 $\mathbb R^3$ 上半正定，并要求原顺序的 $(1,-1,-1)$ 及对应排列给零平方。A3 保留 $u^2=u$，以及同一个固定有理数 $0<\vartheta\le1$ 上全部 $0\le e\le\vartheta u\Rightarrow e^2\le e$。不把 A2 加强为假定一般复三表正性。

对全部实际 $a,b,d\in E$，只用这份旧 $D$ 生成

$$
v=D(a,b)-a\circ d,\quad w=a\circ b+D(a,d),\qquad
r_\pm=b\pm v,\quad s_\pm=d\pm w.
\tag{1.4}
$$

完整 PB 要求每份原评价满足

$$
\gamma(r_+^2+s_+^2+2D(r_+,s_+))
=\gamma(r_-^2+s_-^2+2D(r_-,s_-)).
\tag{1.5}
$$

零、重复、任意幅度、平移、背景及嵌套输入全部量化；外层始终使用(1.4)实际生成的四份原标签。相同点值不授权替换其中任何一份标签。原评价分离使 PB 也是 $E$ 中的元素等式。

**约定 1.3（固定复用源）。** [平方丛卷][SQ]简称 SQ，[原多项式卷][OP]简称 OP，[原多项式 PB 续卷][PB]简称 PB，[半有限卷][SF]简称 SF，均取链接所指定的固定提交。[原原子续卷已提交12–21][AT]简称 AT，固定为提交 `2addd6f369b7387226c2b0cc984623dd3efe40a1`；其17.3的 $n\ge4$ 任意紧底完整矩阵丛分类是独立作者已提交的纸面成果，按8.2复用，不归为本卷新增内容，也不作为 kernel 核验。另以 [PB 的已提交154–160][FPB]作有限关系边界的比较，绝不将它当作完整 PB 模型。后文引用 SQ47、SF105.1 或 PB153.2 时，纳入的是原条目的完整正文、公式、量词、固定上游身份和逐项合取的上游全文，不用消费者表替换它们。

**约定 1.4（原像接口与共同取向）。** SQ31.1–31.4 在(1.1)–(1.5)上的参数为完整 JB 环境 $X_{\rm JB}=E$、恒等包含、满 Jordan 商 $\pi=\operatorname{ev}_t:E\to H_n(\mathbb C)$。满性可直接由常值截面支付；锥、单位和范数准确。SQ31.2 将原二表传给全部数学正读取，得到反对称性、点上零槽，以及

$$
|\phi D(a,b)|^2\le\phi(a^2)\phi(b^2)-\phi(a\circ b)^2,
\qquad \|D(a,b)\|\le\|a\|\|b\|.
\tag{1.6}
$$

后一个界在每点用单位向量读取，再对自伴输出取算子范数。这只是逐对预算，绝不意味着输入连续。

OP80.2 识别每个二阶角的全部实际代表；OP82.1 统一同一简单块的全部角。OP83.1 则给任意实际 $r,a$ 的小连接行：若在某点 $r(t)=\mu p$，$p$ 是任意秩一正交投影，且 $\|(1-p)a(t)p\|<2$，则

$$
D(r,a)(t)=\sigma_t\frac i2[\mu p,a(t)].
\tag{1.7}
$$

$\mu$ 任意实数，第二输入的对角、补角及全部实际背景任意，全部实际原代表都包括。SQ31.4 用固定实际 Pauli 对的同一连续输出给 $Q:I\to\{\pm1\}$，$Q(t)=\sigma_t$。区间连通，故 $Q=\sigma u$，其中 $\sigma\in\{\pm1\}$ 是常数；不是先假定所有点同号。共同符号及这些原像接口均为复用，不重计为区间分类。

**定义 1.5（取向坐标中的同一旧缺陷）。** 将 $Q$ 视为中央自伴截面，令 $J=iQ$。对 $Z\in M$ 定义

$$
\begin{gathered}
x(Z)=(Z+Z^*)/2,\qquad y(Z)=-J(Z-Z^*)/2,\qquad Z=x(Z)+Jy(Z),\\
K(a,b)=\tfrac J2[a,b],\qquad q_D(Z)=x(Z)^2+y(Z)^2+2D(x(Z),y(Z)),\\
F(Z)=\tfrac12\{q_D(Z)-Z^*Z\}=D(x(Z),y(Z))-K(x(Z),y(Z)).
\end{gathered}
\tag{1.8}
$$

这里 $K,J,q_D$ 是数学辅助对象，不是原全词网络的 $K,\mathsf J,q$。每个固定 $F(Z)\in E$，不假定 $F$ 随输入连续。$J^2=-u$、$J^*=-J$，直接乘法给 $Z^*Z=x^2+y^2+J[x,y]$。

## 2. 移动秩一方向的全部连续相位来自实际 PB

**定理 2.1（全局投影场的有限相位运输）。** 在1.1–1.2的模型及 $\mathsf H_I(D)$ 下，设 $p\in E$ 在每点都是秩一正交投影，$W\in M$，且

$$
c=\|(u-p)Wp\|<4,\qquad d=\|(u-p)W^*p\|.
\tag{2.1}
$$

则对每个实连续函数 $\theta:I\to\mathbb R$，有同一实际全域等式

$$
F(e^{i\theta p}W)=F(W).
\tag{2.2}
$$

每份等式由有限次实际 PB 得到，不对 $D$ 或 $F$ 取输入极限。

证明。取有限 $T>0$ 使 $c+d/\sqrt{1+T^2}<4$。先考虑任意连续实函数 $\tau$ 满足 $\inf_t|\tau(t)|>T$。定义同一原域的实际演员和逆元

$$
r=Q\tau p\in E,\quad Jr=i\tau p,\qquad
A=(u-Jr)^{-1}=(u-p)+\alpha p,\quad \alpha=(1-i\tau)^{-1},
\qquad Z_0=AW=x_0+Jy_0.
\tag{2.3}
$$

投影乘法逐点验证 $A$ 是左右逆；所有函数均连续，且 $x_0,y_0\in E$。不要求 $W$ 可逆。置 $v_0=(u-p)Wp$、$w_0=(u-p)W^*p$，有准确全域分块式

$$
(u-p)x_0p=\tfrac12(v_0+\bar\alpha w_0),\qquad
(u-p)y_0p=-\tfrac J2(v_0-\bar\alpha w_0).
\tag{2.4}
$$

两连接范数均至多 $(c+\|\alpha\|d)/2<2$。每点将(1.7)分别用于同一实际 $(r,x_0)$ 和 $(r,y_0)$，首系数为 $Q(t)\tau(t)$；全部背景仍在 $x_0,y_0$ 中。于是先取得两份全域旧内值

$$
D(r,x_0)=K(r,x_0),\qquad D(r,y_0)=K(r,y_0).
\tag{2.5}
$$

现在才对实际三元组 $(r,x_0,y_0)$ 调用(1.4)–(1.5)。SQ32.2 的同一展开给

$$
v+Jw=JrZ_0,\qquad
(r_\pm+Js_\pm)=(u\pm Jr)Z_0,
\tag{2.6}
$$

其中 $r_\pm,s_\pm$ 正是本调用的实际外层。负端点严格等于

$$
(u-Jr)Z_0=W,
\tag{2.7}
$$

正端点等于 $C_\tau W$，其中

$$
C_\tau=(u+Jr)(u-Jr)^{-1}
=(u-p)+\frac{1+i\tau}{1-i\tau}p
=e^{2i\arctan(\tau)p}.
\tag{2.8}
$$

PB 先给两个 $q_D$ 相等；两份普通 Gram 都为 $Z_0^*(u+r^2)Z_0$，故 $F(C_\tau W)=F(W)$。这也可直接视为 SQ52.1 的全局连续投影类实例。演员中的 $Q$ 保证普通相位的符号是 $+2\arctan\tau$；没有漏掉反向取向。

任意连续实 $\beta$ 作用后 $W'=e^{i\beta p}W$，准确满足

$$
(u-p)W'p=(u-p)Wp,\qquad
(u-p)W'^*p=e^{-i\beta}(u-p)W^*p.
\tag{2.9}
$$

故同一 $c,d,T$ 沿这个方向所有相位保持。令 $\theta_0=2\arctan T<\pi$，选 $\varepsilon>0$ 使 $3\varepsilon/2<\pi-\theta_0$。若 $\|\theta\|_\infty<\varepsilon$，置

$$
\phi_1=\pi-\varepsilon+\theta/2,\qquad
\phi_2=-\pi+\varepsilon+\theta/2.
\tag{2.10}
$$

它们的全部值分别位于 $(\theta_0,\pi)$、$(-\pi,-\theta_0)$；离 $\pm\pi$ 至少 $\varepsilon/2$。因此 $\tau_j=\tan(\phi_j/2)$ 是有限连续函数，紧性给统一有界，且 $\inf|\tau_j|>T$。作两次(2.3)–(2.8)，第二次的前件由(2.9)支付；$\phi_1+\phi_2=\theta$ 给(2.2)。没有在 Cayley 图的端点取无穷参数。

一般连续 $\theta$ 在紧区间有界，取一个有限整数 $N$ 使 $\|\theta/N\|_\infty<\varepsilon$，重复上述两步 $N$ 次即可。每个内部大相位前缀都由(2.9)保留前件，不需要靠近单位。零连接、零相位和 $d=0$ 都包含；$\theta=0$ 的等式亦直接成立。∎

## 3. 完整区间上的全部旧响应

**定理 3.1（不预给输入正则性的区间分类）。** 在定义1.1的完整域、准确原评价及全部原质量下，对任意同域总映射 $D:E^2\to E$，

$$
\boxed{\mathsf H_I(D)\iff
\exists!\sigma\in\{1,-1\}\quad
D(a,b)(t)=\sigma\frac i2[a(t),b(t)]
\quad(a,b\in E,\ t\in I).}
\tag{3.1}
$$

相对于给定旧 $D$ 的常取向唯一；不声称所有可容许响应只有一种。正向不假定任何 $D$ 输入连续性、可加性、齐次性、局部性、协变性或下降。

证明，统一近似及连续标架。下面先在任意固定 $W\in M$ 上给出所需的成熟有限矩阵构造，并写明它们在本证明中的作用。令 $\eta>0$。在复矩阵空间令 $P(B)$ 为行列式与特征多项式判别式之积；其非零恰意味着可逆且谱简单。该复多项式不恒零，例如任一具有不同非零对角元的对角矩阵给非零值。

好矩阵 $P(B)\ne0$ 稠密：对任意 $B$ 固定一个好矩阵 $B_*$，复直线 $B+z(B_*-B)$ 上的多项式在 $z=1$ 非零，故只有有限个零点。可取任意接近零的非零参数避开它们。该论证不要求 $B$ 正规，也不排除原 $B$ 的重根或零特征值。

由 $W$ 一致连续选有限分割，使每个闭小段上 $W$ 相对两端的振幅小于 $\eta/8$；在每个分点选好矩阵 $B_j$，距该点 $W$ 小于 $\eta/8$。直线插值 $L_j(s)=(1-s)B_j+sB_{j+1}$ 与原小段的 $W$ 相差小于 $\eta/4$。复参数多项式 $s\mapsto P(L_j(s))$ 在 $0,1$ 均非零，因而不恒零、零集有限。

在 $[0,1]$ 上每个实零点周围选互不相交的小圆盘，避开端点和全部非实零点；把穿过该圆盘的直径换成上半圆弧。圆盘半径可任意小。由横坐标参数化这些半圆并在其余部分保持参数不动，可得连续 $\lambda_j:[0,1]\to\mathbb C$，端点为 $0,1$，避开全部零点，且 $\sup|\lambda_j(s)-s|$ 任意小。若无实零点，直接取 $\lambda_j(s)=s$。令其足够小，使

$$
\sup_s\|L_j(\lambda_j(s))-L_j(s)\|<\eta/4.
\tag{3.2}
$$

所有小段有限，端点一致拼接后得到连续 $Y$，每点可逆且谱简单，并有 $\|Y-W\|<\eta$。这只是存在性的有限多项式绕行，不作未知响应计算。

简单根的局部隐函数定理可将每点附近的全部特征值连续编号：特征多项式在简单根对根变量的导数非零，作为两实方程的 Jacobian 行列式为该复导数模平方。局部编号覆盖整个紧区间；取有限分割使每个闭小段落在一张编号图内，在相邻接点按唯一相等的根作常置换，就得到全区间连续的互异根 $\lambda_1(t),\ldots,\lambda_n(t)$。区间端点不粘合，不需要绕圈后编号相同。

谱插值幂等元及对应正交投影为

$$
E_1(t)=\prod_{k\ne1}\frac{Y(t)-\lambda_k(t)I}{\lambda_1(t)-\lambda_k(t)},
\qquad
p_0(t)=\frac{E_1(t)E_1(t)^*}{\operatorname{Tr}(E_1(t)E_1(t)^*)}.
\tag{3.3}
$$

$E_1$ 连续、秩一、像为所选特征线；分母严格正。秩一正算子除以迹正是其像的正交投影。因此 $p_0$ 连续且

$$
(u-p_0)Yp_0=0,\qquad \|(u-p_0)Wp_0\|<\eta.
\tag{3.4}
$$

只对近似 $Y$ 选择特征线，不声称原 $W$ 有连续特征线。

还要给一个完整连续酉标架，不能只给一条线。对两个正交投影 $p,q$ 且 $\|p-q\|<1/2$，令

$$
T=qp+(u-q)(u-p),\qquad R=T(T^*T)^{-1/2}.
\tag{3.5}
$$

$T-u=(q-p)(2p-u)$，故 $T$ 可逆；$Tp=qT$ 使 $T^*T$ 与 $p$ 交换。于是 $R$ 酉、$RpR^*=q$，且 $q=p$ 时 $R=u$。正定有限矩阵的逆平方根连续，例如在统一紧正谱区间上用实多项式一致逼近 $s^{-1/2}$ 即得。沿 $p_0(t)$ 取有限细分，使每段内 $\|p_0(t)-p_0(t_j)\|<1/2$。先选普通 $V(0)$ 使 $V(0)P_1V(0)^*=p_0(0)$，$P_1=E_{11}$；每段用(3.5)定义

$$
V(t)=R(p_0(t_j),p_0(t))V(t_j).
\tag{3.6}
$$

接点处 $R=u$，故完整酉矩阵 $V(t)$ 连续，且 $VP_1V^*=p_0$。这没有把数学标架当作实际准备或控制。

证明，每个当前输入的统一有限坐标。固定任意 $Z\in M$ 及任意 $U_0\in\mathcal U(M)=C(I,U(n))$，写 $W=U_0Z$、$R_0=\|W\|$。若 $W=0$，由(1.6)直接有 $F(W)=0$；以下构造也允许 $R_0=0$。在前段取 $\eta<1/4$，得到 $p_0,V$。对任意普通秩一投影 $q$ 令 $p=VqV^*$，则

$$
\|(u-p)Wp\|\le\|(u-p_0)Wp_0\|+2R_0\|q-P_1\|.
\tag{3.7}
$$

选 $\rho>0$ 使 $2R_0\rho<1/2$，零 $R_0$ 时任取正 $\rho$。普通开放投影片 $\|q-P_1\|<\rho$ 实张成 $H_n(\mathbb C)$，准确复用 SQ7.1 或 SQ32.4 的迹零化论证：若 Hermitian $H$ 的迹配对消去该片，实二次多项式 $v^*Hv$ 在非空实开锥为零，极化给 $H=0$。因此可选恰 $d_0=n^2$ 个普通投影 $q_j$ 为实基。令

$$
p_j=Vq_jV^*,\qquad c_j=\|(u-p_j)Wp_j\|<1,
\qquad m=4-\max_jc_j>0.
\tag{3.8}
$$

对这组固定普通投影，仅在普通有限维群上使用实逆函数定理：

$$
\Psi(s)=e^{is_{d_0}q_{d_0}}\cdots e^{is_1q_1},\qquad
\mathrm d\Psi_0(s)=i\sum_js_jq_j.
\tag{3.9}
$$

原点导数是 $\mathbb R^{d_0}\to\mathfrak u(n)$ 的实同构。故有单位的普通群开邻域 $\mathcal V$、连续逆坐标 $f_j$，$f_j(I)=0$。缩小邻域，使所有逆坐标满足

$$
|f_j(A)|<\frac{m}{4d_0(1+R_0)}\qquad(A\in\mathcal V).
\tag{3.10}
$$

这里使用的只是有限维逆函数定理，亦即 SQ7.3、32.4 的同一成熟接口。其局部存在与连续性可由普通矩阵对数坐标中的有限维压缩论证核对：将(3.9)的导数化为恒等，缩小闭球使 $\|Dh-I\|<1/2$；对充分小的目标 $y$，映射 $s\mapsto s-h(s)+y$ 保球且压缩，唯一不动点给逆坐标，两个目标的不动点相差至多目标差的两倍。它不作用于 $D,F$ 或某个未知轨道映射。

若酉截面 $U$ 充分一致接近 $u$，则 $V(t)^*U(t)V(t)$ 在所有点都落入同一个 $\mathcal V$。定义实连续函数

$$
s_j(t)=f_j(V(t)^*U(t)V(t)).
\tag{3.11}
$$

于是得到准确有限因子分解

$$
U=e^{is_{d_0}p_{d_0}}\cdots e^{is_1p_1}.
\tag{3.12}
$$

逆坐标是普通连续函数与已知矩阵条目的复合；没有给非正规输入套单变量谱演算，没有假定未知响应的可测性或输入正则性。

对每个实际前缀定义

$$
H_k=e^{is_kp_k}\cdots e^{is_1p_1},\quad H_0=u,\qquad W_k=H_kW.
$$

投影相位界和有限望远镜展开给

$$
\|H_k-u\|\le\sum_{j\le k}\|s_j\|_\infty
<\frac{m}{4(1+R_0)},\qquad
\|W_k-W\|<m/4.
\tag{3.13}
$$

因此对全部 $j,k$ 都有

$$
\|(u-p_j)W_kp_j\|<c_j+m/4\le4-m+m/4<4.
\tag{3.14}
$$

第 $k$ 步在实际 $W_{k-1}$ 上用定理2.1、方向 $p_k$ 和连续相位 $s_k$；内部所有大 Cayley 相位由(2.9)支付。有限归纳给 $F(UW)=F(W)$。这一步没有要求内部大相位前缀接近单位；(3.13)只控制外部有限小相位前缀。

证明，固定函数的全群不变性。固定 $Z$，令 $G_Z(U)=F(UZ)$。前段对每个当前 $U_0$ 重新选 $p_0,V,q_j$，得到 $U_0$ 的一个左范数邻域上 $G_Z$ 常值。因此同一个 $G_Z$ 在 $C(I,U(n))$ 上处处局部常值。邻域及投影可依赖 $U_0$，被比较的 $Z$ 与函数 $G_Z$ 没有改变。

这个范数群路径连通。任意 $U:I\to U(n)$ 先沿 $U_s(t)=U((1-s)t)$ 从自身连续变形到常值 $U(0)$；$U$ 在紧区间一致连续保证该路径在上确界范数连续。再对单个普通矩阵 $U(0)=S\operatorname{diag}(e^{i\alpha_j})S^*$ 用 $S\operatorname{diag}(e^{i(1-s)\alpha_j})S^*$ 接到单位。这里只选择一个普通矩阵的谱角，没有给酉截面选择全局连续对数。

局部常值函数的每个值纤维开，补集是其余开纤维的并。连通性迫使只有一个非空纤维，值域甚至不需要拓扑。因此

$$
F(UZ)=F(Z)\qquad(Z\in M,\ U\in C(I,U(n))).
\tag{3.15}
$$

未知输出沿路径没有取极限。

证明，压住同一个固定旧输出。现在固定任意 $Z\in M$，写 $R_0=\|Z\|$。对每个 $\eta>0$，前段好矩阵近似构造给可逆 $Y_\eta$、$\|Y_\eta-Z\|<\eta$。仅对这份近似输入取连续极分解

$$
B_\eta=(Y_\eta^*Y_\eta)^{1/2}>0,\qquad
U_\eta=Y_\eta B_\eta^{-1}\in C(I,U(n)).
\tag{3.16}
$$

连续性由正定有限矩阵演算给出；可逆性使 $U_\eta$ 两侧酉。原 $Z$ 可以奇异、秩跳变或没有连续精确酉极分解。令 $Z_\eta'=U_\eta^*Z=x_\eta+Jy_\eta$。由 $\|Z_\eta'-B_\eta\|<\eta$，自伴实部收缩性和 $J$ 酉性给

$$
\|y_\eta\|<\eta,\qquad\|x_\eta\|\le R_0.
\tag{3.17}
$$

对这两个实际原输入用(1.6)，已知 $K$ 也有同一乘积界。再用已经完整支付的(3.15)，得到

$$
\|F(Z)\|=\|F(U_\eta^*Z)\|
=\|D(x_\eta,y_\eta)-K(x_\eta,y_\eta)\|
\le2R_0\eta.
\tag{3.18}
$$

对每个正 $\eta$，左侧都是同一个固定原输出的范数。若它为 $c>0$ 且 $R_0>0$，取 $\eta<c/(2R_0)$ 即矛盾。$R_0=0$ 时 $Z=0$，原零行预算直接给 $F(Z)=0$。故所有 $Z$ 都有 $F(Z)=0$。这是固定值的任意小预算，不是 $D(x_\eta,y_\eta)$ 向 $D$ 的输入极限。

任意实际 $a,b\in E$ 取 $Z=a+Jb$，(1.8)遂给全部旧值 $D(a,b)=\sigma i[a,b]/2$。取常值 $h=E_{11}-E_{22}$、$e=E_{12}+E_{21}$，交换子非零，故给定旧 $D$ 的 $\sigma$ 唯一。

证明，全逆向。对任意常数 $\sigma=\pm1$，$D_\sigma=\sigma i[,]/2$ 的全部三元组及全部质量逆向直接消费 SQ33.2，不重复有限分类。其接线可写为：$J=\sigma i$，$Z=b+Jd$，按这份同一 $D_\sigma$ 生成(1.4)后，准确有 $r_\pm+Js_\pm=(u\pm Ja)Z$；两份 $q_{D_\sigma}$ 都是 $Z^*(u+a^2)Z$。通常或相反 C* 乘法的 Schwarz 给全部 P2；实平方给 A2，谱序给同一有理窗口 A3。演员 $a$ 任意，所有零、重复、缩放、背景、嵌套及原质量均在域内，未仅验证所用投影演员。∎

## 4. 全幅度旧行、截断比较及识别后的代数

**推论 4.1（所有实际代表的无阈值秩一行）。** 在定理3.1前件下，对每个 $t\in I$、任意数学秩一 $p=ee^*$、$\|e\|=1$，以及每对实际原 $r,a\in E$，若

$$
r(t)=\mu p,\qquad a(t)=\beta p+ze^*+ez^*+B,
\quad z\in(1-p)\mathbb C^n,\quad B=(1-p)B(1-p)=B^*,
$$

则

$$
D(r,a)(t)=\mu H(-i\sigma z/2),\qquad H(w)=we^*+ew^*.
\tag{4.1}
$$

$\mu,\beta,B,z$ 全部任意，特别没有 $\|z\|<2$ 或振幅上界。两份实际截面在别处的全部背景原样保留；并非仅对一个新选的点标签成立。

证明。将同一旧 $D$ 的(3.1)代入 $[\mu p,a(t)]$ 即得；$\mu=0$、$z=0$ 时两边均零。这一无幅度限制是全域运输后的结论，不能倒用于定理2.1的两份内行准入。∎

**推论 4.2（受限比较在区间成为结论）。** 在同一前件下，SQ56.1 的 $\mathsf T_D$ 成立；更具体地，对任意实连续 $h$、任意实际 $a,b$ 和任意 $t_0$，若 $h(t_0)=1$，则

$$
D(ha,hb)(t_0)=D(a,b)(t_0).
\tag{4.2}
$$

证明。先由3.1识别全部旧值，再用已知交换子的逐点双线性得到(4.2)。因此任取 SQ55.1 的合适截断都可用。不在证明3.1前假定这条比较，不从区间结论外推任意紧基空间的 SQ56.3。∎

**推论 4.3（同一旧乘法的静态入口）。** 在定理3.1的正向前件下，令 $p_\pm=(u\pm Q)/2$，在同一 $M$ 上置

$$
A\star B=p_+AB+p_-BA.
\tag{4.3}
$$

它是通常或相反 C* 乘法，保持原自伴域、锥、单位、范数和全部原质量，并有 $a\star b=S(a,b)-iD(a,b)$。同一个旧 $D$ 因而实双线性、有界连续、中央双模、中央平移中性，并下降到每点评价；这些都是识别后的结论。对任意有限原 $a_j$、复系数 $z_j$、原评价 $\gamma$，

$$
\sum_{j,k}\bar z_jz_k\{\gamma(S(a_j,a_k))-i\gamma D(a_j,a_k)\}
=\gamma_{\mathbb C}(Y^*\star Y)\ge0,
\qquad Y=\sum_jz_ja_j.
\tag{4.4}
$$

同一乘法还给原实部换括号

$$
(a\circ b)\circ c-D(D(a,b),c)
=a\circ(b\circ c)-D(a,D(b,c)),
\tag{4.5}
$$

以及 Jacobi、Jordan 导子律和保全部质量的忠实含单位保锥等距 Hilbert 表示。原评价的表示向量满足 $\|\xi_\gamma\|^2=m_\gamma$，零质量取零向量。表示像不必等于全 $B(H)$，也不自动正规或具有全局密度矩阵。

证明。逐项直接应用 SQ33.3、48.2 的同一 C* 接口，其输入是刚识别的旧 $S-iD$。正泛函不归一亦可复延拓；GNS 只在正质量分量归一，再乘 $\sqrt{m_\gamma}$，并以全部数学态的直和保证忠实。此表示不替换来源中指定的原全词核。∎

## 5. 不先给复类型的有限简单实 JB 区间丛

**定义 5.1（实 JB 完整区间候选载体）。** 取局部平凡有限维简单含单位实 JB 代数丛 $\mathfrak J\to I$，每点 Jordan 秩为同一个 $n\ge3$。图和过渡是含单位实 Jordan 同构，过渡在有限维算子范数拓扑连续。取全部连续截面 $E=\Gamma(I,\mathfrak J)$、逐点 Jordan 乘法、纤维平方锥、单位截面和上确界 JB 范数。原资料和准确评价完全取 SQ61.1–61.2；全部关系 $\mathsf H_{\rm fin}(D)$ 完全取 SQ61.3，即1.2的相同 A1–A3/P2/PB，平方按 JB 乘法解释。不给复类型、结合乘法、取向或全局标架。

**定理 5.2（实 JB 区间上的同响应分类）。** 对5.1的载体及任意同域旧总映射，合法性等价于：全部纤维为 $H_n(\mathbb C)$ 型，并存在唯一连续乘法取向 $o_D\in\Gamma(I,\mathcal O_{\rm alg}(\mathfrak J))$，使全部旧值 $D=K_{o_D}$。在任一全局含单位 Jordan 平凡化中，$K_{o_D}$ 准确为常符号 $\sigma i[,]/2$ 的拉回。存在合法响应的载体恰为全复型载体；在该载体上两种取向分别给两份相反的合法响应。

证明。SQ62.1 支付完整 JB 环境及每点评价的满性、准确商锥和商范数。将同一 $E$、恒等原域包含和 $\pi=\operatorname{ev}_t$ 代入 SQ62.2，完整原关系强制每个简单纤维保单位、双向保锥且等距地 Jordan 同构于 $H_n(\mathbb C)$。这直接复用已付有限商类型排除，不再证明实、四元数或 Albert 排除，也不先假定局部复类型。

全复型以后明确构造平凡化。取有限开图覆盖，先将每张图的固定局部模型经一个固定含单位 Jordan 同构识别为 $H_n(\mathbb C)$。区间的 Lebesgue 数给有限分割 $0=t_0<\cdots<t_m=1$，使每个闭小段 $[t_{j-1},t_j]$ 包含在一张原图 $O_j$ 中；可令每个接点在相邻两图内。设对应纤维坐标为 $\theta_j(t)$。在第一段取 $\psi_1=\theta_1$。若前段已确定，在接点定义固定的含单位 Jordan 自同构

$$
A_j=\psi_{j-1}(t_{j-1})\,\theta_j(t_{j-1})^{-1},
\qquad \psi_j(t)=A_j\theta_j(t).
\tag{5.1}
$$

相邻两段在接点完全相等。有限闭片拼接使 $\psi(t):\mathfrak J_t\to H_n(\mathbb C)$ 连续；逆映射也逐片连续且在接点一致。每个映射保单位、平方和锥，故由准确序单位范数等距。这给实际全局 Jordan 平凡化，并给满的含单位实线性 Jordan 等距同构

$$
T:E\longrightarrow C(I,H_n(\mathbb C)),\qquad (Ta)(t)=\psi(t)a(t).
\tag{5.2}
$$

满性由任意连续矩阵场经上述连续逆映射拉回得到，不是只给稠密包含。没有使用复自同构群连通、矩阵单位提升或未知 $D$ 的协变性。

把同一旧响应写成坐标

$$
D'(A,B)=T\bigl(D(T^{-1}A,T^{-1}B)\bigr),
\qquad \gamma'=\gamma\circ T^{-1}.
\tag{5.3}
$$

$T$ 的双向线性及 Jordan 性逐个保持原二表、相加三表、同一单位窗口、PB 内值和其四个实际外标签；全部评价、准确锥、范数和每份质量保持。$D'$ 不是延拓或另造响应，而是同一个总映射的双射坐标表达。它的每个固定输出仍连续，不增加任何输入正则性。定理3.1给 $D'=\sigma i[,]/2$，故全部旧值为其准确拉回。

SQ42.1–42.4、63.1 的乘法取向覆盖在 Jordan 换图时按保乘法／反乘法字符换号，故上述公式内在地正是 $D=K_{o_D}$。任一全局平凡化将该双覆盖写成 $I\times\{\pm1\}$；区间连通使其连续截面只有两个。非零二阶锚点给相对于旧 $D$ 的唯一性。逆向对每个取向用 SQ63.2 的全部三元组逆向，或把定理3.1的逆向沿(5.2)拉回，均保持全部原对象和质量。∎

## 6. 完整候选的全文合取与准确等价

**定义 6.1（不缩写来源的谓词）。** 令 $\Gamma_I^{\rm real}(\Omega)$ 表示5.1的明确载体、全部准确原资料和对象同一性。定义

$$
\mathcal C_I(\Omega;S,D)
:=\mathcal C_{47}(\Omega;S,D)
\ \land\ [\mathrm{SF105.1\ 第1\!–\!7项全文及式105.1\!–\!105.7}]
\ \land\ [\mathrm{PB153.2全文}].
\tag{6.1}
$$

方括号表示对所指原正文逐子句、逐公式、逐量词的原强度合取，绝非将标题当作条件。$\mathcal C_{47}$ 严格按 SQ64.1 取 SQ47.1–47.13 的全部定义、合同、公式及纳入的上游全文，包含 SQ47.2–47.3 的全部根、静默和其他静态分支。SF105.1 连同 SF96.1 及所纳入的固定上游全文整体保持；PB153.2 连同 PB147.3、141.3、137.3、122.1 及其逐项上游全文整体保持。各原文已指定的更早版本身份不被当前引文改变。它们重叠的合同同时满足，不重复计算为新独立公理。

具体固定纳入 SF105全文及106.1；OP29.2、78.2、87.1及18.2、24.1、57.1、63.2、70.1；FR139.1–139.2、147.1–147.3、155.1–155.2；XV14.1、20.1–20.3、23.1–23.5；R3 8.1–8.5、80.1；AQ8.3–8.4、14.2、25.1、53.1；W95.2、116.1；SM78.2、86.1、43.2、49.1、61.1、69.1；中央续卷 C145.1–145.7、155.1、160.3、171.1–171.7、181.3、186.1–186.7、194.2、199.2；PB122.1，以及各处逐项纳入的全部原定义、条件、对象、实现、原域、质量和量词。缩写及原版本按 SQ47.1、SF98.1、105.1、PB147.3 的原约定。

唯一原 $\Omega/\mathrm{native}$ 及其中全部对象、准备、事件、程序／过程、参考、副本、真实乘积和真正相关联合保持身份。原共同全词 $K/\mathsf J/q$、原 $J,S,U,D_{\rm network},C,G,M_j,N_j,AS,R_2$ 与全部模式网络不被数学辅助符号替代。parent、ready、合法控制、旗标、记录、环境、钟、单位、原 $\sigma,t_0,d$、全部菜单、固定支持全质量及已量化的每个中间切口原强度保留。每份完整输出的每个仍合法未来，所有成功／失败／拒绝／停止／销毁／泄漏／真遗忘／双向返回都不缩到当前矩阵读数。未定义请求保持未定义。同矩阵、同点像或同概率不合并程序、历史、原 $q$ 零集、读取顺序和未来权限。

该模型只选一个静态对象采用5.1，不把整个 $\Omega$ 都改成固定秩区间丛。全部原中心、经典、不等维、无轴、零活动及静默分支仍按原合同。SQ47.2 的完整根类、全部89配置和235实际逆等距边、十一端点、原 ready 和全 E1、正活动两词备选及零活动支、176有界词表各守自己的原量词；不以静默 ready 的零缺陷代替全 E1。SQ47.3 的有限、完整 II₁、近相加／差分面 $F_3$、一般同平方 JB、固定 $B(\ell^2)$、原理想传播及原词恢复各支保持自身额外前件，不被5.1吞并或宣布未付。七项来源在唯一原世界共同实现，不允许分别另选七份模型。

**定义 6.2（完整区间候选）。** 本候选为

$$
\Gamma_I^{\rm real}(\Omega)+\mathsf H_{\rm fin}(D)+\mathcal C_I(\Omega;S,D).
\tag{6.2}
$$

它没有稠密开闭局部点前件，没有额外的 $\mathsf T_D$，也不预给复类型。它保留完整截面域、有限简单固定秩、局部平凡和准确原评价等明确前提，不作整体严格更弱或全局公理更少的比较。

**定理 6.3（完整候选与同响应重构）。** 固定 $\Gamma_I^{\rm real}(\Omega)$，(6.2)准确等价于

$$
[\mathfrak J_t\cong_JH_n(\mathbb C)\ (\forall t\in I)]
+\exists!o\in\Gamma(I,\mathcal O_{\rm alg}(\mathfrak J)),\qquad
D=K_o\ \land\ \mathcal C_I(\Omega;S,K_o).
\tag{6.3}
$$

条件齐备时，SQ48.3 的全部七项量子消费者在同一实际对象、全量词、质量、表示和定义域内成立。

证明。正向由5.2，来源约束同一旧 $D$。逆向用5.2的全部三元组及全部质量逆向，来源仍约束同一个 $K_o$。5.2不需 SQ48.1 的稠密前件，而4.3的证明完整支付 SQ48.2 所需的同一 C* 乘法、全有限复 Gram、原换括号及保质量表示；因此 SQ48.3 的七路证明逐项具有相同的静态入口。下一章展开实际来源和结论；(6.1)所指全文始终与展开共同合取，不被展开取代。∎

## 7. 同一世界的七路条件结论与完整来源边界

**合同 7.1（复 Hilbert、可观察量与实际相干叠加）。** 本项完整采用 SF105.1第1项、SQ47.4及其全部上游。4.3给同一旧 $S-iD$ 的数学表示和全部有限 Gram；具名且可取得的原标签、native、指定跨评价配对、全部原程序各自的词身份、parent／ready、合法控制和实际相干准备仍须来源实际供应。原门序列及 $\sigma,t_0$ 不换身份。

在共同全词网络的接口，仍取同一个复空间 $V_{\rm nat}$、第一槽共轭线性的半正定 Hermitian 型 $K_{\rm nat}$、全部原 $\xi_\gamma$ 及原总集合映射 $\mathsf J_a:V_{\rm nat}\to V_{\rm nat}$；对全部原 $a,b\in E$、$\gamma\in\mathcal P$、$z,w\in V_{\rm nat}$ 和正标签 $c\in C$，保持准确等式及不等式

$$
\begin{aligned}
K_{\rm nat}(\xi_\gamma,\mathsf J_a\xi_\gamma)&=\gamma(a),\\
K_{\rm nat}(\mathsf J_a z,\mathsf J_b w)
&=K_{\rm nat}(z,\mathsf J_{a\circ b}w)
-iK_{\rm nat}(z,\mathsf J_{D(a,b)}w),\\
V_{\rm nat}&=\operatorname{span}_{\mathbb C}
\{\mathsf J_{a_1}\cdots\mathsf J_{a_k}\xi_\gamma:
 k\ge0,\ a_j\in E,\ \gamma\in\mathcal P\},\\
K_{\rm nat}(\xi_\gamma,\xi_\gamma)&\le m_\gamma,\\
K_{\rm nat}(\mathsf J_a\xi_\gamma,
 \mathsf J_c(\mathsf J_a\xi_\gamma))&\ge0.
\end{aligned}
\tag{7.1}
$$

原总映射必须先实际复合，再取有限复线性包，空词及任意有限词长均包括。不能以逐评价独立 GNS 核替换这个共同核；不预给 $\mathsf J_a$ 线性、$\mathsf J_0=0$ 或 $\mathsf J_u=I$。在这些原消费者前件下沿原可见恢复取得共同复 Hilbert 叠加和可观察量。数学表示不制造任意向量准备、全 $B(H)$ 可取得像、实际采用该表示、复制或相干控制。

**合同 7.2（态、效果、Born、全菜单与全质量）。** 完整采用 SF105.1第2项、SQ47.6和全部上游。原评价、原事件、准确效果区间 $[0,u]$、每个实际完整菜单及接受归属保持同源。全部准备、共同根、实际抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定处处有限强度、P9每个分支及各自独立 $W_e$、全部原目标、每个原 $(\xi,g,s)$ 的菜单覆盖、固定支持全质量和每个已量化中间切口完整保持。互探的有限维／最小可见／实尺度范围、其他块自己的 AS/EC、菜单外 OB、忠实二维到三维全质量适配器及非零一维块照原要求支付；原强度、原 $q$、中央权与概率质量不混同。

原有限端口、角／二十七模适配器、完整坐标分区和每条实际平衡行均保持，读取按先原 $g^*$、再原 $d_s^*$、最后同一共同根的原顺序；同矩阵的不同程序分别支付。两只独立九叶彩票 $(6,2,0)/9$、$(4,4,0)/9$、各自第九空程序、十六拒绝叶和相干 $I_3/3$ 返回保留原类型和细记录，不把相干返回细测成经典三结果。

同一个实际完整有限菜单在原事件已绑定、$\sum_je_j=u$ 且 $m_\gamma>0$ 时才给

$$
p_\gamma(j)=\gamma(e_j)/m_\gamma,\qquad \sum_jp_\gamma(j)=1.
\tag{7.2}
$$

条件角菜单另须原 $\sum_je_j=p$、原条件化身份及 $\gamma(p)>0$，才除以 $\gamma(p)$。全部零、不等、次归一质量、中心经典权、不等维和静默块保留未归一读数；零质量不除法、不删分支，更新还须正输出质量。一般态保持原正泛函或已付前对偶身份；只有原合格有限全矩阵物理表示及过程绑定，或相应正常物理表示、指定前对偶和收敛齐备时，才写 $\gamma(e)=\operatorname{Tr}(\rho_\gamma E_e)$、$\rho_\gamma\ge0$、$\operatorname{Tr}\rho_\gamma=m_\gamma$。一般中心、正规子代数、GNS和正延拓不自动供应这份密度式、正常性、准备或菜单。

**合同 7.3（native、真正相关联合与张量）。** 完整采用 SF105.1第3项、SQ47.7及全部上游。原全词共同 $K/\mathsf J$、交叉零、旧局部乘法、每个实际非零相关联合、中央对、经典和不等维块、真实乘积、全部真正相关输入、实际复制及每层递归同源参考均保留。每个被消费的局部全矩阵腿必须在同一实际共同实现内忠实、同向、交换，并满足联合共同生成、原评价分离和所需重数条件。

只有这些条件共同齐备，才识别该原有序联合为 $M_d\otimes M_r$；具体 Hilbert 载体的重数一或不可约性另由原重数条件承担。一般中心对每个实际非零中央对分别保留共同支持、生成、分离与全部相关输入。分别可达、相同边缘、同符号、辅助共同表示、两个角或数学张量域都不产生实际联合，type II腿也不直接满足要求局部全矩阵的消费者。

**合同 7.4（typed CP、Kraus与整台递归参考）。** 完整采用 SF105.1第4项、SQ47.8及其全部上游。对每条实际细分支 $r:A_0\to B_0$、全部合法 typed 前接／后接、每份完整输出的每个仍合法未来及每份原评价，保留

$$
\gamma_{A_0}(\beta_r b)=\gamma_{B_0}^{\,r}(b),
\tag{7.3}
$$

以及反变合法复合、typed分区、全未来自然性、全质量运输和原箭头商下降。由这些原条件先取得正次单位回溯；CP另由完整全槽同标签单位区间过程比较，或由整台实际箭头可再应用的递归同源参考规则取得。系统、整个环境、全部成功／失败／细记录／输入输出port／post-port及每份完整输出每个合法未来，都在同一可再应用规则类；真正遗忘、真实返回和合法复合箭头也须在类内。形式 CP 不反造这些原箭头。

递归路线两端各有共同真支持和忠实同向交换系统腿、参考腿。$A$端保持

$$
i_A:\mathcal A_A\hookrightarrow p_A\mathcal A_{A^+}p_A,
\quad j_A:M_2\hookrightarrow p_A\mathcal A_{A^+}p_A,
\quad i_A(1)=j_A(I_2)=p_A,
\tag{7.4}
$$

$B$端同型。三个实际参考投影 $q_1,q_2,q_3$ 与 $I_2$ 实张成 $(M_2)_{\rm sa}$。每次接线在全部原相关正输入、决定锥的全部原联合评价上保持

$$
\beta_{r^+}i_B=i_A\beta_r,\qquad
0\le\beta_{r^+}(j_B(q))\le j_A(q)
\quad(q\in\{q_j,I_2-q_j:1\le j\le3\}).
\tag{7.5}
$$

补是在共同支持内取 $p-j(q)$，不换成环境单位补；两腿不必生成整个环境或支持角。下一层系统是整台实际 $r^+$ 的全部响应和未来，不仅是根代码。对每条根箭头和每个所需有限 $L$ 都有实际长 $L$ 链，对每个 $k\le L$ 保持忠实累计嵌入与精确支持运输

$$
M_A^k:\mathcal A_{A_0}\otimes M_{2^k}\hookrightarrow\mathcal A_{A_k},
\qquad \beta_kM_B^k=M_A^k(\beta_0\otimes\operatorname{id}_{2^k}),
\qquad P_A^{k+1}=i_{A,k}(P_A^k)\le p_{A,k+1}.
\tag{7.6}
$$

累计真支持不变为新环境单位。任意精度路线量化每个正精度、每个有限深度、全部真支持／事件／相关输入／后口及精确根身份；固定正误差不足。有限长度全称不要求一条物理无限链、免费旁接函子或物理无限张量积；形式参考和根代码扩充不支付完整实际链。已付九号读口及其实际参考、联合和有限返回刚性按原前件复用，不重新列为缺失；返回复合 CP 不推出因子或任意箭头 CP。

Kraus式只在准确合格有限全矩阵域，或另付适用正规物理表示、指定前对偶、分解及收敛的域使用，例如在有限矩阵消费者处 $\beta_r(b)=\sum_\alpha V_{r\alpha}^*bV_{r\alpha}$。一般正规子代数的正常 CP 对偶不自动给全 $B(H)$ 算子 Kraus 表示、可数和或原记录指标。数学扩充、投影、酉元和3.15不生产过程或实际参考。

**合同 7.5（整台仪器、TP、更新与 Lüders）。** 完整采用 SF105.1第5项、SQ47.11及其全部上游。每台原仪器的全部输入运输、完整 typed 菜单、原接受端、整个环境、全部成功／失败／细记录／port／post-port及每份完整输出的每个合法未来保持。真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根可执行词与每份词自己的接受条件均保留；数学平方根不是原词。

同一乘法的正夹心 $a\star c\star a=2a\circ(a\circ c)-a^2\circ c$ 只给静态入口。逐支 CP 及正次单位只给 TNI；整台实际测试的完整 typed 单位分区

$$
\sum_r\beta_r(u_{B_r})=u_{A_0}
\tag{7.7}
$$

才给 TP。不同输出类型不免费识别为物理直和。条件更新的实际输出评价为 $\gamma_B^r(b)=\gamma_A(\beta_rb)$，只有 $\gamma_A(\beta_ru_B)>0$ 才归一为两者之比；零和失败支连同原类型、记录和全部未来保留。细输出相加还须原真正粗事件及实际分组接头。

Lüders另须同一完整输出的投影效果、像内每条射线保持及完整输出校准；同效果、同概率、统计重复性或仅支撑保持不足。在合格矩阵过程域才得到对应的 $\rho\mapsto p\rho p/\operatorname{Tr}(\rho p)$，分母须正；一般平方根效应的更新仍守原可执行词及接受条件。密度、迹类、Kraus和迹公式保持7.4的表示、前对偶和收敛边界；数学迹不抹掉细记录、port未来或接受归属。

**合同 7.6（全历史、全未来、真遗忘、返回与 CountRead）。** 完整采用 SF105.1第6项、SQ47.12及全部上游。所有合法顺序、自适应、并行历史，整个环境、参考副本、全部细记录和泄漏、停止、拒绝、销毁、真正分组遗忘、同数两侧真实返回及同数逆向真实返回，连同每份完整输出的每个仍合法未来，全部保持原类型。可加只沿真正粗事件的实际分组；丢弃档案不等于真遗忘。同数学算子不合并原程序、读取顺序、原 $q$ 零集及 AC方向。

CountRead仍要求读后同一原完整活动输入和它全部合法未来的实际 Return。活动ready接头、接受叶活动输出、第一合法消费者、具名分析词到原实际完整菜单和接受端的接线均须原生供应；读后终端、查询、分母、细地址和失败类型不变成旧 ready。负提升两条活路的分别受控实现与相干聚合实现分别实际取得，数学负号或数值相消不制造活路、不返回完整输出。原精确正生成 $B$ 与另名闭正生成 $B_{\rm cl}$ 不混同；两只独立九叶彩票、各自第九空程序、十六拒绝叶及相干 $I_3/3$ 返回保持原记录与类型。

初始取得、指定有限树、被动精确混合解码、已供应CountRead精确表的支持事件及整支质量、已供应有限返回的数值校准，只在原平稳、真实同源、同初始版本及各自实际域内消费。这些已成结果不重列为缺口；它们不代付整份后续输出的全未来 Return或完整接线。返回在表示层恒等也须全输出／全未来忠实绑定及原档案分离条件。

无限历史、无限或非离散记录、可数可加、物理正常性、指定前对偶及所需收敛仍取原扩展来源。若完整CountRead已强迫无限维忠实响应商，不把它截为一个有限角。有限 PB、数学连续投影、近似和固定范数预算不生产物理无限记录或读后双向返回。所有未定义请求仍未定义，静默和零质量对象的合法未来不删。

**合同 7.7（动力、钟、能量、定义域与共同正作用量）。** 完整采用 SF105.1第7项、SQ47.13及全部上游。同一旧全域乘法、保持可能不完备原域的流、实际门与相位及实际逆、同一实际过程内连续可逆 CPTP 一参数群、物理钟和单位、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、共同仪器、共同作用量和同一个正 $\hbar$ 全部保留。原 $\sigma,t_0,d$、固定域、resolvent与 $3s+r\le1$ 属原设备、参数、定义域和量纲，不与区间坐标、取向符号、IFT参数或有限分割步数混同。

这些前件共同齐备后，才在原合格物理表示和生成元域消费

$$
U(t)=e_\star^{-itH/\hbar},\qquad
i\hbar\frac{d\psi}{dt}=H\psi,\qquad
i\hbar\dot\rho=[H,\rho]_\star,\qquad
\dot b=\frac2\hbar D(H,b).
\tag{7.8}
$$

向量微分限于自伴生成元定义域，密度微分限于相应迹类可微域，Heisenberg响应限于实际可微观测量域；括号、指数和表示均用同一已识别乘法，相反取向不暗换普通乘法。数学有界内导子、范数群路径、谱、辅助随机钟或形式 CP不生产物理时间、可控相位、控制成本、一般无界生成元域、能量意义或跨装置共同尺度。

**约定 7.8（七路共同实现与一般原域边界）。** 上述七路是同一原世界的共同条件，不是七次分别换来源的存在命题。PB153.2保留的一般目标仍是在原146的同一检测器 $\ell$ 及全部实际正分量质量下，从完整原P2/PB控制同一个 $T(q)-2(a+u)\circ H=2\delta$，得到目标相关联合预算或实际运输；不预给一般旧 $D$ 线性、连续、协变、符号表示或原谱标签。当前区间模型的3.1没有解决任意不完备、无原子、不可分原域的这个任务，也不将PB151所排除的一类着色总表升级为一般反模型。完整量子起源还须实际同时供应各路原前件。

## 8. 几何范围、复用归属与完整中文解释

**命题 8.1（区间确实不属于旧稠密局部开闭范围）。** $L(I)=\varnothing$，但定义1.1下3.1仍成立。3.1或5.2的区间证明不推出圆周或任意紧基分类；在 AT12.2 的完整局部平凡复矩阵丛及准确原条件下，$n\ge4$ 的任意紧 Hausdorff 基分类已由 AT17.3 支付，含圆周在内。一般紧基的完整三阶分类仍未解决；一般 JB、type III、非局部平凡、变秩和不完整原域也不由3.1或5.2得到全域分类。

证明。连通区间的非空开闭集只有自身；任一点都可选一个不含整个区间的相对开邻域，其中没有包含该点的开闭邻域，故 $L(I)$ 为空。3.1使用全局连续近似特征线和可缩区间的群路径，没有调用 $L$ 稠密。对圆周，同一简单谱路径绕圈后可能置换特征线；SQ54.3还给平凡矩阵丛中的输入，排除全部阈值合格的非零首步，包括连续投影场。其标准 $D=K$ 仍合法，所以这是该运输方法的障碍，不是完整 PB 的反模型。区间的分段编号及收缩路径不支付绕圈端点相容，不能推出一般紧基分类。5.2另外使用局部平凡、简单固定有限秩及完整截面域；删去这些条件没有上述满同构和实际端点保证。∎

$n=2$ 的任意紧基及完整／合格稠密秩三自旋域直接复用 OP102–108，不作为新增区间结果。$n=1$ 时每点标量二表的行列式预算为零，故旧 $D=0$；两种符号定义同一个零响应，不能保留唯一二点取向的说法。3.1中的原输入可为零、重根、任意秩亏、秩跳变、任意幅度和背景；好矩阵只用于已知矩阵构造，未删这些原输入。零质量不归一，方向一侧为空也不造成遗漏。

**约定 8.2（新内容与成熟工具的准确分界）。** 本卷新填补的分类缺口是 $n=3$ 的完整区间域：不预给输入正则性、稠密 $L$ 或截断比较，由全部原 A1–A3/P2/PB 识别同一个旧 $D$。2.1的连续相位接线及3.1的区间证明支付这一三阶结论，进而给三阶4.1的全幅度原像行和5.2的实 JB 区间应用。3.1、5.2的统一 $n\ge3$ 陈述及证明保留；其中 $n\ge4$ 分类与 AT17.3 重叠，实 JB 形式在已付复类型及相容代数取向后接回同一结果，不计为本卷新增高阶分类。

AT12.2、17.3–17.4 已在任意非空紧 Hausdorff 基、完整局部平凡复 $M_n(\mathbb C)$ 丛、准确原评价及全部原关系下，对 $n\ge4$ 识别全部旧值 $D=iQ[,]/2$，其中 $Q$ 是由同一旧 $D$ 确定的唯一连续中央符号。它不要求稠密局部开闭点或额外截断比较；AT17.4并使 SQ56.1 的相应接头成为结论，故高阶任意紧底的这份比较不再列为缺口。AT15.1的共同左右零方向及18.1的 reducing 秩一线识别也适用于 $n=3$；AT21.2仍留下完整三阶一般目标。本卷仅在区间补上这个三阶分类，不把它外推到一般紧基，也不重写 AT 的定理或证明。

SQ31的准确环境、全部数学正读取和共同取向，OP80.2／82.1／83.1的原像识别，SQ32.2和52.1的实际负端点，SQ7.3／32.4的普通有限维坐标接口，SQ8.2的固定输出预算机制，以及SQ33.2、63.2的完整逆向全部复用。有限原矩阵分类、有限中心／II₁及 $M_3$ 结果不重证、不改判；SQ55–56的截断比较在一般三阶紧基、非完整原域或一般 JB 域仍保留原边界，4.2在本区间模型把它变成结论。

多项式稠密与有限复绕行、简单根局部编号、近投影极分解、开放投影片张成、有限维实逆函数定理、矩阵极分解及正定演算是成熟工具，均在3.1的承重证明内给出所需构造及参数对应，不另立为新一般定理。JB类型强迫只消费SQ62.2及其固定的配平续卷240–247；成熟JB文献的来源身份为 Hanche-Olsen–Størmer《Jordan Operator Algebras》，作者提供的[原书入口][HOS]及SQ62.1–62.2所引条目。它不替本证明支付未知响应的输入正则性。本文结果归为 $\texttt{repo-derived}$ 的纸面综合，不作历史优先权、全球新颖性或穷尽文献搜索主张。

已提交 PB154–160 的有限 $H_4$ 总响应保持A1–A3、全部P2、全部秩一行、全部实二配对换基协变、十六次指定PB和全部标量演员，却被另一条实际PB排除。它的准确作用是有限关系不蕴含所选迹相容；不是完整PB反模型、全分类或区间定理。本卷不采用其迹相容作为额外公理，也不将该构造归为本卷成果。

**定义 8.3（普通几何读法）。** 把整份区间输入想成沿一条线段连续摆放的矩阵。每个矩阵各自有一条特征线，不代表这些线能直接连续挑选；原矩阵可以重根或秩跳变。这里先把整条矩阵路径轻微挪开有限代数坏点，只给近似路径挑线。线段没有绕回接头，局部编号可逐段对齐；近投影的明确酉搬运再把一条线补成整套连续标架。搬运保留的是原矩阵与所选线之间很小的连接，绝不是把原输入换成近似输入后取旧答案。

有了这条近似不变线，原配平关系才能真正开始作用。演员的幅度在全区间统一取大，只压小反向连接；正向连接的小预算由那条线提供。两个实际内值分别通过原二表及已有小行结论，才允许调用原三对象配平。逆元让负端逐字回到当前那份输入，所以运走的始终是同一旧缺陷。两次接近相反半圈的有限动作相加成任意小相位，有限重复得到任意连续相位；没有把无穷大演员或稠密角度极限当作合法步骤。

一条线附近可以挑出足够多的方向，它们在普通有限矩阵空间里张成全部自伴方向。同一标架把它们连续带到区间各点。普通有限维坐标把任何足够小的整份酉旋转准确写成有限个这种方向的相位；每个小相位前缀都有统一余量，内部大动作的前缀又有各自不变的连接预算。换到任意当前旋转后都能重做这一构造，于是固定缺陷在整个酉截面群中处处局部不变。整张旋转表可沿区间收缩到一张常表，再把这一个普通矩阵转回单位，因此所有旋转都保持同一缺陷。这只用未知函数的局部常值，不假定它连续。

最后再选一份可逆近似，仅借它的极分解制造旋转。旋转后的原输入接近一个正矩阵，故其实际虚部任意小。二表把对应旧缺陷的范数压到任意小，而精确运输已把这个范数认作原先固定那一个。因此固定缺陷只能为零。近似过程中旧答案可以没有任何输入连续性；论证从未要求一串不同答案趋于某个答案。

实JB丛的情形先用已付类型定理说明纤维必须是复矩阵自伴部，再沿线段把相邻Jordan图在接点准确对齐。整套坐标变换是原域上的双射，旧响应跟着同一双射换坐标，不是向大空间延拓或换一张标准响应表。由此任意幅度、任意背景和全部原代表的旧答案都被同一个常左右手锁定。这个左右手是乘法方向，不是物理空间维数，也不生产一项可执行控制。

就分类缺口而言，这条线段论证新补的是三阶：四阶及以上的完整局部平凡复矩阵丛，独立作者的已提交 AT17.3 已在任意紧 Hausdorff 基上认回同一旧表，并去掉额外截断比较；本卷的统一高阶结论与之重叠。一般紧基的三阶全表仍未解决，共同零线或 reducing 线的已成局部结论不等于这份全分类。

完整量子候选还要把这份静态入口接到同一原世界的七路实际来源。数学线、坐标、旋转和参数不生产准备、复制、事件、菜单、接受端、过程、完整输出未来、CountRead返回或物理钟。原有有限读取、支持事件、被动解码和有限返回数值校准照原适用域复用；未供应的全未来返回及具名全菜单分析器仍须实际构造。零和失败分支、整个环境、所有细记录、拒绝、停止、销毁及合法未来都继续存在。故本卷给出完整区间数学分类和条件候选，没有宣告整个原 $\Omega$ 的量子起源完成，也没有从尚缺来源推出不可能性。

[SQ]: https://github.com/the-omega-institute/trureturing/blob/70ca2d8fba4197189402b352ad513842cf539304/docs/develop/theory/AURIC_ZERO_DIMENSIONAL_CENTER_SQUARE_ORBIT_RECONSTRUCTION.md
[OP]: https://github.com/the-omega-institute/trureturing/blob/70ca2d8fba4197189402b352ad513842cf539304/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md
[PB]: https://github.com/the-omega-institute/trureturing/blob/70ca2d8fba4197189402b352ad513842cf539304/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md
[SF]: https://github.com/the-omega-institute/trureturing/blob/70ca2d8fba4197189402b352ad513842cf539304/docs/develop/theory/AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md
[FPB]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md
[AT]: https://github.com/the-omega-institute/trureturing/blob/2addd6f369b7387226c2b0cc984623dd3efe40a1/docs/develop/theory/AURIC_ORIGINAL_ATOMIC_SEPARATION_AND_PB_RECONSTRUCTION_CONTINUATION.md
[HOS]: https://hanche.folk.ntnu.no/joa/

## 追加锚（本行以下为增补区）

## 9. 演员轴平移保留 P2，却不运输原零探针预算

### 9.1 固定矩阵的较弱接口与准确来源

本节以[全 PB 多项式卷][AXF]为来源卷 $\mathsf F$，固定身份为 `2c1987c6ad3acbe4f9309ebde7bd204eacddd31a`。直接复用其 §41.1 的固定输出接口、式(39.7)的标准乘法恒等式及 §42 的零平移星形结论；不重证零平移刚性，不把标准零余量 PB 计为新内容。$\mathsf F$ §43 的分离背景稳定性保留自身形状前件，不用于下述真环境连线。

**定义 9.1（轴平移星形的固定输出数据）。** 在本节局部记

$$
\begin{gathered}
\mathcal A_\star=M_3(\mathbb C),\quad 1_\star=I_3,\quad
P_\star=\operatorname{diag}(1,1,0),\quad
\mathcal Q_\star=P_\star\mathcal A_\star P_\star,\\
c=\operatorname{diag}(1,2,0),\quad d=\operatorname{diag}(1,-2,0),\quad
t_0=\begin{pmatrix}0&0&1\\0&0&\sqrt2\\1&\sqrt2&0\end{pmatrix},\\
t=t_\lambda=t_0+\lambda c,\quad s=\rho d,\quad
K_\sigma(a,b)=\frac{\sigma i}{2}[a,b],\quad
g_0=K_\sigma(c,t)=K_\sigma(c,t_0),\quad g=g_0+s,
\qquad \lambda,\rho\in\mathbb R,\quad\sigma\in\{1,-1\}.
\end{gathered}
\tag{9.1}
$$

这里 $\mathcal Q_\star$ 是矩阵角，不是前文正锥 $C$；矩阵乘法、伴随和准确正锥均已给定。局部矩阵符号不替换前文 $E,F,J$。每份 $\phi$ 是 $\mathcal A_\star$ 上的数学正复线性泛函，原质量 $\phi(1_\star)$ 可为任意有限非负实数。对自伴 $U,V$ 置

$$
B_\phi(U,V)=\phi(U^2)\phi(V^2)-\phi(U\circ V)^2\ge0,
\qquad U\circ V=(UV+VU)/2.
\tag{9.2}
$$

只对实际 $x=x^*\in\mathcal Q_\star$ 定义全部原标签

$$
\begin{gathered}
h=K_\sigma(c,x),\quad r=c\circ x,\quad k=c\circ t,\\
R_+=x+h-k,\quad R_-=x-h+k,\quad
S_+=t+r+g,\quad S_-=t-r-g,\\
L_x=-2x\circ(h-k)-2t\circ(r+g),\\
\mathsf{P2}:\quad \phi(g)^2\le B_\phi(c,t),\qquad
\mathsf{PB}_x:\quad |\phi(L_x)|\le
\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}\quad(\phi\ge0).
\end{gathered}
\tag{9.3}
$$

特别是 $r=c\circ x$，不是别的探针变量。该有限接口没有未知总响应 $D$、指定外响应或以 $t$ 为演员的原调用，也没有输入正则性、压缩自然性、相对单位中性或免费 CP 完成。它与定义1.2的 $\mathsf H_I(D)$ 严格分开；若完整模型实际供应已分类角和 $g=D(c,t)$，才按 $\mathsf F$ §41.1 的原 PB 与外层 P2 得到这些必要预算。

### 9.2 每个非零平移的统一余量及区间消费者

**定理 9.2（非零平移的全部正读取零探针余量）。** 对每个实数 $\lambda\ne0$ 定义

$$
\begin{aligned}
T_\lambda&=\sqrt{5\lambda^2+6},&N_\lambda&=\sqrt{17\lambda^2+9/2},&j&=3/2,\\
I_\lambda&=\sqrt{\frac9{16\lambda^2}+\frac43+\frac{16\lambda^2}{9}},&
\kappa_\lambda&=\max\{|\lambda|,|\lambda|^{-1}\},\\
m_\lambda&=\frac1{144\kappa_\lambda^2I_\lambda^6(T_\lambda^2+j^2)N_\lambda(T_\lambda+j)},&
\varepsilon_\lambda&=\min\left\{\frac12,\frac{m_\lambda}{8(T_\lambda+N_\lambda)}\right\}.
\end{aligned}
\tag{9.4}
$$

则对任一 $\sigma$ 及全部 $|\rho|\le\varepsilon_\lambda$，(9.3)的 P2 对全部数学正泛函成立，且原 $x=0$ 的完整标签

$$
R_+=-k,\quad R_-=k,\quad S_\pm=t\pm g,\quad
L_0=-\{t,g\},\qquad \{a,b\}=ab+ba
\tag{9.5}
$$

满足统一余量

$$
\sqrt{B_\phi(-k,t+g)}+\sqrt{B_\phi(k,t-g)}-|\phi(-\{t,g\})|
\ge\frac{m_\lambda}{2}\phi(1_\star)\qquad(\phi\ge0).
\tag{9.6}
$$

因此每个非零 $\lambda$ 都容许明确的非零 $\rho$，例如取 $\rho=\varepsilon_\lambda/2>0$。特别地

$$
\lambda=1,\qquad \rho=\frac1{398131200}
\quad\Longrightarrow\quad
\text{(9.6)左侧}\ge\frac{\phi(1_\star)}{11059200}.
\tag{9.7}
$$

同一定理的实际应用取定义1.1中 $n=3$ 的 $M=C([0,1],M_3(\mathbb C))$，将全部矩阵置为常值截面。对每份数学正泛函 $\Psi$，P2 与(9.6)原样成立，质量为 $\Psi(u)$。而同一非零 $\rho$ 在 $\lambda=0$ 的常值数据被 $\mathsf F$ 定理42.2的一份向量读取复合任意点值映射排除。因此演员轴平移的 P2 不变性不蕴含零探针预算的反向运输。此结论不声称任何非零探针预算、完整响应模型或 $\mathsf H_I(D)$。

### 9.3 全复参数 P2 与明确的共同直线障碍

**证明，P2。** 设 $a=\phi(c^2)$、$b=\phi(c\circ t_0)$、$e=\phi(t_0^2)$。成熟的实 Gram 剪切恒等式给

$$
B_\phi(c,t_0+\lambda c)
=a(e+2\lambda b+\lambda^2a)-(b+\lambda a)^2=ae-b^2.
\tag{9.8}
$$

又 $[c,t_0+\lambda c]=[c,t_0]$，故同一 $\rho$ 的 P2 预算读数完全不变；二表的每个条目不必相同。这不是 PB 运输。

对 $z=X+iY$ 记 $\mathcal R=X^2+Y^2$，形成完整三维矩阵

$$
Q_z=(t_0-zc)^*(t_0-zc)+2\sigma Ys.
\tag{9.9}
$$

写 $v=(1,\sqrt2)^{\mathsf T}$、$c_2=\operatorname{diag}(1,2)$、$s_2=\rho\operatorname{diag}(1,-2)$。$Q_z$ 右下角为 $3$，左上块为 $vv^*+\mathcal R c_2^2+2\sigma Ys_2$，右上列为 $-\bar zc_2v$。其 Schur 补为

$$
D_z=\begin{pmatrix}
1+2\mathcal R/3+2\sigma\rho Y&\sqrt2(1-2\mathcal R/3)\\
\sqrt2(1-2\mathcal R/3)&2+4\mathcal R/3-4\sigma\rho Y
\end{pmatrix},
\tag{9.10}
$$

$$
(D_z)_{11}=\frac23X^2+\frac23\left(Y+\frac32\sigma\rho\right)^2+1-\frac32\rho^2,
\qquad
\det D_z=\frac{16}{3}X^2+\left(\frac{16}{3}-8\rho^2\right)Y^2.
\tag{9.11}
$$

当 $|\rho|\le1/2$，首项严格正，行列式非负；配方给 $D_z\succeq0$，再对环境坐标配方给 $Q_z\succeq0$，包括 $z=0$。这里保留两条环境连线。

置 $\mathcal P_w^\star=t_0^2-2\operatorname{Re}(w)(c\circ t_0)+|w|^2c^2+2\operatorname{Im}(w)g$。展开(9.9)给 $Q_{X+iY}=\mathcal P_{X+i\sigma Y}^\star$。对正 $\phi$，$\phi(\mathcal P_w^\star)$ 正是

$$
\begin{pmatrix}\phi(c^2)&\phi(c\circ t_0)-i\phi(g)\\
\phi(c\circ t_0)+i\phi(g)&\phi(t_0^2)\end{pmatrix}
\tag{9.12}
$$

在列 $(-w,1)^{\mathsf T}$ 上的二次值。这些列及其复数倍涵盖第二坐标非零的全部列；其余列由 $\phi(c^2)\ge0$ 处理。因此(9.12)半正定，行列式给原 P2；(9.8)将它传给所有 $\lambda$。没有除以质量或 Gram 对角，且尚未推出 PB。

**证明，显式矩阵障碍。** 暂置 $\rho=0$，记

$$
J_\star=\begin{pmatrix}0&0&1/2\\0&0&\sqrt2\\-1/2&-\sqrt2&0\end{pmatrix},\quad
g_0=i\sigma J_\star,\qquad
k=\begin{pmatrix}\lambda&0&1/2\\0&4\lambda&\sqrt2\\1/2&\sqrt2&0\end{pmatrix}.
\tag{9.13}
$$

$\det k=-3\lambda$，以下矩阵与 $k$ 两侧相乘均为 $1_\star$：

$$
k^{-1}=\begin{pmatrix}
2/(3\lambda)&-\sqrt2/(6\lambda)&2/3\\
-\sqrt2/(6\lambda)&1/(12\lambda)&\sqrt2/3\\
2/3&\sqrt2/3&-4\lambda/3
\end{pmatrix}.
\tag{9.14}
$$

局部置 $\mathsf A_\lambda=tk^{-1}$、$\mathsf H_\lambda=J_\star k^{-1}$。在 $\lambda=1$ 有

$$
\mathsf A_1=\begin{pmatrix}4/3&\sqrt2/6&-2/3\\\sqrt2/3&5/6&-2\sqrt2/3\\1/3&-\sqrt2/12&4/3\end{pmatrix},\quad
\mathsf H_1=\begin{pmatrix}1/3&\sqrt2/6&-2/3\\2\sqrt2/3&2/3&-4\sqrt2/3\\0&0&-1\end{pmatrix}.
\tag{9.15}
$$

对 $\mathsf E_\lambda=\operatorname{diag}(\lambda,\lambda,1)$，(9.14)逐项给

$$
\mathsf A_\lambda=\mathsf E_\lambda\mathsf A_1\mathsf E_\lambda^{-1},\qquad
\mathsf H_\lambda=\mathsf E_\lambda\mathsf H_1\mathsf E_\lambda^{-1}.
\tag{9.16}
$$

交换子及其明确逆为

$$
\mathsf C_1=[\mathsf A_1,\mathsf H_1]
=\begin{pmatrix}1/3&1/(6\sqrt2)&2/3\\0&-1/3&2\sqrt2\\1/3&-1/(6\sqrt2)&0\end{pmatrix},\quad
\mathsf C_1^{-1}=\begin{pmatrix}
9/8&-3/(8\sqrt2)&15/8\\9\sqrt2/4&-3/4&-9\sqrt2/4\\3/8&3/(8\sqrt2)&-3/8
\end{pmatrix}.
\tag{9.17}
$$

直接乘法给 $\mathsf C_1\mathsf C_1^{-1}=\mathsf C_1^{-1}\mathsf C_1=1_\star$。Frobenius 范数与相似变换给

$$
\|\mathsf C_1^{-1}\|^2\le\|\mathsf C_1^{-1}\|_F^2=\frac{1665}{64}<36,
\qquad
\|[\mathsf A_\lambda,\mathsf H_\lambda]^{-1}\|\le6\kappa_\lambda.
\tag{9.18}
$$

同样逐项平方求和，连同 $J_\star$ 的双边星形，给

$$
\|t\|\le T_\lambda,\quad\|k\|\le N_\lambda,\quad
\|k^{-1}\|\le I_\lambda,\quad\|J_\star\|=j,\quad
\|\mathsf A_\lambda\|\le T_\lambda I_\lambda,\quad
\|\mathsf H_\lambda\|\le jI_\lambda.
\tag{9.19}
$$

特别是 $\|k^{-1}\|_F^2=9/(16\lambda^2)+4/3+16\lambda^2/9$，整个环境行列均在内。这里的相似关系仅比较已知矩阵，不比较未知响应或不同输入的 PB 标签。

对复单位向量 $\eta$，置 $a=\eta^*\mathsf A_\lambda\eta$、$b=\eta^*\mathsf H_\lambda\eta$、$u_\eta=\mathsf A_\lambda\eta-a\eta$、$v_\eta=\mathsf H_\lambda\eta-b\eta$。二者均与 $\eta$ 复正交，且准确有

$$
[\mathsf A_\lambda,\mathsf H_\lambda]\eta
=(\mathsf A_\lambda-a1_\star)v_\eta-(\mathsf H_\lambda-b1_\star)u_\eta.
$$

由于 $|a|\le\|\mathsf A_\lambda\|$、$|b|\le\|\mathsf H_\lambda\|$，(9.18)–(9.19)给共同直线障碍

$$
\frac1{6\kappa_\lambda}
\le2I_\lambda(T_\lambda\|v_\eta\|+j\|u_\eta\|)
\le2I_\lambda\sqrt{T_\lambda^2+j^2}\sqrt{\|u_\eta\|^2+\|v_\eta\|^2},
\quad
\|u_\eta\|^2+\|v_\eta\|^2\ge\frac1{144\kappa_\lambda^2I_\lambda^2(T_\lambda^2+j^2)}.
\tag{9.20}
$$

### 9.4 两笔复亏量、真实面积与有限扰动

**证明，零余量时的严格余量。** 在复向量上定义实 Gram 面积与复 Gram 行列式

$$
\mathcal A(y,z)=\sqrt{\|y\|^2\|z\|^2-(\operatorname{Re}(y^*z))^2},\qquad
\Delta(y,z)=\|y\|^2\|z\|^2-|y^*z|^2.
\tag{9.21}
$$

实正交投影给 $\mathcal A(y,z)=\|y\|\|\Pi_{y,\mathbb R}z\|$，并包括 $y=0$ 地给出

$$
|\mathcal A(y,z+w)-\mathcal A(y,z)|\le\|y\|\|w\|.
\tag{9.22}
$$

向量泛函 $\phi_\xi(U)=\xi^*U\xi$ 满足 $\sqrt{B_{\phi_\xi}(U,V)}=\mathcal A(U\xi,V\xi)$。取 $\|\xi\|=1$、$y=k\xi$、$\eta=y/\|y\|$、$b_\pm=(t\pm g_0)\xi$；由 $k$ 可逆，$\|y\|\ge I_\lambda^{-1}$。又

$$
b_\pm=\|y\|(\mathsf A_\lambda\pm i\sigma\mathsf H_\lambda)\eta,
\qquad
\Delta(y,b_+)+\Delta(y,b_-)
=2\|y\|^4(\|u_\eta\|^2+\|v_\eta\|^2)
\ge\frac1{72\kappa_\lambda^2I_\lambda^6(T_\lambda^2+j^2)}.
\tag{9.23}
$$

等号由到 $\eta$ 复正交补的投影和平行四边形恒等式给出；没有丢掉环境分量。记 $a_\pm=\mathcal A(y,b_\pm)$、$q_\pm=\operatorname{Im}(y^*b_\pm)$，则

$$
a_\pm^2-q_\pm^2=\Delta(y,b_\pm),\quad
0\le|q_\pm|\le a_\pm\le N_\lambda(T_\lambda+j),\quad
 a_\pm-|q_\pm|\ge\frac{\Delta(y,b_\pm)}{2N_\lambda(T_\lambda+j)}.
\tag{9.24}
$$

末式在 $a_\pm+|q_\pm|>0$ 时由平方差分解得到；该和为零时两边均零。零 Gram 情形没有删去。

为区分探针下标与余量，记 $L_0^{(0)}=-\{t,g_0\}$。由 $\{t,[c,t]\}=[c,t^2]$、$[k,t]=[c,t^2]/2$，准确有

$$
L_0^{(0)}=-\sigma i[k,t],\qquad
\phi_\xi(L_0^{(0)})=\sigma(q_++q_-).
\tag{9.25}
$$

这只是 $\mathsf F$(39.7) 的已知标准 PB 在零探针处的恒等式。结合(9.23)–(9.25)及标量三角不等式，得到

$$
\mathcal A(k\xi,(t+g_0)\xi)+\mathcal A(k\xi,(t-g_0)\xi)
-|\phi_\xi(L_0^{(0)})|
\ge(a_+-|q_+|)+(a_--|q_-|)\ge m_\lambda.
\tag{9.26}
$$

新推断是用一个可逆交换子同时控制两笔复 Cauchy–Schwarz 亏量，从而取得真实预算的严格统一余量；并非重证标准零余量预算。

**证明，支付两侧扰动。** 现在恢复 $s=\rho d$，$\|s\|=2|\rho|$。由(9.22)，两笔右端面积的总下降至多

$$
2\|k\xi\|\|s\xi\|\le4N_\lambda|\rho|.
$$

左端 $L_0=L_0^{(0)}-\{t,s\}$ 的绝对读数增加至多 $\|\{t,s\}\|\le4T_\lambda|\rho|$。故每个单位向量的完整原零探针余量至少为

$$
m_\lambda-4(T_\lambda+N_\lambda)|\rho|\ge m_\lambda/2.
\tag{9.27}
$$

### 9.5 全部混合质量、确切有理常数及常值截面接线

**证明，所有正泛函。** 对自伴 $U,V$ 及正泛函 $\psi$，实 Gram 矩阵

$$
G_\psi(U,V)=\begin{pmatrix}\psi(U^2)&\psi(U\circ V)\\\psi(U\circ V)&\psi(V^2)\end{pmatrix}\succeq0.
\tag{9.28}
$$

承重的成熟二阶行列式根不等式为：$M,N\succeq0$ 时

$$
\sqrt{\det(M+N)}\ge\sqrt{\det M}+\sqrt{\det N}.
\tag{9.29}
$$

若 $M>0$，合同变换给 $Q=M^{-1/2}NM^{-1/2}\succeq0$，而 $Q$ 的两个非负特征值给 $\operatorname{tr}Q\ge2\sqrt{\det Q}$；将此代入 $\det(1+Q)=1+\operatorname{tr}Q+\det Q$ 即得(9.29)。以 $M+\delta1$ 替代奇异 $M$，对明确有限矩阵取 $\delta\downarrow0$ 即包含奇异情形。这不涉及未知 $D$ 的任何极限，也不另立新一般定理。

有限维谱分解给每个正泛函 $\phi=\sum_{j=1}^3w_j\phi_{\xi_j}$，其中 $w_j\ge0$、$\|\xi_j\|=1$、$\sum_jw_j=\phi(1_\star)$，零权保留。由(9.28)的线性、行列式根的一次齐次性和(9.29)，

$$
\sqrt{B_\phi(U,V)}\ge\sum_jw_j\sqrt{B_{\phi_{\xi_j}}(U,V)}.
\tag{9.30}
$$

分别用于两对实际原标签，再用 $|\sum_jw_j\phi_{\xi_j}(L_0)|\le\sum_jw_j|\phi_{\xi_j}(L_0)|$，(9.27)给(9.6)。若质量为零，谱权全零、$\phi=0$，结论为 $0\ge0$。至此包含所有混合、次归一、不等及零质量；没有把向量检验直接冒充混合结论。

**证明，有理消费者。** 在 $\lambda=1$，(9.14)给 $I_1=23/12\le2$，且 $\kappa_1=1$、$T_1=\sqrt{11}\le4$、$N_1=\sqrt{43/2}\le5$、$j=3/2\le2$。因此逐个支付分母因子后有

$$
m_1\ge\frac1{144\cdot64\cdot20\cdot5\cdot6}=\frac1{5529600},\quad
\varepsilon_1\ge\min\left\{\frac12,\frac1{8\cdot9\cdot5529600}\right\}
=\frac1{398131200},\quad \frac{m_1}2\ge\frac1{11059200}.
\tag{9.31}
$$

这证明(9.7)。两条环境边仍非零，且 $s\ne0$ 时

$$
c\circ t-ig=\begin{cases}ct-is,&\sigma=1,\\tc-is,&\sigma=-1,\end{cases}
\tag{9.32}
$$

所以通过该零探针接口的行确实有非标准余量。$|\rho|=1/2$ 的 P2 证书对所有平移成立，不表示该残差通过零探针 PB。

**证明，同一定理在本卷区间对象上的消费。** 取含单位正嵌入

$$
\iota:\mathcal A_\star\hookrightarrow M,\qquad (\iota a)(\tau)=a,
\qquad \iota(1_\star)=u,\qquad\tau\in[0,1],\qquad
\iota(ab)=\iota(a)\iota(b),\quad\iota(a^*)=\iota(a)^*.
\tag{9.33}
$$

它还是忠实的复线性保乘法、保伴随映射。因而平方、Jordan 乘法、交换子、反交换子与(9.3)中的全部原标签逐个交换：若 $\widetilde c=\iota c$、$\widetilde t=\iota t$、$\widetilde g=\iota g$、$X=\iota x$，则实际角为 $\iota(P_\star)M\iota(P_\star)$，且

$$
\widetilde h=\iota h,\quad\widetilde r=\widetilde c\circ X=\iota r,\quad
\widetilde k=\iota k,\quad
\widetilde R_\pm=\iota R_\pm,\quad\widetilde S_\pm=\iota S_\pm,\quad
\widetilde L_X=\iota L_x.
\tag{9.34}
$$

任一数学正泛函 $\Psi$ 给 $\phi=\Psi\circ\iota\ge0$，严格保持

$$
\phi(1_\star)=\Psi(u),\quad
B_\Psi(\iota U,\iota V)=B_\phi(U,V),\quad
\Psi(\widetilde L_X)=\phi(L_x),\quad\Psi(\widetilde g)=\phi(g).
\tag{9.35}
$$

于是(9.8)的 P2 剪切不变性及(9.6)的 $X=0$ 余量逐字提升，保留全部质量。这里只传已给常值数据及其乘积，不假定任何未知响应与 $\iota$、压缩或点值交换。

反向比较取同一个非零 $\rho$，在 $\lambda=0$ 直接调用 $\mathsf F$ 定理42.2：取其(42.5)–(42.7)的明确向量 $\xi_{\sigma,\rho}^{(0)}$，其质量为 $1+\varepsilon_\rho^2(1+\theta^2)$，其(42.8)的原零预算违反量至少 $\delta_\rho^2/(4M_\rho)>0$。对任意 $\tau\in[0,1]$，本域的实际点值映射 $\operatorname{ev}_\tau:M\to\mathcal A_\star$ 含单位且正，且 $\operatorname{ev}_\tau\iota=\operatorname{id}$。因此

$$
\Psi_{\tau,\sigma,\rho}^{(0)}
=\phi_{\xi_{\sigma,\rho}^{(0)}}\circ\operatorname{ev}_\tau\ge0,\qquad
\Psi_{\tau,\sigma,\rho}^{(0)}(u)=1+\varepsilon_\rho^2(1+\theta^2)
\tag{9.36}
$$

在零平移常值标签上保留同一严格违反量。这里点值是明确已知映射，不是宣告它属于原物理评价族。因而 $t_0$ 与 $t_0+\lambda c$ 的 P2 预算相同，零预算合法性却不同；(9.33)–(9.36)是本卷实际常值截面消费者，不是独立的嵌入包装命题。定理得证。∎

### 9.6 来源全文、物理接回与尚缺桥梁

本节所需物理来源仍准确采用 $\mathsf F$ 定义41.4的 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$，$S$ 为原对称响应：沿 $41.4\Rightarrow40.1\Rightarrow36.1\Rightarrow32.3\Rightarrow\S27.1\Rightarrow26.3\Rightarrow22.3\Rightarrow18.2\Rightarrow\{10.2,15.2,\mathrm{AH}28.1,64.2,75.1\}\Rightarrow\mathrm{SQ}47.1\text{--}47.13$，将每份定义、合同、公式、量词及逐项递归纳入、逐层固定版本的全部上游全文，逐句、逐公式、逐量词同时合取。编号链和下面说明不替代任何全文或缩短任何量词。

其 AH 直接身份为 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`，W/CC/PT 为 `3b10aed60f60e4901bae6cf2e160bf439d642e64`；SQ 自身 §§1.3、39、41.1、47.1 的两层主源 `dcaebc0b9ca5a3a463fd8cfd161d38967df28668`、`0aa11dbc3dc337d667b98900673e07d67b99bf46` 各守层级。OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`，AH22.1 的 `2addd6f369b7387226c2b0cc984623dd3efe40a1`，AH12.1 的 `39a0505470ea889dd9d4301ad60cd9506a5e8b58`，AH42.1 内的 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7`，以及 R5 的 `aef46ce7497cf8ee6bef9bb7356a4483f3bfe6f0` 全部保持；直接身份不压平内层身份。前文1–8的固定引文、定义6.1和全部七合同另按自身版本完整保留，不在未证对应下将两套钉版谓词认作相同，也不宣告任何一套已实现。

同一 $\Omega/\mathrm{native}$ 的对象、准备、事件、设备、程序、原比较权 $q$、共同全词 $K/\mathsf J$、parent、ready、合法控制、旗标、中心、经典及不等维块、无轴对象、中间切口、全部模式网络、根类、十一端点、配置、实际逆等距边、静默、零活动、终端及读器合同均保持。网络 $D,C$ 不替换成本响应或正锥；未定义请求不补零箭头。原评价族没有扩大为全部数学态或向量准备；(9.35)只是数学正泛函的拉回。

已识别标准块的通常／相反乘法、数学 Hilbert/GNS 与 Born 配对仍按 $\mathsf F$ §§36.1、40.2及 AH64.1、75.1复用，角循环向量平方范数仍是原角质量。式(9.32)的非零余量不能插入标准行结论。实际准备、相干控制、事件绑定的完整 Born 菜单保留同一来源和全部原质量；全局归一须严格正单位质量，角归一另须真实条件化及严格正角质量，零、不等、次归一及非正常质量不删。真正相关联合与张量须同一实际共同来源、全部相关输入、忠实同向交换腿、共同生成、分离及重数；相同边缘、分别可达、数学谱格或辅助 GNS 不支付共同实现。

typed CP、箭头下降、整台递归同源参考、真支持与支持内补、交织夹界、每个所需有限深度和每个正精度均保留。完整仪器、TP、Kraus、更新、Lüders仍需完整 typed 菜单、单位分区、接受端、校准、表示和收敛，量化整个环境、全部成功／失败／细记录／port／post-port 输出及每份完整输出的每个仍合法未来；只在严格正实际输出质量上归一，失败、零支与完整输出不删。合法顺序、自适应、并行历史、真分组遗忘、停止、拒绝、销毁、泄漏、同数两侧及逆向真实 Return、含活动 ready 和 producer 的完整 CountRead 均不被矩阵相等替代；原程序、记录、次序、$q$ 零集和未来权限不合并。

正常性、指定前对偶、可数可加、无限菜单记录和收敛，各须原扩展来源；实际保持原域的连续可逆流及实际逆、物理钟单位、酉实现、生成元域、Hamiltonian 能量、作用量和共同正物理 $\hbar$ 各保留原前件。矩阵反演、数学相似、截面嵌入与有限谱分解不是可执行物理控制，不生产这些来源。R5 §12的非零交替双线性、同域及完整 P/N 入口不删。本节没有从条件量子消费者推出物理实现。

一般原有限谱接口仍需证明 $\mathsf F$(41.28)的两份原缺陷相等：若这些固定数据实际来自完整原模型，则沿其已付恒等式有

$$
\mathcal E_+^D=D(c-g,k)-K_\sigma(c-g,k),\quad
\mathcal E_-^D=D(c+g,-k)-K_\sigma(c+g,-k),\quad
\mathcal E_+^D-\mathcal E_-^D=2cs,\qquad
\mathcal E_+^D=\mathcal E_-^D\ \text{仍须证明}.
\tag{9.37}
$$

没有构造这样的 $D$。原全局标量单位行保留既有结论；一般混合整行、未覆盖相对标量、无限谱、任意输入拼接和完整奇数阶段 UHF 仍须原桥梁。定性 $\omega(q)\to0$ 不支付增长分割的 $N\omega(q)^2\to0$，本节也未给相应率。前文3.1、5.2的全 H／总响应前件没有由零探针付清，故不存在与它们的矛盾或新的全 H 分类。

实与复 Cauchy–Schwarz、正交投影、Schur 补、Frobenius 界、有限维谱分解和二阶行列式根的超可加性均为成熟工具，所需步骤在承重证明内展开。正泛函和表示背景沿 $\mathsf F$ §41.5 的 Blackadar《Operator Algebras》及 Hanche-Olsen–Størmer《Jordan Operator Algebras》。本节的关系推导是非零平移的严格统一余量及其常值截面消费者，不是 P2 剪切或行列式不等式的新一般定理；不作历史优先权、穷尽检索、外部开放问题解决或独立公理数减少主张。

### 9.7 完整直观与全部非零探针的准确余项

把前两个坐标看成刻度为一和二的两间房，第三个坐标是与两房都连通的环境。给输入加上沿演员刻度的对角部分，不改变原二表的面积预算或交换子，因此 P2 看不出这次移动，但原 PB 的外标签确实改变。零平移时，来源卷已用共同零方向及一次有限读取排除所有非零误差；非零平移时，完整的 $k$ 可以反演，得到两份明确三维作用，它们的交换子可逆，所以不可能同时把同一条复直线保持得任意精确。这一个共同障碍同时撑开两笔复 Gram 亏量，再变成真实面积相对左端的统一正余量；小误差对右边两面积的下降和左边绝对读数的增加都能分别付清。平移为一、误差为 $1/398131200$ 时，每份正读取至少留下其质量除以 $11059200$ 的余量；二阶行列式根的超可加性将所有向量读取提升到全部混合读取，零质量仍保留。把这些矩阵逐个放成区间上的常值截面，所有标签、乘积和质量原样通过，故这确是本卷原响应运输主题中的一个有限预算反例：P2 的轴剪切不授权零预算运输。它没有验证任何非零角内探针，更没有造出未知总响应；一般两份缺陷为何相等、增长谱分割如何累加，以及真实准备、完整 Born 菜单、同一相关来源、整台仪器的全部输出与未来、Return、CountRead、正常性、前对偶、物理钟、动力学和共同正作用量，仍由原来的关系与完整来源承担。

准确的未解全探针命题仍是：对(9.1)的任意 $\lambda\ne0$，

$$
\bigl[\mathsf{P2}\ \land\ \mathsf{PB}_0\ \land\
(\forall\,0\ne x=x^*\in\mathcal Q_\star)(\forall\phi\ge0)\ \mathsf{PB}_x\bigr]
\ \stackrel{?}{\Longrightarrow}\ \rho=0.
\tag{9.38}
$$

对(9.7)的候选，首个未付关系准确为

$$
(\forall\,0\ne x=x^*\in\mathcal Q_\star)(\forall\phi\ge0)\quad
|\phi(L_x)|\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{9.39}
$$

区间上还须将(9.39)的探针换成全部 $0\ne X=X^*\in\iota(P_\star)M\iota(P_\star)$，包括所有非常值截面，以(9.3)的同一公式和全部正 $\Psi$ 检验；这些非零常值及非常值探针、未知总 $D$ 的全部原调用均未由本节取得。没有给出该候选的全探针证书或失败非零探针，所以它不是(9.38)、完整 PB或完整原公理的反模型。

[AXF]: https://github.com/the-omega-institute/trureturing/blob/2c1987c6ad3acbe4f9309ebde7bd204eacddd31a/docs/develop/theory/AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md

## 追加锚（本行以下为增补区）

## 10. 同一三维读取的双接触：非零角探针排除零探针候选

### 10.1 原角内的明确有限结论

**定义 10.1（保持全部原标签的参数区域）。** 沿用(9.1)–(9.3)的已给矩阵乘法、伴随、正锥及数学正复线性泛函，局部记 $A=\mathcal A_\star$、$P=P_\star$、$C_\star=PAP$。探针域始终是 $(C_\star)_{\rm sa}$，不是整个 $A_{\rm sa}$。取

$$
\lambda\ne0,\qquad 0<|\rho|\le\min\{1/4,|\lambda|\},\qquad
q=-\operatorname{sgn}(\lambda\rho)\in\{1,-1\}.
\tag{10.1}
$$

同一数据仍为 $t=t_0+\lambda c$、$s=\rho d$、$g=K_\sigma(c,t)+s$。为明确本节所检验的接口，再列出

$$
\begin{gathered}
h=K_\sigma(c,x),\quad r=c\circ x,\quad k=c\circ t,\qquad
R_\pm=x\pm(h-k),\quad S_\pm=t\pm(r+g),\\
L_x=-2x\circ(h-k)-2t\circ(r+g),\qquad
B_\phi(U,V)=\phi(U^2)\phi(V^2)-\phi(U\circ V)^2.
\end{gathered}
\tag{10.2}
$$

这里不引入未知总映射 $D$、已指定的外响应或以 $t$ 为演员的预算，也不给输入连续性、响应缩放、协变性、压缩自然性或单位平移中性。两条环境边保留在每个原标签中。

**定理 10.2（双接触的实际非零探针）。** 对(10.1)中的每对参数及每个 $\sigma=\pm1$，下面(10.4)–(10.6)给出一个有限的实际 $0\ne x=x^*\in C_\star$ 和一个数学正向量泛函 $\phi_\xi$，使

$$
\boxed{\quad
|\phi_\xi(L_x)|-\sqrt{B_{\phi_\xi}(R_+,S_+)}
-\sqrt{B_{\phi_\xi}(R_-,S_-)}>8|\lambda\rho|>0.
\quad}
\tag{10.3}
$$

该读取的完整质量为 $\phi_\xi(1_\star)=\|u\|^2+|z|^2>0$，不作归一。与此同时，全部数学正泛函的 P2 仍由9.3中 $|\rho|\le1/2$ 的证书及(9.8)成立。因此本定理排除的是这份固定输出数据的全部原探针预算，不是构造完整 PB 或完整原公理的反模型。

### 10.2 一个实根及同一块探针的完整定义

**证明，根与可定义性。** 在(9.1)已经给定的实数模型中，令 $p$ 为

$$
H(p)=6p^3+31p^2+54p+39=0,\qquad
-\frac{14}{5}<p<-\frac{11}{4}
\tag{10.4}
$$

的根。这不是从纸面根构造推出实数载体。准确地，$H(-14/5)=-109/125<0$、$H(-11/4)=5/32>0$，而

$$
H'(r)=18(r+31/18)^2+11/18\ge11/18>0\qquad(r\in\mathbb R).
$$

介值定理及严格单调性给存在与唯一性，并同时保留上述严格有理端点界。

先取 $\sigma=1$。定义

$$
\begin{gathered}
b=p+iq,\quad c_0=\operatorname{diag}(1,2),\quad d_0=\operatorname{diag}(1,-2),\quad
v=\binom1{\sqrt2},\quad w=\binom{1/2}{\sqrt2},\\
u=\binom{\sqrt2(1+b)}{-(2+b)/2},\qquad C_j=u^*c_0^ju\quad(j=1,2,3),\\
m=-q\lambda C_2,\quad D_b=(1-b)(2-b),\qquad
Z=\frac{\lambda(2C_1-bC_2)-imD_b}{4p},\\
z=-\sqrt2Z,\quad \xi=\binom{u}{z},\quad \tau=\lambda c_0u+vz,\\
y=-i(c_0-bI_2)^{-1}c_0\tau,\qquad
y_c=(b+2/b)y+(2i/b)\tau+i\lambda c_0^2u.
\end{gathered}
\tag{10.5}
$$

再置

$$
\begin{gathered}
X=[\,y\ \ y_c\,][\,u\ \ c_0u\,]^{-1},\qquad
a=\operatorname{diag}\left(\frac1{p-1},\frac{-2}{p-2}\right),\\
x^{(0)}=X\oplus0,\qquad
x=(X+\rho a)\oplus0,\qquad \phi_\xi(A_1)=\xi^*A_1\xi.
\end{gathered}
\tag{10.6}
$$

$p,b,1-b,2-b,p-1,p-2$ 均非零，且 $u_1u_2\ne0$，因为 $p<0$ 而 $\operatorname{Im}b=q\ne0$。所有矩阵逆具体为

$$
(c_0-bI_2)^{-1}=\operatorname{diag}((1-b)^{-1},(2-b)^{-1}),\qquad
[\,u\ \ c_0u\,]^{-1}
=\frac1{u_1u_2}\begin{pmatrix}2u_2&-u_1\\-u_2&u_1\end{pmatrix}.
$$

因此所有式子都是有限定义；尚须证明的是同一 $X$ 自伴以及预算的严格违反。正泛函 $\phi_\xi$ 的正性直接来自 $\xi^*A_1\xi\ge0$ 对每个 $A_1\ge0$ 成立，其质量是 $\|u\|^2+|z|^2$，其中 $u\ne0$。

### 10.3 同一个矩阵的三项 Hermitian 配对

**证明，自伴实现。** 写

$$
A_0=(p+1)^2+1,\quad B_0=(p+2)^2+1,\qquad
C_1=2A_0+B_0/2,\quad C_2=2A_0+B_0,\quad C_3=2A_0+2B_0.
\tag{10.7}
$$

代入多项式得

$$
2\{C_1-C_3+(p+3)C_2\}=H(p)=0.
\tag{10.8}
$$

又有明确的环境配对

$$
W=w^*u=-\sqrt2/2,\qquad v^*u=-bW,\qquad z\overline W=Z.
\tag{10.9}
$$

由定义 $Xu=y$、$Xc_0u=y_c$。矩阵 $[u\ c_0u]$ 可逆，因此成熟的 Hermitian 型合同判别（极化的二阶基坐标形式）在这里准确要求三项

$$
u^*y\in\mathbb R,\qquad
u^*y_c=\overline{u^*c_0y},\qquad
(c_0u)^*y_c\in\mathbb R.
\tag{10.10}
$$

中间一项必须互为复共轭。两列构成基，故这三项正好是 $[u\ c_0u]^*X[u\ c_0u]$ 的两个对角实性及非对角共轭对称性，足以证明 $X=X^*$。

先用 $u$ 的两个条目作通分，$c_1=1,c_2=2$，得到

$$
\sum_{j=1}^2\frac{c_j^2|u_j|^2}{c_j-b}=\frac{2C_1-bC_2}{D_b},\qquad
\sum_{j=1}^2\frac{c_jv_j\bar u_j}{c_j-b}=\frac{2\sqrt2p}{D_b}.
\tag{10.11}
$$

于是 $D_bu^*y=-i\lambda(2C_1-bC_2)-2i\sqrt2pz=mD_b$，即 $u^*y=m\in\mathbb R$，第一项成立。

记 $\tau_j=u^*c_0^j\tau$，$j=0,1$，及 $n=u^*c_0y$。由(10.5)、(10.9)及 $(c_0-b)y=-ic_0\tau$，

$$
\tau_0=\lambda C_1-\bar bZ,\qquad \tau_1=\lambda C_2+2Z,\qquad
n=bm-i\tau_1,\qquad
u^*y_c=(b+2/b)m+(2i/b)\tau_0+i\lambda C_2.
\tag{10.12}
$$

这里 $m=-q\lambda C_2$、$q^2=1$ 还给出便于逐项核对的实虚分解

$$
\operatorname{Re}Z=\frac{\lambda\{2C_1+3(1-p)C_2\}}{4p},\qquad
\operatorname{Im}Z=\frac{q\lambda(p-3)C_2}{4}.
\tag{10.13}
$$

因此 $2\operatorname{Re}(\bar bZ)=\lambda C_1-\lambda pC_2$。对中间配对直接相减，准确得到

$$
\frac b{2i}(u^*y_c-\bar n)
=(bq-i)m+\lambda C_1-2\operatorname{Re}(\bar bZ)
=pqm+\lambda pC_2=0.
\tag{10.14}
$$

这证明第二项，而不是把 $u^*y_c$ 与 $n$ 无共轭地认作相等。

最后由(10.12)代入 $y_c$，

$$
(c_0u)^*y_c=(b^2+2)m-ib\tau_1+i\lambda C_3,\qquad
\operatorname{Re}(b\tau_1)=\lambda C_1+\lambda(3-p)C_2.
\tag{10.15}
$$

第二式也直接由(10.13)求实部得到。第一式的虚部为

$$
2pqm-\operatorname{Re}(b\tau_1)+\lambda C_3
=\lambda\{C_3-C_1-(p+3)C_2\}=0
\tag{10.16}
$$

其零值由(10.8)给出。这完成全部三项，故 $X=X^*$；$a$ 是实对角矩阵，(10.6)确为实际自伴角探针。

### 10.4 两对完整标签在同一三维向量上接触

**证明，环境不被压缩的同时接触。** 暂令 $s=0$，在 $x^{(0)}$ 上形成全部原标签，以上标 $(0)$ 表示。设

$$
\mathsf X=x^{(0)}\xi,\quad \mathsf T=t\xi,\quad
\mathsf A=(h^{(0)}-k)\xi,\quad
\mathsf B=(r^{(0)}+g_0)\xi.
$$

前两坐标的完整式子是

$$
\begin{aligned}
\mathsf X_{12}&=y,&\quad \mathsf T_{12}&=\tau,\\
\mathsf A_{12}&=\tfrac i2(c_0y-y_c)-\tfrac12(c_0\tau+\lambda c_0^2u),&
\mathsf B_{12}&=\tfrac12(c_0y+y_c)+iwz.
\end{aligned}
\tag{10.17}
$$

把 $y_c$ 及 $(c_0-b)y=-ic_0\tau$ 代入 $\mathsf A_{12}$，得 $\mathsf A_{12}=(\tau-iy)/b$。又因同一已知乘法中

$$
r^{(0)}-ih^{(0)}=cx^{(0)},\qquad g_0+ik=ict,
$$

有 $\mathsf B_{12}-i\mathsf A_{12}=c_0(y+i\tau)=by$。所以前两坐标满足 $\mathsf T=i\mathsf X+b\mathsf A$、$\mathsf B=b\mathsf X+i\mathsf A$。

第三坐标须单独保留并核对。由(10.9)，准确为

$$
\mathsf X_3=0,\qquad \mathsf T_3=-bW,\qquad
\mathsf A_3=-W,\qquad \mathsf B_3=-iW.
\tag{10.18}
$$

它们也满足同样两式。因此在完整的 $\mathbb C^3$ 中

$$
\mathsf T=i\mathsf X+b\mathsf A,\qquad
\mathsf B=b\mathsf X+i\mathsf A,\qquad
S^{(0)}_+\xi=(i+b)R^{(0)}_+\xi,\quad
S^{(0)}_-\xi=(i-b)R^{(0)}_-\xi.
\tag{10.19}
$$

$q=1$ 时负对斜率为实数 $-p$，正对斜率为 $p+2i$；$q=-1$ 时正对斜率为实数 $p$，负对斜率为 $-p+2i$。这两条接触线由同一 $x^{(0)}$、同一 $\xi$ 同时实现，不是分别可达的两个极值。

现在恢复同一非零 $s$ 与 $x=x^{(0)}+\rho(a\oplus0)$。实对角修正满足

$$
(pI_2-c_0)a=d_0,\qquad [a,c_0]=[a,d_0]=0.
$$

故在完整算子标签上准确有

$$
\begin{gathered}
R_\pm=R^{(0)}_\pm+\rho(a\oplus0),\\
S_+=S^{(0)}_++p\rho(a\oplus0),\qquad
S_-=S^{(0)}_--p\rho(a\oplus0).
\end{gathered}
\tag{10.20}
$$

因而 $q=1$ 时仍有 $S_-\xi=-pR_-\xi$，$q=-1$ 时仍有 $S_+\xi=pR_+\xi$。实 Gram 公式遂使这一对的 $B_{\phi_\xi}$ 精确为零，且其 $K_1$ 读取也为零；不是只在 $\rho=0$ 接触。

### 10.5 另一对的复 Gram 亏量与准确残差

**证明，有限亏量。** 将另一对记作 $(R,S)$，定义

$$
\begin{gathered}
R_0=\begin{cases}R^{(0)}_+\xi,&q=1,\\R^{(0)}_-\xi,&q=-1,\end{cases}
\qquad e=\binom{au}{0},\qquad
U=\|R_0\|^2,\quad V_0=\operatorname{Re}(R_0^*e),\quad W_0=\|e\|^2,\\
J=2|\lambda|(p^2-1)>0.
\end{gathered}
\tag{10.21}
$$

(10.18)给 $(R_0)_3=-qW$，故 $U\ge1/2$。两条完整向量式为

$$
R\xi=R_0+\rho e,\qquad S\xi=(qp+2i)R_0+qp\rho e.
\tag{10.22}
$$

对自伴 $R,S$，$\phi_\xi(K_1(R,S))=-\operatorname{Im}((R\xi)^*S\xi)$。直接代入(10.22)得

$$
Q:=\phi_\xi(K_1(R,S))=-2(U+\rho V_0).
\tag{10.23}
$$

成熟的复 Gram 行列式在此给非负亏量

$$
\begin{aligned}
\Delta&=\|R\xi\|^2\|S\xi\|^2-|(R\xi)^*S\xi|^2\\
&=4\rho^2\{UW_0-|R_0^*e|^2\}\le4\rho^2UW_0.
\end{aligned}
\tag{10.24}
$$

具体地，$S\xi-(qp+2i)R\xi=-2i\rho e$；给第二列减去第一列的复数倍不改 Gram 行列式，而给 $R_0$ 加上 $\rho e$ 也不改它与 $e$ 的行列式。这证明等式，包括复线性相关情形。由实部、虚部的平方分解，

$$
B_{\phi_\xi}(R,S)=Q^2+\Delta.
\tag{10.25}
$$

**证明，原左端的准确一次残差。** $\mathsf F$(39.7)只在已知标准乘法中复用：在 $s=0$，对任意实际 $x$，它给 $K_1(R_+,S_+)-K_1(R_-,S_-)=L_x$。在标签中恢复 $s$，外层两个交换子之差增加 $2K_1(x,s)$，而 $L_x$ 减少 $\{t,s\}$，所以完整矩阵恒等式为

$$
K_1(R_+,S_+)-K_1(R_-,S_-)-L_x
=2K_1(x,s)+\{t,s\}.
\tag{10.26}
$$

这不为未知外响应指定任何值。本节局部将右侧读取记为标量 $F$，不替换(1.8)的函数。因 $[a,d_0]=0$，它准确线性于 $\rho$：

$$
F=\phi_\xi(2K_1(x,s)+\{t,s\})
=\rho\,\phi_\xi(2K_1(x^{(0)},d)+\{t,d\}).
\tag{10.27}
$$

令 $j_0=u^*d_0y$、$h_0=u^*d_0c_0^{-1}y$，其中 $c_0^{-1}=\operatorname{diag}(1,1/2)$。由 $(c_0-b)y=-ic_0\tau$ 得 $\tau=iy-ibc_0^{-1}y$，从而

$$
\begin{aligned}
\phi_\xi(2K_1(x^{(0)},d))&=2\operatorname{Im}j_0,\\
\phi_\xi(\{t,d\})&=2\operatorname{Re}(u^*d_0\tau)
=-2\operatorname{Im}j_0+2\operatorname{Im}(bh_0).
\end{aligned}
\tag{10.28}
$$

$d_0c_0^{-1}=3I_2-2c_0$ 给 $h_0=(3-2b)m+2i\tau_1$。再由(10.15)–(10.16)，

$$
\begin{aligned}
\operatorname{Im}(bh_0)
&=q(3-4p)m+2\operatorname{Re}(b\tau_1)\\
&=3qm+2\lambda C_3
=\lambda(2C_3-3C_2)
=\lambda(B_0-2A_0)=-\lambda(p^2-1).
\end{aligned}
\tag{10.29}
$$

因此 $F=-2\lambda\rho(p^2-1)=q|\rho|J$。零面积对的交换子读取为零，另一对在(10.26)之差中的符号是 $q$，故

$$
\phi_\xi(L_x)=q(Q-|\rho|J).
\tag{10.30}
$$

### 10.6 严格有限差额、非零性及两种符号

**证明，完整余项界。** 有理根区间(10.4)给

$$
|u_1|^2<9,\quad |u_2|^2<1/2,\quad
|a_{11}|<1/3,\quad |a_{22}|<1/2,\quad
W_0<1+1/8=9/8<2,\quad
J>\frac{105}{8}|\lambda|>12|\lambda|.
\tag{10.31}
$$

记 $r_0=|\rho|$。复 Cauchy–Schwarz 给 $|V_0|\le\sqrt{UW_0}$，结合 $U\ge1/2$、$W_0<2$ 及 $r_0\le1/4$，

$$
U+\rho V_0\ge U-r_0\sqrt{UW_0}\ge U/2,\qquad
Q<0,\qquad |Q|\ge U.
\tag{10.32}
$$

由(10.24)–(10.25)的平方差分解，全部有限亏量满足

$$
\sqrt{B_{\phi_\xi}(R,S)}-|Q|
=\frac{\Delta}{\sqrt{Q^2+\Delta}+|Q|}
\le\frac{4r_0^2UW_0}{2U}=2r_0^2W_0<4r_0^2.
\tag{10.33}
$$

没有除以零，因为 $U\ge1/2$。另一对面积精确为零，且由(10.30)、$Q<0$ 有 $|\phi_\xi(L_x)|=|Q|+r_0J$。于是

$$
\begin{aligned}
&|\phi_\xi(L_x)|-\sqrt{B_{\phi_\xi}(R_+,S_+)}-\sqrt{B_{\phi_\xi}(R_-,S_-)}\\
&\qquad\ge r_0J-2r_0^2W_0
>12r_0|\lambda|-4r_0^2
\ge8|\lambda\rho|>0,
\end{aligned}
\tag{10.34}
$$

最后一步仅用 $r_0\le|\lambda|$。这是一份实际有限探针的估计，没有极限探针或被省略的余项。

还须排除 $x=0$。由 $u^*Xu=m$、$C_2\ge\|u\|^2>0$、$\|a\|<1/2$ 及 $r_0\le|\lambda|$，

$$
|u^*(X+\rho a)u|
\ge|\lambda|C_2-r_0\|a\|\|u\|^2
>\tfrac12|\lambda|C_2>0.
\tag{10.35}
$$

故 $x\ne0$，其完整质量仍为 $\|u\|^2+|z|^2>0$。质量未被角质量或单位质量代换。

对 $\sigma=-1$，取上述 $x,\xi$ 的逐项复共轭。$c,t,d$ 都是实矩阵，且 $K_{-1}(c,\bar x)=\overline{K_1(c,x)}$，故 $g,h,r,k,R_\pm,S_\pm,L_x$ 全部逐项复共轭。对自伴标签，$\phi_{\bar\xi}(\bar A_1)=\overline{\phi_\xi(A_1)}=\phi_\xi(A_1)$；平方、Jordan 读数及质量均保持。于是同一严格差额和实际非零性适用于另一符号。定理10.2得证。∎

### 10.7 同一组数据的零探针与全探针分离

**定理 10.3（全部正读取零预算仍不足）。** 对每个 $\lambda\ne0$，取(9.4)已经定义的 $\varepsilon_\lambda>0$，并置

$$
\rho_\lambda=\frac12\min\{\varepsilon_\lambda,1/4,|\lambda|\}>0.
\tag{10.36}
$$

对每个符号，同一份 $c,t_\lambda,g_0+\rho_\lambda d$ 满足全部数学正泛函的 P2，以及全部数学正泛函的原 $x=0$ 预算，并有(9.6)的统一余量 $\frac{m_\lambda}{2}\phi(1_\star)$；但该同一数据被定理10.2的一份实际非零 $x$ 和正读取排除，违反量大于 $8|\lambda\rho_\lambda|$。正质量的零探针余量严格为正，零质量仍保留。

特别地，(9.7)的同一有理候选满足上述 P2 和全部零探针余量，却有明确违反

$$
\lambda=1,\quad \rho=\frac1{398131200},\qquad
|\phi_\xi(L_x)|-\sum_{\pm}\sqrt{B_{\phi_\xi}(R_\pm,S_\pm)}
>\frac1{49766400}.
\tag{10.37}
$$

**证明。** (10.36)同时支付 $0<\rho_\lambda\le\varepsilon_\lambda$ 和(10.1)，无需比较 $\varepsilon_\lambda$ 与另外两个上界的大小。定理9.2给全部正读取的 P2、混合质量及零预算余量，定理10.2给同一参数的非零探针。对(10.37)，P2 与零预算直接复用(9.7)、(9.31)；其参数落在(10.1)，而 $8/398131200=1/49766400$，故(10.34)给所示严格界。存在一个正读取的违反已否定全称预算，不需将该读取提升为全体读取上的违反。∎

(9.39)对有理候选的全称命题由(10.37)否定；在(10.1)的整个区域，(9.38)的非零残差前件也被实际探针排除。零残差时，$\mathsf F$(39.7)及复 Cauchy–Schwarz 对每个 $\lambda$ 给全部原探针预算；零平移时，$\mathsf F$ 定理42.2已经排除每个非零 $\rho$。对 $\lambda\ne0$ 且 $|\rho|>\min\{1/4,|\lambda|\}$，这里没有消去残差或构造全探针模型；(9.38)在该剩余区域的全家族推断仍须证明。有限界(10.32)–(10.34)不适用，并不构成原命题的反例。

### 10.8 实际常值角截面消费严格违反

**定理 10.4（完整区间对象中的一个实际失败探针）。** 取本卷 $n=3$ 的 $M=C([0,1],M_3(\mathbb C))$，使用(9.33)的含单位忠实常值嵌入 $\iota$。对定理10.2的任意固定参数、符号和所造探针，令

$$
\widetilde P=\iota(P),\quad \widetilde c=\iota(c),\quad
\widetilde t=\iota(t),\quad \widetilde g=\iota(g),\quad
x_I=\iota(x)\in(\widetilde PM\widetilde P)_{\rm sa}.
\tag{10.38}
$$

则 $x_I$ 是实际非零连续角截面。任取 $\tau_*\in[0,1]$，实际点值映射给数学正泛函

$$
\Psi=\phi_\xi\circ\operatorname{ev}_{\tau_*},\qquad
\Psi(u)=\phi_\xi(1_\star)=\|u\|^2+|z|^2>0.
\tag{10.39}
$$

在(10.2)的同一完整公式下，其全部标签满足

$$
\begin{gathered}
\widetilde h=K_\sigma(\widetilde c,x_I)=\iota(h),\quad
\widetilde r=\widetilde c\circ x_I=\iota(r),\quad
\widetilde k=\widetilde c\circ\widetilde t=\iota(k),\quad
\widetilde g=\iota(g),\\
\widetilde R_\pm=\iota(R_\pm),\quad
\widetilde S_\pm=\iota(S_\pm),\quad
\widetilde L_{x_I}=\iota(L_x),\\
B_\Psi(\widetilde R_\pm,\widetilde S_\pm)
=B_{\phi_\xi}(R_\pm,S_\pm),\quad
\Psi(\widetilde L_{x_I})=\phi_\xi(L_x).
\end{gathered}
\tag{10.40}
$$

因此该实际截面及同一质量正读取严格违反完整的探针预算，差额仍大于 $8|\lambda\rho|$。对定理10.3的相同常值数据，全部正 $\Psi'$ 的 P2 和原 $x_I=0$ 统一余量同时成立，却由(10.38)–(10.40)的一份非零常值截面排除全探针预算。

**证明。** $\iota$ 保乘法、伴随、复线性和单位，故平方、Jordan 乘法、交换子、反交换子及每一个标签逐字运输。忠实性给 $x_I\ne0$，角关系由 $PxP=x$ 运输。点值是含单位正映射且 $\operatorname{ev}_{\tau_*}\iota=\operatorname{id}$，所以(10.39)–(10.40)连同完整质量准确成立。严格违反由(10.3)直接代入，不缩减第三坐标或质量。

对全部正 $\Psi'$ 的零探针正余量，使用(9.35)的 $\phi=\Psi'\circ\iota$，其单位质量恰为 $\Psi'(u)$；定理9.2已支付的混合读取结论直接适用。这里的正泛函拉回与点值复合都是已知数学映射，不给未知 $D$ 增加任何自然性。

若所提常值数据实际作为定义1.2的完整 $\mathsf H_I(D)$ 实现，且实际供应该角内的同号旧值 $D(\widetilde c,x_I)=K_\sigma(\widetilde c,x_I)$ 以及输出 $D(\widetilde c,\widetilde t)=\widetilde g$，则 $\mathsf F$ §41.1 的必要性接线把原 $\operatorname{PB}(\widetilde c;x_I,\widetilde t)$ 与两份实际外层 P2 送到上述预算，产生矛盾。原评价准确决定锥所给数学正读取不要求把 $\Psi$ 宣告为实际准备。因此这些输出和角接口不能共同成为完整实现。前文3.1、5.2仍保留自身全部全 H／总响应前件；本证明不通过假定 $D$ 与 $\iota$、点值或压缩交换来取得矛盾。

一份实际非零常值截面已否定全探针全称，不需检验所有非常值截面。本定理没有验证它们的预算，也没有构造任何未知总 $D$。∎

### 10.9 几何简化、量子对应与仍须共同实现的来源

两间角内房间的刻度仍是一和二，第三间环境房间仍以两条非零边相连。零探针时，非零轴平移使两笔面积具有第9节的统一正余量，所以很小的固定误差能够藏在这幅图里。这里的简化是不用扫描全部探针，而让同一个三维向量同时实现两条相关的 Gram 接触线；三项 Hermitian 配对保证它们确由一块合法自伴探针实现。随后按同一误差加一份实对角修正，把一条实斜率线的面积始终钉在零；另一条线只有二次松弛，而原左端的残差失配准确是一阶量。有限界使这一次实际读取就严格失败。零探针遗漏的正是探针与两条完整标签之间的联合接触条件；两笔分别存在的余量没有支付这个共同条件。这说明零探针充分性的推断失效，不构成完整新量子公理或独立假设更少的结论。

在本节给定代数中，准确的通常／相反量子行对应仍为

$$
c\circ t-ig=\begin{cases}ct-is,&\sigma=1,\\tc-is,&\sigma=-1.\end{cases}
\tag{10.41}
$$

零残差时才得到标准行 $ct$ 或 $tc$；给定乘法、正锥和正读取并非从物理来源重构出来。已分类角的 $C^*$、Hilbert/GNS 与 Born 数学配对仍按9.6及 $\mathsf F$ §§36.1、40.2、41.5消费，循环向量平方范数保持原角质量。成熟的实／复 Gram、Cauchy–Schwarz、极化与二阶矩阵工具各在上述承重证明内使用，不另立已知定理作为新增结果；正泛函与表示背景保留 $\mathsf F$ §41.5 的 Blackadar《Operator Algebras》及 Hanche-Olsen–Størmer《Jordan Operator Algebras》归属。本节的双接触与残差比较不归为这些文献的既有定理，也不据此提出历史优先权或穷尽检索结论。

一般原模型仍须在同一实际输入上处理(9.37)的两份原缺陷

$$
\mathcal E_+^D=D(c-g,k)-K_\sigma(c-g,k),\quad
\mathcal E_-^D=D(c+g,-k)-K_\sigma(c+g,-k),\qquad
\mathcal E_+^D-\mathcal E_-^D=2cs.
\tag{10.42}
$$

本节只在(10.1)排除非零 $s$ 的固定输出预算，未普遍证明 $\mathcal E_+^D=\mathcal E_-^D$。任意环境耦合、一般混合整行与输入拼接、未覆盖相对标量、无限谱及完整奇数阶段 UHF 仍需各自原桥梁；全局标量单位行的既有结论不重开。增长分割还须 $N\omega(\varepsilon)^2\to0$，定性 $\omega(\varepsilon)\to0$ 和本节有限差额不给该速率。R5的全域几何必须保留自身的同域、非零交替双线性及全域关系入口，9.6所钉 §12 的 P/N 前件不变；全域 P/K 几何亦不能由这里一组三维读取代付。整个 $(M_3(\mathbb C))_{\rm sa}$ 不因这份构造成为三维 Pauli 域，也不推出 $\mathfrak{su}(3)$ 的三维叉积分类。

本节的物理来源谓词严格就是9.6所纳入的 $\mathsf F$ 定义41.4、40.1、36.1的同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$；沿

$$
41.4\Rightarrow40.1\Rightarrow36.1\Rightarrow32.3\Rightarrow\S27.1
\Rightarrow26.3\Rightarrow22.3\Rightarrow18.2
\Rightarrow\{10.2,15.2,\mathrm{AH}28.1,64.2,75.1\}
\Rightarrow\mathrm{SQ}47.1\text{--}47.13
$$

逐句、逐公式、逐量词合取每份定义、合同及其逐项递归纳入、逐层固定版本的全部上游全文。此链和下述说明不替代任何全文。AH 的 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`、W/CC/PT 的 `3b10aed60f60e4901bae6cf2e160bf439d642e64`、SQ 的 `dcaebc0b9ca5a3a463fd8cfd161d38967df28668` 与 `0aa11dbc3dc337d667b98900673e07d67b99bf46` 两层、OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`、AH22.1 的 `2addd6f369b7387226c2b0cc984623dd3efe40a1`、AH12.1 的 `39a0505470ea889dd9d4301ad60cd9506a5e8b58`、AH42.1 内的 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7` 及 R5 的 `aef46ce7497cf8ee6bef9bb7356a4483f3bfe6f0` 各守自身层级，不压平、不改钉。本卷6.1及1–8的旧钉版七合同另按自身全文保留，不在未证对应下将两套谓词认作相同。

同一原 $\Omega/\mathrm{native}$ 的对象、准备、事件、设备、程序、比较权、共同全词核、parent、ready、合法控制、旗标、中心、经典与不等维块、无轴对象、中间切口、模式网络、根、十一端点、配置、实际逆等距边、静默、零活动、终端及读器合同不被矩阵取代；网络 $D,C$ 不替换成本响应或数学正锥，未定义请求不补零。数学正读取不制造实际准备、相干控制、事件绑定的完整 Born 菜单或同一相关共同来源；张量仍需全部相关输入、忠实同向交换腿、共同生成、分离及重数。全局归一须严格正实际单位质量，角归一另须真实条件化和严格正角质量，零、不等、次归一及非正常质量保留。

typed CP、箭头下降、整台递归同源参考、真支持与支持内补、交织夹界、每个所需有限深度及每个正精度均守原前件。完整仪器、TP、Kraus、更新和 Lüders仍须完整 typed 菜单、单位分区、接受端、校准、表示与收敛，覆盖整个环境、所有成功／失败／细记录／port／post-port 输出及每份完整输出的每个仍合法未来；仅严格正实际输出质量可归一。合法顺序、自适应、并行历史、真分组遗忘、停止、拒绝、销毁、泄漏、同数两侧与逆向真实 Return、含活动 ready 和 producer 的完整 CountRead不因矩阵相等或当前读取相同而支付，原程序、历史、细记录、读取次序、比较权零集及未来权限不合并。正常性、指定前对偶、可数可加、无限菜单记录与收敛，以及实际保持原域的连续可逆流和实际逆、物理钟单位、酉实现、生成元域、Hamiltonian 能量、作用量及共同正物理 $\hbar$ 仍各由原来源承担。上述有限几何见证没有满足整个来源谓词，也没有完成一般全家族刚性或全局量子起源。

## 追加锚（本行以下为增补区）

## 11. 全正二表的准确阈值与双接触的扩大排除域

### 11.1 同一星形数据的全正二表阈值

**定义 11.1（固定数据、质量与接触差额）。** 本节的代数、角、乘法、正锥和数据始终准确取(9.1)，全部标签及预算取(9.2)–(9.3)。特别是 $t=t_0+\lambda c$、$g=K_\sigma(c,t)+\rho d$，两条非零环境边均保留。每个全称正读取量词仍遍历 $M_3(\mathbb C)$ 上全部数学正复线性泛函，质量为任意有限 $\phi(1_\star)\ge0$，不改为角质量。对一份实际探针和读取，记

$$
\mathscr V(x,\phi)=|\phi(L_x)|
-\sqrt{B_\phi(R_+,S_+)}-\sqrt{B_\phi(R_-,S_-)}.
\tag{11.1}
$$

$\mathscr V>0$ 才是该读取对原 PB 的严格违反。来源卷 $\mathsf F$ 仍是9.1所钉的[全 PB 多项式卷][AXF]，直接身份仍为 `2c1987c6ad3acbe4f9309ebde7bd204eacddd31a`；其(39.7)、41.1和42.2保持原版本和原量词。本节不指定未知总响应或外响应，不增加协变、响应缩放、单位平移中性、压缩自然性或新的 $D$ 前件。

**定理 11.2（全正 P2 的充要阈值）。** 对(9.1)的每个 $\lambda\in\mathbb R$ 和 $\sigma=\pm1$，有

$$
(\forall\phi\ge0)\ \mathsf{P2}(c,t_\lambda;g)
\quad\Longleftrightarrow\quad \rho^2\le\frac23.
\tag{11.2}
$$

端点 $\rho^2=2/3$、退化二表和零质量均包含在内。若 $\rho^2>2/3$，一份明确的完整三维读取为

$$
\zeta_\rho=(1,0,-i\sigma\rho/2)^{\mathsf T},\qquad
\phi_{\zeta_\rho}(A_1)=\zeta_\rho^*A_1\zeta_\rho,
\qquad \phi_{\zeta_\rho}(1_\star)=1+\rho^2/4.
\tag{11.3}
$$

证明。先证充分性。直接复用(9.9)–(9.12)的完整三维矩阵 $Q_{X+iY}$、右下正标量 $3$、其 Schur 补 $D_{X+iY}$ 和二表二次型对应。除了(9.11)的第一对角元及行列式外，第二对角元的配方是

$$
(D_{X+iY})_{22}
=\frac43X^2+\frac43\left(Y-\frac32\sigma\rho\right)^2+2-3\rho^2.
\tag{11.4}
$$

当 $\rho^2\le2/3$，两个对角元均非负，且(9.11)给

$$
\det D_{X+iY}
=\frac{16}{3}X^2+\left(\frac{16}{3}-8\rho^2\right)Y^2\ge0.
$$

故这个 Hermitian 二阶矩阵半正定，包括对角元为零的情形。由环境块 $3>0$ 的 Schur 合同，$Q_{X+iY}\succeq0$ 对每个实 $X,Y$ 成立。这里使用的是成熟的 Schur 补半正定判别，参见 Higham 的[原作者论述](https://nhigham.com/2023/06/01/what-is-the-schur-complement-of-a-matrix/)中正定性检验的半正定版本；不将该一般判别另立为本族的新定理。(9.12)的二次型对应于是给每份正 $\phi$ 的二表半正定，其行列式给 P2；(9.8)再保留同一 $g$ 地将结论传给每个 $\lambda$。整个步骤没有除以质量或 Gram 对角。

必要性由(11.3)直接给出。在同一完整向量上，已知乘法给

$$
\begin{gathered}
\phi_{\zeta_\rho}(c^2)=1,\qquad
\phi_{\zeta_\rho}(t_0^2)=1+\frac34\rho^2,\qquad
\phi_{\zeta_\rho}(c\circ t_0)=0,\\
\phi_{\zeta_\rho}(K_\sigma(c,t_0))=\frac\rho2,\qquad
\phi_{\zeta_\rho}(\rho d)=\rho.
\end{gathered}
\tag{11.5}
$$

因此由相同的剪切恒等式(9.8)，对所有 $\lambda$ 准确有

$$
B_{\phi_{\zeta_\rho}}(c,t_\lambda)
-\phi_{\zeta_\rho}(g)^2=1-\frac32\rho^2.
\tag{11.6}
$$

$\rho^2>2/3$ 时这是真实正读取的严格 P2 违反。零泛函的全部读数为零；充分性中也没有删去任何正质量、奇异密度或混合读取。此阈值是给定星形族的算子二表分类，不是一般协方差或一般 Schur 判别的改名。普通协方差背景仍按 Gibilisco–Hiai–Petz [arXiv:0712.1208v1](https://arxiv.org/abs/0712.1208v1)及 $\mathsf F$ §41.5 的既有归属；这些文献中的一般工具不承担(11.6)的本族结论。∎

### 11.2 不加小残差限制的同一接触构造

**定义 11.3（在扩大参数域上使用原有限公式）。** 取任意 $\lambda\rho\ne0$，置 $q=-\operatorname{sgn}(\lambda\rho)$。取(10.4)的同一个唯一实根 $p$，并严格按(10.5)–(10.6)定义 $b,u,C_j,m,Z,z,\tau,y,y_c,X,a$，这里不施加(10.1)的两个大小限制。所用实际探针和同一读取仍为

$$
\begin{gathered}
b=p+iq,\qquad
X=[\,y\ \ y_c\,][\,u\ \ c_0u\,]^{-1},\qquad
x=(X+\rho a)\oplus0,\qquad
\xi=\binom{u}{z},\qquad \phi_\xi(A_1)=\xi^*A_1\xi,\\
a=\operatorname{diag}\left(\frac1{p-1},\frac{-2}{p-2}\right).
\end{gathered}
\tag{11.7}
$$

先对 $\sigma=1$ 取这些公式；对 $\sigma=-1$ 取其逐项复共轭。§10.2的可定义性和§10.3的三个 Hermitian 配对只用实根关系、$q^2=1$ 及已写出的矩阵乘法，不用 $|\rho|\le1/4$ 或 $|\rho|\le|\lambda|$。故它们直接给 $X=X^*$ 及 $x\in(\mathcal Q_\star)_{\rm sa}$。§§10.4–10.5的完整标签恒等式也在此域原样适用；本定义不把定理10.2的估计结论延伸为前件。

**定理 11.4（比例区间上的实际非零探针排除）。** 对同一(9.1)数据，若

$$
\lambda\ne0,\qquad 0<|\rho|\le\frac{35}{3}|\lambda|,
\tag{11.8}
$$

则对每个 $\sigma=\pm1$，定义11.3给一个实际 $0\ne x=x^*\in\mathcal Q_\star$ 和一份共同的完整三维正读取，使

$$
\mathscr V(x,\phi_\xi)>
2\left(p^2-\frac{121}{16}\right)|\lambda\rho|>0.
\tag{11.9}
$$

不另要求 $|\rho|\le1/4$ 或 $\rho^2\le2/3$；若还要求全部正读取的 P2，则其准确附加范围由定理11.2给出。

证明。以下对 $\sigma=1$ 证明，另一符号最后由原共轭接线取得。先从同一个根提取所需的有理界。$H(-69/25)=-654/15625<0$，而 $H$ 的严格递增性及 $H(-11/4)>0$ 已在§10.2证明，故

$$
-\frac{69}{25}<p<-\frac{11}{4}.
\tag{11.10}
$$

沿用(10.7)的 $A_0,B_0,C_j$，局部另置实数

$$
\begin{gathered}
D_p=(p-1)(p-2),\qquad
\alpha=\frac{2(2p-3)}{D_p},\qquad
\beta=\frac{4-3p}{D_p},\qquad a=\alpha I_2+\beta c_0,\\
\eta=-\frac{2C_1+3(1-p)C_2}{4p},\qquad
\theta=\frac{(p+3)C_2}{2}.
\end{gathered}
\tag{11.11}
$$

其中 $\operatorname{Re}Z=-\lambda\eta$，$\operatorname{Im}Z=q\lambda(p-3)C_2/4$，由原(10.13)准确给出。根区间给

$$
\begin{gathered}
\alpha<0,\qquad |\alpha|<1,\qquad \frac23<\beta<1,\\
\frac{75}{8}<C_2<\frac{49}{5}<10,\qquad
\frac98<\theta<\frac54,\qquad
\frac{23}{2}<\eta<\frac{47}{4},\\
|u_1|^2<\frac{33}{4},\qquad |u_2|^2<\frac25,\qquad
|a_{11}|<\frac4{15},\qquad |a_{22}|<\frac37.
\end{gathered}
\tag{11.12}
$$

为明确这些界的依据，$A_0<(44/25)^2+1=2561/625$、$B_0<(19/25)^2+1=986/625$，而下端有 $A_0>65/16$、$B_0>25/16$，于是 $C_2=2A_0+B_0>155/16>75/8$；$6/25<p+3<1/4$ 再给 $\theta$ 的两界。$|\alpha|<1$ 等价于 $p^2+p-4>0$，$\beta<1$ 等价于 $p^2>2$，而 $\beta>2/3$ 等价于 $8-3p-2p^2>0$，均由(11.10)得到。对 $\eta$，展开 $C_1,C_2$ 后有

$$
\eta=\frac{9r_p^2-10r_p-9+40/r_p}{4},\qquad r_p=-p\in(11/4,69/25).
$$

右式关于 $r_p$ 的导数为 $(18r_p-10-40/r_p^2)/4>0$，故

$$
\frac{23}{2}<\frac{8115}{704}<\eta
<\frac{1001603}{86250}<\frac{47}{4}.
\tag{11.13}
$$

这也完成(11.12)中未直接由分母和坐标给出的界。

现在使用同一接触的联合量。严格沿(10.21)取 $R_0$ 为非实斜率那一对在 $\rho=0$ 的完整 $R$ 向量，取 $e=(au,0)^{\mathsf T}$，并记

$$
U=\|R_0\|^2,\qquad V_0=\operatorname{Re}(R_0^*e),\qquad
W_0=\|e\|^2,\qquad J=2|\lambda|(p^2-1).
\tag{11.14}
$$

另一对仍由(10.20)保持实斜率，其面积精确为零；这不是分别选择的两份最优读取。原(10.18)给 $|(R_0)_3|^2=1/2$。在前两坐标，(10.17)–(10.19)给

$$
(R_0)_{12}=y+q\frac{\tau-iy}{b}.
\tag{11.15}
$$

设 $n=u^*c_0y$。由(10.12)和(10.14)已经给出的 $u^*y=m$、$n=bm-i\tau_1$ 及 $2\operatorname{Re}(\bar bZ)=\lambda(C_1-pC_2)$，准确得到

$$
\begin{aligned}
u^*(R_0)_{12}&=\frac{pm+q\tau_0}{b}=q\bar Z,\\
(c_0u)^*(R_0)_{12}&=\frac{pn+q\tau_1}{b}=pm-i\tau_1,\\
\operatorname{Re}\{u^*(R_0)_{12}\}&=-q\lambda\eta,\\
\operatorname{Re}\{(c_0u)^*(R_0)_{12}\}&=-q\lambda\theta.
\end{aligned}
\tag{11.16}
$$

这里 $\tau_j$ 是原(10.12)的标量配对，不是向量 $\tau$ 的坐标。第一式的分子之所以等于 $qb\bar Z$，正是 $\lambda(C_1-pC_2)=\bar bZ+b\bar Z$；第二式用 $q-ip=-ib$。因 $c_0=\operatorname{diag}(1,2)$，同一两个坐标因此满足

$$
\begin{aligned}
\operatorname{Re}\{\bar u_1(R_0)_1\}&=q\lambda(-2\eta+\theta),\\
\operatorname{Re}\{\bar u_2(R_0)_2\}&=q\lambda(\eta-\theta).
\end{aligned}
\tag{11.17}
$$

这是对实际联合向量的坐标估计。由(11.12)，$2\eta-\theta>87/4$、$\eta-\theta>41/4$，故

$$
\begin{aligned}
\|(R_0)_{12}\|^2
&\ge\frac{\operatorname{Re}(\bar u_1(R_0)_1)^2}{|u_1|^2}
 +\frac{\operatorname{Re}(\bar u_2(R_0)_2)^2}{|u_2|^2}\\
&>\lambda^2\left(\frac{(87/4)^2}{33/4}
                +\frac{(41/4)^2}{2/5}\right)
>315\lambda^2,\qquad U>\frac12+315\lambda^2.
\end{aligned}
\tag{11.18}
$$

最后的两项分别大于 $57$ 与 $262$，故严格大于 $315$。另一方面，$a=\alpha I_2+\beta c_0$ 和(11.16)给出准确的混合配对

$$
V_0=q\lambda\widehat V,\qquad
\widehat V=-\alpha\eta-\beta\theta.
\tag{11.19}
$$

因 $0<-\alpha<1$、$2/3<\beta<1$，有

$$
-\frac54<\widehat V<\frac{47}{4}-\frac23\frac98=11,
\qquad |V_0|<11|\lambda|.
\tag{11.20}
$$

修正向量的完整平方范数则满足

$$
0<W_0=|a_{11}u_1|^2+|a_{22}u_2|^2
<\frac{33}{4}\left(\frac4{15}\right)^2
 +\frac25\left(\frac37\right)^2
=\frac{44}{75}+\frac{18}{245}<\frac23.
\tag{11.21}
$$

这些三个界均来自同一 $R_0,e,\xi$，没有代换环境坐标，也没有将不同参数的最优值拼接。

置 $r_0=|\rho|$。由(11.8)、(11.18)、(11.20)，

$$
r_0|V_0|<\frac{385}{3}\lambda^2<\frac{11}{27}U,
\qquad U+\rho V_0>\frac{16}{27}U.
\tag{11.22}
$$

直接复用(10.22)–(10.25)和(10.30)的完整标签及 $\mathsf F$(39.7)残差恒等式，令 $(R,S)$ 表示非实斜率那一对，便有

$$
\begin{gathered}
Q=\phi_\xi(K_1(R,S))=-2(U+\rho V_0)<0,
\qquad |Q|>\frac{32}{27}U,\\
\Delta=4r_0^2\{UW_0-|R_0^*e|^2\}\le4r_0^2UW_0,\\
B_{\phi_\xi}(R,S)=Q^2+\Delta,\qquad
\phi_\xi(L_x)=q(Q-r_0J).
\end{gathered}
\tag{11.23}
$$

复 Gram 行列式及实、虚部平方分解仍是§10.5使用的成熟工具，归属沿§10.9及 $\mathsf F$ §41.5；新估计是(11.18)–(11.22)对这份实际接触的同时控制。$U\ge1/2$ 保证下式没有零分母。全部有限面积亏量满足

$$
\sqrt{Q^2+\Delta}-|Q|
=\frac{\Delta}{\sqrt{Q^2+\Delta}+|Q|}
\le\frac{4r_0^2UW_0}{2|Q|}
<\frac98r_0^2.
\tag{11.24}
$$

另一对面积精确为零，而 $Q<0$ 给 $|\phi_\xi(L_x)|=|Q|+r_0J$，所以

$$
\begin{aligned}
\mathscr V(x,\phi_\xi)
&>2(p^2-1)r_0|\lambda|-\frac98r_0^2\\
&\ge\left(2(p^2-1)-\frac{105}{8}\right)r_0|\lambda|
=2\left(p^2-\frac{121}{16}\right)|\lambda\rho|>0.
\end{aligned}
\tag{11.25}
$$

严格正性用 $p<-11/4$；特别是(11.8)的闭端点仍严格违反。这是一份有限探针的差额，不是渐近探针或忽略高阶项所得的符号。

还须在扩大范围证明 $x\ne0$。原(10.12)–(10.16)给

$$
\begin{aligned}
\operatorname{Im}(u^*c_0Xu)
&=\operatorname{Im}n=-2\lambda C_2-2\operatorname{Re}Z\\
&=-\frac{\lambda\{2C_1+(p+3)C_2\}}{2p}
=-\frac{\lambda(C_1+C_3)}{2p}\ne0.
\end{aligned}
\tag{11.26}
$$

最后一步使用(10.8)及 $C_1,C_3>0$。$a$ 与 $c_0$ 交换且自伴，故 $u^*ac_0u\in\mathbb R$；于是 $X+\rho a=0$ 将与(11.26)矛盾。这证明每个 $\lambda\ne0$、任意 $\rho$ 的该探针均非零，不再借助小残差三角界。

$u_1u_2\ne0$，而 $\operatorname{Re}Z=-\lambda\eta\ne0$ 给 $z\ne0$，故这份读取的三个坐标均非零。$\phi_\xi$ 的完整质量仍为 $\|u\|^2+|z|^2>0$，且两个面积、左端和全部配对始终使用这一份读取。任意正倍数的该泛函把严格差额和质量同时乘以同一常数，故也可给出任意指定的有限正总质量；零泛函的预算则两边均为零。对 $\sigma=-1$，直接使用§10.6的逐项复共轭：同一 $c,t,d,\lambda,\rho$ 不变，全部自伴标签的实读取、面积和质量不变。这给两种符号的(11.9)。∎

### 11.3 固定非零残差靠近零平移时，这一接触确有缺口

**命题 11.5（原接触在零平移附近的严格正向预算）。** 固定任意实 $\rho\ne0$。定义11.3的同一探针和读取存在明确的 $\varepsilon_\rho>0$，使对每个 $0<|\lambda|<\varepsilon_\rho$ 及每个 $\sigma$，有

$$
x\ne0,\qquad \mathscr V(x,\phi_\xi)<0.
\tag{11.27}
$$

这里只断言这一探针在这一读取上满足严格的原 PB 方向，不断言它在所有读取上成立，更不认证全部探针。该接触差额还有准确的单侧共同极限

$$
\lim_{\lambda\to0,\ \lambda\ne0}\mathscr V(x,\phi_\xi)
=1-\sqrt{1+2\rho^2W_0}<0,
\tag{11.28}
$$

其中 $W_0$ 对 $q=1,-1$ 相同。

证明。先对 $\sigma=1$。对任一固定 $q$，(10.5)中的 $Z,z,\tau,y,y_c,X$ 都准确线性于 $\lambda$，而 $u,a,e$ 与 $\lambda$ 无关。因此可写

$$
(R_0)_{12}=\lambda\widehat R_q,\qquad
U=\frac12+\lambda^2\|\widehat R_q\|^2,\qquad
V_0=q\lambda\widehat V.
\tag{11.29}
$$

这里 $\widehat R_q$ 是将同一有限公式取 $\lambda=1$ 所得的前两坐标。$u_{-q}=\bar u_q$、$a$ 为实矩阵，所以 $W_0=\|au_q\|^2$ 与 $q$ 无关且严格正。$R_0^*e=\lambda\widehat R_q^*(au_q)$，故由前两坐标的复 Cauchy–Schwarz，准确有

$$
\begin{aligned}
\Delta
&=2\rho^2W_0
 +4\rho^2\lambda^2\left\{\|\widehat R_q\|^2W_0
             -|\widehat R_q^*(au_q)|^2\right\}
\ge2\rho^2W_0>0.
\end{aligned}
\tag{11.30}
$$

为了给出有限邻域而非只报极限，令

$$
\begin{gathered}
r_0=|\rho|,\qquad j_p=2(p^2-1)>0,\qquad
\widehat U=\max\{\|\widehat R_1\|^2,\|\widehat R_{-1}\|^2\},\\
M_\rho=1+2\widehat U+22r_0,\qquad
\varepsilon_\rho=\min\left\{1,\frac{r_0W_0}{4j_pM_\rho},
                                  \frac{\sqrt{W_0}}{2j_p}\right\}>0.
\end{gathered}
\tag{11.31}
$$

这些只是同一两支显式矩阵公式的共同上界，不替换任何实际读取。当 $0<\ell=|\lambda|<\varepsilon_\rho$，由(11.20)、(11.29)及 $J=j_p\ell$ 得

$$
|Q|=2|U+\rho V_0|\le M_\rho,\qquad
2|Q|r_0J+r_0^2J^2<\frac12r_0^2W_0+\frac14r_0^2W_0<\Delta.
\tag{11.32}
$$

因此

$$
\sqrt{Q^2+\Delta}>|Q|+r_0J\ge|Q-r_0J|
=|\phi_\xi(L_x)|.
\tag{11.33}
$$

另一对面积仍精确为零，故(11.27)的差额为负；实际非零性由(11.26)保证。另一方面，(11.29)–(11.30)给 $Q\to-1$、$J\to0$、$\Delta\to2\rho^2W_0$，两支均得(11.28)。也可把同一有限公式延到 $\lambda=0$ 并任选 $q=\pm1$：此时 $X=z=0$、$x=(\rho a)\oplus0\ne0$、$\xi=(u,0)^{\mathsf T}$，其实际差额就等于(11.28)右端。对 $\sigma=-1$ 仍用同一逐项复共轭。

这里只对明确已知的矩阵及其标量读取作代数比较；没有对未知 $D$ 取输入极限，也不由不同 $\lambda$ 之间运输 PB。$\lambda=0$ 的同一非零残差仍被 $\mathsf F$ 定理42.2的另一份零探针读取排除。因此原接触的严格正向预算与零平移刚性相容，不能据此判定任何数据通过全部 PB。∎

### 11.4 原全族推断所剩的准确参数包络

**推论 11.6（全部预算的必要残余域）。** 在(9.1)中，同时满足(9.38)前件的非零 $\rho$，若存在，只能位于

$$
\boxed{\quad
0<|\lambda|<\frac3{35}\sqrt{\frac23},\qquad
\frac{35}{3}|\lambda|<|\rho|\le\sqrt{\frac23}.
\quad}
\tag{11.34}
$$

故对 $\lambda=0$ 或 $|\lambda|\ge(3/35)\sqrt{2/3}$，原(9.38)的结论 $\rho=0$ 成立。零残差对任意 $\lambda$ 满足全部正读取的 P2 和每个原角探针的 PB。对(11.34)内的点，本节没有判定其全部预算成立或失败；它们仍须同时满足原 $\mathsf{PB}_0$ 与每个实际非零自伴角探针的全部正读取预算。

证明。$\rho^2>2/3$ 由定理11.2的一份实际 P2 违反排除。$\lambda=0$、$\rho\ne0$ 由 $\mathsf F$ 定理42.2排除，保留其原零探针而不重证该结论。$\lambda\ne0$ 且 $0<|\rho|\le(35/3)|\lambda|$ 由定理11.4的实际非零探针排除。余下的必要条件正是(11.34)，不把此包络中的点宣告为可行。$\rho=0$ 时，复 Cauchy–Schwarz及 $\mathsf F$(39.7)对同一已知乘法直接给 P2 和全部原 PB，包含零、退化及任意质量，沿§10.7的既有逆向结论复用。

定理11.4覆盖的(11.8)严格扩大(10.1)，例如 $\lambda=\rho=1/2$ 的同一数据按定理11.2满足全部正读取的 P2，却被(11.7)排除；原(10.1)没有覆盖它。新增推断是同一接触的联合配对与有限亏量控制，不是 Hermitian 实现、一般 Gram 恒等式、零残差标准 PB 或零平移刚性的再次证明。这里不作历史优先权或穷尽文献的主张。

对区间上的常值数据，可直接使用(9.33)–(9.36)及§10.8已经给定的同一个含单位常值嵌入与点值读取：把(11.7)的非零矩阵放成非零常值角截面，乘积、全部标签、完整质量及(11.9)的严格差额均原样保持。P2 在 $\rho^2\le2/3$ 时对任意正 $\Psi$ 由 $\Psi\circ\iota$ 和定理11.2取得；PB 的违反读取仍是 $\phi_\xi\circ\operatorname{ev}_{s_0}$。这不要求未知 $D$ 与嵌入、点值或压缩交换；如欲接回完整 $\mathsf H_I(D)$，仍须实际供应§10.8所列的同号角旧值、同一输出及 $\mathsf F$ §41.1的原必要性接线。∎

**定义 11.7（保持原强度的一般原域问题与来源）。** (11.34)中的固定输出全族问题仍准确取(9.38)，不是在其前件中增加(11.8)。一般原域的两份混合输入缺陷仍为(9.37)、(10.42)的同一对象

$$
\begin{gathered}
\mathcal E_+^D=D(c-g,k)-K_\sigma(c-g,k),\qquad
\mathcal E_-^D=D(c+g,-k)-K_\sigma(c+g,-k),\\
\mathcal E_+^D-\mathcal E_-^D=2cs.
\end{gathered}
\tag{11.35}
$$

在一般共同实现上取得 $\mathcal E_+^D=\mathcal E_-^D$ 仍是原未付义务，不以定理11.4的一族固定矩阵替代。增长谱分割仍须原联合速率 $N\omega(\varepsilon)^2\to0$，定性 $\omega(\varepsilon)\to0$ 及本节有限差额不给这个速率。一般环境连线、混合整行、输入拼接、相对标量、无限谱与完整奇数阶段 UHF 均保留§§9.6、10.9的原适用范围；已有全 H 分类保持自身的总响应与全域前件。

物理接回所指的谓词仍严格是§§9.6、10.9所固定的同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$，即 $\mathsf F$ 定义41.4、40.1、36.1及其递归上游全文的逐子句合取，保留每个原量词和每层既定版本；本卷6.1及1–8的七合同亦各守自身全文，不将不同钉版谓词认作相同。原 $\Omega/\mathrm{native}$ 的对象、准备、事件、比较权、共同来源与全词核、全部静态和静默分支、完整 typed 菜单及整台仪器的每份输出和合法未来、真实 Return、完整 CountRead，以及原正常性、前对偶、无限记录与收敛、物理钟、实际可逆动力学和共同正物理作用量，仍逐项取这些已纳入的原定义与前件。这些全文不由本段的列名替代。数学正读取不自动成为实际准备，给定矩阵乘法不成为物理来源证明，有限接口中的预算排除也不构成完整 H、未知总 $D$ 或物理反模型。

## 追加锚（本行以下为增补区）

## 12. 固定幅度零探针读取与原星形全族刚性

### 12.1 原矩阵、原质量与一份共同读取

**定义 12.1（互补比例域的有限读取）。** 始终取定义9.1的同一 $\mathcal A_\star=M_3(\mathbb C)$、$P_\star$、$c,d,t_0,t=t_0+\lambda c$、$g=g_0+\rho d$ 及 $g_0=K_\sigma(c,t_0)$，全部预算和标签严格取(9.2)–(9.3)。全称正读取仍是原代数上的全部数学正复线性泛函，质量仍为任意有限 $\phi(I_3)\ge0$。来源 $\mathsf F$ 严格取[全 PB 多项式卷][AXF]的提交 `2c1987c6ad3acbe4f9309ebde7bd204eacddd31a`。其定理42.2、式(39.7)，以及本卷定理11.2、11.4和命题11.5均按原陈述复用。

当 $\lambda\rho\ne0$，置

$$
\begin{gathered}
a=|\lambda|,\qquad b=|\rho|,\qquad
\eta=\operatorname{sgn}(\lambda\rho),\qquad
\alpha=\frac{\sqrt2}{18},\qquad \beta=\frac{4\sqrt2}{27},\\
u=\frac13(2\sqrt2,-1,0)^{\mathsf T},\qquad
e=\frac13(1,2\sqrt2,0)^{\mathsf T},\qquad f=(0,0,1)^{\mathsf T},\\
x=0,\qquad \xi=u+\eta(i\sigma\alpha e+\beta\rho f),\qquad
\phi_\xi(A)=\xi^*A\xi.
\end{gathered}
\tag{12.1}
$$

这里 $u,e,f$ 是 $\mathsf F$(42.5)中原来的实正交单位向量；$x$ 是原角内的实际零探针。$\phi_\xi$ 是整个 $M_3(\mathbb C)$ 上的正复线性泛函，且

$$
\phi_\xi(I_3)=\|\xi\|^2
=1+\frac1{162}+\frac{32\rho^2}{729}.
\tag{12.2}
$$

不归一化，不换成角质量。原基坐标中的 $t_0$ 及 $g_0$ 的两条环境边保留；以下用 $(u,e,f)$ 记录矩阵乘法，只是对同一三维数据换正交坐标。

### 12.2 一份零探针读取的严格排除

**定理 12.2（互补比例域的原零预算违反）。** 对(9.1)的任意 $\sigma=\pm1$ 和实参数

$$
\rho\ne0,\qquad 0<|\lambda|\le\frac{|\rho|}{10},
\tag{12.3}
$$

定义12.1的单一有限读取严格违反原 $\mathsf{PB}_0$。具体地，保持原标签

$$
R_+=-k,\quad R_-=k,\quad S_+=t+g,\quad S_-=t-g,
\quad L_0=-(tg+gt),\qquad k=c\circ t,
\tag{12.4}
$$

并记 $B_\pm=B_{\phi_\xi}(R_\pm,S_\pm)$，则

$$
|\phi_\xi(L_0)|^2-(\sqrt{B_+}+\sqrt{B_-})^2
>
\frac4{15}\left(\frac{1735}{59049}b^2+\frac{38}{75}b^4\right)>0.
\tag{12.5}
$$

不要求 $\mathsf{P2}$，也不限制 $b$ 的大小；全部比较量同时来自(12.1)的同一个 $x,\xi,c,t,g$。

证明。先列出同一实现中的乘法。以下矩阵均在有序正交基 $(u,e,f)$ 中书写：

$$
\begin{gathered}
c=\begin{pmatrix}
10/9&-2\sqrt2/9&0\\-2\sqrt2/9&17/9&0\\0&0&0
\end{pmatrix},\qquad
c^2=\begin{pmatrix}
4/3&-2\sqrt2/3&0\\-2\sqrt2/3&11/3&0\\0&0&0
\end{pmatrix},\\
d=\begin{pmatrix}
2/3&2\sqrt2/3&0\\2\sqrt2/3&-5/3&0\\0&0&0
\end{pmatrix},\qquad
t_0=\begin{pmatrix}
0&0&\sqrt2/3\\0&0&5/3\\\sqrt2/3&5/3&0
\end{pmatrix},\\
k_0=c\circ t_0=\begin{pmatrix}
0&0&0\\0&0&3/2\\0&3/2&0
\end{pmatrix},\qquad
g_0=i\sigma\begin{pmatrix}
0&0&0\\0&0&3/2\\0&-3/2&0
\end{pmatrix}.
\end{gathered}
\tag{12.6}
$$

由 $k=k_0+\lambda c^2$、$t=t_0+\lambda c$、$g=g_0+\rho d$ 作用在坐标列 $(1,i\sigma\eta\alpha,\eta\beta\rho)^{\mathsf T}$ 上，逐项得到

$$
\begin{aligned}
U=k\xi&=\begin{pmatrix}
4\lambda/3-i\sigma\eta\,2\lambda/27\\
\sqrt2(-2\lambda/3+2\eta\rho/9)+i\sigma\eta\,11\sqrt2\lambda/54\\
i\sigma\eta\,\sqrt2/12
\end{pmatrix},\\
T=t\xi&=\begin{pmatrix}
10\lambda/9+8\eta\rho/81-i\sigma\eta\,2\lambda/81\\
\sqrt2(-2\lambda/9+20\eta\rho/81)+i\sigma\eta\,17\sqrt2\lambda/162\\
\sqrt2/3+i\sigma\eta\,5\sqrt2/54
\end{pmatrix},\\
G=g\xi&=\begin{pmatrix}
2\rho/3+i\sigma\eta\,2\rho/27\\
2\sqrt2\rho/3+i\sigma\eta\,7\sqrt2\rho/54\\
\eta\sqrt2/12
\end{pmatrix}.
\end{aligned}
\tag{12.7}
$$

这同时核对 $\sigma$ 的两个取值，无需将原标签改号。置

$$
\begin{gathered}
n=\|U\|^2,\quad m=\|T\|^2+\|G\|^2,\quad
p=\operatorname{Re}(U^*T),\quad
q=\eta\operatorname{Re}(U^*G),\quad
r=\eta\operatorname{Re}(T^*G).
\end{gathered}
\tag{12.8}
$$

由 $\eta\lambda\rho=ab$，(12.7)给下列准确标量：

$$
\begin{aligned}
n&=\frac1{72}+\frac{1339}{486}a^2-\frac{16}{27}ab+\frac8{81}b^2,\\
m&=\frac{1477}{5832}+\frac{659}{486}a^2+\frac{731}{486}b^2,\\
p&=\frac5{324}+\frac{2657}{1458}a^2-\frac8{27}ab+\frac{80}{729}b^2,\\
q&=\frac{23}{486}ab+\frac8{27}b^2,\\
r&=\frac1{18}+\frac{685}{1458}ab+\frac{32}{81}b^2>0.
\end{aligned}
\tag{12.9}
$$

例如 $n$ 中 $\lambda^2$ 的系数由 $1300/729+8/9+121/1458=1339/486$ 给出，交叉项为 $-16\eta\lambda\rho/27$。对 $m$，两项范数分别为

$$
\|T\|^2=\frac{349}{1458}+\frac{659}{486}\lambda^2+\frac{32}{243}\rho^2,
\qquad
\|G\|^2=\frac1{72}+\frac{667}{486}\rho^2.
\tag{12.10}
$$

其中 $\|T\|^2$ 的 $\eta\lambda\rho$ 项相消。其余三个实内积在原实参数中依次为

$$
\begin{aligned}
\operatorname{Re}(U^*T)
&=\frac5{324}+\frac{2657}{1458}\lambda^2
 -\frac8{27}\eta\lambda\rho+\frac{80}{729}\rho^2,\\
\operatorname{Re}(U^*G)
&=\frac{23}{486}\lambda\rho+\frac8{27}\eta\rho^2,\\
\operatorname{Re}(T^*G)
&=\frac\eta{18}+\frac{685}{1458}\lambda\rho+\frac{32}{81}\eta\rho^2.
\end{aligned}
\tag{12.11}
$$

因此表(12.9)中的每一项都取自相同三向量，而非分别优化的读取。

令

$$
H=nm-p^2-q^2,\qquad J=2(nr-pq).
\tag{12.12}
$$

原实 Gram 定义及(12.4)给

$$
\begin{aligned}
B_+&=n(m+2\eta r)-(p+\eta q)^2=H+\eta J,\\
B_-&=n(m-2\eta r)-(p-\eta q)^2=H-\eta J,\\
\phi_\xi(L_0)&=-2\operatorname{Re}(T^*G)=-2\eta r,
\qquad |\phi_\xi(L_0)|=2r.
\end{aligned}
\tag{12.13}
$$

两份 $B_\pm$ 均是原正泛函的 Gram 行列式，故非负。仅为估计而记 $B_\eta=H+J$、$B_{-\eta}=H-J$：$\eta=1$ 时它们依次是原 $B_+,B_-$，$\eta=-1$ 时依次是原 $B_-,B_+$。对这两个非负数用标量 Cauchy–Schwarz，明确取向量 $(\sqrt5,\sqrt3)$ 与 $(\sqrt{B_\eta/5},\sqrt{B_{-\eta}/3})$，得

$$
\begin{aligned}
(\sqrt{B_+}+\sqrt{B_-})^2
&\le8\left(\frac{B_\eta}{5}+\frac{B_{-\eta}}3\right)\\
&=\frac85(H+J)+\frac83(H-J)
=\frac{16}{15}(4H-J).
\end{aligned}
\tag{12.14}
$$

这只是原两笔面积之和的上估计，未改变任一原预算。故

$$
\begin{gathered}
|\phi_\xi(L_0)|^2-(\sqrt{B_+}+\sqrt{B_-})^2\ge\frac4{15}E,\\
E=15r^2-16nm+16p^2+16q^2+8nr-8pq.
\end{gathered}
\tag{12.15}
$$

现在证明 $E$ 在整个(12.3)严格为正。设 $z=a/b$，故 $0<z\le1/10$，并定义

$$
\begin{aligned}
n_z&=\frac{1339}{486}z^2-\frac{16}{27}z+\frac8{81},&
m_z&=\frac{659}{486}z^2+\frac{731}{486},\\
p_z&=\frac{2657}{1458}z^2-\frac8{27}z+\frac{80}{729},&
q_z&=\frac{23}{486}z+\frac8{27},\\
r_z&=\frac{685}{1458}z+\frac{32}{81}.
\end{aligned}
\tag{12.16}
$$

则 $(n,m,p,q,r)=(1/72,1477/5832,5/324,0,1/18)+b^2(n_z,m_z,p_z,q_z,r_z)$。在(12.15)内按 $b^2$ 收集，常数项为

$$
\frac5{108}-\frac{1477}{26244}+\frac{100}{26244}+\frac1{162}=0,
\tag{12.17}
$$

而 $b^2$ 的系数为

$$
\begin{aligned}
C(z)&=\frac{16}{9}r_z-\frac{2630}{729}n_z
      +\frac{40}{81}p_z-\frac{10}{81}q_z-\frac29m_z\\
&=\frac{-1654744z^2+499725z+5205}{177147}.
\end{aligned}
\tag{12.18}
$$

为核对整系数，后一分子的五项按前一行次序恰为

$$
\begin{aligned}
&216(685z+576)-1315(1339z^2-288z+48)\\
&\qquad+60(2657z^2-432z+160)-45(23z+144)-81(659z^2+731).
\end{aligned}
\tag{12.19}
$$

因此有完整分解

$$
\begin{gathered}
E=b^2C(z)+b^4F(z),\\
F(z)=15r_z^2-16n_zm_z+16p_z^2+16q_z^2+8n_zr_z-8p_zq_z.
\end{gathered}
\tag{12.20}
$$

由 $z^2\le z/10$ 及 $499725>1654744/10$，得到

$$
C(z)\ge\frac{5205}{177147}=\frac{1735}{59049}>0.
\tag{12.21}
$$

还须控制可能乘上任意大 $b^4$ 的系数，不能只用一次项的正性。在闭区间 $0\le z\le1/10$，(12.16)逐项给

$$
\begin{gathered}
\frac{16}{405}\le n_z\le\frac8{81}<\frac1{10},\qquad
0<m_z\le\frac{73759}{48600}<\frac85,\\
\frac{292}{3645}\le p_z\le\frac{80}{729}<\frac18,\qquad
\frac8{27}\le q_z\le\frac{1463}{4860}<\frac13,\qquad
r_z\ge\frac{32}{81}>\frac38.
\end{gathered}
\tag{12.22}
$$

这里 $n_z\ge8/81-(16/27)(1/10)=16/405$，而
$n_z-8/81=z(1339z-288)/486\le0$；同样
$p_z\ge80/729-(8/27)(1/10)=292/3645$，且
$p_z-80/729=z(2657z-432)/1458\le0$。$m_z,q_z,r_z$ 的界直接由其非负系数取得。于是 $16p_z^2$ 和 $8n_zr_z$ 非负，可以在下估计中舍去；其余乘积的符号也已确定。因此

$$
\begin{aligned}
F(z)
&>15\left(\frac38\right)^2+16\left(\frac8{27}\right)^2
  -16\left(\frac1{10}\right)\left(\frac85\right)
  -8\left(\frac18\right)\left(\frac13\right)\\
&>2+\frac75-\frac{64}{25}-\frac13=\frac{38}{75}>0.
\end{aligned}
\tag{12.23}
$$

第二个严格号用 $135/64>2$ 及 $1024/729>7/5$。结合(12.20)–(12.23)及 $b>0$，得

$$
E>\frac{1735}{59049}b^2+\frac{38}{75}b^4>0.
\tag{12.24}
$$

这与(12.15)给出(12.5)。原左端绝对值与两面积根的和均有限且非负，故严格的平方差确实推出 $\mathscr V(0,\phi_\xi)>0$，即原预算失败。证明没有取极限、改变响应或将不同实现的最优值拼接。∎

### 12.3 原全部探针的参数完备结论

**定理 12.3（原固定星形的全族充要条件）。** 对准确的(9.1)–(9.3)，任意 $\lambda,\rho\in\mathbb R$ 及 $\sigma=\pm1$，以下三项等价：

$$
\begin{aligned}
&\rho=0;\\
&(\forall x=x^*\in\mathcal Q_\star)(\forall\phi\ge0)\quad\mathsf{PB}_x;\\
&(\forall\phi\ge0)\quad\mathsf{P2}
\quad\land\quad
(\forall x=x^*\in\mathcal Q_\star)(\forall\phi\ge0)\quad\mathsf{PB}_x.
\end{aligned}
\tag{12.25}
$$

每个 $\phi$ 量化整个原代数上全部正复线性泛函及其原有限质量，包括零；$x=0$、退化和任意幅度的原自伴角探针均保留。特别是原(9.38)成立，且(11.34)内没有满足全部原 PB 的非零残差。排除方向无需 P2。

证明。先排除每个 $\rho\ne0$。若 $\lambda=0$，直接调用既定版本 $\mathsf F$ 定理42.2的实际零探针与有限正读取；该结论本来就不要求 P2。若 $\lambda\ne0$，置 $a=|\lambda|>0,b=|\rho|>0$，作穷尽分支：

$$
\begin{cases}
0<b\le(35/3)a:&\text{直接调用定理11.4的实际非零探针与同一读取；}\\
b>(35/3)a:&0<a<(3/35)b<b/10,\quad\text{应用定理12.2。}
\end{cases}
\tag{12.26}
$$

其中 $3/35<1/10$ 等价于 $30<35$。边界 $b=(35/3)a$ 包含在第一分支；定理12.2也包含其自身边界 $a=b/10$。两个已证排除域重叠于 $10a\le b\le(35/3)a$，没有遗漏的非零参数。每个分支都在各自那份固定 $\lambda,\rho,\sigma,c,t,g$ 中给实际失败的 $x,\phi$，不是沿参数变动运输预算。

当 $\rho=0$，直接复用§10.7和推论11.6的逆向结论：$\mathsf F$(39.7)的标准乘法恒等式和复 Cauchy–Schwarz对每个 $\lambda$、全部原 $x$ 及全部正 $\phi$ 给 P2 与 PB。此处不重证标准零残差预算，也不从单一向量读取提升一个新全称断言。原证明不除以质量或 Gram 对角，故零质量、退化及任意有限质量都在原范围内。三项的其余蕴涵由合取投影给出。∎

定理11.2的准确 P2 阈值 $\rho^2\le2/3$ 保持不变；定理12.3判定的是它与全部 PB 的交，而不是重写 P2 阈值。定理9.2的非零平移零探针余量仍只取其原有 $|\rho|\le\varepsilon_\lambda$ 的范围；它没有认证全部原探针。命题11.5仍只断言指定接触在指定读取上的严格正向预算。一个指定读取通过不蕴含同一探针在全部读取通过，更不蕴含全部 PB；(12.26)只需要给出一份实际违反的读取。

**命题 12.4（必要包络内的一份明确消费者）。** 取原固定数据

$$
\lambda=\frac1{100},\qquad \rho=\frac12,\qquad \sigma=\pm1.
\tag{12.27}
$$

它满足定理11.2的全正 P2，严格位于(11.34)的必要包络内部，却被原零探针及下列同一读取排除：

$$
x=0,\qquad
\xi=u+i\sigma\frac{\sqrt2}{18}e+\frac{2\sqrt2}{27}f,
\qquad \phi_\xi(I_3)=\frac{1483}{1458}.
\tag{12.28}
$$

证明。$\rho^2=1/4<2/3$，直接用定理11.2；$35|\lambda|/3=7/60<1/2<\sqrt{2/3}$，且 $1/100<(3/35)\sqrt{2/3}$，所以(11.34)的两个严格不等式均满足。又 $a/b=1/50<1/10$，(12.1)和(12.2)恰为(12.28)，质量为 $1+1/162+8/729=1483/1458$。定理12.2给这份读取的严格失败。∎

### 12.4 固定接口与一般原域的严格范围

**约定 12.5（一般原关系及来源仍取原全文）。** 定理12.3的量词只覆盖定义9.1固定星形的全部实参数及(9.3)的全部原角探针和数学正读取。它没有把一般环境矩阵改为这份星形，也没有构造未知总映射 $D$。特别是这里非空的一维环境块仍为 $0$；要求环境块可逆的分类不用于此处。

一般原域仍严格保留(9.37)、(10.42)和定义11.7中的同一两份混合输入缺陷及其已付差额：

$$
\begin{gathered}
\mathcal E_+^D=D(c-g,k)-K_\sigma(c-g,k),\qquad
\mathcal E_-^D=D(c+g,-k)-K_\sigma(c+g,-k),\\
\mathcal E_+^D-\mathcal E_-^D=2cs,\qquad
\mathcal E_+^D=\mathcal E_-^D\quad\text{在一般共同实现上仍须证明。}
\end{gathered}
\tag{12.29}
$$

固定星形全族的排除不推出这个一般等式。增长谱分割仍须原联合速率 $N\omega(\varepsilon)^2\to0$；定性 $\omega(\varepsilon)\to0$ 与(12.5)的固定有限差额不给该速率。完整 H、总 $D$、混合整行、相对标量、任意输入拼接、无限谱和完整奇数阶段 UHF 均保持§§9.6、10.9及定义11.7的原前件和未解范围；没有新增 $D$ 的连续、可测、可加、齐次、协变、单位平移或压缩前件。

物理来源仍准确是§§9.6、10.9及定义11.7的同一 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$：按 $\mathsf F$ 定义41.4、40.1、36.1及其递归纳入的上游全文逐子句合取，每层固定版本、每个原量词和共同实现条件原样保留。本卷定义6.1和§§1–8的七合同也各守其全文及自身版本，不认作另一个较短谓词，不由此处的交叉引用缩短。原准备、事件、比较权、共同来源与全词核，静态和静默分支，完整 typed 菜单、整台仪器的每份输出及每个合法未来，真实 Return、完整 CountRead，以及正常性、前对偶、无限记录、收敛、物理钟、实际可逆动力学和共同正物理作用量，均按上述原定义与原前件承担。数学正泛函仍不自动是实际准备，有限矩阵乘法仍不自动是物理来源实现。

本节使用的实 Gram 与加权标量 Cauchy–Schwarz 是成熟工具；正泛函与算子代数背景沿 $\mathsf F$ §41.5所引 Blackadar《Operator Algebras》和 Hanche-Olsen–Størmer《Jordan Operator Algebras》。本节新增的是同一有限读取的联合标量关系(12.9)、严格估计(12.5)及其补全原固定星形参数族的推论，属本库推导，不将一般 Gram 工具或已供给的零残差、零平移结论计为新内容，不作历史优先权或穷尽文献主张。这里给出普通数学证明，不作 Lean/kernel 形式验证断言；固定接口结论不成为完整 H、总 $D$ 或递归物理来源的实现证明。

## 追加锚（本行以下为增补区）

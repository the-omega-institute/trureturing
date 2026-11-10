# 原生 Fourier–beta 获取与完整自身边缘返回

## 1. 原始控制类与完整构造

**定义 1.1（精确原曲线及实际端口）。** 使用 [OTF004 定义 19.1](OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md) 的原始合同。对正有理数 $0<e\le1/100$，令

$$
\begin{aligned}
u_e&=e/8,&
k_e&=\left\lceil2048e^{-2}\log(18/e)\right\rceil,&
\ell_e&=\left\lceil32768e^{-4}\log(90/e)\right\rceil,\\
N_*&=8{,}388{,}608{,}000,&
N_e&=\max\left\{N_*,\left\lceil\frac{3k_e+2}{10}\right\rceil,
\left\lceil\frac{15\ell_e+1}{18}\right\rceil\right\},\\
D_e&=\left\lceil\max\{8{,}000{,}000N_e^2,9k_e/e\}\right\rceil,&
m_e&=D_e-1,& M_e=L_e&=10N_e,&Q_e&=18N_e+1.
\end{aligned}
\tag{1.1}
$$

所有未标底的对数均为自然对数；公共参数仍为 $d=1/64$、$\tau_0=1$、$r=1/4$、$B_{\rm field}=2$、$G=1$。内部尺度固定为

$$
m=m_e,\quad D=D_e,\quad a=e/64,\quad s=e/768,
\quad t=me^2,\quad\lambda=ms^2=t/768^2.
\tag{1.2}
$$

内部精度 $a$ 不替换 (1.1) 中的 $e$。场遍历全部原始 $C^2$、秩二映射 $n:U\to S^2$，其中 $U$ 包含两条完整闭 $r=1/4$ 轴段，且
$\|n_{aa}(v e_a)\|_2\le2$（$a=x,y$、$|v|\le1/4$）、$\|n_x(0)\|_2,\|n_y(0)\|_2\le1$。独立场重置供应 $\rho_n(z)=(I+n(z)\cdot\sigma)/2$。初始参考
$R=\operatorname{Sym}^m(\mathbb C^2)$ 只准备一次，初态 $\tau_h=|e_h\rangle\langle e_h|$、$h\in S^2$，与其余输入独立，是唯一含未知 $h$ 的输入。原目标为

$$
D_h(n)=\left(
\frac{h\cdot[n(0)\times n_x(0)]}{2},
\frac{h\cdot[n(0)\times n_y(0)]}{4},0,
\frac{h\cdot n_y(0)}2\right).
\tag{1.3}
$$

比较类保留原始混合辅助、量子与经典记忆、反馈、纠缠、探针回用和有限因果控制。所有准备、控制及解码程序均不依赖实际 $n,h$；固定 $n$ 后，非参考来源的完整律对全部 $h$ 相同。不供应混合输入的纯化。与 $R$ 的接触仅为至多 $L_e$ 次前向原生等距

$$
V=\Pi_+\otimes|++\rangle_{HE}+\Pi_-\otimes|--\rangle_{HE}
\tag{1.4}
$$

及恰一次规定终端 $U_{\rm term}=\exp[-idJ\cdot\sigma/m]$，其中 $d=1/64$、$\tau_0=1$；终端使用在 $+d e_x$ 独立重置且此前未经改动的原场令牌。场重置至多 $Q_e$ 次。其余操作在原始标记 $R$ 上恒等，不直接读取、旋转、拆分、重置、替换或恢复 $R$，不供应未知射线反射或终端逆。

采用有限 CP 节点的声明实际端口语义。每个实际生成的系统都属于最终非参考口 $K$，包括探针、场令牌、$H,E$、原始记录、实际副本、记忆、程序、计数器、路由、工作空间、补偿及终端输出。形式 Kraus 指标不是自动生成的物理环境。下文指定的非参考替换和 Lüders 节点恰有第 8 节列出的实际口，不通过一个另有未保留浴的酉扩张实现。若另一实现生成额外实际环境，须把它加入 $K$ 并另给完整输出界。

对同一运行的输出定义

$$
\mathcal R_h(\omega)=D_{\rm tr}(\omega,\tau_h\otimes\operatorname{Tr}_R\omega),
\quad D_{\rm tr}(X,Y)=\tfrac12\|X-Y\|_1,
\quad\overline\delta=\sup_{n,h}\mathcal R_h(\Omega_{n,h}).
\tag{1.5}
$$

**定理 1.2（完整原生成功控制器）。** 取第 2 节的固定解析常数和显式整数 $r_0$。对每个 $e=2^{-r}$、$r\ge r_0$，存在第 3–10 节指定的一个有限、与实际 $n,h$ 无关的控制器及有理四坐标解码器。在定义 1.1 的全部场、全部 $h$ 和上述声明有限 CP 实际端口下，同一运行满足

$$
\begin{gathered}
\sup_{n,h}\Pr[\|\widehat D-D_h(n)\|_\infty>e]\le2e/3,\\
\overline\delta\le\frac{C_{\rm final}}{t},\qquad
C_{\rm final}=2\cdot768^2(C_{\rm return}+3C_{\rm fail})+5,\\
T_V\le\nu_eq_e+2\le L_e,\qquad
T_{\rm reset}=15\ell_e+2\le Q_e,\qquad T_R\le\nu_eq_e+3,\\
q_e=\left\lceil\log_2(D_eL_e/e)\right\rceil,
\qquad\nu_e\le C_\nu e^{-3}\log(2t/e),\qquad\nu_eq_e\le L_e-2.
\end{gathered}
\tag{1.6}
$$

其中恰执行一次原规定终端。获取前缀使用零次场重置、零次终端；它在自己的全部实际输出 $K_{\rm acq}$ 上满足

$$
\sup_hD_{\rm tr}\bigl(\Gamma_e(\tau_h),
\Phi_{{\rm red},e}(\tau_h)\otimes\sigma_e\bigr)
\le\frac1{16t}\le\frac1t.
\tag{1.7}
$$

$\Phi_{{\rm red},e}$ 是第 3 节同一个有限球冠极分解后、在任何经典 $k$ 记录或副本生成之前，把未测量的 $K_{\rm work}$ 替换为同名固定输出 $|0\rangle\langle0|$ 的通道，恰为 OTF004 定义 26.11 的选择。$\sigma_e$ 在相同的额外实际编译、程序及每次原生访问记录空间上，与输入无关。全部标志、非投影块振幅、失败、停止和截止分支都包含在无条件态内。

控制器使用第 10 节的原全场采样、有理四坐标解码器和恰为 OTF004 定义 17.1 的固定后缀。原始全部记录和各个替换后的同名量子输出都保留。辅助混合旁观记忆可原样保留，各通道比较稳定于任意旁观系统，不使用它们的纯化。

证明。第 3 节同时确定唯一有限球冠族；第 4–6 节给出其 Fourier–beta 逻辑字和完整等距误差；第 7–8 节将所有正、逆及受控访问逐个替换为付费前向原生字并列出全部实际口，证明 (1.7) 和获取预算。第 9 节证明该约化接口的自身边缘返回；第 10 节在同一运行中证明全部场上的成功、规定完成后的返回及余下资源界。$\square$

## 2. 固定解析常数与精度窗口

**定义 2.1（固定振幅及原常数）。** 使用 OTF004 式 (25.6)、(25.8) 的固定函数与常数。为明确其定义，对 $|w|<1$ 令

$$
b=1-|w|^2,\qquad q(w)=e^{-1/b},\qquad\alpha(w)=\bar w/b,
\qquad F_k(w)=\sqrt{q(w)}e^{-|\alpha(w)|^2/2}
\frac{\alpha(w)^k}{\sqrt{k!}},\quad k\ge0,
\tag{2.1}
$$

$F$ 在 $|w|\ge1$ 延拓为零。置

$$
\begin{aligned}
z_0&=\int_{|w|<1}q(w)\,\frac{dA(w)}\pi,&
M_F&=\sup_w(\|F\|+\|DF\|+\|D^2F\|),\\
A=B&=10{,}000(1+M_F)/\sqrt{z_0},&R_0&=4(A+B+2),\\
C_{\rm fail}&=1+256A^2,&
C_{\rm return}&=3R_0+257A^2+2,&t_*&=256\max\{100,R_0\}.
\end{aligned}
\tag{2.2}
$$

这里及下文的导数为实导数算子范数，序列范数为 $\ell^2$ 范数。沿用 OTF004 式 (26.2) 的常数，写成

$$
\begin{aligned}
C_t&=1{,}440{,}000{,}000{,}000,& B_*&=3R_0+2C_{\rm fail},\\
\Lambda&=\max\{t_*,2C_{\rm fail},A^2,64B_*^2,64C_{\rm return}^2\},\\
K_{\rm risk}&=3\cdot768^2C_{\rm fail}+1,\\
e_*&=\min\left\{\frac1{100},\sqrt{\frac{C_t}{768^2\Lambda}},
\frac{C_t}{6K_{\rm risk}},\frac{C_t}{393216}\right\},\\
r_{\rm base}&=\max\{7,\lceil\log_2(1/e_*)\rceil\}.
\end{aligned}
\tag{2.3}
$$

**定义 2.2（高阶范数常数）。** 令 $H(v)=e^{-1/v}$（$v>0$），否则 $H(v)=0$，并置

$$
\theta(v)=\frac{H(v)}{H(v)+H(1-v)},\qquad
\chi(\rho)=\theta(8\rho-4)\theta(12-8\rho).
\tag{2.4}
$$

则 $0\le\chi\le1$，在 $\rho=1$ 的邻域等于一，支撑包含于 $[1/2,3/2]$。令 $(N_{\rm osc}v)_k=kv_k$，对 $0\le j\le26$ 定义

$$
M_j=\sup_w\bigl(\|D^jF(w)\|+\|N_{\rm osc}D^jF(w)\|\bigr).
\tag{2.5}
$$

这些常数有限：对归一相干序列求导后，范数平方由 Poisson 分布的固定阶矩控制，故只按 $|\alpha|$ 多项式增长；复合 $\alpha=\bar w/b$ 后只增加 $b^{-1}$ 的幂，而 $e^{-1/(2b)}$ 压倒每个这样的幂。这也证明所有零延拓在数算子图范数内光滑。

采用 OTF004 的北极立体坐标 $z$、其逆 $h(z)$ 和旋转图。令 $G_j$ 为一加上下列固定几何映射的 $0$ 至 $j$ 阶导数算子范数的全部上确界：Euler 坐标的 $SU(2)$ 作用；在 $|z|\le1$、$|\phi_{g,q}(z)|\le1/100$ 上的
$\phi_{g,q}(z)=z(g^{-1}q h(z))$；在 $1/2\le|x|\le3/2$、输出图满足 $|z|\le1$ 上的径向图
$x\mapsto z(q^{-1}x/|x|)$；以及该环域上的 $\chi(|x|)$。群参数取紧 Euler 角盒，$q$ 遍历旋转图。第一类 Möbius 分母的模至少 $1/\sqrt{1+10^{-4}}$，径向图分母也一致远离零。这些是显式固定光滑映射在紧域上的范数。

固定整数

$$
C=1+\left\lceil10^{100}(26!)^{10}
\left[1+A+B+z_0^{-1}+\sum_{j=0}^{26}(M_j+G_j)\right]^{100}\right\rceil.
\tag{2.6}
$$

乘积和链式法则至多引入 $(26!)^2$ 个分拆项及每次复合至多 26 个几何导数因子，故下文球冠及几何估计可统一用 $C$ 控制，径向延拓用 $C^4$ 控制。这些常数不依赖 $e,m,J,K_0$。

**定义 2.3（显式充分二进窗口）。** 置

$$
\begin{aligned}
M_{\rm Fourier}&=2^{50}C^4,& A_0&=2^{20}768^2M_{\rm Fourier},\\
U_0&=3\cdot10^{16},&C_\nu&=2^{26}A_0,\\
r_0=\max\bigl\{&r_{\rm base},7,
\lceil\log_2(1000U_0M_{\rm Fourier}768^{24})\rceil,\\
&\lceil\log_2(10000A_0)\rceil,
\lceil\log_2(10000C_\nu^2)\rceil\bigr\}.
\end{aligned}
\tag{2.7}
$$

使用 $e=2^{-r}$、$r\ge r_0$，故 $0<e\le2^{-r_0}$。常数由固定显示函数的解析范数定义，不要求其数值物化。原窗口直接给

$$
t\ge C_t e^{-2}\log^2(1/e)\ge C_t/e^2,\quad
\lambda\ge\Lambda,\quad t\ge6K_{\rm risk}/e,
\quad t\ge16384\log(24/e).
\tag{2.8}
$$

## 3. 同时有限化的球冠族与约化目标

**定义 3.1（一次截断、一次正求积）。** 置

$$
K_0=\lceil C^8\lambda s^{-4}\rceil,\qquad
P=\lceil C^{16}\lambda s^{-60}\rceil,\qquad J=P^3.
\tag{3.1}
$$

对 $i,j,k\in\{0,\ldots,P-1\}$，取

$$
\begin{aligned}
A_i&=2\pi(i+1/2)/P,&B_j&=\pi(j+1/2)/P,&G_k&=4\pi(k+1/2)/P,\\
g_{ijk}&=e^{-iA_i\sigma_z/2}e^{-iB_j\sigma_y/2}e^{-iG_k\sigma_z/2},\\
w_{ijk}&=\frac{\cos(\pi j/P)-\cos(\pi(j+1)/P)}{2P^2}.
\end{aligned}
\tag{3.2}
$$

固定按字典序把三元指标编号为 $1\le l\le J$。权重正、和恰为一，是 Euler 单元的精确归一 Haar 质量。令

$$
\begin{aligned}
Z_s&=s^2\int_{|w|<1}\frac{q(w)}{(1+s^2|w|^2)^2}\frac{dA(w)}\pi,\\
f_{lk}(h)&=\frac{\sqrt{w_l}F_k(z(g_l^{-1}h)/s)}
{\sqrt{Z_s}\sqrt{1+1/(100\lambda)}},\qquad 0\le k\le K_0,\\
f_{0k}&=0,\qquad c_l=g_l e_z,\qquad d_f=(J+1)(K_0+1).
\end{aligned}
\tag{3.3}
$$

支撑外按光滑零延拓解释，$L$ 允许零标签。记 $f=(f_{lk})\in\mathbb C^{d_f}$，以 $P_K$ 表示序列的正交截断。

**定理 3.2（该有限族的共同估计）。** 定义 3.1 的同一个截断与同一个求积满足 OTF004 定义 26.2、引理 26.4 的全部条件，并且在全部旋转图上

$$
\|D^jf\|\le2Cs^{-j}\quad(0\le j\le24).
\tag{3.4}
$$

证明。写 $a_g(h)=Z_s^{-1/2}F(z(g^{-1}h)/s)$。由 $Z_s\ge z_0s^2/2$、链式法则及定义 2.2，

$$
\|D_h^ja_g\|\le Cs^{-j-1},\qquad
\|D_gD_h^ja_g\|\le Cs^{-j-2}.
\tag{3.5}
$$

Haar 支撑质量至多 $s^2$，所以
$\int\|D_h^ja_g\|^2dg\le C^2s^{-2j}$。正交截断不增加这些范数。对数算子定义域内的向量，

$$
\|(I-P_K)v\|\le\frac{\|N_{\rm osc}v\|}{K+1}.
\tag{3.6}
$$

故球冠截断至一阶的误差至多 $Cs^{-j-1}/(K_0+1)$；归一化、绝对标量流和范数乘积积分的误差至多 $2C^2s^{-3}/(K_0+1)$，平方尾项还更小。

相关的平方 $j$ 阶导数对 Euler 参数的 Lipschitz 常数至多 $2C^2s^{-2j-3}$；绝对标量流和范数乘积的相应常数至多 $2C^2s^{-4}$。Euler 盒中单元直径小于 $22/P$。由 (3.1)，截断与归一化、流及求积误差同时小于 $1/(1000\lambda)$，对 $h$、旋转图及单位导数方向一致。在 $j=24$ 时，除以 $P$ 前最坏的幂为 $s^{-51}$，仍余 $s^9$。

无限 Haar 族的归一化恰为一，每个 $g$ 的标量流恰为零。共同除以 $\sqrt{1+1/(100\lambda)}$ 后得到

$$
\begin{gathered}
1-1/\lambda\le\|f(h)\|^2\le1,\qquad
\|Df\|\le A/s,\quad\|D^2f\|\le B/s^2,\\
\sum_l\left|\sum_k\overline{f_{lk}}\partial_{\bar z}f_{lk}\right|\le1/\lambda,
\qquad\operatorname{supp}f_{lk}\subset\{\theta(\,\cdot\,,c_l)<2s\}.
\end{gathered}
\tag{3.7}
$$

一、二阶采用 OTF004 引理 25.4 的更尖锐 Haar 界
$8M_F^2/(z_0s^2)$、$128M_F^2/(z_0s^4)$，在原 $A,B$ 内有严格余量。OTF004 式 (26.10) 给无限族的范数乘积积分至少 $1/s$；上述共同截断、求积和归一化仍留下

$$
\sum_l\|f_l(h)\|\,\|\partial_{\bar z}f_l(h)\|\ge1/(2s).
\tag{3.8}
$$

同一平方导数估计给 (3.4)。所有步骤使用向量范数，不引入 $J$ 或 $K_0$ 因子。$f_{lk}$ 是带固定 $g_l$ 图相位的真正标量函数，其 Fourier 展开不依赖相干 ket 的相位选择。$\square$

**定义 3.3（极分解与同名约化工作口）。** 采用 OTF004 式 (26.4) 的 Toeplitz 映射

$$
T_m(b)=D\int_{S^2}b(u)\tau_u\,d\mu(u),\quad
A_{lk}=T_m(f_{lk}),\quad
A_{\rm stack}\psi=\sum_{lk}A_{lk}\psi\otimes|l,k\rangle,
\quad S_{\rm op}=A_{\rm stack}^\dagger A_{\rm stack},
\quad W=A_{\rm stack}S_{\rm op}^{-1/2}.
\tag{3.9}
$$

由 OTF004 命题 25.5 及式 (26.5)，

$$
0\le I-S_{\rm op}\le(C_{\rm fail}/\lambda)I,\qquad
S_{\rm op}\ge I/2,\qquad\|W-A_{\rm stack}\|\le C_{\rm fail}/\lambda.
\tag{3.10}
$$

$W$ 是等距。先施行 $W$，在任何 $k$ 测量、原始记录或副本之前，施行声明的非参考 CP 节点

$$
\mathcal Q_{K_{\rm work}}(X)
=\operatorname{Tr}_{K_{\rm work}}(X)\otimes|0\rangle\langle0|_{K_{\rm work}}.
\tag{3.11}
$$

再对 $L$ 作完整 Lüders 读出，保留 OTF004 式 (26.7) 的同一 $J_l$：测后 $L$、原始 $l$、实际 $l$ 副本、旧两坐标解码器、有理方向 $\widehat h(l)$、固定程序及工作因子。$l=0$ 及无效码的估计固定为零。所得通道为 $\Phi_{{\rm red},e}$。它在上述列明口上恰为

$$
\Phi_{{\rm red},e}(X)=
\left(\sum_{lk}A_{lk}S_{\rm op}^{-1/2}X S_{\rm op}^{-1/2}A_{lk}^\dagger
\otimes|J_l\rangle\langle J_l|\right)\otimes|0\rangle\langle0|_{K_{\rm work}}.
\tag{3.12}
$$

替换后的 $K_{\rm work}$ 仍是同名实际输出。没有原始 $k$ 记录存在；(3.12) 中的 $k$ 是 CP 求和指标。这正是定义 26.11 的约化接口，区别于保留相干 $K_{\rm work}$ 的 $\Phi_{\rm keep}$。

## 4. 共同向量 Fourier 表及其误差

**定义 4.1（径向延拓和有限有理系数表）。** 在 $[-2,2]^3$ 上令

$$
b_e(x)=\chi(|x|)f(x/|x|),\qquad
c_n=\frac1{64}\int_{[-2,2]^3}b_e(x)e^{-i\pi n\cdot x/2}\,dx,
\quad n\in\mathbb Z^3.
\tag{4.1}
$$

在原点邻域取零，按每坐标周期四延拓。令

$$
R_F=\lceil e^{-3/2}\rceil,\quad
\mathcal F=\{n:|n|_\infty\le R_F\},\quad
F_{\rm count}=(2R_F+1)^3,\quad\xi_n=\pi n/2.
\tag{4.2}
$$

为给出完全有限的系数表，固定

$$
L_{\rm int}=C^4/s+6R_F,\quad
B_{\rm int}=\left\lceil10^8tF_{\rm count}(L_{\rm int}+1)\right\rceil,
\quad p_{\rm int}=\left\lceil\log_2(10^8tF_{\rm count}d_f)\right\rceil.
\tag{4.3}
$$

把立方体等分为 $B_{\rm int}^3$ 个单元，在中点对 (4.1) 作归一和。每个实、虚分量的函数值取误差至多 $2^{-p_{\rm int}}$ 的二进有理数；以有证明的初等函数区间求值和一个固定枚举中首个合格输出确定选择。由此定义有理复向量 $a_n$；其 $l=0$ 分量始终精确取零。积分、常数及该有限求值规定定义公共数据，不要求数值执行。

置

$$
\widehat\alpha=\sum_{n\in\mathcal F}\|a_n\|_2,\quad
v_n=a_n/\|a_n\|_2\ (a_n\ne0),\quad
\epsilon_{\rm in}=\frac1{10000t\widehat\alpha},\quad
\beta=2(1+\epsilon_{\rm in})\widehat\alpha,\quad
\delta=\frac1{2\beta}.
\tag{4.4}
$$

零向量的准备权重为零、方向取任意固定向量。

**定理 4.2（维数无关的归一化与二十四阶尾界）。** 上述同一向量表满足

$$
\begin{gathered}
\sum_n\|c_n\|_2\le32M_{\rm Fourier}s^{-3/2}\le A_0e^{-3/2},\\
\sum_{n\notin\mathcal F}\|c_n\|_2\le\frac1{1000t},\qquad
\sum_{n\in\mathcal F}\|a_n-c_n\|_2\le\frac1{10000t},\\
\frac12\le\widehat\alpha\le A_0e^{-3/2}.
\end{gathered}
\tag{4.5}
$$

证明。由定理 3.2 及径向链式法则，在归一体积的 $\mathbb T_4^3$ 上

$$
\|\partial^\gamma b_e\|_{L^2}\le C^4s^{-|\gamma|}
\quad(|\gamma|\le24),\qquad\|b_e\|_{L^2}\le1.
\tag{4.6}
$$

向量 Parseval 等式给

$$
\left(\sum_n|n|^{2j}\|c_n\|_2^2\right)^{1/2}
\le M_{\rm Fourier}s^{-j},\qquad j=2,24.
\tag{4.7}
$$

常数 $2^{50}$ 已包含多重指标和及频率 $\pi/2$ 的因子。取 $H=\lceil1/s\rceil$。低频格点至多 $27H^3$ 个，Cauchy–Schwarz 给其系数范数和至多 $6H^{3/2}$。其余部分用

$$
\sum_{|n|_\infty>H}|n|_\infty^{-4}\le52/H
\tag{4.8}
$$

及 (4.7) 的 $j=2$ 界，得到 $32M_{\rm Fourier}s^{-3/2}$。这是整个向量族的共同归一化，不逐分量累加维数损失。

格壳计数
$(2k+1)^3-(2k-1)^3=24k^2+2\le26k^2$，结合 (4.7) 的 $j=24$ 界给

$$
\sum_{|n|_\infty>R}\|c_n\|_2
\le M_{\rm Fourier}s^{-24}R^{-45/2}.
\tag{4.9}
$$

取 $R=R_F$ 后右端至多 $M_{\rm Fourier}768^{24}e^{39/4}$。原曲线有 $t\le U_0e^{-8}$，而 (2.7) 的窗口使该项至多 $1/(1000t)$。绝对收敛将 Fourier 级数识别为光滑周期延拓，故在球面上恰还原 $f$。

对每个系数，向量被积函数的 Lipschitz 常数至多 $L_{\rm int}$，中点误差至多 $7L_{\rm int}/B_{\rm int}$。分量舍入贡献至多

$$
\sqrt{2d_f}\,2^{-p_{\rm int}}\le\frac2{10^8tF_{\rm count}}.
\tag{4.10}
$$

对有限频率求和给 (4.5) 的表误差。上界仍在 $A_0e^{-3/2}$ 的余量内；下界使用 $\|f(h)\|\ge\sqrt{1-1/\lambda}$、$\lambda\ge2$ 及两个一致逼近误差，得到 $\widehat\alpha\ge1/2$。后续字使用的就是这张有理表。$\square$

## 5. 精确 beta–Toeplitz 桥与矩形输入输出块

**定义 5.1（有限内层多项式与频率轴）。** 令

$$
N=\left\lceil16\left[6e^{-3/2}+\log(1/\epsilon_{\rm in})+1\right]\right\rceil,
\qquad p_n(x)=\sum_{j=0}^N\frac{(i|\xi_n|x)^j}{j!}.
\tag{5.1}
$$

频率轴记作 $\mathfrak a_n=\xi_n/|\xi_n|$（$n\ne0$），零频率取 $e_z$，以区别于系数向量 $a_n$。对任意单位轴 $\mathfrak a$，令

$$
A_{\mathfrak a}=\frac{I+2J_{\mathfrak a}}D,\qquad
B_{\mathfrak a}=\frac{DA_{\mathfrak a}-I}{D+1}
=\frac{2J_{\mathfrak a}}{m+2}.
\tag{5.2}
$$

**定理 5.2（该构造的精确矩形编码）。** 存在第 5.3 段指定的有限酉字 $U_e$ 及仅作用于非参考辅助口的输入输出投影 $\Pi,\widetilde\Pi$，使

$$
\widetilde\Pi U_e\Pi=\widehat A/\beta,\qquad
\widehat A\psi=\sum_{n\in\mathcal F}g_{p_n}(B_{\mathfrak a_n})\psi\otimes a_n,
\qquad\|\widehat A-A_{\rm stack}\|\le\frac3{2500t}.
\tag{5.3}
$$

其所用 beta 多项式和全部归一化由以下证明确定。

证明。只在证明中取轴 $\mathfrak a$ 的自旋基，$J_{\mathfrak a}$ 本征值为 $m/2-k$、$0\le k\le m$。对 $y=(1+\mathfrak a\cdot u)/2$，相干态分辨和方位积分使 $T_m(p(\mathfrak a\cdot u))$ 的非对角元为零，第 $k$ 个对角元为

$$
(m+1)\binom mk\int_0^1p(2y-1)y^{m-k}(1-y)^k\,dy.
\tag{5.4}
$$

此处使用 [DLMF 5.12.E1](https://dlmf.nist.gov/5.12.E1) 的 beta 积分
$B(a,b)=\Gamma(a)\Gamma(b)/\Gamma(a+b)$，实际参数 $m-k+1,k+1$ 都正，且
$(m+1)\binom mk B(m-k+1,k+1)=1$。所以 (5.4) 是 $\operatorname{Beta}(m-k+1,k+1)$ 下的期望。若 $b_k=(m-2k)/(m+2)$，两参数恰为 $(m+2)(1+b_k)/2$、$(m+2)(1-b_k)/2$，从而

$$
T_m(p(\mathfrak a\cdot u))=g_p(B_{\mathfrak a}).
\tag{5.5}
$$

具体地，若 $p(x)=\sum_jp_jx^j$，以 $(z)_v=z(z+1)\cdots(z+v-1)$、$(z)_0=1$ 记升阶乘，则

$$
g_p(b)=\sum_jp_j\sum_{v=0}^j\binom jv2^v(-1)^{j-v}
\frac{\bigl((m+2)(1+b)/2\bigr)_v}{(m+2)_v}.
\tag{5.6}
$$

因此 $\deg g_p\le\deg p$。在 $-1<b<1$ 上，这是正的归一期望，故
$\|g_p\|_{[-1,1]}\le\|p\|_{[-1,1]}$。端点 $b\to1,-1$ 时 beta 分布分别弱收敛到 $y=1,0$ 的点质量；同一多项式公式给 $g_p(1)=p(1)$、$g_p(-1)=p(-1)$。代换 $y\mapsto1-y$ 证明保留实性及奇偶性。这里的全区间界包含端点。

为付费供应 (5.2)，先沿已知轴 $\mathfrak a$ 准备探针，取 $p_D=D/(D+1)$，准备概率 $p_D,1-p_D$ 的选择位。第一支 SELECT $Q_D$，第二支 SELECT $-I$，再反准备选择位，其中

$$
Q_D=\Pi_+-\Pi_-=(I+2J\cdot\sigma_S)/D.
\tag{5.7}
$$

探针和选择位零压缩恰为

$$
p_DA_{\mathfrak a}-(1-p_D)I
=\frac{DA_{\mathfrak a}-I}{D+1}=B_{\mathfrak a}.
\tag{5.8}
$$

线性组合系数绝对值和恰为一。该酉及其逆各需一个新的付费受控 $Q_D$；额外控制均在非参考位上计算。没有去掉 $I/D$ 的偏移，也没有直接供应 $J_{\mathfrak a}/j$。

**构造 5.3（PREP、SELECT、投影和内层 QSVT）。** 这里及第 6 节使用 Gilyén–Su–Low–Wiebe，[《Quantum singular value transformation and beyond》精确 v1 源](https://arxiv.org/src/1806.01838v1) 的 `BlockHam.tex` Definition 15、Theorem 17、Corollary 18 和 Lemma 19。已知结果作为 (5.3) 构造的工具使用。

实区间上的 Taylor 积分余项给

$$
|e^{irx}-p_n(x)|\le\frac{r^{N+1}}{(N+1)!}\le\epsilon_{\rm in},
\qquad r=|\xi_n|\le6e^{-3/2},\quad |x|\le1.
\tag{5.9}
$$

故 $|p_n|\le1+\epsilon_{\rm in}$。其实部为实偶多项式、虚部为实奇多项式，另外两个实虚奇偶分量为零。由 (5.5)–(5.6)，对

$$
\frac{g_{\operatorname{Re}p_n}}{1+\epsilon_{\rm in}},\qquad
\frac{g_{\operatorname{Im}p_n}}{1+\epsilon_{\rm in}}
\tag{5.10}
$$

分别应用实多项式 QSVT。二者在整个 $[-1,1]$ 上范数不超过一，实性、次数和所需奇偶性满足 Theorem 17、Corollary 18。输入输出投影取
$P_B=I_R\otimes|00\rangle\langle00|$，作用于探针及仿射选择位。等权两支选择器在虚支施加相位 $i$，再反准备，得到块

$$
\frac{g_{p_n}(B_{\mathfrak a_n})}{2(1+\epsilon_{\rm in})}.
\tag{5.11}
$$

这个因子二支付复数及奇偶选择的全部归一化。两个标量字合计至多 $2(N+2)$ 次 $B$ 编码调用。

对全部频率相干选择同一个查询序列。已知非参考探针准备
$\sum_n|n\rangle\langle n|\otimes U_{\mathfrak a_n}$ 围住共享的 $Q_D$ 访问，多项式相位按频率选择。Lemma 19 供应这种多相位字，不引入 $F_{\rm count}$ 倍的反射次数。若奇序列需要受控标量字，则相应访问也作付费受控访问。

PREP 将频率口准备为

$$
\sum_{n\in\mathcal F}\sqrt{\frac{\|a_n\|_2}{\widehat\alpha}}\,|n\rangle.
\tag{5.12}
$$

按频率在空白 $L,K_{\rm work}$ 上准备 $v_n$，施行 (5.11) 的标量 SELECT 字，最后仅反准备频率口。这定义 $U_e$。其投影为

$$
\begin{aligned}
\Pi&=I_R\otimes|0_{\rm frequency},0_{\rm labels},0_{\rm flags}\rangle
\langle0_{\rm frequency},0_{\rm labels},0_{\rm flags}|,\\
\widetilde\Pi&=I_{R,L,K_{\rm work}}\otimes|0_{\rm frequency},0_{\rm flags}\rangle
\langle0_{\rm frequency},0_{\rm flags}|.
\end{aligned}
\tag{5.13}
$$

投影、相位、选择和准备全部只作用于非 $R$ 系统。由 (5.11)–(5.12)，矩形块正是 (5.3) 中的 $\widehat A/\beta$。

令 $V_c$ 为相干态分辨的等距、$M_f$ 为向量值乘法算子，则
$A_{\rm stack}=(V_c^\dagger\otimes I)M_fV_c$，所以向量 Toeplitz 映射为压缩收缩。联合使用 Fourier 尾、表舍入和 (5.9)，

$$
\|\widehat A-A_{\rm stack}\|
\le\frac1{1000t}+\frac1{10000t}+\widehat\alpha\epsilon_{\rm in}
=\frac3{2500t}.
\tag{5.14}
$$

目标仍是定义 3.3 同一个有限 $f$ 的极等距 $W$。

所有相位表按 Corollary 18 的构造性实多项式相位分解确定，采用固定根及分支排序；交替字恰取 Definition 15，实多项式包装取 Corollary 18 的 $+\Phi$、$-\Phi$ 字的 Hadamard 共轭直和。内部实偶和虚奇多项式分别使用它，外层也使用同一规定。不合成谱投影。

每个逆都是有限逻辑字的逆序伴随。其中已知非参考准备及其逆是已知矩阵；每个 $Q_D$ 或受控 $Q_D$ 的逆字母由一个新的第 7 节前向原生字供应，使用新记录，不使用 $V^\dagger$，也不倒转已经存在的原生记录。这完成定理 5.2 的逻辑块证明。$\square$

## 6. 外层极变换与无条件完整等距

**定义 6.1（有界奇 erf 多项式及有限相位精度）。** 令

$$
\begin{aligned}
\epsilon_s&=\frac1{10000t^2},&H_s&=\log(16/\epsilon_s),&
\kappa&=\delta^{-1}\sqrt{H_s},\\
\rho&=1+\delta/2,&M_s&=(16/\epsilon_s)^2,\\
n_s&=\text{不小于 }\frac{\log(32M_s/(\epsilon_s\delta))}{\log\rho}
\text{ 的最小奇整数}.
\end{aligned}
\tag{6.1}
$$

令 $E_{n_s}$ 为 $\operatorname{erf}(\kappa x)$ 的 $n_s$ 阶 Chebyshev 截断，并取

$$
P_s(x)=\frac{E_{n_s}(x)}{1+\epsilon_s/8}.
\tag{6.2}
$$

全部内外相位均由构造 5.3 的确定分解给出。如果要求有限位描述，将相位舍入为 $2\pi$ 的二进有理倍数，使角误差至多

$$
\zeta=\frac1{10^8t n_s(N+2)}.
\tag{6.3}
$$

取足够的 $p_\phi$ 使 $2\pi2^{-p_\phi}\le\zeta$ 即可。相位门出现数至多 $100n_s(N+2)$，故完整理想酉的变化至多 $1/(10^6t)$。系数、探针及选择准备具有显式已知有限代数矩阵。相位及这些准备的公共表保留于固定程序口。

**定理 6.2（包括标志和非投影块的完整误差）。** 将外层实奇 QSVT 应用于定理 5.2 的实际矩形编码，而不作投影或后选择，所得完整逻辑等距 $U_{\rm outer}$ 满足

$$
\sup_{\|\psi\|=1}
\|U_{\rm outer}\psi-|0_{\rm compiler}\rangle W\psi\|
<\frac1{32t}.
\tag{6.4}
$$

相应完整通道的半 diamond 误差至多 $1/(32t)$，对任意旁观记忆稳定。

证明。由 (3.10)、(5.14)，$\sigma_{\min}(\widehat A)\ge2/3$。记
$\widehat W=\widehat A(\widehat A^\dagger\widehat A)^{-1/2}$。编码块的每个输入奇异值大于 $\delta=1/(2\beta)$；左侧零奇异子空间不构成输入承诺，也不要求物理投影。

具体的极扰动界为

$$
\|\widehat W-W\|\le10\|\widehat A-A_{\rm stack}\|.
\tag{6.5}
$$

事实上，令 $S=A_{\rm stack}^\dagger A_{\rm stack}$、$T=\widehat A^\dagger\widehat A$，则两者均至少 $4I/9$，且
$\|T-S\|\le3\|\widehat A-A_{\rm stack}\|$。$x^{-1/2}$ 的预解式积分给

$$
\|T^{-1/2}-S^{-1/2}\|
\le\frac{\|T-S\|}{2(4/9)^{3/2}}.
\tag{6.6}
$$

展开两极因子并用 $\|A_{\rm stack}\|\le1$、$\|\widehat A\|<1.01$ 得 (6.5)。

在参数 $\rho=1+\delta/2$ 的 Bernstein 椭圆上，$|\operatorname{Im}z|\le\delta/2$。沿竖线积分 $\operatorname{erf}$ 给

$$
|\operatorname{erf}(\kappa z)|
\le1+\frac{\sqrt{H_s}}{\sqrt\pi}e^{H_s/4}\le M_s.
\tag{6.7}
$$

Chebyshev 系数的 Cauchy 界于是给

$$
\|\operatorname{erf}(\kappa x)-E_{n_s}(x)\|_{[-1,1]}
\le\frac{2M_s\rho^{-n_s}}{\rho-1}\le\epsilon_s/8.
\tag{6.8}
$$

对 $x\ge\delta$，初等 Gaussian 尾界给
$1-\operatorname{erf}(\kappa x)\le\epsilon_s/16$。因此 $P_s$ 为实奇多项式，整个 $[-1,1]$ 上范数不超过一，且在 $[\delta,1]$ 上至少 $1-\epsilon_s$；负半轴结论由奇性给出。

现在对共同有限空间上的 $U_e,\Pi,\widetilde\Pi$ 应用上述 v1 `BlockHam.tex` Corollary 18，增加它的一个实多项式标志 qubit。实性、奇偶性、全区间界和矩形输入奇异值间隙均已核对。对每个单位输入，完整酉输出与嵌入的 $\widehat W\psi$ 的内积恰为

$$
\left\langle\psi,
P_s\left(\sqrt{\widehat A^\dagger\widehat A}/\beta\right)\psi\right\rangle
\ge1-\epsilon_s.
\tag{6.9}
$$

此内积为实数，两完整向量范数均为一，所以

$$
\|U_{\rm outer}\psi-|0_{\rm compiler}\rangle\widehat W\psi\|^2
\le2\epsilon_s.
\tag{6.10}
$$

这包含每个标志、探针和全部非投影块振幅；没有把成功投影块当成确定性通道。残余概率按平方根支付振幅代价。

加上极扰动及可选相位舍入，完整等距误差小于

$$
\frac{10\cdot3/2500+\sqrt{2/10000}+10^{-6}}t
<\frac1{32t}.
\tag{6.11}
$$

算子范数等距误差控制半 diamond 距离，张量任意旁观系统仍成立；比较编译口为固定纯空白态。这证明 (6.4)。$\square$

## 7. 全部控制及逆的付费前向原生展开

**定义 7.1（每个逻辑字母的新原生字）。** 每次 $Q_D$ 或受控 $Q_D$ 调用，包括逆序逻辑字中的每一个字母，分别采用 OTF004 定理 24.2 的一个新 $q_e$ 截止字，所有记录新鲜且保留。为明确其原生操作，设

$$
|x_X\rangle=(|+\rangle+(-1)^x|-\rangle)/\sqrt2,
\qquad F_{cH}=|0\rangle\langle0|_c\otimes I_H
+|1\rangle\langle1|_c\otimes Z_H.
\tag{7.1}
$$

第一槽调用 forward $V$，然后施行非参考 $F_{cH}$，对 $H,E$ 作 $X$ 基 Lüders 读出。其完整结果算子为

$$
L_{xy}=|x_Xy_X\rangle\langle x_Xy_X|_{HE}
\otimes|xy\rangle_B\otimes|xy\rangle_F,
\qquad x,y\in\{0,1\}.
\tag{7.2}
$$

测后 $H,E$、原始两位结果 $B$、实际两位副本 $F$ 均保留；这里从未先生成总自旋 $b$ 的经典记录。OTF004 式 (24.7) 的完整矩阵恒等式给

$$
K^{(c)}_{xy}=\tfrac12Q_D^{x\oplus y}C Q_D,
\qquad C Q_D=|0\rangle\langle0|_c\otimes I+|1\rangle\langle1|_c\otimes Q_D.
\tag{7.3}
$$

每个结果效果为 $I/4$，包括控制位相干交叉块。若第一奇偶为零则成功；否则还需校正一个 $Q_D$。校正槽再次用同一个探针调用 forward $V$，不施行 $F_{cH}$，再作同一完整读出，结果作用为

$$
K^{(u)}_{xy}=\tfrac12Q_D^{x\oplus y}.
\tag{7.4}
$$

在首次奇偶一处校正成功并停止；奇偶零则继续，至多总共 $q_e$ 次调用，仍未成功即标截止并保留该支。无 quantum controlled-$V$、$V^\dagger$、直接 $R$ 门、后选择或无限重试。不受控 $Q_D$ 取固定 $c=1$，仍保留该控制口；额外逻辑控制可在非参考位上计算后控制 $c$。控制和逆的每次实际访问都照此支付。

对每个新访问 $i$，预留恰 $q_e$ 组槽，未使用槽保持空白。若 $w$ 为完整历史，令 $\zeta_w$ 包含其全部新实际量子及记录输出，则

$$
\sigma_{s,q_e}=\sum_{w\ {\rm success}}4^{-|w|}\zeta_w,\qquad
\sigma_{f,q_e}=\sum_{w\ {\rm cutoff}}4^{-q_e}\zeta_w,
\qquad\sigma_{Z_i,q_e}=\sigma_{s,q_e}+\sigma_{f,q_e}.
\tag{7.5}
$$

这是 OTF004 式 (24.9) 的同一空间历史混合；截止总质量为 $2^{-q_e}$。在任意混合、纠缠的逻辑输入及旧记忆上，新字与理想逻辑门张量 $\sigma_{Z_i,q_e}$ 的半 diamond 距离恰为 $2^{-q_e}$，从而至多 $e/(D_eL_e)$。新记录只用于该本地字内部的停止控制；固定槽屏障之后的逻辑门不读取它们。旧原始记录从不擦除或倒转。

**定理 7.2（最坏原生成本及同一完整空间上的获取误差）。** 全部逻辑字用定义 7.1 替换后的前缀满足 (1.7)，且原生最坏调用数不超过 $L_e-2$。

证明。写 $H_0=\log(1/e)$、$H=\log(2t/e)$。从未改动的 ceil/max 元组直接得到

$$
\begin{gathered}
D=8{,}000{,}000N_e^2,\qquad
27000e^{-4}H_0\le N_e\le60000e^{-4}H_0,\\
t\le U_0e^{-8},\qquad q_e\le64H_0.
\end{gathered}
\tag{7.6}
$$

这些是原定义的界，不是替代定义。在 (2.7) 的窗口中，

$$
\log(1/\epsilon_{\rm in})\le\log t+\tfrac52H_0,
\quad H\le40+9H_0,\quad N\le4096e^{-3/2}.
\tag{7.7}
$$

用 $\log\rho\ge\delta/4$ 及
$\log(32M_s/(\epsilon_s\delta))\le32H$，得到

$$
n_s\le1024A_0e^{-3/2}H.
\tag{7.8}
$$

把外层实 QSVT 的交替字、内层两种奇偶字、选择器、全部受控变体及每一个逆都展开。每次 $B$ 编码及其逆各含一个付费 $C Q_D$；内层两字合计至多 $2(N+2)$ 次，外层实包装和交替调用合计给

$$
\nu_e\le4n_s(N+2)\le C_\nu e^{-3}\log(2t/e).
\tag{7.9}
$$

所有投影相位、已知准备和选择逻辑是非参考门，不额外接触 $R$。无放大、逆或控制访问被省略。频率选择共享查询，不乘 $F_{\rm count}$。

由于 $H\le49e^{-1/2}$，窗口中的 $e\le1/(10000C_\nu^2)$ 给

$$
\frac{\nu_eq_e}{L_e}
\le\frac{64C_\nu}{270000}eH
\le\frac{64\cdot49}{100\cdot270000}<\frac12.
\tag{7.10}
$$

所以 $\nu_eq_e\le L_e/2\le L_e-2$。该界包含每一支的 $q_e$，不是期望调用数。

对每一个正、逆或受控逻辑字母分别用新原生字。OTF004 定理 24.5 的稳定复合比较给全部实际输出上的误差

$$
\frac12\|\mathcal G_{\rm native}
-\mathcal G_{\rm logical}\otimes\bigotimes_{i=1}^{\nu_e}\sigma_{Z_i,q_e}\|_\diamond
\le\frac{\nu_e e}{D_eL_e}\le\frac e{D_e}\le\frac1{32t}.
\tag{7.11}
$$

这里固定屏障后的门不读取原生记录，故比较因子确为输入无关的张量积，而非仅有距离界。所有本地截止仍在无条件通道内。

完整外层极字之后才施行 (3.11)，再作 $L$ 的完整读出和同一 $J_l$ 复制、解码。$K_{\rm work}$ 的未测量替换与 $L$ 读出及仅依赖 $L$ 的复制交换，故恰为 (3.12)，无 $k$ 测量、原始 $k$ 记录或 $k$ 副本。将定理 6.2 的完整等距界与 (7.11) 相加，再用公共 CP 后处理的收缩性，得到

$$
D_{\rm tr}\bigl(\Gamma_e(\tau_h),
\Phi_{{\rm red},e}(\tau_h)\otimes\sigma_e\bigr)
\le\frac1{16t}.
\tag{7.12}
$$

$\sigma_e$ 包含固定编译、程序输出及全部同空间访问因子。无环境遗漏或既有记录擦除用于取得此界。前缀不需要场重置或规定终端，证明所述全部结论。$\square$

## 8. 全部实际端口、有限表及空间

**定义 8.1（声明的完整有限实现）。** 下表是定理 1.2 所用有限 CP 实现的全部端口。已知非参考酉字直接作用于表中有限寄存器；选定的替换和 Lüders 仪器恰有表中实际输出。代数 Kraus 标签不是额外生成的系统。

| 端口 | 内容与比较空间 |
| --- | --- |
| $R$ | 原始 $\operatorname{Sym}^m(\mathbb C^2)$，维数 $D$。不拆分、直接旋转、读取、重置、替换或供应未知射线反射；实际接触仅为 forward $V$ 及一次规定终端。 |
| $L,K_{\rm work}$ | $L$ 维数 $J+1$，$K_{\rm work}$ 维数 $K_0+1$。后者在约化替换前保持未测量，并以同名 $|0\rangle\langle0|$ 输出保留。随后保留测后 $L$、原始 $l$、实际 $l$ 副本、旧两坐标解码器和有理三坐标 $\widehat h$；没有产生 $k$ 记录或副本。 |
| 编译量子工作空间 | 频率维数 $F_{\rm count}$、回用探针 $S$、仿射选择位、复数及奇偶选择位、内层实 QSVT 标志、外层实 QSVT 标志、投影相位及控制工作位、基标志。直接构造在频率及 $L,K_{\rm work}$ 之外至多需十个二元因子，全部保留。理想比较为固定空白态；实际残余标志及相干非投影块振幅由完整等距误差覆盖。 |
| 每个访问 $Z_i$ | 对包括逆字母的每个实际逻辑访问预留 $q_e$ 槽。每槽保留 $H,E$、两位原始 $X$ 读数 $B$、两位实际副本 $F$、使用位和奇偶位；再保留局部计数 $0,\ldots,q_e$、活动/成功/截止标记及一个二元工作输出。未用槽空白，全部失败及截止保留；后续逻辑门不使用这些记录。 |
| 固定程序及经典存储 | 全部有限公共系数、相位、轴表及程序、计数、路由寄存器。固定数据及最终确定计数属于输入无关比较因子；本地依赖历史的计数属于相应 $Z_i$。 |
| 场采样及算术 | 全部 $15\ell_e$ 枚场令牌、测后 Pauli 态、原始结果及实际副本，15 个经验均值、两个中心差分向量、有理四坐标解码器及其全部有限工作、程序口。有限字母表上的算术可按可逆查表附加输出，不需要未保留的算术环境。 |
| 规定固定后缀 | $B,A,F,S_t$、两组新 $H,E$、两个原始原生符号历史及全部实际副本、OTF004 定义 17.1 的程序、路由、工作输出和固定替换后的量子口。其 $\widehat\Phi,\mathcal E$ 节点恰取声明端口；旧获取、原生、场、解码和程序输出均作为最终 $K$ 内的旁观口保留。 |

该表中每个 $Z_i$ 的保守维数界为

$$
\dim Z_i\le3(q_e+1)2^{8q_e+1}.
\tag{8.1}
$$

对二进 $e=2^{-r}$，用 (4.3)、(6.3) 的 $B_{\rm int},p_{\rm int},p_\phi$，一个保守的固定程序存储位数为

$$
\begin{aligned}
B_{\rm prog}=\Bigl\lceil10^6
\bigl[&F_{\rm count}d_f+F_{\rm count}(N+1)+n_s(N+2)+1\bigr]\\
\cdot\bigl[&p_{\rm int}+p_\phi+
\lceil\log_2(D+P+K_0+R_F+B_{\rm int}+n_s+N+2)\rceil+r+1\bigr]\Bigr\rceil.
\end{aligned}
\tag{8.2}
$$

全部非参考获取空间可取为

$$
\dim K_{\rm acq}\le
2^{B_{\rm prog}+10}F_{\rm count}(K_0+1)(J+1)^5
\prod_{i=1}^{\nu_e}\dim Z_i.
\tag{8.3}
$$

五个标签因子可分别编码测后 $L$、原始 $l$、实际副本及两个解码输出。原合同不限制记忆维数；所有这些因子均有限。任一另选混合旁观记忆原样保留，其维数另乘到相同两边，不接入纯化。

比较因子精确为

$$
\sigma_e=\sigma_{\rm compiler,program}\otimes
\bigotimes_{i=1}^{\nu_e}\sigma_{Z_i,q_e}.
\tag{8.4}
$$

重置后的 $K_{\rm work}$ 及全部 $J_l$ 属于 $\Phi_{{\rm red},e}$ 本身。每个生成的标志、截止或失败支、探针、工作空间和原生记录都在 $K$ 中，既不为逼近也不为返回比较删除。若改变实际实现而新增环境，(8.1)–(8.4) 及返回证书不自动转移到该扩充实现。

## 9. 同一有限约化目标的自身边缘返回

**定理 9.1（约化目标及实际获取的返回）。** 在同一有限族上，

$$
\begin{aligned}
\mathcal R_h(\Phi_{{\rm red},e}(\tau_h))
&\le\frac{C_{\rm return}+3C_{\rm fail}}\lambda,\\
\mathcal R_h(\Gamma_e(\tau_h))
&\le\delta_{\rm acq}:=
\frac{C_{\rm return}+3C_{\rm fail}}\lambda+\frac2t,
\qquad h\in S^2.
\end{aligned}
\tag{9.1}
$$

第二行使用包含全部访问记录的实际获取边缘。

证明。置 $d_0=C_{\rm fail}/\lambda$。比较对象是 OTF004 式 (26.6) 的同一有限仪器

$$
\Psi_{\rm loc}(X)=\sum_{lk}A_{lk}XA_{lk}^\dagger\otimes|l\rangle\langle l|
+\sqrt{I-S_{\rm op}}X\sqrt{I-S_{\rm op}}\otimes|0\rangle\langle0|,
\tag{9.2}
$$

扩充同一个 $J_l$ 解码/复制口及固定重置 $K_{\rm work}$ 输出。它的实际 $l=0$ 失败支保留。由 (3.10)，极等距与未归一堆叠在单位输入上的秩一成功输出迹范数差至多 $2d_0$；(9.2) 的失败块迹至多 $d_0$。施行共同约化和读出后，

$$
D_{\rm tr}\bigl(\Phi_{{\rm red},e}(\tau_h),
\Psi_{\rm loc}(\tau_h)\otimes|0\rangle\langle0|_{K_{\rm work}}\bigr)
\le3d_0/2,
\tag{9.3}
$$

其中 (9.2) 已包括上述同一 $J_l$ 扩充。

对同空间的两个归一态，三角不等式及偏迹收缩性给

$$
|\mathcal R_h(\omega)-\mathcal R_h(\omega')|
\le2D_{\rm tr}(\omega,\omega').
\tag{9.4}
$$

OTF004 定理 25.6 在内部尺度 $a$、原始 $m$ 上给同一个 $\Psi_{\rm loc}$ 的返回至多 $C_{\rm return}/\lambda$；结合 (9.3)–(9.4) 得第一行。固定编译及原生比较因子不改变此界。再以 (1.7) 的 $1/t$ 完整通道界和 (9.4) 得第二行。这里由同一个有限约化仪器和极范数扰动推得上界，保留的访问记录始终进入自身边缘。$\square$

## 10. 原全场解码、同一规定后缀与最终完整返回

**定义 10.1（原有理四坐标解码器）。** 每个 $l>0$ 的中心 $c_l$ 三坐标各按 OTF004 引理 26.8 舍入到误差至多 $a=e/64$ 的有理数，得到 $\widehat h(l)$；无效码及 $l=0$ 取零。保留全部原始 $l$、实际副本及旧两坐标解码器，不将其替换为二元最优检验。

场采样恰取 OTF004 式 (19.4)、(26.25) 的部分：在
$0,+u_e e_x,-u_e e_x,+u_e e_y,-u_e e_y$ 每个点，对三个固定 Pauli 轴各取 $\ell_e$ 个样本。保留全部 $15\ell_e$ 枚场令牌、测后态、原始结果、实际副本和 15 个经验均值。置

$$
\widehat n_0=\widehat n(0),\qquad
\widehat v_a=\frac{\widehat n(+u_e e_a)-\widehat n(-u_e e_a)}{2u_e},
\quad a=x,y,
\tag{10.1}
$$

并精确计算、输出

$$
\widehat D=\left(
\frac{\widehat h\cdot[\widehat n_0\times\widehat v_x]}2,
\frac{\widehat h\cdot[\widehat n_0\times\widehat v_y]}4,
0,\frac{\widehat h\cdot\widehat v_y}2\right).
\tag{10.2}
$$

所有估计及 $u_e$ 都有理，故这是 OTF004 式 (26.26) 的同一个有限精确有理四坐标解码器，不另添舍入误差。全部均值、两个差分向量、原记录及实际算术工作输出均保留。

**定理 10.2（同一运行的全部成功和最终返回界）。** 在 $\Gamma_e$、定义 10.1 和下述恰为 OTF004 定义 17.1 的固定后缀的同一运行中，定理 1.2 的全部成功、最终自身边缘返回及资源断言成立。

证明。未测量 $K_{\rm work}$ 的替换不改变 $L$ 的分布。由 OTF004 引理 26.8，约化极目标的坏方向概率至多

$$
\Pr[\|\widehat h-h\|_\infty>e/16]
\le\frac{3C_{\rm fail}}\lambda
+4\exp[-(m+2)e^2/16384].
\tag{10.3}
$$

实际完整获取与目标的概率差至多 $1/t$，故以同一 $K_{\rm risk}$ 及原窗口，

$$
\Pr_{\rm actual}[\|\widehat h-h\|_\infty>e/16]
\le\frac{K_{\rm risk}}t+4e^{-t/16384}
\le e/6+e/6=e/3.
\tag{10.4}
$$

全场估计各坐标误差至多 $eu_e/16$ 的好事件，坏概率满足

$$
30\exp[-\ell_e e^2u_e^2/512]\le e/3.
\tag{10.5}
$$

这是对每个原始允许场的同一固定标架采样，不对场作额外限制。

写 $n_0=n(0)$、$n_a=\partial_a n(0)$。原始轴向 $C^2$ 承诺给

$$
\left\|\frac{n(u_e e_a)-n(-u_e e_a)}{2u_e}-n_a\right\|_2
\le\frac1{2u_e}\int_{-u_e}^{u_e}2|v|\,dv=u_e.
\tag{10.6}
$$

场估计对差分再贡献至多 $\sqrt3e/16$。在两个好事件上，

$$
\begin{gathered}
\|\widehat h-h\|_2\le e/8,\qquad
\|\widehat n_0-n_0\|_2\le e^2/64,\qquad
\|\widehat v_a-n_a\|_2\le e/4,\\
\|\widehat h\|_2,\|\widehat n_0\|_2,\|\widehat v_a\|_2\le2,
\qquad\|n_0\|_2=1,\quad\|n_a\|_2\le1.
\end{gathered}
\tag{10.7}
$$

逐项比较 (10.2) 和 (1.3)。叉积项在除以二或四之前的误差至多

$$
\begin{aligned}
&\left|\widehat h\cdot[\widehat n_0\times\widehat v_a]
-h\cdot[n_0\times n_a]\right|\\
&\le\|\widehat h-h\|_2\|n_0\|_2\|n_a\|_2
+\|\widehat h\|_2\bigl(\|\widehat n_0-n_0\|_2\|\widehat v_a\|_2
+\|n_0\|_2\|\widehat v_a-n_a\|_2\bigr)\\
&\le e/8+2(2e^2/64+e/4)\le11e/16.
\end{aligned}
\tag{10.8}
$$

四坐标误差分别至多 $11e/32,11e/64,0,5e/16$，均小于 $e$。两个好事件无需独立，坏事件并集至多 $2e/3$。因而这是全部原始 $n,h$ 上的同一个成功解码器。

**规定后缀。** 计算并保留 (10.2) 后，忽略全部旧获取、场及算术输出，恰接 OTF004 定义 17.1。为指定同一通道，记 $t_{\rm term}=d\tau_0=1/64$、$r_t=1-\cos t_{\rm term}$、$s_t=\sin t_{\rm term}$，在非参考 $B,A,F$ 上取该定义的固定矩阵

$$
\begin{aligned}
O_i={}&-r_t\left[\sigma_{F,i}
+\frac{\sigma_{B,i}(\sigma_A\cdot\sigma_F)
+\sigma_{A,i}(\sigma_B\cdot\sigma_F)}2\right]
+\frac{s_t}2[(\sigma_B-\sigma_A)\times\sigma_F]_i,\\
\Phi(X)&=\frac{\operatorname{Tr}(X)I_2+\sum_i\operatorname{Tr}(O_iX)\sigma_i}2,
\qquad\widehat\Phi(X)=\frac{I_B}2\otimes\Phi(X)_A\otimes\frac{I_F}2,\\
\mathcal E(X)&=\operatorname{Tr}(X)I_2/2.
\end{aligned}
\tag{10.9}
$$

其 CP、TP 性直接使用 OTF004 引理 17.2。准备固定 singlet
$|\psi^-\rangle_{BA}=(|\uparrow\downarrow\rangle-|\downarrow\uparrow\rangle)/\sqrt2$。将 $B$ 送入第一个新 forward $V$；对 $H$ 在原始标签基退相干，保留 $H,E$、原始符号及实际副本，仅在负标签上交换 $B,A$。在 $+d e_x$ 独立重置 $F$，对 $BAF$ 施行恰为 (10.9) 的 $\widehat\Phi$。将其输出 $A$ 送入第二个新 forward $V$，作同样的原始标签退相干并保留两组原生记录及实际副本。随后对 $B,A,F$ 各施行声明的 $\mathcal E$ 并保留这些同名量子输出。

最后，在 $+d e_x$ 另独立重置新鲜、此前未经改动的 $S_t$，恰一次施行

$$
U_{\rm term}=\exp[-idJ\cdot\sigma/m]
\tag{10.10}
$$

并对同一 $S_t$ 施行声明的 $\mathcal E$，仍保留它。不调用其它终端或其逆。原始及实际复制符号、$B,A,F,S_t$、两个新 $H,E$、全部程序、路由及固定工作口均在最终 $K$ 中；(10.9) 不被换成另一个带不同实际输出的扩张。所有分支都执行该后缀。

**实际最终边缘。** 场采样及算术只作用于非参考系统，不能增加自身边缘返回。令 $\omega^{\rm old}_{n,h}$ 为它们完成后的实际 $RM$ 态，$M$ 包含全部旧获取、访问、编译、场和解码口。由 (9.1)，

$$
D_{\rm tr}\bigl(\omega^{\rm old}_{n,h},
\tau_h\otimes\operatorname{Tr}_R\omega^{\rm old}_{n,h}\bigr)
\le\delta_{\rm acq}.
\tag{10.11}
$$

对两边施行同一后缀。它不读取 $M$，公共通道收缩此差至多 $\delta_{\rm acq}$。在乘积输入上，OTF004 定理 17.3 对所有 $h$ 和
$v=n(+d e_x)$ 给全部后缀口的自身边缘返回小于 $80/D$。将比较边缘换成实际最终 $K$ 边缘，由偏迹收缩性再付一次 $\delta_{\rm acq}$，所以

$$
\begin{aligned}
\mathcal R_h(\Omega_{n,h})
&\le2\delta_{\rm acq}+80/D\\
&\le\frac{2\cdot768^2(C_{\rm return}+3C_{\rm fail})+5}{t}
=\frac{C_{\rm final}}t,
\end{aligned}
\tag{10.12}
$$

其中 $80t/D\le80e^2<1$。两次 $\delta_{\rm acq}$ 都属于同一实际旧态的比较，最终使用的是自己的完整实际边缘，未换用单独可达的最优边缘。

**同一最坏资源。** 获取使用至多 $\nu_eq_e$ 次 $V$，无场重置和终端；场部分使用零次 $V$、$15\ell_e$ 次重置；规定后缀再使用两次 $V$、两次独立 $+d e_x$ 重置及一个终端。因此

$$
T_V\le\nu_eq_e+2\le L_e,\quad
T_{\rm reset}=15\ell_e+2\le18N_e+1=Q_e,\quad
T_R\le\nu_eq_e+3.
\tag{10.13}
$$

重置界使用 $18N_e\ge15\ell_e+1$。后缀为 TP 且不改已计算的解码记录，故成功边缘保持。没有额外添加旧 $3k_e$ 参考获取阶段，也没有用固定 $n_*$ 的解码器代替原全场消费者。所有重试和截止已按最坏分支支付。$\square$

## 11. 两种工作接口的适用范围

**命题 11.1（保留相干工作目标与约化目标的区别）。** OTF004 引理 26.6–26.9 对保留相干工作输出的 $\Phi_{\rm keep}$ 及其规定完成的下界，与定理 1.2 相容。

证明。$\Phi_{\rm keep}$ 保留 $K_{\rm work}$ 的相干分量；其完整工作分辨交叉块支持 OTF004 式 (26.13)、(26.15) 和规定完成后的 (26.19) 下界。定理 1.2 使用的却是 (3.11) 后的 $\Phi_{{\rm red},e}$：在任何经典 $k$ 记录生成前，对未测量的非参考工作口作声明替换，保留同名固定输出以及所有已经实际生成的其它口。此为定义 26.11 允许的不同通道。迹距离在非参考约化下收缩，保留工作目标的下界并不反向传给它。因而没有把保留工作目标的下界改成下确界 $R(e)$ 的下界，也没有擦除已有原始记录。OTF004 式 (19.11) 的逆 $D_e e^2$ 下界同样与 (10.12) 的上界相容。$\square$

## 追加锚（本行以下为增补区）

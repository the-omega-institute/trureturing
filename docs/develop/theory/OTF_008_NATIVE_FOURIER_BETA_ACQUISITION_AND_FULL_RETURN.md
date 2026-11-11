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

## 12. 固定有限球冠族的部分工作保留接口

**定义 12.1（公共有理透射率与完整自身边缘）。** 保持定义 1.1 的全部场、初始参考、独立来源、混合旁观记忆、允许控制和资源元组。精度仍为 $e=2^{-r}$、$r\ge r_0$，其中 $r_0$ 恰为 (2.7) 的原整数，不另缩小精度窗口。保持 (1.1)–(1.3) 的 $m,D,s,t,\lambda,D_h(n)$、定义 3.1 的同一个 $K_0,P,J,(g_l,w_l),f_{lk}$、(3.9) 的同一个 $W$，以及第 4–7 节的全部字母、控制、逆和付费前向原生展开。为区别于其它常数，将 (2.6) 的固定整数 $C$ 记为 $C_0$；这是同一个整数。

给定公共有理数 $\eta\in[0,1]$，仅在 (3.11) 的位置、任何经典 $k$ 记录生成之前，改用下列有限非参考 CP 节点。令 $K_+=K_0+1$，在占据数 $0,\ldots,K_0$ 上置

$$
\begin{aligned}
B_j|k\rangle
&=\begin{cases}
\sqrt{\binom{k}{j}(1-\eta)^j\eta^{k-j}}\,|k-j\rangle,&k\ge j,\\
0,&k<j,
\end{cases}\qquad 0\le j\le K_0,\\
\mathcal L_{\eta,K_0}(X)&=\sum_{j=0}^{K_0}B_jXB_j^\dagger,\\
\mathcal Q_\eta(X)&=|0\rangle\langle0|_{K_{\rm work}}
\otimes\mathcal L_{\eta,K_0}(X)_{E_\eta},
\qquad \dim E_\eta=K_+.
\end{aligned}
\tag{12.1}
$$

端点幂取 $0^0=1$。节点的实际输出恰为同名固定 $K_{\rm work}$ 和新口 $E_\eta$；$j$ 只是代数求和指标，不是实际记录或环境。该节点在每个 $L$ 块上相同。随后仍作同一个完整 $L$ 读出、保留同一 $J_l$ 的全部成分、使用定义 10.1 的原全场采样与有理四坐标解码，并恰接 (10.9)–(10.10)、即 OTF004 定义 17.1 的规定后缀。$E_\eta$ 始终被动保留，不测量、不参与反馈、不恢复、不替换。没有 $k$ 测量或其副本。

记数学获取目标为

$$
\Phi_\eta=(\operatorname{id}_{R,J}\otimes\mathcal Q_\eta)
\circ\Phi_{\rm keep},
\tag{12.2}
$$

其中 $\Phi_{\rm keep}$ 恰为 OTF004 (26.7) 对本卷固定族的保留相干工作目标，输出因子的顺序按需要作固定置换。记对应的实际原生获取为 $\Gamma_\eta$，其全部规定完成态为 $\Omega_{\eta,n,h}$。最终 $K_\eta$ 包括第 8 节的全部实际非参考口以及 $E_\eta$ 和公共 $\eta$ 的固定程序口。定义

$$
\Delta_\eta(n,h)=\frac12\left\|
\Omega_{\eta,n,h}-\tau_h\otimes
\operatorname{Tr}_R\Omega_{\eta,n,h}\right\|_1.
\tag{12.3}
$$

比较态使用此同一运行自己的完整最终边缘。$\eta=0$ 的节点是 (3.11) 附加固定空白 $E_0$，$\eta=1$ 则把原相干工作移至 $E_1$ 并保留同名固定工作口。这是新声明的比较族；(3.11)、定理 1.2 和命题 11.1 的原接口保持其原义。假设某实现另外生成实际环境时，须将其加入输出并另证返回界；该假设不属于 (12.1) 的实际端口合同。

## 13. 固定截断下对全部透射率一致的交叉质量

**定理 13.1（有限族的衰减交叉估计）。** 在定义 12.1 的同一个有限族中，对任意 $h$ 只在证明内选择以 $h$ 为中心的相干坐标，令 $e_0=e_h$、$e_1$ 为第一降低向量，并置

$$
f_l=f_l(h),\qquad g_l=\partial_{\bar z}f_l(h),\qquad
H_l=\mathcal L_{\eta,K_0}(|f_l\rangle\langle g_l|),
\qquad T_\eta=\sum_l\|H_l\|_1.
\tag{13.1}
$$

则对每个 $r\ge r_0$、每个 $h$ 和每个 $\eta\in[0,1]$，

$$
\frac{\sqrt\eta}{2s}-\frac1\lambda
\le T_\eta\le\frac{A\sqrt\eta}{s}+\frac2\lambda.
\tag{13.2}
$$

这里 (12.1) 作为有限通道对实 $\eta$ 也有定义；控制器及有限公共描述的结论仍以有理 $\eta$ 为域。

证明。先明确所复用的真空衰减数学及参数对应。令 $\mathcal H_{\rm osc}=\ell^2(\mathbb N)$，$\mathsf D(\alpha)$ 为单模 Weyl 位移，

$$
u_\alpha=\mathsf D(\alpha)|0\rangle
=\left(e^{-|\alpha|^2/2}\frac{\alpha^k}{\sqrt{k!}}\right)_{k\ge0},
\qquad v_\alpha=\mathsf D(\alpha)|1\rangle
=(\mathfrak a^\dagger-\bar\alpha)u_\alpha.
\tag{13.3}
$$

二者正交且范数为一。真空环境衰减通道 $\mathcal L_\eta$ 取振幅参数 $\sqrt\eta,\sqrt{1-\eta}$，保持模为第一模；其 Fock 作用及全部输入的位移关系复用
[BeamSplitter 的 `beamUnitary_fock`](../../../D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.lean)、
[DisplacementCovariance 的 `beam_displacement` 与 `partialTrace_pairDisplacement`](../../../D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.lean)
及其对应的 [BeamSplitter](../../../Blueprint/D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.md)、[DisplacementCovariance](../../../Blueprint/D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.md) 数学叙述。`Attenuator` 中的 `pureAttenuatorOperator` 取环境概率 $p_0=1$、$p_n=0$（$n>0$）。单独的 `coherent_output_covariance` 只陈述相干输入的结论，不足以作为下面非对角算子的全部依据；所用的是上述任意双模向量的位移传输和偏迹关系。

这些是 `literature-attested` 的既有衰减数学：[Van Herstraeten–Guha–Cerf，arXiv:2312.15623v2](https://arxiv.org/html/2312.15623v2) 的 (44) 给任意输入的位移协变，(45) 给 Fock 环境定义，此处只取真空 $n=0$。来源对应见 [Library 文献条目](../../../Library/QuantumStates/vanherstraeten2024nongaussian.md)；[Hertz 等的损耗文献条目](../../../Library/QuantumChannels/hertz2025lossbeamsplitters.md) 使用同一真空损耗参数。第二模的相位约定不影响偏迹通道。不使用非真空环境不等式或熵最优化命题。

具体地，既有双模位移关系取输入位移 $(\alpha,0)$，输出位移为 $(\sqrt\eta\alpha,\sqrt{1-\eta}\alpha)$；偏迹消去第二模的位移。故对迹类算子 $X$，

$$
\mathcal L_\eta(\mathsf D(\alpha)X\mathsf D(\alpha)^\dagger)
=\mathsf D(\sqrt\eta\alpha)\mathcal L_\eta(X)
\mathsf D(\sqrt\eta\alpha)^\dagger.
\tag{13.4}
$$

从任意向量的纯态关系到秩一交叉算子，可对 $|x+i^a y\rangle\langle x+i^a y|$（$a=0,1,2,3$）作极化；再由线性和迹范数连续性延伸到迹类。Fock 公式在真空和一光子上给

$$
\begin{aligned}
U_\eta|0,0\rangle&=|0,0\rangle,\\
U_\eta|1,0\rangle&=\sqrt\eta|1,0\rangle
+\sqrt{1-\eta}|0,1\rangle,\\
\mathcal L_\eta(|0\rangle\langle1|)&=\sqrt\eta|0\rangle\langle1|,\\
\mathcal L_\eta(|u_\alpha\rangle\langle v_\alpha|)
&=\sqrt\eta|u_{\sqrt\eta\alpha}\rangle
\langle v_{\sqrt\eta\alpha}|.
\end{aligned}
\tag{13.5}
$$

第二行的失去光子项与第一行有正交的第二模向量，因而其交叉偏迹为零；最后一行由 (13.4) 得到。这些双模向量仅用于通道恒等式，不是 (12.1) 生成的额外实际口。一般 Fock 公式同样表明 $\mathcal L_\eta$ 限制到占据 $0,\ldots,K_0$ 的输入时，恰为 (12.1) 的有限和，输出没有更高占据数。

现在固定定义 3.1 的原截断和原求积，令 $f_l^\infty,g_l^\infty$ 为同一求积点上不截断的序列及其 $\partial_{\bar z}$ 导数。归一化因子仍是 (3.3) 的因子。由 (2.5)、$Z_s\ge z_0s^2/2$、$\sum_lw_l=1$ 及 (3.6)，

$$
\begin{aligned}
u_{\rm tail}&=\left(\sum_l\|(I-P_K)f_l^\infty\|^2\right)^{1/2}
\le\frac{C_0}{sK_+},\\
v_{\rm tail}&=\left(\sum_l\|(I-P_K)g_l^\infty\|^2\right)^{1/2}
\le\frac{C_0}{s^2K_+}.
\end{aligned}
\tag{13.6}
$$

这里 $P_K$ 截到 $0,\ldots,K_0$；对导数使用中心图关系
$|(z\circ g_l^{-1})'(0)|=1+|z(g_l^{-1}h)|^2\le2$，因为非零支撑内 $|z(g_l^{-1}h)|<s<1$。$C_0$ 由 (2.6) 同时控制 $\sqrt{2/z_0}M_0$ 和 $2\sqrt{2/z_0}M_1$。球冠边界及支撑外的零延拓在数算子图范数内光滑，图极点不在非零支撑内，所以这些界对全部 $h$ 和标架一致。

由 (3.7) 的 $\|f\|\le1$、$\|g\|\le A/s$，秩一迹范数公式和 Cauchy–Schwarz 给

$$
\begin{aligned}
\sum_l\bigl\||f_l^\infty\rangle\langle g_l^\infty|
-|f_l\rangle\langle g_l|\bigr\|_1
&\le E_{\rm tail},\\
E_{\rm tail}&=u_{\rm tail}(A/s+v_{\rm tail})+v_{\rm tail}\\
&\le\frac{3C_0^2}{s^2K_+}
\le\frac{3C_0^{-6}s^2}{\lambda}\le\frac1\lambda.
\end{aligned}
\tag{13.7}
$$

中间一步使用 $A\le C_0$、$C_0\ge2$ 和原来的
$K_+\ge C_0^8\lambda s^{-4}\ge1/s$、$\lambda\ge1$；没有按 $\eta$ 改选截断。把同一分解用于范数乘积，也得到其差的绝对值之和至多 $E_{\rm tail}$。

OTF004 (26.8) 及全纯坐标变换给每个球冠内的标量 $a_l,\kappa_l$，使

$$
f_l^\infty=a_lu_{\alpha_l},\qquad
g_l^\infty=a_l\kappa_lv_{\alpha_l},\qquad
\alpha_l=\frac{\bar w_l'}{1-|w_l'|^2},\quad
w_l'=z(g_l^{-1}h)/s.
\tag{13.8}
$$

这里 $w_l'$ 是局部复坐标，区别于求积权重 $w_l$。在振幅为零处取零向量；平坦边界由连续延拓处理。因此 (13.5) 给

$$
\|\mathcal L_\eta(|f_l^\infty\rangle\langle g_l^\infty|)\|_1
=\sqrt\eta\|f_l^\infty\|\,\|g_l^\infty\|.
\tag{13.9}
$$

记 $I_\infty=\sum_l\|f_l^\infty\|\,\|g_l^\infty\|$。正交截断不增加每个范数，故由同一有限族的 (3.8) 及 (13.7)，

$$
\frac1{2s}\le I_\infty
\le\sum_l\|f_l\|\,\|g_l\|+E_{\rm tail}
\le A/s+E_{\rm tail}.
\tag{13.10}
$$

CPTP 映射对非 Hermitian 迹类算子也收缩迹范数：其伴随为保单位 CP 映射，Schwarz 不等式给算子范数收缩，再用 Schatten 范数对偶。将它用于 (13.7)，由 (13.9) 得

$$
|T_\eta-\sqrt\eta I_\infty|\le E_{\rm tail}.
\tag{13.11}
$$

结合 (13.10)、$0\le\sqrt\eta\le1$ 即为 (13.2)。证明从未除以 $\eta$，故同时覆盖零、端点一及随 $e$ 变化的透射率。所新增的估计是原固定有限球冠族在这一衰减下的交叉质量，不将 (13.4)–(13.5) 的既有通道恒等式作为新增内容。$\square$

## 14. 同一成功原生控制器的部分保留与完整返回

**定理 14.1（全部原场上的定量返回关系）。** 取原 (2.2)–(2.3) 的 $A,B_*$，并置

$$
c=192,\qquad C_{\rm part}=2\cdot768^2(A^2+B_*+2)+2,
\qquad r_1=r_0.
\tag{14.1}
$$

对每个整数 $r\ge r_1$、$e=2^{-r}$、每个公共有理 $\eta\in[0,1]$、每个定义 1.1 的原始允许场 $n$ 和每个 $h\in S^2$，定义 12.1 的同一个有限控制器在声明的有限 CP 实际端口下满足

$$
\max\left\{0,192\sqrt{\frac\eta t}-\frac{C_{\rm part}}t\right\}
\le\Delta_\eta(n,h)
\le C_{\rm part}\left(\frac1t+\sqrt{\frac\eta t}\right).
\tag{14.2}
$$

同一无条件运行还满足原四坐标成功和最坏资源界

$$
\begin{gathered}
\Pr[\|\widehat D-D_h(n)\|_\infty>e]\le2e/3,\\
T_V\le\nu_eq_e+2\le L_e,\qquad
T_{\rm reset}=15\ell_e+2\le Q_e,\qquad T_R\le\nu_eq_e+3,\\
q_e=\lceil\log_2(D_eL_e/e)\rceil,\qquad
\nu_e\le C_\nu e^{-3}\log(2t/e),\qquad \nu_eq_e\le L_e-2.
\end{gathered}
\tag{14.3}
$$

所有分支恰执行一次原规定终端，使用在 $+d e_x$ 独立重置、此前未经改动的场令牌。全部原始记录、实际副本、编译残余和新旧量子口均保留；任意原合同允许的混合旁观辅助保持原独立条件，不供应其纯化。公共程序不依赖实际 $n,h$，且对每个有理 $\eta$ 有有限存储。

证明。以下分别给出改变节点之前的准入、共同领先态、完整后缀的上下界及同一运行的成功和资源。

### 14.1 改变节点之前的完整原生比较

对每个 $k$，$\sum_jB_j^\dagger B_j$ 的第 $k$ 个对角元为
$\sum_{j=0}^k\binom{k}{j}(1-\eta)^j\eta^{k-j}=1$，非对角元为零。所以 (12.1) 在两个端点也为 CPTP。它只作用于非参考工作，且与 $L$ 读出及仅依赖 $L$ 的实际复制、解码交换。

在施行 (3.11) 之前，(6.4) 的完整逻辑等距与 $W$、固定编译因子的半 diamond 距离至多 $1/(32t)$；(7.11) 在全部相同原生历史空间上再给至多 $1/(32t)$。故先相加，再施行共同的 $\mathcal Q_\eta$ 和同一 $L$ 读出，得到

$$
D_{\rm tr}\bigl(\Gamma_\eta(\tau_h),
\Phi_\eta(\tau_h)\otimes\sigma_{e,\eta}\bigr)
\le\epsilon_e,\qquad \epsilon_e=\frac1{16t}.
\tag{14.4}
$$

这里 $\sigma_{e,\eta}$ 是 (8.4) 的固定编译、程序和独立原生记录因子，附加固定公共 $\eta$ 描述。每个标志、非投影块、停止、截止、失败分支和预留未用槽仍在比较空间内。此论证使用改变节点之前的 (6.4)、(7.11)，不反向使用约化后的 (1.7)。其 diamond 比较稳定于全部旧旁观系统。

### 14.2 同一领先态及获取返回

OTF004 (26.5)、引理 26.5 及本卷 (3.10) 对此固定族给

$$
\begin{aligned}
\Xi&=\sum_l|e_0\otimes f_l+e_1\otimes g_l/\sqrt m\rangle
\langle e_0\otimes f_l+e_1\otimes g_l/\sqrt m|
\otimes|J_l\rangle\langle J_l|,\\
\Xi&\ge0,\qquad \operatorname{Tr}\Xi\le2,\qquad
\|\Phi_{\rm keep}(\tau_h)-\Xi\|_1\le B_*/\lambda.
\end{aligned}
\tag{14.5}
$$

将 (12.1) 作用于同一个 $\Xi$，省略共同的固定 $K_{\rm work}$ 因子。令 $F_\eta,G_\eta,H_\eta$ 分别为按正交 $J_l$ 分块的
$\mathcal L_{\eta,K_0}(|f_l\rangle\langle f_l|)$、
$\mathcal L_{\eta,K_0}(|g_l\rangle\langle g_l|)$、$H_l$ 的直和，则

$$
\begin{aligned}
\Xi_\eta={}&|e_0\rangle\langle e_0|\otimes F_\eta
+\frac{|e_1\rangle\langle e_1|\otimes G_\eta}{m}
+\frac{|e_0\rangle\langle e_1|\otimes H_\eta+\mathrm{h.c.}}{\sqrt m},\\
F_\eta,G_\eta&\ge0,\quad\operatorname{Tr}F_\eta\le1,
\quad\operatorname{Tr}G_\eta\le A^2/s^2,
\quad\|H_\eta\|_1=T_\eta,\\
\Xi_\eta&\ge0,\qquad
\|\Phi_\eta(\tau_h)-\Xi_\eta\|_1\le B_*/\lambda.
\end{aligned}
\tag{14.6}
$$

允许未归一化 Hermitian $X$，仍定义
$\mathcal R_h(X)=\|X-\tau_h\otimes\operatorname{Tr}_RX\|_1/2$。由三角不等式及偏迹收缩，

$$
|\mathcal R_h(X)-\mathcal R_h(Y)|\le\|X-Y\|_1.
\tag{14.7}
$$

写 $\beta_\eta=T_\eta/\sqrt m$、$p_\eta=\operatorname{Tr}G_\eta/m\le A^2/\lambda$。在 (14.6) 中 $F_\eta$ 的乘积项与自己的边缘比较相消；激发对角项的贡献为 $p_\eta$，交叉项的贡献为 $\beta_\eta$。所以
$\mathcal R_h(\Xi_\eta)\le\beta_\eta+p_\eta$。由 (13.2)、$\lambda\ge1$、$m\ge1$、(14.4)–(14.7)，实际获取返回至多

$$
\frac{A\sqrt\eta}{\sqrt\lambda}
+\frac{A^2+B_*+2}{\lambda}+\frac1{8t}.
\tag{14.8}
$$

最后一项是 $2\epsilon_e$。将独立场采样的全部输出张量上去，再以保留原数据的等距计算最终解码器，保持领先态的交叉范数、正块迹界和迹范数比较。将这些旧口统记为 $M$，包含 $E_\eta$、混合记忆和全部原生、场及算术输出；记实际旧态为 $\rho_{\rm old}$、相应扩充后的领先态仍为 $\Xi_\eta$，则

$$
\begin{aligned}
\delta_{\rm old}:=\mathcal R_h(\rho_{\rm old})
&\le\frac{A\sqrt\eta}{\sqrt\lambda}
+\frac{A^2+B_*+2}{\lambda}+\frac1{8t},\\
\|\rho_{\rm old}-\Xi_\eta\otimes\sigma_{e,\eta}\|_1
&\le d_{\rm err}:=\frac{B_*}{\lambda}+\frac1{8t}.
\end{aligned}
\tag{14.9}
$$

后续省略共同的固定因子，其迹为一。独立场态和等距算术不引入维数损失，也不接触 $R$。

### 14.3 完整规定后缀的上界

后缀恰为 (10.9)–(10.10)。它忽略每个旧口，包括 $E_\eta$。具体地，在固定 singlet $BA$ 上作第一个新前向 $V$，在原标签基退相干 $H$，保留 $H,E$、原始符号及实际副本，只在负标签交换 $B,A$；独立重置 $F$ 于 $+d e_x$，施行 (10.9) 的固定 $\widehat\Phi$，再对其 $A$ 作第二个新前向 $V$ 及同样的标签保留。对 $B,A,F$ 作同名输出保留的 $\mathcal E$。最后于 $+d e_x$ 独立重置此前未经改动的 $S_t$，执行一次 $\exp[-idJ\cdot\sigma/m]$，对 $S_t$ 作同名保留的 $\mathcal E$。$\widehat\Phi,\mathcal E$ 的 CP、TP 性使用 OTF004 引理 17.2；不更换其实际输出。

记此完整通道为 $\mathcal S_v$，$v=n(+d e_x)$。OTF004 定理 17.3 对全部 $h,v$ 给

$$
\begin{aligned}
\|\mathcal S_v(\tau_h)-\tau_h\otimes\pi_Z\otimes\sigma_1\|_1
&<73/D,\\
\mathcal R_h(\mathcal S_v(\tau_h))&<80/D.
\end{aligned}
\tag{14.10}
$$

对 $\rho_{\rm old}$ 和它自己的乘积比较态
$\tau_h\otimes\operatorname{Tr}_R\rho_{\rm old}$ 施行同一后缀，其距离至多 $\delta_{\rm old}$。在乘积输入上，后缀的输出是
$\mathcal S_v(\tau_h)\otimes\operatorname{Tr}_R\rho_{\rm old}$；使用 (14.10)，再将比较边缘改为实际最终 $K_\eta$ 边缘，由偏迹收缩另付至多 $\delta_{\rm old}$。因此

$$
\begin{aligned}
\Delta_\eta(n,h)&\le2\delta_{\rm old}+80/D\\
&\le1536A\sqrt{\eta/t}
+\frac{2\cdot768^2(A^2+B_*+2)+5/4}{t}.
\end{aligned}
\tag{14.11}
$$

这里 $80t/D=80me^2/D<80e^2<1$。因 $A\ge1$，(14.1) 的 $C_{\rm part}$ 同时大于 $1536A$ 和 (14.11) 的余项常数，给 (14.2) 的上界。这一比较包含全部新后缀记录。

### 14.4 分离乘积、激发和交叉项的后缀下界

仅作为下界检验，在最终态中偏迹新后缀口，保留所有旧口 $M$。令 $\mathcal F_v=\operatorname{Tr}_{\rm new}\mathcal S_v$、$\gamma=\sqrt m/D$。OTF004 (26.20) 给

$$
\| (\mathcal F_v\otimes\operatorname{id}_M)(Y)-Y\|_1
\le40\gamma\|Y\|_1,
\quad\operatorname{supp}Y\subset\operatorname{span}\{e_0,e_1\}\otimes M.
\tag{14.12}
$$

其来源是 (17.12)、(22.9)–(22.11) 的等距望远镜比较：两次原生接触与终端的差分别至多 $6\gamma,6\gamma,8\gamma$，故迹范数常数为 $12+12+16=40$。算子范数界张量任意旧记忆不变；此条件只限制比较输入的支撑，不限制真实输出的降低数，也不要求纯化。

令 $P_h=|e_0\rangle\langle e_0|\otimes I_M$，将 (14.6) 写为 $Y_0+Y_1+Y_c$，依次是乘积对角项、激发对角项和 Hermitian 交叉项。三个估计分别为：由 (14.10) 的尖锐乘积界和 $\operatorname{Tr}F_\eta\le1$，$Y_0$ 经 $\mathcal F_v$ 后的 $P_h/(I-P_h)$ 交叉块范数小于 $80/D$；$Y_1\ge0$ 且迹为 $p_\eta\le A^2/\lambda$，其输出交叉块范数至多该迹；$\|Y_c\|_1=2\beta_\eta$，只对它应用 (14.12)，相对其原交叉块至多付 $80\gamma\beta_\eta$。实际约化输出相对这些项的额外迹范数误差至多 $d_{\rm err}$。所以

$$
\|P_h\operatorname{Tr}_{\rm new}(\Omega_{\eta,n,h})(I-P_h)\|_1
\ge(1-80\gamma)\beta_\eta
-\frac{A^2+B_*}{\lambda}-\frac{80}{D}-\frac1{8t}.
\tag{14.13}
$$

这里没有对整个领先态收取一个与 $\eta$ 无关的 $O(m^{-1/2})$ 误差：尖锐补偿只付给乘积项，近恒等误差只乘以衰减后的交叉质量。

原元组给
$m\ge8{,}000{,}000N_*^2-1>25600$，所以
$\gamma\le1/\sqrt m$、$1-80\gamma\ge1/2$。又 $\beta_\eta\ge0$，由 (13.2)，

$$
\begin{aligned}
\|P_h\operatorname{Tr}_{\rm new}(\Omega_{\eta,n,h})(I-P_h)\|_1
&\ge\frac{\sqrt\eta}{4\sqrt\lambda}
-\frac{A^2+B_*+1/2}{\lambda}-\frac{80}{D}-\frac1{8t}\\
&\ge192\sqrt{\eta/t}
-\frac{768^2(A^2+B_*+1/2)+9/8}{t}.
\end{aligned}
\tag{14.14}
$$

第一行也使用 $1/(2\sqrt m\lambda)\le1/(2\lambda)$。当 (13.2) 的下界为负时，先使用 $\beta_\eta\ge0$ 和 $1-80\gamma\ge1/2$，再代入该下界，故方向仍正确。

对任一归一化 $RM$ 态 $\rho$，其交叉块 $C=P_h\rho(I-P_h)$ 的极分解给一个 Hermitian、算子范数至多一的纯非对角检验，满足其在 $\rho$ 上的期望为 $2\|C\|_1$，在
$\tau_h\otimes\rho_M$ 上的期望为零。因此

$$
\mathcal R_h(\rho)\ge\|P_h\rho(I-P_h)\|_1.
\tag{14.15}
$$

偏迹新后缀口将完整乘积比较态送到该约化态自己的乘积比较态。由迹距离收缩，(14.14)–(14.15) 因而是完整 $\Delta_\eta(n,h)$ 的下界；偏迹只用于数学检验，不是控制器操作。$C_{\rm part}$ 大于 (14.14) 的余项常数，且 $\Delta_\eta\ge0$，得到 (14.2) 的下界。

### 14.5 原四坐标成功的同一运行证明

$\mathcal Q_\eta$ 保迹，所以偏迹其选定输出后，其余所有系统的联合边缘与 $\eta=0$ 完全相同，包括原生标志、$L$ 和全部实际经典记录。后续解码、场采样及规定后缀不读取 $E_\eta$ 或固定工作口。因此每个原 $n,h$ 的完整解码律恰为第 10 节的原律，而非只保证某个方向对的二元可区分性。

具体地，按原有理中心舍入取 $\widehat h(l)$，$l=0$ 或无效码取零。由 (10.3)–(10.4) 和原窗口，

$$
\Pr[\|\widehat h-h\|_\infty>e/16]
\le K_{\rm risk}/t+4\exp(-t/16384)\le e/3.
\tag{14.16}
$$

在 $0,\pm u_e e_x,\pm u_e e_y$ 的三个固定 Pauli 轴各取 $\ell_e$ 次原独立场样本，保留全部 $15\ell_e$ 枚令牌、测后态、原结果、实际副本和均值。每个场坐标估计误差至多 $eu_e/16$ 的共同好事件，其坏概率由原定义给

$$
30\exp[-\ell_e e^2u_e^2/512]\le e/3.
\tag{14.17}
$$

仍令 $\widehat n_0=\widehat n(0)$、
$\widehat v_a=[\widehat n(u_e e_a)-\widehat n(-u_e e_a)]/(2u_e)$，输出恰为

$$
\widehat D=\left(
\frac{\widehat h\cdot[\widehat n_0\times\widehat v_x]}2,
\frac{\widehat h\cdot[\widehat n_0\times\widehat v_y]}4,
0,\frac{\widehat h\cdot\widehat v_y}2\right).
\tag{14.18}
$$

所有运算有理且精确；旧两坐标解码器和其记录仍保留。轴向 $\|n_{aa}\|_2\le2$ 给中心差分偏差
$\frac1{2u_e}\int_{-u_e}^{u_e}2|v|\,dv=u_e$。故在两个好事件上，

$$
\begin{gathered}
\|\widehat h-h\|_2\le e/8,\qquad
\|\widehat n_0-n(0)\|_2\le e^2/64,\qquad
\|\widehat v_a-n_a(0)\|_2\le e/4,\\
\|\widehat h\|_2,\|\widehat n_0\|_2,\|\widehat v_a\|_2\le2.
\end{gathered}
\tag{14.19}
$$

对 $a=x,y$，展开叉积并用 $\|n(0)\|_2=1$、$\|n_a(0)\|_2\le1$，除以二或四之前的误差至多
$e/8+2(2e^2/64+e/4)\le11e/16$；最后一个点积的误差至多
$\bigl(e/8+2(e/4)\bigr)/2=5e/16$。所以四坐标误差分别至多
$11e/32,11e/64,0,5e/16$，全部小于 $e$。坏事件并集至多 $2e/3$，不要求两个好事件独立。完整后缀保迹且不改已保存解码边缘，故这一成功断言与 (14.2) 是同一无条件运行、全部原始 $n,h$ 上的联合合同。

### 14.6 最坏分支资源、完整口与有限公共描述

唯一改变的 (12.1) 是非参考节点，不增加 $V$、场重置或终端。每个正、逆、受控逻辑字母仍以一个新 $q_e$ 截止前向原生字支付，所有历史和未用槽保留。由定理 7.2，获取至多用 $\nu_eq_e\le L_e-2$ 次 $V$，不使用场重置或终端；原全场部分使用 $15\ell_e$ 次重置、零次 $V$；后缀增加两次 $V$、两次独立重置及恰一次规定终端。于是 (14.3) 成立，其中 $18N_e\ge15\ell_e+1$。没有免费逆、额外直接 $R$ 接触、后选择或期望次数代替最坏分支次数。

最终 $K_\eta$ 包含同名固定工作口、被动 $E_\eta$、测后 $L$ 和全部 $J_l$ 成分；频率、探针、控制、奇偶、投影相位、内外层标志及非投影残余；每个原生槽的 $H,E$、原始 $X$ 读数、实际副本、使用和奇偶位、停止/成功/截止/失败/计数及预留空白口；全部旧混合记忆、程序和路由；全部场令牌、测后态、样本、均值、差分、四坐标解码器、旧解码器和算术工作；以及后缀的 $B,A,F,S_t$、两组新 $H,E$、原始符号及其实际副本、程序、路由、工作和固定替换后的同名量子输出。各式中的数学约化都不是遗漏实际输出的操作。

写 $\eta=p/q$ 为既约分数，$0\le p\le q$、$q\ge1$。可用恰
$(K_0+1)(K_0+2)/2$ 个平方根有理系数及其指标、公共 $\eta$ 精确描述 (12.1)；系数平方的分子、分母分别为

$$
\binom{k}{j}p^{k-j}(q-p)^j,\qquad q^k.
\tag{14.20}
$$

分子位数至多 $1+K_0(1+\lceil\log_2(q+1)\rceil)$，分母位数至多
$1+K_0\lceil\log_2(q+1)\rceil$。包括索引和端点约定，一个保守的固定描述界为

$$
B_\eta=64(K_0+2)^3
\bigl(\lceil\log_2(q+1)\rceil+\lceil\log_2(K_0+2)\rceil+1\bigr)
\quad\text{比特}.
\tag{14.21}
$$

因此获取空间可在 (8.3) 右端另乘 $K_+2^{B_\eta}$；同名 $K_{\rm work}$ 已在原界内，新 $K_+$ 因子只计 $E_\eta$。公共描述作为固定保留程序因子，不是新随机结果。任意原混合旁观空间的维数仍原样乘在相同比较两边；场和规定后缀保留其原有限因子。原合同没有记忆维数上限，故每个允许参数都有有限实现描述。这里的平方根有理节点是声明的有限 CP 数学操作，不蕴含有效门数、运行时间、能量或额外物理浴的实现结论。

全部常数保持固定，(2.8) 已给 $\lambda\ge\max\{1,A^2,2C_{\rm fail}\}$、原成功风险窗口和原生预算窗口，所以上述证明不需要扩大 $r_0$。这完成 (14.1)–(14.3) 的全部量词。$\square$

## 15. 部分保留族的尺度消费者及适用范围

**推论 15.1（同一族中一阶返回的充要条件）。** 沿任意允许的二进精度序列 $e\to0$ 和任意公共有理透射率序列 $\eta_e\in[0,1]$，对定义 12.1 的同一族、同一原成功解码器和同一规定后缀，

$$
\sup_{n,h}\Delta_{\eta_e}(n,h)=O(1/t_e)
\quad\Longleftrightarrow\quad
\eta_et_e\text{ 有界}.
\tag{15.1}
$$

必要性更强：沿任意选定的原始允许 $n_e,h_e$ 序列，只要
$\Delta_{\eta_e}(n_e,h_e)=O(1/t_e)$，就已有 $\eta_et_e$ 有界。若 $\eta_et_e\to\infty$，则对全部原始 $n,h$ 一致有

$$
\Delta_{\eta_e}(n,h)=\Theta\!\left(\sqrt{\eta_e/t_e}\right).
\tag{15.2}
$$

证明。若 $\eta_et_e\le M$，(14.2) 给
$t_e\Delta_{\eta_e}(n,h)\le C_{\rm part}(1+\sqrt M)$。反之，若沿某个允许 $n_e,h_e$ 序列有 $t_e\Delta_{\eta_e}(n_e,h_e)\le M$，同一逐点下界给

$$
192\sqrt{\eta_et_e}\le M+C_{\rm part},\qquad
\eta_et_e\le\left(\frac{M+C_{\rm part}}{192}\right)^2.
\tag{15.3}
$$

渐近 $O$ 界只要求尾部，有限前缀的 $t_e$ 和 $\eta_e$ 也有限，故等价成立。若 $\eta_et_e\to\infty$，将 (14.2) 除以 $\sqrt{\eta_e/t_e}$，则下界余项为
$C_{\rm part}/\sqrt{\eta_et_e}\to0$，上界为
$C_{\rm part}(1+1/\sqrt{\eta_et_e})$。特别地，其一致下极限至少为 $192$，给 (15.2)。这为命题 11.1 的保留/约化接口比较提供指定部分保留模型中的完整量化关系；原成功概率、资源和全部自身边缘仍属同一运行。$\square$

**命题 15.2（比较族、基线与来源的边界）。** (14.2)–(15.2) 只约束定义 12.1 的固定有限族和规定完成，不给所有允许控制器的分类或最优性，也不从 OTF004 (19.11) 推出逐点正 $1/t$ 下界。$\eta=0$ 时本结论只给零下界和 $O(1/t)$ 上界；$\eta=1$ 时保留的相干工作在新口上。原生控制器的端口语义、OTF004 §27 的原消费者及本卷第 1–11 节保持各自的声明范围。

证明。(14.2) 的下界对每个原 $n,h$ 成立，但其余项允许 $\eta=0$ 时下界为零。OTF004 (19.11) 则是原控制器比较类的最坏情形下确界 $R(e)$ 的逆 $D_e e^2$ 基线；最坏情形的下界不蕴含每个 $n,h$ 上的同一下界。推论 15.1 的必要性来自 (14.2) 的逐点交叉估计，不使用这样的基线替换。两个端点由 (12.1) 的精确公式得到，不能据此单独推出中间 $\eta$ 的结论；中间族需要 (13.6)–(13.11) 及 (14.13) 的分离估计。

所用真空衰减、位移及一光子恒等式为前引 `literature-attested` 结果；固定球冠截断的 $\eta$ 一致交叉界、改变节点之前的完整原生桥、规定后缀后的逐点返回及原全场消费者的组合是这里的 `repo-derived` 数学应用，不作历史原创性断言。其假设明确选定有限 CP 节点的实际输出，并未给另一个生成额外浴的酉实现证明同一界，亦不声称时间、门、物理来源或宇宙本体结论。$\square$

## 追加锚（本行以下为增补区）

## 16. 原均匀任务的最坏实际重置必要量

**定义 16.1（原合同与实际计数）。** 精度遍历每个正有理数 $0<e\le e_0=1/100$，公共元组严格取 (1.1)，即

$$
\begin{aligned}
u_e&=e/8,&
k_e&=\left\lceil2048e^{-2}\log(18/e)\right\rceil,&
\ell_e&=\left\lceil32768e^{-4}\log(90/e)\right\rceil,\\
N_*&=8{,}388{,}608{,}000,&
N_e&=\max\left\{N_*,\left\lceil\frac{3k_e+2}{10}\right\rceil,
\left\lceil\frac{15\ell_e+1}{18}\right\rceil\right\},\\
D_e&=\left\lceil\max\{8{,}000{,}000N_e^2,9k_e/e\}\right\rceil,&
m_e&=D_e-1=2j_e,&M_e=L_e&=10N_e,&Q_e&=18N_e+1.
\end{aligned}
\tag{16.1}
$$

所有对数均为自然对数。公共参数保持 $d=1/64$、$\tau_0=1$、$r=1/4$、$B_{\rm field}=2$、$G=1$。场遍历 [OTF004 定义 19.1](OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md) 的全部 $C^2$、秩二映射 $n:U\to S^2$：开集 $U$ 包含两条完整闭半径 $1/4$ 坐标轴段，且在这些轴段上 $\|n_{aa}(t e_a)\|_2\le2$（$a=x,y$），在原点 $\|n_x(0)\|_2,\|n_y(0)\|_2\le1$。目标保持 (1.3) 的四个原系数。

对每个 $e$ 及其精确元组，比较每个原合同允许的有限因果控制器及有限解码器；允许任意有限混合辅助、量子和经典记忆、纠缠、反馈、先前输出及探针回用。参考 $R=\operatorname{Sym}^{m_e}(\mathbb C^2)$ 只准备一次，初态 $\tau_h$ 与其余输入独立，是唯一含未知 $h\in S^2$ 的输入。除声明的场源外，全部准备、设备参数、控制和解码程序均与实际 $n,h$ 无关；场信息只通过声明的独立新鲜点重置供给。与 $R$ 的接触保持至多 $L_e$ 次 (1.4) 的 forward $V$，以及恰一次规定终端
$U_{\rm term}=\exp[-id\tau_0J\cdot\sigma/m_e]$；终端使用在 $+d e_x$ 独立重置、此前未经改动的原场令牌。其余操作在原始标记 $R$ 上恒等，不直接读取、旋转、拆分、重置、替换或恢复 $R$，不增加未知射线反射或终端逆。

控制器自己的完整实际非参考口仍为 $K$：包括全部实际探针、场令牌、原生相干 $H,E$、原始记录及实际副本、测量输出及实际环境、记忆、程序、路由、计数器、算术和解码工作、补偿及终端输出。声明 CP 节点的形式 Kraus 指标和证明纯化不自动成为实际输出；另行产生的实际系统必须纳入 $K$。不供应混合辅助的纯化。

成功假设严格为同一个原四坐标解码器对全部上述 $n$、全部 $h\in S^2$ 同时满足

$$
\Pr\!\left[\|\widehat D-D_h(n)\|_\infty\le e\right]\ge1-e.
\tag{16.2}
$$

令 $q_{\rm reset}(e)\le Q_e$ 为该控制器跨全部允许场、方向及执行分支的最大实际总重置次数，包含补偿及规定终端所需的每次重置。这是确定的最坏次数，不是期望次数或可用上限；也不是 (1.6) 中表示实现位长的 $q_e$。

对正迹类算子使用不补缺失质量项的根保真度

$$
F(A,B)=\|\sqrt A\sqrt B\|_1
=\operatorname{Tr}\sqrt{\sqrt A B\sqrt A}.
\tag{16.3}
$$

归一化态的平方保真度为 $F(A,B)^2$；纯态满足 $F(|u\rangle\langle u|,|v\rangle\langle v|)=|\langle u,v\rangle|$。次归一化历史块也使用同一 (16.3)。正规经典—量子直积分使用 [PB §281.5](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md) 式 (281.24) 的块根保真度积分约定。

**定理 16.2（原全场成功的重置必要量）。** 对每个定义 16.1 的正有理精度和每个满足 (16.2) 的原控制器，取绝对常数 $c=1/4096$，有精确整数必要界

$$
\boxed{
q_{\rm reset}(e)\ge
\left\lceil\frac{\log(1/[4e(1-e)])}{-2\log\cos(32e^2)}\right\rceil
\ge\frac1{4096}e^{-4}\log(1/e).
}
\tag{16.4}
$$

以下显式全局场对在同一个 $h_0=(0,1,0)$ 上的完整实际最终态 $\Omega_+,\Omega_-$（空间为原来的 $R\otimes K$）还满足

$$
F(\Omega_+,\Omega_-)\ge g_e^{q_{\rm reset}(e)},
\qquad g_e=\cos(32e^2).
\tag{16.5}
$$

因而对这两个完整实际态作任意二元检验，其等先验错误率 $p$ 都满足

$$
p\ge\frac{1-\sqrt{1-g_e^{2q_{\rm reset}(e)}}}{2}.
\tag{16.6}
$$

这是对每个原全场一致成功控制器的必要陈述；两场检验本身不构成全场成功构造。

证明。固定任意上述 $e$ 及控制器。

### 16.1 同一全局域上的合法场对

令

$$
\begin{aligned}
H(t)&=\frac{t}{1+t^2},&
f_\pm(x)&=\frac x4\pm64e^2H\!\left(\frac{x}{16e}\right),&
v(y)&=\frac14\arctan y,\\
N(u,v)&=(\cos v\sin u,\sin v,\cos v\cos u),&
n_\pm(x,y)&=N(f_\pm(x),v(y)),&U&=\mathbb R^2.
\end{aligned}
\tag{16.7}
$$

两个场在同一个整个 $\mathbb R^2$ 上光滑且为单位向量。直接微分给

$$
H'(t)=\frac{1-t^2}{(1+t^2)^2},\qquad
H''(t)=\frac{2t(t^2-3)}{(1+t^2)^3}.
\tag{16.8}
$$

由 $2|t|\le1+t^2$ 和 $|1-t^2|\le1+t^2$，有 $|H|\le1/2$、$|H'|\le1$，且

$$
|H''(t)|\le
\frac{2|t|}{1+t^2}\frac{t^2+3}{(1+t^2)^2}\le3.
\tag{16.9}
$$

所以在全部 $x$ 上

$$
f_\pm'(x)=\frac14\pm4eH'\!\left(\frac{x}{16e}\right)
\in[21/100,29/100],\qquad
f_\pm''(x)=\pm\frac14H''\!\left(\frac{x}{16e}\right),
\quad |f_\pm''|\le3/4.
\tag{16.10}
$$

另有

$$
v'(y)=\frac1{4(1+y^2)}>0,\qquad
v''(y)=-\frac{y}{2(1+y^2)^2},\qquad
|v'|\le1/4,\quad |v''|\le1/4,\quad |v|<\pi/8.
\tag{16.11}
$$

$N_u,N_v$ 正交，范数分别为 $\cos v>0$、$1$。由 $f_\pm'>0$、$v'>0$，两场在每个有限点的两个偏导线性无关，故在 $U$ 上处处秩二；不要求全局单射。

在整个 $x$ 轴上 $v(0)=0$、$\|N_u\|=\|N_{uu}\|=1$，故

$$
\|(n_\pm)_{xx}(x,0)\|_2
\le3/4+(29/100)^2=8341/10000<1<2.
\tag{16.12}
$$

在整个 $y$ 轴上 $f_\pm(0)=0$、$\|N_v\|=\|N_{vv}\|=1$，故

$$
\|(n_\pm)_{yy}(0,y)\|_2\le1/4+1/16=5/16<2.
\tag{16.13}
$$

原点的精确值为

$$
n_\pm(0)=(0,0,1),\qquad
(n_\pm)_x(0)=(1/4\pm4e,0,0),\qquad
(n_\pm)_y(0)=(0,1/4,0).
\tag{16.14}
$$

原点导数范数分别至多 $29/100$、$1/4$，均不超过 $G=1$。因此两场满足原始两条完整闭半径 $1/4$ 轴段上的每项几何承诺，并有严格余量。

### 16.2 原目标的严格分离及全位置响应重叠

取同一个 $h_0=(0,1,0)$，两次运行的初始参考 $\tau_{h_0}$ 相同。将 (16.14) 代入原目标 (1.3)，不更换任何系数，得到

$$
D_{h_0}(n_\pm)=(1/8\pm2e,0,0,1/8).
\tag{16.15}
$$

第一坐标及无穷范数分离都恰为 $4e>2e$。原闭 $e$ 成功球不相交；把原实际解码结果按 $\widehat D_1>1/8$ 报告为 $+$，否则报告为 $-$，其每个条件错误率都不超过 $e$：在 $+$ 成功事件上 $\widehat D_1\ge1/8+e$，在 $-$ 成功事件上 $\widehat D_1\le1/8-e$。这是 (16.2) 的必要后果，不替换原成功任务。

对全部 $z=(x,y)\in\mathbb R^2$，令

$$
\Delta(x)=f_+(x)-f_-(x)=128e^2H\!\left(\frac{x}{16e}\right),
\qquad |\Delta(x)|\le64e^2.
\tag{16.16}
$$

两 Bloch 向量的内积为 $\sin^2v+\cos^2v\cos\Delta$。声明的响应 $\rho_\pm(z)=(I+n_\pm(z)\cdot\sigma)/2$ 是纯 qubit 态，因而

$$
\begin{aligned}
F(\rho_+(z),\rho_-(z))^2
&=\frac{1+n_+(z)\cdot n_-(z)}2\\
&=1-\cos^2v(y)\sin^2(\Delta(x)/2)\\
&\ge\cos^2(32e^2).
\end{aligned}
\tag{16.17}
$$

这里 $0<32e^2\le2/625<1/2$，所以 $g_e=\cos(32e^2)>0$，且每个位置的根保真度至少为 $g_e$。在 $(x,y)=(16e,0)$ 取等号，故 $g_e$ 是这对响应在整个共同域上的精确下确界。偏轴、远处、自适应选择的位置和规定终端位置均在同一界内，没有限制合法查询地点。

### 16.3 声明新鲜来源的完整使用端口

OTF004 定义 13.1、19.1 中实际使用的来源输入是经典请求点 $z$，声明的量子输出恰为独立新鲜 qubit $\rho_n(z)$。固定 $z$ 时，这个态供应节点是没有旧量子记忆输入的准备通道

$$
T_{n,z}:\mathbb C\longrightarrow B(\mathbb C^2),
\qquad \lambda\longmapsto\lambda\rho_n(z).
\tag{16.18}
$$

这是对已声明使用端口的识别，不是从某个未指定物理供应者的 qubit 边缘推出其全部通道律。

在该边界把 $R$、全部先前实际输出和量子记忆合记为 $M$。独立新鲜供应作用为 $\operatorname{id}_M\otimes T_{n,z}$；在相同经典请求标签 $z$ 条件下，假设 $b\in\{+,-\}$ 的完整使用输出块为

$$
\tau_{b,z}\otimes\rho_b(z).
\tag{16.19}
$$

$\tau_{b,z}$ 是该假设的整个实际次归一化旧记忆块，其迹已经包含自己的请求和历史概率。纯度也核对这一因子化：正联合态若 qubit 边缘为秩一投影 $\rho_b(z)$，则其支撑在 $M\otimes\operatorname{range}\rho_b(z)$，从而与该 qubit 分解；旧记忆边缘不变则来自来源没有旧量子记忆输入。这个论证不判定任何额外供应者端口。

请求生成、路由、允许的覆盖和实际地址记录属于新鲜供应前后的共同、场无关控制器 CP 操作。经典请求可依赖任意先前量子仪器及经典反馈；未测量的相干 $H,E$ 及其它量子系统留在 $M$，不被改称为经典历史。相干点地址 oracle 需要另给来源在地址非对角块上的作用，声明的点重置没有提供该访问。

有限或可数标签的完整供应态为 (16.19) 对 $z$ 的直和。正规连续经典标签取两种实际请求和历史律的共同支配测度 $\mu$，使用可测正迹类密度场 $\tau_b(z)$；完整使用态相对于 $\mu$ 的密度为 $\tau_b(z)\otimes\rho_b(z)$。不假设两假设历史权重相等，也不假设条件量子态相等。

每个控制器节点实际生成的全部系统属于其完整输出 CP 映射，留在 $M$ 或实际后继寄存器。准备、原生门及设备均与实际场无关，故这些完整输出映射在两场下是同一映射；其输出态可因输入不同而不同。代数 Kraus 标签和证明纯化不创建实际输出。若另一个供应者实际导出额外场相关寄存器，则不能在证明中删去它；那是不同于 (16.18) 的来源接口。

### 16.4 复用 PB281.5 于完整混合记忆及最坏停止

直接使用 PB §281.5 式 (281.23)–(281.25)：假设取 $b=\pm$，经典查询标签取实际请求点或决定该点的完整已有经典请求和历史标签，响应取 $\sigma_b(z)=\rho_b(z)$，量子记忆取上述整个实际 $M$，统一响应根保真度取 $g_e$。式 (281.23) 的这次参数代入为

$$
\sum_zF(\tau_{+,z},\tau_{-,z})F(\rho_+(z),\rho_-(z))
\ge g_e\sum_zF(\tau_{+,z},\tau_{-,z}).
\tag{16.20}
$$

正规连续情形将同一代入用于 (281.24) 的积分，保留实际且可不相等的历史权重。这是已有经典—量子自适应机制的使用，不另立通用查询定理。

两次完整初态相同：同一个 $\tau_{h_0}$、同一个可混合辅助态、同一场无关设备和程序，初始根保真度为一。每个间隔中的完整输出控制器仪器及 forward $V$ 都是共同 CPTP 映射，保留其全部实际相干和经典输出，故根保真度不能下降。混合辅助、旁观系统、纠缠旧输出、工作寄存器和回用探针始终作为实际密度算子传递，不接入它们的纯化。

规定终端也保持恰一次原来的共同算子 $\exp[-id\tau_0J\cdot\sigma/m_e]$；在 $+d e_x$ 供应其新鲜未改动令牌的重置是一项已计数响应，适用全位置 (16.17)。全部补偿、记录处理和解码节点同样按其完整共同映射处理。

$q_{\rm reset}(e)$ 是确定的最大实际调用数，适用 PB281.5 的确定最大次数停止条款。等价地，已停止历史在比较递推中接恒等步骤，保真度因子为一，活动历史的因子至少为 $g_e$。这只补齐数学比较，不增加任何物理重置或输出，也不改用期望预算。因此 (281.25) 给出 (16.5)，比较空间仍是原始整个 $R\otimes K$，没有替换为约化或挑选输出。

### 16.5 原错误上限、二元判别及显式常数

对完整实际态作任意二元读出，令
$\alpha=\Pr(-\mid+)$、$\beta=\Pr(+\mid-)$、$p=(\alpha+\beta)/2$。数据处理和经典 Cauchy–Schwarz 给

$$
\begin{aligned}
g_e^{q_{\rm reset}(e)}
&\le F(\Omega_+,\Omega_-)\\
&\le\sqrt{(1-\alpha)\beta}+\sqrt{\alpha(1-\beta)}\\
&\le\sqrt{(\alpha+\beta)(2-\alpha-\beta)}
=2\sqrt{p(1-p)}.
\end{aligned}
\tag{16.21}
$$

若 $p\le1/2$，解这个二次不等式即得 (16.6)；若 $p>1/2$，(16.6) 自动成立。§16.2 从原四坐标解码器取得的阈值检验满足 $p\le e<1/2$，所以

$$
g_e^{2q_{\rm reset}(e)}\le4p(1-p)\le4e(1-e).
\tag{16.22}
$$

$0<g_e<1$，取对数得 (16.4) 中的比值下界，实际最坏次数是整数，故可取上整。这里使用的失败率上限仍为原来的 $e$。

为核对统一常数，对 $0\le\theta\le1/2$，$\sin\theta\le\theta$ 及 $\cos\theta\ge1-\theta^2/2\ge1/2$ 给 $\tan\theta\le2\theta$；积分得到

$$
-\log\cos\theta\le\theta^2,\qquad
-2\log\cos(32e^2)\le2048e^4.
\tag{16.23}
$$

又因 $e\le1/100<1/16$，

$$
\log\frac1{4e(1-e)}\ge\log\frac1{4e}
\ge\frac12\log\frac1e.
\tag{16.24}
$$

分子、分母在全部窗口内均为正，合并 (16.23)–(16.24) 得 $c=1/4096$、$e_0=1/100$ 的 (16.4)，覆盖每个原正有理精度而非一个子列。$\square$

### 16.6 同一重置阶的消费者、来源及边界

OTF004 式 (19.4) 的已有全场成功证书在每个原正有理 $0<e\le1/100$ 上实际使用 $15\ell_e+2$ 次重置，包括补偿和规定终端。它与 (16.4) 给重置这一资源坐标相同的 $e^{-4}\log(1/e)$ 阶。本卷第 1、8、10 节在定理 1.2 声明的二进精度窗口上保留同一场采样数及两次重置的规定完成，全部场令牌、原始结果、实际副本、算术、原生及后缀口仍在自己的完整实际输出中。这些既有上界及构造直接复用，不作新证明，也不把本节必要量换成一次只在两场成功的构造。

本节没有使用或推出实际返回误差的界。重置中的对数来自原失败率 $e$ 的必要置信度；它不恢复 OTF004 §27 已否定的有限 CP 全比较类通用返回对数因子，也不改变本卷第 12–15 节固定部分保留族的适用范围。重置次数不等同于参考接触成本、物理供应成本、时间或时钟成本。

(16.3) 及共同通道根保真度不减所用的成熟来源为 Chefles、Jozsa、Winter，*On the existence of physical transformations between sets of quantum states*，[arXiv:quant-ph/0307227v1](https://arxiv.org/html/quant-ph/0307227v1)，引言的保真度约定和 Lemma 1(a)。该文采用未平方的根保真度，方向为共同 CPTP 变换后保真度不减；不使用 Lemma 1(b) 的纯输入成对变换判据，不向控制器供应额外比较处理器或其环境。

正规连续标签的框架对应 Berta、Furrer、Scholz，*The Smooth Entropy Formalism for von Neumann Algebras*，[arXiv:1107.5460v3](https://arxiv.org/html/1107.5460v3)，§II.2 的正规完全正保单位 Heisenberg 动力学及其预对偶通道、§III.2 式 (16)–(17) 的保真度与单调性。该文采用平方保真度，本节取其正平方根；自适应步骤使用的是已有 PB (281.23)–(281.25)，不把这篇文献称为独立的连续自适应查询定理。这些工具为 `literature-attested`；本节显式全局两场、全位置响应界及对原消费者的完整端口代入为 `repo-derived` 数学应用，不声称穷尽文献或历史原创性。

来源范围严格是 (16.18) 的整个声明使用端口。具有额外场相关输出、场相关时序输出、与旧控制器记忆相互作用、相干量子点地址访问或另行未知场输入的较大供应者，需要不同来源合同及新的比较，不能仅凭其 qubit 边缘与本节相同而移用结论。实际控制器环境始终保留，证明纯化及形式 Kraus 指标不被添加为实际端口；本节不构成所有物理环境实现的断言，也不给出物理准备、来源或时钟的实现界。混合输入下实际完整等距输出的精度问题仍未解决；重置必要量不宣告返回最优性或整个原量子纯理论目标完成。

## 追加锚（本行以下为增补区）

## 17. 实际有限混合酉输出的对数旋转模反例

**定义 17.1（精确原曲线与完整实际酉比较类）。** 精度始终取 [OTF004 定义 19.1](OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md) 的正有理域 $0<e\le1/100$，并逐项保留其取整和最大值：

$$
\begin{aligned}
k_e&=\left\lceil2048e^{-2}\log(18/e)\right\rceil,
&\ell_e&=\left\lceil32768e^{-4}\log(90/e)\right\rceil,\\
N_*&=8{,}388{,}608{,}000,
&N_e&=\max\left\{N_*,\left\lceil\frac{3k_e+2}{10}\right\rceil,
                 \left\lceil\frac{15\ell_e+1}{18}\right\rceil\right\},\\
D_e&=\left\lceil\max\{8{,}000{,}000N_e^2,9k_e/e\}\right\rceil,
&m_e&=D_e-1,\qquad t_e=m_e e^2.
\end{aligned}
\tag{17.1}
$$

对数均为自然对数。令 $R_e=\operatorname{Sym}^{m_e}(\mathbb C^2)$，$\tau_h=|e_h\rangle\langle e_h|$。相干向量、归一球面积和有限 Toeplitz 矩阵沿用 OTF004 式 (14.7)、(25.14)–(25.16)：

$$
e_z=(1+|z|^2)^{-m/2}(|0\rangle+z|1\rangle)^{\otimes m},\qquad
d\mu(z)=\frac{dA(z)}{\pi(1+|z|^2)^2},\qquad
T_m(f)=(m+1)\int_{S^2}f(h)\tau_h\,d\mu(h).
\tag{17.2}
$$

$\rho_\alpha$ 表示 $z\mapsto e^{i\alpha}z$ 的球面旋转。此处积分只定义有限矩阵的各个条目，不是获取原语、连续物理寄存器或额外输入。

取任意有限 $P,K$、独立于 $h$ 的混合态 $\sigma\in\mathcal D(P)$ 和独立于 $h$ 的完整实际等距 $U:R_e\otimes P\to R_e\otimes K$。其整个声明输出及其自身实际边缘为

$$
\Omega_h=U(\tau_h\otimes\sigma)U^\dagger,\qquad
\omega_h=\operatorname{Tr}_R\Omega_h,\qquad
\delta=\sup_hD_{\rm tr}(\Omega_h,\tau_h\otimes\omega_h),\qquad
D_{\rm tr}(X,Y)=\tfrac12\|X-Y\|_1.
\tag{17.3}
$$

$K$ 包括这一实现的全部实际输出；不加入输入纯化、形式 Kraus 寄存器或证明环境，也不丢弃实际生成的系统。所考察的统一充分旋转关系是：存在绝对常数 $C$，对上述每个 $e,\sigma,U$ 均有

$$
\int_{S^2}D_{\rm tr}(\omega_{\rho_{32e}h},\omega_h)^2\,d\mu(h)
\le C(t_e\delta^2+\delta).
\tag{17.4}
$$

这个完整等距比较类宽于带有原生操作、预算及成功解码要求的原始消费者类。OTF004 定理 14.1 的完整实际输出与混合压缩语义保持原样；其反足方向估计不等于 (17.4)。

**定理 17.2（奇异混合输入的有限酉旋转反例；repo-derived）。** 令 $J=2^j\ge128$，$s=e_J=1/J$，$m=m_J=D_{1/J}-1$ 严格按 (17.1) 取值，$\alpha=32/J$，$N=(J+1)^2$。存在 $P_J=K_J$、维数 $2N$，独立于 $h$ 的奇异混合态 $\sigma_J$ 和独立于 $h$ 的有限酉 $U_J$，使 (17.3) 的同一实际输出满足

$$
0<\delta_J\le\frac{C_0}{J^2\sqrt{m_J}},\qquad
\int_{S^2}D_{\rm tr}(\omega_{\rho_{32/J}h},\omega_h)^2\,d\mu(h)
\ge c\frac{(\log J)^2}{J^6}
\tag{17.5}
$$

对全部充分大的二进 $J$ 成立，其中 $c,C_0>0$ 为绝对常数。因此

$$
\frac{\displaystyle\int_{S^2}D_{\rm tr}(\omega_{\rho_{32/J}h},\omega_h)^2\,d\mu(h)}
     {(m_J/J^2)\delta_J^2+\delta_J}
\ge c' (\log J)^2\longrightarrow\infty.
\tag{17.6}
$$

特别地，(17.4) 的统一绝对常数不存在。$\sigma_J$ 的秩为 $N$，有 $N$ 个特征值 $1/N$ 及 $N$ 个零特征值；结论不要求输入满秩。以下所有 $c,C$ 均为可随估计改变的正绝对常数，不依赖 $J,m,w,h$。

证明。先给出全部有限矩阵。取

$$
\begin{aligned}
W_J&=\{\tfrac12+a/J+i(-\tfrac12+b/J):a,b=0,\ldots,J\},\\
P_J=K_J&=\mathbb C^{W_J}\otimes\mathbb C^2,\qquad
\sigma_J=\frac1N\sum_{w\in W_J}|w,0\rangle\langle w,0|,\\
\zeta_w(z)&=\frac{z-w}{1+\overline w z},\qquad
f_w(h)=\frac{s^2\overline{\zeta_w(h)}}{s^2+|\zeta_w(h)|^2},\qquad
A_w=T_m(f_w).
\end{aligned}
\tag{17.7}
$$

在 $\zeta_w=\infty$ 处取连续延拓。令 $\eta=1/\zeta_w$，则该处的表达为 $s^2\eta/(1+s^2|\eta|^2)$，故 $f_w$ 在整个球面实解析，且 $|f_w|\le s/2$。在 $R\otimes\mathbb C^2$ 上置

$$
H_w=A_w\otimes|1\rangle\langle0|+A_w^\dagger\otimes|0\rangle\langle1|,
\qquad U_w=e^{iH_w},\qquad U_J=\bigoplus_{w\in W_J}U_w.
\tag{17.8}
$$

直和保持实际标签 $w$。$H_w$ 自伴，故 $U_J$ 是 $R\otimes P_J$ 到整个 $R\otimes K_J$ 的有限酉。(17.2) 的保单位完全正性给 $\|A_w\|\le s/2$。这些公式指定每个有限矩阵条目，参数只依赖公开的 $J,m,w$，不依赖实际 $h$；没有 $R\otimes K_J$ 以外的生成系统。

### 17.1 第一步：统一标量估计与格点和

写 $g_s(\zeta)=s^2\overline\zeta/(s^2+|\zeta|^2)$，$r=|\zeta|$。直接求导得

$$
\partial_{\overline\zeta}g_s=\frac{s^4}{(s^2+r^2)^2},\qquad
\partial_\zeta g_s=-\frac{s^2\overline\zeta^{2}}{(s^2+r^2)^2}.
\tag{17.9}
$$

其内禀二阶导数统一不超过 $C/s$：在 $r\le2s$ 用 $g_s(\zeta)=s g_1(\zeta/s)$；在 $s\le r\le1$ 对上述有理函数求导；在 $r\ge1$ 则用 $|\eta|\le1$ 上的 $g_s=s^2\eta/(1+s^2|\eta|^2)$。同样三个区域给统一的一阶导数界。

在以 $h$ 为中心的旋转相干坐标中，令 $a_w(h),b_w(h)$ 分别为 $f_w$ 在坐标原点的反全纯及全纯导数绝对值。若 $d=d(h,w)$ 为球面距离，则 $r=\tan(d/2)$，坐标变换导数绝对值为 $1+r^2$，因而

$$
\begin{aligned}
a_w(h)&=(1+r^2)\frac{s^4}{(s^2+r^2)^2}
       \le C\min\{1,(s/d)^4\},\\
b_w(h)&=(1+r^2)\frac{s^2r^2}{(s^2+r^2)^2}
       \le C\min\{1,(s/d)^2\},\\
|f_w(h)|&\le C\min\{s,s^2/d\}.
\end{aligned}
\tag{17.10}
$$

在 $d=0$ 处按连续意义解释；反足处用倒数坐标。格点位于固定有界球极投影矩形，故球面间距至少 $cs$。由互不相交的小球冠，任意 $h$ 的距离 $R$ 邻域内格点数至多 $C(1+(R/s)^2)$。按 $d\asymp2^ks$ 的二进环带求和，(17.10) 分别给 $C2^{-2k}$ 和 $Cs2^{-k}$ 的环带上界，最内球冠占据数有统一界。于是对整个球面统一有

$$
\sum_{w\in W_J}a_w(h)\le C,\qquad
\sum_{w\in W_J}|f_w(h)|b_w(h)\le Cs.
\tag{17.11}
$$

### 17.2 第二步：定量相干向量估计

固定 $w,h$，选任一相干向量 $e_h$，在以 $h$ 为中心的旋转相干坐标 $\xi$ 中作 Taylor 展开：

$$
f_w(\xi)=f_w(h)+p_w\xi+q_w\overline\xi+R_w(\xi),\qquad
|q_w|=a_w(h),\quad |p_w|=b_w(h),\quad
|R_w(\xi)|\le\frac C s|\xi|^2.
\tag{17.12}
$$

当 $|\xi|\le1$ 时，余项界来自固定正则坐标中的 Taylor 定理和第一步的二阶导数界；当 $|\xi|\ge1$ 时，由 $f_w$ 的上确界及一阶导数界得到同一全局界。

复用 (17.2) 的相干分解 $(m+1)\int\tau_\xi\,d\mu=I$。在这一坐标的归一 Dicke 基中，角向及径向矩给

$$
T_m(\xi)e_0=0,\qquad
T_m(\overline\xi)e_0=\frac1{\sqrt m}e_1,
\tag{17.13}
$$

其中 $e_1$ 为第一归一 Dicke 激发。这里对非有界坐标函数只使用所显示的收敛有限矩阵积分。由 $|\langle e_\xi,e_0\rangle|=(1+|\xi|^2)^{-m/2}$ 及三角不等式，

$$
\begin{aligned}
\|T_m(R_w)e_0\|
&\le\frac C s(m+1)\int_0^\infty u(1+u)^{-m/2-2}\,du\\
&=\frac C s\frac{4(m+1)}{m(m+2)}
\le\frac{4C}{ms}.
\end{aligned}
\tag{17.14}
$$

因此对每个 $w,h$，

$$
\begin{aligned}
r_w(h)&:=\|(A_w-f_w(h)I)e_h\|
       \le\frac{a_w(h)}{\sqrt m}+\frac C{ms},\\
r'_w(h)&:=\|(A_w^\dagger-\overline{f_w(h)}I)e_h\|
       \le\frac{b_w(h)}{\sqrt m}+\frac C{ms}.
\end{aligned}
\tag{17.15}
$$

第二式是对 $\overline{f_w}$ 作同一计算。旋转坐标在此只用于计算矩阵恒等式，不施行物理旋转。

### 17.3 第三步：精确酉比较与完整自身边缘返回

对复数 $f$，定义

$$
h_f=f|1\rangle\langle0|+\overline f|0\rangle\langle1|,\qquad
v_f=e^{ih_f}|0\rangle,\qquad
\psi_{w,h}=U_w(e_h\otimes|0\rangle),\qquad
\epsilon_w(h)=\|\psi_{w,h}-e_h\otimes v_{f_w(h)}\|.
\tag{17.16}
$$

在固定嵌入 $E_hv=e_h\otimes v$ 上，以 Duhamel 恒等式比较 $e^{iH_w}$ 和二维演化 $e^{ih_f}$。精确公式

$$
e^{iuh_f}|0\rangle
=\cos(u|f|)|0\rangle
 +i\sin(u|f|)\frac f{|f|}|1\rangle
\tag{17.17}
$$

在 $f=0$ 处按连续意义取值。$|0\rangle$ 分量的嵌入残差为 $r_w$，$|1\rangle$ 分量为 $r'_w$，而 $\int_0^1|\sin(u|f|)|\,du\le|f|/2$，故

$$
\epsilon_w(h)\le r_w(h)+\frac{|f_w(h)|}{2}r'_w(h),\qquad
E_J:=\sup_h\frac1N\sum_w\epsilon_w(h)
\le\frac C{N\sqrt m}+\frac C{ms}.
\tag{17.18}
$$

末步使用 (17.11)、(17.15) 和 $|f_w|\le s/2$。

只作数学比较的态及真正实际态为

$$
\nu_h=\frac1N\bigoplus_w|v_{f_w(h)}\rangle\langle v_{f_w(h)}|,\qquad
\Omega_h=\frac1N\bigoplus_w|\psi_{w,h}\rangle\langle\psi_{w,h}|.
\tag{17.19}
$$

直和迹范数可加，纯态迹距离不超过向量距离，故

$$
D_{\rm tr}(\Omega_h,\tau_h\otimes\nu_h)\le E_J,\qquad
D_{\rm tr}(\omega_h,\nu_h)\le E_J,\qquad
\delta_J\le2E_J.
\tag{17.20}
$$

第二式用偏迹收缩性，第三式用三角不等式。这一返回比较使用同一实际边缘 $\omega_h$，没有用 $\nu_h$ 替换定义 (17.3)。除在 $\omega_h$ 的定义中对 $R$ 取偏迹外，没有丢弃任何输出；$\nu_h$ 不是另行供应的实际态。

### 17.4 第四步：精确原曲线的余项控制与正返回缺陷

由 (17.1) 的原样定义，

$$
\ell_{1/J}\ge32768J^4\log(90J),\qquad
N_{1/J}\ge\tfrac56\ell_{1/J},\qquad
D_{1/J}\ge8{,}000{,}000N_{1/J}^2.
\tag{17.21}
$$

特别地 $m_J\ge8{,}000{,}000N_{1/J}^2-1\ge4{,}000{,}000N_{1/J}^2$，所以对 $J\ge2$，

$$
\sqrt{m_J}\ge J^4\log J\ge J^3,\qquad
\frac J{m_J}\le\frac1{J^2\sqrt{m_J}}.
\tag{17.22}
$$

这些只是精确取整定义的后果，不将 $m_J$ 换成渐近替代量。因 $N=(J+1)^2\ge J^2$，(17.18)–(17.22) 给

$$
\delta_J\le\frac{C_0}{J^2\sqrt{m_J}}.
\tag{17.23}
$$

还须排除零分母。在 $h=w$ 的中心 Dicke 基中，$f_w$ 的径向角形式使 $A_w$ 为加权升移位，且

$$
A_we_0=a e_1,\qquad A_w^\dagger e_1=a e_0,\qquad
0<a=(m+1)\sqrt m\int_0^\infty
\frac{s^2u}{s^2+u}(1+u)^{-m-2}\,du\le s/2.
\tag{17.24}
$$

积分严格为正，上界也由 $\|A_w\|\le s/2$ 得到。相应不变二维子空间上的实际 $w$ 分支输出为
$\cos(a)e_0|0\rangle+i\sin(a)e_1|1\rangle$。完整混合输出中，效果 $(I_R-\tau_w)\otimes I_K$ 检出至少 $\sin^2(a)/N>0$ 的泄漏，而 $\tau_w\otimes\omega_w$ 的该效果概率为零。故 $\delta_J\ge\sin^2(a)/N>0$。

### 17.5 第五步：小 qubit 态保留复标量差

若 $|f|,|g|\le s/2$ 且 $J$ 充分大，则

$$
D_{\rm tr}(|v_f\rangle\langle v_f|,|v_g\rangle\langle v_g|)
\ge\tfrac12|f-g|.
\tag{17.25}
$$

事实上，$|v_f\rangle\langle v_f|$ 的左下非对角条目为 $iM(f)$，其中

$$
M(f)=f\frac{\sin(2|f|)}{2|f|}.
\tag{17.26}
$$

将 $M$ 看作实二维径向映射，其切向和径向微分特征值分别是 $\sin(2r)/(2r)$ 和 $\cos(2r)$，在 $r\le1/10$ 上均至少 $1/2$。沿连接 $f,g$ 的线段积分，强单调性及 Cauchy–Schwarz 给 $|M(f)-M(g)|\ge|f-g|/2$。两 qubit 态的迹距离至少为其非对角条目之差的绝对值，故得 (17.25)。保留标签的正交性遂给

$$
D_{\rm tr}(\nu_h,\nu_g)\ge\frac1{2N}\sum_{w\in W_J}|f_w(h)-f_w(g)|.
\tag{17.27}
$$

### 17.6 第六步：固定正面积片上的对数分离

取固定球面片

$$
\mathcal A=\{h:7/8\le\operatorname{Re}z\le9/8,
                         \ |\operatorname{Im}z|\le1/8\}.
\tag{17.28}
$$

其归一面积为固定正数。写 $z'=e^{i\alpha}z$，则对所有充分大的 $J$，在 $\mathcal A$ 上统一有 $c\alpha\le|z'-z|\le2\alpha$。离开 $w$ 写

$$
\begin{aligned}
f_w(z)&=F_w(z)+B_w(z),\\
F_w(z)&=s^2\frac{1+\overline w z}{z-w}=\frac{s^2}{\zeta_w(z)},\\
B_w(z)&=-\frac{s^4}{\zeta_w(z)(s^2+|\zeta_w(z)|^2)}.
\end{aligned}
\tag{17.29}
$$

主项满足精确恒等式

$$
|F_w(z')-F_w(z)|
=\frac{s^2(1+|w|^2)|z'-z|}{|z'-w|\,|z-w|}.
\tag{17.30}
$$

固定一个充分大的绝对数 $R$。若

$$
r\le|z-w|\le2r,\qquad Rs\le r\le1/16,
\tag{17.31}
$$

则从 $z$ 到 $z'$ 的整个线段到 $w$ 的距离与 $r$ 可比，且其上的 $|1+\overline w z|$ 有正绝对下界。这里 $|z'-z|\le2\alpha=64s$，故一个固定的大 $R$ 即可保证线段分离。沿此线段对 $B_w$ 求导给

$$
|B_w(z')-B_w(z)|\le C\frac{s^4|z'-z|}{r^4}.
\tag{17.32}
$$

取同一固定 $R$ 足够大，使 $C/R^2$ 小于 (17.30) 主项下界常数的一半，便有

$$
|f_w(z')-f_w(z)|\ge c\frac{s^2\alpha}{r^2}
\tag{17.33}
$$

对全部 (17.31) 环带、所有 $z\in\mathcal A$ 统一成立。$R$ 不依赖 $J,m,z$。

还须给出环带内格点的下界，而非仅上界。对 $r\ge R/J$，每个 $r\le|w-z|\le2r$ 环带包含至少 $cJ^2r^2$ 个格点。给每个格点配一个边长 $1/J$ 的正方形；环带中这些格点的方形覆盖内缩环带
$r+\sqrt2/J\le|u-z|\le2r-\sqrt2/J$，当固定 $R$ 足够大时其面积至少 $cr^2$。因 $z\in\mathcal A$ 且 $2r\le1/8$，所有相关环带和格点均在 (17.7) 的格点矩形内，边界不损失这个计数。

在 $R/J$ 与 $1/16$ 之间取互不相交的二进环带；例如隔一个二进尺度取一次，保证边界无重叠计数。对充分大的 $J$，可取至少 $c\log J$ 个，且可将计数阈值取为 $J\ge(16R)^2$ 后再增大一个绝对阈值。每个环带由 (17.33) 贡献至少
$c s^2\alpha J^2=c\alpha$，从而在整个 $\mathcal A$ 上

$$
\sum_{w\in W_J}|f_w(\rho_\alpha h)-f_w(h)|\ge c\alpha\log J.
\tag{17.34}
$$

### 17.7 第七步：实际完整输出的旋转下界

将 (17.27)、(17.34) 与两个端点各自的 (17.20) 合并，对 $h\in\mathcal A$ 得

$$
D_{\rm tr}(\omega_{\rho_\alpha h},\omega_h)
\ge\frac{c\alpha\log J}{N}-2E_J.
\tag{17.35}
$$

此处 $\alpha=32/J$，$N=(J+1)^2\le4J^2$，并且由 (17.18)、(17.22)，

$$
E_J\le\frac C{J^2\sqrt{m_J}}\le\frac C{J^6\log J}.
\tag{17.36}
$$

所以存在一个有限绝对阈值 $J_0$，包含上述标量、格点及余项阈值，使每个二进 $J\ge J_0$ 的 (17.35) 右侧至少为 $c\log J/J^3$。在固定正面积片 $\mathcal A$ 上积分即得

$$
\int_{S^2}D_{\rm tr}(\omega_{\rho_\alpha h},\omega_h)^2\,d\mu(h)
\ge c\frac{(\log J)^2}{J^6}.
\tag{17.37}
$$

这是实际完整 $K_J$ 输出态的估计，所有混合标签及两态寄存器都仍在输出中。

### 17.8 第八步：无界比值与精确反驳范围

同一实际 $\delta_J$ 满足 (17.23)，故用 $t_J=m_J/J^2$ 得

$$
\begin{aligned}
t_J\delta_J^2+\delta_J
&\le\frac{C_0^2}{J^6}+\frac{C_0}{J^2\sqrt{m_J}}\\
&\le\frac{C_0^2+C_0}{J^6}
\end{aligned}
\tag{17.38}
$$

对充分大的 $J$ 成立。(17.24) 使分母严格为正，(17.37)–(17.38) 于是给

$$
\frac{\displaystyle\int_{S^2}D_{\rm tr}(\omega_{\rho_{32/J}h},\omega_h)^2\,d\mu(h)}
     {t_J\delta_J^2+\delta_J}
\ge\frac{c(\log J)^2}{C_0^2+C_0}\longrightarrow\infty.
\tag{17.39}
$$

每个 $J$ 都有限，$e_J=2^{-j}$ 属于原正有理精度域，$m_J$ 是精确原维数，$U_J$ 为实际完整有限酉，$\sigma_J$ 为允许的奇异混合态。因此不存在 (17.4) 所要求的统一绝对常数。整个论证不使用跨方向 Gram 恒等式，也未删除混合展开的任一跨方向交叉项。$\square$

**命题 17.3（原置信度解码分离与反例的消费者边界）。** 保持 OTF004 定义 19.1 的全部原合同：对全部允许场 $n$、全部 $h$，同一有理四坐标解码器达到原目标 (19.2) 的 $e$ 精度，失败率 $\beta\le e$；原生菜单、最坏 $L_e,Q_e$、一次准备参考、独立来源、全部实际输出及规定终端均不改变。固定合法场

$$
n_*(x,y)=(x,y,\sqrt{1-x^2-y^2})
\tag{17.40}
$$

于半径 $1/3$ 的开圆盘，其原目标第一坐标为 $h_y/2$。对任何满足上述成功条件的消费者，置 $\alpha=32e$。在归一面积 $1/4$ 的球冠 $\mathcal C=\{h:h_x\ge1/2\}$ 上，其同一实际输出必有

$$
D_{\rm tr}(\omega_{\rho_\alpha h},\omega_h)\ge1-2e.
\tag{17.41}
$$

定理 17.2 只否定较大的完整等距类上的 (17.4)，不由此给出原始成功消费者的返回下界、反例或全部场成功构造。

证明。场 (17.40) 及其原目标、秩和导数条件逐项复用 OTF004 式 (19.2) 与推论 19.2 的证明。对 $h\in\mathcal C$，$0<\alpha\le0.32$，同一几何分离为

$$
(\rho_\alpha h)_y-h_y
\ge\tfrac12\sin\alpha-(1-\cos\alpha)
\ge\tfrac\alpha2-\tfrac{\alpha^3}{12}-\tfrac{\alpha^2}{2}
>\tfrac\alpha4.
\tag{17.42}
$$

故第一目标坐标相差大于 $\alpha/8=4e>2e$，两个闭 $e$ 成功球不交。同一原解码器在两个输入的各自成功球中均有至少 $1-e$ 的概率，因而由迹距离的数据处理得 (17.41)。这个效果只是对已有实际解码输出的数学检验，不供应新的读出操作。使用的是原来的 $\beta\le e$，没有将其换成 $2e/3$。

定理 17.2 的输入与酉属于 (17.3) 的普遍比较类，但它们的有限矩阵存在性不蕴含原生合成。该构造没有提供原有菜单下的最坏分支 $L_e/Q_e$ 证书、全部允许 $n,h$ 上成功的原四坐标解码器，或携带未改动且独立的 $+d e_x$ 原场令牌的规定终端；不从中取得直接参考控制、物理参数旋转、逆操作、场源或时钟接口。因此它既不反驳原 $\beta\le e$ 返回命题，也不完成原全场任务。未补齐这些共同实现条件的 $\beta\le2e/3$ 数值断言不能充作原成功消费者；本节不建立这一无条件消费者蕴含。

若要对合格的原始成功完整等距消费者推出 $\delta\ge c/(e\sqrt{m_e})$，仍须使用该成功子类的额外约束，或另一个正确的充分关系；(17.41) 保持可用，(17.4) 不能承担此推理。OTF004 推论 19.2 的较弱 Hilbert 能量估计不被替换成 $m\delta^2$。本卷既有有限 CP、部分保留及新鲜点重置结果的各自假设和结论保持原范围。

本节的承重新增内容是 (17.7)–(17.39) 的同一有限混合酉构造及统一纸面估计，标为 `repo-derived`；相干 Toeplitz 分解及保单位 CP 范数界复用 OTF004 (25.14)–(25.16)，完整等距和混合压缩语义复用其定理 14.1，精确原曲线及成功解码球冠复用其定义 19.1、推论 19.2。Taylor 余项、Duhamel 恒等式、迹范数收缩与正交直和可加性、平面格点计数只作为这些新推导中的经典中间工具，不单列为新增定理。该数学结论不包含原生实现、物理来源、时钟实现或历史原创性断言。信息—扰动与非对称性广播的相关引文为 Kretschmann–Schlingemann–Werner，[arXiv:quant-ph/0605009v1](https://arxiv.org/html/quant-ph/0605009v1)，Theorem 3、式 (32)–(35)，及 Marvian–Spekkens，[arXiv:1812.08766v2](https://arxiv.org/html/1812.08766v2)，Theorem 1、Proposition 2、Lemma 4；这些条目仅作相关文献定位，不承担本定理的前提，也不作为 (17.4) 的依据。$\square$

## 追加锚（本行以下为增补区）

## 18. 混合完整等距输出的二值置信度与精度返回界

**定义 18.1（精确原曲线、完整实际等距及共同效果）。** 对每个正有理数 $0<e\le1/100$，逐项使用 [OTF004 定义 19.1](OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md) 及本卷 (1.1) 的原曲线，所有对数均为自然对数：

$$
\begin{aligned}
k_e&=\left\lceil2048e^{-2}\log(18/e)\right\rceil,
&\ell_e&=\left\lceil32768e^{-4}\log(90/e)\right\rceil,\\
N_*&=8{,}388{,}608{,}000,
&N_e&=\max\left\{N_*,\left\lceil\frac{3k_e+2}{10}\right\rceil,
                    \left\lceil\frac{15\ell_e+1}{18}\right\rceil\right\},\\
D_e&=\left\lceil\max\{8{,}000{,}000N_e^2,9k_e/e\}\right\rceil,
&m_e&=D_e-1,\\
L_e&=10N_e,
&Q_e&=18N_e+1.
\end{aligned}
\tag{18.1}
$$

置 $m=m_e$、$R=\operatorname{Sym}^{m}(\mathbb C^2)$，$\tau_h$ 是方向 $h\in S^2$ 的归一自旋相干纯态。取任意有限维 Hilbert 空间 $P,K$，任意独立于 $h$ 的密度算子 $\sigma\in\mathcal D(P)$，以及独立于 $h$ 的等距

$$
U:R\otimes P\longrightarrow R\otimes K.
\tag{18.2}
$$

右端必须是这个实现的整个实际输出。$\sigma$ 可以奇异，不限制秩、非零谱或辅助维数，不供应它的纯化。每个实际产生的非参考系统均在 $K$ 内；没有删除输出，也不把形式 Stinespring 环境或 Kraus 指标当作实际生成系统。定义

$$
\begin{aligned}
\Omega_h&=U(\tau_h\otimes\sigma)U^\dagger,
&\omega_h&=\operatorname{Tr}_R\Omega_h,\\
\delta&=\sup_{h\in S^2}\frac12
 \|\Omega_h-\tau_h\otimes\omega_h\|_1,
&D_{\rm tr}(\rho,\eta)&=\tfrac12\|\rho-\eta\|_1.
\end{aligned}
\tag{18.3}
$$

上确界包括全部 $h$，包括下面两条置信带之间的方向；每个比较态使用该输出自身的实际边缘。二值置信度条件是：存在同一个独立于 $h$ 的效果 $0\le E\le I_K$，使

$$
\begin{aligned}
\operatorname{Tr}(E\omega_h)&\ge1-e
&&\text{对每个 }h_y\ge4e,\\
\operatorname{Tr}(E\omega_h)&\le e
&&\text{对每个 }h_y\le-4e.
\end{aligned}
\tag{18.4}
$$

这里的效果只是对同一输出的数学条件，没有给原控制器增加读出、参考旋转、逆操作或协变性假设。

**定理 18.2（混合完整等距的二值置信度精度界）。** 在定义 18.1 的全部条件下，对每个正有理 $0<e\le1/100$，

$$
\delta\ge
\frac{2/3-2e}{1+144e\sqrt{m_e}/\sqrt{1-16e^2}}
\ge\frac1{512e\sqrt{m_e}}.
\tag{18.5}
$$

常数与 $\dim P$、$\dim K$、$\operatorname{rank}\sigma$、$\sigma$ 的非零特征值及 $E$ 无关。以下给出完整有限维证明；混合压缩及其反全纯导数基线复用 OTF004 定理 14.1 的 (14.4)–(14.8)，局部有界符号估计同时利用符号范数和导数范数。

证明。

### 18.1 混合压缩与两个交叉块

固定 $\tau_h=|v_h\rangle\langle v_h|$ 的归一代表，置

$$
V_h=U(v_h\otimes I_P)=v_h\otimes F_h+B_h,
\qquad (\langle v_h|\otimes I_K)B_h=0.
\tag{18.6}
$$

$V_h$ 是等距，正交分解后的堆叠算子
$W_h=\binom{F_h}{B_h}:P\to K\oplus(v_h^\perp\otimes K)$ 也是等距。因此

$$
F_h^\dagger F_h+B_h^\dagger B_h=I_P,
\qquad \|F_h\|\le1.
\tag{18.7}
$$

令 $\Pi_h=\tau_h\otimes I_K$、$q_h=\operatorname{Tr}(B_h\sigma B_h^\dagger)$。对 (18.3) 的两个态测量效果 $I-\Pi_h$，第二个态在该效果上的概率为零，故 $q_h\le\delta$。置
$T_h=\Omega_h-\tau_h\otimes\omega_h$，则 $\|T_h\|_1\le2\delta$。用自伴酉 $S_h=2\Pi_h-I$ 提取非对角块：

$$
\operatorname{offdiag}(T_h)=\frac{T_h-S_hT_hS_h}{2},
\qquad \|\operatorname{offdiag}(T_h)\|_1\le2\delta.
\tag{18.8}
$$

两个非零块互为伴随，其中一个为
$C_h=(v_h\otimes F_h)\sigma B_h^\dagger$。自伴非对角矩阵的迹范数是 $2\|C_h\|_1$，左乘等距保持奇异值，所以

$$
\|F_h\sigma B_h^\dagger\|_1\le\delta,
\qquad \|B_h\sigma F_h^\dagger\|_1\le\delta.
\tag{18.9}
$$

再用 $W_h$ 的等距性、伴随的迹范数相同以及两个堆叠块的三角不等式，得到

$$
\begin{aligned}
\|B_h\sigma\|_1
&=\|\sigma B_h^\dagger\|_1
 =\|W_h\sigma B_h^\dagger\|_1\\
&\le\|F_h\sigma B_h^\dagger\|_1
     +\|B_h\sigma B_h^\dagger\|_1\\
&\le\delta+q_h\le2\delta.
\end{aligned}
\tag{18.10}
$$

此处没有使用 $\sigma^{-1}$，所以奇异混合态不需要另行处理。

### 18.2 同一实际边缘与有界符号

对 $R$ 偏迹消去 (18.6) 的两个交叉项，给出

$$
\omega_h=F_h\sigma F_h^\dagger+Z_h,
\qquad Z_h=\operatorname{Tr}_R(B_h\sigma B_h^\dagger)\ge0,
\qquad \operatorname{Tr}Z_h=q_h\le\delta.
\tag{18.11}
$$

对任意 $h,g$，展开

$$
F_h\sigma F_h^\dagger-F_g\sigma F_g^\dagger
=(F_h-F_g)\sigma F_h^\dagger
 +F_g\sigma(F_h^\dagger-F_g^\dagger).
$$

由 (18.7) 及伴随的迹范数相同，两项的迹范数均不超过
$\|(F_h-F_g)\sigma\|_1$。因此

$$
\begin{aligned}
\tfrac12\|F_h\sigma F_h^\dagger-F_g\sigma F_g^\dagger\|_1
&\le\|(F_h-F_g)\sigma\|_1,\\
D_{\rm tr}(\omega_h,\omega_g)
&\le\|(F_h-F_g)\sigma\|_1+\delta.
\end{aligned}
\tag{18.12}
$$

最后一项来自 $(q_h+q_g)/2\le\delta$，未以比较边缘替换任一个实际 $\omega_h$。

### 18.3 维数无关的反全纯导数界

选任一固定正交 qubit 基底，在对应球极投影坐标上写

$$
\begin{aligned}
v(z)&=(1+|z|^2)^{-m/2}(|0\rangle+z|1\rangle)^{\otimes m},\\
F(z)&=(\langle v(z)|\otimes I_K)U(v(z)\otimes I_P),
\qquad A(z)=F(z)\sigma.
\end{aligned}
\tag{18.13}
$$

由收缩性及 $\|\sigma\|_1=1$，$\|A(z)\|_1\le1$。采用
$\partial_{\bar z}=(\partial_x+i\partial_y)/2$，令
$t(z)=(I-\tau_z)\partial_zv(z)$。归一张量幂的微分给

$$
\partial_{\bar z}v(z)=-\frac{mz}{2(1+|z|^2)}v(z),
\qquad \|t(z)\|=\frac{\sqrt m}{1+|z|^2}.
\tag{18.14}
$$

在 $F$ 的微分中，bra 与 ket 的平行项相消，留下的正交 bra 恰给

$$
\partial_{\bar z}F(z)=(\langle t(z)|\otimes I_K)B_z.
$$

于是 (18.10) 给出

$$
\|\partial_{\bar z}A(z)\|_1
\le\frac{2\delta\sqrt m}{1+|z|^2}
\le2\delta\sqrt m.
\tag{18.15}
$$

这些是每个有限坐标圆盘上的光滑有限维矩阵值符号。固定基底的选择只改变证明坐标，不是在实现中旋转参考，也不要求 $U$ 协变。

### 18.4 局部有界符号的边界与面积估计

设 $A$ 是闭圆盘 $\{|z|\le r\}$ 上的有限维迹类矩阵值 $C^1$ 函数，且
$\sup\|A\|_1\le1$、$\sup\|\partial_{\bar z}A\|_1\le L$。对 $a$ 满足 $d_a=|a|<r$，逐矩阵元的 Cauchy–Pompeiu 公式为 $A(z)=H(z)-T(z)$，其中

$$
\begin{aligned}
H(z)&=\frac1{2\pi i}\int_{|\zeta|=r}
            \frac{A(\zeta)}{\zeta-z}\,d\zeta,\\
T(z)&=\frac1\pi\int_{|\zeta|<r}
            \frac{\partial_{\bar\zeta}A(\zeta)}{\zeta-z}\,dA(\zeta).
\end{aligned}
\tag{18.16}
$$

边界核的差为 $a/[\zeta(\zeta-a)]$。把迹范数放入积分，利用边界长度 $2\pi r$ 及 $|\zeta-a|\ge r-d_a$，得

$$
\|H(a)-H(0)\|_1
\le\frac1{2\pi}(2\pi r)\frac{d_a}{r(r-d_a)}
=\frac{d_a}{r-d_a}.
\tag{18.17}
$$

面积项在原点满足

$$
\|T(0)\|_1
\le\frac L\pi\int_{|\zeta|<r}\frac{dA(\zeta)}{|\zeta|}
=2Lr.
\tag{18.18}
$$

原圆盘包含于以 $a$ 为中心、半径 $r+d_a$ 的圆盘；在后者上积分
$1/|\zeta-a|$ 恰为 $2\pi(r+d_a)$，故

$$
\|T(a)\|_1\le2L(r+d_a).
\tag{18.19}
$$

合并三个估计，得到这个局部关系的全部常数：

$$
\|A(a)-A(0)\|_1
\le\frac{d_a}{r-d_a}+2L(2r+d_a).
\tag{18.20}
$$

对 (18.13)–(18.15) 取 $r=4d_a>0$、$L=2\delta\sqrt m$，即有

$$
\|A(a)-A(0)\|_1
\le\frac13+36\delta\sqrt m\,d_a.
\tag{18.21}
$$

边界积分的固定加项 $1/3$ 保留在式中；这里没有断言 (17.4) 的无条件平方旋转估计。

### 18.5 同一个效果在两条置信带端点上的应用

取

$$
h_-=(\sqrt{1-16e^2},-4e,0),
\qquad h_+=(\sqrt{1-16e^2},4e,0).
\tag{18.22}
$$

由同一个 $E$ 及迹距离的变分表示，

$$
D_{\rm tr}(\omega_+,\omega_-)
\ge\operatorname{Tr}[E(\omega_+-\omega_-)]\ge1-2e.
\tag{18.23}
$$

两方向的球面夹角是 $\theta=2\arcsin(4e)$。在 (18.13) 中选择一个固定基底，使 $h_-$ 的坐标为 $0$，$h_+$ 的坐标为正实数

$$
a=d_a=\tan(\theta/2)=\frac{4e}{\sqrt{1-16e^2}}.
\tag{18.24}
$$

因为 (18.3) 对全部方向取上确界，(18.15) 在半径 $4d_a$ 的整个圆盘上成立，包括落在两置信带之间的点。(18.12)、(18.21) 及 (18.23) 于是给

$$
1-2e\le\delta+\frac13+36\delta\sqrt m\,d_a.
\tag{18.25}
$$

移项即得

$$
\delta\ge\frac{2/3-2e}{1+36\sqrt m\,d_a}
=\frac{2/3-2e}{1+144e\sqrt m/\sqrt{1-16e^2}},
\tag{18.26}
$$

这是 (18.5) 的较强中间界。全置信带假设在这里供应两个端点，没有引入新的解码器。

### 18.6 全部有理精度域与显式绝对常数

对每个 $0<e\le1/100$，有 $\sqrt{1-16e^2}\ge4/5$，所以 $d_a\le5e$，并且 $2/3-2e\ge1/2$。令 $x=e\sqrt m$。精确原曲线满足
$\log(18/e)>1$、$k_e\ge2048e^{-2}$，且 $m=D_e-1\ge9k_e/e-1$，从而

$$
me^2\ge9k_e e-e^2\ge18432/e-e^2>1,
\qquad x\ge1.
\tag{18.27}
$$

故 (18.26) 的分母至多

$$
1+36\sqrt m\,d_a\le1+180x\le181x\le256x.
$$

结合分子至少 $1/2$，得到

$$
\delta\ge\frac{1/2}{256x}=\frac1{512e\sqrt{m_e}}.
\tag{18.28}
$$

推导没有渐近替换 $m_e$，没有缩小精度窗口，也没有区间延拓或辅助谱限制。$\square$

**命题 18.3（原有理四坐标解码器的必要效果及条件消费者界）。** 保持 OTF004 定义 19.1 和本卷定义 1.1 的全部原合同：同一原解码器对全部允许场 $n$ 和全部 $h$ 达到 $e$ 精度，失败率 $\beta\le e$。在半径 $1/3$ 的开圆盘上取已有合法场

$$
n_*(x,y)=(x,y,\sqrt{1-x^2-y^2}),
\qquad D_h(n_*)=(h_y/2,-h_x/4,0,h_y/2).
\tag{18.29}
$$

同一原解码器的事件 $\{\widehat D_1>0\}$ 在其既有实际输出上的拉回是一个共同效果 $E$，满足 (18.4)。若这个消费者在 $n_*$ 的同一个完整实际实现确实具有 (18.2) 的独立于 $h$ 的等距及独立混合初始化 $\sigma$，并且右端 $R\otimes K$ 就是其全部实际输出，则

$$
\overline\delta\ge\delta_{n_*}
\ge\frac{2/3-2e}{1+144e\sqrt{m_e}/\sqrt{1-16e^2}}
\ge\frac1{512e\sqrt{m_e}},
\tag{18.30}
$$

其中 $\delta_{n_*}=\sup_hD_{\rm tr}(\Omega_{n_*,h},\tau_h\otimes\omega_{n_*,h})$，$\overline\delta$ 仍为同一消费者的原全部场、全部方向最坏返回误差。

证明。场的合法性和 (18.29) 的目标逐项复用 OTF004 推论 19.2：前两坐标保证秩二，原点两轴导数范数为一，闭 $1/4$ 轴段上二阶导数范数为 $(1-t^2)^{-3/2}<2$。在原 $e$ 精度成功事件上，

$$
\begin{aligned}
h_y\ge4e&\ \Longrightarrow\quad
 \widehat D_1\ge h_y/2-e\ge e>0,\\
h_y\le-4e&\ \Longrightarrow\quad
 \widehat D_1\le h_y/2+e\le-e<0.
\end{aligned}
\tag{18.31}
$$

原失败率至多 $e$，所以事件的两条概率界正是 (18.4)。事件及原解码器均固定，故它在既有 $K$ 上的效果不依赖 $h$。这只是已有解码事件的分析，不供应二元最优检验或额外原生读出。对另有实际完整等距条件的同一实现应用定理 18.2，并用原最坏场上确界包括 $n_*$，即得 (18.30)。

本命题的原消费者仍使用 (18.1) 的全部取整、最大值和最坏分支预算 $L_e,Q_e$，以及原生前向 $V$ 菜单；参考只准备一次，是唯一含未知 $h$ 的输入，并与非参考初始完整律独立。任意有限独立混合辅助继续允许，不提供纯化。规定终端仍恰为
$U_{\rm term}=\exp[-id\tau_0J\cdot\sigma/m_e]$，$d=1/64$、$\tau_0=1$，使用在 $+d e_x$ 独立重置且此前未被改动的原场令牌。全部实际探针、场令牌、原生 $H,E$、原始记录、实际副本、记忆、程序、计数器、路由、工作空间、补偿和终端输出继续留在该实现自己的最终 $K$ 内，每个返回比较仍使用自己的实际边缘。证明中的基底变换与积分不属于控制操作。本命题没有构造控制器，也没有给出新的原生预算证书。$\square$

**命题 18.4（旋转反例的置信度诊断与完整接口边界）。** 定理 17.2 的具体有限混合酉族不满足 (18.4)。定理 18.2 及命题 18.3 不恢复 (17.4)，也不把声明约化 CPTP 实现自动变成实际完整等距实现。

证明。在 (17.7)–(17.8) 的该族中，$e=e_J=1/J$ 且 $\|H_w\|\le e/2$，故整个直和酉满足

$$
\|U_J-I\|\le e/2.
\tag{18.32}
$$

对任意输入密度算子 $\rho$，展开
$U_J\rho U_J^\dagger-\rho=(U_J-I)\rho U_J^\dagger+\rho(U_J^\dagger-I)$，得到

$$
D_{\rm tr}(U_J\rho U_J^\dagger,\rho)
\le\|U_J-I\|\le e/2.
\tag{18.33}
$$

取 $\rho=\tau_h\otimes\sigma_J$ 并偏迹，因未作用的输入 $K_J$ 边缘为 $\sigma_J$，有

$$
D_{\rm tr}(\omega_h,\sigma_J)\le e/2,
\qquad D_{\rm tr}(\omega_h,\omega_g)\le e
\quad\text{对每个 }h,g.
\tag{18.34}
$$

但共同效果的两条置信带要求端点距离至少 $1-2e>e$，所以这个族不能满足 (18.4)。这条诊断直接来自已有构造的范数界，不是定理 18.2 的前提。定理 17.2 对无条件积分平方旋转关系 (17.4) 的反驳完整保留；(18.20)–(18.21) 含固定加项，只在宏观置信跳变下给出 (18.25)，不承担原平方旋转关系。

声明约化 CPTP 消费者仅有其声明的实际端口。为其命名一个形式 Stinespring 环境不能满足 (18.2) 的整个实际输出条件；若另一个实现确实产生额外输出，必须将它们纳入 $K$，并对扩大的输出自身实际边缘重新比较。只有同一个原实现确实具有所需独立初始化与完整等距接口时，(18.30) 才适用。本卷第 1–11 节的有限 CP 供应者、第 12–15 节的固定部分保留族、第 16 节的新鲜点重置必要量及 OTF004 的既有约化 CP 结果，均保留各自前提和结论。

本节不构造实际原生来源、时钟、总因果历史或规定终端实现，不增加参考控制、逆操作、来源或读出能力，不给出匹配的最优常数或上界构造。R5、C133、PB 读支持及 Bargmann 有序分支结果不承担这里的精度、物理来源或完整返回前提。原全部场、原生菜单、终端、资源及来源的完整目标不由此完成；对缺少实际完整等距桥的原约化 CP 消费者没有推出 (18.30)。在本定理的精确前提内，(18.28) 排除任何满足 $e\sqrt{m_e}\,\delta\to0$ 的序列。$\square$

定理 18.2 中的混合压缩、两个交叉块和反全纯导数控制对应 OTF004 定理 14.1 的 (14.4)–(14.8)，实际边缘分解对应 (14.10)–(14.11)；精确曲线、原成功合同和 $n_*$ 目标对应其定义 19.1、推论 19.2。本节的承重新增推导为 `repo-derived`：(18.16)–(18.21) 在与端点间距成比例的圆盘上同时使用 $\|F\sigma\|_1\le1$ 和线性于 $\delta$ 的导数界，以至多 $1/3$ 的边界贡献留下固定置信跳变，再由 $d_a=O(e)$ 得到 $1/e$ 因子。它不同于 OTF004 定理 14.1 的反足全局积分和推论 19.2 的 Hilbert 能量估计。Cauchy–Pompeiu 公式是经典中间工具，所需矩阵迹范数、边界和面积常数已在 (18.16)–(18.20) 中直接给出；本节不作历史原创性或穷尽文献断言。

相关文献的指标与前提各守其范围。Kretschmann–Schlingemann–Werner，[arXiv:quant-ph/0605009v1](https://arxiv.org/html/quant-ph/0605009v1)，Theorem 3、式 (31)–(35)，讨论全通道 cb 范数比较及指定互补 Stinespring 通道，不供应本节的相干输入完整自身边缘返回前提。自旋相干信息—扰动文献 [arXiv:quant-ph/0610246v2](https://arxiv.org/html/quant-ph/0610246v2)，引言及 §III 的式 (8)–(10)，采用操作与估计的平均保真度及协变仪器条件；Marvian–Spekkens，[arXiv:1812.08766v2](https://arxiv.org/html/1812.08766v2)，Theorem 1、Proposition 2、Lemma 4，涉及协变与精确保留；[arXiv:2606.18040v2](https://arxiv.org/html/2606.18040v2)，摘要及引言的信号与操作保真度定义，涉及反平行自旋相干对。这些条目仅是相关数学文献，不将其平均指标、协变性、精确保留或不同输入族迁移为 (18.2)–(18.4) 的假设，也不承担 (18.5) 的证明。

## 追加锚（本行以下为增补区）

## 19. 固定同探针槽与仅历史相干处理的原生转换障碍

**定义 19.1（同探针、正固定槽数、仅历史处理的转换族）。** 令 $m=2j$ 为任意正整数，$D=m+1$，$R=\operatorname{Sym}^m(\mathbb C^2)$，$S=\mathbb C^2$。使用 OTF004 式 (13.5)–(13.6) 的同一对互补总自旋投影和同一原生等距，记

$$
\begin{aligned}
\Pi_+&=\frac{J\cdot\sigma_S+(j+1)I}{D},&
\Pi_-&=\frac{jI-J\cdot\sigma_S}{D},\\
Q_D&=\Pi_+-\Pi_-=\frac{I+2J\cdot\sigma_S}{D},&
V&=\Pi_+\otimes|++\rangle_{HE}+\Pi_-\otimes|--\rangle_{HE}.
\end{aligned}
\tag{19.1}
$$

每次调用的 $H,E$ 都新鲜且全部保留。$A$ 表示输入中除标记 $R,S$ 外的全部辅助寄存器；若有逻辑控制位 $c$，则 $c$ 属于 $A$。$Z$ 表示最终除 $R,S$ 外的全部实际寄存器，包括控制位输出。迹距离仍取 $D_{\rm tr}(\rho,\sigma)=\|\rho-\sigma\|_1/2$。

该转换族的一个字满足下列全部条件。

1. 选择有限整数 $q\ge1$；$q$ 可以依赖公开精度 $e$ 和公开程序。每支都恰执行 $q$ 次 forward $V$，始终作用于同一个标记对 $R,S$。
2. 在这些调用之前、之间和之后，允许任意有限、已知、仅作用于辅助及历史寄存器的等距。它们可以相干旋转原生标签、相干复制读数、计算奇偶、处理逻辑控制，并保留计数器、停止标志、程序及全部工作空间。
3. 局部字中除这 $q$ 次 $V$ 外没有操作作用于 $S$；特别不旋转、交换或路由探针，不将停止分支送到替代探针，也没有历史控制的 $S$ 操作。没有原生调用的跳过、controlled-$V$、$V^\dagger$、直接 $R$ 操作、后选择或非等距丢弃。
4. 初始辅助态可为任意有限独立混合态 $\eta_A$，包括奇异态；不供应其纯化。后续所需的新鲜辅助输入可在开始时全部并入 $A$。对控制门的 $c=0$ 输入，取 $\eta_A=|0\rangle\langle0|_c\otimes\eta_{A\setminus c}$，其余独立混合辅助仍任意。
5. 全部实际原生 $H,E$、相干读出环境、原始记录、控制、计数器、停止标志、程序和工作空间均进入 $Z$；没有未保留的实际环境。

这些条件定义所研究的局部转换族，不是对原控制器全部可能机制的必要条件。尤其 $q$ 是正固定的实际调用数，不是期望数，也不是在不同分支调用或不调用的免费控制。

涉及原精度曲线时，完整沿用 OTF004 定义 19.1 和本卷定义 1.1：$e$ 遍历每个正有理数 $0<e\le1/100$，$m=m_e=D_e-1$，$D=D_e$、$L=L_e$、$Q=Q_e$ 和 $t=m_e e^2$ 均取 (1.1) 的精确 ceil/max 元组，不在内部精度处重算。原场仍遍历全部允许的 $C^2$ 秩二 $n$，参考只准备一次且是唯一含未知 $h$ 的输入；任意有限独立混合辅助及其奇异情形均保留。

**定理 19.2（实际完整等距的正规形与精确 pinching；repo-derived）。** 对定义 19.1 的每个字，存在等距 $A_+,A_-:A\to Z$，使

$$
\begin{gathered}
A_b^\dagger A_b=I_A\quad(b=+,-),\qquad A_+^\dagger A_-=0,\\
W_q=\Pi_+\otimes A_++\Pi_-\otimes A_-.
\end{gathered}
\tag{19.2}
$$

令 $C$ 是证明中使用的二维记录空间，正交基为 $|+\rangle_C,|-\rangle_C$，并置

$$
\begin{aligned}
V_0&=\Pi_+\otimes|+\rangle_C+\Pi_-\otimes|-\rangle_C,\\
T(a\otimes|b\rangle_C)&=A_ba.
\end{aligned}
\tag{19.3}
$$

则 $T:A\otimes C\to Z$ 是等距，并在通常的张量重排下有

$$
W_q=(I_{RS}\otimes T)(V_0\otimes I_A).
\tag{19.4}
$$

对任意 $R\otimes S\otimes A$ 上的联合输入算子 $X$，包括相关或混合输入，有

$$
\begin{aligned}
\operatorname{Tr}_Z(W_qXW_q^\dagger)
&=\Delta_\Pi(\operatorname{Tr}_A X),\\
\Delta_\Pi(Y)&=\Pi_+Y\Pi_++\Pi_-Y\Pi_-.
\end{aligned}
\tag{19.5}
$$

因此增加任意有限 $q$ 或改变允许的相干历史处理，都不改变约化 $RS$ 通道：它恰为一次原生调用后的同一 pinching。

证明。零次调用前的辅助预处理是一个等距 $B:A\to A_0$，可写作 $\sum_b\Pi_b\otimes B$。归纳假设某前缀为 $\sum_b\Pi_b\otimes B_b$，其中每个 $B_b$ 都是等距。中间操作恒等作用于 $RS$，只把 $B_b$ 后接另一个辅助等距。下一次 forward $V$ 将 $RS$ 因子左乘 $\Pi_d$，并添加新鲜 $|dd\rangle$。由于 $\Pi_d\Pi_b=0$（$d\ne b$），仅留下

$$
\sum_{b=\pm}\Pi_b\otimes(B_b\otimes|bb\rangle).
\tag{19.6}
$$

每个辅助分支仍是等距。最后一次调用之后，两分支辅助映射的像由于该次新鲜 $|++\rangle,|--\rangle$ 正交而正交；其后的任何共同辅助等距都保持此正交性。这给出 (19.2)。在 (19.3) 的两个记录基向量上计算内积，立即得到 $T^\dagger T=I_{A\otimes C}$ 及 (19.4)。$C$ 只是实际 $|++\rangle,|--\rangle$ 二维张成空间的数学标识，不额外供应操作。

将 $W_qXW_q^\dagger$ 展开成四个 $b,d$ 块。对每个 $RS$ 矩阵元，其辅助算子 $Y$ 满足

$$
\operatorname{Tr}(A_bYA_d^\dagger)
=\operatorname{Tr}(A_d^\dagger A_bY)
=\begin{cases}\operatorname{Tr}Y,&b=d,\\0,&b\ne d.\end{cases}
\tag{19.7}
$$

故偏迹只留下两个投影对角块，得到 (19.5)。这也证明相关辅助输入的情形。偏迹在这里是计算实际完整等距的约化作用，不是允许控制器物理丢弃输出。$\square$

**定理 19.3（原相干输入上的固定门缺陷；repo-derived）。** 取合法原参考方向 $h=e_z$，令

$$
\begin{gathered}
e_0=|j,j\rangle,\qquad
|x+\rangle=(|\uparrow\rangle+|\downarrow\rangle)/\sqrt2,\\
\psi_0=e_0\otimes|x+\rangle,\qquad
\rho_0=|\psi_0\rangle\langle\psi_0|.
\end{gathered}
\tag{19.8}
$$

对定义 19.1 的每个字和任意允许的 $\eta_A$，约化输出是 $\Delta_\Pi(\rho_0)$，且

$$
\begin{aligned}
D_{\rm tr}(\Delta_\Pi(\rho_0),\rho_0)
&=D_{\rm tr}(\Delta_\Pi(\rho_0),Q_D\rho_0Q_D)\\
&=\alpha_D:=\frac12\sqrt{1-D^{-2}}.
\end{aligned}
\tag{19.9}
$$

因而该族不能以小于 $\alpha_D$ 的误差供应 $Q_D$；作为受控 $Q_D$ 的替换时，仅取 $c=0$，其预期 $RS$ 动作为恒等，误差已经至少为 $\alpha_D$。此下界使用原本的相干参考及已知独立探针，不依赖任意纠缠参考输入或对全部输入另加 diamond 精度要求。

证明。输入 (19.8) 满足 $\langle J\cdot\sigma_S\rangle=0$，故

$$
\langle\psi_0,Q_D\psi_0\rangle=D^{-1},\qquad
p_\pm:=\|\Pi_\pm\psi_0\|^2=(1\pm D^{-1})/2.
\tag{19.10}
$$

令 $v_b=\Pi_b\psi_0$，两向量正交。差算子

$$
\rho_0-\Delta_\Pi(\rho_0)
=|v_+\rangle\langle v_-|+|v_-\rangle\langle v_+|
\tag{19.11}
$$

仅有两个非零本征值 $\pm\sqrt{p_+p_-}$，半迹范数等于 $\alpha_D$。以 $Q_D$ 共轭 $\rho_0$ 只反转这两个非对角项的符号，至同一 pinching 的距离相同。定理 19.2 使该约化输出与 $q$ 和 $\eta_A$ 无关。对受控门取 $c=0$，理想门固定 $\psi_0$；将全部辅助输出连同 $c$ 数学偏迹，迹距离收缩性给同一下界。这没有断言完整控制器必须在每个可能输入上复现这扇局部门。$\square$

**定理 19.4（完整逻辑门因子化障碍及抽象锐值；repo-derived）。** 仍取 (19.8)，并记同一字的实际完整输出为

$$
\Omega_q=W_q(\rho_0\otimes\eta_A)W_q^\dagger,
\qquad
\epsilon_D=\sqrt{D^{-1}-\frac1{4D^2}}\le D^{-1/2}.
\tag{19.12}
$$

对每个允许的 $\eta_A$ 和每个 $Z$ 上密度算子 $\sigma_Z$，即使 $\sigma_Z$ 专为此输入选择，也有

$$
D_{\rm tr}(\Omega_q,\rho_0\otimes\sigma_Z)
\ge\frac1{\sqrt2}-\epsilon_D.
\tag{19.13}
$$

这是 $RS$ 与 $Z$ 之间的完整逻辑门因子化界，不是原问题中 $R$ 与 $S,Z$ 之间的自身边缘返回量。

另外，任取单位向量 $u_+\in\operatorname{Ran}\Pi_+$、$u_-\in\operatorname{Ran}\Pi_-$，置 $\psi=(u_++u_-)/\sqrt2$。对每个字及任意混合 $\eta_A$，有精确代数锐值

$$
\inf_{\sigma_Z\in\mathsf D(Z)}
D_{\rm tr}\left(
W_q(|\psi\rangle\langle\psi|\otimes\eta_A)W_q^\dagger,
|\psi\rangle\langle\psi|\otimes\sigma_Z\right)
=\frac1{\sqrt2}.
\tag{19.14}
$$

这个抽象锐性见证不被宣称为额外允许的原准备。

证明。先给出仅用于迹距离比较的数学历史解码。用 (19.3) 的等距 $T$，令 $P_T=TT^\dagger$；任取 $A\otimes C$ 上密度算子 $\zeta$，定义有限 CPTP 映射

$$
\mathcal D_T(Y)=T^\dagger YT+
\operatorname{Tr}[(I-P_T)Y]\zeta.
\tag{19.15}
$$

第一项完全正，第二项是正效果后的固定态准备，且两项的迹之和为 $\operatorname{Tr}Y$。该映射在 $T$ 的像上是左逆。在实际输出上应用 $\mathcal D_T$ 后再取 $\operatorname{Tr}_A$，(19.4) 给出 $V_0\rho_0V_0^\dagger$；同一数学映射把 $\rho_0\otimes\sigma_Z$ 变成 $\rho_0\otimes\sigma_C$，其中 $\sigma_C$ 是某个密度算子。这些操作仅为收缩性证明中的诊断映射，不属于已供应的原生控制器。混合 $\eta_A$ 仅在此数学偏迹下消失，没有物理丢弃，也没有使用可访问纯化。

所需 Bell–乘积距离是已知受控复制现象的有限维直接计算，在此作为中间步骤给出。令 $|\Phi\rangle=(|00\rangle+|11\rangle)/\sqrt2$。对任意 qubit 密度算子 $\sigma$，

$$
D_{\rm tr}(|\Phi\rangle\langle\Phi|,
|0\rangle\langle0|\otimes\sigma)\ge1/\sqrt2.
\tag{19.16}
$$

对两态同时施行 $\operatorname{diag}(1,e^{i\theta})\otimes\operatorname{diag}(1,e^{-i\theta})$ 的平均。Bell 态及第一因子 $|0\rangle\langle0|$ 不变，第二因子被化为 $\sigma=\operatorname{diag}(p,1-p)$，$0\le p\le1$；收缩性使证明下界只需处理此情形。差算子在 $|00\rangle,|11\rangle$ 上的块和其余本征值为

$$
\begin{pmatrix}\tfrac12-p&\tfrac12\\[1mm]\tfrac12&\tfrac12\end{pmatrix},
\qquad -(1-p),\quad0.
\tag{19.17}
$$

唯一正本征值为

$$
f(p)=\frac{1-p+\sqrt{1+p^2}}2,\qquad
f'(p)=\frac{-1+p/\sqrt{1+p^2}}2<0.
\tag{19.18}
$$

差算子的迹为零，故半迹范数恰为 $f(p)$；最小值是 $f(1)=1/\sqrt2$，且 $\sigma=|0\rangle\langle0|$ 取等号。对系统作固定基变换，同时对记录作共轭基变换，Bell 态保持相同形式；因此系统中的 $|0\rangle$ 可换成任一指定纯向量，包括 $|x+\rangle$。这些是证明中的坐标变换，不是原生操作。

有限自旋比较直接复用 OTF004 (13.14) 的四个精确系数，不重证自旋公式。写

$$
u=e_0\otimes|\uparrow\rangle,\qquad
v=e_0\otimes|\downarrow\rangle,\qquad
w=|j,j-1\rangle\otimes|\uparrow\rangle.
\tag{19.19}
$$

由该组系数，压缩记录记号下

$$
V_0\psi_0=\frac1{\sqrt2}\left(
 u\otimes|+\rangle_C+
 \frac{v+\sqrt m\,w}{D}\otimes|+\rangle_C+
 \frac{m v-\sqrt m\,w}{D}\otimes|-\rangle_C\right).
\tag{19.20}
$$

令

$$
B_0=\frac{u\otimes|+\rangle_C+v\otimes|-\rangle_C}{\sqrt2}
=e_0\otimes\operatorname{Bell}_{SC}.
\tag{19.21}
$$

两向量均归一，且

$$
\langle B_0,V_0\psi_0\rangle=1-\frac1{2D},\qquad
D_{\rm tr}(|V_0\psi_0\rangle\langle V_0\psi_0|,
|B_0\rangle\langle B_0|)
=\sqrt{1-\left(1-\frac1{2D}\right)^2}=\epsilon_D.
\tag{19.22}
$$

先对 (19.13) 两态施行 (19.15) 及 $\operatorname{Tr}_A$，再用三角不等式，得到

$$
\begin{aligned}
D_{\rm tr}(\Omega_q,\rho_0\otimes\sigma_Z)
&\ge D_{\rm tr}(V_0\rho_0V_0^\dagger,\rho_0\otimes\sigma_C)\\
&\ge D_{\rm tr}(|B_0\rangle\langle B_0|,
\rho_0\otimes\sigma_C)-\epsilon_D\\
&\ge1/\sqrt2-\epsilon_D.
\end{aligned}
\tag{19.23}
$$

最后一步偏迹 $R$，应用 (19.16) 对 $\operatorname{Bell}_{SC}$ 与 $|x+\rangle\langle x+|\otimes\sigma_C$ 的结论。

对 (19.14)，以 $u_+,u_-$ 为系统二维子空间的正交基，(19.3) 的解码实际向量恰为

$$
\frac{u_+\otimes|+\rangle_C+u_-\otimes|-\rangle_C}{\sqrt2},
\tag{19.24}
$$

并张量同一 $\eta_A$。由 (19.16)、解码及偏迹 $A$，对每个 $\sigma_Z$ 得下界 $1/\sqrt2$。反向取

$$
\begin{aligned}
|+_C\rangle&=(|+\rangle_C+|-\rangle_C)/\sqrt2,\\
\sigma_Z&=T(\eta_A\otimes|+_C\rangle\langle+_C|)T^\dagger.
\end{aligned}
\tag{19.25}
$$

在解码空间中，比较变成 (19.24) 的 Bell 纯态与纯乘积 $\psi\otimes|+_C\rangle$，二者均张量同一 $\eta_A$。纯态重叠模为 $1/\sqrt2$，其迹距离也是 $1/\sqrt2$。张量密度算子不改迹范数，等距不改迹距离，故 (19.25) 达到下界。这对每个混合 $\eta_A$ 成立，不需要满秩、正的最小本征值或任何纯化。$\square$

**命题 19.5（同一原输入的精确参考泄漏；repo-derived）。** 对 (19.12) 的同一实际输出，参考泄漏恰为

$$
p_R:=1-\operatorname{Tr}[(|e_0\rangle\langle e_0|\otimes I_{SZ})\Omega_q]
=\frac{m}{D^2}.
\tag{19.26}
$$

因此常数量级的 $RS$ 门缺陷 (19.9)、(19.13) 不能读成常数量级的 $R$ 返回缺陷，也不是原自身实际边缘返回或任意原控制器的新增下界。

证明。在 (19.20) 中，唯一参考因子正交于 $e_0$ 的分量为

$$
\frac{\sqrt m}{\sqrt2D}\,
 w\otimes(|+\rangle_C-|-\rangle_C).
\tag{19.27}
$$

它的范数平方是 $m/D^2$。历史辅助等距不改变 $R$ 边缘，故由 (19.4) 得 (19.26)。所有式子对每个正整数 $m$ 成立；将其代入精确原 $m_e$ 不要求二进精度，也不改变资源元组。$\square$

**命题 19.6（停止反射消费者的局部转换与实际计数边界）。** 本卷 §§5–6 的 Fourier–beta 逻辑字使用 $Q_D$、受控 $Q_D$ 以及逆逻辑字中的相应字母；§7 在其声明 CP 实际端口下，由经典停止字供应这些字母。考虑仅将该停止机制改为定义 19.1 的机制：把每个槽都执行在同一个未经其他操作的探针上，相干处理仅限全部历史和控制。则任意有限正固定 $q$，包括 $q=q_e$ 或更大的固定填充数如 $2q_e$，均不能使这个替换在 (19.8) 的原输入上恢复 §7 的字母动作或其 $e/(D_eL_e)$ 比较精度。

一个这样的字每支恰支付 $q$ 次 forward $V$、零次场重置、零次规定终端。若用于 $\nu_e$ 个字母，实际原生调用成本是各字所选 $q$ 的和；统一选择 $q_e$ 时，加上既有后缀的两次调用，计数仍为 $\nu_eq_e+2$，但这个计数本身不供应正确门动作。

证明。由定理 19.2，任何这样的字的约化 $RS$ 通道都恰为 $\Delta_\Pi$；定理 19.3 的误差 $\alpha_D$ 与 $q$ 无关且不随 $D\to\infty$ 趋零。在原精度域及精确原元组上，(19.9) 给出的 $\alpha_{D_e}>e/(D_eL_e)$ 排除所述局部比较。计数逐字累加；没有将最坏调用数改成期望数，也没有把停止之后的空白槽当作免费受控原生调用。

此结论针对上述字母替换，不断言完整 Fourier 字中某个实际中间态就是 (19.8)，也没有证明每个原控制器都必须实现此局部门。精确保留旧边缘、逐门任意输入 diamond 精度、独立历史因子、固定时序或保持 $q'=q$ 均不是本命题向原问题新增的必要条件。不同实际机制仍可保留相关历史、旋转或混合探针、路由到替代探针、改变调度、真正跳过调用，或者直接供应最终消费者而不复现这些字母；其中任何机制只要满足原合同，就不由本节排除。带有 $S$ 操作、跳过调用或非等距丢弃的字不满足定义 19.1，不能从本证明取得同一正规形。

OTF004 命题 24.3 假设已制造并永久保留经典总自旋 $b$，给出该类的不能校正界；这里不要求任何经典 $b$。全部标签及读出环境都可以保持相干并由任意历史等距混合；正固定同探针调度中最后一份不可避免的新鲜原生标签给出 (19.2)。这一区别不否定 OTF004 定理 24.2 及本卷 §7 在原声明 CP 端口中的经典停止结果，也不将形式延迟测量中的调用／不调用控制视为免费菜单项。$\square$

**定义 19.7（原完整消费者、来源与未闭合的组合条件）。** 本节的局部字没有场输入，不改变任何允许 $n$ 或其来源，也不准备额外未知方向。决定性见证是原一次准备的 $\tau_{e_z}$、固定已知独立 $|x+\rangle$ 和任意独立有限混合辅助。因此它是原输入对应上的局部门障碍，而不是已完成的解码器、补偿或终端构造。

原完整消费者仍要求：在同一精确原元组上，对全部允许 $C^2$ 秩二场 $n$ 和全部 $h$，同一四坐标解码器达到 (1.3) 的 $e$ 精度及失败率 $\beta\le e$；最坏分支至多 $L_e$ 次 forward $V$ 和至多 $Q_e$ 次独立场重置；参考只准备一次，是唯一含未知 $h$ 的输入；任意独立有限混合辅助允许奇异且不供应纯化。完成仍须恰执行一次规定 $U_{\rm term}$，使用在 $+d e_x$ 独立重置且此前未经改动的原场令牌，并保留同一实际运行的全部输出，与该实现自己的实际最终边缘比较。不新增免费逆、控制、来源或参考操作，不将成功要求缩成局部、两场或二值任务。

在完全等距实现分支上，未闭合的充分构造义务包括：供应排除族之外的实际 forward-only 完整历史访问机制；若继续消费 §§5–6 的既有逻辑字，则证明其活使用所需的输入相关或组合访问关系、实际总误差和确定最坏调用数；处理未测量工作替换、$L$ 读出及其他 CP 节点的实际完整等距对应；处理规定补偿的 $\widehat\Phi$、$B,A,F$ 及后续 $S_t$ 上的每个 $\mathcal E$ 节点和全部实际环境，并支付原资源和规定终端。在同一完整实现上取得 $p_R\le C/(m_e e^2)$ 仍是上界路线的未证条件；从纯参考投影估计到自身边缘 $O(1/\sqrt t)$ 的标准推论或抽象等距扩张，不替代此条件。

§§3–6 的固定有限球冠 $W$、Fourier–beta 估计和既有正 CP 构造各在自己的前提下保留；该正构造的显式二进窗口不替代原正有理全域。§§12–15 的部分保留界和 $\eta t$ 有界判据保持原 CP 端口前提，$\eta=1$ 不自动完成其他 CP 节点。§16 的重置必要阶及其匹配阶保持；§17 的无条件 rotation 反例保持其较宽比较类，不被转换为原成功控制器反例。§18 是同一实际成功完整等距实现、共同二值置信读出下的返回下界，不是任意约化 CP 消费者的结论，也不供应实际来源、时钟或匹配上构造。在 §18 的精确前提下，成功完整等距自身边缘 $O(1/t)$ 路线已被其下界排除，本节不重新提出该目标。

完整物理来源逐层保留 [PB 实际探针与环境耦合续卷 §6](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md) 和 [PB 两角正证书续卷定义 49.1、边界 49.2](AURIC_FULL_PB_TWO_CORNER_POSITIVE_CERTIFICATE_CONTINUATION.md) 的同一 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ 全文及全部递归钉版上游，七项同时要求不变：

1. 同一原来源中的实际复相干准备、原标签、共同全词与合法控制，而非仅有数学向量。
2. 原态、效果、Born 关系、完整菜单及全部零、不等、次归一和非正常质量。
3. 同一实际来源上的真正相关联合、复合与张量；相同边缘不替代联合关系。
4. typed CP、每条分支的未归一上下文、全部输出与合法未来，以及整台递归参考。
5. 完整仪器、TP、成功／失败及细记录输出、条件更新和 Lüders 前件。
6. 全部合法历史、真遗忘、完整实际活动输出、读后 ready、第一合法消费者及真实全未来 Return／CountRead。
7. 实际动力学、物理时钟、能量、一般生成元域及跨装置共同正作用量。

这七项说明不缩短所引全文，也不压平其递归来源。存在性、比较核返回、相同边缘、形式 Stinespring 环境和声明 CP 端口均不自动供应同一实际物理来源、完整输出、全未来真实 Return 或时钟。本节不构造这些条件，不从局部转换障碍或搜索未命中推出来源不存在。

本节的承重新增应用为定义 19.1 的全部有限字上的精确正规形、原相干输入常数 $\alpha_D$、完整门因子化常数 $1/\sqrt2-\epsilon_D$、抽象锐值及同时成立的 $p_R=m/D^2$，标为 `repo-derived`。投影 pinching、受控复制、Bell–乘积距离、迹距离收缩与等距不变性是经典中间工具；已有 [CanonicalRecordAccessRecovery](../../../Blueprint/D5/S3/Quantum/Decoherence/CanonicalRecordAccessRecovery.md) 和 [ReducedRecordAccessDefect](../../../Blueprint/D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect.md) 已区分完整复制记录与约化相干损失，不能把该一般现象重新当作新增成果。自旋系数直接复用 OTF004 (13.14)，不重证 Fourier 估计、beta 桥、极分解或 QSVT。这里给出的是普通有限维纸面推导，不主张新的 Lean 声明、kernel 核验、形式准入、物理实现或历史原创性。

相关停止形态的文献为 Paetznick–Svore，[Repeat-Until-Success: Non-deterministic decomposition of single-qubit unitaries, arXiv:1311.1074v2](https://arxiv.org/html/1311.1074v2)，§3、§3.2；其测量成功／失败、可逆失败与期望成本不供应本节原菜单下完整等距转换或最坏预算。Guerreschi，[Repeat-Until-Success circuits with fixed-point oblivious amplitude amplification, arXiv:1808.02900v1](https://arxiv.org/html/1808.02900v1)，§III、§IV，讨论受控 RUS 的历史相关畸变并在放大中使用 $A S_\phi A^\dagger S_\varphi$；该伴随不是免费 $V^\dagger$，其畸变也不被认作本节障碍。这些相关文献不作为原生实现的精确命中，不承担 (19.2)–(19.27) 的证明，也不支持穷尽文献或历史新颖性断言。

## 追加锚（本行以下为增补区）

## 20. 原有理精度全域上的完整输出原生消费者

**定义 20.1（原合同、输入与精确有限参数）。** 本节采用 [OTF004 定义 19.1](OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md) 和本卷定义 1.1 的完整原合同。对每个正有理数 $0<e\le1/100$，所有对数均为自然对数，置

$$
\begin{aligned}
u&=u_e=e/8,\qquad H_e=\log(18/e),\\
k&=k_e=\left\lceil2048e^{-2}H_e\right\rceil,\qquad
\ell=\ell_e=\left\lceil32768e^{-4}\log(90/e)\right\rceil,\\
N_*&=8{,}388{,}608{,}000,\\
N&=N_e=\max\left\{N_*,
 \left\lceil\frac{3k+2}{10}\right\rceil,
 \left\lceil\frac{15\ell+1}{18}\right\rceil\right\},\\
D&=D_e=\left\lceil\max\{8{,}000{,}000N^2,9k/e\}\right\rceil,\\
m&=m_e=D-1=2j,\qquad M=M_e=L=L_e=10N,\qquad Q=Q_e=18N+1,\\
q&=3k.
\end{aligned}
\tag{20.1}
$$

这些是原精度 $e$ 的原整数，不在另一精度重算。公共参数仍为 $d=1/64$、$\tau_0=1$、$r=1/4$、$B_{\rm field}=2$、$G=1$；内部采样步长 $u$ 不替代 $d$。

场遍历全部原允许的 $C^2$、秩二映射 $n:U\to S^2$，其中开集 $U$ 包含两条完整闭 $r$ 轴段，并满足

$$
\|n_{aa}(t e_a)\|_2\le2\quad(a=x,y,\ |t|\le r),
\qquad \|n_x(0)\|_2,\|n_y(0)\|_2\le1.
\tag{20.2}
$$

场信息只由原独立重置服务 $\rho_n(z)=(I+n(z)\cdot\sigma)/2$ 供应。方向遍历全部 $h\in S^2$，目标仍为

$$
D_h(n)=\left(
 \frac{h\cdot[n(0)\times n_x(0)]}{2},
 \frac{h\cdot[n(0)\times n_y(0)]}{4},0,
 \frac{h\cdot n_y(0)}2\right).
\tag{20.3}
$$

原标记参考 $R=\operatorname{Sym}^m(\mathbb C^2)$ 只准备一次，初态 $\tau_h=|j,h\rangle\langle j,h|$ 与全部其他输入独立，是唯一含未知 $h$ 的输入。设备、控制、解码器及除声明场服务外的准备均不依赖实际 $n,h$；固定 $n$ 后，完整非参考输入律对全部 $h$ 相同。原比较类仍允许任意独立有限混合辅助，包括奇异态，以及记忆、反馈、纠缠和探针回用；不供应混合输入的纯化。以下固定调度只指定该类中的一个见证，不约束其他控制器。

只有前向原生等距 $V$ 和一次规定终端接触 $R$：

$$
\begin{aligned}
V&=\Pi_+\otimes|++\rangle_{HE}+\Pi_-\otimes|--\rangle_{HE},\\
\Pi_+&=\frac{J\cdot\sigma+(j+1)I}{D},\qquad
\Pi_-=\frac{jI-J\cdot\sigma}{D},\\
U_{\rm term}&=\exp[-idJ\cdot\sigma/m].
\end{aligned}
\tag{20.4}
$$

其他全部操作在原 $R$ 上为恒等。终端必须使用在 $+d e_x$ 独立重置且此前未经改动的原场令牌；不提供参考旋转、替换、重置、直接读取、未知射线反射、免费逆或受控原生访问。

**定义 20.2（完整有限电路、记录与有理解码器）。** 取 $q=3k$ 个互异探针 $S_i$，各自独立处于 $I/2$。每槽另准备一个独立备用 qubit $G_i$ 于 $I/2$ 和一个空白 $F_i$ 于 $|0\rangle$。各三元组与 $R$、全部先前寄存器及其他三元组独立。三个固定实验室 Pauli 轴 $a=x,y,z$ 各分配 $k$ 槽。主动非场混合输入恰为这 $2q$ 个 $I/2$ qubit，不访问任何输入纯化。

在槽 $i$，对 $R,S_i$ 执行一次前向 $V$，产生原生 $H_i,E_i$。用已知计算基复制酉把原 $H_i$ 标签复制到 $F_i$，其中 $+$ 编码为 $0$、$-$ 编码为 $1$；再以 $H_i=-$ 为控制交换 $S_i,G_i$。这是保留所有输出的非参考酉操作，不是经未保留浴实现的替换通道。永久保留 $S_i,G_i,H_i,E_i,F_i$。

随后在该槽指定的固定轴 $a$ 上，执行显式 Pauli 记录等距

$$
\mathsf M_a=
 \sum_{y\in\{+1,-1\}}P_{a,y}\otimes|y\rangle_{Y_i}\otimes|y\rangle_{Z_i},
\qquad P_{a,y}=\frac{I+y\sigma_a}{2}.
\tag{20.5}
$$

$Y_i,Z_i$ 都是实际输出 qubit，原 $S_i$ 也保留。该等距由已知基变换、向两个空白 qubit 的复制门及逆基变换组成；全部操作均在非参考口。将 $Y_i=+1$ 的次数写入对应计数器。旧 $S_i,G_i,H_i,E_i,F_i,Y_i,Z_i$ 均不再进入任何后续 $R$ 接触；每个下一原生输入确实是新的独立 $I/2$。

场采样取五个点

$$
\mathcal Z_e=\{0,+u e_x,-u e_x,+u e_y,-u e_y\}.
\tag{20.6}
$$

对每个 $z\in\mathcal Z_e$ 和每个固定轴 $b=x,y,z$，请求 $\ell$ 个互异独立原场令牌。对每个令牌执行同一 $\mathsf M_b$，保留令牌及两个记录输出，并记录 $+1$ 次数。这恰使用 $15\ell$ 次重置，不接触 $R$。因为 $u=e/8\le1/800<r$，全部采样点都在原完整场域内。

将原始记录的值记为 $Y_i\in\{+1,-1\}$ 和 $X_{z,b,s}\in\{+1,-1\}$。这些字母表示实际记录基中的数值，不表示另增观测。定义

$$
\begin{aligned}
\widehat h_b&=\frac2k\sum_{i\text{ 分配给 }b}Y_i,\\
\widehat n_b(z)&=\frac1\ell\sum_{s=1}^{\ell}X_{z,b,s},\qquad
\widehat n_0=\widehat n(0),\\
\widehat g_a&=\frac{\widehat n(+u e_a)-\widehat n(-u e_a)}{2u}
\quad(a=x,y),\\
\widehat D&=\left(
 \frac{\widehat h\cdot[\widehat n_0\times\widehat g_x]}2,
 \frac{\widehat h\cdot[\widehat n_0\times\widehat g_y]}4,
 0,\frac{\widehat h\cdot\widehat g_y}2\right).
\end{aligned}
\tag{20.7}
$$

不对 $\widehat h$ 或 $\widehat n$ 归一化。若参考计数为 $c_{h,b}$、场计数为 $c_{n,z,b}$，前两行分别是 $2(2c_{h,b}-k)/k$ 和 $(2c_{n,z,b}-\ell)/\ell$，故正有理 $e$ 上全部输出四元组都是有理的。将四元组写入实际输出 $O$ 及实际读出副本 $O'$，保留所有原始串、计数和两份输出。

计数、写入和复制由保持数据的有限可逆操作完成。有三个维数 $k+1$ 的计数器和十五个维数 $\ell+1$ 的计数器，联合维数为

$$
d_C=(k+1)^3(\ell+1)^{15}.
\tag{20.8}
$$

有理输出四元组的有限集合基数至多 $d_C$，取 $O,O'$ 为该集合的标签寄存器。由所保留计数器控制的固定写入即完全指定输出操作，无须丢弃工作空间。计数可按上述各有限维数作模加法，实际计数不溢出所需范围。另保留静态程序 $P$、维数 $q+15\ell+2$ 的宏步计数器 $T$，以及任意额外独立有限混合旁观态 $\eta_A$；$A$ 始终由恒等作用保留，包括奇异 $\eta_A$。

记录及解码输出均已生成之后，再请求一个在 $+d e_x$ 独立重置的原场令牌 $S_t$。在其唯一接触前，除规定源准备外不对它作任何操作。恰执行一次 (20.4) 的 $U_{\rm term}$ 并保留 $S_t$。$d=1/64<r$ 保证该点在原域内。不再执行其他后缀、补偿节点、参考操作、逆、受控原生调用、分支后选择或系统丢弃。$T$ 只是有限程序寄存器，不供应物理钟。

该指定电路的完整非参考口 $K$ 恰包含：每个 $S_i,G_i,H_i,E_i,F_i,Y_i,Z_i$；全部 $15\ell$ 个采样场令牌及每个令牌的两个 Pauli 记录输出；终端令牌 $S_t$；十八个计数寄存器；$O,O',P,T,A$。没有其他生成环境或工作空间。原生 $H,E$ 及复制的原标签 $F$ 永不覆盖。qubit 口总数恰为

$$
7q+45\ell+1,
\tag{20.9}
$$

此外是上述有限计数／输出／程序／步寄存器和 $A$。参考 $R$ 的维数为 $D$，不属于 $K$。若另一实现另产生实际输出，必须纳入其自己的 $K$ 并核对实现前件；本节不认证未指定的物理设备。原场服务是原声明来源输入，不是额外未知场口或辅助纯化。

**定理 20.3（同一完整运行的条件成功与显式自身边缘返回；repo-derived 应用）。** 假设原合同的实际量子准备、前向原生、固定标架非参考控制／读出、独立场重置和规定终端菜单按定义 20.1–20.2 的实际端口供应。对每个原正有理 $0<e\le1/100$，定义 20.2 给出一个与实际 $n,h$ 无关的有限因果控制器 $W_e$ 和有限有理四坐标解码器。对全部原允许场 $n$ 和全部 $h\in S^2$，同一完成运行满足

$$
\begin{gathered}
\Pr[\|\widehat D-D_h(n)\|_\infty\le e]\ge1-e,\\
T_V=q=3k\le L,\qquad
T_{\rm reset}=15\ell+1\le Q,\qquad
T_{\rm terminal}=1,\qquad T_R=q+1.
\end{gathered}
\tag{20.10}
$$

置

$$
\begin{aligned}
\lambda_m^2&=\frac m{D^2},\\
g_m&=\frac{4m}{D^2}\sin^2\left(\frac{dD}{2m}\right),\\
r_e&=1-(1-g_m)(1-\lambda_m^2)^q,\\
B_e&=\min\{1,2\sqrt{r_e}\}.
\end{aligned}
\tag{20.11}
$$

对同一完整实际输出 $\Omega_{n,h}$，以其全部实际 $K$ 和其自身实际边缘为比较对象，有

$$
\begin{aligned}
\overline\delta
&:=\sup_{n,h}\frac12\left\|
 \Omega_{n,h}-\tau_h\otimes\operatorname{Tr}_R\Omega_{n,h}
 \right\|_1\\
&\le B_e
 \le\min\left\{1,
 \frac{160\sqrt{\log(18/e)}}{e\sqrt m}\right\}.
\end{aligned}
\tag{20.12}
$$

$B_e$ 是显式有限上界证书，不是迹距离的精确值。任意独立有限混合旁观态 $\eta_A$，包括奇异态，均可原样保留；不使用输入纯化。实际最终参考泄漏的精确表达式为下文 (20.29)，其一致上确界恰为 (20.30)。

证明。以下分别把同一电路的记录事件和实际参考边缘接回原工具；两者始终属于同一完成运行。

### 20.1 保留实现的约化对应及其事件用途

令 $X$ 为 $S,H$ 与任意旁观系统上的联合输入，记 $X_{bb}=\langle b|_H X|b\rangle_H$，旁观系统可包括 $R,E$ 及旧记忆。先复制 $H$ 到空白 $F$，再以负标签控制交换 $S,G$。对该实际酉输出作数学偏迹，得到

$$
\begin{aligned}
&\operatorname{Tr}_{GF}\left[
 U_{\rm cswap}U_{\rm copy}
 (X\otimes I_G/2\otimes|0\rangle\langle0|_F)
 U_{\rm copy}^{\dagger}U_{\rm cswap}^{\dagger}\right]\\
&\quad=X_{++}\otimes|+\rangle\langle+|_H
 +\frac{I_S}{2}\otimes\operatorname{Tr}_S(X_{--})
                  \otimes|-\rangle\langle-|_H
 =\mathcal C(X),
\end{aligned}
\tag{20.13}
$$

其中张量次序按旁观因子重排。对 $F$ 的偏迹消去不同 $H$ 标签间的非对角块；负块中的交换将原先可能与旁观系统相关的 $S$ 内容留在 $G$，把独立 $I/2$ 放在 $S$；正块不变。这正是 OTF004 (13.7)–(13.8)，并对相关输入及全部旁观系统成立。

这里的偏迹仅用于分析记录概率；$G,F$ 在实际电路中均永久保留，并进入 (20.12)。它们不再参与后续接触或解码，所以对任意仅依赖解码记录的事件，电路的约化旧端口律恰为原 $q$ 槽 $\mathcal C$ 前缀，再接所声明的 Pauli 读出、场采样和解码。

直接复用 OTF004 (13.16)–(13.19)，理想单槽和完整旧端口前缀比较为

$$
\begin{aligned}
\xi_h&=\frac12P_{h,+}\otimes|++\rangle\langle++|
       +\frac14I_S\otimes|--\rangle\langle--|,\\
D_{\rm tr}\left(
 \text{旧实际 }q\text{ 槽输出},\tau_h\otimes\xi_h^{\otimes q}
 \right)&\le q\kappa_D,
\qquad \kappa_D=\frac{2D-1}{2D^2}.
\end{aligned}
\tag{20.14}
$$

共同非参考读出、独立场采样和解码通道保持此距离界，从而保持相同事件概率差的界。无需假设实际槽历史独立，也没有把旧约化 CP 返回界转移到新增 $G,F$ 或读出口。

### 20.2 原四坐标事件、有限解码与确定预算

在 $\xi_h$ 中，轴 $b$ 的 Pauli 记录 $Y$ 满足 $\mathbb E(2Y)=h_b$，且 $2Y\in[-2,2]$。理想乘积槽中的三个 $k$ 样本均值直接应用 OTF004 定义 19.1 所用有界样本估计，给出

$$
\Pr_{\rm ideal}\left[\exists b:\
 |\widehat h_b-h_b|>e/16\right]
 \le6\exp(-ke^2/2048)\le e/3.
\tag{20.15}
$$

每个场 Pauli 记录在 $[-1,1]$ 内，均值为 $n_b(z)$。十五个均值同样满足

$$
\Pr\left[\exists z,b:\
 |\widehat n_b(z)-n_b(z)|>eu/16\right]
 \le30\exp(-\ell e^2u^2/512)\le e/3.
\tag{20.16}
$$

第一指数由 $k\ge2048e^{-2}\log(18/e)$ 至少为 $\log(18/e)$；第二指数因 $u=e/8$ 及原 $\ell$ 至少为 $\log(90/e)$。所以两尾分别不超过 $6(e/18)=e/3$ 和 $30(e/90)=e/3$，对整个原有理域成立。

在两好事件上，利用 $\sqrt3<2$，有

$$
\|\widehat h-h\|_2\le e/8,\qquad
\|\widehat n(z)-n(z)\|_2\le eu/8.
\tag{20.17}
$$

精确中心差分是 $n_a(t e_a)$ 在 $[-u,u]$ 上的平均。由 (20.2)，$\|n_a(t e_a)-n_a(0)\|_2\le2|t|$，故其偏差至多 $u$。两端采样在差分中另贡献至多 $(2eu/8)/(2u)=e/8$，于是

$$
\|\widehat g_a-n_a(0)\|_2\le u+e/8=e/4
\quad(a=x,y).
\tag{20.18}
$$

并且 $\|\widehat h\|_2,\|\widehat n_0\|_2\le2$。把未缩放叉积误差写成

$$
\begin{aligned}
&\widehat h\cdot[\widehat n_0\times\widehat g_a]
      -h\cdot[n(0)\times n_a(0)]\\
&=(\widehat h-h)\cdot[n(0)\times n_a(0)]\\
&\quad+\widehat h\cdot[
 (\widehat n_0-n(0))\times n_a(0)
 +\widehat n_0\times(\widehat g_a-n_a(0))].
\end{aligned}
\tag{20.19}
$$

因 $\|n(0)\|_2=1$、$\|n_a(0)\|_2\le1$、$u<1$，其绝对值至多

$$
e/8+2(e/8+2e/4)=11e/8.
\tag{20.20}
$$

因此第一、第二坐标误差分别至多 $11e/16$、$11e/32$。第四坐标误差至多

$$
\frac12\left(e/8+2e/4\right)=5e/16,
\tag{20.21}
$$

第三坐标精确为零。两好事件遂蕴涵原 $\ell^\infty$ 四坐标 $e$ 成功事件，不需估计归一化、导数下界或改变目标。

由 (20.14) 及原 $D\ge9k/e$，实际记录事件概率与理想实验之差至多

$$
q\kappa_D\le\frac{3k}{D}\le e/3.
\tag{20.22}
$$

总失败概率至多 $e/3+e/3+e/3=e$。这只转移记录事件。最后 $U_{\rm term}$ 仅在 $R,S_t$ 上作用，是保迹操作；即使先前记录与 $R$ 相关，它也不改变已经写好的完整记录边缘，故同一完成运行保持此成功概率。

每支确定支付 $T_V=q$、$T_{\rm reset}=15\ell+1$、$T_{\rm terminal}=1$ 和 $T_R=q+1$。原最大值与上取整精确给出

$$
q+2\le10N=L,\qquad15\ell+1\le18N<Q=18N+1.
\tag{20.23}
$$

未使用调用不执行也不计费。具体非参考操作为 $q$ 次原标签复制、$q$ 次受控交换、$q+15\ell$ 次 (20.5)，随后是有限可逆计数与输出写入。记录等距的投影分支正交且投影和为恒等；保留原始串的受控模计数和计数控制的输出置换均无需未列出的丢弃空间。十八个计数器及至多 $d_C$ 个输出标签保证解码有限，$q+15\ell+2$ 个步状态足以标记 $q+15\ell+1$ 个接触／采样宏步骤。这里没有期望成本、随机停止或极限电路，也没有把程序寄存器当作实际物理钟。

### 20.3 新鲜混合输入链与实际参考边缘

除 $V$ 外，所有获取、Pauli 记录、场观测、计数和解码操作只作用在非参考系统。即使 $R$ 与每个旧保留口相关，下一个 $S_i$ 仍是未受作用的独立 $I/2$。因此实际参考边缘逐槽恰按 OTF004 (20.11) 的通道更新：

$$
\mathcal T(X)=\frac{
 2\sum_{a=x,y,z}J_aXJ_a+((j+1)^2+j^2)X}{D^2}.
\tag{20.24}
$$

$q$ 槽后的实际参考边缘精确为 $\mathcal T^q(\tau_h)$。保留 $G,F$、全部读出环境、场令牌和解码器均不改变该边缘；这里没有把相关旧记忆假设成独立。

只在证明坐标中沿 $h$ 取 $e_r=|j,j-r\rangle_h$，$0\le r\le m$。直接复用 OTF004 (20.12) 的已给对角自旋递推，不另立一般递推定理：令 $\pi_r^{(0)}=\mathbf1_{r=0}$，并令 $\pi^{(q)}$ 为以下有限转移矩阵的 $q$ 步分布，边界缺项为零，

$$
\begin{aligned}
\mathsf P(r,r+1)&=\frac{(m-r)(r+1)}{D^2},\\
\mathsf P(r,r-1)&=\frac{r(m-r+1)}{D^2},\\
\mathsf P(r,r)&=1-\mathsf P(r,r+1)-\mathsf P(r,r-1),\\
\mathcal T^q(\tau_h)&=\sum_{r=0}^m\pi_r^{(q)}|e_r\rangle\langle e_r|.
\end{aligned}
\tag{20.25}
$$

这是一份精确有限矩阵幂定义，不是数值递推结果。始终停留在 $r=0$ 的路径给出

$$
\pi_0^{(q)}\ge\left(1-\frac m{D^2}\right)^q.
\tag{20.26}
$$

这些 Markov 路径只是约化对角态的数学展开，不是额外实际自旋测量、独立物理历史或依赖未知 $h$ 的实验操作。

### 20.4 未触终端令牌与精确最终人口

记 $v=n(+d e_x)$、$c=h\cdot v$。终端令牌独立于整个先前运行，故最终参考边缘可仅由 $\mathcal T^q(\tau_h)\otimes\rho_v$ 计算；旧 $R$–记忆相关不影响这一约化计算。由 OTF004 (13.14)、(16.8) 的原总自旋系数，忽略共同标量相位，

$$
U_{\rm term}=\Pi_++z\Pi_-,\qquad z=\exp(idD/m).
\tag{20.27}
$$

在该等式中忽略的只是全局相位。$e_0\otimes|\downarrow\rangle_h$ 与 $e_1\otimes|\uparrow\rangle_h$ 间的跃迁振幅模平方恰为

$$
\left|\frac{\sqrt m(1-z)}D\right|^2
 =\frac{4m}{D^2}\sin^2\left(\frac{dD}{2m}\right)=g_m.
\tag{20.28}
$$

只有初始参考层 $0,1$ 能贡献最终第 $0$ 层人口。参考输入对角，终端自旋的非对角项不另贡献此人口；自旋人口分别为 $(1+c)/2$ 和 $(1-c)/2$。从初始第 $0$ 层流出的量为 $g_m(1-c)\pi_0^{(q)}/2$，由第 $1$ 层流入的量为 $g_m(1+c)\pi_1^{(q)}/2$。所以对同一完整实际 $\Omega_{n,h}$，最终泄漏精确为

$$
\begin{aligned}
p_{\rm final}(n,h)
&:=1-\operatorname{Tr}[(\tau_h\otimes I_K)\Omega_{n,h}]\\
&=1-\pi_0^{(q)}
 +\frac{g_m}{2}\left[
 (1-c)\pi_0^{(q)}-(1+c)\pi_1^{(q)}\right].
\end{aligned}
\tag{20.29}
$$

$c$ 的系数为 $-g_m(\pi_0^{(q)}+\pi_1^{(q)})/2\le0$，所以最大值在 $c=-1$。分布 $\pi^{(q)}$ 与方向无关；对每个原允许场 $n$，$h=-n(+d e_x)$ 都是允许方向。因此精确一致泄漏为

$$
\sup_{n,h}p_{\rm final}(n,h)
 =1-(1-g_m)\pi_0^{(q)}.
\tag{20.30}
$$

再用 (20.26)，得到

$$
\sup_{n,h}p_{\rm final}(n,h)
 \le1-(1-g_m)\left(1-\frac m{D^2}\right)^q=r_e.
\tag{20.31}
$$

这是完整输出的实际参考边缘结论；没有把约化 CP 返回界提升到新增保留口。

### 20.5 对全部实际输出的自身边缘投影应用

对该完整实际态直接应用有限纯参考投影估计。为明确此处的应用，记 $P_h=\tau_h\otimes I_K$、$Q_h=I-P_h$，把 $\Omega=\Omega_{n,h}$ 分块为

$$
P_h\Omega P_h=\tau_h\otimes A_0,\qquad
Q_h\Omega Q_h=B_0,\qquad
P_h\Omega Q_h=C_0,\qquad p=\operatorname{Tr}B_0.
\tag{20.32}
$$

有 $\operatorname{Tr}_R C_0=0$ 和 $\operatorname{Tr}_R\Omega=A_0+\operatorname{Tr}_R B_0$。由正性和标准 Schatten Cauchy–Schwarz 估计，

$$
\|C_0\|_1\le\sqrt{p(1-p)}.
\tag{20.33}
$$

差态的两个对角项 $B_0$ 与 $-\tau_h\otimes\operatorname{Tr}_R B_0$ 具有正交参考支持，各自迹范数为 $p$。两个交叉块的半迹范数贡献至多 $\|C_0\|_1$。故在这一完整 $K$ 上，

$$
\begin{aligned}
\frac12\|\Omega-\tau_h\otimes\operatorname{Tr}_R\Omega\|_1
&\le p+\sqrt{p(1-p)}\\
&\le2\sqrt p.
\end{aligned}
\tag{20.34}
$$

这是标准投影到自身边缘工具在具体电路上的应用，不主张新增一般定理。它不使用可访问纯化、辅助密度逆或正的最小本征值，故包括所有奇异混合旁观输入。比较对象恰是同一 $\Omega$ 的自身实际 $K$ 边缘，不是旧端口边缘或另选乘积态。迹距离的一般上界为 $1$，联同 (20.31) 即得 $\overline\delta\le B_e$。

### 20.6 全有理域的绝对常数

由 $\sin^2x\le x^2$ 及 $D=m+1$，

$$
0\le g_m\le\frac{d^2}{m},\qquad
\frac m{D^2}\le\frac1m.
\tag{20.35}
$$

$g_m$ 是 (20.28) 的跃迁概率，故 $g_m\le1$。Bernoulli 不等式给出

$$
\begin{aligned}
r_e
&\le q\frac m{D^2}+g_m
 \le\frac{q+d^2}{m}.
\end{aligned}
\tag{20.36}
$$

令 $A_e=e^{-2}\log(18/e)$。在整个原域内 $A_e\ge10{,}000$，而 $d^2=1/4096$。精确上取整给出

$$
\begin{aligned}
k&\le2048A_e+1,\\
q+d^2=3k+d^2
 &\le6144A_e+3+1/4096\\
 &\le6145A_e<6400A_e.
\end{aligned}
\tag{20.37}
$$

因此

$$
B_e\le\min\left\{1,2\sqrt{\frac{q+d^2}{m}}\right\}
 \le\min\left\{1,
 \frac{160\sqrt{\log(18/e)}}{e\sqrt m}\right\}.
\tag{20.38}
$$

这包括 $e=1/100$、每个上取整端点及全部更小的原正有理精度，不用渐近窗口、二进限制、逐门 diamond 近似、实际历史独立或近纯辅助假设。定理得证。$\square$

**边界 20.4（原全文来源、既有结果域与未付目标）。** 定理 20.3 是以原实际量子菜单供应为前件的有限消费者应用；这些菜单的物理供应仍标为 `ASSUMED-UNVERIFIED`。完整物理来源保持 [OTF004 定义 19.1](OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md)、本卷定义 1.1、[PB 实际探针与环境耦合续卷 §6](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md) 及 [PB 两角正证书续卷定义 49.1、边界 49.2](AURIC_FULL_PB_TWO_CORNER_POSITIVE_CERTIFICATE_CONTINUATION.md) 的完整合同与全部逐层固定上游，不以七项摘要或另造来源谓词替代其全文。

来源身份按 `deb96eeabf0e2411c95c872ca8232c766ce7dd60` 的上述四份正文解释：OTF004 的 blob 为 `316045b4f10114cb1cb207c0f50dc6285b2b8f51`，本卷 §§1–19 为 `55dbc6ce3410ba3cc1aa4bf8f43c31e81ea603f9`，PB 实际探针续卷为 `d9e05528552f6b39c04cea6e97542acab6265114`，PB 两角续卷为 `3d833411c88065cf06a00372069f17738d01db86`。这些身份引用完整保留内部递归钉版，不用外层读取提交压平内层 SQ、AH、SF、PB 身份。原 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ 中 $S,D$ 仍是原 Jordan 来源响应，其中 $S(a,b)=a\circ b$；它们不被自旋维数 $D=D_e$ 替换。

同一原 $\Omega$ 最终仍须共同供应全部七项完整合同：实际复 Hilbert／相干准备；原态、效果、Born、完整菜单及全部质量分支；真正相关联合、复合与张量；typed CP 及整台递归参考；完整仪器、TP、条件更新与 Lüders；全部合法历史、CountRead、真遗忘及真实全未来 Return；实际动力学、物理钟、能量和共同正 $\hbar$。每项均连同所引原对象、量词、准备、切口、记录、拒绝、停止、销毁、泄漏、全部输出和每个合法未来保留在同一原实现上，不分别换源。该说明与全文共同保留，不缩短全文。条件量子输出 $\Omega_{n,h}$ 的有限电路不生产这个原物理来源 $\Omega$，也不生产实际相干准备、菜单／Born 绑定、全部质量、共同相关复合、整台参考规则、完整仪器、全未来 Return、物理钟或共同作用量；不从搜索未命中推出来源不存在。

本节不合成 $Q_D$、受控 $Q_D$ 或 Fourier 字母，直接使用互异新鲜探针，故不抵触 §19 的固定同探针、仅历史处理局部障碍。该局部门障碍不是原所有消费者的必要门条件。既有 CP、部分保留、重置、rotation 及 §§18–19 结果各保留自身精确适用域：§§1–11 的声明 CP 实际口不被默认为本节完整等距口；§§12–15 的部分保留条件不自动处理其他实际环境；§16 的重置必要阶及匹配阶保持；§17 无条件 rotation 反例仍不成为原成功控制器反例；§18 的完整成功等距及共同二值置信前件保持。

尤其，§18 的已有成功完整等距下界 $1/(512e\sqrt m)$ 与 (20.12) 相容。本节仅给出一个带 $\sqrt{\log(18/e)}$ 差距的完整消费者证书；一致无对数的 $O(1/(e\sqrt{m_e}))$ 匹配上界，以及 $e$ 无关常数 $C$ 的同一运行一致 $p_R\le C/(m_e e^2)$ 构造仍未证。本节不重提 §18 前件下已排除的完整等距 $O(1/(m_e e^2))$ 自身边缘目标，不主张最优性、新增全局下界或物理来源不存在。精确式 (20.29)–(20.30) 是人口／泄漏等式；(20.31)、$B_e$ 及 (20.12) 都是上界，不能改读成精确迹距离。

[C139 父代敏感读树续卷 §§10–15](AURIC_C139_PARENT_SENSITIVE_READ_TREE_AND_GAIN_RECOVERY_BOUNDARY.md) 的保留 occurrence、可读系数与条件平坦地址服务，在其明确扩充的 $P$ 来源内给出条件 CountRead 与同载体 Return；[C139 有限返回校准续卷 §164](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md) 仍区分该来源与原 $B_r$、原钟及全未来接口，尚无这份识别。[E4 阈值卷 §17](FIB_ENTROPY_HARMONIC_RENEWAL_STATE_THRESHOLD.md) 从完整确定坐标矩形与精确有效行得到条件实际运行结论，不是量子原语来源，也不消除其完整 E4 桥梁。二者均不是定理 20.3 的前提；不以扩充 $P$、E4、R5、MPS 或其他 DEV 成果替换原来源或供应本节量子菜单。

**来源 20.5（直接复用与证据范围）。** 本节承重结果是定义 20.2 的具体完整输出消费者、其同一运行成功对应、精确终端人口以及有限 $B_e$ 和绝对常数 $160$ 的普通纸面推导，标为 `repo-derived` 应用。原获取证书、固定标架样本与成功常数直接复用 OTF004 定义 13.1–13.2、(13.5)–(13.19) 和定义 19.1；终端系数直接复用 (13.14)、(16.8)；新鲜 $I/2$ 参考边缘及对角递推直接复用 (20.11)–(20.12)。约化对应只承担记录成功律，完整返回另由实际参考边缘和全部实际口上的投影应用承担。Pauli 记录、有限可逆计数／写入、偏迹局域性、有界样本估计和 Schatten 投影估计均为应用中间工具，不另交付一般 Stinespring、gentle、复制、编译或递推定理。

新鲜完全混合自旋输入的已知递推可参见 Bartlett、Rudolph、Spekkens、Turner，[Degradation of a quantum reference frame, arXiv:quant-ph/0602069v2](https://arxiv.org/html/quant-ph/0602069v2)，§III 与附录 B (39)–(42)。其精确系数在 $m=2j$、下降指标 $r$ 下对应 (20.25)；不使用其后大自旋近似，也不把该数学递推当作原物理来源实现。本节不主张历史原创性或穷尽文献／库搜索，不主张 Lean／kernel 核验、数值或实验验证、工程 CI 认证、物理实现或原七项共同来源目标已经完成。

## 追加锚（本行以下为增补区）

## 21. 正自旋缓存路由与原完整输出的无对数返回

**定义 21.1（原合同与精确精度曲线）。** 沿用 [OTF004 定义 19.1](OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md) 和定义 1.1。对每个正有理数 $0<e\le1/100$，未标底的对数为自然对数，置

$$
\begin{aligned}
u&=u_e=e/8,\quad k=k_e=\left\lceil2048e^{-2}\log(18/e)\right\rceil,\quad
\ell=\ell_e=\left\lceil32768e^{-4}\log(90/e)\right\rceil,\\
N_*&=8{,}388{,}608{,}000,\qquad
N=N_e=\max\left\{N_*,\left\lceil\frac{3k+2}{10}\right\rceil,
 \left\lceil\frac{15\ell+1}{18}\right\rceil\right\},\\
D&=D_e=\left\lceil\max\{8{,}000{,}000N^2,9k/e\}\right\rceil,\qquad
m=m_e=D-1=2j,\\
M&=M_e=L=L_e=10N,\qquad Q=Q_e=18N+1.
\end{aligned}
\tag{21.1}
$$

公共参数仍为 $d=1/64$、$\tau_0=1$、$r=1/4$、$B_{\rm field}=2$、$G=1$；$u$ 不替代 $d$。场遍历所有原允许的 $C^2$ 秩二映射 $n:U\to S^2$，其中开集 $U$ 包含两条完整闭 $r$ 轴段，且 $\|n_{aa}(v e_a)\|_2\le2$（$a=x,y$、$|v|\le r$）、$\|n_x(0)\|_2,\|n_y(0)\|_2\le1$。场信息只经原独立重置 $\rho_n(z)=(I+n(z)\cdot\sigma)/2$ 供应。对所有 $h\in S^2$，四坐标目标为

$$
D_h(n)=\left(
 \frac{h\cdot[n(0)\times n_x(0)]}{2},
 \frac{h\cdot[n(0)\times n_y(0)]}{4},0,
 \frac{h\cdot n_y(0)}2\right).
\tag{21.2}
$$

原标记参考 $R=\operatorname{Sym}^m(\mathbb C^2)$ 只准备一次，初态 $\tau_h=|j,h\rangle\langle j,h|$ 与其余输入独立，是唯一含未知 $h$ 的输入。设备、程序、解码器及除声明场服务外的准备均不依赖实际 $n,h$；固定 $n$ 后非参考来源的完整律对所有 $h$ 相同。原合同允许任意独立有限混合辅助 $\eta_A$，包括奇异态及 $A$ 内部相关，不供应其纯化；本构造将任意这样的 $\eta_A$ 由恒等作用保留。参考接触只有至多 $L$ 次前向原生等距及恰一次规定终端：

$$
\begin{aligned}
\Pi_+&=(J\cdot\sigma+(j+1)I)/D,\qquad \Pi_-=(jI-J\cdot\sigma)/D,\qquad
Q_D=\Pi_+-\Pi_-,\\
V&=\Pi_+\otimes|++\rangle_{HE}+\Pi_-\otimes|--\rangle_{HE},\\
U_{\rm term}&=\exp(-idJ\cdot\sigma/m).
\end{aligned}
\tag{21.3}
$$

场重置至多 $Q$ 次。终端令牌在 $+d e_x$ 独立重置，此前未经改动；其他操作在原 $R$ 上为恒等。直接参考操作、原生逆、受控原生调用和终端逆均不作为供应。每个实际生成的非参考系统都进入同一运行的 $K$，不作分支后选择。下文用半迹范数 $D_{\rm tr}(\rho,\sigma)=\|\rho-\sigma\|_1/2$。

**定义 21.2（逻辑等距、常数与公开精度分支）。** 令 $a=e/64$、$s=e/768$、$t=me^2$、$\lambda=ms^2=t/768^2$。使用 §§3–6 的同一个同时有限化球冠 $f$、堆叠 $A_{\rm stack}$ 及极等距

$$
W=A_{\rm stack}(A_{\rm stack}^\dagger A_{\rm stack})^{-1/2}.
\tag{21.4}
$$

记定理 6.2 的完整逻辑酉 $U_{\rm outer}$ 为 $U_{\rm out}$，用其原有限表、相位选择、编译标志和全部非投影块，止于 (3.11) 工作替换及 $L$ 经典读出之前。展开所有正、逆及受控查询，记其中 $Q_D$ 或受控 $Q_D$ 的实际逻辑字母数为 $\nu$；其余门均为已知非参考门。$K_{\rm work}$ 始终保留，不施行 (3.11)、约化获取或约化补偿后缀。

常数精确取 (2.1)–(2.7)。为区分记号，将 (2.6) 的 $C$ 记为 $C_{\rm src}$，将 (2.2) 的 $B=A$ 在本节记为 $B_{\rm cap}$。具体地，单位圆盘内用 $q(w)=\exp(-1/(1-|w|^2))$、$\alpha(w)=\bar w/(1-|w|^2)$ 和 $F_k(w)=\sqrt{q(w)}\exp(-|\alpha(w)|^2/2)\alpha(w)^k/\sqrt{k!}$，盘外按 (2.1) 平坦延拓。置 $z_0=\int q(w)\,dA(w)/\pi$、$M_F=\sup_w(\|F\|+\|DF\|+\|D^2F\|)$，则

$$
\begin{aligned}
A=B_{\rm cap}&=10000(1+M_F)/\sqrt{z_0},\qquad R_0=4(A+B_{\rm cap}+2),\qquad
C_{\rm fail}=1+256A^2,\\
C_{\rm src}&=1+\left\lceil10^{100}(26!)^{10}
 \left[1+A+B_{\rm cap}+z_0^{-1}+\sum_{j=0}^{26}(M_j+G_j)\right]^{100}\right\rceil,\\
M_{\rm Fourier}&=2^{50}C_{\rm src}^4,\quad
A_0=2^{20}768^2M_{\rm Fourier},\quad C_\nu=2^{26}A_0,\quad U_0=3\cdot10^{16},\\
r_0&=\max\left\{r_{\rm base},7,
 \left\lceil\log_2(1000U_0M_{\rm Fourier}768^{24})\right\rceil,
 \left\lceil\log_2(10000A_0)\right\rceil,
 \left\lceil\log_2(10000C_\nu^2)\right\rceil\right\}.
\end{aligned}
\tag{21.5}
$$

$r_{\rm base}$ 及球冠窗口精确取 (2.2)–(2.3)，$M_j,G_j$ 精确取定义 2.2。$M_j$ 是 $\|D^jF\|$ 与 $\|N_{\rm osc}D^jF\|$ 之和的上确界，$(N_{\rm osc}v)_k=kv_k$；$G_j$ 是同一紧域上 Euler 作用、旋转立体图、径向图及截断的导数界。截断仍为 (2.4) 的 $\chi(\rho)=\theta(8\rho-4)\theta(12-8\rho)$，其中 $\theta(v)=H_+(v)/(H_+(v)+H_+(1-v))$，$H_+(v)=\exp(-1/v)$ 当 $v>0$，否则为零。第 2 节的平坦延拓和紧域界给这些常数的有限性。定义

$$
\begin{aligned}
K_N&=1280(C_\nu+1),&
e_0&=\min\{2^{-r_0},1/(10^6K_N^2)\},\\
K_{\rm cap}&=768(A+R_0+C_{\rm fail})+1,&
C&=\left\lceil\max\{(K_{\rm cap}+K_N^2+132)^2,\,
                              6400\log(18/e_0)\}\right\rceil.
\end{aligned}
\tag{21.6}
$$

$e_0$ 是正有理数，$C$ 是有限正整数，均不依赖实际输入或辅助维数。$e\le e_0$ 使用定义 21.3，$e>e_0$ 使用定义 20.2 的同一完整电路及解码器，包括其独立未触令牌终端。两支均取请求精度 $e$ 的 (21.1)，不在内部尺度、二进精度或另一精度重算原元组。

**定义 21.3（保留的缓存、路由、解码与全部实际口）。** 在 $e\le e_0$ 支取

$$
q=\lceil\log_2(DL/e)\rceil,\qquad B=\nu q .
\tag{21.7}
$$

先准备 $q$ 对相互独立的已知自旋单态 $(B_i,A_i)$（singlet）；对 $i=1,\ldots,q$，在 $R,B_i$ 上各作一次前向 $V$，相干保留原生 $H_i,E_i$。从 $H$ 标签串写入首个正标签的索引，若不存在则写零，并保留原标签、索引及失败位。非零索引控制交换对应的 $B_i$ 与指定位置 $B_1$，称该位置的 qubit 为缓存 $C_{\rm cache}$；零索引时不交换。所有探针、伙伴和原生标签保留，不测量、退相干或后选择该准备。已知单态是控制器自身的准备，不是额外未知方向输入或 $\eta_A$ 的纯化。

依原次序运行展开后的 $U_{\rm out}$。每个逻辑字母 $U\in\{Q_D,\mathrm{controlled}\ Q_D\}$ 对原逻辑探针 $S$ 使用固定 $q$ 槽。槽活动位和奇偶由本字已有记录可逆写入。每槽都恰作一次前向 $V$：活动槽直接用 $S$；非活动槽先受控交换 $S$ 与缓存，调用后交换回来。第一活动槽在调用后施行 (7.1) 的 $F_{cH}$（不受控字取 $c=1$）；后续活动校正槽省去该相位。每个活动槽使用相干记录等距

$$
\mathsf M_X=\sum_{x,y=0}^1|x_X y_X\rangle\langle x_X y_X|_{HE}
                       \otimes|xy\rangle_{B_{\rm X}}\otimes|xy\rangle_{F_{\rm X}},
\qquad |x_X\rangle=(|+\rangle+(-1)^x|-\rangle)/\sqrt2.
\tag{21.8}
$$

原 $H,E$、原始 $xy$ 与实际副本均保留。第一槽奇偶零即成功；若为一，第一处校正奇偶一使该字成功。若到第 $q$ 槽仍活动，写入截止标志并以实际态继续。原始 $xy$ 永不覆盖；本字历史只用于本地停止和记录，后续逻辑门不读取这些历史。

非活动槽不作 $F_{cH}$ 或 $X$ 读出。把该槽原生 $H,E$ 中的原生对通过以非活动为控制的交换移入新鲜两位标志 $Z_i$，原 $H,E$ 寄存器和 $Z_i$ 都保留。$Z_i=00$ 表示正标签，$Z_i=11$ 表示负标签，活动槽留 $Z_i$ 为空白 $00$；另保留活动位。负标签不被舍去，且任何后续门均不读取或覆盖 $Z_i$。这只是相干数据的可逆搬移：非活动槽原 $H,E$ 留下交换来的空白，原生对仍在实际口内。所有槽的非活动空白、失败、截止和不匹配分支均保留。

逻辑字结束后，以有限记录等距 $|l\rangle_L\mapsto|l\rangle_L|l\rangle_{\rm read}|l\rangle_{\rm copy}$ 读 $L$。按定义 10.1 写入 $\widehat h(l)$：正标签中心按坐标以误差至多 $a$ 取有理值，零及无效码取零；保留旧两坐标解码输出、无效码和失败码。场采样在 $0,\pm u e_x,\pm u e_y$ 五点，对三个固定实验室 Pauli 轴各取 $\ell$ 个独立原场令牌。逐个使用 (20.5) 的保留记录等距，保留令牌、两份记录及十五组计数和均值 $\widehat n_b(z)$。置

$$
\begin{aligned}
\widehat g_a&=\frac{\widehat n(+u e_a)-\widehat n(-u e_a)}{2u}\quad (a=x,y),\\
\widehat D&=\left(
 \frac{\widehat h\cdot[\widehat n(0)\times\widehat g_x]}2,\,
 \frac{\widehat h\cdot[\widehat n(0)\times\widehat g_y]}4,\,
 0,\frac{\widehat h\cdot\widehat g_y}2\right).
\end{aligned}
\tag{21.9}
$$

由保留数据控制的有限可逆查表写入 $\widehat D$ 及一份实际副本。所有算术输入和输出均保留，值为有理数且标签集合有限。随后请求一个在 $+d e_x$ 独立重置的原令牌，不作任何中间操作，恰施行一次 $U_{\rm term}$ 并保留令牌。不另施行补偿、恢复、参考替换、逆或后选择。

该分支的 $K$ 包含全部 $2q$ 个准备探针和伙伴、$2q$ 个准备原生 $H_i,E_i$、索引、失败和路由输出；全部逻辑探针、频率、系数标签、$L$、$K_{\rm work}$、LCU 与 QSVT 的选择器、相位、标志及编译口；每个付费槽的原 $H,E$、$X$ 原记录及副本、$Z_i$、活动、奇偶、成功、截止、有限计数及每项历史计算输出；$L$ 的读出及副本、$\widehat h$、旧解码口；全部 $15\ell$ 个场样本令牌及其两份记录、十五组计数和均值、两个差分向量、$\widehat D$ 及副本和全部算术输出；终端令牌、固定公开程序与表、宏步、路由及计数寄存器和 $\eta_A$。布尔函数以保留输入并将函数值加到新有限输出的方式实现。非参考操作是指定有限矩阵、受控置换或显式记录等距，无未列出的丢弃口。另一实现若产生额外实际系统，须将其纳入自己的 $K$ 并另给完整输出对应。$e>e_0$ 支的完整 $K$ 取定义 20.2 的全部实际口。

**定理 21.4（同一完成运行的原成功、无对数泄漏和自身边缘返回）。** 假设原合同实际供应上述量子准备、前向原生、所用已知非参考控制与保留读出（包括相干探针路由）、独立场重置和规定终端。对每个原正有理 $0<e\le1/100$，定义 21.2–21.3 给出一个与实际 $n,h$ 无关的有限因果控制器及有限有理四坐标解码器。对所有定义 21.1 的 $n,h$ 和任意独立有限混合 $\eta_A$，其同一完整实际完成态 $\Omega_{n,h}$ 满足

$$
\begin{gathered}
\Pr[\|\widehat D-D_h(n)\|_\infty>e]\le e,\qquad
T_V\le L_e,\qquad T_{\rm reset}\le Q_e,\qquad T_{\rm terminal}=1,\\
p_R(n,h):=1-\operatorname{Tr}[(\tau_h\otimes I_K)\Omega_{n,h}]
 \le \frac{C}{m_e e^2},\\
\frac12\|\Omega_{n,h}-\tau_h\otimes\operatorname{Tr}_R\Omega_{n,h}\|_1
 \le \min\left\{1,\frac{2\sqrt C}{e\sqrt{m_e}}\right\}.
\end{gathered}
\tag{21.10}
$$

$C$ 精确取 (21.6)，比较边缘是该 $\Omega_{n,h}$ 自己的实际 $K$ 边缘。小精度支的逐支确定计数为 $q+\nu q$ 次前向原生、$15\ell+1$ 次原重置、一次终端和 $q+\nu q+1$ 次参考接触；另一支的确定计数由 (20.10) 给出。相同结论包括每个取整端点、$e=e_0$ 及 $e=1/100$。

证明。先证明 $e\le e_0$ 支，取 $H=\log(1/e)$。辅助 $\eta_A$ 始终按恒等张量保留；获取证明可先在其余系统的纯向量上作，之后张量 $\eta_A$。这不调用其纯化。场采样及终端在各自实际混合令牌上处理。

### 21.1 原有理精度上的逻辑供应

OTF004 §26 的球冠窗口已量化于每个正有理 $e\le e_*$。本卷 §§3–6 的有限公式使用 $e$ 本身、整数上取整、固定区间选择和二进相位舍入；原 $e=2^{-r}$ 的指数 $r$ 不进入这些构造。所需大小条件由 $e\le2^{-r_0}$ 和原整数直接取得。具体地，在整个原域上，

$$
\begin{gathered}
27000e^{-4}H\le N\le60000e^{-4}H,\qquad D=8{,}000{,}000N^2,\\
10^{15}e^{-8}H^2\le m\le3\cdot10^{16}e^{-8}H^2,\qquad t\le U_0 e^{-8},\\
q\le64H,\qquad \log(2t/e)\le40+9H\le20H .
\end{gathered}
\tag{21.11}
$$

下界用 $N\ge5\ell/6$；上界用 $\log(90/e)\le2H$ 及 (21.1) 的上取整逐项界住最大值。$N\ge3k/10$、$k\ge1/e$ 给 $9k/e\le8{,}000{,}000N^2$，右边已是整数。平方后减一给 $m$ 的两界，$H^2\le e^{-2}$ 给 $t$ 的上界。$\log D\le19H$、$\log L\le8H$ 代入 (21.7) 给 $q$ 界；$U_0$ 与 $H\ge\log 100$ 给最后一界。上述推导使用原取整定义，包括其等号端点。

球冠的 (2.8) 由 OTF004 (26.3) 的同一 $m$ 和 $e\le2^{-r_{\rm base}}$ 给出。截断、正求积及导数估计 (3.4)、(3.7)、(3.10) 使用该 $\lambda,s$ 窗口；Fourier 尾至多 $M_{\rm Fourier}768^{24}e^{39/4}$，乘 $t$ 后由 $U_0e^{-8}$ 和 (2.7) 中相应门槛控制。表和 Taylor 误差用同一 $s,t$ 与 (2.7) 的 $A_0$ 门槛；于是 (5.14) 的矩形误差、极分解间隙和 §6 的 erf 多项式估计仍在同一窗口内。(7.7)–(7.9) 的内外次数界使用这些不等式及 $\log(2t/e)$，并逐个展开正、逆和受控字母；不使用二进等式，也不将频率标签数乘入共享访问。故 (6.11) 和 (7.9) 在这些有理 $e$ 上保持原常数。这里延用的是工作替换前的逻辑估计，不扩展定理 1.2 的声明 CP 消费者。

其中所用奇异值变换是 Gilyén–Su–Low–Wiebe，[Quantum singular value transformation and beyond, arXiv:1806.01838v1](https://arxiv.org/src/1806.01838v1) 的原始文稿 Definition 15（交替相位字）、Theorem 17（奇异值变换）、Corollary 18（实多项式）和 Lemma 19（交替相位字的实现）。§§5–6 的输入输出投影及酉在共同有限空间上，内层偶、奇多项式和外层实奇多项式满足各自次数、奇偶性和整个 $[-1,1]$ 上的界，外层用同一正奇异值间隙。受控与伴随逻辑访问照 (7.9) 逐字计费；投影块不当作确定输出。由 (6.9)–(6.11)，包括编译标志及所有非投影振幅的比较为

$$
\|U_{\rm out}\psi-|0_{\rm compiler}\rangle W\psi\|<\frac1{32t},
\qquad
\nu\le C_\nu e^{-3}\log(2t/e),\qquad B\le K_N e^{-3}H^2
\tag{21.12}
$$

（$\psi$ 为逻辑输入嵌入中的单位向量）。最后一界来自 (21.11) 的 $64H$ 和 $20H$。另由 OTF004 (26.4)–(26.5)、引理 26.8 及本卷 (3.10)、(10.3)，同一有限 $W$ 有

$$
\|(I-\tau_h)W|j,h\rangle\|\le A/\sqrt\lambda+(R_0+C_{\rm fail})/\lambda,\qquad
\Pr_W[\|\widehat h-h\|_\infty>e/16]
 \le 3C_{\rm fail}/\lambda+4\exp[-(m+2)e^2/16384].
\tag{21.13}
$$

后一式只读 $L$ 的分布，无须替换 $K_{\rm work}$。

### 21.2 缓存准备的完整向量比较

只在证明中固定 $h$ 的坐标，记 $e_b=|j,j-b\rangle_h$，顶层向量写为 $|j,h\rangle$。写 $|h+\rangle,|h-\rangle$ 为探针沿 $h$ 的本征向量。比较等距为

$$
v_h=P_{h,+}\otimes|++\rangle+P_{h,-}\otimes|--\rangle,\qquad
P_{h,\pm}=|h\pm\rangle\langle h\pm|.
\tag{21.14}
$$

由 OTF004 (13.14)，$V-I_R\otimes v_h$ 在 $|j,h\rangle|h+\rangle$ 上为零，在 $|j,h\rangle|h-\rangle$ 上等于

$$
D^{-1}\bigl(|j,h\rangle|h-\rangle+\sqrt m\,e_1|h+\rangle\bigr)
       \otimes(|++\rangle-|--\rangle).
\tag{21.15}
$$

故限制在参考 $|j,h\rangle$ 上的算子范数恰为 $\sqrt{2/D}$，张量任意探针旁观仍成立。以理想前缀、实际后缀逐项作望远镜，每个理想前缀保持参考为 $|j,h\rangle$。在包括全部准备输出、索引及交换的同一向量空间中，实际准备和 $q$ 次 $v_h$ 的比较误差至多 $q\sqrt{2/D}\le2q/\sqrt m$。后接实际等距保持该界。

对一半已知单态，$v_h$ 的正、负分支各有平方范数 $1/2$；理想准备的分支相互独立，全负扇区平方范数为 $f_0=2^{-q}$。其正交补内，首个正标签交换把 $|h+\rangle$ 放在缓存位置，因此在固定 $h$ 时缓存与所有其余系统因子化。仅在证明中归一化这成功扇区，记其向量为 $|j,h\rangle|h+\rangle_{C_{\rm cache}}\otimes\kappa_h$，其中 $\kappa_h$ 含其余准备口。实际控制器既不知道 $h$，也不选择或归一化该扇区。全负扇区始终保留，其振幅 $\sqrt{f_0}$ 在下文计入。该计算对所有方向（包括实验室极点）相同。

### 21.3 跳过非活动调用的完整比较及理想前缀激发

令 $\mathcal G$ 为数学比较电路，复制定义 21.3 的相干活动槽、读出及全部历史，只在非活动槽写空白而跳过调用，不接触缓存。这个受控调用／跳过只用于比较。由 OTF004 (24.7)–(24.8)，(21.8) 的首槽、校正槽的精确分支算子依次为 $2^{-1}Q_D^{x\oplus y}U$、$2^{-1}Q_D^{x\oplus y}$，包括受控 $U$ 的相干控制交叉块。长度 $b$ 的成功历史因此有算子 $2^{-b}U$，截止历史有 $2^{-q}Q_DU$。每份历史含 $X$ 基的 $H,E$、原始 $xy$、副本、活动位和停止数据。于是成功历史的相干叠加与逻辑输入因子化，且平方范数 $1-2^{-q}$ 与输入无关。每个逆字母也分别满足此对应。相关的停止形态见 Paetznick–Svore，[Repeat-Until-Success: Non-deterministic decomposition of single-qubit unitaries, arXiv:1311.1074v2](https://arxiv.org/html/1311.1074v2)；这里所用的是上述有限分支系数。

所有 $\nu$ 字都成功的扇区恰作 $U_{\rm out}$，张量归一化、输入无关的完整成功历史向量。保留的截止标志区分其正交补，其平方范数

$$
F=1-(1-2^{-q})^\nu\le\nu2^{-q}.
\tag{21.16}
$$

在归一化的理想成功准备上，$\mathcal G$ 的完整输出相对于对应的 $U_{\rm out}$ 张量全成功历史，半迹距离至多 $\sqrt F$（纯态平方重叠为 $1-F$），并有 $\sqrt{p_R(\mathcal G)}\le\sqrt{p_R(U_{\rm out})}+\sqrt F$，由对两正交历史分量施加同一个参考正交投影得到。

令 $N_h=jI-J_h$，则 $N_h|j,h\rangle=0$。$Q_D$ 只在有限自旋二维块 $\{e_b|h-\rangle,e_{b+1}|h+\rangle\}$（$0\le b<m$）作非对角耦合，其系数为 $2\sqrt{(m-b)(b+1)}/D$。两端不耦合的状态不给交换子贡献。每块乘上 $\sqrt{N_h}$ 的本征值差后，由

$$
\frac{2\sqrt{(m-b)(b+1)}}D(\sqrt{b+1}-\sqrt b)
 \le\frac{2\sqrt m}D\le\frac2{\sqrt m}
\tag{21.17}
$$

得 $\|[\sqrt{N_h},Q_D]\|\le2/\sqrt m$。在 $V$ 的输入输出之间，相应交换子为 $[\sqrt{N_h},Q_D]\otimes(|++\rangle-|--\rangle)/2$，不增加该界。活动控制与其余非参考门、相位、记录和路由记账均与 $\sqrt{N_h}$ 交换；一次相干受活动控制的比较槽至多增加同一界。由 $\|\sqrt{N_h}\mathcal G_i\Psi\|\le\|\sqrt{N_h}\Psi\|+2/\sqrt m$ 逐槽归纳，在上述成功准备及空白逻辑输入上，$\mathcal G$ 的任一经过至多 $b$ 槽的完整前缀 $\Psi_b$ 满足

$$
\|\sqrt{N_h}\Psi_b\|\le2b/\sqrt m,\qquad
\langle N_h\rangle_{\Psi_b}\le4b^2/m.
\tag{21.18}
$$

旧记录和反馈全在同一向量内，不假设历史独立。缓存只在 $\mathcal G$ 中始终保持 $|h+\rangle$ 因子。有限自旋端点与半整数 $j$ 同样适用。

### 21.4 付费路由与同一相互作用图景中的记录投影

在缓存为 $|h+\rangle$ 的比较输入上，任意参考向量 $\psi$（可带任意纠缠旧记忆）满足

$$
\langle h+|\Pi_-^{RC_{\rm cache}}|h+\rangle=N_h/D,\qquad
\|\Pi_-^{RC_{\rm cache}}(\psi\otimes|h+\rangle)\|^2
   =\langle\psi|N_h|\psi\rangle/D.
\tag{21.19}
$$

第一式用 $\langle h+|\sigma|h+\rangle=h$，第二式用 $\Pi_-^2=\Pi_-$。此式只给未投影理想前缀上的精确失配质量，并不假设实际缓存经历其他参考接触后仍为联合本征态。

将全部 $B$ 槽按时间编号。对第 $i$ 槽在活动位已写、调用未执行的切口，令 $A_i$ 为活动投影。此处 $A_i$ 作用在保留活动数据上，与 $RC_{\rm cache}$ 投影交换。定义

$$
P_i=A_i I+(I-A_i)\Pi_+^{RC_{\rm cache}},\qquad
\mathsf J_i=P_i\otimes|00\rangle_{Z_i}+(I-P_i)\otimes|11\rangle_{Z_i}.
\tag{21.20}
$$

$P_i$ 是正交投影。在活动扇区，$\mathsf J_i$ 只给空白标志，实际槽与 $\mathcal G$ 的活动槽相同；在非活动扇区，成对受控交换使实际前向 $V$ 恰作用在 $R,C_{\rm cache}$，原生标签移入 $Z_i$ 后恰有 (21.20) 的两项，其他新槽口和比较电路一样为空白。因而实际槽精确因子化为先 $\mathsf J_i$、再相同切口上的理想槽及共同记账，后者在非活动扇区不再作原生调用，并在两扇区都不作用于 $Z_i$。这里的因子化是两扇区上的线性等距等式，故也适用于活动与非活动的相干叠加；其实现就是已付费的路由槽，不需物理投影测量。

在预置全部空白口的同一有限空间内取理想槽及共同门的酉延拓，均在所有 $Z_i$ 上为恒等。令 $G_{<i}$ 为从初始切口到第 $i$ 槽投影前的理想前缀（包括活动位计算），$G_{\rm end}$ 为整个比较获取字。令 $\Psi$ 为 §21.2 的归一化理想成功准备连同逻辑输入及空白口。共同相互作用图景中的投影及其单次失配质量为

$$
\begin{aligned}
\widetilde P_i&=G_{<i}^\dagger P_iG_{<i},\\
\varepsilon_i&=\|(I-\widetilde P_i)\Psi\|^2
 =\|(I-A_i)\Pi_-^{RC_{\rm cache}}G_{<i}\Psi\|^2
 \le\frac{4B^2}{mD},\\
\sum_{i=1}^B\varepsilon_i&\le S:=\frac{4B^3}{mD}.
\end{aligned}
\tag{21.21}
$$

用 (21.19) 和 (21.18) 估计的是同一初态的**未投影**理想前缀；$I-A_i$ 只会降低该范数。酉延拓和其伴随仅作坐标变换，不提供实际逆。因为没有后续门读取或覆盖旧 $Z_i$，实际完整向量的全零标志振幅恰为

$$
G_{\rm end}\widetilde P_B\cdots\widetilde P_1\Psi.
\tag{21.22}
$$

即第 1 槽投影先作用，最后再推回到理想最终坐标；其余旗标历史全在正交补。空槽情形 $\nu=0$ 取 $B=S=F=0$，投影积为恒等。

将 Jingliang Gao，[Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2](https://arxiv.org/html/1410.5688v2)，Theorem 1(a),(b) 应用于同一初态 $|\Psi\rangle\langle\Psi|$ 和上述依次作用的有限正交投影。设接受质量 $a_{\rm acc}=\|\widetilde P_B\cdots\widetilde P_1\Psi\|^2$。在需要非平凡界的窗口内，(b) 给 $a_{\rm acc}\ge1-4S>0$；(a) 比较的是初态与将该投影积所得向量按 $\sqrt{a_{\rm acc}}$ 归一化后的态。其 $D$ 为**全迹范数**，上界 $2\sqrt{\sum_i\varepsilon_i}$，故本卷半迹距离至多 $\sqrt S$。经 $G_{\rm end}$ 推回，归一化接受向量与理想输出的平方重叠至少 $1-S$。全输出与理想输出（张量全空白 $Z_i$）的平方重叠只由 (21.22) 贡献，至少为 $(1-4S)(1-S)\ge1-5S$，在 $S<1/5$ 时给出非平凡界；其余 $S$ 用距离至多一。于是

$$
D_{\rm tr}(\text{实际完整路由输出},\text{理想完整输出})
 \le\min\{1,\sqrt{5S}\}.
\tag{21.23}
$$

另取归一化接受向量的整体相位使其与理想向量的距离最小，平方重叠界给向量距离至多 $\sqrt{2S}$。施参考正交投影后，其泄漏振幅至多 $\sqrt{p_R(\mathcal G)}+\sqrt{2S}$。非接受的全部保留历史的总平方范数至多 $4S$，且标志与接受历史正交。因此用 $\sqrt{2S}+2\sqrt S\le4\sqrt S$ 得

$$
\sqrt{p_R(\text{理想成功准备上的实际路由})}
 \le\sqrt{p_R(\mathcal G)}+4\sqrt S.
\tag{21.24}
$$

只需对 $S<1/16$ 作此推导；否则右侧至少为一。两个界均作用在无条件完整输出，归一化只在证明中使用。误差由未投影同一历史的平方缺陷之和控制；这依赖成功比较准备及完整理想历史的有限自旋激发界，不是对任意门输入的 diamond 范数供应。一个已取得的缓存供全部路由槽使用，其准备代价不按字母重付。

### 21.5 完整获取及原未触终端

由 (21.13)、$\lambda\ge1$、$t\ge1$ 和 (21.12)，有 $\sqrt{p_R(U_{\rm out})}\le K_{\rm cap}/\sqrt t$。将实际准备换为完整理想准备，泄漏振幅及事件半迹误差均至多增加 $2q/\sqrt m$，因为同一实际后缀保持向量差。理想准备中全负扇区的平方范数为 $f_0$，在后缀前后与成功扇区保持正交。比较到归一化成功准备的半迹距离为 $\sqrt{f_0}$；对泄漏振幅分解两分量并用三角不等式，其贡献也至多 $\sqrt{f_0}$。随后对成功准备应用 (21.23)–(21.24)，对 $\mathcal G$ 应用 (21.16)，最后接入相同 $L$ 读出和有理方向解码。得实际获取的泄漏与实际方向坏事件 $b_{\rm acq}$ 的界

$$
\begin{aligned}
\sqrt{p_{\rm acq}}&\le K_{\rm cap}/\sqrt t+2q/\sqrt m
                   +\sqrt{2^{-q}}+\sqrt{\nu2^{-q}}+4\sqrt S,\\
b_{\rm acq}:=\Pr_{\rm actual}[\|\widehat h-h\|_\infty>e/16]
 &\le 3C_{\rm fail}/\lambda+4\exp[-(m+2)e^2/16384]+1/(32t)\\
 &\qquad+2q/\sqrt m+\sqrt{2^{-q}}+\sqrt{\nu2^{-q}}+\sqrt{5S}.
\end{aligned}
\tag{21.25}
$$

方向界使用相同完整口上的距离比较及事件概率差；没有对 $K_{\rm work}$ 作替换，也没有在返回估计中迹掉它。$\kappa_h$ 是从原唯一参考接触实际取得的口所对应的比较因子，不是另行供应的含 $h$ 输入。

对终端取 $P_h=\tau_h\otimes I$。由 (20.27)–(20.28) 的原谱系数及 $\sin^2 x\le x^2$，

$$
\|(I-P_h)U_{\rm term}P_h\|\le\sqrt{g_m}\le d/\sqrt m,\qquad
g_m=\frac{4m}{D^2}\sin^2\!\left(\frac{dD}{2m}\right).
\tag{21.26}
$$

对含旧相关及实际独立令牌的任意密度算子 $\rho$，将 $(I-P_h)U_{\rm term}\rho^{1/2}$ 在 $U_{\rm term}$ 前按 $P_h,I-P_h$ 分解，用 Hilbert–Schmidt 三角不等式，得终端至多增加 $d/\sqrt m$ 的泄漏振幅。非参考采样、读出和算术不增加参考泄漏。故同一完成态满足

$$
\sqrt{p_R(n,h)}\le K_{\rm cap}/\sqrt t+(2q+d)/\sqrt m
                   +\sqrt{2^{-q}}+\sqrt{\nu2^{-q}}+4\sqrt S .
\tag{21.27}
$$

终端只作用于 $R$ 和未经改动的独立原令牌，保持已经写好的解码边缘。

### 21.6 逐支预算及全部原场的成功

实际前向调用精确为 $q+B$：准备付 $q$ 次，每字的 $q$ 槽不论活动与否各付一次。由 (21.11)–(21.12)，

$$
\frac{B}{L}\le\frac{K_N eH}{270000}
 \le\frac{K_N\sqrt e}{270000}<\frac14,\qquad
\frac{q}{L}\le\frac{64e^4}{270000}<\frac14 ,
\tag{21.28}
$$

其中 $H\le e^{-1/2}$ 且 $e\le1/(10^6K_N^2)$。因此 $q+B\le L/2\le L$。场重置恰为 $15\ell+1\le18N<Q$，终端恰一次，故参考接触恰为 $q+B+1$。不存在按期望计算或免费省去的槽。

同一组界给

$$
2q/\sqrt m\le e/100,\qquad
\sqrt{2^{-q}}\le e/100,\qquad
\sqrt{\nu2^{-q}}\le e/100,\qquad
\sqrt{5S}\le e/100.
\tag{21.29}
$$

第一项用 $q\le64H$、$\sqrt m\ge10^7 e^{-4}H$；中间两项用 $2^{-q}\le e/(DL)$、$\nu\le L$ 及 $D\ge m\ge10^{15}e^{-8}H^2$。最后一项用

$$
\sqrt{5S}\le5 B^{3/2}/m
 \le 5 K_N^{3/2}e^{7/2}H/10^{15}
 \le 5 K_N^{3/2}e^3/10^{15}
 \le e/100
\tag{21.30}
$$

以及 (21.6) 的阈值。(21.25) 中其余三项合并至多 $K_{\rm risk}/t+4\exp(-t/16384)$，其中 $K_{\rm risk}=3\cdot768^2 C_{\rm fail}+1$。由 (2.8) 的 $t\ge6K_{\rm risk}/e$、$t\ge16384\log(24/e)$，这部分至多 $e/3$，故 $b_{\rm acq}\le e/3+4e/100$。

十五个场均值坏事件的总概率由 (20.16) 至多 $30\exp(-\ell e^2u^2/512)\le e/3$。在两类好事件上，$\|\widehat h-h\|_2\le e/8$，$\|\widehat n(z)-n(z)\|_2\le eu/8$；原二阶导数上界使精确中心差分偏差至多 $u$，两端样本另贡献至多 $e/8$，故 $\|\widehat g_a-n_a(0)\|_2\le e/4$。代入 (21.9)，由 (20.19)–(20.21) 同一分解，四坐标误差分别至多 $11e/16,11e/32,0,5e/16$。这里只用原上界，不增加导数下界或限制场或方向。于是完成运行失败概率至多 $2e/3+4e/100<e$，不要求两个好事件独立。采样和终端分别有 $|u|<r$、$d<r$。当 $e>e_0$，原精度 $e$ 上的定理 20.3 直接给成功及确定预算。两支的所有计数和输出字母表有限。

### 21.7 统一无对数常数及同一完整边缘

将 (21.27) 乘 $\sqrt t=e\sqrt m$。第一项变为 $K_{\rm cap}$；准备项至多 $128eH\le128$，终端项 $de\le1$。由 $\nu\le L$ 和 $2^{-q}\le e/(DL)$，全负及截止的两项乘 $\sqrt t$ 后各至多一。路由项为

$$
4\sqrt S\,\sqrt t
 =8e B^{3/2}/\sqrt D
 \le(8/10^7)K_N^{3/2}\sqrt e\,H^2
 \le K_N^2.
\tag{21.31}
$$

末步用 $K_N\ge1$ 及 $\sup_{y\ge0}y^2\exp(-y/2)=16\exp(-2)<3$。故此支有

$$
p_R(n,h)\le (K_{\rm cap}+K_N^2+131)^2/(me^2).
\tag{21.32}
$$

对 $e>e_0$，(20.29)–(20.37) 在该支自身完整运行上给

$$
p_R(n,h)\le\frac{3k+d^2}{m}
 \le\frac{6400\log(18/e)}{me^2}
 \le\frac{6400\log(18/e_0)}{me^2}.
\tag{21.33}
$$

(21.6) 的同一个 $C$ 覆盖两支。对每支的实际完成态直接用 (20.32)–(20.34)：以 $P_h=\tau_h\otimes I_K$ 分块，正交参考块的迹为 $p_R$，交叉块的迹范数至多 $\sqrt{p_R(1-p_R)}$；其参考偏迹为零，比较乘积态的第二因子正是这两对角块给出的实际 $\operatorname{Tr}_R\Omega_{n,h}$。故

$$
\frac12\|\Omega_{n,h}-\tau_h\otimes\operatorname{Tr}_R\Omega_{n,h}\|_1
 \le p_R+\sqrt{p_R(1-p_R)}\le2\sqrt{p_R}.
\tag{21.34}
$$

再取一般距离界一，得 (21.10) 的无对数 $O(1/(e\sqrt{m_e}))$ 完整返回。张量同一独立混合密度算子不改变人口、距离或解码事件概率；不需要最小本征值为正、辅助密度逆或可访问纯化。$\square$

**命题 21.5（一次成功逻辑作用后的有限缓存失配）。** 固定 $h=e_z$，参考为原一次准备的 $\tau_{e_z}$，取已知独立缓存 $|\uparrow\rangle$、逻辑探针 $|\downarrow\rangle$。一个 $Q_D$ 字在第一活动槽成功后，紧随的非活动槽对缓存的原生调用出现负标签的条件概率恰为 $4m/D^3$；首槽成功且该槽出现负标签的联合概率为 $2m/D^3$。这里考虑有该非活动槽的字（$q\ge2$），并固定这一输入与这一槽序列。

证明。令 $e_b=|j,j-b\rangle_{e_z}$。由 (21.3) 及 OTF004 (13.14)，归一化的成功逻辑态为

$$
Q_D(e_0|\downarrow\rangle)
 =\frac{1-m}{D}e_0|\downarrow\rangle
  +\frac{2\sqrt m}{D}e_1|\uparrow\rangle.
\tag{21.35}
$$

由 (21.19)，第一分量无失配，第二分量的缓存负投影平方范数因子为 $1/D$；两分量的逻辑探针正交，故负标签概率为 $4m/D^3$。首槽奇偶为零的质量为 $1/2$，得联合概率。此例排除该有限输入上的精确无害缓存恒等式；(21.21) 已按 $N_h/D$ 支付这类缺陷。$\square$

**定义 21.6（适用域及原来源对应）。** 定理 21.4 是 §§3–6 的完整逻辑等距在上述原实际菜单前提下的应用；其承重对应为 (21.20)–(21.24) 的完整历史路由，随后由同一运行消费于 (21.25)–(21.34)。$\Omega_{n,h}$ 是此有限数学消费者的实际端口语义下的完成态。原物理来源 $\Omega$ 则是 [PB 实际探针与环境耦合续卷 §6](AURIC_FULL_PB_ACTUAL_PROBE_AND_ENVIRONMENT_COUPLING_CONTINUATION.md) 与 [PB 两角正证书续卷定义 49.1、边界 49.2](AURIC_FULL_PB_TWO_CORNER_POSITIVE_CERTIFICATE_CONTINUATION.md) 中同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ 的来源对象。完整合同及全部版本身份沿用边界 20.4，逐层保留原定义、全文、量词及固定上游；外层引用不替代内层 SQ、AH、SF、PB 等来源身份，原 $S(a,b)=a\circ b$ 和原响应 $D$ 也不换成电路符号。

同一原 $\Omega$ 仍须共同给出下列七项，各项连同上述全文与全部递归上游保留：

1. 原复 Hilbert、原可观测量、原标签与共同全词上的实际相干准备及合法控制。
2. 原态、效果、Born 绑定、实际完整菜单及全部质量，包括零、不等、次归一、静默与非正常支。
3. 同一实际来源的真正相关联合、复合、张量与实际参考副本。
4. 每条实际 typed CP 分支、未归一上下文、全部输出与合法未来，以及整台递归参考。
5. 完整仪器、TP、成功／失败与细记录输出、条件更新及原 Lüders 前件。
6. 全部合法历史、真遗忘、实际完整活动输出、读后 ready、第一合法消费者及真实全未来 Return／CountRead。
7. 实际动力学、物理钟、能量、一般生成元域及共同正 $\hbar$。

有限数学等距、同一运行的自身边缘比较、相同边缘、形式环境和声明 CP 端口不供应这些同源物理条件。实际接受关联仍守 PB 边界 49.2 的原域和未归一标尺；自身边缘比较不是对全部合法未来的真实 Return。其他有限读出或地址关系不作为定理 21.4 的量子菜单前提。此处的原生控制见证要求供应具体非参考矩阵及准备，不能从其数学描述倒推出实际菜单。

定理 21.4 的充分机制不成为所有原控制器的必要条件。大精度支的 $3k$ 槽、新鲜 $I/2$ 和固定调度仍只是 §20 的见证。小精度支路由探针，不在 §19 固定同探针、仅历史处理的局部障碍类内。§§1–11 的声明 CP 结果、§§12–15 的部分保留条件、§16 的重置必要阶与匹配阶、§17 的无条件旋转反例各保留原域。§18 的完整等距、共同二值置信读出下界保留其准确前件，与 (21.10) 的量级相容；不扩张为任意约化 CP 下界，也不由 (21.10) 取得该类的 $O(1/t)$ 完整返回。§20 的 $B_e$ 及其人口公式仍是原电路的结论，不转移到小精度支的新端口。

## 追加锚（本行以下为增补区）

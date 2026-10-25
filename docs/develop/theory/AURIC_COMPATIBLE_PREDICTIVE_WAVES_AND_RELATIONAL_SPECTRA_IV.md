# AURIC 相容预测波与关系谱 IV：原生完整记录的条件数与观察深度

## 44. 固定源、完整联合距离与复通道范数

**假设 44.1（供应对象及取得合同）。** 本卷接续[第二卷](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_II.md) §§39–43，编号从 §44 起。固定[第一卷](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md) §17.1 的五维物理空间、等距嵌入 $B$、原 Kraus 算子 $K_0,K_1$、终端任务 $P=BEB^\dagger$，以及同一就绪环境、相互作用和环境丢弃合同。固定 $0<d<1$ 及一个已知实角度 $\theta$，不允许随数据改变角度。相容集合始终是第一卷 (35.4)–(35.5) 的全部复混合态集合 $\mathcal K_d$，后继通道及原域提升由第二卷 (39.2) 和第一卷定理 35.4 供应：

$$
S_\rho(X)=B\bigl[UP_+XP_+U^\dagger+(f^\dagger Xf)\rho\bigr]B^\dagger,
\qquad \rho\in\mathcal K_d,\quad X\in M_3(\mathbb C).
\tag{44.1}
$$

以下始终使用正交基 $(\xi,e,f)$；该基中

$$
U=\begin{pmatrix}1&0&0\\0&-1/2&\sqrt3/2\\0&\sqrt3/2&1/2\end{pmatrix},
\quad W=\operatorname{diag}(1,1,-1),
\quad q=\frac1{\sqrt2}\begin{pmatrix}1\\1\\0\end{pmatrix},
\quad E=qq^\dagger,\quad C=2\xi\xi^\dagger.
\tag{44.2}
$$

保留第二卷假设 39.2 的全部标签、两个终端结果、原始联合权重和指定有限终点。具体地，

$$
\begin{gathered}
V_0=Ue^{\mathrm i\theta W},\qquad V_1=V_0W,\qquad
h=(j_1,\ldots,j_n),\\
V_h=V_{j_n}\cdots V_{j_1},\qquad
M_h=V_h^\dagger EV_h,\qquad V_\varnothing=I_3,\\
s=\sin(2\theta),\quad c=\cos(2\theta),\quad z=e^{-2\mathrm i\theta},
\quad a_\theta=\operatorname{dist}\bigl(\theta,(\pi/2)\mathbb Z\bigr)\in[0,\pi/4].
\end{gathered}
\tag{44.3}
$$

$j_1$ 最早作用。第二卷定理 39.3 已给实际压缩效果 $2^{-n}M_h$ 和 $2^{-n}(I_3-M_h)$；这里直接使用该完整物理桥，不另设可选分支模型。精确表是条件性供应的数据，不由一次历史出现、独立同分布样本或额外输入制备推出。已知角度不含角度标定、反馈、逆门或相位控制的取得权。

**定义 44.2（加权记录半范数与相容模量）。** 对迹零 Hermitian 矩阵 $H$ 定义

$$
\begin{aligned}
f_h(H)&=\operatorname{Tr}(HM_h),\\
\delta_{\theta,n}(H)&=2^{-n}\sum_{|h|=n}|f_h(H)|,\\
\Delta_{\theta,N}(H)&=\max_{0\le n\le N}\delta_{\theta,n}(H),
\qquad
\Delta_{\theta,\infty}(H)=\sup_{n\ge0}\delta_{\theta,n}(H).
\end{aligned}
\tag{44.4}
$$

$N$ 为非负整数，空词也在定义内。对 $N\in\mathbb N_0\cup\{\infty\}$ 置

$$
\Lambda_N(d,\theta)=
\sup_{\substack{\rho,\sigma\in\mathcal K_d\\\rho\ne\sigma}}
\frac{\|\rho-\sigma\|_1}{\Delta_{\theta,N}(\rho-\sigma)}.
\tag{44.5}
$$

分子非零而分母为零时，比值定义为 $+\infty$。若把相同态也放入记号，约定 $0/0=0$；它们不影响上确界。全历史模量是先对每一对态取 $\sup_n\delta_{\theta,n}$ 后再取 (44.5) 的上确界，不预先交换这两个运算。$\Delta_{\theta,N}$ 的最大值比较分别指定终点的表；它不是把不同终点无代价合并成一个实验的总变差距离。

**定理 44.3（完整记录的精确总变差与 diamond 桥）。** 令 $p_{\theta,n}(\rho)$ 为 qutrit 态 $\rho$ 经原仪器 $n$ 步后，历史与终端二元回答的完整联合表。则对所有 $\rho,\sigma\in\mathcal K_d$，

$$
\operatorname{TV}\bigl(p_{\theta,n}(\rho),p_{\theta,n}(\sigma)\bigr)
=\delta_{\theta,n}(\rho-\sigma).
\tag{44.6}
$$

令 $\mathcal R_{\theta,n}:M_5\to M_{2^{n+1}}$ 为实际完整经典记录通道，即其 $(h,y)$ 对角条目是 $\operatorname{Tr}(A_hYA_h^\dagger P_y)$，其中 $P_1=P$、$P_0=I_5-P$。则使用不除以二的 diamond 范数，有

$$
\begin{aligned}
\|\mathcal R_{\theta,n}S_\rho-\mathcal R_{\theta,n}S_\sigma\|_\diamond
 &=2\delta_{\theta,n}(\rho-\sigma),\\
\|S_\rho-S_\sigma\|_\diamond&=\|\rho-\sigma\|_1.
\end{aligned}
\tag{44.7}
$$

这两个等式均覆盖全部复输入矩阵及任意有限未触动参考，不限于无参考密度矩阵。

证明。记 $H=\rho-\sigma$。第二卷 (39.5) 给每个历史的两个差条目恰为

$$
r_H(h,1)=2^{-n}f_h(H),\qquad
r_H(h,0)=-2^{-n}f_h(H).
\tag{44.8}
$$

因此 $\|r_H\|_{\ell^1}=2\delta_{\theta,n}(H)$，总变差除以二便是 (44.6)。这里没有删去终端否回答，也没有把 $2^{-n}$ 除掉。

由 (44.1)，对任意复矩阵 $X$，

$$
(\mathcal R_{\theta,n}S_\rho-\mathcal R_{\theta,n}S_\sigma)(X)
=(f^\dagger Xf)\operatorname{diag}(r_H).
\tag{44.9}
$$

对任意 $k\ge1$ 和任意 $Z\in M_k\otimes M_3$，定义

$$
Z_{ff}=(I_k\otimes f^\dagger)Z(I_k\otimes f).
$$

放大差映射的像为 $Z_{ff}\otimes\operatorname{diag}(r_H)$。迹范数理想不等式给 $\|Z_{ff}\|_1\le\|Z\|_1$，张量迹范数相乘，所以 diamond 上界为 $\|r_H\|_{\ell^1}$；无参考输入 $ff^\dagger$ 达到该上界。这是范数等式的数学见证，不是新增制备权限。

同样，后继差映射的放大像为 $Z_{ff}\otimes BHB^\dagger$。等距嵌入保留迹范数，输入 $ff^\dagger$ 再达到上界，得到第一卷 (35.8) 的第二个等式。上述证明不对 $Z$ 加实性、正性或纯性限制。∎

**定理 44.4（统一连续性）。** 在迹零 Hermitian 空间上，每个 $\delta_{\theta,n}$、$\Delta_{\theta,N}$ 及 $\Delta_{\theta,\infty}$ 都满足

$$
0\le \delta_{\theta,n}(H)\le\frac{\|H\|_1}{2},
\qquad
|\Delta_{\theta,N}(H)-\Delta_{\theta,N}(K)|
\le\frac{\|H-K\|_1}{2}.
\tag{44.10}
$$

证明。将 $H=H_+-H_-$ 作正负谱分解，$\operatorname{Tr}H_\pm=\|H\|_1/2$。对任意 $0\preceq M\preceq I$，$|\operatorname{Tr}(HM)|\le\|H\|_1/2$。每层的 $2^n$ 个权重之和为一，故有第一式。三角不等式给 $|\delta_{\theta,n}(H)-\delta_{\theta,n}(K)|\le\delta_{\theta,n}(H-K)$；取有限最大值或上确界给第二式，包括 $N=\infty$。∎

## 45. 全六实方向的严格正实现与参数独立性

**定义 45.1（源的仿射方向空间）。** 令

$$
\mathcal L=\{H=H^\dagger:
\operatorname{Tr}H=\operatorname{Tr}(CH)=\operatorname{Tr}(EH)=0\}.
\tag{45.1}
$$

在 $(\xi,e,f)$ 中它恰为以下六实维空间：

$$
H(x,y,b,t,u,v)=
\begin{pmatrix}
0&-t/2+\mathrm ix&y+\mathrm ib\\
-t/2-\mathrm ix&t&u+\mathrm iv\\
y-\mathrm ib&u-\mathrm iv&-t
\end{pmatrix},
\qquad x,y,b,t,u,v\in\mathbb R.
\tag{45.2}
$$

这里 $t$ 只是方向坐标；第一卷的纤维参数为 $\sqrt d$。由 $C=2\xi\xi^\dagger$ 得 $H_{\xi\xi}=0$，迹零给 $H_{ff}=-H_{ee}$，而 $q^\dagger Hq=0$ 给 $\Re H_{\xi e}=-H_{ee}/2$。特别地，该实部不能在保留 $t$ 的同时设为零。每对相容态的差都属于 $\mathcal L$。

**定理 45.2（每个方向都有真正正态双世界）。** 对每个 $0<d<1$ 和每个 $0\ne H\in\mathcal L$，存在明确的 $\lambda>0$ 和 $\rho_\pm\in\mathcal K_d$ 使

$$
\rho_+-\rho_-=2\lambda H,
\tag{45.3}
$$

且两态均严格正，源的额外 $B_d$ 正性及 $\rho_{aa}-d\ge0$ 均严格满足。两态各有原五维域 CPTP 提升。

证明。沿用第二卷的 $(a,h_{\rm out},g)=(Uq,Ur,Uf)$ 和第一卷的

$$
\tau=3-2\sqrt2,\qquad
\ell=c_\ell(h_{\rm out}-\tau a),\qquad c_\ell=\frac{2+\sqrt2}{\sqrt{12}},
\quad \|\ell\|=1.
$$

写 $\beta=1-d$、$\varepsilon=d\beta/100$，取第二卷 (42.12) 已有严格点，在这一后继基中为

$$
\rho_0=
\begin{pmatrix}
d+\varepsilon&-\varepsilon&4\varepsilon/\sqrt6\\
-\varepsilon&\varepsilon&0\\
4\varepsilon/\sqrt6&0&\beta-2\varepsilon
\end{pmatrix}.
\tag{45.4}
$$

其源参数为 $s_\rho=y_\rho=\varepsilon$、$w_\rho=v_\rho=m_\rho=n_\rho=0$；这里 $s_\rho=\rho_{aa}-d$，与 $\sin(2\theta)$ 不同。由第一卷 (35.9)，或用第二卷 (40.17) 中 $q=(a+3h_{\rm out}+\sqrt6g)/4$ 直接配对，

$$
\operatorname{Tr}\rho_0=1,\quad
\operatorname{Tr}(C\rho_0)=d,\quad
\operatorname{Tr}(E\rho_0)=\frac{6-5d}{16}.
\tag{45.5}
$$

$\varepsilon>0$ 且 $\beta-2\varepsilon\ge49\beta/50>0$。对 (45.4) 后两个对角条目取 Schur 补，剩余条件为

$$
d-\frac{8\varepsilon^2}{3(\beta-2\varepsilon)}>0,\qquad
\frac{8\varepsilon^2}{3(\beta-2\varepsilon)}
\le\frac{d^2\beta}{3675}<d.
\tag{45.6}
$$

故 $\rho_0\succ0$。对第一卷 (35.5) 的 $B_d$，有

$$
\det B_d(\rho_0)
=c_\ell^2\bigl[d\varepsilon(1-\tau^2)-\varepsilon^2(1+\tau)^2\bigr]>0.
\tag{45.7}
$$

严格性来自 $\varepsilon/d=\beta/100<(1-\tau)/(1+\tau)=1/\sqrt2$；其左上条目为 $d>0$，故 $B_d(\rho_0)\succ0$。同时 $s_{\rho_0}=\varepsilon>0$。这些严格条件对整个六维仿射平面都是开条件，而不只对固定 $s_\rho$ 的五维截面成立。

将 $H$ 换到与 $\rho_0$ 相同的正交基，置

$$
h_0=\|H\|_{\rm op},\quad
\mu=\lambda_{\min}(\rho_0)>0,\quad
\nu=\lambda_{\min}(B_d(\rho_0))>0,\quad
\lambda=\frac{\min\{\mu,\nu/2,\varepsilon\}}{2h_0},
\qquad \rho_\pm=\rho_0\pm\lambda H.
\tag{45.8}
$$

则 $\rho_\pm\succeq\mu I/2$，且 $s_{\rho_\pm}\ge\varepsilon/2$。$B_d$ 的方向变化为

$$
\mathcal B(H)=
\begin{pmatrix}
0&a^\dagger H\ell\\
\ell^\dagger Ha&\ell^\dagger H\ell
\end{pmatrix}.
$$

各非零条目绝对值至多 $h_0$，Hermitian 矩阵的最大绝对行和界给 $\|\mathcal B(H)\|_{\rm op}\le2h_0$。因此

$$
B_d(\rho_\pm)\succeq
\bigl(\nu-2\lambda h_0\bigr)I_2\succeq\nu I_2/2.
\tag{45.9}
$$

仿射矩约束由 $H\in\mathcal L$ 保留，第一卷定理 35.4 遂给 $\rho_\pm\in\mathcal K_d$。

为明确原域对应，使用该供应定理的构造：对任一 $\rho=\rho_\pm$，令

$$
L_\rho=\ell^\dagger\rho\ell,\qquad
A_{\min}=\frac{\rho\ell\ell^\dagger\rho}{L_\rho},\qquad
\gamma_\rho=\frac{d-(A_{\min})_{aa}}{\rho_{aa}-(A_{\min})_{aa}},
\quad
A=(1-\gamma_\rho)A_{\min}+\gamma_\rho\rho,\quad D=\rho-A.
\tag{45.10}
$$

供应定理给 $0\preceq A_{\min}\preceq\rho$、$(A_{\min})_{aa}\le d<\rho_{aa}$，故分母正且 $0\le\gamma_\rho<1$；$A,D\succeq0$、$a^\dagger Aa=d$，$D$ 支持于原固定 $N=\ell^\perp$。取原酉识别 $V:\mathbb C^5\to\mathbb C^3\oplus N$，则

$$
\omega=V^\dagger(A\oplus D)V,\qquad
T_\omega(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega
\tag{45.11}
$$

正是第一卷 (35.6) 的原域 CPTP 提升，且 $\mathcal GT_\omega=S_\rho$。这里消费其全域提升结果，不把无物理实现的方向直接计作相容通道。∎

**定理 45.3（全部开参数域上的齐次独立性）。** 对每个固定 $\theta$ 及 $N\in\mathbb N_0\cup\{\infty\}$，

$$
\Lambda_N(d,\theta)
=\sup_{0\ne H\in\mathcal L}
\frac{\|H\|_1}{\Delta_{\theta,N}(H)}.
\tag{45.12}
$$

右边不依赖 $d$，因而以下也记作 $\Lambda_N(\theta)$。

证明。任意相容差在 $\mathcal L$ 内，给左边不大于右边。反向，对任意非零方向使用定理 45.2；分子和分母同乘 $2\lambda$，比值完全不变，零分母也保留。于是反向不等式成立。$d$ 接近端点时，(45.8) 的态分离尺度可以缩小；这里独立的是齐次模量，不是一个统一正分离的见证尺度。∎

## 46. 深度三的加权奇偶反演

**定理 46.1（源特定的精确六坐标反演）。** 固定 $s\ne0$。对 $H=H(x,y,b,t,u,v)\in\mathcal L$，以下从实际表取得的实数

$$
\begin{array}{lll}
S_1=(f_0+f_1)/2,&D_1=(f_0-f_1)/2,\\
S_2=(f_{00}+f_{10})/2,&D_2=(f_{00}-f_{10})/2,\\
S_3=(f_{000}+f_{100})/2,&D_3=(f_{000}-f_{100})/2,\qquad T=f_{010}
\end{array}
\tag{46.1}
$$

满足

$$
S_1=0,\qquad S_2=-\frac34sx,\qquad
S_3=-(1-c)S_2+\frac9{16}s^2t.
\tag{46.2}
$$

置 $R=T+S_2+S_3$，则

$$
\begin{pmatrix}D_1\\D_2\\D_3\\R\end{pmatrix}
=\mathsf B(z)\begin{pmatrix}y\\b\\u\\v\end{pmatrix},
\tag{46.3}
$$

其中一个全实三角形式是

$$
\mathsf B=\frac{\sqrt3}{16}
\begin{pmatrix}
8c&-8s&-4c&4s\\
8c^2-4c-4&(4-8c)s&2c^2+2c-4&(-2c-2)s\\
8c^3+8c^2-4c-4&(-8c^2-8c)s&-c^3-4c^2-c+2&(c^2+4c+3)s\\
-8c^3+16c^2+8c-8&(8c^2-16c-4)s&c^3-2c^2-c-2&(-c^2+2c-1)s
\end{pmatrix}.
\tag{46.4}
$$

它的 Laurent 有理逆为

$$
\mathsf B^{-1}=\frac{\sqrt3}{9}
\begin{pmatrix}
\dfrac{2(3z^4-3z^3+4z^2-3z+3)}{z(z-1)^2}
&\dfrac{4(z^2+1)}{(z-1)^2}
&-\dfrac{8(z^2+z+1)}{(z+1)^2}
&-\dfrac{8(z^2-z+1)}{(z-1)^2}\\
-\dfrac{2\mathrm i(3z^4+3z^3+4z^2+3z+3)}{z(z-1)(z+1)}
&-\dfrac{4\mathrm i(z+1)}{z-1}
&\dfrac{8\mathrm i(z^2-z+1)}{(z-1)(z+1)}
&\dfrac{8\mathrm i(z^2+z+1)}{(z-1)(z+1)}\\
\dfrac{16z}{(z-1)^2}
&-\dfrac{4(z^2-6z+1)}{(z-1)^2}
&-\dfrac{4(z-1)^2}{(z+1)^2}
&-\dfrac{4(z+1)^2}{(z-1)^2}\\
-\dfrac{16\mathrm iz}{(z-1)(z+1)}
&\dfrac{4\mathrm i(z^2-4z+1)}{(z-1)(z+1)}
&\dfrac{4\mathrm i(z^2-4z+1)}{(z-1)(z+1)}
&\dfrac{4\mathrm i(z^2+4z+1)}{(z-1)(z+1)}
\end{pmatrix}.
\tag{46.5}
$$

证明。第二卷 (40.7)–(40.10) 已给这七个效果的明确向量及奇偶坐标。用 (45.2) 与其迹配对：偶部分只剩 $x,t$，得到 (46.2)；$M_{010}$ 的偶配对为 $-S_2-S_3$，故 $R$ 只有奇部分。对一个奇效果 $M$，配对为

$$
2\bigl[y\Re M_{02}+b\Im M_{02}
+u\Re M_{12}+v\Im M_{12}\bigr].
$$

将第二卷 (40.10) 四列依次代入即为 (46.4)；因子二来自 Hermitian 非对角配对，不能略去。

式 (46.5) 是明确的代数证书。具体地，在 (46.4) 中代入

$$
c=\frac{z+z^{-1}}2,\qquad
s=\frac{z^{-1}-z}{2\mathrm i},
\tag{46.6}
$$

与 (46.5) 相乘，四个对角分子分别约为共同分母，十二个非对角分子分别为零，所以 $\mathsf B\mathsf B^{-1}=I_4$。这只使用 $z z^{-1}=1$，在 $z\ne0,\pm1$ 上为有理恒等式；特别地，单位圆上的对应是实线性逆。这里的 $\mathsf B$ 是四阶分析矩阵，与原物理嵌入 $B$ 不同。相同代入给

$$
\det\mathsf B=\frac{81}{512}s^4.
\tag{46.7}
$$

可逆性及下一条中的极点界由实际逆矩阵承担，不从行列式消失阶数推断条件数。所有效果仍是第二卷供应的实际效果；从表坐标作线性运算不执行选支或逆门。∎

**定理 46.2（完整分支权重下的显式上界）。** 若 $s\ne0$，则

$$
\Lambda_3(\theta)\le\frac{C_3}{s^2},\qquad
C_3=\frac{128(1+\sqrt2)}9+\frac{16}3+\frac{896\sqrt3}3<557.
\tag{46.8}
$$

证明。令 $\delta=\Delta_{\theta,3}(H)$。完整表的权重直接给

$$
\begin{gathered}
|D_1|\le\delta,\qquad
|S_2|,|D_2|\le2\delta,\qquad
|S_3|,|D_3|\le4\delta,\\
|T|\le8\delta,\qquad |R|\le14\delta.
\end{gathered}
\tag{46.9}
$$

例如 $|S_3|,|D_3|\le(|f_{000}|+|f_{100}|)/2\le4\delta_{\theta,3}$；单独一坐标则至多 $8\delta_{\theta,3}$。这些是原联合范数的损耗因子，没有把少数历史的概率重新归一化。

由 (46.2) 和 $|1-c|\le2$，

$$
|x|\le\frac{8\delta}{3|s|},\qquad
|t|\le\frac{16(4+2\cdot2)\delta}{9s^2}
=\frac{128\delta}{9s^2}.
\tag{46.10}
$$

为完整控制奇逆，单位圆上

$$
|z-1||z+1|=2|s|,\qquad
\frac1{|z\pm1|^2}\le\frac1{s^2},\qquad |z\pm1|\le2.
\tag{46.11}
$$

第二式来自 $s^2=|z-1|^2|z+1|^2/4$。对 (46.5) 的各多项式取系数绝对值之和，得到逐条目的界

$$
\begin{pmatrix}|y|\\|b|\\|u|\\|v|\end{pmatrix}
\le\frac{\sqrt3}{9}
\begin{pmatrix}
s^{-2}&0&0&0\\0&|s|^{-1}&0&0\\
0&0&s^{-2}&0\\0&0&0&|s|^{-1}
\end{pmatrix}
\begin{pmatrix}
32&8&24&24\\16&8&12&12\\16&32&16&16\\8&12&12&12
\end{pmatrix}
\begin{pmatrix}|D_1|\\|D_2|\\|D_3|\\|R|\end{pmatrix}.
\tag{46.12}
$$

例如第一条目的四次多项式系数绝对值之和为 $16$，给第一行第一系数 $32$；第二行含 $(z+1)/(z-1)$ 的条目使用 $|z+1|^2/(2|s|)\le2/|s|$。其余条目分别使用多项式界 $2,3,4,6,8$ 和 (46.11)。代入权重向量 $(1,2,4,14)$ 得

$$
\begin{aligned}
|y|&\le\frac{160\sqrt3}{3s^2}\delta,&
|b|&\le\frac{248\sqrt3}{9|s|}\delta,\\
|u|&\le\frac{368\sqrt3}{9s^2}\delta,&
|v|&\le\frac{248\sqrt3}{9|s|}\delta.
\end{aligned}
\tag{46.13}
$$

方向坐标 $t$ 的基矩阵为

$$
H_T=\begin{pmatrix}0&-1/2&0\\-1/2&1&0\\0&0&-1\end{pmatrix},
\tag{46.14}
$$

其特征值为 $(1+\sqrt2)/2,(1-\sqrt2)/2,-1$，迹范数为 $1+\sqrt2$。其余五个坐标基矩阵的非零特征值均为 $1,-1$，迹范数各为二。因此

$$
\|H\|_1\le(1+\sqrt2)|t|+2(|x|+|y|+|b|+|u|+|v|)
\le\frac{C_3}{s^2}\delta,
\tag{46.15}
$$

其中仅在最后一步使用 $|s|^{-1}\le s^{-2}$。由定理 45.3 得模量上界。最后，$\sqrt2<14143/10000$、$\sqrt3<17321/10000$ 可由平方验证，代入 $C_3$ 给

$$
C_3<\frac{3133072}{5625}<557.
$$

故常数的严格上界亦不依赖数值拟合。∎

## 47. 真实态见证、例外角度与固定深度指数

**定理 47.1（深度三的正态下见证及浅层无限模量）。** 对 (46.14) 的 $H_T$，

$$
f_h(H_T)=0\quad(|h|\le2),\qquad
f_{j_1j_2j_3}(H_T)=(-1)^{j_2+j_3}\frac9{16}\sin^2(2\theta).
\tag{47.1}
$$

因而

$$
\Delta_{\theta,3}(H_T)=\frac9{16}s^2,\qquad
\Lambda_3(\theta)\ge\frac{16(1+\sqrt2)}{9s^2}\quad(s\ne0),
\tag{47.2}
$$

并且对所有实 $\theta$，$\Lambda_0=\Lambda_1=\Lambda_2=+\infty$。这些下界在每个 $0<d<1$ 都由真正相容正态实现。

证明。$H_T\in\mathcal L$。在 (44.2) 中用 $V'_0=U\operatorname{diag}(1,1,z)$、$V'_1=V'_0W$ 计算共轭效果即可去掉无关的共同标量相位。向量递推 $x_h=(V'_h)^\dagger q$ 给空词、两个单字词、四个二字词的 $x_h^\dagger H_Tx_h$ 均为零；八个三字词的值除以 $9s^2/16$ 依次为

$$
\begin{array}{c|rrrrrrrr}
h&000&001&010&011&100&101&110&111\\ \hline
\text{符号}&1&-1&-1&1&1&-1&-1&1
\end{array}.
\tag{47.3}
$$

为明确表中恒等式的代数，所有 $x_h$ 均可写为 $(\xi+\alpha_he+\beta_hf)/\sqrt2$，其中 $|\alpha_h|^2+|\beta_h|^2=1$。于是

$$
f_h(H_T)=|\alpha_h|^2-\frac12-\frac12\Re\alpha_h.
$$

置 $\epsilon_j=(-1)^{j}$，逐次使用 (44.2) 给

$$
\begin{aligned}
\alpha_\varnothing&=1,\qquad \alpha_{j_1}=-1/2,\\
\alpha_{j_1j_2}&=\frac{1+3\epsilon_{j_2}z^{-1}}4,\\
\alpha_{j_1j_2j_3}
&=\frac{-1-3(\epsilon_{j_2}+\epsilon_{j_3})z^{-1}
+3\epsilon_{j_2}\epsilon_{j_3}z^{-2}}8.
\end{aligned}
$$

代入上一式，使用 $\epsilon_j^2=1$、$z+z^{-1}=2c$ 和 $1-c^2=s^2$，前三级分别为零，第四式恰为 $9\epsilon_{j_2}\epsilon_{j_3}s^2/16$，即 (47.3)。最早标签只改变 $\beta_h$ 的符号，不改变上述配对。这些恒等式在 $s=0$ 也由其多项式形式成立。原始平均权重 $2^{-3}$ 使八个相同绝对值的和仍为 $9s^2/16$，不是八倍此数。

定理 45.2 以 $H=H_T$ 给 $\rho_\pm=\rho_0\pm\lambda H_T$；差的迹范数为 $2\lambda(1+\sqrt2)$，记录差为 $2\lambda$ 倍 (47.1)。比例给 (47.2)，浅层分母为零而两态确实不同，故浅层模量无限。∎

**定理 47.2（精确例外的全深度正态盲区）。** 令

$$
H_Y=\begin{pmatrix}0&0&0\\0&0&\mathrm i\\0&-\mathrm i&0\end{pmatrix}.
\tag{47.4}
$$

若 $\theta\in(\pi/2)\mathbb Z$，则 $\Delta_{\theta,\infty}(H_Y)=0$；因此对所有 $N$，包括 $\infty$，$\Lambda_N(d,\theta)=+\infty$。

证明。此时原 $V_j$ 在标量相位之外为实矩阵，故所有 $M_h$ 都为实对称。纯虚反对称的 Hermitian $H_Y$ 与它们迹配对为零。$H_Y\in\mathcal L$、$\|H_Y\|_1=2$；定理 45.2 实现的 $\rho_0\pm\lambda H_Y$ 是两个不同的正相容态，且由原域提升成为真实双世界。因此这是实际盲对，不只是一条形式方向。第二卷定理 40.1–40.2 还供应完整例外消去子的分类，这里只取其中一个便于估计深度的方向。∎

**定理 47.3（全部实角度的周期对应与二次距离指数）。** 对任意迹零 Hermitian $H$，

$$
\Delta_{\theta+\pi/2,N}(H)=\Delta_{\theta,N}(H)
\quad(N\in\mathbb N_0\cup\{\infty\}).
\tag{47.5}
$$

对 $0<a_\theta\le\pi/4$，

$$
\frac{16(1+\sqrt2)}{9s^2}
\le\Lambda_3(\theta)\le\frac{C_3}{s^2},
\tag{47.6}
$$

并有

$$
\frac{4(1+\sqrt2)}{9a_\theta^2}
\le\Lambda_3(\theta)
\le\frac{C_3\pi^2}{16a_\theta^2}.
\tag{47.7}
$$

这些是非最优常数的上下界，不是 $\Lambda_3$ 的精确值。

证明。$e^{\mathrm i(\pi/2)W}=\mathrm iW$ 给

$$
V_0(\theta+\pi/2)=\mathrm iV_1(\theta),\qquad
V_1(\theta+\pi/2)=\mathrm iV_0(\theta).
$$

每层全部历史仅作标签逐位互换，原始权重保持，故 (47.5) 成立。这是不同参数的代数对应，不是在物理合同中调角。结合定理 46.2、47.1 得 (47.6)。最近例外角距离满足 $|s|=\sin(2a_\theta)$，而区间上的弦界与切线界给 $4a_\theta/\pi\le|s|\le2a_\theta$，于是得到 (47.7)。∎

**定理 47.4（每个固定深度的二次距离下界）。** 对 $N\ge1$、$a_\theta>0$，

$$
\Lambda_N(\theta)\ge\frac1{2N^2a_\theta^2}.
\tag{47.8}
$$

因此每个固定 $N\ge3$ 的模量在例外附近都有精确的逆二次距离阶，其上下常数可以依赖 $N$。

证明。用周期标签对应把最近例外角归到零，记偏移为 $\alpha$，$|\alpha|=a_\theta$。对实 $H_T,E$，复共轭将 $\alpha$ 变为 $-\alpha$，故每个 $f_h(H_T;\alpha)$ 为实偶函数。第二卷的例外闭包只含 $E,E_a,E_b$，而 $H_T$ 消去这三个效果，故任意长度的 $f_h(H_T;0)=0$；偶性给一阶导数为零。

每个原 $V_j$ 的一、二阶算子导数范数均为一。长度 $n$ 的乘积由乘法求导给

$$
\|V_h'\|_{\rm op}\le n,\qquad
\|V_h''\|_{\rm op}\le n+n(n-1)=n^2.
$$

对 $\operatorname{Tr}(H_TV_h^\dagger EV_h)$ 求两次导数，三个项的范数界分别为 $n^2,2n^2,n^2$，故

$$
|f_h''|\le4n^2\|H_T\|_1,\qquad
|f_h(H_T;\alpha)|\le2n^2a_\theta^2\|H_T\|_1.
\tag{47.9}
$$

按全部原权重平均再对 $n\le N$ 取最大，得到 (47.8)，并由定理 45.2 实现其正态见证。对 $N\ge3$，$\Lambda_N\le\Lambda_3$，结合 (47.7) 得固定深度的相反方向上界。$N\le2$ 的精确结论始终为无限，有限下界不替代它。∎

## 48. 全历史极限的紧性与极值次序

**定理 48.1（实现方向球面上的紧性极限）。** 对每个实角度，

$$
\Lambda_\infty(\theta)=\inf_{N\ge0}\Lambda_N(\theta).
\tag{48.1}
$$

证明。在定理 45.2 已完全实现的方向空间取

$$
\mathbb S_{\mathcal L}=\{H\in\mathcal L:\|H\|_1=1\},\qquad
m_N=\min_{H\in\mathbb S_{\mathcal L}}\Delta_{\theta,N}(H).
\tag{48.2}
$$

它是非空紧集，各有限层函数连续，故最小值达到。定理 45.3 和齐次性给 $\Lambda_N=1/m_N$，约定 $1/0=+\infty$。$m_N$ 单调增加且由 $1/2$ 控制，设其极限为 $m$。

取每层最小点 $H_N$，沿一个趋于无穷的子序列有 $H_{N_j}\to H_*$。对每个固定 $k$，当 $N_j\ge k$ 时

$$
\Delta_{\theta,k}(H_{N_j})\le
\Delta_{\theta,N_j}(H_{N_j})=m_{N_j}.
$$

连续性给 $\Delta_{\theta,k}(H_*)\le m$；对 $k$ 取上确界得到 $\Delta_{\theta,\infty}(H_*)\le m$。反向，由 $\Delta_{\theta,N}\le\Delta_{\theta,\infty}$，

$$
m_N\le\inf_{\mathbb S_{\mathcal L}}\Delta_{\theta,\infty},
\qquad
m\le\inf_{\mathbb S_{\mathcal L}}\Delta_{\theta,\infty}.
$$

两方向合并给

$$
\min_{\mathbb S_{\mathcal L}}\Delta_{\theta,\infty}
=m=\sup_Nm_N.
\tag{48.3}
$$

取扩展实数倒数即为 (48.1)，包括 $m=0$。定理 44.4 也直接保证全历史函数连续；以上论证没有假定 $\sup_H$ 与 $\inf_N$ 可以任意交换。每个球面方向的态实现尺度可以不同，齐次性已在 (45.12) 中处理。∎

## 49. 对称平方上的全算子载体与精确投影间隙

**定义 49.1（数学二阶矩载体）。** 只为计算平方响应，取

$$
\mathscr K=\operatorname{Sym}^2(\mathbb C^3),\qquad
\dim_{\mathbb C}\mathscr K=6,
\tag{49.1}
$$

及如下正交基，按 $0,\ldots,5$ 编号：

$$
\mathscr B=
\left(\xi^2,\frac{\xi\otimes e+e\otimes\xi}{\sqrt2},
\frac{\xi\otimes f+f\otimes\xi}{\sqrt2},
e^2,\frac{e\otimes f+f\otimes e}{\sqrt2},f^2\right).
\tag{49.2}
$$

这里 $v^2=v\otimes v$。$\mathscr K$ 是证明中的数学空间，不提供第二份物理副本或双副本测量。去掉公共标量相位，令

$$
P_\theta=\operatorname{diag}(1,1,z),\qquad
V'_0=UP_\theta,\qquad V'_1=UP_\theta W,\qquad
R_j=\operatorname{Sym}^2(V'_j).
\tag{49.3}
$$

在完整的 $36$ 复维算子空间 $\operatorname{End}(\mathscr K)$ 上，内积为 $\langle X,Y\rangle=\operatorname{Tr}(X^\dagger Y)$，范数记为 $\|\cdot\|_2$。定义

$$
\mathscr T_\theta(X)=\frac12(R_0^\dagger XR_0+R_1^\dagger XR_1).
\tag{49.4}
$$

它是两个酉共轭的平均，故为 Hilbert–Schmidt 收缩。$U^2=I_3$，其对称平方为实对称酉矩阵

$$
S=\operatorname{Sym}^2U=
\begin{pmatrix}
1&0&0&0&0&0\\
0&-1/2&\sqrt3/2&0&0&0\\
0&\sqrt3/2&1/2&0&0&0\\
0&0&0&1/4&-\sqrt6/4&3/4\\
0&0&0&-\sqrt6/4&1/2&\sqrt6/4\\
0&0&0&3/4&\sqrt6/4&1/4
\end{pmatrix}.
\tag{49.5}
$$

各基向量中 $f$ 的个数为 $k=(0,0,1,0,1,2)$。令 $Q$ 为仅保留 $k_i=k_j$ 的矩阵条目的正交 pinching，$\mathscr C_S(X)=SXS$，$Q_U=\mathscr C_SQ\mathscr C_S$。计数 $3^2+2^2+1^2=14$ 给 $\operatorname{rank}Q=\operatorname{rank}Q_U=14$。

另以 $\Pi_0,\Pi_1,\Pi_2$ 表示在 $\mathscr K$ 上投到以下三个正交扇区的投影：

$$
\begin{array}{c|c|c}
\text{扇区}&\mathscr B\text{ 的指标}&\text{维数}\\ \hline
0&\{0\}&1\\
1&\{1,2\}&2\\
2&\{3,4,5\}&3
\end{array},
\qquad
\mathscr F=\operatorname{span}_{\mathbb C}\{\Pi_0,\Pi_1,\Pi_2\}.
\tag{49.6}
$$

这些扇区按 $\operatorname{span}(e,f)$ 的总个数分类，与 $Q$ 使用的 $f$ 个数分类不同。每个 $\Pi_j$ 同时与 $S$ 及 $\operatorname{Sym}^2P_\theta$ 交换。

**定理 49.2（秩十四压缩的精确证书及全三十六维间隙）。** 有

$$
\operatorname{ran}Q\cap\operatorname{ran}Q_U=\mathscr F,
\qquad
(I-Q)+(I-Q_U)\succeq\frac38 I
\quad\text{在 }\mathscr F^\perp\text{ 上}.
\tag{49.7}
$$

证明。矩阵单位 $E_{ij}$ 中令

$$
\mathcal I=\{(i,j):k_i=k_j\}.
$$

它是 $\operatorname{ran}Q$ 的十四元正交基。$A=Q\mathscr C_SQ|_{\operatorname{ran}Q}$ 是实对称矩阵，其全部条目由

$$
A_{(i,j),(r,t)}=S_{ir}S_{jt},
\qquad (i,j),(r,t)\in\mathcal I
\tag{49.8}
$$

确定。这一公式和 (49.5) 已给完整 $14\times14$ 矩阵；下述互不交叠的指标块进一步给出其可读分解。记

$$
D_2=\begin{pmatrix}1/4&3/4\\3/4&1/4\end{pmatrix},\quad
K_2=\begin{pmatrix}-1/8&-3\sqrt2/8\\-3\sqrt2/8&1/4\end{pmatrix},
\quad
D_3=\begin{pmatrix}1/16&3/8&9/16\\3/8&1/4&3/8\\9/16&3/8&1/16\end{pmatrix}.
\tag{49.9}
$$

在对应矩阵单位次序中，

$$
\begin{array}{c|c}
\text{指标块}&A\text{ 的块}\\ \hline
((0,0))&(1)\\
((0,1)),\ ((1,0))&(-1/2)\text{ 各一次}\\
((0,3)),\ ((3,0))&(1/4)\text{ 各一次}\\
((1,1),(2,2))&D_2\\
((1,3),(2,4))&K_2\\
((3,1),(4,2))&K_2\\
((3,3),(4,4),(5,5))&D_3
\end{array}.
\tag{49.10}
$$

所列指标共有十四个，正是 $\mathcal I$，且 (49.5) 使异块条目全为零。$D_2$ 在 $(1,1),(1,-1)$ 上的特征值为 $1,-1/2$。$K_2$ 的迹为 $1/8$、行列式为 $-5/16$，故特征值为 $-1/2,5/8$。$D_3$ 在 $(1,1,1),(1,0,-1),(1,-2,1)$ 上的特征值依次为 $1,-1/2,-1/8$。单条目块已显式给值。因此整个压缩的特征多项式为

$$
\det(\lambda I_{14}-A)=
\frac{(\lambda-1)^3(2\lambda+1)^6(4\lambda-1)^2
(8\lambda-5)^2(8\lambda+1)}{524288}.
\tag{49.11}
$$

这是小块的精确代数分解，覆盖全部十四维像空间，无须数值拟合。

在 $\operatorname{ran}Q$ 上，

$$
QQ_UQ=(Q\mathscr C_SQ)^2=A^2.
\tag{49.12}
$$

故两正交投影的主角余弦为 $A$ 的奇异值。其等于一的重数恰为三；在剩余十一维中，奇异值为 $1/2$ 六次、$1/4$ 两次、$5/8$ 两次、$1/8$ 一次。三个已知独立元素 $\Pi_0,\Pi_1,\Pi_2$ 同属于两像空间，故交恰为 $\mathscr F$，不存在漏掉的跨扇区固定方向。

为把这一压缩证书接到整个三十六维载体，使用两投影的主角分解：若一个主角余弦为 $\gamma<1$，在相应二维平面内，两单位像向量内积为 $\gamma$；$Q+Q_U$ 的特征值为 $1+\gamma,1-\gamma$，于是 $(I-Q)+(I-Q_U)$ 的特征值也是 $1-\gamma,1+\gamma$。交上的特征值为零，两像空间共同正交补上的特征值为二。这里维数为

$$
3+2\cdot11+11=36.
\tag{49.13}
$$

因此交外最小值是 $1-5/8=3/8$。这个主角计算是成熟的两投影定理在 (49.8) 的具体应用；它同时说明十四维证书为何控制全部三十六维算子，而不只控制被 pinching 保留的条目。∎

## 50. 全角度共同交换子及非正规算子的预解界

**定理 50.1（实际矩阵词给出的完整不动空间）。** 当 $s\ne0$ 时，

$$
\operatorname{Fix}(\mathscr T_\theta)
=\{X:R_0X=XR_0,\ R_1X=XR_1\}
=\mathscr F.
\tag{50.1}
$$

证明。对任意复算子 $X$，令 $a_j(X)=\|X-R_j^\dagger XR_j\|_2$。酉不变性给

$$
a_0(X)^2+a_1(X)^2
=4\operatorname{Re}\langle X,(I-\mathscr T_\theta)X\rangle.
\tag{50.2}
$$

若 $\mathscr T_\theta X=X$，则左边为零，故 $X$ 分别与两个 $R_j$ 交换；反向显然。这里是随机酉不动点定理的直接范数证明。

原矩阵有以下精确词恒等式：

$$
W=(V'_0)^{-1}V'_1,\qquad
U=(V'_0)^{-1}(V'_1)^2(V'_0)^{-2}V'_1,\qquad
P_\theta=UV'_0,\qquad UP_\theta U=V'_0U.
\tag{50.3}
$$

为核对第二式，注意 $P_\theta W=WP_\theta$，故

$$
V'_1(V'_0)^{-1}=UWU,\qquad
(V'_0)^{-1}(V'_1)^2(V'_0)^{-2}V'_1=WUWUW=U.
\tag{50.4}
$$

最后一个等式来自 $U^2=W^2=I$ 和 $(UW)^3=I$；后一关系可在 (44.2) 的下 $2\times2$ 实旋转块直接相乘得到。此推导不依赖 $\theta$。

因此共同交换子还与 $\operatorname{Sym}^2U$、$\operatorname{Sym}^2P_\theta$ 交换。后者的特征值是 $1,z,z^2$，重数分别为三、二、一。$s\ne0$ 恰保证这三个值互异，故交换条件要求 $QX=X$。同时与 $S$ 交换给 $Q_UX=X$，定理 49.2 迫使 $X\in\mathscr F$。反向，三个总下扇区投影与每个 $R_j$ 交换，故 $\mathscr F$ 全部为不动点。证明没有使用生成群稠密性或完整 Haar 分布。逆词仅用于代数推理，不成为原仪器可以执行的动作。∎

**定理 50.2（所有非例外角度的显式预解界）。** 当 $s\ne0$ 时，$\mathscr F$ 和 $\mathscr F^\perp$ 约化 $\mathscr T_\theta$，且

$$
\kappa_\theta:=
\left\|\left[(I-\mathscr T_\theta)|_{\mathscr F^\perp}\right]^{-1}
\right\|_{2\to2}
\le\frac{1600}{3s^2}.
\tag{50.5}
$$

证明。每个 $R_j$ 的共轭及其逆共轭都固定 $\mathscr F$，故共同保持其正交补；这也适用于平均及其伴随。不预设 $\mathscr T_\theta$ 正规或自伴。

对酉 $G$ 记 $d_G(X)=\|X-G^\dagger XG\|_2$。望远镜分解与酉不变性给

$$
d_{GH}(X)\le d_G(X)+d_H(X),\qquad d_{G^{-1}}(X)=d_G(X).
\tag{50.6}
$$

在对称平方中使用同一词恒等式。(50.3) 的 $U$ 词含三个 $V'_0$ 或其逆因子和三个 $V'_1$ 因子，故它的位移至多 $3a_0+3a_1$。$P_\theta=UV'_0$ 和 $UP_\theta U=V'_0U$ 各再添一个 $V'_0$，于是两者的位移都至多 $4a_0+3a_1$。

$\operatorname{Sym}^2P_\theta$ 共轭的非平凡相位差绝对值只可能为 $|1-z|$ 或 $|1-z^2|$，而

$$
|1-z|=2|\sin\theta|\ge |s|,\qquad
|1-z^2|=2|s|\ge |s|.
\tag{50.7}
$$

逐矩阵单位求 Hilbert–Schmidt 范数，得

$$
\|(I-Q)X\|_2\le\frac{4a_0+3a_1}{|s|},\qquad
\|(I-Q_U)X\|_2\le\frac{4a_0+3a_1}{|s|}.
\tag{50.8}
$$

第二式使用 $UP_\theta U$ 的相同相位差和其固定 pinching $Q_U$。对 $X\perp\mathscr F$，(49.7)、(50.8) 和实 Cauchy–Schwarz 给

$$
\begin{aligned}
\frac38\|X\|_2^2
&\le\|(I-Q)X\|_2^2+\|(I-Q_U)X\|_2^2\\
&\le\frac{2(4a_0+3a_1)^2}{s^2}
\le\frac{50(a_0^2+a_1^2)}{s^2}\\
&=\frac{200}{s^2}\operatorname{Re}
\langle X,(I-\mathscr T_\theta)X\rangle.
\end{aligned}
\tag{50.9}
$$

因此

$$
\operatorname{Re}\langle X,(I-\mathscr T_\theta)X\rangle
\ge\frac{3s^2}{1600}\|X\|_2^2,
\quad
\|(I-\mathscr T_\theta)X\|_2\ge\frac{3s^2}{1600}\|X\|_2.
\tag{50.10}
$$

有限维中这给 $\mathscr F^\perp$ 上的单射与满射，以及 (50.5)。整个界来自实部强制估计，不是把非正规算子的谱半径当成算子逆范数。∎

## 51. 原权重二阶矩、扇区投影与有限深度上界

**定理 51.1（完整记录二阶矩的有限维表示与 Cesàro 极限）。** 令

$$
A_0=|q\otimes q\rangle\langle q\otimes q|\in\operatorname{End}(\mathscr K),
\qquad
H^{(2)}=(H\otimes H)|_{\mathscr K},
\qquad
Q_n(H)=2^{-n}\sum_{|h|=n}f_h(H)^2.
\tag{51.1}
$$

对任意 Hermitian $H$，

$$
Q_n(H)=\operatorname{Tr}\bigl(H^{(2)}\mathscr T_\theta^n(A_0)\bigr).
\tag{51.2}
$$

若 $s\ne0$，记 $\mathsf P_{\mathscr F}$ 为算子 Hilbert 空间上到 $\mathscr F$ 的正交投影，则

$$
\mathsf P_{\mathscr F}A_0=\frac{\Pi_0}{4}+\frac{\Pi_1}{4}+\frac{\Pi_2}{12},
\tag{51.3}
$$

且

$$
\left\|\frac1{N+1}\sum_{n=0}^N\mathscr T_\theta^n(A_0)
-\mathsf P_{\mathscr F}A_0\right\|_2
\le\frac{2\kappa_\theta}{N+1}.
\tag{51.4}
$$

证明。$M_h=x_hx_h^\dagger$，故

$$
f_h(H)^2=
\operatorname{Tr}\bigl[(H\otimes H)
|x_h\otimes x_h\rangle\langle x_h\otimes x_h|\bigr].
$$

对称向量属于 $\mathscr K$。展开 $\mathscr T_\theta^n$ 时，每个时间词恰出现一次，系数恰为 $2^{-n}$，并且其共轭是 $R_{j_1}^\dagger\cdots R_{j_n}^\dagger A_0R_{j_n}\cdots R_{j_1}$，与 (44.3) 的时间方向一致。这证明 (51.2)，包括空词。未把分支平均换成无权轨道平均。

在 (49.2) 中，

$$
q\otimes q=\frac12\xi^2+
\frac1{\sqrt2}\frac{\xi\otimes e+e\otimes\xi}{\sqrt2}
+\frac12 e^2.
$$

三个总下扇区的平方权重依次为 $1/4,1/2,1/4$。将每个权重除以对应维数 $1,2,3$，得到 (51.3)；三个投影彼此正交，故这确为 Hilbert–Schmidt 投影。

令 $B_0=A_0-\mathsf P_{\mathscr F}A_0\in\mathscr F^\perp$。因 $\|A_0\|_2=1$，$\|B_0\|_2\le1$。在 $\mathscr F^\perp$ 上，由望远镜恒等式，

$$
\sum_{n=0}^N\mathscr T_\theta^nB_0
=(I-\mathscr T_\theta^{N+1})
\left[(I-\mathscr T_\theta)|_{\mathscr F^\perp}\right]^{-1}B_0.
\tag{51.5}
$$

收缩性给 $\|I-\mathscr T_\theta^{N+1}\|_{2\to2}\le2$，遂得 (51.4)。这里证明的是有限二阶矩的 Cesàro 收敛；不要求每次幂收敛，也不宣称完整历史分布混合到 Haar 或设计分布。∎

**定理 51.2（源仿射平面上的极限二阶矩下界）。** 对每个 $H\in\mathcal L$，将其按 $\xi\oplus\operatorname{span}(e,f)$ 写为

$$
H=\begin{pmatrix}0&w^\dagger\\w&B_2\end{pmatrix},
\qquad \operatorname{Tr}B_2=0.
\tag{51.6}
$$

则当 $s\ne0$，

$$
\begin{aligned}
m_2(H)
&:=\lim_{N\to\infty}\frac1{N+1}\sum_{n=0}^N Q_n(H)\\
&=\frac{\|w\|^2}{4}+\frac{\operatorname{Tr}(B_2^2)}{24}
\ge\frac{\|H\|_2^2}{24},
\end{aligned}
\tag{51.7}
$$

且每个有限 $N$ 满足

$$
\frac1{N+1}\sum_{n=0}^NQ_n(H)
\ge\left(\frac1{24}-\frac{2\kappa_\theta}{N+1}\right)\|H\|_2^2.
\tag{51.8}
$$

证明。$H\otimes H$ 保持对称子空间；其压缩 Hilbert–Schmidt 范数至多完整范数，

$$
\|H^{(2)}\|_2\le\|H\otimes H\|_2=\|H\|_2^2.
\tag{51.9}
$$

由 (51.2)、(51.4) 和迹配对 Cauchy–Schwarz，平均二阶矩与 $\operatorname{Tr}(H^{(2)}\mathsf P_{\mathscr F}A_0)$ 的差至多 $2\kappa_\theta\|H\|_2^2/(N+1)$，故极限存在。

在零扇区，压缩迹为 $H_{\xi\xi}^2=0$；在一扇区，两个对角配对之和为 $\|w\|^2$；在二扇区，交换算子恒等式给

$$
\operatorname{Tr}_{\operatorname{Sym}^2(\mathbb C^2)}(B_2\otimes B_2)
=\frac{(\operatorname{Tr}B_2)^2+\operatorname{Tr}(B_2^2)}2
=\frac{\operatorname{Tr}(B_2^2)}2.
\tag{51.10}
$$

这里可直接取对称投影 $(I+\mathrm{Swap})/2$ 并使用 $\operatorname{Tr}((A\otimes B)\mathrm{Swap})=\operatorname{Tr}(AB)$。乘 (51.3) 的系数即给 (51.7) 的等式。

又 $\|H\|_2^2=2\|w\|^2+\operatorname{Tr}(B_2^2)$，故

$$
m_2(H)-\frac{\|H\|_2^2}{24}=\frac{\|w\|^2}{6}\ge0.
\tag{51.11}
$$

具体到 (45.2)，$\|w\|^2=t^2/4+x^2+y^2+b^2$，$B_2$ 仍含任意复 $u+\mathrm iv$，所以没有丢掉虚相干方向。带上有限平均误差得到 (51.8)。∎

**定理 51.3（由有限矩得到实际加权记录界）。** 当 $s\ne0$ 且括号为正时，对任意 $H\in\mathcal L$，

$$
\Delta_{\theta,N}(H)\ge
\left[\frac1{32}-\frac{800}{(N+1)s^2}\right]\|H\|_1.
\tag{51.12}
$$

因而当 $(N+1)s^2>25600$，

$$
\Lambda_N(\theta)\le
\left[\frac1{32}-\frac{800}{(N+1)s^2}\right]^{-1}.
\tag{51.13}
$$

证明。$H=0$ 时显然。对非零迹零 Hermitian 三阶矩阵，正、负谱中至少一侧只有一个非零特征值。不妨谱为 $p,-q,-r$，其中 $p=q+r$、$q,r\ge0$；整体变号不影响范数。于是

$$
\|H\|_1=2p,\qquad
\|H\|_2^2=p^2+q^2+r^2\ge\frac32p^2,
\qquad
\|H\|_1^2\le\frac83\|H\|_2^2.
\tag{51.14}
$$

任意秩一投影 $M_h$ 满足 $|f_h(H)|\le\|H\|_{\rm op}=\|H\|_1/2$。故逐历史有

$$
f_h(H)^2\le\frac{\|H\|_1}{2}|f_h(H)|,
\qquad
\delta_{\theta,n}(H)\ge\frac{2Q_n(H)}{\|H\|_1}.
\tag{51.15}
$$

这些比较对同一实际历史及同一态对成立，因此允许按其共同的原权重相加。最大值不小于其数值平均，(51.8) 给

$$
\Delta_{\theta,N}(H)\ge
\frac{2}{\|H\|_1}
\left(\frac1{24}-\frac{2\kappa_\theta}{N+1}\right)\|H\|_2^2.
\tag{51.16}
$$

若该系数为正，才能按方向使用 (51.14) 的下界，得到

$$
\Delta_{\theta,N}(H)\ge
\left[\frac1{32}-\frac{3\kappa_\theta}{2(N+1)}\right]\|H\|_1.
\tag{51.17}
$$

代入 (50.5) 即为 (51.12)。假设其中最终括号为正同时保证上述中间系数为正。定理 45.3 给 (51.13)。此证明中取最大与取平均只是分别指定终点的精确表之间的比较，不供应一个与未知态对无关的固定有效终点。∎

## 52. 真实加权 Bloch 阻碍与逆二次深度阶

**定理 52.1（虚相干方向的完整分支递推下界）。** 对任意实 $\theta$ 及 $N\ge1$，非例外时有

$$
\Lambda_N(\theta)\ge
\max\left\{4,\frac{4}{\sqrt{3N}\,|s|}\right\}.
\tag{52.1}
$$

例外时仍取定理 47.2 的无限结论；$N\le2$ 始终取定理 47.1 的无限结论。

证明。取定理 47.2 的真正可实现方向 $H_Y$。在下二维空间 $\operatorname{span}(e,f)$ 中，写

$$
R=\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},
\qquad D=\operatorname{diag}(1,-1),
\qquad V'_j|_{\operatorname{span}(e,f)}
=R\operatorname{diag}(1,z)D^j.
\tag{52.2}
$$

对均匀权重的完整长度 $n$ 词，将其字母顺序反转不改变分布。因此 $x_h=(V'_h)^\dagger q$ 的下分量分布可由 $w_0=e$ 及以下递推计算：

$$
w\longmapsto D^j\operatorname{diag}(1,\overline z)Rw,
\qquad \mathbb P(j=0)=\mathbb P(j=1)=1/2.
\tag{52.3}
$$

完整 $x_h$ 的下分量为 $w_h/\sqrt2$；这里的随机权重正是每个实际历史的 $2^{-n}$，不是另设选择分支实验。

令归一化 $w_hw_h^\dagger$ 的 Bloch 向量为 $(X_h,Y_h,Z_h)$，取 Pauli 约定

$$
w_hw_h^\dagger=\frac12
\begin{pmatrix}1+Z_h&X_h-\mathrm iY_h\\X_h+\mathrm iY_h&1-Z_h\end{pmatrix}.
\tag{52.4}
$$

下效果为 $w_hw_h^\dagger/2$，$H_Y$ 的下块为负 Pauli $Y$，故

$$
f_h(H_Y)=-Y_h/2,\qquad
\delta_{\theta,n}(H_Y)=\frac12\mathbb E|Y_n|.
\tag{52.5}
$$

每步的 $D^j$ 同时翻转 $X,Y$ 的符号而保留 $Z$，使 $\mathbb E(X_nZ_n)=\mathbb E(Y_nZ_n)=0$；初值 $(0,0,1)$ 也满足此性质。记

$$
p_n=\mathbb E X_n^2,\quad q_n=\mathbb E Y_n^2,\quad
r_n=\mathbb E(X_nY_n),\quad z_n^{(2)}=\mathbb E Z_n^2,
\qquad A_n=\frac{p_n+3z_n^{(2)}}4.
\tag{52.6}
$$

它们来自同一实际分支律，且 $p_n+q_n+z_n^{(2)}=1$，所以 $0\le A_n,q_n\le1$。为逐项推出递推，在随机符号之前置

$$
X_R=X/2-\sqrt3 Z/2,\qquad
X'=cX_R+sY,\quad Y'=sX_R-cY,\quad
Z'=-\sqrt3 X/2-Z/2.
\tag{52.7}
$$

这是先共轭 $R$ 再共轭 $\operatorname{diag}(1,\overline z)$ 的直接 Bloch 公式。随机 $D^j$ 不改变 $Y'^2$ 或 $X'Y'$。利用两个已消去的交矩，

$$
\mathbb E X_R^2=A_n,\qquad
\mathbb E(X_RY)=r_n/2.
$$

平方及相乘 (52.7) 遂给精确的共同实现递推：

$$
\begin{aligned}
p_{n+1}&=c^2A_n+s^2q_n+sc\,r_n,\\
q_{n+1}&=s^2A_n+c^2q_n-sc\,r_n,\\
r_{n+1}&=sc(A_n-q_n)-\frac{c^2-s^2}{2}r_n,
\\
z_{n+1}^{(2)}&=\frac{3p_n+z_n^{(2)}}4,\qquad
(p_0,q_0,r_0,z_0^{(2)})=(0,0,0,1).
\end{aligned}
\tag{52.8}
$$

因为 $|A_n-q_n|\le1$、$|c^2-s^2|/2\le1/2$，归纳或几何级数给

$$
|r_n|\le2|sc|.
$$

因此

$$
q_{n+1}-q_n
=s^2(A_n-q_n)-sc\,r_n
\le s^2+2s^2c^2\le3s^2,
\qquad q_n\le\min\{1,3ns^2\}.
\tag{52.9}
$$

在同一均匀分支测度下使用 Cauchy–Schwarz，

$$
\delta_{\theta,n}(H_Y)
\le\frac12\sqrt{\min\{1,3ns^2\}},\qquad
\Delta_{\theta,N}(H_Y)
\le\frac12\min\{1,\sqrt{3N}|s|\}.
\tag{52.10}
$$

$\|H_Y\|_1=2$，故其比值至少为 (52.1)。定理 45.2 对所有 $d$ 将这同一方向实现为正态对，比例完全保留。因此这是实际完整记录上的必要深度障碍。∎

**定理 52.2（全历史有界模量及必要、充分深度阶）。** 若 $s\ne0$，则

$$
4\le\Lambda_\infty(\theta)=\inf_N\Lambda_N(\theta)\le32.
\tag{52.11}
$$

每个 $N\ge3$ 同时满足

$$
\max\left\{4,\frac4{\sqrt{3N}|s|},\frac1{2N^2a_\theta^2}\right\}
\le\Lambda_N(\theta)\le\frac{C_3}{s^2},
\tag{52.12}
$$

并在 (51.13) 的条件下具有该条更深的上界。特别地，

$$
N+1\ge\frac{51200}{s^2}\quad\Longrightarrow\quad
\Lambda_N(\theta)\le64.
\tag{52.13}
$$

对每个固定 $L>32$，一个一般充分条件为

$$
(N+1)s^2\ge\frac{25600L}{L-32}
\quad\Longrightarrow\quad\Lambda_N(\theta)\le L.
\tag{52.14}
$$

反向，对任意 $0<L<\infty$，

$$
\Lambda_N(\theta)\le L\quad\Longrightarrow\quad
N\ge3,\qquad N\ge\frac{16}{3L^2s^2}.
\tag{52.15}
$$

因此对固定的 $L>32$，使模量降到 $L$ 以下所需的最小深度，在例外角附近有逆平方阶。这里未给最优常数、最优阈值、精确 $\Lambda_\infty$ 或精确 $\Lambda_N$。

证明。由 (51.12) 对每个 $H$ 令 $N\to\infty$，有 $\Delta_{\theta,\infty}(H)\ge\|H\|_1/32$，故 $\Lambda_\infty\le32$；定理 52.1 的 $H_Y$ 同时在所有深度给 $\Delta_{\theta,\infty}(H_Y)\le1/2$，故 $\Lambda_\infty\ge4$。极限等式由定理 48.1，而非未经证明的极值交换。

式 (52.12) 来自定理 46.2、47.4、52.1 及 $\Lambda_N\le\Lambda_3$。代入 (51.12)，(52.13) 使括号至少 $1/64$；更一般地，解

$$
\frac1{32}-\frac{800}{(N+1)s^2}\ge\frac1L
$$

得到 (52.14)。必要条件由浅层无限性及 $4/(\sqrt{3N}|s|)\le L$ 平方得到。

若定义 $N_L(\theta)=\min\{N:\Lambda_N(\theta)\le L\}$，$L>32$ 时此集合非空，且例如

$$
\max\left\{3,\frac{16}{3L^2s^2}\right\}
\le N_L(\theta)
\le\left\lceil\frac{25600L}{(L-32)s^2}\right\rceil.
\tag{52.16}
$$

两侧常数均独立于 $d,\theta$，且 $|s|$ 与 $a_\theta$ 在例外附近等阶，遂得锐利的深度阶。对 $L\le32$，本条没有提供相应充分界；对 $s=0$，所有深度无限的结论优先。∎

## 53. 条件预测、取得资源、供应归属与未决关系

**定理 53.1（有限给定表误差的确定性预测界）。** 固定 $s\ne0$、$N\ge3$，假设对分别指定的各终点 $n=0,\ldots,N$，实际供应一组表 $\widehat p_n$，且有某个真实 $\rho\in\mathcal K_d$ 及一个相容候选 $\sigma\in\mathcal K_d$ 满足

$$
\operatorname{TV}(\widehat p_n,p_{\theta,n}(\rho))\le\varepsilon_n,
\qquad
\operatorname{TV}(\widehat p_n,p_{\theta,n}(\sigma))\le\eta_n.
\tag{53.1}
$$

令 $\epsilon=\max_{0\le n\le N}(\varepsilon_n+\eta_n)$。则

$$
\|S_\rho-S_\sigma\|_\diamond
=\|\rho-\sigma\|_1
\le\Lambda_N(\theta)\epsilon.
\tag{53.2}
$$

对任意实际给定的原输入密度、任意有限未触动参考以及任意给定的后继二元效果，其预测概率差至多 $\Lambda_N(\theta)\epsilon/2$。

证明。每个终点的总变差三角不等式及 (44.6) 给 $\delta_{\theta,n}(\rho-\sigma)\le\varepsilon_n+\eta_n$，故 $\Delta_{\theta,N}(\rho-\sigma)\le\epsilon$。由模量定义及定理 44.3 得 (53.2)。密度矩阵输入上的后继差是 Hermitian 迹零矩阵，任意效果的概率差至多其迹范数的一半；diamond 上界给所述参考范围内的统一估计。∎

**定义 53.2（表、终点及取得成本的条件域）。** 定理 53.1 的 $p_{\theta,n}(\rho)$ 是 (44.6) 的完整表。若实际只供应某个固定原输入的概率，而没有足以确定该表的响应合同，则 (53.1) 不是已获得的前提；数学见证 $ff^\dagger$ 不自动变成可制备输入。若两个候选各距同一给定表至多 $\varepsilon$，其 (53.2) 上界为 $2\Lambda_N\varepsilon$，效果预测差上界为 $\Lambda_N\varepsilon$。这些都是确定性条件界，不是有限样本估计器、置信区间或风险界。

每个深度 $n$ 的联合表有 $2^n$ 个带标签历史行，每行保留是、否两个终端条目，共 $2^{n+1}$ 个条目。证明中的固定维二阶矩压缩免去了数学上逐项列举的必要，却不移除实际取得这张精确表的制备、探测、存储、样本数或其他成本。没有假定独立同分布试样，也没有从一个系统的一次历程取得精确实概率。

式 (51.16) 中，最大值至少为平均值，所保证的是对每个固定 $H$，在所比较的有限终点中存在足够大的响应。该终点可以依赖 $H$。这个不等式本身没有供应一个对所有未知态对同时有效的单一固定终点，也没有供应将所有终点表免费同时取得的实验。有限预算的定义为 $\max_{n\le N}$；全历史的 $\sup_n$ 也是数学比较，不是一次无限长读出。

第二卷假设 39.2 的原时序、就绪环境和标签保留条件始终不变。历史在表中有一坐标，不表示可以选择它发生。正、反矩阵词用于证明相位间隙，不增加逆操作、反馈控制、后选择、新环境基、环境量子访问、相位标定或参考读出权限。

**定义 53.3（成熟中间结果及源特定参数对应）。** 本卷承重内容是 repo-derived 的固定源综合：原权重下的 $\delta,\Delta,\Lambda$ 关系、全六实方向的完整正态实现、浅层逆矩阵的二次尺度、对称平方固定空间与显式深度界。以下成熟工具只作为这些推导的中间输入，不另主张其为新理论，也不作全域原创性判断。

第二卷定理 39.3–39.4 供应实际联合效果和任意相容后继的响应差；定理 40.1–40.2 已给全部实角度的有限效果分类及完整例外消去子，定理 41.1 给精确 Gram 反演，定理 42.4 给严格相容点。第一卷定理 35.2、35.4–35.6 供应完整复 $\mathcal K_d$、原域 CPTP 提升、全参考迹范数桥和额外半正定条件。本卷不以一般有限闭包重证这些接口，也不把理想通道的稳定常数挪用于任意两个非理想后继。

[延续效果闭包](../../../D5/S3/Quantum/Measurement/ContinuationEffectClosure.lean) 的声明 continuationSpace_closure 及其[叙述](../../../Blueprint/D5/S3/Quantum/Measurement/ContinuationEffectClosure.md)定理 1.3，已由第二卷定理 39.4 以矩阵维数三、单 Kraus 分支 $V_j/\sqrt2$、初始效果族 $\{I_3,E\}$ 实例化。它供应最小不变效果空间；深度三的加权逆和本卷的二阶矩间隙是额外的源特定计算。

[信息完备性等价](../../../D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence.lean) 中既有私有声明 density_signature_injective_iff_analysis_injective 已使用“迹零 Hermitian 方向经正态小扰动实现”的一般桥。其载体在这里对应 $d_{\rm matrix}=3$，线性分析对应效果 $M_h$ 的中心化迹配对。一般密度态的正扰动不自动满足 $\mathcal K_d$ 的 $s_\rho$ 与 $B_d$ 条件；定理 45.2 在实际严格点上补足这两项，并调用既有原域提升。因此该一般桥是供应，不是缺失接口，也没有另立仅用于绑定它的声明。[顺序可见空间稳定性](../../../D5/S3/Quantum/Tomography/SequentialVisibleSpaceStability.lean) 和第二卷使用的观察空间消去子判据，同样只供应其已声明域内的定性关系。

以下文献中间输入均为 literature-attested，精确范围为：

- D. D’Alessandro，[*On Quantum State Observability and Measurement*, quant-ph/0307127v1](https://arxiv.org/html/quant-ph/0307127v1)，定理 1–2：可选 Lie 群酉轨道下，不可区分态由可观察空间的正交补描述，轨道张成给可观察性。本卷对应的状态是 $\rho,\sigma$，读出为 $E$ 的原生词共轭，线性分析为 $\operatorname{Tr}((\rho-\sigma)M_h)$。该文的可选控制族不提供这里的原生随机分支权限，也不供应本卷的 $2^{-n}$ 加权深度常数。
- A. J. Scott，[*Tight informationally complete quantum measurements*, quant-ph/0604049v1](https://arxiv.org/html/quant-ph/0604049v1)，式 (34)–(35)：算子框架上下界及框架算子逆。定理 4 的证明使用加权二设计的对称平方二阶矩恒等式，并导出相应重建关系。本卷在浅层对应有限线性分析矩阵 $\mathsf B$；在深层对应 $A_0$ 的原权重二阶矩和扇区投影。这里的投影为 $\Pi_0/4+\Pi_1/4+\Pi_2/12$，不是整个 $\mathscr K$ 上的均匀标量，因而没有以该文的二设计假设宣称原生轨道为完整设计。
- J. Novotný、G. Alber、I. Jex，[*Asymptotic Evolution of Random Unitary Operations*, 0908.4534v1](https://arxiv.org/html/0908.4534v1)，定理 IV.1、式 (22)：随机酉映射的单位模特征空间由各酉的共同相位交换关系刻画；在特征值一处就是共同交换子。本卷的参数为酉 $R_0^\dagger,R_1^\dagger$、权重各 $1/2$、算子载体 $\operatorname{End}(\operatorname{Sym}^2\mathbb C^3)$。定理 50.1 使用其中的不动点机制，具体交换子由 (49.8)–(50.4) 算出；预解和 Cesàro 速率由 (50.9)、(51.5) 另行证明。该文不使一般随机酉映射正规，也不授予完整分布混合或本源的数值间隙。

有限框架反演、正扰动、两正交投影的主角分解、随机酉不动点与均值遍历方法、Schur 补及迹范数不等式均为成熟数学。这里的新关系由其在原固定源、实际联合权重、完整复相容集上的组合和具体常数承担；不把一般方法或换记号当成新的承重定理。

**定义 53.4（保留的未决目标与原理边界）。** 本卷的已知角度结论仍以复 Hilbert 空间、CPTP 组合、Born 迹配对、原 Kraus 仪器及环境时序为前提。它说明这些前提内预测确定性如何随可观察关系和深度变化，不从较少前提出发推出复数结构、Born 规则或原生操作的物理起源。

原擦除标签菜单的全参数精确最小最大问题仍是第一卷定义 38.3 的 (38.6)：对每个 $0<d<1$ 找到达到的最优中心和匹配全部密度中心的下证书。这里保留标签的成对模量既没有更改该菜单，也没有给其精确中心；两问题的目标不相互替代。

本卷没有确定 $\Lambda_3$、$\Lambda_\infty$ 或中间 $\Lambda_N$ 的精确值，也没有优化 $C_3,32,64$ 或深度阈值。得到的是固定深度的锐利逆二次角距离指数，以及固定 $L>32$ 时锐利的逆二次深度阶。精确例外角始终有真实正态盲对；任意有限给定表误差只在定理 53.1 的确定性合同下产生预测界。有限样本风险、试样可用性、实验标定和量子基础原则的来源仍为独立未决关系。

## 追加锚（本行以下为增补区）

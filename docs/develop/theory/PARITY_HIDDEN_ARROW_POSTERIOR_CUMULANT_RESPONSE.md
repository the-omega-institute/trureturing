# 原完整计数后验的第三信息累积量响应

## 121. 原实验、完整计数与有限系数

**定义 121.1（固定模型）。** 取

$$
d_1=1,\quad d_{n+1}=10^{5d_n},\quad Q_n=10^{d_n},\quad
P_n=\sum_{h\le n}10^{d_n-d_h},\quad
\theta=\sum_{h\ge1}10^{-d_h}.
\tag{121.1}
$$

固定满足 $\log(1+r)/[-\log(1-r)]=\theta$ 的原振幅 $r\in(0,1)$，
并固定任意 $\beta\in(1/2,1)$。记

$$
a=(1+r)/2,\quad b=(1-r)/2,\quad
\phi=a\log(1+r)+b\log(1-r),\quad c_q=\phi(1-\beta)/\beta.
$$

每个层级保留以下整数和实数；省略下标 $n$ 时均指该层级：

$$
\lambda=Q^3,\quad M=2^{\lfloor\phi\lambda/(\beta\log2)\rfloor},\quad
\mathsf T=2M\lambda,\quad k_0=\lfloor a\lambda\rfloor,\quad
l_0=\lambda-k_0,
$$

$$
z_0=k_0\log(1+r)+l_0\log(1-r),\quad
q=\lfloor Me^{-z_0}\rfloor,\quad
\delta=Q^{-1/2},\quad B^2=q/Q^{5/2},\quad
\tau=\log(M/q),\quad w=\sqrt{\lambda/q}.
\tag{121.2}
$$

只需考虑 $1\le q<M$ 且 $\epsilon_c=rq/(M-q)<1$ 的充分大层级。
原补偿核在 $\mathcal X=\operatorname{Fin}M\sqcup\operatorname{Fin}M$ 上为

$$
\chi(\operatorname{inl}i)=1,\quad\chi(\operatorname{inr}i)=-1,\quad
b_S(\operatorname{inl}i)=r\mathbf1_S(i)-\epsilon_c\mathbf1_{S^c}(i),\quad
b_S(\operatorname{inr}i)=0,
$$

$$
\mathsf K_S(u,v)=\frac{1+b_S(u)\chi(v)}{2M},\qquad |S|=q.
\tag{121.3}
$$

实验 $\mathcal E=\mathrm{pair}$ 观察 $\mathsf T$ 个独立平稳相邻对，
各对质量为 $(2M)^{-1}\mathsf K_S(u,v)$；实验 $\mathcal E=\mathrm{path}$
观察从均匀初态出发的 $\mathsf T$ 步完整路径。
$\mathbb P_S^{\mathcal E}$ 始终表示这些实际数据律。
支持后验始终由全体大小为 $q$ 的支持上的均匀先验定义。
这些对象与[后验场定义 39.1](PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)、
[波动卷定义 27.1](PARITY_HIDDEN_ARROW_FLUCTUATIONS.md)及
[谱边界定义 68.1](PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)相同。

**定义 121.2（完整纤维）。** 给定实际完整数据 $x$，令 $k_i,l_i$ 为正类行的两种出发计数，
并取原分数和完整窗口

$$
W_i=k_i\log\frac{1+r}{1-\epsilon_c}
       +l_i\log\frac{1-r}{1+\epsilon_c},\qquad
J=\{i:\tau-w<W_i\le\tau+w\}.
\tag{121.4}
$$

以精确分数相等分组 $J=\bigsqcup_jJ_j$，$C_j=|J_j|$。
取唯一共同赔率乘子 $h_x$，使

$$
p_i=\frac{e^{W_i+h_x}}{1+e^{W_i+h_x}},\qquad \sum_i p_i=q.
\tag{121.5}
$$

组内 $p_i=p_j$。令 $\mathsf Q_x$ 为这些辅助独立 Bernoulli 的乘积律，
$\pi_i$ 为原完整固定 $q$ 后验的包含概率，$\mu_j=\sum_{i\in J_j}\pi_i$。
记 $e_k(u_A)=\sum_{I\subseteq A,\,|I|=k}\prod_{i\in I}u_i$，非法指标处取零。
原计数后验为

$$
P_x(m)=\frac{e_{q-\sum_jm_j}((e^{W_i})_{i\notin J})}
 {e_q((e^{W_i})_i)}
 \prod_j\binom{C_j}{m_j}e^{W_jm_j}.
\tag{121.6}
$$

其支持取全部使右侧为正的 $0\le m_j\le C_j$ 元组。
在任何后续幂和中，式 (121.6) 的整个质量连同全部二项多重度一起取幂。
独立 Bernoulli 在总数为 $q$ 下条件化恰给这个后验。特别地，置

$$
Q_x(m)=\prod_j\binom{C_j}{m_j}p_j^{m_j}(1-p_j)^{C_j-m_j},\quad
D(m)=\sum_j(m_j-C_jp_j),\quad\mathcal D(m)=D(m)/B,
$$

$$
\ell(m)=\log\frac{\mathsf Q_x(S_{J^c}=q-\sum_jm_j)}
 {\mathsf Q_x(S_{\mathrm{all}}=q)};
\qquad P_x(m)=e^{\ell(m)}Q_x(m).
\tag{121.7}
$$

在整个盒均可行的纤维上，$\ell$ 在整个盒有限。
这正是谱边界式 (68.3)–(68.5)、(70.6) 的完整计数对象。

定义

$$
v_j=\frac{C_jp_j(1-p_j)}{B^2},\quad
 e_j=\frac{\mu_j-C_jp_j}{B},\quad
V=\sum_jv_j,\quad
E(m)=\sum_j((m_j-\mu_j)/B)^2,\quad
T_x(m)=\frac{E(m)-V}{\sqrt\delta}.
\tag{121.8}
$$

空组补零。给定 $\sigma>0$，令

$$
\lambda_y(m)=\frac{(T_x(m)-y)^2}{2\sigma^2},\quad
P_x^y(m)=\frac{P_x(m)e^{-\lambda_y(m)}}
 {\sum_uP_x(u)e^{-\lambda_y(u)}},\quad
C3_x(y)=\mathbb E_{P_x^y}
 \left[-\log P_x^y-\mathbb E_{P_x^y}(-\log P_x^y)\right]^3.
\tag{121.9}
$$

**定义 121.3（完整有限鞍点）。** 对 $\alpha>0$，取

$$
K_\alpha(t)=-\frac12\sum_j\log(1-2tv_j/\alpha)
 +\sum_j\frac{te_j^2}{1-2tv_j/\alpha}
 +\frac{\delta\sigma^2t^2}{2\alpha},\qquad
K_\alpha'(t_\alpha)=V,\qquad W_\alpha=K_\alpha''(t_\alpha).
\tag{121.10}
$$

若 $v_*:=\max_jv_j>0$，实定义域为 $t<\alpha/(2v_*)$；全零时为 $\mathbb R$。
正噪声使 $K''>0$，且 $K'$ 在定义域两端分别趋于负、正无穷，故根唯一。
全部 $\alpha$ 导数固定实际纤维、所有整数、组集合、$p_j,\mu_j,V$ 和噪声。
系数中的求和始终包含全部原组。

## 122. 第三信息累积量的响应

**定理 122.1（原模型的紧输出第三累积量响应）。** 对定义 121.1 的每个固定 $\beta$，
每个确定正数序列 $\sigma_n$ 满足

$$
L_n:=\log(1/\sigma_n)\longrightarrow\infty,\qquad
\limsup_n L_n/Q_n^3<c_q/2,
\tag{122.1}
$$

以及每个 $R,\varepsilon>0$，均有

$$
\max_{\mathcal E\in\{\mathrm{pair},\mathrm{path}\}}
\sup_{|S|=q_n}\mathbb P_S^{\mathcal E}\left\{
\sup_{|y|\le R}\left|
C3_x(y)-C3_x(0)-\sqrt{\delta_n}\,t_1'''y
-\frac{\delta_n}{2}
 \left.\partial_\alpha^3\frac1{W_\alpha}\right|_{\alpha=1}y^2
\right|>\varepsilon\right\}\longrightarrow0.
\tag{122.2}
$$

证明分解于以下各节，最后在第 127 节汇合。

**定义 122.2（有限配分差）。** 置

$$
\Xi_\alpha(y)=
 \log\frac{\sum_mP_x(m)^\alpha e^{-\alpha\lambda_y(m)}}
 {\sum_mP_x(m)^\alpha e^{-\alpha\lambda_0(m)}}.
\tag{122.3}
$$

若 $f_\alpha$ 为 $P_x^\alpha/\sum P_x^\alpha$ 下的 $T_x$
加独立 $N(0,\sigma^2/\alpha)$ 的密度，则
$\Xi_\alpha(y)=\log[f_\alpha(y)/f_\alpha(0)]$。
每个有限纤维的精确恒等式为

$$
\log\sum_m(P_x^y(m))^\alpha-
\log\sum_m(P_x^0(m))^\alpha
=\Xi_\alpha(y)-\alpha\Xi_1(y),
$$

$$
C3_x(y)-C3_x(0)=-\left.\partial_\alpha^3\Xi_\alpha(y)\right|_{1}.
\tag{122.4}
$$

第一式由代入归一化质量得到；第三次对数配分导数是 $\log P_x^y$ 的第三中心矩，
而惊讶多一个负号，故得第二式。

## 123. 同一实际纤维的三次解析控制

**约定 123.1（原纤维界与范数）。** 以下均在谱边界第 68、69、70、117、119 节的共同实际好事件上工作。
固定其紧性常数后，原式 (117.7)–(117.10)、(119.8)–(119.10) 给

$$
m_Q:=\#\{j:C_j>0\}\le CQ^2=C\delta^{-4},\quad
\log q=c_qQ^3+O(1),\quad N_J:=\sum_jC_j\le CB^2,
$$

$$
c\le V\le C,\quad c\delta\le v_*\le C\delta,\quad
c\delta\le\sum_jv_j^2\le C\delta,\quad
|e_j|\le C\sqrt{v_j}\,e_M,\quad
\|e\|_2\le Ce_M,\quad e_M\le C(\delta^5+q^{-1/2}),
$$

$$
\max_j|p_j-1/2|\le Cq^{-1/2},\quad
cq\le d_c\le d_a\le q,\quad d_a-d_c=B^2V,
\quad d_c:=\sum_{i\notin J}p_i(1-p_i),\quad
 d_a:=\sum_i p_i(1-p_i),
$$

$$
|\ell(m)|\le C\delta^5(1+\mathcal D(m)^2),\quad
\ell(m)\le C\delta^5.
\tag{123.1}
$$

整个盒可行。原核心含 $c/\delta$ 个 $v_j\asymp\delta$ 的坐标。
原式 (117.15)–(117.16) 还给
$-C\|e\|^2\le s_\alpha:=2v_*t_\alpha/\alpha\le s_+<1$，$1\le\alpha\le2$。
原式 (117.24)、(117.26)、(117.33) 的每个固定阶矩均可使用；这些是同一输出条件下的矩，
并不由条件化前的负相关推断。

对函数 $F(\alpha,y)$ 记
$\|F\|_{3,R}=\sup_{1\le\alpha\le2,\,|y|\le R}\sum_{k=0}^3|\partial_\alpha^kF|$。
常数可依赖固定振幅、$\beta,R$ 及上述好事件常数。
$\operatorname{poly}(Q)$ 表示次数固定的多项式上界。
好事件可穷尽，使其补集概率对两个实验和所有确定大小 $q$ 的支持一致趋零。

**引理 123.2（直接的三次有限鞍点估计）。** 固定 $l<c_q/2$，使最终 $L\le lQ^3$。
选取 $\chi_0>0$，满足 $2\chi_0<c_q-l$，并置
$H=\{j:C_j\ge e^{\chi_0Q^3}\}$。
只在本证明中，以 $K_H$ 删除 $H^c$ 的坐标项而保留原噪声项，且仍在完整根 $t_\alpha$ 处置

$$
\epsilon_H=V-K_H'(t_\alpha),\quad W_H=K_H''(t_\alpha),\quad
D_j=1-s_\alpha v_j/v_*,\quad
w_j=v_j/(\alpha D_j),\quad m_j=-e_j/D_j.
\tag{123.2}
$$

有

$$
|s_\alpha^{(k)}|\le C,\quad
|w_j^{(k)}|\le Cw_j,\quad |m_j^{(k)}|\le C|e_j|,\quad
|W_\alpha^{(k)}|+|W_H^{(k)}|\le C\delta\quad(1\le k\le3),
$$

$$
W_\alpha\asymp W_H\asymp\delta,\quad
\sum_{k=0}^3\bigl(|\epsilon_H^{(k)}|
  +|(W_\alpha-W_H)^{(k)}|\bigr)
 \le\operatorname{poly}(Q)e^{-b_0Q^3}
\tag{123.3}
$$

其中 $b_0>0$。令 $X_j$ 独立且分布为 $N(-e_j,v_j/\alpha)$，$j\in H$，
$g_\alpha$ 为 $(\sum_HX_j^2-V)/\sqrt\delta+N(0,\sigma^2/\alpha)$ 的密度，则

$$
\left\|\log\frac{g_\alpha(y)}{g_\alpha(0)}
 +\sqrt\delta\,t_\alpha y+\frac{\delta y^2}{2W_\alpha}\right\|_{3,R}\longrightarrow0.
\tag{123.4}
$$

**证明。** 写 $r_j=v_j/v_*$。完整根方程为

$$
G(s,\alpha):=\alpha^{-1}\sum_j\frac{v_j}{1-sr_j}
 +\sum_j\frac{e_j^2}{(1-sr_j)^2}
 +\frac{\delta\sigma^2s}{2v_*}-V=0.
\tag{123.5}
$$

在原有根区间上 $G_s\ge c$，所有三阶及以下混合偏导有界。
逐次微分 $G(s_\alpha,\alpha)=0$，先得 $G_ss'+G_\alpha=0$，再得

$$
G_ss''+G_{ss}(s')^2+2G_{s\alpha}s'+G_{\alpha\alpha}=0,
$$

$$
G_ss'''+3(G_{ss}s'+G_{s\alpha})s''
 +G_{sss}(s')^3+3G_{ss\alpha}(s')^2
 +3G_{s\alpha\alpha}s'+G_{\alpha\alpha\alpha}=0.
\tag{123.6}
$$

因此 $s',s'',s'''$ 均有界。商法则给 $w,m$ 的三阶界。再由

$$
W_\alpha=2\sum_jw_j^2+4\sum_jw_jm_j^2+\delta\sigma^2/\alpha
\tag{123.7}
$$

得 $W$ 的界；$\sum w_jm_j^2\le C v_*\|e\|^2$。
原低组界为

$$
\sum_{H^c}v_j\le\operatorname{poly}(Q)e^{-(c_q-\chi_0)Q^3},\qquad
\sum_{H^c}e_j^2\le\operatorname{poly}(Q)e^{-(c_q-2\chi_0)Q^3}.
\tag{123.8}
$$

每个删除项的前三次全导数仍带 $v_j$ 或 $e_j^2$，且
$|t_\alpha^{(k)}|\le C/\delta$，$0\le k\le3$，这证明差量界。

完整鞍点倾斜下，高组均值、方差正是 $m_j,w_j$。
把高组能量与原能量噪声中心化并以 $\sqrt{W_H}$ 标准化，其精确特征函数为

$$
\psi_\alpha(\xi)=e^{-\beta_G^2\xi^2/2}
\prod_{j\in H}e^{-i\xi a_j}(1-2i\xi a_j)^{-1/2}
 \exp\left[-\frac{\beta_j^2\xi^2}{2(1-2i\xi a_j)}\right],
$$

$$
a_j=w_j/\sqrt{W_H},\quad
\beta_j=2m_j\sqrt{w_j}/\sqrt{W_H},\quad
\beta_G=\sqrt{\delta\sigma^2/\alpha}/\sqrt{W_H}.
\tag{123.9}
$$

其方差恰为一。前三次系数导数分别由 $Ca_j,C|\beta_j|,C|\beta_G|$ 控制，
$\max a_j\le C\sqrt\delta$，核心块有 $c/\delta$ 项满足 $a_j^2\asymp\delta$。
故

$$
|\psi_\alpha(\xi)|\le E_Q(\xi):=(1+c\delta\xi^2)^{-c'/\delta}.
\tag{123.10}
$$

对中心对数因子逐次求导，利用
$|\xi a_j|/|1-2i\xi a_j|\le1/2$，每个一至三阶导数均由 $C\xi^2a_j^2$ 控制。
非中心因子相应由 $C\xi^2\beta_j^2$ 控制，噪声由 $C\xi^2\beta_G^2$ 控制。
对指数再用三次乘法法则，得到

$$
|\partial_\alpha^k\psi_\alpha(\xi)|
 \le C_k(1+|\xi|^{2k})E_Q(\xi),\quad 0\le k\le3.
\tag{123.11}
$$

包络的所有固定多项式矩一致可积，尾部一致消失。
在 $|\xi|\le\delta^{-1/2}$ 用 Gaussian 上界；在外侧置
$u=\sqrt\delta|\xi|$，积分指数为 $-c'/\delta$ 的幂即可。
固定频率紧集上，直接展开式 (123.9) 及其前三次导数给

$$
\log\psi_\alpha(\xi)=-\xi^2/2+O(\sqrt\delta|\xi|^3),\quad
\partial_\alpha^k\log\psi_\alpha(\xi)
 =O(\sqrt\delta|\xi|^3),\quad1\le k\le3.
\tag{123.12}
$$

二次项的各阶导数为零来自恒等方差一；余项用 $\max a_j\le C\sqrt\delta$
和平方系数和有界逐项求导。这是对精确变换的估计。
若 $q_\alpha$ 为标准化密度，Fourier 反演给

$$
\partial_z^h q_\alpha\to\varphi^{(h)}\quad(0\le h\le3),\qquad
\partial_\alpha^k\partial_z^h q_\alpha\to0
 \quad(k\ge1,\ k+h\le3),
\tag{123.13}
$$

对 $\alpha\in[1,2],z\in\mathbb R$ 一致。
可微性由同一可积包络证明。
$z_y=(\sqrt\delta y+\epsilon_H)/\sqrt{W_H}$ 及前三次导数在紧输出上一致有界，
故 $q_\alpha(z_y)\ge c_R>0$，三次链式法则给

$$
\log\frac{q_\alpha(z_y)}{q_\alpha(z_0)}
 =-\frac{z_y^2-z_0^2}{2}+o_{C^3}(1).
\tag{123.14}
$$

精确撤销倾斜为

$$
g_\alpha(y)=\frac{\sqrt\delta}{\sqrt{W_H}}
 e^{K_H(t_\alpha)-t_\alpha(V+\sqrt\delta y)}q_\alpha(z_y).
\tag{123.15}
$$

比值中速率与前因子消去；式 (123.3) 支付 $\epsilon_H$ 和 $W_H-W_\alpha$ 的全部三次导数，
得到 (123.4)。∎

## 124. 完整固定总数选择的全盒二次近似

**引理 124.1（同一补集的二次选择势）。** 在约定 123.1 的纤维上置

$$
c_0=\frac12\log(d_a/d_c),\qquad
\eta=\frac{B^2}{2d_c},\qquad
\ell_2(m)=c_0-\eta\mathcal D(m)^2.
\tag{124.1}
$$

则 $0\le c_0\le C\delta^5$，$0<\eta\le C\delta^5$，并在整个可行盒上有

$$
|\ell(m)-\ell_2(m)|\le Cq^{-1/2}(1+|\mathcal D(m)|^3).
\tag{124.2}
$$

令 $q_j$ 为原二项组质量，$S_j=-\log(q_j/\max q_j)$，$S_Q=\sum_jS_j$，
$A_y=S_Q+\lambda_y$，并定义三个有限配分函数

$$
J_P(\alpha,y)=\sum_m e^{-\alpha(A_y(m)-\ell(m))},\quad
J_2(\alpha,y)=\sum_m e^{-\alpha(A_y(m)-\ell_2(m))},\quad
J_0(\alpha,y)=\sum_m e^{-\alpha A_y(m)}.
\tag{124.3}
$$

则对某个 $b_1>0$，

$$
\left\|\log\frac{J_P}{J_2}\right\|_{3,R}
 \le\operatorname{poly}(Q)e^{-b_1Q^3}.
\tag{124.4}
$$

**证明。** 对补集 Bernoulli 和写
$H(t)=\sum_{i\notin J}\log(1-p_i+p_ie^t)$，$m_c=H'(0)$。
全局校准给 $m_c=q-\sum_j C_jp_j$，故目标整数 $q-\sum_jm_j=m_c-D(m)$。
logistic 方差满足 $e^{-|t|}d_c\le H''(t)\le e^{|t|}d_c$。
因为 $|D|\le N_J\le Cq\delta^5$，唯一实倾斜根 $u$ 满足
$H'(u)=m_c-D$，且 $|u|\le C|D|/q\le C\delta^5$。
在该区间所有固定阶 $H^{(k)}$，$k\ge2$，均由 $C_kq$ 控制。
Taylor 展开及均值方程给

$$
u=-D/d_c+O(D^2/q^2),\quad
I:=u(m_c-D)-H(u)=D^2/(2d_c)+O(|D|^3/q^2),\quad
|\log(H''(u)/d_c)|\le C|D|/q.
\tag{124.5}
$$

这里 $H(0)=0$。这些界在完整盒上一致，允许其右侧在极端元组处很大。

所需经典中心局部估计对任意 Bernoulli 数组，只要求方差 $d\to\infty$ 和均值为整数：
中心质量为 $(2\pi d)^{-1/2}(1+O(d^{-1/2}))$，常数对数组一致。
为说明其在本处的范围，中心特征乘积满足
$|\Phi(t)|\le e^{-2d\sin^2(t/2)}$，$|t|\le\pi$。
在 $t=\xi/\sqrt d$、$|\xi|\le d^{1/12}$ 上，
$\log\Phi(t)=-\xi^2/2+O(|\xi|^3/\sqrt d)$；
三阶对数导数由 $Cd$ 控制，因为单项的相应界为 $Cp_i(1-p_i)$。
积分与 Gaussian 积分之差至多 $C/\sqrt d$；余下标准化频率由
$e^{-c\xi^2}$ 支付。反演再乘 $d^{-1/2}$ 就得上述相对估计。
相同证明适用于倾斜后的参数，其方差 $H''(u)\asymp q$。
这是 Bernoulli 局部展开的经典步骤，参见 Boistard–Lopuhaä–Ruiz-Gazen，
*Approximation of rejective sampling inclusion probabilities and application to high order correlations*，
[arXiv:1207.5654v1](https://arxiv.org/html/1207.5654v1)，式 (2.1)、(2.5) 及 §4.1。
该引用中的固定阶包含概率展开不作为输出条件下的相关界。

在补集的倾斜均值及全体的原整数均值处分别使用该估计，撤销补集倾斜，得到

$$
\ell=c_0-\frac{D^2}{2d_c}
 +O\left(q^{-1/2}+|D|/q+|D|^3/q^2\right).
\tag{124.6}
$$

代入 $D=B\mathcal D$、$B^2/q=\delta^5$ 即得 (124.2)。
$d_a-d_c=B^2V$ 给 $c_0,\eta$ 的界。
没有删去任何总偏差元组。

为证明三次配分比较，令 $\mu_{\alpha,y}(m)=e^{-\alpha A_y(m)}/J_0(\alpha,y)$。
原式 (117.33) 对每个固定 $k$ 给

$$
\mathbb E_\mu|\mathcal D|^{2k}\le C_k,\quad
\mathbb E_\mu S_Q^k\le C_k(1+m_Q)^k,\quad
\mathbb E_\mu\lambda_y^k\le C_k\delta^{-k}.
\tag{124.7}
$$

因此所有固定混合矩均为 $\operatorname{poly}(Q)$，由 Hölder 不等式可见。
$\ell,\ell_2\le C\delta^5$，且两者绝对值均由 $C\delta^5(1+\mathcal D^2)$ 控制。
若 $a,b\le C\delta^5$，对 $0\le k\le3$ 的函数
$e^{\alpha a}[-(A-a)]^k$ 用均值定理，有

$$
\left|e^{\alpha a}(A-a)^k-e^{\alpha b}(A-b)^k\right|
 \le C_k|a-b|(1+|A|^k+|a|^k+|b|^k).
\tag{124.8}
$$

区间内指数有统一上界。取 $a=\ell,b=\ell_2,A=A_y$，
利用 (124.2)、(124.7) 并逐项求导原有限和，得

$$
|\partial_\alpha^kJ_P-\partial_\alpha^kJ_2|/J_0
 \le q^{-1/2}\operatorname{poly}(Q),\qquad0\le k\le3.
\tag{124.9}
$$

又 $J_2/J_0=e^{\alpha c_0}\mathbb E_\mu e^{-\alpha\eta\mathcal D^2}
\ge1-C\eta\mathbb E_\mu\mathcal D^2\ge1/2$，
$|\partial_\alpha^kJ_2|/J_0\le\operatorname{poly}(Q)$。
使用对数的前三次导数公式并代入 (124.9)，得到 (124.4)。
这一估计在同一输出条件律内完成；它没有以未条件化概率尾界除以稀有输出概率。∎

## 125. 高组条件积分中的秩一选择

**引理 125.1（三次可微的条件秩一修正）。** 在引理 123.2 的高组 Gaussian 实现中置

$$
\mathcal D_G=\sum_{j\in H}(X_j+e_j),\qquad
\lambda_y^G=\frac{((\sum_HX_j^2-V)/\sqrt\delta-y)^2}{2\sigma^2},
\quad S_G=\frac12\sum_{j\in H}(X_j+e_j)^2/v_j.
$$

以 Lebesgue 测度定义

$$
\mathcal J_\eta(\alpha,y)=
 \int_{\mathbb R^H}e^{-\alpha(S_G+\lambda_y^G+\eta\mathcal D_G^2)}\,dX,
\qquad \mathcal J_0=\mathcal J_\eta\big|_{\eta=0}.
\tag{125.1}
$$

取固定于纤维的 $\eta$ 如 (124.1)，则

$$
\left\|\log\frac{\mathcal J_\eta}{\mathcal J_0}\right\|_{3,R}
 \le C\eta\le C\delta^5.
\tag{125.2}
$$

**证明。** 把原输出权重写成高能量加独立能量噪声
$N(0,\delta\sigma^2/\alpha)$ 等于 $h_y=V+\sqrt\delta y$。
在同一个完整 $t_\alpha$ 处倾斜不改变该条件分布。
在其标准化 Fourier 积分中置 $u=\xi/\sqrt{W_H}$。
频率 $u$ 下，高坐标的复协方差、均值为

$$
\widehat w_j=\frac{w_j}{1-2iu w_j},\qquad
\widehat m_j=\frac{m_j}{1-2iu w_j}.
\tag{125.3}
$$

总偏差 $\mathcal D_G$ 的复均值、协方差分别为

$$
M_\alpha(\xi)=\sum_{j\in H}(\widehat m_j+e_j),\qquad
S_\alpha(\xi)=\sum_{j\in H}\widehat w_j.
\tag{125.4}
$$

注意这里 $S_\alpha(\xi)$ 是标量协方差，不是潜在支持。
$\operatorname{Re}S_\alpha\ge0$。
对 $0\le k\le3$，式 (123.3) 给 $|u^{(k)}|\le C|u|$。
反复商法则及 $|u w_j|/|1-2iu w_j|\le1/2$ 给

$$
|\partial_\alpha^k S_\alpha(\xi)|\le C\sum_Hw_j\le C,\qquad
|\partial_\alpha^k M_\alpha(\xi)|\le C\sum_H|e_j|
 \le C\sqrt{m_Q}\|e\|_2\le C\delta^3.
\tag{125.5}
$$

$k=0$ 包括原来的 $e_j$。这些界对所有实频率一致。

复 Gaussian 积分给精确插入因子

$$
\mathcal R_\alpha(\xi)
 =(1+2\alpha\eta S_\alpha)^{-1/2}
 \exp\left[-\frac{\alpha\eta M_\alpha^2}
                   {1+2\alpha\eta S_\alpha}\right].
\tag{125.6}
$$

平方根取在 $\eta=0$ 连续等于一的分支。
这个经典 Gaussian 二次积分可由配方得到：在复均值 $M$、协方差 $S$ 的
Gaussian 积分中插入 $e^{-a z^2}$，完成平方后，行列式因子为
$(1+2aS)^{-1/2}$，剩余常数为 $e^{-aM^2/(1+2aS)}$。
此处原 Fourier 精度的实部正定，$a=\alpha\eta\ge0$，
且 $\operatorname{Re}(1+2aS_\alpha)\ge1$，所以该积分及连续分支均合法。
不需要把输出条件后的高坐标声明为独立。

由 (125.5)、分母的实部下界及逐次微分 (125.6)，有

$$
|\mathcal R_\alpha-1|+
 \sum_{k=1}^3|\partial_\alpha^k\mathcal R_\alpha|
 \le C\eta.
\tag{125.7}
$$

例如 $|\log\mathcal R_\alpha|\le C\eta(1+|M_\alpha|^2)$；
其前三次导数也满足相同界，指数乘法法则给 (125.7)。

令 $q_\alpha$ 如引理 123.2。公共撤倾斜因子抵消后，精确比值为

$$
\frac{\mathcal J_\eta}{\mathcal J_0}
 =1+\frac{(2\pi)^{-1}\int_{\mathbb R}
 e^{-i\xi z_y}\psi_\alpha(\xi)
 [\mathcal R_\alpha(\xi)-1],d\xi}{q_\alpha(z_y)}.
\tag{125.8}
$$

$z_y$ 的前三次导数有界，$q_\alpha(z_y)\ge c_R$，其前三次导数也有界。
对分子求导三次，(123.11)、(125.7) 将每项由
$C\eta(1+|\xi|^9)E_Q(\xi)$ 控制，其积分为 $O(\eta)$。
故比值与一之差及前三次导数均为 $O(\eta)$；再次取对数给 (125.2)。
这里直接控制的是同一条件积分的三次导数，维数 $m_Q$ 没有以未中心化三阶惊讶矩的形式出现。∎

## 126. 三次计数回接与稀有分母

**引理 126.1（原多重度的三次计数比较）。** 取
$Z_L(\alpha)=\sum_{m_{H^c}}e^{-\alpha S_{H^c}(m)}$。
对 $s\in\{0,\eta\}$，令

$$
J_s^{\rm count}(\alpha,y)
 =\sum_m e^{-\alpha(A_y(m)+s\mathcal D(m)^2)},\qquad
\mathcal C_s(\alpha,y)=B^{|H|}Z_L(\alpha)\mathcal J_s(\alpha,y).
\tag{126.1}
$$

则对某个 $b_2>0$，

$$
\left\|\log\frac{J_s^{\rm count}}{\mathcal C_s}\right\|_{3,R}
 \le\operatorname{poly}(Q)e^{-b_2Q^3}.
\tag{126.2}
$$

**证明。** 先固定高组中心盒
$|m_j-C_jp_j|/\sqrt{C_jp_j(1-p_j)}\le Q^2$。
在格点对应的 $B^{-1}$ 边长 Gaussian 格元内，原式 (117.27)–(117.29)、(119.41)–(119.43) 给

$$
|S_H-S_G|\le\epsilon_Q\le\operatorname{poly}(Q)e^{-\chi_0Q^3/2},
$$

$$
|T_x-T_G|\le\Delta_Q
 \le\operatorname{poly}(Q)(B^{-1}+B^{-2}e^{2\chi_0Q^3}),\qquad
\eta_Q:=\Delta_Q/\sigma\le\operatorname{poly}(Q)e^{-bQ^3},
\tag{126.3}
$$

其中 $b>0$，因为 $l<c_q/2$、$2\chi_0<c_q-l$。
低组接上任意原可行元组，且

$$
|\mathcal D-\mathcal D_G|\le d_Q
 :=m_Q/(2B)+m_Qe^{\chi_0Q^3}/B
 \le\operatorname{poly}(Q)e^{-b'Q^3}.
\tag{126.4}
$$

中心格元上 $|\mathcal D_G|\le C Q^2\sum_j\sqrt{v_j}+\sum_j|e_j|
\le\operatorname{poly}(Q)$，所以
$|s\mathcal D^2-s\mathcal D_G^2|\le\operatorname{poly}(Q)d_Q$。
这些是完整低组和完整高组舍入的逐元组界。

令 $U=(T_G-y)/\sigma$。由 (126.3)，

$$
|\lambda_y-U^2/2|\le\eta_Q|U|+\eta_Q^2/2,
$$

$$
|e^{-\alpha\lambda_y}-e^{-\alpha U^2/2}|
 \le C\eta_Q(1+|U|)e^{-\alpha U^2/2+C\eta_Q|U|}.
\tag{126.5}
$$

对每个固定 $k$，
$|a^k-b^k|\le k|a-b|(|a|+|b|)^{k-1}$。
因此前三次配分导数的插入势能
$[-(S_Q+\lambda_y+s\mathcal D^2)]^k$，$0\le k\le3$，
可逐格元与 $[-(S_G+S_L+U^2/2+s\mathcal D_G^2)]^k$ 比较。
积分误差由 (126.3)–(126.5) 乘固定混合矩支付。
低组始终保留原质量及其幂，不作连续近似。

说明这些矩与宽度成本。原式 (117.24)、(117.26) 给所有固定阶
$\mathcal D_G,S_G,S_L,U$ 的条件矩为 $\operatorname{poly}(Q)$；
带 $s=\eta$ 的矩分子不超过无修正的分子，分母比由 (125.2) 下界为 $1/2$。
Young 不等式将 $e^{C\eta_Q|U|}$ 吸收入相对变化 $O(\eta_Q)$ 的稍大噪声宽度。
在同一 $t_\alpha$ 处，$\sigma'^2-\sigma^2$ 对 $K_H,K'_H,W_H$ 的改变分别是

$$
\frac{\delta(\sigma'^2-\sigma^2)t_\alpha^2}{2\alpha},\quad
\frac{\delta(\sigma'^2-\sigma^2)t_\alpha}{\alpha},\quad
\frac{\delta(\sigma'^2-\sigma^2)}{\alpha}.
\tag{126.6}
$$

它们是多项式乘指数小量。标准化位置、正密度下界和全部固定阶插入矩的多项式界保持成立，
附近宽度的密度比有固定上下界。式 (125.3)–(125.8) 在这些附近宽度同样成立。
因此这一吸收仅付多项式成本；配分导数仍由原势能插入计算，不对宽度夹逼求导。

还须支付全部尾部。原幂律二项与 Gaussian 乘积律在高中心盒外的概率至多
$\operatorname{poly}(Q)e^{-cQ^4}$。二项部分可用
$S_j\ge c z_j^2-C$、单组配分下界 $c\sqrt{C_j+1}$ 作距离壳求和，
再对至多 $m_Q$ 个组求并；Gaussian 部分是相同标准化阈值下的正态尾。
二项计数盒上 $S_Q\le CN_J$，$|\mathcal D|\le CB$，
$\lambda_y\le\exp(CQ^3+2L)$。
故三次势能插入和其比较中任何固定次插入在尾部最多付
$\exp(C_kQ^3+2kL)$。Gaussian 的固定多项式尾插入由较高 Gaussian 矩及
Cauchy–Schwarz 支付，仍有 $e^{-c'Q^4}$，噪声因子至多另付 $\sigma^{-2k}$。
选择因子 $e^{-\alpha s\mathcal D^2}$、$e^{-\alpha s\mathcal D_G^2}$ 不超过一。

由 (123.15)，标准化密度在紧输出上至少 $c_R$；
$|K_H(t_\alpha)-t_\alpha V|\le C/\delta$。
因此乘积归一化后的原 Gaussian 输出核积分至少

$$
c_R\sigma e^{-C_R/\delta}.
\tag{126.7}
$$

带 $s=\eta$ 的核积分由 (125.2) 再保留固定比例。
高二项与 Gaussian 无输出归一化常数之比，由相同 Stirling 格元比较及无输出尾估计为 $1+o(1)$。
故除以实际比较分母所付对数成本只有
$O_k(Q^3+L+\delta^{-1})$，严格小于尾指数的 $Q^4$ 阶。
没有对总偏差使用 $Q^2$ 或其他截断。

综合格元和尾部，存在 $b_2>0$ 使

$$
\frac{|\partial_\alpha^kJ_s^{\rm count}
              -\partial_\alpha^k\mathcal C_s|}{\mathcal C_s}
 \le\operatorname{poly}(Q)e^{-b_2Q^3},\quad 0\le k\le3.
\tag{126.8}
$$

比较配分的各固定阶未中心化势能矩均为多项式，因而
$|\partial_\alpha^k\mathcal C_s|/\mathcal C_s\le\operatorname{poly}(Q)$。
对数的前三次导数公式将 (126.8) 化为 (126.2)。
格元体积给 $B^{|H|}$；模态常数已经在 $S_j$ 中精确减去。
上述比较既未舍弃原计数多重度，也未改变原输出条件。∎

## 127. 完整后验的三次桥与概率结论

**引理 127.1（完整计数的三次响应桥）。** 在约定 123.1 的共同纤维类上，

$$
\left\|\Xi_\alpha(y)+\sqrt\delta\,t_\alpha y
               +\frac{\delta y^2}{2W_\alpha}\right\|_{3,R}\longrightarrow0.
\tag{127.1}
$$

**证明。** 由 (124.3)，$J_2=e^{\alpha c_0}J_\eta^{\rm count}$，
$J_0=J_0^{\rm count}$。引理 124.1、125.1、126.1 给出

$$
\log J_P-\log J_0
 =\alpha c_0+\log(\mathcal J_\eta/\mathcal J_0)
       +O_{C^3}\bigl(\operatorname{poly}(Q)e^{-bQ^3}\bigr),
$$

$$
\|\log J_P-\log J_0-\alpha c_0\|_{3,R}\le C\delta^5+o(1).
\tag{127.2}
$$

原 $P_x(m)^\alpha$ 与 $e^{-\alpha(S_Q(m)-\ell(m))}$ 只差输出无关的模态质量常数。
因此 (122.3) 恰为 $\log J_P(\alpha,y)-\log J_P(\alpha,0)$。
式 (127.2) 中的 $\alpha c_0$ 在 $y$ 与零处消去。
再由 $s=0$ 的 (126.2)，
$B^{|H|},Z_L$ 和 Gaussian 归一化常数也在输出比值中精确消去。
剩下 $\log[g_\alpha(y)/g_\alpha(0)]$ 及三次范数趋零的误差。
引理 123.2 即给 (127.1)。∎

**证明 127.2（定理 122.1）。** 对 (127.1) 的实际三次余项在 $\alpha=1$ 求导，
并用精确有限恒等式 (122.4)，得到

$$
\sup_{|y|\le R}\left|
C3_x(y)-C3_x(0)-\sqrt\delta\,t_1'''y
-\frac\delta2(1/W_\alpha)'''\big|_1y^2\right|\longrightarrow0
\tag{127.3}
$$

在每个固定好事件常数类上一致成立。
有限函数光滑，区间端点的一侧三次导数等于普通导数。
此处没有从二次余项推出三次导数。

好事件、原完整窗口与原行估计对 pair、path 两种数据律及全部确定大小 $q$ 的支持一致。
固定好事件常数使其补集概率任意小，再令 $n\to\infty$ 并穷尽这些常数，得到 (122.2)。
也可直接用原核的支持置换等变性核对支持一致性：任意两个大小 $q$ 的支持由同一个正类置换联系，
原数据律、均匀支持先验、分组、精确中心和所有响应函数在该置换下共同运输。
连续输出函数在紧集上的上确界等于可数稠密集上的上确界，所以事件可测。

完整有限系数可由下列隐函数恒等式计算，所有偏导在 $(\alpha,t_\alpha)$ 取值：

$$
t'=-K_{t\alpha}/W,
$$

$$
t''=-\{K_{t\alpha\alpha}+2K_{tt\alpha}t'+K_{ttt}(t')^2\}/W,
$$

$$
t'''=-\{K_{t\alpha\alpha\alpha}
 +3K_{tt\alpha\alpha}t'+3K_{ttt\alpha}(t')^2+K_{tttt}(t')^3
 +3(K_{tt\alpha}+K_{ttt}t')t''\}/W,
$$

$$
(1/W)'''=-W'''/W^2+6W'W''/W^3-6(W')^3/W^4.
\tag{127.4}
$$

这些是 (121.10) 的有限求和导数，包含全部原组、噪声与精确中心；
尤其没有在可被放大的线性项中替换为连续轮廓极限。
所有证明只要求 (122.1) 的严格不等式。∎

**命题 127.3（结论的参数范围）。** 定理 122.1 对每个固定 $\beta\in(1/2,1)$ 和原固定振幅成立，
不要求 $\sigma_n$ 有任何额外多项式速率。它的陈述不包含 $\sigma_n=0$、
$\limsup L_n/Q_n^3=c_q/2$、变化的 $\beta$ 或振幅上的一致性、非紧输出集合或更高信息累积量。

**证明。** $l<c_q/2$ 和 $2\chi_0<c_q-l$ 正是格元误差除以噪声后仍指数小的条件；
其余噪声成本仅为固定多项式或对数阶 $O(L+Q^3)$。
$\sigma>0$ 用于有限层级的正密度和根的存在。
根区间、核心块及好事件常数依赖固定模型参数，输出正密度下界依赖 $R$。
这些证明给出 (122.1) 下每个确定序列的结论，不给所列其他范围的结论。∎

## 追加锚（本行以下为增补区）

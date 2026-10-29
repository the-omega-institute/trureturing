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

## 128. 同一完整后验的增长阶有限喷射

**定义 128.1（阶数、范数与完整系数族）。** 保持定义 121.1–121.3、式 (122.3)
及约定 123.1 的全部对象。固定原振幅、$\beta\in(1/2,1)$、$R<\infty$，
并固定满足 (122.1) 的任意确定正噪声序列。在每个原共同好纤维常数类上选取
$0<l<c_q/2$，使最终 $L\le lQ^3$，再固定

$$
0<\chi<\min\{(c_q/2-l)/16,c_q/32\},\qquad
H=\{j:C_j\ge e^{\chi Q^3}\},
$$

$$
\mu=\min\{\chi,c_q/2-l,c_q-2\chi-l,c_q/2-\chi,c_q-2\chi,1\}>0,
\qquad p=p(Q)=\left\lfloor\frac{\log Q}{64\log\log Q}\right\rfloor.
\tag{128.1}
$$

只考虑 $Q>e^e$。$H$ 仅用于比较积分；$K_\alpha,t_\alpha,W_\alpha$ 仍含全部原组。
对 $a\in[1,2]$ 及光滑函数 $f(\alpha,y)$，令

$$
[f]_{k,a}(y)=\frac{\partial_\alpha^k f(a,y)}{k!},\qquad
\mathfrak n_{p,a}(f)=\sum_{k=0}^p\rho^k\sup_{|y|\le R}|[f]_{k,a}(y)|,
\qquad N_p(f)=\sup_{1\le a\le2}\mathfrak n_{p,a}(f).
\tag{128.2}
$$

其中固定 $\rho>0$ 取小于引理 129.1 的系数半径。系数族为

$$
t_r=\left.\partial_\alpha^r t_\alpha\right|_1,\qquad
u_r=\left.\partial_\alpha^r(W_\alpha^{-1})\right|_1\quad(r\ge0).
\tag{128.3}
$$

它们是定义 121.3 的有限函数的实际导数，
包括所有整数、精确中心、低组与原噪声。式 (127.4) 是其前三阶的同一隐函数求导。
对 $r\ge2$，记 $\kappa_r(y)$ 为 $-\log P_x^y$ 在 $P_x^y$ 下的第 $r$ 累积量，
$\Delta\kappa_r(y)=\kappa_r(y)-\kappa_r(0)$。这里累积量不除以 $r!$ 或任何规模因子。

**定理 128.2（完整计数的同时有限喷射与绝对累积量误差）。** 在每个约定 123.1
的原好纤维常数类上，存在固定 $c,C,\rho>0$，使最终

$$
\begin{aligned}
F(\alpha,y)&=\Xi_\alpha(y)+\sqrt\delta\,t_\alpha y+
                       \frac{\delta y^2}{2W_\alpha},\\
N_p(F)&\le C Q^{-1/4}
 +\exp\{-c\sqrt Q+C(p+1)\log[Q(p+2)]\}\\
&\quad+\exp\{-\mu Q^3/64+CQ^2+C(p+1)\log[Q(p+2)]\}\\
&\quad+\exp\{-cQ^4+L+CQ^2+C(p+1)\log[Q(p+2)]\}.
\end{aligned}
\tag{128.4}
$$

常数不依赖导数指标，也没有未列出的逆噪声幂。起始层级可依赖固定参数、
$R$、原好纤维常数类、严格噪声余量及所选序列。特别地，最终

$$
\max_{2\le r\le p(Q)}\sup_{|y|\le R}
\left|\Delta\kappa_r(y)-(-1)^{r+1}
 \left[\sqrt\delta\,t_r y+\frac\delta2u_r y^2\right]\right|
\le Q^{-1/8}.
\tag{128.5}
$$

对每个 $\varepsilon>0$，原两个实验分别且共同满足

$$
\max_{\mathcal E\in\{\mathrm{pair},\mathrm{path}\}}\sup_{|S|=q_n}
\mathbb P_S^{\mathcal E}\left\{
\max_{2\le r\le p(Q_n)}\sup_{|y|\le R}
\left|\Delta\kappa_r(y)-(-1)^{r+1}
 \left[\sqrt{\delta_n}\,t_r y+\frac{\delta_n}2u_r y^2\right]\right|
>\varepsilon\right\}\longrightarrow0.
\tag{128.6}
$$

证明见第 129–131 节。式 (128.4) 的对数阶成本采用 $\log[Q(p+2)]$。

**约定 128.3（数学输入与引文范围）。** 式 (121.6)–(121.9)、全盒估计 (124.2)、
逐低元组估计 (126.3)–(126.4)、原核心、精确中心界及证明 127.2 的好事件穷尽均直接使用。
谱边界卷的 (117.27)–(117.29)、(119.41)–(119.43) 是同一格元与同一物理标量的估计。
有限 Bayes 识别、赔率校准、固定支持矩和原 path 行界分别使用
`FiniteSupportSelectionBayes.finite_support_bayes`、`UniformPosteriorOdds.result`、
`FiniteSupportPosteriorMoment.finite_support_posterior_moment`、
`ActualMarkedPathPgfPoissonEnvelope.actual_marked_path_pgf_poisson_envelope`
及其在谱边界第 68–70、117、119 节中的原对应。path 的一行、两行输入不被改作增长个数的标记行断言。
这些输入在此不重新推导。

特别地，对每个原组，精确使用 `BinomialFiniteSurprise.result` 的

$$
U=\frac{4e^{1/8}}{1-e^{-1/8}},\qquad D_*=e^{-768}/2,\qquad
Z_j(1/2)\le U\sqrt{C_j+1},\qquad
Z_j(a)\ge D_*\sqrt{C_j+1}\quad(1\le a\le2),
$$

$$
\mathbb E_{a,j}S_j^k\le (U/D_*)[2(k+1)]^k,
\qquad Z_j(b)\le Z_j(1/2)\quad(b\ge1/2).
\tag{128.7}
$$

其 $p_j\in[1/4,3/4]$ 条件由 (123.1) 满足，$C_j=0$ 时 $Z_j=1,S_j=0$。
全有限支撑和两个端点均保留。`BinomialLocalGaussian` 的局部 Stirling 与幂尾
作为既有二项输入使用；本处所需随 $Q$ 的显式格元误差直接取上述谱边界公式。

Fourier 反演、Cauchy 系数估计、复 Gaussian 配方、对数配分的凸性与有限 Taylor 代数
是经典中间步骤。Goodman，[*Asymptotic accuracy of the saddlepoint approximation for
maximum likelihood estimation*, arXiv:2005.11028v3](https://arxiv.org/html/2005.11028v3)，
条件 (2.9)–(2.10) 在固定 iid 求和制度下要求变换的 Fourier 衰减和有限范围的混合导数；
Theorem 6(b) 的加强范围为 $k\le2,1\le k+\ell\le7$ 及 $k=3,\ell\le4$。
其 §2.2、§2.5.5 排除求和规模与独立观测数同时趋于无穷的极限。
Boistard–Lopuhaä–Ruiz-Gazen，[*Approximation of rejective sampling inclusion probabilities
and application to high order correlations*, arXiv:1207.5654v1](https://arxiv.org/html/1207.5654v1)，
式 (2.1)–(2.5)、Lemma 1 与 Theorem 1 给总数条件化 Bernoulli 的中心质量及固定 $k$
包含概率展开；余项对所选 $k$ 个标签一致。其 §3 的若干推论另要求 $N/d$ 有界。
这些结论各按原条件作为方法和选择输入的来源，不承担 (128.4)–(128.6)。
新增推导是下面的同输出阶数一致桥与其在实际完整计数上的合成。

## 129. 实 Fourier 积分的阶数一致控制

**引理 129.1（完整根的共同系数半径）。** 存在固定 $h>0$、$A>1$，可取
$h<1/32$，使每个 $a\in[1-2h,2+2h]$ 的完整根在 $|z-a|<8h$ 内有解析延拓，
并在较小的共同圆盘上有

$$
\begin{gathered}
|[s]_{k,a}|\le A^{k+1},\quad
|[w_j]_{k,a}|\le A^{k+1}v_j,\quad
|[m_j]_{k,a}|\le A^{k+1}|e_j|,\\
|[W]_{k,a}|+|[W_H]_{k,a}|\le A^{k+1}\delta,
\qquad |[W^{-1}]_{k,a}|\le A^{k+1}\delta^{-1},\\
|[\epsilon_H]_{k,a}|+|[W-W_H]_{k,a}|
 \le A^{k+1}\operatorname{poly}(Q)e^{-(c_q-2\chi)Q^3}.
\end{gathered}
\tag{129.1}
$$

其中 $w_j,m_j,W_H,\epsilon_H$ 如 (123.2)，$k\ge0$，正方差坐标才使用相对界。
实轴上 $W,W_H\asymp\delta$。可固定 $0<\rho<h/16$，使上述所有解析系数的
$\rho$ 加权和也服从相应的零阶尺度界。

**证明。** 使用原完整有限方程 (123.5)。在原实根区间，$G_s\ge c>0$，
$|G_s|\le C$；其分母 $\alpha$ 与 $1-sv_j/v_*$ 均有固定正下界。
在固定大小的复邻域中，$|G_{ss}|+|G_{s\alpha}|+|G_\alpha|\le C$，
因为 $\sum v_j\le C,\sum e_j^2\le C e_M^2$，且 $\delta\sigma^2/v_*\le C$。
令 $d=G_s(s_a,a)$，考虑映射

$$
\mathcal T_z(s)=s-d^{-1}G(s,z).
\tag{129.2}
$$

先选固定 $r>0$ 使 $|\partial_s\mathcal T_z|\le1/2$ 在
$|s-s_a|\le r,|z-a|\le r'$ 成立，再选固定 $r'$ 使
$|\mathcal T_z(s_a)-s_a|\le r/2$。压缩迭代给该球内唯一解析根。
所有半径只使用上述共同上下界；在重叠圆盘上由唯一性相容。
同一构造先从 $a\in[1,2]$ 延伸过两端，缩小 $h$ 即覆盖所列实区间及其 $8h$ 邻域。
这里的实根仍由 $K''>0$ 唯一识别。

在进一步缩小的圆盘内，$|W(z)-W(a)|\le W(a)/2$，
$|W_H(z)-W_H(a)|\le W_H(a)/2$。这是先以公式 (123.7) 得到
$|W(z)-W(a)|+|W_H(z)-W_H(a)|\le C\delta|z-a|$ 后选半径所得，
其下界来自同一原核心。商、平方根取实轴正值的延拓。
Cauchy 估计给前两行 (129.1)。低组每个被删除项仍带 $v_j$ 或 $e_j^2$，
直接对 (123.8) 的有限解析和应用同一个圆盘估计给第三行。
在 $\rho$ 小于系数半径的固定比例时求几何级数，得到最后的加权和界。∎

**引理 129.2（同输出 Fourier 导数、密度喷射与秩一插入）。** 沿用 (123.9) 的
实特征函数与 $z_y=(\sqrt\delta y+\epsilon_H)/\sqrt{W_H}$，记

$$
I(\alpha,y,\xi)=e^{-i\xi z_y}\psi_\alpha(\xi),\qquad
E_Q(\xi)=(1+c\delta\xi^2)^{-c'/\delta}.
$$

对所有 $0\le k\le p(Q)$ 及实 $\alpha\in[1-2h,2+2h]$，有

$$
\frac{|\partial_\alpha^k I|}{k!}
 \le C^{k+1}(1+|\xi|)^{2k}E_Q(\xi),
\quad
\frac{|\partial_\alpha^k\{I(\mathcal R_\alpha-1)\}|}{k!}
 \le\eta C^{k+1}(1+|\xi|)^{2k}E_Q(\xi).
\tag{129.3}
$$

$\mathcal R$ 是同一条件积分的精确因子 (125.6)，$\eta$ 是 (124.1) 的原数。
设 $q_\alpha$ 为标准化倾斜密度，则

$$
N_p\left(q_\alpha(z_y)-\varphi(z_y)\right)
 \le C\sqrt\delta+\exp\{-c/\delta+C(p+1)\log[Q(p+2)]\},
\tag{129.4}
$$

$$
N_p\left(\log\frac{\mathcal J_\eta(\alpha,y)}{\mathcal J_0(\alpha,y)}\right)
 \le C\eta+\exp\{-c/\delta+C(p+1)\log[Q(p+2)]\}.
\tag{129.5}
$$

同一个输出条件律、同一个完整根下，还对 $1\le k\le p(Q)$ 有

$$
\mathbb E_{\alpha,y,s}\left[
 |\mathcal D_G|^{2k}+\left(\frac{S_G}{1+m_Q}\right)^k
                         +\delta^k|U_y|^{2k}\right]
 \le [C(k+1)]^{C(k+1)},\qquad s\in\{0,\eta\}.
\tag{129.6}
$$

常数不含逆噪声幂。这些估计也对相对宽度变化为
$\operatorname{poly}(Q)e^{-\mu Q^3/4}$ 的邻近正噪声成立。

**证明。** 引理 129.1 给各实点周围的解析系数界
$|[a_j]_k|\le C^{k+1}a_j$，
$|[\beta_j]_k|\le C^{k+1}|\beta_j|$，
$|[\beta_G]_k|\le C^{k+1}|\beta_G|$，及 $|[z_y]_k|\le C_R^{k+1}$。
当 $e_j=0$ 或 $\beta_G=0$，相应的全系列也为零。
在这些圆盘上，实频率分母保持

$$
|1-2i\xi a_j(z)|\ge c(1+|\xi|a_j(a)).
\tag{129.7}
$$

这是 $|a_j(z)-a_j(a)|\le C|z-a|a_j(a)$ 及反三角不等式的直接结果。
对单个中心对数 $-i\xi a_j-\tfrac12\log(1-2i\xi a_j)$，
围绕实点展开分母；一阶线性项的抵消使每个正阶系数至多
$C^{k+1}\xi^2a_j^2$。具体地，线性变差为
$i\xi\{(1-2i\xi a_j)^{-1}-1\}\Delta a_j$；
二次及以后项使用 $|\xi a_j|/|1-2i\xi a_j|\le1/2$。
非中心对数每个正阶系数相应至多 $C^{k+1}\xi^2\beta_j^2$；
噪声项至多 $C^{k+1}\xi^2\beta_G^2$。
因 $2\sum a_j^2+\sum\beta_j^2+\beta_G^2=1$，求和后为
$C^{k+1}\xi^2$。相位的正阶系数至多 $C_R^{k+1}|\xi|$。

为把对数系数转成指数系数，使用正系数主级数
$\exp\{A v/(1-v)\}$，其中 $A=C(\xi^2+|\xi|)$。
在 $|v|=[2(1+A)]^{-1}$ 上该函数至多 $e$，所以第 $k$ 系数至多
$e[2(1+A)]^k$。乘回实点的模 $|I|=|\psi|\le E_Q$，即得第一条 (129.3)。
这给出了显式阶数成本，未把 $C_k$ 当作共同常数。

对秩一因子，令 $u=\xi/\sqrt{W_H}$。
引理 129.1 与 (129.7) 使 (125.3)–(125.4) 的整个系数系列满足

$$
\sum_{k\ge0}\rho^k|[S_\alpha(\xi)]_{k,a}|\le C\sum_Hw_j\le C,
\qquad
\sum_{k\ge0}\rho^k|[M_\alpha(\xi)]_{k,a}|\le C\sum_H|e_j|\le C\delta^3.
\tag{129.8}
$$

这些界对全部实频率一致。因 $\eta\le C\delta^5$，
$|2z\eta S_z|\le1/2$ 在同一固定圆盘成立。
(125.6) 的平方根与指数的幂级数因此给

$$
\sum_{k\ge0}\rho^k|[\mathcal R-1]_{k,a}|\le C\eta.
\tag{129.9}
$$

与第一条 (129.3) 卷积并缩小一次共同半径，就得第二条。
这里的 $S_\alpha(\xi)$ 仍是复协方差，不是支持集合。

下面分开低频解析估计与实轴高频导数。固定足够小的 $b>0$，置
$T=b/\sqrt\delta$。在 $|\xi|\le T$ 和共同复圆盘内，
对精确变换 (123.9) 展开。方差恒等式在解析延拓中仍成立，故

$$
\log\psi_z(\xi)=-\xi^2/2+R_z(\xi),\qquad
|R_z(\xi)|\le C\sqrt\delta|\xi|^3,\qquad
|\psi_z(\xi)|\le e^{-c\xi^2}.
\tag{129.10}
$$

最后一界先选 $b$ 使 $C\sqrt\delta|\xi|\le1/4$。
非中心项的余项由
$\max a_j\sum\beta_j^2\le C\sqrt\delta$ 控制；噪声项没有三次余项。
同时 $|e^{-i\xi z_y(z)}|\le e^{C_R|\xi|}$。因此在该固定圆盘上

$$
\left|e^{-i\xi z_y(z)}(\psi_z(\xi)-e^{-\xi^2/2})\right|
 \le C_R\sqrt\delta |\xi|^3 e^{-c\xi^2+C_R|\xi|}.
\tag{129.11}
$$

Cauchy 系数估计在较大固定圆盘施于右侧可积主函数，再在 $\rho$ 求和，
给低频积分的 $C\sqrt\delta$ 范数界。Gaussian 的被删频率部分也按此法估计。
这个步骤只解析延拓截断的低频积分。

对实际高频积分只在实轴逐次求导，使用 (129.3)。对 $k\le p$，

$$
\int_{|\xi|>T}(1+|\xi|)^{2k}E_Q(\xi)\,d\xi
 \le \exp\{-c/\delta+C(k+1)\log[Q(k+2)]\}.
\tag{129.12}
$$

为核对范围，在 $T<|\xi|\le\delta^{-1/2}$ 上
$E_Q\le e^{-c_1\xi^2}$，其带幂尾积分至多
$e^{-c_2/\delta}C^{k+1}\delta^{-k-1}$，因为
$k\log(k+2)=o(1/\delta)$。
外侧置 $v=\sqrt\delta|\xi|\ge1$，把
$(1+cv^2)^{-c'/\delta}$ 的一半保留为 $e^{-c_3/\delta}$，另一半积分
$v^{2k}(1+cv^2)^{-c'/(2\delta)}$；$2k+2<c'/(4\delta)$ 最终成立。
该积分至多 $C^{k+1}$，另有尺度因子 $\delta^{-k-1}$。
这证明 (129.12)，也证明每一实际导数的反演与积分交换合法。
合并低频与高频即得 (129.4)。

为证明 (129.6)，在同一倾斜 Fourier 积分中插入多项式。
频率 $u$ 下坐标的复均值、协方差正是 (125.3)，其模不超过 $|m_j|,w_j$。
$\mathcal D_G$ 的复均值和协方差的模至多 $C\delta^3,C$。
复 Gaussian 的 $2k$ 次矩公式含至多 $(2k)!$ 个配对项，因而该插入的模至多
$[C(k+1)]^{2k}$ 倍 $|\psi|$。
对 $S_G^k$ 展开有序的 $k$ 个坐标指标；
$w_j/v_j\le C$、$e_j^2/v_j\le Ce_M^2$ 使其配对和至多
$[C(k+1)]^{2k}(1+m_Q)^k|\psi|$。
这些估计也覆盖非常小但为正的 $v_j$。

能量噪声在倾斜下的均值是 $t_\alpha\delta\sigma^2/\alpha$、方差是
$\delta\sigma^2/\alpha$；再作 Fourier 插入并除以 $\sqrt\delta\sigma$，
复均值的模至多 $C(\sigma/\sqrt\delta+|\xi|\sigma)$、复方差的模至多 $C$。
条件于总能量等于 $V+\sqrt\delta y$ 时，它的负值正是 $U_y$。
因此 $U_y^{2k}$ 的插入至多
$[C(k+1)]^{2k}\delta^{-k}(1+|\xi|)^{2k}|\psi|$。
没有使用 $\sigma^{-2k}$ 来界这个条件插入。
全频积分的相应矩至多 $[C(k+1)]^{C(k+1)}$：低频用 Gaussian 矩，
高频用 (129.12)。分母 $q_\alpha(z_y)\ge c_R$ 由 (129.4) 的零阶部分给出。
这证明 $s=0$ 的 (129.6)。

由精确公式 (125.8)，$\mathcal J_\eta/\mathcal J_0=1+O(\eta)$；
分子是同一个条件 Fourier 积分，并由 (129.9) 控制。
带选择的非负多项式分子不超过无选择的分子，而分母至少保留一半，
故 (129.6) 对 $s=\eta$ 也成立。

在截断 Taylor 代数中，(128.2) 的加权系数和次乘性成立。
$\varphi(z_y)$ 及其倒数在共同系数圆盘上有 $C_R$ 上界，
故它们的 $\rho$ 系数和也有此界。
(129.4) 使 $q_\alpha(z_y)/\varphi(z_y)-1$ 的 $p$ 喷射范数趋零；
对 $\log(1+v)$ 和 $(1+v)^{-1}$ 使用绝对收敛幂级数即可控制对数与倒数喷射。
同理，对 (125.8) 的分子使用 (129.9)、(129.11)–(129.12)，再乘这个倒数喷射，
得到 (129.5)。这个代数论证只需有限阶真实导数和实点正密度。

最后，若 $\sigma'^2/\sigma^2=1+\omega$ 且 $|\omega|$ 为所列指数小量，
在同一个 $t_\alpha$ 处，$K_H,K'_H,W_H$ 的精确变化由 (126.6) 给出。
其系数加权和至多 $\operatorname{poly}(Q)|\omega|$。
新的标准化输出位置仍在原固定紧集，新的密度仍有正下界，
反倾斜前因子的对数变化也是 $\operatorname{poly}(Q)|\omega|$。
所以邻近宽度的核积分之比有固定上下界，上述插入界不变。∎

**推论 129.3（完整有限根的 Gaussian 响应喷射）。** 对原 $g_\alpha$，有

$$
\begin{aligned}
N_p\left(\log\frac{g_\alpha(y)}{g_\alpha(0)}
       +\sqrt\delta t_\alpha y+\frac{\delta y^2}{2W_\alpha}\right)
&\le C\sqrt\delta+
 e^{-c/\delta+C(p+1)\log[Q(p+2)]}\\
&\quad+e^{-\mu Q^3/64+C(p+1)\log[Q(p+2)]}.
\end{aligned}
\tag{129.13}
$$

**证明。** 用原精确撤倾斜公式 (123.15)，其比值等于
$e^{-\sqrt\delta t_\alpha y}q_\alpha(z_y)/q_\alpha(z_0)$。
引理 129.2 的有限 Taylor 对数给

$$
\log\frac{q_\alpha(z_y)}{q_\alpha(z_0)}
=-\frac{z_y^2-z_0^2}{2}+r_\alpha(y),
\qquad N_p(r)\le C\sqrt\delta+e^{-c/\delta+C(p+1)\log[Q(p+2)]}.
$$

又
$z_y^2-z_0^2=\delta y^2/W_H+2\sqrt\delta y\epsilon_H/W_H$。
引理 129.1 支付 $W_H^{-1}-W^{-1}$ 和 $\epsilon_H/W_H$ 的全系数和。
这给 (129.13)，系数仍为完整 $t,W$。∎

## 130. 全复圆盘上的原计数比较与低于一的同输出 escort

**引理 130.1（全元组、双尾部的复配分比较）。** 取原 $S_Q,\mathcal D,\ell,c_0,\eta$，
并对 $\operatorname{Re}z>0$ 定义

$$
\begin{aligned}
G_y(z)&=J_P(z,y),\\
\mathcal C_s(z,y)&=B^{|H|}Z_L(z)\mathcal J_s(z,y),
 &s&\in\{0,\eta\},\\
\mathcal C_P(z,y)&=e^{zc_0}\mathcal C_\eta(z,y).
\end{aligned}
\tag{130.1}
$$

其中 $Z_L(z)=\sum_{m_{H^c}}e^{-zS_{H^c}(m)}$ 精确保留每个原低元组。
存在固定 $c,C>0$，使对每个 $a\in[1,2]$，在整个闭圆盘 $|z-a|\le h$ 上，

$$
\begin{aligned}
&\frac{|J_s^{\rm count}(z,y)-\mathcal C_s(z,y)|}{\mathcal C_s(a,y)}
 +\frac{|G_y(z)-\mathcal C_P(z,y)|}{\mathcal C_P(a,y)}\\
&\hspace{15mm}\le \mathcal E_Q:=
 \exp\{-\mu Q^3/64+CQ^2\}
 +\exp\{-cQ^4+L+CQ^2\},\qquad |y|\le R.
\end{aligned}
\tag{130.2}
$$

分母均在实点 $a$ 取值；并未在复点除以可能为零的配分函数。

**证明。** 先列出实比较分母及低组的共同界。对实 $b$ 在
$[1-2h,2+2h]$，(128.7) 给

$$
\frac{Z_L(b)}{Z_L(a)}\le e^{Cm_Q},\qquad a\in[1,2].
\tag{130.3}
$$

它只是每个低组的 $U/D_*$ 比值相乘。若需把 $b>2$ 作为实基点，
Jensen 在参数 $2$ 及 (128.7) 的 $k=1$ 给
$Z_j(b)/Z_j(2)=\mathbb E_{2,j}e^{-(b-2)S_j}\ge e^{-(b-2)K(1)}$。
$b<1$ 时用单调性 $Z_j(b)\ge Z_j(1)$。
因此所有实基点在所列扩展区间也有同样共同常数的单组上下界。
对固定自然数 $k$，从 $b-1/2\ge1/4$ 与
$x^ke^{-x/4}\le[4(k+1)]^k$ 得该扩展区间上的单组惊讶矩界；
独立低组乘积的第 $k$ 矩至多 $[C(k+1)]^{C(k+1)}(1+m_Q)^k$。
这是对 (128.7) 的直接使用，不把低组改为 Gaussian。

令 $n_H=|H|$，$Z_H^G(b)=\prod_{H}\sqrt{2\pi v_j/b}$。
把 Gaussian 积分除以这个无输出常数，(123.15)、(129.4)、(129.5) 给

$$
c_R\sigma e^{-C_R/\delta}\le
 \frac{\mathcal J_s(b,y)}{Z_H^G(b)}
 \le C_R\sigma e^{C_R/\delta},\qquad s\in\{0,\eta\}.
\tag{130.4}
$$

这里核积分与概率密度相差精确因子 $\sqrt{2\pi}\sigma/\sqrt b$，
而 $|K_H(t_b)-t_b(V+\sqrt\delta y)|\le C_R/\delta$，
$\sqrt\delta/\sqrt{W_H}\asymp1$。所以同输出核在两个实阶数之比满足

$$
\frac{\mathcal C_s(b,y)}{\mathcal C_s(a,y)}\le e^{CQ^2},
\qquad |b-a|\le2h,
\tag{130.5}
$$

因为 $Z_H^G(b)/Z_H^G(a)=(a/b)^{n_H/2}$，$m_Q\le CQ^2$。
(130.4) 中的 $\sigma$ 在此精确抵消。

现在取高组中心盒的全部格元。原 (126.3)–(126.4) 对每个接上的原低元组给

$$
\begin{gathered}
|S_H-S_G|\le\epsilon_Q\le\operatorname{poly}(Q)e^{-\chi Q^3/2},\\
|T_x-T_G|/\sigma\le\eta_Q
 \le\operatorname{poly}(Q)
 \{e^{-(c_q/2-l)Q^3}+e^{-(c_q-2\chi-l)Q^3}\},\\
|\mathcal D-\mathcal D_G|\le d_Q
 \le\operatorname{poly}(Q)e^{-(c_q/2-\chi)Q^3}.
\end{gathered}
\tag{130.6}
$$

中心盒内 $|\mathcal D_G|\le\operatorname{poly}(Q)$，故
$|s\mathcal D^2-s\mathcal D_G^2|\le\operatorname{poly}(Q)d_Q$。
这些都是逐元组界，未删去任何总偏差或低组情形。

写 $b=\operatorname{Re}z$、$U=(T_G-y)/\sigma$。
对任意两个实势能 $A,B$，基本积分恒等式

$$
e^{-zA}-e^{-zB}=-z(A-B)\int_0^1e^{-z[(1-v)B+vA]}\,dv
\tag{130.7}
$$

使 $|z|\le3$ 的整个圆盘受到同一实 $b$ 的支配。
(130.6) 和 $|\lambda_y-U^2/2|\le\eta_Q|U|+\eta_Q^2/2$ 给中心格元误差至多

$$
C(\epsilon_Q+\operatorname{poly}(Q)d_Q+\eta_Q)
 (1+|U|)e^{C\eta_Q|U|}
 e^{-b(S_G+S_L+U^2/2+s\mathcal D_G^2)}.
\tag{130.8}
$$

系数中的额外固定多项式一并吸收入 $\operatorname{poly}(Q)$。
用 $C\eta_Q|U|\le \eta_QU^2+C^2\eta_Q/4$ 把线性指数吸收进
相对变化 $O(\eta_Q)$ 的邻近宽度。引理 129.2 的同输出插入与邻近宽度结论
使 (130.8) 的总积分至多
$\operatorname{poly}(Q)(\epsilon_Q+d_Q+\eta_Q)\mathcal C_s(b,y)$。
格元体积恰为 $B^{-n_H}$；$e^{-zS_L}$ 未改变，
其复模求和恰为 $Z_L(b)$。除以 $\mathcal C_s(a,y)$ 时只用 (130.5)，
不再付 $\sigma^{-1}$。这证明整个复圆盘上的中心部分。

还要包括全部离散尾部与全部连续尾部。对 $b\ge1-2h$，
复核的模不超过一，秩一选择因子的模也不超过一。
原有限二项的 Gaussian 惊讶包络与半 escort 界 (128.7)，以及原正态尾，分别给

$$
\mathbb P_{b,H}^{\rm bin}\{\text{高组中心盒外}\}
 +\mathbb P_{b,H}^{G}\{\text{中心格元并集外}\}
 \le e^{-cQ^4+Cm_Q}.
\tag{130.9}
$$

具体地，对某个坏坐标先从 $e^{-bS_j}$ 留出固定正比例，
$S_j\ge cz_j^2-C$ 在 $|z_j|>Q^2$ 给 $e^{-cQ^4}$；
剩余配分由 $Z_j(1/2)$ 支付，分母由 $D_*\sqrt{C_j+1}$ 支付。
对至多 $CQ^2$ 个坐标求并。Gaussian 同样留出一半二次势能，
格元边界相差 $O(C_j^{-1/2})$，阈值最终至少 $Q^2/2$，所以仍有该尾指数。
所有有限端点都在离散尾部内。
无输出高二项常数与 $B^{n_H}Z_H^G(b)$ 的比由同一中心格元估计及这两个尾部趋于一；
此处无需输出分母。

于是两种完整尾部在除以 (130.4) 的实际比较分母后，至多

$$
\exp\{-cQ^4+L+CQ^2\}.
\tag{130.10}
$$

这里只用一次 $\sigma^{-1}=e^L$。没有在尾部对似然求导，也没有引入
$\sigma^{-2k}$。对全部复点同时成立的零阶 raw 估计将承担后面的所有导数。
由 (130.6)、$\log q=c_qQ^3+O(1)$ 和 (128.1)，中心部分可放宽为
$e^{-\mu Q^3/64+CQ^2}$。这证明 $J_s^{\rm count}$ 的 (130.2)。

为了回接完整选择，先记录固定电荷插入的比较。在上述同一中心格元插入
$1+|\mathcal D|^6$，逐元组误差用 (130.6)；Gaussian 条件矩用 (129.6) 的 $k=3$。
离散全盒有 $|\mathcal D|\le CB$，故插入的最大成本为 $e^{CQ^3}$；
它被 (130.9) 的 $Q^4$ 指数吸收。连续尾部用 Cauchy–Schwarz 与
无输出 $\mathcal D_G$ 的第十二矩，其上界为常数。
所以在实 $b\in[1-h,2+h]$ 的原计数同输出律中，

$$
\frac{\sum_m(1+|\mathcal D(m)|^6)e^{-bA_y(m)}}{J_0^{\rm count}(b,y)}\le C.
\tag{130.11}
$$

实基点区间的小扩展使用 (130.3) 后说明的单组上下界，中心与双尾部证明完全相同。
即便 $\sigma$ 最慢趋零，该插入的 Gaussian 证明也没有逆噪声成本。

最后使用原全盒二次选择估计 (124.2)。由于
$\ell,\ell_2\le C\delta^5$，对 $b=\operatorname{Re}z\ge1-h$，(130.7) 给

$$
|e^{z\ell(m)}-e^{z\ell_2(m)}|
 \le C|\ell(m)-\ell_2(m)|
 \le Cq^{-1/2}(1+|\mathcal D(m)|^3).
\tag{130.12}
$$

这个不等式在整个原盒成立；两种选择势在极端元组可有很大的负值，
仍不影响上界。乘 $e^{-bA_y}$ 并用 (130.11)，有

$$
|G_y(z)-e^{zc_0}J_\eta^{\rm count}(z,y)|
 \le Cq^{-1/2}J_0^{\rm count}(b,y).
\tag{130.13}
$$

$J_0^{\rm count}(b,y)/\mathcal C_P(a,y)\le e^{CQ^2}$ 由已证实 raw 比较、
(130.5) 及 (129.5) 的零阶部分给出。
合并 (130.13) 和 $s=\eta$ 的全圆盘比较，即得第二条 (130.2)。
原全部多重度、全低组幂及完整选择因此都在 raw 估计中。∎

**引理 130.2（低于一的实际同输出 escort 比）。** 对同一个 $G_y$，有

$$
\log\frac{G_y(a-h)}{G_y(a)}\le CQ^2,
\qquad a\in[1,2],\ |y|\le R.
\tag{130.14}
$$

特别地，$\log[G_y(1-h)/G_y(1)]\le CQ^2$。
相同结论对 $\mathcal C_P$ 及 $J_s^{\rm count},\mathcal C_s$ 成立。

**证明。** 先对 Gaussian 比较使用 (130.3)–(130.5)。低组精确成本为
$(U/D_*)^{|H^c|}$，高组体积归一化成本为 $(a/(a-h))^{n_H/2}$；
核积分比的成本为 $e^{C_R/\delta}$，其相同 $\sigma$ 抵消。
原秩一选择比由 (129.5) 的零阶界保持固定上下界，
$e^{(a-h)c_0}/e^{ac_0}$ 也有固定上下界。
故 $\mathcal C_P(a-h,y)/\mathcal C_P(a,y)\le e^{CQ^2}$。
引理 130.1 的实点版本使
$G_y(b)/\mathcal C_P(b,y)=1+o(1)$ 对 $b=a,a-h$ 同时成立。
这里 $a-h$ 的版本由其证明中已列出的扩展实区间取得。
raw 误差趋零来自 $L\le lQ^3$，故两比例最终在 $[1/2,2]$ 内。
相乘给 (130.14)。其它配分函数相同。
这不是以无输出半 escort 的比代替同输出比；核积分及选择项已逐项支付。∎

## 131. 从复 raw 误差到绝对信息累积量

**引理 131.1（实际配分的定量对数转移）。** 对 $p=p(Q)$，

$$
N_p\left(\log\frac{G_y(\alpha)}{\mathcal C_P(\alpha,y)}\right)
 \le \exp\{-\mu Q^3/64+CQ^2+C(p+1)\log[Q(p+2)]\}
 +\exp\{-cQ^4+L+CQ^2+C(p+1)\log[Q(p+2)]\}.
\tag{131.1}
$$

$s=0,\eta$ 的计数/比较配分之对数有同一界。

**证明。** 先说明由 (130.14) 产生的零点控制尺度。
选择 $b_0=C\delta^5$ 大于 $\sup_m\ell(m)$ 及 $c_0$，并令

$$
\widehat G_y(z)=e^{-zb_0}G_y(z),\qquad
\widehat C_y(z)=e^{-zb_0}\mathcal C_P(z,y).
\tag{131.2}
$$

第一函数是有限个 $e^{-zH_m}$ 的和，其中
$H_m=A_y+b_0-\ell(m)\ge0$；第二函数是相同类型的正测度积分，
势能为 $S_L+S_G+\lambda_y^G+\eta\mathcal D_G^2+b_0-c_0\ge0$。
其有限正实点积分与一阶矩均存在。
对两者中任一个 $Z$，置 $f(b)=\log Z(b)$。
对数配分的凸性与单调性，加上 (130.14)，给

$$
0\le -f'(b)\le \frac{2}{h}\{f(a-h)-f(a)\}\le CQ^2,
\qquad a-h/2\le b\le a.
\tag{131.3}
$$

具体地，凸性使
$-f'(b)\le\{f(a-h)-f(b)\}/(b-a+h)$，
分子不超过 $f(a-h)-f(a)$。乘 $e^{-zb_0}$ 的变化仅为 $O(h\delta^5)$。
因此对 $0\le r\le h/2$，
$Z(a-r)/Z(a)\le e^{CQ^2r}$。
若 $|z-a|\le r$，正势能的积分表示又给

$$
\frac{|Z(z)-Z(a)|}{Z(a)}
 \le\mathbb E_a(e^{rH}-1)
 =\frac{Z(a-r)}{Z(a)}-1
 \le e^{CQ^2r}-1.
\tag{131.4}
$$

取固定小 $d>0$ 及 $r_Q=dQ^{-2}$，右侧至多 $1/4$。
于是 $\widehat G_y,\widehat C_y$ 在 $|z-a|\le r_Q$ 上均非零，
并且 $|\mathcal C_P(z,y)|\ge\mathcal C_P(a,y)/2$。
这里只得到随 $Q$ 缩小的圆盘，不要求实际配分在固定复条带非零。

由整个固定圆盘上的 (130.2)，在这个小圆盘上有

$$
\left|\frac{G_y(z)}{\mathcal C_P(z,y)}-1\right|\le2\mathcal E_Q.
\tag{131.5}
$$

$\mathcal E_Q\to0$，所以从实轴正值延拓的对数满足
$|\log(G_y/\mathcal C_P)|\le4\mathcal E_Q$。
在半径 $r_Q$ 用 Cauchy 系数估计，得

$$
\mathfrak n_{p,a}\left(\log\frac{G_y}{\mathcal C_P}\right)
 \le4\mathcal E_Q\sum_{k=0}^p(\rho/r_Q)^k
 \le\mathcal E_Q\exp\{C(p+1)\log[Q(p+2)]\}.
\tag{131.6}
$$

所有实基点与输出共享常数，故得 (131.1)。
其它配分函数本身已有非负势能，重复同一论证即可。
全过程没有从实点零阶误差直接微分，也没有假定固定的实际零点排除区。∎

**证明 131.2（定理 128.2）。** 先在同一个实际纤维合成。
由引理 131.1，

$$
\log G_y(\alpha)=\alpha c_0+|H|\log B+\log Z_L(\alpha)
                         +\log\mathcal J_\eta(\alpha,y)+e_\alpha(y),
\tag{131.7}
$$

其中 $N_p(e)$ 由 (131.1) 控制。
式 (121.6) 中的模态常数与输出无关，所以
$\Xi_\alpha(y)=\log G_y(\alpha)-\log G_0(\alpha)$ 精确成立。
(131.7) 的前三项在此差中精确消去；引理 129.2 支付
$\log(\mathcal J_\eta/\mathcal J_0)$ 的完整 $p$ 喷射。
$\mathcal J_0$ 的 Gaussian 归一化同样在输出比中消去，剩下
$\log(g_\alpha(y)/g_\alpha(0))$。
推论 129.3 因此给 (128.4)，其中
$\sqrt\delta=Q^{-1/4}$、$\eta\le C\delta^5$、$1/\delta=\sqrt Q$。
每一步均在原完整质量或它的同输出比较上进行。

为了明确阶数去权重，任意有限正后验满足

$$
\kappa_r(y)=(-1)^r\left.\partial_\alpha^r
                  \log\sum_m(P_x^y(m))^\alpha\right|_1,
\quad
\Delta\kappa_r(y)=(-1)^r\partial_\alpha^r\Xi_\alpha(y)\big|_1,
\quad r\ge2.
\tag{131.8}
$$

第一式是惊讶的矩母函数
$\sum_mP_x^y(m)e^{s[-\log P_x^y(m)]}=\sum_m(P_x^y(m))^{1-s}$；
第二式用 (122.4) 第一行的精确有限恒等式，其仿射项在 $r\ge2$ 时消失。
代入 $F$ 的定义，故 (128.5) 左侧至多

$$
\max_{2\le r\le p}r!\rho^{-r}N_p(F)
 \le p!\max(1,\rho^{-p})N_p(F).
\tag{131.9}
$$

由 (128.1)，

$$
\log\{p!\max(1,\rho^{-p})\}
 \le p\log p+p\log\max(1,\rho^{-1})
 = (1/64+o(1))\log Q\le\tfrac1{32}\log Q.
\tag{131.10}
$$

所以第一误差项去权重后至多 $CQ^{-7/32}$。
其余三项去权重后的对数额外成本为
$O((p+1)\log[Q(p+2)]+\log Q)=o(\sqrt Q)$。
$-cQ^4+L+CQ^2$ 仍为负的 $Q^4$ 阶，因为 $L\le lQ^3$。
三项最终均小于 $Q^{-1/4}$ 的任意固定正倍数。
因此它们与 $CQ^{-7/32}$ 之和最终小于 $Q^{-1/8}$。
这给原始未归一化累积量的 (128.5)，并非只给 Taylor 系数误差。

最后使用证明 127.2 的原好事件穷尽。对任意 $\zeta>0$，先固定一个原常数类，
使其补集概率对 pair、path 及全部确定大小 $q$ 支持的上确界最终小于 $\zeta$。
在这个同一类上，(128.5) 对全部 $2\le r\le p(Q)$ 同时成立，
其阈值可依赖该类及原确定噪声序列。对每个固定 $\varepsilon>0$，
$Q^{-1/8}<\varepsilon$ 最终成立，故 (128.6) 的上极限至多 $\zeta$。
令 $\zeta\downarrow0$ 即得结论。
没有对导数阶数另选好事件；原支持置换等变性及紧输出上确界的可测性仍按证明 127.2 使用。
完整有限系数族 (128.3) 在首项抵消时也不作替换。∎

**命题 131.3（固定阶推论的逻辑界限与保留的参数范围）。** 仅有每个固定 $k$ 的
$C^k$ 余项趋零，不能推出增长阶的未归一化导数误差趋零。
定理 128.2 的增长阶结论保留定义 121.1 的每个固定振幅、每个固定
$\beta\in(1/2,1)$、全部确定大小 $q$ 支持、两个原实际实验、每个紧实输出区间，
以及满足 (122.1) 的每个确定正噪声序列。

**证明。** 对任意整数序列 $p\to\infty$，函数
$f_p(\alpha)=(\alpha-1)^p/p!$ 在 $[1,2]$ 上每个固定 $k$ 的
$C^k$ 范数趋零，而 $f_p^{(p)}(1)=1$。因此前三阶或任意预先固定的阶数
本身不蕴含 (128.5)；第 129–131 节的共同系数、实 Fourier 尾、全圆盘 raw 比较
及 (131.10) 提供所需的额外推导。
噪声只在 (130.6) 中按原严格余量除一次，尾部只在 (130.10) 付一次逆宽度；
其它阶数成本均不含逆噪声幂。所以不增加 (122.1) 以外的衰减速率条件。
这些公式的范围是所列 $p(Q)$、正噪声与严格边界；零噪声、边界等号、变化振幅或
$\beta$ 的一致性、更大的阶数窗口、非紧输出和概率收敛速率均不属于此命题。∎

## 追加锚（本行以下为增补区）

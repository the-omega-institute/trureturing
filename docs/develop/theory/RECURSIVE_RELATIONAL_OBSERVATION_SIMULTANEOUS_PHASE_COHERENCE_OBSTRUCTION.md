# 同一预测器的相位价格：有限随机保持的相容性障碍与起点例外

## 1. 同一来源、完整尾律与共同模型

固定 $m=2,d=1,\ell=2,n=4$。安装任意有限或可数深度概率先验 $\mu$，满足 $\mu(1),\mu(2)>0$。第一笔实际 Read 之前只抽取一次 $K$；全部提种拒绝与四段载荷使用这个共同 $K$。给定 $K=k$，实际 Read 新鲜条件独立，返回 $\alpha$ 的概率为

$$
r_k=\frac{F_{k+1}}{F_{k+3}},\qquad
r_1=\frac13,\quad r_2=\frac25,\quad
\frac38\le r_k\le\frac5{13}\quad(k\ge3).
\tag{1.1}
$$

来源与更新采用[原边界动力学][BD] §§97、100.1、105.1、114.1，以及[全标记树保持][E1] §2 的原合同。每笔 Read 付费；$\alpha\beta$ 提种0，$\beta\alpha$ 提种1，相等对拒绝并继续付费。在载荷 $p_i$，$\alpha$ 完成标记0，$\beta$ 转入 $q_{\beta,i}$；在 $q_{\beta,i}$，$\alpha$ 返回 $p_i$，$\beta$ 完成标记1。完成前三段后进入下一段，完成第四段后进入 $z_b$，执行唯一原 $\mathrm{Stop}_b$，进入 $z_{\rm done}$；两个终端切面均无 Read 权限。

$C_0(h)$ 包含原控制、种子、裸字段、选择器、全标记树上的 $B,Q^+,Z$、写入与锁存、第四段相位以及 completion、pendingStop、deliveredStop。第三标记的记录先写完再锁存，随后记录保持，原第四段与 Stop 继续。两种种子、所有标记三元组、所有有限正质量拒绝和返回历史均在域内，不先行条件于未来 $E_1$。没有来源重置、重新抽取深度、额外观测或控制端口。

记 $\mathcal H_3$ 为第三标记刚锁存、第四段尚无 Read 的全部正质量有限历史；$\mathcal H_p,\mathcal H_\beta$ 为第三标记后处于 $p_4,q_{\beta,4}$ 的全部正质量有限历史。因此 $\mathcal H_3\subset\mathcal H_p$；$\mathcal H_p$ 还包含任意有限第四段返回圈之后的切面。pending 与 delivered 保留原操作次序，不新增等待窗口。

当前原配置 $c$ 的完整残余转录保留以后全部实际 Read 字母及派生的控制、记录保持、第四标记、completion、原 Stop 与交付事件。从 $p_4$ 的完整有限尾词为

$$
w_{j,0}=(\beta\alpha)^j\alpha,\qquad
w_{j,1}=(\beta\alpha)^j\beta\beta\quad(j\ge0);
\tag{1.2}
$$

从悬置相位的尾词为 $\beta$ 或 $\alpha w_{j,b}$。已取得的悬置 $\beta$ 不再计入未来 Read。还保留两相位各自唯一的无限不完成路径。给定 $c$，原更新把字母唯一送到完整转录，反向可读回全部字母；记这个单射为 $I_c$。这一完整源桥由[随机停止尾律][ST] §2.1 供应。固定深度的原始尾律为

$$
\begin{aligned}
P_{p,r}(w_{j,0})&=r[r(1-r)]^j,&
P_{p,r}(w_{j,1})&=(1-r)^2[r(1-r)]^j,\\
P_{\beta,r}(\beta)&=1-r,&
P_{\beta,r}(\alpha w_{j,0})&=r^2[r(1-r)]^j,\\
&&P_{\beta,r}(\alpha w_{j,1})&=r(1-r)^2[r(1-r)]^j.
\end{aligned}
\tag{1.3}
$$

无限不完成质量为零。实际已取得计数 $A(h),B(h)$ 包含提种拒绝、载荷返回及部分解析。实际完整条件律为

$$
T_h^\mu=I_c\sum_k\nu_h(k)P_{s,r_k},\qquad
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
{\sum_j\mu(j)r_j^{A(h)}(1-r_j)^{B(h)}}.
\tag{1.4}
$$

这是同一个实际 $K$ 的条件律；计数与后验是分析坐标，不是预测器的免费输入。

竞争模型使用一个固定非空有限完整配置集 $M$、来源独立初始化分布 $\eta$、固定时间齐次来源独立行随机矩阵 $P_\alpha,P_\beta$，以及只读实际配置的完整残余律解码器 $D_z$。允许任意随机核，不要求正转移、遍历性、吸收结构或状态数上界。原控制、记录、权限、工作区、程序选择、输出游标与持久随机性全部计入完整配置。没有额外时钟、档案、建议、随机带、连续隐藏寄存器、相关来源种子、精确后验服务或可读配置分布向量。原 Stop 的确定性更新也属于配置更新。模型可以依赖固定安装的 $\mu$，不可以通过有限配置以外的通道依赖实际历史或真实 $K$。

条件于同一实际字 $h=h_1\cdots h_t$，配置分布和两种风险为

$$
\begin{aligned}
\rho_h&=\eta P_{h_1}\cdots P_{h_t},&
\overline D_h&=\sum_z\rho_h(z)D_z,\\
e_{\rm law}(h)&=\operatorname{TV}(\overline D_h,T_h^\mu),&
e_{\rm conf}(h)&=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu),\\
R_j(\mathcal H)&=\sup_{h\in\mathcal H}e_j(h),&&j\in\{\mathrm{law},\mathrm{conf}\}.
\end{aligned}
\tag{1.5}
$$

TV 是半 $\ell^1$ 距离。$\rho_h,\overline D_h$ 仅用于数学分析；运行时只读实际有限配置。先边缘化再取 TV、先取配置 TV 再平均、对实际历史另作来源平均，是三个不同次序。凸性给 $R_{\rm conf}\ge R_{\rm law}$，不使它们逐历史相等。

本卷同时保留两项生成义务：每配置的解码律须由自己的合成字母概率与实际保持所用的同一字母更新生成，支撑于原合法完整转录；另对每条实际正历史及合法正预测概率续接，条件化 $\overline D_h$ 并删去已生成原操作前缀，须得到 $\overline D_{hx}$。后一项称边缘化更新相容性。它不由前一项自动推出。预测合成不是实际来源观察，合成概率不改变真实 $r_K$。

消费[相位闭合半径][PH] 定理2.1 的单独相位最小值，记

$$
\rho_p=\frac{1116529}{22781250},\qquad
\rho_\beta=\frac{239}{6750}.
\tag{1.6}
$$

那里分别用模型 $A,B$ 达到两个相位的值，模型 $A$ 还达到联合查询域的标量最小值。以下讨论的是一个共同模型的风险向量；联合域的标量最大值最优不供应该向量的两个坐标同时最优。

## 2. 任意随机有限完整保持的严格联合障碍

**定理 2.1（共同相位风险的定量分离）。** 对每个上述固定有限或可数先验，对每个满足两项生成义务的任意随机有限完整配置模型，任取 $j_p,j_\beta\in\{\mathrm{law},\mathrm{conf}\}$，置

$$
\epsilon_p=R_{j_p}(\mathcal H_p)-\rho_p,\qquad
\epsilon_\beta=R_{j_\beta}(\mathcal H_\beta)-\rho_\beta.
$$

二者非负，且

$$
17\epsilon_p+7\epsilon_\beta>\sigma,
\qquad
\sigma=\frac{2625336439247}{29359472625000000}>0.
\tag{2.1}
$$

所以一个模型不能在完整的两个相位域同时达到式(1.6)。更强地，对任一上述风险组合，在全部有限状态数的共同模型类中，

$$
\inf_M\max\{R_{j_p}(\mathcal H_p)-\rho_p,
R_{j_\beta}(\mathcal H_\beta)-\rho_\beta\}
\ge\frac\sigma{24}
=\frac{2625336439247}{704627343000000000}
>\frac3{10^6}.
\tag{2.2}
$$

这是不依赖状态数和安装先验的下界，不是尖锐联合前沿或达到性声明。证明事实上只需合法完整尾律与边缘化更新相容性；每配置同更新生成确保其合法性，额外限制不会削弱下界。

**证明。** 先证明两个风险都取 law 的情形。其单独下界由 [ST, §3.3] 或 [PH, 定理2.1] 供应，故超额非负。若任一超额大于 $1/1000$，式(2.1)直接成立，因为 $\sigma<1/1000$。以下设 $0\le\epsilon_p,\epsilon_\beta\le1/1000$。

### 2.1 一个共同预测极限及其全部有限续接

固定这台任意有限机器。[ST, §3.1、§3.3] 的有限正历史见证给出两列历史 $h_m^-,h_m^+$，都在第三书签、实际种子1、前三标记100、前三载荷无返回圈，当前原 $c$ 相同；两列完整配置分布的 TV 趋零，而真实后验分别在深度1、2上的质量趋1。其前奏仅使用原付费相等拒绝对和共同接受后缀，不更改任何源动作。

有限 $M$ 的概率单纯形紧，取子列使两配置分布共同趋于 $\lambda$。对任意固定有限合法第四段前缀 $v$，两后继配置分布共同趋于 $\lambda P_v$。同一有限词在端点深度的似然严格正，其余深度的词似然至多1，故原后验的端点集中在续接 $v$ 后仍成立：若此前端点质量为 $1-\zeta$，此后非端点质量至多 $\zeta/[(1-\zeta)L_k(v)]$。可数非端点总质量一并趋零，没有交换未受控的逐深度极限。

配置解码是概率核，故其 TV 收缩使预测律也在 TV 中收敛。令 $Q_n$ 为 $\lambda P_{(\beta\alpha)^n}$ 所报 $p$ 原始完整尾律，令 $V_n$ 为再接 $\beta$ 后的悬置原始完整尾律。$I_c$ 的单射源桥把完整转录 TV 与这些原始词 TV 逐项对应。两列真实律的端点极限和风险上界给出，对所有 $n\ge0$、$k=1,2$，

$$
\operatorname{TV}(Q_n,P_{p,r_k})\le\rho_p+\epsilon_p,
\qquad
\operatorname{TV}(V_n,P_{\beta,r_k})\le\rho_\beta+\epsilon_\beta.
\tag{2.3}
$$

这个共同 $\lambda$ 是证明坐标，不是机器取得的后验、运行时状态分布服务或新实际历史。

### 2.2 近中心的逐词约束

消费 [ST, §2.2] 的端点符号事件

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha\beta\beta\}.
$$

两事件的端点平均质量为

$$
c_p=\frac{11758471}{22781250},\qquad
c=\frac{5261}{6750},\qquad d=1-c.
\tag{2.4}
$$

因端点事件质量之差恰为相应 $2\rho_s$，式(2.3)及 TV 的事件界给

$$
|Q_n(E_p)-c_p|\le\epsilon_p,
\qquad |V_n(E_\beta)-c|\le\epsilon_\beta.
\tag{2.5}
$$

再对两个端点律 $P_1,P_2$ 和任意律 $Q$ 逐坐标使用

$$
\frac{|q-p_1|+|q-p_2|-|p_1-p_2|}{2}
=\operatorname{dist}(q,[\min(p_1,p_2),\max(p_1,p_2)]).
$$

非负求和表明，若两个距离均至多 $\rho_s+\epsilon_s$，全部越出端点坐标区间的距离总和至多 $2\epsilon_s$。特别地，令

$$
b_n=Q_n(\beta\beta),\qquad
I=[l,h]=[9/25,4/9],
$$

则 $\operatorname{dist}(b_n,I)\le2\epsilon_p$。同一论证给 $Q_n(\alpha)$、$V_n(\beta)$ 各自端点区间外距离至多 $2\epsilon_p,2\epsilon_\beta$，所以两相位的两个下一字母概率都严格正。

原边缘化相容性在每条有限实际见证及其有限续接上成立。预测律在 TV 中收敛，下一字母概率的极限严格正，故条件化等式可取极限。于是 $Q_n$ 条件于首字母 $\beta$ 的残余是 $V_n$，$V_n$ 条件于首字母 $\alpha$ 的残余是 $Q_{n+1}$。其余确定性记录、控制、完成与 Stop 事件沿原更新同样删去。这里没有把“每个配置的生成”误作这项边缘化条件等式。

### 2.3 相容性把两个事件平衡接成递推

令 $\gamma_n=Q_n(\text{首字母为 }\beta)$、$v_n=V_n(\text{首字母为 }\alpha)$、$t_n=\gamma_nv_n$。相容性给

$$
b_n=\gamma_n(1-v_n),\qquad
Q_n(w_{j,1})=t_nQ_{n+1}(w_{j-1,1})\quad(j\ge1).
\tag{2.6}
$$

置 $d_n=1-V_n(E_\beta)$，由悬置事件的两个分支得

$$
d_n=v_n(1-b_{n+1}),\qquad |d_n-d|\le\epsilon_\beta,
\qquad
t_n=\frac{d_nb_n}{1-d_n-b_{n+1}}.
\tag{2.7}
$$

分母严格正；由 $b_n\in I+[-2/1000,2/1000]$、$d_n\in[d-1/1000,d+1/1000]$，还统一大于 $13/40$。令 $\eta_n=Q_n(E_p)-c_p$。式(2.5)–(2.7)给出精确递推

$$
b_n=\frac{c_p+\eta_n}
{1+g_{d_n}(b_{n+1})[1+g_{d_{n+1}}(b_{n+2})]},\qquad
g_e(x)=\frac{ex}{1-e-x},\qquad |\eta_n|\le\epsilon_p.
\tag{2.8}
$$

这对任意随机有限机器导出的共同极限成立，不假设其配置周期、确定性或固定相位参数。

### 2.4 源特定递推的稳定性

记 $g=g_d$，定义

$$
F(x,y)=\frac{c_p}{1+g(x)[1+g(y)]}\qquad(x,y\in I).
$$

$g$ 正且递增，$F$ 对两个变量递减。直接有理比较给

$$
F(h,h)-l=\frac{2321845450741}{160524669656250}>0,
\qquad
h-F(l,l)=\frac{5182736759969}{223698869676450}>0.
\tag{2.9}
$$

所以 $F$ 把 $I^2$ 送入 $I$。又 $g'(x)=dc/(c-x)^2$，对偏导逐项估计得

$$
|F_x|+|F_y|\le L:=
\frac{c_pdc[1+2g(h)]}
{(c-h)^2[1+g(l)(1+g(l))]^2}
=\frac{695713387328312641533061294525}
{832862736637741459097280563598}<\frac{21}{25}.
\tag{2.10}
$$

中值定理给相对于最大坐标距离的 Lipschitz 常数 $L$。连续的 $b\mapsto F(b,b)$ 在 $I$ 中有不动点 $b_\star$：其在 $l$ 的值大于 $l$，在 $h$ 的值小于 $h$，应用介值定理。式(2.10)保证其唯一。

为处理式(2.8)的误差，把 $b_n$ 截到 $I$，记为 $x_n$，则 $|b_n-x_n|\le2\epsilon_p$。在所有比较所经过的矩形中，$0\le x\le9/20$、$0\le e\le9/40$、$1-e-x\ge13/40$，因而

$$
0\le g_e(x)<\frac13,\qquad
|\partial_xg_e(x)|<3,\qquad
|\partial_eg_e(x)|<3,
\qquad c_p<\frac{13}{25}.
\tag{2.11}
$$

这些界分别来自 $ex/(1-e-x)$、$e(1-e)/(1-e-x)^2$、$x(1-x)/(1-e-x)^2$ 的上界。式(2.8)的分子误差影响至多 $\epsilon_p$；把两个输入截到 $I$，两个偏导绝对值之和小于 $5c_p<3$，影响至多 $6\epsilon_p$；把两个 $d_n$ 换成 $d$，分母的变化至多 $5\epsilon_\beta$，倒数与分子合计影响小于 $3\epsilon_\beta$。因此

$$
|b_n-F(x_{n+1},x_{n+2})|
\le7\epsilon_p+3\epsilon_\beta.
\tag{2.12}
$$

置 $\Delta=\sup_{n\ge0}|b_n-b_\star|$。它有限；截到含 $b_\star$ 的区间不会增加距离。式(2.10)、(2.12)给

$$
\Delta\le7\epsilon_p+3\epsilon_\beta+L\Delta,
\qquad
\Delta\le\frac{25}{4}(7\epsilon_p+3\epsilon_\beta).
\tag{2.13}
$$

这是整个无界续接序列的统一推论，不是有限例子的拟合。

### 2.5 第三个返回圈之后的一个完整词冲突

置 $a_\star=db_\star /(c-b_\star)$。不动点等式和该定义给

$$
b_\star[1+a_\star+a_\star^2]=c_p,
\qquad f(a_\star):=ca_\star(1+a_\star+a_\star^2)-c_p(a_\star+d)=0.
\tag{2.14}
$$

对 $a\ge0$，$f'(a)=c(1+2a+3a^2)-c_p>0$。以下有理符号精确成立：

$$
f(233/1000)=-\frac{1703748888347}{4920750000000000}<0,
\qquad
f(234/1000)=\frac{251260555397}{615093750000000}>0.
\tag{2.15}
$$

故 $233/1000<a_\star<234/1000$，从而

$$
b_\stara_\star^3>
\frac{c_p(233/1000)^3}{1+234/1000+(234/1000)^2}
=\frac{1944}{390625}+\sigma.
\tag{2.16}
$$

右边第一项正是两个实际端点在 $w_{3,1}$ 上的较大质量；$\sigma$ 是式(2.1)中的精确正有理数。

式(2.7)中 $t_n$ 对 $b_n,b_{n+1},d_n$ 的偏导绝对值分别小于 $1,1,5$：这由同一 $9/20,9/40,13/40$ 矩形直接得到。故

$$
|t_n-a_\star|\le2\Delta+5\epsilon_\beta,
\qquad 0\le t_n,a_\star<1/3.
$$

相容性把完整词质量写成 $Q_n(w_{3,1})=t_nt_{n+1}t_{n+2}b_{n+3}$。望远镜展开乘积，使用 $b_\star\le4/9$，有

$$
|Q_n(w_{3,1})-b_\stara_\star^3|
\le\frac\Delta{27}+\frac4{27}(2\Delta+5\epsilon_\beta)
=\frac\Delta3+\frac{20}{27}\epsilon_\beta.
\tag{2.17}
$$

另一方面，式(2.3)的逐词近中心约束给 $Q_n(w_{3,1})\le1944/390625+2\epsilon_p$。合并式(2.13)、(2.16)、(2.17)，得到

$$
\sigma<\frac{199}{12}\epsilon_p+
\frac{755}{108}\epsilon_\beta
\le17\epsilon_p+7\epsilon_\beta.
\tag{2.18}
$$

这证明 law 情形。任意所选 conf 风险超额逐坐标不小于 law 超额，故同一不等式适用于全部四个风险组合。式(2.2)由 $17\epsilon_p+7\epsilon_\beta\le24\max(\epsilon_p,\epsilon_\beta)$ 与取下确界得到；$\sigma/24>3/10^6$ 是正分母的有理比较。证毕。

## 3. 第三书签起点与悬置相位可以共同尖锐

**定理 3.1（起点域的有限共同达到器）。** 对每个上述固定先验，存在一个不依赖 $\mu$ 的确定性有限完整保持模型，同时满足两项生成义务，并对两个风险分别有

$$
R_j(\mathcal H_3)=\rho_p,
\qquad R_j(\mathcal H_\beta)=\rho_\beta
\quad(j=\mathrm{law},\mathrm{conf}).
\tag{3.1}
$$

它不在整个 $\mathcal H_p$ 上达到 $\rho_p$。因此 $\mathcal H_3$ 与 $\mathcal H_p$ 在单独最小值相同时，仍可有不同的共同达到问题。

**证明。** 消费 [PH, 定理2.1] 的模型 $B$，记其固定合成概率为

$$
a=\frac{23}{100},\quad
u=\frac{45277}{121660},\quad
v=\frac{6083}{16605},\quad
b=\frac{121003}{304150}.
\tag{3.2}
$$

它们满足 $(1-u)v=a$、$(1-u)(1-v)=b$；模型 $B$ 的悬置完整律是

$$
Q_\beta^B(\beta)=1-v,\qquad
Q_\beta^B(\alpha w_{j,0})=vu a^j,\qquad
Q_\beta^B(\alpha w_{j,1})=vb a^j.
$$

模型 $B$ 的全部深度悬置误差至多 $\rho_\beta$，全部非端点深度还严格小于 $7/200$；其同源合法生成与相容性均由 [PH, §§2.3–2.4] 供应。

在原完整控制之外增加一个计费位 $f$。提种前 $f=0$；第三标记按原规则写完、锁存后令 $f=1$；第四段第一笔实际 Read 令 $f=0$，此后保持0。$f=1$ 只出现在 $\mathcal H_3$ 的 $p_4$ 配置。前奏、标记、记录、第三写前锁存、completion、Stop 均不变。

令

$$
q=\frac{c_p}{1+a+a^2}=\frac{94067768}{233808525},\quad
s=1-\frac q{1-v}=\frac{1108812361}{3037201605},\quad
C=\frac{qvu}{a(1-v)}=\frac{2129553165868}{5658306590115}.
\tag{3.3}
$$

在 $f=1$ 的 $p_4$ 配置，合成下一字母 $\alpha$ 的概率为 $s$，该次更新也清零 $f$；以后所有活动载荷相位使用模型 $B$ 的 $u,v$。原提种活动阶段用各概率 $1/2$ 的合成字母，原 pending 只生成原 Stop，delivered 生成空残余。每步合成使用实际保持的同一字母更新。

从 $f=1$ 起点的完整原始律 $Q_\star$ 满足

$$
Q_\star(w_{0,0})=s,\qquad
Q_\star(w_{j,0})=Ca^j\ (j\ge1),\qquad
Q_\star(w_{j,1})=qa^j\ (j\ge0).
\tag{3.4}
$$

这是首笔分支乘上模型 $B$ 的条件残余；1词等式使用 $vb/(1-v)=a$。其质量和为1，或由合法首分支与几乎必然完成的模型 $B$ 直接得到；无限不完成质量为零。

直接有理比较给 $1/3<s<2/5$、$1/3<C<2/5$、$2/9<a<6/25$，故式(3.4)的全部0词均在两个实际端点质量之间。全部1词的 $qa^j$ 正是 [PH, §2.2] 模型 $A$ 的1词坐标，那里给出的端点夹持对整个无界词族成立。又 $Q_\star(E_p)=q(1+a+a^2)=c_p$，所以全部坐标夹持和事件平衡给

$$
\operatorname{TV}(Q_\star,P_{p,r_1})
=\operatorname{TV}(Q_\star,P_{p,r_2})=\rho_p.
\tag{3.5}
$$

还须控制真实非端点深度。对 $r\in[3/8,5/13]$，$s<r$，原第一字母分解是

$$
Q_\star=s\delta_{[\alpha]}+(1-s)(\beta Q_\beta^B),\qquad
P_{p,r}=r\delta_{[\alpha]}+(1-r)(\beta P_{\beta,r}).
$$

分开两条不交分支，三角不等式和已消费的非端点悬置余量给

$$
\operatorname{TV}(Q_\star,P_{p,r})
\le r-s+(1-s)\operatorname{TV}(Q_\beta^B,P_{\beta,r})
<\frac5{13}-s+(1-s)\frac7{200}
=\frac{9160357989}{219353449250}<\rho_p.
\tag{3.6}
$$

最后的正余量为 $72460163801494/9994291531453125$。因此对任意实际后验，包括可数非端点质量，TV 凸性给第三书签的上界 $\rho_p$。每条实际悬置历史已经清零 $f$，其解码正是模型 $B$，同一供应给上界 $\rho_\beta$。确定性保持使两个风险逐历史相等；已发表的全类下界给式(3.1)的精确达到。

新增位从第一笔 Read 前初始化，在原有限控制上作固定时间齐次更新，全部原记录仍由同一个实际字母轨迹生成。当前完整配置的律描述是原转录桥 $I_c$ 推送下的上述有限概率规则；不用物化无穷概率表。条件于任一合成下一字母，更新后的配置唯一；后续律只读该配置。所以逐词乘积给 $Q_z(xw)=q_z(x)Q_{\delta(z,x)}(w)$，并包含原确定性写入、保持、完成和 Stop 次序。这既证明每配置同更新生成，也因保持确定而证明实际历史边缘化更新相容性。

原保持字段、这个位、固定程序选择、固定有理常数、有限律描述和有界合成工作区全部计入完整配置。逐字流送合成输出不保存已经输出的无界词，不保留累计输出索引或随机带。输出长度、合成随机位与时间没有统一有限上界；实际付费取得、保持、模型、数值表示、输出、工作区、随机位、时间、能量与物理存储分别承担成本。这里只给有限完整保持的数学生成器，不给精确物理装置或总资源最优。

若它还在整个 $\mathcal H_p$ 达到 $\rho_p$，便与定理2.1及已证悬置值矛盾，所以其完整 $p$ 域风险严格更大。证毕。

## 4. 白盒质量、供应交集与未解前沿

**推论 4.1（共同白盒质量的缺口）。** 在式(1.5)的风险与有限完整保持类中，令 $W_j(\mathcal H)=1-R_j(\mathcal H)$。任意一个满足两项生成义务的共同模型，任取两个风险次序，均有

$$
17[(1-\rho_p)-W_{j_p}(\mathcal H_p)]
+7[(1-\rho_\beta)-W_{j_\beta}(\mathcal H_\beta)]>\sigma.
$$

至少一个完整相位质量低于其单独最佳质量，差严格大于 $\sigma/24$。若任务只要求第三书签起点与悬置域，定理3.1给一个共同模型达到两个单独最佳质量。

**证明。** 代入 $W=1-R$，定理2.1及式(2.2)的逐模型不等式给前两句；定理3.1给最后一句。证毕。

这里的白盒质量指固定任务的预测损失及可检查更新，不是实际训练网络的普遍可解释性。有限保持的自然职责是沿原字母保留自己的配置；实际源后验仍由同一个 $K$ 的已取得过滤决定。共同条件更新属于预测律族自身的职责，不能交给一个每次重新取公平标签的边缘读出。障碍在这两项职责的交接：共同有限保持的端点碰撞，加上完整返回词的条件更新，使两个近中心事件必须满足式(2.8)，从而在一个实际完整词上发生定量冲突。没有把配置风险的三深度方法反例升级为本定理；定理2.1另给了全类的普通证明，并首先作用于 law 风险。

[未来响应充分性][FR] §§21–26 的长度—完整转录对应、固定先验实际像上的两窗口恢复与计数恢复，保持成立。那些精确窗口是律的坐标；§25 明确计费的计数与数值精度可随实际历史增长。本定理不否定这种精确可识别性，也不把两个精确数视作两个固定宽度存储单元。若完整计数无界保持被允许，式(1.4)的真实完整条件律本身沿真实似然更新相容；这不是当前固定有限完整配置类的达到器。

[ST] 的终局 $13/266,9/266$、两深度完整尾值、任意随机有限机器的有限正历史见证，以及实际三深度公平端点标签的配置风险反例，均不改判。[PH] 的单独相位精确值与模型 $A$ 的联合域标量最优也不改判。本卷的新内容是：同一模型在整个 $p$ 与悬置域的相容性价格严格分离，且有统一正的定量余量；第三书签域则有一个新增有限位的共同尖锐生成器。这两个域的差别由同一实际返回动作承担。

[FIB ATOM 白盒卷][WB] §§1–2 的五分类是无相邻占位三位窗 $\{000,100,010,101,001\}$ 的局部语法；§§6–8 分开五个输入、四个结构状态、无界精确数值保持，以及指定任务的合法域与更新交换关系。这里同样必须先固定任务及允许续接，再判断一个表示和生成器承担什么义务；这是一项方法对应，不是把其五窗自动机映到当前二字母付费来源。五模式被动记忆、张量符号取得、整树几何、实际地址下界、KBonacci 的 INITIAL 费用与合法边增长均使用不同的来源、动作或损失。本卷不从它们转移半径、维数、取得成本或物理结论；当前桥仅是原付费 Read 词、原控制记录和原 Stop。公开实矩阵是数学常数，不是免费精确实数物理接口。

Berg–Ordentlich–Shayevitz 的[有限记忆综述][Survey] §§2.3、4、6.1、7.3 给有限状态、来源独立随机性、时间不变规则、长期检验与累计预测损失的成熟背景；其[确定性二元检验论文][BOS] §I、式(1)–(9) 使用固定 iid 假设下的长期分类错误。这些损失不等于同一实际停止历史上的完整尾条件 TV，也不提供这里两个相位的共同条件生成器。TV 三角等号、凸性、有限单纯形紧性、介值定理及收缩估计均是成熟中间方法；新增结论由原停止词及式(2.8)、(2.16)的源特定关系承担，不单独重命名通用方法。

严格不等式(2.1)及下界(2.2)尚未给出尖锐联合 Pareto 前沿、其达到性、最小完整配置数、固定配置预算的最优风险或真实历史平均风险。没有声称只有某个确定性或固定相位参数族才受限制；定理2.1覆盖任意随机有限核。没有把无限计数模型、精确后验运算、有限历史截断或总物理成本纳入该覆盖。所有证明为普通数学，不主张 kernel 核验、世界范围优先权、统计或模型独立性、物理实现或持久研究目标完成。

[PH]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md
[ST]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md
[FR]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md
[E1]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md
[BD]: https://github.com/the-omega-institute/trureturing/blob/c633bce93ac6ffd5fa44ae3d9489c87c7557a531/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md
[WB]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md
[Survey]: https://arxiv.org/html/2312.15225v1
[BOS]: https://arxiv.org/pdf/2005.07445v1

## 追加锚（本行以下为增补区）

# 条件更新的价格：完整停止尾上的近相容性与共同达到

## 1. 来源、资源与承担结论的供应

固定 $m=2,d=1,\ell=2,n=4$，安装任意有限或可数深度先验 $\mu$，其中 $\mu(1),\mu(2)>0$。第一笔实际 Read 前只抽取一次 $K$。全部付费提种拒绝和四段载荷共享此 $K$；给定 $K=k$，实际 Read 条件独立，返回 $\alpha$ 的概率为

$$
r_k=\frac{F_{k+1}}{F_{k+3}},\qquad
r_1=\frac13,\quad r_2=\frac25,\quad
\frac38\le r_k\le\frac5{13}\quad(k\ge3).
\tag{1.1}
$$

提种器接受 $\alpha\beta$ 为0、$\beta\alpha$ 为1，相等对拒绝后继续付费。在载荷 $p_i$，$\alpha$ 完成标记0、$\beta$ 进入 $q_{\beta,i}$；在 $q_{\beta,i}$，$\alpha$ 返回 $p_i$、$\beta$ 完成标记1。前三段完成后进入下一段，第四段完成后进入原 pendingStop，随后执行唯一的原 Stop，再进入 deliveredStop；两终端切面无 Read 权限。

原有限完整配置 $C_0$ 保留控制、两种种子、原裸字段与选择器、全标记树上的 $B,Q^+,Z$、权限、第三次写入完成后锁存、其后记录保持、第四段解析、completion 和 Stop 交付状态。两种种子、所有标记三元组以及所有正质量有限拒绝和返回历史都在域内。没有源重置、重新抽取深度、未来 $E_1$ 条件化、额外实际观察或控制端口。这些合同由 [BD]、[E1]、[ST] 供应。

记 $\mathcal H_3$ 为第三标记刚锁存、第四段尚无 Read 的全部正质量历史；$\mathcal H_p,\mathcal H_\beta$ 为其后分别处于 $p_4,q_{\beta,4}$ 的全部正质量有限历史。$\mathcal H_p$ 包括任意有限第四段返回圈，不能用 $\mathcal H_3$ 替代。

完整未来转录保留实际未来 Read 字母，以及由它们产生的原记录、控制、权限、完成、唯一 Stop 和交付事件；保留合法无限不完成路径。给定当前原配置 $c$，字母到转录的映射 $I_c$ 单射，反向能读回字母。[ST, §2.1] 的源桥因此保持 TV。从 $p_4$ 起的有限尾词和固定深度律为

$$
w_{j,0}=(\beta\alpha)^j\alpha,\quad
w_{j,1}=(\beta\alpha)^j\beta\beta,\quad a_r=r(1-r),
$$

$$
\begin{aligned}
P_{p,r}(w_{j,0})&=r a_r^j,&
P_{p,r}(w_{j,1})&=(1-r)^2a_r^j,\\
P_{\beta,r}(\beta)&=1-r,&
P_{\beta,r}(\alpha w_{j,0})&=r^2a_r^j,&
P_{\beta,r}(\alpha w_{j,1})&=r(1-r)^2a_r^j.
\end{aligned}
\tag{1.2}
$$

其中 $j\ge0$，无限不完成质量为零。悬置时已经取得的 $\beta$ 不再计入未来 Read。实际完整条件律为

$$
T_h^\mu=I_c\sum_k\nu_h(k)P_{s,r_k},\qquad
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
{\sum_i\mu(i)r_i^{A(h)}(1-r_i)^{B(h)}}.
\tag{1.3}
$$

计数包括原提种拒绝、全部载荷和部分解析；这两个计数及后验只用于分析，不是运行时输入。

模型类是固定非空有限 COMPLETE 配置集 $M$、来源独立初始化 $\eta$、固定时间齐次来源独立随机字母更新 $P_\alpha,P_\beta$，以及只读实际配置的归一化完整律解码 $D_z$。原控制、记录、许可、程序选择、工作区、输出游标和全部持久随机性都计入 $M$。没有免费时钟、档案、建议、相关源种子、连续隐藏寄存器、持久随机带、精确后验服务或配置分布向量接口。原 Stop 更新也属于完整更新。解码输出完整律的有限描述，而非无穷表。

同一实际历史后的数学配置分布和风险定义为

$$
\begin{aligned}
\rho_h&=\eta P_{h_1}\cdots P_{h_t},&Q_h&=\sum_z\rho_h(z)D_z,\\
e_{\rm law}(h)&=\operatorname{TV}(Q_h,T_h^\mu),&
e_{\rm conf}(h)&=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu),\\
R_j(\mathcal H)&=\sup_{h\in\mathcal H}e_j(h),&&j\in\{\mathrm{law},\mathrm{conf}\}.
\end{aligned}
\tag{1.4}
$$

TV 是半 $\ell^1$。$\rho_h,Q_h$ 是分析坐标，运行时只读实际 $z$。凸性给 $R_{\rm conf}\ge R_{\rm law}$；对实际随机历史平均是另一个量词，本卷不对该平均作下界。

每配置同更新生成始终精确要求：由配置 $z$ 的合成字母概率选取预测字母，然后使用实际保持的同一随机字母更新；产生的完整合法转录律就是 $D_z$。所有确定性记录、完成、Stop 与交付使用原次序。预测合成不是新实际 Read，不改变真实 $r_K$。本卷只放松实际历史边缘化条件更新。

消费 [PH, 定理2.1] 的两个单独最小值，以及 [ST, §3.3] 的任意随机有限机器下界：

$$
\rho_p=\frac{1116529}{22781250},\qquad
\rho_\beta=\frac{239}{6750}.
\tag{1.5}
$$

这些下界不以边缘化相容性为前提。[CO, 定理2.1] 已证明精确相容时 $17\epsilon_p+7\epsilon_\beta>\sigma$，其中

$$
\sigma=\frac{2625336439247}{29359472625000000}>0.
\tag{1.6}
$$

本卷的新结论是该源特定障碍对实际历史条件更新缺陷的定量延拓，以及同一公平端点模型在一般先验上的 law/law 和 law/conf 共同尖锐性。[CO] 是固定公开版本的普通数学供应；这里没有重新核验其 Lean 身份或给它增添 kernel 保证。

## 2. 完整实际历史上的条件更新缺陷

令 $\mathcal H^+$ 包含从第一笔 Read 前直到原 deliveredStop 的所有正质量有限实际操作历史，允许任意有限提种拒绝和载荷返回。对一个合法实际下一操作 $x$，令 $q_h(x)$ 为 $Q_h$ 的该下一操作概率。条件于这个操作并删除其已经产生的字母、确定性写入和控制前缀，得到后继切面的完整残余；记为 $\operatorname{res}_x Q_h$。它与 $Q_{hx}$ 都在原后继配置的完整转录空间上，不只比较终局标签。

**定义2.1。** 对所有上述 $(h,x)$，定义

$$
\delta(h,x)=
\begin{cases}
\operatorname{TV}(\operatorname{res}_x Q_h,Q_{hx}),&q_h(x)>0,\\
0,&q_h(x)=0.
\end{cases}
\tag{2.1}
$$

在零预测概率处不选择一个虚构条件律，也不声称条件等式；0 是“无正预测事件可条件化”的约定。实际更新仍须对该实际合法输入定义，历史及其风险仍在原域内。定义全历史缺陷和第四段缺陷为

$$
\Delta_{\rm all}=\sup_{h\in\mathcal H^+,\ x\ {
\rm legal}}\delta(h,x),\qquad
\Delta_4=\sup_{h\in\mathcal H_p\cup\mathcal H_\beta,\ x\in\{\alpha,\beta\}}\delta(h,x).
\tag{2.2}
$$

显然 $0\le\Delta_4\le\Delta_{\rm all}\le1$。pending 的唯一 Stop 后继以及 delivered 的空残余也属于原完整域；它们的条件比较为零，delivered 无下一操作，取空上确界为0。这是全正历史的最坏缺陷，不是平均、有限样本或长度截断。

**命题2.2（缺陷的实际更新含义及零恢复）。** $\Delta_{\rm all}=0$ 当且仅当原实际历史边缘化更新相容性在每个合法正预测概率续接上成立。任意有限正预测概率前缀的条件残余也等于实际更新后报告的律。$\Delta_4=0$ 给出同样的第四段结论。每配置同更新生成本身不使此缺陷为零。

**证明。** TV 为零等价于两概率律相等，所以第一句逐 $(h,x)$ 成立。对任意正预测概率有限前缀，第一步条件化与实际后继一致，后继上的下一步仍有正预测概率；按前缀长度归纳即得第二句。第四段的正续接在相位间转换或进入原确定性终端，归纳同样成立。

为核对所比较的确是保持与条件化的同一交接，令 $q_z(x)$ 为配置的合成下一字母概率，并令 $G_{z,x}=\sum_{z'}P_x(z,z')D_{z'}$。精确每配置同更新生成给

$$
\operatorname{res}_x Q_h=
\sum_z\frac{\rho_h(z)q_z(x)}{q_h(x)}G_{z,x},\qquad
Q_{hx}=\sum_z\rho_h(z)G_{z,x}\quad(q_h(x)>0).
\tag{2.3}
$$

第一式重加权配置，第二式是在同一实际输入下来源独立地更新原配置分布。两式可能不同；没有把第一式的概率向量交给运行时。式(2.3)由各配置的分支质量 $q_z(x)G_{z,x}$ 求和直接得到，亦适用于含完整确定性操作前缀的转录。证毕。

## 3. 任意随机有限核的质量—缺陷价格

**定理3.1（统一正价格）。** 在§1的原来源、全部有限 COMPLETE 随机模型及精确每配置同更新生成义务下，对任意 $j_p,j_\beta\in\{\mathrm{law},\mathrm{conf}\}$，置

$$
\epsilon_p=R_{j_p}(\mathcal H_p)-\rho_p,\qquad
\epsilon_\beta=R_{j_\beta}(\mathcal H_\beta)-\rho_\beta.
$$

二者非负，且

$$
17\epsilon_p+7\epsilon_\beta+19\Delta_4>\sigma.
\tag{3.1}
$$

所以式(3.1)亦成立于以 $\Delta_{\rm all}$ 替换 $\Delta_4$。常数独立于安装先验、状态数及随机核；不是尖锐前沿声明。

**证明。** 先证 law/law。下界由 [ST]、[PH] 给出。若 $\epsilon_p,\epsilon_\beta,\Delta_4$ 中任一个大于 $1/1000$，结论由 $\sigma<1/1000$ 立即成立。以下三者都不超过 $1/1000$，记 $\delta=\Delta_4$。

固定任意这台有限机器。消费 [ST, §§3.1、3.3] 的有限正历史见证：有两列第三书签历史，同一原配置、种子1、前三标记100，完整配置分布距离趋零，而真实后验分别集中在深度1、2。有限单纯形紧性给共同子列极限 $\lambda$。对每个固定有限合法第四段前缀 $v$，后继配置分布共同趋于 $\lambda P_v$。若端点后验质量原为 $1-\zeta$，续接后非端点质量至多 $\zeta/[(1-\zeta)L_k(v)]$，其中固定端点词似然 $L_k(v)>0$；因此整个可数非端点总质量仍趋零。

有限配置混合到解码律是 TV 收缩的概率核。令 $Q_n$ 为 $\lambda P_{(\beta\alpha)^n}$ 的原始 $p$ 尾律，$V_n$ 为再接 $\beta$ 后的原始悬置尾律；源桥 $I_c$ 删除当前共同确定性字段后保持 TV。对每个 $n\ge0,k=1,2$，风险约束给

$$
\operatorname{TV}(Q_n,P_{p,r_k})\le\rho_p+\epsilon_p,
\qquad \operatorname{TV}(V_n,P_{\beta,r_k})\le\rho_\beta+\epsilon_\beta.
\tag{3.2}
$$

全部有限续接由同一个 $\lambda$ 产生，未给机器添加一个实际历史或分布服务。

消费 [ST, §2.2] 的两个端点符号事件

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha\beta\beta\}.
$$

它们的端点平均质量为 $c_p=11758471/22781250$、$c=5261/6750$，置 $d=1-c$。端点事件差恰为 $2\rho_s$，所以事件 TV 界给

$$
|Q_n(E_p)-c_p|\le\epsilon_p,
\qquad |1-V_n(E_\beta)-d|\le\epsilon_\beta.
\tag{3.3}
$$

逐原子三角余项的和是各坐标到端点区间的距离总和，故(3.2)还给每个坐标区间外距离至多 $2\epsilon_s$，包括无限不完成原子。特别地，置

$$
b_n=Q_n(\beta\beta),\quad I=[l,h]=[9/25,4/9],\quad
\gamma_n=Q_n(\text{首字母为 }\beta),\quad
v_n=V_n(\text{首字母为 }\alpha),\quad d_n=1-V_n(E_\beta),
$$

有 $\operatorname{dist}(b_n,I)\le2\epsilon_p$，
$3/5-2\epsilon_p\le\gamma_n\le2/3+2\epsilon_p$，
$1/3-2\epsilon_\beta\le v_n\le2/5+2\epsilon_\beta$。
因此需要条件化的两个预测字母概率有统一正下界。有限混合律 TV 收敛以及正分母使(2.1)的界可取极限：

$$
\operatorname{TV}(\operatorname{res}_\beta Q_n,V_n)\le\delta,
\qquad \operatorname{TV}(\operatorname{res}_\alpha V_n,Q_{n+1})\le\delta.
\tag{3.4}
$$

这里实际域仍包含预测零概率事件；只是在承担近最优冲突的共同极限中，这两个事件由(3.2)强制为正。

令 $t_n=\gamma_nv_n$，于是 $0<t_n<1/3$。两个条件误差在实际完整事件上给

$$
b_n=\gamma_n(1-v_n)+e_n,\qquad
d_n=v_n(1-b_{n+1})+f_n,
\qquad |e_n|,|f_n|\le\delta.
\tag{3.5}
$$

对 $j\ge1$，连续使用(3.4)，第一步误差至多 $\gamma_n\delta$，第二步至多 $\gamma_nv_n\delta$。近中心界给 $\gamma_n(1+v_n)<1$，所以

$$
|Q_n(w_{j,1})-t_nQ_{n+1}(w_{j-1,1})|\le\delta.
\tag{3.6}
$$

这个界使用完整词事件，保留所有原控制与 Stop 前缀，未把词缩成终局标签。

由(3.5)，精确地

$$
t_n=\frac{(b_n-e_n)(d_n-f_n)}{1-b_{n+1}-d_n+f_n}.
$$

在 $0\le b_n,b_{n+1}\le9/20$、$0\le d_n\le9/40$、$|e_n|,|f_n|\le1/1000$ 的矩形上，分母至少 $324/1000$。此分式对 $e_n,f_n$ 的偏导绝对值分别小于1、5：上界可取 $226/324<1$ 和 $(451/1000)/(324/1000)^2<5$。将 $e_n,f_n$ 换为零得

$$
\left|t_n-\frac{d_nb_n}{1-d_n-b_{n+1}}\right|\le6\delta.
\tag{3.7}
$$

记 $g_e(x)=ex/(1-e-x)$。同一较小矩形上 $0\le g_e(x)<1/3$。乘(3.7)以 $b_{n+1}\le9/20$ 给

$$
|t_nb_{n+1}-b_ng_{d_n}(b_{n+1})|<3\delta.
$$

再用 $t_n,g_{d_n}(b_{n+1})<1/3$，两次乘积比较给

$$
|t_nt_{n+1}b_{n+2}-b_ng_{d_n}(b_{n+1})g_{d_{n+1}}(b_{n+2})|<2\delta.
$$

式(3.6)对 $j=1,2$ 给事件 $E_p$ 与 $b_n+t_nb_{n+1}+t_nt_{n+1}b_{n+2}$ 的差至多 $(2+t_n)\delta\le3\delta$。故源特定事件平衡被放松为

$$
\left|b_n\{1+g_{d_n}(b_{n+1})[1+g_{d_{n+1}}(b_{n+2})]\}-c_p\right|
\le\epsilon_p+8\delta.
\tag{3.8}
$$

下面消费 [CO, §2.4] 的静态代数证书，说明它不需精确相容性：

$$
F(x,y)=\frac{c_p}{1+g_d(x)[1+g_d(y)]}\quad(x,y\in I)
$$

将 $I^2$ 送入 $I$，且对于最大坐标距离的 Lipschitz 常数 $L<21/25$。其唯一常数不动点记为 $b_\star$。这些断言由 $F(h,h)>l$、$F(l,l)<h$、$g'_d(x)=dc/(c-x)^2$ 及

$$
L\le\frac{c_pdc[1+2g_d(h)]}
{(c-h)^2[1+g_d(l)(1+g_d(l))]^2}<\frac{21}{25}
\tag{3.9}
$$

给出；介值定理给存在，收缩界给唯一。

把 $b_n$ 截到 $I$ 得 $x_n$，有 $|b_n-x_n|\le2\epsilon_p$。对(3.8)先除以其至少为1的括号；误差 $8\delta$ 不被放大。在 $x\le9/20,e\le9/40,1-e-x\ge13/40$ 上，$g_e<1/3$ 且 $|\partial_xg_e|,|\partial_eg_e|<3$。分式的两输入偏导和及两参数偏导和都小于3；其分子至多 $c_p+1/1000<0.521$。截取输入的误差至多 $6\epsilon_p$，换 $d_n,d_{n+1}$ 为 $d$ 的误差至多 $3\epsilon_\beta$，事件分子误差至多 $\epsilon_p$。因此

$$
|b_n-F(x_{n+1},x_{n+2})|
\le7\epsilon_p+3\epsilon_\beta+8\delta.
\tag{3.10}
$$

令 $B=\sup_{n\ge0}|b_n-b_\star|$。它有限，截取不会增加到 $b_\star$ 的距离。(3.9)、(3.10)于是给整个无界返回序列的界

$$
B\le\frac{25}{4}(7\epsilon_p+3\epsilon_\beta+8\delta).
\tag{3.11}
$$

消费 [CO, §2.5] 的单词间隙。置 $a_\star=db_\star/(c-b_\star)$，则
$b_\star(1+a_\star+a_\star^2)=c_p$。消去 $b_\star$ 得
$f(a)=ca(1+a+a^2)-c_p(a+d)=0$；$f$ 在非负轴严格递增，$f(233/1000)<0<f(234/1000)$。故

$$
b_\star a_\star^3>
\frac{c_p(233/1000)^3}{1+234/1000+(234/1000)^2}
=\frac{1944}{390625}+\sigma.
\tag{3.12}
$$

此右端的第一项是实际端点在完整词 $w_{3,1}$ 上的较大质量，不是合成数值拟合。

分式 $db/(1-d-b')$ 对 $b,b',d$ 的偏导绝对值在原矩形上分别小于1、1、5；(3.7)给
$|t_n-a_\star|\le2B+5\epsilon_\beta+6\delta$。乘积望远镜展开使用 $t_n,a_\star<1/3,b_\star\le4/9$，给

$$
|t_nt_{n+1}t_{n+2}b_{n+3}-b_\star a_\star^3|
\le\frac B3+\frac{20}{27}\epsilon_\beta+\frac89\delta.
$$

式(3.6)连续三次的误差至多 $(1+1/3+1/9)\delta=13\delta/9$，所以

$$
|Q_n(w_{3,1})-b_\star a_\star^3|
\le\frac B3+\frac{20}{27}\epsilon_\beta+\frac73\delta.
\tag{3.13}
$$

另一方面，(3.2)的逐词端点区间界给 $Q_n(w_{3,1})\le1944/390625+2\epsilon_p$。合并(3.11)–(3.13)，得到

$$
\sigma<\frac{199}{12}\epsilon_p+\frac{755}{108}\epsilon_\beta+19\delta
\le17\epsilon_p+7\epsilon_\beta+19\delta.
$$

最后，对于任一选取的 conf 坐标，其超额不小于对应 law 超额；非负系数使同一不等式适用于全部四个风险组合。证毕。

**推论3.2（趋零缺陷不能买到共同近最优）。** 对任意一列允许状态数和核变化的合法有限模型，若两个指定相位风险趋于各自单独最小值，则

$$
\liminf\Delta_4\ge\frac\sigma{19}
=\frac{2625336439247}{557829979875000000}>0.
\tag{3.14}
$$

若 $\Delta_4\to0$，则

$$
\liminf\max(\epsilon_p,\epsilon_\beta)\ge\sigma/24.
\tag{3.15}
$$

对单个模型且 $\Delta_4<\sigma/19$，还有
$\max(\epsilon_p,\epsilon_\beta)>(\sigma-19\Delta_4)/24$。
这些结论对 $\Delta_{\rm all}$ 同样有效。

**证明。** 重排(3.1)，使用 $17\epsilon_p+7\epsilon_\beta\le24\max(\epsilon_p,\epsilon_\beta)$，再取下极限。证毕。

## 4. 一个共同、合法的非零缺陷达到器

**定理4.1（一般先验的共同 law/law 与 law/conf 达到）。** 对每个§1的先验，复用 [ST, §2.4] 的同一公平端点标签模型 $M_{\rm tag}$：第一笔 Read 前独立于实际源初始化 $J\in\{1,2\}$，各概率 $1/2$，实际全过程保持 $J$。完整配置为 $(C_0,J)$，各标签解码由 $r_J$ 和原控制更新生成的完整未来律。它满足精确每配置同更新生成，且在同一实际来源、同一模型上

$$
R_{\rm law}(\mathcal H_p)=\rho_p,
\qquad R_{\rm law}(\mathcal H_\beta)
=R_{\rm conf}(\mathcal H_\beta)=\rho_\beta.
\tag{4.1}
$$

其缺陷满足

$$
\Delta_4=\frac{1116529}{250593750},\qquad
\frac{1116529}{250593750}\le\Delta_{\rm all}\le\frac1{22}.
\tag{4.2}
$$

若实际先验只支持深度1、2，还同时有 $R_{\rm conf}(\mathcal H_p)=\rho_p$，从而一个共同模型实现全部四个风险组合的两个坐标最优。若 $\mu(\{k\ge3\})>0$，则该模型反而满足

$$
R_{\rm conf}(\mathcal H_p)\ge\rho_p+\frac\eta2,
\qquad \eta=\frac{14219478376}{318644812890625}>0.
\tag{4.3}
$$

这是公平标签方法的全先验边界，不是任意其他随机模型的更强下界。

**证明。** 原实际字母更新确定地更新 $C_0$ 并保持 $J$，因此在每条实际历史后 $J$ 仍公平，与真实 $K$ 无关。预测合成在标签 $J$ 内按 $r_J$ 产生字母，并使用同一原控制和记录更新；提种拒绝、接受、四段解析、第三次先写后锁存和唯一 Stop 都与实际更新相同。提种接受概率 $2r_J(1-r_J)>0$，每段返回概率不超过 $1/4$，故合成几乎必然完成。逐字乘积及原转录桥给每配置完整律，条件于预测字母后的残余正是同一 $J$ 和原后继配置的生成律。pending 与 delivered 残余分别为原 Stop 与空律。因此每配置同更新生成精确成立，全原域保留。

在两个第四段相位，边缘预测都是 $Q_s^{\rm mid}=(P_{s,r_1}+P_{s,r_2})/2$ 的原转录推送。下面新增的是它在一般实际先验上的完整 law 上界；没有把两个独立中心声明为一个生成器。

先看悬置相位。对任意 $1/3\le r\le2/5$，式(1.2)的每个坐标都在两个端点坐标之间。具体地，$1-r$ 递减；$r^{j+2}(1-r)^j$ 的导数符号由 $(j+2)-(2j+2)r>0$ 决定；$r^{j+1}(1-r)^{j+2}$ 在 $j=0$ 时递减，在 $j\ge1$ 时递增，因为 $(j+1)-(2j+3)r\ge0$。无限原子一直为零。于是逐词有

$$
|Q_\beta^{\rm mid}(w)-P_{\beta,r}(w)|
\le\tfrac12|P_{\beta,r_1}(w)-P_{\beta,r_2}(w)|.
$$

求和给 law 风险上界 $\rho_\beta$。实际后验的任意可数混合仍逐坐标在端点区间内；三角等号因而给

$$
\tfrac12\operatorname{TV}(I_cP_{\beta,r_1},T_h^\mu)
+\tfrac12\operatorname{TV}(I_cP_{\beta,r_2},T_h^\mu)=\rho_\beta.
\tag{4.4}
$$

这正是同一公平标签模型的 conf 风险，故其每条悬置历史的 conf 风险都等于 $\rho_\beta$。

$p$ 相位不能用这个逐坐标论证：$w_{3,1}$ 的质量在 $r=3/8$ 高于两个端点，正是 [ST, §3.3] 的方法反例。我们改用该源的全尾连续估计和实际非端点间隙。

令 $r_0=3/8$、$Q=Q_p^{\rm mid}$。在 $j<4$ 的八个完整词上直接有理计算，并以全部剩余质量界住无界尾，给

$$
\begin{aligned}
\operatorname{TV}(Q,P_{p,r_0})
&\le\frac12\sum_{j=0}^3\sum_{b=0}^1
|Q(w_{j,b})-P_{p,r_0}(w_{j,b})|\\
&\quad+\frac12\left[\frac{(2/9)^4+(6/25)^4}{2}+(15/64)^4\right]\\
&=\frac{162769594313}{10497600000000}<\frac2{125}.
\end{aligned}
\tag{4.5}
$$

为使这个有限证书可复算，八个差 $Q-P_{p,r_0}$ 的符号按 $j=0,1,2,3$、每行 $b=0,1$ 排列为 $(-,+),(-,+),(-,-),(-,-)$；半绝对值和为 $1079904575135423/85996339200000000$，余量项为 $253503941476673/85996339200000000$。剩余词总质量恰是四个返回圈的生存概率，故(4.5)不是有限网格代替全尾。

对任意 $r,s\in[1/3,2/5]$，用共同独立均匀数耦合两种 Bernoulli Read，并在各自原解析停止时截尾。首次不一致前解析路径相同。若 $r$ 路径停止时间为 $\tau_r$，第 $i$ 笔之前仍活动的事件只依赖先前均匀数；该笔字母不一致概率为 $|r-s|$。并集界和非负求和给

$$
\operatorname{TV}(P_{p,r},P_{p,s})\le|r-s|\mathbb E_r\tau_r
=|r-s|\frac{2-r}{1-r(1-r)}\le\frac{15}{7}|r-s|.
\tag{4.6}
$$

期望等式由第一笔必读、概率 $1-r$ 再读一笔、概率 $r(1-r)$ 返回起点的递推得到。最后分式在该区间递减，其导数分子为 $1-4r+r^2<0$；在 $r=1/3$ 取最大 $15/7$。这是原完整停止词的耦合；确定性派生记录和 Stop 由单射桥跟随，不删去任何未来 Read。

每个实际非端点 $r_k$ 都在 $[3/8,5/13]$，所以(4.5)、(4.6)给

$$
\operatorname{TV}(Q,P_{p,r_k})<\frac2{125}+\frac{15}{728}
=\frac{3331}{91000}<\rho_p\quad(k\ge3).
\tag{4.7}
$$

最后不等式的正有理余量是 $102879181/8292375000$。两个端点到 $Q$ 的距离都是 $\rho_p$。对(1.3)的同一实际后验用可数混合 TV 凸性，得到每条 $p$ 历史的 law 风险至多 $\rho_p$。全类下界使(4.1)的两个 law 上确界恰等于给定值。

若实际先验只支持两个端点，$T_h^\mu$ 本身位于端点线段上，公平标签的 conf 风险也逐历史等于半端点距离，故额外结论成立。对于一般先验，(4.4)的悬置结论仍成立，但 $p$ 结论失败。例如 [ST, §3.3] 的实际先验 $(1/10000,1/10000,4999/5000)$ 和正第三书签历史 $h_0=\beta\alpha\mid\beta\beta\alpha\alpha$ 给该模型

$$
e_{\rm conf}(h_0)\ge\rho_p+
\frac{27761274267842375925431}{1057908398638978889573990400}>\rho_p.
\tag{4.8}
$$

这是一个模型的 conf 反例；(4.7)同时证明其 law 风险没有被这个反例推高到 $\rho_p$ 以上。

为证明(4.3)，令 $H(r)=r^3(1-r)^5=P_{p,r}(w_{3,1})$。其导数符号由 $3-8r$ 决定，所以在实际非端点区间 $[3/8,5/13]$ 上的最小值为 $H(5/13)$。它严格大于两个端点值；到较大端点 $H(2/5)$ 的差恰是 $\eta$，到 $H(1/3)$ 的差是 $770472928/5352009260481>0$。

取原正实际历史

$$
h_t=(\alpha\alpha)^{3t}(\beta\beta)^{5t}\,
\beta\alpha\mid\beta\beta\alpha\alpha\qquad(t\ge0).
$$

前两个块全部是合法付费提种拒绝，随后取得种子1和前三标记100，当前原配置不变。这条历史的计数是 $A=6t+3,B=10t+3$，深度 $k$ 的似然为

$$
a_{r_k}^{3}H(r_k)^{2t}.
$$

选一个有正先验质量的非端点 $k_0$。两个端点的后验分别至多

$$
\frac{\mu(i)a_{r_i}^{3}}{\mu(k_0)a_{r_{k_0}}^{3}}
\left[\frac{H(r_i)}{H(r_{k_0})}\right]^{2t}\longrightarrow0
\quad(i=1,2).
$$

因此整个非端点后验质量趋1，即使原先验可数且其非端点总质量很小也成立，无须逐深度极限交换。于是 $T_{h_t}^\mu(I_cw_{3,1})\ge H(5/13)-o(1)$，超过两个端点在该词的较大质量至少 $\eta-o(1)$。逐坐标三角余项恒等式给该公平标签模型 $e_{\rm conf}(h_t)\ge\rho_p+(\eta-o(1))/2$；对原正历史取上确界即得(4.3)。这一证明同时绑定付费取得的似然和完整合法未来词；没有让机器读取这些增长计数。

最后计算同一模型的缺陷。在任意原实际活动历史，预测下一 $\alpha$ 后两个标签权重由 $1/2,1/2$ 变为 $5/11,6/11$；预测下一 $\beta$ 后变为 $10/19,9/19$。实际字母更新后标签仍公平。若原后继配置是 $c'$，式(2.3)因此精确给

$$
\delta(h,\alpha)=\frac1{22}\operatorname{TV}(T_{c',1},T_{c',2}),\qquad
\delta(h,\beta)=\frac1{38}\operatorname{TV}(T_{c',1},T_{c',2}).
\tag{4.9}
$$

$T_{c',j}$ 在此表示标签 $j$ 下从原后继切面起的完整未来生成律，包括提种和较早载荷切面。故全历史缺陷至多 $1/22$。在 $p_4$，$\alpha$ 完成0，其残余无标签区别；$\beta$ 转悬置，缺陷为 $2\rho_\beta/38=239/128250$。在 $q_{\beta,4}$，$\beta$ 完成1，其残余无区别；$\alpha$ 返回 $p_4$，缺陷为 $2\rho_p/22=1116529/250593750$。比较两正有理数给(4.2)。这些数在任意正实际相位历史都成立，不依赖实际后验，亦不要求额外实际源查询。证毕。

模型 $(C_0,J)$ 从第一笔实际 Read 前初始化。固定原有限控制、有限记录字典、计费位 $J$、两个有理常数、固定生成程序和有界工作区全部属于完整资源。解码只需“原控制加 $r_J$ 的逐字规则”这一有限描述，既不物化无限概率表，也不保存连续后验。合成字母和转录可以逐字流送，不保留已输出的无界词、累计输出索引或随机带。输出长度、合成随机位和时间无统一有限上界；实际付费取得、保持、模型/表、数值表示、输出、合成工作区、随机位、时间、能量和物理存储是不同成本账户。本结果是数学随机生成器，不是免费精确实数装置或物理资源最优结论。

## 5. 任务相对白盒质量与尚未求出的前沿

对固定任务定义 $W_j=1-R_j$。定理3.1给同一模型、同一先验和同一实际历史域上的质量—相容性价格：

$$
17[(1-\rho_p)-W_{j_p}(\mathcal H_p)]
+7[(1-\rho_\beta)-W_{j_\beta}(\mathcal H_\beta)]
+19\Delta_4>\sigma.
$$

定理4.1则给明确因果比较：

| 同一模型及实际先验 | $p$ 相位风险 | 悬置风险 | 第四段缺陷 |
| --- | --- | --- | --- |
| $M_{\rm tag}$，任意允许先验，law/law | $\rho_p$ | $\rho_\beta$ | $1116529/250593750$ |
| $M_{\rm tag}$，任意允许先验，law/conf | $\rho_p$ | $\rho_\beta$ | 同上 |
| $M_{\rm tag}$，仅两实际端点，全部四组合 | $\rho_p$ | $\rho_\beta$ | 同上 |
| [PH] 的模型 $A$，任意允许先验，两风险 | $\rho_p$ | 小于 $1/25$ | 0 |

最后一行是已发表供应，不计作新达到器。其两个风险相等，因为保持确定。[CO, 定理3.1] 的 $\mathcal H_3/\mathcal H_\beta$ 零缺陷共同尖锐例外也保持；它不能替代这里完整 $\mathcal H_p$ 的无界返回域。

这里的白盒质量是指定实际过程的完整尾预测质量和可检查更新，不是实际训练网络的普遍可解释性。可公开且精确生成的标签模型仍在边缘条件化时改变模型权重，而实际观察不会为这个独立标签提供同样的证据。全部一般先验上的两个 law 最小值可以共同达到；它们与趋零的边缘化相容性不能同时取得。这两个结论使用相同来源、更新、完整未来事件和配置计费。

[ST] 的终局 $13/266,9/266$、两深度完整尾 $\rho_p,\rho_\beta$、全类有限见证和实际三深度标签方法反例不改判。[PH] 的全先验单独最小值和精确相位生成器不改判；[CO] 的精确相容障碍不重复计作新结果。式(3.8)和(3.13)提供新增的实际条件误差到源特定冲突的桥；式(4.5)–(4.7)关闭公平标签机器在一般先验的边缘完整尾上界缺口，式(4.4)同时关闭其悬置 conf 上界缺口。

以下仍未证明：固定缺陷预算下的尖锐联合 Pareto 前沿；达到两 law 最小值所需的最小 $\Delta_4$ 或 $\Delta_{\rm all}$；一般先验含 $p$-conf 坐标的共同最小值是否可由另一随机模型同时达到；最小 COMPLETE 配置数；固定状态预算的最优风险；实际历史平均风险；以及完整全历史缺陷的精确最小值。式(3.14)与标签模型的(4.2)之间存在未关闭的量化区间。式(4.3)只结算公平标签模型，未把它的失败升级成任意模型的 conf 下界，也没有把有界数值枚举升级成无界核证明。

## 6. 供应比较与证据边界

仓内有限 deficiency 风险转移与三角结果处理实验之间的近似随机模拟和有界决策损失；BeliefMarkovUpdate 处理给定实际联合权重的 Bayes 更新。它们不直接给当前来源的完整停止尾、同一实际历史、有限状态保持及边缘更新缺陷。式(2.3)消费成熟的条件混合计算，不新增独立的 Bayes 方法定理。钉版 Mathlib 的 `PMF.bind_apply` 和 `condDistrib_apply_of_ne_zero` 是这些混合及正事件条件化的基础供应，未读到当前源特定风险—缺陷价格；这里只读声明，不作编译结论。

Abate–Redig–Tkachev 的 [条件概率扰动论文][ART] Theorems 1–2、equations (2.1)–(2.2) 研究由条件概率核产生的乘积概率测度的 TV 扰动。其范数是本卷半 $\ell^1$ 的两倍；统一换算后，Theorem 1 的有限前缀逐步误差累积是成熟方法，Theorem 2 在 Borel 空间还给乘积型改进。这里不把它改名为新理论：原共同历史极限、两个完整停止事件的平衡和第三返回圈词的正间隙决定(3.1)。本卷逐词条件误差直接按(3.4)–(3.6)展开，不把整族 $Q_n,V_n$ 预先假定为某个一致路径测度。通用路径扰动界本身不能证明条件核来自同一实际保持，也不供应这三个源特定关系；式(2.3)、(3.4)、(3.8)、(3.13)承担所需对应。

Berg–Ordentlich–Shayevitz 的 [有限记忆综述][Survey] 使用有限状态、来源独立随机性、时间不变规则、长期检验和累计预测损失。其背景可复用，长期分类或累计平方损失不等于本卷每条实际停止历史的完整条件 TV。Balle–Panangaden–Precup 的 [奇异值自动机论文][SVA] Theorem 7.1 要求最小加权自动机、平方可和词函数及其 Hankel 奇异值，给平方词函数误差；它不保持本卷所需的随机归一化、原 paid-Read 条件关系和 COMPLETE 资源合同，因此不能直接供应本前沿。

[WB] §§1–2 的五分类是无相邻占位三位窗 $\{000,100,010,101,001\}$ 的输入语法，动态解释还要对指定续接和递归操作闭合；输入类别数不直接规定控制器状态数。§43 是这些五窗原始输入、首次坏接缝标签和平方完整标签风险；其谱截断与共同树不相容结果提供“局部最佳未必相容”的研究提示，但没有从五窗被动源到当前共享深度源的操作、损失或资源映射。本卷检验的闭合关系具体为(2.3)，误差和质量具体为(2.1)、(1.4)，没有把五窗的状态、谱或损失当成它们的参数。[QSP] 的系数跨度 $2\to3\to2$ 不保证固定子空间单项式/等距作用；这是另一来源与操作的反例。这里不从相同维数、统一术语或比方转移 QSP、机器学习、几何、取得或物理成本结论。张量符号取得、原地址、KBonacci 和其他 atomic 构造也没有在本卷取得这种桥。

TV 凸性、三角余项、有限单纯形紧性、介值与收缩估计、共同均匀耦合和几何生存尾均为成熟工具，消费在上述证明内部。新增知识限于所列原来源的量化不相容价格及共同达到范围。证明都是普通数学与精确有理算术核对；没有 Lean kernel 核验、物理实现、实际训练网络定理、世界范围新颖性、统计或模型独立性、或持续研究目标完成声明。

[CO]: https://github.com/the-omega-institute/trureturing/blob/2fb672d85b9efe8f1b4e7bd135a14474aea3b258/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SIMULTANEOUS_PHASE_COHERENCE_OBSTRUCTION.md
[PH]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md
[ST]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md
[BD]: https://github.com/the-omega-institute/trureturing/blob/c633bce93ac6ffd5fa44ae3d9489c87c7557a531/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md
[E1]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md
[WB]: https://github.com/the-omega-institute/trureturing/blob/b61f5e5c68557444246bef639ca3b41534f09889/docs/develop/theory/FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md
[QSP]: https://github.com/the-omega-institute/trureturing/blob/b61f5e5c68557444246bef639ca3b41534f09889/Blueprint/D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.md
[ART]: https://arxiv.org/abs/1311.3066v1
[Survey]: https://arxiv.org/html/2312.15225v1
[SVA]: https://arxiv.org/html/1711.05994v2

## 追加锚（本行以下为增补区）

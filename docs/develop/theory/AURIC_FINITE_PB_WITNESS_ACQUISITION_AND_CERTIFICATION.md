# AURIC：有限 PB 见证的取得与认证

## 1. 同一固定输出与额外读数合同

**定义 1.1（自然归属与固定接口）。** 本卷为[《全 PB 多项式运输与实根刚性》](AURIC_FULL_PB_POLYNOMIAL_TRANSPORT_AND_REAL_ROOT_RIGIDITY.md) §§34、41–43 的同主题续卷，简称该卷为 $\mathsf F$；直接引用取提交 `265caa03bf0348cdb2214aa17dece360c4bb7f6b` 的正文。复用 $\mathsf F$ 定理 41.2 的比例标签恒等式和定理 43.1 的平方根稳定性，不重证它们。这里研究的缺口是：依赖未知余量的两份数学见证，怎样在额外标量读数合同下变成预先固定、逐项执行的有限认证菜单。

设 $A$ 为含单位复 $C^*$-代数，$P\in A$ 为投影，$p,q\le P$ 为非零正交投影。固定

$$
\begin{gathered}
\Sigma=p+q,\qquad c=p+2q,\qquad \sigma\in\{1,-1\},\qquad
K_\sigma(u,v)=\frac{\sigma i}{2}[u,v],\\
T\in pAq,\qquad \tau=T+T^*,\qquad
t=\tau+b,\qquad b=b^*=(1-\Sigma)b(1-\Sigma),\\
s=s_p+s_q,\qquad s_p=s_p^*\in pAp,\quad s_q=s_q^*\in qAq,\qquad
v=K_\sigma(c,\tau),\qquad g=v+s.
\end{gathered}
\tag{1.1}
$$

整个论证使用同一份 $t,g,s$。$b$ 可任意大，$A$ 可以无限维；只禁止 $\Sigma$ 与其补块之间的连线，并保持 $ptp=qtq=0$。不要求 $T$ 可逆、单射、满射、满支撑或有闭值域，也不要求 $p\sim q$。

对 $x=x^*\in PAP$，完整原标签为

$$
\begin{gathered}
h_x=K_\sigma(c,x),\qquad r_x=c\circ x,\qquad k=c\circ t,
\qquad u\circ w=(uw+wu)/2,\\
R_\pm(x)=x\pm(h_x-k),\qquad
S_\pm(x)=t\pm(r_x+g),\\
L(x)=-2x\circ(h_x-k)-2t\circ(r_x+g).
\end{gathered}
\tag{1.2}
$$

对任意数学正泛函 $\phi$ 定义

$$
B_\phi(U,V)=\phi(U^2)\phi(V^2)-\phi(U\circ V)^2\ge0
\qquad(U=U^*,\ V=V^*).
\tag{1.3}
$$

原固定二表条件始终精确为

$$
\mathsf{P2}(c,t;g):\qquad
\phi(g)^2\le B_\phi(c,t)\qquad(\phi\ge0).
\tag{1.4}
$$

量词包含全部数学正泛函、零泛函、任意有限非负质量及非正常正泛函。不能把有限菜单上的近似检查替代 (1.4)，也不把其中的原质量归一。

**定义 1.2（有限坐标与同输出差额端口）。** 另给已知的含单位 $*$-同构

$$
\Theta:\Sigma A\Sigma\longrightarrow M_r(\mathbb C),\qquad
\operatorname{rank}\Theta(p)=a\ge1,\quad
\operatorname{rank}\Theta(q)=b_0\ge1,\quad r=a+b_0,
\tag{1.5}
$$

以及已知通道 $T$ 和界 $\|T\|\le M$。所需有限维条件仅限于这个支持角。对每个复单位向量 $\xi\in\mathbb C^r$，置

$$
\phi_\xi(y)=\langle\Theta(\Sigma y\Sigma)\xi,\xi\rangle.
\tag{1.6}
$$

这是 $A$ 上质量一的数学正泛函。它是额外端口的指定查询坐标，不宣称每个原物理评价都已被制备成此态。

一次允许查询是 $(x,\xi)$，其中 $x=x^*\in\Sigma A\Sigma$。端口只报告一个实数 $y$，满足

$$
\begin{aligned}
|y-\Delta_g(x,\xi)|&\le\nu,\\
\Delta_g(x,\xi)&=
|\phi_\xi(L(x))|
-\sqrt{B_{\phi_\xi}(R_+(x),S_+(x))}
-\sqrt{B_{\phi_\xi}(R_-(x),S_-(x))},
\end{aligned}
\tag{1.7}
$$

其中 $\nu\ge0$ 已知。$\Delta_g$ 是带符号差额，不作正部截断。平方、Gram 与误差界全部针对 (1.2) 的完整原标签。每次查询都使用同一固定未知 $g$，查询不改变数据；误差可相关、可依赖全部既有报告。本合同直接供应 (1.7) 的标量精度，不额外供应其中各矩或未知矩阵条目。

菜单的已知输入是 $p,q,P,\sigma,\Theta,T,M$ 及精度和阈值；不需要知道 $s,g,b$ 来选择查询。端口对所列请求均可取得报告，是本卷另加的访问假设。它不由数学正泛函的存在、原 P2 或原 PB 自动产生，不是物理取得保证。

## 2. 从余量依赖见证到来源盲的有限菜单

**定理 2.1（PB 特定的有限差额认证）。** 在定义 1.1–1.2 和精确 (1.4) 下，设 $M>0$，取 $\delta>0$、$\eta,\nu\ge0$。令

$$
D=a^2+b_0^2,\qquad d_\pm=\frac{1\pm\sqrt{10}}3.
\tag{2.1}
$$

存在一个在未知 $g$ 之前固定的有序菜单，查询数至多

$$
N\le 2\,9^{2r}\left(1+\frac{4M}{\delta}\right)^D,
\tag{2.2}
$$

且所有探针满足 $\|x\|\le8M$。按预定次序查询全部成员，在且仅在全部报告 $y\le\eta$ 时接受。若有报告超过阈值，可提前结束且不作范数认证。该规则具有以下性质：

1. 对任意允许误差，接受蕴含

$$
\boxed{\ \|s\|\le10^{1/4}
\sqrt{\eta+\nu+55M\delta}.\ }
\tag{2.3}
$$

2. 若 $s=0$ 且 $\eta\ge\nu$，则每份允许报告历史均接受。
3. 更一般地，对任意 $\rho\ge0$，若 $\|s\|\le\rho$ 且 $\eta\ge22M\rho+\nu$，则每份允许报告历史均接受。

这里“来源盲”只指菜单与执行次序不依赖未知 $s,g$；已知 $T$ 可以进入菜单。结论给出条件认证，不给最优查询数、位复杂度、统计样本数或物理制备成本。

**证明，先验候选集与预定查询。** 将 $pAp_{\rm sa}\oplus qAq_{\rm sa}$ 视为实维数 $D$ 的赋范空间，范数为两个块范数的最大值。精确 P2 的角读取直接复用 $\mathsf F$(43.11)：

$$
|\omega(s_p)|^2\le\omega(TT^*),\qquad
|\omega(s_q)|^2\le4\omega(T^*T)
\tag{2.4}
$$

分别对全部 $pAp$、$qAq$ 状态成立。因此状态范数公式给

$$
\|s_p\|\le M,\qquad \|s_q\|\le2M,
\qquad s\in\mathcal K:=
\{z_p+z_q:z_p=z_p^*,\ z_q=z_q^*,\ \|z_p\|\le M,\ \|z_q\|\le2M\}.
\tag{2.5}
$$

这里候选块分别属于 $pAp,qAq$。$\mathcal K$ 由已知坐标和 $M$ 确定，不需判定候选是否满足 P2。

取中心位于 $\mathcal K$ 的有限 $\delta$-网 $\mathcal Z$。通常的体积打包法给

$$
|\mathcal Z|\le(1+4M/\delta)^D.
\tag{2.6}
$$

具体地，$\mathcal K$ 位于半径 $2M$ 的球内；任意距离严格大于 $\delta$ 的中心族，其半径 $\delta/2$ 开球互不相交，且位于半径 $2M+\delta/2$ 的球内。比较 $D$ 维 Lebesgue 体积即得 (2.6)，最大分离族覆盖 $\mathcal K$。同一成熟覆盖论证在 $\mathbb C^r\simeq\mathbb R^{2r}$ 的单位球面上给一份 $1/4$-网 $\mathcal V$，满足 $|\mathcal V|\le9^{2r}$。

这些是通常有限网工具，沿用 Vershynin，[*Introduction to the non-asymptotic analysis of random matrices*，arXiv:1011.3027v7，Lemma 5.2](https://arxiv.org/html/1011.3027v7)。下面还使用其 Lemma 5.4 的二次型范数化方法；复自伴版本的估计在本证明内给出。这些成熟工具本身不提供 PB 的访问合同或下面的标签扰动界。

对每个 $z=z_p+z_q\in\mathcal Z$ 及 $d\in\{d_+,d_-\}$，只用已知数据构造

$$
Z_d(z)=\frac{z_p}{d-1}+\frac{z_q}{d-2},\qquad
u_d=\frac{v}{d-3/2},\qquad x_d(z)=u_d+Z_d(z).
\tag{2.7}
$$

菜单是全部 $(x_d(z),\xi)$，$\xi\in\mathcal V$，预先给定任一枚举次序；不根据报告重选中心。所用分母非零由 $\mathsf F$ §41.2 已付。由 $3<\sqrt{10}<13/4$，两根的系数满足

$$
\begin{gathered}
|d|^{-1}<3/2,\qquad
\max_d|(d-1)^{-1}|=(\sqrt{10}+2)/2<3,\\
\max_d|(d-2)^{-1}|=(\sqrt{10}+5)/5<7/4,\qquad
\|u_d\|\le\frac{7+2\sqrt{10}}3M<\frac92M.
\end{gathered}
\tag{2.8}
$$

由 $\tau^2=TT^*+T^*T=4v^2$ 和正交角范数，$\|\tau\|=\|T\|$、$\|v\|=\|T\|/2$，给出最后一式。正交对角块给 $\|Z_d(z)\|\le7M/2$，故 $\|x_d(z)\|\le8M$。查询总数由 (2.6) 和球面网大小给出 (2.2)。同样的范数界适用于数学见证 $x_d(s)$，但实际菜单不查询未知中心 $s$。

**证明，必须读取原输出的近比例标签。** 固定真实 $s$，仅在证明中选一个满足 $\|s-z\|\le\delta$ 的 $z\in\mathcal Z$。令

$$
e=s-z,\qquad E_d=x_d(z)-x_d(s)=Z_d(z-s),\qquad \|E_d\|\le3\delta.
\tag{2.9}
$$

候选只改变探针；任何标签中的 $g$ 仍为 $v+s$。由于 $Z_d(z)$ 与 $c$ 交换，$\mathsf F$(41.13) 的第一式仍给 $h_{x_d(z)}-k=\tau/d$，而第二式的准确余项为

$$
r_{x_d(z)}+g=d x_d(z)+e.
\tag{2.10}
$$

因而在查询 $x_d(z)$ 上，完整原标签为

$$
\begin{gathered}
R_\pm=x_d(z)\pm\tau/d,\qquad
S_+=b+dR_++e,\qquad S_-=b-dR_--e,\\
\|R_\pm\|\le8M+\tfrac32M<10M.
\end{gathered}
\tag{2.11}
$$

这不是将未知输出换成 $v+z$ 后得到的零 Gram。背景 $b$ 保留在两个 $S$ 标签；由于所有其他元素支撑在 $\Sigma$，对 (1.6) 的读取，$b$ 及其平方和交叉项不贡献。Gram 对第二变量加实数倍第一变量不变，故

$$
\begin{aligned}
B_{\phi_\xi}(R_+,S_+)&=B_{\phi_\xi}(R_+,e),\\
B_{\phi_\xi}(R_-,S_-)&=B_{\phi_\xi}(R_-,-e),\\
\sqrt{B_{\phi_\xi}(R_+,S_+)}+
\sqrt{B_{\phi_\xi}(R_-,S_-)}&\le20M\delta.
\end{aligned}
\tag{2.12}
$$

末式用 $B_\phi(U,e)\le\phi(U^2)\phi(e^2)$ 及 $\phi_\xi(1)=1$。没有把背景从原标签中删除。

记 $\Lambda_d=L(x_d(s))$。$\mathsf F$(41.17) 保证 $\Lambda_d\in\Sigma A\Sigma$ 自伴，并在该数学见证上使两笔支持 Gram 为零。由 (1.2)、$[c,E_d]=0$、$bE_d=E_db=0$，

$$
\begin{aligned}
L(x_d(z))-\Lambda_d
&=-2E_d\circ(\tau/d)-2\tau\circ(cE_d),\\
\|L(x_d(z))-\Lambda_d\|
&\le2M(|d|^{-1}+2)\|E_d\|
\le21M\delta.
\end{aligned}
\tag{2.13}
$$

这里 $cE_d=c\circ E_d$ 是自伴元素。由接受条件和端口误差，全部实际菜单差额至多 $\eta+\nu$。将 (2.12)–(2.13) 加到同一份查询上，得到对每个 $\xi\in\mathcal V$、每个 $d$，

$$
|\phi_\xi(\Lambda_d)|
\le\eta+\nu+41M\delta
\le\kappa:=\eta+\nu+55M\delta.
\tag{2.14}
$$

使用 $55$ 是统一放宽，不主张最佳常数。特别是没有把分别可达的读数当作同一 $s$ 上的联合实现。

**证明，从有限读取恢复原质量预算。** 对任意自伴 $H\in M_r(\mathbb C)$，取单位向量 $w$ 达到 $|\langle Hw,w\rangle|=\|H\|$，再取 $\xi\in\mathcal V$ 使 $\|w-\xi\|\le1/4$。则

$$
|\langle Hw,w\rangle-\langle H\xi,\xi\rangle|
\le2\|H\|\|w-\xi\|\le\|H\|/2,
\qquad
\|H\|\le2\max_{\xi\in\mathcal V}|\langle H\xi,\xi\rangle|.
\tag{2.15}
$$

对 $H=\Theta(\Lambda_d)$，(2.14) 给 $\|\Lambda_d\|\le2\kappa$，即 $-2\kappa\Sigma\le\Lambda_d\le2\kappa\Sigma$。于是对 $A$ 上任意数学正泛函，保留其实际质量而有

$$
|\phi(\Lambda_d)|\le2\kappa\phi(\Sigma)\le2\kappa\phi(1).
\tag{2.16}
$$

完整两笔 Gram 非负，所以 (2.16) 蕴含 $\mathsf F$(43.4) 在真实见证 $x_d(s)$ 上、预算参数为 $2\kappa$ 的全部正泛函不等式。直接应用 $\mathsf F$ 定理 43.1，得

$$
\|s\|\le10^{1/4}\sqrt{(2\kappa)/2}=10^{1/4}\sqrt\kappa.
$$

这一步重新取得全部质量的预算，包含零质量及非正常泛函；没有把有限纯态检验直接冒充原全正 P2。证明了 (2.3)。

**证明，零余量与近零余量的全误差通过。** 先置 $s=0$，在任何固定菜单探针上仍使用完整 $t$。直接复用 $\mathsf F$(42.20)–(42.21) 的已知乘法恒等式：

$$
L=K_\sigma(R_+,S_+)-K_\sigma(R_-,S_-),\qquad
|\phi(K_\sigma(U,V))|\le\sqrt{B_\phi(U,V)}.
\tag{2.17}
$$

故每个菜单的真实差额 $\Delta_{v}(x,\xi)\le0$；任意允许报告至多为 $\nu$，第二项成立。

对于同一个菜单探针，将 $g=v+s$ 与 $g=v$ 作数学比较，$R_\pm$ 不变，$S_\pm$ 分别改变 $\pm s$，$L$ 改变 $-2\tau\circ s$，范数至多 $2M\|s\|$。在实内积 $\operatorname{Re}\langle\cdot,\cdot\rangle$ 下，

$$
\sqrt{B_{\phi_\xi}(R,S)}
=\|\Theta(R)\xi\|\,
\operatorname{dist}_{\mathbb R}\bigl(\Theta(\Sigma S\Sigma)\xi,
\mathbb R\Theta(R)\xi\bigr).
\tag{2.18}
$$

这里 $R=\Sigma R\Sigma$，$S$ 在 $\Sigma$ 与补块之间没有连线；因此先取完整平方再压缩，仍等于相应支持矩阵的平方。$\Theta(R)\xi=0$ 时等式两边为零。到固定实直线的距离是 $1$-Lipschitz，故改变 $S$ 为 $S\pm s$ 时，面积变化至多 $\|R\|\|s\|\le10M\|s\|$。结合 (2.17) 得

$$
\Delta_{v+s}(x,\xi)\le22M\|s\|.
\tag{2.19}
$$

因此 $\eta\ge22M\rho+\nu$ 保证每个允许报告均通过，第三项得证。这里比较标准行只用于证明通过界，真实端口没有查询替代输出。∎

## 3. 精度、资源与零通道边界

**推论 3.1（指定范数精度的有限保证）。** 在定理 2.1 下，给定目标 $\varepsilon>0$。若

$$
2\nu<\frac{\varepsilon^2}{\sqrt{10}},\qquad
\eta=\nu,\qquad
\delta=\frac{\varepsilon^2/\sqrt{10}-2\nu}{55M},
\tag{3.1}
$$

则接受蕴含 $\|s\|\le\varepsilon$，且 $s=0$ 对全部允许误差均通过。菜单查询数满足

$$
N\le2\,9^{2r}
\left(1+\frac{220M^2}{\varepsilon^2/\sqrt{10}-2\nu}\right)^D.
\tag{3.2}
$$

**证明。** (3.1) 使 $\delta>0$，且 $\eta+\nu+55M\delta=\varepsilon^2/\sqrt{10}$。代入 (2.2)–(2.3)，并用 $\eta\ge\nu$ 即得。特别地 $\nu=0$ 时仍取正网格而得到任意给定的正精度；这不把有限菜单升级为精确零认证。∎

**命题 3.2（$M=0$ 与资源含义）。** 若 $M=0$，精确 (1.4) 已蕴含 $s=0$，不需要任何查询。对 $M>0$，定理 2.1 的有限菜单只需同一差额端口，且对外部背景 $b$ 没有资源依赖；该定理不提供有限位菜单生成器或物理重复实验次数。

**证明。** $M=0$ 给 $T=0$；(2.4) 对所有角状态给 $s_p=s_q=0$，即使 $b\ne0$ 也成立。$M>0$ 时，菜单的坐标、根和网中心在未知 $g$ 前固定，逐项取得报告，至多执行 (2.2) 次。选定有限网的数学存在性不自动给其精确实数编码或计算成本；(1.7) 的误差已包含一次差额形成所需的全部读数误差。若只能分别取得矩并在外部计算平方根，必须另证矩误差到 (1.7) 的传播，不能仍将它们无条件计为一次差额调用。$b$ 无界而不进入误差常数的原因是 (1.1) 的分离形状及指定支持读取，不是对一般环境耦合的控制。∎

## 4. 更强平方矩访问下的两标量迹证书

**定理 4.1（原零探针平方标签的迹残差）。** 保持 (1.1)、(1.2)、(1.5)，但本条恒等式本身不需要 (1.4) 或已知 $M$。另给能够直接读取两个原平方标签的端口：在 $x=0$，对固定数学正泛函

$$
\phi_0(y)=\frac{\operatorname{Tr}(\Theta(\Sigma y\Sigma))}{r}
\tag{4.1}
$$

取得

$$
\mu=\phi_0(S_+(0)^2),\qquad
\omega=\phi_0(R_+(0)^2).
\tag{4.2}
$$

则对同一固定 $g=v+s$，完整原标签满足

$$
\boxed{\ E:=\mu-\frac59\omega
=\frac{\operatorname{Tr}(\Theta(s^2))}{r},\qquad
0\le E\le\|s\|^2\le rE.\ }
\tag{4.3}
$$

特别地，准确两矩同时供应时，$E=0$ 当且仅当 $s=0$，而任意外部 $b$ 均保留。

**证明。** $x=0$ 给 $R_+(0)=-k=-3\tau/2$、$S_+(0)=\tau+b+v+s$。在支持角内，$\tau,v$ 为非对角块，$s$ 为对角块；由 $T^2=(T^*)^2=0$，

$$
v^2=\tfrac14\tau^2,\qquad \tau\circ v=0,
\qquad \operatorname{Tr}(\Theta(\tau s))=
\operatorname{Tr}(\Theta(vs))=0.
\tag{4.4}
$$

背景 $b$ 与这三个支持元素的乘积为零，且 $\Sigma b^2\Sigma=0$。因此对完整平方先乘后读，

$$
\begin{aligned}
r\mu&=\tfrac54\operatorname{Tr}(\Theta(\tau^2))+
\operatorname{Tr}(\Theta(s^2)),\\
r\omega&=\tfrac94\operatorname{Tr}(\Theta(\tau^2)).
\end{aligned}
\tag{4.5}
$$

相减得到恒等式。$\Theta(s^2)$ 是正矩阵，其最大特征值为 $\|s\|^2$；其迹位于 $\|s\|^2$ 与 $r\|s\|^2$ 之间，故 (4.3) 成立。有限维的是支持角，不要求整个 $A$ 为矩阵代数。∎

**推论 4.2（两矩的有限精度与近零通过）。** 在定理 4.1 的额外端口下，若报告满足

$$
|\widehat\mu-\mu|\le\epsilon,\qquad
|\widehat\omega-\omega|\le\epsilon,\qquad
\widehat E=\widehat\mu-\tfrac59\widehat\omega,\qquad
\lambda=\tfrac{14}{9}\epsilon,
\tag{4.6}
$$

则

$$
|\widehat E-E|\le\lambda,\qquad
\widehat E\ge-\lambda,\qquad
\|s\|^2\le r(\widehat E+\lambda).
\tag{4.7}
$$

对任意阈值 $\theta\ge0$，以 $\widehat E\le\theta$ 为接受条件，有接受后的界 $\|s\|\le\sqrt{r(\theta+\lambda)}$。若 $\theta\ge\lambda$，零余量对全部允许误差通过；若 $\|s\|\le\rho$ 且 $\theta\ge\rho^2+\lambda$，则该近零余量对全部允许误差通过。取 $\theta=\lambda$ 时，保证 $\|s\|\le\varepsilon$ 的充分条件为

$$
\epsilon\le\frac{9\varepsilon^2}{28r}.
\tag{4.8}
$$

**证明。** (4.6) 的三角不等式给 $|\widehat E-E|\le(1+5/9)\epsilon=\lambda$。由 $E\ge0$ 和 (4.3) 得 (4.7)。接受时用 $E\le\theta+\lambda$；近零时则用 $E\le\|s\|^2\le\rho^2$。在 $s=0$ 时 $\widehat E\in[-\lambda,\lambda]$，故阈值 $\lambda$ 容许全部误差。最后 $r(2\lambda)=28r\epsilon/9$，得到 (4.8)。如果出现 $\widehat E<-\lambda$，它与本条模型和误差合同不相容，不是负的真实平方残差。∎

**定义 4.3（访问比较的准确范围）。** (4.2) 供应差额端口 (1.7) 未提供的两项分别报告的矩；只得到一个带符号差额不能据其定义拆回这两矩。因而定理 4.1 是更强的原标签访问合同下的替代证书，不是定理 2.1 所需菜单的下界反例，也不声称两标量的仪器成本总是更低。若 $T$ 的精确坐标已知，$\omega$ 还可由 (4.5) 算出；两次标量读取是充分上界，不是最小性断言。

若只提供固定正交基的纯态平方矩端口，则 (4.1) 是 $r$ 个基向量读取的平均。分别取得两矩可用 $2r$ 次标量报告、涉及至多 $r$ 个准备位置；若每个基向量上的每个矩误差至多 $\epsilon$，平均后各矩误差仍至多 $\epsilon$。直接供应混合迹端口是另一访问合同，不能由数学混合自动推出。普通信息完备层析与算子框架是成熟的更丰富访问比较，见 D’Ariano–Perinotti–Sacchi，[*Informationally complete measurements and groups representation*，arXiv:quant-ph/0310013v2，§2，式 (3)–(8)](https://arxiv.org/html/quant-ph/0310013v2)；不将其框架重构另列为本卷新定理，也不由它为原 PB 补付任何物理读口。

## 5. 正误差精确零认证的停止障碍与读取方向边界

**命题 5.1（精确全正 P2 内的有限停止障碍）。** 在同一个 $M_2(\mathbb C)$ 中固定

$$
\begin{gathered}
p=E_{11},\quad q=E_{22},\quad P=\Sigma=1,\quad
c=\operatorname{diag}(1,2),\quad t=E_{12}+E_{21},\quad b=0,\\
s_\alpha=\alpha\operatorname{diag}(1,-2),\qquad
g_\alpha=K_\sigma(c,t)+s_\alpha,\qquad
\alpha\in[-2\sqrt2/3,2\sqrt2/3].
\end{gathered}
\tag{5.1}
$$

所有这些固定输出均满足准确 (1.4)，两种 $\sigma$、全部原质量均包括在内。设确定性协议可根据既有报告选择标量查询 $Q$ 及正容差 $\nu_Q>0$，其真实回复 $f_Q(\alpha)$ 对每个固定 $Q$ 在 $\alpha=0$ 连续。允许报告满足 $|y-f_Q(\alpha)|\le\nu_Q$，查询与精度选择不直接访问未知 $\alpha$。

若该协议在 $\alpha=0$ 的一份有限报告历史 $y_1,\ldots,y_n$ 上停止并宣告 $s=0$，且沿该历史选定的查询、容差满足

$$
|y_j-f_{Q_j}(0)|<\nu_{Q_j}\qquad(1\le j\le n),
\tag{5.2}
$$

则存在非零允许 $\alpha$，在同一允许历史上得到同一精确零宣告。因此，不存在既对全部允许来源和误差可靠，又在零余量的每份允许历史上有限停止并成功认证精确零的此类协议。此结论也适用于非自适应有限菜单。

**证明。** $\mathsf F$ 定理 34.1 直接取其参数 $(a,b,v,r)=(1,2,1,\alpha)$，给出区间 (5.1) 的精确全正 P2；不重证其全复参数结论。其余量范数为 $\|s_\alpha\|=2|\alpha|$。

固定 (5.2) 的整段历史。此时确定性选择所给的 $Q_j,\nu_{Q_j}$ 均已固定，即使选择规则本身关于报告不连续也无妨。令

$$
m_j=\nu_{Q_j}-|y_j-f_{Q_j}(0)|>0.
$$

连续性和查询数有限，给某个 $h>0$，使全部 $|\alpha|<h$ 均满足 $|f_{Q_j}(\alpha)-f_{Q_j}(0)|<m_j$。选

$$
0<|\alpha|<\min\{h,2\sqrt2/3\}.
$$

则每个 $y_j$ 对该同一 $\alpha$ 仍是允许报告。按历史长度归纳，第一查询相同，收到相同报告后下一查询及精度相同，直到同一停止点；协议于是错误地宣告 $s_\alpha=0$。零次查询时任意非零允许 $\alpha$ 已给同一结论。

如果要求在零余量的全部允许历史上成功，考虑每步准确回复 $y_j=f_{Q_j}(0)$ 的历史。若有限成功，则因每个容差严格为正，它满足 (5.2)，与可靠性冲突。这不要求统一停止预算。

对原差额查询，固定 $x,\xi$ 后，$L$ 随 $\alpha$ 仿射，$S_\pm$ 随 $\alpha$ 仿射，所有平方矩及 Gram 连续，非负平方根和绝对值也连续。因此 (1.7) 满足本条的连续性前件；(4.2) 的矩查询同样满足。协议在有限次中可选择任意小但严格正的容差，证明依然适用。∎

**命题 5.2（严格余量条件与排除项）。** 命题 5.1 不排除闭误差边界上一份特殊有限历史恰好认证零，也不排除零误差、非连续相等读口或预先正分离的来源类。

**证明。** 在 (5.1) 上，固定正读取 $f(\alpha)=\phi_{e_1}(g_\alpha)=\alpha$。用同一个正容差 $\nu$ 重复读取两次；报告 $(\nu,-\nu)$ 同时要求

$$
\alpha\in[0,2\nu]\cap[-2\nu,0]=\{0\}.
\tag{5.3}
$$

所以该边界历史确能排除全部非零 $\alpha$，但两次误差都饱和，不满足 (5.2)，也不保证零来源的其他历史成功。

零误差下，准确读取 $f(\alpha)=\alpha$ 可直接判定 $\alpha=0$；若允许不连续查询 $f(\alpha)=\mathbf1_{\{\alpha\ne0\}}$，则任何小于 $1/2$ 的误差都允许用阈值 $1/2$ 区分。若预先保证 $\alpha=0$ 或 $|\alpha|\ge a_*>0$，则读取 $f(\alpha)=\alpha$ 且误差 $\nu<a_*/2$，可用 $|y|<a_*/2$ 认证零。这三种访问或来源条件均未满足命题 5.1 的全部前件。该障碍不是完整 $\mathsf H_A(D)$ 的反模型：非零 $\alpha$ 只有固定 P2 证书，$\mathsf F$ 定理 41.2 已保证某份原 PB 见证失败。∎

**命题 5.3（对角读取的单侧 PB 通过盲区）。** 取 (5.1) 中任一非零允许 $\alpha$。对任意实对角候选 $z=z_pp+z_qq$、任意 $d=d_\pm$，使用 (2.7) 的探针 $x_d(z)$，但仅允许密度矩阵为 $\lambda p+\mu q$、$\lambda,\mu\ge0$ 的正读取。则这些读取上的完整原 PB 均成立，尽管 $s_\alpha\ne0$。即使两根及全部此类候选都查询，“所有差额至多为零”这一通过条件也不能推出 $s=0$。

**证明。** 仍有 (2.10)–(2.11)，其中 $e=s_\alpha-z$ 对角，而 $\tau=t$ 非对角。由 $\mathsf F$(41.11) 的 $\tau\circ v=0$，得到

$$
L(x_d(z))=-2(d+d^{-1})Z_d(z)\circ\tau-2\tau\circ e.
\tag{5.4}
$$

该矩阵完全非对角，所以每份所列正读取的 $\phi(L)=0$；两项 Gram 均非负，原 PB 随即成立。读取质量可为任意有限非负数，包含零。此处并未将候选 $z$ 替代真实 $s_\alpha$。

因此以 (2.15) 恢复 $L$ 范数的路线需要跨 $p,q$ 的方向；只在每个块内部取再多状态，也不是非对角 $L$ 的范数化网。本条不声称完整差额数值对 $\alpha$ 恒定；负差额本身仍可能携带信息，其他判定规则不由这个通过反例排除。另一方面，定理 4.1 在该同一例中给 $E=5\alpha^2/2>0$，可以由两个基向量的平方矩平均读出；这是对两项原平方矩的分别访问。∎

## 6. 复用关系、来源全文与保留的数学边界

**定义 6.1（推导归属及适用范围）。** 定理 2.1 的新增连接是 (2.10)–(2.16)：对由已知界形成的候选网，保留真实未知输出的近比例标签，以线性 $M\delta$ 误差把有限差额报告转回两份余量依赖见证的全部质量预算，再调用 $\mathsf F$ 定理 43.1。有限网、二次型范数化、距离函数的 Lipschitz 性与状态范数公式是成熟工具，不单列为新的一般结论。定理 4.1 的原零探针迹消去和第 5 节在精确 P2 家族上的访问边界，与该连接共同构成本卷的 $\texttt{repo-derived}$ 推导；不主张文献优先权或穷尽检索。

仓内普通有限网与取得问题的比较已有 [FIB 自校准关系数学 III](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md) §§18–19：其中的来源、单轨迹和不可复制规则按其自身合同解释，不直接供应本卷同输出差额端口。上述 Vershynin 两引理仅支撑覆盖和范数化，D’Ariano–Perinotti–Sacchi §2 仅支撑信息完备框架比较；都不承担 PB 的原标签估计、实际准备或完整响应重构。

[区间原响应与变投影运输卷](AURIC_INTERVAL_ORIGINAL_RESPONSE_AND_VARIABLE_PROJECTION_TRANSPORT.md) §9 的演员轴平移障碍保留真环境连线及 $t_0+\lambda c$ 的对角输入；它不满足 (1.1) 的分离背景形状，不能被本卷零探针迹式或菜单结论覆盖。

若这些固定数据来自完整原响应，则原 $\mathsf H_A(D)$ 仍按 $\mathsf F$ §41.1 全文保留：同一 $\Omega/\mathrm{native}$、原域、准确锥、分离且决定锥的原评价族、单位、范数、任意总映射 $D$、全部有向 A1/P2 和两种次序、A2 相加三表的全部排列与指定零方向、同一有理 A3，以及每个实际三元组和全部嵌套调用的完整 PB。没有新增 $D$ 的线性、连续、可测、协变、压缩自然性或延拓。固定输入的精确 (1.4) 是保留前件；有限近似菜单只认证该一份输出的范数，不验证完整 $\mathsf H_A(D)$。

**定义 6.2（完全相同的递归来源）。** 物理来源准确为 $\mathsf F$ 定义 41.4 的同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$，其中 $S$ 仍指原对称响应。沿

$$
41.4\Rightarrow40.1\Rightarrow36.1\Rightarrow32.3\Rightarrow\S27.1
\Rightarrow26.3\Rightarrow22.3\Rightarrow18.2
\Rightarrow\{10.2,15.2,\mathrm{AH}28.1,64.2,75.1\}
\Rightarrow\mathrm{SQ}47.1\text{--}47.13
\tag{6.1}
$$

的全文身份关系，将每份定义、合同、公式、量词及逐项递归纳入、逐层固定版本的全部上游全文逐句、逐公式、逐量词同时合取。该链及下述说明都不替代被纳入的全文。

AH 直接身份仍为 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`，W/CC/PT 为 `3b10aed60f60e4901bae6cf2e160bf439d642e64`；SQ 自身两层主源 `dcaebc0b9ca5a3a463fd8cfd161d38967df28668`、`0aa11dbc3dc337d667b98900673e07d67b99bf46`，OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`，AH22.1 的 `2addd6f369b7387226c2b0cc984623dd3efe40a1`，AH12.1 的 `39a0505470ea889dd9d4301ad60cd9506a5e8b58`，AH42.1 内的 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7` 及 R5 原层身份均原样保留，不用直接引用压平内层版本。

同源对象、准备、事件、设备、程序、原比较权、共同全词 $K/J$、parent、ready、合法控制、旗标、原中心、经典及不等维块、无轴对象、中间切口和全部模式网络仍按原全文；未定义请求不补零。原事件绑定的完整 Born 菜单、零／不等／次归一／非正常质量、真实条件化、同一共同相关来源、忠实同向交换腿、共同生成、评价分离及重数均保留。数学向量态、有限坐标或迹不生产这些条件。

typed CP、箭头下降、整台递归同源参考、真支持、支持内补、交织夹界、所需全部有限深度和每个正精度仍须原来源。完整仪器、TP、Kraus、更新及 Lüders 保持完整 typed 菜单、单位分区、接受端、校准、表示与收敛条件，量化整个环境、全部成功／失败／细记录／port／post-port 输出及每份完整输出的每个仍合法未来。停止、拒绝、销毁、泄漏、合法顺序、自适应与并行历史、真正分组遗忘、逆向真实 Return、含活动 ready 与 producer 的完整 CountRead 均不由本卷有限菜单替代。

只有严格正的实际质量可归一；正常性、指定前对偶、可数可加、无限菜单和收敛保持原扩展要求。实际连续可逆动力学及实际逆、原物理钟和单位、适用酉实现、生成元域、Hamiltonian 能量解释、作用量及共同正物理 $\hbar$ 均不由正矩阵证书产生。本卷的 (1.7)、(4.2) 是两种明确额外读数合同，须另证怎样接回同一来源；数学上选出查询并未完成实际取得。

**定义 6.3（未支付的全域关系）。** 本卷只覆盖 (1.1) 的块余量、无对角输入和分离背景。一般 $ptp\ne0$、$qtq\ne0$ 或 $(1-\Sigma)t\Sigma\ne0$ 不在定理 2.1、4.1 的范围。原一般混合输入中 $\mathsf F$(41.28) 的两份完整缺陷相等 $E_+=E_-$ 仍须另证；既有差额 $E_+-E_-=2cs$ 未被改成相等公理。增长有限分割的 $N\omega_{M,\lambda_*}(\varepsilon)^2\to0$、无限谱演员、一般环境运输、任意输入拼接和完整奇数阶段 UHF 全域均未由有限认证支付。精确全正 P2 家族只是固定接口中的来源，不是完整响应反模型。

## 追加锚（本行以下为增补区）

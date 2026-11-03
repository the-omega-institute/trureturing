# AURIC：$F[13]$ 的关系语义

## 量子三轴与递归相容性

定义、定理与纸面证明　 v42.0

2026 年 10 月 31 日　 Asia/Singapore

> 文稿元数据：PDF 标题为「AURIC：F[13] 的关系语义、量子三轴与递归相容性」；作者标识为 AURIC research continuation；主题为 Relational fibers, five-mode couplings, two reflections, task sufficiency and recursive stability。原页眉为「AURIC：关系约束、量子三轴与递归相容性」及「v42 / 2026-10-31」。

> 版本与来源说明：下文保留作者的版本叙述；固定提交、时间、相对 v41 的两路径差异、定向源码核对及未运行数学程序等历史陈述均归于作者，不表示本 Markdown 转写独立认证了这些历史行为。本文的纸面论证不构成 Lean、原生操作、实验或托管 MathJax 认证。

## 摘要

本文把“$F[13]$ 是约束 $F[1],F[3]$ 的关系”作为统一定义的出发点。
关系对象、关系的统计读数和指定关系定律分别承担代数结构、来源信息和可行域约束。
在原五模式中，联合事件为 $\xi\eta$；固定三个占位均值后，唯一遗漏的线性自由度是其概率
$\kappa$。本文重述项目的关系纤维、条件行列式、最大熵补全与任务误差，
进一步给出对数赔率的尖锐稳定界及内部图消元后的关系乘法律。
在声明的非交换接口中，两个二值反射满足 $AB=S+iC$，
其固定关系扇区导出逻辑 qubit；关系 Gram 正性给精确完成圆盘，
固定夹角给三轴椭球及尖锐重构条件数。
递归方面，树上的一致耦合在 Markov 关系下可归一化拼接，并满足质量加权的 TV 稳定界；
三角循环还须满足全局相容约束，其最小修复距离可精确计算。
最后以任务效果空间统一这些结果，并接到项目最新的原事件预测商与同步块不可见核。
本文使用纸面证明；源码核对、文档编译和渲染不构成数学数值或形式化验证。

<a id="section-1"></a>

## 1. 问题、版本与统一立场

本轮固定项目默认分支 `dev` 的提交

`2fe4175f9a8a88d3a2d4fa5deb918b67bc3bf890`，

 时间为 2026-10-31 15:29:21（新加坡）。
相对 v41 的 `79783aa49bcd`，
完整理论子树只有两条变化：新增共同活动度 hard-core 文稿，
以及原生终端认证卷追加 §§12–17。金字塔基础、关联和行列式文稿保持不变。
本轮使用前者的明确 Gibbs 定义、后者的任务相关预测边界，并继续消费既有关系公式。
定向源码阅读不等于全仓数学认证。[[1](#ref-head), [2](#ref-foundation), [3](#ref-correlation), [4](#ref-determinant), [7](#ref-hardcore), [8](#ref-terminal)]

<a id="statement-1-1"></a>

#### 定义 1.1（内部本体与观察接口）

固定单一整体 $(\mathcal A,\omega)$，其中 $\mathcal A$ 为复含单位观测代数，
$\omega$ 是正归一泛函：

$$
\omega(T^\dagger T)\ge0,\qquad \omega(I)=1.
$$

程序、记录、观察者、参考框架与可用控制均为整体内部结构。
有限接口是明确指定的子代数、效果空间及可用操作。
全态域上的重构定理研究这一接口的数学响应，不意味着任意数学态已经能够实际制备。

> 输入限定（定义 1.1）：这里另行供应伴随 $T\mapsto T^\dagger$，它是共轭线性、反转乘积的对合；$\omega$ 是复线性的正归一化态。复含单位代数本身不自动提供这个伴随结构。


对用户的直觉，本文采用以下积极定义：

$$
\boxed{\ F[13]\text{ 承担两个端点如何共同实现的关系角色。}\ }
$$

这句话允许三种精确层次：关系对象可以是联合事件或有序算符乘积；
关系读数是给定来源对它的响应；关系定律则把允许来源限制到一个子集。
于是关系既能约束两端，又能保存仅凭两端边缘不能恢复的信息。

归一化是单位元上的条件 $\omega(I)=1$。
原空模式 $F[\mathrm{null}]$ 的事件为 $e_N$，其概率是 $\omega(e_N)$；
它可以在某个参考标定中承担锚点角色，但 $e_N$ 与单位元分别承担事件和总质量。
本轮沿用 v41 的这个区分，集中研究关系如何进入预测与递归。

<a id="section-2"></a>

## 2. 关系作为相容纤维；最少需要多少关系读数

<a id="statement-2-1"></a>

#### 定义 2.1（相容纤维与关系细化）

设 $\mathscr S$ 是已声明的归一化正态族，当前数据映射为 $L_0$。
观察到 $q$ 后，相容来源集合为

$$
\mathscr C(q)=\{\rho\in\mathscr S:L_0(\rho)=q\}.
$$

给定关系读数 $R(\rho)=r$ 后，集合细化为

$$
\mathscr C(q,r)=\mathscr C(q)\cap R^{-1}(r).
$$

关系定律可以是 $\Phi(q,R(\rho))=0$ 或不等式；它选择相应子集。
目标 $f$ 可由这些数据唯一恢复，当且仅当 $f$ 在相容纤维上为常数。

最后一句是精确判据：若目标在纤维内有两个值，任何单值回答都会把其中至少一个来源回答错；
若恒定，就把该常数作为回答。因此“关系约束两端”不要求关系读数是两个边缘均值的函数。
它恰可用于区分具有相同边缘的不同共同实现。

<a id="thm-dimension"></a>

#### 定理 2.2（任务所需的最小关系维数）

设 $\mathcal B$ 为有限维复 $C^{\ast}$ 代数，使用忠实迹配对。
已有读口的实线性子空间为 $V_0\subseteq\operatorname{Herm}(\mathcal B)$，且 $I\in V_0$；
目标效果的实张成为 $\mathcal T$。在全部密度态上，
若可另外选择 Hermitian 线性读出 $R_1,\ldots,R_k$，
则所有目标可识别，当且仅当

$$
\mathcal T\subseteq V_0+\operatorname{span}_{\mathbb R}\{R_1,\ldots,R_k\}.
$$

允许解码函数非线性也不改变此条件。最少附加实读数为

$$
\boxed{\ k_{\min}=\dim(V_0+\mathcal T)-\dim V_0.\ }
$$

**证明。**

包含成立时，每个目标是已知读出的线性组合，因此可恢复。
反之令 $W=V_0+\operatorname{span}_{\mathbb R}\{R_j\}$，取 $F\in\mathcal T\setminus W$，
以迹内积将其正交分解为 $F=F_W+H$，其中 $H\ne0$、$H\perp W$。
因为 $I\in W$，$\operatorname{Tr} H=0$。记 $d=\operatorname{Tr} I$，足够小的 $\varepsilon>0$ 使

$$
\rho_\pm=I/d\pm\varepsilon H
$$

均正定且迹一。两态对 $W$ 的全部期望相同，而

$$
\operatorname{Tr}(F\rho_+)-\operatorname{Tr}(F\rho_-)=2\varepsilon\operatorname{Tr}(H^2)>0.
$$

故任何解码都失败。维数下界随包含关系得到；选商空间
$(V_0+\mathcal T)/V_0$ 的一组代表基即可达到。

∎

这是一项代数上的最少读数定理。指定原生菜单能否提供这些读数、所需调用和统计精度，
仍由菜单及实际来源决定。若态族预先受到更强非线性限制，最小数目也可改变。

<a id="section-3"></a>

## 3. 原五模式：$F[13]$ 如何成为端点关系

<a id="statement-3-1"></a>

#### 定义 3.1（五模式与端点占位）

逻辑标签按 $(N,1,2,3,13)$ 排列，对应项目数值标签 $(N,2,3,5,25)$。
令 $e_s$ 为互斥模式事件，令 $\xi,\eta,\zeta$ 分别记录位置 $1,3,2$ 的占位。
因此

$$
\xi=e_1+e_{13},\qquad \eta=e_3+e_{13},\qquad \zeta=e_2.
$$

端点读口在共同占位模式中也取一，而独占模式事件只在自身模式中取一。

<a id="prop-events"></a>

#### 命题 3.2（关系事件与单位元）

五模式上有

$$
\boxed{e_{13}=\xi\eta,}
$$

$$
\begin{aligned}
e_N&=1-\xi-\eta-\zeta+\xi\eta,&
e_1&=\xi-\xi\eta,\\
e_2&=\zeta,&e_3&=\eta-\xi\eta.
\end{aligned}
$$

特别地 $\sum_s e_s=1$，而 $e_1e_3=0$。

**证明。**

端点同时占位只在模式 $13$ 发生。其余式从端点事件中减去共同事件，
再由全部事件穷尽得到。互斥模式的乘积为零。

∎

所以“$F[13]$ 是两端关系”可严格实现为 $e_{13}=\xi\eta$。
这里相乘的是两个端点占位函数，而不是两个互斥的独占模式事件。
项目行列式卷直接把 $\Delta$ 称为遗漏的联合关系，并说明共同占位不增加独立空间位置。
[[2](#ref-foundation), [4](#ref-determinant)]

<a id="thm-fiber"></a>

#### 定理 3.3（完整关系纤维；项目既有结果）

设

$$
X=\mathbb E\xi,\quad Y=\mathbb E\eta,\quad Z=\mathbb E\zeta,\quad
r=1-Z,\quad \kappa=\mathbb E(\xi\eta).
$$

则全部五模式概率恰为

$$
\boxed{
p_\kappa=(r-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa).
}
$$

可行三轴满足 $X,Y,Z\ge0,\ X+Z\le1,\ Y+Z\le1$；
在此域上关系参数的完整范围为

$$
\boxed{
L=\max(0,X+Y-r)\le\kappa\le U=\min(X,Y).
}
$$

纤维宽度为

$$
w=U-L=\min\{X,Y,r-X,r-Y\}.
$$

**证明。**

三个读出给 $p_1=X-\kappa,p_3=Y-\kappa,p_2=Z$；
总和一给 $p_N=r-X-Y+\kappa$。五项非负恰为区间条件。
区间非空等价于上述三轴约束。宽度式按 $X\le Y$ 与 $X+Y\le r$
的四种组合相减即得。

∎

当 $w>0$，三个均值仍对应一整条联合概率纤维。
给出实际 $\kappa$ 才把这条纤维定位为一点。
这也是定理 [2.2](#thm-dimension) 的精确例子：

$$
\dim\operatorname{span}_{\mathbb R}\{1,\xi,\eta,\zeta\}=4,\qquad
\operatorname{span}_{\mathbb R}\{1,\xi,\eta,\zeta,\xi\eta\}=\mathbb R^5.
$$

完整五模式对角律恰缺一个线性关系坐标。
空间中的三轴金字塔是四维概率单纯形的投影；指定关系律可以选择三维截面。

<a id="thm-task"></a>

#### 定理 3.4（项目既有关系公式及其尖锐误差推论）

对五模式上的实目标 $f$，记

$$
J_f=f_{13}-f_1-f_3+f_N.
$$

则

$$
\begin{aligned}
\mathbb E_pf={}&f_N+(f_1-f_N)X+(f_3-f_N)Y\\
&+(f_2-f_N)Z+J_f\kappa.
\end{aligned}
$$

固定三轴后，目标可识别恰当且仅当 $J_fw=0$；其最小最坏绝对预测误差为

$$
\boxed{\ \inf_{\widehat m}\sup_{\kappa\in[L,U]}
|\widehat m-\mathbb E_{p_\kappa}f|=\frac{|J_f|w}{2}.\ }
$$

完整概率律满足

$$
\operatorname{TV}(p_\kappa,p_{\kappa'})=2|\kappa-\kappa'|,
\qquad
\inf_{\widehat p}\sup_{\kappa\in[L,U]}\operatorname{TV}(\widehat p,p_\kappa)=w.
$$

**证明。**

代入概率反解得期望式。目标值域是长度 $|J_f|w$ 的闭区间；
任一预测到至少一个端点的距离不小于半长度，中点达到。
两概率律之差是 $(\kappa-\kappa')(1,-1,0,-1,1)$，给 TV 公式。
两个端点概率的 TV 为 $2w$，三角不等式给最坏误差至少 $w$，
中点概率律达到。

∎

例如项目数量读出 $q=2\xi+5\eta+3\zeta$ 满足 $J_q=0$，
但 $J_{q^2}=20$。关系不影响该数量的均值，却影响二阶读出和完整回复律。
这将“关系是信息”变成一项可检验的任务判据。[[3](#ref-correlation), [2](#ref-foundation)]

<a id="section-4"></a>

## 4. 关系强度、补全规则与稳定坐标

<a id="statement-4-1"></a>

#### 定义 4.1（底面关系的三种坐标）

定义

$$
Q=\begin{pmatrix}p_N&p_3\\p_1&p_{13}\end{pmatrix},\qquad
\Delta=\det Q=r\kappa-XY.
$$

当四格全正时，定义赔率与对数赔率

$$
\eta_{\mathrm{odds}}=\frac{p_Np_{13}}{p_1p_3}>0,\qquad
\theta=\log\eta_{\mathrm{odds}}.
$$

这里 $\eta_{\mathrm{odds}}$ 与端点占位函数 $\eta$ 不同。

<a id="thm-entropy"></a>

#### 定理 4.2（条件关系、最大熵与遗漏损失；项目既有结果）

当 $r>0$，

$$
\operatorname{Cov}(\xi,\eta\mid\zeta=0)=\frac{\Delta}{r^2}.
$$

底面条件独立等价于 $\Delta=0$，唯一补全为 $\kappa^\star=XY/r$。
固定三轴后，这个 $p^\star$ 是整个闭纤维的唯一最大熵律，且

$$
\boxed{
H(p^\star)-H(p)=D_2(p\Vert p^\star)
=r\,I_p(\xi:\eta\mid\zeta=0),
}
$$

$$
\boxed{\operatorname{TV}(p,p^\star)=\frac{2|\Delta|}{r}.}
$$

$H,D_2$ 使用二为底的对数；零概率按连续惯例处理。

**证明。**

$Q/r$ 的两个边缘均值为 $X/r,Y/r$，联合概率为 $\kappa/r$；
协方差相减给第一式。二元乘积表在固定边缘下唯一，故独立等价于 $\Delta=0$。
令 $q=Q/r$，其行列边缘为 $u,v$。按中位事件分组，

$$
H(p)=h_2(Z)+rH(q),\qquad
H(p^\star)=h_2(Z)+r[H(u)+H(v)].
$$

若 $q_{ij}>0$，则 $u_iv_j>0$；因此支撑包含，展开有限和得到
$D_2(q\Vert u\otimes v)=H(u)+H(v)-H(q)$，
以及 $D_2(p\Vert p^\star)=rD_2(q\Vert u\otimes v)$。
相对熵非负且只在两律相同取零，给唯一最大值。
最后两律的 $\kappa$ 差为 $\Delta/r$，应用定理 [3.4](#thm-task)。

∎

$r=0$ 时只有中位顶点 $p_2=1$，不定义底面条件律。
此外，条件独立仍可有无条件关联：

$$
\operatorname{Cov}(\xi,\eta)=\frac{\Delta+XYZ}{r}.
$$

最大熵补全是一条明示的关系选择；实际来源是否满足它，由来源本身决定。
它一般也不同于定理 [3.4](#thm-task) 的中点 minimax 选择。[[2](#ref-foundation), [4](#ref-determinant)]

<a id="thm-odds"></a>

#### 定理 4.3（给定关系强度唯一补全及尖锐稳定界）

固定 $r>0$ 和 $0<X,Y<r$。在开纤维 $\kappa\in(L,U)$ 上，
$\theta=\log\eta_{\mathrm{odds}}$ 是从该区间到 $\mathbb R$ 的严格增双射。
记相应五模式律为 $p_\theta$，则

$$
\boxed{
\frac{d\kappa}{d\theta}
=\left(\frac1{p_N}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}\right)^{-1}
\le\frac r{16}.
}
$$

从而

$$
\boxed{
\operatorname{TV}(p_\theta,p_{\theta'})
\le\min\left\{2w,\frac r8|\theta-\theta'|\right\}.
}
$$

常数 $r/8$ 作为所有此类固定边缘的统一 Lipschitz 常数是尖锐的。
对底面条件律，同样有 $\operatorname{TV}(Q_\theta/r,Q_{\theta'}/r)\le|\theta-\theta'|/8$。

**证明。**

对数展开并求导得

$$
\frac{d\theta}{d\kappa}
=\frac1{r-X-Y+\kappa}+\frac1\kappa
+\frac1{X-\kappa}+\frac1{Y-\kappa}>0.
$$

当 $\kappa\downarrow L$，分子中的至少一个概率趋零，分母仍正，故赔率趋零；
当 $\kappa\uparrow U$，分母趋零而分子仍正，故赔率趋无穷。
由连续严格单调得到双射。
四格质量之和为 $r$，Cauchy 不等式给
$(\sum_s p_s)(\sum_s1/p_s)\ge16$，这里求和只在底面四格。
求逆、积分并使用 $\operatorname{TV}=2|\Delta\kappa|$ 即得界；
全纤维直径为 $2w$，给另一截断。
等号导数在四格全为 $r/4$ 时达到，即 $X=Y=r/2,\theta=0$。
取该点任意小的关系参数变化，TV 与 $|\Delta\theta|$ 之比趋 $r/8$，
故统一常数不能降低。底面条件化将 TV 除以 $r$。

∎

这条定理具体回答“关系是否能约束两端”：在给定三轴的内部纤维上，
指定任意有限关系强度 $\theta$ 都唯一选出联合律。
它还说明，归一化与关系规则共同完成的是一项*带条件的重构*。
若边缘落在退化边界，纤维可能本来只有一点；若出现零格，不使用有限对数赔率。

<a id="statement-4-4"></a>

#### 命题 4.4（有限精度关系证书）

固定三轴、$r>0$。若另知 $d_-\le\Delta\le d_+$，则相容纤维准确变为

$$
L'=\max\left\{L,\frac{XY+d_-}{r}\right\},
\qquad
U'=\min\left\{U,\frac{XY+d_+}{r}\right\}.
$$

有相容来源恰当且仅当 $L'\le U'$；此时目标的最小最坏误差为 $|J_f|(U'-L')/2$。
特别地若证书与来源相容，且 $|\Delta-\widehat\Delta|\le\varepsilon$，则

$$
\operatorname{risk}(f)\le
|J_f|\min\left\{\frac w2,\frac{\varepsilon}{r}\right\}
\le |J_f|\min\left\{\frac r4,\frac{\varepsilon}{r}\right\}.
$$

**证明。**

用 $\Delta=r\kappa-XY$ 将关系区间拉回并与原区间相交。
应用定理 [3.4](#thm-task)，再用 $w\le r/2$。

∎

因此无条件质量很小的关系，其绝对误差可以小；相应条件关系却未必精确。
选择关系坐标时应同时说明固定的边缘、质量与所预测的任务。

<a id="section-5"></a>

## 5. 内部结构如何生成关系；递归为什么像级数

项目新 hard-core 文稿定义有限简单图 $G$ 上的实际共同活动度律

$$
\mathbb P(I)=\lambda^{|I|}/Z_G(\lambda),\qquad
Z_G(\lambda)=\sum_{I\ \mathrm{独立}}\lambda^{|I|},\quad\lambda>0.
$$

下述命题从这一明确前提继续推导，不把合法支撑本身当成 Gibbs 来源。[[7](#ref-hardcore)]

<a id="thm-elimination"></a>

#### 定理 5.1（内部消元产生有效端点关系）

设 $W=\{1,2,3\}$ 在 $G$ 中诱导三路径，$R=V(G)\setminus W$。
$N_R(S)$ 表示 $S$ 的 $R$ 内邻点，$Z_U$ 表示 $G[U]$ 的配分函数。
对任意合法局部模式 $S\subseteq W$，

$$
\boxed{p_S=\mathbb P(I\cap W=S)=
\lambda^{|S|}\frac{Z_{R\setminus N_R(S)}}{Z_G}.}
$$

局部五模式的关系赔率因而为

$$
\boxed{
\eta_{\mathrm{odds}}=
\frac{Z_R\,Z_{R\setminus(N_R(1)\cup N_R(3))}}
{Z_{R\setminus N_R(1)}\,Z_{R\setminus N_R(3)}}.
}
$$

**证明。**

固定 $I\cap W=S$ 后，内部剩余集合必须避开 $N_R(S)$；
它除此之外恰为 $G[R\setminus N_R(S)]$ 的任意独立集。
每项权重分解成 $\lambda^{|S|}\lambda^{|I\cap R|}$，求和给边缘式。
将空模式、两个端点单占位及共同占位的四式代入赔率，
$Z_G$ 和端点活动权相消，得到关系式。

∎

两个直接纸面例子揭示了关系的来源。若 $R$ 只有一个点，且同时邻接端点 $1,3$，
则 $\eta_{\mathrm{odds}}=1+\lambda>1$。
若 $R$ 为一条边 $a-b$，$a$ 邻接 $1$、$b$ 邻接 $3$，
则

$$
\eta_{\mathrm{odds}}=\frac{1+2\lambda}{(1+\lambda)^2}<1.
$$

> 例子输入限定：上述负关联例中 $N_R(1)=\{a\}$、$N_R(3)=\{b\}$，所列端点与内部点的关联完整，没有额外的交叉邻接。


所以没有直接端点边，也可由其余内部结构生成正或负的底面条件关联，即改变 $\Delta$ 的符号。
这些例子只使用指定图的有限权重表达式，没有引入外部环境或运行枚举。

<a id="cor-series"></a>

#### 推论 5.2（分离内部块的乘法律与对数级数）

若 $R$ 的诱导图分解为无交叉边的分量 $R_1,\ldots,R_m$，
则上式关系参数满足

$$
\eta_{\mathrm{odds}}=\prod_{j=1}^m\eta_j,\qquad
\theta=\sum_{j=1}^m\theta_j,\quad\theta_j=\log\eta_j,
$$

其中每个 $\eta_j$ 由定理 [5.1](#thm-elimination) 在 $R_j$ 上的四个配分函数比给出。
进一步，固定非退化 $r,X,Y$，以
$\theta_n=\sum_{j\le n}\theta_j$ 定义补全律 $p_{\theta_n}$。
若 $\sum_{j\ge1}|\theta_j|<\infty$，则存在有限 $\theta_\infty$，且

$$
\boxed{
\operatorname{TV}(p_{\theta_n},p_{\theta_\infty})
\le\frac r8\sum_{j>n}|\theta_j|.
}
$$

**证明。**

无交叉边的独立集与权重逐分量分解，故各个配分函数是分量配分函数的乘积，
四项比也逐分量相乘。对数将其转成加法。
绝对可和给 $\theta_n\to\theta_\infty$，应用定理 [4.3](#thm-odds) 得尾和界。

∎

这给“递归类似级数”一个确切实现：每一块提供有效耦合，归一化补全将耦合转换成概率律，
可和尾项控制完整概率误差。级数结论在固定边缘的补全族中成立；
若改变真实图时三轴也改变，需要再控制边缘变化。
它没有凭有限公式自动构造一个无限图的实际 Gibbs 来源。

<a id="section-6"></a>

## 6. 非交换关系：从共同事件到两个反射的乘积

<a id="statement-6-1"></a>

#### 定义 6.1（二值反射与有序关系）

在一个明确的复量子接口上，设

$$
A=A^\dagger,\quad B=B^\dagger,\quad A^2=B^2=I.
$$

定义

$$
U_{13}=AB,\qquad
S=\frac{AB+BA}{2},\qquad C=\frac{AB-BA}{2i}.
$$

$S$ 为对称关系部分，$C$ 为有向关系部分。
这是 $F[13]$ 关系角色的一种非交换实现；实际复关系读数为 $\omega(AB)$。

原五模式与这个字典之间有一个准确代数桥。
在原占位接口取 $A=2\xi-I,\ B=2\eta-I$，它们对易，并且

$$
\boxed{e_{13}=\xi\eta=\frac{I+A+B+AB}{4}.}
$$

一般非交换时，若 $P=(I+A)/2,Q=(I+B)/2$，
仍有 $PQ=(I+A+B+S+iC)/4$，但 $PQ$ 一般不是正事件。
因而可把乘法关系统一起来，同时保留联合事件与有序量子相关的操作差别。

<a id="thm-two-reflections"></a>

#### 定理 6.2（关系酉性与精确预算）

上述二值反射满足

$$
\boxed{AB=S+iC,\qquad (AB)^\dagger AB=AB(AB)^\dagger=I,}
$$

$$
\boxed{[S,C]=0,\qquad S^2+C^2=I.}
$$

$S$ 与 $A,B$ 都对易；$C$ 与 $A,B$ 都反对易。对任何归一化态，

$$
\boxed{
|\omega(AB)|^2+\operatorname{Var}_\omega(S)+\operatorname{Var}_\omega(C)=1.
}
$$

**证明。**

$(AB)^\dagger=BA$，故两侧乘积均为 $I$。
$S,C$ 是同一酉算子及其伴随的实、虚部分，因此对易；
直接展开平方得 $S^2+C^2=I$。
例如 $AS=(B+ABA)/2=SA$，
$AC=(B-ABA)/(2i)=-CA$，对 $B$ 同理。
取平方恒等式的期望，并将二阶矩拆成均值平方与方差，即得最后一式。

∎

关系算符确实可以是酉的。其期望一般只满足 $|\omega(AB)|\le1$；
被压缩到一个均值时，其余预算表现为方差。
这为“关系保持酉性”提供了准确算符表达，而不会把酉性误写成任意均值模长一。

<a id="thm-sector"></a>

#### 定理 6.3（关系扇区导出二维因子）

有限维时按 $S$ 的谱值 $c\in[-1,1]$ 分解。
在 $S=cI$、$|c|<1$ 的非零扇区内，令

$$
s=\sqrt{1-c^2},\qquad D=\frac{B-cA}{s},\qquad N=\frac Cs.
$$

则

$$
A^2=D^2=N^2=I,\qquad AD=iN,\ DN=iA,\ NA=iD,
$$

$$
\boxed{B=cA+sD,\qquad AB=cI+isN.}
$$

该扇区酉等价于 $\mathbb C^2\otimes\mathbb C^m$，其中

$$
(A,D,N)=(\sigma_z,\sigma_x,\sigma_y)\otimes I_m.
$$

当 $c=\pm1$ 时，$C=0,\ B=\pm A$。

**证明。**

$S$ 与 $A,B$ 对易，故其谱空间保持不变；$S^2\le I$ 给谱范围。
在固定扇区，$\{A,B\}=2cI$，从而
$(B-cA)^2=(1-c^2)I$，且 $\{A,B-cA\}=0$。
因此 $D$ 是与 $A$ 反对易的反射。
$AD=(AB-cI)/s=iN$，其余乘法律随之成立。
$D$ 等距交换 $A$ 的两个本征空间，故两者同维；
在正空间选基 $e_j$，以 $De_j$ 为负空间基，就得到所述 Pauli 表示。
端点扇区上 $C^2=I-S^2=0$，所以 $C=0$；
再由 $(B\mp A)^2=0$ 得 $B=\pm A$。

∎

V24 已证明 $c=0$ 的反对易特例。此处把它接到一般关系角与谱分块。[[5](#ref-v24)]
归一化条件态的三个期望在固定非退化扇区上唯一确定*逻辑 qubit 约化态*；
重数因子、跨扇区相干及不同扇区的中心权重不能由这三个数整体恢复。
零质量扇区不定义条件态。端点扇区还可按 $A$ 的正负本征值分成经典表示。

<a id="section-7"></a>

## 7. 关系 Gram 正性、三轴椭球与稳定重构

<a id="thm-gram"></a>

#### 定理 7.1（关系的精确 Gram 约束与完成）

记 $a_0=\omega(A),b_0=\omega(B),z=\omega(AB)$，则

$$
G=\begin{pmatrix}
1&a_0&b_0\\
a_0&1&z\\
b_0&\bar z&1
\end{pmatrix}\succeq0,
\qquad
\boxed{|z-a_0b_0|^2\le(1-a_0^2)(1-b_0^2).}
$$

固定 $a_0,b_0\in[-1,1]$ 后，允许关系 $z$ 恰为上述闭圆盘，
其中充分性指存在某个二值量子接口实现数据。
每个这样的数据组都可由某个 qubit 接口及某个可能混合的 qubit 态实现。

**证明。**

对任意复系数 $\lambda_j$，$G$ 的二次型为

$$
\omega\bigl[(\lambda_0I+\lambda_1A+\lambda_2B)^\dagger
(\lambda_0I+\lambda_1A+\lambda_2B)\bigr]\ge0.
$$

对左上角一取 Schur 补，正性等价于

$$
\begin{pmatrix}
1-a_0^2&z-a_0b_0\\
\bar z-a_0b_0&1-b_0^2
\end{pmatrix}\succeq0,
$$

给圆盘约束。反向令 $c=\Re z$。
若 $|c|<1$，取 $s=\sqrt{1-c^2}$，
$A=\sigma_z,B=c\sigma_z+s\sigma_x$，以及

$$
\rho=\frac12\left[
I+a_0\sigma_z+\frac{b_0-ca_0}{s}\sigma_x
+\frac{\Im z}{s}\sigma_y\right].
$$

圆盘不等式整理后恰为该 Bloch 向量平方和不超过一，
故 $\rho$ 正且迹一；代入得到全部指定读数。
若 $c=\pm1$，$G$ 的正性先给 $|z|\le1$，于是 $z=\pm1$；
再由主子块的零方向得到 $b_0=\pm a_0$。
取 $B=\pm A$ 及 $\omega(A)=a_0$ 的 qubit 态即可。

∎

关系不等式也可写成

$$
(\omega(S)-a_0b_0)^2+\omega(C)^2
\le\operatorname{Var}(A)\operatorname{Var}(B).
$$

对称协方差和有向关系共享同一正性预算。
一般两端均值与复关系共含四个实数据；固定接口的算符关系可以进一步降维。
上述存在性证明没有改变已固定原生菜单的可达范围。

<a id="thm-ellipse"></a>

#### 定理 7.2（固定关系角的三轴完整状态域）

固定非平行 qubit 反射 $A=a\cdot\sigma,B=b\cdot\sigma$，
$|a|=|b|=1$，记 $c=a\cdot b,\ s=\sqrt{1-c^2}>0$，
$N=(a\times b)\cdot\sigma/s$。
按语义标签定义

$$
x_1=\omega(A),\qquad x_3=\omega(B),\qquad x_2=\omega(N).
$$

可实现三元组恰满足

$$
\boxed{
\frac{x_1^2-2cx_1x_3+x_3^2}{1-c^2}+x_2^2\le1.
}
$$

每个合法三元组唯一重构 qubit 态

$$
\boxed{
\rho=\frac12\left[
I+\frac{x_1-cx_3}{1-c^2}A
+\frac{x_3-cx_1}{1-c^2}B+x_2N\right].
}
$$

关系读数为 $z=c+isx_2$，且

$$
\det G=s^2(1-|r_{\mathrm B}|^2)=4s^2\det\rho.
$$

纯态恰在椭球边界；这里 $r_{\mathrm B}$ 是正交 Pauli 框架中的 Bloch 向量。

**证明。**

由定理 [6.3](#thm-sector)，正交框架 $(A,D,N)$ 中的坐标为

$$
r_{\mathrm B}=\left(x_1,\frac{x_3-cx_1}{s},x_2\right).
$$

迹一 Hermitian qubit 矩阵的本征值为 $(1\pm|r_{\mathrm B}|)/2$，
正性恰为 $|r_{\mathrm B}|\le1$。展开平方得到椭球式；
将 $D=(B-cA)/s$ 代回 Pauli 展开得到重构式。
将 $z=c+isx_2$ 代入 Gram 行列式得到
$s^2(1-|r_{\mathrm B}|^2)$；qubit 行列式为 $(1-|r_{\mathrm B}|^2)/4$。

∎

这给用户所问三轴平方和以关系依赖的精确度量。
当 $c=0$，它就是 $x_1^2+x_3^2+x_2^2\le1$；
一般情况下，正确二次式含交叉项与夹角分母。
两个均值和已知角度只决定

$$
|x_2|\le
\sqrt{1-\frac{x_1^2-2cx_1x_3+x_3^2}{1-c^2}}.
$$

即使已知纯态，通常仍有两个法向符号。
算符关系定义了第三方向；实际关系读数才确定该态沿第三方向的位置。

<a id="thm-conditioning"></a>

#### 定理 7.3（尖锐重构稳定性）

在定理 [7.2](#thm-ellipse) 的同一固定、已标定接口中，令

$$
m_\rho=(\operatorname{Tr}\rho A,\operatorname{Tr}\rho B,\operatorname{Tr}\rho N).
$$

任意两态满足

$$
\boxed{
\frac{\|m_\rho-m_\sigma\|_2}{\sqrt{1+|c|}}
\le\|\rho-\sigma\|_1
\le\frac{\|m_\rho-m_\sigma\|_2}{\sqrt{1-|c|}}.
}
$$

两端常数均尖锐。

**证明。**

读出矩阵 $L$ 的三行为 $a^{\mathsf T},b^{\mathsf T},n^{\mathsf T}$，其行 Gram 为

$$
LL^{\mathsf T}=
\begin{pmatrix}1&c&0\\c&1&0\\0&0&1\end{pmatrix},
$$

特征值是 $1+c,1-c,1$。
因此其最大、最小奇异值为 $\sqrt{1+|c|},\sqrt{1-|c|}$。
两个单 qubit 态之差的迹范数等于其 Bloch 向量之差的欧氏范数；
套用奇异值界得式。沿相应奇异向量取足够小的相反 Bloch 向量即达到常数。

∎

若 $|c|\to1$，重构病态；在退化端点，法向本身失去定义。
这与“没有发散”要求相接：稳定三轴接口需要非退化标定或明确的误差预算。
此界固定了 $c$，标定误差仍需另计。

<a id="statement-7-4"></a>

#### 命题 7.4（顺序测量与复关系）

先对 $A$ 作 Lüders 投影测量，再测 $B$，其二值结果乘积的均值为
$\omega(S)=\Re\omega(AB)$。
在固定 qubit 角度接口中，此值恒为 $c$。

**证明。**

置 $P_\alpha=(I+\alpha A)/2$，展开有

$$
\sum_{\alpha=\pm1}\alpha P_\alpha BP_\alpha
=\frac{AB+BA}{2}=S.
$$

取期望即得。

∎

因此完整复关系读数需要相应相干读口或法向测量；
普通顺序结果乘积只给对称部分。这是 V24 反对易特例的一般化。[[5](#ref-v24)]

<a id="section-8"></a>

## 8. 关系门与通用控制的准确连接

<a id="prop-su2"></a>

#### 命题 8.1（每个 qubit 特殊酉变换的两反射表示）

任意 $U\in SU(2)$ 可写为 $U=(a\cdot\sigma)(b\cdot\sigma)$，
其中 $a,b$ 为单位实向量。

**证明。**

写 $U=cI+is\,n\cdot\sigma$，$c^2+s^2=1,s\ge0$。
在 $s>0$ 时选单位 $a\perp n$，令
$b=ca+s(n\times a)$，则 $|b|=1,a\cdot b=c,a\times b=sn$。
Pauli 乘法律给所需乘积；$s=0$ 时取 $b=\pm a$。

∎

这是一项表示定理：若两反射能够随目标重新标定，所有 $SU(2)$ 变换都有这种形式。
对一对固定非平行反射，则有更具体的控制边界。

<a id="statement-8-2"></a>

#### 命题 8.2（固定双反射的闭包范围）

设固定 $U=AB$。则 $AUA=U^{-1}$，任意 $A,B$ 字均可化为
$U^k$ 或 $AU^k$。它们的共轭作用保留无向法线 $\{\pm N\}$，
因而这一固定双反射集合不能在 $PU(2)$ 中稠密。

**证明。**

$A(AB)A=BA=U^{-1}$，并且 $B=AU$。
将任意字中的 $A$ 用 $AU=U^{-1}A$ 移至左侧，再用 $A^2=I$ 约简，
得到两类正规形。$A,B$ 都将 $N$ 共轭为 $-N$；
任意字因此保持无向轴。该无向轴的稳定子是 $PU(2)$ 中的闭真子群，
因此这些门字的闭包不能是整个 $PU(2)$。

∎

该命题只针对这里固定的两个反射，不限制项目原生完整门菜单。
V37 §7.2 的逻辑黄金门 $K_P,K_Q$ 给出一个具体连接：
其第五次幂是反射，反射乘积先生成一维稠密旋转族；
保留原门 $K_P$ 的共轭作用后，得到第二个不共线方向，
交换子再补齐 $\mathfrak{su}(2)$，才建立该编码上的单 qubit 射影通用性。
因此项目的数学门表示和原生生成能力各有明确前提。[[6](#ref-v37)]
归一化、正性和酉性分别刻画总质量、状态可行性和可逆等距演化；
树上的随机核或条件归一化即使稳定，也不因此成为酉门。

<a id="section-9"></a>

## 9. 递归拼接：树上的建设性定理与误差

<a id="statement-9-1"></a>

#### 定义 9.1（共同节点上的一致耦合）

设 $T=(V,E)$ 是有限树，各节点有有限变量 $X_i$ 和边缘 $\mu_i$。
每条边 $ij$ 给归一化耦合 $\pi_{ij}$，
其两个边缘分别为 $\mu_i,\mu_j$。
这里的共享节点指同一个来源变量，边缘数值相同不能独自建立实际共同来源。

<a id="thm-tree"></a>

#### 定理 9.2（树关系的归一化拼接）

选根并将边朝外定向。在 $\mu_i(a)>0$ 时定义
$K_{j|i}(b|a)=\pi_{ij}(a,b)/\mu_i(a)$；
零质量行任取归一概率行。则

$$
\boxed{
P_T(x)=\mu_{\mathrm{root}}(x_{\mathrm{root}})
\prod_{i\to j}K_{j|i}(x_j|x_i)
}
$$

是归一化全局律，有所给全部节点与边边缘，
并在采用该树 Markov 因式分解的类中唯一。

**证明。**

从叶向根求和，各条件核行和一，因此全律归一。
若父节点边缘为 $\mu_i$，则
$P(X_i=a,X_j=b)=\mu_i(a)K_{j|i}(b|a)=\pi_{ij}(a,b)$；
从根递归得到全部边缘。正质量行由边律唯一决定；
零质量父状态不被到达，其任意核行不影响全律。

∎

指定 Markov 关系是唯一性的前提。
例如对三个二值变量，$P_\tau(a,b,c)=\frac18(1+\tau abc)$，
$|\tau|\le1$，所有单点与两点边缘相同，三元关系 $\mathbb E(ABC)=\tau$ 却不同。
因此低阶关系归一化以后，仍可能留下更高阶关系。

<a id="thm-tree-stability"></a>

#### 定理 9.3（树拼接的质量加权稳定界）

设两套一致边缘与耦合为 $(\mu_i,\pi_e)$、$(\nu_i,\chi_e)$，
所得 Markov 树律为 $P,Q$，且 $|V|\ge2$。则

$$
\boxed{
\operatorname{TV}(P,Q)\le
\min\left\{1,\
\sum_{e\in E}\operatorname{TV}(\pi_e,\chi_e)
+\sum_{i\in V}(\deg i-1)\operatorname{TV}(\mu_i,\nu_i)\right\}.
}
$$

若全部节点边缘相同，则

$$
\boxed{\operatorname{TV}(P,Q)\le\min\left\{1,\sum_{e\in E}\operatorname{TV}(\pi_e,\chi_e)\right\}.}
$$

后一界的边系数一是尖锐的。

**证明。**

选一条根边，以其联合律为初始分布，其余边向外。
从 $Q$ 出发，按叶到根顺序逐个将条件核 $L_{j|i}$ 换为 $K_{j|i}$，
最后替换根边。每一步祖先尚未改变，父节点边缘仍为 $\nu_i$。
替换这一核所产生的 TV 为
$\sum_a\nu_i(a)\operatorname{TV}(K_{j|i}(\cdot|a),L_{j|i}(\cdot|a))$；
其余归一化条件因子求和不会增加差异。
由

$$
\nu_iK-\nu_iL=(\mu_iK-\nu_iL)+(\nu_i-\mu_i)K
$$

和三角不等式，该步不超过
$\operatorname{TV}(\pi_{ij},\chi_{ij})+\operatorname{TV}(\mu_i,\nu_i)$。
各节点作父节点恰 $\deg i-1$ 次，根边替换贡献该边 TV。
将各步相加并使用 TV 不超过一，得式。
若节点边缘相同，第二项为零；
仅改变一条边时，边投影给反向 TV 下界，所以等号达到。

∎

这说明条件核里的小分母，在无条件全律中可由父节点质量抵消。
固定极低质量分支的条件预测仍可能敏感。
对越来越深的树，局部误差可和给统一预算；只要求每条边有同一个固定误差，
则累计预算仍可随边数增长。归一化本身不提供收敛速度。

<a id="section-10"></a>

## 10. 循环关系：局部正常为何仍需全局相容

<a id="thm-cycle"></a>

#### 定理 10.1（三角循环的完整约束与精确修复）

设 $A,B,C\in\{-1,1\}$，单点边缘均匀，
指定 $u=\mathbb E(AB),v=\mathbb E(BC),w=\mathbb E(CA)$。
各边分别合法等价于 $(u,v,w)\in[-1,1]^3$。
存在共同全局律，当且仅当

$$
\boxed{
1+u+v+w\ge0,\quad 1+u-v-w\ge0,\quad
1-u+v-w\ge0,\quad 1-u-v+w\ge0.
}
$$

记其可行四面体为 $\mathcal T$，并对
$\sigma\in\{\pm1\}^3,\sigma_1\sigma_2\sigma_3=1$ 定义
$h_\sigma(c)=1+\sigma\cdot c$，$c=(u,v,w)$。
对任意局部合法的 $c$，

$$
\boxed{
\operatorname{dist}_\infty(c,\mathcal T)
=\frac13\max_\sigma[-h_\sigma(c)]_+.
}
$$

**证明。**

点态恒有 $(AB)(BC)(CA)=1$，所以乘积三元组只落在

$$
(1,1,1),\quad(1,-1,-1),\quad(-1,1,-1),\quad(-1,-1,1).
$$

期望必在其凸包，四个面条件即为显示不等式。
反向取

$$
P(a,b,c)=\frac18(1+uab+vbc+wca).
$$

四个条件保证每项非负；求和得归一化、均匀边缘及指定关系。

若无面约束违反，距离为零。否则不同面的系数满足
$h_\sigma(c)+h_\tau(c)=2(1\pm c_j)\ge0$，所以至多一面为负。
写 $h_{\sigma_{\ast}}(c)=-3d<0$，取 $c'=c+d\sigma_{\ast}$。
则违反面变为零；其他 $\tau$ 满足
$\tau\cdot\sigma_{\ast}=-1$，且 $h_\tau(c)\ge3d$，故
$h_\tau(c')\ge2d$。于是 $c'\in\mathcal T$ 且距离为 $d$。
任意相容 $c''$ 必须修复违反量 $3d$，
而 $|\sigma_{\ast}\cdot(c''-c)|\le3\|c''-c\|_\infty$，
故距离至少 $d$。

∎

三条完美反相关边 $u=v=w=-1$ 各自归一化且共享均匀边缘，
却不能来自同一三变量来源；其最小逐边修复幅度为 $2/3$，
由 $(-1/3,-1/3,-1/3)$ 达到。
这把“关系约束关系”写成了全局可行域与尖锐误差证书。
若允许每条边误差至多 $\varepsilon$，
数据可以落入某个全局相容模型恰当且仅当上述距离不超过 $\varepsilon$。

即使边关系已经相容，高阶关系也未必唯一：

$$
P_\tau(a,b,c)=\frac18(1+uab+vbc+wca+\tau abc)
$$

仍给相同三条边，且其完整可行条件是
$|\tau|\le\min_\sigma h_\sigma(c)$。
每个乘积模式有互为全局反号的两个实现，
$abc$ 的符号在这两个实现中相反，故这个界直接来自非负性。

<a id="section-11"></a>

## 11. 最新项目进展：哪些关系需要保留由未来任务决定

<a id="statement-11-1"></a>

#### 定义 11.1（允许未来的效果空间）

在同一有限接口上，设合法后向操作为已给线性映射 $T_a^{\ast}$，
当前效果空间为含 $I$ 的 $V_0$。定义

$$
V_{n+1}=V_n+\sum_a T_a^{\ast}V_n.
$$

对于确定的归一化演化，$T_a^{\ast}I=I$；
若有条件分支，应将各实际分支及失败效果共同保留，或用相应的已给线性分支族。

<a id="statement-11-2"></a>

#### 命题 11.2（有限未来闭合）

$V_n$ 包含全部长度至多 $n$ 的允许未来效果。
若某一步 $V_{n+1}=V_n$，则已经包含所有有限字效果。
在有限维空间内，严格增长至多发生
$\dim\operatorname{Herm}(\mathcal B)-\dim V_0$ 次。

**证明。**

第一句按字长归纳。一次相等意味着每个 $T_a^{\ast}$ 都保持该空间，
所以任意后续组合仍在其中。每次严格增长至少增加一维，给停止界。

∎

把 $\mathcal T$ 取为这个闭合空间，定理 [2.2](#thm-dimension) 就回答：
为了全部允许未来，需要补充多少当前遗漏的关系。
单窗五模式中加上 $\xi\eta$ 已张成 $\mathbb R^5$；
项目实际跨窗来源若还含接缝、累计组成、真实历史或失败信息，
必须在那个实际来源上重新应用闭合条件。

<a id="native-terminal-instance"></a>

### 原生终端认证卷新增的具体实例

最新新增 §§12–17 只在实际记录质量 $m_i(a)>0$ 的分支上，
固定与续卷 III §151.5 相同的条件域：
已供应共同真实档案切口及联合核、整个块正锥上的归一正线性表示，
并另行供应完整标签的粗 Born 行。它随后只问原事件
$A=\{b_1=1\}$ 的全部原七地址未来，而非完整终端标签。
这里的粗 Born 前件针对条件未来行，没有假定一般记录质量 $m_i(a)$
已经等于平方范数权重 $t_i(a)$。[[8](#ref-terminal), [9](#ref-iii)]

该事件效果空间的原始实维为 $609$，加入单位元后为 $610$。
归一块态 $\sigma$ 的完整事件预测由下列坐标精确决定：

$$
\boxed{
\Gamma_0(\sigma)=(\sigma_{000}+\sigma_{010},\sigma_{100}),
\qquad
\Gamma_1(\sigma)=(\sigma_{001},\sigma_{101}).
}
$$

两个同型 $21$ 维块在固定规范下相加。
这两个坐标没有加入跨块相干，也没有把同步控制改成独立控制。

为什么归一化在这里实质起作用？成对原始空间为

$$
\mathcal W=\{(X,Y)\in\operatorname{Herm}_{21}\oplus\operatorname{Herm}_{13}:
5\operatorname{Tr} X=8\operatorname{Tr} Y\}.
$$

它的正交补为 $\mathbb R(5I_{21},-8I_{13})$。
若两归一块态的成对坐标差 $\Gamma_i(\sigma)-\Gamma_i(\tau)$
位于这个方向，则迹零要求
$(105-104)\lambda=0$，从而 $\lambda=0$。
因此加入单位元后，原始空间所缺的一维不留下新的归一预测歧义。
这里归一化作为约束方程参与恢复，空模式没有被重新定义为单位元。

在固定实际纯源面，允许的中心权重偏差 $d$ 满足总和零及未占据块不变。
只在记录零、两个 $21$ 维块都占据且规范射线相同时，全部事件未来的不可见核为

$$
K_u=\mathbb R(1,-1,0);
$$

其余情形为零。项目实际两步前缀 $78$ 正好实现该非零核：

$$
(t_{000},t_{010},t_{100})=(x^3,x^2,x^2),\qquad
x=(\sqrt5-1)/2.
$$

两个 $21$ 维块的规范纯射线相同，$13$ 维块仍有正质量。
相应不可见数学后验可写为

$$
\beta(z)=(x^3+\delta(z),\,x^2-\delta(z),\,x^2),\qquad
-x^3\le\delta(z)\le x^2,\qquad \int\delta\,d\nu=0.
$$

这些约束保留正性、归一化和正确粗均值。
给定切口支持非恒定的此类数学细化，当且仅当其测度代数非平凡，
即存在概率严格介于零与一的可测事件。
在该前提下，两个同步块之间的质量交换可以不改变指定事件的任何允许未来，
同时仍被完整终端标签看见。这个存在性并未确定实际已供应的 $\beta$，
也没有取得新的切口。

这一实例把本轮核心思想落实到项目最新源：

$$
\boxed{
\text{应保留的关系信息}
=\text{实际来源中能改变指定允许未来的区别}.
}
$$

源文还证明存在 $609$ 个原字效果基，每字长至多 $608$；
它没有执行该字表，也没有给出由存在性直接获得的统计样本数或条件数。
这里保留该条件域、实际取得、档案、调用成本与误差合同，
不把数学预测商转写成额外物理操作。

<a id="section-12"></a>

## 12. 统一字典与本轮结论

<div style="overflow-x:auto;max-width:100%">

| 角色 | 原五模式占位接口 | 声明的固定非退化 qubit 接口 |
| --- | --- | --- |
| 两端 | $\xi,\eta$ 及均值 $X,Y$ | 反射 $A,B$ 及均值 $x_1,x_3$ |
| 关系对象 | 联合事件 $e_{13}=\xi\eta$ | 有序乘积 $AB=S+iC$ |
| 关系读数 | $\kappa=\mathbb E(\xi\eta)$ | $z=\omega(AB)=c+isx_2$ |
| 关系约束 | 非负性、$\Delta$ 或指定赔率 | Gram 正性、固定对称角 $c$ |
| 第三读口 | 中位占据 $\zeta$ | 归一有向部分 $N=C/s$ |
| 归一化 | $\sum_s p_s=1=\omega(I)$ | $\operatorname{Tr}\rho=1=\omega(I)$ |
| 空模式/参考 | $e_N$ 是特定事件；可另定锚点 | 参考态和框架需另行标定 |
| 稳定性 | 关系区间、任务系数、TV 界 | 正性椭球与非退化夹角 |
| 递归 | 共同分隔变量与全局相容 | 允许控制下的未来效果闭合 |

</div>

两个接口中的“第三读口”承担不同具体对象；
表格给出关系角色的明确实现方式，实际跨接口等同仍需指定编码。
统一后的核心不是数一数共有五个名称，而是给出以下连续结构：
先声明来源与读口，由关系信息细化相容纤维，
由单位元规定总质量，由正性保证可实现性，
再以允许未来检查是否遗漏关系。

于是用户直觉可以整理为一个带证明的研究命题：

> 
$F[13]$ 是连接两端的关系位置。关系既表现为限制允许共同实现的方程和不等式，
又表现为区分相同边缘来源的额外信息。
在固定关系律或固定非退化量子扇区内，这些数据可压缩成可重构的三轴模型；
递归扩展时，所需关系由全局相容性及未来任务闭合决定。

本轮确实给出了几种可持续推进的数学机制：
对数赔率的可和关系级数、带质量的树拼接误差、
循环相容性的尖锐修复，以及量子三轴的条件数。
它们分别在已陈述的来源、关系和操作假设下成立。
标准 Gram、Pauli、树 Markov 与有限维可观测空间方法不主张原创优先权；
本稿的作用是把这些证明与当前 AURIC 关系语义及原生实例准确连接。

<a id="references"></a>

## 固定来源与使用范围

<a id="ref-head"></a>

**[1]** 
[trureturing，固定提交 2fe4175f9a8a](https://github.com/the-omega-institute/trureturing/commit/2fe4175f9a8a88d3a2d4fa5deb918b67bc3bf890)。
2026-10-31 15:29:21（新加坡）；本文定向核对公开源码及理论树差异。

<a id="ref-foundation"></a>

**[2]** 
[AURIC 金字塔基础公式与关系](https://github.com/the-omega-institute/trureturing/blob/2fe4175f9a8a88d3a2d4fa5deb918b67bc3bf890/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)。
§§2–9：五函数基、关系纤维、条件行列式、minimax、最大熵与 TV。

<a id="ref-correlation"></a>

**[3]** 
[AURIC 金字塔关联与原生接续](https://github.com/the-omega-institute/trureturing/blob/2fe4175f9a8a88d3a2d4fa5deb918b67bc3bf890/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)。
§§3–4：$J_f$、目标关系敏感性及完整纤维。

<a id="ref-determinant"></a>

**[4]** 
[AURIC 金字塔行列式与原生守卫接续](https://github.com/the-omega-institute/trureturing/blob/2fe4175f9a8a88d3a2d4fa5deb918b67bc3bf890/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md)。
定义 0.4、§§1–7：共同占位、遗漏联合关系、条件拼接及赔率参数。

<a id="ref-v24"></a>

**[5]** 
[AURIC 两基态与三通道，V24](https://github.com/the-omega-institute/trureturing/blob/2fe4175f9a8a88d3a2d4fa5deb918b67bc3bf890/docs/develop/theory/AURIC_TWO_BASIS_STATES_THREE_CHANNELS_PHASE_CHIRALITY_AND_RECURSIVE_SQUARE_LAW_V24.md)。
§§2–4：线性重构判据、Bloch 几何、反对易第三算符及 Gram 关系。

<a id="ref-v37"></a>

**[6]** 
[AURIC 二元关系、酉表示与黄金门通用性，V37](https://github.com/the-omega-institute/trureturing/blob/2fe4175f9a8a88d3a2d4fa5deb918b67bc3bf890/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)。
关系表示、接口合同与门集合控制的分层背景。

<a id="ref-hardcore"></a>

**[7]** 
[共同活动度 hard-core 占据的高活动度稳定性与精确缺陷分解](https://github.com/the-omega-institute/trureturing/blob/2fe4175f9a8a88d3a2d4fa5deb918b67bc3bf890/docs/develop/theory/HARD_CORE_COMMON_ACTIVITY_STABILITY_AND_DEFECT.md)。
本文只消费定义 1.1 的同源 Gibbs 律；内部消元与赔率乘法是本文继续推导。

<a id="ref-terminal"></a>

**[8]** 
[递归关系观察：Fibonacci 原生终端认证](https://github.com/the-omega-institute/trureturing/blob/2fe4175f9a8a88d3a2d4fa5deb918b67bc3bf890/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)。
最新 §§12–17：付费共同切口条件域、609/610 效果空间、同步块商、
纯源不可见核、实际前缀 $78$ 与有限原字见证。

<a id="ref-iii"></a>

**[9]** 
[AURIC 量子原则与相干重构续卷 III](https://github.com/the-omega-institute/trureturing/blob/2fe4175f9a8a88d3a2d4fa5deb918b67bc3bf890/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md)。
§151：实际来源、尾块、完整标签与条件律类；
本文沿用其前件，不重新声称取得共同切口或实际操作服务。

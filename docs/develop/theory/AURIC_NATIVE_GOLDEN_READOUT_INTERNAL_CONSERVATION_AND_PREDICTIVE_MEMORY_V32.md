<a id="auric-v32"></a>

# AURIC：原生黄金读口、内部守恒与预测记忆

**五个原生残差的定量闭合、单侧探测与有限记忆的奇异边界**

定义、定理与纸面证明　v32.0

2026 年 10 月 31 日　Asia/Singapore

> **转换归属（编者）。** 以下正文依作者提供的完整 v32.0 XeLaTeX 源稿转换，保留原有历史报告、来源核读、经典归因、纸面证明及适用边界；这些陈述不因转换而成为转换者的独立认证。源稿 SHA-256：`b7910fec3343094bc0e93fcc3954dc61d50e3936e60613f8e340f31d7c3ae930`。字体、页眉、页码与分页排版由 Markdown 替代；数学宏按 TeX 参数规则展开，陈述按各节实际共享计数器编号，只保留源稿显式公式标签 (1)–(25)，全部证明保留可见终止符。私有 ChatGPT 源稿链接按作者原引用保留，不表示转换者取得了该私有文件。

<a id="section-abstract"></a>

## 摘要

本稿继续以单一固定整体态表达观察者、程序、测量、环境坐标、记忆和时钟。
项目最新量子续卷 II 第 111--114 节以一次原生第三读者和五个固定后续，
条件性地消除了 v31 所消费的第二记录响应自由。
本文先给其有限误差消费者：在已取得的精确旧分类及旧记录质量下界 $a\ge h>0$ 下，
五个残差至多 $\varepsilon$ 推出 $1-c\le4\varepsilon/(hx^2)$；
没有定量正质量裕量时，不存在相应统一稳定结论。
新原生矩阵还给单侧黄金读口 $M_0=\sqrt x(I-P)$、
$M_1=x(I-P)+\zeta^{-3}P$，从而得到理想重复的闭式后验与首次发现分布。
随后证明全态尖锐投影平均守恒等价于逐 Kraus 扇区保持，
并构造近守恒等距的精确守恒近似，给出平方根尺度的锐反例。
长期稳定被进一步放宽为可求和平均漂移加趋零的信息性仪器误差。
对于单侧读口，完整计费的确定性在线预测器在全历史一致误差 $\epsilon<x/2$ 下，
最少需要 $N_\epsilon+2$ 个状态，且此数与时间跨度无关。
但把严格零概率改成任意小正数，即使仍精确守恒并几乎必然选支，
也使低于固定阈值的全历史有限记忆预测不可能。
最后区分预测摘要、完整历史档案和相干记录压缩，保留原生初始化、重复 ready、
相位与失败质量的取得义务。全文不给原生有限字自动实现任意 CP 仪器的结论。

<a id="section-1"></a>

## 1. 固定来源、研究前提与本轮问题

本轮默认分支固定为 `dev` 提交

`d81fb8920f72f3d5f46221f6655627e7df791d3f`，

提交时间 2026-10-31 00:15:55（新加坡）。比较基线为 v31 的

`bd2207586c3c64e1a4ebcfa23f53b974a2700385`。
完整 theory 子树有 1056 个文件，相比基线只有四个路径变化：
量子续卷 II 严格追加 §§111--114；Typed cocycle 严格追加 §24；
v30 唯一静态本体源稿新入库；另有一项平均混合理论文件。
$\Omega$ 静态相融、v21 及周期时钟文件在这次比较中不变。
完整 D5 树与 v31 相同，没有新增 Quantum 代码认证。
本稿读取来源并进行纸面证明，未运行 Lean、门字枚举或数学数值程序。 [[1]](#ref-head)、[[2]](#ref-quantum)、[[3]](#ref-typed)、[[4]](#ref-v30)

整体仍是一个固定的正归一代数态 $(\mathcal{A},\omega)$。
内部子代数和张量坐标表示可区分的关系角色，不表示本体之外的第二系统。
数学上选择一个整体态，不等于已证明全部局部约束只容许唯一宇宙解。
对正质量内部历史 $h$，条件读出由

$$
\omega_h(A)=\frac{\omega(P_hAP_h)}{\omega(P_h)}
$$

表达，记录细化满足 $P_h=\sum_yP_{hy}$。
后续控制的因果独立性可以是内部程序与先前记录的关系；
它仍须证明，不能由本体闭合性自动取得。

v31 已证明信息性读口在可求和完整仪器误差下的长期极化，
以及精确平均守恒时只需误差趋零的加强版本。
本轮的任务是把这些抽象前件进一步接到原生矩阵、可核查的守恒结构和预测成本。 [[5]](#ref-v31)

<a id="section-2"></a>

## 2. 项目新增：第三读者关闭既有响应残余族

令

$$
x=\frac{\sqrt5-1}{2},\quad y=\sqrt x,\quad
 \varphi=x^{-1},\quad \zeta=e^{3\pi i/5},\quad x+x^2=1.
$$

项目的原来源为 $H=V_8^{\mathbf1}$，维数十三。
扩大载体 $\mathcal K=V_{12}^{\mathbf1}$ 维数八十九，
含 $J(H\otimes\mathbb{C}^2)$ 的二十六维代码及六十三维补空间。
令 $P=\Pi$ 为秩五投影，$E=I-P$，$D=E+\zeta P$。
源的共同理想相干准备是

<a id="eq:source-V"></a>

$$
V\psi=y\psi\otimes\lvert 0\rangle+xD\psi\otimes\lvert 1\rangle.
 \tag{1}
$$

三个读者为 $I,K_9^2,K_9$。
新第三读者只调用一次已有地址九，不另加任意旋转。
源 §111 给整个代码上的恒等式

<a id="eq:native-port"></a>

$$
(I\otimes B_R)V\psi
 =\zeta^2\left[yE\psi\otimes\lvert 0\rangle
 +(xE\psi+\zeta^{-3}P\psi)\otimes\lvert 1\rangle\right],
 \tag{2}
$$

其中

$$
B_R=\begin{pmatrix}-x&y\zeta^{-1}\\y\zeta^{-1}&-x\zeta^3\end{pmatrix}.
$$

相对分支相位 $\zeta^{-3}$ 被保留。 [[2]](#ref-quantum)

源 §104 的全部旧合同已经给出

<a id="eq:family"></a>

$$
F=q,\quad G=cq+d,\quad
 a=\frac{c}{x+c},\quad0<c\le1,\quad
 d_w\ge0,\quad\sum_wd_w=1-c.
 \tag{3}
$$

$q$ 是十三个合法基坐标的 Born 律，完整输出仍含全部 1024 个旧标签。
对指定原制备 $p_*=1$，源 §111--112 固定一次且共用

<a id="eq:five"></a>

$$
\mathcal F=(\epsilon,3,13,013,0013),\qquad w_*=1000000010.
 \tag{4}
$$

新设置记录零的质量只假设 $b\in[0,1]$。
继承旧全域合同后，再要求新设置与设置零在事件 $w_*$、五个原生后续上相等，
源定理 112.1 得到

<a id="eq:source-closure"></a>

$$
\boxed{F=G=q,\quad c=1,\quad d=0,\quad a=x,\quad b=x^3.}
 \tag{5}
$$

函数结论遍历旧球面与全部旧标签；数值记录结论只针对该制备和三个指定设置。
源 §114 证明旧 $c<1$ 模型至少违反一个新增等式。
所以矩阵局部性和原门菜单并不自动提供新增实际概率隔离。

<a id="section-3"></a>

## 3. 新定理：五个有限残差的显式稳定界

为得到可核查的定量消费者，保留源的完整旧分类 [(3)](#eq:family)。
令 $e_L=e_{00100}$、$e_R=e_{10100}$、$e_*=e_{00000}$，
$L=\operatorname{span}\{e_L,e_R\}$，并定义单位向量

$$
\eta=-xe_L+y\zeta^{-1}e_R,\quad
 \theta_0=-e_L,\quad
 \theta_1=\frac{-x^2e_L+y\zeta^{-4}e_R}{\sqrt2\,x}.
$$

写 $P_z=\lvert z\rangle\langle z\rvert$，这是普通矩阵记号。
置

<a id="eq:A"></a>

$$
A=bP_{\theta_0}+c(1-b)P_{\theta_1}
       -aP_\eta-c(1-a)P_{D\eta},\qquad
 \delta=(a-b)d_{w_*}.
 \tag{6}
$$

$A$ 支撑于 $L$。

**定义 3.1（有符号设置残差）。**

对五个固定字定义

$$
r_f=\langle e_*,K_f(A+\delta I)K_f^*e_*\rangle.
$$

它等于新设置事件边缘减去设置零事件边缘，权重采用同一旧分类中的 $a$ 和给定 $b$。
假设 $\max_{f\in\mathcal F}|r_f|\le\varepsilon$。
另给旧质量的定量裕量 $a\ge h>0$。

**引理 3.2（固定五字的加权消元）。**

记 $r_k=r_{0^k13}$（$k=0,1,2$），并置

$$
R=\frac{r_0+xr_1+r_2}{2+x}.
$$

则有精确公式

$$
\delta=r_\epsilon,\qquad A_{LL}=\frac{r_3-\delta}{x},
$$

<a id="eq:eliminate"></a>

$$
\boxed{A_{RR}=\frac R{x^2}-r_3-\frac\delta x,\qquad
 \operatorname{Tr} A=\frac R{x^2}+xr_3-\frac{2\delta}{x}.}
 \tag{7}
$$

进而

<a id="eq:tracebounds"></a>

$$
|A_{RR}|\le\frac{2\varepsilon}{x^2},\qquad
 |\operatorname{Tr} A|\le\frac{4\varepsilon}{x}.
 \tag{8}
$$

**证明。**

源的字面行限制（§112.5）是

$$
\langle e_*|K_3|_L=\lambda(1,0),\qquad
 \langle e_*|K_{0^k13}|_L
   =\lambda\zeta^k(\alpha,\lambda\zeta^k),
 \quad\alpha=-x,\quad\lambda=y\zeta^{-1}.
$$

空字因 $e_*\perp L$ 给 $\delta=r_\epsilon$，字三给第二式。
另外三个残差是

$$
r_k=x\left(x^2A_{LL}+xA_{RR}+z\zeta^{-k}+\bar z\zeta^k\right)+\delta,
 \qquad z=\alpha\bar\lambda A_{LR}.
$$

由 $1+x\zeta+\zeta^2=0$ 及其共轭，取权重 $(1,x,1)$ 消去振荡项，得
$R=x^3A_{LL}+x^2A_{RR}+\delta$。
代入 $A_{LL}$ 及 $1-x^2=x$，即得 $A_{RR}$；加上 $A_{LL}$ 得迹式。
因为 $|R|,|r_3|,|\delta|\le\varepsilon$，且
$x^{-2}+1+x^{-1}=2x^{-2}$、
$x^{-2}+x+2x^{-1}=4x^{-1}$，便得两个界。

□

**定理 3.3（五残差的定量闭合）。**

<a id="thm:finiteclosure"></a>

在上述已分类族和正质量裕量下，令 $t=1-c$，则

<a id="eq:tbound"></a>

$$
\boxed{t\le\frac{4\varepsilon}{hx^2}.}
 \tag{9}
$$

因此

$$
\sup_{\psi}\operatorname{TV}(G(\psi),F(\psi))
 \le\min\left\{1,\frac{4\varepsilon}{hx^2}\right\},
 \qquad 0\le x-a\le xt,
$$

<a id="eq:bbound"></a>

$$
\boxed{|b-x^3|\le(1+2x^2)t+\frac{4\varepsilon}{x}.}
 \tag{10}
$$

**证明。**

由 [(6)](#eq:A) 及 $c(1-a)=ax$，直接得到

$$
\operatorname{Tr} A=t(b-a),\qquad
 A_{RR}=\frac{c(1-b)}{2x}-a
       =-\frac a2-\frac{c(b-a)}{2x}.
$$

所以 $ta=-(c/x)\operatorname{Tr} A-2tA_{RR}$。
用 [(8)](#eq:tracebounds) 及 $c+t=1$，

$$
ta\le\frac{4c\varepsilon}{x^2}
       +\frac{4t\varepsilon}{x^2}=\frac{4\varepsilon}{x^2}.
$$

除以 $a\ge h$ 得主界。
$G-F=d-tq$ 的总变差至多 $t$。
由 $a=c/(x+c)$，还有
$x-a=x^3t/(1-xt)\le xt$。
最后 $1-x^3=2x^2$ 与 $c(1-b)=2x(a+A_{RR})$ 给

$$
b-x^3=2x(x-a)-2xA_{RR}-t(1-b).
$$

利用 $b\in[0,1]$ 和前述界即可。

□

**命题 3.4（缺少定量正质量时，统一稳定失效）。**

即使保持精确旧分类且每个模型都有 $a>0$，
五个残差趋零也不统一推出 $G-F$ 的全域误差趋零。

**证明。**

取 $c\downarrow0$、$a=c/(x+c)$、$b=a$、
$d=(1-c)\delta_j$，其中 $j$ 为某个合法标签。
此时 $\delta=0$ 且

$$
A=a(P_{\theta_0}+xP_{\theta_1}-P_\eta-xP_{D\eta}),
$$

故所有残差为 $O(a)\to0$。
对另一个合法基输入 $e_k$，
$\operatorname{TV}(G(e_k),F(e_k))=1-c\to1$。
因此没有跨该族的统一零误差模。

□

以上是已分类族内的稳定定理，不是对全部未知连续响应的有限认证。
当用有限原生协议供应这些残差时，还必须计入实际失败、射线误差、成功质量随接续变化、
设置隔离误差及参考质量与 $a$ 的偏差。
源 §113 的残差预算为

$$
e_n=\tau_n+\nu(\kappa_n)+\nu(\kappa'_n)
 +\tfrac12(\gamma_n+\gamma'_n)+\beta_n+\beta'_n\to0.
$$

其有限权重是 $a_{n0},b_n$；若尚无 $a_{n0}-a$ 的定量界，
不能直接把 $e_n$ 当作定理 [3.3](#thm:finiteclosure) 使用固定 $a$ 的全部误差。
这保留了实际质量与极限分类之间的区别。 [[2]](#ref-quantum)

<a id="section-4"></a>

## 4. 一个具体原生目标：单侧黄金量子读口

现在另行采用明确的 Born/CP 保留读出合同。
这项结构允许把 [(2)](#eq:native-port) 的两个列分量解释为 Kraus 算符。
源的指定制备概率重构本身尚未证明任意输入的该合同。

**定义 4.1（单侧黄金仪器）。**

在内部接口 $\mathcal{H}$ 上固定非平凡投影 $P$，令 $E=I-P$，定义

<a id="eq:goldinstrument"></a>

$$
M_0=\sqrt x E,\qquad M_1=xE+\zeta^{-3}P,
 \qquad \mathcal I_i(\rho)=M_i\rho M_i^*.
 \tag{11}
$$

每个内部结果被保留，并按该 CP 仪器更新。

**命题 4.2（完备性、守恒与信息性）。**

[(11)](#eq:goldinstrument) 是完备仪器，且

$$
\sum_iM_i^*M_i=I,\qquad [M_i,P]=0,\qquad
 \sum_iM_i^*PM_i=P.
$$

两扇区的结果似然为

$$
\ell_E=(x,x^2),\qquad \ell_P=(0,1).
$$

**证明。**

$EP=0$ 及 $x+x^2=1$ 给
$M_0^*M_0=xE$、$M_1^*M_1=x^2E+P$。
逐项交换与投影式随即成立。
对支持在各扇区的归一态取迹得到似然。

□

**定理 4.3（完整重复的闭式后验）。**

<a id="thm:onesided"></a>

从固定初态 $\rho_0$ 出发，置 $q_0=\operatorname{Tr}(P\rho_0)$。
只要出现结果零，后验 $q$ 就为零且以后保持为零。
连续 $n$ 次结果一的质量与后验为

<a id="eq:qclosed"></a>

$$
\boxed{\mathbb{P}(1^n)=q_0+(1-q_0)x^{2n},\qquad
 q_n=\frac{q_0}{q_0+(1-q_0)x^{2n}}.}
 \tag{12}
$$

因此无限全一事件的质量为 $q_0$，其上 $q_n\to1$（若 $q_0>0$）；
其余历史最终进入 $E$ 扇区。

**证明。**

$M_0$ 的像在 $E$ 中，其余算符保留该扇区。
又

$$
M_1^n=x^nE+\zeta^{-3n}P,
 \qquad (M_1^n)^*M_1^n=x^{2n}E+P.
$$

取迹给前缀质量，再以 $P$ 读出未归一后继并相除得到后验。
嵌套事件 $1^n$ 的概率连续性给无限全一事件质量。

□

**推论 4.4（首次零记录的分布与条件等待）。**

令 $T$ 为第一个结果零的位置，不发生则 $T=\infty$。
对 $n\ge1$，

$$
\mathbb{P}(T=n)=(1-q_0)x^{2n-1},\qquad
 \mathbb{P}(T=\infty)=q_0.
$$

若 $q_0<1$，则

$$
\boxed{\mathbb{E}[T\mid T<\infty]=x^{-1}=\varphi.}
$$

当 $q_0>0$ 时，无条件 $\mathbb{E} T=\infty$。

**证明。**

$\mathbb{P}(T>n)=\mathbb{P}(1^n)$；相邻尾概率相减得到质量。
条件分布为 $x(x^2)^{n-1}$，因为 $1-x^2=x$，
它是成功概率 $x$ 的几何分布，尾和为 $1/x$。
正质量的无穷等待使无条件期望无穷。

□

这里 $\varphi$ 是该内部协议按读出轮数计量的条件平均等待；
每轮原生调用成本、初始化和实际钟单位尚须另行计入。
当 $0<q_0<1$ 时，任何有限全一前缀在两个扇区下都有正质量。
因此，仅使用这个读口的零错误程序不能在有限全一历史上确定宣布已取得 $P$；
几乎必然的极限选支不等于两个扇区都有有限时的零错误确认。

<a id="section-5"></a>

## 5. 尖锐投影守恒的结构：不能靠正负泄漏抵消

**定义 5.1（完整内部仪器与平均通道）。**

在共同有限维接口上取 Kraus 算符 $K_{y\alpha}$，满足

$$
\mathcal I_y(\rho)=\sum_\alpha K_{y\alpha}\rho K_{y\alpha}^*,
 \quad \sum_{y,\alpha}K_{y\alpha}^*K_{y\alpha}=I,
 \quad\Phi=\sum_y\mathcal I_y.
$$

全部失败与保留后继均在这个接口与结果域中。
令内部等距扩张为

$$
V\psi=\sum_{y,\alpha}K_{y\alpha}\psi\otimes\lvert y,\alpha\rangle,
 \qquad Q=P\otimes I.
$$

**定理 5.2（全态平均守恒的等价刻画）。**

<a id="thm:commutation"></a>

下列三项等价：

<a id="eq:equiv"></a>

$$
\Phi^*(P)=P;\qquad
 [K_{y\alpha},P]=0\ \text{对每个 }y,\alpha;\qquad
 QV=VP.
 \tag{13}
$$

第一项量化全部输入态的平均指针权重守恒。

**证明。**

若 $\Phi^*(P)=P$，对 $u\in\operatorname{ran}E$ 有

$$
0=\langle u,\Phi^*(P)u\rangle
 =\sum_{y,\alpha}\|PK_{y\alpha}u\|^2.
$$

每项非负，故 $PK_{y\alpha}E=0$。
通道完备性又给 $\Phi^*(E)=E$，同理 $EK_{y\alpha}P=0$。
所以每个 Kraus 算符分块对角并与 $P$ 对易。
逆向利用对易性和完备性，
$\sum K^*PK=P\sum K^*K=P$。
最后，等距式按正交记录基展开，逐系数等价于 $PK_{y\alpha}=K_{y\alpha}P$。

□

**推论 5.3（有限精确基校准的结构效力）。**

取 $P$ 与 $E$ 各自的正交基。
若每个基输入的平均输出跨扇区概率都严格为零，则 [(13)](#eq:equiv) 成立。

**证明。**

每个基向量上的跨扇区概率是各 Kraus 泄漏范数平方之和。
全为零迫使各分量在整个基上为零，线性延拓给两个非对角块为零。

□

这依赖事先给定的线性 CP 仪器类和精确零概率，不是有限样本证明任意未知响应的线性。

**推论 5.4（随机混合不能隐藏跨扇区泄漏）。**

若 $\Phi(\rho)=\sum_jp_jU_j\rho U_j^*$，$p_j>0$，
则 $\Phi^*(P)=P$ 当且仅当每个 $U_j$ 与 $P$ 对易。

**证明。**

应用定理于 Kraus 算符 $\sqrt{p_j}U_j$。

□

只对一个实际态保持期望则弱得多。
例如 $P=\lvert 1\rangle\langle 1\rvert$、$\rho=\lvert +\rangle\langle +\rvert$，
$X\rho X=\rho$，但 $[X,P]\ne0$。
而恒等通道虽对所有态保 $P$，若只有一个固定结果，就没有取得任何指针信息。
因此守恒和信息性须分别证明。

<a id="section-6"></a>

## 6. 近守恒的完整结构与平方根边界

**定义 6.1（守恒缺陷与最大扇区泄漏）。**

沿用完整等距 $V$ 和 $Q=P\otimes I$，置

$$
\delta=\|V^*QV-P\|_{\rm op},
$$

$$
\lambda=\max\{\|QV E\|_{\rm op}^2,
                    \|(I-Q)VP\|_{\rm op}^2\}.
$$

**定理 6.2（近守恒等距的精确守恒近似）。**

<a id="thm:shadow"></a>

若 $\delta<1$，则

$$
\delta^2\le\lambda\le\delta,
 \qquad\|QV-VP\|_{\rm op}=\sqrt\lambda.
$$

存在同一输入与记录载体上的等距 $W$，满足 $QW=WP$，且

<a id="eq:shadow"></a>

$$
\boxed{\|V-W\|_{\rm op}
 \le\sqrt\lambda+1-\sqrt{1-\lambda}
 \le\sqrt\delta+1-\sqrt{1-\delta}.}
 \tag{14}
$$

测量相同记录后，两完整旗标仪器的半 diamond 距离至多该界。

**证明。**

算符 $QV-VP=QV E-(I-Q)VP$ 的两个块有正交输入和正交输出，
所以范数平方为 $\lambda$。
左乘收缩 $V^*$ 得 $\delta\le\sqrt\lambda$。
另一方面，$V^*QV-P$ 的 $E$ 对角块为 $(QV E)^*(QV E)$，
$P$ 对角块为 $-((I-Q)VP)^*((I-Q)VP)$，故两者范数都至多 $\delta$。

取块对角截断

$$
V_d=QVP+(I-Q)V E.
$$

则 $QV_d=V_dP$，$\|V-V_d\|=\sqrt\lambda$，且

$$
(1-\lambda)I\le G:=V_d^*V_d\le I.
$$

因此 $G$ 可逆且与 $P$ 对易，令 $W=V_dG^{-1/2}$。
有 $W^*W=I$、$QW=WP$。
由 $V_d=WG^{1/2}$，

$$
\|W-V_d\|=\|I-G^{1/2}\|\le1-\sqrt{1-\lambda}.
$$

三角不等式给第一界，单调性给第二界。
对含任意参考坐标的纯输入，两个等距输出的向量距离至多 $\|V-W\|$；
其纯态半迹距离不超过该距离。
混态用纯化，随后相同记录测量及部分迹均收缩，得到完整半 diamond 界。

□

**命题 6.3（平方根尺度不能普遍改善成线性）。**

在二维空间，先作投影读出再施实旋转 $R_\theta$：

$$
K_i=R_\theta P_i,\qquad 0<\theta<\pi/2.
$$

则平均守恒缺陷为 $\delta=\sin^2\theta$，
但它与任意精确保 $P_1$ 的完整仪器之半 diamond 距离至少为 $\sin\theta=\sqrt\delta$。

**证明。**

其对偶平均投影为
$\sin^2\theta P_0+\cos^2\theta P_1$，故缺陷如述。
输入 $\lvert 0\rangle$ 时实际量子后继是 $R_\theta\lvert 0\rangle$；
任意精确守恒仪器的平均量子后继必须仍支持于一维 $P_0$，即为 $\lvert 0\rangle\langle 0\rvert$。
两态半迹距离为 $\sin\theta$，对完整输出作部分迹给所需下界。
理想投影仪器本身达到这个距离。

□

定理 [6.2](#thm:shadow) 构造的是数学等距。
块截断与逆平方根未因此加入原生可执行菜单，也没有得到免费物理校正。
它用于结构比较和误差分析，不绕过源 §103 的精确有限字障碍。

<a id="section-7"></a>

## 7. 新稳定定理：把平均漂移和信息误差分开

**定义 7.1（两个独立误差合同）。**

对实际历史过滤 $\mathcal F_n$ 和实际条件态 $\rho_n$，令
$q_n=\operatorname{Tr}(P\rho_n)$、$V(q)=q(1-q)$。
从固定 $q_0$ 开始，要求

<a id="eq:drift"></a>

$$
|\mathbb{E}[q_{n+1}\mid\mathcal F_n]-q_n|\le d_n,
 \qquad D_*:=\sum_nd_n<\infty.
 \tag{15}
$$

其中 $d_n$ 是确定的非负误差包络。
每个实际历史上，再给一个平均保 $P$ 的参考仪器，
其理想后验杂质满足统一信息增益

$$
\mathbb{E}_0[V(q')\mid\rho_n]\le V(q_n)-\kappa V(q_n)^2,
 \qquad\kappa>0.
$$

实际与参考在该实际输入上的完整旗标半迹距离至多 $e_n(h_n)$，
且 $e_n(h_n)\to0$ 几乎必然。
这里不要求 $\sum_ne_n<\infty$。

**定理 7.2（可求和漂移加渐近信息性）。**

<a id="thm:twobudgets"></a>

在定义条件下，

$$
\boxed{q_n\to q_\infty\in\{0,1\}\quad\text{几乎必然及 }L^1,}
$$

<a id="eq:polarlimit"></a>

$$
\boxed{|\mathbb{P}(q_\infty=1)-q_0|\le D_*.}
 \tag{16}
$$

若另有确定包络 $e_n(h_n)\le\bar e_n\to0$，
对 $0<\eta<1/2$ 取 $N_\eta$ 使所有 $n\ge N_\eta$ 满足
$\bar e_n+d_n\le\kappa\eta^2(1-\eta)^2/2$，则

<a id="eq:tailoccupancy"></a>

$$
\sum_{n\ge N_\eta}\mathbb{P}(\eta\le q_n\le1-\eta)
 \le\frac{2[V(q_0)+D_*]}{\kappa\eta^2(1-\eta)^2}.
 \tag{17}
$$

**证明。**

记 $b_n=\mathbb{E}[q_{n+1}\mid\mathcal F_n]-q_n$。
$Z_n=q_n-\sum_{j<n}b_j$ 是绝对值至多 $1+D_*$ 的鞅。
有界鞅收敛且漂移绝对可求和，所以 $q_n$ 几乎必然收敛。

对未归一正输出 $\tau$，写 $a=\operatorname{Tr}(P\tau),p=\operatorname{Tr}\tau$。
后验杂质贡献 $g(\tau)=a-a^2/p$（零质量取零）满足

$$
g(\tau)=\min_{0\le z\le1}\operatorname{Tr}\left[((1-2z)P+z^2I)\tau\right].
$$

括号算符在两扇区上的特征值为 $(1-z)^2,z^2$，均在 $[0,1]$。
所以在全部结果作直和后的归一态上，$\sum_yg(\tau_y)$
对半迹距离为 1-Lipschitz。
实际杂质因而满足

$$
\mathbb{E}[V(q_{n+1})\mid\mathcal F_n]
 \le V(q_n)-\kappa V(q_n)^2+e_n(h_n).
$$

令 $A_n=\operatorname{Var}(q_{n+1}\mid\mathcal F_n)$。
因为 $V$ 在 $[0,1]$ 上为 1-Lipschitz，

<a id="eq:varlower"></a>

$$
A_n=V(q_n+b_n)-\mathbb{E}[V(q_{n+1})\mid\mathcal F_n]
 \ge\kappa V(q_n)^2-e_n(h_n)-d_n.
 \tag{18}
$$

同一恒等式又给
$A_n\le V(q_n)-\mathbb{E}[V(q_{n+1})\mid\mathcal F_n]+d_n$。
取期望求和，末项非负，得到

$$
\mathbb{E}\sum_nA_n\le V(q_0)+D_*<\infty.
$$

故 $\sum_nA_n<\infty$ 几乎必然。
若 $V(q_\infty)>0$，式 [(18)](#eq:varlower) 的右侧最终为严格正下界，矛盾。
所以极限二值。有界收敛与漂移求和给式 [(16)](#eq:polarlimit)。
在确定包络条件下，$n\ge N_\eta$ 的中间区域有
$A_n\ge\kappa\eta^2(1-\eta)^2/2$；其余区域 $A_n\ge0$。
代入已得总条件方差界，得到式 [(17)](#eq:tailoccupancy)。

□

**命题 7.3（守恒缺陷供应漂移预算）。**

若每个实际仪器的平均通道满足
$\|\Phi_n^*(P)-P\|_{\rm op}\le d_n$，则式 [(15)](#eq:drift) 对全部实际输入成立。

**证明。**

对实际态取期望，算子范数控制绝对值。

□

**命题 7.4（保持扇区内部动力学的统一信息条件）。**

参考仪器的所有 Kraus 算符与 $P$ 对易。
若某个结果事件的效果 $B$ 满足

$$
PBP\ge bP,\qquad EBE\le aE,\qquad b-a=g>0,
$$

则可取统一信息增益常数 $\kappa=4g^2$，
不要求各 Kraus 在扇区内是标量。

**证明。**

对 $0<q<1$，用两个归一扇区态计算该事件条件似然 $\ell_1,\ell_0$，
有 $\ell_1-\ell_0\ge g$。
跨扇区项对结果概率的迹为零，故后验指针权重服从该二元 Bayes 更新。
其条件方差为
$q^2(1-q)^2(\ell_1-\ell_0)^2/[p(1-p)]\ge4g^2V(q)^2$。
更细结果的条件方差至少为该粗事件的条件方差。
端点直接为零。平均保 $P$ 后，杂质下降等于该方差。

□

**推论 7.5（全态近守恒与实际信息隙的消费者）。**

若存在确定的非负包络 $d_n$，$\sum_nd_n<\infty$，
使每个实际可达历史 $h_n$ 上都有
$\|\Phi_{n,h_n}^*(P)-P\|_{\rm op}\le d_n$，
且实际仪器某二元事件的两个扇区效果在所有这些历史上有同一固定正隙 $g>0$，
则最终可用定理 [6.2](#thm:shadow) 的精确守恒近似作为参考，
从而得到几乎必然极化。

**证明。**

守恒缺陷 $d_n\to0$，所以近似仪器距离
$\eta_n=\sqrt{d_n}+1-\sqrt{1-d_n}\to0$。
对任意输入事件概率差至多 $\eta_n$，故参考事件的两扇区隙至少为 $g-2\eta_n$，
最终至少 $g/2$。
前一命题给参考信息常数 $\kappa=g^2$。
从这一有限层开始应用定理 [7.2](#thm:twobudgets)；有限前缀不影响极限存在和二值性。

□

这条推论没有要求 $\sum_n\sqrt{d_n}<\infty$。
它使用近似结构作数学比较，不把该结构当作实际免费纠错。

**命题 7.6（一个严格弱于总仪器误差可求和的例子）。**

投影读出后施 $R_{\theta_n}$，令 $\theta_n\to0$。
完整仪器误差为 $|\sin\theta_n|$，平均守恒缺陷为 $\sin^2\theta_n$。
若 $\sum_n\sin^2\theta_n<\infty$，实际指针仍稳定。
在这个模型中，若平方和发散，则指针几乎必然无穷次翻转，不能稳定。

**证明。**

每次条件态是 $R_{\theta_n}\lvert Y_n\rangle$。
下一次标签翻转的条件概率为 $\sin^2\theta_n$。
平方和有限时，期望翻转总数有限，故翻转有限次几乎必然；
再用 $\theta_n\to0$，权重趋于一个端点。
平方和发散时，自任意确定层起永不再翻转的概率
$\prod_n(1-\sin^2\theta_n)$ 为零。
所以翻转无穷多，两个端点都有趋近子列。

□

例如 $|\sin\theta_n|=1/(n+2)$ 的总误差不求和，但平方和求和。
这不表示任意原生门误差都自动产生二次的守恒缺陷。

<a id="section-8"></a>

## 8. 单侧读口的最小在线预测记忆

本节只预测重复同一个仪器的下一次结果概率。
不要求恢复完整历史、当前量子态、任意其它门下的未来响应或完整本体。
固定 $0<q_0<1$。

**定义 8.1（完整计费的确定性预测器）。**

预测器有有限状态集 $S$、固定初始状态、总更新
$U:S\times\{0,1\}\to S$ 和输出 $\widehat p:S\to[0,1]$。
全部持久计数、程序阶段和解析状态计入 $S$；
没有免费事件深度、实时钟读数或原来源状态输入。
对每条正概率有限历史 $h$，要求

<a id="eq:prediction"></a>

$$
|\widehat p(\mu(h))-\mathbb{P}(Y_{|h|+1}=0\mid h)|\le\epsilon.
 \tag{19}
$$

要求覆盖全部深度和全部这样的历史。
概率输出的安装描述、数字精度和计算时间不计入状态数，另作资源。

对单侧黄金仪器，任意含零历史的下一次零概率为 $x$；
全一历史后的概率为

<a id="eq:pn"></a>

$$
p_n=\frac{x(1-q_0)x^{2n}}{q_0+(1-q_0)x^{2n}},
 \qquad p_n\downarrow0.
 \tag{20}
$$

**定理 8.2（全历史一致预测的精确最小状态数）。**

<a id="thm:memory"></a>

对 $0<\epsilon<x/2$，令

<a id="eq:N"></a>

$$
N_\epsilon=\min\{n\ge0:p_n\le2\epsilon\}
 =\max\left\{0,
 \left\lceil\frac{\log\!\left(\frac{(1-q_0)(x-2\epsilon)}{2\epsilon q_0}\right)}
 {2\log\varphi}\right\rceil\right\}.
 \tag{21}
$$

则最少状态数恰为

<a id="eq:memory"></a>

$$
\boxed{|S|_{\min}=N_\epsilon+2.}
 \tag{22}
$$

若 $\epsilon\ge x/2$，一个状态足够；若 $\epsilon=0$，没有有限状态预测器。

**证明。**

先构造上界。取状态 $0,\ldots,N_\epsilon-1$，
另加全一饱和态 $s_\infty$ 和已见零态 $s_0$。
在计数态 $n$ 输出 $p_n$，读到一就递增并在阈值进入 $s_\infty$，
读到零则进入 $s_0$。
饱和态读一保持，输出 $p_{N_\epsilon}/2$；读零进入 $s_0$。
$s_0$ 对两结果均保持，输出 $x$。
若 $N_\epsilon=0$，初始直接是饱和态。
所有饱和后的真实 $p_n$ 均在 $[0,p_{N_\epsilon}]$，
故误差至多 $p_{N_\epsilon}/2\le\epsilon$。
其它状态精确，得到 $N_\epsilon+2$ 个状态的实现。

对下界，沿无限全一输入观察有限确定性状态轨道。
它最终进入一个周期，设首次进入周期的深度为 $i$。
每个周期状态在任意大的深度再现，而 $p_n\to0$，
故周期状态的输出必须不超过 $\epsilon$。
在首次到达它的深度 $i$，误差条件又要求 $p_i\le2\epsilon$，
所以 $i\ge N_\epsilon$。
轨道上至少有 $i$ 个暂态和一个周期态，故至少 $N_\epsilon+1$ 个状态。

任何含零历史的状态都不能等于任一全一历史的状态：
若相等，追加任意长的共同全一后缀，更新仍相等，
但两个真实预测分别恒为 $x$ 和趋于零。
当 $2\epsilon<x$ 时不可能同时满足误差界。
故还至少需要一个额外状态，得到下界。

公式 [(21)](#eq:N) 由解 $p_n\le2\epsilon$ 得到。
若 $\epsilon\ge x/2$，常输出 $x/2$ 即可。
若 $\epsilon=0$，周期状态在首次进入时须输出严格正的 $p_i$，
在无穷再现极限又须输出零，矛盾。

□

对固定 $q_0$，状态数为 $O(\log(1/\epsilon))$，
编码这些状态的位数为 $O(\log\log(1/\epsilon))$。
这是指定预测任务的状态成本，不是原生量子仪器、概率计算或完整档案的总成本。
若另供精确深度 $n$，一个“是否见零”的标志即可配合它精确计算 [(20)](#eq:pn)；
此时无界计数资源被移到已供应的内部钟，不能算作免费消失。
$q_0=0$ 或 $1$ 的退化边界各只需一个精确预测状态。

<a id="section-9"></a>

## 9. 一个奇异边界：微小正概率能摧毁有限记忆结论

**定义 9.1（带正暗结果的守恒读口）。**

取 $0<s<x$，将黄金仪器改为

<a id="eq:dark"></a>

$$
M_0^{(s)}=\sqrt x E+\sqrt s P,\qquad
 M_1^{(s)}=xE+\sqrt{1-s}\,\zeta^{-3}P.
 \tag{23}
$$

它仍完备且逐 Kraus 保 $P$，两扇区似然为
$\ell_E=(x,x^2)$、$\ell_P=(s,1-s)$。
当 $s\downarrow0$，其同记录等距在算子范数中趋于原单侧等距。

**命题 9.2（单轮仪器与有限记录律的精确比较）。**

以 $V_s$ 表示保留同一结果坐标的等距，令 $\mathsf P_s^{(n)}$ 表示前 $n$ 个结果的记录律，则

$$
\|V_s-V_0\|=\sqrt{2-2\sqrt{1-s}}\le\sqrt{2s},
$$

$$
\boxed{\operatorname{TV}(\mathsf P_s^{(n)},\mathsf P_0^{(n)})
 =q_0[1-(1-s)^n]\le q_0ns.}
$$

**证明。**

两个等距只在 $P$ 扇区不同，该扇区的结果向量之差的范数平方为
$s+(1-\sqrt{1-s})^2=2-2\sqrt{1-s}$。
记录律的 $E$ 分量完全相同，$P$ 分量分别为零概率 $s$ 的独立重复律
和全一字的点质量。两者总变差就是新律在全一字以外的质量
$1-(1-s)^n$；再乘 $q_0$ 即得等式。Bernoulli 不等式给末界。

□

这个有限跨度界不统一控制无限跨度，下面的阈值定理正好给出其边界。

**定理 9.3（全支持读口的固定有限记忆阈值）。**

<a id="thm:singular"></a>

对定义 [(19)](#eq:prediction) 的同一预测器合同、固定 $0<q_0<1$，
若 $s>0$，则存在有限状态全历史预测器，当且仅当

<a id="eq:threshold"></a>

$$
\boxed{\epsilon\ge\frac{x-s}{2}.}
 \tag{24}
$$

阈值以上一个常输出状态即可。

**证明。**

所有有限二元历史均有正概率。
后验对数优势 $L=\log(q/(1-q))$ 在结果零和一后分别增加

$$
u_0=\log(s/x)<0,\qquad
 u_1=\log((1-s)/x^2)>0.
$$

下一次零概率为 $x-(x-s)q$，取值均落在 $[s,x]$；
沿全零和全一历史分别趋于 $x$ 和 $s$。
因此常输出 $(x+s)/2$ 达到阈值。

反设存在有限状态预测器且 $2\epsilon<x-s$。
它沿全一输入最终周期化，故存在 $i\ge0,p\ge1$，
使深度 $i+kp$ 的状态对全部整数 $k\ge0$ 相同。
取两历史 $1^{i+kp}$ 和 $1^{i+3kp}$，它们的记忆相同，
对数优势相差 $2kpu_1$。
追加同一个零后缀，长度 $m_k$ 取为

$$
\frac{L_0+(i+2kp)u_1}{|u_0|}
$$

的最近非负整数（充分大 $k$ 时正）。
两个新对数优势的中点绝对值至多 $|u_0|/2$，半差为 $kpu_1\to\infty$。
所以两个后验分别趋于零和一，下一次零概率分别趋于 $x$ 和 $s$。
记忆相同且追加后缀相同，输出仍相同，
无法在两侧同时保持误差小于 $(x-s)/2$，矛盾。

□

**推论 9.4（几乎必然稳定不蕴含全历史有限预测记忆）。**

每个 $0<s<x$ 的上述读口仍使实际后验几乎必然极化，且选择质量等于 $q_0$，
但在 [(24)](#eq:threshold) 以下没有固定有限状态的全历史预测器。

**证明。**

该仪器精确保 $P$，两扇区似然差为 $x-s>0$。
二元后验方差至少为 $4(x-s)^2V(q)^2$。
有界鞅与该严格信息增益给二值极限，均值守恒给质量 $q_0$。
记忆结论由定理 [9.3](#thm:singular)。

□

这里没有逻辑冲突。几乎必然极化描述固定整体概率律下的路径极限；
全历史一致预测还量化任意长、正概率但可能极稀有的反向证据后缀。
理想单侧读口的严格零概率产生一个后验吸收状态，
任何正 $s$ 都恢复了两个方向的优势更新。
因此，源中矩阵近似任意准确，并不能自动传递 [(22)](#eq:memory) 的有限记忆结论。
要使用它，应证明严格支持零，或另行采用有限跨度／概率加权的预测合同。

<a id="section-10"></a>

## 10. 预测摘要、完整档案与相干压缩的不同资源

**定理 10.1（有限深度的二结果粗仪器）。**

单侧黄金仪器重复 $n$ 次，把历史粗分为“已经出现零”和“全部为一”，
得到精确 Kraus 形式

<a id="eq:coarse"></a>

$$
K_{0,n}=\sqrt{1-x^{2n}}E,\qquad
 K_{1,n}=x^nE+\zeta^{-3n}P.
 \tag{25}
$$

**证明。**

全一分量已由定理 [4.3](#thm:onesided) 给出。
任意含零历史的 Kraus 乘积都是一个标量乘 $E$；
把这些 CP 分量相加仍为某个非负系数乘 $E\rho E$。
完整性与全一分量的 $E$ 概率 $x^{2n}$ 迫使该系数为 $1-x^{2n}$。

□

**命题 10.2（相干记录的二维压缩与持久档案的下界）。**

取 $n\ge1$。若尚未把每个路径分别经典化并永久记录，
深度 $n$ 的相干记录等距可写为

$$
V_n\psi=E\psi\otimes r_E^{\otimes n}
                +P\psi\otimes r_P^{\otimes n},
$$

$$
r_E=\sqrt x\lvert 0\rangle+x\lvert 1\rangle,\qquad
 r_P=\zeta^{-3}\lvert 1\rangle.
$$

记录向量至多张成二维空间，故在该受限来源上存在深度相关的酉压缩至一个二能级记录。
若全部 $2^n$ 条历史已作为互相正交、各有正质量的持久档案保存，则保留完整档案的载体维数至少为 $2^n$。

**证明。**

两个向量张成空间的维数至多二，
把其一组正交基等距送入二能级记录乘固定冗余向量，补全正交基即可扩为酉。
该压缩依赖已知 $n$ 与原读口，并只对所述来源子空间给出重置冗余的结论。
对持久档案，从每个非零正交记录投影中取一个单位向量，得到 $2^n$ 个正交向量。
在 $0<q_0<1$ 的单侧模型中，$E$ 分量使每个有限二元字都有正质量，故下界适用。

□

相干压缩可把原档案测量变成压缩空间上的一般 POVM，
但生成并保留其输出仍需要相应记录资源。
本结论不称二维为所有测量、解码、在线更新和重置成本之和。

**命题 10.3（保存旧标签时不能免费重置记录）。**

若一个内部酉对正交输入记录满足

$$
U(\lvert h\rangle\otimes\lvert 0\rangle)=\lvert 0\rangle\otimes\lvert g_h\rangle,
$$

则 $\langle g_h,g_{h'}\rangle=\delta_{hh'}$。

**证明。**

酉保持内积。

□

旧记录可以搬到整体的另一个内部角色，不能在保持其区分能力时消失。
这一结论无需本体外环境，也没有假设热浴或引入热力学耗散公式。

**命题 10.4（固定有限自治载体不能精确重复严格退相干半群）。**

令系统与内部辅助的联合载体为固定有限维，辅助从同一个初始态出发，
以后只重复同一个联合酉 $U$，不作外部重置。
其每步系统限制态不能对全部 $n$ 精确等于单侧黄金仪器的非选择性通道 $\Phi^n$
在全部初态上的输出。

**证明。**

单侧通道在跨扇区块上满足

$$
E\Phi(\rho)P=x\zeta^3 E\rho P,
$$

所以对某个跨扇区相干初态，该块模严格趋零。
有限维酉却存在 $n_k\to\infty$ 使 $U^{n_k}\to I$。
可用其有限个本征相位的同时回归证明：
把紧环面分成任意小的有限盒，若干幂中两项落入同盒，
相除得到接近单位的正次幂；随精度趋零可取无界次数，
若次数有界则出现精确周期，再取其倍数。
故联合态沿该子列回到初始态，系统限制态也回到初态，
与其跨块已趋零矛盾。

□

有限深度的相干压缩不受此命题排除；它使用随深度变化的操作。
无限维或不断访问新内部支持也不受此有限自治假设限制。

<a id="section-11"></a>

## 11. 原生取得、时钟与下一条证明义务

当前项目已经给出同一来源中的三设置矩阵及五字实际隔离消费者。
其中共同准备 [(1)](#eq:source-V) 涉及的完整受控奇相位，
仍受源 §103 的有限精确字障碍限制；§105、§113 给逐精度有限近似。
该全码障碍不单独排除仅在 ready 子空间上采用不同方案的精确取得。
新增第三读者只增加一次 $K_9$，但这没有免费供应任意多轮 ready、
任意输入上的 CP 更新、完整记录保存或全部实际隔离概率。 [[2]](#ref-quantum)

如果实际原生协议给出总仪器误差 $e_n$ 与平均守恒缺陷 $d_n$，
本篇的直接消费者是

$$
\sum_nd_n<\infty,\qquad e_n\to0,
 \qquad\text{以及参考读口的统一正信息隙}.
$$

若有更强可求和 $e_n$，可直接使用 v31 的统一误差定理。
若仅有每层固定非零原生误差，则须另证实际长期结构，
不能把有限单次比较界无限重复而自动得到稳定。

设第 $n$ 轮实际执行字长为 $L_n$，
一个内部门计数钟的累计标签可以取 $\sum_{j\le n}L_j$，
再与内部参考钟进行标定。式 [(22)](#eq:memory) 中的预测器没有免费读取这个标签。
把一个无界计数器移入内部钟并向预测器供应，会改变资源合同。
同样，几何重建可以继续消费稳定且校准的记录，
但本篇的统计读口和记忆定理并未额外推出四维方向、二次钟律或引力作用量。

项目新 Typed cocycle §24 另给一个相近的资源提醒：
在其真实来源和最终取得合同下，$C_{\rm stat}=2$、$C_{\rm on}\le3$，
却不存在每个源商点上最多两个状态的忠实跟踪实现。
这不是 $C_{\rm on}=3$ 的最小性结论。
它表明任务充分摘要与实时忠实跟踪全源具有不同的约束，
与本篇区分预测器、完整档案和量子状态保持的做法一致。 [[3]](#ref-typed)

本轮已经把 v31 的若干抽象前件转成具体数学对象：
五个实际残差给可计算闭合界；原生矩阵给单侧黄金目标；
尖锐投影守恒给逐分支结构；漂移与信息分开后给更弱的稳定条件；
读口支持零决定全历史预测记忆是否可以固定有限。
下一项最直接的工作，是对一个实际有限原生取得序列同时给出
初始支持、全过程泄漏、守恒缺陷和信息隙，并在选定的记录合同中核算真实成本。

<a id="references"></a>

## 固定来源与前篇

<a id="ref-head"></a>

**[1]**

The Omega Institute, *trureturing*,
[固定 dev 提交 d81fb8920f72f3d5f46221f6655627e7df791d3f](https://github.com/the-omega-institute/trureturing/commit/d81fb8920f72f3d5f46221f6655627e7df791d3f)，
2026-10-31 00:15:55 Asia/Singapore。

<a id="ref-quantum"></a>

**[2]**

项目，[《AURIC FIB ATOM 与量子基本原则：续卷 II》](https://github.com/the-omega-institute/trureturing/blob/d81fb8920f72f3d5f46221f6655627e7df791d3f/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)，固定版本，
新增 §§111--114，继承 §§103--107 的指定假设与原生边界。
本轮新增文本完整读取；旧密度与调和分解作为已标明的来源依赖消费。

<a id="ref-typed"></a>

**[3]**

项目，[《Typed Residual Cocycle Reconstruction》](https://github.com/the-omega-institute/trureturing/blob/d81fb8920f72f3d5f46221f6655627e7df791d3f/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md)，新增 §24，尤其定理 24.4。
其最终真实源商取得、完整状态和仅名称更新合同均保留。

<a id="ref-v30"></a>

**[4]**

项目，[《唯一静态本体、内生观察者与黄金递归时钟》](https://github.com/the-omega-institute/trureturing/blob/d81fb8920f72f3d5f46221f6655627e7df791d3f/docs/develop/theory/AURIC_UNIQUE_STATIC_ONTOLOGY_ENDOGENOUS_OBSERVERS_AND_GOLDEN_RECURSIVE_CLOCKS_V30.md)，v30。
文件明确标注作者源稿转换归属；入库不构成独立证明认证。

<a id="ref-v31"></a>

**[5]**

前篇，*AURIC：内生记录、长期稳定与时钟几何重建*，v31，2026-10-30。
[原 LaTeX 源稿](https://chatgpt.com/library?file_id=libfile_3ba793f8512c819192e6dae38b90baa9&account_id=personal)。
本稿对守恒、稳定与记忆的新证明在正文给出；不宣称这些纸面推演已由 Lean 验证。

# AURIC：黄金嵌套闭包与稳健有限观察器

从实际记录的非唯一性到未知初值下的全未来保证

定义、定理与纸面证明　v34.0

2026 年 10 月 31 日　Asia/Singapore

> 编排说明：下文为作者 v34.0 原稿的完整 Markdown 转写。作者在原稿中报告的仓库比较、历史收录、源码审阅与未运行项目，以及“本轮”等第一人称陈述，保留其作者归属；这些陈述不构成本转写对历史操作的独立认证。文末 v33 私有 PDF 链接按原稿保留，不表示已取得访问。文中的纸面证明与所引 Lean 源码也不表示本稿已获 Lean 编译认证。

## 摘要

本稿继续固定单一静态整体、全部观察角色与程序内生的研究前提。
项目量子续卷 II 新增第 117–120 节证明：即使终端 Born 响应、指定质量、
所有正质量纯投影后继及现有完整有限原生供应合同都相同，实际计算记录律仍不唯一。
本文先在明确的标量记录规则类中，提出一个额外的跨输入黄金嵌套关系；
证明它与二元互补关系足以强制 $g(t)=t$，并给无连续性假设的显式稳定界
$\|g-\mathrm{id}\|_\infty\le\varphi^3(\eta+c)$。
有限轨道和有共同连续模的有限网格分别给目标输入与全域的条件证书。
在独立取得完整量子输出误差合同后，本文进一步证明：不必知道实际初始权重或取得实际后验，
只需等待 $m$ 层、读取 $L$ 层并保存有限计数，就能把全部未来扇区偏离风险界为
$(\sqrt2 r^L+\sum_{j\ge m}e_j)/b$。
一份可计算的趋零误差尾界使该结果成为有限程序，逻辑状态数至多
$m+L(L+1)/2+2$。初始区间校准的从零时刻障碍、可求和性与有效尾模的区别、
以及信息重叠与最优判决之间的不同，构成三条不能省略的边界。
所有新增结论是有明确前件的纸面证明；不宣称已取得原生嵌套协议、重复准备、
全仪器误差证书、有限样本独立性或物理时空重建。

<a id="section-1"></a>

## 1 固定来源与本轮推进位置

本轮固定 `dev` 提交为

`98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa`，

时间为 2026-10-31 02:14:07（新加坡）。比较基线为 v33 的

`9b2366610a50c2bf7e2b09cda7004b94224202ee`。

完整 theory 与 D5 子树均未被截断；相对基线有 6 个 theory 文件和 13 个 Lean 文件变化。
本稿的直接量子依据是续卷 II 纯追加的 §§117–120；
新 ROC 反例用于限制信息钟的判决解释。Typed、Actual-cut、Periodic-clock、
Output-resolved instrument closure 与 Records time arrow 在该次比较中未变。
新入库的旧作者稿不构成独立认证。[1](#bib-head)、[2](#bib-quantum)、[3](#bib-roc)、[4](#bib-archive)

本体仍为一个固定正归一态 $(\mathcal A,\omega)$。
系统、辅助坐标、记录、准备程序、计算器及内部索引都属于同一整体。
局部条件态或张量表示是内部接口表示，不引入外部观察者或外部物理时间。
但静态正线性态的存在，没有自动证明某个局部输入坐标与实际记录之间的全部概率对应。
本稿在下表中明确各层前件。

| 层次 | 本稿实际使用的结构 | 仍需单独取得的内容 |
| --- | --- | --- |
| 整体与关系 | 固定 $(\mathcal A,\omega)$，内部记录与条件化 | 具体输入到实际读口的识别 |
| 标量响应 | $m_0=g(t)$，二元归一，黄金嵌套缺陷 | 标量性、跨协议事件对应与测试权限 |
| 完整输出 | 全结果旗标与保留量子载体的半迹误差 | 失败处理、准备、跨层误差与尾模 |
| 有限观察器 | 有理比较、窗口计数与有限输出表 | 原生控制实现、安装与运行费用 |

全文未运行 Lean、CAS、数学数值实验或门字枚举。所称定理证明是下文给出的纸面推导；
引用 Lean 文件时仅报告源码内的命题和证明内容。

<a id="section-1-1"></a>

### 1.1 项目新增的强非识别结论

置

$$
x=\frac{\sqrt5-1}{2},\qquad\varphi=x^{-1},\qquad x^2=1-x,
 \qquad \rho_*=(1+x^2)^{-1}.
$$

项目 §117 在同一十三维旧源、八十九维全载体、二十六维代码及六十三维补空间上，
固定同一 ready 输入、原生控制、扩大终端以及每个正质量结果的纯投影后继。
令

$$
\mathcal A_0=\{x,x^2,x^3,1-x^3,\rho_*,1-\rho_*\},\qquad
 R(t)=\prod_{a\in\mathcal A_0}(t-a),
$$

<a id="eq:sourcefamily"></a>

$$
h(t)=t(1-t)(2t-1)R(t)^2,\qquad
 g_\lambda(t)=t+\lambda h(t),\quad -1\le\lambda\le1.
                                                        \tag{1}
$$

计算记录零的实际质量为 $g_\lambda(\|M_0\chi\|^2)$，后继仍为 $[M_0\chi]$。
规则固定、解析、端点确定、归一、标签交换协变；所有当前指定质量和有限供应合同都成立。
它们定义在纯输入上，源文没有声称其混态延拓仿射或为线性 CP 仪器。[2](#bib-quantum)

源 §119 对任意不同的 $\lambda,\mu\in[-1,1]$，给允许的精确两次 $K_9$ 调用事件 $\mathcal E$，使

<a id="eq:sourcegap"></a>

$$
|\mathbb P_\lambda(\mathcal E)-\mathbb P_\mu(\mathcal E)|
 =|\lambda-\mu|\Gamma(x^4)>0,\qquad
 \Gamma(t)=t(1-t)(1-2t)R(t)^2.
                                                        \tag{2}
$$

同一有限初始化／耦合供应序列，在原制备 $p_\dagger=11$ 的第三设置上，记录差还趋于
$|\lambda-\mu|\Gamma(x^5)>0$。因此这里不只是更换后继的一般仪器反例；
它保持全部当前源特定合同，连纯后继也相同。
缺口位于**其它允许输入上的实际记录质量**。[2](#bib-quantum)
这里的非识别是已列局部资料不能唯一确定一个完整操作模型；
它不声称同一个已固定 $\omega$ 上的同一已识别事件可以有两个质量。
比较中的 $\lambda$ 也不是真实整体随观察切换的动态参数。

源 §120.2 同时给清楚的正向接口：若另证所有纯输入的实际记录由同一效果
$0\le B\le I$ 表示，端点确定性迫使 $B=M_0$。
事实上，对 $u\in\operatorname{ran}M_0$，
$\langle u,(I-B)u\rangle=0$ 推出 $Bu=u$；
对 $v\in\ker M_0$，$\langle v,Bv\rangle=0$ 推出 $Bv=0$。
这便强制 $g(t)=t$。取得固定效果表示仍是额外义务；本稿下面给另一种较具体的条件性闭合。

> 编者注（符号作用域）：本段所引 §120.2 的 M₀ 是原源中的计算结果零投影，效果表示的结论 B=M₀ 在该投影语境下成立；它不是第 3 节式 [(10)](#eq:qnd) 中另行定义的 QND Kraus 算子 M₀。此处保留原稿记号，两个作用域分别理解。

<a id="section-2"></a>

## 2 黄金嵌套：以跨输入关系关闭记录余量

<a id="statement-2.1"></a>

#### 定义 2.1（标量二元规则与两类缺陷）

本节只研究同一个函数 $g:[0,1]\to[0,1]$ 表示的记录律
$m_0(\chi)=g(\|M_0\chi\|^2)$、$m_1=1-m_0$。
定义互补缺陷与黄金嵌套缺陷

<a id="eq:defects"></a>

$$
c=\sup_{t\in[0,1]}|g(1-t)+g(t)-1|,
 \qquad
 \eta=\sup_{t\in[0,1]}|g(xt)-g(x)g(t)|.
                                                        \tag{3}
$$

精确嵌套有明确的额外操作含义：某个直接输入的事件与一个分两层取得的事件，
其实际概率被证明相同，后者两层质量分别为 $g(x)$ 与 $g(t)$。
普通概率树只给 $\mathbb P(A\cap B)=\mathbb P(A)\mathbb P(B\mid A)$；
**把左侧进一步认同为另一输入的 $g(xt)$，才是新增关系。**
相同硬件、同一静态整体或相同平方范数都不自动供应这一步。
本节没有证明一般射线／历史依赖规则已经可写成同一个标量 $g$。

<a id="prop:finiteanchors"></a>

#### 命题 2.2（有限点校准的函数类障碍）

给定任意有限且在 $a\mapsto1-a$ 下闭合的集合 $A\subset(0,1)$，
存在不恒等于 $t$ 的实解析、严格递增函数 $g:[0,1]\to[0,1]$，满足
$g(0)=0,g(1)=1,g(1-t)=1-g(t)$，且 $g(a)=a$ 对全部 $a\in A$ 成立。

**证明。**

取 $H_A(t)=t(1-t)(2t-1)\prod_{a\in A}(t-a)^2$，
令 $g=t+\lambda H_A$。
有 $H_A(1-t)=-H_A(t)$、$|H_A(t)|\le t(1-t)$。
取 $0<|\lambda|\le1$ 得
$t^2\le g(t)\le1-(1-t)^2$，保证值域和端点；
再取 $|\lambda|\|H'_A\|_\infty<1$ 便有 $g'>0$。
多项式非零而在所有节点为零，完成证明。

∎

这是一般函数类的非唯一性，不能在未核对原生合同和可达输入之前，
把任意新多项式都宣称为新的全原生反模型。
对一个已完全分类的一参数族，有限额外测试当然可能足以定参数。

<a id="thm:goldenclosure"></a>

#### 定理 2.3（黄金嵌套的自校准与全域稳定性）

对定义 [(3)](#eq:defects) 的任意 $g$，

<a id="eq:closure"></a>

$$
\boxed{|g(x)-x|\le x(\eta+c),\qquad
 \|g-\mathrm{id}\|_\infty\le\varphi^3(\eta+c).}
                                                        \tag{4}
$$

特别地，精确互补与精确黄金嵌套推出 $g(t)=t$ 对全部 $t$ 成立。
若已经取得精确校准 $g(x)=x$，则较紧的有效界为

<a id="eq:calibratedclosure"></a>

$$
\boxed{\|g-\mathrm{id}\|_\infty\le\varphi^2(\eta+c).}
                                                        \tag{5}
$$

不要求连续性、可测性或单调性；这些常数不宣称为最优。

**证明。**

记 $a=g(x)$、$E_*=\eta+c$。在嵌套式取 $t=x$，由 $x^2=1-x$ 得
$|a^2+a-1|\le E_*$。
因

$$
a^2+a-1=(a-x)(a+x+1),\qquad a+x+1\ge1+x=x^{-1},
$$

有 $|a-x|\le xE_*$。
置 $f(t)=g(t)-t$、$M=\sup|f|\le1$，则

$$
|f(xt)-xf(t)|\le\eta+|a-x|\,g(t)\le\eta+xE_*=:b_*.
$$

对 $u\le x$，写 $u=xt$，得到 $|f(u)|\le xM+b_*$。
对 $u\ge1-x$，反射到 $1-u\le x$，得到 $|f(u)|\le xM+b_*+c$。
由于 $x>1/2$，两区间覆盖 $[0,1]$，故

$$
M\le xM+b_*+c,
 \qquad
 M\le\frac{(1+x)(\eta+c)}{1-x}=\varphi^3(\eta+c).
$$

上确界不需要取到。如果 $a=x$，同样论证可直接取 $b_*=\eta$，给式 [(5)](#eq:calibratedclosure)。
零缺陷情形即得恒等律。

∎

<a id="statement-2.4"></a>

#### 推论 2.4（项目一参数族的单个分离关系）

对式 [(1)](#eq:sourcefamily)，

<a id="eq:singlewitness"></a>

$$
g_\lambda(x^4)-g_\lambda(x)g_\lambda(x^3)
 =-\lambda\Gamma(x^4).
                                                        \tag{6}
$$

因此，新增该处精确嵌套关系即迫使该族的 $\lambda=0$；若残差至多 $\beta$，则
$|\lambda|\le\beta/\Gamma(x^4)$。

**证明。**

源节点给 $g_\lambda(x)=x$、$g_\lambda(x^3)=x^3$，
而 $h(x^4)=-\Gamma(x^4)$ 且源 §119 已证 $\Gamma(x^4)>0$。直接相减即可。

∎

该处直接记录事件已有原生见证，但它与嵌套事件的实际等价尚未供应。
这个推论只排除已知族的余量，不将单点校准升级成任意未知函数的全域识别。

<a id="prop:target"></a>

#### 命题 2.5（有限目标轨道证书）

设互补关系精确，令 $\Delta(u)=g(xu)-xg(u)$，并定义

$$
T(t)=\begin{cases}t/x,&t\le x,\\(1-t)/x,&t>x.\end{cases}
$$

固定目标 $t_0$，令 $t_{j+1}=T(t_j)$。则对任意 $N\ge1$，

<a id="eq:orbitcert"></a>

$$
\boxed{|g(t_0)-t_0|
 \le x^N+\sum_{j=0}^{N-1}x^j|\Delta(t_{j+1})|.}
                                                        \tag{7}
$$

若这 $N$ 个残差均认证至多 $\delta$，右侧至多
$x^N+\delta(1-x^N)/(1-x)$。

**证明。**

$T$ 的值在 $[0,1]$。对 $f=g-\mathrm{id}$，每步有
$f(t)=s(t)[xf(Tt)+\Delta(Tt)]$，其中 $s(t)=1$ 或 $-1$。
迭代、取绝对值，并用 $\|f\|_\infty\le1$ 即得。

∎

这只认证指定目标；所需轨道输入与概率残差能否实际取得，仍是独立前件。
它不要求共同 Lipschitz 模，也不把有限轨道等同于全域测试。

<a id="statement-2.6"></a>

#### 推论 2.6（共同连续模下的有限网格证书）

若另外取得整个候选规则类共同的 Lipschitz 常数 $K$，互补精确，
网格覆盖半径为 $h$，网格上的嵌套残差至多 $\eta_0$，则

<a id="eq:mesh"></a>

$$
\|g-\mathrm{id}\|_\infty
 \le\varphi^3[\eta_0+(1+x)Kh].
                                                        \tag{8}
$$

若每个截断到 $[0,1]$ 的函数值有认证误差 $\nu$，可将 $\eta_0$ 换成
$\eta_{\rm observed}+3\nu$。

**证明。**

残差函数 $g(xt)-g(x)g(t)$ 的 Lipschitz 常数至多 $(x+1)K$。
从最近网格点延拓后用定理 [2.3](#thm:goldenclosure)。
一个单值误差加一个两因子乘积误差至多 $\nu+2\nu$，得到末式。

∎

源 §118 的 $K=6$ 属于其构造的反模型族，不是全部未知记录规则自动共享的先验。
有限样本如何供应这些认证区间，还需要重复准备和统计合同。

<a id="section-3"></a>

## 3 从记录质量到完整输出误差

<a id="statement-3.1"></a>

#### 引理 3.1（相同后继下质量误差的确切转换）

若二元读口在两个模型中有相同归一后继 $\rho_0,\rho_1$，
质量分别为 $(g(t),1-g(t))$ 与 $(t,1-t)$，则完整旗标输出满足

<a id="eq:masscq"></a>

$$
\frac12\left\|
 g(t)\rho_0\oplus[1-g(t)]\rho_1
 -t\rho_0\oplus(1-t)\rho_1\right\|_1=|g(t)-t|.
                                                        \tag{9}
$$

零质量端点按零块解释。若实际后继另有半迹误差 $k_0,k_1$，则上界变成
$|g(t)-t|+g(t)k_0+[1-g(t)]k_1$。

**证明。**

块直和的迹范数相加，且归一正态的迹范数为一，给等式。
实际后继情形先用相同实际质量替换后继，再用三角不等式。

∎

因此黄金闭包误差在*相同已取得后继*的接口上可以转成完整输出误差。
只知道概率接近、却不控制后继时，不得使用这一转换。
也不能把纯输入上的这个界，未经混态或实际可达输入核对就宣布为全仪器界。

以下固定非平凡投影 $P$、$E=I-P$，并明确给出数学参考仪器

<a id="eq:qnd"></a>

$$
M_0=\sqrt{x}\,E+\sqrt{s}\,P,\qquad
 M_1=xE+\sqrt{1-s}\,e^{i\theta}P,
 \qquad 0<s<x.
                                                        \tag{10}
$$

它完整，因为 $x+x^2=1$。记

<a id="eq:rg"></a>

$$
g_*=x-s>0,\qquad
 r=\sqrt{xs}+x\sqrt{1-s}\in(0,1),\qquad U(q)=\sqrt{q(1-q)}.
                                                        \tag{11}
$$

这里 $g_*$ 是两扇区概率差，与上一节的函数 $g$ 不同。
$r<1$ 由两不同归一似然向量的严格 Cauchy--Schwarz 不等式给出。

<a id="statement-3.2"></a>

#### 定义 3.2（同输入的完整误差合同）

实际历史 $h$ 后的完整归一输出写为
$\mathcal I_{n,h}(\rho)=\bigoplus_y\tau_y$；参考为
$\mathcal J(\rho)=\bigoplus_{y=0,1}M_y\rho M_y^*$，
在额外标签上补零。结果标记取自一个已给定的共同有限字母表，包含 $0,1$ 和失败标记。
假设有确定数 $e_n\ge0$，使对每个正质量实际历史和其实际输入态

<a id="eq:completeerror"></a>

$$
\frac12\|\mathcal I_{n,h}(\rho_h)-\mathcal J(\rho_h)\|_1\le e_n.
                                                        \tag{12}
$$

比较包括全部失败结果，以及后续操作可访问的整个保留量子载体。

参考 $\mathcal J$ 是线性 CPTP 旗标通道。
下面的误差传播只需实际输出在实际输入上合法归一且满足 [(12)](#eq:completeerror)，
不需要从未知实际规则免费推出一个全域线性 CP 延拓。
如果只证明某个丢弃记忆后的边缘距离，则未取得本定义。

<a id="statement-3.3"></a>

#### 引理 3.3（完整误差的三个直接消费者）

令 $q_n=\operatorname{Tr}(P\rho_n)$，$p_n$ 为实际下一次标签零的条件概率。
在 [(12)](#eq:completeerror) 下，

<a id="eq:driftread"></a>

$$
\left|\mathbb E(q_{n+1}\mid\mathcal F_n)-q_n\right|\le e_n,
 \qquad |p_n-(x-g_*q_n)|\le e_n,                         \tag{13}
$$

<a id="eq:impurity"></a>

$$
\mathbb E[U(q_{n+1})\mid\mathcal F_n]\le rU(q_n)+\sqrt{2e_n}.
                                                        \tag{14}
$$

**证明。**

完整参考输出的总指针质量等于 $q_n$，零标签质量等于 $x-g_*q_n$。
两者都是归一旗标态上的效果期望，故半迹距离分别控制其差。
为证明末式，把每个输出块再以 $\{P,E\}$ 取迹，得到经典归一分布
$(a_y,b_y)_y$。记其平方根向量为 $v$，参考的为 $w$。
则 $\|v\|=\|w\|=1$，且

$$
\|v-w\|^2\le\sum_i|v_i^2-w_i^2|\le2e_n.
$$

令 $S$ 交换每对扇区坐标，则
$\sum_y\sqrt{a_yb_y}=\tfrac12\langle v,Sv\rangle$。
两分布的此量之差至多 $\|v-w\|\le\sqrt{2e_n}$。
该量正是实际 $\mathbb E U(q_{n+1})$；零质量块按零延拓。
参考逐结果 Bayes 公式给 $\mathbb E_0U(q_{n+1})=rU(q_n)$，完成证明。

∎

<a id="lem:hybrid"></a>

#### 引理 3.4（有限窗口的完整记录组合界）

固定深度 $m$ 的任意正质量实际历史，从其同一个实际条件态出发，
分别执行 $L$ 层实际过程和 $L$ 层参考过程，并保留全部窗口标签与量子载体。
则它们的归一 CQ 态满足

<a id="eq:hybrid"></a>

$$
\frac12\|\Omega_L^{\rm act}-\Omega_L^{\rm ref}\|_1
 \le\sum_{j=m}^{m+L-1}e_j.
                                                        \tag{15}
$$

**证明。**

在第 $k$ 层的实际各历史块上，把下一次实际输出替换为同输入的参考输出。
按实际块质量加权，替换误差至多 $e_{m+k}$。
再把参考旗标通道施于实际与参考两套第 $k$ 层 CQ 态；
其线性和迹距离收缩性，使旧误差不增加。
因此 $d_{k+1}\le d_k+e_{m+k}$，且 $d_0=0$，归纳即得。
这只在实际输入上调用 [(12)](#eq:completeerror)，未要求未知实际映射对任意输入线性。

∎

<a id="section-4"></a>

## 4 不取得初始权重的稳健有限观察器

<a id="lem:test"></a>

#### 引理 4.1（有限精度的两扇区窗口判别）

对参考仪器 [(10)](#eq:qnd) 的长度 $L$ 记录 $h$，令 $k$ 为零的个数，
两纯扇区记录概率分别为

<a id="eq:windowlikelihood"></a>

$$
A_h=x^{2L-k},\qquad B_h=s^k(1-s)^{L-k},\qquad
 v_h=\frac{B_h}{A_h+B_h}.
                                                        \tag{16}
$$

只把 $v_h$ 计算为误差至多 $1/6$ 的有理数 $\widehat v_h$；
若 $\widehat v_h\ge1/2$ 则选 $C(h)=1$，否则选 $C(h)=0$。
那么两个纯扇区各自的误判率都至多 $\sqrt2 r^L$。

**证明。**

两个似然均严格正。若选 $1$，则 $v_h\ge1/3$，即 $B_h\ge A_h/2$，
所以在纯 $E$ 扇区的错误集合上 $A_h\le\sqrt2\sqrt{A_hB_h}$。
同理，选 $0$ 时 $v_h\le2/3$，在纯 $P$ 扇区的错误集合上
$B_h\le\sqrt2\sqrt{A_hB_h}$。
逐字求和，并用乘积结构

$$
\sum_{|h|=L}\sqrt{A_hB_h}
 =\left(\sqrt{xs}+\sqrt{x^2(1-s)}\right)^L=r^L
$$

便得两界。这里只比较两个有理数，不需要判定真实 $v_h$ 是否恰等于 $1/2$。

∎

该检验不使用实际 $q_0$。等先验量 $v_h$ 只是计算判别表的方法，
没有把实际初始态替换成等权混合态。

<a id="thm:window"></a>

#### 定理 4.2（未知初值、实际误差与全部未来的窗口界）

假设完整误差合同 [(12)](#eq:completeerror) 成立，且

$$
D_m:=\sum_{j\ge m}e_j<\infty.
$$

先等待 $m$ 层，随后读取 $L\ge1$ 层，在 $N=m+L$ 用引理 [4.1](#lem:test) 选 $C$。
若有额外失败标签，观察器可固定映射为二元符号零后计数；
实际完整记录律仍保留全部标签，参考在额外标签上的质量为零。
则对任意初始实际态、任意 $0<b\le1$，

<a id="eq:mainwindow"></a>

$$
\boxed{
 \mathbb P_{\rm act}\!\left(\sup_{n\ge N}|q_n-C|\ge b\right)
 \le\min\left\{1,\frac{\sqrt2r^L+D_m}{b}\right\}.}
                                                        \tag{17}
$$

同一界也在给定任意正质量 $\mathcal F_m$ 历史后成立。
它不要求取得实际 $q_0$、实际后验数值或先证明 $q_n$ 几乎必然极化。

**证明。**

固定窗口开始的实际历史和条件态 $\rho_m$。
对全部窗口记录定义效果

$$
F=\bigoplus_h[(1-C(h))P+C(h)E],\qquad0\le F\le I.
$$

参考输出的 $F$ 期望是两个纯扇区误判率按未知
$q_m=\operatorname{Tr}(P\rho_m)$ 的混合；相干交叉块不贡献这两个投影的迹。
由引理 [4.1](#lem:test)，该期望至多 $\sqrt2r^L$，包括 $q_m=0,1$。
引理 [3.4](#lem:hybrid) 和效果期望界遂给

<a id="eq:mispoint"></a>

$$
\mathbb E_{\rm act}[a_N\mid\mathcal F_m]
 \le\sqrt2r^L+\sum_{j=m}^{N-1}e_j,
 \qquad a_N=(1-C)q_N+C(1-q_N).                       \tag{18}
$$

由式 [(13)](#eq:driftread)，$q_n+D_n$ 与 $1-q_n+D_n$ 是非负超鞅。
给定 $\mathcal F_N$ 与 $C$，条件最大不等式给

$$
\mathbb P\!\left(\sup_{n\ge N}|q_n-C|\ge b\mid\mathcal F_N\right)
 \le\min\{1,(a_N+D_N)/b\}.
$$

先在有限未来区间证明，再令区间增大；若上确界只在极限达到阈值，
从 $b-\epsilon$ 递增逼近 $b$ 即涵盖。
条件化到 $\mathcal F_m$，用 [(18)](#eq:mispoint) 及

$$
\sum_{j=m}^{N-1}e_j+D_N=D_m
$$

得到 [(17)](#eq:mainwindow)。最后对开始历史取平均给无条件界。

∎

这个证明避免把每一步条件态误差除以极小历史概率。
窗口内先比较*完整带质量输出*，再对同一记录函数施加效果，
最后用实际漂移尾控制无限未来。给定 $\mathcal F_m$ 的保证位于窗口开始时；
它不表示每个稀有的窗口结果在 $\mathcal F_N$ 条件下都具有相同风险。
$p_n$ 始终指实际物理标签零的概率；额外结果按零计数仅属于预测器的内部更新，
不把其物理概率加进 $p_n$。

<a id="cor:fsm"></a>

#### 推论 4.3（可计算尾证书供应有限状态概率预测）

另设 $s$ 可计算，且取得可计算有理上界
$\overline D_m\ge D_m$、$\overline D_m\to0$。
给定有理 $0<\varepsilon<g_*/2$、$0<\delta<1$，可有效选择有限 $m,L$，
构造确定观察器，使对每个初始实际态都有

<a id="eq:prediction"></a>

$$
\boxed{\mathbb P_{\rm act}
 \{\sup_{n\ge m+L}|\widehat p_n-p_n|\le\varepsilon\}
 \ge1-\delta.}                                           \tag{19}
$$

逻辑状态数可取

<a id="eq:states"></a>

$$
\boxed{M\le m+\frac{L(L+1)}2+2.}                       \tag{20}
$$

**证明。**

选正有理 $b$ 满足 $g_*b<\varepsilon/3$。
先找 $m$ 使

$$
\overline D_m<\min(\delta b/2,\varepsilon/3),
$$

再从可计算 $r<1$ 取得有理 $\overline r\in(r,1)$，逐个检查有理不等式
$2\overline r^L<\delta b/2$ 来选择 $L\ge1$，从而保证 $\sqrt2r^L<\delta b/2$。
可计算性、严格不等式的余量及相应收敛性保证这些搜索终止。
不用精确计算对数的取整，也不用判断两个可计算实数相等。

在窗口前设 $m$ 个等待状态；窗口中存储 $(j,k)$，其中
$0\le j<L$、$0\le k\le j$。
第 $L$ 个符号到来时按预先计算的有理判别表进入两个吸收预测态之一。
这给式 [(20)](#eq:states)。额外标签固定按零计数，无须将其从实际概率律删去。

两个吸收态分别输出 $x$、$s$ 的有理近似，误差小于 $\varepsilon/3$。
在定理 [4.2](#thm:window) 的成功事件上，对全部 $n\ge N$，

$$
|\widehat p_n-p_n|
 \le\varepsilon/3+g_*|q_n-C|+e_n
 <\varepsilon/3+\varepsilon/3+\overline D_m<\varepsilon.
$$

坏事件概率至多 $\delta$，从而得到预测保证。

∎

等待和窗口深度由观察器自己的有限控制态计数；没有借入免费的外部时钟。
吸收的是*预测器的逻辑状态*，实际读口仍按已给合同继续运行。
表的计算、安装、输出位数、真实记录、重复准备和执行模块分别计费。
定理既不实现自由擦除，也不宣称一个固定有限封闭酉系统可永远无成本地产生新记录。

<a id="prop:tail"></a>

#### 命题 4.4（有效尾模不能由可求和性自动推出）

存在可计算非负有理序列 $(e_n)$，$\sum_ne_n\le1/2$，
但不存在可计算有理 $\overline D_N\to0$ 使
$\sum_{n\ge N}e_n\le\overline D_N$。

**证明。**

按可计算阶段有限模拟各图灵机。第 $k$ 台机器第一次被确认停机时，
只支付一次 $2^{-k-2}$（$k=0,1,\ldots$）。每个阶段支付和 $e_n$ 可计算，
总支付不超过 $1/2$。
若存在所述尾界，对给定 $k$ 搜索 $\overline D_N<2^{-k-2}$。
模拟到阶段 $N-1$：若该机还未被确认停机，以后也不能停机，
否则尾和至少含这笔支付。于是可以判定停机问题，矛盾。

∎

这个例子不指认任何实际编译器有不可计算误差；它证明不能删掉推论中的有效性前件。

<a id="statement-4.5"></a>

#### 命题 4.5（趋零误差不足以永久冻结）

即使每层误差 $e_n\to0$，且实际 $U(q_n)=0$ 恒成立，
实际扇区仍可几乎必然交换无穷次。

**证明。**

在二维载体取上述 QND 参考，从一个扇区端点开始。
每次参考读出后，独立地以概率 $e_n=1/(n+2)$ 交换两扇区，并保留交换标志。
把参考完整输出的交换标志固定为零，实际与参考的半迹距离至多 $e_n$。
每步后的态仍在某个端点，故杂质为零。
对任意 $n_0$，从此再无交换的概率为

$$
\lim_{M\to\infty}\prod_{n=n_0}^{M}\left(1-\frac1{n+2}\right)
 =\lim_{M\to\infty}\frac{n_0+1}{M+2}=0.
$$

对 $n_0$ 取可数并，得到交换几乎必然发生无穷多次，$q_n$ 不收敛。

∎

这限制的是永久端点冻结；若交换标志已保留，两状态机可以追踪它，
所以本命题不证明全部有限状态预测都不可能。

<a id="section-5"></a>

## 5 区间校准：从零时刻的障碍与条件出证

本节的正向后验公式明确使用精确 QND 仪器；
一般实际偏离不能仅被解释成一个先验区间。

<a id="thm:initial"></a>

#### 定理 5.1（从零时刻开始的未知校准障碍）

若只知 $q_0\in[\ell,u]$，同一个确定预测器欲对每个允许 $q_0$ 保证

$$
\mathbb P_{q_0}\{\sup_{n\ge0}|\widehat p_n-p_n|\le\varepsilon\}
 \ge1-\delta,\qquad\delta<1,
$$

则必要有

<a id="eq:initbarrier"></a>

$$
\boxed{\varepsilon\ge\frac{g_*(u-\ell)}2.}              \tag{21}
$$

**证明。**

任何结果出现前，$\widehat p_0$ 是同一个数；
真实 $p_0=x-g_*q_0$ 遍历长度 $g_*(u-\ell)$ 的区间。
单点逼近整个区间的最小最大误差为其半宽。
若不满足此界，对某个初值，第零时刻已经确定失败，成功概率为零。

∎

所以推论 [4.3](#cor:fsm) 的起点 $m+L$ 是实质条件，不能改写成从零时刻的任意精度保证。
这个下界针对确定单值输出；随机化、区间输出或新增校准需要另列问题。

<a id="prop:interval"></a>

#### 命题 5.2（先验区间的精确传播与有限条件证书）

设 $0<\ell\le q_0\le u<1$，正支持似然已知，
累计似然比为 $\Lambda_n>0$。
置 $T_\Lambda(q)=q\Lambda/(1-q+q\Lambda)$，则

<a id="eq:interval"></a>

$$
q_n\in[\underline q_n,\overline q_n]
 =[T_{\Lambda_n}(\ell),T_{\Lambda_n}(u)].                \tag{22}
$$

令 $D=\operatorname{logit} u-\operatorname{logit}\ell$，则

<a id="eq:width"></a>

$$
\sup_{\Lambda>0}[T_\Lambda(u)-T_\Lambda(\ell)]
 =\tanh(D/4).                                          \tag{23}
$$

对固定参考读口，取 $0<\alpha<1/2$，在首次
$\overline q_n\le\alpha$ 或 $\underline q_n\ge1-\alpha$ 时选对应扇区。
该数学停时 $\tau_\alpha$ 几乎必然有限；其条件最终错误概率至多 $\alpha$，
并有统一尾界

<a id="eq:intervaltail"></a>

$$
\mathbb P_{q_0}(\tau_\alpha>n)
 \le\min\left\{1,\frac{r^n}{2\sqrt{a_\alpha(1-a_\alpha)}}\right\},
 \quad a_\alpha=\frac{1}{1+\exp[-(\operatorname{logit}\alpha-D)]}.
                                                        \tag{24}
$$

**证明。**

Bayes 公式给
$\operatorname{logit} T_\Lambda(q)=\operatorname{logit} q+\log\Lambda$，且 $T_\Lambda$ 单调递增，
因此区间及其固定 logit 宽度成立。
记 logistic 函数为 $S(z)=(1+e^{-z})^{-1}$。
两参数间距为 $D$ 时，

$$
S(z+D/2)-S(z-D/2)
 =\frac{\sinh(D/2)}{\cosh z+\cosh(D/2)}
$$

在 $z=0$ 最大，给式 [(23)](#eq:width)。
由精确 QND 的鞅及 $\mathbb E U(q_n)=U(q_0)r^n$，
$q_n\to B\in\{0,1\}$ 几乎必然，且
$q_n=\mathbb P(B=1\mid\mathcal F_n)$。
有界的初始 logit 差使两个区间端点趋向同一个 $B$，所以停时有限。
出证时真实后验被相应端点约束，故条件错误至多 $\alpha$。
若到 $n$ 仍未出证，两个区间端点分别跨过 $\alpha$ 和 $1-\alpha$ 的内部侧，
固定 logit 差推出 $a_\alpha<q_n<1-a_\alpha$。
最后用 $\mathbb E U(q_n)\le r^n/2$ 和 Markov 不等式给尾界。

∎

当 $\ell,u,s$ 可计算、$\alpha$ 为给定正有理数时，每层计算两个端点的有理外包，
其单侧误差至多 $\alpha/2$，直接将这些有理端点与 $\alpha$、$1-\alpha$ 比较并出证。
实际停时不晚于精确区间阈值为 $\alpha/2$ 的数学停时，所以几乎必然有限，
等待尾在式 [(24)](#eq:intervaltail) 中以 $\alpha/2$ 替换 $\alpha$。
精确区间停时只用于证明，不作为内部计算原语。
若先验区间含零或一，以上有限 logit 论证不适用；例如 $[0,u]$ 的下端点始终为零，
阻止这种区间规则认证 $P$。
这不妨碍定理 [4.2](#thm:window) 的每个初值统一、窗口前评价的概率保证。

<a id="section-6"></a>

## 6 信息钟控制重叠，但不唯一决定最优判决

v33 的信息钟 $\mathcal T_n=-\log R_n$ 使用两扇区记录律的亲和
$R_n$，在固定读口为 $R_n=r^n$。
它精确控制 $\mathbb E U(q_n)$，却不能把全部二元决策目标都化为一个数。[5](#bib-v33)
下面给出此处所需的经典亲和界及显式等号构造，不作世界范围的新颖性主张。

<a id="thm:risk"></a>

#### 定理 6.1（给定重叠的 Bayes 风险夹界及等先验尖锐性）

设两扇区记录分布为 $A_h,B_h$，先验为 $1-q,q$。
定义带先验重叠与最佳记录判决错误率

$$
C=\sum_h\sqrt{(1-q)A_h\,qB_h},\qquad
 e_{\rm Bayes}=\sum_h\min\{(1-q)A_h,qB_h\}.
$$

则

<a id="eq:bayesbounds"></a>

$$
\boxed{\frac{1-\sqrt{1-4C^2}}2
 \le e_{\rm Bayes}\le\min\{C,q,1-q\}.}                \tag{25}
$$

当 $q=1/2$、$R=\sum_h\sqrt{A_hB_h}$ 时，

<a id="eq:equalbounds"></a>

$$
\frac{1-\sqrt{1-R^2}}2\le e_{\rm Bayes}\le R/2,
                                                        \tag{26}
$$

且任意给定 $R\in[0,1]$ 的两端界都可由有限记录分布达到。

**证明。**

令 $a_h=(1-q)A_h,b_h=qB_h,m_h=\min(a_h,b_h),M_h=\max(a_h,b_h)$。
逐记录选择较大联合质量给最小错误 $\sum m_h$。
由 $m_h\le\sqrt{a_hb_h}$ 得上界；总先验质量也各自给上界。
Cauchy--Schwarz 给

$$
C=\sum_h\sqrt{m_hM_h}
 \le\sqrt{\left(\sum m_h\right)\left(\sum M_h\right)}
 =\sqrt{e_{\rm Bayes}(1-e_{\rm Bayes})}.
$$

又 $e_{\rm Bayes}\le1/2$，解此二次不等式得下界。
等先验时，令 $t=\sqrt{1-R^2}$。
二元分布 $A=((1+t)/2,(1-t)/2)$、$B=((1-t)/2,(1+t)/2)$ 达到下界。
三元分布 $A=(1-R,R,0)$、$B=(0,R,1-R)$ 达到上界。
直接代入其重叠与逐记录最小质量即验证。

∎

因此同一个 $\mathcal T=-\log R$ 可对应不同最佳判决错误。
这是固定记录分布上的最优判决；进一步优化量子测量本身，又是另一个优化域。

<a id="section-6-1"></a>

### 6.1 项目新 ROC 反例的准确用途

新 Lean 源 `FidelityMeasurementROCRefutation` 包含
`theorem result : ¬ claim`，否定“排序保真度测量的每个累计 ROC 点均最优”。
源反例为满秩密度矩阵

$$
\rho=\frac1{20}\begin{pmatrix}2&1&1\\1&10&1\\1&1&8\end{pmatrix},\qquad
 \sigma=\frac1{40}\begin{pmatrix}16&4&2\\4&20&1\\2&1&4\end{pmatrix}.
$$

其保真度可观测量为 $D=\operatorname{diag}(2,1,1/2)$。
第一坐标阈值效果与另一个合法效果的性能如下。[3](#bib-roc)

| 效果 | 假阳性 $\operatorname{Tr}(F\rho)$ | 真阳性 $\operatorname{Tr}(F\sigma)$ |
| --- | --- | --- |
| 第一坐标投影 | $1/10$ | $2/5$ |
| $F_*=vv^*/1382$, $v=(37,2,-3)^{\mathsf T}$ | $1/10$ | $5539/13820$ |

其中 $\|v\|^2=1382$，故 $F_*$ 是投影；真阳性改善为 $11/13820>0$。
源证明还核对正定性、$\sigma=D\rho D$ 和相应平方根可观测量身份。
它没有否定保真度优化本身，也没有形式化本稿的黄金闭包或有限观察器定理。
本轮仅审阅源码，未重跑 Lean。

<a id="section-7"></a>

## 7 内生资源与下一条应完成的项目接口

本稿把当前缺口和可用消费者接成三步证明依赖：

1. 实际跨输入嵌套对应与互补，经定理 [2.3](#thm:goldenclosure) 给标量记录质量的统一界。
2. 同后继／完整后继与准备误差另行核对，才取得完整同输入误差 $e_n$ 及有效尾界 $\overline D_m$。
3. 在共同实际协议上，定理 [4.2](#thm:window) 与推论 [4.3](#cor:fsm) 给未知初值下的有限窗口、全未来概率保证。

第一步是本稿新的条件闭包；第二步的取得工作尚未由项目现有合同完成。
误差分解、初始化、耦合、全部结果及未来可访问记忆必须在同一实际协议中被核对。
不能分别选取不同反事实模型中的有利前件，再声称一个共同实现已经存在。

若第 $j$ 次完整读口实际使用原生字长 $L_j^{\rm gate}$，
总调用量仍是 $G_N=\sum_{j<N}L_j^{\rm gate}$；
参考信息钟是 $\mathcal T_L=L\log(1/r)$。
二者都是内部协议的计量，但它们衡量不同对象。
有限预测器的状态上界不等于总物理存储上界；
逐精度存在有限原生字，也不等于已取得关于精度的计算长度界。

最直接的后续工作应是：针对一个明确可执行的嵌套事件族，
证明其跨输入对应；同时给相同实际读口的完整误差分解和可计算尾预算。
这会把目前的条件闭包推进为源特定的取得定理。
在完成该接口之前，本稿不从关系图、概率重叠或范数稳定性推导空间维度、
物理固有时、Lorentz 度规或引力场方程。

<a id="bibliography"></a>

## 固定来源与前篇

<a id="bib-head"></a>

**[1]**
项目固定提交，2026-10-31 02:14:07（新加坡），
[固定提交 98d92f3c4013](https://github.com/the-omega-institute/trureturing/commit/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa)。

<a id="bib-quantum"></a>

**[2]**
[AURIC quantum reconstruction continuation II](https://github.com/the-omega-institute/trureturing/blob/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)，
重点为 §§117–120；§§104–116 为其保留合同及既有消费者。

<a id="bib-roc"></a>

**[3]**
[FidelityMeasurementROCRefutation.lean](https://github.com/the-omega-institute/trureturing/blob/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa/D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.lean)，
定义 `claim`、显式三维见证及 `result`。

<a id="bib-archive"></a>

**[4]**
[AURIC native golden readout v32 作者稿归档](https://github.com/the-omega-institute/trureturing/blob/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa/docs/develop/theory/AURIC_NATIVE_GOLDEN_READOUT_INTERNAL_CONSERVATION_AND_PREDICTIVE_MEMORY_V32.md)。
其转换身份与历史快照应保持区分。

<a id="bib-v33"></a>

**[5]**
AURIC v33，*内生信息钟与可认证的有限观察者*，2026-10-31。
[完整 PDF](https://chatgpt.com/library?file_id=libfile_73dfa7e2dd5881918b85ca68d70ae237&account_id=personal)。
本稿续接其完整输出、信息钟、漂移超鞅与有限精度预测的条件结构。

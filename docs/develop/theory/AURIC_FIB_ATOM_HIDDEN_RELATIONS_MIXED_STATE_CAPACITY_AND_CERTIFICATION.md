# Auric FIB-ATOM：隐藏关系的混态容量与认证续卷

本卷沿用[隐藏关系统计、相位与接缝续卷 C-94–C-97](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS_CONTINUATION.md#94-五模式混态底面张量结构与完整双副本测量)
的任意五维密度算子、指定底面张量识别、实际双副本测量和固定均值容量。
这里的编号 C-94–C-97 指该卷，C-98–C-101 指本卷；每个统计结论保留其实际成对来源条件。

## 98. 全部成对试验上的随时有效认证

**假设 C-98.1（给定历史后的乘积来源零假设）。** 令 $\mathcal F_{n-1}$ 表示第 $n$ 轮前
全部已观察记录及允许的过去随机性。在给定该历史后，下一对的实际条件密度算子必须是

$$
\rho_n\otimes\rho_n,
\tag{C98.1}
$$

其中 $\rho_n$ 可依历史变化，并且其底面条件态 $\sigma_n$ 可分离。
当 $r_n=\operatorname{Tr}(P_{\mathrm b}\rho_n)>0$ 时按 C-94.2 定义 $\sigma_n$；
若 $r_n=0$，所有四符号概率为零，该轮为零记录。
这个零假设无需固定 $r,X,Y,Z$，也允许 $r_n=1$ 或边缘退化；
式 (C95.5) 的纯度比较不依赖严格内部条件。
若存在尚未包含在历史中的共同随机来源，条件配对律是
$\int\rho_z\otimes\rho_z\,d\pi(z)$，不能仅凭边缘相等把它改写成
$(\int\rho_z\,d\pi(z))^{\otimes2}$。

假设 C-98.1 只要求每个实际历史下的所列条件合同；跨轮 iid 并非本章前提。
轮内独立、轮内两份相同、跨轮 iid 是三个不同性质。

**定义 C-98.2（预先固定的对照、投注参数与全部试验计数）。** 在观察数据以前选择
比较 $--$ 与 $-+$，固定 $0<\lambda<1$、$0<\alpha<1$。
每轮执行式 (C94.9) 的完整测量，记录

$$
V_n=\begin{cases}
1,&--,\\
-1,&-+,\\
0,&+-,\ ++,\ \text{或未同时进入底面}.
\end{cases}
\qquad
E_0=1,\quad E_N=\prod_{n=1}^N(1+\lambda V_n).
\tag{C98.2}
$$

$N$ 计入全部成对试验，包含一份或两份底面选择失败及所有零记录。
令首次越界时刻为

$$
\tau=\inf\{N\ge1:E_N\ge1/\alpha\},\qquad\inf\varnothing=+\infty.
\tag{C98.3}
$$

越界时输出“拒绝给定历史下每轮底面均可分离的乘积来源合同”。
在另有固定同态来源前提时，这成为该固定条件态的纠缠认证。
对历史自适应来源，拒绝复合的全轮合同，不据此逐个判定某个历史状态或识别一个固定平稳态。

**定理 C-98.3（条件乘积零假设下的全时间误判界）。** 在假设 C-98.1 下，

$$
\Pr(\exists N\ge1:E_N\ge1/\alpha)\le\alpha.
\tag{C98.4}
$$

不需要知道 $r_n,X_n,Y_n,Z_n$，也不需要假定 $\tau$ 有限或可积。

证明。每个因子属于 $\{1-\lambda,1,1+\lambda\}$，严格为正，
且 $0<E_n\le(1+\lambda)^n$，所以各有限时刻可积。
条件于 $\mathcal F_{n-1}$，假设 C-98.1 允许对同一条件态使用式 (C97.1)，
因而

$$
\mathbb E[V_n\mid\mathcal F_{n-1}]
=q_{--}^{(n)}-q_{-+}^{(n)}
=\frac{r_n^2}{2}\bigl(\mathcal P^{(n)}-\mathcal P_B^{(n)}\bigr)\le0.
\tag{C98.5}
$$

$r_n=0$ 时同样成立。$E_{n-1}$ 对过去可测且非负，故

$$
\mathbb E[E_n\mid\mathcal F_{n-1}]
=E_{n-1}\bigl(1+\lambda\mathbb E[V_n\mid\mathcal F_{n-1}]\bigr)
\le E_{n-1}.
\tag{C98.6}
$$

所以 $E_n$ 是非负超鞅。为完整写出有界停止的步骤，固定整数 $N$，
$T=\tau\wedge N$。对 $k\le N$ 有路径恒等式

$$
E_T=1+\sum_{k=1}^N\mathbf1_{\{T\ge k\}}(E_k-E_{k-1}).
\tag{C98.7}
$$

$\{T\ge k\}$ 对 $\mathcal F_{k-1}$ 可测；各项可积，
对每项先取条件期望，由式 (C98.6) 得 $\mathbb E E_T\le1$。
在 $\{\tau\le N\}$ 上 $E_T=E_\tau\ge1/\alpha$，其余事件上仍非负。
于是

$$
\alpha^{-1}\Pr(\tau\le N)\le\mathbb E E_{\tau\wedge N}\le1.
\tag{C98.8}
$$

事件 $\{\tau\le N\}$ 随 $N$ 递增，其并为 $\{\tau<\infty\}$，
概率的下连续性给式 (C98.4)。这一步未对无界停止时刻直接套用可积性结论。证毕。

所用全时间机制是 Ville 的非负超鞅不等式；精确文献供应为
Howard、Ramdas、McAuliffe、Sekhon，*Time-uniform Chernoff bounds via nonnegative supermartingales*，
[arXiv:1808.03204v6](https://arxiv.org/abs/1808.03204v6)，§2.3 Lemma 1、式 (18)，
其 §6.1 给证明并归属 Ville。此处的具体因子由五模式双事件纯度差供应，
上面的有限停止推导给它在本条件零假设中的全部参数与风险范围。

**约定 C-98.4（有限截止、预先选择与算术成本）。** 可设置任意有限资源截止点；
截止仍未越界只输出“尚未认证”，不能输出“已证明可分离”。
定理控制的是整个越界事件，所以允许边读边停；
反复使用一个仅在固定样本数有效的阈值没有自动获得同一保证。
若观察数据后再从两个对照中挑选较显著者，不能沿用未经调整的原 $\alpha$。
例如预先给两个检验各分配 $\alpha/2$，再以并集界校准，才有一个直接的总风险方案。

若 $\lambda=a/b$、$\alpha=c/d$ 为预先给定的有理数，
$0<a<b$、$0<c<d$，记至 $N$ 轮的正负记录数为 $n_+,n_-$，则

$$
E_N=\frac{(b+a)^{n_+}(b-a)^{n_-}}{b^{n_++n_-}},\qquad
E_N\ge d/c\ \Longleftrightarrow\
c(b+a)^{n_+}(b-a)^{n_-}\ge d\,b^{n_++n_-}.
\tag{C98.9}
$$

这给有限整数的精确比较；零记录不改乘积但仍支付一次双副本试验。
分子分母的位长随非零记录数增长，故精确有理运算不具有免费位成本。
本章概率保证计数的是试验，未把算术时间、存储或制备实施成本计为零。

## 99. 相干承诺下的有限平均认证成本

**假设 C-99.1（固定 iid 来源与最低相干承诺）。** 固定 C-96 家族的一份状态、
固定 $r,X,Y$ 及其基，每轮提供实际独立相同的两份 $\rho_\gamma$，
跨轮完整测量结果独立同分布。给定 $0<\gamma_0<1$，承诺
$\gamma\in[\gamma_0,1]$，在观察数据前选择
$\lambda=\gamma_0^2$、$0<\alpha<1$，并沿用 C-98 的固定对照和停止规则。
以下所有 $\log$ 均为自然对数。

**定理 C-99.2（付费试验的有限平均值及超越界上限）。** 令

$$
h=w(r-w)>0,\qquad A=\log(1/\alpha)>0,
$$

$$
d(\lambda)=\frac{1+\lambda}{2}\log(1+\lambda)
+\frac{1-\lambda}{2}\log(1-\lambda).
\tag{C99.1}
$$

则 $d(\lambda)>0$、$\mathbb E\tau<\infty$，并有

$$
\mathbb E\tau\le
\frac{\log(1/\alpha)+\log(1+\lambda)}{w(r-w)d(\lambda)}.
\tag{C99.2}
$$

$\tau$ 为全部双副本试验次数，平均制备份数为 $2\mathbb E\tau$。

证明。式 (C96.3) 给每轮完整三值分布

$$
\Pr(V=1)=\tfrac h2(1+\gamma^2),\quad
\Pr(V=-1)=\tfrac h2(1-\gamma^2),\quad
\Pr(V=0)=1-h.
\tag{C99.3}
$$

因此 $\Pr(V\ne0)=h$，条件于保留的两种符号，正号概率为
$(1+\gamma^2)/2\ge(1+\lambda)/2$。
记 $Y_n=\log(1+\lambda V_n)$、$S_N=\sum_{n=1}^NY_n=\log E_N$，
则增量 iid，并且

$$
\log(1-\lambda)\le Y_n\le\log(1+\lambda).
\tag{C99.4}
$$

它们的均值为

$$
\begin{aligned}
\mu&=\frac h2\bigl[(1+\gamma^2)\log(1+\lambda)
 +(1-\gamma^2)\log(1-\lambda)\bigr]\\
&=h\left[d(\lambda)+\frac{\gamma^2-\lambda}{2}
\log\frac{1+\lambda}{1-\lambda}\right]\ge h d(\lambda)>0.
\end{aligned}
\tag{C99.5}
$$

最后的严格正性可直接微分：$d(0)=0$，
$d'(\lambda)=\tfrac12\log((1+\lambda)/(1-\lambda))>0$ 对 $0<\lambda<1$ 成立。

先证明有限平均停止，之后才使用无界停止和恒等式。
由有界性，函数 $c(t)=\mathbb E e^{-tY_1}$ 在零邻域可微，
$c(0)=1$、$c'(0)=-\mu<0$。
具体在三值分布上它就是

$$
c(t)=1-h+\tfrac h2(1+\gamma^2)(1+\lambda)^{-t}
+\tfrac h2(1-\gamma^2)(1-\lambda)^{-t}.
\tag{C99.6}
$$

故存在固定 $t_*>0$ 使 $0<c(t_*)<1$。
若 $\tau>N$，前 $N$ 轮从未达到 $A$，特别有 $S_N<A$。
对非负变量 $e^{-t_*S_N}$ 用 Markov 不等式，再用跨轮独立性，得到实际尾界

$$
\Pr(\tau>N)\le\Pr(S_N<A)
\le e^{t_*A}\mathbb E e^{-t_*S_N}
=e^{t_*A}c(t_*)^N\qquad(N\ge0).
\tag{C99.7}
$$

$\tau>0$ 的尾和等式由指标函数的单调收敛给出，即使事先允许无穷期望也成立。
因此

$$
\mathbb E\tau=\sum_{N\ge0}\Pr(\tau>N)
\le\frac{e^{t_*A}}{1-c(t_*)}<\infty.
\tag{C99.8}
$$

这也推出 $\Pr(\tau<\infty)=1$；有限均值没有以 Wald 恒等式作为前提。
这里使用的是指数矩与 Markov 的经典 Chernoff 方法，所需 iid、有界性、
正漂移以及实际几何尾上界均已明确给出，不从“有正漂移”直接省略可积性。

现在固定有限整数 $m$。路径上

$$
S_{\tau\wedge m}=\sum_{k=1}^mY_k\mathbf1_{\{\tau\ge k\}}.
\tag{C99.9}
$$

事件 $\{\tau\ge k\}$ 只由前 $k-1$ 轮决定，和 $Y_k$ 独立。
有限求和取期望所以得到

$$
\mathbb E S_{\tau\wedge m}
=\mu\sum_{k=1}^m\Pr(\tau\ge k)=\mu\mathbb E(\tau\wedge m).
\tag{C99.10}
$$

设 $B=\max\{-\log(1-\lambda),\log(1+\lambda)\}$。
由 $\tau$ 可积及增量有界，$|S_{\tau\wedge m}|\le B\tau$ 是可积支配，
且 $S_{\tau\wedge m}\to S_\tau$ 几乎必然。
支配收敛和右侧单调收敛使式 (C99.10) 成为

$$
\mathbb E S_\tau=\mu\mathbb E\tau.
\tag{C99.11}
$$

这是在此实际假设下证明的 Wald 停止和恒等式。
首越界前有 $S_{\tau-1}<A$，末次增量至多 $b=\log(1+\lambda)$，故

$$
A\le S_\tau<A+b,\qquad
\mu\mathbb E\tau=\mathbb E S_\tau\le A+b.
\tag{C99.12}
$$

代入式 (C99.5) 即得所需上界。
每轮确实使用两份，路径上制备数等于 $2\tau$，故平均数亦乘二。证毕。

**命题 C-99.3（小相干尺度与明确的渐近范围）。** 当 $\gamma_0\downarrow0$，

$$
d(\gamma_0^2)=\frac{\gamma_0^4}{2}+O(\gamma_0^8),
\tag{C99.13}
$$

因此固定 $\alpha\in(0,1)$ 时，这个已构造规则满足

$$
\mathbb E\tau=O\!\left(\frac{\log(1/\alpha)}{w(r-w)\gamma_0^4}\right).
\tag{C99.14}
$$

更一般，该上界对 $0<\alpha\le\alpha_*<1$ 一致成立，常数可依 $\alpha_*$；
不声明对无限制的 $\alpha\uparrow1$ 一致。

证明。由几何级数在任意紧子区间上的一致收敛，
积分 $d'(\lambda)=\operatorname{artanh}\lambda$ 得

$$
d(\lambda)=\sum_{k\ge1}\frac{\lambda^{2k}}{(2k)(2k-1)}
=\frac{\lambda^2}{2}+\frac{\lambda^4}{12}+O(\lambda^6).
\tag{C99.15}
$$

例如 $0\le\lambda\le\lambda_*<1$ 时，首项以后的和至多
$\lambda^4/[12(1-\lambda_*^2)]$，足以给式 (C99.13)。
又 $d(\lambda)\ge\lambda^2/2$、$\log(1+\lambda)\le\lambda$。
固定 $A=\log(1/\alpha)>0$ 时，$A+\lambda=O(A)$；
若 $\alpha\le\alpha_*<1$，则 $A\ge\log(1/\alpha_*)>0$，同一估计一致成立。
代入式 (C99.2) 得所述范围。
若允许 $\alpha=\exp(-\gamma_0^6)$，则 $A=\gamma_0^6$，
而 $\log(1+\gamma_0^2)$ 为 $\gamma_0^2$ 阶，不能吸收到统一常数乘 $A$ 中。
事实上固定 $h>0$ 时式 (C99.14) 右侧尺度趋零而 $\tau\ge1$，
所以这种不加限制的一致大 $O$ 断言确实错误。证毕。

**命题 C-99.4（两个数值成本的有理界）。** 在
$r=4/5$、$w=2/5$、$\alpha=1/100$ 下，式 (C99.2) 给

| 最低相干量 $\gamma_0$ | $\lambda$ | 平均全部双副本试验次数 | 平均制备份数 |
| ---: | ---: | ---: | ---: |
| $1/2$ | $1/4$ | 小于 $956$ | 小于 $1912$ |
| $1/4$ | $1/16$ | 小于 $14921$ | 小于 $29842$ |

证明。此时 $h=4/25$，式 (C99.15) 的前两项给

$$
d(1/4)\ge\frac{97}{3072},\qquad
d(1/16)\ge\frac{1537}{786432}.
\tag{C99.16}
$$

为保留对数界的精确依据，对 $0<z<1$ 使用

$$
\log\frac{1+z}{1-z}
=2\sum_{j=0}^{m-1}\frac{z^{2j+1}}{2j+1}+R_m(z),\qquad
0<R_m(z)\le\frac{2z^{2m+1}}{(2m+1)(1-z^2)}.
\tag{C99.17}
$$

该式由 $2/(1-z^2)$ 的几何级数积分得到；尾项分母至少为 $2m+1$，
求几何和即得界。
令 $U_m(z)$ 为右侧有限和加显示的尾上界，则有理数比较给

$$
\begin{aligned}
\log125&=6\log2+\log(125/64)
<6U_{12}(1/3)+U_{12}(61/189)<\frac{4829}{1000},\\
\log(425/4)&=6\log2+\log(425/256)
<6U_{12}(1/3)+U_{12}(169/681)<\frac{23329}{5000}.
\end{aligned}
\tag{C99.18}
$$

两处 $z$ 由 $(v-1)/(v+1)$ 得到，故都是式 (C99.17) 的合法有理输入。
再作精确交叉相乘：

$$
\frac{4829}{1000}<956\,\frac4{25}\,\frac{97}{3072},\qquad
\frac{23329}{5000}<14921\,\frac4{25}\,\frac{1537}{786432}.
\tag{C99.19}
$$

式 (C99.2) 的分子分别为 $\log125$ 与 $\log(425/4)$；
式 (C99.16)–(C99.19) 因此给表中的严格上界，制备数乘二。证毕。

这里的 $\gamma_0^{-4}$ 是区分可分离背景与微弱相干增量的该规则上界。
C-92 的首次事件等待只要求一次成功，经典混合也可能成功；两种任务不同。
本章未给所有测量策略的最优下界，也未把双副本实验的次数转成原生逐位读取复杂度。

## 100. 相同单份密度矩阵与不同配对来源

**命题 C-100.1（底面单份可分离的相关副本反例）。** 在相同的实际五维测量上，
对 $0<r<1$ 定义成对密度算子

$$
\tau_{\rm corr}=r|\Omega\rangle\langle\Omega|
+(1-r)|2,2\rangle\langle2,2|.
\tag{C100.1}
$$

它的两个单份边缘相同，均为

$$
\rho_{\rm one}=r\frac{I_{\mathrm b}}4+(1-r)|2\rangle\langle2|,
\qquad I_{\mathrm b}=P_{\mathrm b}.
\tag{C100.2}
$$

每份底面条件态为可分离的 $I_4/4$，但联合测量有

$$
q_{--}^{\rm corr}=r,\qquad q_{-+}^{\rm corr}=q_{+-}^{\rm corr}
=q_{++}^{\rm corr}=0,\qquad q_{\mathrm f}^{\rm corr}=1-r.
\tag{C100.3}
$$

证明。式 (C100.1) 是两个归一化正交纯态投影的凸组合。
把 $\Omega$ 写成
$\frac12\sum_{s\in\{0,1,3,13\}}\epsilon_s|s,f(s)\rangle$，
其中 $f$ 依次将 $0,1,3,13$ 送到 $13,3,1,0$，
$\epsilon_0=\epsilon_{13}=1$、$\epsilon_1=\epsilon_3=-1$。
$f$ 是置换，所以第二份偏迹中的
$\langle f(t)|f(s)\rangle=\delta_{st}$ 消掉全部交叉项，得到
$\operatorname{Tr}_2|\Omega\rangle\langle\Omega|=I_{\mathrm b}/4$；
第一份偏迹同理。中模式项的任一偏迹为 $|2\rangle\langle2|$，即得式 (C100.2)。
条件态 $I_4/4=(I_2/2)\otimes(I_2/2)$ 明确可分离。

由 C-94.4，$Q_{--}$ 是 $\Omega$ 的秩一投影，故
$Q_{--}\Omega=\Omega$，其余三个符号投影因正交而消去 $\Omega$。
$|2,2\rangle$ 被全部 $Q_{st}$ 消去、被 $Q_{\mathrm f}$ 保留，
$\Omega$ 则被 $Q_{\mathrm f}$ 消去。直接取迹给式 (C100.3)。
相关来源两份同时在底面的概率是 $r$，与乘积来源的 $r^2$ 不同。证毕。

**命题 C-100.2（均匀单份边缘的二十倍差异及累积越界）。** 取 $r=4/5$，则
$\rho_{\rm one}=I_5/5$。保持这个单份密度矩阵不变，
独立配对和式 (C100.1) 的相关配对分别给

$$
q_{--}^{\rm ind}=\frac1{25},\qquad
q_{--}^{\rm corr}=\frac45,\qquad
q_{--}^{\rm corr}/q_{--}^{\rm ind}=20.
\tag{C100.4}
$$

若独立同分布地重复相关配对，并仍使用 C-98 的正投注规则，
则对任意 $0<\lambda,\alpha<1$ 都以概率一最终越界，
尽管每个单份底面边缘一直可分离。

证明。独立来源的条件态为 $I_4/4$，
$\mathcal P=1/4$、$\mathcal P_A=\mathcal P_B=1/2$，
式 (C94.15) 给 $q_{--}^{\rm ind}=r^2/16=1/25$。
相关值由式 (C100.3) 给出，所以比值为二十。
相关试验的 $V$ 只有 $1,0$，正号概率为 $r>0$。
令 $K=\lceil\log(1/\alpha)/\log(1+\lambda)\rceil$。
每次正号使证据乘 $1+\lambda$，有 $K$ 个正号即越界。
每段长度 $K$ 的不相交试验块全部为正的概率是 $r^K>0$，各块独立。
前 $m$ 块没有这样的块的概率为 $(1-r^K)^m\to0$，
所以几乎必然有限时刻得到至少 $K$ 个正号并越界。证毕。

这个例子不满足 C-98.1 的实际条件乘积零假设，故不与其风险界矛盾。
单份边缘相等、甚至完整单份密度矩阵完全相同，都没有替代成对来源的联合关系。
此处读到的是副本之间预先准备的关系，不能把它归为单份底面 $A,B$ 之间的纠缠。

副本关系的这一一般边界有明确先例：S. J. van Enk，
*Can measuring entanglement be easy?*，
[quant-ph/0606017v1](https://arxiv.org/abs/quant-ph/0606017v1)，式 (3)–(8) 及第三项异议，
讨论共同未知制备参数、相关多份描述及单份纠缠的错误归因。
Mintert–Buchleitner [quant-ph/0605250v3](https://arxiv.org/abs/quant-ph/0605250v3)
正文末段明确要求可靠来源实际提供 $\rho\otimes\rho$。
这里消费这种已知的来源限定，式 (C100.1)–(C100.4) 给当前五模式读口、
相同 $I_5/5$ 边缘和完整失败概率的具体反例；不将一般副本漏洞称为新发现。

## 101. 数学供应的参数对应与认证范围

**约定 C-101.1（同一对象上的供应映射）。** 本组的载体、固定参数和读口按下表对应；
每一行只供应列出的结构。

| 数学来源 | 当前参数及实际消费的内容 |
| --- | --- |
| [HiddenRelations 续卷 C-84.1–C-84.3、C-85.1–C-85.3](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS_CONTINUATION.md#84-隐藏宽度底面质量与所选面积的完整字典) | 同序 $(0,1,2,3,13)$、$r=1-Z$、$\kappa=p_{13}$、闭区间及 $w$；纯态容量是任意混态容量的纯态达到者。规范角仍为 $\eta=\tfrac18\log[p_0p_{13}/(p_1p_3)]$。 |
| [同续卷 C-67.2、C-76.1–C-76.2、C-78.3](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS_CONTINUATION.md#67-四角关系的规范椭圆与边缘比较) | 规范概率椭圆经过正行列平衡及面积归一化；底面基的标准序是 $(0,3,1,13)$；归一化四项 $\Omega$ 在局部副本重排后是两个 singlet 的乘积。 |
| [同续卷 C-91.1–C-93.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS_CONTINUATION.md#91-同一实际纯态的两份投影与底面概率成本) | 实际相同制备、底面双份质量 $r^2$ 和固定投影；$T$ 是首次事件等待，本组 $\tau$ 是证据越界等待，两者的成功判据不同。 |
| [《辛预测完成》§35.5–§35.7](SYMPLECTIC_PREDICTIVE_COMPLETION.md#355-固定可见均值后的真正辛约化) | 纯振幅固定矩相位商的 $\omega_{\rm red}=d\chi\wedge d\kappa$ 和面积 $2\pi w$；该卷 $\tau_{\rm SP}=8\eta$、$I_{\rm SP}=\mathcal I$，不与本组停止时间 $\tau$ 混同。 |
| [《内在分类与多边形几何》B-6.1–B-6.3](AURIC_FIB_ATOM_INTRINSIC_CLASSIFICATION_AND_POLYGON_GEOMETRY.md#6-五模式平均几何及完整概率纤维) | $L=\kappa_-$、$U=\kappa_+$、$w=U-L$，对角支撑限制必须与原闭纤维相交；其几何面积没有被改称密度矩阵的面积。 |
| [《共同来源正性与历史前缀》C-30.1](AURIC_FIB_ATOM_COMMON_SOURCE_POSITIVITY_AND_HISTORICAL_PREFIXES.md#30-合法双窗共正核的同边缘符号谱与记录应用) | $(O,L,T,R,J)\leftrightarrow(0,1,2,3,13)$，保留共同联合律与方向。该处的合法原生双窗支撑是附加接缝条件；这里的双份仪器定义在 $\mathcal H_5^{\otimes2}$，没有自动施加或实现原生接缝。 |
| [《实际 renewal 仪器与检测器秩》定义 22.1、定理 22.3](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#22-all-sum-conditional-acquisition-at-the-cubic-near-one-order) | 来源是在同一历史上逐位读取的平稳 no11 流，完整间隔对在首次实际 tick 后取得；成本 $L=1+\tau_{\rm native}+\sum_{j=1}^N(K_{2j-1}+K_{2j}+2)$ 保留初始等待、所有零位及闭合 tick。 |

最后一行与本组共享“条件比例消参不消除取得成本”的核算要求。
其原生参数 $q_{\rm native}$、逐位次数 $L$，与本组底面质量 $r$、
成对次数 $\tau$、事件概率 $q_{--}$ 不具有已指定的等同关系，
尤其不从记号相似推出 $r=1-q_{\rm native}$。
跨模型转移复杂度必须另给保持实际来源、可执行操作、输出事件和成本单位的映射。

**约定 C-101.2（经典机制与本组应用的边界）。** 交换测纯度、纯度差纠缠见证、
两量子位凸屋顶、非负超鞅全时间界、指数矩尾估计以及可积 iid 停止和，均为经典中间机制。
本组在 C-94、C-96–C-100 的对应条目内给准确文献归属及当前参数下的完整推导。
承重应用是固定五模式均值的两个容量、共同达到构造、相干插值，
以及从实际五维测量到有风险控制的证书和全部制备成本的连接；不附带全球原创性断言。

这些是所声明模型中的普通数学证明。状态集合中的存在性、固定对角上的变化、
实际轮内乘积输入、历史条件来源合同和固定 iid 成本条件各自承担不同结论。
坐标翻转或局部换基用于证明不等于原生可用控制，数学投影不自动供应物理仪器。
本组也没有把混态赋予唯一纯态相位，或从单份边缘构造未知态克隆。

## 追加锚（本行以下为增补区）

## 102. 单份底面质量与配对来源的量子边界

**定义 C-102.1（底面事件与连接算子）。** 令

$$
P_{\mathrm b}=\Pi_0+\Pi_1+\Pi_3+\Pi_{13},
\qquad r=\operatorname{tr}(P_{\mathrm b}\rho).
$$

设 $\Gamma$ 是两份五模式系统上的任意密度算子，且两份边缘都等于 $\rho$：

$$
\operatorname{Tr}_1\Gamma=\operatorname{Tr}_2\Gamma=\rho.
$$

把

$$
\Delta=\Gamma-\rho\otimes\rho
$$

称为配对连接算子。它满足

$$
\operatorname{Tr}_1\Delta=\operatorname{Tr}_2\Delta=0.
\tag{C102.1}
$$

因此任意单份观测量 $A$、$B$ 都看不到它：

$$
\operatorname{tr}\bigl((A\otimes I)\Delta\bigr)=0,\qquad
\operatorname{tr}\bigl((I\otimes B)\Delta\bigr)=0.
\tag{C102.2}
$$

它只可能通过真正的二份观测量显现。这个连接可以是经典相关，也可以含有跨份相干；零偏迹本身不判定纠缠。

**命题 C-102.2（底面联合质量的 Fréchet 区间）。** 定义

$$
r_{12}=\operatorname{tr}\bigl((P_{\mathrm b}\otimes P_{\mathrm b})\Gamma\bigr).
$$

则

$$
\boxed{
\max(0,2r-1)\le r_{12}\le r.
}
\tag{C102.3}
$$

若来源是乘积来源 $\Gamma=\rho\otimes\rho$，则

$$
r_{12}=r^2.
\tag{C102.4}
$$

对任意底面内的二份效果 $0\le Q\le P_{\mathrm b}\otimes P_{\mathrm b}$，其事件概率

$$
q_Q(\Gamma)=\operatorname{tr}(Q\Gamma)
$$

满足

$$
0\le q_Q(\Gamma)\le r_{12}\le r,\qquad
q_Q(\Gamma)-q_Q(\rho\otimes\rho)=\operatorname{tr}(Q\Delta).
\tag{C102.5}
$$

**证明。** 由 $0\le P_{\mathrm b}\le I$，有
$0\le P_{\mathrm b}\otimes P_{\mathrm b}\le P_{\mathrm b}\otimes I$。
取 $\Gamma$ 的迹并使用第一边缘为 $\rho$，得 $r_{12}\le r$。
同样，正算子

$$
(I-P_{\mathrm b})\otimes(I-P_{\mathrm b})\ge0
$$

给出 $1-2r+r_{12}\ge0$，从而 $r_{12}\ge2r-1$；再与
$r_{12}\ge0$ 合并即得 (C102.3)。乘积情形直接因迹的乘法性得到 (C102.4)。
对 $Q$ 使用 $0\le Q\le P_{\mathrm b}\otimes P_{\mathrm b}$ 即得第一项不等式，第二项是 $\Delta$ 的定义展开。式 (C102.1)–(C102.2) 由偏迹的定义和迹的循环性得到。证毕。

这个命题把“相同单份状态”与“相同配对来源”分开：固定 $\rho$ 只固定 $r$，不固定 $r_{12}$，更不固定 $q_Q$。乘积零假设把 $r_{12}$ 压到 $r^2$；历史条件下的共同来源可以把它推向区间的另一端。因而单份边缘、单份纯度或单份相位读数都不能替代 C-98.1 所需的联合来源条件。

**例 C-102.3（当前五模式的饱和上端）。** 在 C-100.1 的构造中取 $r=4/5$，并令 $\Gamma_{\rm corr}$ 为式 (C100.1) 的两份来源。它的两个单份边缘仍都是 $I_5/5$，但

$$
r_{12}(\Gamma_{\rm corr})=r=\frac45,\qquad
r_{12}(I_5/5\otimes I_5/5)=r^2=\frac{16}{25}.
\tag{C102.6}
$$

而 $Q_{--}\le P_{\mathrm b}\otimes P_{\mathrm b}$ 且式 (C100.3) 给出
$q_{--}(\Gamma_{\rm corr})=4/5$。因此这里的二十倍事件差首先是配对连接
$\Delta$ 的读出；它不能被解释成单份底面状态改变，也不能单独推出底面内部
$A$、$B$ 两个模式已经纠缠。

**推论 C-102.4（连接读出是二份证据）。** 对任一二份效果 $Q$，若

$$
\delta_Q=\left|\operatorname{tr}(Q\Delta)\right|>0,
$$

则 $\Gamma$ 与乘积来源 $\rho\otimes\rho$ 的二份迹距离满足

$$
\frac12\left\|\Gamma-\rho\otimes\rho\right\|_1\ge\delta_Q.
\tag{C102.7}
$$

证明。将 $\Delta$ 的迹与效果 $Q$ 配对，并使用迹距离对任意效果的变分界。
这个证据只认证配对来源偏离乘积来源；若要把它称为跨份纠缠，还必须另加
可分离集合、部分转置或其他纠缠判据。$\square$

本节的算子不等式是有限维正性和迹的直接推导，不主张新的普遍量子不等式。
在本项目中它的新增用途是：把 C-98 的乘积来源合同、C-100 的相同单份边缘反例，
以及实际双副本读口统一成一个可测的连接算子 $\Delta$；因此 $F[1,3]$ 型的二阶关系
只有在指定二份效果或相互作用后才成为量子可观测量，不能由单份读数自动升级为
能量、纠缠或曲率。

## 追加锚（本行以下为增补区）

## 103. 局部通道不能读出配对连接

**命题 C-103.1（局部后处理的连接盲性）。** 沿用定义 C-102.1。设
\(\mathcal E:\mathcal L(\mathcal H)\to\mathcal L(\mathcal K)\) 是任意完全正保迹映射，
\(M\) 是 \(\mathcal K\) 上的任意可观测量。则

$$
\operatorname{tr}\!\left[
(M\otimes I)(\mathcal E\otimes\operatorname{id})(\Delta)
\right]=0.
\tag{C103.1}
$$

第二份上的任意局部通道也有同样结论。换句话说，给定相同的单份边缘，任意只在一份上
进行的量子处理、测量和经典后处理，都不能把配对连接 \(\Delta\) 变成单份读数差异。

**证明。** 取 \(\mathcal E^*\) 为 Hilbert--Schmidt 对偶。迹的循环性和对偶定义给出

$$
\operatorname{tr}\!\left[
(M\otimes I)(\mathcal E\otimes\operatorname{id})(\Delta)
\right]
=
\operatorname{tr}\!\left[
(\mathcal E^*(M)\otimes I)\Delta
\right].
$$

右端由式 (C-102.2) 为零。完全正性和保迹性只保证 \(\mathcal E\) 是合法的局部量子
操作；零值本身只使用 \(\operatorname{Tr}_1\Delta=0\)。证毕。

这条命题把两个层次分开。\(\Delta\) 可以被二份效果 \(Q\) 读出，因为
\(\operatorname{tr}(Q\Delta)\) 未必为零；但任何单份通道都只能看到边缘 \(\rho\)。因此
“存在非零二份连接读数”不能推出单份 coherent flag port，也不能推出纠缠。后两种
结论分别需要二份端口的量词和独立的纠缠判据。

**定义 C-103.2（二份端口的类型提升）。** 若 \(v_i\in\mathcal H\) 是单份 probe，
二份问题的自然 probe 是

$$
w_{(i,j)}=v_i\otimes v_j\in\mathcal H\otimes\mathcal H.
$$

只有在端口的输入域、密度输入的全称量词以及保持的 probe 概率都同时提升到
\(\mathcal H\otimes\mathcal H\) 后，才可以提出二份 port 维数下界，例如比较各
product component 的维数与二份相干维数。C-102 的 \(\Delta\) 在这一路线上只供应
来源敏感度

$$
\delta_{ij}=\operatorname{tr}\!\left[
(P_i\otimes P_j)\Delta
\right],
$$

不供应端口下界本身。当前仓内结果尚未证明该二份 product-component 下界，故该桥接
仍标为开放问题。

## 追加锚（本行以下为增补区）

## 104. 二份 probe 的乘积分量与相干端口税

### 104.1 从单份 probe 到二份 product probe

令单份 Hilbert 空间为有限维 \(H\)，令 \(v_i\in H\) 是归一化 probe。若以

$$
i\sim j\quad\Longleftrightarrow\quad \langle v_i,v_j\rangle\neq0
$$

生成非正交图的连通分量 \(C,D\)，并记

$$
V_C=\operatorname{span}\{v_i:i\in C\},\qquad
V_D=\operatorname{span}\{v_j:j\in D\},
$$

则二份 product probe

$$
w_{(i,j)}=v_i\otimes v_j\in H\otimes H
$$

的 \(C\times D\) 分量满足

$$
\operatorname{span}\{w_{(i,j)}:(i,j)\in C\times D\}
=V_C\otimes V_D,
$$

从而

$$
\dim(V_C\otimes V_D)=\dim(V_C)\dim(V_D).
\tag{C104.1}
$$

这里需要保留三个条件：probe 家族必须确实包含所有 \((i,j)\) 的笛卡尔提升；端口必须对同一个二份输入域 \(H\otimes H\) 工作；保持概率的量词必须是对所有二份密度态成立。若只给一份实际来源、一个固定效果或有限校准样本，(C104.1) 不能推出端口维数下界。

归一化使每个 probe 与自身的内积非零，因此在 product 图中可以固定一个坐标、沿另一坐标的连通路径移动；这正是 \(C\times D\) 而不是更小的孤立子集成为分量的原因。维数乘法来自张量积的基，而不是来自 \(\Delta\) 的数值。

### 104.2 五模式的两个边界

取 AURIC 五态标签

$$
B=\{0,1,2,3,13\},\qquad H=\mathbb C^5.
$$

若 probe 菜单只有计算基投影

$$
\{P_s=|s\rangle\langle s|:s\in B\}
$$

及其 product 菜单 \(\{P_s\otimes P_t\}\)，每个非正交分量都是单例，因而最大的 product 分量维数为 \(1\)。在这个菜单上，二份概率可以由五乘五个经典 flag 保持；这不要求一个四维量子相干端口。

加入相干 rank-one effect

$$
Q_{--}=|\Omega\rangle\langle\Omega|,\qquad
|\Omega\rangle=\frac12\bigl(
|0,13\rangle+|13,0\rangle-|1,3\rangle-|3,1\rangle\bigr)
$$

后，\(\Omega\) 与四个计算基 product vector 都有非零重叠。该连通分量由五个向量生成，但 \(\Omega\) 已在四个向量的张成内，所以其实际分量维数为 \(4\)。在一个对所有二份密度输入保持这些 probe 概率的有限 flagged port 模型中，product 菜单给出 \(q\ge1\)，而加入 \(Q_{--}\) 后给出 \(q\ge4\)；相应的正交嵌入达到 \(q=4\) 仍需在 Lean 中补齐。

这两个数值不能压缩成 \(q=f(p_{13})\)。前者只测计算基的联合占据，后者测到四个标签之间的相干方向；相同的 \(p_{13}\) 可以对应不同的相干端口成本。

### 104.3 与连接算子分层

沿用 C-102 和 C-103，令

$$
\Delta=\Gamma-\rho\otimes\rho.
$$

二份 probe 的来源差异是

$$
\delta_{ij}=\operatorname{tr}\bigl((P_i\otimes P_j)\Delta\bigr),\qquad
\delta_\Omega=\operatorname{tr}(Q_{--}\Delta).
$$

这些量说明来源是否偏离乘积来源；它们不改变 (C104.1) 的线性代数，也不单独证明纠缠。特别地，\(\Gamma\) 可以是可分离的经典对角来源而仍有非零 \(\delta_\Omega\) 或非零其它二份连接读数。要声称纠缠，仍须另加可分离集合、PPT 或其它纠缠判据；要声称端口下界，仍须给出二份端口的 CPTP 结构和全称保持合同。

因此当前状态是：C-102/C-103 已把“来源连接”和“局部通道”分开；C-104 给出 product-component 维数乘法以及五模式 \(1\to4\) 的条件性候选；从该候选到当前 dev 中可冻结的 Lean 定理，还缺 Fin-5 标签映射、\(\Omega\) 的分量张成计算、有限 flagged port 的实例化和对应的来源敏感度恒等式。缺少这些桥接之前，不把 \(F[1,3]\) 叫作能量、纠缠或单份相干端口维数。
## 105. 完整 product-plus-Omega 菜单中的纠缠盲纤维与参数读口

**定义 C-105.1（两份分割、置换与分开执行的测量设置）。** 沿用 C-104 的正交标签
$B=\{0,1,2,3,13\}$、$H=\mathbb C^5$、$P_s=|s\rangle\langle s|$，
两份系统记作 $H^{(1)}\otimes H^{(2)}$。本章的可分离与纠缠一律相对于
$H^{(1)}\mid H^{(2)}$；它与 C-94.2 在每一份底面内指定的
$\mathbb C_A^2\mid\mathbb C_B^2$ 是不同分割。定义对合置换

$$
f(0)=13,\quad f(13)=0,\quad f(1)=3,\quad f(3)=1,\quad f(2)=2,
\qquad e_s=|s,f(s)\rangle.
\tag{C105.1}
$$

五个 $e_s$ 正交归一。令 $I_{25}$ 为二份空间的恒等算子，
$Q=|\Omega\rangle\langle\Omega|$，其中 $\Omega$ 是 C-104.2 的向量。
完整菜单 $\mathcal M$ 包含两个分别执行的设置：计算基 PVM
$\{P_s\otimes P_u:s,u\in B\}$，以及二元 PVM $\{Q,I_{25}-Q\}$。
对二份密度算子 $\Gamma$ 定义观察映射

$$
\mathcal O_{\mathcal M}(\Gamma)
=\left(\bigl(\operatorname{tr}((P_s\otimes P_u)\Gamma)\bigr)_{s,u\in B},
\operatorname{tr}(Q\Gamma)\right).
\tag{C105.2}
$$

二元设置的补事件概率由 $1-\operatorname{tr}(Q\Gamma)$ 决定。
这里的 $25$ 个基效果与 $Q$ 不组成一个 $26$ outcome POVM：前者之和已经是
$I_{25}$，再加 $Q$ 得 $I_{25}+Q$。纤维指映射 (C105.2) 的逆像，
比较的是同一二份状态在这些不同设置下的精确期望。

**定义 C-105.2（承诺的连续混态族）。** 定义

$$
\begin{aligned}
S&=\frac15\sum_{s\in B}|e_s\rangle\langle e_s|,\\
|\Psi\rangle&=\frac12(e_0+e_{13}+e_1-e_3),\\
T&=\frac45|\Psi\rangle\langle\Psi|+\frac15|e_2\rangle\langle e_2|,\\
\Gamma_t&=(1-t)S+tT,\qquad t\in[0,1]\subset\mathbb R.
\end{aligned}
\tag{C105.3}
$$

承诺族包括固定的实际基、固定的置换、所列实系数及相位，只有 $t$ 可以变化。
它不假定 $\Gamma_t=\rho\otimes\rho$，也不把相同边缘当作轮内独立。
记四维空间

$$
V=\operatorname{span}\{e_0,e_{13},e_1,e_3\},\qquad
P_V=\sum_{s\ne2}|e_s\rangle\langle e_s|,
\qquad K=T-S=\frac45|\Psi\rangle\langle\Psi|-\frac15P_V.
\tag{C105.4}
$$

$\Gamma_t=S+tK$。在 $V$ 的有序基 $(e_0,e_{13},e_1,e_3)$ 中，令
$v=(1,1,1,-1)^{\mathsf T}$，则

$$
\left.\Gamma_t\right|_V=\frac15\bigl((1-t)I_4+t vv^\dagger\bigr),
\qquad \langle e_2|\Gamma_t|e_2\rangle=\frac15;
\tag{C105.5}
$$

$V$ 与 $e_2$ 之间以及这五维支撑之外的矩阵元全为零。

**定理 C-105.3（密度性、相同边缘与底面质量）。** 对每个实数 $0\le t\le1$，
$\Gamma_t$ 是密度算子，两个边缘均为 $\rho=I_5/5$。沿用 C-94.2 的底面识别，
每份的底面质量与条件态，以及二份的底面联合质量分别为

$$
\begin{aligned}
\operatorname{Tr}_2\Gamma_t&=\operatorname{Tr}_1\Gamma_t=I_5/5,\\
r&=\operatorname{tr}(P_{\mathrm b}\rho)=4/5,\qquad
\sigma=\frac{\iota^\dagger\rho\iota}{r}=I_4/4,\\
r_{12}(\Gamma_t)&=\operatorname{tr}((P_{\mathrm b}\otimes P_{\mathrm b})\Gamma_t)=4/5.
\end{aligned}
\tag{C105.6}
$$

证明。$\|\Psi\|^2=4/4=1$，且 $\Psi\perp e_2$。
$S$ 是五个单位向量投影的等权混合，$T$ 是两个单位向量投影的凸组合，
故二者正半定、迹一；$0\le t\le1$ 保证 $\Gamma_t$ 同样如此。
对于任意 $s,a\in B$，有

$$
\begin{aligned}
\operatorname{Tr}_2(|e_s\rangle\langle e_a|)
&=\langle f(a)|f(s)\rangle\,|s\rangle\langle a|,
\\
\operatorname{Tr}_1(|e_s\rangle\langle e_a|)
&=\langle a|s\rangle\,|f(s)\rangle\langle f(a)|.
\end{aligned}
\tag{C105.7}
$$

$f$ 是置换，故两种偏迹都消去 $s\ne a$ 的交叉项。
$S$ 的任一边缘为 $I_5/5$；$|\Psi\rangle\langle\Psi|$ 的任一边缘为
$P_{\mathrm b}/4$，因此 $T$ 的任一边缘为
$(4/5)(P_{\mathrm b}/4)+(1/5)|2\rangle\langle2|=I_5/5$。
线性性给 $\Gamma_t$ 的两个边缘。将 $I_5/5$ 压缩到 C-94.2 的四维底面并除以
$4/5$，得到 $I_4/4=(I_2/2)\otimes(I_2/2)$，所以每份的条件底面可分离。
二份底面投影在 $V$ 上为恒等、在 $e_2$ 上为零。
$S$ 的底面权重为四个 $1/5$ 之和，$T$ 的底面权重为 $4/5$，
于是整族的 $r_{12}=4/5$。乘积边缘来源 $\rho\otimes\rho=I_{25}/25$ 才有
$r_{12}=r^2=16/25$；本族达到 C-102.2 区间的上端 $r_{12}=r$。证毕。

**定理 C-105.4（完整菜单的一条恒定纤维）。** 对每个实数 $0\le t\le1$ 以及
全部 $s,u\in B$，有

$$
\operatorname{tr}((P_s\otimes P_u)\Gamma_t)
=\begin{cases}1/5,&u=f(s),\\0,&u\ne f(s),\end{cases}
\qquad \operatorname{tr}(Q\Gamma_t)=1/5.
\tag{C105.8}
$$

因而 $\mathcal O_{\mathcal M}(\Gamma_t)=\mathcal O_{\mathcal M}(S)$，
而相对于具有相同边缘的乘积来源，连接读数恒为

$$
\Delta_t=\Gamma_t-I_{25}/25,\qquad
\operatorname{tr}(Q\Delta_t)=\frac15-\frac1{25}=\frac4{25}.
\tag{C105.9}
$$

证明。$S$ 在五个 $e_s$ 上的对角元全为 $1/5$。
$T$ 在四个底面 $e_s$ 上的对角元为 $(4/5)|1/2|^2=1/5$，
在 $e_2$ 上也为 $1/5$，其余计算基对角元为零。
凸组合给全部 $25$ 个基概率。写

$$
|\Omega\rangle=\frac12(e_0+e_{13}-e_1-e_3),\qquad
\langle\Omega|\Psi\rangle=\frac{1+1-1+1}{4}=\frac12.
\tag{C105.10}
$$

故 $\operatorname{tr}(QS)=(1/5)\sum_s|\langle\Omega|e_s\rangle|^2=1/5$，
$\operatorname{tr}(QT)=(4/5)|1/2|^2=1/5$；$e_2$ 对两者的 $Q$ 读数均无贡献。
迹的线性性给整个实区间上的恒等式。$Q$ 为归一化秩一投影，
故 $\operatorname{tr}(QI_{25}/25)=1/25$，得到 (C105.9)。证毕。

**定理 C-105.5（同一纤维中的可分离端点与连续纠缠族）。** $\Gamma_0=S$
相对于 $H^{(1)}\mid H^{(2)}$ 可分离；每个 $0<t\le1$ 的 $\Gamma_t$
相对于同一分割均纠缠。$t\mapsto\Gamma_t$ 连续且单射。

证明。$S=(1/5)\sum_s P_s\otimes P_{f(s)}$ 是明确的产品密度算子凸组合，
所以可分离。对第二份取计算基部分转置，约定

$$
(|a,b\rangle\langle c,d|)^{\mathsf T_2}
=|a,d\rangle\langle c,b|.
\tag{C105.11}
$$

由 (C105.3)，$\langle0,13|\Gamma_t|13,0\rangle=t/5$。
$|0,0\rangle$ 与 $|13,13\rangle$ 在原计算基对角上均不匹配置换，
故其对角元为零。部分转置的相应二阶压缩为

$$
\left.\Gamma_t^{\mathsf T_2}\right|_{\operatorname{span}\{|0,0\rangle,|13,13\rangle\}}
=\begin{pmatrix}0&t/5\\t/5&0\end{pmatrix}.
\tag{C105.12}
$$

令 $|z_-\rangle=(|0,0\rangle-|13,13\rangle)/\sqrt2$，则 $\|z_-\|=1$，

$$
\langle z_-|\Gamma_t^{\mathsf T_2}|z_-\rangle=-t/5<0\qquad(t>0).
\tag{C105.13}
$$

可分离态的部分转置必正半定：对任意产品密度算子
$A\otimes B$，其第二份部分转置是 $A\otimes B^{\mathsf T}\succeq0$，
凸组合仍正半定。这是 Peres 的 PPT 必要条件，见
Asher Peres，*Separability Criterion for Density Matrices*，
[Phys. Rev. Lett. 77, 1413–1415 (1996)](https://doi.org/10.1103/PhysRevLett.77.1413)，
[arXiv:quant-ph/9604005v2](https://arxiv.org/abs/quant-ph/9604005v2)，式 (3)–(6)
（交换两份即可采用这里的第二份转置约定）。负期望直接排除可分离性；
这里没有使用 PPT 在 $5\times5$ 上的充分性。
$\Gamma_t=S+tK$ 是有限维仿射映射，因而连续；所列非对角元为 $t/5$，
所以不同 $t$ 给不同状态。证毕。

本构造的矩阵结构属于成熟的 maximally correlated 类型。
具体地，局部置换酉 $U_f|s\rangle=|f(s)\rangle$ 满足
$(I_5\otimes U_f)e_s=|s,s\rangle$，因此将 (C105.3) 变成
$\sum_{s,a}c_{sa}(t)|s,s\rangle\langle a,a|$。
这一类型的标准定义见 Tohya Hiroshima、Masahito Hayashi，
*Finding a maximally correlated state: Simultaneous Schmidt decomposition of bipartite pure states*，
[Phys. Rev. A 70, 030302(R) (2004)](https://doi.org/10.1103/PhysRevA.70.030302)，
[arXiv:quant-ph/0405107v2](https://arxiv.org/abs/quant-ph/0405107v2)，式 (1)、(4)。
这里复用该结构与 PPT 判据；本章的仓内综合是 (C105.3) 的特定符号选择同时保持
C-104 的全部基概率和 $Q$ 读数，并给同一纤维的参数读口，不作原创性主张。

**定理 C-105.6（承诺族内的精确参数识别与原四维支撑）。** 增加一个分别执行的
二元设置 $\{R_+,I_{25}-R_+\}$，其中

$$
|r_+\rangle=\frac{e_0+e_{13}}{\sqrt2},\qquad
R_+=|r_+\rangle\langle r_+|.
\tag{C105.14}
$$

在定义 C-105.2 的承诺族内，其精确期望满足

$$
p_+(t)=\operatorname{tr}(R_+\Gamma_t)=\frac{1+t}{5},\qquad
\frac15\le p_+(t)\le\frac25,\qquad t=5p_+(t)-1.
\tag{C105.15}
$$

$R_+$ 的支撑包含于 $V$；将这个 rank-one probe 加入 C-104 的非正交图后，
原来的四维连通分量仍为 $V$，没有扩大。

证明。$r_+$ 归一化，故 $R_+$ 与其补算子组成合法二元 PVM。
$S$ 给 $\operatorname{tr}(R_+S)=1/5$。
$\langle r_+|\Psi\rangle=1/\sqrt2$ 且 $r_+\perp e_2$，
所以 $\operatorname{tr}(R_+T)=(4/5)(1/2)=2/5$。
凸组合给 (C105.15)，斜率 $1/5$ 严格为正，反解唯一确定 $t$。
由于 $r_+\in V$，有 $P_VR_+P_V=R_+$。
它与 $e_0,e_{13}$ 的内积均为 $1/\sqrt2$，与其它 $23$ 个计算基向量的内积为零，
且 $\langle\Omega|r_+\rangle=1/\sqrt2$。
因此它接到原四维分量，不接到其余基向量；旧四个基向量仍张成 $V$，
加入一个已经属于 $V$ 的向量不增加维数。
二元设置的补效果只给 $1-p_+(t)$，并非一个额外的 rank-one probe。证毕。

**命题 C-105.7（识别、纠缠与端口结论的适用范围）。** 映射 (C105.2) 在二份密度态域上
不能单独判定 $H^{(1)}\mid H^{(2)}$ 的可分离性；它的一个纤维包含 $S$ 和全部
$\Gamma_t$，$0<t\le1$。加入 $R_+$ 后，(C105.15) 只在固定基、固定相位和固定矩阵族
(C105.3) 的承诺下，从精确期望识别参数及其是否为零。它不是对任意二份输入的状态层析
或通用纠缠判据，也不把有限样本频率当作精确期望。

证明。定理 C-105.4 给相同完整菜单读数，定理 C-105.5 给不同可分离性；
任何只依赖这些相同读数的判定函数都只能给同一个输出。
本族给出一个纤维内的连续线段，不声称分类整个纤维。
定理 C-105.6 的反解则使用了整个承诺族，而非仅使用相同边缘。
例如族外的可分离态 $P_0\otimes P_{13}$ 也有
$\operatorname{tr}(R_+(P_0\otimes P_{13}))=1/2>1/5$，
故单独的阈值 $p_+>1/5$ 不是无承诺纠缠判据。证毕。

C-77 的同概率纯相位族改变的是单份底面 concurrence；这里的单份条件底面
始终为 $I_4/4$，而纠缠只发生在两份五维系统之间。
C-78.3/C-91.2 的 $q_\Omega=r^2\mathcal C^2/4$ 需要同一实际纯态的独立两份
或其指定的底面乘积块，不能用于 (C105.3) 的相关混态来源。
(C105.9) 的非零连接既存在于可分离端点，也存在于纠缠族，因而本身不认证纠缠。
C-100 的相同边缘反例与 C-102/C-103 的局部盲性供应这个区分，
(C105.8) 进一步给出包含 $Q$ 的完整菜单仍然合并两类来源的显式连续纤维。

$R_+$ 的支撑结论只属于当前 probe 图的线性代数。
要连接 C-104 的条件性相干端口候选，仍须给出同一个 $H\otimes H$ 输入域、
对所有二份密度输入保持概率的 CPTP 编码与解码，以及有限且固定的经典 flag 空间；
承诺族内识别参数不能替代这些全称合同。
量子压缩的文献框架见 Andreas Bluhm、Lukas Rauber、Michael M. Wolf，
*Quantum compression relative to a set of measurements*，
[Ann. Henri Poincaré 19, 1891 (2018)](https://doi.org/10.1007/s00023-018-0660-z)，
[arXiv:1708.04898](https://arxiv.org/abs/1708.04898)。它是条件性压缩背景，
不是本族纠缠的证据。C-104 所列标签映射、分量计算与有限 flagged CPTP
实例化的形式桥接仍是独立的未证义务；本章的族内恒等式与支撑关系不能代替
$q\ge4$ 通用端口定理的证明。
(C105.3) 与 (C105.14) 给出数学状态和测量效果；它们本身不供应 AURIC 原生系统中的
物理制备、相位参照或联合测量实现。

## 追加锚（本行以下为增补区）

## 106. 完整联合人口纤维上的无族承诺认证与精确白噪声边界

**定义 C-106.1（实际联合人口与两个观察纤维）。** 沿用 C-105.1 的 $B,H,f,e_s,Q,R_+$，
以及 C-105.2 的 $S,T,\Psi,\Gamma_t$。所有密度算子均为
$H^{(1)}\otimes H^{(2)}$ 上任意复矩阵 $\Gamma\succeq0$、$\operatorname{tr}\Gamma=1$；
可分离性仍只相对于 $H^{(1)}\mid H^{(2)}$。
定义同一实际状态的精确联合概率和两个二元设置的响应

$$
p_{su}(\Gamma)=\langle s,u|\Gamma|s,u\rangle,\qquad
q(\Gamma)=\operatorname{tr}(Q\Gamma),\qquad
p_R(\Gamma)=\operatorname{tr}(R_+\Gamma),
\tag{C106.1}
$$

$$
\begin{aligned}
\mathfrak D&=\left\{\Gamma\succeq0:\operatorname{tr}\Gamma=1,\quad
p_{su}(\Gamma)=\tfrac15\mathbf1_{\{u=f(s)\}}\quad\text{对所有 }s,u\in B\right\},\\
\mathfrak F&=\{\Gamma\in\mathfrak D:q(\Gamma)=1/5\}.
\end{aligned}
\tag{C106.2}
$$

$\mathfrak F$ 是 C-105 原完整菜单在 $S$ 处的纤维；$\mathfrak D$ 只固定全部 $25$ 个
联合基概率。它们都不要求 $\Gamma=\Gamma_t$、实矩阵、乘积来源或轮内独立。
不同测量设置的期望须属于同一个实际状态；两个单份边缘相同不供应这个条件。

**定理 C-106.2（该人口纤维唯一的 PPT 态与可分离态）。** 对每个 $\Gamma\in\mathfrak D$，

$$
\Gamma^{\mathsf T_2}\succeq0
\quad\Longleftrightarrow\quad\Gamma=S
\quad\Longleftrightarrow\quad\Gamma\text{ 可分离}.
\tag{C106.3}
$$

因此同样的等价关系适用于包含原 $Q$ 约束的 $\mathfrak F$。

证明。设 $\mathcal E=\operatorname{span}\{e_s:s\in B\}$。
正半定复矩阵满足 $|\Gamma_{xy}|^2\le\Gamma_{xx}\Gamma_{yy}$；这是其二阶主子式的非负性。
若 $x=|s,u\rangle$ 且 $u\ne f(s)$，人口合同给 $\Gamma_{xx}=0$，所以整行和整列均为零。
从而不存在连接 $\mathcal E$ 与其正交补的隐蔽矩阵元，并且

$$
\Gamma=\sum_{s,a\in B}c_{sa}|e_s\rangle\langle e_a|,\qquad
C=(c_{sa})\succeq0,\quad c_{ss}=1/5,\quad c_{as}=\overline{c_{sa}}.
\tag{C106.4}
$$

这里保留全部复相位。局部置换将 $e_s$ 送到 $|s,s\rangle$，故这是已知的
maximally correlated 结构；其定义见 Hiroshima–Hayashi，
[quant-ph/0405107v2](https://arxiv.org/abs/quant-ph/0405107v2)，式 (1)。
按 C-105.11 的第二份转置约定，

$$
\Gamma^{\mathsf T_2}
=\sum_{s,a}c_{sa}|s,f(a)\rangle\langle a,f(s)|.
\tag{C106.5}
$$

对每个无序对 $s\ne a$，子空间
$\operatorname{span}\{|s,f(a)\rangle,|a,f(s)\rangle\}$ 上的块为

$$
\begin{pmatrix}0&c_{sa}\\\overline{c_{sa}}&0\end{pmatrix},
\qquad\text{特征值 }+|c_{sa}|,-|c_{sa}|.
\tag{C106.6}
$$

这十个二维块与五个 $e_s$ 上的单点块互相正交，合计维数 $20+5=25$。
故 PPT 当且仅当全部非对角 $c_{sa}$ 为零，当且仅当 $\Gamma=S$。
这个块谱是 Rains，*A semidefinite program for distillable entanglement*，
[quant-ph/0008047v2](https://arxiv.org/abs/quant-ph/0008047v2)，§6 Lemma 6.3 的证明、
式 (6.20)–(6.21) 的直接应用；这里的额外关系是实际联合人口强制进入该结构。
$S=(1/5)\sum_s P_s\otimes P_{f(s)}$ 是产品态的凸组合。
反向的“可分离推出 PPT”是 Peres，
[quant-ph/9604005v2](https://arxiv.org/abs/quant-ph/9604005v2)，式 (3)–(6) 的必要条件。
因此三者等价，且 C-105.4 给 $q(S)=1/5$。证毕。

式 (C106.3) 使用完整人口纤维的结构，没有使用一般 $5\times5$ 系统的 PPT 充分性。
其所需零概率是总体概率的精确零；有限次试验中某些格子计数为零，不能直接满足
(C106.2)，也不能据此推出精确支撑压缩。

**命题 C-106.3（联合人口解除 $R_+$ 的族承诺及等号处的复相干反例）。** 对任意
$\Gamma\in\mathfrak D$，令 $c=c_{0,13}$，则

$$
p_R(\Gamma)=1/5+\operatorname{Re}c,\qquad
p_R(\Gamma)\ne1/5\ \Longrightarrow\ \Gamma\text{ 非 PPT 且纠缠}.
\tag{C106.7}
$$

该蕴含不需要 C-105.2 的 $\Gamma_t$ 承诺，亦不需要 $q=1/5$。
即使另有原 $Q$ 约束，$p_R=1/5$ 仍不能认证可分离。

证明。$R_+$ 的两个对角项各贡献 $1/10$，两个交叉项合计贡献
$\operatorname{Re}c$。若响应不等于 $1/5$，则 $c\ne0$，由 (C106.6) 得非 PPT。
为验证等号处的不完备性，取任意实数 $0<|\eta|\le1/5$，定义

$$
\widetilde\Gamma_\eta
=S+i\eta\bigl(|e_0\rangle\langle e_{13}|
              -|e_{13}\rangle\langle e_0|\bigr).
\tag{C106.8}
$$

其 $e_0,e_{13}$ 块是 $\begin{pmatrix}1/5&i\eta\\-i\eta&1/5\end{pmatrix}$，
特征值 $1/5\pm|\eta|$；其余三个匹配向量各有特征值 $1/5$，其余二十维为零。
所以这是迹一正半定复密度算子，全部人口满足 (C106.2)。
$\operatorname{Re}(i\eta)=0$ 给 $p_R(\widetilde\Gamma_\eta)=1/5$。
$\Omega$ 在这些向量上的系数均为实数；特别其 $e_0,e_{13}$ 系数同为 $1/2$，
故反对称的纯虚交叉项对 $Q$ 的贡献为
$(i\eta-i\eta)/4=0$。因此

$$
q(\widetilde\Gamma_\eta)=1/5,\qquad
\widetilde\Gamma_\eta\in\mathfrak F,\qquad
\operatorname{spec}\left(
\left.\widetilde\Gamma_\eta^{\mathsf T_2}\right|_{
\operatorname{span}\{|0,0\rangle,|13,13\rangle\}}
\right)=\{+|\eta|,-|\eta|\}.
\tag{C106.9}
$$

它与 $S$ 在全部原菜单和新增 $R_+$ 上均不可区分，却仍纠缠。证毕。

**命题 C-106.4（C-105 读口在有泄漏时的无承诺认证）。** 对任意复二份密度算子
$\Gamma$，不施加人口纤维或状态族限制，记

$$
\begin{aligned}
d_0&=p_{0,13}(\Gamma),&d_{13}&=p_{13,0}(\Gamma),\\
x&=p_{0,0}(\Gamma),&y&=p_{13,13}(\Gamma),\\
c&=\langle0,13|\Gamma|13,0\rangle,&
g&=p_R(\Gamma)-\tfrac12(d_0+d_{13})=\operatorname{Re}c.
\end{aligned}
\tag{C106.10}
$$

所有 $d_0,d_{13},x,y$ 非负。PPT 必须满足

$$
|c|^2\le xy,\qquad |g|\le\sqrt{xy};\qquad
|g|>\sqrt{xy}\ \Longrightarrow\ \Gamma\text{ 非 PPT 且纠缠}.
\tag{C106.11}
$$

不违反这些不等式不能认证一般二份态可分离。

证明。这里消费 Peres PPT 必要条件及正半定二阶主子式条件：
$\Gamma^{\mathsf T_2}$ 在 $|0,0\rangle,|13,13\rangle$ 上的压缩恰为
$\begin{pmatrix}x&c\\\overline c&y\end{pmatrix}$。
若其正半定，行列式 $xy-|c|^2\ge0$。
由 $|\operatorname{Re}c|\le|c|$ 与 $x,y\ge0$ 得所列读口界；违反它即可排除 PPT。
这是已知正性判据在当前读口中的参数对应，不另立一般正性定理。
对 $g$ 的正方向，还可使用线性算子

$$
W=\tfrac12(P_0\otimes P_0+P_{13}\otimes P_{13})
  -R_++\tfrac12(P_0\otimes P_{13}+P_{13}\otimes P_0),
\qquad \operatorname{tr}(W\Gamma)=\tfrac{x+y}{2}-g.
\tag{C106.12}
$$

其期望等于 $z_-=(|0,0\rangle-|13,13\rangle)/\sqrt2$ 在部分转置下的二次型，
故在所有 PPT 态上非负。算术–几何均值给 $\sqrt{xy}\le(x+y)/2$，
所以根号界在不对称泄漏下至少与这一固定线性界一样强；在 $x=y$ 时二者相同。
在 $\mathfrak D$ 上 $x=y=0$、$d_0=d_{13}=1/5$，恢复 (C106.7)，
而不曾把一般来源换成 $\Gamma_t$。证毕。

**定理 C-106.5（C-105 连续混态族的白噪声 PPT 与可分离精确阈值）。** 对所有实数
$t,\epsilon\in[0,1]$，定义归一化密度算子

$$
\Gamma_{t,\epsilon}=(1-\epsilon)\Gamma_t+\epsilon I_{25}/25,
\qquad \epsilon_*(t)=\frac{5t}{1+5t}.
\tag{C106.13}
$$

则

$$
\Gamma_{t,\epsilon}\text{ 可分离}
\quad\Longleftrightarrow\quad\Gamma_{t,\epsilon}^{\mathsf T_2}\succeq0
\quad\Longleftrightarrow\quad\epsilon\ge\epsilon_*(t).
\tag{C106.14}
$$

(C106.11) 的同一人口与 $R_+$ 见证恰好检测 $\epsilon<\epsilon_*(t)$ 的全部态。

证明。C-105.3 已给 $\Gamma_t$ 的密度性，白噪声凸组合仍为密度算子。
置

$$
a=\frac{(1-\epsilon)t}{5},\qquad \delta=\frac\epsilon{25},\qquad
h=\frac{1-\epsilon}{5};\qquad a,\delta,h\ge0.
\tag{C106.15}
$$

匹配基人口均为 $h+\delta$，其余二十格均为 $\delta$；
四个底面匹配向量之间的非对角元为 $\pm a$，与 $e_2$ 相接者均为零。
因此选定块和见证读数为

$$
\begin{aligned}
\left.\Gamma_{t,\epsilon}^{\mathsf T_2}\right|_{
\operatorname{span}\{|0,0\rangle,|13,13\rangle\}}
 &=\begin{pmatrix}\delta&a\\a&\delta\end{pmatrix},\\
d_0=d_{13}&=h+\delta,\quad x=y=\delta,\\
p_R(\Gamma_{t,\epsilon})&=h+\delta+a,\quad g=a,\quad
\operatorname{tr}(W\Gamma_{t,\epsilon})=\delta-a.
\end{aligned}
\tag{C106.16}
$$

故 $\delta<a$ 时 $z_-$ 给严格负二次型，而根号见证也恰好违反。
其余四角对的部分转置块同样有特征值 $\delta\pm a$。
完整块谱为五个 $h+\delta$、六个 $\delta+a$、六个 $\delta-a$ 和八个 $\delta$，
因此 PPT 当且仅当 $\delta\ge a$。因 $1+5t>0$，

$$
\delta\ge a
\quad\Longleftrightarrow\quad\epsilon\ge5(1-\epsilon)t
\quad\Longleftrightarrow\quad\epsilon\ge\frac{5t}{1+5t}.
\tag{C106.17}
$$

PPT 的这一计算还不足以证明可分离；下面给出实际的可分离上证书。
第二份的底面投影记为 $P_{\mathrm b}=I_5-P_2$。由式 (C105.7) 的偏迹计算，
$\operatorname{Tr}_1|\Psi\rangle\langle\Psi|=P_{\mathrm b}/4$。
消费可分离锥的秩一加约化矩阵供应，得到

$$
C_\Psi=|\Psi\rangle\langle\Psi|+I_5\otimes(P_{\mathrm b}/4)
\quad\text{可分离},\qquad
\operatorname{tr}C_\Psi=1+5=6,\qquad \omega_\Psi=C_\Psi/6.
\tag{C106.18}
$$

这里的供应也可由 Vidal–Tarrach 的纯态 random robustness 精确实例得到。
$\Psi$ 在 $\mathbb C^5\otimes\operatorname{ran}P_{\mathrm b}\cong\mathbb C^5\otimes\mathbb C^4$
中有四个 Schmidt 系数 $1/2$。原文
[quant-ph/9806094](https://arxiv.org/abs/quant-ph/9806094)，印刷页 15 式 (41)、
附录 B.2 式 (B.29)–(B.33)，采用
$(|\Psi\rangle\langle\Psi|+sI_{n_1n_2}/(n_1n_2))/(1+s)$，
且 $s=n_1n_2a_1a_2$。
代入 $n_1=5,n_2=4,a_1=a_2=1/2$ 得 $s=5$，所以
$(|\Psi\rangle\langle\Psi|+I_{20}/4)/6$ 明确可分离；
将第二份四维空间局部等距嵌入 $H$ 即得 $\omega_\Psi$。
这是对纯态 $\Psi$ 应用该定理，不是对混态 $\Gamma_t$ 直接套用纯态公式。

令两个明确的产品密度态为
$D_2=P_2\otimes P_2=|e_2\rangle\langle e_2|$、
$J_2=(I_5/5)\otimes P_2$。当 $\delta\ge a$ 时，有实际凸分解

$$
\boxed{\quad
\Gamma_{t,\epsilon}
=(1-\epsilon)(1-t)S+aD_2+24a\,\omega_\Psi+5aJ_2
                  +25(\delta-a)\frac{I_{25}}{25}.
\quad}
\tag{C106.19}
$$

验证等式：$24a\omega_\Psi=4a|\Psi\rangle\langle\Psi|+aI_5\otimes P_{\mathrm b}$，
$5aJ_2=aI_5\otimes P_2$，二者的产品背景合为 $aI_{25}$；
再加末项成为 $\delta I_{25}$。
余下 $aD_2+4a|\Psi\rangle\langle\Psi|=(1-\epsilon)tT$，
因而恢复 (C106.13)。五个权重均非负，而且

$$
(1-\epsilon)(1-t)+a+24a+5a+25(\delta-a)
=(1-\epsilon)(1-t)+5a+\epsilon=1.
\tag{C106.20}
$$

所有分量都可分离且归一化，故这是可分离上证书，而非 PPT 充分性的推断。
结合 Peres 必要条件和 (C106.17) 得三重等价。

在边界处 $\delta=a=t/[5(1+5t)]$，末项权重为零，其余权重依次为

$$
\frac{1-t}{1+5t},\qquad\frac{t}{5(1+5t)},\qquad
\frac{24t}{5(1+5t)},\qquad\frac{t}{1+5t},
\tag{C106.21}
$$

仍为和一的非负数。$t=0$ 时 $\epsilon_*=0$，整条噪声线是
$(1-\epsilon)S+\epsilon I_{25}/25$，均可分离；$\epsilon=0,t>0$ 恢复 C-105 的非 PPT 态。
$t=1$ 时阈值为 $5/6$，边界分解为
$D_2/30+(4/5)\omega_\Psi+J_2/6$，三项权重和为一。
$\epsilon=1$ 时 $a=0$，(C106.19) 只剩 $I_{25}/25$。
故全部闭区间端点均已包含。证毕。

(C106.19) 使本族的 PPT 阈值与可分离阈值相同；其已知供应为纯态 robustness 与可分离锥，
当前结论是 C-105 混态族及实际读口的对应应用，不作原创性主张。
若只观测到 (C106.16) 中的部分读数而没有整族承诺，违反见证仍能认证纠缠，
不违反见证却不能借用本族的可分离分解。特别加噪后不沿用无泄漏的固定阈值 $p_R>1/5$。

**命题 C-106.6（同一见证的局部 $X/Y$ 乘积期望对应）。** 在两份空间分别定义

$$
\begin{aligned}
A&=|0\rangle\langle13|,&X_1&=A+A^\dagger,&Y_1&=-i(A-A^\dagger),\\
B'&=|13\rangle\langle0|,&X_2&=B'+B'^\dagger,&Y_2&=-i(B'-B'^\dagger).
\end{aligned}
\tag{C106.22}
$$

对任意复密度 $\Gamma$ 和 (C106.10) 的同一个 $c$，有

$$
\begin{aligned}
R_+&=\tfrac12(P_0\otimes P_{13}+P_{13}\otimes P_0)
       +\tfrac14(X_1\otimes X_2-Y_1\otimes Y_2),\\
\operatorname{Re}c&=\tfrac14\bigl(\langle X_1\otimes X_2\rangle_\Gamma
                                  -\langle Y_1\otimes Y_2\rangle_\Gamma\bigr),\\
\operatorname{Im}c&=-\tfrac14\bigl(\langle X_1\otimes Y_2\rangle_\Gamma
                                   +\langle Y_1\otimes X_2\rangle_\Gamma\bigr).
\end{aligned}
\tag{C106.23}
$$

若各局部设置确实可用上述算子的全部谱效果，局部相位参照按 (C106.22) 对齐，
且各设置采样同一实际稳定来源 $\Gamma$，则乘积结果的平均值可重建同一见证期望。
这里要求的谱结果为 $-1,0,+1$，包含该两维子空间外的零结果；每个谱效果须是实际可用的测量效果。

证明。$A\otimes B'=|e_0\rangle\langle e_{13}|$。
展开 $X_1\otimes X_2-Y_1\otimes Y_2$ 得
$2(A\otimes B'+A^\dagger\otimes B'^\dagger)$，
展开 $X_1\otimes Y_2+Y_1\otimes X_2$ 得
$-2i(A\otimes B'-A^\dagger\otimes B'^\dagger)$。
而 $\operatorname{tr}((A\otimes B')\Gamma)=\overline c$，
所以实部与虚部的符号如 (C106.23) 所列。
$X_j,Y_j$ 在所选两维空间上为 Pauli 算子，在其正交补上为零。
若 $E^{(1)}_\lambda,E^{(2)}_\mu$ 为实际可用的局部谱效果，
联合结果概率为 $\operatorname{tr}((E^{(1)}_\lambda\otimes E^{(2)}_\mu)\Gamma)$，
按 $\lambda\mu$ 加权求和恰为相应乘积算子的期望。
这个恒等式不要求两份独立；它要求各设置的概率来自同一实际状态，
否则不同来源的四个期望不能组合成某一个 $c$。证毕。

期望的这种线性重建不等于 $R_+$ 二元投影仪器的选择后状态或扰动合同。
谱效果的数学存在亦不证明 AURIC FIB 原生控制具备这些设置、相位对齐或物理实现。
这些结论不改变每份底面 concurrence 的分割，也不把非零来源协方差直接当作纠缠。
C-104 的全输入 flagged CPTP 编解码与通用端口维数合同仍须各自证明；
局部乘积期望对应没有供应这些全称映射。

## 追加锚（本行以下为增补区）

## 107. 匹配人口纤维的完整线性认证与整态独立副本纯度

**定义 C-107.1（同一人口纤维的实方向与固定读数）。** 沿用 C-106 的
$B=(0,1,2,3,13)$、$f$、$e_s=|s,f(s)\rangle$、$\mathcal E$、$S$、
$\mathfrak D$、$\mathfrak F$ 和 $Q$。令 $J:\mathbb C^5\to H^{(1)}\otimes H^{(2)}$
为 $J|s\rangle=e_s$ 的等距嵌入，$J^\dagger J=I_5$。
C-106.2 给每个 $\Gamma\in\mathfrak D$ 唯一的压缩
$C=J^\dagger\Gamma J$，满足 $\Gamma=JCJ^\dagger$、$C\succeq0$、$C_{ss}=1/5$。
定义实向量空间及实线性泛函

$$
\begin{aligned}
V&=\{X\in M_5(\mathbb C):X=X^\dagger,\ X_{ss}=0\ (s\in B)\},\\
\ell_Q(X)&=\operatorname{tr}(J^\dagger QJX),\qquad V_Q=\ker\ell_Q\subset V,\\
\mathfrak D&=\{J(I_5/5+X)J^\dagger:X\in V,\ I_5/5+X\succeq0\},\\
\mathfrak F&=\{J(I_5/5+X)J^\dagger:X\in V_Q,\ I_5/5+X\succeq0\}.
\end{aligned}
\tag{C107.1}
$$

Hermitian 算子的迹配对为实数。对任意有限固定 Hermitian 菜单
$\mathcal A=(A_1,\ldots,A_m)$，每个 $A_j$ 作用在原来的 $25$ 维二体空间，设

$$
\begin{aligned}
M_{\mathcal A}(\Gamma)&=(\operatorname{tr}(A_j\Gamma))_{j=1}^m,\\
L_{\mathcal A}(X)&=(\operatorname{tr}(J^\dagger A_jJX))_{j=1}^m,\\
M_{\mathcal A}(\Gamma)-M_{\mathcal A}(S)&=L_{\mathcal A}(X).
\end{aligned}
\tag{C107.2}
$$

这里的固定菜单独立于未知输入；所有读数是同一实际 $\Gamma$ 的精确总体期望。
在 $\mathcal K=\mathfrak D$ 或 $\mathfrak F$ 上的“完整纠缠分类”指存在函数
$d:M_{\mathcal A}(\mathcal K)\to\{0,1\}$，使对每个 $\Gamma\in\mathcal K$，
$d(M_{\mathcal A}(\Gamma))=0$ 当且仅当 $\Gamma$ 对原分割
$H^{(1)}\mid H^{(2)}$ 可分离。$d$ 可非线性；限制在于输入数据是固定单副本线性菜单。

**定理 C-107.2（C-106 纤维上分类完备性恰为受限层析完备性）。** 对上述每个
有限固定菜单，以下四个条件在 $\mathcal K=\mathfrak D$ 上等价：

1. 菜单在 $\mathcal K$ 上完整分类纠缠。
2. $\{\Gamma\in\mathcal K:M_{\mathcal A}(\Gamma)=M_{\mathcal A}(S)\}=\{S\}$。
3. $\ker(L_{\mathcal A}|_V)=\{0\}$。
4. $M_{\mathcal A}$ 在 $\mathcal K$ 上单射。

在 $\mathcal K=\mathfrak F$ 上，完全相同的四条件等价，但第三条必须换成
$\ker(L_{\mathcal A}|_{V_Q})=\{0\}$。

证明。C-106.2 说明两个集合中唯一可分离态均为 $S$。
所以分类函数存在当且仅当没有纠缠态与 $S$ 共用读数，即第一、二条等价。
若受限核为零，式 (C107.2) 立即给第二条；任意两个状态之差均在相应方向空间中，
因而也给第四条。第四条蕴含第二条，因为 $S$ 本身属于集合。

反之，若 $0\ne X$ 属于相应受限核，令 $\|X\|_{\rm op}$ 为压缩空间上的算子范数。
对任何实数 $\varepsilon$ 满足

$$
0<|\varepsilon|<\frac1{5\|X\|_{\rm op}},\qquad
I_5/5+\varepsilon X\succeq
(1/5-|\varepsilon|\|X\|_{\rm op})I_5\succ0,
\tag{C107.3}
$$

$\Gamma_\varepsilon=J(I_5/5+\varepsilon X)J^\dagger$ 就是人口仍精确固定的密度态。
在 $V_Q$ 情形，$\ell_Q(X)=0$ 又保持 $q=1/5$。
它不等于 $S$，故按 C-106.2 纠缠；线性性给它与 $S$ 的所有菜单期望相同，
违反第二条。这证明必要性。证毕。

式 (C107.3) 的严格正性只在五维匹配支撑 $\mathcal E$ 内成立。
$S$ 在整个 $25$ 维空间的秩为五；沿 $\mathcal E^\perp$ 增加任意方向并不合法。
这里没有使用 $S$ 是全部二体密度态集合的内点，而是使用它是人口纤维在指定仿射空间中的相对内点。

该核与差空间判据复用 Heinosaari–Mazzarella–Wolf，
*Quantum Tomography under Prior Information*，
[arXiv:1109.5478](https://arxiv.org/abs/1109.5478)，Proposition 2 及其后自伴期望的 Definition 2；
其 Proposition 1 区分算子空间维数与 POVM 结果数。
Carmeli–Heinosaari–Maniscalco–Schultz–Toigo，
*Determining quantum coherence with minimal resources*，
[arXiv:1708.05597v1](https://arxiv.org/abs/1708.05597v1)，Theorems 1–2，
在完整正交基测量模型中用不可见扰动刻画相干检测，并由检测得到全部非对角元。
本条应用的是 C-106 特定支撑内的唯一可分离点与固定人口，
并把既知 $Q$ 的额外限制保留；没有将该文关于基测量的设置数结论移作任意菜单的结论。

**推论 C-107.3（锐利的独立实统计量数）。** 以 (C107.2) 在相应方向空间上的秩
计独立新增实统计量，$\mathfrak D$ 的完整分类恰需秩 $20$；
在 $\mathfrak F$ 中已知原 $Q$ 约束时，新增菜单恰需在 $V_Q$ 上有秩 $19$。
这两个数都可由抽象 Hermitian 菜单达到。

证明。十个无序匹配对各有任意复数 $X_{sa}$，下三角由共轭确定，对角为零，故

$$
\dim_{\mathbb R}V=2\binom52=20.
\tag{C107.4}
$$

令 $x_{sa}=\operatorname{Re}X_{sa}$，按 $s<a$ 的模式顺序，
$J^\dagger\Omega=(1,-1,0,-1,1)^T/2$ 给

$$
\ell_Q(X)=\tfrac12(
 x_{0,13}+x_{1,3}-x_{0,1}-x_{0,3}-x_{1,13}-x_{3,13}).
\tag{C107.5}
$$

取 $X=|0\rangle\langle13|+|13\rangle\langle0|$ 即得 $\ell_Q(X)=1/2$，
所以它确为非零实线性约束，$\dim_{\mathbb R}V_Q=19$。
秩–零化度与 C-107.2 给必要性和充分性；列出 $m$ 个值只给秩不超过 $m$，
重复、依赖或在纤维上恒定的期望不计新方向。

具体地，设 $K_{sa}=|e_s\rangle\langle e_a|$。全部十对的两个 Hermitian 算子

$$
H^R_{sa}=K_{sa}+K_{sa}^\dagger,\qquad
H^I_{sa}=i(K_{sa}-K_{sa}^\dagger)
\tag{C107.6}
$$

在 $\Gamma=JCJ^\dagger$ 上的期望依次为
$2\operatorname{Re}c_{sa}$、$2\operatorname{Im}c_{sa}$，因为
$\operatorname{tr}(K_{sa}\Gamma)=c_{as}=\overline{c_{sa}}$。
这二十个实坐标达到 (C107.4)。在 $\mathfrak F$ 上可删去
$H^R_{0,13}$：保留其余十九坐标，由 (C107.5) 的零值恢复

$$
\operatorname{Re}c_{0,13}=
\operatorname{Re}c_{0,1}+\operatorname{Re}c_{0,3}
+\operatorname{Re}c_{1,13}+\operatorname{Re}c_{3,13}
-\operatorname{Re}c_{1,3}.
\tag{C107.7}
$$

故十九也是可达下界；这里的人口与原 $Q$ 已给定，不计入新增预算。证毕。

这些数计的是精确期望的独立实方向，既不是测量设置数，也不是试验次数。
例如一个 $k$ 结果的归一化 POVM 完整概率律只有至多 $k-1$ 个独立差方向；
若只用这一个 POVM 的完整律补足人口纤维，分别须有 $k\ge21$ 或 $k\ge20$。
它可以只有一个设置。抽象达到性也不要求把每个坐标作为一个独立设置：
取相应方向空间的一组 Hermitian 对偶代表 $B_1,\ldots,B_n$，
在 $\mathcal E$ 上令 $E_j=I_5/(n+1)+\delta B_j$（$1\le j\le n$）、
$E_{n+1}=I_5/(n+1)-\delta\sum_jB_j$，充分小的 $\delta>0$ 保证全部效果非负且和为 $I_5$。
在 $\mathcal E^\perp$ 上把恒等效果并入最后一项，就得到原空间上 $n+1$ 结果的 POVM；
在人口纤维上其完整律的秩为 $n$。这是上述 Proposition 1 的有限维正性构造的受限应用，
不供应实际装置、有限样本精度或这些效果的原生可执行性。

**命题 C-107.4（四模式菜单遗漏中模式的八个实方向）。** 令
$\mathcal E_4=\operatorname{span}\{e_0,e_1,e_3,e_{13}\}$、$P_4$ 为其正交投影。
即使给定全部满足 $A=P_4AP_4$ 的 Hermitian 观测，其在 $V$ 上的共同不可见方向仍恰为

$$
\mathcal N_2=\left\{
\sum_{a\in\{0,1,3,13\}}
\bigl(z_a|e_2\rangle\langle e_a|+
\overline{z_a}|e_a\rangle\langle e_2|\bigr):z_a\in\mathbb C
\right\},\qquad \dim_{\mathbb R}\mathcal N_2=8.
\tag{C107.8}
$$

式中把方向经 $J$ 嵌回原空间。$\mathcal N_2\subset V_Q$，故加上原 $Q$ 仍不能消掉这八维。
全体四模式观测在 $V$ 上秩为十二，在 $V_Q$ 上秩为十一。

证明。与所有四模式 Hermitian 算子的迹配对为零，等价于
$P_4XP_4=0$。零对角条件留下的仅是四条连接 $e_2$ 的复相干，给 (C107.8)；
反向每一这样的方向显然不可见。$\Omega\in\mathcal E_4$ 给 $\ell_Q=0$。
四模式内部六个复相干给十二实维，(C107.5) 是它们中一个非零约束；
所以在 $V_Q$ 上只剩十一维可见，八维不可见。证毕。

更具体地，任取 $z=(z_a)_{a\in\{0,1,3,13\}}\in\mathbb C^4$，令
$Z_z$ 为 (C107.8) 中的矩阵，定义

$$
\Gamma_z=S+Z_z,\qquad
\|z\|_2\le1/5.
\tag{C107.9}
$$

$Z_z$ 在 $\mathcal E$ 上的特征值为 $+\|z\|_2,-\|z\|_2,0,0,0$：
当 $z\ne0$ 时只须在 $e_2$ 与 $\sum_a\overline{z_a}e_a/\|z\|_2$ 张成的二维空间上取谱。
因而 $\Gamma_z$ 在该支撑上谱为
$1/5\pm\|z\|_2,1/5,1/5,1/5$，在其余二十维为零。
它保持原全部二十五个人口、$q=1/5$ 和所有四模式期望；
只要 $z\ne0$，C-106.2 就给纠缠。这是实在的合法反例族，包含边界 $\|z\|_2=1/5$；
不只是忽略正性的线性核计数。其纯度为 $1/5+2\|z\|_2^2$。

(C107.6) 的五模式达到性包含这四条连接，不能只检查原四角相位。
如另外实际允许对每一对 $s<a$ 使用局部算子
$D=|s\rangle\langle a|$、$F=|f(s)\rangle\langle f(a)|$，
设 $X_D=D+D^\dagger$、$Y_D=-i(D-D^\dagger)$，$X_F,Y_F$ 同理，则

$$
\begin{aligned}
\langle X_D\otimes X_F-Y_D\otimes Y_F\rangle_\Gamma
 &=4\operatorname{Re}c_{sa},\\
\langle X_D\otimes Y_F+Y_D\otimes X_F\rangle_\Gamma
 &=-4\operatorname{Im}c_{sa}.
\end{aligned}
\tag{C107.10}
$$

这是 C-106.6 的同一个局部乘积展开，第二式的负号来自
$\operatorname{tr}((D\otimes F)\Gamma)=\overline{c_{sa}}$。
将这些期望解释为实验读数，须实际拥有各局部算子全部 $-1,0,+1$ 谱效果、
按上述有序模式对齐的复相位参照，并使不同设置采样同一稳定来源 $\Gamma$。
这些乘积观测不要求原 $H^{(1)}$ 与 $H^{(2)}$ 独立；目标正是它们可能纠缠的联合态。
期望重建不等于投影仪器及其选择后状态等价，也不提供任何原生 FIB 控制。

**定理 C-107.5（同一原二体态的纯度完整判据）。** 对每个
$\Gamma=JCJ^\dagger\in\mathfrak D$，包括 $\mathfrak F$ 的全部复输入，

$$
\begin{aligned}
\operatorname{tr}\Gamma^2
 &=\operatorname{tr}C^2
 =\tfrac15+2\sum_{s<a}|c_{sa}|^2,\\
\Gamma\text{ 可分离}
 &\Longleftrightarrow\operatorname{tr}\Gamma^2=1/5,\\
\Gamma\text{ 纠缠}
 &\Longleftrightarrow\operatorname{tr}\Gamma^2>1/5.
\end{aligned}
\tag{C107.11}
$$

证明。等距嵌入和迹循环性给首个等号。
Hermitian 性给 $\operatorname{tr}C^2=\sum_{s,a}|c_{sa}|^2$，
五个对角各贡献 $1/25$，十个非对角无序对各贡献两次。
余项非负且同时为零当且仅当 $C=I_5/5$。
最后使用 C-106.2，而不是把一般混态的“纯度大”误当一般纠缠充分条件。证毕。

这里测的是原来整个 $H_5^{(1)}\otimes H_5^{(2)}$ 上 $\Gamma$ 的纯度，
不是每份 $H_5$ 的纯度，也不是 C-94 的底面条件态纯度。
完整单副本线性数据本身能由 (C107.11) 后处理计算纯度；
单个二次函数完成此特殊分类，不反驳 C-107.3 对固定线性输入的下界。

**定义 C-107.6（四个物理因子与整份交换）。** 将一份原二体系统重命名为
$A\otimes B=H_5^{(1)}\otimes H_5^{(2)}$，为它准备第二份 $A'\otimes B'$。
四因子顺序固定为 $A,B,A',B'$，每因子五维。
$\Gamma$ 的纠缠始终指 $A\mid B$；两副本的分割是
$(A\otimes B)\mid(A'\otimes B')$，两者不同。
整份交换 $W$ 定义为

$$
W|a,b,a',b'\rangle=|a',b',a,b\rangle,
\qquad W=W^\dagger,\quad W^2=I.
\tag{C107.12}
$$

它同时交换 $A\leftrightarrow A'$、$B\leftrightarrow B'$，
在重排为 $A,A',B,B'$ 后为 $F_{AA'}\otimes F_{BB'}$。
$W$ 不等于原系统内部交换 $A\leftrightarrow B$，也不等于 C-106 的秩一 $Q$。

**命题 C-107.7（实际独立整份副本的交换读数）。** 若单轮实际输入确为
$\Gamma_{AB}\otimes\Gamma_{A'B'}$，两份在已对齐的模式识别下具有同一密度矩阵，
并且允许测量 $W$ 的谱效果 $(I\pm W)/2$，则

$$
\begin{aligned}
\langle W\rangle_{\Gamma\otimes\Gamma}
 &=\operatorname{tr}(\Gamma^2),\\
\Pr(+)&=\tfrac12(1+\operatorname{tr}\Gamma^2),\qquad
\Pr(-)=\tfrac12(1-\operatorname{tr}\Gamma^2).
\end{aligned}
\tag{C107.13}
$$

因此在 $\mathfrak D$ 或 $\mathfrak F$ 的精确人口承诺下，
$\langle W\rangle=1/5$ 当且仅当原 $A\mid B$ 可分离，
$\langle W\rangle>1/5$ 当且仅当它纠缠。

证明。对于原 $25$ 维空间上的任意矩阵 $G,H$，逐指标计算给

$$
\operatorname{tr}(W(G\otimes H))
=\sum_{u,v}G_{vu}H_{uv}=\operatorname{tr}(GH).
\tag{C107.14}
$$

在同一个实际输入上取 $G=H=\Gamma$，再对 $W$ 的两个谱效果取迹，得到 (C107.13)；
C-107.5 完成分类。没有用单纯的 $\operatorname{tr}(G\otimes H)$ 乘法公式替代交换恒等式。证毕。

这是 Ekert–Alves–Oi–Horodecki–Horodecki–Kwek，
*Direct estimations of linear and nonlinear functionals of a quantum state*，
[quant-ph/0203016v1](https://arxiv.org/abs/quant-ph/0203016v1)，式 (2)、(4) 的整态参数应用。
Filip 的预印本 [quant-ph/0108119](https://arxiv.org/abs/quant-ph/0108119)，
发表为 *Overlap and entanglement-witness measurements*，
[Phys. Rev. A 65, 062320](https://doi.org/10.1103/PhysRevA.65.062320)，
式 (12)–(15) 明确区分无相关输入的重叠与一般相关输入的交换读数。
Brun，*Measuring polynomial functions of states*，
[quant-ph/0401067](https://arxiv.org/abs/quant-ph/0401067)，将密度矩阵的多项式写为张量幂上的期望；
该表示与制备、操作的实际可取得性是不同前提。
C-94–C-101 已使用副本纯度和相关来源边界，本条把载体换回 C-106 的完整 $\Gamma$，
并消费其特定人口纤维上的完整分类，而不另称交换测纯度为新结果。

**命题 C-107.8（相同整份边缘的相关输入障碍）。** 在上述四因子空间上取

$$
\Xi=\tfrac15\sum_{s\in B}
 |e_s\rangle\langle e_s|_{AB}\otimes
 |e_s\rangle\langle e_s|_{A'B'}.
\tag{C107.15}
$$

它是归一化正半定密度算子，两个整份边缘都恰为 $S$，但

$$
\operatorname{Tr}_{A'B'}\Xi=\operatorname{Tr}_{AB}\Xi=S,\qquad
\operatorname{tr}(W\Xi)=1\ne1/5=\operatorname{tr}S^2.
\tag{C107.16}
$$

证明。五个正交匹配向量各自归一化，偏迹逐项留下
$(1/5)|e_s\rangle\langle e_s|$。每个 $e_s\otimes e_s$ 是 $W$ 的 $+1$ 特征向量，
故交换期望为一。独立输入 $S\otimes S$ 则由 (C107.14) 给 $1/5$。
所以相同边缘没有固定这个二副本联合期望。
$\Xi$ 甚至是四个五维因子上的产品纯态凸组合；这里的差异不需要副本间纠缠。
若把一错误归为边缘 $S$ 的纯度，再按 (C107.11) 分类，就会把可分离 $S$ 误判为纠缠。证毕。

(C107.13) 的输入假设要求实际联合态为张量平方，不只是两边缘相等、同名来源、
相同人口或共同未知参数。它的结论只规定单轮期望；任何跨轮估计还须相应的来源稳定性或条件统计假设。
独立重新制备同一 $\Gamma$ 是制备合同，数学映射 $\Gamma\mapsto\Gamma\otimes\Gamma$
不是从一份未知输入执行克隆的操作。
一个整态交换期望与二十或十九个线性坐标的比较，不能推出设置、样本数或装置成本的节省。
这些结论不建立自适应协议的一般下界、有限样本的无误完整分类、原生 FIB 实现、物理压缩或仪器等价。
《递归关系观察：量子端口协变与认证前沿》§1 的独立 $\mathbb C^5$ 制备及等待、完整秩一仪器菜单
明确不含来源副本和任意未来控制；它不供应本条的整态副本及交换谱测量权限。

## 追加锚（本行以下为增补区）

## 108. 实际局部行走菜单的匹配来源不可见纤维、锐利纯度与十四旗擦除

**假设 C-108.1（原二体来源上的条件性局部菜单）。** 保留 C-106–C-107 的同一个
$A\mid B=H^{(1)}\mid H^{(2)}$、$B=(0,1,2,3,13)$、
$f(0)=13,f(13)=0,f(1)=3,f(3)=1,f(2)=2$、$e_s=|s,f(s)\rangle$、
$J|s\rangle=e_s$、$S=JI_5J^\dagger/5$、$Q$ 和精确人口纤维 $\mathfrak D$。
将两边各自的有序局部基按位置对应为

$$
\begin{array}{c|ccccc}
\text{原标签}&0&1&2&3&13\\ \hline
\text{行走标签}&N&2&3&5&25
\end{array}.
\tag{C108.1}
$$

每边使用《递归关系观察：量子测量相对边界》（下称 QMB）假设 1.1 的同一个
$K$、$U(t)=e^{-itK}$、$t\ge0$ 和完整五结果秩一 Lüders 读数；
允许 Stop。条件性双边合同允许局部作用 $U(t)\otimes I$、$I\otimes U(u)$、
两边的完整局部读数，以及按已保留的双方经典记录选取后续局部动作。
两边的非负等待可分别选择；局部 Stop 后不再对该边作用。
每个策略有有限深度，所有有限深度都纳入比较。
输入无关的随机控制资源、策略及其记录规则在比较的两个输入间相同。
完整历史保留两边结果、动作及停止；事件分组仅是这些记录的经典后处理。
记完整历史律为 $P_\Gamma^\pi$，所有这些策略组成 $\mathcal M_{\rm loc}$。

这是对同一份可能相关的 $\Gamma_{AB}$ 的两个局部实例的访问假设，不要求
$\Gamma_{AB}=\rho_A\otimes\rho_B$。它不从单系统任意 $\mathbb C^5$ 输入制备、
原生树或其记忆合同推出；也不授予独立模式相位、任意酉、重置、源副本、
交换仪器、量子旁信息或隐藏 Kraus 记录。
不同设置的总体律均以同一矩阵 $\Gamma$ 为输入定义；若实际估计它们，来源跨设置
具有这个共同矩阵是额外的制备要求，不能由相同局部边缘代替。

**引理 C-108.2（被动匹配相位与全部有限历史的闭包）。** 在 (C108.1) 的顺序中令
$D=\operatorname{diag}(1,i,i,i,1)$，$d_s=D_{ss}$，并令

$$
\eta_s=d_sd_{f(s)},\qquad
(\eta_0,\eta_1,\eta_2,\eta_3,\eta_{13})=(1,-1,-1,-1,1),\qquad
Z=\operatorname{diag}(\eta_s).
\tag{C108.2}
$$

则 $(D\otimes D)J=JZ$。$\mathcal M_{\rm loc}$ 的每个确定控制完整分支的效果
属于

$$
\left\{DH D^\dagger\otimes DL D^\dagger:
             H,L\in\operatorname{Sym}_5(\mathbb R),\ H,L\succeq0\right\}.
\tag{C108.3}
$$

全部历史事件和输入无关随机策略的效果属于这些乘积的非负和或积分。
全部可用双边效果的实线性张成，在 $J$ 压缩后恰为
$\operatorname{Sym}_5(\mathbb R)$；这里不声称每个张成成员本身是可执行效果。

证明。逐项乘相位得到 $1\cdot1,i\cdot i,i\cdot i,i\cdot i,1\cdot1$，
所以 (C108.2) 成立。QMB 定义 1.2 及《AURIC FIB 二阶关系完成》
定理 65.2–65.3 给被动帧中的真实等待
$O(t)=D^\dagger U(t)D$ 为实正交矩阵，完整读分支为实模式投影，
且实际单边效果实张成恰为 $D\operatorname{Sym}_5(\mathbb R)D^\dagger$。
这里复用其非负等待右导数张成证书，不把被动 $D$ 或导数作为控制。

固定一条双方完整记录后，自适应策略指定的每个动作都已确定；不同因子的作用交换，
该分支 Kraus 算子因而为 $M_h^A\otimes M_h^B$。
将每边所有实际等待和读分支按原次序相乘，得
$M_h^A=DL_h^AD^\dagger$、$M_h^B=DL_h^BD^\dagger$，其中 $L_h^A,L_h^B$ 为实矩阵。
其效果即 (C108.3)，取 $H=(L_h^A)^TL_h^A$、$L=(L_h^B)^TL_h^B$。
未读的一边也适用，空乘积为恒等。
经典策略的分支权重只乘上输入无关非负系数；互斥记录求和给事件。
对输入无关随机种子先固定种子作上述分支展开，再积分，给相同闭包。
因此使用未归一化分支即可处理零概率记录，无须对零概率事件作条件化。

对任意实对称 $H,L$，直接按匹配基计算

$$
\left[J^\dagger(DHD^\dagger\otimes DLD^\dagger)J\right]_{sa}
=\eta_s\eta_a H_{sa}L_{f(s)f(a)}.
\tag{C108.4}
$$

右边为实对称矩阵，给压缩张成的上界。
另一方面菜单包含两个互不依赖地预选等待的一读后 Stop 协议，故其效果张成包含
两个单边实际效果张成的张量积。
令 $E_{sa}=|s\rangle\langle a|$。
$H=E_{ss},L=E_{f(s)f(s)}$ 在 (C108.4) 给 $E_{ss}$；
当 $s\ne a$，$H=E_{sa}+E_{as}$、
$L=E_{f(s)f(a)}+E_{f(a)f(s)}$ 给
$\eta_s\eta_a(E_{sa}+E_{as})$。
每个 $H,L$ 都是单边实际效果的有限实线性组合，故这些乘积是实际乘积效果的有限实线性组合。
它们张成全部实对称矩阵，给下界，并证明增加上述经典自适应不会增加压缩后的方向。证毕。

**定理 C-108.3（原人口纤维上的双向全菜单等价与十维盲核）。** 对每个
$\Gamma=JCJ^\dagger\in\mathfrak D$，下列条件等价：

$$
\begin{aligned}
& P_\Gamma^\pi=P_S^\pi\quad\text{对每个 }\pi\in\mathcal M_{\rm loc};\\
& \operatorname{Re}C=I_5/5;\\
& C=I_5/5+iA,\qquad A\in M_5(\mathbb R),\quad A^T=-A,
                    \quad I_5/5+iA\succeq0.
\end{aligned}
\tag{C108.5}
$$

在 C-107 的二十维零对角 Hermitian 方向空间 $V$ 上，此实际菜单的秩与核维数
分别恰为 $10,10$，核为

$$
\mathcal N_{\rm loc}=i\operatorname{Skew}_5(\mathbb R).
\tag{C108.6}
$$

所有满足 (C108.5) 的态都还属于原 $Q$ 纤维 $\mathfrak F$。
在已知 $Q$ 的十九维 $V_Q$ 上，菜单的秩为九、核仍为十维。

证明。引理 C-108.2 说明整个菜单在匹配支撑内的效果恰张成实对称矩阵。
所以全部历史律相同，当且仅当 $C-I_5/5$ 与每个实对称矩阵的迹配对为零。
必要性也可直接用 (C108.4) 的无序对代表：对应差读数为
$2\eta_s\eta_a\operatorname{Re}c_{sa}$。
所有 $\eta_s$ 非零，故全部十个实部必须消失；对角已由人口给定。
反之，Hermitian 的 $C-I_5/5$ 若实部为零，恰能唯一写成 $iA$、$A$ 实反对称。
对任意实对称 $H$，

$$
\operatorname{tr}(AH)=\operatorname{tr}((AH)^T)
=\operatorname{tr}(H^TA^T)=-\operatorname{tr}(HA)
=-\operatorname{tr}(AH)=0.
\tag{C108.7}
$$

最后的零使用特征为零。故每个确定分支的差读数为零，非负和与积分仍为零，
给全体随机自适应历史的充分性。正性没有被丢弃：它保留为 (C108.5) 的明确条件。
这是 Heinosaari–Mazzarella–Wolf，
[arXiv:1109.5478v1](https://arxiv.org/html/1109.5478v1)，Proposition 2
的观察差空间判据在该匹配支撑上的应用。

零对角 Hermitian 矩阵的十个无序对各有一个实部和一个虚部。
菜单恰保留十个实部，十个虚部组成 (C108.6)；小范数的这些方向都可由正性内部
$I_5/5$ 实现，所以这不是包含非法扰动的虚假维数。
$J^\dagger QJ$ 是 C-107.3 已给的实对称矩阵，故 (C108.7) 使
$q(\Gamma)=q(S)=1/5$。原 $\ell_Q$ 在十维实部空间上非零，
已知它只消掉一个可见实方向，给 $V_Q$ 上的秩九与核十。证毕。

**定理 C-108.4（不可见来源的锐利整态纯度包络）。** 对所有满足 (C108.5) 的态，

$$
\boxed{\qquad \frac15\le\operatorname{tr}(\Gamma^2)\le\frac9{25}.\qquad}
\tag{C108.8}
$$

下界等号当且仅当 $\Gamma=S$。上界等号当且仅当 $iA$ 的谱为
$\{1/5,1/5,0,-1/5,-1/5\}$（计重数）；此时 $C$ 和 $\Gamma$ 的秩都是三。
除 $S$ 外，该不可见纤维的全部态对原来的 $A\mid B$ 分割纠缠。

证明。$H=iA$ 为 Hermitian，且逐项共轭满足 $\overline H=-H$。
若 $Hz=\lambda z$，$\lambda\in\mathbb R$，则
$H\overline z=-\lambda\overline z$。
共轭给 $\lambda$ 与 $-\lambda$ 特征空间之间的反线性双射，故重数相等。
五维 Hermitian 谱定理因此允许把 $H$ 的全部谱写为
$0,+a,-a,+b,-b$，其中 $a,b\ge0$，包括退化的 $a=0$ 或 $b=0$。
$C=I_5/5+H\succeq0$ 当且仅当 $a,b\le1/5$。
这里的谱配对由共轭与谱定理得到，不把一个额外的正交正规形当作新测量。
等距嵌入给

$$
\operatorname{tr}(\Gamma^2)=\operatorname{tr}(C^2)
=\frac15+2(a^2+b^2)
\in\left[\frac15,\frac15+\frac4{25}\right].
\tag{C108.9}
$$

下界等号迫使 $a=b=0$，Hermitian 性再给 $A=0$。
上界等号迫使 $a=b=1/5$，此时 $C$ 的非零谱恰为 $2/5,2/5,1/5$。
最后直接消费 C-106.2 的唯一可分离点结论，或 C-107.5 的同一整态纯度判据；
并非对一般混态以纯度单独判纠缠。
相应部分转置的已知块谱来源为 Rains，
[quant-ph/0008047v2](https://arxiv.org/html/quant-ph/0008047v2)，
§6 Lemma 6.3 的证明、式 (6.20)–(6.21)。证毕。

**命题 C-108.5（同一人口及原 $Q$ 纤维内达到每个中间值）。** 在原标签中定义

$$
\begin{aligned}
A_t&=\frac t5(E_{0,13}-E_{13,0}+E_{1,3}-E_{3,1}),\\
C_t&=I_5/5+iA_t,\qquad \widehat\Gamma_t=JC_tJ^\dagger,
                   \qquad 0\le t\le1.
\end{aligned}
\tag{C108.10}
$$

$\widehat\Gamma_t$ 的全部 $25$ 个人口和 $q=1/5$ 与 $S$ 相同，
它与 $S$ 的所有 $\mathcal M_{\rm loc}$ 历史律相同，且

$$
\operatorname{spec}(C_t)=
\left\{\frac{1+t}{5},\frac{1-t}{5},\frac{1+t}{5},\frac{1-t}{5},\frac15\right\},
\qquad
\operatorname{tr}(\widehat\Gamma_t^2)=\frac15+\frac{4t^2}{25}.
\tag{C108.11}
$$

因此 (C108.8) 的每个值都达到；$t=1$ 是合法归一化的秩三上端点。

证明。按 $(0,13)\mid(1,3)\mid(2)$ 分块，$C_t$ 是两个
$\frac15\left(\begin{smallmatrix}1&it\\-it&1\end{smallmatrix}\right)$
和单点 $1/5$ 的直和。
两个二维块的特征向量分别为 $(1,-i)^T/\sqrt2$、$(1,i)^T/\sqrt2$，
其特征值分别为 $(1+t)/5$、$(1-t)/5$；所以全闭区间上正半定且迹一。
对角 $1/5$ 给原人口，定理 C-108.3 给全菜单等价及原 $Q$ 等价。
平方谱求和给 (C108.11)。
给定 $p\in[1/5,9/25]$，取 $t=\sqrt{25(p-1/5)/4}\in[0,1]$ 即得纯度 $p$。
$t=1$ 时还可直接写正性证书

$$
C_1=\frac15\bigl(u_0u_0^\dagger+u_1u_1^\dagger+u_2u_2^\dagger\bigr),\qquad
u_0=|0\rangle-i|13\rangle,\quad
u_1=|1\rangle-i|3\rangle,\quad u_2=|2\rangle,
\tag{C108.12}
$$

这三个向量非零且互相正交，其范数平方为 $2,2,1$，所以秩三、迹一。
$t=0$ 是 $S$；任意 $t>0$ 由 C-108.4 给原分割的纠缠。证毕。

**定理 C-108.6（同一相关来源被实际十四旗端口精确擦除）。** 固定
《递归关系观察：达到的十四旗量子端口》（下称 QFA）定义 2.1 的实际数据：

$$
\begin{aligned}
F_{14}&=\{(\mathrm A,k,\ell):0\le k,\ell<3\}
       \sqcup\{(\mathrm B,k):0\le k<5\},\\
c_{\mathrm A,k,\ell}&=10/27,\qquad c_{\mathrm B,k}=1/3,\qquad
P_\nu=v_\nu v_\nu^T,\quad v_\nu\in\mathbb R^5,\quad \|v_\nu\|=1,\\
\sum_{\nu\in F_{14}}c_\nu P_\nu&=I_5,\qquad
R_\nu=DP_\nu D^\dagger,\quad E_\nu=c_\nu R_\nu,\\
\widetilde T(X)&=\sum_{\nu\in F_{14}}\operatorname{tr}(E_\nu X)R_\nu
=D\left[\sum_{\nu\in F_{14}}c_\nu P_\nu(D^\dagger XD)P_\nu\right]D^\dagger.
\end{aligned}
\tag{C108.13}
$$

$v_\nu$ 的三点、五点系数及两旋转平面取 QFA 式 (2.1)–(2.3) 的原值；
归一化等式正是其引理 2.2，$\widetilde T$ 是其定理 2.3 的同一个固定全块 CPTP 端口，
不是新优化的通道。
对每个满足 (C108.5) 的同一份相关 $\Gamma$，有

$$
\boxed{\quad(\widetilde T\otimes\widetilde T)(\Gamma)
              =(\widetilde T\otimes\widetilde T)(S).\quad}
\tag{C108.14}
$$

共同输出可分离，而且对实际全部 $14\times14$ 个旗对，其联合编码概率逐项相同：

$$
\begin{aligned}
p_{\nu\mu}
&=\operatorname{tr}((E_\nu\otimes E_\mu)\Gamma)
 =\frac{c_\nu c_\mu}{5}\sum_{s\in B}
                      v_\nu(s)^2v_\mu(f(s))^2\ge0,\\
(\widetilde T\otimes\widetilde T)(\Gamma)
&=\sum_{\nu,\mu\in F_{14}}p_{\nu\mu}R_\nu\otimes R_\mu
 =\frac15\sum_{s\in B}\widetilde T(\Pi_s)\otimes\widetilde T(\Pi_{f(s)}).
\end{aligned}
\tag{C108.15}
$$

证明。令 $r_s=v_\nu(s)v_\mu(f(s))\in\mathbb R$。
被动坐标中的来源系数为 $ZCZ=I_5/5+iZAZ$，而 $ZAZ$ 仍实反对称。
因而同一旗对的 Born 概率恰为

$$
c_\nu c_\mu\sum_{s,a}r_sr_a\eta_s\eta_a c_{sa}
=c_\nu c_\mu\left[\frac15\sum_s r_s^2
                  +i\sum_{s,a}r_sr_a\eta_s\eta_a A_{sa}\right]
=\frac{c_\nu c_\mu}{5}\sum_s r_s^2.
\tag{C108.16}
$$

末个双和中 $s=a$ 项为零，$(s,a)$ 与 $(a,s)$ 项相消。
这个计算对九个 A 旗和五个 B 旗的每一对成立，不更换它们的向量、权重或旗数。
由 (C108.13) 的归一化，

$$
\sum_{\nu,\mu}p_{\nu\mu}
=\frac15\sum_s
\left(\sum_\nu c_\nu v_\nu(s)^2\right)
\left(\sum_\mu c_\mu v_\mu(f(s))^2\right)=1.
\tag{C108.17}
$$

每个 $R_\nu$ 是归一化纯态，故 (C108.15) 是显式产品密度态凸分解，证明可分离。
把其中的和先按 $s$ 展开，给 (C108.15) 的最后一式；直接对 $S$ 作用局部通道也得同式，
于是 (C108.14) 成立。
对相关 $\Gamma$ 使用的始终是联合概率
$\operatorname{tr}((E_\nu\otimes E_\mu)\Gamma)$，没有把它换成边缘概率的乘积。
秩一 Kraus 的 measure-and-prepare 与纠缠破坏性质是
Horodecki–Shor–Ruskai，
[quant-ph/0302031](https://arxiv.org/html/quant-ph/0302031)，式 (1)–(2)、Theorem 4(A–D)
的已知对应；该一般性质本身不推出与 $S$ 的精确输出相等，后者由 (C108.16) 给出。证毕。

**推论 C-108.7（保持实际历史与认证原来源所需关系的分离）。** 在假设 C-108.1
及精确人口合同下，同一个全菜单等价类内同时存在唯一可分离态 $S$、
所有 $t\in(0,1]$ 的纠缠态 $\widehat\Gamma_t$，以及整态纯度区间
$[1/5,9/25]$ 的全部值。不存在仅以所有 $\mathcal M_{\rm loc}$ 完整历史律为输入的函数，
能在该类内正确返回原 $A\mid B$ 可分离性或整态纯度。
即使给出两个实际十四旗编码的完整联合旗律，仍没有这样的函数。

证明。C-108.3 与 C-108.5 使这些态的全菜单律相同，C-108.15 使它们的全部联合旗律相同；
而 $t=0$ 与任意 $t>0$ 的可分离性不同，$t$ 变化时纯度取遍上述非退化区间。
同一输入的函数只能给同一值，故不可能同时正确。证毕。

此推论比较的是同一原二体来源、指定实际局部操作和精确总体概率。
C-107.7 的整态交换纯度读数仍另外要求实际输入
$\Gamma_{AB}\otimes\Gamma_{A'B'}$ 及整份交换的谱仪器；
本菜单及局部端口没有给出这四个因子或源副本独立性。
(C108.14) 是该不可见纤维到一个通道纤维的包含，不刻画这个通道纤维的全部成员。
QFA 定理 5.1 的 $\alpha$ 是这一个单系统端口在原单系统历史 TV 目标下的达到误差；
这里没有把它变成相关双边输入的统一误差、diamond 距离、无约束 minimax 值，
也没有优化该纤维的 negativity。
C-108.3–C-108.7 是已述菜单张成、匹配来源和指定端口的联合应用推导，
不将实反对称谱配对、交换测纯度或一般纠缠破坏定理作为新内容。

## 109. 匹配来源、稀疏相干与实际有限等待的端口兼容性

本章把 C-106–C-108 的同一原 $A\mid B$ 来源，与单系统端口的一个额外人口合同连接。
精确实现某个固定通道的量子维数、任意复输入上的实际历史误差、承诺来源族的历史模拟，
是三个不同问题。相同全谱且具有全部相同实际历史的两个匹配态，其关联通道的精确端口
维数可以分别为二和三；另一方面，一次实际等待已经证明，达到既有误差上界的压缩端口
必须改变原匹配来源的某个联合人口。两种结论使用同一来源字典，但不互相替代。

**定义 C-109.1（固定来源、额外人口合同与三个资源坐标）。** 记
《递归关系观察：量子测量相对边界》为 QMB，
《量子端口协变与认证前沿》为 QPC，
《经典量子端口的精确证书》为 QEC。
单系统输入、未来菜单、$\mathfrak C_q$ 及 $e(T)$ 完全沿用
[QPC 定义 1.1–1.3](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_PORT_COVARIANCE_AND_CERTIFIED_FRONTIER.md)：
所有复 $\mathbb C^5$ 密度输入，非负等待 $U(t)=e^{-itK}$、完整秩一模式读数及 Stop，
所有有限自适应历史，一个事先固定的有限经典旗编码，以及每个整个 $M_q$ 块上的 CPTP
解码。无量子旁路、可读隐藏 Kraus 记录或外部参考测量。$e(T)$ 是该单系统的最坏完整
历史 TV，不是相关双边来源的误差或 diamond 距离。$1\le q\le5$。

原二体来源仍是 C-106 的 $B=(0,1,2,3,13)$、$f=(0\ 13)(1\ 3)$，$f(2)=2$，
$J e_s=|s,f(s)\rangle$，以及

$$
\mathfrak D=\{JCJ^\dagger:C\succeq0,\ C_{ss}=1/5\},\qquad
S=JI_5J^\dagger/5.
\tag{C109.1}
$$

系数坐标 $j=0,1,2,3,4$ 依次对应原标签 $(0,1,2,3,13)$ 和行走标签
$(N,2,3,5,25)$。令 $V e_j=|B_j\rangle_A$，$W e_j=|f(B_j)\rangle_B$；
$T_A$ 是由 $V$ 搬运到原 $A$ 因子的通道，$B$ 因子不动，也不进入端口。
这些是标签识别，不是新增可执行门。双边历史使用 C-108.1 的条件性实际局部菜单
$\mathcal M_{\rm loc}$，仍不要求 $A,B$ 独立。

定义额外合同

$$
\mathrm{BP}(T):\quad
\operatorname{tr}(\Pi_sT(\rho))=\operatorname{tr}(\Pi_s\rho)
\quad\text{对每个复密度态 }\rho\text{ 和每个原模式 }s.
\tag{C109.2}
$$

原竞争类 $\mathfrak C_q$ 没有这个合同。对一个固定通道定义
$q_{\rm exact}(T)=\min\{q:T\in\mathfrak C_q\}$，要求在所有复矩阵上精确实现同一个
$T$。对 $C\succeq0$ 定义 $k(C)$ 为有限分解 $C=\sum_a z_az_a^\dagger$ 中
$\max_a|\operatorname{supp}z_a|$ 的最小值；向量未必归一化，权重吸收入向量。
这里的基固定。$k(C)$ 是 coherence number，既不是 $\operatorname{rank}C$，也不是旗数。

**命题 C-109.2（人口合同的同源字典）。** 对任意 CPTP $T:M_5\to M_5$，下列条件等价：
$\mathrm{BP}(T)$；$T(\Pi_s)=\Pi_s$ 对所有 $s$ 成立；
$(T_A\otimes\mathrm{id})(S)\in\mathfrak D$；
$(T_A\otimes\mathrm{id})(\mathfrak D)\subseteq\mathfrak D$；
以及归一化、输出因子在前的 Choi 态

$$
\chi_T=\frac15\sum_{s,t}T(E_{st})\otimes E_{st},\qquad
\operatorname{Tr}_{\rm out}\chi_T=I_5/5
\tag{C109.3}
$$

满足 $(V\otimes W)\chi_T(V\otimes W)^\dagger\in\mathfrak D$。
此时存在唯一相关矩阵 $M\succeq0$、$M_{ss}=1$，使

$$
T(X)=M\circ X,\qquad
(V\otimes W)\chi_T(V\otimes W)^\dagger=J(M/5)J^\dagger,
\qquad C\longmapsto M\circ C.
\tag{C109.4}
$$

最后一式是 $(T_A\otimes\mathrm{id})(JCJ^\dagger)$ 的系数矩阵。

证明。复用 [C-29.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)
的基人口保持分类及其零平方和证明；这里把来源和量词对应写明。
BP 对输入 $\Pi_s$ 使输出对角集中在 $s$。正性给
$|X_{rt}|^2\le X_{rr}X_{tt}$，故 $T(\Pi_s)=\Pi_s$。
在任意有限 Kraus 族 $K_a$ 中，对 $r\ne s$ 有
$0=\sum_a|K_a(r,s)|^2$，每个 $K_a$ 因而对角。
写 $K_a=\operatorname{diag}z_a$ 得 $M=\sum_a z_az_a^\dagger$，
保迹给 $M_{ss}=1$。反向的 CPTP 性消费
[SecondOrder 定理 109.2](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md#109-联合记录的正性与最小环境秩)，
对角 Kraus 作用直接给 (C109.2) 与 (C109.4)。这不是另一个 Schur 分类。

对 $S$ 的实际联合人口逐项为

$$
\langle r,f(s)|(T_A\otimes\mathrm{id})(S)|r,f(s)\rangle
=\frac15\langle r|T(\Pi_s)|r\rangle.
\tag{C109.5}
$$

若输出属于 $\mathfrak D$，它们迫使各基投影固定。反向由 (C109.4) 的 Schur 乘积正性
及单位对角得到整个纤维保持。Choi 的同一人口也是 (C109.5)；其正性迫使支撑位于
$\operatorname{span}\{|s,s\rangle\}$，所以必为
$\frac15\sum_{s,t}M_{st}|s,s\rangle\langle t,t|$。
Choi 逆对应恢复 $T(E_{st})=M_{st}E_{st}$，且局部 $V,W$ 恰给 (C109.4)。
没有转置或遗漏 $1/5$。这些式子只是同一个通道的代数表示，不授予最大纠缠参考输入、
参考读数，或把一个未知给定的 $JCJ^\dagger$ 物理编程成 $T$ 的程序。证毕。

**定理 C-109.3（同一匹配矩阵的精确端口资源）。** 对 $\Gamma_C=JCJ^\dagger\in\mathfrak D$
设 $T_C(X)=(5C)\circ X$。则对每个 $q$，

$$
T_C\in\mathfrak C_q\quad\Longleftrightarrow\quad
C=\sum_a z_az_a^\dagger,\quad |\operatorname{supp}z_a|\le q
\quad\Longleftrightarrow\quad
\operatorname{SN}_{A\mid B}(\Gamma_C)\le q.
\tag{C109.6}
$$

其中分解均有限，Schmidt number 在原 $A\mid B$ 切口上取值。因此
$q_{\rm exact}(T_C)=k(C)=\operatorname{SN}_{A\mid B}(\Gamma_C)$。

证明。QMB 定理 5.1 的有限块端口等价于存在同一通道的有限秩至多 $q$ Kraus 族。
具体地，编码分支 Kraus $B_{fa}:\mathbb C^5\to\mathbb C^q$ 和整个块的解码 Kraus
$R_{fb}:\mathbb C^q\to\mathbb C^5$ 给 $K_{fab}=R_{fb}B_{fa}$，其秩至多 $q$，
解码保迹给总族完备。C-109.2 的零平方和论证作用于这个族本身，故这些 $K_{fab}$
全部对角；没有混合 Kraus 后再假定秩不变。
对角矩阵的秩就是非零对角数，得 $M=5C$ 的 $q$ 稀疏 Gram 分解。

反向若 $M=\sum_a z_az_a^\dagger$ 且每个支撑大小至多 $q$，取
$K_a=\operatorname{diag}z_a$。为每个 $a$ 选择固定坐标等距嵌入
$V_a:\mathbb C^q\to\mathbb C^5$，其像包含 $\operatorname{ran}K_a$；
不足 $q$ 个坐标时补齐，零向量分支可省略。定义

$$
B_a=V_a^\dagger K_a,\quad
\operatorname{Enc}(X)=(B_aXB_a^\dagger)_a,\quad
\operatorname{Dec}_a(Y)=V_aYV_a^\dagger.
\tag{C109.7}
$$

$V_a^\dagger V_a=I_q$ 使解码在整个 $M_q$ 上保迹；而
$V_aV_a^\dagger K_a=K_a$ 给
$\sum_aB_a^\dagger B_a=\sum_aK_a^\dagger K_a=I_5$。
每个矩形夹乘在任意参考放大下为正，故编码和解码 CPTP。
复合在所有复矩阵上等于 $T_C$，全部量子路径通过其 $q$ 块，没有旁路。

对任一 $\Gamma_C=\sum_a|\psi_a\rangle\langle\psi_a|$ 的正纯态分解，
向 $\operatorname{ran}J$ 的正交补投影给
$\sum_a\|(I-JJ^\dagger)\psi_a\|^2=0$，故每个 $\psi_a=Jz_a$。
矩阵系数是 $\operatorname{diag}z_a$ 乘一个置换；$Jz_a$ 的 Schmidt 秩恰等于
$|\operatorname{supp}z_a|$。逆向也逐项成立，证明 (C109.6)。
这对应于标准 coherence-number/Schmidt-number 关系以及 QMB 的 Kraus 秩合同，
不是独立来源副本之间的切口。证毕。

**定理 C-109.4（一个不可见纤维中的等谱边与三角形）。** 使用系数坐标的矩阵单位，令

$$
\begin{gathered}
L=E_{04}-E_{40},\qquad
R=E_{01}-E_{10}+E_{12}-E_{21}+E_{20}-E_{02},\\
0\le a\le1/\sqrt3,\quad b=\sqrt3\,a,\\
M_{\rm pair}(a)=I_5+ibL,\qquad M_{\rm tri}(a)=I_5+iaR,\\
C_x(a)=M_x(a)/5,\quad \Gamma_x(a)=JC_x(a)J^\dagger,\quad
T_x(a)(X)=M_x(a)\circ X.
\end{gathered}
\tag{C109.8}
$$

两者均为合法相关矩阵，$C_x$ 的共同全谱为

$$
\left\{\frac{1+b}{5},\frac{1-b}{5},\frac15,\frac15,\frac15\right\},
\qquad \operatorname{tr}(\Gamma_x^2)=\frac{5+6a^2}{25}.
\tag{C109.9}
$$

$\Gamma_x$ 的谱再添二十个零。对每个 $\pi\in\mathcal M_{\rm loc}$，
$P_{\Gamma_{\rm pair}(a)}^\pi=P_{\Gamma_{\rm tri}(a)}^\pi=P_S^\pi$；
它们也属于原 $Q$ 纤维 $\mathfrak F$。$a>0$ 时两者在原切口上都纠缠。

证明。边块 $iL$ 的本征值是 $1,-1$。三角块满足
$R^2=\mathbf1\mathbf1^T-3I_3$、$R\mathbf1=0$，所以 $iR$ 的本征值为
$0,\sqrt3,-\sqrt3$。其余两个坐标固定；这给 (C109.9) 和全参数区间的正性。
也可用以下共同可核的谱分解明确给出三角上界：在前三坐标中令

$$
u=(1,1,1)/\sqrt3,\quad p=(1,-1,0)/\sqrt2,\quad
z=(1,1,-2)/\sqrt6,\quad h_\pm=(p\mp iz)/\sqrt2.
$$

$Rp=-\sqrt3z$、$Rz=\sqrt3p$，$u,h_+,h_-$ 为复正交单位向量，故

$$
M_{\rm tri}=uu^\dagger+(1+b)h_+h_+^\dagger
 +(1-b)h_-h_-^\dagger+E_{33}+E_{44}.
\tag{C109.10}
$$

边块类似地用 $g_\pm=(e_0\mp ie_4)/\sqrt2$：
$M_{\rm pair}=(1+b)g_+g_+^\dagger+(1-b)g_-g_-^\dagger+
E_{11}+E_{22}+E_{33}$。
这些有限 Gram 因子也给通道合法性，$b=1$ 时零权重项直接省略。
谱平方和为 $(5+2b^2)/25$。两者实部都为 $I_5/5$，故
C-108.3 给全部有限自适应双边历史及原 $Q$ 约束，而非仅单读边缘等价。
非零虚部使 $\Gamma_x\ne S$，C-106.2 给原切口纠缠。证毕。

**定理 C-109.5（全区间的锐端口阈值）。** (C109.8) 的精确通道资源及原切口
Schmidt number 均满足

$$
\begin{array}{c|ccc}
&a=0&0<a\le1/2&1/2<a\le1/\sqrt3\\ \hline
q_{\rm exact}(T_{\rm pair})&1&2&2\\
q_{\rm exact}(T_{\rm tri})&1&2&3
\end{array}.
\tag{C109.11}
$$

证明。$a=0$ 时 $M=I_5$，五个单坐标 Kraus 给标量完全去相干通道。
$a>0$ 的非零非对角元排除任何单坐标 Gram 分解，因此资源至少二。
边的 (C109.10) 后的分解最多五旗、各支撑至多二，给二的上界。
三角的 (C109.10) 最多五旗、各支撑至多三，给全区间三的上界。
在 $0\le a\le1/2$，还存在精确的二稀疏分解

$$
M_{\rm tri}=(1-2a)(E_{00}+E_{11}+E_{22})
 +a\sum_{(j,k)\in\{(0,1),(1,2),(2,0)\}}
 (e_j-ie_k)(e_j-ie_k)^\dagger+E_{33}+E_{44}.
\tag{C109.12}
$$

所有权重非负，$a=1/2$ 的前三个单坐标项为零，不影响二维构造。
每个上界都通过 (C109.7) 给一组事先固定、整个块 CPTP 的真正编码和解码，
不只是准备一个输出态。

要排除 $a>1/2$ 的任意二稀疏分解，令 $I=\{0,1,2\}$。
任何支撑至多二的复向量 $v$ 都满足

$$
2\sum_{j<k,\ j,k\in I}|v_j\overline v_k|
\le\sum_{j\in I}|v_j|^2.
$$

至多一个无序对非零，故这就是 $2|xy|\le|x|^2+|y|^2$。
对任何有限分解求和并用三角不等式，必有
$2\sum_{j<k\in I}|M_{jk}|\le\operatorname{tr}M[I,I]=3$。
三角矩阵左侧是 $6a$，当 $a>1/2$ 严格矛盾。这个论证覆盖所有复向量和所有有限旗数。
等价的对偶证书是 $H=(I_3-iR|_I)\oplus0_2$：其每个至多二坐标主压缩都正半定，
但 $\operatorname{tr}(H C_{\rm tri})=(3-6a)/5<0$。
这是稀疏分解的代数证书，没有把 $H$ 当作新增实际菜单效果。
C-109.3 完成两种资源的转移。证毕。

**推论 C-109.6（全谱和环境秩仍不能决定精确端口）。** 取 $a=5/9$，则

$$
\begin{gathered}
C_{\rm pair}=I_5/5+(i\sqrt3/9)(E_{04}-E_{40}),\qquad
C_{\rm tri}=I_5/5+(i/9)R,\\
\operatorname{spec}C_x={1/5+\sqrt3/9,1/5-\sqrt3/9,1/5,1/5,1/5\},\\
\operatorname{tr}\Gamma_x^2=37/135,\qquad \operatorname{rank}M_x=5,
\qquad M_x\prec2I_5.
\end{gathered}
\tag{C109.13}
$$

两者具有完全相同的所有实际双边历史律、全部特征值及纯度，而精确端口分别为二和三。
SecondOrder 定理 109.2 的纯初始环境受控记录实现，最小环境维数均为五。
所以这些共同数据不能决定 $q_{\rm exact}$；即使 $M\preceq2I$ 也不足以刻画二维端口。

证明。$1/25-1/27>0$ 给五个特征值严格正，$25/27<1$ 给
$5\sqrt3/9<1$。C-109.4–C-109.5 给其余断言。
二稀疏的三角角落条件在 $C_{\rm tri}$ 上成为 $1/3\le3/10$，相差 $1/30$；
上述 $H$ 的迹为 $-1/15$。同一数据的函数只能返回同一值，不能同时正确返回二与三。
这里的全谱是所给矩阵的数学属性，没有声称菜单能实验测定它。
在另一个端点 $a=1/\sqrt3$，共同谱为 $\{2/5,1/5,1/5,1/5,0\}$，
纯度 $7/25$、环境秩四，(C109.11) 的二与三分叉仍成立。证毕。

**引理 C-109.7（一次实际有理等待的严格碰撞证书）。** 沿用 QPC 的被动坐标
$D=\operatorname{diag}(1,i,i,i,1)$，则实际生成元和等待为

$$
A=-iD^\dagger KD=
\begin{pmatrix}
0&1&1&1&0\\-1&0&0&0&-1\\-1&0&0&0&0\\-1&0&0&0&-1\\0&1&0&1&0
\end{pmatrix},\qquad O(t)=e^{tA}.
\tag{C109.14}
$$

设 $t_0=2/3$，$v=O(t_0)^Te_N$，$p_s=|v_s|^2$。则

$$
\sum_sp_s^2<53/250.
\tag{C109.15}
$$

证明。$A^T=-A$，故 $v=e^{-2A/3}e_N$ 为实单位向量。
$A$ 的最大绝对行和与列和均为三，由加权 Cauchy–Schwarz，
$\|Ax\|_2^2\le\sum_i(\sum_j|A_{ij}|)\sum_j|A_{ij}||x_j|^2
\le9\|x\|_2^2$，因此欧氏算子范数至多三，
$\|(-2/3)A\|_{\rm op}\le2$。指数级数在该有限维范数中绝对收敛。
取 $w=\sum_{k=0}^{12}(-2A/3)^ke_N/k!$；尾项比从 $k=13$ 起至多 $1/7$，从而

$$
\|v-w\|_2\le\sum_{k\ge13}\frac{2^k}{k!}
\le\frac76\frac{2^{13}}{13!}=\frac4{2606175}.
\tag{C109.16}
$$

具体有理列不是独立轨道角的替代，直接按 $c_0=e_N$、
$c_{k+1}=-2Ac_k/[3(k+1)]$ 求到 $k=12$ 得

$$
w=\left(
\frac{107738440637}{248594813775},
\frac{490347766}{1104865839},
\frac{4899328858}{9207215325},
\frac{490347766}{1104865839},
-\frac{91371050044}{248594813775}
\right)^T.
\tag{C109.17}
$$

每个坐标误差至多 (C109.16)。有理外包区间如下，所有端点除以 $100000$：

$$
\begin{array}{c|rrrrr}
s&N&2&3&5&25\\ \hline
\text{下端}&43338&44380&53211&44380&-36756\\
\text{上端}&43340&44381&53212&44381&-36754
\end{array}.
\tag{C109.18}
$$

其合法性可逐坐标直接检验
$\ell_s<w_s-4/2606175\le v_s\le w_s+4/2606175<u_s$。
例如第三坐标上端仍留有正余量 $5581607/119693799225000$。
因此用绝对值较大的端点四次方求和，得

$$
\sum_s|v_s|^4
\le\frac{43340^4+2\cdot44381^4+53212^4+36756^4}{100000^4}
=\frac{10565071620411213137}{50000000000000000000}
<\frac{53}{250}.
\tag{C109.19}
$$

最后严格差为 $34928379588786863/50000000000000000000$。
指数尾界把有理截断与实际有限等待相连，不能仅由最后这个有理比较推出结论。
本证书没有使用轨道闭包中的独立角、极限时间或负的物理等待。证毕。

**定理 C-109.8（实际菜单误差迫使匹配人口改变）。** 对每个 $q=1,2,3,4$，
每个原 $T\in\mathfrak C_q$ 若满足额外 BP 合同，则

$$
e(T)>1-53q/250>u_q:=(5-q)/7.
\tag{C109.20}
$$

同一个输入 $\rho_0=Dvv^TD^\dagger$、同一个实际等待 $t_0=2/3$、完整模式读数后 Stop，
已经统一见证所有这些通道和所有这四个 $q$ 的第一个严格界。
故任意原 $T\in\mathfrak C_q$ 若 $e(T)\le u_q$，则
$(T_A\otimes\mathrm{id})(S)$ 至少一个非匹配联合人口严格为正。
特别地，所有达到的原 minimizer 都改变这个匹配人口合同。

证明。在 C-109.3 提供的同一个秩受限对角 Kraus 族写
$M=\sum_a z_az_a^\dagger$、$|\operatorname{supp}z_a|\le q$、
$\sum_a|z_a(s)|^2=1$。稀疏 Cauchy–Schwarz 给对任意复 $x$

$$
x^\dagger Mx=\sum_a|z_a^\dagger x|^2
\le\sum_a q\sum_s|z_a(s)|^2|x_s|^2=q\|x\|_2^2,
\qquad M\preceq qI_5.
\tag{C109.21}
$$

这是必要方向，C-109.6 已排除逆向。被动对角 $D$ 不改变 BP 或 Schur 矩阵：
$D^\dagger T(DXD^\dagger)D=M\circ X$；此为坐标恒等式，不增加未来相位控制。
允许制备任意复输入使 $\rho_0$ 合法。$U(t_0)D v=D O(t_0)v=De_N=e_N$，
所以未经替换的完整读数以概率一给 $N$。替换后的同一事件概率为

$$
F_T=\langle v|\widehat T(vv^T)|v\rangle
=\sum_{s,t}p_sM_{st}p_t=p^TMp
\le q\sum_sp_s^2<53q/250.
\tag{C109.22}
$$

这是真实 Born 概率；因理想律为点质量，整个五结果读数的 TV 恰为 $1-F_T$。
保留这一读数和 Stop 的历史即给 $e(T)\ge1-F_T$。
没有用任意参考效果、diamond 范数或把两来源的边缘概率相乘。
输入向量的定义使用 $O(t_0)^T$ 不表示实施反向等待；未来协议只等待 $2/3$。

数值比较均为严格有理关系：

$$
\begin{array}{c|c|c}
q&1-53q/250&u_q\\ \hline
1&197/250&4/7\\2&72/125&3/7\\3&91/250&2/7\\4&19/125&1/7
\end{array},\qquad
1-53q/250-u_q=(500-121q)/1750>0.
\tag{C109.23}
$$

若 $e(T)\le u_q$，逆否命题给非 BP。C-109.2 说明必有一个 $T(\Pi_s)\ne\Pi_s$。
正性和迹一于是使某个 $r\ne s$ 的 $\langle r|T(\Pi_s)|r\rangle>0$；
(C109.5) 在同一 $S$ 上给所述非匹配人口。QMB 定理 5.1 的紧性、达到性与显式
$u_q$ 端口给每个原 minimizer 的误差至多 $u_q$，所以也在此结论内。
这里没有算出任意 $q<5$ 的无约束最优值。证毕。

**推论 C-109.9（当前标量端口比较与平稳性边界）。** QEC 定理 3.2、4.4、5.1
给同一全复输入、同一原菜单上的一个固定十四旗标量端口 $T_\xi$，其
$e(T_\xi)=\xi<529/1000$。故对 BP 的 $q=1,2$ 端口，

$$
e(T)>72/125>529/1000>\xi.
\tag{C109.24}
$$

因此 BP 与 $e(T)\le\xi$ 同时成立必需 $q\ge3$；不声称三维充分。
对于本实际连通行走，BP 且 walk-stationary 的 CPTP 通道只能是恒等通道。
特别是 $\mathfrak C_q$、BP、walk-stationary 三者交集在 $q<5$ 时为空；
QPC/QRC 的无约束平稳化不能作为 BP 子问题内的约化。

证明。前半由 (C109.23) 与 QEC 的当前 $\xi$ 证书直接比较。
若 Schur 通道 $T_M$ 与所有实际行走共轭交换，对 $\Pi_j$ 在 $t=0$ 求导得
$T_M([K,\Pi_j])=[K,\Pi_j]$。在每个 $K_{ij}\ne0$ 的边上必须有 $M_{ij}=1$。
实际边是 $N$–$2$、$N$–$3$、$N$–$5$、$2$–$25$、$5$–$25$，图连通。
相关矩阵是单位记录的 Gram 矩阵，单位重叠等于一强制记录相同；沿边传播使全部记录
相同，$M=\mathbf1\mathbf1^\dagger$，故 $T=\mathrm{id}$。
这一步复用 C-29.3 的记录刚性，也可直接消费 SecondOrder 定理 79.2 的实际实效果
保持刚性。恒等的 Choi 态为 Schmidt 秩五的纯态，故其精确端口为五。

QPC 定理 3.3 的设计共轭保持 $\mathfrak C_q$ 和原误差，却旋转 BP 所固定的基；
它未声称保持 BP。若 $q<5$ 的 BP 输入端口平稳平均后仍 BP，就与上面的空交集矛盾。
QRC 定理 3.2 的无约束实/平稳/反射代表及其十二坐标继续在各自原域上使用。
$T_\xi$ 的平稳性与标量合法性也迫使它不是 BP；没有把 QFA 的矩阵元代入该通道。证毕。

**命题 C-109.10（当前 QEC 编码在同一不可见来源上的精确擦除）。** 使用 QEC
定义 3.1 和式 (3.2)–(3.3) 自己的十四旗设计。其真实向量是

$$
\begin{aligned}
v_{\mathrm A,k,l}&=\sqrt{3/7}\,w_+(2\pi k/3)
                 +\sqrt{4/7}\,w_-(2\pi l/3),&c_{\mathrm A,k,l}&=7/18,\\
v_{\mathrm B,k}&=\sqrt{2/3}\,d+\sqrt{1/3}\,w_+(2\pi k/5),
&c_{\mathrm B,k}&=3/10,
\end{aligned}
$$

其中 $w_\pm,d$ 是 QEC 定义 1.3 的同一实际谱平面向量。
记 $P_f=v_fv_f^T$、$E_f=c_fDP_fD^\dagger$、
$\sigma_f=Dv_fv_f^TD^\dagger$。对所有 C-108 不可见态，包括 (C109.8) 的两族，

$$
\begin{aligned}
\operatorname{tr}((E_f\otimes E_g)\Gamma)
 &=\operatorname{tr}((E_f\otimes E_g)S),\\
(T_\xi\otimes T_\xi)(\Gamma)
 &=\sum_{f,g}\operatorname{tr}((E_f\otimes E_g)S)\,
      \sigma_f\otimes\sigma_g
 =(T_\xi\otimes T_\xi)(S).
\end{aligned}
\tag{C109.25}
$$

证明。每个 $v_f$ 为实单位向量，真实编码效果就是 $E_f$，解码输出就是
$\sigma_f$。C-108.4 的匹配压缩使
$J^\dagger(E_f\otimes E_g)J$ 为实对称矩阵，其与 $C-I_5/5$ 的迹配对为零。
这给联合旗律相等，继而对同一相关来源用联合权重给第二式；权重非负、总和为一。
这是可分离输出的显式产品凸分解。它使用 QEC 的 $3/7,4/7,2/3,1/3$，
不以 QFA 的旧权重替代。旗律是编码的数学读数，不另外暴露为未来菜单。证毕。

甚至局部标量完全去相干 $\Delta_A(X)=\sum_s\Pi_sX\Pi_s$ 已将每个
$JCJ^\dagger\in\mathfrak D$ 送到 $S$，并保持匹配人口。
对 (C109.8) 的承诺族，C-108.3 使这个标量方案精确保持全部实际双边历史。
因此 (C109.11) 的三维是实现所指定关联通道在所有输入上作用的资源，
绝非仅模拟这些来源历史所需的下界；(C109.20) 的误差则是一个通道对所有允许
单系统输入同时承担的目标。环境维数、Kraus/旗数和 $q$ 不能混为一个数字。

**注记 C-109.11（文献对应、证据层级与未决边界）。**
Schur/GI 分类消费 C-29.2 与 SecondOrder 109.2；其一般文献是
de Vicente–Streltsov，[*The power of the resource theory of genuine quantum coherence*,
Theorem 1](https://arxiv.org/html/1604.08031v2)。
coherence number 的有限稀疏纯态定义及二层比较矩阵判据见
Ringbauer 等，[*Certification and Quantification of Multilevel Quantum Coherence*,
§I.1、Theorem 1](https://arxiv.org/html/1707.05282v3)；本章的角落不等式与对偶 $H$
是该成熟框架在这一个复三角矩阵上的显式证书。
Choi/Schmidt/Kraus 秩对应见 Chruściński–Kossakowski，
[*On partially entanglement breaking channels*, Theorem 1 证明](https://arxiv.org/html/quant-ph/0511244v1)；
其输入因子在前的约定在 (C109.3) 明确交换为输出在前。
固定有限经典旁信息和整个块压缩合同见 Bluhm–Rauber–Wolf，
[*Quantum compression relative to a set of measurements*, Definition 4.1、Lemmas 5.2–5.3](https://arxiv.org/html/1708.04898v4)。
文献的精确观测保持目标不直接等于这里的实际历史 TV。

仓内新增的综合应用是上述原匹配来源与固定通道的完整资源字典、同实际观察纤维同全谱的
锐二/三维分叉，以及一次实际有限等待对所有四种压缩维数给出的匹配人口不兼容性。
不主张一般 Schur、coherence 或 Schmidt-number 理论的原创性。
规范有限 CP/Kraus、Choi、记录边缘和 Born 分支供应分别是
`FiniteKrausRepresentation.krausRepresentation`、
`PhyslibLeaf.MatrixMap.choi_of_kraus`、`finite_kraus_quantum_channel`、
`EnvironmentMarginalChannel.environment_marginal_channel` 和
`finite_kraus_instrument_born_marginal`；这些供应不包含本章完整端口/来源/实际等待定理。
本章给普通数学推导，不将其声明为端到端 Lean 形式化。
完整形式桥仍须把整个块端口、同族秩和对角性、匹配纯态分解、矩阵指数的解析尾界、
实际 Born/TV 协议以及 QEC 的具体设计在一个精确类型合同中连接。
有理矩阵和常数的精确核对不能单独替代这些义务。

仍未解决整个不可见纤维的最大 coherence number、BP 限制下最优误差、任何 $q<5$ 的
无约束 $\varepsilon_q$ 精确值、三维在 $\xi$ 的充分性或一般非零人口泄漏的定量界。
原 QEC 区间 $5197/10000\le\varepsilon_1\le\xi$ 保持其原含义。
这里没有原生树到任意复态的制备映射、额外相位控制、源副本、交换测量或参考接入；
数学标签映射和相同全谱都不供应这些操作。

## 追加锚（本行以下为增补区）

## 110. 无附加人口合同的有限端口误差与同源人口泄漏

**定义 C-110.1（整个块端口的泄漏与纯态存活率）。** 设 $d\ge1$、$1\le q\le d$，
固定 $\mathbb C^d$ 的模式基。$\mathfrak C_q^{(d)}$ 是经过有限经典旗与整个 $M_q$ 块的
CPTP 编码、解码所实现的通道类；当 $d=5$ 时就是 C-109.1 的原 $\mathfrak C_q$。
编码分支的 Kraus 算子记为 $B_{fa}:\mathbb C^d\to\mathbb C^q$，解码分支的算子记为
$R_{fb}:\mathbb C^q\to\mathbb C^d$，满足

$$
\sum_{f,a}B_{fa}^\dagger B_{fa}=I_d,\qquad
\sum_bR_{fb}^\dagger R_{fb}=I_q\quad\text{对每个 }f.
\tag{C110.1}
$$

所有数据允许为复数，经典旗有限且事先固定，解码在整个块上保迹。
输入到输出的全部量子路径通过这个 $q$ 维块。对任意 CPTP $T:M_d\to M_d$ 定义

$$
\begin{aligned}
m_{rs}(T)&=\langle r|T(\Pi_s)|r\rangle,\qquad \Pi_s=|s\rangle\langle s|,\\
\ell(T)&=\frac1d\sum_s\sum_{r\ne s}m_{rs}(T),\\
F_v(T)&=\langle v|T(|v\rangle\langle v|)|v\rangle,\qquad
p_s=|v_s|^2,\qquad c(v)=\sum_sp_s^2\quad(\|v\|_2=1).
\end{aligned}
\tag{C110.2}
$$

$\ell$ 使用固定原模式基，不要求该基在任意酉变换下保持。$F_v$ 是数学上的同态
纯态存活率；只有把它对应到一个允许的输入和未来读数之后，才成为实际菜单的误差见证。

**定理 C-110.2（任意复端口的存活率—泄漏界）。** 对每个 $T\in\mathfrak C_q^{(d)}$
和每个复单位向量 $v$，有 $1/d\le c(v)\le1$、$0\le\ell(T)\le1$，以及

$$
\boxed{\quad
\sqrt{F_v(T)}\le\sqrt{q\,c(v)}+
\sqrt{d(1-c(v))\,\ell(T)}.\quad}
\tag{C110.3}
$$

$\ell(T)$ 由通道决定，与选用的 Kraus 族无关。该界不要求 BP、保单位性、协变性、
实 Kraus 数据或后选择。

证明。沿用 QMB 定理 5.1 的整个块端口到低秩 Kraus 族的方向，直接在给定编码和解码
上取 $K_{fab}=R_{fb}B_{fa}$。由 (C110.1)，

$$
T(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger,\qquad
\operatorname{rank}K_\alpha\le q,\qquad
\sum_\alpha K_\alpha^\dagger K_\alpha=I_d.
\tag{C110.4}
$$

这是同一个通道的一组实际有限分解；不在任意 Kraus 混合后假设各项仍低秩。
这个成熟对应见 Chruściński–Kossakowski，
[*On partially entanglement breaking channels*, Theorem 1 的证明](https://arxiv.org/html/quant-ph/0511244v1)，
以及 Bluhm–Rauber–Wolf，
[*Quantum compression relative to a set of measurements*, Definition 4.1、Lemma 5.2 的证明](https://arxiv.org/html/1708.04898v4)。
后者的精确观测保持目标和这里的实际历史 TV 仍是不同合同。

正性、保迹给 $m_{rs}\ge0$、$\sum_rm_{rs}=1$，而

$$
m_{rs}=\sum_\alpha|K_\alpha(r,s)|^2,\qquad
\sum_{\alpha,r\ne s}|K_\alpha(r,s)|^2=d\ell(T).
\tag{C110.5}
$$

第一式的左端不含 Kraus 选择，因而第二式在任意其他表示下仍是同一数值。
特别是 $0\le\ell\le1$；$p_s\ge0$、$\sum_sp_s=1$ 和 Cauchy–Schwarz 给
$1/d\le c\le1$。

令 $P=\operatorname{diag}(p_s)$，按有限 Kraus 指标定义复向量

$$
a_\alpha=\operatorname{tr}(K_\alpha P)=\sum_sp_sK_\alpha(s,s),\qquad
b_\alpha=\sum_{r\ne s}\overline{v_r}K_\alpha(r,s)v_s.
\tag{C110.6}
$$

于是 $F_v(T)=\sum_\alpha|a_\alpha+b_\alpha|^2$。
消费 QPC 引理 8.1 使用的成熟复矩阵秩—迹估计
$|\operatorname{tr}X|^2\le\operatorname{rank}(X)\|X\|_{\rm HS}^2$，
取 $X=K_\alpha P$，其秩至多 $q$，得到

$$
\begin{aligned}
\|a\|_2^2
&\le q\sum_\alpha\|K_\alpha P\|_{\rm HS}^2\\
&=q\sum_sp_s^2\sum_{\alpha,r}|K_\alpha(r,s)|^2
=q\sum_sp_s^2=qc.
\end{aligned}
\tag{C110.7}
$$

这里用的是右乘 $P$ 后的列范数与保迹等式；未使用行范数归一化或 $T(I)=I$。
上述秩—迹估计对任意复矩阵成立：奇异值分解先界
$|\operatorname{tr}X|\le\sum_{j=1}^{\operatorname{rank}X}\sigma_j$，再用
Cauchy–Schwarz；它不要求 $X$ 为正或 Hermitian。

对 (C110.6) 的非对角和用复 Cauchy–Schwarz，得

$$
\begin{aligned}
|b_\alpha|^2
&\le\left(\sum_{r\ne s}|v_r|^2|v_s|^2\right)
      \sum_{r\ne s}|K_\alpha(r,s)|^2\\
&=(1-c)\sum_{r\ne s}|K_\alpha(r,s)|^2,\\
\|b\|_2^2&\le d(1-c)\ell(T).
\end{aligned}
\tag{C110.8}
$$

在同一有限指标空间用三角不等式
$\sqrt{F_v(T)}=\|a+b\|_2\le\|a\|_2+\|b\|_2$，即得 (C110.3)。
这里的新关系是把这些成熟矩阵工具用于固定模式基下的通道泄漏；没有把一般 CP、
Kraus 秩或矩阵范数工具当作新结论。证毕。

**定理 C-110.3（每个原匹配来源的精确人口 TV）。** 保留 C-109.1 的原
$A\mid B$、$B=(0,1,2,3,13)$、$f=(0\ 13)(1\ 3)$、$f(2)=2$、$J$、$V$ 和 $W$。
对任意 $C\succeq0$、$C_{ss}=1/5$，令
$\Gamma_C=JCJ^\dagger$、$\Gamma'_C=(T_A\otimes\mathrm{id})(\Gamma_C)$。
只在原 $A$ 因子作用同一 $T$，$B$ 不进入端口；$m_{rs}$ 的索引按 $V$ 与原模式对应。
则对所有模式 $r,s$，

$$
\begin{aligned}
\langle r,f(s)|\Gamma'_C|r,f(s)\rangle&=m_{rs}(T)/5,\\
\langle r,f(s)|\Gamma_C|r,f(s)\rangle&=\delta_{rs}/5,\\
\operatorname{TV}(P_{\Gamma'_C}^{\rm pop},P_{\Gamma_C}^{\rm pop})
&=\ell(T)=P_{\Gamma'_C}^{\rm pop}\{(r,f(s)):r\ne s\}.
\end{aligned}
\tag{C110.9}
$$

$P^{\rm pop}$ 是两边立即完整局部模式读数的联合律。因此在 C-108.1 的条件性
局部完整历史接口下，原来源与变换后来源的最坏历史 TV 至少为 $\ell(T)$。
这些式子对整个 $\mathfrak D$ 一致成立，因而也覆盖 C-108.3 的每个不可见成员。

证明。将同一份来源展开为
$\Gamma_C=\sum_{j,k}C_{jk}|j\rangle\langle k|\otimes|f(j)\rangle\langle f(k)|$。
在第二因子用 $|f(s)\rangle$ 夹取时，由 $f$ 单射只剩 $j=k=s$，故第一式是
$C_{ss}\langle r|T(\Pi_s)|r\rangle=m_{rs}/5$。这不将 $C$ 的联合权重拆为边缘之积。
原律只支撑 $r=s$，且 $0\le m_{ss}\le1$，所以

$$
\operatorname{TV}
=\frac1{10}\left(\sum_s(1-m_{ss})+\sum_s\sum_{r\ne s}m_{rs}\right)
=\frac15\sum_s\sum_{r\ne s}m_{rs}=\ell(T).
\tag{C110.10}
$$

立即读数使用允许的零等待，然后两边 Stop；未匹配事件只是完整记录的经典分组。
故它是 C-108.1 中一个真实有限策略，其 TV 给全部策略上确界的下界。
原标签与行走标签按 (C108.1) 的位置对应，$T_A$ 由 $V$ 搬运；$f$ 是来源配对标签，
不表示在 $B$ 上另加可执行门。没有独立副本、参考寄存器或参考测量。证毕。

**定理 C-110.4（原单系统实际菜单的误差—泄漏曲线）。** 令
$v=O(2/3)^Te_N$、$c_0=\sum_s|v_s|^4$，其中 $O$ 与被动坐标
$D=\operatorname{diag}(1,i,i,i,1)$ 都取自 C-109.7。
对每个 $q=1,2,3,4$ 和原 $T\in\mathfrak C_q$，其所有复单系统输入上的实际完整历史误差满足

$$
\begin{aligned}
e(T)&\ge1-\left(\sqrt{qc_0}+\sqrt{5(1-c_0)\ell(T)}\right)^2,\\
e(T)&>1-\left(\sqrt{53q/250}+2\sqrt{\ell(T)}\right)^2.
\end{aligned}
\tag{C110.11}
$$

若 $e(T)<1-qc_0$，还可反解第一式为

$$
\ell(T)\ge
\frac{\left(\sqrt{1-e(T)}-\sqrt{qc_0}\right)^2}{5(1-c_0)}.
\tag{C110.12}
$$

上述误差下界的右端为负时仅为无效的负下界，不断言误差严格为正。

证明。C-109.7 的实际矩阵指数及解析尾界给
$1/5\le c_0<53/250<1$，而非只给一列有理近似。
在被动坐标中取 $\widehat T(X)=D^\dagger T(DXD^\dagger)D$。
该式只改变表示；对同一 Kraus 族作 $K_\alpha\mapsto D^\dagger K_\alpha D$
保持秩和完备性，且逐项保持 $m_{rs}$，故
$\widehat T\in\mathfrak C_q$、$\ell(\widehat T)=\ell(T)$。
这里无需把 $D$ 或 $D^\dagger$ 加入未来菜单。

任意复输入的量词允许制备 $\rho_0=Dvv^\dagger D^\dagger$。
C-109.7–C-109.8 已给同一实际正等待 $t_0=2/3$ 后
$U(t_0)Dv=e_N$，所以理想完整模式律是 $N$ 处点质量。
对替换通道使用完全相同的等待、完整读数和 Stop，$N$ 的概率恰为
$F_v(\widehat T)$，该历史律的 TV 恰为 $1-F_v(\widehat T)$。
因此 $e(T)\ge1-F_v(\widehat T)$。把 C-110.2 用于 $\widehat T$ 即得第一式。

由 $c_0\ge1/5$ 得 $\sqrt{5(1-c_0)\ell}\le2\sqrt\ell$，而
$q>0$、$c_0<53/250$ 给 $\sqrt{qc_0}<\sqrt{53q/250}$。
两项之和非负，且后一上界严格为正，故平方保持严格比较，得到第二式。
若 $e(T)<1-qc_0$，则 $\sqrt{1-e(T)}-\sqrt{qc_0}>0$；
由存活率界移项、平方并除以 $5(1-c_0)>0$ 即得 (C110.12)。
这条链使用原实际菜单的一个事件，没有把 $e(T)$ 换成 diamond 范数或双边来源误差。证毕。

**推论 C-110.5（达到基准时四个严格正的同源 TV 下界）。** 对每个
$q\in\{1,2,3,4\}$，设原 $T\in\mathfrak C_q$ 满足
$e(T)\le u_q=(5-q)/7$。令

$$
a_q=\frac{q+2}{7},\quad b_q=\frac{53q}{250},\quad
\delta_q=\frac14\left(\sqrt{a_q}-\sqrt{b_q}\right)^2,\quad
r_q=\frac{(a_q-b_q)^2}{8(a_q+b_q)}.
\tag{C110.13}
$$

则 $\ell(T)>\delta_q>r_q>0$，其中四个精确保守有理下界为

$$
\begin{array}{c|c|c|c}
q&a_q&b_q&r_q\\ \hline
1&3/7&53/250&143641/15694000\\
2&4/7&53/125&16641/6097000\\
3&5/7&159/250&18769/33082000\\
4&6/7&106/125&2/326375
\end{array}.
\tag{C110.14}
$$

同一严格下界同时作用于每个原 $\Gamma_C\in\mathfrak D$ 的 (C110.9) 人口 TV，
也给 C-108.1 条件性局部历史误差的下界，包含全部不可见成员。
保留实际 $c_0$ 还给较细的必要条件

$$
\ell(T)\ge
\frac{\left(\sqrt{(q+2)/7}-\sqrt{qc_0}\right)^2}{5(1-c_0)}.
\tag{C110.15}
$$

证明。精确比较
$a_q-b_q=(500-121q)/1750>0$，且 $0<b_q<a_q<1$。
从 (C110.11) 和 $e(T)\le1-a_q$ 得
$\sqrt{b_q}+2\sqrt\ell>\sqrt{a_q}$；两根之差为正，故
$\ell>\delta_q>0$。同理，第一式与 $qc_0<b_q<a_q$ 给 (C110.15)。

为获得完全有理的下界，令 $x=\sqrt{a_q}$、$y=\sqrt{b_q}$。
$x>y>0$ 给 $(x+y)^2<2(a_q+b_q)$，而
$(x-y)(x+y)=a_q-b_q$，所以

$$
\delta_q=\frac{(a_q-b_q)^2}{4(x+y)^2}
>\frac{(a_q-b_q)^2}{8(a_q+b_q)}
=\frac{(500-121q)^2}{14000(621q+500)}=r_q>0.
\tag{C110.16}
$$

逐一代入四个整数并约分即得表中有理数。
C-110.3 将同一通道数值变成每个实际来源的精确人口 TV，故无需对 $C$ 另作优化。
QMB 定理 5.1 的达到性和显式 $u_q$ 上界使每个原无约束 minimizer 也满足本推论，
但此处不求出其误差精确值。证毕。

**命题 C-110.6（零泄漏端点与必要条件的边界）。** 对任意有限维 CPTP $T$，
$\ell(T)=0$ 当且仅当各基投影固定，也当且仅当 BP 成立。
此时任意有限 Kraus 表示都逐项对角，且 C-110.2 退为 $F_v(T)\le qc(v)$。
在原五态菜单中，完全去相干通道给零泄漏但不满足标量端口的 $u_1$ 误差基准；
重置通道给严格正泄漏但最坏误差仍为一。
五维恒等端口则同时有零误差与零泄漏。

证明。(C110.5) 是非负有限和，故 $\ell=0$ 等价于所有 Kraus 非对角元为零。
对角族的完备性使 $T(\Pi_s)=\Pi_s$，也使每个输入的各基人口保持。
反向若基投影固定或 BP 成立，则 $m_{rs}=\delta_{rs}$，直接有 $\ell=0$。
这就是 C-109.2 的零平方和论证在任意 $d$ 的同一端点；未给原竞争类额外添加 BP。
令 $\ell=0$ 代入 (C110.3) 即得所述存活率界。

具体取 $\Delta(X)=\sum_s\Pi_sX\Pi_s$，其五个秩一 Kraus 算子是 $\Pi_s$，
故 $\Delta\in\mathfrak C_1$、$\ell(\Delta)=0$ 且 $F_v(\Delta)=c(v)$。
同一个 $t_0$ 事件给 $e(\Delta)\ge1-c_0>197/250>4/7=u_1$。
另一方面，对 C-108.3 的不可见承诺族，
$(\Delta_A\otimes\mathrm{id})(\Gamma_C)=S$，C-108.3 证明其全部条件性实际双边历史
与 $S$ 相同。因此这些承诺来源的精确标量历史模拟，与全部复输入上的通道误差要求不同。

取固定原模式 $j$，$R_j(X)=\operatorname{tr}(X)\Pi_j$ 的有限 Kraus 族是
$|j\rangle\langle s|$，故 $R_j\in\mathfrak C_1$。
其 $m_{rs}=\delta_{rj}$ 给 $\ell(R_j)=4/5$。
输入任一 $\Pi_s$、$s\ne j$，立即完整读数后 Stop 的两律不交，故 $e(R_j)=1$；
C-110.3 同时给每个匹配来源的人口 TV 恰为 $4/5$。
因此正泄漏本身不保证准确，C-110.5 的下界不是充分条件或最优常数。
最后 $\mathrm{id}\in\mathfrak C_5$ 的一个整块实现直接给 $e=\ell=0$，
故四个严格正下界不延伸到 $q=5$。这些例子既不改变来源切口，
也不将旗数、环境维数、整个块维数与承诺历史模拟资源混为一项。证毕。

## 追加锚（本行以下为增补区）

## 111. 完整历史不可见纤维的四层上限与等谱二／四分叉

**定义 C-111.1（同一纤维及固定坐标中的两个矩阵）。** 沿用 C-108.1 的
条件性实际局部菜单、C-109.1 的原标签、$f,J,V,W$ 与全部复输入合同，记

$$
\mathcal I=\{C=I_5/5+iA:A\in M_5(\mathbb R),\ A^T=-A,\ C\succeq0\}.
\tag{C111.1}
$$

因此 $J\mathcal I J^\dagger$ 恰为 C-108.3 中与 $S$ 具有全部相同实际历史律的
完整人口纤维。$k(C)$、$\operatorname{SN}_{A\mid B}$、
$T_C(X)=(5C)\circ X$ 与 $q_{\rm exact}$ 均按 C-109.1–C-109.3 定义；
稀疏性始终在原系数坐标 $j=0,\ldots,4$ 中计算，依次对应
$(0,1,2,3,13)$，不在另一个基中重新定义。

令 $\omega=e^{2\pi i/5}$，并在这些原坐标中定义向量和投影

$$
u_m(j)=\frac{\omega^{mj}}{\sqrt5},\qquad
P_m=u_mu_m^\dagger,\qquad m,j\in\{0,1,2,3,4\}.
\tag{C111.2}
$$

指数按模五解释，负指数取单位圆上的逆。定义

$$
\begin{aligned}
C^{\rm F}&=\frac15(P_0+2P_1+2P_2),\\
C^{\rm E}&=\frac15\bigl[
(e_0-ie_4)(e_0-ie_4)^\dagger+
(e_1-ie_3)(e_1-ie_3)^\dagger+e_2e_2^\dagger
\bigr].
\end{aligned}
\tag{C111.3}
$$

$u_m$ 是指定原坐标中书写矩阵的辅助向量，不增加傅里叶控制、相位门、制备能力
或读出操作。$C^{\rm E}$ 是 C-108.5 的 $t=1$ 矩阵在同一标签识别下的写法。

**定理 C-111.2（完整复 PSD 纤维的统一四层上界）。** 对每个 $C\in\mathcal I$，

$$
k(C)\le4,\qquad
\operatorname{SN}_{A\mid B}(JCJ^\dagger)\le4,\qquad
q_{\rm exact}(T_C)\le4.
\tag{C111.4}
$$

有限分解可以选为至多二十个四稀疏向量；这些分解允许任意复振幅。

证明。对复 PSD 矩阵逐项共轭仍为 PSD：对任意 $z$，

$$
z^\dagger\overline C z
=\overline{(\overline z)^\dagger C\overline z}\ge0.
$$

由 $C+\overline C=2I_5/5$，得到

$$
0\preceq C\preceq2I_5/5,\qquad \operatorname{tr}C=1.
\tag{C111.5}
$$

将特征值按 $\lambda_0\ge\cdots\ge\lambda_4\ge0$ 排列，则
$\lambda_0\le2/5$，而 $\sum_{m=1}^4\lambda_m=1-\lambda_0\ge3/5$。
非负数的平方根满足
$\sqrt{\sum_m x_m}\le\sum_m\sqrt{x_m}$，因为右边的平方等于
$\sum_mx_m+2\sum_{m<n}\sqrt{x_mx_n}$。故

$$
\sqrt{\lambda_0}
\le\sqrt{2/5}<\sqrt{3/5}
\le\sqrt{\sum_{m=1}^4\lambda_m}
\le\sum_{m=1}^4\sqrt{\lambda_m}.
\tag{C111.6}
$$

这里消费成熟的复矩阵谱充分判据：PSD 矩阵的最大特征值平方根不超过其余
特征值平方根之和时，该矩阵的 factor width 至多 $n-1$。
其谱锥框架见 Johnston–Moein–Pereira–Plosker，
[*Absolutely k-Incoherent Quantum States and Spectral Inequalities for Factor Width of a Matrix*,
arXiv:2205.05110v2](https://arxiv.org/html/2205.05110v2)，§2.1–§2.2、Theorems 3、8；
上述平方根充分形式由 Johnston–Russo–Sikora，
[*Tight bounds for antidistinguishability and circulant sets of pure quantum states*,
arXiv:2311.17047v2](https://arxiv.org/html/2311.17047v2)，Theorem 5.1 的证明给出，
与其 Theorem 3.2 的 Gram/factor-width 对应一致。
该充分方向适用于任意复 PSD 矩阵，无 circulant 或非奇异假设；
circulant 是该文逆向结论的条件，不是这里充分方向的条件。
在本题也可直接对 $G=5C$ 使用其单位对角 Gram 表述：
$G\succeq0$ 且 $G_{jj}=1$，故它是五个单位向量的 Gram 矩阵；
(C111.6) 乘以 $\sqrt5$ 给所需谱条件。
Theorems 5.1、3.2 给 $G$ 的四稀疏有限分解，
再把每个分解向量除以 $\sqrt5$ 即给 $C$ 的相同支撑分解。

具体地，factor width 至多四的有限分解可按每个向量的一个零坐标分成五组。
每组之和 $F_r\succeq0$ 仅支撑在坐标 $r$ 的补集，且
$C=\sum_{r=0}^4F_r$。在该四维坐标子空间内对 $F_r$ 作谱分解，
每组至多四个秩一项，合计至多二十项，且仍为原基中的四稀疏向量。
最后直接应用 C-109.3 的同一来源及整个块通道字典，得另两个不等式。
这个论证没有先限制 $A$ 的十个自由坐标，也没有把实分解代替复分解。证毕。

**命题 C-111.3（同历史、同全谱、同最大纯度的秩三矩阵）。**
$C^{\rm E},C^{\rm F}\in\mathcal I$，且二者及其原匹配态具有相同的非零谱
$2/5,2/5,1/5$，系数矩阵的全谱均为

$$
\{2/5,2/5,1/5,0,0\},\qquad
\operatorname{rank}C^{\rm E}=\operatorname{rank}C^{\rm F}=3,\qquad
\operatorname{tr}((C^{\rm E})^2)=\operatorname{tr}((C^{\rm F})^2)=9/25.
\tag{C111.7}
$$

原匹配态在二十五维空间的全谱再补二十个零；其全部实际
$\mathcal M_{\rm loc}$ 历史律与 $S$ 相同。

证明。单位根的几何级数给
$\sum_{j=0}^4\omega^{mj}=0$，$m=1,2,3,4$，所以 $u_0,\ldots,u_4$
为正交归一基，$\sum_mP_m=I_5$，且
$\overline P_m=P_{-m}$。因此

$$
C^{\rm F}+\overline{C^{\rm F}}
=\frac25(P_0+P_1+P_2+P_3+P_4)=2I_5/5.
\tag{C111.8}
$$

(C111.3) 直接给其 PSD 性、谱、秩和迹，(C111.8) 给
$\operatorname{Re}C^{\rm F}=I_5/5$；Hermitian 性使其虚部实反对称。
更显式地，在原坐标中

$$
C^{\rm F}_{jk}=\frac1{25}
\bigl(1+2\omega^{j-k}+2\omega^{2(j-k)}\bigr),\qquad
A^{\rm F}_{jk}=\frac2{25}
\left(\sin\frac{2\pi(j-k)}5+\sin\frac{4\pi(j-k)}5\right).
\tag{C111.9}
$$

当 $j\ne k$ 时实部为零，当 $j=k$ 时对角为 $1/5$。
$C^{\rm E}$ 的三个互相正交向量的平方范数为 $2,2,1$，
故有同谱；其非对角项仅为 $(0,4)$、$(1,3)$ 上的 $i/5$
及各自的共轭，因而也在 $\mathcal I$。
$J^\dagger J=I_5$ 保持非零谱和纯度。C-108.4 给此纯度是整个不可见纤维的最大值，
C-108.3 给全部实际历史律相同。证毕。

**引理 C-111.4（原三坐标支撑在该值域中的强制系数平衡）。**
令 $\mathcal R=\operatorname{span}_{\mathbb C}\{u_0,u_1,u_2\}$。
对任意复向量 $z=c_0u_0+c_1u_1+c_2u_2\in\mathcal R$，若
$|\operatorname{supp}z|\le3$，则

$$
|c_0|^2=|c_2|^2.
\tag{C111.10}
$$

证明。五个原坐标中至少有两个不同的零坐标 $r,s$。令
$x=\omega^r,y=\omega^s$，则 $x\ne y$ 且 $|x|=|y|=1$。
多项式 $p(t)=c_0+c_1t+c_2t^2$ 满足 $p(x)=p(y)=0$。
相减并使用 $x-y\ne0$，得 $c_1=-c_2(x+y)$；
代回得到 $c_0=c_2xy$。所以 $|c_0|=|c_2|$。
这也包括 $c_2=0$、零向量以及支撑少于三的情况；没有假设系数为实数、
非零系数等模、特定的三个支撑坐标或特定的分解项数。证毕。

**定理 C-111.5（任意有限复分解的四层锐性及五项达到）。**

$$
k(C^{\rm F})=4,\qquad k(C^{\rm E})=2.
\tag{C111.11}
$$

更具体地，设
$\alpha=(-1+i\sqrt7)/2$，并定义五个原坐标向量

$$
z_r=\frac15\left(u_0+\alpha\omega^{-r}u_1+
                 \overline\alpha\omega^{-2r}u_2\right),
\qquad r=0,1,2,3,4.
\tag{C111.12}
$$

则

$$
C^{\rm F}=\sum_{r=0}^4z_rz_r^\dagger,\qquad
\|z_r\|^2=1/5,\qquad
\operatorname{supp}z_r=\{0,1,2,3,4\}\setminus\{r\}.
\tag{C111.13}
$$

证明。先证下界。假设对某个任意有限 $N$ 存在
$C^{\rm F}=\sum_{a=1}^Nz_az_a^\dagger$，
且每个 $z_a\in\mathbb C^5$ 的原坐标支撑至多三。
由 $u_3,u_4\in\ker C^{\rm F}$，对 $m=3,4$ 有

$$
0=u_m^\dagger C^{\rm F}u_m
=\sum_{a=1}^N|u_m^\dagger z_a|^2.
\tag{C111.14}
$$

每项非负，故每个 $z_a$ 均与 $u_3,u_4$ 正交，属于 $\mathcal R$。
将其唯一写成 $z_a=c_{a0}u_0+c_{a1}u_1+c_{a2}u_2$。
引理 C-111.4 逐项给 $|c_{a0}|^2=|c_{a2}|^2$，求和却得到

$$
\frac15=u_0^\dagger C^{\rm F}u_0
=\sum_a|c_{a0}|^2
=\sum_a|c_{a2}|^2
=u_2^\dagger C^{\rm F}u_2=\frac25,
\tag{C111.15}
$$

矛盾。有限项数 $N$ 没有预定上限，所有权重均已吸收入任意复向量，
因此该论证排除了定义 $k$ 中的全部三稀疏有限分解。

再证构造。(C111.12) 的交叉项在对 $r$ 求和后全部消失，
因为不同的 $0,1,2$ 次幂之差不被五整除。
由 $|\alpha|^2=2$，其和恰为
$(P_0+2P_1+2P_2)/5$，且每个平方范数为 $(1+2+2)/25=1/5$。
逐坐标有

$$
z_r(j)=\frac1{5\sqrt5}
 \left[1+\alpha\omega^{j-r}+
             \overline\alpha\omega^{2(j-r)}\right].
\tag{C111.16}
$$

利用 $\alpha+\overline\alpha=-1$，括号内的多项式为

$$
1+\alpha t+\overline\alpha t^2
=(t-1)(\overline\alpha t-1).
\tag{C111.17}
$$

第二个根的模为 $1/\sqrt2$，不在单位圆上；所以在五个单位根中恰有
$t=1$ 一个零，即 $j=r$。这证明 (C111.13)，从而给四的达到。
$C^{\rm E}$ 的 (C111.3) 已是三个支撑大小分别为 $2,2,1$ 的有限分解。
它有非零非对角元，而一稀疏向量的秩一和必为对角矩阵，故其 $k$ 恰为二。证毕。

**命题 C-111.6（同一 Schur 通道的整个块有限精确实现与资源坐标）。**
对 $C^{\rm F}$，存在量子维数四、五个经典旗、每旗一个编码 Kraus 算子
及一个整个块解码 Kraus 算子的精确实现。
对 $C^{\rm E}$，对应存在量子维数二、三个经典旗的这种实现。
二者的最小量子维数分别恰为四与二；二者的最小无约束 Kraus 数均为三。

证明。对 $C^{\rm F}$ 取 (C111.12) 的五个向量，并令
$K_r=\sqrt5\operatorname{diag}z_r$，所以

$$
K_r(j,j)=\frac15
 \left[1+\alpha\omega^{j-r}+
              \overline\alpha\omega^{2(j-r)}\right],\qquad
\operatorname{rank}K_r=4.
\tag{C111.18}
$$

(C111.13) 给

$$
\sum_rK_r^\dagger K_r=I_5,\qquad
\sum_rK_rXK_r^\dagger=(5C^{\rm F})\circ X
\quad\text{对每个 }X\in M_5(\mathbb C).
\tag{C111.19}
$$

为每个 $r$ 固定一个坐标等距嵌入
$V_r:\mathbb C^4\to\mathbb C^5$，其像为坐标 $r$ 的正交补，
取 $B_r=V_r^\dagger K_r$。于是

$$
\operatorname{Enc}(X)=(B_rXB_r^\dagger)_{r=0}^4,\qquad
\operatorname{Dec}\bigl((Y_r)_{r=0}^4\bigr)
=\sum_{r=0}^4V_rY_rV_r^\dagger.
\tag{C111.20}
$$

$V_r^\dagger V_r=I_4$，所以每个分支解码在整个 $M_4$ 上保迹，
而不只是对编码像保迹。又由
$V_rV_r^\dagger K_r=K_r$，得到
$\sum_rB_r^\dagger B_r=I_5$。
任意参考放大下的夹乘正性给编码与解码完全正，故两者均 CPTP。
它们事先固定，复合在全部复矩阵上恰为 (C111.19)，所有量子路径都通过四维块。
这里的任意参考放大只证明完全正性，不授予参考制备或测量。

对 $C^{\rm E}$，三个 $K$ 的对角向量分别取
$e_0-ie_4,e_1-ie_3,e_2$；三个支撑依次嵌入二维块，
第三个支撑用任一个不同原坐标补足二维。相同的 (C109.7) 计算证明整个
$M_2$ 上的解码合同、总保迹和对所有复矩阵的精确复合。

C-109.3 连同 (C111.11) 给量子维数的下界，允许竞争方案有任意有限旗数、
每旗任意有限编码／解码 Kraus 数，且无需其 Kraus 向量等模。
最后，二者的规范归一化 Choi 态经 $(V\otimes W)$ 的标签等距对应分别就是
$JC^{\rm E}J^\dagger$ 与 $JC^{\rm F}J^\dagger$，故 Choi 秩均为三。
标准 Choi/Kraus 秩定理使最小无约束 Kraus 数恰为三；
其三个 Kraus 未被要求分别具有最优端口所需的秩界。
显示构造的五旗／五 Kraus 与三旗／三 Kraus 是达到方案的计数，
没有声称五是四维实现的最少旗数或最少受秩限制 Kraus 数。证毕。

**推论 C-111.7（完整纤维最大值与观察不识别的精确范围）。**
在 C-108.1 的实际菜单假设下，

$$
\boxed{
\max_{C\in\mathcal I} k(C)
=\max_{C\in\mathcal I}\operatorname{SN}_{A\mid B}(JCJ^\dagger)
=\max_{C\in\mathcal I}q_{\rm exact}(T_C)=4.
}
\tag{C111.21}
$$

$C^{\rm E}$ 与 $C^{\rm F}$ 说明：即使同时给出全部实际双边历史律、
完整来源谱、最大整态纯度和矩阵秩，也不能确定原 $A\mid B$ Schmidt number，
或相应同一个 Schur 通道在全部复输入上的最小精确量子块维数。
这些读数相同的两个成员所需资源分别为二和四。

证明。C-111.2 给整个集合的统一上界，C-111.5 与 C-109.3 给达到。
C-111.3 给两个成员的全部所述读数相同，C-111.5–C-111.6 给资源不同，
故任何只依赖这些读数的函数不能在二者上均正确。三个资源坐标的比较为

$$
\begin{array}{c|cc}
 & C^{\rm E}&C^{\rm F}\\ \hline
k(C)=\operatorname{SN}_{A\mid B}=q_{\rm exact}(T_C)&2&4\\
\text{所示经典旗数}&3&5\\
\text{所示复合 Kraus 数}&3&5\\
\text{最小无约束 Kraus 数}=\operatorname{rank}C&3&3\\
\operatorname{tr}(C^2)&9/25&9/25
\end{array}
\tag{C111.22}
$$

原切口始终是 $J e_s=|s,f(s)\rangle$ 的 $A\mid B$，
而非两个独立制备来源之间的切口。$T_C$ 与 $JCJ^\dagger$ 的关系始终是
C-109.2–C-109.3 的同矩阵 Choi／Schur 字典；
对一般匹配输入 $JD J^\dagger$，其局部通道作用仍为
$D\mapsto(5C)\circ D$。特别地，它把 $S$ 保持为 $S$，
没有把 $S$ 变成 $JCJ^\dagger$，也不把未知来源态变成一个通道程序。
(C111.21) 的量词是对每个固定 $C$ 可选择一组固定端口，
并使它精确作用于每个复输入；它没有断言一组不含 $C$ 信息的端口同时实现所有
不同的 $T_C$。

对承诺来源历史，C-110.6 的标量去相干方案仍成立：
$(\Delta_A\otimes\mathrm{id})(JCJ^\dagger)=S$，
并由 C-108.3 保持该承诺族的全部实际双边历史律。
因此四维是指定通道的精确整个块资源上限及达到值，
不是该承诺历史模拟任务的下界。
(C111.21) 也不决定 BP 限制下的最优历史误差、无约束
$\varepsilon_q$ 的精确值或任何近似实现的资源。
标签识别和辅助傅里叶向量均未提供原生树制备桥、额外相位控制、来源副本、
独立制备、交换测量、参考接入或物理资源界。

本章的新增综合推导是完整指定纤维的锐最大值、其固定原坐标中的达到构造、
三稀疏分解的值域系数障碍及同谱最大纯度的二／四资源分叉。
factor-width 的有限复分解、局部 PSD 对偶与 coherence number 的一般框架
分别沿用上述两篇文献及 Ringbauer 等，
[*Certification and Quantification of Multilevel Quantum Coherence*,
arXiv:1707.05282v3](https://arxiv.org/html/1707.05282v3)，§I.1、Theorem 1；
原来源／Schmidt／整个块资源对应直接消费 C-109.3。
这里不主张这些成熟成分或该综合结果的全球原创性。证毕。

## 追加锚（本行以下为增补区）

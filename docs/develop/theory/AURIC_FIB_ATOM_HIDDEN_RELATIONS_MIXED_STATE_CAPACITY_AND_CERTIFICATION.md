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

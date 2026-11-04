# 情境时空算术的量子扩展：程序信息与精确续接

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](159_179_LONG_HORIZON_PREDICTION.md) · [续卷](204_224_CALIBRATION_AND_SPECTRAL_CAPACITY.md)


<a id="entry-708"></a>

## 追加锚（本行以下为增补区）

<a id="section-180"></a>

## 180. 查询时长、配对辨识的总调用成本与临界视界的界限

**定义 180.1（可选择时长的终端查询）。** 保留定义178.1的处理器及其显式参数，令 $\varepsilon=1-r$、$\gamma=-\log r$。一次时长为正整数 $N$ 的查询，重新均匀初始化隐藏记忆，让同一系统无中间干预地通过 $N$ 次处理器，只返回终端系统；其成本为 $N$ 次处理器调用。不同查询的记忆独立。初始可访问态、控制规则与私有随机源均不依赖实际未知 $w$，但可依赖已知 $r$ 和待区分的参数对。允许任意有限维量子工作空间与参考系统；查询间操作采用具有有限或标准 Borel 经典结果空间的可测量子仪器，并允许根据已有经典记录选择下一次时长和是否停止；时长选择是经典选择，不包括时长的相干叠加。不得访问隐藏记忆。总预算 $B$ 要求每条记录分支都满足 $\sum_jN_j\le B$，输入准备和重置不另计成本，平均判错率无条件计算。

记时长 $N$ 的查询通道为 $\mathcal T_w^{(N)}$，则其 Schur 系数为
$$
a_N=\beta^N,\qquad
u_N(w)=r^NZ_{N,w/x}(\alpha),\qquad
F_N(w)=\begin{pmatrix}1&a_N&u_N(w)\\a_N&1&a_N\\u_N(w)&a_N&1\end{pmatrix}.
\tag{180.1}
$$
记 $n(r)=\min\mathcal M_r$ 为最小最大风险视界。对等先验的两个已知假设 $0\le w_0<w_1\le\delta(r)$，令 $d=w_1-w_0$；$B_{1/4}(r;w_0,w_1)$ 是使允许协议的平均判错率下确界不超过 $1/4$ 的最小整数总预算。采用第179节的经典程序模拟方法；允许自适应选择时长时，程序分布按当前所选时长取值，不能直接假设所有程序态同分布。

**定理 180.2（全部整数时长上的统一程序界）。** 存在与 $N,w$ 无关的常数 $c,C>0$，使全部充分近一的 $r$、全部 $N\ge1$ 和 $w\in[0,\delta(r)]$ 都满足
$$
\pi_{N,+}(w):=\frac{1+u_N(w)-2a_N}{2}\ge c\min\{\gamma N,1\},
\qquad
\pi_{N,-}(w):=\frac{1-u_N(w)}2\ge c\min\{\gamma N,1\}.
\tag{180.2}
$$
因而每个时长都有正的经典程序分解
$$
\mathcal T_w^{(N)}
=a_N\operatorname{Id}+\pi_{N,+}(w)\mathcal Q_+
+\pi_{N,-}(w)\mathcal Q_-.
\tag{180.3}
$$
这里 $\mathcal Q_\pm$ 是第179节相邻系数为零、$02$ 系数为 $\pm1$ 的固定通道。一次查询的参考辅助最优信息量及其程序信息量分别满足
$$
I_1^{(N)}(r,w)=\frac{u_N'(w)^2}{1-u_N(w)^2}
\le I_{{\rm prog},N}(r,w)
:=\frac{u_N'(w)^2}{4}
\left(\frac1{\pi_{N,+}(w)}+\frac1{\pi_{N,-}(w)}\right)
\le\frac{CN}{\varepsilon}.
\tag{180.4}
$$
均衡 $02$ 输入达到第一个等号。另令 $P_{N,w}=(a_N,\pi_{N,+}(w),\pi_{N,-}(w))$ 为程序分布；使用自然对数的经典相对熵满足有限参数差界
$$
D(P_{N,w_0}\Vert P_{N,w_1})
\le \frac{CNd^2}{\varepsilon}.
\tag{180.5}
$$

证明。 由 $\alpha/\gamma\to\sqrt3<7/4$，可统一取 $\alpha/\gamma\le7/4$、$x\ge1/2$。令 $t=\gamma N$。有 $a_N\le r^N=e^{-t}$，而每条符号路径的相位绝对值不超过 $N\alpha\le7t/4$。

若 $0<t\le1$，用 $\cos z\ge1-z^2/2$ 及指数函数的三阶下界，得到
$$
\begin{aligned}
1+u_N-2a_N
&\ge e^{-t}\left(e^t-1-\frac{49t^2}{32}\right)\\
&\ge e^{-t}t\left(1-\frac{33t}{32}+\frac{t^2}{6}\right)
\ge\frac{13}{96e}\,t.
\end{aligned}
\tag{180.6}
$$
最后一个二次式在 $[0,1]$ 上递减，末值为 $13/96$。若 $1\le t\le7/6$，则每条相位的绝对值不超过 $49/24<2\pi/3$，所以 $Z_{N,w/x}\ge-1/2$，从而
$$
1+u_N-2a_N\ge1-\frac{5}{2e}>0.
\tag{180.7}
$$
若 $t\ge7/6$，则粗界 $Z_{N,w/x}\ge-1$ 给出
$$
1+u_N-2a_N\ge1-3e^{-7/6}>0.
\tag{180.8}
$$
另有 $1-u_N\ge1-e^{-t}\ge(1-e^{-1})\min\{t,1\}$。故（180.2）可取
$$
c=\min\left\{
\frac{13}{192e},\frac{1-5/(2e)}2,
\frac{1-3e^{-7/6}}2,\frac{1-e^{-1}}2
\right\}>0.
\tag{180.9}
$$
程序权重总和为一，逐系数比较即得（180.3）。这也证明 $2a_N-1<u_N<1$，故第179节证明中的一般 Schur 信息量优化适用，给出（180.4）的精确单次值。

为控制导数，令 $M=N-1$，以 $c_k\in[-1,1]$ 表示在 $M$ 个位置恰有 $k$ 次翻转时终端余弦的平均值。条件符号链给出 Bernstein 多项式
$$
Z_{N,p}=\sum_{k=0}^{M}\binom Mk p^k(1-p)^{M-k}c_k,
\quad
|\partial_pZ_{N,p}|\le2(N-1),
\quad
|\partial_p^2Z_{N,p}|\le4(N-1)(N-2).
\tag{180.10}
$$
后两界分别来自一阶、二阶系数差；$N=1,2$ 的零阶情形按实际多项式解释。于是 $|u_N'(w)|\le2(N-1)e^{-t}/x$。代入（180.2）可得
$$
\frac{I_{{\rm prog},N}}N
\le\frac{2}{cx^2\gamma}
\frac{t e^{-2t}}{\min\{t,1\}}
\le\frac{8}{c\varepsilon}.
\tag{180.11}
$$
这里使用 $\gamma\ge\varepsilon$ 及 $t e^{-2t}/\min\{t,1\}\le1$，可取 $C=8/c$。经典模拟和信息量单调性给出（180.4）的其余不等式。

对有限参数差，令 $b_N=[u_N(w_1)-u_N(w_0)]/2$，则 $|b_N|\le e^{-t}(N-1)d/x$。两个程序分布只有后两个权重分别改变 $b_N,-b_N$。由 $D(P\Vert Q)\le\sum_i(P_i-Q_i)^2/Q_i$，
$$
D(P_{N,w_0}\Vert P_{N,w_1})
\le b_N^2\left(\frac1{\pi_{N,+}(w_1)}+\frac1{\pi_{N,-}(w_1)}\right)
\le\frac{CNd^2}{\varepsilon},
\tag{180.12}
$$
证明（180.5）。证毕。

**定理 180.3（允许自适应时长的最优总调用量级）。** 在定义180.1的协议类内，有
$$
B_{1/4}(r;w_0,w_1)
=\Theta\!\left(\frac{1-r}{(w_1-w_0)^2}\right),
\tag{180.13}
$$
其中常数可对全部充分近一的 $r$ 和全部允许的正参数差统一选择。上界由固定时长 $n(r)$ 的独立均衡 $02$ 输入实现，下界覆盖依据已有记录自适应选择时长的全部允许协议。若只允许第179节的二步查询，则相同判错目标的最小总调用数为 $\Theta(\varepsilon^{-3}/d^2)$；因此允许选择时长后的最小成本与二步接口的最小成本之比为 $\Theta(\varepsilon^4)$。

证明。 先证明预算下界。把协议的每次时长 $N$ 查询替换为（180.3）的固定受控通道和一个新鲜程序符号。为分析保留全部程序符号、量子仪器的经典输出、时长选择和停止记录，记其联合分布为 $\mathsf P_j$，$j=0,1$。给定完整的过往记录，当前条件量子态及控制操作不依赖未知假设；因此下一次仪器输出和时长选择具有相同的条件核。只有新程序符号的条件分布 $P_{N,w_j}$ 依赖假设。经典相对熵的链式法则和（180.5）于是给出
$$
D(\mathsf P_0\Vert\mathsf P_1)
\le\frac{Cd^2}{\varepsilon}
\mathbb E_0\!\left[\sum_jN_j\right]
\le\frac{CBd^2}{\varepsilon}.
\tag{180.14}
$$
每次时长至少为一，故至多发生 $B$ 次查询；停止后补一个不依赖参数的吸收记录，即可把链式法则写在固定长度上。允许一般经典结果空间时，同式由条件概率核的链式法则给出。

最终条件量子态由完整记录经不依赖假设的制备映射给出。因此最终两个输出的半迹范数距离 $d_{\rm tr}(\sigma_0,\sigma_1)=\tfrac12\lVert\sigma_0-\sigma_1\rVert_1$ 不超过 $\operatorname{TV}(\mathsf P_0,\mathsf P_1)$。经典 Pinsker 不等式及（180.14）给出
$$
d_{\rm tr}(\sigma_0,\sigma_1)
\le\sqrt{\frac{CBd^2}{2\varepsilon}}.
\tag{180.15}
$$
等先验判错率不超过 $1/4$ 要求该距离至少为 $1/2$，故 $B\ge\varepsilon/(2Cd^2)$。对协议下确界取逼近序列仍保留此必要条件。

再构造匹配上界。记
$$
T=\frac{\pi}{3\sqrt3},\qquad A=e^{-T},\qquad U=\frac A2,
\qquad D_* =\frac{A(1-T)}2>0.
\tag{180.16}
$$
已有 $\varepsilon n\to T$、$n\alpha\to\pi/3$、$r^n\to A$。又由 $g_r\le B_1=O(\varepsilon)$、$K_r>n$ 及显式 $\delta$ 得 $\delta=O(\varepsilon^3)$。第179节给出 $r-\beta=O(\varepsilon^2)$，所以 $a_n=\beta^n\to A$。

由（178.17）记 $L_n=\partial_pZ_{n,p}|_{p=0}$，则 $\varepsilon L_n\to(1-T)/2$。二阶导数界（180.10）证明
$$
\sup_{0\le w\le\delta}
\left|u_n'(w)-\frac{r^nL_n}{x}\right|
\le\frac{4r^n(n-1)(n-2)\delta}{x^2}=O(\varepsilon).
\tag{180.17}
$$
因而 $u_n(w)\to U$ 及 $\varepsilon u_n'(w)\to D_*$ 都在整个区间上一致成立；积分后还有对所有正参数差的一致割线极限
$$
\frac{\varepsilon[u_n(w_1)-u_n(w_0)]}{w_1-w_0}\longrightarrow D_*.
\tag{180.18}
$$
这一步不把一个仅对固定参数差有效的余项除以任意小的 $d$。并列最大视界也满足同样的视界极限。

均衡 $02$ 测量给出 Bernoulli 概率 $q_\pm^{(n)}(w)=(1\pm u_n(w))/2$。两个假设的根保真度 $f_n$ 满足精确恒等式
$$
1-f_n=\frac{[u_n(w_1)-u_n(w_0)]^2}{8}
\sum_{\nu=\pm}
\frac1{\left(\sqrt{q_\nu^{(n)}(w_0)}+
\sqrt{q_\nu^{(n)}(w_1)}\right)^2}.
\tag{180.19}
$$
于是，在全部允许参数对上一致有
$$
\frac{1-f_n}{d^2/\varepsilon^2}\longrightarrow
\frac{F_*}{8}>0,
\qquad F_*:=\frac{D_*^2}{1-U^2}
=\frac{A^2(1-T)^2}{4(1-A^2/4)}.
\tag{180.20}
$$
$m$ 个独立均衡测量的似然比测试具有判错率至多 $f_n^m/2$。故取 $m=O(\varepsilon^2/d^2)$ 即可达到 $1/4$，所需总调用数 $nm=O(\varepsilon/d^2)$。由于 $d\le\delta=O(\varepsilon^3)$，$\varepsilon^2/d^2\to\infty$ 一致成立，整数取整的附加一次查询不改变成本量级。与下界合并即得（180.13）；第179节的二步接口成本再乘每次的固定成本二，得到所述比值。证毕。

**定理 180.4（预测临界视界不等于最佳信息时长）。** 对任意固定 $t>0$ 和满足 $\varepsilon N(r)\to t$ 的整数时长序列，最优单次信息量的每调用极限为
$$
\varepsilon\frac{I_1^{(N(r))}(r,w)}{N(r)}
\longrightarrow
f(t):=
\frac{e^{-2t}[\sin(\sqrt3t)/\sqrt3-t\cos(\sqrt3t)]^2}
{t[1-e^{-2t}\cos^2(\sqrt3t)]},
\tag{180.21}
$$
且收敛对 $w\in[0,\delta(r)]$ 一致。在 $T=\pi/(3\sqrt3)$ 处，$f'(T)>0$；因此存在略长于临界视界的时长，其渐近每调用信息量严格更大。这里不声称已经确定 $f$ 的全局最大点或自适应信息量的精确最佳常数。

证明。 对该序列，（180.10）的二阶导数界与 $\delta=O(\varepsilon^3)$ 仍给出与（180.17）同阶的误差。三角和（178.17）于是给出一致极限
$$
\varepsilon u_N'(w)\longrightarrow
e^{-t}\left[\frac{\sin(\sqrt3t)}{\sqrt3}-t\cos(\sqrt3t)\right],
\qquad u_N(w)\longrightarrow e^{-t}\cos(\sqrt3t).
\tag{180.22}
$$
将其代入（180.4）的精确单次值，即得（180.21），包括方括号为零的时长。

令 $g(t)=\sin(\sqrt3t)/\sqrt3-t\cos(\sqrt3t)$，则 $g'(t)=\sqrt3t\sin(\sqrt3t)$。在 $T$ 处直接对数微分得到
$$
\frac{f'(T)}{f(T)}
=-2+\frac{6T}{1-T}-\frac1T
-\frac{2A^2}{1-A^2/4}>0.
\tag{180.23}
$$
确有 $1/2<T<1$，所以前三项之和大于二；又 $e^T>1+T>3/2$，故 $A<2/3$，最后一个正分式小于一。因此右端为正，小幅增加 $T$ 会增加 $f$。这一常数层面的改进与（180.13）的最优成本量级相容。证毕。

<a id="entry-710"></a>

## 追加锚（本行以下为增补区）

<a id="section-181"></a>

## 181. 实环境标架、精确自适应信息量与最优查询尺度

**定义 181.1（局部信息率与预算优化）。** 沿用第180节的重置终端查询、经典时长选择及分支预算合同。在固定的 $r,w$ 处对未知参数 $w$ 微分；每个候选控制协议在求导时保持固定。令 $I_m^{(N)}(r,w)$ 为 $m$ 次固定时长 $N$ 查询的全部允许自适应协议的最大信息量，令 $I_{B,\mathrm{var}}^*(r,w)$ 为总调用预算 $B$ 下、允许经典自适应时长的最终记录与量子输出之信息量上确界，并定义
$$
\mathscr I(r,w):=\sup_{N\ge1}
\frac{u_N'(w)^2}{N[1-u_N(w)^2]}.
\tag{181.1}
$$
这些量是局部 SLD 信息量准则；固定局部设计点上的优化不自动给出未知参数的有限样本最优判别常数。以下使用的环境扩张与交叉项消去方法属于既有通道估计工具：Demkowicz-Dobrzański、Maccone，*Using entanglement against noise in quantum metrology*，arXiv:1407.2934v3，式（9），给出交叉算符为零时的一般自适应上界。这里直接构造达到单次下界的环境标架，并将其用于当前配对族。

**定理 181.2（所有固定时长的精确自适应加法性）。** 对全部充分近一的 $r$、全部 $w\in[0,\delta(r)]$ 和正整数 $m,N$，有
$$
I_m^{(N)}(r,w)
=m\frac{u_N'(w)^2}{1-u_N(w)^2}.
\tag{181.2}
$$
独立均衡 $02$ 输入及各次的固定对称、反对称基测量达到等号。特别地，第179节的二步接口满足精确式
$$
I_m^{(2)}(r,w)=m\frac{4J(r)^2}{1-u(w)^2},
\qquad
\sup_{w\in[0,\delta(r)]}
\left|\frac{I_m^{(2)}(r,w)}{m(1-r)^3}-9\right|\longrightarrow0,
\tag{181.3}
$$
且极限对所有正整数 $m$ 统一。该式收紧第179节的程序上界，不改变其有限辨识成本结论。

证明。 固定 $N$，略写 $a=a_N$、$u=u_N(w)$、$h=(1+u)/2$、$\ell=(1-u)/2$。由（180.2）有 $0<a<h<1$。在实三维环境中取单位向量
$$
v_0=(\sqrt h,\sqrt\ell,0),\qquad
v_2=(\sqrt h,-\sqrt\ell,0),\qquad
v_1=\left(\frac a{\sqrt h},0,\sqrt{1-\frac{a^2}{h}}\right).
\tag{181.4}
$$
其 Gram 矩阵恰为 $F(a,u)$，所以等距映射 $V_u|i\rangle=|i\rangle v_i$ 实现该 Schur 通道。各 $v_i$ 为实单位向量，故
$$
V_u^\dagger\partial_uV_u=0,
\qquad
(\partial_uV_u)^\dagger\partial_uV_u
=\operatorname{diag}\left(
\frac1{16h\ell},\frac{a^2}{16h^2(h-a^2)},\frac1{16h\ell}\right).
\tag{181.5}
$$
其中中间项不超过端点项，等价于 $a^2\le h^2$。因此对 $w$ 求导后，记 $A_w=(\partial_wV_w)^\dagger\partial_wV_w$，有
$$
V_w^\dagger\partial_wV_w=0,
\qquad
4\lVert A_w\rVert=\frac{u_N'(w)^2}{1-u_N(w)^2}.
\tag{181.6}
$$

说明它怎样控制已有参数信息的输入。设信号—参考态的当前切向量满足 $\dot\rho=(L\rho+\rho L)/2$，且 $I(\rho)=\operatorname{Tr}(\rho L^2)<\infty$。取任一纯化 $|\psi\rangle$，令 $|\xi\rangle=(L\otimes I)|\psi\rangle/2$，则
$$
\langle\psi|\xi\rangle=0,\qquad
4\lVert\xi\rVert^2=I(\rho).
\tag{181.7}
$$
局部归一化曲线 $\bigl(|\psi\rangle+s|\xi\rangle\bigr)/\sqrt{1+s^2\lVert\xi\rVert^2}$ 的约化态具有相同的当前态和一阶切向量。这里仅匹配切向量，不要求它在邻域中纯化原来的整条输入曲线，因此不需要把任意变秩输入的 SLD 值误等同于整条曲线的最小纯化速度。

施加 $V_w$ 后，纯态切向量为 $\dot V_w|\psi\rangle+V_w|\xi\rangle$。由（181.6），交叉内积消失，纯态切向量与纯态本身仍正交。偏迹的信息量单调性遂给出
$$
I\bigl((\mathcal T_w^{(N)}\otimes\operatorname{Id})(\rho_w)\bigr)
\le I(\rho_w)+4\operatorname{Tr}(\rho_wA_w)
\le I(\rho_w)+\frac{u_N'(w)^2}{1-u_N(w)^2}.
\tag{181.8}
$$
参考上的恒等因子在迹中省略；无限输入信息量时上界按扩展实数理解。该论证也覆盖秩亏的有限 SLD 切向量，因为约化态的 SLD 信息量只依赖当前态与一阶切向量。

从不依赖未知参数的初态开始，每次查询间控制都不增加信息量，每次查询最多增加（181.8）的第二项。归纳得到（181.2）的上界。独立均衡输入达到单次最优信息量，其固定基测量产生独立 Bernoulli 样本，信息量可加，给出匹配下界。（181.3）再由第179节的一致单次极限得到。端点按通道的光滑局部延伸取单侧值。证毕。

**定理 181.3（自适应预算的信息率）。** 第181.1式的上确界对每个允许的 $r,w$ 都由某个有限整数时长达到，并有
$$
I_{B,\mathrm{var}}^*(r,w)\le B\,\mathscr I(r,w),
\qquad
\lim_{B\to\infty}\frac{I_{B,\mathrm{var}}^*(r,w)}B=\mathscr I(r,w).
\tag{181.9}
$$
因此经典反馈选择时长不能超过最佳固定时长的局部每调用信息率。此结论不把有限预算中不能整除的剩余调用算成已经使用。

证明。 在当前选择的时长寄存器上，（181.6）的等距映射作分块受控作用，停止分支取恒等映射。交叉算符在每块都为零。对每条已有记录应用（181.8）并保留经典记录的信息量，得到一次查询的信息增量不超过当前时长 $N$ 的 $I_1^{(N)}(r,w)$ 的期望。对全部查询求和，
$$
I_{\rm out}(r,w)
\le\mathbb E_w\sum_j I_1^{(N_j)}(r,w)
\le\mathscr I(r,w)\,\mathbb E_w\sum_jN_j
\le B\,\mathscr I(r,w).
\tag{181.10}
$$
这里使用带经典记录的条件信息量分解；标准 Borel 结果空间以相应条件积分表示。也可把整个有限预算协议纯化，保留正交的记录环境：参数无关的仪器扩张保持切向量范数，每个受控 $V_N$ 的交叉项为零，其新增平方范数按当前记录概率加权，直接得到同一个界。停止后补恒等映射，使总槽数不超过 $B$。

对固定 $r,w$，由（180.10）及 $|u_N|\le r^N$，
$$
\frac{I_1^{(N)}(r,w)}N
\le\frac{4(N-1)^2r^{2N}}{x^2N(1-r^{2N})}\longrightarrow0
\qquad(N\to\infty).
\tag{181.11}
$$
而 $N=2$ 的信息量严格为正，所以最大值由有限 $N_*$ 达到。预算 $B$ 时使用 $\lfloor B/N_*\rfloor$ 次独立均衡查询，达到 $\lfloor B/N_*\rfloor I_1^{(N_*)}$；除以 $B$ 并令 $B\to\infty$，与上界合并证明（181.9）。证毕。

**定理 181.4（全时长最优常数的变分表达）。** 令 $f(t)$ 为（180.21）的显式曲线，则
$$
F_{\max}:=\max_{t>0}f(t)
\tag{181.12}
$$
存在、有限且严格为正，并有
$$
\sup_{w\in[0,\delta(r)]}
\left|(1-r)\mathscr I(r,w)-F_{\max}\right|
\longrightarrow0.
\tag{181.13}
$$
任何最优整数时长 $N_*(r,w)$ 的归一化值 $(1-r)N_*(r,w)$ 都最终落在一个固定紧区间内；沿任意 $r\uparrow1$、允许的 $w=w(r)$ 及最优时长选择，其聚点均属于 $\operatorname*{arg\,max}_{t>0}f(t)$。反过来，任取该最大点集中的 $t_0$，按 $N(r)=\lfloor t_0/(1-r)\rfloor$ 选择查询时长，就在全部允许 $w$ 上统一达到极限信息率 $F_{\max}/(1-r)$。不要求最大点唯一。

证明。 必须同时控制短时长、紧区间和长时长，不能仅对（180.21）的逐点极限取上确界。令 $s=\gamma N$，其中 $\gamma=-\log r$。翻转一个 Bernoulli 位至多使相位改变 $2N\alpha$，且改变前后的相位绝对值都不超过 $N\alpha$。用余弦导数界 $|\sin z|\le|z|$，得到另一条统一导数界
$$
|\partial_p Z_{N,p}|\le2(N-1)N^2\alpha^2\le2N^3\alpha^2.
\tag{181.14}
$$
因为 $\alpha/\gamma$ 有界、$x\ge1/2$、$\varepsilon\le\gamma$，以及 $1-u_N^2\ge1-e^{-2s}$，对 $0<s\le1$ 可用（181.14）证明
$$
\varepsilon\frac{I_1^{(N)}(r,w)}N\le C_0s^4.
\tag{181.15}
$$
具体地，左侧不超过常数倍的 $\varepsilon N^5\alpha^4/s$，而 $\alpha\le C\gamma$ 将其界为常数倍的 $(\varepsilon/\gamma)s^4$。对 $s\ge1$，改用（180.10）的一阶粗界，得到
$$
\varepsilon\frac{I_1^{(N)}(r,w)}N\le C_\infty s e^{-2s}.
\tag{181.16}
$$
两个常数都可与 $N,w,r$ 无关。这两条界分别在 $s\downarrow0$ 和 $s\to\infty$ 一致趋零。

在任一固定 $0<b\le\varepsilon N\le B_0<\infty$ 的区间上，（180.17）的误差控制统一成立：$N=O(\varepsilon^{-1})$、$\delta=O(\varepsilon^3)$，所以导数误差为 $O(\varepsilon)$。结合三角和（178.17）及 $\alpha/\varepsilon\to\sqrt3$，可得（180.22）及（180.21）在这个区间和全部允许 $w$ 上的统一版本。分母有固定正下界 $1-r^{2N}$，故取平方与商不破坏统一收敛。

显式 $f$ 连续，并由上述尾界满足 $f(t)\to0$，当 $t\downarrow0$ 或 $t\to\infty$；在 $T=\pi/(3\sqrt3)$ 处 $f(T)>0$。因此 $F_{\max}$ 存在且最大点集是 $(0,\infty)$ 内的非空紧集。先把两端的统一尾界压到任意给定误差之下，再在中间紧区间取统一极限，即得（181.13）。

同样的尾界与 $f(T)>0$ 把所有离散最优时长限制在统一紧区间。若其归一化时长沿子列收敛到 $t$，紧区间上的统一极限及（181.13）强迫 $f(t)=F_{\max}$。最后，$\varepsilon\lfloor t_0/\varepsilon\rfloor\to t_0$，代入统一紧区间极限即证明反向可达性。由（180.23），$T$ 自身不是该最大点集的成员；这里仍不提供全局最大点的唯一性或闭式表达。证毕。

<a id="entry-712"></a>

## 追加锚（本行以下为增补区）

<a id="section-182"></a>

## 182. 偏置判别的三能级增益与最优读出的任务依赖

**定义 182.1（同一实 Schur 族的二元决策）。** 固定 $0<a<1$ 和
$$
2a-1<u_0<u_1<1,
\qquad
F(a,u)=\begin{pmatrix}1&a&u\\a&1&a\\u&a&1\end{pmatrix},
\qquad
\mathcal T_u(X)=F(a,u)\odot X.
\tag{182.1}
$$
该范围内 $F(a,u)$ 正定且对角为一，因此 $\mathcal T_u$ 是通道。一次实验可自由选择与未知假设无关的信号—参考输入，使用一次 $\mathcal T_{u_j}$，再作联合测量。假设 $H_j$ 的先验为 $\pi_j$；损失为猜错的概率。定义
$$
h_j=\frac{1+u_j}{2},\quad \ell_j=1-h_j,\quad
\pi_0=\frac{h_1}{h_0+h_1},\quad
\pi_1=\frac{h_0}{h_0+h_1},\quad
k=\pi_0-\pi_1=\frac{u_1-u_0}{2+u_0+u_1}>0.
\tag{182.2}
$$
这里先固定两条候选通道，再指定这一组合法先验；它不是对全部先验的最优式。均衡 $02$ 探针 $|+\rangle=(|0\rangle+|2\rangle)/\sqrt2$ 的输出为
$$
\tau_j=h_j|+\rangle\langle+|+\ell_j|-\rangle\langle-|,
\qquad | -\rangle=(|0\rangle-|2\rangle)/\sqrt2.
\tag{182.3}
$$
故保留整个输出态与保留二项概率 $(h_j,\ell_j)$ 对这组实验等价。本文使用第15.3节的 Schur 输出等距表示与第121节的实验比较原则。一般量子统计比较的文献为 Buscemi，*Comparison of quantum statistical models: equivalent conditions for sufficiency*，arXiv:1004.3794v4：定义7比较全部决策集合与收益，式（49）—（50）定义 CPTP 充分性；定理3的统计态射与命题5的完全比较须区分。以下通过具体风险差与正性障碍论证，不借用任意维度下未经限定的比较逆定理。

**定理 182.2（选定偏置先验的精确全局最优风险）。** 在（182.1）—（182.2）的实验中，均衡 $02$ 输出的最小风险为 $\pi_1$，而允许任意信号—参考输入时的最小风险为
$$
P_{\rm err}^*=\pi_1-k\frac{a^2}{1+2a}<\pi_1.
\tag{182.4}
$$
令 $d=1+2a$、$\nu_*=a^2/d$。达到等号的输入与猜测 $H_1$ 的测量效应分别为
$$
|\psi_*\rangle=
\sqrt{\frac{1+a}{2d}}(|0\rangle+|2\rangle)+\sqrt{\frac ad}|1\rangle,
\qquad
M_1=|\chi_*\rangle\langle\chi_*|,
\quad
|\chi_*\rangle=
\sqrt{\frac{1+a}{2d}}(|0\rangle+|2\rangle)-\sqrt{\frac ad}|1\rangle.
\tag{182.5}
$$
另一个效应为 $M_0=I-M_1$；无需参考系统。

证明。 由先验的选法，$\pi_1h_1=\pi_0h_0$，故均衡输出的加权差为 $-k|-\rangle\langle-|$。其正部为零，始终猜 $H_0$ 已达到风险 $\pi_1$。对一般输入，通道的加权差满足
$$
\Delta:=\pi_1\mathcal T_{u_1}-\pi_0\mathcal T_{u_0}
=-k\,\mathcal S_{F_-},\qquad F_-:=F(a,-1),
\quad \mathcal S_C(X):=C\odot X.
\tag{182.6}
$$
这里 $\mathcal S_{F_-}$ 只是 Hermitian 保持线性映射，并不假定它为通道。

先将任意混合信号—参考输入纯化；丢弃额外纯化系统不增加 Hermitian 迹范数，因此求上界只需纯输入。写 $|\Psi\rangle=\sum_i|i\rangle|v_i\rangle$，令 $p_i=\lVert v_i\rVert^2$、$D_p=\operatorname{diag}(\sqrt{p_i})$。信号标签保证 $|i\rangle|v_i\rangle/\sqrt{p_i}$ 两两正交，零人口处任选参考单位向量即可补成等距映射 $V$。对任意 Hermitian 矩阵 $C$，
$$
(\mathcal S_C\otimes\operatorname{Id})(|\Psi\rangle\langle\Psi|)
=VD_pCD_pV^\dagger.
\tag{182.7}
$$
因此迹范数只依赖 $p$，同样的值可由信号纯态 $\sum_i\sqrt{p_i}|i\rangle$ 达到。

以下正半定分解同时控制所有人口分布，无须先假定最优输入对称。令 $q=(1,-1,1)^{\mathsf T}$、$z=(a,1+a,a)^{\mathsf T}$，则直接逐项计算得
$$
C:=F_-+\nu_*qq^{\mathsf T}
=2|-\rangle\langle-|+\frac{zz^{\mathsf T}}d\succeq0.
\tag{182.8}
$$
由于 $C$ 的每个对角元为 $1+\nu_*$，而 $q$ 的分量平方均为一，矩阵
$D_pF_-D_p=D_pCD_p-\nu_*D_pqq^{\mathsf T}D_p$ 的右侧两项分别正半定，迹为 $1+\nu_*$ 与 $\nu_*$。迹范数三角不等式遂给出
$$
\lVert D_pF_-D_p\rVert_1\le1+2\nu_*.
\tag{182.9}
$$

取（182.5）的输入人口 $p_*=(\frac{1+a}{2d},\frac ad,\frac{1+a}{2d})$，令 $s=a/d$、$t=1-s$。在 $|-\rangle$ 方向，$D_{p_*}F_-D_{p_*}$ 的特征值为 $t>0$；在 $|+\rangle,|1\rangle$ 张成的空间内，其矩阵为
$$
\begin{pmatrix}0&a\sqrt{st}\\a\sqrt{st}&s\end{pmatrix}.
\tag{182.10}
$$
向量 $\sqrt t|+\rangle-\sqrt s|1\rangle=|\chi_*\rangle$ 的特征值为 $-a s=-\nu_*$，另一个特征值为正。因此（182.9）达到等号，而 $M_1$ 正是加权输出差 $-kD_{p_*}F_-D_{p_*}$ 的正谱投影。使用二元 Helstrom 公式 $P_{\rm err}=(1-\lVert\Delta(\rho)\rVert_1)/2$，得到（182.4）。

也可直接核对两种条件概率：
$$
m_j:=\Pr(M_1\mid H_j)
=\frac{(1+a)^2h_j}{d^2}-\frac{a^2}d,
\qquad
\pi_1m_1-\pi_0m_0=k\nu_*.
\tag{182.11}
$$
所以 $\pi_0m_0+\pi_1(1-m_1)=\pi_1-k\nu_*$，与谱计算一致。证毕。

**定理 182.3（两能级可恢复与三能级不可恢复的精确分界）。** 固定任一纯信号—参考输入，并以 $p_i$ 表示其三个信号人口。存在与 $j$ 无关的 CPTP 解码器，将两个均衡输出 $\tau_j$ 分别变成该输入的两个通道输出，当且仅当
$$
p_0p_1p_2=0.
\tag{182.12}
$$
在（182.2）的偏置任务中，所有满足（182.12）的纯输入最小风险都恰为 $\pi_1$；所有 $p_0p_1p_2>0$ 的纯输入都能取得严格小于 $\pi_1$ 的风险。此分类包括任意参考，但不将任意混合输入按其对角人口作同样分类。

证明。 因为 $\tau_j$ 在同一基中对角，任何解码器对这两个态的作用等于按 $+$、$-$ 制备两个固定状态 $\sigma_+,\sigma_-$。由 $h_0\ne h_1$，方程 $\rho_j=h_j\sigma_++\ell_j\sigma_-$ 唯一确定
$$
\sigma_\pm=VD_pF(a,\pm1)D_pV^\dagger.
\tag{182.13}
$$
两者迹均为一。$F(a,1)$ 正半定，其反对称特征值为零、对称块行列式为 $2(1-a^2)>0$，故 $\sigma_+$ 总为状态。另一方面，
$$
\det(D_pF_-D_p)=-4a^2p_0p_1p_2.
\tag{182.14}
$$
三个人口均正时该行列式为负，$\sigma_-$ 不正，故解码器不存在；同时加权输出差 $-kVD_pF_-D_pV^\dagger$ 有严格正部，Helstrom 风险严格小于 $\pi_1$。任一人口为零时，剩余的至多二阶主子矩阵正半定：相邻块行列式为 $1-a^2>0$，$02$ 块行列式为零。这时 $\sigma_-$ 也是状态，制备（182.13）即给出解码器，且加权输出差负半定，风险等于 $\pi_1$。证毕。

**定理 182.4（不存在对所有先验统一最优的一次探针）。** 对（182.1）的同一对候选通道，没有一个固定的一次信号—参考输入，能在所有二元先验下都达到允许任意输入的最小风险，即使允许测量随先验变化。特别地，第179—181节的均衡探针在局部 SLD 信息量和等先验判别上的最优性，不使它成为全部决策任务的充分读出。

证明。 先验相等时，未加权通道差仅有 $02,20$ 系数 $u_1-u_0$。由（182.7），任一纯输入给出的迹范数为
$$
2(u_1-u_0)\sqrt{p_0p_2}\le u_1-u_0.
\tag{182.15}
$$
等号强迫 $p_1=0$、$p_0=p_2=1/2$。因此均衡探针达到等先验全局最小风险 $1/2-(u_1-u_0)/4$，而每个达到该最小值的纯信号—参考输入，在（182.2）下的风险均为 $\pi_1$，严格大于（182.4）。这排除纯输入的统一最优性。

若某个混合输入在所有先验下统一最优，将其额外纯化且保留纯化参考后，丢弃该参考能复现原实验，所以纯化实验在每个先验下至少一样好。原实验已是全局最优，纯化也必须在每个先验下最优，与上述结论矛盾。

同一个障碍还排除更强的程序模拟：不存在固定 CPTP 处理器，以任意信号输入及一份 $\tau_j$ 为输入，精确实现整个 $\mathcal T_{u_j}$。否则固定程序基态 $+$、$-$ 得到两个 CPTP 映射 $\mathcal R_+,\mathcal R_-$，线性方程唯一强迫 $\mathcal R_\pm=\mathcal S_{F(a,\pm1)}$。但 $F_-$ 有负特征值，$\mathcal S_{F_-}$ 作用于均匀信号纯态给出 $F_-/3$，甚至不保持正性，矛盾。

对第177—181节的终端查询，可取 $a=a_N$、$u_j=u_N(w_j)$，只要选出的两值满足 $u_0<u_1$；第180节保证（182.1）的严格域，二步查询的 $w_0<w_1$ 总满足这一顺序。此时（182.4）的风险差完全发生在一次完整重置查询内部，不要求访问隐藏记忆，也不改变既有等先验多次判别的成本界。证毕。

<a id="entry-714"></a>

## 追加锚（本行以下为增补区）

<a id="section-183"></a>

## 183. 全先验判别曲线与三能级探针的精确适用区间

**定义 183.1（有序候选与先验偏置）。** 沿用（182.1）的同一对通道，记
$$
D=u_1-u_0>0,\qquad v=\frac{u_0+u_1}{2},\qquad
\pi_0=\frac{1+b}{2},\quad\pi_1=\frac{1-b}{2},\qquad -1\le b\le1.
\tag{183.1}
$$
令 $R^*(b)$ 为一次通道调用、任意信号—参考输入及联合测量的最小平均误判概率。探针和测量可以依赖已知的候选通道与先验，不可依赖实际未知标签。以下给出全部先验的最优值；采用的 Helstrom 公式和参考归约与第182节相同。加权通道范数的一般框架可参见 Jenčová，*Comparison of quantum channels and statistical experiments*，arXiv:1512.07016v2，第2.2节式（1）—（3）；这里直接求出当前三阶符号的最优值。

对 $b>0$，定义
$$
c=\frac{D-2b(1+v)}4,\qquad q=ba,\qquad
b_-:=\frac{D}{2+u_0+u_1+4a},\qquad
b_+:=\frac{D}{2+u_0+u_1-4a^2}.
\tag{183.2}
$$
这些符号中的 $c,q$ 随 $b$ 变化，且 $0<b_-<b_+<1$。

**定理 183.2（偏向较小参数时的三个最优区间）。** 对 $0<b\le1$，有
$$
R^*(b)=\frac{1-b}{2}-G(b),
\qquad
G(b)=
\begin{cases}
c,&0<b\le b_-,\\[2pt]
\displaystyle\frac{q^2+bc}{b-c+2q},&b_-<b<b_+,\\[6pt]
0,&b_+\le b\le1.
\end{cases}
\tag{183.3}
$$
第一个区间可用均衡 $02$ 输入，读到 $|+\rangle$ 时猜 $H_1$；最后一个区间始终猜 $H_0$ 即最优。中间区间令
$$
s_*:=\frac{q-c}{b-c+2q},\qquad t_*:=1-s_*=
\frac{b+q}{b-c+2q}.
\tag{183.4}
$$
此时 $0<s_*<1$，输入 $\sqrt{t_*}|+\rangle+\sqrt{s_*}|1\rangle$，并以
$|\eta_*\rangle=\sqrt{t_*}|+\rangle-\sqrt{s_*}|1\rangle$ 的投影为猜 $H_1$ 的效应，即达到（183.3）。全部最优值都无需参考系统；端点可以存在额外的最优决策，不要求最优实现唯一。

证明。 加权通道差 $\pi_1\mathcal T_{u_1}-\pi_0\mathcal T_{u_0}$ 的 Schur 符号为
$$
M=\begin{pmatrix}-b&-q&z\\-q&-b&-q\\z&-q&-b\end{pmatrix},
\qquad z=\frac D2-bv=b+2c.
\tag{183.5}
$$
其输出的迹恒为 $-b$，故给定输入的误判率为 $\pi_1$ 减去加权输出正部的迹。由（182.7）及纯化，只需对人口 $p$ 最大化 $\operatorname{Tr}(D_pMD_p)_+$。

为求该最大值，可以将 $p_0,p_2$ 对称化，但须保留相干旗标。令 $U$ 交换能级 $0,2$，将任意纯输入 $|\Psi\rangle$ 替换成
$$
\frac{|\Psi\rangle|0\rangle_F+(U\otimes I)|\Psi\rangle|1\rangle_F}{\sqrt2}.
\tag{183.6}
$$
新输入的人口为 $((p_0+p_2)/2,p_1,(p_0+p_2)/2)$。对输出旗标去相干后，得到两个等权且酉等价的 Hermitian 块，迹范数之和等于原输入的迹范数。去相干不增加 Hermitian 迹范数，所以未去相干的新输出至少一样好；又因迹固定，正部迹也至少一样大。再由（182.7），可用同人口的信号纯态达到新值。

因此取 $p_1=s$、$p_0=p_2=(1-s)/2$。在 $|-\rangle$ 方向，矩阵 $D_pMD_p$ 的特征值为 $-(b+c)(1-s)\le0$，其中
$b+c=[D+2b(1-v)]/4>0$；对称块为
$$
B_s=\begin{pmatrix}
c(1-s)&-q\sqrt{s(1-s)}\\
-q\sqrt{s(1-s)}&-bs
\end{pmatrix}.
\tag{183.7}
$$
它至多有一个严格正特征值。

当 $c\ge q$ 时，$cI-B_s$ 的对角元非负，且行列式为
$$
s\bigl[c^2-q^2+s(bc+q^2)\bigr]\ge0.
\tag{183.8}
$$
所以正部迹至多为 $c$；$s=0$ 达到该值。此条件恰为 $b\le b_-$。

当 $-ba^2<c<q$ 时，令 $L=b-c+2q>b+q>0$、$g=(q^2+bc)/L>0$。下面给出对任意人口都有效的上界。令 $r=(1,-1,1)^{\mathsf T}$，则
$$
M-g rr^{\mathsf T}\preceq0.
\tag{183.9}
$$
确实，反对称特征值为 $-2(b+c)<0$；对称块为
$\left(\begin{smallmatrix}2(c-g)&\sqrt2(g-q)\\\sqrt2(g-q)&-b-g\end{smallmatrix}\right)$，其行列式为
$2[g(b-c+2q)-(bc+q^2)]=0$，而 $g-c=(q-c)^2/L>0$，故两对角元非正。由（183.9），
$$
D_pMD_p\preceq gD_prr^{\mathsf T}D_p,
\qquad \operatorname{Tr}(D_pMD_p)_+\le g.
\tag{183.10}
$$
最后一个不等式来自 $\operatorname{Tr}X_+=\max_{0\le E\le I}\operatorname{Tr}(EX)$ 及 $\lVert D_pr\rVert^2=1$。

取（183.4）的 $s_*,t_*$，则
$c t_*+q s_*=q t_*-b s_*=g$。因此 $|\eta_*\rangle$ 是（183.7）的特征值 $g$ 所属单位向量。另一个对称特征值非正，反对称特征值亦非正，故所给测量达到正部迹 $g$。该中间条件恰为 $b_-<b<b_+$。

当 $c\le-ba^2=-q^2/b$ 时，（183.5）的对称块
$\left(\begin{smallmatrix}2c&-\sqrt2q\\-\sqrt2q&-b\end{smallmatrix}\right)$ 两对角元非正、行列式 $-2(bc+q^2)\ge0$；反对称特征值也为负，故 $M\preceq0$，所有输入的增益均为零。此条件恰为 $b\ge b_+$。公式在两处分界连续相接。最后，$h_0=(1+u_0)/2>a>a^2$，故 $2+u_0+u_1-4a^2>D$；结合分母次序得到所述阈值范围。证毕。

**定理 183.3（相反偏置与三能级增益的不对称性）。** 当 $-1\le b\le0$ 时，令 $\zeta=-b$，则
$$
R^*(b)=\frac{1-\zeta}{2}
-\max\left\{0,\frac{D-\zeta(2-u_0-u_1)}4\right\}.
\tag{183.11}
$$
均衡 $02$ 输入对这整个先验半区都最优。括号内为正时，读到 $|-\rangle$ 猜 $H_0$，否则始终猜 $H_1$。在 $b=0$，两种表达都给出 $R^*(0)=1/2-D/4$。

证明。 对 $\zeta>0$，改看较小先验假设 $H_0$ 的加权差 $\pi_0\mathcal T_{u_0}-\pi_1\mathcal T_{u_1}$。其符号对角为 $-\zeta$、相邻项为 $-\zeta a$、端点项为 $-D/2-\zeta v$。仍可用（183.6）对称化。反对称特征值是
$$
(1-s)\frac{D-2\zeta(1-v)}4.
\tag{183.12}
$$
对称块具有（183.7）的形状，只需将 $b,q,c$ 换成
$\zeta,\zeta a,\widetilde c=-D/4-\zeta(1+v)/2$。因为 $(1+v)/2>a>a^2$，有 $\widetilde c<-\zeta a^2$，所以这个块负半定。正部迹遂不超过（183.12）在 $s=0$ 时的正部，均衡输入达到该值。$\zeta=0$ 则直接由（182.15）处理。证毕。

**定理 183.4（严格三能级区间与校准先验的嵌入）。** 在 $b_-<b<b_+$ 内，每一个支持于至多两个信号能级的纯输入，都严格劣于（183.4）的探针，即使该输入带有参考。第182节的先验 $b=k=D/(2+u_0+u_1)$ 严格位于此区间内，且（183.3）—（183.4）还原（182.4）—（182.5）。

证明。 支持于相邻两个能级时，加权差只含相应负半定主块，增益为零。支持于 $02$ 时，两个对角系数为 $-b$、非对角系数为 $z=b+2c>-b$。其可达最大正部迹为 $\max(c,0)$：$z\le b$ 时该主块负半定；$z>b$ 时，固定总人口为一的最大特征值由均衡人口达到，值为 $(z-b)/2=c$。参考不改变这些迹范数。

中间区间的 $g>0$ 且 $g-c=(q-c)^2/L>0$，所以 $g>\max(c,0)$，证明严格差距。分母次序给出 $b_-<k<b_+$；代入 $b=k$ 得 $c=0$、$q=ka$、$s_*=a/(1+2a)$、$g=ka^2/(1+2a)$，正是第182节的值。证毕。

<a id="entry-716"></a>

## 追加锚（本行以下为增补区）

<a id="section-184"></a>

## 184. 经典程序的精确生成成本与可读信息的严格差距

**定义 184.1（有限经典程序的一阶生成成本）。** 固定 $0<a<1$、$2a-1<u<1$，记 $\mathcal T_v=\mathcal S_{F(a,v)}$、$h=(1+u)/2$、$\ell=1-h$。在名义点 $u$ 的有限经典程序由有限多个与参数无关的 CPTP 映射 $\mathcal R_j$，以及在 $u$ 附近可微的概率 $p_j(v)$ 组成，要求全部 $p_j(u)>0$，并满足
$$
\sum_jp_j(u)\mathcal R_j=\mathcal T_u,
\qquad
\sum_jp_j'(u)\mathcal R_j=\partial_u\mathcal T_u.
\tag{184.1}
$$
定义其局部成本及最优值为
$$
I_{\rm prog}(u)=\sum_j\frac{p_j'(u)^2}{p_j(u)},
\qquad
\mathfrak C(a,u)=\inf I_{\rm prog}(u),
\tag{184.2}
$$
下确界取遍任意有限字母数的程序。若要求在一个邻域内精确满足 $\sum_jp_j(v)\mathcal R_j=\mathcal T_v$，则记相应最优值为 $\mathfrak C_{\rm exact}(a,u)$。这两种优化都在名义点逐点进行，程序组件在求导时保持固定。

这个操作量属于既有的通道切向模拟框架：Matsumoto，*On metric of quantum channel spaces*，arXiv:1006.0300v1，第3.3节定义以经典程序 Fisher 信息量计量的 $G^{\max}$。量子态版本的反向估计及 RLD 输入下界见同作者 *Reverse estimation theory, Complementarity between SLD and RLD, and monotone distances*，arXiv:quant-ph/0511170v1，第4节的一阶匹配构造与输入信息量不等式。以下给出当前通道族的显式最优值与达到它的固定程序，直接证明所需下界，不把量子态模拟结论直接当作通道模拟等号。

**定理 184.2（三个经典符号达到全局最小生成成本）。** 在第184.1节的范围内，
$$
\mathfrak C(a,u)=\mathfrak C_{\rm exact}(a,u)
=\frac{1-a^2}{(1-u)(1+u-2a^2)}
=\frac{1-a^2}{4\ell(h-a^2)}.
\tag{184.3}
$$
下确界由三个固定通道达到。更具体地，按名义点选择
$$
c=\frac{a\ell}{1-a^2},\qquad
\mathcal R_+=\mathcal S_{F(1,1)},\quad
\mathcal R_-=\mathcal S_{F(-1,1)},\quad
\mathcal R_c=\mathcal S_{F(c,2c^2-1)}.
\tag{184.4}
$$
令 $H=(1+v)/2$，定义
$$
p_c(v)=\frac{1-H}{1-c^2},\qquad
p_+(v)=\frac{H+a-(1+a)c}{2(1-c)},\qquad
p_-(v)=\frac{H-a+(1-a)c}{2(1+c)}.
\tag{184.5}
$$
这些权重在整个 $2a-1<v<1$ 内都严格为正，并精确模拟 $\mathcal T_v$；它们在设计点 $v=u$ 的信息量达到（184.3）。

证明。 首先不得把优化域预先缩成 Schur 通道。设 $P_i=|i\rangle\langle i|$。因为 $\mathcal T_u(P_i)=P_i$ 为纯态，而（184.1）将它写成正权重状态凸组合，所以每个 $\mathcal R_j(P_i)=P_i$。取 $\mathcal R_j$ 的任一 Kraus 表示，正性迫使每个 $K_{j\alpha}|i\rangle$ 都落在 $\mathbb C|i\rangle$ 内；各 Kraus 算符遂为对角矩阵。因此每个组件自动是某个相关矩阵 $C_j\succeq0$、$\operatorname{diag}C_j=\mathbf1$ 的 Schur 通道。

令 $F=F(a,u)$，$E$ 为只有 $02,20$ 两项等于一的矩阵，并令 $s_j=p_j'(u)/p_j(u)$。值与切向量匹配给出 $\sum_jp_jC_j=F$、$\sum_jp_js_jC_j=E$。于是
$$
\begin{pmatrix}F&E\\E&Q\end{pmatrix}
=\sum_jp_j
\begin{pmatrix}C_j&s_jC_j\\s_jC_j&s_j^2C_j\end{pmatrix}\succeq0,
\qquad Q=\sum_jp_js_j^2C_j.
\tag{184.6}
$$
每个加项正半定，因为它是 $C_j$ 与 $\left(\begin{smallmatrix}1&s_j\\s_j&s_j^2\end{smallmatrix}\right)$ 的张量积，按分块顺序表示。$F$ 正定，故 Schur 补给出 $Q\succeq EF^{-1}E$。$Q$ 的每个对角元都等于 $I_{\rm prog}$，而
$$
(EF^{-1}E)_{00}=(F^{-1})_{22}
=\frac{1-a^2}{(1-u)(1+u-2a^2)}.
\tag{184.7}
$$
取该对角元即得适用于全部有限程序的下界；它只使用一阶匹配，所以也适用于精确模拟。

现核对达到性。$h>a$ 给出 $0<c<a/(1+a)<1$。前两个组件为秩一相关矩阵；第三个是单位向量
$ (c,\sqrt{1-c^2})$、$(1,0)$、$(c,-\sqrt{1-c^2})$ 的 Gram 矩阵，故也定义通道。（184.5）满足
$$
p_++p_-+p_c=1,\qquad
p_+-p_-+c p_c=a,\qquad
p_++p_-+c^2p_c=H.
\tag{184.8}
$$
相应混合矩阵的相邻项为 $a$，端点项为 $2H-1=v$，从而精确实现整族通道。任意允许的 $v$ 都有 $H>a$，故 $p_->0$；由 $(1+a)c<a$ 得 $p_+>0$；$p_c>0$ 由 $H<1$ 得到。

令 $d=1-a^2$、$q=h-a^2>0$。在设计点，固定 $c=a\ell/d$ 后可化简为
$$
p_+(u)=\frac{q}{2(1-a)(1-c)},\quad
p_-(u)=\frac{q}{2(1+a)(1+c)},\quad
p_c(u)=\frac{\ell}{1-c^2}.
\tag{184.9}
$$
对 $v$ 求导时 $c$ 保持不变，三项导数分别为
$1/[4(1-c)]$、$1/[4(1+c)]$、$-1/[2(1-c^2)]$。代入（184.2）得
$$
I_{\rm prog}(u)
=\frac1{4(1-c^2)}\left[\frac1\ell+\frac{1-ac}{q}\right]
=\frac d{4\ell q},
\tag{184.10}
$$
最后一步使用 $dc=a\ell$。这同时达到一阶模拟与精确模拟的下界，证明（184.3）。证毕。

**定理 184.3（二符号限制的严格额外成本）。** 若第184.1节的程序只允许两个正权重符号，则最小成本为
$$
\mathfrak C_2(a,u)=\frac1{(1-u)(1+u-2a^2)}
=\frac{\mathfrak C(a,u)}{1-a^2}>\mathfrak C(a,u).
\tag{184.11}
$$
因而三个符号是达到（184.3）所需的最少有限字母数。

证明。 设程序为 $p(v)\mathcal R_1+[1-p(v)]\mathcal R_2$。目标切向量非零，所以 $p'(u)\ne0$。由值与切向量的两条线性方程，$\mathcal R_1,\mathcal R_2$ 都必须落在通过 $\mathcal T_u$、方向为 $\partial_u\mathcal T_u$ 的同一仿射直线上，即它们为固定相邻系数 $a$ 的 $\mathcal T_{v_-},\mathcal T_{v_+}$。交换符号后可取 $v_-<u<v_+$。

$F(a,v)$ 正半定的完整条件为 $2a^2-1\le v\le1$：反对称特征值为 $1-v$，对称块为 $\left(\begin{smallmatrix}1+v&\sqrt2a\\\sqrt2a&1\end{smallmatrix}\right)$。所以 $2a^2-1\le v_-<u<v_+\le1$。匹配方程迫使程序的局部信息量为
$$
\frac1{(u-v_-)(v_+-u)}
\ge\frac1{(u-2a^2+1)(1-u)}.
\tag{184.12}
$$
取两个端点通道达到等号，且其线性混合在 $u$ 邻域精确模拟。一个符号的固定通道无法产生非零切向量，结合定理184.2即得最少符号数。证毕。

**定理 184.4（生成与读取的严格信息比）。** 对同一条通道，最大单次可读 SLD 信息量为 $I_{\rm read}(a,u)=1/(1-u^2)$，而
$$
\frac{\mathfrak C(a,u)}{I_{\rm read}(a,u)}
=1+\frac{a^2(1-u)}{1+u-2a^2}>1.
\tag{184.13}
$$
特别地，对第179节的二步接口，以未知配对参数 $w$ 求导、令 $\varepsilon=1-r$，有
$$
\sup_{0\le w\le\delta(r)}
\left|\frac{\mathfrak C_w(r,w)}{\varepsilon^3}-12\right|\longrightarrow0,
\qquad
\sup_{0\le w\le\delta(r)}
\left|\frac{\mathfrak C_w(r,w)}{I_1^{(2)}(r,w)}-\frac43\right|\longrightarrow0.
\tag{184.14}
$$
这里 $\mathfrak C_w$ 仍指对同一二步终端通道逐点优化的有限经典程序成本；生成所用程序标签不属于查询者可访问的输出。

证明。 第181节的实 Stinespring 标架在全部 $0<a<h<1$ 的同一范围内给出可读值 $1/(1-u^2)$，且均衡输入达到它。将（184.3）相除，利用
$(1-a^2)(1+u)-(1+u-2a^2)=a^2(1-u)$，即得（184.13）。

二步接口中 $a=\beta^2$、$u=u_2(w)$、$u_2'(w)=2J$。第178—179节给出在全部允许 $w$ 上统一成立的
$$
1-a^2=4\varepsilon+O(\varepsilon^2),\qquad
\ell=\varepsilon+O(\varepsilon^2),\qquad
h-a^2=3\varepsilon+O(\varepsilon^2),\qquad
J/\varepsilon^2\longrightarrow3.
\tag{184.15}
$$
因此 $\mathfrak C(a,u)\sim1/(3\varepsilon)$。重新参数化将程序信息量乘以 $(2J)^2$，得到 $\mathfrak C_w\sim12\varepsilon^3$；由第181节 $I_1^{(2)}\sim9\varepsilon^3$，再得比值 $4/3$，两者都为一致极限。第179节系数18的程序仍是合法上界；（184.14）求出了这个接口的最小经典程序成本，而可读信息的精确系数仍为9。证毕。

<a id="entry-718"></a>

## 追加锚（本行以下为增补区）

<a id="section-185"></a>

## 185. 最优生成程序的等号结构与有限字母的全区间障碍

**定义 185.1（程序得分与名义中心）。** 固定第184节的 $a,u$，记
$$
h=\frac{1+u}{2},\quad \ell=1-h,\quad d=1-a^2,\quad q=h-a^2,
\quad c=\frac{a\ell}{d},\quad B=\frac d{4\ell q}.
\tag{185.1}
$$
对满足（184.1）的正权重有限程序，记其相关矩阵为 $C_j$、权重为 $p_j$、得分为 $s_j=p_j'/p_j$，全部在当前名义点求值。$e_0,e_1,e_2$ 为标准基，$F=F(a,u)$、$E=\partial_uF$。允许 $C_j$ 为复 Hermitian 相关矩阵；不预先限制它们具有实对称形状。

通道切向模拟框架沿用第184节的文献。Matsumoto，arXiv:quant-ph/0511170v1，第6节定理3已给出满秩量子态族全局最优反向估计的交换条件；这里的每个生成组件还必须是保迹通道，因而其相关矩阵逐个具有单位对角。以下等号分类与有限字母计数直接使用这一附加约束，不由量子态版本的全局结论代替。

**定理 185.2（达到最小成本的全部组件类型）。** 程序达到 $I_{\rm prog}=B$ 当且仅当全部正权重组件可分成以下三类，其得分与矩阵分别满足
$$
\begin{aligned}
\mathcal J_+:&\quad C_j=F(1,1),& s_j&=\frac{1-a}{2q},\\
\mathcal J_-:&\quad C_j=F(-1,1),&s_j&=\frac{1+a}{2q},\\
\mathcal J_c:&\quad C_j(e_0+e_2)=2c C_je_1,&s_j&=-\frac1{2\ell}.
\end{aligned}
\tag{185.2}
$$
这里“当且仅当”在已满足值与切向量匹配的程序中判断。三类的总权重均严格为正，且为
$$
P_+=\frac{h+a-(1+a)c}{2(1-c)},\quad
P_-=\frac{h-a+(1-a)c}{2(1+c)},\quad
P_c=\frac{\ell}{1-c^2}.
\tag{185.3}
$$
中央类的条件平均矩阵恰为
$$
\frac1{P_c}\sum_{j\in\mathcal J_c}p_jC_j=F(c,2c^2-1).
\tag{185.4}
$$
所以最优程序合并同类标签后还原第184节的三符号程序；合并不丢失局部 Fisher 信息量，因为每一类内部的得分相同。

证明。 沿用（184.6）的 $Q$，其 Schur 补具有精确平方分解
$$
Q-EF^{-1}E
=\sum_jp_j(s_jI-EF^{-1})C_j(s_jI-F^{-1}E)\succeq0.
\tag{185.5}
$$
展开右侧并使用 $\sum_jp_jC_j=F$、$\sum_jp_js_jC_j=E$ 即得恒等式。若 $I_{\rm prog}=B$，左侧第 $00$、$22$ 对角元都为零；右侧为正权重的非负平方之和，故每一项都必须在这两个方向为零。正半定矩阵 $C_j$ 遂满足
$$
C_j(s_je_0-F^{-1}e_2)=0,
\qquad C_j(s_je_2-F^{-1}e_0)=0.
\tag{185.6}
$$
逆矩阵的相关系数为
$$
(F^{-1})_{00}=(F^{-1})_{22}=B,\quad
(F^{-1})_{02}=A,\quad
B-A=\frac1{2\ell},\quad B+A=\frac1{2q},\quad
(F^{-1})_{10}=(F^{-1})_{12}=-\frac a{2q}.
\tag{185.7}
$$
对（185.6）作差与求和，得到
$$
\left(s_j+\frac1{2\ell}\right)C_j(e_0-e_2)=0,
\qquad
\left(s_j-\frac1{2q}\right)C_j(e_0+e_2)+\frac aq C_je_1=0.
\tag{185.8}
$$

若 $s_j\ne-1/(2\ell)$，第一式给出 $C_je_0=C_je_2$。第二式于是迫使
$C_je_1=\lambda C_je_0$，其中 $\lambda=(1-2q s_j)/a$ 为实数。由 $C_j$ 的对角均为一及 Hermitian 性，先取第0行、再取第1行即得 $1=\lambda^2$。因此 $\lambda=1$ 或 $-1$，三个列向量都确定，分别得到（185.2）的第一类与第二类。这个推理同时排除了未计入的复相位。

若 $s_j=-1/(2\ell)$，代入第二式，并使用 $q+\ell=d$，即得
$C_j(e_0+e_2)=2c C_je_1$。这正是第三类。反过来，三类条件逐一代回（185.8），再取和差就还原（185.6）。因此（185.5）的端点对角元为零，迫使 $I_{\rm prog}=B$，证明等号分类。

令 $n=e_0+e_2-2c e_1$。中央类满足 $C_jn=0$。将值匹配 $F=\sum_jp_jC_j$ 作用于 $n$，则只有两个端点类留下贡献。第0行与第1行分别给出
$$
(1-c)P_++(1+c)P_-=h-ac,
\qquad
(1-c)P_+-(1+c)P_-=a-c.
\tag{185.9}
$$
解得（185.3）的前两式，再由总权重为一得到第三式。第184节已给出它们的严格正性。扣除两个端点类后，剩余矩阵唯一确定；（184.8）的精确分解表明它就是 $P_cF(c,2c^2-1)$，证明（185.4）。

最后，若某类得分恒为 $s$，则该类总权重 $P$ 的导数为 $Ps$，聚合后的信息量为 $(Ps)^2/P=Ps^2$，恰等于聚合前的 $\sum p_js^2$。证毕。

**定理 185.3（中央等号面的复参数化）。** 对 $0<c<1$，全部满足 $C(e_0+e_2-2c e_1)=0$ 的 Hermitian 单位对角相关矩阵，恰为
$$
C_c(t)=\begin{pmatrix}
1&c+it&2c^2-1+2ict\\
c-it&1&c+it\\
2c^2-1-2ict&c-it&1
\end{pmatrix},\qquad t\in\mathbb R,\quad t^2\le1-c^2.
\tag{185.10}
$$
令 $\theta=\arccos c$、$z_\pm=(e^{\pm i\theta},1,e^{\mp i\theta})^{\mathsf T}$，则该线段的两端为秩一相关矩阵 $z_\pm z_\pm^\dagger$，且
$$
\tfrac12(z_+z_+^\dagger+z_-z_-^\dagger)=F(c,2c^2-1).
\tag{185.11}
$$
因此定理185.2只强迫中央参数 $t$ 的条件平均为零，不强迫每个中央组件为实矩阵。

证明。 写 $C_{01}=x$。核关系的第0行给出 $C_{02}=2cx-1$，第1行给出 $C_{12}=2c-\bar x$。第2行与 Hermitian 性再给出 $C_{12}=x$，故 $\operatorname{Re}x=c$。写 $x=c+it$ 就得到（185.10）的全部项。

核关系表示第三列为前两列的固定线性组合，所以整个矩阵正半定，当且仅当左上二阶块正半定；例如以列系数矩阵 $R=\left(\begin{smallmatrix}1&0&-1\\0&1&2c\end{smallmatrix}\right)$ 可写成 $C=R^\dagger C_{\{0,1\}}R$。二阶块行列式为 $1-c^2-t^2$，即给出所述参数区间。区间两端 $t=\pm\sin\theta$ 分别得到 $z_\pm z_\pm^\dagger$，其共轭平均为（185.11）。将三符号最优程序的中央分支平分成这两个端点，并共用中央得分，就得到中央组件非实的四符号最优程序，证明最后断言。证毕。

**定义 185.4（一个固定字母表上的全区间精确程序）。** 令 $J$ 是 $(2a-1,1)$ 中的非空开区间。固定 $m$ 个 CPTP 映射 $\mathcal R_1,\ldots,\mathcal R_m$，允许各概率 $p_j(v)$ 在 $J$ 上为非负 $C^1$ 函数，并要求 $\sum_jp_j(v)\mathcal R_j=\mathcal T_v$。在某点 $v$，用活跃集合 $A(v)=\{j:p_j(v)>0\}$ 定义点态信息量
$$
I(v)=\sum_{j\in A(v)}\frac{p_j'(v)^2}{p_j(v)}.
\tag{185.12}
$$
零权重处因函数在双侧非负而有 $p_j'(v)=0$。这里采用当前概率及一阶切向量确定的点态值，不把邻域信息量的连续延拓当作同一个定义。

**定理 185.5（有限固定程序只能在有限多个点达到最低成本）。** 对第185.4节的程序，若在至少一个点达到 $I(v)=\mathfrak C(a,v)$，则字母表中必须包含 $\mathcal S_{F(1,1)}$ 与 $\mathcal S_{F(-1,1)}$ 两种组件，且达到等号的不同点总数至多为 $m-2$。特别地，任何固定有限程序都不可能在开区间 $J$ 的每一点达到最低成本。若各符号在整个 $J$ 上始终为正权重，则最多只能有一个等号点。

证明。 在任意等号点，删去零权重标签不改变值或切向量；将剩余概率以当前值及导数作局部线性延伸，就得到归一且严格为正的有限切向程序。活跃组件按第184节自动成为 Schur 通道，并满足定理185.2的三类结构。两种端点类的总权重都严格为正，所以固定字母表中必有这两种组件；中央类总权重也严格为正，所以至少有一个非端点组件在该点活跃。

固定某个非端点组件 $C_j$。只要它在一个等号点活跃，就只能属于中央类。取（185.2）中央关系的第1行，得到
$$
\frac{(C_j)_{10}+(C_j)_{12}}2
=c(v)=\frac{a(1-v)}{2(1-a^2)}.
\tag{185.13}
$$
左侧由该固定组件唯一决定，右侧随 $v$ 严格递减。因此一个非端点标签至多能在一个等号点活跃。不同等号点各需至少一个这样的标签，且不能复用；去掉至少两个端点标签后，至多剩 $m-2$ 个，证明计数界。若从未活跃的组件不是 Schur 通道，它不承担任何等号点，因此也不会破坏计数。

若所有标签处处正权重，取任一等号点所需的非端点标签；它在另一假定等号点仍活跃，与（185.13）的唯一性矛盾，故等号点至多一个。开区间有无限多个点，所以有限字母表无法处处达到最小值。该结论限制的是统一达到最低成本；第184节的三符号程序仍可精确模拟整个允许区间。证毕。

<a id="entry-720"></a>

## 追加锚（本行以下为增补区）

<a id="section-186"></a>

## 186. 固定生成程序的统一正差距与四分支改进

**定义 186.1（固定程序的最坏相对成本）。** 固定 $0<a<1$，令 $J_a=(2a-1,1)$、$\mathcal T_u=\mathcal S_{F(a,u)}$。程序 $\mathcal P$ 由有限多个不随 $u$ 改变的 CPTP 组件 $\mathcal R_j$ 与非负 $C^1$ 概率 $p_j(u)$ 组成，并在整个 $J_a$ 满足
$$
\sum_jp_j(u)\mathcal R_j=\mathcal T_u.
\tag{186.1}
$$
采用第185.4节的点态信息量约定，定义
$$
I_{\mathcal P}(u)=\sum_{j:p_j(u)>0}\frac{p_j'(u)^2}{p_j(u)},\qquad
B(a,u)=\frac{1-a^2}{(1-u)(1+u-2a^2)},
$$
$$
R(\mathcal P)=\sup_{u\in J_a}\frac{I_{\mathcal P}(u)}{B(a,u)},
\qquad
R_*(a)=\inf_{\mathcal P}R(\mathcal P).
\tag{186.2}
$$
下确界允许任意有限字母数，且每个候选必须用同一套固定组件模拟全部参数。$B$ 是第184节允许按名义点重新设计组件时的最小生成成本。因而 $R_*$ 比较的是统一设计与逐点设计，而不是生成成本与实验可读信息量。

这里沿用 Matsumoto，*On metric of quantum channel spaces*，arXiv:1006.0300v1，第3.3节的经典切向模拟框架。其量子态反向估计的整体交换条件见 arXiv:quant-ph/0511170v1，第6节；以下统一下界直接处理当前通道族每个组件的单位对角约束，不将该状态条件当作通道的极小极大结论。

**定理 186.2（不依赖字母数的统一正差距）。** 对每个 $0<a<1$，
$$
R_*(a)\ge
1+\frac{a^2}{[1+4a+2(1+a)\log2]^2}>1.
\tag{186.3}
$$
因此即使允许字母数沿程序序列不断增加，也不能使全区间最坏相对成本趋于一。

证明。 任取满足（186.1）的有限程序，记
$$
h=\frac{1+u}{2},\quad \ell=1-h,\quad d=1-a^2,\quad q=h-a^2=d-\ell>0.
\tag{186.4}
$$
先将全部 CPTP 组件归约成固定标量支撑。删去在整个区间从未活跃的标签。每个剩余组件在某点具有正权重；因为 $\mathcal T_u$ 固定每个纯基态，第184.2节的纯态凸分解与 Kraus 论证迫使该组件是相关矩阵 $C_j$ 的 Schur 通道。将每个 $C_j$ 在端点交换 $0\leftrightarrow2$ 与复共轭下平均。此操作保持正半定、单位对角以及目标矩阵 $F(a,u)$，故保持精确模拟。概率曲线不变，信息成本也不变。

平均后的矩阵具有形状 $F(x,2H-1)$，其中 $x,H$ 为实数，正半定条件等价于 $x^2\le H\le1$。当 $|x|<1$ 时令 $\lambda=(1-H)/(1-x^2)$，则
$$
F(x,2H-1)=\lambda F(x,2x^2-1)
+(1-\lambda)\left[\frac{1+x}{2}F(1,1)+\frac{1-x}{2}F(-1,1)\right].
\tag{186.5}
$$
系数非负且与参数无关；$x=\pm1$ 时矩阵本来就是对应端点。按（186.5）拆分各标签，并保留不同原标签的副本。若拆分比例为 $\theta_k$，则新概率为 $\theta_kp_j$，其信息量之和仍是 $p_j'^2/p_j$。零比例项删去，零概率处的导数为零。所以这一步也精确保留第185.4节约定的信息成本。

归约后只须研究固定有限支撑 $x_j\in[-1,1]$ 上的随机变量 $X$，其概率曲线满足
$$
\mathbb E X=a,\qquad \mathbb E X^2=h.
\tag{186.6}
$$
这些约束同时保证相关矩阵混合为 $F(a,u)$。定义另一组归一概率及其均值、方差
$$
\nu_j(u)=\frac{(1-x_j^2)p_j(u)}{\ell},\qquad
m=\mathbb E_\nu X,\qquad \sigma^2=\operatorname{Var}_\nu X.
\tag{186.7}
$$
端点标签的 $\nu$ 权重为零。由（186.6）得到
$\mathbb E X^3=a-\ell m$、$\mathbb E X^4=h-\ell(m^2+\sigma^2)$。将 $X^2$ 对常数与 $X$ 作线性回归后，剩余方差为
$$
\begin{aligned}
V&=\operatorname{Var}(X^2)-\frac{\operatorname{Cov}(X^2,X)^2}{q}\\
&=\ell(h-m^2-\sigma^2)-\frac{\ell^2(a-m)^2}{q}\\
&=\frac{\ell q}{d}
-\frac{\ell d}{q}\left(m-\frac{a\ell}{d}\right)^2
-\ell\sigma^2.
\end{aligned}
\tag{186.8}
$$
这是有限矩恒等式，不对支撑大小作任何限制。

在活跃标签上令 $s_j=p_j'/p_j$，在零权重标签上置 $s_j=0$。非负 $C^1$ 函数在内部零点导数为零，所以对归一性及（186.6）求导，得到
$$
\mathbb Es=0,\qquad \mathbb E(sX)=0,\qquad
\mathbb E(sX^2)=\tfrac12.
\tag{186.9}
$$
以 $Y=X^2-h-\operatorname{Cov}(X^2,X)(X-a)/q$ 表示回归残差，则 $\mathbb EY^2=V$、$\mathbb E(sY)=1/2$。Cauchy–Schwarz 不等式给出
$$
I_{\mathcal P}V\ge\tfrac14.
\tag{186.10}
$$
若 $R=R(\mathcal P)=\infty$，所需下界已成立。否则 $I_{\mathcal P}\le RB=Rd/(4\ell q)$；结合（186.8）与（186.10），可得
$$
\left|m-\frac{a\ell}{d}\right|
\le\frac qd\sqrt{1-\frac1R},
\qquad
\sigma^2\le\frac qd\left(1-\frac1R\right).
\tag{186.11}
$$
特别地 $R\ge1$。这两式表明，接近逐点最优要求辅助分布同时靠近移动中心 $a\ell/d$ 并具有很小方差。

然而固定支撑上均值的移动也受同一个得分限制。对（186.7）求导，并使用 $\mathbb E[s(1-X^2)]=-1/2$，得到
$$
m'=\frac1\ell\mathbb E[s(1-X^2)(X-m)].
\tag{186.12}
$$
由于 $(1-X^2)^2\le1-X^2$，再用 Cauchy–Schwarz 和（186.11），有
$$
|m'|^2\le\frac{I_{\mathcal P}}{\ell^2}
\mathbb E[(1-X^2)^2(X-m)^2]
\le\frac{I_{\mathcal P}\sigma^2}{\ell}
\le\frac{R-1}{4\ell^2}.
\tag{186.13}
$$
因此对任意 $2a-1<u_0<u_1<1$，
$$
|m(u_1)-m(u_0)|
\le\sqrt{R-1}\log\frac{1-u_0}{1-u_1}.
\tag{186.14}
$$

取 $u_1=a$，让 $u_0\downarrow2a-1$。目标中心 $a\ell/d$ 在这两点间的差趋于 $a/[2(1+a)]$；两处的 $q/d$ 分别趋于 $a/(1+a)$ 与 $(1+2a)/[2(1+a)]$。三角不等式、（186.11）和（186.14）给出
$$
\frac{a}{2(1+a)}
\le\sqrt{R-1}
\left[\frac{1+4a}{2(1+a)\sqrt R}+\log2\right].
\tag{186.15}
$$
这里只对已成立的不等式取极限，不要求概率或均值在区间左端具有极限。用 $1/\sqrt R\le1$ 放大右端，再移项平方，得到（186.3）对当前任意程序成立；取下确界即证。证毕。

**定理 186.3（三符号设计族内的精确极小极大值）。** 在第184节的三组件族
$F(1,1),F(-1,1),F(c,2c^2-1)$ 中，固定 $0<c<a/(1+a)$，采用（184.5）的全区间精确权重。其信息量 $I_c$ 满足
$$
\frac{I_c(u)}{B(a,u)}=\frac1{1-z_c(u)^2},\qquad
z_c(u)=\frac{dc-a\ell}{q}.
\tag{186.16}
$$
在上述 $c$ 范围内，唯一使全区间最坏相对成本最小的选择为
$$
c_* =\frac a{1+2a},\qquad
R_3(a)=\frac{(1+2a)^2}{(1+a)(1+3a)}<\frac98.
\tag{186.17}
$$
因此 $R_*(a)\le R_3(a)$；此处的最优性仅针对所述三符号设计族。

证明。 三个支撑点为 $1,-1,c$，故辅助分布 $\nu$ 集中在 $c$，在（186.8）中有 $m=c,\sigma^2=0$。三点均为正概率时，对常数与 $X$ 正交的函数空间为一维，所以得分与非零残差 $Y$ 成比例。（186.9）遂使（186.10）达到等号，给出 $I_c=1/(4V)$。将（186.8）除以 $\ell q/d$ 即得到（186.16）。也可直接对（184.5）求导后相加得到相同恒等式。

由于
$$
z_c'(u)=\frac{d(a-c)}{2q^2}>0,\qquad
\lim_{u\uparrow1}z_c(u)=c,\qquad
\lim_{u\downarrow2a-1}z_c(u)=\frac{1+a}{a}c-1<0,
\tag{186.18}
$$
全区间上 $|z_c|$ 的上确界为
$\max\{c,1-(1+a)c/a\}$。前项严格增加、后项严格减少；其最大值在二者相等时唯一最小，解得 $c_*$。代入 $1/(1-c_*^2)$ 即得 $R_3$。最后
$9(1+a)(1+3a)-8(1+2a)^2=(1-a)(1+5a)>0$，证明严格上界。证毕。

**定理 186.4（四组件严格改进三符号设计族）。** 当 $a=1/2$、$0<u<1$ 时，存在四个固定组件的全区间精确程序，使
$$
R(\mathcal P)=\frac{4075}{3822}
=\frac{16}{15}-\frac3{6370}
<R_3(\tfrac12).
\tag{186.19}
$$
因而三符号设计族的极小极大值不是所有有限程序的极小极大值，且
$$
1+\frac1{36(1+\log2)^2}
\le R_*(\tfrac12)\le\frac{4075}{3822}.
\tag{186.20}
$$

证明。 取四个组件 $F(1,1),F(-1,1),F(1/5,2/25-1),F(3/10,18/100-1)$ 的 Schur 通道。记
$$
A(u)=323+265u+5u^2-5u^3,\qquad
D(u)=111+435u-5u^2+5u^3,
$$
$$
p_+=\frac{A(u)}{784},\qquad p_-=\frac{D(u)}{2184},\qquad
p_0=\frac{25(1-u)(3+u^2)}{336},\qquad
p_1=\frac{50(1-u)(4-u^2)}{637}.
\tag{186.21}
$$
四个权重在 $(0,1)$ 严格为正：$A\ge323$，$D\ge111-5>0$，后两项的各因子也严格为正。直接展开得
$$
p_++p_-+p_0+p_1=1,\qquad
p_+-p_-+\tfrac15p_0+\tfrac3{10}p_1=\tfrac12,
$$
$$
p_++p_-+\tfrac1{25}p_0+\tfrac9{100}p_1=\tfrac{1+u}{2}.
\tag{186.22}
$$
所以程序在整个区间精确模拟目标。等价地，它是中心 $1/5$ 与 $3/10$ 的两组三符号程序，以 $\alpha(u)=(3+u^2)/7$ 和 $1-\alpha(u)$ 混合，再合并共同的两个端点标签。

令 $Q(u)=I_{\mathcal P}(u)/B(1/2,u)$。对（186.21）中的完整权重求导，包含 $\alpha$ 的导数，通分后得到恒等式
$$
\frac{4075}{3822}-Q(u)
=\frac{25(1-u)P(u)}{3822(3+u^2)(4-u^2)A(u)D(u)},
\tag{186.23}
$$
其中多项式采用无组合系数的 Bernstein 基展开为
$$
P(u)=\sum_{k=0}^9 b_k u^k(1-u)^{9-k},
$$
$$
\begin{aligned}
(b_0,\ldots,b_9)=(&185868,\ 53289912,\ 399010545,\\
&1263052704,\ 2112746798,\ 1919242930,\\
&863793010,\ 153863608,\ 39440664,\ 25769520).
\end{aligned}
\tag{186.24}
$$
所有系数为正，分母的所有因子在区间内为正，故 $Q(u)<4075/3822$。另一方面，两个端点权重在 $u\uparrow1$ 时保持正值，其信息量除以发散的 $B$ 后趋于零；两个中央权重线性消失，给出
$$
\lim_{u\uparrow1}Q(u)
=\frac{4/7}{1-(1/5)^2}+\frac{3/7}{1-(3/10)^2}
=\frac{4075}{3822}.
\tag{186.25}
$$
所以该程序的上确界恰为（186.19），而不是仅有一个离散采样上界。结合（186.3）即得（186.20）。这些界没有确定 $R_*(a)$ 的精确值，也没有确定其下确界是否由某个有限程序达到。证毕。

<a id="entry-722"></a>

## 追加锚（本行以下为增补区）

<a id="section-187"></a>

## 187. 一枚非交换程序消去固定经典设计的统一额外成本

**定义 187.1（固定量子处理器与程序的信息量）。** 仍固定 $0<a<1$、$J_a=(2a-1,1)$。有限维量子程序由固定的 CPTP 映射
$\mathcal G:\mathcal B(\mathbb C^3\otimes\mathcal H_P)\to\mathcal B(\mathbb C^3)$ 与一条 $C^1$ 密度矩阵曲线 $\rho_u$ 组成，要求对每个输入 $\omega$ 及全部 $u\in J_a$，
$$
\mathcal G(\omega\otimes\rho_u)=\mathcal T_u(\omega).
\tag{187.1}
$$
程序与输入初始独立；每次使用提供一份新的程序态，不要求处理器保留程序。以程序态的 SLD 信息量作为输入信息成本，记为 $I_Q(\rho_u)$。若 $\rho_u=\sum_j\lambda_j|j\rangle\langle j|$ 是某一点的谱分解，则采用
$$
I_Q(\rho_u)=
\sum_{j,k:\lambda_j+\lambda_k>0}
\frac{2|\langle j|\rho_u'|k\rangle|^2}{\lambda_j+\lambda_k}.
\tag{187.2}
$$
这是当前态与切向量确定的点态值。称整条程序曲线为交换的，若 $[\rho_u,\rho_v]=0$ 对全部 $u,v\in J_a$ 成立。定义量子程序的最优最坏相对成本
$$
R_Q^*(a)=\inf_{(\mathcal G,\rho)}\sup_{u\in J_a}\frac{I_Q(\rho_u)}{B(a,u)},
$$
下确界取遍满足（187.1）的所有有限维固定处理器及程序曲线。

固定处理器与可变程序寄存器是既有的量子编程框架。Hillery、Ziman、Bužek，*Implementation of quantum maps by programmable quantum processors*，Phys. Rev. A **66**, 042302（2002），DOI:10.1103/PhysRevA.66.042302，第II.B节式（2.12）处理混合程序，第III.B节的 $Y$ 处理器由数据基控制程序上的幺正操作。下面使用该结构，计算当前三能级通道族的确切信息成本，并与第186节的统一经典下界比较。

**定理 187.2（固定量子比特程序的统一成本与交换障碍）。** 记 $d=1-a^2$，令 $X,Y,Z$ 为程序量子比特上的 Pauli 矩阵。定义
$$
\rho_u=\frac12\left[I+\frac{a(1-u)}{\sqrt d}X+uZ\right],
\qquad
U_0=I,\quad U_1=\sqrt d\,X+aZ,\quad U_2=Z,
\tag{187.3}
$$
以及固定处理器
$$
W=\sum_{i=0}^2|i\rangle\langle i|\otimes U_i,
\qquad
\mathcal G(\Omega)=\operatorname{Tr}_P(W\Omega W^\dagger).
\tag{187.4}
$$
则 $\rho_u$ 在 $J_a$ 内为满秩密度矩阵，$\mathcal G$ 精确实现（187.1），并在整个区间满足
$$
I_Q(\rho_u)=B(a,u)
=\frac{1-a^2}{(1-u)(1+u-2a^2)}.
\tag{187.5}
$$
该程序族在不同参数处不交换：
$$
[\rho_u,\rho_v]=\frac{ia(u-v)}{2\sqrt d}Y\ne0
\qquad(u\ne v).
\tag{187.6}
$$
与此相对，任何满足（187.1）的有限维交换程序，不论其固定处理器如何选择，都必须满足
$$
\sup_{u\in J_a}\frac{I_Q(\rho_u)}{B(a,u)}
\ge1+\frac{a^2}{[1+4a+2(1+a)\log2]^2}>1.
\tag{187.7}
$$
而所有有限维量子程序的精确极小极大值为
$$
R_Q^*(a)=1.
$$
因此（187.3）以一枚非交换量子比特程序达到最优最坏相对成本，而所有有限维交换程序都有统一的正额外成本。

证明。 $\rho_u$ 的迹为一，且
$$
\det\rho_u=\frac{(1-u)(1+u-2a^2)}{4d}>0.
\tag{187.8}
$$
因为 $2a-1>2a^2-1$，允许区间中的两个分子因子均为正，所以它确为满秩密度矩阵。$XZ+ZX=0$ 给出 $U_1^\dagger U_1=(d+a^2)I=I$；其他两个 $U_i$ 也幺正，故 $W$ 幺正并定义固定 CPTP 处理器。

处理器作用于输入矩阵单位 $|i\rangle\langle j|$ 后，乘上相关系数
$$
C_{ij}(u)=\operatorname{Tr}(U_i\rho_uU_j^\dagger)
=\operatorname{Tr}(\rho_u U_j^\dagger U_i).
\tag{187.9}
$$
程序态的三个 Pauli 期望为
$\langle X\rangle=a(1-u)/\sqrt d$、$\langle Y\rangle=0$、$\langle Z\rangle=u$。于是 $C_{ii}=1$，并且
$$
C_{01}=\sqrt d\,\langle X\rangle+a\langle Z\rangle=a,
\qquad C_{02}=\langle Z\rangle=u,
$$
$$
C_{12}=\operatorname{Tr}[\rho_u Z(\sqrt d\,X+aZ)]
=a+i\sqrt d\,\langle Y\rangle=a.
\tag{187.10}
$$
其余项由 Hermitian 性给出，所以 $C(u)=F(a,u)$。这逐矩阵单位证明（187.1），同时保证与任意外部参考系统张量恒等映射后仍实现同一通道。

接着计算信息量。对满秩量子比特态 $\rho=(I+\mathbf r\cdot\boldsymbol\sigma)/2$，将 SLD 写成 $L=\alpha I+\boldsymbol\beta\cdot\boldsymbol\sigma$，方程 $\rho'=(\rho L+L\rho)/2$ 化为
$\alpha+\mathbf r\cdot\boldsymbol\beta=0$、$\boldsymbol\beta+\alpha\mathbf r=\mathbf r'$。解出它们并取 $\operatorname{Tr}(\rho L^2)$，得到通常的 Bloch 表达式
$$
I_Q=|\mathbf r'|^2+
\frac{(\mathbf r\cdot\mathbf r')^2}{1-|\mathbf r|^2}.
\tag{187.11}
$$
在当前曲线中，记 $A=(1-u)(1+u-2a^2)$，则
$$
|\mathbf r'|^2=\frac1d,\qquad
\mathbf r\cdot\mathbf r'=\frac{u-a^2}{d},\qquad
1-|\mathbf r|^2=\frac Ad,
\qquad A+(u-a^2)^2=d^2.
\tag{187.12}
$$
代入（187.11）即得 $I_Q=1/d+(u-a^2)^2/(dA)=d/A$，证明（187.5）。此外，Pauli 乘法给出
$[\rho_u,\rho_v]=(i/2)(\mathbf r_u\times\mathbf r_v)\cdot\boldsymbol\sigma$，其叉积只有 $Y$ 分量 $a(u-v)/\sqrt d$，即为（187.6）。

最后设某个有限维程序族处处交换。有限维 Hermitian 交换族可同时对角化，故存在一个不随参数改变的正交基，使
$$
\rho_u=\sum_{j=1}^{m}p_j(u)|j\rangle\langle j|.
\tag{187.13}
$$
各 $p_j$ 非负且为 $C^1$ 函数。固定处理器诱导出 $m$ 个固定 CPTP 组件
$\mathcal R_j(\omega)=\mathcal G(\omega\otimes|j\rangle\langle j|)$，并满足
$\sum_jp_j(u)\mathcal R_j=\mathcal T_u$。在这个固定基中，$\rho_u'$ 也对角；（187.2）因此恰为
$$
I_Q(\rho_u)=\sum_{j:p_j(u)>0}\frac{p_j'(u)^2}{p_j(u)}.
\tag{187.14}
$$
内部零概率处导数为零，所以该等式也适用于支持变化。程序遂属于第186.1节的固定有限经典程序，应用定理186.2即得（187.7）。

对任意精确量子程序，固定输入第181节的均衡端点探针后，整个输出是程序态经过一个与参数无关的 CPTP 映射。SLD 数据处理给出 $I_Q(\rho_u)\ge1/(1-u^2)$，从而
$$
\sup_{u\in J_a}\frac{I_Q(\rho_u)}{B(a,u)}
\ge\sup_{u\in J_a}\frac{1+u-2a^2}{d(1+u)}=1.
$$
最后的上确界由 $u\uparrow1$ 的极限得到；每个区间内的比值都小于一。（187.5）达到这个普遍下界，因此 $R_Q^*(a)=1$。这里最优的是全区间最坏比值，并未把 $B$ 断言为任意内部参数点的最低量子成本。证毕。

**定理 187.3（同一程序的非正交编码与三种信息量）。** 第187.2节的量子程序可由两种固定非正交纯态制备。令
$$
|\chi\rangle=a|0\rangle+\sqrt d\,|1\rangle,
\qquad t(u)=\frac{u-2a^2+1}{2d},
\tag{187.15}
$$
则 $a/(1+a)<t<1$，$|\langle0|\chi\rangle|^2=a^2$，并有
$$
\rho_u=t(u)|0\rangle\langle0|+[1-t(u)]|\chi\rangle\langle\chi|.
\tag{187.16}
$$
如果同时保留指示这两种制备方式的正交经典标签，其 Fisher 信息量为 $B(a,u)/d$；仅保留量子程序时为 $B(a,u)$；当前通道的一次最大可读 SLD 信息量为 $1/(1-u^2)$。三者严格满足
$$
\frac{B(a,u)}d>B(a,u)>\frac1{1-u^2}.
\tag{187.17}
$$
这里比较的是同一参数在三个不同接口中的信息量，不将保留程序中的信息量等同于其全部制备资源。

证明。 （187.16）的右侧矩阵为
$\left(\begin{smallmatrix}t+(1-t)a^2&(1-t)a\sqrt d\\(1-t)a\sqrt d&(1-t)d\end{smallmatrix}\right)$。
代入 $1-t=(1-u)/(2d)$，即还原（187.3）。参数区间给出所述 $t$ 范围。经典制备标签的两个概率为 $t,1-t$，所以其信息量为
$$
I_{\rm label}=\frac{t'^2}{t(1-t)}
=\frac1{(1-u)(1+u-2a^2)}
=\frac Bd.
\tag{187.18}
$$
也可将标签与相应纯态一同保留；由于条件纯态均与参数无关，所得分块态的信息量仍是这个值。丢弃正交标签后得到（187.16），其信息量由（187.5）给出。$0<d<1$ 证明第一项严格下降。

同一处理器以纯程序 $|0\rangle$ 和 $|\chi\rangle$ 分别生成 $\mathcal T_1$ 与 $\mathcal T_{2a^2-1}$；故保留标签的版本正是第184.3节端点二符号模拟的一个实现。最后，第181节给出通道最大可读值，而第184.4节的精确比值为
$$
B(a,u)(1-u^2)
=1+\frac{a^2(1-u)}{1+u-2a^2}>1,
\tag{187.19}
$$
证明（187.17）。

（187.5）给出达到最优最坏相对成本的固定量子处理器。这个极小极大结论并不声称其信息量在每个参数点都最小；对任意精确量子程序，SLD 数据处理及第181节的达到输入仅给出必要下界 $I_Q\ge1/(1-u^2)$。式（187.7）的更强障碍以整条程序族交换为条件，不能移除该条件后用于任意量子程序。证毕。

<a id="entry-724"></a>

## 追加锚（本行以下为增补区）

<a id="section-188"></a>

## 188. 量子程序的逐点下确界、统一等号障碍与秩变化边界

**定义 188.1（逐点设计与局部恒秩设计）。** 固定 $0<a<1$ 和名义点 $u_0\in J_a=(2a-1,1)$。在第187.1节所有有限维固定量子程序中，定义
$$
\mathfrak Q(a,u_0)=\inf I_Q(\rho_{u_0}),\qquad
\mathfrak Q_{\rm reg}(a,u_0)
=\inf_{\operatorname{rank}\rho_u\text{ 在 }u_0\text{ 邻域恒定}}I_Q(\rho_{u_0}).
\tag{188.1}
$$
两种下确界都要求每个候选精确模拟整个 $J_a$，但允许为不同 $u_0$ 选择不同固定处理器及程序曲线。信息量采用（187.2）的点态 SLD 约定。记
$$
I_{r}(u)=\frac1{1-u^2}.
\tag{188.2}
$$
它是第181节同一通道的一次最大可读信息量。以下讨论逐点下确界与同一程序同时达到下界的区别；第187节归一于 $B(a,u)$ 的极小极大值仍为一。

**定理 188.2（恒秩程序也能逼近可读下界）。** 对每个允许的 $a,u_0$，
$$
\mathfrak Q(a,u_0)=\mathfrak Q_{\rm reg}(a,u_0)=I_{r}(u_0).
\tag{188.3}
$$
更具体地，对任意 $0<\lambda<1$，存在一个程序空间维数为十、在 $u_0$ 附近秩恒定的固定程序，精确模拟整个 $J_a$，并满足
$$
I_Q(\rho_{u_0})=\frac{I_{r}(u_0)}\lambda.
\tag{188.4}
$$
因此只要 $I_{r}(u_0)/B(a,u_0)<\lambda<1$，它在设计点的成本就严格低于第187节显式量子比特程序的成本 $B(a,u_0)$。

证明。 第187节的固定探针与数据处理给出所有候选的下界 $I_Q\ge I_{r}$。为构造逼近程序，令
$$
h=\frac{1+u_0}{2},\quad \ell=1-h,\quad q=h-a^2,\quad
\gamma^2=\frac1{16h\ell}=\frac{I_{r}(u_0)}4.
\tag{188.5}
$$
取第181节随参数变化的实环境向量
$$
v_0(u)=(\sqrt{(1+u)/2},\sqrt{(1-u)/2},0),\quad
v_2(u)=(\sqrt{(1+u)/2},-\sqrt{(1-u)/2},0),
$$
$$
v_1(u)=\left(\frac a{\sqrt{(1+u)/2}},0,
\sqrt{1-\frac{a^2}{(1+u)/2}}\right).
\tag{188.6}
$$
它们的 Gram 矩阵为 $F(a,u)$。以下向量与导数均在 $u_0$ 取值，有
$$
\langle v_i,v_i'\rangle=0,\qquad
\|v_0'\|^2=\|v_2'\|^2=\gamma^2,
\qquad
\|v_1'\|^2=\frac{a^2}{16h^2q}<\gamma^2.
\tag{188.7}
$$
最后的不等式等价于 $a^2<h^2$，由 $h>a$ 得到。在四维环境中取单位向量 $e$，与原三维空间正交，并令
$$
w_i=\frac{v_i'}\gamma+
\sqrt{1-\frac{\|v_i'\|^2}{\gamma^2}}\,e.
\tag{188.8}
$$
每对 $(v_i,w_i)$ 正交归一，故固定映射 $V_i|0\rangle=v_i$、$V_i|1\rangle=w_i$ 是等距映射。受数据基控制的等距映射 $\sum_i|i\rangle\langle i|\otimes V_i$ 后接环境迹，定义一个固定处理器。

令 $x=u-u_0$，给该处理器输入纯程序
$$
|\phi_x\rangle=\cos(\gamma x)|0\rangle+\sin(\gamma x)|1\rangle.
\tag{188.9}
$$
输出通道的实相关矩阵记为 $G(x)$。因为 $e$ 与全部 $v_i$ 正交，Gram 矩阵求导给出
$$
G(0)=F_0:=F(a,u_0),\qquad G'(0)=E:=\partial_uF(a,u),
\qquad I_Q(|\phi_x\rangle)=4\gamma^2.
\tag{188.10}
$$
这里 $G$ 为解析的相关矩阵曲线；尚未要求它在零点外等于目标。

固定 $0<\lambda<1$，定义修正矩阵
$$
H(x)=\frac{F_0+xE-\lambda G(x/\lambda)}{1-\lambda}.
\tag{188.11}
$$
则 $H(0)=F_0\succ0$、$H'(0)=0$，且对角恒为一。连续性保证它在零点邻域仍为实正定相关矩阵。

令 $E_1,E_2,E_3$ 为三种实对称非对角坐标矩阵。选取足够小的 $r>0$，使六个固定矩阵 $C_{k,\pm}=F_0\pm rE_k$ 都正定。写
$H(x)-F_0=\sum_{k=1}^3\delta_k(x)E_k$，取
$$
p_{k,\pm}(x)=\frac16\pm\frac{\delta_k(x)}{2r}.
\tag{188.12}
$$
在足够小的邻域，六项概率都严格为正、总和为一，且其相关矩阵平均为 $H(x)$。因为 $\delta_k'(0)=0$，全部概率在零点的导数为零。

在量子比特块与六维经典块的正交直和上，使用程序
$$
\tau_x=\lambda|\phi_{x/\lambda}\rangle\langle\phi_{x/\lambda}|
\ \oplus\ (1-\lambda)\operatorname{diag}(p_{k,\pm}(x)).
\tag{188.13}
$$
固定处理器按块分别执行上述等距处理器及六个 Schur 通道。式（188.11）保证混合后的相关矩阵恰为 $F_0+xE$，所以它在邻域内精确模拟目标。两个块的总权重固定；经典块在零点没有一阶变化，因此其点态信息量为零，而量子块给出
$$
I_Q(\tau_0)=\lambda\frac{4\gamma^2}{\lambda^2}
=\frac{I_{r}(u_0)}\lambda.
\tag{188.14}
$$
该局部程序在整个充分小的邻域内秩恒为七。

取光滑截断函数 $\chi(u)\in[0,1]$，在 $u_0$ 附近恒为一，其支撑紧含于局部程序成立的邻域。以另一个正交量子比特块放置第187节的全区间程序，形成
$\chi(u)\tau_{u-u_0}\oplus[1-\chi(u)]\rho_u^{(187)}$。在局部块未定义的区域将其加权块置零；截断函数在该区域的邻域已经为零，故整条态曲线光滑。固定处理器按块执行相应通道，两分支在实际使用处都等于目标，因而在全部 $J_a$ 精确模拟。总维数为 $2+6+2=10$；设计点附近保持（188.14）与恒秩性质。令 $\lambda\uparrow1$，结合普遍下界，证明（188.3）。证毕。

**定理 188.3（同一量子程序不可能在开区间处处达到可读下界）。** 任何第187.1节的有限维固定程序，都不存在非空开区间 $K\subseteq J_a$，使
$$
I_Q(\rho_u)=I_{r}(u)\qquad\text{对所有 }u\in K.
\tag{188.15}
$$
该断言不要求程序族交换，也不要求其秩恒定。

证明。 固定第181节的均衡 $02$ 输入。令 $|\pm\rangle=(|0\rangle\pm|2\rangle)/\sqrt2$，取整个输出空间上的二元 POVM
$M_+=|+\rangle\langle+|+|1\rangle\langle1|$、$M_-=|-\rangle\langle-|$，使两效应之和为恒等算符。目标输出的中间基态权重为零，故测量得到概率
$h(u)=(1+u)/2$、$\ell(u)=(1-u)/2$。该试验连同固定处理器，在程序上诱导一个不依赖参数的二元 POVM，其经典信息量恰为 $I_{r}$。

使用固定的 Naimark 等距嵌入 $J$，将该 POVM 表为更大有限维程序空间上的正交投影 $P_+,P_-$，满足 $P_++P_-=I$。嵌入态 $\sigma_u=J\rho_uJ^\dagger$ 的 SLD 信息量不变。为使处理器在整个扩大的程序空间上有定义，取任一固定原程序态 $\rho_*$，使用 CPTP 映射
$$
\mathcal D(\tau)=J^\dagger\tau J+
\operatorname{Tr}[(I-JJ^\dagger)\tau]\rho_*.
\tag{188.16}
$$
它在嵌入态上还原原程序。将原处理器与 $\mathcal D$ 组合，就得到固定扩展处理器，仍对任意数据输入精确生成同一通道。

现假设（188.15）成立。SLD 测量信息不等式及其等号条件的原始框架见 Braunstein、Caves，*Statistical Distance and the Geometry of Quantum States*，Phys. Rev. Lett. **72**, 3439（1994），DOI:10.1103/PhysRevLett.72.3439，式（24）—（26）。这里直接保留支持上的平方根因子，以免将满秩简化条件用于秩亏态。

对每个 $u\in K$，双侧非负性使 $\sigma_u'$ 在 $\sigma_u$ 的核上的压缩为零，故可取有限 Hermitian SLD $L_u$，满足
$\sigma_u'=(L_u\sigma_u+\sigma_uL_u)/2$。对 $j\in\{+,-\}$，设
$A_j=P_j\sqrt{\sigma_u}$、$B_j=P_jL_u\sqrt{\sigma_u}$。在 Hilbert–Schmidt 内积下，
$$
\|A_j\|_2^2=p_j,
\quad\operatorname{Re}\langle A_j,B_j\rangle=p_j',
\quad\sum_j\|B_j\|_2^2=I_Q(\sigma_u).
\tag{188.17}
$$
Cauchy–Schwarz 给出 $(p_j')^2/p_j\le\|B_j\|_2^2$。所有 $p_j$ 严格为正；若总和达到等号，则每项都达到等号，并有 $B_j=s_jA_j$，其中
$$
s_+=\frac1{2h},\qquad s_-=-\frac1{2\ell}.
\tag{188.18}
$$
因此，令 $D_u=s_+P_++s_-P_-$，相加得到
$L_u\sqrt{\sigma_u}=D_u\sqrt{\sigma_u}$。右乘平方根并取伴随，遂得
$$
\sigma_u'=\frac12(D_u\sigma_u+\sigma_uD_u).
\tag{188.19}
$$
这个论证不需要逆转 $\sigma_u$，所以也适用于非满秩情形。

令 $K_u=\sqrt h\,P_++\sqrt\ell\,P_-$。它在区间内可逆，且 $K_u'=D_uK_u/2$；（188.19）表明 $K_u^{-1}\sigma_uK_u^{-1}$ 的导数为零。故存在固定的正半定矩阵 $A$，使 $\sigma_u=K_uAK_u$。写
$$
A_+=P_+AP_+,\quad A_-=P_-AP_-,\quad C=P_+AP_-,
$$
$$
\sigma_u=hA_++\ell A_-+\sqrt{h\ell}(C+C^\dagger).
\tag{188.20}
$$
由测量概率 $\operatorname{Tr}(P_+\sigma_u)=h$、$\operatorname{Tr}(P_-\sigma_u)=\ell$，可得 $\operatorname{Tr}A_+=\operatorname{Tr}A_-=1$，所以两者都是固定密度矩阵。

将（188.20）送入固定扩展处理器，对所有数据输入同时得到通道恒等式
$$
\mathcal T_u=h\mathcal R_++\ell\mathcal R_-
+\sqrt{h\ell}\,\mathcal S,
\tag{188.21}
$$
其中 $\mathcal R_\pm$ 是以 $A_\pm$ 为程序的固定 CPTP 通道，$\mathcal S$ 是以交叉项 $C+C^\dagger$ 定义的固定线性映射。目标 $\mathcal T_u$ 对 $u$ 仿射，而 $1,u,\sqrt{1-u^2}$ 在任何非空开区间上线性无关。故（188.21）迫使
$\mathcal S=0$、$\mathcal R_+=\mathcal T_1$、$\mathcal R_-=\mathcal T_{-1}$。这里后两个等式只是由仿射系数决定，不假定程序在端点存在。

但 $\mathcal T_{-1}$ 不是完全正映射。事实上，对 $n=(1,-2a,1)^{\mathsf T}$，
$$
n^{\mathsf T}F(a,-1)n=-4a^2<0.
\tag{188.22}
$$
将该 Schur 乘子作用于均匀相干输入 $\frac13\sum_{i,j}|i\rangle\langle j|$，输出正是 $F(a,-1)/3$，不是正半定矩阵。这已经违背正性，与 $\mathcal R_-$ 为 CPTP 矛盾。证毕。

**定理 188.4（秩变化允许点态达到，但不消除邻近成本）。** 若使用（187.2）的点态信息量约定，则对任意 $a,u_0$，存在一个有限维光滑固定程序，精确模拟全部 $J_a$，并在设计点满足 $I_Q(\rho_{u_0})=I_{r}(u_0)$。可以使它在充分小的去心邻域满足
$$
\lim_{u\to u_0,\ u\ne u_0}I_Q(\rho_u)
=I_{r}(u_0)+4k,
\qquad k>0.
\tag{188.23}
$$
因此这种达到不属于定理188.2的局部恒秩逼近，不提供开区间上平滑达到下界的程序。

证明。 沿用（188.9）—（188.10）的解析相关矩阵 $G(x)$。取足够大的常数 $k>0$，令 $\epsilon(x)=kx^2$，并在零点外定义
$$
H(x)=G(x)+\frac{F_0+xE-G(x)}{kx^2}.
\tag{188.24}
$$
由于 $G(0)=F_0$、$G'(0)=E$，该式在零点有解析延拓，且
$$
H(0)=F_0-\frac{G''(0)}{2k}.
\tag{188.25}
$$
取 $k$ 足够大即可使它正定；$H$ 的对角仍恒为一，因此它在零点邻域为实正定相关矩阵。用以 $H(0)$ 为中心的六个固定矩阵 $H(0)\pm rE_j$，照（188.12）构造严格正的解析经典概率 $p_j(x)$，精确实现 $H(x)$。

在足够小的邻域，$0\le\epsilon<1$，程序
$$
\tau_x=[1-kx^2]|\phi_x\rangle\langle\phi_x|
\ \oplus\ kx^2\operatorname{diag}(p_j(x))
\tag{188.26}
$$
精确生成 $(1-\epsilon)G+\epsilon H=F_0+xE$。在 $x=0$，经典块及其导数都为零，量子块的一阶切向量与 $|\phi_x\rangle$ 相同，所以（187.2）给出 $I_Q(\tau_0)=4\gamma^2=I_{r}(u_0)$。

在去心邻域，直和各块的 SLD 信息量分解为
$$
I_Q(\tau_x)
=(1-kx^2)4\gamma^2+kx^2I_{c}(x)
+\frac{4k}{1-kx^2},
\tag{188.27}
$$
其中 $I_{c}$ 是严格正的解析经典概率曲线的信息量，在零点附近有界。取极限即得（188.23）。再照定理188.2用光滑截断函数接到第187节的全区间程序，保持设计点附近全部性质。

程序在设计点秩为一，在充分小的去心邻域秩为七。点态 SLD 与连续延拓的差别符合既有的秩变化边界：Šafránek，*Discontinuities of the quantum Fisher information and the Bures metric*，Phys. Rev. A **95**, 052320（2017），DOI:10.1103/PhysRevA.95.052320，定理1式（13）对 $C^2$ 态族给出 $H_c=H+2\sum_{p_j=0}p_j''$。在当前构造中，新出现的六个本征值之和为 $kx^2$，所以 Bures 信息在设计点等于 $I_{r}(u_0)+4k$，并未降到点态 SLD 的值。证毕。

<a id="entry-726"></a>

## 追加锚（本行以下为增补区）

<a id="section-189"></a>

## 189. 固定量子程序相对于可读信息的维数无关正差距

**定义 189.1（以可读信息归一的统一成本）。** 固定 $0<a<1$，仍以 $J_a=(2a-1,1)$ 为参数区间。对第187.1节的有限维固定量子程序，令
$$
\widehat R(\mathcal G,\rho)
=\sup_{u\in J_a}\frac{I_Q(\rho_u)}{I_r(u)},
\qquad I_r(u)=\frac1{1-u^2},
\qquad
\widehat R_Q^*(a)=\inf_{(\mathcal G,\rho)}\widehat R(\mathcal G,\rho).
\tag{189.1}
$$
每个候选都必须精确模拟全部 $J_a$。下确界允许任意有限程序维数，信息量仍采用（187.2）的点态 SLD 约定。这里的归一分母是实验可读信息 $I_r$，与第187节以逐点经典生成成本 $B$ 为分母的 $R_Q^*$ 不同。

取三个内部参数值
$$
u_- =\frac{3a-1}{2},\qquad u_0=a,\qquad u_+=\frac{1+a}{2},
\qquad h_i=\frac{1+u_i}{2},\quad\ell_i=1-h_i,
\tag{189.2}
$$
并定义
$$
M_a=\begin{pmatrix}
h_-&h_0&h_+\\
\ell_-&\ell_0&\ell_+\\
\sqrt{h_-\ell_-}&\sqrt{h_0\ell_0}&\sqrt{h_+\ell_+}
\end{pmatrix},
\qquad
\begin{pmatrix}\alpha_-\\\alpha_0\\\alpha_+\end{pmatrix}
=M_a^{-1}\begin{pmatrix}0\\1\\0\end{pmatrix}.
\tag{189.3}
$$
函数 $\sqrt{1-u^2}$ 严格凹，故三个点在其图上不共线；结合前两行张成常数与 $u$，可知 $M_a$ 可逆。令
$$
S_a=|\alpha_-|+|\alpha_+|,
\qquad \mu_a=\frac{\sqrt{1+8a^2}-1}{6},
\qquad
\Delta(a)=\frac{\mu_a^2(1-u_+^2)}{S_a^2}.
\tag{189.4}
$$
$S_a>0$：否则（189.3）前两行之和迫使 $\alpha_0=1$，而第一行又要求 $h_0=0$，矛盾。因此 $\Delta(a)>0$，且只依赖已知参数 $a$。

**定理 189.2（任意有限维量子程序都有统一正额外成本）。** 对所有 $0<a<1$，
$$
1+\Delta(a)\le\widehat R_Q^*(a)\le1+a.
\tag{189.5}
$$
特别地，即使允许程序维数沿候选序列不断增加，也不能使整区间的最坏成本比趋于一。这比第188.3节的不能处处达到等号更强，同时不改变第188节允许随名义点重新设计时的逐点下确界。

证明。 任取一个精确程序。沿第188.3节，固定均衡 $02$ 输入及完整的二元输出 POVM，用固定 Naimark 嵌入把诱导测量写成互补投影 $P_+,P_-$。将程序态记为 $\sigma_u$；其点态 SLD 信息量保持不变。采用（188.16）的 CPTP 解码，将处理器扩展到整个嵌入程序空间。于是它不仅能处理 $\sigma_u$，还可以处理下文构造的其他密度矩阵。

令 $h=(1+u)/2$、$\ell=(1-u)/2$，并设
$$
D_u=\frac{P_+}{2h}-\frac{P_-}{2\ell},
\qquad
\mathcal E_u=\sigma_u'-\frac12(D_u\sigma_u+\sigma_uD_u).
\tag{189.6}
$$
对任一 Hermitian SLD $L_u$，第188节所用测量信息不等式具有精确剩余平方
$$
\|(L_u-D_u)\sqrt{\sigma_u}\|_2^2
=I_Q(\sigma_u)-I_r(u).
\tag{189.7}
$$
事实上，$\operatorname{Tr}(\sigma_uD_u^2)=I_r$，而
$\operatorname{Re}\operatorname{Tr}(\sigma_uD_uL_u)
=\sum_{j=\pm}(p_j'/p_j)p_j'=I_r$；展开平方即得（189.7）。这沿用 Braunstein–Caves 测量信息不等式的支持敏感形式，出处与边界见第188.3节。

记 $Z_u=(L_u-D_u)\sqrt{\sigma_u}$，则
$$
\mathcal E_u=\frac12(Z_u\sqrt{\sigma_u}+\sqrt{\sigma_u}Z_u^\dagger),
\qquad
\|\mathcal E_u\|_1\le\|Z_u\|_2
=\sqrt{I_Q(\sigma_u)-I_r(u)}.
\tag{189.8}
$$
这里使用 Schatten 范数的 Cauchy–Schwarz 不等式及 $\|\sqrt{\sigma_u}\|_2=1$。$\mathcal E_u$ 由 $C^1$ 态曲线和光滑的 $D_u$ 直接定义，因而连续；证明没有要求所选 $L_u$ 连续，也没有对它求导。

令
$$
K_u=\sqrt h\,P_++\sqrt\ell\,P_-,\qquad
\tau_u=K_u^{-1}\sigma_uK_u^{-1}.
\tag{189.9}
$$
由 $K_u'=D_uK_u/2$ 及（189.6），
$$
\tau_u'=K_u^{-1}\mathcal E_uK_u^{-1},
\qquad
\|\tau_u'\|_1
\le\frac{\sqrt{I_Q(\sigma_u)-I_r(u)}}{\min(h,\ell)}.
\tag{189.10}
$$
这把信息量超出可读值的部分，转成同一程序曲线在固定表示下的变化界。

在参考点 $u_0=a$ 令 $A=\tau_{u_0}$，并构造
$$
\widehat\sigma_u=K_uAK_u
=hA_++\ell A_-+\sqrt{h\ell}(C+C^\dagger),
\quad A_\pm=P_\pm AP_\pm,\quad C=P_+AP_-.
\tag{189.11}
$$
$A\succeq0$，而参考点的测量概率保证 $\operatorname{Tr}A_+=\operatorname{Tr}A_-=1$。因此 $\widehat\sigma_u$ 对所有 $-1<u<1$ 都是密度矩阵，且 $\widehat\sigma_{u_0}=\sigma_{u_0}$。

记 $R=\widehat R(\mathcal G,\rho)$。若 $R=\infty$，下界自动成立；否则数据处理给出 $R\ge1$。在闭区间 $[u_-,u_+]$ 上，
$$
\min(h,\ell)\ge\frac{1-a}{4},\qquad
I_r(u)\le\frac1{1-u_+^2},\qquad
|u_\pm-u_0|=\frac{1-a}{2}.
\tag{189.12}
$$
第二式使用 $|u_-|\le u_+$。将（189.10）在参考点与两端点之间积分，再使用 $\|K_u\|_\infty^2\le1$，得到
$$
\|\sigma_{u_i}-\widehat\sigma_{u_i}\|_1
\le\frac{2}{\sqrt{1-u_+^2}}\sqrt{R-1}
\quad(i\in\{-,+\});
\qquad
\|\sigma_{u_0}-\widehat\sigma_{u_0}\|_1=0.
\tag{189.13}
$$
只对连续的 $\mathcal E_u$ 与 $\tau_u'$ 使用积分，所以该界允许程序在区间内发生秩变化。

现在向同一个固定扩展处理器输入另一个数据态
$\omega=|s\rangle\langle s|$，其中 $|s\rangle=(|0\rangle+|1\rangle+|2\rangle)/\sqrt3$。实际程序给出的输出为
$X_u=F(a,u)/3$；参考程序给出的输出具有形式
$$
\widehat X_u=hX_++\ell X_-+\sqrt{h\ell}\,Y,
\tag{189.14}
$$
其中 $X_+,X_-$ 是以密度矩阵 $A_+,A_-$ 为程序得到的密度矩阵，$Y$ 是固定 Hermitian 交叉项的输出。固定输入后的处理器为 CPTP，故迹范数收缩把（189.13）原样传给 $\|X_{u_i}-\widehat X_{u_i}\|_1$。两个试验分别使用同一程序态族与同一固定处理器：前一个给出测量概率与信息剩余，后一个检验生成通道的正性。

由（189.3），有
$$
\sum_i\alpha_i=1,\qquad\sum_i\alpha_i u_i=-1,
\qquad\sum_i\alpha_i\sqrt{h_i\ell_i}=0.
\tag{189.15}
$$
因此
$$
\sum_i\alpha_i X_{u_i}=\frac13F(a,-1),
\qquad
\sum_i\alpha_i\widehat X_{u_i}=X_-.
\tag{189.16}
$$
这些系数只用于线性恒等式，允许为负，不将它们作为混合概率。

矩阵 $F(a,-1)$ 在反对称端点方向的特征值为二，在对称端点与中间基态张成的子空间上具有矩阵 $\left(\begin{smallmatrix}0&\sqrt2a\\\sqrt2a&1\end{smallmatrix}\right)$。因此 $F(a,-1)/3$ 恰有一个负特征值 $-\mu_a$。令 $\Pi$ 为对应的一维谱投影，则
$$
\operatorname{Tr}\!\left(\Pi\frac{F(a,-1)}3\right)=-\mu_a,
\qquad\operatorname{Tr}(\Pi X_-)\ge0.
\tag{189.17}
$$
两个矩阵都具有迹一，所以差为无迹 Hermitian 矩阵。对这种矩阵 $H$，任一效应 $0\le\Pi\le I$ 都满足 $|\operatorname{Tr}(\Pi H)|\le\|H\|_1/2$。于是（189.17）、（189.16）和三角不等式给出
$$
2\mu_a\le\left\|\frac13F(a,-1)-X_-\right\|_1
\le\sum_i|\alpha_i|\,\|X_{u_i}-\widehat X_{u_i}\|_1
\le\frac{2S_a}{\sqrt{1-u_+^2}}\sqrt{R-1}.
\tag{189.18}
$$
移项平方即得 $R\ge1+\Delta(a)$。其常数与程序维数、所选 Naimark 扩张及处理器无关，故可以对全部有限维程序取下确界。

最后，第187节显式量子比特程序在全区间具有 $I_Q=B$，且
$$
\frac{B(a,u)}{I_r(u)}
=\frac{(1-a^2)(1+u)}{1+u-2a^2},
\qquad
\sup_{u\in J_a}\frac{B(a,u)}{I_r(u)}=1+a.
\tag{189.19}
$$
该比值随 $u$ 严格递减，其上确界来自 $u\downarrow2a-1$，证明（189.5）的上界。上述两界未确定 $\widehat R_Q^*(a)$ 的精确值或达到其下确界的程序。证毕。

<a id="entry-728"></a>

## 追加锚（本行以下为增补区）

<a id="section-190"></a>

## 190. 全区间精确程序的二维障碍与三维纯态逐点达到

**定义 190.1（程序的联合维数与指定点成本）。** 固定 $0<a<1$，令
$$
J_a=(2a-1,1),\qquad
F(a,u)=\begin{pmatrix}1&a&u\\a&1&a\\u&a&1\end{pmatrix},\qquad
\mathcal T_u=\mathcal S_{F(a,u)}.
\tag{190.1}
$$
沿用第187.1节的固定 CPTP 处理器、全区间精确性与点态 SLD 信息约定。程序曲线的联合支持空间及其维数定义为
$$
\mathcal H_{\rm joint}=\operatorname{span}\!\left(\bigcup_{u\in J_a}\operatorname{ran}\rho_u\right),
\qquad d_{\rm joint}=\dim\mathcal H_{\rm joint}.
\tag{190.2}
$$
它计算整族程序共同需要的固定空间，不等于单个 $\rho_u$ 的秩。对指定的 $u_0\in J_a$，比较不同固定处理器及其全区间程序在 $u_0$ 的信息成本；处理器可以随设计点 $u_0$ 改变，但一旦选定，就必须对全部 $u\in J_a$ 使用同一个处理器。记
$$
I_r(u)=\frac1{1-u^2},\qquad
B(a,u)=\frac{1-a^2}{(1-u)(1+u-2a^2)}.
\tag{190.3}
$$

**定理 190.2（任意固定量子比特处理器的逐点下界）。** 任意满足第187.1节条件、程序空间维数为二的固定处理器，都满足
$$
I_Q(\rho_u)\ge B(a,u)\qquad(u\in J_a).
\tag{190.4}
$$
该结论允许复量子比特态、任意固定 CPTP 处理器及 $C^1$ 程序曲线的秩变化。第187.2节的处理器在全区间同时达到（190.4），因此 $B$ 是该二维类中的逐点最小值。

证明。 写 $\rho_u=(I+r(u)\cdot\sigma)/2$。由处理器对程序输入的线性性，诱导信号映射具有形式
$$
\Phi_r=\Phi_0+\mathcal Lr,
\tag{190.5}
$$
其中 $\mathcal L$ 是从 $\mathbb R^3$ 到保持 Hermitian 性的信号映射实向量空间的线性映射。全区间精确性给出 $\mathcal Lr(u)=\mathcal T_u-\Phi_0$。右侧是非恒定仿射直线，在两个不同参数处有原像，故对全部实数参数都有原像。令 $N=\ker\mathcal L$；其唯一最小 Euclidean 范数原像为
$$
\bar r(u)=c+uv,\qquad c,v\in N^\perp,\quad v\ne0.
\tag{190.6}
$$
于是 $r=\bar r+z$，其中 $z,z'\in N$。对 $u\in J_a$，$|\bar r|\le|r|\le1$，所以 $\bar\rho_u=(I+\bar r(u)\cdot\sigma)/2$ 也是程序态，并经同一处理器给出 $\mathcal T_u$。这是另一条合法制备曲线，不将到 $N^\perp$ 的正交投影宣称为量子通道。

先比较两条曲线的信息量。令
$$
A=\bar r\cdot v,\qquad \beta=1-|\bar r|^2.
\tag{190.7}
$$
在 $J_a$ 内有 $\beta>0$：非恒定仿射直线若在内部参数处接触单位球面，就不能在该参数的两侧仍处于闭球内。若实际程序为混态，记 $q=|z|^2<\beta$；由量子比特 SLD 公式和正交分解，
$$
I_Q(\rho_u)=|v|^2+|z'|^2+\frac{(A+z\cdot z')^2}{\beta-q},
\qquad
I_Q(\bar\rho_u)=|v|^2+\frac{A^2}{\beta}.
\tag{190.8}
$$
取 $w=z'+Az/\beta$，直接完成平方得到
$$
I_Q(\rho_u)-I_Q(\bar\rho_u)
=|w|^2+\frac{(z\cdot w)^2}{\beta-q}\ge0.
\tag{190.9}
$$
若实际程序在该点为纯态，两侧的正性及可微性迫使 $r\cdot r'=0$。点态 SLD 公式给出 $I_Q(\rho_u)=|r'|^2$；此时 $|z|^2=\beta$、$z\cdot z'=-A$，故
$$
I_Q(\rho_u)=|v|^2+|z'|^2
\ge|v|^2+\frac{A^2}{\beta}=I_Q(\bar\rho_u).
\tag{190.10}
$$
所以最小范数制备的信息量不超过实际程序的信息量，包括实际程序发生秩变化的点。这里使用（187.2）的点态值，没有将它替换为邻近 Bures 信息的极限；这一约定的区别见 Šafránek，Phys. Rev. A **95**, 052320（2017），DOI:10.1103/PhysRevA.95.052320，式（2）—（4）及第188.4节。

仿射直线 $\bar r(u)$ 与 Bloch 闭球相交于一个有限非退化弦，对应参数区间 $[b_-,b_+]$，两端程序 $\rho_-,\rho_+$ 为不同纯态。恒等式 $\Phi_{\bar r(u)}=\mathcal T_u$ 对全部实数 $u$ 成立，故弦上每个物理态都生成 $\mathcal T_u$。矩阵 $F(a,u)$ 的反对称端点特征值为 $1-u$，对称块为
$$
\begin{pmatrix}1+u&\sqrt2a\\\sqrt2a&1\end{pmatrix}.
$$
因此 $\mathcal T_u$ 的完整 CP 参数区间为 $[2a^2-1,1]$。弦包含整个 $J_a$，故
$$
b_+=1,\qquad 2a^2-1\le b_-\le2a-1.
\tag{190.11}
$$
这里没有要求原程序曲线在端点收敛；端点程序由仿射直线本身提供。

令 $b=b_-$、$s^2=\operatorname{Tr}(\rho_+\rho_-)<1$。弦上程序是两个纯态的仿射混合，
$$
\bar\rho_u=t\rho_++(1-t)\rho_-,\qquad
 t=\frac{u-b}{1-b},\qquad
I_Q(\bar\rho_u)=\frac{1-s^2}{(u-b)(1-u)}.
\tag{190.12}
$$
最后一式可由 $1-|\bar r|^2=4(1-s^2)t(1-t)$ 代入量子比特公式直接得到，包含正交端点的情形。

固定均衡 $02$ 输入 $|+\rangle=(|0\rangle+|2\rangle)/\sqrt2$。程序到输出的同一个 CPTP 映射将 $\rho_+$ 送到 $|+\rangle\langle+|$，将 $\rho_-$ 送到
$$
\frac{1+b}{2}|+\rangle\langle+|+
\frac{1-b}{2}|-\rangle\langle-|,
\qquad | -\rangle=\frac{|0\rangle-|2\rangle}{\sqrt2}.
$$
采用平方保真度 $\mathsf F(\rho,\eta)=(\operatorname{Tr}\sqrt{\sqrt\rho\eta\sqrt\rho})^2$，CPTP 单调性给出 $s^2\le(1+b)/2$。于是
$$
I_Q(\rho_u)\ge\frac{1-b}{2(u-b)(1-u)}
\ge\frac{1-a^2}{(1-u)(1+u-2a^2)}.
\tag{190.13}
$$
第二步使用 $b\ge2a^2-1$ 及
$\partial_b[(1-b)/(2(u-b)(1-u))]=1/[2(u-b)^2]>0$。第187.2节给出达到，证毕。

此推导使用整个区间上趋近 $u=1$ 的精确性来固定弦的上端点。它不对仅匹配单点值及一阶导数的局部切向程序断言同一下界。固定程序依赖的线性框架见 Hillery、Ziman、Bužek，Phys. Rev. A **66**, 042302（2002），DOI:10.1103/PhysRevA.66.042302，第II.B节式（2.12）；保真度数据处理及程序信息界的背景见 Pirandola、Lupo，Phys. Rev. Lett. **118**, 100502（2017），DOI:10.1103/PhysRevLett.118.100502，arXiv:1609.02160v3 补充材料式（37）—（40）。本条的弦端点约束与 $B$ 下界由上述当前通道族的计算给出。

**定理 190.3（三维纯态在任意设计点规则达到可读下界）。** 对每个 $u_0\in J_a$，存在一个固定处理器与一条 $C^\infty$ 的三维纯程序态曲线，精确生成全部 $\mathcal T_u$，并满足
$$
I_Q(\rho_{u_0})=I_r(u_0).
\tag{190.14}
$$
该程序在整个 $J_a$ 上秩恒为一。

证明。 写 $h=(1+u)/2\in(a,1)$、$\ell=1-h$，以及 $h_0=(1+u_0)/2$、$\ell_0=1-h_0$。以下常数只依赖 $a,u_0$：
$$
A_0=\frac{au_0}{h_0},\qquad B_0=2a\sqrt{\frac{\ell_0}{h_0}},\qquad
s=1-A_0^2-B_0^2=1-\frac{a^2}{h_0^2}>0,
\tag{190.15}
$$
$$
c=\sqrt{\frac a{1-a}},\qquad
\delta=\frac{(1-a)s}{s+aB_0^2},\qquad
A_2=1-\delta,\qquad B_2=\delta c.
\tag{190.16}
$$
因为 $B_0>0$，有 $0<\delta<1-a$，从而 $A_2>a$、$B_2>0$。定义
$$
K=\begin{pmatrix}A_0&0&B_0\\0&A_2&B_2\\0&0&0\end{pmatrix},
\qquad Z=\operatorname{diag}(1,1,-1).
\tag{190.17}
$$
$K$ 是严格压缩算子。事实上，$I-KK^\dagger$ 的第三个对角块为一，其前两个坐标上的块为
$$
\begin{pmatrix}
s&-B_0\delta c\\
-B_0\delta c&2\delta-\delta^2/(1-a)
\end{pmatrix}.
\tag{190.18}
$$
左上元为正，而行列式恰为
$$
\delta\left[2s-\frac{\delta(s+aB_0^2)}{1-a}\right]=\delta s>0.
$$
所以 $I-KK^\dagger\succ0$，亦有 $I-K^\dagger K\succ0$。

取三个从 $\mathbb C^3$ 到 $\mathbb C^6$ 的等距映射
$$
W_0=\begin{pmatrix}I\\0\end{pmatrix},\qquad
W_2=\begin{pmatrix}Z\\0\end{pmatrix},\qquad
W_1=\begin{pmatrix}K\\\sqrt{I-K^\dagger K}\end{pmatrix}.
\tag{190.19}
$$
信号控制的等距映射 $V=\sum_{i=0}^2|i\rangle\langle i|\otimes W_i$，随后对六维环境取迹，定义一个固定 CPTP 处理器。用实纯程序向量
$$
\psi_u=
\begin{pmatrix}\sqrt h\cos\theta(h)\\\sqrt h\sin\theta(h)\\\sqrt\ell\end{pmatrix},
\qquad \rho_u=|\psi_u\rangle\langle\psi_u|.
\tag{190.20}
$$
诱导 Schur 系数为 $C_{ij}=\langle W_j\psi_u,W_i\psi_u\rangle$。由于 $ZK=K$、$\psi_u$ 为实向量，
$$
C_{02}=u,\qquad C_{01}=C_{12}=f(h,\theta),
$$
$$
f(h,\theta)=h(A_0\cos^2\theta+A_2\sin^2\theta)
+\sqrt{h(1-h)}(B_0\cos\theta+B_2\sin\theta).
\tag{190.21}
$$
故只需全局光滑地选取 $0\le\theta(h)<\pi/2$，使 $f(h,\theta(h))=a$。

先看两端角度。$f(h,0)=hA_0+B_0\sqrt{h(1-h)}$ 关于 $h$ 严格凹；由（190.15），
$$
f(h_0,0)=a,\qquad f_h(h_0,0)=0.
\tag{190.22}
$$
因此 $f(h,0)\le a$，等号恰在 $h=h_0$。另一端函数 $f(h,\pi/2)$ 关于 $h$ 凹，且在闭区间 $[a,1]$ 的端点满足
$$
f(a,\pi/2)=a,\qquad f(1,\pi/2)=A_2>a.
\tag{190.23}
$$
由凹性，它在每个 $h\in(a,1)$ 严格大于 $a$。

对固定的内部 $h$，在 $0<\theta<\pi/2$ 有
$$
\frac{f_\theta(h,\theta)}{\sin\theta\cos\theta}
=2h(A_2-A_0)+\sqrt{h(1-h)}
\left(\frac{B_2}{\sin\theta}-\frac{B_0}{\cos\theta}\right).
\tag{190.24}
$$
右侧严格递减，并从正无穷趋向负无穷，所以 $f$ 随角度先严格增、后严格减，只有一个最大点。结合（190.22）—（190.23），方程 $f=a$ 在 $[0,\pi/2)$ 恰有一个根，且总位于严格上升段；下降段的值不小于其右端值，而该值严格大于 $a$。在 $h=h_0$ 时这个根为零，且
$$
f_\theta(h_0,0)=\sqrt{h_0\ell_0}\,B_2>0.
\tag{190.25}
$$
因此隐函数定理及根的唯一性给出整个 $(a,1)$ 上的光滑函数 $\theta(h)$，并且
$$
\theta(h_0)=0,\qquad
\theta'(h_0)=-\frac{f_h(h_0,0)}{f_\theta(h_0,0)}=0.
\tag{190.26}
$$
这既保证处理器在整个 $J_a$ 精确生成目标通道，也保证设计点的角度运动没有一阶贡献。

最后，归一实向量满足 $\langle\psi_u,\psi_u'\rangle=0$。径向变化与角度变化正交，直接微分（190.20）得
$$
I_Q(\rho_u)=4\|\psi_u'\|^2
=\frac1{4h\ell}+4h\left(\frac{d\theta}{du}\right)^2
=I_r(u)+4h\left(\frac{d\theta}{du}\right)^2.
\tag{190.27}
$$
由（190.26），在 $u=u_0$ 恰达到 $I_r(u_0)$。程序为全区间光滑纯态，所以这里没有第188.4节由程序秩变化产生的孤立 SLD 跳变。证毕。

**定理 190.4（规则逐点最优的最小联合程序维数恰为三）。** 在每个指定的 $u_0\in J_a$，所有有限维固定处理器的全区间精确程序，其点态信息成本最小值为 $I_r(u_0)$；即使要求程序在设计点附近秩恒定，该最小值仍被达到。达到它所需的最小联合程序维数恰为三。

证明。 第181节的均衡 $02$ 输入及二元输出测量，在任意精确程序上诱导信息量为 $I_r(u)$ 的固定测量，故测量信息不等式给出 $I_Q(\rho_u)\ge I_r(u)$。第190.3节提供三维且全区间秩恒定的达到。另一方面，
$$
\frac{B(a,u)}{I_r(u)}-1
=\frac{a^2(1-u)}{1+u-2a^2}>0\qquad(u\in J_a).
\tag{190.28}
$$
若联合支持包含于某个固定二维空间，将程序输入限制到该空间仍给出一个固定 CPTP 处理器，第190.2节就排除了达到 $I_r$；一维程序只能产生恒定通道，也不可能精确生成本族。因此最小联合维数为三，第190.3节的纯态曲线必张成整个三维程序空间。

本结论将第188.2节的规则逐点下确界加强为三维纯态达到，而不改变其原有构造。这里的量词是对每个设计点可选择一个处理器；同一个处理器在其余参数处的额外成本由（190.27）保留。第188.3节的开区间等号障碍及第189.2节的统一正差距仍适用，故三维逐点达到不蕴含全区间同时达到。证毕。

<a id="entry-730"></a>

## 追加锚（本行以下为增补区）

<a id="section-191"></a>

## 191. 局部精确最优的混态节省与纯态二维障碍

**定义 191.1（局部精确程序及规则达到）。** 固定 $0<a<1$、$t\in J_a=(2a-1,1)$。局部精确程序由一个包含 $t$ 的开区间 $U\subset J_a$、一个固定 CPTP 处理器和一条定义在 $U$ 上的 $C^1$ 程序曲线组成，要求
$$
\mathcal G(\omega\otimes\rho_u)=\mathcal T_u(\omega)
\qquad(u\in U)
\tag{191.1}
$$
对全部信号输入成立。称在 $t$ 规则达到，若程序秩在 $t$ 的某个邻域恒定且 $I_Q(\rho_t)=I_r(t)$，其中 $I_r(u)=1/(1-u^2)$。这是在一个真实开区间内精确生成通道的要求，比仅匹配 $\mathcal T_t$ 与其一阶导数强；其覆盖域又小于第190节要求的整个 $J_a$。

量子估计文献中的局部模拟可采用切向意义：Kołodyński、Demkowicz-Dobrzański，*Efficient tools for quantum metrology with uncorrelated noise*，New J. Phys. **15**, 073043（2013），DOI:10.1088/1367-2630/15/7/073043，arXiv:1303.7271v2，第4.1.2节与附录D式（D.1），允许通道等式具有 $O((u-t)^2)$ 余项。本节（191.1）要求开区间内严格相等，以下二维构造与纯态障碍均针对这个更强条件。

**定理 191.2（局部二维满秩程序精确达到）。** 对每个 $t\in J_a$，存在一个二维满秩的解析局部精确程序，在 $t$ 达到 $I_r(t)$。

证明。 令 $h_0=(1+t)/2$、$\ell_0=1-h_0$，并取
$$
A_0=\frac{at}{h_0},\qquad B_0=2a\sqrt{\frac{\ell_0}{h_0}},\qquad
\frac{B_0}{\sqrt{1-A_0^2}}<\lambda<1.
\tag{191.2}
$$
由 $h_0>a$ 得 $A_0^2+B_0^2=a^2/h_0^2<1$，所以这个 $\lambda$ 区间非空。定义
$$
\beta=\frac{B_0}{\lambda},\qquad
K=\begin{pmatrix}A_0&\beta\\0&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1).
\tag{191.3}
$$
$A_0^2+\beta^2<1$，故 $K$ 是严格压缩算子。与第190节相同，从二维程序空间到四维环境取等距映射
$$
W_0=\begin{pmatrix}I\\0\end{pmatrix},\qquad
W_2=\begin{pmatrix}Z\\0\end{pmatrix},\qquad
W_1=\begin{pmatrix}K\\\sqrt{I-K^\dagger K}\end{pmatrix}.
\tag{191.4}
$$
用信号基控制这些等距映射，再对环境取迹，得到固定 CPTP 处理器。

令 $X$ 为 Pauli 矩阵，取仿射程序曲线
$$
\rho_u=\frac12(I+x(u)X+uZ),\qquad
x(u)=\frac{\lambda(1-tu)}{\sqrt{1-t^2}},\qquad
k=\frac{\lambda^2}{1-t^2}.
\tag{191.5}
$$
其满秩物理区间为 $(b_-,b_+)$，其中
$$
b_\pm=\frac{kt\pm\sqrt{1-\lambda^2}}{1+kt^2}.
\tag{191.6}
$$
事实上，$\rho_u\succ0$ 等价于
$$
q(u):=1-u^2-k(1-tu)^2>0.
\tag{191.7}
$$
这个二次函数的根为（191.6），且 $q(t)=(1-\lambda^2)(1-t^2)>0$，故 $b_-<t<b_+$。取 $U=(b_-,b_+)\cap J_a$，它是包含 $t$ 的非空开区间。

处理器的 Schur 系数由 $\operatorname{Tr}(\rho_uW_j^\dagger W_i)$ 给出。由于 $ZK=K$、程序矩阵为实对称矩阵，
$$
C_{02}=u,\qquad
C_{01}=C_{12}=A_0\frac{1+u}{2}+\frac{\beta x(u)}2=a.
\tag{191.8}
$$
因此处理器在全部 $U$ 精确生成目标通道。这个恒等式也表明整个闭弦 $[b_-,b_+]$ 都位于 $F(a,u)$ 的 CP 区间 $[2a^2-1,1]$；不过它不包含 $J_a$ 的完整上尾。具体地，$q(1)=-k(1-t)^2<0$，而 $q(t)>0$、$t<1$，所以 $b_+<1$。

对 Bloch 向量 $(x(u),0,u)$，满秩 SLD 公式为
$$
I_Q(\rho_u)=1+(x')^2+\frac{(u+xx')^2}{1-u^2-x^2}.
\tag{191.9}
$$
将可读下界移到左边，完成平方可得
$$
I_Q(\rho_u)-I_r(u)
=\frac{[(1-u^2)x'+ux]^2}{(1-u^2)(1-u^2-x^2)}
=\frac{k(u-t)^2}{(1-u^2)q(u)}.
\tag{191.10}
$$
它在 $t$ 恰为零，在 $U\setminus\{t\}$ 严格为正。程序在 $U$ 始终满秩且解析，所以这是规则达到。证毕。

例如，当 $0<a<1/2$、$t=0$ 时，可取 $2a<\lambda<1$，有 $K=\left(\begin{smallmatrix}0&2a/\lambda\\0&0\end{smallmatrix}\right)$、$\rho_u=(I+\lambda X+uZ)/2$，物理区间为 $|u|<\sqrt{1-\lambda^2}$。此时（191.10）成为 $\lambda^2u^2/[(1-u^2)(1-u^2-\lambda^2)]$，直接显示在零点达到及其邻域的正额外成本。这是本定理的参数特化，不改变全区间二维下界的覆盖假设。

**定理 191.3（局部纯程序达到仍不能使用二维空间）。** 设一个固定处理器在包含 $t\in J_a$ 的开区间上精确生成 $\mathcal T_u$，且程序曲线在该区间为 $C^1$ 纯态。若程序联合空间维数不超过二，则
$$
I_Q(\rho_t)>I_r(t).
\tag{191.11}
$$

证明。 一维程序只能生成恒定通道，所以只需考虑二维。取处理器的 Stinespring 等距表示 $V$。对信号基态 $|i\rangle$，目标通道保持纯输出 $|i\rangle\langle i|$，故对每个程序向量 $\psi_u$，
$$
V(|i\rangle\otimes\psi_u)=|i\rangle\otimes w_i(u).
\tag{191.12}
$$
程序向量在任一非空精确开区间内张成整个二维空间：否则所有程序投影相同，诱导通道不随 $u$ 变化。由线性性，（191.12）因此推广为
$$
V=\sum_{i=0}^2|i\rangle\langle i|\otimes W_i,
\qquad W_i^\dagger W_i=I
\tag{191.13}
$$
在整个信号与二维程序输入空间上的恒等式。这里的受控等距形状由纯基态输出推出，没有预先限制处理器类型。

固定均衡 $02$ 输入并测量 $|+\rangle,|-\rangle$。由（191.13），其在任意程序输入上的信号输出均位于 $02$ 子空间；因此得到完整的二维程序 POVM
$$
M_\pm=\frac12(I\pm\operatorname{Re}A),\qquad
A=W_2^\dagger W_0,
\qquad p_+=h=\frac{1+u}{2},\quad p_-=\ell=1-h.
\tag{191.14}
$$
$A$ 是压缩算子，且 $\operatorname{Re}A=(A+A^\dagger)/2$。测量的信息量为 $I_r$，所以一般测量信息不等式已给出 $I_Q\ge I_r$。

反设在 $t$ 取等号。令 $L$ 为该点的 SLD，$\psi=\psi_t$。支持敏感的测量等号条件要求
$$
\sqrt{M_j}L\psi=s_j\sqrt{M_j}\psi,
\qquad s_j=\frac{p_j'}{p_j}\ne0,
\qquad j\in\{+,-\}.
\tag{191.15}
$$
这一条件可由每项 Hilbert 空间 Cauchy–Schwarz 等号直接取得，亦见 Braunstein–Caves，Phys. Rev. Lett. **72**, 3439（1994），DOI:10.1103/PhysRevLett.72.3439，式（24）—（26）的支持敏感等号条件。若某个 $M_j$ 可逆，（191.15）就给出 $L\psi=s_j\psi$；但 $\langle\psi,L\psi\rangle=\operatorname{Tr}\rho'=0$，与 $s_j\ne0$ 矛盾。故两个非零效应都是秩一。二维中两个秩一正效应之和为单位算子，必为互补正交投影。

选择其本征基，令 $M_\pm=(I\pm Z)/2$，从而 $\operatorname{Re}A=Z$。由 $\|A\|\le1$，在 $Z$ 的两个本征向量上，实部为 $\pm1$ 的期望值已经饱和 Cauchy–Schwarz；因此 $A=Z$。又因 $W_0,W_2$ 为等距映射，$W_2^\dagger W_0=Z$ 蕴含 $W_2=W_0Z$。

在 $t$ 附近选择连续可微的归一纯态向量，并用固定基向量相位令
$$
\psi_u=\begin{pmatrix}\sqrt h\\ e^{i\varphi(u)}\sqrt\ell\end{pmatrix},
\qquad\varphi(t)=0.
\tag{191.16}
$$
这里对 $C^1$ 曲线只需取 $C^1$ 的局部相位。纯态信息量为
$$
I_Q(\rho_u)=I_r(u)+4h\ell(\varphi')^2.
\tag{191.17}
$$
所以等号迫使 $\varphi'(t)=0$，并有
$$
\psi_t=\begin{pmatrix}\sqrt{h_0}\\\sqrt{\ell_0}\end{pmatrix},
\qquad
v:=\psi_t'=\begin{pmatrix}1/(4\sqrt{h_0})\\-1/(4\sqrt{\ell_0})\end{pmatrix}.
\tag{191.18}
$$
令 $K=W_0^\dagger W_1$。通道的两个固定实系数给出
$$
\langle\psi_u,K\psi_u\rangle=a,
\qquad
\langle Z\psi_u,K\psi_u\rangle=a.
\tag{191.19}
$$
第一式使用 $C_{01}$ 的复共轭仍等于实数 $a$，第二式使用 $W_2=W_0Z$。两式相加相减先给出整个邻域的向量恒等式；再在 $t$ 求导，得到
$$
K\psi_u=\begin{pmatrix}a/\sqrt h\\0\end{pmatrix},
\qquad
Kv=\begin{pmatrix}-a/(4h_0\sqrt{h_0})\\0\end{pmatrix}.
\tag{191.20}
$$
两个实向量 $\psi_t,v$ 线性无关，故它们的像唯一确定整个复矩阵：
$$
K=\begin{pmatrix}A_0&B_0\\0&0\end{pmatrix},
\qquad A_0=\frac{at}{h_0},\quad B_0=2a\sqrt{\frac{\ell_0}{h_0}}>0.
\tag{191.21}
$$
于是（191.19）第一式在附近每个参数的实部都必须满足
$$
a=A_0h+B_0\sqrt{h\ell}\cos\varphi(u)
\le A_0h+B_0\sqrt{h\ell}
$$
$$
=a-\frac a{h_0}
\left(\sqrt{h\ell_0}-\sqrt{\ell h_0}\right)^2.
\tag{191.22}
$$
对 $u\ne t$，最后的平方严格为正，矛盾。因此不能在 $t$ 达到等号，结合测量信息下界即得（191.11）。证毕。

**定理 191.4（局部与全区间、纯态与混态的维数分离）。** 对任意 $t\in J_a$，达到可读下界所需的最小联合程序维数具有以下取值：允许混态且只要求局部精确、规则达到时为二；要求局部程序曲线为纯态时为三；要求精确覆盖整个 $J_a$ 时为三，且三维达到可用全程纯态完成。

证明。 局部一维程序不能产生非恒定通道，定理191.2给出二维满秩达到。定理191.3排除局部纯二维达到，定理190.3给出三维纯态的全区间达到，因而也给出局部纯态达到。全区间的下界与达到由定理190.4给出。

特别地，二维局部规则达到若在设计点为纯态，则恒秩条件使它在邻域仍为纯态，与定理191.3矛盾。因此二维局部规则达到在设计点必须满秩。这里没有排除只在单点为纯态、周围发生秩变化的程序；也没有求出局部纯二维程序信息量的精确下确界。上述维数分别针对已写明的覆盖域与秩条件，不能将局部混态构造带入第190节的全区间类。证毕。

<a id="entry-732"></a>

## 追加锚（本行以下为增补区）

<a id="section-192"></a>

## 192. 有限点全部最优与连续区间的正积分成本

**定义 192.1（归一额外成本与固定比较区间）。** 固定 $0<a<1$，仍考虑精确生成全部 $\mathcal T_u$、$u\in J_a=(2a-1,1)$ 的有限维固定程序。定义
$$
D(u)=I_Q(\rho_u)-I_r(u),\qquad
e(u)=\frac{I_Q(\rho_u)}{I_r(u)}-1=(1-u^2)D(u),
\qquad I_r(u)=\frac1{1-u^2}.
\tag{192.1}
$$
由固定均衡 $02$ 读出，$D,e\ge0$。取第189节的比较区间
$$
I_a=[u_-,u_+],\qquad
u_- =\frac{3a-1}{2},\quad u_0=a,\quad u_+=\frac{1+a}{2},
\qquad |I_a|=1-a.
\tag{192.2}
$$
沿用（189.3）的三个实系数 $\alpha_-,\alpha_0,\alpha_+$，即令 $h_i=(1+u_i)/2$、$\ell_i=1-h_i$ 后满足
$$
\sum_i\alpha_i h_i=0,\qquad
\sum_i\alpha_i\ell_i=1,\qquad
\sum_i\alpha_i\sqrt{h_i\ell_i}=0.
\tag{192.3}
$$
令
$$
C_a=\max(|\alpha_-|,|\alpha_+|)>0,
\qquad \mu_a=\frac{\sqrt{1+8a^2}-1}{6},
$$
$$
\Gamma(a)=\frac{\mu_a^2(1-a)(1-u_+^2)}{4C_a^2}>0.
\tag{192.4}
$$
$C_a>0$ 由第189.1节 $|\alpha_-|+|\alpha_+|>0$ 得到。

**定理 192.2（任意有限维程序的额外信息具有正积分下界）。** 对任意 $C^1$ 的全区间精确程序曲线，允许秩变化，有
$$
\int_{I_a}\sqrt{D(u)}\,du\ge\frac{\mu_a(1-a)}{2C_a},
\tag{192.5}
$$
$$
\int_{I_a}D(u)\,du\ge\frac{\mu_a^2(1-a)}{4C_a^2},
\qquad
\int_{I_a}e(u)\,du\ge\Gamma(a).
\tag{192.6}
$$
积分均取非负函数的 Lebesgue 积分，允许值为正无穷；常数与程序维数无关。

证明。 先说明秩变化时的可测性。对任一内部参数，有限 Hermitian SLD $L$ 满足 $\rho'=(L\rho+\rho L)/2$，因而
$$
I_Q(\rho_u)=\sup_{H=H^\dagger}
\left[2\operatorname{Tr}(\rho_u'H)-\operatorname{Tr}(\rho_uH^2)\right].
\tag{192.7}
$$
对固定 $u$，方括号等于 $I_Q-\operatorname{Tr}(\rho_u(H-L)^2)$，并在 $H=L$ 达到上确界。由于它对有限维变量 $H$ 连续，可以只取一个可数稠密的 Hermitian 矩阵集合。每个固定 $H$ 对应的函数关于 $u$ 连续，所以 $I_Q$ 下半连续，从而 $D,e$ 及 $\sqrt D$ 都是非负 Borel 函数。这使用点态 SLD 约定，不假设 SLD 矩阵沿曲线连续。

沿第189节，用固定 Naimark 嵌入与 CPTP 解码把读出写成互补投影 $P_\pm$，程序记为 $\sigma_u$。令
$$
K_u=\sqrt h\,P_++\sqrt\ell\,P_-,\qquad
\tau_u=K_u^{-1}\sigma_uK_u^{-1},\qquad
\widehat\sigma_u=K_u\tau_aK_u,
\tag{192.8}
$$
其中 $h=(1+u)/2$、$\ell=1-h$。第189节的精确剩余平方给出
$$
\|\tau_u'\|_1\le\frac{\sqrt{D(u)}}{\min(h,\ell)}.
\tag{192.9}
$$
$\tau_u'$ 由连续的程序导数及光滑矩阵直接定义，因此可对它使用微积分基本定理。由于 $\|K_{u_i}\|_\infty^2\le1$，
$$
\|\sigma_{u_-}-\widehat\sigma_{u_-}\|_1
\le\int_{u_-}^{a}\frac{\sqrt{D(u)}}{\min(h,\ell)}\,du,
$$
$$
\|\sigma_{u_+}-\widehat\sigma_{u_+}\|_1
\le\int_a^{u_+}\frac{\sqrt{D(u)}}{\min(h,\ell)}\,du,
\qquad \sigma_a=\widehat\sigma_a.
\tag{192.10}
$$
上式右边为无穷时不等式仍成立。

向同一扩展处理器输入均衡三能级纯态，实际输出为 $X_u=F(a,u)/3$，参考输出为 $\widehat X_u$。第189节的固定分块展开及（192.3）给出
$$
\sum_i\alpha_iX_{u_i}=F(a,-1)/3,
\qquad
\sum_i\alpha_i\widehat X_{u_i}=X_-,
\tag{192.11}
$$
其中 $X_-$ 是密度矩阵。$F(a,-1)/3$ 的负特征值为 $-\mu_a$，两者迹均为一，故其迹范数距离至少为 $2\mu_a$。再用固定处理器的迹范数收缩、（192.10）及中点误差为零，得到
$$
2\mu_a\le
|\alpha_-|\int_{u_-}^{a}\frac{\sqrt{D(u)}}{\min(h,\ell)}\,du
+|\alpha_+|\int_a^{u_+}\frac{\sqrt{D(u)}}{\min(h,\ell)}\,du.
\tag{192.12}
$$
在 $I_a$ 上，$\min(h,\ell)\ge(1-a)/4$，故
$$
2\mu_a\le\frac{4C_a}{1-a}\int_{I_a}\sqrt{D(u)}\,du,
\tag{192.13}
$$
证明（192.5）。若 $\int D$ 有限，Cauchy–Schwarz 给出 $(\int\sqrt D)^2\le(1-a)\int D$；若无穷，所需下界自动成立。最后，$|u_-|\le u_+$，所以 $1-u^2\ge1-u_+^2$，结合 $e=(1-u^2)D$ 即得（192.6）。证毕。

**定理 192.3（任意有限组设计点可由同一纯程序同时达到）。** 对任意有限非空集合 $\mathcal S=\{v_1,\ldots,v_m\}\subset J_a$，存在一个固定处理器和一条 $C^\infty$ 纯程序曲线，精确生成全部 $J_a$，程序空间维数不超过 $3m$，且
$$
I_Q(\rho_{v_i})=I_r(v_i)\qquad(1\le i\le m).
\tag{192.14}
$$
因此在这些条件下，有限集合上的最坏信息成本比的最小值为一，并被达到。

证明。 对每个 $v_i$，取定理190.3的三维实归一向量 $\psi_i(u)$ 及固定处理器 $\mathcal G_i$。每个分支在全部 $J_a$ 精确生成同一个 $\mathcal T_u$，且在 $v_i$ 达到下界。

若 $m\ge2$，为 $i=2,\ldots,m$ 选择光滑截断函数 $0\le\chi_i\le1$，其紧支集在 $J_a$ 内两两不交、避开 $v_1$，并且在 $v_i$ 的某邻域恒为一。定义
$$
g_1=1-\sum_{i=2}^m\chi_i,\qquad g_i=\chi_i\ (i\ge2),
\qquad b_i=\frac{g_i}{\sqrt{\sum_jg_j^2}}.
\tag{192.15}
$$
同一参数处至多一个截断函数非零，故 $\sum_jg_j^2\ge1/2$，归一化全局光滑。$b_i$ 在 $v_i$ 附近恒为一，其他振幅在那里恒为零。$m=1$ 时直接取 $b_1=1$。

令 $\mathcal H_P=\bigoplus_{i=1}^m\mathbb C^3$，$E_i$ 为固定块嵌入，并取
$$
\Psi_u=\bigoplus_i b_i(u)\psi_i(u),\qquad
\rho_u=|\Psi_u\rangle\langle\Psi_u|.
\tag{192.16}
$$
这是一条全局光滑、归一且秩恒为一的程序曲线。定义固定处理器
$$
\mathcal G(X)=\sum_i\mathcal G_i\!\left[(I\otimes E_i^\dagger)X(I\otimes E_i)\right].
\tag{192.17}
$$
每项为 CP，且 $\sum_iE_iE_i^\dagger=I$ 保证整体保迹。处理器舍弃程序不同块之间的交叉项，故
$$
\mathcal G(\omega\otimes\rho_u)
=\sum_i b_i(u)^2\mathcal T_u(\omega)=\mathcal T_u(\omega).
\tag{192.18}
$$
所有分支的精确性属于同一个实际参数 $u$，因此这里可以直接组合。

实归一分支满足 $\langle\psi_i,\psi_i'\rangle=0$。固定块正交及 $\sum_i b_i^2=1$ 给出
$$
I_Q(\rho_u)=4\|\Psi_u'\|^2
=\sum_i b_i^2 I_Q(\psi_i(u))+4\sum_i(b_i')^2
$$
$$
=I_r(u)+4h\sum_i b_i^2(\theta_i')^2+4\sum_i(b_i')^2,
\tag{192.19}
$$
其中 $\theta_i(u)$ 是第190节角度与 $h=(1+u)/2$ 的复合，所有导数均对 $u$ 求取。该式保留了切换振幅的信息成本。在 $v_i$，只有第 $i$ 个分支被选中，振幅导数全部为零，且 $\theta_i'(v_i)=0$，所以（192.14）成立。结合普遍的 $I_Q\ge I_r$，有限集合上的最小比值确为一。证毕。

固定程序、纯程序与正交控制标签的背景见 Hillery、Ziman、Bužek，Phys. Rev. A **66**, 042302（2002），DOI:10.1103/PhysRevA.66.042302，第II.B节式（2.12）—（2.16）与第III.A节；纯态信息度量见 Braunstein–Caves，Phys. Rev. Lett. **72**, 3439（1994），DOI:10.1103/PhysRevLett.72.3439。这里的有限点达到来自第190节具体曲线与上述固定块拼接。$3m$ 是充分维数上界，不宣称它最小，也不宣称达到点的数量增加必然要求维数增加。

**定理 192.4（稠密有限校准必须失去统一导数界）。** 第189节的常数 $\Delta(a)>0$ 已在固定比较区间上给出
$$
\sup_{u\in I_a} e(u)\ge\Delta(a).
\tag{192.20}
$$
设一个全区间精确的光滑纯程序在有限非空集合 $\mathcal S\subset I_a$ 上满足 $e(s)=0$，并令
$$
\rho(\mathcal S)=\max_{u\in I_a}\min_{s\in\mathcal S}|u-s|>0.
\tag{192.21}
$$
则
$$
\max_{u\in I_a}|e'(u)|\ge\frac{\Delta(a)}{\rho(\mathcal S)}.
\tag{192.22}
$$

证明。 第189.2节的全部积分与三个比较点都位于 $I_a$；将其全区间上确界 $R$ 换成 $\sup_{I_a}I_Q/I_r$，原证明及常数不变，得到（192.20）。光滑纯态的信息量由 $4(\|\Psi'\|^2-|\langle\Psi,\Psi'\rangle|^2)$ 给出，所以 $e$ 在 $I_a$ 光滑并取得最大值。设最大点为 $v$，取距离它最近的 $s\in\mathcal S$。$e(v)\ge\Delta(a)>0=e(s)$，故 $v\ne s$。均值定理给出二者之间一点 $\xi$，使
$$
|e'(\xi)|=\frac{e(v)-e(s)}{|v-s|}
\ge\frac{\Delta(a)}{\rho(\mathcal S)},
$$
证明所需结论。更一般地，若已知 $e$ 在 $I_a$ 的 Lipschitz 常数为 $L$，则
$$
\max_{I_a}e\le\max_{\mathcal S}e+L\rho(\mathcal S).
\tag{192.23}
$$
因此有限设计点可以全部满足精确最优；但当其覆盖半径趋于零时，这些设计不能同时保持统一的导数界。定理192.2还要求每个设计保留至少 $\Gamma(a)$ 的额外成本积分。这里比较的是参数函数的有限点值与连续区间控制，不涉及有限试验次数造成的统计误差，也不将逐个有限集合可重新设计替换为同一程序在整个区间达到。证毕。

<a id="entry-734"></a>

## 追加锚（本行以下为增补区）

<a id="section-193"></a>

## 193. 局部纯二维程序的精确成本下确界与转置不变约束

**定义 193.1（纯二维邻域精确生成的逐点成本）。** 固定 $0<a<1$、$t\in J_a=(2a-1,1)$，令
$$
F(a,u)=\begin{pmatrix}1&a&u\\a&1&a\\u&a&1\end{pmatrix},\qquad
\mathcal T_u=\mathcal S_{F(a,u)},\qquad
B(a,u)=\frac{1-a^2}{(1-u)(1+u-2a^2)}.
\tag{193.1}
$$
一个局部纯二维程序由包含 $t$ 的非空开区间 $U\subset J_a$、$U$ 上的 $C^1$ 秩一密度矩阵曲线 $\rho_u\in M_2$，以及与 $u$ 无关的 CPTP 映射
$$
\mathcal G:M_3\otimes M_2\longrightarrow M_3
\tag{193.2}
$$
组成，要求对每个 $u\in U$ 和每个信号态 $\omega$ 都有 $\mathcal G(\omega\otimes\rho_u)=\mathcal T_u(\omega)$。不同程序允许使用不同的 $U$。成本取关于 $u$ 的 SLD 信息量，记
$$
\mathfrak P_{2,\mathrm{loc}}(a,t)
=\inf_{(U,\rho,\mathcal G)}I_Q(\rho_t).
\tag{193.3}
$$
这里要求整个 $U$ 上的严格等式；仅在 $t$ 匹配值和一阶导数的程序不属于此定义。第191节给出了每个这种程序都不能达到 $I_{\rm read}(t)=1/(1-t^2)$ 的结论。以下求出整个程序类的下确界。

**定理 193.2（纯二维局部成本等于经典生成成本）。** 对定义193.1的全部参数，
$$
\boxed{\mathfrak P_{2,\mathrm{loc}}(a,t)=B(a,t)}.
\tag{193.4}
$$
每个允许程序在其整个定义区间上满足 $I_Q(\rho_u)\ge B(a,u)$。另一方面，对任意 $\delta>0$，存在秩一解析程序及固定处理器，在包含 $t$ 的真实开区间内精确生成 $\mathcal T_u$，且
$$
B(a,t)\le I_Q(\rho_t)<B(a,t)+\delta.
\tag{193.5}
$$
因此纯二维局部下确界与单次可读信息的精确比值为
$$
\frac{\mathfrak P_{2,\mathrm{loc}}(a,t)}{I_{\rm read}(t)}
=1+\frac{a^2(1-t)}{1+t-2a^2}>1.
\tag{193.6}
$$
式（193.4）是下确界陈述，不断言某个允许程序在 $t$ 达到 $B(a,t)$。

证明。 先建立任意处理器的下界。以 Pauli 矩阵记 $\rho_u=(I+r(u)\cdot\sigma)/2$；纯性等价于 $|r(u)|=1$。固定处理器诱导从实 Bloch 向量到信号线性映射的仿射映射，其线性部分为
$$
\mathcal L(x)(X)=\frac12\mathcal G\bigl(X\otimes(x\cdot\sigma)\bigr),\qquad x\in\mathbb R^3.
\tag{193.7}
$$
若 $\mathcal L$ 的实秩为三，则它是单射。因为 $\mathcal T_u$ 是关于 $u$ 的非恒定仿射直线，精确性迫使 $r(u)=r(t)+(u-t)v$，其中固定向量 $v\ne0$。但 $|r(t)+(u-t)v|^2=1$ 不可能在开区间上恒成立，因为二次项系数为 $|v|^2>0$。所以
$$
\operatorname{rank}_{\mathbb R}\mathcal L\le2.
\tag{193.8}
$$
选择非零核方向，并对程序作固定酉基变换，可令该方向为 Pauli 矩阵 $Y$。于是对所有信号算符 $X$ 都有 $\mathcal G(X\otimes Y)=0$。

固定任意信号态 $\omega$，定义从程序到信号输出的通道
$$
\mathcal E_\omega(\tau)=\mathcal G(\omega\otimes\tau).
\tag{193.9}
$$
它从 $M_2$ 映到 $M_3$，是 CPTP，且消去 $Y$。在上述程序基下，转置保持 $I,X,Z$ 而使 $Y$ 变号，故 $\mathcal E_\omega\circ T=\mathcal E_\omega$。其归一化 Choi 态因而满足
$$
C_\omega=\frac12\sum_{j,k=0}^1|j\rangle\langle k|\otimes
\mathcal E_\omega(|j\rangle\langle k|),\qquad
C_\omega^{T_1}=C_\omega\succeq0.
\tag{193.10}
$$
这里使用 $2\times3$ 系统的 PPT 可分性判据：M. Horodecki、P. Horodecki、R. Horodecki，*Separability of mixed states: necessary and sufficient conditions*，arXiv:quant-ph/9605038v2，定理3及其后关于第一因子转置的注记。因此 $C_\omega$ 可分，有限维中可写成有限和 $\sum_k w_k A_k\otimes\tau_k$，其中 $A_k,\tau_k$ 为密度矩阵、$w_k\ge0$。由 $\operatorname{Tr}_{\rm out}C_\omega=I_2/2$ 以及 Choi 重构公式，得到
$$
\mathcal E_\omega(\tau)=\sum_k\operatorname{Tr}(M_k\tau)\tau_k,
\qquad M_k=2w_k A_k^{\mathsf T}\succeq0,\qquad \sum_kM_k=I_2.
\tag{193.11}
$$
这是可分 Choi 态与测量—制备表示的标准对应；参见 Horodecki、Shor、Ruskai，*Entanglement Breaking Channels*，arXiv:quant-ph/0302031v2，定理4。上面的重构直接保留二维输入、三维输出，不要求输入输出维数相同。这里取得测量—制备形式的是固定信号输入后的 $\mathcal E_\omega$，不是断言 $\mathcal T_u$ 本身是纠缠破坏通道。

取严格正概率向量 $p=(p_0,p_1,p_2)$，令 $|s_p\rangle=\sum_i\sqrt{p_i}|i\rangle$，并固定 $\omega=|s_p\rangle\langle s_p|$。记 $D_p=\operatorname{diag}(\sqrt p)$、$E_{02}=E_{20}=1$ 且 $E$ 其余项为零，则
$$
\Sigma_u=D_pF(a,u)D_p=\sum_k q_k(u)\tau_k,\qquad
\Sigma_u'=D_pED_p,\qquad q_k(u)=\operatorname{Tr}(M_k\rho_u).
\tag{193.12}
$$
$F(a,u)$ 在 $J_a$ 上正定，故 $\Sigma_u$ 可逆。在任何固定的内部点，若 $q_k(u)=0$，则两侧非负性与可微性给出 $q_k'(u)=0$。以下和式省略这些零项。设 $s_k=q_k'/q_k$，有
$$
\begin{pmatrix}\Sigma_u&\Sigma_u'\\\Sigma_u'&Q_u\end{pmatrix}
=\sum_{k:q_k>0}q_k
\begin{pmatrix}\tau_k&s_k\tau_k\\s_k\tau_k&s_k^2\tau_k\end{pmatrix}\succeq0,
\qquad Q_u=\sum_{k:q_k>0}\frac{q_k'^2}{q_k}\tau_k.
\tag{193.13}
$$
Schur 补和取迹遂给出
$$
\operatorname{Tr}(\Sigma_u'\Sigma_u^{-1}\Sigma_u')
\le\operatorname{Tr}Q_u
=\sum_{k:q_k>0}\frac{q_k'^2}{q_k}
\le I_Q(\rho_u).
\tag{193.14}
$$
最后一步是固定 POVM 下的 SLD 信息量单调性。前一个不等式是经典反向制备的 RLD 下界的直接分块证明；其一般反向估计背景见 Matsumoto，*Reverse estimation theory, Complementarity between SLD and RLD, and monotone distances*，arXiv:quant-ph/0511170v1，第4节。测量界采用 Braunstein、Caves，*Statistical distance and the geometry of quantum states*，Physical Review Letters 72, 3439–3443（1994），DOI:10.1103/PhysRevLett.72.3439 的 SLD 约定。

逆矩阵的两个端点对角元为
$$
(F(a,u)^{-1})_{00}=(F(a,u)^{-1})_{22}
=\frac{1-a^2}{(1-u)(1+u-2a^2)}=B(a,u).
\tag{193.15}
$$
所以由（193.12）及迹的循环性，
$$
\operatorname{Tr}(\Sigma_u'\Sigma_u^{-1}\Sigma_u')
=\operatorname{Tr}\bigl(D_p^2EF(a,u)^{-1}E\bigr)
=(p_0+p_2)B(a,u).
\tag{193.16}
$$
保持 $p_0,p_2>0$ 而令 $p_1\downarrow0$，即得 $I_Q(\rho_u)\ge B(a,u)$。此极限只作用于下界的数值；每次应用（193.14）时仍使用满支持信号输入与可逆输出，并未在奇异极限态上求逆。秩论证只用各程序自己的非空开区间，不要求全部程序共享一个区间。

再构造逼近下界的纯二维程序。固定名义点 $t$，简记 $B=B(a,t)$、$h_0=(1+t)/2$、$\ell_0=1-h_0$，并置 $c=a\ell_0/(1-a^2)$。使用定理184.2的三个固定通道 $\mathcal R_+,\mathcal R_-,\mathcal R_c$ 及其在整个 $J_a$ 上严格为正的仿射概率
$$
\begin{aligned}
p_c(u)&=\frac{1-(1+u)/2}{1-c^2},\\
p_+(u)&=\frac{(1+u)/2+a-(1+a)c}{2(1-c)},\\
p_-(u)&=\frac{(1+u)/2-a+(1-a)c}{2(1+c)}.
\end{aligned}
\tag{193.17}
$$
令 $p_j=p_j(t)$、$v_j=p_j'(t)$；这些常数满足
$$
\sum_jp_j=1,\qquad \sum_jv_j=0,\qquad
\sum_j\frac{v_j^2}{p_j}=B,
\qquad p_j(u)=p_j+(u-t)v_j.
\tag{193.18}
$$
三项 $v_j$ 均非零。定义
$$
q_j=\frac{v_j^2}{Bp_j},\qquad
C=1+\max_j\frac{q_j}{p_j},\qquad
0<\varepsilon<\frac1{2C},\qquad \lambda=\sqrt{1-C\varepsilon}.
\tag{193.19}
$$
于是 $\sum_jq_j=1$、$q_j>0$、$\lambda^2>1/2$。取三个实对称测量算符
$$
M_j=\begin{pmatrix}
\dfrac{p_j-\varepsilon q_j}{1-\varepsilon}&\dfrac{\lambda v_j}{\sqrt B}\\[2mm]
\dfrac{\lambda v_j}{\sqrt B}&q_j
\end{pmatrix}.
\tag{193.20}
$$
由（193.18）立即有 $\sum_jM_j=I_2$。两个对角元严格为正，且
$$
\det M_j
=\frac{\varepsilon q_j}{1-\varepsilon}
\bigl[p_j(1+C-C\varepsilon)-q_j\bigr]>0.
\tag{193.21}
$$
严格正性使用 $q_j/p_j\le C-1$、$C\varepsilon<1/2$；同样有 $\varepsilon q_j<p_j/2$。所以这些算符组成固定 POVM。

令
$$
R_\varepsilon=\frac{2\lambda\sqrt{\varepsilon(1-\varepsilon)}}{\sqrt B},\qquad
U_\varepsilon=J_a\cap(t-R_\varepsilon,t+R_\varepsilon),
\tag{193.22}
$$
并在这个包含 $t$ 的非空开区间上定义 Bloch 向量
$$
r_\varepsilon(u)=\left(
\frac{\sqrt B(u-t)}\lambda,
\sqrt{4\varepsilon(1-\varepsilon)-\frac{B(u-t)^2}{\lambda^2}},
1-2\varepsilon
\right),\qquad
\rho_u^{(\varepsilon)}=\frac{I+r_\varepsilon(u)\cdot\sigma}{2}.
\tag{193.23}
$$
根号内严格为正，且 $|r_\varepsilon(u)|=1$，故这是一条解析的纯态曲线。实测量算符不读取 $Y$ 分量，直接计算得到
$$
\operatorname{Tr}(\rho_u^{(\varepsilon)}M_j)
=(1-\varepsilon)\frac{p_j-\varepsilon q_j}{1-\varepsilon}
+\varepsilon q_j+\frac{\sqrt B(u-t)}\lambda\frac{\lambda v_j}{\sqrt B}
=p_j(u).
\tag{193.24}
$$
固定处理器先测量程序的 $M_j$，再对信号执行 $\mathcal R_j$。明确地，对联合输入算符 $Z$ 可写为
$$
\mathcal G_\varepsilon(Z)=\sum_j\mathcal R_j\!\left(
\operatorname{Tr}_{P}\bigl[(I\otimes\sqrt{M_j})Z(I\otimes\sqrt{M_j})\bigr]\right).
\tag{193.25}
$$
它是 CPTP，且（193.17）、（193.24）给出 $\mathcal G_\varepsilon(\omega\otimes\rho_u^{(\varepsilon)})=\mathcal T_u(\omega)$，在整个 $U_\varepsilon$ 上是严格等式。

纯 Bloch 曲线的 SLD 信息量为 $|r_\varepsilon'(u)|^2$。在 $u=t$，只有第一分量的导数非零，因此
$$
I_Q(\rho_t^{(\varepsilon)})=\frac B{\lambda^2}
=\frac B{1-C\varepsilon}\longrightarrow B
\qquad(\varepsilon\downarrow0).
\tag{193.26}
$$
任意给定 $\delta>0$，再要求 $\varepsilon<\delta/[C(B+\delta)]$ 即得（193.5）。与已经证明的下界合用，得到（193.4），相除并化简得到（193.6）。上述逼近中 $R_\varepsilon\to0$；在 $\varepsilon=0$ 直接取极限不能得到仍有非空定义邻域的纯态曲线，因此这个构造没有把下确界升级为最小值。证毕。

<a id="entry-736"></a>

## 追加锚（本行以下为增补区）

<a id="section-194"></a>

## 194. 纯二维成本下确界的不达到性与固定精确邻域的正差距

**定理 194.1（每个局部纯二维程序严格高于下确界）。** 在定义193.1的程序类中，对每个 $t\in U$ 都有
$$
I_Q(\rho_t)>B(a,t).
\tag{194.1}
$$
因此定理193.2的下确界不由任何一个允许程序达到。

证明。 固定一个允许程序及内部点 $t$。沿用（193.7）的实线性映射 $\mathcal L$，记 $K=\ker\mathcal L\ne\{0\}$、$A=K^\perp$，以及 Bloch 向量 $r(u)$。$\mathcal L$ 在 $A$ 上单射，故目标通道的非恒定仿射性迫使
$$
P_A r(u)=a_0+(u-t)v,\qquad v\in A\setminus\{0\}.
\tag{194.2}
$$
若 $r(t)\perp K$，则 $|a_0|=1$。但非恒定仿射线不可能在内点经过单位球面而两侧都留在闭单位球内；具体地，两个对称参数的平方范数平均为 $1+s^2|v|^2>1$。所以可以选择单位向量 $n\in K$ 使 $n\cdot r(t)\ne0$。

以固定程序酉变换将 $n$ 转到 $Y$ 方向。于是 $\mathcal G(X\otimes Y)=0$，而 $r_y(t)\ne0$。在 $t$ 的一个较小邻域内定义
$$
\sigma_u=\frac{\rho_u+\rho_u^{\mathsf T}}2
=\frac{I+r_x(u)X+r_z(u)Z}{2}\succ0.
\tag{194.3}
$$
它生成同一条通道。这个式子只构造另一条合法状态曲线，不把转置平均视为 CPTP 操作，也不对它使用信息量单调性。记 $s=(r_x,r_z)$。由纯性 $|s|^2+r_y^2=1$ 以及 $r_y\ne0$，直接得到
$$
I_Q(\rho_u)=|r'(u)|^2
=|s'(u)|^2+\frac{(s(u)\cdot s'(u))^2}{1-|s(u)|^2}
=I_Q(\sigma_u).
\tag{194.4}
$$
最后一项使用满秩 qubit 的 SLD 公式。

还需要固定信号输入之间的共同实现。第191.3节的受控 Stinespring 推导适用于当前任意处理器：程序向量张成整个二维空间，而每个信号基态输出固定为同一纯基态，所以
$$
V=\sum_{i=0}^2|i\rangle\langle i|\otimes W_i,
\qquad W_i^\dagger W_i=I_2.
\tag{194.5}
$$
因而对所有程序态 $\tau$，诱导通道都是 Schur 通道。令 $|s_0\rangle=(|0\rangle+|1\rangle+|2\rangle)/\sqrt3$，并定义
$$
\mathcal E_0(\tau)=\mathcal G(|s_0\rangle\langle s_0|\otimes\tau).
\tag{194.6}
$$
$3\mathcal E_0(\tau)$ 就是整个诱导通道的相关矩阵，且 $\operatorname{diag}\mathcal E_0(\tau)=(1/3,1/3,1/3)$ 对所有程序态恒成立。对任意概率向量 $p$，定义 $D_p=\operatorname{diag}(\sqrt p)$、$|s_p\rangle=\sum_i\sqrt{p_i}|i\rangle$，则同一处理器满足
$$
\mathcal E_p(\tau):=\mathcal G(|s_p\rangle\langle s_p|\otimes\tau)
=3D_p\mathcal E_0(\tau)D_p.
\tag{194.7}
$$

$\mathcal E_0$ 从二维映到三维且消去 $Y$。由第193节使用的 $2\times3$ PPT 判据和 Choi 重构，它存在一个有限测量—制备表示。因为 $\mathcal E_0\circ T=\mathcal E_0$，把各测量效应换成其与转置的平均，可以得到实对称效应的同一个表示：
$$
\mathcal E_0(\tau)=\sum_k\operatorname{Tr}(N_k\tau)\tau_k,
\qquad N_k=N_k^{\mathsf T}\succeq0,\quad \sum_kN_k=I_2.
\tag{194.8}
$$
这里 $\tau_k$ 为固定三维密度矩阵。删去零效应后，$q_k(u)=\operatorname{Tr}(N_k\sigma_u)>0$ 在所取邻域内恒成立；并有 $q_k(u)=\operatorname{Tr}(N_k\rho_u)$。

对每个 $p$ 定义
$$
w_k(p)=3\operatorname{Tr}(D_p^2\tau_k)
=3\sum_i p_i(\tau_k)_{ii},\qquad
\mathcal F(p)=\sum_k w_k(p)\frac{q_k'(t)^2}{q_k(t)}.
\tag{194.9}
$$
由（194.7）及其保迹性，$\{w_k(p)N_k\}_k$ 对每个 $p$ 都是 POVM。对于严格正的 $p$，相应的归一输出态为 $3D_p\tau_kD_p/w_k(p)$；因此（193.13）—（193.16）的同一分块证明及测量界给出
$$
(1-p_1)B(a,t)\le\mathcal F(p)\le I_Q(\sigma_t).
\tag{194.10}
$$
这里的测量—制备分解固定于 $\mathcal E_0$，只按（194.7）对输出作变换，故 $\mathcal F(p)$ 是 $p$ 的一个有限线性函数。

假设 $I_Q(\rho_t)=B(a,t)$。由（194.4）、（194.10）和连续性，令 $p\to p_*=(1/2,0,1/2)$ 得到
$$
\mathcal F(p_*)=I_Q(\sigma_t)=B(a,t).
\tag{194.11}
$$
此步取有限标量函数的极限，不在奇异信号输出上使用逆矩阵。

令 $L$ 为满秩态 $\sigma_t$ 的唯一 SLD。它是实对称矩阵，因为 $\sigma_t,\sigma_t'$ 都是实对称矩阵，SLD 方程及其转置有同一个唯一解。测量 $\{w_k(p_*)N_k\}$ 达到（194.11）的信息量。满秩 SLD 的测量等号条件要求，对每个非零效应 $H_k=w_k(p_*)N_k$，
$$
\sqrt{H_k}L=s_k\sqrt{H_k},\qquad s_k\in\mathbb R.
\tag{194.12}
$$
它可由逐效应 Hilbert–Schmidt Cauchy–Schwarz 等号及 $\sigma_t$ 可逆直接推出；原始表述见 Braunstein、Caves，*Statistical distance and the geometry of quantum states*，Physical Review Letters 72, 3439–3443（1994），DOI:10.1103/PhysRevLett.72.3439，式（24）—（27）。因此每个这种效应支持在 $L$ 的一个本征空间中。$L$ 不是标量矩阵，否则迹为零的导数迫使 $L=0$，与 $I_Q=B>0$ 矛盾。故它有两个互异本征值，记其秩一实投影为 $P_+,P_-$。

若 $w_k(p_*)>0$，则 $N_k$ 支持在其中一个本征空间中。若 $w_k(p_*)=0$，则 $\tau_k$ 的 $00,22$ 对角元均为零，半正定性迫使相应行列也为零，故 $\tau_k=|1\rangle\langle1|$。这些零权重项的聚合效应满足
$$
N_0:=\sum_{k:w_k(p_*)=0}N_k
=I_2-\sum_{k:w_k(p_*)>0}N_k,
\tag{194.13}
$$
也在 $P_+,P_-$ 基下对角。因此（194.8）对全部程序态只依赖两个数 $\operatorname{Tr}(P_\pm\tau)$：正权重项分别为本征投影的倍数，零权重项具有同一个输出态并可合并。于是
$$
\mathcal E_0(\tau)=\sum_{\nu\in\{+,-\}}
\operatorname{Tr}(P_\nu\tau)\mathcal E_0(P_\nu).
\tag{194.14}
$$
因 $\mathcal E_0$ 决定全部诱导 Schur 系数，（194.14）提升为诱导信号通道的同一个二项分解。令固定 CPTP 通道 $\mathcal R_\nu(\omega)=\mathcal G(\omega\otimes P_\nu)$，便有
$$
\mathcal T_u=p(u)\mathcal R_++[1-p(u)]\mathcal R_-,\qquad
p(u)=\operatorname{Tr}(P_+\rho_u)=\operatorname{Tr}(P_+\sigma_u).
\tag{194.15}
$$
在所取邻域内，$0<p(u)<1$。名义点的 SLD 投影测量给出
$$
\frac{p'(t)^2}{p(t)[1-p(t)]}=I_Q(\sigma_t)=B(a,t).
\tag{194.16}
$$
这却是一个二符号经典精确程序，而定理184.3要求它的成本至少为 $B(a,t)/(1-a^2)>B(a,t)$，矛盾。结合定理193.2的非严格下界，得到（194.1）。证毕。

**定理 194.2（固定邻域上的统一正差距）。** 固定 $0<a<1$、$t\in J_a$，以及
$$
0<R<\min\{t-(2a-1),1-t\}.
\tag{194.17}
$$
存在 $\eta(a,t,R)>0$，使每个在包含 $[t-R,t+R]$ 的开区间上精确生成 $\mathcal T_u$ 的纯二维 $C^1$ 程序都满足
$$
I_Q(\rho_t)\ge B(a,t)+\eta(a,t,R).
\tag{194.18}
$$
特别地，若局部纯二维程序序列的名义成本趋于 $B(a,t)$，则对每个固定的 $R$，充分靠后的程序都不能在包含 $[t-R,t+R]$ 的开区间上保持上述精确性。

证明。 简记
$$
J_c=\frac1{(t-(2a^2-1))(1-t)}=\frac{B(a,t)}{1-a^2}.
\tag{194.19}
$$
考虑以下有限维集合 $\mathscr K_R$。它的元素为五元组 $(\mathcal G,\rho_-,\rho_0,\rho_+,d)$：$\mathcal G:M_6\to M_3$ 为 CPTP；其（193.7）中的实 Bloch 线性部分满足 $\operatorname{rank}\mathcal L\le2$；三个 $\rho_\nu$ 为纯 qubit 密度矩阵，分别通过同一处理器精确生成 $\mathcal T_{t-R},\mathcal T_t,\mathcal T_{t+R}$。还要求
$$
d=d^\dagger,\qquad \operatorname{Tr}d=0,\qquad
\rho_0d+d\rho_0=d,\qquad 2\operatorname{Tr}(d^2)\le J_c,
\tag{194.20}
$$
以及对每个信号算符 $X$ 都有
$$
\mathcal G(X\otimes d)=\mathcal S_E(X),\qquad
E_{02}=E_{20}=1,\quad E_{ij}=0\ \text{于其余位置}.
\tag{194.21}
$$
这些条件都是有限维闭条件。CPTP 映射的 Choi 矩阵集合紧，纯密度矩阵集合紧，（194.20）又控制 $d$ 的 Hilbert–Schmidt 范数，所以 $\mathscr K_R$ 紧。这里不固定 Stinespring 环境维数，也不需要曲线空间的紧性。

该集合非空。取完整 CP 区间的两个端点通道 $\mathcal T_{2a^2-1}$、$\mathcal T_1$，用仿射概率的纯正交标记程序
$$
|\psi_u\rangle=\sqrt{p(u)}|0\rangle+\sqrt{1-p(u)}|1\rangle,
\qquad p(u)=\frac{1-u}{2(1-a^2)}
\tag{194.22}
$$
控制这两个通道。它在完整 CP 区间内部精确，Bloch 线性部分秩为一，且在 $t$ 的信息量等于 $J_c$。取其三个状态及导数即可得到集合中的元素。

关键是 $\mathscr K_R$ 中每个五元组都能实现为某个较小开邻域内的纯态精确曲线，并保留 $\rho_0,d$。以 $r_-,r_0,r_+$ 表示其三个 Bloch 向量，以 $\dot r$ 表示 $d=(\dot r\cdot\sigma)/2$。令 $K=\ker\mathcal L$、$A=K^\perp$，写成
$$
r_0=a_0+b_0,\qquad \dot r=v+w,\qquad a_0,v\in A,\quad b_0,w\in K.
\tag{194.23}
$$
由值、导数与端点匹配，以及 $\mathcal L|_A$ 的单射性，
$$
P_A r_\pm=a_0\pm Rv,\qquad v\ne0.
\tag{194.24}
$$
两个端点投影的范数不超过一，故平方相加得到
$$
|a_0|^2+R^2|v|^2\le1,
\qquad |a_0|<1,\quad b_0\ne0.
\tag{194.25}
$$
纯切向条件（194.20）等价于 $r_0\cdot\dot r=0$，亦即 $a_0\cdot v+b_0\cdot w=0$。

对充分小的实数 $s$ 定义
$$
a(s)=a_0+sv,\qquad
b(s)=\sqrt{1-|a(s)|^2}\,\frac{b_0+sw}{|b_0+sw|},\qquad
r(s)=a(s)+b(s).
\tag{194.26}
$$
由（194.25），根号与分母在零附近均严格为正。该曲线解析、$|r(s)|=1$，且 $r(0)=r_0$。求导并用切向条件得
$$
b'(0)=w-\frac{a_0\cdot v+b_0\cdot w}{|b_0|^2}b_0=w,
\qquad r'(0)=\dot r.
\tag{194.27}
$$
又因 $b(s)\in K$，通过同一固定处理器得到的通道恰为 $\mathcal T_{t+s}$。所以这是定义193.1中的一个真实局部纯二维程序，其名义成本为
$$
I_Q=|\dot r|^2=2\operatorname{Tr}(d^2).
\tag{194.28}
$$
这个实现不声称覆盖原来的整个半径 $R$；只需在零的某个开邻域内成立，就能应用定理194.1。因此紧集 $\mathscr K_R$ 上的连续函数 $Q=2\operatorname{Tr}(d^2)$ 处处严格大于 $B(a,t)$。它取得最小值 $m_R$，并满足
$$
B(a,t)<m_R\le J_c.
\tag{194.29}
$$
取 $\eta=m_R-B(a,t)>0$。

任意满足本定理固定邻域要求的实际程序，若 $I_Q(\rho_t)\le J_c$，则其处理器、三个状态与导数组成 $\mathscr K_R$ 的元素：秩约束由第193节的纯性论证保证，且纯态成本等于（194.28）。所以它的成本至少为 $m_R$。若成本大于 $J_c$，则由（194.29）也至少为 $m_R$。这证明（194.18）及其序列结论。所用 $m_R$ 是有限维松弛集合的最小值，不据此断言原固定邻域程序类存在最优程序；此论证也没有给出 $\eta$ 对 $R$ 的显式速率。证毕。

<a id="entry-738"></a>

## 追加锚（本行以下为增补区）

<a id="section-195"></a>

## 195. 纯二维精确邻域的半径与额外信息成本的二次量级

**定义 195.1（固定半径的纯二维最优成本）。** 固定 $0<a<1$、$t\in J_a=(2a-1,1)$，记 $d_t=\min\{t-(2a-1),1-t\}>0$。对 $0<R<d_t$，令 $\mathfrak P_2(a,t;R)$ 为定义193.1的纯二维程序在名义点 $t$ 的 SLD 信息量下确界，但要求其精确开区间包含整个闭区间 $[t-R,t+R]$。处理器及程序可依赖 $a,t,R$；一旦选定，在求导及该区间内运行时保持处理器固定。沿用
$$
B=B(a,t)=\frac{1-a^2}{(1-t)(1+t-2a^2)},\qquad
J_c=\frac{B}{1-a^2}.
\tag{195.1}
$$

**定理 195.2（固定精确半径的二次成本）。** 对每个固定的 $a,t$，存在常数 $c_1,c_2,R_0>0$，使全部 $0<R<R_0$ 满足
$$
c_1R^2\le\mathfrak P_2(a,t;R)-B(a,t)\le c_2R^2.
\tag{195.2}
$$
因此固定精确邻域的额外成本在 $R\downarrow0$ 时为 $\Theta(R^2)$。常数允许依赖 $a,t$；此结论不主张最佳首项系数，也不主张固定半径的下确界一定达到。

证明。 先证明对全部允许程序统一成立的下界。固定
$$
H=\frac{J_c-B}{2}>0,\qquad Q_*=B+H<J_c.
\tag{195.3}
$$
设实际程序的名义信息量为 $Q$，超额为 $\delta=Q-B>0$。先处理 $Q\le Q_*$；大于此上限的情形在后面单独估计。

沿第194节的记号，$K=\ker\mathcal L$，名义 Bloch 向量的核分量为 $b_0=P_Kr(t)$，其在 $K^\perp$ 上的仿射投影斜率为 $v$。两个端点均为物理态，故（194.24）—（194.25）给出
$$
|b_0|^2\ge R^2|v|^2.
\tag{195.4}
$$
这里还能取得 $|v|\ge1$。事实上，固定均衡 $02$ 信号输入并读取对称、反对称输出之差，得到一个固定程序可观测量 $M=m_0I+b\cdot\sigma$，满足 $-I\preceq M\preceq I$，且在目标程序上的期望值为 $u$。于是 $|b|\le1$。该读数经过诱导通道取得，所以 $b\perp K$，并由求导得 $b\cdot v=1$。因此
$$
|b_0|\ge R.
\tag{195.5}
$$

将 $b_0/|b_0|$ 转到程序的 $Y$ 方向，并取第194节的满秩实影子曲线 $\sigma_u$。在名义点，它的最小特征值 $\lambda$ 满足
$$
\lambda=\frac{1-\sqrt{1-|b_0|^2}}2
\ge\frac{|b_0|^2}{4}\ge\frac{R^2}{4},
\qquad I_Q(\sigma_t)=Q.
\tag{195.6}
$$
转置平均仍只用于构造等成本状态曲线，不被当成物理操作。令 $L$ 为 $\sigma_t$ 的 SLD，$g>0$ 为其两个本征值之差。写 $L=l_0I+l\cdot\sigma$，影子 Bloch 向量为 $s$，则 $\operatorname{Tr}(\sigma_tL)=0$ 给出 $l_0=-l\cdot s$，从而
$$
Q=|l|^2-(l\cdot s)^2\le|l|^2,
\qquad g=2|l|\ge2\sqrt Q\ge2\sqrt B.
\tag{195.7}
$$

使用（194.8）的同一个有限测量—制备表示
$$
\mathcal E_0(Z)=\sum_k\operatorname{Tr}(N_kZ)\tau_k,
\qquad N_k=N_k^{\mathsf T}\succeq0,\quad \sum_kN_k=I_2,
\tag{195.8}
$$
其中 $\mathcal E_0$ 是均匀信号输入后的程序到输出通道。删去零效应。固定边界信号人口 $p_*=(1/2,0,1/2)$，令
$$
w_k=\frac32\bigl[(\tau_k)_{00}+(\tau_k)_{22}\bigr],\qquad
A_k=w_kN_k,\qquad q_k=\operatorname{Tr}(N_k\sigma_t)>0.
\tag{195.9}
$$
第194节的共同实现及标量极限保证 $\{A_k\}$ 是 POVM，且它在影子状态上的经典信息量 $F_*$ 至少为 $B$。记
$$
\Delta=Q-F_*,\qquad 0\le\Delta\le\delta.
\tag{195.10}
$$

以下量化满秩测量的等号条件。在 $L$ 的本征基中，令 $o_k=(N_k)_{+-}$、$T_k=\operatorname{Tr}N_k>0$。对 $w_k>0$ 置 $s_k=q_k'/q_k$，其中导数在 $t$ 取值。逐效应展开 SLD 剩余平方得
$$
\Delta=\sum_{k:w_k>0}
\left\|\sqrt{A_k}(L-s_kI)\sqrt{\sigma_t}\right\|_2^2
\ge\lambda\sum_{k:w_k>0}\operatorname{Tr}\bigl[A_k(L-s_kI)^2\bigr].
\tag{195.11}
$$
$\|\cdot\|_2$ 为 Hilbert–Schmidt 范数。若 $L$ 的本征值为 $\ell_+,\ell_-$，则对任意正效应 $A\ne0$ 和实数 $s$，
$$
A_{++}(\ell_+-s)^2+A_{--}(\ell_--s)^2
\ge g^2\frac{A_{++}A_{--}}{\operatorname{Tr}A}
\ge g^2\frac{|A_{+-}|^2}{\operatorname{Tr}A}.
\tag{195.12}
$$
第一步是关于 $s$ 的二次函数取最小值，第二步是 $A\succeq0$ 的二阶行列式条件。因此
$$
\Delta\ge\lambda g^2\sum_k\frac{w_k|o_k|^2}{T_k},\qquad
\left(\sum_k\sqrt{w_k}|o_k|\right)^2
\le\frac{2\Delta}{\lambda g^2}.
\tag{195.13}
$$
最后一步使用 Cauchy–Schwarz 与 $\sum_kT_k=2$；零 $w_k$ 项贡献为零，估计不依赖效应个数。

以下的 SLD 本征投影始终固定在名义点 $t$，不随参数求导。令 $\mathcal D_L$ 为 $L$ 本征基下的投影去相干映射，$\Pi_1=|1\rangle\langle1|$ 为信号态。完备性使 $\sum_k(N_k-\mathcal D_L(N_k))=0$，故对任意 Hermitian 程序算符 $Z$，
$$
(\mathcal E_0-\mathcal E_0\circ\mathcal D_L)(Z)
=\sum_k\operatorname{Tr}\bigl[(N_k-\mathcal D_L(N_k))Z\bigr](\tau_k-\Pi_1).
\tag{195.14}
$$
二维非对角 Hermitian 矩阵的算符范数为其非对角项模，所以该迹系数的绝对值不超过 $|o_k|\|Z\|_1$。另外，
$$
\|\tau_k-\Pi_1\|_1
\le2\sqrt{1-(\tau_k)_{11}}
=2\sqrt{\frac{2w_k}{3}}.
\tag{195.15}
$$
这一标准纯态距离界可直接验证：先对纯态 $|\psi\rangle$ 在它与 $|1\rangle$ 张成的平面中对角化差矩阵，得到 $2\sqrt{1-|\langle1|\psi\rangle|^2}$；再对 $\tau_k$ 的纯态分解使用迹范数凸性和平方根凹性。

将（195.13）—（195.15）合并，并用（195.6）—（195.7），得到
$$
\begin{aligned}
\|(\mathcal E_0-\mathcal E_0\circ\mathcal D_L)(Z)\|_1
&\le\frac4{\sqrt3}\frac{\sqrt\Delta}{\sqrt\lambda\,g}\|Z\|_1\\
&\le\frac4{\sqrt{3B}}\frac{\sqrt\delta}{R}\|Z\|_1.
\end{aligned}
\tag{195.16}
$$
这一步保留了当前处理器的测量—制备结构及（195.9）的输出权重，不是从一般 SLD 保留推出状态可恢复。一般量子模型中，SLD 信息量保留并不保证可恢复性；反例见 Gao、Li、Marvian、Rouzé，*Sufficient statistic and recoverability via Quantum Fisher Information metrics*，arXiv:2302.02341v1，命题1.1。式（195.11）的测量剩余平方来自 Braunstein–Caves，Physical Review Letters 72, 3439–3443（1994），DOI:10.1103/PhysRevLett.72.3439 的测量信息不等式及其等号机制。

现在定量使用二符号障碍。令 $C_+,C_-$ 取遍三维 Hermitian 正半定相关矩阵，即各自对角元全为一；令 $q\in[0,1]$、$z\in\mathbb R$ 满足
$$
z^2\le Q_*q(1-q).
\tag{195.17}
$$
这些变量构成非空紧集。在其上定义连续残差
$$
\mathcal R(C_+,C_-,q,z)=\max\left\{
\left\|\frac{F(a,t)-qC_+-(1-q)C_-}{3}\right\|_1,
\left\|\frac{E-z(C_+-C_-)}{3}\right\|_1
\right\},
\tag{195.18}
$$
其中 $E_{02}=E_{20}=1$，其余项为零。令 $\zeta$ 为该残差的最小值，则
$$
\zeta>0.
\tag{195.19}
$$
否则残差在某一点为零。若 $q=0$ 或 $1$，则（195.17）给出 $z=0$，无法匹配非零 $E$。若 $0<q<1$，两个相关矩阵的通道及概率值、导数 $q,z$ 构成一阶匹配的二符号经典程序，成本不超过 $Q_*<J_c$，违反定理184.3。因此紧集上没有零残差，证明（195.19）。此常数只依赖固定的 $a,t$。

对当前实际程序，取 SLD 本征投影 $P_+,P_-$，并令
$$
C_\pm=3\mathcal E_0(P_\pm),\qquad
q=\operatorname{Tr}(P_+\sigma_t),\qquad
z=\operatorname{Tr}(P_+\sigma_t').
\tag{195.20}
$$
受控 Stinespring 形式保证 $C_\pm$ 都是相关矩阵。满秩性给出 $0<q<1$，SLD 投影测量给出 $z^2/[q(1-q)]=Q\le Q_*$，故这些变量属于（195.17）的紧集。又因为
$$
\mathcal E_0(\sigma_t)=\frac{F(a,t)}3,\qquad
\mathcal E_0(\sigma_t')=\frac E3,\qquad
\|\sigma_t'\|_1=|s'(t)|\le\sqrt Q\le\sqrt{Q_*},
\tag{195.21}
$$
将（195.16）分别用于 $Z=\sigma_t$ 与 $Z=\sigma_t'$，得到
$$
\zeta\le K_*\frac{\sqrt\delta}{R},\qquad
K_*:=\frac{4\max\{1,\sqrt{Q_*}\}}{\sqrt{3B}}.
\tag{195.22}
$$
因此在 $Q\le Q_*$ 时有 $\delta\ge(\zeta^2/K_*^2)R^2$。若 $Q>Q_*$，则 $\delta>H$；又因 $R<d_t\le1-a<1$，有 $\delta\ge HR^2$。所以对全部实际程序统一成立
$$
I_Q(\rho_t)-B\ge c_1R^2,\qquad
c_1:=\min\left\{H,\frac{\zeta^2}{K_*^2}\right\}>0.
\tag{195.23}
$$
取下确界即得所需下界。

上界使用第193节的显式纯二维程序。它按固定 $a,t$ 给出常数 $C=1+\max_j(q_j/p_j)\ge2$，以及
$$
I_Q(\rho_t^{(\varepsilon)})=\frac B{1-C\varepsilon},\qquad
R_\varepsilon^2=\frac{4\varepsilon(1-\varepsilon)(1-C\varepsilon)}B.
\tag{195.24}
$$
这里 $R_\varepsilon$ 是该构造在名义点两侧的解析纯态定义半径，精确区间再与 $J_a$ 相交。取
$$
R_0=\min\left\{d_t,\frac1{\sqrt{2BC}}\right\},\qquad
0<R<R_0,\qquad \varepsilon=\frac{BR^2}{2}.
\tag{195.25}
$$
此时 $\varepsilon<1/(4C)$，故 $1-C\varepsilon>3/4$、$1-\varepsilon>3/4$，从而
$$
R_\varepsilon^2>\frac{9R^2}{8}>R^2.
\tag{195.26}
$$
所以该程序的精确开区间确实包含闭区间 $[t-R,t+R]$。其成本满足
$$
I_Q(\rho_t^{(\varepsilon)})-B
=\frac{BC\varepsilon}{1-C\varepsilon}
<\frac23CB^2R^2.
\tag{195.27}
$$
取 $c_2=2CB^2/3$，结合（195.23）得到（195.2）。所给 $c_1$ 通过固定有限维紧集上的正残差定义，$c_2$ 来自一个明确构造；二者都不被断言为最佳系数。证毕。

<a id="entry-740"></a>

## 追加锚（本行以下为增补区）

<a id="section-196"></a>

## 196. 纯二维程序的圆弧正规形、有限优化与确定的二次首项

**定理 196.1（圆弧替代与不可见转动的精确信息成本）。** 固定定义193.1中的一个纯二维程序、连通精确开区间 $U$ 及名义点 $t\in U$。存在使用同一处理器、定义在同一个 $U$ 上的解析纯态程序 $\widetilde\rho_u$，满足 $\widetilde\rho_t=\rho_t$，并在每个 $u\in U$ 同时满足
$$
\mathcal G(\omega\otimes\widetilde\rho_u)=\mathcal T_u(\omega),\qquad
I_Q(\widetilde\rho_u)\le I_Q(\rho_u).
\tag{196.1}
$$
替代程序的 Bloch 曲线位于一个平面圆弧上。若处理器的实 Bloch 到通道映射秩为二，则原程序本身已经是这样的解析圆弧。

证明。 令 $K=\ker\mathcal L$，其中 $\mathcal L$ 如（193.7）。第193节给出 $K\ne\{0\}$，而目标非恒定排除 $\mathcal L$ 的秩为零。将原 Bloch 曲线正交分解为
$$
r(u)=x(u)+b(u),\qquad
x(u)=P_{K^\perp}r(u)=x_0+(u-t)v,\qquad v\ne0.
\tag{196.2}
$$
$x(u)$ 的仿射性来自 $\mathcal L|_{K^\perp}$ 单射和目标通道仿射。其范数在每个 $u\in U$ 都严格小于一：若在内点等于一，两个充分小的对称位移之平方范数平均为 $1+s^2|v|^2>1$，与它们都是单位 Bloch 向量的投影矛盾。

因此在整个 $U$ 上可定义
$$
\beta(u)=\sqrt{1-|x(u)|^2}>0,\qquad e(u)=\frac{b(u)}{\beta(u)}\in K,\qquad |e(u)|=1.
\tag{196.3}
$$
$e$ 是 $C^1$ 曲线，且 $e\cdot e'=0$。由于 $v\perp K$，求导后所有交叉项消失，得到精确恒等式
$$
I_Q(\rho_u)=|r'(u)|^2
=|v|^2+\frac{(x(u)\cdot v)^2}{1-|x(u)|^2}
 +(1-|x(u)|^2)|e'(u)|^2.
\tag{196.4}
$$
取固定单位向量 $n=e(t)$，并定义
$$
\widetilde r(u)=x(u)+\sqrt{1-|x(u)|^2}\,n,
\qquad \widetilde\rho_u=\frac{I+\widetilde r(u)\cdot\sigma}{2}.
\tag{196.5}
$$
这是一条在整个 $U$ 上解析的纯态曲线。$n\in K$ 保证诱导通道与原曲线相同，在 $t$ 又有 $\widetilde r(t)=r(t)$。并且
$$
I_Q(\rho_u)-I_Q(\widetilde\rho_u)
=(1-|x(u)|^2)|e'(u)|^2\ge0.
\tag{196.6}
$$
该替代指定另一种程序准备，不断言它能由作用在原程序上的 CPTP 映射取得。

令 $x_\perp=x_0-(x_0\cdot v)v/|v|^2$。它同时垂直于 $v,n$，而（196.5）位于平面
$$
x_\perp+\operatorname{span}\{v,n\}
\tag{196.7}
$$
与单位球面的交圆上。圆心为 $x_\perp$，半径为 $\sqrt{1-|x_\perp|^2}>0$；正平方根选择其中的半圆弧或更小的弧。当 $\operatorname{rank}\mathcal L=2$ 时，$K$ 为一维，连续单位向量 $e(u)$ 在连通区间上只能恒定，所以原曲线已等于替代曲线。秩为一时，$x_0,v$ 共线，替代曲线是大圆弧，原曲线在二维核内的额外转动恰贡献（196.6）。证毕。

**定理 196.2（固定精确半径的有限优化等价式）。** 固定定义195.1中的 $a,t,R$。以 $\Phi_{\mathcal G}(x)$ 表示处理器在 Bloch 程序态 $(I+x\cdot\sigma)/2$ 下诱导的信号线性映射。令 $\mathscr F(a,t,R)$ 由有限变量 $(\mathcal G,n,x,v)$ 构成，要求 $\mathcal G:M_6\to M_3$ 为 CPTP，$n,x,v\in\mathbb R^3$，并满足
$$
\begin{gathered}
|n|^2=1,\qquad \mathcal L_{\mathcal G}n=0,\qquad
n\cdot x=n\cdot v=0,\\
\Phi_{\mathcal G}(x)=\mathcal T_t,\qquad
\mathcal L_{\mathcal G}v=\mathcal S_E,\\
|x-Rv|^2<1,\qquad |x+Rv|^2<1,
\end{gathered}
\tag{196.8}
$$
其中 $E_{02}=E_{20}=1$，其余项为零。于是
$$
\mathfrak P_2(a,t;R)
=\inf_{\mathscr F(a,t,R)}
\left[|v|^2+\frac{(x\cdot v)^2}{1-|x|^2}\right].
\tag{196.9}
$$
可行集非空；式中的分母严格为正。此等价式不要求下确界在可行集内达到。

证明。 对任意可行元，平方范数的凸性给出
$$
\max_{|s|\le R}|x+sv|^2
\le\max\{|x-Rv|^2,|x+Rv|^2\}<1.
\tag{196.10}
$$
由连续性，这个严格不等式在包含 $[-R,R]$ 的稍大开区间上仍成立，并可把对应的 $t+s$ 保持在 $J_a$ 内。令
$$
r(t+s)=x+sv+\sqrt{1-|x+sv|^2}\,n.
\tag{196.11}
$$
正交条件保证 $|r|=1$；处理器的三个线性约束保证它在该开区间内精确生成 $\mathcal T_{t+s}$。程序解析，且名义成本恰为
$$
|r'(t)|^2=|v|^2+\frac{(x\cdot v)^2}{1-|x|^2}.
\tag{196.12}
$$
因此原程序类的下确界不超过（196.9）右边。

反过来，任意原程序通过定理196.1得到同处理器的圆弧替代。取其 $x=x(t)$、$v=x'$、$n=e(t)$。因为 $t\pm R$ 都是原开区间的内部点，第196.1节的严格投影范数结论给出（196.8）的两个严格端点条件。其余约束来自同一正交分解和通道精确性。这是一个可行元，且（196.6）说明其目标值不超过原名义成本。取下确界即得反向不等式。

非空性还可直接展示。令 $d=1-a^2$、$b=2a^2-1$；固定处理器测量程序 $Z$，在两个结果下分别执行 $\mathcal T_1$ 与 $\mathcal T_b$，诱导参数为 $u=a^2+dr_z$。取
$$
n=e_x,\qquad x=\frac{t-a^2}{d}e_z,\qquad v=\frac1d e_z.
\tag{196.13}
$$
由于 $t\pm R\in J_a\subset(b,1)$，所有约束成立；其目标值为 $J_c=B/(1-a^2)$。因此下确界有限。端点条件取平均还给出 $|x|^2+R^2|v|^2<1$，特别地分母为正。证毕。

**定理 196.3（半代数成本与唯一正二次首项）。** 函数 $(a,t,R)\mapsto\mathfrak P_2(a,t;R)$ 在定义195.1的参数域上是半代数函数。存在一个正的有限函数 $\kappa(a,t)$，使每个固定的 $0<a<1$、$2a-1<t<1$ 都满足
$$
\mathfrak P_2(a,t;R)
=B(a,t)+\kappa(a,t)R^2+o(R^2)
\qquad(R\downarrow0).
\tag{196.14}
$$
$\kappa$ 关于 $(a,t)$ 联合半代数；若 $a,t$ 都是实代数数，则 $\kappa(a,t)$ 也是实代数数。

证明。 先把（196.8）写成有限实代数条件。处理器 $\mathcal G:M_6\to M_3$ 的未归一化 Choi 矩阵 $J_{\mathcal G}$ 为 $18\times18$ Hermitian 矩阵，满足
$$
J_{\mathcal G}\succeq0,\qquad
\operatorname{Tr}_{\rm out}J_{\mathcal G}=I_6.
\tag{196.15}
$$
以实对称部分和虚反对称部分作实坐标，全部主子式非负表达半正定性，保迹条件为线性方程。通道等式只需在信号矩阵空间的固定九元 Hermitian 基上检查；矩阵单位和 Pauli 矩阵的实、虚部系数为有理数，故（196.8）的其余约束成为有限个具有有理系数的实多项式等式或严格不等式。

令 $z$ 汇集这些有限变量，$\mathcal A(a,t,R,z)$ 表示可行性，并记
$$
D(z)=1-|x|^2>0,\qquad
N(z)=|v|^2D(z)+(x\cdot v)^2.
\tag{196.16}
$$
目标值为 $N/D$。在参数域内，$p=\mathfrak P_2(a,t;R)$ 等价于以下一阶实数公式：
$$
\begin{aligned}
&\forall z:\ \mathcal A(a,t,R,z)\ \Longrightarrow\ N(z)\ge pD(z),\\
&\forall\varepsilon>0\ \exists z:\
\mathcal A(a,t,R,z)\ \land\ N(z)<(p+\varepsilon)D(z).
\end{aligned}
\tag{196.17}
$$
第一行给出下界，第二行要求可行值任意接近该下界；它不要求最小值取得。非空性和有限性由定理196.2保证。所有乘去分母的步骤都发生在 $D>0$ 的可行域内。

对（196.17）使用 Tarski–Seidenberg 实数量词消去，得到具有有理系数的无量词多项式符号公式，所以成本函数的图是半代数集。所用标准结果及系数保持可参见 Saugata Basu，*Algorithms in Real Algebraic Geometry: A Survey*，arXiv:1409.1534v1，第2.1节定理2.1及第2.5.2节定理2.27；其第1.1节同时采用实数域与实代数数域作为实闭域实例。严格可行约束和下确界未取得都不妨碍这一量词消去。

现固定 $a,t$，令
$$
g(R)=\frac{\mathfrak P_2(a,t;R)-B(a,t)}{R^2}.
\tag{196.18}
$$
这是正半径上的半代数函数。定理195.2保证它在充分小半径内夹在两个固定的严格正常数之间。它在零的右极限必存在：若下极限与上极限不同，选一个严格位于二者之间的数 $c$，则 $\{R:g(R)<c\}$ 与 $\{R:g(R)>c\}$ 都在零点累积。每个实直线上的半代数集都是有限个区间和点的并，所以这两个互斥集合都必须包含一个 $(0,\eta)$，矛盾。这里的一维结构直接来自有限多个实多项式零点对直线的划分，无须额外正则性。于是
$$
\kappa(a,t):=\lim_{R\downarrow0}g(R)\in(0,\infty),
\tag{196.19}
$$
并得到（196.14）。该余项对每个固定的 $a,t$ 陈述，不断言参数间一致性。

$\kappa$ 的图也能用一阶公式定义。以 $\Gamma_P(a,t,R,p)$ 表示（196.17）及参数域条件，则 $k=\kappa(a,t)$ 等价于
$$
\begin{gathered}
\forall\varepsilon>0\ \exists\eta>0\ \forall R,p:\\
\bigl[\Gamma_P(a,t,R,p)\land R<\eta\bigr]
\ \Longrightarrow\
-\varepsilon R^2<p-B(a,t)-kR^2<\varepsilon R^2.
\end{gathered}
\tag{196.20}
$$
$\Gamma_P$ 已包含 $R>0$，且每个允许的 $a,t$ 都有任意小的允许半径，故此公式不空洞。$B$ 的分母在参数域内为正，可安全消去。再次使用实数量词消去，得到 $\kappa$ 的联合半代数性。

最后固定实代数的 $a,t$。（196.20）经量词消去后，以实代数系数的有限多项式符号条件刻画唯一单点 $\{\kappa(a,t)\}$。若该点不是实代数数，则这些非零多项式都不在该点为零；有限多个符号会在其某个开邻域内同时不变，与公式只刻画单点矛盾。因此该点是某个非零实代数系数多项式的根，进而对 $\mathbb Q$ 代数。

这确定了二次首项的存在与数域性质，没有给出 $\kappa$ 的数值、最小多项式或低成本计算方法，也不改变原优化中的下确界与最小值之别。证毕。

<a id="entry-742"></a>

## 追加锚（本行以下为增补区）

<a id="section-197"></a>

## 197. 得分的二次残差与纯二维程序的显式半径代价

**定义 197.1（三结果程序的得分矩）。** 固定 $0<a<1$、$2a-1<t<1$，取定理184.2以 $t$ 为设计点的三个固定通道及其仿射概率。记
$$
p_j=p_j(t)>0,\qquad v_j=p_j'(t),\qquad
s_j=\frac{v_j}{p_j},\qquad M_k=\sum_jp_js_j^k,
\qquad j\in\{+,-,c\}.
\tag{197.1}
$$
于是 $M_1=0$、$M_2=B=B(a,t)>0$。定义得分平方相对于常数与得分的加权二次残差
$$
V=\sum_jp_j\left(s_j^2-B-\frac{M_3}{B}s_j\right)^2
=M_4-B^2-\frac{M_3^2}{B}.
\tag{197.2}
$$
这里常数向量与得分向量在 $p$ 加权内积下正交，其平方范数分别为一与 $B$，故（197.2）确为正交投影残差。仿射概率的导数始终对参数求取，三个通道及设计点保持固定。

**定理 197.2（偏移圆弧的精确构造与显式首项上界）。** 定理196.3的二次首项满足
$$
0<\kappa(a,t)\le\frac V4
=\frac{a^2(1-a^2)^2}{2(1-t)^2(1+t-2a^2)^3}
=\frac{a^2B(a,t)^2}{2(1+t-2a^2)}.
\tag{197.3}
$$
存在一族纯二维程序，分别在包含 $[t-R,t+R]$ 的开邻域内精确生成目标通道，其名义成本满足
$$
I_Q(\rho_t^{(R)})
=B+\frac V4R^2+o(R^2)
\qquad(R\downarrow0).
\tag{197.4}
$$
每个程序使用一个固定的三结果秩一 POVM，随后执行定义197.1的相应固定通道。这里固定是指程序运行时不随未知参数变化；允许程序设计依赖 $a,t,R$。上界不主张该程序在所有处理器中最优。

证明。 先保留任意固定实数偏移系数 $\alpha$。对充分小的 $\varepsilon$ 与 $z$ 在一的邻域，令
$$
A_j(\varepsilon,z)=p_j-\alpha\varepsilon\sqrt z\,\frac{v_j}{\sqrt B},
\qquad
q_j(\varepsilon,z)=
\frac{2(1-\varepsilon)zv_j^2}
{B\left[A_j(\varepsilon,z)+
\sqrt{A_j(\varepsilon,z)^2-4\varepsilon(1-\varepsilon)zv_j^2/B}\right]}.
\tag{197.5}
$$
所有 $v_j$ 非零。在 $(\varepsilon,z)=(0,1)$ 附近，根号与分母严格为正，故这些函数实解析，并有
$$
q_j(0,z)=\frac{zv_j^2}{Bp_j},\qquad
\sum_jq_j(0,1)=1,\qquad
\partial_z\sum_jq_j(0,1)=1.
\tag{197.6}
$$
实解析隐函数定理遂给出 $z=z(\varepsilon)$，满足 $z(0)=1$、$z>0$ 及 $\sum_jq_j(\varepsilon,z(\varepsilon))=1$。下文的 $q_j$ 均沿此解析分支取值。式（197.5）是下列二次方程的小根在零点的解析延拓：
$$
\varepsilon q_j^2-
\left(p_j-\alpha\varepsilon\sqrt z\,\frac{v_j}{\sqrt B}\right)q_j
+(1-\varepsilon)z\frac{v_j^2}{B}=0.
\tag{197.7}
$$
令 $q_j^0=v_j^2/(Bp_j)$。在零点对该方程求导，再用 $\sum_jq_j'=0$，得到
$$
z'(0)=1-\sum_j\frac{(q_j^0)^2}{p_j}
-\frac\alpha{\sqrt B}\sum_j\frac{v_jq_j^0}{p_j}
=1-\frac{M_4}{B^2}-\alpha\frac{M_3}{B^{3/2}}.
\tag{197.8}
$$
本构造只要求 $z>0$，不额外要求 $z\le1$。

对充分小的正 $\varepsilon$，定义实对称效应
$$
N_j=
\begin{pmatrix}
\dfrac{p_j-\alpha\varepsilon\sqrt z\,v_j/\sqrt B-\varepsilon q_j}{1-\varepsilon}
&\dfrac{\sqrt z\,v_j}{\sqrt B}\\[2mm]
\dfrac{\sqrt z\,v_j}{\sqrt B}&q_j
\end{pmatrix}.
\tag{197.9}
$$
两个对角元严格为正，由（197.7）其行列式为零，故 $N_j$ 是正半定秩一矩阵。又因 $\sum_jv_j=0$、$\sum_jp_j=\sum_jq_j=1$，有 $\sum_jN_j=I_2$。因此测量 $\{N_j\}$ 并条件执行 $\mathcal R_j$ 定义一个固定 CPTP 处理器。

令 $\delta=u-t$，在下式根号严格为正的开区间上定义纯程序 Bloch 曲线
$$
r_\varepsilon(\delta)=
\left(
\alpha\varepsilon+\sqrt{B/z}\,\delta,
\sqrt{4\varepsilon(1-\varepsilon)-
       (\alpha\varepsilon+\sqrt{B/z}\,\delta)^2},
1-2\varepsilon
\right),
\qquad
\rho_{t+\delta}=\frac{I+r_\varepsilon(\delta)\cdot\sigma}{2}.
\tag{197.10}
$$
它为解析单位 Bloch 曲线。直接代入 Born 概率可见，式（197.9）的左上项与曲线横坐标中的偏移恰相消：
$$
\operatorname{Tr}(N_j\rho_{t+\delta})=p_j+\delta v_j.
\tag{197.11}
$$
所以处理器在该开区间与 $J_a$ 的交集上，对所有信号输入精确生成 $\mathcal T_{t+\delta}$。

在名义点，纯态 SLD 信息量为 Bloch 速度平方。由（197.10）有
$$
Q_\varepsilon:=I_Q(\rho_t)
=\frac Bz\,
\frac{4\varepsilon(1-\varepsilon)}
     {4\varepsilon(1-\varepsilon)-\alpha^2\varepsilon^2}.
\tag{197.12}
$$
结合（197.8），得到
$$
Q_\varepsilon-B
=B\varepsilon\left[
\frac{M_4}{B^2}-1+
\alpha\frac{M_3}{B^{3/2}}+\frac{\alpha^2}{4}
\right]+O(\varepsilon^2).
\tag{197.13}
$$

精确区间随偏移而不再关于零对称，所以还须验证完整的闭区间覆盖。取固定常数
$$
C_\alpha=1+\frac{|\alpha|B^{3/2}}4,
\qquad
\varepsilon_R=\frac B4R^2+C_\alpha R^3.
\tag{197.14}
$$
对固定的 $a,t,\alpha$，由 $z(\varepsilon_R)=1+O(R^2)$ 可得
$$
\begin{aligned}
&4\varepsilon_R(1-\varepsilon_R)
-\left(|\alpha|\varepsilon_R+
       \sqrt{B/z(\varepsilon_R)}\,R\right)^2\\
&\quad=
\left(4C_\alpha-\frac{|\alpha|B^{3/2}}2\right)R^3+O(R^4)
=\left(4+\frac{|\alpha|B^{3/2}}2\right)R^3+O(R^4)>0
\end{aligned}
\tag{197.15}
$$
只要 $R$ 充分小。左侧严格为正保证（197.10）的根号在整个 $[-R,R]$ 上严格为正，连续性再给出包含该闭区间的开域。取 $R<\min\{t-(2a-1),1-t\}$，亦可将开域限制在 $J_a$ 内。这个论证给出逐个固定参数的充分小半径结论，不给出所有允许半径的统一覆盖保证。

因为 $\varepsilon_R/R^2\to B/4$，式（197.13）给出
$$
\lim_{R\downarrow0}\frac{Q_{\varepsilon_R}-B}{R^2}
=\frac{B^2}{4}\left[
\frac{M_4}{B^2}-1+
\alpha\frac{M_3}{B^{3/2}}+\frac{\alpha^2}{4}
\right].
\tag{197.16}
$$
这个关于 $\alpha$ 的二次式在
$$
\alpha_*=-\frac{2M_3}{B^{3/2}}
\tag{197.17}
$$
处取得最小值 $V/4$。于是（197.4）成立；将每个实际程序的成本与定义195.1的下确界比较，再用定理196.3的极限，即得 $\kappa\le V/4$。这只优化当前显式构造中的偏移系数，没有把它升级为对所有处理器的极小性结论。

最后计算当前三结果程序的矩。记 $D=1+t-2a^2>0$、$\ell=(1-t)/2$、$q=D/2$、$d=1-a^2$、$c=a\ell/d$。由（184.9），三个得分分别为
$$
s_+=\frac{1-a}{2q},\qquad
s_-=\frac{1+a}{2q},\qquad
s_c=-\frac1{2\ell}.
\tag{197.18}
$$
为计算残差，取三个向量 $1,s,s^2$ 的加权 Gram 矩阵。其行列式既可按第一行展开，也可由三点 Vandermonde 矩阵分解，得到
$$
BV=
\det\begin{pmatrix}1&0&B\\0&B&M_3\\B&M_3&M_4\end{pmatrix}
=p_+p_-p_c\prod_{i<j}(s_i-s_j)^2.
\tag{197.19}
$$
这里 $p_+p_-p_c=q^2\ell/[4d(1-c^2)^2]$，三个得分差为 $a/q$、$d(1-c)/(2q\ell)$、$d(1+c)/(2q\ell)$。代入这些量与 $B=d/(4\ell q)$，并直接求取三阶矩，得到
$$
M_3=\frac{2d(a^2-t)}{(1-t)^2D^2},
\qquad
V=M_4-B^2-\frac{M_3^2}{B}
=\frac{2a^2d^2}{(1-t)^2D^3}.
\tag{197.20}
$$
因此（197.3）的两个显式表达相等。$V$ 的严格正性也可直接从（197.2）看出：两个正得分互不相同，第三个得分为负，若残差为零，则一个首项系数为一的二次多项式在这三个不同点都为零，矛盾。

若限制 $\alpha=0$，同一计算给出构造系数 $(M_4-B^2)/4$；允许偏移后，将其降低 $M_3^2/(4B)$，当且仅当 $t\ne a^2$ 时为严格改进。该变化来自同一精确程序中对得分平方的线性部分的消去，其余残差承担（197.4）的二次成本。

本证明沿用第193节的测量后条件执行通道构造与纯态 SLD 速度公式；经典程序信息成本的背景为 Matsumoto，*On metric of quantum channel spaces*，arXiv:1006.0300v1，第3.3节。实解析隐函数定理和加权正交投影仅作为标准工具用于上述具体 POVM 与半径构造，不以一般的一阶模拟代替这里的开邻域精确等式。证毕。

<a id="entry-744"></a>

## 追加锚（本行以下为增补区）

<a id="section-198"></a>

## 198. 有限仿射读出的纯二维成本：二次残差与二值得分的分界

**定义 198.1（有限仿射读出的精确程序成本）。** 给定有限个 $p_j>0$、$v_j\in\mathbb R$，其中 $j\in\{1,\ldots,m\}$、$m\ge2$，并要求向量 $v$ 非零且
$$
\sum_jp_j=1,\qquad \sum_jv_j=0.
\tag{198.1}
$$
令 $s_j=v_j/p_j$，允许重复得分与零得分。记
$$
B=\sum_jp_js_j^2>0,\qquad
M_k=\sum_jp_js_j^k,\qquad
V=M_4-B^2-\frac{M_3^2}{B}\ge0.
\tag{198.2}
$$
非负性来自（197.2）的加权投影残差恒等式。$V=0$ 当且仅当得分恰取两个不同值：残差为零要求一个首一二次多项式在所有得分处为零，而 $B>0$ 与零均值排除单值得分；反向由任意两点上的二次插值给出。对充分小的 $R>0$，令 $\mathfrak C_2(p,v;R)$ 为下列程序的名义 SLD 信息量下确界：固定 $m$ 结果 qubit POVM $\{N_j\}$，以及在某个包含 $[-R,R]$ 的开区间上的 $C^1$ 纯 qubit 曲线 $\rho_u$，满足
$$
\operatorname{Tr}(N_j\rho_u)=p_j+uv_j
\tag{198.3}
$$
对全部 $j$ 和该区间内的 $u$ 精确成立。区间限制在所有右侧概率都严格为正的范围内；名义点为 $u=0$。POVM 可随设计半径变化，但运行时与 $u$ 无关。

**定理 198.2（有限仿射读出的精确二次系数与二值得分边界）。** 在定义198.1的条件下，若得分至少取三个不同值，则 $V>0$ 且
$$
\mathfrak C_2(p,v;R)=B+\frac V4R^2+o(R^2)
\qquad(R\downarrow0).
\tag{198.4}
$$
若得分恰取两个不同值，则对每个闭区间 $[-R,R]$ 包含于正概率区间内的 $R$，都有 $\mathfrak C_2(p,v;R)=B$，且由同一个在整个正概率区间上精确的纯程序达到。

特别地，若处理器被限制为先作三结果 qubit 测量、再执行第184.2节在固定设计点选择的三个通道，则其纯程序的最优二次系数正是第197.3式的显式上界。此限制下的等号不决定任意 CPTP 处理器类中的 $\kappa(a,t)$。

证明。 先处理二值得分。记两得分为 $s_-<0<s_+$，对应的组概率为 $P_\pm=\sum_{j:s_j=s_\pm}p_j$。令 $W_\pm(u)=P_\pm(1+s_\pm u)$，取纯态向量 $\psi_u=\sqrt{W_+(u)}|0\rangle+\sqrt{W_-(u)}|1\rangle$。对每个组内结果 $j$，取效应 $N_j=(p_j/P_\pm)|\pm\rangle\langle\pm|$，其中 $|+\rangle=|0\rangle$、$|-\rangle=|1\rangle$。这些效应归一，给出精确概率 $p_j(1+s_j u)$；纯态信息量在零点为 $P_+s_+^2+P_-s_-^2=B$。测量信息下界给出反向不等式，故达到 $B$。整个正概率区间内平方根解析，结论同时适用于其中的每个闭区间。

以下假定至少三种不同得分，因此 $V>0$。式（197.5）—（197.17）的构造对任意有限结果数保持相同的归一与矩公式。若 $v_j=0$，相应小根 $q_j$ 和非对角项恒为零，效应为 $\operatorname{diag}(p_j/(1-\varepsilon),0)$，仍为正半定秩一；其余结果沿用原来的严格正对角论证。因此把固定通道省去，便得到满足（198.3）的 POVM 与纯态曲线，并给出
$$
\limsup_{R\downarrow0}
\frac{\mathfrak C_2(p,v;R)-B}{R^2}\le\frac V4.
\tag{198.5}
$$
测量的 SLD 信息不等式给出每个实际程序的成本 $Q\ge B$。以下证明匹配下界。

先排除只有一个可见 Bloch 方向的测量。若从 Bloch 向量到结果概率的线性部分秩为一，则所有效应同时对角化。它等价于先作一个二结果投影测量，再由固定随机矩阵产生 $m$ 个结果。记两个条件概率向量为 $P_-,P_+$，名义二结果权重为 $\lambda$，其导数为 $\dot\lambda\ne0$。因为目标概率沿直线 $p+uv$ 变化，两个 $P_\pm$ 均在该直线上。记相应坐标为 $u_-<0<u_+$。纯程序信息量不小于该二结果测量的信息量，即
$$
Q\ge\frac1{(-u_-)u_+}.
\tag{198.6}
$$
令 $s_{\min}=\min_js_j<0<s_{\max}=\max_js_j$。直线上所有概率非负的完整区间是 $[-1/s_{\max},-1/s_{\min}]$，所以
$$
Q\ge-s_{\min}s_{\max}>B.
\tag{198.7}
$$
严格性由
$$
-s_{\min}s_{\max}-B
=\sum_jp_j(s_j-s_{\min})(s_{\max}-s_j)>0
\tag{198.8}
$$
给出：至少一个得分严格位于两极值之间且权重为正。秩零不能产生非零的 $v$；秩三亦不可能，因为单射的 Bloch 线性部分会迫使原纯曲线为非恒定仿射直线，而单位球面不含这样的开线段。因此余下只需处理秩二情形。

对秩二测量，令 $K$ 为从 Bloch 向量到概率的线性映射之核。$K$ 为一维；精确等式（198.3）迫使 $K^\perp$ 中的投影沿非恒定仿射直线运动。该投影在精确开区间的每一点都严格位于单位圆盘内，否则两个充分小对称位移的平方范数平均会超过一。故核方向分量不为零，在连通区间内符号固定。

选择可见平面中的坐标，使投影速度沿 $X$、垂直速度的坐标非负；把核方向作为 $Y$。以 $c>0$ 表示可见速度，原纯程序可写成
$$
r(u)=\left(x+cu,\ \pm\sqrt{H^2-(x+cu)^2},\ 1-2\varepsilon\right),
\qquad
H^2=4\varepsilon(1-\varepsilon),\qquad
0<\varepsilon\le\frac12.
\tag{198.9}
$$
核分量的符号不影响以下成本。POVM 效应在这个坐标中为实对称矩阵，写作
$$
N_j=\begin{pmatrix}A_j&b_j\\b_j&q_j\end{pmatrix},
\qquad b_j=\frac{v_j}{c},\qquad
A_j=\frac{p_j-b_jx-\varepsilon q_j}{1-\varepsilon}.
\tag{198.10}
$$
每个效应满足 $0\preceq N_j\preceq I$，且 $\sum_jq_j=1$。纯态信息量及精确闭区间的必要条件为
$$
Q=\frac{c^2H^2}{H^2-x^2},\qquad
|x|+cR<H.
\tag{198.11}
$$
端点仍是精确开区间的内部点，所以不等式严格。

考虑任意 $R_n\downarrow0$ 的程序序列，满足 $Q_n-B=O(R_n^2)$。秩一情形由固定正差距（198.7）排除。以下证明其秩二参数必满足
$$
\varepsilon_n\to0,\qquad
c_n^2\to B,\qquad
\frac{x_n^2}{\varepsilon_n}\to0.
\tag{198.12}
$$
因 $|b_j|\le1$ 且某个 $v_j\ne0$，有 $c\ge\max_j|v_j|>0$；又由（198.11）有 $c^2\le Q$，故速度有上下界。若沿某子列 $\varepsilon\ge\varepsilon_0>0$，则 $H^2$ 有正下界，而 $Q$ 的有界性给出
$$
H^2-x^2=\frac{c^2H^2}{Q}
\tag{198.13}
$$
也有正下界。

去掉 Bloch 向量的 $Y$ 分量，得到满秩影子状态
$$
\sigma_0=\frac{I+xX+(1-2\varepsilon)Z}{2},
\qquad \sigma_0'=\frac{cX}{2}.
\tag{198.14}
$$
所有效应都看不到 $Y$，所以其输出仍为 $p,v$。直接用 qubit SLD 公式可知影子成本恰为（198.11）的 $Q$。由（198.13），其最小特征值一致地远离零；效应、状态与导数遂可取收敛子列。极限中测量的信息量为 $B$，影子的量子信息量也为 $B$，因此达到满秩 SLD 测量等号。若 $L$ 为极限 SLD，等号要求
$$
\sqrt{N_j}(L-s_jI)\sqrt{\sigma_0}=0.
\tag{198.15}
$$
满秩性允许消去右侧因子，故每个非零效应的支持必须在 $L$ 的特征值 $s_j$ 对应空间内。所有 $p_j$ 都严格为正，因而所有效应都非零；至少三种不同得分要求二维 Hermitian 矩阵具有至少三个不同特征值，矛盾。这证明 $\varepsilon_n\to0$。所用支持敏感等号为 Braunstein–Caves，Physical Review Letters 72, 3439（1994），DOI:10.1103/PhysRevLett.72.3439，式（24）—（26）；这里先建立满秩界再使用等号，不把去掉 $Y$ 的操作当作一般 CPTP 映射。

现在 $|x|<H$ 给出 $x\to0$，式（198.10）给出 $A_j\to p_j$。半正定性意味着 $b_j^2\le A_jq_j$，所以
$$
\frac{B}{c^2}=\sum_j\frac{b_j^2}{p_j}
\le\sum_j\frac{A_jq_j}{p_j}=1+o(1).
\tag{198.16}
$$
结合 $c^2\le Q\to B$，得到 $c^2\to B$；再由（198.11）得到 $x^2/H^2\to0$，从而完成（198.12）。

令 $z=B/c^2$。正性约束（198.10）等价于
$$
\varepsilon q_j^2-
\left(p_j-\sqrt z\,\frac{v_j}{\sqrt B}x\right)q_j
+(1-\varepsilon)z\frac{v_j^2}{B}\le0.
\tag{198.17}
$$
在 $(\varepsilon,x,z)=(0,0,1)$ 附近，将其小根用有理化表达延拓为实解析函数 $f_j(\varepsilon,x,z)$。其形式与（197.5）相同，只把 $\alpha\varepsilon$ 替换为 $x$。实际效应满足 $q_j\ge f_j$，故 $\sum_jf_j\le1$。由于在该点 $\partial_z\sum_jf_j=1$，归一方程 $\sum_jf_j=1$ 定义唯一局部解析函数 $z_*(\varepsilon,x)$，且邻域内 $\sum_jf_j$ 对 $z$ 严格递增。因此
$$
z\le z_*(\varepsilon,x).
\tag{198.18}
$$
令 $A=M_4/B^2-1$、$k=M_3/B^{3/2}$。分别对归一方程求导给出
$$
z_*(\varepsilon,x)=1-A\varepsilon-kx
+O\bigl((\varepsilon+|x|)^2\bigr).
\tag{198.19}
$$
因为（198.12）把所有低成本序列送入这个同一局部邻域，该展开可用于每个这样的序列，而不预先假定 $x/\varepsilon$ 有界。

令 $T=\varepsilon+x^2/\varepsilon$，则（198.12）给出 $T\to0$。由（198.11）、（198.18）及 $|x|\le T/2$，可取只依赖 $p,v$ 的常数 $K>0$，使
$$
Q-B\ge B\left[A\varepsilon+kx+\frac{x^2}{4\varepsilon}\right]
-KT^2.
\tag{198.20}
$$
对充分小的 $T$ 成立。这个余项界直接来自解析函数倒数及几何因子的展开：$\varepsilon+|x|=O(T)$，所以前者的二阶余项为 $O(T^2)$；$x^2/[4\varepsilon(1-\varepsilon)]=x^2/(4\varepsilon)+O(T^2)$，其平方与两个一阶项的乘积同样为 $O(T^2)$。因此该估计在所有趋近（198.12）区域的序列上使用同一个局部常数，不要求先有界化 $x/\varepsilon$。

关键在于这不是可能退化的二次式。由 $A-k^2=V/B^2>0$，
$$
A\varepsilon+kx+\frac{x^2}{4\varepsilon}
=\frac VB^2\varepsilon+
\varepsilon\left(\frac{x}{2\varepsilon}+k\right)^2
\ge c_0\left(\varepsilon+\frac{x^2}{\varepsilon}\right)
\tag{198.21}
$$
对某个只依赖 $p,v$ 的 $c_0>0$ 成立；最后一步是变量 $\sqrt\varepsilon,x/\sqrt\varepsilon$ 上正定二次式的最小特征值界。因此（198.20）和 $Q-B=O(R^2)$ 迫使
$$
\varepsilon=O(R^2),\qquad
\frac{x^2}{\varepsilon}=O(R^2),\qquad x=O(R^2).
\tag{198.22}
$$
这在使用有界偏移展开之前排除了其他退化速率。

闭区间条件（198.11）又给出 $4\varepsilon(1-\varepsilon)>c^2R^2$，故
$$
\liminf\frac{\varepsilon}{R^2}\ge\frac B4.
\tag{198.23}
$$
将（198.21）的平方项丢去，并用（198.22）把余项化为 $o(R^2)$，即得每个低成本序列都满足
$$
\liminf\frac{Q-B}{R^2}
\ge\frac VB\liminf\frac{\varepsilon}{R^2}
\ge\frac V4.
\tag{198.24}
$$
对下确界，在每个 $R_n$ 选择成本不超过 $\mathfrak C_2(p,v;R_n)+R_n^3$ 的实际程序。式（198.5）保证该序列满足上述低成本假设；（198.24）遂给出下确界的匹配下界，结合（198.5）证明（198.4）。整个论证不要求最优程序存在。

最后，定理184.2的三个固定通道在其相关矩阵坐标 $(1,a,h)$ 上分别为 $(1,1,1)$、$(1,-1,1)$、$(1,c,c^2)$，对应行列式非零，因为 $|c|<1$。所以它们的仿射混合权重由目标通道唯一确定，正是（184.5）的三概率。要求测量后仅执行这三个通道，遂与（198.3）的固定仿射读出问题等价。将（197.20）的 $V$ 代入即可得到所述受限处理器的精确系数；允许其他处理器会扩大优化域，本定理没有对该扩大域证明同样下界。证毕。

<a id="entry-746"></a>

## 追加锚（本行以下为增补区）

<a id="section-199"></a>

## 199. 任意纯二维处理器的精确二次成本：算子相关矩阵锁定极限

**定义 199.1（圆弧程序的分块相关矩阵域）。** 固定定义195.1的 $a,t,R$，记 $F=F(a,t)$、$E_{02}=E_{20}=1$ 且其余 $E$ 元素为零。令 $\mathscr M(a,t,R)$ 由参数 $\varepsilon,x,c,C$ 构成，其中
$$
0<\varepsilon\le\frac12,\qquad c>0,\qquad x\in\mathbb R,
\qquad C=C^T\in M_3(\mathbb R),\qquad \operatorname{diag}C=\mathbf1,
\tag{199.1}
$$
并要求
$$
\Gamma=
\begin{pmatrix}
\dfrac{F-xE/c-\varepsilon C}{1-\varepsilon}&E/c\\[2mm]
E/c&C
\end{pmatrix}\succeq0,
\qquad
|x|+cR<\sqrt{4\varepsilon(1-\varepsilon)}.
\tag{199.2}
$$
定义该参数的名义成本
$$
Q(\varepsilon,x,c)
=\frac{4c^2\varepsilon(1-\varepsilon)}
       {4\varepsilon(1-\varepsilon)-x^2}.
\tag{199.3}
$$
式（199.2）使分母严格为正，也使 $C$ 自动成为相关矩阵。

**定理 199.2（六维分块矩阵与全部处理器的精确优化等价）。** 对定义199.1的参数，
$$
\mathfrak P_2(a,t;R)
=\inf_{\mathscr M(a,t,R)}Q(\varepsilon,x,c).
\tag{199.4}
$$
可行集非空，且其中每个参数都满足 $1\le c\le\sqrt Q$。该等价式允许原始程序使用任意固定 CPTP 处理器，不预设其为测量—制备处理器，也不要求下确界达到。

证明。 先从任意原始程序出发。定理196.1将其替换为使用同一处理器、同一完整精确开区间的圆弧程序，名义成本不增加。将圆弧平面中的仿射投影速度作为 $X$ 方向，将固定的不可见方向作为 $Y$，圆心方向作为 $Z$ 并取非负坐标，可写成
$$
r(t+u)=
\left(x+cu,\ \pm\sqrt{h^2-(x+cu)^2},\ 1-2\varepsilon\right),
\qquad h^2=4\varepsilon(1-\varepsilon),
\tag{199.5}
$$
其中 $c>0$、$0<\varepsilon\le1/2$。大圆对应 $\varepsilon=1/2$，因此这一写法亦包括秩一可见映射的圆弧替代。原开区间包含闭区间，故根号在两个端点都严格为正，得到（199.2）的严格覆盖条件。速度平方即为（199.3）。

依第191.3、194.1节的受控 Stinespring 论证，存在等距映射 $W_i:\mathbb C^2\to\mathcal E$，使处理器的等距扩张为
$$
V(|i\rangle\otimes\psi)=|i\rangle\otimes W_i\psi,
\qquad W_i^\dagger W_i=I_2.
\tag{199.6}
$$
令 $K_{ij}=W_i^\dagger W_j$，则算子 Gram 矩阵 $K=(K_{ij})\succeq0$，且 $K_{ii}=I_2$。须保留指标方向：程序状态 $\rho$ 诱导的 Schur 系数为
$$
F_\rho{}_{ij}=\operatorname{Tr}(\rho K_{ji}).
\tag{199.7}
$$
不可见 $Y$ 方向意味着 $\operatorname{Tr}(YK_{ji})=0$，所以每个二阶程序块满足 $K_{ij}^T=K_{ij}$；这一步尚不意味着各块为 Hermitian。

现在把整个 Gram 矩阵替换为
$$
K^{\mathbb R}=\frac{K+\overline K}{2}.
\tag{199.8}
$$
它仍正半定，且对角块仍为 $I_2$。它整体为实对称矩阵，各程序块也为实对称矩阵，因此 $K^{\mathbb R}_{ji}=K^{\mathbb R}_{ij}$。由于每个原块都看不到程序的 $Y$ 分量，沿同一条纯曲线有
$$
\operatorname{Tr}(\rho K^{\mathbb R}_{ji})
=\operatorname{Re}\operatorname{Tr}(\rho K_{ji})
=F(a,t+u)_{ij}.
\tag{199.9}
$$
这构造了另一组合法 Gram 数据，不声称对未知量子输入作复共轭是一条物理通道。实化可以改变可见映射的秩；所得处理器仍属于这里的完整优化域。

按程序基先分组，将 $K^{\mathbb R}$ 重排为 $\left(\begin{smallmatrix}U&A\\A&C\end{smallmatrix}\right)$，其中三个块均为实对称三阶矩阵，$\operatorname{diag}U=\operatorname{diag}C=\mathbf1$、$\operatorname{diag}A=0$。沿（199.5）的 Schur 矩阵为
$$
(1-\varepsilon)U+\varepsilon C+(x+cu)A=F+uE.
\tag{199.10}
$$
比较值与导数，得到 $A=E/c$ 及 $U=(F-xE/c-\varepsilon C)/(1-\varepsilon)$，恰为（199.2）。因此每个原始程序对应一个可行参数，成本不超过原成本。

反过来，给定可行的 $\Gamma$，按信号指标重新分块，其程序块为 $\left(\begin{smallmatrix}U_{ij}&E_{ij}/c\\E_{ij}/c&C_{ij}\end{smallmatrix}\right)$。Gram 分解给出 $W_i^\dagger W_j=K_{ij}$，而对角块 $I_2$ 保证（199.6）为等距映射。对环境取偏迹即得 CPTP 处理器。各块实对称且 $K_{ji}=K_{ij}$，故（199.7）与（199.10）给出对全部信号输入的精确目标通道。严格覆盖条件使（199.5）在包含所需闭区间的稍大开域上解析，亦可将其限制在 $J_a$ 内。因此该参数产生名义成本恰为 $Q$ 的实际程序，证明下确界的反向不等式。

第184.3节的两端点程序保证原程序类非空，故矩阵域非空。$\Gamma$ 的六个对角元均为一，其 $E/c$ 块中存在元素 $1/c$；对应二阶主子式非负给出 $c\ge1$。式（199.3）给出 $Q\ge c^2$。证毕。

**定理 199.3（任意处理器的二次首项与显式极限矩阵）。** 对每个固定的 $0<a<1$、$2a-1<t<1$，
$$
\boxed{
\mathfrak P_2(a,t;R)
=B(a,t)+\frac{a^2B(a,t)^2}{2(1+t-2a^2)}R^2+o(R^2)
}
\qquad(R\downarrow0).
\tag{199.11}
$$
特别地，定理196.3的系数为
$$
\kappa(a,t)=\frac{a^2(1-a^2)^2}
{2(1-t)^2(1+t-2a^2)^3}.
\tag{199.12}
$$
记 $d=1-a^2$、$D=1+t-2a^2$、$\eta=(a^2-t)/d$。在定义199.1的可行参数中，任意成本趋向 $B$ 的序列都满足
$$
\varepsilon\to0,\qquad c^2\to B,\qquad
\frac{x^2}{\varepsilon}\to0,\qquad
C\longrightarrow C_0:=
\begin{pmatrix}1&0&\eta\\0&1&0\\\eta&0&1\end{pmatrix}.
\tag{199.13}
$$
这里的极限只涉及固定 $a,t$，不要求精确区间具有共同正半径。

证明。 首先证明（199.13）。因为 $1\le c\le\sqrt Q$，成本趋于 $B$ 时 $c$ 有固定上下界；$\Gamma$ 是六阶相关矩阵，所以它及其子块属于固定紧集。若某子列 $\varepsilon\ge\varepsilon_0>0$，则 $h^2=4\varepsilon(1-\varepsilon)$ 有正下界，而
$$
h^2-x^2=\frac{c^2h^2}{Q}
\tag{199.14}
$$
也有正下界。取收敛子列，极限分块矩阵仍正半定，且极限圆弧在名义点附近有一个真正的开定义域。按定理199.2的反向构造，它给出名义成本恰为 $B$ 的局部精确纯二维程序，与定理194.1的严格不达到性矛盾。因此 $\varepsilon\to0$，进而 $x\to0$。

上左块趋向正定的 $F$，故充分靠后可取 Schur 补，得到
$$
C\succeq\frac{1-\varepsilon}{c^2}\,
E\left(F-\frac xcE-\varepsilon C\right)^{-1}E.
\tag{199.15}
$$
取 $00$ 对角元并用 $(EF^{-1}E)_{00}=B$，得到 $c^2\ge B+o(1)$。结合 $c^2\le Q\to B$，可知 $c^2\to B$；再用（199.3）可知 $x^2/\varepsilon\to0$。

任一 $C$ 的聚点 $C_\infty$ 满足
$$
C_\infty\succeq\frac{EF^{-1}E}{B},\qquad
\operatorname{diag}C_\infty=\mathbf1.
\tag{199.16}
$$
右侧矩阵的对角为 $(1,0,1)$。因此正半定残差的对角为 $(0,1,0)$，其第零和第二行列必须全部为零。这迫使
$$
C_\infty=\frac{EF^{-1}E}{B}+|1\rangle\langle1|=C_0.
\tag{199.17}
$$
聚点唯一，故整个序列收敛，完成（199.13）。

现在提取二次成本。记
$$
A_3=(EF^{-1}EF^{-1}E)_{00},\qquad
A_C=(EF^{-1}C_0F^{-1}E)_{00}.
\tag{199.18}
$$
由（199.15）的 $00$ 对角元及逆矩阵的一阶展开，沿上述低成本序列有
$$
c^2-B\ge
\frac{A_3}{\sqrt B}x+(A_C-B)\varepsilon
+o(|x|+\varepsilon).
\tag{199.19}
$$
展开合法因为 $F$ 正定、$C$ 一致有界且 $c$ 有正下界。未给速率的 $C-C_0$ 总是乘以 $\varepsilon$，所以贡献 $o(\varepsilon)$；将 $1/c$ 替换为 $1/\sqrt B$ 贡献 $o(|x|)$。不需要预先控制 $C$ 的收敛速度。

这两个矩阵系数可直接计算。由
$$
F^{-1}e_2=
\begin{pmatrix}\eta B\\-a/D\\B\end{pmatrix},\qquad
B(1-\eta^2)=\frac1d,
\tag{199.20}
$$
得到
$$
A_3=2\eta B^2,\qquad
A_C=B^2(1+3\eta^2)+\frac{a^2}{D^2}.
\tag{199.21}
$$
令 $A=A_C/B-1$、$k=A_3/B^{3/2}=2\eta\sqrt B$，则
$$
A-k^2
=B(1-\eta^2)+\frac{a^2}{BD^2}-1
=\frac{2a^2}{D}>0.
\tag{199.22}
$$
它也等于第197节的 $V/B^2$，但（199.20）—（199.22）直接从任意处理器的极限矩阵取得该数。

设 $T=\varepsilon+x^2/\varepsilon$。式（199.13）使 $T\to0$，且 $|x|\le T/2$。结合（199.3）、（199.19）得到
$$
Q-B\ge
B\left(A\varepsilon+kx+\frac{x^2}{4\varepsilon}\right)+o(T).
\tag{199.23}
$$
括号中的二次式满足
$$
A\varepsilon+kx+\frac{x^2}{4\varepsilon}
=\frac{2a^2}{D}\varepsilon
+\varepsilon\left(\frac{x}{2\varepsilon}+k\right)^2
\ge c_0T
\tag{199.24}
$$
对某个固定 $c_0>0$ 成立。因此任何 $R\downarrow0$ 且 $Q-B=O(R^2)$ 的可行序列都满足 $T=O(R^2)$。由严格覆盖条件，
$$
4\varepsilon(1-\varepsilon)>c^2R^2,
\qquad
\liminf\frac{\varepsilon}{R^2}\ge\frac B4.
\tag{199.25}
$$
将（199.24）的平方项丢去，余项因 $T=O(R^2)$ 而为 $o(R^2)$，故
$$
\liminf\frac{Q-B}{R^2}
\ge\frac{2a^2B}{D}\liminf\frac{\varepsilon}{R^2}
\ge\frac{a^2B^2}{2D}.
\tag{199.26}
$$
定理197.2给出相同系数的实际程序上界。由定理199.2，在任意半径序列上选择成本与下确界相差至多 $R^3$ 的可行参数；结合定理193.2的成本下界，所得参数满足 $Q-B=O(R^2)$，所以（199.26）适用。上下界匹配即得（199.11）与（199.12）。

因此，第197节的三结果测量—制备构造已经在二次首项上达到任意固定处理器类的最优值。这不主张它在每个正半径处取得最小值，也不主张各处理器类的高阶项相同。全部推导保留开邻域精确性、固定程序维数与同一处理器内的联合矩阵正性；Gram 分解与 Schur 补只作为该具体优化的标准工具。固定处理器与程序输入的标准框架可参见 Hillery、Ziman、Bužek，*Implementation of quantum maps by programmable quantum processors*，Physical Review A 66, 042302（2002），DOI:10.1103/PhysRevA.66.042302，第II节。证毕。

<a id="entry-748"></a>

## 追加锚（本行以下为增补区）

<a id="section-200"></a>

## 200. 二维最优程序的满秩刚性与最大精确续接区间

**定义 200.1（二维名义最优程序与续接域）。** 固定 $0<a<1$、$t\in J_a=(2a-1,1)$，令 $\mathcal T_u=\mathcal S_{F(a,u)}$、$I_r(u)=1/(1-u^2)$。本节的程序由一个固定 CPTP 处理器 $\mathcal G:M_6\to M_3$、一个包含 $t$ 的连通开区间 $U\subset J_a$ 和其上的 $C^1$ 二维密度矩阵曲线组成，满足
$$
\mathcal G(\omega\otimes\rho_u)=\mathcal T_u(\omega)
\quad(u\in U),\qquad
I_Q(\rho_t)=I_r(t).
\tag{200.1}
$$
通道等式针对全部信号输入，不只针对一个选定探针；任何点都不预先规定程序秩。这里 $I_Q$ 取点态 SLD 值 $\operatorname{Tr}(\rho_tL^2)$，其中 $\rho_t'= (L\rho_t+\rho_tL)/2$；不将跨秩的度量极限代作该点值。记
$$
h_0=\frac{1+t}{2},\qquad
A_0=\frac{at}{h_0},\qquad
B_0=2a\sqrt{\frac{1-t}{1+t}},\qquad
\lambda_*:=\frac{B_0}{\sqrt{1-A_0^2}}.
\tag{200.2}
$$
由 $h_0>a$ 及 $A_0^2+B_0^2=a^2/h_0^2<1$，可知 $0<\lambda_*<1$。

**定理 200.2（名义等号强制全区间仿射正规形）。** 每个定义200.1的程序，经过一个不依赖 $u$ 的程序酉坐标变换，都在整个 $U$ 上具有形式
$$
\rho_u=\frac12\left(I+x_\lambda(u)X+uZ\right),\qquad
x_\lambda(u)=\frac{\lambda(1-tu)}{\sqrt{1-t^2}},
\qquad \lambda_*\le\lambda<1.
\tag{200.3}
$$
该程序在全部 $U$ 上满秩。反过来，对每个 $\lambda\in[\lambda_*,1)$，存在固定 CPTP 处理器使（200.3）在
$$
U_\lambda=J_a\cap\{u:q_\lambda(u)>0\},\qquad
q_\lambda(u)=1-u^2-\frac{\lambda^2}{1-t^2}(1-tu)^2
\tag{200.4}
$$
上满足定义200.1。每个原程序的精确开区间都包含于其对应的 $U_\lambda$。

证明。 先取任意程序的 Stinespring 等距表示 $V$。对每个 $u\in U$，输入 $|i\rangle\langle i|\otimes\rho_u$ 的信号输出为纯态 $|i\rangle\langle i|$。分解 $\rho_u$ 在其支持上的正权本征投影，利用输出在 $|i\rangle$ 正交补上的概率为零及各分量非负，可知 $V$ 把 $|i\rangle\otimes\operatorname{supp}\rho_u$ 映入 $|i\rangle\otimes\mathcal E$。所有程序支持的线性包必须是整个二维空间；否则所有密度矩阵都为同一个一维投影，诱导通道恒定，与目标随 $u$ 变化矛盾。故由线性性，
$$
V=\sum_{i=0}^2|i\rangle\langle i|\otimes W_i,
\qquad W_i^\dagger W_i=I_2.
\tag{200.5}
$$
这是在整个联合输入空间上的恒等式，不只沿已给程序曲线成立。

以均衡 $02$ 信号输入并读取 $|+\rangle,|-\rangle$，在程序空间得到 POVM
$$
M_\pm=\frac12(I\pm\operatorname{Re}A),\qquad
A=W_2^\dagger W_0,
\qquad p_\pm(u)=\frac{1\pm u}{2}.
\tag{200.6}
$$
这项读出的经典信息量为 $I_r$，故它在 $t$ 饱和 SLD 测量信息界。设 $L$ 为 $\rho_t$ 的 SLD，$s_+=1/(1+t)$、$s_-=-1/(1-t)$。支持敏感的测量等号条件给出
$$
\sqrt{M_\pm}L\sqrt{\rho_t}
=s_\pm\sqrt{M_\pm}\sqrt{\rho_t}.
\tag{200.7}
$$
此标准条件来自逐效应 Hilbert–Schmidt Cauchy–Schwarz 等号；参见 Braunstein、Caves，*Statistical distance and the geometry of quantum states*，Physical Review Letters **72**, 3439–3443（1994），DOI:10.1103/PhysRevLett.72.3439，式（24）—（27）。

两个效应非零，而 $s_+\ne s_-$。若 $\rho_t$ 满秩，则可在（200.7）右消去 $\sqrt{\rho_t}$，两个效应分别支持于 $L$ 的两个不同一维本征空间。若 $\rho_t=|\psi\rangle\langle\psi|$ 为纯态，则该式变成 $\sqrt{M_\pm}L\psi=s_\pm\sqrt{M_\pm}\psi$。任一效应若可逆便推出 $L\psi=s_\pm\psi$，但 $\langle\psi,L\psi\rangle=\operatorname{Tr}\rho_t'=0$，与 $s_\pm\ne0$ 矛盾。所以此时两个效应也都为秩一。两种情形下，两个秩一正效应之和为单位算子，必为互补正交投影。

纯态处的 SLD 使用是点态的：在以 $\psi$ 为第一基向量的坐标中，双侧 $C^1$ 正性使核上的对角导数为零，迹为零又使另一个对角导数为零；余下的非对角导数有 Hermitian SLD 解。因此上述论证没有从满秩公式跨秩取极限。选定投影测量的固定程序坐标后，
$$
M_\pm=\frac12(I\pm Z),\qquad
\operatorname{Re}A=Z.
\tag{200.8}
$$
压缩算子 $A$ 在 $Z$ 的两个本征向量上的实期望值已分别达到 $1,-1$，所以对应的范数与 Cauchy–Schwarz 界均饱和，得 $A=Z$。再由等距性得到 $W_2=W_0Z$。这两条恒等式属于固定处理器，因而适用于全部 $U$。

令 $h(u)=(1+u)/2$、$\ell(u)=(1-u)/2$。由于（200.6）的测量已为 $Z$ 投影，程序可写为
$$
\rho_u=\begin{pmatrix}h(u)&\overline{z(u)}\\z(u)&\ell(u)\end{pmatrix}.
\tag{200.9}
$$
记 $K=W_0^\dagger W_1=\left(\begin{smallmatrix}\alpha&\beta\\\gamma&\delta\end{smallmatrix}\right)$，则 $\|K\|\le1$。两个固定的实 Schur 系数分别给出 $\operatorname{Tr}(\rho_uK)=a$ 和 $\operatorname{Tr}(\rho_uZK)=a$；其中第一式可从实际 $01$ 系数取复共轭取得。相加相减，得到整个 $U$ 上的两个复数恒等式
$$
\alpha h(u)+\beta z(u)=a,\qquad
\gamma\overline{z(u)}+\delta\ell(u)=0.
\tag{200.10}
$$
若 $\beta=0$，第一式要求固定 $\alpha$ 与非恒定 $h$ 的乘积恒为非零常数 $a$，不可能。因此 $\beta\ne0$，并且 $z(u)=(a-\alpha h(u))/\beta$ 在整个 $U$ 上为仿射函数。

式（200.9）及 $z$ 的仿射性使整个 Bloch 曲线成为非恒定仿射线，其 $Z$ 坐标的导数为一。这样的线不能在 $U$ 的内点接触单位球面：若 $|r(u_0)|=1$，对充分小的 $s>0$，两点平方范数的平均为 $1+s^2|r'|^2>1$，而两点都须为合法态。故程序在整个 $U$ 上满秩，名义点为纯态的情形已经排除。

现在可在（200.7）消去 $\sqrt{\rho_t}$，得到唯一的 $L=\operatorname{diag}(1/(1+t),-1/(1-t))$。将它代入 SLD 方程 $\rho_t'=(L\rho_t+\rho_tL)/2$ 的 $10$ 元，得到
$$
z'(t)=-\frac{t}{1-t^2}z(t).
\tag{200.11}
$$
仿射性于是强制
$$
z(u)=z(t)\frac{1-tu}{1-t^2}\qquad(u\in U).
\tag{200.12}
$$
$z(t)$ 不能为零，否则 $z$ 恒为零，再与（200.10）第一式矛盾。以一个固定对角程序酉变换令 $z(t)>0$，并置 $\lambda=2z(t)/\sqrt{1-t^2}$。名义满秩性给出 $0<\lambda<1$，而（200.12）恰为（200.3）。

将该表达代回（200.10），逐项比较仿射系数，得到
$$
K=\begin{pmatrix}A_0&B_0/\lambda\\0&0\end{pmatrix}.
\tag{200.13}
$$
下行消失是因为 $1-tu$ 与 $1-u$ 线性无关：两者若成比例便要求 $t=1$，与 $t\in J_a$ 矛盾。因此压缩条件给出
$$
A_0^2+\frac{B_0^2}{\lambda^2}\le1,
\qquad \lambda\ge\lambda_*.
\tag{200.14}
$$
至此没有假定处理器的 Bloch 映射单射；程序的全区间仿射性由两个固定的通道系数直接推出。

式（200.3）的正性等价于 $q_\lambda(u)\ge0$。这个严格凹二次式满足 $q_\lambda(t)=(1-\lambda^2)(1-t^2)>0$，所以有两个不同实根，并只在两根之间为正。一个由合法态组成且包含 $t$ 的开区间不能包含任一根，否则根外侧也须属于该开区间而使 $q_\lambda<0$。故 $q_\lambda>0$ 在全部 $U$ 成立，证明满秩性与域的包含关系。

反向构造取（200.13）的压缩算子，使用
$$
W_0=\begin{pmatrix}I_2\\0\end{pmatrix},\qquad
W_2=\begin{pmatrix}Z\\0\end{pmatrix},\qquad
W_1=\begin{pmatrix}K\\\sqrt{I_2-K^\dagger K}\end{pmatrix}.
\tag{200.15}
$$
即使 $\lambda=\lambda_*$ 时 $\|K\|=1$，根号仍正半定，三个 $W_i$ 仍为等距映射。以信号基控制它们，再取环境偏迹，便得到固定 CPTP 处理器。第191.2节的计算对这里的闭端点参数同样成立：$ZK=K$，而 $A_0h(u)+(B_0/\lambda)x_\lambda(u)/2=a$，故三个目标 Schur 系数分别为 $a,a,u$。由第191.2节的满秩信息公式，
$$
I_Q(\rho_u)-I_r(u)
=\frac{\lambda^2(u-t)^2}
{(1-t^2)(1-u^2)q_\lambda(u)}.
\tag{200.16}
$$
它在 $t$ 为零；（200.4）上程序解析且满秩，完成反向构造。证毕。

**定理 200.3（全部最优二维程序共享的最大续接域）。** 记
$$
b_\pm^*(a,t)=
\frac{a^2t\pm\sqrt{(h_0^2-a^2)(h_0^2-a^2t^2)}}{h_0^2}.
\tag{200.17}
$$
定义200.1中所有允许精确区间均包含于
$$
U_*(a,t)=(b_-^*,b_+^*)\cap J_a,
\tag{200.18}
$$
且存在一个程序以整个 $U_*$ 为精确区间。因此 $U_*$ 是这个程序类按包含关系的最大续接域。它也可写为
$$
U_*(a,t)=\left\{u\in J_a:
 h_0^2(1-u^2)>a^2(1+t^2-2tu)\right\}.
\tag{200.19}
$$
有 $-1<b_-^*<t<b_+^*<1$。对任意满足 $[t-R,t+R]\subset J_a$ 的 $R>0$，存在定义200.1的程序在包含该闭区间的开域上精确，当且仅当
$$
R<R_*(a,t):=
\frac{\sqrt{(h_0^2-a^2)(h_0^2-a^2t^2)}
-|t|(h_0^2-a^2)}{h_0^2}.
\tag{200.20}
$$

证明。 对固定 $u\in J_a$，式（200.4）随正参数 $\lambda$ 严格递减，因为 $|tu|<1$。故在 $\lambda\ge\lambda_*$ 的全部正规形中，$\lambda=\lambda_*$ 的正性区间包含其他全部正性区间。定理200.2的反向构造允许这个端点，遂同时给出普遍上界及其达到。

将（200.2）化简得
$$
\frac{\lambda_*^2}{1-t^2}
=\frac{a^2}{h_0^2-a^2t^2}.
\tag{200.21}
$$
分母严格为正。于是
$$
(h_0^2-a^2t^2)q_{\lambda_*}(u)
=h_0^2(1-u^2)-a^2(1+t^2-2tu).
\tag{200.22}
$$
右边为严格凹二次式，解其两个根即得（200.17）—（200.19）。它在 $u=t$ 为正，而在 $u=\pm1$ 分别为 $-a^2(1\mp t)^2<0$，故两根严格位于 $-1,t,1$ 的相应间隙。

一个包含闭区间 $[t-R,t+R]$ 的允许开域存在，等价于两个端点严格位于 $(b_-^*,b_+^*)$ 内；与 $J_a$ 的严格包含已由假设保证。因此条件为
$$
R<\min\{t-b_-^*,b_+^*-t\}.
\tag{200.23}
$$
两根中点为 $a^2t/h_0^2$，半宽为（200.17）中的根号除以 $h_0^2$，将名义点到中点的距离减去便得（200.20）。等号 $R=R_*$ 不允许，因为至少一个端点落在物理区间的根上，无法再有包含它的合法开延拓。

这里控制的是点态 SLD 名义等号的精确续接域；式（200.16）同时显示，在域内离开名义点便有正的信息额外成本。结论不要求一个程序在整个 $U_*$ 处处达到 $I_r$，也不从超过该半径时的不达到性推出严格为正的最优成本差距。定理200.2还排除了第191.4节单独保留的名义纯态、邻域变秩的等号情形；这里无需预设恒秩。证毕。

<a id="entry-750"></a>

## 追加锚（本行以下为增补区）

<a id="section-201"></a>

## 201. 混态二维精确成本的半径阈值：达到、临界不达到与正差距

**定义 201.1（允许混态的固定半径成本）。** 固定 $0<a<1$、$t\in J_a=(2a-1,1)$ 及
$$
0<R<\min\{t-(2a-1),1-t\}.
\tag{201.1}
$$
令 $\mathfrak M_2(a,t;R)$ 为全部二维程序的名义点态 SLD 信息量下确界，其中程序允许为混态、允许秩变化，要求一个固定 CPTP 处理器在某个包含 $[t-R,t+R]$ 的连通开区间 $U\subset J_a$ 上，对全部信号输入精确产生 $\mathcal T_u$，程序密度矩阵曲线为 $C^1$。这里的点态信息量采用定义200.1的 SLD 约定。与纯程序成本的关系为
$$
I_r(t)\le\mathfrak M_2(a,t;R)\le\mathfrak P_2(a,t;R)<\infty.
\tag{201.2}
$$
第一个不等式来自均衡 $02$ 读出的测量信息界，第二个来自程序类的包含关系；有限性由第184.3节的两个固定端点通道程序给出。

**定理 201.2（全部混态程序的仿射替代与有限优化）。** 每个定义201.1的程序均可在同一处理器、同一完整 $U$ 上替换为一个解析满秩仿射程序 $\sigma_u$，在每个 $u\in U$ 都满足
$$
\mathcal G(\omega\otimes\sigma_u)=\mathcal T_u(\omega),\qquad
I_Q(\sigma_u)\le I_Q(\rho_u).
\tag{201.3}
$$
令 $\Phi_{\mathcal G}(b)$ 表示 Bloch 程序 $(I+b\cdot\sigma)/2$ 诱导的信号映射，$\mathcal L_{\mathcal G}$ 表示它对 $b$ 的实线性部分。令 $E_{02}=E_{20}=1$，其他 $E$ 元素为零。以 $\mathscr A_R$ 表示满足
$$
\begin{gathered}
\mathcal G:M_6\to M_3\ \text{为 CPTP},\qquad b,v\in\mathbb R^3,\\
\Phi_{\mathcal G}(b)=\mathcal T_t,\qquad
\mathcal L_{\mathcal G}(v)=\mathcal S_E,\\
|b-Rv|<1,\qquad |b+Rv|<1
\end{gathered}
\tag{201.4}
$$
的有限变量集合，则
$$
\mathfrak M_2(a,t;R)
=\inf_{\mathscr A_R}\left[|v|^2+
\frac{(b\cdot v)^2}{1-|b|^2}\right].
\tag{201.5}
$$
这不宣称下确界在严格端点域内达到。

证明。 对给定程序，令 $K=\ker\mathcal L_{\mathcal G}$，并正交分解其 Bloch 向量
$$
r(u)=x(u)+y(u),\qquad x(u)\in K^\perp,\quad y(u)\in K.
\tag{201.6}
$$
目标通道仿射，而 $\mathcal L_{\mathcal G}|_{K^\perp}$ 单射，所以 $x(u)=b+(u-t)v$，其中 $v\ne0$。它的范数在 $U$ 上处处严格小于一：投影先给出 $|x|\le1$，若某内点达到一，非恒定仿射线两侧的平方范数平均便严格大于一，矛盾。因此 $\sigma_u=(I+x(u)\cdot\sigma)/2$ 是整个 $U$ 上的解析满秩曲线，且 $y$ 不可见保证它产生同一目标通道。

信息量比较可直接处理秩边界。在原态满秩的一个点，记
$$
A=1-|x|^2>0,\qquad q=A-|y|^2>0,\qquad
\alpha=x\cdot v,\qquad w=y'+\frac{\alpha}{A}y.
\tag{201.7}
$$
代入二维满秩 SLD 公式并完成平方，得到精确恒等式
$$
I_Q(\rho_u)-I_Q(\sigma_u)
=|w|^2+\frac{(y\cdot w)^2}{q}\ge0,
\qquad I_Q(\sigma_u)=|v|^2+\frac{\alpha^2}{A}.
\tag{201.8}
$$
若原态在该点为纯态，双侧 $C^1$ 正性给出 $r\cdot r'=0$，点态 SLD 公式给出 $I_Q(\rho_u)=|r'|^2$。此时 $|y|^2=A>0$，且 $y\cdot y'=-\alpha$，所以 Cauchy–Schwarz 给出
$$
I_Q(\rho_u)=|v|^2+|y'|^2
\ge |v|^2+\frac{\alpha^2}{A}=I_Q(\sigma_u).
\tag{201.9}
$$
这也覆盖原曲线只在孤立点为纯态的情形。若 $K=\{0\}$，原曲线本来就是上述满秩仿射曲线。这里构造的是另一种状态准备；未把 Bloch 正交投影宣称为 CPTP 操作。所用 SLD 与测量信息框架见 Braunstein、Caves，Physical Review Letters **72**, 3439–3443（1994），DOI:10.1103/PhysRevLett.72.3439，式（24）—（26）；秩边界使用点态表达，不从满秩分母公式取极限。

仿射替代在两个闭区间端点仍满秩，所以每个原程序给出（201.4）的一个可行元，且（201.5）的目标值不超过原名义成本。反过来，对任意可行元，平方范数的凸性使 $|b+sv|<1$ 在 $|s|\le R$ 成立。两个端点均严格，故可取包含该闭区间的稍大开域并保持 $t+s\in J_a$。在此域准备 Bloch 向量 $b+sv$，两个通道线性约束给出对所有信号输入的精确 $\mathcal T_{t+s}$，其名义成本恰为（201.5）。两向比较完成证明。

**定理 201.3（精确半径的三个成本区间）。** 以定理200.3的 $b_+^*(a,t)$ 定义
$$
R_0(a,t)=b_+^*(a,t)-t>0.
\tag{201.10}
$$
对定义201.1的每个允许半径，成立
$$
\begin{array}{c|c|c}
\text{半径条件}&\mathfrak M_2(a,t;R)&\text{名义下界的达到性}\\ \hline
R<R_0&I_r(t)&\text{由一个实际程序达到}\\
R=R_0&I_r(t)&\text{无实际程序达到}\\
R>R_0&>I_r(t)&\text{与下界有严格正差距}
\end{array}
\tag{201.11}
$$
每一行均以该半径同时满足（201.1）为条件，不要求临界半径对所有 $a,t$ 都属于允许范围。最后一行的正差距依赖固定的 $a,t,R$，不在参数变化时主张统一下界。

证明。 先把定理200.3的最大域在 $J_a$ 内化简。令 $\ell_a=2a-1$，并记
$$
P_*(u)=h_0^2(1-u^2)-a^2(1+t^2-2tu),\qquad h_0=\frac{1+t}{2}.
\tag{201.12}
$$
直接计算给出
$$
P_*(\ell_a)=a(t-\ell_a)(1-\ell_at)>0.
\tag{201.13}
$$
两个因子为正，因为 $\ell_a<t$ 且 $|\ell_at|<1$。因此 $b_-^*<\ell_a$，最大域是 $(\ell_a,b_+^*)$。当 $R<R_0$ 且（201.1）成立时，$\lambda=\lambda_*$ 的程序在包含所需闭区间的开域精确，且名义成本为 $I_r(t)$。由（201.2）便得第一行。当 $R=R_0$ 时，闭区间的上端点为 $b_+^*$；定理200.2、200.3排除任何名义等号程序具有所需开延拓，包括名义点发生秩变化的候选。

临界点虽不达到，却可逼近。设 $\mathcal G_*$、$\sigma_z$ 为 $\lambda=\lambda_*$ 的程序，定义于 $(\ell_a,b_+^*)$。令 $\mathcal C_1(X)=\mathcal T_1(\operatorname{Tr}_P X)$ 为忽略程序并对信号施行 $\mathcal T_1$ 的 CPTP 处理器。对 $0<s<1$，取
$$
\mathcal G_s=(1-s)\mathcal G_*+s\mathcal C_1,
\qquad z_s(u)=\frac{u-s}{1-s},\qquad
\rho_u^{(s)}=\sigma_{z_s(u)}.
\tag{201.14}
$$
$\mathcal T_z$ 关于 $z$ 仿射，故在 $z_s(u)\in(\ell_a,b_+^*)$ 时，对所有信号输入有
$$
\mathcal G_s(\omega\otimes\rho_u^{(s)})
=(1-s)\mathcal T_{z_s(u)}(\omega)+s\mathcal T_1(\omega)
=\mathcal T_u(\omega).
\tag{201.15}
$$
该程序的精确开域为
$$
V_s=\bigl(s+(1-s)\ell_a,\ s+(1-s)b_+^*\bigr)\subset J_a.
\tag{201.16}
$$
其上端点严格大于 $b_+^*=t+R_0$。临界半径允许时，$t-R_0>\ell_a$，所以充分小的 $s>0$ 又使下端点严格小于 $t-R_0$。于是 $V_s$ 包含整个临界闭区间。

在名义点附近 $\sigma_z$ 满秩且解析，故其信息量 $\widehat I(z)$ 连续，且 $\widehat I(t)=I_r(t)$。参数变换的链式法则给出
$$
I_Q(\rho_t^{(s)})
=\frac{\widehat I(z_s(t))}{(1-s)^2}
\longrightarrow I_r(t)\qquad(s\downarrow0).
\tag{201.17}
$$
每个 $s$ 使用一个固定处理器；混合权不随运行参数 $u$ 变化。结合普遍下界与临界不达到性，得到第二行。

最后证明第三行的严格差距，而不仅是不达到。把（201.4）的两个严格端点条件放宽为 $|b\pm Rv|\le1$，得到闭集合 $\overline{\mathscr A}_R$。这里的横线仅指这个指定的闭松弛，不预先断言它等于 $\mathscr A_R$ 的拓扑闭包。端点平方范数取平均给出
$$
|b|^2+R^2|v|^2\le1.
\tag{201.18}
$$
对每个闭松弛可行元，固定均衡 $02$ 信号输入，并在输出读取范数为一的可观测量 $X_{02}=|0\rangle\langle2|+|2\rangle\langle0|$。把这个可观测量经程序到输出的 CPTP 映射拉回，得到一个程序 Hermitian 压缩算子 $H=mI+w\cdot\sigma$，所以 $|w|\le1$。两个通道等式使相应期望沿 $b+sv$ 的导数为一，因此
$$
w\cdot v=1,\qquad |v|\ge1,
\qquad |b|^2\le1-R^2.
\tag{201.19}
$$
所以名义状态一致远离纯态边界，且目标函数分母 $1-|b|^2\ge R^2>0$。有限维 CPTP 映射集合的 Choi 表示紧，式（201.18）使 $b,v$ 有界；约束均闭，故 $\overline{\mathscr A}_R$ 为非空紧集，目标函数在其上连续。记它的最小值为 $m_R$，则
$$
\mathfrak M_2(a,t;R)\ge m_R\ge I_r(t).
\tag{201.20}
$$
第二个不等式成立，因为任一闭松弛元在名义点附近仍给出满秩的精确仿射程序；无需在半径端点外延拓就能应用测量信息界。

若 $m_R=I_r(t)$，其一个最小元在名义邻域达到等号，因而满足定理200.2的正规形，参数 $\lambda\ge\lambda_*$。该正规形与最小元的 Bloch 曲线都仿射；它们在邻域相等，故作为仿射函数处处相等。闭端点正性于是迫使
$$
t+R\le b_+(\lambda)\le b_+^*(a,t),
\tag{201.21}
$$
其中第二个不等式来自 $q_\lambda\le q_{\lambda_*}$。这与 $R>R_0$ 矛盾。因此 $m_R>I_r(t)$，取 $\delta(a,t,R)=m_R-I_r(t)>0$ 即得
$$
\mathfrak M_2(a,t;R)\ge I_r(t)+\delta(a,t,R).
\tag{201.22}
$$
这里没有把闭松弛的最小值等同于严格开延拓问题的下确界，也没有求出超临界成本的精确函数。三行分别给出实际达到、只能逼近及由紧性保证的正差距，证明完成。

<a id="entry-752"></a>

## 追加锚（本行以下为增补区）

<a id="section-202"></a>

## 202. 超临界续接成本的二次起步：等距转动与等号稳定性

**定义 202.1（允许的临界点及转动参数）。** 固定定义201.1的 $a,t$，令 $b=b_+^*(a,t)$、$R_0=b-t$，并假设
$$
0<R_0<\min\{t-(2a-1),1-t\}.
\tag{202.1}
$$
沿用第200节的 $A_0,\lambda_*$，另记
$$
\beta_*:=\sqrt{1-A_0^2},\qquad
x_*(u)=\frac{2a-A_0(1+u)}{\beta_*}
=\frac{\lambda_*(1-tu)}{\sqrt{1-t^2}},
\qquad q_*(u)=1-u^2-x_*(u)^2,
\tag{202.2}
$$
以及
$$
\gamma=\frac{2(a-A_0)}{\beta_*}>0,\qquad
v_*=-\frac{2\gamma x_*(b)}{q_*'(b)}>0,
\qquad
\Lambda=\frac{2}{(1-t)(1+t)^2}
+\frac{t^2\gamma^2}{(1-t^2)q_*(t)}>0.
\tag{202.3}
$$
这些量均针对固定的 $a,t$。正性由 $a-A_0=a(1-t)/(1+t)>0$、$x_*(b)>0$、$q_*(t)>0$ 以及上根的 $q_*'(b)<0$ 保证。

**定理 202.2（转动处理器给出的显式二次上界）。** 在定义202.1的参数域内，
$$
\limsup_{\delta\downarrow0}
\frac{\mathfrak M_2(a,t;R_0+\delta)-I_r(t)}{\delta^2}
\le\frac{\Lambda}{v_*^2}<\infty.
\tag{202.4}
$$
其中充分小的正 $\delta$ 均保持半径合法。这个上界由固定二维程序输入与三维环境的实际 CPTP 处理器族给出。

证明。 令环境标准基为 $e_0,e_1,e_2$，取充分小的实设计参数 $s$，并定义
$$
\begin{aligned}
&W_0=(e_0,e_1),\\
&W_2=\left(e_0,-(1-2s^2)e_1+2s\sqrt{1-s^2}\,e_2\right),\\
&f_s=se_1+\sqrt{1-s^2}\,e_2,\qquad
v=(A_0,\beta_*)^T,\quad v^\perp=(-\beta_*,A_0)^T,\\
&W_1=e_0v^T+f_s(v^\perp)^T.
\end{aligned}
\tag{202.5}
$$
各 $W_i:\mathbb C^2\to\mathbb C^3$ 都为等距映射。用信号基控制它们，再对环境取偏迹，得到对全部联合输入定义的固定 CPTP 处理器 $\mathcal G_s$；每个 $s$ 的处理器不随运行参数 $u$ 变化。直接求重叠得到
$$
W_0^\dagger W_1=W_2^\dagger W_1
=\begin{pmatrix}A_0&\beta_*\\-s\beta_*&sA_0\end{pmatrix},
\qquad
W_2^\dagger W_0=\operatorname{diag}(1,-1+2s^2).
\tag{202.6}
$$
准备实仿射 Bloch 曲线
$$
r_s(u)=\bigl(x_s(u),0,z_s(u)\bigr),\qquad
x_s(u)=\frac{x_*(u)+\gamma s}{1-s^2},\qquad
z_s(u)=\frac{u-s^2}{1-s^2}.
\tag{202.7}
$$
实际 Schur 系数取 $\operatorname{Tr}(\rho W_j^\dagger W_i)$。由于程序实对称，（202.6）的两个相邻系数都为
$$
A_0(h+s\ell)+\frac{\beta_*(1-s)x_s(u)}2=a,
\qquad h=\frac{1+z_s(u)}2,\quad\ell=\frac{1-z_s(u)}2;
\tag{202.8}
$$
另一个系数为 $s^2+(1-s^2)z_s(u)=u$。因此在程序物理的每个 $u\in J_a$ 上，对所有信号输入精确产生 $\mathcal T_u$。

满秩条件的分子是
$$
\begin{aligned}
D_s(u)
&=(1-s^2)^2-[x_*(u)+\gamma s]^2-(u-s^2)^2\\
&=q_*(u)-2\gamma x_*(u)s-[2(1-u)+\gamma^2]s^2.
\end{aligned}
\tag{202.9}
$$
$D_0$ 的上根 $b$ 是单根，故隐函数定理给出实解析的邻近上根 $b(s)$，满足
$$
b(0)=b,\qquad
b'(0)=\frac{2\gamma x_*(b)}{q_*'(b)}=-v_*<0.
\tag{202.10}
$$
所以负 $s$ 将上端点一阶向外推。名义点与下端点在临界时已有严格物理余量；第201.3节还给出 $b_-^*<2a-1<t-R_0$，故这些余量在小扰动下保持。

计算名义成本时，全部状态处于名义点的满秩邻域。对任意实平面 Bloch 曲线 $(x,0,z)$，SLD 公式可改写为
$$
I_Q=\frac{(z')^2}{1-z^2}
+\frac{[(1-z^2)x'+zz'x]^2}
{(1-z^2)(1-z^2-x^2)},
\tag{202.11}
$$
其中撇号对运行参数 $u$ 求导。对（202.7），第一项为
$$
\frac1{(1-u)(1+u-2s^2)}.
\tag{202.12}
$$
在 $u=t$，第二项的分子括号于 $s=0$ 为零，其对 $s$ 的一阶导数为 $t\gamma$；分母于零为 $(1-t^2)q_*(t)>0$。因此名义成本 $Q_s$ 满足
$$
Q_s-I_r(t)=\Lambda s^2+o(s^2).
\tag{202.13}
$$
此处用了 $x_*'(t)=-t x_*(t)/(1-t^2)$，以及（202.12）相对 $I_r(t)$ 的二次系数 $2/[(1-t)(1+t)^2]$。

对小的 $\delta>0$，利用（202.10）选择负 $s=s(\delta)$，使
$$
b(s)=b+\delta+\delta^2,
\qquad s(\delta)=-\frac{\delta}{v_*}+O(\delta^2).
\tag{202.14}
$$
上端点严格超过 $t+R_0+\delta$，下端点的固定余量仍在，故程序具有包含半径 $R_0+\delta$ 闭区间的合法开延拓。代入（202.13）即得（202.4）。这是一族确定的处理器与程序准备，没有参数依赖的后选择。证毕。

**定理 202.3（严格二次下界与唯一正首项）。** 在定义202.1的参数域内，存在 $\kappa_{\mathrm m}(a,t)\in(0,\infty)$，使
$$
\boxed{
\mathfrak M_2(a,t;R_0+\delta)
=I_r(t)+\kappa_{\mathrm m}(a,t)\delta^2+o(\delta^2)
}
\qquad(\delta\downarrow0),
\tag{202.15}
$$
并有 $\kappa_{\mathrm m}\le\Lambda/v_*^2$。成本及该首项系数在相应参数域上半代数；实代数 $a,t$ 给出实代数的 $\kappa_{\mathrm m}(a,t)$。本节不确定该系数的精确值。

证明。 首先证明二次归一下确界严格为正。反设存在 $\delta_n\downarrow0$，使成本额外量为 $o(\delta_n^2)$。选择与下确界相差至多 $\delta_n^3$ 的实际程序，并用定理201.2作同域仿射替代，可得可行元 $(\mathcal G_n,b_n,v_n)$，名义成本 $Q_n$ 满足
$$
g_n:=Q_n-I_r(t)=o(\delta_n^2),\qquad g_n\ge0,
\qquad R_n=R_0+\delta_n.
\tag{202.16}
$$
由（201.18）、（201.19），这些元有界，名义状态一致满秩，且 $|v_n|$ 有固定上界。取收敛子列，极限属于半径 $R_0$ 的闭松弛，目标函数连续且等于 $I_r(t)$。一致名义满秩界使极限在 $t$ 附近仍是一个实际的满秩开域程序，故定理200.2适用；该局部结论与极限曲线均为仿射，因而确定其整个参数线。它属于参数 $\lambda\ge\lambda_*$ 的正规形。上端点正性与 $q_{\lambda_*}(b)=0$ 又迫使 $\lambda=\lambda_*$。因此，作一个固定程序坐标变换后，极限就是（202.2）的状态曲线及其投影读出。

下面所有 $O(\cdot)$ 的常数只依赖这条子列的一个固定邻域及固定 $a,t$。记名义状态为 $\rho_n\succeq\mu I$，其中 $\mu>0$ 一致；$L_n$ 为其 SLD。完整二结果读出为 $M_{\pm,n}$，其概率固定为 $(1\pm t)/2$，得分为
$$
s_+=\frac1{1+t},\qquad s_-=-\frac1{1-t}.
\tag{202.17}
$$
支持敏感的测量信息差给出精确恒等式
$$
g_n=\sum_{j=\pm}
\left\|\sqrt{M_{j,n}}(L_n-s_jI)\sqrt{\rho_n}\right\|_{\mathrm{HS}}^2
\ge\mu\sum_{j=\pm}\operatorname{Tr}\bigl(M_{j,n}(L_n-s_jI)^2\bigr).
\tag{202.18}
$$
这是 Braunstein–Caves 测量界的平方余项，直接展开即可验证；本节两个概率始终正。支持条件的原始表述见 Physical Review Letters **72**, 3439–3443（1994），DOI:10.1103/PhysRevLett.72.3439，式（24）—（26）。

对每个 $n$，用一个不随运行参数变化的程序酉变换对角化 $H_n=M_{+,n}-M_{-,n}$，并按极限的两个本征值标号。谱间隙趋于二，可以选择这些坐标使极限仍为 $Z$。在此坐标中写
$$
M_{+,n}=\operatorname{diag}(1-e_{+,n},e_{-,n}),
\qquad e_{\pm,n}\ge0,\quad e_{\pm,n}\to0.
\tag{202.19}
$$
名义状态与其导数的收敛、统一满秩性保证 $L_n\to S:=\operatorname{diag}(s_+,s_-)$。若 $L_n$ 的两个对角元为 $\ell_+,\ell_-$、非对角元为 $z$，则（202.18）右侧除以 $\mu$ 后的迹和为
$$
\begin{aligned}
&2|z|^2+(1-e_+)(\ell_+-s_+)^2+e_+(\ell_+-s_-)^2\\
&\qquad +e_-(\ell_--s_+)^2+(1-e_-)(\ell_--s_-)^2.
\end{aligned}
\tag{202.20}
$$
各项非负，且两个得分有固定非零间隙。因此
$$
e_{\pm,n}=O(g_n),\qquad L_n-S=O(\sqrt{g_n}).
\tag{202.21}
$$
令 $H_n=\alpha_n I+\beta_nZ$，则 $\alpha_n=O(g_n)$、$\beta_n=1-O(g_n)$。精确读出在整个仿射曲线上满足
$$
r_{z,n}(u)=\frac{u-\alpha_n}{\beta_n},
\qquad r_{z,n}'=1+O(g_n).
\tag{202.22}
$$

名义点的非对角元趋于 $\lambda_*\sqrt{1-t^2}/2>0$。用固定对角酉变换令它为正实数 $\zeta_n$，并设 $\lambda_n=2\zeta_n/\sqrt{1-t^2}\to\lambda_*$。SLD 方程及（202.21）给出
$$
\rho_{10,n}'(t)=-\frac{t}{1-t^2}\zeta_n+O(\sqrt{g_n}).
\tag{202.23}
$$
程序本身仿射，所以在一切有界的参数位置，其 Bloch 向量都与参数 $\lambda_n$ 的第200节正规形相差 $O(\sqrt{g_n})$。这个比较也适用于所需的两个闭区间端点。

还须约束 $\lambda_n$，不能把任意相近的正规形误当合法处理器。名义状态满秩且信号基态输出纯，使每个处理器具有受控等距表示 $W_{i,n}$。令 $A_n=W_{2,n}^\dagger W_{0,n}$，则 $\operatorname{Re}A_n=H_n$。于是
$$
\|W_{2,n}-W_{0,n}Z\|_{\mathrm{HS}}^2
=4-2\operatorname{Re}\operatorname{Tr}(A_nZ)
=4-4\beta_n=O(g_n).
\tag{202.24}
$$
此式不要求等距扩张随 $n$ 收敛，也不固定其最小环境维数。

记 $K_n=W_{0,n}^\dagger W_{1,n}$。精确的两个相邻 Schur 系数、（202.24）以及有界的状态导数，给出在 $t$ 的值与导数约束
$$
\begin{gathered}
\operatorname{Tr}(\rho_nK_n)=a,\qquad
\operatorname{Tr}(\rho_n ZK_n)=a+O(\sqrt{g_n}),\\
\operatorname{Tr}(\rho_n'K_n)=0,\qquad
\operatorname{Tr}(\rho_n' ZK_n)=O(\sqrt{g_n}).
\end{gathered}
\tag{202.25}
$$
第一式从实际 $01$ 系数取复共轭取得，另外一个实际系数为 $\operatorname{Tr}(\rho W_2^\dagger W_1)$。相加相减后，$K_n$ 的上下两行分别由两个二阶线性系统控制。在准确正规形处，这两个系统的行列式为 $-\zeta_n/[2(1-t)]$ 与 $-\zeta_n/[2(1+t)]$；它们一致远离零。结合（202.22）、（202.23），可得
$$
K_n=\begin{pmatrix}A_0&B_0/\lambda_n\\0&0\end{pmatrix}
+O(\sqrt{g_n}),\qquad
B_0=2a\sqrt{\frac{1-t}{1+t}}.
\tag{202.26}
$$
因 $K_n$ 为压缩算子，而 $\lambda_n\to\lambda_*>0$，遂有
$$
A_0^2+\frac{B_0^2}{\lambda_n^2}\le1+O(\sqrt{g_n}),
\qquad \lambda_n\ge\lambda_*-O(\sqrt{g_n}).
\tag{202.27}
$$

在上端点 $u_n=b+\delta_n$，实际程序为合法态。与正规形的 $O(\sqrt{g_n})$ 比较及（202.27）说明
$$
q_*(b+\delta_n)\ge-O(\sqrt{g_n}).
\tag{202.28}
$$
但 $q_*'(b)<0$，所以对某个固定 $c>0$ 及充分大的 $n$，左边不超过 $-c\delta_n$。因此 $\delta_n=O(\sqrt{g_n})$，与（202.16）矛盾。证明了
$$
0<\liminf_{\delta\downarrow0}
\frac{\mathfrak M_2(a,t;R_0+\delta)-I_r(t)}{\delta^2}
\le\limsup_{\delta\downarrow0}
\frac{\mathfrak M_2(a,t;R_0+\delta)-I_r(t)}{\delta^2}
\le\frac{\Lambda}{v_*^2}.
\tag{202.29}
$$

最后把上下二次界提升为确定首项。定理201.2的有限优化用 Choi 正半定性、保迹方程、通道等式和严格端点不等式表示为有限半代数域，目标是正分母上的有理函数。其下确界通过“所有可行值不低于它，且任意正误差内存在可行值”的一阶实数公式定义。因此，按定理196.3证明中的同一量词消去步骤，$\mathfrak M_2$ 是半代数函数；此处并不要求取得下确界。所用标准实代数结果见 Saugata Basu，*Algorithms in Real Algebraic Geometry: A Survey*，arXiv:1409.1534v1，定理2.1、2.27。

$R_0(a,t)$ 亦半代数，所以（202.29）中的归一比值为一维半代数函数。其上、下极限若不同，选居中的水平值，两个互斥的半代数子水平与超水平集都会在零累积，因而各自包含某个右开邻域，矛盾。故归一比值有唯一的严格正有限极限 $\kappa_{\mathrm m}$，即（202.15）。其极限关系也能用一阶实数公式定义，再次量词消去给出联合半代数性。固定实代数 $a,t$ 后，系数是一个由实代数系数符号条件定义的单点，故本身为实代数数。

本结论针对每个固定的允许临界点，不主张靠近参数域边界的统一余项，也不把显式构造的上界系数认定为最优系数。证毕。

<a id="entry-754"></a>

## 追加锚（本行以下为增补区）

<a id="section-203"></a>

## 203. 超临界首项的显式最优值：二参数构造与任意处理器的切向下界

**定义 203.1（临界二次型及其对偶长度）。** 固定定义202.1的允许临界点，沿用 $A_0,\beta_*,x_*,q_*,\gamma,b,R_0$，并记
$$
\begin{gathered}
\nu=-\frac{2x_*(b)}{q_*'(b)}>0,\qquad
 d=\frac{2aA_0-1-b}{\beta_*^3},\qquad
 k=\frac{1+t}{\beta_*}>0,\\
 D_0=(1-t^2)q_*(t)>0,\qquad
 c_0=\frac{2}{(1-t)(1+t)^2}>0,\\
 E_0=1+\frac{td}{k}
 =\frac{1-tb}{(1+t)\beta_*^2}>0,\\
 \mathcal J=\nu^2\left(
 \frac{\gamma^2E_0^2}{c_0}+\frac{d^2D_0}{k^2}\right)>0.
\end{gathered}
\tag{203.1}
$$
$E_0$ 的第二个表达式使用 $A_0(1+t)=2at$；其正性由 $|t|,|b|<1$ 保证。另设
$$
\xi(u)=\left.\frac{\partial}{\partial A}
\frac{2a-A(1+u)}{\sqrt{1-A^2}}\right|_{A=A_0}
=\frac{2aA_0-1-u}{\beta_*^3},
\qquad \xi(b)=d.
\tag{203.2}
$$

**定理 203.2（任意二维处理器的精确超临界二次系数）。** 在定义203.1的参数域上，第202节的首项系数为
$$
\boxed{\quad
\kappa_{\mathrm m}(a,t)=\mathcal J^{-1}.
\quad}
\tag{203.3}
$$
因此，允许任意固定 CPTP 处理器、任意 $C^1$ 二维程序及秩变化，并保持整个闭半径区间的开延拓上对所有信号输入精确相等时，仍有
$$
\mathfrak M_2(a,t;R_0+\delta)
=I_r(t)+\mathcal J^{-1}\delta^2+o(\delta^2).
\tag{203.4}
$$
该系数由三维环境中的二参数受控等距构造渐近达到。结论仅针对固定允许的 $a,t$；不主张有限正 $\delta$ 下的精确最优成本或跨参数边界的统一余项。

证明。 先构造上界。在（202.5）中将设计参数 $A_0,\beta_*$ 换成 $A,\beta(A)=\sqrt{1-A^2}$，仍取
$$
 v=(A,\beta(A))^T,\qquad
 v^\perp=(-\beta(A),A)^T,
\tag{203.5}
$$
其余 $W_0,W_2,f_s$ 不变。对每个固定的邻近 $(A,s)$，这仍是一个固定处理器。令
$$
 x_A(u)=\frac{2a-A(1+u)}{\beta(A)},\quad
 \gamma_A=\frac{2(a-A)}{\beta(A)},\quad
 x_{A,s}(u)=\frac{x_A(u)+\gamma_A s}{1-s^2},\quad
 z_s(u)=\frac{u-s^2}{1-s^2}.
\tag{203.6}
$$
第202节的重叠恒等式逐项成立，故三个非平凡 Schur 系数精确为 $a,a,u$；这里 $A,s$ 都是设计参数，不随 $u$ 变化。

取路径 $A=A_0+h\varepsilon$、$s=\sigma\varepsilon$。程序的实横向分量满足
$$
 x_{A,s}(u)=x_*(u)+\varepsilon[h\xi(u)+\gamma\sigma]+O(\varepsilon^2),
\qquad z_s(u)=u+O(\varepsilon^2).
\tag{203.7}
$$
这些展开及其 $u$ 导数在固定有界参数区间上一致。由（202.11）、（202.12）以及
$$
 (1-t^2)\xi'(t)+t\xi(t)=-k,
\tag{203.8}
$$
名义成本的二次型为
$$
 Q-I_r(t)=\varepsilon^2\left[
 c_0\sigma^2+\frac{(t\gamma\sigma-kh)^2}{D_0}
 \right]+o(\varepsilon^2).
\tag{203.9}
$$
邻近物理上根 $b(\varepsilon)$ 的一阶速度则是
$$
 b'(0)=-\nu(dh+\gamma\sigma).
\tag{203.10}
$$

令 $N=t\gamma\sigma-kh$。端点速度与成本变成
$$
 -\nu\left(\gamma E_0\sigma-\frac d k N\right),
 \qquad c_0\sigma^2+\frac{N^2}{D_0}.
\tag{203.11}
$$
加权 Cauchy–Schwarz 不等式表明，速度至少一时成本至少 $\mathcal J^{-1}$；等号在
$$
 \sigma_*=-\frac{\nu\gamma E_0}{c_0\mathcal J},\qquad
 N_* =\frac{\nu dD_0}{k\mathcal J},\qquad
 h_* =\frac{t\gamma\sigma_*-N_*}{k}
\tag{203.12}
$$
处取得。沿此设计路径，$b'(0)=1$。隐函数定理允许选择
$$
 b(\varepsilon(\delta))=b+\delta+\delta^2,
 \qquad \varepsilon(\delta)=\delta+O(\delta^2).
\tag{203.13}
$$
临界下端点保有固定物理余量，所以上、下端点均严格位于实际程序的物理开域中。由（203.9）得到
$$
 \limsup_{\delta\downarrow0}
 \frac{\mathfrak M_2(a,t;R_0+\delta)-I_r(t)}{\delta^2}
 \le\mathcal J^{-1}.
\tag{203.14}
$$

下面证明所有处理器都服从相同下界。考虑任一趋于零的 $\delta_n>0$，以及相应成本距下确界至多 $\delta_n^3$ 的实际程序。按定理201.2替换为同域、同处理器的满秩仿射程序。上界（203.14）保证其名义成本差
$$
 g_n=Q_n-I_r(t)=O(\delta_n^2).
\tag{203.15}
$$
只需研究归一成本的任一有限下极限子列。以下作必要的进一步子列选择，并省略指标 $n$。

第202节的紧性与等号稳定性允许选择固定于运行参数的程序坐标，使二结果读出及名义 SLD 满足
$$
 H=\operatorname{diag}(1-2e_+,-1+2e_-),\qquad
 e_\pm=O(\delta^2),\qquad
 L-\operatorname{diag}(s_+,s_-)=O(\delta).
\tag{203.16}
$$
精确读出给出
$$
 z(u)=\frac{u-\alpha}{\beta},\qquad
 \alpha=e_--e_+,\quad\beta=1-e_+-e_-.
\tag{203.17}
$$
相位可选成名义非对角元为正。第202节证明还给出状态曲线与参数 $\lambda$ 的正规形相差 $O(\delta)$，以及 $\lambda\ge\lambda_*-O(\delta)$。在端点 $b+\delta$ 的正性又给出 $\lambda\le\lambda_*+O(\delta)$：其正规形判别式为
$$
 q_\lambda(u)=q_*(u)
 -\frac{(\lambda^2-\lambda_*^2)(1-tu)^2}{1-t^2},
\tag{203.18}
$$
而 $q_\lambda(b+\delta)\ge-O(\delta)$，$1-tb>0$。因此在固定有界区间上连同导数都有
$$
 x(u)=x_*(u)+\delta\chi(u)+o(\delta),\qquad
 y(u)=O(\delta),\qquad z(u)=u+O(\delta^2),
\tag{203.19}
$$
其中 $\chi$ 为某个实仿射函数；这是有界仿射系数取子列后的极限，不假定最优元随 $\delta$ 可微。

用受控等距表示写处理器，记
$$
 C=W_2^\dagger W_0,\quad K=W_0^\dagger W_1,\quad
 \Delta W=W_2-W_0Z,\quad
 K_0=\begin{pmatrix}A_0&\beta_*\\0&0\end{pmatrix}.
\tag{203.20}
$$
第202节给出 $K=K_0+O(\delta)$。由 $\operatorname{Re}C=H$，逐列精确计算可得
$$
 \|\Delta W e_0\|^2=4e_+,\qquad
 \|\Delta W e_1\|^2=4e_-.
\tag{203.21}
$$
还需要比 $C-Z=O(\delta)$ 更强的估计。写
$$
 C=\begin{pmatrix}1-2e_++ip_0&\zeta\\
 -\overline\zeta&-1+2e_-+ip_1\end{pmatrix}.
\tag{203.22}
$$
先由（203.21）知 $p_j,\zeta=O(\delta)$。由于 $C$ 为压缩算子，$I-C^\dagger C\succeq0$，其两个对角元非负且为 $O(\delta^2)$，故非对角元亦为 $O(\delta^2)$。将其展开为 $-2\zeta+O(\delta^2)$，得到 $\zeta=O(\delta^2)$。实际系数 $\operatorname{Tr}(\rho_uC)=u$ 为实，结合其导数，给 $p_0,p_1$ 一个二阶线性系统；由（203.17），两个布居及其导数的行列式趋于 $-1/2$，而非对角贡献为 $O(\delta^2)$。所以
$$
 C-Z=O(\delta^2),\qquad W_0^\dagger\Delta W=O(\delta^2).
\tag{203.23}
$$

将 $W_0$ 的两列视为固定的正交基向量，令 $P_\perp$ 投影到它们的正交补，并设
$$
 v=(A_0,\beta_*)^T,\quad w=(-\beta_*,A_0)^T,
 \qquad T=P_\perp W_1.
\tag{203.24}
$$
有 $T^\dagger T=I-K^\dagger K=ww^T+O(\delta)$。因而 $\|Tv\|=O(\sqrt\delta)$、$\|Tw\|=1+O(\delta)$。取 $f=Tw/\|Tw\|$，则
$$
 T=fw^T+O(\sqrt\delta).
\tag{203.25}
$$
这一步保留了秩一边界可能产生的平方根误差，并未假设整个 $W_1$ 一阶可微。定义有界实数的子列极限
$$
 d_j=\lim\operatorname{Re}\left\langle
 \frac{\Delta W e_j}{\delta},f\right\rangle,
 \qquad j=0,1.
\tag{203.26}
$$
由（203.21）和单位向量投影，
$$
 \liminf\frac{e_+}{\delta^2}\ge\frac{d_0^2}{4},\qquad
 \liminf\frac{e_-}{\delta^2}\ge\frac{d_1^2}{4}.
\tag{203.27}
$$
而（203.23）、（203.25）说明 $\delta^{-1}\Delta W^\dagger W_1$ 的逐项实部趋于 $(d_0,d_1)^Tw^T$。所需量只有两列的范数与内积；更大的环境不会改变这些估计。

将 $K$ 第一行的一阶实部写为
$$
 \operatorname{Re}(K_{00},K_{01})
 =v^T+\delta(\theta w^T-\eta v^T)+o(\delta),
 \qquad \eta\ge0.
\tag{203.28}
$$
$\eta$ 非负来自行范数不超过一。两个精确相邻系数给出
$$
 \operatorname{Tr}(\rho K)=a,\qquad
 2\operatorname{Tr}(\rho P_-K)
 =\operatorname{Tr}(\rho\Delta W^\dagger W_1).
\tag{203.29}
$$
将它们在一阶取实部，利用（203.19）、（203.25）—（203.28），得到
$$
 \chi(u)=\left(\theta+\frac{d_0}{2}\right)
 \frac{1+u-2aA_0}{\beta_*^2}
 +\frac\gamma2 d_1+\frac{2a}{\beta_*}\eta.
\tag{203.30}
$$
例如第二式先消去 $K$ 下行对迹的贡献，余下为 $\beta_*\chi/2$、第一行变化及 $\tfrac12w^T\rho_*(d_0,d_1)^T$；代入 $A_0h+\beta_*x_*/2=a$ 即得（203.30）。因此，令
$$
 h=-\beta_*\left(\theta+\frac{d_0}{2}\right),\quad
 \sigma=\frac{d_1}{2},\quad J=\frac{2a}{\beta_*}\eta\ge0,
\tag{203.31}
$$
便有
$$
 \chi(u)=h\xi(u)+\gamma\sigma+J,
 \qquad
 N:=(1-t^2)\chi'(t)+t\chi(t)
 =-kh+t\gamma\sigma+tJ.
\tag{203.32}
$$

最后比较成本和端点。丢弃 Bloch 向量的 $y$ 分量不会增加点态 SLD 信息。具体地，若 $q_{xz}=1-x^2-z^2$、$p=xx'+zz'$，两者的信息差恰为
$$
 \frac{(q_{xz}y'+py)^2}{q_{xz}(q_{xz}-y^2)}\ge0.
\tag{203.33}
$$
这里分母在名义点一致为正。对实平面投影使用（202.11），其第一项为 $[\beta^2-(t-\alpha)^2]^{-1}$。由（203.17）展开，再用（203.27）、（203.32），得到
$$
 \begin{aligned}
 \liminf\frac{g}{\delta^2}
 &\ge\frac{(1+t)d_0^2+(1-t)d_1^2}{2(1-t^2)^2}
 +\frac{N^2}{D_0}\\
 &\ge c_0\sigma^2+\frac{N^2}{D_0}.
 \end{aligned}
\tag{203.34}
$$
在 $u=b+\delta$，状态正性及（203.19）给出
$$
 q_*'(b)-2x_*(b)\chi(b)\ge0,
 \qquad -\nu\chi(b)\ge1.
\tag{203.35}
$$
由（203.32）消去 $h$，可写成
$$
 \chi(b)=\gamma E_0\sigma-\frac d kN+E_0J.
\tag{203.36}
$$
因 $E_0>0$、$J\ge0$，故
$$
 -\nu\left(\gamma E_0\sigma-\frac d kN\right)
 \ge1+\nu E_0J\ge1.
\tag{203.37}
$$
将（203.11）的同一加权 Cauchy–Schwarz 不等式用于（203.34）、（203.37），便得归一成本下极限至少 $\mathcal J^{-1}$。结合（203.14），证明（203.3）、（203.4）。整个下界保留任意复相位与环境维数，只在不增成本或扩大可行集合的方向舍去非负项；上界则由实际处理器实现。证毕。

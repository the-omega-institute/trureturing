# 观察者相对时空的因果—相容—恢复理论

## 1. 理论范围与基本约定

**定义 1.1（观察者相对时间的关系模型）。** 一个观察者相对时间模型由共同来源、带类型的部分过程、实际记录、操作权限、策略和路径钟组成。来源关系可以同时包含静态配置、事件依赖、仪器和档案；过程指标只标记关系链中的位置，不预设图外时钟。本文分别研究静态关系极限、正方形谱、FIB-ATOM、证成过程、双光锥延续，以及历史回流、最小边界和取证—遗忘平衡。

完整来源中存在某个对象、对象从当前可达、对象能有限取得、对象已经进入当前记录，是四种不同谓词：

$$
\boxed{
\text{整体中存在}
\neq\text{从当前可达}
\neq\text{可以有限取得}
\neq\text{已经进入当前记录}.
}
$$

**假设 1.2（接口与共同实现）。** 除明确另设概率律或量子通道的章节外，过程确定且允许部分操作。每次比较使用同一个来源域、同一套合法操作及实际可访问记录。仍可查询的外部档案、原始数据、校准、权限和控制器状态均属于接口；表示省略一个字段不构成其物理删除。备选操作的合法性不意味着它们已在同一历史中同时执行。

**定义 1.3（纤维、对数与恢复）。** 对 $f:X\to Y$，令

$$
\ker f=\{(x,x'):f(x)=f(x')\}.
$$

此处核指不可区分关系，不限于线性核。目标 $T:X\to Z$ 能由 $f$ 精确恢复，指存在 $g:f(X)\to Z$ 满足 $T=g\circ f$，等价于 $T$ 在每条 $f$ 纤维上恒定。该等价采用 [关系观察主卷](RECURSIVE_RELATIONAL_OBSERVATION.md) 的实际像因子化与 [恢复几何卷](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md) 的目标恢复判据；不另把它作为新增结果。存在恢复函数不预设算法、有限取得或费用。除另行声明外，$\log$ 为自然对数，容量以 $\log_2$ 为单位。

## 2. 静态关系极限与内部观察者

**定义 2.1（完整来源族）。** 固定带类型的关系语言和约束，令 $\Omega$ 为满足约束的完整实现集合，$\omega\in\Omega$ 为实际实现。其关系图为 $\mathcal G_\omega$，观察者的完整过程为子结构

$$
\mathcal O_\omega\subseteq\mathcal G_\omega.
$$

局部式 $s'=F_a(s)$ 表示两个事件位置之间的相容关系；先后属于图的内部结构。“静态”指不另引入推动整个图变化的外部参数，不指内部没有先后。实际配置、允许操作与全部合法续接的区别采用 [过程几何卷](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) 第 1、2 节。

**定义 2.2（有限联合视图）。** 设 $\mathscr W$ 为非空有向窗口族，每个窗口具有真实联合读出

$$
r_W:\Omega\to X_W,\qquad X_W=r_W(\Omega).
$$

对 $W\le W'$，限制映射满足 $r_{W'W}r_{W'}=r_W$，并满足恒等与复合相容律。于是有

$$
\iota:\Omega\to\varprojlim_W X_W.
$$

窗口细化可以增加空间范围、历史范围、关系种类或精度，不定义物理时间推进。

**假设 2.3（紧来源实现接口）。** $\Omega$ 非空且紧，各 $r_W$ 连续，各 $X_W$ 为 Hausdorff 空间。采用过程几何卷第 4 节的相容完成接口：每个相容线程有共同来源，而 $\iota$ 单射当且仅当全部视图联合分离来源。

该接口的紧性依据如下。对线程 $(x_W)$，闭集 $F_W=r_W^{-1}\{x_W\}$ 非空；有限组窗口的共同上界 $V$ 满足 $F_V\subseteq\bigcap_WF_W$，故有限交性质给出共同来源。来源唯一恰好要求

$$
\forall W,\ r_W(\omega)=r_W(\omega')\Longrightarrow\omega=\omega'.
$$

这一标准紧性论证不提供取得来源的算法或费用。若撤去紧性，最终全零的二进制序列能实现任意有限全一前缀，却不能实现全一线程：每个有限前缀可补零，无穷全一序列不属于该来源族。

## 3. 动态全息边界与完整行为

**定义 3.1（带类型的实际过程）。** 对每个类型 $i$，给定状态集 $S_i$ 和读出 $q_i:S_i\to M_i$。具名动作 $a:i\to j$ 具有合法域、后继及标签

$$
D_a\subseteq S_i,\qquad F_a:D_a\to S_j,\qquad \ell_a:D_a\to L_a.
$$

读出包含假设 1.2 的全部仍可访问资源。

**定义 3.2（动态充分边界）。** $q$ 动态充分，指合法域、标签和后继在实际像 $q_i(S_i)$ 上自主且精确地下降。使用 [过程几何卷](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) 定理 3.2 的严格响应纤维判据，其具体条件为

$$
q_i(s)=q_i(t)\Longrightarrow
\bigl(s\in D_a\iff t\in D_a\bigr),
$$

且在合法时

$$
\ell_a(s)=\ell_a(t),\qquad q_j(F_as)=q_j(F_at).
$$

必要性来自下降映射单值；充分性由 $\overline F_a(q_i(s))=q_j(F_as)$ 与代表元无关而得，并沿有限路径归纳。仅保当前显示值不足以满足该接口。

**定义 3.3（完整行为和残余）。** $\beta_i(s)$ 记录从 $s$ 出发的全部有限合法操作词、响应与终点读出，包括空词的当前读出。令

$$
s\equiv_i t\iff\beta_i(s)=\beta_i(t).
$$

沿共同合法词 $u$ 取残余 $\operatorname{res}_u$，满足

$$
\beta(F_us)=\operatorname{res}_u\beta(s).
$$

该行为对象不宣称所有备选实验可共同执行。

**假设 3.4（最粗未来充分表示接口）。** 使用过程几何卷定理 3.3 及第 6 节的行为商：每个精确表示的核包含于 $\ker\beta$，行为像本身具有良定义后继。来自某个初态的残余集合有限，当且仅当该行为具有有限状态精确实现。有限输出、有限工作寄存器或逐来源有限，不替代同一来源族上的残余并集有限。

此处的有限性仅是状态数判据，不保证从有限实验判定它，也不保证精确取得实数标签。

## 4. 观察选择与相容实现

**定义 4.1（事件纳入与相容来源）。** 令 $E$ 为事件集，每个实现指定事件子集 $\omega\subseteq E$。固定初始边界后，$C$ 是已发生的有限事件域，包含必要依赖。令

$$
\Omega_C=\{\omega\in\Omega:C\subseteq\omega\},\qquad
\operatorname{Excl}(C)=E\setminus\bigcup_{\omega\in\Omega_C}\omega,
$$

$$
\operatorname{Cl}(C)=\bigcap_{\omega\in\Omega_C}\omega.
$$

合法历史满足 $\Omega_C\ne\varnothing$。$C$ 是完整历史对象，不等于有限观察者的当前记忆。

**定理 4.2（纳入、排除与无新增排除的精确条件）。** 若 $C\subseteq D$，则

$$
\Omega_D\subseteq\Omega_C,\qquad
\operatorname{Excl}(C)\subseteq\operatorname{Excl}(D).
$$

对合法扩展 $C'=C\cup\{e\}$，有

$$
\Omega_{C'}=\Omega_C\iff e\in\operatorname{Cl}(C).
$$

**证明。** 包含 $D$ 的实现包含 $C$；对实现并集取补得排除包含。最后的等式恰好表示全部原相容实现本已包含 $e$。因此发生并耗时的事件不必严格减少候选，候选排除也不表示备选结构从整体中被消灭。$\square$

**定理 4.3（由既有记录决定的动作不增加来源区分）。** 若 $m:X\to M$，动作选择 $a=\pi\circ m$，则

$$
\ker(m,a)=\ker m.
$$

**证明。** 相同 $m$ 给相同动作，联合记录相同又蕴含 $m$ 相同。新响应、后果或额外来源可以细化纤维；该式只涉及选动作这一确定后处理。计算仍可将既有关系转为可用证书。$\square$

**定理 4.4（合法延拓的因果前沿）。** 设事件形成偏序，$C$ 有限且向下闭，$e\notin C$ 的全部严格前驱属于 $C$。令 $\partial C=\operatorname{Max}(C)$、$\downarrow e=\{x:x\preceq e\}$，则

$$
\partial(C\cup\{e\})=(\partial C\setminus\downarrow e)\cup\{e\}.
$$

**证明。** 向下闭性排除 $e$ 位于旧事件之前；旧极大事件中仅位于 $e$ 之前的成员失去极大性，$e$ 成为新极大事件。两个并行事件汇合为一个验证事件时，前沿数可从二降至一，历史域仍扩大。$\square$

**定理 4.5（高阶相容与路线排除的边界）。** 在约束 $x+y+z=0\pmod2$ 下，任意两变量取一可延拓为合法赋值，但三变量同时取一不合法。两条从同一事件出发的互斥路线仍可具有共同未来事件。

**证明。** 两个一配一个零满足偶校验，三个一不满足。对第二句，在 $1+1$ 维时空取 $p=(0,0)$、$q_\pm=(1,\pm v)$、$r=(2,0)$，$0<v<1$；两段位移均满足 $\Delta t>|\Delta x|$，故两条路线均可到 $r$。因此两两相容不推出共同相容，排除某具体前提可排除依赖它的事件实例，却不排除整个几何未来锥。$\square$

## 5. 前缀增长与剩余行为合并

**定义 5.1（同源前缀与未来行为）。** 固定共同来源域 $X$，$u$ 在 $X$ 上共同合法，$v$ 在 $F_u(X)$ 上共同合法，即拼接词 $uv$ 在 $X$ 上共同合法。令

$$
P_u(x)=\operatorname{tr}_u(x),\qquad B_u(x)=\beta(F_ux).
$$

$P_u$ 保留完整已执行事件词，$B_u$ 保留后继之后的全部允许行为；二者不默认等于当前有限记录。

**定理 5.2（前缀—残余双向包含）。** 有

$$
\boxed{\ker P_{uv}\subseteq\ker P_u,\qquad
\ker B_u\subseteq\ker B_{uv}.}
$$

若执行 $uv$ 后存在允许程序从后继状态精确读取 $P_u$，还具有

$$
\ker B_{uv}\subseteq\ker P_u.
$$

**证明。** 拼接式

$$
P_{uv}(x)=P_u(x)\mathbin{\|}\operatorname{tr}_v(F_ux)
$$

使完整前缀相等蕴含较短前缀相等。残余式 $B_{uv}=\operatorname{res}_vB_u$ 给另一包含。若档案仍可读取，行为相同的状态必须给出相同档案响应，得到最后一式。包含未必严格。$\square$

**定义 5.3（永久恢复损失）。** 固定来源目标 $T:X\to Z$。相对执行词 $u$ 和后继接口，永久不可恢复指存在 $x,x'$ 满足

$$
T(x)\ne T(x'),\qquad B_u(x)=B_u(x').
$$

若此前有有限允许程序恢复 $T$，此后满足该式，称发生观察者相对的不可逆恢复事件。此定义采用定义 1.3 的恢复判据；权限、介质可达性或记录覆盖必须体现在实际接口中。当前读数相同而未来行为不同不满足永久性。

**定理 5.4（可逆整体的有限精确自主边界）。** 若 $F:X\to X$ 双射，$R:X\to M$ 满射，$M$ 有限，且 $RF=fR$，则 $f$ 双射。

**证明。** 对每个 $m=R(x)$，有 $m=f(R(F^{-1}x))$，故 $f$ 满射，有限性给单射。完整可逆、有限且精确封闭自主的边界不能在此更新中合并边界值。环境输入、访问限制或近似须另行指定。$\square$

## 6. 因果双锥、延续与路径钟

**定义 6.1（因果锚点和连续观察者）。** 在事件偏序上令

$$
J^-(p)=\{e:e\preceq p\},\qquad J^+(p)=\{e:p\preceq e\}.
$$

反对称性给 $J^-(p)\cap J^+(p)=\{p\}$，传递性给

$$
p\preceq q\Longrightarrow
J^-(p)\subseteq J^-(q),\quad J^+(q)\subseteq J^+(p).
$$

交点是一事件，不是整个观察者。一般偏序不预设洛伦兹光锥。若另给洛伦兹流形，连续观察者为曲线 $\gamma:I\to M$，未来类时切向满足 $\dot\gamma(\tau)\in\operatorname{Int}C^+_{\gamma(\tau)}$，记录事件为 $p_k=\gamma(\tau_k)$。任意 $\tau_0<\tau_1$ 间还有中点，故记录的下一项不等于连续时空的最小后继点。度量、类时与类光约定参见 David Tong, [General Relativity，第 3 节](https://www.damtp.cam.ac.uk/user/tong/gr/grhtml/S3.html)。

**定理 6.2（裸光锥的非零后继选择障碍）。** 在 $1+1$ 维令 $U=\Delta t+\Delta x$、$V=\Delta t-\Delta x$。只使用原点及未来锥、并对所有

$$
(U,V)\mapsto(e^\eta U,e^{-\eta}V)
$$

等变的单值规则，不能选出唯一非零位移。

**证明。** 原点与锥在这些变换下不变，唯一输出必须同时满足 $U_*=e^\eta U_*$、$V_*=e^{-\eta}V_*$，对所有 $\eta$ 只能为零。结论只涉及裸锥信息；加入状态、动力学或控制后不受此无选择结论约束。$\square$

**定义 6.3（路径钟与状态势）。** 给每条合法边经校准的增量 $\tau_a(s)\ge0$，路径钟为沿路求和：

$$
\tau(s,uv)=\tau(s,u)+\tau(F_us,v),\qquad\tau(s,\varepsilon)=0.
$$

有限图上的状态钟是函数 $t$，使每条边 $e$ 满足 $\tau_e=t(\operatorname{target}e)-t(\operatorname{origin}e)$。采用过程几何卷第 9 节的路径钟与状态势分离：存在该势当且仅当底层无向图每条有限闭走法的有符号标签和为零。必要性由望远镜求和；充分性是在每个连通分支选根沿路积分，零闭和保证路径无关。正时长自环、或两条同端点路线历时分别为二和三，均不满足条件。

**定理 6.4（同锥不确定时长，同位置不确定内部状态）。** 给定洛伦兹度量 $g$，令

$$
\tau[\gamma]=\int\sqrt{-g(\dot\gamma,\dot\gamma)}\,d\lambda.
$$

正共形因子 $g'=\Omega^2g$ 保留局部因果锥，而沿类时曲线的时长被改为含 $\Omega$ 的积分；两条类时路线可在同一位置汇合而内部记录不同。

**证明。** 切向范数平方乘以正数 $\Omega^2$，符号不变，积分被积项乘以 $\Omega$。取常数 $\Omega=2$ 即使非零时长翻倍。定理 4.5 的两条路线分别保留标签 $+$、$-$ 即给同位置不同内部状态。$\square$

## 7. 取得旧证据的新事件

**定义 7.1（来源、档案、请求与验证）。** 设 $e$ 为源事件，$a$ 为档案，$q$ 为请求，$r$ 为响应，$v$ 为验证。依赖为

$$
e\to a\to r,\qquad q\to r\to v.
$$

$\operatorname{source}(r)=e$ 是引用关系，不定义 $r=e$。

**定理 7.2（旧来源与新取得的分离）。** 上述依赖要求 $e\prec r$、$q\prec r$，不要求 $e\prec q$。恢复旧内容不推出恢复旧观察者状态，也不推出旧事件再次发生。

**证明。** 取 $e,q$ 为不可比的两节点，令 $a$ 在 $e$ 后，$r$ 接收 $a,q$，$v$ 在 $r$ 后，即满足所有依赖。另令响应只包含旧比特而后继观察者持有新请求标记；内容恢复而状态不同。在完整静态图中，未取得与已取得对应不同事件位置，无需让旧节点再次发生。$\square$

## 8. 有限取证与无限可辨识

**定义 8.1（有限证据闭包）。** 给初始证据集 $I$ 和有限前提规则 $P\Rightarrow e$。令

$$
C_0=I,\qquad
C_{n+1}=C_n\cup\{e:\exists(P\Rightarrow e),\ P\subseteq C_n\}.
$$

有限取得指 $e\in\bigcup_nC_n$。该闭包接口可用有限合法推导树表示：由层数归纳可构树，由树高归纳可入层；有限前提保证存在共同有限层。单有 $p\Rightarrow q$、$q\Rightarrow p$ 而 $I=\varnothing$ 时，各层为空，自洽依赖不产生取得。

**假设 8.2（紧源有限读出接口）。** $S$ 紧，$T:S\to Z$ 连续且 $Z$ 有限离散，连续读出 $q_j:S\to Y_j$ 的值域 $Y_j$ 均为有限离散空间，并联合分离不同目标值。采用紧性有限子覆盖原理：存在有限组读出，使 $T=g(q_{j_1},\ldots,q_{j_m})$。

其依据是紧集 $\{(s,t):T(s)\ne T(t)\}$ 被开集 $\{(s,t):q_j(s)\ne q_j(t)\}$ 覆盖；有限子覆盖与定义 1.3 给因子化。读数能否在同一来源上实际共同取得，仍由操作合同决定。

**定理 8.3（全序列可辨识不保证逐位查询有限终止）。** 在 $S=\{0,1\}^{\mathbb N}$ 上允许逐位查询，目标

$$
T(x)=1\iff x=000\cdots
$$

由完整序列决定，但不存在对所有输入正确且总有限停止的查询算法。

**证明。** 若在全零输入有限停止，仅查有限位置。将一个未查位置改成一，保持全部查询历史，却改变目标，矛盾。额外生成规则或有限证明证书属于更强接口。$\square$

**定义 8.4（取证深度与有限停止层）。** 对来源候选集 $B$、已执行前缀 $h$ 和目标 $T$，$D_T(h,B)$ 为正确确定性协议的最小最坏步数，无有限协议时取 $\infty$。所有首动作必须在 $B$ 上共同合法。有限动作及响应模型中，

$$
D_T(h,B)=0\iff T|_B\text{ 恒定},
$$

非恒定时有 Bellman 递推

$$
D_T(h,B)=1+\min_a\max_{r:\,B_{a,r}\ne\varnothing}D_T(ha,B_{a,r}).
$$

这里取从零层逐层构造的有限可解集合所确定的解。任意有限正确树的首动作给下界，将正确子树接到首动作给上界；循环方程本身不证明停止。存在完整解树、存在有限树、存在小状态商及其构造成本，是分别指定的条件。

## 9. 奇数频率正方形谱与临界读出

**定义 9.1（正方形轨道及对角读出）。** 在 $[-\pi,\pi]$ 上令

$$
h(\theta)=1-\frac{2|\theta|}{\pi},
$$

并作 $2\pi$ 周期延拓。置 $k(\theta)=h(\theta-\pi/2)$，

$$
\Gamma(\theta)=(h(\theta)-k(\theta),\,h(\theta)+k(\theta)).
$$

这是从右上角出发的单位正方形轨道。对 $N\ge1$ 令

$$
P_N(\theta)=(X_N,Y_N)=
\sum_{\substack{1\le n\le2N-1\\n\ {\rm odd}}}\frac{\Gamma(n\theta)}n,
$$

$$
U_N=\frac{X_N+Y_N}{2}
=\sum_{n\ {\rm odd}}\frac{h(n\theta)}n,\qquad
V_N=\frac{Y_N-X_N}{2}
=\sum_{n\ {\rm odd}}\frac{k(n\theta)}n.
$$

有限求和均以 $2N-1$ 为上界。每层半边长为 $1/n$、周期为 $T/n$ 时，相对移动中心的周界速度为 $(8/n)(n/T)=8/T$；这不约束叠加末端的传播速度。

**定理 9.2（相干角点增长与算术共振）。** 令 $A_N=\sum_{j=0}^{N-1}(2j+1)^{-1}$。则

$$
U_N(0)=A_N
=\frac12\log N+\log2+\frac{\gamma}{2}
+\frac1{48N^2}+O(N^{-4}),
$$

其中 $\gamma$ 为 Euler 常数，$A_9=2.0806239512\ldots$。若 $\theta=\pi p/q$、$q>0$、$\gcd(p,q)=1$，则 $q$ 奇时

$$
U_N(\theta)=\frac{(-1)^p}{2q^2}\log N+C_{p,q}+O_q(N^{-1});
$$

$q$ 偶时 $U_N(\theta)$ 收敛。若 $\theta/\pi$ 无理，则

$$
\frac{U_N(\theta)}{\log N}\longrightarrow0.
$$

最后一式不声称无理点上原级数全部收敛。

**证明。** $A_N=H_{2N}-H_N/2$；标准调和数展开直接给角点公式。分段线性三角波的 Fourier 展开是

$$
h(\theta)=\frac8{\pi^2}
\sum_{m\ {\rm odd}}\frac{\cos(m\theta)}{m^2}.
$$

系数由分段积分得到，级数绝对一致收敛。序列 $h((2j+1)\pi p/q)$ 以 $q$ 为周期。平均奇数相位时，等比和筛去 $q\nmid m$ 的谐波。$q$ 偶时没有奇数倍；$q$ 奇时，$m=q\ell$ 的平均为 $(-1)^{p\ell}=(-1)^p$，故周期均值为

$$
\mu_{p,q}=
\begin{cases}(-1)^p/q^2,&q\ {\rm odd},\\0,&q\ {\rm even}.\end{cases}
$$

减去均值后的周期序列部分和有界；分部求和使其奇数调和加权级数收敛、尾部为 $O_q(N^{-1})$。均值乘以 $A_N$ 给有理点公式。无理点使用旋转均匀分布：三角多项式逐项等比求和，再一致逼近连续函数 $h$，得到前 $N$ 项平均趋零；分部求和给调和加权和为 $o(\log N)$。所用旋转平均与调和数展开是标准中间步骤，结论针对此指定正方形叠加。$\square$

**定义 9.3（圆形读出与内部谐波）。** 令

$$
C_N(x)=\sum_{\substack{1\le n\le2N-1\\n\ {\rm odd}}}\frac{\cos nx}{n},
\qquad
S_N(x)=\sum_{\substack{1\le n\le2N-1\\n\ {\rm odd}}}\frac{\sin nx}{n}.
$$

采用标准奇数对数级数

$$
\sum_{n\ {\rm odd}\ge1}\frac{z^n}{n}
=\operatorname{arctanh}z
=\frac12\log\frac{1+z}{1-z},\qquad |z|<1,
$$

参见 [DLMF §4.38](https://dlmf.nist.gov/4.38)。在 $x\notin\pi\mathbb Z$，其边界值为

$$
C(x)=\frac12\log\left|\cot\frac x2\right|,
\qquad S(x)=\frac{\pi}{4}\operatorname{sgn}(\sin x).
$$

定义 $\chi_4(m)=(-1)^{(m-1)/2}$，仅用于奇数 $m$。平移三角波的 Fourier 级数给

$$
k(\theta)=\frac8{\pi^2}
\sum_{m\ {\rm odd}}\frac{\chi_4(m)\sin(m\theta)}{m^2},
$$

$$
U_N(\theta)=\frac8{\pi^2}\sum_{m\ {\rm odd}}\frac{C_N(m\theta)}{m^2},
\qquad
V_N(\theta)=\frac8{\pi^2}\sum_{m\ {\rm odd}}
\frac{\chi_4(m)S_N(m\theta)}{m^2}.
$$

有限外层求和与绝对收敛内层交换合法。正方形改变内部谐波，圆形本身已经具有对数读出。

**定理 9.4（有界方向与共振跃变）。** 对全部 $\theta$，

$$
V_N(\theta)\longrightarrow V(\theta),\qquad |V(\theta)|\le\frac{\pi}{4},
$$

其中

$$
V(\theta)=\frac2\pi\sum_{m\ {\rm odd}}
\frac{\chi_4(m)}{m^2}\operatorname{sgn}(\sin m\theta),
\qquad\operatorname{sgn}(0)=0.
$$

令 $G=\sum_{\ell\ {\rm odd}}\chi_4(\ell)/\ell^2$。对既约有理点 $\theta=\pi p/q$、$q$ 奇，

$$
V(\theta+)-V(\theta-)
=\frac{4G}{\pi}\frac{(-1)^p\chi_4(q)}{q^2}.
$$

**证明。** $S_N$ 对 $x,N$ 一致有界。令 $\delta=\operatorname{dist}(x,\pi\mathbb Z)$，在 $n\delta\le1$ 的部分用 $|\sin nx|\le n\delta$；余下部分用奇数等比和的 $O(1/\delta)$ 界及分部求和，得到统一常数。逐点有 $S_N(x)\to(\pi/4)\operatorname{sgn}(\sin x)$；可求和的 $m^{-2}$ 因而允许交换极限。上界来自 $\sum_{m\ {\rm odd}}m^{-2}=\pi^2/8$。

符号级数的尾部一致小，故单侧极限逐项计算。仅 $q\mid m$ 的项跳变；写 $m=q\ell$，跳变为 $2(-1)^{p\ell}=2(-1)^p$，且 $\chi_4(q\ell)=\chi_4(q)\chi_4(\ell)$，求和得到公式。$\square$

**定理 9.5（点态共振与均方稳定）。** 对归一化范数

$$
\|f\|_2^2=\frac1{2\pi}\int_{-\pi}^{\pi}|f(\theta)|^2\,d\theta,
$$

存在 $Y\in L^2$，使

$$
\|Y-Y_N\|_2\le\frac1{2\sqrt N}.
$$

对实响应核 $K\in L^2$，置 $\mathcal O_K(f)=(2\pi)^{-1}\int Kf$，则

$$
|\mathcal O_K(Y_N)-\mathcal O_K(Y)|
\le\frac{\|K\|_2}{2\sqrt N}.
$$

宽度 $2\varepsilon$ 的周期平均窗口，$0<\varepsilon\le\pi$，满足

$$
|\Delta\mathcal O|\le\frac{\sqrt\pi}{2\sqrt{N\varepsilon}}.
$$

**证明。** Parseval 正交性给

$$
\|C-C_N\|_2^2=\|S-S_N\|_2^2
=\frac12\sum_{j=N}^{\infty}\frac1{(2j+1)^2}
\le\frac1{8N}.
$$

末式用 $(2j+1)^{-2}<1/(4j(j+1))$ 望远镜求和。整数倍频保持归一化均方范数，内部谐波绝对权重总和为一，所以 $U,V$ 各自尾部范数不超过对应圆形尾部。$U$ 偶、$V$ 奇，尾部正交，且 $Y_N=U_N+V_N$，得到第一界。Cauchy–Schwarz 给核界；平均窗口的核为 $\pi/\varepsilon$ 乘窗口指示函数，范数为 $\sqrt{\pi/\varepsilon}$。固定分辨率稳定不含范数随精度无界的点探针。$\square$

**定理 9.6（Fibonacci 尺度的两种读出速率）。** 取 $N=F_d$、$F_0=0,F_1=1$、$\varphi=(1+\sqrt5)/2$。固定 $L^2$ 核的误差为 $O(\varphi^{-d/2})$；奇分母有理点的共振高度为

$$
U_{F_d}(\pi p/q)=\frac{(-1)^p\log\varphi}{2q^2}d+O_q(1).
$$

**证明。** 将 $F_d=\varphi^d/\sqrt5+O(\varphi^{-d})$ 代入定理 9.2 和 9.5。尺度序列不指定操作次序或钟增量，故这些速率不单独定义时间箭头。$\square$

**定义 9.7（中点起步的梯形高度）。** 令 $\tau$ 为奇的 $2\pi$ 周期函数，在 $[0,\pi]$ 上定义为

$$
\tau(\theta)=
\begin{cases}
4\theta/\pi,&0\le\theta\le\pi/4,\\
1,&\pi/4\le\theta\le3\pi/4,\\
4(\pi-\theta)/\pi,&3\pi/4\le\theta\le\pi.
\end{cases}
$$

它是正方形右侧中点起步的纵向高度。对奇数 $m$ 定义完全乘法符号 $\chi_8$，其在模八余数 $1,3$ 上为一，在 $5,7$ 上为负一。此符号由所列余数定义，不采用其他 Dirichlet 特征的同名约定。分段积分给正弦系数

$$
b_m=\frac{8\sqrt2}{\pi^2}\frac{\chi_8(m)}{m^2}.
$$

**定理 9.8（改变几何基元后的精确校准）。** 以 $\tau$ 作各层基元，重构单位方波 $\operatorname{sgn}(\sin\theta)$ 的奇数外层权重为

$$
a_n=\frac{\pi}{2\sqrt2}\frac1n
\prod_{p\mid n}\left(1-\frac{\chi_8(p)}p\right).
$$

按奇数 $n$ 递增截断时，$\sum a_n\tau(n\theta)$ 在 $L^2$ 中收敛到该方波。

**证明。** 频率 $r$ 的系数为约数卷积 $c_r=\sum_{n\mid r}a_nb_{r/n}$。方波系数为 $4/(\pi r)$；完全乘法函数 $\chi_8(n)/n^2$ 的卷积逆为 $\mu(n)\chi_8(n)/n^2$，反演得公式。

令倍频算子 $\mathcal D_mf(\theta)=f(m\theta)$，并置 $\mathcal T=\sum_{m\ {\rm odd}}b_m\mathcal D_m$。因

$$
\|\mathcal T/b_1-I\|
\le\sum_{\substack{m\ge3\\m\ {\rm odd}}}\frac1{m^2}
=\frac{\pi^2}{8}-1<1,
$$

$\mathcal T$ 由 Neumann 级数可逆。权重满足 $|a_n|\le c(1+\log n)/n$，因为乘积至多 $\sum_{d\mid n}1/d\le1+\log n$，故 $(a_n)\in\ell^2$。令 $f_N=\sum_{n\le2N-1,\ n\ {\rm odd}}a_n\sin n\theta$，有 $\mathcal Tf_N=\sum a_n\tau(n\theta)$；连续性及逐频率卷积使其极限具有方波的全部 Fourier 系数，因而等于方波。逐层换基元不是整体的同一线性投影，校准权重也不自动保留等相对速度。$\square$

## 10. 历史搬运正方形与恢复代价

**定义 10.1（baker 历史搬运接口）。** 在 $[0,1)^2$ 上置

$$
B(x,y)=\left(2x-b,\frac{y+b}{2}\right),\qquad b=\lfloor2x\rfloor.
$$

该符号移位结构与经典 baker 映射相关；参见 [Classical limit in terms of symbolic dynamics for the quantum baker's map](https://arxiv.org/abs/quant-ph/9908040)。它是另一个过程模型，不是第 9 节周界叠加的坐标变换。完整逆式为

$$
B^{-1}(x',y')=\left(\frac{x'+b}{2},2y'-b\right),
\qquad b=\lfloor2y'\rfloor.
$$

**定理 10.2（有限纵向记录的精确未来合并）。** 设整数 $K\ge1$，只读纵向前 $K$ 位 $r=\lfloor2^Ky\rfloor$，只允许向前演化及读取当前 $(x,r)$，无额外恢复通道，则

$$
r'=\left\lfloor\frac r2\right\rfloor+2^{K-1}b.
$$

相同 $(x,r)$ 的状态具有相同全部未来响应。从 $y_0=0$ 出发的输入词 $1011$ 与 $0011$，在 $K=3$ 时均给末记录 $110$，完整纵坐标分别为 $13/16$、$12/16$。

**证明。** 将 $y'=(y+b)/2$ 取整得更新式。相同横坐标给相同 $b$，相同记录再给相同下一记录，归纳得到行为相同。逐步代入四个比特得到所列分数。区别仍存在于完整状态，却不在声明接口中。$\square$

**定理 10.3（有界初值单次恢复的精确风险）。** 共同后续输入全零，$y_s=2^{-s}y_0$。设 $D\ge0$、$\varepsilon\ge0$，$y_0\in I=[a,a+D]\subset(0,1)$，仅取得

$$
z=2^{-s}y_0+\eta,\qquad|\eta|\le\varepsilon.
$$

在任意估计器上取最小、在初值与合法误差上取最大，得到

$$
R_s^*=\min\left(\frac D2,\,2^s\varepsilon\right).
$$

**证明。** 给定 $z$ 的相容区间为 $I\cap[2^s(z-\varepsilon),2^s(z+\varepsilon)]$，取中点给上界。令 $m$ 为 $I$ 中点、$d=\min(D/2,2^s\varepsilon)$；初值 $m-d,m+d$ 配相反误差，产生同一数据 $2^{-s}m$。任意估计器至少在一端误差为 $d$，故界精确。$\square$

**定理 10.4（精度追索速度阈值）。** 若 $\varepsilon_s=\varepsilon_0\,2^{-vs}$，则

$$
R_s^*=\min(D/2,\varepsilon_0\,2^{(1-v)s}).
$$

对精确位接口，初始目标在第 $j>K_0$ 位，后续可读深度为 $K(s)=K_0+\lfloor vs\rfloor$，恢复条件为 $K(s)\ge j+s$。当 $v>1$，

$$
s_{\min}=\left\lceil\frac{j-K_0}{v-1}\right\rceil;
$$

$v\le1$ 时不能追上。当 $D>0$、$\varepsilon_0>0$ 时，恢复风险趋零也恰好要求 $v>1$。

**证明。** 代入定理 10.3 得风险。目标每步向深处移动一位；因 $s$ 和 $j-K_0$ 为整数，$\lfloor vs\rfloor\ge j-K_0+s$ 等价于 $(v-1)s\ge j-K_0$，得到阈值。若有更优旧读数、快照或逆操作，此接口假设不成立，须另计。$\square$

## 11. FIB-ATOM 的来源、容量与双曲结构

**定义 11.1（来源语法与组成读出）。** 采用 [Fibonacci 原子关系生成](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的有序树

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle,\qquad
\rho(\alpha)=\beta,\quad\rho(\beta)=\langle\beta,\alpha\rangle.
$$

组成 $c(t)=(a,b)$ 满足

$$
c(\rho t)=Mc(t),\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad q(a,b)=2a+3b.
$$

这些关系不规定采样、概率或物理钟。既有双读出为

$$
y_0=2a+3b,\quad y_1=3a+5b,\qquad
a=5y_0-3y_1,\quad b=-3y_0+2y_1.
$$

它恢复组成，不恢复叶序与括号。

**定理 11.2（组成纤维中的来源树容量）。** $a,b\ge0$，$a+b\ge1$ 时，组成为 $(a,b)$ 的有序满二叉来源树有

$$
C_{a+b-1}\binom{a+b}{a}
$$

棵，$C_n=(n+1)^{-1}\binom{2n}{n}$。这些树的全部数量轨迹相同。

**证明。** 标准 Catalan 计数给树形 $C_{a+b-1}$；在固定叶序中选 $a$ 个位置标 $\alpha$ 给二项系数，二者独立。数量轨迹只依赖 $M^n(a,b)$，因而相同；无限次读取该族数量不能补回未编码的树关系。$\square$

**定义 11.3（五模式与接缝）。** 禁相邻 $11$ 的三位窗为

$$
000,\ 100,\ 010,\ 101,\ 001,
$$

对应标签 $[\mathrm{null}],[2],[3],[2,5],[5]$。拼窗须保留前窗末位与后窗首位不能同时为一的接缝条件；标签语言不是五个可任意拼接的独立数码。

**定理 11.4（合法历史的有限取证容量）。** 长度 $L\ge0$ 的全部禁 $11$ 串有 $F_{L+2}$ 个。若当前记录至多 $2^K$ 值，每个响应至多 $2^b$ 值，正确确定性协议至多请求 $n$ 次，则无误区分全部历史的必要条件为

$$
K+bn\ge\log_2F_{L+2}.
$$

响应容量包括可读失败标签与可用于区分的时间差。

**证明。** 按首部零或一零分类，串数满足 Fibonacci 递推，初值为一、二。每个初始记录对应深度至多 $n$、分支至多 $2^b$ 的树，叶数至多 $2^{bn}$，全部记录至多 $2^{K+bn}$ 个叶子。无误区分要求叶数不少于历史数。$L=20,K=8,b=1$ 时 $F_{22}=17711>2^{14}$，故至少七次一比特响应。此为必要界，不构造达到它的协议。$\square$

**假设 11.5（两种 Fibonacci 语言的区别）。** 全部禁 $11$ 语言的计数增长率为 $\log_2\varphi$。严格 Fibonacci 替换子移位采用其另行声明的发生频率测度；母卷给出的零熵结论仅用于后者。计数增长率不定义实际随机熵产生。

**定理 11.6（三位窗的有限模八相位接口）。** 对 Zeckendorf 编码 $n=\sum_{j\ge2}\varepsilon_jF_j$，按权重指标递增、从 $j=2$ 开始读取三位窗，至多 $64$ 个状态足以维护 $n\bmod8$ 并检查接缝。

**证明。** $(F_{12},F_{13})\equiv(0,1)\pmod8$，递推给模八周期十二。保存

$$
(r,\ell,b)\in\mathbb Z/8\mathbb Z\times\mathbb Z/4\mathbb Z\times\{0,1\}.
$$

其中 $\ell$ 为当前窗口位置模四，$b$ 为前窗末位。新窗 $(e_0,e_1,e_2)$ 先检查内部及 $be_0\ne1$，再加 $\sum_{i=0}^2e_iF_{2+3\ell+i}$ 到 $r$，更新 $\ell,b$。恰需至多 $8\cdot4\cdot2$ 状态。未声明这是最少状态，也不恢复完整历史或素因子。$\square$

**定理 11.7（FIB 两步递推的洛伦兹型不变量）。** 令

$$
Q(a,b)=a^2+ab-b^2,\qquad
\mathsf T=a+b/2,\quad\mathsf X=\sqrt5\,b/2.
$$

则 $Q(Mc)=-Q(c)$、$Q(M^2c)=Q(c)$、$Q=\mathsf T^2-\mathsf X^2$，两步递推为

$$
\begin{pmatrix}\mathsf T'\\\mathsf X'\end{pmatrix}
=
\begin{pmatrix}3/2&\sqrt5/2\\\sqrt5/2&3/2\end{pmatrix}
\begin{pmatrix}\mathsf T\\\mathsf X\end{pmatrix}.
$$

对 $u=\mathsf T+\mathsf X$、$v=\mathsf T-\mathsf X$，有 $u'=\varphi^2u$、$v'=\varphi^{-2}v$。

**证明。** 代入 $M(a,b)=(b,a+b)$ 得符号翻转，两次执行恢复。坐标替换给所列矩阵及零方向。亦有 $Q=(a+b\varphi)(a+b\varphi')$，$\varphi'=(1-\sqrt5)/2$，是标准黄金环范数在此组成递推中的表达。$M$ 可逆，计数组合坐标未指定物理钟或不可逆接口，故此结构不单独证明物理时间箭头。$\square$

## 12. 证成结果、证书与生成历史

**定义 12.1（逻辑证成与证书接口）。** 给逻辑背景 $\Gamma$、命题 $P$ 和证书 $\pi$，$\operatorname{Check}_\Gamma(\pi,P)=1$ 表示合法证成。标准演绎闭包满足

$$
\Gamma\vdash P\Longrightarrow
\operatorname{Cn}(\Gamma\cup\{P\})=\operatorname{Cn}(\Gamma),
$$

因为可将每次引用 $P$ 替换为其证明。证成不定义真值在完成时改变；它改变有限主体是否持有证据和后续使用成本。证明项的逻辑等同性不定义物理源码或顺序记录被删除。可逆计算的保历史、复制结果与逆向清理构造参见 Bennett, [Logical Reversibility of Computation](https://www.cs.princeton.edu/courses/archive/fall04/cos576/papers/bennett73.html)。

**定理 12.2（固定证书库不能恢复独立任务的实际顺序）。** 若独立任务 $A,B$ 的最终证书固定，规范证书库对执行顺序不敏感，全部未来访问只依赖此库且无其他顺序档案，则

$$
\varnothing\to\{A\}\to\{A,B\},\qquad
\varnothing\to\{B\}\to\{A,B\}
$$

的实际顺序不可恢复。对 $m$ 个独立任务，区分全部顺序至少需要 $\lceil\log_2(m!)\rceil$ 比特；依赖偏序 $D$ 有 $e(D)$ 个合法线性展开时，界为 $\lceil\log_2e(D)\rceil$。

**证明。** 两历史给相同库和全部后续行为，却有不同顺序目标，定义 1.3 排除恢复。全部顺序有 $m!$ 个、偏序展开有 $e(D)$ 个，无误记录须有相应多个值。若顺序档案可访问，前提不成立。$\square$

**定理 12.3（目标正确与历史分辨率的统一容量）。** 设 $\mathcal H$ 为非空有限历史集，$T:\mathcal H\to Y$，整数 $L\ge1$。要求记录能恢复 $T$，且每条记录纤维至多合并 $L$ 个历史，则最少状态数为

$$
|M|_{\min}=\sum_{t\in T(\mathcal H)}
\left\lceil\frac{|T^{-1}(t)|}{L}\right\rceil.
$$

**证明。** 一记录纤维不能混合不同目标值。每个目标纤维至少分成所列个数的大小至多 $L$ 的块；分别分块并记录目标与块号可达下界。该计数统一证明顺序、FIB 历史和有限窗口的区分任务，不保证高效编码或跨尺度自主更新。$\square$

## 13. 量子通道中的新增记录与恢复损失

**定义 13.1（指定测量接口）。** 本节以通道取代不相容测量的共同经典赋值。置

$$
|+\rangle=(|0\rangle+|1\rangle)/\sqrt2,\qquad
|-\rangle=(|0\rangle-|1\rangle)/\sqrt2,
$$

$$
\mathcal M_Z(\rho)=\sum_{z=0,1}
|z\rangle\langle z|_C\otimes P_z\rho P_z.
$$

输入可由 $X$ 测量区分，而通道保留经典 $Z$ 结果与测量后系统。标准量子仪器约定参见 Watrous, [The Theory of Quantum Information，第 2、3 章](https://cs.uwaterloo.ca/~watrous/TQI/)。

两输入的 $Z$ 对角元均为 $1/2$，通道去掉交叉项，故直接有

$$
\mathcal M_Z(|+\rangle\langle+|)
=\mathcal M_Z(|-\rangle\langle-|)
=\frac12|0\rangle\langle0|_C\otimes|0\rangle\langle0|
+\frac12|1\rangle\langle1|_C\otimes|1\rangle\langle1|.
$$

仅从该输出施加任意同一后续通道仍得相同数据，不能恢复原 $X$ 标签；后来允许测 $X$ 不等于恢复原标签。若相干仪器或环境可访问，则不再是此接口，不能由该等式断言整体信息毁灭。

## 14. 未来预测与公开反馈

**定义 14.1（后继预测与完整过去）。** 当前读出为 $R(\omega)$，已声明协议的下一事件为 $Q(\omega)$。定义 1.3 给

$$
Q=fR\iff
\bigl(R(\omega)=R(\omega')\Longrightarrow Q(\omega)=Q(\omega')\bigr).
$$

函数存在不保证可计算或及时取得。若主张同一完整过去和规律允许不同未来，所需条件是存在满足同一规律的 $\omega_0,\omega_1$，使

$$
\omega_0|_{\mathrm{Past}}=\omega_1|_{\mathrm{Past}},
\qquad
\omega_0|_{\mathrm{Future}}\ne\omega_1|_{\mathrm{Future}}.
$$

此条件不由当前读数不足或暂时计算失败推出。能动性若定义为由理由、目标与控制过程形成行动，须另给控制结构；不可预测性不替代该定义。

**定理 14.2（公开反应预测的对角障碍）。** 若预测器提前公布 $b\in\{0,1\}$ 并声称等于主体下一动作，主体能取得 $b$，两动作都合法，策略类允许 $a=1-b$，则没有对该策略类全部过程正确的公开预测器。

**证明。** 正确性要求 $b=a$，合法反应要求 $a=1-b$，于是 $b=1-b$，矛盾。反应策略完全确定；该障碍不排除受限、未公开或概率预测，也不从不可预测推出自由意志。公开读数进入被预测过程的输入。$\square$

## 15. 表示不变性、自校准与联合包含

**定理 15.1（保过程重编码的恢复不变性）。** 两过程间双射 $\Phi$ 保留类型、全部当前读出、合法域、标签及后继：

$$
q'\Phi=q,\qquad \Phi F_a=F'_a\Phi.
$$

对应目标为 $T'=T\Phi^{-1}$。则完整行为、目标恢复、对应协议深度和永久不可恢复关系相同；若还保操作费用与钟标签，费用和路径历时亦相同。

**证明。** 对词长归纳逐步运输合法性、响应和后继。自适应选择器看到相同响应而选择对应动作；恢复函数经 $\Phi^{-1}$ 运输，反向用 $\Phi$。转换本身若须物理计算、存储或通信，该费用须另计。$\square$

**定义 15.2（目标敏感的自校准）。** 发现 $R(x)=R(x')$ 而 $T(x)\ne T(x')$，就是当前表示不足的见证。补充合法读出 $S$ 得 $R'=(R,S)$；充分性仍须证明

$$
R'(x)=R'(x')\Longrightarrow T(x)=T(x').
$$

分开一对来源不保证分开全部目标纤维。允许读出仍不足时，仅能收缩目标要求或保留不确定性；坐标旋转、FIB 编码和名称替换若满足定理 15.1，不能自行产生恢复箭头。

**定理 15.3（观察者延续的联合结构）。** 在共同来源、按定义 5.1 共同合法的拼接词 $uv$、有限因果历史和给定路径钟下，实际延续 $C\subseteq C'$ 同时满足

$$
\Omega_{C'}\subseteq\Omega_C,\qquad
\ker P_{uv}\subseteq\ker P_u,\qquad
\ker B_u\subseteq\ker B_{uv},
$$

$$
\tau(s,uv)=\tau(s,u)+\tau(F_us,v).
$$

**证明。** 分别使用定理 4.2、5.2 和定义 6.3。事件域、相容来源、经历纤维、未来行为纤维和历时属于不同对象，不是同一信息标量；当前有限记忆也不等于完整事件档案。$\square$

## 16. 观察者相对时间对象与物理桥接条件

**定义 16.1（恢复时间结构）。** 固定观察者、事件位置及实际接口 $\sigma$，定义

$$
\mathfrak T_{\mathcal O,\sigma}
=\left(\prec_{\mathcal O},\,\tau_{\mathcal O},
\,\Omega_C,\,D_{\mathcal O},\,\ker\beta_\sigma\right).
$$

分量分别为因果依赖、路径钟、相容来源、有限取证深度及永久行为不可区分关系。该对象不将发散、盲区、不可预测或证明完成定义成时间。

**定理 16.2（若干不充分的时间判据）。** 发散不蕴含过程演化；永久盲区不蕴含过程方向；历史不可恢复不蕴含随机律的时间不对称；证明完成不蕴含逻辑不可逆；裸锥不决定唯一轨迹；不可预测不决定能动性。

**证明。** 无操作的一项发散数列给第一例。恒等演化且读出省略一个比特给第二例。双向独立公平比特过程在有限窗口读出下不能恢复窗外历史，其律却在反序下不变，给第三例。定义 12.1 的可逆计算构造给第四例。定理 6.2 给第五例。外部随机比特输出未包含任何理由或控制结构，给最后一例。$\square$

**假设 16.3（物理实现桥）。** 将上述对象用于物理时空，需要另行给出共同实现：图内钟的相互校准、信号操作与因果锥的对应、恢复误差与真实噪声及存储资源的对应、不同观察者读数的转换律。一般偏序不预设连续洛伦兹几何近似；因果集的相关条件参见 [The causal set approach to quantum gravity](https://arxiv.org/abs/1903.11544)。双曲计数不变量或无界坐标本身不提供这些桥接条件。

## 17. 观察筛选与记忆压缩

**定义 17.1（完整取得历史与当前记忆）。** 固定共同来源 $\Omega$，完整取得历史为 $H:\Omega\to\mathcal H$，当前可访问记忆为 $M=E\circ H$，其中 $E:\mathcal H\to\mathcal M$ 为编码。$M$ 仍包含所有可查询内外部档案。令

$$
\Omega_h=\{\omega:H(\omega)=h\},\qquad
\Omega_m=\{\omega:M(\omega)=m\}.
$$

这里历史纤维不等同于定义 4.1 的任意事件包含域；前者要求精确历史值，后者要求包含指定事件。

**定理 17.2（记忆合并与取证筛选）。** 有

$$
\Omega_m=\bigcup_{h:E(h)=m}\Omega_h.
$$

若在完整历史上追加响应 $r$，则 $\Omega_{h,r}\subseteq\Omega_h$。同一更新可同时细化完整经历的纤维并合并当前记忆的纤维。

**证明。** $M(\omega)=m$ 等价于 $E(H(\omega))=m$，给并集公式。联合历史 $(H,Y)$ 的纤维包含于 $H$ 纤维。取两旧比特值配新响应，最终只保新比特：完整记录细化，而两个旧值被合并。取证和压缩是分别作用的筛选与合并。$\square$

## 18. 固定目标的取证—遗忘平衡

**假设 18.1（有限概率与确定记忆更新）。** 在同一有限概率空间上，$Z$ 为固定历史目标，$M$ 为更新前全部可访问记忆，$Y$ 为新响应，$M^+=F(M,Y)$。策略由 $M$ 决定；若另有随机种子或输入，须加入联合变量。熵与互信息在本节使用比特单位。条件互信息及链式法则采用 Shannon 的标准有限概率定义：

$$
I(A;B\mid C)=H(A\mid C)-H(A\mid B,C)\ge0.
$$

**定义 18.2（取证增益、压缩损失及其恒等式）。** 令

$$
G_Z=I(Z;Y\mid M),\qquad
L_Z=I(Z;M,Y\mid M^+).
$$

二者非负。由标准熵链式法则及 $M^+$ 的函数性，

$$
G_Z=H(Z\mid M)-H(Z\mid M,Y),
$$

$$
L_Z=H(Z\mid M^+)-H(Z\mid M,Y),
$$

因而在此更新接口中

$$
\boxed{
H(Z\mid M^+)-H(Z\mid M)=L_Z-G_Z,
}
$$

$$
I(Z;M^+)-I(Z;M)=G_Z-L_Z.
$$

这是链式法则对指定记录更新的应用，不是热量公式。

**定理 18.3（同一步的目标依赖与累计容量）。** 令 $U,V$ 独立公平比特，$M=U,Y=V,M^+=V$。目标 $U$ 的 $(G,L)$ 为 $(0,1)$，目标 $V$ 为 $(1,0)$，联合目标 $(U,V)$ 为 $(1,1)$。对固定 $Z$ 的连续确定更新，若每个末记忆至多 $2^K$ 个值，则

$$
I(Z;M_n)-I(Z;M_0)
=\sum_{j=0}^{n-1}(G_{Z,j}-L_{Z,j}),
$$

$$
\sum_{j=0}^{n-1}L_{Z,j}
\ge\sum_{j=0}^{n-1}G_{Z,j}-K+I(Z;M_0).
$$

**证明。** 独立性给旧目标新响应增益零、新目标增益一；最终只保 $V$，故损失分别为一、零，联合目标两者均一。逐步相加定义 18.2 的恒等式，使用 $I(Z;M_n)\le H(M_n)\le K$。正损失只说明此次压缩，后续可重新取得；永久性仍要求定义 5.3 的全部行为条件。$\square$

## 19. 消去隐藏变量与历史回流

**假设 19.1（完整线性载体）。** 本节允许整个直和线性载体，过程关系为

$$
\begin{aligned}
x_{n+1}&=Ax_n+Bz_n,\\
z_{n+1}&=Cx_n+Dz_n.
\end{aligned}
$$

$x$ 为当前边界读数，$z$ 为未直接读取的变量，指标 $n$ 标记过程链位置。若实际来源只占受约束子集，纤维条件须在真实联合像上检验。

**定义 19.2（精确消元的回流核）。** 反复展开第二式，得到标准线性消元式

$$
z_n=D^nz_0+\sum_{j=0}^{n-1}D^{n-1-j}Cx_j,
$$

$$
x_{n+1}=Ax_n+BD^nz_0+\sum_{j=0}^{n-1}BD^{n-1-j}Cx_j.
$$

令 $K_j=BD^jC$。其中 $Ax_n$ 为当前直接项，$BD^nz_0$ 为隐藏初态残余，$K_j$ 为边界信息经内部再返回的作用。$n=0$ 时和为空。

消去未解析变量后的记忆项属于 Mori–Zwanzig 的既有机制，参见 [A Priori Estimation Of Memory Effects In Coarse-Grained Nonlinear Systems Using The Mori-Zwanzig Formalism](https://arxiv.org/abs/1611.06277)。精确改写不预设计算复杂度降低。矩阵 $D^j$ 的路径展开给“边界—内部—边界”的关系传播；旧区别在新事件位置形成响应，不定义逆向因果。

**定理 19.3（因果路径不保证区别可恢复）。** 取 $B=(1,1)$、$D=I$，隐藏差异 $\delta z=(a,-a)^{\mathsf T}$，$a\ne0$，则 $BD^j\delta z=0$ 对全部 $j\ge0$ 成立；即使每个隐藏分量均有通向边界的耦合，给定读出仍不能识别该区别。

**证明。** $D^j\delta z=\delta z$，而 $B\delta z=a-a=0$。同边界初态的两个来源具有相同边界序列，归纳消元式亦得此结论。传播可达性与读出耦合、相消及精度是不同条件。$\square$

## 20. 当前盲区、永久盲区与最小边界

**定义 20.1（线性动态记忆商）。** 设 $V$ 为维数 $d$ 的实线性空间，$T:V\to V$、$C:V\to Y$ 线性，完整演化为 $s_{n+1}=Ts_n$，固定精确读出为 $y_n=Cs_n$。自本节起，涉及线性映射时的核采用零子空间 $\ker C=\{v:Cv=0\}$；定义 1.3 的纤维关系对应差向量属于此子空间。令

$$
K_0=\ker C,\qquad
N_\infty=\bigcap_{j\ge0}\ker(CT^j),\qquad
\mathcal M_{\mathrm{dyn}}=K_0/N_\infty.
$$

$N_\infty\subseteq K_0$；记忆商表示当前未读到而以后仍可能影响读出的方向。采用 [关系观察主卷](RECURSIVE_RELATIONAL_OBSERVATION.md) 的隐藏反馈与预测记忆结构；此处不以读数省略定义永久丢失。

**假设 20.2（有限维可观测接口）。** 使用标准有限维可观测矩阵

$$
\mathcal O_d=
\begin{pmatrix}C\\CT\\\vdots\\CT^{d-1}\end{pmatrix},
\qquad N_\infty=\ker\mathcal O_d.
$$

$d=0$ 时矩阵为空，核为零空间。等式的依据为 Cayley–Hamilton：$T^d$ 是较低次幂的线性组合，高次幂递推亦然，前 $d$ 次读出为零因而全部为零。

**定义 20.3（最小动态补充维数）。** 令 $r_\infty=\operatorname{rank}\mathcal O_d$、$r_0=\operatorname{rank}C$。标准秩—零度及商维数公式给

$$
d_{\mathrm{mem}}=\dim\mathcal M_{\mathrm{dyn}}
=r_\infty-r_0.
$$

在线性附加记录 $L:V\to\mathbb R^m$ 中，要求联合记录 $(C,L)$ 足以恢复全部未来读出，最少额外坐标数亦为 $r_\infty-r_0$。

其线性代数依据是 $\ker(C,L)\subseteq N_\infty$，故

$$
r_\infty\le\operatorname{rank}(C,L)\le r_0+m.
$$

在 $V/N_\infty$ 上选取当前读出遗漏方向的坐标达到下界；$N_\infty$ 的 $T$ 不变性使该联合记录有自主后继。零补充恰好要求 $\ker C$ 在 $T$ 下不变。这里维数不是比特容量，也不是这些坐标已经被实际取得的证明；精确实坐标可要求无界精度。

## 21. 可逆有限维模型的后移观察

**假设 21.1（固定精确读出的可逆线性接口）。** 在第 20 节进一步要求 $T$ 可逆，定义

$$
\beta_n(s)=(CT^ns,CT^{n+1}s,\ldots).
$$

采用不变子空间的标准有限维性质：

$$
\ker\beta_n=T^{-n}N_\infty=N_\infty.
$$

理由为 $TN_\infty\subseteq N_\infty$，可逆性和有限维给 $\dim TN_\infty=\dim N_\infty$，故包含为等号，继而 $T^{-n}N_\infty=N_\infty$。仅后移起点不会在此类别中产生新的精确永久盲区。

**定义 21.2（由有限未来重建当前读数）。** 当 $d\ge1$ 时，写特征多项式关系

$$
T^d+a_{d-1}T^{d-1}+\cdots+a_1T+a_0I=0.
$$

可逆性给 $a_0\ne0$，因而

$$
Cs=-\frac1{a_0}
\left(CT^ds+a_{d-1}CT^{d-1}s+\cdots+a_1CTs\right).
$$

当 $d=0$ 时全部线性读数为零，无须该公式。此式给精确重建，不给稳定误差界。若读出有限精度、通道改变、来源无限维、约化不可逆，或无法取得所需实验，前述接口不再自动适用。收缩特征值自身不推出永久失辨。

## 22. 正方形与 FIB 的后续回读

**定义 22.1（正方形四分之一圈接口）。** 正方形周界上的点每四分之一圈采样一次，更新和横坐标读出为

$$
T_\square=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
C_\square=(1,0).
$$

于是 $y_0=x_0,y_1=-z_0$，

$$
\mathcal O_2=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
(x_0,z_0)=(y_0,-y_1).
$$

矩阵满秩给 $N_\infty=\{0\}$、$d_{\mathrm{mem}}=1$。绕行次数若作为目标须另加历史变量，二维周期相位不记录它。

**定义 22.2（FIB 数量的未来重建接口）。** 对定义 11.1 的 $T_F=M,C_F=(2,3)$，

$$
\mathcal O_2=\begin{pmatrix}2&3\\3&5\end{pmatrix},
\qquad \det\mathcal O_2=1.
$$

既有双读出公式给组成恢复，当前秩一、未来秩二，故 $d_{\mathrm{mem}}=1$。$M^2=M+I$ 给

$$
y_{n+2}=y_{n+1}+y_n,\qquad y_n=y_{n+2}-y_{n+1}.
$$

这里恢复的是组成读数，不是来源树或实际执行顺序。

**定理 22.3（长历史和的有限充分实现）。** 同一 FIB 更新写为 $x_{n+1}=z_n,z_{n+1}=x_n+z_n$，则

$$
x_{n+1}=z_0+\sum_{j=0}^{n-1}x_j.
$$

虽然消元式涉及任意长历史和，边界未来可由二维充分状态或二阶递推承接：

$$
x_{n+1}=x_n+x_{n-1}\qquad(n\ge1).
$$

**证明。** 在定义 19.2 取 $A=0,B=C=D=1$ 得求和式。比较 $n$ 与 $n-1$ 的两式，得到差分关系，$n=1$ 亦由原始更新成立。记录两个相邻值便能自主更新，无须保存逐项历史。$\square$

## 23. 极限表示与有限精度恢复视界

**定义 23.1（归一化 FIB 的稳定方向）。** 令 $A=T_F/\varphi$，其特征值为 $1,-\varphi^{-2}$，$\Pi$ 为特征值一的谱投影，则

$$
A^n=\Pi+(-\varphi^{-2})^n(I-\Pi),\qquad A^n\to\Pi.
$$

每个有限阶段可逆，极限投影不可逆。

**定理 23.2（有限精确区别与极限合并）。** 若 $s-s'\in\ker\Pi$ 且 $s\ne s'$，则全部有限 $n$ 满足 $A^ns\ne A^ns'$，但两者极限相等。

**证明。** 差为 $(-\varphi^{-2})^n(s-s')$，有限时非零、极限为零。先保留有限精确数据再恢复，与先换成极限投影再恢复，是两个不同接口。$\square$

**假设 23.3（全部未来的确定性误差接口）。** 取 $0<|\lambda|<1$，初值 $z_0\in[-L,L]$，$L\ge0$、$\varepsilon\ge0$，并从第 $n\ge0$ 步起取得

$$
y_{n+k}=\lambda^{n+k}z_0+e_k,\qquad |e_k|\le\varepsilon,\quad k\ge0.
$$

误差按最坏情况取任意合法序列，不假设独立、可平均抵消、能放大重测或有旧快照。

**定理 23.4（全部无限未来仍有精确最坏恢复界）。** 即使允许估计器使用全部上述未来序列，最小最坏误差为

$$
\boxed{R_n^*=\min(L,\varepsilon|\lambda|^{-n}).}
$$

**证明。** 首次读数除以 $\lambda^n$ 并裁剪到初值区间，误差至多 $\varepsilon|\lambda|^{-n}$；输出零则至多 $L$，择优给上界。令 $\delta=\min(L,\varepsilon|\lambda|^{-n})$。两个初值 $\pm\delta$ 各配 $e_k=\mp\lambda^{n+k}\delta$，其模不超过 $\varepsilon$，使全部读数均为零。任意估计器在至少一端误差不小于 $\delta$，给下界。$\square$

**定理 23.5（精确可逆与有限精度箭头的分离）。** 在假设 23.3 下，$\varepsilon=0$ 给 $R_n^*=0$；固定 $\varepsilon>0$ 给 $R_n^*\to L$。归一化 FIB 稳定方向的误差放大率为 $\varphi^{2n}$。

**证明。** 前两式由定理 23.4，最后代入 $|\lambda|=\varphi^{-2}$。若精度随 $n$ 改善，风险由 $\varepsilon_n|\lambda|^{-n}$ 与区间半径比较，而不是仅由收缩存在决定。$\square$

## 24. 允许操作与永久盲区

**定义 24.1（受控永久核）。** 固定完整线性来源域、精确读出 $C$ 和总线性操作族 $\mathcal A=\{T_a\}$。对有限词 $w=a_1\cdots a_m$，置 $T_w=T_{a_m}\cdots T_{a_1}$，空词为恒等，令

$$
N_{\mathcal A}=\bigcap_{w\in\mathcal A^*}\ker(CT_w).
$$

若改为部分操作，合法性本身须加入行为，不能只交输出核。

**定理 24.2（扩大真实操作权限的核单调性）。** 若 $\mathcal A\subseteq\mathcal A'$，来源、读出及原操作均保持，则

$$
N_{\mathcal A'}\subseteq N_{\mathcal A}.
$$

**证明。** 新词集包含旧词集，交集增加条件。相对于原操作语言永久隐藏的方向不必对扩大后的语言隐藏；此为增加潜在实验的结论。实际执行某一操作可改变状态、消耗准备或破坏另一接口，不由本式推出执行后恢复能力单调。$\square$

## 25. 联合时间结构中的三个定量对象

**定义 25.1（记忆缺口、风险与信息净变）。** 在各自假设下定义

$$
d_{\mathrm{mem}}=\dim\ker C-\dim N_\infty,\qquad
R_n^*(\varepsilon)=\min(L,\varepsilon|\lambda|^{-n}),
$$

$$
\Delta H(Z\mid M)=L_Z-G_Z.
$$

第一量为补充线性维数，第二为指定访问和误差下的历史恢复风险，第三为指定概率律与固定目标的信息净变。含这些数据的观察者结构可写为

$$
\mathfrak T_{\mathcal O}
=\left(\text{事件依赖},\text{路径钟},\text{相容性},
\text{记忆缺口},\text{取证与遗忘},\text{恢复精度}\right).
$$

只在相应线性、概率或误差条件具备时采用该分量。

**定理 25.2（三个量不代替路径钟）。** 路径钟可增长而记忆缺口不变；有限协议可执行许多步而无目标增益；旧目标恢复恶化可与新目标取得同时发生。

**证明。** 给固定 $T,C$ 的每条边标一单位时间，缺口由同一子空间决定而不变。恒定响应且不改变目标相关记录给任意步数、$G_Z=0$。定理 18.3 的更新同时遗忘 $U$、取得 $V$；配同一个正钟增量得到第三例。$\square$

## 26. 证成过程与目标信息的进一步分离

**定义 26.1（恒真目标与持证目标）。** 若在固定背景 $\Gamma$ 的全部允许模型中 $P$ 为真，作为随机目标的真值 $Z=P$ 恒定，故 $H(Z)=0$，与它的全部互信息也为零。持有可检查证书、取得证书所需步数、后续调用成本，以及生成顺序，均是其他目标。

**定理 26.2（证据取得不以历史遗失为必要条件）。** 存在证书已取得且生成历史仍可恢复的接口；也存在证书已取得而生成顺序不可恢复的接口。

**证明。** 第一种接口保存可读证书及完整顺序档案，读取后者即可恢复历史。第二种为定理 12.2 的规范库。两者均已取得固定证书，只有档案和访问条件不同，故证成沿依赖关系的向前性不要求遗忘。$\square$

## 27. 回流、共同盲区与恢复箭头

**定义 27.1（三个不同的隐藏条件）。** 对当前读出核中的来源区别，分别定义：后续回流指某个允许行为读出可分开；永久行为盲区指全部允许行为均不能分开；有限精度恢复视界指在给定误差集合下存在目标不同而全部允许数据相同的来源—误差对。三者分别需要行为、操作权限或误差合同，不仅是当前切面的描述。

**定理 27.2（隐藏存在不决定恢复箭头）。** 有模型当前隐藏而以后精确恢复；有模型全程精确隐藏；有模型有限阶段精确可恢复而固定误差下全部未来不能保证恢复。因而恢复箭头由回流结构、精度和访问条件共同决定。

**证明。** 定义 22.1 的正方形纵坐标在下一读出恢复，给第一种。定理 19.3 的相消方向给第二种。假设 23.3 和定理 23.4 给第三种；零误差下首次读数已足够，固定误差下两相反初值可给全部同数据。$\square$

**假设 27.3（共同实现的桥接义务）。** 将回流核、最小边界、路径钟及信号锥组合为同一物理模型，须同时指定：补充坐标的实际取得程序；内部传播和可控操作；噪声、档案与误差的联合来源；目标和概率律；钟校准及跨观察者转换。记忆核的数值识别可参考 [Data-driven learning for the Mori–Zwanzig formalism: a generalization of the Koopman learning framework](https://arxiv.org/abs/2101.05873)，但拟合既有序列不代替全部声称保留操作上的充分性。

**定理 27.4（关系整体与观察者恢复的不对称可共同实现）。** 存在完整关系仍保留、历史事件继续约束后继，而有限接口不能唯一恢复旧目标的模型；亦存在新增证据进入当前边界时旧区别退出可恢复域的模型。

**证明。** 定理 10.2 的完整 baker 状态可逆保存两份不同纵坐标，有限接口却合并它们；定义 10.1 的递推关系仍约束每个后继。取定理 18.3 的覆盖更新，并要求未来只读取保留的 $V$、旧 $U$ 无其他通道，即同时取得 $V$ 并永久失去 $U$ 的区分。这些构造证明两种条件可以共存，不宣称每次钟增长都必须发生不可恢复。$\square$

## 追加锚（本行以下为增补区）

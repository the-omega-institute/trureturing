# 递归关系观察：双臂终止实验的共同参数辨识

## 1. 联合参数比较源与原源的嵌入

**假设 1.1（同一双臂图上的联合参数比较源）。** 固定 $a,b>0$、$a+b=1$，记 $p_0=a,p_1=b$。令 $\Lambda$ 为 $(0,1)^2$ 上的任意 Borel 概率测度，先抽取一次 $(Q_L,Q_R)\sim\Lambda$，独立抽取根位 $X_0$，其中 $\Pr(X_0=x)=p_x$。条件于同一个三元组 $(Q_L,Q_R,X_0)$，两条外向 Markov 臂相互独立；左臂始终使用 $Q_L$，右臂始终使用 $Q_R$，各臂的转移矩阵为

$$
P_q=\begin{pmatrix}1-q&q\\1&0\end{pmatrix}.
\tag{CPI.1}
$$

原始可见种子 $U$ 的空间 $(\mathcal U,\mathcal E)$ 为任意可测空间，律为概率测度 $\lambda$，并独立于全部源变量。一个具体的联合实现为

$$
\begin{aligned}
\Omega&=\mathcal U\times(0,1)^2\times\{0,1\}
                \times[0,1]^{\{L,R\}\times\mathbb N_{>0}},\\
\mathbb P&=\lambda\otimes\Lambda\otimes(p_0\delta_0+p_1\delta_1)
                \otimes\operatorname{Leb}^{\otimes(\{L,R\}\times\mathbb N_{>0})},\\
Z_{s,0}&=X_0,\qquad
Z_{s,n}=\mathbf1_{\{Z_{s,n-1}=0\}}\mathbf1_{\{V_{s,n}<Q_s\}},
\quad s\in\{L,R\},\ n\ge1.
\end{aligned}
\tag{CPI.2}
$$

这里 $V$ 是最后一个因子的坐标族，$\operatorname{Leb}$ 是 $[0,1]$ 上的均匀概率测度。递推在每个有限坐标上 Borel 可测，故给出可测的完整源。把 $Z_{L,n}$ 放在顶点 $-n$、$Z_{R,n}$ 放在顶点 $n$，共同的 $Z_{L,0}=Z_{R,0}=X_0$ 放在根。每个固定参数及根下，两个独立均匀坐标族确实产生式（CPI.1）的两条条件独立臂。参数不在换臂、新边或新测试时重抽。

这是明确另定义的比较源。原共同参数源仍是 [Process Geometry 定义27.1](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) 的源；本卷定理2.2、3.1及命题4.1–4.2为此比较源上的 `repo-derived` 推导。紧区间矩唯一性与多项式逼近仅在定理3.1内部作为既有中间步骤使用，亦见 [Terminal Event Experiment 定理3.1(d)](RECURSIVE_RELATIONAL_OBSERVATION_TERMINAL_EVENT_EXPERIMENT.md) 中对原源的应用。

**定义 1.2（原取得接口、档案与共同参数命题）。** 已读区域从根开始且始终为连通区间。活动时每步只允许向 $L$ 或 $R$ 取得该侧一条未读边，支付一单位新边数。回答 $0$ 表示两端不同，回答 $1$ 表示两端相同。式（CPI.1）禁止 $11$，故回答 $1$ 是 $00$ 标记；接口在首次标记立即吸收，此后只给固定拒绝。策略的动作只能可测地依赖原种子和已获有限动作—回答词，等待策略在每个活动步骤都查询。完整有限终止档案记为

$$
H=\bigl(U;(J_1,0),\ldots,(J_{T-1},0),(J_T,1)\bigr).
\tag{CPI.3}
$$

其中 $T$ 为已支付边数，$\ell_T,r_T$ 为左右已获边数，$\ell_T+r_T=T$，空间范围为 $[-\ell_T,r_T]$。有限记录空间取离散可测结构，完整档案空间取与 $\mathcal U$ 的乘积结构；可另添一个无限未终止符号，使终止前的定义也总有取值。保留档案的任务允许读取已保留的 $U$ 和旧记录，不为终止后的原生接口增加读取端口。共同参数命题为

$$
\Lambda(\mathsf D)=1,\qquad
\mathsf D=\{(x,y)\in(0,1)^2:x=y\}.
\tag{CPI.4}
$$

“由实验律辨识”指这个性质在给定策略的整个档案分布的每条纤维上不变。分布是数学上的整个概率测度，不是一份实际档案，也不包含重置、重复取得或精确求值该测度的操作许可。

源的路径回放、首次标记吸收和根位锚定沿用 PG27 的组合结构。相应的原源数学供应分别可见 [AdaptiveMarkerStoppingTails](../../../D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.lean) 的 `actualRun`、`zeroReplay`、`stopped_execution_replay_bridge`、`armLaw`、`conditionalSourceLaw`、`jointLaw`、`arm_alternating_mass`、`conditional_no_marker_cylinder_mass`。这些声明的概率源使用一个共同参数；下面的双参数概率式由式（CPI.2）推导。

**命题 1.3（对角推送精确还原原共同源）。** 对任意 $(0,1)$ 上的 Borel 概率测度 $\mu$，令 $\Delta(q)=(q,q)$。在假设1.1中取 $\Lambda=\Delta_\#\mu$，则源、原种子及任意定义1.2策略的全部实际档案的联合律，等于 PG27 在相同 $a,b,\mu,\lambda$ 与相同策略下的联合律。反之，若式（CPI.4）成立，令 $\mu=(\operatorname{pr}_L)_\#\Lambda$，则 $\Lambda=\Delta_\#\mu$。

证明。原源也可由式（CPI.2）的独立均匀族实现，只须把两处 $Q_s$ 都代入同一次抽出的 $Q\sim\mu$。映射

$$
(u,q,x,v)\longmapsto(u,(q,q),x,v)
\tag{CPI.5}
$$

把该原始乘积测度推送为 $\lambda\otimes\Delta_\#\mu\otimes(p_0\delta_0+p_1\delta_1)\otimes\operatorname{Leb}^{\otimes(\{L,R\}\times\mathbb N_{>0})}$。递推给出的每一个源位逐坐标相同；策略读取同一原种子、同一已获词，所以按步归纳得到相同动作、回答和首次标记时间，吸收后的拒绝也相同。因此上述全部联合律相同。反向，在 $\mathsf D$ 上恒有 $(Q_L,Q_R)=\Delta(Q_L)$，对任意 Borel 集推送即得 $\Lambda=\Delta_\#\mu$。没有把两个独立参数的相同边缘当成逐点相同。证毕。

## 2. 不依赖原种子的四步终止设计

**定义 2.1（交错互补的取得词）。** 令 $\pi_\square$ 在尚未标记时反复执行无限词

$$
w=LRRL\,LRRL\,LRRL\cdots,
\tag{CPI.6}
$$

首次标记即停止。这个策略不读取 $U$ 或隐藏参数，不需要种子含有任何随机位。记其首次标记时间为 $T$，令 $c_s(n)$ 为 $w$ 的前 $n$ 项中侧 $s$ 的次数。置 $P=Q_LQ_R$，并对 $k\ge0$ 定义

$$
t_k=\int(xy)^k\Lambda(dx,dy),\quad
u_k=\int x(xy)^k\Lambda(dx,dy),\quad
v_k=\int y(xy)^k\Lambda(dx,dy).
\tag{CPI.7}
$$

这些数均有限，$t_0=1$；$\nu_k$ 是数列符号，不是新的概率先验。

**定理 2.2（实际存活柱集与终止质量）。** 在假设1.1和定义2.1下，$T<\infty$ 几乎处处。对固定 $(q_L,q_R)\in(0,1)^2$、固定根 $x$，以 $\mathbb P_{q_L,q_R,x}$ 表示式（CPI.2）中先固定这些坐标再生成两臂的概率，令 $p=q_Lq_R$。精确的存活质量为

| 已付步数 $n$ | $(c_L(n),c_R(n))$ | $\mathbb P_{q_L,q_R,0}(T>n)$ | $\mathbb P_{q_L,q_R,1}(T>n)$ |
| --- | --- | --- | --- |
| $4k$ | $(2k,2k)$ | $p^k$ | $p^k$ |
| $4k+1$ | $(2k+1,2k)$ | $q_Lp^k$ | $p^k$ |
| $4k+2$ | $(2k+1,2k+1)$ | $p^{k+1}$ | $p^k$ |
| $4k+3$ | $(2k+1,2k+2)$ | $p^{k+1}$ | $q_Rp^k$ |

混合后的全部终止质量 $h_n=\Pr(T=n)$ 为

$$
\begin{aligned}
h_{4k+1}&=a(t_k-\nu_k),&
h_{4k+2}&=a(\nu_k-t_{k+1}),\\
h_{4k+3}&=b(t_k-v_k),&
h_{4k+4}&=b(v_k-t_{k+1}),\qquad k\ge0.
\end{aligned}
\tag{CPI.8}
$$

此外，$U$ 独立于 $T$ 及其所获动作—回答词，原种子律始终为 $\lambda$。

证明。在源支持上，标记前每条已获边的两端都不同，所以每条已获臂前缀从同一根开始交替。对于任意已查询长度 $(\ell,r)$，固定根零时左、右臂分别用了 $\lceil\ell/2\rceil,\lceil r/2\rceil$ 个 $0\to1$ 转移；固定根一时分别用了 $\lfloor\ell/2\rfloor,\lfloor r/2\rfloor$ 个。其余存活转移均为概率一的 $1\to0$。在固定同一 $(q_L,q_R,x)$ 后两臂才可相乘，故无标记柱集质量为

$$
q_L^{e_x(\ell)}q_R^{e_x(r)},\qquad
e_0(m)=\lceil m/2\rceil,\quad e_1(m)=\lfloor m/2\rfloor.
\tag{CPI.9}
$$

策略实际存活至 $n$ 当且仅当这两个长度为 $(c_L(n),c_R(n))$ 的臂前缀没有标记：存活时实际查询词是 $w$ 的前缀；反向，若此前缀均无标记，实际执行不会提前吸收。代入四种长度即得表中全部式子。这是将原源的交替柱集乘法分别用于两个参数，而非把原共同参数尾式中的 $q$ 静默换成一对参数。

对每个根分别用相邻存活质量之差求首次标记质量。根零只可能在块内第一、第二步标记，分别得到 $p^k(1-q_L)$、$p^kq_L(1-q_R)$；根一只可能在第三、第四步标记，分别得到 $p^k(1-q_R)$、$p^kq_R(1-q_L)$。再乘 $a,b$ 并对 $\Lambda$ 积分，得到式（CPI.8）。特别地，$\Pr(T>4k)=t_k$。由于 $0<P<1$ 处处，$P^k\to0$ 且由一控制，支配收敛给出 $t_k\to0$，所以有限终止的总质量为一。这不要求 $\mathbb E[T]$ 有限，也没有对未终止的源实施无限多次实际查询。

整个确定词及实际停止都是源坐标的可测函数，不读取独立的 $U$；因而对每个 $E\in\mathcal E$ 和 $n\ge1$，$\Pr(U\in E,T=n)=\lambda(E)h_n$。全部结论都通过原乘积测度积分成立，不对任意种子空间的单点作条件除法。证毕。

**命题 2.3（终端计数、空间范围与根的显式互译）。** 对定义2.1的每份实际有限档案，$T$ 与终端长度对 $(\ell_T,r_T)$、终端空间范围 $[-\ell_T,r_T]$ 可测互相恢复。真实根是已付步数的函数

$$
\chi(T)=
\begin{cases}
0,&T\equiv1,2\pmod4,\\
1,&T\equiv3,0\pmod4.
\end{cases}
\qquad X_0=\chi(T).
\tag{CPI.10}
$$

$(U,T)$ 可测恢复完整 $H$，并恢复该连通已获区间的全部绝对位；无须取得额外源边。于是 $T$、终端长度对和终端空间范围的整个分布含有相同的共同参数辨识信息。

证明。$T$ 给出定义2.1中的确定长度对 $(c_L(T),c_R(T))$，反向由两长度相加取回 $T$，空间范围的两个端点也逐一给出长度。若最后查询侧是 $s$，其标记前长度是 $c_s(T)-1$，此前全部边交替，最后标记的内端点为零。因此

$$
X_0=(c_s(T)-1)\bmod2.
\tag{CPI.11}
$$

当 $T=4k+1,4k+2$ 时，该侧总长度均为 $2k+1$；当 $T=4k+3,4k+4$ 时均为 $2k+2$，这给出式（CPI.10）。给定 $U,T$，按 $w$ 取前 $T$ 个动作，前 $T-1$ 个回答为零、最后一个为一，恢复式（CPI.3）。从式（CPI.11）的根沿每条已获臂交替，最后唯一标记边保持零，即恢复全部已获位。所有映射在可数记录截面上定义，故可测；它们不恢复未读臂。源的原始响应即使不直接输出根位，保留记录后仍允许这次有限回溯。证毕。

## 3. 整个终止律到共同参数关系的映射

**定理 3.1（单一合法设计辨识对角集中）。** 固定假设1.1的 $a,b$ 和任意原种子律。对任意 $\Lambda$，定义2.1的整个终止计数律 $h=(h_n)_{n\ge1}$、等价的终端空间范围律，确定下列数和测度：

$$
\begin{aligned}
t_k(h)&=\sum_{n>4k}h_n,\\
\nu_k(h)&=t_k(h)-h_{4k+1}/a,\\
v_k(h)&=t_k(h)-h_{4k+3}/b,\\
\rho_h&=( (x,y)\mapsto xy)_\#\Lambda.
\end{aligned}
\tag{CPI.12}
$$

其中 $\rho_h$ 是 $[0,1]$ 上唯一满足 $\int p^k\rho_h(dp)=t_k(h)$ 的 Borel 概率测度；它实际集中在 $(0,1)$。特别地，下面是从整个取得律到关系缺口的精确映射：

$$
\begin{aligned}
\mathcal J(h)
&=\nu_0(h)+v_0(h)-2\int\sqrt p\,\rho_h(dp)\\
&=\int(\sqrt x-\sqrt y)^2\,\Lambda(dx,dy)\ \ge0,\\
\mathcal J(h)=0
&\quad\Longleftrightarrow\quad\Lambda(\mathsf D)=1.
\end{aligned}
\tag{CPI.13}
$$

积分项可以直接写成所恢复尾坐标的极限。对每个整数 $m\ge1$ 令

$$
A_m(h)=\sum_{j=0}^{m}\sqrt{j/m}\binom mj
       \sum_{i=0}^{m-j}(-1)^i\binom{m-j}{i}\,t_{j+i}(h).
\tag{CPI.14}
$$

则 $A_m(h)\to\int\sqrt p\,\rho_h(dp)$，并有统一误差界

$$
\left|A_m(h)-\int\sqrt p\,\rho_h(dp)\right|
\le(4m)^{-1/4}.
\tag{CPI.15}
$$

若 $\mathcal J(h)=0$，共同参数的原先验也由该律唯一恢复为

$$
\mu=(p\mapsto\sqrt p)_\#\rho_h,
\qquad \Lambda=\Delta_\#\mu.
\tag{CPI.16}
$$

因此若一个比较源的 $\pi_\square$ 终止律等于某个原 PG27 共同源在该同一设计下的终止律，它必集中在对角线上，且具有相同的共同参数先验。

证明。定理2.2给 $t_k=\Pr(T>4k)$，式（CPI.8）给其余两个恢复式，故式（CPI.12）的前三式与式（CPI.7）相同。$P$ 的推送律确实具有这些矩。将它视为紧区间上的概率测度，若另一个概率测度具有相同矩，则二者对多项式积分相同；多项式在 $C([0,1])$ 中一致稠密，故它们对所有连续函数积分相同，从而是同一 Borel 测度。这正是原终止实验中使用的经典紧区间矩唯一性中间步骤，在此作用于乘积 $P$，没有假设 $Q_L,Q_R$ 独立或边缘相等。

式（CPI.14）来自通常的 Bernstein 多项式

$$
B_m(p)=\sum_{j=0}^{m}\sqrt{j/m}\binom mj p^j(1-p)^{m-j}.
\tag{CPI.17}
$$

展开 $(1-p)^{m-j}$ 后对 $\rho_h$ 积分，恰得 $A_m(h)$。作为这一经典逼近步骤的定量界，若 $K$ 具有二项分布 $\operatorname{Bin}(m,p)$，则 $B_m(p)=\mathbb E\sqrt{K/m}$。利用 $|\sqrt u-\sqrt v|\le\sqrt{|u-v|}$、Cauchy–Schwarz 不等式及该二项分布的方差，有

$$
\begin{aligned}
|B_m(p)-\sqrt p|
&\le\mathbb E\sqrt{|K/m-p|}\\
&\le\bigl(\mathbb E|K/m-p|^2\bigr)^{1/4}
=\bigl(p(1-p)/m\bigr)^{1/4}
\le(4m)^{-1/4}.
\end{aligned}
\tag{CPI.18}
$$

因此对任意先验均得到式（CPI.15）和该极限，无需对未知的 $\Lambda$ 作有限支撑限制。这里的二项随机变量仅表示多项式的数学恒等式，不是给观察者增设的抽样操作。

又有 $\nu_0=\mathbb E Q_L$、$v_0=\mathbb E Q_R$，且 $\int\sqrt p\rho_h(dp)=\mathbb E\sqrt{Q_LQ_R}$；展开平方即得式（CPI.13）。被积函数非负，零点集恰为 $\mathsf D$。若积分为零，则对每个 $r\ge1$，其大于等于 $1/r$ 的集合质量不超过 $r\mathcal J(h)=0$；这些集合的并为 $\mathsf D^c$，故对角质量为一。反向在对角线上平方恒为零，积分也为零。这只把非负积分零的既有原则用于该实际取得律所恢复的缺口。

在对角线上 $P=Q_L^2$ 且 $Q_L>0$，故 $Q_L=\sqrt P$，得到式（CPI.16）并由命题1.3回到原源。若两个设计律相同，它们给同一 $\mathcal J$ 与 $\rho_h$；原共同源的缺口为零，比较源因而也为对角集中，并由式（CPI.16）给出同一 $\mu$。该恢复只针对共同参数性质及成立时的共同先验，不断言此设计在所有双参数先验上都是单射。证毕。

## 4. 取得不足与粗化的实际不可辨识例

**命题 4.1（始终向左的完整终止实验不辨识共同参数）。** 固定假设1.1中的任意 $a,b,\lambda$，使用活动时始终查询 $L$ 的确定等待策略 $\pi_L$。比较

$$
\Lambda_0=\delta_{(1/2,1/2)},\qquad
\Lambda_1=\delta_{(1/2,1/3)}.
\tag{CPI.19}
$$

两源下 $\pi_L$ 均几乎必然有限终止，完整原种子档案、终端长度、根和全部已获位的联合律相同；但 $\Lambda_0(\mathsf D)=1$、$\Lambda_1(\mathsf D)=0$。

证明。在式（CPI.2）中给两源使用同一 $U,X_0$ 和同一均匀坐标族。左臂参数同为 $1/2$，故其完整左臂逐坐标相同。策略只访问这条臂，所以取得的动作、回答、吸收时间和恢复的位都逐路径相同。固定根零时，存活 $n$ 步的概率为 $2^{-\lceil n/2\rceil}$；根一时为 $2^{-\lfloor n/2\rfloor}$，二者均趋于零，因此终止概率为一。右臂在比较实现中可以不同，但从未被这个策略取得；对角质量的差别由式（CPI.19）直接得到。证毕。

**命题 4.2（四步块计数和根仍可丢失共同参数关系）。** 对定义2.1的设计，只保留

$$
N=\lfloor(T-1)/4\rfloor
\tag{CPI.20}
$$

以及恢复的根 $X_0$ 和原种子 $U$。则对每个 $E\in\mathcal E$、$x\in\{0,1\}$、$k\ge0$，

$$
\Pr(U\in E,X_0=x,N=k)
=\lambda(E)p_x\int p^k(1-p)\,\rho_h(dp).
\tag{CPI.21}
$$

此粗律恰好确定乘积律 $\rho_h$，但不能辨识共同参数命题。例如

$$
\widetilde\Lambda_0=\delta_{(1/2,1/2)},\qquad
\widetilde\Lambda_1=\delta_{(1/3,3/4)}
\tag{CPI.22}
$$

给出相同的 $(U,X_0,N)$ 律，一个对角集中，另一个完全不在对角上。相反，它们在完整终止计数律下可区分。

证明。$N\ge k$ 当且仅当 $T>4k$。定理2.2的第一行对两个根均为 $P^k$，故固定根的相邻块尾之差为 $P^k(1-P)$；乘根质量、对联合先验和原种子积分即得式（CPI.21）。该式表明粗律由 $\rho_h$ 决定；反向对 $N\ge k$ 求概率，得到 $t_k$，再用定理3.1内部的紧区间矩唯一性取回 $\rho_h$。这没有恢复块内停止位置。

式（CPI.22）中的乘积都为 $1/4$，所以两源给相同粗律，且两个根值都保留其原来的正质量。它们的对角质量分别为一和零。完整律则已在第一步不同：式（CPI.8）给第一源 $h_1=a/2$，第二源 $h_1=2a/3$，由 $a>0$ 严格区分。这说明保留共同乘积、终端根和已完成块数仍可合并关系不同的实际源；定理3.1用到的块内质量正是被这次粗化丢弃的关系。证毕。

## 追加锚（本行以下为增补区）

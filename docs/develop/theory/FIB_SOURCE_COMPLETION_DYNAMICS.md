# FIB 来源联合完成与剥离动力学

## 1. 有限来源、组成与经典条带

**定义 1.1（来源与方向）。** 令 $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$，并固定

$$
\phi=\frac{1+\sqrt5}{2},\qquad \psi=-\phi^{-1},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
\alpha=\binom10,\qquad \beta=M\alpha=\binom01.
$$

外部单位位，即权重 $F_2=1$ 的位，恒为零。来源地址的第 $j$ 位对应权重 $F_{j+3}$，因此地址首位对应 $F_3=2$。本卷的有限来源集合为

$$
D=\{b\in\{0,1\}^{\mathbb N}:b_jb_{j+1}=0\text{ 对所有 }j\ge0,
\ b_j=0\text{ 对所有充分大的 }j\}.
$$

有限词按高位补零识别；不存在独立的长度坐标或 End 读出。全零地址 $0^\infty$ 属于 $D$。词 $u=u_0\cdots u_{k-1}$ 一律按低位到高位书写。其组成、数量与首接缝分别为

$$
t_u=\sum_{j<k}u_jM^j\alpha,\qquad
x(b)=\sum_{j\ge0}b_jM^j\alpha,\qquad
q(a,b)=2a+3b,\qquad s(b)=b_0.
$$

空词的组成为零。这里的 $q$ 是整数格上的行向量 $(2,3)$，不与来源地址中的字母混同。

**命题 1.2（数量与组成）。** 对每个 $j\ge0$，$q(M^j\alpha)=F_{j+3}$。故来源 $b\in D$ 的数量为 $q(x(b))=\sum_jb_jF_{j+3}$。组成映射 $x:D\to\mathbb Z^2$ 单射，且 $x(b)=0$ 当且仅当 $b=0^\infty$。

证明。$M^2=M+I$，而 $q(\alpha)=2,q(M\alpha)=3$，给出同一 Fibonacci 递推与初值。为直接说明唯一性，考虑权重 $F_2,\ldots,F_k$ 的合法非相邻和的最大值 $S_k$，取 $S_1=0,S_2=1$。按是否占用最高位分解，得到 $S_k=\max(S_{k-1},F_k+S_{k-2})=F_{k+1}-1$，最后一步由归纳及 Fibonacci 递推得出。故两个不同合法表示若在最高的不同位置 $k$ 分别为一、零，前者在该位及以下的数量至少为 $F_k$，后者至多为 $S_{k-1}=F_k-1$，更高相同位又相互抵消，数量不可能相同。将固定的零单位位并入这一论证，得到 $D$ 上数量映射单射，因而组成也单射。各非零位的数量权重严格为正，故数量为零只能来自全零来源。$\square$

**约定 1.3（母卷输入及坐标翻译）。** 使用母卷 [《FIBONACCI_ATOMIC_RELATION_GENERATION》](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的命题 182.1：对整数 $z=(a,b)$，在 $q(z)>0$ 的前提下，$z$ 是单位位为零的实际规范来源组成，当且仅当

$$
-1<a+b\psi<\phi.
$$

这是正数量命题；零来源另由命题 1.2 处理。将三位地址分组为五种合法窗口，只改变记法，不改变这个命题的来源域。

设

$$
P(z)=a+\phi b,\qquad E(z)=b-\phi a=-\phi(a+b\psi).
$$

条带等价于 $-\phi^2<E(z)<\phi$。对于实际来源，$P(x(b))=\sum_jb_j\phi^j$，而 $a+b\psi=\sum_jb_j\psi^j$。这正是经典黄金基整数的两个共轭坐标：Gazeau–Verger-Gaugry [2] 的 Proposition 3.1、式 (3.2)，第 2444 页，以及式 (3.11)，第 2445 页，在 Case (i) 取 $\beta=\phi$ 时刻画的是

$$
\mathbb Z_\phi^+
=\{a+b\phi\in\mathbb Z[\phi]:a+b\phi\ge0,
\ -1<a+b\psi<\phi\}.
$$

文献此处包含零，并要求非负实坐标 $P(z)$；母卷的实际来源识别使用严格正整数数量 $q(z)>0$。两者的坐标对应如上，不能省去各自的正性条件。[2] 将该条带结果归于 Burdík–Frougny–Gazeau–Krejčar [3]。本卷直接复用该条带，不另赋予它新的数学归属。

母卷命题 161.1 与推论 161.2 还给出：在单位位、低位合法前缀固定且没有 End 承诺时，每个数量模余数都能由正数量有限延长实现，单靠前缀拓扑不存在连续的全部有限来源数量模解码器。这是标量数量结果。下一节的二维共同实现由显式构造证明。

## 2. 远端共同实现与完整乘积完成

**定义 2.1（联合有限观察）。** 令

$$
\Omega=\{\omega\in\{0,1\}^{\mathbb N}:\omega_j\omega_{j+1}=0\},\qquad
G=\widehat{\mathbb Z}^{2},\qquad K=\Omega\times G.
$$

$\Omega$ 取前缀拓扑；$\widehat{\mathbb Z}=\varprojlim_m\mathbb Z/m\mathbb Z$ 按整除关系取全模数逆极限。记标准嵌入为 $\iota:\mathbb Z^2\hookrightarrow G$。整数矩阵及行向量 $q$ 按每层模运算延拓到 $G$，所以 $qz$ 是一个 profinite 整数，$qz\bmod m$ 是其有限读数。对于合法长度 $L$ 的词集合 $W_L$、整数 $m\ge1$，实际联合观察是

$$
Q_{L,m}(b)=(b|_L,x(b)\bmod m).
$$

在 $K$ 上用同一记号表示延拓 $Q_{L,m}(\omega,z)=(\omega|_L,z\bmod m)$。

联合观察一致性意指具有相同有限低位前缀与相同二维模余数。相应一致结构由这些有限观察的相等关系生成。接缝已经是地址首位，不另加一个独立二点坐标。

**引理 2.2（显式远端向量补偿）。** 给定任意 $L\ge0$、$p\in W_L$、$m\ge1$ 与 $r\in(\mathbb Z/m\mathbb Z)^2$，存在同一个 $b\in D$，满足 $b|_L=p$ 及 $x(b)\equiv r\pmod m$。新增非零位可全部位于任意预指定的远处之后。

证明。$m=1$ 时补零即可；若要求远端有非零位，在远处添加一个孤立一。设 $m\ge2$。因 $\det M=-1$，$M\bmod m$ 属于有限群 $\operatorname{GL}_2(\mathbb Z/m\mathbb Z)$。取其阶的一个倍数 $T\ge3$，使 $M^T\equiv I\pmod m$。令

$$
t_p=\sum_{j<L}p_jM^j\alpha,\qquad
r-t_p\equiv A\alpha+B\beta\pmod m,
\qquad 0\le A,B<m.
$$

选足够远的 $T$ 的倍数 $N\ge L+1$。保留 $p$，并且只在下列高位添加一：

$$
N+iT\quad(0\le i<A),\qquad
N+(A+j)T+1\quad(0\le j<B).
$$

第一组内部间距为 $T$，第二组也是 $T$；两组均非空时，交界间距为 $T+1$。首个新增位与前缀最后位置间距至少二。因此全部接缝合法，得到有限支持来源。两组模贡献分别为 $A\alpha$ 与 $B\beta$，故总组成余数为 $r$。

若 $A=B=0$ 而还要求远处确有非零位，或者要求在已构造来源之外再延长，可以在所有已用位置之上选 $m$ 个指数为 $T$ 倍数、间距为 $T$ 的位置置一。它们贡献 $m\alpha\equiv0\pmod m$。这同时保持前缀、余数和合法性。整个证明始终使用同一个来源，未将分别可达的两个边缘拼成联合实现。$\square$

**定理 2.3（联合完成）。** 每个 $Q_{L,m}$ 的实际像恰为 $W_L\times(\mathbb Z/m\mathbb Z)^2$。这些像在前缀截断与模约化下的逆极限为 $K$，而

$$
\Gamma=\{(b,\iota(x(b))):b\in D\}
$$

在 $K$ 中稠密。$K$ 是定义 2.1 指定的一致结构的紧致完成。

证明。实际像的满射性就是引理 2.2。$L\le L'$ 且 $m\mid m'$ 时，连接映射分别截取词与约化余数，因而逆极限分解为

$$
\varprojlim_{L,m}\bigl(W_L\times(\mathbb Z/m\mathbb Z)^2\bigr)
=\left(\varprojlim_LW_L\right)\times
\left(\varprojlim_m(\mathbb Z/m\mathbb Z)^2\right)
=K.
$$

有限多个模条件并入最小公倍数，有限多个前缀条件并入最长前缀。每个非空基本开集遂由引理 2.2 命中 $\Gamma$。两因子都是紧致 Hausdorff 空间；有限观察分离 $K$ 的点，给出其紧致一致结构，并在 $\Gamma$ 上诱导所声明结构。紧致 Hausdorff 一致空间完备，稠密嵌入因此实现所需完成。

具体地，对于任意 $(\omega,z)\in K$，逐次取 $b^{(n)}\in D$，满足 $b^{(n)}|_n=\omega|_n$ 且 $x(b^{(n)})\equiv z\pmod{n!}$，则 $(b^{(n)},\iota(x(b^{(n)})))\to(\omega,z)$。$\square$

**命题 2.4（完成点与未经补偿的截断）。** $\Gamma$ 是可数稠密真子集，其点恰是最终零地址配上该地址的实际整数组成。若 $\omega$ 有无限多个一，则原始截断和

$$
t_L(\omega)=\sum_{j<L}\omega_jM^j\alpha
$$

在 $G$ 中不收敛。因此一般完成点 $(\omega,z)$ 的 $z$ 不能解释为该原始和的极限。

证明。每个最终零地址只有一个实际组成；无限支持地址没有有限来源代表。$D$ 可数，而 $K$ 不可数，故 $\Gamma$ 为真子集。若截断和在 $G$ 中收敛，其模二余数必最终恒定。但每次经过占用位置 $j$，差为 $M^j\alpha\not\equiv0\pmod2$，因为 $M\bmod2$ 可逆。无限多个这样的差排除最终恒定。定理 2.3 的近似来源使用可变的远端补偿尾，与原始截断不同。$\square$

**推论 2.5（无有限 End 证书）。** 任意给定的有限前缀和有限多个模观察，都同时容纳某个来源及在任意远处另有非零位的有限来源。因此这些观察不能认证未读高位全部为零。

证明。合并模数后，使用引理 2.2 末段的零余数远端延长。即使观察来自零来源也成立。$\square$

## 3. 自然移位、剥离与投影逆的障碍

**定义 3.1（自然移位与添位）。** 记 $\sigma\omega=(\omega_1,\omega_2,\ldots)$，$\Omega_i=\{\omega:\omega_0=i\}$，$K_i=\Omega_i\times G$。定义

$$
R(\omega,z)=h_0(\omega,z)=(0\omega,Mz),
$$

$$
h_1:K_0\longrightarrow K_1,\qquad
h_1(\omega,z)=(1\omega,\alpha+Mz),
$$

$$
\delta:K\longrightarrow K,\qquad
\delta(\omega,z)=(\sigma\omega,M^{-1}(z-\omega_0\alpha)).
$$

$R$ 是在最低端添加一个零；$R^3$ 才是添加一个三位零窗口。添一的守卫是原首位为零。$M^{-1}=\left(\begin{smallmatrix}-1&1\\1&0\end{smallmatrix}\right)$ 为整数矩阵，所以以上算术公式在 $G$ 上有意义。

**命题 3.2（分支、部分逆与前像数）。** $h_0:K\to K_0$ 与 $h_1:K_0\to K_1$ 均为同胚，逆分别为 $\delta|_{K_0}$ 与 $\delta|_{K_1}$。$\delta$ 是满射局部同胚，并且

$$
|\delta^{-1}(\nu,w)|=
\begin{cases}
2,&\nu_0=0,\\
1,&\nu_0=1.
\end{cases}
$$

这些映射保持实际来源图，且 $\delta(\Gamma)=\Gamma=\delta^{-1}(\Gamma)$。

证明。前置零始终合法，前置一恰在尾首位为零时合法；直接代入公式得到两组互逆关系。$K_0,K_1$ 是闭开集，覆盖 $K$，所以 $\delta$ 局部为同胚。$h_0$ 给每个目标一个前像，$h_1$ 在且仅在目标首位零时给另一个前像，且首位不同使二者不同。

对实际来源，恒等式 $x(b)=b_0\alpha+Mx(\sigma b)$ 证明剥离保持实际性，合法添位也保持实际性。若 $\delta(\omega,z)=(b,\iota(x(b)))\in\Gamma$，则 $\omega=sb$ 最终为零，且 $z=s\alpha+M\iota(x(b))=\iota(x(sb))$，所以全部前像实际。由 $h_0$ 的存在又有 $\delta(\Gamma)=\Gamma$。$\square$

**定义 3.3（仅接缝—算术观察）。** 只保留首位及全部组成余数的完成为

$$
C=\{0,1\}\times G,\qquad
\Pi:K\to C,\quad \Pi(\omega,z)=(\omega_0,z).
$$

记 $j_C(b)=(b_0,\iota(x(b)))$。实际像为 $C_D=j_C(D)$，取 $C$ 的子空间拓扑。引理 2.2 取 $L=1$ 说明它在 $C$ 中稠密。实际移位定义为 $R_D(j_C(b))=j_C(0b)=(0,\iota(Mx(b)))$。

**命题 3.4（投影移位与三个不同的逆问题）。** 自然移位下降为

$$
R_C(s,z)=(0,Mz),\qquad \Pi R=R_C\Pi.
$$

每个 $(0,w)$ 恰有两个 $R_C$ 前像，首位一的点没有前像。$\Pi$ 的每个纤维却都是不可数的。另一方面，实际移位 $R_D:C_D\to R_D(C_D)$ 是双射，但其逆在定义域的每一点都不连续。

证明。$M$ 在 $G$ 上为自同构，所以 $(0,w)$ 的两个前像准确是 $(0,M^{-1}w)$ 与 $(1,M^{-1}w)$。而 $\Pi^{-1}(s,z)=\Omega_s\times\{z\}$ 不可数：首位固定后，在足够高的偶数位置可以独立选择一或零，其他位置取零。

实际来源由组成唯一识别，故 $R_D$ 单射，并按定义对自身像满射。固定任意 $b\in D$。对每个 $n$，引理 2.2 给 $c_n\in D$，使 $(c_n)_0=1-b_0$，$x(c_n)\equiv x(b)\pmod{n!}$。于是

$$
R_D(j_C(c_n))=(0,\iota(Mx(c_n)))\longrightarrow
(0,\iota(Mx(b)))=R_D(j_C(b))
$$

在实际像子空间中成立；但逆像 $j_C(c_n)$ 的首接缝恒为 $1-b_0$，不可能趋向 $j_C(b)$。因此实际逆在 $R_D(j_C(b))$ 不连续。$b$ 任意，得到处处不连续。完成映射的二对一、投影的不可数纤维、实际双射的逆不连续，是三条不同陈述。$\square$

**命题 3.5（剥离不下降到 $C$）。** 不存在映射 $d_C:C\to C$ 满足 $\Pi\delta=d_C\Pi$，即使不要求 $d_C$ 连续。

证明。取 $p=(0^\infty,z)$ 与 $p'=(010^\infty,z)$，二者旧首位同为零且算术坐标相同，故 $\Pi p=\Pi p'$。但 $\Pi\delta p=(0,M^{-1}z)$，$\Pi\delta p'=(1,M^{-1}z)$，二者不同。完整地址保存下一首位，因而命题 3.2 的总剥离在 $K$ 上闭合。$\square$

## 4. 指定有限实验的观察等价与最小边界

**定义 4.1（动作及读出合同）。** 一个有限脚本是一列有限条指令，动作仅允许 $R$、总动作 $\delta$ 和带守卫的 $h_1$；读出指令为任意声明模数 $m\ge1$ 下的 $q(z)\bmod m$。每个成功动作记录成功标记；$h_1$ 在 $K_0$ 外记录失败并立即终止该脚本，不再执行后续指令。脚本的迹是这些成功、失败及数量余数的有限记录。不同脚本分别在同一个初态上定义各自的迹，不要求在一次破坏性失败后重新使用同一份状态。

迹的观察一致结构由有限组脚本迹相等的关系生成。这里没有精确整数数量读出、End 证书、无限时刻记录或完整历史读出。失败是该实验的终止结果，不是正常空间 $K$ 内的后继点。

**定理 4.2（有限实验一致结构恰为联合观察）。** 在 $K$ 以及其稠密实际子集 $\Gamma$ 上，定义 4.1 的迹一致结构与定义 2.1 的有限前缀—向量余数一致结构相同。

证明。先从联合观察控制迹。固定一个有限脚本。每次 $R$ 或成功 $h_1$ 只添加一个已知位，每次 $\delta$ 只删除一个首位。所有守卫只询问当前首位。因此，长度至多为“脚本中 $\delta$ 的总数加一”的初始前缀，足以决定全程符号行为与首次失败位置。算术坐标沿每个已确定的成功分支作整数仿射变换，由 $M,M^{-1}$ 和 $\alpha$ 组合而成。将脚本所有读出模数并入一个最小公倍数 $m$，初始 $z\bmod m$ 遂决定所有余数输出。有限组脚本取最大所需前缀长度及共同模数。因此某个 $Q_{L,m}$ 的相等关系包含于这组迹的相等关系。脚本迹也由此成为连续的有限值函数。

反方向，固定 $L,m$。对于每个 $0\le j<L$，执行脚本“$\delta^j$ 后尝试 $h_1$”。前面的剥离总能执行，最后添一成功当且仅当 $\omega_j=0$；失败当且仅当 $\omega_j=1$。这组实验准确恢复前 $L$ 位。另取两个读数脚本，分别在初态读取 $qz\bmod m$，以及先作 $R$ 再读取 $qMz\bmod m$。因为

$$
\begin{pmatrix}q\\qM\end{pmatrix}
=\begin{pmatrix}2&3\\3&5\end{pmatrix},\qquad
\det\begin{pmatrix}2&3\\3&5\end{pmatrix}=1,
$$

两读数在每个模数下都恢复整个向量余数，具体恢复矩阵为 $\left(\begin{smallmatrix}5&-3\\-3&2\end{smallmatrix}\right)$。故有限组迹相等迫 $Q_{L,m}$ 相等。两方向均为有限观察关系的包含，正是所需一致结构相等；限制到 $\Gamma$ 仍成立。$\square$

**定理 4.3（限定于该合同的紧致商最小性）。** 设 $Y$ 为紧致 Hausdorff 空间，$\theta:K\to Y$ 是连续满射。若每个定义 4.1 的脚本迹都能通过 $\theta$ 忠实读出，即对每个脚本 $e$ 存在函数 $\bar T_e:Y\to\operatorname{Trace}(e)$ 使 $T_e=\bar T_e\theta$，则 $\theta$ 为同胚。

证明。若 $\theta(p)=\theta(p')$，所有脚本迹相同。定理 4.2 的反向构造使二者具有相同任意有限前缀与任意向量模余数。故其地址相同、profinite 坐标相同，因而 $p=p'$。$\theta$ 单射；连续紧致到 Hausdorff 的双射为同胚。因为 $\theta$ 是商映射，而 $T_e$ 连续，已存在的 $\bar T_e$ 也连续。若 $Y$ 自身携带忠实的动作、守卫与读出，当然满足这里的迹因子条件。结论只涉及所指定实验族及连续紧致 Hausdorff 商。$\square$

**反例 4.4（只有删零逆时的首个一摘要）。** 将动作合同削弱为 $R$、仅在首位零时可执行的 $\delta|_{K_0}$，以及有限模数量读出。令

$$
\ell(\omega)=\min\{j:\omega_j=1\},\qquad \ell(0^\infty)=\infty.
$$

取 $\mathbb N\cup\{\infty\}$ 的一点紧化拓扑。映射 $(\omega,z)\mapsto(\ell(\omega),z)$ 连续满射到 $(\mathbb N\cup\{\infty\})\times G$，并保持这套弱合同：$R$ 使 $\ell$ 加一，删零在 $\ell>0$ 时使其减一，$\infty$ 始终保持，算术更新分别为 $Mz$ 与 $M^{-1}z$。定义域与失败由 $\ell=0$ 决定。可是地址 $100^\infty$ 与 $1010^\infty$ 配同一个 $z$ 时被合并。故这套弱合同允许真商，不能从仅有删零逆推出定理 4.3 的全地址最小性。

## 5. 合法前缀、完整共同尾与带时差群胚

**定义 5.1（前缀映射的合法域）。** 对合法词 $u$，长度记为 $k$，令

$$
F_u=\begin{cases}
\Omega,&k=0\text{ 或 }u_{k-1}=0,\\
\Omega_0,&u_{k-1}=1,
\end{cases}\qquad
h_u:F_u\times G\longrightarrow [u]\times G,
$$

$$
h_u(\nu,w)=(u\nu,t_u+M^kw).
$$

$[u]$ 表示地址以 $u$ 开头。前缀字母按低位到高位排列；若以一步添位实现 $h_u$，实际动作依次添加 $u_{k-1},\ldots,u_0$，即 $h_u=h_{u_0}\circ\cdots\circ h_{u_{k-1}}$，每步保留其守卫。

**命题 5.2（前缀与迭代公式）。** $h_u$ 是到 $[u]\times G$ 的同胚，逆为 $\delta^k$ 在该柱集上的限制，并且对任意 $p=(\omega,z)\in K$，

$$
\delta^k p=\left(\sigma^k\omega,
M^{-k}(z-t_{\omega|_k})\right).
$$

若 $u,v$ 长度分别为 $k,l$，则由共同尾 $(\nu,w)\in(F_u\cap F_v)\times G$ 给出的前缀替换 $h_v(\nu,w)\mapsto h_u(\nu,w)$ 具有公式

$$
z_p=t_u+M^{k-l}(z_q-t_v).
$$

完整共同尾条件准确是

$$
\sigma^k\omega_p=\sigma^l\omega_q=\nu,\qquad
M^{-k}(z_p-t_u)=M^{-l}(z_q-t_v)=w,
\qquad \nu\in F_u\cap F_v.
$$

证明。跨接缝合法性只有 $u_{k-1}\nu_0=0$，恰由 $F_u$ 表达。反复使用 $\delta$ 的定义，归纳得到迭代公式，随即给出 $h_u$ 的逆；算术仿射映射与符号前置、截断连续，故为同胚。消去共同算术尾 $w$ 得替换公式，反代即得到必要充分条件。$\square$

仅符号尾相同不足够。例如 $p=(0^\infty,0)$ 与 $q=(0^\infty,\iota(\alpha))$ 地址全部相同，但任意剥离后的算术坐标分别是零与 $M^{-l}\alpha\ne0$，没有完整共同尾。

**定义 5.3（带时差群胚与仿射参数）。** 定义

$$
\mathcal G_\delta
=\{(p,n,q):\text{存在 }k,l\ge0, n=k-l,
\ \delta^kp=\delta^lq\}.
$$

箭头从 $q$ 指向 $p$。单位为 $(p,0,p)$，逆为 $(q,-n,p)$，乘法为

$$
(p,n,q)(q,m,r)=(p,n+m,r).
$$

合法词 $u,v$ 与开集 $O\subseteq(F_u\cap F_v)\times G$ 定义开双截面

$$
Z(u,v,O)=\{(h_u(t),|u|-|v|,h_v(t)):t\in O\}.
$$

这些双截面给出群胚拓扑。时差 $n$ 保留前缀长度差；对箭头取参数

$$
a=t_u-M^nt_v\in\mathbb Z^2,\qquad z_p=M^nz_q+\iota(a).
$$

**命题 5.4（群胚及半直积余循环）。** 上述乘法闭合，双截面的范围与来源映射均为到开集的同胚。参数 $(a,n)$ 不依赖共同尾表示，并满足

$$
(a,n)(b,m)=(a+M^nb,n+m).
$$

因而它是值于 $\mathbb Z^2\rtimes_M\mathbb Z$ 的仿射余循环。时差零的子群胚是等长共同尾等价关系，平移量按普通加法组合。

证明。设第一箭头由 $(k,l)$ 表示，第二由 $(k',l')$ 表示。则

$$
\delta^{k+k'}p=\delta^{l+k'}q=\delta^{l+l'}r,
$$

所以复合有时差 $(k+k')-(l+l')=n+m$；逆与单位也直接满足定义。每个箭头取自己的有限前缀，就属于某个 $Z(u,v,O)$。命题 5.2 使范围、来源在该集合上均为同胚。

为验证拓扑基的交性质，考虑一个同时属于 $Z(u,v,O)$ 和 $Z(u',v',O')$ 的箭头。两组时差相同，故可交换两组使 $|u'|=|u|+d$、$|v'|=|v|+d$，$d\ge0$。共同尾等式迫存在同一个合法长度 $d$ 词 $a$，使 $u'=ua,v'=va$。交集在该箭头附近由较长词对表示，尾域为 $O'\cap h_a^{-1}(O)$，并保留双方的合法尾域。这是开集，给出仍在交集内的双截面。不同的时差没有交集。因此上述集合确成拓扑基。逆只交换两个前缀。对于两个可合成双截面，匹配的中间地址前缀必相容；把较短中间前缀延长到较长者，并将同一尾前缀同时延长它对应的另一端，便得到共同中间词 $w$。局部乘积于是把词对 $(u,w)$、$(w,v)$ 送到 $(u,v)$，尾域为两个开尾域的交，尾参数不变。这证明乘法连续。

算术公式给 $\iota(a)=z_p-M^nz_q$，标准整数嵌入单射，故 $a$ 唯一。若将共同尾前缀 $v'$ 同时添到两词后，则 $t_{uv'}=t_u+M^kt_{v'}$、$t_{vv'}=t_v+M^lt_{v'}$，新增项在 $t_{uv'}-M^{k-l}t_{vv'}$ 中抵消。两个可合成算术仿射式复合，直接得到 $a+M^nb$。$n=0$ 时可且必须以等长词表示，遂为普通整数平移。$\square$

仿射等式本身不能替代合法域和符号共同尾。在 $p_0=(0^\infty,0)$，每个 $(p_0,n,p_0)$，$n\in\mathbb Z$，都是箭头，其中非零 $n$ 给出非单位稳定子。把群胚仅记为点对关系，会把这些箭头与单位混同。

**定理 5.5（有限来源的稠密饱和轨道）。**

$$
\Gamma=\bigcup_{k\ge0}\delta^{-k}\{p_0\}.
$$

它是 $p_0$ 的完整群胚轨道，并对 $\mathcal G_\delta$ 饱和；它也在全部合法前缀替换下饱和。实际有限来源中唯一周期点是 $p_0$。

证明。实际来源删去全部占用位后同时得到零地址和零组成。反之，若 $\delta^kp=p_0$，命题 5.2 迫 $\sigma^k\omega=0^\infty$ 且 $z=t_{\omega|_k}$，即 $p\in\Gamma$。由命题 3.2，$\Gamma$ 在正向剥离及全部前像下保持；若 $\delta^kp=\delta^lq$ 且 $q\in\Gamma$，共同尾实际，故 $p$ 也实际。每个实际点与 $p_0$ 有箭头，且 $p_0$ 固定，故其轨道恰为 $\Gamma$。稠密性来自定理 2.3。实际点最终到达 $p_0$，若同时周期则只能等于 $p_0$。$\square$

## 6. Profinite 周期方程与三个周期点

**引理 6.1（非零整数乘法与整数右端）。** 设 $A$ 为整数二阶矩阵，$d=\det A\ne0$。则 $A:G\to G$ 单射，像为闭开子群，并且

$$
w\in AG\quad\Longleftrightarrow\quad
\operatorname{adj}(A)w\in dG.
$$

对整数右端 $c\in\mathbb Z^2$，方程 $Az=\iota(c)$ 在 $G$ 中有解，当且仅当 $c\in A\mathbb Z^2$；有解时唯一，且为整数向量 $\operatorname{adj}(A)c/d$ 的标准嵌入。

证明。非零整数 $d$ 的乘法在 $\widehat{\mathbb Z}$ 上单射：若 $dy=0$，对任意 $n$ 在模 $|d|n$ 中取 $y$ 的代表 $a$，则 $|d|n\mid da$，故 $n\mid a$。于是 $y\bmod n=0$ 对所有 $n$ 成立。伴随恒等式 $\operatorname{adj}(A)A=dI$ 遂证明 $A$ 单射。

像判据的必要性也由该恒等式给出。反之，若 $\operatorname{adj}(A)w=dz$，则 $d(Az-w)=0$，所以 $Az=w$。$AG$ 包含 $dG$。而 $d\widehat{\mathbb Z}$ 恰是约化到模 $|d|$ 的核：在模 $|d|n$ 取可被 $d$ 整除的代表，除以 $d$ 即得到兼容的模 $n$ 坐标。因此 $dG$ 开，$AG$ 也开；紧致像又保证 $AG$ 闭。

若 $c$ 为整数，则整数向量 $\operatorname{adj}(A)c$ 属于 $dG$ 当且仅当各坐标被 $d$ 整除，这是模 $|d|$ 的普通整数条件。候选解因此为整数；伴随恒等式保证它满足原方程，单射性保证唯一。$\square$

**命题 6.2（循环接缝与不可补救的周期纤维）。** 对 $k\ge1$，合法纯周期地址 $\omega=u^\infty$ 要求词内部和末位到首位的接缝均无相邻一。该地址上的 $\delta^k$ 固定点满足

$$
(I-M^k)z=t_u.
$$

它存在当且仅当 $-t_u\in(M^k-I)\mathbb Z^2$，存在时算术坐标唯一且为整数。若地址最小周期为 $d$，则它存在任何联合周期纤维，当且仅当存在 $\delta^d$ 固定纤维；联合最小周期也为 $d$。更长周期不能修复缺失的算术纤维。

证明。命题 5.2 给固定点方程。$M$ 的特征值为 $\phi,\psi$，两者的任何正次幂都不等于一，故 $\det(M^k-I)\ne0$。引理 6.1 给存在性、唯一性及整数性。联合周期必为符号最小周期 $d$ 的倍数。若 $\delta^{rd}p=p$，则 $\delta^dp$ 具有同一地址，也被 $\delta^{rd}$ 固定。同一地址的该固定算术坐标唯一，故 $\delta^dp=p$。反方向显然，最小周期由符号最小周期决定。$\square$

例如合法地址 $(100)^\infty$ 的三周期方程为 $(M^3-I)z=-\alpha$，而 $M^3-I=2M$。模二即矛盾，所以它没有任何联合周期纤维。

**定理 6.3（正常空间的完整周期分类）。** $\delta$ 在 $K$ 上的全部周期点为

$$
p_0=(0^\infty,0),\qquad
p_1=((10)^\infty,\iota(1,-1)),\qquad
p_2=((01)^\infty,\iota(-1,0)).
$$

$p_0$ 固定，$p_1,p_2$ 组成一个二周期。因此对每个 $n\ge1$，

$$
|\operatorname{Fix}(\delta^n)|=
\begin{cases}1,&n\text{ 为奇数},\\3,&n\text{ 为偶数}.\end{cases}
$$

证明。命题 6.2 使任意周期点的算术坐标为整数 $z=(a,b)$。将其地址沿周期双向延伸为 $(\omega_j)_{j\in\mathbb Z}$，相应算术轨道 $(z_j)$ 也周期，且

$$
z_j=\omega_j\alpha+Mz_{j+1},\qquad
P(Mz)=\phi P(z),\qquad E(Mz)=\psi E(z),\qquad
P(\alpha)=1,\quad E(\alpha)=-\phi.
$$

沿负索引迭代 $P(z_0)=\phi^{-1}(P(z_{-1})-\omega_{-1})$，周期有界项乘 $\phi^{-n}$ 后趋零，得到

$$
P(z)=-\sum_{n\ge1}\omega_{-n}\phi^{-n}.
$$

沿正索引迭代 $E(z_j)=-\phi\omega_j+\psi E(z_{j+1})$，同理得到

$$
E(z)=-\phi\sum_{j\ge0}\omega_j(-\phi^{-1})^j.
$$

两个级数都绝对收敛。循环接缝合法，使双向列仍无相邻一。第一式按位置 $(2j+1,2j+2)$ 分组，每对最多选一位，最大贡献来自较低指数，因此

$$
0\le\sum_{n\ge1}\omega_{-n}\phi^{-n}
\le\sum_{j\ge0}\phi^{-(2j+1)}=1.
$$

第二式的偶位贡献非正，奇位贡献非负。舍去不利项、将有利位全取一，分别给

$$
-1\le P(z)\le0,\qquad
-\frac{\phi}{1-\phi^{-2}}=-\phi^2
\le E(z)\le\frac1{1-\phi^{-2}}=\phi.
$$

反解线性坐标为

$$
a=\frac{P-\phi E}{\phi+2},\qquad
b=\frac{\phi P+E}{\phi+2}.
$$

由此得到明确格点界

$$
-1\le a\le\frac{\phi^3}{\phi+2}<2,\qquad
-2<-\frac{\phi^3}{\phi+2}\le b\le\frac{\phi}{\phi+2}<1.
$$

整数性迫 $a\in\{-1,0,1\}$、$b\in\{-1,0\}$。再施加 $-1\le a+\phi b\le0$：$b=0$ 时仅 $a=-1,0$；$b=-1$ 时仅 $a=1$。只剩 $(-1,0),(0,0),(1,-1)$。

$z=0$ 时，$P=0$ 迫所有负索引位零，周期性迫整个地址全零。$z=(-1,0)$ 时，$E=\phi$。上界等号要求每个偶位零、每个奇位一：任何遗漏的正项或出现的负项都会使和严格减小。因此地址为 $(01)^\infty$。$z=(1,-1)$ 时，$E=-\phi^2$；下界等号同理要求全部偶位一、奇位零，给 $(10)^\infty$。直接代入 $M^{-1}$ 验证

$$
\delta p_0=p_0,\qquad \delta p_1=p_2,\qquad \delta p_2=p_1.
$$

三个候选均实现，分类完整。二周期点地址无限支持且组成有负坐标，故不属于 $\Gamma$。$\square$

## 7. 一个有限图构造及其路径逆系统

**定义 7.1（有限图与无限路径因子）。** 对每个 $m\ge1$，令 $B_m=(\mathbb Z/m\mathbb Z)^2$。图 $\mathscr G_m$ 的顶点为 $V_m=\{0,1\}\times B_m$，边定义为

$$
(s,r)\longrightarrow(t,w)
\quad\Longleftrightarrow\quad
st=0\text{ 且 }w=M^{-1}(r-s\alpha)\pmod m.
$$

图无平行重边。令 $X_m$ 为该图的单边无限顶点路径空间，路径左移为 $\tau_m$；另记

$$
K_m=\Omega\times B_m,\qquad
\delta_m(\omega,r)=(\sigma\omega,M^{-1}(r-\omega_0\alpha)).
$$

有限的是图，而非 $X_m$ 或 $K_m$。一个顶点可以有两个后继；单值的剥离动力学作用于整条路径，不能把边关系当作顶点集合上的确定性动力学。

**命题 7.2（路径共轭与满射连接）。** 映射

$$
\Theta_m(\omega,r)=((\omega_j,r_j))_{j\ge0},\qquad
r_j=M^{-j}(r-t_{\omega|_j})\pmod m
$$

是 $K_m\to X_m$ 的同胚，满足 $\Theta_m\delta_m=\tau_m\Theta_m$。若 $m\mid n$，路径约化 $X_n\to X_m$ 连续满射，与左移交换，每条路径恰有 $(n/m)^2$ 个提升。而

$$
(K,\delta)\cong\varprojlim_m(X_m,\tau_m).
$$

证明。公式满足边递推。逆映射从整条路径取全部符号与初始余数，二者互逆且连续。连接映射保留符号并约化各余数。给定 $X_m$ 路径，任选初始余数的一个模 $n$ 提升，保留同一符号地址，按递推生成所有后续余数；这准确给出全部 $(n/m)^2$ 个路径提升。

兼容路径族在每层有相同符号地址，因为连接映射保留符号，任意两个模数有共同倍数。初始余数组成唯一 $z\in G$，后续余数由递推决定。$K$ 到该逆极限因而连续双射；紧致到 Hausdorff 使之为同胚，递推保证与动力学交换。也可使用共尾阶乘模数塔。$\square$

**定理 7.3（全部有限图原始）。** 对每个 $m\ge1$，$\mathscr G_m$ 强连通，其邻接矩阵原始，即某一正幂的每个元素均严格为正。更具体地，任意两个顶点之间，每个长度 $n\ge4m^2-2$ 都有路径。

证明。给定起终顶点 $(s,r),(t,w)$。引理 2.2 提供同一个有限来源 $b$，首位为 $s$，组成满足 $x(b)\equiv r-w\pmod m$。取 $M\bmod m$ 的周期 $T$，并选足够大的 $T$ 倍数 $n$，使全部来源非零位都在前 $n-1$ 位内，特别是 $b_{n-1}=0$。模一时可直接取 $T=1$。按前 $n$ 个来源位走图路径后，算术余数为

$$
r_n=M^{-n}(r-x(b))=w\pmod m.
$$

末个已读位零，允许下一符号为给定的 $t$，所以得到起点到目标的路径。这证明强连通，只使用完整向量共同实现。

顶点 $(0,0)$ 有一步自环。图有 $v=2m^2$ 个顶点，任意顶点到 $(0,0)$、以及 $(0,0)$ 到任意顶点，分别可取无重复顶点的路径，长度至多 $v-1$。对于任意 $n\ge2v-2$，在中间插入适量自环，得到恰长 $n$ 的路径。邻接矩阵所有这些幂均严格为正，证明原始性与所给界。$\square$

**反例 7.4（路径满射不保固定周期提升）。** $K_3$ 中地址 $(100)^\infty$、初始余数 $(2,1)$ 给出三周期点，因为

$$
(M^3-I)\binom21=2M\binom21=\binom26
\equiv-\alpha\pmod3.
$$

但模六下同一方程左侧第一坐标总为偶数，右侧为奇数，没有解。因此 $K_6\to K_3$ 的三周期固定点集合约化不满射。每条无限路径仍能提升，提升路径却未必保持周期三。各层分别存在的算术周期或随层变化的长周期，不能充当全 profinite 空间的同一周期。

## 8. 精确名字、拓扑熵与实际混合见证

**定义 8.1（分区和拓扑熵）。** 对 $L\ge1,m\ge1$，取闭开分区

$$
\mathcal P_{L,m}=
\{[u]\times\{z:z\bmod m=r\}:u\in W_L,\ r\in B_m\}.
$$

对于有限开覆盖 $\mathcal U$，以 $N(\mathcal U)$ 表示最小子覆盖数，定义

$$
h(\delta,\mathcal U)=\limsup_{n\to\infty}\frac1n
\log N\left(\bigvee_{j=0}^{n-1}\delta^{-j}\mathcal U\right),\qquad
h_{\rm top}(\delta)=\sup_{\mathcal U}h(\delta,\mathcal U).
$$

本卷使用自然对数。

**命题 8.2（全部非空有限名字的准确计数）。** 对所有 $n,L,m\ge1$，

$$
\left|\bigvee_{j=0}^{n-1}\delta^{-j}\mathcal P_{L,m}\right|
=m^2F_{n+L+1}.
$$

每个名字都由实际有限来源实现。长度 $L$ 的顶点路径记录则有 $m^2F_{L+2}$ 个；$L$ 条边记录包含 $L+1$ 个顶点。

证明。无相邻一词数满足 $|W_0|=1,|W_1|=2$；按首位零或首两位一零分解，得到 $|W_j|=|W_{j-1}|+|W_{j-2}|$，故 $|W_j|=F_{j+2}$。

连续 $n$ 次长度 $L$ 的地址观察共同覆盖位置 $0,\ldots,n+L-2$，即 $n+L-1$ 位。初始余数 $z\bmod m$ 与这一前缀决定全部后续余数 $M^{-j}(z-t_{\omega|_j})\bmod m$。反过来，全部观察窗口恢复这段前缀，第零次读出恢复初始余数。因此名字与 $W_{n+L-1}\times B_m$ 一一对应，数量如式。完整乘积允许全部组合，引理 2.2 给每个组合的实际见证。$L$ 个顶点的记录同理是长度 $L$ 符号词加一个初始余数，而边数约定多一个顶点。$\square$

**定理 8.3（拓扑熵）。** $h_{\rm top}(\delta)=\log\phi$，每个 $\delta_m$ 的拓扑熵也等于 $\log\phi$。

证明。互不相交的非空分区覆盖必须选取全部原子，故命题 8.2 与 $F_j=(\phi^j-\psi^j)/\sqrt5$ 给

$$
h(\delta,\mathcal P_{L,m})
=\lim_{n\to\infty}\frac{2\log m+\log F_{n+L+1}}n
=\log\phi.
$$

这些分区在所有有限开覆盖中共尾：对每个点，在包含它的某覆盖成员内取基本柱邻域；紧致性给有限个这种邻域覆盖 $K$。取最长前缀和全部模数的最小公倍数，所得 $\mathcal P_{L,m}$ 细化原覆盖。细化在逆像与联合下保持，因此所有覆盖的熵不超过 $\log\phi$；分区 $\mathcal P_{1,1}$ 已达到该值。固定 $m$ 时相同论证适用于 $K_m$。

额外算术信息的名字成本准确为一个 $2\log m$，而非每步重付该成本；后续模余数由初态和符号递推决定。熵定义先固定有限观察，再取时间增长率，最后对观察取上确界，不能将随时间增大的模数当作固定覆盖。$\square$

**定理 8.4（拓扑混合且有实际见证）。** 对任意非空开集 $U,V\subset K$，存在 $N$，使每个 $n\ge N$ 都满足

$$
\Gamma\cap U\cap\delta^{-n}V\ne\varnothing.
$$

因此 $\delta$ 拓扑混合。阈值可依赖所选开集的前缀长度与模数。

证明。各取包含于 $U,V$ 的基本柱，并细化为共同模数 $m$、非空合法词 $p,q$，长度分别为 $L,H\ge1$，初始余数分别为 $a,b$。从顶点 $(p_0,a)$ 沿 $p$ 走 $L-1$ 条边到达 $A$，令 $B=(q_0,b)$。定理 7.3 保证，当

$$
n\ge L-1+4m^2-2
$$

时，从 $A$ 到 $B$ 有恰长 $n-(L-1)$ 的桥段。其后接 $q$ 的剩余 $H-1$ 条边，再接零尾，得到合法符号路径。它以 $p$ 开头，在第 $n$ 位以 $q$ 开头，算术递推从 $a$ 到第 $n$ 步的 $b$。

该有限路径规定长度 $n+H$ 的前缀 $u$。引理 2.2 给同一个实际来源 $d$，具有该前缀且 $x(d)\equiv a\pmod m$。真实剥离的迭代公式保证第 $n$ 步组成余数为 $b$，地址前缀为 $q$。于是 $(d,\iota(x(d)))\in U\cap\delta^{-n}V$，对每个所述 $n$ 均成立。证明不需要全部模数共享阈值。$\square$

**命题 8.5（周期、混合与孤立错误分量）。** 正常系统的正熵、混合性与定理 6.3 的三个周期点相容。若另选可辨认的吸收错误点，载体及映射须另定义为

$$
K^+=K\sqcup\{\bot\},\qquad
\delta^+=\delta\sqcup\operatorname{id}_{\{\bot\}}.
$$

则 $K^+$ 不拓扑传递、不混合，熵仍为 $\log\phi$，奇数次迭代的固定点为两个，偶数次为四个。

证明。熵与混合分别要求有限轨道段数量及开集间长时间通达，都不要求这些段按同一周期在全部模数上闭合；反例 7.4 展示周期提升的额外障碍。因此不能以某一有限图的周期增长公式代替定理 8.3。

错误点是分离的孤立分量。取 $U=\{\bot\}$ 和任意非空正常开集 $V$，任意迭代都不相交，所以不传递。把 $\{\bot\}$ 加为每个分区的单独原子，名字数从 $m^2F_{n+L+1}$ 变为 $m^2F_{n+L+1}+1$；这些分区仍细化任意开覆盖，熵仍为 $\log\phi$。错误点另增一个固定点，故计数如述。

对应有限图应是 $\mathscr G_m$ 与一个分离自环顶点的不交并。若改为从各正常顶点加入出错边，则路径空间会记录出错以前的路径和时刻，已不是单一错误孤点。定义 4.1 的失败仅终止一个脚本，并不采用这些新增路径。$\square$

## 9. Parry–Haar 测度、强混合与熵唯一性

**定义 9.1（符号 Markov 测度与 Haar 测度）。** 黄金均值图的邻接矩阵、正向量与转移矩阵为

$$
A=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
r=\binom{\phi}{1},\qquad Ar=\phi r,\qquad
P_{st}=\frac{A_{st}r_t}{\phi r_s},\qquad
P=\begin{pmatrix}\phi^{-1}&\phi^{-2}\\1&0\end{pmatrix}.
$$

其平稳分布为

$$
\pi_0=\frac{\phi^2}{\phi^2+1},\qquad
\pi_1=\frac1{\phi^2+1}.
$$

记 $\nu$ 为初始分布 $\pi$、转移 $P$ 的单边平稳 Markov 测度，即合法柱的概率为

$$
\nu([s_0\cdots s_{k-1}])
=\pi_{s_0}\prod_{j=0}^{k-2}P_{s_js_{j+1}}.
$$

这些有限分布一致，因而定义 $\Omega$ 上的 Borel 概率；$\pi P=\pi$ 使它移位不变。记 $\mu$ 为 $G$ 的归一化 Haar 概率，其模 $m$ 推前为 $B_m$ 上的均匀概率 $u_m$。这些兼容均匀分布也直接定义 $\mu$；平移和整数可逆矩阵保持每层均匀分布，故保持 $\mu$。令 $\lambda=\nu\times\mu$。Parry [4] 是这一内禀 Markov 构造的经典出处；以下给出本卷所需的有限图及熵证明。

**命题 9.2（直接不变性与满支撑）。** $\lambda$ 在 $\delta$ 下不变且满支撑。

证明。对每个固定符号 $s$，$F_s(z)=M^{-1}(z-s\alpha)$ 保持 Haar 测度。因此对任意有界 Borel 函数 $f$，

$$
\begin{aligned}
\int_K f\circ\delta\,d\lambda
&=\int_\Omega\int_G
f(\sigma\omega,F_{\omega_0}(z))\,d\mu(z)\,d\nu(\omega)\\
&=\int_\Omega\int_G
f(\sigma\omega,w)\,d\mu(w)\,d\nu(\omega)\\
&=\int_\Omega\int_G f(\eta,w)\,d\mu(w)\,d\nu(\eta).
\end{aligned}
$$

最后一步使用 $\nu$ 的移位不变性，故直接证明联合不变。每个非空合法柱的 $\nu$ 测度正，每个模余数陪集的 $\mu$ 测度为 $m^{-2}>0$；这些乘积构成开集基，遂满支撑。$\square$

**命题 9.3（有限图的正特征向量与准确转移）。** 记 $\mathscr G_m$ 的邻接矩阵为 $A_m$。其正右、左特征向量分别可取

$$
R_{(s,z)}=r_s,\qquad L_{(s,z)}=r_s,
$$

特征值均为 $\phi$，谱半径恰为 $\phi$。对应转移与平稳分布为

$$
Q_m(v,w)=\frac{A_m(v,w)R_w}{\phi R_v},\qquad
\Pi_m(s,z)=\frac{\pi_s}{m^2}.
$$

通过命题 7.2 的路径共轭，$\nu\times u_m$ 正是此平稳 Markov 链。

证明。逐行求和得到 $A_mR=\phi R$。对于目标 $(t,w)$，每个允许前符号 $s$ 恰有一个前余数 $z=Mw+s\alpha$，所以逐列求和给

$$
(L^{\mathsf T}A_m)_{(t,w)}
=\sum_s A_{st}r_s=\phi r_t.
$$

这里使用二态矩阵 $A$ 的对称性，并不要求余数图本身对称。加权最大范数 $\|f\|_R=\max_v|f_v|/R_v$ 下，$\|A_mf\|_R\le\phi\|f\|_R$，所以谱半径不超过 $\phi$；已有特征值使其等于 $\phi$。由定理 7.3，图原始。这些是该图的正 Perron–Frobenius 数据。

$Q_m$ 每行和为一，每条允许边的概率恰为 $P_{st}$。归一化的 $L_vR_v$ 为 $\pi_s/m^2$；也可逐列直接检查

$$
\sum_{s:A_{st}=1}\frac{\pi_s}{m^2}P_{st}
=\frac{\pi_t}{m^2}.
$$

在 $\nu\times u_m$ 下，一段合法顶点路径的概率为

$$
\frac1{m^2}\pi_{s_0}\prod_{j=0}^{k-2}P_{s_js_{j+1}},
$$

因为该路径恰规定符号块和一个初始余数。这正是初始分布 $\Pi_m$ 与转移 $Q_m$ 的柱公式，证明所述 Markov 性。$\square$

相应条件逆核也由平稳流给出：

$$
\Pr\bigl((s,Mw+s\alpha)\mid(t,w)\bigr)
=\frac{\pi_sP_{st}}{\pi_t}
=\frac{A_{st}r_s}{\phi r_t}.
$$

完整后继 $(\eta,w)\in K$ 下，同一公式给出 $\lambda$ 的条件前像分布：$\eta_0=0$ 时，$h_0,h_1$ 两个前像的权重分别为 $\phi^{-1},\phi^{-2}$；$\eta_0=1$ 时只有 $h_0$，权重一。为验证它，可先对有限后继符号柱和模余数柱应用上述平稳流公式；符号 Markov 性使再给定后继的其余有限符号不改变前位权重，Haar 仿射不变性使任意后继模余数不改变权重。这些柱生成 Borel 代数，故公式确定完整后继的一个正则条件分布版本。此逆核只针对 $\lambda$，并非将两个前像均分，也不针对任意其他不变测度。

**引理 9.4（有限原始链的收敛与混合）。** 对每个固定 $m$，

$$
Q_m^n(v,w)\longrightarrow\Pi_m(w)
$$

对所有顶点成立。该平稳路径系统强混合。

证明。定理 7.3 及每条边的正转移概率保证某个 $N$ 下 $Q_m^N$ 的所有元素正。设顶点数为 $v$，$a=\min_{i,j}Q_m^N(i,j)>0$，$\varepsilon=va\le1$。若 $\varepsilon<1$，每行都能写为

$$
Q_m^N(i,\cdot)=\varepsilon u+(1-\varepsilon)B(i,\cdot),
$$

其中 $u$ 是全部顶点上的均匀概率，$B$ 是随机矩阵。任意两行概率分布的 $\ell^1$ 距离在右乘随机矩阵时不增加，故右乘 $Q_m^N$ 时缩小至少为原来的 $1-\varepsilon$。利用已知平稳分布 $\Pi_m$，得到

$$
\|\zeta Q_m^{kN}-\Pi_m\|_1
\le(1-\varepsilon)^k\|\zeta-\Pi_m\|_1.
$$

余下少于 $N$ 步仍不增加距离，遂得到全部幂收敛。若 $\varepsilon=1$，所有行本来就是 $u$，同样直接成立。此论证同时证明平稳分布唯一。

对于分别依赖顶点 $0,\ldots,a$ 和 $0,\ldots,b$ 的两个柱函数，将第二个函数平移 $n>a$ 步，其联合积分是有限求和：中间连接权重为 $Q_m^{n-a}(v_a,w_0)$，其余权重来自两个固定块。将中间权重取极限 $\Pi_m(w_0)$，有限和分解为两积分的乘积。因此柱函数混合。柱函数的线性张成在路径空间的 $L^2$ 中稠密；保测性与 Cauchy–Schwarz 不等式给对任意 $L^2$ 函数的延伸，故强混合。$\square$

**定理 9.5（完整联合系统的强混合）。** 对任意 $f,g\in L^2(K,\lambda)$，

$$
\int_K f\,(g\circ\delta^n)\,d\lambda
\longrightarrow\left(\int_Kf\,d\lambda\right)
\left(\int_Kg\,d\lambda\right).
$$

因此 $\lambda$ 遍历。

证明。令 $\mathcal F_r$ 为由完整符号地址和 $z\bmod r!$ 生成的 $\sigma$ 代数。它们递增，并生成 $K$ 的 Borel $\sigma$ 代数。有限前缀—模余数柱函数在 $L^2$ 中稠密：这些柱形成生成代数，而可在测度中由此代数逼近的集合构成包含该代数的 $\sigma$ 代数；再用简单函数逼近即可。

设 $f_r=\mathbb E_\lambda[f\mid\mathcal F_r]$，$g_r=\mathbb E_\lambda[g\mid\mathcal F_r]$。这些条件期望作为正交投影满足 $f_r\to f,g_r\to g$ 于 $L^2$。具体地，若柱函数 $h$ 属于某个 $\mathcal F_R$，则 $r\ge R$ 时该投影固定 $h$，并有 $\|f-f_r\|_2\le2\|f-h\|_2$，由稠密性得到收敛。

固定 $r$ 后，$f_r,g_r$ 是 $K_{r!}$ 的函数，引理 9.4 给混合极限。而保测性使 $\|g\circ\delta^n\|_2=\|g\|_2$，从而

$$
\left|\int f(g\circ\delta^n)-\int f_r(g_r\circ\delta^n)\right|
\le\|f-f_r\|_2\|g\|_2+\|f_r\|_2\|g-g_r\|_2.
$$

右侧与 $n$ 无关。先固定 $r$ 令 $n\to\infty$，再令 $r\to\infty$，证明完整系统的混合。若集合 $B$ 满足 $\delta^{-1}B=B$ 模零，则混合给 $\lambda(B)=\lambda(B)^2$，所以其测度为零或一，即遍历。论证只用非可逆保测映射的 $L^2$ 等距性。$\square$

**定义 9.6（可测分割熵）。** 对有限可测分割 $\mathcal Q$，以 $0\log0=0$ 定义

$$
H_\rho(\mathcal Q)=-\sum_{C\in\mathcal Q}\rho(C)\log\rho(C),\qquad
\mathcal Q^{(n)}=\bigvee_{j=0}^{n-1}T^{-j}\mathcal Q,
$$

$$
h_\rho(T,\mathcal Q)=\lim_{n\to\infty}\frac1nH_\rho(\mathcal Q^{(n)}),
\qquad h_\rho(T)=\sup_{\mathcal Q}h_\rho(T,\mathcal Q),
$$

其中 $T$ 为 $\rho$ 保测映射。极限存在，因为联合熵的链式法则与保测性给
$H_\rho(\mathcal Q^{(n+k)})\le H_\rho(\mathcal Q^{(n)})+H_\rho(\mathcal Q^{(k)})$，子可加序列的单位长度极限等于其下确界。条件熵为
$H_\rho(\mathcal Q\mid\mathcal R)=H_\rho(\mathcal Q\vee\mathcal R)-H_\rho(\mathcal R)$。

**引理 9.7（非可逆生成分割的不等式与逼近）。** 对任何保测映射 $T$ 和有限分割 $\mathcal Q,\mathcal R$，

$$
h_\rho(T,\mathcal Q)
\le h_\rho(T,\mathcal R)+H_\rho(\mathcal Q\mid\mathcal R).
$$

若有限分割 $\mathcal R_r$ 递增且生成全部可测集模零，则对每个有限 $\mathcal Q$，
$H_\rho(\mathcal Q\mid\mathcal R_r)\to0$。有限时间联合不改变熵率：

$$
h_\rho\left(T,\bigvee_{j=0}^{r-1}T^{-j}\mathcal P\right)
=h_\rho(T,\mathcal P).
$$

以上不要求 $T$ 可逆。

证明。链式法则与“增加条件不增大条件熵”给

$$
\begin{aligned}
H_\rho(\mathcal Q^{(n)})
&\le H_\rho(\mathcal R^{(n)})
  +H_\rho(\mathcal Q^{(n)}\mid\mathcal R^{(n)})\\
&\le H_\rho(\mathcal R^{(n)})
  +\sum_{j=0}^{n-1}H_\rho(T^{-j}\mathcal Q\mid T^{-j}\mathcal R)\\
&=H_\rho(\mathcal R^{(n)})+nH_\rho(\mathcal Q\mid\mathcal R).
\end{aligned}
$$

最后一步是联合分布在保测逆像下不变，并未使用反向动力学。除以 $n$ 取极限，得到第一式。

对于逼近，$\bigcup_r\sigma(\mathcal R_r)$ 为代数。能够在测度中由此代数任意逼近的集合，对补与有限并封闭，也对可数并封闭：先截取有限并控制测度尾差，再逼近该有限并。因此这类集合包含其生成的 $\sigma$ 代数。设 $\mathcal Q$ 有 $k$ 个原子，可用足够大的某个 $\mathcal R_r$ 的原子构造一个预测标签 $\widehat X_r$，使真实标签 $X$ 的误判概率 $e_r\to0$。令误判指示为 $E_r$，由于 $\widehat X_r$ 是 $\mathcal R_r$ 可测，链式法则给

$$
H_\rho(X\mid\mathcal R_r)
\le H_\rho(E_r)+e_r\log k
=-e_r\log e_r-(1-e_r)\log(1-e_r)+e_r\log k\longrightarrow0.
$$

递增性保证以后分割的条件熵更小，故整个序列趋零。

最后，对 $\mathcal R=\bigvee_{j<r}T^{-j}\mathcal P$，其 $n$ 步联合恰是 $\mathcal P$ 的 $n+r-1$ 步联合。固定 $r$ 时把该熵除以 $n$，极限与 $\mathcal P$ 的熵率相同。$\square$

**定理 9.8（所有不变测度的精确熵桥梁）。** 设 $\rho$ 是任意 $\delta$ 不变 Borel 概率，$\eta$ 为其符号边缘。则

$$
h_\rho(\delta)=h_\eta(\sigma).
$$

同样，任意 $\delta_m$ 不变概率的熵等于其符号边缘的熵。

证明。符号边缘不变，因为符号投影与 $\delta,\sigma$ 交换。记首位分割为 $\mathcal S$，联合首位—模数分割为 $\mathcal P_m=\mathcal P_{1,m}$。在 $\Omega$ 上，$\bigvee_{j<r}\sigma^{-j}\mathcal S$ 递增生成 Borel 集；引理 9.7 的逼近与有限联合不变性证明

$$
h_\eta(\sigma)=h_\eta(\sigma,\mathcal S)
=\lim_{n\to\infty}\frac1nH_\eta(\omega_0,\ldots,\omega_{n-1}).
$$

这里也没有调用可逆生成元定理。

命题 8.2 的名字对应不仅适用于计数，还给出对任意 $\rho$ 的信息恒等：$\mathcal P_m^{(n)}$ 的标签等价于
$(\omega_0,\ldots,\omega_{n-1},z\bmod m)$。条件熵至多 $2\log m$，所以

$$
H_\eta(\omega_0,\ldots,\omega_{n-1})
\le H_\rho(\mathcal P_m^{(n)})
\le H_\eta(\omega_0,\ldots,\omega_{n-1})+2\log m.
$$

固定 $m$，除以 $n$ 得 $h_\rho(\delta,\mathcal P_m)=h_\eta(\sigma)$。

现在取

$$
\mathcal R_r=\bigvee_{j=0}^{r-1}\delta^{-j}\mathcal P_{r!}.
$$

它们递增，标签准确包含前 $r$ 位和模 $r!$ 的初始余数，故生成 $K$ 的全部 Borel 集。对任意有限可测分割 $\mathcal Q$，引理 9.7 给

$$
\begin{aligned}
h_\rho(\delta,\mathcal Q)
&\le h_\rho(\delta,\mathcal R_r)+H_\rho(\mathcal Q\mid\mathcal R_r)\\
&=h_\rho(\delta,\mathcal P_{r!})+H_\rho(\mathcal Q\mid\mathcal R_r)\\
&=h_\eta(\sigma)+H_\rho(\mathcal Q\mid\mathcal R_r).
\end{aligned}
$$

令 $r\to\infty$，再对 $\mathcal Q$ 取上确界，得到 $h_\rho(\delta)\le h_\eta(\sigma)$。反向不等式由任意固定 $\mathcal P_m$ 的熵率已经给出。

在 $K_m$ 上，用固定 $\mathcal P_m$ 的越来越长时间联合代替阶乘塔，同样递增生成全部 Borel 集，证明同一等式。无限 profinite 纤维没有被视为有限集合；只有每个固定模数的额外块熵有界。$\square$

**引理 9.9（有限图的熵等号强制 Markov 性）。** 对任意 $m\ge1$，$\mathscr G_m$ 的任意平稳单边路径测度的熵不超过 $\log\phi$；达到 $\log\phi$ 的唯一测度是命题 9.3 的平稳 Markov 测度。

证明。设顶点过程为 $(V_j)_{j\ge0}$。其有限字母分割和全部未来逆像生成路径 Borel 集。由引理 9.7，其系统熵等于块熵率。令

$$
c_j=H(V_j\mid V_0,\ldots,V_{j-1}),\qquad j\ge1.
$$

平稳性及条件熵单调性给

$$
c_{j+1}\le H(V_{j+1}\mid V_1,\ldots,V_j)=c_j.
$$

块熵为 $H(V_0)+\sum_{j=1}^{n-1}c_j$，所以熵率 $h=\lim_jc_j\le c_1$。

设 $\zeta_v=\Pr(V_0=v)$，在 $\zeta_v>0$ 的顶点上令实际一步条件转移为 $p_v(w)$。路径合法使它只支持允许边，而 $Q_m(v,w)>0$ 在所有这些边成立。由 $Q_m$ 的正向量公式及平稳性，

$$
\begin{aligned}
\mathbb E[-\log Q_m(V_0,V_1)]
&=\log\phi+\mathbb E[\log R_{V_0}-\log R_{V_1}]\\
&=\log\phi.
\end{aligned}
$$

因而

$$
H(V_1\mid V_0)
=\log\phi-\sum_{v:\zeta_v>0}\zeta_v
D(p_v\Vert Q_m(v,\cdot))
\le\log\phi.
$$

这里 $D(p\Vert q)=\sum_wp(w)\log(p(w)/q(w))\ge0$，且等号当且仅当 $p=q$。非负性可由 $-\log t\ge1-t$ 应用于 $t=q(w)/p(w)$ 后求和得到；等号要求各正概率位置比值一，并且不存在剩余 $q$ 质量。因此 $h\le c_1\le\log\phi$。

若 $h=\log\phi$，两个不等式都取等。KL 等号先迫所有 $\zeta_v>0$ 的实际转移为 $Q_m$。于是平稳顶点分布满足 $\zeta Q_m=\zeta$，零概率顶点不贡献额外项。引理 9.4 的唯一平稳性迫 $\zeta=\Pi_m$，特别地全部顶点概率正。

此外 $c_j$ 递减而极限已经等于 $c_1$，所以每个 $c_j=c_1$。平稳性又有 $H(V_j\mid V_{j-1})=c_1$，因此对每个 $j$，

$$
H(V_j\mid V_{j-1})-
H(V_j\mid V_0,\ldots,V_{j-1})=0.
$$

该差是各有限历史条件分布相对仅给当前顶点的条件分布的平均 KL 散度。等号迫每个正概率历史上的下一顶点分布只依赖最后顶点，且等于 $Q_m$。这对所有有限历史成立，链式概率公式遂给全部块概率

$$
\Pr(V_0=v_0,\ldots,V_{k-1}=v_{k-1})
=\Pi_m(v_0)\prod_{j=0}^{k-2}Q_m(v_j,v_{j+1}).
$$

所以路径过程是一阶 Markov，测度唯一。反之，这个平稳 Markov 测度的条件转移就是 $Q_m$，其块熵率为
$\mathbb E[-\log Q_m(V_0,V_1)]=\log\phi$，确实取等。$\square$

**定理 9.10（唯一最大熵测度与唯一 Parry 提升）。** $\lambda=\nu\times\mu$ 是 $(K,\delta)$ 的唯一最大熵不变 Borel 概率，其熵为 $\log\phi$。更具体地，任何符号边缘为 $\nu$ 的 $\delta$ 不变概率都等于 $\lambda$。

证明。引理 9.9 在 $m=1$ 时给黄金均值符号系统的唯一最大熵测度恰为 $\nu$，熵为 $\log\phi$。命题 9.2 给 $\lambda$ 不变，定理 9.8 给 $h_\lambda(\delta)=h_\nu(\sigma)=\log\phi$，与定理 8.3 的拓扑熵相同。对任意不变 $\rho$，定理 9.8 与 $m=1$ 的熵上界给 $h_\rho(\delta)\le\log\phi$，故 $\lambda$ 达到所有不变概率的最大熵。

若 $\rho$ 的符号边缘为 $\nu$，则每个模数投影 $\rho_m$ 都是 $\delta_m$ 不变提升，并由定理 9.8 有熵 $\log\phi$。引理 9.9 强制 $\rho_m=\nu\times u_m$ 对所有 $m$ 成立。这些投影确定每个有限前缀—模余数柱的概率，而这些柱生成 Borel 集，所以 $\rho=\nu\times\mu$。

若 $\rho$ 为任意最大熵测度，定理 9.8 先使其符号边缘的熵为 $\log\phi$，$m=1$ 的唯一性迫边缘为 $\nu$，再由上段唯一提升得到 $\rho=\lambda$。证明次序先建立所有不变测度的熵桥梁，再使用熵等号，未用待证的唯一性作为前提。$\square$

固定点 $p_0$ 上的 Dirac 概率与二周期 $\{p_1,p_2\}$ 上的均匀概率仍是其他不变概率；其有限块熵有界，故熵为零。因而唯一性准确限定于最大熵和 Parry 边缘的不变提升。定理 9.5 的强混合只涉及正常载体上的 $\lambda$；有限链收敛的常数可以依赖模数，本卷不提出跨全部模数的统一混合速率。

## 10. 数学参考文献

[1] [《FIBONACCI_ATOMIC_RELATION_GENERATION》](FIBONACCI_ATOMIC_RELATION_GENERATION.md)，命题 161.1、推论 161.2、命题 182.1。分别使用固定前缀的标量数量模满像及连续解码障碍、正数量单位零来源的开条带识别。二维共同实现、完成动力学和测度结论由本卷的证明给出。

[2] J.-P. Gazeau and J.-L. Verger-Gaugry, “Diffraction spectra of weighted Delone sets on beta-lattices with beta a quadratic unitary Pisot number,” *Annales de l’Institut Fourier* **56** (7) (2006), 2437–2461. [DOI: 10.5802/aif.2245](https://doi.org/10.5802/aif.2245)。黄金基属于 Case (i)；Proposition 3.1／式 (3.2)，第 2444 页，及式 (3.11)，第 2445 页，是约定 1.3 的经典非负黄金基整数条带。该文的正半轴与共轭坐标条件不替代母卷的正整数数量条件。

[3] Č. Burdík, C. Frougny, J.-P. Gazeau and R. Krejčar, “Beta-integers as natural counting systems for quasicrystals,” *Journal of Physics A: Mathematical and General* **31** (1998), 6449–6472. [DOI: 10.1088/0305-4470/31/30/011](https://doi.org/10.1088/0305-4470/31/30/011)。黄金基正半轴条带的原始出处为 Lemma 4.1(ii)、式 (30)；[2] 的 Proposition 3.1 明确以其参考文献 [8] 归属该结果。本卷采用 [2] 所列精确条带及 [1] 的实际来源识别。

[4] W. Parry, “Intrinsic Markov chains,” *Transactions of the American Mathematical Society* **112** (1964), 55–66. [DOI: 10.1090/S0002-9947-1964-0161372-1](https://doi.org/10.1090/S0002-9947-1964-0161372-1)。使用其经典正特征向量 Markov 构造的数学归属；本卷所需的有限图转移、平稳分布、混合和最大熵唯一性均在第 9 节证明。

## 追加锚（本行以下为增补区）

## 11. 前缀剥离的精确纤维、恢复记录与条件信息方向

**约定 11.1（已知剥离长度与恢复对象）。** 沿用 $D,\Omega,G,K,\Gamma,M,\alpha,t_u,h_u,\delta$；单位位固定为零，零来源包含在内，高位补零视为同一来源，没有独立长度或 End 观察。剥离长度 $k\ge0$ 已知，删除最低的 $k$ 位后将尾重新从低位编号。对 $p=(\omega,z_{\rm in})$，记

$$
U=\omega|_k,\qquad
Y=\delta^kp=(\eta,z_{\rm out}),\qquad b=\eta_0,
$$

$$
\mathcal C_k(b)=\{u\in\{0,1\}^k:
 u_ju_{j+1}=0\ (0\le j<k-1),\quad
 k=0\text{ 或 }u_{k-1}b=0\}.
$$

空词记为 $\varepsilon$，$\mathcal C_0(b)=\{\varepsilon\}$。恢复对象是原来的完整联合点 $p$；在实际域上它等价于恢复原有限来源。全部信息量用 $\log_2$，第 8、9 节的自然对数熵换成位时除以 $\log2$。

以下复用命题 5.2 的前缀逆和命题 9.3 的条件逆核。约束词的 Fibonacci 计数、有限纤维编码的鸽巢原理、条件 Shannon 熵及 Parry 的内禀 Markov 律是经典工具；Parry 归属见第 10 节 [4]。三位窗口记法与低到高方向沿用[母卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md)定义 104.2。

**定理 11.2（完整尾的全部前像与准确数量）。** 对任意 $y=(\eta,z)\in K$，映射

$$
u\longmapsto h_u(y)=(u\eta,t_u+M^kz)
$$

给出 $\mathcal C_k(b)$ 到 $(\delta^k)^{-1}\{y\}$ 的双射，其中 $b=\eta_0$。若 $y\in\Gamma$，这些前像全部属于 $\Gamma$，且是实际域中的全部前像；若 $y\notin\Gamma$，实际域没有前像。纤维数量为

$$
N_k(b)=|\mathcal C_k(b)|=
\begin{cases}
F_{k+2},&b=0,\\
F_{k+1},&b=1,
\end{cases}
\qquad N_0(0)=N_0(1)=1.
$$

证明。命题 5.2 使每个相容前缀 $u$ 满足 $\delta^kh_u(y)=y$；不同 $u$ 给不同地址。反之，任意前像的地址必是 $u\eta$，接缝要求 $u\in\mathcal C_k(b)$，同一迭代公式迫算术坐标等于 $t_u+M^kz$，没有第二个自由的算术选择。

若 $y=(\eta,\iota(x(\eta)))\in\Gamma$，则 $\eta$ 最终为零，$u\eta$ 也最终为零，且

$$
x(u\eta)=t_u+M^kx(\eta).
$$

所以同一个前缀与尾同时实现地址和组成。反向剥离保持实际性，故实际前像的输出必在 $\Gamma$。这也给出纯符号域 $\Omega$、$D$ 上的相同前缀双射。

准确计数可直接复用命题 8.2：$b=0$ 时所有合法长度 $k$ 词都允许；$b=1,k\ge1$ 时最后一位必须为零，删除这位后恰剩任意合法长度 $k-1$ 词。后者也可把低到高词反转，将末位零条件变成首位零条件，再使用同一基础计数。为包含 $k=0$，按末位 $s$ 反向延长，有

$$
N_{k+1}(0)=N_k(0)+N_k(1),\qquad
N_{k+1}(1)=N_k(0),\qquad (N_0(0),N_0(1))=(1,1).
$$

Fibonacci 递推立即给所述公式。$\square$

**推论 11.3（三位逆分支与多窗历史）。** 对固定完整尾，删除一个低窗口的相容前缀恰为

$$
\begin{aligned}
\mathcal C_3(0)&=\{000,100,010,101,001\},\\
\mathcal C_3(1)&=\{000,100,010\}.
\end{aligned}
$$

其局部标签 $q(t_u)$ 分别为 $0,2,3,7,5$ 和 $0,2,3$，其中零标签记作 $\mathsf{null}$。删除 $L\ge0$ 个低窗口时，同一完整尾的前像数分别为

$$
N_{3L}(0)=F_{3L+2},\qquad N_{3L}(1)=F_{3L+1}.
$$

特别地，两窗为 $21$ 或 $13$，不按 $5^2=25$ 计。

证明。三位内部禁止相邻一，反向接缝禁止 $u_2=b=1$，逐项即得到上述两个集合；数值标签由 $q(\alpha)=2,q(M\alpha)=3,q(M^2\alpha)=5$ 得到。这里条件是保留尾的首位 $b$。正向读取窗口时的入接缝 $s$ 却限制 $su_0=0$；$s=1$ 的允许词为 $000,010,001$，标签为 $\mathsf{null},3,5$，不能代替反向的 $\mathsf{null},2,3$。

多窗公式取定理 11.2 的 $k=3L$。相邻窗口仍共享 no-11 接缝约束，每个允许的全前缀恰决定一条剥离历史。因此五种局部标签不能按独立选择相乘；两窗数由 $F_8=21,F_7=13$ 给出。$\square$

**定义 11.4（精确恢复的残余记录）。** 固定 $X=K$ 或 $X=\Gamma$。残余字母表为有限集 $\mathcal E$，编码器 $e:X\to\mathcal E$，解码器 $d$ 在实际可取得的记录对上满足

$$
d(\delta^kp,e(p))=p\qquad(p\in X).
$$

$k$ 和输出 $Y$ 是解码器的已知输入。除此以外，凡随被删前缀而变化、并被保留下来的有限元数据，都计入 $e$，包括以状态或码长携带的区别。字母表容量讨论的是精确恢复每个来源，概率零的分支也不能省去。

**定理 11.5（最小恢复字母表与达到构造）。** 定义 11.4 的记录充分，当且仅当 $e$ 在每个 $\delta^k$ 纤维上单射。最小统一字母表大小为 $F_{k+2}$；仅考虑输出尾首位为给定 $b$ 的来源时，最小字母表大小为 $N_k(b)$。最小固定二进制位数分别为

$$
\left\lceil\log_2F_{k+2}\right\rceil,\qquad
\left\lceil\log_2N_k(b)\right\rceil.
$$

$k=0$ 时可以用空记录。若 $k$ 无上界，虽逐次已知 $k$，也不存在大小统一有界的有限总记录字母表，能恢复全部来源。

证明。若同一纤维内 $p\ne p'$ 而 $e(p)=e(p')$，解码器收到相同记录对，不能同时返回两个原点；故必须纤维内单射。反之，单射使每个可取得的 $(y,a)$ 对应唯一原点，取该点即定义解码器。这里只要求在编码像上解码，不要求解释未使用的记录对。

定理 11.2 给 $b=0$ 的纤维大小 $F_{k+2}$、$b=1$ 的纤维大小 $F_{k+1}$。两种尾在实际域都存在，例如 $0^\infty$ 和 $10^\infty$ 配各自组成；鸽巢原理给两个下界。

达到下界的编码如下：以 $0<1$、按 $u_0,u_1,\ldots$ 的字典序排列 $\mathcal C_k(b)$，记从零开始的秩为 $\operatorname{rank}_{k,b}(u)$，取

$$
\mathcal E=\{0,\ldots,F_{k+2}-1\},\qquad
e(p)=\operatorname{rank}_{k,\eta_0}(\omega|_k).
$$

解码器从 $y=(\eta,z)$ 取得 $b=\eta_0$，按秩找出唯一 $u\in\mathcal C_k(b)$，返回 $h_u(y)$。定理 11.2 保证精确恢复，实际输出还保证恢复点实际。固定 $b$ 时将字母表缩为 $\{0,\ldots,N_k(b)-1\}$ 即达到条件下界。$m$ 个固定比特只能表示 $2^m$ 个值，反过来可把上述秩写成相应长度的二进制串，遂得两个取整式。

$k=0$ 只有空前缀，解码器直接返回 $y$。若存在固定大小 $B$ 的总字母表适用于所有 $k$，取 $k$ 使 $F_{k+2}>B$，并固定输出为零来源，则该纤维已有多于 $B$ 个实际前像，矛盾。已知 $k$ 不能区分同一个 $k$ 的这些前像。$\square$

若另有免费元数据 $m(p)$，同一论证把新增记录的统一下界与达到值改为 $\max_{y,a}|\{p:\delta^kp=y,\ m(p)=a\}|$，因此改变免费信息合同会改变界。若采用变长码，需连同码长和定界规则计算记录，平均码长还取决于概率律。秩构造达到的是整块记录容量；它不证明编码、解码或流式更新所需的总内存最优，也不计尾的存储成本。

**定理 11.6（Parry–Haar 律下给定完整未来的前缀分布）。** 令输入联合点按定义 9.1 的 $\lambda=\nu\times\mu$ 分布。仅在此概率律下，对 $k>0$，给定完整输出 $Y=(\eta,z)$ 的一个正则条件分布版本为

$$
\Pr_\lambda(U=u\mid Y=(\eta,z))=
\begin{cases}
\displaystyle\frac{r_{u_0}}{\phi^k r_b},&u\in\mathcal C_k(b),\\
0,&u\notin\mathcal C_k(b),
\end{cases}
\qquad b=\eta_0,\quad r_0=\phi,\ r_1=1.
$$

相应原点的条件分布把上述质量放在 $h_u(\eta,z)$ 上。$k=0$ 时空前缀的概率为一、原点条件分布为 $Y$ 上的点质量。输出算术坐标 $z_{\rm out}$ 与整个输入符号地址 $\omega$ 独立。

证明。命题 9.3 的一步逆核是 $A_{st}r_s/(\phi r_t)$。将合法前缀与末端首位 $b$ 连起来，逆核的 $k$ 个因子望远镜消去，得到

$$
\prod_{j=0}^{k-1}\frac{A_{u_j u_{j+1}}r_{u_j}}{\phi r_{u_{j+1}}}
=\frac{r_{u_0}}{\phi^k r_b},\qquad u_k=b.
$$

为验证条件确实包含完整符号未来，而非只有首接缝，固定任意合法有限未来柱 $[bv_1\cdots v_n]$。按定义 9.1 的 Markov 柱公式，前缀与此柱的联合概率除以未来柱的概率，未来内部的转移因子全部抵消，余下

$$
\frac{\pi_{u_0}}{\pi_b}
\prod_{j=0}^{k-1}P_{u_j u_{j+1}}
=\frac{r_{u_0}^2}{r_b^2}
\frac{r_b}{\phi^k r_{u_0}}
=\frac{r_{u_0}}{\phi^k r_b}.
$$

非法接缝给零。所有有限未来柱生成完整尾的 Borel 集，柱上的条件积分恒等式因而延伸到全部尾事件。各前缀概率的和为一，既可由上述柱分解得到，也可由 $\pi P^k=\pi$ 验证。

还必须检查联合算术未来。命题 5.2 给

$$
z_{\rm out}=M^{-k}(z_{\rm in}-t_{\omega|_k}).
$$

对每个固定的整个地址 $\omega$，这一仿射映射保持 $\mu$：$M\in\operatorname{GL}_2(\mathbb Z)$ 且 Haar 测度平移不变。因此对任意 Borel 集 $B\subseteq\Omega,C\subseteq G$，

$$
\begin{aligned}
\Pr_\lambda(\omega\in B,z_{\rm out}\in C)
&=\int_B\mu\{v:M^{-k}(v-t_{\omega|_k})\in C\}\,d\nu(\omega)\\
&=\nu(B)\mu(C).
\end{aligned}
$$

所以 $z_{\rm out}$ 与 $(U,\eta)$ 独立，再给定任意完整算术尾事件也不改变前缀权重。将符号柱与算术模柱组合并延伸到其生成的 Borel 集，就验证了所述联合条件分布。有限分支公式是 Borel 核，故给出一个正则条件分布版本；任意条件版本只须 $\lambda$ 几乎处处相同。原点由 $U,Y$ 唯一恢复，得到 $h_u(Y)$ 上的条件质量。输出之后的全部剥离轨道也由 $Y$ 决定，不再另增条件信息。$\square$

三位时，该版本的非零权重明确为

$$
\begin{aligned}
b=0:\quad &p(000)=p(001)=p(010)=\phi^{-3},\\
&p(100)=p(101)=\phi^{-4};\\
b=1:\quad &p(000)=p(010)=\phi^{-2},\qquad p(100)=\phi^{-3}.
\end{aligned}
$$

它们依赖前缀首位及保留尾首位；五个逆分支没有被均分。概率中的地址与组成仍来自同一个输入点，独立性是产品 Haar 律的结论。

**定理 11.7（指定律的平均删除信息）。** 对定理 11.6 的 $U,Y$，以有限随机变量的通常条件 Shannon 熵定义

$$
H_\lambda(U\mid Y)=\int_K
\left[-\sum_u p_k(u\mid y)\log_2 p_k(u\mid y)\right]d\lambda(y),
\qquad 0\log_2 0=0.
$$

则对每个 $k\ge0$，

$$
H_\lambda(U\mid Y)=k\log_2\phi.
$$

证明。$k>0$ 时，对实际抽到的合法前缀，定理 11.6 给

$$
-\log_2 p_k(U\mid Y)
=k\log_2\phi+\log_2r_{\omega_k}-\log_2r_{\omega_0}.
$$

有限和的条件期望再取总期望，左侧就是 $H_\lambda(U\mid Y)$。平稳性使 $\omega_0,\omega_k$ 同有分布 $\pi$，两个边界项期望相消。$k=0$ 时只有空前缀，熵为零。$\square$

$\log_2N_k(b)$ 是给定尾的纤维容量；它是该纤维上所有概率律的最大熵，通常不等于当前条件律的熵。三位剥离的这里平均值是 $3\log_2\phi$，不是普适的 $\log_25$。$H_\lambda(U\mid Y)$ 等于第 9 节每步动力熵换底后的 $k$ 倍；该等式来自已经证明的 Parry 条件律和平稳边界项，不能由熵数值相等反推任意提升的分支律。

逆纤维条件熵与动力熵也没有一般相等定律。例如双边公平二元 Bernoulli 移位可逆，每个完整输出只有一个前像，逆纤维条件熵为零；长度 $n$ 的连续符号块却有熵 $n$ 位。中心块 $[-r,r]$ 的 $n$ 步联合有 $n+2r$ 位，固定 $r$ 后熵率为一，而这些分割递增生成全部可测集，按引理 9.7 的逼近不等式得到动力熵一位每步。这是经典移位的区别，不是热量等式。

**命题 11.8（有限来源上的概率边界）。** $\nu(D)=0$，因而 $\lambda(\Gamma)=0$。对任意另选的实际有限来源概率律 $Q$，固定 $k$ 后仍有

$$
0\le H_Q(U\mid Y)
\le\mathbb E_Q[\log_2N_k(\eta_0)]
\le\log_2F_{k+2}.
$$

这里 $Q$ 可支持于任意多个有限来源，并非要求其支撑本身有限；条件熵仍有限，因为 $U$ 的字母表有限。

证明。令 $E_n=\{\omega:\omega_j=0\text{ 对全部 }j\ge n\}$。平稳 Markov 律给连续 $\ell$ 个零的柱概率为 $\pi_0P_{00}^{\ell-1}=\pi_0\phi^{-(\ell-1)}$，故这些柱递减到 $E_n$ 时概率趋零。于是 $\nu(E_n)=0$；$D=\bigcup_nE_n$ 给 $\nu(D)=0$，而 $\Gamma\subseteq D\times G$ 给联合零测度。

在 $Q$ 下，$Y$ 取值于可数的 $\Gamma$。每个正概率输出的条件前缀分布支持于 $\mathcal C_k(b)$，设其质量为 $a_u$，均匀分布为 $v_u=1/N_k(b)$。经典熵界可直接写成

$$
\log_2N_k(b)-H(a)=\sum_u a_u\log_2\frac{a_u}{v_u}\ge0.
$$

非负性与零质量约定沿用引理 9.9 的相对熵论证。对输出求期望，再用 $N_k(b)\le F_{k+2}$，得到全部不等式。单一来源的点质量使条件熵为零；对零尾的全部 $F_{k+2}$ 个前像取均匀律，使上界 $\log_2F_{k+2}$ 达到。$\square$

因此 Parry–Haar 律不提供有限整数来源上的抽样律，$k\log_2\phi$ 也不自动成为这些来源的平均损失。有限来源集合可数无限，给每个来源相同质量不能形成概率律：正的共同质量使总和发散，零的共同质量使总和为零。另选 $Q$ 后，概率零分支不影响 $H_Q$，却仍参与定义 11.4 的全部来源精确恢复容量。

**命题 11.9（头观察、尾保留与具体碰撞）。** 定义三位头标签

$$
\chi(p)=q(t_{\omega|_3})\in\{0,2,3,5,7\},\qquad 0\equiv\mathsf{null}.
$$

单独 $\chi$ 是五值头观察，不保留尾；$\delta^3$ 保留完整尾而擦除头。兼容的联合记录 $(\chi(p),\delta^3p)$ 在 $K$ 和 $\Gamma$ 上均可逆到原点，逆为找到标签对应的唯一合法三位词 $u$ 后返回 $h_u(Y)$。

实际来源数量 $10=[2,2]$ 与 $11=[3,2]$ 删除最低窗口后都变成数量 $2=[2]$。即使额外同时保留规范窗口数 $2$、被删窗口末位 $0$ 和 End 资格值 $1$，这两个来源仍发生同一碰撞。

证明。五个合法三位词的 $q(t_u)$ 两两不同，标签恰能恢复 $u$。兼容性正是 $u\in\mathcal C_3(\eta_0)$，然后定理 11.2 恢复全部地址及算术坐标；不兼容的头尾对不在记录像中。单独头标签则合并同头的各个合法尾。

具体地，两个来源的地址按低到高分别为 $100\,100\,0^\infty$ 与 $010\,100\,0^\infty$，组成分别为

$$
x_{10}=\alpha+M^3\alpha,\qquad
x_{11}=M\alpha+M^3\alpha.
$$

由命题 1.2，$q(M^3\alpha)=F_6=8$，数量即 $2+8=10$ 与 $3+8=11$。两地址内部和跨窗接缝都合法；命题 5.2 使两联合点在 $\delta^3$ 后同为 $(10^\infty,\iota(\alpha))$。两者最高非零窗口都是第二窗 $100$，故规范窗口数都是二，被删第一窗末位都是零。按母卷定义 104.2，最高窗口非零使两者的 End 资格都为一；这一额外资格值也不能分开它们，并未为本章增加 End 观察。$\square$

**命题 11.10（限定于观察的不可逆与有限容量）。** 定义剥离的观察等价关系

$$
p\sim_kp'\quad\Longleftrightarrow\quad\delta^kp=\delta^kp'.
$$

则 $\sim_k\ \subseteq\ \sim_{k+1}$。充分记录 $e$ 使 $p\mapsto(\delta^kp,e(p))$ 在自身像上可逆；仅保留 $\delta^kp$ 时，精确恢复障碍恰是非单点纤维。有限来源系统无需在每一步严格丢失信息，五种头值也不构成普适观察操作分类。

证明。相同 $k$ 步输出再作一次相同映射，仍有相同 $k+1$ 步输出，给关系的包含；不要求每对来源在每一步都新增合并。带记录的可逆性来自定理 11.5，无记录的恢复则当且仅当纤维单点。命题 11.9 给实际非单点纤维，但 $k=0$ 没有删除，一位删除在尾首位一的纤维也只有一个前像。

对任意有限来源集合 $S\subset\Gamma$，有限状态集直接取 $S$ 就能保留来源身份，恒等变换或置换在每一步都保留它。无界 $k$ 下恢复全部来源所需记录无统一有限上界，是定理 11.5 的全来源、全删除长度量词；它不要求这个固定有限 $S$ 丢弃其有限内容。

五个头值来自长度三的局部合法地址语法；更换长度即得到其他 Fibonacci 数量，且跨窗选择受约束。五值分割没有给出所有观测操作的分类，也没有证明五个独立的盲维度。上述关系包含描述的是删除合同中的信息方向：只有在非单点纤维被合并且恢复数据未保留时，原来源区别才无法由输出重建。这些结论未指定物理能量、热浴、实现过程或时间变量，不能据此推导物理热量或普遍的物理时间箭头，也不能推出一切识别都严格遗忘。$\square$

## 追加锚（本行以下为增补区）

## 12. 有限来源的删位律与保留端点的极限

**约定 12.1（一个有界来源与同一概率律）。** 沿用定义 1.1 的 $D$，对整数 $N\ge0$ 取

$$
D_N=\{\omega\in D:\omega_j=0\text{ 对所有 }j\ge N\},
\qquad |D_N|=F_{N+2}.
$$

$N$ 是给定的来源上界，不是另行抽样的长度；单位位为零，零来源包含在内，高位补零识别，没有独立 End 符号。$D_0=\{0^\infty\}$。在 $D$ 上，$\delta\omega=(\omega_1,\omega_2,\ldots)$；经实际图 $\omega\mapsto(\omega,\iota(x(\omega)))$ 识别，这也是第 3 节的联合剥离，组成没有另一个随机选择。

对一个固定概率律 $Q$，令 $X\sim Q$ 取值于 $D_N$，并定义

$$
Y_k=\delta^kX,\qquad L_k=H_Q(X\mid Y_k)\quad(k\ge0).
$$

始终先抽取同一个 $X$，再推前得到全部 $Y_k$。记 $Q_N$ 为 $D_N$ 上的均匀律，其损失记为 $E_{N,k}$。全部熵与相对熵用 $\log_2$，$0\log_2 0=0$，并记

$$
h_2(t)=-t\log_2t-(1-t)\log_2(1-t),\qquad
D_2(p\Vert q)=\sum_{c=0}^1p_c\log_2\frac{p_c}{q_c}.
$$

以下计数复用定理 11.2，恢复准则复用定理 11.5；$A,P,\pi,\nu$ 沿用定义 9.1，$\mu,\lambda$ 的含义不变。约束词计数、Shannon 链式法则、Markov 桥及 Perron–Frobenius 分解是所用的经典方法，Parry 构造的出处见第 10 节 [4]。

**命题 12.2（有限来源的商与恢复容量）。** 将核定义为等值关系

$$
\ker_N\delta^k=\{(\omega,\omega')\in D_N^2:
\delta^k\omega=\delta^k\omega'\},
$$

而非某个代数运算的核。对 $0\le k\le N$，$\delta^k:D_N\to D_{N-k}$ 满射，商的等价类数为 $F_{N-k+2}$。保留尾首位为 $b$ 的类大小为 $F_{k+2-b}$；$k=N$ 时只有零尾，只有大小 $F_{N+2}$ 的一个类。此外，

$$
\ker_N\delta^k\subsetneq\ker_N\delta^{k+1}\quad(0\le k<N),
\qquad \ker_N\delta^k=D_N^2\quad(k\ge N).
$$

若解码器已知 $k$ 和 $Y_k$，要求精确恢复每个 $D_N$ 来源，则最小统一残余字母表大小及固定比特数分别为

$$
F_{\min(k,N)+2},\qquad
\left\lceil\log_2F_{\min(k,N)+2}\right\rceil.
$$

证明。任意 $\eta\in D_{N-k}$ 都可前置 $k$ 个零得到 $D_N$ 中的前像，故满射；命题 8.2 的词数给商的类数。定理 11.2 的相容前缀与纤维双射在此恰落于 $D_N$，给类大小。空尾以首位零处理，不引入第二个尾。

关系的包含来自 $\delta^{k+1}=\delta\circ\delta^k$。令 $e_k$ 仅在第 $k$ 位为一。对 $k<N$，$0,e_k\in D_N$，在 $k$ 步后分别为零和 $e_0$，在 $k+1$ 步后却都为零，证明严格包含。$N$ 步后全部来源为零，遂稳定。

对 $k\le N$，最大纤维是零尾的纤维，大小 $F_{k+2}$；对 $k\ge N$，唯一纤维为整个 $D_N$。定理 11.5 的纤维内单射准则与秩编码分别给下界和达到值，固定比特数随之得到。商的类数计算有多少种输出，残余字母表计算同一输出中还需分开多少个来源，两者不能互换。$\square$

**命题 12.3（同一来源律的损失与准确严格性）。** 对约定 12.1 的任意 $Q$，

$$
L_0=0,\qquad L_k=H_Q(X)\ (k\ge N),\qquad
L_{k+1}-L_k=H_Q(Y_k\mid Y_{k+1})\in[0,1].
$$

增量严格为正，当且仅当存在某个后继 $y$，其两个不同一步前驱 $z,z'$ 同时满足

$$
\delta z=\delta z'=y,\qquad
\Pr(Y_k=z)>0,\quad\Pr(Y_k=z')>0.
$$

若 $Q$ 在 $D_N$ 上满支撑，则每个 $k<N$ 的增量严格为正。点质量的全部损失为零；若 $0\le j<N$ 且 $X$ 在 $\{0,e_j\}$ 上均匀，则

$$
L_k=\begin{cases}0,&k\le j,\\1,&k\ge j+1.\end{cases}
$$

证明。$Y_k$ 是 $X$ 的函数，$Y_{k+1}$ 又是 $Y_k$ 的函数，故链式法则给

$$
L_k=H_Q(X)-H_Q(Y_k),\qquad
H_Q(Y_k)-H_Q(Y_{k+1})=H_Q(Y_k\mid Y_{k+1}).
$$

一步纤维至多有两个来源，故每个正概率后继的条件熵至多一位。有限分布的熵为零恰当其为点质量，因此平均条件熵为正恰当某个正概率后继含两个正概率前驱。满支撑时，零来源与 $e_k$ 在第 $k$ 步给这两个前驱。端点由 $Y_0=X$、$Y_N=0$ 得到。点质量没有概率区别；在两点例中，$Y_k$ 在 $k\le j$ 时仍区分原来的两点，在 $j+1$ 步时首次合并，给所述唯一一次一位损失。$\square$

**推论 12.4（均匀有限来源的准确删位熵）。** 取 $X\sim Q_N$，$0\le k\le N$，记

$$
L=N-k,\qquad Z=F_{N+2},\qquad
 a=F_{k+2},\qquad b=F_{k+1}.
$$

则

$$
E_{N,k}=
\frac{aF_{L+1}\log_2a+bF_L\log_2b}{Z}.
$$

对 $0\le k<N$，准确增量为

$$
E_{N,k+1}-E_{N,k}
=\frac{F_{k+3}F_{N-k}}{F_{N+2}}
 h_2\!\left(\frac{F_{k+1}}{F_{k+3}}\right)>0.
$$

端点为 $E_{N,0}=0$、$E_{N,N}=\log_2F_{N+2}$，以后保持该值；$N=0$ 时全部损失为零。

证明。给定保留尾 $\eta$，$Q_N$ 在其纤维上条件均匀。首位零、首位一的尾分别有 $a,b$ 个前像，故每个这样的尾概率分别为 $a/Z,b/Z$，条件熵分别为 $\log_2a,\log_2b$。长度 $L\ge1$ 的尾中，两种首位分别有 $F_{L+1},F_L$ 个：首位零后余下任意合法长度 $L-1$ 词，首位一则受下一位零的约束。$L=1$ 的两种尾各有一个。$L=0$ 时只取零尾，两种数量按 $F_1=1,F_0=0$ 解释。按尾求平均即给第一式；它还给出计数恒等式 $aF_{L+1}+bF_L=Z$。

对增量，按 $Y_{k+1}$ 分组。首位一的后继只有前驱 $0Y_{k+1}$，条件熵为零。首位零的每个后继有前驱 $0Y_{k+1}$、$1Y_{k+1}$，在 $Y_k$ 律中的质量分别为 $a/Z,b/Z$。合计为 $F_{k+3}/Z$，条件分裂为 $a/F_{k+3},b/F_{k+3}$。这样的后继有 $F_{N-k}$ 个，包括 $k=N-1$ 时唯一的零尾。命题 12.3 因而给准确增量，两个分支质量均正。$k=0$ 时 $a=b=1$，$k=N$ 时只剩大小 $Z$ 的零尾纤维，故端点成立；$N=0$ 时 $Z=1$。

例如 $D_2$ 的三个来源词为 $00,10,01$。删去一位后，尾 $0,1$ 的概率为 $2/3,1/3$，不是 $D_1$ 上的均匀概率 $1/2,1/2$。相应 $E_{2,1}=2/3$ 位；若每步另抽一个均匀尾，就已经改变了来源律，不能代入同一历史的损失增量。$\square$

**命题 12.5（固定左端的单边极限）。** 固定 $k\ge0$，在 $N\to\infty$ 时，$Q_N$ 下 $Y_k$ 首位的分布趋于

$$
p_k=\left(\frac{F_{k+2}}{\phi^{k+1}},
           \frac{F_{k+1}}{\phi^{k+2}}\right).
$$

全部固定长度前缀的极限确定 $\Omega$ 上的概率律 $\nu_{\rm left}$：若合法词 $w$ 长度为 $\ell\ge1$，末位为 $c$，则

$$
\nu_{\rm left}([w])=\phi^{-(\ell+c)}.
$$

此律的初始分布为 $p_0=(\phi^{-1},\phi^{-2})$，转移矩阵是定义 9.1 的 $P$，且 $p_k=p_0P^k$；它不是平稳律 $\nu$。

证明。推论 12.4 给 $N>k$ 时两种首位的概率为

$$
\left(\frac{F_{k+2}F_{N-k+1}}{F_{N+2}},
      \frac{F_{k+1}F_{N-k}}{F_{N+2}}\right).
$$

Binet 公式 $F_n=(\phi^n-(-\phi^{-1})^n)/\sqrt5$ 给所述极限。固定前缀 $w$ 后的延长数，由末位 $c$ 决定，恰为 $F_{N-\ell+2-c}$，所以柱概率趋于 $\phi^{-(\ell+c)}$。

长度一时得到 $p_0$。若已有前缀末位 $c$，添上允许位 $d$，两个极限柱概率之比为 $\phi^{-1+c-d}$；乘上合法性因子 $A_{cd}$，正是

$$
P_{cd}=\frac{A_{cd}h_d}{\phi h_c},\qquad
(h_0,h_1)=(\phi,1).
$$

这里 $h$ 是定义 9.1 的同一个正特征向量。每行转移和为一，因而这些柱概率一致，并定义所述 Markov 律。其第 $k$ 位分布是 $p_0P^k$，与前面的极限相同。$p_{0,1}=\phi^{-2}\ne1/(\phi^2+1)=\pi_1$，故初始分布并非平稳分布。这是无限地址上的柱极限，不是全体有限整数来源上的均匀概率。$\square$

**推论 12.6（左端删位熵及不消失的绝对修正）。** 对固定 $k\ge0$，

$$
\begin{aligned}
E_k^{\rm left}:=\lim_{N\to\infty}E_{N,k}
 &=p_{k,0}\log_2F_{k+2}+p_{k,1}\log_2F_{k+1}\\
 &=k\log_2\phi+D_2(p_k\Vert p_0).
\end{aligned}
$$

它也等于 $H_{\nu_{\rm left}}(\omega|_k\mid\sigma^k\omega)$。$k=0$ 时两项均零；对每个 $k>0$，$D_2(p_k\Vert p_0)>0$。进一步，

$$
p_k\longrightarrow\pi=\frac{(\phi^2,1)}{\phi^2+1},\qquad
D_2(p_k\Vert p_0)\longrightarrow D_2(\pi\Vert p_0)>0,
$$

$$
\frac{D_2(p_k\Vert p_0)}k\longrightarrow0,
\qquad \frac{E_k^{\rm left}}k\longrightarrow\log_2\phi.
$$

证明。固定 $k$ 时在推论 12.4 中取 Binet 极限，得到第一行。为识别其条件熵，$k\ge1$ 时任意合法长度 $k+1$ 词 $ub$ 的 $\nu_{\rm left}$ 概率都是 $\phi^{-(k+1+b)}$。对同一 $b$ 有 $F_{k+2-b}$ 个这样的前缀。因此给定 $\omega_k=b$，前缀在 $\mathcal C_k(b)$ 上均匀；Markov 性使再给定任意有限未来柱不改变这个条件律。柱上的条件积分恒等式延伸到完整未来的 $\sigma$ 代数，得到一个正则条件分布版本，避免对零概率的单条无限尾取概率之比。其条件熵是 $\log_2F_{k+2-b}$，按 $p_k$ 平均即为 $E_k^{\rm left}$。空前缀的情形直接成立。

准确比值为

$$
\frac{p_{k,0}}{p_{0,0}}=F_{k+2}\phi^{-k},\qquad
\frac{p_{k,1}}{p_{0,1}}=F_{k+1}\phi^{-k}.
$$

将它们代入相对熵定义，便得到第二行。$k>0$ 时，$\phi^k=F_k\phi+F_{k-1}$ 是无理数，而 $F_{k+2}$ 是整数，故第一个比值不可能为一，$p_k\ne p_0$。引理 9.9 的相对熵非负性及等号准则遂给严格正性。

Binet 公式还给 $p_{k,0}\to\phi/\sqrt5$、$p_{k,1}\to\phi^{-1}/\sqrt5$，这正是 $\pi$；并非 $p_0$。由于 $p_0$ 的两个坐标均正，相对熵在概率单纯形上连续。$\pi\ne p_0$ 给正的常数极限；除以 $k$ 才趋零。

对平稳符号律 $\nu$，定理 11.6、11.7 的符号条件律给 $H_\nu(\omega|_k\mid\sigma^k\omega)=k\log_2\phi$。在 $\nu_{\rm left}$ 下，已知左端使相同完整尾的前缀均匀；在 $\nu$ 下，其权重为 $h_{u_0}/(\phi^kh_b)$。这里比较的是分别声明的两个来源律，正的 KL 项准确保留了它们的端点区别。无限地址的损失均指有限前缀的条件熵，不取整个无限流熵的“无穷减无穷”。$\square$

**命题 12.7（内块给定完整右尾的有限律）。** 取 $X\sim Q_N$，固定 $k\ge1,r\ge0,r+k\le N$，令

$$
U=(X_r,\ldots,X_{r+k-1}),\qquad
V=\delta^{r+k}X,\qquad b=V_0.
$$

当 $r+k=N$ 时，$V=0^\infty$，取 $b=0$。对 $u\in\{0,1\}^k$，记

$$
I(u,b)=\left(\prod_{j=0}^{k-2}A_{u_ju_{j+1}}\right)A_{u_{k-1}b},
$$

空乘积为一。对每个正概率右尾 $v$，有

$$
\Pr_{Q_N}(U=u\mid V=v)
=I(u,b)\frac{F_{r+2-u_0}}{F_{r+k+2-b}}.
$$

$r=0$ 时，它在相容前缀上均匀。固定 $k$，令 $r\to\infty$，上述条件律的极限为

$$
I(u,b)\frac{h_{u_0}}{\phi^kh_b}.
$$

该极限对同一 $b$ 不依赖右尾长度；只需 $N\ge r+k$，包括右尾为空的边界。

证明。给定 $v$ 后，全部相容长度 $r+k$ 左前缀等概率，定理 11.2 给其数量 $F_{r+k+2-b}$。固定块 $u$ 合法并与 $b$ 相容时，它之前还有 $r$ 位可选，数量为 $F_{r+2-u_0}$；否则数量为零。因此上述分子、分母准确计数同一条件事件，求和自动归一。$r=0$ 时 $F_{2-u_0}=1$。Binet 公式给

$$
\frac{F_{r+2-u_0}}{F_{r+k+2-b}}
\longrightarrow\phi^{-k+b-u_0}
=\frac{h_{u_0}}{\phi^kh_b},
$$

得到极限。右尾已经完整给定，所以没有要求它到右端的距离趋于无穷。

这个极限核是定理 11.6 在平稳符号律 $\nu$ 下给定完整未来的条件前缀核。若 $V$ 为无限随机未来，则应将它解释为正则条件分布：按首位 $b$ 定义核，并在每个有限未来柱上验证条件积分恒等式，再延伸到生成的 $\sigma$ 代数。不能把无限未来的单点当成正概率事件相除。给定右尾的收敛不等于无条件内块已达到平稳分布；后者还要平均右端的实际权重。$\square$

**命题 12.8（双端桥与有限均匀来源的 Parry 表示）。** 在命题 12.7 中另保留左接缝 $a=X_{r-1}$；$r=0$ 时以虚拟位 $a=0$ 代替。对每个正概率的 $(a,V=v)$，

$$
\Pr_{Q_N}(U=u\mid a,V=v)
=\frac{A_{a u_0}I(u,b)}{(A^{k+1})_{ab}},\qquad
A^{k+1}=\begin{pmatrix}F_{k+2}&F_{k+1}\\F_{k+1}&F_k\end{pmatrix}.
$$

给定整个左前缀而非只给 $a$ 时，公式相同。这正是转移矩阵 $P$ 在端点 $a,b$ 给定时的长度 $k$ 隐藏块桥律。特别地，$Q_N$ 恰等于从虚拟位 $X_{-1}=0$ 出发、以 $P$ 转移、再条件于 $X_N=0$ 的有限 Parry 桥。

证明。给定 $a,v$ 时，每个相容块 $u$ 的左侧可选来源数相同，右侧已经固定。若整个左前缀也固定，该共同数就是一。合法块的数目是从 $a$ 到 $b$ 的 $k+1$ 步图路径数 $(A^{k+1})_{ab}$；均匀 $Q_N$ 遂给所述桥律。矩阵幂公式由 $A^2=A+I$ 与 Fibonacci 递推得到，$k\ge1$ 时所有端点对的分母均正。

在 Markov 律下，把 $s_0=a,s_{k+1}=b$，中间 $k$ 位为 $u$，路径概率望远镜相消为

$$
\prod_{j=0}^{k}P_{s_js_{j+1}}
=A_{a u_0}I(u,b)\,\phi^{-(k+1)}\frac{h_b}{h_a},
$$

而

$$
(P^{k+1})_{ab}=(A^{k+1})_{ab}\,\phi^{-(k+1)}\frac{h_b}{h_a}.
$$

按端点条件化即给同一均匀桥。对整个 $D_N$ 词，从 $-1$ 的零到 $N$ 的零共有 $N+1$ 次转移，每条合法路径的概率均为 $\phi^{-(N+1)}$，桥的路径数为 $(A^{N+1})_{00}=F_{N+2}$，故条件概率恰为 $1/F_{N+2}$。$N=0$ 时桥没有隐藏来源位，仅给 $D_0$ 的点质量。两个虚拟零表示已声明的左右边界，不增加独立长度或 End 观察。

均匀性来自 $Q_N$ 或指定的 Parry 转移产品，并非来自 no-11 支撑本身。例如在 $D_1$ 的 $0,1$ 上分别赋质量 $3/4,1/4$，虚拟端点仍都是零，隐藏位却不均匀。

隐藏块保留的是左右两个端口之间的桥关系，不是将可见两侧直接拼接的许可。合法词 $101$ 隐去中间的 $0$，可见端点是 $a=b=1$，其一位桥唯一为 $0$；直接拼成 $11$ 却非法。因而内部删除不能在没有额外接缝条件时当作前缀剥离。$\square$

**命题 12.9（无条件内区的双边距离与局部收敛）。** 固定 $k\ge1$，令 $r\ge0,s=N-r-k\ge0$。记 $e_0=(1,0)^{\mathsf T}$、$\mathbf1=(1,1)^{\mathsf T}$。对任意 $u\in\{0,1\}^k$，

$$
\Pr_{Q_N}(U=u)=
\frac{(e_0^{\mathsf T}A^{r+1})_{u_0}
\left(\prod_{j=0}^{k-2}A_{u_ju_{j+1}}\right)
(A^s\mathbf1)_{u_{k-1}}}{F_{N+2}}.
$$

在 $N\to\infty$ 的序列上，该无条件块律趋于平稳 Parry 块律，当且仅当 $r\to\infty$ 且 $s\to\infty$。此时

$$
\Pr_{Q_N}(U=u)\longrightarrow
\pi_{u_0}\prod_{j=0}^{k-2}P_{u_ju_{j+1}}.
$$

证明。从虚拟左零到 $u_0$ 的左段有 $r+1$ 条边，其数为 $(e_0^{\mathsf T}A^{r+1})_{u_0}$。右段在块后尚有 $s$ 位，各末位都能接虚拟右零，故数量为 $(A^s\mathbf1)_{u_{k-1}}$；$s=0$ 时它为一。乘上块内合法性因子，除以全部来源数，得到准确公式。

令 $C=\phi^2+1$，$h=(\phi,1)^{\mathsf T}$、$g=(1,-\phi)^{\mathsf T}$。两向量正交、平方范数同为 $C$，并分别对应特征值 $\phi,-\phi^{-1}$。因此对每个 $n\ge0$，

$$
A^n=\phi^n\frac{hh^{\mathsf T}}C
+(-\phi^{-1})^n\frac{gg^{\mathsf T}}C.
$$

当 $r,s$ 都趋于无穷时，在准确计数公式中分别用第一项作两侧主项，并用 $F_{N+2}=(A^{N+1})_{00}\sim\phi^{N+1}h_0^2/C$。由于 $h^{\mathsf T}\mathbf1=\phi^2$，所得极限为

$$
\frac{h_{u_0}h_{u_{k-1}}}{C\phi^{k-1}}
\prod_{j=0}^{k-2}A_{u_ju_{j+1}}
=\pi_{u_0}\prod_{j=0}^{k-2}P_{u_ju_{j+1}}.
$$

为证明必要性，若 $r$ 不趋于无穷，取子序列使整数 $r$ 固定；$N\to\infty$ 使右距离趋于无穷。命题 12.5 给块首位的极限分布 $p_r=p_0P^r\ne\pi$：$P$ 可逆，$\pi P=\pi$，若 $p_0P^r=\pi$ 则反乘 $P^{-r}$ 迫 $p_0=\pi$，矛盾。若 $s$ 不趋于无穷，同样取 $s$ 固定的子序列。$Q_N$ 对长度 $N$ 词的反转不变，故块末位分布等于原词第 $s$ 位分布，极限为 $p_s\ne\pi$。任一有界端距都阻止整个块律趋于平稳律。

这些极限仅涉及固定长度柱事件。$Q_N$ 本身不投影一致：第零位为一的概率在 $N=1$ 时为 $1/2$，在 $N=2$ 时为 $1/3$。将各 $Q_N$ 看成 $\Omega$ 上补零的概率，仍有 $Q_N(D)=1$，而命题 11.8 给 $\nu(D)=0$。$\nu_{\rm left}(D)=0$ 也成立：从任意第 $n$ 位开始连续 $\ell$ 个零的概率为 $p_{n,0}\phi^{-(\ell-1)}$，令 $\ell\to\infty$ 再对 $n$ 取可数并即可。因此以 $d_{\rm TV}(Q,R)=\sup_B|Q(B)-R(B)|$ 定义总变差距离时，

$$
d_{\rm TV}(Q_N,\nu)=d_{\rm TV}(Q_N,\nu_{\rm left})=1
\quad\text{对每个 }N\ge0.
$$

平移后的有限来源仍最终为零，同一集合也分离其律与 $\nu$。局部柱极限因而不能升级成整条流的总变差收敛；固定左边界的极限为 $\nu_{\rm left}$，只有两端都远离固定内块时才得到 $\nu$。$\square$

**推论 12.10（指定 FIB 删除的信息方向）。** 对同一个有界来源 $X$，仅保留 $Y_k$ 的删除形成命题 12.2 的等价关系粗化链；在指定的同一律 $Q$ 下，其概率损失非递减，严格增加恰发生于命题 12.3 的两个正概率前驱合并。对 $D_N$ 的每个来源，最多 $F_{N+2}$ 个残余记录值已足以精确恢复任意删除长度后的来源；有限来源身份也能由有限状态恒等映射或置换无损保存。

证明。等价关系与条件熵分别由命题 12.2、12.3 给出，残余记录由前者的容量式给出。有限集 $D_N$ 本身可作保存身份的状态集，恒等映射与置换都是双射。因此上述不可逆性以没有保留恢复记录的指定删除为条件，不是有限记忆必然遗忘的定理。精确恢复容量、指定律下的条件熵和实现所需的总内存是不同问题；这些结论没有物理能量、热浴或时间变量前提，不能推导物理热量或普遍的物理时间箭头。$\square$

## 追加锚（本行以下为增补区）

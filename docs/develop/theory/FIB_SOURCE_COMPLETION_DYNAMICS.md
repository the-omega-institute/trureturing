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

## 13. 初始化可逆时域的精确总状态成本与实际来源的完整历史

**定义 13.1（有限时域初始化模拟）。** 设 $X$ 为有限集合，$f:X\to X$ 为确定映射，$H\ge0$ 为整数。一个时域 $H$ 的初始化可逆模拟是四元组 $(E,P,\eta,i)$，其中 $E$ 为有限内部状态集，$P:E\to E$ 为一个置换，$\eta:E\to X$ 为固定且与时间无关的全定义读出，$i:X\to E$ 为初始化映射，满足

$$
\eta(P^t i(x))=f^t(x)
\qquad(x\in X,\ 0\le t\le H).
$$

成本为总状态数 $|E|$；机器、时钟、记忆及其他内部状态全部计入 $E$，没有另行免费的时间坐标。条件 $t=0$ 给出 $\eta i=\operatorname{id}_X$，从而 $i$ 单射。此定义只约束初始化轨道的指定时域，不要求在整个 $E$ 上成立 $\eta P=f\eta$。记

$$
L=X\setminus f(X),\qquad m=|X|.
$$

$L$ 是没有前驱的来源集合。若 $X=\varnothing$，全定义映射 $\eta:E\to X$ 迫使 $E=\varnothing$，空置换给出成本零的模拟。

**定理 13.2（精确总状态成本）。** 在定义 13.1 的全部条件下，初始化可逆模拟的最小总状态数为

$$
\min |E|=|X|+H|X\setminus f(X)|=m+H|L|.
$$

该式包括空集合、$H=0$ 以及 $f$ 为置换的情形。

证明。先证下界。集合 $P^H i(X)$ 有 $m$ 个不同状态。考虑另一个状态集合

$$
B=\{P^t i(\ell):\ell\in L,\ 0\le t<H\}.
$$

若 $P^t i(\ell)=P^s i(\ell')$，可交换两对指标而假设 $t\le s$。由 $P$ 可逆，消去 $P^t$ 后得到 $i(\ell)=P^{s-t}i(\ell')$。当 $s=t$ 时，$i$ 单射给 $\ell=\ell'$；当 $s>t$ 时，模拟条件给

$$
\ell=f^{s-t}(\ell')\in f(X),
$$

因为 $1\le s-t\le H$，这与 $\ell\in L$ 矛盾。因此 $B$ 的各个标记状态互异，$|B|=H|L|$。若其中一个状态等于 $P^H i(x)$，消去 $P^t$ 并读出得到

$$
\ell=f^{H-t}(x)\in f(X),\qquad 1\le H-t\le H,
$$

同样矛盾。所以 $B$ 与 $P^H i(X)$ 不交，给出 $|E|\ge m+H|L|$。$H=0$ 时 $B$ 为空，下界仍成立。

为达到此界，在 $f$ 的有限有向图中，为每个 $y\in f(X)$ 选择一个前驱 $p(y)$，只保留边 $p(y)\to y$。若 $y$ 位于 $f$ 的一个周期上，指定 $p(y)$ 为该周期的前一顶点。每个像顶点的选定入度为一，每个 $L$ 顶点的入度为零；每个顶点的选定出度至多为一，因为从 $x$ 保留的边只能指向 $f(x)$。

选定图因此分解成不交的有向周期和有向路径，孤立顶点作为长度一的路径。其周期恰为 $f$ 的原周期：原周期的全部边都已指定，而任一选定周期也必是 $f$ 的周期。路径不能进入一个周期，因为周期顶点唯一的选定入边已由周期前驱占用。每条路径的起点入度为零，因而恰属 $L$；反之，每个 $L$ 顶点都是一条路径的唯一起点。因此共有 $|L|$ 条路径。

对一条包含 $r\ge1$ 个原顶点的路径，写成

$$
x_0\longrightarrow x_1\longrightarrow\cdots\longrightarrow x_{r-1},
\qquad x_{a+1}=f(x_a)\quad(0\le a<r-1).
$$

增加 $H$ 个与全部原顶点及其他新增状态不同的状态 $a_1,\ldots,a_H$，将这条路径闭合成置换周期

$$
x_0,x_1,\ldots,x_{r-1},a_1,\ldots,a_H.
$$

这个周期共有 $r+H$ 个状态，其中新增的只有 $H$ 个。读出定义为

$$
\eta(x_a)=x_a\quad(0\le a<r),\qquad
\eta(a_j)=f^j(x_{r-1})\quad(1\le j\le H).
$$

当 $H=0$ 时直接把原路径闭合成长度 $r$ 的周期。原有周期保持不变，读出在其顶点上也是恒等映射。初始化把每个 $x\in X$ 放在它自己的原顶点。

从路径顶点 $x_a$ 出发，任意 $0\le t\le H$ 的周期位置为 $a+t$，且

$$
a+t\le r-1+H<r+H.
$$

所以指定时域内不会跨过闭合边。当 $a+t<r$ 时读出为 $x_{a+t}=f^t(x_a)$；当 $a+t=r-1+j$ 且 $1\le j\le H$ 时，读出为 $f^j(x_{r-1})=f^t(x_a)$。从原周期顶点出发则在所有时刻都沿 $f$ 运行。这给出定义 13.1 的模拟，总共增加 $H|L|$ 个状态，成本正好为 $m+H|L|$。空 $X$ 的结论由定义 13.1 给出；若 $f$ 是置换，$L=\varnothing$，选定图只有原周期，构造就是 $E=X,P=f$。$\square$

**推论 13.3（有界 FIB 单位删位与整窗删位的成本）。** 沿用约定 12.1 的 $D_N$，单位位恒为零，全部地址无相邻一，支持位位于 $N$ 以下，零来源包含在内，高位补零识别，没有独立 End。对最低一位删除 $\delta:D_N\to D_N$，时域 $H$ 的最小初始化可逆模拟成本为

$$
C_N(H)=F_{N+2}+HF_N\qquad(N,H\ge0).
$$

若一步改为删去整个三位窗口，即 $f=\delta^3$，且 $H$ 计窗口步数，则最小成本为

$$
C_N^{\rm win}(H)
=F_{N+2}+H\bigl(F_{N+2}-F_{\max(N-3,0)+2}\bigr).
$$

第二式的一次置换步对应一个三位窗口。若改以一次置换步对应一位删除，并要求每一中间单位删位时刻也读出，则 $H$ 个窗口所覆盖的单位步时域为 $3H$，相应成本为 $C_N(3H)=F_{N+2}+3HF_N$。两个式子的时域步单位不同。

证明。命题 12.2 给 $|D_N|=F_{N+2}$。对 $N\ge1$，

$$
\delta(D_N)=D_{N-1},\qquad
|D_N\setminus\delta(D_N)|
=F_{N+2}-F_{N+1}=F_N.
$$

像的等式也可直接看到：删位后的支持小于 $N-1$，任意这样的尾都能前置零而得到 $D_N$ 的来源。$N=0$ 时只有零来源，缺像数为零，恰为 $F_0$。定理 13.2 给第一式。三次删位的像为 $D_{\max(N-3,0)}$，再用同一定理给窗口式；要求全部单位中间时刻时直接以 $3H$ 为时域。

这些量计算内部状态的基数，没有指定概率律，因而不是 Shannon 熵。命题 12.2 的静态恢复合同把删位长度 $k$ 和保留尾当作已知信息，只计算残余记录字母表，其最小容量为

$$
R_N(k)=F_{\min(k,N)+2}.
$$

当 $k\ge N$ 时，保留尾已为零，$R_N(k)$ 不再增加。初始化置换模拟则还须在同一固定读出下维持整个指定时域；$N\ge1$ 时，定理 13.2 的叶时刻状态仍迫使成本随 $H$ 增加。有限置换的每个内部轨道都会返回初始化状态，延长时域必须把不相容的返回推到时域之外。这种状态成本不是零尾之后继续产生的来源条件熵损失；对同一 $D_N$ 来源和同一律 $Q$，$H_Q(X\mid\delta^kX)$ 在 $k\ge N$ 时已恒为 $H_Q(X)$。$\square$

**命题 13.4（无限时域障碍与全局交换合同）。** 对有限 $X$ 和确定映射 $f:X\to X$，一个有限的 $(E,P,\eta,i)$ 同时满足

$$
\eta(P^t i(x))=f^t(x)\qquad(x\in X,\ t\ge0)
$$

当且仅当 $f$ 为置换。对有界 FIB 来源，即使只指定一个非零 $x\in D_N$，也不存在有限置换 $P$、固定读出 $\eta$ 和初始化状态 $e$，使 $\eta(P^t e)=\delta^t x$ 对所有 $t\ge0$ 成立。

另一个合同是全局可逆因子：对任意集合 $E,X$、映射 $f:X\to X$、双射 $g:E\to E$ 和满射 $\eta:E\to X$，若

$$
\eta g=f\eta\quad\text{在全部 }E\text{ 上成立},
$$

则 $f$ 必满射。因此 $N\ge1$ 时，$\delta:D_N\to D_N$ 也没有这种全局可逆因子。全局交换要求强于定义 13.1 仅在初始化轨道及指定时域上的等式。

证明。一个全时域的有限模拟也是每个有限时域 $H$ 的模拟。由定理 13.2，固定的 $|E|$ 必大于等于 $|X|+H|L|$，所以 $L=\varnothing$。有限集上的满射是置换；反之取 $E=X,P=f,\eta=i=\operatorname{id}_X$ 即可，空集也包括在内。

对单一非零 $x\in D_N$，若有上述有限实现，则存在 $q\ge1$ 使 $P^q e=e$。取整数 $a$ 使 $aq\ge N$，得到

$$
x=\eta(e)=\eta(P^{aq}e)=\delta^{aq}x=0^\infty,
$$

矛盾。对于全局因子，任取 $x\in X$，由 $\eta$ 满射可取 $e$ 使 $\eta(e)=x$；再由 $g$ 可逆，

$$
x=\eta(gg^{-1}e)=f(\eta(g^{-1}e))\in f(X).
$$

故 $f$ 满射。推论 13.3 的像计算说明 $N\ge1$ 时 $\delta(D_N)=D_{N-1}\subsetneq D_N$，给出 FIB 结论。

有限状态的限制可以在初始化合同中用可数状态解除。B. V. Rajarama Bhat、Sandipan De、Narayan Rakshit，*A caricature of dilation theory* (2021)，arXiv:2004.09255v1，[预印本 Theorem 1.20](https://arxiv.org/html/2004.09255v1)，给出经典集合论构造。将其读出写为 $X$ 值，构造为

$$
\begin{aligned}
E&=X\times\mathbb Z,& P(x,n)&=(x,n+1),& i(x)&=(x,0),\\
\eta(x,n)&=\begin{cases}f^n(x),&n\ge0,\\x,&n<0.\end{cases}
\end{aligned}
$$

从初始化状态出发，$P^t i(x)=(x,t)$，所以对所有 $t\ge0$ 都有正确读出；对于有限或可数 $X$，$E$ 至多可数。它适用于这里的 $D_N$ 以及可数的实际来源 $D$，是上述有限成本与无限时域障碍的经典边界比较。在 $n\ge0$ 时有 $\eta P(x,n)=f\eta(x,n)$；在 $n<0$ 时，两边分别为 $x$ 与 $f(x)$，故只在 $f(x)=x$ 时相等。因此该初始化构造不提供任意 $f$ 的全局交换等式，负时刻的交换也不是处处失败。$\square$

**定义 13.5（实际来源的完整逆历史）。** 在无统一支持上界的实际域 $D=\bigcup_{N\ge0}D_N$ 上，定义

$$
\mathcal H_D
=\left\{(x^{(n)})_{n\ge0}\in D^{\mathbb N}:
\delta x^{(n+1)}=x^{(n)}\text{ 对所有 }n\ge0\right\},
\qquad \pi_0((x^{(n)}))=x^{(0)}.
$$

每个历史坐标都是实际有限来源，不是任意无限右尾。历史动力学及其逆定义为

$$
\begin{aligned}
\widehat\delta(x^{(0)},x^{(1)},x^{(2)},\ldots)
&=(\delta x^{(0)},x^{(0)},x^{(1)},\ldots),\\
\widehat\delta^{-1}(x^{(0)},x^{(1)},x^{(2)},\ldots)
&=(x^{(1)},x^{(2)},x^{(3)},\ldots).
\end{aligned}
$$

兼容关系保证二者都落在 $\mathcal H_D$ 且互逆，并有 $\pi_0\widehat\delta=\delta\pi_0$。双边地址空间取

$$
Z_D=\{z\in\{0,1\}^{\mathbb Z}:z_jz_{j+1}=0\text{ 对所有 }j\in\mathbb Z,
\ \exists J\in\mathbb Z\ \forall j\ge J, z_j=0\},
\qquad (Sz)_j=z_{j+1}.
$$

右方最终为零，左方不施加最终为零的条件；负指标表示较早来源的已删地址位，不是定义 1.1 的外部单位位。$D$ 取 $\{0,1\}^{\mathbb N}$ 前缀乘积拓扑的子空间拓扑，$\mathcal H_D$ 取 $D^{\mathbb N}$ 乘积拓扑的子空间拓扑，$Z_D$ 取 $\{0,1\}^{\mathbb Z}$ 乘积拓扑的子空间拓扑；二元字母表均取离散拓扑。

**定理 13.6（实际有限来源的双边历史模型）。** 映射

$$
\Phi:Z_D\longrightarrow\mathcal H_D,\qquad
\bigl(\Phi(z)^{(n)}\bigr)_j=z_{j-n}
\quad(n\ge0,\ j\ge0)
$$

是同胚，且 $\Phi S=\widehat\delta\Phi$。其逆为

$$
\bigl(\Phi^{-1}((x^{(n)})_{n\ge0})\bigr)_k
=\begin{cases}
x^{(0)}_k,&k\ge0,\\
x^{(-k)}_0,&k<0.
\end{cases}
$$

更一般地，对任意整数 $k$ 和 $n\ge\max(0,-k)$，同一个逆地址满足 $z_k=x^{(n)}_{k+n}$。$\pi_0$ 为满射，$\widehat\delta$ 是实际 $D$ 的全局可逆历史实现。若将全部历史坐标限制在同一个 $D_N$ 内，则历史空间只有全零历史。

证明。若 $z\in Z_D$，每个 $n$ 的右尾 $(z_{j-n})_{j\ge0}$ 都无相邻一且最终为零，故属于 $D$。对于全部 $n,j\ge0$，

$$
\bigl(\delta\Phi(z)^{(n+1)}\bigr)_j
=z_{j+1-(n+1)}=z_{j-n}
=\bigl(\Phi(z)^{(n)}\bigr)_j,
$$

所以 $\Phi(z)$ 是兼容历史。

反之，兼容历史满足 $\delta^{m-n}x^{(m)}=x^{(n)}$ 对所有 $m\ge n\ge0$ 成立。因此，当 $n\ge\max(0,-k)$ 且 $m\ge n$ 时，

$$
x^{(n)}_{k+n}=x^{(m)}_{k+m}.
$$

这说明 $z_k=x^{(n)}_{k+n}$ 与允许的 $n$ 无关，并给出所列逆公式。对任意相邻整数 $k,k+1$，取同一个足够大的 $n$ 使 $k+n\ge0$，则 $z_k,z_{k+1}$ 是合法来源 $x^{(n)}$ 的相邻位，不能同时为一。对 $k\ge0$，$z_k=x^{(0)}_k$，故 $z$ 的右方最终为零，$z\in Z_D$。再取 $k=j-n$，得到 $z_{j-n}=x^{(n)}_j$，证明两映射互逆。

对 $n=0$，$\Phi(Sz)^{(0)}=\delta\Phi(z)^{(0)}$；对 $n\ge1$，任意 $j\ge0$ 有

$$
\bigl(\Phi(Sz)^{(n)}\bigr)_j
=z_{j-n+1}
=\bigl(\Phi(z)^{(n-1)}\bigr)_j.
$$

这正是 $\Phi S=\widehat\delta\Phi$。$S$ 和其逆右移都保持 $Z_D$。

拓扑方面，$\Phi$ 的每个输出位 $(n,j)$ 只依赖输入位 $j-n$；规定有限多个历史坐标的有限前缀，只规定 $z$ 的有限多个坐标。逆映射的每个位 $k$ 也只依赖历史的单个坐标位：$k\ge0$ 时取 $(0,k)$，$k<0$ 时取 $(-k,0)$。乘积子空间的柱集因而证明双向连续，无须紧致性前提。任意 $x\in D$ 都可在负指标补零而得到 $z\in Z_D$，所以 $\pi_0$ 满射。

若全部 $x^{(n)}\in D_N$，对任意 $n\ge0$ 有

$$
x^{(n)}=\delta^N x^{(n+N)}=0^\infty,
$$

因为 $\delta^N$ 在 $D_N$ 上恒为零；$N=0$ 时 $D_0$ 本来就只有零来源。这给出有界历史的唯一性。$\square$

**命题 13.7（完整历史纤维及其保留的信息）。** 对每个固定实际右尾 $x\in D$，完整历史纤维 $\pi_0^{-1}\{x\}$ 的基数都是连续统 $2^{\aleph_0}$。经定理 13.6，它恰为所有与 $x$ 接缝相容的合法双边左过去。对任意 $h=(x^{(n)})\in\mathcal H_D$，

$$
\pi_0\widehat\delta^t h=\delta^t x^{(0)}\quad(t\ge0),
\qquad
\pi_0\widehat\delta^{-n}h=x^{(n)}\quad(n\ge0).
$$

因此，每个完整历史状态保留指定来源的全部删去位及所选的相容更早过去；完整历史空间容纳每一种允许的过去，当前右尾读出只保留尚未删去的位。

证明。固定非负指标为 $x$ 后，任一历史由负指标的二元序列确定，纤维基数至多为 $2^{\aleph_0}$。为得到下界，对任意 $(\varepsilon_m)_{m\ge1}\in\{0,1\}^{\mathbb N_{\ge1}}$，置

$$
z_j=x_j\quad(j\ge0),\qquad
z_{-2m}=\varepsilon_m\quad(m\ge1),\qquad
z_{-(2m-1)}=0\quad(m\ge1).
$$

任意两自由位之间都有一个零，$z_{-1}=0$ 又隔开左方与 $x_0$ 的接缝，因此所得双边地址合法，且右方仍最终为零。不同自由序列给出不同纤维元素，遂得到下界 $2^{\aleph_0}$。

正向读出公式由 $\pi_0\widehat\delta=\delta\pi_0$ 迭代得到，反向公式由移去前 $n$ 个历史坐标得到。在双边坐标中，时刻 $t$ 的右尾为 $(z_{t+j})_{j\ge0}$，完整的 $S^tz$ 仍记录全部 $z_k$：$0\le k<t$ 的原来源位已进入负指标，更早的 $k<0$ 也仍存在。实际来源的组成由地址按定义 1.1 唯一确定，历史模型没有添加独立的算术选择。纤维计数描述完整历史对象的大小；它不把全部允许过去的保留强加给每一种可逆实现。$\square$

**命题 13.8（唯一历史提升及其非满射反例）。** 设 $E$ 为任意集合，$g:E\to E$ 为双射，$\eta:E\to D$ 满足全局等式 $\eta g=\delta\eta$。则存在唯一映射 $\Lambda:E\to\mathcal H_D$，满足

$$
\pi_0\Lambda=\eta,\qquad
\Lambda g=\widehat\delta\Lambda,
\qquad
\Lambda(e)=(\eta(g^{-n}e))_{n\ge0}.
$$

即使 $\eta$ 为满射，$\Lambda$ 也不必为满射。具体地，定义

$$
Z_{\rm fin}
=\{z\in Z_D:|\{j\in\mathbb Z:z_j=1\}|<\infty\},
\qquad
\eta_{\rm fin}(z)=(z_j)_{j\ge0}.
$$

$Z_{\rm fin}$ 是 $Z_D$ 的可数、真、稠密子空间，$S$ 及 $S^{-1}$ 都保持它，$\eta_{\rm fin}$ 满射到 $D$，且

$$
\eta_{\rm fin}S=\delta\eta_{\rm fin}.
$$

此可逆实现的唯一历史提升为 $\Phi|_{Z_{\rm fin}}$，其像严格小于 $\mathcal H_D$。因此，为每个来源提供至少一条允许过去与保留每条允许的无限过去，是两个不同要求。

证明。全局等式给出

$$
\delta\eta(g^{-(n+1)}e)=\eta(g^{-n}e),
$$

所以所列 $\Lambda(e)$ 是兼容历史。其第零坐标为 $\eta(e)$。$\Lambda(ge)$ 的第零坐标为 $\delta\eta(e)$，第 $n\ge1$ 坐标为 $\eta(g^{-(n-1)}e)$，这恰为 $\widehat\delta\Lambda(e)$。

若 $\Lambda':E\to\mathcal H_D$ 也满足这两个交换等式，由 $g$ 和 $\widehat\delta$ 可逆可得 $\Lambda'g^{-n}=\widehat\delta^{-n}\Lambda'$。于是

$$
(\Lambda'(e))^{(n)}
=\pi_0\widehat\delta^{-n}\Lambda'(e)
=\pi_0\Lambda'(g^{-n}e)
=\eta(g^{-n}e),
$$

对所有 $n\ge0$ 成立，给出唯一性。

整数集的有限子集构成可数集合，所以 $Z_{\rm fin}$ 至多可数；仅在一个整数指标为一的地址已给出可数无穷多个成员。双向平移保持有限支持与无相邻一条件。对每个 $x\in D$，负指标补零得到 $Z_{\rm fin}$ 中的前像，故 $\eta_{\rm fin}$ 满射；坐标计算给全局交换等式。

令 $z_{-2m}=1$ 对每个 $m\ge1$ 成立，其余坐标全为零，就得到 $Z_D\setminus Z_{\rm fin}$ 的成员，证明子空间为真。任意 $z\in Z_D$ 的截断

$$
z^{[M]}_j=\begin{cases}z_j,&-M\le j\le M,\\0,&\text{其他 }j\end{cases}
\qquad(M\ge0)
$$

都在 $Z_{\rm fin}$ 中：改位为零不能制造相邻一。任意有限坐标柱在足够大的 $M$ 下与 $z$ 一致，故 $z^{[M]}\to z$，证明稠密。唯一提升公式在这些双边地址上恰给 $\Phi$；由于 $\Phi$ 单射且 $Z_{\rm fin}$ 为真子空间，提升不是满射。这个可数反例也说明命题 13.7 的连续统纤维不是一般可逆实现的记忆基数下界。$\square$

**推论 13.9（恢复、初始化模拟与历史保留的条件区分）。** 在同一 FIB 来源与删位映射上，已知长度和尾的精确静态恢复、指定时域的初始化可逆模拟、满射读出下的全局可逆因子、以及全部逆历史保留，分别由不同条件约束。静态恢复使用命题 12.2 的 $R_N(k)$；单位删位的初始化模拟使用推论 13.3 的 $C_N(H)$；有界 $D_N$ 在 $N\ge1$ 时没有全局可逆因子，而无统一上界的实际 $D$ 具有命题 13.8 的可数全局实现和定义 13.5 的完整历史实现。

证明。前两项的成本来自各自的已知信息与模拟等式，后两项的存在性及差异由命题 13.4、定理 13.6 和命题 13.8 给出。可数实现的满射读出经唯一提升接入完整历史，却不覆盖全部历史；这给出了各要求之间可用的比较映射及其边界。另一方面，$D_N$ 上的恒等映射是有限且无损的来源身份保存，故单凭状态有限不能推出信息擦除。仅保留 $\delta^kX$ 的指定观察，其等价关系粗化和同一律下的条件熵方向仍由命题 12.2、12.3 决定；这些条件不等同于可逆实现或全部过去保留的要求。$\square$

## 追加锚（本行以下为增补区）

## 14. 折叠、延续与边界几何

本章固定 [FIBONACCI_ATOMIC_RELATION_GENERATION.md](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §§150–151 的低位到高位窗口约定，并沿用本卷已经定义的 FIB 单位位、无相邻一条件和高位补零合同。记
\[
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad q=(2,3).
\]
本章的“时间”只表示指定的删窗递推及其未来响应；“空间”只表示下述实区间商空间。两者的兼容性是定理条件，不是关于物理时空起源的断言。

**定义 14.1（来源域、窗口分解与两种观察）。** 设 $D$ 为采用固定单位位 $0$ 和高位补零识别的 canonical finite address 域，$\Omega$ 为所有单侧、无相邻一的无限地址，$T=\sigma^3$ 为删除最低三位的移位。对 $d\in D$，令 $\chi(d)$ 为最低三位窗口，令 $\sigma^3d$ 为删除该窗口所得尾部。则
\[
d\longmapsto\bigl(\chi(d),\sigma^3d\bigr)
\]
把 $D$ 双射到满足接缝合法性的有限窗口—尾部对。这里同时保留头和尾，因而没有发生信息商化。对每个合法窗口 $\sigma$，其组成向量的仿射更新写作
\[
F_\sigma(x)=M^3x+d_\sigma .
\]
在有效输入域上 $F_\sigma$ 单射；事实上其线性部分 $M^3$ 在 $\mathbb Z^2$ 上可逆。原始有序树域另记为 $\mathcal T$，其元素保留叶标签、括号和左右次序；组成投影只保留 $(a,b)$，并不等同于 $\mathcal T$。

**命题 14.2（canonical 分解的无损性与五窗状态）。** 在定义 14.1 的 canonical 域中，保持 $\chi(d)$ 与 $\sigma^3d$ 的联合读数是无损的；只保留其中一个投影才形成商。在这个 canonical 有限来源合同上，$q(x(d))$ 已是单射；因此五个窗口并不提供五个内在盲方向。五个首窗按最高位分为两种延拓类：
\[
\{\mathrm{null},2,3\}\quad\text{与}\quad\{25,5\}.
\]
前者的下一窗口可取 $2$，后者不能取 $2$；故下一标签 $2$ 区分两个活的合法性状态。若把读入非法串后的永久拒绝状态也纳入完整识别器，则得到两个合法状态加一个吸收非法状态，共三个状态。

证明。头—尾映射的逆映射就是把 $\chi(d)$ 接回尾部，并按固定单位位合同消除多余的高位零。$M^3$ 可逆说明 $F_\sigma$ 不会在有效域内自行合并两个输入。于是合并只能来自忘记头、尾或来源合同本身。最高位为零的三窗允许下一窗口的最低位为一；最高位为一的两窗使下一窗口的 incoming guard 状态为一，因而要求下一窗口的最低位为零。尾词 $2=100$ 在前一类合法、后一类非法，故两类不能合并。非法状态一旦进入便对所有继续输入拒绝，因而是吸收状态。证毕。

**命题 14.3（原始树与组成商的区别）。** 在原始有序树域上，令 $\rho$ 为母卷中定义的树替换，令 $c(T)=(a(T),b(T))$。按母卷 ATOM5.4、18.4 和 44–45 的记号，当前读出行向量为 $q=(2,3)=\epsilon M^3$。则 $\rho$ 在 $\mathcal T$ 上单射，且组成商对 $\rho$ 稳定：
\[
c(\rho T)=Mc(T).
\]
当前读数 $q\,c(T)$ 与下一读数 $qM\,c(T)$ 联合时可恢复组成
\[
a=5(qc)-3(qMc),\qquad b=2(qMc)-3(qc),
\]
但仍不能恢复括号、左右次序或叶位置信息。以 $T(6,1)$ 和 $T(1,4)$ 表示任取一棵组成分别为 $(6,1)$、$(1,4)$ 的固定树，在同一等概率二点来源律下，
\[
\begin{array}{c|ccc}
 &qM^0c&qM^1c&qM^2c\\ \hline
T(6,1)&15&23&38\\
T(1,4)&14&23&37
\end{array}
\]
因而来源标签关于这三个单次读数的条件不确定度依次为 $0,1,0$ 比特。

证明。$\rho$ 的递归解码由母卷的叶和内部节点规则给出：像中的单叶 $\beta$ 只能来自 $\alpha$，像中的 $\langle\beta,\alpha\rangle$ 只能来自 $\beta$，其余内部像逐子树解码。因此 $\rho$ 单射。矩阵恒等式给出组成更新和两次读数的逆公式。上表直接由 $q=(2,3)$、$qM=(3,5)$、$qM^2=(5,8)$ 与两组成向量相乘得到。两树在中间时刻有同一数值，首尾时刻又分开，说明“每一时刻都有一个观察”并不产生单调遗忘链。单调链需要实际的后处理因子化或纤维嵌套；它不能从不断更换观察函数本身推出。证毕。

**命题 14.4（共同边界的精确收缩与两个粗化操作）。** 沿用 [FIB_RELATIONAL_CONTINUATION_GEOMETRY.md](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) §§5.2–5.4 的共同实现和共享变量合同。从状态零出发，左窗口按其最高位（output seam）分成权重 $(3,2)$，右窗口的 incoming-guard 响应按同一 seam 分成 $(5,3)$，则精确共同实现数为
\[
3\cdot5+2\cdot3=21.
\]
若先分别把两张表聚合，再相乘，则得到
\[
(3+2)(5+3)=40.
\]
若直接删去中间的 no-$11$ 接缝约束而任意拼接五个左窗和五个右窗，则得到
\[
5\cdot5=25.
\]

证明。第一式在 seam 上逐项匹配同一个实际实现：最高位为零的 $\mathrm{null},2,3$ 只和右侧五种相容响应相乘，最高位为一的 $25,5$ 只和右侧三种相容响应 $\mathrm{null},3,5$ 相乘；共享变量只计一次，故为内积 $21$。第二式分别聚合两张 guard 响应表，产生所有交叉项 $3\cdot5+3\cdot3+2\cdot5+2\cdot3=40$。右表的三个窗口 $\mathrm{null},3,5$ 在两种 guard 行中各有一次记录，聚合后保留这些重复记录；两个交叉项又将不匹配的 seam 行任意配对。因此 $40$ 不是四十个不同的合法两窗来源。第三式只把五个左窗口和五个右窗口各列一次，删去中间 no-$11$ 约束后任意配对，故为 $25$；其中合法对仍有 $21$ 个，另四个对由左侧 $25,5$ 与右侧 $2,25$ 组成。$40$ 是“分别聚合带 guard 的响应表再组合”，$25$ 是“删除 seam 约束后任意组合”；二者作用于不同的记录与约束，不能按粗细顺序排列。把完整 response 表替换到 interior，只保证声明的外部 continuation 任务；它不恢复源树的括号和次序，源树恢复是另一性质。证毕。

### 14.1 区间编码、纤维和有限来源

**定义 14.5（本章的状态地址与区间编码）。** 为区分本卷的首位类、联合柱与母卷的路径状态，令
\[
A_0=\Omega,\qquad A_1=\{\omega\in\Omega:\omega_0=0\},
\]
其中本卷定义3.1的 $\Omega_i$ 仍表示 first-bit class，$K_i=\Omega_i\times G$ 仍表示 joint cylinder；它们不与此处的状态地址 $A_s$ 混用。令
\[
\phi=\frac{1+\sqrt5}{2},\qquad t=\phi^{-1},\qquad
\psi=-t,\qquad \gamma=\psi^3=-t^3,
\]
\[
I_0=[-1,\phi],\qquad I_1=[-1,t].
\]
这两个区间就是母卷 ATOM §§150–151 的 $K_0,K_1$；本章用 $I_i$ 避免与本卷的 joint cylinder $K_i$ 和 joint-domain $K$ 冲突。窗口按低到高读为
\[
\Sigma=\{\mathrm{null},2,3,25,5\}
=\{000,100,010,101,001\},
\]
并置
\[
\Delta_{\mathrm{null}}=0,\quad
\Delta_2=1,\quad
\Delta_3=-t,\quad
\Delta_{25}=2-t,\quad
\Delta_5=t^2.
\]
合法图为
\[
0\to0:\mathrm{null},2,3,\qquad
0\to1:25,5,\qquad
1\to0:\mathrm{null},3,\qquad
1\to1:5.
\]
若 $\omega\in A_s$ 是位地址，记其第 $n$ 个低到高三位窗口为
$\sigma_n(\omega)\in\Sigma$，定义
\[
\kappa_s(\omega)=\sum_{n\ge0}\gamma^n\Delta_{\sigma_n(\omega)}.
\]
删除动力学为 $T=\sigma^3$（在位地址上删除最低三位），这里使用 $M^3$ 所对应的三位窗口，而不使用第13章双边历史中的移位符号 $S$。
本章的一个时间步始终是一个三位窗口步；若改用第13章的单位删位时钟，三位窗口对应三个单位步，二者的视界参数不可混用。

**命题 14.6（五个根分支、极值和状态相对的唯一性）。** 五个根分支在 $I_0$ 中按空间顺序为
\[
\begin{array}{c|c}
\sigma&f_\sigma(I_{\mathrm{tail}})\\ \hline
3&[-1,t-1]\\
\mathrm{null}&[t-1,2t-1]\\
5&[2t-1,t]\\
2&[t,2t]\\
25&[2t,\phi],
\end{array}
\qquad f_\sigma(y)=\Delta_\sigma+\gamma y,
\]
其中 $5,25$ 的尾区间为 $I_1$，其余窗口的尾区间为 $I_0$。状态一只使用前三个空间块。令
\[
L=(3,25)^\infty,\qquad R=(25,3)^\infty,\qquad U=5L.
\]
则 $L$ 从两种状态都唯一编码 $-1$；$R$ 从状态零唯一编码 $\phi$；$U$ 从状态一唯一编码 $t$，而在状态零中 $t$ 还由 $2R$ 编码。四个根接触点为
\[
t-1,\quad 2t-1,\quad t,\quad 2t.
\]

证明。直接计算
\[
f_3(\phi)=-1,\qquad f_{25}(-1)=\phi,\qquad f_5(-1)=t.
\]
左端只能由窗口 $3$ 到达，右端在状态零只能由 $25$ 到达，在状态一只能由 $5$ 到达；每一步的尾端点又被唯一强制，故得到所列周期地址。状态零还允许 $2$，且 $f_2(\phi)=t$，所以 $t$ 在状态零有 $2R$ 与 $5L$ 两条地址；在状态一没有窗口 $2$，故 $U$ 唯一。根分支端点由表中相邻闭区间直接读出。证毕。

**定理 14.7（状态相对的编码纤维）。** 对固定起始状态 $s$，设 $\mathcal E_s$ 为所有合法有限前缀柱区间的内部公共端点集合。则
\[
|\kappa_s^{-1}(x)|=
\begin{cases}
2,&x\in\mathcal E_s,\\
1,&x\notin\mathcal E_s.
\end{cases}
\]
集合 $\mathcal E_s$ 可数且在 $I_s$ 中稠密；根区间两个外部极值为单编码。所有双编码均由一个有限前缀后接上述状态相对的极值尾产生，因而每个双编码点都是有限层内部端点，且不存在三重编码。

证明。固定长度前缀 $w$ 的柱像是
\[
I_w=f_w(I_{s(w)}).
\]
第一层五块（状态一为三块）内部两两不交，只在相邻端点相交；对每个前缀应用单射仿射映射，得到任意深度柱分块同样只在端点相交。若两条地址第一次在某位分歧，则共同坐标位于两个相邻分支的交点；分支尾必须是相应区间的极值，命题14.6使每一侧尾地址唯一。故至多两条地址，且每个内部端点确实给出两条地址。有限前缀可数、每层端点有限，所以 $\mathcal E_s$ 可数；柱直径至多 $|I_0||\gamma|^n$，故各层端点并在区间中稠密。外部极值由命题14.6唯一。证毕。

令 $D\subset A_0$ 为 eventually-null 地址（尾部全为 $\mathrm{null}$），并令 $P=\kappa_0(D)$。定理14.7中的双编码尾部均为非零周期尾，根极值也不是 eventually-null，故 $D$ 中的地址避开所有 $\mathcal E_0$，$\kappa_0|_D$ 单射。特别地，canonical finite address 的单射性来自固定单位位和高位补零约定，而不是把无限地址中的端点另行识别。

**命题 14.8（根接触阻止全空间删除因子）。** 令
\[
a=3L,\qquad b=\mathrm{null}R,\qquad z=t-1.
\]
则 $\kappa_0(a)=\kappa_0(b)=z$，而
\[
\kappa_0(Ta)=-1,\qquad \kappa_0(Tb)=\phi.
\]
因此不存在任何单值映射 $f:I_0\to I_0$，无论是否要求连续，都满足
\[
f\circ\kappa_0=\kappa_0\circ T
\quad\text{在 }A_0\text{ 上成立}.
\]

证明。由
\[
f_3(-1)=-t+t^3=t-1=f_{\mathrm{null}}(\phi)
\]
得到同一点的两条地址，而删除首窗后正是 $L$ 与 $R$ 的两个不同极值。若存在 $f$，同一点 $z$ 必须有两个不同像，矛盾。证毕。

**命题 14.9（有限来源上的连续性与非一致连续性）。** 删除在 $P$ 上诱导良定义映射
\[
g:P\to P,\qquad g(\kappa_0\omega)=\kappa_0(T\omega).
\]
截断任意合法地址并以 $\mathrm{null}^{\infty}$ 补尾可知 $P$ 在 $I_0$ 中稠密。它在 $P$ 的每一点连续，局部为
\[
g(x)=\frac{x-\Delta_\sigma}{\gamma}
\]
的仿射分支，但不一致连续，且不存在连续延拓 $\bar g:I_0\to I_0$。取
\[
L_N=(3,25)^N\mathrm{null}^{\infty},\qquad
R_N=(25,3)^N\mathrm{null}^{\infty},\qquad
\varepsilon_N=\gamma^{2N},
\]
则
\[
\kappa_0(L_N)=-1+\varepsilon_N,\qquad
\kappa_0(R_N)=\phi(1-\varepsilon_N),
\]
并且
\[
\begin{aligned}
x_N&=\kappa_0(3L_N),&
y_N&=\kappa_0(\mathrm{null}R_N),\\
|x_N-y_N|&=t\varepsilon_N\longrightarrow0,&
|g(x_N)-g(y_N)|
&=\phi^2(1-\varepsilon_N)\longrightarrow\phi^2.
\end{aligned}
\]

证明。$D$ 避开根接触和所有外部极值，所以每个 $x\in P$ 落在唯一首分支的相对内部邻域，分支公式给出点态连续性。两列都在 $P$ 中且趋于同一接触点 $z$，但删窗后的值趋于 $-1$ 和 $\phi$，故不一致连续；若有连续延拓则两列像必须有同一极限，矛盾。若以首个不同窗口位置 $k$ 定义前缀超度量 $d_\gamma(\omega,\nu)=|\gamma|^k$，则
\[
|\kappa_0(\omega)-\kappa_0(\nu)|
\le |I_0|\,d_\gamma(\omega,\nu)
=\phi^2d_\gamma(\omega,\nu),
\]
所以 $\kappa_0$ 对符号前缀尺度是 $\phi^2$-Lipschitz；这不意味着其逆或普通实数完成具有同一一致结构。证毕。

### 14.2 有限未来响应与动态边界

**定义 14.10（有限未来响应塔）。** 对 $h\ge0$ 定义
\[
Z_h(\omega)=\bigl(\kappa_0\omega,\kappa_0T\omega,\ldots,\kappa_0T^h\omega\bigr),
\qquad
\mathcal R_h=Z_h(A_0)\subset\mathbb R^{h+1}.
\]
一个长度 $h$ 的合法窗口前缀记为 $w=(\sigma_0,\ldots,\sigma_{h-1})$，末状态为 $s(w)$。对 $y\in I_{s(w)}$ 定义
\[
\Psi_w(y)_j=
\sum_{k=j}^{h-1}\gamma^{k-j}\Delta_{\sigma_k}
+\gamma^{h-j}y,\qquad 0\le j\le h.
\]

**定理 14.11（有限未来的线段分解）。** 有
\[
\mathcal R_h=\bigcup_{|w|=h}\Psi_w(I_{s(w)}).
\]
每个集合是非退化闭线段，且不同合法前缀给出的线段包括端点在内互不相交。因而
\[
\#\pi_0(\mathcal R_h)=F_{3h+2},
\]
其中末状态为零、为一的线段数分别为
\[
F_{3h+1},\qquad F_{3h}.
\]
这里 $h=0$ 时按空前缀末状态零解释。对每个 $0\le j<h$，
\[
z_j-\gamma z_{j+1}=\Delta_{\sigma_j}
\]
恢复第 $j$ 个窗口。

证明。若地址为 $w$ 后接尾地址，其尾部编码 $y$ 属于 $I_{s(w)}$，递归展开即得 $\Psi_w(y)$；反过来每个 $y$ 都由某个合法尾地址取得，故并集等式成立。五个 $\Delta_\sigma$ 两两不同，线性变换
\[
(z_0,\ldots,z_h)\mapsto
(z_0-\gamma z_1,\ldots,z_{h-1}-\gamma z_h,z_h)
\]
把每条线段送到固定的前缀增量列表乘以末坐标区间，故不同前缀不能相交。长度 $3h$ 的无相邻一词数为 $F_{3h+2}$；按最后一位计数得到 $F_{3h+1}$ 与 $F_{3h}$。证毕。

**命题 14.12（忘记末坐标的精确端点识别）。** 令
\[
\pi_h:\mathcal R_{h+1}\to\mathcal R_h,\qquad
\pi_h(z_0,\ldots,z_{h+1})=(z_0,\ldots,z_h).
\]
则 $\pi_h$ 连续满射。其每个纤维大小为一或二；被识别的不同端点对数为
\[
4F_{3h+1}+2F_{3h}
=F_{3h+5}-F_{3h+2},
\]
且不存在更大的纤维。该有限数不等于固定层 $\mathcal R_h$ 自身的可数双编码集合。

证明。固定父前缀 $w$ 后，子前缀 $w\sigma$ 的线段经 $\pi_h$ 映到父线段中的子区间
\[
\pi_h\Psi_{w\sigma}(y)=\Psi_w(f_\sigma(y)).
\]
状态零父段有五个相邻子块，状态一父段有三个相邻子块；每个相邻接点被两侧各一次取得，外端点只一次取得。由定理14.11不同父段互不相交，所以可把各父段端点数相加。父段数为 $F_{3h+1}+F_{3h}$，子段数为 $5F_{3h+1}+3F_{3h}$，差即
\[
4F_{3h+1}+2F_{3h}=F_{3h+5}-F_{3h+2}.
\]
这只计数“忘末坐标”所重新粘合的有限端点对。固定层的双地址纤维所对应的像点集合则恰为
\[
\{z\in\mathcal R_h:|Z_h^{-1}(z)|=2\}
=\bigcup_{|w|=h}\Psi_w(\mathcal E_{s(w)}).
\]
确实，$Z_h$ 恢复前 $h$ 个窗口，剩余纤维就是固定末状态的尾编码纤维。由定理14.7，每条父段中的这类像点可数且稠密；有限个父段互不相交，所以并集在 $\mathcal R_h$ 中可数且稠密。它位于 $\mathcal R_h$，而非一律位于 $I_0$，也不同于 $\pi_h$ 本次识别的有限端点对。证毕。

**定理 14.13（逆极限、删除和有限层的失败）。** 逆极限
\[
\varprojlim(\mathcal R_h,\pi_h)
\]
同胚于 $A_0$。删除首坐标的映射
\[
d_h:\mathcal R_{h+1}\to\mathcal R_h,\qquad
d_h(z_0,\ldots,z_{h+1})=(z_1,\ldots,z_{h+1})
\]
连续满射，并满足
\[
d_hZ_{h+1}=Z_hT,\qquad
\pi_hd_{h+1}=d_h\pi_{h+1}.
\]
因此逆极限上存在连续自映射 $\widehat T$，且它与 $T$ 共轭。另一方面，对任意固定 $h$，不存在单值映射 $A_h:\mathcal R_h\to\mathcal R_h$ 使
\[
A_hZ_h=Z_hT.
\]
对于同时保留当前列表 $Z_h$ 和一次删窗后的列表 $Z_hT$ 的指定任务，二者的联合纤维恰为 $Z_{h+1}$ 的纤维。具体地，$Z_{h+1}$ 有 $h+2$ 个坐标，索引为 $0,\ldots,h+1$，且
\[
(Z_h(\omega),Z_h(T\omega))
=\bigl((z_0,\ldots,z_h),(z_1,\ldots,z_{h+1})\bigr),
\qquad (z_0,\ldots,z_{h+1})=Z_{h+1}(\omega).
\]
因此 $\mathcal R_{h+1}$ 是这项配对响应任务的纤维商；这不使它成为可自主更新的有限层边界。

证明。映射
\[
J(\omega)=(Z_h(\omega))_{h\ge0}
\]
连续。若 $J(\omega)=J(\nu)$，则
\[
\Delta_{\sigma_n(\omega)}
=Z_{n+1}(\omega)_n-\gamma Z_{n+1}(\omega)_{n+1}
=Z_{n+1}(\nu)_n-\gamma Z_{n+1}(\nu)_{n+1}
=\Delta_{\sigma_n(\nu)}
\]
对所有 $n$ 成立，故 $\omega=\nu$。反之，给定逆极限中的相容族，集合
\[
C_h=\{\omega:Z_h(\omega)=b_h\}
\]
是非空闭集且递减；$A_0$ 是有限离散字母乘积中的紧闭子集，故 $\bigcap_hC_h$ 非空。于是 $J$ 满射；紧到 Hausdorff 的连续双射是同胚。$A_0$ 是紧、零维、无孤立点空间，故按 Cantor 空间刻画同胚于 Cantor 空间。$d_h$ 的等式由删去首窗口直接得出；任意 $\omega$ 可由 $\mathrm{null}\omega$ 前接，故满射，交换式给出逆极限上的 $\widehat T$。

最后，取命题14.8的 $a,b$，在前面各加 $h$ 个 $\mathrm{null}$，得到相同的 $Z_h$，而 $Z_hT$ 的末坐标分别为 $-1$ 和 $\phi$，故同层单值更新不存在。配对列表与 $Z_{h+1}$ 可按上式互相恢复，所以两者的相等关系完全一致。任何能解码这两个列表的摘要 $\eta$ 都满足 $\ker\eta\subseteq\ker Z_{h+1}$，因而在其实际像上有唯一满射到 $\mathcal R_{h+1}$，将 $\eta(\omega)$ 送到 $Z_{h+1}(\omega)$；反向 $Z_{h+1}$ 直接解码两列表。这是指定任务的集合论商最小性，不声称任意连续边界的最粗细化。证毕。

**命题 14.14（动态边界的普适性与资源界）。** 设 $B$ 为 Hausdorff 空间，$\eta:A_0\to B$、$f:B\to I_0$、$A:B\to B$ 满足
\[
\kappa_0=f\circ\eta,\qquad \eta\circ T=A\circ\eta.
\]
则 $\eta$ 必为单射。若 $\eta$ 连续，则它是 $A_0$ 到其像的同胚。不存在连续有限离散值记录 $r:A_0\to E$（$E$ 有限离散）使 $(\kappa_0,r)$ 单射。作为集合论对象，精确实数 $\kappa_0$ 加一个按双纤维选择的 Borel 端点位记录可以单射并携带传输后的集合论动力学。

证明。若 $\eta(\omega)=\eta(\nu)$，则对每个 $n$，
\[
\kappa_0(T^n\omega)=f(A^n\eta(\omega))
=f(A^n\eta(\nu))=\kappa_0(T^n\nu).
\]
定理14.11的递归差分恢复每个窗口，故 $\omega=\nu$。连续单射从紧空间到 Hausdorff 空间是到像的同胚。另一方面，每个非空合法柱集都可在其末状态后接 $3L$ 与 $\mathrm{null}R$，得到同一坐标的两条地址；若有限离散记录在某点连续，它必须在某个柱邻域常值，遂不能分离该碰撞。按每个双纤维任选一条地址的 Borel 选择，所得一位记录与实坐标联合后单射；它是端点集合上的记录，不能解释为有限精度存储或连续边界。证毕。

### 14.3 联合完成域与最小预测商

**命题 14.15（联合完成 $K=\Omega\times G$ 的预测商）。** 沿用本卷第3.1节和第5.2节的联合完成域
\[
K=\Omega\times G,\qquad
T_K(\omega,z)=\delta^3(\omega,z)
=\bigl(T\omega,M^{-3}(z-d_{\mathrm{first\ window}})\bigr).
\]
令 $\kappa_K(\omega,z)=\kappa_0(\omega)$。则对任意两点 $(\omega,z),(\nu,z')\in K$，
\[
\kappa_K(T_K^n(\omega,z))=\kappa_K(T_K^n(\nu,z'))
\ \forall n\ge0
\quad\Longleftrightarrow\quad
\omega=\nu.
\]
因此所有未来 $\kappa_K$ 响应的最小预测商是 $\Omega$，而不是 $K$；当前坐标的纤维为 $\kappa_0^{-1}(x)\times G$，完整未来的纤维为 $\{\omega\}\times G$。在实际有限图
\[
\Gamma=\{(\omega,g_\Gamma(\omega)):\omega\in D\}\subset K
\]
上，$\kappa_K$ 单射；若改用 $D\times G$，该单射性一般消失。

证明。$\kappa_K$ 只取地址坐标，故联合 $z$ 从所有未来响应中消失。若所有响应相同，定理14.11逐位恢复 $\omega$；反之同一 $\omega$ 对任意 $z,z'$ 给出同一响应。对当前时刻只需用定理14.7的纤维，再与 $G$ 作直积；全未来时地址被完全恢复而 $z$ 仍未被观察。$\Gamma$ 是图，且 $\kappa_0|_D$ 单射，故其限制单射；把图扩成 $D\times G$ 后，同一地址的不同 $z$ 重新进入同一观察纤维。证毕。

### 14.4 概率律、几乎处处因子与条件信息

**定理 14.16（左端律与平稳律的区间推前）。** 令 $\nu_{\mathrm{left}}$ 为本卷命题12.5的左端地址律，令 $\nu$ 为本卷定义9.1的平稳 Parry 律；两者都使用
\[
P=\begin{pmatrix}t&t^2\\1&0\end{pmatrix}.
\]
对长度为 $n$、末位为 $s\in\{0,1\}$ 的合法位柱，左端律满足
\[
\nu_{\mathrm{left}}([w])=t^{\,n+s}.
\]
若 $w$ 是长度为 $m$ 的窗口前缀、末状态为 $s$，则
\[
\nu_{\mathrm{left}}([w])
=|\gamma|^m t^s
=\frac{|I_w|}{\phi^2}.
\]
端点地址集合为可数集且两种律均给它零质量，从而
\[
(\kappa_0)_*\nu_{\mathrm{left}}
=\frac{1}{\phi^2}\,\mathrm{Leb}\!\restriction_{[-1,\phi]}.
\]
平稳律的初始分布为
\[
\pi=\frac{(\phi^2,1)}{\phi^2+1},
\]
其区间推前密度为
\[
\frac{d(\kappa_0)_*\nu}{dx}
=
\begin{cases}
\displaystyle\frac{\phi}{\phi^2+1},&-1<x<t,\\[5pt]
\displaystyle\frac{1}{\phi^2+1},&t<x<\phi.
\end{cases}
\]
左侧系数较大；端点处的密度值任意。

证明。对左端律，正向 Markov 连乘中 Perron 向量因子望远镜相消，得到 $t^{n+s}$。窗口柱的区间长度为 $|\gamma|^m|I_s|$，且 $|I_0|=\phi^2$、$|I_1|=\phi=\phi^2t$，故正好得到长度比。每层柱区间内部不交，端点至多两条编码；端点并为可数集，且每个单点柱质量随层数趋零，故端点质量为零。柱区间网格的最大长度趋零，按连续函数的区间逼近即得归一化长度测度。

平稳律的初始质量分别为 $\pi_0,\pi_1$。相对于左端律，首位为零、为一的密度比常数分别为
\[
\frac{\pi_0}{t}=\frac{\phi^3}{\phi^2+1},
\qquad
\frac{\pi_1}{t^2}=\frac{\phi^2}{\phi^2+1}.
\]
首位零的区间为 $[-1,t]$，首位一的区间为 $[t,\phi]$；乘以左端的均匀密度即得所列两段常密度。证毕。

**命题 14.17（分支逆变换、平稳性与来源律的区别）。** 在根接触点之外定义区间删窗
\[
f(x)=\frac{x-\Delta_\sigma}{\gamma}
\quad\text{当 }x\text{ 位于首窗 }\sigma\text{ 的内部}.
\]
在两个外端点使用唯一合法地址的后继值
\[
f(-1)=\phi,\qquad f(\phi)=-1.
\]
在每个内部根接触点，固定选择相邻两个首窗之一，并以该分支的逆公式定义 $f$ 的值。两个合法后继不同：若共同坐标为 $x$，它们分别为 $(x-\Delta_\sigma)/\gamma$ 与 $(x-\Delta_\tau)/\gamma$，而 $\Delta_\sigma\ne\Delta_\tau$。这样得到一个固定的 Borel 映射 $f:I_0\to I_0$。若以
\[
a=\frac{\phi}{\phi^2+1},\qquad b=\frac1{\phi^2+1},\qquad r=|\gamma|
\]
表示平稳推前的左右密度，则逆分支传递给下一次响应的密度为
\[
(a,b)\longmapsto\bigl(r(3a+2b),\,r(2a+b)\bigr)=(a,b).
\]
相反，左端律的均匀密度 $c=1/\phi^2$ 传递为
\[
\left(\frac{5r}{\phi^2},\,\frac{3r}{\phi^2}\right),
\]
故不平稳。端点选择不影响这两个测度论结论。

证明。目标落在 $(-1,t)$ 时，三个左侧空间分支 $3,\mathrm{null},5$ 和两个右侧空间分支 $2,25$ 都有原像；目标落在 $(t,\phi)$ 时，仅左侧的 $3,\mathrm{null}$ 与右侧的 $2$ 有原像。这里“左侧”指首位为零的空间块，不指窗口最高位。每个逆分支长度因子为 $r$，遂得矩阵式。代入 $t^3(3a+2b)=a$ 与 $t^3(2a+b)=b$（等价于 $\phi^4=3\phi+2$、$\phi^3=2\phi+1$）即得不变性。均匀左端密度对五个、三个逆分支分别求和，得到后一式。证毕。

**命题 14.18（固定选点的全时间条件与选点存在性）。** 固定命题14.17的 Borel 映射 $f$，令
\[
E_{\mathrm{root}}
=\kappa_0^{-1}\bigl(\{t-1,2t-1,t,2t\}\bigr),\qquad
E_f=\{\omega\in A_0:f(\kappa_0\omega)\ne\kappa_0(T\omega)\}.
\]
$E_{\mathrm{root}}$ 有八条地址；$E_f$ 在每个根接触二元纤维中恰含未被所选后继满足的一条地址，因而是其有限子集。对任意 Borel 地址概率律 $Q$，这个固定 $f$ 满足
\[
f^n\circ\kappa_0=\kappa_0\circ T^n
\quad Q\text{-几乎处处同时对所有 }n\ge0
\]
当且仅当
\[
Q\!\left(\bigcup_{n\ge0}T^{-n}E_f\right)=0.
\]
一步的 Borel 几乎处处因子存在，当且仅当每个内部根接触纤维的两条地址不同时具有正的 $Q$-质量。全时间同时成立的 Borel 因子存在，当且仅当这同一条件对
\[
\overline Q=\sum_{n\ge0}2^{-n-1}(T^n)_*Q
\]
成立。满足存在性时，可选命题14.17的分支公式及合法端点后继。非原子地址律是充分条件，但不是必要条件；特别地，$\nu_{\mathrm{left}}$ 和 $\nu$ 都满足全时间条件。

证明。根接触之外，唯一首窗的逆公式给出 $f(\kappa_0\omega)=\kappa_0(T\omega)$，两个外端点也由唯一地址给出这条等式。每个内部根接触的两首窗增量不同，所以两后继不同，固定选点恰满足其中一个；这说明 $E_f$ 的上述描述。

若 $\omega$ 避开 $\bigcup_{n\ge0}T^{-n}E_f$，则每个 $T^n\omega$ 都满足一步交换，归纳得到全部 $f^n(\kappa_0\omega)=\kappa_0(T^n\omega)$。反向，若同一 $\omega$ 满足所有时间等式，则相邻的第 $n$、第 $n+1$ 条给
\[
f(\kappa_0(T^n\omega))
=f(f^n(\kappa_0\omega))
=f^{n+1}(\kappa_0\omega)
=\kappa_0(T^{n+1}\omega).
\]
故 $T^n\omega\notin E_f$ 对所有 $n$ 成立。这证明固定 $f$ 条件的两方向，且使用的是同一个全测度集合。

若某根接触的两地址都具有正 $Q$-质量，任意单值 $f$ 在共同坐标上至多满足一个后继，故一步几乎处处关系不可能成立。反之，若不存在这样的二元纤维，在每个接触点选取具有正质量的地址的后继；若两者都为零质量，则任取一个合法后继。所得 $E_f$ 为零质量，给出一步因子。所有选择只修改有限多个点，所以 $f$ 仍为 Borel。

对固定 $f$，所有混合权重严格为正，故
\[
\overline Q(E_f)=0
\quad\Longleftrightarrow\quad
Q(T^{-n}E_f)=0\ \text{对每个 }n\ge0
\quad\Longleftrightarrow\quad
Q\!\left(\bigcup_{n\ge0}T^{-n}E_f\right)=0.
\]
因此对 $\overline Q$ 应用一步存在性判据即给全时间存在性的充分性。若任意 Borel 映射已给出全时间因子，相邻时间等式使它对每个 $(T^n)_*Q$ 都满足一步关系，也就对 $\overline Q$ 满足一步关系；上述二元纤维判据给必要性。混合律的零质量条件等价于逐点同时的全时间结论，并非仅仅一个平均时间结论。

每个 $T^n$ 的单点前像由长度 $n$ 的窗口前缀确定，故有限；于是 $\bigcup_{n\ge0}T^{-n}E_{\mathrm{root}}$ 可数。非原子律给它零质量，两种 Markov 律的非原子性已由定理14.16的柱质量证明。非原子性并非必要：取 $Q=\delta_{3L}$，并选 $f(t-1)=-1$。地址 $3L$ 的正时间轨道为 $L,R,L,R,\ldots$，其坐标为 $-1,\phi,-1,\phi,\ldots$，恰与 $f$ 的外端点更新相符。因此全时间关系成立，尽管 $Q(E_{\mathrm{root}})=1$。证毕。

**推论 14.19（逻辑非单射与平均条件信息）。** 对任意给每个地址单点质量为零的地址律，$\kappa_0$ 只有可数个二重纤维，故在去掉该可数集合后有 Borel 逆。若 $C$ 是由地址决定的有限可测标签，则
\[
H(C\mid \kappa_0)=0.
\]
另一方面，若概率律在某一内部根接触二元纤维的两条地址上各给正质量，则该纤维上的首窗口标签 $\sigma_0$ 的条件不确定度为正；等权二点根接触律给出一比特。对两地址也各有正质量的一般深层接触，须取两地址首次不同的窗口 $\sigma_k$：它在该纤维上具有正的条件不确定度，而当 $k>0$ 时两地址的首窗口相同，首标签在该纤维上的条件不确定度为零。因而“逻辑上非单射”“给定任务是否可预测”和“平均条件信息是否损失”是三个不同命题；不能用无限熵相减，也不能向地址外加入独立随机标签来改变它们。

证明。可数端点地址集合为零质量，Borel 逆在其补集上由有限柱嵌套给出，故任何有限地址可测函数由 $\kappa_0$ 几乎处处确定。若某接触纤维的两地址质量分别为 $p,q>0$，给定其共同坐标的条件分布为 $p/(p+q),q/(p+q)$。首次不同的窗口区分这两条地址，所以它在该纤维上的条件熵为 $h_2(p/(p+q))>0$，对平均条件熵贡献 $(p+q)h_2(p/(p+q))$；在等权二点来源律下此值为一比特。内部根接触的首次不同窗口是第零窗；深层接触在第 $k>0$ 窗才不同，故不能从其二重性推断首标签有不确定度。证毕。

### 14.5 结论范围

**命题 14.20（任务因子化与边界自主更新的条件）。** 在本章的 FIB 模型中，折叠把合法地址组织成实区间，并可把 interior 替换为针对已声明外部 continuation 任务的 response；递归删窗的一个时间步是三个地址位。对摘要 $\eta:A_0\to B$，所有指定任务响应可通过实际像 $\eta(A_0)$ 解码，当且仅当这些响应分别在每个 $\eta$ 纤维上恒定。若还要求边界自身具有自主更新 $A:\eta(A_0)\to\eta(A_0)$，则准确的额外条件是
\[
\eta(\omega)=\eta(\nu)
\quad\Longrightarrow\quad
\eta(T\omega)=\eta(T\nu).
\]
完整未来行为边界具有这一闭合性质；固定有限层 $Z_h$ 能解码其指定视界内的响应，却不具有同层自主更新。当前列表与一次删窗后列表的联合任务由 $Z_{h+1}$ 精确表示。全未来的 $\kappa_0$ 行为在 $A_0$ 上恢复完整地址；在联合完成域 $K$ 上，它只恢复 $\Omega$，仍不恢复独立的算术坐标 $G$。若改为区间上的全时间几乎处处更新，则须固定来源律和端点选点，并满足命题14.18的缺陷轨道零质量条件。

证明。任务响应在 $\eta$ 纤维上恒定时，按任意代表定义实际像上的响应，代表无关性给良定义；已有解码时，将同一个摘要代入即得纤维恒定性。自主更新的代表公式只能是 $A(\eta(\omega))=\eta(T\omega)$，它良定义恰等价于所列后继纤维条件。这分别复用基础卷 [FIB_RELATIONAL_CONTINUATION_GEOMETRY.md](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) 定义3.2–3.3的动态充分边界与行为商，不以静态任务因子化代替后继条件；有限视界的合同沿用其定义4.1。若 continuation 还包括自适应动作选择，则须保留 [RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) 定理3.3–3.4所要求的合法动作、共同记录及策略因子条件。

具体地，完整行为 $\mathcal B(\omega)=(\kappa_0(T^n\omega))_{n\ge0}$ 经 $T$ 更新就是删除其首坐标，所以相同行为必有相同后继行为；基础卷的行为商由此闭合。定理14.13说明其实际像与 $A_0$ 的地址等价，并给出每个固定有限层更新失败的同纤维见证；配对列表只给指定的当前与下一步列表，不赋予任一有限层自主更新。命题14.15给出联合完成 $K$ 的行为纤维为 $\{\omega\}\times G$，命题14.18给出区间因子的测度限定。共同边界替换还须保持命题14.4所用的同一实现与接缝约束，不能由分别可实现的响应自行拼成整体。五种窗口来自三位 guarded contract 的五个合法词，不能解释为五种普遍几何操作或五个盲方向。只有在声明了实际不可逆后处理、来源域和保留记录后，才可以谈时间箭头；有限性本身不推出遗忘。证毕。

相关图导向迭代函数系统的区间分割可与 Mauldin–Williams, “Hausdorff dimension in graph directed constructions”, *Transactions of the AMS* 309 (1988), 811–829, DOI:10.1090/S0002-9947-1988-0961615-4 对照；本章只使用其图导向编码的标准背景，具体端点、纤维、删窗和概率计算均由上述 FIB 数据给出。前述结论不声称物理空间或物理时间由折叠产生，也不声称有限精度、自动信息损失或新的优先性。

## 追加锚（本行以下为增补区）

## 15. 窗尺度下的 FIB 受控置换容量与外部记录

本章沿用第14章与母卷 [FIBONACCI_ATOMIC_RELATION_GENERATION.md](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §§150–151 的低位到高位窗口方向，把窗口长度推广为整数 $r\ge1$。所问的是：外部逐窗供给合法 FIB 命令时，一个有限的当前窗口读者能否用固定的置换分支跟随全部延续，以及内部状态和外部标签如何交换容量。它与第13章将来源一次初始化后自主运行的合同不同。

### 15.1 驱动合同与实际可达容量

**定义 15.1（当前窗口的受控置换读者）。** 令

$$
\Sigma_r=\{a=a_0\cdots a_{r-1}\in\{0,1\}^r:
 a_ja_{j+1}=0\ (0\le j<r-1)\},
\qquad \ell(a)=a_0,\quad h(a)=a_{r-1}.
$$

每个词从低位到高位书写。两窗的合法接缝为

$$
s\longrightarrow a\quad\Longleftrightarrow\quad h(s)\ell(a)=0.
$$

合法输入是任意无限序列 $(a_t)_{t\ge0}$，其中 $a_t\in\Sigma_r$ 且 $a_{t-1}\to a_t$ 对每个 $t\ge1$ 成立。任何有限合法窗口史都能后接全零窗而延成这样的输入。所有首窗均可初始化；没有另加的长度或 End 读出。

固定外部标签数 $k\ge0$，记 $\mathcal C_k=\{1,\ldots,k\}$，$k=0$ 时为空集。读者具有有限内部状态集 $E$、固定的全定义读出 $\eta:E\to\Sigma_r$、固定初始化 $i:\Sigma_r\to E$，以及对每个 $(a,c)\in\Sigma_r\times\mathcal C_k$ 固定的置换 $P_{a,c}:E\to E$。要求 $\eta i(a)=a$。成本是总状态数 $|E|$；机器、时钟、持续记忆及其他改变中的内部数据全部属于 $E$。

一套因果策略是对每个有限合法输入史给出下一标签的同一组规则。写成

$$
c_t=\tau_t(a_0,\ldots,a_t)\in\mathcal C_k,\qquad
 e_0=i(a_0),\qquad e_t=P_{a_t,c_t}(e_{t-1})\quad(t\ge1),
$$

并要求

$$
\eta(e_t)=a_t\qquad(t\ge0)
$$

对每条合法无限输入成立。策略不能读取尚未供给的命令，也不能为每条完整无限输入另选一套规则。必要性允许上述规则依赖整个已供给历史，包括由它确定的先前标签和状态；若选择器另有改变中的内部记忆，该记忆须并入 $E$。外部命令及所选标签是驱动资源，外部保存的历史也不冒充免费内部状态。以下充分构造只用当前 $e$ 与新命令 $a$ 选择标签，无须历史记忆。定义置换和选择器的静态表不增加改变中的状态。

正确性只约束这套策略实际选出的分支。令 $R\subseteq E$ 为它在所有有限合法输入史上实际到达的状态并集，$R_a=R\cap\eta^{-1}(a)$；不要求未选标签的像仍在 $R$ 中，也不要求那些像读出正确。这里的 $P_{a,c}$ 是当前窗口读者的状态置换，与定义14.1的组成仿射更新 $F_\sigma$ 没有预设的同一关系。

**定理 15.2（可达纤维判据与精确最小总状态）。** 在定义15.1的合同下，有限读者存在，当且仅当存在正整数向量 $(n_a)_{a\in\Sigma_r}$，满足

$$
\sum_{s\to a}n_s\le k n_a\qquad(a\in\Sigma_r).
\tag{15.1}
$$

每个满足此式的向量都能由一个总状态数 $\sum_a n_a$、各读出纤维大小恰为 $n_a$ 的读者实现。任意读者实际可达的纤维大小 $n_a=|R_a|$ 满足此式。因此，若记无实现时的最小值为 $+\infty$，精确最小成本为

$$
N_r(k)=\min\left\{\sum_{a\in\Sigma_r}n_a:
 n_a\in\mathbb Z_{>0},\ \sum_{s\to a}n_s\le k n_a\ \forall a\right\}.
\tag{15.2}
$$

必要性所用的 $n_a$ 是 $|R_a|$，不是未经证明便视作可达的整个 $|\eta^{-1}(a)|$。

证明。先设存在读者。每个初始化 $i(a)$ 都属于 $R_a$，故 $n_a\ge1$。固定目标窗 $a$。对每个 $e\in\bigcup_{s\to a}R_s$，固定选一条到达 $e$ 的有限合法见证史；其末窗为 $\eta(e)$。把 $a$ 接到这条史后，再补零延成无限输入，因果策略必选出某个标签 $c(e,a)$，且

$$
P_{a,c(e,a)}(e)\in R_a.
$$

映射 $e\mapsto(c(e,a),P_{a,c(e,a)}(e))$ 从上述并集到 $\mathcal C_k\times R_a$ 是单射：若两个像相同，标签相同，而同一 $P_{a,c}$ 是置换，故原状态相同。不同状态的见证史可以不同，同一状态在其他史上也可以选不同标签；固定一个见证已经足够。因此得到式（15.1），并有 $|E|\ge|R|=\sum_a n_a$。此处从未沿未选标签扩大 $R$。

反之，给定满足式（15.1）的正整数向量，取

$$
E=\{(a,j):a\in\Sigma_r,\ 1\le j\le n_a\},\qquad
E_a=\{(a,j):1\le j\le n_a\},\qquad
\eta(a,j)=a,\qquad i(a)=(a,1).
$$

固定 $E$ 的一个全序。对每个目标 $a$，将允许的源状态集

$$
D_a=\bigcup_{s\to a}E_s
$$

依序分为 $k$ 个块 $G_{a,1},\ldots,G_{a,k}$，每块至多 $n_a$ 个状态；空块允许存在。式（15.1）保证可以这样分块。把每块的第 $j$ 个状态送到 $(a,j)$，得到部分单射 $I_{a,c}:G_{a,c}\to E_a$。其定义域和像等势，故两个补集 $E\setminus G_{a,c}$ 与 $E\setminus I_{a,c}(G_{a,c})$ 也等势。按固定全序将这两个补集的第 $j$ 个元素配对，便将 $I_{a,c}$ 延成固定的全局置换 $P_{a,c}$；空块按同一规则延成恒等置换。

当 $\eta(e)\to a$ 时，选择包含 $e$ 的唯一块标签 $c$。于是 $\eta(P_{a,c}(e))=a$。从每个 $i(a_0)$ 出发归纳，即得同一套只依赖 $(e,a)$ 的策略对全部合法输入正确。补集延拓上的其他状态与未选标签没有读出要求。下界与此构造给出式（15.2）；当可行集合非空时，正整数总成本的良序性保证最小值取得。证毕。

### 15.2 两类容量、标签阈值与整数最优解

**命题 15.3（低位类最小化的精确约化）。** 沿用 $F_0=0,F_1=1$，在本章局部记

$$
A_r=F_{r+1},\qquad B_r=F_r,\qquad C_r=F_{r-1}.
$$

$\Sigma_r$ 中低位为零和为一的窗数分别为 $A_r,B_r$，所以不同窗口读出仍有 $F_{r+2}=A_r+B_r$ 个。所有最优容量向量都在各低位类内常值，分别记为正整数 $u,v$；精确优化为

$$
N_r(k)=\min_{u,v\in\mathbb Z_{>0}}
 \{A_ru+B_rv:
 ku\ge A_ru+B_rv,\quad kv\ge B_ru+C_rv\}.
\tag{15.3}
$$

两类是容量约束的约化，不是把所有窗口读出压成两个值；第14章按最高位分的后继许可类与这里按低位分的目标容量类也须区别。

证明。按 incoming guard 与新位的顺序 $0,1$，单个位的合法计数矩阵为

$$
Q=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Q^r=\begin{pmatrix}A_r&B_r\\B_r&C_r\end{pmatrix}\quad(r\ge1).
\tag{15.4}
$$

第一式的行是读入前的 guard，列是读入位；第二式由 Fibonacci 递推归纳得到，行表示 incoming guard，列表示窗口最高位。这个 $Q$ 使用接缝状态的次序，明确不同于本卷原组成矩阵 $M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$ 的组成坐标次序。母卷 §237 的三位接缝矩阵就是这里的 $Q^3$；计数对应不使状态置换等同于组成动作。

最低位固定为零时，余下 $r-1$ 位从 guard 零出发，数目为 $A_r$；最低位为一时，余下位从 guard 一出发，数目为 $B_r$。最低位已固定后，末位为零的两类数目是 $Q^{r-1}$ 的第零列，即 $B_r,C_r$。对于 $r=1$，这里使用 $Q^0=I$，直接得到窗 $0$ 与 $1$、相应数目 $A_1=B_1=1,C_1=0$，不用负指标 Fibonacci 数。

任取满足式（15.1）的向量，令 $u$ 为低位零类容量的最小值，$v$ 为低位一类容量的最小值，将该类所有容量分别降至 $u,v$。对低位零的目标，全部窗都是允许前驱；取原容量达到 $u$ 的目标，其原不等式给 $\sum_s n_s\le ku$，降低源容量后仍成立。对低位一的目标，允许前驱恰为最高位零的窗；取原容量达到 $v$ 的目标，其原不等式给 $\sum_{h(s)=0}n_s\le kv$，降低后同样成立。降低后的两个源和分别为 $A_ru+B_rv$ 与 $B_ru+C_rv$。于是约化保持整数性与可行性；若原向量在任一类中不常值，总成本严格下降。反之，式（15.3）的常值向量直接满足全部逐窗不等式。证毕。

**定理 15.4（外部标签数的精确阈值）。** 对每个 $r\ge1$，定义15.1的有限读者存在恰当且仅当

$$
k\ge\lceil\phi^r\rceil.
\tag{15.5}
$$

$k=0$ 时不存在策略；$r=1$ 时恰需 $k\ge2$，且所有可行 $k$ 都有 $N_1(k)=2$。

证明。设 $x=(u,v)^{\mathsf T}$ 是式（15.3）的正整数可行点。由于 $Q(\phi,1)^{\mathsf T}=\phi(\phi,1)^{\mathsf T}$ 且 $Q$ 对称，正行向量 $w=(\phi,1)$ 满足 $wQ^r=\phi^r w$。把 $Q^rx\le kx$ 左乘 $w$，得到 $\phi^r wx\le kwx$；$wx>0$，故 $k\ge\phi^r$。递推恒等式 $\phi^r=F_r\phi+F_{r-1}$ 与 $F_r\ge1$ 说明它是无理数，因此整数 $k$ 必严格大于 $\phi^r$，即满足式（15.5）。

反过来，设 $k\ge\lceil\phi^r\rceil$。由 $A_r=B_r+C_r$ 与 $\phi^r=B_r\phi+C_r$，有 $k>A_r\ge C_r$。$Q^r$ 的特征值为 $\phi^r,\psi^r$，其中 $\psi=-\phi^{-1}$，所以

$$
\Delta_r(k)=(k-A_r)(k-C_r)-B_r^2
 =(k-\phi^r)(k-\psi^r)>0.
$$

取整数点

$$
u=B_r,\qquad v=k-A_r.
$$

它的两个坐标为正，且

$$
ku-(A_ru+B_rv)=0,\qquad
kv-(B_ru+C_rv)=\Delta_r(k)>0.
$$

因此容量可行，定理15.2给出有限读者。$k=0$ 时，全零输入也需要在第一步选标签，而 $\mathcal C_0$ 为空，故直接不可能。$r=1$ 的两个容量约束为 $ku\ge u+v$、$kv\ge u$；$k\ge2$ 时 $(u,v)=(1,1)$ 可行，而两个不同初始化读出迫使至少两个状态，所以 $N_1(k)=2$。证毕。

**定理 15.5（有界单变量公式与唯一最优容量）。** 固定 $r\ge1$ 与可行的 $k\ge\lceil\phi^r\rceil$。令

$$
v_r(u;k)=\left\lceil\frac{B_ru}{k-C_r}\right\rceil,
$$

并定义

$$
\begin{aligned}
u_*&=\min\{u\in\{1,\ldots,B_r\}:
 B_rv_r(u;k)\le(k-A_r)u\},\\
v_*&=v_r(u_*;k).
\end{aligned}
\tag{15.6}
$$

此集合非空，且

$$
N_r(k)=A_ru_*+B_rv_*.
\tag{15.7}
$$

$(u_*,v_*)$ 是唯一的最优两类容量，全部逐窗最优容量也唯一：低位零类各为 $u_*$，低位一类各为 $v_*$。达到总成本最小值的读者必有 $R=E$，其实际读出纤维即具有这些容量；置换、初始化和策略本身不因此唯一。另有精确的单状态纤维判据

$$
N_r(k)=F_{r+2}\quad\Longleftrightarrow\quad k\ge F_{r+2}.
\tag{15.8}
$$

证明。定理15.4给 $k>C_r$ 及 $k>A_r$。对固定正整数 $u$，式（15.3）的第二个约束等价于

$$
v\ge v_r(u;k).
$$

$v_r(u;k)$ 为正整数，随 $u$ 非递减。第一个约束等价于 $B_rv\le(k-A_r)u$，故此 $u$ 存在可行的正整数 $v$，当且仅当

$$
B_rv_r(u;k)\le(k-A_r)u;
$$

若可行，最便宜且唯一最便宜的 $v$ 就是 $v_r(u;k)$。定理15.4的可行点 $(B_r,k-A_r)$ 说明 $u=B_r$ 满足这个判据，因此式（15.6）非空，最小可行正整数 $u$ 已在 $1\le u\le B_r$ 中取得。

函数 $g(u)=A_ru+B_rv_r(u;k)$ 严格递增，因为 $A_r>0$ 而第二项非递减。任何更大的可行 $u$ 成本都高于 $u_*$，任何在 $u_*$ 上更大的 $v$ 也增加成本。于是式（15.7）与两变量最优解的唯一性成立；命题15.3排除不常值的逐窗最优向量。若某个最小读者有不可达状态，定理15.2的可达容量向量就以 $|R|<|E|=N_r(k)$ 满足同一判据，矛盾，所以 $R=E$。

初始化覆盖每个不同窗口读出，故总成本至少为 $|\Sigma_r|=F_{r+2}$。若取等，每个可达纤维都只有一个状态；对任意低位零目标，式（15.1）遂给 $F_{r+2}\le k$。反之，当 $k\ge F_{r+2}=A_r+B_r$ 时，$(u,v)=(1,1)$ 可行：两个左侧源和分别为 $A_r+B_r$ 与 $B_r+C_r=A_r$。定理15.2的构造达到窗口数下界。证毕。

**定理 15.6（偶数窗最小标签的整格闭式）。** 设 $r\ge2$ 为偶数，令

$$
L_r=F_{r+1}+F_{r-1}=A_r+C_r.
$$

则 $L_r=\lceil\phi^r\rceil$ 是最小可行标签数，并且

$$
N_r(L_r)=F_{2r},\qquad (u_*,v_*)=(B_r,C_r).
\tag{15.9}
$$

这给出精确的正整数最优值与唯一容量，不只是实数松弛的最小值。

证明。$Q^r$ 的迹为 $L_r=\phi^r+\psi^r$；偶数 $r\ge2$ 时 $\psi^r=\phi^{-r}\in(0,1)$。所以整数 $L_r$ 严格位于 $\phi^r$ 与 $\phi^r+1$ 之间，正是其上取整。行列式恒等式给出 Cassini 关系

$$
A_rC_r-B_r^2=\det Q^r=1.
$$

在 $k=A_r+C_r$ 时，可行约束恰为 $C_ru\ge B_rv$ 与 $A_rv\ge B_ru$。因此定义

$$
\alpha=A_rv-B_ru\ge0,\qquad
\beta=C_ru-B_rv\ge0
$$

得到两个非负整数，并由 Cassini 关系直接相消得

$$
(u,v)=\alpha(B_r,C_r)+\beta(A_r,B_r).
\tag{15.10}
$$

反之，任意非负整数 $\alpha,\beta$、不同时为零，按式（15.10）得到正整数 $u,v$，且两个约束的余量恰为 $\alpha,\beta$；这里 $C_r\ge1$。因此式（15.10）完整描述可行正整数锥，而非只取它的实数边界。

将 $Q^{2r}=(Q^r)^2$ 的非对角元和左上角元比较，得到

$$
B_r(A_r+C_r)=F_{2r},\qquad
A_r^2+B_r^2=F_{2r+1}.
$$

故每个可行点的成本都是

$$
A_ru+B_rv=\alpha F_{2r}+\beta F_{2r+1}.
$$

$F_{2r+1}>F_{2r}>0$，且 $\alpha,\beta$ 是不同时为零的非负整数，所以唯一最小选择为 $\alpha=1,\beta=0$，成本为 $F_{2r}$，容量为 $(B_r,C_r)$。命题15.3进一步给出全部逐窗容量的唯一性。证毕。

### 15.3 三个精确容量及其固定置换构造

**命题 15.7（四位窗、七标签的二十一状态实现）。** 在定义15.1的合同下，

$$
N_4(7)=21.
$$

其唯一最优逐窗容量为：低位零的五个窗各三个状态，低位一的三个窗各两个状态。固定置换可用七个三元块与六个二元块加一个单元块构造。

证明。按低位到高位书写，两类字母为

$$
\begin{aligned}
\Sigma_4^{(0)}&=\{0000,0001,0010,0100,0101\},\\
\Sigma_4^{(1)}&=\{1000,1001,1010\}.
\end{aligned}
$$

取 $E_a=\{(a,1),(a,2),(a,3)\}$ 当 $\ell(a)=0$，取 $E_a=\{(a,1),(a,2)\}$ 当 $\ell(a)=1$；读出与初始化如定理15.2。以字母的固定字典序、再以副本指标递增给 $E$ 排序。

对于低位零目标 $a$，允许源状态是全部 $21$ 个状态；依序每三个分成一块，恰为七块。标签 $c$ 的第 $j$ 个源状态送到 $(a,j)$，$1\le j\le3$。对于低位一目标，允许前驱窗为

$$
\{0000,0010,0100,1000,1010\}.
$$

前三个低位零窗各有三个副本，后两个低位一窗各有两个副本，允许源状态共有 $3\cdot3+2\cdot2=13$ 个。依序把前十二个状态分成六对，第十三个单独作为第七块；每对的两个状态分别送到 $(a,1),(a,2)$，单元块送到 $(a,1)$。每个标签的部分单射都按定理15.2的有序补集配对延成全局置换。选择包含当前状态的块标签，就由同一套无历史记忆策略跟随每条合法输入。故这是一套实际的二十一状态构造，无须列出完整置换表。

下界由定理15.6取 $r=4$ 给出：$A_4=5,B_4=3,C_4=2,L_4=7$，所以任意读者至少需要 $F_8=21$ 个状态，最优容量只能为 $(3,2)$。构造与下界相合。证毕。

**命题 15.8（八状态与五状态的单纤维构造）。** 在同一合同下，

$$
N_4(8)=8,\qquad N_3(5)=5.
$$

两种情形都可取每个窗口读出一个状态，以固定换位实现全部合法输入。

证明。一般地，若 $m=|\Sigma_r|$ 且 $k=m$，取 $E=\Sigma_r$、$\eta=i=\operatorname{id}$，给字母固定编号 $c(s)\in\{1,\ldots,m\}$。对每个目标 $a$ 和源字母 $s$，定义 $P_{a,c(s)}$ 为交换 $s,a$ 的换位，$s=a$ 时为恒等置换。当前状态为 $s$ 且命令 $a$ 合法时选择标签 $c(s)$，所得状态就是 $a$；由归纳得到所有合法输入的正确读出。每个 $P_{a,c}$ 在整个 $E$ 上都是一个固定置换。

$r=4$ 时 $m=F_6=8$，所以该构造恰用八状态、八标签；八个不同初始化读出也给八状态下界。$r=3$ 时字母是第14章的 $\{000,100,010,101,001\}$，$m=F_5=5$，同一换位规则恰用五状态、五标签；五个初始化读出给五状态下界，且

$$
\phi^3=2+\sqrt5\in(4,5)
$$

说明五标签本身也是此尺度的精确最小值。证毕。

### 15.4 分支、反馈与保留标签的逆向恢复

**命题 15.9（最小的反馈合并反例）。** 每个固定分支 $P_{a,c}$ 是置换，并不推出因果选择后的状态更新单射。该区别已在 $r=1,k=2,|E|=2$ 的最小读者中出现。

证明。取 $E=\Sigma_1=\{0,1\}$、$\eta=i=\operatorname{id}$，令 $J$ 交换 $0,1$，并取四个固定分支

$$
P_{0,1}=\operatorname{id},\qquad P_{0,2}=J,\qquad
P_{1,1}=J,\qquad P_{1,2}=\operatorname{id}.
$$

当前状态为零时选标签一，为一时选标签二。命令零在两种当前状态下都合法，两种选定分支都读出零；命令一只能从当前零合法到达，所选 $J$ 读出一。因此同一策略对全部无相邻一输入正确，且各分支都是置换。但是固定到达命令零后的反馈更新为

$$
0\longmapsto P_{0,1}(0)=0,\qquad
1\longmapsto P_{0,2}(1)=0,
$$

所以遗忘标签后它合并两个不同前驱。两个初始化读出迫使至少两状态，定理15.4迫使至少两标签，此反例在这两项资源上均最小。证毕。

**命题 15.10（有序标签记录的精确恢复条件）。** 对定义15.1中任何正确的选定执行，若一步之后保留 $(e_t,c_t)$，就能唯一恢复该步命令 $a_t$ 与前一内部状态 $e_{t-1}$。更一般地，对任意有限长度 $H$ 的合法窗口史，最终状态 $e_H$ 连同全部有序标签记录 $(c_1,\ldots,c_H)$ 唯一恢复完整的窗口史 $(a_0,\ldots,a_H)$ 与内部状态史 $(e_0,\ldots,e_H)$。此条件不要求选择器无历史记忆，但只恢复本合同建模的数据。

证明。正确性给 $a_t=\eta(e_t)$，固定分支的可逆性给

$$
e_{t-1}=P_{\eta(e_t),c_t}^{-1}(e_t).
\tag{15.11}
$$

因此实际发生的一步没有第二个相容的前一状态或命令。对有限执行，从 $t=H$ 递减使用式（15.11），逐次得到 $e_{H-1},\ldots,e_0$；再读出 $a_t=\eta(e_t)$，包括初始化首窗 $a_0$。标签记录的顺序和长度是保留记录的一部分。$H=0$ 时直接由 $e_0$ 读出首窗。整个恢复不需要从当前状态重新计算曾经选过的标签，也不需要把外部命令史预先留下。

命题15.9说明删去标签记录时，即使前一状态只在两个初始化之间选择，也可能失去唯一恢复；相反，对任意预先固定的有限命令与标签列表，内部状态更新是固定置换的复合，仍为置换。后者保持的是同一外部驱动列表下的内部状态区别，不是不同输入史之间的区别。上述保留记录不恢复未建模的控制器数据、环境变量或原始树结构，也不给出完整历史记录的最小资源公式。证毕。

**命题 15.11（任意标签史合同的不可能性）。** 若将定义15.1加强为：对每条合法无限命令输入与每条任意标签序列都要求正确读出，则对任意 $r\ge1$ 和有限 $k$ 都不存在有限读者。这比在某一选定策略的可达集 $R$ 上要求未选标签也一步读对更强。

证明。$k=0$ 时没有标签序列可用于执行第一步，仍不能成为定义15.1的读者。设 $k\ge1$ 且存在加强后的读者。固定所有时刻都用标签一，则 $P_{a,1}$、原来的 $E,\eta,i$ 构成只有一个标签的读者，并对每条合法输入正确。定理15.4却要求至少 $\lceil\phi^r\rceil\ge2$ 个标签，矛盾。

此反证使用任意标签选择能够在全部时刻继续执行。若仅假设某一既定策略的 $R$ 上每个未选标签也有正确的一步读出，那些未选像仍可能落在 $E\setminus R$；这项一步假设没有保证后续未选步骤正确。因此不能把它未经证明当成任意标签史合同，也不能在定理15.2的下界中用它擅自扩张或闭合 $R$。证毕。

### 15.5 自主边界、尺度解释与文献背景

**命题 15.12（有限自主闭合与尺度的边界）。** 若将全部状态、控制器和时钟合成一个有限闭合系统，并要求其自主更新为一个固定置换，则任何固定初始化的窗口读出流都是周期流，因而不能产生全部合法 FIB 无限窗口流。定义15.1的受驱动读者可以用有限状态跟随全部合法流，精确条件是定理15.4，而这个结论不改变第13章的自主初始化模拟障碍。五个窗口和五个最小标签只在 $r=3$ 的本合同中相合，不能从中推出五种普遍观察或几何操作。

证明。设自主闭合系统为有限集 $E$ 上的置换 $P$ 与固定读出 $\eta$。任意初态 $e$ 属于某个有限周期，存在 $d\ge1$ 使 $P^de=e$，所以 $\eta(P^{t+d}e)=\eta(P^te)$ 对所有 $t\ge0$ 成立。合法流并不全是周期流：取全零窗 $z=0^r$ 与 $b=10^{r-1}$，只在窗口时刻 $2^j$（$j\ge1$）放 $b$，其余时刻放 $z$。$r=1$ 时一位窗彼此由至少一个零隔开；$r\ge2$ 时 $b$ 最高位为零，所有接缝也合法。$b$ 出现无限多次而间距无界，所以此流不可能周期。它因此不能由任何有限自主置换及固定读出产生。

受驱动合同每一步取得新命令，并依当前状态选外部标签，故不具备上述固定自主置换假设。命题15.9又说明，分支可逆性不能代替整个反馈更新的可逆性；命题15.10给出保留有序外部记录时的确切逆向恢复。第13章在一次初始化、固定自主置换与固定读出下的结论依然适用，不能用新命令与新标签消除那些前提中的资源限制。

在当前窗口任务中，不同读出数是 $F_{r+2}$，最小外部标签数是 $\lceil\phi^r\rceil$，总内部状态数是式（15.6）–（15.7）的整数值。$r=3$ 时前两者同为五且 $N_3(5)=5$；$r=4$ 时不同读出为八，最小标签为七，而 $N_4(7)=21$、$N_4(8)=8$。故“五”来自三位无相邻一窗口的尺度与任务合同，改变尺度会改变这些计数。

本章接到既有接缝响应边界所需的数学接口只是 $\Sigma_r$、合法关系 $s\to a$、标签数 $k$ 与当前窗读出 $\eta$；容量判据据此提供受控实现层。它既不把完整来源恢复纳入当前窗任务，也不把两个容量类替代为两个窗口读出。有限状态本身不迫使任意既定来源身份丢失，例如恒等置换永久保留有限来源；这里发生的合并须由实际的反馈选择、删去的标签记录或其他已声明投影来判定。各式是状态与标签的基数结论，没有假定概率律，也不提供物理熵、热量或时空起源的结论。证毕。

受限语言上的状态拆分与编码具有成熟背景，可参照 R. Adler、D. Coppersmith、M. Hassner，*Algorithms for sliding block codes – An application of symbolic dynamics to information theory*，*IEEE Transactions on Information Theory* 29(1) (1983), 5–22，[DOI:10.1109/TIT.1983.1056597](https://doi.org/10.1109/TIT.1983.1056597)。本章的具体容量方向、可达集下界、置换补集延拓和 Fibonacci 整数最优值由上述直接证明承担；这项引文只提供状态拆分与受限编码的背景，不把外部编码定理未经合同对应就转用于本章，也不主张这些推导的原创优先性。

## 追加锚（本行以下为增补区）

## 16. 实际边界记录的尖锐噪声阈值与有限量化预算

### 16.甲 模型、来源域与采样合同

**定义 16.1（有限前缀恢复与实际误差记录）。** 沿用定义14.5的合法地址域 $A_0=\Omega$、$A_1$、五窗图、区间 $I_0=[-1,\phi]$、$I_1=[-1,t]$ 及编码 $\kappa_s$。本章固定

$$
t=\frac{\sqrt5-1}{2},\qquad
\phi=1+t,\qquad
a=t^3=2t-1,\qquad
\gamma=-a=-t^3,\qquad
T=\sigma^3.
$$

一个时间步删除三个地址位。令 $b(\mathrm{null})=b(2)=b(3)=0$、$b(5)=b(25)=1$，其中 $b(\ell)$ 是窗口 $\ell$ 的输出 guard；起始 guard 为零时五窗都允许，起始 guard 为一时只允许 $\mathrm{null},3,5$。对 $y\in I_{b(\ell)}$ 置

$$
f_\ell(y)=\Delta_\ell-a y,\qquad
(\Delta_3,\Delta_{\mathrm{null}},\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t).
$$

母卷 [FIBONACCI_ATOMIC_RELATION_GENERATION.md](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §§150–151 与本卷命题14.6给出的实际分支区间为

$$
\begin{array}{c|cc}
\ell&\text{合法尾区间}&f_\ell(I_{b(\ell)})\\ \hline
3&I_0&[-1,t-1]\\
\mathrm{null}&I_0&[t-1,a]\\
5&I_1&[a,t]\\
2&I_0&[t,2t]\\
25&I_1&[2t,\phi].
\end{array}
$$

这些区间包含端点；每个合法尾区间内的点都由对应 guard 的某条实际合法地址取得。这里保持地址，不将共同区间端点的两条来源识别。外部单位位沿用定义1.1，固定为零；高位补零不产生独立长度或 End 读出。令 $D\subset\Omega$ 为最终全是 $\mathrm{null}$ 的地址，允许有限非零部分的长度任意大；$D$ 不是具有统一长度上限的有限码本。

固定整数 $h\ge1$，恢复目标为前 $h$ 个窗口

$$
W_h(\omega)=(\sigma_0(\omega),\ldots,\sigma_{h-1}(\omega)).
$$

实际取得的初始连续样本为

$$
z_j=\kappa_0(T^j\omega),\qquad 0\le j\le h,\qquad
Z_h(\omega)=(z_0,\ldots,z_h).
$$

它们来自同一地址的实际演化，并满足

$$
z_j+a z_{j+1}=\Delta_{\sigma_j(\omega)},\qquad 0\le j<h.
$$

对来源域 $X=\Omega$ 或 $D$，闭误差合同为 $\|r-Z_h(\omega)\|_\infty\le\varepsilon$，开误差合同为 $\|r-Z_h(\omega)\|_\infty<\varepsilon$。解码器只须在各合同的实际观察域上返回 $W_h(\omega)$；同一观察域中的所有相容来源必须给出同一前缀。闭合同取 $\varepsilon\ge0$，开合同取 $\varepsilon>0$。以下“统一恢复”指对域内全部来源和合同内全部误差正确，并不要求解码器连续。$h=0$ 的空前缀任务另行视为平凡任务。

### 16.乙 精确实值样本的分离与噪声阈值

**定理 16.2（不同前缀分量的全局最小分离）。** 对每个 $h\ge1$，固定合法前缀 $w$ 的响应集合是定理14.11中的闭仿射线段

$$
C_w=\left\{
\left(
\sum_{k=j}^{h-1}\gamma^{k-j}\Delta_{w_k}
+\gamma^{h-j}y
\right)_{j=0}^{h}
:y\in I_{s(w)}
\right\}.
$$

不同前缀分量的全局最小 $L^\infty$ 距离恰为

$$
\min_{w\ne v}\ \min_{z\in C_w,\ z'\in C_v}
\|z-z'\|_\infty=\frac t2.
$$

常值地址 $\mathrm{null}^{\infty}$ 与 $5^\infty$ 取得此最小值。限制为已知起始 guard 一时同一全局最小值仍成立；这两个地址从两种 guard 都合法。

证明。固定前缀后，末尾编码值遍历其实际末状态区间。逐次展开 $z_j=\Delta_{w_j}+\gamma z_{j+1}$ 即得线段公式；反向将任意合法末尾接回 $w$，说明该公式的每一点都实际可达。

五个平移量的严格递增次序为

$$
-t<0<t^2<1<2-t,
$$

相邻间隔为 $t,t^2,t,t^2$，最小间隔为 $t^2$。若 $w,v$ 在某个 $j<h$ 不同，记 $d_i=z_i-z'_i$、$M=\|z-z'\|_\infty$，则

$$
t^2\le|\Delta_{w_j}-\Delta_{v_j}|
=|d_j+a d_{j+1}|
\le(1+a)M=2tM.
$$

故 $M\ge t/2$，所有不同前缀的线段也包括端点在内互不相交。$\mathrm{null}^{\infty}$ 的每个坐标都是零，而 $5^\infty$ 的每个坐标都是

$$
\frac{t^2}{1+a}=\frac t2.
$$

两者前缀不同，所有坐标差均为 $t/2$，所以全局下界取得。它们也从 guard 一合法，故该限制域同样取得下界。这里没有断言任意两个分量间距都为 $t/2$；例如首窗分别为 $3$ 与 $25$ 时，平移差为 $2$，同一不等式给出距离至少 $2/(2t)=\phi$。证毕。

**定理 16.3（完整来源的尖锐闭误差与开误差阈值）。** 在完整来源域 $\Omega$ 上，从 $h+1$ 个实际样本的闭误差记录统一恢复 $W_h$，当且仅当

$$
\varepsilon<\frac t4.
$$

在正半径开误差合同下，统一恢复当且仅当

$$
0<\varepsilon\le\frac t4.
$$

闭合同严格低于阈值时，残差最近平移量解码器具有统一正判定余量

$$
m=\frac{t^2}{2}-2t\varepsilon
=2t\left(\frac t4-\varepsilon\right)>0.
$$

证明。对实际取得的误差记录计算

$$
d_j=r_j+a r_{j+1},\qquad 0\le j<h.
$$

若 $e_j=r_j-z_j$，则

$$
|d_j-\Delta_{\sigma_j}|
=|e_j+a e_{j+1}|
\le 2t\varepsilon.
$$

当 $\varepsilon<t/4$，右端严格小于最小平移间隔的一半 $t^2/2$，所以五个平移量中距 $d_j$ 最近的一个唯一且正是 $\Delta_{\sigma_j}$。到最近平移量判定边界的距离至少为 $m$，逐个 $j$ 解码便恢复完整目标前缀。

在开合同下，每个坐标误差严格小于 $\varepsilon$，故残差误差严格小于 $2t\varepsilon$；即使 $\varepsilon=t/4$ 也严格小于半间隔，因而恢复成立。对闭合同的 $\varepsilon=t/4$，常值观察

$$
r=\left(\frac t4,\ldots,\frac t4\right)
$$

同时与 $\mathrm{null}^{\infty}$、$5^\infty$ 相容，二者目标前缀不同。相同观察对更大的闭半径也相容；对 $\varepsilon>t/4$，它与两者的误差均严格小于半径，也否定开合同的统一恢复。这些常值见证从 guard 一仍合法，所以已知起始 guard 一的同类阈值相同。

严格闭阈值还允许有限精度的近似访问：若 $\rho>0$ 已知且 $\varepsilon+\rho<t/4$，用误差至多 $\rho$ 的有理数近似 $p_j$ 替代 $r_j$。在 $\mathbb Q(t)$ 内计算 $p_j+a p_{j+1}$，其总误差仍严格小于半间隔，所有比较均可有限完成。开合同临界处则有每份有限记录自身的严格余量，未给出对全部记录共同的正余量。证毕。

**定理 16.4（最终空尾来源的临界闭阈值与不连续性）。** 在 $D$ 上，不同 $W_h$ 的任意两个响应向量距离严格大于 $t/2$，但这些距离的下确界为 $t/2$。闭误差统一前缀恢复恰在

$$
0\le\varepsilon\le\frac t4
$$

成立。令 $c=t/4$，在临界闭误差的实际观察域

$$
\mathcal O_{D,h,c}
=\bigcup_{\omega\in D}
\{r:\|r-Z_h(\omega)\|_\infty\le c\}
$$

上，每个正确的前缀解码器都在 $r_*=c(1,\ldots,1)$ 不连续，其中前缀值域取离散拓扑。

证明。$t^2=1-t$ 使

$$
\mathbb Z[t]=\{m+nt:m,n\in\mathbb Z\}
$$

对加法、乘法封闭。每个 $D$ 坐标都是有限个 $\gamma$ 幂与平移量乘积的和，故属于 $\mathbb Z[t]$。由 $t$ 无理，

$$
\frac t2\notin\mathbb Z[t];
$$

否则 $t/2=m+nt$ 会强制 $m=0,n=1/2$，与整数系数矛盾。两个 $D$ 向量的最大坐标差由某一坐标取得，而该差的绝对值仍在 $\mathbb Z[t]$。定理16.2给出下界 $t/2$，环排除性使等号不可能，故距离严格大于 $t/2$。

若同一观察与两个不同前缀的 $D$ 来源都相容，三角不等式给出来源向量距离至多 $2\varepsilon$。在 $\varepsilon\le c$ 时这与严格距离矛盾。因此每个实际观察唯一决定目标前缀，按该前缀定义解码器便得到统一恢复；此处不要求相容的完整来源唯一。

取 $N>h$ 与

$$
\omega_N=5^N\mathrm{null}^{\infty}\in D.
$$

有限几何级数给出

$$
Z_h(\omega_N)_j
=\frac t2\left(1-\gamma^{N-j}\right),
\qquad 0\le j\le h.
$$

所以 $Z_h(\omega_N)$ 趋于常值向量 $(t/2,\ldots,t/2)$，它与零向量的距离趋于 $t/2$，且各 $N$ 的距离都严格大于 $t/2$。这证明下确界。对任何 $\varepsilon>c$，取足够大 $N$ 使该距离小于 $2\varepsilon$，则零向量与 $Z_h(\omega_N)$ 的中点同时落在二者的闭误差盒内，前缀分别为 $\mathrm{null}^h$ 与 $5^h$，所以统一恢复失败。

最后，$r_*$ 来自 $\mathrm{null}^{\infty}$ 加上每坐标误差 $c$，必须解码为 $\mathrm{null}^h$；而

$$
r_N=Z_h(\omega_N)-c(1,\ldots,1)
$$

来自 $\omega_N$ 加上每坐标误差 $-c$，必须解码为 $5^h$。两列均在 $\mathcal O_{D,h,c}$，且 $r_N\to r_*$，输出却不趋于 $r_*$ 的输出，故任何正确解码器在那里不连续。

临界前缀唯一不推出完整来源唯一。例如观察零向量同时与 $\mathrm{null}^{\infty}$ 和足够远处才出现一个 $5$ 的地址 $\mathrm{null}^M5\mathrm{null}^{\infty}$ 相容：后者在 $0\le j\le h<M$ 的坐标为 $\gamma^{M-j}t^2$，其最大绝对值可小于 $c$。两来源不同，但目标前缀都是 $\mathrm{null}^h$。证毕。

### 16.丙 临界代数系数合同与实数访问

**命题 16.5（临界等距规则及其表示前提）。** 在 $D$ 的闭临界合同 $\varepsilon=t/4$ 下，若每个 $r_j$ 以指定实嵌入中的精确元素

$$
r_j=p_j+q_jt,\qquad p_j,q_j\in\mathbb Q
$$

给出，且输入保证来自该合同，则存在有限的前缀解码算法。先计算 $d_j=r_j+a r_{j+1}$ 并选最近平移量。若最近值等距，则只能是 $(\mathrm{null},5)$ 或 $(2,25)$；对这两个按数值递增排列的候选，规则为

$$
\begin{array}{c|c}
\text{选择较低平移量}&r_j-t/4\in\mathbb Z[t]\\
\text{选择较高平移量}&r_j+t/4\in\mathbb Z[t].
\end{array}
$$

在合法输入保证下恰有一项成立。对一般实数的 Cauchy 近似访问，不存在在所有该合同观察及其所有合法名字上均停机、均正确的有限查询解码器。

证明。临界残差误差至多为

$$
(1+a)c=2t\frac t4=\frac{t^2}{2}.
$$

因此真实平移量必为最近者之一。最近值等距只发生在相邻平移量的中点；间隔 $t$ 的中点离两端均为 $t/2>t^2/2$，不符合保证，故只剩间隔 $t^2$ 的两对。

若较低平移量真实，达到中点需要

$$
e_j+a e_{j+1}=(1+a)c.
$$

由 $e_j,e_{j+1}\le c$ 与 $a>0$，等式等价于

$$
(c-e_j)+a(c-e_{j+1})=0,
$$

两项非负，故 $e_j=e_{j+1}=c$。于是 $r_j-c=z_j\in\mathbb Z[t]$。若较高平移量真实，同理负端极值迫使 $e_j=e_{j+1}=-c$，于是 $r_j+c\in\mathbb Z[t]$。两项不能同时成立，因为其差为 $t/2\notin\mathbb Z[t]$；合法输入又保证至少一项成立。无等距时最近值唯一，故上述规则逐窗正确。

精确系数下，

$$
r_j-c\in\mathbb Z[t]\iff p_j\in\mathbb Z,\ q_j-\frac14\in\mathbb Z,
$$

$$
r_j+c\in\mathbb Z[t]\iff p_j\in\mathbb Z,\ q_j+\frac14\in\mathbb Z.
$$

这些都是有限整数性判定。$\mathbb Q(t)$ 中的等式由基 $1,t$ 的唯一系数判定；序比较可将 $p+qt$ 写成 $(p-q/2)+(q/2)\sqrt5$，在有理部分与根式部分异号时比较其平方，同号时直接确定符号。$\sqrt5$ 无理保证除零元素外不会出现未决等号，故所有最近值比较亦有限完成。这里的算法使用输入保证，不承担验证整条来源或误差保证的任务；系数描述有限但长度无统一上界。

对 Cauchy 访问，设查询精度 $n$ 得到有理向量 $v_n$，满足 $\|v_n-r\|_\infty\le2^{-n}$。给 $r_*$ 选择一个每次误差都严格小于 $2^{-n}$ 的名字，有理数稠密性允许这样选择。假设某个正确算法在该名字上停机，它只用了有限次查询；所用答复到各自允许误差边界的余量有正的最小值。由定理16.4的 $r_N\to r_*$，足够大的 $N$ 使全部这些答复也都是 $r_N$ 的合法近似。将有限答复补全成 $r_N$ 的合法 Cauchy 名字，算法得到同一查询记录与同一输出，却必须分别返回 $\mathrm{null}^h$ 和 $5^h$，矛盾。精确代数系数提供的离散信息因此是额外的表示资源，不能由任意实数近似访问免费取得。证毕。

### 16.丁 有限颜色、连通格与等宽格

**定义 16.6（同一量化器的相邻对判据）。** 取一个固定函数

$$
Q:I_0\longrightarrow\{0,\ldots,q-1\}
$$

并删去未用颜色，记 $C_j=Q^{-1}(j)$。所有采样位置使用同一个 $Q$，准确记录实际坐标的颜色。对每个下一颜色 $j$ 和窗口 $\ell$ 定义当前颜色集合

$$
E_\ell(j)=
\{Q(f_\ell(y)):y\in C_j\cap I_{b(\ell)}\}.
$$

定义 $q_{\min}$ 为能够从相邻两个实际颜色统一恢复首窗的此类量化器最小非空颜色数。连通类要求每个 $C_j$ 在实直线上连通；等宽类要求 $I_0$ 分成 $q$ 个等长区间，每个内部切点归其左右某一格，两个外端点归端格。

**定理 16.7（相邻对充要判据与无约束下界）。** 从有序对 $(Q(z_0),Q(z_1))$ 在全部 $\Omega$ 上统一恢复首窗，当且仅当对每个下一颜色 $j$，五个集合 $E_\ell(j)$ 两两不交。满足判据时，每个实际有序对 $(i,j)$ 由

$$
i\in E_\ell(j)
$$

选择唯一窗口 $\ell$，于是 $h+1$ 个实际连续颜色恢复前 $h$ 窗。无正则性假设而满足首窗恢复合同的任意 $Q$ 均须满足 $q\ge5$。

证明。若 $i\in E_\ell(j)\cap E_{\ell'}(j)$ 且 $\ell\ne\ell'$，存在相应合法尾值 $y,y'$，二者下一颜色都是 $j$，两当前颜色都是 $i$。定义16.1的区间满像保证这些尾值由实际合法尾地址取得；从 guard 零分别前接 $\ell,\ell'$，就得到同一实际颜色对和两个不同首窗，解码不可能。

反之，实际有序对必在真实窗口的 $E_\ell(j)$ 中。两两不交保证没有第二候选，定义该对的解码值即可。对每个 $0\le k<h$ 应用于 $(Q(z_k),Q(z_{k+1}))$；每条移位后地址仍在 $A_0$ 中，即使其实际 incoming guard 为一，故同一判据逐窗适用。充要性是相邻对首窗任务的判据，并不把更长整段联合解码自动等同于此任务。

将五个窗口分别前接共同的实际尾 $\mathrm{null}^{\infty}$，下一坐标都是零、下一颜色都是 $Q(0)$，当前坐标依次为 $-t,0,t^2,1,2-t$。它们的当前颜色必须全部不同，故 $q\ge5$，这一步没有使用连通性。证毕。

**定理 16.8（六个连通格的构造与精确最小值）。** 以下六个混合端点归属的格满足定理16.7的判据：

$$
\begin{aligned}
C_0&=[-1,-1/2],&
C_1&=(-1/2,0],&
C_2&=(0,t/2],\\
C_3&=(t/2,3t/2),&
C_4&=[3t/2,2t],&
C_5&=(2t,\phi].
\end{aligned}
$$

以行标表示下一颜色、表内集合表示当前颜色时，完整解码表为：

| 六格下一颜色 | $E_3$ | $E_{\mathrm{null}}$ | $E_5$ | $E_2$ | $E_{25}$ |
| --- | --- | --- | --- | --- | --- |
| 六格色 $0$ | $\{0,1\}$ | $\{2\}$ | $\{3\}$ | $\{4\}$ | $\{5\}$ |
| 六格色 $1$ | $\{0\}$ | $\{1,2\}$ | $\{3\}$ | $\{4\}$ | $\{5\}$ |
| 六格色 $2$ | $\{0\}$ | $\{1\}$ | $\{2,3\}$ | $\{4\}$ | $\{5\}$ |
| 六格色 $3$ | $\{0\}$ | $\{1\}$ | $\{2\}$ | $\{3\}$ | $\{4,5\}$ |
| 六格色 $4$ | $\{0\}$ | $\{1\}$ | $\varnothing$ | $\{3\}$ | $\varnothing$ |
| 六格色 $5$ | $\{0\}$ | $\{1\}$ | $\varnothing$ | $\{3\}$ | $\varnothing$ |

连通纤维类的精确最小颜色数为六；对任意函数类，得到界

$$
5\le q_{\min}\le6.
$$

证明。$t$ 是 $x^2+x-1$ 的正根，该多项式在正轴严格递增。在 $3/5,5/8$ 的值分别为 $-1/25,1/64$，故

$$
\frac35<t<\frac58.
$$

负斜率分支将端点次序与开闭端反向。逐格得到下表，它列出完整的实际像区间；$5,25$ 两列始终先将尾格与 $I_1$ 相交。

| 六格尾区间 | $f_3$ 的像 | $f_{\mathrm{null}}$ 的像 | $f_5$ 的像 | $f_2$ 的像 | $f_{25}$ 的像 |
| --- | --- | --- | --- | --- | --- |
| 六格尾 $C_0$ | $[-1/2,t-1]$ | $[a/2,a]$ | $[1/2,t]$ | $[t+1/2,2t]$ | $[3/2,\phi]$ |
| 六格尾 $C_1$ | $[-t,-1/2)$ | $[0,a/2)$ | $[t^2,1/2)$ | $[1,t+1/2)$ | $[2-t,3/2)$ |
| 六格尾 $C_2$ | $[t/2-1,-t)$ | $[3t/2-1,0)$ | $[t/2,t^2)$ | $[3t/2,1)$ | $[1+t/2,2-t)$ |
| 六格尾 $C_3$ | $(7t/2-3,t/2-1)$ | $(9t/2-3,3t/2-1)$ | $[a,t/2)$ | $(9t/2-2,3t/2)$ | $[2t,1+t/2)$ |
| 六格尾 $C_4$ | $[5t-4,7t/2-3]$ | $[6t-4,9t/2-3]$ | $\varnothing$ | $[6t-3,9t/2-2]$ | $\varnothing$ |
| 六格尾 $C_5$ | $[-1,5t-4)$ | $[t-1,6t-4)$ | $\varnothing$ | $[t,6t-3)$ | $\varnothing$ |

例如 $f_3(-1/2)=-1/2$、$f_{\mathrm{null}}(0)=0$、$f_5(t/2)=t/2$、$f_2(t/2)=3t/2$ 与 $f_{25}(t)=2t$ 分别位于 $C_0,C_1,C_2,C_4,C_4$。尾格 $C_3$ 对 $5,25$ 的有效部分是 $(t/2,t]$，所以两像分别为 $[a,t/2)$ 与 $[2t,1+t/2)$；后者包含 $C_4$ 的端点 $2t$，也包含 $C_5$ 中的点。对窗口 $2$，尾格 $C_3$ 不包含 $t/2$，故像的上端 $3t/2$ 排除，整像留在 $C_3$。同样，$f_{\mathrm{null}}(C_1)$ 包含零及其右侧，$f_5(C_2)$ 包含 $t/2$ 及其右侧。这些端点归属正好给出表中的非单元素集合。

其余区间由 $3/5<t<5/8$ 与 $t^2=1-t$ 严格定位。例如 $0<a/2<a<t/2$、$t/2<t^2<1/2<t<3t/2<1$、$2t<1+t/2<2-t<3/2<\phi$；负半轴的像端点按各行所列次序落在 $C_0$ 或 $C_1$。像表中的每个区间都实际取得全部所列点，因此颜色表的每一项既无遗漏也没有虚增。每行五个集合两两不交，由定理16.7证明六格充分。

为证连通下界，取命题14.6的 $L=(3,25)^\infty$，它从 guard 一合法且编码为 $-1$；尾地址 $5L$ 从 guard 一合法且编码为 $t$。六个点严格递增：

$$
\begin{aligned}
x_1&=2t-2=f_3(t),&
x_2&=3t-2=f_{\mathrm{null}}(t),&
x_3&=a=f_5(t)=f_{\mathrm{null}}(-1),\\
x_4&=t=f_5(-1),&
x_5&=2t=f_2(-1),&
x_6&=\phi=f_{25}(-1).
\end{aligned}
$$

分别前接 $3,\mathrm{null},5$ 到共同实际尾 $5L$，强制 $x_1,x_2,x_3$ 的颜色两两不同；前接 $\mathrm{null},5,2,25$ 到共同实际尾 $L$，强制 $x_3,x_4,x_5,x_6$ 的颜色两两不同。因此六点列表中任意相邻点颜色不同。实直线的连通子集必包含其任意两点之间的点；若 $x_i,x_k$ 在同一连通纤维且 $i<k$，当 $k=i+1$ 直接矛盾，当 $k>i+1$ 则同一纤维也包含 $x_{i+1}$，仍矛盾。故六点全部颜色不同，连通类至少六色。与构造合并得到精确最小值六；无约束类的上界也由同一构造取得，下界由定理16.7取得。连通下界中的区间包含步骤只适用于连通纤维。证毕。

**定理 16.9（等宽量化的精确最小值八）。** 等宽类的最小颜色数恰为八。取

$$
u(x)=\frac{8(x+1)}{\phi^2},\qquad
Q_8(x)=
\begin{cases}
\lfloor u(x)\rfloor,&0\le u(x)<8,\\
7,&u(x)=8.
\end{cases}
$$

所有内部切点归右格，右外端点 $\phi$ 归最后一格。其相邻对的完整表为：

| 八格下一颜色 | $E_3$ | $E_{\mathrm{null}}$ | $E_5$ | $E_2$ | $E_{25}$ |
| --- | --- | --- | --- | --- | --- |
| 八格色 $0$ | $\{1\}$ | $\{3\}$ | $\{4\}$ | $\{6\}$ | $\{7\}$ |
| 八格色 $1$ | $\{1\}$ | $\{3\}$ | $\{4\}$ | $\{6\}$ | $\{7\}$ |
| 八格色 $2$ | $\{1\}$ | $\{3\}$ | $\{4\}$ | $\{6\}$ | $\{7\}$ |
| 八格色 $3$ | $\{0,1\}$ | $\{2,3\}$ | $\{4\}$ | $\{5,6\}$ | $\{7\}$ |
| 八格色 $4$ | $\{0\}$ | $\{2\}$ | $\{3,4\}$ | $\{5\}$ | $\{6,7\}$ |
| 八格色 $5$ | $\{0\}$ | $\{2\}$ | $\varnothing$ | $\{5\}$ | $\varnothing$ |
| 八格色 $6$ | $\{0\}$ | $\{2\}$ | $\varnothing$ | $\{5\}$ | $\varnothing$ |
| 八格色 $7$ | $\{0\}$ | $\{1,2\}$ | $\varnothing$ | $\{4,5\}$ | $\varnothing$ |

证明。先证明八格充分。若下一标准化坐标为 $v=u(y)$，当前标准化坐标的五个公式依次为

$$
u(f_3(y))=a(8-v),\qquad
u(f_{\mathrm{null}}(y))=a(16-v),
$$

$$
u(f_5(y))=4+a(4-v),\qquad
u(f_2(y))=4+a(12-v),\qquad
u(f_{25}(y))=8-av.
$$

尾区间为 $I_0$ 的三个窗口 $3,\mathrm{null},2$ 使用 $0\le v\le8$；窗口 $5,25$ 使用

$$
0\le v\le8t=4+4a.
$$

这里的尾区间区别由输出 guard 决定。$a$ 满足 $a^2+4a=1$，且

$$
\frac3{13}<a<\frac14.
$$

后者由 $x^2+4x-1$ 在 $3/13,1/4$ 的值分别为 $-4/169,1/16$ 及正轴递增性得到。它给出完整整数定位：

$$
\begin{array}{c|c}
1\le n\le4&0<na<1\\
5\le n\le8&1<na<2\\
9\le n\le12&2<na<3\\
13\le n\le16&3<na<4.
\end{array}
$$

记五个公式的常数项分别为 $c_\ell=8a,16a,4+4a,4+12a,8$。对未受 guard 截断的下一格 $J_j=[j,j+1)$，$0\le j\le6$，完整像为

$$
(c_\ell-a(j+1),c_\ell-aj];
$$

最后下一格 $J_7=[7,8]$ 的像为 $[c_\ell-8a,c_\ell-7a]$。上述整数定位逐行给出 $3,\mathrm{null},2$ 三列。例如下一格 $3$ 的三像分别为 $(4a,5a]$、$(12a,13a]$、$(4+8a,4+9a]$，分别跨越整数 $1,3,6$，得到 $\{0,1\},\{2,3\},\{5,6\}$。最后下一格的三像为 $[0,a]$、$[8a,9a]$、$[4+4a,4+5a]$，得到 $\{0\},\{1,2\},\{4,5\}$。其余下一格的各像两端处于同一整数格，恰为表中单元素集合。

对受限窗口，$4<4+4a<5$，所以只有下一格 $0,\ldots,4$ 可达。窗口 $5$ 在前四格的像分别为

$$
(4+3a,4+4a],\quad
(4+2a,4+3a],\quad
(4+a,4+2a],\quad
(4,4+a],
$$

全部为当前颜色 $4$。窗口 $25$ 的对应像为

$$
(8-a,8],\quad(8-2a,8-a],\quad
(8-3a,8-2a],\quad(8-4a,8-3a],
$$

全部为当前颜色 $7$，其中 $8$ 按定义归颜色 $7$。受限的下一格 $4$ 是闭区间 $[4,4+4a]$，其两个像由 $a^2+4a=1$ 化成

$$
[16a,4],\qquad [4+12a,8-4a].
$$

它们分别给出 $\{3,4\}$ 与 $\{6,7\}$。特别地，窗口 $5$ 在 $v=4$ 时的当前值 $4$ 归颜色 $4$，窗口 $3$ 在 $v=8$ 时的当前值零归颜色零；所有内部整数切点以及两个外端点都被保留。每个像都由实际合法尾取得，每行五集合两两不交，因此八格满足判据。

再证等宽下界。至多五格均为连通纤维，已由定理16.8排除；这一步使用连通下界，而非仅使用无约束的五色下界。六等宽格的最后内部切点为

$$
d_5=-1+\frac{5(2+t)}6=\frac{4+5t}{6}.
$$

由 $t>3/5>4/7$ 得 $d_5<2t<\phi$。共同实际尾 $L$ 的编码为 $-1$，两个合法来源 $2L$、$25L$ 的当前值分别为 $2t,\phi$，同在最后一格，下一值完全相同。因此六格失败，与内部切点归属无关。

对七等宽格，置 $d_k=-1+k(2+t)/7$。合法常值尾 $P_3=3^\infty$ 的编码为 $-t/(1+a)=-1/2$，故来源

$$
\omega=2\,5\,P_3,\qquad
\nu=25\,5\,L
$$

的实际相邻坐标分别为

$$
(z_0,z_1)=\left(\frac32-t,\frac12\right),
\qquad
(z'_0,z'_1)=(2t,t).
$$

合法性由 $2:0\to0$、$25:0\to1$、$5:0\to1$ 或 $1\to1$、$3:1\to0$ 及 $L$ 从 guard 一合法直接检查。由 $1/2<t<5/8$，

$$
d_4<\frac12<t<d_5,\qquad
d_5<\frac32-t<2t<d_6.
$$

其中 $d_4<1/2$、$d_5<3/2-t$、$2t<d_6$ 各自化为 $t<5/8$；$t<d_5$ 化为 $2t<3$，$3/2-t<2t$ 化为 $t>1/2$。因此两来源都产生当前颜色 $5$、下一颜色 $4$，首窗却为 $2,25$。四个坐标都严格位于相应格内部，任何内部切点归属都不能修复该碰撞。六、七格失败与八格构造合并，证明等宽类精确最小值八。证毕。

### 16.戊 实际取得的数量、存储与噪声合同

**定理 16.10（初始连续取得的尖锐数量与固定时刻集的界限）。** 为在全部 $\Omega$ 上统一恢复前 $h\ge1$ 窗，$h+1$ 个初始连续实际坐标充分，而只有 $h$ 个不足，即使每个坐标都是精确实数。上述六格或八格量化器也以 $h+1$ 个初始连续颜色恢复该前缀。任何预先固定的有限非负整数采样时刻集，都不能从其精确坐标恢复全部完整无限来源。

证明。充分性由定理16.3的零误差解码或定理16.7的相邻对解码得到。为证不足，取

$$
\alpha_h=\mathrm{null}^{h}L,\qquad
\beta_h=\mathrm{null}^{h-1}5\,5\,L.
$$

两来源合法，目标位置 $h-1$ 的窗分别为 $\mathrm{null}$ 与 $5$。在该位置两尾的编码相同，因为

$$
\kappa_0(\mathrm{null}L)=f_{\mathrm{null}}(-1)=a,
\qquad
\kappa_0(5\,5L)=f_5(t)=a.
$$

于是 $0\le j<h$ 的实际坐标完全相同：

$$
\kappa_0(T^j\alpha_h)
=\kappa_0(T^j\beta_h)
=\gamma^{h-1-j}a.
$$

任意后处理或精确量化都无法区分这 $h$ 个相同输入，故 $h$ 个初始连续取得不足。

对固定有限时刻集 $F$，若 $F$ 非空，取 $h>\max F$，则同一对 $\alpha_h,\beta_h$ 在 $F$ 的全部精确坐标相同，而完整地址不同；$F$ 为空时不足显然。因此否定的是固定有限时刻集的完整来源恢复，不涉及其他自适应且无统一取得次数上限的协议。证毕。

**命题 16.11（两种明确方案的零额外噪声余量）。** 定理16.8的六格方案与定理16.9的八格方案，在量化前允许任意逐坐标加性误差时，都没有正的统一额外误差容限；即使取得无限多个颜色也不能消除各自的碰撞。

证明。$\mathrm{null}^{\infty}$ 与 $5^\infty$ 的每个实际坐标分别为零与 $t/2$。六格方案中，精确颜色分别恒为 $1,2$。对任意提出的正容限 $\eta$，选

$$
0<\delta<\min\{\eta,t/2\}.
$$

将 $\mathrm{null}^{\infty}$ 的每个实际样本都读为 $\delta$，颜色便恒为 $2$，与零误差的 $5^\infty$ 全部记录相同，首窗却不同。

八格方案中，

$$
u(0)=4-4a\in(3,4),\qquad u(t/2)=4.
$$

所以精确颜色分别恒为 $3,4$。选

$$
0<\delta<\min\{\eta,\phi^2/8\},
$$

将 $5^\infty$ 的每个样本读为 $t/2-\delta$，标准化值严格落在 $(3,4)$，颜色便恒为 $3$，与零误差 $\mathrm{null}^{\infty}$ 的全部记录相同。两种碰撞的误差任意小且所有读数仍在 $I_0$ 内，故对无限记录也成立。结论分别属于这两个指定量化器，不转用于任意其他六色或八色方案。证毕。

**定理 16.12（截断到区间的九格中点方案与正余量）。** 将 $I_0$ 分成九个等宽格，内部切点归右格，外端点归端格；记格宽、格中点及截断映射为

$$
w_9=\frac{\phi^2}{9},\qquad
m_k=-1+\left(k+\frac12\right)w_9,\quad 0\le k\le8,
$$

$$
P(x)=\min\{\phi,\max\{-1,x\}\}.
$$

对 $x\in I_0$，量化器具体为 $Q_9(x)=\lfloor9(x+1)/\phi^2\rfloor$（$x<\phi$），并置 $Q_9(\phi)=8$。

实际样本 $z_j$ 先取得近似值 $s_j$，满足 $|s_j-z_j|\le\eta$，再记录 $P(s_j)$ 的九格颜色。若接收端使用对应中点的数值 $\widehat z_j$，额外的中点数值求值误差满足

$$
|\widehat z_j-m_{Q_9(P(s_j))}|\le\xi,
$$

则充分的统一合同为

$$
\eta+\xi<g_9,\qquad
g_9=\frac t4-\frac{\phi^2}{18}
=\frac{7t-4}{36}>0.
$$

在此合同下，$h+1$ 个九值记录恢复全部 $\Omega$ 来源的前 $h$ 窗，包括所有合法端点。$\xi$ 是格中点半宽之外的额外数值误差。

证明。真值 $z_j\in I_0$ 时，逐一考虑 $s_j<-1$、$s_j\in I_0$、$s_j>\phi$，均有

$$
|P(s_j)-z_j|\le|s_j-z_j|\le\eta.
$$

截断后的读数与其格中点距离至多为格半宽，包括外端点。因此

$$
|\widehat z_j-z_j|
\le\eta+\frac{\phi^2}{18}+\xi
<\frac t4.
$$

将 $\widehat z_j$ 代入定理16.3的残差最近平移量解码即可恢复每个窗。正性由 $t>3/5>4/7$ 得到。半宽项 $\phi^2/18$ 已完整计入格内重构误差，不能再次当作 $\xi$ 添加；若某个合同改将 $\xi$ 定义为全部中点重构误差，则相应充分式应写为 $\eta+\xi<t/4$。

有限近似访问也能实际使用该方案。取得有理近似 $s_j$ 并将其误差计入 $\eta$；截断值及九格切点均可在 $\mathbb Q(t)$ 中有限比较，因而可以量化取得的近似读数。若真实 $z_j$ 恰为切点，近似读数可落在任一侧，前述总误差界仍成立，不必决定真实样本的精确格归属。接收端可以使用精确代数中点，或在已知严格剩余余量内作有限数值求值并计入 $\xi$。九格在此只提供充分构造与所列严格误差界，未给出抗噪量化器的最小格数或最优误差容限。证毕。

**命题 16.13（记录成本、不可见因子与自主更新界限）。** 当 $h$ 与采样顺序已由合同给定时，保存全部 $h+1$ 个六值或八值记录可用 $3(h+1)$ 个固定位，保存全部九值记录可用 $4(h+1)$ 个固定位。这些是指定记录的定长存储上界。有限颜色的固定数量记录不能标识 $D$ 中所有完整来源；地址观察在 $\Omega\times G$ 上也不能恢复独立的 $G$ 坐标。任何满足定理16.7的有限颜色量化器，都不存在对全部来源成立的自主颜色更新函数 $A$ 使

$$
Q(\kappa_0(T\omega))=A(Q(\kappa_0(\omega))).
$$

证明。六与八个符号均可单射编码到三个位，九个符号可单射编码到四个位，按时间次序保存全部取得记录即得上界。若在内部保存 $h$、采样计数器、控制状态或解码后的前缀，其存储也属于总内部状态，不能从上述“指定记录”上界中删去；若这些参数或命令逐次由外部给定，它们是外部资源，不能因此宣称取得记录的装置自主。逐对解码可只暂存两个相邻颜色，但任何另行保留的历史记录仍须计入存储。这些上界不宣称最优码率或完整装置的最小状态数。

任意固定 $N$ 个 $q$ 值记录至多有 $q^N$ 个不同列表，而 $D$ 含无穷多个不同地址 $\mathrm{null}^M5\mathrm{null}^{\infty}$，所以这些列表不能标识全部完整来源。这是有限值记录的基数结论；它不否定带有无界系数描述长度的精确代数实数记录在其他合同中的单射性。

在乘积 $\Omega\times G$ 上，全部样本只依赖地址 $\omega$，所以 $(\omega,g)$ 与 $(\omega,g')$ 对任意 $g,g'$ 都有同一记录。无观察 $G$ 的合同便不能恢复该独立因子。对于仅投影到 $D$ 的图域，阈值由其实际地址投影决定，不能把有限来源的临界闭阈值转移到全 $\Omega$ 完成域。

若存在所列自主颜色更新 $A$，初始颜色 $i$ 会决定整条颜色流 $i,A(i),A^2(i),\ldots$。相邻对解码又从这条流决定全部地址窗口，于是最多 $q$ 条完整地址，矛盾于 $\Omega$ 包含无穷多个不同合法地址。精确标量也已有命题14.8的同坐标异后继障碍。即使窗口另由外部供给，从一个带误差的初始坐标按

$$
z_{j+1}=\frac{z_j-\Delta_{\sigma_j}}{\gamma}
$$

递推，初始误差大小仍逐步放大为 $a^{-j}|e_0|$，不自动给出这里要求的统一精度未来样本。

本章的五窗来自既定三位合法词与 guard，六格与八格最小值来自各自测量类的约束。它们不建立五窗与五种几何操作或五个盲方向的对应；预先定义的实区间、时钟及地址模型也不由这些解码结论推出物理空间、物理时间或物理起源。精确实数样本与有限颜色记录承担不同的资源合同。证毕。

### 16.己 数学引用

本章的 FIB 分支数据使用母卷 [FIBONACCI_ATOMIC_RELATION_GENERATION.md](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §§150–151；合法满像、极值尾和响应线段使用本卷定义14.5、命题14.6及定理14.11。全部具体分离常数、临界环判定、格表与下界见证由本章证明给出。

有限字母的零误差区分与半最小距离解码具有经典背景，可参照 F. J. MacWilliams and N. J. A. Sloane, The Theory of Error-Correcting Codes, North-Holland, 1977；Cauchy 名字与连续可计算性的背景可参照 K. Weihrauch, Computable Analysis: An Introduction, Springer, 2000。这里不将外部编码定理直接转用于实区间分量，也不依赖外部定理替代命题16.5的有限查询反证；这些引用只提供方法背景，不构成原创优先性断言。

## 追加锚（本行以下为增补区）

## 17. 同一 Borel 五色观察的实际相邻解码

### 17.甲 闭分支与实际地址合同

**定义 17.1（五标签的精确相邻观察）。** 沿用定义14.5的地址域 $A_0=\Omega$、$A_1=\{\omega\in\Omega:\omega_0=0\}$、区间编码 $\kappa_s$ 及三位删除 $T=\sigma^3$。本章置

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad \gamma=-g,
$$

$$
X=I_0=[-1,\phi],\qquad I=I_1=[-1,t],\qquad O=[t,\phi].
$$

这里 $I\cap O=\{t\}$，同一个标量 $t$ 不拆成两个副本。标签集按空间顺序记为 $\Lambda=\{3,0,5,2,25\}$，其中 $0=\mathrm{null}=000$，$25$ 是一个窗口标签 $[2\ 5]=101$；五标签的三位词依次为 $010,000,001,100,101$。$0$ 不是额外的第六个符号。令

$$
f_a(y)=\Delta_a-gy,\qquad
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t).
$$

标签 $3,0,2$ 的合法尾域为 $X$，标签 $5,25$ 的合法尾域为 $I$。每个分支的图都保留闭域的全部端点。精确相邻观察合同要求所有采样位置使用同一个单值函数 $Q:X\to\mathcal C$；一个实际地址的首窗为 $a$ 时，解码输入为

$$
\bigl(Q(\kappa_0(\omega)),Q(\kappa_0(T\omega))\bigr).
$$

若 $\mathcal C=\{1,2,3,4,5\}$，固定解码器 $D:\mathcal C^2\to\Lambda$ 如下，行是当前颜色，列是下一实际样本的颜色。

| 解码器 $D$ 的当前颜色 | 下一色 $1$ | 下一色 $2$ | 下一色 $3$ | 下一色 $4$ | 下一色 $5$ |
| --- | --- | --- | --- | --- | --- |
| 五色当前 $1$ | $0$ | $0$ | $0$ | $3$ | $0$ |
| 五色当前 $2$ | $5$ | $5$ | $5$ | $0$ | $3$ |
| 五色当前 $3$ | $3$ | $3$ | $3$ | $5$ | $2$ |
| 五色当前 $4$ | $25$ | $25$ | $25$ | $2$ | $3$ |
| 五色当前 $5$ | $2$ | $2$ | $2$ | $25$ | $2$ |

目标是同时满足

$$
D\bigl(Q(f_a(y)),Q(y)\bigr)=a
\qquad\text{对每个合法的 }(a,y).
$$

**定理 17.2（闭分支合同与实际来源的共同实现）。** 定义17.1的每条合法分支边 $(f_a(y),y)$ 都由某条从 guard 零出发的实际地址取得；每条实际相邻样本边又属于其中一个合法分支。因此对全部合法闭分支验证解码等式，恰好验证了全部 $\Omega$ 实际地址的相邻解码合同。

证明。定义14.5、命题14.6及定义16.1给出

$$
\kappa_0(A_0)=X,\qquad \kappa_1(A_1)=I,
$$

以及合法前接后的等式

$$
\kappa_0(a\eta)=\Delta_a-g\kappa_{b(a)}(\eta),\qquad
b(3)=b(0)=b(2)=0,\quad b(5)=b(25)=1.
$$

两种状态的编码使用同一个窗口级数，故当 $\eta\in A_1\subset A_0$ 时，$\kappa_1(\eta)=\kappa_0(\eta)$。

满像关系也可直接由这些闭分支核对。状态零的五个像依次为

$$
[-1,-t^2],\quad[-t^2,g],\quad[g,t],\quad[t,2t],\quad[2t,\phi],
$$

它们覆盖 $X$；状态一的合法首窗 $3,0,5$ 的像是前三段，覆盖 $I$。给定状态 $s$ 及 $x_0\in I_s$，在该状态的合法分支中取空间位置最右的一个包含 $x_0$ 的分支，令 $x_1$ 为其合法尾值，再对尾状态重复。这样得到合法标签 $a_0,a_1,\ldots$ 和一致的尾状态，不需要为轨道组件选代表。对每个 $N\ge1$，仿射等式给出

$$
x_0=\sum_{j=0}^{N-1}(-g)^j\Delta_{a_j}+(-g)^N x_N.
$$

所有 $x_N$ 都在有界区间 $X$ 内，且 $0<g<1$，故余项趋于零。拼接这些三位合法词便得到从状态 $s$ 出发的地址，其编码是 $x_0$。这证明满像关系，且不识别同坐标的不同地址。

现在给定合法 $(a,y)$。按满像关系取 $\eta\in A_{b(a)}$ 编码为 $y$，从 guard 零前接 $a$，接缝合法。来源 $a\eta$ 的当前值是 $f_a(y)$，三位删除后的实际值是 $y$。反过来，任意实际地址分解为首窗 $a$ 和实际尾 $T\omega$，其接缝状态使尾值属于上述合法尾域，级数第一项给出同一个仿射等式。两方向证明结论。证毕。

### 17.乙 联合端点核心与固定延伸

**定义 17.3（辅助标量选枝与端点核心）。** 记

$$
(e_0,e_1,e_2,e_3,e_4,e_5)=(-1,-t^2,g,t,2t,\phi),
\qquad E=\{e_0,e_1,e_2,e_3,e_4,e_5\}.
$$

五个合法闭分支像为

$$
f_3(X)=[e_0,e_1],\quad f_0(X)=[e_1,e_2],\quad
f_5(I)=[e_2,e_3],\quad f_2(X)=[e_3,e_4],\quad
f_{25}(I)=[e_4,e_5].
$$

在内部公共端点选择右侧分支，定义

$$
\alpha(x)=
\begin{cases}
3,&e_0\le x<e_1,\\
0,&e_1\le x<e_2,\\
5,&e_2\le x<e_3,\\
2,&e_3\le x<e_4,\\
25,&e_4\le x\le e_5,
\end{cases}
\qquad
T_{\mathrm{sel}}(x)=\frac{\Delta_{\alpha(x)}-x}{g}.
$$

$T_{\mathrm{sel}}$ 仅是构造颜色的辅助标量选枝函数；$T$ 始终表示实际地址的三位删除。它们不是同一种对象。共同端点可以有另一条实际分支，故不能用 $T_{\mathrm{sel}}(x)$ 替换任意地址的实际下一样本。核心颜色规定为

$$
\bigl(Q(e_0),Q(e_1),Q(e_2),Q(e_3),Q(e_4),Q(e_5)\bigr)
=(4,1,2,3,4,5).
$$

允许色集为 $S_I=\{1,2,3,4\}$、$S_O=\{3,4,5\}$；$t=e_3$ 的唯一颜色为 $3\in S_I\cap S_O$。

**定理 17.4（全部十条端点边的相容性）。** $T_{\mathrm{sel}}$ 是 Borel 函数，每个标量至多有五个 $T_{\mathrm{sel}}$-前驱，且 $T_{\mathrm{sel}}(E)\subseteq E$。核心颜色对所有输出属于 $E$ 的合法边同时满足定义17.1的解码等式，包括四条未选中的公共端点边。

证明。五个像区间由 $t^2=1-t$ 及各个负斜率分支的两端值算出，内部两两不交。因此 $T_{\mathrm{sel}}$ 有五个仿射 Borel 分片，每片对给定尾值至多提供一个前驱。核心的选定后继为

$$
\begin{aligned}
T_{\mathrm{sel}}(e_0)&=e_5,&T_{\mathrm{sel}}(e_1)&=e_5,&
T_{\mathrm{sel}}(e_2)&=e_3,\\
T_{\mathrm{sel}}(e_3)&=e_5,&T_{\mathrm{sel}}(e_4)&=e_3,&
T_{\mathrm{sel}}(e_5)&=e_0.
\end{aligned}
$$

每个分支单射，其输出端点只能来自该分支合法尾域的端点。逐一列出便得到下表；它既列出所有可能的端点输出，也核对了同一份核心颜色。

| 端点边编号 | 实际尾 $y$ | 标签 $a$ | 当前值 $f_a(y)$ | 同一表的解码 |
| --- | --- | --- | --- | --- |
| 核心17甲 | $e_0$ | $3$ | $e_1$ | $D(1,4)=3$ |
| 核心17乙 | $e_0$ | $0$ | $e_2$ | $D(2,4)=0$ |
| 核心17丙 | $e_0$ | $5$ | $e_3$ | $D(3,4)=5$ |
| 核心17丁 | $e_0$ | $2$ | $e_4$ | $D(4,4)=2$ |
| 核心17戊 | $e_0$ | $25$ | $e_5$ | $D(5,4)=25$ |
| 核心17己 | $e_5$ | $3$ | $e_0$ | $D(4,5)=3$ |
| 核心17庚 | $e_5$ | $0$ | $e_1$ | $D(1,5)=0$ |
| 核心17辛 | $e_5$ | $2$ | $e_3$ | $D(3,5)=2$ |
| 核心17壬 | $e_3$ | $5$ | $e_2$ | $D(2,3)=5$ |
| 核心17癸 | $e_3$ | $25$ | $e_4$ | $D(4,3)=25$ |

其中六条是选定边，另四条分别是 $e_1,e_2,e_3,e_4$ 的另一来源。表中各等式由 $D$ 的对应格给出。输出不在 $E$ 的合法边则必有

$$
x=f_a(y)\notin E\quad\Longrightarrow\quad
\alpha(x)=a,\quad T_{\mathrm{sel}}(x)=y,
$$

因为其输出在唯一一个分支像的内部。证毕。

**定义 17.5（固定延伸表与带类型颜色映射）。** 对合法尾色定义固定映射 $\mathcal K_a$：

| 延伸表的尾色 $d$ | $\mathcal K_3(d)$ | $\mathcal K_0(d)$ | $\mathcal K_5(d)$ | $\mathcal K_2(d)$ | $\mathcal K_{25}(d)$ |
| --- | --- | --- | --- | --- | --- |
| 延伸17尾色 $1,2,3$ | $3$ | $1$ | $2$ | $5$ | $4$ |
| 延伸17尾色 $4$ | $1$ | $2$ | $3$ | $4$ | $5$ |
| 延伸17尾色 $5$ | $2$ | $1$ | 不使用 | $5$ | 不使用 |

尾色 $5$ 只能出现在 $O$ 类型，不用于尾域为 $I$ 的标签。每个使用的表格满足

$$
D(\mathcal K_a(d),d)=a.
$$

对 $I$ 类型合法尾色，标签 $3,0,5$ 的输出在 $S_I$ 中，标签 $2,25$ 的输出在 $S_O$ 中；对 $O$ 类型合法尾色，标签 $3,0$ 的输出在 $S_I$ 中，标签 $2$ 的输出在 $S_O$ 中。这些性质均由表格逐格给出。

在不含端点的集合上进一步使用 $U_I=\{1,2,3\}$、$U_O=\{4,5\}$。若 $x$ 及其选定尾都不在 $E$，按 $x<t$ 或 $x>t$ 记当前类型为 $\iota(x)=I$ 或 $O$，并定义

$$
h_x:U_{\iota(T_{\mathrm{sel}}x)}\longrightarrow U_{\iota(x)}
$$

为相应 $\mathcal K_{\alpha(x)}$ 的限制。全部可能的带类型表如下。

| 带类型分支编号 | 标签与类型 | 映射 $h_x$ |
| --- | --- | --- |
| 回传17甲 | $3:I\leftarrow I$ | 常值 $3$ |
| 回传17乙 | $0:I\leftarrow I$ | 常值 $1$ |
| 回传17丙 | $5:I\leftarrow I$ | 常值 $2$ |
| 回传17丁 | $2:O\leftarrow I$ | 常值 $5$ |
| 回传17戊 | $25:O\leftarrow I$ | 常值 $4$ |
| 回传17己 | $3:I\leftarrow O$ | $4\mapsto1,\ 5\mapsto2$ |
| 回传17庚 | $0:I\leftarrow O$ | $4\mapsto2,\ 5\mapsto1$ |
| 回传17辛 | $2:O\leftarrow O$ | $4\mapsto4,\ 5\mapsto5$ |

这些映射保持所列 $U$ 类型，且

$$
D(h_x(d),d)=\alpha(x)
\quad\text{对每个 }d\in U_{\iota(T_{\mathrm{sel}}x)}.
$$

尾类型为 $I$ 的映射全为常值；唯一的 $O\leftarrow O$ 映射是标签 $2$ 的恒等映射。

### 17.丙 无轨道代表选择的全域可测构造

**定理 17.6（端点盆、首次常值回传与 Borel 单值性）。** 定义

$$
\mathcal B_E=\bigcup_{n\ge0}T_{\mathrm{sel}}^{-n}(E),
\qquad Y=X\setminus\mathcal B_E.
$$

则 $\mathcal B_E$ 是可数 Borel 集，且

$$
T_{\mathrm{sel}}^{-1}(\mathcal B_E)=\mathcal B_E.
$$

以下规则与定义17.3的核心颜色联合定义一个全域单值 Borel 函数 $Q$。在 $\mathcal B_E\setminus E$ 上，令

$$
n_E(x)=\min\{n\ge1:T_{\mathrm{sel}}^n x\in E\},
\qquad
Q(x)=\mathcal K_{\alpha(x)}\bigl(Q(T_{\mathrm{sel}}x)\bigr),
$$

按 $n_E$ 递增定义。在 $Y$ 上，令 $x_j=T_{\mathrm{sel}}^j x$ 及

$$
\nu(x)=\min\{n\ge0:x_{n+1}<t\},
$$

若集合为空则令 $\nu(x)=\infty$。定义

$$
Q(x)=
\begin{cases}
(h_{x_0}\circ h_{x_1}\circ\cdots\circ h_{x_n})(1),
&\nu(x)=n<\infty,\\
h_x(4),&\nu(x)=\infty.
\end{cases}
$$

这个函数满足

$$
Q(I)\subseteq S_I,\qquad Q(O)\subseteq S_O,
$$

且在 $Y$ 上有 $Q(x)\in U_{\iota(x)}$ 和统一递推

$$
Q(x)=h_x\bigl(Q(T_{\mathrm{sel}}x)\bigr).
$$

永久 $O$ 尾情形精确为

$$
\{x\in Y:\nu(x)=\infty\}
=\left\{-\frac\phi2,-\frac{t^2}{2},\frac\phi2\right\},
$$

这三个点的颜色依次为 $1,2,4$。

证明。由定理17.4，每层 $T_{\mathrm{sel}}^{-n}(E)$ 至多有 $6\cdot5^n$ 个点。因此 $\mathcal B_E$ 可数，亦为 Borel 集。若 $x\in\mathcal B_E$，某次迭代到达 $E$，下一次仍在 $E$，所以 $T_{\mathrm{sel}}x\in\mathcal B_E$；反过来，若 $T_{\mathrm{sel}}x\in\mathcal B_E$，再加一次前置迭代便有 $x\in\mathcal B_E$。这证明完全不变等式，特别是 $T_{\mathrm{sel}}(Y)\subseteq Y$。

若 $n_E(x)=1$，盆内规则只读取已经指定的核心颜色；若 $n_E(x)>1$，则 $n_E(T_{\mathrm{sel}}x)=n_E(x)-1$。故它是自然数深度上的良定义递推，无循环选择。定理17.4使每个非核心标量使用唯一后继；定义17.5的类型保持性质又按深度归纳保证所有映射均有合法输入，所得颜色属于相应 $S_I$ 或 $S_O$。核心本身不应用盆内延伸规则。例如 $f_3(e_5)=e_0$ 的核心颜色为 $4$，而 $\mathcal K_3(5)=2$；核心的解码已经由十条联合等式满足，故这并不是两份冲突的规定。

在 $Y$ 上，全部 $x_j$ 避开 $E$，特别是 $x_j\ne t$，所以每个点有唯一类型。若 $\nu(x)=n<\infty$，则 $x_{n+1}$ 的类型是 $I$，末尾输入 $1\in U_I$ 合法；沿表中的类型箭头向左复合，每一步输入和输出均合法。最右的 $h_{x_n}$ 是尾类型为 $I$ 的常值映射，所以其值不依赖末尾取 $U_I$ 中哪一种颜色。这只是到首次常值边的有限回传，并没有假定尚未着色的尾点颜色是 $1$。寻找从 $x_1$ 开始的首次 $I$ 尾也保留了当前点在 $I$、而其首个尾在 $O$ 的情形。

若 $\nu(x)=\infty$，则 $x_j\in O$ 对所有 $j\ge1$ 成立。首个映射 $h_x$ 的输入域是 $U_O$，所以 $h_x(4)$ 合法，但当前点未必属于 $O$。从 $x_1$ 开始，每一条边都是 $2:O\leftarrow O$，其颜色映射为恒等。因此 $Q(T_{\mathrm{sel}}x)=4$，首步回传正是 $h_x(4)$；对于当前点在 $I$ 的两种首边，它分别给出 $1,2$，不能用统一常数 $4$ 代替。

进一步令

$$
z=\frac1{1+g}=\frac\phi2,
\qquad f_2(z)=z.
$$

对于永久 $O$ 尾，$x_1=f_2^m(x_{m+1})$ 对每个 $m\ge1$ 成立。因 $f_2$ 的收缩比为 $g$，而全部尾点有统一界，

$$
|x_1-z|=g^m|x_{m+1}-z|\longrightarrow0.
$$

故 $x_1=z$。$z>t$，只有标签 $3,0,2$ 可以前接这个尾值，其当前值为

$$
f_3(z)=-\frac\phi2,\qquad
f_0(z)=-\frac{t^2}{2},\qquad f_2(z)=z.
$$

$z\notin E$ 且 $T_{\mathrm{sel}}z=z$，所以 $z\notin\mathcal B_E$；其余两点的选定后继是 $z$，完全不变性使它们也不在 $\mathcal B_E$。反向包含随即成立，三点颜色由带类型表得到。

现在核对 $Y$ 上的统一递推。若 $\nu(x)=0$，则 $h_x$ 为常值，且 $Q(T_{\mathrm{sel}}x)\in U_I$，所以把末尾输入 $1$ 换为这一已定义颜色不改变结果。若 $1\le\nu(x)=n<\infty$，则 $\nu(T_{\mathrm{sel}}x)=n-1$；将有限复合的首项 $h_x$ 分离便得到递推。若 $\nu(x)=\infty$，前述恒等尾给出 $Q(T_{\mathrm{sel}}x)=4$，亦得到递推。三种情形同时证明所有 $Y$ 点的颜色属于对应 $U$ 类型。

最后证明可测性。对有限 $n\ge0$，首次返回层是 Borel 集

$$
C_n=Y\cap\bigcap_{k=1}^{n}\{x:T_{\mathrm{sel}}^k x>t\}
\cap\{x:T_{\mathrm{sel}}^{n+1}x<t\},
$$

其中 $n=0$ 的中间部分为空交。永久层为

$$
C_\infty=Y\cap\bigcap_{k\ge1}\{x:T_{\mathrm{sel}}^k x>t\}.
$$

$T_{\mathrm{sel}}$ 的每个有限迭代都是 Borel，故这些层两两不交、均为 Borel，且覆盖 $Y$。映射 $x\mapsto h_x$ 由有限值的 Borel 数据 $\alpha(x),\iota(x),\iota(T_{\mathrm{sel}}x)$ 决定。在 $C_n$ 上按长度 $n+1$ 的带类型分支词分片，有限复合在每片上常值，所以 $Q|_{C_n}$ 为 Borel；在 $C_\infty$ 上 $h_x(4)$ 也为 Borel。$\mathcal B_E$ 上每个颜色纤维是可数个单点的并。于是全域每个纤维满足

$$
\begin{aligned}
Q^{-1}(\{d\})={}&\{x\in\mathcal B_E:Q(x)=d\}\\
&\cup\bigcup_{n\ge0}\{x\in C_n:Q(x)=d\}
\cup\{x\in C_\infty:Q(x)=d\},
\end{aligned}
$$

右端全为 Borel 集，证明 $Q$ 是 Borel 函数。构造始终由点态公式及有限深度递推给值，没有选择任意组件代表，也没有对不同循环独立选色。轨道若汇合，读到的是汇合点同一个 $Q$；周期中的递推也由上面的逐点等式同时闭合。证毕。

### 17.丁 精确五色与实际连续取得

**定理 17.7（同一 Borel 量化器的精确五色定理）。** 定理17.6的全域 $Q$ 对全部五个合法闭分支图同时满足

$$
D\bigl(Q(f_a(y)),Q(y)\bigr)=a.
$$

它恰好使用五色，且

$$
Q(I)=\{1,2,3,4\},\qquad Q(O)=\{3,4,5\}.
$$

在全部 $\Omega$ 实际地址的精确相邻观察合同中，任意单值有限颜色函数配任意确定解码器都至少需要五种非空颜色；Borel 类与不加正则性限制的函数类的最小颜色数因而都恰为五。

证明。给定合法边 $x=f_a(y)$，若 $x\in E$，则定理17.4已经列出该边，特别是 $y\in E$，十条联合等式全部成立。若 $x\notin E$，则 $a=\alpha(x)$、$y=T_{\mathrm{sel}}x$。完全不变性保证 $x,y$ 同在 $\mathcal B_E$，或同在 $Y$。前者由盆内规则及 $D(\mathcal K_a(d),d)=a$ 得到解码；后者由 $Y$ 上的统一递推及 $D(h_x(d),d)=\alpha(x)$ 得到解码。这包括每条实际边，而不是只验证选中的端点边。

此论证也说明盆在所有合法闭分支下完全不变：非端点边的两个端都同属盆或同属补集；端点输出和它的全部合法尾都在核心中。任何迭代双地址只能先经过同一个非端点分支，再在公共端点首次分歧，故核心外的深度递推与十条核心等式共同处理全部深度的多地址情形。

定理17.6给出类型包含关系。核心中 $e_0,e_1,e_2,e_3\in I$ 的颜色分别是 $4,1,2,3$，$e_3,e_4,e_5\in O$ 的颜色分别是 $3,4,5$，所以两个包含关系都是等式，全域使用全部五色。

为证下界，取命题14.6的共同实际尾

$$
L=(3,25)^\infty\in A_1\subset A_0,\qquad \kappa_0(L)=-1.
$$

接缝图使 $3L,0L,5L,2L,25L$ 全部是从 guard 零出发的合法地址。它们下一实际值相同，均为 $-1$；当前值依次为

$$
f_3(-1)=-t^2=e_1,\quad f_0(-1)=g=e_2,\quad
f_5(-1)=t=e_3,\quad f_2(-1)=2t=e_4,\quad
f_{25}(-1)=\phi=e_5.
$$

五值严格递增，因而彼此不同。若任意候选量化器 $\widetilde Q$ 将其中两个当前值赋予同一颜色，则这两个实际来源产生完全相同的有序对

$$
\bigl(\widetilde Q(f_a(-1)),\widetilde Q(-1)\bigr),
$$

但首窗不同，任何确定解码器都不能同时正确。这强制五种当前颜色两两不同，故至少五色。上面的全域 Borel 构造取得五色，两个函数类的下界和上界相等。定理17.2确保这里的五条分支均有共同实际尾，而非只是在扩大模型中形式可用。证毕。

**定理 17.8（实际取得的重叠对恢复）。** 设 $\ell\ge1$，$\omega\in\Omega$，已经实际取得同一来源的连续精确样本

$$
z_j=\kappa_0(T^j\omega),\qquad 0\le j\le\ell.
$$

仅记录这 $\ell+1$ 个样本的五色值，即可恢复前 $\ell$ 个标签，恢复公式为

$$
\sigma_j(\omega)=D(Q(z_j),Q(z_{j+1})),\qquad 0\le j<\ell.
$$

证明。每个删窗后地址 $T^j\omega$ 都属于 $A_0$；当其实际 incoming guard 为一时，它还满足相应更小的合法首窗集合，但仍是定义17.1合同中的地址。对每个 $j$，其自己的实际尾 $T^{j+1}\omega$ 给出

$$
z_j=f_{\sigma_j(\omega)}(z_{j+1}),
$$

且 $z_{j+1}$ 在该标签的合法尾域内。定理17.7对这条实际边恢复 $\sigma_j(\omega)$。在相邻的恢复中共用已经取得的 $Q(z_{j+1})$，故 $\ell+1$ 个样本覆盖 $\ell$ 个重叠相邻对。证毕。

**定理 17.9（共享当前点的实际尾必须保留）。** 同一当前标量 $e_1=-t^2$ 的来源 $3L$ 与 $0R$，其中 $R=(25,3)^\infty$，在本构造下分别给出实际颜色对 $(1,4)$ 与 $(1,5)$，解码为 $3$ 与 $0$。所以定理17.8的样本条件不能以“对当前标量应用辅助选枝取得后继”替换。

证明。命题14.6给出 $\kappa_0(L)=-1=e_0$、$\kappa_0(R)=\phi=e_5$，且

$$
f_3(e_0)=e_1=f_0(e_5).
$$

定义17.3给出 $Q(e_1)=1$、$Q(e_0)=4$、$Q(e_5)=5$，解码表又有 $D(1,4)=3$、$D(1,5)=0$。辅助选枝只取 $T_{\mathrm{sel}}(e_1)=e_5$，故它对应第二条来源的尾，不能给出第一条来源自己的下一实际值。恢复公式利用实际取得的相邻样本，不把一个标量的任选逆枝当作实际演化。证毕。

本章的合同是精确样本上的 Borel 可测观察。连通纤维合同、等宽分格合同和要求扰动容限的合同是不同的数学条件；定理17.7不以可测性代替这些条件。定理16.8的连通类六色与定理16.9的等宽类八色结论仍按各自合同适用，原来的无约束界 $5\le q_{\min}\le6$ 亦仍成立；定理17.7把精确相邻任务的无约束最小值确定为五。定理17.8只以已实际取得的样本为前提，未提供由当前标量取得未来样本或自主颜色更新的条件。

### 17.戊 数学引用

本章使用定义14.5、命题14.6及定义16.1的合法地址、满像与实际分支桥梁，使用定理16.7的同一观察函数的相邻解码合同。可数单点并、Borel 分片函数和 Borel 复合的基础可参照 A. S. Kechris, Classical Descriptive Set Theory, Springer, 1995。具体解码表、全部端点联合赋色与可测实现由本章的定义和证明给出；该引用只支撑一般可测性背景，不承担本构造的分支等式，也不作新颖性断言。

## 18. 指定五色量化器的完整纤维与拓扑

### 18.甲 固定构造的颜色规则与收缩环带

**定义 18.1（本章唯一分析的函数与区间族）。** 本章的 $Q$ 严格指第17章的函数：端点颜色为 $(4,1,2,3,4,5)$，核心外使用定义17.5的 $\mathcal K_a,h_x$，永久 $O$ 尾使用 $Q(x)=h_x(4)$。颜色集取离散拓扑，定义域 $X=[-1,\phi]$ 取实直线的相对拓扑。令

$$
F=f_2,\qquad F(y)=1-gy,\qquad z=\frac\phi2,
$$

$$
b=F(t)=3t-1,\qquad c=2t,\qquad
u=f_3(t)=-2t^2,\qquad v=f_0(t)=-t^4.
$$

区间端点 $u$ 与第17章的首次返回时间 $\nu(x)$ 是不同记号。对 $n\ge0$ 定义

$$
s_n=F^n(\phi),\qquad r_n=F^n(c),\qquad
J_n=F^n([c,\phi)),\qquad H_n=F^n([b,c)).
$$

于是 $s_0=\phi$、$s_1=t$、$s_2=b$。记

$$
V_4=\{z\}\cup\bigcup_{n\ge0}J_n,\qquad
V_5=\{\phi\}\cup\bigcup_{n\ge0}H_n.
$$

**定理 18.2（固定延伸规则的两种基本尾型）。** 此 $Q$ 满足

$$
Q^{-1}(4)\cap I=\{-1\},\qquad
Q^{-1}(3)\cap O=\{t\},
$$

且对 $y\in I\setminus\{-1\}$ 有

$$
\begin{array}{c|ccccc}
a&3&0&5&2&25\\ \hline
Q(f_a(y))&3&1&2&5&4.
\end{array}
$$

对 $t<y<\phi$ 则有 $Q(y)\in\{4,5\}$，并且

$$
Q(F(y))=Q(y),\qquad
\begin{array}{c|cc}
Q(y)&4&5\\ \hline
Q(f_3(y))&1&2\\
Q(f_0(y))&2&1.
\end{array}
$$

证明。核心中，$I$ 内只有 $e_0=-1$ 取色 $4$，$O$ 内只有 $e_3=t$ 取色 $3$。在盆的非核心点，输出类型为 $I$ 的三个延伸函数 $\mathcal K_3,\mathcal K_0,\mathcal K_5$ 只输出 $1,2,3$；输出类型为 $O$ 的两个延伸函数 $\mathcal K_2,\mathcal K_{25}$ 只输出 $4,5$。在 $Y$ 上则直接有 $U_I,U_O$ 的限制。因此

$$
Q(I\setminus\{-1\})\subseteq\{1,2,3\},\qquad
Q(O\setminus\{t\})\subseteq\{4,5\}.
$$

对 $y\in I\setminus\{-1,t\}$，五个输出均不在核心，固定延伸表在尾色 $1,2,3$ 上的第一行给出所列常值。$y=t$ 时，标签 $3,0,2$ 的输出不在核心，仍用该行；标签 $5,25$ 的输出分别是 $e_2,e_4$，其核心颜色为 $2,4$，与所列结果一致。

若 $t<y<\phi$，其尾色为 $4$ 或 $5$。输出 $F(y)$ 位于 $(t,b)$，而 $f_3(y),f_0(y)$ 分别位于 $(-1,u),(-t^2,v)$，均不在核心。若这些点在盆内，应用 $\mathcal K$；若在 $Y$ 内，应用 $h$。两者对尾色 $4,5$ 使用同一固定表，给出上述恒等与重命名规则。端点不能扩大进 $Q(F(y))=Q(y)$ 的定义域：$Q(\phi)=5$，但 $Q(F\phi)=Q(t)=3$；$Q(t)=3$，但 $Q(Ft)=Q(b)=5$。证毕。

**定理 18.3（收缩环带的覆盖、奇偶端点与 $O$ 上的全部纤维）。** 有

$$
F^n(x)=z+(-g)^n(x-z),
$$

及严格次序

$$
-1<u<-t^2<v<g<t<z<b<c<\phi.
$$

全部区间的端点归属为

$$
\begin{aligned}
J_{2m}&=[r_{2m},s_{2m})
=[z+g^{2m}(c-z),z+g^{2m}(\phi-z)),\\
J_{2m+1}&=(s_{2m+1},r_{2m+1}]
=(z-g^{2m+1}(\phi-z),z-g^{2m+1}(c-z)],\\
H_{2m}&=[s_{2m+2},r_{2m})
=[z+g^{2m}(b-z),z+g^{2m}(c-z)),\\
H_{2m+1}&=(r_{2m+1},s_{2m+3}]
=(z-g^{2m+1}(c-z),z-g^{2m+1}(b-z)].
\end{aligned}
$$

所有 $J_n,H_n$ 非空，有正长度，且彼此两两不交；它们的并为 $(t,\phi)\setminus\{z\}$。在 $O$ 上的完整纤维恰为

$$
Q^{-1}(3)\cap O=\{t\},\qquad
Q^{-1}(4)\cap O=V_4,\qquad
Q^{-1}(5)\cap O=V_5,
$$

颜色 $1,2$ 在 $O$ 上不出现。

证明。$F(z)=z$，故 $F(x)-z=-g(x-z)$，归纳即得迭代公式。$t$ 是 $x^2+x-1$ 的正根，代入 $3/5,5/8$ 得 $3/5<t<5/8$。配合 $t^2=1-t$，得到 $-1<u<-t^2<v<0<g<t$。又有

$$
F(\phi)=t,\quad F^2(\phi)=b,\quad
c-b=\phi-c=t^2>0,
$$

以及 $t<z=\phi/2$、$b-z=g^2(\phi-z)>0$，给出全部严格次序。

负斜率迭代在奇数次反转区间方向与开闭端，偶数次保持方向，故得到四个区间公式。令 $d=\phi-z>0$，并用 $b-z=g^2d$，则完整环带为

$$
F^{2m}([b,\phi))=[z+g^{2m+2}d,z+g^{2m}d),
$$

$$
F^{2m+1}([b,\phi))=(z-g^{2m+1}d,z-g^{2m+3}d].
$$

偶数环带按半开归属两两不交，覆盖 $(z,\phi)$；奇数环带亦两两不交，覆盖 $(t,z)$，因为 $s_{2m}\downarrow z$、$s_{2m+1}\uparrow z$。两组在 $z$ 两侧，不相交。每个环带又由 $J_n,H_n$ 不交分成两段：公共点 $r_n$ 归 $J_n$，不归 $H_n$，另一环带端点由上述奇偶半开约定唯一归属。两种基本区间长度都等于 $t^2$，故

$$
|J_n|=|H_n|=g^nt^2>0.
$$

定理18.2对 $y\in I\setminus\{-1\}$ 给出 $Q=5$ 在 $F(I\setminus\{-1\})=[b,c)$ 上，$Q=4$ 在 $f_{25}(I\setminus\{-1\})=[c,\phi)$ 上；其中 $c$ 的核心颜色也为 $4$。这决定第零环带的颜色。对该环带的任意点，其所有 $F$ 迭代都在 $(t,\phi)$ 内，定理18.2的恒等规则反复保留颜色。于是每个 $J_n$ 全取色 $4$，每个 $H_n$ 全取色 $5$。环带已覆盖全部非固定内部点，剩余 $t,z,\phi$ 的指定颜色为 $3,4,5$，故纤维公式完整。证毕。

### 18.乙 五个全域纤维与全部极大连通分支

**定理 18.4（全域五个颜色纤维）。** 定义18.1的 $V_4,V_5$ 给出

$$
\begin{aligned}
Q^{-1}(1)&=f_3(V_4)\cup f_0(V_5)\cup[v,g),\\
Q^{-1}(2)&=f_3(V_5\setminus\{\phi\})\cup f_0(V_4)\cup[g,t),\\
Q^{-1}(3)&=[u,-t^2)\cup\{t\},\\
Q^{-1}(4)&=\{-1\}\cup V_4,\\
Q^{-1}(5)&=V_5.
\end{aligned}
$$

这些集合两两不交，覆盖 $X$；每个集合都是由定义18.1和定理18.3明确给出的可数区间与单点的并。

证明。对 $y\in I\setminus\{-1\}$，定理18.2给出三个 $I$ 输出的常值，且

$$
f_3(I\setminus\{-1\})=[u,-t^2),\qquad
f_0(I\setminus\{-1\})=[v,g),\qquad
f_5(I\setminus\{-1\})=[g,t).
$$

在剩余的两段，

$$
f_3(O)=[-1,u],\qquad f_0(O)=[-t^2,v],
$$

内部尾色 $4,5$ 经 $f_3$ 分别变成 $1,2$，经 $f_0$ 分别变成 $2,1$。$f_3(\phi)=-1$ 是核心例外，取色 $4$，所以色 $2$ 的 $f_3$ 像从 $V_5$ 中删去 $\phi$；$f_0(\phi)=-t^2$ 的核心颜色为 $1$，恰与 $f_0(V_5)$ 一致。另一对接点 $f_3(t)=u$、$f_0(t)=v$ 分别取色 $3,1$，已经归入常值区间。$g$ 归色 $2$，$t$ 归色 $3$。最后在 $O$ 上使用定理18.3，且 $-1$ 是 $I$ 中唯一的色 $4$ 点。

因此各公式在每个开段及所有接点上都给出原函数的颜色；$[-1,u]$、$[u,-t^2]$、$[-t^2,v]$、$[v,g]$、$[g,t]$、$[t,\phi]$ 覆盖 $X$。接点只有上面核对的一个颜色，内部又来自不交环带或常值段，所以不存在遗漏或额外重叠。$f_3,f_0$ 都是仿射同胚，将定理18.3的半开区间映成半开区间并反转两端归属，故这些公式也是全域的明确区间加点表达式。证毕。

**定理 18.5（每种颜色的全部极大连通分支及精确数量）。** $Q$ 的五个纤维的极大连通分支恰为下表；所有出现的 $n$ 均遍历非负整数。

| 纤维编号 | 全部极大连通分支 | 分支数 |
| --- | --- | --- |
| 拓扑18色 $1$ | $\{f_3(z)\}$，$\{-t^2\}$，$[v,g)$，每个 $f_3(J_n)$，每个 $f_0(H_n)$ | $\aleph_0$ |
| 拓扑18色 $2$ | $\{f_0(z)\}$，$[g,t)$，每个 $f_3(H_n)$，每个 $f_0(J_n)$ | $\aleph_0$ |
| 拓扑18色 $3$ | $[u,-t^2)$，$\{t\}$ | $2$ |
| 拓扑18色 $4$ | $\{-1\}$，$\{z\}$，每个 $J_n$ | $\aleph_0$ |
| 拓扑18色 $5$ | $\{\phi\}$，每个 $H_n$ | $\aleph_0$ |

特别是 $\{z\},\{f_3(z)\},\{f_0(z)\}$ 各自是所在纤维的单点连通分支，虽然它们不是各自纤维的孤立点。

证明。实直线上的连通子集必须包含任意两点之间的整段区间。因而一个已知不交的区间与单点分割，只要证明不同候选块之间有异色点，就确定了全部极大连通分支。下面同时核对每个包含端点、接触点和极限点。

先在 $O$ 上，定理18.3给出每个环带内的 $J_n,H_n$ 两段，它们在 $r_n$ 接触。$r_n$ 属于 $J_n$，颜色为 $4$，$H_n$ 排除它；该点两侧分别有正长度的色 $4,5$ 内部。$J_n$ 的另一端 $s_n$ 被排除。若 $n=0$，该端是颜色 $5$ 的 $\phi$；若 $n=1$，该端是颜色 $3$ 的 $t$；若 $n\ge2$，则 $s_n=F^{n-2}(b)$ 归 $H_{n-2}$，颜色为 $5$。在后一种情形，$s_n$ 两侧分别邻接 $H_{n-2}$ 与 $J_n$ 的正长度内部。$H_n$ 的另一端 $s_{n+2}=F^n(b)$ 被包含，颜色为 $5$，其外侧邻接 $J_{n+2}$ 的正长度色 $4$ 内部。因此在同一侧按环带排列时，每两个相邻的色 $4$ 区间之间都有一个正长度色 $5$ 区间，每两个相邻的色 $5$ 区间之间都有一个正长度色 $4$ 区间；包含公共端点不会把同色的两段合并。

左右两列环带都趋于 $z$。连接 $z$ 与任意其他色 $4$ 点的实区间中，总有更靠近 $z$ 的某个非空 $H_n$ 内部，故该连接区间不全是色 $4$。所以 $\{z\}$ 是一个分支，而不是将全部 $J_n$ 连为一体的桥。色 $5$ 不含 $z$；跨越 $z$ 的连通集必含 $z$，因而也不能连接两侧的 $H_n$。$\phi$ 与所有 $H_n$ 之间有非空的 $J_0$ 色 $4$ 段，所以 $\{\phi\}$ 是色 $5$ 的另一个分支。$J_n$ 的内部点趋于 $z$，故色 $4$ 的单点分支 $\{z\}$ 并不是纤维中的孤立点。这证明 $O$ 内所有分支及其极大性。

在 $f_3((t,\phi))=(-1,u)$ 内，$f_3$ 为仿射同胚，尾色 $4,5$ 分别重命名为 $1,2$。由前段的分隔结论，色 $1$ 的候选块是每个 $f_3(J_n)$ 及 $\{f_3(z)\}$，色 $2$ 的候选块是每个 $f_3(H_n)$；相邻块的异色正长度分隔和半开端点归属全部随同胚保留。连接 $f_3(z)$ 与任何同色的其他点也必须穿过某个 $f_3(H_n)$ 内部，所以其单点仍是极大连通分支。在 $f_0((t,\phi))=(-t^2,v)$ 内，尾色 $4,5$ 分别重命名为 $2,1$；同理得到色 $2$ 的每个 $f_0(J_n)$ 及 $\{f_0(z)\}$、色 $1$ 的每个 $f_0(H_n)$。两种像区间族都有内部点趋于其各自固定像点，故这两个单点分支也不是纤维中的孤立点。

仍须排除这些像段与常值段通过边界合并。完整的接点颜色及紧邻两侧颜色如下；外端点仅使用定义域内的一侧。

| 分支接点编号 | 点 | 点上色 | 左侧紧邻色 | 右侧紧邻色 |
| --- | --- | --- | --- | --- |
| 接点18甲 | $-1$ | $4$ | 定义域外 | $1$ |
| 接点18乙 | $u$ | $3$ | $1$ | $3$ |
| 接点18丙 | $-t^2$ | $1$ | $3$ | $2$ |
| 接点18丁 | $v$ | $1$ | $2$ | $1$ |
| 接点18戊 | $g$ | $2$ | $1$ | $2$ |
| 接点18己 | $t$ | $3$ | $2$ | $4$ |
| 接点18庚 | $\phi$ | $5$ | $4$ | 定义域外 |

例如 $t$ 右侧的第一个环带段是 $J_1$，色 $4$；它经 $f_3$ 映到 $u$ 左侧并取色 $1$，经 $f_0$ 映到 $v$ 左侧并取色 $2$。$\phi$ 左侧是 $J_0$，它经 $f_0$ 映到 $-t^2$ 右侧并取色 $2$，经 $f_3$ 映到 $-1$ 右侧并取色 $1$。其余侧色来自定理18.4的三个常值区间。这说明 $u$ 只延伸色 $3$ 的区间，$-t^2$ 单独取色 $1$，$v$ 只延伸 $[v,g)$，$g$ 只延伸 $[g,t)$，没有同色像段跨接这些端点。

具体地，色 $1$ 的 $f_3$ 像块与其 $f_0$ 像块之间有整个色 $3$ 区间 $[u,-t^2)$；单点 $-t^2$ 又由右邻的色 $2$ 段与后面的 $f_0(H_n)$ 分开。$[v,g)$ 的左侧是色 $2$ 段，右端 $g$ 也是色 $2$，所以它不能与色 $1$ 的其他块合并。色 $2$ 的两种像块之间同样被 $[u,-t^2)$ 分开，$[g,t)$ 则与左侧所有像块之间隔着非空的色 $1$ 区间 $[v,g)$，且其右端 $t$ 为色 $3$。色 $3$ 的 $[u,-t^2)$ 与 $\{t\}$ 之间包含色 $1,2$ 的点，故为恰好两个分支。色 $4$ 的 $-1$ 与 $O$ 内任何同色点之间也有异色点，故 $\{-1\}$ 单独成分支。所有非单点候选块都是区间，因此连通；所有不同候选块已经逐类被异色点分开，因此都是极大连通分支。

定理18.4保证表中块穷尽五个纤维。$J_n,H_n$ 全有正长度，且两两不交，所以含有这些无穷区间族的色 $1,2,4,5$ 各至少有可数无穷多个分支；表中每行又只有可数个块，故分支数恰为 $\aleph_0$。色 $3$ 则由已经证明的两个块给出精确数量 $2$。证毕。

### 18.丙 精确不连续点与三个聚点

**定义 18.6（局部不连续核与聚点）。** 令

$$
K_Q=\{z\}\cup\{s_n:n\ge0\}\cup\{r_n:n\ge0\}
=\{z\}\cup\{F^n(\phi),F^n(2t):n\ge0\}.
$$

$K_Q$ 是本章的标量不连续核，不是本卷此前的 joint-domain $K$。对集合 $B\subset X$，$B'$ 表示在 $X$ 相对拓扑中的聚点集，即每个相对邻域都含有不同于该点的 $B$ 中点的所有点。$\operatorname{Disc}(Q)$ 表示 $Q:X\to\mathcal C$ 的不连续点集。

**定理 18.7（指定 $Q$ 的精确不连续集合）。** 对定义18.1固定的函数，按定义域 $X$ 的相对拓扑有

$$
\operatorname{Disc}(Q)
=K_Q\cup f_3(K_Q)\cup f_0(K_Q)\cup\{g\}.
$$

证明。离散有限颜色函数在一个点连续，当且仅当该点有颜色恒定的相对邻域。

先限制到 $O$。定理18.3的所有 $J_n,H_n$ 内部都有常值邻域。每个 $r_n$ 是色 $4,5$ 两个正长度区间的共同边界，故不连续。$s_0=\phi$ 自身为色 $5$，左邻为色 $4$；$s_1=t$ 自身为色 $3$，右邻为色 $4$，故两点在 $O$ 的相对拓扑中也不连续。对 $n\ge2$，$s_n$ 是 $H_{n-2}$ 与 $J_n$ 的共同边界，两侧分别有色 $5,4$ 的内部，故不连续。$z$ 的每个邻域中都有趋近它的 $H_n$ 色 $5$ 内部，而 $Q(z)=4$，所以不连续；实际上两种颜色的内部都从两侧趋近它。其余点都在某个环带段的内部，因此 $Q|_O$ 的不连续集合恰为 $K_Q$。

在 $f_3((t,\phi))=(-1,u)$ 中，定理18.2把尾色 $4,5$ 一一重命名为 $1,2$，并由仿射同胚 $f_3$ 搬运。因此该开段的不连续集合恰为 $f_3(K_Q\cap(t,\phi))$：常值邻域被同胚保留，异色邻点也被同胚保留。同理，在 $f_0((t,\phi))=(-t^2,v)$ 中，一一重命名 $4,5\mapsto2,1$ 给出恰为 $f_0(K_Q\cap(t,\phi))$ 的不连续点。

这两段的四个端点在全域相对拓扑中均不连续。$-1=f_3(\phi)$ 自身为色 $4$，右侧为色 $1$；$u=f_3(t)$ 自身为色 $3$，左侧为色 $1$；$-t^2=f_0(\phi)$ 自身为色 $1$，右侧为色 $2$；$v=f_0(t)$ 自身为色 $1$，左侧为色 $2$。它们均已包含在 $f_3(K_Q)\cup f_0(K_Q)$ 中。

剩余的三个开区间 $(u,-t^2)$、$(v,g)$、$(g,t)$ 分别恒为色 $3,1,2$。它们的接点除 $g$ 外都已经列入前三项；$g$ 左邻为色 $1$，自身及右邻为色 $2$，所以必须另加入 $\{g\}$。$t$ 作为 $O$ 的端点已经属于 $K_Q$，在全域中也不连续。上述开段与接点覆盖 $X$，所以没有其他不连续点。证毕。

**定理 18.8（闭可数性、精确聚点集与开稠密常值域）。** 此函数的不连续集合是可数闭集，且精确聚点集为

$$
\operatorname{Disc}(Q)'
=\left\{\frac\phi2,-\frac\phi2,-\frac{t^2}{2}\right\}.
$$

$X\setminus\operatorname{Disc}(Q)$ 是相对开稠密集，$Q$ 在其上局部常值。其余不连续点在不连续集合中均为孤立点。

证明。由定理18.3的迭代公式，$s_n,r_n$ 均趋于 $z$，且从不等于 $z$。每一列的偶数子列在 $z$ 上方严格递减，奇数子列在下方严格递增。给定任何不含 $z$ 的闭小区间，只有有限多个 $s_n,r_n$ 落在其中。因此两列并集的唯一聚点是 $z$；将 $z$ 加入后，$K_Q$ 为闭可数集，并有 $K_Q'=\{z\}$。同样，仿射同胚保持聚点，故

$$
(f_3(K_Q))'=\{f_3(z)\},\qquad
(f_0(K_Q))'=\{f_0(z)\}.
$$

有限并的聚点集等于各聚点集的并：若一个点不是任一集合的聚点，各集合分别存在一个去掉该点后不相交的邻域，有限次取交便给出并集的这种邻域；反向包含直接成立。单点集 $\{g\}$ 没有聚点。定理18.7因此给出

$$
\operatorname{Disc}(Q)'=\{z,f_3(z),f_0(z)\}.
$$

三点分别是 $\phi/2,-\phi/2,-t^2/2$，彼此不同；$K_Q,f_3(K_Q),f_0(K_Q)$ 分别位于互不相交的闭区间 $[t,\phi],[-1,u],[-t^2,v]$ 内。它们及 $\{g\}$ 都是闭可数集，有限并仍闭可数，故不连续集合闭且可数。已经证明的精确聚点式也说明其余不连续点均为该集合的孤立点。

闭性使补集相对开。实直线任意非空开区间不可数，$X$ 的任意非空相对开集都含有一个非空开区间；一个可数集合因而不能包含这样的相对开集。这说明不连续集合无相对内部，补集稠密。最后，对补集内每点，定理18.7的覆盖证明给出所在常值开段；等价地，离散值函数在该点连续便有常值邻域。因此 $Q$ 在整个开稠密补集上局部常值。证毕。

### 18.丁 有限颜色与有限连通片的区别

**定理 18.9（本构造不能由有限个连通片给出）。** 对第17章指定的 $Q$，颜色 $1,2,4,5$ 中任何一个纤维都不能写成有限个实区间与有限个单点的并。因此这个函数不能由有限个标量切点的常值分格完整表示。它仍有定义18.1和定理18.3所给的有限篇幅递推描述。

证明。每个实区间和单点都是连通集。有限个连通集的并的连通分支数至多为该有限个数：每个非空连通集位于并集的一个连通分支内，每个分支又必须包含至少一个这样的集合。定理18.5给出颜色 $1,2,4,5$ 各有 $\aleph_0$ 个分支，与任何有限个连通片的表示矛盾。若一个量化规则由有限个切点的常值区间及切点赋色给出，每个纤维必为有限个区间和有限个点的并，故也不能等于本 $Q$。另一方面，定义18.1的两种初始半开区间、一个仿射收缩及四个奇偶端点公式，已经完整指定所有区间族和纤维，所用公式的篇幅有限。有限颜色字母表与有限递推描述均不强制有限个空间连通片。该结论逐字只针对本章固定的 $Q$，不对其他五色观察函数的正则性作全称推断。证毕。

本章的拓扑结论只分析第17章已经逐点定义的函数及精确标量域，未加入其他测量合同。纤维的无限分支、可数闭不连续集和三个聚点是这个函数的具体性质。

### 18.戊 数学引用

本章的 FIB 数据及实际来源桥梁来自定义14.5、命题14.6和定理17.2；固定颜色规则来自定义17.3、定义17.5及定理17.6。迭代收缩公式、全纤维、全部分支和精确不连续集由本章证明。实直线连通子集为区间、单调仿射同胚保持连通性与聚点，以及有限离散值函数的局部常值判据，可参照 J. R. Munkres, Topology, 2nd ed., Prentice Hall, 2000, §§18, 23–24。这里使用这些基础性质，不将它们改写成对任意五色量化器的结论，也不作原创优先性断言。

## 追加锚（本行以下为增补区）

## 19. 固定解码表强制的无限连通分支

**定义 19.1（固定表的全部精确实现）。** 沿用定义17.1的 $t,\phi,g,X,I,O,f_a,\Lambda$ 和固定解码器 $D$，以及定义17.3的六端点 $e_j$。本章的 $Q$ 遍历所有单值函数 $Q:X\to\{1,2,3,4,5\}$，只要求

$$
\begin{aligned}
D(Q(f_a(y)),Q(y))&=a
&&\text{对所有 }a\in\{3,0,2\},\ y\in X,\\
D(Q(f_a(y)),Q(y))&=a
&&\text{对所有 }a\in\{5,25\},\ y\in I.
\end{aligned}
$$

这些是完整闭域上的逐点合同，包含所有共享端点；同一个 $Q$ 用于两个实际相邻样本，不对不同来源另选赋色。由定理17.2，它们等价于全部实际地址的精确相邻解码合同。本章不假设 $Q$ 可测，也不指定定义17.5–17.6的延伸规则。沿用定义18.1中与赋色无关的记号

$$
F=f_2,\qquad F(y)=1-gy,\qquad z=\frac\phi2,\qquad
r_n=F^n(2t),\qquad s_n=F^n(\phi)\quad(n\ge0).
$$

**定理 19.2（固定 $D$ 的普遍无限分支障碍）。** 对定义19.1中的每一个 $Q$，必有

$$
(Q(e_0),Q(e_1),Q(e_2),Q(e_3),Q(e_4),Q(e_5))
=(4,1,2,3,4,5),
$$

$$
Q(F(y))=4\quad\Longleftrightarrow\quad Q(y)=4
\qquad(y\in X).
$$

点 $r_0,r_2,r_4,\ldots$ 分别属于 $Q^{-1}(4)\cap O$ 的两两不同连通分支，也属于全域纤维 $Q^{-1}(4)$ 的两两不同连通分支。因此这两个集合均有无限多个连通分支，色 $4$ 纤维不能写成有限个实区间与有限个单点的并。

证明。先从合同推出端点颜色。在共同合法尾点 $e_0=-1\in I$，五个标签的当前值依次为

$$
(f_3(e_0),f_0(e_0),f_5(e_0),f_2(e_0),f_{25}(e_0))
=(e_1,e_2,e_3,e_4,e_5).
$$

这些点的颜色必须两两不同，否则相同的有序颜色对会要求 $D$ 输出两个不同标签。因此 $Q(e_0)$ 所在列必须包含五个标签各一次。第 $5$ 列缺少标签 $5,25$，排除 $Q(e_0)=5$。若 $Q(e_0)\in\{1,2,3\}$，这三个相同的列强制

$$
(Q(e_1),Q(e_2),Q(e_3),Q(e_4),Q(e_5))=(3,1,2,5,4).
$$

但另一个合法闭分支满足 $f_0(e_5)=e_1$，故合同要求 $D(3,4)=0$，而固定表给出 $D(3,4)=5$，矛盾。于是 $Q(e_0)=4$，第 $4$ 列随即给出所述六端点颜色。这一推导使用全部合法图中的共同尾边和共享当前端点边，没有假定某个具体构造的核心赋色。

其次，第 $4$ 行中标签 $2$ 只出现在第 $4$ 列，第 $4$ 列中标签 $2$ 也只出现在第 $4$ 行。因此在 $D(u,v)=2$ 的前提下，$u=4$ 当且仅当 $v=4$。标签 $2$ 对每个 $y\in X$ 都合法，将 $(u,v)=(Q(F(y)),Q(y))$ 代入即得双向成员资格等价。又有 $F(X)=[t,2t]\subseteq O\subseteq X$，所有迭代仍合法；由 $Q(e_4)=4$、$Q(e_5)=5$ 归纳得到

$$
Q(r_n)=4,\qquad Q(s_n)\ne4\qquad(n\ge0).
$$

最后建立交错次序。由 $t^2=1-t$、$g=2t-1$ 得 $z=1/(1+g)=\phi/2$、$F(z)=z$，从而

$$
F^k(y)=z+(-g)^k(y-z),\qquad 0<g<1.
$$

有 $s_1=t$、$s_2=F(t)=3t-1$，以及 $r_0-s_2=t^2>0$。由于 $r_0=2t<\phi=s_0$ 且 $F^2$ 严格递增，$r_2<s_2$；又由 $s_2-z=g^2(\phi-z)>0$ 得 $z<s_2<r_0$，故 $r_2-z=g^2(r_0-z)>0$。这先给出严格的基础次序

$$
z<r_2<s_2<r_0<s_0.
$$

对它应用严格递增且固定 $z$ 的 $F^{2n}$，得到

$$
z<r_{2n+2}<s_{2n+2}<r_{2n}<s_{2n}\qquad(n\ge0).
$$

特别地，偶数列 $r_{2n}$ 严格递减。任取 $m>n$，便有

$$
r_{2m}\le r_{2n+2}<s_{2n+2}<r_{2n}.
$$

两端点都是色 $4$，中间的 $s_{2n+2}$ 却不是色 $4$。全部这些点在 $O$ 中，因为 $r_0,s_0\in O$ 且 $F(X)\subseteq O$。实直线上的连通子集包含任意两点之间的整个区间，所以无论在 $Q^{-1}(4)\cap O$ 还是在 $Q^{-1}(4)$ 中，包含 $r_{2m}$ 与 $r_{2n}$ 的同一个连通分支都会被该中间点否定。这证明对所有 $m>n$ 的分支两两不同。有限个区间与单点的并至多有有限个连通分支，故有限连通片表示也被排除。证毕。

本定理由固定表、完整实际分支合同和交错收缩轨道推导；所用实直线连通子集的区间性质可参照第18章引用的 Munkres, Topology, §§23–24。证明只给出无限分支的见证，不给出全部分支数的上界；定理18.5的恰可数无穷结论仍独立地只针对定义18.1指定的 $Q$。有限输出字母表并不强制有限个空间连通片。这里的全称量词只遍历与定义17.1这张固定 $D$ 相容的 $Q$，不推广至任意五色解码表，也不推出有限精度可计算性、连续性、正扰动裕量、自主预测或物理时间与空间的起源。

## 追加锚（本行以下为增补区）

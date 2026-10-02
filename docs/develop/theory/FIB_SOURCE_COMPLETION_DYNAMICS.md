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
## 20. 任意五色解码表在归一化 $p=2$ 情形的局部无限分支

本章研究同一个五色观察函数在全部实际合法相邻样本上的精确解码，解码表可以任意选择。结论针对由共同尾和共享端点确定的归一化 $p=2$ 情形：在 $t/2$ 的每个足够小邻域中，颜色 $2,3$ 的两个限制纤维至少一个有无限多个连通分支。这个结论只依赖完整闭分支合同，不要求可测性、连续性或任何预定的颜色延伸规则。

### 20.甲 任意解码表、实际满域与端点归一化

**定义 20.1（任意五色表的完整实际合同）。** 置

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad
I=[-1,t],\quad O=[t,\phi],\quad X=[-1,\phi].
$$

使用恒等式

$$
t^2=1-t,\qquad 1+g=2t,\qquad
g^2+4g=1,\qquad 0<g<1.
$$

标签集为 $\Lambda=\{3,0,5,2,25\}$，颜色集为 $\mathcal C=\{1,2,3,4,5\}$。标签 $0$ 是三位窗 $000$，标签 $25$ 是单个三位窗 $101$；其余标签 $3,5,2$ 分别表示三位窗 $010,001,100$。颜色编号 $2,3$ 与 FIB 窗口标签 $2,3$ 属于不同的集合：$Q$ 的值是颜色，$D$ 的值是标签；给颜色改名不改变标签。

五个仿射分支为

$$
f_a(y)=\Delta_a-gy,\qquad
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t).
$$

标签 $3,0,2$ 的合法尾域是 $X$，标签 $5,25$ 的合法尾域是 $I$，全部端点均保留。本章的 $D:\mathcal C^2\to\Lambda$ 遍历任意确定解码表，$Q:X\to\mathcal C$ 遍历单值函数；合同为

$$
\begin{aligned}
D(Q(f_a(y)),Q(y))&=a
&&\text{对所有 }a\in\{3,0,2\},\ y\in X,\\
D(Q(f_a(y)),Q(y))&=a
&&\text{对所有 }a\in\{5,25\},\ y\in I.
\end{aligned}
$$

表的第一输入是当前颜色，第二输入是下一实际样本的颜色。同一个 $Q$ 用于两个相邻位置，也用于全部来源，公共标量点只能有一个颜色。这里不假设第17章的固定表或固定延伸规则。

沿用标量端点记号

$$
(e_0,e_1,e_2,e_3,e_4,e_5)=(-1,-t^2,g,t,2t,\phi).
$$

本章始终把 $A_0,A_1$ 留给定义14.5的实际地址空间，不以它们命名标量。对颜色同时重命名 $Q$ 和 $D$ 后，端点归一化写成

$$
Q(e_j)=j\quad(1\le j\le5),\qquad p=Q(e_0).
$$

这一归一化的合法性和 $p$ 的允许值由下一个引理给出。

**引理 20.2（实际满域、共同尾与全部端点约束）。** 定义20.1的闭分支合同等价于全部实际地址的精确相邻解码合同。共同实际尾 $e_0=-1$ 的五个当前颜色两两不同，所以端点归一化不损失任何五色实现。归一化后必有 $p\in\{2,4\}$，并且

$$
\begin{aligned}
D(1,p)&=3,& D(2,p)&=0,& D(3,p)&=5,&
D(4,p)&=2,& D(5,p)&=25,\\
D(p,5)&=3,& D(1,5)&=0,& D(3,5)&=2,&
D(2,3)&=5,& D(4,3)&=25.
\end{aligned}
$$

证明。定理17.2给出实际地址满像

$$
\kappa_0(A_0)=X,\qquad \kappa_1(A_1)=I,
\qquad A_1\subset A_0,
$$

并且 $\kappa_1(\eta)=\kappa_0(\eta)$ 对 $\eta\in A_1$ 成立。标签 $3,0,2$ 需要 guard 零的尾，标签 $5,25$ 需要 guard 一的尾。给定 $y\in I$，可取同一个 $\eta\in A_1$ 编码为 $y$；它同时是 $A_0$ 中的地址，因此 $3\eta,0\eta,5\eta,2\eta,25\eta$ 都从 guard 零合法出发。它们共用实际尾 $\eta$，当前值分别为 $f_a(y)$，删除首窗后的实际值全部是 $y$。给定 $y\in X$，同理可取 $\eta\in A_0$，同时前接 $3,0,2$。反向由任何实际地址的首窗及其自己的尾得到对应合法边。这说明全部闭域上的量词都由实际来源取得，不是把地址模型外的点补入合同。

五个完整分支像为

$$
\begin{aligned}
f_3(X)&=[e_0,e_1],& f_0(X)&=[e_1,e_2],&
f_5(I)&=[e_2,e_3],\\
f_2(X)&=[e_3,e_4],& f_{25}(I)&=[e_4,e_5].
\end{aligned}
$$

各分支严格单调，其输出端点只来自合法尾域的端点。因而全部输出落在这六个标量端点的边恰为下列十条，包含每个共享端点的两种合法来源。

| 第20章端点边 | 实际尾 | 标签 | 当前值 | 归一化后的合同 |
| --- | --- | --- | --- | --- |
| 20端点甲 | $e_0$ | $3$ | $e_1$ | $D(1,p)=3$ |
| 20端点乙 | $e_0$ | $0$ | $e_2$ | $D(2,p)=0$ |
| 20端点丙 | $e_0$ | $5$ | $e_3$ | $D(3,p)=5$ |
| 20端点丁 | $e_0$ | $2$ | $e_4$ | $D(4,p)=2$ |
| 20端点戊 | $e_0$ | $25$ | $e_5$ | $D(5,p)=25$ |
| 20端点己 | $e_5$ | $3$ | $e_0$ | $D(p,5)=3$ |
| 20端点庚 | $e_5$ | $0$ | $e_1$ | $D(1,5)=0$ |
| 20端点辛 | $e_5$ | $2$ | $e_3$ | $D(3,5)=2$ |
| 20端点壬 | $e_3$ | $5$ | $e_2$ | $D(2,3)=5$ |
| 20端点癸 | $e_3$ | $25$ | $e_4$ | $D(4,3)=25$ |

共同尾 $e_0$ 可由命题14.6的实际地址 $L=(3,25)^\infty\in A_1$ 取得。前接五个不同标签后的当前值为 $e_1,\ldots,e_5$。若其中两点同色，它们与同一个尾色 $Q(e_0)$ 组成相同的有序颜色对，却要求确定表输出两个不同标签，矛盾。因此五点恰用全部五色。取颜色置换 $\rho$ 把原来 $Q(e_j)$ 送到 $j$，同时将表变为 $(c,d)\mapsto D(\rho^{-1}(c),\rho^{-1}(d))$，便得到所述归一化，标签不变。

在共同实际尾 $e_5=\phi$，合法标签 $3,0,2$ 的三个当前颜色分别为 $p,1,3$，也必须两两不同，所以 $p\notin\{1,3\}$。若 $p=5$，共同尾 $e_0$ 的第一条边强制 $D(1,5)=3$，而尾 $e_5$ 的标签 $0$ 边强制 $D(1,5)=0$。同一个表格不能同时取标签 $3$ 与 $0$，排除 $p=5$。剩余恰为 $p\in\{2,4\}$。证毕。

**引理 20.3（同一实际尾色的整列确定性）。** 令 $S=Q(I)$。对每个 $c\in S$，映射 $d\mapsto D(d,c)$ 是从五种颜色到五个标签的双射。因此存在确定的总函数

$$
F,Z,H:S\longrightarrow S
$$

使对每个 $y\in I$ 都有

$$
Q(f_3(y))=F(Q(y)),\qquad
Q(f_0(y))=Z(Q(y)),\qquad
Q(f_5(y))=H(Q(y)).
$$

对每个 $c\in S$，三个颜色 $F(c),Z(c),H(c)$ 两两不同。本章的 $F$ 是颜色映射，不是第18、19章记为 $F$ 的标量分支 $f_2$。

证明。取 $y\in I$ 且 $Q(y)=c$。由引理20.2可给五个合法前接使用同一条实际尾地址。它们的五个当前颜色必须两两不同，因而恰是 $\mathcal C$；相应五个表值为五个不同标签。这证明第 $c$ 列是双射，也说明其结论不依赖选取哪一个具有颜色 $c$ 的尾点。若 $y,y'\in I$ 同色，则对任一标签 $a$，$Q(f_a(y))$ 与 $Q(f_a(y'))$ 是该列中标签 $a$ 唯一对应的行色，故必相等。

三个分支在 $I$ 上的像为

$$
f_3(I)=[-2t^2,-t^2],\qquad
f_0(I)=[-t^4,g],\qquad
f_5(I)=[g,t].
$$

这些区间都包含于 $I$，所以标签 $3,0,5$ 的确定行色仍在 $S$ 中，定义了所述三个总函数。同一列不同标签对应不同行色，给出两两不同。证毕。

### 20.乙 三个实际收缩固定点强制尾域五色齐全

**引理 20.4（$p=2$ 的三个不交固定色集合）。** 在定义20.1的合同及归一化 $p=2$ 下，置

$$
h=\frac t2,\qquad u=-\frac34,\qquad v=-\frac{t^2}{4}.
$$

三个映射 $f_5,f_3\circ f_5,f_0\circ f_5$ 都是 $I$ 上的合法自收缩，固定点依次为 $h,u,v$，且

$$
-1<u<v<0<h<t.
$$

令 $r=Q(h)$、$s=Q(u)$、$k=Q(v)$，则

$$
H(2)=3,\qquad H(3)=2,\qquad
H(r)=r,\quad F(H(s))=s,\quad Z(H(k))=k,
$$

$$
\{r,s,k\}=\{1,4,5\},\qquad Q(I)=\mathcal C.
$$

这一结论不使用任何正则性假设。

证明。端点 $f_5(e_0)=e_3$ 与 $f_5(e_3)=e_2$，结合 $Q(e_0)=2$、$Q(e_3)=3$、$Q(e_2)=2$ 及引理20.3，给出 $H(2)=3$、$H(3)=2$。

由 $1+g=2t$ 得

$$
f_5(h)=t^2-g\frac t2=\frac t2=h.
$$

两个复合的公式为

$$
(f_3\circ f_5)(y)=-t-gt^2+g^2y,
\qquad (f_0\circ f_5)(y)=-gt^2+g^2y.
$$

恒等式 $t+gt^2=3g$ 与 $1-g^2=4g$ 给出其固定点

$$
\frac{-t-gt^2}{1-g^2}=-\frac34=u,\qquad
\frac{-gt^2}{1-g^2}=-\frac{t^2}{4}=v.
$$

引理20.3的像区间保证每一步留在 $I$，收缩比分别为 $g,g^2,g^2$。又 $1/2<t<1$、$0<t^2<1/2$，所以所列三点严格位于 $I$ 内并满足上述次序。这些不是只在颜色图中存在的形式固定点：实际周期地址 $5^\infty$、$(3,5)^\infty$、$(0,5)^\infty$ 都从 guard 一合法出发，分别沿 $5:1\to1$、$3:1\to0$ 后接 $5:0\to1$、$0:1\to0$ 后接 $5:0\to1$ 循环。其编码分别满足这三个固定点方程，收缩唯一性给出编码 $h,u,v$。它们因此都是实际合法的 $I$ 点。

对三个固定点应用颜色确定性，得到 $H(r)=r$、$F(H(s))=s$、$Z(H(k))=k$。为同时核对固定颜色的不同性与排除项，定义

$$
\begin{aligned}
R_H&=\{c\in S:H(c)=c\},\\
R_{FH}&=\{c\in S:F(H(c))=c\},\\
R_{ZH}&=\{c\in S:Z(H(c))=c\}.
\end{aligned}
$$

三个集合分别含 $r,s,k$，所以均非空。它们两两不交：若 $c\in R_H\cap R_{FH}$，则 $F(c)=H(c)=c$，违反同一输入的不同输出；$R_H\cap R_{ZH}$ 同理。若 $c\in R_{FH}\cap R_{ZH}$，则在合法颜色输入 $H(c)\in S$ 处有 $F(H(c))=Z(H(c))$，仍矛盾。

它们都避开颜色 $2,3$。$H$ 在这两色上交换，故 $R_H$ 不含它们。对 $c\in\{2,3\}$，有 $H(H(c))=c$；若 $F(H(c))=c$，便有 $F(H(c))=H(H(c))$，违反输入 $H(c)$ 处的不同输出；$Z$ 的情形相同。于是三个集合是不交的非空子集，全部包含于只有三个元素的 $\{1,4,5\}$。它们各为单点，其并恰为 $\{1,4,5\}$，从而 $r,s,k$ 恰用这三色。颜色 $2,3$ 已在 $e_0,e_3\in I$ 出现，所以 $S=\mathcal C$。证毕。

### 20.丙 穿孔局部常值性与两个端点反证

**定义 20.5（两侧局部常值、有限连通片与限制纤维）。** 称 $Q$ 在 $h=t/2$ 两侧分别具有常值穿孔邻域，是指存在 $0<\eta_-,\eta_+<t/2$ 和颜色 $c_-,c_+$，使

$$
Q(x)=c_-\quad(h-\eta_-<x<h),\qquad
Q(x)=c_+\quad(h<x<h+\eta_+).
$$

这个条件不规定 $Q(h)$，也不要求两侧颜色相同。称 $Q$ 有有限连通片表示，是指每个颜色纤维都是有限个实区间与单点的并，区间可以采用任意开闭端点。对 $0<\epsilon<t/2$，记

$$
J_\epsilon=(h-\epsilon,h+\epsilon)\subset I,\qquad
E_{c,\epsilon}=Q^{-1}(c)\cap J_\epsilon.
$$

限制纤维的连通分支指 $E_{c,\epsilon}$ 在实直线通常拓扑中的极大连通子集。以下结论中的“无限多个”只排除有限个，不给出分支基数的上界。

**引理 20.6（局部常值假设下的 $I$ 内侧分离与单点纤维）。** 假设完整合同、归一化 $p=2$，并假设定义20.5的两侧局部常值性。则左、右常值分别是颜色 $2,3$。任意颜色不能同时在 $I$ 中的 $h$ 两侧出现，并且对引理20.4的 $r,s,k$ 有

$$
Q^{-1}(r)\cap I=\{h\},\qquad
Q([-1,h))=\{2,s,k\},\qquad
Q((h,t])=\{3\}.
$$

这里的侧分离和单点纤维结论均只在 $I$ 内成立。

证明。$f_5(h)=h$ 给出对 $x\in I$ 的实际迭代公式

$$
f_5^n(x)=h+(-g)^n(x-h).
$$

全部迭代留在 $I$，所以颜色满足 $Q(f_5^n(x))=H^n(Q(x))$。从实际尾点 $-1$ 出发，颜色交换律给出

$$
\begin{aligned}
f_5^{2n}(-1)&=h-g^{2n}(1+h)<h,
&Q(f_5^{2n}(-1))&=2,\\
f_5^{2n+1}(-1)&=h+g^{2n+1}(1+h)>h,
&Q(f_5^{2n+1}(-1))&=3.
\end{aligned}
$$

两列分别从左、右趋近 $h$，故假定的左侧常值只能是 $2$，右侧常值只能是 $3$。

若存在 $x,y\in I$ 满足 $x<h<y$ 且 $Q(x)=Q(y)=c$，则对每个 $n$，

$$
Q(f_5^{2n}(x))=H^{2n}(c)=Q(f_5^{2n}(y)).
$$

偶数迭代保持两侧，且两点都趋近 $h$；充分大时它们分别落入左右常值邻域，颜色应分别为 $2,3$，矛盾。这证明只在 $I$ 内的同色侧分离。

再取 $x\in I$ 且 $Q(x)=r$。因为 $H(r)=r$，所有迭代都保持颜色 $r$。若 $x\ne h$，则迭代从不等于 $h$，且最终进入穿孔常值邻域，必须取色 $2$ 或 $3$；但 $r\in\{1,4,5\}$，矛盾。因此 $Q^{-1}(r)\cap I=\{h\}$。

颜色 $2$ 在 $-1<h$ 出现，颜色 $s,k$ 分别在 $u,v<h$ 出现；侧分离使它们不能在右侧出现。颜色 $r$ 又只在 $h$ 出现。五色已由 $\{2,3,r,s,k\}$ 用尽，故右侧只允许颜色 $3$；$t>h$ 确实取色 $3$。反过来，颜色 $3$ 既已在右侧出现，便不能在左侧出现，颜色 $r$ 也不能在那里出现。三个左侧见证保证左侧像恰为 $\{2,s,k\}$。证毕。

**引理 20.7（$p=2$ 不允许两侧分别局部常值）。** 对定义20.1的任意 $D,Q$，若归一化 $p=2$，则 $Q$ 在 $h=t/2$ 两侧不能分别具有常值穿孔邻域。

证明。反设具有该性质，应用引理20.4和20.6。端点 $e_1=-t^2<h$ 取色 $1$，而 $Q^{-1}(r)\cap I=\{h\}$，故 $r\ne1$。由于 $r\in\{1,4,5\}$，只剩以下两种情况。

若 $r=4$，则 $\{s,k\}=\{1,5\}$。取实际固定点 $y_*\in\{u,v\}$ 中取色 $5$ 的那个；它在 $I$ 中且 $y_*<h$。合法分支 $f_5$ 把它送到

$$
f_5(y_*)=h-g(y_*-h)\in(h,t].
$$

该点取色 $3$，所以这条实际标签 $5$ 边要求

$$
D(3,5)=5.
$$

另取实际尾 $\phi=e_5$，其色也是 $5$；合法标签 $2$ 满足 $f_2(\phi)=t=e_3$，当前色为 $3$，所以这条实际边要求

$$
D(3,5)=2.
$$

这两个尾标量不同，却有同一尾色 $5$，相同有序颜色对必须解出不同标签，矛盾。第一条边由 $A_1$ 中编码为 $y_*$ 的尾前接 $5$ 得到，第二条边由实际尾 $R=(25,3)^\infty\in A_0$ 前接 $2$ 得到。$\phi\notin I$，这里没有对 $\phi$ 使用标签 $5$，也没有将颜色函数 $H$ 的 $I$ 内规则当作 $\phi$ 的非法分支规则。

若 $r=5$，则 $\{s,k\}=\{1,4\}$，左侧恰允许颜色 $\{1,2,4\}$。在同一个实际尾点 $t\in I$，五个标签均合法。其中

$$
f_3(t)=-2t^2<h,\qquad f_0(t)=-t^4<h,
$$

且两点都在 $I$ 内，所以它们的颜色均属于 $\{1,2,4\}$。另外两个当前值已经固定为

$$
f_5(t)=g=e_2,\qquad Q(f_5(t))=2,
$$

$$
f_{25}(t)=2t=e_4,\qquad Q(f_{25}(t))=4.
$$

引理20.3的同尾五输出不同性使 $f_3(t),f_0(t)$ 都不能取色 $2$ 或 $4$，于是两点都只能取色 $1$，再次违反同尾不同性。共同实际尾可以取命题14.6的 $U=5L\in A_1$，因此这五条边确实共享同一条实际地址尾，不是分别指定的最优实现。

两种允许的 $r$ 都矛盾，反设不成立。证毕。

### 20.丁 局部无限分支定理与有限连通片障碍

**定理 20.8（任意解码表的 $p=2$ 局部无限分支）。** 设 $t,\phi,g,I,X,f_a,\Lambda$ 如定义20.1，$Q:X\to\mathcal C$ 和任意确定表 $D:\mathcal C^2\to\Lambda$ 对全部合法闭分支满足

$$
D(Q(f_a(y)),Q(y))=a.
$$

按共同实际尾 $-1$ 的五个当前点归一化为 $Q(e_j)=j$（$1\le j\le5$），并假设 $Q(-1)=2$。则 $Q(I)=\mathcal C$，$Q$ 在 $h=t/2$ 两侧不能分别具有常值穿孔邻域；而且对每个 $0<\epsilon<t/2$，集合

$$
Q^{-1}(2)\cap(h-\epsilon,h+\epsilon),\qquad
Q^{-1}(3)\cap(h-\epsilon,h+\epsilon)
$$

至少一个有无限多个连通分支。定理不要求 $Q$ 可测，也不要求其他正则性。

证明。引理20.4给出 $Q(I)=\mathcal C$，引理20.7给出局部常值障碍。剩下须从这一障碍推出每个指定邻域内的分支结论，不能用全域无限性替代局部无限性。

固定 $0<\epsilon<t/2$，反设 $E_{2,\epsilon}$ 和 $E_{3,\epsilon}$ 都只有有限多个连通分支。令

$$
x_n=f_5^{2n}(-1)=h-g^{2n}(1+h),\qquad
 y_n=f_5^{2n+1}(-1)=h+g^{2n+1}(1+h).
$$

由端点交换律及实际合法迭代，$Q(x_n)=2$、$Q(y_n)=3$。又 $x_n\uparrow h$ 且 $y_n\downarrow h$，所以两列在充分大后分别落入 $E_{2,\epsilon}$、$E_{3,\epsilon}$。

第一列的无穷多个点分布在有限多个分支中，至少一个分支 $C_2$ 含有无穷子列。取其中一点 $x_N\in C_2$。对任何 $x_N<x<h$，该子列趋近 $h$，所以可取同在 $C_2$ 的更后一点 $x_n>x$。实直线的连通子集包含任意两点之间的整段，故 $x\in C_2$。这证明

$$
(x_N,h)\subseteq C_2\subseteq E_{2,\epsilon},
$$

即某个完整左侧穿孔邻域恒为色 $2$。

同理，$E_{3,\epsilon}$ 的一个分支 $C_3$ 含有 $y_n$ 的无穷子列。取 $y_M\in C_3$；对任何 $h<y<y_M$，可取该子列中更后一点 $y_m<y$，连通性给出 $y\in C_3$。因此

$$
(h,y_M)\subseteq C_3\subseteq E_{3,\epsilon},
$$

某个完整右侧穿孔邻域恒为色 $3$。两个区间均在 $J_\epsilon$ 内，满足定义20.5，与引理20.7矛盾。故这两个限制纤维不能同时只有有限个连通分支，至少一个必有无限多个。$\epsilon$ 任意，所述量词成立。证毕。

**推论 20.9（归一化 $p=2$ 的有限连通片非存在性）。** 在定理20.8的完整实际合同下，不存在有限连通片表示的五色观察函数。更具体地，颜色 $2$ 与颜色 $3$ 的两个全域纤维不能同时各为有限个实区间与单点的并。

证明。若两个纤维都有这种表示，将每个区间或单点与 $J_\epsilon$ 相交，仍为区间、单点或空集。故 $E_{2,\epsilon},E_{3,\epsilon}$ 都是有限个连通集的并。有限个连通集的并至多有有限个连通分支：每个非空连通集位于并集的一个分支内，每个分支至少包含其中一个集合。这与定理20.8矛盾。有限连通片五色表示特别使这两个纤维都具有所述有限表示，因此也被排除。证毕。

### 20.戊 结论范围与数学依据

定理20.8的颜色 $2,3$ 是由共同尾五输出确定的归一化颜色编号，不是 FIB 标签。其无限分支结论的精确量词为：对每个 $0<\epsilon<t/2$，两个限制颜色纤维至少一个有无限多个分支。它不宣称两者都无限，不指定这两个纤维的分支基数为可数无穷，也不指定颜色 $4$ 承担无限分支。侧分离和固定色 $r$ 的单点纤维是局部常值反设下在 $I$ 内的中间结论，不是对 $X$ 上任意同色点的限制。

引理20.2只把端点归一化归结为 $p=2$ 或 $p=4$；本章排除了 $p=2$ 的有限连通片合同，$p=4$ 情形仍在本章定理之外。因此任意解码表的普遍有限连通片非存在性并未由本章解决。本章也不构造不规则的 $p=2$ 实现，不结算这种实现本身的存在性。第19章固定表下的颜色 $4$ 障碍、第18章指定函数的精确可数分支，以及第16章连通、等宽、噪声与取得数量的上下界，各自保留原合同；不能将这些不同条件合并为一个任意表的结论。

实际满像、完整闭域与同一实际尾的共同前接使用定义14.5、命题14.6和定理17.2。三个实际周期固定点、整列确定性、固定色集合不交、局部常值反证及局部分支结论由本章给出。实直线连通子集包含两点间整段的性质可参照第18章引用的 J. R. Munkres, Topology, 2nd ed., §§23–24；这里不依赖可测性，也不作原创优先性断言。

结论属于已经定义的 FIB 地址、精确实样本和有限颜色合同，不给出有限精度计算算法、连续性、正噪声裕量或全局自主预测，也不建立五窗与五种普遍几何操作的对应，不推出物理时间或物理空间的起源。

## 追加锚（本行以下为增补区）

## 21. 任意五色解码表的无限空间连通分支与有限连通片六色界

本章沿用定义20.1的同一标量观察函数与任意解码表合同，补足归一化 $p=4$ 的两种尾域颜色情形。结合定理20.8和推论20.9，得到：每个精确五色实现至少有一个颜色纤维含无限多个连通分支；如果要求每色只有有限多个连通分支，最小颜色数恰为六。这里的精确解码始终针对全部实际合法闭分支，包括共享端点和共同实际尾。

### 21.甲 合同、统一记号与有限连通片的局部性质

使用定义20.1的常数、标量端点和分支：

$$
\begin{gathered}
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad g=t^3=2t-1,\\
I=[-1,t],\qquad O=[t,\phi],\qquad X=[-1,\phi],\\
(e_0,e_1,e_2,e_3,e_4,e_5)=(-1,-t^2,g,t,2t,\phi),\\
f_a(y)=\Delta_a-gy,\qquad
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})=(-t,0,t^2,1,2-t).
\end{gathered}
$$

颜色集是 $\mathcal C=\{1,2,3,4,5\}$，FIB 标签集是 $\Lambda=\{3,0,5,2,25\}$。标签 $0$ 表示窗口 $000$，标签 $25$ 表示窗口 $101$；数值相同的颜色编号和标签仍是不同对象。标量端点一律记为 $e_j$，不占用实际地址空间 $A_0,A_1$ 的名称。任意函数 $Q:X\to\mathcal C$ 和同一确定表 $D:\mathcal C^2\to\Lambda$ 必须满足

$$
\begin{aligned}
D(Q(f_a(y)),Q(y))&=a
&& (a\in\{3,0,2\},\ y\in X),\\
D(Q(f_a(y)),Q(y))&=a
&& (a\in\{5,25\},\ y\in I).
\end{aligned}
$$

第一输入是当前颜色，第二输入是实际尾颜色。引理20.2保证此合同与全部实际地址的相邻解码等价，并允许归一化

$$
Q(e_j)=j\quad(1\le j\le5),\qquad p=Q(e_0)\in\{2,4\}.
$$

本章不重新证明该端点归一化，也不重新证明 $p=2$ 的局部障碍；其完整依据分别是引理20.2和定理20.8、推论20.9。

令 $S=Q(I)$。依引理20.3，每个 $c\in S$ 的第 $c$ 列是五颜色到五标签的双射。统一记颜色变换

$$
(F,Z,H,R,P)=(T_3,T_0,T_5,T_2,T_{25}).
$$

这里 $F,Z,H:S\to S$，$R,P:S\to\mathcal C$；对合法尾 $y\in I$，有 $Q(f_a(y))=T_a(Q(y))$。若 $Q(y)\in S$，标签 $3,0,2$ 的同一列唯一性也适用于 $y\in X$，而标签 $5,25$ 仍只用于 $y\in I$。在 $S=\mathcal C$ 时，$F,Z,R$ 因而在全部 $X$ 上确定；在 $S=\{1,2,3,4\}$ 时，不预设尾色 $5$ 的标签 $2$ 输出确定。复合记号一律右先左后，例如 $FZ=F\circ Z$。这些符号都是颜色函数，实际标量映射始终写成 $f_a$ 或其复合。

实际类型和像区间为

$$
\begin{aligned}
f_3(X)&=[e_0,e_1]\subset I,&
f_0(X)&=[e_1,e_2]\subset I,\\
f_5(I)&=[e_2,e_3]\subset I,&
f_{25}(I)&=[e_4,e_5]\subset O,\\
f_2(I)&=[1-gt,2t]=[3t-1,2t]\subset O,&
f_2(X)&=[t,2t]\subset X.
\end{aligned}
$$

$f_2$ 的实际固定点是 $z=\phi/2\in(t,\phi)$，不在 $I$ 中；因此 $f_2$ 的自收缩论证使用 $X$，不能把 $f_2(I)$ 当成 $I$ 自映射。

**引理 21.1（有限连通片与两侧局部常值）。** 对非退化紧区间 $J$ 上的有限颜色函数，若每个颜色纤维只有有限多个连通分支，则每个纤维是有限个实区间与单点的并。这样的函数在每个内点的左、右两侧分别具有常值穿孔邻域，在两个外端点具有单侧常值穿孔邻域；点本身的颜色不受这些邻域常值限制。

证明。实直线的每个连通子集包含其任意两点之间的整段，所以非空连通分支是区间或单点。各纤维只有有限多个分支，便给出所述有限表示。反过来，有限个区间与单点的并也只有有限多个连通分支，因为每个非空连通集属于并集的一个分支，而每个分支至少包含其中一个集合。

收集全部有限表示中的区间端点及单点，得到有限集合 $B\subset J$。在 $J\setminus B$ 的每个区间上，各纤维的成员资格不变，故函数恒色。对任意指定点，可在其左右各取足够短而不含 $B$ 中其他点的区间；端点只取位于 $J$ 内的一侧。这证明局部常值性，不要求指定点属于相邻区间的颜色。证毕。

**引理 21.2（一般紧区间上的负收缩不变色轨道）。** 设 $J=[a,b]$、$a<b$，$Q$ 在 $J$ 上有有限连通片表示，且

$$
G:J\to J,\qquad G(x)=\alpha-\lambda x,\qquad 0<\lambda<1.
$$

令 $z_G=\alpha/(1+\lambda)$ 为实际固定点。只假设某个颜色 $c$ 的类前向不变，且具有非固定实现点：

$$
G\bigl(Q^{-1}(c)\cap J\bigr)\subseteq Q^{-1}(c)\cap J,
\qquad Q(x_c)=c,\quad x_c\ne z_G.
$$

则 $z_G\in(a,b)$，且 $Q$ 在 $z_G$ 左、右两个充分小的穿孔邻域都恒为 $c$。本引理不要求存在全局确定的颜色变换，也不要求 $Q(z_G)=c$。

证明。$G(J)\subseteq J$ 给出 $G(a)\ge a$、$G(b)\le b$，从而固定点属于 $J$。若 $z_G=a$，则 $G(b)=a-\lambda(b-a)<a$；若 $z_G=b$，则 $G(a)=b+\lambda(b-a)>b$。两种情形都违反自映射性，故固定点在内部。

实际迭代公式为

$$
G^n(x_c)=z_G+(-\lambda)^n(x_c-z_G).
$$

它从不等于 $z_G$，始终保持颜色 $c$，交替位于固定点的两侧并趋近固定点。引理21.1给出两侧各自的最终常值。奇、偶子列分别进入这两个邻域，迫使两侧常值都等于 $c$。轨道不访问固定点本身，所以没有对 $Q(z_G)$ 加入要求。证毕。

**推论 21.3（确定颜色变换的吸引根）。** 在引理21.2的条件下，另外设有限颜色集 $C=Q(J)$ 上有确定变换 $T:C\to C$，满足 $Q(G(x))=T(Q(x))$。若 $T(c)=c$，颜色 $c$ 有非固定实现点，且每个颜色都在非固定点实现，则每个颜色的 $T$ 轨道最终进入 $c$；$c$ 是唯一固定颜色，且没有非平凡颜色周期。特别地，若每个颜色在 $J$ 中有非空开区间实现，则 $T$ 有唯一吸引根。

证明。$T(c)=c$ 使颜色 $c$ 前向不变，所以引理21.2强制固定点两侧恒为 $c$。对任意颜色 $d$，选非固定实现点 $x_d$。其实际轨道永不命中固定点，最终进入两侧常值邻域，故

$$
T^n(d)=Q(G^n(x_d))=c
$$

对所有充分大的 $n$ 成立。另一固定颜色或非平凡周期都不能最终进入 $c$。若每色有开区间，实际固定点的颜色 $c_0=Q(z_G)$ 满足 $T(c_0)=c_0$，且其开区间内可选非固定点；每个其他颜色也可作同样选择，于是前面的论证应用于 $c_0$。在这一确定变换推论中，$Q(z_G)$ 必等于唯一根；这不是引理21.2单独作出的结论。证毕。

**引理 21.4（正收缩的无周期规则）。** 若有限连通片函数 $Q:J\to C$（其中 $C=Q(J)$）与正斜率仿射自收缩 $G(x)=\alpha+\lambda x$、$0<\lambda<1$ 满足 $QG=TQ$，则 $T$ 没有长度至少二的颜色周期。

证明。设 $d$ 属于这样的周期，取 $Q(x)=d$。实际固定点若等于 $x$，则 $T(d)=d$，与非平凡周期矛盾。因此 $x\ne z_G$，且

$$
G^n(x)=z_G+\lambda^n(x-z_G)
$$

保持在固定点同一侧并趋近它。引理21.1在该侧给出最终常值，使 $T^n(d)$ 最终恒定，与周期矛盾。若固定点位于 $J$ 的端点，使用其内侧邻域即可。证毕。

### 21.乙 四尾色的端点邻域、非确定出口与实际固定色集合

以下假设有限连通片表示、$p=4$ 和 $S=\{1,2,3,4\}$。颜色 $5$ 只在 $O\setminus I$ 出现。对每个 $c\in S$，前三个输出属于 $S$，五个输出又两两不同，所以存在唯一遗漏色 $q(c)\in S$，使

$$
(F(c),Z(c),H(c),q(c))\text{ 是 }(1,2,3,4)\text{ 的排列},
\qquad \{R(c),P(c)\}=\{q(c),5\}.
$$

**引理 21.5（四尾色的必要表项、端点邻域与吸收条件）。** 在上述条件下，必有 $D(2,5)=2$，且存在 $\epsilon_-,\epsilon_+>0$ 使

$$
Q=4\text{ 在 }(-1,-1+\epsilon_-),\qquad
Q=5\text{ 在 }(\phi-\epsilon_+,\phi).
$$

确定颜色数据为

$$
\begin{array}{c|ccccc}
c&F(c)&Z(c)&H(c)&R(c)&P(c)\\\hline
3&a&4-a&2&5&4\\
4&1&2&3&4&5
\end{array}
\qquad a\in\{1,3\}.
$$

尾色 $5$ 的 $f_3,f_0$ 输出分别唯一为颜色 $4,1$。以

$$
\widehat F|_S=F,\quad \widehat F(5)=4,
\qquad \widehat Z|_S=Z,\quad \widehat Z(5)=1
$$

定义实际复合诱导的总函数

$$
A=\widehat F R,\qquad B=\widehat F P,\qquad C=\widehat ZR:S\to S.
$$

它们分别对应 $f_3f_2,f_3f_{25},f_0f_2:I\to I$，并满足

$$
\begin{gathered}
A(3)=4,\quad A(4)=1,\qquad
B(3)=1,\quad B(4)=4,\qquad
C(3)=1,\quad C(4)=2,\\
\forall c\in S\quad \exists n\ge0\quad B^n(c)=4.
\end{gathered}
$$

证明。引理20.2给出完整的第 $4$ 列，得到色 $4$ 的整行变换数据。尾色 $3$ 的标签 $5,25$ 已输出颜色 $2,4$，故 $F(3),Z(3)$ 只能是 $1,3$；余下的标签 $2$ 输出颜色 $5$。这给出所列两行。

第 $4$ 列的标签 $2$ 只有颜色 $4$ 这一行。因此对全部 $y\in X$，只要 $Q(y)=4$ 就有 $Q(f_2(y))=4$。这是 $X$ 上的前向不变颜色类。实际点 $e_4=2t$ 取色 $4$，且不同于 $f_2$ 的固定点 $z=\phi/2$。引理21.2应用于 $J=X$，强制 $z$ 两侧充分小的穿孔邻域都恒为 $4$。

从实际尾 $\phi$ 出发的 $f_2$ 轨道不命中 $z$，故最终进入颜色 $4$ 的邻域。其第一步为 $\phi\mapsto t$，颜色 $5\mapsto3$；在尾色 $3$ 时下一颜色确定为 $5$。引理20.2又给出

$$
D(1,5)=0,\qquad D(3,5)=2,\qquad D(4,5)=3.
$$

所以尾色 $5$ 的标签 $2$ 当前色只可能属于 $\{2,3,5\}$。若 $D(2,5)\ne2$，集合 $\{3,5\}$ 对所有实际标签 $2$ 出口前向封闭，轨道不可能进入颜色 $4$，矛盾。因此 $D(2,5)=2$。这个论证允许色 $5$ 有不止一个标签 $2$ 出口，没有将它定义成确定的颜色函数。

现在第 $5$ 列在行 $1,2,3,4$ 的值为

$$
(D(1,5),D(2,5),D(3,5),D(4,5))=(0,2,2,3).
$$

$f_3,f_0$ 的输出属于 $I$，在那里没有颜色 $5$，故尾色 $5$ 的两种输出唯一为 $4,1$。这证明 $\widehat F,\widehat Z$ 的合法性。三个复合均先从 $I$ 到 $O$，再用全 $X$ 合法的 $f_3$ 或 $f_0$ 回到 $I$，因此 $A,B,C$ 的实际类型和确定性成立。代入两行已定数据得到它们的端点颜色值。

还需证明端点邻域，不能只使用抽象颜色表。有限连通片表示在非退化区间 $I$ 内至少给出一个恒色非空开区间 $U$：否则各色只含有限个点，不能覆盖 $I$。取其颜色 $c\in S$。五个 $f_a(U)$ 都是非空开区间，颜色分别为该列的五种不同输出。因此颜色 $5$ 在 $O$ 中有非空开区间 $U_5$。$f_3(U_5)$ 是 $I$ 内颜色 $4$ 的非空开区间，包含一个 $x_4>-1$。

实际复合满足

$$
G_B(y)=(f_3f_{25})(y)=-1+g^2(y+1),\qquad B(4)=4.
$$

$x_4$ 的全部 $G_B$ 迭代保持颜色 $4$，从右侧趋近 $-1$。引理21.1的端点单侧常值性迫使 $-1$ 的充分小右邻域恒为 $4$。对这个邻域应用 $f_{25}(-1+s)=\phi-gs$，并使用 $P(4)=5$，得到 $\phi$ 的充分小左邻域恒为 $5$。

最后，对任意 $c\ne4$ 选实际点 $x_c\in I$ 取色 $c$，它必满足 $x_c>-1$。$G_B^n(x_c)$ 从右侧趋近 $-1$，最终进入颜色 $4$ 的邻域，所以 $B^n(c)=4$。对颜色 $4$ 直接使用 $B(4)=4$。这证明全部颜色的 $B$ 吸收条件。证毕。

**引理 21.6（四尾色的普遍无非平凡周期规则）。** 设 $T:S\to S$ 由合法实际收缩复合

$$
w=f_a\circ v:I\to I,\qquad a\in\{3,0,5\}
$$

诱导，其中 $v:I\to I$ 是合法分支复合或恒等映射，并诱导确定颜色变换 $V$。则 $T=T_aV$ 没有长度至少二的颜色周期。这一结论不需要有限连通片假设。

证明。反设存在长度 $m\ge2$ 的周期，其不同颜色组成 $E\subset S$，$|E|=m$。令 $b,c$ 为 $\{3,0,5\}\setminus\{a\}$ 中的另外两个标签，定义

$$
L_b=T_bVT^{m-1},\qquad L_c=T_cVT^{m-1}.
$$

$T,L_b,L_c$ 分别由 $w,f_bvw^{m-1},f_cvw^{m-1}$ 诱导。这三个实际映射都是闭区间 $I$ 的仿射自收缩，各有一个实际固定点；其 $Q$ 颜色使相应颜色变换固定。因此

$$
\operatorname{Fix}(T),\qquad \operatorname{Fix}(L_b),\qquad
\operatorname{Fix}(L_c)
$$

都是非空集合。它们两两不交：$L_b,L_c$ 对同一颜色输入的最外层输出不同；若 $T(d)=d$，则 $T^{m-1}(d)=d$，且

$$
T_b(V(d))\ne T_a(V(d))=d,\qquad
T_c(V(d))\ne T_a(V(d))=d.
$$

它们也全部避开 $E$。$T$ 不固定周期中的任何颜色；对 $d\in E$，同列不同输出给出

$$
L_b(d)\ne T_a(V(T^{m-1}(d)))=T^m(d)=d,
$$

$L_c$ 同理。因此 $E$ 外还必须容纳三个两两不交的非空实际固定色集合，总共至少需要 $m+3\ge5$ 种颜色，与 $|S|=4$ 矛盾。证毕。

本引理适用于 $F,Z,H$（内层取恒等映射），也适用于下文全部 $FA,ZA,HA,FC,ZC,HZA$。$A,C$ 的实际映射是 $I\to O\to I$ 的自收缩；在它们之后附加 $f_3,f_0,f_5$，仍是合法 $I$ 自收缩。$HZA$ 的内层是 $f_0f_3f_2:I\to I$，最外层是 $f_5$，也符合引理。另一个所需事实是：任何确定的实际仿射自收缩 $I\to I$ 都有至少一个固定颜色；这直接来自其实际固定点，即使它没有引理所要求的最外层类型。下文对 $C$ 使用这个较弱事实。

### 21.丙 四尾色的两条路径与全部表项排除

**定理 21.7（$p=4$、四尾色的有限连通片非存在性）。** 定义20.1的任意表合同在归一化 $p=4$、$Q(I)=\{1,2,3,4\}$ 下，不存在有限连通片表示的 $Q$。

证明。采用引理21.5、21.6的必要条件。尾色 $5$ 经标签 $2$ 可以输出 $2,3,5$，尾色 $3$ 唯一输出 $5$。从 $\phi$ 出发的实际标签 $2$ 轨道最终到达颜色 $4$，所以必须有一次从颜色 $5$ 退出到颜色 $2$。

若 $R(2)\in\{2,3,5\}$，集合 $\{2,3,5\}$ 对全部允许的实际出口前向封闭，无法进入 $4$。故 $R(2)\in\{1,4\}$。若 $R(2)=1$ 而 $R(1)\ne4$，则 $\{1,2,3,5\}$ 同样前向封闭，仍不能进入 $4$。因此两种必要路径穷尽如下；色 $5$ 的非确定自返或回到 $3$ 不增加第三种退出路径。

| 第21章四尾路径 | $q(2)$ | $R(2)$ | $P(2)$ | 额外条件 |
| --- | --- | --- | --- | --- |
| 21四尾型 I | $1$ | $1$ | $5$ | $q(1)=4,\ R(1)=4,\ P(1)=5$ |
| 21四尾型 II | $4$ | $4$ | $5$ | 无额外指定 |

两型均有 $B(2)=4$。又 $B(3)=1,B(4)=4$，每色最终被 $B$ 吸收到 $4$。故 $B(1)$ 不能为 $1$（固定在 $1$），也不能为 $3$（形成 $1\leftrightarrow3$），所以 $B(1)\in\{2,4\}$。写 $d=q(1)$，得到规则

$$
F(d)\notin\{2,4\}\quad\Longrightarrow\quad
P(1)=5,\ R(1)=d,\ A(1)=F(d).
\tag{21甲}
$$

因为另一可能 $P(1)=d$ 会给出 $B(1)=F(d)$，违反吸收条件。

型 I。此时

$$
\{F(1),Z(1),H(1)\}=\{1,2,3\},\qquad
\{F(2),Z(2),H(2)\}=\{2,3,4\}.
$$

由 $H(3)=2,H(4)=3$，$H(2)=3$ 会产生二周期，$H(2)=4$ 会产生三周期。引理21.6故强迫 $H(2)=2$。于是 $\{F(2),Z(2)\}=\{3,4\}$；$Z(2)=4$ 与 $Z(4)=2$ 形成二周期，故

$$
Z(2)=3,\qquad F(2)=4.
$$

若 $F(1)=2$，$F$ 有 $1\to2\to4\to1$；若 $F(1)=3$，由 $A(1)=F(4)=1,A(3)=4$，$FA$ 有 $1\leftrightarrow3$。故 $F(1)=1$，$Z(1)\in\{2,3\}$。若 $Z(3)=1$，$Z(1)=2$ 会产生 $1\to2\to3\to1$，$Z(1)=3$ 会产生 $1\leftrightarrow3$。故 $Z(3)=3$，从而

$$
(C(1),C(2),C(3),C(4))=(2,Z(1),1,2).
$$

若 $Z(1)=2$，则 $(ZC)(2)=3,(ZC)(3)=2$，违反引理21.6。若 $Z(1)=3$，则 $C=(2,3,1,2)$ 没有任何固定颜色，违反实际收缩 $f_0f_2:I\to I$ 的固定点性质。型 I 的全部取值被排除。

型 II。现在 $q(2)=4,R(2)=4,P(2)=5$，故

$$
\{F(2),Z(2),H(2)\}=\{1,2,3\},\qquad
A(2)=1,\ A(3)=4,\ C(2)=2,\ C(3)=1.
\tag{21乙}
$$

$H(2)=3$ 与 $H(3)=2$ 形成二周期，只剩 $H(2)=1$ 或 $2$。

先设 $H(2)=1$。已定链为 $4\to3\to2\to1$，无非平凡周期强迫 $H(1)=1$。若 $F(3)=1$，则 $Z(3)=3$。$F(1)$ 不能为 $1$（同列已有 $H(1)=1$）、$3$ 或 $4$（分别与 $F(3)=1,F(4)=1$ 形成二周期），故 $F(1)=2$。$F(2)=3$ 会形成三周期，因此 $F(2)=2,Z(2)=3$；剩下 $(Z(1),d)$ 恰为 $(3,4)$ 或 $(4,3)$。

若 $F(3)=3$，则 $Z(3)=1$。若 $Z(2)=3$，无论 $Z(1)\in\{2,3,4\}$ 取何值，都沿 $4\to2\to3\to1$ 的链闭成非平凡周期。因此 $Z(2)=2,F(2)=3$。$Z(1)=3$ 也产生二周期，只剩 $2$ 或 $4$。当 $Z(1)=2$ 时，$F(1)=4$ 会与 $F(4)=1$ 交换，所以 $F(1)=3,d=4$；当 $Z(1)=4$ 时，$\{F(1),d\}=\{2,3\}$。这穷尽了 $H(2)=1$ 的前提分支。四行最终排除为：

| 第21章四尾排除行 | 全部子条件 | 必要代入 | 引理21.6禁止的二周期 |
| --- | --- | --- | --- |
| 21四尾甲1 | $F(3)=1,\ Z(1)=3$ | $A(2)=1,\ A(3)=4$ | $(ZA)(2)=3,\ (ZA)(3)=2$ |
| 21四尾甲2 | $F(3)=1,\ Z(1)=4,\ d=3$ | 式(21甲)给 $A(1)=1$ | $(HZA)(1)=3,\ (HZA)(3)=1$ |
| 21四尾甲3 | $F(3)=3,\ Z(1)=2,\ F(1)=3,\ d=4$ | 式(21甲)给 $A(1)=1$ | $(FA)(1)=3,\ (FA)(3)=1$ |
| 21四尾甲4 | $F(3)=3,\ Z(1)=4,\ \{F(1),d\}=\{2,3\}$ | $F(d)=3$，故 $A(1)=3$ | $(HA)(1)=2,\ (HA)(2)=1$ |

第二行使用 $H(Z(1))=H(4)=3$ 和 $H(Z(4))=H(2)=1$；第四行使用 $H(3)=2,H(1)=1$。其余两行由式(21乙)及各行已定值直接得到。所有复合都是引理21.6覆盖的合法实际自收缩。

再设 $H(2)=2$。此时 $F(2),F(3)$ 各在 $\{1,3\}$ 中，先穷尽四种组合：

| 第21章四尾前提行 | $(F(2),F(3))$ | 无周期与同列不同性强迫的条件 |
| --- | --- | --- |
| 21四尾前提甲 | $(1,1)$ | $F(1)=1$，否则与 $F(1)$ 形成二周期；$Z(1)\in\{2,3,4\}$ |
| 21四尾前提乙 | $(1,3)$ | $Z(1)=1$，否则沿 $4\to2\to3\to1$ 形成 $Z$ 周期；$F(1)=3,\ \{H(1),d\}=\{2,4\}$ |
| 21四尾前提丙 | $(3,1)$ | $F(1)=1$，否则沿 $2\to3\to1$ 或 $4\to1$ 形成 $F$ 周期；$Z(1)=3$ |
| 21四尾前提丁 | $(3,3)$ | $Z(1)=1$，否则形成 $Z$ 周期；$F(1)\in\{2,3\}$ |

第二行中，$F(1)=2$ 或 $4$ 分别与 $F(2)=1$ 或 $F(4)=1$ 形成二周期。第三行在 $F(1)=1$ 后，$Z(1)=1$ 被同列不同性排除，$2,4$ 均与 $Z(2)=1,Z(4)=2$ 形成周期，所以 $Z(1)=3$。第四行中，$Z(2)=Z(3)=1,Z(4)=2$ 使任何 $Z(1)\ne1$ 闭成周期；$F(1)=1$ 被同列不同性排除，$F(1)=4$ 与 $F(4)=1$ 形成二周期。因此该前提表没有遗漏取值。

将其子条件全部展开，得到七行排除：

| 第21章四尾排除行 | 组合及子条件 | 必要代入 | 引理21.6禁止的二周期 |
| --- | --- | --- | --- |
| 21四尾乙1 | $(1,1),\ Z(1)=2$ | $Z(2)=3,\ C(2)=2,\ C(3)=1$ | $(ZC)(2)=3,\ (ZC)(3)=2$ |
| 21四尾乙2 | $(1,1),\ Z(1)=3$ | $A(2)=1,\ A(3)=4$ | $(ZA)(2)=3,\ (ZA)(3)=2$ |
| 21四尾乙3 | $(1,1),\ Z(1)=4$ | $F$ 恒为 $1$，式(21甲)给 $A(1)=1$ | $(HZA)(2)=3,\ (HZA)(3)=2$ |
| 21四尾乙4 | $(1,3)$ | $d\in\{2,4\},\ F(d)=1$，故 $A(1)=1$ | $(FA)(1)=3,\ (FA)(3)=1$ |
| 21四尾乙5 | $(3,1)$ | $Z(1)=3,\ A(2)=1,\ A(3)=4$ | $(ZA)(2)=3,\ (ZA)(3)=2$ |
| 21四尾乙6 | $(3,3),\ F(1)=2$ | $C(2)=2,\ C(3)=1$ | $(FC)(2)=3,\ (FC)(3)=2$ |
| 21四尾乙7 | $(3,3),\ F(1)=3$ | $d\in\{2,4\}$，故 $A(1)=F(d)\in\{1,3\},\ F(A(1))=3$ | $(FA)(1)=3,\ (FA)(3)=1$ |

第三行的两值分别为 $H(Z(A(2)))=H(4)=3$ 和 $H(Z(A(3)))=H(2)=2$。最后一行使用 $F(1)=F(3)=3$、$F(4)=1$；其余行由式(21乙)及前提表直接代入。需要决定 $A(1)$ 的行都满足 $F(d)\notin\{2,4\}$，所以式(21甲)逐字适用。

型 II 的两个 $H(2)$ 分支均被穷尽排除，型 I 也已排除。两种路径来自前向封闭集合的全域必要条件，而不是有限次实际轨道抽查。整个证明没有限制 $Q(O)$ 是否额外含颜色 $1$，也没有指定 $D(5,5)$；这些未定值不产生额外路径或表项情形。定理成立。证毕。

### 21.丁 五尾色的开区间见证、根分配与复合类型

以下假设有限连通片表示、$p=4$ 和 $S=\mathcal C$。引理20.3使每个颜色列都是五标签排列，$F,Z,R$ 在全部 $X$ 上确定，$H,P$ 在 $I$ 上确定。端点数据为

$$
\begin{array}{c|ccccc}
c&F(c)&Z(c)&H(c)&R(c)&P(c)\\\hline
3&F(3)&Z(3)&2&R(3)&4\\
4&1&2&3&4&5\\
5&4&1&H(5)&3&P(5)
\end{array}
\qquad \{H(5),P(5)\}=\{2,5\}.
$$

**引理 21.8（五尾色的区间实现与合法自收缩规则）。** 在上述条件下，必有

$$
R(3)=1,\qquad \{F(3),Z(3)\}=\{3,5\},
$$

且每个颜色都在 $I$ 内有非空开区间实现。每个确定的合法奇长度实际复合 $I\to I$ 的颜色变换都有唯一吸引根；每个确定的合法偶长度实际复合 $I\to I$ 没有非平凡颜色周期。$R$ 在 $X$ 上以 $4$ 为唯一吸引根，且其从颜色 $5$ 出发的路径只有

$$
5\to3\to1\to4,
\qquad\text{或}\qquad
5\to3\to1\to2\to4.
\tag{21丙}
$$

证明。$R(4)=4$，实际点 $2t$ 取色 $4$ 且不同于 $z=\phi/2$。引理21.2用于 $f_2:X\to X$，使 $z$ 两侧最终恒为 $4$。从实际点 $\phi$ 出发的轨道不命中 $z$，所以其确定颜色序列最终进入 $4$，而前两色为 $5\to3$。在第 $3$ 列中，$H(3)=2,P(3)=4$，所以 $R(3)\in\{1,3,5\}$；值 $3,5$ 分别产生避开 $4$ 的固定色或二周期，故 $R(3)=1$，剩余 $F(3),Z(3)$ 恰为 $3,5$。

$F,Z$ 中固定颜色 $3$ 的那个函数，由 $f_3$ 或 $f_0:I\to I$ 诱导。实际点 $t$ 取色 $3$，且不是这两个映射的固定点。引理21.2遂给出颜色 $3$ 的 $I$ 内非空开区间。对该区间应用另一个分支，其颜色输出为 $5$，得到颜色 $5$ 的 $I$ 内非空开区间。再使用

$$
F(5)=4,\qquad Z(5)=1,\qquad Z(4)=2,
$$

分别对颜色 $5$ 的区间应用 $f_3,f_0$，并对所得颜色 $4$ 的区间应用 $f_0$，得到颜色 $4,1,2$ 的 $I$ 内开区间。所有分支严格仿射且在此处都把 $I$ 映入 $I$，故这些开区间非空。这证明全部五色的实际区间见证，未先行假设颜色不是孤立实现。

每个非空合法分支复合的斜率是 $(-g)^k$。奇长度 $I$ 自收缩为负斜率，实际固定点颜色必为其颜色变换的固定色。所有颜色已有开区间见证，故推论21.3适用，给出唯一吸引根。偶长度的正斜率规则直接由引理21.4给出。

对 $R$ 使用 $J=X$；每色的 $I$ 内开区间也给出 $X$ 内非固定实现点。推论21.3使 $R$ 以 $4$ 为唯一根。现有链为 $5\to3\to1$，所以 $R(1)$ 不能为 $1,3,5$，只剩 $2,4$。若 $R(1)=2$，则 $R(2)$ 只有取 $4$ 才能避开该链上的周期并进入根。这给出式(21丙)。证毕。

$F,Z,H$ 各有唯一根，与 $R$ 的根两两不同：若两个分支有同一根色，它们在该颜色输入处都输出该色，违反同列不同性。$F,Z$ 中一个以 $3$ 为根；另一个由 $F(4)=1,F(5)=4$ 或 $Z(4)=2,Z(5)=1$ 只能以 $1$ 或 $2$ 为根。$H$ 的根则在剩余的 $1,2,5$ 中。$P$ 的实际映射是 $I\to O$，这里不赋予它自收缩的根规则。

下面是排除证明中全部所用偶、奇复合的实际类型。箭头按实际标量分支读取，函数复合仍右先左后。

| 第21章五尾复合 | 颜色变换 | 实际合法类型路径 | 使用规则 |
| --- | --- | --- | --- |
| 21五尾偶甲 | $FH$ | $I\xrightarrow{f_5}I\xrightarrow{f_3}I$ | 正斜率无非平凡周期 |
| 21五尾偶乙 | $FZ$ | $I\xrightarrow{f_0}I\xrightarrow{f_3}I$ | 正斜率无非平凡周期 |
| 21五尾偶丙 | $ZF$ | $I\xrightarrow{f_3}I\xrightarrow{f_0}I$ | 正斜率无非平凡周期 |
| 21五尾偶丁 | $ZP$ | $I\xrightarrow{f_{25}}O\xrightarrow{f_0}I$ | 正斜率无非平凡周期 |
| 21五尾奇甲 | $FPH$ | $I\xrightarrow{f_5}I\xrightarrow{f_{25}}O\xrightarrow{f_3}I$ | 全色开区间见证后的唯一吸引根 |
| 21五尾奇乙 | $ZPH$ | $I\xrightarrow{f_5}I\xrightarrow{f_{25}}O\xrightarrow{f_0}I$ | 全色开区间见证后的唯一吸引根 |

在经过 $O$ 的路径上，最后的 $f_3,f_0$ 使用全 $X$ 合法的规则；由于 $S=\mathcal C$，相应颜色变换也确实在这些实际尾上确定。

### 21.戊 五尾色的全部根分支与唯一必要表

**命题 21.9（五尾色的穷尽表约束）。** 在引理21.8的条件下，必要颜色表唯一为

$$
\begin{array}{c|ccccc}
c&F(c)&Z(c)&H(c)&R(c)&P(c)\\\hline
1&1&2&3&4&5\\
2&1&3&2&5&4\\
3&5&3&2&1&4\\
4&1&2&3&4&5\\
5&4&1&2&3&5
\end{array}
$$

这是全域实现的必要条件，不单凭表项赋予它共同标量实现。

证明。先分 $F(3)=3,Z(3)=5$ 与 $F(3)=5,Z(3)=3$ 两种情形。

第一种分配：$F(3)=3,Z(3)=5$。$F$ 以 $3$ 为根；已定链 $5\to4\to1$ 使 $F(1)\in\{2,3\}$，且 $F(2)\ne2$。若 $F(1)=2$，根条件还强迫 $F(2)=3$。逐项排除 $F(2)$ 的其他取值：

| 第21章五尾首分配排除 | 待排值 | 由已定数据形成的周期 |
| --- | --- | --- |
| 21五尾首甲 | $F(2)=4$ | $(FH)(3)=4,\ (FH)(4)=3$ |
| 21五尾首乙 | $F(2)=3$ | $(FZ)(3)=4,\ (FZ)(4)=3$ |
| 21五尾首丙 | $F(2)=5$，根条件给 $F(1)=3$ | $FZ:\ 3\to4\to5\to3$ |

这些都是合法偶长度复合的非平凡周期，所以 $F(2)=1$；随后 $F(1)=2$ 会与 $F(2)=1$ 形成二周期，故 $F(1)=3$。

$Z$ 的根只能为 $1$ 或 $2$。若根为 $1$，则 $Z(1)=1$，而 $FZ$ 有 $3\to4\to1\to3$，不允许。故 $Z$ 以 $2$ 为根，$Z(2)=2$。又 $Z(3)=5,Z(5)=1,Z(4)=2$，无周期和唯一根迫使 $Z(1)\in\{2,4\}$：值 $1$ 是另一固定色，值 $3,5$ 会闭成周期。

$H$ 的根只剩 $1$ 或 $5$。若根为 $1$，$H(1)=1$，$H(5)=2$；由链 $4\to3\to2$，颜色 $2$ 要进入根只能有 $H(2)=1$，这与同列 $F(2)=1$ 冲突。若根为 $5$，则 $H(5)=5$；$H(2)=2,3,4$ 分别导致额外固定色、二周期、三周期，$H(2)=1$ 又与 $F(2)=1$ 冲突，故 $H(2)=5$。第 $1$ 列已有 $F(1)=3$，$Z(1),R(1)$ 均在 $\{2,4\}$ 中且必须不同，因此 $\{H(1),P(1)\}=\{1,5\}$。唯一根排除 $H(1)=1$，所以 $H(1)=5$。于是 $FH$ 有

$$
1\to4\to3\to1,
$$

再次违反偶长度规则。第一种分配全部排除。

第二种分配：$F(3)=5,Z(3)=3$。$Z$ 以 $3$ 为根。若 $H(5)=5$，则 $(FH)(4)=5,(FH)(5)=4$，故

$$
H(5)=2,\qquad P(5)=5.
$$

$H$ 的根不可能为 $5$，于是 $F,H$ 的根恰为 $1,2$ 的两种次序。

若 $H$ 以 $1$ 为根、$F$ 以 $2$ 为根，链 $4\to3\to2$ 与 $5\to2$ 使 $H(1)=H(2)=1$，链 $3\to5\to4\to1$ 使 $F(1)=F(2)=2$。第 $1$ 列的 $R(1)\in\{2,4\}$ 与 $F(1)=2$ 不同，故 $R(1)=4$；剩余 $Z(1),P(1)$ 为 $3,5$。$Z(1)=5$ 会与 $Z(5)=1$ 形成二周期，所以 $Z(1)=3$。第 $2$ 列已有 $H(2)=1,F(2)=2$，$Z(2)=4$ 与 $Z(4)=2$ 形成二周期，因此 $Z(2)\in\{3,5\}$。两种值全部被下表排除：

| 第21章五尾根序排除 | 子条件 | 偶长度复合的二周期 |
| --- | --- | --- |
| 21五尾根序甲 | $H$ 根 $1$、$F$ 根 $2$、$Z(2)=3$ | $(ZF)(1)=3,\ (ZF)(3)=1$ |
| 21五尾根序乙 | $H$ 根 $1$、$F$ 根 $2$、$Z(2)=5$ | $(ZF)(2)=5,\ (ZF)(5)=2$ |

因此只剩 $H$ 以 $2$ 为根、$F$ 以 $1$ 为根，故

$$
H(2)=2,\qquad H(5)=2,\qquad F(1)=1.
$$

$Z$ 的根为 $3$，所以 $Z(1)\in\{2,3,4\}$。若 $Z(1)=3$，则 $(FZ)(1)=5,(FZ)(5)=1$，故 $Z(1)\in\{2,4\}$。由 $Z(4)=2,Z(5)=1$，无论这两值取哪一个，要使颜色 $2$ 进入根 $3$ 都只能 $Z(2)=3$：值 $1,4,5$ 会闭成非平凡周期，值 $2$ 是另一固定色。

第 $2$ 列已有 $H(2)=2,Z(2)=3$，所以 $F(2)\in\{1,4,5\}$。值 $4$ 使 $(FH)(4)=5,(FH)(5)=4$，被排除。若 $F(2)=5$，$Z(1)=2$ 会使 $(FZ)(1)=5,(FZ)(5)=1$，故 $Z(1)=4$。第 $1$ 列迫使 $R(1)=2$，式(21丙)再给 $R(2)=4$；第 $2$ 列于是强迫 $P(2)=1$。但

$$
(ZPH)(2)=Z(P(2))=Z(1)=4,\qquad
(ZPH)(4)=Z(P(3))=Z(4)=2.
$$

这是合法奇长度自收缩的二周期，违反全部颜色已有开区间见证后的唯一根规则。

故 $F(2)=1$，第 $2$ 列给 $\{R(2),P(2)\}=\{4,5\}$。第 $1$ 列中 $F(1)=1$，而 $Z(1),R(1)\in\{2,4\}$ 必须不同，所以 $\{H(1),P(1)\}=\{3,5\}$。最后两次奇长度排除为：

| 第21章五尾末分支排除 | 待排值及已定条件 | 奇长度复合的二周期 |
| --- | --- | --- |
| 21五尾末甲 | $H(1)=5,\ P(5)=5,\ P(3)=4$ | $(FPH)(1)=4,\ (FPH)(4)=1$ |
| 21五尾末乙 | $H(1)=3,\ P(2)=5$ | $(ZPH)(1)=2,\ (ZPH)(2)=1$ |

第一行排除后得到 $H(1)=3,P(1)=5$；第二行遂排除 $P(2)=5$，得到 $P(2)=4,R(2)=5$。式(21丙)因此不允许 $R(1)=2$，只能 $R(1)=4$，继而 $Z(1)=2$。所有五列恰为命题陈述中的表。

证明中的初始两种分配、两种根次序、$F(2)$ 的全部余值及最后两项二选一均已穷尽。所有周期都来自已经列明类型的实际复合；偶长度使用引理21.4，奇长度只在引理21.8完成全部开区间见证后使用推论21.3。证毕。

### 21.己 唯一五尾表的实际固定点侧反证

**定理 21.10（$p=4$、五尾色的有限连通片非存在性）。** 定义20.1的任意表合同在归一化 $p=4$、$Q(I)=\mathcal C$ 下，不存在有限连通片表示的 $Q$。

证明。若存在，命题21.9强迫其全部颜色变换为唯一必要表。颜色变换 $U=ZP$ 在颜色 $1,2,3,4,5$ 上依次为

$$
(U(1),U(2),U(3),U(4),U(5))=(1,2,2,1,1).
$$

它对应同一个实际正斜率自收缩

$$
G=f_0f_{25}:I\to I,\qquad G(y)=g^2y-g(2-t).
$$

由 $1-g^2=4g$，实际固定点是

$$
q=-\frac{2-t}{4}.
$$

$t$ 为 $x^2+x-1$ 的正根，故 $1/2<t<2/3$；于是

$$
q-(-t^2)=\frac{2-3t}{4}>0,\qquad -t^2<q<0<g.
$$

颜色 $1$ 在 $e_1=-t^2$ 实现且被 $U$ 固定，颜色 $2$ 在 $e_2=g$ 实现且也被 $U$ 固定。这两条实际 $G$ 轨道分别保持颜色 $1,2$，从左、右趋近 $q$。有限连通片的两侧局部常值性因此强迫

$$
Q=1\text{ 在 }q\text{ 的充分小左穿孔邻域},\qquad
Q=2\text{ 在 }q\text{ 的充分小右穿孔邻域}.
\tag{21丁}
$$

在 $I$ 中，任何颜色 $1$ 的实现点都不能位于 $q$ 右侧。否则其 $G$ 轨道始终保持颜色 $1$，保持在右侧并趋近 $q$，最终进入式(21丁)的颜色 $2$ 邻域，矛盾。

由于 $Q(I)=\mathcal C$，取实际点 $y\in I$ 取色 $5$。若 $y>q$，$U(5)=1$ 使 $G(y)$ 成为 $q$ 右侧的颜色 $1$ 点，与上一段矛盾。若 $y=q$，则 $G(y)=y$ 应使 $U(5)=5$，也与表冲突。因此 $y<q<0$。然而该表有 $Z(5)=1$，合法分支 $f_0$ 给出

$$
Q(f_0(y))=1,\qquad f_0(y)=-gy>0>q.
$$

$f_0(y)\in I$，于是又产生一个 $q$ 右侧的颜色 $1$ 实现，矛盾。唯一必要表不能由有限连通片的同一标量 $Q$ 实现。结合命题21.9的穷尽性，结论成立。证毕。

### 21.庚 任意解码表的全域无限分支与精确六色界

**定理 21.11（任意五色表必有无限连通分支纤维）。** 设 $Q:X\to\mathcal C$ 是任意单值函数，$D:\mathcal C^2\to\Lambda$ 是任意确定表，并且对定义20.1的全部合法闭分支图满足精确解码合同。则五色全部实际使用，且至少一个颜色 $c\in\mathcal C$ 的全域纤维 $Q^{-1}(c)$ 有无限多个连通分支。此结论不要求可测性或其他正则性。

证明。引理20.2的共同实际尾强迫五个当前颜色不同，故恰使用五色，并可同时重命名 $Q,D$ 达到端点归一化 $p\in\{2,4\}$。颜色置换保持每个纤维的连通分支数。

反设全部五个纤维都只有有限多个连通分支。引理21.1使它们各为有限个区间与单点的并，因此 $Q$ 有有限连通片表示。若 $p=2$，推论20.9已经排除这种表示，其更强局部结论由定理20.8给出；这里无需重证该情形。

若 $p=4$，实际端点 $e_0,e_1,e_2,e_3\in I$ 分别取色 $4,1,2,3$，故

$$
\{1,2,3,4\}\subseteq Q(I)\subseteq\mathcal C.
$$

这只有 $Q(I)=\{1,2,3,4\}$ 与 $Q(I)=\mathcal C$ 两种可能，分别被定理21.7和定理21.10排除。所有归一化情形都矛盾，所以至少一个纤维有无限多个连通分支。整个推理保留全部共享端点和共同实际尾，不使用第17章的固定表。证毕。

**推论 21.12（有限连通片类的精确最小颜色数为六）。** 在全部实际合法相邻样本的同一标量观察函数合同中，允许任意有限非空颜色集和任意确定解码表，并要求每色纤维只有有限多个连通分支，则最小颜色数恰为六。

证明。共同实际尾 $-1$ 的五个合法前接输出必须异色，由引理20.2的同尾论证或定理16.7得到至少五色。若恰为五色，可将颜色重命名为 $\mathcal C$，定理21.11强迫至少一个纤维有无限多个连通分支，违反本类条件。故至少六色。

定理16.8已经给出六个连通纤维

$$
\begin{aligned}
C_0&=[-1,-1/2],& C_1&=(-1/2,0],& C_2&=(0,t/2],\\
C_3&=(t/2,3t/2),& C_4&=[3t/2,2t],& C_5&=(2t,\phi]
\end{aligned}
$$

及它们对全部合法闭分支的完整相邻解码判据。该处的窗口 $\mathrm{null}$ 就是本章标签 $0$，其六种颜色 $0,\ldots,5$ 与标签仍分开读取。每色为一个连通区间，特别属于有限连通片类；定理16.7给出确定解码器，定理17.2及引理20.2给出实际来源与闭分支合同的等价性。于是本类有六色实现，上下界相等。证毕。

该最小值针对使用同一个 $Q$ 记录已经实际取得的当前样本与下一样本，并由同一表恢复首窗的合同。颜色纤维可以有任意有限数量的区间和孤立点；没有要求每色连通，也没有要求各区间等宽。定理21.11只断言至少一个纤维的分支数非有限，不指定承担该性质的颜色，不给出其分支基数上界。

定理17.7的同一 Borel 五色构造仍满足全部闭分支合同；本章排除的是有限连通片表示，不排除该构造。无正则性限制与 Borel 类的最小颜色数仍恰为五，有限连通片类的最小值六只适用于推论21.12的附加条件。第18章对指定构造的纤维描述和第19章对固定表的结果分别保留原来的条件。

### 21.辛 数学依据

本章的实际满域、共同尾、共享端点及整列确定性使用定义14.5、命题14.6、定理17.2和引理20.2、20.3；$p=2$ 障碍直接使用定理20.8、推论20.9。六色上界使用定理16.8及定理16.7，已有 Borel 五色实现使用定理17.7。一般紧区间上的不变色轨道、确定颜色吸引根、四尾色的实际固定色集合排除和五尾色的实际侧反证由本章的陈述与证明给出。

实直线连通子集的区间性质可参照第18章引用的 J. R. Munkres, Topology, 2nd ed., §§23–24。仿射收缩固定点和迭代使用显式公式 $G^n(x)=z_G+s^n(x-z_G)$、$|s|<1$；有限表分支的排除均由逐项列出的必要条件推导，不以有限轨道检验代替全域证明。

## 追加锚（本行以下为增补区）

## 22. 最终空尾来源的五个环境区间与单标量恢复

### 22.甲 来源合同与全部端点逆关联

**约定 22.1（有限来源与观察任务）。** 沿用定义1.1的 $D$、定义14.5的状态地址 $A_0,A_1$、窗口集 $\Sigma$ 与编码 $\kappa_s$，并沿用定义16.1的

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t=t^{-1},\qquad
a=t^3=2t-1,\qquad \gamma=-a,\qquad T=\sigma^3.
$$

窗口按低位到高位读为

$$
(\mathrm{null},2,3,25,5)=(000,100,010,101,001).
$$

外部单位位固定为零；$D$ 的地址最终全零，按高位补零识别，包含全零地址，没有独立长度或 End 坐标。一个窗口步删除三位。记 $P=\kappa_0(D)$，当前及实际尾部坐标满足

$$
z_j=\kappa_0(T^j\omega),\qquad
z_j=f_{\sigma_j(\omega)}(z_{j+1}),\qquad
f_\ell(y)=\Delta_\ell-a y.
$$

$5,25$ 的合法尾区间为 $I_1=[-1,t]$，其余三窗的合法尾区间为 $I_0=[-1,\phi]$；起始 guard 一只允许 $3,\mathrm{null},5$。状态下标限定合法地址域，不改变同一地址的级数值。

本章给出上述来源和访问合同下的普通纸面结果。定理14.7后的 $\kappa_0|_D$ 单射、命题14.9的稠密像及真实删窗映射直接复用；成员识别直接使用约定1.3及母卷命题182.1。

**命题 22.2（十个合法端点关联与实际尾部避端点）。** 置

$$
e_0=-1,\quad e_1=t-1=-t^2,\quad e_2=a,\quad
e_3=t,\quad e_4=2t,\quad e_5=\phi,\qquad
E=\{e_0,e_1,e_2,e_3,e_4,e_5\}.
$$

六个端点严格递增。对于全部合法分支，目标在 $E$ 中的逆关联恰为下表；其中 $(\ell,y)$ 表示 $y\in I_{b(\ell)}$ 且 $f_\ell(y)$ 等于该行端点。

| 目标端点 | 全部合法逆关联 $(\ell,y)$ |
| --- | --- |
| $e_0$ | $(3,e_5)$ |
| $e_1$ | $(3,e_0)$、$(\mathrm{null},e_5)$ |
| $e_2$ | $(\mathrm{null},e_0)$、$(5,e_3)$ |
| $e_3$ | $(5,e_0)$、$(2,e_5)$ |
| $e_4$ | $(2,e_0)$、$(25,e_3)$ |
| $e_5$ | $(25,e_0)$ |

因此合法分支满足 $f_\ell(y)\in E\Rightarrow y\in E$，且

$$
\kappa_0(T^j\omega)\notin E
\qquad(\omega\in D,\ j\ge0).
$$

证明。命题14.6的五个闭分支像按空间顺序为

$$
[e_0,e_1],\quad[e_1,e_2],\quad[e_2,e_3],\quad
[e_3,e_4],\quad[e_4,e_5],
$$

分别对应 $3,\mathrm{null},5,2,25$。用 $t^2=1-t$ 代入 $f_\ell(y)=\Delta_\ell-a y$，得到表中的十个等式。每个分支严格单调，其闭像只含 $E$ 中的两个相邻端点，每个端点在该分支中又至多有一个逆像。因此五个分支的十个合法关联全部列尽。若 incoming guard 为一，只删除不允许的 $2,25$ 关联，不增加关联，逆向封闭性仍成立。

任取 $\omega\in D$。有整数 $m$ 使 $T^m\omega=\mathrm{null}^{\infty}$，故 $z_m=0$。若某个 $z_j\in E$，在 $j<m$ 时逆向封闭性依次推出 $z_{j+1},\ldots,z_m\in E$；在 $j\ge m$ 时已有 $z_j=0$。两种情形均与 $0\notin E$ 矛盾。$\square$

### 22.乙 五个区间格与完整有限恢复

**定理 22.3（一次当前颜色的五格解码及尖锐性）。** 在环境区间 $I_0\subset\mathbb R$ 上取五个格

$$
\begin{aligned}
B_3&=[e_0,e_1),& B_{\mathrm{null}}&=[e_1,e_2),&
B_5&=[e_2,e_3),\\
B_2&=[e_3,e_4),& B_{25}&=[e_4,e_5].
\end{aligned}
$$

令 $Q_5(x)=\ell$ 当且仅当 $x\in B_\ell$。则

$$
Q_5(\kappa_0(\omega))=\sigma_0(\omega)
\qquad(\omega\in D).
$$

在 $D$ 上，无论要求从一个当前颜色恢复首窗，还是要求从同一量化器的实际相邻颜色对恢复首窗，最少颜色数均为五；在环境区间格类中也取得这个最小值。

证明。真实当前值属于真实首窗的闭分支像。命题22.2排除该像的两个端点，所以它属于该分支唯一的开内部，恰落在相应 $B_\ell$ 中。首窗只需当前颜色即可恢复；相邻对解码器也可直接返回其第一颜色标签。

下界复用定理16.7的共同尾论证。五个来源 $\ell\,\mathrm{null}^{\infty}$ 都实际属于 $D$，其当前坐标按 $3,\mathrm{null},5,2,25$ 次序为

$$
-t,\quad0,\quad t^2,\quad1,\quad2-t,
$$

后继坐标则同为零。单颜色正确性要求五个当前颜色不同；相邻对合同下第二颜色同为 $Q(0)$，仍要求五个当前颜色不同。由此两种合同均至少五色，上述五格取得下界。$\square$

这里计数的是 $\mathbb R$ 中的环境区间 $B_\ell$，不是把可数集合 $P\cap B_\ell$ 称为连通区间。改变根端点的邻格归属不影响 $P$ 上的正确性，但上述归属给出一个确定的环境量化器。

**命题 22.4（通过既有成员接口后的精确系数解码）。** 给定指定实嵌入中的精确整数系数

$$
x=u+vt,\qquad u,v\in\mathbb Z,
$$

先使用约定1.3及母卷命题182.1的成员接口：接受恰在

$$
(u,v)=(0,0)\quad\text{或}\quad
\bigl[\,2u-3v>0\ \text{且}\ -1<u+vt<\phi\,\bigr].
$$

对接受的输入，逐窗分支逆运算在有限步后输出唯一 canonical 有限位词；拒绝的输入不进入该循环。

证明。接口中的坐标代换是母卷整数组成 $(A,B)=(u,-v)$，故

$$
A+B\psi=u+vt=x,\qquad q(A,B)=2u-3v.
$$

正数量分支由既有开条带识别给出，零分支由命题1.2给出。这里仅调用该接口，不另证明成员分类。正数量和严格条带均须保留，例如 $3t-1$ 虽在根分支内部却有数量 $-11$，而 $2$ 虽有正数量却在 $I_0$ 外。

接受后，令当前 guard 为 $s=0$。当前 $x=0$ 时停止；否则按定理22.3输出 $\ell=Q_5(x)$，再置

$$
x\longleftarrow\frac{\Delta_\ell-x}{a},\qquad
s\longleftarrow b(\ell).
$$

这就是命题14.9的真实删窗映射 $g$，因为对实际来源

$$
g(\kappa_0\omega)=\kappa_0(T\omega),\qquad
\frac{\Delta_\ell-x}{a}=\frac{x-\Delta_\ell}{\gamma}.
$$

每次更新仍是同一来源的实际尾部值，仍属于 $P$，仍避开 $E$；$s=1$ 时输出只可能为 $3,\mathrm{null},5$。这给出整个循环的来源、区间及 guard 不变量。

精确整数系数在更新下封闭。写 $\Delta_\ell=c_\ell+d_\ell t$，使用 $a^{-1}=3+2t$，得到

$$
(u,v)\longleftarrow
\bigl(3(c_\ell-u)+2(d_\ell-v),
2(c_\ell-u)+(d_\ell-v)\bigr).
$$

零测试由 $(u,v)=(0,0)$ 判定。切点比较在 $\mathbb Q(t)$ 中使用命题16.5的有限比较规则：将 $p+qt$ 写成 $(p-q/2)+(q/2)\sqrt5$，先判零，同号项直接定号，异号项比较绝对值的平方。因此循环所需算术和分支判定均为有限精确运算。

定理14.7后的单射性给出

$$
\kappa_0(T^j\omega)=0
\quad\Longleftrightarrow\quad
T^j\omega=\mathrm{null}^{\infty}.
$$

有限来源最终到达这个尾部，所以循环终止。输出截至最后一个非 null 窗口的窗口列，转成三位块后去掉高端多余零，得到 canonical 有限位词；初值零输出空词，表示全零地址。指定 $h$ 窗的任务则可在停止后用 null 补足。$\square$

停止判据是完整当前尾部标量为零。当前标签为 null 本身不是停止判据：$\mathrm{null}\,5\,\mathrm{null}^{\infty}$ 的首窗是 null，当前标量却为 $-a t^2\ne0$。null 是窗口 $000$，不承担独立 End 的含义。

解码恢复的是 $D$ 中按高位补零识别的来源。原先写下的高端零数量、独立声明长度或 End 位置均不能由它恢复，外部单位位已固定而非待恢复参数。原始有序树的括号和左右次序也不在此合同中。命题14.15的实际图 $\Gamma$ 上组成随地址恢复；独立乘积 $D\times G$ 中自由的 $G$ 坐标仍不可见。

### 22.丙 近似名字、颜色演化与单样本噪声

**命题 22.5（任意 Cauchy 名字的固定前缀与完整词停止边界）。** 假定输入承诺 $x\in P$，访问只提供任意有理 Cauchy 名字 $r_n$，满足 $|r_n-x|\le2^{-n}$。对任意预先指定的整数 $h\ge0$，可以有限查询计算前 $h$ 窗。没有对全部 $P$ 输入及其全部合法名字均有限停机、输出完整 canonical 有限词并宣布结束的算法。

证明。$h=0$ 返回空前缀。对 $h>0$，逐步提高精度，直到

$$
[r_n-2^{-n},r_n+2^{-n}]
$$

严格包含于某个根分支的开内部。命题22.2保证真实值距根端点为正，所以该步骤对每个输入都会终止。识别首窗后，用精确仿射运算和误差界形成 $g(x)$ 的 Cauchy 名字；$g(x)\in P$，故可重复。有限重复 $h$ 次即可得到前缀，包括零尾的 null 补齐，不需要精确零测试。这里不提供独立于输入的统一查询精度。

若存在所述完整词算法，在零来源的全零名字上停机时，它只查询有限多个精度。取

$$
\omega_M=\mathrm{null}^M5\mathrm{null}^{\infty}\in D,
\qquad x_M=\kappa_0(\omega_M)=\gamma^M t^2\ne0.
$$

因为 $x_M\to0$，可选 $M$ 使 $|x_M|$ 小于全部已查询精度的允许误差。相同有限零答复于是也可补全为 $x_M$ 的合法名字；算法沿相同查询路径给出相同完整词，不能同时正确输出零来源与 $\omega_M$。若算法没有查询，矛盾直接成立。$\square$

精确系数和任意 Cauchy 名字是两种访问合同。前者的有限描述长度并无统一上界，例如

$$
\gamma^M t^2=F_{3M+1}-tF_{3M+2}
$$

由 $M=0$ 时的 $t^2=1-t$ 及乘以 $\gamma=1-2t$ 后的 Fibonacci 三步递推得到。其整数系数随 $M$ 无界，所需删窗次数也无界。固定前缀的有限查询、无限输出补零地址流、有限输出完整词并给出结束信号分别是不同任务。

**命题 22.6（五色不构成自主删窗状态）。** 不存在函数 $A:\Sigma\to\Sigma$ 使

$$
Q_5(g(x))=A(Q_5(x))\qquad(x\in P).
$$

证明。$\mathrm{null}^{\infty}$ 与 $\mathrm{null}\,5\,\mathrm{null}^{\infty}$ 的当前颜色均为 null，下一颜色却分别为 null 与 $5$。同一当前颜色不能有这两个不同自主后继。$\square$

所以一个当前颜色提供首窗标签，而继续分支逆算使用精确标量；它没有把确定性的标量删窗变成五状态的自主预测器。

**命题 22.7（一次实标量首窗任务的零统一噪声余量）。** 对每个 $\eta>0$，若当前一次记录允许全部实误差 $|e|\le\eta$，不存在对所有 $D$ 来源正确的首窗解码器；允许全部 $|e|<\eta$ 时也不存在。此结论允许任意解码函数，不限于 $Q_5$。

证明。复用命题14.9的实际有限来源

$$
L_m=(3,25)^m\mathrm{null}^{\infty},\qquad
R_m=(25,3)^m\mathrm{null}^{\infty},\qquad
\epsilon_m=\gamma^{2m}=a^{2m}.
$$

其坐标为 $-1+\epsilon_m$ 与 $\phi(1-\epsilon_m)$。两个合法有限来源 $3L_m$ 与 $\mathrm{null}R_m$ 的首窗不同，当前值分别为

$$
x_m=e_1-a\epsilon_m,\qquad
y_m=e_1+t^2\epsilon_m,\qquad
y_m-x_m=t\epsilon_m\longrightarrow0.
$$

选 $m$ 使 $t\epsilon_m/2<\eta$。同一实际记录 $(x_m+y_m)/2$ 距两个值均为 $t\epsilon_m/2$，同时符合两种误差合同，却要求两个不同首窗答案。$\square$

每个固定 $x\in P$ 距相邻根切点仍为正，因而有个别的局部首窗误差余量；缺少的是全 $D$ 的统一正余量。若只取得一次有误差的初值，再沿正确标签计算分支逆，初值误差在第 $j$ 步放大为 $a^{-j}|r_0-z_0|$；这些计算值不是重新取得的同精度实际样本。

### 22.丁 完成域的端点与数学依据

命题14.6中的 $L=(3,25)^\infty$、$R=(25,3)^\infty$、$U=5L$ 给出四个根接触的两条实际地址：

| 根接触点 | 两条完整地址 |
| --- | --- |
| $e_1$ | $3L$ 与 $\mathrm{null}R$ |
| $e_2$ | $\mathrm{null}L$ 与 $5U$ |
| $e_3$ | $5L$ 与 $2R$ |
| $e_4$ | $2L$ 与 $25U$ |

同一行的当前坐标相同、首窗不同；它们均含非零周期尾，不属于 $D$。外端点 $e_0,e_5$ 的唯一极值地址也不属于 $D$。这解释了完成域和最终空尾域的任务差别：全 $\Omega$ 中一次未量化标量已不能统一决定首窗，命题14.8还排除全域单值标量删窗；$D$ 中全部这些端点被避开。

全 $\Omega$ 的实际相邻对环境连通格最小值仍是定理16.8的六，任意五色解码表的全域空间分支障碍仍按第20–21章的量词成立。本章的五格结论只作用于 $D$。定理16.2–16.5针对 $h+1$ 个实际连续响应的分离和正噪声阈值也保留原合同，与命题22.7的一次取得不同。

本章的来源、编码、成员接口及真实删窗分别引用定义1.1、约定1.3、定义14.5、命题14.6、定理14.7、命题14.9和母卷 [FIBONACCI_ATOMIC_RELATION_GENERATION.md](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 命题182.1；精确代数比较引用命题16.5，共同零尾下界引用定理16.7。这些条件数学结果限定于既定地址、实区间编码和三位删窗时钟。

## 23. 已知支持上界的一次标量间距、完整来源与前缀噪声

### 23.甲 实际有限集合的极值与完整间距

**约定 23.1（已知位支持与一次实记录）。** 沿用约定12.1的 $D_N$，整数 $N\ge0$ 是解码器预先知道的位支持上界。外部单位位固定为零，高位补零识别，零来源包含在内，没有独立长度或 End 字段。定义14.5的编码在该域写成同一个位级和：

$$
\kappa(\omega)=\kappa_0(\omega)
=\sum_{j=0}^{N-1}\omega_j(-t)^j,\qquad S_N=\kappa(D_N).
$$

定理14.7后的单射性直接用于 $D_N$；不另证明来源计数或单射性。本章给出这一个当前标量记录 $r=\kappa(\omega)+e\in\mathbb R$ 的普通纸面结果，误差合同涵盖全部允许的实数 $e$，不限制记录的数字网格。$N$ 以位计，不是三位窗口数。

**定理 23.2（实际分块、达到的极值与全点对间距）。** 对整数 $k\ge0$，实际有限集合的极小值为

$$
m_k=\min S_k=-1+t^{2\lfloor k/2\rfloor}.
$$

对 $N\ge2$，按首位作实际集合分解有

$$
S_N=A_N\cup B_N,\qquad
A_N=-tS_{N-1},\qquad B_N=1+t^2S_{N-2},
$$

其中 $A_N$ 是首位零的全部来源值，$B_N$ 是首位一的全部来源值，且

$$
\min B_N-\max A_N=t^{N-2}>0.
$$

对每个 $N\ge1$，全码本的最小不同点距离恰为

$$
d_N=\min_{x\ne y\in S_N}|x-y|=t^{N-1}.
$$

$S_0=\{0\}$ 无不同点对；$S_1=\{0,1\}$、$S_2=\{-t,0,1\}$ 分别有 $d_1=1$、$d_2=t$。

证明。奇数指标的项为负，偶数指标的项为非负。每个地址值均不小于取全部奇数位负项所得的和，而奇数位全一、偶数位全零的地址没有相邻一，确实属于 $D_k$。所以逐项极小值同时达到，且

$$
m_k=-\sum_{j=0}^{\lfloor k/2\rfloor-1}t^{2j+1}
=-1+t^{2\lfloor k/2\rfloor},
$$

空和包括 $k=0,1$。首位为零时，余下 $N-1$ 位可为任意 $D_{N-1}$ 地址；首位为一时，第二位强制为零，余下 $N-2$ 位可为任意 $D_{N-2}$ 地址。两种拼接均实际合法，故得到精确分块等式。

负缩放与正缩放给出

$$
\max A_N=-t m_{N-1},\qquad \min B_N=1+t^2m_{N-2}.
$$

这些极值由相应奇数位极小词分别前接 $0$、$10$ 达到。于是

$$
\begin{aligned}
\min B_N-\max A_N
&=1+t^2m_{N-2}+t m_{N-1}\\
&=t^{2+2\lfloor(N-2)/2\rfloor}
 +t^{1+2\lfloor(N-1)/2\rfloor}\\
&=t^{N-1}+t^N=t^{N-2}.
\end{aligned}
$$

第二行用 $1-t-t^2=0$；按 $N$ 奇偶，两个指数恰是 $N-1,N$。两块严格有序，跨块最小距离因此就是达到的极值间隙。

对全点对下界作强归纳。$S_1$ 的不同点距为一。设 $N\ge2$，两不同点同在 $A_N$ 时，由更小指标的结论，其距至少为 $t\,t^{N-2}=t^{N-1}$；同在 $B_N$ 时，$N=2$ 的该块为单点，无此点对，$N\ge3$ 时其距至少为 $t^2t^{N-3}=t^{N-1}$。分属两块时，其距至少为 $t^{N-2}>t^{N-1}$。由此全部不同点对均达到所需下界。

零地址与只在第 $N-1$ 位为一的地址同属 $D_N$，其标量为 $0$ 与 $(-t)^{N-1}$，距离正好为 $t^{N-1}$。合并上下界即得精确最小值；列出长度至多二的合法词便得所述 $S_0,S_1,S_2$。$\square$

### 23.乙 完整来源的闭开误差边界与访问精度

**定理 23.3（一个共同解码器对全部实记录的尖锐条件）。** 设 $N\ge1$。闭误差合同中，存在一个函数 $\mathcal D_N:\mathbb R\to D_N$，对每个 $\omega\in D_N$ 和每个满足 $|r-\kappa(\omega)|\le\eta$ 的实数 $r$ 都返回 $\omega$，当且仅当

$$
2\eta<d_N=t^{N-1}\qquad(\eta\ge0).
$$

正半径开误差合同将允许记录改为 $|r-\kappa(\omega)|<\eta$，其对应充要条件为

$$
2\eta\le d_N=t^{N-1}\qquad(\eta>0).
$$

$N=0$ 时常值解码器返回零来源，对任意误差半径正确；半径零的开合同没有允许记录，另视为空合同。

证明。闭条件成立时，令 $x$ 为真实码点，对任意不同码点 $y$ 有

$$
|r-y|\ge |x-y|-|r-x|\ge d_N-\eta>\eta\ge|r-x|.
$$

真实码点是唯一最近点。开条件成立时，令 $\rho=|r-x|<\eta$，则

$$
|r-y|\ge d_N-\rho\ge2\eta-\rho>\rho.
$$

所以开合同也有唯一正确最近点。选最近码点，再用既有单射性返回其来源；合同外的并列点任意破同，得到一个定义在全部 $\mathbb R$ 上的共同解码器。这是存在一个解码器对全部输入正确的结论。

反向只用定理23.2的同一实际达到对。取零来源和最高允许位单独占用的来源，令

$$
r_N=\frac{(-t)^{N-1}}2.
$$

这个中点距两个不同来源值均为 $d_N/2$。闭合同若 $2\eta\ge d_N$，它与两者同时相容；开合同若 $2\eta>d_N$，它也与两者同时相容。任一解码函数不能在同一记录上返回两个来源。闭等号因此失败，开等号则由充分性成立。$\square$

特别地，$N=1$ 的闭半径须小于 $1/2$、正开半径可到 $1/2$；$N=2$ 的对应边界为 $t/2$。$N=0$ 不代入不存在的不同点最小距离。

**命题 23.4（总绝对精度与临界近似访问）。** 对已知 $N\ge1$，若用于判定的数值相对真实来源标量的总绝对误差保证不超过 $2^{-p}$，一个充分的整数精度条件为

$$
2^{1-p}<t^{N-1}
\quad\Longleftrightarrow\quad
p>1+(N-1)\log_2\phi.
$$

闭合同严格低于定理23.3阈值时，存在统一正的额外近似余量。正开合同在临界半径 $\eta=d_N/2$ 时，任意合法实记录的 Cauchy 访问可以逐步提高精度并对该记录终止，但没有对全部记录共同的正额外误差余量或统一查询精度上界。

证明。充分条件是将闭总误差 $2^{-p}$ 代入定理23.3。若实际取得记录的误差为 $\eta$，后续近似误差为 $\rho$，总误差至多 $\eta+\rho$；闭合同中可选任何 $\rho<d_N/2-\eta$。码本有限且所有码点为精确代数数，可以用命题16.5的运算比较。

开临界合同中，每个真实记录都有唯一最近码点。它到所有竞争码点的距离差有正的最小值，故逐步缩小 Cauchy 误差界，直到最近点被严格认证，会对该输入终止。然而记录可从最小间距点对的中点两侧任意接近它，两侧都为合法记录且应返回不同来源。任意固定正近似容差下，可取足够近的两侧记录，使同一有限近似答复符合两者。因此没有统一的正额外余量，也没有足以判定全部记录的统一精度上界。$\square$

这里的 $p$ 是指定总绝对误差合同的充分条件，不是设备最小存储位数或有限传感器字母表的最优性结论。定理23.3的必要性使用任意实记录，尤其使用达到对的中点；若记录被限制在某个传感器字母表中，充分性仍成立，必要性须针对该字母表另行判断。对同一个实记录提高查询精度，不增加实际取得次数；固定的一份有限精度记录也不自动提供可继续细化的 Cauchy 访问。

### 23.丙 真前缀的共同间距与类别解码

**推论 23.5（全部前缀任务的距离、实际见证与类别噪声）。** 对整数 $0\le k\le N$，令 $\pi_k(\omega)=(\omega_0,\ldots,\omega_{k-1})$。当 $1\le k\le N$ 时，定义不同目标答案之间的最小距离

$$
\delta_{N,k}
=\min_{\substack{\omega,\nu\in D_N\\
\pi_k(\omega)\ne\pi_k(\nu)}}
|\kappa(\omega)-\kappa(\nu)|.
$$

则

$$
\delta_{N,k}=
\begin{cases}
t^{N-2},&1\le k<N,\\
t^{N-1},&k=N\ge1.
\end{cases}
$$

真前缀情形自动有 $N\ge2$。存在一个共同函数 $\mathcal D_{N,k}:\mathbb R\to\pi_k(D_N)$，对全部来源及全部允许实记录正确，当且仅当

$$
\begin{aligned}
\text{闭误差 }|r-\kappa(\omega)|\le\eta:\quad
&2\eta<\delta_{N,k} &&(\eta\ge0),\\
\text{开误差 }|r-\kappa(\omega)|<\eta:\quad
&2\eta\le\delta_{N,k} &&(\eta>0).
\end{aligned}
$$

$k=0$ 是常值空前缀任务，对任意误差半径正确；$N=0$ 只允许该任务。半径零的开合同为空。

证明。设 $1\le k<N$，任取两个目标不同的来源，令 $j<k$ 为首个不同位，$M=N-j\ge2$。若 $j>0$，其共同前一位必为零，否则合法性强制两条地址的第 $j$ 位均为零。删去共同前缀后的两实际尾部因此分属定理23.2的首位零、一块 $A_M,B_M$。共同前缀在标量差中消去，所以

$$
|\kappa(\omega)-\kappa(\nu)|
=t^j|\kappa(\delta^j\omega)-\kappa(\delta^j\nu)|
\ge t^j t^{M-2}=t^{N-2}.
$$

这个下界已包括所有合法尾部抵消。

为同时取得全部非空真前缀的下界，对 $N\ge2$ 定义同一对完整实际地址

$$
\begin{aligned}
b^{(N)}_j=1
&\quad\Longleftrightarrow\quad
j=0\ \text{或}\ (3\le j<N\text{ 且 }j\text{ 为奇数}),\\
c^{(N)}_j=1
&\quad\Longleftrightarrow\quad
2\le j<N\text{ 且 }j\text{ 为偶数}.
\end{aligned}
$$

其他位为零。非零位间距均至少为二，支持均在 $[0,N)$，故二者同属 $D_N$。第零位已不同，因此每个非空前缀都不同；实际标量差为

$$
\begin{aligned}
\kappa(b^{(N)})-\kappa(c^{(N)})
&=1-\sum_{j=2}^{N-1}t^j\\
&=1-\frac{t^2(1-t^{N-2})}{1-t}
=t^{N-2}.
\end{aligned}
$$

$N=2$ 的和为空，见证为低位优先的 $10$ 与 $00$，仍取得一。于是同一对合法来源同时取得每个 $1\le k<N$ 的精确距离。$k=N$ 直接复用定理23.2的完整来源间距与最高位达到对。

按目标前缀 $w$ 取有限类别

$$
C_w=\{\kappa(\omega):\omega\in D_N,\ \pi_k(\omega)=w\}.
$$

若一个记录与不同类别的 $x,y$ 同时相容，闭合同给出

$$
\delta_{N,k}\le|x-y|
\le|x-r|+|r-y|\le2\eta;
$$

开合同将最后一步改为严格小于 $2\eta$。对应充分条件下均矛盾，而真实类别必有相容点，所以相容来源的共同前缀唯一，选择它便得到一个共同正确解码器。也可取任意最近码点并返回其前缀：若最近点属于错误类别，其距离不大于真实点到记录的距离，同一三角不等式又产生矛盾。所有最近点因此都给出正确前缀，不必是唯一来源。

必要性在真前缀情形只使用上述同一实际达到对的中点

$$
\mu_N=\frac{\kappa(b^{(N)})+\kappa(c^{(N)})}{2},
$$

它不依赖 $k$，距两个不同类别均为 $\delta_{N,k}/2$。闭合同在 $2\eta\ge\delta_{N,k}$ 时允许这个共同记录，开合同在 $2\eta>\delta_{N,k}$ 时允许它，故解码失败。完整前缀情形则复用定理23.3的同一中点 $r_N$。$\square$

同前缀最近点并列确实会发生。对 $N\ge2$ 及任意 $1\le k<N$，定理23.3的 $r_N$ 到零码点和仅最高位占用码点的距离均为 $d_N/2$。定理23.2的全点对下界保证没有第三点更近，故这两个不同来源同时最近；二者的前 $k$ 位却均为零。闭半径 $\eta=d_N/2$ 仍严格小于真前缀阈值 $\delta_{N,k}/2$，该记录符合正确前缀合同。开合同可取 $d_N/2<\eta\le\delta_{N,k}/2$。这显示类别恢复容许多个同答案来源，不能要求完整来源唯一。

类别距离也给出所需的近似访问条件。记 $d(r,C_w)=\min_{x\in C_w}|r-x|$；每个类别距离是 $r$ 的 $1$-Lipschitz 函数。闭合同严格低于阈值时，若 $w$ 是真实类别、$v\ne w$，则

$$
d(r,C_v)-d(r,C_w)\ge\delta_{N,k}-2\eta>0.
$$

因此可以按该统一距离差预留有限近似预算，不需打破同类别码点的并列。开临界半径 $\eta=\delta_{N,k}/2$ 时，每个实际记录到真实类别的距离严格小于 $\eta$，到任一错误类别的距离严格大于 $\eta$；有限多个类别给出该输入自身的正差。逐步细化 Cauchy 访问，直到一个类别距离被严格认证为最小，就会对每个合法输入终止。实际达到中点的两侧记录具有不同前缀且可任意接近，故这里也没有全输入统一的正额外近似余量或统一查询精度上界。误差预算包含取得及后处理误差，有限固定记录不能代替可细化访问。

所有边界参数可直接列明：$N=1$ 只有 $k=0$ 常值任务和 $k=1$ 距离一的完整任务；$N=2$ 有 $\delta_{2,1}=1$、$\delta_{2,2}=t$。对固定 $N\ge2$，全部非空真前缀的阈值相同，比完整来源阈值大固定因子

$$
\frac{\delta_{N,k}}{d_N}=t^{-1}=\phi\qquad(1\le k<N).
$$

在真前缀范围内继续缩短 $k$ 不再提高这个最坏阈值。未要求输出的尾部仍参与测量：

$$
\kappa(\omega)
=\sum_{j<k}\omega_j(-t)^j+(-t)^k\kappa(\delta^k\omega).
$$

上述实际达到对正利用合法尾部抵消把不同首位的读数推近。对任意固定非空 $k$，令允许支持 $N\to\infty$，就有 $\delta_{N,k}=t^{N-2}\to0$；这不提供无支持上界的统一正单样本余量。

若目标是前 $h$ 个三位窗口，整数 $h\ge0$，已知支持以外的位固定为零，故该任务等价于

$$
k=\min(3h,N).
$$

$h=0$ 或 $N=0$ 为常值任务；$0<3h<N$ 使用真前缀距离 $t^{N-2}$；$3h\ge N\ge1$ 使用完整来源距离 $t^{N-1}$。特别地，$N=1,2$ 时任意 $h\ge1$ 均是完整来源任务。这里 $h$ 仅指定输出窗口数，仍只取得当前一个实记录。

### 23.丁 任意有限来源集与无界支持的区别

**命题 23.6（任意有限子域的完整地址与任务类别）。** 设 $\mathcal F\subset D$ 是解码器已知的非空有限集合。精确当前标量按定理14.7直接唯一标识其完整地址。若 $|\mathcal F|\ge2$，置

$$
d_{\mathcal F}
=\min_{\substack{\omega,\nu\in\mathcal F\\\omega\ne\nu}}
|\kappa(\omega)-\kappa(\nu)|>0.
$$

对全部 $\mathcal F$ 来源及全部允许实记录，完整地址恢复的闭误差条件为 $2\eta<d_{\mathcal F}$，正开误差条件为 $2\eta\le d_{\mathcal F}$。若 $\mathcal F$ 为单点，常值解码不需记录或误差约束。

首窗任务另按不同 $\sigma_0$ 类别取最小距离 $d_{\mathcal F}^{\mathrm{win}}$；有至少两个首窗类别时，其闭、正开条件分别为 $2\eta<d_{\mathcal F}^{\mathrm{win}}$、$2\eta\le d_{\mathcal F}^{\mathrm{win}}$。全部来源首窗相同时，首窗任务为常值，不施加半径限制。

证明。有限性和既有单射性给出正的完整最小距离。定理23.3的最近点及达到对中点论证仅使用这两个性质，将 $S_N,d_N$ 换为 $\kappa(\mathcal F),d_{\mathcal F}$ 即得完整地址结论。首窗任务使用推论23.5的类别论证，将前缀类换为首窗类即可；不需要完整来源唯一相容。有限 $\mathcal F$ 总包含于某个 $D_N$，故 $d_{\mathcal F}\ge d_N$ 是可用的下界，但不必是其精确值。$\square$

去掉有限子域或统一支持上界后，定理23.2的零地址与最高位单独占用地址给出任意小的完整来源距离，同一中点排除 $D$ 上任何正的统一完整地址误差半径。不过 $N\ge4$ 时这对来源的首个三位窗口相同，均为 null；该达到对本身不证明首窗任务失败。首窗的一次记录障碍由命题22.7的不同首窗实际来源对给出。

一次精确当前颜色、一次完整标量的完整地址恢复、一次实误差记录的任务类别恢复，以及第16章的 $h+1$ 个实际连续取得，是不同合同。多次实际响应的相邻残差可以消去尾部，不能把它们替换为一次有误差值的逆算输出。上述间距和精度结果均以这些明确的对象、支持、任务和访问条件为范围。

### 23.戊 数学依据

有界来源域及 padding 合同使用约定12.1，位级标量与三位分组的对应使用定义1.1后的共轭公式及定义14.5，单射性使用定理14.7。实际有限分块、极值、全点对距离由定理23.2给出；完整地址误差判据和访问条件由定理23.3、命题23.4给出；推论23.5直接使用定理23.2的首位块间隙与完整间距，补充真前缀的共同实际见证和类别访问。任意有限子域引用命题23.6。单标量首窗的无界支持边界使用命题22.7，实际多次取得的不同阈值引用定理16.2–16.5。

## 追加锚（本行以下为增补区）

## 24. 连通观察的正裕量最小七格与右归属七格的尖锐噪声预算

### 24.1 实际闭分支、来源域与统一仪器

**定义 24.10（两次实际取得的含噪首窗合同）。** 沿用定义14.5的低到高三位窗口、合法地址域 $\Omega$、最终为 null 的实际有限来源域 $D$、三位删除 $T=\sigma^3$ 和编码 $\kappa_s$。本章固定

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad H=1+g=2t,
$$

$$
X=[-1,\phi],\qquad I=[-1,t],\qquad
\mu=\frac{t^2}{8}=\frac{g}{4H}=\frac{3-\sqrt5}{16}.
$$

$H$ 是仿射误差系数，窗口视界另记为 $L$。半径 $\mu$ 使用上述 $\kappa$ 坐标归一化；若把坐标乘以常数，误差半径也按其绝对值缩放。

标签集为 $\Lambda=\{3,0,5,2,25\}$，其中 $0=\mathrm{null}$，$25$ 是三位词 $101$ 的单个窗口标签。五条带标签实际闭图为

$$
\begin{aligned}
S_3&=\{(-t-gy,y):y\in X\},&
S_0&=\{(-gy,y):y\in X\},\\
S_5&=\{(t^2-gy,y):y\in I\},&
S_2&=\{(1-gy,y):y\in X\},\\
S_{25}&=\{(2-t-gy,y):y\in I\}.&&
\end{aligned}
$$

统一记 $f_\ell(y)=\Delta_\ell-gy$，合法尾域记为 $I_\ell$；$I_3=I_0=I_2=X$，$I_5=I_{25}=I$。定理17.2保证每个合法闭图点都由同一条实际 $\Omega$ 地址的相邻样本共同实现，反方向也成立；特别地，端点属于实际合同。有限来源的带标签子集记为 $S_\ell^D$，不将它等同于整个闭图。

量化器 $Q:X\to\{0,\ldots,q-1\}$ 的每个纤维 $C_i$ 是非空区间，标签从左到右编号；可以有单点格和任意合法端点归属。同一个 $Q$ 用于两个坐标，一个固定确定解码器 $d_7$ 只取得两个箱号。对真实点 $p=(f_\ell(y),y)$，先分别加误差，再裁剪：

$$
(u,v)=\operatorname{clip}_{X^2}(p+(\varepsilon_0,\varepsilon_1)),
\qquad d_7(Q(u),Q(v))=\ell.
$$

闭预算 $\nu\ge0$ 要求对所有 $|\varepsilon_0|,|\varepsilon_1|\le\nu$ 成立；正开预算 $\nu>0$ 要求对所有 $|\varepsilon_0|,|\varepsilon_1|<\nu$ 成立。误差可任意分别选择，没有随机性或概率独立假设；箱号记录本身准确。来源域必须明确为全部 $\Omega$ 或全部 $D=\bigcup_ND_N$。下界中的解码器可任意取；$d_7$ 不与第17章的五色解码器混用。

全布局预算定理使用更窄的严格右归属七格类：

$$
\begin{gathered}
-1<a<b<c<d<e<f<\phi,\\
C_0=[-1,a),\quad C_1=[a,b),\quad C_2=[b,c),\\
C_3=[c,d),\quad C_4=[d,e),\quad C_5=[e,f),\quad C_6=[f,\phi].
\end{gathered}
$$

字母 $d$ 是切点，$d_7$ 是解码器。最小格数定理则允许前述更广的连通区间类。

以下代数界供全部证明使用：

$$
t^2+t=1,\qquad g^2+4g=1,\qquad
\frac8{13}<t<\frac58,\qquad
\frac3{13}<g<\frac14.
$$

正轴上 $x^2+x$ 严格递增，在 $8/13$ 与 $5/8$ 的值分别为 $168/169$ 与 $65/64$，故得到 $t$ 的界；$g=2t-1$ 给出其余界。特别地 $1/5<g<1/4$、$H>1$。裁剪到包含真实点的闭区间不增加误差，所以始终有

$$
|u-f_\ell(y)|\le\nu,\qquad |v-y|\le\nu.
$$

### 24.2 闭网格纯性与至多六格障碍

**引理 24.11（闭网格纯性与统一正裕量）。** 令 $J_i=\overline{C_i}$、$R_{ij}=J_i\times J_j$。对有限个非空区间格，存在一个确定解码器和一个正的统一误差裕量，当且仅当每个 $R_{ij}$ 至多与一种标签的闭图 $S_\ell$ 相交。

证明。若同一闭矩形与不同标签的真实点 $p,p'$ 相交，$C_i\times C_j$ 在 $R_{ij}$ 中相对稠密。对任意 $\eta>0$，分别选属于该实际格对的目标 $z,z'$，使

$$
\|z-p\|_\infty<\eta,\qquad \|z'-p'\|_\infty<\eta.
$$

各来源直接采用误差 $z-p$、$z'-p'$，目标在 $X^2$ 内，裁剪固定它们。两来源于是取得相同箱号对 $(i,j)$，标签却不同。这里不需要格具有内部：若 $C_i$ 是单点，$\overline{C_i}=C_i$，该坐标的目标就固定为此点；其他坐标仍按相对稠密性选取。因此单点格和任意端点归属也满足这项必要性，且任意正开预算同样被排除。

反过来，若闭网格纯，定义

$$
\delta=\min_{\substack{\ell,i,j\\S_\ell\cap R_{ij}=\varnothing}}
\operatorname{dist}_\infty(S_\ell,R_{ij}).
$$

每个 $S_\ell,R_{ij}$ 都非空紧；不相交时距离严格为正。参与最小值的集合非空：每个矩形至多遇一种标签，故至少有四种标签与之不相交。有限性给出 $\delta>0$。把遇到 $S_\ell$ 的格对解码为 $\ell$，未遇任何图的格对任意补全。取 $\eta=\delta/2$。若真实标签为 $\ell$，含噪观察在 $C_i\times C_j$，则

$$
\operatorname{dist}_\infty(S_\ell,R_{ij})\le
\|(u,v)-p\|_\infty\le\eta<\delta.
$$

因而 $S_\ell$ 必与该矩形相交；纯性保证解码正确。$\square$

**定理 24.12（包括单点格的六格正裕量障碍）。** 在全部 $\Omega$ 上，任何至多六个非空连通区间格、任意端点归属的统一相邻仪器，都没有正的统一误差裕量。

证明。正裕量迫使引理24.11的纯性，以下只用这个必要条件。先设恰有六格，编号 $0,\ldots,5$。共同合法尾 $-1$ 和 $t$ 分别产生按标签 $3,0,5,2,25$ 排列的五个严格递增当前点：

$$
(-t^2,\ g,\ t,\ 2t,\ \phi),
\qquad
(-t-t^4,\ -t^4,\ g,\ 1-t^4,\ 2t).
$$

每行的五个箱号必须不同。第一行使 $Q(2t)\le4$，第二行的五个箱号于是恰为 $0,1,2,3,4$。合并两行得到

$$
Q(g)=2,\quad Q(t)=3,\quad Q(2t)=4,\quad Q(\phi)=5,
\qquad Q(-t^2)\in\{0,1\}.
$$

若 $Q(-t^2)=0$，共同合法尾 $\phi$ 下的标签 $3,0$ 分别给当前值 $-1,-t^2$，均产生 $(0,5)$。故 $Q(-t^2)=1$。

合法常值地址 $3^\infty,0^\infty,5^\infty,2^\infty$ 的相邻坐标分别是

$$
(-1/2,-1/2),\quad(0,0),\quad(s,s),\quad(r,r),
\qquad s=t/2,\quad r=\phi/2.
$$

四个箱号必须不同。所需严格次序为

$$
-t-t^4<-1/2<-t^2<-t^4<0<g<s<t<r<1-t^4.
$$

其中 $g<s$ 由 $t<2/3$ 得到；$r<1-t^4$ 等价于 $t>3/5$。其余次序由上述代数界得到。$t$ 与 $1-t^4$ 的箱号均为 $3$，故 $Q(r)=3$；$s$ 夹在箱号 $2,3$ 的点之间且不能取 $3$，故 $Q(s)=2$；继续向左得到 $Q(0)=1$、$Q(-1/2)=0$。

记闭包端点为

$$
J_i=[\beta_i,\beta_{i+1}],\qquad
-1=\beta_0\le\beta_1\le\cdots\le\beta_6=\phi.
$$

相邻非空区间覆盖 $X$，故确有此表示；单点格对应相邻端点相等。已确定的箱号给出

$$
-1/2\le\beta_1\le-t^2,\quad
0\le\beta_2\le g,\quad
s\le\beta_3\le t,\quad
1-t^4\le\beta_4\le2t\le\beta_5.
$$

对闭尾格定义

$$
\mathcal E_\ell(j)=
\{i:\exists y\in J_j\cap I_\ell,\ f_\ell(y)\in J_i\}.
$$

每列的不同标签集合必须两两不交；边界点仍同时属于相邻闭格。

尾格 $0$ 包含 $-1,-1/2$。标签 $3$ 已占当前闭格 $1,0$；其余四个标签在尾 $-1$ 依次占当前闭格 $2,3,4,5$。纯性用尽全部六格，故这一列按标签 $3,0,5,2,25$ 恰为

$$
\{0,1\},\quad\{2\},\quad\{3\},\quad\{4\},\quad\{5\}.
$$

共同边界 $\beta_1$ 把标签 $0,5,2,25$ 的当前格 $2,3,4,5$ 传入尾格 $1$。固定点 $0\in J_1$ 使标签 $0$ 还占当前格 $1$；而

$$
-1\le f_3(\beta_1)\le f_3(-1/2)=-1/2\le\beta_1
$$

使标签 $3$ 占当前格 $0$。纯性再次用尽六格，故尾格 $1$ 的列恰为

$$
\{0\},\quad\{1,2\},\quad\{3\},\quad\{4\},\quad\{5\}.
$$

共同边界 $\beta_2$ 把标签 $5,2,25$ 的当前格 $3,4,5$ 传入尾格 $2$，标签 $5$ 的固定点 $s\in J_2$ 又占当前格 $2$。还须核对另外两标签：

$$
f_3(\beta_2)\le-t<-1/2\le\beta_1,
\qquad
\beta_1\le-t^2\le-g^2\le f_0(\beta_2)\le0\le\beta_2.
$$

两来源合法且当前值在 $X$ 中，因此它们分别占闭格 $0,1$。本列的六个当前格已经由各标签占尽，特别地 $\mathcal E_2(2)=\{4\}$。

共同边界 $\beta_3$ 于是把标签 $2$ 的当前格 $4$ 传入尾格 $3$。但 $\beta_3\le t<1-t^4\le\beta_4$，故 $t\in J_3$；合法标签 $25$ 在尾 $t$ 的当前值为 $2t\in J_4$。同一列中标签 $2,25$ 都占当前格 $4$，矛盾。

五格时，两行五点都必须依次取箱号 $0,1,2,3,4$，却令共享点 $g$ 同时取箱号 $1$ 和 $2$。少于五格连共同尾 $-1$ 下的五种标签也不能区分。故全部至多六格均被排除。证明中只有闭格和相对稠密性，没有正格长假设。$\square$

### 24.3 平移 $\mu$ 的严格七格构造

**定理 24.13（一个固定解码器的全域包含表）。** 取

$$
a=-\frac12+\mu,\quad b=\mu,\quad c=g+\mu,\quad
d=t+\mu,\quad e=1+\mu,\quad f=2t+\mu
$$

及定义24.10的右归属七格。存在一个固定确定解码器 $d_7$，对全部 $\Omega$ 的每个闭预算 $0\le\nu<\mu$ 和每个正开预算 $0<\nu\le\mu$ 同时正确。

证明。七个格长依次为

$$
\frac12+\mu,\quad\frac12,\quad g,\quad
t^2,\quad t^2,\quad g,\quad t^2-\mu=\frac78t^2,
$$

全部严格为正。对任意实切点 $z$，裁剪后的坐标满足

$$
v\le z\ \Longrightarrow\ u\ge f_\ell(z)-H\nu,
\qquad
v\ge z\ \Longrightarrow\ u\le f_\ell(z)+H\nu.
$$

例如前一式由 $y\le z+\nu$、分支递减和 $u\ge f_\ell(y)-\nu$ 得到。这里只计算仿射表达式；真实尾 $y$ 始终留在 $I_\ell$ 内。

以下五个边界等式使用 $4H\mu=g$：

$$
\begin{aligned}
f_3(a)+H\mu&=a,& f_0(b)+H\mu&=b,\\
f_0(a)-H\mu&=b,& f_2(a)-H\mu&=e,\\
f_2(b)+H\mu&=e.&&
\end{aligned}
$$

第一式利用固定点 $-1/2$，第二式利用固定点 $0$；第三式的差为

$$
f_0(a)-H\mu-b=g/2-(g+H+1)\mu
=g/2-2H\mu=0.
$$

后两式由 $f_2=f_0+1$ 得到。其余所需严格分离量为

$$
\begin{aligned}
f_5(b)-H\mu-c&=g^2/2>0,\\
f_{25}(b)-H\mu-f&=g^2/2>0,\\
f_2(b)-H\mu-d&=t^2-g/2>0,\\
f_2(d)-H\mu-d&=g/2>0.
\end{aligned}
$$

第一量等于 $t^2-g-2H\mu=(1-4g)/2=g^2/2$；第二量由 $f_{25}=f_5+1$、$f=c+1$ 得到。第三量等于 $t^2(1-t/2)$。第四量等于 $1-2t^2-g/2=g/2$。

五分支真实当前像依次为

$$
[-1,t-1],\quad[t-1,g],\quad[g,t],\quad[t,2t],\quad[2t,\phi].
$$

对 $\nu<\mu$，全域含噪观察范围及当前箱号如下。

| 24.13 当前支 | 全域观察范围 | 当前箱号 |
| --- | --- | --- |
| 七格当前支 $3$ | $[-1,b)$ | $\{0,1\}$ |
| 七格当前支 $0$ | $(a,c)$ | $\{1,2\}$ |
| 七格当前支 $5$ | $(b,d)$ | $\{2,3\}$ |
| 七格当前支 $2$ | $(c,f)$ | $\{3,4,5\}$ |
| 七格当前支 $25$ | $(e,\phi]$ | $\{5,6\}$ |

全部端点比较为

$$
\begin{aligned}
b-(t-1+\mu)&=t^2>0,\\
(t-1-\mu)-a&=g/2-2\mu=\frac{g^2}{2H}>0,\\
g+\mu&=c,\\
(g-\mu)-b&=g-2\mu=g\left(1-\frac1{2H}\right)>0,\\
t+\mu&=d,\\
(t-\mu)-c&=t^2-2\mu=\frac34t^2>0,\\
2t+\mu&=f,\\
(2t-\mu)-e&=g-2\mu>0.
\end{aligned}
$$

等式处用 $\nu<\mu$ 获得严格界。标签 $5,25$ 的真实尾域还给出 $v\le t+\nu<d$，故未来箱号 $4,5,6$ 对它们不可能。

列为未来箱号、表项为当前箱号的包含集合：

| 24.13 未来支 | $0$ | $1$ | $2$ | $3$ | $4$ | $5$ | $6$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 七格未来支 $3$ | $\{0,1\}$ | $\{0\}$ | $\{0\}$ | $\{0\}$ | $\{0\}$ | $\{0\}$ | $\{0\}$ |
| 七格未来支 $0$ | $\{2\}$ | $\{1,2\}$ | $\{1\}$ | $\{1\}$ | $\{1\}$ | $\{1\}$ | $\{1\}$ |
| 七格未来支 $5$ | $\{3\}$ | $\{3\}$ | $\{2,3\}$ | $\{2,3\}$ | $\varnothing$ | $\varnothing$ | $\varnothing$ |
| 七格未来支 $2$ | $\{5\}$ | $\{4,5\}$ | $\{4\}$ | $\{4\}$ | $\{3,4\}$ | $\{3,4\}$ | $\{3,4\}$ |
| 七格未来支 $25$ | $\{6\}$ | $\{6\}$ | $\{5,6\}$ | $\{5,6\}$ | $\varnothing$ | $\varnothing$ | $\varnothing$ |

逐行核对如下。标签 $3$ 在未来箱号至少为 $1$ 时有 $v\ge a$，故 $u\le f_3(a)+H\nu<a$，当前箱号为 $0$；未来箱号 $0$ 使用全域范围。

标签 $0$ 在未来格 $0$ 中有 $v<a$，故 $u\ge f_0(a)-H\nu>b$，结合 $u<c$ 得当前格 $2$；未来箱号至少为 $2$ 时有 $v\ge b$，故 $u\le f_0(b)+H\nu<b$，结合 $u>a$ 得格 $1$；未来格 $1$ 使用全域范围。

标签 $5$ 在未来格 $0,1$ 中有 $v<b$，故 $u\ge f_5(b)-H\nu>c$，结合 $u<d$ 得格 $3$。未来格 $2,3$ 使用全域范围；其余未来格由真实尾域排除。

标签 $2$ 在未来格 $0$ 中有 $v<a$，故 $u>e$，结合 $u<f$ 得格 $5$；在未来格 $1$ 中有 $v<b$，故 $u>d$，只能在格 $4,5$。未来格 $2,3$ 中 $b\le v<d$，两端估计分别给 $u<e$ 与 $u>d$，故当前格为 $4$。未来格 $4,5,6$ 中仍有 $v\ge b$，故 $u<e$，结合全域 $u>c$ 得格 $3,4$。

标签 $25$ 在未来格 $0,1$ 中有 $v<b$，故 $u\ge f_{25}(b)-H\nu>f$，当前格为 $6$；未来格 $2,3$ 使用全域范围，其余未来格由真实尾域排除。

每列的不同标签集合两两不交。令 $d_7(i,j)$ 等于表中唯一包含 $i$ 的标签；没有出现的格对统一补为标签 $0$。这给出一个与 $\nu$ 无关的全定义解码器。表是充分包含表，不要求每个表项都可达；所有空项均由尾域证明。对开预算 $\mu$ 中任一误差对，取 $r=\max(|\varepsilon_0|,|\varepsilon_1|)<\mu$，调用同一解码器的闭预算 $r$ 结论。更小正开预算随即成立。$\square$

### 24.4 同标签有限稠密性与精确观察目标转移

**命题 24.14（保标签的严格余量转移）。** 对每个 $\ell\in\Lambda$，有 $\overline{S_\ell^D}=S_\ell$。对任何固定 $Q$ 和固定解码器、任意 $\nu>0$：

$$
\begin{aligned}
D\text{ 上闭预算 }\nu\text{ 正确}
&\ \Longrightarrow\ \Omega\text{ 上开预算 }\nu\text{ 正确},\\
D\text{ 上开预算 }\nu\text{ 正确}
&\ \Longleftrightarrow\ \Omega\text{ 上开预算 }\nu\text{ 正确}.
\end{aligned}
$$

$\Omega$ 上任一预算正确均可限制到 $D$。上述转移不要求 $Q$ 连续或纤维连通。

证明。按定理17.2，对合法尾坐标 $y$ 取合法尾地址 $\eta$。保留其前 $n$ 个窗口，后续置为 $0^\infty$，记为 $\eta^{(n)}$。将位改为零不制造相邻一；前接 $\ell$ 的接缝也保持合法。于是 $\ell\eta^{(n)}\in D$，首标签始终为 $\ell$。窗口级数给出

$$
\kappa(\eta)-\kappa(\eta^{(n)})
=(-g)^n\kappa(T^n\eta),\qquad
|\kappa(\eta)-\kappa(\eta^{(n)})|\le\phi g^n\longrightarrow0.
$$

当前坐标差是尾坐标差的 $g$ 倍，故相邻点的最大范数差也不超过 $\phi g^n$。这是逐标签稠密性；其反向包含由闭图的闭性得到。

现在固定 $\Omega$ 中标签为 $\ell$ 的真实点 $p$，以及由严格小于 $\nu$ 的误差产生的实际裁剪目标 $z$。裁剪不增加误差，故 $\|z-p\|_\infty<\nu$。可取同标签有限真实点 $p_D$，满足

$$
\|p_D-p\|_\infty<\nu-\|z-p\|_\infty.
$$

为这个有限来源直接选新误差 $\varepsilon_D=z-p_D$。则

$$
\|\varepsilon_D\|_\infty<\nu,\qquad
\operatorname{clip}_{X^2}(p_D+\varepsilon_D)=z.
$$

目标是完全相同的 $z$，不是仅仅接近 $z$；因此箱号完全相同，切点归属和 $Q$ 的连续性均无关。$D$ 上的闭或开正确性都强迫该记录解码为 $\ell$。限制方向直接，证明结论。$\square$

特别地，$D$ 上闭预算 $\nu>0$ 给同一仪器在 $\Omega$ 上每个闭预算 $0\le r<\nu$ 的正确性。严格余量是关键：当目标距真实点恰为 $\nu$ 时，有限近似的新误差可超过 $\nu$，故这里没有得到 $D$ 闭预算 $\nu$ 推出 $\Omega$ 闭预算 $\nu$。闭临界失败须另有实际有限见证。

### 24.5 不依赖预选包含表的端点二分

**引理 24.15（实际共同尾强迫 $B\in\{2,3\}$）。** 对任何在 $\Omega$ 上有正裕量的严格右归属七格仪器，记

$$
\begin{gathered}
A=Q(-t^2),\quad B=Q(g),\quad C=Q(t),\quad D_\ast=Q(2t),\\
E=Q(-t-t^4),\quad F_0=Q(-t^4),\quad G=Q(1-t^4).
\end{gathered}
$$

$D$ 仍表示实际有限来源，$D_\ast$ 只是端点箱号。则 $B\in\{2,3\}$。若 $B=3$，有 $C=G=4,D_\ast=5$；若 $B=2$，有 $E=0,A=F_0=1$，且 $C=3$ 或 $4$，后一情形有 $C=G=4,D_\ast=5$。

证明。共同合法尾 $-1,t$ 的两行五点迫使

$$
A<B<C<D_\ast<6,\qquad E<F_0<B<G<D_\ast.
$$

共同合法尾 $\phi$ 下的标签 $3,0$ 还迫使 $A\ge1$。所以 $2\le B\le3$。若 $B=3$，第一行给 $C=4,D_\ast=5$；由 $t<1-t^4$ 和第二行得 $4=C\le G<5$，故 $G=4$。若 $B=2$，第二行给 $E=0,F_0=1$，而 $E\le A\le F_0$ 与 $A\ge1$ 给 $A=1$；第一行给 $C=3$ 或 $4$。$C=4$ 时同理得 $D_\ast=5,G=4$。全部比较来自实际来源与有序纤维。$\square$

**引理 24.16（实际预算的闭矩形距离必要条件）。** 对严格七格，令

$$
\delta_{\ell,ij}=\operatorname{dist}_\infty(S_\ell,R_{ij}).
$$

若正闭预算 $\nu$ 对全部 $\Omega$ 正确，则对不同标签 $\ell,m$ 必有

$$
\max(\delta_{\ell,ij},\delta_{m,ij})\ge\nu.
$$

证明。若两距离都严格小于 $\nu$，紧性给出各自合法源点和闭矩形目标。严格非空区间的内部在闭包中稠密，故可将两目标分别稍移入 $(\operatorname{int}C_i)\times(\operatorname{int}C_j)$，保持两误差最大范数严格小于 $\nu$。外端格也有非空内部；目标仍在 $X^2$ 内，裁剪固定它们。两标签于是取得同一实际箱号对，矛盾。这里只推出非严格的距离必要条件，不把闭格等距接触当成实际闭预算碰撞。$\square$

### 24.6 $B=3$ 的实际尾距离与预算证书

**命题 24.17（$B=3$ 时 $\nu\le g/5<\mu$）。** 任何 $B=3$ 的严格七格仪器在 $\Omega$ 上的可行正闭预算都满足 $\nu\le g/5$。

证明。引理24.15与右归属给出

$$
-1<a\le-t^2<0,\quad a<b<c\le g,\quad g<d\le t,
\qquad 1-t^4<e\le2t<f<\phi.
$$

令 $s=t/2,r=\phi/2$。有 $g<s<t<r<1-t^4$，故标签 $2$ 的合法固定点 $(r,r)$ 在实际格 $(4,4)$。若 $d\le s$，标签 $5$ 的固定点也在该格，零误差即失败；所以 $d>s$，标签 $5$ 固定点在格 $(3,3)$。

先核对三个距离：

$$
\delta_{0,33}=[c]_+,\qquad
\delta_{5,44}=d-s,\qquad
\delta_{2,60}=f-2t,\qquad [z]_+=\max(z,0).
$$

null 图上至少一个坐标不大于 $0$，点 $(0,0)$ 达到第一距离；$c\le0$ 时此点已在闭格内。标签 $5$ 图上至少一个坐标不大于固定点 $s$，点 $(s,s)$ 达到第二距离。标签 $2$ 当前值最大为 $2t$，实际端点 $(2t,-1)$ 达到第三距离。相应另一标签的零距离见证为标签 $5$ 的 $(s,s)$、标签 $2$ 的 $(r,r)$、标签 $25$ 的 $(\phi,-1)$。引理24.16给出

$$
c\ge\nu>0,\qquad d\ge s+\nu,\qquad f\ge2t+\nu.
$$

下面列出证书用到的全部八个距离。表中 $q$ 表示该行的正距离；“加 $q$”或“减 $q$”指源点由目标角点的两个坐标同时加或减 $q$ 得到。

| 24.17 距离项 | 精确距离 | 正值目标与方向 | 正值合法源尾 | 零值源尾 |
| --- | --- | --- | --- | --- |
| 距甲：$\delta_{5,30}$ | $[(t^2-d-ga)/H]_+$ | $(d,a)$，加 $q$ | $(a+t^2-d)/H$ | $a$ |
| 距乙：$\delta_{2,41}$ | $[(1-e-gb)/H]_+$ | $(e,b)$，加 $q$ | $(b+1-e)/H$ | $b$ |
| 距丙：$\delta_{2,53}$ | $[(e+gc-1)/H]_+$ | $(e,c)$，减 $q$ | $(c+1-e)/H$ | $c$ |
| 距丁：$\delta_{25,53}$ | $[(2-t-f-gd)/H]_+$ | $(f,d)$，加 $q$ | $(d+2-t-f)/H$ | $d$ |
| 距戊：$\delta_{5,42}$ | $[(d+gb-t^2)/H]_+$ | $(d,b)$，减 $q$ | $(b+t^2-d)/H$ | $b$ |
| 距己：$\delta_{2,42}$ | $[(1-e-gc)/H]_+$ | $(e,c)$，加 $q$ | $(c+1-e)/H$ | $c$ |
| 距庚：$\delta_{0,31}$ | $[(c+ga)/H]_+$ | $(c,a)$，减 $q$ | $(a-c)/H$ | $a$ |
| 距辛：$\delta_{5,31}$ | $[(t^2-d-gb)/H]_+$ | $(d,b)$，加 $q$ | $(b+t^2-d)/H$ | $b$ |

这些是到有限合法线段的距离。证明下界时，用源点的恒等式 $x+gy=\Delta_\ell$：若矩形右上角在直线下侧，差为 $\Delta_\ell-u_+-gv_+$；若左下角在直线上侧，差为 $u_-+gv_--\Delta_\ell$。任意最大范数误差 $q$ 对 $x+gy$ 的改变至多为 $Hq$，故得到表中的非负部分下界。

正值时表中的角点和源尾达到下界，且源尾合法，核对如下。距甲的尾 $(a+t^2-d)/H$ 属于 $(-1,s)$：分子由 $a>-1,d\le t$ 严格大于 $-H$，由 $a<0<d$ 严格小于 $t^2=Hs$。距乙的尾属于 $(-1,1)$：$b>-1,e\le H$ 给下界，$b<g,e>0$ 给上界。距丙、己的共同尾 $(c+1-e)/H$ 也属于 $(-1,1)$，其分子大于 $-g>-H$ 且小于 $H$。距丁正值尾等于 $d+q>0$；由 $d\le t,f>2t$，分子严格小于 $Ht$，故尾在 $(0,t)$。距戊、辛的共同尾属于 $(-1,s)$，其分子大于 $-H$，又由 $b<c\le g<d$ 严格小于 $t^2$。距庚的尾 $(a-c)/H$ 属于 $(-1,0)$，因为 $a>-1,c\le g$、$a<0<c$。这些范围分别包含于标签 $5,25,2,0$ 的真实尾域；两个源坐标均来自所列同一个尾。

未截断表达式非正时，所列零值尾也合法，且当前值确在对应闭当前格：

$$
\begin{array}{c|l}
\text{距甲}&c<t^2<f_5(a)\le d\\
\text{距乙}&d\le t<1-g^2<f_2(b)\le e\\
\text{距丙}&e\le f_2(c)<1<f\\
\text{距丁}&e\le2t\le f_{25}(d)\le f\\
\text{距戊}&d\le f_5(b)<t<e\\
\text{距己}&d\le t<1-g^2\le f_2(c)\le e\\
\text{距庚}&c\le f_0(a)<g<d\\
\text{距辛}&c\le g<f_5(b)\le d.
\end{array}
$$

其中 $1-g^2>t$ 等价于 $(7g-1)/2>0$，由 $g>1/5$ 保证；$c\le g<t^2$，$a,b,c<t$，$d\le t$，所以零值尾同样没有越界。至此全部正值、零值距离均已核对，负的有符号表达式只表示距离为零。

现在使用这些距离。null 的实际端点 $(g,-1)$ 已在闭格 $(3,0)$，距甲与引理24.16给出

$$
d\le t^2-ga-H\nu.
$$

故标签 $5$ 在真实尾 $a$ 的当前值严格大于 $d$，又严格小于 $t<e$；尾 $a$ 归实际格 $1$，所以该标签实际占用 $(4,1)$。距乙给出

$$
e\le1-gb-H\nu.
$$

若 $\nu\le g/8$，结论已成立。以下设 $\nu>g/8$。由前面的辅助条件，

$$
\frac{2-t-f-gd}{H}
\le\frac{2-t-(2t+\nu)-g(s+\nu)}H
=\frac g4-\nu<\nu.
$$

取非负部分仍严格小于 $\nu$，故距丁小于预算；在闭格 $(5,3)$ 中，距丙必须至少为 $\nu$，即

$$
e\ge1-gc+H\nu.
$$

这使距己为零，故闭格 $(4,2)$ 中的距戊必须至少为 $\nu$，得到

$$
d\ge t^2-gb+H\nu.
$$

后式又使距辛为零；闭格 $(3,1)$ 中的距庚于是至少为 $\nu$，得到

$$
c\ge-ga+H\nu.
$$

合并上下界，

$$
g(b-a)\ge2H\nu,\qquad g(c-b)\ge2H\nu,
$$

$$
4H\nu\le g(c-a)\le Hc-H\nu.
$$

因此 $5\nu\le c\le g$，即 $\nu\le g/5$。最后 $g<1/4$ 给 $4H<5$，故 $g/5<g/(4H)=\mu$。这里不要求右侧界 $g/5$ 可取得。$\square$

### 24.7 开临界预算的必要切点刚性

**定理 24.18（开预算 $\mu$ 强迫前三个切点）。** 若某个严格右归属七格仪器在全部 $\Omega$ 上对开预算 $\mu$ 正确，则

$$
a=-\frac12+\mu,\qquad b=\mu,\qquad c\ge g+\mu.
$$

这是必要条件，不是其余切点的分类或充分性陈述。

证明。该仪器对每个闭预算 $0<\nu<\mu$ 都正确。命题24.17排除 $B=3$，否则选 $g/5<\nu<\mu$ 即矛盾。因此 $B=2$，引理24.15给

$$
E=0,\qquad A=F_0=1,\qquad C=3\text{ 或 }4.
$$

先证明两支均有 $c\ge g+\mu$。

当 $C=3$，共同合法尾 $-1$ 下，null 和标签 $5$ 的当前值为 $g,t$，在相邻格 $2,3$。对每个 $0<\nu<\mu$ 必有 $c>g+\nu$，否则把 null 当前坐标从 $g$ 扰到右归属切点 $c$，取得 $(3,0)$，与标签 $5$ 的零误差记录相同。令 $\nu\uparrow\mu$，得到 $c\ge g+\mu$。

当 $C=4$，有 $G=4,D_\ast=5$，切点满足

$$
-t-t^4<a\le-t^2<0,\quad -t^4<b\le g<c<d\le t,
\qquad 1-t^4<e\le2t<f<\phi.
$$

共同合法尾 $-1$ 下，标签 $2,25$ 的当前值为 $2t,\phi$，在相邻格 $5,6$。每个闭预算 $\nu<\mu$ 都要求

$$
2t+\nu<f\le\phi-\nu.
$$

若左式失败，把标签 $2$ 扰到 $f$ 就与标签 $25$ 的零误差记录碰撞；若右式失败，标签 $25$ 可以用小于 $\nu$ 的误差进入格 $5$、靠近 $f$，与标签 $2$ 的零误差记录碰撞。取极限得

$$
2t+\mu\le f\le\phi-\mu.
$$

反设 $c<g+\mu$。定义传播阈值

$$
\kappa_{\mathrm p}=\frac{gt^2}{H+1},\qquad
\mu-\kappa_{\mathrm p}
=\frac{g(2-7g)}{4H(H+1)}>0.
$$

这是辅助常数，与地址编码 $\kappa_s$ 分开。选一个闭预算

$$
\max\{c-g,\kappa_{\mathrm p}\}<\nu<\mu.
$$

于是 $g<c<g+\nu$，且 $2t+\nu<f\le\phi-\nu$。所有下述来源和误差都使用这同一个严格子临界闭预算。

null 来源 $(g,-1)$ 可把当前观察选为

$$
c<u_0<\min\{d,g+\nu\},
$$

取得实际记录 $(3,0)$，当前误差严格小于 $\nu$，未来误差为零。再定义两个真实尾

$$
y_5=\frac{t^2-d}{g},\qquad y_2=\frac{1-e}{g}.
$$

由 $g<d\le t$、$1-t^4<e\le2t$，两尾均在 $[-1,t)$。它们分别给出标签 $5$ 的真实点 $(d,y_5)$ 和标签 $2$ 的真实点 $(e,y_2)$。因各格严格非空、$\nu>0$，把当前坐标在对应切点两侧作足够小的扰动，标签 $5$ 可取得当前格 $3,4$，标签 $2$ 可取得当前格 $4,5$；未来观察分别固定为合法的 $y_5,y_2$，裁剪不变。

记 $j_5=Q(y_5),j_2=Q(y_2)$。为避免标签 $5$ 与 null 的 $(3,0)$ 碰撞，必须 $j_5\ge1$。还必须有 $y_2>y_5$。否则 $y_2$ 也是标签 $5$ 的合法尾，且

$$
d=f_5(y_5)\le f_5(y_2)\le t<e.
$$

标签 $5$ 在这个尾零误差取得当前格 $4$，标签 $2$ 则把当前切点 $e$ 向左扰一点也取得格 $4$，未来坐标完全相同，矛盾。于是 $y_2>y_5$ 给 $j_2\ge j_5$；两标签各自又都可取得当前格 $4$，故箱号不能相等。因此

$$
j_2>j_5\ge1,\qquad j_2\ge2.
$$

再令

$$
y_0=\frac{2-t-f-\nu}{g},\qquad
\lambda=y_0-\nu=\frac{2-t-f-H\nu}{g}.
$$

$f\le\phi-\nu$ 给 $y_0\ge-1$，$f>2t+\nu$ 给 $y_0<t$。由 $2-3t=t^4=gt$ 与 $\nu>\kappa_{\mathrm p}$，

$$
\lambda<t-\frac{(H+1)\nu}{g}<t-t^2=g.
$$

选足够小的 $\varepsilon>0$，使

$$
y_{25}=y_0+\varepsilon/g<t,\qquad
e<f-\varepsilon<f,\qquad
\lambda+\varepsilon/g<g.
$$

$y_{25}\ge-1$，故这是合法标签 $25$ 来源，其真实当前值为 $f+\nu-\varepsilon$。两个坐标均加误差 $-\nu$，当前观察为格 $5$ 内的 $f-\varepsilon$，未来观察计入左端裁剪后为

$$
v=\max\{-1,\lambda+\varepsilon/g\}<g.
$$

没有右端裁剪，因为该表达式小于 $g<\phi$。这实际产生记录 $(5,Q(v))$。

必有 $v>y_2$。否则 $v\in[-1,y_2]$ 是标签 $2$ 的合法尾，并且

$$
e=f_2(y_2)\le f_2(v)\le2t<f.
$$

标签 $2$ 在同一未来观察 $v$ 下零误差也取得当前格 $5$，直接碰撞。于是 $v>y_2$ 给 $Q(v)\ge j_2$。标签 $2$ 的真实切点来源 $(e,y_2)$ 又已取得 $(5,j_2)$，所以还须 $Q(v)>j_2\ge2$。但 $v<g$ 与 $Q(g)=2$ 给 $Q(v)\le2$，矛盾。这一支也有 $c\ge g+\mu$。整个传播只用选定的 $\nu<\mu$，没有调用 $\Omega$ 的闭临界正确性。

现在证明负端切点饱和。令 $s=t/2$，有

$$
g+2\mu-s=t^5/4>0,
\qquad c\ge g+\mu>s-\mu.
$$

又 $b\le g<s$，故可取

$$
w_5\in(b,c)\cap(s-\mu,s+\mu).
$$

标签 $5$ 的合法固定点 $(s,s)$ 用严格小于 $\mu$ 的误差将两坐标扰到 $w_5$，取得 $(2,2)$。若 $b<\mu$，因 $c>0$ 还可取

$$
w_0\in(b,c)\cap(-\mu,\mu),
$$

把 null 固定点 $(0,0)$ 扰入同一格对，违反开预算正确性。因此 $b\ge\mu>0$。

$a\le-t^2<0<b$，所以 null 零误差记录为 $(1,1)$。标签 $3$ 的合法固定点为 $(-1/2,-1/2)$。若 $a<-1/2+\mu$，区间 $(a,b)$ 与 $(-1/2-\mu,-1/2+\mu)$ 相交，把该固定点两坐标扰入交集也会取得 $(1,1)$。故

$$
a\ge-\frac12+\mu.
$$

最后，标签 $3$ 的真实端点 $(-t^2,-1)$ 已占实际格 $(1,0)$。null 线段到 $R_{10}=[a,b]\times[-1,a]$ 的精确距离为

$$
q=\left[\frac{-ga-b}{H}\right]_+.
$$

正值时合法源尾 $y_\ast=(a-b)/H$ 属于 $(-1,0)$：由 $a\ge-1/2+\mu,b\le g$，有 $a-b>-1/2-g>-H$，而 $a<0<b$ 给上界。真实点为 $(b+q,a+q)$，目标为角点 $(b,a)$；恒等式 $x+gy=0$ 给相同距离下界。非正时，尾 $a$ 合法且 $a<-ga\le b$，null 点 $(-ga,a)$ 已在闭格内，故距离确为零。

若 $q<\mu$，将达到距离的目标稍移入实际格 $(1,0)$ 的内部，仍保持误差严格小于 $\mu$，就与标签 $3$ 碰撞。目标在支持内，裁剪固定。因此

$$
q\ge\mu,\qquad b+ga+H\mu\le0.
$$

另一方面，前述两个下界给

$$
b+ga+H\mu
\ge\mu+g(-1/2+\mu)+H\mu
=2H\mu-g/2=0.
$$

两边饱和；$g>0$ 迫使 $b=\mu$、$a=-1/2+\mu$，完成必要刚性。这里未把距离等号当成实际临界碰撞。$\square$

### 24.8 通用有限临界见证与尖锐结论

**命题 24.19（来源 $0,115$ 排除所有剩余闭临界候选）。** 任一满足定理24.18必要切点条件的严格右归属七格布局，在闭预算 $\mu$ 下都让两个实际有限来源产生相同箱号对 $(2,2)$，而首标签不同。

证明。第一来源为 $\omega_0=0^\infty\in D$，真实相邻坐标为 $(0,0)$，首标签为 $0$。施加误差 $(\mu,\mu)$，观察成为 $(b,b)$。内切点归右，故箱号对为 $(2,2)$。

第二来源为

$$
\omega_{115}=5\,5\,5\,0^\infty.
$$

低到高位地址为 $001\,001\,001\,000\cdots$；窗内和接缝均无相邻一，故属于 $D$，首标签为 $5$。沿用第14章 $M$ 与组成读出 $q=(2,3)$，有

$$
d_5=(1,1),\qquad M^3d_5=(3,5),\qquad M^6d_5=(13,21),
$$

$$
d_5+M^3d_5+M^6d_5=(17,27),\qquad
q(17,27)=115.
$$

位权同样给 $5+21+89=115$；删除首窗后的尾组成为 $(4,6)$，数量为 $26$。直接对同一有限来源递推，得到真实坐标

$$
\begin{aligned}
x&=t^2(1-g+g^2)=s(1+g^3)=17-27t,\\
y&=t^2(1-g)=s(1-g^2)=4-6t,
\qquad s=t/2.
\end{aligned}
$$

其中 $Hs=t^2$，且 $x-y=t^2g^2>0$。两个坐标均施加误差 $-\mu$。下側严格余量为

$$
(y-\mu)-b=y-2\mu=t^2(3/4-g)>0.
$$

上側严格余量为

$$
\begin{aligned}
(g+\mu)-(x-\mu)
&=g+2\mu-s-sg^3\\
&=t^5/4-t^{10}/2
=\frac{t^5(1-2t^5)}4>0.
\end{aligned}
$$

这里 $0<t^5<t^2<1/2$，所以正号严格。由 $b=\mu,c\ge g+\mu$，

$$
b<y-\mu<x-\mu<g+\mu\le c.
$$

两观察坐标都严格在格 $2$ 内，裁剪不变，也取得 $(2,2)$。两实际有限来源的首标签为 $0,5$，任何确定解码器均失败。$0$ 侧精确使用右归属切点，$115$ 侧保有严格格内余量。$\square$

**定理 24.20（两来源域的严格右归属七格全布局预算）。** 对 $\mathcal E=\Omega$ 和 $\mathcal E=D$，定义 $\mathcal B_{\mathrm c}(\mathcal E)$ 为存在某个严格右归属七格仪器、在全部 $\mathcal E$ 上统一正确的闭预算集合，定义 $\mathcal B_{\mathrm o}(\mathcal E)$ 为对应正开预算集合。则

$$
\boxed{\mathcal B_{\mathrm c}(\Omega)=\mathcal B_{\mathrm c}(D)=[0,\mu),}
$$

$$
\boxed{\mathcal B_{\mathrm o}(\Omega)=\mathcal B_{\mathrm o}(D)=(0,\mu].}
$$

闭预算上确界 $\mu$ 无布局可取得，正开预算最大值 $\mu$ 可由定理24.13的同一固定布局和解码器取得。

证明。定理24.13给 $\Omega$ 上全部 $\nu<\mu$ 的闭正确性与开预算 $\mu$ 的正确性；限制到 $D$ 得全部充分方向。

若某固定仪器在 $D$ 上闭预算 $\mu$ 正确，命题24.14给同一仪器在 $\Omega$ 上开预算 $\mu$ 正确。命题24.17先排除 $B=3$，定理24.18给必要刚性，命题24.19随即以 $D$ 中的实际来源反驳闭预算 $\mu$ 正确性。任何 $\Omega$ 上闭预算 $\mu$ 正确的仪器也会限制成 $D$ 上的此类仪器，因此同样失败。更大闭预算包含闭预算 $\mu$，也不可能；任何开预算 $\nu>\mu$ 同样包含所有绝对误差不超过 $\mu$ 的误差对，故被排除。没有通过稠密性跨越闭等号。$\square$

对定理24.13的固定布局，上述存在性结论加强为该同一仪器的准确合同：闭预算正确恰当且仅当 $0\le\nu<\mu$，正开预算正确恰当且仅当 $0<\nu\le\mu$。必要方向仍由命题24.19的同一有限对给出。

**推论 24.21（统一正裕量的连通格最小值七）。** 在全部 $\Omega$ 上，或在全部最终为 null 且无统一支持上界的 $D$ 上，两次实际坐标使用同一个连通区间量化器并恢复首窗时，具有某个统一正闭预算或某个统一正开预算的最小非空格数都恰为七。此最小值允许任意合法端点归属和单点格。

证明。$\Omega$ 上至多六格已由定理24.12排除。若 $D$ 上某至多六格仪器有闭预算 $\nu>0$，命题24.14使其在 $\Omega$ 上有闭预算 $\nu/2>0$，矛盾。若声称正开预算，先限制成一个更小正闭预算即可。引理24.11在下界中用相对稠密性，故单点格没有被遗漏。定理24.13的严格七格取闭预算 $\mu/2>0$，给两个来源域的上界。$\square$

这项最小值是正模拟误差下的统一观察容量。全 $\Omega$ 的精确零误差连通最小值六由定理16.8给出；实际 $D$ 的一次精确标量与颜色合同见第22章。它们具有不同的精度与取得条件。对已知固定 $D_N$ 或已知有限码本，第23章的距离合同仍适用；$D=\bigcup_ND_N$ 的统一结论不能改写为每个固定有限子集都需要七格。全布局尖锐半径仅针对严格右归属七格，不延伸到左归属、退化七格、非连通纤维或其他观察机制。定理24.18也没有分类剩余切点。七个箱号是七个符号，不能与七个比特或七个量子比特等同。

### 24.9 实际多窗取得、响应边界与数学依据

**推论 24.22（$L+1$ 个实际记录恢复 $L$ 个窗口）。** 固定定理24.13的 $Q,d_7$。对整数 $L\ge1$、任一 $\omega\in\Omega$ 或 $\omega\in D$，实际取得

$$
z_n=\kappa_0(T^n\omega),\qquad
r_n=Q(\operatorname{clip}_X(z_n+\varepsilon_n)),
\qquad 0\le n\le L.
$$

若每个 $|\varepsilon_n|\le\nu<\mu$，或每个 $|\varepsilon_n|<\mu$，则

$$
\bigl(d_7(r_0,r_1),d_7(r_1,r_2),\ldots,d_7(r_{L-1},r_L)\bigr)
$$

恰为 $\omega$ 的前 $L$ 个窗口。

证明。每个 $T^n\omega$ 仍是合法状态零地址；若实际 incoming guard 为一，则其尾是该域中的合法子集，仍受同一闭图合同覆盖。对每个 $0\le n<L$，真实点 $(z_n,z_{n+1})$ 属于该首窗的合法闭图。定理24.13对相邻误差对 $(\varepsilon_n,\varepsilon_{n+1})$ 给出正确标签。共享样本 $z_n$ 只有一个实际取得、一个误差 $\varepsilon_n$ 和一个记录 $r_n$，在左右两个解码对中一致使用；无需为每个相邻对重新选择误差。开预算情形也可对有限列表取共同 $r=\max_n|\varepsilon_n|<\mu$ 后调用闭预算结论。$\square$

这里是 $L+1$ 次实际取得的充分构造，没有推出更强的取得数量下界，也没有从初始箱号自主预测未取得的未来样本。它恢复指定窗口任务，不能替代完整地址、原始有序树或全部未来的重构。

与折叠和边界的关系使用既有第11–14章的条件结果：头—尾联合保留与丢弃一个投影的区别由命题14.2及定理11.2–11.5给出；共享接缝决定共同实现，不能将分别聚合的表任意相乘，见命题14.4；有限未来响应是指定任务的商边界，连续取得更长列表增加所保留的响应，见定理14.11、14.13及命题14.14。上述七格结果是在该实际响应合同上增加噪声和连通纤维条件所得的观察容量，不给出物理时空起源，也不把五个窗口解释为五个内在盲方向。

本章的来源与分支依据为定义14.5、命题14.6、定理14.7及定理17.2；闭网格纯性、六格障碍、平移构造、严格转移、实际距离证书、必要刚性与有限临界见证分别由引理24.11至命题24.19给出。定理24.20和推论24.21、24.22仅在这些明确的来源、误差、纤维、端点和实际取得条件下成立。

## 追加锚（本行以下为增补区）

## 25. 严格七格的端点归属、有限来源闭临界与完成域障碍

### 25.1 共同来源合同与正开预算的归属不变性

沿用定义24.10的实际来源域 $D\subset\Omega$、五标签闭图 $S_\ell$、合法尾域 $I_\ell$、仿射分支 $f_\ell$ 和逐坐标加误差后裁剪的合同。固定

$$
t=\frac{\sqrt5-1}{2},\quad \phi=1+t,\quad g=t^3=2t-1,
\quad H=1+g=2t,\quad \mu=\frac{t^2}{8}=\frac{g}{4H}.
$$

$H$ 始终是仿射误差系数；窗口视界保留记号 $L$，解码器记为 $d_7$，与切点 $d$ 区分。严格七格指

$$
-1<a<b<c<d<e<f<\phi,
$$

每个内部切点独立归相邻左格或右格，格按空间次序编号 $0,\ldots,6$；支持端点 $-1,\phi$ 分别归端格 $0,6$。两个坐标使用同一个量化器和一个固定确定解码器。两坐标必须来自同一实际地址；共同实现依据为定理17.2，实际取得合同见推论24.22。$D$ 是全部最终为 null 的来源，长度没有统一上界。

**引理 25.10（同来源、同解码器的正开归属不变性）。** 固定任意一组严格切点、任意实际来源点 $p\in X^2$ 及正开预算 $r>0$。改变内部切点归属，不改变这个同一来源可取得的箱号对集合。因此对任何指定来源子集和任何固定 $d_7$，正开预算 $r$ 的正确性与内部归属无关。

证明。设归属规则 $B$ 下允许的误差产生裁剪目标 $z$ 和记录 $(i,j)$。裁剪不增加到真实点的距离，故

$$
\|z-p\|_\infty<r.
$$

两种归属共有相同闭格 $J_i,J_j$，且 $z\in J_i\times J_j$。严格格长保证各格内部在闭包中稠密，故可取

$$
w\in\operatorname{int}J_i\times\operatorname{int}J_j,
\qquad \|w-z\|_\infty<r-\|z-p\|_\infty.
$$

仍从原来源 $p$ 出发，直接选择新误差 $w-p$，其最大绝对值严格小于 $r$。$w\in X^2$，裁剪固定它，且所有归属规则在内部一致，故规则 $A$ 也取得 $(i,j)$。交换 $A,B$ 得双向包含。支持端点的目标同样可移入对应端格内部，来源及标签始终没有改变。同一记录集合保证同一 $d_7$ 的正确性等价。这里使用严格误差余量和正格长，不转移闭预算等号，也不涉及单点格。$\square$

### 25.2 所选全左布局的闭临界包含与精确等号

**定理 25.11（有限来源取得闭预算 $\mu$）。** 取定理24.13的六个切点

$$
a=-\frac12+\mu,\quad b=\mu,\quad c=g+\mu,\quad
 d=t+\mu,\quad e=1+\mu,\quad f=2t+\mu,
$$

将全部内部切点归左，即

$$
\begin{aligned}
C_0&=[-1,a],&C_1&=(a,b],&C_2&=(b,c],\\
C_3&=(c,d],&C_4&=(d,e],&C_5&=(e,f],&C_6&=(f,\phi].
\end{aligned}
$$

定理24.13的同一个表解码器 $d_7$ 在全部 $D$ 上对闭预算 $\mu$ 正确，在全部 $\Omega$ 上对正开预算 $\mu$ 及所有较小闭预算正确。

证明。格长的严格正性由定理24.13给出。对任意合法真实点 $(f_\ell(y),y)$ 和闭预算 $\mu$，裁剪后的观察 $(u,v)$ 满足

$$
|u-f_\ell(y)|\le\mu,\qquad |v-y|\le\mu,
\qquad f_\ell(v)-H\mu\le u\le f_\ell(v)+H\mu.
$$

最后一对界由 $v-\mu\le y\le v+\mu$ 和斜率 $-g$ 得到。仿射表达式可用于比较任意 $v$，真实尾 $y$ 仍留在 $I_\ell$。定理24.13的全域端点比较在闭临界给出充分包含

$$
\begin{array}{c|ccccc}
\ell&3&0&5&2&25\\ \hline
u&[-1,b)&(a,c]&(b,d]&(c,f]&(e,\phi].
\end{array}
$$

例如 null 的下端与 $a$ 的差为 $g^2/(2H)>0$，标签 $5,2,25$ 的下端保护量分别为 $g-2\mu,3t^2/4,g-2\mu>0$。上端等号 $u=c,d,f$ 分别仍归当前格 $2,3,5$。标签 $5,25$ 的受限真实尾域另外保证

$$
v\le y+\mu\le t+\mu=d,
$$

故这两标签的未来箱号只能为 $0,1,2,3$，包括 $v=d$ 的等号。

记 $E_\ell^{24}(j)$ 为定理24.13所列的充分包含集合，列 $j$ 表示未来箱号。闭预算 $\mu$ 下的全左布局仍由该表包含，只需作两处增补：

$$
E_0^{\mathrm L}(0)=E_0^{24}(0)\cup\{1\}=\{1,2\},
\qquad E_2^{\mathrm L}(0)=E_2^{24}(0)\cup\{4\}=\{4,5\}.
$$

其余 $E_\ell^{\mathrm L}(j)$ 取 $E_\ell^{24}(j)$。这些是包含集合，不断言整张表的每个项都精确可达；例如标签 $2$、未来格 $4$ 的 $\{3,4\}$ 可以保留为安全的上估计。

逐行证明如下。定理24.13的五个主动等式与四个严格正差均在同一切点下成立。标签 $3$ 在未来箱号至少为 $1$ 时有 $v>a$，从而

$$
u\le f_3(v)+H\mu<f_3(a)+H\mu=a,
$$

当前格为 $0$；未来格 $0$ 使用全域范围。null 在未来格 $0$ 有 $v\le a$，故 $u\ge f_0(a)-H\mu=b$，当前格为 $1$ 或 $2$，其中格 $1$ 必须恰取 $u=b$。未来箱号至少为 $2$ 时 $v>b$，故 $u<f_0(b)+H\mu=b$，当前格为 $1$；未来格 $1$ 使用全域范围。

标签 $5$ 在未来格 $0,1$ 有 $v\le b$，由 $f_5(b)-H\mu>c$ 得 $u>c$，当前格为 $3$；未来格 $2,3$ 使用全域范围，之后的格由受限尾界排除。标签 $25$ 同理使用 $f_{25}(b)-H\mu>f$，在未来格 $0,1$ 取得当前格 $6$，其余仍由全域范围和受限尾界处理。

标签 $2$ 在未来格 $0$ 有 $u\ge f_2(a)-H\mu=e$，当前格为 $4$ 或 $5$，其中格 $4$ 必须恰取 $u=e$。未来格 $1$ 有 $v\le b$，由 $f_2(b)-H\mu>d$ 得当前格 $4,5$。未来格 $2,3$ 满足 $b<v\le d$，两端比较分别给

$$
u<f_2(b)+H\mu=e,\qquad
u\ge f_2(d)-H\mu>d,
$$

所以当前格为 $4$。未来格 $4,5,6$ 仍有 $v>b$，故 $u<e$，与全域 $u>c$ 合并得当前格 $3,4$。至此全部标签、未来格及其空项均已包含。

主动上端等号也是安全的。一般地，在 $v\ge z$ 时，若 $u=f_\ell(z)+H\mu$，则

$$
f_\ell(z)+H\mu=u\le f_\ell(y)+\mu
\le f_\ell(v-\mu)+\mu
\le f_\ell(z-\mu)+\mu=f_\ell(z)+H\mu.
$$

每步都取等，$g>0$ 迫使 $v=z,y=z-\mu$。对 $(\ell,z)=(3,a),(0,b),(2,b)$，相应真实点和观察为

$$
\begin{array}{c|c|c|c}
\ell&\text{真实点}&\text{观察}&\text{左归属记录}\\ \hline
3&(-1/2,-1/2)&(a,a)&(0,0)\\
0&(0,0)&(b,b)&(1,1)\\
2&(1,0)&(e,b)&(4,1).
\end{array}
$$

这些观察坐标都在支持内部，所以取等时原误差必须为 $(\mu,\mu)$；反向施加这对误差确实取得所列安全记录。全域上端 $u=c,d,f$ 的取等则由

$$
u\le f_\ell(y)+\mu\le f_\ell(-1)+\mu
\qquad(\ell=0,5,2)
$$

迫使 $y=-1$ 和当前误差 $+\mu$，其左归属仍为上述当前格 $2,3,5$。受限尾端 $v=d$ 由 $v\le y+\mu\le d$ 迫使 $y=t$、未来误差 $+\mu$，而未来格仍为 $3$。支持端点 $-1,\phi$ 由裁剪及端格处理，不需排除任何支持端点来源。

两项增补共用一个精确的下端等号证明。令 $\Delta\in\{0,1\}$，分别对应标签 $0,2$，其新增记录分别为 $(1,0),(4,0)$。未来格 $0$ 给 $v\le a$，新增当前格给 $u\le b+\Delta$；于是

$$
\begin{aligned}
b+\Delta\ge u
&\ge\Delta-gy-\mu\\
&\ge\Delta-g(v+\mu)-\mu\\
&\ge\Delta-g(a+\mu)-\mu=b+\Delta.
\end{aligned}
$$

全部取等，因而

$$
v=a,\qquad y=y_*:=a+\mu
=-\frac12+2\mu=-\frac{1+t}{4}=-\frac\phi4,
$$

$$
f_\ell(y_*)=\Delta+\frac{g\phi}{4}=\Delta+2\mu,
\qquad u=b+\Delta.
$$

这里 $2\mu=t^2/4=(1-t)/4$、$g\phi=t^2$ 给出两个数值等式。$a,b,e$ 都严格在支持内部，故裁剪不能隐藏另一误差实现，原误差恰为 $(-\mu,-\mu)$。反过来，$y_*\in(-1,0)$ 对两标签均合法；定理17.2给实际共同实现，施加该误差恰得 $(b,a)$ 或 $(e,a)$。因此两项新增记录的数值尾和误差均已唯一确定。只有 null 的 $(1,0)$ 与标签 $3$ 跨标签重叠；标签 $2$ 的 $(4,0)$ 本身没有冲突。

对每个有限尾，编码是有限和

$$
\sum_{n=0}^{N-1}(-g)^n\Delta_{\ell_n}\in
\mathbb Z[t]=\{m+nt:m,n\in\mathbb Z\}.
$$

这是因为 $g$ 和五个平移量都属于该环，且 $t^2=1-t$ 保持整数系数。删除窗口仍得到有限尾，接缝合法性只限制可选项，不破坏环包含。另一方面，若 $y_*=m+nt$，则

$$
(4m+1)+(4n+1)t=0.
$$

$t$ 无理迫使 $4m+1=4n+1=0$，与整数性矛盾。因此 $y_*\notin\mathbb Z[t]$，这个数值不可能是任何 $D$ 来源的实际尾；不需要也不声称环包含的逆命题。

删去这两个在 $D$ 上不可能的新增项，恰恢复定理24.13的充分表，其各列不同标签集合两两不交。因此直接复用该表的 $d_7$，包括未列格对统一补为 $0$ 的约定，即得全部 $D$ 的闭预算 $\mu$ 正确性。对 $\Omega$ 的正开预算 $\mu$，两新增项所强迫的误差 $(-\mu,-\mu)$ 已不允许，也恢复同一表；每个较小闭预算是该开预算的子集。引理25.10也使此开预算合同与定理24.13的右归属合同一致。解码器不依赖来源、来源长度或误差值。

仪器仍要求精确比较观察与切点、准确记录箱号；有限来源的代数排除是在证明中使用的必要条件，不是解码器接收的额外尾值。这里没有把精确箱号访问改成只给任意精度近似的实数访问。$\square$

### 25.3 任意归属的实际闭临界碰撞与固定布局的大预算有限见证

**命题 25.12（完成域闭临界不可取得）。** 任意严格七格切点、任意内部左右归属及任意固定确定解码器，都不能在全部 $\Omega$ 上取得闭预算 $\mu$。此外，定理25.11的所选全左布局在全部 $D$ 上对每个 $r>\mu$ 的正开预算和闭预算均失败，见证可固定为实际有限来源 $0,115$。

证明。反设某任意归属仪器在 $\Omega$ 上闭预算 $\mu$ 正确。先弱化为正开预算 $\mu$，再由引理25.10把这个开合同转到同切点的全右归属，保持同一解码器。定理24.18于是给原切点的必要条件

$$
a=-\frac12+\mu,\qquad b=\mu,\qquad c\ge g+\mu.
$$

这一步没有转移闭预算等号。现在回到原归属，逐项构造实际碰撞。

若 $b$ 归右，有限来源 $0^\infty$ 的真实点为 $(0,0)$，误差 $(\mu,\mu)$ 给观察 $(b,b)$，记录 $(2,2)$。命题24.19的合法有限来源 $5^3 0^\infty$，低到高位为 $001\,001\,001\,000\cdots$，数量为 $115$，其同来源真实相邻点为

$$
x=t^2(1-g+g^2)=17-27t,\qquad
y=t^2(1-g)=4-6t,\qquad x-y=t^2g^2>0.
$$

该命题的严格余量给

$$
y-2\mu=t^2(3/4-g)>0,\qquad
g+2\mu-x=\frac{t^5(1-2t^5)}4>0.
$$

故误差 $(-\mu,-\mu)$ 后

$$
b<y-\mu<x-\mu<g+\mu\le c.
$$

两个观察都在格 $2$ 内，也取得 $(2,2)$。两个来源的首标签为 $0,5$，且均有限；其他切点归属不影响此碰撞，裁剪固定全部目标。

若 $b$ 归左、$a$ 归右，合法地址 $3^\infty$ 的同来源固定点为 $(-1/2,-1/2)$。施加 $(\mu,\mu)$ 后得到 $(a,a)$，记录 $(1,1)$。有限零来源以零误差也取得 $(1,1)$，因为 $a<0<b$。两标签为 $3,0$，目标在支持内部，裁剪不变。$3^\infty$ 是 $\Omega$ 来源，不将它称为有限来源。

若 $a,b$ 均归左，取定理25.11确定的合法 null 点 $(2\mu,y_*)$。定理17.2保证其实际共同实现；误差 $(-\mu,-\mu)$ 给 $(b,a)$，记录 $(1,0)$。另一标签 $3$ 的合法端点为

$$
(f_3(-1),-1)=(-t^2,-1).
$$

其当前坐标严格在格 $1$ 内，因为

$$
-t^2-a=\frac g2-\mu>0,\qquad -t^2<0<b,
$$

而尾 $-1$ 在端格 $0$。零误差也取得 $(1,0)$，与 null 碰撞。所有目标都在支持内，裁剪固定；$y_*$ 的有限尾排除不影响 $\Omega$ 的实际实现。这一支也给出所选全左布局自身的闭临界碰撞。

三支穷尽 $a,b$ 的归属，不限制 $c,d,e,f$ 的归属；各支均在原仪器下产生相同箱号对和不同实际首标签，故任意确定解码器失败。

最后固定定理25.11的全左切点，此时 $c=b+g$。上面的同一来源 $115$ 及误差 $(-\mu,-\mu)$ 已使两观察严格在 $(b,c)$ 内。对任意 $r>\mu$，选择

$$
0<\epsilon<\min\{r-\mu,g\}.
$$

有限零来源用误差 $(\mu+\epsilon,\mu+\epsilon)$，观察为 $(b+\epsilon,b+\epsilon)\in(b,c)^2$，也取得 $(2,2)$。两来源的误差范数均严格小于 $r$，目标在支持内，因此同一有限对同时排除该固定布局的正开预算 $r$ 和闭预算 $r$。$\square$

### 25.4 允许任意归属的存在预算与有限像边界

**定理 25.13（严格七格的准确存在预算）。** 令 $\mathcal B_{\mathrm c}^{\mathrm{arb}}(\mathcal E)$ 和 $\mathcal B_{\mathrm o}^{\mathrm{arb}}(\mathcal E)$ 分别表示：存在某个严格七格切点、某种内部左右归属及一个固定确定解码器，对全部来源域 $\mathcal E$ 正确的闭预算和正开预算集合。则

| 25.13 来源域 | 闭预算存在集合 | 正开预算存在集合 |
| --- | --- | --- |
| 完成地址域 $\Omega$ | $[0,\mu)$ | $(0,\mu]$ |
| 全部实际有限来源 $D$ | $[0,\mu]$ | $(0,\mu]$ |

证明。定理25.11的一个全左布局和同一 $d_7$ 同时提供表中所有存在方向，特别是 $D$ 的闭临界端点。命题25.12排除任意归属的 $\Omega$ 闭预算 $\mu$；更大闭预算及任何正开预算 $r>\mu$ 均包含全部闭预算 $\mu$ 的误差对，也被排除。

若某仪器在 $D$ 上闭预算 $r>\mu$ 正确，命题24.14的保标签严格余量桥给同一仪器在 $\Omega$ 上正开预算 $r$ 正确，与刚才的排除矛盾。该命题还使两个来源域在同一仪器、同一正开预算下的正确性等价，故 $D$ 的正开预算也不能超过 $\mu$。严格转移没有给 $D$ 闭临界推出 $\Omega$ 闭临界；前者的存在性仅由定理25.11的全左构造承担。$\square$

存在量词允许选择仪器，不要求每一种混合归属都成功；定理24.18的必要切点也不成为充分分类。限定为全右归属时，定理24.20对 $D$ 的闭临界排除仍保持其原假设。上述预算范围针对严格非退化七格，不扩展至单点格、非连通纤维或固定有限码本；正裕量最小七格的更广合同沿用推论24.21。

此处新结论是同标签有限来源像与其完成闭图的端点区别：命题24.14保证有限像稠密，定理25.11却以整数环排除唯一有害等号尾，而命题25.12在完成域实现该尾。没有推出有限像到该尾的统一正间隔，也没有由这些观察合同推出物理时间或空间的起源。

## 追加锚（本行以下为增补区）

## 26. 三次实际观察的六格正裕量与连续视界最小值

### 26.1 同一来源的延迟首窗合同

沿用定义14.5、定义24.10的 $\Omega,D,T=\sigma^3,\kappa_s$，以及

$$
t=\frac{\sqrt5-1}{2},\quad \phi=1+t,\quad g=t^3=2t-1,
\qquad X=[-1,\phi],\quad I=[-1,t].
$$

标签为 $\Lambda=\{3,0,5,2,25\}$，其中 $0=\mathrm{null}$。对一条实际合法地址 $\omega$，记 $x_m=\kappa_0(T^m\omega)$。每个实际相邻对满足 $x_m=f_{\ell_m}(x_{m+1})$，其中

$$
\begin{aligned}
f_3(y)&=-t-gy,& f_0(y)&=-gy,& f_5(y)&=t^2-gy,\\
f_2(y)&=1-gy,& f_{25}(y)&=2-t-gy.&&
\end{aligned}
$$

标签 $3,0,2$ 的合法尾域为 $X$，标签 $5,25$ 的合法尾域为 $I$；按标签 $3,0,5,2,25$ 排列的当前像依次为

$$
[-1,-t^2],\quad[-t^2,g],\quad[g,t],\quad[t,2t],\quad[2t,\phi].
$$

这些是定理17.2的实际闭分支，包含支持端点与分支接触点。incoming guard 为一时只允许 $3,0,5$，对应地址是上述状态零域的合法子集；两种状态的编码使用同一个级数。

固定整数 $h\ge0$、一个各纤维均为非空连通区间的固定量化器 $Q:X\to\{0,\ldots,q-1\}$ 和一个全定义确定解码器。实际连续取得 $x_0,\ldots,x_h$，记录

$$
v_m=\operatorname{clip}_X(x_m+\varepsilon_m),\qquad
R_m=Q(v_m),\qquad |\varepsilon_m|\le\nu.
$$

闭预算 $\nu$ 的正确性要求对域内每条地址及所有分别任意选择的允许误差，解码 $(R_0,\ldots,R_h)$ 得其首窗。这里没有误差的概率或独立性假设；记录箱号本身准确，全部样本来自同一实际地址。裁剪给出 $|v_m-x_m|\le\nu$。视界 $h$ 指 $h+1$ 次实际取得，不是由标量递推生成的记录。

### 26.2 一个固定六格三样本仪器

**定理 26.10（有理六格、全定义解码器与闭预算）。** 取五个切点

$$
a=-\frac25,\quad b=\frac15,\quad c=\frac{11}{20},\quad
d=\frac{11}{10},\quad e=\frac75
$$

及六格

$$
\begin{aligned}
C_0&=[-1,a),& C_1&=[a,b),& C_2&=[b,c),\\
C_3&=[c,d),& C_4&=[d,e),& C_5&=[e,\phi].
\end{aligned}
$$

令 $Q_6$ 为此量化器、$\nu_*=1/1000$。下表定义一个全域固定解码器 $\mathcal D_6:\{0,\ldots,5\}^3\to\Lambda$，输入为 $(i,j,k)$；$d$ 只表示切点。

| 26.10 当前箱号 $i$ | 其余箱号条件 | $\mathcal D_6(i,j,k)$ |
| --- | --- | --- |
| 三样本当前 $0$ | 任意 $j,k$ | $3$ |
| 三样本当前 $1$ | $j\ge1$，任意 $k$ | $0$ |
| 三样本当前 $1$ | $j=0,\ k\ge4$ | $3$ |
| 三样本当前 $1$ | $j=0,\ k\le3$ | $0$ |
| 三样本当前 $2$ | $j\ge1$，任意 $k$ | $5$ |
| 三样本当前 $2$ | $j=0,\ k\ge3$ | $0$ |
| 三样本当前 $2$ | $j=0,\ k\le2$ | $5$ |
| 三样本当前 $3$ | $j\ge1$，任意 $k$ | $2$ |
| 三样本当前 $3$ | $j=0,\ k\ge2$ | $5$ |
| 三样本当前 $3$ | $j=0,\ k\le1$ | $2$ |
| 三样本当前 $4$ | $j=0$，任意 $k$ | $2$ |
| 三样本当前 $4$ | $j\ge1$，任意 $k$ | $25$ |
| 三样本当前 $5$ | 任意 $j,k$ | $25$ |

对全部 $\Omega$ 及其子域 $D$，此仪器从三个实际连续记录统一恢复首窗，允许闭预算 $|\varepsilon_0|,|\varepsilon_1|,|\varepsilon_2|\le\nu_*$。

证明。复用第24.1节的严格有理界 $8/13<t<5/8$、$3/13<g<1/4$，得到 $-1<a<b<c<d<e<\phi$，六格均非空。以下均取 $\nu=\nu_*$。先用当前像排除不可能的首标签：

| 26.10 观察当前格 | 可能的真实首标签 |
| --- | --- |
| 三样本范围 $C_0$ | $3$ |
| 三样本范围 $C_1$ | $3,0$ |
| 三样本范围 $C_2$ | $0,5$ |
| 三样本范围 $C_3$ | $5,2$ |
| 三样本范围 $C_4$ | $2,25$ |
| 三样本范围 $C_5$ | $25$ |

所需端点比较为

$$
\begin{gathered}
a+\nu<-t^2,\quad b+\nu<g,\quad b-\nu>-t^2,\\
c+\nu<t,\quad c-\nu>g,\quad d+\nu<2t,\\
d-\nu>t,\quad e-\nu>2t.
\end{gathered}
$$

例如 $a+\nu=-399/1000<t-1=-t^2$，因为 $t>8/13$；其余由同一有理界直接得到。每个观察格只需用其闭包和 $|v_0-x_0|\le\nu$，所以内部切点等号没有被排除；$5,25$ 始终使用受限尾域 $I$ 所给的当前像。

记

$$
r=\frac1g=3+2t<\frac{17}{4},\qquad
F(y)=\frac{-t-y}{g}=-(2+t)-ry.
$$

四个可能混淆的当前格所需逆分支端点为

$$
\begin{aligned}
A&=F(a)=-\frac{4+t}{5},&
B&=-rb=-\frac{3+2t}{5},\\
C&=r(t^2-c)=-\frac{13+2t}{20},&
D&=r(1-d)=-\frac{3+2t}{10},\\
E&=r(2-t-e)=\frac{t-1}{5}.&&
\end{aligned}
$$

其中 $a-A,a-B,a-C,E-a>3/10$，而 $a-D=g/10>1/50$。此外

$$
(r+1)\nu<\frac{21}{4000}<\frac1{50}.
$$

由当前格的下端和 $|v_0-x_0|\le\nu$，首标签 $3$ 在格 $1$、首标签 $0$ 在格 $2$、首标签 $5$ 在格 $3$、首标签 $2$ 在格 $4$ 时，真实 $x_1$ 分别至多为 $A+r\nu,B+r\nu,C+r\nu,D+r\nu$。再计入第二次观察的误差 $\nu$，上述严格端点差均迫使 $v_1<a$，即 $j=0$。首标签 $25$ 在格 $4$ 时，则由当前格的上端得 $x_1\ge E-r\nu$，故 $v_1>a$，即 $j\ge1$。这证明格 $4$ 的两行，并证明格 $1,2,3$ 在 $j\ge1$ 时的三行。

剩余情形为 $i\in\{1,2,3\},j=0$。此时

$$
x_1\le a+\nu<-t^2.
$$

实际地址 $T\omega$ 的当前坐标严格低于其他四分支的当前像，所以其真实首标签必为 $3$；guard 一也允许该标签。因此同一来源的实际第三坐标恰为 $x_2=F(x_1)$。这里使用第二次误差来确定真实分支，没有把两条分别可实现的边拼接，也没有从 $x_1$ 自主取得 $x_2$。

再记

$$
\begin{aligned}
U_A&=F(A)=\frac{4\phi}{5},&
U_B&=F(B)=\frac{3\phi}{5},\\
U_C&=F(C)=\frac{3+8t}{20},&
U_D&=F(D)=-\frac{7+2t}{10},
\end{aligned}
\qquad \eta=(r^2+1)\nu.
$$

从当前观察误差到第一次逆分支，误差界为 $r\nu$；再对真实关系 $x_2=F(x_1)$ 使用斜率 $-r$，误差界为 $r^2\nu$；第三次观察增加 $\nu$。第二次观察的误差只用于上述分支推断，不另加一个传播逆误差项。所有六个剩余真实标签分支由下表覆盖：

| 26.10 当前格与真实首标签，且 $j=0$ | 真实 $x_1$ 的端点界 | 实际观察 $v_2$ 的界 |
| --- | --- | --- |
| 三样本第三支 $i=1,\ell=3$ | $x_1\le A+r\nu$ | $v_2\ge U_A-\eta$ |
| 三样本第三支 $i=1,\ell=0$ | $x_1\ge B-r\nu$ | $v_2\le U_B+\eta$ |
| 三样本第三支 $i=2,\ell=0$ | $x_1\le B+r\nu$ | $v_2\ge U_B-\eta$ |
| 三样本第三支 $i=2,\ell=5$ | $x_1\ge C-r\nu$ | $v_2\le U_C+\eta$ |
| 三样本第三支 $i=3,\ell=5$ | $x_1\le C+r\nu$ | $v_2\ge U_C-\eta$ |
| 三样本第三支 $i=3,\ell=2$ | $x_1\ge D-r\nu$ | $v_2\le U_D+\eta$ |

例如 $i=1,\ell=0$ 给 $x_0=-gx_1\le b+\nu$，故 $x_1\ge B-r\nu$；递减的 $F$ 给 $x_2\le U_B+r^2\nu$，再由 $v_2\le x_2+\nu$ 得表中第二行。其余各行同样分别使用当前格的下端或上端，并两次反向不等号。

六个严格分离量满足

$$
U_A-d,\quad d-U_B,\quad U_B-c,\quad c-U_C,
\quad U_C-b,\quad b-U_D>\frac1{10}.
$$

例如 $d-U_B=(5-6t)/10>1/8$、$c-U_C=2(1-t)/5>3/20$；其他四个量分别为 $(8t-3)/10,(1+12t)/20,(8t-1)/20,(9+2t)/10$，均由第24.1节的界严格大于 $1/10$。而

$$
\eta<\frac{305}{16000}<\frac1{10}.
$$

于是格 $1$ 的两标签观察 $v_2$ 严格分居 $d$ 两侧，格 $2$ 的两标签严格分居 $c$ 两侧，格 $3$ 的两标签严格分居 $b$ 两侧，对应阈值恰为 $k=4,3,2$。这给出最后六行。13 行互不交叠且覆盖全部输入三元组；未发生的三元组也已确定赋值。所有排除与分离均来自真实分支和同一地址关系，不要求所有表项都可达。

整个证明对闭预算端点同样成立。真实支持端点 $-1,\phi$ 和合法受限尾域端点均由闭分支包含，裁剪只降低坐标误差；内部切点按所列右归属取箱号，格闭包估计和严格决策差覆盖其全部等号情形。证毕。$\square$

### 26.3 任意延迟的共同尾下界与有限来源转移

**定理 26.11（全未来不消除五格连通障碍）。** 在 $\Omega$ 上，至多五个非空连通区间格不能统一恢复首窗，即使当前颜色准确且从时间一开始的整个精确未来 $(x_1,x_2,\ldots)$ 全部可用。因此任意固定有限视界的正噪声合同至少需要六格。此下界允许任意端点归属和单点格。

证明。直接复用定理16.8的六点共同尾见证，而明确保留其完整未来。令 $L=(3,25)^\infty$，它从 guard 一合法且坐标为 $-1$；$5L$ 也从 guard 一合法且坐标为 $t$。六个严格递增点为

$$
\begin{aligned}
u_1&=2t-2=f_3(t),& u_2&=3t-2=f_0(t),\\
u_3&=g=f_5(t)=f_0(-1),& u_4&=t=f_5(-1),\\
u_5&=2t=f_2(-1),& u_6&=\phi=f_{25}(-1).
\end{aligned}
$$

三个来源 $3(5L),0(5L),5(5L)$ 合法，且对每个 $m\ge1$ 都有

$$
T^m\bigl(\ell(5L)\bigr)=T^{m-1}(5L),\qquad \ell\in\{3,0,5\}.
$$

所以它们完整未来的实际地址和精确坐标完全相同，不同首窗迫使 $Q(u_1),Q(u_2),Q(u_3)$ 两两不同。同样，四个合法来源 $0L,5L,2L,25L$ 对每个 $m\ge1$ 都有 $T^m(\ell L)=T^{m-1}L$，迫使 $Q(u_3),Q(u_4),Q(u_5),Q(u_6)$ 两两不同。六点中每对相邻点颜色不同；若一个连通格含 $u_i,u_k$ 且 $k>i+1$，也必含 $u_{i+1}$，仍矛盾。因此六点属于六个不同格。

任意有限含噪合同必须包含零误差记录；共同尾的精确未来又决定所有未来颜色，故上述碰撞排除所有至多五格的此类合同。这里的完整精确未来从时间一开始，当前观察仍为颜色；没有把当前精确实数也作为输入。$\square$

**命题 26.12（固定有限视界的精确观察目标转移）。** 固定有限 $h\ge0$、同一 $Q$ 和同一解码器。若该仪器在全部 $D$ 上对闭预算 $\nu>0$ 正确，则它在全部 $\Omega$ 上对闭预算 $\nu/2$ 正确。因此 $D$ 上任意固定有限视界的正裕量合同至少需要六格，且两样本的正裕量合同至少需要七格。

证明。对一条 $\omega\in\Omega$，选一个整数 $N>h$ 满足

$$
\phi g^{N-h}<\nu/2.
$$

保留其前 $N$ 个窗口、后接 $0^\infty$，得到一条实际地址 $\omega^{(N)}\in D$。置零不会制造相邻一，截断接缝合法，首标签保持不变。记 $x_m^{(N)}=\kappa_0(T^m\omega^{(N)})$。窗口级数对同一个截断来源给出

$$
x_m-x_m^{(N)}=(-g)^{N-m}\kappa_0(T^N\omega),\qquad
|x_m-x_m^{(N)}|\le\phi g^{N-h}<\nu/2,
\quad 0\le m\le h.
$$

任给原来源的误差 $|\varepsilon_m|\le\nu/2$，令裁剪前目标为 $s_m=x_m+\varepsilon_m$，并对截断来源选择

$$
\varepsilon_m^{(N)}=s_m-x_m^{(N)}.
$$

则每个 $|\varepsilon_m^{(N)}|<\nu$，且 $x_m^{(N)}+\varepsilon_m^{(N)}=s_m$ 精确成立。裁剪前目标逐坐标完全相同，因而裁剪值和全部记录箱号完全相同，包括任何切点等号。$D$ 上正确性使原来源记录返回所保留的首标签，得到 $\Omega$ 上闭预算 $\nu/2$ 正确性。这是命题24.14的严格余量方法在一个固定有限列表上的应用；不是分别选择 $h+1$ 条有限来源。

若 $q\le5$，与定理26.11矛盾；当 $h=1,q\le6$ 时，与定理24.12矛盾。正开预算先限制成任意更小的正闭预算即可。转移使用有限 $h$ 和正的剩余余量，不推出 $D$ 的零误差六格下界，也不推出 $D$ 的无限记录下界或无限列表的一致近似。$\square$

### 26.4 连续视界最小值、滑动取得与响应边界

**推论 26.13（共同闭预算下的准确格数与六格取得数）。** 对来源域 $\mathcal E=\Omega$ 或 $D$，在闭预算 $\nu_*=1/1000$、同一连通区间量化器和实际初始连续取得的首窗任务中：两样本的最小格数为七，每个固定 $h+1\ge3$ 样本视界的最小格数为六。允许选择任意正统一预算和任意固定有限视界时，最小格数也为六；使用六格时，实际连续取得的最小样本数为三。

证明。两样本下界由定理24.12及命题26.12给出；第24.1节的 $t<5/8$ 给

$$
\mu=\frac{1-t}{8}>\frac3{64}>\frac1{1000}.
$$

故定理24.13的七格仪器在同一闭预算 $\nu_*$ 正确，上下界相合。三样本六格上界由定理26.10给出。每个固定 $h\ge2$ 可定义解码器只取前三个记录而忽略其余记录；所有未来样本仍按合同实际取得。下界由定理26.11及命题26.12给出，所以每个此类有限视界恰需六格。

六格不能用两样本取得正裕量；若一个仅用当前记录的六格仪器成功，将其解码器用于相邻对并忽略第二记录便得到被排除的两样本仪器。因此三次是六格在此连续取得合同中的最小值。全 $\Omega$ 的完整精确未来下界和 $D$ 的正噪声固定有限视界下界保持各自范围。定理16.8仍是精确相邻任务的六格结论；命题16.11仅排除其中两个指定布局的正余量，不排除定理26.10的布局。第24章的最小七格结论仍只作用于两样本合同。$\square$

**推论 26.14（一致滑动三元组恢复多窗）。** 固定 $Q_6,\mathcal D_6$。对整数 $L\ge1$ 和一条 $\omega\in\Omega$ 或 $D$，实际取得 $L+2$ 个连续坐标，记录

$$
R_n=Q_6\!\left(\operatorname{clip}_X\bigl(\kappa_0(T^n\omega)+\varepsilon_n\bigr)\right),
\qquad 0\le n\le L+1,\quad |\varepsilon_n|\le\nu_*.
$$

则 $\mathcal D_6(R_n,R_{n+1},R_{n+2})=\sigma_n(\omega)$ 对全部 $0\le n<L$ 成立。

证明。每个 $T^n\omega$ 仍是合法状态零地址；实际 guard 一只限制其合法子集，定理26.10仍适用。对该同一地址的三个连续坐标应用定理26.10即得第 $n$ 窗。共享样本只有一次实际取得、一个误差 $\varepsilon_n$ 和一个颜色 $R_n$，在全部重叠三元组中一致使用；没有按窗口重新选择误差或重新取得共享样本。$\square$

在共同预算下，每样本字母表从七个值减为六个值，首窗解码增加一次实际取得；恢复 $L$ 窗时，第24章的充分构造用 $L+1$ 个七值记录，本章用 $L+2$ 个六值记录。字母表缩小与取得数量增加是不同资源坐标，此比较不推出总存储、总装置成本或取得机制的全局最优值；六个符号也不是六个比特。$\nu_*$ 是明确的充分闭预算，本章没有优化六格噪声半径，也没有建立稀疏或自适应取得的最小值。

所用实际分支与共同实现来自定义14.5、命题14.6及定理17.2，任意延迟的连通下界复用定理16.8的同尾六点链，两样本正裕量障碍与七格上界复用定理24.12、24.13，有限视界的转移使用命题24.14的严格余量方法。本章的新增证明为固定有理布局的三样本包含与误差界，以及这些前置在所述连续视界和滑动合同下的结论。

与第14章的响应边界相接，增加一次同一来源的实际时间观察，能在这个指定任务和共同误差预算下减少一个连通空间量化格。这是地址折叠、共同接缝、未来响应与观察分辨率之间的明确模型关系；全部三元组仍由实际来源承担，未取得的坐标没有被推断取得。它不提供自主颜色演化、有限记录的完整无限地址恢复，也不建立物理时间或空间的起源。

## 追加锚（本行以下为增补区）

## 27. 实际未来的六格噪声上界、有限临界排除与严格余量边界

沿用定义14.5和第26.1节的实际地址域 $\Omega$、最终为 null 的子域 $D$、三位删除 $T$、首窗标签 $\Lambda=\{3,0,5,2,25\}$ 及 $t,\phi,X,I$。置 $g=t^3=2t-1$，本章局部噪声记号为

$$
\lambda_{\mathrm{noise}}=\frac{t^2}{10},\qquad
\lambda:=\lambda_{\mathrm{noise}}.
$$

这里的 $\lambda$ 只表示噪声半径，不是前文的概率测度或其他局部参数。第24–25章的噪声半径 $\mu=t^2/8$ 满足 $\lambda=4\mu/5$。

固定一个各格均为非空连通区间的量化器 $Q:X\to\mathcal C$，其中颜色字母表 $\mathcal C$ 有限。同一 $Q$ 用于同一合法地址的每个连续实际坐标

$$
x_j(\omega)=\kappa_0(T^j\omega),\qquad
R_j=Q\!\left(\operatorname{clip}_X(x_j(\omega)+\varepsilon_j)\right).
$$

误差在裁剪前分别任意选择；闭预算 $\nu$ 指每个 $|\varepsilon_j|\le\nu$，正开预算指每个 $|\varepsilon_j|<\nu$。一个固定确定解码器只接收实际取得的颜色记录并恢复 $\sigma_0(\omega)$。有限视界 $h\ge0$ 接收 $R_0,\ldots,R_h$；整个无限记录合同接收 $(R_j)_{j\ge0}$。允许任意合法端点归属和单点格。

**定理 27.1（六格的有限视界严格上界与完成域全未来上界）。** 若 $Q$ 至多有六格，且上述仪器在正预算 $\nu$ 下对指定来源域统一正确，则：

- 对每个固定有限 $h\ge0$，来源域为 $\Omega$ 或 $D$ 时，闭预算和正开预算均必须满足 $\nu<\lambda$。
- 对整个无限记录，来源域为 $\Omega$ 时，闭预算必须满足 $\nu<\lambda$，正开预算必须满足 $\nu\le\lambda$。

证明。定理26.11的实际共同尾六点障碍排除 $\Omega$ 上的至多五格，连完整精确未来也不能消除该障碍。有限视界的 $D$ 合同由引理27.2转到同一仪器的 $\Omega$ 正开合同，再限制为一个正闭子预算，也排除至多五格。因此只需处理六格。引理27.3给出 $\nu\le\lambda$ 及等号时的唯一切点布局。命题27.4排除 $\Omega$ 的闭等号，且保留整个实际共同未来。每个固定有限视界下，$\Omega$ 的开等号直接强制该布局；$D$ 的闭或开等号由引理27.2先转到 $\Omega$ 的开等号，也强制同一布局。命题27.6在此布局内给出两条实际 $D$ 来源的严格误差碰撞，因而同时排除两个域的有限视界开、闭等号。各证明如下。$\square$

### 27.1 同标签有限向量转移与实际共同尾

**引理 27.2（同一仪器的有限向量严格余量转移）。** 固定有限 $h\ge0$、同一 $Q$、同一解码器及 $r>0$。若它们在 $D$ 上对闭预算 $r$ 正确，则在 $\Omega$ 上对正开预算 $r$ 正确；$D$ 与 $\Omega$ 上的正开预算 $r$ 正确性等价。

证明。使用命题26.12的同来源、保首标签截断，但保留所需的整个有限目标向量。固定 $\omega\in\Omega$ 及一组 $|\varepsilon_j|<r$，令

$$
z_j=\operatorname{clip}_X(x_j(\omega)+\varepsilon_j),\qquad
s=\max_{0\le j\le h}|z_j-x_j(\omega)|<r.
$$

裁剪不增加到 $x_j(\omega)\in X$ 的距离。保留 $\omega$ 的前 $N>h$ 个窗口、后接 $0^\infty$，得到一条合法 $\omega^{(N)}\in D$，首标签相同。窗口级数给出

$$
|x_j(\omega)-x_j(\omega^{(N)})|
\le\phi g^{N-h}\longrightarrow0,\qquad 0\le j\le h.
$$

选 $N$ 使此界严格小于 $r-s$，再对这同一条有限来源取误差

$$
\varepsilon_j^{(N)}=z_j-x_j(\omega^{(N)}).
$$

全部误差严格小于 $r$，全部裁剪后目标逐坐标恰为原来的 $z_j\in X$。所以同一个 $Q$ 给出完全相同的有限颜色向量，包括任何切点等号；同一解码器返回所保留的同一首标签。这个论证可从 $D$ 的闭或开合同出发；反向开合同由限制到 $D$ 得到。没有为不同坐标另选来源，也不要求 $Q$ 连续。有限最大值和正余量是转移的条件，不给出无限向量的同样转移。$\square$

**引理 27.3（四组共同尾、五切点的上界与临界刚性）。** 六格仪器在 $\Omega$ 上对正闭预算 $\nu$ 正确，无论使用固定有限视界还是整个无限记录，都必须满足 $\nu\le\lambda$。正开预算同样必须满足此弱上界。在闭或正开临界预算 $\lambda$ 下，六格按从左到右编号，其切点只能是

$$
\begin{aligned}
a&=-t^2-\lambda,& b&=g-3\lambda,& c&=t-5\lambda,\\
d&=2t-7\lambda,& e&=2t+\lambda.&&
\end{aligned}
$$

此时 $-1<a<b<c<d<e<\phi$，所以单点格与重合切点均被排除。

证明。五个实际分支为

$$
\begin{aligned}
f_3(y)&=-t-gy,&f_0(y)&=-gy,&f_5(y)&=t^2-gy,\\
f_2(y)&=1-gy,&f_{25}(y)&=2-t-gy.&&
\end{aligned}
$$

$3,0,2$ 可前接 $A_0$ 的尾，$5,25$ 可前接 $A_1$ 的尾；定理17.2给出 $\kappa_0(A_0)=X$、$\kappa_1(A_1)=I$，在 $A_1\subset A_0$ 上两个级数相同。每次共同尾比较都先取一条实际合法尾 $\eta$，再前接两个合法且不同的标签 $\ell,m$。两条来源 $\ell\eta,m\eta$ 的当前值为 $f_\ell(y),f_m(y)$，而对全部 $j\ge1$，

$$
T^j(\ell\eta)=T^j(m\eta)=T^{j-1}\eta.
$$

若当前允许颜色集合相交，选择该共同颜色，并在以后全部取相同的零误差，便得到整个记录相同而首标签不同的实际碰撞。因此其当前允许颜色集合必须不交。有限视界也受此必要条件约束。

先保留所有退化可能，将格闭包写为

$$
J_0=[-1,a],\ J_1=[a,b],\ J_2=[b,c],\
J_3=[c,d],\ J_4=[d,e],\ J_5=[e,\phi],
\qquad a\le b\le c\le d\le e.
$$

不在这里选择端点归属。复用定理16.8、26.11的实际尾 $L=(3,25)^\infty$、$U=5L$；二者在 guard 一合法，坐标为 $-1,t$。六个严格递增见证为

$$
p_1=2t-2,\quad p_2=3t-2=-t^4,\quad
p_3=g,\quad p_4=t,\quad p_5=2t,\quad p_6=\phi.
$$

实际共同尾组 $3U,0U,5U$ 强制前三点颜色两两不同，组 $0L,5L,2L,25L$ 强制后四点颜色两两不同。每对相邻点颜色不同；连通格若含两个非相邻点，也含它们之间的相邻点，仍矛盾。故 $Q(p_i)=i-1$。

再取实际尾 $R=(25,3)^\infty$，坐标 $\phi$。共同尾来源 $3R,0R$ 的当前值为 $-1,-t^2$，颜色不同；$-t^2$ 严格位于 $p_1,p_2$ 之间，故其颜色为 $1$。另一个共同尾对 $2U,25U$ 的当前值为

$$
v:=1-t^4=3t-1=t+g,\qquad 2t.
$$

$v$ 位于 $t,2t$ 之间且不能取颜色 $4$，故其颜色为 $3$。于是得到只用弱不等式的切点约束

$$
p_1\le a\le-t^2,\quad -t^4\le b\le g,\quad
g\le c\le t,\quad v\le d\le2t,\quad 2t\le e\le\phi.
\tag{27.1}
$$

对当前值为 $u,u+\Delta$ 的实际共同尾对，闭预算正确性先要求 $2\nu<\Delta$；否则位于 $X$ 内的共同中点已给碰撞。在 $2\nu<\Delta$ 时，两个允许目标 $u+\nu,u+\Delta-\nu$ 严格位于两真实值之间，故在 $X$ 内，裁剪固定。其颜色必须不同，所以至少一个切点位于

$$
[u+\nu,u+\Delta-\nu].
\tag{27.2}
$$

这是必要的弱切点条件，没有把闭包接触误当同色碰撞。若 $u$ 遍历一个闭区间，只有两个候选切点 $p\le q$，左端只能用 $p$、右端只能用 $q$，则

$$
q-p\le\Delta-2\nu.
\tag{27.3}
$$

因为 $p$ 可服务的参数集合为 $[p-\Delta+\nu,p-\nu]$，$q$ 的为 $[q-\Delta+\nu,q-\nu]$。若两切点之差更大，两服务区间之间有非空缺口，不能覆盖一个左端要求前者、右端要求后者的连通参数区间。此论证允许重合切点。

现在使用四组精确的实际共同尾族；每个参数值都由所列尾域内的一条实际地址实现：

| 27.3 实际前接对 | 共同尾坐标域 | 较小当前值 $u$ 的准确范围 | 差 $\Delta$ | 仅有候选切点 |
| --- | --- | --- | --- | --- |
| 27.3a 标签 $3,0$ | $y\in X$ | $f_3(y)\in[-1,-t^2]$ | $t$ | $a,b$ |
| 27.3b 标签 $0,5$ | $y\in I$ | $f_0(y)\in[-t^4,g]$ | $t^2$ | $b,c$ |
| 27.3c 标签 $5,2$ | $y\in I$ | $f_5(y)\in[g,t]$ | $t$ | $c,d$ |
| 27.3d 标签 $2,25$ | $y\in I$ | $f_2(y)\in[v,2t]$ | $t^2$ | $d,e$ |

第一族的分离区间上端至多为 $g-\nu<c$；在 $u=-1$ 时只有 $a$ 可用，在 $u=-t^2$ 时只有 $b$ 可用。因此

$$
a\le-t^2-\nu,\qquad b-a\le t-2\nu.
$$

第二族的分离区间位于 $[-t^4+\nu,t-\nu]$ 内，由 (27.1) 排除 $a,d,e$；在两端 $u=-t^4,g$ 分别只能用 $b,c$。第三族位于 $[g+\nu,2t-\nu]$ 内，排除 $a,b,e$；两端 $u=g,t$ 分别只能用 $c,d$。第四族位于 $[v+\nu,\phi-\nu]$ 内，排除 $a,b,c$；两端 $u=v,2t$ 分别只能用 $d,e$。由 (27.3)，

$$
c-b\le t^2-2\nu,\qquad d-c\le t-2\nu,\qquad
e-d\le t^2-2\nu,\qquad e\ge2t+\nu.
$$

四个相邻切点差望远镜求和，使用 $t+t^2=1$，得到

$$
\phi+2\nu\le e-a\le2t+2t^2-8\nu=2-8\nu,
\qquad 10\nu\le2-\phi=t^2.
\tag{27.4}
$$

四族各次比较内部共享一条真实完整尾，且都约束同一 $Q$；不要求不同族共用一个尾，也没有拼接独立边缘像。正开预算 $r$ 包含每个 $0<\nu<r$ 的闭子预算，令 $\nu\uparrow r$ 得 $r\le\lambda$。

临界闭预算下，(27.4) 的外端相等，故两个外端切点约束和四个切点差约束的全部非负余量都为零，得到陈述中的切点。临界开预算下，对同一固定切点取闭子预算趋于 $\lambda$，先得到同样的全部弱约束，再得到同一刚性。相邻差交替为

$$
t-2\lambda>0,\qquad t^2-2\lambda=\frac45t^2>0.
$$

此外 $-a=11t^2/10<1$，$\phi-e=t^2-\lambda=9\lambda>0$；这里 $0<t^2<1/2$。所以切点严格且在支持内部。$\square$

### 27.2 完成域的闭临界归属矛盾

**命题 27.4（实际完整共同尾排除闭临界）。** 引理27.3的临界布局在 $\Omega$ 上不可能对闭预算 $\lambda$ 正确，即使解码器接收整个无限颜色记录。

证明。共同尾 $R$ 的来源 $3R,0R$ 当前值为 $-1,-t^2$。第一来源取零误差，第二取 $-\lambda$ 到达 $a$；未来均取零误差。若 $a$ 归左格 $C_0$，整个记录相同，所以 $a$ 必须归右。共同尾 $L$ 的来源 $2L,25L$ 当前值为 $2t,\phi$；分别取 $+\lambda,0$ 到达 $e,\phi$，未来均取零误差。因此 $e$ 必须归左。目标 $-1,a,e,\phi$ 都在 $X$ 内。

记 $s_1=a,s_2=b,s_3=c,s_4=d,s_5=e$。对 $k=1,2,3,4$，由 $\kappa_1(A_1)=I$ 选择一条实际 guard 一尾 $\eta_k$，其坐标为

$$
y_k=-1+\frac{k\phi}{5}\in(-1,t).
$$

依次使用合法前接对 $(3,0),(0,5),(5,2),(2,25)$，每对都共享所选的同一 $\eta_k$。由 $g\phi=t^2=10\lambda$，较小当前值依次为

$$
\begin{aligned}
f_3(y_1)&=-t^2-2\lambda=a-\lambda,\\
f_0(y_2)&=g-4\lambda=b-\lambda,\\
f_5(y_3)&=t-6\lambda=c-\lambda,\\
f_2(y_4)&=2t-8\lambda=d-\lambda.
\end{aligned}
$$

对应差为 $\Delta_k=t,t^2,t,t^2$，且 $s_{k+1}-s_k=\Delta_k-2\lambda$，故较大当前值为 $s_{k+1}+\lambda$。所有当前值和目标均在 $X$ 内：较小值至少为 $a-\lambda=-6t^2/5>-1$，较大值至多为 $e+\lambda=2t+2\lambda<\phi$。

对较小来源取 $+\lambda$，对较大来源取 $-\lambda$，当前目标分别为 $s_k,s_{k+1}$；以后均取零误差。若 $s_k$ 归右而 $s_{k+1}$ 归左，两目标属于同一中间格，完整共同未来又相同，造成不同首标签的碰撞。因此每对相邻切点都禁止“右归属随后左归属”。但首切点 $a$ 归右、末切点 $e$ 归左，五个归属中必有一次这种过渡，矛盾。此处使用大小恰为 $\lambda$ 的当前误差，结论只排除闭临界。$\square$

### 27.3 非整数环柱内部的两侧有限来源

**引理 27.5（有限柱端点与两侧同柱有限尾）。** 每个合法有限窗口柱的两个标量端点都在 $\mathbb Z[t]=\{m+nt:m,n\in\mathbb Z\}$ 中。点

$$
y_*=-1+\frac{\phi}{5}=\frac{t-4}{5}
$$

在 $I$ 内部且不属于 $\mathbb Z[t]$。取任一实际 $\eta_*\in A_1$ 编码 $y_*$，它的每个有限前缀柱都将 $y_*$ 包含在内部；该同一柱中，最终为 null 的合法 guard 一尾坐标在 $y_*$ 两侧都可任意逼近它。

证明。从任一 guard 出发的合法有限词 $w$ 若终止于 guard $s$，其完整柱像为 $J_w=f_w(I_s)$，其中 $I_0=X,I_1=I$。这是非退化闭区间，因为 $f_w$ 的斜率是非零的 $(-g)^{|w|}$。$I_0,I_1$ 的端点、五个平移量及 $-g$ 都在 $\mathbb Z[t]$ 内，有限仿射复合仍在该环内，故两端点在环中。

若 $(t-4)/5=m+nt$，则 $(5m+4)+(5n-1)t=0$。$t$ 的无理性迫使 $5n=1$，与 $n$ 为整数矛盾。又 $y_*=-1+\phi/5\in(-1,t)$，定理17.2保证所需 $\eta_*$ 存在；它不可能位于任何有限柱的端点。

固定其前 $N$ 个窗口 $w_N$。对任何以此词开始的实际 guard 一尾，保留更长的合法初段再接 $0^\infty$，仍合法且保留 $w_N$；收缩级数保证其坐标趋于原坐标。完整柱像是 $J_{w_N}$，因此这样的有限尾坐标在整个柱像中稠密。$y_*$ 是柱内部点，所以对每个 $\epsilon>0$ 可分别从柱内的左右开区间选取最终为 null 的实际尾 $\eta_-,\eta_+\in A_1$，满足

$$
\kappa(\eta_-)=y_*-\delta_-,\qquad
\kappa(\eta_+)=y_*+\delta_+,\qquad
0<\delta_-,\delta_+<\epsilon.
$$

这是在两侧分别选取有限尾，不是断言某一条 $\eta_*$ 的任意截断会从两侧逼近，也不声称 $y_*$ 有有限实现。$\square$

**命题 27.6（每个固定有限视界的严格临界碰撞）。** 对引理27.3的临界切点布局，任意固定有限 $h\ge0$ 都存在两条首标签不同的实际 $D$ 来源，在每个坐标使用严格小于 $\lambda$ 的误差，产生完全相同的长度 $h+1$ 颜色记录。结论与切点归属无关。

证明。第一临界间隙满足

$$
f_3(y_*)=a-\lambda,\qquad f_0(y_*)=b+\lambda,
\qquad b-a=t-2\lambda>0.
$$

选择整数 $N\ge h$ 使

$$
\operatorname{diam}(X)g^{N-h}<2\lambda,
$$

再用引理27.5在同一个 $w_N$ 柱内分别选取 $\eta_-,\eta_+$，使

$$
0<\delta_-,\delta_+<\epsilon,\qquad
0<\epsilon<\min\left\{\frac{\lambda}{g},\frac{2(b-a)}{g}\right\}.
$$

取两条完整实际来源 $\omega_-=3\eta_-$、$\omega_+=0\eta_+$。两个前接都可接 guard 一尾；两条来源最终为 null，首标签分别为 $3,0$。令 $x_j^\pm=\kappa_0(T^j\omega_\pm)$，则

$$
x_0^-=a-\lambda+g\delta_-,\qquad
x_0^+=b+\lambda-g\delta_+.
$$

当前目标分别选择

$$
z_0^-=a+\frac{g\delta_-}{2},\qquad
z_0^+=b-\frac{g\delta_+}{2}.
$$

两目标都严格在 $(a,b)$ 内，故同色而不依赖任何端点归属。相应误差为

$$
\varepsilon_0^-=\lambda-\frac{g\delta_-}{2},\qquad
\varepsilon_0^+=-\lambda+\frac{g\delta_+}{2},
$$

其绝对值严格小于 $\lambda$。

对 $1\le j\le h$，两条实际尾 $T^{j-1}\eta_-,T^{j-1}\eta_+$ 仍共享至少 $N-j+1$ 个窗口。对这个共同前缀使用实际级数，得到

$$
|x_j^--x_j^+|
\le\operatorname{diam}(X)g^{N-j+1}
\le\operatorname{diam}(X)g^{N-h}<2\lambda.
$$

为两个来源选择同一个以后目标

$$
z_j=\frac{x_j^-+x_j^+}{2}\in X,\qquad 1\le j\le h.
$$

它是两个来源在该时刻的真实坐标中点，每个所需误差严格小于 $\lambda$。全部当前目标和以后目标在 $X$ 内，裁剪固定。于是当前目标同色，以后目标逐坐标相等，整个有限记录相同而首标签不同。当 $h=0$ 时只使用当前目标，后面的列表为空。

这里两条有限尾来自同一柱的两侧，彼此不要求有相同的完整未来；各自全部坐标都由其自身完整来源承担。来源对依赖所选 $h$，此有限前缀估计不延伸为全部未来的统一估计。$\square$

### 27.4 严格预算余量下的无限到有限边界

**定理 27.7（紧致完成域的严格余量有限取得）。** 固定上述任意有限格量化器 $Q$，不限定为六格。若一个整个无限记录的固定确定解码器在 $\Omega$ 上对正预算 $\nu$ 正确，预算可为闭或正开，则对每个 $0<\rho<\nu$，存在一个有限 $h\ge0$ 和一个固定解码器

$$
d_h:\mathcal C^{h+1}\longrightarrow\Lambda
$$

使同一个 $Q$ 在全部 $\Omega$ 上从前 $h+1$ 次实际取得的记录，对闭预算 $\rho$ 统一恢复首窗。

证明。$\Omega$ 是有限离散位字母表乘积中的闭合法子空间，因而紧致；首窗类

$$
F_\ell=\{\omega\in\Omega:\sigma_0(\omega)=\ell\},\qquad\ell\in\Lambda,
$$

是有限窗口决定的开闭柱集，因而也紧致。每个 $x_j$ 连续：$T^j$ 连续，编码级数一致收敛。给有限颜色字母表 $\mathcal C$ 离散拓扑，记 $C_i=Q^{-1}(i)$、$J_i=\overline{C_i}^{\,X}$。在紧致乘积 $\Omega\times\mathcal C^{\mathbb N_0}$ 中定义

$$
\mathscr R_\rho=
\{(\omega,r):\operatorname{dist}(x_j(\omega),J_{r_j})\le\rho
\text{ 对全部 }j\ge0\}.
$$

每个固定坐标条件是有限个闭距离条件与开闭颜色条件的并，故闭；全部坐标的交仍闭，所以 $\mathscr R_\rho$ 紧致。这个关系的见证是对所有坐标共用的一条完整 $\omega$，不是逐坐标选择来源。按首标签投影为

$$
\mathscr K_\ell=
\{r:\exists\omega\in F_\ell,\ (\omega,r)\in\mathscr R_\rho\},
$$

每个 $\mathscr K_\ell$ 都是紧致集的投影，因而紧致。

闭包关系中的每个见证都能在较大预算内由同一来源实际实现。固定统一正余量

$$
\delta=\frac{\nu-\rho}{2}>0.
$$

对 $(\omega,r)\in\mathscr R_\rho$，每个 $j$ 取 $J_{r_j}$ 中到 $x_j(\omega)$ 的最近点 $z_j$，再由 $C_{r_j}$ 在其闭包中的稠密性取 $v_j\in C_{r_j}$ 满足 $|v_j-z_j|<\delta$；单点格直接取其唯一点。于是

$$
\varepsilon_j=v_j-x_j(\omega),\qquad
|\varepsilon_j|<\rho+\delta=\frac{\rho+\nu}{2}<\nu.
$$

甚至 $\sup_j|\varepsilon_j|\le(\rho+\nu)/2<\nu$。全部 $v_j\in X$，裁剪固定，所得实际颜色流恰为 $r$。此选择覆盖单点格和任意端点归属；误差仍相对于同一 $\omega$ 的真实轨迹定义，并使用一个对所有坐标共同的正余量。因无限解码器在原开或闭预算下正确，不同首标签的 $\mathscr K_\ell$ 必须两两不交。

对不同 $\ell,m$，考虑 $\mathscr K_\ell\times\mathscr K_m$ 中的嵌套紧致集

$$
E_h^{\ell,m}=\{(r,s):r_j=s_j\text{ 对 }0\le j\le h\},\qquad h\ge0.
$$

若所有 $E_h^{\ell,m}$ 都非空，紧致性给出其交中的一对流；它们每个坐标都相等，违背 $\mathscr K_\ell\cap\mathscr K_m=\varnothing$。因此每对不同首标签都在某个有限前缀长度已分离。首标签有限，取这些长度的最大值得到一个统一有限 $h$。定义 $d_h$ 返回与给定前缀相容的唯一 $\mathscr K_\ell$ 的标签；无相容流的输入任意赋值，得到全定义确定函数。

最后固定任一实际 $\omega$ 及闭预算 $\rho$ 下已取得的前 $h+1$ 个记录。它们的裁剪目标 $v_j\in C_{R_j}$ 满足

$$
\operatorname{dist}(x_j(\omega),J_{R_j})
\le|x_j(\omega)-v_j|\le\rho.
$$

仅为证明见证，在 $j>h$ 处以同一来源的零未来误差延伸为 $r_j=Q(x_j(\omega))$。此完整流属于 $\mathscr K_{\sigma_0(\omega)}$，故其已取得前缀由 $d_h$ 正确解码。这个延伸没有作为观测数据交给 $d_h$，也没有宣称未取得坐标已被取得。$\square$

定理27.7保持量化器 $Q$，可以改变解码器；此证明只给出 $h$ 的存在性，不提供可计算的视界界。严格余量用于将闭包点移到实际颜色格内，故此证明不给出 $\rho=\nu$ 的有限化，也不将非紧致 $D$ 的无限记录合同转到有限记录合同。

**推论 27.8（预算 $1/25$ 下的有限连续视界最小七格）。** 对 $\Omega$ 或 $D$，固定任一有限 $h\ge1$，在闭或正开预算 $\nu=1/25$ 下统一恢复首窗的连通量化器最小格数为七。

证明。第24.1节的 $8/13<t<5/8$ 给出

$$
\lambda<\frac1{26}<\frac1{25}<\frac3{64}<\mu.
$$

定理27.1排除至多六格；定理25.13给七格存在范围，定理24.13的已给定七格相邻仪器在此预算下可用。对任意 $h\ge1$，实际取得规定的全部记录后，解码器只使用前两个记录，即得七格上界。$\square$

这些结论把响应边界的容量同允许的未来和实际取得相联系：同一个首窗任务中，有限连续记录受到六格半径 $\lambda$ 的严格限制；若整个完成未来在更大预算下足以分辨首窗，严格缩小预算后就存在一个足够的有限响应边界。后一关系使用经典紧致性，仍以同一完整来源及真正取得的有限列表为依据，不生成未取得的未来。

本章的证明不决定 $\Omega$ 整个无限记录的正开临界 $\lambda$，不提出 $D$ 的整个无限记录结论，也不确定六格半径的准确上确界、匹配构造或跨全部有限视界的统一严格间隙。这里没有自主标量或颜色动力学，亦没有从地址折叠和观察容量推出物理时空起源或热力学时间箭头。

## 追加锚（27·本行以下为增补区）

## 28. 六格完整记录的有限来源临界半径与完成域统一噪声间隙

沿用第27章的实际地址、三位删除和误差合同。来源标签为 $\Lambda=\{3,0,5,2,25\}$，其中 $0=\mathrm{null}$；六个颜色按空间顺序编号为 $\mathcal C=\{0,1,2,3,4,5\}$。这两个字母表不同，合法地址的 guard 状态也不是颜色状态。置

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad
X=[-1,\phi],\qquad I=[-1,t],
$$

$$
\lambda:=\lambda_{\mathrm{noise}}=\frac{t^2}{10}
=\frac{1-g}{20}.
$$

这里的 $\lambda$ 只表示本章噪声半径。固定同一个六格连通量化器 $Q:X\to\mathcal C$，各格非空，允许任意合法切点归属及单点格；同一实际地址始终给出

$$
x_j(\omega)=\kappa_0(T^j\omega),\qquad
R_j=Q\!\left(\operatorname{clip}_X(x_j(\omega)+\varepsilon_j)\right).
$$

闭预算 $\nu$ 指每个 $|\varepsilon_j|\le\nu$，正开预算指每个 $|\varepsilon_j|<\nu$。误差在裁剪前分别任意选择，正开合同不要求统一的严格上确界余量。解码器是一个固定确定函数，只接收合同规定的实际颜色记录，目标是恢复 $\sigma_0(\omega)$。$D$ 是最终为空尾的来源域，$\Omega$ 是完整合法来源域。

以下先证明 $D$ 的完整记录合同，再用一对真实周期来源给出 $\Omega$ 的全布局定量上界。两者使用不同的来源域，完整记录和每个固定有限视界也分别处理。

### 28.1 临界闭扩张关系与有限来源的完整记录

记引理27.3的临界切点为

$$
\begin{aligned}
p_1^\star=a^\star&=-t^2-\lambda,&
p_2^\star=b^\star&=g-3\lambda,&
p_3^\star=c^\star&=t-5\lambda,\\
p_4^\star=d^\star&=2t-7\lambda,&
p_5^\star=e^\star&=2t+\lambda.&&
\end{aligned}
\tag{28.1}
$$

其六格闭包依次为 $[-1,a^\star],[a^\star,b^\star],\ldots,[e^\star,\phi]$。令

$$
\begin{aligned}
E_0&=[-1,-t^2],\\
E_1&=[-t^2-2\lambda,g-2\lambda],\\
E_2&=[g-4\lambda,t-4\lambda],\\
E_3&=[t-6\lambda,2t-6\lambda],\\
E_4&=[2t-8\lambda,2t+2\lambda],\\
E_5&=[2t,\phi].
\end{aligned}
\tag{28.2}
$$

对颜色流 $R\in\mathcal C^{\mathbb N_0}$，定义完整闭扩张关系的来源纤维

$$
P_E(R)=
\{\omega\in D:x_j(\omega)\in E_{R_j}\text{ 对全部 }j\ge0\}.
\tag{28.3}
$$

任何临界闭预算下的实际记录都满足该关系。事实上，若裁剪前误差不超过 $\lambda$，裁剪后目标到 $x_j\in X$ 的距离也不超过 $\lambda$；目标在其颜色格内，故 $x_j$ 在该格闭包的 $\lambda$ 扩张与 $X$ 的交中，恰为 (28.2)。这里只使用必要包含，不把闭扩张端点的接触当作实际可取得的等价判据。

**定理 28.1（有限来源完整闭扩张关系的唯一性）。** 对每个完整颜色流 $R$，都有 $|P_E(R)|\le1$。因此临界布局 (28.1) 存在一个固定完整记录解码器，在 $D$ 上对闭预算 $\lambda$ 正确；同一解码器适用于该布局的每一种合法切点归属。

证明。命题14.6和定理17.2给出按空间顺序排列的五个实际根像

$$
[-1,-t^2],\quad[-t^2,g],\quad[g,t],
\quad[t,2t],\quad[2t,\phi],
\tag{28.4}
$$

分别对应标签 $3,0,5,2,25$。先穷尽六个扩张格可容纳的不同标签。

$E_0$ 除标签 $3$ 外，只可能在 $-t^2$ 接触标签 $0$；但 $f_0(y)=-gy=-t^2$ 强制 $y=\phi$。由命题14.6，编码 $\phi$ 的尾唯一为非最终空尾的 $R_{\mathrm{ext}}=(25,3)^\infty$，不可能是 $D$ 来源的实际尾。$E_5$ 除标签 $25$ 外，只可能在 $2t$ 接触标签 $2$；$f_2(y)=1-gy=2t$ 强制 $y=-1$，其唯一极值尾 $L=(3,25)^\infty$ 同样不在 $D$。因此有限来源在两个端格共享颜色时不能有不同的当前标签。

四个内格分别只允许相邻标签对

$$
(\ell_k,m_k)=(3,0),(0,5),(5,2),(2,25),
\qquad 1\le k\le4.
\tag{28.5}
$$

确切地，$E_1$ 的下端为 $-6t^2/5>-1$、上端为 $g-t^2/5<g$，只与根像 $3,0$ 相交。$E_2$ 的下端比 $-t^2$ 大 $g+3t^2/5>0$、上端小于 $t$，只允许 $0,5$。$E_3$ 的下端比 $g$ 大 $2t^2/5>0$、上端小于 $2t$，只允许 $5,2$。$E_4$ 的下端比 $t$ 大 $t-4t^2/5>0$、上端比 $\phi$ 小 $4t^2/5>0$，只允许 $2,25$。这些都是闭格的排除，包含全部等号情形。

置

$$
y_k=-1+\frac{k\phi}{5}\in I,\qquad
(\Delta_1,\Delta_2,\Delta_3,\Delta_4)=(t,t^2,t,t^2).
$$

使用 $g\phi=t^2=10\lambda$ 和五个分支公式，临界恒等式为

$$
E_k=[f_{\ell_k}(y_k),f_{m_k}(y_k)],
\qquad
f_{m_k}(y)-f_{\ell_k}(y)=\Delta_k
\quad(1\le k\le4).
\tag{28.6}
$$

现在若两条不同的 $D$ 来源都属于 $P_E(R)$，取它们最后一个不同窗口的位置 $n$。其 $n+1$ 时刻以后是完全相同的有限尾，记该实际尾坐标为 $y$。在时刻 $n$，两个端格已被排除，只能出现 (28.5) 的某个相邻对；必要时交换两来源的顺序。两个当前值为 $f_{\ell_k}(y),f_{m_k}(y)$，均在 $E_k$ 内，差恰为 $\Delta_k$。但 (28.6) 中 $E_k$ 的宽度也恰为 $\Delta_k$，所以两个值必须分别等于其左右端点。分支的斜率 $-g\ne0$，从而强制 $y=y_k$。

有限尾的窗口级数只有有限个非零项，其平移量和 $-g$ 都属于 $\mathbb Z[t]$，故 $y\in\mathbb Z[t]$。另一方面，

$$
y_k=\frac{k-5}{5}+\frac{k}{5}t\notin\mathbb Z[t]
\qquad(1\le k\le4).
$$

若 $y_k=m+nt$，其中 $m,n\in\mathbb Z$，则 $t$ 的无理性迫使 $5n=k$，与 $1\le k\le4$ 矛盾。这排除了最后一个不同窗口，证明完整闭扩张关系本身的纤维唯一性。

定义 $d_\infty:\mathcal C^{\mathbb N_0}\to\Lambda$：若 $P_E(R)$ 有唯一来源，返回其首标签；若为空，返回 $0$。实际闭预算记录的真实来源必在该纤维中，所以此函数正确。关系 (28.3) 不依赖切点归属，因此同一函数适用于全部归属。这里得到的是完整记录的集合论唯一性，不给出有限停止时刻或有效识别算法。$\square$

**定理 28.2（六格有限来源完整记录的准确正半径范围）。** 在 $D$ 上允许完整无限记录时，六格连通仪器的闭预算与正开预算可行范围都恰为

$$
\boxed{(0,\lambda].}
\tag{28.7}
$$

证明。定理28.1的固定布局与解码器适用于闭预算 $\lambda$ 的全部子合同，包括正开预算 $\lambda$，给出 (28.7) 的存在方向。

反之，假设某个六格仪器在 $D$ 的完整记录合同下，对开或闭预算 $\nu>\lambda$ 正确。固定 $\lambda<\rho<\nu$。我们只检验完整来源的实际共同尾当前值，不转移无限观察向量。

取任意一条实际完整尾 $\eta$，以及可合法前接它的两个不同标签。若这两个当前值在闭半径 $\rho$ 下能取得同一颜色，取对应的两个裁剪后目标 $v,v'\in X$；各目标到自己的当前真值的距离不超过 $\rho$。把这同一条 $\eta$ 截断为一条共同的最终空尾 $\eta_N$，保留所需 incoming guard。收缩级数允许 $N$ 足够大，使两个前接后的当前真值各改变不到 $\nu-\rho$。对新的两条有限来源直接取误差到原目标 $v,v'$，大小都严格小于 $\nu$。从下一时刻起，两来源的实际地址恰为同一条 $\eta_N$，以后全部取相同的零误差，便自动给出完全相同的整个未来记录。连同当前同色，这是 $D$ 上的完整记录碰撞，矛盾。

因此，所有合法完整共同尾对在闭半径 $\rho$ 下的当前允许颜色必须不交。引理27.3的五切点定位与四组必要不等式只使用这一分离条件，故同一个 $Q$ 的切点必须满足

$$
a\le-t^2-\rho,\qquad e\ge2t+\rho,\qquad
p_{k+1}-p_k\le\Delta_k-2\rho
\quad(1\le k\le4).
$$

复用其望远镜求和，即得

$$
\phi+2\rho\le e-a\le2-8\rho,
\qquad \rho\le\frac{t^2}{10}=\lambda,
$$

与所选 $\rho>\lambda$ 矛盾。此处只转移两个当前目标，以后使用新来源精确共同的有限尾，没有近似整个无限记录，也没有通过近似转移闭临界端点。$\square$

### 28.2 一对真实周期来源的全未来共同记录

**命题 28.3（临界布局内的严格周期碰撞）。** 存在两条首窗不同的实际合法周期地址，在布局 (28.1) 的任意切点归属下产生同一完整颜色记录 $(1,0,2)^\infty$。两条误差流具有共同的闭上界

$$
r=\frac{44g-5}{152}<\lambda.
\tag{28.8}
$$

证明。取

$$
\omega^-=(3,3,5,0,3,0)^\infty,\qquad
\omega^+=T^3\omega^-=(0,3,0,3,3,5)^\infty.
\tag{28.9}
$$

窗口 $3,0$ 输出 guard 零，窗口 $5$ 输出 guard 一；每个 $5$ 后都接允许 incoming guard 一的窗口 $0$，两条周期接缝也合法。首窗分别为 $3,0$。第一来源的周期六实际坐标如下，第二来源的坐标是同表向前三位的循环移位：

| 28.3 周期相位 $j\bmod6$ | 实际窗口 | $z_j=x_j(\omega^-)$ |
| --- | --- | --- |
| 28.3a 相位 $0$ | $3$ | $-(33+6g)/76$ |
| 28.3b 相位 $1$ | $3$ | $-(52+5g)/76$ |
| 28.3c 相位 $2$ | $5$ | $(23+14g)/76$ |
| 28.3d 相位 $3$ | $0$ | $(8+15g)/76$ |
| 28.3e 相位 $4$ | $3$ | $-(47+8g)/76$ |
| 28.3f 相位 $5$ | $0$ | $(6+9g)/76$ |

这些标量由同一实际地址承担。为逐项核对，使用

$$
g^2+4g=1,\qquad t=\frac{1+g}{2},\qquad t^2=\frac{1-g}{2}.
$$

对 $f_3(y)=-t-gy,\ f_0(y)=-gy,\ f_5(y)=t^2-gy$，六个递推的分子准确为

$$
\begin{aligned}
76f_3(z_1)&=-38-38g+52g+5g^2=-33-6g=76z_0,\\
76f_3(z_2)&=-38-38g-23g-14g^2=-52-5g=76z_1,\\
76f_5(z_3)&=38-38g-8g-15g^2=23+14g=76z_2,\\
76f_0(z_4)&=47g+8g^2=8+15g=76z_3,\\
76f_3(z_5)&=-38-38g-6g-9g^2=-47-8g=76z_4,\\
76f_0(z_0)&=33g+6g^2=6+9g=76z_5.
\end{aligned}
\tag{28.10}
$$

合法周期地址的级数编码满足相同递推；六分支复合斜率为 $g^6<1$，固定点唯一，故表中确为该地址的实际坐标。

所需严格比较全部由有理界

$$
\frac4{17}<g<\frac6{25}
\tag{28.11}
$$

给出。多项式 $x^2+4x-1$ 在正轴严格递增，在两端的值分别为 $-1/289$ 与 $11/625$，而 $g$ 是其正根。用 $g$ 写前三个临界切点：

$$
a^\star=\frac{11g-11}{20},\qquad
b^\star=\frac{23g-3}{20},\qquad
c^\star=\frac{1+3g}{4}.
$$

定义真实坐标到近侧切点的距离

$$
A=a^\star-z_0=\frac{239g-44}{380},\quad
B=z_3-b^\star=\frac{97-362g}{380},\quad
C=b^\star-z_5=\frac{392g-87}{380}.
\tag{28.12}
$$

三者均为正，且

$$
\begin{aligned}
\lambda-A&=\frac{63-258g}{380}>0,&
\lambda-B&=\frac{343g-78}{380}>0,&
\lambda-C&=\frac{106-411g}{380}>0,\\
A-B&=\frac{601g-141}{380}>0,&
A-C&=\frac{43-153g}{380}>0.&&
\end{aligned}
\tag{28.13}
$$

例如 $63-258g>27/25$、$343g-78>46/17$、$601g-141>7/17$；其余分子同样由 (28.11) 的相应端点给出正值。因此 $0<B<A<\lambda$、$0<C<A<\lambda$。其余三个坐标满足

$$
-1<z_1<z_4<a^\star,\qquad b^\star<z_2<c^\star.
\tag{28.14}
$$

可直接核对

$$
\begin{aligned}
z_4-z_1&=\frac{5-3g}{76}>0,&
a^\star-z_4&=\frac{26+249g}{380}>0,&52+5g&<76,\\
z_2-b^\star&=\frac{172-367g}{380}>0,&
c^\star-z_2&=\frac{43g-4}{76}>0.&&
\end{aligned}
$$

取固定的内部余量与观测目标

$$
m_0=\frac{\lambda-A}{2},\qquad
m_3=\frac{\lambda-B}{2},\qquad
m_5=\frac{\lambda-C}{2},
$$

$$
(u_0,u_1,u_2,u_3,u_4,u_5)
=(a^\star+m_0,\ z_1,\ z_2,\ b^\star-m_3,\ z_4,\ b^\star+m_5).
\tag{28.15}
$$

因为三个 $m_i$ 均在 $(0,\lambda/2)$ 内，且

$$
b^\star-a^\star=t-2\lambda>8\lambda,\qquad
c^\star-b^\star=t^2-2\lambda=8\lambda,
$$

所以

$$
u_0,u_3\in(a^\star,b^\star),\qquad
u_1,u_4\in(-1,a^\star),\qquad
u_2,u_5\in(b^\star,c^\star).
\tag{28.16}
$$

三个非零误差为

$$
u_0-z_0=\frac{\lambda+A}{2},\qquad
u_3-z_3=-\frac{\lambda+B}{2},\qquad
u_5-z_5=\frac{\lambda+C}{2},
$$

其余为零。由 (28.13)，最大绝对值恰为

$$
r=\frac{\lambda+A}{2}
=\frac{44g-5}{152}
=\lambda-m_0<\lambda.
$$

对 $\omega^-$ 使用 $(u_0,\ldots,u_5)^\infty$，对 $\omega^+$ 使用其向前三位的循环移位。真实坐标也恰相差该移位，所以两套误差都满足同一闭上界 $r$。所有目标在 $X$ 内，裁剪固定；(28.16) 使两条完整颜色记录都恰为 $(1,0,2)^\infty$，任意切点归属不改变颜色。不同首窗因此不能被同一解码器同时恢复。$\square$

### 28.3 全布局的统一定量间隙

**定理 28.4（完成域全未来与有限来源固定视界的统一上界）。** 置

$$
\boxed{\epsilon=\frac{343g-78}{6080}>0,\qquad
U=\lambda-\epsilon=\frac{382-647g}{6080}<\lambda.}
\tag{28.17}
$$

对 $\Omega$ 上任意六个非空连通格、任意合法端点归属及固定首窗解码器，每个可行的正闭预算或正开预算都必须满足

$$
\boxed{\nu<U,}
\tag{28.18}
$$

即使解码器取得整个无限记录也如此。对 $D$，同一严格上界适用于每个预先固定的有限视界 $h\ge0$。

证明。先在 $\Omega$ 上考虑闭预算。引理27.3的四组实际共同尾必要条件为：

$$
a\le-t^2-\nu,\qquad e\ge2t+\nu,\qquad
p_{k+1}-p_k\le\Delta_k-2\nu\quad(1\le k\le4).
\tag{28.19}
$$

每对来源都共享自己的完整实际未来，因此该必要条件也约束完整记录合同。对于正开预算，同一个 $Q$ 和同一个解码器在每个 $0<\rho<\nu$ 的闭子预算下正确；在 (28.19) 中令 $\rho\uparrow\nu$ 即得同样的弱不等式。这里取极限的只是固定切点的必要数值不等式，没有闭合正开误差流集合。引理27.3的求和先给出 $\nu\le\lambda$。

令 $s=\lambda-\nu\ge0$，以 (28.1) 为参照，定义非负松弛

$$
\alpha=a^\star+s-a,\qquad
\beta=e-e^\star+s,\qquad
\sigma_k=\Delta_k-2\nu-(p_{k+1}-p_k).
$$

两种展开 $e-a$ 的方式分别给出

$$
e-a=e^\star-a^\star-2s+\alpha+\beta
=e^\star-a^\star+8s-\sum_{k=1}^4\sigma_k,
$$

因而

$$
\alpha+\beta+\sum_{k=1}^4\sigma_k=10s.
\tag{28.20}
$$

逐个切点有

$$
p_k-p_k^\star=(2k-1)s-\alpha-\sum_{i<k}\sigma_i,
$$

其中被减去的非负量不超过 $10s$，所以得到不对称的漂移界

$$
\boxed{(2k-11)s\le p_k-p_k^\star\le(2k-1)s.}
\tag{28.21}
$$

特别地，

$$
a^\star-9s\le a\le a^\star+s,\qquad
b^\star-7s\le b\le b^\star+3s,\qquad
c^\star-5s\le c\le c^\star+5s.
\tag{28.22}
$$

保持命题28.3的两条实际周期来源、六个目标及误差全部不变。其三个近切点余量准确为

$$
m_0=\frac{63-258g}{760},\qquad
m_3=\frac{343g-78}{760}=8\epsilon,\qquad
m_5=\frac{106-411g}{760}.
$$

还需如下严格余量：

$$
\begin{aligned}
m_0-\epsilon&=\frac{582-2407g}{6080}>0,\\
m_5-3\epsilon&=\frac{1082-4317g}{6080}>0.
\end{aligned}
\tag{28.23}
$$

由 $g<6/25$，两分子分别大于 $108/25$ 与 $1148/25$。又 $0<m_3<\lambda/2$，故

$$
0<\epsilon<\lambda/16,\qquad
r=\lambda-m_0<U.
\tag{28.24}
$$

其余会受内部切点移动影响的目标余量都大于 $\lambda$。对 $u_0$ 到 $b^\star$、$u_3$ 到 $a^\star$、$u_5$ 到 $c^\star$ 的距离，这由两个格宽及 $m_i<\lambda/2$ 直接得到。对未移动的三个目标，准确比较为

$$
a^\star-z_4=\frac{26+249g}{380}>\lambda,\qquad
a^\star-z_1>a^\star-z_4,
$$

$$
z_2-b^\star=\frac{172-367g}{380}>\lambda,\qquad
c^\star-z_2=\frac{43g-4}{76}>\lambda.
\tag{28.25}
$$

逐项减去 $\lambda=(19-19g)/380$，相关分子分别为 $7+268g,\ 153-348g,\ 234g-39$，都由 (28.11) 为正。$z_1,z_4$ 到固定支持端点 $-1$ 的距离也始终为正。

现假设存在可行预算 $U\le\nu\le\lambda$，则 $0\le s\le\epsilon$。由 (28.22)–(28.23)，

$$
u_0-a\ge m_0-s>0,\qquad
b-u_3\ge m_3-7s\ge\epsilon>0,\qquad
u_5-b\ge m_5-3s>0.
$$

$u_0$ 的另一侧边界 $b$ 最多向下移动 $7\epsilon$，$u_3$ 的另一侧边界 $a$ 最多向上移动 $\epsilon$，$u_5$ 的另一侧边界 $c$ 最多向下移动 $5\epsilon$。这些损失都小于 $\lambda$，因而不能耗尽刚才大于 $\lambda$ 的原余量。对 $u_1=z_1,u_4=z_4$，$a$ 最多向下移动 $9\epsilon<\lambda$；对 $u_2=z_2$，$b$ 最多向上移动 $3\epsilon$、$c$ 最多向下移动 $5\epsilon$。由 (28.25)，六个固定目标仍满足

$$
u_0,u_3\in(a,b),\qquad
u_1,u_4\in(-1,a),\qquad
u_2,u_5\in(b,c).
\tag{28.26}
$$

因此这些格在所需位置有严格内部，单点格及端点归属均不能改变该碰撞。使用完全相同的两条周期来源和固定目标流，两条记录仍为 $(1,0,2)^\infty$，每个误差的绝对值不超过 $r<U\le\nu$。这同时违反闭预算和逐坐标正开预算的正确性。预算 $\nu>\lambda$ 已由 (28.19) 排除，故 $\Omega$ 的全部可行正预算都满足 (28.18)。相同碰撞也适用于其每个固定有限视界。

最后固定 $D$ 上的一个有限 $h$。引理27.2保持同一 $Q$、同一解码器和首标签，把 $D$ 的闭或正开预算 $\nu$ 正确性转为 $\Omega$ 的正开预算 $\nu$ 正确性。其转移只保留有限目标向量：在有限列表的正误差余量内，用同一来源的合法有限截断逼近全部真实坐标，再逐坐标取新误差到完全相同的原目标。因此它保留切点颜色，不要求量化器连续。应用刚证出的 $\Omega$ 上界即得 $\nu<U$。有限最大值的严格余量是该转移的条件；这里没有把两条周期来源的整个无限目标流转到 $D$。$\square$

### 28.4 来源域、取得范围与响应边界

六格连通首窗合同的结果可分别列为：

| 28.4 来源域 | 规定的实际记录 | 正闭预算及逐坐标正开预算 | 范围性质 |
| --- | --- | --- | --- |
| 28.4a 最终空尾域 $D$ | 整个无限记录 | 恰为 $(0,\lambda]$ | 准确范围，临界布局达到 $\lambda$ |
| 28.4b 最终空尾域 $D$ | 每个固定有限 $R_0,\ldots,R_h$ | 必须 $\nu<U$ | 必要上界 |
| 28.4c 完整来源域 $\Omega$ | 每个固定有限 $R_0,\ldots,R_h$ | 必须 $\nu<U$ | 必要上界 |
| 28.4d 完整来源域 $\Omega$ | 整个无限记录 | 必须 $\nu<U$ | 必要上界 |

后三行只给必要上界，不宣称其中每个预算都有匹配仪器。对于 $\Omega$ 的完整记录和两个域的固定有限视界，可行正预算集合非空时，其上确界至多为 $U$；逐个预算严格小于 $U$ 不推出上确界严格小于 $U$。本章不确定这些合同的准确最优半径或上确界是否可达。$r$ 只是固定周期见证的误差上界，$\epsilon$ 与各 $m_i$ 是证明余量，不能另当作全布局最优半径。

定理28.1使用完整闭扩张关系排除有限来源的全部不同地址，临界唯一性不只针对正开误差。命题28.3的周期地址不在 $D$，其全未来碰撞也没有从一族有限视界碰撞交换量词得到。定理28.2只近似两个共同尾当前目标；定理28.4对 $D$ 的转移只近似一个固定有限列表。这些范围使 $D$ 的完整记录达到 $\lambda>U$ 与全部有限视界的上界相容。完整记录唯一性不提供有限或有效停止保证，固定视界上界也不裁决自适应停止合同。

就首窗恢复这一任务而言，响应边界是同一完整地址在规定时刻真正取得的颜色记录；分辨能力由来源域、噪声合同和允许使用的未来共同决定。临界六格可以从全部未来分辨每条有限来源，完整来源域却保留真实周期来源的共同记录，并在所有满足近临界必要条件的布局中保持该碰撞。地址折叠后的标量位置与删窗次序据此组织任务相对的空间、时间和边界关系；上述恢复与碰撞结论限定了边界能携带哪些来源信息。它们不推出物理时空起源、颜色自主更新、总存储最小值或热力学时间箭头。

## 追加锚（28·本行以下为增补区）

## 29. 临界六格的有限状态自适应首窗恢复与实际空尾后等待界

本章固定第28.1节的临界布局 (28.1)、闭扩张区间 (28.2) 以及同一实际来源的连续取得合同。沿用 $t=(\sqrt5-1)/2$、$\phi=1+t$、$g=t^3=2t-1$、$\lambda=t^2/10$，并记 $I_0=X=[-1,\phi]$、$I_1=[-1,t]$。来源标签为 $\Lambda=\{3,0,5,2,25\}$，其中 $0=\mathrm{null}$；观察颜色为 $\mathcal C=\{0,1,2,3,4,5\}$。合法 guard、来源标签和观察颜色分别保留，不相互识别。

量化器 $Q$ 始终为同一个临界六格仪器，允许五个切点任意合法归属。对一条实际地址 $\omega\in\Omega$，实际取得的颜色为

$$
x_j(\omega)=\kappa_0(T^j\omega),\qquad
R_j=Q\!\left(\operatorname{clip}_X(x_j(\omega)+\varepsilon_j)\right),
\qquad |\varepsilon_j|\le\lambda.
\tag{29.1}
$$

误差在裁剪前逐坐标分别受限。以下结论也适用于逐坐标正开预算。有限来源域 $D$ 仍为最终全是空窗的地址。停止目标只要求返回原始首窗 $\sigma_0(\omega)$；停止计数是已经取得的颜色数。

本章证明一个固定有限状态观察器：在任何实际 $\Omega$ 记录上，它一旦停止，首窗输出正确；在每个实际 $D$ 记录上，它有限停止。还存在只依赖此固定观察器的有限整数 $K$，使实际空尾从窗口 $N$ 开始的每次实际运行都满足 $T_{\mathrm{stop}}\le N+K$。这里 $N$ 不作为输入，也不由该输出认证。

### 29.1 最终颜色一与完成域的完整候选纤维

**定义 29.1（闭关系候选与首标签证书）。** 对任意已经取得的有限色词 $r_0,\ldots,r_h$，定义

$$
\begin{aligned}
\mathcal K_h(r)
&=\{\eta\in\Omega:x_j(\eta)\in E_{r_j}\text{ 对 }0\le j\le h\},\\
\mathcal L_h(r)
&=\{\sigma_0(\eta):\eta\in\mathcal K_h(r)\}.
\end{aligned}
\tag{29.2}
$$

对完整色流再定义

$$
\mathcal K_\infty(r)=\bigcap_{h\ge0}\mathcal K_h(r).
\tag{29.3}
$$

这里 $E_i$ 正是 (28.2) 的六个闭区间。实际闭预算记录的真实来源属于所有相应候选集，由第28.1节的裁剪距离包含得到。候选集描述的是闭扩张关系；它没有把每个扩张端点都宣称为任意切点归属下可实际取得的同色目标。

**引理 29.2（实际空尾产生颜色一，最终颜色一强制候选空尾）。** 若实际来源 $\omega\in D$ 从窗口 $N$ 起全是空窗，则其每个允许误差记录都有 $R_j=1$，$j\ge N$。反之，对任何色流 $r$，若 $r_j=1$ 对所有 $j\ge N$ 成立，则每条 $\eta\in\mathcal K_\infty(r)$ 都从窗口 $N$ 起全是空窗，因而属于 $D$。

证明。实际空尾给 $x_j(\omega)=0$。由 (28.1)，

$$
a^\star=-11\lambda<-\lambda,
\qquad
b^\star-\lambda=g-4\lambda
=t^2\left(t-\frac25\right)>0.
\tag{29.4}
$$

所以 $[-\lambda,\lambda]\subset(a^\star,b^\star)$。该区间在 $X$ 内，每个允许的零值观察均严格位于颜色一格的内部；裁剪和切点归属都不改变结论。

再考察闭关系候选。定理28.1对 (28.4) 的根像已经核对：$E_1$ 只容纳来源标签 $3,0$。置

$$
L=\min E_1=-\frac65t^2,\qquad f_3(y)=-t-gy.
$$

由于 $f_3$ 严格递减，

$$
\begin{aligned}
\min E_1-\max f_3(E_1)
&=L+t+gL\\
&=t-\frac65(1+g)t^2
=t-\frac{12}{5}g
=\frac{12-19t}{5}
>\frac1{40}>0.
\end{aligned}
\tag{29.5}
$$

这里使用 $1+g=2t$、$t^3=g$ 及 $t<5/8$。若同一候选地址在相邻时刻 $j,j+1$ 的两个坐标都在 $E_1$ 内，当前标签若为 $3$，则当前值属于 $f_3(E_1)$，与 (29.5) 矛盾；故当前标签为 $0$。对完整候选的所有 $j\ge N$ 应用此结论，得到 $T^N\eta=0^\infty$。两个相邻颜色一约束只强制其对应的当前空窗；最终空尾结论使用全部后续约束。$\square$

**推论 29.3（有限来源实际记录在完成域上的单点纤维）。** 对任意 $\omega\in D$ 及其任意实际闭预算完整记录 $r$，都有

$$
\mathcal K_\infty(r)=\{\omega\}.
\tag{29.6}
$$

证明。真实来源满足全部闭关系约束。引理29.2使每条完成域候选都属于 $D$，于是 $\mathcal K_\infty(r)=P_E(r)$，其中右侧为 (28.3) 的有限来源纤维。直接使用定理28.1得到唯一性。该定理已经包含两个端格的非有限极值尾排除，以及最后一个不同窗口所强制的 $y_k=-1+k\phi/5\notin\mathbb Z[t]$、$1\le k\le4$ 的完整环障碍，故这里使用的是闭关系本身的唯一性，含全部端点情形。$\square$

### 29.2 紧致性给出的有限首窗证书

**定理 29.4（安全的自适应停止与按来源的误差一致界）。** 对有限颜色前缀采用如下固定规则：在第一次 $\mathcal L_h(r)$ 为非空单点集时停止，返回其唯一标签；空集或多标签时继续。此规则在每个实际 $\Omega$ 记录上停止时正确，在每个实际 $D$ 记录上有限停止。对每个固定 $\omega\in D$，停止计数在其全部允许误差流上具有一个有限上界。

证明。实际 $\Omega$ 来源始终属于 $\mathcal K_h(r)$，因此其首标签始终在 $\mathcal L_h(r)$ 中。非空单点证书遂正确；空集不构成证书。

对有限来源记录证明终止。无相邻一的单侧地址空间 $\Omega$ 是紧致二元乘积空间的闭子集。每个 $\eta\mapsto x_j(\eta)$ 连续，因为删窗连续，窗口级数一致收敛。闭区间约束使 $\mathcal K_h(r)$ 为紧集，且这些集合随 $h$ 嵌套递减。记真实首标签为 $\ell$，并令

$$
F_\ell=\{\eta\in\Omega:\sigma_0(\eta)\ne\ell\}.
$$

首标签只依赖前三位，所以 $F_\ell$ 为闭开集，特别是紧集。推论29.3给出

$$
\bigcap_{h\ge0}\bigl(\mathcal K_h(r)\cap F_\ell\bigr)=\varnothing.
$$

若每个交集均非空，嵌套紧集的有限交性质就会给出共同元素，矛盾。故某个有限 $h$ 已排除全部错误首标签；真实来源仍在候选中，于是 $\mathcal L_h(r)=\{\ell\}$。规则在至多 $h+1$ 次实际取得后停止。

最后固定 $\omega$，选其一个真实空尾起点 $N$。引理29.2使所有可能完整记录在 $N$ 后都恒为颜色一。它们由长度 $N$ 的有限色词决定，因而只有有限种。对实际可取得的这些记录分别取已经证明存在的停止计数，再取有限最大值，得到只依赖 $\omega$ 的误差一致上界。规则不需要知道 $N$ 或这个最大值。$\square$

这一紧致性论证先给出首窗停止泛函。它的有限状态实现由下述闭区间有限表示给出，不能仅由单点纤维和紧致性推得。

### 29.3 两个代数嵌入限定的有限端点集

继续使用定义14.5的合法 guard 图及平移量。对每条合法边 $s\xrightarrow{\ell}s'$，记

$$
f_\ell(y)=\Delta_\ell-gy,\qquad
F_\ell(x)=\frac{\Delta_\ell-x}{g},\qquad
D_{s,\ell}=f_\ell(I_{s'}).
\tag{29.7}
$$

$D_{s,\ell}$ 是该带 guard 分支的完整闭域。合法边为

$$
0\to0:3,0,2;\qquad 0\to1:5,25;\qquad
1\to0:3,0;\qquad 1\to1:5.
\tag{29.8}
$$

它们的根像和全部端点由命题14.6、定理17.2给出。

**引理 29.5（固定共轭界八的端点闭合）。** 设 $t'=-\phi$ 为 $t$ 的代数共轭，$x'$ 表示 $\mathbb Q(t)$ 中的共轭。定义

$$
\mathscr L=\frac15\mathbb Z[t],\qquad
B=\{x\in\mathscr L\cap X:|x'|\le8\}.
\tag{29.9}
$$

则 $B$ 有限，包含 $I_0,I_1$、全部合法 $D_{s,\ell}$ 及全部 $E_i$ 的端点，并满足

$$
x\in B,\quad F_\ell(x)\in X
\quad\Longrightarrow\quad F_\ell(x)\in B.
\tag{29.10}
$$

证明。代数恒等式为

$$
g'=-\frac1g,\qquad \frac1g=3+2t\in\mathbb Z[t].
\tag{29.11}
$$

每个 $\Delta_\ell$ 在 $\mathbb Z[t]$ 中，故每个删除逆分支 $F_\ell$ 保持格 $\mathscr L$。在共轭嵌入中，

$$
F_\ell(x)'=gx'-g\Delta_\ell'.
\tag{29.12}
$$

由 $t<5/8$ 和 $\phi<2$，有 $0<g<1/4$，且全部标签满足 $|\Delta_\ell'|<4$：五个绝对值依次为 $\phi,0,\phi^2,1,2+\phi$。于是 $x\in B$ 时

$$
|F_\ell(x)'|
\le g\bigl(|x'|+|\Delta_\ell'|\bigr)
<\frac14(8+4)=3<8.
\tag{29.13}
$$

若实嵌入的像还在 $X$ 中，格保持和此界共同给出 (29.10)。

核对全部初始端点。状态区间与合法分支域的端点属于

$$
\{-1,\phi,t,-t^2,g,2t\}\subset\mathbb Z[t]\cap X.
$$

用 $\lambda=t^2/10$ 改写 (28.2)，其内格端点分别来自

$$
\begin{aligned}
E_1&=[-6t^2/5,g-t^2/5],\\
E_2&=[g-2t^2/5,t-2t^2/5],\\
E_3&=[t-3t^2/5,2t-3t^2/5],\\
E_4&=[2t-4t^2/5,2t+t^2/5].
\end{aligned}
\tag{29.14}
$$

因此所有相关端点都在 $\mathscr L\cap X$。其共轭绝对值统一不超过

$$
\max\left\{
\frac65\phi^2,\quad
2\phi+1+\frac25\phi^2,\quad
2\phi+\frac45\phi^2,\quad
1+2\phi
\right\}<8.
\tag{29.15}
$$

这个界包括两端格端点、两个状态区间端点和所有合法分支端点；$\phi<2$ 直接验证右侧严格小于八。故全部初始端点均在 $B$。

最后，若 $x=(m+nt)/5\in B$，则

$$
n=\frac{5(x-x')}{t-t'},\qquad m=5x-nt,
\qquad t-t'=\sqrt5>0.
\tag{29.16}
$$

$|x|\le\phi$ 和 $|x'|\le8$ 同时给两个整数 $m,n$ 有界，只容许有限多个整数对。有限性使用的是两个嵌入的联合界；只说实坐标属于有界区间 $X$ 不足以证明格点有限。$\square$

观察器的端点只需要闭扩张区间、状态区间和分支域的端点；原量化器的切点本身不承担这个格闭合条件。本章统一使用 (29.9) 的共轭界八。

### 29.4 带 guard 的闭覆盖与共同地址提升

**定义 29.6（闭基本片和全包含图）。** 对每个 $s\in\{0,1\}$，将有限集 $B_s=B\cap I_s$ 按实数顺序排列。令 $\mathcal A_s$ 包含每个端点单点集 $\{b\}$，以及 $B_s$ 中每对相邻端点之间的闭区间 $[b,c]$。这些非空紧集构成 $I_s$ 的有限闭覆盖；端点上的重叠被保留。

图节点为 $(s,P)$，其中 $P\in\mathcal A_s$。定义带来源标签的边

$$
(s,P)\xrightarrow{\ell}(s',Q)
\quad\Longleftrightarrow\quad
s\xrightarrow{\ell}s'\text{ 合法},\quad
P\subseteq D_{s,\ell},\quad
Q\subseteq F_\ell(P).
\tag{29.17}
$$

节点与颜色 $i$ 相容的条件是 $P\subseteq E_i$。两个边条件分别要求整个当前片位于合法分支域、整个后继片位于同一个分支像内。

**命题 29.7（规范片、完整像并与端点保留）。** 对 $x\in I_s$，若 $x\in B_s$，取规范片 $\{x\}$；否则取内部含 $x$ 的唯一基本闭区间。任何包含 $x$、且端点属于 $B_s$ 的闭子区间都包含这个规范片。特别地，实际点的规范片保留其全部闭观察约束与合法分支约束。若 $P\subseteq D_{s,\ell}$，则

$$
F_\ell(P)=
\bigcup\{Q\in\mathcal A_{s'}:Q\subseteq F_\ell(P)\}.
\tag{29.18}
$$

证明。单点情形直接成立。非端点 $x$ 所在基本区间的内部没有 $B_s$ 点，故端点在 $B_s$ 的闭子区间不能穿过该基本区间的内部截断它。应用到 $E_i\cap I_s$ 和合法分支域即可；交区间的端点由引理29.5包含在 $B_s$ 中。

$F_\ell(P)$ 是位于 $I_{s'}$ 的单点或闭区间。其端点是 $P$ 的端点在 $F_\ell$ 下的像，因 (29.10) 属于 $B_{s'}$。所有内部基本区间及所有端点单点集恰好覆盖这个像，得到 (29.18)。因此若实际后继值在 $F_\ell(P)$ 中，其规范后继片也整个包含在该像中。只在一个端点发生的约束由对应单点集保留。$\square$

**定理 29.8（有限路径的共同尾提升与无限路径的收缩提升）。** 每条有限图路径可从任意一个终端片内的点及其一条合法终端尾地址，联合提升为同一实际地址的全部所列坐标。每条无限图路径也联合提升为一条实际地址。反过来，每条满足指定闭颜色约束的实际有限或无限历史都具有相应规范片图路径。起始 guard 为零时，所得地址在 $\Omega$ 中。

证明。先取有限路径

$$
(s_0,P_0)\xrightarrow{\ell_0}(s_1,P_1)
\xrightarrow{\ell_1}\cdots
\xrightarrow{\ell_{n-1}}(s_n,P_n).
$$

任选 $x_n\in P_n$，并按定理17.2的状态相对满像关系取一条 $\eta_n\in A_{s_n}$ 编码它。倒向定义

$$
x_j=f_{\ell_j}(x_{j+1}),\qquad j=n-1,\ldots,0.
$$

由 (29.17)，$f_{\ell_j}(P_{j+1})\subseteq P_j$，故全部坐标属于所选片。把合法窗 $\ell_{n-1},\ldots,\ell_0$ 倒向前接到这一条终端尾上，guard 逐步匹配，得到一个共同地址，联合实现全部分支等式和全部节点颜色约束。这允许任意终端点，不为不同节点分别换尾。

再取无限路径。令

$$
H_n=f_{\ell_0}\circ\cdots\circ f_{\ell_{n-1}}(P_n),
\qquad H_0=P_0.
$$

各 $H_n$ 非空紧致，下一条边给 $H_{n+1}\subseteq H_n$，且

$$
\operatorname{diam}(H_n)\le
 g^n\operatorname{diam}(X)\longrightarrow0.
$$

嵌套紧致性与收缩给出唯一共同点。对每个后缀作同一构造得到 $x_j\in P_j$；后缀嵌套集的相容性给 $x_j=f_{\ell_j}(x_{j+1})$。边标签按合法 guard 图拼成一条无限地址。展开任一后缀的前 $n$ 步，余项为 $(-g)^n x_{j+n}$，由有界性趋零，所以这些 $x_j$ 正是该同一地址的窗口级数坐标。闭片保留收缩极限，即使它位于端点；所有 $P_j\subseteq E_{r_j}$ 的约束遂同时成立。

反向取一条实际地址，在每个时刻保留其实际 guard，并选坐标的规范片。命题29.7使当前片整个位于实际分支域内；实际下一坐标在 $F_{\ell_j}(P_j)$ 中，故其规范片整个位于该像内，于是 (29.17) 成立。闭颜色约束同样给规范片与颜色相容。有限路径允许以该实际地址的终端尾延续，无限路径按所有实际窗口延续。$\square$

这里的精确性指图路径与闭扩张关系的共同实现。它不把闭关系替换成每种端点归属下的字面含噪可取得集合。全域和全后继片包含使提升由一个终端尾共同承担；单有两集合相交不能给出上述结论。

### 29.5 保留原首标签的确定有限状态跟踪器

**定义 29.9（首坐标初始化、标签集合更新与停止包装）。** 将图节点附上原始首标签 $\ell\in\Lambda$，并附上阶段标志 $\mathrm{init}$ 或 $\mathrm{ord}$。确定跟踪器的状态是这个有限带标签节点集的子集，另有一个尚未读入任何颜色的起始状态。

读入第一个实际颜色 $r_0$ 时，初始化集合为

$$
V_0(r_0)=
\{((0,P),\ell,\mathrm{init}):
P\subseteq E_{r_0},\quad
0\xrightarrow{\ell}s'\text{ 合法},\quad
P\subseteq D_{0,\ell}\}.
\tag{29.19}
$$

这里的 $s'$ 由合法首窗决定。读入下一实际颜色 $i$ 时，每个初阶段元素只能沿标签恰为其所存 $\ell$ 的图边前进，目的片须整个位于 $E_i$ 内，保留原标签并改为普通阶段。普通阶段元素可沿任意合法图边前进，同样筛选新颜色并保留原首标签。对所有元素取目的集合，即给出确定子集更新；空集也按此规则更新。记读入 $r_0,\ldots,r_h$ 后的集合为 $V_h(r)$，其标签投影为 $\operatorname{Tag}(V_h(r))$。

跟踪器在每个新前缀上继续作这个精确更新。停止包装在首次标签投影为非空单点集时输出该标签，并进入对应吸收输出状态。吸收输出状态收到任意后续颜色仍保持原输出；标签投影为空时不输出。

**定理 29.10（全部有限前缀上的精确标签与有限状态首窗停止）。** 对任意有限色词，包括不可能的实际记录前缀，都有

$$
\operatorname{Tag}(V_h(r))=\mathcal L_h(r).
\tag{29.20}
$$

因此停止包装用有限个内部状态实现定理29.4的同一个停止规则。它在所有实际 $\Omega$ 记录上停止时正确，在所有实际 $D$ 记录上有限停止；结论对任意切点归属同时成立。

证明。初始化时，每个保留的 $((0,P),\ell,\mathrm{init})$ 都有 $P\ne\varnothing$ 且 $P\subseteq D_{0,\ell}$。任选 $x_0\in P$，其 $y=F_\ell(x_0)\in I_{s'}$ 可由定理17.2取合法尾编码；前接 $\ell$ 就给一个首标签为 $\ell$ 的 $\mathcal K_0(r)$ 来源。反向，任一 $\mathcal K_0(r)$ 来源的规范首片同时保留颜色约束与其真实首分支约束，必进入 (29.19)。这证明 $h=0$ 的等式，且首标签由分支域和合法 guard 保留。

对 $h\ge1$，集合更新精确保留全部长度 $h$ 的相容图路径，第一条边的标签必须等于存储的首标签。沿后续边仅保留这个原标签，没有把当前窗口标签改作恢复目标。任一保留路径由定理29.8从一条终端尾联合提升，得到 $\mathcal K_h(r)$ 内具有所存首标签的一条地址，故没有额外标签。反向，任一 $\mathcal K_h(r)$ 地址的规范片路径按同一定理存在，其实际首标签正确初始化，每次新颜色筛选都保留此路径，故没有遗漏标签。于是 (29.20) 对全部前缀成立。

图节点、标签和阶段标志构成有限集，其全部子集也构成有限集；加入起始状态及各标签吸收输出状态后仍有限。定理29.4的安全性和终止性遂直接适用。整个跟踪和停止只读取新近实际取得的颜色，不以自行生成的未来颜色更新候选。$\square$

(29.20) 属于持续更新的候选跟踪器，吸收输出属于停止包装。某个已产生单点证书的前缀如果随后接上不可能的颜色，持续跟踪器的候选可以变空；包装仍保留此前输出。这不撤回任何实际记录上的正确输出，因为实际来源始终保留在闭候选集中，不能发生这种实际候选消失。有限状态存在性在这里由固定有限集合和关系给出；没有列举端点、生成转移表、计算状态数或声称最小存储。

### 29.6 实际空尾之后的统一追加取得界

**定理 29.11（颜色一停止盆中的有限追加等待）。** 对上述固定吸收停止包装，存在有限整数 $K$，使对每条实际 $\omega\in D$、每个允许误差流及每个满足 $T^N\omega=0^\infty$ 的 $N\ge0$，其停止计数均满足

$$
T_{\mathrm{stop}}\le N+K.
\tag{29.21}
$$

$K$ 只依赖固定有限状态观察器，不依赖来源、支持、误差或 $N$。

证明。令 $S$ 为停止包装的有限状态集，$H$ 为其吸收输出状态集，$\delta_1:S\to S$ 为读入颜色一的转移。设 $q_n$ 是取得前 $n$ 个颜色后的状态，$q_0$ 为起始状态；停止计数是首次 $q_n\in H$ 的 $n$。即使已经停止，数学上也用吸收转移定义其后状态。

定义仅针对恒定输入一的停止盆

$$
U=\{q\in S:\delta_1^k(q)\in H\text{ 对某个有限 }k\ge0\},
$$

并对 $q\in U$ 定义

$$
\tau(q)=\min\{k\ge0:\delta_1^k(q)\in H\},
\qquad K=\max_{q\in U}\tau(q).
\tag{29.22}
$$

$H\subseteq U$，故 $U$ 非空；$U$ 有限，且每个 $\tau(q)$ 由定义有限，因此 $K$ 是有限整数。这没有假定 $S$ 中每个状态在 $1^\infty$ 输入下都停止；盆外状态可以不停止。

对给定实际运行，引理29.2保证 $R_j=1$，$j\ge N$。若 $T_{\mathrm{stop}}\le N$，则 $q_N\in H$，结论直接成立。否则

$$
q_{N+k}=\delta_1^k(q_N),\qquad k\ge0.
$$

定理29.10已经证明该实际 $D$ 运行最终停止，故 $q_N\in U$，于是

$$
T_{\mathrm{stop}}=N+\tau(q_N)\le N+K.
$$

早期不同的允许误差只决定进入盆中的哪个状态，均受同一最大值约束。$\square$

这是一个实际观察数量界，没有计算 $K$。观察器既不接收也不认证 $N$；在数学保证中知道实际空尾起点，与仪器从有限颜色中检测这个起点是不同任务。

**命题 29.12（无统一初始视界与有限状态停止相容）。** 首窗安全恢复的停止计数在 $D$ 的允许实际记录上没有统一有限上界，即使误差都严格小于 $\lambda$。

证明。对任意固定 $h\ge0$，直接使用命题27.6：同一临界布局有两条首标签不同的实际 $D$ 来源，在严格误差下产生同一长度 $h+1$ 前缀。各自以后取零误差即可延续为允许完整记录。任何只根据已取得颜色确定动作的安全规则，都不能在这个共同前缀或其更短前缀上返回首标签，否则对两条来源返回同一标签，至少一条错误。由于 $h$ 任意，不存在统一初始视界。来源对可以随 $h$ 改变，故此障碍不否定逐条记录的有限停止，也不否定实际空尾之后的 (29.21)。$\square$

### 29.7 空窗首标签、支持认证和 End 的区别

**命题 29.13（延迟非零窗保留任意有限全一前缀）。** 零来源 $0^\infty$ 的任何有限全一颜色前缀，都与一个非零有限来源在同一仪器下的零误差记录相容；该非零窗可以晚于任意指定的有限位置。因此这种前缀不能认证完整来源为零、已经发生 End，或其全部相容有限来源的任何有限支持上界。在所有 $D$ 实际记录上安全的完整地址输出规则，不能在零来源的全一记录上有限停止。

证明。固定已取得视界 $h\ge0$ 及任意有限位置界 $B_0$。由 (29.4)，

$$
\rho=\min\{-a^\star,b^\star\}>0.
$$

取整数 $M>\max\{h,B_0,0\}$ 足够大，使 $t^2g^{M-h}<\rho$。定义合法有限来源

$$
\omega_M=0^M5\,0^\infty.
\tag{29.23}
$$

首 $M$ 个窗口为空；标签 $5$ 后的 guard 一允许空窗接回 guard 零，故此地址合法。对 $0\le j\le h$，窗口级数给

$$
x_j(\omega_M)=t^2(-g)^{M-j},\qquad
|x_j(\omega_M)|\le t^2g^{M-h}<\rho.
\tag{29.24}
$$

全部这些真实坐标严格位于 $(a^\star,b^\star)$ 内，所以零误差、不改变坐标的裁剪以及任意切点归属都给颜色一。零来源的每次允许观察也都是颜色一，故两条来源共享这个有限前缀；然而 $\omega_M$ 的非零窗在 $M>B_0,h$，其实际空尾只从 $M+1$ 开始。

若从此有限前缀认证 End 已发生或给一个对全部相容来源有效的有限支持上界，再取晚于该界的 $M$ 就矛盾。若完整地址规则在零来源全一记录的某个有限前缀上停止，其同一输出也会用于这个不同的实际 $\omega_M$ 记录，故不能同时安全。这个结论针对零来源记录上的完整地址停止，不断言每条其他记录都不能恢复完整地址。$\square$

有限状态首窗观察器可以在零来源上停止，并在共享该停止前缀的延迟非零来源上给出相同的空窗首标签；两者首窗均为 $0$，所以输出正确。首窗输出并不宣布后续窗口都为空。固定有限内部记忆、无统一初始等待界、实际空尾后的统一追加等待界和完整来源或 End 认证，遂具有各自的精确量词与结论。

本章使用已发表在本卷的闭分支满像、临界闭扩张区间、有限来源最后差异唯一性及有限视界碰撞；新增连接由最终颜色一约束、紧致错误首标签排除、双嵌入有限端点覆盖、共同地址路径提升和有限停止盆给出。这些是普通纸面数学证明，采用经典紧致性、收缩和有限集合论；本章没有形式内核核验或实验数据。有限状态结果只承担此固定首窗任务，不给出端点或状态计数、生成表、最优记忆、全部流式重建的总有限记忆、来源擦除、物理时空起源或热力学时间箭头。

## 追加锚（29·本行以下为增补区）

## 30. 完整逐窗流式恢复的有限状态障碍与增长历史构造

本章把响应目标从原始首窗改为全部窗口的有序流式恢复。固定第28.1节的临界六格布局 (28.1)，以及第29章的同一实际来源合同。置

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad \lambda=\frac{t^2}{10},\qquad
X=I_0=[-1,\phi],\quad I_1=[-1,t].
$$

量化器 $Q:X\to\mathcal C$ 在所有时刻相同，颜色字母表为 $\mathcal C=\{0,1,2,3,4,5\}$，其切点为

$$
a^\star=-t^2-\lambda,\quad b^\star=g-3\lambda,\quad
c^\star=t-5\lambda,\quad d^\star=2t-7\lambda,\quad
e^\star=2t+\lambda.
\tag{30.1}
$$

五个切点各取任意固定合法归属。来源窗口字母表为 $\Lambda=\{3,0,5,2,25\}$，其中 $0=\mathrm{null}$，$25$ 是一个窗口标签。$\Omega$ 为起始 guard 零的完整合法地址空间，$D\subset\Omega$ 为最终全是空窗的来源域。地址、guard 和颜色分别保留。一条实际来源承担全部观察坐标：

$$
x_j(\omega)=\kappa_0(T^j\omega),\qquad
r_j=Q\!\left(\operatorname{clip}_X(x_j(\omega)+\varepsilon_j)\right),
\qquad |\varepsilon_j|\le\lambda,\quad j\ge0.
\tag{30.2}
$$

误差在裁剪前逐坐标分别受限。下述障碍使用严格小于 $\lambda$ 的完整实际误差流，恢复构造则安全地覆盖全部闭预算记录。本章只使用命题28.3的周期地址和内部目标、推论29.3的完成域单点纤维，以及定义29.6、命题29.7和定理29.8的精确有限图；不重复它们的完整证明。

### 30.1 有序输出与全部可读保留信息

**定义 30.1（完整逐窗输出合同与有限状态）。** 确定因果规则从固定初始状态出发，每取得一个颜色，输出一个有限窗口词，允许空词；各批按取得顺序连接，已经输出的标签不撤回、不重排。允许固定的初始输出。对每个 $\omega\in D$ 的每条实际允许记录，要求全部有限时刻的累计输出都是 $\omega$ 的窗口前缀，并要求每个位置 $j\ge0$ 的窗口最终在有限次取得后输出。无限空窗补齐属于所需输出，不另要求 End 或识别最后一个非空窗。

有限状态实现指存在有限集 $S$、初始状态 $q_0$，以及固定映射

$$
\delta:S\times\mathcal C\to S,\qquad
o:S\times\mathcal C\to\Lambda^\ast,
\tag{30.3}
$$

其中 $\Lambda^\ast$ 表示有限窗口词；每次新颜色只通过当前状态决定转移和本批输出。凡能被后续动作读取的信息都计入状态，包括位置计数、时钟、保留历史和可回读输出。只写且不可回读的输出由上述合同处理；可回读输出不能作为未计价的外部记忆。规则也可以只在可延伸为实际记录的历史上给定，下面使用的每条历史都有实际 $D$ 延伸。

这里不限定等待时长，不限定每批输出长度，也不要求所有位置具有共同的取得延迟界。有限状态限制的是全部保留信息的可能取值，不是单步输出的长度或任务是否给 End。

### 30.2 实际有限来源迫使周期前缀字面静默

沿用命题28.3，记

$$
P=(3,3,5,0,3,0),\qquad
\omega^-=P^\infty,\qquad \omega^+=T^3\omega^-,
$$

$$
\rho=(1,0,2)^\infty=W^\infty,\qquad W=(1,0,2,1,0,2),\qquad
r_{\mathrm{per}}=\frac{44g-5}{152}<\lambda.
\tag{30.4}
$$

为避免与颜色记录 $r$ 混淆，将 (28.8) 的共同误差上界写为 $r_{\mathrm{per}}$。两条地址的首窗分别为 $3$ 与 $0$。记 (28.15) 的周期六目标为 $u_j^-$，其向前三位移位为 $u_j^+$；命题28.3已经证明

$$
|u_j^\pm-x_j(\omega^\pm)|\le r_{\mathrm{per}},
\qquad Q(u_j^\pm)=\rho_j,
\tag{30.5}
$$

且全部目标在 $X$ 中并严格位于相应颜色格内部。$P$ 中每个 $5$ 后接允许 incoming guard 一的 $0$，接缝及移位接缝均合法；这些是实际周期地址，不是分别选择的坐标。

**引理 30.2（保留有限目标的截断与强制静默）。** 对定义30.1的有序因果输出规则，只要它在 $D$ 的全部实际严格预算 $|\varepsilon_j|<\lambda$ 记录上正确，在每个有限前缀 $\rho|_H$ 上，累计输出都恰为空词；特别地，每个 $W^k$ 上均没有输出。该结论不要求规则在 $\Omega\setminus D$ 上正确。

证明。对任意合法地址 $\eta$，保留前 $N$ 个窗口并后接 $0^\infty$，记为 $\eta^{[N]}$。两个 outgoing guard 都允许空窗接入，故此截断合法且属于 $D$；$N\ge1$ 时保留首标签。由相同的窗口级数平移量和分支斜率 $-g$，有精确尾项等式

$$
x_j(\eta)-x_j(\eta^{[N]})
=(-g)^{N-j}x_N(\eta),\qquad 0\le j<N.
\tag{30.6}
$$

截断地址在 $N$ 时刻的尾坐标为零，原尾坐标在 $X$ 中，因而

$$
|x_j(\eta)-x_j(\eta^{[N]})|
\le\phi g^{N-j}.
\tag{30.7}
$$

这是第27.1节有限目标转移所用截断的同一来源尾项表达式。

固定任意取得长度 $H\ge0$，取整数 $N>H$ 足够大，使

$$
\phi g^{N-H}<\lambda-r_{\mathrm{per}}.
\tag{30.8}
$$

分别截断 $\omega^-$ 和 $\omega^+$，得到首标签仍为 $3$ 和 $0$ 的两条实际 $D$ 来源。对 $0\le j<H$，在对应截断来源上取误差
$\varepsilon_j^\pm=u_j^\pm-x_j((\omega^\pm)^{[N]})$。由 (30.5)、(30.7) 和 (30.8)，

$$
|\varepsilon_j^\pm|
\le r_{\mathrm{per}}+\phi g^{N-H}<\lambda.
\tag{30.9}
$$

目标恰为原来的 $u_j^\pm\in X$，裁剪固定这些目标，内部颜色不依赖切点归属。因此这两条有限来源同时实现指定的全部 $H$ 个颜色 $\rho|_H$。对每条来源从时刻 $H$ 起全部取零误差，即延伸为完整实际允许记录；没有把周期无限地址替代为有限来源，也没有为不同观察坐标另换来源。

因果性使共同前缀上的累计输出相同。若非空，其第一个标签就必须同时为 $3$ 和 $0$，与正确性矛盾。因此累计输出为空；$H=0$ 也迫使固定初始输出为空。由于输出只追加，各批不能通过后续取消而得到空词，这就是每个此类前缀上的字面静默。整个论证只在两条实际 $D$ 延伸上使用正确性。$\square$

### 30.3 一个固定实际后缀与有限状态障碍

**命题 30.3（共同完整后缀的实际有限来源族）。** 固定整数 $m\ge1$ 满足

$$
\phi g^{6m}<\lambda-r_{\mathrm{per}}.
\tag{30.10}
$$

令 $\tau=P^m0^\infty\in D$，并令 $V$ 为这一条来源在固定 $Q$ 下的完整零误差记录：

$$
V_j=Q(x_j(\tau)),\qquad j\ge0.
\tag{30.11}
$$

则对每个整数 $k\ge0$，来源 $\zeta_k=P^{k+m}0^\infty\in D$ 都有一条完整实际记录恰为 $W^kV$，其全部裁剪前误差严格小于 $\lambda$。$m,\tau,V$ 不随 $k$ 改变。

证明。$0<g<1$ 和 $\lambda-r_{\mathrm{per}}>0$ 保证这样的 $m$ 存在。$P$ 的周期接缝合法，末窗为 $0$，所以 $\tau$ 和全部 $\zeta_k$ 合法。$\zeta_k$ 正是 $\omega^-$ 在 $6(k+m)$ 个窗口后的空尾截断。对 $0\le j<6k$，取误差使目标恰为 $u_j^-$，则

$$
\begin{aligned}
|u_j^--x_j(\zeta_k)|
&\le r_{\mathrm{per}}+\phi g^{6(k+m)-j}\\
&\le r_{\mathrm{per}}+\phi g^{6m}<\lambda.
\end{aligned}
\tag{30.12}
$$

这些目标全在相应格的严格内部，给出 $W^k$，不受裁剪或切点归属影响。对 $j\ge6k$ 全部取零误差；精确地址等式

$$
T^{6k}\zeta_k=\tau
\tag{30.13}
$$

使后续全部真实坐标和颜色恰为 (30.11) 的同一个 $V$。这是同一实际来源的完整误差流，不是各边缘约束的拼接。$k=0$ 时前缀为空，整条记录就是 $V$。$j\ge6m$ 时 $x_j(\tau)=0$，而 $a^\star<0<b^\star$，故 $V_j=1$。$V$ 中其余零误差坐标若落在切点上，也由同一个固定归属决定；因所有运行的后缀来源都是 $\tau$，该归属仍给共同后缀。$\square$

**定理 30.4（完整有序流式恢复不能使用固定有限状态）。** 对临界布局 (30.1) 的每种固定合法切点归属，不存在满足定义30.1完整逐窗合同的确定有限状态实现。即使只要求对严格误差记录正确，也有此障碍；它不使用 End、统一延迟或每批长度界。

证明。设存在有限状态实现，令 $q_k$ 为读完 $W^k$ 后的全部保留状态。引理30.2使所有这些历史的早先输出都为空。有限性给出 $k<\ell$ 满足 $q_k=q_\ell$。在两次运行之后接上命题30.3的同一个完整实际后缀 $V$，确定性就给出相同的未来转移和输出批次。早先输出均为空，因此两条完整记录 $W^kV$ 和 $W^\ell V$ 的总输出流相同。

两条所需来源却在有限窗口位置 $6(k+m)$ 不同：

$$
\sigma_{6(k+m)}(\zeta_k)=0,\qquad
\sigma_{6(k+m)}(\zeta_\ell)=3.
\tag{30.14}
$$

前者已经进入空尾，后者还有下一份 $P$。每个位置最终输出的要求使这一有限位置在两次运行中都必须被输出；相同的输出流不能同时给出两个不同标签，矛盾。全部记录和误差由命题30.3实际实现，故没有使用对周期无限来源的正确性。$\square$

这个证明还说明：对任何正确的确定规则，静默前缀 $W^k$ 后的保留状态必须在共同后缀 $V$ 下具有两两不同的未来输出行为。它给出不可压入一个固定有限状态集的区分要求，不给出最优状态数、随取得长度变化的尖锐记忆率或其他布局的同类障碍。

### 30.4 每个有限窗口前缀都有持续证书

**定义 30.5（已取得历史的共同候选与前缀集）。** 令 $E_i$ 为 (28.2) 的闭扩张区间，等价地，

$$
E_i=\{x\in X:\operatorname{dist}(x,\overline{C_i})\le\lambda\},
$$

其中 $C_i=Q^{-1}(i)$ 保留实际归属。对已取得 $n\ge0$ 个颜色的历史 $r|_n$，定义

$$
F_n(r)=\{\eta\in\Omega:x_j(\eta)\in E_{r_j}\text{ 对 }0\le j<n\},
\qquad F_0(r)=\Omega,
\tag{30.15}
$$

以及对 $L\ge0$ 的有限窗口前缀集

$$
\mathcal P_{n,L}(r)=\{\eta|_L:\eta\in F_n(r)\}.
\tag{30.16}
$$

$\eta|_L=(\sigma_0(\eta),\ldots,\sigma_{L-1}(\eta))$；$L=0$ 时是空词。这里的所有约束都作用于同一条 $\eta$。$F_n$ 是闭关系候选，不把扩张端点宣称为任意归属下可实际取得的目标；只有真实记录到该闭关系的必要包含被使用。

**定理 30.6（有限前缀的持续认证）。** 对每条实际 $\omega\in D$ 的每个允许完整记录 $r$，以及每个有限 $L\ge0$，存在有限取得长度 $H_L$，使

$$
\mathcal P_{n,L}(r)=\{\omega|_L\}
\qquad\text{对全部 }n\ge H_L.
\tag{30.17}
$$

证明。裁剪不增加到真实 $x_j(\omega)\in X$ 的距离，实际目标属于 $C_{r_j}\subseteq\overline{C_{r_j}}$，故 $\omega\in F_n(r)$ 对每个 $n$ 成立。此包含对实际 $\Omega$ 来源也成立。$\Omega$ 紧致，坐标映射连续，$E_i$ 闭，因而 $F_n(r)$ 是嵌套非空紧集。对 $n\ge1$，它就是定义29.1的 $\mathcal K_{n-1}(r)$；推论29.3给出

$$
\bigcap_{n\ge0}F_n(r)=\{\omega\}.
\tag{30.18}
$$

固定 $L\ge1$，长度 $L$ 的真前缀柱集
$Z_L=\{\eta\in\Omega:\eta|_L=\omega|_L\}$ 是闭开集。嵌套紧集
$F_n(r)\cap(\Omega\setminus Z_L)$ 的交由 (30.18) 为空。若每个这样的有限阶段集合都非空，紧致有限交性质就给共同元素，矛盾。因此某个有限 $H_L$ 已使此集合为空。后续候选只缩小，而真实来源始终在内，得到 (30.17)。$L=0$ 时取 $H_0=0$。$\square$

量词为“每条实际 $D$ 记录、每个有限 $L$、存在一个有限 $H_L$”。证书对后续取得持续有效，但不同 $L$ 的 $H_L$ 可以不同；没有把所有位置同时认证所需的取得长度换成一个有限数。候选域使用紧致的 $\Omega$，其全记录纤维由推论29.3在实际 $D$ 记录上成为单点；仅在非紧的 $D$ 中写唯一性不能替代这一论证。

### 30.5 精确有限图的任意前缀测试与有效准备

继续使用定义29.6的同一固定图 $G$。为避免将图中的后继片与量化器 $Q$ 混淆，节点写为 $(s,A)$，其中 $A\in\mathcal A_s$；$\mathcal A_s$ 含相邻端点间的整个闭区间及所有端点单点集。起始节点为 guard 零的全部节点。合法边和颜色容许关系原样为

$$
(s,A)\xrightarrow{\ell}(s',A')
\quad\Longleftrightarrow\quad
s\xrightarrow{\ell}s'\text{ 合法},\quad
A\subseteq D_{s,\ell},\quad A'\subseteq F_\ell(A),
\tag{30.19}
$$

$$
(s,A)\text{ 容许颜色 }i
\quad\Longleftrightarrow\quad A\subseteq E_i.
$$

这里 $F_\ell$ 是 (29.7) 的分支映射，与带取得下标的候选集 $F_n(r)$ 不同。两个边条件都是全片包含，不能改成相交；端点单点也保留。定理29.8保证每条有限起始路径从一个合法终端尾联合提升为一条实际 $\Omega$ 地址，也保证每条满足指定闭约束的实际地址有其规范片路径。

**命题 30.7（取得 $n$ 个颜色、请求 $L$ 个窗口的精确有限测试）。** 给定任意有限色词 $r|_n$ 和 $L\ge0$，取

$$
M=\max\{0,n-1,L\}.
\tag{30.20}
$$

考虑 $G$ 中具有 $M$ 条边的全部起始路径，节点编号为 $0,\ldots,M$。仅对 $j<n$ 的节点施加已经取得的颜色 $r_j$，不对任何 $j\ge n$ 的节点施加颜色约束。其前 $L$ 条边的标签词集合恰为 $\mathcal P_{n,L}(r)$。同一等式对任意更大的有限边数也成立。

证明。任意 $\eta\in F_n(r)$ 的规范片路径具有所需的全部已取得约束，其前 $L$ 条边标签恰为 $\eta|_L$，故没有遗漏。反向，任一保留路径按定理29.8从其终端片的一个点及一条合法终端尾提升。得到的一个共同实际地址同时实现所有所列节点、观察约束和边标签，属于 $F_n(r)$，且前 $L$ 个窗口恰为所存词，故没有额外候选。$M\ge n-1$ 使最后已取得颜色有对应节点，$M\ge L$ 使最后请求窗口有对应边；特别地，$L>n$ 时请求的后续标签仍由路径和合法尾承担，但没有假定尚未取得的颜色。更大的有限路径用相同双向论证即可。$\square$

一个显式有限递推实现此集合测试。记 $\epsilon$ 为空词，初始化

$$
U_0=\{((0,A),\epsilon):A\in\mathcal A_0,\quad
n=0\text{ 或 }A\subseteq E_{r_0}\}.
\tag{30.21}
$$

对 $0\le j<M$，由每个 $(v,p)\in U_j$ 及每条边 $v\xrightarrow{\ell}v'$ 形成 $(v',p')$，其中

$$
p'=
\begin{cases}
p\ell,&j<L,\\
p,&j\ge L.
\end{cases}
\tag{30.22}
$$

仅在 $j+1<n$ 时要求 $v'$ 容许 $r_{j+1}$，否则不加颜色条件；对所得对取集合，得到 $U_{j+1}$。$U_M$ 的词投影就是 (30.16)。每个阶段只含有限节点及长度 $\min\{j,L\}$ 的有限词，阶段数也有限，因此可以判定空集、单词和多词并在单词时返回它。$n=0$ 时没有颜色测试，$L=0$ 时只测试共同候选是否非空；没有要求判定任何无限路径性质。词长可增长，不能由图节点有限推出这一整族测试使用固定有限状态。

**命题 30.8（固定图及测试的有限代数有效性）。** $G$ 可以由有限的精确代数准备给定，命题30.7的每个有限实例随后具有可终止的精确计算；这不需要未知的无限记录判定器。

证明。引理29.5固定端点集

$$
B=\{x\in\tfrac15\mathbb Z[t]\cap X:|x'|\le8\},
\qquad t'=-\phi.
$$

若 $x=(u+vt)/5$，则 (29.16) 的两个嵌入界给

$$
|v|\le\frac{5(\phi+8)}{\sqrt5},
\qquad |u|\le5\phi+t|v|.
\tag{30.23}
$$

因此整数系数 $u,v$ 落在一个可给定的有限范围；成员条件、端点排序及全部包含测试都归结为 $\mathbb Q(t)$ 的精确比较。对此二次域，先用 $t^2+t-1=0$ 化为 $p+qt$，$p,q\in\mathbb Q$；等号由 $t$ 无理性精确判定。非零表达式的符号可由该多项式正根的有理隔离区间逐次细化判定，非零性保证有限终止。合法 guard 边已经由 (29.8) 固定。由此可有限筛选 $B$、形成基本闭片并判定 (30.19) 及颜色容许关系，随后使用有限递推 (30.21)—(30.22)。

这说明有限准备和各阶段测试的有效性，不给出端点、路径或状态的枚举表，也不声称执行过生成、计数或实验。引理29.5的端点闭合和命题29.7的全像覆盖已经负责图的数学正确性；这里仅说明其精确代数数据具有有限取得方法。$\square$

### 30.6 增长历史、每次至多一个标签的恢复规则

**定义 30.9（增长有限历史的逐窗规则）。** 规则保留全部已取得有限色词 $r|_n$ 和已输出窗口数 $k$，初始 $n=k=0$，初始输出为空。每次取得新颜色后，令 $n$ 增一，对当前历史只作一次测试 $\mathcal P_{n,k+1}(r)$：

若它为非空单词集 $\{p\}$，输出 $p$ 的最后一个窗口标签，并令 $k$ 增一；若为空集或含多个词，则不输出且 $k$ 不变。每次只输出至多一个窗口，不在同一次取得后继续追赶其他位置。

测试由命题30.7的有限递推给出，固定图的准备由命题30.8给出。规则只使用已经取得的有限历史，$n$ 是其长度，且始终 $k\le n$。$k$ 是实际保留的位置信息，不能当作状态之外的免费计数器。前次测试的临时标签集合可在本次计算结束后丢弃，下一步从有限历史重新计算；不需要回读已经写出的标签。空候选明确拒绝认证，在实际合同内则真实来源保证候选永不为空。

**定理 30.10（完成域安全与有限来源逐位置最终输出）。** 定义30.9给出一个固定的有效确定因果规则，每次取得仅作有限计算并输出至多一个窗口。对每条实际 $\Omega$ 闭预算记录，所有输出都是其真实来源的有序前缀；对每条实际 $D$ 闭预算记录，每个窗口位置最终都在有限次取得后输出，包括全部无限空窗补齐。

证明。先证安全。设 $\omega\in\Omega$ 产生实际记录 $r$，则 $\omega\in F_n(r)$ 对每个 $n$ 成立。当当前测试为 $\{p\}$ 时，必有

$$
p=\omega|_{k+1}.
\tag{30.24}
$$

初始输出为空。若已输出 $k$ 个正确窗口，(30.24) 的最后标签正是位置 $k$ 的真实窗口；追加它就给前 $k+1$ 个正确窗口。这一归纳对全部实际 $\Omega$ 记录成立。各阶段的单词证书包含同一真实来源，所以不会用彼此不相容的来源前缀拼接输出。安全性不要求 $\omega$ 最终为空尾，也不要求在 $\Omega\setminus D$ 上持续进展。

再证 $D$ 上的逐位置最终输出。固定 $\omega\in D$ 的任一实际记录 $r$，令 $\tau_L$ 为第 $L$ 个输出标签产生时已经取得的颜色数，置 $\tau_0=0$。对 $L\ge1$，假设前 $L-1$ 个窗口已在有限取得长度 $\tau_{L-1}$ 后输出。取定理30.6的 $H_L$，并令

$$
n_L=\max\{H_L,\tau_{L-1}+1\}.
\tag{30.25}
$$

如果在第 $n_L$ 次取得的决策之前已经输出至少 $L$ 个窗口，则结论成立。否则，由 $n_L-1\ge\tau_{L-1}$，此时恰有 $L-1$ 个输出，故当前请求长度 $k+1=L$。定理30.6的持续证书使此次测试恰为 $\{\omega|_L\}$，于是输出位置 $L-1$。因此实际输出时刻满足

$$
\tau_L\le\max\{H_L,\tau_{L-1}+1\}<\infty.
\tag{30.26}
$$

由 $L$ 归纳，每个有限位置都被输出，空尾中的任意有限位置也在此范围内。规则不需要知道 $H_L$、$\tau_{L-1}$ 的未来值或空尾起点；这些仅用于证明实际运行的进展。因果性和每步有限计算来自定义30.9及命题30.7—30.8，全部决策都只在已取得的有限数据上进行。$\square$

(30.26) 是逐条记录、逐个有限输出长度的定性保证。它不赋予每次实际颜色到达之间一个固定处理时间，不给统一延迟、吞吐量或内存效率。全部取得历史及输出计数都是增长的保留信息；有限阶段的临时计算虽有限，其大小也没有全局固定界。

### 30.7 首窗响应与完整回应的不同保留义务

定理29.10的首窗观察器仍然正确：它只需在有限带首标签节点的子集上跟踪，并在认证一个标签后进入吸收输出状态。完整有序输出改变了必须保留的区别。引理30.2中的静默前缀还没有给任何窗口答案，命题30.3的同一个实际后缀随后要求恢复不同长度的完整来源。因而这些前缀在未来回应上不能合并为同一状态。首窗已经认证后不再需要的区别，在完整回应合同中仍可能承担后续窗口的位置和标签。

定理30.10采用另一种保留方式：保留增长的已取得历史，按需测试越来越长的来源前缀。每个阶段的数据和计算都是有限的，固定候选图也有限；所有阶段合起来允许的历史、请求词长和位置计数却不落在一个固定有限集内。这正是它与定理30.4相容的原因。任何可读时钟、历史重放或输出存储若承担这些区别，都属于保留状态。

逐位置最终输出也不等于有限时刻的完整来源答复。命题29.13已经证明，零来源的任意有限全一记录不能认证以后再无非空窗，也不能给出对全部相容有限来源有效的支持上界。对每个预定有限空窗前缀得到证书，与在一次有限取得后宣布全部剩余窗口都为空，是不同的量词；本章规则持续取得和输出，不发 End，也不从有限前缀推出完整来源停止。

本章将固定临界六格下的实际有限来源障碍与增长历史的互补构造集中为同一附录，所需周期坐标、闭纤维和共同地址图提升直接引用第28—29章。结论属于普通纸面数学，使用精确代数、紧致性、有限集合递推和归纳；没有形式内核核验或实验数据。范围限于同一个临界平稳布局、任意固定合法切点归属和逐坐标闭预算 $\lambda$。它不提供最优状态数、尖锐记忆率、其他布局的统一流式障碍、完整来源有限停止、物理时空起源或热力学时间箭头。

## 追加锚（30·本行以下为增补区）

## 31. 端点属于 $\mathbb Q(t)$ 的闭观察与有限全路径图

第29章的临界闭扩张区间具有有限共同地址图，第30章用该图测试越来越长的来源前缀。本章给出这种有限表示的端点条件：有限个闭观察区间的端点属于 $\mathbb Q(t)$ 时，同一带 guard 的闭覆盖构造仍然成立；反方向，在接受全部无限路径、平移量属于这个域的有限图中，标量极值也属于这个域。因此，对完成域上的非空闭根区间，其完整来源原像具有指定的有限全路径表示，当且仅当两个有效端点属于 $\mathbb Q(t)$。这个充要结论只约束根时刻，未来观察不受限。

### 31.1 来源合同、系数域与闭成员关系

**定义 31.1（有限闭观察的共同来源合同）。** 沿用定义14.5、定理17.2与 (29.7)—(29.8) 的地址、编码和 incoming guard。置

$$
\mathbb F=\mathbb Q(t)=\mathbb Q(\sqrt5),\qquad
t=\frac{\sqrt5-1}{2},\quad \phi=1+t,\quad g=t^3=2t-1,
\qquad I_0=X=[-1,\phi],\quad I_1=[-1,t].
\tag{31.1}
$$

$\mathbb F$ 只表示系数域，不表示本卷已有的联合完成域 $K=\Omega\times G$。$A_0=\Omega$、$A_1=\{\omega\in\Omega:\omega_0=0\}$ 始终表示来源地址域，不用来命名闭覆盖。窗口标签为 $\Lambda=\{3,0,5,2,25\}$，其中 $0=\mathrm{null}$，$25$ 是一个三位窗口标签。合法边及其仿射数据为

$$
\begin{gathered}
0\to0:3,0,2;\qquad 0\to1:5,25;\qquad
1\to0:3,0;\qquad 1\to1:5,\\
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t),\\
f_\ell(y)=\Delta_\ell-gy,\qquad
F_\ell(x)=\frac{\Delta_\ell-x}{g},\qquad
D_{s,\ell}=f_\ell(I_{s'})\quad
\text{当 }s\xrightarrow{\ell}s'\text{ 合法}.
\end{gathered}
\tag{31.2}
$$

给定有限族 $E_1,\ldots,E_r$，每个成员为端点在 $\mathbb F$ 中的闭区间，或为空集；允许单点区间。只使用其有效部分 $\bar E_i=E_i\cap X$。非空有效部分仍为端点在 $\mathbb F$ 中的闭区间。对一个初始 guard $s_0$ 和一条地址 $\omega\in A_{s_0}$，记其实际窗口、后续 guard 和坐标为

$$
\ell_j=\sigma_j(\omega),\qquad
s_j\xrightarrow{\ell_j}s_{j+1},\qquad
x_j=\kappa_{s_j}(T^j\omega).
\tag{31.3}
$$

两个状态的编码使用同一个窗口级数；在 $T^j\omega\in A_{s_j}$ 上，$x_j$ 也等于 $\kappa_0(T^j\omega)$。给每个指定时刻一个指标集 $H_j\subseteq\{1,\ldots,r\}$，所要求的正成员关系是

$$
x_j\in\bar E_i\qquad(i\in H_j).
\tag{31.4}
$$

$H_j=\varnothing$ 表示此时没有观察约束，不表示这些区间的成员位全为零。时刻可以只取一个有限前缀，也可以取全部非负整数；同一时刻允许多个闭约束。区间之间允许重叠。所有窗口、guard 和观察坐标必须来自 (31.3) 的同一条实际地址，不能为各坐标分别选择来源。

本章直接使用定理17.2的状态相对满像 $\kappa_s(A_s)=I_s$、合法前接等式和完整端点尾。命题14.8所示同标量、不同实际后继仍被保留；这里没有把标量观察替换为全空间上的单值自主删除映射。

### 31.2 公分母格与共轭闭合

**引理 31.2（有限 $\mathbb F$ 端点族的有界闭合集）。** 令 $C$ 为全部非空 $\bar E_i$ 的端点、两个状态区间端点和所有合法分支域端点的并。存在整数 $q\ge1$ 及实数 $R\ge0$，使

$$
\mathscr L_q=q^{-1}\mathbb Z[t],\qquad
B=\{x\in\mathscr L_q\cap X:|x'|\le R\}
\tag{31.5}
$$

是包含 $C$ 的有限集，并满足

$$
x\in B,\quad F_\ell(x)\in X
\quad\Longrightarrow\quad F_\ell(x)\in B.
\tag{31.6}
$$

这里 $t'=-\phi$，撇号为 $\mathbb F$ 的非平凡共轭嵌入。

证明。$\mathbb F$ 中每个数都唯一写成 $a+bt$，$a,b\in\mathbb Q$。$C$ 有限，故对这些有理系数取公分母即可得到 $C\subseteq\mathscr L_q$。状态端点和分支端点本来就在 $\mathbb Z[t]$ 中。沿用 (29.11)—(29.12) 的代数单位和共轭恒等式，

$$
g^{-1}=3+2t\in\mathbb Z[t],\qquad
g'=-g^{-1},\qquad
F_\ell(x)'=gx'-g\Delta_\ell'.
\tag{31.7}
$$

因此每个 $F_\ell$ 保持 $\mathscr L_q$。令 $A_\Delta=\max_{\ell\in\Lambda}|\Delta_\ell'|$，选取

$$
R\ge\max_{c\in C}|c'|,\qquad
R\ge\frac{gA_\Delta}{1-g}.
\tag{31.8}
$$

此处 $C$ 包含状态端点，因而非空。对 $x\in B$，共轭更新给出

$$
|F_\ell(x)'|\le g(R+A_\Delta)\le R.
\tag{31.9}
$$

结合格保持及实嵌入中的条件 $F_\ell(x)\in X$，得到 (31.6)。

有限性使用两个嵌入。若 $x=(m+nt)/q\in B$，其中 $m,n\in\mathbb Z$，则

$$
n=\frac{q(x-x')}{\sqrt5},\qquad m=qx-nt,
\qquad
|n|\le\frac{q(\phi+R)}{\sqrt5},\quad
|m|\le q\phi+t|n|.
\tag{31.10}
$$

所以两个整数系数同时有界，$B$ 有限。只给实坐标 $x\in X$ 不够；有限性来自双嵌入的联合界。$C\subseteq B$ 则由 (31.8) 直接得到。$\square$

这个推广把第29章固定的公分母五和共轭界八替换为适配有限端点族的 $q,R$。它要求的是端点属于 $\mathbb F$，不是端点只在某个更大的代数扩域中。这里的有限性不提供具体图节点数量或最小状态数。

### 31.3 带类型闭覆盖与整条地址的精确图

**定义 31.3（闭片覆盖与唯一的全包含边规则）。** 对 $s\in\{0,1\}$，令 $B_s=B\cap I_s$。有限闭覆盖 $\mathcal P_s$ 包含每个 $b\in B_s$ 的单点片 $\{b\}$，以及 $B_s$ 中每对相邻点之间的整个闭区间。节点为 $(s,P)$，$P\in\mathcal P_s$；其 guard 类型保留为 $s$。边只采用

$$
(s,P)\xrightarrow{\ell}(s',Q)
\quad\Longleftrightarrow\quad
s\xrightarrow{\ell}s'\text{ 合法},\qquad
P\subseteq D_{s,\ell},\qquad
Q\subseteq F_\ell(P).
\tag{31.11}
$$

节点容许指标集 $H$ 当且仅当 $P\subseteq\bar E_i$ 对每个 $i\in H$ 成立。有限指标集的选择构成有限的观察字母表；空指标集在每个节点都容许。闭片在端点处重叠，端点单点另外保留。

**定理 31.4（有限闭观察族的共同来源图）。** 定义31.3给出有限图。它对定义31.1的全部有限或无限正成员关系同时精确：每条带容许观察的图路径联合提升为一条实际合法地址，反过来每条满足相应关系的实际地址都有保留原窗口和实际 guard 的规范片路径。有限路径的提升允许任意终端片内的点及其一条合法终端尾，未来没有观察要求；无限路径的全部坐标由同一地址实现。底层图没有死端，并保留单点观察、空观察和所有 guard、分支端点的情形。

证明。引理31.2已给有限端点集、状态端点和分支端点。若 $P\subseteq D_{s,\ell}$，则 $F_\ell(P)$ 是 $I_{s'}$ 中的非空闭区间或单点；其端点由 (31.6) 属于 $B_{s'}$。因此命题29.7的规范片与全像并结论在这里成为

$$
F_\ell(P)=
\bigcup\{Q\in\mathcal P_{s'}:Q\subseteq F_\ell(P)\}.
\tag{31.12}
$$

该命题所需条件只是闭区间端点属于相应切点集，本章已由引理31.2逐项满足。具体而言，$x\in B_s$ 时其规范片为 $\{x\}$；否则为内部含 $x$ 的唯一基本闭区间。任何包含 $x$、且端点属于 $B_s$ 的闭子区间都包含该规范片。观察交集 $\bar E_i\cap I_s$ 的非空端点也在 $B_s$ 中，故实际点的规范片同时保留所有满足的正成员约束和实际分支域约束。实际下一坐标的规范片由 (31.12) 整个包含在同一个 $F_\ell(P)$ 中。这正好给出 (31.11)，证明规范路径的完备性，包括只发生在端点的约束。

整条提升使用定理29.8的同一结构结论。其有限提升只用非空终端片、状态相对满像、合法 guard 前接以及

$$
f_{\ell_j}(P_{j+1})\subseteq P_j;
\tag{31.13}
$$

这些条件由 (31.11) 和定理17.2全部提供。因此同一个终端点和同一条终端尾承担整条有限路径的坐标与观察；它不把逐边存在替代成联合存在。其无限提升只用闭片紧致性、(31.13) 与统一收缩 $0<g<1$：前缀像嵌套，直径不超过 $g^N\operatorname{diam}(X)$，后缀所得坐标满足同一窗口级数，余项 $(-g)^Nx_{j+N}$ 趋零。第29.8条的证明不使用公分母五、数值界八或临界六色的特殊形状，故在本章替换为 $\mathscr L_q,R,\mathcal P_s,\bar E_i$ 后直接给出所述有限和无限共同地址提升。

最后，合法闭分支域覆盖每个 $I_s$，其端点全在 $B_s$ 中，所以每个基本片 $P$ 至少整个位于一个合法分支域。由 (31.12)，这个分支的非空像包含一个后继片，故每个节点有出边。任何有限路径均可无限延续。空观察 $\bar E_i=\varnothing$ 没有相容节点，恰好排除要求它的历史；单点观察有其端点单点节点，并保留其实际合法延续。附加无限观察要求可以排除延续，但这不改变底层图没有死端的结论。$\square$

精确性针对闭成员关系 (31.4)。当 $\bar E_i$ 取为 (28.2) 的闭扩张区间时，它继续表示第29—30章的共同候选关系；并不把闭扩张端点自动宣称为每种切点归属下字面可取得的颜色目标。整个构造始终使用 (31.11) 的一个图规则。

### 31.4 有限全路径仿射图的交替极值

**定义 31.5（全路径表示与非空初始条件）。** 给定有限有向图 $\Gamma=(V,\mathcal E)$ 和有限初始节点集 $V_{\mathrm{in}}\subseteq V$。每条边 $e:v\to w$ 带平移量 $d_e\in\mathbb F$，其仿射映射为 $x\mapsto d_e-gx$。接受的对象恰为从 $V_{\mathrm{in}}$ 出发的全部无限边路径，标量编码为

$$
\pi(e_0e_1\cdots)=\sum_{n\ge0}(-g)^n d_{e_n}.
\tag{31.14}
$$

没有另外的实数侧条件、外部选取的路径子集或额外接受测试。先删去没有无限延续的节点，并将边限制到剩余节点；初始集取与剩余节点的交。此操作不改变任何原有无限初始路径：其每个后续节点都有由该路径给出的无限延续。每个剩余节点至少有一条剩余出边。剩余初始集为空时，表示空集；非空时，从每个剩余初始节点都有实际接受的无限路径。

FIB 应用还要求节点带 incoming guard、初始 guard 为零、每条边遵守 (31.2) 并取 $d_e=\Delta_{\ell(e)}$。于是边标签拼成实际 $\Omega$ 地址，(31.14) 就是 $\kappa_0$。极值定理本身不需要这个额外的来源识别条件。

**定理 31.6（域内极值与交替最优路径）。** 对定义31.5剪除后的每个节点 $v$，其全部无限路径的标量像 $\mathcal S_v$ 是非空紧集。记

$$
m_v=\min\mathcal S_v,\qquad M_v=\max\mathcal S_v.
$$

则 $m_v,M_v\in\mathbb F$，而且各由一条实际的最终周期边路径取得。非空有限初始集的总标量像同样具有属于 $\mathbb F$ 的最小值、最大值及相应取得路径。

证明。固定一个剩余节点 $v$，此时剩余边集非空。从 $v$ 出发的无限边路径空间，是有限离散边字母表乘积空间的闭子集：首节点和每一处边接续都是闭条件。剪除后的出边条件保证它非空，所以它紧致。令 $C_d=\max_e|d_e|$；级数尾部统一不超过 $C_dg^N/(1-g)$，故 (31.14) 连续，$\mathcal S_v$ 非空紧致，两个极值存在且取得。

全路径语义给出完整的首边分解

$$
\mathcal S_v=\bigcup_{e:v\to w}(d_e-g\mathcal S_w).
\tag{31.15}
$$

从 $w$ 出发的每条无限路径都可以接在该首边后，没有另外的过滤条件。斜率为负，故精确的 Bellman 方程是

$$
m_v=\min_{e:v\to w}(d_e-gM_w),\qquad
M_v=\max_{e:v\to w}(d_e-gm_w).
\tag{31.16}
$$

每个最小、最大都在有限非空出边集中取得。配对更新作用于全部 $(m_v,M_v)$；有限最小值和最大值的变化各不超过候选值的最大变化，所以此更新在上确界范数下的收缩因子为 $g$。特别地，两个固定点若相差上确界 $a$，就有 $a\le ga$，故固定点唯一。负斜率要求两类极值相互更新。

对每个 $v$ 固定选取 (31.16) 中一条最小边和一条最大边。策略状态是 $(v,-)$ 或 $(v,+)$，分别表示当前要取得 $m_v$ 或 $M_v$。从 $(v,-)$ 沿所选最小边到 $(w,+)$，从 $(v,+)$ 沿所选最大边到 $(w,-)$。这个策略在有限的加倍状态集上确定，且每一步都是真实的剩余图边。因此从任一策略状态出发得到一条合法无限边路径；不能只在原节点上固定同一条边来代替交替。

沿该策略路径记 $z_n$ 为当前策略状态对应的真实极值，$d_n$ 为所选边的平移量。由选择等式，

$$
z_n=d_n-gz_{n+1},\qquad
z_0=\sum_{n=0}^{N-1}(-g)^n d_n+(-g)^Nz_N.
\tag{31.17}
$$

所有 $z_N$ 的绝对值不超过 $C_d/(1-g)$，余项趋零。所以这条策略路径确实取得起始极值，不只是给出一个满足局部选择的候选值。有限确定的策略状态必在某处重复，其后状态和边重复；故该边路径最终周期。若平移序列的前周期长为 $k$、周期长为 $p\ge1$，其编码为

$$
\sum_{j=0}^{k-1}(-g)^j d_j
+(-g)^k
\frac{\displaystyle\sum_{r=0}^{p-1}(-g)^r d_{k+r}}
{1-(-g)^p}
\in\mathbb F.
\tag{31.18}
$$

分母非零，因为 $0<g<1$；其余各项全在 $\mathbb F$ 中。于是每个 $m_v,M_v$ 属于该域。初始总像是非空有限并 $\bigcup_{v\in V_{\mathrm{in}}}\mathcal S_v$，其两个极值分别取自一个初始节点的极值，因而也在域中且由接受路径取得。$\square$

负斜率的区别在一个节点、平移量为 $0,1$ 的两条自环中已经可见。交替边词 $(0,1)^\infty$ 与 $(1,0)^\infty$ 分别给

$$
m=-\frac{g}{1-g^2},\qquad M=\frac1{1-g^2}.
\tag{31.19}
$$

由 (31.16) 的配对收缩和这两个值满足相应方程，它们就是实际极值。错误地写成 $m=\min_d(d-gm)$ 会得到 $m=0$；在原单节点上始终选同一自环也不能取得所列极值。这个例子只说明一般仿射图为何需要奇偶类型，不把两条自环解释成 FIB 的合法 guard 图。

### 31.5 只限制根时刻的区间充要条件

**推论 31.7（非空闭根区间的准确端点分类）。** 对非空闭区间 $J=[a,b]\subseteq X$，存在定义31.5所规定的有限全路径 FIB 表示，其全部初始边标签地址恰为

$$
\{\omega\in\Omega:\kappa_0(\omega)\in J\},
\tag{31.20}
$$

当且仅当 $a,b\in\mathbb F$。这里初始节点集有限，初始 guard 为零，边使用固定 FIB 标签和平移量，且所有无限初始路径都接受；除了根成员条件，不限制未来观察。结论包含 $a=b$ 的单点区间。

证明。先设两个端点在 $\mathbb F$ 中。在定义31.1中只取观察 $J$，按引理31.2及定义31.3构图。初始节点恰取

$$
V_{\mathrm{in}}(J)=\{(0,P):P\in\mathcal P_0, P\subseteq J\}.
\tag{31.21}
$$

后续节点不再施加观察约束。每个初始路径按定理31.4联合提升为根值在 $J$ 中的实际地址；反过来每条根值在 $J$ 中的实际地址，其根规范片整个包含在 $J$ 中，规范路径属于上述初始集。故边标签语言恰为 (31.20)。定理17.2的满像保证 $J$ 非空时存在这样的地址；底层图无死端，初始路径不会在后续无约束延续中丢失。单点 $J$ 的初始化使用它的单点片。

反向，设给定这种有限全路径表示。剪除没有无限延续的节点不改变其语言。由状态零满像，(31.20) 的标量像恰为 $J$，所以有非空剩余初始集。定理31.6强制这个像的最小值、最大值属于 $\mathbb F$；它们正是 $a,b$。必要性实际上只需要标量像恰为 $J$，完整来源原像相等是更强的条件。$\square$

空目标由空初始集表示，没有端点限制。请求区间若伸到 $X$ 外，分类作用于非空交集 $J=E\cap X$ 的有效端点，不能对被裁掉的外部参数提出域条件。特别地，对根阈值 $E=(-\infty,\theta]$：$-1\le\theta\le\phi$ 时非空有效目标为 $[-1,\theta]$，其有限全路径表示等价于 $\theta\in\mathbb F$；$\theta>\phi$ 时全部来源均接受，$\theta<-1$ 时没有来源接受，外部阈值无需在该域中。

未来无约束是推论31.7的一部分。把根初始化替换为任意指定的无限平稳色流，或强制未来每步都从一个不覆盖 $X$ 的观察族中取标签，会另外删掉地址。定理31.4仍然精确表示相应联合关系，但它的根标量像不再由这条推论保证等于 $J$，因此不能据此宣称同一个区间充要结论。

**命题 31.8（域成员条件与无理性的区别）。** 根区间 $[-1,1/2]$ 和 $[-1,t]$ 都有推论31.7的有限全路径表示；根区间 $[-1,\sqrt2-1]$ 没有这种表示。

证明。$1/2,t\in\mathbb F$，且都在 $X$ 中，直接应用推论31.7。另一方面，$1<\sqrt2<2$ 给 $\sqrt2-1\in(0,1)\subset X$。若 $\sqrt2\in\mathbb Q(\sqrt5)$，写成 $u+v\sqrt5$，$u,v\in\mathbb Q$。平方比较有理部分和 $\sqrt5$ 系数，得到

$$
u^2+5v^2=2,\qquad uv=0.
\tag{31.22}
$$

若 $v=0$，则 $u^2=2$；若 $u=0$，则 $v^2=2/5$。两者均不可能是有理数平方，因为平方的每个素数赋值为偶数，而这两个数的素数 $2$ 赋值为一。因此 $\sqrt2\notin\mathbb F$，从而 $\sqrt2-1\notin\mathbb F$；推论31.7给出障碍。$\square$

$t$ 是无理数而在 $\mathbb F$ 中，$\sqrt2-1$ 是代数数却不在 $\mathbb F$ 中；后者甚至满足系数属于 $\mathbb F$ 的方程 $(x+1)^2-2=0$。准确判据是域成员关系，不能换成“端点有理”、 “端点无理”或“端点在 $\mathbb F$ 上代数”。

### 31.6 接受语义、响应边界与适用范围

全路径分解 (31.15) 是极值定理的实质条件。仅知某个被额外筛选的路径族紧致，不足以推出这条分解。例如，对任意 $\theta\in X$，原有有限 FIB guard 图的无限地址在附加条件 $\kappa_0(\omega)\le\theta$ 下形成紧集，标量最大值恰为 $\theta$。当 $\theta\notin\mathbb F$ 时，这不反驳定理31.6：附加实数测试已经承担了图本身未表示的限制，其尾路径不能任意独立前接。紧致性保证极值存在，全路径分解和交替策略才保证极值落在系数域。

闭正成员关系也不同于确定的完整成员位输出。对 $E=[-1,0]$，正位 $x\in E$ 是闭约束；负位 $x\notin E$ 的标量像却为 $(0,\phi]$。有限图的全部无限初始路径空间紧致，编码连续，所以这种非紧的半开像没有本章的精确全路径表示。端点属于 $\mathbb F$ 本身不保证确定的半开分区或全部正负成员位都有同样的闭图模型；本章覆盖保留的是可重叠的正关系和端点单点。

系数域条件同样不能隐去。在允许任意实数平移量的模型中，一个平移量为 $(1+g)\theta$ 的自环，其唯一无限路径就编码为 $\theta$，无论 $\theta$ 是否属于 $\mathbb F$。定理31.6限制平移量属于 $\mathbb F$，FIB 应用进一步固定为原五个 $\Delta_\ell$；不能把待表示的端点直接藏入边系数，再引用该定理。

来源范围是完成域 $\Omega$，包括合法无限尾和所有端点尾。推论31.7没有把这个域换成仅有最终空尾的 $D$；状态相对满像和紧致全路径语义承担了必要性中的真实闭区间像。第29章的有限首窗观察器、第30章的完整有序输出障碍和增长历史构造仍按各自任务合同使用。候选图有限不意味着全部来源任务都有固定有限状态实现，端点分类也不给最小状态数、尖锐记忆率或处理时间。

有限响应图的这条解释依赖三件事：端点具有共同分母的域内格表示，删除逆分支在共轭方向收缩，以及 guard 与闭片全包含关系保留实际共同地址。五个标签给出具体分支和平移数据；仅凭“五”这个数目不能推出端点闭合或任意观察族的有限精确表示。反方向的极值障碍还依赖全路径接受和域内系数，不能由分支数目替代这些假设。

后续定理附录宜将这一条证明链集中在同一处：已有 FIB 来源图和状态满像，代数单位的公分母格与双嵌入有界性，闭片的共同地址提升，负斜率折扣的交替极值策略，最后是根区间的端点分类。代数单位、双嵌入格和折扣极值策略都是标准数学成分；这里给出它们与本卷来源合同的具体桥接，不作原创性断言。结论是普通纸面数学，不是形式内核核验或实验结果。域外端点的障碍仅排除指定有限全路径图的精确表示，不排除任意算法、任意观察方式、有限观察字母表、实数访问、噪声容忍、近似表示、其他接受条件或物理模型，也不承担物理时空起源的结论。

## 追加锚（31·本行以下为增补区）

## 32. 根区间的无限接受、域端点与有限前缀停止

第31章把非空闭根区间的有限全路径表示归结为有效端点属于 $\mathbb F=\mathbb Q(t)$。本章允许端点任意归属，并把接受条件改为有限 Büchi 自动机的无限访问条件。准确的端点域仍是 $\mathbb F$，充分方向还可以使用确定弱 Büchi 自动机。与此并列，某条实际地址能否得到有限前缀答复，取决于它是否出现了成员关系一致的柱；无限字可以由有限规则接受，并不保证这条字的类别能在有限窗后宣布。

### 32.1 完整根原像与有效端点

**定义 32.1（根区间、端点归属与无限字识别）。** 全章沿用定义31.1的 $\mathbb F,t,\phi,g,I_s,X,A_s,\Omega$ 和 (31.2) 的实际标签、合法 guard 边及仿射分支。具体地，

$$
\begin{gathered}
\mathbb F=\mathbb Q(t),\quad t=(\sqrt5-1)/2,\quad
\phi=1+t,\quad g=t^3=2t-1,\quad 0<g<1,\\
I_0=X=[-1,\phi],\qquad I_1=[-1,t],\\
\Lambda=\{3,0,5,2,25\},\qquad
0\to0:3,0,2;\quad 0\to1:5,25;\quad
1\to0:3,0;\quad 1\to1:5.
\end{gathered}
\tag{32.1}
$$

$0$ 是空窗口，$25$ 是一个窗口标签。初始 guard 固定为零。读取 $\sigma_n(\omega)$ 就是读取同一实际位地址的第 $n$ 个三位窗口；合法无限标签字与这些实际地址对应。$\mathbb F$ 表示域，$A_s$ 表示状态地址域，$\Omega=A_0$ 表示完成来源，$X$ 表示标量区间；既有 $K$ 仍表示联合完成域。$T$ 仍是删除最低三位的来源映射，$g$ 只是正收缩系数。对同一地址记

$$
x_n=\kappa_{s_n}(T^n\omega)\in I_{s_n},\qquad
s_n\xrightarrow{\ell_n}s_{n+1},\qquad
x_n=\Delta_{\ell_n}-gx_{n+1}.
\tag{32.2}
$$

这里平移量仍为 $(-t,0,t^2,1,2-t)$，按标签 $(3,0,5,2,25)$ 排列。两种状态的编码使用同一个窗口级数。定理17.2给出 $\kappa_s(A_s)=I_s$，并保留所有实际端点尾；不把共同标量的不同地址识别，也不选择一个自主标量删除分支。

设 $J\subseteq X$ 为非空区间，令 $a=\inf J$、$b=\sup J$，并令 $\alpha,\beta\in\{0,1\}$ 分别表示 $a,b$ 是否属于 $J$。若 $a=b$，非空性要求 $\alpha=\beta=1$，此时 $J=\{a\}$。统一写为

$$
\begin{aligned}
J&=\{x\in X:
[x>a\ \lor\ (\alpha=1\land x=a)]
\land[x<b\ \lor\ (\beta=1\land x=b)]\},\\
L_J&=\kappa_0^{-1}(J)
=\{\omega\in\Omega:\kappa_0(\omega)\in J\}.
\end{aligned}
\tag{32.3}
$$

$L_J$ 是完整原像，同标量的全部地址具有同一成员答案。若名义区间 $E$ 延伸到支撑外，先取 $J=E\cap X$；非空时本章端点条件只作用于 $a,b$，归属也按交集确定。空交集单独处理，不给不存在的有效端点施加条件。

有限 Büchi 自动机每步消费一个实际窗口标签；一个字被接受，指存在从有限初始状态集出发、无限次访问指定接受状态的无限运行。这里“$\omega$-正则”按有限非确定 Büchi 自动机定义，其在 $\Lambda^{\mathbb N}$ 中的接受字必须恰为指定的合法地址语言。确定型每个字只有一条运行；弱型指每个强连通分量的接受位一致。非法 guard 字不能被接受。根条件 (32.3) 是唯一观察约束，不给 $x_n$ 再施加一列移位观察。

地址空间 $\Omega$ 在有限标签的前缀拓扑下是紧致闭空间，合法有限前缀 $w=\ell_0\cdots\ell_{N-1}$ 的柱记为 $[w]_\Omega$。若其终端 guard 为 $s_N$，置 $H_0=\phi,H_1=t$，则由实际尾满像得到

$$
\begin{aligned}
p_N(w)&=\sum_{j<N}(-g)^j\Delta_{\ell_j},\\
I_w:=\kappa_0([w]_\Omega)
&=p_N(w)+(-g)^N I_{s_N}
=f_{\ell_0}\circ\cdots\circ f_{\ell_{N-1}}(I_{s_N}),\\
\operatorname{diam}(I_w)
&=g^N(1+H_{s_N})>0.
\end{aligned}
\tag{32.4}
$$

每个柱的所有标量值由同一已观察前缀的合法延续取得，柱像是非退化闭区间。对一个固定地址，这些像嵌套且直径趋零。柱的开闭性来自前缀拓扑，编码连续性也直接由统一级数余项得到。全章使用完整 $\Omega$，不换成最终空尾子域 $D$。

**定理 32.2（任意端点归属的根区间分类）。** 对定义32.1的非空 $J$，

$$
L_J\text{ 是 }\omega\text{-正则}
\quad\Longleftrightarrow\quad
a,b\in\mathbb F.
\tag{32.5}
$$

在右侧成立时，存在读取同一实际地址、保留实际 guard 的有限确定弱 Büchi 识别器。允许非确定性或改变两个端点的归属，不扩大这里的有效端点类别。空目标恒可识别；非空单点按同一域条件分类。证明的充分方向见定理32.5，必要方向见定理32.7。有限前缀答复是定理32.9的另一条件，不是本定理的附带保证。

### 32.2 有限残余阈值与负斜率奇偶

**定义 32.3（共享 guard 和奇偶的逆阈值跟踪器）。** 先设 $a,b\in\mathbb F$。在引理31.2中取闭观察 $\{a\},\{b\}$，得到一个包含这两个端点、状态端点及分支端点的有限集 $B$。它满足

$$
B=\{z\in q^{-1}\mathbb Z[t]\cap X:|z'|\le R\},
\qquad
z\in B,\ F_\ell(z)\in X\ \Longrightarrow\ F_\ell(z)\in B,
\qquad
F_\ell(z)=\frac{\Delta_\ell-z}{g}.
\tag{32.6}
$$

这里复用 (31.5)—(31.10)：$g^{-1}=3+2t$ 使公分母格不变，而

$$
F_\ell(z)'=gz'-g\Delta_\ell',\qquad
|F_\ell(z)'|\le g(R+A_\Delta)\le R.
\tag{32.7}
$$

当实嵌入的更新仍在 $X$ 中时，共轭界与公分母格保持；双嵌入的整数系数界给出有限性。于是任何仍未决的逆阈值轨道都在同一个有限 $B$ 中。只限制实值范围不能代替这项共轭界。本章以 $B$ 的元素作为有限状态标签，不另行搜索一个轨道。

一个阈值 $\theta$ 的比较状态为 $U(z)$（未决，$z\in B\cap I_s$）、$C(-)$ 或 $C(+)$（原根差的严格符号已经结算）。全局状态共享实际 guard $s$ 和奇偶符号 $\varepsilon\in\{+1,-1\}$；有两个比较坐标时，状态为 $(s,\varepsilon,r_a,r_b)$，另设永久拒绝状态 $\bot$。初态为 $(0,+1,U(a),U(b))$。

无论比较是否已经结算，每次先检查 $s\xrightarrow{\ell}s'$ 是否为 (32.1) 的合法边。非法则进入 $\bot$，且永不离开。合法则把共享奇偶改为 $\eta=-\varepsilon$，guard 改为 $s'$；已经结算的 $C(\pm)$ 保持原符号。对每个未决坐标 $U(z)$，令 $c=F_\ell(z)$，使用实际下一 guard 的闭尾区间：

$$
U(z)\longmapsto
\begin{cases}
U(c),&-1\le c\le H_{s'},\\
C(\eta),&c<-1,\\
C(-\eta),&c>H_{s'}.
\end{cases}
\tag{32.8}
$$

$C(+1)$、$C(-1)$ 分别就是 $C(+)$、$C(-)$。第一种更新由 (32.6) 保持在有限状态集中。等于尾区间端点时仍走未决分支；不能把闭端点等号结算成严格符号。下面证明中的符号反转使用更新后的 $\eta$，不是更新前的 $\varepsilon$。

如果使用名义阈值 $\theta<-1$，根比较可直接初始化为 $C(+)$；$\theta>\phi$ 时为 $C(-)$。这样的外部阈值不必纳入 $B$，也不必属于 $\mathbb F$，因为在所有合法根来源上已有严格关系。恰为 $-1$ 或 $\phi$ 时仍须使用未决初态。定理32.2的实现直接使用有效端点，因而不依赖被裁掉的外部参数。

**引理 32.4（严格结算与永久未决的准确语义）。** 对任何合法地址，阈值跟踪器永久未决当且仅当 $x_0=\theta$；若 $x_0<\theta$ 或 $x_0>\theta$，则经过有限窗后永久结算为相应严格符号。每一次已经结算的符号都对该前缀的全部合法延续正确，包括后来仍须检查 guard 的情形。

证明。在读过 $N$ 个窗口、比较仍为 $U(z_N)$ 时，不变量为

$$
\varepsilon_N=(-1)^N,\qquad
\theta=p_N(w)+(-g)^Nz_N,\qquad
x_0-\theta=(-g)^N(x_N-z_N).
\tag{32.9}
$$

初态满足它。下一合法窗口给出 $x_N-z_N=-g(x_{N+1}-c)$，故原根差的符号取决于 $\eta=-\varepsilon_N$ 与 $x_{N+1}-c$ 的乘积。$c<-1$ 时所有合法下一尾都严格大于 $c$，符号为 $\eta$；$c>H_{s'}$ 时所有下一尾都严格小于 $c$，符号为 $-\eta$。这正是 (32.8)，并证明严格结算对整个当前柱有效。

若 $x_0=\theta$，未决不变量强制 $z_N=x_N$，下一阈值就是实际 $x_{N+1}\in I_{s'}$，所以每步继续未决。这包括一个端点的全部合法编码。反之，永久未决时，$z_N,x_N\in I_{s_N}\subseteq X$，因而

$$
|x_0-\theta|
\le g^N\operatorname{diam}(X)\longrightarrow0.
\tag{32.10}
$$

所以永久未决只能是等号。若原差非零，永久未决已被排除，比较必在有限步严格结算；结算符号的正确性已证，后续合法窗口不再改变它。非法延续则被 $\bot$ 排除。$\square$

由此，有限未决前缀只是尚未得到严格分离，不能被宣布为等号。等号语义依赖整条合法无限运行的永久未决行为，严格结算则已经是对整个柱成立的有限证书。

### 32.3 端点归属的弱 Büchi 接受

**定理 32.5（同一地址上两个端点的确定弱识别）。** 当有效端点属于 $\mathbb F$ 时，定义32.3给出一个识别 $L_J$ 的有限确定弱 Büchi 自动机，对全部端点编码遵守 (32.3) 的归属。

证明。先对一个阈值指定接受位。$\bot$ 永远不接受；合法比较状态按下表赋位，其中“未决接受”只表示无限运行的 Büchi 状态位。

| 根比较谓词 | 未决 $U(z)$ | 已结算 $C(-)$ | 已结算 $C(+)$ |
| --- | --- | --- | --- |
| $x_0<\theta$ | 不接受 | 接受 | 不接受 |
| $x_0\le\theta$ | 接受 | 接受 | 不接受 |
| $x_0>\theta$ | 不接受 | 不接受 | 接受 |
| $x_0\ge\theta$ | 接受 | 不接受 | 接受 |
| $x_0=\theta$ | 接受 | 不接受 | 不接受 |

引理32.4表明，每条合法运行或者永久未决，或者最终永久保留一个正确严格符号。因此每行的接受位最终恒定，且该恒定位恰是相应根谓词的真值。一旦出现非法窗口，运行有永久拒绝后缀；此前有限次的接受访问不能使它通过 Büchi 条件。接受一个未决状态不意味着当时已经确认等号或成员关系，因为它以后仍可能走到拒绝的严格状态。

对下端点使用 $x_0>a$（$\alpha=0$）或 $x_0\ge a$（$\alpha=1$）；对上端点使用 $x_0<b$（$\beta=0$）或 $x_0\le b$（$\beta=1$）。两个坐标读取同一个标签，共享实际 guard 和奇偶。产品状态接受当且仅当两个坐标的接受位都为真。

这里逐状态取合取确实给出两个 Büchi 条件的合取：每个坐标的接受位在合法运行上最终恒定，故两个最终真值同时为真当且仅当产品无限次接受。若其中一个最终为假，产品只能有有限次接受。这个论证依赖本跟踪器的最终恒定性，不能作为任意两个 Büchi 自动机逐状态合取的规则。

每个比较坐标只能从未决进入某个严格类，不能返回，也不能在两个严格类之间转换。因此每个强连通分量具有固定的未决／严格类型；guard 和奇偶即使在分量内变化，也不改变任何接受位。$\bot$ 是拒绝分量，产品的其他分量同样有统一接受位，故自动机为确定弱型。状态有限性由 $B$、两个 guard、两个奇偶和有限比较类型给出。引理32.4和 (32.3) 随即证明接受语言恰为 $L_J$。$\square$

$a=b$ 且两端都归属时，两项合取恰为等号纤维；同点但有一端不归属的名义区间为空，使用恒拒绝识别器即可。名义下界大于上界、或与支撑无交集时也如此。$J=X$ 可由接受全部合法 guard 运行的识别器处理；$X$ 的某一支撑端点若被排除，则相应比较仍按上表保留等号拒绝。支撑外的边界严格成立或严格不成立，内部有效端点和恰在支撑上的端点才承担归属条件。以上均不从有限未决前缀推出等号。

### 32.4 从 Büchi 接受转到闭包全路径图

**引理 32.6（活状态裁剪的紧致标签闭包）。** 设非空 $L\subseteq\Omega$ 由任意有限 Büchi 自动机接受，允许非确定性、多个初态和平行边。先与 (32.1) 的 guard 图取产品。称产品状态为活状态，指从该状态存在一个无限 Büchi 接受延续。只保留活状态、两端都活的原边和活初态，随后忘掉接受位。所得有限图从保留初态出发的全部无限路径，其标签语言 $C$ 满足

$$
C=\overline L.
\tag{32.11}
$$

地址闭包取前缀拓扑；因 $\Omega$ 为闭集，环境标签空间中的闭包与其相对闭包一致。所得图没有额外路径过滤条件。

证明。guard 产品不改变 $L$，却使以后每条表示路径都合法。非空性保证至少一个活初态。每个活状态都有通向活状态的边：取一条接受延续的首步，其余无限后缀仍接受。任何接受运行上的全部状态都活，因为去掉有限次访问不改变无限接受。故 $L\subseteq C$。

保留图的完整无限边运行空间，是有限离散边空间乘积中的闭集，初态和边接续条件也闭，因而紧致。把完整运行连续投影为标签字，其像 $C$ 紧致、从而闭。这给出 $\overline L\subseteq C$。非确定性在这一步由完整运行的紧致投影处理；不把各长度分别存在的运行误当成已选好的一条共同运行。

反向，给定 $w\in C$，固定一条产生 $w$ 的保留图运行。对每个长度 $N$，其前 $N$ 步结束于某活状态；在这条固定运行的前缀后接一条从该状态出发的接受延续。拼接仍是从原初态出发的运行，且有限前缀不影响其 Büchi 接受。于是得到 $L$ 中具有 $w$ 的指定前 $N$ 个标签的字。它们在前缀拓扑下趋于 $w$，所以 $w\in\overline L$。$\square$

忘掉接受位可以引入一直不访问接受状态、却在每一步保留接受出口的路径；这些路径属于闭包，未被误称为原接受字。活状态条件已经用于有限裁剪，裁剪后的无限路径全部接受，不在路径外再施加一个原 Büchi 条件。

**定理 32.7（有限 Büchi 语言的域内上下确界）。** 对任意非空有限 Büchi 语言 $L\subseteq\Omega$，

$$
\inf\kappa_0(L),\quad\sup\kappa_0(L)\in\mathbb F.
\tag{32.12}
$$

两值分别由 $\overline L$ 中的最终周期合法标签地址取得；它们不必由 $L$ 中的地址取得。

证明。引理32.6的有限全路径图初始 guard 为零，每条边使用原来的标签和平移量 $\Delta_\ell\in\mathbb F$，因而满足定义31.5的 FIB 条件。所有活节点都有无限延续。直接应用定理31.6，其标量像的最小值、最大值在 $\mathbb F$ 中，并由最终周期路径取得。负斜率在此仍要求 (31.15)—(31.17) 的配对极值：最小值的首边使用后继最大值，最大值的首边使用后继最小值。引理32.6已经把接受条件全部吸收到闭包图，故这次应用没有外部筛选。

对任何 $L\subseteq\Omega$，连续性与紧致性还给出

$$
\kappa_0(\overline L)=\overline{\kappa_0(L)}.
\tag{32.13}
$$

左到右可由地址前缀逼近和 (32.4) 的直径界得到：闭包地址是 $L$ 中地址的极限，编码随之前趋于其值。右到左则因为左侧是紧集，包含 $\kappa_0(L)$，所以包含该标量像的闭包。标量闭包可在 $X$ 或实直线上取，因 $X$ 闭而结果一致。故闭包图的两个取得极值正是 (32.12) 的上下确界。$\square$

定理32.2的必要性现在得到：完整原像与满像保证

$$
\kappa_0(L_J)=J,\qquad
\kappa_0(\overline{L_J})=\overline J=[a,b].
\tag{32.14}
$$

因此定理32.7强制 $a,b\in\mathbb F$。结合定理32.5，(32.5) 得证。若端点不属于 $J$，对应极值地址只保证在闭包中取得，不能冒称原接受语言取得；若端点属于 $J$，完整原像才进一步把该极值地址纳入 $L_J$。单点非空时上下确界相同，仍给同一域条件。空语言没有在此被赋予有限实数极值。

必要性允许有限非确定性；端点排除只改变接受位，不改变 $\overline J$ 的两个有效极值。因此命题31.8的 $\sqrt2-1\notin\mathbb F$ 继续排除以它为有效端点的非空根区间的 $\omega$-正则完整原像，不论这个端点是否归属。端点仅为代数数，甚至在 $\mathbb F$ 上代数，都不能替代属于 $\mathbb F$ 的条件。

### 32.5 标量闭包等式不等于整个端点纤维的闭包

**命题 32.8（接触点 $0R$ 的原像闭包反例）。** 令

$$
z=t-1=-t^2,\qquad R=(25,3)^\infty,\qquad J_-=[-1,z).
\tag{32.15}
$$

则

$$
0R\in\kappa_0^{-1}(\overline{J_-}),
\qquad
0R\notin\overline{\kappa_0^{-1}(J_-)}.
\tag{32.16}
$$

证明。命题14.6给出合法 $R$ 的值 $\phi$，故 $0R$ 合法且值为 $-g\phi=z$。但其首窗为 $0$ 的整个柱像是

$$
\kappa_0([0]_\Omega)=f_0(X)=[z,g].
\tag{32.17}
$$

这个开闭柱与 $\kappa_0^{-1}(J_-)$ 不相交，足以排除 $0R$ 属于地址闭包；其标量却在 $\overline{J_-}=[-1,z]$ 中。$\square$

另一条接触地址是 $3L_{\mathrm{ext}}$，其中 $L_{\mathrm{ext}}=(3,25)^\infty$ 编码 $-1$；由命题14.8，它也编码 $z$。其首窗柱像为 $[-1,z]$，随后包含它的柱均非退化、以 $z$ 为端点且在左侧。因此每个这样的柱都含有值小于 $z$ 的合法地址，$3L_{\mathrm{ext}}\in\overline{\kappa_0^{-1}(J_-)}$。这也具体显示标量闭包中的一个值可以由部分端点编码取得，而不要求同纤维的每条地址都在地址闭包中。

必要性使用的是 (32.13)—(32.14)，不是一般错误的等式 $\overline{\kappa_0^{-1}(J)}=\kappa_0^{-1}(\overline J)$。反例的两条地址始终保留各自实际后继；从标量左侧趋近 $z$ 不意味着能在前缀拓扑中趋近 $0R$。

### 32.6 逐地址的有限前缀停止判据

**定理 32.9（成员柱证书与有效的逐前缀测试）。** 固定根区间 $J$，在仅依次取得同一实际地址窗口的访问合同下，一个对所有合法延续都正确的二值成员答复能在地址 $\omega$ 的某个有限前缀处停止，当且仅当存在 $N\ge0$，其实际前缀 $w_N$ 满足

$$
I_{w_N}\subseteq J
\quad\text{或}\quad
I_{w_N}\cap J=\varnothing.
\tag{32.18}
$$

这是逐地址的有限信息证书判据。若另外给定非空 $J$ 两个有效端点的精确 $\mathbb F$ 表示和归属位，则逐次测试 (32.18) 是有效的，且恰在具有这种证书的地址上停止。空目标及全支撑目标可直接答复。

证明。有限前缀答复只能依赖已经取得的标签。任何合法延续都提供相同前缀，而 (32.4) 的满像保证 $I_{w_N}$ 中每个点都由某个这样的延续取得。因此答“属于”必须对整个柱像成立，答“不属于”必须对整个柱像不相交；否则有共享前缀的实际反例。反过来，任一包含或不相交关系都给出对所有合法延续正确的相应答复。该存在性不要求预先有任意实参数的统一计算描述。

给定精确域表示后，(32.4) 的两个柱端点 $l_N<u_N$ 属于 $\mathbb F$，并可按实际奇偶写为

$$
(l_N,u_N)=
\begin{cases}
(p_N-g^N,\ p_N+g^NH_{s_N}),&N\text{ 偶},\\
(p_N-g^NH_{s_N},\ p_N+g^N),&N\text{ 奇}.
\end{cases}
\tag{32.19}
$$

对非空 $J$，正证书的准确测试为

$$
I_{w_N}\subseteq J
\quad\Longleftrightarrow\quad
[l_N>a\ \lor\ (l_N=a\land\alpha=1)]
\land
[u_N<b\ \lor\ (u_N=b\land\beta=1)],
\tag{32.20}
$$

负证书的准确测试为

$$
\begin{aligned}
I_{w_N}\cap J=\varnothing
\quad\Longleftrightarrow\quad&
u_N<a\ \lor\ (u_N=a\land\alpha=0)\\
&{}\lor\ l_N>b\ \lor\ (l_N=b\land\beta=0).
\end{aligned}
\tag{32.21}
$$

这两项也适用于非空单点，此时 $a=b$、两归属位都为一。其正证书因柱非退化而不成立；负证书仍由精确不相交测试确定。

域运算化为 $r+st$，$r,s\in\mathbb Q$。由于 $t$ 无理，等号可精确判定；对非零表达式，其符号可由 $t^2+t-1=0$ 的正根有理隔离区间逐次细化判定，非零性保证有限终止。因此每一个已取得前缀的测试有效。按窗口依次更新实际 $p_N,s_N$ 并测试，出现证书就停止；没有证书时不发二值答复。由前半段，这恰是允许停止的记录集合。$\square$

“端点属于 $\mathbb F$”给出定理32.2的识别器存在性；“已给出精确 $\mathbb F$ 表示”则提供这里执行代数测试所需的数据。这两句话不是同一个输入合同。本章不从任意可计算实数描述合成域内表示，不提供对任意这种描述的域成员判定，也不声称任意实端点都具有统一有效的停止测试。

严格比较在定义32.3中结算时已给出相应柱证书，但整个区间的有限停止不等于两个跟踪坐标均严格结算。端点归属与单侧柱可能在某个坐标永久未决时就使 (32.20) 或 (32.21) 成立。Büchi 状态接受位也不能代替这些全柱测试。

### 32.7 端点编码、单侧柱与全域停止障碍

**命题 32.10（边界记录的有限答复区别）。** 对非退化根区间、单点根区间及支撑端点，定理32.9具有以下逐地址后果。

证明。先取非退化 $J$ 的一个内部有效端点 $c\in(-1,\phi)$。若 $c$ 唯一编码，则由定理14.7，它不是任何有限层的内部柱端点。因此在该地址的每个柱像中，$c$ 都位于区间内部，两侧都有实际合法延续。取足够靠近 $c$ 的两侧值，其中一侧属于 $J$、另一侧不属于 $J$；端点自身归属不改变这一点。所以该边界地址没有 (32.18) 的有限证书。

若 $c$ 双编码，两条地址在首次分歧处选择两个相邻柱。仿射方向可能反转，但标量上仍是一条位于左侧、一条位于右侧，公共端点为 $c$。此后各自更深柱都包含 $c$、保持在对应一侧、非退化且直径趋零。故对于以 $c$ 为端点的非退化 $J$，可以按标量上的区间内侧和外侧区分两条地址：当 $c$ 归属 $J$ 时，内侧地址最终有全柱正证书，外侧地址始终有相反成员的延续；当 $c$ 不归属 $J$ 时，外侧地址最终有全柱负证书，内侧地址始终有相反成员的延续。这里“最终”选取足够短的柱，使它不触及 $J$ 的另一个端点。任何较早柱也包含后续混合柱，所以不能绕过所述不停止结论。

例如，在 $z=t-1$ 处，$3L_{\mathrm{ext}}$ 的柱位于左侧，$0R$ 的柱位于右侧。对 $[-1,z]$，前者在首窗 $3$ 后即可答“属于”，后者不能得到有限正答复；对 $[-1,z)$，后者在首窗 $0$ 后即可答“不属于”，前者不能得到有限负答复。两条等号运行在定义32.3中都永久未决，归属仍由无限接受条件决定。因此严格符号结算与全柱停止确有不同。标量的反向逼近不能被转移成对两个编码都成立的前缀逼近。

另一个实际例子是零地址 $0^\infty$。每个前缀的柱像为

$$
I_{0^N}=(-g)^NX,
\tag{32.22}
$$

都含正值和负值。对 $[-1,0]$ 或 $[-1,0)$，这些柱均有两种成员答案，故零地址都没有有限停止证书。无限弱识别器却分别接受、拒绝其永久未决的零阈值运行，准确表达两种上端点归属。

若 $J=\{c\}$，每条编码 $c$ 的地址都不能停止：每个柱像非退化，同时含 $c$ 和另一个不属于单点的值。这不依赖 $c$ 是单编码还是双编码，也适用于支撑端点。若地址值不同于 $c$，柱直径趋零，最终有不相交证书。唯一标量编码、单点目标和单点来源柱是不同概念；本章的有限来源柱没有单点像。

支撑端点只使用实际存在的一侧。命题14.6中编码 $-1$ 的唯一地址 $L_{\mathrm{ext}}$，对任意 $-1<b<\phi$ 的 $J=[-1,b]$，最终有全柱正证书；对 $J=(-1,b]$，它虽不属于 $J$，每个非退化柱仍含右邻的成员值，不能有限答“不属于”。右支撑端点 $\phi$ 的唯一地址 $R$ 有对称区别。非退化目标的支撑端点归属与单点支撑目标也不能混同。

最后，若实际根值属于 $J$ 的相对内部，或属于 $X\setminus J$ 的相对内部，某个相对邻域具有一致成员答案；柱直径趋零且包含实际值，故最终有相应柱证书。以上所有断言都由实际柱满像和边界编码得到，未引入支撑外的假想延续。$\square$

**定理 32.11（非平凡目标不能在全部完成来源上有限停止）。** 若 $J$ 非空且 $J\ne X$，不存在只依次取得实际地址前缀、对所有 $\Omega$ 输入都正确并都在有限窗后停止的二值成员分类器。这个前缀信息障碍不依赖其工作记忆是否有限。

证明。若这样的分类器存在，每次有限答复必须在对应柱上保持同一答案。于是正类 $L_J$ 和负类 $\Omega\setminus L_J$ 都是前缀柱的并，二者均开，因而均为开闭集。在紧致 $\Omega$ 中，两类都紧致。又因成员关系为完整原像且 $\kappa_0$ 满射，

$$
\kappa_0(L_J)=J,\qquad
\kappa_0(\Omega\setminus L_J)=X\setminus J.
\tag{32.23}
$$

连续像紧致，故这两个标量集合均在 $X$ 中闭。于是 $J$ 在连通区间 $X$ 中开闭，只能为空或为 $X$，与假设矛盾。证明只用了前缀所保留的信息，未给工作记忆设置上界。$\square$

对空目标或全支撑目标，合法输入可以直接给常量答案；对其余目标，定理32.2即使给出有限弱 Büchi 识别器，也不消除定理32.11。停止困难不是每条地址都存在：定理32.9及命题32.10逐条确定哪些记录有有限证书。也不能把这个针对全部完成来源的结论未经检验转移到非紧的最终空尾子域 $D$，或转移到拥有额外实数访问、其他观察信息的模型。

### 32.8 接受语义与结论边界

闭全路径语义、Büchi 无限接受和有限前缀答复承担三种不同条件。第31章的全部路径空间紧致，其连续标量像闭；本章的接受子语言可以不闭，端点归属由无限访问条件实现。必要性先把接受语言换成引理32.6精确给出的闭包全路径图，再用第31章的负斜率交替极值；它没有把原接受语言当作紧集，也没有留下一个隐藏的实数路径过滤器。有限答复则必须满足整个实际柱成员一致，不能由当下的 Büchi 接受位推断。

这条根区间端点分类始终读取初始 guard 零的同一实际地址，使用固定的五个平移量、完整状态尾区间和全部端点编码。它不扩张为任意平稳移位观察流的联合识别定理。$\mathbb F$ 不是联合完成域 $K$，$\Omega$ 不是标量区间 $X$，来源删除 $T$ 也没有被降为全区间上的单值自主动力学。非确定性在必要性中由完整运行的紧致标签投影处理，充分性采用的仍是共享 guard／奇偶的残余逆阈值跟踪器。

本章给出普通纸面证明，复用引理31.2与定理31.6的现有代数和全路径结论。它不宣称形式内核核验、原创性、最小状态数、状态数量公式或复杂度界。前缀停止障碍限于这里的精确二值、完整原像与前缀访问合同，不承担任意有限观察者的统一障碍，也不推出物理时间方向、时空起源或热力学解释。

## 追加锚（32·本行以下为增补区）

## 33. 折叠边界的两区间记忆律

本章固定第28.1节的六格仪器、同一地址的连续取得合同和任意一个固定的切点归属向量。置

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad g=t^3=2t-1,\qquad \lambda=\frac{t^2}{10},
$$

$$
X=[-1,\phi],\qquad I=[-1,t],\qquad
(a,b,c,d,e)=(-t^2-\lambda,\ g-3\lambda,\ t-5\lambda,\ 2t-7\lambda,\ 2t+\lambda).
\tag{33.1}
$$

五个实际窗口标签为 $\Lambda=\{3,0,5,2,25\}$，六个观察颜色为 $\mathcal C=\{0,1,2,3,4,5\}$。实际分支和尾域是

$$
f_\ell(y)=\Delta_\ell-gy,\qquad
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})=(-t,0,t^2,1,2-t),
\tag{33.2}
$$

其中 $3,0,2$ 的尾域为 $X$，$5,25$ 的尾域为 $I$。切点归属只决定各颜色格的端点旗标；它不改变 (33.1)--(33.2) 的实际地址和 guard 关系。对 $\nu\ge0$，记 $J_i$ 为颜色 $i$ 闭格，记

$$
E_i^\nu=X\cap\{x:\operatorname{dist}(x,J_i)\le\nu\}.
\tag{33.3}
$$

任何实际颜色记录都满足 $x_j\in E_{R_j}^\nu$。这是必要关系；在闭半径的端点处，是否存在实际目标仍由切点归属决定。本章所有跨来源比较都保留一个实际来源的整条轨迹，并把每个来源的归属向量固定在整条记录上。

### 33.1 分隔类型与两步中心

**定义 33.1（临界分隔表）。** 令 $\delta=\lambda-\nu$。在 $0\le\nu\le\lambda$ 时，临界闭扩张区间为

$$
\begin{aligned}
E_0^\lambda&=[-1,-t^2],&
E_1^\lambda&=[-6t^2/5,g-t^2/5],\\
E_2^\lambda&=[g-2t^2/5,t-2t^2/5],&
E_3^\lambda&=[t-3t^2/5,2t-3t^2/5],\\
E_4^\lambda&=[2t-4t^2/5,2t+t^2/5],&
E_5^\lambda&=[2t,\phi].
\end{aligned}
\tag{33.4}
$$

内部区间在半径 $\nu$ 下两端各向内移动 $\delta$，而

$$
E_0^\nu=[-1,-t^2-\delta],\qquad
E_5^\nu=[2t+\delta,\phi].
\tag{33.5}
$$

四种内部当前颜色的唯一可能分隔类型、下一共同颜色和下一共同标签如下：

$$
\begin{array}{c|c|c|c|c}
 i&(\ell_i,m_i)&s_i&H(i)&q_i\\ \hline
1&(3,0)&-1+\phi/5&0&3\\
2&(0,5)&-1+2\phi/5&1&0\\
3&(5,2)&-1+3\phi/5&1&0\\
4&(2,25)&-1+4\phi/5&2&5
\end{array}
\tag{33.6}
$$

其中 $\ell_i$ 是较低分支、$m_i$ 是较高分支；并且

$$
E_i^\lambda=[f_{\ell_i}(s_i),f_{m_i}(s_i)].
\tag{33.7}
$$

在 $0\le\nu<\lambda$ 时，端颜色不能产生不同当前标签：$E_0^\nu$ 只涉及标签 $3$，$E_5^\nu$ 只涉及标签 $25$。在 $\nu=\lambda$ 的完成域 $\Omega$ 上，另有两个实际接触：$0(25,3)^\infty$ 的当前值为 $f_0(\phi)=-t^2$，当 $Q(a)=0$ 时误差 $-\lambda$ 给出颜色 $0$；$2(3,25)^\infty$ 的当前值为 $f_2(-1)=2t$，当 $Q(e)=5$ 时误差 $+\lambda$ 给出颜色 $5$。这些归属各自在整条记录上固定。定理33.3使用 $\nu\le\nu_*<\lambda$，不包含这两个接触。四个 $s_i$ 分别落在唯一的 $E_{H(i)}^\lambda$ 内；相邻排除所需的正差为

$$
\begin{aligned}
\min E_1^\lambda-s_1&=(5t-2)/5,\\
s_2-\max E_0^\lambda&=(2-3t)/5,&
\min E_2^\lambda-s_2&=(10t-4)/5,\\
s_3-\max E_0^\lambda&=(3-2t)/5,&
\min E_2^\lambda-s_3&=(9t-5)/5,\\
s_4-\max E_1^\lambda&=(5-7t)/5,&
\min E_3^\lambda-s_4&=(4t-2)/5.
\end{aligned}
\tag{33.8}
$$

这些量为正可由 $3/5<t<5/8$ 得到。若两个实际来源在颜色 $i$ 处使用不同标签，并在下一处仍有共同颜色，则令 $u,v$ 为按 (33.6) 排序的两个实际下一尾坐标。负斜率和 (33.7) 给出

$$
u\le s_i-\frac\delta g,\qquad
v\ge s_i+\frac\delta g.
\tag{33.9}
$$

因而下一共同颜色只能是 $H(i)$；若下一标签也共同，则只能是 $q_i$。对 $q_i$ 的负斜率逆映射再用一次 (33.9)，得到两步中心

$$
(z_1,z_2,z_3,z_4)=\left(\frac{2t}{5},\ 1+\frac{4t}{5},\ \frac t5,\ \frac{3t}{5}\right),
\tag{33.10}
$$

以及两步后的闭区间必要条件

$$
\boxed{
[z_i-\delta/g^2,z_i+\delta/g^2]
\subseteq E_r^\nu\cap D_i,
}
\tag{33.11}
$$

其中 $r$ 是第三个共同颜色，$D_1=D_2=D_3=X$，$D_4=I$。这里的 $D_i$ 是实际合法尾域；它保留了标签 $5,25$ 的尾域限制。若相关候选区间端点写成 $L+\alpha\delta$ 与 $U-\beta\delta$，且分母为正，则 (33.11) 的一侧精确给出

$$
\delta\le \min\left\{
\frac{g^2(z_i-L)}{1+\alpha g^2},
\frac{g^2(U-z_i)}{1+\beta g^2}
\right\}.
\tag{33.12}
$$

本章五次使用中速度只有 $0$ 或 $1$，所以 (33.12) 的两个分母都严格为正。

**引理 33.2（五行清除表）。** 对 (33.11) 的所有允许第三颜色，清除量的完整表为

$$
\begin{array}{c|c|c}
 i& r&\text{允许的最大 }\delta\\ \hline
1&2&K_1=\dfrac{g^2(2/5-g)}{1+g^2}=\dfrac{12-49g}{50}\\
2&5&K_2=\dfrac{g^2t}{5}=\dfrac{13g-3}{10}\\
3&1&K_{31}=\dfrac{g^2(g-1/5)}{1+g^2}=\dfrac{47g-11}{50}\\
3&2&K_{32}=\dfrac{g^2(7-11t)}{5(1+g^2)}=\dfrac{5-21g}{20}\\
4&2&K_4=\dfrac{2g^3}{5(1+g^2)}=\dfrac{9g-2}{25}.
\end{array}
\tag{33.13}
$$

证明。由 (33.4)、(33.10) 逐端点代入 (33.11)。类型 $1$ 的中心只在 $E_2^\lambda$ 内，左端余量为 $2/5-g$，得到 $K_1$。类型 $2$ 的中心只能落在 $E_5^\lambda$，支撑右端余量为 $t/5$，得到 $K_2$。类型 $3$ 的中心分别落在 $E_1^\lambda,E_2^\lambda$，给出 $K_{31},K_{32}$；类型 $4$ 只给出 $E_2^\lambda$，得到 $K_4$。所有未列区间在 $\delta=0$ 时已不含相应中心，收缩不会重新产生候选。每个候选的合法尾域正是 (33.11) 中的 $D_i$，故没有用非法尾补足清除表。$\square$

用 $g^2+4g=1$ 化简 (33.13)。多项式 $x^2+4x-1$ 在正轴严格递增，且在 $4/17$、$17/72$ 处符号相反，所以

$$
\frac4{17}<g<\frac{17}{72}.
\tag{33.14}
$$

这一区间逐项给出

$$
K_1-K_2=\frac{27-114g}{50}>0,\quad
K_1-K_{32}=\frac{7g-1}{100}>0,\quad
K_1-K_4=\frac{16-67g}{50}>0,
\tag{33.15}
$$

以及 $K_{32}-K_{31}=(47-199g)/100>0$。故唯一最大清除量是 $K_1$。

**定理 33.3（临界五次采集的实际首标签分离）。** 置

$$
\boxed{\nu_*:=\lambda-K_1=\frac{93g-19}{100}}.
\tag{33.16}
$$

则对每个 $0\le\nu\le\nu_*$，任意两个实际来源各自使用一个固定切点归属向量（两向量可以不同），在逐坐标闭误差界 $|e_j|\le\nu$ 下，任意五个连续颜色唯一确定首窗口标签。该结论同样适用于 $0<\nu\le\nu_*$ 的逐坐标正开误差流 $|e_j|<\nu$；$\nu=0$ 为精确无误差情形，并且

$$
0<\frac\lambda2<\nu_*<\lambda.
\tag{33.17}
$$

证明。若 $\nu<\nu_*$，则 $\delta>K_1$。由 (33.13)--(33.15)，任何不同当前标签在三个共同颜色之后都不能在下一处重新共同；所以不同标签的分歧会从一个共同颜色位置传播到下一个位置。若五个颜色相同而首标签不同，在位置 $0,1,2$ 连续应用传播，四个位置的标签都不同。端颜色已被排除，而内部颜色依照 $H$ 必须遵循

$$
1\to0,\qquad2\to1\to0,\qquad3\to1\to0,\qquad4\to2\to1\to0,
\tag{33.18}
$$

不可能出现四个连续内部颜色，矛盾。

还需处理 $\nu=\nu_*$ 的等号。除类型 $1$ 外，(33.15) 仍严格清除共同下一标签。类型 $1$ 若下一标签共同，只能是 $q_1=3$，且第三颜色只能是 $2$。等号迫使承载首标签 $0$ 的同一实际来源在两个坐标满足

$$
 x_0=b+\nu_*,\qquad x_2=b-\nu_*.
\tag{33.19}
$$

第一颜色为 $1$ 要求其裁剪目标是内部切点 $b$，故其固定量化器必须有 $Q(b)=1$；第三颜色为 $2$ 又要求同一来源的裁剪目标仍为 $b$，故必须有 $Q(b)=2$。一个来源的切点归属在整条记录上是固定的，矛盾。这个矛盾发生在一个来源的两次观测内，所以比较的另一来源即使使用不同的固定归属向量也不影响论证；不能把一个来源的归属随时间切换。

因此等号处传播也成立，五次采集的唯一性随即由 (33.18) 得到。等号结算使用的是 (33.19) 中同一实际来源的两个可取得目标，不是把闭扩张端点自动当作实际颜色。最后，(33.14) 给出

$$
\nu_*-\frac\lambda2=\frac{191g-43}{200}>0,
$$

且 $K_1>0$ 给出 $\nu_*<\lambda$、$\nu_*>0$。正开合同是闭合同的子合同，故同时成立。$\square$

### 33.2 归属旗标下的共同有限表

**定义 33.4（实际区间和整词可行性）。** 固定一个切点归属向量 $o$。把每个实际颜色格 $C_i^o$ 写成带左右包含旗标的区间。对闭合同和正开合同分别令

$$
B_{i,o}^{\le}(\rho)=X\cap(C_i^o+[-\rho,\rho]),\qquad
B_{i,o}^{<}(\rho)=X\cap(C_i^o+(-\rho,\rho)).
\tag{33.20}
$$

Minkowski 和的一个端点当且仅当两个加数的相应端点都被包含时才被包含。因此，闭噪声区间 $[-\rho,\rho]$ 在与 $X$ 相交前保留原格的端点包含旗标；正开噪声区间 $(-\rho,\rho)$ 在 $\rho>0$ 时使扩张后的两个端点都为开端点。与闭区间 $X$ 相交时，一个交集端点只有在两个区间都包含该点时才包含；若截断点位于扩张区间内部，则该点可以被包含。精确的 $\rho=0$ 情形使用 $B_{i,o}^{\le}(0)=C_i^o$，正开合同仅用于 $\rho>0$。负斜率仿射逆映射交换左右端点及其旗标，正斜率保持它们。

给定长度 $n$ 颜色词 $w$ 和一个从 guard 零出发、长度为 $n$ 的合法来源前缀 $\alpha$，令 $A_{\alpha,j}$ 为从末尾共同尾标量到第 $j$ 坐标的仿射映射，令 $I_s$ 为其终 guard 的尾域。定义

$$
Y_{\alpha,w,o}^{\diamond}
=I_s\cap\bigcap_{j=0}^{n-1}
 A_{\alpha,j}^{-1}\bigl(B_{w_j,o}^{\diamond}(\rho)\bigr),
\qquad \diamond\in\{\le,<\}.
\tag{33.21}
$$

(33.21) 只保留一个共同尾标量和一个整词归属向量。它非空，当且仅当有一个实际地址、一个固定归属向量和一条共同误差流实现整个词 $w$。

**命题 33.5（五次采集的单表准入）。** 在 $\rho=\nu_*$、$n=5$ 的闭合同下，定义

$$
L_{\rho,o}(w)=
\{\alpha_0:\exists\alpha\text{ 合法且 }Y_{\alpha,w,o}^{\le}\ne\varnothing\},\qquad
L_\rho^{\rm all}(w)=\bigcup_{o\in\{L,R\}^5}L_{\rho,o}(w).
\tag{33.22}
$$

则

$$
|L_\rho^{\rm all}(w)|\le1
\quad\text{对所有 }w\in\mathcal C^5.
\tag{33.23}
$$

因此存在一个共同的有限表 $F:\mathcal C^5\to\Lambda$：在非空词上返回 (33.22) 的唯一标签，在空词上任取固定的空标签。

证明。若 (33.23) 失败，则两个实际来源各自使用一个固定归属向量，产生相同五色词而首标签不同，与定理33.3矛盾。反向方向由 (33.21) 的同一尾标量提升：取交集中的一点，由定理17.2实现一个同一终尾，再按 $\alpha$ 前接；每个坐标的 Minkowski 归属给出该坐标的实际目标。故 (33.21) 没有把各坐标可行性拼成不同来源。外层仅有 $2^5=32$ 个固定向量；(33.23) 是跨归属向量的唯一性前提，而不是逐向量分别唯一后再拼接。这里定义了一个有限表的存在，不生成表项或状态计数。$\square$

**定理 33.6（小噪声固定滑窗解码）。** 对每个 $0\le\nu\le\nu_*$，同一表 $F$ 的五色滑窗给出一个固定确定解码器：每次取得第五个颜色后输出一个首窗口标签；它对所有实际 $\Omega$ 记录安全，对 $D$ 记录逐位置生效。其完整持久内存是常数，延迟为四次取得。

证明。第 $\nu$ 合同包含于第 $\nu_*$ 合同，故同一表仍正确。每个移位后的尾 $T^j\omega$ 都是一个合法 state-zero 地址；若其 incoming guard 为一，则因 $I\subseteq X$ 且首标签集合 $\{3,0,5\}$ 包含于根 guard 零允许的标签集合，它仍是根合法地址。因此

$$
F(R_j,R_{j+1},R_{j+2},R_{j+3},R_{j+4})=\sigma_0(T^j\omega).
\tag{33.24}
$$

解码器在启动时保留四个已取得颜色和一个有限暖机标志；第五次取得后应用 $F$，输出一个标签，丢弃最旧颜色并移位。它不保留绝对位置、输出历史、可读时钟或重放输入，也不把输出端口当作可读存储。表、四格颜色缓冲、当前颜色寄存器和控制状态都取自固定有限字母表，故完整内存恒定，且每个位置延迟四次取得。定理29.4的首标签安全性、定理30.10的逐位置共同来源测试以及 (33.24) 给出 $D$ 上全部窗口的有限生效。解码器不发出 End，也不认证来源支撑上界。$\square$

### 33.3 两个长度100的闭返回环

**定义 33.7（返回块和共同颜色）。** 令

$$
\theta=\frac{2t}{5},\qquad
U=(5,0,3,0,3,3),\qquad
V=(0,3,3,5,0,3),
\tag{33.25}
$$

并令 $C$ 为二十窗口词

$$
C=(5,5,3,2,2,0,3,3,3,25,5,0,0,2,2,25,3,3,0,5).
\tag{33.26}
$$

记 $d_*=(2,1,0,2,1,0)$，并指定

$$
c_*=(2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2).
$$

对高侧和低侧分别置

$$
H=(\theta,t^2],\qquad L=[0,\theta),
$$

$$
 z_U=\frac{23+14g}{76},\qquad z_V=\frac{6+9g}{76},\qquad
h=z_U-\theta>0,\qquad \ell=\theta-z_V>0.
\tag{33.27}
$$

以下逐坐标证明这两个共同颜色词及返回关系。对任意 $x\in H,y\in L$，$U,V$ 都能以严格小于 $\lambda$ 的误差实现共同词 $d_*$，且

$$
f_U(x)=(1-g^6)z_U+g^6x,\qquad
f_V(y)=(1-g^6)z_V+g^6y,
\tag{33.28}
$$

所以 $U$ 保持 $H$、$V$ 保持 $L$。同一实际轨迹的 $C$ 块在 $[0,t^2]$ 上有共同词 $c_*$；其位置 $0$ 到 $18$ 使用下面表中的固定内部目标，误差上界为

$$
R_C=\frac{\lambda+g^2t^2}{2}<\lambda,
\tag{33.29}
$$

位置 $19$ 取零误差即可。特别地，$(c_*)_1=3$，而 $(d_*)_1=1$。

先核对 guard。对任意 incoming guard $s\in\{0,1\}$，$U,V$ 的逐步 guard 分别为

$$
(s,1,0,0,0,0,0),\qquad (s,0,0,0,1,0,0).
$$

每个相邻 guard 和相应标签都满足定义14.5的合法边，两词均以 guard 零结束。因此它们可以前接任意实际 state-zero 尾；在每个前接来源内，下面的标量 $x$ 或 $y$ 始终指其同一个终尾的坐标。

对 $0\le j<6$，记 $P_{U,j}=f_{U_j}\circ\cdots\circ f_{U_5}$、$P_{V,j}=f_{V_j}\circ\cdots\circ f_{V_5}$。为显示全部六个后缀，置

$$
T_2=t^2,\qquad
L_1^\lambda=a-\lambda=-6T_2/5,\qquad
U_1^\lambda=b+\lambda=g-T_2/5,
$$

$$
\begin{aligned}
A(z)&=-t+gt+g^2z=L_1^\lambda+g^2(z-\theta),\\
B(z)&=gt+g^2z=U_1^\lambda+g^2(z-\theta),\\
u(x)&=-gA(x),\qquad v(y)=T_2-gB(y),\\
u_-&=u(T_2),\quad u_+=u(\theta),\qquad
v_-=v(\theta),\quad v_+=v(0).
\end{aligned}
$$

这里 $A=f_3\circ f_3$、$B=f_0\circ f_3$；所有表达式都是指定终尾的仿射函数。在闭比较区间 $x\in[\theta,T_2]$、$y\in[0,\theta]$ 上，它们的精确范围为

$$
\begin{array}{c|c|c|c|c}
j&P_{U,j}(x)&P_{U,j}([\theta,T_2])&
P_{V,j}(y)&P_{V,j}([0,\theta])\\ \hline
0&T_2-gB(u(x))&
[T_2-gB(u_+),T_2-gB(u_-)]&
-gA(v(y))&[-gA(v_+),-gA(v_-)]\\
1&B(u(x))&[B(u_-),B(u_+)]&
A(v(y))&[A(v_-),A(v_+)]\\
2&-t-gu(x)&[-t-gu_+,-t-gu_-]&
-t-gv(y)&[-t-gv_+,-t-gv_-]\\
3&u(x)&[u_-,u_+]&v(y)&[v_-,v_+]\\
4&A(x)&[L_1^\lambda,A(T_2)]&
B(y)&[gt,U_1^\lambda]\\
5&-t-gx&[-t-gT_2,-t-g\theta]&
-t-gy&[-t-g\theta,-t].
\end{array}
$$

这些行由最内层的末标签逐次前接得到，故不是六个独立选取的坐标。逐位置的严格颜色条件如下。由 $3/5<t<5/8$、(33.14) 及 $g^2<1/16<1/10$，有

$$
\begin{gathered}
0<\theta<T_2<t,\qquad
g^2T_2<\lambda,\qquad
L_1^\lambda+t=(11t-6)/5>0,\\
A(T_2)-a=g^2(T_2-\theta)-\lambda<0,\qquad
gt-b=\lambda-g^2\theta>0,\qquad
U_1^\lambda<g.
\end{gathered}
$$

所以位置 $4$ 的范围分别包含于 $[a-\lambda,a)$ 和 $(b,b+\lambda]$；其唯一半径 $\lambda$ 接触分别是 $x=\theta$ 与 $y=\theta$。同时 $A(x)\in(-t,-T_2)$、$B(y)\in(0,g)$，从而

$$
u(x)\in[gT_2,gt],\qquad
v(y)\in[T_2-g^2,T_2].
$$

令 $L_2^\lambda=b-\lambda=g-2T_2/5$、$U_2^\lambda=c+\lambda=t-2T_2/5$。下列正差核对位置 $3$ 的两个范围：

$$
\begin{aligned}
gT_2-L_2^\lambda&=T_2(2/5-T_2)>0,&
U_2^\lambda-g&=3T_2/5>0,&gt&<g,\\
T_2-g^2-g&=gT_2>0,&
U_2^\lambda-T_2&=(12t-7)/5>0.
\end{aligned}
$$

又有 $gt=T_2^2<T_2$，因此 $0<u(x),v(y)\le T_2$，且位置 $3$ 严格位于 $(L_2^\lambda,U_2^\lambda)$。位置 $1$ 所需的两个进一步分隔是

$$
\theta-gt=t(2/5-g)>0,\qquad
T_2-g^2-\theta=(33g-7)/10>0.
$$

于是

$$
0<B(u(x))<U_1^\lambda,\qquad
L_1^\lambda<A(v(y))<0.
$$

这就给出位置 $1$ 严格位于 $(L_1^\lambda,U_1^\lambda)$。其中 $B(u(x))<g$，而 $-t<A(v(y))<-T_2$，故位置 $0$ 分别位于 $[T_2-g^2,T_2]$ 和 $[gT_2,gt]$，也都严格位于 $(L_2^\lambda,U_2^\lambda)$。最后 $0<u(x),v(y)\le T_2<\phi$，且

$$
-t-gT_2>-1,\qquad a+t=(21t-11)/10>0.
$$

位置 $2,5$ 遂都严格位于 $(-1,a)$，可用零误差取得颜色 $0$。六个位置因此给出 $d_*$；在 $x>\theta,y<\theta$ 时，位置 $4$ 也严格位于扩张格内部。对任一内部闭格 $J_i=[l_i,r_i]$，若真值位于 $(l_i-\lambda,r_i+\lambda)$，则 $(z-\lambda,z+\lambda)\cap(l_i,r_i)\ne\varnothing$，从该交集取目标即得严格误差及内部颜色，不受切点归属影响。

两词的周期地址分别是命题28.3中周期来源的相位 $2$ 与相位 $5$，故其固定点是 (33.27) 的 $z_U,z_V$。也可将上述第零行在这些值处代入核对固定点。六步斜率为 $g^6$，给出 (33.28)，且

$$
z_U-\theta=\frac{39-6g}{380}>0,\qquad
T_2-z_U=\frac{15-52g}{76}>0,\qquad
z_V>0,\qquad
\theta-z_V=\frac{46+31g}{380}>0.
$$

因 $0<g^6<1$，(33.28) 是终尾与各自固定点的严格凸组合，证明两侧区间保持。

再给出 $C$ 的完整证书。记 $q_j=(A_j+B_jg)/10$，令 $q_{20}=q_0=\theta$。下表的 guard 指定每个接缝；最后两列分别是 $20(q_j-\min J_{(c_*)_j})$ 和 $20(\max J_{(c_*)_j}-q_j)$。

| 33.7 C 位置 | guard | 标签 | $(A_j,B_j)$ | 颜色 | 左内部差的分子 | 右内部差的分子 |
| --- | --- | --- | --- | --- | --- | --- |
| 33.7 C0 | $1\to1$ | $5$ | $(2,2)$ | $2$ | $7-19g$ | $1+11g$ |
| 33.7 C1 | $1\to1$ | $5$ | $(5,3)$ | $3$ | $5-9g$ | $3+21g$ |
| 33.7 C2 | $1\to0$ | $3$ | $(-8,0)$ | $0$ | $4$ | $5+11g$ |
| 33.7 C3 | $0\to0$ | $2$ | $(7,3)$ | $3$ | $9-9g$ | $21g-1$ |
| 33.7 C4 | $0\to0$ | $2$ | $(9,3)$ | $4$ | $5-21g$ | $3+13g$ |
| 33.7 C5 | $0\to0$ | $0$ | $(1,1)$ | $2$ | $5-21g$ | $3+13g$ |
| 33.7 C6 | $0\to0$ | $3$ | $(-5,-1)$ | $0$ | $10-2g$ | $13g-1$ |
| 33.7 C7 | $0\to0$ | $3$ | $(-4,0)$ | $1$ | $3-11g$ | $5+23g$ |
| 33.7 C8 | $0\to0$ | $3$ | $(-9,-1)$ | $0$ | $2-2g$ | $7+13g$ |
| 33.7 C9 | $0\to1$ | $25$ | $(12,4)$ | $5$ | $3-11g$ | $6+2g$ |
| 33.7 C10 | $1\to1$ | $5$ | $(3,3)$ | $2$ | $9-17g$ | $9g-1$ |
| 33.7 C11 | $1\to0$ | $0$ | $(0,2)$ | $1$ | $11-7g$ | $19g-3$ |
| 33.7 C12 | $0\to0$ | $0$ | $(-2,0)$ | $1$ | $7-11g$ | $1+23g$ |
| 33.7 C13 | $0\to0$ | $2$ | $(8,2)$ | $3$ | $11-11g$ | $23g-3$ |
| 33.7 C14 | $0\to0$ | $2$ | $(6,2)$ | $3$ | $7-11g$ | $1+23g$ |
| 33.7 C15 | $0\to1$ | $25$ | $(14,4)$ | $5$ | $7-11g$ | $2+2g$ |
| 33.7 C16 | $1\to0$ | $3$ | $(-5,1)$ | $0$ | $10+2g$ | $9g-1$ |
| 33.7 C17 | $0\to0$ | $3$ | $(-6,0)$ | $0$ | $8$ | $1+11g$ |
| 33.7 C18 | $0\to0$ | $0$ | $(-1,1)$ | $1$ | $9-9g$ | $21g-1$ |
| 33.7 C19 | $0\to1$ | $5$ | $(3,1)$ | $2$ | $9-21g$ | $13g-1$ |

逐行代入 $g^2+4g=1$ 得 $q_j=\Delta_{C_j}-gq_{j+1}$，包括末行返回 $q_{20}=\theta$。例如首行使用 $\Delta_5=(1-g)/2$，有 $10f_5(q_1)=5-5g-5g-3g^2=2+2g$；末行有 $10f_5(\theta)=5-5g-2g-2g^2=3+g$。所有 guard 边合法，末 guard 一与首 guard 一相接；首标签 $5$ 也允许从 guard 零开始。因此该表是合法周期地址 $C^\infty$ 的实际轨迹：二十步复合的斜率为 $g^{20}<1$，表中的固定点唯一。特别地，

$$
f_C(x)=\theta+g^{20}(x-\theta).
$$

表中的全部内部差严格为正。较小的差可直接用 (33.14) 核对：

$$
\begin{gathered}
5-21g>1/24,\qquad 3-11g>29/72,\qquad
7-19g>181/72,\\
13g-1>35/17,\qquad 9g-1>19/17,\qquad
19g-3>25/17,\qquad 21g-1>67/17,\qquad
23g-3>41/17.
\end{gathered}
$$

其余差由 $0<g<1/4$ 直接为正。故每个 $q_j$ 严格位于表列颜色格内部。对任意一个实际 guard-one 终尾标量 $x\in[0,T_2]$，其 $C$ 后缀坐标精确为

$$
P_{C,j}(x)=q_j+(-g)^{20-j}(x-\theta),\qquad 0\le j<20.
$$

位置 $j\le18$ 固定取目标 $q_j$，由于 $|x-\theta|\le T_2$，

$$
|P_{C,j}(x)-q_j|\le g^2T_2<R_C<\lambda.
$$

末位置取真实坐标为目标，误差为零，而

$$
P_{C,19}([0,T_2])=[T_2(1-g),T_2]\subset(b,c):
\quad T_2(1-g)=g+g^2>g>b,\quad
c-T_2=(5g-1)/4>0.
$$

这证明指定的整词 $c_*$ 可在一个实际终尾前同时实现。全部目标在格内部，裁剪固定目标，任何固定切点归属均适用。中心返回式还给出 $f_C([0,T_2])\subseteq[0,T_2]$、$f_C(H)\subseteq H$ 和 $f_C(L)\subseteq L$；每个有限复合保持两侧的严格分隔。

取 $\chi=g^{20}$、$\varsigma=g^{60}$。两种二进制选择在 A、B 两个分量中的来源词和共同颜色词为

$$
\begin{array}{c|c|c|c}
\text{选择}&\text{A 分量}&\text{B 分量}&\text{共同颜色}\\ \hline
0&U^{10}C^2&V^{10}C^2&d_*^{10}c_*^2\\
1&CU^{10}C&CV^{10}C&c_*d_*^{10}c_*.
\end{array}
\tag{33.30}
$$

每个块的长度都是 $60+40=100$，从 guard 一出发并回到 guard 一。令高侧位移为 $D=x-\theta$，低侧位移为 $D=\theta-y$。按来源词的外到内复合约定，精确返回映射为

$$
\begin{aligned}
F_0^H(D)&=(1-\varsigma)h+\varsigma\chi^2D,&
F_1^H(D)&=\chi(1-\varsigma)h+\varsigma\chi^2D,\\
F_0^L(D)&=(1-\varsigma)\ell+\varsigma\chi^2D,&
F_1^L(D)&=\chi(1-\varsigma)\ell+\varsigma\chi^2D.
\end{aligned}
\tag{33.31}
$$

其中选择 $0$ 的两个 $C$ 都在内层；选择 $1$ 有一个内层 $C$ 和一个外层 $C$。对尾输入总是最右侧的内层映射先作用；选择 $1$ 的外层 $C$ 最后作用，使其最终返回位移带有外层因子 $\chi$；(33.31) 记录了这两个复合顺序的差别。

**引理 33.8（闭返回矩形与每个中间输入）。** 置

$$
\delta_H=\chi(1-\varsigma)h,\qquad
\delta_L=\chi(1-\varsigma)\ell,\qquad
H_0=[\theta+\delta_H,t^2],\qquad L_0=[0,\theta-\delta_L],
\tag{33.32}
$$

以及

$$
H_1=[\theta+\chi^2\delta_H,t^2],\qquad
L_1=[0,\theta-\chi^2\delta_L].
\tag{33.33}
$$

则四个映射 (33.31) 保持 $H_0\times L_0$。在任一选择的十次 $U$ 或 $V$ 运行中，每个单独 $U/V$ 块的实际终尾都在 $H_1\times L_1$；固定词 $UC,VC$ 的单独块也有此性质。每个 $C$ 块的终尾属于 $[0,t^2]$。

证明。$h<t^2-\theta$、$\ell<\theta$ 且 $0<\chi,\varsigma<1$，故 (33.32) 非空。映射的常数项至少为 $\delta_H$ 或 $\delta_L$；在上端点使用单调性和凸组合即得上界 $t^2-\theta$ 或 $\theta$，所以矩形不变。选择 $0$ 在进入最内层 $U/V$ 前已经通过 $C^2$，选择 $1$ 通过一个 $C$；因此每个十次运行的最小位移至少为 (33.33) 的端点。再向外应用 (33.28)，因 $h>\chi^2\delta_H$、$\ell>\chi^2\delta_L$，下界和上界均保持。词 $UC,VC$ 的终尾经过一个 $C$，给出更大的下界。$C$ 在两侧半区间内保持实际尾域，故其终尾都在 $[0,t^2]$。$\square$

**定义 33.9（统一 U/V 端点余量）。** 对六个后缀仿射图

$$
P_{U,j}=f_{U_j}\circ\cdots\circ f_{U_5},\qquad
P_{V,j}=f_{V_j}\circ\cdots\circ f_{V_5},\qquad 0\le j<6,
$$

定义 $\rho_U$ 为下列有限端点集上的最大距离：

$$
\begin{aligned}
\rho_U=\max\{&\operatorname{dist}(P_{U,j}(x),J_{(d_*)_j}):
 x\in\{\theta+\chi^2\delta_H,t^2\},\\
&\operatorname{dist}(P_{V,j}(y),J_{(d_*)_j}):
 y\in\{0,\theta-\chi^2\delta_L\},\ 0\le j<6\}.
\end{aligned}
\tag{33.34}
$$

**定理 33.10（统一的真实误差余量）。** 有

$$
0\le\rho_U<\lambda,\qquad
R_*:=\max\{\rho_U,R_C\}<\lambda,\qquad
\boxed{\nu_0:=\frac{\lambda+R_*}{2}<\lambda},
\tag{33.35}
$$

且 $\nu_*<\nu_0$。

证明。定义33.7的六行精确后缀范围覆盖 $[\theta,t^2]$、$[0,\theta]$ 上每个实际坐标，其中只有位置 $4$ 在 $\theta$ 处达到半径 $\lambda$。引理33.8给出 $\chi^2\delta_H>0$、$\chi^2\delta_L>0$，故在 (33.33) 的闭区间上

$$
P_{U,4}(x)\ge a-\lambda+g^2\chi^2\delta_H>a-\lambda,\qquad
P_{V,4}(y)\le b+\lambda-g^2\chi^2\delta_L<b+\lambda.
$$

位置 $4$ 的另一端分别严格小于 $a$、严格大于 $b$；其余五个位置在更大的闭比较区间上已经严格位于相应扩张格内部。因此 (33.34) 的每个端点距离都严格小于 $\lambda$，有限最大值给出 $\rho_U<\lambda$。距离到闭区间经过仿射图后是凸函数，它在 $H_1,L_1$ 上的最大值出现在端点，所以这一界覆盖引理33.8的每个中间输入，并非只控制返回点。再由 (33.29)，$R_*<\lambda$，且 $R_*<\nu_0<\lambda$。令

$$
\alpha=\frac{\nu_0-\rho_U}{2\phi^2}>0,\qquad
T_i(z)=(1-\alpha)\operatorname{proj}_{J_i}(z)+\alpha m_i,
$$

其中 $m_i$ 是 $J_i$ 的中点。由于 $\nu_0>\rho_U\ge0$ 且 $\nu_0<\lambda<2\phi^2$，

$$
0<\alpha\le\frac{\nu_0}{2\phi^2}<1.
$$

因此 $T_i(z)$ 位于颜色格内部，且 $\operatorname{diam}X=\phi^2$，故每个 $U/V$ 坐标可用一个实际目标实现，误差至多

$$
\rho_U+\alpha\phi^2=\frac{\rho_U+\nu_0}{2}<\nu_0.
\tag{33.36}
$$

$C$ 块使用 (33.29) 的固定内部目标及其末位零误差。因此所有同一实际来源上的有限前缀都有一个共同误差上界

$$
R_0=\max\left\{\frac{\rho_U+\nu_0}{2},R_C\right\}<\nu_0.
\tag{33.37}
$$

不需要把不同坐标的标量见证拼成不同来源。

为了比较两个预算，注意 $\max\{\rho_U,R_C\}\ge R_C$，而不计算 $\rho_U$ 也有

$$
\nu_0\ge\frac{3\lambda+g^2t^2}{4}=\frac{53-213g}{80}.
$$

由 (33.14)，

$$
\frac{53-213g}{80}-\nu_*=\frac{341-1437g}{400}>0.
\tag{33.38}
$$

故 $\nu_*<\nu_0$。$\square$

### 33.4 实际历史族与线性配置下界

**定理 33.11（同一未来后缀的二进制静默族）。** 对每个 $n\ge0$，存在 $2^n$ 个实际颜色历史，长度为

$$
N_n=26+100n,
\tag{33.39}
$$

其共同误差上界为同一个 $R_0<\nu_0$，并具有以下性质：每个历史有两个首窗口不同的实际完成来源；所有 A 分量都可接同一个完整未来颜色后缀。

证明。固定实际退出

$$
\tau_A=5\,0^\infty,\qquad \tau_B=0^\infty,
$$

其标量分别为 $t^2\in H_0$ 和 $0\in L_0$，零误差颜色分别为

$$
S_A=(2,1,1,\ldots),\qquad S_B=(1,1,1,\ldots).
\tag{33.40}
$$

固定 stem 为 $(UC,VC)$，从初始 guard 零合法开始，长度 $26$，共同颜色为 $d_*c_*$，并以 guard 一结束。给定二进制词 $z=z_1\cdots z_n$，按 (33.30) 在 A、B 两分量各选对应的百步块，得到来源 $\alpha_z,\beta_z$。由引理33.8，所有返回点及每个中间 $U/V$ 输入都在同一闭矩形；由定理33.10，每一个坐标在这些**同一实际来源**上都能以误差至多 $R_0$ 得到规定颜色。将固定退出接到其后并取零误差，得到

$$
h_zS_A\quad\text{和}\quad h_zS_B,
\tag{33.41}
$$

其中

$$
h_z=d_*c_*\,v_{z_1}\cdots v_{z_n},
$$

$$
v_0=d_*^{10}c_*^2,\qquad v_1=c_*d_*^{10}c_*.
$$

所有 $h_z$ 长度都是 (33.39)。由 $(d_*)_1=1$ 和 $(c_*)_1=3$，两个百步颜色块 $v_0,v_1$ 的第二个颜色分别为 $1,3$，所以 $v_0\ne v_1$。两个块长度同为 $100$，共同前缀长度固定，故 $z\mapsto h_z$ 是单射，确有 $2^n$ 个不同颜色历史。

每个 A 分量的首次二进制差别出现在一个百步块的第二个来源窗口：选择 $0$ 给出 $0$，选择 $1$ 给出 $5$；因此 A 来源词两两不同。B 分量的首窗口为 $0$，A 分量的首窗口为 $5$，所以在读完 $h_z$ 时尚不能发出任何标签。$\square$

**推论 33.12（完整配置的线性容量下界）。** 任何确定、因果、按序、追加输出的正确解码器，在预算 $\nu_0$ 下于长度 $N_n$ 的某个检查点需要至少 $2^n$ 个两两不同的完整持久配置；固定宽度二进制表示因此至少需要 $n$ 位容量，亦即

$$
\operatorname{Mem}_{\rm peak}(N_n)\ge \frac{N_n-26}{100}.
\tag{33.42}
$$

证明。若两个不同的 $z,z'$ 在各自的 $h_z,h_{z'}$ 后有同一完整配置，则把两次运行都继续接同一个可读未来颜色后缀 $S_A$。此前输出均为空，确定性迫使未来输出相同；但 A 分量的要求来源词在首次不同的百步块处已经不同，矛盾。故配置至少有 $2^n$ 个。所有输入长度相同，读取的采集计数、时钟或重放位置不能把这些配置免费合并；任何可读的历史、输出存储、计数器或辅助缓存都属于完整配置。固定宽度编码给出 $n$ 位下界；变长二进制串最大长度少于 $n$ 时总数不超过 $2^n-1$，同样不能容纳这族配置。它是不同实际来源造成的峰值下界，不说一个固定来源的内存永远增长。$\square$

### 33.5 线性上界与两区间结论

**定理 33.13（临界闭图的线性峰值上界）。** 沿用第29.8节的有限闭覆盖和共同来源提升，在闭预算 $\lambda$ 下存在一个固定确定的有序流式解码器，使每个实际 $\Omega$ 记录的输出始终为真实来源前缀、每个 $D$ 记录的每个窗口最终输出，并且在取得 $N$ 个颜色后的全部工作及持久存储峰值满足

$$
\operatorname{Mem}(N)\le C(N+1)
\tag{33.43}
$$

其中 $C$ 只依赖固定图、字母表和编码约定。

证明。对第 $n\ge1$ 次取得阶段，令 $k$ 为阶段开始时的已输出窗口数。解码器从 $k=0$ 开始，每个取得阶段先取得一个新颜色，完成一次下述测试后至多输出一个标签，再进入下一次取得；因此处理新取得的第 $n$ 个颜色时，先前只有 $n-1$ 个取得阶段，不变量 $k\le n-1$ 成立。由此 $L=k+1\le n$，对当前长度 $n$ 的颜色词取

$$
L=k+1,\qquad M=\max\{n-1,L\}\le n.
\tag{33.44}
$$

在第29.8节的有限图上按固定边序作深度优先遍历，保留深度不超过 $M$ 的一条路径、长度不超过 $L$ 的第一条参考来源词和常数个比较标志。节点在深度 $j<n$ 时只接受已取得颜色 $r_j$；之后不再附加颜色约束。第29.8节的共同尾提升说明，这个有限路径测试所得的长度 $L$ 来源词集合，正好是满足全部闭颜色约束的实际共同来源集合的投影；不同路径产生同一来源词时只保留一份参考词，不以路径数充当来源数。搜索若遇到两个不同参考词即返回多词，若无路径返回空，若只保留一个词返回单词。

有限分支和深度保证测试终止。每个栈帧只存一个固定图节点、下一条边的固定索引和一个固定字母表标签，帧数不超过 $M+1$；当前路径词、参考词和已取得颜色历史各为 $O(N+1)$。全局深度、扫描位置、$n,k,L,M$ 和有限旗标只需 $O(\log(N+2))$ 位，临时比较空间在路径之间复用。因此存在固定 $C$ 使整个阶段、包括临时 DFS 峰值，都满足 (33.43)。

若测试为单词，输出其最后一个标签并使 $k$ 增一；空或多词则不输出。真实 $\Omega$ 来源始终在候选集合内，所以单词输出安全。对 $D$，第30.10节的共同来源紧致性和逐位置论证保证每个固定位置最终达到单词测试；推理只使用同一实际来源的闭约束，不把空集当成认证。已输出标签不再作为可读历史保存，输入历史和所有可读位置均已计入上界。$\square$

记号约定：定理33.14与定义33.16（包括 (33.48)）中的记忆阶数均指正确解码器的最优最坏情形完整内存阶数。$\Theta(N+1)$ 表示每个正确解码器都有 $\Omega(N+1)$ 的最坏情形峰值下界，而定理33.13所构造的一个固定解码器达到 $O(N+1)$ 上界；这不对任意低效的正确解码器主张同样的上界。

**定理 33.14（两个已证区间和未决中间带）。** 在同一固定仪器、固定归属、逐坐标误差合同和按序追加输出合同下：

1. 对每个 $0\le\nu\le\nu_*$，定理33.6给出固定五色缓冲、暖机长度四和常数完整内存；
2. 对每个 $\nu_0\le\nu\le\lambda$，定理33.13给出线性峰值上界，而推论33.12由误差合同包含关系首先在 $N_n=26+100n$ 给出线性下界。对任意 $N\ge26$，取 $n=\lfloor(N-26)/100\rfloor$，则 $N_n\le N$；最坏情形的截至取得 $N$ 次的峰值随 $N$ 单调不减，故

   $$
   \operatorname{Mem}_{\rm peak}(N)\ge\operatorname{Mem}_{\rm peak}(N_n)\ge\left\lfloor\frac{N-26}{100}\right\rfloor.
   $$

   结合线性上界，并将有限初始范围吸收进 $\Theta$ 常数，得到

   $$
   \boxed{\operatorname{Mem}_{\rm peak}(N)=\Theta(N+1)};
   $$
3. 由于 $\nu_*<\nu_0$，区间 $(\nu_*,\nu_0)$ 的统一最优记忆阶数和精确有限延迟阈值在本章没有结算；$\nu_*$ 只对三次采集的局部传播蕴含是精确上界，命题33.15也只反驳该局部蕴含在更大预算下的延伸。

这里的两个区间是存在性和容量结论，不构成一个全局精确阈值。它们不推出物理时间箭头、所有有限系统的不可避免遗忘、尖锐常数、实时处理效率、最优状态数、End 或来源支撑认证。

### 33.6 局部常数的实际反例与全域碰撞边界

**命题 33.15（局部传播常数的实际精确性）。** 对任意 $\nu>\nu_*$，存在两个实际合法来源，它们在三个连续观测上产生共同颜色词 $(1,0,2)$，首标签分别为 $3,0$，第二标签共同为 $3$；所有目标都在各自颜色格内部，且可接完整合法的未来尾。因此更大预算下失败的只是定理33.3所用的三次采集局部传播蕴含。

证明。令

$$
 k=K_1,\qquad s=\frac{g-7}{10},\qquad z=\frac{1+g}{5},\qquad q=\frac{8-g}{50},
$$

并取两个 state-zero 合法尾 $\eta^+,\eta^-$，其当前标量为

$$
 y^+=z+q=\frac{18+9g}{50},\qquad y^-=z-q=\frac{2+11g}{50}.
\tag{33.45}
$$

来源 $(3,3)\eta^+$ 和 $(0,3)\eta^-$ 都合法。前三个真实坐标为

$$
\begin{array}{c|cc}
& (3,3)\eta^+&(0,3)\eta^-\\ \hline
0&a-\nu_*&b+\nu_*\\
1&(-34-7g)/50&(-36+17g)/50\\
2&(18+9g)/50&b-\nu_*.
\end{array}
\tag{33.46}
$$

中间一行严格在颜色 $0$ 内，$y^+$ 严格在颜色 $2$ 内。给定 $\nu>\nu_*$，取

$$
0<\epsilon<\min\{\nu-\nu_*,(b-a)/2,c-b\}.
$$

第一坐标分别取内部目标 $a+\epsilon,b-\epsilon$，第二坐标取零误差，第三坐标分别取 $y^+$ 和内部目标 $b+\epsilon$。三个非零误差的大小均为 $\nu_*+\epsilon<\nu$；两条记录遂均为 $(1,0,2)$，且两来源的下一标签都是 $3$。目标都在格内部，之后接各自的实际合法尾即可。$\square$

第28.2节的命题28.3在全 $\Omega$ 上的实际周期碰撞另给出独立半径

$$
\rho_{\rm col}=\frac{44g-5}{152},\qquad
\rho_{\rm col}-\nu_*=\frac{597-2434g}{3800}>0.
\tag{33.47}
$$

闭合同在 $\nu=\rho_{\rm col}$ 时直接使用命题28.3的内部目标。正开合同的等号还需一个严格见证：沿用该命题的实际周期坐标 $z_j$，记 (28.12) 的三个正距离为

$$
A_p=a-z_0,\qquad B_p=z_3-b,\qquad C_p=b-z_5,
\qquad 0<B_p,C_p<A_p<\lambda.
$$

把其位置 $0,3,5$ 的内部目标分别取为

$$
a+\frac{\lambda-A_p}{4},\qquad
b-\frac{\lambda-B_p}{4},\qquad
b+\frac{\lambda-C_p}{4},
$$

其余位置仍取 $z_1,z_2,z_4$。这把 (28.15) 的三个内部偏移各缩小一半，目标仍严格在原颜色格内。三个非零误差的绝对值分别为 $(\lambda+3A_p)/4$、$(\lambda+3B_p)/4$、$(\lambda+3C_p)/4$，故整条周期误差的共同上界为

$$
\frac{\lambda+3A_p}{4}
<\frac{\lambda+A_p}{2}
=\rho_{\rm col}.
$$

第二来源使用同一组三位循环移位的目标，仍给完整共同记录 $(1,0,2)^\infty$。因此对闭合同及正开合同，在 $\nu\ge\rho_{\rm col}$ 时，要求对全部 $\Omega$ 来源恢复首标签的解码器即使允许完整无限记录也不能正确。这不妨碍只要求 $\Omega$ 安全、$D$ 逐位置生效的解码器；它也不是把局部三次反例提升成全局有限延迟结论。由 (33.38) 只比较预算次序，不需要计算 $\rho_U$。全流碰撞、五次局部分离和两区间内存结论的量词分别是完整记录、五色前缀和完整有序输出，不能互相替代。

**定义 33.16（两区间折叠记忆律）。** 在本章的固定观察合同和非负噪声域 $\nu\ge0$ 下，把“同一折叠几何”理解为 (33.1)--(33.3) 的地址、分支、切点和 guard 不变，把“边界需保留的历史量”理解为完成正确有序输出所需的完整可读配置。则

$$
0\le\nu\le\nu_*\quad\Longrightarrow\quad O(1),
\qquad
\nu_0\le\nu\le\lambda\quad\Longrightarrow\quad \Theta(N+1).
\tag{33.48}
$$

这一定义只记录已证的两个预算区间；它不把中间带压成一个未经证明的阈值，也不把观察精度变化解释成普遍物理时间或空间起源。对本章范围内的迭代问题，答案是：在几何与有序重建任务相同而观测精度提高时，边界所需保留的历史可以从线性增长降为固定四格颜色缓冲；在 $(\nu_*,\nu_0)$ 内，所需历史阶数仍是开放的。

## 追加锚（33·本行以下为增补区）

## 34. 两个实际端点的尖锐前缀恢复、有限尾差值与操作访问

### 34.甲 两次取得、共同来源与前缀残差

本章固定已知整数 $n\ge1$，只取得同一实际来源在删去 $n$ 个三位窗口前后的两个标量。恢复目标是被删去的前 $n$ 窗，而不是完整来源、支持长度或结束位置。第16章的实际相邻样本结果在 $n=1$ 时是本章等半径结论的前例；对 $n>1$，本章不取得中间样本。第23章的码本间距、第14与17章的 guard 几何及第22章的精确当前值访问分别承担不同前提。

**定义 34.1（两个实际端点与误差合同）。** 沿用定义1.1、14.5与17.1，置

$$
t=\phi^{-1}=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
R=\mathbb Z[t],\qquad K=\mathbb Q(t),
$$

$$
g=t^3,\qquad \gamma=-g,\qquad N=3n,\qquad
a=g^n,\qquad \sigma=(-1)^n,\qquad c=\gamma^n=\sigma a,
\qquad \delta=\delta_n=t^{3n-1}=\phi a.
$$

$\Omega$ 是起始 guard 零的全部合法单侧地址，$D\subset\Omega$ 是最终全零的地址；外部单位位固定为零，高位补零不提供独立长度坐标。窗口标签仍为

$$
(0,2,3,25,5)=(000,100,010,101,001),\qquad 0=\mathrm{null},
$$

$$
(\Delta_0,\Delta_2,\Delta_3,\Delta_{25},\Delta_5)
=(0,1,-t,2-t,t^2).
$$

删除 $T$ 每次删去三位。对一条实际来源 $\omega$，两个真实坐标与目标为

$$
x_0=\kappa_0(\omega),\qquad x_n=\kappa_0(T^n\omega),\qquad
P_n(\omega)=(\omega_0,\ldots,\omega_{N-1}).
$$

这里 $P_n$ 写成 $N$ 个位，与前 $n$ 个窗口等价。实际取得的记录是

$$
r=(r_0,r_n)=(x_0+e_0,x_n+e_n)\in\mathbb R^2.
$$

两个误差独立允许，意指合同涵盖全部允许的误差对，不作随机独立性假设。没有中间样本、量化器、受限记录字母表或统一尾支持上界；两次真实坐标始终由同一来源共同给出。闭合同取有限非负半径 $\varepsilon_0,\varepsilon_n$，要求 $|e_0|\le\varepsilon_0,|e_n|\le\varepsilon_n$。正开合同取两个正半径并将两处不等式改为严格；正混合合同取两个正半径，恰有一处严格。记

$$
H=\varepsilon_0+a\varepsilon_n.
$$

“恢复”先指存在一个精确实记录上的确定函数，对每条允许来源及每个允许误差对返回 $P_n$。实际有效记录域之外的输出任意。普通 Cauchy 近似访问、连续性及终止性另行讨论，不能由这个函数的集合论存在直接取得。

对合法长度 $N$ 位前缀 $u$，令末 guard 为 $s(u)=u_{N-1}$，并置

$$
A(u)=\sum_{j=0}^{N-1}u_j(-t)^j,
\qquad I_0=[-1,\phi],\qquad I_1=[-1,t],
$$

$$
T_s=\{\kappa_s(\eta):\eta\text{ 从 guard }s\text{ 合法且最终全零}\}.
$$

状态下标只限制合法尾域，不改变同一地址的标量级数。实际分支方程逐次展开给出

$$
x_0=A(u)+cx_n,\qquad A(u)=x_0-cx_n.
$$

因此前缀 $u$ 的精确共同端点集合为

$$
E_u^\Omega=\{(A(u)+cy,y):y\in I_{s(u)}\},\qquad
E_u^D=\{(A(u)+cy,y):y\in T_{s(u)}\}.
$$

定理17.2的状态相对满像和合法前接使第一式的每一点都由一条实际完整来源取得；第二式使用实际有限尾。每个 $T_s$ 是可数的，包含零，属于 $R$，并在 $I_s$ 中稠密：固定一条合法尾，保留越来越长的前缀后补零即可。命题14.6的极值尾非有限，故

$$
T_0\subset R\cap(-1,\phi),\qquad T_1\subset R\cap(-1,t).
$$

这些共同端点集合不是两个边缘区间的乘积。即使 $A(u)$ 落在一个有限码本中，实际来源及其尾也没有因此获得支持上界证书。

### 34.乙 既有间距与全部临界前缀对

**命题 34.2（前缀码本与最小间距对的分类）。** 前缀残差码本恰为第23章的 $S_N$：

$$
\mathcal A_n=\{A(u):u\text{ 合法且长度为 }N\}=S_N,
\qquad \min_{u\ne v}|A(u)-A(v)|=\delta.
$$

$A$ 对这些前缀单射。两个不同前缀的码距等于 $\delta$，当且仅当它们只在最后一位不同。每一对可以唯一写成 $u^0=p0,u^1=p1$，其中 $p$ 长度为 $N-1$、合法且末位为零；末 guards 分别为 $0,1$，并且

$$
A(u^1)-A(u^0)=(-t)^{N-1}=-\sigma\delta.
$$

证明。前缀补零的实际来源值正是 $A(u)$，所有 $D_N$ 地址也这样给出一个前缀，所以码本相等。单射性复用定理14.7后的有限来源单射性；间距直接使用定理23.2，不重证其全点对间距。

为分类等号对，若首个不同位是 $j\le N-2$，共同前一位必为零（$j=0$ 时无此前一位），于是删去共同前缀后得到 $M=N-j\ge2$ 的两个不同初位块。定理23.2已给出这两块之间的达到间隙 $t^{M-2}$。恢复共同前缀只乘以 $(-t)^j$，所以原码距至少为

$$
t^jt^{M-2}=t^{N-2}>t^{N-1}=\delta.
$$

因此最小对只能在末位分歧。反向只在末位分歧时码差恰为 $(-t)^{N-1}$；合法性又强制共同倒数第二位为零。这证明所有最小对的分类。$\square$

若 $p0,p1$ 的真实尾分别为 $y_0,y_1$，记 $h=y_1-y_0$，则它们同一来源方程给出的当前差是

$$
x_0^1-x_0^0=\sigma(ah-\delta).
$$

对任意两个不同前缀的共同端点对，记其最大范数距离为 $D_{\rm pair}$，有

$$
\delta\le |A(u)-A(v)|
\le |x_0-x'_0|+a|x_n-x'_n|
\le(1+a)D_{\rm pair}.
$$

对实际记录则计算可见残差

$$
b(r)=r_0-cr_n=A(u)+e_0-ce_n.
$$

闭合同下 $|b(r)-A(u)|\le H$；正开或正混合合同下严格小于 $H$。这个尾消去恒等式只使用两个已经取得的实际坐标，不生成一次新的测量。

### 34.丙 实际有限尾差值的完整条带

**定理 34.3（指定 guards 的有限尾差值）。** 有精确集合等式

$$
\boxed{T_1=-tT_0,\qquad T_1-T_0=R\cap(-\phi^2,\phi).}
$$

特别地，$(T_1-T_0)\cap[0,\phi)=R\cap[0,\phi)$。右侧每个差值都由两条实际有限合法尾精确实现，而非只由一个趋近序列逼近。

证明。guard 一的尾首位必须为零；删去这一个零位得到任意 guard 零尾，反向前接一个零位也始终合法。位级数给出 $T_1=-tT_0$。这是实际地址的字面前接操作，重新分成三位窗口后仍是同一固定原点和外部单位位合同，并非更换标量坐标。

有限尾的严格端点界给出

$$
T_1-T_0\subset R\cap(-1-\phi,t+1)
=R\cap(-\phi^2,\phi).
$$

反向使用约定1.3的实际正数量条带输入。对 $x=A+Bt\in R$，定义整数数量泛函

$$
\mathsf q(x)=2A-3B.
$$

它对应整数组成 $(A,-B)$，其标量是 $A+Bt$。约定1.3给出的充分条件是

$$
x\in R,\qquad -1<x<\phi,\qquad \mathsf q(x)>0
\quad\Longrightarrow\quad x\in T_0.
$$

零来源另由命题1.2处理。命题1.2还给出单个实际占位的数量

$$
\mathsf q((-t)^j)=F_{j+3}\qquad(j\ge0).
$$

固定任意 $h\in R\cap(-\phi^2,\phi)$。为实现 $h=y-z$，需要 $y\in(-1,t)$ 且 $z=y-h\in(-1,\phi)$，即

$$
J_h=(L,U),\qquad L=\max(-1,h-1),\qquad U=\min(t,h+\phi).
$$

所给 $h$ 的界恰使 $L<U$，而 $L,U\in R$。选择整数 $m\ge1$ 使 $0<t^{2m}<U-L$，置 $w=U-t^{2m}\in R\cap J_h$。对 $k>m$ 置

$$
y_k=w+t^{2k},\qquad z_k=y_k-h,\qquad x_k=-\phi y_k.
$$

由于 $L<w<y_k<U$，有

$$
-1<z_k<\phi,\qquad -1<x_k<\phi.
$$

此时不能只凭环成员和区间位置宣告有限来源。还须同时使两个实际整数数量为正。利用加性及单占位数量式，得到

$$
\begin{aligned}
\mathsf q(z_k)&=\mathsf q(w-h)+F_{2k+3},\\
\mathsf q(x_k)&=\mathsf q(-\phi w)+F_{2k+2},
\end{aligned}
$$

其中 $-\phi t^{2k}=-t^{2k-1}=(-t)^{2k-1}$。两个固定项都是整数；Fibonacci 项趋于正无穷，所以同一个充分大的 $k$ 使两处严格正性同时成立。约定1.3于是分别提供实际有限 guard 零尾 $\alpha_k,\beta_k$，其标量为 $x_k,z_k$。前接一个零位得到实际有限 guard 一尾 $0\alpha_k$，并且

$$
\kappa_1(0\alpha_k)=-t x_k=y_k,
\qquad \kappa_1(0\alpha_k)-\kappa_0(\beta_k)=y_k-z_k=h.
$$

这给出逆包含，证明完整条带。$\square$

这里使用的是严格正整数数量 $\mathsf q$，不是经典黄金基整数的非负共轭实坐标。约定1.3所区分的两种正性保持各自的前提；本章复用母卷输入，不重新审计其证明。差值条带也不意味着单尾等式 $T_s=R\cap\operatorname{int}I_s$：例如 $t\in R\cap(-1,\phi)$ 却有 $\mathsf q(t)=-3$，不是实际 guard 零有限尾。上面的共同小位平移使两个数量同时为正，同时精确保留指定差值。

### 34.丁 闭误差的完整非负象限

**定理 34.4（闭合同的尖锐区域）。** 对两个闭误差半径，$\Omega$ 上恢复当且仅当

$$
\boxed{H<\delta/2.}
$$

$D$ 上的完整区域为：精确当前轴 $\varepsilon_0=0$ 允许任意 $\varepsilon_n\ge0$；当 $\varepsilon_0>0$ 时，严格低于加权边界可以恢复，严格高于边界不能恢复。在边界

$$
\varepsilon_0>0,\qquad H=\delta/2,
\qquad h=2\varepsilon_n\in[0,\phi),
$$

恢复失败当且仅当 $h\in R$，等价地，恢复当且仅当 $h\notin R$。这里 $h<\phi$ 是必要范围，不能删去后仍使用环判据。

证明。闭合同下若同一记录与两个不同前缀的实际来源相容，则

$$
\delta\le |A(u)-A(v)|
\le |x_0-x'_0|+a|x_n-x'_n|
\le2\varepsilon_0+2a\varepsilon_n=2H.
$$

因此 $H<\delta/2$ 禁止碰撞；此时残差 $b(r)$ 距真实码值严格小于半间距，有限码本的唯一最近码恢复前缀。

为核对整个 $\Omega$ 象限及尾区间饱和，取实际合法前缀

$$
u^0=0^N,\qquad u^1=0^{N-1}1,
$$

即窗口前缀 $0^n$ 与 $0^{n-1}5$。对任意 $h\in[0,\phi]$，选择尾标量

$$
y_0=-th\in I_0,\qquad y_1=t^2h\in I_1.
$$

它们满足 $y_1-y_0=h$；分别按定理17.2选择一条实际尾并合法前接，便得到两条共同端点方程成立的完整来源。两个端点分离为

$$
|x_n^1-x_n^0|=h,\qquad |x_0^1-x_0^0|=\delta-ah.
$$

取 $h=\min(2\varepsilon_n,\phi)$。对于所有不同前缀的来源，在终端差至多 $2\varepsilon_n$ 的约束下，当前差的最小值因此恰为

$$
Q(\varepsilon_n)=\max(\delta-2a\varepsilon_n,0).
$$

下界由码距不等式给出，上述同一实际端点对达到它。两个闭误差矩形相交恰在两处真实坐标差分别不大于两倍半径时；其坐标中点就是一个共同记录。因此闭碰撞存在恰在 $2\varepsilon_0\ge Q(\varepsilon_n)$，即 $H\ge\delta/2$。

饱和处 $h=\phi$ 给出 $y_0=-1,y_1=t$ 和相同当前坐标。它们来自两个不同末位的实际完成来源；闭终端半径达到 $\phi/2$ 后，即使当前值精确也不能在 $\Omega$ 上恢复。饱和不为加权严格区域之外增加恢复点。

转到 $D$，若 $\varepsilon_0=0$，则 $r_0=\kappa_0(\omega)$。定理14.7后的有限来源单射性使其集合论上确定整个有限地址，因而确定目标前缀，终端记录可不使用。第22章另外给出固定前缀的 Cauchy 访问；这与完成域的端点碰撞不同。

设 $\varepsilon_0>0,H>\delta/2$。若 $\varepsilon_n=0$，给上述两个前缀都接零尾，真实终端相同、当前差为 $\delta<2\varepsilon_0$，所以已有实际 $D$ 碰撞。若 $\varepsilon_n>0$，选择

$$
\max\left(0,\frac{\delta-2\varepsilon_0}{a}\right)
<h<\min(2\varepsilon_n,\phi).
$$

边界严格超出且 $\varepsilon_0>0$ 保证这个区间非空。固定上面 $y_0=-th,y_1=t^2h$ 的两条合法完成尾；分别截断并补零。两个实际有限尾同时趋近指定尾值，故由同一仿射方程给出的两处严格分离界

$$
|x_n^1-x_n^0|<2\varepsilon_n,\qquad
|x_0^1-x_0^0|<2\varepsilon_0
$$

在足够长的同次截断后同时保留。中点记录便是实际有限来源碰撞。这里没有独立近似两个坐标的边缘极值。

最后设 $\varepsilon_0>0,H=\delta/2$。任何闭碰撞都强制码距链每处取等号，故由命题34.2属于 $p0,p1$ 最小对。令两条实际尾差为 $d=y_1-y_0$，并记 $h=2\varepsilon_n$。边界给出

$$
2\varepsilon_0=\delta-ah>0,\qquad 0\le h<\phi.
$$

终端与当前碰撞条件为

$$
|d|\le h,\qquad |\delta-ad|\le\delta-ah.
$$

因 $d\le h<\phi$，第二式只能在 $d\ge h$ 时成立，所以 $d=h$。这证明实际有限尾差值条件 $h\in T_1-T_0$ 对每一个临界碰撞都是必要的。反向一旦实际有限尾达到该差值，把它们接到 $0^N,0^{N-1}1$，两处差就分别为 $2\varepsilon_0,2\varepsilon_n$，中点造成闭碰撞。定理34.3在必要范围 $[0,\phi)$ 内将此条件精确化为 $h\in R$。

若 $h\notin R$，每份有效记录的所有相容来源给出同一目标前缀；按它定义函数，再在无效输入处任意补全，即得集合论恢复。$\square$

特别地，边界的 $h=0$ 失败，因为两条零尾已达到差零；$h=1$ 也失败，例如 guard 一有限尾 $5\,0^\infty$ 的标量为 $t^2$，guard 零有限尾 $3\,0^\infty$ 的标量为 $-t$，两者差为一。另一方面，$\phi\in R$ 却不属于 $T_1-T_0$，所以环判据不能越过 $h<\phi$ 的正当前半径条件。精确当前轴也不能用该条件替代。

### 34.戊 正开、正混合合同及精确坐标轴

**定理 34.5（严格误差与非空坐标轴）。** 两个正半径下，正开合同及正混合合同在 $\Omega,D$ 上的恢复条件均恰为

$$
\boxed{H\le\delta/2.}
$$

精确坐标是非空条件 $e_j=0$，不同于字面开半径零。非空轴合同的条件分别如下。

| 34章非空轴合同 | $\Omega$ 上恢复条件 | $D$ 上恢复条件 |
| --- | --- | --- |
| 当前精确，终端闭 $\varepsilon_n\ge0$ | $\varepsilon_n<\phi/2$ | 全部 $\varepsilon_n\ge0$ |
| 当前精确，终端正开 $\varepsilon_n>0$ | $\varepsilon_n\le\phi/2$ | 全部 $\varepsilon_n>0$ |
| 终端精确，当前闭 $\varepsilon_0\ge0$ | $\varepsilon_0<\delta/2$ | $\varepsilon_0<\delta/2$ |
| 终端精确，当前正开 $\varepsilon_0>0$ | $\varepsilon_0\le\delta/2$ | $\varepsilon_0\le\delta/2$ |

证明。正半径下，只要一处误差严格，残差误差就严格小于 $H$；所以 $H\le\delta/2$ 时唯一最近码正确。若 $H>\delta/2$，定理34.4的正双半径构造给出两处真实分离都严格低于两倍半径的实际有限来源；中点满足两处正开界，也满足任何正混合界，故失败。

当前精确时，任何当前相同而前缀不同的完成来源对都有

$$
|x_n-x'_n|=|A(u)-A(v)|/a\ge\delta/a=\phi.
$$

定理34.4的 $h=\phi$ 实际对达到这个最小终端差，故闭与正开终端条件分别为 $\varepsilon_n<\phi/2$、$\varepsilon_n\le\phi/2$。$D$ 的当前精确行由有限来源单射性给出。终端精确时只剩当前残差误差；接相同零尾的最小前缀对在两域都达到当前差 $\delta$，因此给出表中严格闭界和含等号正开界。$\square$

若把任何一处写成 $|e_j|<0$，没有允许误差，合同为空，正确性仅是空域上的真空陈述。两坐标均精确时两域都可恢复。若 $n=0$，目标本身为空，常函数对所有非空合同都正确；本章不同前缀的间距与临界值仅对 $n\ge1$ 定义。

### 34.己 等半径、实际达到与精确系数访问

**推论 34.6（两个端点的等半径距离）。** 置

$$
\boxed{d_n=\frac{\delta_n}{1+g^n}
=\frac{t^{3n-1}}{1+g^n},\qquad \varepsilon_n^{\mathrm{eq}}=d_n/2.}
$$

不同目标前缀的实际共同端点对，其最大范数距离在 $\Omega$ 上最小值为 $d_n$ 且达到；在 $D$ 上下确界为 $d_n$ 而不达到。等半径误差恢复为

| 34章等半径来源域 | 闭半径 $\varepsilon\ge0$ | 正开半径 $\varepsilon>0$ |
| --- | --- | --- |
| 完成来源 $\Omega$ | $\varepsilon<d_n/2$ | $0<\varepsilon\le d_n/2$ |
| 最终空尾来源 $D$ | $\varepsilon\le d_n/2$ | $0<\varepsilon\le d_n/2$ |

证明。命题34.2后的共同端点下界给出 $D_{\rm pair}\ge\delta/(1+a)=d_n$。给前缀 $0^n$ 接零尾，给 $0^{n-1}5$ 接一条标量恰为 $d_n$ 的实际 guard 一尾。后者存在，因为

$$
0<d_n=\frac{\phi a}{1+a}
\le\frac{\phi g}{1+g}=\frac t2<t.
$$

这里 $a\le g$ 且 $1+g=2t$。这两条实际来源的端点分别为

$$
(0,0),\qquad(-\sigma d_n,d_n),
$$

距离恰为 $d_n$，证明完成域达到。守住 guard 一是这一步的合法接缝条件。

对有限域，证明 $d_n\notin R$。代数共轭为 $t'=-\phi$，从而 $a'=\sigma/a$，且 $t$、$\phi$、$a$ 都是 $R$ 的单位。分母范数为整数

$$
\operatorname{Nm}(1+a)=
\begin{cases}
a-a^{-1},&n\text{ 奇},\\
2+a+a^{-1},&n\text{ 偶}.
\end{cases}
$$

由 $g^2+4g=1$，奇数 $n\ge1$ 时范数绝对值至少四；偶数 $n\ge2$ 时由 $g^2+g^{-2}=18$ 得范数至少二十。因此 $1+a$ 不是单位；若 $d_n=\phi a/(1+a)$ 属于 $R$，单位分子就会迫使 $1+a$ 也是单位，矛盾。

距离下界的等号强制尾差绝对值恰为 $d_n$；两条实际有限尾的差属于 $R$，所以 $D$ 上不能达到。固定前面标量为 $d_n$ 的一条 guard 一完成尾，截断后补零得到同 guard 的实际有限尾 $y_k\to d_n$。保持前缀 $0^{n-1}5$，其共同端点

$$
(-\sigma\delta+cy_k,y_k)\longrightarrow(-\sigma d_n,d_n)
$$

与零来源的距离均严格大于 $d_n$，但趋于它。这证明有限域的下确界。

等半径加权误差为 $H=(1+a)\varepsilon$。在闭等号处 $h=2\varepsilon=d_n\notin R$，定理34.4使 $D$ 可恢复而 $\Omega$ 不可恢复；正开等号由定理34.5给出。$\square$

$n=1$ 时 $d_1=t/2$、临界半径为 $t/4$，与定理16.2–16.5的一窗两样本结果一致。$d_n=\Theta(g^n)$ 的间距阶由第23章的 $t^{3n-1}$ 及有界因子 $1+g^n$ 继承；本章增加的是两个共同端点的尖锐因子、实际达到区别与访问边界，不另提出容量定理。

**命题 34.7（承诺有效的临界等距记录）。** 在定理34.4可恢复的闭临界预算下，$\varepsilon_0>0,H=\delta/2,h=2\varepsilon_n\notin R$。对承诺有效的 $D$ 记录，取所有满足 $|b(r)-A(u)|\le\delta/2$ 的码候选。候选至多两个；若有两个，必为命题34.2的 $p0,p1$。其唯一可能的尾标量分别是

$$
y_0=r_n-\varepsilon_n,\qquad y_1=r_n+\varepsilon_n.
$$

恰有一个属于 $R$，该候选就是目标前缀。若预算和记录额外以指定实嵌入中的精确 $K$ 系数表示，则这一候选选择可以有限精确完成。

证明。长度为 $\delta$ 的码候选区间至多含两个码；两个同时出现时，间距迫使码差为 $\delta$ 且残差为中点。以 $p0,p1$ 定向，中点残差对两候选分别强制误差角

$$
(-\sigma\varepsilon_0,+\varepsilon_n),\qquad
(+\sigma\varepsilon_0,-\varepsilon_n).
$$

于是其可能尾值恰如陈述。尾差 $h\notin R$ 使它们不能同时在 $R$；有效性承诺提供一个实际有限候选，故至少一个在 $R$。这样环测试在承诺下确定目标。单候选时有效性已经确定它。

精确 $K$ 表示下，命题16.5的系数比较可有限计算残差及最近码；$p+qt\in R$ 恰在两个有理系数均为整数时成立。若没有有效来源承诺，环成员并不保证尾合法或误差合同成立，规则不承担来源认证。$\square$

精确域系数是额外访问资源；一般实记录及一般 Cauchy 预算没有因此取得环成员、精确相等或临界预算判定。尤其本命题不把 $R\cap I_s$ 当作 $T_s$，也不从任意 Cauchy 名字中提取精确代数表示。

### 34.庚 同一实际记录的闭包与连续性

**命题 34.8（闭记录集合的联合闭包）。** 对固定闭预算，定义

$$
\begin{aligned}
V_u^D&=\{(A(u)+cy+e_0,y+e_n):
 y\in T_{s(u)},\ |e_0|\le\varepsilon_0,\ |e_n|\le\varepsilon_n\},\\
V_u^\Omega&=\{(A(u)+cy+e_0,y+e_n):
 y\in I_{s(u)},\ |e_0|\le\varepsilon_0,\ |e_n|\le\varepsilon_n\}.
\end{aligned}
$$

则

$$
\boxed{\overline{V_u^D}=V_u^\Omega.}
$$

若此预算在 $D$ 上允许恢复，令 $V^D=\bigcup_uV_u^D$，其唯一强制前缀函数为 $F$，值域取离散拓扑、记录域取最大范数的子空间拓扑。对 $r\in V_u^D$，有

$$
\boxed{F\text{ 在 }r\text{ 连续}
\quad\Longleftrightarrow\quad
r\notin\bigcup_{v\ne u}V_v^\Omega.}
$$

证明。$V_u^\Omega$ 是紧区间和闭误差矩形的连续像，故紧且闭，包含 $V_u^D$。反向固定一条实现 $y$ 的合法完成尾和两处固定误差；只截断这一条尾后补零，得 $y_k\in T_{s(u)}$ 趋于 $y$。保持同一误差对，两处实际记录共同趋于指定记录，证明逆包含。

若有效 $r$ 属于某个 rival 完成记录集，则该集的联合闭包等式给出不同前缀的实际有限记录趋于 $r$，强制函数不连续。若 $r$ 不属于任何 rival 集，有限个前缀对应的紧集之并是闭集，故 $r$ 有一个邻域不遇到任何 rival 实际记录，函数在那里局部常值。$\square$

本闭包等式属于当前两实值闭误差合同；它保留一条实际尾及两处固定误差。它没有把量化器的端点归属、开格记录或第32章的逐地址接受语义替换为闭包展开。

### 34.辛 闭临界的全部有效不连续点

**定理 34.9（可恢复闭临界的接触点分类）。** 固定

$$
\varepsilon_0>0,\qquad H=\delta/2,\qquad
h=2\varepsilon_n\notin R.
$$

这时 $0<h<\phi$。对每个合法长度 $N-1$ 且末位零的 $p$，置

$$
\Gamma_p(y)=\bigl(A(p0)+cy-\sigma\varepsilon_0, y+\varepsilon_n\bigr).
$$

有效 $D$ 记录上的全部不连续点恰为

$$
\boxed{\mathcal B=
\bigcup_p\left\{\Gamma_p(y):
-1<y<t-h,\quad y\in T_0\ \text{或}\ y+h\in T_1\right\}.}
$$

两处有限尾条件不能同时成立。$\mathcal B$ 可数、非空，且在每一条完整闭接触线段 $\Gamma_p([-1,t-h])$ 上稠密；线段的两个端点本身不是有效 $D$ 接触记录。其余有效记录处的连续性按命题34.8判断；特别地，$V^D\setminus\mathcal B$ 的每一点连续。

证明。由于零属于 $R$，可恢复预算的 $h$ 不能为零；$\varepsilon_0>0$ 又给出 $h<\phi$。若两个不同前缀的完成记录集相交，临界码距链必须全取等号。命题34.2使它们成为 $p0,p1$；定理34.4的等号分析强制

$$
y_1-y_0=h,\qquad x_0^1-x_0^0=-2\sigma\varepsilon_0.
$$

两个误差矩形的交集因此由相反的饱和角给出，所有共同完成记录恰为 $\Gamma_p(y)$，其中

$$
y\in I_0,\qquad y+h\in I_1
\quad\Longleftrightarrow\quad -1\le y\le t-h.
$$

这样的记录来自实际有限来源恰在 $y\in T_0$ 或 $y+h\in T_1$ 时；它们不可能同时成立，因为 $h\notin R$。也没有第三码值：此记录的残差是这两个间距 $\delta$ 的码的中点，半径 $\delta/2$ 的残差区间容不下第三个码。饱和角还使同一候选下的可能尾值唯一，所以没有遗漏其他有限表示。

端点 $y=-1$ 不是 $T_0$ 成员，而 $y+h=-1+h\notin R$，也不是 $T_1$ 成员。端点 $y=t-h\notin R$ 不是 $T_0$ 成员，其 rival 值 $y+h=t$ 又是非有限极值。所以有效参数严格在开区间内。命题34.8于是给出所列集合的充分性和必要性。

可数性来自有限个 $p$ 及两种可数尾集。$T_0$ 在 $I_0$ 中稠密，因此 $T_0\cap(-1,t-h)$ 在接触参数开区间内稠密，也逼近两个端点；$\Gamma_p$ 连续且由第二坐标单射，得到每条接触上的稠密性。

为逐预算给出一个实际有效不连续锚，选择整数 $K_0\ge1$ 满足

$$
g^{2K_0}<\phi-h.
$$

命题14.9的实际 guard 零有限尾

$$
\eta^0=(3,25)^{K_0}0^\infty,\qquad
y=\kappa_0(\eta^0)=-1+g^{2K_0}
$$

满足 $-1<y<t-h$。令 $z=y+h\in(-1,t)$。因 $y\in R,h\notin R$，$z\notin R$，不能是有限尾值；定理17.2仍提供一条固定的实际 guard 一完成尾 $\eta^1$ 实现 $z$。任取上述 $p$，前接 $p0$ 到 $\eta^0$ 得实际有限来源，其饱和误差记录为

$$
r^*=\Gamma_p(y).
$$

把这一条固定 rival 尾 $\eta^1$ 截断并补零，得实际有限 guard 一尾值 $z_k\to z$。前接 $p1$ 并使用同一相反误差角，给出

$$
r^k=\bigl(A(p1)+cz_k+\sigma\varepsilon_0, z_k-\varepsilon_n\bigr).
$$

临界等式 $\delta=2\varepsilon_0+ah$ 给出共同差公式

$$
r^k-r^*=(c(z_k-z),z_k-z)\longrightarrow(0,0).
$$

每个 $r^k$ 都是实际有限来源的有效记录，却要求 $p1$；有效极限 $r^*$ 要求 $p0$。集合论恢复排除它们相等，但不排除趋近。这既证明非空，也直接证明每个预算都有有效输入上的不连续性。$\square$

### 34.壬 严格区域、临界近似与 Cauchy 访问

**命题 34.10（统一分离与正开临界的点态可读性）。** 若 $H<\delta/2$，两个目标前缀不同的实际闭记录满足统一分离

$$
\boxed{\|r-r'\|_\infty\ge\frac{\delta-2H}{1+a}>0.}
$$

残差最近码解码可以通过逐次 Cauchy 加细有限完成。正开或正混合的正半径临界合同 $H=\delta/2$ 在每个有效记录处也可通过严格最近码加细有限完成，但强制前缀函数在 $\Omega,D$ 的各自有效记录域上均不一致连续。

证明。把两份记录的残差误差分别界为 $H$，则

$$
\delta\le |A(u)-A(v)|
\le(1+a)\|r-r'\|_\infty+2H,
$$

给出分离式。严格闭区域的真实残差位于唯一最近码的开判定区，到相邻判定边界至少有 $\delta/2-H>0$ 的余量。$c$ 与有限码本是已知代数数据；对 $r_0,r_n$ 的 Cauchy 包围区间作仿射组合，逐次加细，直到整个残差包围区间位于一个码的严格最近区域，即可输出。每个有效名字都会在有限精度后满足这个严格包含。

正开或正混合临界处，至少一处实际误差严格，因此每份有效记录仍有 $|b(r)-A(u)|<\delta/2$ 的个别严格余量，同一加细程序点态终止。它没有所有记录共有的正余量。

为严格排除一致连续性，记 $h=2\varepsilon_n\in(0,\phi)$，固定定理34.4所用的实际最小前缀对及完成尾 $y_0=-th,y_1=t^2h$。令 $\theta_k\in(0,1)$ 趋于一，使用两处都严格内缩的相反误差角

$$
e^{0,k}=(-\sigma\theta_k\varepsilon_0,+\theta_k\varepsilon_n),\qquad
e^{1,k}=(+\sigma\theta_k\varepsilon_0,-\theta_k\varepsilon_n).
$$

在 $\Omega$ 上保持两条实际尾不变；在 $D$ 上分别截断这两条固定尾并补零，取实际尾值 $y_{0,k}\to y_0,y_{1,k}\to y_1$。两条相应共同端点记录的两处误差都严格低于半径，故在正开及正混合合同下有效。它们的前缀不同，而随着尾截断与误差角同时趋于接触，记录差趋于零。正开恢复使它们每次仍不同，却不能使前缀函数一致连续。$\square$

**定理 34.11（闭临界的全部有效名字终止障碍）。** 在定理34.9的任何可恢复闭临界预算下，不存在只访问两个记录的普通有理 Cauchy 名字、同时对所有有效 $D$ 记录及其所有合法名字都正确并终止的算法。该结论不声称每个单独名字都不能终止。

证明。名字模型为查询精度 $j$ 返回有理向量 $v_j$，满足 $\|v_j-r\|_\infty\le2^{-j}$。在定理34.9的有效锚 $r^*$ 上，选择一个每次近似误差都严格小于 $2^{-j}$ 的合法名字，有理向量稠密性允许这样选择。

若所述算法在这个名字上终止，只用有限次查询。每个已用答复到允许误差边界的余量为正，有限集的最小余量也为正。选足够近的 rival 有效记录 $r^k$，使它与 $r^*$ 的距离小于该最小余量，则同一批有限答复也都合法近似 $r^k$；剩余精度可补成 $r^k$ 的一个合法名字。相同有限查询路径必给出相同前缀，却必须在 $r^*$ 返回 $p0$、在 $r^k$ 返回 $p1$，矛盾。若没有查询，两个不同目标的有效记录已经给出矛盾。$\square$

这个障碍不只发生于不可计算预算。例如取可精确代数描述的

$$
\varepsilon_n=\frac14,\qquad
\varepsilon_0=\frac{a(\phi-1/2)}2.
$$

它们为正且 $H=\delta/2$，而 $h=1/2\notin R$。集合论恢复、命题34.7的额外精确系数访问和普通 Cauchy 访问的终止障碍在此仍分别成立。

命题34.8与定理34.9对其他闭临界有效记录给出的是点态拓扑连续性分类。若要将这些连续点进一步宣称为可执行的成员排除程序，还须给出预算等参数的有效数据和相应严格比较方法；本章不从任意实预算的拓扑连续性自动推出算法。相反，命题34.10的严格最近码程序直接使用已知代数码本和记录加细，其严格裕量是明确的终止依据。

### 34.癸 精确当前轴的点态访问与一致连续性

**命题 34.12（固定前缀的精确当前恢复）。** 在 $D$ 上取 $\varepsilon_0=0$。对任意有限闭终端半径 $\varepsilon_n\ge0$，每个有效记录的当前值严格位于唯一目标柱区间内部。由当前坐标的普通 Cauchy 名字可以点态有限恢复固定前缀；强制前缀函数处处连续，并且一致连续当且仅当

$$
\varepsilon_n<\phi/2.
$$

若终端合同为正开，点态结论仍对每个正半径成立，一致连续的条件仍是 $\varepsilon_n<\phi/2$。

证明。长度 $N$ 的目标柱区间为

$$
C_u=A(u)+cI_{s(u)}.
$$

定理14.7的固定深度柱分块内部两两不交，只在相邻端点相交。有限来源避开所有共同端点和外部极值，所以每个精确当前值 $r_0\in\kappa_0(D)$ 严格位于其唯一 $C_u$ 的内部。该点有不遇到其他目标柱的当前坐标邻域，不论终端记录为何，其有效记录的目标均不变。这证明处处点态连续。

有限个 $C_u$ 的端点都是已知代数数。逐次加细当前值的包围区间，直到它严格包含于一个柱内部，再输出对应前缀。每个实际有限来源距柱边界为正，故对每个合法 Cauchy 名字都点态终止。这是第22章固定前缀访问的深度柱写法，不需要精确零测试或尾支持认证。

若 $\varepsilon_n<\phi/2$，则 $H=a\varepsilon_n<\delta/2$，命题34.10的统一分离给出一致连续性。反向取 $\varepsilon_n\ge\phi/2$，使用实际有限尾

$$
L_k=(3,25)^k0^\infty,\qquad 5L_k\qquad(k\ge1).
$$

$L_k$ 从两种 incoming guard 都合法，$5L_k$ 从 guard 一合法。命题14.9与分支 $f_5(y)=t^2-gy$ 给出

$$
y_{0,k}=-1+g^{2k},\qquad
y_{1,k}=t-g^{2k+1},
$$

$$
d_k=y_{1,k}-y_{0,k}
=\phi-(1+g)g^{2k}\in(0,\phi),\qquad d_k\to\phi.
$$

分别前接 $0^N,0^{N-1}1$，取得实际精确当前值

$$
x_{0,k}^0=cy_{0,k},\qquad
x_{0,k}^1=-\sigma\delta+cy_{1,k}.
$$

两份终端记录都取同一个中点 $m_k=(y_{0,k}+y_{1,k})/2$。所需终端误差为 $d_k/2<\phi/2\le\varepsilon_n$，因此

$$
r_k^0=(x_{0,k}^0,m_k),\qquad r_k^1=(x_{0,k}^1,m_k)
$$

是目标前缀不同的实际有效 $D$ 记录，而且

$$
\|r_k^0-r_k^1\|_\infty=a(\phi-d_k)\longrightarrow0.
$$

这排除一致连续性，并因误差严格小于 $\phi/2$ 同时覆盖终端正开半径的等号与更大值。

这些记录的共同当前极限是 $-c$，即尾端点 $-1,t$ 给出的两个相邻深度柱的共同端点。定理14.7排除它属于 $\kappa_0(D)$。所以这里的不一致连续性没有制造有效精确当前记录上的不连续点；它与定理34.9的实际有限锚不同。$\square$

### 34.子 数学依赖与结论边界

本章的地址、正数量和条带输入分别来自定义1.1、命题1.2及约定1.3；实际窗口与 guard 几何来自定义14.5、命题14.6、定理14.7、命题14.9及定理17.2；一窗相邻观察和精确系数访问由定理16.2–16.5提供前例；精确当前固定前缀访问由命题22.5提供；码本及初位块间隙直接复用定理23.2。有限尾差值的精确共同平移、两个端点的加权区域、实际达到区别及记录访问分析均按本章陈述的合同作普通纸面推导，不冒称 Lean kernel 核验或文献新颖性。

两个实际端点的残差保留被删前缀所需的区别；允许尾变化后的联合距离及误差角，决定这些区别何时仍能从两份记录读出。闭临界的 $D$ 优势来自某个尾差不能由两条有限尾共同达到；它并不阻止一个有效有限记录被 rival 的实际有限记录任意逼近。精确当前轴则借助有限来源避开柱端点而保有每个固定前缀的局部余量。存在、实际达到、连续性及普通近似访问因此承担各自不同的结论。

$n$ 是已知窗口差，两个精确实数也不是固定有限位存储。这里没有物理时空生成、物理时间箭头、普遍遗忘、存储位数、运行时间或硬件最优结论；没有 End 输出、隐藏支持证书或额外实际观测。精确域或环预算分类不等于对任意 Cauchy 预算作临界判定，固定前缀的点态终止也不等于完整有限词的统一结束认证。条带复用保留约定1.3的实际正数量前提及其与经典共轭正性的区别。

## 追加锚（34·本行以下为增补区）
## 35. 已知有限尾的精确恢复余量、相位闭式与最小周期

### 35.甲 支持证书与两个共同端点

本章在第34章的两端点合同中加入已知的有限尾支持证书。整数 $n\ge1$ 与 $K\ge0$ 均为给定参数；实际来源属于 $D_{3(n+K)}$，恢复目标仍是前 $n$ 个三位窗口。支持证书限制尚未取得的体部，两个标量则是同一来源已经实际取得的边界记录。它们的联合关系决定恢复余量，不能以两个独立边缘区间替代。

**定义 35.1（有限尾合同与归一化余量）。** 沿用定义1.1、14.5、34.1和约定23.1的来源、guard 与位支持约定，置

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t=t^{-1},\qquad
R=\mathbb Z[t],\qquad g=t^3=\sqrt5-2,
$$

$$
q=g^n,\qquad r=g^K,\qquad s=(-1)^n,\qquad
\delta=\phi q,\qquad d=d_n=\frac{\phi q}{1+q}.
$$

对实际来源 $\omega\in D_{3(n+K)}$，令

$$
E_n(\omega)=(\kappa_0(\omega),\kappa_0(T^n\omega))=(x_0,x_n),
\qquad P_n(\omega)=(\omega_0,\ldots,\omega_{3n-1}).
$$

两个坐标各只取得一次；原始误差独立允许于闭区间 $[-d/2,d/2]$，即涵盖全部这样的误差对，不附加随机独立性前提。没有量化器、中间样本或独立 End 字段。外部单位位为零，没有相邻一，高位补零不改变来源身份。定义

$$
d_{n,K}=\min_{\substack{\omega,\nu\in D_{3(n+K)}\\
P_n(\omega)\ne P_n(\nu)}}
\|E_n(\omega)-E_n(\nu)\|_\infty,
\qquad \mu_{n,K}=d_{n,K}-d,\qquad a_K=g^{-K}\mu_{n,K}.
$$

来源集有限，且零前缀与只在第 $3n-1$ 位为一的前缀均可补零实现，所以最小值有竞争对象且达到。$d$ 是推论34.6的无统一支持上界时的临界距离；$\mu_{n,K}$ 是加入证书后的额外距离。记 $T_{b,K}$ 为从 incoming guard $b\in\{0,1\}$ 出发、支持严格低于位 $3K$ 的实际有限尾标量集合，并令

$$
H_K=T_{1,K}-T_{0,K}.
$$

每条尾的位索引从自己的原点零开始。$T_{b,0}=\{0\}$，而零延长给出 $T_{b,K}\subseteq T_{b,K+1}$。对 $z\in\mathbb Q(t)$，撇号表示 $t'=-\phi$ 的代数共轭，$N(z)=zz'$ 表示域范数；特别地

$$
g'=-g^{-1},\qquad q'=s/q,\qquad
\delta'=-st/q,\qquad d'=-\frac{t}{1+sq}.
$$

### 35.乙 实际兄弟前缀与定量余量

**命题 35.2（实际尾差的精确最小化）。** 有

$$
\boxed{d_{n,K}=\min_{h\in H_K}F(h),\qquad
F(h)=\max\{\lvert\delta-qh\rvert,\lvert h\rvert\}.}
$$

最小化只需非负差值；对 $h\ge0$，

$$
F(h)-d=
\begin{cases}
q(d-h),&0\le h\le d,\\
h-d,&h\ge d.
\end{cases}
$$

对全部实数 $h$ 还成立 $F(h)-d\ge q|h-d|$。

证明。合法前缀 $u$ 与其相容实际尾 $y$ 给出的两个端点始终为

$$
(x_0,x_n)=(A(u)+sqy,y),\qquad
A(u)=\sum_{j<3n}u_j(-t)^j.
$$

复用定理23.2的码本间距及首位块间隙，或等价地使用命题34.2的分类：兄弟前缀只在最后一位不同，其截距差为 $-s\delta$；非兄弟前缀的截距差至少为 $t^{3n-2}=\delta/t$。若两个共同端点的距离为 $D_{\rm pair}$，则

$$
|A(u)-A(v)|\le(1+q)D_{\rm pair}.
$$

非兄弟因而有

$$
D_{\rm pair}\ge\frac{\delta}{t(1+q)}>\delta,
$$

因为 $t(1+q)\le t(1+g)=2t^2<1$。两个零尾的兄弟对已达到 $\delta$，故非兄弟不能最小化。

兄弟 $p0,p1$ 的尾分别为 $y_0\in T_{0,K},y_1\in T_{1,K}$；其尾差 $h=y_1-y_0$ 与当前差分别为 $h$ 和 $s(qh-\delta)$，给出 $F(h)$。反向，对 $H_K$ 的每一个差值，分别将其两个实际尾接到窗口前缀 $0^n$ 与 $0^{n-1}5$，两条接缝合法，支持均低于 $3(n+K)$。故每一个差值都由一对实际来源共同端点实现，而不是独立选择标量坐标。

零属于 $H_K$，$F(0)=\delta$；若 $h<0$，则 $F(h)\ge\delta-qh>\delta$。对 $0\le h\le d$，有 $\delta-qh\ge h$，所以 $F(h)=\delta-qh$；对 $h\ge d$，两式 $\delta-qh\le h$ 与 $qh-\delta<h$ 给出 $F(h)=h$。这证明分段式。负轴上

$$
F(h)-d\ge q(d-h)=q|h-d|,
$$

非负轴上的分段式同样给出所述全轴下界。$\square$

**定理 35.3（严格余量、初始平台与固定深度的阶）。** 对全部 $n\ge1,K\ge0$，

$$
\boxed{\frac{q^2r}{3}\le\mu_{n,K}
\le\min\{qd,\ 2\phi qr\}.}
$$

而且

$$
\boxed{d_{n,K}=\delta\quad(0\le K\le n).}
$$

$d_{n,K}$ 随 $K$ 非增且趋于 $d$；每个有限 $K$ 的余量严格为正。对固定 $n$，有 $\mu_{n,K}=\Theta_n(g^K)$，这里不把隐含常数宣称为同时独立于 $n,K$。

证明。先使用推论34.6的代数障碍并写出其数值：$\delta$ 是 $R$ 的单位，而

$$
|N(1+q)|=
\begin{cases}
q^{-1}-q,&n\text{ 奇},\\
2+q+q^{-1},&n\text{ 偶}
\end{cases}
\ge4.
$$

故 $d\notin R$。实际尾的共轭是非负位和，支持低于 $3K$ 给出

$$
0\le y'\le\sum_{j<3K}\phi^j
=\phi(r^{-1}-1),\qquad
|h'|\le\phi(r^{-1}-1)\quad(h\in H_K).
$$

对 $h\in H_K$，非零代数整数 $W=(1+q)h-\delta$ 满足 $|N(W)|\ge1$。由于 $1+sq>0$，

$$
\begin{aligned}
|W'|&\le\frac{1+sq}{q}\phi(r^{-1}-1)+\frac tq\\
&\le\frac{\phi(1+sq)}{qr}.
\end{aligned}
$$

最后一步用 $t\le\phi(1+sq)$；其最小右侧至少是 $\phi(1-g)>t$。于是

$$
|h-d|\ge\frac{qr}{\phi(1+q)(1+sq)},\qquad
F(h)-d\ge\frac{q^2r}{\phi(1+q)(1+sq)}.
$$

分母不超过 $\phi(1+g)^2=4t<3$。对实际最小值应用此式即得下界。这只共轭了选定的代数表达式 $W$，没有将最大值或绝对值函数当成可共轭的运算。

零尾兄弟对给出上界 $\mu_{n,K}\le\delta-d=qd$。当 $K\ge1$ 时，置 $z=d-\phi r$。由 $d\le t/2<t$ 及 $\phi r\le\phi g=t^2<1$，有 $-1<z<t$。定义14.5、命题14.6与定理17.2的状态相对区间实现提供一条标量为 $z$ 的合法 guard 一完成尾。将它截到前 $K$ 个窗口再补零，得到实际有限尾 $\widetilde y$。同一地址的剩余标量绝对值不超过 $\phi$，故

$$
|\widetilde y-z|\le\phi r,\qquad
d-2\phi r\le\widetilde y\le d.
$$

若 $\widetilde y<0$，以整条零尾替换；否则保持原尾。所得 $y\in T_{1,K}$ 满足 $0\le y\le d$ 且 $d-y\le2\phi r$。将它与零 guard 零尾相比较，命题35.2给出 $\mu_{n,K}\le q(d-y)\le2\phi qr$。$K=0$ 时两条尾都为零，$\mu_{n,0}=qd$，且 $qd\le2\phi q$，所以同一上界成立。

初始平台的 $K=0$ 情形就是前缀码本间距。若 $1\le K\le n$，两个不同尾标量均属于 $S_{3K}$，定理23.2给出尾差绝对值至少为 $t^{3K-1}=\phi r\ge\delta$。若两条尾相同，则当前坐标差就是不同前缀码差，仍至少为 $\delta$。零尾兄弟对达到此值，证明平台。

零延长使实际来源域随 $K$ 嵌套，因此最小距离非增；上界 $2\phi qr\to0$ 又使其趋于 $d$。固定 $n$ 时可取阶比较常数 $q^2/3$ 与 $2\phi q$。这些常数不能换成同时独立于两参数的正下界常数：在 $K=n$，

$$
g^{-n}\mu_{n,n}=d=\frac{\phi g^n}{1+g^n}\longrightarrow0
\quad(n\to\infty).
$$

$\square$

### 35.丙 合法复制与先于可达性定义的候选

**引理 35.4（实际仿射复制及尖锐共轭必要条件）。** 定义

$$
M(h)=\delta(1-q)+q^2h.
$$

则

$$
M(H_K)\subseteq H_{K+2n},\qquad
M(d)=d,\qquad M(h)-d=q^2(h-d),\qquad a_{K+2n}\le a_K.
$$

每个 $h\in H_K$ 满足 $|h'|<g^{-K}$。若将实际差值写成 $h=d+zg^K$，则必有 $|z'|<1$。

证明。取 $h=y_1-y_0$ 的实际尾实现。构造两个长度 $6n$ 位的前缀，只使用位置 $3n-1$ 与 $6n-1$。$n$ 为奇数时，两处一都放入正前缀，负前缀全零；$n$ 为偶数时，正前缀只在 $6n-1$ 放一，负前缀只在 $3n-1$ 放一。两前缀的标量差均为 $\delta(1-q)$。

两前缀首位为零，内部没有相邻一；正前缀末位为一，故正好允许原 guard 一尾 $y_1$；负前缀末位为零，故允许原 guard 零尾 $y_0$。拼接后正尾的 incoming guard 一与负尾的 incoming guard 零仍合法，支持低于 $3(K+2n)$。两个附加尾共同乘以 $(-g)^{2n}=q^2$，所以差值是 $M(h)$。固定点及位移公式由 $(1+q)d=\delta$ 直接得到。对非负最小化差值，$M(h)>0$ 且保持位于 $d$ 的哪一侧；命题35.2的两分支均将余量乘以 $q^2$。实际复制因而给出 $a_{K+2n}\le a_K$。

为证尖锐共轭界，令 $N=3K$。合法尾的共轭为 $\sum_{j<N}\omega_j\phi^j$。$N$ 为偶数时，将位置配成 $(0,1),(2,3),\ldots$，每对至多贡献较高位，故共轭和不超过 $\phi^N-1$。$N$ 为奇数时，单独保留位置零，再配成 $(1,2),(3,4),\ldots$，上界为 $\phi^N-t$。两界都严格小于 $\phi^N=g^{-K}$，$K=0$ 的零尾也满足此严格界。两条尾共轭均在 $[0,g^{-K})$，所以差值满足 $|h'|<g^{-K}$。

现在对同一个实际差值反复作合法复制。第 $j$ 次复制在深度 $K+2nj$ 的实际差值为

$$
M^j(h)=d+zg^{K+2nj}.
$$

将其共轭界乘以 $g^{K+2nj}$，得到

$$
\left|g^{K+2nj}d'+(-1)^Kz'\right|<1.
$$

令 $j\to\infty$，有 $|z'|\le1$。若等号成立，则实数域中的 $z'=1$ 或 $-1$ 经共轭给出 $z=1$ 或 $-1$。因 $h,zg^K\in R$，将迫使 $d\in R$，与定理35.3中的单位分母障碍矛盾。因此 $|z'|<1$。$\square$

**命题 35.5（有限非空候选与全部深度的下界）。** 对 $0\le k<2n$，先定义纯代数集合

$$
\mathcal C_{n,k}=\left\{a\in(1+q)^{-1}R:
0<a\le\phi,\quad |a'|<q^{-1},\quad d+ag^k\in R\right\}.
$$

每个集合有限且非空，所以可定义

$$
A_{n,k}=\min\mathcal C_{n,k}.
$$

尚不假定任何候选已在某个尾深度达到，就有

$$
\boxed{a_K\ge A_{n,K\bmod2n},\qquad
0<A_{n,k}\le2\phi q.}
$$

证明。实际最小化差值可取 $h\ge0$；其距离 $F(h)$ 等于 $h$ 或 $\delta-qh$，因而属于 $R$。所以

$$
a_K=g^{-K}(F(h)-d)\in(1+q)^{-1}R,
\qquad d+a_Kg^K=F(h)\in R.
$$

若 $h\ge d$，写 $h=d+a_Kg^K$，引理35.4给出 $|a_K'|<1<q^{-1}$。若 $h<d$，则 $h=d-(a_K/q)g^K$，同一必要条件给出 $|a_K'|<q^{-1}$。定理35.3还给出 $0<a_K\le2\phi q<\phi$，其中 $K=0$ 由 $a_0=qd$ 单独包含。

$M$ 的截距属于 $R$、斜率 $q^2$ 是 $R$ 的单位，所以它是 $R$ 上的仿射双射。固定点公式说明

$$
d+ag^{K+2n}=M(d+ag^K),
$$

故 $d+ag^K\in R$ 当且仅当 $d+ag^{K+2n}\in R$。逆向在这里仅用于环成员性，没有断言逆向复制后的尾可实际实现。因此每个实际 $a_K$ 都属于相位 $K\bmod2n$ 的候选集合；取 $K=k$ 即证明该集合非空及其最小值的大小界。

有限性来自两个嵌入的有界矩形。对 $a$ 乘以固定的 $1+q$ 后，得到 $R$ 中两个共轭坐标均有界的点；若它写成 $A+Bt$，则

$$
B=\frac{x-x'}{\sqrt5},\qquad
A=\frac{\phi x+tx'}{\sqrt5}
$$

使两个整数系数均有界，故只有有限多个点。最小值存在并给出全部实际深度的下界。$\square$

### 35.丁 固定条带、严格前驱与相位闭式

**引理 35.6（小格点差）。** 若 $u\in R$ 且 $0<u\le\phi,|u'|<2$，则 $u\in\{t,1,\phi\}$。

证明。写 $u=A+Bt$，由两个嵌入的逆公式，

$$
-\frac2{\sqrt5}<B<\frac{\phi+2}{\sqrt5}.
$$

左端大于 $-1$，右端小于 $2$，所以整数 $B$ 为零或一。$B=0$ 时物理坐标界强制 $A=1$；$B=1$ 时强制 $A=0$ 或一。即得到 $1,t,\phi$。$\square$

**命题 35.7（固定条带的最小点与对相位前驱）。** 令

$$
X_{n,k}=A_{n,k}/q,\qquad
\rho_{n,k}=-\frac{\phi g^{-k}}{1+q},
$$

相位下标按模 $2n$ 读取。$X_{n,k}$ 是陪集 $\rho_{n,k}+R$ 在条带 $|x'|<1$ 中的最小正点，且 $0<X_{n,k}\le\phi$。定义

$$
L(w)=\begin{cases}
t,&-1<w<-t,\\
\phi,&-t<w<0,\\
1,&0<w<1.
\end{cases}
$$

则

$$
\boxed{X_{n,k+n}=L(X_{n,k}')-X_{n,k}.}
$$

证明。置 $a=qx$，用 $qg^k$ 的单位性可得

$$
d+ag^k\in R
\quad\Longleftrightarrow\quad
x+\frac{\phi g^{-k}}{1+q}\in R,
$$

而 $|x'|=q|a'|$。命题35.5提供正条带点；有界矩形的格点有限性保证在任一已知正点以下能取最小点。任何更小正条带点也满足原候选的上界，故这个最小点就是 $X_{n,k}$。

陪集不含 $R$ 中的点，否则非单位 $1+q$ 将整除单位 $\phi g^{-k}$；特别地，它不含零。若最小正点 $x>\phi$，在 $x'>0$ 时减一，在 $x'\le0$ 时减 $\phi$，得到仍在同一条带中的更小正点：共轭分别为 $x'-1\in(-1,0)$ 与 $x'+t\in(-1,1)$。矛盾，所以 $x\le\phi$。

又因

$$
\rho_{n,k+n}+\rho_{n,k}=-\frac{\phi g^{-k}}q\in R,
$$

对相位陪集是原陪集的负集。于是 $-X_{n,k+n}$ 是原陪集条带中最大的负点。这样的负点存在：对最小正点，仍按上述规则减一或减 $\phi$，结果不能为正或零，故为负；在它与零之间用格点有限性取最大负点。

这两个相邻点的距离 $\Delta=X_{n,k}+X_{n,k+n}$ 属于 $R$，满足 $0<\Delta\le\phi$ 与 $|\Delta'|<2$。引理35.6只允许 $t,1,\phi$。令 $w=X_{n,k}'$，减 $t$ 保持条带恰在 $-1<w<-t$，减一保持条带恰在 $0<w<1$；剩余 $-t<w<0$ 只允许三者中的 $\phi$。选择最小合法步长即得到最大负前驱，因为更小的前驱间隙也必须在这三个值中。端点 $w=0$ 或 $-t$ 会经共轭给出 $x=0$ 或 $\phi$，均是被排除的环点；条带本身排除 $w=\pm1$。所以三个严格情形完整，得到公式。$\square$

**推论 35.8（全部相位的闭式值）。** 对所有 $n\ge1$，候选最小值恰为

$$
\boxed{\begin{aligned}
A_{n,j}&=g^{n-j}d &&(0\le j<n),\\
A_{n,n}&=\begin{cases}d,&n\text{ 偶},\\d-q,&n\text{ 奇},\end{cases}\\
A_{n,n+j}&=q-g^{n-j}d
&&(1\le j<n,\ j\text{ 奇}),\\
A_{n,n+j}&=\phi q-g^{n-j}d
&&(2\le j<n,\ j\text{ 偶}).
\end{aligned}}
$$

这四个范围覆盖全部 $2n$ 个相位；它们此时是纯代数最小值，实际有限尾的达到另由下文证明。

证明。对 $0\le j<n$，取

$$
x=g^{-j}d=\frac{\phi g^{n-j}}{1+q}.
$$

有 $0<x\le t^2/(1+q)<t$，且

$$
x'=(-1)^jg^jd',\qquad
|x'|\le\frac{t}{1-g}<1,\qquad
d+qxg^j=(1+q)d=\delta\in R.
$$

所以 $x$ 是对应条带中的正点。若有更小正点，则它与 $x$ 的差属于 $R$，物理坐标严格在 $(0,t)$、共轭绝对值小于二，违反引理35.6。因此 $X_{n,j}=g^{-j}d$，得到第一行。

再应用命题35.7。在奇数 $j$ 时，$X_{n,j}'$ 为正且小于一，故 $L=1$，得到第三行。在偶数 $j\ge2$ 时，它为负且绝对值小于 $g^j\le g^2<t$，故 $L=\phi$，得到第四行。$j=0$ 时保留 $n$ 的奇偶：偶数 $n$ 有 $d'\in(-t,0)$，奇数 $n$ 有 $d'\in(-1,-t)$，因此

$$
A_{n,n}=\begin{cases}
q(\phi-d)=d,&n\text{ 偶},\\
q(t-d)=d-q,&n\text{ 奇}.
\end{cases}
$$

这些值均正：第一半的条带点小于 $t$，其一或 $\phi$ 的补差为正；奇数情形的特殊值为 $d-q=q(t-q)/(1+q)>0$。

$n=1$ 时，后两个指标范围为空，$d=t/2$，而

$$
A_{1,0}=qd=\frac{t^4}{2},\qquad
A_{1,1}=d-q=q(t-d)=qd.
$$

所以这一情形的两个相位相等，闭式没有将它误作严格不同相位。$\square$

### 35.戊 同时满足数量、guard 与支持的实际成员条件

**命题 35.9（正差值的精确有界成员条件）。** 对 $x=a+bt\in R$，记

$$
Q(x)=2a-3b=\frac{gx+g^{-1}x'}{\sqrt5},\qquad
B_K=F_{3K+3}.
$$

有精确集合描述

$$
\begin{aligned}
T_{0,K}&=\{x\in R:-1<x<\phi,\ 0\le Q(x)<B_K\},\\
T_{1,K}&=\{x\in R:-1<x<t,\ 0\le Q(x)<B_K\}.
\end{aligned}
$$

特别地，对 $h\in R\cap(0,t)$，$h\in H_K$ 当且仅当存在整数 $k,j$ 使

$$
\boxed{\begin{gathered}
\max(0,Q(h))\le k\le\min(B_K-1,B_K-1+Q(h)),\\
kt^2+g(h-1)<j<kt^2+gt.
\end{gathered}}
$$

证明。$Q$ 是约定1.3及定理34.3中实际整数数量的坐标翻译。公式右侧在基底 $1,t$ 上分别等于二、负三，故与左侧相等。正数量环点在 $(-1,\phi)$ 中的实际来源表示复用约定1.3；零来源由命题1.2处理。数量零的环点写成 $a=3m,b=2m$，其标量为 $m/g$，故在此开区间中只有零。

命题1.2给出占位 $j$ 的数量 $F_{j+3}$。支持低于位 $N$ 的合法和不超过允许额外单位位时的最大和 $F_{N+3}-1$，因此其数量小于 $F_{N+3}$；反向，只要某位 $j\ge N$ 被占用，它就贡献至少 $F_{N+3}$，其他贡献非负。因此数量上界恰好认证支持低于 $N$，取 $N=3K$ 得第一式。

实际 guard 零尾若首位为零，标量为 $-tz$，$z\in(-1,\phi)$，所以它在 $(-1,t)$。若首位为一，则第二位为零，标量为 $1+t^2z>1-t^2=t$。故物理条带 $(-1,t)$ 恰好挑出首位为零的实际尾，也就是 incoming guard 一的合法尾；支持条件不变，得到第二式。

为实现 $h=y_1-y_0$，在 $0<h<t$ 下，两处物理条带等价于

$$
h-1<y_1<t,\qquad y_0=y_1-h.
$$

令 $k=Q(y_1)$，则 $Q(y_0)=k-Q(h)$。两条尾的数量必须同时在 $\{0,\ldots,B_K-1\}$，恰好得到所列整数区间。$Q(-\phi)=1$，$Q$ 的整数核是 $g^{-1}\mathbb Z$，所以数量为 $k$ 的全部环点写成

$$
y_1=-k\phi+j/g,\qquad j\in\mathbb Z.
$$

把物理开区间乘以 $g$，并用 $g\phi=t^2$，得到所列严格整数不等式。反向，这些同时成立的条件经两条精确尾描述分别提供实际 $y_1,y_0$，所以它们不仅是必要的环与区间条件。$\square$

**引理 35.10（五个旋转点的严格覆盖）。** 若

$$
h\in R,\qquad0<h<t,\qquad B_K-|Q(h)|\ge5,
$$

则 $h\in H_K$。

证明。置 $\alpha=t^2$。五个旋转点 $0,\alpha,2\alpha,3\alpha,4\alpha$ 在圆周上的递增代表是

$$
0,\quad 3\alpha-1=t^4,\quad\alpha,\quad
4\alpha-1=\alpha+t^4,\quad2\alpha.
$$

其逐段圆周间隙为

$$
t^4,\quad g,\quad t^4,\quad g,\quad g.
$$

这些恒等式由 $t^2=1-t$ 得出，且 $0<t^4<g$。任何五个连续旋转迭代只是这五点的共同旋转，因此任何长度严格大于 $g$ 的开弧都遇到其中一点。

命题35.9的允许数量区间在非空时含恰好 $B_K-|Q(h)|$ 个连续整数。对应的严格整数区间长度为

$$
g(t-h+1)=g(\phi-h)>g,
$$

同时小于 $g\phi=t^2<1$。它等价于旋转点 $\{k\alpha\}$ 遇到一个固定的该长度开弧。五点间隙严格小于弧长，故开端点不会丢掉全部命中点；允许数量中任取五个连续整数即提供一个符合严格区间的 $k,j$。命题35.9于是给出带两个数量、两个 guards 及支持条件的实际成员。$\square$

### 35.己 最小候选的实际达到与显式常数

**定理 35.11（最小候选在 $n+2$ 后的实际达到）。** 对 $n\ge2,K\ge n+2$，

$$
\boxed{a_K=A_{n,K\bmod2n}.}
$$

证明。令 $k=K\bmod2n$，选择已由命题35.5定义的最小候选 $a=A_{n,k}$，并置

$$
z=-a/q<0,\qquad h=d+zr,\qquad
\eta=1-|z'|>0.
$$

由候选的共轭界与大小界，$|z'|<1$ 且 $|z|\le2\phi$；这些界在实际达到之前就已建立。相位环成员性给出 $D=d+ar\in R$，从而

$$
h=\frac{\delta-D}{q}\in R.
$$

取 $\sigma\in\{1,-1\}$ 使 $\sigma z'=|z'|$。非零代数整数 $(1+q)(1-\sigma z)$ 的范数绝对值至少一，故

$$
\eta\ge\frac{1}{|N(1+q)|(1+|z|)}
\ge\frac{q}{(1+q)^2(1+|z|)}
\ge\frac{qg}{(1+q)^2},
$$

最后一步用 $1+2\phi=g^{-1}$。这里非零性由 $|z'|<1$ 保证。

为给出实际数量余量，将 $Q$ 按有理线性延伸至 $\mathbb Q(t)$。Binet 公式与 $r'=(-1)^K/r$ 分别给出

$$
B_K=\frac{(gr)^{-1}+(-1)^Kgr}{\sqrt5},\qquad
Q(d+zr)=Q(d)+\frac{gzr+(-1)^Kz'/(gr)}{\sqrt5}.
$$

因而

$$
\begin{aligned}
B_K-|Q(h)|
&\ge\frac{\eta}{\sqrt5\,gr}
-|Q(d)|-\frac{gr}{\sqrt5}(1+|z|)\\
&\ge\frac{\eta}{\sqrt5\,gr}-C_z,
\qquad
C_z=|Q(d)|+\frac g{\sqrt5}(1+|z|).
\end{aligned}
$$

现在显式控制这个常数。$n\ge2$ 给出 $q\le g^2$，且

$$
Q(d)=\frac1{\sqrt5}
\left(\frac{t^2q}{1+q}-\frac{\phi^2}{1+sq}\right)<0.
$$

因此

$$
|Q(d)|<\frac{\phi^2}{\sqrt5(1-g^2)}
=\frac{8+5t}{4\sqrt5}<\frac54.
$$

这里 $1-g^2=4g$，而最后不等式等价于 $t>3/5$。再用 $g(1+|z|)\le g(1+2\phi)=1$，得到

$$
\boxed{C_z<\frac54+\frac1{\sqrt5}.}
$$

当 $K\ge n+2$ 时，$r\le qg^2$，所以

$$
\begin{aligned}
\frac{\eta}{\sqrt5\,gr}
&\ge\frac{1}{\sqrt5\,g^2(1+g^2)^2}
=\frac{g^{-4}}{20\sqrt5}\\
&>\frac{25}{4}+\frac1{\sqrt5}.
\end{aligned}
$$

等式用 $(1+g^2)^2=20g^2$。严格比较可直接核对为

$$
g^{-4}=305+72g,\qquad \sqrt5=2+g,\qquad
g^{-4}-125\sqrt5-20=35-53g>0,
$$

其中 $0<g<1/4$。故 $B_K-|Q(h)|>5$。

还须验证物理条带。由 $q\le g^2$ 和 $g<1/4$，有 $4g^2(1+q)<1$；于是

$$
|z|r\le2\phi qg^2<\frac d2,
\qquad0<\frac d2<h<d\le\frac t2<t.
$$

环成员性、物理开条带与数量余量现在同时满足，引理35.10提供实际 $h\in H_K$。命题35.2的下分支给出

$$
F(h)-d=q(d-h)=ar.
$$

它达到命题35.5的全局下界，所以 $a_K=a$。这里实现的是各相位所需的最小候选，没有断言原候选集合的每一点都在此深度可达。$\square$

### 35.庚 全部初始深度的实际见证与唯一例外

**定理 35.12（全部深度、精确递推与最早起点）。** 对全部 $n\ge1,K\ge0$，

$$
\boxed{\mu_{n,K}=g^K\left(A_{n,K\bmod2n}
+q\,\mathbf1_{\{n\text{ 奇},\ K=n\}}\right).}
$$

因此缩放递推恰为

$$
\boxed{\mu_{n,K+2n}=q^2\mu_{n,K}
-q^4\mathbf1_{\{n\text{ 奇},\ K=n\}}.}
$$

使无修正递推对所有 $K\ge L_n$ 成立的最小非负整数为

$$
\boxed{L_n=\begin{cases}0,&n\text{ 偶},\\n+1,&n\text{ 奇}.\end{cases}}
$$

证明。先处理 $n\ge2$。$0\le K<n$ 时，两条零尾给出 $\mu_{n,K}=qd$，归一化为 $g^{n-K}d=A_{n,K}$，与推论35.8的第一半相位下界相等。$K=n$ 时，平台给出 $a_n=d$；闭式使它在偶数 $n$ 时正好为最小候选，在奇数 $n$ 时超过最小候选 $d-q$ 恰好 $q$。

剩余初始深度 $K=n+1$ 的闭式是

$$
A_{n,n+1}=q(1-d/g)
=g^{-1}\bigl(d-q(2-t)\bigr).
$$

由于 $0<d/g\le t^2/(1+q)<t^2<1$，此值严格为正。令 $h=q(2-t)$，上式给出 $0<h<d$。取一条尾 $\xi$，仅在其局部位置 $3n,3n+2$ 放一。两位置不相邻，首位为零，支持低于 $3(n+1)$，而

$$
\kappa(\xi)=(-t)^{3n}(1+t^2)=s q(2-t)=s h.
$$

偶数 $n$ 时，将 $\xi$ 作为正 guard 一尾，负 guard 零尾取零；奇数 $n$ 时，正尾取零，负尾取 $\xi$。两种情形的实际差值都恰为 $h\in H_{n+1}$，两处 incoming guards 也都相容。其归一化余量为

$$
g^{-(n+1)}q(d-h)=g^{-1}(d-h)=A_{n,n+1}.
$$

这给出深度 $n+1$ 的实际达到。其余 $K\ge n+2$ 由定理35.11覆盖，所以 $n\ge2$ 的全部深度均已确定。

$n=1$ 独立处理，不使用要求 $q\le g^2$ 的数量估计。推论35.8已给出共同候选最小值 $A=t^4/2=qd$，$d=t/2$。深度零的零尾达到 $a_0=A$，引理35.4的复制与命题35.5的下界共同将等式传播到所有偶数深度。深度一的平台给出 $a_1=d>A$。

在深度三，正 guard 一尾取零，负 guard 零尾仅在局部位置 $3,5,8$ 放一。这些位合法且支持低于九；实际差值为

$$
h=t^3+t^5-t^8=28t-17=d-\frac{t^{10}}2.
$$

由 $0<t^{10}<t$ 得 $0<h<d$，其余量为

$$
g(d-h)=\frac{t^{13}}2=Ag^3.
$$

全局下界使 $a_3=A$；合法复制再覆盖全部奇数深度 $K\ge3$。故 $n=1$ 时只有 $K=1$ 例外，恰与所述通式一致。

最后，同相位下 $g^{K+2n}=q^2g^K$。唯一异常归一化增量 $q$ 发生在奇数 $n$ 的 $K=n$，它在未归一化余量中等于 $q^2$；乘以 $q^2$ 后产生修正 $q^4$。后移深度 $K+2n$ 不可能等于异常深度 $n$，所以递推正好有这一处例外。偶数 $n$ 时所有非负深度都满足无修正递推；奇数 $n$ 时递推在 $K=n$ 严格失败，其他深度成立，故最早全局起点恰为 $n+1$。$\square$

### 35.辛 商环单位阶与最小周期

**定理 35.13（任意拟议周期的排除与相位严格区分）。** 序列 $a_K$ 的最小最终周期为 $2n$（$n\ge2$）及一（$n=1$）。$n\ge2$ 时全部 $2n$ 个相位值两两不同；$n=1$ 时 $a_K=t^4/2$ 在 $K=0$ 与全部 $K\ge2$ 成立，其最终常值段的最早起点为二。

证明。实际达到已经由定理35.12建立。现在令 $I=(1+q)R$，对候选 $a$ 写 $b=(1+q)a\in R$。候选的相位条件恰为

$$
d+ag^k\in R
\quad\Longleftrightarrow\quad
bg^k\equiv-\delta\pmod I.
$$

$g$ 与 $\delta$ 都是单位；所以一旦 $a$ 满足某相位条件，$b$ 在 $R/I$ 中也为单位。若同一 $a$ 满足相位 $k,\ell$，可合法消去 $b$，得到 $g^k\equiv g^\ell\pmod I$。这不要求商环为整环。反向，这个同余使两个相位条件等价，其余候选条件与相位无关，故两个非空候选集相等。否则它们不相交。因此

$$
\boxed{A_{n,k}=A_{n,\ell}
\quad\Longleftrightarrow\quad g^k\equiv g^\ell\pmod I.}
$$

特别地，不同候选集的最小值不会偶然重合。$g^n\equiv-1\pmod I$ 给出 $g^{2n}\equiv1$，所以 $g$ 的单位阶 $o_n$ 存在且整除 $2n$。

若非零 $u\in I$，其整数范数必须满足 $|N(u)|\ge|N(1+q)|$。对 $j>0$，置 $v=g^j$，直接计算

$$
|N(1-g^j)|=
\begin{cases}
v^{-1}-v,&j\text{ 奇},\\
v^{-1}+v-2,&j\text{ 偶}
\end{cases}
<g^{-j}.
$$

并且

$$
g^{-(n-1)}<|N(1+q)|.
$$

偶数 $n$ 时右侧大于 $q^{-1}$，此式直接成立；奇数 $n$ 时两侧差为 $q^{-1}(1-g-q^2)>0$，因为 $q\le g<1/4$。于是对 $0<j<n$，

$$
|N(1-g^j)|<g^{-j}\le g^{-(n-1)}<|N(1+q)|,
$$

所以 $g^j\not\equiv1\pmod I$。$n\ge2$ 时 $q<g$，有

$$
|N(1+q)|\ge q^{-1}-q>g^{-1}-g=4=|N(2)|.
$$

若 $g^n\equiv1$，结合 $g^n\equiv-1$ 将给出 $2\in I$，与此范数界矛盾。$2n$ 的任何真因子至多为 $n$，故 $o_n=2n$。相位同余公式于是使全部 $2n$ 个相位最小值两两不同。

还须排除不整除 $2n$ 的任意拟议最终周期。若正整数 $p$ 是最终周期，取足够大的 $K$，使 $a_K$ 与 $a_{K+p}$ 都等于实际达到的相位最小值。相等最小值给出 $g^K\equiv g^{K+p}\pmod I$，消去单位 $g^K$ 得 $g^p\equiv1$，所以 $o_n\mid p$。反向，$o_n$ 的倍数保持各相位集合，也保持最终实际余量序列。因此最小最终周期正是 $o_n$。

$n=1$ 时，$1+g=2t$ 且 $t$ 是单位，故 $I=2R$；又 $g=2t-1\equiv1\pmod{2R}$，单位阶为一。推论35.8给出共同值 $t^4/2$，定理35.12给出仅深度一例外且该处为较大的 $d$，因此最终常值段恰从二开始。$\square$

**推论 35.14（全部整倍深度与联合参数阶）。** 对 $\ell\ge0$，

$$
\boxed{\mu_{n,2\ell n}=q^{2\ell+1}d.}
$$

对正奇数 $j$，

$$
\boxed{\mu_{n,jn}=q^j
\begin{cases}
d,&n\text{ 偶，或 }j=1,\\
d-q=q(t-d),&n\text{ 奇且 }j\ge3.
\end{cases}}
$$

证明。偶数倍的相位为零，$A_{n,0}=qd$ 且无异常；奇数倍的相位为 $n$，代入推论35.8与定理35.12即可。特别地，联合变化的 $n,K$ 在偶数倍深度上有 $\mu_{n,K}\asymp g^{2n+K}$，在正奇数倍深度上有 $\mu_{n,K}\asymp g^{n+K}$，两处比较常数均可独立于 $n,K$。因为 $d/q=\phi/(1+q)$ 被两个固定正数夹住，而

$$
\frac{d-q}{q}=\frac{t-q}{1+q}
\ge\frac{t-g}{1+g}>0.
$$

这些结论直接来自全部深度公式，无需另加一组部分和最优性证明。$\square$

### 35.壬 有效记录类的达到距离与额外误差

**命题 35.15（有效类距离及闭开扰动的精确边界）。** 在原始每坐标闭半径 $d/2$ 下，对合法目标前缀 $u$ 定义

$$
V_u^{n,K}=\bigcup_{\substack{\omega\in D_{3(n+K)}\\P_n(\omega)=u}}
\left(E_n(\omega)+[-d/2,d/2]^2\right).
$$

则不同目标类的最小距离达到，并且

$$
\boxed{\min_{u\ne v}\operatorname{dist}_\infty(V_u^{n,K},V_v^{n,K})
=\mu_{n,K}>0.}
$$

若在已经取得的有效记录上再允许任意实数的每坐标闭扰动半径 $\zeta\ge0$，一个共同前缀解码函数存在当且仅当 $2\zeta<\mu_{n,K}$。若新增扰动为正开半径 $\zeta>0$，条件恰为 $2\zeta\le\mu_{n,K}$。

证明。两个中心 $p,q$ 的等半径闭方块之间，逐坐标的区间距离是 $\max\{|p_i-q_i|-d,0\}$；最大范数距离取两坐标最大值，所以

$$
\operatorname{dist}_\infty
\left(p+[-d/2,d/2]^2,q+[-d/2,d/2]^2\right)
=\max\{\|p-q\|_\infty-d,0\}.
$$

方块紧致，距离由某对实际允许误差后的记录达到。再对有限个不同前缀中心取最小值，定理35.3保证 $d_{n,K}>d$，故所得精确距离为 $d_{n,K}-d=\mu_{n,K}$，且仍达到。

两份原有效记录若额外闭扰动后相同，它们原距离至多 $2\zeta$。因此 $2\zeta<\mu_{n,K}$ 时不同前缀的新增记录域两两不交，按所属类给出共同解码函数。反向，取距离恰为 $\mu_{n,K}$ 的不同类记录，其实数中点到二者的最大范数距离均为 $\mu_{n,K}/2$；若 $2\zeta\ge\mu_{n,K}$，这个中点是两个闭扰动合同共同允许的记录，无法解码。正开扰动时，两处严格误差使共同记录要求原距离严格小于 $2\zeta$，故等号仍充分；严格超过时同一中点给出必要性。$\square$

### 35.癸 普通有理 Cauchy 访问的精度与边界

**定理 35.16（保证精度与最坏最大请求指数）。** 对同一已经取得的有效记录，每次查询整数指数 $p\ge0$ 返回有理近似，认证每坐标绝对误差不超过 $2^{-p}$。要求解码对全部有效记录及全部合法名字均正确并终止，允许自适应查询。其最坏最大请求指数的最优值满足

$$
\boxed{p_{\rm worst}(n,K)=\log_2(1/\mu_{n,K})+O(1),}
$$

这里的加性常数可独立于 $n,K$。一个显式充分指数是

$$
\boxed{p=\left\lceil(2n+K)\log_2(1/g)\right\rceil+3.}
$$

固定 $n$ 时，$p_{\rm worst}(n,K)=K\log_2(1/g)+O_n(1)$；在偶数整倍深度与正奇数整倍深度上分别为

$$
(2n+K)\log_2(1/g)+O(1),\qquad
(n+K)\log_2(1/g)+O(1).
$$

证明。先选 $\rho=2^{-p}<\mu_{n,K}/2$，查询两个记录坐标到该精度，得到有理向量 $v$。考虑实际有限来源中满足

$$
\|v-E_n(\omega)\|_\infty\le d/2+\rho
$$

的相容集合。真实来源在其中；若两个相容来源的前缀不同，三角不等式将给出

$$
\|E_n(\omega)-E_n(\nu)\|_\infty
\le d+2\rho<d+\mu_{n,K}=d_{n,K},
$$

矛盾。因此相容集合有唯一的目标前缀。有限来源中心和 $d$ 属于已知代数域，和有理 $v,\rho$ 的比较可精确判定；这给出有限终止的访问判据，不附加寻找该集合的时间界。

取 $p=\lceil\log_2(2/\mu_{n,K})\rceil+1$ 就有严格充分精度，给出普适加性常数的上界。定理35.3的粗下界还给出

$$
\mu_{n,K}\ge g^{2n+K}/3,\qquad
2^{-\lceil(2n+K)\log_2(1/g)\rceil-3}
\le g^{2n+K}/8<\mu_{n,K}/2,
$$

所以所列显式指数充分。

为证必要的最大请求指数阶，取命题35.15中距离恰为 $\mu_{n,K}$ 的不同前缀有效记录 $r^0,r^1$。只要某查询的认证半径严格大于 $\mu_{n,K}/2$，两个坐标的允许近似区间都有包含中点的非空内部，故存在同时合法的有理答复，甚至可选为对两个记录都严格合法。

如果一个共同解码程序在所有名字上请求的指数都不超过整数 $P$，且 $2^{-P}>\mu_{n,K}/2$，可为每个指数不超过 $P$ 预选这种共享有理答复；其余更细指数分别补成两个记录的合法名字。程序沿这两个名字的查询、答复和自适应选择完全相同。其终止输出也相同，却必须分别输出两个不同前缀，矛盾。因此这样的 $P$ 不能保证全部名字上的恢复，得到 $\log_2(1/\mu_{n,K})$ 减去普适常数的下界。结合充分指数即得所述最优阶。

当认证半径恰好等于 $\mu_{n,K}/2$ 时，共同近似区间可以退化为无理单点，未必含有理答复。故这里的必要性使用严格大于，不能从命题35.15的任意实扰动闭等号直接推导出普通有理答复的统一等号阈值。

固定 $n$ 的阶由定理35.3给出；两个联合整倍深度的阶由推论35.14的精确值及其普适比较常数给出。其余深度由推论35.8与定理35.12的闭式和唯一异常项精确确定。$\square$

### 35.子 边界精度、隐藏体部与结论范围

给定 $K$ 时，隐藏体部的支持上界使不同前缀的有效两端点记录类拥有正且达到的距离 $\mu_{n,K}$。因此原始闭临界误差之后仍有严格的额外访问余量；有限尾数量约束、guard 相容性与同一来源的端点方程共同决定这个余量。随着允许的隐藏体部增长，$\mu_{n,K}$ 非增趋于零，固定 $n$ 的最大请求指数按 $K\log_2(1/g)+O_n(1)$ 增长。

只承诺每条来源最终有限、却不给共同支持证书时，推论34.6仍给出 $D$ 上闭临界的集合论恢复；定理34.11则给出普通 Cauchy 名字对全部有效记录的终止障碍。消失的是跨全部允许来源的正记录距离与统一精度保障，并不是每个有限域中的可识别性。两个已取得端点的精度、两个端点的联合相容性以及完整来源的结束认证，因而是不同的任务关系。

本章复用定理23.2的实际码本间距与分块间隙、约定1.3和命题1.2的正数量来源表示、定义14.5及定理17.2的合法 guard 区间实现，以及第34章的共同端点与临界访问合同。全部结论限于已知 $n,K$、实际 $D_{3(n+K)}$、前 $n$ 窗目标、两次共同来源取得及每坐标原始闭误差 $d/2$。精度指数衡量访问已有记录所请求的认证准确度，不是总存储、运行时间、查询次数、额外物理取得或 End 检测；折叠及删窗的这些关系也不作物理时空生成、物理时间箭头或普遍遗忘的断言。

## 追加锚（35·本行以下为增补区）

## 36. 完整历史的精确常数阈值、单一记忆转变与有效有理逼近

### 36.1 同一来源、观察合同与已发布前提

本章固定临界六格仪器及实际 FIB 地址，不改变折叠、删除或 guard。置

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad g^2+4g=1,
$$

$$
\lambda=\frac{t^2}{10}=\frac{1-g}{20},\qquad
\rho=\frac{239g-44}{380},\qquad
X=I_0=[-1,\phi],\quad I_1=[-1,t].
$$

窗口字母表为 $\Lambda=\{3,0,5,2,25\}$，其中 $0$ 是空窗，$25$ 是一个三位窗口标签；颜色字母表为 $\mathcal C=\{0,1,2,3,4,5\}$。实际合法边、平移量及分支为

$$
\begin{gathered}
0\to0:3,0,2;\qquad 0\to1:5,25;\qquad
1\to0:3,0;\qquad 1\to1:5,\\
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})=(-t,0,t^2,1,2-t),\\
f_\ell(y)=\Delta_\ell-gy,\qquad
F_\ell(x)=\frac{\Delta_\ell-x}{g}.
\end{gathered}
$$

$\Omega=A_0$ 是起始 guard 零的完整合法地址空间；$A_1$ 是 incoming guard 一允许的地址，$D_s\subset A_s$ 是最终空尾地址，$D=D_0$。两个状态使用同一个窗口级数，$\kappa_s(A_s)=I_s$。每条合法边 $s\xrightarrow{\ell}s'$ 的完整闭分支域为 $f_\ell(I_{s'})$；按空间排列的五个根像依次是

$$
[-1,-t^2],\quad[-t^2,g],\quad[g,t],\quad[t,2t],\quad[2t,\phi].
$$

固定切点

$$
(a,b,c,d,e)=(-t^2-\lambda,\ g-3\lambda,\ t-5\lambda,\ 2t-7\lambda,\ 2t+\lambda).
$$

每个切点只有一个固定合法归属，整条记录始终使用同一个 $Q$。记实际格为 $C_i=Q^{-1}(i)$，其闭包为 $J_i=[l_i,r_i]$；六格均有正长度。任一记录的所有坐标由一个实际地址承担：

$$
x_j(\omega)=\kappa_{s_j}(T^j\omega)=\kappa_0(T^j\omega),\qquad
x_j=\Delta_{\sigma_j(\omega)}-gx_{j+1},\qquad
r_j=Q\!\left(\operatorname{clip}_X(x_j+e_j)\right).
$$

误差在裁剪前独立选取，不能为不同位置另换来源。闭预算为 $|e_j|\le\nu$；正开预算只在 $\nu>0$ 使用，要求每个 $|e_j|<\nu$；逐记录严格余量合同要求每条记录存在自己的 $\varepsilon_r>0$，使 $\sup_j|e_j|\le\nu-\varepsilon_r$，不要求整个记录类共用一个正余量。

**定义 36.9（完整记忆恢复合同）。** 解码器确定、因果，从固定初态出发；每次实际取得允许有限计算和一个有限输出批次。输出按位置有序、只追加、不可回读。在每条实际 $\Omega$ 记录上，累计输出始终是真实地址的前缀；在每条实际 $D$ 记录上，每个位置最终经有限取得和有限计算输出，包括全部空窗补齐。没有 End、支持上界、输入免费重放或免费可读时钟。

完整配置包括所有能影响未来动作的可读控制、持久与临时数据、计数器、位置、时序信息和输出侧存储。记 $B^{\mathrm{worst}}_{\nu,\mathcal A}(N)$ 为解码器 $\mathcal A$ 在固定合同的全部实际记录上，截至第 $N$ 次取得的完整存储峰值的上确界。上界是存在一个固定解码器、对全部实际记录一致成立的界；下界对每个满足合同的解码器成立，见证可随有限视界 $N$ 改变。最优阶数同时包含这两个量词，不给任意低效解码器强加上界。固定宽度 $B$ 位最多容纳 $2^B$ 个完整配置；长度至多 $B$ 的完整二进制串最多容纳 $2^{B+1}-1$ 个配置。固定控制若另编码，也计价。

本章引用的已发布前提均指本卷[固定修订 `819c6e825e6f06abdaf195b18fa3ec5ba8423217`](https://github.com/the-omega-institute/trureturing/blob/819c6e825e6f06abdaf195b18fa3ec5ba8423217/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md)：定义14.5、命题14.6、定理17.2给出实际地址、端点尾、guard 相对满像和合法前接；第27.1节及第30.2节给出合法空尾截断。保留一个长度 $M$ 前缀而替换其终尾时，有同一来源的精确恒等式

$$
\widehat x_j-x_j=(-g)^{M-j}(\widehat x_M-x_M),\qquad 0\le j\le M.
$$

因此 $D_s$ 的标量像在 $I_s$ 中稠密。每个有限尾的标量属于 $\mathbb Z[t]$；反方向不作为前提，属于 $\mathbb Q(t)$ 或 $\mathbb Z[t]$ 不自动给出有限尾实现。

引理31.2、定义31.3和定理31.4对任一有限 $\mathbb Q(t)$ 端点闭观察族给出有限逆闭合端点集 $B$。节点为 $(s,P)$，包含全部端点单点片及相邻端点间的整个闭区间；唯一边规则是

$$
(s,P)\xrightarrow{\ell}(s',P')
\quad\Longleftrightarrow\quad
s\xrightarrow{\ell}s'\text{ 合法},\quad
P\subseteq f_\ell(I_{s'}),\quad P'\subseteq F_\ell(P).
$$

颜色 $i$ 在节点容许，当且仅当整个 $P\subseteq E_i$。实际闭关系地址有规范片路径；任一有限路径可从其终端片的任意一个点及编码该点的一条实际合法尾，倒向提升为一个共同地址。无限路径也有同一地址的收缩提升，底层图无死端。两条包含条件不能换成相交；闭关系路径不自动是含噪实际记录。

定理28.1给出 $D$ 上临界完整闭关系唯一性；推论29.3、定理30.6给出每条实际 $D$ 记录在 $\Omega$ 闭候选中的单点交及每个固定前缀的有限持续认证。定理33.13给出闭预算 $\lambda$ 下的一个 $O(N+1)$ 完整峰值解码器。定理33.10—33.11、推论33.12及定理33.14给出指定的

$$
\nu_0=\frac{\lambda+\max\{\rho_U,R_C\}}2\in\mathbb Q(t),\qquad
R_C=\frac{\lambda+g^2t^2}{2},\qquad \nu_0<\lambda,
$$

其中 $\rho_U$ 是定义33.9的有限端点最大距离；百窗族的完整误差具有一个共同上界 $R_0<\nu_0$，并在 $N_n=26+100n$ 给出 $n$ 位线性下界。本章直接使用这些结果，不重构百窗族；第33章所述两个区间不包含以下新定义的全局半径 $R$。

采集计数有两个用途。泵送、误差转移与六层证书在位置 $0,\ldots,M-1$ 取得 $M$ 个出发颜色，再走 $M$ 条来源边；位置 $M$ 未观察，接上的未来是终尾的 $S_\xi$。残余解码器取得 $n$ 色、走 $n-1$ 边；位置 $n-1$ 已观察，若其终尾为 $\xi$，随后零误差未来从 $S_{T\xi}$ 开始，不能再次取得终端坐标。

### 36.2 精确有限视界与严格误差的对数下界

**引理 36.10（局部分隔、四色回返与六窗强制）。** 对 $0\le\nu<\lambda$ 置 $\delta=\lambda-\nu$。临界闭扩张为

$$
\begin{aligned}
E_0^\lambda&=[-1,-t^2],& E_1^\lambda&=[-6t^2/5,g-t^2/5],\\
E_2^\lambda&=[g-2t^2/5,t-2t^2/5],&E_3^\lambda&=[t-3t^2/5,2t-3t^2/5],\\
E_4^\lambda&=[2t-4t^2/5,2t+t^2/5],&E_5^\lambda&=[2t,\phi].
\end{aligned}
$$

半径 $\nu$ 的内部端点各向内移动 $\delta$；$E_0^\nu=[-1,-t^2-\delta]$，$E_5^\nu=[2t+\delta,\phi]$。端色不容不同当前标签。内部共同色的不同标签、下一共同色与可能共同下一标签如下，$s_i=-1+i\phi/5$：

| 36.10 分隔类型 | 有序当前标签 | 下一共同色 | 若下一标签共同 |
| --- | --- | --- | --- |
| 36.10a 类型1 | $(3,0)$ | $0$ | $3$ |
| 36.10b 类型2 | $(0,5)$ | $1$ | $0$ |
| 36.10c 类型3 | $(5,2)$ | $1$ | $0$ |
| 36.10d 类型4 | $(2,25)$ | $2$ | $5$ |

按低、高当前分支编号的实际下一坐标满足 $u\le s_i-\delta/g$、$v\ge s_i+\delta/g$。三色中，类型3共同下一标签的必要界为 $\delta\le\max\{K_{31},K_{32}\}$，类型4的必要界为 $\delta\le K_4$，其中

$$
K_{31}=\frac{47g-11}{50},\qquad K_{32}=\frac{5-21g}{20},\qquad
K_4=\frac{9g-2}{25}=\frac{2g^3}{5(1+g^2)}.
$$

类型2若有四个共同颜色且下一标签共同，则必须

$$
\delta\le J:=\frac{2g^4}{5(1+g^3)}.
$$

在 $\nu\le\rho$ 时，类型2四色后在下一位置强制类型1，类型3三色后强制类型1，类型4三色后强制类型2。从类型1开始的 $6m$ 个共同闭颜色强制实际来源前缀

$$
P_A^m,\quad P_B^m,\qquad
P_A=(3,3,5,0,3,0),\quad P_B=(0,3,0,3,3,5).
$$

证明。分隔表及三色界使用定义33.1、引理33.2的全部闭分支和合法尾域计算：$E_i^\lambda=[f_{\ell_i}(s_i),f_{m_i}(s_i)]$，负斜率给上述下一坐标夹逼；中心只属于表列下一扩张格。若下一标签共同，两步中心依次为 $2t/5,1+4t/5,t/5,3t/5$。类型3只剩第三色1或2，分别给 $K_{31},K_{32}$；类型4只剩第三色2，给 $K_4$。这些必要条件保持同一对完整轨迹。

对类型2共同下一标签0，第三色为5，两步坐标满足

$$
x_2^{\rm low}\ge z+\delta/g^2,\quad
x_2^{\rm high}\le z-\delta/g^2,\qquad z=1+4t/5.
$$

色5在 $\delta>0$ 下强制两条实际标签25。再逆一次，第四坐标夹住

$$
w=\frac{2-t-z}{g}=\frac{g-5}{10},\qquad
x_3^{\rm low}\le w-\delta/g^3,\quad x_3^{\rm high}\ge w+\delta/g^3.
$$

$w$ 只在 $E_0^\lambda$ 内，因为 $-1<w<-t^2$，且 $\min E_1^\lambda-w=(5g-1)/10>0$。共同第四闭格必须含 $w$，故是色0。其上端给 $w+\delta/g^3\le-t^2-\delta$；用 $-t^2-w=2g/5$ 得 $\delta\le J$。

$g$ 是 $x^2+4x-1$ 的正根；在正轴的单调性给 $4/17<g<17/72<1/4$。直接比较有

$$
\delta_\rho:=\lambda-\rho=\frac{63-258g}{380},\qquad
\delta_\rho-K_4=\frac{467-1974g}{1900}>\frac{11}{22800}>0,
$$

$$
K_4-K_{31}=\frac{7-29g}{50}>0,\quad
K_4-K_{32}=\frac{141g-33}{100}>0,
$$

$$
\frac{J}{K_4}=\frac{g(1+g^2)}{1+g^3}<1,\qquad
\frac{g^4/5}{K_4}=\frac{g(1+g^2)}2<1.
$$

故 $\delta_\rho>K_4>\max\{K_{31},K_{32},J,g^4/5\}$。对类型1，下一色0强制两条下一标签3；第三色2，两步中心 $z_1=2t/5$ 给

$$
x_2^A\ge z_1+\delta/g^2,\qquad x_2^B\le z_1-\delta/g^2.
$$

$z_1-g=g^2/5$ 且 $\delta>g^4/5$，故 $x_2^A>g>x_2^B$；色2只含标签0、5，得到 $(3,3,5)$ 与 $(0,3,0)$。末位置是类型2，四个共同颜色又在下一位置强制类型1，且两来源角色互换。两组三窗组成 $P_A,P_B$；它们都合法，$P_A$ 回 guard 零，$P_B$ 回 guard 一且下一0合法。

第 $r$ 个三窗起点为 $3r$，向下一组三窗传播只使用位置 $3r+2,\ldots,3r+5$。产生 $2m$ 组三窗的最后传播在 $r=2m-2$，只用到 $6m-1$；所以 $6m$ 颜色足够，不多用一个终端颜色。$\square$

**定理 36.11（准确有限延迟阈值）。** 对每种固定归属，在 $D$ 或 $\Omega$ 上存在统一首窗有限取得视界的闭预算恰为 $0\le\nu<\rho$，正开预算恰为 $0<\nu<\rho$。若 $m\ge1$ 满足

$$
\phi^2g^{6m}<\rho-\nu,
$$

则 $6m+2$ 色足够；滑动该有限表得到对全部 $\Omega$ 安全、对 $D$ 逐位置生效的常数完整记忆解码器，延迟 $6m+1$。在 $\rho$，每个有限视界均有首窗不同的实际 $D/D$ 共同前缀，所有受约束误差严格小于 $\rho$，目标在格内部。

证明。同一六分支复合与其固定点为

$$
f_{P_A}(x)=30-129g+g^6x,\qquad
\alpha=\kappa(P_A^\infty)=\frac{-33-6g}{76},\qquad a-\alpha=\rho.
$$

任一实际 $P_A^m$ 柱与此周期成员在根坐标的差至多 $\phi^2g^{6m}$。若首色1而从类型1开始共享 $6m$ 色，引理36.10强制该柱，遂

$$
x_0^A\le\alpha+\phi^2g^{6m}<a-\nu,
$$

与色1的闭必要下端 $a-\nu$ 矛盾。初始类型2、3在偏移1进入类型1，类型4在偏移2进入；其传播窗口分别最多用到位置3、2、4。$6m+2$ 色包含每一种进入后的 $6m$ 强制块，因此排除全部首标签分歧。证明使用归属无关的闭关系，对所有固定归属共同成立。每个可行色词赋予唯一首标签，不可行词任赋固定标签，即得有限表；移位的 guard 一尾也是根 guard 零允许的地址，故滑动应用安全。表、暖机、固定色缓冲和工作控制全部计价，不需增长计数器，得到常数完整存储。

端点反方向需要实际目标。命题28.3的周期六坐标及所需颜色为

| 36.11 周期相位 | $z_j$ | 颜色 |
| --- | --- | --- |
| 36.11a 相位0 | $-(33+6g)/76=\alpha$ | $1$ |
| 36.11b 相位1 | $-(52+5g)/76$ | $0$ |
| 36.11c 相位2 | $(23+14g)/76$ | $2$ |
| 36.11d 相位3 | $(8+15g)/76$ | $1$ |
| 36.11e 相位4 | $-(47+8g)/76$ | $0$ |
| 36.11f 相位5 | $(6+9g)/76$ | $2$ |

$P_B^\infty$ 的坐标为该表的三位循环移位。除 $z_0$ 外，各相位到所需格内部目标有严格余量：

$$
-1<z_1<z_4<a,\qquad b<z_2<c,
$$

$$
0<z_3-b=\frac{97-362g}{380}<\rho,\qquad
0<b-z_5=\frac{392g-87}{380}<\rho.
$$

最后两个严格上界分别由 $\rho-(z_3-b)=(601g-141)/380>0$、$\rho-(b-z_5)=(43-153g)/380>0$ 给出。选足够小 $\eta>0$，将五个非临界相位固定送到 $z_1,z_2,b-\eta,z_4,b+\eta$；目标在正确格内部，误差最大值 $r_{\rm nb}<\rho$。再取

$$
0<\epsilon<\min\{\rho-r_{\rm nb},\rho,2(b-a)\}.
$$

给定取得长度 $H$，选 $k$ 使 $6k\ge H$ 且 $\phi^2g^{6k-H+1}<\epsilon$。两条实际有限地址

$$
\omega_{A,k}=P_A^k0^\infty,\qquad \omega_{B,k}=P_B^k0^\infty
$$

都合法，首标签为3、0。它们相对于各自周期地址的精确位移为

$$
x_j(\omega_{A,k})-z_{j\bmod6}=(-g)^{6k-j}(-z_0),
$$

$$
x_j(\omega_{B,k})-z_{(j+3)\bmod6}=(-g)^{6k-j}(-z_3),\qquad 0\le j<6k.
$$

在 $j<H$，位移绝对值小于 $\epsilon$。A 的临界相位 $j\equiv0\pmod6$ 有位移 $(-z_0)g^{6k-j}>0$；B 的临界相位 $j\equiv3\pmod6$ 有位移 $z_3g^{6k-j}>0$。所以每个临界值都为 $\alpha+q$，$0<q<\epsilon$，可送至内部目标 $a+q/2$，误差 $\rho-q/2\in(0,\rho)$。非临界相位保留原目标，误差仍小于 $\rho$。裁剪固定全部目标，所有归属给相同颜色 $(1,0,2)^\infty|_H$。

第 $H$ 次取得后，两条来源各取零误差，成为各自一个完整实际 $D$ 记录。有限前缀的误差最大值严格小于 $\rho$，故每条完整记录有自己的正严格余量。并不要求它们在第 $H$ 色后继续共同。任意 $H$ 的这些实际前缀排除统一视界；它们也用于所有更大预算。$\square$

**命题 36.12（完整 $\Omega$ 记录的端点区别）。** 闭预算 $\rho$ 的完整记录在 $\Omega$ 上全部唯一，当且仅当切点 $a$ 归色0。正开预算 $\rho$ 的完整记录对所有归属全部唯一。每个 $\nu>\rho$ 都存在归属无关的实际周期完整碰撞，误差严格小于 $\nu$。

证明。若两地址有同一完整记录，取其首个不同窗口。相应移位尾仍合法；引理36.10在不超过两步后得到类型1，任意长六窗强制及收缩使两尾必须为 $P_A^\infty,P_B^\infty$，可交换角色。某相位的真实值为 $\alpha$，所需色1的唯一闭预算 $\rho$ 目标是 $a$。当 $a$ 归色0时不可取得；在正开误差下，无论归属亦不可取得，故没有首个分歧。

若 $a$ 归色1，在临界相位用目标 $a$，其余相位用定理36.11的固定内部目标，两周期地址均得到 $(1,0,2)^\infty$。若 $\nu>\rho$，改用 $a+\theta$，其中 $0<\theta<\min\{b-a,\nu-\rho\}$；此目标内部，临界误差 $\rho+\theta<\nu$，其余误差更小，得到任意归属下的严格周期碰撞。证明逐一作用于首个不同窗口，不以图循环代替完整实际记录。周期碰撞不在 $D$，与 $D$ 上完整记录唯一性及逐位置生效相容。$\square$

**引理 36.13（精确观察、全部未决等式与有限前缀提升）。** 对固定归属、闭预算 $q\in\mathbb Q(t)\cap[0,\lambda]$，令

$$
O_i^{\le}=\{x\in X:\exists y\in C_i, |x-y|\le q\},\quad
E_i=\overline{O_i^{\le}},\quad Z_i=E_i\setminus O_i^{\le}.
$$

$O_i^{\le}$ 恰为实际含噪可取得关系，$Z_i$ 至多含两个扩张端点。对正半径 $q$ 的正开关系，有

$$
O_i^{<}=\{x\in X:\exists y\in C_i, |x-y|<q\}
=X\cap(l_i-q,r_i+q).
$$

它与切点归属无关，闭包仍为通常 $E_i$；在 $q=\rho$，其排除集为

$$
Z_0^{<}=\{a+\rho\},\quad Z_5^{<}=\{e-\rho\},\quad
Z_i^{<}=\{l_i-\rho,r_i+\rho\}\quad(1\le i\le4).
$$

$-1\in O_0^{<}$、$\phi\in O_5^{<}$，不能删除零误差可达的支撑端点。零严格预算的关系为空，另行处理，不代入上述正半径公式。

对这些 $E_i$ 用第31章构造 $B$ 和闭图。一个精确状态为 $(s,P,S)$，其中 $S\subseteq B\cap I_s$ 保存全部未决端点等式排除。读色 $i$ 要求 $P\subseteq E_i$，插入 $Z_i\cap P$；沿合法来源边更新为

$$
S'=\{F_\ell(z):z\in S\cup(Z_i\cap P), F_\ell(z)\in I_{s'}\}.
$$

两分量的 guard、片与集合分别保存。非退化片总是 $D_s$-live 和 $A_s$-live；单点 $P=\{z\}$ 的 $A_s$-live 条件为 $z\notin S$，$D_s$-live 还要求一条实际合法有限尾在 guard $s$ 编码 $z$。后者等价于带类型单点图从 $(s,\{z\})$ 有有限路径到标量零单点，两个终端 guard 均允许 $0^\infty$。一个有限出发观察路径从 guard 零、空集合开始，恰在各终端状态通过指定来源域 live 测试时，能用每分量一个实际完整来源实现全部规定颜色和边。

证明。裁剪不增加到 $x\in X$ 的距离；实际裁剪后目标在 $C_i$，故属于 $O_i$。反向取定义中的一个 $y$，使用误差 $y-x$，裁剪固定 $y$。对正开关系，两个开区间 $(l_i,r_i)$ 与 $(x-q,x+q)$ 相交恰给所列严格不等式，选内部目标即可。这也说明只排除扩张接触，保留支撑截断端点。

有限性来自 $\mathbb Q(t)$ 的闭包端点及引理31.2，不来自待编码点的域成员身份。若过去坐标的禁止等式为 $x_j=z$，在同一实际边链上，它等价于当前尾值等于运输后的逆阈值。阈值离开实际下一 guard 区间时，该等式对全部合法延续不可能；否则保留。负斜率不改变等式真假，不需符号旗标；不同旧义务到达同一阈值时可合并，因为它们询问同一当前坐标的相同等式。若阈值永久未离开，收缩给 $|x_j-z|\le g^r\operatorname{diam}X\to0$，故等式确实成立。因 $B$ 逆闭合，全部集合状态有限。

非退化基本片的内部不含 $B$，所以不含任何未决阈值；由满像及合法空尾截断稠密性，可在内部选一个实际 $D_s$ 尾标量。单点必须避免 $S$，并在 $D_s$ 情形具有实际有限尾。$0\in B$，且一个 $B$ 内有限尾的逆轨迹留在 $B$，最终到零；反向，从带类型单点的有限合法路径到零可前接零尾。因此单点到零测试准确，不能只用 $z\in\mathbb Q(t)$ 代替。

选定一个通过 live 测试的终尾，从它倒向提升整个有限路径。未决义务由终尾标量避开，已解除义务对所有延续不成立，片外的端点从未成为义务；所以每个旧坐标属于 $E_i\setminus Z_i=O_i$。逐坐标选实际目标，前缀外取零误差，得到同一个完整来源的实际记录。反向，任一实际记录的规范路径终值避开所有未决等式，单点若为有限尾则可到零，故通过测试。

等价地，live 状态可以经不增加颜色义务的未观察来源边到达空集合；$D$ 情形再到两片均含零。选定终尾避开阈值时，每个旧阈值必在有限步离开 guard 区间，否则刚证的永久等式与避开条件矛盾；有限集合于是全部清除。反向用清除路径及终尾作整条提升即可。这些未观察边仅决定完成存在性，不是解码器额外取得。$\square$

**定理 36.14（混合 live 图的常数构造与泵送容量）。** 在引理36.13的精确关系中，将第一分量指定为 $D$-live、第二分量指定为 $\Omega$-live。每步读一个共同出发色并走两个实际来源边；从全部 guard 零、空集合初态出发，第一步要求不同来源标签，之后保留全部可达混合 live 状态。若该图在第一分歧后有 $M$ 个顶点且无环，$H=M+1$ 色给一个常数完整记忆解码器，$\Omega$ 安全、$D$ 延迟 $M$ 生效。若有可达返回环且合同有解码器，则存在固定 $a,m\ge1$，使每个合法解码器在某一实际 $D$ 记录上，截至 $N\ge a$ 访问至少

$$
1+\left\lfloor\frac{N-a}{m}\right\rfloor
$$

个不同完整配置。相应完整二进制峰值为 $\Omega(\log(N+2))$。

证明。精确提升将长度 $L$ 的实际混合首窗歧义等价为首步后的 $L-1$ 条 live 边。无环图至多有 $M$ 个路径顶点，故歧义长度至多 $M$。在每个 $H$ 色词上，列其全部实际 $\Omega$ 完成的首标签：单点返回标签，否则返回永久停止指令。滑动保存 $H-1$ 色、有限暖机和停止位。实际 $\Omega$ 尾始终在表候选中，所发标签安全；实际 $D$ 的每个移位 $H$ 色词均无异标签 $\Omega$ 完成，停止不发生，每个位置延迟 $M$ 输出。固定表及全部工作控制计价且有限。

有环时，固定包含首次分歧的 stem、一个返回环，并记颜色词 $h,w$，两分量来源词 $P,Q$ 和 $A,B$，其中 $|h|=|P|=|Q|=a$、$|w|=|A|=|B|=m$、$P_0\ne Q_0$。完整返回状态含全部 guard、片和未决集合。在其两片中固定实际尾 $\xi\in D$、$\eta\in\Omega$，标量避开各自未决集合。对每个 $k\ge0$，同一终尾的整条提升给

$$
\alpha_k=PA^k\xi\in D,\qquad \beta_k=QB^k\eta\in\Omega,
$$

及实际完整记录 $hw^kS_\xi$、$hw^kS_\eta$。恰有 $a+km$ 个出发颜色及来源边，终端未观察，所以这些未来不重复一个坐标。不同首窗迫使 $hw^k$ 上累计输出为空。

先排除空尾导致的来源合并。若 $\alpha_i=\alpha_j$，$i<j$，消去共同有限前缀得到 $\xi=A^{j-i}\xi$，所以 $\xi=A^\infty$。因 $\xi$ 最终为空，必有 $A=0^m$、$\xi=0^\infty$，全部 $\alpha_k=P0^\infty$。这时一个固定 $D$ 来源在精确关系中实现每个 $hw^k$，故逐坐标选择实际允许目标即可实现 $hw^\infty$，没有使用闭端点目标的极限。每个有限取得位于某个强制静默检查点之前，按序追加使此记录永远无输出，违背首窗生效。因此有合法解码器时 $\alpha_k$ 两两不同。

令 $q_k$ 为有限处理 $hw^k$ 后的完整配置；每个前缀有实际 $D$ 延续，故阶段有限处理保证配置存在。若 $q_i=q_j$，接同一个实际未来 $S_\xi$ 后，确定性给相同未来输出；此前输出为空，而 $D$ 生效要求总补齐来源分别为不同的 $\alpha_i,\alpha_j$，矛盾。可读计数和时序均在配置内，不提供免费绝对阶段。

令 $K_N=\lfloor(N-a)/m\rfloor$。一个实际记录 $hw^{K_N}S_\xi$ 经过 $q_0,\ldots,q_{K_N}$，全部检查点不晚于 $N$。若峰值为 $B_N$，固定宽度给 $2^{B_N}\ge K_N+1$；可变长度给 $2^{B_N+1}-1\ge K_N+1$，即

$$
B_N\ge\lceil\log_2(K_N+1)\rceil
\quad\text{或}\quad
B_N\ge\lceil\log_2(K_N+2)\rceil-1.
$$

工作峰值不小于检查点持久存储。这个证明也适用于任何同形的精确正开关系；在逐记录严格余量合同中，常数来源排除还需该无限静默记录本身有严格余量，下面在 $\rho$ 单独满足此条件。$\square$

**定理 36.15（严格 $\rho$ 泵送及准确常数记忆范围）。** 对每种固定归属，在 $\rho$ 存在两条固定实际有限终尾及固定 $a,m\ge1$，使泵送记录满足

$$
\forall r\text{ 属于该族},\quad
\exists\varepsilon_r>0,\quad \sup_j|e_j(r)|\le\rho-\varepsilon_r.
$$

每个合法解码器在这族上有定理36.14的对数最坏峰值下界。这些同一见证适用于每个实数 $\nu\ge\rho$；在 $0\le\nu\le\lambda$ 的闭合同以及 $0<\nu\le\lambda$ 的两种严格合同中，常数完整记忆存在当且仅当 $\nu<\rho$。

证明。只在 $\rho\in\mathbb Q(t)$ 构造引理36.13的正开精确图，插入新的 $Z_i^{<}$，不沿用闭合同的排除集或闭泵送误差。第一步要求不同标签，两侧都保留 $D$-live。定理36.11的任意长实际严格 $D/D$ 前缀有其规范路径，有限图必有可达环。固定两条 $D$ 终尾 $\xi,\eta$，分别避开完整返回状态的未决集合。整条严格提升给实际 $PA^k\xi,QB^k\eta$ 及 $hw^kS_\xi,hw^kS_\eta$。每条记录的非零误差仅在有限前缀，每个严格小于 $\rho$，后接零误差，取有限最大值即得它自己的 $\varepsilon_r$；不把这些余量的下确界声称为正。

定理36.14的配置容量证明直接用于这族。为覆盖逐记录严格余量合同，再检查其常数来源排除：若 $A=0^m$、$\xi=0^\infty$，stem 后同一真实来源的每个标量均为零。环色只有有限种，各色在零处均由精确 $O_i^{<}$ 可取得；每种色固定选一个严格目标，stem 也只选有限个目标。因此 $hw^\infty$ 是一个具有统一严格余量的实际 $D$ 记录，仍因所有 $hw^k$ 检查点强制静默而违背生效。常数分支被排除，容量结论没有另做一份证明。

定理33.13的闭 $\lambda$ 解码器保证各合同存在合法解码器，因此不是无解情形。每个误差 $|e_j|<\rho\le\nu$，逐记录最大值也严格小于任何 $\nu\ge\rho$，同一族在所有这些实预算仍合法；不需要一般实数半径的有限图。低于 $\rho$ 则用定理36.11的闭有限表；对数下界排除 $\rho$ 及以上的常数存储。$\square$

### 36.3 全部亚临界闭候选的宽度与一个残余解码器

**引理 36.16（完整闭图的共同尾宽度）。** 对每个 $b_0\in\mathbb Q(t)\cap[0,\lambda)$，令 $G_{b_0}$ 为第31章对六个 $E_i^{b_0}$ 的完整闭图。一个固定历史的每个终端顶点至多支持一个不同过去来源词，包括所有无有限尾实现的 $\Omega$ 单点。取得 $n$ 色、走 $n-1$ 边时，若 $H_n$ 是全部不同词/终端顶点对，$R_n$ 是删除全局最长共同前缀后的对集，则

$$
|H_n|\le |V(G_{b_0})|,\qquad |R_n|\le |V(G_{b_0})|.
$$

该完整界不延伸到 $b_0=\lambda$：有限尾可达顶点仍至多一词，但某些实际 $\Omega$ 单点可有至少两个不同过去词。

证明。先区分精确关系与闭关系。引理36.13中，若两个路径到达同一 $D$-live 完整状态 $(s,P,S)$，可选择同一合法有限尾 $\xi$，其标量在 $P\setminus S$。整条提升给两个实际有限来源 $u\xi,v\xi$，取得同一过去色词，之后接同一实际未来。定理28.1的实际唯一性使 $u=v$。在 $n$ 色、$n-1$ 边约定下，先满足终端已经取得的颜色及其排除，再接 $S_{T\xi}$，不能重复 $S_\xi$ 的首坐标。

这一精确共同尾论证本身不蕴含闭候选界。一个抽象反例是零噪声支持 $[-1,2]$，实际格 $[-1,0],(0,1),[1,2]$，三条来源 $A0^\infty,B0^\infty,C0^\infty$ 的首真值分别为 $0,1,1/2$，以后共同真值 $-1$。三条实际完整记录分别以色0、2、1开始，因而唯一；把中格闭合为 $[0,1]$ 后，实际历史色1却有三个不同过去词到同一个有限尾状态。不可取得的两个闭端点造成多词，不能用实际唯一性消掉它们。

FIB 有额外的严格宽度性质。令 $\delta=\lambda-b_0>0$。实际根像穷尽共同闭格可含的不同标签，并给出：

| 36.16 共同闭颜色 | 可能不同标签 | 平移差 | 扩张格宽 |
| --- | --- | --- | --- |
| 36.16a 色0 | $(3,0)$ | $t$ | $t-\delta$ |
| 36.16b 色1 | $(3,0)$ | $t$ | $t-2\delta$ |
| 36.16c 色2 | $(0,5)$ | $t^2$ | $t^2-2\delta$ |
| 36.16d 色3 | $(5,2)$ | $t$ | $t-2\delta$ |
| 36.16e 色4 | $(2,25)$ | $t^2$ | $t^2-2\delta$ |
| 36.16f 色5 | $(2,25)$ | $t^2$ | $t^2-\delta$ |

端格列在 $\delta>0$ 已不可能，保留它们只放宽必要条件。内部四行由空间根像和临界扩张端点直接给出；缩小格不会添加新标签。每行宽度严格小于相应平移差。

若两条实际合法地址在某个截止以后完全同尾、此前不同，取最后不同来源标签的位置 $j$。共同实际 $x_{j+1}$ 使

$$
x_j^{(2)}-x_j^{(1)}
=\Delta_{\ell_j^{(2)}}-\Delta_{\ell_j^{(1)}}
$$

恰为表列平移差，不可能同时位于所需共同闭格。现在两个候选路径到同一 $(s,P)$，通过 guard 相对满像选择 $P$ 内任意一个点及编码它的同一实际 $\Omega$ 尾，即使 $P$ 为无有限尾实现的单点。整条提升使两个过去词接这条共同尾，最后不同标签论证迫使过去词相同。计数顶点并去掉全局共同前缀，得到全部候选界，没有删除任何 $\Omega$ 单点，也没有把宽度推出自实际记录唯一性。

在 $\lambda$，若顶点含实际有限尾标量，接同一有限尾可构成共同完整闭关系，定理28.1仍使过去词唯一。所有非退化片由截断稠密性具有这种尾。但完整单点界失败：取 $a,b$ 均归色1，令

$$
s_*=-1+\phi/5=\frac{-4+t}{5}\notin\mathbb Z[t],
$$

并取实际 guard 零尾 $\tau$ 编码 $s_*$。两条来源 $3\tau,0\tau$ 的当前真值分别为 $a-\lambda,b+\lambda$，送到实际目标 $a,b$ 后共同得到色1，之后为同一个 $S_\tau$。逆端点闭合包含单点 $(0,\{s_*\})$，故出发观察约定下该单点支持过去词3、0。两来源都不在 $D$，因为其共同移位尾标量不在 $\mathbb Z[t]$。这是真实闭预算单点例外，只说明至少两个，不说明无界重数。临界线性上界仍由定理33.13提供。$\square$

**定理 36.17（有界宽度、有界幂形式的完整残余解码器）。** 固定 $b_0\in\mathbb Q(t)\cap[0,\lambda)$ 及完整闭图。假设每个残余词都属于一个固定有限模板族

$$
a_0P_1^{k_1}a_1\cdots P_d^{k_d}a_d,\qquad
k_i\in\mathbb N,
$$

其中所有字面词、非空周期词均固定，幂因子数有固定上界，另允许空词和有限字面模板。则存在一个在每条实际闭预算 $\nu\le b_0$ 的 $\Omega$ 记录上安全、在每条实际 $D$ 记录上逐位置生效的解码器，完整工作与持久峰值为 $O(\log(N+2))$。每次处理和输出批次均有限。

证明。采用已观察终端约定，完整保留

$$
H_n=\{(v,w):\text{初始路径有 }n-1\text{ 条边、读 }r_0,\ldots,r_{n-1},
\text{终点 }v,\text{来源词 }w\}.
$$

每个 $w$ 长度 $n-1$，相同对合并，路径重数不计。设 $p_n$ 为这些词的全局最长共同前缀，

$$
R_n=\{(v,h):(v,p_nh)\in H_n\},\qquad
L_n=n-1-|p_n|.
$$

所有残余词长度相同。若 $L_n>0$，每个词都有一个首标签不同的伙伴；否则该词的首标签在所有词中相同，与最长性矛盾。引理36.16给固定候选对数量上界 $A=|V(G_{b_0})|$。

在第一个取得阶段，保存容许首色的全部初始 $(v,\varnothing)$。每个后续阶段保持精确不变量：已写出且不再保存的词是 $p_n$，保存的恰为全部 $R_n$，各词由规范模板标识和指数元组表示。读新色 $i$ 后，沿每条 $v\xrightarrow{\ell}v'$ 且 $v'$ 容许 $i$ 的边形成

$$
\widetilde R=\{(v',h\ell):(v,h)\in R_n,\ v\xrightarrow{\ell}v',\ i\in C(v')\}.
$$

合并完全相同的词/顶点对，求全部新词的最长共同前缀 $c$，依序输出 $c$ 并从每词删去它，再规范化。所得恰为 $R_{n+1}$，累计输出为 $p_nc=p_{n+1}$；旧候选只延长或删除，所以 $p_n$ 单调为前缀。空集进入永久静默状态，实际记录不会到达它。

存储证明包括整个更新而非只看最终描述。一个指数不超过残余长度，因周期词非空，故至多 $n$；每对用固定数量 $O(\log(n+2))$ 位整数。图最大出度固定，合并前至多 $A$ 乘该出度个描述；旧、临时及新描述共存仍只有固定数量。临时扩展只保存原规范元组和一个新标签，删前缀再添一个偏移，不能形成跨阶段的递归偏移链。

任意索引字符通过固定字面词、指数、块长度和余数计算，不展开词。词相等、去重和最长共同前缀都用位置扫描及固定数量长度、索引、偏移计数器。输出 $c$ 时，在任一保留扩展描述上逐字符扫描写出，只存批次长度与当前位置，不保存批次缓冲。规范化在固定模板表中逐一尝试指数元组，各坐标只遍历 $0,\ldots,L$，用索引扫描比对偏移描述；模板假设保证至少一次匹配，固定顺序取第一项。每个循环有限，循环计数器数量固定；不必保存搜索树或累计计算步数。找到规范形式后丢弃临时标签和偏移，再开始下一次取得。

所有计数、输入和输出位置、表、控制、旧元组、比较空间及当前写出控制均计价。每个可变整数不超过固定倍数的 $n+1$，故整个阶段及此前峰值为 $O(\log(N+2))$。有限计算不保证实时、吞吐量或多项式时间。

安全性来自整条闭图完备性：每个实际 $\Omega$ 来源始终有候选路径，$p_n$ 必为该同一真实来源前缀。对实际 $\omega_*\in D$，定义

$$
F_n^{b_0}(r)=\{\omega\in\Omega:x_j(\omega)\in E_{r_j}^{b_0},\ 0\le j<n\}.
$$

真实来源在内，且 $F_n^{b_0}(r)\subseteq F_n^\lambda(r)$。推论29.3给 $\bigcap_nF_n^\lambda(r)=\{\omega_*\}$，所以较小半径候选亦有同一单点交。闭候选紧致；每个固定错误前缀柱的补集最终被排除，取稍晚的 $n$ 使 $n-1$ 足以包含请求词长，便有 $|p_n|$ 至少为该词长。精确更新在有限阶段输出整个新共同前缀，故每个补齐位置最终输出。没有假定完整 $\Omega$ 记录全部可识别，也没有发 End。此安全性、规范化和生效证明用于以下所有对数上界，不另设一种残余实现。$\square$

### 36.4 局部复位、端点排除及一个有效可选的较大半径

置

$$
\nu_L=g-\frac15,\qquad
J_4=\frac{(9g-1)g^3}{10(1+g^3)},\qquad
C=\max\{J,J_4,g^4/5\},\qquad U=\lambda-C.
$$

**引理 36.18（类型4的两步复位与严格剩余余量）。** 在 $b_0<\lambda$、$\delta=\lambda-b_0>J_4$ 时，类型4的四个共同闭颜色使其在位置1或2成为类型2。并且

$$
0<C<K_{32},\qquad \rho<\nu_L<U<\lambda.
$$

证明。记当前标签2、25的来源为A、B，下一共同色2。若下一标签不同，则只能为0、5，已是位置1的类型2。若共同，必为5，两分量分别从 guard 零、一进入 guard 一；共同第三色2，两步中心为 $z_4=3t/5$，故

$$
x_2^A\ge z_4+\delta/g^2,\qquad x_2^B\le z_4-\delta/g^2.
$$

$z_4>g$，高坐标A在第三色2中必用标签5；另一标签若不同则是0，位置2成为角色交换后的类型2。若再次共同5，两侧从 guard 一继续合法逆5，第四坐标夹住

$$
q_*=\frac{t^2-z_4}{g}=\frac g5,\qquad
x_3^A\le q_*-\delta/g^3,\quad
x_3^B\ge q_*+\delta/g^3.
$$

$q_*$ 只在 $E_1^\lambda$ 内：它高于 $E_0^\lambda$，且

$$
\max E_1^\lambda-q_*=\frac{9g-1}{10}>0,\qquad
\min E_2^\lambda-q_*=\frac{5g-1}{5}>0.
$$

共同第四色于是为1，上端给
$q_*+\delta/g^3\le g-t^2/5-\delta$，即 $\delta\le J_4$，矛盾。全部逆映射作用于同一对实际完整轨迹，并保留每一步实际 guard。

由 $4/17<g<17/72<1/4$，

$$
K_{32}>\frac1{480},\qquad
K_{32}-K_{31}=\frac{47-199g}{100}>0,
$$

$$
J<\frac1{640},\qquad J_4<\frac1{512},\qquad
g^4/5<\frac1{1280}.
$$

$J_4$ 的上界使用 $9g-1<5/4$、$g^3<1/64$，各量均为正，遂 $C<K_{32}$。又 $\lambda-K_{32}=\nu_L$，且

$$
\nu_L-\rho=\frac{141g-32}{380}>0.
$$

得到全部比较；这些是精确代数比较，不给某个已选半径的数值读数。$\square$

**引理 36.19（类型3的闭等号枝与第六色排除）。** 在闭半径 $\nu_L$，类型3若共享三个颜色且下一标签相同，只剩第三色2的一条等号枝。当前高标签2的来源B满足

$$
x_0^B=d+\nu_L=\frac{9+47g}{20},\qquad
x_2^B=b-\nu_L=\frac{1+3g}{20}.
$$

实际取得该枝要求 $Q(d)=3$、$Q(b)=2$；B不在 $D$。在这些相容归属下，五个共同颜色确可由实际来源取得；六个共同闭颜色不可能，不论归属。特别地，在完整闭关系中，六色使类型3的下一标签分歧。

证明。第一标签5、2分别留下 guard 一、零，所有合法共同下一标签3、0、5均须考虑。局部分隔中心及下一色1排除共同3、5，只能共同0；其第三色1、2的必要界分别为 $K_{31},K_{32}$。由于 $\delta_L=\lambda-\nu_L=K_{32}>K_{31}$，只剩第三色2，且 $\delta_L=\lambda g^2$。以A表示初始标签5的来源，两步夹逼成为

$$
x_2^A\ge p:=\frac{3+g}{20},\qquad
x_2^B\le r:=\frac{1+3g}{20}.
$$

$r=b-\nu_L$ 正是 $E_2^{\nu_L}$ 下端，故 $x_2^B=r$。B的前两标签2、0随即强制

$$
x_1^B=-gr=\frac{11g-3}{20},\qquad
x_0^B=1-gx_1^B=\frac{9+47g}{20}.
$$

色3在第一位置只能用目标 $d$，色2在第三位置只能用目标 $b$，故须两项所列固定归属，误差分别为 $-\nu_L,+\nu_L$。这是两个不同切点的相容要求，不能误当同一切点归属矛盾；正开合同却排除两次等号。若任一归属不满足，精确图留下的相应未决等式不能解除。

每个移位有限尾标量属于 $\mathbb Z[t]$，但
$r=(-1+3t)/10\notin\mathbb Z[t]$，由 $t$ 无理、系数表示唯一即得。因此B不是最终空尾；仍须作为实际 $\Omega$ 候选保留。

若共享第四色，B在位置2有标签0，下一值为

$$
s=-r/g=-\frac{7+g}{20}.
$$

它只在扩张色1内，因为 $s-(a+\nu_L)=2g^2/5>0$，且 $s<b-\nu_L$。A的位置2只能为0或5。若为0，

$$
x_3^A\le-\frac{13+3g}{20}
<a-\nu_L=-\frac{7+9g}{20},
$$

与共同第四色1矛盾。若为5，两侧在位置2构成类型2；又

$$
x_2^A\le c+\nu_L=\frac{1+35g}{20}<2g=f_5(-t^2),
$$

负斜率给 $x_3^A>-t^2$，结合色1上端小于 $g$，A的位置3标签为0。B也如此，因为 $s+t^2=(3-11g)/20>0$。故此类型2有共同下一标签0。若原来共享六色，位置 $2,3,4,5$ 可用引理36.10的四色规则；$\delta_L=K_{32}>J$ 排除这个共同下一标签，矛盾。这个排除作用于完整闭关系，未用 $D$-live 或归属筛选。

五色实际见证保留该等号的准确边界。选 guard 一实际终尾标量

$$
y_A=\frac{3g-5}{20},\qquad y_B=\frac{g-13}{20},
$$

二者均在 $I_1$ 中；分别前接合法词 $(5,0,5,0,25)$ 与 $(2,0,0,0,25)$。整条实际分支等式给

| 36.19 五色位置 | A真值 | B真值 | 共同色 |
| --- | --- | --- | --- |
| 36.19a 位置0 | $(15-29g)/20$ | $(9+47g)/20$ | $3$ |
| 36.19b 位置1 | $-(1+5g)/20$ | $(11g-3)/20$ | $1$ |
| 36.19c 位置2 | $(9+g)/20$ | $(1+3g)/20$ | $2$ |
| 36.19d 位置3 | $(g-7)/20$ | $-(7+g)/20$ | $1$ |
| 36.19e 位置4 | $(27+7g)/20$ | $(29+7g)/20$ | $5$ |

取 $0<\epsilon<\min\{3g^2/10,g^3/10,d-c,c-b\}$。位置0把A送到 $c+\epsilon$、B送到 $d$；位置2把A送到 $c-\epsilon$、B送到 $b$；其余三处零误差。A的两误差余量分别为

$$
\nu_L-(c-x_0^A)=3g^2/10,\qquad
\nu_L-(x_2^A-c)=g^3/10,
$$

故其目标内部、误差严格在预算内。B两次误差恰为预算，所需归属保证色3、2；其他真值严格在色1、1、5内部。后接零误差得到实际完整记录，前五色 $(3,1,2,1,5)$，没有第六色共同延伸。可选尾由 guard 满像一次实现，不能把表中坐标分别选取。$\square$

**引理 36.20（完整紧致类型3域的严格间隙）。** 令

$$
\mathcal K=\{(\omega,\eta)\in\Omega^2:
\sigma_0(\omega)=5,\ \sigma_0(\eta)=2,\
\sigma_1(\omega)=\sigma_1(\eta)\}.
$$

对 $z,z'\in X$ 定义共同闭颜色成本

$$
c_*(z,z')=\min_i\max\{\operatorname{dist}(z,J_i),
\operatorname{dist}(z',J_i)\},\qquad
\mathcal C_6(\omega,\eta)=\max_{0\le j<6}c_*(x_j(\omega),x_j(\eta)).
$$

则非空紧致 $\mathcal K$ 上取得的最小值

$$
\beta_3=\min_{\mathcal K}\mathcal C_6
$$

满足 $\beta_3>\nu_L$。域保留全部共同下一标签3、0、5；成本使用闭格，不声称闭目标在任意归属下可取得。

证明。合法地址空间紧致，有限标签映射局部常值，实际标量映射连续，故 $\mathcal K$ 闭开、紧致。$(5,0)0^\infty$ 与 $(2,0)0^\infty$ 使其非空。有限个距离、最小值和最大值连续，故最小值取得。$\mathcal C_6\le v$ 当且仅当在六个位置分别有一个共同闭色，使同一两地址的坐标均在 $E_i^v$ 中。若取得的 $\beta_3\le\nu_L$，则一个完整域成员在 $\nu_L$ 有六个共同闭色；初始5、2在该预算唯一共同色为3，下一标签共同，与引理36.19矛盾。得到严格间隙。这不是非紧集上逐点严格不等式的统一化，也不只最小化旧等号枝。$\square$

**定理 36.21（六次出发证书、有效较大半径与全部单幂残余）。** 存在一个终止的精确选择程序，给出有理 $\widehat\nu$ 及有限证书，满足

$$
\nu_L<\widehat\nu<\min\{\beta_3,U\}<\lambda.
$$

在该半径，全部残余词属于固定族

$$
\Lambda^{\le8}\ \sqcup\
\{uP^kv:|u|\le3,\ P\in\{P_A,P_B\},\ |v|\le5,\ k\ge0\}.
$$

同一个定理36.17解码器于是对每个实预算 $0\le\nu\le\widehat\nu$ 给 $O(\log(N+2))$ 完整峰值上界，统一于所有固定归属。该程序与证书是终止规格，不给一个已经计算的半径值。

证明。对有理候选 $\mu<U$，在 $\mathbb Q(t)$ 中按引理31.2构造全部六个 $E_i^\mu$ 的完整闭图。将每个 guard 零顶点对放入层 $L_0$。在第 $j$ 步，只在当前两个顶点有共同容许色时，读取这个出发色并遍历两条来源边：第0步标签固定为 $(5,2)$；第1步两标签相同，包含所有合法3、0、5；第2、3、4、5步不限制来源标签。形成全部后继层 $L_{j+1}$，最后检查 $L_6=\varnothing$。

这是六个观察坐标 $0,\ldots,5$ 和六条来源边，位置6未观察。最后层不要求共同颜色，不加第七色；第六条边标签不受限制。任何实际完整地址都有这条边，不因此漏掉来源。没有归属排除、未决等式筛选或 $D$-live 筛选，所有 $\Omega$ 单点均保留。

若第六层非空，从两终端片各选一条实际合法尾，倒向提升全部六步，即有 $\mathcal K$ 中一个地址对共享六个闭色。反向，任一这样的完整地址对沿规范片到位置6，全部包含边及原来源标签保留，故到达 $L_6$。因此空层恰证所需缺席，即 $\mu<\beta_3$。

有限证书可包含 $\mu$、有限端点集及六层。检查端点集包含全部观察、guard 和分支域端点，且每个 $z\in B$、每个逆分支满足 $F_\ell(z)\in X\Rightarrow F_\ell(z)\in B$；再重建全部带类型单点、相邻闭片、全包含边及容许色。层可取准确可达集，也可取明确包含每个合法后继的有限上集；要求 $L_0$ 含每个 guard 零初始对，$L_{j+1}$ 含 $L_j$ 的每个上述允许后继，$L_6$ 为空，并检查 $\nu_L<\mu<U$。由重建完备性，不能只检查一个选取的子图。

具体选择候选

$$
\mu_n=\frac{\lfloor2^n\nu_L\rfloor+1}{2^n},\qquad n=0,1,\ldots.
$$

$\nu_L=\sqrt5-11/5$ 无理，故 $0<\mu_n-\nu_L<2^{-n}$。固定二次域的精确比较可求此整数下取整。若 $\mu_n\ge U$，略过，不查询图；否则作六层有限测试，空层就返回 $\widehat\nu=\mu_n$ 及证书。每个阶段有限。引理36.20与 $U>\nu_L$ 给正数
$\epsilon=\min\{\beta_3-\nu_L,U-\nu_L\}$；充分大的 $n$ 有 $\mu_n<\min\{\beta_3,U\}$，测试必接受。程序不使用 $\beta_3$ 的数值，也不需要成功指标的事先界。

在被接受的半径 $\delta=\lambda-\widehat\nu>C$。类型2用四色规则在偏移1进入类型1。类型4在四个颜色内于 $e=1$ 或2进入类型2，其四色窗口 $e,\ldots,e+3$ 不晚于位置5，于是偏移 $d=e+1\le3$ 进入类型1。类型3由六层缺席强制下一标签分歧，其下一共同色1使偏移1成为类型1。类型1已在偏移0；$\delta>g^4/5$ 与 $\delta>J$ 保持引理36.10的三窗回返和 $6k$ 色强制 $P_A^k,P_B^k$，最后传播不多取一个颜色。

现在对每个非空残余 $h$ 选首标签不同的伙伴，整条闭路径分别提升。若其共同长度为 $L$，全局前缀删去后还有 $L+1$ 个共同已取得颜色，全部来自这两条实际完整轨迹。$L\le8$ 用字面模板；$L\ge9$ 用六色进入得到 $d\le3$，令

$$
k=\left\lfloor\frac{L-d}{6}\right\rfloor\ge1.
$$

$6k$ 标签和所需 $6k$ 颜色均在该残余及已取得范围中，故
$h=uP^kv$，$|u|=d\le3$，$|v|=L-d-6k\le5$。对每个候选都可作这个选择，所以没有只压缩某个被选对。固定 $L$ 下每个单幂模板的唯一可能指数满足 $6k=L-|u|-|v|$，故模板数乘图顶点数已经给全部候选的一个固定界；引理36.16还独立给更直接的顶点宽度界。端点单点没有任何删去。

将该固定族代入定理36.17，不重复实现。闭图及局部推导与归属无关；更小实预算的实际记录都保留在此一固定有理半径图中，所以同一解码器适用于它们，无需实数预言机。作为推论，它也适用于闭端点 $\nu_L$；有限延迟端点 $\rho$ 与本节充分对数半径仍是不同边界。$\square$

### 36.5 SCC 的来源词相干性与一般对数上界

**定理 36.22（同步返回相干、周期和边相位）。** 设有限有向图的每条边输出有限字母表的一个符号，$S$ 是含环强连通分量，$s=|V(S)|$。以下三条件等价：在某个基点的任意两个非空返回词 $A,B$，长度分别为 $a,b$，满足

$$
A^{L/a}=B^{L/b},\qquad L=\operatorname{lcm}(a,b);
$$

存在 $1\le p\le s$、$P\in\Sigma^p$ 与相位映射 $\theta:V(S)\to\mathbb Z/p\mathbb Z$，使每条内部边 $e:v\to w$ 满足

$$
\ell(e)=P_{\theta(v)},\qquad \theta(w)=\theta(v)+1\pmod p;
$$

从每个固定进入顶点出发，全部有限内部路径输出均为同一个固定周期无限词的前缀。在这些条件下，每个顶点的返回均相干；图路径和观察颜色词仍可不同。

证明。从基点 $q$ 选最短非空返回 $C$。最短性排除重复的内部顶点，故 $|C|\le s$。令 $P$ 是 $C^\infty$ 的最短周期块，$p=|P|\le |C|$。任一非空返回词 $A$ 与 $C$ 同步相等，故 $A^\infty=C^\infty=P^\infty$，且 $p$ 整除 $|A|$。所用周期事实可将无限周期词延伸到双侧：保持它的整数移位形成 $\mathbb Z$ 的子群，其最小正生成元是 $p$，所以全部正周期都是 $p$ 的倍数。

对 $v$，任选 $q$ 到 $v$ 路径，令 $\theta(v)$ 为其长度模 $p$。若另选一条路径，给两条都接同一 $v$ 到 $q$ 返回路径；所得非空返回长度均被 $p$ 整除，空返回的长度0也如此，故原路径长度同余，相位良定义。内部边使路径长加一，给相位递增；将 $q$ 到 $v$ 路径、该边和 $w$ 到 $q$ 路径合成非空返回，其词是 $P$ 的幂，边字符的位置恰为 $\theta(v)$，得到字符方程。

有边相位时，任一内部路径逐步输出固定相位旋转的 $P^\infty$ 前缀；返回长度被 $p$ 整除，输出完整周期幂，所有同步返回相同。若只有第三条件，任意返回可任意重复，其无限重复必须等于基点的同一个无限词；所以两个返回的同步幂相同。三条件于是等价。$\square$

该定理跨分量的结果是固定有限的多幂模板。强连通缩合图是有限 DAG，一条路径只访问有限多个分量，且不返回旧分量。固定分量行程、连接边和各段进入相位；在含环分量内，输出是一个周期旋转的前缀，将长度除以周期长，整数商给幂、有限余数给固定字面后缀。无环部分和连接边也给有限字面词。取全部有限选择的并，得到

$$
a_0P_1^{k_1}a_1\cdots P_d^{k_d}a_d,
$$

幂因子数至多该缩合路径访问的含环分量数，所有块固定。允许多个含环 SCC，不要求一条路径至多一个环。例如两个相干自环以字面边 $c$ 连接，输出 $a^icb^j$；固定长度下仍有增长的词数，不能全改写成固定有限的单幂族。多幂形式是必要允许的描述类型；它本身也不限制一个历史保留多少候选。

**定理 36.23（完整闭分歧图相干给对数完整上界）。** 对 $b_0\in\mathbb Q(t)\cap[0,\lambda)$，使用完整 $G_{b_0}$，其带类型节点包括全部 $\Omega$ 单点。配对顶点有共同容许色；配对边由两条实际来源边组成，以有序来源标签对 $(\ell,m)\in\Lambda^2$ 为输出符号。从全部 guard 零初始对沿相同来源标签前进，跨过第一条不同标签边后，保留每个可达配对延续，得到完整闭分歧图 $\mathcal D_{b_0}$。如果每个含环 SCC 的有序来源对返回相干，则定理36.17给闭预算 $b_0$ 及每个较小实际预算的 $O(\log(N+2))$ 完整峰值上界。

证明。配对路径逐位置可选一个共同色，但边的内容字母是来源标签对，不能把不同颜色词或路径重数当作来源分歧。取任一非空残余 $h$，有首标签不同的伙伴。两个候选在已写出的全局前缀上标签相同，从其首个残余标签的不同边开始，后续配对路径就在 $\mathcal D_{b_0}$ 内；终端在 $n$ 色、$n-1$ 边约定下已经有共同容许色。没有把终端坐标观察两次。

定理36.22及缩合 DAG 分解给有序来源对路径的固定有限多幂族。投影第一分量，再加入首次不同边的一个有限字面标签，覆盖每个残余；第二分量同样可投影。独立的引理36.16给所有闭候选的固定宽度。两者满足定理36.17的全部条件，其指数元组规范化即给完整存储上界，安全和 $D$ 生效亦由同一解码器证明。

有限图、词数的多项式增长或 $D/D$ 返回相干都不独自供应这个结论。这里相干性针对完整 $\Omega$ 闭分歧图，宽度另外证明；没有丢弃无有限尾的单点，也没有假定候选集合能由其宇宙词数压缩。所有较小预算记录包含于固定 $b_0$ 闭关系，直接使用这个图即可。$\square$

### 36.6 闭来源分支向实际严格误差线性见证的转移

**引理 36.24（固定终尾近似与内部目标的统一余量）。** 设 $0\le b_0<\nu<\lambda$，$\Delta=\nu-b_0$。一个合法长度 $M$ 前缀接实际 $\Omega$ 终尾 $\xi\in A_s$，其标量为 $x$；选固定合法 $\widehat\xi\in D_s$，标量 $\widehat x$ 满足 $|\widehat x-x|<\Delta/4$。若原来前缀各坐标满足规定闭格 $E_{i_j}^{b_0}$，则替换尾后的同一个实际有限来源可取得全部规定色，统一误差严格小于

$$
r_*:=b_0+\Delta/2=\frac{b_0+\nu}{2}<\nu.
$$

该近似不依赖前缀的长度或内容，目标均在相应格内部，归属无关；替换轨迹不必留在旧图的片中。

证明。合法空尾截断在每个 guard 的标量区间稠密，所以可选择上述一个尾，保留终端 guard。前缀的合法接缝不变，精确来源等式给

$$
\widehat x_j-x_j=(-g)^{M-j}(\widehat x-x),\qquad
|\widehat x_j-x_j|<\Delta/4.
$$

到闭格的距离是1-Lipschitz，故
$\operatorname{dist}(\widehat x_j,J_{i_j})<b_0+\Delta/4$。设 $D_X=\phi^2$，$\alpha=\Delta/(4D_X)\in(0,1)$，$m_i$ 为格中点，定义

$$
T_i(y)=(1-\alpha)\operatorname{proj}_{J_i}(y)+\alpha m_i.
$$

所有格正长度，故 $T_i(y)$ 是内部点，且

$$
|T_i(\widehat x_j)-\widehat x_j|
\le \operatorname{dist}(\widehat x_j,J_i)+\alpha D_X
<b_0+\Delta/2.
$$

目标在 $X$ 内，裁剪固定它；取误差为该目标与实际新坐标之差。没有长度累积误差，因为所有扰动都由一个终尾差乘收缩幂产生。终尾可以来自 $\Omega$ 单点，其有限近似可以离开单点和旧闭片；新来源的合法 guard 和实际目标已经足够，无需在旧图里强行重新实现。$\square$

**定理 36.25（不相干闭返回的实际线性下界）。** 若完整 $\mathcal D_{b_0}$ 在 $b_0\in\mathbb Q(t)\cap[0,\lambda)$ 有不相干含环 SCC，则对每个较大实预算 $b_0<\nu<\lambda$，每个符合定义36.9的解码器都有实际 $D$ 记录见证

$$
B^{\mathrm{worst}}_{\nu,\mathcal A}(N)
\ge \left\lfloor\frac{N-a}{L}\right\rfloor-O(1)
\qquad(N\ge a),
$$

其中 $a,L$ 是固定正整数。所有二进制见证的完整误差具有同一个 $r_*<\nu$ 上界并后接零误差，所以该线性下界同时适用于闭、正开和逐记录严格余量合同。与定理33.13合并，得到这些较大预算的最优 $\Theta(N+1)$ 阶数。

证明。不相干给同一配对顶点 $q$ 的两个非空返回，同步到长度 $L$ 后，其有序来源对词不同。至少一分量不同，必要时交换两个分量使第一来源词 $U_0\ne U_1$；第二词记 $V_0,V_1$。每个环的出发顶点选一个共同容许色，得到 $W_0,W_1$，均长 $L$。固定一个从初始对到 $q$、包含首次分歧的 stem，来源词为 $P,Q$，颜色词 $h$，长 $a$。记首次不同来源标签的位置为 $k<a$，前 $k$ 个标签为同一固定词。

在 $q$ 的两终端片中固定实际 $\Omega$ 尾 $\xi,\eta$；包括只有非有限尾的单点，guard 满像仍供应它们。对每个二进制词 $z=z_1\cdots z_n$，从这两条固定尾整条提升得

$$
PU_{z_1}\cdots U_{z_n}\xi,\qquad
QV_{z_1}\cdots V_{z_n}\eta,
$$

它们在闭预算 $b_0$ 下满足共同色词
$h_z=hW_{z_1}\cdots W_{z_n}$。这里只是共同闭关系。

对目标预算 $\nu$，分别固定一次 $\widehat\xi,\widehat\eta\in D$，各终尾标量误差小于 $\Delta/4$，不随 $n,z$ 变化。引理36.24使

$$
\widehat\alpha_z=PU_{z_1}\cdots U_{z_n}\widehat\xi,\qquad
\widehat\beta_z=QV_{z_1}\cdots V_{z_n}\widehat\eta
$$

成为实际有限来源，共同取得 $h_z$，全部前缀误差严格小于 $r_*=(b_0+\nu)/2$。经过 $M_n=a+nL$ 个出发颜色及来源边，终端坐标未观察，分别接零误差未来，得实际完整记录

$$
h_zS_{\widehat\xi}\quad\text{和}\quad h_zS_{\widehat\eta}.
$$

第一分量的未来对全部 $n,z$ 完全相同，来自同一个字面实际终尾；没有拼接独立可行未来。若采用已观察终端约定，可额外取得 $q$ 的一个共同容许色；同一余量使其实际可取得，此后未来须改为 $S_{T\widehat\xi}$。这只改变常数一，不能重复终端取得。

完整 $D$ 记录唯一性迫使 $W_0\ne W_1$。否则 $n=1$ 的两条第一分量来源，stem相同、来源返回词不同，却在同一零误差未来下有相同完整实际颜色记录；它们都是闭 $\nu<\lambda$ 记录，违反定理28.1。同步长度相同，所以固定 $n$ 的 $z\mapsto h_z$ 单射，$z\mapsto\widehat\alpha_z$ 也单射。

安全性应用于每个 $h_z$ 的两条实际延续，迫使旧输出只是共同 stem 前 $k$ 标签的某个前缀。因此旧输出有至多 $k+1$ 种；不能对任意分歧 stem假定此前完全静默。记处理完 $h_z$ 的完整配置为 $c_z$，旧输出为 $o_z$。若不同 $z,z'$ 的 $(c_z,o_z)$ 相同，接同一个实际未来 $S_{\widehat\xi}$ 给相同未来输出，加上相同旧输出得到相同补齐来源，与 $\widehat\alpha_z\ne\widehat\alpha_{z'}$ 及逐位置生效矛盾。故有 $2^n$ 个不同联合对，至少

$$
\#\{c_z\}\ge \frac{2^n}{k+1}
$$

个配置。把旧输出作为有限种可能值只用于这一联合计数，它仍为不可回读输出，不是免费可读存储。计入控制、计数、时序和所有输出侧可读信息后，二进制容量给 $B^{\mathrm{worst}}_{\nu,\mathcal A}(M_n)\ge n-O(1)$。取 $n=\lfloor(N-a)/L\rfloor$，最坏峰值随有限视界不减，即得所述界。

两分量实际前缀误差均统一小于 $r_*<\nu$，终尾零误差，所以两种严格合同亦接受全部共同历史、对手延续和共同未来。见证可随 $N$ 改变，不要求一个固定有限来源的内存永远增长。正余量 $\Delta$ 是本定理条件，不能在 $\nu=b_0$ 擅自取零。$\square$

### 36.7 完整记忆的单一转变半径

**定义 36.26（完整闭来源分歧的转变半径）。** 对每个 $b_0\in\mathbb Q(t)\cap[0,\lambda)$，选择一个符合第31章完整性与共同尾提升的有限闭表示，并取定理36.23的完整分歧图。定义

$$
\mathcal B=\{b_0\in\mathbb Q(t)\cap[0,\lambda):
\mathcal D_{b_0}\text{ 有不相干的可达含环 SCC}\},\qquad
R=\inf\mathcal B.
$$

不相干按有序来源对字母的同步词判定；不同路径或观察词本身不算内容分歧。以下证明非空性，并证明 $R$ 不依赖有效完整表示的选择及切点归属。这里不假定不同半径的端点集、图或 SCC 相互嵌套。

**定理 36.27（准确常数区间与单一亚临界记忆转变）。** 定义36.26的集合非空，且

$$
\rho<g-\frac15<\widehat\nu\le R\le\nu_0<\lambda.
$$

在定义36.9的闭预算合同下，最优最坏完整峰值的阶数为

$$
\begin{array}{c|c}
0\le\nu<\rho&O(1)\\
\rho\le\nu<R&\Theta(\log(N+2))\\
R<\nu\le\lambda&\Theta(N+1).
\end{array}
$$

这些结论适用于每个固定实预算和每种固定归属。$R$ 是本章的半径；在 $\nu=R$ 的准确记忆阶数未由本定理确定。

证明。先用已发布的指定 $\nu_0\in\mathbb Q(t)$ 及百窗线性下界。如果 $\mathcal D_{\nu_0}$ 每个含环 SCC 相干，定理36.23会给同一预算的一个对数完整解码器，违背推论33.12的普遍线性下界。故 $\nu_0\in\mathcal B$，集合非空，$R\le\nu_0<\lambda$。这一步引用第33章的已证高预算区间，不把全局 $R$ 定理归给第33章。

若 $b_0\in\mathcal B$ 且 $b_0<\widehat\nu$，取 $b_0<\nu\le\widehat\nu$。定理36.25在该预算给普遍线性下界，定理36.21却供应对数解码器，矛盾。所以 $\mathcal B\cap[0,\widehat\nu)=\varnothing$，$R\ge\widehat\nu$。由引理36.18及选择不等式得到整个严格下段括界。

对任意实数 $0\le\nu<R$，选 $\nu<b_0<R$，$b_0\in\mathbb Q(t)$，可取有理数。定义下确界使 $b_0\notin\mathcal B$，完整图的含环 SCC 全相干；定理36.23给实际 $\nu$ 的对数上界。没有在一般实参数上查询有限图。

对任意 $R<\nu<\lambda$，下确界性质给某个 $b_0\in\mathcal B$ 且 $b_0<\nu$。定理36.25的固定终尾近似和内部目标给实际线性下界；定理33.13的临界解码器给相应线性上界。对 $\nu=\lambda$，先在 $(R,\lambda)$ 的一个中间预算取得实际线性见证，再由记录类包含沿用至 $\lambda$；同一个临界上界仍成立。

最后，定理36.11给 $\nu<\rho$ 的常数解码器，定理36.15给 $\nu\ge\rho$ 的严格实际对数下界。合并得到三行阶数：对数行与线性行的上界均由一个构造达到，下界均针对每个合法解码器。

若换用另一族有效完整表示而得到 $R'$，同样论证仍给 $R'$ 两侧的对数上界与线性下界。若 $R<R'$，任取其间预算，一个表示给线性下界，另一个给对数上界，矛盾；反向同理。因此 $R$ 与表示无关。闭格 $J_i$ 及闭图不取决于归属；上界保留每种实际归属的来源，下界使用内部目标，对每种归属均成立，故同一个 $R$ 与归属无关。

还可得到语义上的上闭性：

$$
b_0\in\mathcal B,\quad b_0<c_0<\lambda,\quad c_0\in\mathbb Q(t)
\quad\Longrightarrow\quad c_0\in\mathcal B.
$$

因为定理36.25在 $c_0$ 给线性下界，相干的 $c_0$ 图会由定理36.23给相反上界。此论证只比较实际恢复合同，不比较两个图的端点或 SCC 身份。

端点 $R$ 保留未决：下界转移要求严格正噪声余量，上界选图要求严格更大的相干域内半径；仅从 $R=\inf\mathcal B$ 不能在等号处供应任何一项。也不由此证明下确界取得、$R\in\mathbb Q(t)$ 或其代数性质。$\square$

**推论 36.28（两种严格合同在 $R$ 之外的同一阶数）。** 对正开合同及逐记录严格余量合同，正预算上的同一个半径 $R$ 给

$$
\begin{array}{c|c}
0<\nu<\rho&O(1)\\
\rho\le\nu<R&\Theta(\log(N+2))\\
R<\nu\le\lambda&\Theta(N+1).
\end{array}
$$

每种合同在 $R$ 处的阶数仍未决，不假定与闭合同端点结果相同。

证明。闭预算上界在较小严格记录类上仍安全并逐位置生效。定理36.15在 $\rho$ 独立构造的精确严格族已经逐记录有 $\varepsilon_r>0$，给两种严格合同的对数下界；同一族用于全部 $\nu\ge\rho$，没有声称全族在某个共同小于 $\rho$ 的半径上合法。

若 $R<\nu<\lambda$，取 $b_0\in\mathcal B$、$b_0<\nu$，定理36.25给全部二进制见证的共同界 $r_*=(b_0+\nu)/2<\nu$，后接零误差，故强于两种严格要求。$\nu=\lambda$ 用一个中间预算的同一严格族。零处逐坐标严格不等式无记录，不列为正开预算。端点未决理由与正余量和相干上包络有关，不能从合同包含关系裁定等号阶数。$\square$

### 36.8 有限返回证书与转变半径的有效有理逼近

本节使用已经成立的定理36.22—36.27。前述记忆阶数与 $R$ 的存在证明不依赖本节的有效逼近。

**引理 36.29（长度至多 $2s-1$ 的完整返回测试）。** 在有限单符号边图的一个 $s$ 顶点含环 SCC 中，固定基点 $q$，选最短非空返回 $C$，以及每个顶点 $v$ 的简单路径

$$
A_v:q\to v,\qquad B_v:v\to q,\qquad
|A_v|,|B_v|\le s-1,\qquad A_q=B_q=\varnothing.
$$

只测试每个非空 $A_vB_v$ 和每条内部边 $e:v\to w$ 的返回 $A_veB_w$，分别与 $C$ 同步比较来源词。每个被测返回长至多 $2s-1$，$|C|\le s$。全部比较相等当且仅当 SCC 的所有返回相干；失败给显式不同同步返回，成功给 本原周期及全部边相位证书。

证明。相干当然使每个比较相等。反向，令 $P$ 是 $C$ 的本原根，$p=|P|\le |C|$。一个非空测试返回 $U$ 的成功比较

$$
U^{L/|U|}=C^{L/|C|},\qquad L=\operatorname{lcm}(|U|,|C|)
$$

使 $U^\infty=P^\infty$；定理36.22中已证明的最小周期事实给 $p\mid |U|$，且 $U$ 是 $P$ 的整幂。定义 $\theta(v)=|A_v|\bmod p$。顶点返回给

$$
|A_w|+|B_w|\equiv0\pmod p,
$$

省略的空返回在 $q$ 也满足此式；边返回给
$|A_v|+1+|B_w|\equiv0\pmod p$。相减得 $\theta(w)=\theta(v)+1$。边 $e$ 在测试词 $A_veB_w$ 的位置 $|A_v|$，该词为 $P$ 的幂，故 $\ell(e)=P_{\theta(v)}$。所有内部边满足定理36.22的相位条件，全部返回相干。

顶点返回至多 $2s-2$，边返回至多 $2s-1$，最短基准返回至多 $s$。因此不相干必在这份有限表中失败，失败的 $C,U$ 正是所需同基点不同同步词。判断使用实际输出字母，不把两个不同边或不同图路径错误计为不同来源内容。$\square$

**定理 36.30（固定二次域的完整图决定与有限证书）。** 对每个有限给定的 $b_0\in\mathbb Q(t)\cap[0,\lambda)$，存在终止的精确构造和判断，决定 $b_0\in\mathcal B$。它涵盖完整可达闭分歧图，每种结果都有有限证书；不允许以被选子图证明没有不相干返回。

证明。一个域元素唯一表示为 $a+ct$，$a,c\in\mathbb Q$；使用 $t^2=1-t$ 作有限域运算，等号比较两个系数。非零符号可用正根的有理隔离区间有限细化判定，或化为 $r+s\sqrt5$ 后以符号和平方比较判定。这里的有效性只在固定有序域 $\mathbb Q(t)$ 中。

对六个 $E_i^{b_0}$，取全部观察端点、guard 区间端点及合法分支域端点的有限集合 $\mathscr C$。选共同分母 $q\ge1$ 和整数 $H$ 满足

$$
H\ge\max_{c\in\mathscr C}|c'|,\qquad
H\ge\frac{gA_\Delta}{1-g},\qquad
A_\Delta=\max_{\ell\in\Lambda}|\Delta_\ell'|.
$$

通过整数递增及有限精确比较可取得这样的 $H$。引理31.2给

$$
B_{b_0}=\{x\in q^{-1}\mathbb Z[t]\cap X:|x'|\le H\},
$$

包含所需全部端点，且 $F_\ell(B_{b_0})\cap X\subseteq B_{b_0}$。对 $x=(m+nt)/q$，同时嵌入界给

$$
|n|\le\frac{q(\phi+H)}{\sqrt5},\qquad
|m|\le q\phi+t|n|.
$$

于是有可有限给出的整数搜索矩形，精确成员比较列出 $B_{b_0}$。使用 $g^{-1}=3+2t$、$g'=-g^{-1}$、$F_\ell(x)'=gx'-g\Delta_\ell'$，其格保持和逆闭合正是引理31.2的条件，未扩展到其他代数域。

排序端点，构造每个 guard 内的全部单点及相邻闭区间，逐一构造所有满足全包含规则的来源边及整个片的容许颜色。采用固定确定的分母、整数界和排序选择，得到一个有效完整表示族。定理31.4证明该族的规范路径完备及任意实际终尾的整条提升；有限域成员资格不替代实际来源存在性。定理36.27使采用这一表示族不改变 $R$。

有限配对操作先保留共同容许色，遍历全部 guard 零初始对的同标签可达部分，再取首次不同标签边及其全部可达延续，得到完整 $\mathcal D_{b_0}$。有限可达性和 SCC 分解终止。无内部环的单点 SCC 不需返回测试；每个含环 SCC 用引理36.29，基准、简单路径、有限返回表及同步词比较均有限。成功返回 $P,\theta$，失败返回同基点两个显式不同同步来源对词。由定理36.22，所有含环 SCC 成功恰为 $b_0\notin\mathcal B$；任何一个失败即为 $b_0\in\mathcal B$。

相干证书需覆盖全部可达 SCC，提供每个含环分量的周期与相位，并逐边满足相位方程。不相干证书提供达到该分量的分歧 stem 和失败的两个返回；同步有序对词不同必在至少一个来源分量不同，可供应定理36.25。图完整性可由有限端点清单中的必需端点和逆闭合条件检查，再重建全部带类型片、全包含边和颜色、可达分歧图及 SCC。单点不能删去，不能附加归属或 $D$-live 筛选。只提供某些相干环不构成完整相干证书。

每个环的返回测试也可由穷尽 $1\le p\le s$ 的有限相位候选判定，但有限返回表已经同时供应正、负证书，不需另一种半径判断。此定理说明有限可执行规格和终止性，不给运行成本或图大小的有效效率界。$\square$

**定理 36.31（有理包络与等号安全的二分）。** 存在终止程序，对每个 $n\in\mathbb N$ 返回有理数 $l_n,u_n,r_n$ 及有限端点证书，使

$$
l_n\le R\le u_n,\qquad u_n-l_n=2^{-n},\qquad
r_n=\frac{l_n+u_n}{2},\qquad
|r_n-R|\le2^{-n-1}.
$$

因此 $R$ 是可计算实数。程序不使用 $b_0=R$ 的等号预言机，不报告本章已执行某次半径近似，也不裁定 $R$ 处的记忆阶数。

证明。定理36.27的语义上闭性给两项弱含义：

$$
b_0\in\mathcal B\Longrightarrow R\le b_0,\qquad
b_0\notin\mathcal B\Longrightarrow b_0\le R
\qquad(0\le b_0<\lambda).
$$

第一项由下确界直接得到。若第二项失效，即 $R<b_0$，取 $a_0\in\mathcal B$ 且 $a_0<b_0$，语义上闭性迫使 $b_0\in\mathcal B$，矛盾。故“相干”只供 $b_0\le R$，不能解读成严格低于 $R$；“不相干”只供 $R\le b_0$。也可由上闭性及有理稠密性得 $R=\inf(\mathcal B\cap\mathbb Q)$：对任意 $\epsilon>0$，先取 $\mathcal B$ 元素小于 $\min\{R+\epsilon,\lambda\}$，再向上取仍低于该界的有理数，上闭性使它也属于 $\mathcal B$。

初始化有理区间 $[l,u]=[0,1]$，已知 $0<R<\lambda<1$。执行恰好 $n$ 次：令 $b_0=(l+u)/2$。若 $b_0\ge\lambda$，只把 $u$ 更新为 $b_0$，不查询图；$R<\lambda\le b_0$ 使更新正确。若 $b_0<\lambda$，用定理36.30的完整有限判断；有不相干 SCC 则置 $u=b_0$，全部相干则置 $l=b_0$。全部图查询只在有理子域的 $[0,\lambda)$ 内，比较 $\lambda$ 在固定二次域中精确终止。

每步保持 $l\le R\le u$，且有理宽度减半，故恰好 $n$ 步后的宽度为 $2^{-n}$，中点误差至多一半。若某个中点恰为 $R$，不相干结果把 $R$ 作为上端，相干结果把 $R$ 作为下端，两者均保持包络；不需先识别等号。每个查询终止，请求迭代数有限，所以整个精度请求程序终止。

最终证书可只保留最后两端各自的完整相干或不相干证书；未改变的粗端点及无需图查询的上端用 $0<R<\lambda<1$ 和相应精确比较证明。此前二分查询不是最终包络所需的材料。有限证书证明 $l_n\le R\le u_n$，有理算术证明宽度和中点误差。选择 $\widehat\nu$ 与逼近 $R$ 的规格均无需一个已知的 $\beta_3$ 值，也无需跨预算图包含。$\square$

本章结果限于固定六格仪器、实际共同来源、完整记忆计价和指定的输出合同。有效性意味着每个有限给定的 $\mathbb Q(t)$ 图问题及每个有理精度请求终止；这里没有给出已生成的图、成功半径数值或实际二分读数。它不证明任意代数扩域有同样有限表示，不给实际运行时间、实时采集效率或总取得成本的界。$R$ 的精确符号值、算术性质、下确界是否取得以及闭、正开、逐记录严格余量三种合同在准确预算 $R$ 的记忆阶数均保留未决。所有上、下界属于纸面数学与算法规格，不承担形式内核已验证的声明。

## 追加锚（36·本行以下为增补区）

## 37. 折叠剥离中的守卫预测、有限记录与条件信息

### 37.1 原始操作合同与记号

本章固定

$$
G=\widehat{\mathbb Z}^{\,2},\qquad K=\Omega\times G,\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
\alpha=\binom10,\quad q=(2,3),
$$

其中 $\Omega$ 是无相邻一的单边地址空间。定义总的零插入、带守卫的一插入和总剥离

$$
h_0(\omega,z)=(0\omega,Mz),\qquad
h_1(\omega,z)=(1\omega,\alpha+Mz)\quad(\omega_0=0),
$$

$$
\delta(\omega,z)=\bigl(\sigma\omega,M^{-1}(z-\omega_0\alpha)\bigr).
$$

在首位为一时执行 $h_1$ 进入单独的吸收失败结果；失败不是可逆操作，也不产生额外读数。每条脚本从同一点、同一初始记录独立开始。实际有限来源图记为 $\Gamma$，而本章的独立坐标载体始终是 $K$。只使用原有标量余数读数，不加入已删除位输出、$\operatorname{End}$ 测试、$K$ 上的精确整数读出、自由时钟或圆柱测试逆命令。

对 $p=(\omega,z_0)$ 写

$$
\delta^jp=(\sigma^j\omega,z_j),\qquad U_j=\omega_j,\qquad c_j=qz_j,
$$

并定义

$$
L_n=\ker\delta^n,\qquad
T_{m,r}(p)=(c_0,\ldots,c_r)\bmod m,
$$

$$
Q^{\rm save}_{m,n}(p)=\bigl(\delta^np,(c_j\bmod m)_{0\le j<n}\bigr).
$$

$L_n$ 只表示没有保留记录时的剥离损失；$T_{m,r}$ 有 $r+1$ 次读数；$Q^{\rm save}_{m,n}$ 有 $n$ 次剥离前保存的读数和一个精确终端点。观察的核是观察值相等的等价关系，关系的细化不等于从已丢弃的商中重建信息。

对合法有限词 $u=u_0\cdots u_{s-1}$ 写 $t_u=\sum_{i<s}u_iM^i\alpha$，令 $\Omega_0=\{\eta\in\Omega:\eta_0=0\}$，并明确规定

$$
F_u=\begin{cases}
\Omega,&u=\varepsilon\text{ 或 }u_{s-1}=0,\\
\Omega_0,&u_{s-1}=1.
\end{cases}
$$

$[u]$ 是地址以 $u$ 开头的圆柱。复用定义 5.1 与命题 5.2，原有前缀映射 $h_u=P_u$ 及其数学分支逆为

$$
P_u(\eta,r)=(u\eta,t_u+M^{|u|}r),\qquad D_u=\delta^{|u|}|_{[u]\times G}.
$$

函数复合从右向左作用，$h_u=h_{u_0}\circ\cdots\circ h_{u_{s-1}}$，实际动作依次插入 $u_{s-1},\ldots,u_0$；$u=\varepsilon$ 时是恒等。于是 $\delta^s h_u=D_uP_u=\mathrm{id}$ 于 $F_u\times G$，而 $h_u\delta^s=P_uD_u=\mathrm{id}$ 只在圆柱 $[u]\times G$ 上成立。这里的 $D_u$ 只是描述已有总剥离在圆柱上的分支，不是新授权的圆柱测试逆；固定原语脚本在有限输入圆柱上是有限个 $P_vD_u$ 分支的并，失败分支进入吸收态。

### 37.2 共同递推与有限标量迹核

由同一条轨迹上的恒等式

$$
z_j=U_j\alpha+Mz_{j+1}
$$

以及 $qM^{-1}=(1,2)$ 得

$$
c_1=qM^{-1}z_0-U_0,\qquad
c_j-c_{j+1}-c_{j+2}=2U_j+U_{j+1}.
\tag{37.1}
$$

合法相邻对 $00,01,10$ 对应的右端分别为 $0,1,2$。矩阵

$$
\begin{pmatrix}q\\qM^{-1}\end{pmatrix}
=\begin{pmatrix}2&3\\1&2\end{pmatrix}
$$

行列式为一。令 $p'=(\omega',z'_0)$、$\Delta_j=U'_j-U_j$、$v=(-3,2)^{\mathsf T}$。

**定理 37.1（有限标量迹核）。** 当 $r\ge1$ 时，

$$
T_{m,r}(p)=T_{m,r}(p')
\Longleftrightarrow
\begin{cases}
 z'_0-z_0\equiv \Delta_0v\pmod m,\\
 2\Delta_j+\Delta_{j+1}\equiv0\pmod m\quad(0\le j\le r-2).
\end{cases}
\tag{37.2}
$$

当 $r=0$ 时核只有 $qz_0\equiv qz'_0\pmod m$；当 $m=1$ 时迹恒定。

**证明。** $c_0=c'_0$ 与 $c_1=c'_1$ 给出

$$
q(z'_0-z_0)\equiv0\pmod m,\qquad qM^{-1}(z'_0-z_0)\equiv\Delta_0\pmod m.
$$

用上述行列式为一的矩阵求逆，得到第一行。式 (37.1) 对两条轨迹相减，得到第二行的必要性。反过来，前两个读数相同且每个相邻位对的递推右端相同，逐次递推即得到 $c_j=c'_j$，故条件充分。$r=0$ 和 $m=1$ 直接由定义得到。证毕。

由此得到全部短情形。$r=0$ 时只有一个标量读数，不确定地址；$r=1$ 时没有递推残差，给定 $(c_0,c_1)$ 和候选首位 $b$，初始余数为

$$
z_0\equiv\begin{pmatrix}2&-3\\-1&2\end{pmatrix}
\binom{c_0}{c_1+b}\pmod m.
$$

若 $m\ge3,r\ge2$，$0,1,2$ 在模 $m$ 下互异，故残差依次恢复全部 $U_0,\ldots,U_{r-1}$，再恢复 $z_0\bmod m$；精确等价数据是 $(\omega|_r,z_0\bmod m)$。若 $m=2,r\ge1$，残差只恢复 $U_1,\ldots,U_{r-1}$，不恢复 $U_r$。又因 $v\equiv\alpha\pmod2$，式 (37.2) 的第一行等价于 $z'_1\equiv z_1\pmod2$；精确等价数据是 $((\sigma\omega)|_{r-1},z_1\bmod2)$。当 $r=1$ 时该地址词为空，两个读数仍由行列式为 $-1$ 的行矩阵 $(qM,q)$ 确定 $z_1\equiv(c_0-c_1,c_1)^{\mathsf T}\pmod2$。首位变化须同时满足 $z'_0-z_0\equiv(U'_0-U_0)\alpha\pmod2$，这是算术补偿，不能在固定算术坐标下任意擦除首位。$m=1$ 时所有长度的迹均恒定。

### 37.3 守卫预测内核与操作次序

在 $X=K\sqcup\{\bot\}$ 上把非法 $h_1$ 总化为 $\bot$，全部动作固定 $\bot$。对任意关系 $E\subseteq X\times X$ 和动作族 $A$ 定义

$$
\mathcal I_A(E)=\bigcap_{v\in A^*}(T_v\times T_v)^{-1}E,
\qquad T_{a_1\cdots a_t}=a_t\circ\cdots\circ a_1,
\qquad T_\varepsilon=\mathrm{id}_X.
$$

这里 $a_1\cdots a_t$ 按实际执行顺序写，交包括空词。该关系是包含于 $E$ 的最大 $A$ 不变子关系；若 $E$ 是等价关系，它也是等价关系。置

$$
\mathcal I_+=\mathcal I_{\{h_0,h_1\}},\qquad
\mathcal I_-=\mathcal I_{\{\delta\}},\qquad
\mathcal I_{\rm mix}=\mathcal I_{\{h_0,h_1,\delta\}}.
$$

复合算子同样从右向左：$\mathcal I_-\mathcal I_+(E)=\mathcal I_-(\mathcal I_+(E))$ 先形成插入内关系，再作剥离细化，其实验先剥离后插入；$\mathcal I_+\mathcal I_-(E)$ 的实验先插入后剥离。每个中间输出都是一个脚本前缀的终点输出，故全词终点比较也包含全部中间读数及首次失败；并未保存隐藏的已删位。

令 $E_1$ 只区分正常结果和失败，$E_m$（$m\ge2$）再要求 $qz\bmod m$ 相同，令 $E_{\rm all}=\bigcap_{m\ge1}E_m$。定义

$$
S_m=\ker(U_0,z\bmod m),\quad
B_m=\ker(\omega,z\bmod m),
$$

$$
D_2=\ker\bigl(\sigma\omega,M^{-1}(z-\omega_0\alpha)\bmod2\bigr).
$$

上述 $S_m,B_m,D_2$ 都将 $\bot$ 单列；模一算术坐标平凡，所以 $S_1$ 只记首位、$B_1$ 记完整地址。表中纯插入、纯剥离和混合列分别为 $\mathcal I_+(E)$、$\mathcal I_-(E)$ 和 $\mathcal I_{\rm mix}(E)$。

**定理 37.2（完整预测分类）。** 在正常点上，各声明读数的预测内核如下；失败点始终是单独一类。

| 读数 | 纯插入 | 纯剥离 | 混合脚本 | $\mathcal I_-\mathcal I_+$ | $\mathcal I_+\mathcal I_-$ |
|---|---|---|---|---|---|
| 仅成功/失败 | $S_1$ | $E_1$ | $B_1$ | $B_1$ | $S_1$ |
| 模 $2$ | $S_2$ | $D_2$ | $B_2$ | $B_2$ | $B_2$ |
| 模 $m\ge3$ | $S_m$ | $B_m$ | $B_m$ | $B_m$ | $B_m$ |
| 全部有限模数 | $\ker(U_0,z)$ | $\Delta_K$ | $\Delta_K$ | $\Delta_K$ | $\Delta_K$ |

**证明。** 插入守卫直接读取首位。执行 $h_0$ 前后读取 $qz$ 与 $qMz$，其系数矩阵

$$
\begin{pmatrix}q\\qM\end{pmatrix}
=\begin{pmatrix}2&3\\3&5\end{pmatrix}
$$

行列式为一，故模 $m$ 恢复 $z$；其后的插入守卫只依赖已插入的词。于是纯插入核为 $S_m$。混合脚本先执行任意次剥离，再尝试 $h_1$，逐位测试地址守卫；配合同一算术矩阵恢复地址和算术余数，得到 $B_m$。

纯剥离时使用定理 37.1。模 $m\ge3$，递推右端的三个值互异，先恢复全部地址，再由前两次读数恢复 $z\bmod m$，故为 $B_m$。模二只恢复移位地址和 $z_1\bmod2$，故为 $D_2$；模一没有算术信息且总剥离永不失败，故为 $E_1$。这些关系显然在各自操作下保持。

对复合次序，$\mathcal I_-(S_m)=B_m$：空剥离词保留初始向量余数，$\delta^j$ 后的首位给 $U_j$，反向由 $B_m$ 产生所有这些数据。模二时若 $(p,p')\in\mathcal I_+(D_2)$，以 $h_0$ 作测试即得 $d_2(h_0p)=d_2(h_0p')$，其中 $d_2=(\sigma\omega,z_1\bmod2)$；$\delta h_0=\mathrm{id}$ 使这恰为 $B_2$。反向包含由 $B_2$ 的插入不变性得到。模 $m\ge3$ 时纯剥离已经是 $B_m$，插入保持它。全部模数下，纯插入仍只给 $\ker(U_0,z)$；纯剥离以模三恢复整个地址，再逐模恢复 $z$，故其核为 $\Delta_K$。混合列与两种复合也为 $\Delta_K$。模一时取 $p=(0^\infty,0)$ 与 $p'=(010^\infty,\iota(M\alpha))$：两点纯插入均有相同成功/失败行为，但脚本“先剥离再尝试 $h_1$”在两点上的结果相反，故 $B_1\subsetneq S_1$，两操作内核不作为一般算子交换。证毕。

模二的严格区别已有实际见证：$p_0=(0^\infty,0)$ 与 $(10^\infty,\iota(\alpha))$ 的初始数量为零与二，之后剥离轨迹相同，故纯剥离奇偶迹相同；$h_1$ 的守卫区分它们，$h_0$ 后的数量零与三也区分它们。

表中的“全部有限模数”指由有限实验组成的族，允许无限多个模数与任意长有限脚本。纯插入核是 $\ker(U_0,z)$，不同于纯剥离、混合和复合项的对角核；没有一个有限脚本读出任意完整无限状态。有限观察层面也有双向确定性：任意指定长度 $t$ 的地址前缀由 $T_{3,\max(2,t)}$ 恢复，再用首位和两次模 $m$ 读数恢复任意指定的 $z\bmod m$；反向，每条有限剥离脚本的读数由其有限初始前缀与一个有限向量余数确定。因此全部模数的纯剥离迹给出定理 2.3 的联合有限观察一致结构；此论证不只依靠限制到 $\Gamma$ 后的集合核相等。裸 $\Omega$ 上只有成功/失败地址结论；算术列需要 $K$ 或其实际来源图上的既定算术坐标。成功分支的有限同缝正规形只说明每条固定脚本在有限地址圆柱上是有限个前缀替换，不增加操作。

为避免接缝方向混淆，三位反向终端守卫的精确有序标签为

$$
(\mathrm{null},2,3,2\,5,5)=(000,100,010,101,001),\qquad 0=\mathrm{null}.
$$

尾首位为一时保留其中的 $(000,100,010)$；正向入接缝为一时允许词为 $(000,010,001)$，标签为 $(\mathrm{null},3,5)$。这些是同一守卫合同下的有序掩码，不能把反向终端表换成正向入接缝表。

### 37.4 精确终端记录、实际碰撞与损失方向

在 $Q^{\rm save}_{m,n}$ 中，精确终端点包含整个剩余地址和完整的 profinite 向量。此处是精确终端前提，不是有限终端观察。

**定理 37.3（精确终端核）。**

$$
\ker Q^{\rm save}_{m,n}=L_n\cap\ker T_{m,n},
$$

且

$$
\ker Q^{\rm save}_{m,n}=
\begin{cases}
L_n,&m=1, n\ge1,\\
L_1,&m=2, n\ge1,\\
\Delta_K,&m\ge3\text{ 或 }n=0.
\end{cases}
\tag{37.3}
$$

**证明。** 精确终端给出 $c_n$，第一式由定义成立。模 $m\ge3$ 时，已知 $z_{j+1}$ 与保存的 $c_j$，有

$$
c_j-qMz_{j+1}\equiv2U_j\pmod m.
$$

$0$ 与 $2$ 在模 $m$ 下不同，所以逐步唯一恢复 $U_j$ 和 $z_j$；不需除以二。模二由定理 37.1 恢复 $U_1,\ldots,U_{n-1}$ 及 $z_1\bmod2$。与精确终端的完整地址尾合起来，得到整个 $\sigma\omega$；再由命题 5.2 得精确向量 $z_1=t_{U_1\cdots U_{n-1}}+M^{n-1}z_n$，故 $\delta p$ 唯一。$n=1$ 时该词为空，$z_1=z_n$。反向，若 $\delta p=\delta p'$，所有后继状态相同，初始向量只差 $(U'_0-U_0)\alpha$，初始标量只差 $2(U'_0-U_0)$，所以全部保存奇偶读数与精确终端都相同，恰为 $L_1$。模一只剩未记录剥离核。$n=0$ 时观察本身是恒等。证毕。

定理 11.2（完整尾的全部前像与准确数量）与推论 11.3（三位逆分支与多窗历史）给出三次剥离后，在终尾首位为零时有 $F_5=5$ 个合法前缀、首位为一时有 $F_4=3$ 个；这是守卫约束下的纤维数，而不是五个独立盲位。定义 11.4（精确恢复的残余记录）与定理 11.5（最小恢复字母表与达到构造）给出相应的最小条件记录。

命题 11.9（头观察、尾保留与具体碰撞）给出实际碰撞

$$
\begin{aligned}
p_{10}&=(100\,100\,0^\infty,\iota(\alpha+M^3\alpha)),\\
p_{11}&=(010\,100\,0^\infty,\iota(M\alpha+M^3\alpha)),
\end{aligned}
$$

它们满足

$$
\delta^3p_{10}=\delta^3p_{11}=(10^\infty,\iota(\alpha)).
$$

两点的初始标量量分别为 $10,11$，模五初始余数为 $0,1$；共同终端量为 $2$，终端模五余数均为 $2$。保存初始读数可以区分它们；只给终端和未保存的剥离则不能。其它相等属性不会变成新的原语读数。

未记录剥离的核严格增长。取 $p_0=(0^\infty,0)$ 与

$$
e_n=(0^n10^\infty,\iota(M^n\alpha)).
$$

则 $(p_0,e_n)\in L_{n+1}\setminus L_n$。同一构造由联合实际来源实现，因此 $\Delta=L_0\subsetneq L_1\subsetneq\cdots$ 在 $K$ 和 $\Gamma$ 上都严格；在固定有限来源子集上则可按长度稳定。相反，保留更多标量迹使核细化。对 $m\ge3,r\ge2$，该细化在 $K$ 和 $\Gamma$ 上也严格：引理 2.2 联合实现前缀 $0^r1$ 与初始向量余数零，所得同一实际来源与 $p_0$ 在 $T_{m,r}$ 下相同、在 $T_{m,r+1}$ 下不同，直接用定理 37.1 的前缀等价式即可。两种方向比较的是不同的保留数据；支持有界的稳定性沿用命题 12.2，不改变这里的无界来源量词。

空词与 $h_0$ 再接 $\delta$ 给出同一状态映射和同一滞后；若把动作序列写入记录，这两个脚本的记录仍不同，差异来自显式保留的历史坐标。零点满足 $\delta p_0=p_0$，所以固定零点阻碍从状态本身定义全局状态时钟。保留历史坐标会改变观察合同。

### 37.5 有限终边界、CRT 规则与共同实现

现在只给有限终端数据。对已知 $m,\ell\ge1$、$n,k\ge0$，定义

$$
R=R^{\rm fin}_{m,\ell;n,k}(p)=
\left((\sigma^n\omega)|_k,\ z_n\bmod\ell,\ (c_j\bmod m)_{j<n}\right),
$$

$$
d=\gcd(m,\ell),\qquad L=\operatorname{lcm}(m,\ell),\qquad a=m/d=L/\ell,
$$

$$
J_L=(\omega|_{n+k},z_0\bmod L).
$$

$W_t$ 表示全部合法长度 $t$ 词，$W_0=\{\varepsilon\}$。$R=f(J_L)$，目标集合是 $\mathcal J=W_{n+k}\times(\mathbb Z/L\mathbb Z)^2$，令 $\mathcal F_\rho=f^{-1}\{\rho\}$；纤维只在有限集合上取，且只对达到的观察值 $\rho\in f(\mathcal J)$ 取最大值。$n=0$ 时仍以 $J_L=(\omega|_k,z_0\bmod L)$ 为目标；不能把目标模数改成 $\ell$。

设终端词为 $w$、终端向量余数为 $r\bmod\ell$、保存读数为 $b_j\bmod m$。令

$$
t_u=\sum_{i<|u|}u_iM^i\alpha.
$$

**定理 37.4（一个守卫 CRT 候选规则）。** $J_L$ 中的候选恰为所有合法词 $uw$（$|u|=n$）及 $y\bmod L$，满足

$$
y\equiv t_u+M^nr\pmod\ell,
$$

$$
qM^{-j}(y-t_{u|_j})\equiv b_j\pmod m\qquad(0\le j<n).
\tag{37.4}
$$

**证明。** 前缀公式给 $z_0=t_u+M^nz_n$，故第一式是必要且充分的终端约束；连续剥离前的标量读数是 $qM^{-j}(z_0-t_{u|_j})$，故第二式同样必要且充分。合法性包含 $u$ 与 $w$ 的两侧守卫，特别是 $k=0$ 时不存在右接缝位。两类约束合起来恰好给 $R=f(J_L)$ 的定义，证毕。

**引理 37.5（共同 CRT 相容性与逐词算术重数）。** 记 $\mathcal A_\rho$ 为式 (37.4) 存在算术解的合法擦除词集合。每个相容擦除词的算术提升数为

$$
g_n=\begin{cases}a^2,&n=0,\\a,&n=1,\\1,&n\ge2.
\end{cases}
\tag{37.5}
$$

当 $n=1$ 时，候选位 $b$ 相容当且仅当 $bw$ 合法且

$$
b_0-qMr\equiv2b\pmod d.
$$

记

$$
S=\begin{pmatrix}2&3\\1&2\end{pmatrix},\qquad
\upsilon=\binom{-3}{2}.
$$

当 $n\ge2$ 时，置

$$
x_m(u_0)=S^{-1}\binom{b_0}{b_1+u_0}
=\begin{pmatrix}2&-3\\-1&2\end{pmatrix}\binom{b_0}{b_1+u_0}\pmod m.
$$

候选 $u$ 相容当且仅当 $uw$ 合法，并同时满足

$$
b_j-b_{j+1}-b_{j+2}\equiv2u_j+u_{j+1}\pmod m
\quad(0\le j\le n-3),
$$

$$
x_m(u_0)\equiv t_u+M^nr\pmod d.
$$

相容时其唯一向量 $y\bmod L$ 由

$$
y\equiv x_m(u_0)\pmod m,\qquad
y\equiv t_u+M^nr\pmod\ell
$$

共同确定；$n=2$ 时递推残差条件为空。

**证明。** 对两个模数，广义 CRT 在每个坐标上给出：指定模 $m$ 与模 $\ell$ 余数可合并，当且仅当它们模 $d$ 相同；合并值在模 $L$ 下唯一。确切地，写 $m=da$、$\ell=d\ell'$，则 $\gcd(a,\ell')=1$。在一个模 $\ell$ 代表 $x_\ell$ 上加 $\ell e$ 后，要求模 $m$ 等于 $x_m$，归结为 $\ell'e\equiv(x_m-x_\ell)/d\pmod a$；右端有意义恰在相容时，且 $\ell'$ 可逆，故逐坐标唯一。这同一个相容判据作用于整个向量，没有独立拼接标量边缘。

$n=0$ 时仅有 $y\equiv r\pmod\ell$，$y=r+\ell e\pmod L$ 的两坐标 $e\bmod a$ 各有 $a$ 种，因此有 $a^2$ 个提升，地址词恰为 $w$，包括 $k=0$ 的空词。

$n=1$ 时终端给出 $x_\ell=b\alpha+Mr\pmod\ell$，保存行是 $qy\equiv b_0\pmod m$。取该向量的整数代表，写 $y=x_\ell+\ell e\pmod L$。标量方程可解必须且只需 $b_0-qx_\ell\equiv0\pmod d$，即声明的位相容式。相容时剩下

$$
(\ell/d)qe\equiv(b_0-qx_\ell)/d\pmod a.
$$

$\ell/d$ 是模 $a$ 的单位；$S$ 在每个模数下都是双射，所以 $e\mapsto qe$ 是满射，给定其第一行后第二行仍有且仅有 $a$ 种。因而每个相容位的向量解恰有 $a$ 个。这里 $a=1$ 也成立。

$n\ge2$ 时给定首位，前两读数给 $Sy=(b_0,b_1+u_0)^{\mathsf T}\pmod m$，$\det S=1$ 使 $y\bmod m$ 唯一。定理 37.1 的同一递推证明保证其余保存读数恰由上述残差条件检验。再与终端所给的模 $\ell$ 向量按广义 CRT 合并，存在时恰有一个模 $L$ 向量。后续读数只排除词，不增加向量重数。证毕。

**命题 37.6（全部相容地址词、短长度与尖锐恢复）。** 以下分类列出每个达到的观察 $\rho=(w,r,(b_j))$ 的完整 $\mathcal A_\rho$；每个词的向量候选由引理 37.5 给出。

$n=0$ 时 $\mathcal A_\rho=\{\varepsilon\}$，$R=(\omega|_k,z_0\bmod\ell)$ 是直接快照，目标仍为 $J_L$。

$n=1$ 时

$$
\mathcal A_\rho=\{b\in\{0,1\}:bw\text{ 合法},\ b_0-qMr\equiv2b\pmod d\}.
$$

$d\le2$ 时它是全部接缝合法位，$d\ge3$ 时它是一个由 $R$ 确定的位。

$n=2$ 时，令 $x_*=S^{-1}(b_0,b_1)^{\mathsf T}$，则

$$
\mathcal A_\rho=\{eb\in\{00,01,10\}:ebw\text{ 合法},\
(-4e,2e-b)^{\mathsf T}\equiv M^2r-x_*\pmod d\}.
$$

因此 $d=1$ 时是全部接缝合法的相邻对；$d=2$ 时第二位 $b$ 确定，$b=0$ 时可为 $00,10$，$b=1$ 时仅可为 $01$；$d\ge3$ 时两位都确定。

$n\ge3,m\ge3$ 时，保存的迹确定 $v=U_0\cdots U_{n-2}$ 及 $x_m=z_0\bmod m$，且

$$
\mathcal A_\rho=\{vb:b\in\{0,1\},\ vbw\text{ 合法},\
x_m\equiv t_v+bM^{n-1}\alpha+M^nr\pmod d\}.
$$

$d=1$ 时两种接缝合法末位全部出现；$d\ge2$ 时末位唯一。

$n\ge3,m=2$ 时，保存的迹确定非空中间词 $v=U_1\cdots U_{n-2}$ 及 $s_2=z_1\bmod2$，而相容词恰为

$$
\mathcal A_\rho=\{evb:e,b\in\{0,1\},\ evbw\text{ 合法},\
s_2\equiv t_v+bM^{n-2}\alpha+M^{n-1}r\pmod d\}.
$$

这里 $d=\gcd(2,\ell)$。$\ell$ 偶时末位 $b$ 唯一，首位 $e$ 仅受 $ev$ 守卫；$\ell$ 奇时末位仅受 $vbw$ 守卫，首位仅受 $ev$ 守卫，全部合法组合共同出现。$n=2$ 时中间词为空，须用上面的相邻对分类。

$n\ge3,m=1$ 时 $\mathcal A_\rho=\{u\in W_n:uw\text{ 合法}\}$，每个词的向量就是 $t_u+M^nr\bmod\ell$。

**证明。** $n=0$ 已由引理给出。$n=1$ 的两个候选残差是零与二；二者模 $d$ 相同恰当 $d=1,2$。达到的观察保证至少一个合法位相容，故 $d\le2$ 时全部合法位相容，$d\ge3$ 时仅一个。这里 $k=0$ 不提供右守卫，允许两种位；$k\ge1,w_0=1$ 时合法性本身强制零。

$n=2$ 时 $x_m(e)=x_*+e\upsilon$，而终端模 $\ell$ 向量为 $e\alpha+bM\alpha+M^2r$。相容式等价于

$$
e(\upsilon-\alpha)-bM\alpha=(-4e,2e-b)^{\mathsf T}\equiv M^2r-x_*\pmod d.
$$

三个合法对的签名为

$$
00\mapsto(0,0),\qquad01\mapsto(0,-1),\qquad10\mapsto(-4,2).
$$

前两个签名仅在 $d=1$ 重合；第一与第三仅在 $d=1,2$ 重合；第二与第三的差为 $(-4,3)$，其坐标互素，仅在 $d=1$ 重合。所以 $d\ge3$ 三者互异，$d=2$ 精确区分第二位，$d=1$ 无签名约束。这是完整的共同向量相容检验，并非分别取得两位后将它们独立组合；$11$ 始终非法。引理 37.5 给每个相容对一个向量。

$n\ge3,m\ge3$ 时，保存的 $n$ 个读数是 $T_{m,n-1}$，定理 37.1 确定 $v,x_m$。仅末位未进入这些读数的位更新，故没有其它标量条件。两种末位的终端相容向量差为 $M^{n-1}\alpha$。该向量在模 $d\ge2$ 下非零，因为 $M$ 可逆而 $\alpha=(1,0)^{\mathsf T}$ 非零；所以公因子 $d\ge2$ 的向量分辨率已经足够。特别在 $d=2$，可由已恢复的 $z_{n-1}\bmod2$ 和终端 $z_n\bmod2$ 用

$$
z_{n-1}-Mz_n\equiv U_{n-1}\alpha\pmod2
$$

恢复最后位；不能把标量零与二在模二下区分。$d=1$ 时广义 CRT 对每个合法末位可解，无其它删位候选。

$m=2,n\ge2$ 时，$b_0=qMz_1\pmod2$、$b_1=qz_1\pmod2$，矩阵行 $(qM,q)$ 的行列式为 $-1$，故确定 $s_2$。定理 37.1 又确定 $U_1,\ldots,U_{n-2}$；这些数据恰产生全部保存奇偶读数。前缀公式从 $z_1$ 到终端给出

$$
z_1\equiv t_v+bM^{n-2}\alpha+M^{n-1}r\pmod\ell.
$$

与 $s_2$ 合并的唯一条件正是声明的模 $d$ 向量式。偶数 $\ell$ 时两个末位的差 $M^{n-2}\alpha\pmod2$ 非零，所以末位唯一，并得 $z_1\bmod\ell$。奇数 $\ell$ 时 $d=1$，每个合法末位都有唯一 $z_1\bmod2\ell$；随后每个合法首位给 $z_0=e\alpha+Mz_1\bmod2\ell$。首位改变时同步改变初始向量，且 $q\alpha=2$，故不改变任何保存奇偶读数。这个构造证明全部允许的首末组合共同相容，并未把任意算术余数当成独立可选量。$m=1$ 时无标量约束，终端公式即给全部候选。证毕。

以上证明给出同一 $R$ 可测的地址摘要。记 $V=U_0\cdots U_{n+k-1}$；每行的全部合法补全恰好是其相容词集合，均带有引理 37.5 的共同重数。

| 情形 | $R$ 固定的地址数据 | 每个相容词的算术重数 |
|---|---|---|
| $n=0$ | $V$ | $a^2$ |
| $n=1,d\ge3$ | $V$ | $a$ |
| $n=1,d\le2$ | $w$ | $a$ |
| $n=2,d\ge3$ | $V$ | $1$ |
| $n=2,d=2$ | $(U_1,w)$ | $1$ |
| $n=2,d=1$ | $w$ | $1$ |
| $n\ge3,m=1$ | $w$ | $1$ |
| $n\ge3,m=2,\ell$ 偶 | $U_1\cdots U_{n+k-1}$ | $1$ |
| $n\ge3,m=2,\ell$ 奇 | $(U_1\cdots U_{n-2},w)$ | $1$ |
| $n\ge3,m\ge3,d\ge2$ | $V$ | $1$ |
| $n\ge3,m\ge3,d=1$ | $(U_0\cdots U_{n-2},w)$ | $1$ |

用 $\mathscr S(V)$ 表示相应行的摘要，精确地有 $\mathcal A_\rho=\{u:uw\text{ 合法},\ \mathscr S(uw)=\mathscr S(\rho)\}$。摘要决定相容地址词及其后验地址律，但不替代 $R$ 的完整 CRT 数据；每个词的实际算术支撑仍依赖整个观察。

对 $m\ge3$，恢复全部删除位的统一尖锐条件是 $n=1,2$ 时 $d\ge3$，$n\ge3$ 时 $d\ge2$。恢复整个 $J_L$ 的统一尖锐条件是

$$
\begin{array}{c|c}
n&\text{条件}\\ \hline
1&m\mid\ell,\\
2&d\ge3,\\
n\ge3&d\ge2.
\end{array}
\tag{37.6}
$$

充分性由上述候选分类及 $g_n$ 直接得到：$n=1,m\mid\ell$ 使 $d=m\ge3,a=1$；其余两行词唯一且算术重数一。一次读数即使 $d\ge3$ 恢复了位，一般也只得到 $(\omega|_{k+1},z_0\bmod\ell,qz_0\bmod m)$，其 $a$ 个向量提升不可省略。算术部分等价于 $qz_0\bmod L$ 与 $qM^{-1}z_0\bmod\ell$，不是未经条件限定的完整二维模 $L$ 向量。

必要性由以下成对碰撞给出，无须使用后面的熵表。与 $p_0$ 比较且取终端观察词 $0^k$：若 $d=1,n\ge1$，把擦除词 $0^n$ 换成 $0^{n-1}1$，选初始整数向量 $y'$ 满足 $y'\equiv0\pmod m$、$y'\equiv M^{n-1}\alpha\pmod\ell$。互素 CRT 保证存在；最后位尚未更新前全部保存模 $m$ 读数为零，终端模 $\ell$ 向量也为零。若 $d=2,n=1$ 或 $2$，取擦除首位一、其它位零，选 $y'\equiv\upsilon\pmod m$、$y'\equiv\alpha\pmod\ell$；$\upsilon-\alpha=(-4,2)^{\mathsf T}$ 被二整除，所以存在。其前两读数满足 $q\upsilon=0$、$qM^{-1}\upsilon=1$，与首位一补偿后都为零；终端也相同。这两类给出位恢复条件的必要性，任意有限 $k$ 均不能消除碰撞。

$n=1,m\nmid\ell$ 时另有纯算术碰撞：同一全零地址的初始向量取零和 $\ell\upsilon$。$q\upsilon=0$ 保证保存读数相同，$M^{-1}\ell\upsilon$ 模 $\ell$ 为零，终端相同；但 $\ell\upsilon\not\equiv0\pmod L$，否则 $a=L/\ell>1$ 必须同时整除 $-3$ 和 $2$，矛盾。因而即使位已恢复，整体目标仍不唯一。具体地，$m=6,\ell=3,n=1$ 可取向量 $(3,0)^{\mathsf T}$；$m=6,\ell=2,n=2$ 可取首位一、向量 $\upsilon$；$m=3,\ell=2,n\ge3$ 可取末位一、向量 $3M^{n-1}\alpha$。它们分别展示算术不足、短记录公因子二不足和互素末位不足。

无论 $\ell$ 取何值，只要 $m=2,n\ge1$，首位都不能统一恢复：对任一首位零的精确尾 $y$，$h_0(y),h_1(y)$ 后继相同，初始标量相差二，其后全部轨道相同；取 $y=p_0$ 两点同时在 $\Gamma$。若 $\ell$ 偶且 $n\ge1$，上述奇偶分类恰给一次剥离后的有限快照

$$
R\ \text{等价于}\ ((\sigma\omega)|_{n+k-1},z_1\bmod\ell).
$$

$n=1$ 时 $c_0\equiv qMz_1\pmod2$ 已由偶数终端余数决定；$n\ge2$ 时恢复中间词、最后位并反推 $z_1\bmod\ell$。反向该快照产生全部保存读数与终端数据，不需要 $U_0$。若 $\ell$ 奇且 $n=1$，准确数据为 $((\sigma\omega)|_k,z_1\bmod\ell,qMz_1\bmod2)$，多出一个标量奇偶方程；$n\ge2$ 时用上述 $z_1$ 的共同 CRT 候选，不把首末位或余数独立选择。$k=0$ 始终没有右接缝测试，$n=0$ 始终是单独的直接快照。

在相同模数 $m=\ell$ 时，$n\ge1,m\ge3$ 等价于 $(\omega|_{n+k},z_0\bmod m)$，$m=2$ 等价于 $((\sigma\omega)|_{n+k-1},z_1\bmod2)$，$m=1$ 只保留终端词。合法词计数、向量余数数目及 $\delta$ 的满射性给观察像的大小分别为

$$
m^2F_{n+k+2},\qquad4F_{n+k+1},\qquad F_{k+2}\qquad(n\ge1).
$$

$n=0$ 不套用一次剥离等价；此时同模快照的像为 $m^2F_{k+2}$，$k=0$ 的地址词为空。

由引理 2.2（显式远端向量补偿），在长度 $n+k$ 前缀和模 $L$ 向量余数的同一有限观察上，每个合法目标由同一个实际有限来源联合实现。因此

$$
J_L(\Gamma)=\mathcal J=J_L(K).
$$

沿该来源的命题 5.2 迭代公式同时产生完整 $R$。所以 $f$ 的有限像、候选目标及上述每个碰撞在 $\Gamma$ 上也有实际代表；与零目标比较时可保留实际零来源 $p_0$。显示的完成域坐标对本身不自动属于 $\Gamma$，实际代表按其有限前缀和模 $L$ 余数联合取得。该引理不规定共同的精确无限尾或全部未来记录，也不允许把分别实现的边缘拼成一个来源。

### 37.6 精确有限残余字母与最小附加记录

固定终端词 $w$，若 $k\ge1$ 令 $\tau=w_0$；若 $k=0$ 只在计数中令 $\tau=0$，这不是对未观察下一位取值。记

$$
N_n(0)=F_{n+2},\qquad N_n(1)=F_{n+1}.
$$

**定理 37.7（有限终端记录的精确残余字母）。** 由共同的地址摘要、式 (37.5) 和守卫计数，固定该终端词的最大纤维 $M_\tau$ 为

| 长度 | 条件 | $M_\tau$ |
|---|---|---|
| $n=0$ | 全部 | $a^2$ |
| $n=1$ | $d\le2$ | $a(2-\tau)$ |
| $n=1$ | $d\ge3$ | $a$ |
| $n=2$ | $d=1$ | $3-\tau$ |
| $n=2$ | $d=2$ | $2$ |
| $n=2$ | $d\ge3$ | $1$ |
| $n\ge3$ | $m=1$ | $N_n(\tau)$ |
| $n\ge3$ | $m=2,\ell$ 奇 | $2(2-\tau)$ |
| $n\ge3$ | $m=2,\ell$ 偶 | $2$ |
| $n\ge3$ | $m\ge3,d=1$ | $2-\tau$ |
| $n\ge3$ | $m\ge3,d\ge2$ | $1$ |

**证明。** 命题 37.6 已给出全部相容词，引理 37.5 给出每词 $g_n$ 个向量，所以对每个达到的 $\rho$，

$$
|\mathcal F_\rho|=g_n|\mathcal A_\rho|.
$$

这不是任意算术坐标与地址选择的独立乘积：每个词的向量只能在共同终端/标量 CRT 方程的解集中选，且全部解已由引理刻画。

$n=0$ 时地址词已固定，故每个纤维为 $a^2$，包括空右词。$n=1,d\ge3$ 时一个位有 $a$ 个提升；$d\le2$ 时零位总合法，一位仅当 $\tau=0$ 才合法，每个相容位都有 $a$ 个提升，所以每个纤维为 $a(2-\tau)$。

$n=2,d=1$ 时相邻合法对是 $00,01,10$；$\tau=1$ 排除末位一的 $01$，所以每个纤维为 $3-\tau$。$d=2$ 时 $U_1$ 固定：$U_1=0$ 给 $00,10$，$U_1=1$ 只给 $01$，故精确大小为 $2-U_1$。$d\ge3$ 时两个位固定且每词一个向量，大小一。这里未知位相邻，不能把两个二选一算成四。

$n\ge3,m=1$ 时全部合法擦除词相容，每词一个向量；定理 11.2 的守卫词计数给 $N_n(\tau)$。这里只复用词的计数，不把有限向量边界当成精确终尾；$k=0$ 的每个词都可接未观察的零尾，故有全部 $F_{n+2}$ 个词。

$n\ge3,m\ge3$ 时仅末位未决。$d\ge2$ 时它唯一，大小一；$d=1$ 时零末位总合法，一末位需要已知前位 $U_{n-2}=0$ 且 $\tau=0$，故个别纤维精确为

$$
1+(1-U_{n-2})(1-\tau).
$$

$n\ge3,m=2,\ell$ 偶时，已知 $U_1$ 至终端词，只有初始位未决；允许位数为 $2-U_1$，且每位通过 $z_0=U_0\alpha+Mz_1\bmod L$ 给唯一相容向量，故纤维大小就是 $2-U_1$。$\ell$ 奇时，非空中间词 $U_1\cdots U_{n-2}$ 固定，首位有 $2-U_1$ 种，末位有 $1+(1-U_{n-2})(1-\tau)$ 种。命题 37.6 证明每个合法末位先共同确定唯一 $z_1\bmod2\ell$，每个合法首位再共同确定唯一 $z_0\bmod2\ell$，所以所有允许组合确实相容，纤维为

$$
(2-U_1)\bigl[1+(1-U_{n-2})(1-\tau)\bigr].
\tag{37.7}
$$

这里两端由同一非空已知词分隔，$n=3$ 时一位中间词已经足够；$n=2$ 不适用此乘积。逐式取最大值即给表中的上界。

这些上界全部达到。固定任意合法终端词 $w$，取 $r=0$、全部 $b_j=0$，用全零擦除词使该观察达到。在 $K$ 上可取地址 $0^nw0^\infty$ 与初始向量零；在实际域用后述联合实现取得相同有限目标。

$n=0$ 时零向量有 $a^2$ 个提升。$n=1$ 时相容式是 $2b\equiv0\pmod d$，所以 $d\le2$ 给全部接缝合法位、$d\ge3$ 给零位，每词的 $a$ 个提升全部存在。$n=2$ 时固定签名为零：$d=1$ 给全部接缝合法对，$d=2$ 给 $00,10$，$d\ge3$ 给 $00$；共同 CRT 为每对提供唯一向量。

$n\ge3,m\ge3$ 时恢复出的前缀和初始模 $m$ 向量为零，$d=1$ 给全部接缝合法末位，$d\ge2$ 只给零末位。奇偶情形的中间词与 $s_2$ 都为零；偶数 $\ell$ 固定末位零、首位两种，奇数 $\ell$ 给首位两种与 $2-\tau$ 种末位，每种组合的共同算术解由命题 37.6 保证。模一则每个合法词都由终端公式给一个向量。因此同一零算术观察对固定的 $w$ 达到每行 $M_\tau$，不是将互不相容的最优边缘拼起来。证毕。

对所有达到的有限观察取最大值，得到精确的全局最坏纤维

| 长度 | 条件 | $W$ |
|---|---|---|
| $n=0$ | 全部 | $a^2$ |
| $n=1$ | $d\le2$ | $2a$ |
| $n=1$ | $d\ge3$ | $a$ |
| $n=2$ | $d=1,2,\ge3$ | $3,2,1$ |
| $n\ge3$ | $m=1$ | $F_{n+2}$ |
| $n\ge3$ | $m=2,\ell$ 奇/偶 | $4,2$ |
| $n\ge3$ | $m\ge3,d=1/\ge2$ | $2,1$ |

取全零终端词（$k=0$ 时为空词）、零终端向量和全零保存读数，即实际零来源 $p_0$ 的 $R$，有 $\tau=0$，上述共同相容性逐行证明它达到全局最大 $W=M_0$。$n=0$ 时这也包括没有任何地址数据的空词情形，其 $a^2$ 只是缺少算术精度。

对每个已计数的目标，长度 $n+k$ 的合法前缀和模 $L$ 向量余数一起满足引理 2.2 的输入，故同一个实际来源实现两者；$R=f(J_L)$ 使其全部终端及保存数据保持。于是每个个别纤维、固定 $w$ 的上界和零观察最坏纤维在 $\Gamma$ 上都同样锐。这只传递有限目标纤维，不要求这些代表具有相同精确无限终尾。

令 $\mathcal E$ 是与已有 $R$ 合用、用于精确恢复 $J_L$ 的静态辅助字母表。复用定理 11.5（最小恢复字母表与达到构造）的有限纤维排序原理：在大小 $W$ 的纤维中为每个不同目标取一个来源代表，它们有相同 $R$，所以辅助符号必须互异，给 $|\mathcal E|\ge W$。反向，固定有限目标集合的一个顺序，以目标在自身 $\mathcal F_{R(p)}$ 中的秩编码，复用 $\{0,\ldots,W-1\}$；解码器由 $R$ 找纤维，再由秩取唯一目标，故达到 $W$。因而精确容量为

$$
|\mathcal E|_{\min}=W=M_0,\qquad
\text{固定二进制位数}_{\min}=\left\lceil\log_2W\right\rceil.
\tag{37.8}
$$

固定终端词时把 $W$ 换成 $M_\tau$，给定一个达到的完整观察时把它换成该观察的实际纤维大小。若 $e=g(R)$ 只依赖已有观察，非单点纤维中的不同目标仍由同一个 $e$ 表示，不能解析；辅助记录必须在源/目标区别尚可取得时保留，或由真正允许的附加观察提供。式 (37.8) 是静态容量，不计 $R$ 已有的存储、取得、在线更新、工作内存或物理成本，也不是完整来源恢复定理。

### 37.7 指定 Parry–Haar 律下的有限条件后验与熵

复用定义 9.1（符号 Markov 测度与 Haar 测度），概率只在本节声明为

$$
\lambda_{\rm PH}=\nu\otimes\mu
$$

在 $K$ 上的平稳 Parry–Haar 律。令 $\phi=(1+\sqrt5)/2$、$H_2(t)=-t\log_2t-(1-t)\log_2(1-t)$（零质量项取零），并写

$$
P=\begin{pmatrix}\phi^{-1}&\phi^{-2}\\1&0\end{pmatrix},\quad
\pi_0=\frac{\phi^2}{\phi^2+1},\quad\pi_1=\frac1{\phi^2+1},\quad
h=\log_2\phi,\quad
s=H_2(\pi_1),\quad
\gamma=\frac{2}{\phi^2+1}.
$$

设达到的有限观察为 $R=\rho$，终端词为 $w$，相容擦除词集合为 $\mathcal A_\rho$。定义 9.1 的产品律使每个合法地址词与每个初始模 $L$ 向量有联合质量

$$
\Pr(J_L=(uw,x))=L^{-2}\nu([uw]).
$$

空柱的权重取一。$R=f(J_L)$，而引理 37.5 给每个相容词恰好 $g_n$ 个向量，所以

$$
\Pr(R=\rho)=L^{-2}g_n\sum_{v\in\mathcal A_\rho}\nu([vw])>0.
$$

分子是单个相容目标的上述质量，分母是同一纤维中所有目标的质量和；有限 Bayes 公式遂给

$$
\Pr(J_L=(uw,x)\mid R=\rho)
=\frac{\nu([uw])}{g_n\displaystyle\sum_{v\in\mathcal A_\rho}\nu([vw])}.
\tag{37.9}
$$

纤维外概率为零；没有对精确无限尾的零概率单点进行有限事件条件化。对一个相容词求和其 $g_n$ 个向量，得到

$$
\Pr(V=uw\mid R=\rho)=
\frac{\nu([uw])}{\sum_{v\in\mathcal A_\rho}\nu([vw])},\qquad
\Pr(z_0\bmod L=x\mid V=uw,R=\rho)=1/g_n
$$

于该词的相容算术支撑上。共同 $g_n$ 是每个词对固定完整观察的相同 Haar 似然因子，故可在地址后验中抵消。命题 37.6 已证明相容词恰为摘要 $\mathscr S$ 的全部合法补全，因此

$$
\Pr(V=uw\mid R=\rho)=\Pr(V=uw\mid\mathscr S=\mathscr S(\rho)),
$$

$$
H(J_L\mid R)=\log_2g_n+H(V\mid\mathscr S).
$$

所以只有地址边缘后验及其条件熵由摘要决定；每个词的实际相容算术余数仍须用 $\rho$ 的全部 CRT 方程求出，完整目标后验的支撑仍依赖全部 $R$。地址词按 Parry 柱权重相对加权，不按纤维个数均匀；上述似然计算没有假设保存读数与地址先验独立。

命题 9.3 的反向一步律给定后继零时权重 $\phi^{-1},\phi^{-2}$，后继一时前位被守卫强制为零；因此一侧平均条件熵为 $h$，也直接复用定理 11.7 的一步值。定理 11.6—11.7 给完整未来的前缀平均值 $nh$；Markov 性使条件于非空有限终端词时第一未来位已足够，故在本节只引用其有限未来后果。无未来位时，平稳有限块的链式法则给 $s+(n-1)h$。

对中间位给定两侧，复用命题 12.8（双端桥与有限均匀来源的 Parry 表示）的一位桥律；只有两侧均为零才有 $000$ 与 $010$ 两条路径，且

$$
P_{00}^2=P_{01}P_{10}=\phi^{-2}.
$$

该位在此事件上公平，其余两侧组合强制零；事件的平稳概率为

$$
\Pr(U_{j-1}=0,U_{j+1}=0)=\pi_0(P^2)_{00}
=2\pi_0\phi^{-2}=2\pi_1,
$$

故

$$
H(U_j\mid U_{j-1},U_{j+1})=\gamma.
\tag{37.10}
$$

这是命题 12.8 特例的平稳平均，不是每个固定端点对的熵，也不另立一般桥定理。

对奇数终端模数、$n\ge3$ 的两端未决情形，令 $I=U_1\cdots U_{n-2}$、$A=U_0$、$B=U_{n-1}$。固定同一非空中间词 $I=i$，首末位的 Markov 柱权重分解为左因子 $\pi_aP_{a i_0}$、中间固定转移乘积及右因子；$k=0$ 时右因子为 $P_{i_{n-3}b}$，$k\ge1$ 时右因子为 $P_{i_{n-3}b}P_{bw_0}$ 再乘 $w$ 的固定内部转移。因此对同一 $I,w$ 归一化后，

$$
\Pr(A=a,B=b\mid I,w)
=\Pr(A=a\mid U_1)\Pr(B=b\mid U_{n-2},w).
$$

式 (37.9) 的共同算术似然保证完整 $R$ 不再改变这个地址分解。左因子是反向一步律，平均熵 $h$；右因子在 $k=0$ 时是正向一步律，平均熵 $h$，在 $k\ge1$ 时是给定 $U_{n-2},U_n$ 的一位桥，平均熵 $\gamma$。即使 $n=3$ 的中间词只有一位，分解仍成立；$n=2$ 中间词为空且两位相邻，须保留单独的两位块行。

$k=0$ 时使用 $\sum_{t=0}^1P_{bt}=1$ 对未观察的下一位积分，不能给定 $U_n=0$；计数用的虚拟 $\tau=0$ 不参与概率条件。$k\ge1$ 时终端更远位的转移因子在条件化中消去，故不进一步减少擦除位的不确定性；改变 $k$ 仍改变 $R,J_L$ 的完整目标和算术支撑，不是在识别它们的完整后验。

**定理 37.8（有限目标条件熵）。** $H(J_L\mid R)$ 的完整表为

| 长度 | 条件 | $k=0$ | $k\ge1$ |
|---|---|---|---|
| $n=0$ | 全部 | $2\log_2a$ | $2\log_2a$ |
| $n=1$ | $d\le2$ | $\log_2a+s$ | $\log_2a+h$ |
| $n=1$ | $d\ge3$ | $\log_2a$ | $\log_2a$ |
| $n=2$ | $d=1$ | $s+h$ | $2h$ |
| $n=2$ | $d=2$ | $h$ | $h$ |
| $n=2$ | $d\ge3$ | $0$ | $0$ |
| $n\ge3$ | $m=1$ | $s+(n-1)h$ | $nh$ |
| $n\ge3$ | $m=2,\ell$ 奇 | $2h$ | $h+\gamma$ |
| $n\ge3$ | $m=2,\ell$ 偶 | $h$ | $h$ |
| $n\ge3$ | $m\ge3,d=1$ | $h$ | $\gamma$ |
| $n\ge3$ | $m\ge3,d\ge2$ | $0$ | $0$ |

**证明。** 对每个地址词，算术项是 $\log_2g_n$；再对 (37.9) 的 Parry 柱概率取地址条件熵。无删除时只有 $a^2$ 个算术提升。一次读数在 $d\ge3$ 时确定首位，在 $d\le2$ 时保留首位，其条件熵分别为 $0$、$s$ 或 $h$。两次读数使用命题 37.6 的已证摘要：$d=1$ 时 $H(U_0,U_1\mid w)$ 为 $k=0$ 的 $s+h$ 或 $k\ge1$ 的 $2h$；$d=2$ 时摘要已有 $U_1,w$，剩余熵 $H(U_0\mid U_1,w)=H(U_0\mid U_1)=h$；$d\ge3$ 无剩余地址。这给出全部短长度行。

当 $n\ge3,m=1$，所有擦除位只受终端词，链式法则给 $s+(n-1)h$ 或已发表第 11.6—11.7 节的有限未来值 $nh$。当 $m\ge3$ 时只可能剩最后一位，$d=1$ 给一侧熵 $h$ 或双侧桥熵 $\gamma$，$d\ge2$ 为零。模二偶数终端模数只留下首位，熵为 $h$；奇数终端模数留下首尾两位，中间词分隔它们，得到 $2h$ 或 $h+\gamma$。这正好给出所有行。证毕。

例如 $n=2,d=1,k\ge1$ 且 $w_0=0$ 时，相容词 $00,01,10$ 各有一个算术提升，式 (37.9) 与反向 Parry 柱权重给它们的条件概率分别为 $\phi^{-2},\phi^{-2},\phi^{-3}$，并非各三分之一；$\phi^{-2}+\phi^{-2}+\phi^{-3}=1$。熵与残余字母是不同量，始终保持

$$
H(J_L\mid R)\le \mathbb E\log_2|\mathcal F_R|
\le\log_2\max_\rho|\mathcal F_\rho|.
\tag{37.11}
$$

有限纤维不均匀时不能取 $\log$ 最大纤维作为熵。已发表的命题 11.8 给出 $\lambda_{\rm PH}(\Gamma)=0$；联合引理只传递有限像和容量，不传递 $\Gamma$ 上的概率律。没有一击编码长度、允许的取得机制、在线内存最优性、物理熵或时间箭头结论。

### 37.8 历史、拓扑与适用边界

定理 13.6（实际有限来源的双边历史模型）、命题 13.7（完整历史纤维及其保留的信息）与命题 13.8（唯一历史提升及其非满射反例）区分当前终尾、足以恢复的保存记录、选定的可逆实现和全部相容历史。定理 13.6 的同胚/共轭是双边地址空间 $Z_D$ 与逆历史空间 $\mathcal H_D$ 之间的结论：$D$ 取单边地址前缀乘积的子空间拓扑，$\mathcal H_D$ 取 $D^{\mathbb N}$ 的乘积子空间拓扑；它不自动给出联合地址—profinite 拓扑下 $\Gamma$ 的同胚，也不推出全模数迹拓扑。集合核相等不能替代连续性和有限观察的证明。

若两条成功历史到达同一完整当前状态，并且后续记录和控制相同，则所有未来脚本的守卫、失败和读数均相同；旧历史只有在显式保留的历史坐标中才可被区分。$\delta h_0=\mathrm{id}$ 与零固定点给出基本例子。历史纤维的基数不转化为通用实现内存下界。

本章只讨论指定的 $K$、$\Gamma$、观察合同和有限目标。在 $K$ 上声明的 Parry–Haar 律下，$\Gamma$ 是零测度集合；定理 37.8 的概率只属于该律。有限目标随 $n$ 改变，残余表不是同一装置的单调在线成本轨迹；静态容量也不包含采集或物理成本。所有结论均保留守卫、失败、短长度、相邻位、空接缝和共同实现条件。

## 37.99 追加锚

## 37.100 终端地址长度与算术支撑（更正）

本节替代第 37.7 节「改变 $k$ 仍改变 $R,J_L$ 的完整目标和算术支撑」中的算术支撑依赖子句：改变 $k$ 改变 $R$ 的终端地址数据长度与 $J_L$ 的地址目标长度，但在下述固定非空接缝条件下，算术支撑不变。定理 37.7 的有限纤维与残余容量、式 (37.9) 的后验及定理 37.8 的熵公式保留原陈述与前提。

**定理 37.101（固定非空接缝下的支撑）。** 固定 $m,\ell\ge1$、$n\ge0$、终端向量余数 $r\bmod\ell$ 与保存读数 $(b_j\bmod m)_{j<n}$。设两个达到的观察为 $\rho=(w,r,(b_j))$ 与 $\rho'=(w',r,(b_j))$，其中 $w,w'$ 是长度 $k,k'\ge1$ 的合法终端词且 $w_0=w'_0$。则 $\mathcal A_\rho=\mathcal A_{\rho'}$，且对每个共同相容擦除词 $u$，式 (37.4) 的 $y\bmod L$ 解集相同；因而投影到 $z_0\bmod L$ 的算术支撑也相同，与终端更远位无关。

证明。因 $w,w'$ 均合法，$n\ge1$ 时 $uw$ 合法恰当 $u\in W_n$ 且 $u_{n-1}w_0=0$，换成 $w'$ 不改变此条件；$n=0$ 时只有空擦除词。式 (37.4) 的两类算术方程只含 $u,r,(b_j),m,\ell,n$，不含 $k$ 或 $w$ 的更远位。因此合法候选、是否有算术解及每词的全部算术解均保持。这里比较的是擦除词与算术解集，不把不同长度的完整地址目标 $uw$ 与 $uw'$ 视为同一目标。$k=0$ 时不存在右接缝，不能给未观察的下一位指定零，也不属于上述同首位比较。

**定理 37.102（实际零来源核对）。** 取 $m=\ell=3,n=1$。实际零来源 $p_0=(0^\infty,0)\in\Gamma$ 在 $k=1$ 与 $k=2$ 时分别给终端词 $0$ 与 $00$，两者的终端向量余数均为零、保存读数均为 $c_0=0$。两者的相容擦除词均只有 $0$，相容算术支撑均为 $\{(0,0)\}$。

证明。零来源在剥离下固定。这里 $L=3$；对候选擦除位 $b\in\{0,1\}$，式 (37.4) 给 $y\equiv b\alpha\pmod3$ 与 $qy\equiv0\pmod3$，故 $2b\equiv0\pmod3$，强制 $b=0$ 及 $y=(0,0)\bmod3$。两个零终端词均满足守卫，但完整目标中的地址词分别为 $00$ 与 $000$，长度确实不同。

## 37.199 追加锚

## 38 精确预算下混合相干与完整记忆三分律

固定临界六格 FIB 仪器、一个固定的合法切点归属以及
$$
t=\frac{\sqrt5-1}{2},\qquad g=t^3=2t-1,\qquad
\lambda=\frac{t^2}{10}.
$$
本章只讨论一个给定的
$$
b\in\mathbb Q(t),\qquad 0\le b<\lambda .
$$
窗口边、guard、来源分支和归属均保持固定。记 $\Omega$ 为起始 guard 为零的全部合法地址，记 $D\subset\Omega$ 为最终为空的地址。解码器确定且因果；每次取得允许有限计算和有限输出批次，输出按位置有序、只追加且不可回读。它在每条实际 $\Omega$ 记录上保持安全，在每条实际 $D$ 记录上逐位置生效，包括无限空窗补齐。所有可读的持久存储、工作存储、控制、计数器、位置和时序信息都计入完整内存；没有 End、支持上界、免费重放或免费时钟。

为固定仪器记切点为
$$
a_c=-t^2-\lambda,\qquad b_c=g-3\lambda,\qquad c_c=t-5\lambda,
\qquad d_c=2t-7\lambda,\qquad e_c=2t+\lambda,
$$
来源分支和 guard 的具体关系为
$$
0\to0:3,0,2;\quad 0\to1:5,25;\qquad
1\to0:3,0;\quad 1\to1:5,
$$
并采用 $f_\ell(y)=\Delta_\ell-gy$ 与其逆 $F_\ell$。本章不改变这些切点的归属，也不把闭扩张端点自动当作实际目标。

这里
$$
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})=(-t,0,t^2,1,2-t).
$$

采用一个统一的出发坐标约定：第 $n$ 步先读取第 $n$ 个出发颜色，再沿每条候选历史的合法来源边延伸。因此取得 $n$ 个颜色后，每条候选历史包含 $n$ 条候选来源边及其标签，坐标 $n$ 尚未观察；实际观察输入是颜色，隐藏的来源标签并非观察读数。固定终尾 $\xi$ 接在这一步之后时，未来记录写作 $S_\xi$。这与已发表解码器中“$n$ 色、$n-1$ 边”的记号只差一个终端坐标，本章所有计数均采用当前约定。

本章的规范图是一般可达的混合 divergence-flag 图 $\mathcal M_b$。第一分量必须 $D$-live，第二分量必须 $\Omega$-live；首源标签是其强连通分量所用的边字母。则最坏情形、截至 $N$ 次取得的最优完整峰值满足
$$
\boxed{
\begin{array}{c|c}
\mathcal M_b & \text{最优完整峰值}\\ \hline
\text{无环}&O(1)\\
\text{有环且每个有环强连通分量首源相干}&\Theta(\log(N+2))\\
\text{存在首源不相干的有环强连通分量}&\Theta(N+1).
\end{array}}
\tag{38.1}
$$
这里的结论是一个针对指定 $b$ 的有限数学判定；不执行图构造，也不评价任何具体预算。证明的关键是精确的端点排除、全路径提升、完整的最长公共前缀矩阵，以及在相同预算下固定混合终尾的泵送。

### 38.1 精确观察、端点闭包和状态

设六个实际颜色格为 $C_i$（切点归属已固定），并定义
$$
O_i^b=\{x\in X:\exists y\in C_i,\ |x-y|\le b\},\qquad
E_i^b=\overline{O_i^b},\qquad Z_i^b=E_i^b\setminus O_i^b.
\tag{38.2}
$$
裁剪不会改变这个等价关系：实际目标给出 $O_i^b$ 中的点，反之取误差为目标减去真实坐标即可。闭扩张的端点不能自动视为实际可取得的颜色，故必须保留 $Z_i^b$。

来源标签集为
$$
\Lambda=\{3,0,5,2,25\},
$$
合法边为
$$
0\to0:3,0,2,\qquad 0\to1:5,25,\qquad
1\to0:3,0,\qquad 1\to1:5,
$$
且
$$
f_\ell(y)=\Delta_\ell-gy,\qquad
F_\ell(x)=\frac{\Delta_\ell-x}{g}.
\tag{38.3}
$$
其中 $I_0=X=[-1,1+t]$，$I_1=[-1,t]$。已发表引理31.2、定义31.3和定理31.4适用于这些 $\mathbb Q(t)$ 端点。构造有限端点集合时，除观察端点、两个 guard 端点和所有合法分支域端点外，**先把标量零加入种子**，再作所有仍落在 $X$ 内的逆分支闭包。记所得有限集为 $B$。于是 $0\in B$，并且
$$
z\in B,\quad F_\ell(z)\in X\Longrightarrow F_\ell(z)\in B.
\tag{38.4}
$$
这个显式零种子是之后单点有限尾判定的必要部分。

一个精确单分量状态写为
$$
q=(s,P,S),\qquad P\subseteq I_s,\qquad S\subseteq B\cap I_s,
\tag{38.5}
$$
其中 $P$ 是基本闭区间或单点，$S$ 保存从全部过去颜色传输下来的未决等式排除。读入颜色 $i$ 时要求
$$
P\subseteq E_i^b,
$$
并把 $Z_i^b\cap P$ 加入 $S$。若随后走合法边 $\ell:s\to s'$，则把每个未决阈值经 $F_\ell$ 传输，并删去落在 $I_{s'}$ 外的阈值：
$$
S'=\{F_\ell(z):z\in S\cup(Z_i^b\cap P),\ F_\ell(z)\in I_{s'}\}.
\tag{38.6}
$$
两个不同历史若传到同一个阈值，所询问的是同一个当前坐标等式，故可以合并。负斜率只反向不等式，不改变等式真假。

对 $D_s$ 写 $\kappa_s(D_s)$ 表示 guard 为 $s$ 的最终空尾标量集合。状态的精确生存性为
$$
\begin{array}{c|c}
\text{域}&\text{live 条件}\\ \hline
\Omega&P\text{ 非退化，或 }P=\{z\}\text{ 且 }z\notin S,\\
D&P\text{ 非退化，或 }P=\{z\},\ z\notin S,\ z\in\kappa_s(D_s).
\end{array}
\tag{38.7}
$$
非退化片的内部避开有限集 $B$，且合法空尾截断在每个 guard 区间内稠密，所以可选取避开 $S$ 的 $D$-尾和 $\Omega$-尾。单点没有这样的自由度，必须逐字检验排除。

单点的 $D$-条件还可完全写成有限图的可达性：带 guard 类型的单点 $(s,\{z\})$ 当且仅当沿合法单点边可在有限步到达标量为零的单点，才有有限合法尾。正向地，有限尾在最终空尾前经过一串逆分支，因 (38.4) 全部留在 $B$，最终到达零；反向地，从该单点到零的路径后接 $0^\infty$ 即为有限尾。仅有 $z\in\mathbb Q(t)$ 不能替代这个测试。

**精确提升与逆向生存。** 取一条有限精确路径，若终端状态通过 (38.7)，任选其域内的一个终尾标量避开终端的 $S$，并选一条相应合法终尾。已发表定理31.4的全包含边规则
$$
P\subseteq f_\ell(I_{s'}),\qquad P'\subseteq F_\ell(P)
\tag{38.8}
$$
把这个同一终尾沿整条路径向前提升。已经离开 guard 的阈值对所有延续都不可能相等，仍在 $S$ 中的阈值则由终尾的避开保证不相等。因此整条路径的每个过去颜色都由同一个实际来源实现。反向地，任何实际完成给出末状态的 live 条件。

由此得到：若一条边的目标是 $D$-live（分别为 $\Omega$-live），则其来源也是 $D$-live（分别为 $\Omega$-live）。这就是逆向生存性；有限尾可在边前接回去，且最终空性在有限前缀前接下保持。丢失的 $D$-生存性以后不会重新出现。

对一个长度为 $n$ 的共同取得历史，记
$$
H_n=\{(q,w):q\text{ 为 }\Omega\text{-live 精确状态，存在该历史的精确路径到 }q,\ |w|=n\},
$$
并以 $H_n^D$ 表示终状态为 $D$-live 的子集。若两个路径落到同一个 $(s,P,S)$，则忘去 $S$ 后是已发表完整闭图中的同一终端顶点。由于 $b<\lambda$，已发表第36章引理36.16的完整闭宽度（包括无有限尾的 $\Omega$-单点）给出：固定历史在每个终端闭顶点至多有一个过去来源词。因此
$$
|H_n|\le Q
\tag{38.9}
$$
其中 $Q$ 是固定的精确 $\Omega$-状态数；同一精确状态的合并无需比较未保存的词。若某时 $H_n^D=\varnothing$，逆向生存性使其以后永久为空，解码器可进入永久静默状态；实际 $D$ 记录不会到达这个状态。

这里使用的是严格亚临界的完整闭宽度，而不是只对 $D$-live 状态作唯一性假设。令 $\delta=\lambda-b>0$。在一个共同闭颜色中可能出现的不同来源标签只有下表所列的类型；右列是该共同闭扩张的宽度，中列是两条分支的平移差：
$$
\begin{array}{c|c|c|c}
\text{颜色}&\text{不同标签}&\text{平移差}&\text{闭扩张宽度}\\ \hline
0&(3,0)&t&t-\delta\\
1&(3,0)&t&t-2\delta\\
2&(0,5)&t^2&t^2-2\delta\\
3&(5,2)&t&t-2\delta\\
4&(2,25)&t^2&t^2-2\delta\\
5&(2,25)&t^2&t^2-\delta
\end{array}
\tag{38.9a}
$$
端点行在 $\delta>0$ 时已经不能产生新的不同标签，保留它们只会放宽必要条件。若同一闭颜色历史的两条路径到达同一个闭终端顶点，利用 guard 相对满像在终端片内选同一个 $\Omega$-尾，即使该片是没有有限尾的单点。取两有限来源词的最后一个不同标签位置 $j$；其后的来源标签和同一终尾相同，故下一坐标相同，而 (38.3) 使第 $j$ 个真坐标之差恰为表中的平移差。两坐标不可能同时落在表中的共同闭扩张内，因为每个平移差严格大于相应宽度。于是两过去词相同。该论证覆盖所有 $\Omega$-only 单点，说明 (38.9) 的宽度来自完整闭候选，而非来自把 $D$-唯一性误用于开关系。

### 38.2 一般可达 divergence-flag 图

把一个 $D$-live 精确状态和一个 $\Omega$-live 精确状态配成一对。两分量读取同一个颜色，各走自己的合法来源边并分别更新 pending 集。两分量从 guard 零、空 pending 集出发。flag 在来源词相等时为零；第一次出现不等来源标签后置为一，并且以后永久保持一。只保留每一步都混合生存的后继。

$\mathcal M_b$ 定义为所有从上述初态可达、flag 已为一的混合状态和边的图。允许在第一次分歧前有任意长的相等来源前缀；不在输出边界复位 pending 集，也不把第一次分歧强制改成一个新起点。逆向生存性保证实际可完成的混合路径的每个中间状态仍在图中。

若一条边 $e$ 的第一分量来源标签为 $\ell_1(e)$，则本章所有强连通分量的字母投影固定为
$$
\ell_1:E(\mathcal M_b)\longrightarrow\Lambda.
\tag{38.10}
$$
第二分量标签、颜色和有序标签对仍保留在状态转移中，但不取代 (38.10) 的投影。对同一状态的两个非空返回，设长度分别为 $m_0,m_1$，第一源词为 $U_0,U_1$，令 $L=\operatorname{lcm}(m_0,m_1)$。称它们相干，当且仅当
$$
U_0^{L/m_0}=U_1^{L/m_1}.
\tag{38.11}
$$
一个强连通分量首源相干，是指其任一基点的所有非空返回均满足 (38.11)。

有限单字母图的相干判定可写成相位证书。若分量有 $s$ 个顶点，则相干等价于存在 $1\le p\le s$、周期词 $P\in\Lambda^p$ 和 $\theta:V\to\mathbb Z/p\mathbb Z$，使每条内部边 $v\to w$ 满足
$$
\ell_1(v\to w)=P_{\theta(v)},\qquad
\theta(w)=\theta(v)+1\pmod p.
\tag{38.12}
$$
证明是标准的返回周期论证：取最短返回，其内部顶点不重复，长度不超过 $s$；其无限重复的最短周期块为 $P$。相干性使每个返回的无限重复都等于 $P^\infty$，于是路径长度模 $p$ 给出良定义的 $\theta$，每条边的标签就是相应相位。反向地，(38.12) 直接使所有返回成为周期幂。沿缩合 DAG 穿过多个有环分量时，固定入口、出口和连接边，所有第一源词属于有限多个形式
$$
a_0P_1^{e_1}a_1\cdots P_d^{e_d}a_d,\qquad e_i\in\mathbb N,
\tag{38.13}
$$
其中允许多个幂因子；不能把多个相干分量错误压成一个幂。

### 38.3 全部候选的最长公共前缀矩阵

固定长度 $n$ 的历史。令 $p_n$ 为所有 $H_n$ 来源词的最长公共前缀，并写
$$
w_n(q)=p_n v_n(q),\qquad |v_n(q)|=r_n.
\tag{38.14}
$$
令 $A_n$ 为所有终端精确状态，$A_n^D$ 为其中的 $D$-live 状态。只要 $A_n^D\ne\varnothing$，保存下列数据：

1. 全部 $A_n$ 的状态标识及其 $D$-live 标志；
2. 每个 $d\in A_n^D$ 的残余词 $v_n(d)$ 的多幂模板描述；
3. 残余长度 $r_n$；
4. 对每个 $D$-行和每个 $\Omega$-列的完整矩阵
$$
\mathsf C_n(d,q)=\operatorname{lcp}\bigl(v_n(d),v_n(q)\bigr),
\qquad d\in A_n^D,\ q\in A_n.
\tag{38.15}
$$

每一个 $\Omega$-only 状态都保留其列，虽然不保存该列对应的完整词；所有 $D$-行都保留。矩阵符号固定为 $\mathsf C_n$，不使用此前章节的损失记号。由 (38.9)，行数、列数和矩阵大小均由固定常数界定。

假设在第 $n+1$ 步读入一个颜色。生成全部颜色相容的后继，只保留 $\Omega$-live 目标，并在每个合并后的目标状态 $q'$ 选一条代表入边
$$
q\xrightarrow{c}q'.
\tag{38.16}
$$
同一目标状态的所有代表入边所拼出的完整来源词相同，因为状态词唯一。若目标 $d'$ 是 $D$-live，逆向生存性保证所选前驱 $d$ 也是 $D$-live，所以其旧残余描述可用；新的 $D$-词不需要从未保存的 $\Omega$-only 词重建。

设代表入边为
$$
d\xrightarrow{a}d',\qquad q\xrightarrow{c}q'.
$$
在尚未发射新的共同前缀时，新残余的长度为 $r_n+1$，且
$$
\widetilde{\mathsf C}(d',q')=
\begin{cases}
\mathsf C_n(d,q),&\mathsf C_n(d,q)<r_n,\\
 r_n+1,&\mathsf C_n(d,q)=r_n\text{ 且 }a=c,\\
 r_n,&\mathsf C_n(d,q)=r_n\text{ 且 }a\ne c.
\end{cases}
\tag{38.17}
$$
若旧最长公共前缀在残余内部已经结束，追加字母不能增加它；若两旧残余全等，则追加字母相等时增加一位，否则停在 $r_n$。因此该式只读取旧矩阵和两个新增标签，对未保存的列词没有隐式访问。代表的选择不影响结果，因为目标状态所代表的完整词唯一。

构造过程中暂不释放任何旧数据：保留所有旧行、旧列、旧词描述、代表入边和完整旧矩阵，即使某个旧状态最终不在后继集合中。使用固定大小的 old/new 缓冲区，先完成全部后继、合并、$\widetilde{\mathsf C}$、新 $D$-词描述和发射批次的准备，再释放旧缓冲区。

若新的 $D$-live 集为空，进入永久静默状态。否则任选新 $D$-状态 $d_*$，置
$$
c_*=\min_{q'\in A_{n+1}}\widetilde{\mathsf C}(d_*,q').
\tag{38.18}
$$
由于 $d_*$ 本身是候选，右侧正是所有新候选词的共同前缀长度。由 $d_*$ 的扩展词逐字写出这 $c_*$ 个首字母；对每个新 $D$-词删除同样的前缀，并令
$$
\mathsf C_{n+1}(d',q')=\widetilde{\mathsf C}(d',q')-c_* ,\qquad
r_{n+1}=r_n+1-c_*.
\tag{38.19}
$$
所有差值非负，且发射后的累计输出正好由 $p_n$ 延长为 $p_{n+1}$。删除后逐一把新词正规化为固定模板表示，最后才丢弃旧描述。初态 $A_0$ 是 guard 为零、pending 集为空的全部 $\Omega$-live 单分量精确状态，其中的 $D$-live 状态构成 $A_0^D$，使用空残余、$r_0=0$ 和零矩阵。混合图 $\mathcal M_b$ 另将两个这样的初始分量配对，并要求第一分量 $D$-live、第二分量 $\Omega$-live。由上述步骤对 $n$ 归纳，即得 (38.14)--(38.15) 的不变量。整个过程中没有回读已发射输出，也没有重建任何 $\Omega$-only 词。

### 38.4 相干分量的多幂表示与上界

设某个残余 $v_n(d)$ 非空。由于 $p_n$ 已是所有候选词的最长公共前缀，存在一个 $\Omega$-live 候选词在残余的首字母处与它不同。取这两个候选的原始精确路径；它们在 $p_n$ 上相同，随后跨过第一次不等来源边，之后的混合路径留在 $\mathcal M_b$。所以每个非空 $D$-残余都是一个初始有限标签加上 $\mathcal M_b$ 的首源投影路径词。

若 $\mathcal M_b$ 无环，flag-one 路径长度有统一上界，故所有残余长度、矩阵项和模板参数均在固定有限集合内。更新时不需要保存绝对取得计数；状态标识、有限残余和全部比较控制均为常数大小。由 (38.17)--(38.19) 得到一个常数完整内存解码器。

现在假设 $\mathcal M_b$ 有环且每个有环强连通分量首源相干。相位证书 (38.12) 及缩合图的有限 DAG 给出有限个多幂模板 (38.13)，覆盖每个 $D$-残余。模板数、每个模板的幂因子数和字面块长度都只依赖固定图。一个幂指数不超过残余长度，故可用 $O(\log(n+2))$ 位存储。矩阵有至多 $Q^2$ 个整数项，每项也至多为 $n$。

完整工作空间必须覆盖整个更新阶段，而不只是最终的规范描述。保存旧/新状态表、旧/新矩阵、旧/新 $D$-词描述、代表入边、追加标签、删除偏移、最长公共前缀比较位置、模板编号、固定数目的指数搜索计数器和输出扫描位置，每个可变整数均只需 $O(\log(n+2))$ 位。任意模板词的指定位置可由固定字面块、幂指数和一个位置计数器直接读取；比较和求最长公共前缀用索引扫描，绝不展开线性词。删除前缀得到的临时描述只增加一个偏移和一个追加字母。正规化时遍历固定模板及其指数元组，用索引字符比较寻找匹配；这是有限数学搜索，不提出运行时间界，也不保存搜索树。由模板保证至少存在一个匹配。

于是上界解码器的完整峰值为
$$
O(\log(N+2)).
\tag{38.20}
$$
所有实际 $\Omega$ 来源的精确候选都被保留，故每次发射的共同前缀安全。对实际 $D$ 来源，其精确候选在每一步都为 $D$-live，因而不会进入静默状态。另一方面，固定预算 $b<\lambda$ 的精确候选包含于临界闭预算 $\lambda$ 的候选集合；已发表定理30.6对每条实际 $D$ 记录和每个有限 $L$ 给出某个 $H_L$，使所有更长取得历史的临界闭候选都共享真实前 $L$ 个来源标签。因此本章的 $p_n$ 也最终包含该前缀，逐位置输出成立。这里使用的是闭的 $\Omega$ 候选紧致性；没有把精确的开端点关系当作紧空间，也没有假定 $\Omega$-only 词具有自身的幂表示。

### 38.5 相同预算的循环下界

先设 $\mathcal M_b$ 有一个可达有环强连通分量。取一条包含第一次分歧的 stem 到达一个完整返回状态，再取一条非空返回。stem 的颜色、第一和第二来源词分别记为 $h,P,Q$，返回的对应词记为 $w,A,B$，其中
$$
|h|=|P|=|Q|=a,\qquad |w|=|A|=|B|=m\ge1.
\tag{38.21}
$$
令 $k<a$ 为 $P,Q$ 的第一次不同位置；其前面有 $k$ 个共同来源标签。返回状态包括两个 guard、两个片、两个完整 pending 集，而不是只包括投影标签。

在该同一完整返回状态一次选定第一分量的 $D$-尾 $\xi$ 和第二分量的 $\Omega$-尾 $\eta$，各自标量避开当前 pending 集。对每个 $j\ge0$，整条提升给出同预算 $b$ 下的实际来源和记录
$$
\alpha_j=PA^j\xi\in D,\qquad
\beta_j=QB^j\eta\in\Omega,
\tag{38.22}
$$
$$
hw^jS_\xi\quad\text{和}\quad hw^jS_\eta.
\tag{38.23}
$$
终端坐标在本章约定中未观察，故未来确实从同一个 $S_\xi$ 或 $S_\eta$ 开始；没有重复取得终端坐标。所有返回次数使用同一个预算和同一返回状态的 pending 约束，没有任何预算余量。

由于 stem 在位置 $k$ 首次分歧，安全性允许在每个 $hw^j$ 后已经写出的词至多是共同 stem 的一个前缀，故只有至多 $k+1$ 种可能的旧输出。若 $\alpha_i=\alpha_j$（$i<j$），消去共同有限前缀得
$$
\xi=A^{j-i}\xi.
$$
这迫使 $\xi=A^\infty$；而 $\xi$ 最终为空，于是 $A=0^m$ 且 $\xi=0^\infty$。在这个常值分支，所有 $\alpha_j$ 都是同一来源 $P0^\infty$。

常值分支仍不能给出一个合法解码器。对该同一实际来源的任意坐标 $r$，取足够大的有限 $j$，使坐标 $r$ 落在记录 (38.23) 的共同取得段内；该记录证明该坐标的颜色属于精确可取得集合。逐坐标选择一个实际目标即可实现无限颜色词 $hw^\infty$，没有取闭端点目标的极限。每个有限取得时刻都位于某个 $hw^j$ 检查点之前，安全性仍由 $\beta_j$ 强制旧输出只能是共同 stem 前缀；有序只追加输出因此在这条实际 $D$ 记录上永远不能越过位置 $k$，违背逐位置生效。故在存在合法解码器的前提下，$\alpha_j$ 必须两两不同。

记处理完 $hw^j$ 后的完整配置为 $c_j$，并把此前输出记为 $o_j$。若 $(c_i,o_i)=(c_j,o_j)$，则接上同一个实际未来 $S_\xi$ 后，确定性和不可回读输出给出相同的未来输出；但两个不同的 $D$ 来源 $\alpha_i,\alpha_j$ 要求在某个有限位置输出不同标签，矛盾。因此 $J+1$ 个检查点给出至少
$$
\frac{J+1}{k+1}
\tag{38.24}
$$
个不同完整配置。一条随视界 $N$ 选定的实际记录 $hw^JS_\xi$ 按顺序经过所有这些检查点，所以这是单条实际记录上的峰值下界。至多容纳这些配置的完整二进制存储必须满足
$$
B^{\rm worst}_{b,\mathcal A}(N)\ge
\log_2\!\left(\frac{\lfloor (N-a)/m\rfloor+1}{k+1}\right)-O(1),
\tag{38.25}
$$
从而任何有环图都给出 $\Omega(\log(N+2))$ 下界。结合 38.4 的上界，得到第二行的 $\Theta(\log(N+2))$。计数中包含了完整配置、可读计数和时序，旧输出只作为至多 $k+1$ 个联合状态的分母，不被当作免费可读存储。

### 38.6 首源不相干给出线性下界

设某个有环强连通分量首源不相干。取同一完整混合状态上的两条返回，并同步到相同长度 $L$，使其第一源词为 $U_0,U_1$，且
$$
U_0\ne U_1,\qquad |U_0|=|U_1|=L.
\tag{38.26}
$$
第二源词和共同颜色词分别记为 $V_0,V_1$ 与 $W_0,W_1$。取包含第一次分歧的 stem，词为 $(h,P,Q)$，长度为 $a$，并令 $k<a$ 为首次不等位置。一次选定同一返回状态的 $D$-尾 $\xi$ 和 $\Omega$-尾 $\eta$。对任意二进制词 $z=z_1\cdots z_j$，整条提升给出
$$
\alpha_z=PU_{z_1}\cdots U_{z_j}\xi\in D,
\qquad
\beta_z=QV_{z_1}\cdots V_{z_j}\eta\in\Omega,
\tag{38.27}
$$
以及同预算共同取得历史
$$
h_z=hW_{z_1}\cdots W_{z_j}.
\tag{38.28}
$$
第一分量的未来对所有 $z$ 都是同一个 $S_\xi$。因为两个返回的等长第一源词不同，固定 $j$ 时 $z\mapsto\alpha_z$ 单射；不需要任何噪声预算余量或闭端点极限。

还必须说明共同颜色块本身随二进制拼接而不同。若 $W_0=W_1$，则取只用一次返回的两条第一分量来源 $PU_0\xi$ 与 $PU_1\xi$。它们是不同的有限来源词，且由同一个精确返回状态、同一个实际终尾和同一个共同颜色词得到相同的完整实际记录；这直接违反安全性与 $D$ 上逐位置生效的解码器合同。所以 $W_0\ne W_1$。由于两个块等长，固定 $j$ 时 $z\mapsto h_z$ 也单射；同时 $z\mapsto\alpha_z$ 由 $U_0\ne U_1$ 单射。

安全性再次说明每个 $h_z$ 后的旧输出只能是共同 stem 前缀之一，最多 $k+1$ 种。若两个不同的 $z,z'$ 同时有相同完整配置和相同旧输出，接同一个 $S_\xi$ 会产生相同未来输出，违背两个不同 $D$ 来源的逐位置生效。因此在同一长度 $a+jL$ 的所有二进制历史中，至少有
$$
\frac{2^j}{k+1}
\tag{38.29}
$$
个不同完整配置。这里的配置可分布在不同实际记录上，但最坏情形峰值至少要容纳它们；它们在相同取得长度比较，故不能借助未计价的阶段号合并。取 $j=\lfloor(N-a)/L\rfloor$，容量估计给出
$$
B^{\rm worst}_{b,\mathcal A}(N)\ge j-O(1)=\Omega(N+1).
\tag{38.30}
$$
已发表定理33.13的临界闭图解码器在 $b\le\lambda$ 的所有较小实际记录上仍安全并逐位置生效，给出 $O(N+1)$ 上界。因此首源不相干的第三行为 $\Theta(N+1)$。

线性证明只使用第一分量的首源分支，并要求它确实为 $D$-live。第二分量仅用于安全性竞争；把一个只在 $\Omega$-only 单点上分支的分量交换到第一位置，不能推出线性下界。

### 38.7 一个固定闭返回族的精确终尾判据

上面的混合图直接保留实际 $D/\Omega$ 生存性。对于一个先在闭图中提出、再想在同一预算转成指定返回片内固定实际终尾的具体族，可以给出完全充要的判据。固定一条含分歧 stem、两条同步返回和它们的共同出发颜色词；返回 piece 分别记为 $P_1\subseteq I_{s_1}$ 与 $P_2\subseteq I_{s_2}$。返回词已同步到同一长度，并按第一源投影取为不同的两个词。本节要求两条固定终尾的标量分别位于指定的 $P_1$ 与 $P_2$；以下充要条件和失败结论均在这一限制内。

从最初空 pending 集开始，沿 stem 以及两条返回的每一个有限二进制拼接传输 (38.6) 的排除集合。空拼接也包括在内。令 $S_j(z)$ 为拼接 $z\in\{0,1\}^*$ 后在第 $j$ 个返回片的 pending 集，并置
$$
S_j^*=\bigcup_{z\in\{0,1\}^*}S_j(z),\qquad
K_j=P_j\setminus S_j^*,\qquad j=1,2.
\tag{38.31}
$$
尽管拼接数无穷，所有 $S_j(z)$ 都是有限集 $B\cap I_{s_j}$ 的子集；它们由有限 pending 状态的可达性决定，故并集仍是有限集合。则存在一个固定第一尾 $\xi\in D_{s_1}$ 和一个固定第二尾 $\eta\in\Omega_{s_2}$，满足 $\kappa_{s_1}(\xi)\in P_1$ 和 $\kappa_{s_2}(\eta)\in P_2$，使它们在预算 $b$ 下实现整个有限拼接族，当且仅当
$$
K_1\cap\kappa_{s_1}(D_{s_1})\ne\varnothing,\qquad K_2\ne\varnothing.
\tag{38.32}
$$

先证充分性。由 (38.32) 选定第一片中的一个标量 $x_1$ 和第二片中的一个标量 $x_2$，分别编码为固定的 $D$-尾和 $\Omega$-尾，且避开每一个 $S_j(z)$。对任一有限拼接 $z$，从这个同一终尾沿整条 stem 与返回路径提升。终端标量避开该拼接的全部未决排除，已传出片的排除由 (38.6) 保证永不相等，于是同一对固定终尾实现该拼接的所有观察和来源边。

再证必要性。若标量分别位于指定 $P_1,P_2$ 的固定终尾实现整个路径族，则其终端标量不能等于任一拼接产生的未决阈值；因此标量分别属于 $K_1,K_2$。第一尾本来属于 $D_{s_1}$，所以其标量属于 $K_1\cap\kappa_{s_1}(D_{s_1})$；第二尾属于 $\Omega_{s_2}$，而状态相对满像给出 $K_2$ 中每个标量的合法尾。两方向均使用同一个终尾的全路径提升，因而不是对每个拼接另选一个来源。

若两片都非退化，有限集 $B$ 的内部补集非空，且最终空尾标量在片内稠密，所以 (38.32) 自动成立。单点可能因其点落入 $S_j^*$ 而失败；第一片即使未被排除，还可能没有任何有限最终空尾标量。第二片为 $\Omega$-only 单点并不妨碍安全性。这里的失败只说明这个指定闭返回族不能由标量分别位于 $P_1,P_2$ 的一对固定终尾转移；它不排除这些返回片之外不受本节限定的终尾，也不排除同一预算的另一族或另一条混合见证，更不构成一个具体的亚临界 FIB 反例。特别地，不能从一般 singleton 测试断言一个完全 singleton 的首源不相干 FIB 强连通分量确实存在。

### 38.8 三分律、有限判定与范围

把 38.1--38.7 合并。端点种子和 (38.4) 给出有限的精确状态空间；(38.7) 给出 $D$-live 与 $\Omega$-live；全包含边和共同终尾提升给出整个历史的实际性；(38.9) 给出包含所有 $\Omega$-only 单点的固定宽度。由这些事实构成的 $\mathcal M_b$ 是一个有限数学对象。

若它无环，38.4 给出常数上界；下界不再需要循环泵送，故得到第一行。若它有环且全部有环强连通分量满足首源相干，38.4 给出对数上界，38.5 对任一可达环给出对数下界，得到第二行。若存在首源不相干的有环强连通分量，38.6 给出线性下界，而定理33.13 的固定解码器给出线性上界，得到第三行。这三个条件互斥且穷尽所有有限有向图情形。

强连通分量的首源相干性可由 (38.12) 的有限相位证书决定；也可用有限长度返回证书作相同的精确比较。这里的“决定”只表示对给定 $b\in\mathbb Q(t)$ 存在有限精确的数学规格，不给出具体图或预算分类。多项式数量的路径或词本身不提供工作空间界；真正使用的是固定候选宽度、固定多幂描述和 (38.17)--(38.19) 的全矩阵更新。

三分律严格依赖 $b<\lambda$。在临界端点，完整闭图的 $\Omega$-only 单点可能承载多个过去词，故本章的全宽度前提不自动延伸。对不属于 $\mathbb Q(t)$ 的任意代数预算，本章也不提供第31章所需的有限端点逆闭包；不把“代数”替换为本章的域假设。未知的过渡半径、其是否属于某个代数域以及其端点记忆阶数均不在本章结论内。

本章只断言固定仪器、固定归属、固定 $b\in\mathbb Q(t)\cap[0,\lambda)$ 下的完整记忆阶数。没有复位图等同性、未知半径数值分类、跨归属独立性、物理时间或熵解释，也没有把任何未验证的图执行、程序运行或形式证明当作结论。所有下界使用同一预算下的实际有限来源和实际共同未来；所有上界计入处理期间的旧/新缓存、矩阵、计数器和输出扫描。

## 38.99 追加锚
## 39. 固定返回族的有限包络证书与端点可行性

同一个合法返回族允许任意多个有限返回，但其最小闭观察预算可以由有限个区间端点确定。闭证书能否支持一对固定的实际终尾，则另受颜色端点归属约束：非退化包络的内部自动避开全部归属障碍；单点竞争包络必须检查一个带端点旗标的轨道可行集。本章证明这两层结论，并在满足完整恢复合同时把它们连接到记忆下界和定义36.26的转变半径 $R$。

所用前提均为本卷[固定版本中的已发布结果](https://github.com/the-omega-institute/trureturing/blob/b7e6d6b26598bea84f42ed06e830a11bd5cff1ea/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md)：定义14.5、命题14.6、定理14.7和定理17.2提供实际地址、状态相对纤维和满像；式 (28.1) 及定理28.1提供固定六格仪器与有限来源完整闭记录唯一性；定义31.3及定理31.4提供全包含边与整条来源提升；定义36.9规定完整记忆合同；引理36.16、定理36.17、定理36.22—36.23、引理36.24、定理36.25和36.27提供已证宽度、相干上界、裕量转移及单一转变。线性上界直接使用定理33.13。本章只新增固定有限族的几何和精确终尾桥接，不重构这些图或解码器。

### 39.1 固定仪器、合法返回族与观察时序

**定义 39.1.1（来源与拥有端点的观察区间）。** 置

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad \mathbb F=\mathbb Q(t),\qquad
\lambda=\frac{t^2}{10},
$$

$$
I_0=X=[-1,\phi],\qquad I_1=[-1,t],\qquad 0<g<1.
$$

窗口标签为 $\Lambda=\{3,0,5,2,25\}$，其中 $0$ 表示空窗，$25$ 是一个三位窗口标签。实际 guard 边与平移量为

$$
\begin{gathered}
0\to0:3,0,2;\qquad 0\to1:5,25;\qquad
1\to0:3,0;\qquad 1\to1:5,\\
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t),\qquad f_\ell(x)=\Delta_\ell-gx.
\end{gathered}
$$

沿用定义14.5的状态地址域 $A_s$，$A_0=\Omega$，$D_s\subset A_s$ 为最终空尾地址，$D=D_0$。两个 guard 使用同一个级数编码 $\kappa_s$。对合法词 $w=w_0\cdots w_{r-1}$，前接映射的次序始终是

$$
f_w=f_{w_0}\circ\cdots\circ f_{w_{r-1}},\qquad
f_\varnothing=\mathrm{id},\qquad f_w(x)=A_w+(-g)^r x.
$$

定理17.2给出 $\kappa_s(A_s)=I_s$ 及合法前接等式。定理14.7给出每个固定 guard、每个标量的完成地址纤维至多为二；每个双编码均在有限前缀后使用命题14.6的非空周期极值尾。因此 $\kappa_s$ 在 $D_s$ 上单射。空尾 $0^\infty$ 从两种 guard 都合法且编码为零。给任一 $\xi\in A_s$ 保留前 $m$ 个窗口，再接 $0^\infty$，所得地址在 $D_s$ 中；若原终端标量为 $x_m$，截断误差为 $(-g)^m x_m$，绝对值至多 $\phi g^m$。故 $\kappa_s(D_s)$ 在 $I_s$ 中稠密。这个密度是 guard 区间中的密度，不预设任何返回吸引子中有稠密的有限尾。

固定式 (28.1) 的六个颜色格，并固定一次合法切点归属。记五个切点为

$$
q_1=-t^2-\lambda,\quad q_2=g-3\lambda,\quad
q_3=t-5\lambda,\quad q_4=2t-7\lambda,\quad
q_5=2t+\lambda.
$$

实际格为 $C_i=Q^{-1}(i)$，$i=0,\ldots,5$；其闭包依次为

$$
J_0=[-1,q_1],\quad J_1=[q_1,q_2],\quad
J_2=[q_2,q_3],\quad J_3=[q_3,q_4],\quad
J_4=[q_4,q_5],\quad J_5=[q_5,\phi].
$$

这些端点属于 $\mathbb F$，六个闭包均有正长度。颜色标签、来源标签和 guard 是三种不同的对象。实际取得按同一个 $Q$ 计算

$$
r_j=Q\!\left(\operatorname{clip}_X(x_j+e_j)\right),\qquad
x_j=\Delta_{\sigma_j}-gx_{j+1}.
$$

闭预算 $c\ge0$ 要求每个 $|e_j|\le c$。定义

$$
E_i^c=\{x\in X:\operatorname{dist}(x,J_i)\le c\},\qquad
O_i^c=\{x\in X:\exists y\in C_i, |x-y|\le c\}.
$$

$E_i^c$ 是闭松弛区间，$O_i^c$ 是保留实际端点旗标的可取得区间。后者恰好表示含裁剪的实际颜色可取得性：裁剪非扩张且固定 $x\in X$，所以实际目标 $y$ 满足 $|y-x|\le |e|$；反向取 $e=y-x$，裁剪固定 $y$ 即可。

若 $J_i=[l_i,u_i]$，则

$$
E_i^c=[\max\{-1,l_i-c\},\min\{\phi,u_i+c\}].
$$

一个 $x\in E_i^c$ 属于 $O_i^c$，当且仅当

$$
\operatorname{dist}(x,J_i)<c
\quad\text{或}\quad
\bigl(\operatorname{dist}(x,J_i)=c
\text{ 且 }\operatorname{proj}_{J_i}(x)\in C_i\bigr).
$$

严格不等号时可在投影附近选实际格点；等号时，区间上唯一最近点必须被该格拥有。$c=0$ 时该规则直接还原 $x\in C_i$。由此包括支撑裁剪在内，始终有

$$
\overline{O_i^c}=E_i^c,\qquad
E_i^c\setminus O_i^c\subseteq\partial E_i^c.
$$

**定义 39.1.2（一对固定终尾承担的二返回族）。** 固定合法 guard $s_1,s_2$，从初始 guard 零到它们的合法入口词（stem）$P,Q$，以及共同颜色词 $h$，满足

$$
|P|=|Q|=|h|=a_0\ge0.
$$

固定两个同步三元组

$$
(U_0,V_0,W_0),\qquad(U_1,V_1,W_1),\qquad
|U_i|=|V_i|=|W_i|=L\ge1,\qquad U_0\ne U_1.
$$

每个 $U_i$ 合法地从 $s_1$ 返回 $s_1$，每个 $V_i$ 合法地从 $s_2$ 返回 $s_2$。这些是指定的来源词和颜色词，不把路径重数或不同颜色词另算作来源内容。

对所有有限二进制词 $z=z_1\cdots z_n\in\{0,1\}^*$，包括空词，要求同一对固定尾 $\xi\in A_{s_1},\eta\in A_{s_2}$ 承担

$$
\alpha_z=PU_{z_1}\cdots U_{z_n}\xi,\qquad
\beta_z=QV_{z_1}\cdots V_{z_n}\eta,\qquad
h_z=hW_{z_1}\cdots W_{z_n}.
$$

颜色在出发坐标读取。长 $M_n=a_0+nL$ 的历史只观察坐标 $0,\ldots,M_n-1$；经过这 $M_n$ 条来源边后的终端坐标未观察。两条来源分别接自己的完整未来，$\xi,\eta$ 无须有共同未来颜色记录。几何定理允许空 stems；后面的记忆结论另要求 $P\ne Q$，并以 $k<a_0$ 记其首次不同的位置。

恢复合同完全沿用定义36.9：固定确定初态、因果处理、每次取得有限计算与有限输出批次，输出有序、只追加且不可回读；全部实际 $\Omega$ 记录上安全，全部实际 $D$ 记录上每个位置最终生效，包括无限空窗补齐。所有可影响未来的可读控制、持久和临时数据、计数器、位置、时序及输出侧信息均计入完整配置。没有 End、来源支持上界或免费重放。$B^{\mathrm{worst}}_{c,\mathcal A}(N)$ 表示截至第 $N$ 次取得的最坏完整峰值。

### 39.2 两个等斜率返回的规范最小包络

**定理 39.2.1（两种符号的最小不变区间）。** 置

$$
a=(-g)^L,\qquad f_{U_i}(x)=A_{1i}+ax,\qquad
f_{V_i}(x)=A_{2i}+ax,
$$

$$
A_j^- =\min_{i=0,1}A_{ji},\qquad
A_j^+=\max_{i=0,1}A_{ji},\qquad j=1,2.
$$

则 $0<|a|<1$，这些量属于 $\mathbb F$。两个分量的规范包络 $H_j=[m_j,M_j]$ 为

$$
(m_j,M_j)=
\begin{cases}
\displaystyle\left(\frac{A_j^-}{1-a},\frac{A_j^+}{1-a}\right),&a>0,\\[6pt]
\displaystyle\left(\frac{A_j^-+aA_j^+}{1-a^2},
\frac{A_j^++aA_j^-}{1-a^2}\right),&a<0.
\end{cases}
$$

$H_j$ 是包含两映射各自像的最小非空紧区间，且 $H_j\subseteq I_{s_j}$。其端点在 $\mathbb F$ 中，由合法完成地址取得；按返回块计，端点地址的周期为一或至多二。这里的“包络”指最小不变区间，不宣称两映射吸引子填满该区间。

**证明。** 对一个分量省略下标，记极小、极大平移映射为 $G^-,G^+$。若 $a>0$，公式满足

$$
m=A^-+am,\qquad M=A^++aM.
$$

每个映射保持顺序，其端点像位于这两个界之间，所以 $G_i([m,M])\subseteq[m,M]$。若 $a<0$，公式满足

$$
m=A^-+aM,\qquad M=A^++am.
$$

映射颠倒顺序，所有下端点像不小于 $m$，所有上端点像不大于 $M$，仍得不变性。分母非零，且两式的宽度分别为

$$
M-m=\frac{A^+-A^-}{1-a}\quad(a>0),\qquad
M-m=\frac{A^+-A^-}{1+a}\quad(a<0),
$$

因此端点顺序正确，也覆盖相等平移的单点情形。

设 $J$ 是任一非空紧区间且 $G_0(J),G_1(J)\subseteq J$，取 $x\in J$。正斜率时 $(G^-)^n(x)\to m$、$(G^+)^n(x)\to M$。负斜率时

$$
(G^-\circ G^+)^n(x)\to m,\qquad
(G^+\circ G^-)^n(x)\to M,
$$

因为两个复合的斜率都是 $a^2$，并分别固定 $m,M$。所有这些点属于 $J$，闭性使 $m,M\in J$，区间性再给 $[m,M]\subseteq J$，证明最小性。合法返回使 $I_{s_j}$ 本身为两映射的不变紧区间，故 $H_j\subseteq I_{s_j}$。

正斜率的极值地址是一个极值返回块的无限重复；负斜率的极值地址交替使用极小、极大平移块。每个块返回同一 guard，故无限拼接合法。仿射递推展开的尾余项以 $|a|^n$ 趋零，所得地址确实编码上述端点。这同时证明极值取得和块周期结论，不以区间内部的填充性为前提。显式公式则给端点的域成员关系。$\square$

**推论 39.2.2（来源分支与包络退化）。** 第一包络非退化，且

$$
U_0\ne U_1\Longrightarrow m_1<M_1,\qquad
H_2\text{ 为单点}\Longleftrightarrow V_0=V_1.
$$

**证明。** 等长词的返回映射具有相同斜率；若平移也相同，在零标量处求值就给 $U_0 0^\infty$ 与 $U_1 0^\infty$ 相同的标量。这两条从同一 guard 出发的最终空尾地址合法；若词不同，其等长前缀不同，地址就不同，违反定理14.7的 $D_s$ 单射性。因此第一平移严格不同，定理39.2.1的宽度式给 $m_1<M_1$。第二分量同理：$V_0\ne V_1$ 时宽度正；$V_0=V_1$ 时两个映射相同，包络是其唯一固定点。$\square$

**命题 39.2.3（完成极值不必是有限来源）。** 在 guard 零取 $U_0=0,U_1=2,L=1$。该返回族的两个完成极值均由合法完成地址取得，但两端均无 $D_0$ 代表。

**证明。** 两者均为实际合法自返回，$a=-g$、平移分别为 $0,1$，故

$$
m=-\frac{g}{1-g^2},\qquad M=\frac1{1-g^2}.
$$

合法地址 $(0,2)^\infty$、$(2,0)^\infty$ 的级数分别为 $-g(1+g^2+\cdots)$ 与 $1+g^2+\cdots$，取得这两个值。它们都不最终为空尾。若某一标量另有最终空尾编码，就与已给的周期地址形成双编码；定理14.7却要求双编码的两侧都是有限前缀后的非空极值尾，矛盾。因而两端均无 $D_0$ 代表。这个例子只用于区分 $\Omega$ 与 $D$ 的极值载体，不指定全局转变见证。$\square$

### 39.3 全部后缀与一个有限族的最小闭预算

**定义 39.3.1（完整端点证书）。** 对词 $w$，以 $w[r:]$ 表示从位置 $r$ 开始的后缀。保留下列所有带索引的区间／颜色条目，值相同的条目也不删除：

$$
\begin{array}{ll}
(f_{P[r:]}(H_1),h_r),\quad(f_{Q[r:]}(H_2),h_r),
&0\le r<a_0,\\
(f_{U_i[r:]}(H_1),(W_i)_r),\quad
(f_{V_i[r:]}(H_2),(W_i)_r),
&i=0,1,\quad 0\le r<L.
\end{array}
$$

记这张带索引清单为 $\mathscr L$，其长度恰为 $2a_0+4L$。空 stems 使前两类为空，但 $L\ge1$ 保证清单非空。若 $H=[l,u]$，定义

$$
d(H,J_i)=\max\{\operatorname{dist}(l,J_i),
\operatorname{dist}(u,J_i)\},\qquad
\theta=\max_{(H,i)\in\mathscr L}d(H,J_i).
$$

**定理 39.3.2（固定终尾、全部有限词的最小闭预算）。** $\theta\in\mathbb F$ 且 $\theta\ge0$。存在一对固定合法完成尾使定义39.1.2的每个有限历史满足闭约束，当且仅当闭预算 $c\ge\theta$。特别地，在 $\theta$，每一对终端标量位于 $H_1,H_2$ 的合法尾都同时实现整个族的闭约束。尾可以不在这些包络内，但这不会使预算低于 $\theta$。

**证明。** 各后缀是域内仿射映射，像区间的两端属于 $\mathbb F$；斜率为负时交换端点次序即可。对 $J_i=[l_i,u_i]$，

$$
\operatorname{dist}(x,J_i)=\max\{l_i-x,0,x-u_i\}.
$$

有限个域元素的最大值仍是其中一个域元素，故 $\theta\in\mathbb F$。距离到闭区间为凸函数；在一个紧区间上的最大值恰等于两个端点距离的最大值。

先证充分性。在每个 $H_j$ 选一个点，并由定理17.2选一条编码它的合法尾，固定后不随 $n,z$ 改变。每个剩余返回复合把 $H_j$ 送进 $H_j$。某个 stem 坐标因此属于相应 stem 后缀的像区间；某个返回块内部坐标属于该返回后缀的像区间。清单包括两分量、两种返回和每一个出发位置，所以最大距离不超过 $\theta$，所有指定闭约束同时成立。空二进制词时没有返回，直接测试全部 stem 坐标；$M_n=0$ 时没有观察，亦包含于这个结论。

再证必要性。设同一对固定尾的标量 $x_1,x_2$ 在预算 $c$ 下满足所有有限词的闭约束。按定理39.2.1，对一个分量和一个所需端点，选重复极值块或交替极值块的有限选择词 $z^{(m)}$，使对应返回复合作用于该 $x_j$ 后趋于 $m_j$ 或 $M_j$。这不要求 $x_j\in H_j$；收缩仍给同一极限。

要测试 $(f_{P[r:]}(H_1),h_r)$，把 $z^{(m)}$ 接在 $P$ 后，固定被测 stem 位置的颜色为 $h_r$。对应坐标趋于 $f_{P[r:]}(m_1)$ 或 $f_{P[r:]}(M_1)$；它们的每个有限近似都在闭区间 $E_{h_r}^c$ 内，故两个极限也在内。$Q$ 的条目同理。要测试某个 $U_i[r:]$，选择词先取 $i$，其后接极值选择词；该第一个返回块的位置 $r$ 始终观察 $(W_i)_r$，坐标极限给 $f_{U_i[r:]}(m_1)$ 和 $f_{U_i[r:]}(M_1)$。$V_i$ 的每个条目同理。

这逐一证明清单的每个端点距离至多 $c$，所以 $\theta\le c$。不同分量、不同端点可以使用不同的选择词：约束对每个有限二进制词都是全称命题，必要性只逐项取极限，不要求边际极值由同一无限选择序列联合取得。充分性已对同一对尾和同一有限词证明联合满足，因而没有独立拼接不同来源坐标。$\square$

这是一个已指定族的有限符号证书。删掉 stems 会漏掉空选择词及其约束；只检查返回起点会漏掉真正观察的块内坐标。$\theta$ 的最小性是闭关系中的取得，不自动宣称在固定端点归属下全部颜色实际可取得，也不宣称它等于 $R$。

### 39.4 非退化包络的直接内部转移

**定理 39.4.1（一个内部终点消除全部待检查归属障碍）。** 若 $H_j$ 非退化，则任一合法尾，只要其标量 $x\in\operatorname{int}H_j$，就在预算 $\theta$ 下实际取得该分量的每个有限历史的所有指定颜色。同一尾可固定用于所有长度和选择词。这样的尾可选在 $D_{s_j}$ 中。

**证明。** 固定任意有限选择词、任意被观察坐标及其指定色 $i$。从终端到这个坐标的完整来源后缀映射记为 $G$；它包括所需 stem 或返回后缀和此后全部返回，斜率是非零的 $(-g)^{M_n-r}$。定理39.3.2的充分性对整个 $H_j$ 给

$$
G(H_j)\subseteq E_i^\theta.
$$

$G$ 单射，所以 $G(H_j)$ 是非退化闭子区间，且

$$
G(\operatorname{int}H_j)=\operatorname{int}G(H_j).
$$

一个严格位于 $G(H_j)$ 两个端点之间的点，也严格位于 $E_i^\theta$ 的两个端点之间；而 $E_i^\theta\setminus O_i^\theta$ 只可能是其端点。因此

$$
G(\operatorname{int}H_j)
\subseteq O_i^\theta.
$$

这对每个有限 $G$ 都成立，选择同一内部 $x$ 后不再依赖历史。由 $O_i^\theta$ 的定义，每个坐标可选一个实际格目标并取相应误差；这些目标都作用于前接该固定尾所得的同一合法来源，因而给实际颜色历史。

更明确地，若 $e\in E_i^\theta\setminus O_i^\theta$ 是未拥有的扩张端点，运输到终端的禁等式为 $G(x)=e$。在上述包含下，这个等式与 $H_j$ 的交只能位于 $\partial H_j$：内部点的像严格在子区间内部，不能是外层区间的端点。把所有历史、所有观察位置的禁等式并在一起，仍有

$$
H_j\cap\bigcup_{G,i}G^{-1}(E_i^\theta\setminus O_i^\theta)
\subseteq\{m_j,M_j\}.
$$

因此没有遗漏任何尚待检查的排除，也不需要构造另一个逆闭合端点集。$\operatorname{int}H_j$ 是 $I_{s_j}$ 中的非空开区间，定义39.1.1所证合法空尾截断密度给一个 $D_{s_j}$ 标量落在其中；固定其尾即可。$\square$

第一包络由推论39.2.2总是非退化，故在 $\theta$ 总有一条统一实际第一 $D$ 尾。如果第二包络也非退化，同样得到统一实际第二 $D$ 尾。端点本身可以可行或不可行；本定理只证明所有可能的内部排除均消失，不把两端的归属另行假定为可行。

### 39.5 单点竞争包络的完整旗标可行集

**定义 39.5.1（有限区间 $T$ 与全部迭代的可行集 $K$）。** 若 $H_2=\{y\}$，由推论39.2.2有 $V_0=V_1=:V$。记

$$
F=f_V,\qquad F(x)=y+a(x-y),\qquad 0<|a|<1.
$$

在预算 $\theta$ 定义

$$
T=I_{s_2}
\cap\bigcap_{0\le r<a_0}f_{Q[r:]}^{-1}(O_{h_r}^\theta)
\cap\bigcap_{i=0}^1\bigcap_{0\le r<L}
f_{V[r:]}^{-1}(O_{(W_i)_r}^\theta),
$$

$$
K=\{x\in I_{s_2}:F^n(x)\in T\text{ 对所有 }n\ge0\}.
$$

所有区间运算保留实际左右包含旗标：负斜率逆像交换左右，交集端点在每个有关约束均被包含时才被包含。$T$ 可以为空或为单点，其有限端点属于 $\mathbb F$。虽然 $V$ 相同，两个颜色词 $W_0,W_1$ 的全部位置仍都必须检查。若 stems 为空，对应交集为空族约束，不删除返回约束。

**定理 39.5.2（精确轨道集合与合法尾的域）。** 一个合法竞争终尾实际实现该分量的所有有限历史，当且仅当其标量位于 $K$。这个集合有完整有限描述

$$
K=
\begin{cases}
T,&a>0\text{ 且 }y\in\overline T,\\
\varnothing,&a>0\text{ 且 }y\notin\overline T,\\
T\cap F^{-1}(T),&a<0.
\end{cases}
$$

因此

$$
K\ne\varnothing\Longleftrightarrow
\begin{cases}
T\ne\varnothing\text{ 且 }y\in\overline T,&a>0,\\
y\in T,&a<0.
\end{cases}
$$

对允许竞争终尾在整个 $I_{s_2}$ 中选择的族，这就是固定实际竞争尾的充要条件。如果另要求终端标量在指定原图返回片 $P_2$ 内，条件是 $K\cap P_2\ne\varnothing$；特别地，$P_2=\{y\}$ 时，两种符号都要求 $y\in T$。

**证明。** 先证轨道等价。由于全部竞争返回都为 $V$，stem 后接 $n$ 个返回时，其坐标是 $Q$ 后缀作用于 $F^n(x)$。一个选定返回块后接 $n$ 个剩余返回时，其位置 $r$ 的坐标是 $f_{V[r:]}(F^n(x))$，颜色仍随这个选定块为 $W_0$ 或 $W_1$。每个 $n\ge0$、每个选定色词、每个 suffix 都在族中出现，所有这些颜色实际可取得恰为 $F^n(x)\in T$ 对每个 $n$ 成立。反向，族的每个被观察坐标都属于这两种形式。$n=0$ 测试空选择词的 stems 和最后一个被观察返回块；未观察的终端坐标没有另加一个颜色约束。合法返回本身保持 guard 区间，故这些是同一实际来源上的合法坐标。

若 $0<a<1$，

$$
F^n(x)=y+a^n(x-y)\longrightarrow y.
$$

一条轨道全部在 $T$ 中，必有 $x\in T$ 且 $y\in\overline T$。反向，设这两个条件成立。$x=y$ 时轨道恒定且在 $T$；$x\ne y$ 时，每个正次迭代严格位于 $x$ 与 $y$ 之间。区间 $T$ 含 $x$，闭包含 $y$，所以包含所有这样的中间点，即使 $y$ 自身是不被包含的端点。严格夹点的包含也可直接由选一个比该点更靠近 $y$ 的 $T$ 点再用区间性得到。因此可行集为 $T$。若 $y\notin\overline T$，收敛性排除每一条轨道，得空集。

若 $-1<a<0$，必要性显然要求 $x,F(x)\in T$。这两个点不同的时候位于 $y$ 两侧，并且 $y$ 严格在它们之间。它们相同的时候只能是 $x=y$。若两点均在区间 $T$，连同端点的整个闭线段 $[\min\{x,F(x)\},\max\{x,F(x)\}]$ 都在 $T$ 内。后续迭代交替在 $y$ 两侧，离 $y$ 的距离每次乘 $|a|$，每个点均在这条线段内，故前两次成员条件已经充分。这证明 $K=T\cap F^{-1}(T)$。非恒定的两个成员点迫使夹在其中的 $y\in T$，恒定点也要求 $y\in T$；反之 $y\in T$ 直接给恒定可行轨道，证明非空判据。

空 $T$ 的闭包仍为空，所有行均给空 $K$。若 $T=\{q\}$，可行轨道只能恒定，所以只有 $q=y$ 可行；这也由上述公式直接得到。端点开闭已经被 $T$ 与 $F^{-1}(T)$ 的旗标完整保留，不能用其闭包替代实际成员关系。

最后，由定理17.2，每个选定 $x\in K$ 都有从 $s_2$ 出发的合法完成尾。选一条后固定，所有前接坐标只依赖这个标量；轨道等价保证它服务整个有限族。竞争方只承担 $\Omega$ 安全义务，无须落在 $D_{s_2}$。另加终端片限制时，选择点存在恰为 $K\cap P_2\ne\varnothing$。若 $P_2$ 是这些返回的原图片，全包含提升还给 $F(P_2)\subseteq P_2$ 及整条前缀在相应原图片中；故固定点在 $P_2$ 的选择满足该额外路径限制。不能把这一片限制暗加到无限制族。$\square$

**命题 39.5.3（正斜率允许趋近未拥有极限）。** 合法两空窗返回的映射为 $F(x)=g^2x$，固定点 $y=0$。仅作为仿射轨道说明，取 $T=(0,1]$。正斜率映射的每条始于 $T$ 的轨道在每个有限次迭代后仍属于 $T$，但固定点不属于 $T$。负斜率映射 $F(x)=-gx$ 与同一个 $T$ 则无可行轨道。若另把终尾限制在 $\{0\}$，正斜率例也失败。这不声称该特定 $T$ 已由实际六格族在某个最小亚临界预算实现；它只说明闭极限成员与实际轨道成员为何必须分开。

**证明。** $F^n(x)=g^{2n}x\in T$ 对每个 $x\in T$、每个有限 $n$ 都成立，虽然 $0\notin T$。负斜率映射第一步就变号，故在同一个区间中无可行轨道；若终尾被限制在固定点，该点又不属于这个区间，故正斜率例也失败。$\square$

结合定理39.4.1，第一 $D$ 尾总存在；非退化竞争包络也有固定 $D$ 尾，单点竞争包络则恰按本节选择固定 $\Omega$ 尾。这给本族在 $\theta$ 的统一实际尾存在性。单点判据失败只排除这个指定的来源／颜色族及所声明的片限制，不排除其他族、其他颜色选择或其他记忆下界机制。

### 39.6 不相干第一来源的闭 SCC 不会被困在单点

**命题 39.6.1（单点传播和四地址矛盾）。** 考虑定义31.3的全包含闭图片对及其有限配对图，所有路径具有定理31.4的任意合法终尾整条提升性质。在一个含环 SCC 中，若某顶点的第一来源片为单点，则整个 SCC 的第一来源片都为单点，并且第一来源投影的返回相干。因而第一来源返回不相干的 SCC 在每个顶点都有非退化第一片。

**证明。** 对第一来源的一条边，原片 $P$ 与目标片 $P'$ 满足

$$
P'\subseteq f_\ell^{-1}(P).
$$

$f_\ell$ 单射；$P$ 为单点时，其逆像为单点，非空 $P'$ 只能为单点。沿路径传播，再由强连通性达到整个 SCC。

如果第一来源返回不相干，按照定理36.22的同步定义，有同基点的两个非空返回，重复到共同正长度 $L$ 后第一来源词 $U_0,U_1$ 不同。该基点第一片记为 $\{x\}$，guard 为 $s$。由状态相对满像，选一条从 $s$ 出发编码 $x$ 的合法尾 $\tau$。在第二片也选一条合法尾；对四条实际配对路径都用这一对终尾整条提升。其第一来源给出

$$
U_0U_0\tau,\qquad U_0U_1\tau,\qquad
U_1U_0\tau,\qquad U_1U_1\tau.
$$

每条路径从同一基点到同一基点，终尾标量为 $x$，整条提升把首标量放回 $\{x\}$。四条地址都从 guard $s$ 出发、编码 $x$；由于块长相同且 $U_0\ne U_1$，其前 $2L$ 标签两两不同。定理14.7却只允许同 guard 同标量至多两个完成地址，矛盾。故所有第一来源返回相干。$\square$

这排除了“真正分支的第一来源完全落在无有限尾单点”这一障碍。结论不使非分支竞争片非退化；竞争单点仍须按定理39.5.2检查。四地址论证需要整条路径的共同来源提升，只有逐边独立的点态兼容性不能支持它。完整候选宽度已由引理36.16证明，宽度界也不能替代这里的纤维矛盾，更不能单独推出词存储为对数阶。

### 39.7 精确预算上的共同第一未来与配置下界

**定理 39.7.1（固定第一 $D$ 尾、竞争 $\Omega$ 尾的同预算计数）。** 假设 $\theta<\lambda$，stems $P,Q$ 不同，首次不同位置为 $k<a_0$，并且本族存在定理39.5.2所要求的固定竞争尾：第二包络非退化，或其单点可行判据成功；如附加原图片限制，则相应交集判据也成功。对每个符合定义36.9的解码器 $\mathcal A$，有

$$
\#\{\text{处理完 }h_z\text{ 的完整配置}:z\in\{0,1\}^n\}
\ge\frac{2^n}{k+1},
$$

$$
B^{\mathrm{worst}}_{\theta,\mathcal A}(N)
\ge\left\lfloor\frac{N-a_0}{L}\right\rfloor-O(1)
\qquad(N\ge a_0).
$$

与定理33.13合并，在这个指定预算 $\theta$ 的最优最坏完整记忆为 $\Theta(N+1)$。

**证明。** 固定定理39.4.1的第一尾 $\xi\in D_{s_1}$，固定成功判据供应的第二尾 $\eta\in A_{s_2}$。对每个 $n,z$，$\alpha_z\in D$、$\beta_z\in\Omega$ 都实际取得 $h_z$，预算正是 $\theta$。在恰好 $M_n=a_0+nL$ 次出发取得后，终端坐标未观察；分别接两条尾的零误差完整记录，得到

$$
h_zS_\xi\text{ 为 }\alpha_z\text{ 的实际记录},\qquad
h_zS_\eta\text{ 为 }\beta_z\text{ 的实际记录}.
$$

$S_\xi$ 对全部 $n,z$ 是同一个字面未来。$S_\eta$ 可以不同于 $S_\xi$；竞争来源只用于在共同过去上的安全限制，不要求它接第一未来。

固定 $n$ 的 $2^n$ 条第一来源两两不同，因为同步块 $U_0,U_1$ 等长且不同。如果两个 $h_z$ 相同，这两条不同的 $D$ 来源会共享完整实际记录 $h_zS_\xi$。预算 $\theta<\lambda$ 的记录满足临界闭关系，定理28.1的唯一性排除它。因此这些取得历史也两两不同；来源分支不是一个未经证明的颜色分支假设。

对每个共同过去 $h_z$，安全性同时适用于第一、第二来源的实际延续。两来源的 stems 在位置 $k$ 首次不同，所以已经写出的词 $o_z$ 只能是它们共同前 $k$ 标签的一个前缀，至多有 $k+1$ 种可能。记取得阶段全部有限处理结束后的完整配置为 $c_z$。若不同 $z,z'$ 的 $(c_z,o_z)$ 相同，随后给同一个未来 $S_\xi$，确定性和完整配置的定义使全部未来输出相同；此前输出也相同。这会使两个不同 $D$ 来源的完整有序输出相同，违反逐位置生效及安全性。于是 $(c_z,o_z)$ 有 $2^n$ 种，配置至少有 $2^n/(k+1)$ 种。

写出词只作有限种联合计数，不成为免费可读存储；能影响未来的输出位置、时序和输出侧状态已经在 $c_z$ 内。定义36.9的二进制配置容量给

$$
B^{\mathrm{worst}}_{\theta,\mathcal A}(M_n)
\ge n-O(1).
$$

取 $n=\lfloor(N-a_0)/L\rfloor$，用截至取得 $N$ 次的最坏峰值不减性，得所述下界。见证是实际有限来源记录，可以随 $N$ 改变。定理33.13的一个固定临界解码器也适用于每个较小实际预算，给匹配线性上界；这里的最优阶数不对任意低效解码器宣称上界。$\square$

本证明直接给混合尾所需的固定未来计数，使用已发布唯一性和解码器存在性，无须另假定竞争方有限或两方未来相同。若竞争判据失败，不能应用本定理；该失败本身也不给对数上界，后者仍须完整候选结构满足已证上界条件。

### 39.8 从 $\theta$ 出发的显式正裕量转移

**定理 39.8.1（所有 $\theta<\nu<\lambda$ 的固定有限尾见证）。** 假设定义39.1.2的 stems 不同、$k<a_0$，且 $\theta<\lambda$。对每个固定实预算 $\theta<\nu<\lambda$，这个闭族供应一对固定合法 $D$ 终尾及其实际共同过去，迫使每个合法解码器满足

$$
B^{\mathrm{worst}}_{\nu,\mathcal A}(N)
\ge\left\lfloor\frac{N-a_0}{L}\right\rfloor-O(1).
$$

最优阶数为 $\Theta(N+1)$。该结论不要求 $\theta$ 的单点竞争判据成功；几何替换部分也适用于空 stems，但空 stems 没有本下界的首次不同位置。

**证明。** 设 $\Delta=\nu-\theta>0$。从 $H_j$ 各选一个标量 $x_j$，并由满像各选一条合法完成尾 $\xi_j\in A_{s_j}$。定理39.3.2从 $\theta$ 本身供应这对固定尾的整个闭族。由合法空尾截断密度，各固定一次

$$
\widehat\xi_j\in D_{s_j},\qquad
|\widehat x_j-x_j|<\Delta/4,\qquad j=1,2.
$$

这些近似不随 $n,z$ 改变，也不必位于 $H_j$ 或原图返回片内；它们保持正确终端 guard，所有前接来源仍合法。

对长 $M_n=a_0+nL$ 的任一个历史，记原坐标与替换后坐标为 $x_{j,z,r},\widehat x_{j,z,r}$。前缀完全相同，仿射后缀给每个被观察位置 $0\le r<M_n$ 的精确等式

$$
\widehat x_{j,z,r}-x_{j,z,r}
=(-g)^{M_n-r}(\widehat x_j-x_j),\qquad
|\widehat x_{j,z,r}-x_{j,z,r}|<\Delta/4.
$$

若该位置规定颜色 $i$，闭证书给 $x_{j,z,r}\in E_i^\theta$。距离是1-Lipschitz，所以

$$
\operatorname{dist}(\widehat x_{j,z,r},J_i)
<\theta+\Delta/4.
$$

令 $D_X=\operatorname{diam}X=\phi^2$，$p_i$ 为到 $J_i$ 的投影，$c_i$ 为其中点，置

$$
\varepsilon=\frac{\Delta}{4D_X},\qquad
y_{j,z,r}=(1-\varepsilon)p_i(\widehat x_{j,z,r})+\varepsilon c_i.
$$

由 $0<\Delta<\lambda<D_X$，有 $0<\varepsilon<1$。每个格正长度，故 $y_{j,z,r}$ 是实际格的严格内部点，归属无关，并在 $X$ 内。其对投影的位移满足

$$
|y_{j,z,r}-p_i(\widehat x_{j,z,r})|
\le\varepsilon\frac{\operatorname{diam}J_i}{2}
\le\Delta/8<\Delta/4.
$$

从而取实际误差 $e_{j,z,r}=y_{j,z,r}-\widehat x_{j,z,r}$，有

$$
|e_{j,z,r}|
\le\operatorname{dist}(\widehat x_{j,z,r},J_i)
+|y_{j,z,r}-p_i(\widehat x_{j,z,r})|
<\theta+\Delta/2<\nu.
$$

裁剪固定内部目标，因此替换后的两条合法 $D$ 来源实际取得同一规定历史 $h_z$。每个分量的所有坐标仍来自前接该固定近似尾的一条地址；目标可逐坐标选择，但不能更换来源。误差没有按历史长度累加，它始终是一个终尾差乘收缩幂，再加一次内部目标位移。

经过恰好 $M_n$ 次出发取得，分别接 $S_{\widehat\xi_1},S_{\widehat\xi_2}$ 的零误差未来。第一未来对所有 $n,z$ 相同，竞争方接自己的未来即可。完整记录的误差均有一个共同严格预算上界

$$
r_*:=\theta+\Delta/2<\nu,
$$

其后全为零。定理28.1再次使不同第一来源的 $h_z$ 不同，定理39.7.1证明中的 $(c_z,o_z)$ 计数逐句适用，仍有 $2^n/(k+1)$ 个完整配置，得到相同线性下界。定理33.13给上界。

整个构造初始化于 $\theta$，裕量是 $\nu-\theta$。若该族曾在预算 $b$ 从闭图抽出，仍允许 $\theta<\nu<b$；没有改用 $\nu-b$，也没有要求在 $\theta$ 或 $\nu$ 构造新图。替换后的轨迹离开旧片不会影响合法前接和实际目标证明。$\square$

引理36.24给同一量化转移机制，本节将它明确用于有限族的最小闭预算，并给足其初始化前提。终端坐标始终未观察，附加未来从 $S_{\widehat\xi_1}$ 首坐标开始。若另采用残余解码器的已观察终端约定，须先把那一次额外取得单独计入，并把后续未来改为 $S_{T\widehat\xi_1}$；同一终端坐标不能取得两次。

### 39.9 与转变半径比较及条件取得的界限

沿用定义36.26：对每个 $b\in\mathbb F\cap[0,\lambda)$ 取第31章的有效完整闭表示及完整闭分歧图 $\mathcal D_b$，置

$$
\mathcal B=\{b\in\mathbb F\cap[0,\lambda):
\mathcal D_b\text{ 有来源对返回不相干的可达含环 SCC}\},
\qquad R=\inf\mathcal B.
$$

定理36.27证明 $\mathcal B$ 非空、$0<R<\lambda$，并给每个实际实预算 $\nu<R$ 的 $O(\log(N+2))$ 完整上界。相干性按同步来源词判定，不按图路径或颜色词重数判定。以上是本节比较所需的已发布事实，不预设 $R\in\mathbb F$ 或下确界取得。

**定理 39.9.1（一个已抽取族的代数上证书）。** 设定义39.1.2的族从某个 $b\in\mathbb F\cap[0,\lambda)$ 的完整闭分歧图抽取：stem 从初始 guard 零的配对顶点进入返回基点并包含一次来源分歧；两个同基点返回经重复同步到 $L$，定向后 $U_0\ne U_1$；颜色为每个出发顶点的共同容许颜色。则

$$
R\le\theta\le b<\lambda.
$$

**证明。** 记返回基点的原图两片为 $P_1,P_2$。沿每条返回反向应用全包含边，得到

$$
f_{U_i}(P_1)\subseteq P_1,\qquad
f_{V_i}(P_2)\subseteq P_2.
$$

两片非空紧且为区间，定理39.2.1的最小性给 $H_j\subseteq P_j$。在每个 stem 或选定返回的出发位置，整条提升允许任一 $P_j$ 终点及任一编码它的合法尾，完整后缀像位于该位置原图片内；这整个片又位于选定颜色的 $E_i^b$。限制终点到 $H_j$ 后，清单 $\mathscr L$ 的每一条区间都位于其对应 $E_i^b$，故端点最大距离给 $\theta\le b$。这一步没有把闭颜色宣称为每种归属下的实际取得。

若 $\theta<R$，选 $\theta<\nu<R$。定理36.27的 $R<\lambda$ 使定理39.8.1可用；其从 $\theta$ 开始的固定尾构造在实际预算 $\nu$ 给每个解码器线性下界。已发布的低于 $R$ 的对数解码器却在同一合同和预算给相反上界，矛盾。因此 $R\le\theta$。本论证不先假设 $R\le\theta$，不假设跨预算图嵌套，也不要求 $\theta$ 的竞争精确判据成功。$\square$

**命题 39.9.2（同时一致有界的两种词长才给条件取得）。** 假设有预算 $b_j\in\mathcal B$、$b_j\downarrow R$，并能对每个 $j$ 选择上述闭分支见证，使分歧 stems 的长度和同步返回的长度同时满足固定界

$$
a_0\le A,\qquad 1\le L\le L_*,
$$

其中 $A,L_*$ 是与 $j$ 无关的有限整数。则有一个固定来源／颜色族的阈值 $\theta$ 满足

$$
R=\theta\in\mathbb F.
$$

**证明。** 来源标签、颜色标签和 guard 均为固定有限集。长度不超过 $A$ 的 stem 三元组 $(P,Q,h)$ 只有有限种；长度不超过 $L_*$ 的同步返回三元组对也只有有限种。包含 guard、两分量定向及颜色的完整族因此只有有限种，至少一种沿无限子序列重复。该族的 $a,A_{ji},H_j,\mathscr L$ 不随抽取图或预算改变，其 $\theta$ 固定。定理39.9.1沿此子序列给

$$
R\le\theta\le b_j\longrightarrow R,
$$

所以 $R=\theta$，域成员关系由定理39.3.2给出。$\square$

这个命题的两个一致词长界是尚未解除的假设，本章不供应 $A$ 或 $L_*$。定理36.29的有限返回长度界依赖一个固定 SCC 的顶点数，同步后的长度也随该图变化；它不一致地约束趋近 $R$ 的一列图。引理31.2和定理36.30的逐预算有限端点构造依赖该预算全部端点系数的公分母与共轭界。实数预算保持在有界区间内，既不界定这些分母，也不界定另一个嵌入中的坐标，因而不供应一致图大小或上述词长界。定理36.31的可计算有理包络同样不等于一个有限族的符号取得证书。

定理31.6把一个固定有限全路径图的极值放在 $\mathbb F$ 中，前提是接受恰为该图的全部无限路径、平移量在该域中。这里的 $R$ 是变动预算下分歧条件的下确界，尚未表示为这样一个固定图的极值。推论31.7的域外根端点障碍只能排除其指定表示，不能反向供应未知转变参数的有限图。把“每个预算有限”替换为“近转变一致有限”，或把“每族阈值在域内”替换为“所有族的下确界在域内”，都缺少命题39.9.2的实质前提。

对一个已经独立证明等于 $R$ 的具体有限族，可以再应用本章精确尾测试及其符合条件的同预算计数；若该族失败，仍须其他精确预算见证或满足自身全部前提的分类结果。本章没有确定这样的族，没有确定 $R$ 的数值、无条件域成员性、下确界取得或准确端点的记忆阶数，也没有推出不同端点归属或不同噪声合同在 $R$ 上的阶数相同。有限端点回答的是一个固定返回族的全部有限展开及其固定实际终尾；全局取得仍是另一条待证明的桥。这里的取得次数是观察合同中的离散计数，空间区间是指定标量编码的像，结论不承担物理时间或空间起源的断言。

## 39.99 追加锚
## 40. 精确闭根观察的有限全路径表示大小无统一上界

本章研究一个固定的表示任务：用原 FIB 单窗口标签、guard 与仿射映射，使全部无限初始路径的标量像恰好等于指定的闭根观察区间。先对标量像相等证明下界，再把完整来源原像的精确表示作为推论。未来无约束表示根时刻以后不再指定观察颜色；根限制必须由图及其有限初始集承担。

对每个固定开窗口 $J=(u,v)$，只要 $\rho<u<v<\lambda$，下面构造固定的合法词 $w$、有限来源 $\xi$、内点 $b_*\in J$ 及整数 $n_0\ge1$，使两两不同的预算满足

$$
b_n\in J\cap\mathbb Q(t),\qquad
b_n\longrightarrow b_*\in J,\qquad
10b_n\in\mathbb Z[t]\qquad(n\ge n_0).
$$

在每个 $b_n$，任意合法逆闭合端点集都必须在同一个固定小区间中包含至少 $n+1$ 个不同点。更强地，任何上述有限全路径图，只要其标量像恰为 $E_2^{b_n}$，其存活顶点数 $s$ 就满足

$$
\boxed{\displaystyle
s\ge\left\lceil\frac{|w|+6n}{2}\right\rceil\ge3n.}
$$

每个所构造的区间仍有有限精确表示。这里无界的是预算变化时所需的表示大小，而非同一固定预算下取得长度增长的记忆代价。

### 40.1 原单窗口来源与全路径合同

**定义 40.1（全路径 FIB 表示及其标量像）。** 置

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad \lambda=\frac{t^2}{10},\qquad
I_0=X=[-1,\phi],\qquad I_1=[-1,t].
$$

沿用定义14.5的来源域 $A_0=\Omega$、$A_1=\{\omega\in\Omega:\omega_0=0\}$。令 $D_s\subset A_s$ 为最终空尾地址，$D=D_0$。标签集为 $\Lambda=\{3,0,5,2,25\}$，其中 $0=\mathrm{null}=000$，$25=101$ 是一个窗口标签。标签与仿射数据固定为

$$
f_\ell(y)=\Delta_\ell-gy,\qquad
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t).
$$

合法边恰为

$$
0\to0:3,0,2;\qquad0\to1:5,25;\qquad
1\to0:3,0;\qquad1\to1:5.
$$

一条边对应一个三位窗口步。对合法词 $w=(\ell_0,\ldots,\ell_{m-1})$，约定 $f_w=f_{\ell_0}\circ\cdots\circ f_{\ell_{m-1}}$，故其斜率为 $(-g)^m$。删除算子 $T$ 每步删除一个这样的窗口。

一个全路径表示是顶点集、边集均有限的有向图。每个顶点带 incoming guard；有限初始集中的顶点全为 guard 零；每条边带原标签 $\ell$、原映射 $f_\ell$，并遵守上述 guard 接续。接受对象恰为从初始集出发的全部无限边路径，其标量为

$$
\pi(\ell_0\ell_1\cdots)
=\sum_{j\ge0}(-g)^j\Delta_{\ell_j}.
$$

不附加实数成员测试、Büchi 条件或外部路径筛选，不把来源相关偏移藏入初始值，也不以多窗口宏边改变计数。原标签与 guard 保证每条接受路径给出实际 $\Omega$ 地址，且 $\pi=\kappa_0$。

全部接受路径的标量集合称为图的标量像。标量像恰为 $E\subseteq X$，称为标量像意义下的精确表示。更强的完整根原像表示要求边标签地址语言恰为

$$
\{\omega\in\Omega:\kappa_0(\omega)\in E\}.
$$

两种要求的关系来自[定理17.2](https://github.com/the-omega-institute/trureturing/blob/b7e6d6b26598bea84f42ed06e830a11bd5cff1ea/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L3305)的状态相对满像 $\kappa_s(A_s)=I_s$：完整根原像相等蕴含标量像相等。主下界只使用后者。

按定义31.5剪除没有无限延续的顶点，将边及初始集限制到剩余部分；这不改变无限初始路径。令 $s$ 为剩余的存活顶点数，也可进一步剪除不可达顶点。非空标量像保证至少有一个存活初始顶点。原图允许非确定选择、平行边与多个初始顶点。

状态零的五个完整闭分支像依空间顺序为

$$
[-1,-t^2],\quad[-t^2,g],\quad[g,t],\quad[t,2t],\quad[2t,\phi].
$$

状态一只允许前三个分支，覆盖 $I_1$。分支接触点及其全部合法端点尾均保留。每条合法边 $s\xrightarrow{\ell}s'$ 的实际尾域为 $I_{s'}$，其当前域为 $f_\ell(I_{s'})$。两个状态使用同一窗口级数，故状态一地址在 $A_1\subset A_0$ 中的两个编码相同。

给定 $x\in I_s$，可逐步在当前 guard 的闭分支中选择一个包含当前坐标的分支，并取其合法逆像作为下一坐标。对所得合法标签和 guard，

$$
x=\sum_{j=0}^{N-1}(-g)^j\Delta_{\ell_j}+(-g)^Nx_N,
\qquad x_N\in I_{s_N}\subseteq X.
$$

余项趋零，证明状态相对满像。空标签从两种 guard 均合法且把下一 guard 重置为零；截断任意合法地址并接 $0^\infty$ 仍合法，原标量与截断标量之差至多 $\phi^2g^N$。因此有限来源标量在各 $I_s$ 中稠密。以下选择有限来源时使用的正是这个实际来源构造，而非任意环元素的实现性。

### 40.0 有限来源极值的算术排除

**命题 40.0（交替极值没有有限来源代表）。** 记

$$
m=-\frac{g}{1-g^2}=-\frac14,\qquad
M=\frac1{1-g^2}=\frac{3+2t}{4}.
$$

则 $m,M\notin\mathbb Z[t]$。每个 $D$ 标量都属于 $\mathbb Z[t]$，因为它是有限窗口和

$$
\sum_{j=0}^{N-1}(-g)^j\Delta_{\ell_j}
$$

（其后为零标签），而 $g$ 与所有 $\Delta_\ell$ 都在 $\mathbb Z[t]$。因此 $m$ 与 $M$ 均没有有限来源代表。

**证明。** 由 $g^2+4g=1$ 得 $1-g^2=4g$，所以 $m=-1/4$；又由 $g^{-1}=3+2t$ 得 $M=(3+2t)/4$。$t$ 无理，故 $1,t$ 在 $\mathbb Q$ 上线性无关；于是 $-1/4$ 以及系数为 $3/4,1/2$ 的 $(3+2t)/4$ 都不属于 $\mathbb Z[t]$。$D$ 地址最终为空，故其级数恰为上列有限和；$\mathbb Z[t]$ 对加法和乘法封闭，给出每个 $D$ 标量均在 $\mathbb Z[t]$。$□$

### 40.2 交替极值策略与晚位标签

**引理 40.2（带符号极值路径的定量计数）。** 定义40.1的非空表示有 $s$ 个存活顶点时，其初始总标量像的最小值、最大值均由一条确定的带符号策略路径取得。若该策略轨道的暂态长为 $k$、循环长为 $p$，则

$$
p\ge1,\qquad k+p\le2s,
\qquad k\le2s-1.
$$

**证明。** 对每个存活顶点 $v$，全部无限后续路径构成有限离散边字母表乘积中的非空闭集，因而紧致。标量级数的尾部统一趋零，所以其像 $\mathcal S_v$ 为非空紧集。记 $m_v=\min\mathcal S_v$、$M_v=\max\mathcal S_v$。全路径接受保证完整的首边分解；负斜率于是给出

$$
\begin{aligned}
\mathcal S_v&=\bigcup_{e:v\to z}
\bigl(\Delta_{\ell(e)}-g\mathcal S_z\bigr),\\
m_v&=\min_{e:v\to z}
\bigl(\Delta_{\ell(e)}-gM_z\bigr),\\
M_v&=\max_{e:v\to z}
\bigl(\Delta_{\ell(e)}-gm_z\bigr).
\end{aligned}
$$

这就是[定理31.6](https://github.com/the-omega-institute/trureturing/blob/b7e6d6b26598bea84f42ed06e830a11bd5cff1ea/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L8454)的交替极值等式。在每个 $v$ 的两个有限极值式中各固定选一条取得等号的边。带符号状态 $(v,-)$ 表示取得 $m_v$，沿所选最小边转到 $(z,+)$；$(v,+)$ 表示取得 $M_v$，沿所选最大边转到 $(z,-)$。这些选择在至多 $2s$ 个状态上定义确定转移，每步仍是一条实际图边。

初始总像为有限并 $\bigcup_{v\in V_{\rm in}}\mathcal S_v$。选一个取得所需初始极值的顶点及符号，沿上述策略前进。若 $z_j$ 是第 $j$ 个带符号状态所对应的真实极值，则

$$
z_j=\Delta_{\ell_j}-gz_{j+1},\qquad
z_0=\sum_{j=0}^{N-1}(-g)^j\Delta_{\ell_j}+(-g)^Nz_N.
$$

所有 $z_N$ 有界，故余项趋零，该无限图路径确实取得初始极值，并按全路径合同接受。确定轨道首次重复前至多经过 $2s$ 个不同状态，分成 $k$ 个暂态状态和 $p\ge1$ 个循环状态，得到 $k+p\le2s$。最小、最大相互交替是负斜率所强制的；计数须保留加倍状态集。$\square$

**引理 40.3（唯一有限来源的晚位非空标签）。** 设定义40.1的一个非空表示，其总标量像的一个极值 $e$ 有实际最终空尾地址 $\omega\in D$，且该地址在零起始位置 $j$ 带非空标签。则该表示的存活顶点数满足

$$
s\ge\left\lceil\frac{j+2}{2}\right\rceil.
$$

**证明。** [定理14.7](https://github.com/the-omega-institute/trureturing/blob/b7e6d6b26598bea84f42ed06e830a11bd5cff1ea/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L1921)分类的是固定起始状态下的全部编码纤维。两条地址若首次分歧，当前坐标必为相邻闭分支的公共端点，两个后继尾必为各自尾区间的极值。命题14.6列出的极值地址为

$$
L=(3,25)^\infty,\qquad
R=(25,3)^\infty,\qquad U=5L.
$$

它们及其有限前接均非最终空尾。因此具有实际 $D$ 地址的 $e$ 不参加任何双编码；其地址在整个 $\Omega$ 中唯一：

$$
\kappa_0^{-1}\{e\}=\{\omega\}\qquad\text{在 }\Omega\text{ 中}.
$$

这是完整纤维分类的结论，强于 $\kappa_0$ 在 $D$ 上单射；只知 $e\in\mathbb Z[t]$ 不能替代实际有限来源。

引理40.2给出的极值策略路径带合法 guard 零地址、标量为 $e$，故其标签序列必等于 $\omega$。策略的最终循环若含非空标签，该标签将无穷次出现，与最终空尾矛盾。所以全部非空标签都在暂态中，位置 $j$ 强制 $k\ge j+1$。由 $p\ge1$、$k+p\le2s$，

$$
2s\ge k+p\ge j+2,
$$

得到所述界。这里唯一的是来源地址，图内同一地址可以由多条路径承担。$\square$

### 40.3 一个固定的六周期来源邻域

固定第36.1节的六格仪器。为避免预算符号与切点混淆，记

$$
a=-t^2-\lambda,\qquad c_-=g-3\lambda,\qquad
c_+=t-5\lambda,\qquad c_3=2t-7\lambda,\qquad c_4=2t+\lambda.
$$

实际格 $C_i$ 的切点归属固定，其闭包为

$$
\begin{gathered}
J_0=[-1,a],\quad J_1=[a,c_-],\quad J_2=[c_-,c_+],\\
J_3=[c_+,c_3],\quad J_4=[c_3,c_4],\quad J_5=[c_4,\phi].
\end{gathered}
$$

各格均有正长度；闭扩张记作 $E_i^b=(J_i+[-b,b])\cap X$。实际取得仍按同一个 $Q$ 和裁剪到 $X$ 的含噪坐标定义。

置

$$
\rho=\frac{239g-44}{380},\qquad
A=(3,3,5,0,3,0),\qquad
B=(0,3,0,3,3,5),\qquad
\mathbf d=(1,0,2,1,0,2),
$$

$$
\alpha=-\frac{33+6g}{76},\qquad
\beta=\frac{8+15g}{76}.
$$

这两个词在[引理36.10](https://github.com/the-omega-institute/trureturing/blob/b7e6d6b26598bea84f42ed06e830a11bd5cff1ea/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L11215)中使用，其周期坐标及成本见[定理36.11的证明](https://github.com/the-omega-institute/trureturing/blob/b7e6d6b26598bea84f42ed06e830a11bd5cff1ea/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L11299)。其 guard 链为

$$
0\xrightarrow{3}0\xrightarrow{3}0\xrightarrow{5}1
\xrightarrow{0}0\xrightarrow{3}0\xrightarrow{0}0,
$$

$$
1\xrightarrow{0}0\xrightarrow{3}0\xrightarrow{0}0
\xrightarrow{3}0\xrightarrow{3}0\xrightarrow{5}1.
$$

$A$ 是 guard 零返回词，$B$ 是 guard 一返回词；$B$ 首标签为空，亦可从 guard 零起始，并在首步之后进入同一 guard 链。

以下表列出 $A^\infty$ 的实际周期坐标及其所需闭格距离。

| 40 周期相位 | 标签 | 坐标 $z_r$ | 颜色 $\mathbf d_r$ | 到所需闭格的距离 |
| --- | --- | --- | --- | --- |
| 40相位0 | $3$ | $-(33+6g)/76=\alpha$ | $1$ | $\rho$ |
| 40相位1 | $3$ | $-(52+5g)/76$ | $0$ | $0$ |
| 40相位2 | $5$ | $(23+14g)/76$ | $2$ | $0$ |
| 40相位3 | $0$ | $(8+15g)/76=\beta$ | $1$ | $(97-362g)/380$ |
| 40相位4 | $3$ | $-(47+8g)/76$ | $0$ | $0$ |
| 40相位5 | $0$ | $(6+9g)/76$ | $2$ | $(392g-87)/380$ |

用 $g^2+4g=1$、$t=(1+g)/2$，这六个坐标逐项满足 $z_r=f_{A_r}(z_{r+1})$，下标模六。例如

$$
f_3(z_1)=\frac{-38-38g+52g+5g^2}{76}
=-\frac{33+6g}{76}=z_0,
\qquad
f_0(z_0)=\frac{33g+6g^2}{76}
=\frac{6+9g}{76}=z_5.
$$

其余四个递推为

$$
\begin{aligned}
f_3(z_2)&=\frac{-38-38g-23g-14g^2}{76}
=-\frac{52+5g}{76}=z_1,\\
f_5(z_3)&=\frac{38-38g-8g-15g^2}{76}
=\frac{23+14g}{76}=z_2,\\
f_0(z_4)&=\frac{47g+8g^2}{76}
=\frac{8+15g}{76}=z_3,\\
f_3(z_5)&=\frac{-38-38g-6g-9g^2}{76}
=-\frac{47+8g}{76}=z_4.
\end{aligned}
$$

因此这是同一条实际周期来源的六坐标。$B$ 是 $A$ 的三位循环移位，故 $B^\infty$ 的坐标为 $z_{r+3}$；颜色词周期为三，移位后仍为 $\mathbf d$。六次复合的斜率为 $g^6$，周期固定点唯一，故

$$
f_A(x)=\alpha+g^6(x-\alpha),\qquad
f_B(y)=\beta+g^6(y-\beta).
$$

闭成本也可逐项核对。正根 $g$ 满足 $4/17<g<17/72<1/4$；这是将 $x^2+4x-1$ 代入两端并用正轴单调性所得的有理括界。它给出

$$
\begin{gathered}
-1<z_1<z_4<a,\qquad c_-<z_2<c_+,\qquad
a-z_0=\rho,\\
0<z_3-c_- =\frac{97-362g}{380}<\rho,\qquad
0<c_--z_5=\frac{392g-87}{380}<\rho.
\end{gathered}
$$

其中两个严格上界的差恰为

$$
\rho-(z_3-c_-)=\frac{601g-141}{380}>0,\qquad
\rho-(c_--z_5)=\frac{43-153g}{380}>0.
$$

还可直接检查

$$
a-z_4=\frac{26+249g}{380}>0,\qquad
z_2-c_- =\frac{172-367g}{380}>0,\qquad
c_+-z_2=\frac{43g-4}{76}>0,
$$

以及 $\lambda-\rho=(63-258g)/380>0$。表中两条周期来源到各自所需闭格的最大距离因而恰为 $\rho$。这些坐标来自固定来源，未把不同来源的逐坐标可行性拼成一条轨迹。

**引理 40.4（对整个预算窗口固定的来源邻域）。** 给定 $\rho<u<v<\lambda$，可固定选取 $\varepsilon>0$，使

$$
\rho+\varepsilon<u,\qquad
H_A=[\alpha-\varepsilon,\alpha+\varepsilon]\subset\operatorname{int}I_0,\qquad
H_B=[\beta-\varepsilon,\beta+\varepsilon]\subset\operatorname{int}I_1.
$$

两个区间分别在 $f_A,f_B$ 下不变。任取终尾标量于 $H_A\times H_B$，前接一对 $A,B$ 块时，其六个对应坐标到共同所需闭格的距离均至多 $\rho+\varepsilon$。固定每个分量的一条合法终尾后，这个性质可重复任意有限次；在每个 $b\in J$ 下，整段共同色历史均可由实际内部目标取得，误差严格小于 $b$。

**证明。** $\alpha,\beta$ 在相应 guard 区间的内部，且 $u-\rho>0$，故可选这样的 $\varepsilon$。由 $0<g^6<1$，两个以固定点为中心的区间在其返回映射下不变。

一个六窗块的第 $r$ 个出发坐标，$0\le r<6$，由其终尾标量通过长 $6-r$ 的实际后缀映射得到。该映射斜率为 $(-g)^{6-r}$。终尾相对周期标量移动至多 $\varepsilon$，该坐标移动至多 $g^{6-r}\varepsilon\le\varepsilon$。到闭格的距离为1-Lipschitz，周期表于是给出上界 $\rho+\varepsilon$。重复时，每个块的终尾仍落在同一不变区间内；各坐标由同一个分量终尾及其后缀映射承担，故整段历史联合可行。

对任意固定 $b\in J$，有 $b-(\rho+\varepsilon)>0$。每个所需闭格均非退化，可以把其最近点向相应格内部移动足够小的距离，保持误差小于 $b$。内部目标属于所有固定合法归属下的同一颜色，且在 $X$ 内，裁剪不改变目标。这样得到实际共同色历史。$\square$

该邻域支持一个固定相干的六窗配对重复。共同色余量来自同一来源的收缩扰动；它本身没有提供第二种不相干返回。

### 40.4 固定有限来源与延后的非空标签

**引理 40.5（有限来源趋近周期固定点）。** 可以固定选取一条 $\xi\in D$，使 $x=\kappa_0(\xi)\in\operatorname{int}H_A$。对所有 $j\ge0$，令

$$
y_j=f_A^j(x)=\alpha+g^{6j}(x-\alpha).
$$

这些点均为实际有限来源 $A^j\xi$ 的标量，属于同一个 $H_A$，两两不同，并从 $x$ 所在的一侧单调趋于 $\alpha$。

**证明。** 定义40.1所说明的满像与合法空尾截断给出有限来源稠密性，因此存在这样的 $\xi$。[定理16.4证明中的有限和观察](https://github.com/the-omega-institute/trureturing/blob/b7e6d6b26598bea84f42ed06e830a11bd5cff1ea/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L2812)指出 $\mathbb Z[t]=\{a+bt:a,b\in\mathbb Z\}$ 对加法、乘法封闭；有限来源标量是 $-g$ 的幂与原平移量的有限乘积和，故 $x\in\mathbb Z[t]$。另一方面

$$
\alpha=-\frac{27+12t}{76}\notin\mathbb Z[t].
$$

若它等于整数系数的 $a+bt$，基 $1,t$ 上有理系数的唯一性将强制 $a=-27/76$、$b=-12/76$，矛盾。因此 $x\ne\alpha$。

$A$ 从 guard 零返回零，故 $A^j\xi$ 为一条接缝合法的实际有限来源，复合公式给出其标量 $y_j$。返回不变性给 $y_j\in H_A$；$0<g^6<1$ 及 $x-\alpha\ne0$ 给出两两不同与单调收敛。$\square$

现在固定一条 $\eta\in A_1$，使 $\kappa_1(\eta)\in H_B$，例如取 $\eta=B^\infty$。对每个 $j$，引理40.4保证同一对完整来源 $A^j\xi,B^j\eta$ 联合实现整个历史 $\mathbf d^j$，且对所有 $b\in J$ 均有严格余量。$\xi,\eta$ 固定，只有前接块数改变。这不把不同长度见证的坐标混用，也不把有限点 $y_j$ 宣称为某个图中的回归顶点。

### 40.5 把端点定位在同一预算窗口的内部

当 $0<b<\lambda$ 时，颜色2的闭根观察区间为

$$
E_2^b=[c_--b,c_++b]\subset\operatorname{int}X.
$$

其下端严格大于 $g-4\lambda>-1$，上端严格小于 $t-4\lambda<t<\phi$。底格长度为 $c_+-c_-=t^2-2\lambda>0$，故区间非空且两个端点均未被裁掉。特别地，$(c_--v,c_--u)$ 是 $X$ 内的非空开区间。

**引理 40.6（固定的合法根定位词）。** 存在一个从 guard 零起始、在 guard 零结束的有限合法词 $w$，使

$$
f_w(\alpha)\in(c_--v,c_--u).
$$

**证明。** 在目标开区间中固定选一点 $z$。由状态零满像，取一条实际合法来源编码 $z$。令 $p_N$ 为其前 $N$ 个窗口，末 guard 为 $s_N$。整个柱 $f_{p_N}(I_{s_N})$ 包含 $z$，其直径不超过 $\phi^2g^N$。令 $N$ 足够大，使该直径小于 $z$ 到目标开区间两端的距离；整个闭柱即包含于目标区间。即使 $z$ 是自身柱的端点，这个直径论证仍成立。

在 $p_N$ 后接一个空标签，再接 $A^\infty$。空标签从任一 $s_N$ 均合法，并把末 guard 置为零，所以 $w=p_N0$ 从零到零，所接周期尾合法。新来源仍在原柱中，标量为 $f_w(\alpha)$，从而满足要求。$\square$

**命题 40.7（固定内点极限、系数分母与共轭增长）。** 固定以上 $J,H_A,\xi,w$，置 $m=|w|$，定义

$$
b_*=c_--f_w(\alpha),\qquad
b_n=c_--f_w(y_n).
$$

存在一个 $n_0\ge1$，使所有 $n\ge n_0$ 的 $b_n$ 两两不同，属于 $J\cap\mathbb Q(t)$，趋于同一个固定内点 $b_*\in J$，并满足 $10b_n\in\mathbb Z[t]$。若撇号表示非平凡共轭嵌入，则

$$
b_n'=b_*'-g^{-(m+6n)}(x'-\alpha'),\qquad |b_n'|\longrightarrow\infty.
$$

**证明。** 引理40.6给 $u<b_*<v$。$f_w$ 的斜率为 $(-g)^m$，故

$$
b_n=b_*-(-g)^m g^{6n}(x-\alpha).
$$

右侧扰动非零，绝对值严格递减至零。于是预算两两不同，趋于这个固定 $b_*$；取 $n_0$ 使扰动小于 $\min\{b_*-u,v-b_*\}$，便同时得到全部尾项属于 $J$。

端点 $f_w(y_n)$ 有字面上的实际地址

$$
wA^n\xi\in D.
$$

它属于 $\mathbb Z[t]$，而 $10c_-=10g-3t^2\in\mathbb Z[t]$，所以

$$
10b_n=10c_--10f_w(y_n)\in\mathbb Z[t].
$$

等价地 $b_n\in\frac1{10}\mathbb Z[t]\subset\mathbb Q(t)$。这里是系数公分母可取十，约分后的共同系数分母整除十；并未要求每个约分分母恰为十。

[引理31.2的共轭恒等式](https://github.com/the-omega-institute/trureturing/blob/b7e6d6b26598bea84f42ed06e830a11bd5cff1ea/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L8360)给出 $g'=-g^{-1}$，从而 $(-g)'=g^{-1}$。共轭上述精确预算式，因 $6n$ 为偶数，得到

$$
b_n'=b_*'-g^{-m}g^{-6n}(x'-\alpha').
$$

共轭为单射，$x\ne\alpha$ 意味着 $x'\ne\alpha'$；$0<g<1$ 于是强制 $|b_n'|\to\infty$。$\square$

实预算被限制在固定有界区间且系数分母受限，仍不足以统一控制另一嵌入。引理31.2的端点有限性同时使用实坐标界与共轭界；上式说明其共轭参数不会从本章两个限制自动获得统一界。下面的任意逆闭合长链还将给出独立于那一特定构造的必要性。

$w$ 只用于定位一个根端点。这里没有要求、也没有推导穿过 $w$ 的共同歧义颜色史；已证明的共同历史属于随后的固定 $A,B$ 配对。

### 40.6 任意合法逆闭合集都含增长链

**定理 40.8（被同一实际来源强制的逆端点链）。** 对 $n\ge n_0$，设 $\mathcal E_n\subseteq X$ 包含预算 $b_n$ 的观察端点，并具有以下合法逆闭合性质：每当 $s\xrightarrow{\ell}s'$ 为合法边，当前点 $z\in\mathcal E_n\cap f_\ell(I_{s'})$，则

$$
F_\ell(z)=\frac{\Delta_\ell-z}{g}\in\mathcal E_n.
$$

则

$$
\boxed{|\mathcal E_n\cap H_A|\ge n+1.}
$$

同样，若端点按 guard 分层，$\mathcal E_{n,s}\subseteq I_s$，根下端在零层且上述合法边把零层或一层的点逆送入相应下一层，则 $|\mathcal E_{n,0}\cap H_A|\ge n+1$。引理31.2的全局逆闭合性质足以满足这里的假设。

**证明。** 有效根下端为

$$
e_n=c_--b_n=f_w(y_n)=\kappa_0(wA^n\xi),
$$

故 $e_n\in\mathcal E_n$。沿这条固定实际来源，记第 $r$ 个标签、guard 和坐标为 $\ell_r,s_r,z_r$。每一步均有

$$
z_r=f_{\ell_r}(z_{r+1})\in f_{\ell_r}(I_{s_{r+1}}),\qquad
F_{\ell_r}(z_r)=z_{r+1}\in I_{s_{r+1}}.
$$

因此从 $z_0=e_n$ 出发，合法逆闭合逐步强制所有后续坐标。逆去 $w$ 的 $m$ 个标签后得到 $y_n$；再逆去一个完整 $A$ 块得到 $y_{n-1}$，随后逐块得到 $y_{n-2},\ldots,y_0$。各块之间和块内部的每一步均由同一地址提供实际下一 guard 与合法尾坐标，故不是在域外形式地使用六次逆映射。

引理40.5使这 $n+1$ 个点两两不同且全部在固定 $H_A$ 中，证明未分层断言。各 $A$ 块起点的 guard 都为零，同一个逐步论证亦证明分层断言。$\square$

这个下界适用于所有满足假设的端点闭合集，与其额外种子、共轭截断半径或端点生成方式无关。它没有把这些点置于同一强连通分量。

### 40.7 标量像下界与完整根原像

**定理 40.9（精确闭根标量像的状态下界）。** 固定命题40.7的数据。对任意 $n\ge n_0$，每个定义40.1意义下标量像恰为 $E_2^{b_n}$ 的有限全路径 FIB 表示，其存活顶点数满足

$$
\boxed{\displaystyle
s\ge\left\lceil\frac{m+6n}{2}\right\rceil\ge3n.}
$$

**证明。** 闭区间的下端未被裁剪；精确标量像相等使图的最小标量恰为 $e_n=c_--b_n$。这个数有实际有限地址 $wA^n\xi$，引理40.3所用的全 $\Omega$ 纤维唯一性因而适用。

在 $A^n$ 的最后一块中，标签 $3$ 位于零起始的相对位置 $6n-2$：最后一块的六个标签为 $3,3,5,0,3,0$，其倒数第二位为非空 $3$。加上 $w$，唯一端点地址在位置

$$
j=m+6n-2
$$

带非空标签。引理40.2选出的实际最小值策略路径必须给出这个唯一地址；其最终循环全为空，所以该非空标签在暂态中。于是

$$
k\ge m+6n-1,\qquad p\ge1,\qquad k+p\le2s.
$$

因此 $2s\ge m+6n$，取整数上整得到所述界。这些 $k,p$ 是加倍带符号策略的暂态与循环长度；原图本身无须确定，同一地址也无须只有一条图路径。$\square$

这里的必要性只使用标量像精确相等，不要求图顶点是闭片，不要求顶点端点逆闭合，也不要求全部根原像地址都出现。定理40.8是另一项独立的端点必要性，定理40.9的证明未由端点数直接推断图顶点数。

**推论 40.10（每个完整根原像有限可表而大小不一致有界）。** 每个 $n\ge n_0$ 的完整根原像

$$
\mathcal L_n=\{\omega\in\Omega:
\kappa_0(\omega)\in E_2^{b_n}\}
$$

都有未来无约束的有限全路径 FIB 表示；每个这种表示均满足定理40.9的下界。因此在任一开窗口 $J\subset(\rho,\lambda)$ 上，即使只取收敛到其固定内点 $b_*$ 的上述预算尾列，也不存在统一有限的表示大小上界。

**证明。** $b_n\in\mathbb Q(t)$，两个有效端点 $c_--b_n,c_++b_n$ 均在该域内。[推论31.7](https://github.com/the-omega-institute/trureturing/blob/b7e6d6b26598bea84f42ed06e830a11bd5cff1ea/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L8515)给出完整闭根原像的有限表示。具体地，引理31.2及定义31.3提供有限的 guard 闭片图，保留端点单点片，并只以

$$
V_{\rm in}=\{(0,P):P\subseteq E_2^{b_n}\}
$$

作根初始化；未来不再施加观察。定理31.4的共同地址提升保证每条无限初始路径都给出根在该区间中的实际地址，反过来每条这样的实际地址都有规范片路径。状态零满像使该语言的标量像恰为整个闭区间，故定理40.9适用。下界随 $n$ 发散。$\square$

主定理与存在性推论的假设强度不同：前者的状态下界已在标量像相等时成立，后者用完整语言性质证明有限可表性并继承下界。二者都把根成员关系交给图，不在路径生成之后补上隐藏的根测试。

### 40.8 从较大模型提取时必须控制大小

**命题 40.11（预算无关的提取界及已有初始集情形）。** 设较大模型 $\mathscr M_b$ 的计价大小为非负整数 $s_b$。若存在同一个与预算无关的函数 $F:\mathbb N\to\mathbb N$，使每个所考虑模型都能提取成定义40.1的全路径 FIB 表示，标量像恰为 $E_2^b$，且提取后存活顶点数至多 $F(s_b)$，则

$$
F(s_{b_n})\ge\left\lceil\frac{m+6n}{2}\right\rceil.
$$

因此模型大小 $s_{b_n}$ 也无统一有限上界。提取所需的相位、控制和接受条件消除状态均须包括在 $F$ 中。

若较大模型已经是有限原 FIB 来源图，精确根观察仅选择其已有 guard 零初始顶点的一个子集，随后未来自由，并且该选择所得标量像恰为 $E_2^b$，则可取 $F(s)=s$。

**证明。** 对提取图应用定理40.9即可得到 $F(s_{b_n})$ 的界。若 $s_{b_n}\le S$ 对所有足够大的 $n$ 成立，则提取图的大小至多

$$
\max_{0\le q\le S}F(q)<\infty,
$$

与所述增长界矛盾。这个论证无须 $F$ 单调；也可用它的有限最大值包络替换 $F$。

在已有初始集情形，只选择顶点子集，没有新增顶点；剪除死端及不可达部分还会减少数目。因此提取图大小不超过原图大小，$F(s)=s$。推论31.7的根初始化正具有这种形式。$\square$

提取界必须统一于预算。逐个预算知道转换有限，却允许转换状态数依端点无控制地增长，不足以把本章下界转移给原模型。多窗口宏边、改变的仿射数据、额外实数测试、筛选接受路径或持续未来观察要求，只有在其消除确实恢复原单窗口全路径合同且满足同一 $F$ 界时，才符合命题40.11的假设。特别地，选择已有初始集后仍保留未来颜色限制，并不自动属于 $F(s)=s$ 的自由未来情形。

### 40.9 参数复杂度、回归边界与固定预算记忆

**推论 40.12（转变附近的窗口定位与任务边界）。** [定理36.27](https://github.com/the-omega-institute/trureturing/blob/b7e6d6b26598bea84f42ed06e830a11bd5cff1ea/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L11893)给出

$$
\rho<g-\frac15<\widehat\nu\le R\le\nu_0<\lambda.
$$

因而在 $R$ 上方任意小的邻域中，都可选一个开窗口 $J$ 使推论40.10成立；在任意 $\rho<u<v<R$ 的窗口中也成立。后一窗口的每个固定预算同时具有定义36.9合同下的最优完整记忆阶数 $\Theta(\log(N+2))$。

**证明。** 任给 $h>0$，由 $\rho<R<\lambda$，可选

$$
R<u<v<\min\{R+h,\lambda\}.
$$

对这个固定 $J=(u,v)$ 应用命题40.7及推论40.10。每个这样的选择给出各自固定的 $w,\xi,b_*\in J$ 与预算列。任意 $\rho<u<v<R$ 已满足同样构造的前提；定理36.27的对数行适用于窗口中的每个固定预算。$\square$

转变附近的无界性在这里通过改变 $J$ 量化。一次选定窗口后，$b_n$ 趋于它的固定内点 $b_*$；没有把同一列改写成趋于 $R$ 的序列。若需要不用确定 $R$ 的具体值即可认证的下方窗口，可在 $(\rho,\widehat\nu)$ 中选 $J$。

本章的 $n$ 改变预算和精确闭根区间；固定预算解码器的 $N$ 则计取得长度。定理36.27对固定预算的记忆界允许常数依该预算而变，并计入控制、持久与临时工作存储、计数与时序信息。本章跨预算增长的图大小因此与每个固定预算的对数完整记忆相容，不能替代一个固定预算的流式记忆下界。

闭根目标的端点在主定理中不可删去：图的最小值恰是唯一有限来源 $wA^n\xi$ 的标量，晚位非空标签才强制长暂态。有限全路径空间紧致、编码连续，亦保证该最小值取得。若改为某种实际归属规定的精确半开根集合，就改变了这个目标；紧致全路径标量像也不能自动表示非紧半开区间。在 $e_n=c_--b_n$，以恰好预算 $b_n$ 实际取得颜色2是否成立，可依赖切点 $c_-$ 的归属。闭标量像定理不借此宣称 owned color 的取得性。引理40.4的周期邻域有严格余量，内部目标的实际颜色结论独立成立。

证明隔离了一条确实受阻的路线：在某个这样的预算窗口中，先统一限制完整精确根表示或满足命题40.11提取合同的较大图之大小，再以这个大小推导后续统一界。这一路线的第一步已被定理40.9排除。结论止于这条明确的表示合同；它没有证明或反驳两条分支返回的统一 disagreement 数界 $K$。

增长由唯一端点来源的晚位标签和极值策略的暂态承担。定理40.8的链未被证明位于同一 SCC；固定 $A,B$ 邻域仅重复一个相干配对，也未从中抽出不相干返回族或无界最短分支返回。仅保留回归分支所需信息的较小充分商仍可能存在。这样的商须另行证明每次合并与返回串接保留联合标量可行性及同一实际来源；有限分隔类型本身不承担这个证明。

本章不给 $R$ 的精确值、域成员关系、算术性质、达到性或等号处记忆阶数，不把源标签时钟与仿射坐标解释成物理时空起源。结论是原 FIB 合同下的纸面数学：精确闭根表示的大小下界、任意合法逆闭合的增长链，以及满足明确统一提取条件时的后果。

## 40.99 追加锚（本行以下为增补区）

## 41. 正预算余量下的有限回返分支表示

本章固定临界六格 FIB 仪器、一个固定切点归属和出发时钟。记

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad g=t^3,\qquad \lambda=\frac{t^2}{10},
$$

$$
X=I_0=[-1,\phi],\qquad I_1=[-1,t],\qquad D_X=\operatorname{diam}X=\phi^2,
$$

$$
f_\ell(x)=\Delta_\ell-gx,\qquad
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})=(-t,0,t^2,1,2-t).
$$

来源字母表为 $\Lambda=\{3,0,5,2,25\}$，颜色字母表为 $\mathcal C=\{0,1,2,3,4,5\}$。合法 guard 边为

$$
0\to0:3,0,2;\qquad 0\to1:5,25;\qquad 1\to0:3,0;\qquad 1\to1:5.
$$

$A_s$ 是 incoming guard 为 $s$ 的完整合法来源地址，$D_s\subseteq A_s$ 是最终全为空窗的地址，且 $\Omega=A_0$、$D=D_0$。来源边在 出发时取得一个颜色；取得 $M$ 个颜色观察坐标 $0,\ldots,M-1$，坐标 $M$ 的尾端不观察。颜色格闭包记为 $J_i$，闭预算 $a$ 的扩张为

$$
E_i^a=\{x\in X:\operatorname{dist}(x,J_i)\le a\}.
$$

来源身份、guard、颜色和标量属于不同层次；同标量的不同字面来源地址始终保留。以下直接使用定理39.2.1、推论39.2.2和定理39.3.2给出的规范凸包、来源非退化性及最小闭预算；正裕量转移和与 $R$ 的比较分别沿用定理39.8.1与定理39.9.1的相应证明。

### 41.1　正余量主定理

令 $0\le b<c<\lambda$，$\Delta=c-b>0$，并置

$$
q_\Delta=\left\lceil\frac{D_X}{(1-g)\Delta}\right\rceil+1,\qquad N_\Delta=64q_\Delta^2.
$$

则存在一个至多含 $8q_\Delta$ 个单来源顶点的有限闭片表示。记 $\mathcal L_a(w)$ 为真实完整来源在预算 $a$ 下实现颜色词 $w$ 的集合，有限词只约束已取得的 出发坐标，空词不施加颜色约束；记 $\mathcal L_{\rm mesh}(w)$ 为下述完整无限网格路径语言，则对每个有限或无限 $w$ 有

$$
\mathcal L_b(w)\subseteq\mathcal L_{\rm mesh}(w)\subseteq\mathcal L_c(w).
$$

有序单来源乘积至多含 $N_\Delta$ 个成对顶点。若 $b$ 有闭分支族，则 $c$ 的成对表示有可达含环 SCC，其第一来源投影不相干；可取得两个同基点返回，未同步时每个返回的长度和分歧边数至多 $2N_\Delta-1$。同步并改根到一条来源边的末端后，有一条出发边前缀和两条等长不相干返回，返回共同长度至多

$$
2N_\Delta(2N_\Delta-1).
$$

该字族还有 $\theta\in\mathbb Q(t)$ 满足 $R\le\theta\le c$，其中 $R$ 是完整闭图不相干分支预算集合的下确界。下面证明这些断言，并始终分开网格余量 $c-b$ 与实际化余量 $\nu-\theta$。

### 41.2　重叠网格、裁剪和全包含边

取

$$
h=(1-g)\Delta,\qquad r=\frac{1+g}{2(1-g)}h=\frac{1+g}{2}\Delta,
$$

中心为

$$
a_j=-1+jh,\qquad 0\le j\le\left\lceil D_X/h\right\rceil.
$$

末中心可在 $X$ 右侧，但所有片都实际裁剪，右端覆盖不丢失；每个 $x\in X$ 距某中心至多 $h/2$。对八个合法 $(s,\ell)$ 和每个中心保留非空闭片

$$
P(s,\ell,j)=I_s\cap f_\ell(I_{s'})\cap[a_j-r,a_j+r],
$$

其中 $s\xrightarrow{\ell}s'$ 合法。顶点 $(s,\ell,j)$ 的 $s$ 是真实 incoming guard，$\ell$ 是当前出发边的来源标签装饰，不是额外观察。单点片、闭端点和同片的不同装饰全部保留，故单来源顶点不超过 $8q_\Delta$。

若 $v=(s,\ell,j)$、$w=(s',m,k)$，定义边

$$
v\xrightarrow{\ell}w
\quad\Longleftrightarrow\quad
s\xrightarrow{\ell}s'\text{ 合法且 }f_\ell(P_w)\subseteq P_v.
$$

颜色 $i$ 在 $v$ 容许，当且仅当 $P_v\subseteq E_i^c$。边使用原始 $f_\ell$，不引入宏步、重置或新系数；初态 guard 为零。

固定一条预算 $b$ 下实际满足颜色约束的完整来源，保留其真实 guard $s_j$、标签 $\ell_j$ 和坐标 $x_j$，并对每个 $x_j$ 选最近中心 $a_{k_j}$。则 $x_j\in P(s_j,\ell_j,k_j)$。对 $z\in P_{j+1}$，有

$$
\begin{aligned}
|f_{\ell_j}(z)-a_{k_j}|
&\le gr+g\frac h2+\frac h2\\
&=gr+\frac{1+g}{2}h=r.
\end{aligned}
$$

又 $f_{\ell_j}(z)\in f_{\ell_j}(I_{s_{j+1}})\subseteq I_{s_j}$，所以 guard 和下一标签的分支裁剪不会破坏包含。若 $x_j\in E_i^b$，则对任意 $z\in P_j$ 有

$$
|z-x_j|\le r+\frac h2=\Delta,\qquad
\operatorname{dist}(z,J_i)\le b+\Delta=c,
$$

故 $P_j\subseteq E_i^c$。最近中心选择沿同一来源地址完成，不能为不同观察位置另换来源；有限历史结束后仍沿同一地址选中心，只解除后续颜色约束。

### 41.3　完整无限路径语言和有限终尾提升

$\mathcal L_{\rm mesh}(w)$ 的元素必须由从 guard 零出发的一条完整无限网格路径及其字面来源词给出。若 $|w|=M<\infty$，仅在出发顶点 $v_j$、$0\le j<M$ 要求容许 $w_j$，$v_M$ 及以后不要求颜色；若 $w$ 无限，则每次出发都受约束。没有外部实数成员资格作为接受条件。

对固定无限网格路径和位置 $j$，令

$$
K_{j,N}=f_{\ell_j}\circ\cdots\circ f_{\ell_{j+N-1}}(P_{v_{j+N}}).
$$

全包含边使 $K_{j,N+1}\subseteq K_{j,N}\subseteq P_{v_j}$；它们非空紧，且 $\operatorname{diam}K_{j,N}\le g^ND_X\to0$。交集唯一，坐标满足 $x_j=f_{\ell_j}(x_{j+1})$；有界尾项消失，故它正是该完整字面来源的真实标量。片的颜色容许性遂给出 $c$-闭约束，得到

$$
\mathcal L_b(w)\subseteq\mathcal L_{\rm mesh}(w)\subseteq\mathcal L_c(w),
\qquad \mathcal L_{\rm mesh}(\varnothing)=\Omega.
$$

有限路径另有独立的语义提升：给定一条 $M$ 边有限图路径，在最终 incoming guard 的终片中取一点，再由状态相对满像取一条编码该点的合法无限终尾，前接这 $M$ 个原始标签。全包含倒推给出全部已观察坐标的颜色约束，终端坐标不观察；单点片也有这样的终尾。此终尾不必从同一装饰顶点继续：其首标签可能不同于该顶点装饰，首标签即使相同也没有逐个后继片的全包含链。因此有限提升不代替无限路径证明，也不声称一个片等于其装饰顶点所有无限标量路径的像。

端点别名为

$$
\zeta_-=(3,25)^\infty,\qquad \zeta_t=5\zeta_-,\qquad
\kappa(\zeta_-)=-1,\quad\kappa(\zeta_t)=t,
$$

且

$$
g=f_0(-1)=f_5(t).
$$

两个不同根地址 $0\zeta_-$、$5\zeta_t$ 给出同一根标量。一个 guard 零、下一标签装饰为 $0$ 且含 $g$ 的片，可在有限提升中选择第二条地址作为终尾，却不能用自己的出边装饰拼出它。故来源保持必须保留字面地址。两侧一般只是包含，闭扩张端点也不自动成为任意固定归属下的实际颜色目标。

### 41.4　成对有限历史和来源词分支

取全部有序单来源顶点对，成对顶点数至多

$$
(8q_\Delta)^2=N_\Delta.
$$

成对边由两条合法来源边和一个共同出发颜色组成，有限历史的末成对顶点不要求下一共同色。有限共同颜色词由两条各自无限的底层来源路径实现，只在已观察前缀要求共同颜色；此前缀后两条来源独立继续，未来颜色可不同。只有无限共同颜色词才在每一步要求无限共同色边路径。单来源包含证明按此约定同时保留实际来源对及其历史。

从全部 guard 零初态沿共同颜色的等标签边到首次分歧，再保留其后全部共同色可达延续，得到分歧图；分歧前历史不复制顶点，所以仍不超过 $N_\Delta$。若预算 $b$ 有闭分支族，固定其前缀、同步返回和一对终尾，并把分支分量定为第一来源。对每个二进制词 $z=z_1\cdots z_n$，网格提升给出两条各自无限来源，第一来源词含固定前缀及

$$
U_{z_1}\cdots U_{z_n},
$$

故有 $2^n$ 个不同来源词，长度随 $n$ 线性增长。

若分歧图每个含环 SCC 的第一来源投影都相干，定理36.22的来源词相位刻画及其凝聚 DAG 多幂模板论证给出有限个有界幂模板；长度不超过 $T$ 的第一来源词数只呈多项式增长，不能容纳上述指数族。因此存在可达含环 SCC，其第一来源投影不相干。这里计数的是不同字面来源词，不使用路径重数、颜色词数、标量格点数或解码候选宽度作为代理。

### 41.5　直接应用短返回测试

对该 SCC 的第一来源标签投影直接应用引理36.29的短返回测试。若 SCC 有 $s\le N_\Delta$ 个顶点，则同一基点有最短非空返回长度 $p\le s$，以及另一返回长度 $q\le2s-1$；最小公倍数同步后两条第一来源词不同。每条边只输出一个来源符号，正好满足测试假设。

未同步时，两返回长度及分歧边数均至多 $2N_\Delta-1$；同步长度为

$$
L=\operatorname{lcm}(p,q)\le pq\le s(2s-1)\le N_\Delta(2N_\Delta-1).
$$

同步保留原始 guard、共同颜色和逐边全包含关系。这是网格表示中的返回界，不是任意精确端点图的字面返回界。

### 41.6　排除全等返回并改根

先证每个可达非空返回含不同来源标签边。若某返回全部标签相同，反复它并作整条路径提升，两个分量得到相同字面周期尾和相同标量序列。把该尾接在一条可达分歧前缀后，在最后一个不同来源标签处，定义33.1的式 (33.4)—(33.7) 所列当前分支和共同闭格端点关系给出

$$
|x_{j+1}-y_{j+1}|\ge\frac{2(\lambda-c)}g>0.
$$

这个分隔只用当前共同闭色和不同当前标签，不要求下一坐标已观察，也不要求终尾属于 $D$，与相同周期尾导致的相等矛盾。故所有返回都含分歧边。

令同步返回为 $\Gamma_0,\Gamma_1$，长度均为 $L$，基点为 $q$。在 $\Gamma_0$ 选一条分歧边，写

$$
\Gamma_0=AB,
$$

其中 $A$ 以该边结束、终点为 $r$，$B:r\to q$ 可为空。在 $r$ 定义

$$
\rho_0=BABA,\qquad \rho_1=B\Gamma_1A.
$$

两者长度均为 $2L$。若 $\alpha,\beta,V$ 是 $A,B,\Gamma_1$ 的第一来源词，则新词是

$$
\beta\alpha\beta\alpha,\qquad \beta V\alpha.
$$

若相等，左右消去给出 $\alpha\beta=V$，违背原同步不相干性。故

$$
L_*=2L\le2N_\Delta(2N_\Delta-1).
$$

只取 $A$ 的最后一条分歧边作前缀，保留其来源标签 $\ell\ne m$ 和共同出发颜色。固定 $r$ 的一对合法终尾，有限提升使同一对终尾支持 $\rho_0,\rho_1$ 的所有有限拼接，包括空拼接。若该边原来从 guard 一出发，标签 $3,0,5$ 均在 guard 零行合法，下一 guard、尾域和映射不变；一次来源边和颜色已经计入，不能把它写成复制顶点或重置图。

### 41.7　规范凸包和域值阈值

把上述族写为

$$
F=(\ell,m,i_*;U_0,V_0,W_0;U_1,V_1,W_1),
$$

其中 $\ell\ne m$、$U_0\ne U_1$，三个词族长度均为 $L_*$。因 $L_*$ 偶数，

$$
a=(-g)^{L_*}=g^{L_*}\in(0,1),
$$

$$
f_{U_i}(x)=A_{1i}+ax,\qquad f_{V_i}(y)=A_{2i}+ay.
$$

令 $A_j^- =\min_i A_{ji}$、$A_j^+=\max_i A_{ji}$，[定理39.2.1](https://github.com/the-omega-institute/trureturing/blob/2df103b7b35a286abf0c12170a4694af808bb92a/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13238)给出

$$
H_j=\left[\frac{A_j^-}{1-a},\frac{A_j^+}{1-a}\right]\subseteq I_{s_j}.
$$

一般候选还允许奇数返回。完整公式是

$$
H_j=
\begin{cases}
\left[\dfrac{A_j^-}{1-a},\dfrac{A_j^+}{1-a}\right],&a>0,\\[8pt]
\left[\dfrac{A_j^-+aA_j^+}{1-a^2},\dfrac{A_j^++aA_j^-}{1-a^2}\right],&a<0.
\end{cases}
$$

由[推论39.2.2](https://github.com/the-omega-institute/trureturing/blob/2df103b7b35a286abf0c12170a4694af808bb92a/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13295)，等长的 $U_0\ne U_1$ 使仿射平移项不同、第一凸包非退化：否则同一最终空尾接在两个不同来源词后会给两个不同 $D$ 地址同一标量，违反14.7给出的标量映射在 $D$ 上的单射性。第二凸包允许为单点。

有限端点—颜色清单为

$$
(f_\ell(H_1),i_*),\qquad(f_m(H_2),i_*),
$$

$$
(f_{U_i[r:]}(H_1),(W_i)_r),\qquad
(f_{V_i[r:]}(H_2),(W_i)_r),
\quad i=0,1,\quad0\le r<L_*.
$$

对 $K=[p,q]$ 定义

$$
d(K,J_i)=\max\{\operatorname{dist}(p,J_i),\operatorname{dist}(q,J_i)\},
$$

令 $\theta$ 为该有限清单的最大代价。仿射系数、端点、距离和有限最大值均在 $\mathbb Q(t)$，故 $\theta\in\mathbb Q(t)$。[定理39.3.2](https://github.com/the-omega-institute/trureturing/blob/2df103b7b35a286abf0c12170a4694af808bb92a/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13336)保证同一对合法 $\Omega$ 终尾实现全部有限二进制拼接（含空拼接）的闭历史，并以同一对终尾给出最小性；不把两个分量分别最优的轨迹拼作联合轨迹。该定理的必要性应用于 $c$ 下已有的同一对终尾竞争族，得到

$$
0\le\theta\le c<\lambda.
$$

这里不对任意实数 $c$ 构造域端点精确图。

### 41.8　从 $\theta$ 出发的严格余量实际化

将[定理39.8.1](https://github.com/the-omega-institute/trureturing/blob/2df103b7b35a286abf0c12170a4694af808bb92a/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13526)用于上述一边前缀族。取 $\theta<\nu<\lambda$，置 $\delta=\nu-\theta>0$。从 $H_1,H_2$ 取 $x,y$，由状态相对满像取合法尾 $\xi\in A_{s_1}$、$\eta\in A_{s_2}$；单点也有合法尾。一次性选最终空尾

$$
\widehat\xi\in D_{s_1},\qquad \widehat\eta\in D_{s_2},\qquad
|\widehat x-x|<\delta/4,\quad|\widehat y-y|<\delta/4.
$$

替换尾不随二进制词和长度改变，也不必留在旧凸包或网格片内。对 $z=z_1\cdots z_n$，令

$$
\widehat\alpha_z=\ell U_{z_1}\cdots U_{z_n}\widehat\xi,\qquad
\widehat\beta_z=mV_{z_1}\cdots V_{z_n}\widehat\eta,
$$

$$
h_z=i_*W_{z_1}\cdots W_{z_n},\qquad M_n=1+nL_*.
$$

把替换尾与预算 $\theta$ 下的原尾比较，在所有 $j<M_n$ 有

$$
\widehat x_j-x_j=(-g)^{M_n-j}(\widehat x-x),\qquad
\widehat y_j-y_j=(-g)^{M_n-j}(\widehat y-y).
$$

故位移严格小于 $\delta/4$。距离到闭格为 $1$-Lipschitz；若 $p_i$ 是到 $J_i$ 的投影、$m_i$ 是格中点，取

$$
\tau=\frac{\delta}{4D_X}\in(0,1),\qquad T_i(v)=(1-\tau)p_i(v)+\tau m_i.
$$

目标在格内部且在 $X$ 内，故裁剪固定它，并有

$$
\operatorname{dist}(\widehat x_j,J_i)<\theta+\delta/4,\qquad
|T_i(\widehat x_j)-\widehat x_j|<\theta+\delta/2<\nu,
$$

第二分量同理。该严格界对所有词、长度、分量和固定归属统一成立。完成 $M_n$ 次出发 后，未观察终尾正是 $\widehat\xi$ 或 $\widehat\eta$，分别接零误差未来得

$$
h_zS_{\widehat\xi},\qquad h_zS_{\widehat\eta}.
$$

第一分量未来 $S_{\widehat\xi}$ 对所有 $z,n$ 相同；两分量未来不要求同色，也没有重复取得终端。等长 $U_0\ne U_1$ 给出 $2^n$ 个不同第一来源。临界完整记录唯一性按预算包含适用于 $\nu<\lambda$，故不同二进制词的 $h_z$ 不可相同。首标签 $\ell\ne m$ 使安全性迫使整个 $h_z$ 期间静默；若两个末配置相同，接同一第一未来将导致相同输出，违背不同 $D$ 来源的逐位置生效。因此取得 $M_n$ 次后至少有 $2^n$ 个不同完整配置，得到

$$
B^{\mathrm{worst}}_{\nu,\mathcal A}(M_n)\ge n-O(1),\qquad
B^{\mathrm{worst}}_{\nu,\mathcal A}(N)\ge
\left\lfloor\frac{N-1}{L_*}\right\rfloor-O(1).
$$

沿用[定理39.9.1](https://github.com/the-omega-institute/trureturing/blob/2df103b7b35a286abf0c12170a4694af808bb92a/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13609)证明中的正裕量反证：若 $\theta<R$，取 $\theta<\nu<R$，便与定理36.27的 $R$ 以下对数上界冲突，故

$$
R\le\theta\le c,\qquad\theta\in\mathbb Q(t).
$$

此处必须有 $\nu-\theta>0$，绝不以可能非正的 $\nu-c$ 替代；$\nu=\theta$ 不给出实际颜色结论。

### 41.9　精度给出的返回字长界

令 $\mathcal B\subseteq\mathbb Q(t)\cap[0,\lambda)$ 为存在不相干可达含环 SCC 的完整闭预算集合，$R=\inf\mathcal B$。固定有限端点最大值 $\rho_U$ 采用定义33.9的式 (33.34)。令

$$
\zeta=\frac{2t}{5},\quad z_U=\frac{23+14g}{76},\quad z_V=\frac{6+9g}{76},\quad
h=z_U-\zeta,\quad \ell_0=\zeta-z_V,
$$

$$
\chi=g^{20},\qquad \varsigma=g^{60},\qquad
\delta_H=\chi(1-\varsigma)h,\qquad \delta_L=\chi(1-\varsigma)\ell_0.
$$

取定义33.7的式 (33.25) 所定六字返回词 $U,V$ 和颜色词 $d_*$，写
$P_{U,j}=f_{U_j}\circ\cdots\circ f_{U_5}$、
$P_{V,j}=f_{V_j}\circ\cdots\circ f_{V_5}$。则

$$
\begin{aligned}
\rho_U=\max\{&\operatorname{dist}(P_{U,j}(x),J_{(d_*)_j}):
 x\in\{\zeta+\chi^2\delta_H,t^2\},\\
&\operatorname{dist}(P_{V,j}(y),J_{(d_*)_j}):
 y\in\{0,\zeta-\chi^2\delta_L\},\ 0\le j<6\}.
\end{aligned}
$$

这是固定的有限端点最大值，已知 $\rho_U<\lambda$。令

$$
R_C=\frac{\lambda+g^2t^2}{2},\qquad
\nu_0=\frac{\lambda+\max\{\rho_U,R_C\}}2.
$$

定理36.27给出 $R\le\nu_0<\lambda$。有效输入为

$$
\epsilon\in\mathbb Q(t),\qquad0<\epsilon<\lambda-\nu_0.
$$

定义

$$
Q_\epsilon=\left\lceil\frac{2D_X}{(1-g)\epsilon}\right\rceil+1,\qquad
N_\epsilon=64Q_\epsilon^2,\qquad
B(\epsilon)=2N_\epsilon(2N_\epsilon-1).
$$

在证明中若 $0<\epsilon<\lambda-R$，取 $b\in\mathcal B$ 满足
$R\le b<R+\epsilon/2$，令 $c_*=R+\epsilon$，则

$$
\Delta=c_*-b>\epsilon/2,\qquad q_\Delta\le Q_\epsilon,\qquad N_\Delta\le N_\epsilon.
$$

网格、短返回和改根给出一边前缀族，返回长度至多 $B(\epsilon)$。真实网格预算可为任意实数；这里不调用任意实预算的域端点图。域值运算只在提取出有限字后由凸包公式完成。

### 41.10　充分上界和两个零余量边界

$8q_\Delta$、$N_\Delta$、$2N_\Delta-1$ 和 $2N_\Delta(2N_\Delta-1)$ 都是充分上界，不是必要状态数、最短返回或最小分歧数下界。它们随 $\Delta\downarrow0$ 的构造阶数分别至多为 $\Delta^{-1}$、$\Delta^{-2}$、$\Delta^{-2}$ 和 $\Delta^{-4}$。

当 $\Delta=0$ 时网格尺度消失；当 $\nu-\theta=0$ 时终尾替换和内部目标没有严格余量。两项正余量结果不能取极限推出同预算结论。也不由此得到 $R$ 的精确值、域成员性、下确界取得、端点记忆阶数、统一返回界或物理时空解释。定理36.30—36.31已给出 $R$ 的有效逼近；本章新增的是精度依赖的语义字长和证书形式，不是新的可计算性或效率声明。

### 41.11　只以有效精度为输入的完整有限选择

#### 41.11.1　完整候选语法

对 $\epsilon$ 考虑所有 $1\le L\le B(\epsilon)$ 的有序元组

$$
F=(\ell,m,c;U_0,V_0,W_0;U_1,V_1,W_1).
$$

要求：

1. $\ell,m\in\Lambda$ 都从初始 guard 零合法出发，$\ell\ne m$，下一 guard 为 $s_1,s_2$，前缀颜色 $c\in\mathcal C$；
2. $U_i$ 是从 $s_1$ 回到 $s_1$ 的合法来源词，$V_i$ 是从 $s_2$ 回到 $s_2$ 的合法来源词，四者长度均为 $L$；
3. $W_i\in\mathcal C^L$；
4. $U_0\ne U_1$。

候选有序，保留两种来源分量排列；每个返回和前缀都按 出发取得颜色，终端坐标不观察。允许奇数和偶数 $L$、第二分量单点、任意颜色词；不要求 $V_0\ne V_1$ 或 $W_0\ne W_1$，不施加端点图可达性过滤，也不要求候选返回出现在预先选定的精确图中。

未经 guard 和内容筛选的候选数至多

$$
120\sum_{L=1}^{B(\epsilon)}5^{4L}6^{2L},
$$

故候选集有限；该上界只证明有限性，不给出选择所需计算量的效率界。

#### 41.11.2　正负斜率凸包和严格筛选

对语法合法 $F$ 置 $a=(-g)^L$，写

$$
 f_{U_i}(x)=A_{1i}+ax,\qquad f_{V_i}(y)=A_{2i}+ay,
$$

$A_j^- =\min_iA_{ji}$、$A_j^+=\max_iA_{ji}$，并用完整公式

$$
H_j=
\begin{cases}
\left[\dfrac{A_j^-}{1-a},\dfrac{A_j^+}{1-a}\right],&a>0,\\[8pt]
\left[\dfrac{A_j^-+aA_j^+}{1-a^2},\dfrac{A_j^++aA_j^-}{1-a^2}\right],&a<0.
\end{cases}
$$

然后列出全部 前缀/后缀 端点区间

$$
(f_\ell(H_1),c),\quad(f_m(H_2),c),
$$

$$
(f_{U_i[r:]}(H_1),(W_i)_r),\quad
(f_{V_i[r:]}(H_2),(W_i)_r),
\quad i=0,1,\quad0\le r<L.
$$

对每项 $(K,j)$ 取端点距离最大值，全部项的最大值定义为 $\theta(F)$。因

$$
\operatorname{dist}(x,[u,v])=\max\{u-x,0,x-v\},
$$

$\theta(F)\in\mathbb Q(t)$ 且严格比较 $\theta(F)<\lambda$ 可决定。只保留

$$
\mathcal C_\epsilon=\{F:\text{语法合法且 }\theta(F)<\lambda\}.
$$

定理39.2.1和定理39.3.2给每个保留族一对固定合法终尾，支持所有有限二进制拼接（含空拼接）；单点对手和奇数返回均保留。

#### 41.11.3　每个保留候选的下界

设 $F\in\mathcal C_\epsilon$。对任意 $\theta(F)<\nu<\lambda$，第41.8节（定理39.8.1的一边前缀特例）的同一替换终尾、内部目标和共同第一未来给出线性完整记忆下界。若 $\theta(F)<R$，取 $\theta(F)<\nu<R$，便与该预算的对数上界冲突。因此

$$
R\le\theta(F)\qquad(F\in\mathcal C_\epsilon).
$$

这个证明独立于返回奇偶和第二凸包是否单点，只用 $\ell\ne m$、$U_0\ne U_1$、规范闭实现和严格正余量。

#### 41.11.4　非空性和近优候选

输入条件及 $R\le\nu_0$ 给出 $R+\epsilon<\lambda$。在正确性证明中取 $b\in\mathcal B$ 满足 $R\le b<R+\epsilon/2$，令 $c_*=R+\epsilon$。前述网格—改根构造给出语法合法 $F_*$，其长度不超过 $B(\epsilon)$ 且

$$
\theta(F_*)\le c_*=R+\epsilon<\lambda.
$$

故 $F_*\in\mathcal C_\epsilon$，候选集非空。未知 $R,b,c_*$ 只在存在性证明出现，不是候选生成、阈值计算或比较预言机的输入。

#### 41.11.5　完整最小值和证书边界

在固定有限顺序下取

$$
F_\epsilon\in\operatorname*{argmin}_{F\in\mathcal C_\epsilon}\theta(F),
\qquad\theta_\epsilon=\theta(F_\epsilon).
$$

有限性、非空性和 $\mathbb Q(t)$ 精确次序给出纸面终止性，并且

$$
R\le\theta_\epsilon\le\theta(F_*)\le R+\epsilon.
$$

返回的局部证书包括字面元组、两个 guard、两个凸包端点、全部后缀—颜色区间和端点最大值；它足以核对 $R\le\theta_\epsilon$。但是单个局部证书不能推出 $\theta_\epsilon-\epsilon\le R$；这一侧必须由完整预定候选集合的全局最小化与近优候选存在性共同承担。有限候选最小值的取得也不等于同一个族取得 $R$。

由上述有限性和最小值选择可得：每个有效输入 $\epsilon\in\mathbb Q(t)$、$0<\epsilon<\lambda-\nu_0$ 都有一个完整有限候选集，其返回长度满足

$$
L\le B(\epsilon)=2N_\epsilon(2N_\epsilon-1),
$$

并可选择阈值满足

$$
R\le\theta_\epsilon\le R+\epsilon.
$$

## 41.99 追加锚（本行以下为增补区）
## 42. 折叠边界的方向、周期与固定终尾证书

### 42.0　41.1 与 41.4 的闭合同澄清

**定义 42.0（字面终尾与分歧承诺）。** 对颜色词 $w$ 和预算 $a$，闭观察来源集合 $\mathcal L_a^{\mathrm{cl}}(w)$ 只包含字面尾 $\xi\in A_0$，并要求每一个已观察出发位置 $j<|w|$ 都满足
$$
\kappa(T^j\xi)\in E_{w_j}^{a};
$$
有限词的终点 $j=|w|$ 不观察，因而不附加颜色条件。这里的 $\xi$、其来源标签和 incoming guard 均保留为同一实际地址；闭包含关系也不等同于某个 ownership 下的实际取得集成员关系。

本章所称闭分支族，是定义 39.1.2 的已供应数据：两条等长 stems $P,Q$ 从各自初始 guard 零进入共同基点，存在固定的观察首个差异位置 $k<|P|$，并有两条等长且第一来源词不同的返回；同一对字面终尾对所有有限历史保持固定。定理 36.25 提供这一较强合同的实际化；其目标预算 $b$ 可取满足该定理严格余量条件的任意实数，41 章所用的近 $R$ 精度链调用的正是这一供应。仅有 $P=Q$ 的 unrestricted diagonal family，即使具有指数多的词，也不能凭其计数单独进入 divergence 图或冒充第一来源分歧。

因此，41.1 的 $\mathcal L_a^{\mathrm{cl}}(w)$ 不是把每个有限网格片任意拼成一个新来源，41.4 的闭分支也不是只凭共同颜色词的指数计数得到；它们都保留实际 guards、字面来源、首个观察差异、同一对固定终尾和有限端未观察的合同。

### 42.1 约定、来源合同与问题范围

本章固定实际六格 FIB 仪器、原始来源标签、incoming guards 和完整包含边规则；引用本卷钉定修订 [`cfe06a9af05aff5b3d2ffa4d478cea124842a1a3`](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md) 的已发表结果。置
$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad g^2+4g=1,\qquad
\lambda=\frac{t^2}{10}=\frac{1-g}{20}.
$$
状态区间为 $I_0=[-1,\phi]$、$I_1=[-1,t]$。来源标签及实际边为
$$
\begin{array}{c|c}
0\longrightarrow0&3,0,2\\
0\longrightarrow1&5,25\\
1\longrightarrow0&3,0\\
1\longrightarrow1&5
\end{array}
$$
并且
$$
f_\ell(x)=\Delta_\ell-gx,\qquad
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t).
\tag{42.1}
$$
五个内部切点取为
$$
(q_1,q_2,q_3,q_4,q_5)
=(-t^2-\lambda,\ g-3\lambda,\ t-5\lambda,\ 2t-7\lambda,\ 2t+\lambda),
$$
其中 $q_0=-1,q_6=\phi$，颜色格的闭包为 $J_c=[q_c,q_{c+1}]$。对预算 $0<\beta<\lambda$ 写
$$
E_c^\beta=I_0\cap[q_c-\beta,q_{c+1}+\beta].
\tag{42.2}
$$
切点归属为 $\omega\in\{L,R\}^{\{1,\ldots,5\}}$：$\omega_k=L$ 将 $q_k$ 归给颜色 $k-1$，$\omega_k=R$ 将其归给颜色 $k$；相应实际取得集为
$$
O_{c,\omega}^{\beta}
=\{x\in I_0:\exists z\in C_{c,\omega},\ |x-z|\le\beta\},
\tag{42.3}
$$
其闭包是 $E_c^\beta$。闭端点属于 $E_c^\beta$ 不等于它属于 $O_{c,\omega}^\beta$。

对合法边 $s\xrightarrow{\ell}s'$，完整图节点和边遵循
$$
P\subseteq f_\ell(I_{s'}),\qquad
P'\subseteq F_\ell(P),\qquad
F_\ell(x)=\frac{\Delta_\ell-x}{g}.
\tag{42.4}
$$
这里 $P,P'$ 是闭区间或单点。交集条件不能替代 (42.4) 的整片条件。$\Omega_s=A_s$ 表示 guard 为 $s$ 的全部合法尾，$D_s\subseteq\Omega_s$ 表示最终空尾。定理 14.7 给出每个固定 guard、每个标量在全部 $\Omega_s$ 中的编码纤维至多为二；双编码的两条地址均以非空周期极值尾结束，故一个实际 $D_s$ 标量在全部 $\Omega_s$ 中只有其唯一的 $D_s$ 编码。这不主张 $\kappa_s$ 在 $\Omega_s$ 上单射。guard 相对满像 $\kappa_s(\Omega_s)=I_s$ 和合法前接来自定理 17.2；对任一合法尾保留前 $m$ 个窗口再接 $0^\infty$，标量误差至多 $\phi g^m$，故 $\kappa_s(D_s)$ 在 $I_s$ 中稠密。这些前提与定理 31.4 的共同路径提升均在本章使用。对第 31、38 章的有限端点图，单点 $z$ 的 $D_s$-存活还要求其带 guard 单点沿合法逆边在有限步到达零，单有 $z\in\mathbb Q(t)$ 不够。

本章只处理：第二来源片为 singleton、第二来源投影相干、第一来源投影可能不相干的已供应有限实际 SCC；以及由这些 SCC 抽出的固定返回族。$\beta\in\mathbb Q(t)$ 时第 31 章供应有限闭图；对其他实预算，下述有限图结论以所需实际全包含图已另行供应为前提，不宣称它自动有限。物理时空、热力学熵、五种普遍物理操作、全局转变半径的取得或精确值，都不由下述有限条件推出。

若某个精确节点还带有有限 pending 等式集 $S$，其 live 条件为
$$
\begin{array}{c|c}
\text{域}&\text{条件}\\ \hline
\Omega&P\text{ 非退化，或 }P=\{z\},\ z\notin S,\\
D&P\text{ 非退化，或 }P=\{z\},\ z\notin S,\ z\in\kappa_s(D_s).
\end{array}
\tag{42.0}
$$
非退化片的内部标量可以同时避开有限 $S$ 并由 $D_s$ 或 $\Omega_s$ 编码；单点必须逐字检查。式 (42.0) 保留 $D$-liveness 与 $\Omega$-safety 的区别，不能把竞争方的安全尾默认为有限尾。

### 42.2 顶点、合法方向和逐颜色 tight

设有限闭配对 SCC 的顶点写成
$$
v=(s_v,P_v;r_v,\{y_v\}),
\tag{42.5}
$$
其中 $P_v$ 为第一片，$\{y_v\}$ 为第二片。定义共同闭色集合
$$
C_\beta(v)=\{c:P_v\subseteq E_c^\beta,\ y_v\in E_c^\beta\}.
\tag{42.6}
$$
第二片的相干性给每条内部边 $e:v\to w$ 一个相同的第二来源词关系 $y_v=f_{m_e}(y_w)$。若第一片在含环 SCC 的一个顶点是单点，则由 (42.4) 沿路径传播后整个 SCC 的第一片都是单点。若该 SCC 的第一来源返回词不相干，取同基点、等长且第一词不同的两个返回 $U_0,U_1$，并用同一对终尾提升四条组合
$$
U_0U_0\tau,\quad U_0U_1\tau,\quad U_1U_0\tau,\quad U_1U_1\tau.
$$
它们从同一 guard 编码同一标量，却有至少四个不同的有限标签前缀，违背定理 14.7 的至多二重编码。因此不相干第一 SCC 的每个第一片都非退化。

令
$$
B(v,c)=\operatorname{dist}(y_v,J_c)\le\beta.
\tag{42.7}
$$
当 $B(v,c)=\beta>0$ 时，外侧符号为
$$
\sigma(v,c)=
\begin{cases}
-1,&y_v=q_c-\beta,\\
+1,&y_v=q_{c+1}+\beta.
\end{cases}
\tag{42.8}
$$
方向 $\eta\in\{-1,+1\}$ 在 $v$ 合法，意为存在 $\varepsilon>0$ 使
$$
y_v+\eta a\in I_{r_v}\qquad(0\le a\le\varepsilon).
\tag{42.9}
$$
下端点只允许正方向，上端点只允许负方向，内部点允许两方向。边
$$
a:(v,\eta)\longrightarrow(w,-\eta)
\tag{42.10}
$$
保留当且仅当其原边 $e:v\to w$ 合法，选取颜色 $c\in C_\beta(v)$，且
$$
B(v,c)<\beta
\quad\text{或}\quad
\bigl(B(v,c)=\beta,\ \sigma(v,c)\eta<0\bigr).
\tag{42.11}
$$
方向翻转不是记号选择，而是实际误差运输
$$
\delta_v=-g\,\delta_w.
\tag{42.12}
$$
对这条被选颜色边定义
$$
T(a)=[B(v,c)=\beta].
\tag{42.13}
$$
顶点有另一种 tight 色，不能把选择的 slack 色边标为 $T=1$；tight 是逐边逐色的事实。

若需要未扰动周期 rival 尾本身实际 owned，给颜色边附加
$$
\kappa(a)=
\begin{cases}
\varnothing,&B(v,c)<\beta,\\
(k,R),&y_v=q_k-\beta,\ c=k,\\
(k,L),&y_v=q_k+\beta,\ c=k-1.
\end{cases}
\tag{42.14}
$$
记由 (42.11) 得到的闭方向图为 $\mathcal H_\beta$，逐边通过 (42.14) 筛选的图为 $\mathcal H_{\beta,\omega}^{\mathrm{ref}}$。闭图允许用未拥有的周期点作参考再向内扰动；reference-owned 图才要求周期点自身通过五个切点归属。

### 42.3 两旗标同步平方与精确充要条件

本节的 $\mathcal H$ 可以取闭方向图 $\mathcal H_\beta$，或固定归属的 reference-owned 图 $\mathcal H_{\beta,\omega}^{\mathrm{ref}}$；第二来源投影均继承原 SCC 的相干性。

在 $\mathcal H$ 的同步图中，状态为
$$
(u,v,d,a),\qquad d,a\in\{0,1\}.
\tag{42.15}
$$
同步走边 $e:u\to u'$、$f:v\to v'$ 时，两条颜色边各自选择其配对来源两分量的共同颜色；$e$ 与 $f$ 的所选颜色可以不同。旗标更新为
$$
d'=d\lor[\ell_1(e)\ne\ell_1(f)],\qquad
a'=a\lor T(e)\lor T(f).
\tag{42.16}
$$
其中 $d$ 只看第一来源标签，颜色标签、第二来源标签和边编号都不能代替它。

**命题 42.3（方向—tight 证书的充要条件）。** 下列三项等价：

1. $\mathcal H$ 含一个第一来源不相干的含环 SCC，且该 SCC 含一条实际选色的 tight 边；
2. 存在某个 $q$ 使
   $$
   (q,q,0,0)\leadsto(q,q,1,1);
   \tag{42.17}
   $$
3. 存在同基点、等长、非空的两个方向返回，第一来源词不同，且至少一个返回逐边访问 $T=1$ 的选色边。

**证明。** 由 1 到 2，取第一词不同的返回并在同一 SCC 内接上一条经过指定 tight 边的共同闭行走。同步两分量的方向符号始终相同；共同后缀不消除已经置一的 $d$，并使 $a=1$，得到 (42.17)。由 2 到 3，投影同步路径；两个旗标正好给出第一词差异和逐边 tight 访问。由 3 到 1，两条返回的顶点属于同一 SCC，第一词不同给出不相干，$T=1$ 边给出该 SCC 的 tight 选色边。整个论证没有把某个顶点的其他 tight 色传播给当前选色边。$\square$

设底层 SCC 顶点数为 $N$，方向副本中有 $N_+$ 个正向点、$N_-$ 个负向点。同步可达有序对只有同方向的
$$
K=N_+^2+N_-^2\le2N^2
\tag{42.18}
$$
种；加两旗标至多有 $4K\le8N^2$ 个状态。最短接受路径不重复状态，且闭返回长度为偶数，所以不带共同末边时可取
$$
L\le4K-2\le8N^2-2.
\tag{42.19}
$$

还可要求同一 disagreement 边为共同末边。因为若 SCC 内每条边的第一、第二标签都相同，第一投影会继承第二投影的相干性，所以存在
$$
b:u\longrightarrow q,\qquad \ell_1(b)\ne\ell_2(b).
\tag{42.20}
$$
在同步图中从 $(q,q,0,0)$ 走到 $(u,u,1,a)$，再同步走 $(b,b)$；要求此前已访问 tight，或令 $T(b)=1$。对该有限接受语言取最短路径，最后一边加上所得两条返回都以 $b$ 结束，长度为偶数且
$$
\boxed{L\le4K\le8N^2.}
\tag{42.21}
$$
该 $b$ 同时是合法的一边 stem：原边从 incoming guard 一合法时，从 guard 零也合法，后继 guard 与仿射映射不变。这里没有把 SCC 换成其投影，也没有交换第一、第二标签。若有五切点赋值，则同步状态再带部分赋值 $\mu$；最多 $3^5$ 种赋值，固定 $\omega$ 时删边即可使用 (42.21)，未固定 $\omega$ 时正证书长度至多 $8N^2\,3^5$。

### 42.4 返回 hull、自身预算锁与所有权

取命题 42.3 的两条返回 $D_0,D_1$，共同长度为偶数 $L$，共同末边为 $b$，基点为 $q$；$s_q,r_q$ 表示该基点原配对顶点的两个 guards。第一来源返回映射为
$$
F_i(x)=A_i+cx,\qquad c=g^L\in(0,1),
\tag{42.22}
$$
且 $A_0\ne A_1$。否则两条不同的第一词接同一个合法零尾会给同一标量，违反定理 14.7 的 $D$ 单射性。完整包含使 $F_i(P_q)\subseteq P_q$；重复极小、极大平移的返回分别收敛到 $\min(A_0,A_1)/(1-c)$ 和 $\max(A_0,A_1)/(1-c)$。$P_q$ 闭且为区间，故包含两极限及其间的整个区间。依定理 39.2.1，规范不变 hull 是非退化区间
$$
H_1=
\left[
\frac{\min(A_0,A_1)}{1-c},
\frac{\max(A_0,A_1)}{1-c}
\right]\subseteq P_q,
\qquad F_i(H_1)\subseteq H_1.
\tag{42.23}
$$
第二来源相干且基点为 singleton，两个等长返回有同一个仿射映射
$$
F_2(y)=B+cy,\qquad F_2(y_q)=y_q,
\tag{42.24}
$$
故第二 hull 为 $\{y_q\}$。

完整包含边规则把 $H_1$ 和 $\{y_q\}$ 的每个后缀送入相应的 $E_c^\beta$，并保留原 guards、来源词和所选颜色。于是固定有限二返回族的最小闭预算 $\beta_{\mathrm{fam}}$ 满足 $\beta_{\mathrm{fam}}\le\beta$。命题 42.3 中的 tight 边所选颜色在 singleton rival 上的成本恰为 $\beta$；将含该边的返回放在前面并继续任意次返回，成本沿后缀收缩因子趋近 $\beta$。若一个固定闭预算低于 $\beta$，这些历史不可能全部满足。因此
$$
\boxed{\beta_{\mathrm{fam}}=\beta.}
\tag{42.25}
$$
这里的等号来自真正被选择的 rival-tight 槽，不来自顶点上另一个未选颜色的 tight 标记。它也不意味着存在固定 $b<\beta$ 支持全部有限历史。

共同末边 $b$ 置于前面后，任意有限历史都写成
$$
bD_{z_1}\cdots D_{z_n},\qquad z\in\{0,1\}^n,
\tag{42.26}
$$
并且包括空词 $n=0$。终端坐标在最后一条出发边之后尚未观察；接上的未来从固定尾的首个观察开始。

### 42.5 同一对固定终尾的全族实际实现

第一分量先由 guard 相对的截断稠密性选择一条合法固定 $D$ 尾 $\xi$，使其标量 $x=\kappa_{s_q}(\xi)\in\operatorname{int}H_1$。第一片整片被送入闭扩张格已经足够，不能把整个原片 $P_q$ 包含在某个 $O_{c,\omega}^\beta$ 中另列为必要条件。每个来源后缀是非零斜率仿射映射，因此 $x$ 的像落在非退化可行区间内部，成本严格低于 $\beta$；实际目标可以取在 $J_c$ 内部，自动属于每一种归属下的 $O_{c,\omega}^\beta$。

在 reference-owned 图 $\mathcal H_{\beta,\omega}^{\mathrm{ref}}$ 中，固定一条合法周期 rival 尾 $\zeta$，使 $\kappa_{r_q}(\zeta)=y_q$。所有所选 tight 色已满足 (42.14)，其他色有严格余量，故
$$
(\xi,\zeta)
\tag{42.27}
$$
支持每一个有限二进制历史，且 rival 可以在等号上实际取得。这里第一尾属于 $D$，第二尾只保证属于 $\Omega$。

在只使用闭方向图时，取基点合法方向 $\eta_q$，并取充分小的 $h\ne0$ 使
$$
\operatorname{sign}h=\eta_q,\qquad y_q+h\in I_{r_q}.
\tag{42.28}
$$
两条返回和 stem 只有有限个选定槽；相干 rival 的参考值与后续返回的选择及次数无关。若有 slack 槽，将它们与 $\beta$ 的最小正间隙记为 $\Delta>0$；取
$$
|h|<\beta/2,\qquad |h|<\Delta/2.
\tag{42.29}
$$
若没有 slack 槽，第二个幅度限制为空条件，略去 $\Delta$；还须保留 (42.28) 的合法 guard 限制。

沿长度为 $M$ 的前缀，到观察位置 $j$ 的位移为
$$
u_j=(-g)^{M-j}h.
\tag{42.30}
$$
总长度为 $M=1+nL$，偶长返回使每个拼接的终端方向都是 $\eta_q$，一边 stem 的方向则是 $-\eta_q$。方向图的每一步翻转保证 $u_j$ 在每个 tight 槽朝向内侧。对选定 tight 槽，
$$
\operatorname{dist}(y_j+u_j,J_c)
=\beta-|h|g^{M-j}<\beta,
\tag{42.31}
$$
slack 槽由距离函数的 1-Lipschitz 性和 (42.29) 仍严格低于 $\beta$。于是同一对固定尾
$$
\boxed{(\xi,\zeta_h)}
\tag{42.32}
$$
支持所有 $bD_z$ 历史（包括空返回词）和每个所有权 $\omega$，其中 $\zeta_h$ 是一次固定的合法尾，标量为 $y_q+h$。还可先在上述非空单侧开区间内选一个 $D$ 标量，再以它与 $y_q$ 的差定义 $h$ 并固定其尾；不声称任意预定 $h$ 都有 $D$ 编码。因此存在同一对实际 $D/D$ literal tails，同时服务全部有限历史及每个 $\omega$。

扰动后的第二标量可能离开原 singleton 片，甚至离开旧闭图节点；这不损害实际性，因为每条坐标仍由同一固定来源词、合法 guard 和 (42.30) 的误差运输产生，目标在实际色片内。不能用“仍在旧片”替代来源词和 guard 的验证。

(42.32) 只给每条有限历史自己的严格余量。随着后续返回次数增加，(42.31) 的改善量趋于零，所以没有统一的固定 $b<\beta$。这正与 (42.25) 相容。

### 42.6 参考归属、五切点证书与全包含范围

将逐边要求 (42.14) 在同步路径上累积为部分赋值
$$
\mu:\{1,\ldots,5\}\rightharpoonup\{L,R\}.
\tag{42.33}
$$
冲突的要求拒绝该同步步；空要求不改变 $\mu$。对固定的 $\omega$，接受路径存在且 $\mu\subseteq\omega$ 当且仅当 reference-owned 方向图满足命题 42.3 的准则。所有接受路径产生的 $\mu$ 组成 $\mathscr M_{\mathrm{dir,tight}}$，故
$$
\mathcal H_{\beta,\omega}^{\mathrm{ref}}\text{ 有所需 SCC}
\iff
\exists\mu\in\mathscr M_{\mathrm{dir,tight}},\ \mu\subseteq\omega.
\tag{42.34}
$$
这同时保留了方向、第一词差异、所选 tight 色和五切点归属；不能把它拆成分别存在的三个条件。

对于较低预算的种子，需另固定一个最终周期参考，而不是把量词扩大到所有二返回词。从 (42.23) 选一个由极值返回无限重复取得的端点 $h_1$，第二检查点仍为 $y_q$；以前置 stem 和一个含 tight 的返回为有限前缀，再接这个指定极值返回的无限重复。参考前缀长为 $d$，周期长为偶数 $L$，且最早 active 观察时间为 $j_*<d$。这里 active 指两个分量中任一个的所选槽成本等于 $\beta$；未核对归属前，参考只满足闭观察关系。

在终端检查点选 $s_1\in\{-1,0,+1\}$、$s_2=\eta_q$：若第一分量有 active 槽，$s_1$ 朝 $H_1$ 内部；若没有，可取 $s_1=0$。每个第一后缀把整个 $H_1$ 送入其闭扩张格，故端点朝内的位移严格改善该分量的每个 active 槽。第二分量的改善由方向图保证。设两检查点 guard 为 $s_q,r_q$。共同等幅选择还必须有一个非空合法单侧幅度区间 $(0,\kappa_0)$，使对每个 $0<\kappa<\kappa_0$ 都有
$$
h_1+\kappa s_1\in I_{s_q},\qquad y_q+\kappa s_2\in I_{r_q},
$$
且按原来源后缀运输后，在两个分量的每个 active 槽均朝内。这个条件保留两分量的真实 guard 和全部 active 槽，不能只用 rival 符号代替。上述 hull 内侧和合法方向给出这种共同区间；若检验另一个参考，则需重新验证它非空。由 guard 相对满像，一次选定编码这两个标量的合法 $\Omega/\Omega$ 尾，并对下述全部 $n\ge0$ 固定这一对 literal tails。取同一充分小幅度 $\kappa>0$，令
$$
M_n=d+nL,\qquad
b_n=\beta-\kappa g^{M_n-j_*}.
\tag{42.35}
$$
对每个分量的每个 active 时间 $r$，成本是 $\beta-\kappa g^{M_n-r}$；最早的 $j_*$ 给出 $b_n$，更晚的 active 槽严格小于它。有限 prefix/cycle 的 slack 槽有共同正间隙；缩小 $\kappa_0$，同时使位移与 $\beta-b_n\le\kappa$ 的总影响小于该间隙，并使 $\kappa<\beta/2$，即可保证所有 $n\ge0$ 的 slack 槽也严格小于 $b_n$。无 slack 槽时这项限制为空。因此这是同一个参考前缀加 $n$ 个指定周期的闭 $b_n$ 实现。

要使它成为归属 $\omega$ 下的实际精确 $b_n$ 记录，必须同时检查两个分量在最早 active 时间 $j_*$ 的每个等号目标：低于所选格的等号要求 $\omega_k=R$，高于所选格的等号要求 $\omega_k=L$。同一时间若两个分量都 active，两项都必须加入；若所得五切点部分赋值冲突，则该精确种子失败。其他槽严格低于 $b_n$，可选内部目标；终端未观察，不增加一次等号义务。此检查与 $n$ 无关，因为它保留同一参考槽、颜色和外侧方向。reference-owned 图只保证 rival 项，不自动保证第一 hull 端点贡献的项。

以上共同幅度存在性只建立 $\Omega/\Omega$ 来源，不供应第一分量的 $D$-liveness。若要用于要求第一来源有限的恢复下界，必须另给同一等幅选择的实际有限尾见证；若要称为 $D/D$，两个分量都必须另有这种见证。两个 guard 中分别稠密的 $D$ 标量，不能保证同一个 $\kappa$ 同时命中这两个受约束的标量集合。单点的 $D$-生存仍需到零的有限合法路径，不能由 $\mathbb Q(t)$ 成员性推出。即使未扰动的 rival singleton 是 $\Omega$-only，合法共同幅度可以在 $\Omega/\Omega$ 域内存在；这不使它获得有限尾编码。此结论只针对一个固定最终周期参考及它的规定有限历史，不推出整族在某个固定 $b<\beta$ 下可行，也不把附加等号检查纳入 (42.21) 的完备长度界。

### 42.7 固定族的 A 或 B 轨道判据

固定一个共同 stem $(P,Q,h)$ 和两条等长返回
$$
(U_0,V,W_0),\qquad(U_1,V,W_1),
\quad |U_i|=|V|=L.
\tag{42.36}
$$
第一规范 hull $H_1$ 非退化，第二返回映射为
$$
F(x)=y+a(x-y),\qquad a=(-g)^L,\qquad 0<|a|<1.
\tag{42.37}
$$
沿用第 39 章的固定族合同：stems 从初始 guard 零进入指定基点，两个返回各自回到同一 guard；由完整后缀清单与 hull 端点最大成本得到该族自身最小闭预算 $\beta>0$，并有 $\beta<\lambda$。每个第一后缀将 $H_1$ 整体送入所选 $E_c^\beta$，第二参考点也满足全部闭槽。以下只是定理 39.5.2 的有限 active/slack 展开，不重新分类解码器。

列出 rival 的全部观察槽，包括 stem 后的空返回词和 stem-only 槽：
$$
\mathscr S=
\{(f_{Q[j:]},h_j):0\le j<|Q|\}
\cup
\{(f_{V[j:]},(W_i)_j):i=0,1,\ 0\le j<L\}.
\tag{42.38}
$$
相同后缀若配有不同颜色仍保留两次。对槽 $\alpha$ 写 $(G_\alpha,c_\alpha)$，并定义
$$
T_\omega=I_r\cap\bigcap_{\alpha\in\mathscr S}
G_\alpha^{-1}(O_{c_\alpha,\omega}^{\beta}),\qquad
K_\omega=\bigcap_{n\ge0}F^{-n}(T_\omega).
\tag{42.39}
$$
空返回词的槽要求 $n=0$，所以 (42.39) 没有漏掉最早观察；若 stem 为空，第一集合为空，也不添加虚构 terminal 观察。

令 $\mathscr A$ 是在周期点 $y$ 处达到 $\beta$ 的 active 槽，令 $\sigma_\alpha$ 为其下侧 $-1$ 或上侧 $+1$ 符号，$\gamma_\alpha=G_\alpha'$。定义
$$
\mathrm A:\quad y\in T_\omega,
\tag{42.40}
$$
即周期参考自身的每个等号槽均满足实际归属；严格 slack 槽自动满足。定义
$$
\mathrm B:\quad a>0,\quad
\exists\eta\in\{-1,+1\},\ \exists\varepsilon>0:
\begin{cases}
y+\eta u\in I_r\ (0\le u\le\varepsilon),\\
\sigma_\alpha\gamma_\alpha\eta<0\quad(\alpha\in\mathscr A).
\end{cases}
\tag{42.41}
$$
这是同一个合法 guard 方向改善全部 active 槽；不能只检查未 owned 的 active 槽。

**定理 42.7（固定族的 A 或 B）。**
$$
\boxed{K_\omega\ne\varnothing\iff \mathrm A\ \lor\ \mathrm B.}
\tag{42.42}
$$

**证明。** 第一分量取 $\operatorname{int}H_1$ 的固定 $D$ 尾，所有后缀将 $H_1$ 送入对应闭扩张格，故只需检查第二分量。若 A 成立，固定编码周期点 $y$ 的合法周期尾；$F(y)=y$，每个槽的像落在对应实际取得集，故整个有限族可行。若 B 成立，取小的 $u>0$ 并令 $x=y+\eta u$。active 槽满足
$$
\operatorname{dist}(G_\alpha(y+\eta v),J_{c_\alpha})
=\beta+\sigma_\alpha\gamma_\alpha\eta v<\beta
\quad(0<v\le u),
\tag{42.43}
$$
slack 槽由有限正间隙保持严格可行。因 $a>0$，
$$
F^n(x)=y+\eta a^n u,
\tag{42.44}
$$
全部迭代留在同一单侧区间，因此一条固定合法尾支持每个有限词，包括空词。

反设 $K_\omega\ne\varnothing$ 且 A 失败，取 $x\in K_\omega$，则 $x\ne y$；若 $a<0$，$x$ 与 $F(x)$ 在 $y$ 两侧，而二者均在 $T_\omega$，凸性迫使 $y\in T_\omega$，矛盾。因此 $a>0$。对任一 active 槽，闭可行性给
$$
\sigma_\alpha\gamma_\alpha(x-y)\le0.
\tag{42.45}
$$
因为 $\gamma_\alpha\ne0$ 且 $x\ne y$，(42.45) 实际严格小于零，方向 $\eta=\operatorname{sign}(x-y)$ 满足 (42.41)，且从 $y$ 朝 $x$ 的小段仍在 guard 区间。故 B 成立。第一分量的固定 $D$ 尾与第二分量的固定 $\Omega$ 尾合并即得 (42.42)。B 供应非空单侧开区间，可再由 $D$ 密度选第二尾为 $D$；A 单独只保证周期 $\Omega$ 尾。$\square$

若 $a<0$ 且存在 active 槽，取 $x,F(x)\in T_\omega$，则
$$
\sigma_\alpha\gamma_\alpha(x-y)\le0,\qquad
a\,\sigma_\alpha\gamma_\alpha(x-y)\le0,
$$
只能有 $x=y$。所以
$$
a<0,\ \mathscr A\ne\varnothing
\Longrightarrow
K_\omega=
\begin{cases}
\{y\},&\mathrm A\text{ 成立},\\
\varnothing,&\mathrm A\text{ 失败}.
\end{cases}
\tag{42.46}
$$
没有 active 槽时 A 自动成立，负斜率也可有非周期 guard 终尾。不能通过将奇长返回平方而消除固定全族中的 active 交替：原族允许其后返回数相差一的两个历史；若 active 只在 stem，这两个条件分别来自空返回词和一个返回词。只留下偶数块会改变原族。若额外要求 rival 终尾留在原 singleton 片 $\{y\}$，则唯一候选是 $y$，B 的非零扰动被该附加限制杀死，判据只剩 A。

(42.42) 是 unrestricted guard criterion：$x$ 只需在真实终端 guard 区间 $I_r$ 中，并由固定来源词前接。第 38.7 节的 piece-restricted criterion 则把终尾限制在指定 $P_2$，并从中删除所有 pending 等式，得到 $K_2=P_2\setminus S_2^*$；二者不能混写。

方向图接口还要求同一批已选 stem 和返回路径满足 (42.4)、两原片的逐色闭全包含，并且图上的 rival 参考值与词后缀值一致。B 使 $L$ 为偶数；将基点方向 $\eta$ 运输为返回位置 $j$ 的 $(-1)^{L-j}\eta$ 和 stem 位置 $j$ 的 $(-1)^{|Q|-j}\eta$，每条边翻转，两个返回在同一方向闭合，stem 到达该方向。合法 guard 前接保证全部运输方向合法，(42.41) 正好保证每个 active 所选边被闭方向图保留；反向从闭合提升读取基点方向就恢复 B。原 singleton 参考自身再通过所有归属槽恰为 A。因此在这个同路径图接口下，reference-owned 版本的闭合提升条件是 A 与 B 的合取，而固定混合终尾存在性是 A 与 B 的析取。族自身预算不自动使一个在更大预算供应的原片图满足这些全包含条件。

### 42.8 三周期 singleton rival 的实际排除

本节证明：对每个 $0<\beta<\lambda$，原始 guards 和完整包含规则下，第二来源为实际本原三周期 singleton 时，不能存在第一来源不相干闭 SCC。

先记
$$
\frac{59}{250}<g<\frac{17}{72},
\tag{42.47}
$$
这是由 $g^2+4g-1=0$ 的单调性直接得到的。临界带可写成
$$
\begin{array}{lll}
E_0^\lambda=[-1,-t^2],&
E_1^\lambda=[a,b],&
E_2^\lambda=[c,d],\\
E_3^\lambda=[e,f],&
E_4^\lambda=[h,i],&
E_5^\lambda=[j,\phi],
\end{array}
\tag{42.48}
$$
其中
$$
\begin{aligned}
a&=\frac{3(g-1)}5,& b&=\frac{11g-1}{10},&
c&=\frac{6g-1}5,& d&=\frac{3+7g}{10},\\
e&=\frac{1+4g}5,& f&=\frac{7+13g}{10},&
h&=\frac{3+7g}5,& i&=\frac{11+9g}{10},&
j&=1+g.
\end{aligned}
\tag{42.49}
$$
因 $\beta<\lambda$，实际闭双色带包含于这些临界带，故所有带和 guard 排除均适用于 $\beta$。

原始根分支像还给出严格次临界的标签限制：颜色 $0$ 只允许来源 $3$，颜色 $5$ 只允许来源 $25$；中间四色依次只允许 $\{3,0\},\{0,5\},\{5,2\},\{2,25\}$。令 $\widehat B_k=[q_k-\lambda,q_k+\lambda]$。若某相位在实际双色带 $[q_k-\beta,q_k+\beta]$ 中，将它移到相位零；其来源标签依次被强迫为 $3,0,5,2,25$，相位一的实际逆像落在 $(s_{k-1},s_k)$，其中 $s_m=-1+m\phi/5$。这个带强迫来自同一实际逆分支及 guard，不允许自由拼接相位；临界端点的额外标签也不带入次临界论证。

对三周期来源词 $(u,v,w)$，相位零坐标为
$$
x_{uvw}=\frac{\Delta_u-g\Delta_v+g^2\Delta_w}{D},
\qquad D=1+g^3=17g-3,\qquad
D^{-1}=\frac{71+17g}{76}.
\tag{42.50}
$$
实际 guard 强迫的逐相位颜色上包络如下；表中坐标给出 $76(y_0,y_1,y_2)$：
$$
\begin{array}{c|c|c}
\text{实际来源三字词}&76(y_0,y_1,y_2)&
\text{三个相位的必要颜色包络}\\ \hline
(3,3,5)&(-35+5g,-55-3g,33+17g)&(\{0,1\},0,3)\\
(3,3,2)&(-31-g,-65-7g,77+27g)&(\{0,1\},0,4)\\
(3,3,25)&(-32+10g,-72-6g,104+34g)&(\{0,1\},0,5)\\
(0,3,3)&(6+10g,-34-6g,-48-4g)&(\{1,2\},0,0)\\
(0,3,0)&(10+4g,-44-10g,-4+6g)&(\{1,2\},0,1)\\
(5,0,5)&(26+18g,-8+12g,20+8g)&(\{2,3\},1,2)\\
(5,0,2)&(30+12g,-18+8g,64+18g)&(\{2,3\},1,3)\\
(5,0,25)&(29+23g,-25+9g,91+25g)&(\{2,3\},1,\{4,5\})\\
(2,0,3)&(67+23g,13+9g,-61-13g)&(\{3,4\},2,0)\\
(2,0,0)&(71+17g,3+5g,-17-3g)&(\{3,4\},1,1)\\
(25,5,3)&(87+31g,39+27g,-69-g)&(\{4,5\},3,0)
\end{array}
\tag{42.51}
$$
这正是从实际双色相位强迫得到的全部十一种必要 envelope，而不是把分别可行的三相位任意拼接。各单色相位由坐标栏与全部 $\widehat B_k$ 的严格比较给出：带 $1$ 的下一相位在颜色 $0$ 唯一段，末标签 $5,2,25$ 分别给颜色 $3,4,5$ 唯一段；带 $3$ 的下一相位在颜色 $1$ 唯一段，末标签 $5,2$ 分别给颜色 $2,3$ 唯一段，末标签 $25$ 保留 $\{4,5\}$ 上包络。带 $2$、带 $4$ 和最后一行的坐标按 (42.47) 与 (42.49) 作相同严格线性比较。只有 $(5,0,25)$ 一行保留两处双色上包络；实际允许集合可以更小。

为完整核对表 (42.51)，以下给出带强迫和坐标排除。双色相位移到相位零后：

- 在带 $1$，前两标签均为 $3$。末标签 $3$ 的固定点为 $-1/2<a$；末标签 $0$ 给
  $$
  x_{330}=-(17+3g)/38,\qquad x_{330}-a=(29-129g)/190<0.
  $$
  故只剩 $(3,3,5),(3,3,2),(3,3,25)$。
- 在带 $2$，相位零为 $0$，下一标签为 $3$ 或 $0$。下一标签为 $0$ 时，最大末标签 $25$ 也给
  $$
  x_{00,25}<g^2(2-t)<c,\qquad c-g^2(2-t)=\frac{157g-37}{10}>0.
  $$
  下一标签为 $3$ 时，若末标签至少 $5$，则
  $$
  x_{035}=\frac{9+15g}{76},\qquad x_{035}-b=\frac{83-343g}{380}>0.
  $$
  故只剩 $(0,3,3),(0,3,0)$。
- 在带 $3$，前两标签被强迫为 $5,0$。末标签 $3$ 或 $0$ 时相位零不超过 $x_{500}=t^2/D<t^2<e$，故只剩 $(5,0,5),(5,0,2),(5,0,25)$。
- 在带 $4$，相位零为 $2$，下一标签只能 $0$ 或 $5$；周期必须回到允许 $2$ 的 incoming guard 零。下一标签为 $0$ 时末标签只允许 $3,0,2$，其中 $2$ 给
  $$
  x_{202}=(37+11g)/38,\qquad x_{202}-f=(26-96g)/95>0,
  $$
  故只剩 $(2,0,3),(2,0,0)$；下一标签为 $5$ 时 guard 只允许末标签 $3$ 或 $0$，且两者均满足
  $$
  x_{250}<1-gt^2<h,\qquad h-(1-gt^2)=\frac{39g-9}{10}>0.
  $$
- 在带 $5$，前两标签强迫为 $25,5$；回到 incoming guard 零要求末标签为 $3$ 或 $0$，后者是 $(5,0,25)$ 的循环旋转，故只保留 $(25,5,3)$ 作为代表。

先考虑任意实际周期第一来源，周期长度为 $3k$，每相位采用表中相应包络内的共同颜色；不预设第一词是三周期。令 $x_r(n)=x_{3n+r}$，其中 $n\in\mathbb Z/k\mathbb Z$、$r=0,1,2$，所以 $x_0(n+1)$ 也是同一循环中的实际坐标，接缝处的来源方程和 guard 同样成立。表中各包络与 (42.47) 给出以下正余量：
$$
\begin{aligned}
gt+g^2e-b&=\frac{3g^3}{5}>0,&
2g-d&=\frac{13g-3}{10}>0,\\
c-g^2d&=\frac{23-95g}{10}>0,&
c-g^2f&=\frac{43-181g}{10}>0,\\
1+g^2e-f&=\frac{115g-27}{10}>0,&
e-t^2&=\frac{13g-3}{10}>0.
\end{aligned}
\tag{42.52}
$$
逐行沿循环接缝推得：

- $(\{0,1\},0,3)$ 中，若相位零选 $0$，则 $x_0\ge gt+g^2e>b$；故选 $3$。相位二若选 $2$，则 $x_2\ge1+gt^2>f$，故三标签为 $(3,3,5)$。
- $(\{0,1\},0,4)$ 和 $(\{0,1\},0,5)$ 同样排除相位零的 $0$。相位二为 $4$ 时末标签 $25$ 给 $x_2\ge2-t+gt^2>i$，故为 $2$；相位二为 $5$ 时 guard 强迫 $25$，得到 $(3,3,2)$、$(3,3,25)$。
- $(\{1,2\},0,0)$ 中，$x_1<-t^2$，故相位零为 $5$ 会给 $x_0>t^2(1+g)=2g>d$。相位零为 $3$ 时三步值最大为 $f_{333}(-1)=(17g-5)/2<a$，余量为 $a-f_{333}(-1)=(19-79g)/10>0$。因此只能为 $0$，得到 $(0,3,3)$。
- $(\{1,2\},0,1)$ 中相位零 $5$ 被 $2g>d$ 排除；相位零 $3$ 的两种末标签均给 $f_{330}(a)<a$，故为 $0$。又 $x_1<0$，相位二不能选 $3$，得到 $(0,3,0)$。
- $(\{2,3\},1,2)$ 中相位二正值迫使相位一为 $0$；相位零若为 $0$ 则 $x_0\le g^2d<c$，故为 $5$ 或 $2$。两者均使下一相位零为正，故相位二不能为 $0$，而下一 guard 排除相位零 $2$，得到 $(5,0,5)$。
- $(\{2,3\},1,3)$ 同样先得相位一为 $0$；相位零 $0$ 违反 $g^2f<c$，相位零 $2$ 违反 $1+g^2e>f$，故为 $5$。下一相位零大于 $t^2$，相位二不能为 $5$，得到 $(5,0,2)$。
- $(\{2,3\},1,\{4,5\})$ 中相位二为正，先迫使相位一为 $0$。相位零 $2$ 被 $1+g^2e>f$ 排除；又下一块 $x_0(n+1)\ge c>0$，相位二无论为 $2$ 或 $25$ 都有 $x_2<2-t$，故相位零 $0$ 给 $x_0<g^2(2-t)<c$，也被排除。相位零只能为 $5$；相位二若为 $2$ 则 $x_2<1-gt^2<h$，故为 $25$，得到 $(5,0,25)$。
- $(\{3,4\},2,0)$ 中相位二为 $3$ 且 $x_2<-t^2$；相位一若为 $5$ 则 $x_1>2g>d$，故为 $0$。相位零为 $5$ 给 $x_0<t^2(1-g^2)<e$，余量为 $(11-46g)/5>0$；为 $25$ 给 $x_0\ge2-t-g^2>i$，余量为 $(13g-3)/5>0$。因此只能为 $2$，得到 $(2,0,3)$。
- $(\{3,4\},1,1)$ 中相位零为正。相位二若为 $3$ 给 $x_2<-t<a$，相位一若为 $3$ 给 $x_1\le-t+g^2\phi=2g-1<a$；相位零为 $5$ 给 $x_0<t^2<e$，为 $25$ 给 $x_0\ge2-t-g^3\phi>i$，故只能为 $2$，得到 $(2,0,0)$。
- $(\{4,5\},3,0)$ 中相位零若为 $2$，由下一相位零正得统一上界
  $$
  x_0<1-gt^2-g^2t=3-9g<h,
  $$
  故为 $25$；其后 guard 排除相位一 $2$，得到 $(25,5,3)$。

因此每个循环第一来源的每个 $3$-块均被强迫为表中对应三字词，且循环接缝也被使用。现在回到实际 SCC。定理 36.22 的 rival 相位表示保证每个返回长度为 $3k$。若 rival 各相位唯一色，同基点的两个同步等长返回具有逐位相同的共同颜色词；在第一终端片内选同一合法 $\Omega$ 尾，完整包含提升和引理 36.16 的共同尾宽度迫使两个第一来源词相同，故第一投影相干。

若有双色相位，任取一条实际 SCC 返回，长度为 $3k$，逐 departure 选其容许共同颜色。完整包含使其第一返回收缩映射将基点闭片送入自身；重复返回所得极限固定点在该片内，其合法周期来源的每个后缀也保留全部闭观察约束。第二分量则正是给定三周期 singleton 轨道。因此第一个分量是同一条实际 $3k$ 周期来源，正好满足上面的循环指标及接缝条件，第一词必须是对应三字词的 $k$ 次幂。基点相位不同只需循环旋转。于是同一基点的所有返回同步后第一词相同，第一投影仍相干。这里没有把局部三步历史拼成周期，使用的是实际闭返回的固定点和每个接缝的 guard。

三周期例仍可以有 tight rival。取表中实际周期 $(25,5,3)^\infty$，其第一坐标
$$
y_0=\frac{87+31g}{76}.
\tag{42.53}
$$
令
$$
\beta_* =q_5-y_0=\frac{103g-18}{190},
\qquad
\beta_*-\rho=\frac{8-33g}{380}>0,\qquad
\lambda-\beta_*=\frac{55-225g}{380}>0.
\tag{42.54}
$$
它在第一相位是颜色 $5$ 的 lower-tight 点，另外两相位为唯一色 $3,0$，来源沿 $0\to1\to1\to0$ 合法。这里的端点种子明确为
$$
y_0=q_5-\beta_*.
\tag{42.55}
$$
此处 $y_0$ 本身是闭观察区间 $E_5^{\beta_*}$ 的端点种子；从带 guard 零的 $y_0$ 依次沿合法逆分支 $F_{25},F_5,F_3$ 得到表中 $y_1,y_2,y_0$。第 31 章的端点逆闭包因而包含这三个坐标，供给带类型 singleton 节点及合法周期边。这才证明它们属于实际 singleton 分区；仅有 $\beta_*,y_0\in\mathbb Q(t)$ 不足以证明指定点是该分区端点，也不证明它有有限尾。这是真实 rival 周期例，不是第一来源不相干配对 SCC 的实现例。

### 42.9 周期一与奇周期范围

周期一的实际固定点及其合法常数来源包括
$$
3^\infty\mapsto-\frac12,\qquad
0^\infty\mapsto0,\qquad
5^\infty\mapsto\frac t2,\qquad
2^\infty\mapsto\frac\phi2.
\tag{42.56}
$$
它们的实际 guard 自环分别为 $0\to0$ 的 $3,0,2$ 和 $1\to1$ 的 $5$；$3,0$ 也可从初始 guard 一开始，再进入零。标签 $25$ 的重复不是合法 guard：$25$ 把 $0$ 送入 $1$，而 $1\to1$ 不允许 $25$。

四个坐标在每个 $0<\beta<\lambda$ 下分别只有共同闭颜色 $0,1,2,3$。直接检查其相邻临界扩张端点即可：
$$
\begin{array}{c|c|c}
\text{实际来源}&\text{唯一颜色}&\text{严格隔离不等式}\\ \hline
3^\infty&0&-1<-\tfrac12<a,\\
0^\infty&1&-t^2<0<c,\\
5^\infty&2&b<\tfrac t2<e,\\
2^\infty&3&d<\tfrac\phi2<h.
\end{array}
$$
这里 $a=q_1-\lambda$、$-t^2=q_1+\lambda$、$c=q_2-\lambda$、$b=q_2+\lambda$、$e=q_3-\lambda$、$d=q_3+\lambda$、$h=q_4-\lambda$。所需正余量依次为
$$
\begin{gathered}
a+\tfrac12=(6g-1)/10>0,\qquad c=(6g-1)/5>0,\\
\tfrac t2-b=(7-17g)/20>0,\qquad
e-\tfrac t2=(11g-1)/20>0,\\
\tfrac\phi2-d=9(1-g)/20>0,\qquad
h-\tfrac\phi2=(23g-3)/20>0,
\end{gathered}
$$
均由 (42.47) 得出。这些坐标也在相应实际格内部，所以其唯一颜色不依赖 ownership。

若周期一 singleton rival 的 SCC 有第一不相干返回，将两个返回重复到相同长度；rival 的唯一色使两条路径的共同颜色词逐位相同。在第一终端片内选同一个合法尾，通过 (42.4) 完整提升两条路径。它们前缀不同、尾相同，最后一个不同来源标签的平移差却严格大于所选共同闭格的宽度，违背引理 36.16。因此两个第一来源词必相同，周期一也不能承载第一不相干 SCC。

42.8 节给出了本原三周期的完整排除。由此得到的奇周期结论仅是：若一个奇数本原周期 singleton rival 承载第一来源不相干 SCC，则其周期至少为 $5$。这只是下界；没有构造周期五对象，也没有排除所有奇数周期。

### 42.10 声明 SCC 的全局 ownership 圆柱

固定一个预算 $\beta$、一个已供应的完整闭分歧图及其声明的有限 SCC 家族 $\mathcal S_\beta$：每个 $S\in\mathcal S_\beta$ 是原始图 flag-one 区域的含环 SCC，第一投影不相干、第二片 singleton 且第二投影相干。此处使用原 SCC，未作方向筛选。对每个顶点保留真实颜色边的 ownership 要求 (42.14)。在 $S$ 上构造带状态
$$
(v,w,d,\mu),\qquad d\in\{0,1\},
\tag{42.57}
$$
其中 $\mu$ 是已累积的五切点部分赋值。同步走两条原配对边 $e:v\to v'$、$f:w\to w'$ 时，分别选择 $c\in C_\beta(v)$ 和 $c'\in C_\beta(w)$：$c$ 是 $e$ 自身两来源分量的共同颜色，$c'$ 是 $f$ 自身两来源分量的共同颜色，二者无须相等。将所选颜色副本 $\kappa(e,c)$、$\kappa(f,c')$ 的两项要求都加入 $\mu$，冲突即拒绝，并置 $d'=d\lor[\ell_1(e)\ne\ell_1(f)]$。这是两条返回各自的共同历史，不要求两条返回共享同一个色词。从 $(q,q,0,\varnothing)$ 到 $(q,q,1,\mu)$ 的路径给出一个 ownership 证书；未观察终端不添加要求。所有这样的 $\mu$ 的包含极小族记为 $\mathscr M_S$，再令
$$
\mathscr M_\beta=\min_{\subseteq}\bigcup_{S\in\mathcal S_\beta}\mathscr M_S,\qquad
[\mu]=\{\omega:\mu\subseteq\omega\}.
\tag{42.58}
$$
定义受 ownership 保留的谓词
$$
F_\beta(\omega)\iff
\exists S\in\mathcal S_\beta:
S_\omega\text{ 含第一投影不相干的含环 SCC}.
\tag{42.59}
$$
这里 $S_\omega$ 保留原实际来源边，并在每个 departure 只保留至少一个被 $\omega$ 接受的共同颜色：要求该颜色包含整个第一闭片且对周期 singleton rival 实际可取得。第一闭片无需全体 owned，后面的内部尾处理其实际性；终端坐标仍未观察。

**定理 42.10（精确圆柱并与量词）。**
$$
\boxed{
F_\beta(\omega)
\iff
\omega\in\bigcup_{\mu\in\mathscr M_\beta}[\mu]
\iff
\bigvee_{\mu\in\mathscr M_\beta}
\bigwedge_{k\in\operatorname{dom}\mu}[\omega_k=\mu(k)].
}
\tag{42.60}
$$

**证明。** 若 $F_\beta(\omega)$ 成立，取其不相干 SCC 的两条返回并同步到相等长度。分别沿两条路径的每个 departure 选择被 $\omega$ 接受的共同颜色，允许同一同步时间的两种颜色不同；将两条路径的全部要求累积，得到一致的 $\mu\subseteq\omega$ 和接受路径。若删去某项是因为另一接受项 $\mu'\subsetneq\mu$，则 $[\mu]\subseteq[\mu']$，所以极小化不改变圆柱并集。反向若 $\mu\subseteq\omega$ 来自接受路径，两条返回各自所选的共同颜色都对 rival 实际可取得，第一片闭包含仍保持，且两个第一词不同。两条闭行走的全部顶点能经共同基点互达，属于 $S_\omega$ 的同一含环 SCC；故 $F_\beta(\omega)$ 成立。两方向都未要求 $c=c'$，也未交换来源标签投影。$\square$

因此
$$
\exists\omega\,F_\beta(\omega)\iff\mathscr M_\beta\ne\varnothing,
\tag{42.61}
$$
而
$$
\forall\omega\,F_\beta(\omega)
\iff
\bigcup_{\mu\in\mathscr M_\beta}[\mu]=\{L,R\}^{\{1,\ldots,5\}}.
\tag{42.62}
$$
(42.62) 是 $\forall\omega\,\exists S$，不是 $\exists S\,\forall\omega$。一个 ownership 可以由某个 SCC 见证，另一个 ownership 由另一 SCC 见证；不能把所有 SCC 谓词相交。整个圆柱族至多 $3^5$ 项，代表有限数学证书而非图枚举程序。

若 $\mathcal S_\beta\ne\varnothing$，置
$$
N_*=\max_{S\in\mathcal S_\beta}|S|,
\tag{42.63}
$$
则每个正 ownership 都有一个重基点的两返回证书
$$
L\le2N_*^2-1.
\tag{42.64}
$$
证明如下：取一个接受路径的两返回及其所选颜色边的并集 $U$，顶点经共同基点互达，故 $U$ 强连通且第一投影不相干，第二投影仍相干。因此其中有真正 disagreement 边 $e:p\to q$；否则两来源投影逐边相同，第一投影会继承第二相干性。以 $q$ 为新基点，定理 36.22 的基点不变性保持第一不相干。在 $U$ 内重新取普通同步平方的最短第一词不同返回，而不旋转、加长旧接受对；状态数至多 $2|V(U)|^2$，不重复状态的路径长度至多 $2|S|^2-1$。所有选色与 ownership 要求沿 $U$ 保留，无新赋值。用 $e$ 作一边初始 stem；incoming guard 一合法的标签从 guard 零也合法，下一 guard 与映射不变。这个重基点步骤没有把同一来源标签投影错换。

在新基点依第 39.2 节取非退化第一 hull，并在其内部一次固定合法 $D$ 尾 $\xi$。第二相干性使等长返回有同一个来源词 $V$，一次固定周期 $\Omega$ 尾 $\eta=V^\infty$。内部尾的非零斜率后缀避开全部扩张端点，rival 的所选颜色要求则包含在已接受 $\mu$ 中。因此这一对 literal tails 和固定颜色词，在同一预算下实现所有有限拼接（包括空词），且同时对每个 $\omega\supseteq\mu$ 有效。针对固定的 $\omega$，要把 rival 尾也选为 $D$，精确条件是其实际轨道集 $K_\omega\cap\kappa_{r_q}(D_{r_q})\ne\varnothing$；B 的非零合法内向区间加 $D$ 密度是充分条件，A 单独则还须 $y_q\in\kappa_{r_q}(D_{r_q})$。仅通过 (42.42) 不供应 $D$ rival。线性记忆证明要求第一分量 $D$-live，第二分量只承担 $\Omega$ 安全义务。

记一边 stem 的两来源词和颜色词为 $(P,Q,h)$，长度 $a=|P|=|Q|=|h|=1$。若所选两返回的第一词为 $U_0\ne U_1$、共同颜色词为 $W_0,W_1$，则对每个 $n\ge0$、$z\in\{0,1\}^n$ 有实际共同历史
$$
h_z=hW_{z_1}\cdots W_{z_n},\qquad
\alpha_z=PU_{z_1}\cdots U_{z_n}\xi\in D,\qquad
\gamma_z=QV^n\eta\in\Omega.
\tag{42.68}
$$
对每个满足定义 36.9 完整恢复合同的解码器，同一 $n$ 下的 $\alpha_z$ 两两不同；若两个 $h_z$ 相同，则固定第一未来会给不同 $D$ 来源同一完整记录，已发表的闭唯一性排除这一点。设 stem 首次不同位置为 $k$，$\Omega$ 安全性使每个 $h_z$ 后的旧输出至多有 $k+1$ 种共同前缀。若两条不同历史在同一完整配置和旧输出相遇，再接同一个第一未来，确定性与 $D$-liveness 产生矛盾。因此处理完这些历史至少需要 $2^n/(k+1)$ 个配置；所有可读控制、工作存储、计数、位置、时序及输出侧状态均计入，容量至多为 $2^{B+1}-1$，得到
$$
B^{\mathrm{worst}}_{\beta,\omega}(a+nL)\ge n-O(1),
\tag{42.69}
$$
即正 ownership 的同预算线性下界；竞争尾仍只承担 $\Omega$ 安全义务。

定义 $C_\beta(\omega)$ 为同一家族中存在一个 retained cycle（在已进入 divergence flag-one 区域）的谓词。简单环长度至多 $|S|$。该环必有来源分歧边：若两标签沿环处处相同，两分量返回是同一收缩映射，重复后都取得其同一固定点；接回 flag-one 的较早分歧前缀，得到两条有限位置曾不同、以后完全同尾而有共同闭色的来源，违背引理 36.16 的最后不同标签排除。将环旋转到此边的 head，并以该边作合法一边 disagreement stem。固定第一非退化片内非固定点的 $D$ 尾，并固定第二周期 $\Omega$ 尾，重复环的第一标量迭代两两不同。每个检查点在同一个未来下必须有不同完整配置，故
$$
C_\beta(\omega)\Longrightarrow
B_{\beta,\omega}^{\mathrm{worst}}(N)=\Omega(\log(N+2)).
\tag{42.65}
$$
更具体地，若 stem 后的环词为 $W$、第一来源环词为 $U$，取第一片内部不等于 $U$ 的固定点的标量 $x$ 及固定 $D$ 尾 $\xi$，则 $P U^n\xi$ 随 $n$ 两两不同：严格收缩的非固定点迭代不重复。第二分量接其实际周期 $\Omega$ 尾，给出同一 ownership 下的安全竞争历史。stem 首次分歧位置只有有限个共同前缀长度，故每个检查点的旧输出只有常数种可能；若两个检查点的完整配置和旧输出相同，接同一个第一未来会使两个不同 $D$ 来源产生相同的最终输出，违反安全性与逐位置生效。实际记录 $hW^KS_\xi$ 经过从 $h$ 到 $hW^K$ 的全部检查点，故前 $K$ 次环重复在单条记录上需要至少线性于 $K$ 的不同配置，二进制容量给出对数峰值下界。这个论证只使用一个周期参考和一个实际环，不把循环谓词提升为全解码器上界。

这只是循环下界；$\neg F_\beta$ 或 $\neg C_\beta$ 都不给全解码器的常数或对数上界。对固定 $\beta\in\mathbb Q(t)\cap[0,\lambda)$，完整的固定预算三分律和其 $D/\Omega$ pending 状态、$\Omega$-only 单点、最长公共前缀矩阵及多幂模板，已经由已发表第 38.1–38.8 节及式 (38.1) 给出；本章不把声明子族的负谓词当作该完整分类。

在已发表预算
$$
\rho=\frac{239g-44}{380}
\tag{42.66}
$$
完整图没有第一不相干 SCC，且所有 ownership 下精确记忆仍为
$$
\Theta(\log(N+2)).
\tag{42.67}
$$
这里定理 36.15 的实际严格泵送给出对数下界，定理 36.21 的固定闭解码器给出覆盖 $\rho$ 及某个更大亚临界半径的对数上界。若 $\rho$ 的完整闭分歧图有不相干 SCC，定理 36.25 会在这两个半径之间的某个预算供应线性下界，违背同一预算的对数上界。因此该图没有不相干 SCC，尤其没有本章声明的第一不相干 singleton-rival SCC。

这是实际 FIB 的负/非恒定例：声明家族为空，(42.60) 对每个 ownership 都为假，但不能据此推出常数记忆。不能用这些 restricted 谓词替代第 38 章的完整上界前提；按该章作完整线性判定时，也必须保留全部 exact $D/\Omega$ 状态。

### 42.11 固定族与已发表轨道、记忆结果的接口

第 39.2–39.5 节已给固定返回族的最小闭预算、非退化 hull 的内部尾以及 singleton rival 的 $T_\omega,K_\omega$ 判据；(42.39)–(42.46) 只把这些公式按空词、stem-only 槽和 unrestricted guard 量词重新列出。命题 39.6.1 的四地址论证给出第一不相干 SCC 不能困在单点；定理 39.7.1 给精确预算上的同预算配置下界，定理 39.8.1 给从闭预算向较大实际预算的固定尾转移。对固定 $\mathbb Q(t)$ 亚临界预算，已发表第 38 章的完整分类负责常数、对数、线性的完整候选图三分律；本章的新方向和周期结果不取代它。

尤其要保留一个分离的 lower-budget 量词：先固定某一个最终周期参考和一对共同等幅的合法 $\Omega/\Omega$ 尾，对每个 $n\ge0$，(42.35) 给该规定有限历史的 $b_n<\beta$ 种子；这需要两分量的合法幅度区间、全部 active 内向条件和最早 active 时间的全部等号归属。它不等于“所有二返回历史在同一个 $b_n$ 下可行”，也不等于 rival sign-only 条件。任何第一尾为 $D$ 或两尾为 $D/D$ 的加强，都还须单独的实际有限尾见证。

方向和 hull 也不要求扰动尾留在原 singleton piece。原始 sources、guards、完整误差运输和每个实际目标才是实际合法性的证据；旧片成员性只在明确声明 piece-restricted 判据时才加入。真实 FIB 周期表与抽象区间轨道必须分开：例如正斜率 $F(x)=g^2x$、$T=(0,1]$ 的轨道说明只是闭极限成员与实际成员的抽象区别，不能冒充六格 FIB 的周期证据。

### 42.12 失败检查、经济修复与下一结构缺口

若一个候选方向证书失败，具体修复是逐边重新选择共同颜色、重新检查 (42.11) 的 guard 方向和 (42.14) 的切点要求；若冲突只来自某个切点，则把该部分赋值保留在 $\mu$ 中并检查另一 SCC 或另一选色边，不能预设替代证书存在。若低预算种子失败，检查两个分量的共同合法幅度、每个 active 内向条件和最早等号归属；只有另需有限来源时，才再检查实际有限尾见证或单点 $D$-可达零路径。不能用 $\mathbb Q(t)$、rival sign 或较大预算的闭包含替代这些检查。若固定族 A 失败而 B 成立，允许 unrestricted guard 的非周期终尾；若必须保留 singleton，则只有实际 owned 的周期点可用，改换族仍须另有证据。

尚未解决的一个真实 FIB 结构缺口是：当预算趋近全局转变半径时，能否对实际混合分支见证的 stem 和同步返回长度给出同时一致的上界。一条图大小路线是控制所需完整 exact $D/\Omega$ divergence 图或足够保留见证的 recurrent quotient，再应用相应有限图长度界；另一条路线是直接证明足够短的实际语义见证。对本章声明家族，若另有 $N_*$ 的一致界，(42.64) 才给相应返回的一致界；它不自动覆盖完整混合图的所有见证。完整图大小无界只阻止以该大小直接代入的路线，不排除更小商图或统一语义长度界。要否定所有这种语义界，须证明实际见证的最短必要长度无界，而非仅某个图表示越来越大。同时有界词长的条件取得及其额外 ownership 检查仍按第 39.9 节处理；此处不宣称全局 $R$ 的取得、算术性质或精确值。

### 42.13 结论与迭代问题

在本章已固定的合法二返回族中，第一 hull 非退化且全部第一后缀闭包含时，一条 hull 内部的固定 $D$ 尾处理第一分量；singleton rival 的固定 $\Omega$ 尾存在性恰由 A 或 B 判定。真实来源词、guards 和同一对 literal tails 承担所有有限延续，空词也在量词内。方向证书另外逐边锁定所选 tight 和方向翻转，给自身预算恰为 $\beta$ 的同预算固定 $D/D$ 实现；reference-owned 细化则保留未扰动周期尾。这些结论限定于声明的族或有限 SCC，不把这种表示宣称为任意折叠边界的普遍必要条件。

对迭代问题，本章给出的可复用条件是这个固定族的完整来源合同与全族轨道可行性。局部端点可行性本身不足以供应该证书：实际周期三的 guard 强迫排除目标第一不相干 SCC，负斜率加 active 槽只留下周期点或空集，未拥有的原 singleton 端点在终尾限片时也失败。经济的接口是只增加方向与周期结果，hull、轨道和记忆判据分别复用第 39、38 章；更一般的折叠边界、较小 recurrent quotient 和全局 $R$ 的义务保持开放。

## 42.99 追加锚（本行以下为增补区）

## 43. 固定实际尾、有限返回树与预算缺口容量

**约定 43.0（周期见证、实际尾与实预算引用的范围）。** 第42.10节中“A 单独则还须 $y_q\in\kappa_{r_q}(D_{r_q})$”限定的是把 A 所用的未扰动周期见证本身选作 $D$ 尾。存在某条可用 $D$ rival 的一般条件仍为 $K_\omega\cap\kappa_{r_q}(D_{r_q})\ne\varnothing$，不能把中心的 $D$ 成员性提升为该存在性的必要条件。只有另已证明 $K_\omega=\{y_q\}$，例如第42.7节的负斜率且存在 active 槽情形，或明确限制终尾留在原 singleton piece 时，才可作这种简化。

第42.8—42.9节对实数 $0<\beta<\lambda$ 使用的是引理36.16证明中的最后不同标签与严格标量宽度论证；该论证只需原分支、guard 和宽度不等式。它不把原先在 $\mathbb Q(t)$ 预算下给出的有限端点图构造推广到任意实预算；涉及有限图的结论仍要求实际提供满足原完整包含规则的图。

**命题 43.1（固定证书的范围）。** 固定同一个 guarded FIB 来源：两个合法 stem、同一组来源标签、同一共同颜色历史、一对固定实际 $D/D$ 终尾，以及一个正闭预算 $\beta$. 观察只发生在 departure 位置，未观察的终端不附加颜色。以下分别刻画共同等幅扰动的实际性、不等幅 active seed 的精确等号预算，以及深度不超过 $n$ 的整棵二返回树的闭成本；第43.22—43.24节再给出负斜率的奇偶尾式、实际相邻平台和 H+ 下的条件容量代入。区间编码、前接仿射式、完成地址满像、有限来源唯一性和两返回规范 hull 使用[定义14.5](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L1854)、[命题14.6](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L1894)、[定理14.7](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L1921)、[定理17.2](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L3305)、[定理34.3](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L9847)、[命题35.9](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L10708)、[定理36.11](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L11299)、[定理39.2.1](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13238)、[推论39.2.2](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13295)、[定理39.3.2](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13336)及[定理39.4.1](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13358)的已发表结论；这里只把它们应用到同时固定的实际来源。

环陪集只说明环成员相容；实际 $D$ 尾还必须满足 incoming guard、严格物理条带和 $Q\ge0$. 精确等号预算只看当前前缀中已经出现的 active 槽。整树最大值由逐个实际端点取得的有限清单给出，且其阈值属于这个固定有限族；没有选定 tight 锁时，中心只能写成该族的 $B_*$. 这些量词不推出全局阈值、统一跨预算常数或任何物理生成结论。

本章的来源与观察记号沿用[定义39.1.1](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13123)及[式(28.1)](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L7138)，引用均指本卷[固定修订 `cfe06a9af05aff5b3d2ffa4d478cea124842a1a3`](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md)。$I_0=X=[-1,\phi]$、$I_1=[-1,t]$ 是闭 guard 支撑；$A_0=\Omega$、$D_0=D$，$D_s\subset A_s$ 是最终空尾地址。来源标签为 $\Lambda=\{3,0,5,2,25\}$，其中 $0$ 是空窗、$25$ 是一个窗口标签；它们与观察颜色 $0,\ldots,5$ 分开。实际合法边、平移量和前接次序为

$$
\begin{gathered}
0\to0:3,0,2;\qquad 0\to1:5,25;\qquad
1\to0:3,0;\qquad 1\to1:5,\\
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t),\qquad f_\ell(x)=\Delta_\ell-gx,\\
f_w=f_{w_0}\circ\cdots\circ f_{w_{|w|-1}},\qquad f_\varnothing=\mathrm{id}.
\end{gathered}
$$

两个 guard 的编码都是 $\kappa_s(\xi)=\sum_{j\ge0}(-g)^j\Delta_{\xi_j}$。一次固定合法切点归属，令 $\lambda=t^2/10$，颜色切点与闭包为

$$
\begin{gathered}
q_1=-t^2-\lambda,\quad q_2=g-3\lambda,\quad q_3=t-5\lambda,
\quad q_4=2t-7\lambda,\quad q_5=2t+\lambda,\\
J_0=[-1,q_1],\quad J_1=[q_1,q_2],\quad J_2=[q_2,q_3],\\
J_3=[q_3,q_4],\quad J_4=[q_4,q_5],\quad J_5=[q_5,\phi].
\end{gathered}
$$

实际拥有格 $C_c$ 是闭包 $J_c$ 的内部加上归属于它的端点，观察为 $\mathcal Q(\operatorname{clip}_X(x+e))$。对 $b\ge0$，沿用

$$
E_c^b=\{x\in X:\operatorname{dist}(x,J_c)\le b\},\qquad
O_c^b=\{x\in X:\exists v\in C_c,\ |x-v|\le b\}.
$$

裁剪非扩张且固定 $x\in X$，反向取 $e=v-x$ 即可，故 $O_c^b$ 恰为实际可取得区间。对 $x\in E_c^b$，实际取得的充要条件是距离严格小于 $b$，或距离等于 $b$ 且唯一最近点 $\operatorname{proj}_{J_c}(x)$ 被 $C_c$ 拥有；$b=0$ 时仍须 $x\in C_c$。以下把严格 guard 条带记为 $J_s^{\mathrm{fin}}$，与颜色闭包 $J_c$ 区分。

### 43.2 实际有限尾的精确条带

**命题 43.2（两种 incoming guard 的有限尾集合）。** 令

$$
 t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad g=t^3,\qquad R=\mathbb Z[t],\qquad t'=-\phi,\qquad g'=-g^{-1}.
$$

置

$$
 J_0^{\mathrm{fin}}=(-1,\phi),\qquad J_1^{\mathrm{fin}}=(-1,t).
$$

若 $x=A+Bt\in R$，定义

$$
 Q(x)=2A-3B=\frac{gx+g^{-1}x'}{\sqrt5}.
$$

对 guard $s=0,1$，实际最终空窗地址的标量集合恰为

$$\boxed{T_s=\{x\in R\cap J_s^{\mathrm{fin}}:Q(x)\ge0\}.}$$

其中 $Q(x)>0$ 是非零有限来源的严格数量条件；$Q(x)=0$ 在 $J_0^{\mathrm{fin}}$ 中只给 $x=0$，它是零来源例外。guard 一的集合也可写为 $T_1=-tT_0$。同一 guard 下，每个标量 $x\in I_s$ 在全部完成地址域 $A_s$ 中至多有两个编码；若有编码属于 $D_s$，该标量在全部 $A_s$ 中即只有这一条编码。由于 $A_s\subseteq\Omega$ 且有限地址避开 guard 零的全部双编码点，每个实际有限地址的标量在整个 $\Omega$ 中也只有这一条编码。

**证明。** [约定1.3](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L34)把母卷的正数量条件翻译为 $R$ 中的整数条带；定理34.3及命题35.9把同一条件写成当前 guard、支持和 $Q$ 的坐标形式。于是已发表的有限来源数量条件对 guard 零给出

$$
 x\in R,\quad -1<x<\phi,\quad Q(x)>0
 \Longrightarrow x\in T_0,
$$

而 $Q(x)=0$ 时，写 $A=3m,B=2m$ 得 $x=m/g$。在 $(-1,\phi)$ 内只有 $m=0$，[命题1.2](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L30)的零来源正好给出 $x=0$。反向方向由任何有限位串的实际展开直接得到 $x\in R\cap J_0^{\mathrm{fin}}$ 和 $Q(x)\ge0$。

guard 一的首位必须为零。删去这个首位得到 guard 零地址，标量乘以 $-t$，所以 $T_1=-tT_0$。若首位为一，则下一位受 no-$11$ 约束为零，标量为 $1+t^2z>1-t^2=t$, $z\in(-1,\phi)$，仍在 guard 零条带，却位于 guard 一条带的另一侧，因而不属于 incoming guard 一。于是两个 guard 都满足所写集合等式。

命题14.6给出每个根分支的实际极值尾，定理14.7给出每个标量 $x\in I_s$ 在固定 guard 的全部 $A_s$ 中至多两个编码，并说明双编码只能在有限前缀后接非零周期极值尾。根极值和这些双编码尾都不是 eventually-null；因此 $D_s$ 避开双编码点，定理14.7之后的限制 $\kappa_s|_{D_s}$ 在每个 guard 上单射。证毕。

**命题 43.3（数量的两个用途）。** 命题43.2中的 $Q$ 是实际有限来源的整数数量，不是把共轭 $x'$ 非负当作充分条件。

**证明。** 有限位串给出

$$
 x'=\sum_j b_j\phi^j\ge0,\qquad b_j\in\{0,1\},
$$

因此共轭非负是必要条件；只有结合 $R$、$J_s^{\mathrm{fin}}$ 和 $Q\ge0$ 才得到实际尾。特别地，$t\in R\cap J_0^{\mathrm{fin}}$ 而 $Q(t)=-3$，所以环条带本身不是有限来源集合。证毕。

### 43.4 等幅扰动的陪集与实际性

**命题 43.4（共同等幅的环必要条件）。** 设两个纯周期参考为

$$
 h=\frac{A_U}{1-(-g)^{L_U}},\qquad y=\frac{A_V}{1-(-g)^{L_V}},\qquad A_U,A_V\in R,
$$

其中 $U,V$ 是实际合法返回词。给定 $\varepsilon_1\in\{-1,0,1\}$、$\varepsilon_2\in\{-1,+1\}$，若存在 $\kappa>0$ 使

$$
 x_1=h+\varepsilon_1\kappa\in T_{s_1},\qquad x_2=y+\varepsilon_2\kappa\in T_{s_2},
$$

且两个方向均非零，则必有

$$\boxed{h-\varepsilon_1\varepsilon_2y\in R.}$$

当这个条件成立时，两个允许幅度的环陪集相交；它本身不保证实际 $D/D$ 尾。

**证明。** 两个 $x_i$ 都在 $R$，故

$$
 \varepsilon_2x_1-\varepsilon_1x_2
 =\varepsilon_2h-\varepsilon_1y\in R.
$$

将这个等式乘以单位 $\varepsilon_2$，得到

$$
 x_1-\varepsilon_1\varepsilon_2x_2
 =h-\varepsilon_1\varepsilon_2y\in R,
$$

即得所写条件。反过来，该条件使

$$
\varepsilon_1(R-h)=\varepsilon_2(R-y)
$$

成为同一个 $R$ 陪集，故只在环成员层面存在共同幅度。要得到实际尾，还必须同时检查 $J_{s_i}^{\mathrm{fin}}$ 和 $Q(x_i)\ge0$；命题43.2给出这个检查的充要性。证毕。

**命题 43.5（同号时的共同实际 $D/D$ 充分性）。** 假设 $\varepsilon_1=\varepsilon_2=\varepsilon\in\{-1,+1\}$，并且参考点各自沿该方向有一个共同的非空开幅度区间：存在 $\eta>0$，使每个 $0<\kappa<\eta$ 都满足

$$
 h+\varepsilon\kappa\in J_{s_1}^{\mathrm{fin}},\qquad y+\varepsilon\kappa\in J_{s_2}^{\mathrm{fin}}.
$$

则对任意 $\eta_0\in(0,\eta)$，存在 $0<\kappa<\eta_0$ 使两个点同时属于 $T_{s_1},T_{s_2}$，当且仅当

$$\boxed{h-y\in R.}$$

选定一次这样的 $\kappa$ 后，两个有限尾字面量可以固定用于所有后续历史。

**证明。** 必要性是命题43.4。设 $h-y=C\in R$。由于 $R=\mathbb Z+\mathbb Zt$ 在实轴稠密，可在 $(0,\eta_0)$ 内取 $\kappa_0$，使

$$
 u=h+\varepsilon\kappa_0\in R,\qquad v=y+\varepsilon\kappa_0=u-C\in R.
$$

再取充分大的整数 $m$，置

$$
 u_m=u+t^{2m},\qquad v_m=v+t^{2m},\qquad
 \kappa_m=\kappa_0+\varepsilon t^{2m}.
$$

于是

$$
 u_m=h+\varepsilon\kappa_m,\qquad v_m=y+\varepsilon\kappa_m,\qquad u_m-v_m=C.
$$

当 $m$ 足够大时，$\kappa_m\in(0,\eta_0)$ 且两个点仍在各自的开条带内。由已发表的单占位数量式，

$$
 Q(t^{2m})=\frac{g t^{2m}+g^{-1}\phi^{2m}}{\sqrt5}
=F_{2m+3}\longrightarrow+\infty.
$$

所以同一个 $m$ 可使 $Q(u_m)>0$ 和 $Q(v_m)>0$ 同时成立。命题43.2遂给出两个实际有限尾。共同加入的 $t^{2m}$ 保留差值、同号方向和两个 guard，故这是实际 $D/D$ 的充分性。由于每个任意小的 $\eta_0$ 都可这样处理，得到任意小的合法共同幅度。证毕。

**命题 43.6（相反号的纯周期共轭障碍）。** 任一实际合法纯周期标量 $z$ 满足

$$
 z'\le0,
$$

且只要周期词含有非零来源标签，就有 $z'<0$。因此若 $\varepsilon_1=-\varepsilon_2$ 且 $h,y$ 中至少一个是非零纯周期参考，则不存在 $\kappa>0$ 使两个扰动点同时属于相应的 $T_s$。即使 $h+y\in R$，环陪集条件也不足。

**证明。** 对长度 $L$ 的实际返回词，写

$$
 z=\frac{A_U}{1-(-g)^L},\qquad
 A_U=\sum_{r=0}^{L-1}(-g)^r\Delta_{U_r}.
$$

代数共轭把 $(-g)$ 变为 $g^{-1}$，而各非零窗口的共轭平移严格为正，零窗口的共轭平移为零。因此 $A_U'\ge0$，非零词时 $A_U'>0$，同时

$$
 (1-(-g)^L)'=1-g^{-L}<0.
$$

从而 $z'=A_U'/(1-g^{-L})\le0$，严格性如上。若相反号共同幅度存在，则

$$
 x_1+x_2=h+y.
$$

每个有限尾的共轭是位和，故 $x_1',x_2'\ge0$。但 $h'+y'<0$，矛盾。若 $h=y=0$，则 $x_1+x_2=0$；两个共轭均非负且和为零，遂只能 $x_1=x_2=0$，这又迫使 $\kappa=0$，不符合正幅度。证毕。

**命题 43.7（零方向及其他退化情形）。** 若 $\varepsilon_1=0$，则共同等幅构造的第一分量必要且充分地要求 $h\in T_{s_1}$；第二分量还必须在其指定单侧区间内实际找到 $y+\varepsilon_2\kappa\in T_{s_2}$。若 $h$ 是非零纯周期参考，则该条件失败；若 $h=0$，它是零尾例外，不能被非有限性结论替代。若两个方向均非零而参考之一为零，则命题43.6仍排除相反号正幅度；同号情形仍按命题43.5检查共同条带和 $h-y\in R$。

**证明。** 第一坐标不随 $\kappa$ 变化，所以它必须本身属于命题43.2的实际集合；这也显然是充分的第一坐标条件。第二坐标是单独的单侧实际尾问题，需由其开条带和数量条件解决。命题43.6的共轭证明覆盖一个参考为零、另一个非零的相反号情形；全零情形已在该命题末尾处理。证毕。

**命题 43.8（实际六周期例与非整陪集）。** 已发表六周期参考

$$
 P_A=(3,3,5,0,3,0),\qquad P_B=(0,3,0,3,3,5)
$$

分别回到 guard 零和 guard 一，并在共同颜色流 $(1,0,2)^\infty$ 下有相位零与相位三的周期标量

$$
 \alpha=-\frac{33+6g}{76},\qquad z_3=\frac{8+15g}{76}.
$$

在偶数个六步检查点，A 的向内改善方向是 $+1$，B 的向内改善方向是 $-1$。相反号等幅所需的环条件为 $\alpha+z_3\in R$，但

$$
 \alpha+z_3=\frac{-25+9g}{76}=\frac{-17+9t}{38}\notin\mathbb Z[t].
$$

所以这一个实际周期参考甚至没有相应的环陪集兼容，当然不存在共同等幅 $D/D$ 尾。这个例子只说明实际 PA/PB 参考的代数障碍；它不宣称一个不相干 paired SCC，也不提供任何分支存在性结论。

**证明。** 方向由六周期中 active 相位相对检查点的运输符号直接给出：A 的 active 相位是 $r\equiv0\pmod6$，B 的 active 相位是 $r\equiv3\pmod6$，负斜率运输使两者所需方向相反。相反号的命题43.4条件变成 $\alpha+z_3\in R$。用 $g=2t-1$ 化简得到所写式；其在基底 $1,t$ 下两个系数均为非整数，故不在 $R$。证毕。

### 43.9 不等幅的单一实际种子

**命题 43.9（固定历史的所有 active 槽与精确等号预算）。** 固定同一来源、共同颜色历史、同一对参考周期点 $h_i$、合法 stem 和合法返回。返回长度 $L$ 为正偶数，因而重复返回的运输因子为正 $g^L$. 令原有限历史为

$$
 H_n=H_{\rm pre}W^n,\qquad M_n=d+nL,
$$

其中只观察 departure 位置 $r<M_n$，终端位置 $M_n$ 不观察。active 指参考历史中到指定闭格的距离恰为 $\beta$ 的槽；假设至少一个这样的槽在某个有限前缀中实际出现。对每个会实际出现的 active 槽 $(i,r)$，选定原来向内的方向 $\varepsilon_i$ 和一次固定的正幅度 $\eta_i$，并取同一对固定实际尾

$$
 x_i=h_i+\varepsilon_i\eta_i\in T_{s_i}.
$$

假设 $\beta>0$；每个 active 槽的 signed transport 都沿 $\varepsilon_i$ 指向其闭格内部，并在所有 $n$ 中保留同一个单侧距离段；所有非 active 槽在参考值处有共同严格余量 $\Delta>0$. 若没有非 active 槽，约定 $\Delta=+\infty$ 并删除下述关于 $\Delta$ 的限制。幅度在假设中一次选定并满足

$$
\eta_{\max}:=\max_i\eta_i<\min\{\beta/2,\Delta/3\},
$$

其中 $\min\{\beta/2,+\infty\}=\beta/2$. 令

$$
 \mathcal A_n=\{(i,r):r<M_n\text{ 且该槽在 }H_n\text{ 中 active}\}.
$$

$\mathcal A_n$ 在每个深度都定义。只在 $\mathcal A_n\ne\varnothing$ 时定义

$$
\gamma_n=\min_{(i,r)\in\mathcal A_n}\eta_i g^{-r},\qquad
\widehat b_n=\beta-g^{M_n}\gamma_n.
$$

在这些深度，同一对固定实际尾承担 $H_n$ 的最大闭距离恰为

$$\boxed{\widehat b_n=\beta-g^{M_n}\gamma_n.}$$

其等号槽为

$$\boxed{\mathcal E_n=\{(i,j_i):j_i<M_n,\ \eta_i g^{-j_i}=\gamma_n\},}$$

其中 $j_i$ 是分量 $i$ 在当前前缀中已经出现的第一次 active 时间；不存在于当前前缀的分量不计入。精确预算 $\widehat b_n$ 下，给定归属可实现当且仅当 $\mathcal E_n$ 中每一个实际等距目标的端点归属于指定颜色；所有最小者和 ties 都必须检查。

**证明。** 对 active 槽，前缀到终端的长度为 $M_n-r$，固定尾的仿射运输给出准确距离

$$
 \operatorname{dist}_{i,r}=\beta-\eta_i g^{M_n-r}
 =\beta-g^{M_n}(\eta_i g^{-r}).
$$

同一分量的 $\eta_i g^{-r}$ 随 $r$ 严格增加，所以它在当前前缀中的最小值只能由已经出现的第一次 active 时间 $j_i$ 取得。不能用一次尚未出现的 eventual return occurrence 代替 $j_i$。

由假设，所有 guard、来源接缝和 active 单侧方向对这一次固定的 $\eta_i$ 同时成立。每个非 active 槽的扰动后距离至多 $\beta-\Delta+\eta_{\max}$。另一方面，active 的预算下降量满足

$$
 0<g^{M_n}\gamma_n\le\eta_{\max},
$$

所以

$$
\beta-\Delta+\eta_{\max}<\beta-g^{M_n}\gamma_n.
$$

最大值确实由 $\mathcal A_n$ 给出，得到公式。其等号集合正是所有当前分量的第一次 active 槽中达到最小权重的那些槽。

若等号槽的最近闭格点属于指定的实际颜色区间，取该点即可；若不等号槽距离严格小于 $\widehat b_n$，可把目标略移入其指定颜色的内部而仍留在预算内。反之，等号槽的距离已经是全局最大值，若其唯一最近端点不属于指定归属，就没有另一个距离不增的实际目标可取。因此这些端点旗标是精确归属条件。证毕。

**命题 43.10（稳定的分量权重与任意归属的严格放松）。** 只对 $\mathcal A_n\ne\varnothing$ 的深度定义 $\gamma_n$；若某个最早 active 时间尚未进入前缀，则该较早历史保留其实际成本和端点旗标，不用未出现的槽补入最小值。令 $I_n$ 为当前前缀中已经出现 active 槽的分量集合，令 $I_\infty=\bigcup_n I_n$；对每个 $i\in I_\infty$，令 $j_i$ 为其在完整历史中的第一次 active 时间。存在 $n_0$ 使得

$$
 \gamma_n=\gamma_*:=\min_{i\in I_n}\eta_i g^{-j_i}
 =\min_{i\in I_\infty}\eta_i g^{-j_i}\qquad(n\ge n_0),
$$

并且

$$
 \widehat b_n=\beta-\gamma_*g^{d+nL}\quad(n\ge n_0).
$$

在相邻两层均有定义时，$\gamma_{n+1}\le\gamma_n$，故 $\widehat b_n$ 严格递增。若 $0<\theta<1$，则

$$\boxed{\widetilde b_n=\beta-\theta g^{M_n}\gamma_n}$$

满足 $\widehat b_n<\widetilde b_n<\beta$，并对每个当前历史、每个所有权归属都可由同一对固定实际尾实现。

若要求同一个分量在所有深度（包括 $n=0$）控制等号，必须有 $j_i<d$，即它的第一次 active 槽已经在 stem 前缀中；若 $j_i\ge d$，由此分量得到的断言只从其首次出现的深度起成立。

**证明。** 每个分量只有一个第一次 active 时间；一旦该时间进入前缀，后来的同分量槽权重更大。有限个分量的最小值遂在某个固定 $n_0$ 后稳定。加入返回块只增加候选槽，所以 $\gamma_{n+1}\le\gamma_n$，而

$$
 g^{M_{n+1}}\gamma_{n+1}\le g^L g^{M_n}\gamma_n<g^{M_n}\gamma_n.
$$

这给出严格递增。严格放松的预算比精确最大距离大，所有观察坐标距其闭格严格小于 $\widetilde b_n$；按实际颜色区间内部取目标，端点是否归属不再影响可行性。固定尾和原来源历史没有改变。证毕。

### 43.11 一对固定 D/D 尾承载整棵二返回树

**命题 43.11（树的 guarded 证书）。** 令 $0<\beta$，并固定两个同长、实际合法的 stem $P,Q$，其来源 guard 都从 $0$ 出发，分别到达 $s_1,s_2$，且 $d=|P|=|Q|$. 固定两个实际合法的正偶长度返回 $U_0,U_1:s_1\to s_1$，令 $L=|U_i|$，以及一个实际合法的正偶长度返回 $V:s_2\to s_2$，三者长度同为 $L$. 要求

$$
 U_0\ne U_1,\qquad a=g^L\in(0,1).
$$

所有 stem、return 和接缝的来源标签、incoming guard 与 outgoing guard 均取自实际合法边；这些是证书的一部分。第一分量返回映射写成

$$
 G_i(x)=A_i+ax,\qquad A_0\ne A_1,\qquad i=0,1.
$$

第二分量使用同一个返回词 $V$，其映射为

$$
 F(x)=y+a(x-y).
$$

以下 $J_c$ 是固定六格仪器的闭颜色区间，$E_c^\beta=J_c+[-\beta,\beta]$ 与物理支撑的交按已发表闭合同理解。记 stem 颜色块为 $H=(H_r)_{0\le r<d}$，第一返回颜色块为 $W_i=((W_i)_r)_{0\le r<L}$；同一 $W_i$ 也标在 rival 的共同返回 $V$ 上。所谓固定实际 $D/D$ 尾，是一次选定的两个实际地址 $\xi\in D_{s_1}$、$\eta\in D_{s_2}$；它们的来源标签、guard 接缝和尾字面量在所有 $z$ 中均不变。

令 $H_1=[u,v]$ 是第一分量两映射的规范最小不变区间，取一个固定实际尾标量

$$
 x_1\in T_{s_1}\cap(u,v),
$$

并取一个固定实际尾标量 $x_2=y+h\in T_{s_2}$. 对第一分量的每个实际 stem/return departure suffix $\alpha$，令 $f_\alpha$ 为该 departure 到所在 stem 或返回块末端的固定后缀映射，即 $f_{P[r:]}$ 或 $f_{U_i[r:]}$；完整历史的后缀再复合其后所有返回，$c_\alpha$ 为 $H_r$ 或 $(W_i)_r$，并要求有限证书

$$
 f_\alpha(H_1)\subseteq E_{c_\alpha}^{\beta}
 \qquad\text{for every such actual }\alpha.
$$

单独记 rival 的有限槽：对 stem $Q$ 的每个位置使用同一个 $H_r$，对共同返回 $V$ 的每个位置分别使用 $(W_0)_r$ 和 $(W_1)_r$. 对所得每一个实际槽 $\alpha$，令 $r_\alpha$ 为固定后缀 $f_{Q[r:]}$ 或 $f_{V[r:]}$，并要求

$$
 q_\alpha(0):=\beta-\operatorname{dist}(r_\alpha(y),J_{c_\alpha})\ge0,
 \qquad
 q_\alpha(1):=\beta-\operatorname{dist}(r_\alpha(x_2),J_{c_\alpha})>0.
$$

这里的 rival 清单分别包含两种 $W_i$ 发生，不能用一个颜色块代替；清单有限且每一项都来自实际 guard/source 词。对每个二进制词 $z=z_1\cdots z_k$（包括空词）固定来源

$$
 \alpha_z=PU_{z_1}\cdots U_{z_k}\xi,\qquad
 \beta_z=QV^k\eta,\qquad |z|=k,
$$

以及共同指定颜色历史 $H W_{z_1}\cdots W_{z_k}$. 每个观察都是 departure observation，位置为 $0\le r<d+kL$；终端坐标 $d+kL$ 没有额外颜色。

**证明。** 定理39.2.1和推论39.2.2给出 $H_1$、两返回的规范 hull 和 $A_0\ne A_1$；命题43.2给出所选 $\xi,\eta$ 的实际 $D$ 性。第一分量的有限证书逐一覆盖 $P$ 与 $U_i$ 的所有 departure suffix，rival 清单逐一覆盖 $Q$ 与 $V$ 的两种 $W_i$ 颜色，因此同一对尾对每个 $z$ 和每个 $k$ 都保留同一来源、guard、颜色和正 seed margin。$V$ 相同使 rival 轨道只由 $F^k(x_2)$ 决定；$U_0,U_1,V$ 本身都是回到声明 guard 的实际返回，所以每个拼接词的 guard 合法性来自来源证书，而不是由 hull 定理给任意词补出返回 guard。观察范围在终端之前，故未观察终端没有额外颜色。证毕。

**命题 43.12（第一分量的统一 margin，含物理裁剪）。** 在命题43.11的条件下，置

$$
 d_1=\min\{x_1-u,v-x_1\}>0.
$$

对第一分量任意 departure 槽，其完整后缀仿射映射 $f$ 的斜率绝对值为 $g^D$，其中 $D\ge1$ 是该 departure 到未观察终端的来源长度。若该槽在闭预算 $\beta$ 下有

$$
 f(H_1)\subseteq (J_{c}+[-\beta,\beta])\cap X,\qquad
 X=[-1,\phi],
$$

则

$$\boxed{\beta-\operatorname{dist}(f(x_1),J_c)\ge\min\{\beta,d_1\}g^D.}$$

因此对深度不超过 $n$ 的所有第一分量观察，统一有

$$
\beta-\operatorname{dist}(f(x_1),J_c)\ge c_1a^n,\qquad c_1=\min\{\beta,d_1\}g^d>0.
$$

**证明。** $f(H_1)$ 是一个闭区间，$f(x_1)$ 到它的两个端点均至少为 $d_1g^D$。若 $J_c=[l,r]$，在未裁剪扩张内有

$$
 \beta-\operatorname{dist}(q,J_c)=\min\{\beta,\ q-(l-\beta),\ (r+\beta)-q\}.
$$

物理支撑把扩张区间与 $X$ 相交。由于 $J_c\subseteq X$ 且 $f(x_1)\in f(H_1)\subseteq X$，到 $J_c$ 的距离仍是实轴上的距离；被裁剪的边界不会成为 $J_c$ 的新点，也不会减少 $f(x_1)$ 到原扩张两端的有效单侧距离。因此

$$
\beta-\operatorname{dist}(f(x_1),J_c)\ge\min\{\beta,d_1g^D\}\ge\min\{\beta,d_1\}g^D.
$$

一条深度 $k\le n$ 的历史的 departure 到终端长度满足 $D\le d+nL$；因 $g^D\ge g^{d+nL}=g^da^n$，得到结论。这个证明处理了物理支撑裁剪，没有把未裁剪端点当成实际目标。证毕。

**命题 43.13（rival 的凹余量，允许进入或穿过颜色格）。** 对命题43.11的每个第二分量槽 $\alpha$，令其后缀斜率为 $\gamma_\alpha=(-g)^{s_\alpha}$，并置

$$
 q_\alpha(t)=\beta-\operatorname{dist}\bigl(r_\alpha(y)+t\gamma_\alpha h,J_{c_\alpha}\bigr),\qquad 0\le t\le1.
$$

由于 $r_\alpha(y+t h)=r_\alpha(y)+t\gamma_\alpha h$ 沿同一合法 guard 区间的仿射像且位于物理支撑 $X$，而 $J_{c_\alpha}\subseteq X$，物理裁剪不改变到 $J_{c_\alpha}$ 的距离表达式。函数 $q_\alpha$ 在整个 $[0,1]$ 上都是凹函数；即使扰动进入或穿过颜色格，下列界仍成立。若 $q_\alpha(0)=0$，则

$$
 t q_\alpha(1)\le q_\alpha(t)\le|\gamma_\alpha h|t;
$$

若 $q_\alpha(0)>0$，则

$$
 q_\alpha(t)\ge\min\{q_\alpha(0),q_\alpha(1)\}>0.
$$

所以命题43.11的有限槽清单给出 $c_2>0$，使所有深度不超过 $n$ 的 rival departure 均满足

$$
\beta-\operatorname{dist}(r_\alpha(F^k(x_2)),J_{c_\alpha})\ge c_2a^n.
$$

**证明。** 到闭区间的距离是凸函数，故其负值加常数 $q_\alpha$ 凹；距离还是 1-Lipschitz，给出上界。由于 $F^k(x_2)=y+a^kh$，实际取值是 $q_\alpha(a^k)$。凹函数位于端点弦之上，分别得到两种下界。若 reference 值或固定尾值进入或穿过颜色格内部，公式仍只使用距离函数的凸性，不要求扰动停留在同一个外部侧；两端和整条线段均在 $X$ 内，所以物理裁剪不会改变所用距离。

槽数有限，取

$$
 c_2=\min_\alpha\begin{cases}
 q_\alpha(1),&q_\alpha(0)=0,\\
 \min\{q_\alpha(0),q_\alpha(1)\},&q_\alpha(0)>0
 \end{cases}>0.
$$

因 $k\le n$ 且 $a^k\ge a^n$，即得统一下界。证毕。

### 43.14 精确有限树成本及端点实现

**命题 43.14（所有长度不超过 $n$ 的精确闭成本）。** 令 $B_n$ 是命题43.11整棵树中所有实际来源、所有 departure 观察坐标到各自指定闭格的最大距离。若

$$
 c=\min\{c_1,c_2\}>0,
$$

则

$$
 B_n\le\beta-ca^n<\beta.
$$

$B_n$ 可由固定有限个实际端点公式精确取得。具体地，令

$$
 A_-=\min\{A_0,A_1\},\quad A_+=\max\{A_0,A_1\},\quad
 p_-=\frac{A_-}{1-a},\quad p_+=\frac{A_+}{1-a}.
$$

第一分量在所有至多 $N$ 个返回后的终端值的区间包络为

$$
 K_N^{(1)}=[\ell_N,u_N],
$$

$$
 \ell_N=\min\{x_1,p_-+a^N(x_1-p_-)\},\qquad
 u_N=\max\{x_1,p_++a^N(x_1-p_+)\}.
$$

第二分量包络为

$$
 K_N^{(2)}=[\ell_N^{(2)},u_N^{(2)}],\qquad
 \ell_N^{(2)}=\min\{x_2,y+a^N(x_2-y)\},\quad
 u_N^{(2)}=\max\{x_2,y+a^N(x_2-y)\}.
$$

令 $\mathscr F_{\rm st}$ 为第一分量的 stem 槽，$\mathscr F_{\rm ret}$ 为其两种返回槽，令 $\mathscr R_{\rm st}$ 为 rival 的 stem 槽，$\mathscr R_{\rm ret}$ 为 rival 的共同返回槽（各自带上 $W_0,W_1$ 两种颜色副本）。对 $\alpha\in\mathscr F_{\rm st}\cup\mathscr R_{\rm st}$ 取 $N_\alpha=n$；对 $\alpha\in\mathscr F_{\rm ret}\cup\mathscr R_{\rm ret}$ 在 $n\ge1$ 时取 $N_\alpha=n-1$，在 $n=0$ 时删去这些返回槽。若 $f_\alpha$ 是第一分量槽的固定后缀，$r_\alpha$ 是 rival 槽的固定后缀，则

$$
\begin{aligned}
 B_n=\max\Bigl(\{\operatorname{dist}(f_\alpha(\ell_{N_\alpha}),J_{c_\alpha}),
 \operatorname{dist}(f_\alpha(u_{N_\alpha}),J_{c_\alpha}):
 \alpha\in\mathscr F_{\rm st}\cup\mathscr F_{\rm ret}\text{ 当前存在}\}
 \\cup\{\operatorname{dist}(r_\alpha(\ell_{N_\alpha}^{(2)}),J_{c_\alpha}),
 \operatorname{dist}(r_\alpha(u_{N_\alpha}^{(2)}),J_{c_\alpha}):
 \alpha\in\mathscr R_{\rm st}\cup\mathscr R_{\rm ret}\text{ 当前存在}\}\Bigr).
\end{aligned}
$$

若这些有限槽在 $n=0$ 均为空，则约定 $B_0=0$；否则上式只取实际存在的槽。

每个列出的端点分别由一个实际词实现；该最大值不是把不同词的独立极值拼接成一条来源。

**证明。** 由于 $a>0$，固定长度 $k$ 的第一返回组合在 $x_1$ 上的最小值和最大值分别由全取 $A_-$ 和全取 $A_+$ 的词取得，所得值为

$$
 p_-+a^k(x_1-p_-),\qquad p_++a^k(x_1-p_+).
$$

对 $0\le k\le N$，每个序列单调趋向其固定点，所以全部实际点的最小值、最大值就是 $\ell_N,u_N$；若极值为 $x_1$，由空词取得，若为迭代值，使用重复极值返回取得。第二分量只有一个返回映射，故其两个端点由空词或重复 $V$ 取得。

任一第一分量 departure 坐标是其终端值经 $f_\alpha$ 得到，任一 rival 坐标是其终端值经 $r_\alpha$ 得到。距离到闭区间是凸函数，在相应闭区间 hull 上的最大值出现在端点，因此上述分量特定的有限清单给出上界。反过来每个端点都由实际词取得，清单中的每一项都是一个真实历史的成本；其中最大的那一项也被实际取得，故等式成立。stem 槽的 $N=n$、返回槽的 $N=n-1$ 正是因为观察发生在当前返回块离开时，当前块之后还剩这些返回；终端本身未观察，所以没有额外颜色项。命题43.12和43.13给出每个项的统一 margin，因而 $B_n\le\beta-ca^n$；若没有观察项则 $B_0=0$。证毕。

**命题 43.15（边界层、$n=0$ 和单支 tight）。** 命题43.14同时包括以下情形：

1. $n=0$ 时只有 stem departure 槽；没有人为加入终端颜色，若没有任何 departure，则 $B_0=0$。
2. 若周期参考的 tight 值只在 stem 槽中出现，该 stem 槽在 $n=0$ 已存在，但其有限层成本仍由 $N=0$ 的实际端点词计算；周期 tight 参考通常只在返回次数趋于无穷时达到，不能说空词已经取得 $\beta$. 命题43.11的严格 seed margin 也排除了把有限 $D$ 尾直接当作该周期等号。
3. 若周期参考的 tight 值只在一条返回中，该返回槽从 $n=1$ 起才出现；“首取该返回”只实现其第一次有限层端点，参考 tight 值要在其后接更多返回时逼近。$n=0$ 不包含该槽，不能把参考等号反向计入 $B_0$。
4. 一个被选作极限锁的 rival 槽必须是清单中确实观察到的槽；别的颜色的 tight 端点或规范包络的任意端点不提供这个锁。

**证明。** 这些都是命题43.14中当前槽集合和端点实际词的直接分情况。返回槽的第一次出现需要一次返回，故其后缀返回数为 $n-1$；stem 槽从空词开始，故为 $n$。任何未观察终端都不产生颜色条件。证毕。

### 43.16 指数尾与实际阈值

**命题 43.16（选定 rival tight 锁下的双侧指数界）。** 假设命题43.11的槽清单中选定一个实际 rival 槽 $\alpha_\star$，满足

$$
 q_{\alpha_\star}(0)=0,\qquad q_{\alpha_\star}(1)>0.
$$

也就是该选定观察槽的周期极限成本恰为 $\beta$，而同一固定实际尾在该槽留下严格 seed margin。则存在常数 $C\ge c>0$，对所有 $n\ge0$ 有

$$\boxed{c\,g^{Ln}=c\,a^n\le\beta-B_n\le C\,a^n=C\,g^{Ln},}$$

并且 $B_n\uparrow\beta$。存在 $n_0$ 和 $\kappa>0$ 使

$$\boxed{B_n=\beta-\kappa a^n\qquad(n\ge n_0).}$$

**证明。** 下界已由命题43.14给出。对上界，若 $\alpha_\star$ 是 stem 槽，取恰有 $n$ 个返回的实际 stem 词。由距离的 1-Lipschitz 性质和 $q_{\alpha_\star}(0)=0$，

$$
 0\le q_{\alpha_\star}(a^n)\le|\gamma_{\alpha_\star}h|a^n,
$$

所以该实际槽给出

$$
 \beta-B_n\le|\gamma_{\alpha_\star}h|a^n.
$$

若它只在一个返回内部出现，则对 $n\ge1$ 取以该返回开头、其后接 $n-1$ 个返回的实际词，得到

$$
 \beta-B_n\le|\gamma_{\alpha_\star}h|a^{n-1}
 =a^{-1}|\gamma_{\alpha_\star}h|a^n.
$$

$n=0$ 的返回槽不存在，但 $\beta-B_0\le\beta$；把 $\beta$ 加入 $C$ 即得所有 $n$ 的上界。于是 $B_n\to\beta$，而嵌套历史给出单调非降。

为得到最终精确式，把命题43.14中的 $\ell_N,u_N$ 按固定符号分支展开。对 $n\ge1$ 置 $z=a^n$；stem 端点是 $z$ 的仿射函数，返回端点是 $z/a$ 的仿射函数。对闭格 $J=[l,r]$，

$$
 \operatorname{dist}(x,J)=\max\{l-x,0,x-r\}.
$$

所以存在一个固定有限集 $\mathcal F$ 和域内常数 $b_j,k_j$，使

$$
 B_n=\max_{j\in\mathcal F}(b_j+k_j a^n),\qquad n\ge1.
$$

令 $B_*=\max_jb_j=\sup_nB_n$。选定的 rival tight 槽和上界已经给 $B_*=\beta$。令

$$
 k_*=\max\{k_j:b_j=\beta\}.
$$

单调性和 $B_n<\beta$ 强迫 $k_*<0$：若 $k_*>0$，最终会超过 $\beta$；若 $k_*=0$，最终最大值会等于 $\beta$，也与命题43.14的严格 margin 矛盾。有限个截距小于 $\beta$ 的直线最终低于截距为 $\beta$、斜率为 $k_*$ 的直线，因此某个 $n_0$ 后

$$
 B_n=\beta+k_*a^n=\beta-\kappa a^n,\qquad\kappa=-k_*>0.
$$

这条上界锁来自 $\alpha_\star$ 的实际周期极限，未使用无关颜色或任意扩大后的 hull 端点。证毕。

**命题 43.17（没有选定 tight 锁时的正确中心）。** 若不具备命题43.16的选定 tight 槽，则有限仿射包络仍给出

$$
 B_n=\max_{j\in\mathcal F}(b_j+k_ja^n)\quad(n\ge1),\qquad
 B_*=\sup_nB_n=\max_jb_j,
$$

并且存在 $n_0$ 及 $k_*\le0$ 使

$$
 B_n=B_*+k_*a^n\quad(n\ge n_0).
$$

此时只能以实际族阈值 $B_*$ 为中心；若写 $\kappa=-k_*$，它可以为零。不能把 $B_*$ 替换成给定的 $\beta$，也不能由没有 tight 锁的 margin 证明 $\beta-B_n=\Theta(a^n)$。

这里仍须保留命题43.11的逐槽严格 seed margin；删去它，命题43.14的正下界 $c a^n$ 以及任意归属下的严格放松都不再成立。

**证明。** 有限直线最大值的最终支配项证明与命题43.16相同。因 $B_n\le B_*$，最终斜率不能为正；斜率为零允许 $\kappa=0$。没有任何步骤把 $B_*$ 识别为外加预算 $\beta$。证毕。

### 43.18 精确闭成本的 owned 实现

**命题 43.18（精确 $B_n$ 的端点归属条件）。** 固定一个具体归属 $\omega$，令 $C_{c,\omega}$ 是颜色 $c$ 的实际拥有区间，$J_c=\overline{C_{c,\omega}}$。在预算恰为 $B_n$ 时，整棵深度不超过 $n$ 的树可实际取得，当且仅当每一个达到最大值的实际三元组

$$
 (\text{word},\text{component},\text{departure slot})
$$

的最近点投影 $\operatorname{proj}_{J_c}(x)$ 属于 $C_{c,\omega}$。最大值相等的所有三元组都必须满足这个 endpoint flag；只检查一个周期词或一个 tight 颜色不够。

等价地，只需检查命题43.14的有限清单中每个现存槽的两个实际极端坐标都属于 $O_{c,\omega}^{B_n}$；其中 $O_{c,\omega}^{B_n}$ 按本章开头的拥有格定义。正距离等号处使用最近端点旗标，零距离等号处检查实际坐标归属。这个条件包括 $B_n=0$；若没有观察，条件为空。

当 $B_n=0$ 时，这一条件退化为每个实际观察坐标本身属于其被指定归属的颜色区间；不能因坐标落在闭格端点就自动取得。

**证明。** 命题43.14说明每个端点极值由实际词取得，故逐槽两端属于 $O_{c,\omega}^{B_n}$ 是必要条件。该拥有扩张仍是区间；两端均属于它时，它包含整个两端之间的线段，因而包含该槽的每个实际坐标，给出充分性。不同槽的端点见证可以来自不同词，未把它们拼成独立来源。若某一实际坐标的距离严格小于 $B_n$，则由 $O_c^{B_n}$ 的开端点性质，可以把最近目标略移入其拥有的颜色区间而仍不超过预算。若距离等于 $B_n$，最近闭格点是唯一不增距离的候选；它不属于 $C_{c,\omega}$ 时，任何拥有目标都要增加距离，故不能在精确预算取得。逐个应用于所有实际达到 $B_n$ 的三元组即得充要性。$B_n=0$ 时没有严格余量，所有坐标都属于等号情形。证毕。

**命题 43.19（严格更大但仍低于 $\beta$ 的预算）。** 在命题43.14的严格 margin 条件下，任意

$$
 B_n<b<\beta
$$

都允许同一对固定实际 $D/D$ 尾承担整棵深度不超过 $n$ 的树，并且对每一种端点归属都可逐槽选择拥有区间内部的目标。一个明确选择是

$$
 b=\frac{\beta+B_n}{2}.
$$

若命题43.16成立，则任意固定 $b<\beta$ 都不能承担所有深度的同一无界二返回族。

**证明。** $B_n<b$ 使每个实际观察坐标严格落在相应闭格的预算扩张内部；实际颜色区间的内部目标遂可在距离 $b$ 内选取。来源、stem、返回和两个尾均没有改变。若固定 $b<\beta$ 支持全部深度，则必须有 $B_n\le b$ 对所有 $n$；命题43.16给出的 $B_n\uparrow\beta$ 与此矛盾。证毕。

### 43.20 量词和观察历史的边界

**命题 43.20（来源词、观察词与已证明的树族）。** 命题43.11—43.19证明的是：对每个 $n$ 和每个 $|z|\le n$，同一对固定实际 $D/D$ 尾使指定的来源词和 departure 颜色历史满足相应预算。它没有把 $2^n$ 个来源词自动识别成 $2^n$ 个不同观察历史。

若另要推出不同历史，必须额外同时满足预算处于已发表有限来源唯一性合同的适用范围、两条来源的完整未来满足该合同的共同未来要求，以及来源词确实不同；本章的两条固定尾本身不替代这些假设。

**证明。** 来源词由 $U_0\ne U_1$ 的字面分支区分，但颜色投影可能在有限前缀上相同。已发表[定理28.1](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L7165)和[推论29.3](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L7632)在其完整闭关系、实际有限来源和共同完整记录前提下才给单点纤维；没有这些前提，来源词计数只说明构造了多少来源实例，不说明观察历史的基数。故本章保留两种量词，不作未经证明的历史计数。证毕。

### 43.21 新增内容与既有算术的分界

**命题 43.21（本章新增桥接的闭合范围）。** 条带、guard 满像和 $D$ 单射性作为已发表前提；本章的新增桥接仅为：

1. 复用约定1.3、定理34.3和命题35.9的 strip arithmetic、定义14.5、命题14.6及定理14.7的实际 guard 与 $D$ 单射性；新的内容只是把这些已发表条件应用为两个同时满足的 $T_s$ 尾判据；
2. 给出等号相同幅度的同号共同证书、相反号纯周期共轭障碍、零方向条件及 PA/PB 实例；
3. 用当前出现的 active 槽定义 $\gamma_n$，并逐槽确定精确等号的 ownership flags；
4. 对固定 stem、固定等长偶返回、同一 rival 返回和固定 D/D 尾，给出全树的逐端点 $B_n$、指数界和最终有限仿射式；
5. 对双非退化负斜率包络给出全槽奇偶成本尾式及实际平台例，并在另加 H+、真正分歧词干和完整恢复合同后代入既有配置计数。

规范 hull 的最小性、guard 满像、有限来源唯一性、六周期观察数据和闭格端点定义仍是已发表输入。上述结论不扩展为全局 $R$ 的取得性、不扩展为所有归属的统一记忆常数，也不把有限来源数量当作执行、枚举或形式验证。

**证明。** 第一项的条带和有限来源部分是已发表命题的复用，新增部分是它在 simultaneous-tail 问题中的合取应用。第二、三项由命题43.4—43.10证明，第四项由命题43.11—43.19证明，第五项由推论43.22、例及推论43.23和推论43.24证明；其余输入只在所标出的已有命题处使用。每次使用都保留了实际 guard、来源标签、共同历史、固定尾和未观察终端的量词，因此没有引入超出本章范围的对象。证毕。

### 43.22 负返回的余量交换与奇偶预算尾式

固定[定义39.1.2](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13209)中的合法来源数据：$P,Q$ 从 guard 零进入 $s_1,s_2$，共同颜色词为 $h$，且 $|P|=|Q|=|h|=m\ge0$；$U_i,V_i$ 分别合法返回各自 guard，$W_i$ 为指定共同颜色词，且

$$
|U_i|=|V_i|=|W_i|=L\ge1,\qquad U_0\ne U_1.
$$

一次固定实际尾 $\xi_1\in D_{s_1}$、$\xi_2\in D_{s_2}$。每个二进制词 $z=z_1\cdots z_k$ 同时指定

$$
\alpha_z=PU_{z_1}\cdots U_{z_k}\xi_1,\qquad
\beta_z=QV_{z_1}\cdots V_{z_k}\xi_2,\qquad
h_z=hW_{z_1}\cdots W_{z_k}.
$$

两来源都在 $D$ 中。历史长 $m+kL$，只观察各条来源的出发坐标 $0,\ldots,m+kL-1$；终端坐标未观察。两个分量始终使用同一个 $z$，不逐坐标另选来源。

**推论 43.22（双内部尾的负斜率有限预算）。** 设 $L$ 为奇数，$a=(-g)^L=-r$，$0<r=g^L<1$。两个分量的返回映射为

$$
G_{ji}(x)=A_{ji}-rx,\qquad
A_j^-:=\min_iA_{ji}<\max_iA_{ji}=:A_j^+\quad(j=1,2).
$$

使用定理39.2.1的两个非退化规范包络

$$
H_j=[m_j,M_j],\qquad
m_j=\frac{A_j^- -rA_j^+}{1-r^2},\qquad
M_j=\frac{A_j^+ -rA_j^-}{1-r^2},
$$

并假定固定尾标量 $x_j=\kappa_{s_j}(\xi_j)$ 满足 $m_j<x_j<M_j$。

完整槽清单保留每个分量、每个位置和两种返回：stem 条目为 $(f_{P[\rho:]},h_\rho)$、$(f_{Q[\rho:]},h_\rho)$，$0\le\rho<m$；返回条目为 $(f_{U_i[\rho:]},(W_i)_\rho)$、$(f_{V_i[\rho:]},(W_i)_\rho)$，$i=0,1$、$0\le\rho<L$。以 $\alpha$ 索引这 $2m+4L$ 个条目，记它的分量为 $j(\alpha)$、颜色为 $c_\alpha$、非空后缀映射为 $f_\alpha$，其斜率为

$$
\gamma_\alpha=(-g)^{s_\alpha}\ne0,\qquad s_\alpha\ge1.
$$

stem 槽置 $d_\alpha=0$，返回槽置 $d_\alpha=1$。假定完整规范闭阈值

$$
\theta=\max_\alpha\max\{
\operatorname{dist}(f_\alpha(m_{j(\alpha)}),J_{c_\alpha}),
\operatorname{dist}(f_\alpha(M_{j(\alpha)}),J_{c_\alpha})\}>0.
\tag{43.22.1}
$$

令 $B_n$ 为全部 $|z|\le n$ 的两分量、全部指定出发观察到相应闭格的最大距离；没有观察时定义 $B_n=0$。则 $B_n$ 是该有限族的精确闭成本，

$$
B_n<\theta\quad(n\ge0),\qquad B_n\uparrow\theta.
\tag{43.22.2}
$$

存在 $n_0\ge2$ 及 $\kappa_0,\kappa_1>0$，使

$$
B_n=\theta-\kappa_{n\bmod2}r^n\quad(n\ge n_0),\qquad
r\kappa_0\le\kappa_1\le\kappa_0/r.
\tag{43.22.3}
$$

因而最终 $B_{n+2}>B_n$；相邻层允许平台。两个系数由下面的完整临界端点公式确定。

**证明。** 先固定一个分量，省略下标。规范端点满足 $m=A^- -rM$、$M=A^+ -rm$。记固定长度 $k$ 的实际最小值、最大值为 $m_k,M_k$，从 $m_0=M_0=x$ 出发。负斜率使

$$
m_k=A^- -rM_{k-1},\qquad M_k=A^+ -rm_{k-1}.
\tag{43.22.4}
$$

两极值都由实际词取得：最小值的外层用最小平移返回，内层用最大值的见证；最大值反之。递归得到交替使用极小、极大平移的长度 $k$ 词。这个构造不要求吸引子填满 $H$。

置 $D^-=x-m>0$、$D^+=M-x>0$。从(43.22.4)减去规范端点等式，左右余量每步交换并同乘 $r$，故

$$
\begin{array}{c|cc}
 &m_k-m&M-M_k\\ \hline
k\text{ 偶}&r^kD^-&r^kD^+\\
k\text{ 奇}&r^kD^+&r^kD^-
\end{array}.
\tag{43.22.5}
$$

同一奇偶类的余量随长度严格减小。因此深度不超过 $N\ge1$ 时，两端分别比较长度 $N$ 和 $N-1$；两个候选长度的极值均实际取得。定义

$$
p_j=\min\{D_j^-,D_j^+/r\},\qquad
q_j=\min\{D_j^+,D_j^-/r\}>0.
$$

由 $rp_j=\min\{rD_j^-,D_j^+\}\le q_j$ 及 $rq_j=\min\{rD_j^+,D_j^-\}\le p_j$，有 $rp_j\le q_j\le p_j/r$。该分量全部 $|z|\le N$ 的标量凸包恰为

$$
K_{j,N}=\begin{cases}
[m_j+r^Np_j, M_j-r^Nq_j],&N\ge1\text{ 偶},\\
[m_j+r^Nq_j, M_j-r^Np_j],&N\text{ 奇},\\
\{x_j\},&N=0.
\end{cases}
\tag{43.22.6}
$$

前两行的每个端点由某个长度 $N$ 或 $N-1$ 的交替极值词取得；$N=1$ 时包括空词。$N=0$ 只有固定尾，必须单列，不能把裁掉另一奇偶类余量后的 $p_j,q_j$ 公式代入零层。

对于深度 $n$，stem 槽的全部后续词为 $|w|\le n$；返回槽的全部后续词为 $|w|\le n-1$，它们由词 $iw$ 实现。更早的块不改变当前出发坐标的后缀值。因此置

$$
N_\alpha(n)=n-d_\alpha,
$$

其中返回槽只在 $n\ge1$ 存在；$n=0$ 删除全部返回槽。记 $K_{j,N}=[\ell_{j,N},u_{j,N}]$，允许两端相等，得到精确式

$$
B_n=\max_{\alpha\ \mathrm{现存}}\max\{
\operatorname{dist}(f_\alpha(\ell_{j(\alpha),N_\alpha(n)}),J_{c_\alpha}),
\operatorname{dist}(f_\alpha(u_{j(\alpha),N_\alpha(n)}),J_{c_\alpha})\}.
\tag{43.22.7}
$$

空最大值按最小非负成本取零，故空 stems 时 $B_0=0$。终端未观察，没有额外末端颜色槽。距离闭区间是凸函数，给出(43.22.7)的上界；两端实际取得，给出必要下界，负后缀斜率也已由同时测两端处理。不同分量或槽的最大值见证可以是不同的词，但每个见证都使用同一 $z$ 指定的两条完整来源。这里没有把边际最优坐标拼成一个联合来源。

每个有限返回复合把内部尾送进 $\operatorname{int}H_j$，由(43.22.5)也可见两端余量严格为正。每个 $f_\alpha(H_j)$ 非退化，且由(43.22.1)包含于未裁剪扩张 $J_{c_\alpha}+[-\theta,\theta]$。内部点的像严格位于该扩张两端之间，$\theta>0$ 因而使距离严格小于 $\theta$。物理裁剪的区间包含同样蕴含这个未裁剪包含，不增加成本。有限族给 $B_n<\theta$。族包含给单调非降；(43.22.6)的两端趋于规范两端，(43.22.7)遂给 $B_n\to\theta$。这也直接核对了(43.22.1)作为该固定尾族的真实全深度闭阈值，与定理39.3.2一致。

为计算尾式，记 $e_j^-=m_j,e_j^+=M_j$，并定义

$$
\eta_{j,-,0}=p_j,\quad\eta_{j,+,0}=q_j,\qquad
\eta_{j,-,1}=q_j,\quad\eta_{j,+,1}=p_j.
$$

完整临界端点集为

$$
\mathcal A=\{(\alpha,e):e\in\{-,+\},
\ \operatorname{dist}(f_\alpha(e_{j(\alpha)}^e),J_{c_\alpha})=\theta\}.
$$

它非空。固定 $\sigma=n\bmod2$，$n\ge2$ 时槽端点的规范余量恰为

$$
r^n r^{-d_\alpha}\eta_{j(\alpha),e,\,\sigma\oplus d_\alpha},
$$

其中 $\oplus$ 是模二加法。临界端点的像距闭格为正，且必为像区间在该侧的最外端；否则另一个端点的距离会大于 $\theta$，违背(43.22.1)。因此向像区间内部移动充分小的距离，格外距离恰减少同样大小。故其临界距离线性支的系数为负，绝对值为 $|\gamma_\alpha|r^{-d_\alpha}\eta_{j(\alpha),e,\sigma\oplus d_\alpha}$。于是最终系数的完整公式为

$$
\boxed{\displaystyle
\kappa_\sigma=
\min_{(\alpha,e)\in\mathcal A}
|\gamma_\alpha|\,r^{-d_\alpha}
\eta_{j(\alpha),e,\,\sigma\oplus d_\alpha}>0.}
\tag{43.22.8}
$$

这里每个候选均正，直接证明两个系数正。还需排除非临界端点在任意晚层重新支配：(43.22.6)—(43.22.7)及
$\operatorname{dist}(y,[l,u])=\max\{l-y,0,y-u\}$ 把每种奇偶的 $B_n$ 写成固定有限条 $b_h+s_hr^n$ 的最大值。最大截距为 $\theta$；截距等于 $\theta$ 的支恰来自上述临界端点，最大斜率为 $-\kappa_\sigma$。对于 $b_h<\theta$ 且 $s_h> -\kappa_\sigma$ 的支，只需令

$$
r^n\le\frac{\theta-b_h}{s_h+\kappa_\sigma};
$$

其他较低截距支自动不超过临界最大支。有限个正右端允许选择共同 $n_0\ge2$，证明(43.22.3)的精确尾式。

把尾式代入 $B_{n+1}\ge B_n$，偶层到奇层给 $\kappa_0\ge r\kappa_1$，奇层到偶层给 $\kappa_1\ge r\kappa_0$，即所列兼容不等式。两层之差始终为

$$
B_{n+2}-B_n=\kappa_{n\bmod2}r^n(1-r^2)>0\quad(n\ge n_0).
$$

若 $\kappa_0=r\kappa_1$，最终偶层到奇层为平台；若 $\kappa_1=r\kappa_0$，最终奇层到偶层为平台。两等号不能同时成立；两不等式都严格时才有最终逐相邻层严格增长。例及推论43.23给出实际平台。$\square$

**精确归属与较大预算。** 对任一固定合法归属，预算恰为 $B_n$ 时的充要条件是(43.22.7)中每个现存槽的两端实际坐标都属于 $O_{c_\alpha}^{B_n}$。必要性来自端点见证；充分性来自 $O_{c_\alpha}^{B_n}$ 的区间性。按开头的投影规则检查等号端点即可；$B_n=0$ 时仍保留实际坐标归属，空观察则无约束。闭格最短距离在 $J_i\subset X$ 中取得，裁剪不改变闭成本。

任意 $b>B_n$ 都可把这有限族的全部目标选在指定格内部，并保持每个误差严格小于 $b$，因此适用于每一种固定合法归属，且来源、共同词和两条实际尾不变。例如 $b_n=(\theta+B_n)/2<\theta$ 实现全部 $|z|\le n$，包括空词。由于 $B_n\uparrow\theta$，任何一个固定 $b<\theta$ 都不能覆盖这个同一无界族。在 $\theta$ 的全族内部尾归属结论与定理39.4.1一致。本推论要求两个非退化包络，不转移到单点竞争包络；后者应使用[定理39.5.2](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13415)的旗标轨道判据。

### 43.23 实际六格中的永久相邻平台

**例及推论 43.23（固定合法尾的次临界平台）。** 取空且相同的 stems、guard 零，并取窗口标签词

$$
L=3,\quad r=g^3,\qquad
U_0=V_0=000,\quad U_1=V_1=200,\qquad
W_0=111,\quad W_1=311.
$$

此处 $000,200$ 分别表示三个来源窗口标签，$111,311$ 表示三个颜色。所有来源标签 $0,2$ 都是实际 $0\to0$ 边。一次固定两条相同的最终空尾

$$
\xi_1=\xi_2=(0,0,0,2)0^\infty\in D_0,
\qquad x_1=x_2=(-g)^3=-r.
$$

所以每个共同选择词给出的两来源完全相同且合法，$G_0(x)=-rx$、$G_1(x)=1-rx$，两个非退化包络相同：

$$
H=[m,M]=\left[-\frac r{1-r^2},\frac1{1-r^2}\right],\qquad m<-r<M.
\tag{43.23.1}
$$

其完整阈值与全部有限深度成本为

$$
\theta=M-q_4\in(0,\lambda),\qquad B_0=0,
\qquad
\boxed{B_{2j+1}=B_{2j+2}
=\theta-\frac{r^{2j+4}}{1-r^2}\quad(j\ge0).}
\tag{43.23.2}
$$

每一对平台的最大值由实际选择词 $1(01)^j$ 取得。对于每个 $n\ge1$，在恰好成本 $B_n$ 下实际取得全部指定颜色，当且仅当切点 $q_4$ 属于颜色3；$n=0$ 无观察，不需要该条件。

**证明。** 所需常数界可以完全用有理数证明。$g>0$ 且 $g^2+4g-1=0$；多项式 $F(u)=u^2+4u-1$ 在 $u\ge0$ 上严格递增，而

$$
F(72/305)=-\frac1{93025}<0,
\qquad F(17/72)=\frac1{5184}>0.
$$

又 $72\cdot72=5184<5185=17\cdot305$，故

$$
\frac{72}{305}<g<\frac{17}{72}<\frac14,
\qquad r<\frac1{64},\qquad
M<\frac{4096}{4095}<\frac{65}{64}.
\tag{43.23.3}
$$

两个返回的全部非临界出发后缀只有 $0,00,000$，指定颜色均为1。其包络像分别为

$$
f_0(H)=[-gM,grM],\qquad
f_{00}(H)=[-g^2rM,g^2M],\qquad
f_{000}(H)=[-rM,r^2M].
$$

所有这些像的下端大于 $-65/256$，上端小于 $65/1024$。由 $t^2=(1-g)/2$ 得

$$
q_1=-\frac{11(1-g)}{20}< -\frac{33}{80}< -\frac{65}{256},
\qquad
q_2=\frac{23g-3}{20}>\frac{741}{6100}>\frac{65}{1024}.
$$

最后两个比较分别由 $33\cdot256>65\cdot80$ 与 $741\cdot1024>65\cdot6100$ 得到。因此每个非临界后缀的整个像都在 $\operatorname{int}J_1$，其所有有限来源坐标均有零成本，并实际属于颜色1。这覆盖返回0的三个位置及返回1的后两个位置，两个分量均如此；空 stems 没有其他槽。

唯一正成本类型是返回1的首位置、颜色3。该后缀为 $200$，所以

$$
G_1(H)=[1-rM,M],\qquad
1-rM>\frac{4031}{4096}>\frac{31}{32},
\qquad q_4=\frac{13+27g}{20}<\frac{31}{32}.
$$

其中 $q_4$ 的上界使用 $g<17/72$，因为 $(13+27\cdot17/72)/20=31/32$。整个像严格在 $J_3$ 上方，最大闭距离遂为 $\theta=M-q_4>0$。另一方面 $\lambda=(1-g)/20$，所以

$$
q_4+\lambda=\frac{7+13g}{10}
>1+\frac{21}{3050}
>\frac{4096}{4095}>M.
$$

第一个不等式用 $g>72/305$，第二个等价于 $21\cdot4095>3050$。于是 $\theta<\lambda$，没有借助小数近似。

固定尾余量及不超过深度的系数为

$$
D^-=(-r)-m=\frac{r^3}{1-r^2},\qquad D^+=M+r,
\qquad
p=\frac{r^3}{1-r^2},\quad q=\frac{r^2}{1-r^2},\quad p=rq.
$$

这些最小值选择确实成立：$D^-<D^+/r$ 等价于 $1+r-r^3-r^4=(1+r)(1-r^3)>0$；$D^-/r<D^+$ 等价于 $1+r-r^2-r^3=(1+r)(1-r^2)>0$。唯一临界规范端点是返回1的下端 $m$，它经 $G_1$ 反向映成 $M$。在(43.22.8)中 $d_\alpha=1$、$|\gamma_\alpha|=r$，因此

$$
\kappa_0=q=\frac{r^2}{1-r^2},\qquad
\kappa_1=p=\frac{r^3}{1-r^2}=r\kappa_0.
$$

还须证明(43.23.2)对全部深度成立。$n=1$ 的返回后续深度为零，$G_1(x)=1+r^2=M-r^4/(1-r^2)$，故直接给所列 $B_1$。若 $n=2j+1$、$j\ge1$，返回槽后续深度 $N=2j$，(43.22.6)给最低标量 $m+r^{2j+3}/(1-r^2)$。若 $n=2j+2$、$j\ge0$，$N=2j+1$ 给相同最低标量。经 $G_1$ 后最高坐标均为

$$
M-\frac{r^{2j+4}}{1-r^2}.
$$

所有颜色3坐标在 $J_3$ 上方，其他槽零成本，所以这恰为最大成本坐标。交替词 $(01)^j$ 在长度 $2j$ 取得固定长度最小值

$$
G_{(01)^j}(x)=m+r^{2j}D^-.
$$

前接返回1便得见证词 $1(01)^j$，长度 $2j+1$，同时属于深度 $2j+1$ 和 $2j+2$ 的树。$j=0$ 就是词1。因而最大值确实取得，偶数平台没有漏掉别的槽。

对 $n\ge1$，$B_n>0$。在达到最大值的颜色3槽，预算 $B_n$ 只能使用唯一最近目标 $q_4$，故必须 $q_4\in C_3$。反向，若该端点归属颜色3，所有最大槽都可用它；其他颜色3槽距离小于 $B_n$，可用格内部目标；所有颜色1槽已在内部，误差可取零。于是条件充分。深度零的空历史成本为零且无归属检查。$\square$

此例证明永久相邻平台在实际 FIB 六格和固定内部 D/D 尾中发生。两条 stems 空且相同，不能从这里推出分歧 SCC、来源竞争或完整记忆下界。

### 43.24 条件正尾式的预算缺口与配置容量

这里使用[定义36.9](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L11179)的完整记忆合同，并复用[定理36.25](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L11832)的联合配置计数及[第38.6节](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md#L13043)的共同第一未来论证。不另假定或构造 SCC。

**推论 43.24（H+ 下的有限视界容量代入）。** 固定合法入口词 $P,Q$，分别从 guard 零进入 $s_1,s_2$，共同颜色词为 $h$，$|P|=|Q|=|h|=m$。固定实际尾 $\xi_j\in D_{s_j}$，以及合法自返回 $U_i,V_i$ 和共同颜色块 $W_i$，$|U_i|=|V_i|=|W_i|=L$，其中 $L$ 为偶数、$a=g^L\in(0,1)$、$U_0\ne U_1$。要求 stems 真正分歧：其首次不同位置为固定 $k<m$。共同二进制词定义

$$
\alpha_z=PU_{z_1}\cdots U_{z_{|z|}}\xi_1,\qquad
\beta_z=QV_{z_1}\cdots V_{z_{|z|}}\xi_2,\qquad
h_z=hW_{z_1}\cdots W_{z_{|z|}}.
$$

两来源经过 $m+|z|L$ 个指定出发观察及来源边后终端未观察；第一来源都接同一固定实际尾 $\xi_1$ 的零误差完整未来 $S_{\xi_1}$。以全部 $|z|\le n$ 的两分量、全部指定出发槽到相应闭格的最大距离定义精确成本 $B_n$，没有观察时成本为零，并包括空词。

明确采用以下附加假设 **H+**：上述一个固定实际族的全部 $|z|\le n$ 的精确闭成本为 $B_n$；存在固定 $\beta,\kappa>0$ 及整数 $n_0\ge1$，使

$$
B_n=\beta-\kappa a^n\qquad(n\ge n_0).
\tag{43.24.1}
$$

H+ 包括字面固定尾与全槽成本，不由一条形式上的正斜率映射或供应构造的名称自动保证。它在这里是显式条件，没有证明这类实际族存在。命题43.16只有在命题43.11的全部实际证书、逐槽严格种子余量和所选 rival tight 锁均成立时才供应这条尾式；要用于本推论，还须另有真正分歧词干及下述实际共同第一未来和恢复合同。例及推论43.23的相同空词干不满足这些分歧条件。

固定预算 $b=\beta-\delta$，满足

$$
0<\delta<\min\{\beta,\kappa a^{n_0}\}.
\tag{43.24.2}
$$

并要求 $b$ 属于所采用恢复合同的预算范围；在亚临界应用中明确保留 $0<b<\lambda$。固定一次合法归属，并取在这个预算与归属下满足完整恢复合同的解码器 $\mathcal A$：它确定、因果、从固定初态出发，每次取得允许有限计算和有限输出批次；输出按序只追加且不可回读；它在全部实际 $\Omega$ 记录上安全，在全部实际 $D$ 记录上逐位置最终生效，包括无限空窗补齐。没有 End、支持上界或免费重放。

完整配置计入所有能影响未来的可读控制、持久与临时数据、计数器、输入及输出位置、时序、可读时钟和输出侧信息。记 $\mathcal C_{b,\mathcal A}(M)$ 为处理完恰好 $M$ 次取得后，在全部实际记录上可能出现的完整配置数。配置可分布在不同记录上。

置

$$
T=\frac{\log(\kappa/\delta)}{\log(1/a)},\qquad
n=\lceil T\rceil-1,\qquad M_n=m+nL,\qquad
\rho=\frac{\log2}{\log(1/a)}.
$$

则 $n\ge n_0$、$B_n<b$，并有

$$
\boxed{\displaystyle
\mathcal C_{b,\mathcal A}(M_n)\ge\frac{2^n}{k+1}
\ge\frac{1}{2(k+1)}
\left(\frac{\kappa}{\delta}\right)^\rho.}
\tag{43.24.3}
$$

**证明。** 条件(43.24.2)给 $T>n_0$。若 $T=q$ 为整数，则 $n=q-1$，且 $\kappa a^n=\delta/a>\delta$；取 $q$ 只会得到等号成本。若 $q<T<q+1$，则 $n=q<T$，仍有 $\kappa a^n>\delta$。两种情形均有

$$
n\ge n_0,\qquad T-1\le n<T,\qquad
B_n=\beta-\kappa a^n<\beta-\delta=b.
\tag{43.24.4}
$$

所以这是尾式范围内满足严格成本不等式的最大整数深度。每个指定坐标到闭格的距离小于 $b$，可把最近目标略移入指定格内部而保持误差小于 $b$。深度 $n$ 的树有限，因此两分量可选一个共同的严格误差上界小于 $b$，两条固定尾保持不变。分别接各自零误差未来得到完整实际记录，适用于任意固定合法归属，也适用于正开及逐记录严格余量合同。

现对 $|z|=n$ 的 $2^n$ 个历史使用既有计数。等长且不同的第一返回使 $z\mapsto\alpha_z$ 单射。若两个历史相同，第一来源接同一个 $S_{\xi_1}$ 会有相同完整实际记录，安全性与 $D$ 上逐位置生效将迫使两个来源相同，矛盾；所以历史也不同。每个历史都有第二来源的实际延续，安全性把此刻旧输出限制为两 stems 的共同前 $k$ 标签的某个前缀，至多 $k+1$ 个值。旧输出不可回读，仅作为这个有限集合参与计数。

记此刻完整配置为 $c_z$、旧输出为 $o_z$。若不同 $z,z'$ 的 $(c_z,o_z)$ 相同，继续读取同一个第一来源未来 $S_{\xi_1}$，确定性给相同未来输出；加上相同旧输出，与两个不同 $D$ 来源的逐位置生效矛盾。因此 $2^n$ 个联合对两两不同，配置数至少 $2^n/(k+1)$。同一取得长度比较已计入所有可读时钟、阶段号和输出侧信息，不能另外用它们免费区分配置。最后 $n\ge T-1$ 给

$$
2^n\ge2^{T-1}=\frac12(\kappa/\delta)^\rho,
$$

即(43.24.3)。这是定理36.25和第38.6节的计数在本固定有限深度族上的代入。$\square$

**位数与视界。** 若完整配置采用固定宽度二进制表示，截至 $M_n$ 次取得的最坏完整峰值 $H^{\mathrm{fix}}_{b,\mathcal A}(M_n)$ 满足

$$
H^{\mathrm{fix}}_{b,\mathcal A}(M_n)
\ge\left\lceil\log_2\mathcal C_{b,\mathcal A}(M_n)\right\rceil
\ge n-\log_2(k+1)\ge T-1-\log_2(k+1).
\tag{43.24.5}
$$

若配置表示为最大长度 $H^{\mathrm{var}}$ 的变长完整二进制串，允许空串，长度至多 $H$ 的串共有 $2^{H+1}-1$ 个，故

$$
\begin{aligned}
H^{\mathrm{var}}_{b,\mathcal A}(M_n)
&\ge\left\lceil\log_2(\mathcal C_{b,\mathcal A}(M_n)+1)\right\rceil-1\\
&\ge n-1-\log_2(k+1)\ge T-2-\log_2(k+1).
\end{aligned}
\tag{43.24.6}
$$

控制与所有可读辅助信息均已在表示内。若可能配置数无限，任何有限位容量都不够，相应下界自动成立。精确观察视界为

$$
M_n=m+L(\lceil T\rceil-1),\qquad
m+L(T-1)\le M_n<m+LT.
\tag{43.24.7}
$$

因 $a=g^L$，这也给 $M_n=\log(\kappa/\delta)/\log(1/g)+O(1)$，误差仅由固定 $m,L$ 控制。计数对象是出发观察次数；终端未来的首色尚未取得，不能多算一个终端颜色，也不把该视界解释为物理运行时间。

准确量词是：固定满足 H+ 及分歧、实际延续条件的一族数据后，对每个满足(43.24.2)及合同范围的预算、每个固定合法归属、每个在该预算与归属下满足合同的解码器，都有相应视界的记录族给出下界。解码器可随预算改变；下界是跨记录的最坏容量，不要求一条轨迹经历全部配置，也不给跨预算统一解码器定理。族包含与 H+ 给 $B_n\uparrow\beta$，所以一个固定 $b<\beta$ 不能覆盖这个同一无界族。严格取整提供的余量也不保证一个与预算无关的正比例噪声余量。

本章仅涉及已指定实际族的共同有限尾、有限深度成本、实际端点归属及既有配置计数的条件代入。在命题43.11—43.19的单一 rival 返回供应路线中，命题43.16依据全部实际证书、逐槽严格种子余量和所选 rival tight 锁，把实际中心识别为 $\beta$；没有这一识别时，命题43.17只给实际中心 $B_*$。推论43.24则独立以 H+ 假定其固定族的正尾式，H+ 本身给出 $B_*=\beta$，不额外要求命题43.16的单一 rival 证书。负斜率结果要求两个非退化包络和内部固定 $D/D$ 尾，不能移用于单点竞争包络。平台例的相同空词干与 H+ 容量桥接要求的真正分歧词干分开；H+ 始终是附加条件，不供应实际分支存在性。上述结论不裁定全局转变半径及其取得，不给统一记忆分类、数值实验或物理时空起源结论；配置代入只复用既有计数。

## 43.99 追加锚（本行以下为增补区）
## 44. 百窗口分歧族的实际正预算尾式与配置容量

本章以式 (33.30) 的指定二返回族供应推论43.24所需的 H+，只补该实际实例的内部固定尾、规范阈值及有限深度尾式。所用公开前提均指本卷[固定修订 cfe06a9af05aff5b3d2ffa4d478cea124842a1a3](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md)：定义14.5和定理17.2的合法来源与前接、定义33.7的完整逐坐标证书、引理33.8及定理33.10的中间输入余量、定理39.2.1和39.3.2的规范包络与全槽阈值。容量部分沿用定义36.9及定理36.25、第38.6节的共同第一未来计数。

**定义 44.1（实际来源与观察）。** 置

$$
t=\frac{\sqrt5-1}{2},\quad \phi=1+t,\quad g=2t-1=t^3,
\quad \lambda=\frac{t^2}{10},\quad c=\frac{2t}{5},
\quad I_0=X=[-1,\phi],\quad I_1=[-1,t].
$$

来源窗口标签为 $\{3,0,5,2,25\}$，其中 $0$ 是空窗，$25$ 是一个窗口标签。保留原合法 guard 边及原前接映射：

$$
\begin{gathered}
0\to0:3,0,2;\qquad 0\to1:5,25;\qquad
1\to0:3,0;\qquad 1\to1:5,\\
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t),\qquad f_\ell(x)=\Delta_\ell-gx,\\
f_w=f_{w_0}\circ\cdots\circ f_{w_{|w|-1}},\qquad f_\varnothing=\mathrm{id}.
\end{gathered}
\tag{44.1}
$$

以 $\mathcal A_s$ 记定义14.5中从 guard $s$ 出发的合法完成地址域，$D_s$ 是其中最终空尾的地址，$\Omega=\mathcal A_0$、$D=D_0$；编码为 $\kappa_s(\xi)=\sum_{r\ge0}(-g)^r\Delta_{\xi_r}$。合法前接满足 $\kappa_s(w\xi)=f_w(\kappa_{s'}(\xi))$，不识别字面不同的来源。

一次固定任意合法切点归属，以 $\mathcal Q$ 表示对应六格量化器，实际格为 $C_i=\mathcal Q^{-1}(i)$。式 (28.1)、定义39.1.1给出

$$
\begin{gathered}
q_1=-t^2-\lambda,\quad q_2=g-3\lambda,\quad q_3=t-5\lambda,
\quad q_4=2t-7\lambda,\quad q_5=2t+\lambda,\\
J_0=[-1,q_1],\ J_1=[q_1,q_2],\ J_2=[q_2,q_3],\\
J_3=[q_3,q_4],\ J_4=[q_4,q_5],\ J_5=[q_5,\phi],
\qquad J_i=\overline{C_i}.
\end{gathered}
\tag{44.2}
$$

实际观察为 $\mathcal Q(\operatorname{clip}_X(x+e))$。对 $b\ge0$，记

$$
O_i^b=\{x\in X:\exists y\in C_i, |x-y|\le b\}.
$$

由裁剪非扩张且固定 $X$，此集合恰表示预算 $b$ 下的实际可取得性。一个点属于 $O_i^b$ 当且仅当其到 $J_i$ 的距离小于 $b$，或距离等于 $b$ 且唯一最近点被 $C_i$ 拥有。$b=0$ 时仍须检查实际归属；$O_i^b$ 是保留端点旗标的区间。

**定义 44.2（字面固定的同步数据）。** 采用定义33.7的原词

$$
\begin{aligned}
U&=(5,0,3,0,3,3),& V&=(0,3,3,5,0,3),\\
d&=(2,1,0,2,1,0),\\
C&=(5,5,3,2,2,0,3,3,3,25,5,0,0,2,2,25,3,3,0,5),\\
e&=(2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2).
\end{aligned}
$$

令

$$
\begin{array}{c|c|c|c}
i&A_i&B_i&W_i\\ \hline
0&U^{10}C^2&V^{10}C^2&d^{10}e^2\\
1&CU^{10}C&CV^{10}C&ed^{10}e
\end{array},\qquad P=UC,\quad Q=VC,\quad h=de.
\tag{44.3}
$$

这里 $A_i,B_i,W_i$ 正是式 (33.30) 的两种选择，$|P|=|Q|=|h|=26$，全部返回及颜色块长 $L=100$。固定实际尾

$$
\boxed{\xi_1=A_1\,5\,0^\infty=(CU^{10}C)5\,0^\infty,
\qquad \xi_2=B_1\,0^\infty=(CV^{10}C)0^\infty.}
\tag{44.4}
$$

对每个有限二进制词 $z=z_1\cdots z_q$，包括空词，同一 $z$ 同时指定

$$
\alpha_z=PA_{z_1}\cdots A_{z_q}\xi_1,\qquad
\beta_z=QB_{z_1}\cdots B_{z_q}\xi_2,\qquad
h_z=hW_{z_1}\cdots W_{z_q}.
\tag{44.5}
$$

历史只观察出发坐标 $0,\ldots,26+100q-1$；经过这些来源边后的终端坐标未观察。后接的零误差完整未来分别是

$$
S_{\xi_j}=\bigl(\mathcal Q(\kappa_{s_r}(T^r\xi_j))\bigr)_{r\ge0},
\tag{44.6}
$$

其中 $T$ 删除一个三位窗口，$s_r$ 是该尾的实际 guard。所有第一来源共享字面尾 $\xi_1$ 的这个未来；第二来源接自己的 $S_{\xi_2}$。

**引理 44.3（guard、分歧及返回方向）。** 两 stems 合法地从 guard 零进入 guard 一，首次分歧位置为 $k=0$；四个返回均是合法的 guard 一自返回，两尾在 $D_1$，故 (44.5) 的两来源在 $D$。两种第一来源返回、第二来源返回和共同颜色块分别不同。置

$$
\begin{gathered}
z_U=\frac{23+14g}{76},\qquad z_V=\frac{6+9g}{76},\\
h_H=z_U-c=\frac{39-6g}{380},\qquad
h_L=c-z_V=\frac{46+31g}{380},\\
\chi=g^{20},\quad s=g^{60},\quad a=s\chi^2=g^{100},
\qquad b_j=(1-s)h_j\quad(j=H,L).
\end{gathered}
$$

在高侧位移 $D=x-c$ 和低侧位移 $D=c-y$ 中，实际返回恰为

$$
F_{j0}(D)=b_j+aD,\qquad F_{j1}(D)=\chi b_j+aD.
\tag{44.7}
$$

**证明。** $U,V$ 的完整 guard 序列分别为

$$
(s_0,1,0,0,0,0,0),\qquad(s_0,0,0,0,1,0,0),
$$

而 $C$ 的序列为

$$
(s_0,1,1,0,0,0,0,0,0,0,1,1,0,0,0,0,1,0,0,0,1).
$$

逐标签按 (44.1) 检查，首标签 $5$ 允许 $s_0=0,1$。$U,V$ 结束于零，$C$ 结束于一，因此每个接缝合法。尾 $\xi_1$ 在 $A_1$ 后使用 $1\xrightarrow{5}1\xrightarrow{0}0$，再重复 $0\xrightarrow{0}0$；尾 $\xi_2$ 在 $B_1$ 后使用 $1\xrightarrow{0}0$，再重复空窗。两者最终为空。$P,Q$ 首标签为 $5,0$；$A_0,A_1$ 的第二标签为 $0,5$，$B_0,B_1$ 的首标签为 $0,5$，$W_0,W_1$ 的第二颜色为 $1,3$。这些自返回不要求沿途避开 guard 一。

由 (33.28) 及定义33.7的 $f_C(u)=c+\chi(u-c)$，$U^{10},V^{10}$ 的位移映射为 $(1-s)h_j+sD$。选择0先作用内层 $C^2$，选择1先作用内层 $C$、最后作用外层 $C$，分别给出 (44.7)，与 (33.31) 一致。证毕。

**引理 44.4（物理规范包络与具体内部尾）。** 令

$$
d_j^-=\frac{\chi b_j}{1-a},\qquad d_j^+=\frac{b_j}{1-a}.
$$

定理39.2.1的两条非退化规范最小包络在物理坐标中为

$$
H_1=[m_1,M_1]=[c+d_H^-,c+d_H^+],\qquad
H_2=[m_2,M_2]=[c-d_L^+,c-d_L^-].
\tag{44.8}
$$

它们严格包含于引理33.8的返回矩形内部。固定尾标量 $x_j=\kappa_1(\xi_j)$ 满足 $m_j<x_j<M_j$。

**证明。** $0<\chi,a<1$、$b_H,b_L>0$，且

$$
\chi b_j<d_j^-<d_j^+<h_j;
$$

末式来自 $(1-s)/(1-s\chi^2)<1$。定义33.7给出 $h_H<t^2-c$、$h_L<c$，于是

$$
H_1\times H_2\subset
\operatorname{int}\bigl([c+\chi b_H,t^2]\times[0,c-\chi b_L]\bigr).
\tag{44.9}
$$

这同时保持实际 guard 一尾域。高侧物理极小、极大返回分别是 $A_1,A_0$；低侧换回 $y=c-D$ 后分别是 $B_0,B_1$，不能照搬位移端点的次序。

退出 $5\,0^\infty$、$0^\infty$ 的标量为 $t^2,0$。令 $E_H=t^2-c$、$E_L=c$，由 (44.7)

$$
X_j=\chi b_j+aE_j,\qquad x_1=c+X_H,\qquad x_2=c-X_L.
\tag{44.10}
$$

以下用有理界检查内部性。$g^2+4g=1$ 给 $0<g<1/4$，所以

$$
h_H>\frac{39-6/4}{380}>\frac1{16},\qquad
h_L>\frac{46}{380}>\frac1{16},\qquad
0<E_H,E_L<1,\quad \chi,s<\frac14,\quad a<\frac1{256}.
$$

并且 $E_j>h_j>d_j^-$；高侧的严格差是 $t^2-z_U=(15-52g)/76>0$，低侧的严格差是 $z_V>0$。因此

$$
(1-\chi)b_j=(1-\chi)(1-s)h_j>\frac9{256}>aE_j,
\tag{44.11}
$$

$$
X_j-d_j^-=a(E_j-d_j^-)>0,\qquad
X_j<\chi b_j+(1-\chi)b_j=b_j<d_j^+.
$$

第一等式使用 $d_j^-=\chi b_j+ad_j^-$。这证明 (44.4) 的字面尾严格位于 (44.8) 内部，不留下另选实际尾的假设。证毕。

**定义 44.5（全部带索引槽及规范预算）。** 保留定义39.3.1的每一个槽，即

$$
\begin{array}{ll}
(f_{P[r:]}(H_1),h_r),\ (f_{Q[r:]}(H_2),h_r),&0\le r<26,\\
(f_{A_i[r:]}(H_1),(W_i)_r),\ (f_{B_i[r:]}(H_2),(W_i)_r),
&i=0,1,\ 0\le r<100.
\end{array}
$$

以 $\alpha\in\mathscr L$ 索引，记来源分量 $j(\alpha)$、指定颜色 $c_\alpha$，以及 $f_\alpha(u)=v_\alpha+\gamma_\alpha u$，其中 $\gamma_\alpha=(-g)^{|\text{后缀}|}\ne0$。相同数值的槽仍保留各自索引，$|\mathscr L|=2\cdot26+4\cdot100=452$。定义完整的904端点最大值

$$
\boxed{\displaystyle
\beta=\max_{\alpha\in\mathscr L}\max_{e\in\{m_{j(\alpha)},M_{j(\alpha)}\}}
\operatorname{dist}(f_\alpha(e),J_{c_\alpha}).}
\tag{44.12}
$$

令 $B_n$ 是 (44.5) 中全部 $|z|\le n$、两分量、全部指定出发坐标到相应闭格的最大距离。该有限族包括空词，且不增加未观察终端的颜色槽。

**命题 44.6（正的规范阈值与全槽余量）。** 式 (44.12) 属于 $\mathbb Q(t)$，是该固定返回族的最小全深度闭阈值，并且

$$
\boxed{0<\lambda-g^2(t^2-c)\le\beta\le R_*<\lambda.}
\tag{44.13}
$$

对 (44.4) 的同一对尾，每个有限历史在预算 $\beta$ 下均实际可取得，适用于每一种固定合法归属。

**证明。** 域成员关系和规范最小性直接应用定理39.3.2，但严格上下界须覆盖本实例全部槽。按组成块计，两 stems 有两个 $U/V$ 和两个 $C$，四个返回有四十个 $U/V$ 和八个 $C$。所以全部槽恰分为 $42\cdot6=252$ 个 $U/V$ 槽与 $10\cdot20=200$ 个 $C$ 槽。

由 (44.9) 及引理33.8，每个单独 $U,V$ 的终尾输入分别属于

$$
[c+\chi^3b_H,t^2],\qquad[0,c-\chi^3b_L],
$$

每个 $C$ 的输入属于 $[0,t^2]$。这同时覆盖 stems、两种返回及每个块内位置。定义33.9的完整六后缀端点最大值在本记号下是

$$
\begin{aligned}
\rho_U=\max\{&\operatorname{dist}(f_{U[r:]}(u),J_{d_r}):
 u\in\{c+\chi^3b_H,t^2\},\ 0\le r<6;\\
&\operatorname{dist}(f_{V[r:]}(v),J_{d_r}):
 v\in\{0,c-\chi^3b_L\},\ 0\le r<6\}.
\end{aligned}
$$

距离经仿射映射后为凸函数，因此这24端点式控制全部252个 $U/V$ 槽。定理33.10的严格性来自定义33.7的六行后缀证书：只有位置4在输入 $c$ 处接触预算 $\lambda$，上述正位移把两个输入区间都与 $c$ 严格分开，故 $\rho_U<\lambda$。

对全部 $C$ 槽，定义33.7的20行坐标证书可写为 $p_{20}=p_0=c$、$10p_r=A_r+B_rg$，其中按 $r=0,\ldots,19$ 的完整有序表为

$$
\begin{gathered}
(2,2),(5,3),(-8,0),(7,3),(9,3),\\
(1,1),(-5,-1),(-4,0),(-9,-1),(12,4),\\
(3,3),(0,2),(-2,0),(8,2),(6,2),\\
(14,4),(-5,1),(-6,0),(-1,1),(3,1).
\end{gathered}
$$

该证书逐行满足 $p_r=\Delta_{C_r}-gp_{r+1}$ 及 $p_r\in\operatorname{int}J_{e_r}$；原表的全部左右内部差为正，其中最小型差 $5-21g>1/24$ 由 (33.14) 的 $4/17<g<17/72$ 保证。于是对同一个终尾 $u\in[0,t^2]$，

$$
f_{C[r:]}(u)=p_r+(-g)^{20-r}(u-c).
$$

位置 $0\le r\le18$ 取原证书的内部目标 $p_r$，误差至多 $g^2t^2$；位置19的整个像为

$$
[t^2(1-g),t^2]\subset(q_2,q_3),
$$

可取零误差。故全部200个 $C$ 槽均被原完整证书覆盖。令 $R_C=(\lambda+g^2t^2)/2$，定理33.10给 $R_*:=\max\{\rho_U,R_C\}<\lambda$，遂有 $\beta\le R_*$。这里 $R_*$ 只作上界，规范阈值始终是 (44.12)。

正性测试第一 stem $UC$ 的位置4，指定颜色为1，完整后缀是 $(3,3)C$。定义33.7给出

$$
f_{33}(u)=q_1-\lambda+g^2(u-c).
$$

由 $f_C(H_1)\subset(c,t^2)$，该槽的全部像都低于 $q_1$，到 $J_1$ 的距离至少为 $\lambda-g^2(t^2-c)$。又 $g^2<1/16<1/10$，故此数大于 $\lambda-g^2t^2>0$，证明 (44.13)。

最后，每个有限剩余返回把 $x_j\in\operatorname{int}H_j$ 送入内部；每个 $f_\alpha$ 非零斜率，内部点的像严格位于 $f_\alpha(H_j)$ 两端之间。该像区间包含于 $J_{c_\alpha}+[-\beta,\beta]$，$\beta>0$ 使所有这些实际点的距离严格小于 $\beta$。可把最近目标略移入指定格内部而保持误差小于 $\beta$，归属障碍全部消失。这也是定理39.4.1在本字面尾上的直接应用。证毕。

**引理 44.7（有限深度的精确端点与归属）。** 记

$$
D_{j,-}=x_j-m_j>0,\qquad D_{j,+}=M_j-x_j>0,
\qquad d_\alpha=\begin{cases}0,&\text{stem 槽},\\1,&\text{返回槽}.
\end{cases}
$$

全部长度不超过 $N$ 的返回复合作用于 $x_j$ 后，标量凸包恰为

$$
K_{j,N}=[m_j+a^ND_{j,-},\ M_j-a^ND_{j,+}]\qquad(N\ge0).
\tag{44.14}
$$

每个端点均由实际长度恰为 $N$ 的词取得。对 $n\ge1$，精确成本为

$$
\boxed{\begin{aligned}
B_n=\max_{\alpha\in\mathscr L}\max\bigl\{&
\operatorname{dist}(f_\alpha(m_j+a^{n-d_\alpha}D_{j,-}),J_{c_\alpha}),\\
&\operatorname{dist}(f_\alpha(M_j-a^{n-d_\alpha}D_{j,+}),J_{c_\alpha})\bigr\},
\qquad j=j(\alpha).
\end{aligned}}
\tag{44.15}
$$

零层只保留52个 stem 槽，$B_0=\max_{\alpha\text{ 为 stem 槽}}\operatorname{dist}(f_\alpha(x_{j(\alpha)}),J_{c_\alpha})$。此外

$$
B_n<\beta\quad(n\ge0),\qquad B_n\uparrow\beta.
\tag{44.16}
$$

预算恰为 $B_n$ 时，实际取得整棵有限树的充要条件是每个现存槽在 (44.15) 中的两端实际坐标均属于 $O_{c_\alpha}^{B_n}$；零层以 $f_\alpha(x_j)$ 检查。任意 $b>B_n$ 则对每种固定合法归属都能以内部目标实际取得。

**证明。** 正斜率返回的极小、极大平移映射分别固定 $m_j,M_j$。长度 $N$ 的极值按正斜率归纳为 (44.14)；第一分量下端由 $1^N$、上端由 $0^N$ 取得，第二分量下端由 $0^N$、上端由 $1^N$ 取得。$N=0$ 是空词和单点 $x_j$。因两余量正，这些区间随 $N$ 扩大，所以同式也是全部长度不超过 $N$ 的凸包；不要求返回吸引子填满区间。

stem 槽后面可接全部 $|w|\le n$ 的返回；指定返回 $i$ 的槽后面可接全部 $|w|\le n-1$，端点由选择词 $iw$ 在第一个返回块中实现。更早的块不改变当前出发坐标的后缀值，故没有更大端点。凸性给 (44.15) 的上界，实际端点词给下界；同时测两端处理了负斜率后缀。每个见证都属于 (44.5) 中同一 $z$ 指定的联合来源，不同槽的下界无须由同一个 $z$ 同时取得。

内部性与命题44.6给每个有限坐标严格成本小于 $\beta$；有限最大值仍严格小于 $\beta$。树包含给单调非降，(44.14)—(44.15) 的端点极限给 $B_n\to\beta$。归属条件的必要性来自实际端点见证，充分性来自 $O_i^{B_n}$ 的区间性和上述凸包。正的等号距离必须使用被拥有的投影；零成本仍检查实际坐标的归属。若 $b>B_n$，有限树所有目标可移入格内部并取共同严格误差上界小于 $b$，裁剪固定这些目标。证毕。

**引理 44.8（完整临界集的正尾式）。** 令 $e_{j,-}=m_j$、$e_{j,+}=M_j$，并保留所有临界端点

$$
\mathcal A=\{(\alpha,\varepsilon):\alpha\in\mathscr L,
\ \varepsilon\in\{-,+\},\quad
\operatorname{dist}(f_\alpha(e_{j(\alpha),\varepsilon}),J_{c_\alpha})=\beta\}.
$$

它非空，且实例常数

$$
\boxed{\displaystyle
\kappa=\min_{(\alpha,\varepsilon)\in\mathcal A}
|\gamma_\alpha|\,a^{-d_\alpha}D_{j(\alpha),\varepsilon}>0}
\tag{44.17}
$$

满足：存在固定整数 $n_0\ge1$，使

$$
\boxed{B_n=\beta-\kappa a^n\qquad(n\ge n_0),\qquad a=g^{100}.}
\tag{44.18}
$$

**证明。** 所有 $D_{j,\varepsilon}>0$、$|\gamma_\alpha|>0$；有限非空集给 $\kappa>0$，且 $\kappa\in\mathbb Q(t)$。由

$$
\operatorname{dist}(y,[l,u])=\max\{l-y,0,y-u\},
$$

式 (44.15) 是固定有限条 $b_r+c_ra^n$ 的最大值，所有截距不超过 $\beta$。截距为 $\beta>0$ 的支恰来自完整临界集的格外距离。这样的端点必是其像区间在该格外方向的最外端，否则另一端点距离更大，与 (44.12) 矛盾。从它向像区间内部移动，格外线性支的减少系数恰为 $|\gamma_\alpha|a^{-d_\alpha}D_{j,\varepsilon}$。所以全部最高截距支的最大斜率为 $-\kappa$，它们的最大值恰为 $\beta-\kappa a^n$。

对任一较低截距支 $b_r<\beta$，若 $c_r\le-\kappa$，它始终低于该临界最大支；若 $c_r>-\kappa$，只须

$$
a^n\le\frac{\beta-b_r}{c_r+\kappa}.
$$

有限个正右端与 $a^n\to0$ 给出共同 $n_0\ge1$，包括零距离支，证明精确等式 (44.18)。这保留所有临界系数及所有非临界竞争支，不指定一个支配端点。任取满足这些不等式的固定起始层即可，不要求最小 $n_0$。证毕。

**推论 44.9（实际 H+ 供应与预算缺口容量）。** 对定义44.2的同一个字面固定族，H+ 的实际族条件由 (44.13)、(44.15)、(44.18) 满足。固定一个由引理44.8得到的 $n_0$，对每个

$$
0<\delta<\min\{\beta,\kappa a^{n_0}\},\qquad b=\beta-\delta\in(0,\lambda),
$$

每种固定合法归属，以及在该预算与归属下满足定义36.9完整恢复合同的解码器 $\mathcal D$，令 $\mathcal C_{b,\mathcal D}(N)$ 为处理完恰好 $N$ 次取得后，全部实际记录上可能出现的完整配置数。置

$$
T=\frac{\log(\kappa/\delta)}{\log(1/a)},\qquad
n=\lceil T\rceil-1,\qquad N_n=26+100n,\qquad
\rho=\frac{\log2}{100\log(1/g)}.
$$

则

$$
\boxed{\mathcal C_{b,\mathcal D}(N_n)\ge2^n
\ge\frac12\left(\frac\kappa\delta\right)^\rho,\qquad
H^{\mathrm{fix}}_{b,\mathcal D}(N_n)\ge n,\quad
H^{\mathrm{var}}_{b,\mathcal D}(N_n)\ge n.}
\tag{44.19}
$$

这里两个 $H$ 分别是截至该视界的最坏完整配置固定宽度、可变长度二进制最大位容量。合同要求确定、因果、固定初态，每次取得允许有限计算及有限输出批次，输出按序只追加、不可回读；全部实际 $\Omega$ 记录上安全，全部实际 $D$ 记录上每个位置最终生效，包括无限空窗补齐。完整配置计入所有影响未来的可读控制、持久与临时数据、计数器、输入与输出位置、时序、可读时钟及输出侧信息；没有 End、支持上界或免费重放。

**证明。** 这是推论43.24在 $m=26,L=100,k=0$ 的代入；实例的实际性和正尾式已由本章证明。严格取整仍须保留：$\delta<\kappa a^{n_0}$ 给 $T>n_0$，于是

$$
n\ge n_0,\qquad T-1\le n<T,\qquad
\kappa a^n>\delta,\qquad B_n<b.
$$

若 $T=q$ 为整数，必须取 $n=q-1$；取 $q$ 会得到 $B_q=b$，不能保证任意归属下的严格取得。引理44.7使全部 $|z|\le n$ 的两分量以内部目标共同取得指定历史，并有统一误差上界小于 $b$。后接 (44.6) 的各自零误差未来，得到完整实际 $D$ 记录；尾仍是 (44.4)，未随预算、深度或 $z$ 改变。

恰好深度 $n$ 的 $2^n$ 个历史因等长且不同的 $W_0,W_1$ 两两不同，其第一来源也因 $A_0\ne A_1$ 两两不同。每个历史有首标签 $5,0$ 的两条实际延续，安全性迫使此刻旧输出为空。若两个历史后的完整配置相同，接同一个第一来源未来 $S_{\xi_1}$，确定性给相同全部输出，与两个不同 $D$ 来源的逐位置生效矛盾。因此完整配置至少有 $2^n$ 个。这复用定理36.25和第38.6节的计数；本实例 $k=0$ 无旧输出因子损失。$n\ge T-1$ 给出 (44.19) 的幂次界。

固定宽度少于 $n$ 位不能表示 $2^n$ 个配置；可变长度最大值少于 $n$ 时，含空串在内至多有 $\sum_{r=0}^{n-1}2^r=2^n-1$ 个串，所以其最大位容量也至少是 $n$。若配置数无限，下界自动成立。精确视界是 $26+100(\lceil T\rceil-1)$ 个出发观察；未来首色尚未取得，不重复计入终端。相同取得长度的计数可以跨不同实际记录，所有可读辅助信息均已计价。上述严格余量也使这些见证适用于相同恢复要求下的正开及逐记录严格余量合同。证毕。

**注记 44.10（结论范围）。** 对这个指定族，不再需要附加实际供应假设：两条字面 $D_1$ 尾、两条非退化物理规范包络、全部452槽的904端点阈值和正尾式均由上述证明给定。在 $\beta$ 下同一全族对每种固定合法归属实际取得；任何固定 $b<\beta$ 都不能覆盖该同一无界族，因为 $B_n\uparrow\beta$。有限端点最大值和临界最小值是精确公式，其数值化、单一最大槽的识别或最小起始层的求取均不是推论44.9的前提。容量结论仍按所列预算范围及完整恢复合同量化，解码器可随预算改变，不要求一条轨迹经历全部配置。新增数学仅是该实际供应与既有容量结论的局部代入，不确定全局转变半径的识别或取得、跨族最优性、全解码器分类、物理时空起源、执行效率或形式化内核验证。

## 44.99 追加锚（本行以下为增补区）
## 45. 本原五周期 singleton rival 的首源相干与折叠延续

### 假设与定义 45.1（原来源、闭观察及给定完整图）

本章使用同一实际 FIB 来源地址，保留所有 $\Omega$ 地址、单点、根端点及无有限尾地址。置
$$
t=\frac{\sqrt5-1}{2},\qquad g=t^3=2t-1=\sqrt5-2,\qquad
g^2+4g=1,\qquad \phi=1+t,
$$
$$
X=I_0=[-1,\phi],\qquad I_1=[-1,t],\qquad
\lambda=\frac{1-g}{20},\qquad 0<\beta<\lambda,\qquad
\delta=\lambda-\beta>0.
$$
地址域为 $A_0=\Omega$、$A_1=\{\omega\in\Omega:\omega_0=0\}$。三位窗口标签按根像的空间次序为
$$
(r_1,r_2,r_3,r_4,r_5)=(3,0,5,2,25),
\qquad
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})=(-t,0,t^2,1,2-t).
$$
其中 $0=\mathrm{null}=000$，$25=101$ 是一个窗口标签。实际分支、逆分支和全部 guard 为
$$
f_\ell(x)=\Delta_\ell-gx,\qquad F_\ell(x)=\frac{\Delta_\ell-x}{g},
$$
$$
0\to0:3,0,2;\quad 0\to1:5,25;\quad
1\to0:3,0;\quad1\to1:5.
\tag{45.1}
$$
从 guard $s$ 出发的合法地址编码为
$\kappa_s(\omega)=\sum_{n\ge0}(-g)^n\Delta_{\ell_n}$。
同一个实际地址给出全部坐标、窗口及后续 guard，满足
$x_n=f_{\ell_n}(x_{n+1})$。合法根像依次为
$$
3:[-1,-t^2],\quad0:[-t^2,g],\quad5:[g,t],\quad
2:[t,2t],\quad25:[2t,\phi];
\tag{45.2}
$$
guard 一只允许前三块。合法根像覆盖各 $I_s$；逐步选择含给定点的合法块并取逆像，余项 $(-g)^Nx_N$ 趋零，故 $\kappa_s(A_s)=I_s$。合法前接使用同一个级数，且 $A_1\subset A_0$ 的两种编码一致。

对字面有限词 $W=\ell_0\cdots\ell_{n-1}$，统一记 $f_W=f_{\ell_0}\circ\cdots\circ f_{\ell_{n-1}}$，即把该词前接到同一个终尾；其斜率为 $(-g)^n$。后文 $f_{333}$、$f_T$ 等均取这一顺序。

原六格闭包 $J_0,\ldots,J_5$ 的切点为
$$
q_1=\frac{11(g-1)}{20},\quad q_2=\frac{23g-3}{20},\quad
q_3=\frac{1+3g}{4},\quad q_4=\frac{13+27g}{20},\quad
q_5=\frac{21+19g}{20}.
$$
即 $J_0=[-1,q_1]$、$J_j=[q_j,q_{j+1}]$（$1\le j\le4$）、$J_5=[q_5,\phi]$。本章的允许色始终指原预算的**闭成员关系**
$E_i^\beta=\{x\in X:\operatorname{dist}(x,J_i)\le\beta\}$，不指另外指定端点归属后的可取得集合。记临界端点
$$
\begin{aligned}
a&=\frac{3(g-1)}5,&b&=\frac{11g-1}{10},&c&=\frac{6g-1}5,&d&=\frac{3+7g}{10},\\
e&=\frac{1+4g}5,&f&=\frac{7+13g}{10},&h&=\frac{3+7g}5,&i&=\frac{11+9g}{10}.
\end{aligned}
$$
于是
$$
\begin{aligned}
E_0^\beta&=[-1,-t^2-\delta],&E_1^\beta&=[a+\delta,b-\delta],\\
E_2^\beta&=[c+\delta,d-\delta],&E_3^\beta&=[e+\delta,f-\delta],\\
E_4^\beta&=[h+\delta,i-\delta],&E_5^\beta&=[2t+\delta,\phi].
\end{aligned}
\tag{45.3}
$$
原色 $0,5$ 分别只允许标签 $3,25$；原色 $1,2,3,4$ 的标签集合依次为
$\{3,0\},\{0,5\},\{5,2\},\{2,25\}$。这些限制由 (45.2)—(45.3) 直接得到。

**给定图假设。** 输入是一张完整的原闭覆盖图：一个共同有限端点集 $B\subset X$ 包含观察、guard 及分支域端点，且
$$
z\in B,\quad F_\ell(z)\in X\quad\Longrightarrow\quad F_\ell(z)\in B.
$$
令 $B_s=B\cap I_s$。原节点恰为 $(s,P)$，其中 $P$ 是 $B_s$ 中的端点单点，或相邻两个端点间的整个闭区间；保留全部这些规范基本片。边恰按原规则
$$
(s,P)\xrightarrow{\ell}(s',Q)
\quad\Longleftrightarrow\quad
s\xrightarrow{\ell}s'\text{ 合法},\quad
P\subseteq f_\ell(I_{s'}),\quad Q\subseteq F_\ell(P)
\tag{45.4}
$$
取全部满足条件的边。节点允许色 $i$ 当且仅当 $P\subseteq E_i^\beta$。配对顶点由具有至少一个共同允许色的两个原节点组成，配对边由两条原边组成，出发顶点选择共同色；边终端不另读一次观察。所有 SCC 均在这张原配对图或其声明的保留原片、原边的子图内讨论。

这不是任意互相重叠的闭片假设。规范片只在端点相交；两个同 guard 的基本片若共享非退化区间，就必为同一片。逆闭合还使每个实际点有规范路径：端点取单点，否则取内部含该点的唯一基本片。任何端点在 $B_s$ 中、含该点的闭区间都包含其规范片。

由 (45.4)，有限路径上 $f_{\ell_j}(P_{j+1})\subseteq P_j$。在终端片中只选一次标量和同 guard 合法尾，倒向前接即同时实现整条路径的全部坐标及出发颜色。无限路径的前缀像嵌套且直径至多 $g^N\operatorname{diam}X$，也由同一合法地址实现。特别地，一个返回反复使用后，其复合收缩把基点片映入自身，唯一固定点给同一实际周期来源及全部中间 guard、颜色；这将任意返回变为实际循环，而非逐坐标独立取点。

上述来源与图合同分别见本卷定义14.5、命题14.6、定理14.7、17.2，式(28.1)—(28.2)，定义31.3及定理31.4；所用公开文本固定为 [本卷修订 cfe06a9](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md)。引理31.2对 $\mathbb Q(t)$ 端点给出这种有限逆闭合集的构造。本章对任意实 $\beta$ 的陈述以**已供应上述完整有限图**为条件，不从域内构造推出任意实预算的图存在性。

在含环 SCC $S$ 内，第二来源投影相干并有 singleton rival，其字面来源本原周期为五，记该实际周期为 $R=(R_0,\ldots,R_4)$、坐标为 $y_0,\ldots,y_4$。若只在一个顶点指定第二片单点，逆像包含沿强连通性使所有第二片都为单点。相干性给良定义的五相位映射 $\pi:S\to\mathbb Z/5\mathbb Z$，每边使相位增加一，第二标签为 $R_{\pi(v)}$，第二单点由共同周期级数确定为 $y_{\pi(v)}$。这一相位结论的证明是：固定基点返回的最短字面周期块；所有同步返回相等则每条返回都是该块的幂，长度被五整除；给到某顶点的两条路径接同一返程，所得长度同余，故路径长度模五定义 $\pi$。这正是定理36.22的证明在本原五周期上的应用，图的环长最大公因数可以是五的更大倍数。

定义
$$
D_\beta=\{r\in\mathbb Z/5\mathbb Z:\#\{j:y_r\in E_j^\beta\}=2\}.
\tag{45.5}
$$
非相邻临界色之间的间隙为 $c+t^2=d>0$、$e-b=3(1-g)/10>0$、$h-d=d>0$、$2t-f=3(1-g)/10>0$。因此每相位至多两色，而原六格覆盖保证至少一色。本章证明第一投影的同步返回相干性：任意同基点非空返回的第一词 $U,V$，长度 $m,n$，满足
$$
U^{L/m}=V^{L/n},\qquad L=\operatorname{lcm}(m,n).
\tag{45.6}
$$

### 引理 45.2（任意实次临界预算的同尾宽度）

两条实际合法来源若在位置 $N$ 起有同一个字面合法尾，并在位置 $0,\ldots,N-1$ 逐位置属于同一个原预算闭色，则其前 $N$ 个标签相同。

**证明。** 若不同，取最后不同位置 $r<N$。共同下一坐标使当前两值之差恰为标签平移差。根像与闭格宽度给

| 共同色 | 可能不同标签 | 平移差 | 闭格宽度 |
| --- | --- | --- | --- |
| 0 | $3,0$ | $t$ | $t-\delta$ |
| 1 | $3,0$ | $t$ | $t-2\delta$ |
| 2 | $0,5$ | $t^2$ | $t^2-2\delta$ |
| 3 | $5,2$ | $t$ | $t-2\delta$ |
| 4 | $2,25$ | $t^2$ | $t^2-2\delta$ |
| 5 | $2,25$ | $t^2$ | $t^2-\delta$ |

端格行保留了严格次临界时已不能发生的接触标签，仍是必要上包络。每行宽度严格小于平移差，矛盾。这复用引理36.16的严格宽度证明，只涉及实数次序及 $\delta>0$，无需预算属于数域。终尾允许为任何实际 $\Omega$ 尾。$\square$

### 引理 45.3（零双色及非退化片）

若 $D_\beta=\varnothing$，第一投影相干。若第一投影不相干，则 $S$ 的每个第一片非退化。

**证明。** 零双色时，同基点返回重复到共同长度 $5k$ 后，rival 的各出发相位只有一个原预算闭色，故两路径的出发颜色历史完全相同。在同一第一终端片及 guard 中固定同一个点、同一个实际合法尾；全包含提升与引理45.2使第一词相同。这里不观察终端，且不删除任何单点或端点。

后一断言使用命题39.6.1的内容，亦可直接证明。单点第一片沿 $Q\subseteq F_\ell(P)$ 传播，强连通性使全部第一片单点。若有同步等长不同第一返回词 $U_0,U_1$，固定基点单点 $x$ 的同 guard 尾 $\tau$，则全包含提升给 $U_0U_0\tau,U_0U_1\tau,U_1U_0\tau,U_1U_1\tau$ 四条不同地址，均编码 $x$。同 guard 同标量至多两个地址：首个分歧只能在相邻根像的公共端点，两侧尾是相应状态区间的唯一极值尾；有限前接保持这一性质。这是定理14.7的纤维证明，排除四地址，故单点 SCC 相干。$\square$

### 定义 45.4（相位条带、颜色类型及同源终端递推）

以后统一置
$$
s_j=-1+\frac{j\phi}{5}\ (0\le j\le5),\qquad
\theta=\frac{2t}{5},\quad u=\frac t5,\quad
v_*=-\frac{5+g}{10},\quad H=\frac{t^2-\theta}{g},
$$
$$
K_*=2-8g,\qquad J_*=\frac{7+2g}{5},\qquad
\eta=\frac{3t}{5},\qquad L_*=f_3f_3(c)=\frac{96g-25}{5}.
\tag{45.7}
$$
特别地 $s_1=(g-7)/10$、$s_2=(g-2)/5$、$s_3=-gt/5=(3g-1)/10$、$s_4=(1+2g)/5$、$s_5=t$。本章 $u$ 仅表示 $t/5$；分支5的平移始终写成 $t^2$。定义严格临界带及其逆条带
$$
\begin{aligned}
B_1&=(a,-t^2),&B_2&=(c,b),&B_3&=(e,d),&B_4&=(h,f),&B_5&=(2t,i),\\
C_j&=(s_{j-1},s_j),& F_{r_j}(B_j)&=C_j.
\end{aligned}
\tag{45.8}
$$
这些 $B_j$ 只表示临界 $\lambda$ 成员资格。实际双色带为相应闭交 $E_{j-1}^\beta\cap E_j^\beta\subset B_j$。令 $U_j=\{j-1,j\}$ 为**颜色指标集**，$H_j^\beta=\bigcup_{a\in U_j}E_a^\beta$ 为**标量集合**。其临界外包络分别是 $[-1,b],[a,d],[c,f],[e,i],[h,\phi]$。

单双色相位旋到零，带号为 $j$，后四个固定原单色为 $C=(c_1,c_2,c_3,c_4)$。对指标集 $A\subseteq\{0,\ldots,5\}$，定义
$$
H(A)=\bigcup_{a\in A}E_a^\beta,\qquad
\mathcal K_s^A(\varnothing)=I_s\cap H(A),
$$
$$
\mathcal K_s^A(cC')=E_c^\beta\cap
\bigcup_{s\xrightarrow{\ell}s'} f_\ell\bigl(\mathcal K_{s'}^A(C')\bigr).
\tag{45.9}
$$
当 $A=\{0,\ldots,5\}$ 时，$H(A)=X$，表示不加终端颜色；当 $A=U_j$ 时，表示下一相位零的颜色必要条件。递推的每条分支是一条实际共同来源和全程 guard，固定字面四尾时只保留该分支。并集表示不同整条合法尾的选择，不授予各坐标独立自由。

### 引理 45.5（任意 $5k$ 返回的末次分歧与实际五步合流）

在单双色情形，第一投影不相干必给同一实际宏 SCC 内两条五边路径
$$
v_-\xrightarrow{\ell T}w,\qquad v_+\xrightarrow{mT}w,
\qquad \ell\ne m,\quad |T|=4,
\tag{45.10}
$$
其中两个出发第一片分居 $y_0$ 两侧，首标签分别属于相邻对，四标签 $T$ 字面相同，$w$ 为同一个原配对顶点。其共同后继包含非退化区间，沿同一个实际尾满足后四单色及下一相位零条件。

**证明。** 任取不相干同步返回。可把基点移到唯一双色相位：用 SCC 内同一进程及返程包住原来的两条等长不同返回，所得两返回仍等长且不同。相位映射使长度为 $5k$。在同一基点第一片 $P$ 中选同一个终尾，对两路径作整条提升；由引理45.3，$P$ 非退化。

还需说明“不相干片严格分侧”。若某第一片含有其相位的 rival 点 $y_r$，由45.7该周期避开根接触，旋转的字面周期尾在该第一 guard 也合法：guard 一时 $y_r\in I_1$，其根标签只能3、0、5，与 guard 零下的唯一根标签一致，后续 guard 由标签确定。以这个周期尾同时作为两侧终尾，沿该顶点任一返回作联合提升；第一来源和 rival 满足该返回所选的完全相同出发色词。引理45.2使其第一词等于 rival 返回词。该基点所有返回遂相干，相干性沿 SCC 传播，与假设矛盾。因此每个第一片均不含对应 $y_r$；一个第一片既非退化又为区间，故整片严格在它的一侧。

取最后不同第一标签位置 $r$。其后字面后缀相同，对终端片 $P$ 作该后缀仿射像，得到位置 $r+1$ 的同一个非退化区间 $K_1$；它及随后每个后缀像均整个位于两条路径各自对应的原片中。如果 $r$ 在单色相位，引理45.2的最后位置宽度矛盾直接适用，故 $r$ 在唯一双色相位，即 $r\equiv0\pmod5$。因而后面至少还有四个共同出发标签与颜色。

两个首标签的输出 guard 可以不同；共同后继尾从两者中较严格的 guard 合法。在下一共同标签之后，输出 guard 相同。此后每一位置的非退化共同后缀像，包含于同 guard 的两原基本片，规范相邻片性质迫使这两片相同。第二投影的标签在两同步路径各位置均由相干 rival 的相位固定；它的 guard 由此前标签决定，单点则由同一周期级数确定。因此在位置 $r+5$，两侧的两个原节点分别相同，给出同一个配对终点 $w$。这里使用了非退化共同像、原规范片和实际 guard；没有从相同颜色或相同相位推断顶点相同。

首标签分类和分侧由引理45.6的区间计算给出。起点、终点均在相位零。原 SCC 中同相位顶点之间的连接路径长度都被五整除，按五边切块，故它们属于同一宏 SCC。末次分歧的五步路径无需本身为返回。$\square$

若只为排除不相干，上述证明也给一个不依赖顶点合流的直接必要条件：同一非退化 $K_1$ 满足两首标签及固定四尾，且其**同一**五步终值落入 $H(U_j)$。反向若确有 (45.10) 且从 $w$ 在同 SCC 内可返回两个起点，分别拼成返回后，按原边数的最小公倍数重复；末五字仍为 $\ell T,mT$，所以不相干。局部可行集非空并不供应这些返程。

### 引理 45.6（八方向及其共同尾外包络）

最后不同标签按平移量递增排序为 $(\ell,m)$。在双色带 $j$，它只可能为 $(r_{j-1},r_j)$ 或 $(r_j,r_{j+1})$，不存在的端项删去。两当前点分别取低色 $j-1$、高色 $j$。令 $s_*\in\{0,1\}$ 为两输出 guard 的最大值，则
$$
J_{\ell,m}=I_{s_*}\cap f_\ell^{-1}(E_{j-1}^\beta)
\cap f_m^{-1}(E_j^\beta),\qquad
M_{\ell,m}^A=J_{\ell,m}\cap\mathcal K_{s_*}^A(C).
\tag{45.11}
$$
引理45.5的共同区间满足 $K_1\subseteq M_{\ell,m}^{U_j}$，且固定字面尾也在这一递推中。未写终端上标时，$M_{\ell,m}$ 表示 $M_{\ell,m}^{\{0,\ldots,5\}}$。所有八方向为

| 双色带 $j$ | 下侧标签对 | 上侧标签对 |
| --- | --- | --- |
| 1 | — | $(3,0)$ |
| 2 | $(3,0)$ | $(0,5)$ |
| 3 | $(0,5)$ | $(5,2)$ |
| 4 | $(5,2)$ | $(2,25)$ |
| 5 | $(2,25)$ | — |

**证明。** 两首标签坐标差为正平移差，同色已由严格宽度排除，故只能分别取两色。两色并集在带2、3、4只允许三个相邻根标签；首尾的非相邻平移差为 $1$，超过并集宽 $1-2\lambda-2\delta$，故只剩相邻对。端带本来只允许两个根标签。

下侧对的低色下端约束给 $z_1\le s_{j-1}-\delta/g$；rival 的实际双色给 $y_1\ge s_{j-1}+\delta/g$。上侧对的高色上端约束给 $z_1\ge s_j+\delta/g$；rival 给 $y_1\le s_j-\delta/g$。其余首色界均保留在 $J_{\ell,m}$。前接两首标签所得低点严格低于 $y_0$、高点严格高于 $y_0$：上侧低点不超过 $f_{r_j}(s_j)-\delta$，而 rival 不小于 $f_{r_j}(s_j)+\delta$；高点位于下一根标签 $r_{j+1}$ 的合法根域，而 rival 严格在根域 $r_j$ 内，故高点严格在其右侧。下侧的低点在前一合法根域 $r_{j-1}$ 内，严格在 rival 左侧；高点不小于 $f_{r_j}(s_{j-1})+\delta$，而 rival 不超过 $f_{r_j}(s_{j-1})-\delta$。由45.5第一片均避开 rival，包含这些像的原基本片也必整片分居两侧。

$A_1\subset A_0$ 使同一个从 $s_*$ 合法的尾同时合法于两输出 guard；原首色逆像及 (45.9) 因此是精确的同源必要外包络。它放松了指定原 SCC 的片及返程，故仅其空性或无非退化区间可以直接排除；非空性不能证明 SCC 存在。$\square$

### 引理 45.7（严格带端点与覆盖准备）

本原五周期 rival 不在任何 $B_j$ 的端点或根接触点。若 $|D_\beta|\ge3$，则 $D_\beta$ 必有循环相邻对。

**证明。** 令 $R_*=\mathbb Z[t]$。对奇数 $p$，若 $y\in\tfrac15R_*\setminus R_*$ 为周期坐标，则
$[1-(-g)^p]y\in R_*$。但
$$
R_*/5R_*\simeq\mathbb F_5[\varepsilon]/(\varepsilon^2),\quad
t=2+\varepsilon,\quad -g=2-2\varepsilon.
$$
奇数 $p$ 时 $1-(-g)^p$ 的常数项为 $1-2^p\ne0$，故为单位。乘五约化即得 $5y\in5R_*$，矛盾。八个非根临界端点的五倍依次为
$$
6t-6,\ 11t-6,\ 12t-7,\ 7t-2,\ 8t-3,\ 13t-3,\ 14t-4,\ 9t+1,
$$
均非 $5R_*$ 成员，所以不能为奇周期坐标。根接触点 $-t^2,g,t,2t$ 的每条地址由根像端点迫使，在有限前缀后进入非恒定二周期极值尾 $(3,25)^\infty$ 或 $(25,3)^\infty$（状态一上端先用5）。若又为奇周期来源，该尾同时有周期二和奇数，必恒定，矛盾。这一排除仅用于 rival，任意 $5k$ 第一来源的端点仍全部保留。

在循环五点集上，无相邻子集 $D$ 满足 $D\cap(D+1)=\varnothing$，从而 $2|D|\le5$。故实际双色至少三处必有相邻对；“至多二”仅在**没有相邻元素**的条件下成立。$\square$

以下精确比较统一由 $p(z)=z^2+4z-1$ 得到：
$$
\frac{72}{305}<g<\frac{305}{1292}<\frac{17}{72},
\tag{45.12}
$$
因为 $p(72/305)=-1/93025$、$p(305/1292)=1/1292^2$、$p(17/72)=1/5184$，且 $p$ 在正轴递增。以后所列正差可直接用这三界及 $g^2=1-4g$ 核对。

### 引理 45.8（相邻严格临界带的原预算循环上包络）

若实际五周期 rival 有两个相邻相位属于严格临界带 $B_j$，则与它共享原预算闭颜色记录的每条实际 $5k$ 循环第一来源，都逐块等于 rival 五窗词。这里 $k\ge1$ 任意；两个相位不必在实际 $\beta$ 下均双色，其余相位也不必单色。

**证明。** 把所选相邻相位置零、一。$F_{r_j}(B_j)=C_j$ 与五个 $B_l$ 的相交只允许
$$
2\to1,\qquad4\to2,\qquad5\to3.
\tag{45.13}
$$
例如 $C_1=(-1,s_1)$ 没有临界带，$C_2=(s_1,s_2)$ 只交 $B_1$，$C_3=(s_2,s_3)$ 没有临界带，$C_4=(s_3,s_4)$ 只交 $B_2$，$C_5=(s_4,t)$ 只交 $B_3$。以下用 $U_j$ 记录两色指标外包络；非 $U$ 栏表示唯一临界色。原预算兼容必位于这些包络内，但本证明仍用原色允许的标签和实际 guard。

所需正差集中为
$$
\begin{aligned}
gt+g^2e-b&=3g^3/5,&2g-d&=(13g-3)/10,\\
a-f_{333}(-1)&=(19-79g)/10,&a-(2g-1)&=(2-7g)/5,\\
e-t^2(1-g^2)&=(11-46g)/5,&2-t-g^2-i&=(13g-3)/5,\\
c-g^2d&=(23-95g)/10,&c-g^2f&=(43-181g)/10,\\
c-g^2i&=(23-97g)/10,&\theta-(gt+g^2i)&=(11-46g)/5,\\
1+g^2e-f&=(115g-27)/10,&h-(1-gt^2)&=(39g-9)/10,\\
c-g^2(2-t)&=(157g-37)/10,&2-t-g^3\phi-i&=(91g-21)/10.
\end{aligned}
\tag{45.14}
$$
右栏全部严格正；另外
$$
\begin{aligned}
h-(1-gt^2+g^2K_*)&=(1479g-349)/10>43/3050,\\
e-(t^2+g^2K_*)&=f-(1+g^2K_*)=(1453g-343)/10>1/3050,\\
i-(2-3g+g^2K_*)&=(1479g-349)/10,\\
t^2+g^2(2-2g)-d&=(51-216g)/5>0,\\
c-g^2(2-t+g^2\phi)&=2g^4/5>0.
\end{aligned}
\tag{45.15}
$$

**(a) 转移 $2\to1$。** rival 前三标签为 $(0,3,3)$：相位一在 $B_1$，相位二在 $C_1$，都用3。相位三 $y_3>\theta>g$，标签 $u_3$ 只可能 $5,2,25$。同一周期令末标签为 $v_4$，则
$$
y_0=K_*-g^3y_3,\qquad0<y_0<K_*<t/5,
\qquad y_4=f_{v_4}(y_0),\quad y_3=f_{u_3}f_{v_4}(y_0).
$$
guard 给 $u_3=5,25$ 时 $v_4\in\{3,0,5\}$，$u_3=2$ 时五个末标签都可接下一首标签0。前三色为 $(U_2,U_1,0)$，全部末两色为

| $(u_3,v_4)$ | 相位三、四的颜色包络 |
| --- | --- |
| $(5,3)$ | $(3,0)$ |
| $(5,0)$ | $(2,1)$ |
| $(5,5)$ | $(2,2)$ |
| $(2,3)$ | $(4,0)$ |
| $(2,0)$ | $(U_4,1)$ |
| $(2,5)$ | $(3,2)$ |
| $(2,2)$ | $(3,U_4)$ |
| $(2,25)$ | $(3,5)$ |
| $(25,3)$ | $(5,0)$ |
| $(25,0)$ | $(5,1)$ |
| $(25,5)$ | $(U_5,2)$ |

颜色栏来自同一个 $z=y_0\in(0,K_*)$：末坐标为 $\Delta_{v_4}-gz$，前一坐标为 $\Delta_{u_3}-g\Delta_{v_4}+g^2z$。末标签3、0、5、2、25分别给唯一色0、1、2、临界带4、唯一色5；前接5到末标签0给 $t^2+g^2z<e$，前接2到0给 $1<1+g^2z<f$，前接2到5给 $1-gt^2+g^2z<h$，前接25到5给 $2t<2-3g+g^2z<i$。其余组合的端点为同一显式式子：$t^2+gt+g^2z$ 在唯一色3，$1+gt+g^2z$ 在唯一色4，$2-t+gt+g^2z$ 在唯一色5；$1-g+g^2z$ 及 $1-g(2-t)+g^2z$ 在唯一色3；$2-t+g^2z$ 在唯一色5，$t^2(1-g)+g^2z$ 在唯一色2。这些界由 (45.14)—(45.15) 核对，故第三临界双色相位也被保留。

现取任意实际第一循环，记块坐标为 $x_r(n)$、$n\in\mathbb Z/k\mathbb Z$，真实下一块为 $w=x_0(n+1)$。相位二色0强制3。相位三下端至少 $e$ 的行，若相位一用0，得 $x_1=gt+g^2x_3\ge gt+g^2e>b$，故相位一为3；相位零用5得 $x_0\ge2g>d$，用3得 $x_0=f_{333}(x_3)\le f_{333}(-1)<a$，故为0。

仅末色 $(2,1),(2,2)$ 尚需同一循环界。前者末色1若用3，则 $x_4\le-t-ga<a$，所以末标签0；相位三若用0，得 $x_3=g^2w\le g^2d<c$，所以为5，且 $x_3\ge t^2+g^2a>\theta$。后者 $x_4>0$ 直接迫使相位三为5，且 $x_3\ge t^2-gd>\theta$。两正差分别为 $(119g-27)/10$、$(9g-2)/5$。由 $b=gt+g^2\theta$，相位一仍为3，相位零仍为0。于是所有行都有 $0<x_0=K_*-g^3x_3<K_*$。

末色0、1、2、5分别强制3、0、5、25；末色 $U_4$ 时，5给 $x_4<t^2<e$，25给 $x_4>2-t-gK_*>i$，正差 $(42-177g)/5>0$，故末标签2。相位三逐行固定：色2已固定5；色3末标签3时，2给 $x_3>1+gt>f$，故为5，其他色3行 $x_4>0$ 排除5，故为2；色4末标签3时，25给 $x_3>2-t+gt>i$，故为2；色5固定25；$U_4$ 末标签0时，5给 $x_3<t^2+g^2K_*<e$，25给 $x_3>2-t>i$，故为2；$U_5$ 末标签5时，2给 $x_3<1-gt^2+g^2K_*<h$，故为25。这证明十一行的全部第一词逐块等于对应 rival。

**(b) 转移 $4\to2$。** rival 前两标签 $(2,0)$，相位二在 $C_2$，只能3或0。下一周期首标签2要求末标签 $v_4\in\{3,0,2\}$。若相位二用0，则 $y_3=-y_2/g>J_*>i$，相位三为25，末标签只剩3、0；0给 $y_3\le2-t+g^2f<J_*$，余量 $2(11-46g)/5>0$，所以只剩后三字 $(0,25,3)$。若相位二用3，则 $y_3<\theta$，相位三候选3、0、5；5只能接末标签3、0，两者使 $y_4<0$，故 $y_3>t^2>\theta$，矛盾。于是前两色 $(U_4,U_2)$ 下的完整后三行是

| 后三标签 | 后三色包络 |
| --- | --- |
| $(0,25,3)$ | $(1,5,0)$ |
| $(3,3,3)$ | $(0,U_1,0)$ |
| $(3,3,0)$ | $(0,0,1)$ |
| $(3,3,2)$ | $(U_1,0,3)$ |
| $(3,0,3)$ | $(0,2,0)$ |
| $(3,0,0)$ | $(0,1,1)$ |
| $(3,0,2)$ | $(0,1,3)$ |

颜色计算在同一个 $z=y_0\in[h,f]$ 上使用
$(y_2,y_3,y_4)=(f_{w_2}f_{u_3}f_{v_4}(z),f_{u_3}f_{v_4}(z),f_{v_4}(z))$。末标签3、0、2分别在唯一色0、1、3；$f_3f_3(z)$ 在 $B_1$，$f_3f_0(z),f_3f_2(z)$ 在唯一色0，$f_0f_3(z)$ 在唯一色2，$f_0f_0(z),f_0f_2(z)$ 在唯一色1。再按第三标签前接，给表中相位二各色；所用端点只为 $h,f$，故各栏仍为联合来源上包络。

任意第一循环的 $(1,5,0)$ 行先强制末两标签3、25及相位二标签0。相位一用3给 $x_1=-t+g^2x_3\le2g-1<a$；用5则同循环给 $x_3=2-2g+g^2w>2-2g$、$x_1>t^2+g^2(2-2g)>d$；故为0。相位零用5给 $x_0<t^2<e$，用25给 $x_0\ge2-t-g^3\phi>i$，故为2，得到 $(2,0,0,25,3)$。

其余六行相位二通常色0，故为3。例外 $(U_1,0,3)$ 行，末色3用5给 $x_4<t^2<e$，故为2；相位三为3，相位二若为0则 $x_2=gt+g^2x_4\ge gt+g^2e>b$，故也为3。后三标签依次确定如下：$(0,U_1,0)$ 的相位三用0给 $gt+g^2w>b$，故为3；$(0,0,1)$ 末标签3因 $w>0$ 不在色1，故为0；$(U_1,0,3)$ 已定为3、2；$(0,2,0)$ 的相位三用5给 $x_3\ge2g>d$，故为0；$(0,1,1)$ 的相位三用3给 $2g-1<a$，故为0且末为0；$(0,1,3)$ 的 $x_4>0$ 排除相位三标签3，故为0。

所有六行，相位一用5都因 $x_2\le-t^2$ 得 $x_1\ge2g>d$。相位三为3时，相位一用3形成三个连续3而给 $x_1<a$；相位三为0时，相位一用3给 $x_1=f_3f_3(x_3)=a+g^2(x_3-\theta)<a$，因为对应 $x_3$ 分别不超过 $gt+g^2i,g^2i$ 或严格为负，均小于 $\theta$。故相位一统一为0。相位零用5、25分别给 $x_0\le t^2(1-g^2)<e$、$x_0\ge2-t-g^2>i$，故为2；最后一行末标签5遂给 $x_4<t^2<e$，故为2。七行全部强制。

**(c) 转移 $5\to3$。** rival 前三标签 $(25,5,0)$：相位二在 $C_3$，标签0；有 $u<y_3<J_*$，$y_0\in[2t,i]$。末标签 $v_4\in\{3,0,2\}$。相位三用0时，末标签0给 $y_3\le g^2i<u$，2给负值，故只剩3；相位三用5、25时，guard 排除末标签2；$(25,3)$ 又给 $y_3\ge2-2g+2tg^2=11g-1>J_*$。前三色 $(U_5,U_3,1)$ 下只剩

| 后两标签 | 后两色包络 |
| --- | --- |
| $(0,3)$ | $(2,0)$ |
| $(5,3)$ | $(3,0)$ |
| $(5,0)$ | $(U_3,1)$ |
| $(2,3)$ | $(4,0)$ |
| $(2,0)$ | $(4,1)$ |
| $(2,2)$ | $(3,3)$ |
| $(25,0)$ | $(5,1)$ |

这些栏在同一个 $z\in[2t,i]$ 上由 $(f_{u_3}f_{v_4}(z),f_{v_4}(z))$ 得到：末3、0、2为唯一色0、1、3；$f_5f_0(z)=t^2+g^2z$ 位于 $B_3$，保留 $U_3$；另六前接像分别位于所列唯一色2、3、4、4、3、5，端点直接取 $2t,i$。没有把该 $U_3$ 当成原预算实际双色。

第一循环中 $x_0\in[h,\phi]$、$x_1\in[c,f]$、相位二色1且 $x_3>0$，故相位二用3给 $x_2<-t<a$，只能为0。相位一用0给 $x_1=g^2x_3<c$：除色5行外 $x_3\le i$；色5行末色1因 $w>0$ 固定0，相位三为25，故 $x_3\le2-t+g^2\phi$，仍由 (45.15) 得矛盾。相位一用2则 incoming guard 零，迫使相位零为2（25输出一，不能接2），但 $x_1=1+g^2x_3>1$、$x_0=1-gx_1<1-g<h$，矛盾。因此相位一为5。相位零若为2又给 $x_0=1-gt^2-g^3x_3<1-gt^2<h$，故为25。

末色0、1、3分别强制3、0、2。相位三：色2末3时，5给 $x_3\ge2g>d$，故0；色3末3时，2给 $x_3\ge1+gt^2>f$，故5；色3末2时，$x_4>0$ 排除5，故2；色4末3时，25给 $x_3\ge2-t+gt^2>i$，故2；色4末0时，25给 $x_3>2-t>i$，故2；色5固定25。$U_3$ 末0行中，2给 $x_3\ge1+g^2h>f$；已知相位零为25且 $x_1>0$，故每块 $x_0<2-t$，0又给 $x_3=g^2w<g^2(2-t)<c$，故只能5。这里 $1+gt^2-f=c>0$、$2-t+gt^2-i=b>0$，补齐七行。

三组证明均在任意 $5k$ 循环上保留真实 $w=x_0(n+1)$，并逐块强制对应 rival 词。所有包络的取得只要求 rival 的严格临界带位置；实际 $\beta$ 的颜色资格从未被提升到 $\lambda$。对原图返回应用45.1的周期提升并同步旋转，即得第一投影相干。$\square$

### 引理 45.9（恰两个不相邻实际双色的十九个必要包络）

设 $|D_\beta|\ge2$ 且没有循环相邻元素，则第一投影相干。

**证明。** 引理45.7给 $|D_\beta|=2$；这里不能把前提改成“非空”，因为单双色是另一个实际情形。如果 rival 另有两个相邻的严格临界带相位，直接应用引理45.8的**临界上包络版本**，不宣称它们在原预算都双色。否则五循环上没有相邻临界带，故临界带相位最多两处；已知两实际双色使其恰有两处。旋转后置于相位零、二，其余三相位不在临界带，且由45.7避开临界端点，因此具有唯一临界色及唯一原预算色。

设 $y_0\in B_k$、$y_2\in B_l$。根域及 $y_1\in C_k$ 给完整两步关系

| 初带 $k$ | 相位一标签 | 相位二可达带 $l$ |
| --- | --- | --- |
| 1 | 3 | 3、4、5 |
| 2 | 3 | 1、2 |
| 3 | 0 | 2、3、4、5 |
| 4 | 0 | 1、2 |
| 4 | 5 | 3 |
| 5 | 5 | 1、2 |

例如初带2相位一若用0，$y_2>J_*>i$，到不了临界带；初带4目标带1时，$y_1=f_0(y_2)\in B_2$，已出现临界相邻带而由45.8处理。其余行是 $C_k$ 与实际根域相交再取实际逆像，不允许自由挑选第二坐标。令相位三、四标签为 $u_3,v_4$，周期闭合始终要求
$$
y_4=f_{v_4}(y_0),\qquad y_3=f_{u_3}f_{v_4}(y_0)\in C_l.
\tag{45.16}
$$

**目标带1。** 初带只能2、5，相位二、三标签3，且 $y_4>\theta$，所以末标签仅5、2、25。初带2末2给 $y_4\in B_4$ 与相位零临界相邻，排除；末5、25留下第6、7行。初带5的下一首标签25要求末输出零，所以只剩末2，得第18行。

**目标带2。** 初带只能2、3、4、5，相位二标签0，相位三3或0。若相位三0，则 $y_4>J_*$，末必25；其输出一不能接初带4、5的首标签2、25；初带2、3又有 $y_0>0$，给 $y_4<2-t<J_*$，也不行。所以相位三为3且 $y_4<\theta$。末5在初带2、3给 $y_4\ge t^2-gd>\theta$，初带4、5则 guard 不合法，故末只剩3、0。末3给 $y_3=f_3f_3(y_0)=a+g^2(y_0-\theta)$；初带3、4、5时在 $B_1$，与相位二相邻，排除；初带2给第8行。末0在初带2、3、5给第9、10、19行；初带4由前两步要求 $y_2<u$，而闭合给 $y_2=gt-g^3y_0\ge gt-g^3f>u$，余量 $(9/5)g^4\phi>0$，排除。

**目标带3。** 初带只能1、3、4，相位二、三标签5、0，且 $u<y_4<J_*$。末0在初带1给 $f_0(y_0)<u$，另两初带给负值；末3也为负，故只看5、2、25。初带1给第1—3行；初带3的末5、2给第11、12行，末25给 $y_4\in B_5$ 与相位零相邻，排除；初带4末输出必须零，故只剩2，得第17行。

**目标带4。** 初带只能1、3，相位二标签2，相位三0或5。相位三5时，$3t/5<y_4<t$，guard 限末3、0、5；末3为负，末0不在所需区间，末5只在初带1可能，得第4行。相位三0时，$y_4<u$，末只能3、0。初带1末0使 $y_4\in B_2$ 与相位零相邻，末3使 $y_3=f_0f_3(y_0)\in B_2$ 与相位二相邻，均排除。初带3末3、0给第13、14行。

**目标带5。** 初带只能1、3，相位二、三标签25、5，且 $-1<y_4<3t/5$，末只可能3、0、5。初带1末3得第5行，末0使 $y_4\in B_2$ 与相位零相邻，末5给 $y_4>3t/5$，排除；初带3末3、5给第15、16行，末0使 $y_3=f_5f_0(y_0)\in B_3$ 与相位二相邻，排除。

这五个目标带的来源分支已经穷尽。所余十九行及颜色包络为

| 行 | rival 五窗 | 五相位颜色包络 |
| --- | --- | --- |
| 1 | $(3,3,5,0,5)$ | $(U_1,0,U_3,1,3)$ |
| 2 | $(3,3,5,0,2)$ | $(U_1,0,U_3,1,4)$ |
| 3 | $(3,3,5,0,25)$ | $(U_1,0,U_3,1,5)$ |
| 4 | $(3,3,2,5,5)$ | $(U_1,0,U_4,2,3)$ |
| 5 | $(3,3,25,5,3)$ | $(U_1,0,U_5,3,0)$ |
| 6 | $(0,3,3,3,5)$ | $(U_2,0,U_1,0,2)$ |
| 7 | $(0,3,3,3,25)$ | $(U_2,0,U_1,0,5)$ |
| 8 | $(0,3,0,3,3)$ | $(U_2,0,U_2,0,0)$ |
| 9 | $(0,3,0,3,0)$ | $(U_2,0,U_2,0,1)$ |
| 10 | $(5,0,0,3,0)$ | $(U_3,1,U_2,0,1)$ |
| 11 | $(5,0,5,0,5)$ | $(U_3,1,U_3,1,2)$ |
| 12 | $(5,0,5,0,2)$ | $(U_3,1,U_3,1,3)$ |
| 13 | $(5,0,2,0,3)$ | $(U_3,1,U_4,2,0)$ |
| 14 | $(5,0,2,0,0)$ | $(U_3,1,U_4,1,1)$ |
| 15 | $(5,0,25,5,3)$ | $(U_3,1,U_5,3,0)$ |
| 16 | $(5,0,25,5,5)$ | $(U_3,1,U_5,2,2)$ |
| 17 | $(2,5,5,0,2)$ | $(U_4,2,U_3,1,3)$ |
| 18 | $(25,5,3,3,2)$ | $(U_5,3,U_1,0,3)$ |
| 19 | $(25,5,0,3,0)$ | $(U_5,2,U_2,0,1)$ |

颜色栏仍由同一 $z=y_0\in B_k$ 的式(45.16)给出：末3、0、5、2、25的坐标是 $\Delta_{v_4}-gz$，相位三是 $\Delta_{u_3}-g\Delta_{v_4}+g^2z$。初带1、2的相位一为唯一色0，初带3为唯一色1，第17行为唯一色2，第18、19行分别唯一色3、2。上面的目标带筛选已删去所有临界相邻的后三相位；剩余相位三、四在两严格带之间的唯一色中。例如第8行的 $f_3f_3(z)$ 在 $B_1$ 以下，而末3在唯一色0；第9、10、19行的 $f_3f_0(z)$ 在唯一色0、末0在唯一色1；第11、12行的 $f_0f_5(z),f_0f_2(z)$ 在唯一色1；第4、16行的 $f_5f_5(z)$ 在唯一色2，第5、15行的 $f_5f_3(z)$ 在唯一色3。第1—3、13、14、17行的相位三分别由 $f_0$ 前接正末点，落在表列色1或2；第6、7、18行的 $f_3$ 前接末点落在色0。各判定取相应 $B_k$ 的两个显式端点代入；严格边界不可能由45.7保证。表是必要包络，不宣称每行实际存在，也不宣称两处 $U$ 在所有预算都是双色。

现证明十九行对任意 $5k$ 第一循环的强制。继续记 $x_r(n)$，$w=x_0(n+1)$。除 (45.14) 外还用下列正差：
$$
\begin{aligned}
2-t-gt^2+2g^3-i&=(301g-71)/10,\\
h-(1-2g^2)&=(8-33g)/5,&h-(1-ge)&=K_*/5,\\
t^2(1-g)+g^2c-s_4&=(89g-21)/5=2g^4\phi/5,\\
2-t-gt^2(1-g)-i&=g^4/5,\\
h-(1-gt^2+g^3t)&=(157g-37)/5,\\
J_*-(2-t-gL_*)&=(191-809g)/10>27/12920.
\end{aligned}
\tag{45.17}
$$

**第1—5行。** 相位一色0强制3；相位零只可能3或0。若用0，则 $x_0=gt+g^2x_2\le b$，故 $x_2\le\theta$；因此 $x_2>\theta$ 时相位零必须3。

第1—3行末点为正，强制相位三色1标签0，故 $x_2=\Delta_{\ell_2}+g^2x_4$，其中 $\ell_2$ 为实际第一来源相位二标签。标签2由 $1+g^2e>f$ 排除；第1、2行标签0分别由 $g^2f<c,g^2i<c$ 排除。第3行末色5强制25；每块相位零都有 $x_0\ge L_*$：用3时 $x_0=f_3f_3(x_2)\ge f_3f_3(c)$，用0时 $x_0>0>L_*$。故真实闭合给 $x_4\le2-t-gL_*<J_*$，相位二用0就有 $x_2<g^2J_*=c$，也排除。三行相位二皆5且 $x_2>t^2>\theta$，相位零皆3。第1行末色3的标签2给 $x_4\ge1+gt^2>f$，故末5；第2行末色4的25给 $x_4\ge2-t+gt^2>i$，故末2；第3行末25已定。

第4行 $x_2\ge e>\theta$ 固定相位零3；末色3的2仍给 $1+gt^2>f$，故末5、$x_4\ge2g$；相位三色2后接正值强制5，得 $x_3\le t^2-2g^2$。相位二用5给 $x_2<t^2<e$，用25给 $x_2\ge2-t-gt^2+2g^3>i$，故为2。第5行 $x_2\ge h>\theta$ 固定相位零3，末色0固定3；相位三色3的2给 $1+gt^2>f$，故5且 $x_3\ge2g$。相位二用2给 $x_2\le1-2g^2<h$，故25。五行全部强制。

**第6—9行。** 相位一、三的色0均固定3。第6、7行 $x_2\le b<\theta$，相位零用5给 $x_0\ge2g>d$，用3给 $f_3f_3(x_2)<a$，故0且 $x_0\ge gt-g^2>0$。第6行末色2不能用0，故5；第7行末色5固定25，两者 $x_4>\theta$。相位二用0给 $x_2=gt+g^2x_4>b$，故3。第8、9行相位零、二的5因后接色0皆给至少 $2g>d$；第8行末固定3，第9行末3给 $x_4\le-t-ga<a$，故0。两行 $x_4\le b<\theta$，相位二用3给 $f_3f_3(x_4)<a$，故0且 $x_2=gt+g^2x_4\le gt+g^2b<b<\theta$；相位零用3再给 $f_3f_3(x_2)<a$，故0。

**第10行。** 相位三色0固定3，末色1因 $w>0$ 固定0。相位二用5给 $2g>d$，用3给 $f_3f_3(x_4)<a$（$x_4<0$），故0；$x_2>0$ 又固定相位一色1为0。闭合给 $x_2=gt-g^3w$，并有 $u<x_2<gt$，下界由 $w\le f$ 及 $gt-g^3f-u=(9/5)g^4\phi$。相位零用0给 $g^2x_2<c$，用2给 $1+g^2x_2>f$，故5。

**第11、12行。** 正末点固定相位三为0；相位二用0给 $g^2f<c$，故为5或2且 $x_2>t^2$；相位一色1于是固定0。相位零用0给 $g^2f<c$，用2给 $1+g^2x_2>f$，故5。第11行末色2因 $w>0$ 固定5，第12行末色3的5给 $x_4<t^2<e$，故2。第12行 $x_4\ge e>u$；第11行已知下一块标签5，故 $w\le t$、$x_4\ge t^2-gt=g>u$。两行相位二用2都给 $1+g^2x_4>f$，故5。

**第13、14行。** $x_2\ge e>0$ 固定相位一0；相位零用0、2分别由 $g^2i<c,1+g^2e>f$ 排除，故5。第13行末固定3，相位三色2的5给 $2g>d$，故0；相位二用5、25分别给 $x_2\le t^2(1-g^2)<e$、$x_2\ge2-t-g^2>i$，故2。第14行末色1因 $w>0$ 固定0，相位三用3给 $-t+g^2w\le2g-1<a$，故0；相位二用5给 $t^2<e$，用25给 $2-t-g^3\phi>i$，故2。

**第15行。** $x_2\ge h>0$ 固定相位一0，相位零用2给 $1+g^2h>f$；相位二用2给 $x_2\le1-ge<h$，故25，且 $x_2<2-t$。相位零用0遂给 $x_0<g^2(2-t)<c$，故5。末色0固定3，相位三用2给 $1+gt^2>f$，故5。

**第16行。** 同样固定相位一0、排除相位零2。末色2因 $w>0$ 固定5，相位三色2因 $x_4>0$ 也固定5；因此 $x_3=t^2(1-g)+g^2w\ge t^2(1-g)+g^2c>s_4$。相位二用2给 $x_2=1-gx_3<h$，故25且 $x_2<2-t$；相位零用0给 $g^2(2-t)<c$，故5。

**第17行。** $w>0$ 固定末色3为2，正 $x_4$ 固定相位三色1为0；相位二用0、2分别由 $g^2f<c,1+g^2e>f$ 排除，故5，$x_2>0$ 固定相位一色2为5。相位零5给 $x_0<t^2<e$；又 $x_2=t^2+g^2x_4>t^2$，故 $x_1<t^2(1-g)$，相位零25给 $x_0>2-t-gt^2(1-g)>i$，也排除，故2。

**第18行。** $w>0$ 固定末色3为2，相位三色0固定3；相位二0给 $gt+g^2e>b$，故3。相位一色3的2给 $1+gt^2>f$，故5且 $x_1\ge2g$；相位零2给 $1-2g^2<h$，故25。

**第19行。** $w>0$ 固定末色1为0，相位三色0固定3；相位二5给 $2g>d$，3给 $f_3f_3(x_4)<a$，故0。$x_2>0$ 固定相位一色2为5；$x_4<0$ 又给 $x_2<gt$、$x_1>t^2-g^2t$，相位零2给 $x_0<1-gt^2+g^3t<h$，故25。

十九行的第一词全部逐块等于各自 rival，真实终尾始终为同一循环的下一块。每个原返回由45.1提升为这样的循环，长度为任意 $5k$；同步旋转后，同基点第一返回均为同一五字的整幂，故相干。$\square$

### 命题与例 45.10（至少两双色的覆盖及三双色实际来源）

若 $|D_\beta|\ge2$，第一投影相干；不能增加“实际双色数至多二”的前提。

**证明。** 有实际相邻对时，它们在严格临界带，45.8适用；无实际相邻对时，45.7给恰两个，45.9适用。至少三处自动含相邻对，不需额外假设。

为核对这一量词，取 $R=(2,0,0,3,3)$、$\delta=1/10000$、$\beta=\lambda-\delta$、$D=1+g^5$。全部接缝输出 guard 零，五字非常值而五为素数，故本原周期五。同一周期坐标为
$$
y_0=\frac{1+2g^4}{D},\quad y_4=-t-gy_0,\quad
y_3=-2g+g^2y_0,\quad y_2=2g^2-g^3y_0=-gy_3,\quad y_1=-gy_2.
\tag{45.18}
$$
这些式子同时满足 $y_0=1-gy_1$。有 $1<y_0<101/100$，
$$
f-y_0=\frac{g^4(2+5g^2)}{5D}>\frac1{3125}>\delta,
\qquad y_0-h>\frac1{20}>\delta.
$$
后一式由 $h<19/20$；前一式由 $g>1/5,D<2$。用45.12代入同一周期式，还得
$$
-21/50<y_3<-41/100,\quad9/100<y_2<3/25,\quad
-3/100<y_1<-1/50,\quad-9/10<y_4<-4/5.
$$
原带端点满足 $a+\delta<-21/50$、$-t^2-\delta>-41/100$、$c+\delta<9/100$、$b-\delta>3/25$。所以相位零在实际带4，相位二在实际带2，相位三在实际带1；另外两点分别仅允许色1、0，即 $D_\beta=\{0,2,3\}$。这些均为精确有理界与代数式，没有数值程序证据。本例仅反驳无条件的双色数上界，不是不相干反例；其相邻对恰由45.8处理。$\square$

### 引理 45.11（$(3,0)$：带1上侧、带2下侧）

两个 $(3,0)$ 方向均不能是首源不相干的末次分歧。

**证明。** 按45.6，rival 的 $y_1$ 与共同尾的 $z_1$ 严格分居 $s_1$ 两侧。这个阈值只在临界色0中，所以共同首色为0，两来源相位一标签均3。逆像使两第二坐标分居 $\theta$ 两侧，共同第二色为2；高坐标用5，低坐标可用0或5。低者用0时，两第三坐标分居 $s_2$，共同第三色1；高者用0，低者可用3或0，第四坐标分别跨 $s_1$ 或 $J_*$，给第四色0或5。两第二标签均5时，第三坐标跨 $H$，共同第三色3；两来源此时 incoming guard 一，色3只可用5，再逆像跨 $F_5(H)=-4/5$，第四色0。因而完整四色仅为
$$
(0,2,1,0),\qquad(0,2,1,5),\qquad(0,2,3,0).
\tag{45.19}
$$
这一步保留每一实际来源的分支，严格跨阈值来自 $\delta/g$ 间隙，不是自由四色选择。

带1的前两模式分别固定 rival 为 $(3,3,5,0,3)$、$(3,3,5,0,25)$。第一词的同周期关系给
$$
y_3=gt+g^2y_0,\qquad
y_0=-2g+g^2t^2-g^4t-g^5y_0.
$$
因 $y_0\ge-1$，有 $y_0<(585g-139)/2<-9/20$；后一正差为 $(1381-5850g)/20>1/12920$。色1在相位零要求 $\beta\ge q_1-y_0$，而
$$
(q_1-y_0)-(q_2-y_3)=\frac{1-21g}{10}-4gy_0
>\frac{1-3g}{10}>0.
$$
所以 $y_3>q_2-\beta$；它原观察色1，已不超过 $q_2+\beta$，另一端也在色2右端以下，故又允许原色2，成为第二实际双色。第二词的末色5给 $y_4>2t$，于是 $y_2=t^2+g^2y_4>t^2+2tg^2>q_3$，正差 $(47g-11)/4$；其原色2保证色3的另一端，故相位二也实际双色。

带2的前两模式分别固定 rival 为 $(0,3,0,3,3)$、$(0,3,0,0,25)$。第一词 $y_0>0$ 给 $y_4<-t$，故 $y_2=gt+g^2y_4<2g^2<q_2$，正差 $q_2-2g^2=(183g-43)/20$；原色2及正 $y_2$ 使它同时满足色1两端，产生第二双色。第二词则 $y_4<2-t$，给 $y_2=g^2y_4<g^2(2-t)<c$，连原色2都不满足。

剩余 $(0,2,3,0)$ 对任何实际第一来源都强制后四字
$$
T=(3,5,5,3).
$$
首尾色0固定3；第三色3若用2，后接色0给至少 $1+gt^2>f$，故用5；第二色2后接正第三点不能用0，故也5。固定实际终尾 $w$ 时
$$
x_2=\frac{5-19g}{2}-g^3w,\qquad
\frac{5-19g}{2}-g^3b-\theta=\frac85g^4\phi>0.
\tag{45.20}
$$
带2 rival 周期尾 $w=y_0\le b-\delta$ 遂给 $y_2>\theta$，但标签0、3又给 $y_0=gt+g^2y_2\le b-\delta$，要求 $y_2<\theta$，矛盾。带1任意 $5k$ 第一循环的下一块 $w\in H(U_1)\subset[-1,b]$，同式强制 $x_2>\theta$；相位零若用0则 $x_0=gt+g^2x_2>b$，故只能3。因此全部第一词逐块为 $(3,3,5,5,3)$，相干。

最后一步是**全返回强制**，并未断言未加终端条件的所有 $M_{3,0}$ 都为空。若对这一剩余模式加入 $A=U_1$，(45.20)同时使共同尾不可能满足 $z_1\ge s_1+\delta/g$，故受终端约束的 $M_{3,0}^{U_1}$ 为空。$\square$

### 引理 45.12（$(0,5)$：带2上侧、带3下侧）

这两个方向也被完全排除；带2上侧的剩余模式使用全返回强制。

**证明。** 两第一后继严格跨 $s_2$，首共同色1。高第一坐标用0，低者用0或3。两者都用0时，第二坐标跨 $J_*$，第二色5、两标签25；第三坐标跨 $F_{25}(J_*)=(g-5)/10$，第三色0、两标签3；第四坐标跨 $F_3((g-5)/10)=-3/5$，第四色0。低第一坐标用3时，第二坐标跨 $s_1$，第二色0、两标签3；第三坐标跨 $\theta$，第三色2，高者用5、低者用0或5，第四色分别1或3。所以完整四色恰为
$$
(1,5,0,0),\qquad(1,0,2,1),\qquad(1,0,2,3).
\tag{45.21}
$$
共同尾从 guard 一合法；以上所有接缝均按45.1保持。

第一模式在带2给 rival $(0,0,25,3,3)$，固定点
$y_0=(75-317g)/(2D)$、$D=1+g^5$，且
$y_0-c=-g^5b/D<0$，违反 $y_0\ge c+\delta$。在带3给 $(5,0,25,3,3)$，有 $y_0=(38-159g)/D>23/50$、$y_3=-2g+g^2y_0$；前一界的分子余量为 $(3533-14965g)/50>0$。相位零色2要求 $\beta\ge y_0-q_3$，而
$$
(y_0-q_3)-(q_1-y_3)
=(2-4g)y_0-(33g-3)/10
>(61-257g)/50>0.
$$
故相位三原色0的点又满足色1左端，色1右端由原色0上界保证，产生第二实际双色。

带3其余模式中，rival 是高第一后继，故相位一、二标签0、3，相位三坐标低于 $\theta$。模式 $(1,0,2,1)$ 的相位三标签0；末色1若用3，因 $y_0>0$ 得 $y_4<-t<a$，故末0，闭合给 $y_3=g^2y_0\le g^2d<c$，违反色2。模式 $(1,0,2,3)$ 的相位三标签5输出一，末色3也只能5，得 $y_3=1-3g+g^2y_0>1-3g>\theta$，正差 $4g^2/5$，违反该分支的阈值方向。

带2余下两模式，对任意 $5k$ 第一循环保持真实 $w=x_0(n+1)\in H(U_2)\subset[a,d]$，相位二色0固定3。模式 $(1,0,2,1)$ 中，末3给 $x_4\le-t-ga<a$，故末0；相位三0给 $x_3=g^2w\le g^2d<c$，故5且 $x_3=t^2+g^2w\ge t^2+g^2a>\theta$，余量 $(119g-27)/10$。模式 $(1,0,2,3)$ 中，正末点迫使相位三5，输出一又迫使末色3为5，得 $x_3=1-3g+g^2w\ge1-3g+g^2a>\theta$，余量 $(47g-11)/5$。两模式的相位一若0，给 $x_1=gt+g^2x_3>b$，故3；相位零5给至少 $2g>d$，3形成三个连续3而给 $f_{333}(x_3)<a$，故只能0。

因此全部第一词逐块分别为 $(0,3,3,5,0)$ 或 $(0,3,3,5,5)$，不容不同同步返回。这完成带2上侧的全返回排除，**不推出未约束终端的 $M_{0,5}$ 为空**。$\square$

### 引理 45.13（$(5,2)$：带3上侧、带4下侧）

对这两个方向，未加终端颜色的实际局部 $M_{5,2}$ 已为空。

**证明。** 两第一后继跨 $s_3$，第一色1；高者用0，低者用3或0。低者用3时，两第二坐标跨 $s_1$，第二色0、标签3；第三坐标跨 $\theta$，第三色2，高者5、低者0或5，给第四色1或3。

两第一标签都0时，第二坐标跨 $u$，第二色1或2。第二色1时，高者用0，低者0或3；两者都0使第三坐标跨 $v_*$，第三色0、标签3，第四坐标跨 $-2/5$，第四色0或1；低者用3使第三坐标跨 $s_1$，第三色0，再逆像跨 $\theta$，第四色2。第二色2时，低者用0、高者0或5；都0仍给第三色0、第四色0或1；高者5时第三坐标跨 $s_2$，第三色1，高者0、低者3或0，第四色分别0或5。因此九种完整必要四色是
$$
\begin{gathered}
(1,0,2,1),(1,0,2,3),\\
(1,1,0,0),(1,1,0,1),(1,1,0,2),\\
(1,2,0,0),(1,2,0,1),(1,2,1,0),(1,2,1,5).
\end{gathered}
\tag{45.22}
$$
所用逆阈值等式为 $F_0(s_3)=u$、$F_0(u)=v_*$、$F_3(v_*)=-2/5$、$F_3(s_1)=\theta$、$F_5(\theta)=H$。阈值 $s_3,v_*$ 分别只在临界色1、0内，$u$ 只在1、2内，$-2/5$ 只在0、1内，保证没有漏掉其他共同色。

**带3上侧。** rival 相位零标签 $R_0=5$，$e+\delta\le y_0\le d-\delta$，第一后继为低者。若其**相位一**标签 $R_1=3$，则 $y_1\le-t^2$，所以由相位零分支5得 $y_0=t^2-gy_1\ge2g>d$，矛盾。这排除第一行组；不是把相位零标签称为3。于是 $R_1=0$，第二坐标是高者，$y_2>u$。第二色1的三项全部给 $y_2>u>q_2$，而原色1上界为 $q_2+\beta$，故又满足色2，产生第二实际双色；正差 $u-q_2=(5-21g)/20$。

剩余第二色2的四项分别如下。$(1,2,0,0)$ 固定 rival $(5,0,0,3,3)$，给 $y_2=2g^2-g^3y_0<2g^2<u$，违反 $y_2>u$；正差 $u-2g^2=(81g-19)/10$。$(1,2,0,1)$ 先由 $y_0>0$ 排除末3，故词 $(5,0,0,3,0)$；周期给 $y_2=gt-g^3y_0<gt$、$y_0=t^2+g^2y_2$。相位零色3要求 $\beta\ge q_3-y_0$，而
$$
(q_3-y_0)-(y_2-q_2)
=2c-(1+g^2)y_2
>2c-(1+g^2)gt=\frac{157g-37}{5}>0.
$$
所以相位二原色2又满足色1上端；下端由正原色2保证，产生第二双色。$(1,2,1,0)$ 固定词 $(5,0,5,0,3)$，给 $y_3=gt+g^2y_0\ge gt+g^2e>b$，违反色1。$(1,2,1,5)$ 固定 $(5,0,5,0,25)$，末色5给 $y_2=t^2+g^2y_4>t^2+2tg^2>q_3$；原色2保证色3另一端，故第二双色。带3九项全部排除。

**带4下侧。** rival 相位零标签 $R_0=2$，$h+\delta\le y_0\le f-\delta$，第一后继为高者，所以 $R_1=0$。第一行组的 $(1,0,2,1)$ 后继标签0、3、0，末3因 $y_0>0$ 不在色1，故末0，给 $y_3=g^2y_0\le g^2f<c$。$(1,0,2,3)$ 后继标签0、3、5，输出一使末5，给 $y_3=1-3g+g^2y_0>\theta$，但此分支应低于 $\theta$。其余七项两第一标签都0，rival 第二坐标为低者，$y_2<u$。

$(1,1,0,0)$ 固定 $(2,0,0,3,3)$，给 $y_2=2g^2-g^3y_0>0$、$y_0=1+g^2y_2>1$。色3在相位零要求 $\beta\ge y_0-q_4$，而
$$
(y_0-q_4)-(q_2-y_2)
=(1-g^3)y_0+2g^2-q_4-q_2
>g^3t>0.
$$
所以相位二原色1又满足色2左端，产生第二双色。$(1,1,0,1)$ 排除末3后固定 $(2,0,0,3,0)$，给 $y_2=gt-g^3y_0\ge gt-g^3f>u$，余量 $(9/5)g^4\phi$，违反低侧。$(1,1,0,2)$ 中低第二坐标用3，前四标签 $(2,0,3,3)$；第四色2的坐标高于 $\theta>g$，只能末5，其输出一不能接下一周期首标签2，guard 矛盾。

$(1,2,0,0)$ 仍固定 $(2,0,0,3,3)$，给 $y_2<2g^2<q_2$；原色2因此同时允许色1。$(1,2,0,1)$ 固定 $(2,0,0,3,0)$，仍给 $y_2>u$。$(1,2,1,0)$ 的低第三坐标用3、末3，仍为 $(2,0,0,3,3)$，故 $y_2<q_2$ 产生第二双色。$(1,2,1,5)$ 的低第三坐标用0、末25，其输出一同样不能接下一首标签2。带4九项也全部排除。

每项仅用同一 rival 周期、原色成员关系或原 guard，故不论共同尾终端为何都不成立，即相应实际 $M_{5,2}^{\{0,\ldots,5\}}=\varnothing$。引理45.5于是排除任意 $5k$ 末次分歧。$\square$

### 引理 45.14（$(2,25)$：带4上侧的局部空性）

带4唯一双色 rival 对应的未加终端颜色 $M_{2,25}$ 为空。

**证明。** 记 $Y=y_0$，带4给 $h+\delta\le Y\le f-\delta$，相位零标签2及 guard 零，故
$$
y_1\in[s_3+\delta/g,s_4-\delta/g].
$$
共同尾须从 guard 一合法；高首标签25取色4，给 $x_1\ge s_4+\delta/g$。因 $b<s_4<e$，phase 1 共同色只能2，且共同尾标签为5。因此
$$
s_2+\delta/g\le x_2\le\eta-\delta/g^2.
\tag{45.23}
$$
rival 相位一单色2给 $y_1>b-\delta$，使用弱式也足够。若此处用0，则 $y_2\le-(b-\delta)/g<a+\delta$，因为
$$
b+ga-(1-g)\delta>b+ga-(1-g)\lambda=2g^2/5>0.
\tag{45.24}
$$
它只能取色0，而 $x_2\ge s_2+\delta/g>-t^2-\delta$ 不能取色0，矛盾。故 rival 相位一也为5，给 $y_2\ge\eta+\delta/g^2$。由 $b<\eta<e$，相位二共同色也只能2，rival $y_2>\eta>g$ 强制标签5，继而
$$
s_2+\delta/g\le y_3\le g/5-\delta/g^3.
$$
此区间在根0内部，故相位三标签0且 $y_4\ge-1/5+\delta/g^4$。下一周期首标签2要求末输出零，末标签只可能3、0、2。末0给 $y_4=-gY\le-gh<-1/5$，其中 $gh=(7-25g)/5>1/5$；末3更低，均矛盾。故 rival 必为 $(2,5,5,0,2)$，其实际周期固定点为
$$
Y=\frac{21-85g}{D},\quad D=1+g^5,\quad
y_2=t^2+g^2-g^3Y.
$$
精确恒等式
$$
(y_2-e)-(Y-h)=\frac{54g^4}{5D}>0
\tag{45.25}
$$
使 $y_2>e+\delta$；原共同色2又给 $y_2\le d-\delta<f-\delta$，所以相位二还严格允许原色3，产生第二实际双色。矛盾在检查第一终端以前已经发生，故未约束终端的 $M_{2,25}^{\{0,\ldots,5\}}$ 确实为空；加入 $A=U_4$ 仍为空。$\square$

### 引理 45.15（$(2,25)$：带5下侧的同源终端排除）

带5唯一双色 rival 的局部共同尾，若尚未被 rival 周期及唯一双色条件排除，只能具有
$$
R=(25,5,5,0,0),\qquad C=(2,2,1,1),\qquad T=(5,5,0,0).
\tag{45.26}
$$
它的同一五步终值不能取下一相位零所需的色4或5。因此 $M_{2,25}^{U_5}=\varnothing$，且任意 $5k$ 不相干返回均被排除。

**证明。** 带5给 $2t+\delta\le Y=y_0\le i-\delta$，相位零标签25，输出一，
$$
y_1\in[s_4+\delta/g,t-\delta/g].
$$
低首标签2必须取色4，给共同尾 $x_1\le s_4-\delta/g$。两相位一共享色2，rival 标签5，且
$$
s_2+\delta/g\le y_2\le\eta-\delta/g^2.
\tag{45.27}
$$
共同尾此处仅可用0或5。

**共同尾先用0。** 此时 $x_2\le s_2-\delta/g$，不能取色2；rival 的 $y_2$ 不能取色0，所以相位二共同色1。rival 的 $y_2$ 在根0内部，标签0。共同尾 $x_2$ 若用3，则 $x_3\le s_1-\delta/g$，相位三只能色0；若用0，则 $x_3\ge J_*+\delta/g^2>i$，相位三只能色5。

色5情形，$y_3\ge2t+\delta$，故 $y_1=t^2+g^2y_3\ge t^2+2g^2t+g^2\delta$，于是
$$
y_1-e-\delta>\frac{107g-25}{10}>0
$$
（使用 $\delta<\lambda$）；相位一原色2的上界保证色3右端，所以出现第二实际双色。

色0情形，rival 前四标签 $(25,5,0,3)$，末标签仅3、0、2，因为下一首标签25要求 incoming 零。末3、0分别给
$$
\begin{aligned}
Y&=(36-147g)/D,&(y_3-a)-(i-Y)&=4(394g-93)/D>0,\\
Y&=(17-61g)/(2D),&(y_2-c)-(i-Y)&=(10773g-2543)/(5D)>0.
\end{aligned}
\tag{45.28}
$$
由 $\delta\le i-Y$，第一项使原色0的 $y_3>a+\delta$，色1另一端由原色0上界保证；第二项使原色1的 $y_2>c+\delta$，色2另一端由原色1上界保证。都产生第二实际双色。末2给 $y_4=1-gY$，故
$$
y_2>gt+g^2-g^3i>b,
\qquad gt+g^2-g^3i-b=(395g-93)/10>0,
$$
直接违反色1。三个正分子由 $394g-93>3/305$、$10773g-2543>41/305$、$395g-93>75/305$ 核对。共同尾先用0的全部分支已排除。

**共同尾先用5。** 此时 $x_2\ge\eta+\delta/g^2$ 而 $y_2\le\eta-\delta/g^2$，故相位二共同色2。若 rival 此处用0，由单色2得 $y_2\ge b-\delta$，再由 (45.24) 得 $y_3<a+\delta$，只能色0；但共同尾 $x_2>\eta>g$ 必用5，给
$$
s_2+\delta/g\le x_3\le g/5-\delta/g^3,
\tag{45.29}
$$
不能取色0。故 rival 相位二也为5，$y_3\ge g/5+\delta/g^3$。式(45.29)在临界唯一色1区，所以相位三共同色1。共同尾 $x_3$ 在根0内部；rival 的 $y_3>0$，在色1也只可用0。于是
$$
x_4\ge-1/5+\delta/g^4,\qquad y_4\le-1/5-\delta/g^4.
\tag{45.30}
$$
rival 末标签仍仅3、0、2；2给 $y_4=1-gY>0$，违反上界；3给 $y_4=-t-gY<a$，实际色只能0，而共同尾 $x_4>-1/5$ 不能取色0。故末0，得到 (45.26) 的 rival。此时 $-1/3<y_4=-gY<-1/5$，处于唯一临界色1区，第四色固定1。共同尾 $x_4>-1/5$ 在色1只能用0，故四尾也固定为 $T$。

对同一共同尾的实际终值 $w=x_5$，(45.30)给
$$
w=-x_4/g\le\frac1{5g}-\frac{\delta}{g^5},\qquad
h+\delta-\left(\frac1{5g}-\frac{\delta}{g^5}\right)
=c+\delta(1+g^{-5})>0.
\tag{45.31}
$$
但是下一相位零的必要标量集合为 $H(U_5)=E_4^\beta\cup E_5^\beta$，全部点至少 $h+\delta$。因此 $w\notin H(U_5)$。精确的递推基值是 $\mathcal K_s^{U_5}(\varnothing)=I_s\cap H(U_5)$，故得到 $M_{2,25}^{U_5}=\varnothing$；没有把标量集合 $H(U_5)$ 当作颜色指标集代入上标。

由45.5，任何 $5k$ 不相干返回在该带必须提取这一个方向的固定字面四尾，并保留同一个终端、其下一相位颜色及原 SCC 回归。它与 (45.31) 矛盾，完成带5排除。这里不声称未加终端的局部 $M$ 为空。$\square$

### 定理 45.16（给定原完整图的本原五周期首源相干）

在45.1的实际来源、原 guard、闭六格、$0<\beta<\lambda$ 和给定完整规范全包含图假设下，若含环配对 SCC 的第二来源投影为 coherent singleton rival，字面来源本原周期五，则其第一来源投影满足同步相干性 (45.6)。

**证明。** 按实际 $|D_\beta|$ 分成零、一个、至少两个。零双色由45.3；至少两个由45.8—45.10，三处以上先取循环相邻对。单双色若不相干，45.5—45.6在同一实际宏 SCC 中提取八方向之一；45.11—45.15全部排除。其机制分别为

| 标签对及带位 | 排除机制 |
| --- | --- |
| $(3,0)$，带1上侧 | 两四色给实际额外双色；余下一四色强制全部 $5k$ 循环 |
| $(3,0)$，带2下侧 | 实际额外双色、违反原色或 rival 自身周期矛盾 |
| $(0,5)$，带2上侧 | 一四色违反原色；余下两四色强制全部 $5k$ 循环 |
| $(0,5)$，带3下侧 | 实际额外双色、原色或固定阈值矛盾 |
| $(5,2)$，带3上侧 | 九四色全部为实际额外双色、阈值或原色矛盾，局部 $M$ 为空 |
| $(5,2)$，带4下侧 | 九四色全部为实际额外双色、周期或 guard 矛盾，局部 $M$ 为空 |
| $(2,25)$，带4上侧 | rival 五周期强制第二实际双色，局部 $M$ 为空 |
| $(2,25)$，带5下侧 | 局部 $M$ 可有区间；同一终值缺失下一相位色4、5 |

分类没有把任一临界带成员当作实际双色，也没有把第一来源周期限制为五：所有返回长度 $5k$ 都由原全包含提升、固定字面尾及原颜色条件控制。全部单点、根端点和无有限尾地址仍保留。各基点同步返回相同，即得结论。$\square$

这是给定完整图的条件定理。其证明未要求任意实预算自动存在有限图，也没有把第31章的数域构图假设移除。

### 命题 45.17（真实局部折叠及其非延续终端）

存在实际本原五周期、唯一双色带5的 rival，其未约束终端局部 $M_{2,25}$ 含非退化区间；两首标签和字面四尾可由原完整图的全包含路径表示，但同一终端不能续接为下一相位零的配对顶点。

**证明。** 固定
$$
\delta=g^4/40,\qquad \beta=\lambda-g^4/40=(14g-3)/8,
\qquad R=(25,5,5,0,0),\quad D=1+g^5.
$$
$0<\delta<1/10240<\lambda$。相位 guards 为 $(0,1,1,1,0,0)$，所有接缝合法；非常值五字的本原周期为五。同一周期的坐标为
$$
Y=\frac{9-27g}{2D},\quad y_4=-gY,\quad y_3=g^2Y,
\quad y_2=t^2-g^3Y,\quad y_1=1-3g+g^4Y.
\tag{45.32}
$$
临界带两端裕量为
$$
i-Y=\frac{1919-8129g}{10D}>\frac3{25840}>\delta,
\qquad Y-2t=\frac{1945g-459}{2D}>\frac9{244}>\delta.
$$
第一界用 $g<305/1292,D<2$，第二界用 $g>72/305,D<2$。故相位零严格拥有原色4、5。其余坐标由同一式(45.32)满足
$$
1/4<y_1<1/3,\quad17/48<y_2<t^2<e,\quad
0<y_3<g^2i<c,\quad-1/3<y_4<-1/5.
$$
这些是临界唯一色2、2、1、1区，且到指定原色内部端点的距离大于 $1/100>\delta$；例如 $c-g^2i=(23-97g)/10>7/720$ 保证唯一临界色界，而 $g^2(2t)<y_3<g^2i$ 连同45.12直接给色1两端的内部裕量。因而原预算恰有相位零双色。

取共同四尾 $T=(5,5,0,0)$，固定 phase 4 坐标 $x_4=-1/10$。沿同一来源前接及取其合法终值，得到
$$
\begin{aligned}
x_5&=(4+g)/10,&x_3&=g/10,\\
x_2&=(4-g)/10,&x_1&=(6-13g)/10,\\
x_0^-&=f_2(x_1)=(23-58g)/10=h+g^4/10,\\
x_0^+&=f_{25}(x_1)=(28-63g)/10=i+g^4/10.
\end{aligned}
\tag{45.33}
$$
特别地 $x_4=f_0(x_5)$，没有把 $x_4$ 错当第五步终端。两个首点分别在原色4、5内部：低首点距色4临界下端为 $g^4/10=4\delta$，距实际下端为 $3\delta$；其色4上端及高首点色5两端由 $h<i<\phi$ 和45.12给严格余量。四个共同后继分别在原色2、2、1、1内部，粗界 $1/4<x_1<1/3$、$1/3<x_2<2/5$、$0<x_3<1/40$、$x_4=-1/10$ 与45.3直接核对；各点也严格在相应合法根域及 incoming guard 内。低首标签2输出零，高首标签25输出一；共同下一标签5从两 guard 都合法，随后输出 guard 相同。

实际终值 $x_5\in I_0$ 按满像选一次实际合法尾，便同时承担 $2T$ 与 $25T$ 的全部坐标。所有颜色和 guard 不等式严格，故在 $x_5$ 的一个小开区间 $W$ 内仍成立。固定 $T$ 的四步像 $f_T(W)$ 是斜率 $g^4$ 的非退化区间，属于 $J_{2,25}\cap\mathcal K_1^{\{0,\ldots,5\}}(2,2,1,1)$。这是一个真实共同尾区间，不是两个独立点或临界包络拼接。

本例预算、周期点及观察端点均在 $\mathbb Q(t)$。引理31.2的构造可在有限端点族中加入五个周期点：取其系数共同分母 $q$，再取同时覆盖这些点及原端点共轭值、并满足 $R_B\ge g\max_\ell|\Delta_\ell'|/(1-g)$ 的界，令
$B=\{z\in q^{-1}\mathbb Z[t]\cap X:|z'|\le R_B\}$。撇号表示 $t'=-\phi$ 的共轭嵌入；两个嵌入同时有界使 $B$ 有限，$F_\ell(z)'=gz'-g\Delta_\ell'$ 使其逆闭合。按原单点及相邻闭片规则取完整图，五个 rival 单点及其实际周期边都存在。

在 $W$ 中避开有限多个各前缀仿射逆像的端点，选取更小开区间，使两个首点和全部共同尾坐标各留在固定规范基本片的内部。规范路径完备性及逆闭合给整片包含 $Q\subseteq F_\ell(P)$，颜色端点在 $B$ 中保证整片允许指定原色。因而两首标签和同一字面四尾有原非退化基本片的全包含路径；下一共同标签5之后 guard 同步，同一个非退化共同像使后续规范片相同，终端第一节点也相同。这只证明原单来源图中的局部路径以及位置零至四的共同出发颜色，没有制造配对 SCC。

其共同终端仍是 $x_5=(4+g)/10$ 附近的原片。引理45.15的 (45.31) 对该全包含路径中的每个终端点成立，因此整个终片在 $h+\delta$ 以下，缺失色4、5。rival 的下一单点是同一 $Y$，只能允许色4、5；二者在终端无共同允许色，故不能成为下一宏相位的配对顶点，更不能回到同一宏 SCC。有限出发观察后的终端未另读一次色，但**复用为下一块**必须满足那一块的实际出发颜色，这正是失败条件。$\square$

### 命题 45.18（折叠与可复用边界的条件）

在本章的来源及记录合同内，局部 body-to-boundary 替换必须保留同一来源尾的延续条件；局部四步同色及合流不足以成为可重复边界。

**证明。** $M_{\ell,m}^{\{0,\ldots,5\}}$ 仅表达两首标签和四个原观察可由同一个合法尾实现。实际复用还要求该尾的同一五步终值属于 $H(U_j)$、保留终端 guard 与原规范片全包含，并在同一实际宏 SCC 中有返程。45.17给真实非退化局部折叠和同一原第一终点，而45.31证明同一终值缺失下一相位颜色，故局部折叠不能复用。45.5的正反路径论证也分别保留宏 SCC 回归，而没有以局部非空性代替它。$\square$

这回答了本章限定的折叠问题：完整的本原五周期分类排除了 coherent singleton rival 对面的可复用第一来源分支；区分局部折叠与可复用边界的精确条件，是同一终值的下一相位闭颜色、实际 guard、原全包含节点及 SCC 返程共同成立。本章不把五种窗口解释成五种基本操作，不声称折叠生成物理时间或时空，也不推出全局半径值或取得、所有周期 singleton 消除、解码器记忆分类、形式验证或原创性结论。

## 45.99 追加锚（本行以下为增补区）
## 46. 共同来源的有限未来碰撞分离判据与一个深度二实例

单点竞争来源的周期相位只确定竞争方的当前标量，并不确定共同颜色历史。要排除一个局部跨色碰撞，还须保留共同字面尾部在后续相位中的合法延续条件。本章给出这一接口的充分判据：若所有最后不同标签的共同尾碰撞，在某个有限未来深度都消失，则原全包含 SCC 的第一来源返回相干。随后给出同一个实际五周期来源上的严格深度一见证和整个相应碰撞条目的深度二排除。

所用公开前提为本卷[固定版本](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md)的定义14.5、命题14.6、定理14.7与17.2、定义31.3与定理31.4、引理36.16、定理36.22、引理36.29及命题39.6.1。下面重述所需合同，并给出本章判据、紧致性和实例的完整证明。不重新分类短奇周期，也不把局部相位数据当作一个已实现的 SCC。

### 46.1 原来源、guard、闭颜色与观察时序

固定

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad g^2+4g=1,\qquad
\lambda=\frac{t^2}{10}=\frac{1-g}{20}.
\tag{46.1}
$$

来源域为 $A_0=\Omega$，即无相邻一的单侧无限位地址；$A_1=\{\omega\in\Omega:\omega_0=0\}\subset A_0$。窗口从低位到高位读，$T=\sigma^3$ 删除一个三位窗口。原窗口与映射为

$$
\begin{gathered}
\Lambda=\{3,0,5,2,25\}=\{010,000,001,100,101\},\\
I_0=X=[-1,\phi],\qquad I_1=[-1,t],\\
0\to0:3,0,2;\qquad 0\to1:5,25;\qquad
1\to0:3,0;\qquad 1\to1:5,\\
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t),\qquad f_\ell(x)=\Delta_\ell-gx.
\end{gathered}
\tag{46.2}
$$

这里 $25$ 是一个窗口标签，$0$ 是空窗。标签自身决定 outgoing guard：

$$
o(3)=o(0)=o(2)=0,\qquad o(5)=o(25)=1.
\tag{46.3}
$$

对合法有限词 $w=w_0\cdots w_{h-1}$，前接次序为 $f_w=f_{w_0}\circ\cdots\circ f_{w_{h-1}}$，空词的映射为恒等映射；因此 $f_w(x)=a_w+(-g)^h x$。

两个状态使用同一个连续窗口级数

$$
\kappa_s(\omega)=\sum_{j\ge0}(-g)^j\Delta_{\sigma_j(\omega)}.
\tag{46.4}
$$

其状态相对满像为 $\kappa_s(A_s)=I_s$。对合法前接，$\kappa_s(\ell\tau)=f_\ell(\kappa_{o(\ell)}(\tau))$。为核对满像及端点，状态零的根分支按空间顺序是

$$
\begin{array}{c|ccccc}
\ell&3&0&5&2&25\\ \hline
f_\ell(I_{o(\ell)})
&[-1,-t^2]&[-t^2,g]&[g,t]&[t,2t]&[2t,\phi].
\end{array}
\tag{46.5}
$$

状态一保留前三段。它们分别覆盖 $I_0,I_1$。任取 $x\in I_s$，逐步选择包含当前点的合法闭分支并取逆像，得到一致的标签、guard 和有界尾坐标。迭代仿射等式的余项是 $(-g)^N x_N\to0$，故这些选择拼成一条编码 $x$ 的实际地址；不是逐坐标另选来源。

还使用状态相对纤维至多二这一事实。其原因是各层合法前缀柱内部互不相交，首次不同标签只能发生于两个相邻柱的共同端点，此时两侧尾值均被强制为状态区间的极值。极值地址为 $L=(3,25)^\infty$ 编码 $-1$，$R=(25,3)^\infty$ 从状态零编码 $\phi$，$5L$ 从状态一编码 $t$；由 $f_3(\phi)=-1$、$f_{25}(-1)=\phi$、$f_5(-1)=t$，且每个状态的外端只在一个根分支中，每一步的极值尾都唯一被强制。因此每侧不再有分支，同一 guard、同一标量至多有两条地址。全部接触点和极值地址均保留。

沿用原六格及一次固定的合法端点归属 $Q$。令

$$
\begin{gathered}
q_1=-t^2-\lambda,\quad q_2=g-3\lambda,\quad
q_3=t-5\lambda,\quad q_4=2t-7\lambda,\quad q_5=2t+\lambda,\\
J_0=[-1,q_1],\quad J_1=[q_1,q_2],\quad
J_2=[q_2,q_3],\quad J_3=[q_3,q_4],\quad
J_4=[q_4,q_5],\quad J_5=[q_5,\phi].
\end{gathered}
\tag{46.6}
$$

实际格是 $Q^{-1}(c)$，闭包为 $J_c$。对原预算 $0\le b<\lambda$，只使用原闭扩张

$$
E_c^b=X\cap(J_c+[-b,b])=[L_c,U_c].
\tag{46.7}
$$

闭关系 $x\in E_c^b$ 不自动保证在每种端点归属下实际取得颜色 $c$。实际取得是 $Q(\operatorname{clip}_X(x+e))$。若 $b>0$ 且 $\operatorname{dist}(x,J_c)<b$，可将最近点移入格内部，保持误差严格小于 $b$；这种取得适用于每一种固定合法归属。等号情形须检查最近端点的实际拥有者，$b=0$ 时须直接检查实际格成员资格。本章的判据使用包含实际关系的闭关系，实例则另证严格余量。

一段长 $M$ 的边历史在出发坐标 $0,\ldots,M-1$ 取得 $M$ 个颜色；走完 $M$ 条边后的坐标 $M$ 未观察。有限路径随后可接任意合法终尾，不能额外要求终端颜色。

### 46.2 从实际单点 SCC 提取本原相位

在 $b\in\mathbb Q(t)\cap[0,\lambda)$ 的原完整闭配对图中，取一个实际含环 SCC $S$。单来源顶点保留 guard 和非空闭片；原边规则是

$$
(s,P)\xrightarrow{\ell}(s',P')
\quad\Longleftrightarrow\quad
s\xrightarrow{\ell}s'\text{ 合法},\quad
P\subseteq f_\ell(I_{s'}),\quad f_\ell(P')\subseteq P.
\tag{46.8}
$$

配对顶点的两片允许至少一个共同出发颜色，且整片都包含于相应 $E_c^b$。定理31.4保证：固定终端两片中的一对点及各自一条合法尾，任一有限配对路径均由这一对尾联合倒向提升；无限路径也有同一对实际地址的收缩提升。以下始终使用全包含规则，不以相交替代包含，也不以指定的周期词制造图片或 SCC。

这一提升的直接理由是：有限路径从固定终尾倒向置 $x_j=f_{\ell_j}(x_{j+1})$，(46.8)逐步保证 $x_j\in P_j$；合法 guard 保证前接的整条地址合法，级数等式保证这些都是该同一地址的实际坐标。两分量各用一次固定的终尾，遂同时取得各共同闭成员关系。对无限路径，标签和 guard 已给出一条合法无限地址；固定位置 $j$ 的有限倒向坐标，等于该地址级数的前 $n-j$ 项加趋零的有界余项 $(-g)^{n-j}x_n$，故收敛到同一地址的实际坐标。各 $P_j$ 和 $E_c^b$ 闭，故极限仍在原片和所需闭颜色中。这个证明包含单点、支撑端点及无有限尾编码的情形。

一个来源投影称为**返回相干**，是指同一基点任意两个非空返回词 $A,B$，长度为 $a,b$ 时，在 $L=\operatorname{lcm}(a,b)$ 满足 $A^{L/a}=B^{L/b}$。这是来源字面词的条件；路径和颜色词仍可不同。

**引理46.2.1（单点传播、本原相位与实际坐标）。** 假设 $S$ 某顶点的第二来源片为单点。则整个 $S$ 的第二片均为单点，第二来源返回相干。存在一个本原词 $V$、$p=|V|$ 及映射

$$
\vartheta:V(S)\longrightarrow\mathbb Z/p\mathbb Z,
\qquad \vartheta(w)=\vartheta(v)+1
\tag{46.9}
$$

使每条内部边 $v\to w$ 的第二标签为 $V_{\vartheta(v)}$。若 $y_r$ 是字面周期地址 $V^\infty$ 从相位 $r$ 出发的标量，则相位 $r$ 的每个第二片恰为 $\{y_r\}$。所有返回长度都是 $p$ 的倍数；不要求存在长度恰为 $p$ 的返回。

**证明。** 若当前片是单点，(46.8) 和 $f_\ell$ 的单射性迫使后继非空片也为单点；强连通性使单点传播到全分量。若第二来源不相干，取同基点两个返回并重复到同长 $L$，第二词 $B_0\ne B_1$。在基点第二单点选一条实际尾，第一片也固定一条实际尾。对四个返回拼接使用同一对尾，全包含提升给四条第二地址

$$
B_0B_0\tau,\quad B_0B_1\tau,\quad
B_1B_0\tau,\quad B_1B_1\tau.
$$

它们从同一 guard 编码同一单点，等长不同块使四条地址两两不同，与46.1的纤维至多二矛盾。因此第二来源相干。

为明确相位提取，固定基点 $q$ 的一个最短非空返回 $C$，取其第二无限词的最短周期块 $V$。每个第二返回词 $B$ 与 $C$ 同步相等，故 $B^\infty=C^\infty=V^\infty$，且 $p\mid |B|$。这里最短周期整除一切周期：把周期无限词按其已有周期延伸到双侧，保持它的整数平移形成 $\mathbb Z$ 的子群，最小正生成元就是 $p$。

令 $\vartheta(q)=0$，对任一 $v$ 用 $q$ 到 $v$ 的路径长度模 $p$ 定义 $\vartheta(v)$。给两条这样的路径接同一条 $v$ 到 $q$ 的路径，所得返回长度均被 $p$ 整除，所以相位良定义；空返回长度零亦满足整除。内部边使相位加一。将到该边的路径及回 $q$ 路径拼成返回，其第二词是 $V$ 的整幂，故边标签是相应的 $V_{\vartheta(v)}$。

对任一顶点取一条经过它的非空返回。该返回第二词是相位旋转的 $V$ 的整幂，重复返回从原 guard 合法，因而给实际周期地址。第二单点被此返回的仿射前接映射送入自身；收缩映射固定点唯一，等于该实际周期地址的标量 $y_r$。这同时证明了实际合法性和坐标唯一性。$\square$

定义原预算的相位颜色集及其包络

$$
\mathcal C_r=\{c:y_r\in E_c^b\},\qquad
K_r=\bigcup_{c\in\mathcal C_r}E_c^b,
\qquad r\in\mathbb Z/p\mathbb Z.
\tag{46.10}
$$

每个 $\mathcal C_r$ 非空且至多含两个相邻颜色。确实，相邻切点间距依次为 $t-2\lambda,t^2-2\lambda,t-2\lambda,8\lambda$，均严格大于 $2\lambda$；所以两个不相邻的原闭扩张在 $b<\lambda$ 时不能相交。若两个相邻扩张都含 $y_r$，它们的并集相连。因此 $K_r$ 是闭区间。这个结论是逐相位的，未限制整个周期的双色相位数；46.8将给出无界的实际地址例子。

### 46.3 保留同一实际尾的有限未来集合

对相位 $r$、incoming guard $s$ 及整数 $N\ge0$，定义

$$
H_{r,s}^{(0)}=I_s,\qquad
H_{r,s}^{(N+1)}
=K_r\cap\bigcup_{s\xrightarrow{\ell}s'\ \mathrm{合法}}
f_\ell\bigl(H_{r+1,s'}^{(N)}\bigr).
\tag{46.11}
$$

这里及以后相位下标均模 $p$。这是原实际分支上的集合递推，不是新的图归约。

**引理46.3.1（有限视界的精确语义）。** $H_{r,s}^{(N)}$ 是有限个闭区间的并，允许空集及单点，且

$$
H_{r,s}^{(N+1)}\subseteq H_{r,s}^{(N)}\subseteq I_s.
\tag{46.12}
$$

此外，$x\in H_{r,s}^{(N)}$ 当且仅当存在一条实际地址 $\tau\in A_s$，使

$$
\kappa_s(\tau)=x,\qquad
\kappa_0(T^j\tau)\in K_{r+j}\quad(0\le j<N).
\tag{46.13}
$$

坐标 $N$ 不受观察约束，全部坐标由同一条 $\tau$ 承担。

**证明。** 零层是闭区间；仿射像、有限并和闭区间交保持有限闭区间并，归纳给出第一项。合法根像均在 $I_s$ 中，故 $H^{(1)}\subseteq H^{(0)}$；递推对后继集合单调，归纳给出(46.12)。

零层的语义就是状态相对满像。若 $x\in H_{r,s}^{(N+1)}$，选一条递推中的合法边及一个 $z\in H_{r+1,s'}^{(N)}$ 使 $x=f_\ell(z)$。归纳选一条编码 $z$ 并承担后续全部 $N$ 个约束的实际尾，前接 $\ell$ 得到同一实际地址，首坐标另由 $x\in K_r$ 保证。反向，对(46.13)的地址剥离其实际首标签，得到同一后继尾及递推成员关系。归纳结束。$\square$

因此，$H^{(N)}$ 不是把 $N$ 个独立边际可行点拼起来的集合。它也不要求未来地址留在指定 $S$ 内；它包含所有满足原相位闭颜色约束的实际地址，这一放宽将在充分性证明中使用。

### 46.4 原闭颜色的有符号共同尾碰撞区间

对 $\ell\ne m$ 及 $c,d\in\mathcal C_r$，令 $s=\max\{o(\ell),o(m)\}$，定义

$$
\mathcal I_{\ell,m}^{c,d}
=I_s\cap f_\ell^{-1}(E_c^b)\cap f_m^{-1}(E_d^b).
\tag{46.14}
$$

它检测的是一个共同尾标量 $x$：两个当前值分别为 $f_\ell(x),f_m(x)$。尾必须能接在两标签之后；因 $A_1\subset A_0$，两 outgoing guards 的共同地址域恰是 $A_s$，其标量域为较严格的 $I_s$。不能为两侧分别选择两个尾标量。

原映射斜率为负，故精确的闭区间公式是

$$
\boxed{
\mathcal I_{\ell,m}^{c,d}
=I_s\cap
\left[
\max\left\{\frac{\Delta_\ell-U_c}{g},
                 \frac{\Delta_m-U_d}{g}\right\},
\min\left\{\frac{\Delta_\ell-L_c}{g},
                 \frac{\Delta_m-L_d}{g}\right\}
\right].}
\tag{46.15}
$$

左端大于右端时为空，相等时保留单点。式中不附加碰撞发生处在 $S$ 中的 incoming guard 限制；所有标签均可从 guard 零前接。这样可能添加无法从某个原顶点出发的候选，却不会漏掉原路径的最后不同标签碰撞。共同尾的 outgoing guard 限制及(46.11)中的未来合法 guard 均未放宽。实际不相干返回必产生候选的论证因此仍成立。

**引理46.4.1（原同色严格宽度排除）。** 当 $c=d$ 时，$\mathcal I_{\ell,m}^{c,c}=\varnothing$，对全部实际 $\Omega$ 尾和闭端点成立。

**证明。** 置 $\delta=\lambda-b>0$。由(46.5)—(46.7)，一个共同闭颜色能包含的不同当前标签，仅有下表中的可能对；端格在亚临界预算下已不能同时遇到这两个根域，保留其行只放宽必要条件。

| 共同闭颜色 | 可能不同标签 | 平移差的绝对值 | 原扩张格宽 |
| --- | --- | --- | --- |
| $0$ | $3,0$ | $t$ | $t-\delta$ |
| $1$ | $3,0$ | $t$ | $t-2\delta$ |
| $2$ | $0,5$ | $t^2$ | $t^2-2\delta$ |
| $3$ | $5,2$ | $t$ | $t-2\delta$ |
| $4$ | $2,25$ | $t^2$ | $t^2-2\delta$ |
| $5$ | $2,25$ | $t^2$ | $t^2-\delta$ |

例如 $E_1^b=[-t^2-2\lambda+\delta,g-2\lambda-\delta]$，$E_2^b=[g-4\lambda+\delta,t-4\lambda-\delta]$；其余格同理由原切点算出。与五个完整根域比较即给表中标签对，缩小预算不会添加标签。若 $x\in\mathcal I_{\ell,m}^{c,c}$，状态相对满像给 $x$ 的一条 $A_s$ 地址，前接两标签都合法；两当前值相差 $\Delta_\ell-\Delta_m$，而表中每个共同格的宽度都严格小于该差的绝对值，矛盾。证明无需有限尾实现。$\square$

所以只需检验双色相位中的 $c\ne d$ 条目。同一个竞争相位并不保证两条路径选择同一个共同颜色，不能直接跨颜色使用此宽度表。

### 46.5 有限未来分离推出第一来源返回相干

**定理46.5.1（原预算的有限未来碰撞分离充分判据）。** 保持46.2的实际原全包含 SCC、第二单点、本原相位与原预算。若存在有限整数 $N\ge0$，使每个相位 $r$、每对不同标签 $\ell,m$ 及每对不同颜色 $c,d\in\mathcal C_r$ 均满足

$$
\boxed{
\mathcal I_{\ell,m}^{c,d}
\cap H_{r+1,\max\{o(\ell),o(m)\}}^{(N)}
=\varnothing,}
\tag{46.16}
$$

则 $S$ 的第一来源返回相干。特别地，若每个相位只有一种颜色，结论直接由原同色宽度排除得到。

**证明。** 反设第一来源不相干。依同步返回的定义，存在同一基点 $q$ 的两个非空返回；重复到共同正长度 $L$ 后，第一来源词 $U_0,U_1$ 不同。引理36.29也可供应这样的返回证书，但此处不需要其长度上界。第二相位使这两条返回的第二词相同，均是从 $\vartheta(q)$ 出发的周期词整幂，且 $p\mid L$。这不要求任何原返回长度恰为 $p$，也不限制其倍数的奇偶。

先固定一条 $q$ 的非空返回 $R$，第一、第二词记为 $A,B$。设基点两片为 $P_q^{(1)},P_q^{(2)}$。全包含关系给

$$
f_A(P_q^{(1)})\subseteq P_q^{(1)},\qquad
f_B(P_q^{(2)})\subseteq P_q^{(2)}.
\tag{46.17}
$$

两个收缩前接映射的固定点均在各自片中：从片内任一点反复前接，所有迭代留在闭片且收敛到固定点。因 $R$ 是合法返回，字面周期尾

$$
\tau=A^\infty,\qquad \eta=B^\infty
\tag{46.18}
$$

分别从基点两个 guard 合法，编码上述固定点，无须最终空尾。将这**同一对实际周期终尾**接到两个同步返回之后。有限提升保证每个出发坐标都在该路径的原片中；终端之后则沿同一条 $R$ 无限重复。每次重复的出发坐标仍有原共同闭色，第二坐标仍为相应 $y_r$。终端本来未观察，此处的无限延续单独由 $R$ 的合法性与全包含给出。

比较得到的实际第一地址 $U_0\tau,U_1\tau$。令 $j<L$ 为它们最后一个不同标签位置，标签为 $\ell\ne m$。从 $j+1$ 起，两条第一地址是同一个字面后缀 $\zeta$，包含相同的有限后段及固定周期尾 $\tau$。令 $x=\kappa_0(\zeta)$，$r=\vartheta(q)+j$。因 $\zeta$ 从两条路径的 outgoing guards 都合法，$\zeta\in A_s$，其中 $s=\max\{o(\ell),o(m)\}$。

在位置 $j$，两条原配对路径分别选某个共同闭色 $c,d$。第二坐标同为 $y_r$，所以 $c,d\in\mathcal C_r$，而第一坐标满足

$$
f_\ell(x)\in E_c^b,\qquad f_m(x)\in E_d^b,
\qquad x\in\mathcal I_{\ell,m}^{c,d}.
\tag{46.19}
$$

若 $c=d$，引理46.4.1已给矛盾。若 $c\ne d$，后缀 $\zeta$ 的每个出发坐标，先沿共同标签后段、再沿固定 $R$，都属于相应 $K_{r+1+h}$。于是同一条 $\zeta$ 对每个有限 $n$ 都证明

$$
x\in H_{r+1,s}^{(n)}\qquad(n\ge0).
\tag{46.20}
$$

特别地取 $n=N$，与(46.16)矛盾。故第一来源的所有同步返回词相同。相位刻画亦可对第一来源应用，得到其返回相干。$\square$

证明实际上定位了不相干返回必有的障碍：至少一个跨色碰撞条目具有一条同一实际无限尾，在每一层 $H^{(n)}$ 中存活。其关键是固定终尾后的最后不同标签，而不是路径数、不同颜色史或独立的逐边可行性。

### 46.6 固定标量的紧致性与固定数据的共同深度

**命题46.6.1（持续碰撞的实际尾与有限条目同深度）。** 固定一个实际周期来源的相位数据及一个实预算 $0\le b<\lambda$；此命题不要求由某个 SCC 供应这些数据。对某个条目 $e=(r,\ell,m,c,d)$，令 $s=\max\{o(\ell),o(m)\}$。以下等价：

1. 每个 $N\ge0$ 都有 $\mathcal I_{\ell,m}^{c,d}\cap H_{r+1,s}^{(N)}\ne\varnothing$。
2. 存在一个固定标量 $x\in\mathcal I_{\ell,m}^{c,d}$ 及一条固定实际尾 $\zeta\in A_s$，满足 $\kappa_s(\zeta)=x$，且其所有出发坐标均属于相应 $K_{r+1+h}$。

对这组固定数据的全部跨色条目，逐条最终为空，等价于存在同一个有限 $N$ 使(46.16)全部成立；也等价于不存在上述持续碰撞。

**证明。** 若第一项成立，闭紧集

$$
B_N=\mathcal I_{\ell,m}^{c,d}\cap H_{r+1,s}^{(N)}
$$

非空且递减。先由紧致性选一个固定 $x\in\bigcap_N B_N$。再在紧地址空间 $A_s$ 中定义

$$
\mathscr A_N(x)=\left\{\zeta\in A_s:
\kappa_s(\zeta)=x,\quad
\kappa_0(T^h\zeta)\in K_{r+1+h}\ (0\le h<N)\right\}.
\tag{46.21}
$$

地址域 $A_s$ 在有限字母的乘积空间中由禁字 $11$ 及 guard 的初位条件定义，是闭的，故紧。级数编码和移位连续，所有 $K$ 闭，故这些地址集闭紧；引理46.3.1使其非空，且它们递减。其交中的一条地址就是所需同一尾。这里先固定标量，再取嵌套地址交，未将不同深度、不同编码或不同坐标的边际选择拼接。第二项显然推出第一项。

若某条目的持续交为空，而各有限层都非空，刚才的紧致性便给持续尾，矛盾。所以该条目在某个有限 $N_e$ 已空。固定 $p$、原预算和相位后，标签、颜色、相位的条目数有限；取这些 $N_e$ 的最大值，并用(46.12)，即可得到共同深度。无条目时取 $N=0$。反向及与无持续碰撞的等价关系直接成立。$\square$

持续尾可在 guard 零分别前接 $\ell,m$，其当前闭色分别为 $c,d$；以后与同一实际周期竞争来源逐相位满足共同闭颜色关系。此处说的是闭关系，未把端点自动实际化。即使持续尾存在，它也没有给出原图中同一基点上的可达闭返回；包络允许的地址未必能承担指定 SCC 的返回串接。因此本章没有建立(46.16)对第一相干性的必要性，也没有建立持续碰撞与第一不相干 SCC 的等价性。尤其不能在尚未构造真实实例时，宣称已证明该充分判据严格非必要。

共同深度的量词仅针对固定数据。有限条目取最大值不提供跨周期、跨预算的一致深度。

### 46.7 同一个五周期实例：深度一存活，整个条目在深度二消失

令

$$
W=(0,3,3,5,0),\qquad \eta=W^\infty.
\tag{46.22}
$$

其 guard 链是 $(0,0,0,0,1,0)$，从零合法返回零，任意重复都合法。长度五为素数且词不恒定，故字面来源本原周期恰为五。记同一实际地址的相位坐标为 $y_r$。由

$$
f_{033}(z)=2g^2-g^3z,\qquad f_{50}(z)=t^2+g^2z
$$

及周期闭合可得

$$
y_0=\frac{2g^2-g^3t^2}{1+g^5},\qquad
y_1=-y_0/g,\qquad
y_2=-t-gt^2-g^3y_0.
\tag{46.23}
$$

这些坐标不是独立选择的点。由 $g$ 是 $z^2+4z-1$ 的正根，在正轴上比较得

$$
\frac4{17}<g<\frac14,\qquad \frac35<t<\frac58.
\tag{46.24}
$$

**命题46.7.1（严格的两色历史见证）。** 在

$$
b_*=99\lambda/100,\qquad \delta_*=\lambda/100
\tag{46.25}
$$

下，固定任意一条标量为 $x=-3/4$ 的实际尾 $\tau\in A_0$，两条来源 $3\tau,0\tau$ 分别能与同一 $\eta$ 严格共同取得

$$
(3\tau,\eta):\ (1,0),\qquad
(0\tau,\eta):\ (2,0).
\tag{46.26}
$$

对每一种固定合法端点归属，所需误差均可严格小于 $b_*$，目标均可选在实际格内部。因此

$$
-\frac34\in\mathcal I_{3,0}^{1,2}\cap H_{1,0}^{(1)}.
\tag{46.27}
$$

**证明。** 先核对 rival 的原颜色。由 $g>4/17>15/64$、$t^2<1/2$ 及 $1+g^5<1025/1024$，

$$
y_0=\frac{g^2(2-gt^2)}{1+g^5}
>\frac{(15/64)^2(2-1/8)}{1025/1024}
=\frac{3375}{32800}>\frac{13}{128},\qquad
3375\cdot128=432000>426400=13\cdot32800.
$$

上界为 $y_0<2g^2<1/8$，故

$$
\frac{13}{128}<y_0<\frac18.
\tag{46.28}
$$

相位零的原相邻闭扩张交为

$$
E_1^{b_*}\cap E_2^{b_*}
=\left[\frac{6g-1}{5}+\delta_*,
        \frac{11g-1}{10}-\delta_*\right].
$$

因 $\delta_*<1/2000$，(46.24)与(46.28)给完整的严格比较

$$
\frac{6g-1}{5}+\delta_*
<\frac{201}{2000}<\frac{13}{128}<y_0<\frac18
<\frac{27}{170}-\frac1{2000}
<\frac{11g-1}{10}-\delta_*.
\tag{46.29}
$$

所以 $\mathcal C_0=\{1,2\}$，$y_0$ 到两个原闭格的距离都严格小于 $b_*$。另一方面，$t^2=(1-g)/2<13/34$，故

$$
-1<-\frac{17}{32}<y_1<-\frac{13}{32}
<-t^2-\delta_*.
\tag{46.30}
$$

其中最后一步用 $13/34+1/2000<13/32$。这使 $y_1$ 严格位于 $E_0^{b_*}$ 的两端之间，从而到 $J_0$ 的距离严格小于 $b_*$。

状态零满像提供 $\tau$；标签 $3,0$ 均合法，且均输出 guard 零，故同一条 $\tau$ 可接在两侧。两当前值为

$$
f_3(-3/4)=-\frac12+\frac g4,\qquad
f_0(-3/4)=\frac{3g}{4}.
$$

第一个值在 $q_1$ 左侧，其到 $J_1$ 的距离是

$$
q_1-f_3(-3/4)=\frac{6g-1}{20}
<\frac{99(1-g)}{2000}=b_*.
\tag{46.31}
$$

严格不等式等价于 $699g<199$，由 $g<1/4$ 成立。第二个值严格位于 $J_2$ 内，因为

$$
\frac{3g}{4}-q_2=\frac{3-8g}{20}>0,\qquad
q_3-\frac{3g}{4}=\frac14>0.
\tag{46.32}
$$

共同下一坐标 $-3/4$ 严格位于 $J_0$ 内，因为 $-1<-3/4<q_1$，而 $q_1>-11/20$。结合(46.29)—(46.32)，在每个所需颜色中将目标选在格内部，就得到(46.26)的两个实际记录；各记录始终使用同一个 $Q$，竞争来源均为同一条 $\eta$，仅允许两条记录各选自己的误差。有限个目标误差的最大值严格小于 $b_*$，所以两段历史合用一个正余量；之后可各接零误差未来。共同尾 $\tau$ 则一次固定，没有为不同位置换来源。

两个出发颜色之后的坐标未观察。(46.31)—(46.32)给碰撞区间成员关系，$-3/4\in K_1$ 和实际尾语义给 $H_{1,0}^{(1)}$ 成员关系，证明(46.27)。$\square$

这两条颜色历史不同，原同色宽度不能将它们排除。此见证没有构造共同基点返回或全包含 SCC。

**命题46.7.2（所有实数亚临界预算下的整个条目深度二排除）。** 保持同一个实际 $W^\infty$，对每个实数 $0\le b<\lambda$，由该原预算定义(46.10)—(46.15)，都有

$$
\boxed{\mathcal C_2=\{0\},\qquad
\mathcal I_{3,0}^{1,2}\cap H_{1,0}^{(2)}=\varnothing.}
\tag{46.33}
$$

若相位零未同时允许颜色1、2，该区间不是待检条目；排除式本身仍成立。交换两标签及两颜色后结论相同。

**证明。** 置 $\delta=\lambda-b>0$。由(46.23)—(46.24)、$t^2<1/2$ 及 $0<y_0<1/8$，

$$
-1<-\frac{385}{512}<y_2<-t.
\tag{46.34}
$$

这里 $t+gt^2+g^3y_0<5/8+1/8+1/512=385/512$。原格0的右端为 $q_1=-11t^2/10$，且

$$
q_1+t=\frac{21t-11}{10}>0.
$$

所以 $y_2\in\operatorname{int}J_0$，在每个非负预算下都允许颜色0。颜色1在临界闭扩张的左端为 $-6t^2/5$，而

$$
t-6t^2/5=\frac{11t-6}{5}>0.
$$

因此 $y_2<-t<-6t^2/5$，不属于 $E_1^\lambda$ 或更高颜色的扩张；缩到原预算也不属于它们。这证明 $\mathcal C_2=\{0\}$，并给

$$
K_2=E_0^b=[-1,-t^2-\delta]\subset(-\infty,0).
\tag{46.35}
$$

现在任取 $x\in\mathcal I_{3,0}^{1,2}$。仅其第一项颜色条件 $f_3(x)\in E_1^b$ 就迫使

$$
-t-gx\ge-6t^2/5+\delta.
$$

令 $s_*=-1+\phi/5=(g-7)/10$。恒等式

$$
\frac{6t^2/5-t}{g}=s_*,\qquad
s_*+t^2=-\frac{1+2g}{5}<0
$$

给

$$
x\le s_*-\delta/g<-t^2.
\tag{46.36}
$$

由完整根域(46.5)，guard 零下严格低于 $-t^2$ 的坐标只能由标签3编码。因此每一条编码 $x$ 的实际地址都以3开头，下一 guard 仍为零，其下一坐标唯一等于

$$
x^+=\frac{-t-x}{g}
\ge\frac{-t-s_*}{g}+\frac{\delta}{g^2}
=\frac{2t}{5}+\frac{\delta}{g^2}>0.
\tag{46.37}
$$

若同时 $x\in H_{1,0}^{(2)}$，引理46.3.1给同一实际尾，其下一坐标必须属于相位二的 $K_2$，与(46.35)—(46.37)矛盾。该证明覆盖整个碰撞区间，只用其中一个颜色下界；包括 $x=-1$ 或只有非有限 $\Omega$ 地址的点，均不删除端点。$\square$

对旧见证 $x=-3/4$，还可直接看到每条实际 $\tau$ 的首标签都为3，且

$$
\kappa_0(T\tau)=\frac{3/4-t}{g}>\frac12,
$$

其中用 $t<5/8$、$g<1/4$。竞争方该相位只允许负的 $K_2$，所以两条历史都不能再取得第三个共同颜色。深度一的真实见证是暂态的：它在 $N=1$ 存活，在 $N=2$ 失败。这里排除的是(46.33)的整个条目，没有声称这个 rival 的全部条目均通过深度二，也没有将它当作 SCC 反例或严格非必要性实例。

### 46.8 实际本原奇周期中的双色相位数无界

逐相位至多两色并不意味着双色相位总数有统一上界。以下短构造仍使用实际地址和原预算 $b_*$，不供应任何 SCC 单点片实现。

**命题46.8.1。** 对偶数 $k\ge2$，令

$$
V_k=W^k0,\qquad \eta_k=V_k^\infty.
\tag{46.38}
$$

这些是实际合法的本原奇周期来源；其原预算 $b_*$ 下的双色相位数随 $k$ 无界。

**证明。** $W$ 从 guard 零合法返回零，再添一个 $0$ 仍从零返回零，故 $V_k$ 的任意重复均合法。若 $V_k=B^d$ 为 $d$ 次整幂，则窗口5的出现次数 $k$ 被 $d$ 整除，词长 $5k+1$ 也被 $d$ 整除。于是 $d\mid k$ 且 $d\mid5k+1$，只能 $d=1$。因此字面本原周期就是 $5k+1$，偶数 $k$ 使其为奇数。

由(46.29)，存在 $\varepsilon>0$，使 $[y_0-\varepsilon,y_0+\varepsilon]$ 严格位于 $E_1^{b_*}\cap E_2^{b_*}$ 内。选择一个固定整数 $m_0\ge1$，使

$$
\operatorname{diam}(X)g^{5m_0}=\phi^2g^{5m_0}<\varepsilon.
$$

从 $\eta_k$ 的相位 $5j$ 出发，其中 $0\le j\le k-m_0$，其字面尾与 $W^\infty$ 至少共享 $k-j\ge m_0$ 个完整 $W$ 块。两条地址共享长度 $5(k-j)$ 的合法前缀，前缀后的尾坐标都在 $X$ 中；同一仿射前接的收缩给

$$
\left|\kappa_0(T^{5j}\eta_k)-y_0\right|
\le\phi^2g^{5(k-j)}<\varepsilon.
\tag{46.39}
$$

故这 $k-m_0+1$ 个不同相位都严格允许颜色1、2。46.2的逐相位排除又保证没有第三种颜色。令偶数 $k\to\infty$，数量无界。这里的严格重叠也可按46.1在每种固定归属下实际取得；整个证明均来自合法地址的共同前缀，未使用人为提供的单点图切片。$\square$

### 46.9 可复用接口与未解决的义务

可复用的桥接内容是(46.14)—(46.16)：共同尾保留较严格的 outgoing guard、原相位闭颜色包络，以及沿同一实际地址的有限未来成员关系。全包含返回提供一对固定实际周期终尾，最后不同标签把第一不相干性送到持续碰撞；固定标量的地址紧致性再把无持续碰撞转成固定数据的有限分离。五周期实例证明多保留一层未来确实排除了整个局部碰撞类，因此这个充分判据及配套实例值得作为一个独立接口保留。

一般奇周期路线仍须证明：每个实际奇周期竞争来源的相关条目最终都分离，或者补入足以排除最后不同标签碰撞的原 SCC 限制。本章没有证明这项义务。持续相位包络碰撞也不自动提供原共同基点可达性、两条可同步返回或其合法串接；这些返回条件仍须在实际原图中成立。相干性对本判据的必要性、以及持续碰撞与 SCC 不相干性的等价性均未建立。

有限区间并的递推及固定条目的共同深度，不给出区间分量数、实际所需深度或原图构造代价的统一界；引理36.29的返回界依赖一个固定 SCC 的顶点数，不能转成跨周期或跨预算的统一未来深度。

## 46.99 追加锚
## 47. 原完整图上的碰撞入口、有限相位边界与实际套索尾

固定一个合格的次临界预算、已经给出的原完整端点图，以及已经属于该图的实际单点 rival。本章把一个不同头、共同字面未来的碰撞条目，精确地归约为原图相位展开中的到环问题；到环时由一条实际最终周期来源作见证，不到环时由一个有限观察深度排除。共同返回另由同一 SCC 内的来源词相干性刻画。这里的有限图到环论证是经典复用；所需接口是原端点、全部 guard、整片颜色包含与同一实际来源之间的精确对应。

来源及图合同直接采用本卷定义14.5、命题14.6、定理14.7、17.2、引理31.2、定义31.3及定理31.4；共同尾严格宽度、来源返回相干性及有限返回测试分别采用引理36.16、定理36.22和引理36.29，标准分歧入口采用定理36.23，分歧后的正分隔采用41.6。上述已发表前提见[本卷固定修订](https://github.com/the-omega-institute/trureturing/blob/cfe06a9af05aff5b3d2ffa4d478cea124842a1a3/docs/develop/theory/FIB_SOURCE_COMPLETION_DYNAMICS.md)。奇数周期部分只使用引理45.7证明中的端点排除，不使用五周期分类。

### 定义 47.1（固定原图、原单点轨道与碰撞合同）

置

$$
t=\frac{\sqrt5-1}{2},\qquad \phi=1+t,\qquad
g=t^3=2t-1,\qquad \lambda=\frac{t^2}{10},
$$
$$
\beta\in\mathbb Q(t)\cap[0,\lambda),\qquad
\delta=\lambda-\beta>0,\qquad
I_0=X=[-1,\phi],\quad I_1=[-1,t].
$$

$A_0=\Omega$、$A_1\subset A_0$ 是原实际地址域，$\kappa_s(A_s)=I_s$；$T$ 删除一个三位窗口。来源标签集为 $\Lambda=\{3,0,5,2,25\}$，其中 $0$ 是空窗，$25$ 是一个标签。合法 guard 边与仿射分支为

$$
0\to0:3,0,2;\quad 0\to1:5,25;\quad
1\to0:3,0;\quad 1\to1:5,
$$
$$
f_a(x)=\Delta_a-gx,\quad F_a(x)=\frac{\Delta_a-x}{g},\quad
(\Delta_3,\Delta_0,\Delta_5,\Delta_2,\Delta_{25})
=(-t,0,t^2,1,2-t).
\tag{47.1}
$$

记 $o(3)=o(0)=o(2)=0$、$o(5)=o(25)=1$。标签 $a$ 的 outgoing guard 始终是 $o(a)$。根像按空间次序为

$$
3:[-1,-t^2],\quad 0:[-t^2,g],\quad
5:[g,t],\quad 2:[t,2t],\quad25:[2t,\phi].
$$

六色切点是

$$
q_1=-t^2-\lambda,\quad q_2=g-3\lambda,\quad
q_3=t-5\lambda,\quad q_4=2t-7\lambda,\quad
q_5=2t+\lambda.
$$

令 $q_0=-1,q_6=\phi$，$J_c=[q_c,q_{c+1}]$，并只使用原预算闭扩张

$$
E_c=E_c^\beta=X\cap(J_c+[-\beta,\beta])=[L_c,U_c],
\qquad 0\le c\le5.
\tag{47.2}
$$

这些集合表示闭成员关系。关于固定切点归属的实际含噪颜色取得，仍须另核对目标和误差；闭成员关系本身不供应严格误差余量。

输入图 $G$ 是定义31.3的**原完整图**。其既有公共有限端点集 $B$ 包含 (47.2) 的有效端点、guard 端点及全部合法分支域端点，并满足

$$
z\in B,\quad F_a(z)\in X\quad\Longrightarrow\quad F_a(z)\in B.
\tag{47.3}
$$

令 $B_s=B\cap I_s$。原节点恰为 $(s,P)$，其中 $P$ 是 $B_s$ 中的一个端点单点，或两个相邻端点间的整个闭片；全部这些片均保留。原边恰为

$$
(s,P)\xrightarrow{a}(s',Q)
\quad\Longleftrightarrow\quad
s\xrightarrow{a}s'\text{ 合法},\quad
P\subseteq f_a(I_{s'}),\quad Q\subseteq F_a(P).
\tag{47.4}
$$

同一标量片在两个 guard 中出现时是两个节点。以下不改变 $B$，不插入碰撞端点或 rival 点，不以区间相交替代 (47.4)。

同时给定一条实际本原周期 rival，窗口词为 $V=v_0\cdots v_{p-1}$，其相位坐标、周期 guards 为 $y_r,u_r$，指标模 $p$。要求

$$
y_r=f_{v_r}(y_{r+1}),\qquad
(u_r,\{y_r\})\xrightarrow{v_r}(u_{r+1},\{y_{r+1}\})
\text{ 已是 }G\text{ 的原边}.
\tag{47.5}
$$

任意实际周期地址不自动满足这个原单点成员假设。若输入来自原配对图的一个含环 SCC，且第二来源有单点，则交换分量使用命题39.6.1，第二片在整个 SCC 都是单点且第二来源返回相干。定理36.22给其本原词和边相位；通过各顶点的返回是对应旋转词的整幂，收缩固定点唯一，故同相位单点都等于 $y_r$。内部前驱标签又决定 $u_r=o(v_{r-1})$。沿一条返回取出各相位即得到 (47.5)，保持原节点身份。

记

$$
\mathcal C_r=\{c:y_r\in E_c\},\qquad
K_r=\bigcup_{c\in\mathcal C_r}E_c,
$$
$$
H_{r,s}^{(0)}=I_s,\qquad
H_{r,s}^{(N+1)}=K_r\cap
\bigcup_{s\xrightarrow{a}s'\,\mathrm{合法}}
f_a\bigl(H_{r+1,s'}^{(N)}\bigr).
\tag{47.6}
$$

对 $a=(r,\ell,m,c,d)$，其中 $\ell\ne m$、$c,d\in\mathcal C_r$，定义

$$
s_a=\max\{o(\ell),o(m)\},\qquad
\mathcal I_a=I_{s_a}\cap F_\ell(E_c)\cap F_m(E_d).
\tag{47.7}
$$

因为 $A_1\subset A_0$，同一个字面尾可接在两个头后面，当且仅当它从较严格 guard $s_a$ 合法。区间 (47.7) 的两个逆像分别是

$$
F_\ell(E_c)=\left[\frac{\Delta_\ell-U_c}{g},
\frac{\Delta_\ell-L_c}{g}\right],\qquad
F_m(E_d)=\left[\frac{\Delta_m-U_d}{g},
\frac{\Delta_m-L_d}{g}\right].
$$

取三者下端最大值和上端最小值；下端大于上端时为空，等号时保留单点。引理36.16的严格宽度排除 $c=d$ 的条目，详见47.4；以下待检条目因此取 $c\ne d$。

定义相位图 $\mathcal P$：其顶点是

$$
(r,s,P),\quad (s,P)\in V(G),\quad
P\subseteq E_c\text{ 对某个 }c\in\mathcal C_r;
\tag{47.8}
$$

边 $(r,s,P)\xrightarrow{a}(r+1,s',Q)$ 恰取自 (47.4)。这是固定 rival 轨道的原配对图相位展开；颜色条件是整片包含。每个顶点可有多个容许共同色，各次访问可选择其中一个。令

$$
M=|V(\mathcal P)|\le p|V(G)|,\qquad
\mathcal J_a=\{(r+1,s_a,P)\in V(\mathcal P):P\subseteq\mathcal I_a\}.
\tag{47.9}
$$

### 引理 47.2（原规范片及有限观察的精确仿射像）

每个非空 $\mathcal I_a$ 是原 $s_a$-片的并。对其任一点 $x$，原规范片 $P_{s_a}(x)$ 整个包含于 $\mathcal I_a$；若 $x$ 同时属于若干所选闭色，则同一规范片同时包含于这些闭色。

对 $N\ge1$，令 $\Gamma_{a,N}$ 为从 $\mathcal J_a$ 出发、具有 $N$ 个顶点的 $\mathcal P$ 路径。写一条路径为

$$
\pi=((r+1+j,s_j,P_j))_{0\le j<N},\qquad
P_j\xrightarrow{a_j}P_{j+1}\quad(0\le j<N-1).
$$

以 $f_w=f_{a_0}\circ\cdots\circ f_{a_{N-2}}$，空词时取恒等映射，则有集合等式

$$
\boxed{\displaystyle
\mathcal I_a\cap H_{r+1,s_a}^{(N)}
=\bigcup_{\pi\in\Gamma_{a,N}} f_w(P_{N-1}).}
\tag{47.10}
$$

**证明。** 非空 $\mathcal I_a$ 的有效端点是 $I_{s_a}$ 的端点，或是某个原颜色端点 $z$ 的 $F_\ell(z)$、$F_m(z)$，且该逆像落在 $I_{s_a}\subset X$。由 (47.3) 它已在 $B_{s_a}$ 中。定理31.4使用的规范片是：$x\in B_s$ 时取 $\{x\}$，否则取内部含 $x$ 的唯一相邻端点闭片。一个端点在 $B_s$ 中、包含 $x$ 的闭区间必包含此片。因此 $P_{s_a}(x)\subseteq\mathcal I_a$；它们覆盖该区间。所选 $E_c\cap I_s$ 的有效端点也在 $B_s$，故同一论证同时保留全部满足的颜色约束。

先说明 (47.6) 的准确语义：$x\in H_{r,s}^{(N)}$ 当且仅当存在**一条** $\tau\in A_s$，其初始标量为 $x$，且

$$
\kappa_0(T^j\tau)\in K_{r+j}\qquad(0\le j<N).
\tag{47.11}
$$

零层由状态相对满像成立。递推时选一条合法首边及后继集合所供应的同一实际尾，合法前接得到整个来源；反向则剥离该实际首边。归纳还给出各 $H^{(N)}$ 为紧集且递减。递推有 $N$ 个来源标签，位置 $N$ 的坐标未观察。

取左侧的点及 (47.11) 的实际地址。其各时刻的规范片保留实际 guard、分支域、全部所选共同色，并由定理31.4形成原全包含边。首片包含于 $\mathcal I_a$，故前 $N$ 个观察顶点给出 $\Gamma_{a,N}$ 中的路径；实际终点 $x_{N-1}\in P_{N-1}$ 给 $x=f_w(x_{N-1})$。

反向，取右侧的一条路径和任意 $z\in P_{N-1}$。状态相对满像给从 $s_{N-1}$ 出发编码 $z$ 的一条实际尾。用同一个终点和同一条终尾沿 $N-1$ 条全包含边前接，得到初始标量 $f_w(z)$。所有 $N$ 个显示坐标落在各自的整片及所选共同色内，首点在 $\mathcal I_a$ 中。终尾的下一坐标属于其实际 guard 区间，但不另受观察约束，故 (47.11) 成立。第二分量始终取给定 rival 的同一个字面旋转尾，所以全部颜色关系由同一对实际地址同时实现。这里没有逐边另选来源。$\square$

当 $N=1$，(47.10) 就是 $\mathcal I_a\cap K_{r+1}\cap I_{s_a}=\bigcup_{(r+1,s_a,P)\in\mathcal J_a}P$，不显示任何边。当 $N=0$，交集是 $\mathcal I_a$，不施加相位颜色条件；不能以空路径误将它改为 $\bigcup\mathcal J_a$。空入口集使所有 $N\ge1$ 的右侧为空；空图采用相同空并约定。

### 定理 47.3（固定原图的有限碰撞—实际套索边界）

在47.1的全部固定输入下，对每个碰撞条目 $a$，以下五项等价：

1. 每个 $N\ge0$ 都有 $\mathcal I_a\cap H_{r+1,s_a}^{(N)}\ne\varnothing$。
2. $\mathcal I_a\cap H_{r+1,s_a}^{(M+1)}\ne\varnothing$。
3. $\mathcal J_a$ 在 $\mathcal P$ 中可达一个有向环。
4. 存在一条同一实际尾 $\tau\in A_{s_a}$，初始标量在 $\mathcal I_a$ 中，且每个 $j\ge0$ 都有 $\kappa_0(T^j\tau)\in K_{r+1+j}$。
5. 第4项可由同一字面尾 $\tau=A R^\infty$ 实现，且可取

$$
0\le |A|\le M-1,\qquad 1\le |R|\le M,\qquad
|A|+|R|\le M,\qquad p\mid |R|.
\tag{47.12}
$$

第五项的长度断言在存在见证时使用，因而此时 $M\ge1$。前接 $\ell,m$ 给两条不同实际地址 $\ell\tau,m\tau$；它们与同一 rival 的当前闭色分别为 $c,d$，以后的闭颜色词可完全相同。它们的共同未来是同一个字面 $\tau$，而非仅仅两个相等标量。

**证明。** 第1项蕴含第2项。由 (47.10)，第2项供应从 $\mathcal J_a$ 出发、含 $M+1$ 个观察顶点和 $M$ 条显示边的路径。有限图中的重复顶点给可达有向环，即第3项。

从可达环中取一个简单有向环，再取入口到该环的最短路径，以首次遇到该环的位置结束。前段不重复顶点，且除终点外与环不交。若前段长为 $h_A$、环长为 $h$，这些不同顶点共 $h_A+h$ 个，故 $h_A+h\le M$。令第一来源标签词为 $A,R$。相位随每边增加一，环闭合使 $p\mid h$。这证明 (47.12)；其和界来自这个简单套索选择，不能由任意到环路径分别具有的两个界相加获得。

设入环片为 $P_*$，并写

$$
f_R(z)=D_R+(-g)^h z,\qquad
D_R=\sum_{j=0}^{h-1}(-g)^j\Delta_{R_j}.
$$

全包含边给 $f_R(P_*)\subseteq P_*$。从闭片中任一点迭代这个收缩，极限仍在 $P_*$，且是唯一固定点

$$
z_*=\frac{D_R}{1-(-g)^h}\in P_*,\qquad
x=f_A(z_*)\in P_0\subseteq\mathcal I_a.
\tag{47.13}
$$

原合法返回使 $R^\infty$ 是从入环 guard 出发的实际地址；其窗口级数正是 (47.13)。前接原路径 $A$，全部中间坐标由同一尾、同一固定点实现，并落在原全包含片内。环同时闭合 rival 相位，每次重复可选同一组整片容许色。因此 $A R^\infty\in A_{s_a}$ 给第5项。此证明保留单点片及全部端点，并供应一条来源，未把各有限层独立的见证拼接。

第5项蕴含第4项，第4项由 (47.11) 蕴含第1项。最后，$\tau\in A_{s_a}\subseteq A_{o(\ell)}\cap A_{o(m)}$，故两个头都能从 incoming guard 零合法前接；(47.7) 给各自当前闭色，(47.11) 给同一个未来闭颜色词。$\square$

还须核对这两个头使用的是**原全包含边**。对套索首片 $P_0$，取其一个规范代表点 $\xi$：非退化片取内部点，单点片取该点。由于两个 guard 端点都在公共 $B$ 中，$P_0$ 在 $o(\ell),o(m)$ 两种 guard 下均是同一标量规范片，只带各自类型。令 $P_\ell$ 是 $f_\ell(\xi)$ 的 guard 零规范片。它整个包含于 $E_c$ 及 $f_\ell(I_{o(\ell)})$；其逆像端点在 $B$ 中，规范片性质给

$$
P_0\subseteq F_\ell(P_\ell).
$$

故 $(0,P_\ell)\xrightarrow{\ell}(o(\ell),P_0)$ 是原边，且承载 $P_0$ 内的**所有**终尾点，包括 (47.13) 的新固定点。$m$ 同理。这不要求把 $f_\ell(P_0)$ 另加为基本片。

若 $o(\ell)\ne o(m)$，两个目标节点仍不同。$\tau$ 的首标签从较严格 guard 合法，也从较宽 guard 合法；该标签的根域和映射相同，其 outgoing guard 由标签唯一决定。因此两份 $P_0$ 沿同一个首标签到套索的同一个后继片后，才具有相同的带类型节点。无限套索有首标签，即使 $A$ 为空也可取 $R$ 的首标签，故此核对没有空首边例外。

**固定实例的有限排除。** 若 $\mathcal J_a$ 不可达环，则 $\mathcal I_a\cap H_{r+1,s_a}^{(M+1)}=\varnothing$；反之此有限交集非空已经供应 (47.13) 的实际套索。把全部碰撞入口并为 $\mathcal J$，全部条目存在共同有限排除深度，当且仅当 $\mathcal J$ 不可达环；成立时 $M+1$ 足够。无不同色条目时这是空条件。形式上 $M=0$ 时深度为1，所有入口为空；在 (47.5) 的非空实际输入中，rival 自身的相位轨道已经使 $\mathcal P$ 非空。

### 命题 47.4（正分隔、标准分歧入口及不可达的全等环）

对任何 $x\in\mathcal I_a$，有

$$
\boxed{|x-y_{r+1}|\ge\frac{2(\lambda-\beta)}{g}>0.}
\tag{47.14}
$$

任何实际双头持续见证都供应定理36.23的原完整闭分歧图 $\mathcal D_\beta$ 的初始入口。碰撞入口不能到达每条边第一标签均等于相位 rival 标签的有向环。

**证明。** 引理36.16的根域与闭宽度表在当前预算给出以下全部可能性：端色0、5分别只允许标签3、25；内色中可能不同的标签和平移差、闭格宽为

| 共同色 | 不同标签 | 平移差 $D$ | 原闭格宽 |
| --- | --- | --- | --- |
| 1 | $3,0$ | $t$ | $t-2\delta$ |
| 2 | $0,5$ | $t^2$ | $t^2-2\delta$ |
| 3 | $5,2$ | $t$ | $t-2\delta$ |
| 4 | $2,25$ | $t^2$ | $t^2-2\delta$ |

实际根域限制和 $\delta>0$ 排除了端色中的不同标签。这同时证明47.1所用的同色排除：共同尾 $x$ 前接 $\ell\ne m$ 时，当前差恰为 $\Delta_\ell-\Delta_m$，其绝对值大于同色宽度，故同色 $\mathcal I_a$ 为空。

两个碰撞头中至少一个 $a_*$ 不同于 $v_r$；取它的当前所选色 $e$，则 $f_{a_*}(x),y_r\in E_e$。两个值确属其原实际根域：$x\in I_{s_a}\subseteq I_{o(a_*)}$，而 rival 是 (47.5) 的实际地址。因此它们落在上述某一内色行，$D=|\Delta_{a_*}-\Delta_{v_r}|$，并有

$$
g|x-y_{r+1}|
=|\Delta_{a_*}-\Delta_{v_r}-(f_{a_*}(x)-y_r)|
\ge D-|f_{a_*}(x)-y_r|\ge2\delta.
$$

这就是41.6在本接口上的分隔式；它不要求下一坐标已观察，也不要求尾属于有限来源域。

现取任一实际持续见证。其 $a_*$-头可从 guard 零前接，rival 旋转的整个字面地址也可从 guard 零出发，因为 $A_{u_r}\subseteq A_0$。按定理31.4取这两条地址的原规范配对路径；头部具有共同闭色 $e$，后续各位置由持续见证选择一个共同闭色。初始对的两个 guard 都为零，**第一条边**就输出 $(a_*,v_r)$，两标签不同。故它立即跨过定理36.23规定的第一分歧边，全部后续配对延续均属于 $\mathcal D_\beta$。首次分歧前的相同标签段可以为空，不需另证初始可达性。

最后，若入口可达一个全等标签环，沿到环路径再无限重复该环，47.3的同源提升给一条尾，其标签最终等于对应的 rival 旋转尾。前接上述不同头后，与实际 rival 得到两条不同、最终同字面尾且逐位置具有共同闭色的地址。取它们最后不同标签的位置，共同下一尾使当前差等于表列平移差，严格宽度给矛盾。这是引理36.16及41.6的原排除机制。故每个可达环至少含一条不同标签边。$\square$

### 命题 47.5（端点排除下的严格侧别与必要奇偶条件）

另假设 rival 的各相位避开根接触点 $-t^2,g,t,2t$。则从碰撞入口可达的每个顶点 $(q,s,P)$ 都满足 $y_q\notin P$，所以整片严格位于 $y_q$ 的一侧。同标签边翻转侧别，不同标签边保持侧别。因此任一可达环上的同标签边数为偶数。若环长为 $kp$，不同标签边数 $d_R$ 必须满足

$$
d_R\ge1,\qquad d_R\equiv kp\pmod2.
\tag{47.15}
$$

当 $p$ 为奇数时，$d_R\equiv k\pmod2$；这里仍允许 $k$ 为偶数。

**证明。** 若 $y_q\in P\subseteq I_s$，对应 rival 的同一个字面旋转尾也从 $s$ 合法。$s=0$ 时直接用 $A_{u_q}\subseteq A_0$。$s=1$ 时，$y_q\in[-1,t]$ 且避开根接触点，rival 的当前根标签只能是3、0、5；它们都从 guard 一合法，下一 guard 和后续字面尾不变。

选择一条从某碰撞入口到此顶点的原路径，以该 rival 尾和标量 $y_q$ 为终尾作全包含提升。入口标量仍在 $\mathcal I_a$，每个显示顶点仍与对应 rival 相位有共同闭色。再前接不同于 $v_r$ 的碰撞头，得到不同而最终同字面尾的两条地址；在终尾以后二者完全相等，也有共同闭色。这与47.4使用的最后分歧严格宽度矛盾。因此 $y_q\notin P$；闭片是区间或单点，侧别为严格的常值。

考虑一条可达边 $(q,s,P)\xrightarrow{a}(q+1,s',Q)$，任选 $x'\in Q$，令 $x=f_a(x')\in P$。若 $a=v_q$，

$$
x-y_q=-g(x'-y_{q+1}),
$$

故侧别翻转。若 $a\ne v_q$，$P$ 的某个整片共同色也包含 $y_q$，原根域和47.4的内色表使这两个标签是相应相邻对。根像的空间顺序与 $\Delta_a-\Delta_{v_q}$ 的符号一致；rival 避开根接触点，故

$$
\operatorname{sgn}(x-y_q)=\operatorname{sgn}(\Delta_a-\Delta_{v_q}),\qquad
|x-y_q|\le|\Delta_a-\Delta_{v_q}|-2\delta.
$$

由

$$
x'-y_{q+1}=\frac{\Delta_a-\Delta_{v_q}-(x-y_q)}g
$$

可知下一差也具有该符号，故侧别保持。回到同一相位、同一片时侧别不变，因此同标签翻转次数为偶数；相位闭合给环长 $kp$，47.4又排除 $d_R=0$，即得 (47.15)。$\square$

引理45.7的端点证明对任意奇数周期排除了四个根接触点以及八个非根临界双色带端点：非根部分用 $\mathbb Z[t]/5\mathbb Z[t]$ 中 $1-(-g)^p$ 的单位性，根部分用命题14.6、定理14.7强制的非恒定二周期极值尾。故奇数 $p$ 可直接使用本命题；其有限相位五点覆盖断言不在这里使用。47.2—47.4不依赖奇数性或这个额外端点前提。(47.15) 仅是必要条件，没有排除满足该条件的非全等环。

### 命题 47.6（共同字面未来与同一 SCC 返回的准确接口）

固定原配对图的一个含环 SCC $S$，仍以第一来源标签为边输出。以下两项等价，作为定理36.22及引理36.29的直接复用：

1. $S$ 的第一来源返回不相干。
2. $S$ 内有两条内部边，其第一标签 $\ell\ne m$，各目标后面有一条始终留在 $S$ 内的无限路径，两个第一来源字面未来完全相同。

这里两条头边的源、目标可以是不同的带类型顶点；不将 outgoing guards 的不同抹去。在第二来源为 (47.5) 的单点相位时，第1项供应的第2项还可取为同一 rival 相位的两头，当前共同色必不同，并由**同一实际第一尾**及同一实际 rival 同时实现。

**证明。** 若第一来源返回相干，定理36.22给一个本原词 $W$ 和全部内部边的相位。两目标的无限未来分别是 $W^\infty$ 的两个相位旋转；字面相同使目标相位相同，否则会给 $W$ 更短周期。边相位每次加一，故两个源相位也相同，两个头标签必须相同，排除第2项。

若返回不相干，引理36.29给同基点两个非空返回，同步重复后第一词 $U_0,U_1$ 长度相同而不相等。取最后不同标签位置，之后至基点的第一标签后段完全相同。再接基点任一非空内部返回 $C$ 的无限重复，两头之后的无限第一标签词遂相同，全部路径留在 $S$ 内。

还要核对实际联合实现。$f_C$ 把基点第一闭片送入自身，故其唯一固定点在该片；以实际 $C^\infty$ 为同一第一终尾。在第二单点分量取该基点的实际 rival 旋转尾。对两条同步返回以及它们在最后不同标签之后的后段，使用这一对相同终尾作全包含提升。第一后段的字面标签和终尾都相同，因而给同一实际第一尾，即使两目标 guards 原来不同；两侧合法性由原路径供应。第二来源相干使同步路径的每个位置具有同一 rival 相位和单点坐标。因此两个头分别满足 (47.7)，且 $c=d$ 会违反47.4的同色排除，必有 $c\ne d$。这也供应该条目的实际持续见证。$\square$

对一个具体的47.3套索，两头后的路径先保留各自 outgoing guard，经过第一个共同标签后可合流，并到达某个含环 SCC $S_*$。要用**这两条头边**证成共同返回，须从 $S_*$ 回到两条头边的适当原带类型源顶点，并使它们及其到 $S_*$ 的路径都在同一 SCC。若尾路径已经从两头通向 $S_*$，从 $S_*$ 到两个头源的返回连接恰好使整个两头结构内部化；47.6于是给返回不相干。guard 零改根只供应47.4的标准初始入口，不能代替这些返回连接，也不能将返回时的带类型头重新命名。

有限共同返回检查直接使用引理36.29：若固定 $S$ 有 $s$ 个顶点，最短非空基准返回长至多 $s$，测试返回长至多 $2s-1$，以最小公倍数同步比较第一来源词。不同图路径、不同颜色历史或路径重数均不等于不同来源词。第二来源已有单点相干时，第一来源相干与有序来源对相干相互对应，因为第二来源的同步返回始终相同。

### 结论 47.7（固定实例的有限边界及剩余原几何义务）

对于本章固定的 $\beta,G,V$，每个原碰撞条目的持续性都有精确有限边界：入口不可达环时，至迟由 $M+1$ 个出发观察排除；可达环时，供应一条满足 (47.12)—(47.13) 的同一实际最终周期尾。标准36.23入口已由不同 guard 零头直接提供。所有可能可达环含来源分歧；在奇周期端点排除下还须满足严格侧别及 (47.15)。

若要排除一类尚未确定的原图碰撞，仍须证明该类的碰撞入口不能通向这些非全等环。若要把一个持续碰撞提升为第一来源返回不相干，仍须供应47.6要求的同一 SCC 内共同返回。前者是原几何可达性义务，后者是回到适当带类型双头的义务；已经存在的初始分歧入口不再是缺口。固定图上的这些问题由其有限边界和已有返回测试刻画，本章没有判定所有实例的可达性取值。

尤其，奇数本原周期不使每个返回长度为奇数，周期长度 $kp$ 的偶数倍仍须保留；必要奇偶条件不提供全奇周期排除。这里没有构造新的实际持续碰撞实例。图大小与周期共同决定 $M$，没有跨预算、跨周期的一致深度界，也不从这一接口推出全局半径或完整解码器结论。本文的时间是原窗口步及其相位，空间是原仿射坐标与闭成员关系；没有物理时空起源的推论。

### 注记 47.16（46.8 的相位计数范围）

在46.8中，(46.39) 后的 $k-m_0+1$ 个相位计数用于满足 $k\ge\max\{2,m_0\}$ 的偶数 $k$，其指标范围为 $0\le j\le k-m_0$。命题46.8.1对所有偶数 $k\ge2$ 的合法性与本原性结论，以及双色相位数无界的结论保持不变。

## 47.99 追加锚（本行以下为增补区）

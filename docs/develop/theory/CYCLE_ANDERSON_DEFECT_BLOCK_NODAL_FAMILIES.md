# 圈上 Anderson 模型的无对称坏势：单值演算、缺陷块族与合数长度

> **本卷的机器契约(逐条可查,落地后不改)。** 消化器 `generic-v1`;地址(locator)由
> `tools/StrataLint.Engine/Digestion/Atomizers/GenericAtomizer.cs` **仅从本文件的字节**算出,
> 不查任何词表。本卷**只增不减**:卷首恒定区与既有各章一经合入即**一字不改**,
> 全部修订、勘误、增补一律写在文末**追加锚**之后的新章里。旧章保留为历史记录;
> 勘误的形式是新章点名旧编号并给出改判,不是回去改旧字节(CLAUDE.md 第 1.2 条、第 4.2 条)。

## 1. 定位、状态与产地

**参考输入,不是真源。** 本卷是 trureturing 的参考输入:提供出处与灵感,不承担机器治理,Lean 形式化才是唯一真源。不得把任何形式化工件反向绑定到本卷的章节号或定理号上(CLAUDE.md 第 4.3 条)。

**证明状态。** 本卷给出 ZFC 内的普通数学散文与一个有限精确核验代码块(第 10 章)。本卷未经 Lean kernel 验证,不得称 kernel-verified;哪条已被形式化,以冻结账本为准,不以本卷自述为准(CLAUDE.md 第 2.4 条)。依赖第 10 章代码的命题在第 9 章「核验边界」中逐条列出。

**产地(CLAUDE.md 第 5.2 条三项)。**
①**skill 上下文**:`consensus-rnd:sshx`。
②**载体与分工**:本卷正文由实施席 Claude Code subagent(Opus 5.5,回退席位)产出;选题由六席思考面板(Opus 5.5 三席、Fable 5.1 三席)收敛,其中无穷族候选与小长度读数最初由面板席位给出,本席复算并写成证明;评审三席为 Claude Code subagent(Opus 与 Fable 混合)。实施席与评审席同属一个载体族,不冒充跨厂商多样性。
③**混合方式**:三席并发盲评;approve/reject/abstain 票数与分歧裁决在评审后由编排者写入拉取请求正文。
宿主会话 ID:`02860e2e-a1ec-4fd1-b72b-435e73e0a63d`,恢复命令 `claude --resume 02860e2e-a1ec-4fd1-b72b-435e73e0a63d`。

**读法。** 本卷按写作时序排列:第 1–10 章是基线叙述,其后每一批增补自带一节「本批导航」,说明它扩充、限定或改判了前文的哪一条。基线叙述中的「本卷」一律指写下它的那一次工作,不随后续增补改写。

**与母卷的关系。** 母卷是 `docs/develop/theory/CYCLE_ANDERSON_PERSISTENT_NODAL_BRANCHES.md`(下称「母卷」)。母卷定理 3.2 把坏势刻画为某个站点上的持续节点分支,并在长度 8 与 9 的圈上给出与 Laplace 算子没有非平凡共享对称的坏势;母卷注 5.2 指出更长的圈需要非周期构造,开放问题 6.2 问哪些合数长度存在此类势,开放问题 6.3 问节点因子能否用转移矩阵描述。本卷回答这三处缺口的主要部分:

1. 第 3 章用单值矩阵刻画持续节点分支:站点 $j$ 的节点因子与从 $j$ 出发的单值矩阵的「上三角单位」条件有相同的不可约因子(定理 3.6)。
2. 第 4 章证明单点缺陷原理:把块 $u$ 重复 $m\ge3$ 次得到周期势,在任一站点任意改动势值后,该站点有持续节点分支,其节点因子被无平方因子的 $\pm\Psi_m(\operatorname{tr}B_u)$ 整除(定理 4.3、命题 4.9);对 $\Psi_m$ 的单个根,可改动的站点放宽为一个同余类(定理 4.6)。
3. 第 5 章给出由 $\pm1$ 游程结构判定共享交换子只含标量的单边判据(定理 5.4)。
4. 第 6 章构造显式族 $U_{r,m}$,证明对一切 $r,m\ge3$ 它在 $C_{rm}$ 上是坏势且共享交换子只含标量(定理 6.2),并推出:每个既非素数、也非素数两倍的长度 $L\ge3$ 都有此类势(定理 6.4);节点因子含有 $\Psi_m(\sigma_{u_r})$ 的全部不可约因子,块迹有 Chebyshev 闭式 $\sigma_{u_r}=bS_{r-1}(a)-2S_{r-2}(a)$(命题 6.9);$r=3$ 时不可约分解是显式的(定理 6.5),$r\le8$、$m\le12$ 时节点因子恰为 $\pm\Psi_m(\sigma_{u_r})$(命题 7.5)。
5. 第 7 章处理小长度:$L=4$ 不存在(命题 7.2),$L=6,10,14$ 不存在(命题 7.4,依赖第 10 章的有限精确证书);于是 $3\le L\le21$ 时此类势存在当且仅当 $L$ 既非素数也非素数两倍(定理 7.6)。余下的开放长度恰为 $L=2p$,$p\ge11$ 为素数(开放问题 8.5)。

## 2. 记号与约定

**约定 2.1（沿用母卷的记号）。** 本卷沿用母卷约定 2.1–2.5:$C_L$、$A_L$、$\Delta_L=2I-A_L$、$e_i$、$E_{ij}$,Anderson 哈密顿量 $H_t=\Delta_L+tV$($V=\operatorname{diag}(v)$),特征多项式 $p=\det(\lambda I-H_t)$ 与主子式多项式 $q_j=\det(\lambda I-H_t^{(j)})$,坏势与好势,共享对称与共享交换子。除另行说明外 $L\ge3$,站点取 $\mathbb Z/L\mathbb Z$ 中的值,势 $v\in\mathbb R^L$;取值于 $\{-1,1\}$ 的势称为 $\pm1$ 势。若母卷定理 3.2 的五个等价条件对站点 $j$ 成立,称 $v$ 在 $j$ 处有**持续节点分支**;此时 $p$ 与 $q_j$ 在 $\mathbb R(t)[\lambda]$ 中的首一最大公因式记作 $g_j$,称为 $j$ 处的**节点因子**。由母卷定理 3.2 的证明,$g_j\in\mathbb R[t][\lambda]$。

**约定 2.2（字母与转移矩阵）。** 对势 $v$ 与站点 $i$,记

$$
d_i=d_i(\lambda,t)=2+tv_i-\lambda\in\mathbb R[\lambda,t],\qquad T(d)=\begin{pmatrix}d&-1\\ 1&0\end{pmatrix},\qquad \det T(d)=1 .
$$

对 $\pm1$ 势,沿用母卷定义 4.2 的记号 $a=2-\lambda+t$,$b=2-\lambda-t$:$v_i=1$ 时 $d_i=a$,$v_i=-1$ 时 $d_i=b$。对定义在 $\mathbb Z$ 或 $\mathbb Z/L\mathbb Z$ 上的序列 $z$,记 $Z_i=(z_i,z_{i-1})^{\top}$。站点 $i$ 处的本征方程 $d_iz_i-z_{i-1}-z_{i+1}=0$ 等价于 $Z_{i+1}=T(d_i)Z_i$。当 $(\lambda,t)$ 取某个含 $\mathbb R$ 的域 $K$ 中的值 $(\lambda_0,t_0)$ 时,上述多项式按值代入,$H_{t_0}$ 视为 $K$ 上的矩阵。

**约定 2.3（块、块转移矩阵与块迹）。** 块是有限实序列 $u=(u_0,\dots,u_{r-1})$,$r\ge1$。记 $d(x)=2+tx-\lambda$,

$$
B_u=T(d(u_{r-1}))\cdots T(d(u_1))\,T(d(u_0)),\qquad \sigma_u=\operatorname{tr}B_u\in\mathbb R[\lambda,t].
$$

$\pm1$ 块也写成 $\{+,-\}$ 上的字,例如 $u=-++$ 表示 $(-1,1,1)$,此时 $B_u=T(a)T(a)T(b)$。$u^k$ 表示 $k$ 个 $u$ 的串接;圈 $C_L$ 上的势写成循环字 $v_0v_1\cdots v_{L-1}$。由块 $u$ 生成的 $C_{rm}$ 上的周期势记作 $\tilde u$,$\tilde u_i=u_{i\bmod r}$。

**约定 2.4（Chebyshev 多项式与 $\Psi_m$）。** 令 $S_{-2}=-1$,$S_{-1}=0$,$S_0=1$,并对 $n\ge0$ 令 $S_{n+1}(x)=xS_n(x)-S_{n-1}(x)$;于是 $S_n(2\cos\theta)\sin\theta=\sin((n+1)\theta)$。对整数 $m\ge1$ 令

$$
\Psi_m(x)=\prod_{0<k<m/2}\bigl(x-2\cos(2\pi k/m)\bigr)\in\mathbb R[x],
$$

空积为 $1$。$\Psi_m$ 首一,次数为 $\lfloor(m-1)/2\rfloor$,根两两不同且都在开区间 $(-2,2)$ 内;例如 $\Psi_3=x+1$,$\Psi_4=x$,$\Psi_5=x^2+x-1$,$\Psi_6=x^2-1$。

**约定 2.5（二面体作用、游程与生成代数）。** 二面体群 $D_L$ 由旋转 $i\mapsto i+s$ 与反射 $i\mapsto s-i$ 组成,作为置换矩阵作用于 $\mathbb R^L$;势 $v$ 的稳定子是满足 $v_{\pi(i)}=v_i$ 的 $\pi\in D_L$ 全体。设 $\pm1$ 势 $v$ 两种值都出现;$v$ 的一个**游程**是循环相邻、取值相同的站点的极大集合,取值为 $\varepsilon$ 的游程称 $\varepsilon$-游程,其站点数称为长度。记 $P_\varepsilon=\tfrac12(I+\varepsilon V)$($\varepsilon=\pm1$),对站点集 $S$ 记 $P_S=\sum_{i\in S}E_{ii}$。$\mathcal A_v$ 表示由 $A_L$ 与 $V$ 生成的实有单位代数,它也由 $\Delta_L$ 与 $V$ 生成。$J_\ell$ 表示 $\ell$ 个顶点的路的邻接矩阵($J_1=(0)$)。

## 3. 单值演算

**定义 3.1（单值矩阵）。** 设 $v$ 是 $C_L$ 上的势,$j$ 是站点。站点 $j$ 处的单值矩阵是

$$
M_j=T(d_{j+L})\,T(d_{j+L-1})\cdots T(d_{j+1})=\begin{pmatrix}\alpha_j&\beta_j\\ \gamma_j&\delta_j\end{pmatrix},
$$

下标按模 $L$ 理解,故最左的因子是 $T(d_j)$。其中 $\alpha_j,\beta_j,\gamma_j,\delta_j\in\mathbb R[\lambda,t]$,且 $\det M_j=1$。

**引理 3.2（连分式行列式与单值矩阵的迹）。** 设 $R$ 是交换环,$x_1,\dots,x_n\in R$。记 $K_n(x_1,\dots,x_n)$ 为对角元 $x_1,\dots,x_n$、次对角元全为 $-1$ 的 $n\times n$ 三对角矩阵的行列式,并约定空序列的 $K_0=1$、长度为 $-1$ 的 $K_{-1}=0$。则:

1. 对 $n\ge1$,

$$
T(x_n)\cdots T(x_1)=\begin{pmatrix}K_n(x_1,\dots,x_n)&-K_{n-1}(x_2,\dots,x_n)\\ K_{n-1}(x_1,\dots,x_{n-1})&-K_{n-2}(x_2,\dots,x_{n-1})\end{pmatrix};
$$

2. 对 $n\ge3$,对角元为 $x_1,\dots,x_n$、在循环相邻位置 $(i,i\pm1\bmod n)$ 取 $-1$、其余为 $0$ 的 $n\times n$ 矩阵 $X$ 满足

$$
\det X=K_n(x_1,\dots,x_n)-K_{n-2}(x_2,\dots,x_{n-1})-2=\operatorname{tr}\bigl(T(x_n)\cdots T(x_1)\bigr)-2 .
$$

因此对 $C_L$ 上的势 $v$ 与任一站点 $j$,有 $\gamma_j=(-1)^{L-1}q_j$ 与 $\alpha_j+\delta_j-2=(-1)^Lp$。

**证明。** 按最后一行展开三对角行列式:最后一行只有 $(n,n)$ 位的 $x_n$ 与 $(n,n-1)$ 位的 $-1$;后者的余子式矩阵最后一列只剩 $(n-1,n)$ 位的 $-1$,其行列式为 $-K_{n-2}(x_1,\dots,x_{n-2})$,带符号 $(-1)^{2n-1}=-1$。于是

$$
K_n(x_1,\dots,x_n)=x_nK_{n-1}(x_1,\dots,x_{n-1})-K_{n-2}(x_1,\dots,x_{n-2}),\qquad n\ge1,
$$

$n=1$ 时由约定 $K_{-1}=0$ 成立。同理按第一行展开得 $K_n(x_1,\dots,x_n)=x_1K_{n-1}(x_2,\dots,x_n)-K_{n-2}(x_3,\dots,x_n)$。

(1) 对 $n$ 归纳。$n=1$ 时右边为 $\begin{pmatrix}x_1&-1\\1&0\end{pmatrix}=T(x_1)$。设 $n$ 时成立,左乘 $T(x_{n+1})$:第一行等于 $x_{n+1}$ 乘旧第一行减旧第二行,即

$$
\bigl(x_{n+1}K_n(x_1,\dots,x_n)-K_{n-1}(x_1,\dots,x_{n-1}),\ -x_{n+1}K_{n-1}(x_2,\dots,x_n)+K_{n-2}(x_2,\dots,x_{n-1})\bigr),
$$

由最后一行的递推,它等于 $\bigl(K_{n+1}(x_1,\dots,x_{n+1}),\,-K_n(x_2,\dots,x_{n+1})\bigr)$;第二行等于旧第一行。这正是 $n+1$ 时的公式。

(2) 用 Leibniz 展开。置换 $\pi$ 的项 $\prod_iX_{i,\pi(i)}$ 非零只当 $\pi(i)\in\{i-1,i,i+1\}$ 对一切 $i$ 成立。两个旋转 $i\mapsto i\pm1$ 满足此条件,因 $n\ge3$ 它们不同;每个都是 $n$-轮换,符号 $(-1)^{n-1}$,项为 $(-1)^n$,贡献合计 $2(-1)^{n-1}(-1)^n=-2$。若 $\pi$ 不是旋转,则 $\pi$ 只由不动点与相邻对换组成:若 $\pi(i)=i+1$,则 $i$ 所在的轮换沿 $i,i+1,i+2,\dots$ 前进,直到首次出现 $\pi(k)=k-1$;单射性迫使 $k-1$ 尚未作为像出现,故 $k=i+1$,即 $(i\ i+1)$ 是对换;若一直前进则 $\pi$ 是旋转;$\pi(i)=i-1$ 的情形对称。不含对换 $(n\ 1)$ 的这类置换恰是路矩阵(删去 $(1,n)$、$(n,1)$ 两个角元)的全部非零 Leibniz 项,合计 $K_n(x_1,\dots,x_n)$;含 $(n\ 1)$ 的项等于对换符号 $-1$ 乘 $X_{n1}X_{1n}=1$ 再乘中间路 $x_2,\dots,x_{n-1}$ 的全部非零 Leibniz 项,合计 $-K_{n-2}(x_2,\dots,x_{n-1})$。由 (1),$\operatorname{tr}(T(x_n)\cdots T(x_1))=K_n(x_1,\dots,x_n)-K_{n-2}(x_2,\dots,x_{n-1})$。

最后,$H_t-\lambda I$ 的对角元是 $d_i$、循环相邻位置是 $-1$。删去站点 $j$ 后,按 $j+1,\dots,j+L-1$ 的顺序排列剩余站点(同时置换行列不改变行列式),$H_t^{(j)}-\lambda I$ 是对角元 $d_{j+1},\dots,d_{j+L-1}$ 的三对角矩阵,故 $q_j=(-1)^{L-1}K_{L-1}(d_{j+1},\dots,d_{j+L-1})$。另一方面 $M_j=T(d_j)\,N$,$N=T(d_{j+L-1})\cdots T(d_{j+1})$,而 $T(d_j)$ 的第二行是 $(1,0)$,故 $\gamma_j=N_{11}=K_{L-1}(d_{j+1},\dots,d_{j+L-1})$,由 (1)。同理按 $j+1,\dots,j+L$ 的循环顺序排列全部站点,(2) 给出 $\det(H_t-\lambda I)=\operatorname{tr}M_j-2$,即 $(-1)^Lp=\alpha_j+\delta_j-2$。∎

**注 3.3（先例）。** 引理 3.2 (1) 是连分式行列式(continuant)的标准递推;(2) 与 $p$ 的表达式是周期 Jacobi 算子 Floquet 判别式的有限圈形式。两者都是已知结果,写出证明只为本卷自足;出处见第 9 章。

**引理 3.4（任意域上的节点步）。** 设 $K$ 是域,$H\in K^{n\times n}$ 对称,$n\ge2$,$j$ 是下标,$\lambda_0\in K$。则存在 $z\in K^n\setminus\{0\}$ 使 $Hz=\lambda_0z$ 且 $z_j=0$,当且仅当 $\lambda_0$ 同时是 $\det(\lambda I-H)$ 与 $\det(\lambda I-H^{(j)})$ 的根。

**证明。** 记 $\langle x,y\rangle=\sum_ix_iy_i$,它是 $K^n$ 上的非退化对称双线性型;对子空间 $W$ 有 $(W^{\perp})^{\perp}=W$。对对称矩阵 $S$,$(\operatorname{im}S)^{\perp}=\ker S^{\top}=\ker S$,故 $\operatorname{im}S=(\ker S)^{\perp}$。

若 $Hz=\lambda_0z$,$z\ne0$,$z_j=0$,则 $\lambda_0$ 是 $H$ 的本征值;删去第 $j$ 个坐标得 $z'\ne0$,且对 $i\ne j$ 有 $(H^{(j)}z')_i=(Hz)_i=\lambda_0z_i$,故 $\lambda_0$ 也是 $H^{(j)}$ 的本征值。反之,设 $\lambda_0$ 是两者的根,取 $H^{(j)}$ 的本征向量 $y'\in K^{n-1}$,在第 $j$ 位补 $0$ 得 $y$。则 $(H-\lambda_0I)y=\gamma e_j$,$\gamma=\sum_kH_{jk}y_k$。若 $\gamma=0$,$y$ 即所求。若 $\gamma\ne0$,则 $e_j\in\operatorname{im}(H-\lambda_0I)=(\ker(H-\lambda_0I))^{\perp}$,于是非零核 $\ker(H-\lambda_0I)$ 中每个 $z$ 都满足 $z_j=\langle z,e_j\rangle=0$。∎

**注 3.5（与母卷的关系）。** 引理 3.4 在 $K=\mathbb R$ 时就是母卷定理 3.2 证明中的节点步;那里用正交补,这里只用双线性型,因而对 $\mathbb R(t)$ 的代数闭包同样成立。下面的定理 3.6 需要这一点。

**定理 3.6（持续节点分支的单值刻画）。** 设 $v\in\mathbb R^L$,$L\ge3$,$j$ 是站点,$M_j$ 如定义 3.1。

1. 对任一含 $\mathbb R$ 的域 $K$ 与任一 $(\lambda_0,t_0)\in K^2$,下列三条等价:(a) 存在 $z\in K^L\setminus\{0\}$ 使 $H_{t_0}z=\lambda_0z$ 且 $z_j=0$;(b) $\gamma_j(\lambda_0,t_0)=0$ 且 $\alpha_j(\lambda_0,t_0)=1$;(c) $M_j(\lambda_0,t_0)e_1=e_1$。此时 $\delta_j(\lambda_0,t_0)=1$,即 $M_j(\lambda_0,t_0)$ 是对角元为 $1$ 的上三角矩阵;满足 (a) 的 $z$ 在相差非零倍数的意义下唯一,且 $z_{j+1}\ne0$。
2. $\mathbb R(t)[\lambda]$ 中的首一不可约多项式 $\pi$ 同时整除 $p$ 与 $q_j$,当且仅当它同时整除 $\gamma_j$ 与 $\alpha_j-1$。因此节点因子 $g_j$ 与 $\gcd(\gamma_j,\alpha_j-1)$ 有相同的首一不可约因子;$v$ 在 $j$ 处有持续节点分支,当且仅当 $\gamma_j$ 与 $\alpha_j-1$ 在 $\mathbb R(t)[\lambda]$ 中有正次数的公因子。
3. $v$ 是坏势,当且仅当存在站点 $j$ 使 $\operatorname{Res}_\lambda(\gamma_j,\alpha_j-1)=0$ 于 $\mathbb R[t]$。

**证明。** (1) 先证 (a)⇒(c)。把 $z$ 按周期延拓到 $\mathbb Z$,本征方程对一切 $i\in\mathbb Z$ 成立,于是 $Z_{i+1}=T(d_i)Z_i$。若 $z_{j+1}=0$,则 $Z_{j+1}=0$,而每个 $T(d_i)$ 可逆,故一切 $Z_i=0$,与 $z\ne0$ 矛盾。把 $z$ 放缩使 $z_{j+1}=1$,则 $Z_{j+1}=e_1$,且

$$
e_1=Z_{j+1+L}=T(d_{j+L})\cdots T(d_{j+1})\,Z_{j+1}=M_j(\lambda_0,t_0)\,e_1 .
$$

再证 (c)⇒(a)。令 $Z_{j+1}=e_1$,对 $i=j+1,\dots,j+L$ 递推 $Z_{i+1}=T(d_i)Z_i$。由于 $T(d)(x,y)^{\top}=(dx-y,x)^{\top}$,$Z_{i+1}$ 的第二个坐标等于 $Z_i$ 的第一个坐标,故存在唯一的 $z_j,z_{j+1},\dots,z_{j+L+1}$ 使 $Z_i=(z_i,z_{i-1})^{\top}$,并且站点 $i=j+1,\dots,j+L$ 处的方程 $d_iz_i-z_{i-1}-z_{i+1}=0$ 成立。条件 $M_je_1=e_1$ 即 $Z_{j+L+1}=Z_{j+1}$,即 $z_{j+L+1}=z_{j+1}=1$,$z_{j+L}=z_j=0$。于是 $z_{j+1},\dots,z_{j+L}$ 定义了 $\mathbb Z/L\mathbb Z$ 上的向量,它在 $j\equiv j+L$ 处为 $0$,在 $j+1$ 处为 $1$;站点 $j+1,\dots,j+L-1$ 处的方程已成立,站点 $j\equiv j+L$ 处的方程由 $z_{j+L+1}=z_{j+1}$ 化为已成立的那一条。故 (a) 成立。

(b)⇔(c):$M_je_1=(\alpha_j,\gamma_j)^{\top}$。若 (b) 成立,$\det M_j=\alpha_j\delta_j-\beta_j\gamma_j=1$ 给出 $\delta_j=1$。唯一性:满足 (a) 的 $z$ 都有 $z_{j+1}\ne0$,而 $(z_j,z_{j+1})=(0,z_{j+1})$ 通过递推决定整个 $z$,故这样的 $z$ 构成一维空间去掉零向量。

(2) 取 $\mathbb R(t)$ 的代数闭包 $F$ 与 $\pi$ 在 $F$ 中的一个根 $`\lambda_*`$。$\pi$ 是 $`\lambda_*`$ 在 $\mathbb R(t)$ 上的极小多项式,故对 $f\in\mathbb R(t)[\lambda]$ 有 $`\pi\mid f\iff f(\lambda_*)=0`$。把 $H_t$ 看作 $F$ 上的对称矩阵,其特征多项式与 $j$ 处主子式多项式分别是 $p$ 与 $q_j$。由引理 3.4($K=F$),$`p(\lambda_*)=q_j(\lambda_*)=0`$ 当且仅当 (a) 对 $`(\lambda_*,t)`$ 成立;由 (1),这当且仅当 $`\gamma_j(\lambda_*,t)=0`$ 且 $`\alpha_j(\lambda_*,t)=1`$。两端各自等价于 $\pi$ 的整除条件。于是 $g_j=\gcd(p,q_j)$ 与 $\gcd(\gamma_j,\alpha_j-1)$ 的首一不可约因子相同,其中一个次数为正当且仅当另一个次数为正;由母卷定理 3.2 的 (1),前者次数为正就是持续节点分支。

(3) 由引理 3.2 (1),$\gamma_j=K_{L-1}(d_{j+1},\dots,d_{j+L-1})$ 的 $\lambda$-首项是 $(-\lambda)^{L-1}$,$\alpha_j=K_L(d_{j+1},\dots,d_{j+L})$ 的 $\lambda$-首项是 $(-\lambda)^L$;两者首项系数都是 $\pm1$。故在域 $\mathbb R(t)$ 上,$\operatorname{Res}_\lambda(\gamma_j,\alpha_j-1)=0$ 当且仅当两者有正次数公因子,由 (2) 当且仅当 $j$ 处有持续节点分支。母卷推论 3.3 说 $v$ 坏当且仅当某个站点有持续节点分支。∎

**注 3.7（模 $\gamma_j$ 的平方关系）。** 由引理 3.2 与 $\det M_j=1$,

$$
(-1)^L\alpha_j\,p=\alpha_j(\alpha_j+\delta_j-2)=\alpha_j^2+1+\beta_j\gamma_j-2\alpha_j=(\alpha_j-1)^2+\beta_j\gamma_j .
$$

所以模 $\gamma_j$ 有 $(-1)^L\alpha_jp\equiv(\alpha_j-1)^2$:在 $q_j$ 的根上,$p$ 的消失与 $\alpha_j-1$ 的消失等价,这是定理 3.6 (2) 的另一种读法。该恒等式在后文证明中不被使用。

## 4. 单点缺陷原理

**引理 4.1（Chebyshev 幂公式）。** 设 $R$ 是交换环,$B\in R^{2\times2}$,$\det B=1$,$x=\operatorname{tr}B$。则对一切 $n\ge0$,

$$
B^n=S_{n-1}(x)\,B-S_{n-2}(x)\,I,\qquad\text{特别地}\qquad B^m-I=S_{m-1}(x)\,B-\bigl(S_{m-2}(x)+1\bigr)I .
$$

**证明。** $n=0$ 时右边为 $0\cdot B+I$,$n=1$ 时为 $B-0\cdot I$。设 $n\ge1$ 时成立。由 Cayley–Hamilton 定理 $B^2=xB-I$,于是

$$
B^{n+1}=S_{n-1}B^2-S_{n-2}B=(xS_{n-1}-S_{n-2})B-S_{n-1}I=S_nB-S_{n-1}I,
$$

最后一步用约定 2.4 的递推。∎

**命题 4.2（$\Psi_m$ 与 $B^m=I$）。** 设 $m\ge3$。

1. $\Psi_m$ 是 $S_{m-1}$ 与 $S_{m-2}+1$ 在 $\mathbb Q[x]$ 中的首一最大公因式;特别地 $\Psi_m\in\mathbb Z[x]$。
2. 设 $K$ 是含 $\mathbb R$ 的代数闭域,$B\in K^{2\times2}$,$\det B=1$,$\Psi_m(\operatorname{tr}B)=0$。则 $B^m=I$,且 $B\ne\pm I$。

**证明。** (1) 由约定 2.4,$S_{m-1}(2\cos\theta)\sin\theta=\sin(m\theta)$。对 $k=1,\dots,m-1$ 取 $\theta=\pi k/m\in(0,\pi)$,得 $S_{m-1}$ 的 $m-1$ 个两两不同的实根 $2\cos(\pi k/m)$;$S_{m-1}$ 首一且次数为 $m-1$,所以这就是它的全部根,且都是单根。在这些点上

$$
S_{m-2}(2\cos\theta)\sin\theta=\sin(\pi k-\theta)=-(-1)^k\sin\theta,
$$

故 $S_{m-2}(2\cos(\pi k/m))=-1$ 当且仅当 $k$ 为偶数。写 $k=2k'$,条件 $0<k<m$ 变为 $0<k'<m/2$。所以 $S_{m-1}$ 与 $S_{m-2}+1$ 在 $\mathbb C$ 中的公共根恰是 $\Psi_m$ 的根,并且它们是 $S_{m-1}$ 的单根,于是二者在 $\mathbb C[x]$ 中的首一最大公因式是 $\Psi_m$。Euclid 算法不离开 $\mathbb Q$,故同一个最大公因式在 $\mathbb Q[x]$ 中算出,$\Psi_m\in\mathbb Q[x]$。$\Psi_m$ 首一且整除首一的 $S_{m-1}\in\mathbb Z[x]$,由 Gauss 引理 $\Psi_m\in\mathbb Z[x]$。

(2) 设 $\operatorname{tr}B=2\cos\theta$,$\theta=2\pi k/m$,$0<k<m/2$,故 $0<\theta<\pi$。$K$ 含 $\mathbb R$ 的代数闭包 $\mathbb C$,令 $\zeta=\cos\theta+i\sin\theta\in K$。$B$ 的特征多项式是 $\mu^2-2\cos\theta\,\mu+1=(\mu-\zeta)(\mu-\zeta^{-1})$,而 $\zeta^2\ne1$,故两个特征值不同,$B$ 在 $K$ 上可对角化,$B=G\operatorname{diag}(\zeta,\zeta^{-1})G^{-1}$。由 $\zeta^m=1$ 得 $B^m=I$;特征值不同说明 $B$ 不是数量矩阵,故 $B\ne\pm I$。∎

**定理 4.3（单点缺陷原理）。** 设 $r\ge1$,$m\ge3$,$L=rm\ge3$,$u\in\mathbb R^r$ 是块,$\tilde u$ 是它生成的 $C_L$ 上的周期势(约定 2.3)。设 $q$ 是站点,势 $w\in\mathbb R^L$ 在 $q$ 以外的站点上与 $\tilde u$ 相同,$w_q$ 是任意实数。则:

1. $\Psi_m(\sigma_u)$ 作为 $\lambda$ 的多项式次数为 $r\lfloor(m-1)/2\rfloor\ge1$,首项系数为 $\pm1$;
2. 对每个实数 $t_0$ 与 $\Psi_m(\sigma_u(\cdot,t_0))$ 的每个复根 $\lambda_0$,$\lambda_0$ 是实数,并且 $H^w_{t_0}=\Delta_L+t_0\operatorname{diag}(w)$ 有本征值 $\lambda_0$ 的、在 $q$ 处为零的实本征向量;
3. $\Psi_m(\sigma_u)$ 在 $\mathbb R(t)[\lambda]$ 中的每个首一不可约因子都整除 $w$ 在 $q$ 处的节点因子 $g_q$。

特别地,$w$ 在 $q$ 处有持续节点分支,$w$ 是坏势。

**证明。** (1) 由引理 3.2 (1),$B_u$ 的 $(1,1)$ 元是 $K_r(d(u_0),\dots,d(u_{r-1}))$,其 $\lambda$-首项是各对角元之积的首项 $(-\lambda)^r$;$(2,2)$ 元是 $-K_{r-2}(\cdots)$,$\lambda$-次数至多 $r-2$。所以 $\sigma_u$ 的 $\lambda$-次数为 $r$、首项系数为 $(-1)^r$,与 $t$ 无关。$\Psi_m$ 首一且次数 $\lfloor(m-1)/2\rfloor\ge1$($m\ge3$),合成后得 (1)。

*一般域上的步骤。* 设 $K$ 是含 $\mathbb R$ 的代数闭域,$(\lambda_0,t_0)\in K^2$ 满足 $\Psi_m(\sigma_u(\lambda_0,t_0))=0$。考虑 $\mathbb Z$ 上的递推

$$
\tilde d_iz_i-z_{i-1}-z_{i+1}=0\quad(i\in\mathbb Z),\qquad \tilde d_i=2+t_0u_{i\bmod r}-\lambda_0 ,
$$

其解空间由 $Z_0\in K^2$ 唯一确定,是二维的。由于 $\tilde d_{i+r}=\tilde d_i$,有 $Z_{kr}=B^kZ_0$,其中 $B=B_u(\lambda_0,t_0)$。由命题 4.2 (2),$B^m=I$,故 $Z_L=Z_0$。序列 $i\mapsto Z_{i+L}$ 满足同一个递推(系数周期为 $r$,而 $r\mid L$)且与 $i\mapsto Z_i$ 在 $i=0$ 处相同,故 $Z_{i+L}=Z_i$ 对一切 $i$ 成立:递推的每个解都是 $L$-周期的。取 $z_q=0$、$z_{q+1}=1$ 的那个解(由 $Z_{q+1}=e_1$ 向两侧递推得到),它给出 $\tilde z\in K^L\setminus\{0\}$,满足 $H^{\tilde u}_{t_0}\tilde z=\lambda_0\tilde z$ 与 $\tilde z_q=0$。由于

$$
H^w_{t_0}=H^{\tilde u}_{t_0}+t_0\,(w_q-\tilde u_q)\,E_{qq},\qquad E_{qq}\tilde z=\tilde z_q\,e_q=0,
$$

有 $H^w_{t_0}\tilde z=\lambda_0\tilde z$,且 $\tilde z_q=0$。

(2) 取 $K=\mathbb C$。上一步给出 $H^w_{t_0}$ 的复本征向量 $\tilde z$;$H^w_{t_0}$ 是实对称矩阵,故 $\lambda_0$ 是实数。$\operatorname{Re}\tilde z$ 与 $\operatorname{Im}\tilde z$ 都满足 $H^w_{t_0}x=\lambda_0x$ 与 $x_q=0$,且至少一个非零。由 (1),$\Psi_m(\sigma_u(\cdot,t_0))$ 次数为正,复根 $\lambda_0$ 存在。

(3) 设 $\pi$ 是 $\Psi_m(\sigma_u)$ 的首一不可约因子,$`\lambda_*`$ 是它在 $\mathbb R(t)$ 的代数闭包 $F$ 中的根。以 $K=F$、$`(\lambda_0,t_0)=(\lambda_*,t)`$ 应用一般域上的步骤,得 $H^w_t$ 在 $F$ 上的本征向量在 $q$ 处为零;由引理 3.4,$`p_w(\lambda_*)=q_{w,q}(\lambda_*)=0`$,而 $\pi$ 是 $`\lambda_*`$ 的极小多项式,故 $\pi\mid p_w$,$\pi\mid q_{w,q}$,从而 $\pi\mid g_q$。由 (1) 这样的 $\pi$ 存在,$g_q$ 次数为正;由母卷定理 3.2 与推论 3.3,$w$ 在 $q$ 处有持续节点分支并且是坏势。∎

**推论 4.4（单字母缺陷字）。** 设 $r\ge1$,$m\ge3$,$rm\ge3$,$u\in\{-1,1\}^r$,$0\le s<r$,$u^{\sharp}$ 是把 $u$ 的第 $s$ 个字母变号所得的块。则 $C_{rm}$ 上的 $\pm1$ 势 $w=u^{m-1}u^{\sharp}$ 是坏势;它在站点 $q=(m-1)r+s$ 处有持续节点分支,且 $\Psi_m(\sigma_u)$ 的每个首一不可约因子都整除 $g_q$。

**证明。** $w$ 与 $\tilde u$ 只在站点 $q$ 处可能不同,应用定理 4.3。∎

**注 4.5（解释与先例）。** 当 $w=\tilde u$ 时,定理 4.3 的一般域上的步骤说的是:Bloch 相位 $2\pi k/m$($0<k<m/2$)处周期算子的本征空间是二维的,这是周期 Jacobi 算子 Floquet 理论的熟知事实(第 9 章)。在本征值的二维本征空间里总有在给定站点 $q$ 为零的向量,而在 $q$ 为零的本征向量不受 $q$ 处势值的影响,这一点也是初等的。定理 4.3 的内容在于把二者合在一起:缺陷破坏了周期势的平移对称与(一般情形下的)反射对称,却留下一条对一切耦合 $t$ 都存在、并由 $\Psi_m(\sigma_u)$ 显式给出的节点分支。由定理 3.6,在 $q$ 处这表现为 $M_q$ 在 $\Psi_m(\sigma_u)$ 的根上是上三角单位矩阵;引理 4.1 把周期部分的单值写成 $B^m-I=S_{m-1}(\sigma_u)B-(S_{m-2}(\sigma_u)+1)I$,命题 4.2 (1) 说明 $\Psi_m(\sigma_u)$ 恰是使两个系数同时为零的因子。

**定理 4.6（同余站点上的多点缺陷）。** 设 $r\ge1$,$m\ge3$,$L=rm$,$u\in\mathbb R^r$,$\tilde u$ 如定理 4.3。取整数 $0<j<m/2$,令 $c=2\cos(2\pi j/m)$,$g=\gcd(m,2j)$,$e=m/g$,站点集

$$
Q=\{\,q+k\,e\,r\bmod L:\ k\in\mathbb Z\,\}\subset\mathbb Z/L\mathbb Z,\qquad |Q|=g .
$$

设势 $w\in\mathbb R^L$ 在 $Q$ 以外与 $\tilde u$ 相同,在 $Q$ 上取任意实数。则:

1. 对每个实数 $t_0$ 与 $\sigma_u(\cdot,t_0)-c$ 的每个复根 $\lambda_0$,$\lambda_0$ 是实数,$H^w_{t_0}$ 有本征值 $\lambda_0$ 的实本征向量 $z$,它在 $Q$ 的每个站点处为零,并且对一切 $k\ge1$ 满足 $z_{q+kr}=S_{k-1}(c)\,z_{q+r}$;
2. $\sigma_u-c$ 在 $\mathbb R(t)[\lambda]$ 中的每个首一不可约因子,对每个 $q'\in Q$ 都整除 $w$ 在 $q'$ 处的节点因子 $g_{q'}$。

特别地,$w$ 在 $Q$ 的每个站点处都有持续节点分支。$g=1$ 时 $Q=\{q\}$;$m$ 为偶数且 $j=1$ 时 $Q=\{q,\,q+L/2\}$。

**证明。** 由 $0<2j<m$ 得 $m\nmid2j$,故 $e\ge2$;$Q$ 是 $\mathbb Z/L\mathbb Z$ 中以 $er$ 为步长的陪集,$er\mid L$,元素个数为 $L/(er)=g$。

设 $K$ 是含 $\mathbb R$ 的代数闭域,$(\lambda_0,t_0)\in K^2$ 满足 $\sigma_u(\lambda_0,t_0)=c$。令 $\theta=2\pi j/m$,则 $\Psi_m(c)=0$,与定理 4.3 证明中的一般域步骤相同,递推 $\tilde d_iz_i-z_{i-1}-z_{i+1}=0$ 的解空间是二维的,且每个解都是 $L$-周期的。取 $z_q=0$、$z_{q+1}=1$ 的解 $z$。令 $B'=T(\tilde d_{q+r-1})\cdots T(\tilde d_q)$,则 $Z_{q+r}=B'Z_q$ 且 $Z_{q+kr}=B'^kZ_q$。$B'$ 的因子是 $B_u$ 的因子的一个循环轮换,故 $B'$ 与 $B_u(\lambda_0,t_0)$ 相似,$\operatorname{tr}B'=c$,$\det B'=1$。由引理 4.1,

$$
Z_{q+kr}=S_{k-1}(c)\,B'Z_q-S_{k-2}(c)\,Z_q,
$$

取第一个坐标并用 $z_q=0$ 得 $z_{q+kr}=S_{k-1}(c)\,z_{q+r}$。而 $S_{k-1}(c)\sin\theta=\sin(k\theta)$,$\sin\theta\ne0$;当 $k=en$($n\in\mathbb Z_{\ge0}$)时 $k\theta=(m/g)\,n\cdot2\pi j/m=\pi\cdot(2j/g)\cdot n\in\pi\mathbb Z$,因为 $g\mid2j$。所以 $z$ 在 $q+n\,e\,r$($n\in\mathbb Z_{\ge0}$)处为零,由 $L$-周期性在整个 $Q$ 上为零。于是

$$
H^w_{t_0}z=H^{\tilde u}_{t_0}z+t_0\sum_{q'\in Q}(w_{q'}-\tilde u_{q'})\,z_{q'}\,e_{q'}=\lambda_0z .
$$

(1) 取 $K=\mathbb C$:$H^w_{t_0}$ 实对称,故 $\lambda_0$ 实;取 $z$ 的实部或虚部中非零的一个即得实本征向量,它仍在 $Q$ 上为零并满足同一递推关系,因而仍满足 $z_{q+kr}=S_{k-1}(c)z_{q+r}$(该关系对实部与虚部分别成立)。由定理 4.3 的证明 (1),$\sigma_u(\cdot,t_0)-c$ 的 $\lambda$-次数为 $r\ge1$,复根存在。

(2) 设 $\pi$ 是 $\sigma_u-c$ 的首一不可约因子,$`\lambda_*`$ 是它在 $\mathbb R(t)$ 的代数闭包 $F$ 中的根。以 $K=F$、$`(\lambda_*,t)`$ 应用上面的步骤,得 $H^w_t$ 在 $F$ 上的本征向量在每个 $q'\in Q$ 处为零;由引理 3.4,$`p_w(\lambda_*)=q_{w,q'}(\lambda_*)=0`$,故 $\pi\mid g_{q'}$。∎

**注 4.7（多点缺陷的范围）。** 定理 4.3 对应于同时使用 $\Psi_m$ 的全部根、只在一个站点 $q$ 改动的情形;定理 4.6 对 $\Psi_m$ 的单个根放宽到 $\gcd(m,2j)$ 个同余站点。两者都要求改动的站点落在周期势某个节点本征向量的零点集中。母卷例 4.1 的势不在定理 4.3 与 4.6 的范围内(命题 8.4)。

**引理 4.8（带内块迹的根都是单根）。** 设 $u\in\mathbb R^r$,$r\ge1$,$t_0\in\mathbb R$,$c=2\cos\theta$,$0<\theta<\pi$。则 $\sigma_u(\cdot,t_0)-c$ 的 $r$ 个复根都是实的单根。

**证明。** 记 $\delta_i=2+t_0u_i$。$r=1$ 时 $\sigma_u=\delta_0-\lambda$,结论显然。$r=2$ 时 $\sigma_u-c=(\delta_0-\lambda)(\delta_1-\lambda)-2-c$,其判别式 $(\delta_0-\delta_1)^2+4(2+c)>0$,两根实且不同。

设 $r\ge3$。令 $H_\theta$ 为 $r\times r$ 复矩阵:对角元 $\delta_0,\dots,\delta_{r-1}$,$(i,i+1)$ 与 $(i+1,i)$ 位($0\le i\le r-2$)为 $-1$,角元 $(r-1,0)$ 位为 $-e^{i\theta}$、$(0,r-1)$ 位为 $-e^{-i\theta}$,其余为 $0$。$H_\theta$ 是 Hermite 矩阵。按引理 3.2 (2) 证明中的 Leibniz 展开计算 $\det(H_\theta-\lambda I)$:只由不动点与相邻对换组成的置换给出与那里相同的 $K_r-K_{r-2}$(对换 $(r-1\ 0)$ 的两个角元之积是 $e^{i\theta}e^{-i\theta}=1$);向前旋转的项是 $(-1)^{r-1}\cdot(-1)^{r-1}(-e^{i\theta})=-e^{i\theta}$,向后旋转的项是 $-e^{-i\theta}$。故

$$
\det(H_\theta-\lambda I)=\sigma_u(\lambda,t_0)-2\cos\theta ,
$$

于是 $\sigma_u(\cdot,t_0)-c$ 的根(计重数)就是 $H_\theta$ 的本征值(计代数重数),都是实数。设 $\lambda_0$ 是其中之一,$y\in\mathbb C^r$ 是 $H_\theta$ 对 $\lambda_0$ 的本征向量。令 $z_{kr+i}=e^{ik\theta}y_i$($k\in\mathbb Z$,$0\le i<r$),逐行核对 $H_\theta y=\lambda_0y$(第 $0$ 行与第 $r-1$ 行用到角元)可知 $z$ 满足递推 $(2+t_0u_{i\bmod r}-\lambda_0)z_i-z_{i-1}-z_{i+1}=0$($i\in\mathbb Z$)且 $Z_r=e^{i\theta}Z_0$。又 $Z_r=B_u(\lambda_0,t_0)Z_0$,而 $Z_0=(y_0,e^{-i\theta}y_{r-1})^{\top}$ 决定 $z$ 从而决定 $y$。所以 $y\mapsto Z_0$ 是从 $H_\theta$ 的 $\lambda_0$-本征空间到 $B_u(\lambda_0,t_0)$ 的 $e^{i\theta}$-本征空间的单射。$B_u(\lambda_0,t_0)$ 的迹为 $2\cos\theta$、行列式为 $1$,特征值 $e^{\pm i\theta}$ 不同,后一个本征空间是一维的。于是 $\lambda_0$ 的几何重数为 $1$;Hermite 矩阵的几何重数等于代数重数,故 $\lambda_0$ 是单根。∎

**命题 4.9（$\Psi_m(\sigma_u)$ 无平方因子并整除节点因子）。** 在定理 4.3 的条件下,$\Psi_m(\sigma_u)$ 在 $\mathbb R(t)[\lambda]$ 中无平方因子,并且 $(-1)^{r\lfloor(m-1)/2\rfloor}\Psi_m(\sigma_u)$(关于 $\lambda$ 首一)在 $\mathbb R[t][\lambda]$ 中整除 $w$ 在 $q$ 处的节点因子 $g_q$。

**证明。** 记 $N=r\lfloor(m-1)/2\rfloor$,$F=\Psi_m(\sigma_u)$;由定理 4.3 (1),$(-1)^NF$ 是 $\mathbb R[t][\lambda]$ 中关于 $\lambda$ 首一的多项式。取 $t_0=0$。$F(\cdot,0)=\prod_{0<k<m/2}(\sigma_u(\cdot,0)-2\cos(2\pi k/m))$;由引理 4.8,每个因子只有单根;不同 $k$ 的因子没有公共根,因为在公共根处 $\sigma_u$ 会取两个不同的值。故 $F(\cdot,0)$ 无重根。若 $h^2\mid F$,$h\in\mathbb R(t)[\lambda]$ 首一不可约,则 $h$ 与余因子都在 $\mathbb R[t][\lambda]$ 中($\mathbb R[t]$ 整闭,母卷定理 3.2 证明中的同一论证),代入 $t=0$ 后 $h(\cdot,0)$ 首一、次数为正,其平方整除 $F(\cdot,0)$,矛盾。所以 $F$ 的首一不可约因子两两不同;由定理 4.3 (3) 每个都整除 $g_q$,$\mathbb R(t)[\lambda]$ 是唯一分解整环,故 $(-1)^NF\mid g_q$;两者首一且系数在 $\mathbb R[t]$ 中,商也在 $\mathbb R[t][\lambda]$ 中。∎

## 5. 共享交换子的游程判据

**引理 5.1（对角单位的传播）。** 设 $v\in\mathbb R^L$,$L\ge3$。若存在站点 $j$ 使 $E_{jj}\in\mathcal A_v$ 且 $E_{j+1,j+1}\in\mathcal A_v$,则 $\mathcal A_v=M_L(\mathbb R)$。此时与 $\Delta_L$、$V$ 都可交换的复矩阵只有数量矩阵,$(\Delta_L,V)$ 没有非平凡共享对称。

**证明。** 设 $E_{k-1,k-1},E_{kk}\in\mathcal A_v$。则 $A_LE_{kk}A_L=(e_{k-1}+e_{k+1})(e_{k-1}+e_{k+1})^{\top}$。令 $Q=I-E_{k-1,k-1}\in\mathcal A_v$;因 $L\ge3$,$k+1\ne k-1$,故 $Qe_{k-1}=0$,$Qe_{k+1}=e_{k+1}$,从而

$$
QA_LE_{kk}A_LQ=E_{k+1,k+1}\in\mathcal A_v .
$$

从 $k=j+1$ 出发沿圈归纳,所有 $E_{kk}$ 都在 $\mathcal A_v$ 中。于是 $E_{kk}A_LE_{k+1,k+1}=E_{k,k+1}$ 与 $E_{k+1,k+1}A_LE_{kk}=E_{k+1,k}$ 都在 $\mathcal A_v$ 中,而任一矩阵单位 $E_{ik}$ 是沿圈从 $i$ 走到 $k$ 的这些相邻矩阵单位之积($i=k$ 时就是 $E_{kk}$)。所以 $\mathcal A_v=M_L(\mathbb R)$。与每个 $E_{ik}$ 可交换的复矩阵 $X$ 满足 $X_{ik}=X_{ii}\delta_{ik}$ 与 $X_{ii}=X_{kk}$,即为数量矩阵(母卷定理 4.6 证明的第一段);实正交的数量矩阵只有 $\pm I$。∎

**引理 5.2（路的谱与互素条件）。** 对 $\ell\ge1$,$J_\ell$ 的本征值是 $2\cos(\pi k/(\ell+1))$,$k=1,\dots,\ell$,两两不同。对 $\ell,\ell'\ge1$,$J_\ell$ 与 $J_{\ell'}$ 没有公共本征值,当且仅当 $\gcd(\ell+1,\ell'+1)=1$。

**证明。** 对 $1\le k\le\ell$ 令 $\varphi_i=\sin(\pi ki/(\ell+1))$,$i=0,\dots,\ell+1$,则 $\varphi_0=\varphi_{\ell+1}=0$,$\varphi_1\ne0$,且由和角公式 $\varphi_{i-1}+\varphi_{i+1}=2\cos(\pi k/(\ell+1))\varphi_i$。故 $(\varphi_1,\dots,\varphi_\ell)$ 是 $J_\ell$ 对 $2\cos(\pi k/(\ell+1))$ 的本征向量。余弦在 $(0,\pi)$ 上单射,这 $\ell$ 个值两两不同,因而是 $J_\ell$ 的全部本征值。

两组本征值相交,当且仅当存在 $1\le k\le\ell$、$1\le k'\le\ell'$ 使 $k/(\ell+1)=k'/(\ell'+1)$。若 $g=\gcd(\ell+1,\ell'+1)\ge2$,取 $k=(\ell+1)/g$、$k'=(\ell'+1)/g$,则 $1\le k\le(\ell+1)/2\le\ell$,同理 $1\le k'\le\ell'$,两组相交。若 $g=1$,由 $k(\ell'+1)=k'(\ell+1)$ 得 $(\ell+1)\mid k$,与 $1\le k\le\ell$ 矛盾。∎

**引理 5.3（游程投影）。** 设 $v$ 是两种值都出现的 $\pm1$ 势,$\varepsilon\in\{\pm1\}$,$\ell$ 是某个 $\varepsilon$-游程的长度,并设对每个长度 $\ell''\ne\ell$ 的 $\varepsilon$-游程都有 $\gcd(\ell+1,\ell''+1)=1$。令 $U$ 为全部长度为 $\ell$ 的 $\varepsilon$-游程之并。则 $P_U\in\mathcal A_v$。

**证明。** $P_\varepsilon=\tfrac12(I+\varepsilon V)\in\mathcal A_v$,故 $B_\varepsilon=P_\varepsilon A_LP_\varepsilon\in\mathcal A_v$;其 $(i,k)$ 元当 $v_i=v_k=\varepsilon$ 时等于 $(A_L)_{ik}$,否则为 $0$。一个长度为 $\ell_R$ 的游程 $R=\{i_0,i_0+1,\dots,i_0+\ell_R-1\}$ 满足 $\ell_R\le L-1$,圈上两端都在 $R$ 内的边恰是 $\{i_0+s,i_0+s+1\}$,$0\le s\le\ell_R-2$:边 $\{i_0+\ell_R-1,i_0\}$ 只在 $\ell_R-1\equiv\pm1\pmod L$ 时存在,即 $\ell_R=2$(此时它就是 $\{i_0,i_0+1\}$)或 $\ell_R=L$(已排除)。两个不同的 $\varepsilon$-游程之间没有边,否则由极大性它们是同一个游程。因此在适当排序下

$$
B_\varepsilon=\bigoplus_{R}J_{\ell_R}\ \oplus\ 0,
$$

其中 $R$ 跑遍 $\varepsilon$-游程,$0$ 作用在取值 $-\varepsilon$ 的站点上。令 $\Sigma$ 为 $J_\ell$ 的谱,$\Sigma'$ 为其余出现的 $\varepsilon$-游程长度 $\ell''$ 对应的 $J_{\ell''}$ 的谱之并;由引理 5.2 二者不交。取实系数插值多项式 $f$,在 $\Sigma$ 上取 $1$,在 $\Sigma'$ 上取 $0$。实对称矩阵可对角化,故 $f(J_\ell)=I$,$f(J_{\ell''})=0$,于是

$$
P_\varepsilon f(B_\varepsilon)=\bigoplus_{\ell_R=\ell}I\ \oplus\ \bigoplus_{\ell_R\ne\ell}0\ \oplus\ 0=P_U\in\mathcal A_v .
$$

这就是所求。∎

**定理 5.4（单边判据）。** 设 $v\in\{-1,1\}^L$,$L\ge3$,两种值都出现。设存在 $\varepsilon\in\{\pm1\}$ 与正整数 $\ell,\ell'$,使:$U$(长度为 $\ell$ 的 $\varepsilon$-游程之并)与 $U'$(长度为 $\ell'$ 的 $(-\varepsilon)$-游程之并)都非空;每个其他 $\varepsilon$-游程长度 $\ell''$ 满足 $\gcd(\ell+1,\ell''+1)=1$;每个其他 $(-\varepsilon)$-游程长度 $\ell'''$ 满足 $\gcd(\ell'+1,\ell'''+1)=1$;并且 $C_L$ 中恰有一条边一端在 $U$、另一端在 $U'$。则 $\mathcal A_v=M_L(\mathbb R)$,$(\Delta_L,V)$ 的共享交换子只含数量矩阵,没有非平凡共享对称。

**证明。** 由引理 5.3,$P_U,P_{U'}\in\mathcal A_v$。$U\cap U'=\varnothing$,故 $X=P_{U'}A_LP_U=\sum E_{i'i}$,和取遍一端 $i\in U$、另一端 $i'\in U'$ 的边;由假设 $X=E_{i'i}$,其中 $i'=i\pm1$。$A_L$ 与 $P$ 都对称,$X^{\top}=P_UA_LP_{U'}\in\mathcal A_v$,于是 $XX^{\top}=E_{i'i'}$ 与 $X^{\top}X=E_{ii}$ 都在 $\mathcal A_v$ 中。$i$ 与 $i'$ 相邻,由引理 5.1 得结论。∎

**命题 5.5（母卷两例满足单边判据）。** 母卷例 4.1 的势 $(1,1,1,1,-1,1,-1,-1)$($L=8$)与母卷定义 4.2 的势 $(1,1,-1,1,1,-1,1,-1,-1)$($L=9$)都满足定理 5.4 的假设,取 $\varepsilon=+1$、$\ell=1$、$\ell'=2$。因此二者的共享交换子都只含数量矩阵。

**证明。** $L=8$:$+$-游程为 $\{0,1,2,3\}$(长 4)与 $\{5\}$(长 1),$-$-游程为 $\{4\}$(长 1)与 $\{6,7\}$(长 2)。$\gcd(2,5)=1$,$\gcd(3,2)=1$。$U=\{5\}$,$U'=\{6,7\}$,连接二者的边只有 $\{5,6\}$:站点 $5$ 的另一邻居是 $4\notin U'$,站点 $7$ 的另一邻居是 $0\notin U$。$L=9$:$+$-游程为 $\{0,1\}$、$\{3,4\}$(长 2)与 $\{6\}$(长 1),$-$-游程为 $\{2\}$、$\{5\}$(长 1)与 $\{7,8\}$(长 2)。$\gcd(2,3)=1$。$U=\{6\}$,$U'=\{7,8\}$,连接二者的边只有 $\{6,7\}$:站点 $6$ 的另一邻居是 $5\notin U'$,站点 $8$ 的另一邻居是 $0\notin U$。由定理 5.4 得结论。∎

**注 5.6（与母卷的关系）。** 命题 5.5 对 $L=9$ 重新得到母卷定理 4.6,对 $L=8$ 给出母卷注 4.8 中只作记录、未在母卷中证明的交换子平凡性的一个证明。定理 5.4 是充分条件;第 8 章不讨论其必要性。也可以用 Burnside 定理(复数域上作用不可约的矩阵代数是全矩阵代数)代替引理 5.1 的直接构造,但那需要先证不可约性,本卷不用。

## 6. 缺陷块族与合数长度

**定义 6.1（缺陷块族 $U_{r,m}$）。** 对 $r\ge3$、$m\ge2$,令 $u_r=-+^{r-1}$,$u_r^{\sharp}=--+^{r-2}$(把 $u_r$ 的第 $1$ 个字母变号,字母从 $0$ 起编号),并令

$$
U_{r,m}=u_r^{\,m-1}\,u_r^{\sharp}\in\{-1,1\}^{rm},\qquad q_{r,m}=(m-1)r+1 .
$$

等价地,$(U_{r,m})_i=-1$ 当且仅当 $i\equiv0\pmod r$ 或 $i=q_{r,m}$。记 $\sigma_r=\sigma_{u_r}$。

**定理 6.2（$U_{r,m}$ 是无对称坏势）。** 设 $r\ge3$。

1. 对每个 $m\ge2$,$(\Delta_{rm},\operatorname{diag}(U_{r,m}))$ 的共享交换子只含数量矩阵,没有非平凡共享对称。
2. 对每个 $m\ge3$,$U_{r,m}$ 是坏势,在站点 $q_{r,m}$ 处有持续节点分支,且 $\Psi_m(\sigma_r)$ 的每个首一不可约因子都整除节点因子 $g_{q_{r,m}}$。

因此对一切 $r,m\ge3$,Lindblad 与 Guerrero 的逆问题(坏势是否必与 Laplace 算子共享非平凡对称)在 $C_{rm}$ 上有否定回答。

**证明。** 记 $L=rm$,$q=q_{r,m}$。取值 $-1$ 的站点是 $0,r,2r,\dots,(m-1)r$ 与 $q=(m-1)r+1$。

(1) 先确定游程。对 $0\le k\le m-2$,站点 $kr$ 的两个邻居都取 $+1$:$kr+1$ 不是 $r$ 的倍数($r\ge3$),也不等于 $q$($k\le m-2$);$kr-1$(对 $k=0$ 是 $L-1=(m-1)r+r-1$)模 $r$ 余 $r-1\ne0$,且不等于 $q$,因为 $q$ 模 $r$ 余 $1$ 而 $r-1\ne1$。故 $\{kr\}$ 是长 1 的 $-$-游程,共 $m-1$ 个。站点 $(m-1)r$ 与 $q$ 相邻且都取 $-1$;$(m-1)r-1$ 模 $r$ 余 $r-1$,取 $+1$;$q+1=(m-1)r+2\le L-1$(因 $r\ge3$),模 $r$ 余 $2\ne0$,取 $+1$。故 $U'=\{(m-1)r,\,q\}$ 是唯一一个长 2 的 $-$-游程,其余 $-$-游程长 1。相邻两个 $-$-游程之间是 $+$-游程:对 $0\le k\le m-2$,$\{kr+1,\dots,kr+r-1\}$ 长 $r-1$;从 $q+1$ 到 $L-1$ 的 $U=\{(m-1)r+2,\dots,mr-1\}$ 长 $r-2\ge1$。

取 $\varepsilon=+1$、$\ell=r-2$、$\ell'=2$。$U$ 是唯一一个长 $r-2$ 的 $+$-游程,其余 $+$-游程长 $r-1$,而 $\gcd(r-1,r)=1$;其余 $-$-游程长 $1$,$\gcd(3,2)=1$。连接 $U$ 与 $U'$ 的边:$U'$ 的两个外部邻居是 $(m-1)r-1$ 与 $q+1$,其中只有 $q+1$ 在 $U$ 中;$U$ 的两个外部邻居是 $q$ 与 $L\equiv0$,其中只有 $q$ 在 $U'$ 中。故恰有一条边 $\{q,q+1\}$。由定理 5.4 得 (1)。

(2) $U_{r,m}$ 与 $\tilde u_r$ 只在 $q$ 处不同($\tilde u_r$ 在 $q$ 处为 $+1$),由推论 4.4($s=1$)或定理 4.3 得 (2)。

最后,(1) 说明 $U_{r,m}$ 不与 $\Delta_{rm}$ 共享任何非平凡正交对称,(2) 说明它是坏势。∎

**引理 6.3（可分解长度）。** 对整数 $L\ge3$,存在整数 $r,m\ge3$ 使 $L=rm$,当且仅当 $L$ 不是素数、不是素数的两倍、也不等于 $8$。

**证明。** 若 $L=rm$,$r,m\ge3$,则 $L$ 是合数;若 $L=2p$,$p$ 为素数,则 $L$ 的因子只有 $1,2,p,2p$,不存在两个都 $\ge3$ 的因子之积等于 $L$;$8$ 的因子是 $1,2,4,8$,同理。反之设 $L$ 不属于这三类。若 $L$ 有奇素因子 $p$ 且 $L/p\ge3$,取 $(r,m)=(L/p,p)$。若 $L$ 的每个奇素因子 $p$ 都有 $L/p\le2$,则 $L\in\{p,2p\}$,已排除;若 $L$ 没有奇素因子,则 $L=2^e$,$e\ge2$;$e=2$ 时 $L=4=2\cdot2$ 已排除,$e=3$ 已排除,$e\ge4$ 时取 $(r,m)=(4,2^{e-2})$。∎

**定理 6.4（每个既非素数也非素数两倍的长度都有无对称坏势）。** 设 $L\ge3$ 既不是素数,也不是素数的两倍。则 $C_L$ 上存在 $\pm1$ 势,它是坏势,且与 $\Delta_L$ 的共享交换子只含数量矩阵。

**证明。** 若 $L\ne8$,由引理 6.3 写 $L=rm$,$r,m\ge3$,取 $U_{r,m}$,用定理 6.2。若 $L=8$,取母卷例 4.1 的势:母卷例 4.1 证明了它在站点 $1$ 处对一切实数 $t$ 有在该处为零的本征向量,故它是坏势;命题 5.5 给出交换子平凡。∎

**定理 6.5（$r=3$ 子族的节点因子）。** 设 $m\ge3$,$q=3m-2$。在约定 2.2 的坐标 $a,b$ 中 $\sigma_3=a^2b-2a-b$。对每个 $0<k<m/2$,多项式 $\sigma_3-2\cos(2\pi k/m)$ 在 $\mathbb R(t)[\lambda]$ 中不可约,且不同 $k$ 给出的多项式两两不相伴。因此 $\Psi_m(\sigma_3)$ 在 $\mathbb R(t)[\lambda]$ 中无平方因子,

$$
\Psi_m(\sigma_3)=\prod_{0<k<m/2}\bigl(\sigma_3-2\cos(2\pi k/m)\bigr)
$$

是它的不可约分解,并且 $(-1)^{\lfloor(m-1)/2\rfloor}\Psi_m(\sigma_3)$(关于 $\lambda$ 首一)在 $\mathbb R[t][\lambda]$ 中整除 $U_{3,m}$ 在 $q$ 处的节点因子 $g_q$。$m=3$ 时 $-\Psi_3(\sigma_3)=-(\sigma_3+1)$ 就是母卷定义 4.2 的三次式 $c$。

**证明。** $u_3=-++$,$B_{u_3}=T(a)T(a)T(b)$。对任意 $x,y,z$,

$$
T(y)T(z)=\begin{pmatrix}yz-1&-y\\ z&-1\end{pmatrix},\qquad \operatorname{tr}\bigl(T(x)T(y)T(z)\bigr)=x(yz-1)-z-y=xyz-x-y-z,
$$

取 $x=y=a$、$z=b$ 得 $\sigma_3=a^2b-2a-b$。

固定 $c=2\cos\theta$,$\theta=2\pi k/m\in(0,\pi)$,则 $\sigma_3-c=(a^2-1)\,b-(2a+c)$ 关于 $b$ 是一次的。若它在 $\mathbb R[a,b]$ 中分解为两个非常数因子,其中一个因子 $f(a)$ 不含 $b$ 且次数为正,并同时整除 $a^2-1$ 与 $2a+c$。$2a+c$ 的唯一根是 $-c/2=-\cos\theta$,而 $\cos^2\theta-1=-\sin^2\theta\ne0$,矛盾。故 $\sigma_3-c$ 在 $\mathbb R[a,b]$ 中不可约。变量替换 $a=2-\lambda+t$、$b=2-\lambda-t$ 是 $\mathbb R^2$ 上可逆的仿射变换,故 $\sigma_3-c$ 在 $\mathbb R[\lambda,t]$ 中不可约;它关于 $\lambda$ 的首项系数是 $-1$(来自 $a^2b$ 的 $(-\lambda)^3$),从而在 $\mathbb R[t]$ 上本原,由 Gauss 引理在 $\mathbb R(t)[\lambda]$ 中不可约。若 $\sigma_3-c=\kappa(\sigma_3-c')$,$\kappa\in\mathbb R(t)^{\times}$,比较 $\lambda^3$ 的系数得 $\kappa=1$,于是 $c=c'$;故不同的 $k$ 给出两两不相伴的不可约因子。

由定理 6.2 (2),每个 $-(\sigma_3-2\cos(2\pi k/m))$(首一)都整除 $g_q$。它们两两互素,$\mathbb R(t)[\lambda]$ 是唯一分解整环,故其乘积 $(-1)^{\lfloor(m-1)/2\rfloor}\Psi_m(\sigma_3)$ 整除 $g_q$。二者都关于 $\lambda$ 首一且系数在 $\mathbb R[t]$ 中,用首一多项式作带余除法不离开 $\mathbb R[t][\lambda]$,故商也在 $\mathbb R[t][\lambda]$ 中。$m=3$ 时 $\Psi_3(\sigma_3)=a^2b-2a-b+1$,即母卷引理 4.3 中的 $k(a,b)$,而母卷引理 4.3 给出 $c=-k$。∎

**注 6.6（与母卷九圈例的对应）。** $U_{3,3}=-++-++--+$。设 $v$ 为母卷定义 4.2 的势,则对一切 $i$ 有 $(U_{3,3})_i=v_{5-i}$:$U_{3,3}$ 是母卷九圈势在反射 $i\mapsto5-i$ 下的像。该反射把 $U_{3,3}$ 的缺陷站点 $q_{3,3}=7$ 映到 $5-7\equiv7$,与母卷定理 4.4 的节点站点 $7$ 一致。因此母卷定理 4.4 与 4.6 是定理 6.2 在 $(r,m)=(3,3)$ 时的情形,定理 6.5 在 $m=3$ 时还原母卷引理 4.3 的三次式。逐项核对:$v=(1,1,-1,1,1,-1,1,-1,-1)$,$v_{5-i}$ 依 $i=0,\dots,8$ 依次为 $v_5,v_4,v_3,v_2,v_1,v_0,v_8,v_7,v_6=-1,1,1,-1,1,1,-1,-1,1$。

**命题 6.7（十二圈上的显式节点本征向量）。** 在 $C_{12}$ 上取 $U_{3,4}=-++-++-++--+$,$a,b$ 如约定 2.2,$\sigma_3=a^2b-2a-b$。令

$$
z=\bigl(a,\ ab-1,\ b,\ 1,\ 0,\ -1,\ -a,\ 1-ab,\ -b,\ -1,\ 0,\ 1\bigr)\in\mathbb R[a,b]^{12},
$$

即 $z_{i+6}=-z_i$。则对任意 $(\lambda,t)$,

$$
(H_t-\lambda I)\,z=\sigma_3\,(e_1-e_7).
$$

因此对每个实数 $t$ 与 $\sigma_3(\cdot,t)$ 的每个实根 $\lambda$(这样的根存在),$z$ 是 $H_t$ 的本征向量,并且同时在站点 $4$ 与 $10$ 处为零。结合定理 6.2 (1),$U_{3,4}$ 是 $C_{12}$ 上与 $\Delta_{12}$ 不共享非平凡对称的坏势。

**证明。** 字母依次为 $d=(b,a,a,b,a,a,b,a,a,b,b,a)$。逐站点计算残差 $r_i=d_iz_i-z_{i-1}-z_{i+1}$:

$$
\begin{aligned}
r_0&=ba-1-(ab-1)=0, & r_1&=a(ab-1)-a-b=\sigma_3, & r_2&=ab-(ab-1)-1=0,\\
r_3&=b-b-0=0, & r_4&=0-1+1=0, & r_5&=-a-0+a=0,\\
r_6&=-ab+1-(1-ab)=0, & r_7&=a(1-ab)+a+b=-\sigma_3, & r_8&=-ab-(1-ab)+1=0,\\
r_9&=-b+b-0=0, & r_{10}&=0+1-1=0, & r_{11}&=a-0-a=0 .
\end{aligned}
$$

这给出所述恒等式。固定实数 $t$,$\sigma_3(\cdot,t)$ 是 $\lambda$ 的三次实多项式(首项系数 $-1$),有实根;在该根处 $(H_t-\lambda I)z=0$,而 $z_3=1$,故 $z$ 是在站点 $4$ 与 $10$ 处为零的实本征向量。由母卷约定 2.4 与母卷推论 3.3 证明的第一段,势是坏势;共享交换子平凡由定理 6.2 (1)。∎

**注 6.8（与定理 4.3、4.6 的一致性）。** 命题 6.7 是定理 4.6 在 $(r,m,j)=(3,4,1)$ 时的显式形式:$\Psi_4(\sigma_3)=\sigma_3$,$\gcd(4,2)=2$,$Q=\{10,4\}$。按定理 4.6,还可以在站点 $4$ 处任意改动势值而保留这条节点分支。

**命题 6.9（块迹的 Chebyshev 闭式）。** 对 $r\ge1$,块 $-+^{r-1}=(-1,1,\dots,1)\in\{-1,1\}^r$ 的块迹是

$$
\sigma_{-+^{r-1}}=b\,S_{r-1}(a)-2\,S_{r-2}(a).
$$

因此对 $r,m\ge3$,多项式 $\Psi_m\bigl(bS_{r-1}(a)-2S_{r-2}(a)\bigr)$ 的每个首一不可约因子都整除 $U_{r,m}$ 在 $q_{r,m}$ 处的节点因子。例如 $\sigma_3=b(a^2-1)-2a$,$\sigma_4=b(a^3-2a)-2(a^2-1)$。

**证明。** 由约定 2.3,该块的转移矩阵是 $T(a)^{r-1}T(b)$。$T(a)$ 的行列式为 $1$、迹为 $a$,由引理 4.1,$T(a)^{r-1}=S_{r-2}(a)T(a)-S_{r-3}(a)I$(对 $r\ge1$ 成立,$r=1$ 时右边为 $0\cdot T(a)+I$)。又 $\operatorname{tr}T(b)=b$,$\operatorname{tr}(T(a)T(b))=ab-2$。于是

$$
\sigma_{-+^{r-1}}=S_{r-2}(a)(ab-2)-S_{r-3}(a)\,b=b\bigl(aS_{r-2}(a)-S_{r-3}(a)\bigr)-2S_{r-2}(a)=bS_{r-1}(a)-2S_{r-2}(a),
$$

最后一步是约定 2.4 的递推。第二句由定理 6.2 (2)。∎

## 7. 小长度与精确节点因子

**引理 7.1（有理耦合证书）。** 设 $v\in\mathbb R^L$,$L\ge3$。若对每个站点 $j$ 都存在实数 $t_j$,使 $p(\cdot,t_j)$ 与 $q_j(\cdot,t_j)$ 在 $\mathbb R[\lambda]$ 中互素,则 $v$ 是好势。并且好坏性与二面体稳定子是否平凡,在二面体重标号 $v\mapsto v\circ\pi$($\pi\in D_L$)与变号 $v\mapsto-v$ 下都不变。

**证明。** $p$ 与 $q_j$ 关于 $\lambda$ 首一,结式与取值 $t=t_j$ 可交换:$\operatorname{Res}_\lambda(p,q_j)(t_j)=\operatorname{Res}_\lambda(p(\cdot,t_j),q_j(\cdot,t_j))$,右边非零,因为互素的两个多项式没有公共复根。故每个 $\operatorname{Res}_\lambda(p,q_j)$ 都不是零多项式,由母卷推论 3.3,$v$ 是好势。设 $\Pi$ 是 $\pi\in D_L$ 的置换矩阵,则 $\Pi$ 与 $A_L$ 可交换,$H_t(v\circ\pi)$ 与 $H_t(v)$ 经 $\Pi$ 共轭,本征值相同、本征向量只差坐标置换;又 $H_t(-v)=H_{-t}(v)$,而「除有限个 $t$ 外」的条件在 $t\mapsto-t$ 下不变。$v\circ\pi$ 的稳定子是 $v$ 的稳定子的共轭,$-v$ 的稳定子与 $v$ 的相同。∎

**命题 7.2（长度 4）。** $C_4$ 上每个 $\pm1$ 势都有非平凡二面体稳定子,因而与 $\Delta_4$ 共享非平凡对称。特别地 $C_4$ 上没有与 Laplace 算子不共享非平凡对称的坏 $\pm1$ 势。

**证明。** 由引理 7.1 的变号不变性,可设取值 $-1$ 的站点集 $N$ 至多两个元素。$N=\varnothing$ 时旋转 $i\mapsto i+1$ 固定 $v$;$N=\{n\}$ 时反射 $i\mapsto2n-i$ 固定 $v$;$N=\{n,n'\}$ 时反射 $i\mapsto n+n'-i$ 交换 $n,n'$,固定 $v$。这些都是 $D_4$ 的非单位元,其置换矩阵不等于 $I$,且元素非负故不等于 $-I$;它与 $A_4$、$V$ 都可交换,是非平凡共享对称。∎

**命题 7.3（长度 6 的无对称势只有一类）。** $C_6$ 上二面体稳定子平凡的 $\pm1$ 势,恰是 $U_{3,2}=-++--+$ 在 $D_6$ 作用下的 $12$ 个像;它们都恰有三个站点取 $-1$,且这一集合在变号下封闭。

**证明。** 记 $N$ 为取值 $-1$ 的站点集,$k=|N|$。变号把 $N$ 换成补集,不改变稳定子,故先设 $k\le3$。$k\le2$ 时命题 7.2 证明中的同样三种旋转或反射(把 $4$ 换成 $6$)固定 $v$。$k=3$ 时,按循环顺序列出 $N$ 的三个元素,相邻元素之间的距离构成正整数的循环间隔序列,三项之和为 $6$;在循环轮换意义下只有 $(2,2,2)$、$(1,1,4)$、$(1,2,3)$、$(1,3,2)$ 四种。$(2,2,2)$ 时旋转 $i\mapsto i+2$ 固定 $N$;$(1,1,4)$ 时 $N=\{n-1,n,n+1\}$,反射 $i\mapsto2n-i$ 固定 $N$。保持 $N$ 的二面体元素把 $N$ 双射到自身并保持距离,旋转保持循环顺序,反射反转循环顺序;非单位的旋转没有不动点,所以若 $N$ 被非单位的旋转保持,它在 $N$ 上诱导非平凡的循环移位,间隔序列在某个非平凡循环轮换下不变,三项必须相等;若 $N$ 被反射保持,间隔序列的反序在循环轮换意义下等于自身。$(1,2,3)$ 的三项互不相同,反序 $(3,2,1)$ 的循环轮换是 $(3,2,1)$、$(2,1,3)$、$(1,3,2)$,都不是 $(1,2,3)$;$(1,3,2)$ 同理。故后两种的稳定子平凡。间隔类型为 $(1,2,3)$ 的集合是 $\{n,n+1,n+3\}$,共 $6$ 个,彼此差一个旋转;反射 $i\mapsto-i$ 把它们变成间隔类型 $(1,3,2)$ 的 $6$ 个集合。$U_{3,2}$ 的 $N=\{0,3,4\}$ 的间隔序列是 $(3,1,2)$,属于类型 $(1,2,3)$。$k>3$ 的情形经变号化为 $k<3$,其稳定子非平凡;$k=3$ 时补集仍有三个元素,故这 $12$ 个势构成的集合在变号下封闭。∎

**命题 7.4（长度 6、10、14 无此类坏势）。** 对 $L\in\{6,10,14\}$,$C_L$ 上每个二面体稳定子平凡的 $\pm1$ 势都是好势。因此在这三个长度上,不存在与 $\Delta_L$ 不共享非平凡对称的坏 $\pm1$ 势。本命题依赖第 10 章的有限精确核验。

**证明。** 第 10 章的代码对 $L\in\{6,10,14\}$ 枚举 $\{-1,1\}^L$,在 $D_L$ 作用与变号生成的群的每个轨道中取一个代表,只保留 $D_L$-轨道长为 $2L$(即稳定子平凡)的代表,并对每个这样的代表 $v$ 与每个站点 $j$,在正整数 $t_0\le29$ 中找到一个,使 $p(\cdot,t_0)$ 与 $q_j(\cdot,t_0)$ 在 $\mathbb Q[\lambda]$ 中的 Euclid 算法终止于非零常数。$p$ 与 $q_j$ 用引理 3.2 的公式 $p=(-1)^L(\operatorname{tr}M_j-2)$、$q_j=(-1)^{L-1}K_{L-1}(d_{j+1},\dots,d_{j+L-1})$ 以有理数精确计算;$\mathbb Q[\lambda]$ 中互素蕴含 $\mathbb R[\lambda]$ 中互素。代码断言每个代表都找到了证书。由引理 7.1,这些代表都是好势,并且同一轨道中的势也是好势,稳定子也平凡。

若 $v$ 是坏势且与 $\Delta_L$ 不共享非平凡对称,则 $v$ 的二面体稳定子平凡:否则稳定子中非单位元的置换矩阵 $\Pi$ 满足 $\Pi\ne I$,$\Pi\ne-I$,且与 $A_L$、$V$ 可交换,是非平凡共享对称。于是 $v$ 落在某个已证为好势的轨道中,矛盾。∎

**命题 7.5（族 $U_{r,m}$ 节点因子的精确形,$r\le8$、$m\le12$）。** 设 $3\le r\le8$,$3\le m\le12$,$q=q_{r,m}$。则 $U_{r,m}$ 在 $q$ 处的节点因子是

$$
g_q=(-1)^{r\lfloor(m-1)/2\rfloor}\,\Psi_m(\sigma_r),
$$

其 $\lambda$-次数为 $r\lfloor(m-1)/2\rfloor$。$r=3$ 时它就是定理 6.5 中的乘积。本命题依赖第 10 章的有限精确核验。

**证明。** 记 $N=r\lfloor(m-1)/2\rfloor$。由命题 4.9(取 $u=u_r$,$w=U_{r,m}$),$(-1)^N\Psi_m(\sigma_r)$ 是 $g_q$ 的首一因子,$\lambda$-次数为 $N$(定理 4.3 (1))。另一方面 $g_q$ 首一、系数在 $\mathbb R[t]$ 中,并在 $\mathbb R[t][\lambda]$ 中整除 $p$ 与 $q_q$;代入 $t=1/3$ 后仍首一、次数不变,并整除 $p(\cdot,1/3)$ 与 $q_q(\cdot,1/3)$ 的最大公因式。第 10 章的代码对每个 $(r,m)$ 以有理数精确计算该最大公因式,断言其次数为 $N$,故 $\deg_\lambda g_q\le N$。两个首一多项式一个整除另一个且次数相同,故相等。∎

**定理 7.6（$3\le L\le21$ 的完整回答）。** 设 $3\le L\le21$。$C_L$ 上存在与 $\Delta_L$ 不共享非平凡对称的坏 $\pm1$ 势,当且仅当 $L$ 既不是素数也不是素数的两倍,即 $L\in\{8,9,12,15,16,18,20,21\}$。本定理对 $L\in\{6,10,14\}$ 的部分依赖第 10 章的有限精确核验。

**证明。** 充分性是定理 6.4。必要性:若 $L$ 是素数,由 Lindblad 与 Guerrero 的命题 4.1($d=1$、$L$ 为素数时,势是坏势当且仅当它关于某个顶点反射对称),每个坏势都有顶点反射这一非平凡共享对称。若 $L$ 是素数的两倍且 $L\le21$,则 $L\in\{4,6,10,14\}$,由命题 7.2 与命题 7.4 不存在此类势。在 $3\le L\le21$ 中去掉素数 $3,5,7,11,13,17,19$ 与 $4,6,10,14$,余下的正是所列八个长度。∎

## 8. 反例与不能推广的边界

**命题 8.1（$m\ge3$ 不能去掉）。** $U_{3,2}=-++--+$ 的共享交换子只含数量矩阵,但它是好势。所以定理 6.2 (2) 中的条件 $m\ge3$ 不能放宽为 $m\ge2$;这与 $\Psi_2=1$ 一致。本命题的好势部分依赖第 10 章的有限精确核验。

**证明。** 交换子平凡是定理 6.2 (1) 在 $(r,m)=(3,2)$ 时的情形。由命题 7.3,$U_{3,2}$ 的二面体稳定子平凡,由命题 7.4,它是好势。∎

**命题 8.2（周期不超过 2 的块只给出对称势）。** 设 $r\in\{1,2\}$,$r\mid L$,$L\ge3$,$\tilde u$ 是周期为 $r$ 的势,$w$ 至多在站点 $q$ 处与 $\tilde u$ 不同。则反射 $\rho_q:i\mapsto2q-i$ 是 $w$ 的非平凡二面体对称。因此推论 4.4 在 $r\le2$ 时得到的坏势都与 Laplace 算子共享非平凡对称。

**证明。** $L$ 是 $r$ 的倍数,故 $i\bmod r$ 在 $\mathbb Z/L\mathbb Z$ 上有定义;$2q-i\equiv i\pmod 2$,而 $r\mid2$,故 $\tilde u_{\rho_q(i)}=\tilde u_i$。$\rho_q$ 固定 $q$,故也保持 $w$。因 $L\ge3$,$\rho_q(q+1)=q-1\ne q+1$,$\rho_q$ 不是单位元,其置换矩阵是非平凡共享对称。∎

**命题 8.3（缺陷位置不能任意选）。** 设 $m\ge3$,$w=(-++)^{m-1}(+++)$ 是把 $u_3$ 的第 $0$ 个字母变号所得的单字母缺陷字。则 $w$ 是坏势,但反射 $i\mapsto3(m-2)-i$ 是它的非平凡二面体对称。

**证明。** 坏势由推论 4.4($s=0$)。$w$ 取 $-1$ 的站点集是 $\{0,3,\dots,3(m-2)\}$,反射 $i\mapsto3(m-2)-i$ 把 $3k$ 映到 $3(m-2-k)$,保持该集合;它把 $1$ 映到 $3m-7\ne1$(因 $3m-8$ 不是 $3m$ 的倍数),不是单位元。∎

**命题 8.4（族 $U_{r,m}$ 不穷尽无对称坏势）。** 母卷例 4.1 的势 $v_8=(1,1,1,1,-1,1,-1,-1)$ 不是任何满足 $m\ge3$ 的单点缺陷字 $u^{m-1}u^{\sharp}$(推论 4.4 的形式),也不是定理 4.6 中任何 $m\ge3$ 的周期势在站点集 $Q$ 上的修改;但母卷例 4.1 在站点 $1$ 处给出的节点多项式 $g$(它整除节点因子 $g_1$)等于 $\Psi_4(\sigma_{+-})$:

$$
\lambda^2-4\lambda+2-t^2=ab-2=\operatorname{tr}\bigl(T(b)T(a)\bigr)=\Psi_4(\sigma_{+-}).
$$

**证明。** 若 $v_8=u^{m-1}u^{\sharp}$ 且 $8=rm$、$m\ge3$,则 $r\in\{1,2\}$,由命题 8.2 $v_8$ 有非平凡二面体对称,与命题 5.5 的交换子平凡矛盾。再看定理 4.6 的形式:$8=rm$、$m\ge3$ 同样迫使 $r\in\{1,2\}$,周期势只有常数 $\pm1$ 与 $\pm(+-)^4$ 四个;$v_8$ 与它们取值不同的站点集分别是 $\{4,6,7\}$($+1$)、$\{0,1,2,3,5\}$($-1$)、$\{1,3,4,5,6\}$($+-+-+-+-$)、$\{0,2,7\}$($-+-+-+-+$)。定理 4.6 的 $Q$ 是步长 $er$ 的陪集,$|Q|=\gcd(m,2j)$:$r=2$ 时 $m=4$、$j=1$,$Q$ 有 $2$ 个元素;$r=1$ 时 $m=8$,$j\in\{1,2,3\}$,$Q$ 有 $2$、$4$、$2$ 个元素,步长分别为 $4$、$2$、$4$。五元集放不进至多四元的 $Q$;三元集 $\{4,6,7\}$ 与 $\{0,2,7\}$ 同时含奇偶站点,放不进步长为偶数的陪集。故 $v_8$ 不是这种修改。等式部分:$\operatorname{tr}(T(x)T(y))=xy-2$,$ab=(2-\lambda)^2-t^2$,故 $ab-2=\lambda^2-4\lambda+2-t^2$,这正是母卷例 4.1 的 $g$;而 $\Psi_4(x)=x$。母卷例 4.1 证明了 $g$ 整除 $p$ 与 $q_1$,故 $g\mid g_1$;本命题不断言 $g=g_1$。∎

**开放问题 8.5（长度 $2p$）。** 对素数 $p\ge11$,$C_{2p}$ 上是否存在与 $\Delta_{2p}$ 不共享非平凡对称的坏 $\pm1$ 势?本卷的构造到不了这些长度:推论 4.4 需要 $L=rm$ 且 $m\ge3$;在 $L=2p$ 时只能 $r\in\{1,2\}$,由命题 8.2 得到的都是对称势;$r=p$、$m=2$ 时 $\Psi_2=1$,定理 4.3 不给出节点分支。定理 7.6 对 $p\le7$ 给出否定回答,但它依赖逐个长度的有限证书,不提供对一般 $p$ 的论证。缺的是一个对 $L=2p$ 的结构性障碍,例如把 Lindblad 与 Guerrero 对素数长度的单位根论证推广到 $2p$ 次单位根。

**开放问题 8.6（节点因子的精确形与其他节点站点）。** 命题 7.5 只覆盖 $3\le r\le8$、$3\le m\le12$。对一般的 $r,m\ge3$,$U_{r,m}$ 在 $q_{r,m}$ 处的节点因子是否等于 $\pm\Psi_m(\sigma_r)$(命题 4.9 只给出整除),以及 $r\ge4$ 时 $\sigma_r-2\cos(2\pi k/m)$ 在 $\mathbb R(t)[\lambda]$ 中的不可约分解,本卷均未证明;缺的是节点因子次数的一般上界。$U_{r,m}$ 在缺陷站点以外的持续节点分支,本卷只知道定理 4.6 给出的同余站点(例如命题 6.7 中的站点 $4$),其余站点未研究。

**开放问题 8.7（节点因子的一般描述）。** 命题 8.4 表明,无对称坏势的节点因子可以含 Chebyshev 形的因子 $\Psi_4(\sigma_{+-})$,而势本身既不是周期势的单点修改,也不是定理 4.6 意义下的同余多点修改。产生这一因子的机制是什么?是否每个坏 $\pm1$ 势在某个站点处的节点因子都含有某个块迹 $\sigma_u$ 的 $\Psi_m(\sigma_u)$ 的不可约因子?这是母卷开放问题 6.3 在本卷之后的剩余部分。

## 9. 来源、文献状态与核验边界

**文献表态(CLAUDE.md 第 3.7 条,每条命题只取一个值)。**

| 来源 | 精确范围与使用边界 |
| --- | --- |
| O. Lindblad, E. Guerrero, *Simple Eigenvalues and Non-vanishing Eigenvectors of the Anderson Model*, arXiv:2512.00278v1,§1(算子与定义 1.1、定理 1.3 之后的逆问题)、命题 2.3、引理 3.2、命题 4.1 | `literature-attested`:算子 $H_t=\Delta+tV$、好势与坏势的定义与二分(经母卷推论 3.3 使用)、逆问题的提法,以及命题 4.1:$d=1$ 且 $L$ 为素数时,势(对实值势陈述)是坏势当且仅当它关于某个顶点反射对称;后者用于定理 7.6 的素数长度部分。核对 v1 的 HTML 全文:该文不讨论合数长度,不使用转移矩阵或单点缺陷,也未给出无对称坏势。 |
| 母卷 `docs/develop/theory/CYCLE_ANDERSON_PERSISTENT_NODAL_BRANCHES.md`:约定 2.1–2.5、定理 3.2、推论 3.3、例 4.1、定义 4.2、引理 4.3、定理 4.4、4.6 | 本仓既有卷,作为输入引用,不在本卷重新表态;其各条的文献表态见母卷第 8 章。 |
| G. Teschl, *Jacobi Operators and Completely Integrable Nonlinear Lattices*, Math. Surveys Monogr. 72, AMS 2000,第 7 章(周期 Jacobi 算子、Floquet 判别式、Bloch 解) | `literature-attested`:引理 3.2 (2) 与 $p=(-1)^L(\operatorname{tr}M_j-2)$ 是 Floquet 判别式的有限圈形式;注 4.5 所说周期算子在 Bloch 相位 $2\pi k/m$($0<k<m/2$)处的二重简并;引理 4.8 是「Floquet 判别式在带内的根都是单根」的有限形式。式号定位未核;本卷对引理 3.2 写出了完整证明,不依赖该书。 |
| R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd ed., Addison-Wesley 1994,§6.7(continuants) | `literature-attested`:引理 3.2 (1) 的连分式行列式递推与 $2\times2$ 矩阵积表示。 |
| J. C. Mason, D. C. Handscomb, *Chebyshev Polynomials*, Chapman & Hall/CRC 2003,第 1 章 | `literature-attested`:$S_n(2\cos\theta)\sin\theta=\sin((n+1)\theta)$(第二类 Chebyshev 多项式的变量缩放),用于命题 4.2 与约定 2.4;引理 4.1 的幂公式是 Cayley–Hamilton 定理的标准推论,小节定位未核。 |
| A. E. Brouwer, W. H. Haemers, *Spectra of Graphs*, Springer 2012,§1.4(路的谱) | `literature-attested`:路 $J_\ell$ 的谱为 $2\cos(\pi k/(\ell+1))$,即引理 5.2 的第一句;小节定位未核。引理 5.2 的互素判据是本卷的初等推论。 |
| S. Lang, *Algebra*, rev. 3rd ed., Springer 2002,第 IV 章 §2(Gauss 引理)与 §8(结式) | `literature-attested`:Gauss 引理与首一多项式结式的取值交换性,用于命题 4.2 (1)、定理 6.5、引理 7.1。 |
| — | `literature-attested`:引理 3.2、注 3.3、引理 4.1、引理 4.8。 |
| — | `repo-derived`:定义 3.1、引理 3.4(母卷节点步在任意域上的形式)、定理 3.6、注 3.5、注 3.7、命题 4.2、推论 4.4、注 4.5、注 4.7、命题 4.9、引理 5.1、引理 5.2、引理 5.3、定理 5.4、命题 5.5、注 5.6、定义 6.1、引理 6.3、定理 6.5、注 6.6、命题 6.7、注 6.8、命题 6.9、引理 7.1、命题 7.2、命题 7.3、命题 7.5、命题 8.1–8.4。 |
| — | `suspected-novel`:定理 4.3(单点缺陷原理)、定理 4.6(同余站点上的多点缺陷)、定理 6.2(族 $U_{r,m}$)、定理 6.4(既非素数也非素数两倍的长度)、命题 7.4、定理 7.6。检索范围:arXiv:2512.00278v1 的 HTML 全文;母卷第 8 章所列检索;以「bad potential」「Anderson model」「cycle」「symmetry」「converse」「composite length」组合的网络检索;latent symmetry 与 cospectral vertices 文献,包括 D. Smith, B. Webb, *Hidden symmetries in real and theoretical networks*, Physica A 514 (2019) 855–867(arXiv:1803.02328)、M. Röntgen 等, *Latent symmetry induced degeneracies*(arXiv:2011.13404)、M. Kempton, J. Sinkovic, D. Smith, B. Webb, *Characterizing cospectral vertices via isospectral reduction*, Linear Algebra Appl. 594 (2020) 226–248(仅核到书目信息)。这些文献讨论固定矩阵的隐藏对称与本征向量分量的消失,检索范围内未见对单参数族 $\Delta+tV$ 的持续节点分支、周期势单点缺陷或合数长度逆问题的处理。这不确立检索范围之外的优先权。 |

**核验边界。** 第 10 章的代码是本卷唯一的代码块,输入固定,只做两件事:(i) 对 $L\in\{4,6,10,14\}$,枚举 $\{-1,1\}^L$ 在二面体作用与变号下的轨道代表,对稳定子平凡的每个代表与每个站点,在正整数 $t_0\le29$ 中寻找使 $p(\cdot,t_0)$ 与 $q_j(\cdot,t_0)$ 在 $\mathbb Q[\lambda]$ 中互素的证书,并断言全部找到;它打印各长度的轨道总数与稳定子平凡的轨道数,读数为 $L=4$:$4$ 与 $0$;$L=6$:$8$ 与 $1$;$L=10$:$44$ 与 $18$;$L=14$:$362$ 与 $261$。(ii) 对 $3\le r\le8$、$3\le m\le12$,在 $t=1/3$ 处计算 $U_{r,m}$ 的 $p$ 与 $q_{q_{r,m}}$ 的最大公因式次数,断言等于 $r\lfloor(m-1)/2\rfloor$;同时断言 $\Psi_m(\sigma_r(\cdot,1/3))$ 与其导数互素,这一项只是命题 4.9 在 $t=1/3$ 处的一致性核对,不被任何证明使用。全部算术用 Python 标准库的有理数,末行打印哨兵 `ALL_FINITE_CHECKS_PASSED`。

依赖该代码的命题恰为:命题 7.4、命题 7.5、定理 7.6 中 $L\in\{6,10,14\}$ 的部分、命题 8.1 中好势的部分。第 3–6 章(含命题 6.7 的逐站点核对)与命题 7.2、7.3 不依赖任何计算。代码不覆盖:$L\ge22$ 的长度(特别是 $L=2p$,$p\ge11$);$r\ge9$ 或 $m\ge13$ 时 $U_{r,m}$ 节点因子的精确形。有限运行不证明任何关于一般 $L$ 或一般 $m$ 的全称命题。

## 10. 有限精确核验

下面的代码只用 Python 标准库,输入固定。

```python
from fractions import Fraction as Fr


def trim(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def pmul(p, q):
    if not p or not q:
        return []
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return trim(r)


def prem(p, q):
    p = list(p)
    while len(p) >= len(q) and p:
        c, k = p[-1] / q[-1], len(p) - len(q)
        for i, y in enumerate(q):
            p[i + k] -= c * y
        trim(p)
    return p


def pgcd_deg(p, q):
    p, q = trim(list(p)), trim(list(q))
    while q:
        p, q = q, prem(p, q)
    return len(p) - 1


def letter(vi, t):
    # d_i = 2 + t v_i - lam as a polynomial in lam
    return [Fr(2) + t * vi, Fr(-1)]


def transfer(ds):
    # product T(d_{n-1}) ... T(d_0) with T(d) = [[d, -1], [1, 0]]
    m = [[[Fr(1)], []], [[], [Fr(1)]]]
    for d in ds:
        m = [[padd(pmul(d, m[0][j]), [-c for c in m[1][j]]), m[0][j]] for j in range(2)]
        m = [[m[0][0], m[1][0]], [m[0][1], m[1][1]]]
    return m


def p_and_q(v, t, j):
    n = len(v)
    ds = [letter(v[(j + 1 + k) % n], t) for k in range(n)]
    path = transfer(ds[:-1])
    full = transfer(ds)
    q = path[0][0] if (n - 1) % 2 == 0 else [-c for c in path[0][0]]
    tr = padd(padd(full[0][0], full[1][1]), [Fr(-2)])
    p = tr if n % 2 == 0 else [-c for c in tr]
    return p, q


def dihedral_images(v):
    n = len(v)
    out = []
    for s in range(n):
        out.append(tuple(v[(i + s) % n] for i in range(n)))
        out.append(tuple(v[(s - i) % n] for i in range(n)))
    return out


def certify_length(n):
    seen, asym, certified = set(), 0, 0
    for bits in range(2 ** n):
        v = tuple(1 if (bits >> i) & 1 else -1 for i in range(n))
        imgs = dihedral_images(v)
        key = min(imgs + [tuple(-x for x in w) for w in imgs])
        if key in seen:
            continue
        seen.add(key)
        if len(set(imgs)) < 2 * n:
            continue
        asym += 1
        for t0 in range(1, 30):
            t = Fr(t0)
            if all(pgcd_deg(*p_and_q(v, t, j)) == 0 for j in range(n)):
                certified += 1
                break
    return len(seen), asym, certified


for n in (4, 6, 10, 14):
    classes, asym, certified = certify_length(n)
    print("L", n, "classes", classes, "trivial-stabilizer", asym, "good-certified", certified)
    assert asym == certified


def pgcd(p, q):
    p, q = trim(list(p)), trim(list(q))
    while q:
        p, q = q, prem(p, q)
    return p


def pdiff(p):
    return trim([i * c for i, c in enumerate(p)][1:])


def compose(big_p, s):
    out = []
    for c in reversed(big_p):
        out = padd(pmul(out, s), [c])
    return out


def psi(m):
    # Psi_m = monic gcd of S_{m-1} and S_{m-2} + 1 in Q[x]
    x = [Fr(0), Fr(1)]
    s = [[Fr(1)], x]
    while len(s) <= m:
        s.append(padd(pmul(x, s[-1]), [-c for c in s[-2]]))
    g = pgcd(s[m - 1], padd(s[m - 2], [Fr(1)]))
    return [c / g[-1] for c in g]


def family(r, m):
    return ([-1] + [1] * (r - 1)) * (m - 1) + [-1, -1] + [1] * (r - 2)


t = Fr(1, 3)
for r in range(3, 9):
    for m in range(3, 13):
        q = (m - 1) * r + 1
        p, qq = p_and_q(family(r, m), t, q)
        deg = pgcd_deg(p, qq)
        block = transfer([letter(x, t) for x in [-1] + [1] * (r - 1)])
        sigma = padd(block[0][0], block[1][1])
        big_f = compose(psi(m), sigma)
        assert deg == len(big_f) - 1 == r * ((m - 1) // 2)
        assert len(pgcd(big_f, pdiff(big_f))) == 1
    print("U_r,m exact nodal degree and squarefree Psi_m(sigma_r) at t=1/3: r", r, "m 3..12")

print("ALL_FINITE_CHECKS_PASSED")
```

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）

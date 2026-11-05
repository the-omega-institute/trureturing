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

**事实 3.2（连分式行列式与单值矩阵的迹）。** 设 $R$ 是交换环,$x_1,\dots,x_n\in R$。记 $K_n(x_1,\dots,x_n)$ 为对角元 $x_1,\dots,x_n$、次对角元全为 $-1$ 的 $n\times n$ 三对角矩阵的行列式,并约定空序列的 $K_0=1$、长度为 $-1$ 的 $K_{-1}=0$。则:

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

**注 3.3（先例）。** 事实 3.2 (1) 是连分式行列式(continuant)的标准递推;(2) 与 $p$ 的表达式是周期 Jacobi 算子 Floquet 判别式的有限圈形式。两者都是已知结果,写出证明只为本卷自足;出处见第 9 章。

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

(3) 由事实 3.2 (1),$\gamma_j=K_{L-1}(d_{j+1},\dots,d_{j+L-1})$ 的 $\lambda$-首项是 $(-\lambda)^{L-1}$,$\alpha_j=K_L(d_{j+1},\dots,d_{j+L})$ 的 $\lambda$-首项是 $(-\lambda)^L$;两者首项系数都是 $\pm1$。故在域 $\mathbb R(t)$ 上,$\operatorname{Res}_\lambda(\gamma_j,\alpha_j-1)=0$ 当且仅当两者有正次数公因子,由 (2) 当且仅当 $j$ 处有持续节点分支。母卷推论 3.3 说 $v$ 坏当且仅当某个站点有持续节点分支。∎

**注 3.7（模 $\gamma_j$ 的平方关系）。** 由事实 3.2 与 $\det M_j=1$,

$$
(-1)^L\alpha_j\,p=\alpha_j(\alpha_j+\delta_j-2)=\alpha_j^2+1+\beta_j\gamma_j-2\alpha_j=(\alpha_j-1)^2+\beta_j\gamma_j .
$$

所以模 $\gamma_j$ 有 $(-1)^L\alpha_jp\equiv(\alpha_j-1)^2$:在 $q_j$ 的根上,$p$ 的消失与 $\alpha_j-1$ 的消失等价,这是定理 3.6 (2) 的另一种读法。该恒等式在后文证明中不被使用。

## 4. 单点缺陷原理

**事实 4.1（Chebyshev 幂公式）。** 设 $R$ 是交换环,$B\in R^{2\times2}$,$\det B=1$,$x=\operatorname{tr}B$。则对一切 $n\ge0$,

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

**证明。** (1) 由事实 3.2 (1),$B_u$ 的 $(1,1)$ 元是 $K_r(d(u_0),\dots,d(u_{r-1}))$,其 $\lambda$-首项是各对角元之积的首项 $(-\lambda)^r$;$(2,2)$ 元是 $-K_{r-2}(\cdots)$,$\lambda$-次数至多 $r-2$。所以 $\sigma_u$ 的 $\lambda$-次数为 $r$、首项系数为 $(-1)^r$,与 $t$ 无关。$\Psi_m$ 首一且次数 $\lfloor(m-1)/2\rfloor\ge1$($m\ge3$),合成后得 (1)。

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

**注 4.5（解释与先例）。** 当 $w=\tilde u$ 时,定理 4.3 的一般域上的步骤说的是:Bloch 相位 $2\pi k/m$($0<k<m/2$)处周期算子的本征空间是二维的,这是周期 Jacobi 算子 Floquet 理论的熟知事实(第 9 章)。在本征值的二维本征空间里总有在给定站点 $q$ 为零的向量,而在 $q$ 为零的本征向量不受 $q$ 处势值的影响,这一点也是初等的。定理 4.3 的内容在于把二者合在一起:缺陷($w_q\ne\tilde u_q$)破坏了周期势的全部平移对称,而反射对称只保留 $\tilde u$ 的那些固定 $q$ 的反射。理由:若 $\pi\in D_L$ 保持 $w$,则两个 $r$-周期势 $\tilde u$ 与 $\tilde u\circ\pi$ 都在 $\{q,\pi^{-1}(q)\}$ 以外与 $w$ 相同,而二者若在某站点不同,就在该站点模 $r$ 剩余类的全部 $m\ge3$ 个站点上不同,故 $\tilde u\circ\pi=\tilde u$,再由 $w_q\ne\tilde u_q$ 得 $\pi(q)=q$,非单位的旋转没有不动点;反之 $\tilde u$ 的固定 $q$ 的对称显然保持 $w$。所以缺陷站点是 $\tilde u$ 某个反射对称的不动点时该反射保留,命题 8.3 即是此例;否则 $w$ 没有非平凡二面体对称,族 $U_{r,m}$ 即是此例(定理 6.2 (1) 给出更强的交换子平凡)。无论哪种情形,缺陷都留下一条对一切耦合 $t$ 都存在、并由 $\Psi_m(\sigma_u)$ 显式给出的节点分支。由定理 3.6,在 $q$ 处这表现为 $M_q$ 在 $\Psi_m(\sigma_u)$ 的根上是上三角单位矩阵;事实 4.1 把周期部分的单值写成 $B^m-I=S_{m-1}(\sigma_u)B-(S_{m-2}(\sigma_u)+1)I$,命题 4.2 (1) 说明 $\Psi_m(\sigma_u)$ 恰是使两个系数同时为零的因子。

**定理 4.6（同余站点上的多点缺陷）。** 设 $r\ge1$,$m\ge3$,$L=rm$,$u\in\mathbb R^r$,$\tilde u$ 如定理 4.3。取整数 $0<\nu<m/2$(Bloch 指标,不同于站点指标 $j$),令 $c=2\cos(2\pi\nu/m)$,$g=\gcd(m,2\nu)$,$e=m/g$,站点集

$$
Q=\{\,q+k\,e\,r\bmod L:\ k\in\mathbb Z\,\}\subset\mathbb Z/L\mathbb Z,\qquad |Q|=g .
$$

设势 $w\in\mathbb R^L$ 在 $Q$ 以外与 $\tilde u$ 相同,在 $Q$ 上取任意实数。则:

1. 对每个实数 $t_0$ 与 $\sigma_u(\cdot,t_0)-c$ 的每个复根 $\lambda_0$,$\lambda_0$ 是实数,$H^w_{t_0}$ 有本征值 $\lambda_0$ 的实本征向量 $z$,它在 $Q$ 的每个站点处为零,并且对一切 $k\ge1$ 满足 $z_{q+kr}=S_{k-1}(c)\,z_{q+r}$;
2. $\sigma_u-c$ 在 $\mathbb R(t)[\lambda]$ 中的每个首一不可约因子,对每个 $q'\in Q$ 都整除 $w$ 在 $q'$ 处的节点因子 $g_{q'}$。

特别地,$w$ 在 $Q$ 的每个站点处都有持续节点分支。$g=1$ 时 $Q=\{q\}$;$m$ 为偶数且 $\nu=1$ 时 $Q=\{q,\,q+L/2\}$。

**证明。** 由 $0<2\nu<m$ 得 $m\nmid2\nu$,故 $e\ge2$;$Q$ 是 $\mathbb Z/L\mathbb Z$ 中以 $er$ 为步长的陪集,$er\mid L$,元素个数为 $L/(er)=g$。

设 $K$ 是含 $\mathbb R$ 的代数闭域,$(\lambda_0,t_0)\in K^2$ 满足 $\sigma_u(\lambda_0,t_0)=c$。令 $\theta=2\pi\nu/m$,则 $\Psi_m(c)=0$,与定理 4.3 证明中的一般域步骤相同,递推 $\tilde d_iz_i-z_{i-1}-z_{i+1}=0$ 的解空间是二维的,且每个解都是 $L$-周期的。取 $z_q=0$、$z_{q+1}=1$ 的解 $z$。令 $B'=T(\tilde d_{q+r-1})\cdots T(\tilde d_q)$,则 $Z_{q+r}=B'Z_q$ 且 $Z_{q+kr}=B'^kZ_q$。$B'$ 的因子是 $B_u$ 的因子的一个循环轮换,故 $B'$ 与 $B_u(\lambda_0,t_0)$ 相似,$\operatorname{tr}B'=c$,$\det B'=1$。由事实 4.1,

$$
Z_{q+kr}=S_{k-1}(c)\,B'Z_q-S_{k-2}(c)\,Z_q,
$$

取第一个坐标并用 $z_q=0$ 得 $z_{q+kr}=S_{k-1}(c)\,z_{q+r}$。而 $S_{k-1}(c)\sin\theta=\sin(k\theta)$,$\sin\theta\ne0$;当 $k=en$($n\in\mathbb Z_{\ge0}$)时 $k\theta=(m/g)\,n\cdot2\pi\nu/m=\pi\cdot(2\nu/g)\cdot n\in\pi\mathbb Z$,因为 $g\mid2\nu$。所以 $z$ 在 $q+n\,e\,r$($n\in\mathbb Z_{\ge0}$)处为零,由 $L$-周期性在整个 $Q$ 上为零。于是

$$
H^w_{t_0}z=H^{\tilde u}_{t_0}z+t_0\sum_{q'\in Q}(w_{q'}-\tilde u_{q'})\,z_{q'}\,e_{q'}=\lambda_0z .
$$

(1) 取 $K=\mathbb C$:$H^w_{t_0}$ 实对称,故 $\lambda_0$ 实;取 $z$ 的实部或虚部中非零的一个即得实本征向量,它仍在 $Q$ 上为零并满足同一递推关系,因而仍满足 $z_{q+kr}=S_{k-1}(c)z_{q+r}$(该关系对实部与虚部分别成立)。由定理 4.3 的证明 (1),$\sigma_u(\cdot,t_0)-c$ 的 $\lambda$-次数为 $r\ge1$,复根存在。

(2) 设 $\pi$ 是 $\sigma_u-c$ 的首一不可约因子,$`\lambda_*`$ 是它在 $\mathbb R(t)$ 的代数闭包 $F$ 中的根。以 $K=F$、$`(\lambda_*,t)`$ 应用上面的步骤,得 $H^w_t$ 在 $F$ 上的本征向量在每个 $q'\in Q$ 处为零;由引理 3.4,$`p_w(\lambda_*)=q_{w,q'}(\lambda_*)=0`$,故 $\pi\mid g_{q'}$。∎

**注 4.7（多点缺陷的范围）。** 定理 4.3 对应于同时使用 $\Psi_m$ 的全部根、只在一个站点 $q$ 改动的情形;定理 4.6 对 $\Psi_m$ 的单个根放宽到 $\gcd(m,2\nu)$ 个同余站点。两者都要求改动的站点落在周期势某个节点本征向量的零点集中。母卷例 4.1 的势不在定理 4.3 与 4.6 的范围内(命题 8.4)。

**事实 4.8（带内块迹的根都是单根）。** 设 $u\in\mathbb R^r$,$r\ge1$,$t_0\in\mathbb R$,$c=2\cos\theta$,$0<\theta<\pi$。则 $\sigma_u(\cdot,t_0)-c$ 的 $r$ 个复根都是实的单根。

**证明。** 记 $\delta_i=2+t_0u_i$。$r=1$ 时 $\sigma_u=\delta_0-\lambda$,结论显然。$r=2$ 时 $\sigma_u-c=(\delta_0-\lambda)(\delta_1-\lambda)-2-c$,其判别式 $(\delta_0-\delta_1)^2+4(2+c)>0$,两根实且不同。

设 $r\ge3$。令 $H_\theta$ 为 $r\times r$ 复矩阵:对角元 $\delta_0,\dots,\delta_{r-1}$,$(i,i+1)$ 与 $(i+1,i)$ 位($0\le i\le r-2$)为 $-1$,角元 $(r-1,0)$ 位为 $-e^{i\theta}$、$(0,r-1)$ 位为 $-e^{-i\theta}$,其余为 $0$。$H_\theta$ 是 Hermite 矩阵。按事实 3.2 (2) 证明中的 Leibniz 展开计算 $\det(H_\theta-\lambda I)$:只由不动点与相邻对换组成的置换给出与那里相同的 $K_r-K_{r-2}$(对换 $(r-1\ 0)$ 的两个角元之积是 $e^{i\theta}e^{-i\theta}=1$);向前旋转的项是 $(-1)^{r-1}\cdot(-1)^{r-1}(-e^{i\theta})=-e^{i\theta}$,向后旋转的项是 $-e^{-i\theta}$。故

$$
\det(H_\theta-\lambda I)=\sigma_u(\lambda,t_0)-2\cos\theta ,
$$

于是 $\sigma_u(\cdot,t_0)-c$ 的根(计重数)就是 $H_\theta$ 的本征值(计代数重数),都是实数。设 $\lambda_0$ 是其中之一,$y\in\mathbb C^r$ 是 $H_\theta$ 对 $\lambda_0$ 的本征向量。令 $z_{kr+i}=e^{ik\theta}y_i$($k\in\mathbb Z$,$0\le i<r$),逐行核对 $H_\theta y=\lambda_0y$(第 $0$ 行与第 $r-1$ 行用到角元)可知 $z$ 满足递推 $(2+t_0u_{i\bmod r}-\lambda_0)z_i-z_{i-1}-z_{i+1}=0$($i\in\mathbb Z$)且 $Z_r=e^{i\theta}Z_0$。又 $Z_r=B_u(\lambda_0,t_0)Z_0$,而 $Z_0=(y_0,e^{-i\theta}y_{r-1})^{\top}$ 决定 $z$ 从而决定 $y$。所以 $y\mapsto Z_0$ 是从 $H_\theta$ 的 $\lambda_0$-本征空间到 $B_u(\lambda_0,t_0)$ 的 $e^{i\theta}$-本征空间的单射。$B_u(\lambda_0,t_0)$ 的迹为 $2\cos\theta$、行列式为 $1$,特征值 $e^{\pm i\theta}$ 不同,后一个本征空间是一维的。于是 $\lambda_0$ 的几何重数为 $1$;Hermite 矩阵的几何重数等于代数重数,故 $\lambda_0$ 是单根。∎

**命题 4.9（$\Psi_m(\sigma_u)$ 无平方因子并整除节点因子）。** 在定理 4.3 的条件下,$\Psi_m(\sigma_u)$ 在 $\mathbb R(t)[\lambda]$ 中无平方因子,并且 $(-1)^{r\lfloor(m-1)/2\rfloor}\Psi_m(\sigma_u)$(关于 $\lambda$ 首一)在 $\mathbb R[t][\lambda]$ 中整除 $w$ 在 $q$ 处的节点因子 $g_q$。

**证明。** 记 $N=r\lfloor(m-1)/2\rfloor$,$F=\Psi_m(\sigma_u)$;由定理 4.3 (1),$(-1)^NF$ 是 $\mathbb R[t][\lambda]$ 中关于 $\lambda$ 首一的多项式。取 $t_0=0$。$F(\cdot,0)=\prod_{0<k<m/2}(\sigma_u(\cdot,0)-2\cos(2\pi k/m))$;由事实 4.8,每个因子只有单根;不同 $k$ 的因子没有公共根,因为在公共根处 $\sigma_u$ 会取两个不同的值。故 $F(\cdot,0)$ 无重根。若 $h^2\mid F$,$h\in\mathbb R(t)[\lambda]$ 首一不可约,则 $h$ 与余因子都在 $\mathbb R[t][\lambda]$ 中($\mathbb R[t]$ 整闭,母卷定理 3.2 证明中的同一论证),代入 $t=0$ 后 $h(\cdot,0)$ 首一、次数为正,其平方整除 $F(\cdot,0)$,矛盾。所以 $F$ 的首一不可约因子两两不同;由定理 4.3 (3) 每个都整除 $g_q$,$\mathbb R(t)[\lambda]$ 是唯一分解整环,故 $(-1)^NF\mid g_q$;两者首一且系数在 $\mathbb R[t]$ 中,商也在 $\mathbb R[t][\lambda]$ 中。∎

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

**注 6.8（与定理 4.3、4.6 的一致性）。** 命题 6.7 是定理 4.6 在 $(r,m,\nu)=(3,4,1)$ 时的显式形式:$\Psi_4(\sigma_3)=\sigma_3$,$\gcd(4,2)=2$,$Q=\{10,4\}$。按定理 4.6,还可以在站点 $4$ 处任意改动势值而保留这条节点分支。

**命题 6.9（块迹的 Chebyshev 闭式）。** 对 $r\ge1$,块 $-+^{r-1}=(-1,1,\dots,1)\in\{-1,1\}^r$ 的块迹是

$$
\sigma_{-+^{r-1}}=b\,S_{r-1}(a)-2\,S_{r-2}(a).
$$

因此对 $r,m\ge3$,多项式 $\Psi_m\bigl(bS_{r-1}(a)-2S_{r-2}(a)\bigr)$ 的每个首一不可约因子都整除 $U_{r,m}$ 在 $q_{r,m}$ 处的节点因子。例如 $\sigma_3=b(a^2-1)-2a$,$\sigma_4=b(a^3-2a)-2(a^2-1)$。

**证明。** 由约定 2.3,该块的转移矩阵是 $T(a)^{r-1}T(b)$。$T(a)$ 的行列式为 $1$、迹为 $a$,由事实 4.1,$T(a)^{r-1}=S_{r-2}(a)T(a)-S_{r-3}(a)I$(对 $r\ge1$ 成立,$r=1$ 时右边为 $0\cdot T(a)+I$)。又 $\operatorname{tr}T(b)=b$,$\operatorname{tr}(T(a)T(b))=ab-2$。于是

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

**证明。** 第 10 章的代码对 $L\in\{6,10,14\}$ 枚举 $\{-1,1\}^L$,在 $D_L$ 作用与变号生成的群的每个轨道中取一个代表,只保留 $D_L$-轨道长为 $2L$(即稳定子平凡)的代表,并对每个这样的代表 $v$ 与每个站点 $j$,在正整数 $t_0\le29$ 中找到一个,使 $p(\cdot,t_0)$ 与 $q_j(\cdot,t_0)$ 在 $\mathbb Q[\lambda]$ 中的 Euclid 算法终止于非零常数。代码实际检查的是更强的条件:对每个代表,按 $t_0=1,2,\dots$ 的顺序取第一个对全部站点 $j$ 同时满足上述条件的 $t_0$,它蕴含逐站点的条件;对 $L\in\{6,10,14\}$ 的每个代表,第一个尝试值 $t_0=1$ 即满足。$p$ 与 $q_j$ 用事实 3.2 的公式 $p=(-1)^L(\operatorname{tr}M_j-2)$、$q_j=(-1)^{L-1}K_{L-1}(d_{j+1},\dots,d_{j+L-1})$ 以有理数精确计算;$\mathbb Q[\lambda]$ 中互素蕴含 $\mathbb R[\lambda]$ 中互素。代码断言每个代表都找到了证书。由引理 7.1,这些代表都是好势,并且同一轨道中的势也是好势,稳定子也平凡。

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

**证明。** 若 $v_8=u^{m-1}u^{\sharp}$ 且 $8=rm$、$m\ge3$,则 $r\in\{1,2\}$,由命题 8.2 $v_8$ 有非平凡二面体对称,与命题 5.5 的交换子平凡矛盾。再看定理 4.6 的形式:$8=rm$、$m\ge3$ 同样迫使 $r\in\{1,2\}$。定理 4.6 中的块 $u\in\mathbb R^r$ 是实块,但 $v_8$ 在 $Q$ 以外与 $\tilde u$ 相同;$Q$ 的元素彼此相差 $er$ 的倍数,落在同一个模 $r$ 剩余类中,且 $|Q|=g=m/e\le m/2$(定理 4.6 的证明给出 $e\ge2$),而每个模 $r$ 剩余类有 $m$ 个站点,所以每个模 $r$ 剩余类都有 $Q$ 以外的站点 $i$,在那里 $u_{i\bmod r}=\tilde u_i=(v_8)_i\in\{\pm1\}$。故 $u\in\{-1,1\}^r$,周期势只有常数 $\pm1$ 与 $\pm(+-)^4$ 四个;$v_8$ 与它们取值不同的站点集分别是 $\{4,6,7\}$($+1$)、$\{0,1,2,3,5\}$($-1$)、$\{1,3,4,5,6\}$($+-+-+-+-$)、$\{0,2,7\}$($-+-+-+-+$)。定理 4.6 的 $Q$ 是步长 $er$ 的陪集,$|Q|=\gcd(m,2\nu)$:$r=2$ 时 $m=4$、$\nu=1$,$Q$ 有 $2$ 个元素;$r=1$ 时 $m=8$,$\nu\in\{1,2,3\}$,$Q$ 有 $2$、$4$、$2$ 个元素,步长分别为 $4$、$2$、$4$。五元集放不进至多四元的 $Q$;三元集 $\{4,6,7\}$ 与 $\{0,2,7\}$ 同时含奇偶站点,放不进步长为偶数的陪集。故 $v_8$ 不是这种修改。等式部分:$\operatorname{tr}(T(x)T(y))=xy-2$,$ab=(2-\lambda)^2-t^2$,故 $ab-2=\lambda^2-4\lambda+2-t^2$,这正是母卷例 4.1 的 $g$;而 $\Psi_4(x)=x$。母卷例 4.1 证明了 $g$ 整除 $p$ 与 $q_1$,故 $g\mid g_1$;本命题不断言 $g=g_1$。∎

**开放问题 8.5（长度 $2p$）。** 对素数 $p\ge11$,$C_{2p}$ 上是否存在与 $\Delta_{2p}$ 不共享非平凡对称的坏 $\pm1$ 势?本卷的构造到不了这些长度:推论 4.4 需要 $L=rm$ 且 $m\ge3$;在 $L=2p$ 时只能 $r\in\{1,2\}$,由命题 8.2 得到的都是对称势;$r=p$、$m=2$ 时 $\Psi_2=1$,定理 4.3 不给出节点分支。定理 7.6 对 $p\le7$ 给出否定回答,但它依赖逐个长度的有限证书,不提供对一般 $p$ 的论证。缺的是一个对 $L=2p$ 的结构性障碍,例如把 Lindblad 与 Guerrero 对素数长度的单位根论证推广到 $2p$ 次单位根。

**开放问题 8.6（节点因子的精确形与其他节点站点）。** 命题 7.5 只覆盖 $3\le r\le8$、$3\le m\le12$。对一般的 $r,m\ge3$,$U_{r,m}$ 在 $q_{r,m}$ 处的节点因子是否等于 $\pm\Psi_m(\sigma_r)$(命题 4.9 只给出整除),以及 $r\ge4$ 时 $\sigma_r-2\cos(2\pi k/m)$ 在 $\mathbb R(t)[\lambda]$ 中的不可约分解,本卷均未证明;缺的是节点因子次数的一般上界。$U_{r,m}$ 在缺陷站点以外的持续节点分支,本卷只知道定理 4.6 给出的同余站点(例如命题 6.7 中的站点 $4$),其余站点未研究。

**开放问题 8.7（节点因子的一般描述）。** 命题 8.4 表明,无对称坏势的节点因子可以含 Chebyshev 形的因子 $\Psi_4(\sigma_{+-})$,而势本身既不是周期势的单点修改,也不是定理 4.6 意义下的同余多点修改。产生这一因子的机制是什么?是否每个坏 $\pm1$ 势在某个站点处的节点因子都含有某个块迹 $\sigma_u$ 的 $\Psi_m(\sigma_u)$ 的不可约因子?这是母卷开放问题 6.3 在本卷之后的剩余部分。

## 9. 来源、文献状态与核验边界

**文献表态(CLAUDE.md 第 3.7 条,每条命题只取一个值)。**

| 来源 | 精确范围与使用边界 |
| --- | --- |
| O. Lindblad, E. Guerrero, *Simple Eigenvalues and Non-vanishing Eigenvectors of the Anderson Model*, arXiv:2512.00278v1,§1(算子与定义 1.1、定理 1.3 之后的逆问题)、命题 2.3、引理 3.2、命题 4.1 | `literature-attested`:算子 $H_t=\Delta+tV$、好势与坏势的定义与二分(经母卷推论 3.3 使用)、逆问题的提法,以及命题 4.1:$d=1$ 且 $L$ 为素数时,势(对实值势陈述)是坏势当且仅当它关于某个顶点反射对称;后者用于定理 7.6 的素数长度部分。核对 v1 的 HTML 全文:该文不讨论合数长度,不使用转移矩阵或单点缺陷,也未给出无对称坏势。 |
| 母卷 `docs/develop/theory/CYCLE_ANDERSON_PERSISTENT_NODAL_BRANCHES.md`:约定 2.1–2.5、定理 3.2、推论 3.3、例 4.1、定义 4.2、引理 4.3、定理 4.4、4.6 | 本仓既有卷,作为输入引用,不在本卷重新表态;其各条的文献表态见母卷第 8 章。 |
| G. Teschl, *Jacobi Operators and Completely Integrable Nonlinear Lattices*, Math. Surveys Monogr. 72, AMS 2000,第 7 章(周期 Jacobi 算子、Floquet 判别式、Bloch 解) | `literature-attested`:事实 3.2 (2) 与 $p=(-1)^L(\operatorname{tr}M_j-2)$ 是 Floquet 判别式的有限圈形式;注 4.5 所说周期算子在 Bloch 相位 $2\pi k/m$($0<k<m/2$)处的二重简并;事实 4.8 是「Floquet 判别式在带内的根都是单根」的有限形式。式号定位未核;本卷对事实 3.2 写出了完整证明,不依赖该书。 |
| R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd ed., Addison-Wesley 1994,§6.7(continuants) | `literature-attested`:事实 3.2 (1) 的连分式行列式递推与 $2\times2$ 矩阵积表示。 |
| J. C. Mason, D. C. Handscomb, *Chebyshev Polynomials*, Chapman & Hall/CRC 2003,第 1 章 | `literature-attested`:$S_n(2\cos\theta)\sin\theta=\sin((n+1)\theta)$(第二类 Chebyshev 多项式的变量缩放),用于命题 4.2 与约定 2.4;事实 4.1 的幂公式是 Cayley–Hamilton 定理的标准推论,小节定位未核。 |
| A. E. Brouwer, W. H. Haemers, *Spectra of Graphs*, Springer 2012,§1.4(路的谱) | `literature-attested`:路 $J_\ell$ 的谱为 $2\cos(\pi k/(\ell+1))$,即引理 5.2 的第一句;小节定位未核。引理 5.2 的互素判据是本卷的初等推论。 |
| S. Lang, *Algebra*, rev. 3rd ed., Springer 2002,第 IV 章 §2(Gauss 引理)与 §8(结式) | `literature-attested`:Gauss 引理与首一多项式结式的取值交换性,用于命题 4.2 (1)、定理 6.5、引理 7.1。 |
| S. Roy, *A spectral viewpoint on the single defect tight-binding chain*, arXiv:2607.29467 | `literature-attested`(同类结果):均匀最近邻紧束缚链上单个在位缺陷的「暗子空间」,即在缺陷站点振幅为零、因而不受缺陷影响的本征态。定理 4.3 在 $r=1$(常数块、单点缺陷)时的特例是同一机制在圈上的形式:本征值 $2+tu_0-2\cos(2\pi k/m)$ 的、在缺陷站点为零的本征向量与缺陷强度 $w_q$ 无关;本卷只把它作为中间步骤与先例。只核对到摘要:该文对链陈述,圈上的对应与「对任意缺陷强度」的逐字陈述未核全文。 |
| — | `literature-attested`:事实 3.2、注 3.3、事实 4.1、事实 4.8。这三条事实是已知结果,只作后文证明的中间步骤,不作为本卷新增的定理;写出证明只为自足。 |
| — | `repo-derived`:定义 3.1、引理 3.4(母卷节点步在任意域上的形式)、定理 3.6、注 3.5、注 3.7、命题 4.2、推论 4.4、注 4.5、注 4.7、命题 4.9、引理 5.1、引理 5.2(其首句路的谱是 `literature-attested` 的中间步骤,见 Brouwer–Haemers 行;互素判据为本卷推论)、引理 5.3、定理 5.4、命题 5.5、注 5.6、定义 6.1、引理 6.3、定理 6.5、注 6.6、命题 6.7、注 6.8、命题 6.9、引理 7.1、命题 7.2、命题 7.3、命题 7.5、命题 8.1–8.4。 |
| — | `suspected-novel`:定理 4.3(单点缺陷原理;承重部分是一般实块 $u\in\mathbb R^r$、一切耦合 $t$,以及 $\Psi_m(\sigma_u)$ 的每个首一不可约因子整除节点因子,与命题 4.9 合起来即无平方因子的 $\pm\Psi_m(\sigma_u)$ 整除节点因子;$r=1$ 特例是 Roy 行所列的 `literature-attested` 中间步骤)、定理 4.6(同余站点上的多点缺陷)、定理 6.2(族 $U_{r,m}$)、定理 6.4(既非素数也非素数两倍的长度)、命题 7.4、定理 7.6。检索范围:arXiv:2512.00278v1 的 HTML 全文;母卷第 8 章所列检索;以「bad potential」「Anderson model」「cycle」「symmetry」「converse」「composite length」组合的网络检索;latent symmetry 与 cospectral vertices 文献,包括 D. Smith, B. Webb, *Hidden symmetries in real and theoretical networks*, Physica A 514 (2019) 855–867(arXiv:1803.02328)、M. Röntgen 等, *Latent symmetry induced degeneracies*, Phys. Rev. Lett. 126 (2021) 180601(arXiv:2011.13404)、M. Kempton, J. Sinkovic, D. Smith, B. Webb, *Characterizing cospectral vertices via isospectral reduction*, Linear Algebra Appl. 594 (2020) 226–248(仅核到书目信息)。这些文献讨论固定矩阵的隐藏对称与本征向量分量的消失,检索范围内未见对单参数族 $\Delta+tV$ 的持续节点分支、周期势单点缺陷或合数长度逆问题的处理。这不确立检索范围之外的优先权。 |

**核验边界。** 第 10 章的代码是本卷唯一的代码块,输入固定,只做两件事:(i) 对 $L\in\{4,6,10,14\}$,枚举 $\{-1,1\}^L$ 在二面体作用与变号下的轨道代表,对稳定子平凡的每个代表,在正整数 $t_0\le29$ 中寻找一个对全部站点 $j$ 同时使 $p(\cdot,t_0)$ 与 $q_j(\cdot,t_0)$ 在 $\mathbb Q[\lambda]$ 中互素的证书(比命题 7.4 证明所需的逐站点证书更强,并蕴含后者),并断言全部找到;对 $L\in\{6,10,14\}$ 的每个代表,第一个尝试值 $t_0=1$ 即是证书,所用的 $t_0$ 不在打印输出中;它打印各长度的轨道总数与稳定子平凡的轨道数,读数为 $L=4$:$4$ 与 $0$;$L=6$:$8$ 与 $1$;$L=10$:$44$ 与 $18$;$L=14$:$362$ 与 $261$。(ii) 对 $3\le r\le8$、$3\le m\le12$,在 $t=1/3$ 处计算 $U_{r,m}$ 的 $p$ 与 $q_{q_{r,m}}$ 的最大公因式次数,断言等于 $r\lfloor(m-1)/2\rfloor$;同时断言 $\Psi_m(\sigma_r(\cdot,1/3))$ 与其导数互素,这一项只是命题 4.9 在 $t=1/3$ 处的一致性核对,不被任何证明使用。全部算术用 Python 标准库的有理数,末行打印哨兵 `ALL_FINITE_CHECKS_PASSED`。

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
## 11. 缺陷站点节点因子的全参数恒等式

**定理 11.1（指定缺陷站点的精确节点因子）。** 对任意整数 $r,m\ge3$，令 $L=rm$、$q=(m-1)r+1$，在 $\mathbb Z/L\mathbb Z$ 上取定义 6.1 的势

$$
U_i=\begin{cases}-1,&i\equiv0\pmod r\ \text{或}\ i=q,\\1,&\text{其余情形}。\end{cases}
$$

令 $t$ 为不定元，$K=\mathbb R(t)$，并记

$$
H=\Delta_L+t\operatorname{diag}(U),\qquad
p=\det(\lambda I_L-H),\qquad
Q=\det(\lambda I_{L-1}-H^{(q)}),\qquad
g=\operatorname{monic\_gcd}_{K[\lambda]}(p,Q).
$$

这里 $H^{(q)}$ 是同时删除第 $q$ 行与第 $q$ 列所得的实际主子矩阵，其余对角元保持 $2+tU_i$。沿用约定 2.2、2.4，置

$$
a=2-\lambda+t,\qquad b=2-\lambda-t,\qquad
\sigma_r=bS_{r-1}(a)-2S_{r-2}(a),\qquad
N=r\left\lfloor\frac{m-1}{2}\right\rfloor.
$$

则在 $K[\lambda]$ 中有精确的首一恒等式

$$
\boxed{\quad g=(-1)^N\Psi_m(\sigma_r).\quad}
$$

因而 $\deg_\lambda g=N$，且 $g$ 无平方因子。

**证明。** 令 $\widetilde U_i=-1$ 当且仅当 $i\equiv0\pmod r$，其余站点取 $1$，并令

$$
H_0=\Delta_L+t\operatorname{diag}(\widetilde U),\qquad
p_0=\det(\lambda I_L-H_0).
$$

由 $\widetilde U_q=1$，有 $H=H_0-2tE_{qq}$。删除第 $q$ 行列后，两矩阵完全相同。行列式对第 $(q,q)$ 元的线性给出

$$
Q=\det(\lambda I_{L-1}-H_0^{(q)}),\qquad
p=p_0+2tQ,\qquad
\operatorname{monic\_gcd}(p,Q)=\operatorname{monic\_gcd}(p_0,Q).
\tag{11.1}
$$

这里保留的是圈的主子矩阵，而非把删点后端点的对角元改成 $1$ 的路 Laplace 矩阵。零振幅不受在位秩一扰动影响，是此恒等式的本征向量表述；均匀圈上的对应见 S. Roy，[*A spectral viewpoint on the single defect tight-binding chain*](https://arxiv.org/html/2607.29467v1)，§2.1–2.2、式 (1)–(4)、(10)：其跃迁系数取 $\gamma=1$，背景常数对角元 $c$ 对应能量平移 $E=\lambda-c$，其缺陷强度对应 $2t$。此处 $H_0$ 的对角元具有周期 $r$，式 (11.1) 直接来自上述行列式线性。

在周期背景 $\widetilde U$ 上，从状态 $Z_{q+1}=(z_{q+1},z_q)^{\mathsf T}$ 向前传递一个周期。因为 $q\equiv1\pmod r$，依次经过的站点 $q+1,\ldots,q+r$ 的系数是 $r-2$ 个 $a$、一个 $b$、一个 $a$。故该周期的传递矩阵为

$$
C=T(a)T(b)T(a)^{r-2},\qquad
\det C=1,\qquad
\operatorname{tr}C=\operatorname{tr}\bigl(T(a)^{r-1}T(b)\bigr)=\sigma_r,
\tag{11.2}
$$

最后一个等式使用命题 6.9。从 $q+1$ 到 $q+L+1$ 恰经过 $m$ 个相同周期，所以背景的整圈单值矩阵是 $C^m$。由事实 3.2，实际周期边界与实际主子式满足

$$
(-1)^Lp_0=\operatorname{tr}(C^m)-2,\qquad
(-1)^{L-1}Q=(C^m)_{21}.
\tag{11.3}
$$

周期单值的标准对应见 G. Teschl，[*Jacobi Operators and Completely Integrable Nonlinear Lattices*](https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf)，式 (1.28)–(1.30)、§7.1 式 (7.3)–(7.10)：取该书 Jacobi 系数 $a_{\mathrm T}(n)=-1$、$b_{\mathrm T}(n)=2+t\widetilde U_n$、谱参数 $z=\lambda$；交换该书状态 $(z_n,z_{n+1})^{\mathsf T}$ 的两个坐标，即得到本卷的 $(z_{n+1},z_n)^{\mathsf T}$ 与 $T(2+t\widetilde U_{n+1}-\lambda)$。该书判别式是单值迹的一半，因而单周期判别式为 $\sigma_r/2$，整圈的周期条件对应式 (11.3) 中的迹 $2$。

取 $K$ 的代数闭包 $F$，令 $\lambda_*\in F$ 为 $p,Q$ 的任一公共根。下文把 $a,b,C,\sigma_r$ 均在 $\lambda=\lambda_*$ 处取值，仍用同一字母表示。由式 (11.1)、(11.3)，矩阵 $M=C^m$ 满足

$$
M_{21}=0,\qquad \operatorname{tr}M=2,\qquad \det M=1.
$$

若 $M_{11}=\alpha$、$M_{22}=\delta$，则 $\alpha+\delta=2$、$\alpha\delta=1$，从而 $(\alpha-1)^2=0$。域中没有非零幂零元，故 $\alpha=\delta=1$，于是

$$
C^me_1=e_1,\qquad e_1=(1,0)^{\mathsf T}.
\tag{11.4}
$$

设

$$
s=S_{r-2}(a),\qquad v=S_{r-3}(a),\qquad h=bs-v.
$$

事实 3.2 的常系数情形给出 $T(a)^{r-2}$ 的第一列为 $(s,v)^{\mathsf T}$；也可由事实 4.1 与 $S_n$ 的递推直接读出。因此

$$
Ce_1=\begin{pmatrix}ah-s\\h\end{pmatrix}.
\tag{11.5}
$$

现证明在这个公共根处 $h\ne0$。若 $h=0$，则 $Ce_1=-s e_1$，由式 (11.4) 得 $(-s)^m=1$，特别地 $s\ne0$。由于 $r\ge3$，多项式

$$
\bigl(-S_{r-2}(X)\bigr)^m-1\in\mathbb R[X]
$$

次数为 $m(r-2)>0$，且以 $a$ 为根。因此 $a$ 在 $\mathbb R$ 上代数，$s,v$ 也在 $\mathbb R$ 上代数。又 $h=0$ 与 $s\ne0$ 给出 $b=v/s$，故 $b$ 在 $\mathbb R$ 上代数。这迫使

$$
t=\frac{a-b}{2}
$$

在 $\mathbb R$ 上代数，与 $t$ 是不定元矛盾。于是式 (11.5) 的第二个坐标确实非零。

以事实 4.1 计算式 (11.4)，有

$$
0=(C^m-I)e_1
 =S_{m-1}(\sigma_r)Ce_1-
   \bigl(S_{m-2}(\sigma_r)+1\bigr)e_1.
\tag{11.6}
$$

取第二个坐标，因 $h\ne0$，得 $S_{m-1}(\sigma_r)=0$；再取第一个坐标，得 $S_{m-2}(\sigma_r)+1=0$。命题 4.2 (1) 给出这两个一元多项式的首一最大公因式为 $\Psi_m$。将其 Bézout 恒等式代入 $\sigma_r$，得到

$$
\Psi_m\bigl(\sigma_r(\lambda_*,t)\bigr)=0.
\tag{11.7}
$$

这一步同时排除带边：$S_{m-1}(2)=m$、$S_{m-1}(-2)=(-1)^{m-1}m$ 均不为零，故任何公共根均不满足 $\sigma_r=\pm2$；标量单周期矩阵 $C=\pm I$ 已包含在被排除的 $h=0$ 情形中。

还须控制最大公因式的重数。主子式 $Q\in\mathbb R[t][\lambda]$ 关于 $\lambda$ 首一且次数为 $L-1$。在 $t=0$ 处，它是对角元为 $2$、相邻非对角元为 $-1$ 的 $L-1$ 阶路矩阵的特征多项式。因此

$$
Q(\lambda,0)=\prod_{j=1}^{L-1}
 \left(\lambda-2+2\cos\frac{\pi j}{L}\right).
\tag{11.8}
$$

这些根两两不同：对 $1\le j\le L-1$，正弦向量 $y_i=\sin(\pi ji/L)$，$1\le i\le L-1$，在边界 $y_0=y_L=0$ 下给出本征值 $2-2\cos(\pi j/L)$，而余弦在 $(0,\pi)$ 上严格单调。故 $\operatorname{Res}_\lambda(Q,\partial_\lambda Q)$ 在 $t=0$ 的取值不为零；首一性使次数在这个取值下保持，结式的取值与系数取值可交换。于是 $Q$ 在 $K[\lambda]$ 中无重根，$g\mid Q$ 也无重根。

对 $g$ 的任一首一不可约因子 $\pi$，在 $F$ 中取其一个根。它是 $p,Q$ 的公共根，式 (11.7) 表明 $\pi\mid\Psi_m(\sigma_r)$。因为 $g$ 无重根，合并全部不可约因子便得到反向整除

$$
g\mid\Psi_m(\sigma_r)\qquad\text{于 }K[\lambda].
\tag{11.9}
$$

另一方面，命题 4.9 已给出无平方因子的首一多项式 $(-1)^N\Psi_m(\sigma_r)$ 整除 $g$；此处直接使用该结论。由 $S_{r-1}$ 首一且次数为 $r-1$，$bS_{r-1}(a)-2S_{r-2}(a)$ 关于 $\lambda$ 的首项为 $(-1)^r\lambda^r$，而 $\Psi_m$ 首一且次数为 $\lfloor(m-1)/2\rfloor$，故 $\Psi_m(\sigma_r)$ 的首项为 $(-1)^N\lambda^N$。两向整除与首一性遂给出所述恒等式；次数与无平方因子性随即成立。∎

**推论 11.2（指定站点的代数节点分支与次数上界）。** 在定理 11.1 的条件下，令 $F=\overline{\mathbb R(t)}$。使实际圈矩阵 $H$ 存在非零本征向量 $z\in F^L$ 且 $z_q=0$ 的谱值，恰为

$$
\bigcup_{\substack{k\in\mathbb Z\\0<2k<m}}
\left\{\lambda_*\in F:
 bS_{r-1}(a)-2S_{r-2}(a)=2\cos\frac{2\pi k}{m}\right\},
$$

其中方程中的 $a,b$ 均在 $\lambda=\lambda_*$ 处取值。该集合共有 $r\lfloor(m-1)/2\rfloor$ 个不同元素；每个谱值的节点本征向量空间恰为一维，且可唯一归一化为 $z_{q+1}=1$。特别地，开放问题 8.6 第一子句所需的一般上界为

$$
\deg_\lambda g\le r\left\lfloor\frac{m-1}{2}\right\rfloor,
$$

并由命题 4.9 的下界取等号。

**证明。** 引理 3.4 把节点本征向量的存在等价为 $p,Q$ 有公共根，定理 11.1 给出这些公共根的全部首一因子与重数。命题 4.9 的无平方因子性和次数给出不同根的数目。对固定谱值，若 $z_q=z_{q+1}=0$，由每一步可逆的本征递推得到 $z=0$；因此在节点本征向量空间上，线性映射 $z\mapsto z_{q+1}$ 是单射，存在性使其为到 $F$ 的同构。这也就是定理 3.6 (1) 的归一化结论。∎

## 追加锚（本行以下为增补区）

## 12. 带内迹因子的不可约性与特化异常

**约定 12.1（系数域与辅助多项式）。** 沿用定理 11.1 的整数 $r,m\ge3$、$L=rm$、指定站点 $q=(m-1)r+1$、实际圈矩阵 $H$、主子矩阵 $H^{(q)}$、特征多项式 $p,Q$ 与 $K=\mathbb R(t)$。$a,b,\sigma_r$ 及 $S_n,\Psi_m$ 沿用该定理与约定 2.4。记

$$
X=S_{r-1}(a),\qquad Y=S_{r-2}(a),\qquad Z=S_{r-3}(a),\qquad
h=\left\lfloor\frac{m-1}{2}\right\rfloor,\qquad
G=(-1)^{rh}\Psi_m(\sigma_r)\in\mathbb R[t][\lambda].
$$

因而 $\sigma_r=bX-2Y$；定理 11.1 给出 $G=g$ 于 $K[\lambda]$。

**引理 12.2（所有带内迹因子的函数域不可约性）。** 对每个整数 $r\ge3$ 和每个实数 $c$，若 $|c|<2$，则 $\sigma_r-c$ 在 $\mathbb R(t)[\lambda]$ 中不可约，其 $\lambda$-次数为 $r$，首项系数为 $(-1)^r$。

**证明。** 先把 $a,b$ 当作代数独立变量。由事实 3.2 的常系数矩阵积公式，

$$
T(a)^{r-1}=\begin{pmatrix}X&-Y\\Y&-Z\end{pmatrix},
\qquad Y^2-XZ=1,
$$

第二式来自 $\det T(a)=1$。关于 $b$ 的一次多项式

$$
E_c=Xb-(2Y+c)\in\mathbb R[a][b]
$$

是本原的：若 $X$ 与 $2Y+c$ 有非常数公因子，取该公因子的一个复根 $\alpha$。恒等式 $Y^2-XZ=1$ 给出 $Y(\alpha)^2=1$，故 $Y(\alpha)=\pm1$，而 $|c|<2$ 蕴含 $2Y(\alpha)+c\ne0$，矛盾。因此 $\gcd_{\mathbb R[a]}(X,2Y+c)=1$。$E_c$ 在 $\mathbb R(a)[b]$ 中是一次多项式，因而不可约；由 Gauss 引理，它在 $\mathbb R[a,b]$ 中不可约。

坐标变换有多项式逆

$$
a=2-\lambda+t,\qquad b=2-\lambda-t,
\qquad t=\frac{a-b}{2},\qquad \lambda=2-\frac{a+b}{2},
$$

所以给出环同构 $\mathbb R[a,b]\simeq\mathbb R[t,\lambda]$。在该同构下，$E_c$ 变为 $\sigma_r-c$，仍不可约。$S_{r-1}$ 首一、次数为 $r-1$，故 $bX$ 的 $\lambda$-首项为 $(-1)^r\lambda^r$，而 $2Y+c$ 的 $\lambda$-次数至多为 $r-2$。于是 $\sigma_r-c$ 在 $\mathbb R[t][\lambda]$ 中的首项系数为单位 $(-1)^r$，从而本原。再次应用 Gauss 引理，得到它在 $\mathbb R(t)[\lambda]$ 中不可约。

两次 Gauss 引理分别用于系数环 $\mathbb R[a]$ 与 $\mathbb R[t]$；所用标准工具见 S. Lang，*Algebra*，修订第三版，第 IV 章 §2。本引理将定理 6.5 的 $r=3$ 结论扩展到全部 $r\ge3$ 和全部实数 $|c|<2$。∎

**定理 12.3（节点因子的完整首一不可约分解）。** 在约定 12.1 的条件下，置

$$
c_k=2\cos\frac{2\pi k}{m},\qquad
f_k=(-1)^r(\sigma_r-c_k),\qquad 1\le k\le h.
$$

定理 11.1 的节点因子有完整分解

$$
\boxed{\displaystyle g=G=\prod_{k=1}^{h}f_k\quad\text{于 }\mathbb R(t)[\lambda].}
$$

每个 $f_k$ 都首一、不可约且次数为 $r$；不同 $k$ 的因子两两不相伴，每个因子的重数恰为 $1$。此外 $G$ 在 $\mathbb R[t][\lambda]$ 中同时整除 $p,Q$。对每个实数 $t_0$，每个 $f_k(\lambda,t_0)$ 在 $\mathbb R[\lambda]$ 中分解为 $r$ 个不同的一次因子。

**证明。** 由约定 2.4，各 $c_k$ 在 $(-2,2)$ 内两两不同。引理 12.2 给出各 $f_k$ 首一、不可约且次数为 $r$。若 $f_k$ 与 $f_\ell$ 相伴，首一性使二者相等，比较二者的常数差便得 $c_k=c_\ell$，从而 $k=\ell$。依约定 2.4 展开 $\Psi_m$，再直接应用定理 11.1 的精确 gcd 恒等式，即得所示分解和全部重数。

用首一多项式 $G$ 除 $p,Q$，带余除法在 $\mathbb R[t][\lambda]$ 中进行；余式在 $K[\lambda]$ 中由 $G=g$ 为零，所以本来就为零。这给出原系数环中的整除。最后，对块 $u_r=-+^{r-1}$ 与带内值 $c_k$ 应用事实 4.8，各实特化都有 $r$ 个实单根，故得到所述一次因子分解。函数域的不可约性与实特化的一次分解分别属于不同的系数域。∎

**命题 12.4（公共因子的全实特化与有限升阶集合）。** 固定整数 $r,m\ge3$。对每个实数 $t_0$，$G(\lambda,t_0)$ 都是 $p(\lambda,t_0),Q(\lambda,t_0)$ 的次数为 $rh$ 的首一公共因子。令 $P_1,Q_1\in\mathbb R[t][\lambda]$ 为首一商

$$
p=GP_1,\qquad Q=GQ_1,
$$

并定义

$$
\mathcal R_{r,m}(t)=\operatorname{Res}_\lambda(P_1,Q_1).
$$

则 $\mathcal R_{r,m}\in\mathbb R[t]\setminus\{0\}$，且对每个实数 $t_0$ 有

$$
\operatorname{monic\_gcd}_{\mathbb R[\lambda]}
 \bigl(p(\lambda,t_0),Q(\lambda,t_0)\bigr)=G(\lambda,t_0)
\quad\Longleftrightarrow\quad \mathcal R_{r,m}(t_0)\ne0.
$$

因此，重新求得的特化 gcd 次数超过 $rh$ 的实耦合集合，恰为 $\mathcal R_{r,m}$ 的实零点集，且为有限集。

**证明。** 定理 12.3 给出原系数环中的首一整除；由于 $p,Q,G$ 都关于 $\lambda$ 首一，商 $P_1,Q_1$ 也首一。定理 11.1 的 $G=g$ 说明 $P_1,Q_1$ 在 $K[\lambda]$ 中互素，故其结式非零。首一性使 $G,P_1,Q_1$ 在每个实特化下保持次数，并使结式与特化交换。于是于 $\mathbb R[\lambda]$ 有

$$
\operatorname{monic\_gcd}\bigl(p(\lambda,t_0),Q(\lambda,t_0)\bigr)
 =G(\lambda,t_0)\,
  \operatorname{monic\_gcd}\bigl(P_1(\lambda,t_0),Q_1(\lambda,t_0)\bigr).
$$

最后一个 gcd 为 $1$，当且仅当 $\mathcal R_{r,m}(t_0)\ne0$；若不为 $1$，其次数为正。非零一元多项式只有有限个实零点，遂得全部结论。这里的结式与特化性质是标准工具，见 Lang 同书第 IV 章 §8，亦即母卷定理 3.2 与本卷引理 7.1 所用的性质。∎

**命题 12.5（非零耦合的额外节点根）。** 对实际缺陷圈 $r=5,m=3$，有 $L=15$、$q=11$。取 $t_0=1/2$，则 $\lambda-3/2$ 同时整除 $p(\lambda,t_0)$ 与 $Q(\lambda,t_0)$，却不整除 $G(\lambda,t_0)$。特别地 $\mathcal R_{5,3}(1/2)=0$，且这个特化后的首一 gcd 次数严格大于 $5$。

**证明。** 令 $H_0,p_0,C$ 如定理 11.1 证明中式 (11.1)–(11.3)，并记 $A=T(a)$、$B=T(b)$、$D=bY-Z$。由事实 3.2，$A^{r-2}$ 的第一列为 $(Y,Z)^{\mathsf T}$，故

$$
Ce_1=ABA^{r-2}e_1
 =A\begin{pmatrix}bY-Z\\Y\end{pmatrix}
 =\begin{pmatrix}aD-Y\\D\end{pmatrix},
\qquad C_{21}=D.
$$

记

$$
s_m(x)=S_{m-1}(x),\qquad
F_m(x)=xS_{m-1}(x)-2\bigl(S_{m-2}(x)+1\bigr).
$$

直接对式 (11.3) 使用事实 4.1 的幂公式并取相应矩阵元与迹，得到

$$
Q=(-1)^{L-1}s_m(\sigma_r)D,\qquad
p_0=(-1)^L F_m(\sigma_r),\qquad p=p_0+2tQ.
$$

这些公式使用实际圈的周期边界和实际删点主子矩阵，后者的剩余对角元仍是 $2+tU_i$。周期 Jacobi 的相应单值约定见 G. Teschl，*Jacobi Operators and Completely Integrable Nonlinear Lattices*，§7.1；其半迹判别式在此为 $\sigma_r/2$。S. Roy，[*A spectral viewpoint on the single defect tight-binding chain*](https://arxiv.org/html/2607.29467v1)，§2 式 (1)–(4)、(10)，讨论的是均匀周期背景上的单点缺陷及零振幅态；这里的周期背景是块 $u_5$ 的重复，上式由本卷的矩阵公式给出。

在 $\lambda=3/2,t=1/2$ 处，$a=1,b=0$，而约定 2.4 的递推给出

$$
X=S_4(1)=-1,\qquad Y=S_3(1)=-1,\qquad Z=S_2(1)=0,
\qquad D=0,\qquad \sigma_5=2.
$$

所以 $Q=0$；又 $F_3(2)=2S_2(2)-2(S_1(2)+1)=6-6=0$，故 $p_0=p=0$。另一方面 $h=1$、$\Psi_3(x)=x+1$，从而

$$
G(3/2,1/2)=(-1)^5\Psi_3(2)=-3\ne0.
$$

由因式定理，$\lambda-3/2$ 是特化后额外出现的公共因子；结合命题 12.4 得到结式取零与次数严格增加。∎

## 追加锚（本行以下为增补区）

## 13. 两倍奇素数圈上的节点次数饱和

**约定 13.1（实际圈、谱坐标与目标）。** 本章至第 17 章中，$p\ge3$ 为奇素数，$L=2p$，所有站点均为带标号的 $\mathbb Z/(2p)\mathbb Z$。每条边权与每个顶点质量均为 $1$，

$$
H_t=2I-A_{2p}+t\operatorname{diag}(v),\qquad
P(\lambda,t)=\det(\lambda I-H_t),\qquad
Q_j(\lambda,t)=\det(\lambda I-H_t^{(j)}).
$$

$H_t^{(j)}$ 仅同时删除第 $j$ 行列；其余对角元仍为 $2+tv_i$，不改为删点后图的度数。首一 gcd 记为 $g_j\in\mathbb R(t)[\lambda]$。持续节点、$\operatorname{Bad}(v)$ 与 $\operatorname{Shared}(v)$ 分别采用约定 2.1 以及母卷约定 2.4、2.5；特别地，

$$
\operatorname{Shared}(v)\iff
\exists O\in O(2p,\mathbb R),\quad
O\ne I,\ O\ne-I,\quad
O\Delta_{2p}=\Delta_{2p}O,\quad
O\operatorname{diag}(v)=\operatorname{diag}(v)O.
$$

这里的 $O$ 遍历实际实正交矩阵。开放问题 8.5 对应的断言为

$$
T:\quad \forall\text{奇素数 }p\ge11\quad
\forall v\in\{-1,1\}^{2p},\qquad
\operatorname{Bad}(v)\Longrightarrow\operatorname{Shared}(v).
\tag{13.1}
$$

下文采用 $x=2-\lambda$。关于 $\lambda$ 的首一多项式 $f$ 的 $x$ 坐标首一版本为 $(-1)^{\deg f}f(2-x,t)$。长度 $p-1$ 为偶数，因而该长度的连分式行列式在两种坐标下均首一。

**约定 13.2（自由节点多项式）。** 置 $n=p-1$、$h=(p-1)/2$，并记

$$
D_p(x)=S_{p-1}(x)=\prod_{k=1}^{p-1}\left(x-2\cos\frac{\pi k}{p}\right)
\tag{13.2}
$$

**定理 13.3（有理势的节点次数饱和）。** 对每个 $v\in\mathbb Q^{2p}$ 与每个站点 $j$，有

$$
\deg_\lambda g_j\in\{0,p-1\}.
\tag{13.3}
$$

若 $g_j\ne1$，则 $g_j\in\mathbb Q[t][\lambda]$，且

$$
g_j(\lambda,0)=S_{p-1}(2-\lambda).
\tag{13.4}
$$

$g_j$ 在函数域上无重根。当 $g_j\ne1$ 时，对每个实数 $t_0$，$g_j(\lambda,t_0)$ 都有恰好 $p-1$ 个不同实根，并是实际 $P(\lambda,t_0),Q_j(\lambda,t_0)$ 的首一公共因子。这些根均给出站点 $j$ 的实际节点本征向量。

更精确地，允许 $g_j=1$，写 $P=g_jP_1$、$Q_j=g_jQ_1$，则 $P_1,Q_1\in\mathbb Q[t][\lambda]$ 首一，

$$
R_j(t)=\operatorname{Res}_\lambda(P_1,Q_1)\ne0,
$$

且每个实数 $t_0$ 都满足

$$
\operatorname{monic\_gcd}(P(\cdot,t_0),Q_j(\cdot,t_0))
 =g_j(\cdot,t_0)\operatorname{monic\_gcd}(P_1(\cdot,t_0),Q_1(\cdot,t_0)).
\tag{13.5}
$$

因此重新求取的实特化 gcd 仅在有限个耦合处升阶，其升阶集合恰为 $R_j$ 的实零点；所有这些特化 gcd 均无重根。

**证明。** 母卷注 3.4 允许在 $\mathbb Q(t)$ 内计算同一个 gcd；母卷定理 3.2 的整闭论证给出首一因子及其商均在 $\mathbb Q[t][\lambda]$。以下不重新证明该定理的全实耦合准则。

下面使用经典分圆输入：$D_p$ 的根组成两个互异的有理共轭轨道，每个含 $h$ 个根，取负交换这两个轨道。故 $D_p$ 的根集在取负下封闭的首一有理因子只能是 $1$ 或 $D_p$。Chebyshev 根公式取自约定 2.4。令 $\zeta=\exp(2\pi i/p)$。偶数 $k$ 对应的根为 $\zeta^a+\zeta^{-a}$，$a\in(\mathbb Z/p\mathbb Z)^\times/\{\pm1\}$。经典的素数分圆多项式不可约性给出 $[\mathbb Q(\zeta):\mathbb Q]=p-1$；又 $\zeta$ 满足 $Z^2-(\zeta+\zeta^{-1})Z+1=0$，且 $\mathbb Q(\zeta+\zeta^{-1})\subset\mathbb R$、$\zeta\notin\mathbb R$，故这个实子域的次数恰为 $h$。分圆自同构传递地作用于上述 $h$ 个不同的根，它们组成一个不可约因子的根集。其余奇数 $k$ 的根恰为这些根的相反数，也组成一个不可约因子；两根集不交，因为 $\cos(\pi k/p)$ 在 $1\le k\le p-1$ 上严格递减，而 $p-k$ 与 $k$ 奇偶相反。偶因子的根集在取负下封闭，故只能同时包含这两个有理轨道，或都不包含。分圆不可约性是经典输入；Lindblad–Guerrero [LG] 命题 4.1 的证明也使用 $\Phi_p(Z)=1+\cdots+Z^{p-1}$ 的这一性质。

在 $t=0$，实际删点矩阵是对角元 $2$ 的 $2p-1$ 阶 Dirichlet 路矩阵，故

$$
Q_j(\lambda,0)=\prod_{\ell=1}^{2p-1}
 \left(\lambda-2+2\cos\frac{\pi\ell}{2p}\right).
$$

自由圈的本征值为 $2-2\cos(\pi k/p)$，$0\le k\le2p-1$。$0,4$ 各为单本征值，其余 $p-1$ 个不同本征值各为二重；它们在上述路谱中恰对应 $\ell=2k$，$1\le k\le p-1$，各出现一次。所以自由圈的首一特化 gcd 恰为 $S_{p-1}(2-\lambda)$，每个 $g_j(\lambda,0)$ 均为它的首一有理因子，且次数不降。

令 $J=\operatorname{diag}((-1)^i)$。实际偶圈满足

$$
JH_tJ=4I-H_{-t},
$$

删除 $j$ 行列后同式成立。故若 $d=\deg g_j$，gcd 的唯一首一性给出

$$
g_j(\lambda,t)=(-1)^d g_j(4-\lambda,-t).
\tag{13.6}
$$

在 $t=0$，其根集在 $\lambda\mapsto4-\lambda$ 下封闭，亦即在 $x\mapsto-x$ 下封闭。上述分圆轨道结论迫使这个根集为空或为全部自由节点根集，证明式 (13.3)、(13.4)。

对任意实数 $t_0$，$H_{t_0}^{(j)}$ 为非零相邻非对角元的实对称三对角矩阵。它的本征向量由第一个坐标和零 Dirichlet 边界唯一确定；第一个坐标为零就使全部坐标为零。因此每个本征空间至多一维，实对称性使全部本征值实且简单。于是每个 $Q_j(\cdot,t_0)$ 无重根，特别地 $Q_j$ 在函数域上无重根。首一整除保留全部实特化的次数，故 $g_j\mid Q_j$ 给出全部所述重数结论。节点向量的存在及其实值性直接采用母卷定理 3.2。

最后，函数域 gcd 恰为 $g_j$，故 $P_1,Q_1$ 互素、$R_j\ne0$。首一性允许结式与每个实特化交换；在 $\mathbb R[\lambda]$ 中提出共同因子即得式 (13.5)。其额外 gcd 为正次数恰当 $R_j(t_0)=0$，非零一元多项式的实零点有限。∎

## 14. 配对和的反射障碍与二重复块族

**定义 14.1（对径配对和）。** 对 $v\in\mathbb Q^{2p}$，定义 $p$ 周期序列

$$
w_r=v_r+v_{r+p},\qquad r\in\mathbb Z/p\mathbb Z.
$$

称 $w$ 关于剩余类 $c$ 反射，若 $w_{c+r}=w_{c-r}$ 对全部 $r$ 成立。实际圈中剩余类 $c$ 对应对径顶点对 $\{c,c+p\}$。

**定理 14.2（持续节点迫使配对和反射）。** 若 $v\in\mathbb Q^{2p}$ 在站点 $j$ 有持续节点，则 $w$ 关于 $j\bmod p$ 反射。若 $w$ 非常数，至多一个剩余类能成为反射中心，因而持续节点只能位于一个对径顶点对中。若 $w$ 没有反射中心，则 $v$ 是好势：除有限个实际实耦合外，$H_t$ 谱简单且全部本征向量各坐标非零。

**证明。** 定理 13.3 保证每个自由节点值

$$
\lambda_k=2-2\cos\theta_k,\qquad \theta_k=\frac{\pi k}{p},\quad1\le k\le p-1,
$$

都由 $g_j$ 的根延拓。由于 $g_j(\cdot,0)$ 与 $Q_j(\cdot,0)$ 在这些值处均为单根，隐函数定理给出局部实解析根 $\lambda_k(t)$。以 $z_j(t)=0$、$z_{j+1}(t)=1$ 和实际本征递推归一化，得到解析节点向量；其余闭合条件由 $g_j\mid P,Q_j$ 与本卷定理 3.6 保证。$t=0$ 时该向量是

$$
s_i=\frac{\sin(\theta_k(i-j))}{\sin\theta_k}.
$$

令 $c_i=\cos(\theta_k(i-j))$。自由圈上 $c,s$ 是同一本征值的正交本征向量。对 $H_tz(t)=\lambda_k(t)z(t)$ 在零处求导并与 $c$ 取内积，自由矩阵的对称性及 $\langle c,s\rangle=0$ 给出 $\langle c,Vs\rangle=0$，即

$$
\sum_{i=0}^{2p-1}v_i\sin\frac{2\pi k(i-j)}p=0,
\qquad1\le k\le p-1.
\tag{14.1}
$$

这一步不假设实际圈在零处或非零耦合处谱简单；只使用实际删点路的单根。配对 $i$ 与 $i+p$，式 (14.1) 说明 $p$ 点序列 $r\mapsto w_{j+r}$ 的全部离散傅里叶系数均为实数。于是奇部 $w_{j+r}-w_{j-r}$ 的全部傅里叶系数为零；傅里叶矩阵可逆，奇部为零。这就是所需反射。

若 $w$ 同时关于不同剩余类 $c,d$ 反射，则两反射的合成是非零平移 $2(c-d)$。因为 $p$ 是奇素数，该平移生成全部 $\mathbb Z/p\mathbb Z$，迫使 $w$ 为常数。最后，若无反射，所有站点均无持续节点；母卷推论 3.3 直接给出好势与有限例外耦合的结论。∎

**推论 14.3（整个 $U_{p,2}$ 族为好势）。** 对每个奇素数 $p\ge3$，实际 $C_{2p}$ 上定义 6.1 的

$$
U_{p,2}=(-+^{p-1})(--+^{p-2})
$$

是好势，同时其共享交换子仅含数量矩阵。

**证明。** 配对和为

$$
w_0=-2,\qquad w_1=0,\qquad w_r=2\quad(r\ne0,1).
$$

若有反射，它必须固定唯一取 $-2$ 的剩余类 $0$，故中心为 $0$；又必须固定唯一取 $0$ 的剩余类 $1$，迫使 $1=-1\pmod p$，矛盾。因此定理 14.2 给出好势。共享交换子结论直接复用定理 6.2 (1) 的 $r\ge3,m\ge2$ 范围，取 $r=p,m=2$；其代数输入也见 [F]。定理 6.2 (2) 与缺陷坏势机制仍要求 $m\ge3$，本推论不把该条件改成 $m\ge2$。∎

## 15. 保留两条半圆方向的多项式闭合

**定义 15.1（有序开半圆与端部多项式）。** 固定站点 $j$，置 $a=j+p$、$n=p-1$，定义两个从 $j$ 向 $a$ 行走的实际有序势字

$$
u=(v_{j+1},\ldots,v_{j+p-1}),\qquad
z=(v_{j-1},\ldots,v_{j-p+1}).
$$

这里 $z$ 表示势字；以下节点向量另记 $\psi$。对任意势字 $b=(b_1,\ldots,b_k)$，令

$$
\mathcal K_b(x,t)=K_k(x+tb_1,\ldots,x+tb_k),\qquad\mathcal K_\varnothing=1.
$$

本卷事实 3.2 的 continuant 是所用输入。记

$$
F=\mathcal K_u,\quad G=\mathcal K_z,\quad
B=\mathcal K_{(u_1,\ldots,u_{n-1})},\quad
D=\mathcal K_{(z_1,\ldots,z_{n-1})},\quad d_a=x+tv_a,
$$

$$
M=\frac{F+G}{2},\qquad E=d_aF-B+D,\qquad
\delta=\sum_{r=1}^n u_r-\sum_{r=1}^n z_r.
\tag{15.1}
$$

$B,D$ 删去的是各自有序字的末位，因而不能只用无方向的半圆谱代替这些数据。

**引理 15.2（每个实耦合的精确闭合）。** 对任意实际实势 $v$、任意实数 $t_0$ 与任意复数 $x_0$，存在满足 $\psi_j=0$ 的非零实际圈本征向量，谱值为 $\lambda_0=2-x_0$，当且仅当

$$
(F+G)(x_0,t_0)=0,\qquad E(x_0,t_0)=0.
\tag{15.2}
$$

这时可唯一归一化为 $\psi_{j+1}=1$，且 $\psi_{j-1}=-1$、$\psi_a=F(x_0,t_0)=-G(x_0,t_0)$。若条件成立，$x_0$ 为实数，归一化向量为实向量。

**证明。** 站点 $j$ 的方程给出 $\psi_{j-1}=-\psi_{j+1}$。后者不能为零，否则连续两个零坐标经可逆递推迫使全部坐标为零。取归一化值 $1,-1$。沿第一条半圆，事实 3.2 的递推给出

$$
\psi_{j+r}=K_{r-1}(x+tu_1,\ldots,x+tu_{r-1}),\quad1\le r\le p,
$$

沿第二条半圆给出相同公式的负值，字母换成 $z$。两者在 $a$ 处一致恰当 $F=-G$。到达 $a$ 前的两个坐标分别为 $B,-D$，故 $a$ 处方程恰为 $d_aF-B+D=0$。其余站点方程已由递推满足；$j$ 处方程也已满足。因此式 (15.2) 充分且必要，并实际重构了原圈向量。实际实对称矩阵的本征值实，故 $x_0$ 实；所有归一化递推系数也实。此证明未除以 $F,G,B,D$ 中任一个，不排除 $\psi_a=0$ 或任何实耦合。∎

**定理 15.3（有理势的恒等式判据与二值势的和约束）。** 对 $v\in\mathbb Q^{2p}$，站点 $j$ 持续，当且仅当 $M\mid E$ 于 $\mathbb Q(t)[x]$；等价地，以下是 $\mathbb Q[x,t]$ 中的恒等式：

$$
E=\left(d_a+\frac{t\delta}{2}\right)M.
\tag{15.3}
$$

条件成立时，$M$ 就是定理 13.3 的节点因子的 $x$ 坐标版本。对每个实数 $t_0$，$M(\cdot,t_0)$ 恰有 $p-1$ 个不同实根，每一个都按引理 15.2 给出原圈节点向量。

若进一步 $v\in\{-1,1\}^{2p}$，持续性必迫使

$$
\boxed{\ \sum_{r=1}^{p-1}v_{j+r}=\sum_{r=1}^{p-1}v_{j-r}.\ }
\tag{15.4}
$$

对这种二值势，持续性等价于式 (15.4) 与下面的有向闭合恒等式同时成立：

$$
\boxed{\ (x+tv_{j+p})(F-G)=2(B-D).\ }
\tag{15.5}
$$

**证明。** 若 $j$ 持续，定理 13.3 给出次数 $n$ 的无重根 $g_j$。在 $\overline{\mathbb Q(t)}$ 中，它的每个根对应实际节点解；引理 15.2 的代数递推同样适用，故这些根均使 $F+G$ 与 $E$ 消失。$M$ 首一且次数恰为 $n$，所以它等于 $g_j$ 的 $x$ 坐标版本，并整除 $E$。比较 $x^{n+1}$、$x^n$ 的系数，商恰为 $x+tv_a+t\delta/2$；这是原多项式环中的首一除法，得到式 (15.3)。

反之，若 $M\mid E$，则 $M$ 在 $t=0$ 等于 $D_p$，故它在函数域上无重根。引理 15.2 的代数递推使 $M$ 的每个根同时为实际圈特征多项式及实际删点多项式的根。无重根性给出 $M$ 同时整除两者；首一性使这两个整除均在 $\mathbb Q[t][x]$ 中成立。母卷定理 3.2 遂给出持续性，定理 13.3 给出 $M$ 的全部实特化断言。也可直接把式 (15.3) 代入引理 15.2，逐根构造每个特化的节点向量。

现在设 $v$ 为二值势，$u,z$ 中的 $+1$ 数量分别为 $b,c$。按 $x,t$ 的总次数取最高齐次部分，

$$
F_n=(x+t)^b(x-t)^{n-b},\qquad
G_n=(x+t)^c(x-t)^{n-c}.
$$

持续时 $M$ 整除实际圈多项式；后者的最高齐次部分为 $\prod_i(x+tv_i)$。故 $M_n=(F_n+G_n)/2$ 的每个 $t=1$ 根只能为 $1$ 或 $-1$。若 $b\ne c$，令 $d=|b-c|\ge1$，提出共同的 $(x+t)$、$(x-t)$ 幂后，$M_n(x,1)$ 含有非常数因子

$$
\frac{(x+1)^d+(x-1)^d}{2}.
$$

该因子在 $x=1,-1$ 均不为零，却有复根，矛盾。因此 $b=c$，即 $\delta=0$，这恰为式 (15.4)。把 $\delta=0$ 代入式 (15.3)，展开 $2E=d_a(F+G)$，得到式 (15.5)。逆向代回同样成立。和约束的这里一项使用了二值假设；它未被宣称为全部有理势的结论。∎

## 16. 全部奇素数的二值反周期分类

**约定 16.1（反周期与实际顶点反射）。** 本章设 $v_i\in\{-1,1\}$ 且

$$
v_{i+p}=-v_i\qquad(i\in\mathbb Z/(2p)\mathbb Z).
\tag{16.1}
$$

站点 $j$ 的实际顶点反射为 $\rho_j(i)=2j-i\pmod{2p}$，固定 $j,j+p$。定义 15.1 中的两条有序字满足

$$
z=(-u_n,\ldots,-u_1).
\tag{16.2}
$$

continuant 在反转序列下不变，因为同时反转行列是矩阵共轭。因此

$$
G(x,t)=F(x,-t)=F(-x,t).
\tag{16.3}
$$

最后一个等式使用 $n$ 偶及 continuant 每个单项式的字母数与 $n$ 同奇偶。

**引理 16.2（半圆公因子的二择）。** 对满足式 (16.1) 的势，$F$ 与 $G=F(x,-t)$ 在 $\mathbb Q(t)[x]$ 中或者互素，或者相等。

**证明。** 设 $d$ 为二者首一 gcd。整闭性给出 $d\in\mathbb Q[t][x]$，且 $d(x,0)\mid D_p(x)$，次数不降。由式 (16.3)，$x\mapsto-x$ 交换 $F,G$ 的根集，故 $d(x,0)$ 的根集在取负下封闭。定理 13.3 证明中的分圆轨道结论迫使 $\deg d=0$ 或 $n$。后一情形两个 $n$ 次首一多项式均等于 $d$。∎

**定理 16.3（反周期势在指定站点的完整分类）。** 对每个奇素数 $p\ge3$、每个满足式 (16.1) 的实际二值势 $v$ 与每个实际站点 $j$，下列条件等价：

1. $v$ 在 $j$ 处有持续节点；
2. $v_{j+r}=v_{j-r}$ 对每个 $r\in\mathbb Z/(2p)\mathbb Z$ 成立；
3. $H_t$ 在一个与 $t$ 无关的非零实子空间上保持不变，该子空间的所有向量在 $j,j+p$ 处均为零，且它是实际反射 $\rho_j$ 的负特征子空间。

当上述等价条件成立时，该反射的置换矩阵 $O_j$ 为实际实正交矩阵，$O_j\ne\pm I$，并与 $\Delta_{2p}$、$\operatorname{diag}(v)$ 同时可交换。

**证明。** 先证 (1)⇒(2)。由定理 15.3，$\delta=0$。结合式 (16.2)，$\sum_r u_r=0$，所以 $u$ 中正负字母各 $h=n/2$ 个。又

$$
M=\frac{F(x,t)+F(x,-t)}2
$$

是实际节点因子，既是 $x$ 的偶多项式，也是 $t$ 的偶多项式。对径平移 $i\mapsto i+p$ 把 $v$ 换成 $-v$，所以把站点 $j$ 的节点 gcd 变成站点 $a=j+p$ 在 $-t$ 下的节点 gcd；$M$ 的 $t$ 偶性表明 $a$ 的节点因子也等于 $M$。

反设 $F\ne G$。引理 16.2 给出 $\gcd(F,G)=1$，从而 $\gcd(F,M)=1$。$M$ 无重根。在 $\overline{\mathbb Q(t)}$ 中，取它的任一根 $x_*$；引理 15.2 给出一个在 $j$ 为零、在 $a$ 为 $F(x_*,t)\ne0$ 的本征向量。同时，$a$ 的节点因子也是 $M$，所以存在同一谱值的、在 $a$ 为零的非零本征向量。后者存在性可直接使用本卷引理 3.4；两个向量线性无关。因此每个 $M$ 根都是实际圈特征多项式的至少二重根。

记实际 $x$ 坐标特征多项式为

$$
\mathcal P(x,t)=\det(xI-A_{2p}+tV)=P(2-x,t).
$$

无重根性给出 $M^2\mid\mathcal P$。$\mathcal P$ 为 $x$ 的偶多项式：对径平移给出 $\mathcal P(x,-t)=\mathcal P(x,t)$，二分符号矩阵 $J$ 给出 $\mathcal P(-x,-t)=\mathcal P(x,t)$。商首一、偶且次数为 $2$，故

$$
\mathcal P=(x^2+c(t))M^2.
\tag{16.4}
$$

这里不假定函数域上实际圈的谱简单；相反，上述步骤完整处理了可能的重谱。

计算 $x^{n-2}$ 的系数。$F$ 是 $n$ 阶路矩阵 $A_{\rm path}-t\operatorname{diag}(u)$ 的特征多项式。该矩阵迹为零，平方迹为 $nt^2+2(n-1)$，故其 $x^{n-2}$ 系数及 $M$ 的对应系数均为

$$
-\frac n2t^2-(n-1).
$$

实际 $2p$ 圈的矩阵 $A_{2p}-tV$ 迹为零，平方迹为 $2pt^2+4p$，其 $x^{2p-2}$ 系数为 $-pt^2-2p$。比较式 (16.4)，使用 $n=p-1$ 得

$$
c(t)=-(t^2+4),\qquad
\mathcal P=(x^2-t^2-4)M^2.
\tag{16.5}
$$

在 $t=0$，$M=D_p$ 的全部根严格位于 $(-2,2)$；根的连续性使充分小的非零实数 $t$ 下，这些根的最大值仍小于 $\sqrt{t^2+4}$。式 (16.5) 遂断言实际实对称矩阵 $A_{2p}-tV$ 的最大本征值为 $\sqrt{t^2+4}$。

令 $\mathbf1=(1,\ldots,1)^{\mathsf T}$。反周期性给出 $\sum_i v_i=0$，而二值性给出 $Vv=\mathbf1$、$\|v\|^2=\|\mathbf1\|^2=2p$。在正交标准基 $\mathbf1/\sqrt{2p},v/\sqrt{2p}$ 上，$A_{2p}-tV$ 的压缩矩阵为

$$
\begin{pmatrix}2&-t\\-t&\gamma\end{pmatrix},\qquad
\gamma=\frac{v^{\mathsf T}A_{2p}v}{2p}
       =\frac1p\sum_{i=0}^{2p-1}v_iv_{i+1}\ge-2.
\tag{16.6}
$$

当 $\gamma=-2$ 时该矩阵的最大本征值为 $\sqrt{t^2+4}$。对 $t\ne0$，这个最大本征值随 $\gamma$ 严格增加；由显式公式

$$
\frac{2+\gamma+\sqrt{(2-\gamma)^2+4t^2}}2
$$

求导即可验证。因此若 $\gamma>-2$，式 (16.6) 中的压缩矩阵已有大于 $\sqrt{t^2+4}$ 的 Rayleigh 商，与实际矩阵的最大本征值矛盾。必有 $\gamma=-2$，而每个 $v_iv_{i+1}\in\{-1,1\}$，所以全部相邻乘积均为 $-1$。势字严格交替，因而 $u=z$、$F=G$，与反设矛盾。故实际上 $F=G$。

持续闭合恒等式 (15.5) 随即给出 $B=D$。现在 $F=G$ 与 $B=D$ 保留了两个字的方向，足以逐字重构：若 $K_n$ 与其删末位的 $K_{n-1}$ 已知，continuant 递推

$$
K_n=(x+tu_n)K_{n-1}-K_{n-2}
$$

的首一带余除法唯一恢复商 $x+tu_n$ 及余式 $-K_{n-2}$；两字的商相等，故 $u_n=z_n$。递归下去恢复全部字母。因此 $u=z$。$j$ 与 $a$ 是反射不动点，其余站点按这两个字对应，遂有 $v\circ\rho_j=v$，即 (2)。

若 (2) 成立，令 $(O_j\psi)_i=\psi_{2j-i}$。它是实正交置换矩阵，$O_j^2=I$；它交换 $j+1,j-1$，故不为 $I$，又因有正的对角元而不为 $-I$。反射保持实际圈邻接关系及势，故与 $\Delta_{2p},V$ 可交换。负特征子空间

$$
W_j=\{\psi:O_j\psi=-\psi\}
 =\operatorname{span}_{\mathbb R}\{e_{j+r}-e_{j-r}:1\le r\le p-1\}
$$

维数为 $p-1>0$，所有向量在 $j,a$ 为零，并对每个实际实数 $t$ 同时为 $H_t$ 的不变子空间。这证明 (2)⇒(3)。每个 $H_t|_{W_j}$ 实对称且作用于非零空间，因此有非零实本征向量，原圈中的延拓仍在 $j$ 为零。母卷定理 3.2 给出 (3)⇒(1)，且这一方向对全部实耦合成立。∎

**推论 16.4（反周期坏势当且仅当具有实际顶点反射）。** 对每个奇素数 $p\ge3$ 与每个满足式 (16.1) 的二值势，

$$
\operatorname{Bad}(v)
\iff\exists j\ \forall i,\ v_{2j-i}=v_i.
\tag{16.7}
$$

特别地，这整个类满足 $\operatorname{Bad}(v)\Rightarrow\operatorname{Shared}(v)$；若坏势的持续站点为 $j$，则实际反射就是 $\rho_j$。

**证明。** 母卷推论 3.3 把坏势等价为某个站点持续；定理 16.3 分别给出两个方向及实际正交矩阵。∎

## 17. 原域剩余类与数学依赖

**命题 17.1（断言 $T$ 的精确剩余推断）。** 对断言 (13.1)，下列类别均已满足其蕴含：配对和 $w$ 无反射的二值势；$w$ 为常数的二值势；以及在 $w$ 的某个反射中心处具有实际顶点反射的二值势。对其余势，只可能有一个配对和反射中心 $c\in\mathbb Z/p\mathbb Z$，持续站点仅能为 $c$ 或 $c+p$。在这样的候选站点 $j$，仍未判定的一般推断为

$$
\begin{gathered}
p\ge11\text{ 为奇素数},\quad v\in\{-1,1\}^{2p},\quad
w\text{ 非常数且关于 }j\bmod p\text{ 反射},\\
\sum_{r=1}^{p-1}v_{j+r}=\sum_{r=1}^{p-1}v_{j-r},\qquad
u\ne z,\qquad
(x+tv_{j+p})(F-G)=2(B-D)
\end{gathered}
\quad\Longrightarrow\quad\operatorname{Shared}(v).
\tag{17.1}
$$

其中 $u,z,F,G,B,D$ 均为定义 15.1 的实际有序半圆数据。若式 (17.1) 对全部这样的势成立，则 $T$ 成立；若 $T$ 成立，则式 (17.1) 成立。本章各结果未证明式 (17.1)，也未给出它或 $T$ 的反例。

**证明。** 无配对和反射时，定理 14.2 已给出好势。若 $w$ 为常数，其值只可能为 $-2,0,2$；取 $\pm2$ 迫使 $v$ 为常数，实际非单位旋转便是共享正交对称；取 $0$ 正是式 (16.1)，采用推论 16.4。若有实际顶点反射，该置换矩阵直接给出 $\operatorname{Shared}$。其余类别的反射中心与候选站点限制由定理 14.2 给出。在候选站点，定理 15.3 的必要和约束不成立或有向恒等式不成立时，该站点不持续；两候选站点均不持续时，母卷推论 3.3 给出好势。剩下的恰为式 (17.1) 的前提；其中 $u\ne z$ 表示该候选站点的实际顶点反射不保持势。定理 15.3 又保证前提中的恒等式与和约束确实给出坏势。因此 $T$ 与对这一剩余类的蕴含等价。∎

**注 17.2（对称的量词与适用边界）。** 式 (17.1) 的结论仍对约定 13.1 的全部实际共同正交对称量化。没有可见二面体对称不能推出没有这样的正交对称；某个依赖耦合的矩阵对称也不能给出同时与 $\Delta,V$ 可交换的一个固定矩阵。定理 15.3 使用的两个有序势字和引理 15.2 的重构均直接属于原实际圈，未以辅助等谱对象代替原域。某个更强的辅助证书若不成立，不构成式 (13.1) 的反例。推论 14.3 结算了全部奇素数的 $U_{p,2}$ 好势性；其结论与 $m\ge3$ 时缺陷族的坏势性具有不同参数范围。

**数学来源与新增推断。** 母卷定理 3.2、推论 3.3 与注 3.4 提供持续节点准则、好坏二分的结式形式及有理系数下降；这些结果在这里直接使用。本卷事实 3.2、定理 3.6 提供 continuant、单值及节点归一化；定理 6.2 (1) 提供推论 14.3 的共享交换子结论。分圆域的有理轨道、实对称矩阵的谱定理与 Rayleigh 商、单根的隐函数定理、Gauss 引理和结式的实特化是经典中间工具。定理 13.3 的两轨道饱和推断，定理 14.2 的配对和障碍及其无穷族应用，定理 15.3 的有向闭合与二值和约束，以及定理 16.3 的反周期分类是这里给出的数学推导；它们不作为所引文献的结论陈述。

| 引用 | 数学内容与实际使用范围 |
| --- | --- |
| [LG] O. Lindblad, E. Guerrero, *Simple Eigenvalues and Non-vanishing Eigenvectors of the Anderson Model*, [arXiv:2512.00278v1](https://arxiv.org/html/2512.00278v1)，定义 1.1、命题 2.3、引理 3.2、命题 4.1 及其式 (4)–(7) | 实际算子 $\Delta+tV$、好坏势、共同正交对称机制；命题 4.1 处理素数圈，证明中的分圆及一阶 Fourier 关系是定理 13.3、14.2 所用经典方法的对应。这里的 $C_{2p}$ 结论不由该素数圈命题直接推出；定理 14.2 使用全部饱和节点根，未假设一阶劈裂非零。 |
| [J] G. Teschl, *Jacobi Operators and Completely Integrable Nonlinear Lattices*, AMS，Mathematical Surveys and Monographs 72，2000，[作者全文](https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf)，§7.1 | 周期 Jacobi 传递矩阵及 Floquet 半迹；对应 Jacobi 系数 $a(k)=-1,b(k)=2+tv_k$，谱参数 $\lambda$。本章实际行列式与端部约定直接采用本卷事实 3.2，不以一个自由端路 Laplace 矩阵替代实际主子矩阵。 |
| [A] S. Lang, *Algebra*, 修订第三版，Springer，2002，第 IV 章 §2、§8 | Gauss 引理、首一 gcd、结式及特化；用于定理 13.3、15.3 与引理 16.2 的系数域及多项式整除。 |
| [M] R. A. Horn, C. R. Johnson, *Matrix Analysis*, 第二版，Cambridge，2013，§4.2–4.3 | 实对称谱、Rayleigh 商与实际主子矩阵的谱关系；定理 16.3 中的二维压缩保持同一实际矩阵，比较方向为压缩的最大 Rayleigh 商不超过全矩阵最大本征值。 |
| [F] `D5/S3/Combinatorics/Graph/Walks/AndersonDefectFamily.lean` 的 `defect_family`，及其输入 `AndersonDefectSeed.lean` 的 `defect_diagonal_seed` | 既有缺陷族代数：$r\ge3,m\ge2$ 的共享交换子结论；同一族的节点与坏势结论另要求 $m\ge3$。这里只消费前者的参数范围，不重复推导这些代数结论。 |

## 追加锚（本行以下为增补区）
## 18. 两个对径持续站点的实际反射分类

**定义 18.1（逐耦合持续性与两个独立的存在量词）。** 设 $p\ge3$ 为奇素数，实际带标号圈为 $\mathbb Z/(2p)\mathbb Z$，边权和顶点质量均为 $1$，$v\in\{-1,1\}^{2p}$，并沿用约定 13.1 的 $H_t$。记

$$
\mathsf N_j(v)\iff
\forall t\in\mathbb R\ \exists\lambda\in\mathbb R\
\exists\psi\in\mathbb R^{2p}\setminus\{0\},\qquad
H_t\psi=\lambda\psi,\quad\psi_j=0.
\tag{18.1}
$$

母卷定理 3.2 将此条件与约定 2.1 的持续节点等同。$\mathsf N_j(v)\land\mathsf N_{j+p}(v)$ 中的两个存在量词分别属于各自的站点和耦合；不要求预先选定同一本征值、同一本征向量或与 $t$ 无关的向量。

**定理 18.2（全部二值势的两个对径持续站点分类）。** 对每个奇素数 $p\ge3$、每个上述实际二值势 $v$ 和每个带标号站点 $j$，有

$$
\boxed{\quad
\mathsf N_j(v)\land\mathsf N_{j+p}(v)
\quad\Longleftrightarrow\quad
\forall i\in\mathbb Z/(2p)\mathbb Z,\quad v_{2j-i}=v_i.
\quad}
\tag{18.2}
$$

右端成立时，一个同时与原矩阵 $\Delta_{2p}$、$\operatorname{diag}(v)$ 可交换的固定实际实正交矩阵为

$$
(O_j\psi)_i=\psi_{2j-i},\qquad O_j\ne I,\quad O_j\ne-I.
\tag{18.3}
$$

**证明。** 置 $a=j+p$、$n=p-1$。沿用定义 15.1 的实际有序字 $u,z$ 和多项式 $F,G,B,D,M$。从 $a$ 的正、负方向走向 $j$ 时，有序开半圆字分别为 $\operatorname{rev}z$、$\operatorname{rev}u$；continuant 的反转不变性给出相应多项式分别为 $G,F$。因此，如果两个站点都持续，定理 15.3 给出的两个首一节点因子在 $x$ 坐标下都是

$$
M=\frac{F+G}{2},\qquad \deg_xM=n.
\tag{18.4}
$$

这里使用的是实际主子矩阵和实际有向重构，不需要实际圈的谱简单。定理 13.3 给出 $M$ 无重根及 $M(x,0)=D_p(x)$，定理 15.3 的二值和约束给出

$$
s:=\sum_{r=1}^n u_r=\sum_{r=1}^n z_r.
\tag{18.5}
$$

先说明此处可用于任意两个有理字的一个二择推断。若 $b,c\in\mathbb Q^n$，令 $F_b=\mathcal K_b$、$F_c=\mathcal K_c$，并在 $\mathbb Q(t)[x]$ 中取首一 gcd $d$。首一因子的整闭性使 $d$ 及其商属于 $\mathbb Q[t][x]$，故 $d(x,0)\mid D_p(x)$，且次数不降。三对角行列式的二分符号共轭给出

$$
F_b(-x,-t)=(-1)^nF_b(x,t),\qquad
F_c(-x,-t)=(-1)^nF_c(x,t).
$$

gcd 的首一唯一性遂给出 $d(x,t)=(-1)^{\deg d}d(-x,-t)$。因此 $d(x,0)$ 的根集在取负下封闭。直接使用定理 13.3 证明中的两个有理分圆轨道：$D_p$ 的首一有理因子若具有这种根集，只能为 $1$ 或 $D_p$。所以

$$
\gcd(F_b,F_c)=1\quad\hbox{或}\quad F_b=F_c.
\tag{18.6}
$$

这段推断只要求两个字有理、长度为 $p-1$；并未使用约定 16.1 的反周期关系。分圆轨道是定理 13.3 的既有输入，首一因子下降和 Gauss 引理亦同该定理及 [A]。

反设 $F\ne G$。式 (18.6) 给出 $\gcd(F,G)=\gcd(F,M)=1$。在 $\overline{\mathbb Q(t)}$ 中取 $M$ 的任一根 $x_*$。引理 15.2 的实际递推在该域中仍成立，给出一个原圈本征向量 $\psi$，满足

$$
\psi_j=0,\qquad\psi_a=F(x_*,t)\ne0.
$$

另一方面，$a$ 的节点因子也是 $M$，故同一谱值有一个在 $a$ 为零的非零原圈本征向量。存在性使用引理 3.4，两个向量因在 $a$ 处的取值而线性无关。于是 $M$ 的每个根都是实际特征多项式

$$
\mathcal P(x,t)=\det(xI-A_{2p}+t\operatorname{diag}(v))
$$

的至少二重根。$M$ 无重根，故 $M^2\mid\mathcal P$；首一除法使二次首一商属于 $\mathbb Q[t][x]$。令 $e=v_j$、$f=v_a$，写

$$
\mathcal P=(x^2+\alpha(t)x+\beta(t))M^2.
\tag{18.7}
$$

下面的系数计算全部属于同一个实际圈。两个半圆矩阵 $A_{\rm path}-t\operatorname{diag}(u)$、$A_{\rm path}-t\operatorname{diag}(z)$ 的迹均为 $-ts$，平方迹均为 $nt^2+2(n-1)$。所以 $F,G,M$ 的前两项系数相同：

$$
M=x^n+ts\,x^{n-1}
 +\left(\frac{s^2-n}{2}t^2-(n-1)\right)x^{n-2}
 +\text{更低次项}.
\tag{18.8}
$$

$n=2$ 时公式止于常数项。对原圈矩阵 $A_{2p}-t\operatorname{diag}(v)$，总势和为 $S=2s+e+f$，迹为 $-tS$，平方迹为 $2pt^2+4p$。利用特征多项式的第二项系数 $((\operatorname{tr}K)^2-\operatorname{tr}(K^2))/2$，比较式 (18.7) 的最高两项，得到

$$
\begin{aligned}
\alpha(t)&=t(e+f),\\
\beta(t)&=\left(\frac{S^2-2p}{2}-(2s^2-n)-2s(e+f)\right)t^2-4\\
 &=ef\,t^2-4.
\end{aligned}
$$

最后一步使用 $n=p-1$ 和 $e^2=f^2=1$。因此反设所迫使的精确恒等式为

$$
\mathcal P=\bigl((x+te)(x+tf)-4\bigr)M^2.
\tag{18.9}
$$

在 $t=0$，$M=D_p$ 的根全部严格小于 $2$。由于首一多项式根的连续性，对充分小的实数 $|t|$，实际矩阵 $K_t=A_{2p}-t\operatorname{diag}(v)$ 的最大本征值必为二次因子的较大根

$$
r(t)=-\frac{e+f}{2}t+
 \sqrt{4+\frac{(e-f)^2}{4}t^2}.
\tag{18.10}
$$

这里仅用自由最大本征值与其余根的严格间隙，不假设所有耦合处谱简单。在单位常向量上的 Rayleigh 商给出

$$
2-\frac{S}{2p}t\le r(t).
$$

将式 (18.10) 在零处的一次展开代入，分别令 $t\downarrow0$ 和 $t\uparrow0$，得到

$$
\frac{S}{2p}=\frac{e+f}{2}.
\tag{18.11}
$$

若 $e=f$，平均值为 $e\in\{-1,1\}$ 的二值势必处处等于 $e$；于是 $u=z$、$F=G$，与反设矛盾。

若 $e=-f$，式 (18.11) 给出 $S=0$。置 $\mathbf1=(1,\ldots,1)^{\mathsf T}$，将 $K_t$ 压缩到实际二维空间 $\operatorname{span}\{\mathbf1,v\}$。因为 $S=0$、$v_i^2=1$，基 $\mathbf1/\sqrt{2p},v/\sqrt{2p}$ 正交标准，压缩矩阵为

$$
\begin{pmatrix}2&-t\\-t&\gamma\end{pmatrix},\qquad
\gamma=\frac{v^{\mathsf T}A_{2p}v}{2p}
 =\frac1p\sum_{i=0}^{2p-1}v_iv_{i+1}\ge-2.
\tag{18.12}
$$

这是定理 16.3 证明中二维压缩的同一个计算；其所需条件在这里由式 (18.11) 和二值性保证，未借用反周期性。对固定 $t\ne0$，压缩的最大本征值为

$$
L_t(\gamma)=\frac{2+\gamma+
 \sqrt{(2-\gamma)^2+4t^2}}2,
$$

且 $L_t' (\gamma)>0$，$L_t(-2)=\sqrt{4+t^2}$。取充分小的非零实数 $t$，式 (18.10) 断言原矩阵的最大本征值等于 $\sqrt{4+t^2}$；Rayleigh 原理禁止压缩具有更大的最大本征值。因此 $\gamma=-2$，从而每个 $v_iv_{i+1}=-1$，势严格交替。严格交替势由 $i\mapsto2j-i$ 保持，仍给出 $u=z$、$F=G$，矛盾。两种端点情形穷尽，故 $F=G$。

定理 15.3 的有向闭合式 (15.5) 现在给出 $B=D$。直接采用定理 16.3 证明末段的有向重构：已知首一 $K_k$ 及其删末位的 $K_{k-1}$，递推

$$
K_k=(x+tb_k)K_{k-1}-K_{k-2}
$$

的首一带余除法唯一恢复最后字母 $b_k$ 和下一项 $K_{k-2}$。从 $(F,B)=(G,D)$ 递归恢复全部字母，得 $u=z$。这正是原带标号势满足 $v_{2j-i}=v_i$；反射固定的两个端点 $j,a$ 对其自身势值没有额外限制。至此证明了必要性。

反之，设该实际顶点反射保持 $v$。式 (18.3) 的置换保持实际邻接关系和势值，故分别与原 $\Delta_{2p}$、$\operatorname{diag}(v)$ 可交换。它固定 $e_j$，交换 $e_{j+1},e_{j-1}$，所以 $O_j\ne\pm I$。其负特征子空间

$$
W_j=\operatorname{span}_{\mathbb R}
 \{e_{j+r}-e_{j-r}:1\le r\le p-1\}
$$

维数为 $p-1>0$，每个向量在 $j,a$ 均为零，且被每个实际 $H_t$ 保持。对每个实数 $t$，实对称限制 $H_t|_{W_j}$ 有非零实本征向量，因而同时提供两处所需的节点。这一充分机制也是 [LG] 引理 3.2 (2) 和定理 16.3 充分方向的实际反射机制。Rayleigh 原理及压缩比较使用 [M] §4.2–4.3；周期 Jacobi 的单值解释见 [J] §7.1–7.2，但式 (18.7)–(18.12) 直接计算原圈矩阵，不将辅助周期谱当作原谱。∎

## 19. 两条回文开半圆的完整分类

**定义 19.1（实际双回文切口）。** 对定义 18.1 的 $p,v,j$，置 $a=j+p$，保留从 $j$ 向 $a$ 的两个实际有序字

$$
u_r=v_{j+r},\qquad z_r=v_{j-r},\qquad1\le r\le p-1.
$$

称此切口双回文，若

$$
u_r=u_{p-r},\qquad z_r=z_{p-r}\qquad(1\le r\le p-1).
\tag{19.1}
$$

**定理 19.2（双回文切口的逐站点分类）。** 对每个奇素数 $p\ge3$、每个实际二值势和每个满足式 (19.1) 的切口，有

$$
\boxed{\qquad
\mathsf N_j(v)\quad\Longleftrightarrow\quad
\mathsf N_{j+p}(v)\quad\Longleftrightarrow\quad u=z.
\qquad}
\tag{19.2}
$$

任一条件成立时，式 (18.3) 的 $O_j$ 就是原势的固定非平凡共享实正交反射。

**证明。** 先设 $\mathsf N_j(v)$。在同一个带标号单位圈上定义二值势 $\widehat v$，仅把 $j$ 处的值换为 $v_a$：

$$
\widehat v_i=v_i\ (i\ne j),\qquad\widehat v_j=v_a.
$$

对每个实数 $t$，原节点向量 $\psi_j=0$ 满足

$$
H_t(\widehat v)\psi
 =H_t(v)\psi+t(v_a-v_j)E_{jj}\psi
 =H_t(v)\psi.
\tag{19.3}
$$

故 $\mathsf N_j(\widehat v)$，并且这个等式反向同样成立。式 (19.3) 是本卷式 (11.1) 所用单点节点不变性的向量形式；这里只消费该初等秩一事实，不使用缺陷重复数或 Chebyshev 块族的假设。

令 $\sigma(i)=2j+p-i\pmod{2p}$。它交换 $j,a$；对两条开半圆分别有

$$
\sigma(j+r)=j+p-r,\qquad
\sigma(j-r)=j-p+r.
$$

式 (19.1) 使每条半圆的实际内部势在这次反转下不变，而 $\widehat v_j=\widehat v_a$ 使端点也相容。因此 $\sigma$ 的实际置换矩阵 $R$ 分别与 $\Delta_{2p}$、$\operatorname{diag}(\widehat v)$ 可交换。将 $\widehat v$ 在 $j$ 处的每个节点向量乘以 $R$，得到同一耦合下在 $a$ 为零的非零本征向量。所以 $\mathsf N_a(\widehat v)$。

现在将定理 18.2 应用于实际势 $\widehat v$，得 $\widehat v_{j+r}=\widehat v_{j-r}$，即 $u=z$。这里 $R$ 只用于 $\widehat v$ 上的节点传递；原势所需的对称由 $u=z$ 回接：$\rho_j(i)=2j-i$ 固定两个原端点，并逐项配对原势的两条半圆，因而确实保持原 $v$。所得原反射是 $O_j$，不是把 $R$ 冒作原势的对称。

若从 $\mathsf N_a(v)$ 出发，从 $a$ 看到的两条字为 $\operatorname{rev}z$、$\operatorname{rev}u$，仍各自回文。相同论证以 $a$ 为起点给出这两个字相等，亦即 $u=z$。最后，$u=z$ 时直接用定理 18.2 的实际反射充分方向，得到两个站点均持续及所述 $O_j$。∎

**定理 19.3（非常数配对和下的全局好坏分类）。** 在定理 19.2 的条件下，另设实际配对和 $w_r=v_r+v_{r+p}$ 非常数。则

$$
\boxed{\qquad \operatorname{Bad}(v)\iff u=z.\qquad}
\tag{19.4}
$$

因此，每个 $u\ne z$ 的双回文切口势都是好势：除有限个实耦合外，原 $H_t$ 谱简单且每个非零本征向量的每个坐标均非零。这包括 $\sum_ru_r=\sum_rz_r$ 的所有不等字对，不限制其内部排列、游程或长度 $p-1$。每个坏例都有式 (18.3) 的固定原反射。

**证明。** 对 $1\le r\le p-1$，原配对和与有序字满足

$$
w_{j+r}=u_r+z_{p-r},\qquad
w_{j-r}=z_r+u_{p-r}.
$$

双回文性使二者都等于 $u_r+z_r$，故 $w$ 关于 $j\bmod p$ 反射。由于 $w$ 非常数，定理 14.2 保证这是唯一剩余类反射中心，且任何持续站点只能为 $j$ 或 $a$。若 $v$ 坏，母卷推论 3.3 给出某个持续站点，定理 19.2 遂给出 $u=z$。反之 $u=z$ 时，定理 18.2 直接构造原节点与原反射，故坏。若 $u\ne z$，两个候选站点均不持续，其余站点由定理 14.2 排除；母卷推论 3.3 给出好势及有限例外集合。等和字对未在任何一步被排除，故所述范围全部成立。∎

**命题 19.4（常数配对和的准确边界）。** 对双回文切口，若 $w$ 为常数，则有以下穷尽分类。

若 $w\equiv2\varepsilon$、$\varepsilon\in\{-1,1\}$，原势处处等于 $\varepsilon$，故 $u=z$，两个切口端点持续，且 $O_j$ 是原共享反射。

若 $w\equiv0$，则 $v_{i+p}=-v_i$，$z=-u$，所以 $u\ne z$，定理 19.2 保证两个切口端点均不持续。然而全局结论为

$$
\operatorname{Bad}(v)
\iff\exists k\in\mathbb Z/(2p)\mathbb Z\
 \forall i,\ v_{2k-i}=v_i;
\tag{19.5}
$$

存在这样的 $k$ 时，原共享反射为 $(O_k\psi)_i=\psi_{2k-i}$，且 $k\bmod p\ne j\bmod p$。特别地，式 (19.4) 不能去掉非常数条件。

**证明。** 二值配对和的常数值只能为 $-2,0,2$。值为 $2\varepsilon$ 时每对的两个值均为 $\varepsilon$。值为零时恰为反周期势；由 $z_r=-u_{p-r}$ 及式 (19.1) 得 $z=-u$。全局等价式 (19.5) 直接采用推论 16.4，且其构造为原 $O_k$；若 $k$ 与 $j$ 同剩余类，就会使 $u=z$，与 $z=-u$ 矛盾。

具体地，对每个奇素数 $p\ge3$，在原标号上取

$$
v_i=1\quad(0\le i\le p-1),\qquad
v_i=-1\quad(p\le i\le2p-1),\qquad j=0.
$$

此时 $u=1^{p-1}$、$z=(-1)^{p-1}$，两字都回文而不等，且 $w\equiv0$。实际反射 $i\mapsto p-1-i$ 保持两个常号半圆；它的顶点中心为 $k=(p-1)/2$，因此按推论 16.4 或定理 18.2，势是坏势并有固定原共享反射。它在指定端点 $0,p$ 均不持续，仍在另一对径对持续。这正是常数 $w$ 时失去唯一候选站点限制所允许的情形。∎

## 20. 原剩余推断的单站点与非回文限制

**推论 20.1（式 (17.1) 的实际剩余形状）。** 固定原断言 $T$ 的范围 $p\ge11$ 为奇素数。设一个实际二值势和站点 $j$ 满足式 (17.1) 的全部前提：$w$ 非常数且关于 $j\bmod p$ 反射，两条实际有序开半圆等和而不等，并满足原有向恒等式

$$
(x+tv_{j+p})(F-G)=2(B-D).
$$

则两个候选站点中恰好 $j$ 持续，$j+p$ 不持续；原圈的全部持续站点集合恰为 $\{j\}$。此外，$u,z$ 中至少一个不是回文。

**证明。** 等和与所述恒等式经定理 15.3 直接给出 $\mathsf N_j(v)$。若 $\mathsf N_{j+p}(v)$ 也成立，定理 18.2 就给出原反射，亦即 $u=z$，矛盾。定理 14.2 的唯一配对和反射中心排除其余站点，因此持续站点集合确为单点。若两字都回文，定理 19.2 又由 $\mathsf N_j(v)$ 推出 $u=z$，仍矛盾。这些推断均由原节点、有向重构和原反射桥接而来。∎

**命题 20.2（剩余范围与全部实际正交矩阵）。** 令 $\mathcal R$ 为式 (17.1) 的前提所定义的实际势与指定站点对的集合，并令

$$
\mathcal R'=\{(p,v,j)\in\mathcal R:
 \{i:\mathsf N_i(v)\}=\{j\},\quad
 u\ne\operatorname{rev}u\ \text{或}\ z\ne\operatorname{rev}z\}.
$$

则 $\mathcal R=\mathcal R'$。原断言 $T$ 仍等价于

$$
\forall(p,v,j)\in\mathcal R',\quad
\exists O\in O(2p,\mathbb R),\quad O\ne\pm I,\quad
O\Delta_{2p}=\Delta_{2p}O,\quad
O\operatorname{diag}(v)=\operatorname{diag}(v)O.
\tag{20.1}
$$

推论 20.1 不决定 $\mathcal R'$ 是否为空，亦不判定式 (20.1) 的真假。仅排除二面体置换不能排除式 (20.1) 中的全部实际实正交矩阵。

**证明。** 包含 $\mathcal R'\subseteq\mathcal R$ 来自定义，反向包含是推论 20.1。命题 17.1 给出 $T$ 与对 $\mathcal R$ 的同一共享正交对称蕴含等价，代入集合等式即得式 (20.1)。最后的矩阵量词保持约定 13.1 的原定义；二面体置换只是 $O(2p,\mathbb R)$ 中的有限子集，检查该子集没有给出其余矩阵不存在的推断。∎

## 追加锚（本行以下为增补区）

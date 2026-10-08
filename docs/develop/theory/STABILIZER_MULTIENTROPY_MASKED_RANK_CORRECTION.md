# 奇复本稳定子多熵的掩码秩修正:偶闭途径判据、符号与图形式依赖

> **本卷的机器契约(逐条可查,落地后不改)。** 消化器 `generic-v1`;地址(locator)由
> `tools/StrataLint.Engine/Digestion/Atomizers/GenericAtomizer.cs` **仅从本文件的字节**算出,
> 不查任何词表。本卷**只增不减**:卷首恒定区与既有各章一经合入即**一字不改**,
> 全部修订、勘误、增补一律写在文末**追加锚**之后的新章里。旧章保留为历史记录;
> 勘误的形式是新章点名旧编号并给出改判,不是回去改旧字节(CLAUDE.md 第 1.2 条、第 4.2 条)。

## 1. 定位、状态与产地

**参考输入,不是真源。** 本卷是 trureturing 的**参考输入**:提供出处与灵感,不承担机器治理,
Lean 形式化才是唯一真源。不得把任何形式化工件反向绑定到本卷的章节号或定理号上(第 4.3 条)。

**证明状态。** 本卷给出的是 ZFC 内的普通数学散文与有限精确核验。
**本卷未经 Lean kernel 验证,不得称 kernel-verified**;哪条已被形式化,以冻结账本为准,不以本卷自述为准(第 2.4 条)。

**产地(第 5.2 条三项)。**
①**skill 上下文**:`consensus-rnd:sshx`;
②**载体与分工**:本卷正文由实施席 Claude Code subagent(Opus 5.5)产出;选题由六席思考面板(Opus 5.5 三席、Fable 5.1 三席)收敛;定理 7.3 的两个图态构造与 $K_4$ 分支的负修正(定理 5.1(d)、推论 5.2)最初由思考面板席位(Claude Code subagent,Opus 5.5 与 Fable 5.1)给出,实施席(Opus 5.5)复算并写成证明;评审三席为 Claude Code subagent(Opus 5.5 与 Fable 5.1 混合)。实施席与评审席同属一个载体族,不冒充跨厂商的模型多样性;
③**混合方式**:三席并发盲评。
会话 ID:`02860e2e-a1ec-4fd1-b72b-435e73e0a63d`,恢复命令 `claude --resume 02860e2e-a1ec-4fd1-b72b-435e73e0a63d`。

**读法。** 本卷按写作时序排列:第 1–10 章是基线叙述,其后每一批增补自带一节「本批导航」,
说明它扩充、限定或改判了前文的哪一条。**基线叙述中的「本次」「本轮」一律指写下它的那一次工作**,
不随后续增补改写。

**内容提要。** 本卷以卷《Stabilizer multi-entropy at every odd replica index》(下称母卷)为前提。母卷对奇复本指标 $n\ge3$ 把 $S_n^{(\mathtt q)}$ 写成 $F=\mathbb F_2(\zeta)$ 上秩 $\rho_t$ 之和(母卷定理 3.1),在字符至多取三值时把 $\rho_t$ 化为掩码秩 $r(\pi_t)$(母卷命题 4.1),并在四圈上算出掩码秩表达式的偏差(母卷命题 5.1);母卷注 6.1 不比较一般情形下的 $\rho_t$ 与 $r(\pi_t)$,开放问题 6.3 问 $S_n^{(\mathtt q)}$ 是否为掩码秩的函数,开放问题 6.4 问修正和何时为零、符号由什么决定。本卷给出:按掩码图连通分支可加的局部亏差与 β 缩放判据,其可解性恰由偶长闭途径的交替积刻画(定理 3.1);无偶圈的掩码图上两种秩相等(定理 3.3);路、圈与四顶点图的带权秩表(命题 4.1、4.2);分支为四方单比特图的不交并的修正和闭式与符号(定理 5.1、推论 5.2);单字符的两侧界与完全多部型上的负修正(定理 6.1、6.2);掩码秩在至多三块的分割上与图形式无关、在四块分割上依赖图形式(定理 7.1、7.2);对母卷开放问题 6.3 在图形式读法下的否定回答(定理 7.3;态不变量读法见开放问题 8.6);以及一个所有图形式的修正和都非零的六比特态(命题 8.3,计算机辅助)。

## 2. 记号与约定

**约定 2.1（沿用母卷的记号）。** 本卷沿用母卷约定 2.1–2.5 与母卷第 5 节开头的全部记号:奇数 $n\ge3$,方数 $\mathtt q\ge2$,复本群 $G=(\mathbb Z/n)^{\mathtt q-1}$,本原 $n$ 次单位根 $\zeta$ 与域 $F=\mathbb F_2(\zeta)$,字符 $t\in G$ 的取值函数 $f_t$ 与其纤维分割 $\pi_t$,图形式 $\Gamma\in\mathbb F_2^{N\times N}$(对称、对角为零),着色 $\mathrm{col}:[N]\to[\mathtt q]$(允许空方),对角阵 $\Lambda_t$,矩阵 $M_t=\Lambda_t\Gamma+\Gamma\Lambda_t$ 与其秩 $\rho_t=\operatorname{rank}_FM_t$,掩码矩阵 $\Gamma^\pi$ 与掩码秩 $r(\pi)=\operatorname{rank}_{\mathbb F_2}\Gamma^\pi$,下降阶乘 $(a)_k$,以及掩码秩表达式 $S_n^{\mathrm{mask}}$。记 $S_n=S_n^{(\mathtt q)}$,$\lambda_u=\lambda_u(t)=\zeta^{f_t(\mathrm{col}(u))}$。需要指明图形式时写 $\rho_t(\Gamma)$、$r_\Gamma(\pi)$、$S_n^{\mathrm{mask}}(\Gamma)$。任一对称、对角为零的 $\Gamma\in\mathbb F_2^{N\times N}$ 都是图态 $|\Gamma\rangle$ 的一个图形式,故凡只涉及 $\Gamma$ 与 $\mathrm{col}$ 的陈述对一切这样的 $\Gamma$ 成立。一个方称为被占据,如果它至少含一个量子比特;对 $\mathtt q$ 个方的分割 $\pi$,它在被占据方集合 $O$ 上的诱导分割是 $\{B\cap O:\ B\in\pi,\ B\cap O\ne\varnothing\}$。$S(p,k)$ 是第二类 Stirling 数。

**约定 2.2（掩码图、边权与修正和）。** 对 $t\in G$,掩码图 $H_t$ 是顶点集 $[N]$ 上的简单图,$uv$ 为其边当且仅当 $\Gamma^{\pi_t}_{uv}=1$。由于 $\zeta$ 是本原 $n$ 次单位根,$\lambda_u=\lambda_v$ 当且仅当 $\mathrm{col}(u)$ 与 $\mathrm{col}(v)$ 落在 $\pi_t$ 的同一块中;又在特征 $2$ 中 $\lambda_u+\lambda_v=0$ 当且仅当 $\lambda_u=\lambda_v$。故 $uv\in E(H_t)$ 当且仅当 $\Gamma_{uv}=1$ 且 $\lambda_u\ne\lambda_v$,并且

$$
(M_t)_{uv}=\Gamma^{\pi_t}_{uv}\,(\lambda_u+\lambda_v),\qquad M_t=\Lambda_t\Gamma^{\pi_t}+\Gamma^{\pi_t}\Lambda_t ,
$$

即 $M_t$ 的非零元恰好位于 $H_t$ 的边上(这一观察即母卷命题 4.1 证明的第一步)。边 $uv\in E(H_t)$ 的权是 $w_t(uv)=\lambda_u+\lambda_v\in F^\times$。修正和定义为

$$
\Delta=\Delta(\Gamma,\mathrm{col},n)=\sum_{0\ne t\in G}\big(\rho_t-r(\pi_t)\big).
$$

由母卷定理 3.1 与母卷第 5 节的 $S_n^{\mathrm{mask}}$ 定义,对每个规范化纯量子比特稳定子态、其每个图形式与每个着色,

$$
S_n-S_n^{\mathrm{mask}}=\frac{\log2}{2(n-1)\,n^{\mathtt q-2}}\,\Delta .\tag{2.1}
$$

因 $\pi_0$ 只有一块,$\Gamma^{\pi_0}=0$,又 $M_0=0$,故 $\Delta=\sum_{t\in G}(\rho_t-r(\pi_t))$。对 $C\subseteq[N]$,$M_t[C]$ 与 $\Gamma^{\pi_t}[C]$ 记行列都取自 $C$ 的主子阵,局部亏差记为 $\delta_C(t)=\operatorname{rank}_FM_t[C]-\operatorname{rank}_{\mathbb F_2}\Gamma^{\pi_t}[C]$。$k_t$ 记 $f_t$ 在被占据方上取到的不同值的个数。对四个两两不同的方 $c_1,c_2,c_3,c_4$,记 $D=\#\{t\in G:\ f_t(c_1),f_t(c_2),f_t(c_3),f_t(c_4)\ \text{两两不同}\}$;由母卷命题 5.1 的计数,当 $\mathtt q\ge4$ 时无论 $\mathtt q$ 是否在 $c_1,\dots,c_4$ 之中都有

$$
D=(n-1)(n-2)(n-3)\,n^{\mathtt q-4},\qquad \frac{D}{(n-1)\,n^{\mathtt q-2}}=\frac{(n-2)(n-3)}{n^2}.\tag{2.2}
$$

**约定 2.3（途径、圈与匹配）。** 设 $H$ 是简单图。途径是顶点序列 $W=(u_0,u_1,\dots,u_k)$,其中每个 $u_iu_{i+1}$ 是边;$|W|=k$ 是其长度,$u_k=u_0$ 时称闭途径;$k=0$ 的途径称为平凡途径。圈是长度 $k\ge3$、$u_0,\dots,u_{k-1}$ 两两不同的闭途径,按 $k$ 的奇偶称为奇圈或偶圈;说 $H$ 无偶圈,指 $H$ 不含长度为偶数的圈。$W^-=(u_k,\dots,u_0)$ 是反向途径;若 $W$ 的终点是 $W'$ 的起点,$W\cdot W'$ 是先走 $W$ 再走 $W'$ 的途径。对字符 $t$ 与 $H_t$ 中的途径 $W$,交替积为

$$
\alpha_t(W)=\prod_{i=0}^{k-1}w_t(u_iu_{i+1})^{(-1)^i}\in F^\times ,
$$

平凡途径的交替积为 $1$。逐项比较指数即得

$$
\alpha_t(W\cdot W')=\alpha_t(W)\,\alpha_t(W')^{(-1)^{|W|}},\qquad \alpha_t(W^-)=\alpha_t(W)^{(-1)^{|W|-1}} ;\tag{2.3}
$$

前一式成立,是因为 $W'$ 的第 $i$ 步在 $W\cdot W'$ 中是第 $|W|+i$ 步;后一式成立,是因为 $W^-$ 的第 $i$ 步走的是 $W$ 的第 $k-1-i$ 条边,其指数 $(-1)^i=(-1)^{k-1}(-1)^{k-1-i}$。顶点子集 $S$ 上的诱导子图记为 $H[S]$,$\mathrm{PM}(H)$ 为 $H$ 的完美匹配之集,$\mathrm{pm}(H)=|\mathrm{PM}(H)|$,$\nu(H)$ 为 $H$ 的最大匹配所含边数。偶圈 $Z$ 的边集恰好分成两个完美匹配 $Z^{(1)}$、$Z^{(2)}$(相间的边各成一组);由定义,从 $Z$ 上任一点、沿任一方向读出时,指数为 $+1$ 的边恰好组成 $Z^{(1)}$、$Z^{(2)}$ 之一,故交替积是 $\prod_{e\in Z^{(1)}}w_t(e)\big/\prod_{e\in Z^{(2)}}w_t(e)$ 或其倒数,故条件 $\alpha_t(Z)=1$ 与起点和方向无关。

**约定 2.4（交错阵的标准事实）。** 设 $K$ 是特征 $2$ 的域,$A\in K^{m\times m}$ 交错,即对称且对角为零;$H(A)$ 是 $[m]$ 上以 $\{uv:\ A_{uv}\ne0\}$ 为边集的支撑图;$A[S]$ 是行列都取自 $S$ 的主子阵。以下标准事实作为引用步骤使用,不是本卷的条目:(i) Pfaffian 的完美匹配展开在特征 $2$ 中没有符号,且含非边的项为零,故 $|S|$ 为偶数时 $\operatorname{Pf}(A[S])=\sum_{\mathfrak m\in\mathrm{PM}(H(A)[S])}\prod_{uv\in\mathfrak m}A_{uv}$,空集的 Pfaffian 为 $1$;(ii) Cayley 恒等式 $\det A[S]=\operatorname{Pf}(A[S])^2$,而 $|S|$ 为奇数时 $\det A[S]=0$;(iii) $\operatorname{rank}A=\max\{|S|:\ \det A[S]\ne0\}$。(iii) 的证明是:若 $\det A[S]\ne0$ 则 $\operatorname{rank}A\ge|S|$;反之取 $S$ 使 $A$ 中以 $S$ 为指标的行构成行空间的一组基,$T$ 为其补,则存在 $X$ 使 $A_{T,\bullet}=XA_{S,\bullet}$,特别地 $A_{T,S}=XA_{S,S}$,由对称性 $A_{S,T}=A_{T,S}^{\mathsf T}=A_{S,S}X^{\mathsf T}$,于是 $A_{S,\bullet}=A_{S,S}\,[\,I\mid X^{\mathsf T}\,]$,其秩 $|S|$ 不超过 $\operatorname{rank}A_{S,S}$,故 $A[S]$ 可逆。合起来得

$$
\operatorname{rank}_KA=\max\Big\{|S|:\ S\subseteq[m],\ \sum_{\mathfrak m\in\mathrm{PM}(H(A)[S])}\ \prod_{uv\in\mathfrak m}A_{uv}\ne0\Big\}\le2\,\nu(H(A)).\tag{2.4}
$$

另用到:$\mathbb F_2$ 上矩阵的秩在域扩张下不变;分块对角阵的秩是各块秩之和;非零交错阵的秩至少为 $2$(取一个非零元 $A_{uv}$,则 $\det A[\{u,v\}]=A_{uv}^2\ne0$)。

**约定 2.5（图态的稳定子与局部补）。** $X,Y,Z$ 是单比特 Pauli 矩阵,$P_u$ 表示作用在第 $u$ 个量子比特上的 $P$,$\mathsf S=\operatorname{diag}(1,i)$。对 $[N]$ 上的图 $\Gamma$ 与顶点 $w$,记 $N_\Gamma(w)$ 为邻域,$K_w=X_w\prod_{u\in N_\Gamma(w)}Z_u$。以下标准事实作为引用步骤使用(图态的稳定子刻画,先例见第 9 节 Hein、Eisert、Briegel 一行):$K_w|\Gamma\rangle=|\Gamma\rangle$;诸 $K_w$ 两两对易,生成不含 $-I$ 的 $2^N$ 元 Pauli 子群 $\mathcal S_\Gamma$,其公共 $+1$ 特征空间是一维的,由 $|\Gamma\rangle$ 张成。顶点 $v$ 处的局部补 $\tau_v(\Gamma)$ 是把 $N_\Gamma(v)$ 中两两不同顶点之间的边全部取反(有则删、无则添)所得的图;它不改变与 $v$ 相连的边。两图称为局部补等价,如果可以经有限次局部补互相得到。

## 3. 掩码秩相等的判据

**定理 3.1（分支可加性与 β 缩放判据）。** 设 $n\ge3$ 为奇数,$\mathtt q\ge2$,$\Gamma\in\mathbb F_2^{N\times N}$ 对称且对角为零,$\mathrm{col}:[N]\to[\mathtt q]$ 为任一着色,$t\in G$,并设 $C_1,\dots,C_s$ 是掩码图 $H_t$ 的全部连通分支的顶点集(孤立顶点各成一个分支)。则:

(a) $\rho_t-r(\pi_t)=\sum_{i=1}^s\delta_{C_i}(t)$。

(b) 设 $C$ 是 $H_t$ 的一个连通分支的顶点集。若存在 $\beta_u\in F^\times$($u\in C$)使得对 $H_t$ 中两端都在 $C$ 内的每条边 $uv$ 都有 $\beta_u\beta_v=w_t(uv)$,则 $\delta_C(t)=0$。

(c) (b) 中的族 $(\beta_u)_{u\in C}$ 存在,当且仅当 $H_t[C]$ 中每条长度为偶数的闭途径 $W$ 都满足 $\alpha_t(W)=1$。

(d) 若 $H_t[C]$ 是二部图,则 (c) 的条件等价于:$H_t[C]$ 的每个圈 $Z$ 都满足 $\prod_{e\in Z^{(1)}}w_t(e)=\prod_{e\in Z^{(2)}}w_t(e)$;并且只需对 $H_t[C]$ 的任意一棵生成树的全部基本圈检验这一等式。

特别地,若 $H_t$ 的每个连通分支都满足 (c) 的条件,则 $\rho_t=r(\pi_t)$。该条件是充分的,不是必要的(命题 8.1)。

**证明。** (a) 把量子比特按 $C_1,\dots,C_s$ 依次排列。不同分支之间没有 $H_t$ 的边,而由约定 2.2,$M_t$ 与 $\Gamma^{\pi_t}$ 的非零元都只出现在 $H_t$ 的边上,所以两者都是以 $C_1,\dots,C_s$ 为块的分块对角阵,对角块分别是 $M_t[C_i]$ 与 $\Gamma^{\pi_t}[C_i]$。分块对角阵的秩是各块秩之和,相减即得 (a)。

(b) 令 $B=\operatorname{diag}(\beta_u)_{u\in C}$,它在 $F$ 上可逆。对 $u,v\in C$,若 $uv\in E(H_t)$,则 $(B\,\Gamma^{\pi_t}[C]\,B)_{uv}=\beta_u\beta_v=\lambda_u+\lambda_v=(M_t)_{uv}$;否则两边都是 $0$。故 $M_t[C]=B\,\Gamma^{\pi_t}[C]\,B$,从而 $\operatorname{rank}_FM_t[C]=\operatorname{rank}_F\Gamma^{\pi_t}[C]=\operatorname{rank}_{\mathbb F_2}\Gamma^{\pi_t}[C]$,后一等号是秩在域扩张下不变。

(c) 先证一个传播式:若族 $(\beta_u)$ 满足 (b) 中全部边方程,则对 $H_t[C]$ 中任一途径 $W=(u_0,\dots,u_k)$,

$$
\beta_{u_k}=\alpha_t(W)^{(-1)^{k-1}}\,\beta_{u_0}^{(-1)^k}.\tag{3.1}
$$

对 $k$ 归纳:$k=0$ 时 $\alpha_t(W)=1$,两边都是 $\beta_{u_0}$。设 (3.1) 对 $W$ 成立,$W'=W\cdot(u_k,u_{k+1})$。由边方程,$\beta_{u_{k+1}}=w_t(u_ku_{k+1})\,\beta_{u_k}^{-1}=w_t(u_ku_{k+1})\,\alpha_t(W)^{(-1)^k}\beta_{u_0}^{(-1)^{k+1}}$;而由 (2.3),$\alpha_t(W')^{(-1)^k}=\alpha_t(W)^{(-1)^k}\,w_t(u_ku_{k+1})$,两式相同。

必要性:若 $W$ 是长度 $k$ 为偶数的闭途径,(3.1) 给出 $\beta_{u_0}=\alpha_t(W)^{-1}\beta_{u_0}$,故 $\alpha_t(W)=1$。

充分性:设每条偶长闭途径的交替积为 $1$。取定 $r\in C$。若 $H_t[C]$ 是二部图,令 $\beta_r=1$。否则 $H_t[C]$ 含奇圈;从 $r$ 沿一条路走到该奇圈上的一点,绕圈一周,再沿原路返回,得到从 $r$ 出发的奇长闭途径 $Q$。有限域 $F$ 中平方映射是单射,从而是双射,故存在唯一的 $\beta_r\in F^\times$ 使 $\beta_r^2=\alpha_t(Q)$。对从 $r$ 出发的任一奇长闭途径 $Q'$,$Q\cdot {Q'}^{-}$ 是偶长闭途径,由 (2.3),

$$
1=\alpha_t(Q\cdot {Q'}^{-})=\alpha_t(Q)\,\big(\alpha_t(Q')^{(-1)^{|Q'|-1}}\big)^{(-1)^{|Q|}}=\alpha_t(Q)\,\alpha_t(Q')^{-1},
$$

因为 $|Q'|-1$ 为偶数而 $|Q|$ 为奇数;故对从 $r$ 出发的每条奇长闭途径都有 $\beta_r^2=\alpha_t(Q')$。现对 $v\in C$ 取一条从 $r$ 到 $v$、长度为 $k$ 的途径 $W$(连通性保证存在),定义 $\beta_v=\alpha_t(W)^{(-1)^{k-1}}\beta_r^{(-1)^k}$;对 $v=r$ 取平凡途径,与上面选定的 $\beta_r$ 一致。

这一定义与 $W$ 的选取无关。设 $W_1$、$W_2$ 是从 $r$ 到 $v$ 的途径,长度为 $k_1$、$k_2$。由 (2.3),闭途径 $W_1\cdot W_2^-$ 的交替积是 $\alpha_t(W_1)\,\alpha_t(W_2)^{(-1)^{k_1+k_2-1}}$。若 $k_1\equiv k_2\pmod 2$,该闭途径长度为偶数,其交替积 $\alpha_t(W_1)\alpha_t(W_2)^{-1}$ 等于 $1$,于是 $\alpha_t(W_1)=\alpha_t(W_2)$,而两个定义式中的指数也相同。若 $k_1\not\equiv k_2$,不妨 $k_1$ 为偶数、$k_2$ 为奇数,则 $W_1\cdot W_2^-$ 是从 $r$ 出发的奇长闭途径,其交替积 $\alpha_t(W_1)\alpha_t(W_2)$ 等于 $\beta_r^2$;两个定义式分别为 $\alpha_t(W_1)^{-1}\beta_r$ 与 $\alpha_t(W_2)\beta_r^{-1}$,它们相等恰好等价于 $\beta_r^2=\alpha_t(W_1)\alpha_t(W_2)$。这时 $H_t[C]$ 不是二部图,$\beta_r$ 正是按上一段选定的。

最后验证边方程。设 $uv$ 是 $C$ 内的边,$W$ 是从 $r$ 到 $u$ 的长度为 $k$ 的途径,则 $W'=W\cdot(u,v)$ 是到 $v$ 的长度为 $k+1$ 的途径,$\alpha_t(W')=\alpha_t(W)\,w_t(uv)^{(-1)^k}$。按定义

$$
\beta_u\beta_v=\alpha_t(W)^{(-1)^{k-1}}\beta_r^{(-1)^k}\cdot\alpha_t(W)^{(-1)^k}\,w_t(uv)\,\beta_r^{(-1)^{k+1}}=w_t(uv).
$$

(d) 设 $H_t[C]$ 是二部图。每个圈都是偶长闭途径,所以 (c) 的条件蕴含每个圈满足 $\alpha_t(Z)=1$,按约定 2.3 这就是两组完美匹配的权积相等。反之,设 $T$ 是 $H_t[C]$ 的一棵生成树,且 $T$ 的每个基本圈都满足该等式。取根 $r$,令 $\beta_r=1$,对 $v\in C$ 用 $T$ 中从 $r$ 到 $v$ 的唯一路 $P_v$(长度 $k_v$)定义 $\beta_v=\alpha_t(P_v)^{(-1)^{k_v-1}}$。对树边 $uv$($v$ 是 $u$ 的子顶点),$P_v=P_u\cdot(u,v)$,上一段末的计算给出 $\beta_u\beta_v=w_t(uv)$。对非树边 $uv$,设 $P$ 是 $T$ 中从 $u$ 到 $v$ 的路,长度 $j$;因 $H_t[C]$ 是二部图且 $u,v$ 相邻,$j$ 为奇数。$P$ 上全是树边,(3.1) 的推导只用到途径上各边的方程,故 $\beta_v=\alpha_t(P)^{(-1)^{j-1}}\beta_u^{(-1)^j}=\alpha_t(P)\beta_u^{-1}$,即 $\beta_u\beta_v=\alpha_t(P)$。基本圈 $Z=P\cdot(v,u)$ 是从 $u$ 出发、长度 $j+1$ 的闭途径,$\alpha_t(Z)=\alpha_t(P)\,w_t(uv)^{(-1)^j}=\alpha_t(P)\,w_t(uv)^{-1}$;由假设 $\alpha_t(Z)=1$,得 $\beta_u\beta_v=w_t(uv)$。于是族 $(\beta_u)$ 满足全部边方程,由 (c) 的必要性部分,(c) 的条件成立。

末句由 (a)、(b)、(c) 合并得到。∎

**推论 3.2（每个分支至多三值）。** 在定理 3.1 的设定下,若 $H_t$ 的每个连通分支的顶点集 $C$ 上,$\{\lambda_u:\ u\in C\}$ 至多含三个元素,则 $\rho_t=r(\pi_t)$。特别地,当 $f_t$ 在被占据方上至多取三个值时 $\rho_t=r(\pi_t)$,这正是母卷命题 4.1。

**证明。** 由定理 3.1(a)(b),只需对每个分支 $C$ 构造 (b) 中的族。若 $\lambda$ 在 $C$ 上只取一个值,则 $C$ 内没有 $H_t$ 的边,取 $\beta_u=1$。若取两个值 $a\ne b$,则 $C$ 内每条边连接取值 $a$ 与取值 $b$ 的顶点,取 $\beta_u=s$,其中 $s\in F^\times$ 满足 $s^2=a+b$(平方映射是 $F$ 的双射)。若取三个值 $a,b,c$,取母卷命题 4.1 证明中的 $\beta_a,\beta_b,\beta_c$,它们满足 $\beta_a\beta_b=a+b$、$\beta_b\beta_c=b+c$、$\beta_a\beta_c=a+c$,并令 $\beta_u=\beta_{\lambda_u}$。在每种情形下 $C$ 内的边 $uv$ 都满足 $\lambda_u\ne\lambda_v$ 与 $\beta_u\beta_v=\lambda_u+\lambda_v$。∎

**定理 3.3（无偶圈的掩码子图）。** 在定理 3.1 的设定下,若 $C\subseteq[N]$ 使 $H_t[C]$ 不含偶圈(例如 $C$ 是 $H_t$ 的一个不含偶圈的连通分支的顶点集),则

$$
\operatorname{rank}_FM_t[C]=\operatorname{rank}_{\mathbb F_2}\Gamma^{\pi_t}[C]=2\,\nu(H_t[C]),
$$

特别地 $\delta_C(t)=0$。$H_t[C]$ 为森林时,其中 $\operatorname{rank}_{\mathbb F_2}\Gamma^{\pi_t}[C]=2\nu(H_t[C])$ 是已知的森林邻接阵秩公式的特例(先例与定位见第 9 节),本卷不主张其新颖性。

**证明。** 先证:对每个 $S\subseteq C$,$H_t[S]$ 至多有一个完美匹配。若 $\mathfrak m_1\ne\mathfrak m_2$ 都是 $H_t[S]$ 的完美匹配,则对称差 $\mathfrak m_1\triangle\mathfrak m_2$ 非空,且 $S$ 的每个顶点在两个匹配中各恰关联一条边,故它在对称差中的度为 $0$ 或 $2$(两条边不同时为 $2$),相邻的两条边分属两个匹配;故对称差的每个非平凡连通分支是一个圈,其上的边交替属于 $\mathfrak m_1$ 与 $\mathfrak m_2$,长度为偶数,且因图是简单图,长度至少为 $4$。这与 $H_t[C]$ 不含偶圈矛盾。

由 (2.4),对 $M_t[C]$(支撑图为 $H_t[C]$,边权非零),$|S|$ 为偶数时和式 $\sum_{\mathfrak m\in\mathrm{PM}(H_t[S])}\prod_{uv\in\mathfrak m}w_t(uv)$ 或者是空和 $0$,或者恰有一项,是若干非零元之积,因而非零;它非零当且仅当 $H_t[S]$ 有完美匹配。同理对 $\Gamma^{\pi_t}[C]$ 在 $\mathbb F_2$ 上(边权均为 $1$),和式非零当且仅当 $H_t[S]$ 有完美匹配。故两个秩都等于 $\max\{|S|:\ S\subseteq C,\ H_t[S]\ \text{有完美匹配}\}$。取 $S$ 为一个最大匹配所覆盖的顶点集即达到 $2\nu(H_t[C])$,而 $H_t[S]$ 的完美匹配是 $H_t[C]$ 中含 $|S|/2$ 条边的匹配,故最大值恰为 $2\nu(H_t[C])$。∎

**推论 3.4（无偶圈的图形式）。** 设 $n\ge3$ 为奇数,$\mathtt q\ge2$,且图 $\Gamma$ 不含偶圈(例如森林、奇圈)。则对每个着色与每个 $t\in G$,$\rho_t=r(\pi_t)=2\nu(H_t)$;于是 $\Delta=0$,并且对以 $\Gamma$ 为图形式的稳定子态有 $S_n=S_n^{\mathrm{mask}}(\Gamma)$。

**证明。** $H_t$ 是 $\Gamma$ 的子图,其圈都是 $\Gamma$ 的圈,所以 $H_t$ 不含偶圈。对 $H_t$ 的每个分支用定理 3.3,再由定理 3.1(a) 求和,得 $\rho_t=r(\pi_t)$,两者都是各分支的 $2\nu$ 之和,即 $2\nu(H_t)$。对 $t$ 求和得 $\Delta=0$,再用 (2.1)。∎

## 4. 小图的带权秩

**命题 4.1（路与圈的带权秩）。** 设 $K$ 是特征 $2$ 的域,$A\in K^{m\times m}$ 是交错阵,其支撑图 $H(A)$ 恰为下列图之一(即 $A_{uv}\ne0$ 当且仅当 $uv$ 是该图的边)。

(i) 若 $H(A)$ 是 $m\ge1$ 个顶点的路,则 $\operatorname{rank}_KA=2\lfloor m/2\rfloor$。

(ii) 若 $H(A)$ 是长度 $L$ 为奇数的圈($m=L\ge3$),则 $\operatorname{rank}_KA=L-1$。

(iii) 若 $H(A)$ 是长度 $L$ 为偶数的圈 $Z$($m=L\ge4$),则当 $\prod_{uv\in Z^{(1)}}A_{uv}\ne\prod_{uv\in Z^{(2)}}A_{uv}$ 时 $\operatorname{rank}_KA=L$,否则 $\operatorname{rank}_KA=L-2$。

特别地,偶圈 $C_L$ 的邻接矩阵在 $\mathbb F_2$ 上的秩为 $L-2$;并且在定理 3.1 的设定下,若某个 $t$ 使 $H_t$ 的一个分支 $C$ 恰为偶圈 $Z$,则 $\delta_C(t)=2$ 当 $\alpha_t(Z)\ne1$,$\delta_C(t)=0$ 当 $\alpha_t(Z)=1$。边权全为 $1$ 的情形,即路与圈的邻接阵在 $\mathbb F_2$ 上的秩,是已知结果(先例与定位见第 9 节),本卷不主张其新颖性;本命题的新内容是任意非零边权的特征 $2$ 形式。

**证明。** (i)(ii) 路与奇圈不含偶圈。定理 3.3 的证明中关于 $\mathrm{rank}$ 的论证只用到支撑图不含偶圈与边权非零,故同样给出 $\operatorname{rank}_KA=2\nu(H(A))$;而 $\nu$ 对 $m$ 个顶点的路为 $\lfloor m/2\rfloor$,对长度 $L$ 的奇圈为 $(L-1)/2$。

(iii) 长度 $L$ 的偶圈恰有两个完美匹配 $Z^{(1)}$、$Z^{(2)}$:完美匹配含圈上某一条边 $e$ 时,与 $e$ 相邻的两条边被排除,依次推下去,它被唯一确定为 $e$ 所在的那组相间边。故由约定 2.4,$\operatorname{Pf}(A)=\prod_{Z^{(1)}}A_{uv}+\prod_{Z^{(2)}}A_{uv}$,它在特征 $2$ 中非零当且仅当两积不同,此时 $\operatorname{rank}A=L$。对真子集 $S\subsetneq[m]$,$H(A)[S]$ 是若干条路的不交并,不含偶圈,故由 (2.4) 与定理 3.3 证明的第一段,$A[S]$ 的 Pfaffian 非零当且仅当 $H(A)[S]$ 有完美匹配。$|S|=L-1$ 为奇数时没有完美匹配;删去两个相邻顶点所得的 $L-2$ 个顶点的路有完美匹配。因此 $\operatorname{Pf}(A)=0$ 时 $\operatorname{rank}A=L-2$。

$\mathbb F_2$ 上邻接矩阵的两积都为 $1$,故秩为 $L-2$。最后一句:$M_t[C]$ 以 $Z$ 为支撑图,其两组完美匹配的权积相等当且仅当 $\alpha_t(Z)=1$(约定 2.3),于是 $\operatorname{rank}_FM_t[C]\in\{L,L-2\}$ 按此分情形,而 $\operatorname{rank}_{\mathbb F_2}\Gamma^{\pi_t}[C]=L-2$。∎

**命题 4.2（四顶点带权秩表）。** 设 $K$ 是特征 $2$ 的域,$\lambda_1,\lambda_2,\lambda_3,\lambda_4\in K$ 两两不同,$H$ 是顶点集 $\{1,2,3,4\}$ 上的图,$A\in K^{4\times4}$ 由 $A_{uv}=\lambda_u+\lambda_v$($uv\in E(H)$)、其余为 $0$ 给出。记完全图 $K_4$ 的三个完美匹配为 $\mathfrak m_1=\{12,34\}$、$\mathfrak m_2=\{13,24\}$、$\mathfrak m_3=\{14,23\}$,$\omega_j=\prod_{uv\in\mathfrak m_j}(\lambda_u+\lambda_v)$。则 $\omega_1,\omega_2,\omega_3$ 都非零且

$$
\omega_1+\omega_2+\omega_3=0.\tag{4.1}
$$

于是,记 $p=\mathrm{pm}(H)\in\{0,1,2,3\}$:当 $p\in\{1,2\}$ 时 $\operatorname{rank}_KA=4$;当 $p\in\{0,3\}$ 且 $H$ 有边时 $\operatorname{rank}_KA=2$;$H$ 无边时为 $0$。$H$ 的邻接矩阵在 $\mathbb F_2$ 上的秩:当 $p\in\{1,3\}$ 时为 $4$;当 $p\in\{0,2\}$ 且 $H$ 有边时为 $2$;$H$ 无边时为 $0$。并且 $p=2$ 当且仅当 $H$ 是四圈或 $K_4$ 去掉一条边(菱形),$p=3$ 当且仅当 $H=K_4$。故以 $A_H$ 记 $H$ 的邻接矩阵,

$$
\operatorname{rank}_KA-\operatorname{rank}_{\mathbb F_2}A_H=\begin{cases}2, & \mathrm{pm}(H)=2,\\ -2, & H=K_4,\\ 0, & \text{其余情形}.\end{cases}\tag{4.2}
$$

**证明。** 由 $\lambda$ 两两不同,每个因子 $\lambda_u+\lambda_v$ 非零,故 $\omega_j\ne0$。展开:

$$
\begin{aligned}
\omega_1&=\lambda_1\lambda_3+\lambda_1\lambda_4+\lambda_2\lambda_3+\lambda_2\lambda_4,\\
\omega_2&=\lambda_1\lambda_2+\lambda_1\lambda_4+\lambda_3\lambda_2+\lambda_3\lambda_4,\\
\omega_3&=\lambda_1\lambda_2+\lambda_1\lambda_3+\lambda_4\lambda_2+\lambda_4\lambda_3 .
\end{aligned}
$$

六个单项式 $\lambda_u\lambda_v$($u<v$)中每一个恰好出现在两行里,特征 $2$ 中相消,得 (4.1)。$H$ 的完美匹配就是包含于 $E(H)$ 的那些 $\mathfrak m_j$,故由约定 2.4,$\operatorname{Pf}(A)=\sum_{\mathfrak m_j\subseteq E(H)}\omega_j$:$p=0$ 时为 $0$;$p=1$ 时为某个 $\omega_j\ne0$;$p=2$ 时为两个 $\omega$ 之和,由 (4.1) 等于第三个,非零;$p=3$ 时为 $0$。二元子集 $\{u,v\}$ 上的 Pfaffian 是 $A_{uv}$,非零当且仅当 $uv$ 是边;一元与三元子集的主子式为零。由 (2.4) 得 $K$ 上的秩。$\mathbb F_2$ 上(边权为 $1$)的 Pfaffian 是 $p\bmod2$,同理得 $\mathbb F_2$ 上的秩。$p=2$ 时 $E(H)$ 恰含两个 $\mathfrak m_j$,两者之并是四圈;$E(H)$ 至多再含第三个匹配的一条边,否则 $p=3$。四圈本身与四圈添一条弦(即菱形)都只含两个 $\mathfrak m_j$。$p=3$ 时 $E(H)$ 含全部六条边。(4.2) 由前述两张秩表逐项相减。∎

## 5. 不交并的修正和与符号

**定理 5.1（不交并的修正和）。** 设 $n\ge3$ 为奇数,$\mathtt q\ge2$,$[N]=Q_1\sqcup\cdots\sqcup Q_s$,$\Gamma$ 在不同的 $Q_j$ 之间没有边,$\Gamma_j=\Gamma[Q_j]$,$\mathrm{col}$ 是任一着色。记 $\Delta_j=\Delta(\Gamma_j,\mathrm{col}|_{Q_j},n)$,它按约定 2.2 对同一个 $\mathtt q$ 与同一个 $G$ 计算。则:

(a) $\Delta=\sum_{j=1}^s\Delta_j$。

(b) 若 $\Gamma_j$ 不含偶圈,或 $Q_j$ 中的量子比特至多占据三个方,则 $\Delta_j=0$。

(c) 若 $\Gamma_j$ 是长度 $L\ge4$ 的偶圈,则 $\Delta_j$ 的每个求和项属于 $\{0,2\}$,从而 $\Delta_j\ge0$;若另有 $n\ge5$,且这 $L$ 个量子比特位于 $L$ 个两两不同的方(从而 $\mathtt q\ge L$),则 $\Delta_j>0$。

(d) 若 $|Q_j|=4$,且这四个量子比特位于四个两两不同的方 $c_1,c_2,c_3,c_4$(从而 $\mathtt q\ge4$),则

$$
\Delta_j=\begin{cases}2D, & \mathrm{pm}(\Gamma_j)=2,\\ -2D, & \Gamma_j=K_4,\\ 0, & \text{其余情形},\end{cases}
$$

其中 $D=(n-1)(n-2)(n-3)\,n^{\mathtt q-4}$ 如 (2.2)。

**证明。** (a) $\lambda_u$ 只依赖于 $\mathrm{col}(u)$,所以 $M_t[Q_j]$ 与 $\Gamma^{\pi_t}[Q_j]$ 分别是对 $(\Gamma_j,\mathrm{col}|_{Q_j})$ 构造的 $M_t$ 与 $\Gamma_j^{\pi_t}$。$\Gamma$ 是以 $Q_1,\dots,Q_s$ 为块的分块对角阵,$M_t=\Lambda_t\Gamma+\Gamma\Lambda_t$ 与 $\Gamma^{\pi_t}$ 也是,故对每个 $t$ 有 $\rho_t=\sum_j\rho_t^{(j)}$ 与 $r(\pi_t)=\sum_jr^{(j)}(\pi_t)$,其中上标 $(j)$ 表示对 $(\Gamma_j,\mathrm{col}|_{Q_j})$ 计算的量。对 $t\ne0$ 求和即得。

(b) 若 $\Gamma_j$ 不含偶圈,由推论 3.4,$\Delta_j=0$。若 $Q_j$ 至多占据三个方,则对每个 $t$,$f_t$ 在这些方上至多取三个值,由推论 3.2(或母卷命题 4.1)每个求和项为零。

(c) 对每个 $t$,$(\Gamma_j)^{\pi_t}$ 的图是偶圈 $\Gamma_j$ 的生成子图。若它缺至少一条边,它是若干条路的不交并,不含偶圈,由定理 3.3 与定理 3.1(a),求和项为 $0$。若它等于整个圈 $Z=\Gamma_j$,由命题 4.1 的最后一句,求和项为 $2$ 或 $0$。

再设 $n\ge5$,并沿圈把量子比特记为 $z_1,\dots,z_L$($z_iz_{i+1}$ 与 $z_Lz_1$ 是边),$z_i$ 位于方 $c_i$,诸 $c_i$ 两两不同。取四个两两不同的剩余类 $e_a,e_b,e_c,e_d\in\mathbb Z/n$(由 $n\ge5$ 可取),按位置给出指数

$$
(e_a,\ e_b,\ e_c,\ e_d,\ e_c,\ e_d,\ \dots,\ e_c,\ e_d),
$$

即 $z_1,z_2$ 分别取 $e_a,e_b$,$i\ge3$ 时 $z_i$ 在 $i$ 为奇数时取 $e_c$、为偶数时取 $e_d$。若 $\mathtt q$ 是某个 $c_i$,就把该位置上的那个符号所对应的剩余类选为 $0$(四个剩余类只需两两不同,可以如此选择)。由于诸 $c_i$ 两两不同,且对 $c<\mathtt q$ 的 $t_c$ 可以任意指定,存在 $t\in G$ 使 $f_t(c_i)$ 等于第 $i$ 个位置的指数。记 $a=\zeta^{e_a}$ 等,它们两两不同。相邻位置取值不同,故 $(\Gamma_j)^{\pi_t}=Z$。边 $z_1z_2,z_2z_3,\dots,z_Lz_1$ 的权依次为 $a+b,\ b+c,\ c+d,\ c+d,\ \dots,\ c+d,\ d+a$,于是

$$
\frac{\prod_{Z^{(1)}}w_t}{\prod_{Z^{(2)}}w_t}=\frac{(a+b)(c+d)^{L/2-1}}{(b+c)(c+d)^{L/2-2}(d+a)}=\frac{(a+b)(c+d)}{(b+c)(a+d)},
$$

而 $(a+b)(c+d)+(b+c)(a+d)=ad+bc+ab+cd=(a+c)(b+d)\ne0$。故 $\alpha_t(Z)\ne1$,该项为 $2$,从而 $\Delta_j\ge2>0$。

(d) 若 $f_t$ 在 $c_1,\dots,c_4$ 上取四个两两不同的值,则四个 $\lambda$ 两两不同,$(\Gamma_j)^{\pi_t}=\Gamma_j$,由命题 4.2 的 (4.2),求和项为 $2$、$-2$ 或 $0$,按 $\Gamma_j$ 所属情形而定。否则 $f_t$ 在这四个方上至多取三个值,由推论 3.2 求和项为 $0$。前一类 $t$ 恰有 $D$ 个(约定 2.2)。∎

**推论 5.2（四方单比特分支的显式修正与符号）。** 设 $n\ge3$ 为奇数,$\mathtt q\ge4$,$\Gamma$ 与 $\mathrm{col}$ 如定理 5.1,且每个 $\Gamma_j$ 属于下列三类之一:(i) 不含偶圈;(ii) $Q_j$ 至多占据三个方;(iii) $|Q_j|=4$ 且这四个量子比特位于四个两两不同的方。记 $N_2$ 为第 (iii) 类中满足 $\mathrm{pm}(\Gamma_j)=2$ 的分支数(即四圈与菱形),$N_3$ 为第 (iii) 类中 $\Gamma_j=K_4$ 的分支数。则对以 $\Gamma$ 为图形式的稳定子态,

$$
S_n-S_n^{\mathrm{mask}}=\frac{(n-2)(n-3)}{n^2}\,(N_2-N_3)\,\log2 .\tag{5.1}
$$

当 $n\ge5$ 时,差的符号是 $N_2-N_3$ 的符号,且 $S_n=S_n^{\mathrm{mask}}$ 当且仅当 $N_2=N_3$;当 $n=3$ 时两边都为零。特别地,单个四圈分支给出母卷命题 5.1 的值 $\tfrac{(n-2)(n-3)}{n^2}\log2$,单个 $K_4$ 分支给出 $-\tfrac{(n-2)(n-3)}{n^2}\log2$。

**证明。** 由定理 5.1(a),$\Delta=\sum_j\Delta_j$。第 (i)、(ii) 类分支由定理 5.1(b) 贡献 $0$;第 (iii) 类分支由定理 5.1(d) 贡献 $2D$、$-2D$ 或 $0$;同时属于 (i) 与 (iii) 的分支不含偶圈,因而不是四圈、菱形或 $K_4$,在两种算法下都贡献 $0$。故 $\Delta=2D(N_2-N_3)$,代入 (2.1) 与 (2.2) 得 (5.1)。$n\ge5$ 时系数 $(n-2)(n-3)/n^2>0$,$n=3$ 时为零。∎

## 6. 两侧界与完全多部型

**定理 6.1（单字符两侧界）。** 设 $n\ge3$ 为奇数,$\mathtt q\ge2$,$\Gamma$ 与 $\mathrm{col}$ 任意,$t\in G$。则

$$
\rho_t\le\min\{\,2\,r(\pi_t),\ 2\,\nu(H_t)\,\},\qquad r(\pi_t)\le2\,\nu(H_t),
$$

并且当 $H_t$ 有边时 $\rho_t\ge2$、$r(\pi_t)\ge2$。上界 $\rho_t=2r(\pi_t)$ 可以达到:当 $n\ge5$、$\mathtt q\ge4$ 时,取 $N=4$、$\Gamma$ 为四圈、四个量子比特位于四个不同的方,且 $f_t$ 在这四个方上取四个两两不同的值,则 $\rho_t=4$、$r(\pi_t)=2$。下界 $\rho_t=2$ 可以与 $r(\pi_t)=2\lfloor k/2\rfloor$ 同时出现,其中 $k\le\min(n,\mathtt q)$ 可取到 $\min(n,\mathtt q)$(定理 6.2);故允许 $n$ 与 $\mathtt q$ 增大时,比值 $\rho_t/r(\pi_t)$ 没有正的下界。

**证明。** 由约定 2.2,$M_t=\Lambda_t\Gamma^{\pi_t}+\Gamma^{\pi_t}\Lambda_t$,而 $\Lambda_t$ 可逆,故 $\rho_t\le\operatorname{rank}_F(\Lambda_t\Gamma^{\pi_t})+\operatorname{rank}_F(\Gamma^{\pi_t}\Lambda_t)=2\operatorname{rank}_F\Gamma^{\pi_t}=2r(\pi_t)$。$M_t$ 与 $\Gamma^{\pi_t}$ 都是以 $H_t$ 为支撑图的交错阵(前者在 $F$ 上,后者在 $\mathbb F_2$ 上),由 (2.4) 两者的秩都不超过 $2\nu(H_t)$。$H_t$ 有边时两者都是非零交错阵,秩至少为 $2$。上界的例子:此时 $H_t$ 是整个四圈,四个 $\lambda$ 两两不同,命题 4.2 给出 $\rho_t=4$($\mathrm{pm}=2$),$r(\pi_t)=2$。∎

**定理 6.2（完全多部型的秩与负修正）。** 设 $n\ge3$ 为奇数,$\mathtt q\ge2$,着色 $\mathrm{col}$ 占据 $p$ 个方,并设 $\Gamma$ 满足:凡 $\mathrm{col}(u)\ne\mathrm{col}(v)$ 都有 $\Gamma_{uv}=1$(同一方内的边任意)。对 $t\in G$ 记 $k_t$ 为 $f_t$ 在被占据方上取到的不同值的个数。则对每个 $t\in G$,

$$
\rho_t=\begin{cases}2, & k_t\ge2,\\ 0, & k_t=1,\end{cases}\qquad r(\pi_t)=2\Big\lfloor\frac{k_t}{2}\Big\rfloor .
$$

满足 $k_t=k$ 的 $t$ 恰有 $S(p,k)\,(n-1)_{k-1}\,n^{\mathtt q-p}$ 个,于是

$$
\Delta=-2\,n^{\mathtt q-p}\sum_{k=4}^{\min(p,n)}S(p,k)\,(n-1)_{k-1}\Big(\Big\lfloor\frac k2\Big\rfloor-1\Big),\tag{6.1}
$$

空和为 $0$。特别地 $\Delta\le0$,且 $\Delta<0$ 当且仅当 $p\ge4$ 且 $n\ge5$;当 $k_t\ge2$ 时 $\rho_t/r(\pi_t)=1/\lfloor k_t/2\rfloor$。$p=4$ 时 $\Delta=-2D$。

**证明。** 对 $u\ne v$:若 $\mathrm{col}(u)\ne\mathrm{col}(v)$,则 $\Gamma_{uv}=1$,$(M_t)_{uv}=\lambda_u+\lambda_v$;若 $\mathrm{col}(u)=\mathrm{col}(v)$,则 $\lambda_u=\lambda_v$,$(M_t)_{uv}=0=\lambda_u+\lambda_v$。对角元为 $0=\lambda_u+\lambda_u$。故以 $\lambda=(\lambda_u)_u$ 与全一列向量 $\mathbf 1$ 记,

$$
M_t=\lambda\,\mathbf 1^{\mathsf T}+\mathbf 1\,\lambda^{\mathsf T},
$$

其秩至多为 $2$。$k_t=1$ 时 $\lambda$ 在全部量子比特上是常数(空方不含量子比特),$M_t=0$。$k_t\ge2$ 时存在 $\lambda_u\ne\lambda_v$,$M_t$ 非零,秩至少为 $2$,故 $\rho_t=2$。

对 $r(\pi_t)$:$\Gamma^{\pi_t}_{uv}=1$ 当且仅当 $\lambda_u\ne\lambda_v$。按 $\lambda$ 的值把 $[N]$ 分成 $k=k_t$ 个非空纤维 $V_1,\dots,V_k$,则 $u\in V_i$ 所在的行是 $V_i$ 的补集的示性向量。同一纤维内的行彼此相同,列亦然;删去重复的行与列不改变秩,所得 $k\times k$ 矩阵是 $J_k-I_k$($J_k$ 为全一阵)。在 $\mathbb F_2$ 上 $(J_k-I_k)^2=J_k^2-2J_k+I_k=kJ_k+I_k$。$k$ 为偶数时它等于 $I_k$,秩为 $k$。$k$ 为奇数时 $(J_k-I_k)\mathbf 1=(k-1)\mathbf 1=0$,秩至多 $k-1$,而删去最后一行一列所得 $J_{k-1}-I_{k-1}$ 的阶为偶数,秩为 $k-1$。故秩为 $2\lfloor k/2\rfloor$。

计数:设 $O$ 为被占据方之集。若 $\mathtt q\in O$,满足 $k_t=k$ 的 $f_t|_O$ 对应于把 $O$ 分成 $k$ 块、含 $\mathtt q$ 的块取值 $0$、其余 $k-1$ 块取两两不同的非零值,共 $S(p,k)(n-1)_{k-1}$ 种;$O$ 外的 $\mathtt q-p$ 个坐标 $t_c$ 自由,得 $S(p,k)(n-1)_{k-1}n^{\mathtt q-p}$。若 $\mathtt q\notin O$,共 $S(p,k)(n)_k$ 种,$O$ 外有 $\mathtt q-1-p$ 个自由坐标,而 $(n)_k\,n^{\mathtt q-1-p}=(n-1)_{k-1}\,n^{\mathtt q-p}$,结果相同。由于 $k_t\le\min(p,n)$,

$$
\Delta=\sum_{k=2}^{\min(p,n)}S(p,k)(n-1)_{k-1}n^{\mathtt q-p}\Big(2-2\Big\lfloor\frac k2\Big\rfloor\Big),
$$

$k=2,3$ 的项为零,即得 (6.1)。各项非正;存在 $k\ge4$ 的项当且仅当 $\min(p,n)\ge4$,而 $n$ 为奇数,即 $p\ge4$ 且 $n\ge5$,此时 $k=4$ 的项为 $-2n^{\mathtt q-p}S(p,4)(n-1)_3<0$。$p=4$ 时 (6.1) 只剩 $k=4$ 一项 $-2n^{\mathtt q-4}(n-1)(n-2)(n-3)=-2D$。∎

满足定理 6.2 假设的例子有:$p$ 个量子比特位于 $p$ 个不同方的完全图 $K_p$;各部分别恰为一个方的全部量子比特的完全多部图。

## 7. 图形式依赖与母卷开放问题 6.3

**定理 7.1（至多三块的掩码秩与图形式无关）。** 设 $\psi$ 是 $N$ 个量子比特上的规范化纯稳定子态,$\mathrm{col}$ 是着色,$O$ 是被占据方之集,$\Gamma$ 与 $\Gamma'$ 是 $\psi$ 的两个图形式。则:

(a) 对每个在 $O$ 上的诱导分割至多有三块的 $\pi\in\Pi(\mathtt q)$,$r_\Gamma(\pi)=r_{\Gamma'}(\pi)$。

(b) 对每个奇数 $n\ge3$,$\sum_{0\ne t\in G}\rho_t(\Gamma)=\sum_{0\ne t\in G}\rho_t(\Gamma')$(这是母卷注 3.2 的重述)。

(c) 对每个奇数 $n\ge3$,

$$
\Delta(\Gamma,\mathrm{col},n)-\Delta(\Gamma',\mathrm{col},n)=\sum_{t\in G:\ k_t\ge4}\big(r_{\Gamma'}(\pi_t)-r_\Gamma(\pi_t)\big).
$$

**证明。** (a) 掩码矩阵 $\Gamma^\pi$ 只取决于被占据方中哪些落在 $\pi$ 的同一块,即只取决于 $\pi$ 在 $O$ 上的诱导分割。若诱导分割只有一块,则 $\Gamma^\pi=(\Gamma')^\pi=0$。否则设诱导分割的块为 $B_1,\dots,B_k$,$k\in\{2,3\}$,令 $\mathrm{col}'(u)=j$ 当 $\mathrm{col}(u)\in B_j$;这是 $\psi$ 的一个 $k$ 方着色,且在 $\mathrm{col}'$ 下最细分割 $\{\{1\},\dots,\{k\}\}$ 的掩码矩阵就是 $\Gamma^\pi$(对 $\Gamma'$ 同理)。对 $k$ 方态 $(\psi,\mathrm{col}')$ 用母卷推论 4.2,取 $n=3$(此时 $\min(n,k)\le3$):$k=2$ 时 $\Pi_3(2)$ 为空,得 $S_3^{(2)}(\psi,\mathrm{col}')=\tfrac{\log2}{2}\,r_\Gamma(\pi)$;左边按约定 2.2 只依赖 $\psi$ 与 $\mathrm{col}'$,故 $r_\Gamma(\pi)=r_{\Gamma'}(\pi)$。$k=3$ 时

$$
S_3^{(3)}(\psi,\mathrm{col}')=\frac{\log2}{6}\Big[\sum_{\sigma\in\Pi_2(3)}r'_\Gamma(\sigma)+r_\Gamma(\pi)\Big],
$$

其中 $r'_\Gamma(\sigma)$ 是 $\mathrm{col}'$ 下的掩码秩;每个 $\sigma\in\Pi_2(3)$ 的掩码矩阵等于 $\Gamma^{\hat\sigma}$,$\hat\sigma\in\Pi(\mathtt q)$ 是按 $\sigma$ 合并 $B_1,B_2,B_3$ 并把 $[\mathtt q]\setminus O$ 并入其中一块所得的二块分割,由 $k=2$ 的情形它与图形式无关。于是 $r_\Gamma(\pi)$ 等于只依赖 $\psi$ 与 $\mathrm{col}$ 的量,对 $\Gamma'$ 取同一值。

(b) 由母卷定理 3.1,对 $\psi$ 的每个图形式都有 $Z_n^{(\mathtt q)}=2^{-\frac12\sum_{t\ne0}\rho_t}$,而左边只依赖 $\psi$ 与 $\mathrm{col}$(母卷注 3.2)。

(c) $\pi_t$ 在 $O$ 上的诱导分割恰有 $k_t$ 块。由 (b),两个修正和之差为 $\sum_{t\ne0}\big(r_{\Gamma'}(\pi_t)-r_\Gamma(\pi_t)\big)$;由 (a),$k_t\le3$ 的项为零;$t=0$ 时 $k_t\le1$。∎

**定理 7.2（同一态的两种图形式）。** 设 $n\ge3$ 为奇数,$\mathtt q\ge4$,$N=4$,量子比特 $1,2,3,4$ 依次位于两两不同的方 $c_1,c_2,c_3,c_4$。记 $K_{1,3}$ 为以 $1$ 为中心的星 $\{12,13,14\}$,$K_4$ 为完全图,$C_4=\{12,23,34,14\}$,$P_4=\{13,23,24\}$(路 $1$–$3$–$2$–$4$)。则:

(a) $K_4$ 与 $K_{1,3}$ 是同一个态的图形式;$\Delta(K_{1,3})=0$,$\Delta(K_4)=-2D$;对 $f_t$ 在 $c_1,\dots,c_4$ 上取四个两两不同值的 $t$,$r_{K_4}(\pi_t)=4$、$r_{K_{1,3}}(\pi_t)=2$,对其余 $t$ 两者相等;并且

$$
S_n^{\mathrm{mask}}(K_4)-S_n^{\mathrm{mask}}(K_{1,3})=\frac{(n-2)(n-3)}{n^2}\log2 .
$$

(b) $C_4$ 与 $P_4$ 是同一个态的图形式;$\Delta(P_4)=0$,$\Delta(C_4)=2D$;对上述 $t$,$r_{P_4}(\pi_t)=4$、$r_{C_4}(\pi_t)=2$,对其余 $t$ 两者相等;并且

$$
S_n^{\mathrm{mask}}(P_4)-S_n^{\mathrm{mask}}(C_4)=\frac{(n-2)(n-3)}{n^2}\log2 .
$$

(c) $\{1,2,3,4\}$ 上的每个图都局部补等价于一个不含偶圈的图。因此,四个量子比特位于四个两两不同方的每个稳定子态都有一个图形式使 $S_n=S_n^{\mathrm{mask}}$;对推论 5.2 中的每个不交并,逐个替换其第 (iii) 类分支,也得到一个使 $S_n=S_n^{\mathrm{mask}}$ 的图形式。

特别地,当 $n\ge5$ 时,$S_n^{\mathrm{mask}}$ 不是 $(\psi,\mathrm{col})$ 的函数;母卷命题 5.1 的偏差属于四圈这一图形式,同一个态的图形式 $P_4$ 给出精确值。

**证明。** 第一步(局部补的局部 Clifford 实现)。设 $\Gamma$ 是 $[N]$ 上的图,$v$ 是顶点,$U=e^{i\pi X_v/4}\prod_{u\in N_\Gamma(v)}\mathsf S_u$。下面验证 $U|\Gamma\rangle=\mu\,|\tau_v(\Gamma)\rangle$,$|\mu|=1$;这一结论是已知的(先例见第 9 节:Van den Nest、Dehaene、De Moor;Hein、Eisert、Briegel),此处的验证只用约定 2.5。由 $XZ=-ZX$ 得 $e^{i\theta X}Ze^{-i\theta X}=Ze^{-2i\theta X}=\cos2\theta\,Z+\sin2\theta\,Y$,取 $\theta=\pi/4$ 得 $Y$;又 $e^{i\pi X/4}$ 与 $X$ 对易,$\mathsf SX\mathsf S^\dagger=Y$,$\mathsf S$ 与 $Z$ 对易。记 $\Gamma'=\tau_v(\Gamma)$,$N=N_\Gamma(v)$,$K'_w$ 为 $\Gamma'$ 的生成元。由于 $\tau_v$ 不改变 $v$ 的邻域,$UK_vU^\dagger=K_v=K'_v$。对 $u\in N$,$K_u=X_uZ_v\prod_{w\in N_\Gamma(u)\setminus\{v\}}Z_w$,故 $UK_uU^\dagger=Y_uY_v\prod_{w\in N_\Gamma(u)\setminus\{v\}}Z_w$;另一方面 $N_{\Gamma'}(u)\setminus\{v\}=(N_\Gamma(u)\setminus\{v\})\triangle(N\setminus\{u\})$,在 $K'_vK'_u$ 中 $v$ 上是 $XZ=-iY$,$u$ 上是 $ZX=iY$,其余顶点 $w$ 上 $Z$ 的次数为 $[w\in N\setminus\{u\}]+[w\in N_{\Gamma'}(u)\setminus\{v\}]\equiv[w\in N_\Gamma(u)\setminus\{v\}]\pmod 2$,于是 $K'_vK'_u=Y_vY_u\prod_{w\in N_\Gamma(u)\setminus\{v\}}Z_w=UK_uU^\dagger$。对 $w\notin N\cup\{v\}$,$U$ 不作用在 $w$ 上,$N_\Gamma(w)$ 不含 $v$ 且 $\tau_v$ 不改变它,而 $\mathsf S$ 与 $Z$ 对易,故 $UK_wU^\dagger=K_w=K'_w$。所以 $U\mathcal S_\Gamma U^\dagger\subseteq\mathcal S_{\Gamma'}$,两边都有 $2^N$ 个元素,从而相等;$U|\Gamma\rangle$ 被 $\mathcal S_{\Gamma'}$ 的每个元素固定,由约定 2.5 它是 $|\Gamma'\rangle$ 的模为 $1$ 的倍数。$e^{i\pi X/4}$ 与 $\mathsf S$ 把 Pauli 矩阵共轭为 Pauli 矩阵,是单比特 Clifford 酉阵;若 $\psi=\lambda(U_1\otimes\cdots\otimes U_N)|\Gamma\rangle$,则 $\psi=\lambda\mu(U_1\otimes\cdots\otimes U_N)U^{-1}|\Gamma'\rangle$,故 $\Gamma'$ 也是 $\psi$ 的图形式。经有限次局部补得到的图同理。

第二步(两条链)。$K_{1,3}$ 中 $N(1)=\{2,3,4\}$,$\tau_1$ 添上 $23,24,34$,得 $K_4$。$C_4$ 中 $N(1)=\{2,4\}$,$\tau_1$ 添上 $24$,得 $\{12,14,23,24,34\}$;其中 $N(2)=\{1,3,4\}$,$\tau_2$ 添上 $13$、删去 $14$ 与 $34$,得 $\{12,13,23,24\}$;其中 $N(3)=\{1,2\}$,$\tau_3$ 删去 $12$,得 $\{13,23,24\}=P_4$。由第一步,两对图分别是同一个态的图形式。

第三步(修正和与掩码秩)。$K_{1,3}$ 与 $P_4$ 是森林,由推论 3.4 修正和为 $0$。由定理 5.1(d)(取 $s=1$),$\Delta(K_4)=-2D$,而 $\mathrm{pm}(C_4)=2$ 给出 $\Delta(C_4)=2D$。对 $f_t$ 在 $c_1,\dots,c_4$ 上取四个不同值的 $t$,掩码图是整个图,由命题 4.2 的 $\mathbb F_2$ 秩表:$\mathrm{pm}(K_4)=3$、$\mathrm{pm}(P_4)=1$ 给出秩 $4$,$\mathrm{pm}(K_{1,3})=0$、$\mathrm{pm}(C_4)=2$ 给出秩 $2$。其余 $t$ 满足 $k_t\le3$,由定理 7.1(a) 两种图形式的掩码秩相等。最后,同一个态与着色的 $S_n$ 相同,由 (2.1),$S_n^{\mathrm{mask}}(\Gamma)=S_n-\frac{\log2}{2(n-1)n^{\mathtt q-2}}\Delta(\Gamma)$,代入上述修正和与 (2.2) 得 (a)(b) 中的差值。$n\ge5$ 时差值非零,故 $S_n^{\mathrm{mask}}$ 不是 $(\psi,\mathrm{col})$ 的函数。

第四步((c))。设 $\Gamma_0$ 是 $\{1,2,3,4\}$ 上的图。若它不含偶圈,无须变换。否则它含偶圈;四个顶点上的偶圈只能是四圈,故 $\Gamma_0$ 是四圈添 $0$、$1$ 或 $2$ 条弦,即 $C_4$ 型、菱形或 $K_4$。对 $K_4$,任一顶点 $v$ 处的 $\tau_v$ 删去 $v$ 的三个邻点之间的三条边,得以 $v$ 为中心的星。对菱形 $K_4\setminus\{ab\}$,设 $c,d$ 为另两个顶点,$N(c)=\{a,b,d\}$,$\tau_c$ 添上 $ab$、删去 $ad$ 与 $bd$,得 $\{ca,cb,cd,ab\}$,即三角形 $abc$ 加悬挂边 $cd$,其唯一的圈是三角形,不含偶圈。对四圈,在任一顶点 $v$ 处作 $\tau_v$ 会添上 $v$ 的两个邻点之间的弦,得菱形,再按上一句处理。由第一步,所得图是同一个态的图形式;由母卷约定 2.3,每个稳定子态都有图形式,故四个量子比特分属四方的态都有一个 $\{1,2,3,4\}$ 上的图作为图形式,再经上述变换得到不含偶圈的图形式,由推论 3.4 得 $S_n=S_n^{\mathrm{mask}}$。对推论 5.2 中的不交并,在第 (iii) 类分支内的顶点处作局部补只改变该分支内部的边,逐个分支替换后,每个分支属于第 (i) 或第 (ii) 类,由定理 5.1(a)(b) 得 $\Delta=0$,再用 (2.1)。∎

**定理 7.3（母卷开放问题 6.3 在图形式读法下的否定回答）。** 设 $n\ge5$ 为奇数,$\mathtt q\ge4$。存在两个 $\mathtt q$ 方的图态 $|\Gamma_A\rangle$、$|\Gamma_B\rangle$,各含 $32$ 个量子比特,第 $1,2,3,4$ 方各含 $8$ 个量子比特、其余方为空,使得对每个 $\pi\in\Pi(\mathtt q)$ 都有 $r_{\Gamma_A}(\pi)=r_{\Gamma_B}(\pi)$,但

$$
S_n(\Gamma_A)-S_n(\Gamma_B)=\frac{(n-2)(n-3)}{n^2}\log2>0 .
$$

于是对 $n\ge5$、$\mathtt q\ge4$,$S_n$ 不是图形式的掩码秩族 $\big(r(\pi)\big)_{\pi\in\Pi(\mathtt q),\,|\pi|\ge2}$ 的函数。

构造如下。下列各图都以四个量子比特为顶点,其中第 $i$ 个量子比特位于第 $i$ 方($i=1,2,3,4$),边按方的标号书写:星 $K_{1,3}=\{12,13,14\}$,路 $P^{\flat}=\{12,14,23\}$,路 $P^{\sharp}=\{12,13,24\}$,四圈 $Z=\{13,14,23,24\}$,以及四个「樱桃」$V_1=\{12,13\}$、$V_2=\{12,14\}$、$V_3=\{13,14\}$、$V_4=\{23,24\}$。$\Gamma_A$ 是三个 $K_{1,3}$、一个 $P^{\flat}$、一个 $P^{\sharp}$、一个 $Z$ 与八个孤立量子比特(第 $1,2,3,4$ 方各两个)的不交并;$\Gamma_B$ 是 $V_1,V_2,V_3,V_4$ 各两份的不交并。

**证明。** 先算 $\mathtt q=4$ 时的掩码秩。对四个量子比特分属四方的单个分支 $\Gamma_0$ 与 $\{1,2,3,4\}$ 的分割 $\sigma$(块之间用 / 分隔):若 $\sigma=a/bcd$,$\Gamma_0^\sigma$ 只含 $a$ 的关联边,是星或空图,秩为 $2$ 当 $a$ 有邻点、否则为 $0$(定理 3.3);若 $\sigma=ab/cd$,$\Gamma_0^\sigma$ 是以二阶矩阵 $\begin{pmatrix}\Gamma_{ac}&\Gamma_{ad}\\ \Gamma_{bc}&\Gamma_{bd}\end{pmatrix}$ 为非对角块的分块反对角阵,秩为该二阶矩阵的 $\mathbb F_2$ 秩的两倍;若 $|\sigma|=3$,$\Gamma_0^\sigma$ 是 $\Gamma_0$ 删去唯一二元块内部的边(若有)所得的图,若 $|\sigma|=4$,它是 $\Gamma_0$ 本身,其 $\mathbb F_2$ 秩由命题 4.2 的 $\mathbb F_2$ 秩表给出(完美匹配个数为奇数时为 $4$,为偶数且有边时为 $2$,无边时为 $0$)。逐项应用得下表;孤立量子比特所在的掩码矩阵为零,不计入。

| 分支 | 1/234 | 2/134 | 3/124 | 4/123 | 12/34 | 13/24 | 14/23 | 12/3/4 | 13/2/4 | 14/2/3 | 23/1/4 | 24/1/3 | 34/1/2 | 1/2/3/4 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $K_{1,3}$ | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| $P^{\flat}$ | 2 | 2 | 2 | 2 | 4 | 4 | 2 | 4 | 4 | 2 | 2 | 4 | 4 | 4 |
| $P^{\sharp}$ | 2 | 2 | 2 | 2 | 4 | 2 | 4 | 4 | 2 | 4 | 4 | 2 | 4 | 4 |
| $Z$ | 2 | 2 | 2 | 2 | 2 | 4 | 4 | 2 | 4 | 4 | 4 | 4 | 2 | 2 |
| $V_1$ | 2 | 2 | 2 | 0 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| $V_2$ | 2 | 2 | 0 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| $V_3$ | 2 | 0 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| $V_4$ | 0 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| $\Gamma_A$ | 12 | 12 | 12 | 12 | 16 | 16 | 16 | 16 | 16 | 16 | 16 | 16 | 16 | 16 |
| $\Gamma_B$ | 12 | 12 | 12 | 12 | 16 | 16 | 16 | 16 | 16 | 16 | 16 | 16 | 16 | 16 |

由定理 5.1(a) 的分块对角论证,掩码秩对分支可加,故 $\Gamma_A$ 行是 $3K_{1,3}+P^{\flat}+P^{\sharp}+Z$ 各行之和,$\Gamma_B$ 行是 $2(V_1+V_2+V_3+V_4)$ 各行之和,两行逐项相等。

对一般的 $\mathtt q\ge4$,两个图态都只占据第 $1,2,3,4$ 方,由定理 7.1(a) 证明的第一句,$r(\pi)$ 只依赖 $\pi$ 在 $\{1,2,3,4\}$ 上的诱导分割;诱导分割只有一块时两边都是 $0$,否则它是表中的某一列。故对每个 $\pi\in\Pi(\mathtt q)$ 都有 $r_{\Gamma_A}(\pi)=r_{\Gamma_B}(\pi)$。母卷第 5 节的 $S_n^{\mathrm{mask}}=\frac{\log2}{2(n-1)n^{\mathtt q-2}}\sum_{|\pi|\ge2}(n-1)_{|\pi|-1}r(\pi)$ 是掩码秩族的函数,所以 $S_n^{\mathrm{mask}}(\Gamma_A)=S_n^{\mathrm{mask}}(\Gamma_B)$。

由定理 5.1:$K_{1,3}$、$P^{\flat}$、$P^{\sharp}$、各 $V_i$ 与孤立量子比特都不含偶圈,贡献 $0$;$Z$ 是四个量子比特分属四方的四圈,$\mathrm{pm}(Z)=2$,贡献 $2D$。故 $\Delta(\Gamma_A)=2D$,$\Delta(\Gamma_B)=0$。由 (2.1) 与 (2.2),

$$
S_n(\Gamma_A)-S_n(\Gamma_B)=\frac{\log2}{2(n-1)n^{\mathtt q-2}}\cdot2D=\frac{(n-2)(n-3)}{n^2}\log2,
$$

$n\ge5$ 时为正。末句:若存在函数 $\Phi$ 使每个图态都有 $S_n=\Phi\big((r(\pi))_\pi\big)$,则 $\Gamma_A$、$\Gamma_B$ 的 $S_n$ 相同,矛盾。∎

**注 7.4（开放问题 6.3 的两种读法）。** 由定理 7.2,掩码秩族是图形式与着色的属性,不是态与着色的属性;母卷开放问题 6.3 中「两个具有相同掩码秩的稳定子态」若按掩码秩族来读,只能理解为两个具有相同掩码秩族的图形式,定理 7.3 对这一读法给出否定回答。换成态的不变量后的问法见开放问题 8.6,定理 7.3 不回答它。

## 8. 反例与不能推广的边界

**不能推广的边界。** 本卷全部陈述都在母卷的设定之内:规范化纯量子比特稳定子态、奇数 $n\ge3$、母卷约定 2.2 的复本约定。本卷不涉及偶数 $n$(母卷开放问题 6.2)、qudit 稳定子态、混合态与非稳定子态。定理 3.1 的条件是 $\rho_t=r(\pi_t)$ 的充分条件(命题 8.1);定理 3.3 只处理不含偶圈的掩码子图;推论 5.2 的闭式只覆盖其所列的三类分支,对含有其他偶圈结构的分支(例如五个或更多量子比特、含四圈以外的偶圈或位于更多方的分支),除定理 5.1(c) 的偶圈情形、定理 6.2 的完全多部情形与命题 8.3 的单个例子外,本卷不给出修正和的值或符号。定理 6.1 的下界 $2$ 不能改进为 $\rho_t\ge c\,r(\pi_t)$ 的形式:由定理 6.2,对 $k_t=k$ 的字符,$\rho_t/r(\pi_t)=1/\lfloor k/2\rfloor$。定理 7.3 只说明掩码秩族不决定 $S_n$;它不排除 $S_n$ 由某个图形式的掩码秩族与其他数据共同决定。

**命题 8.1（β 缩放判据不是必要条件:蝶形图）。** 设 $n\ge5$ 为奇数,$\mathtt q\ge4$。取五个量子比特 $1,\dots,5$ 与蝶形图 $\Gamma=\{12,13,23,14,15,45\}$(两个三角形 $1$–$2$–$3$ 与 $1$–$4$–$5$ 共用顶点 $1$)。令量子比特 $1$ 位于第 $\mathtt q$ 方,量子比特 $2,4$ 位于第 $1$ 方,量子比特 $3$ 位于第 $2$ 方,量子比特 $5$ 位于第 $3$ 方,并取 $t\in G$ 使 $t_1=1$、$t_2=2$、$t_3=3$。则 $H_t=\Gamma$ 连通,定理 3.1(b) 中的族 $(\beta_u)$ 不存在,但 $\rho_t=r(\pi_t)=4$。

**证明。** 由取法,$\lambda_1=1$,$\lambda_2=\lambda_4=\zeta$,$\lambda_3=\zeta^2$,$\lambda_5=\zeta^3$。指数 $0,1,2,3$ 在 $\mathbb Z/n$ 中两两不同($n\ge5$),六条边的端点取值都不同,故 $H_t=\Gamma$。若族 $(\beta_u)$ 存在,则由三角形 $1$–$2$–$3$ 的三个边方程,$\beta_1^2=\frac{(\beta_1\beta_2)(\beta_1\beta_3)}{\beta_2\beta_3}=\frac{(1+\zeta)(1+\zeta^2)}{\zeta+\zeta^2}=\frac{(1+\zeta)^2}{\zeta}$;由三角形 $1$–$4$–$5$,$\beta_1^2=\frac{(1+\zeta)(1+\zeta^3)}{\zeta+\zeta^3}=\frac{1+\zeta^3}{\zeta(1+\zeta)}=\frac{1+\zeta+\zeta^2}{\zeta}$。这里用了特征 $2$ 中的 $1+\zeta^2=(1+\zeta)^2$ 与 $1+\zeta^3=(1+\zeta)(1+\zeta+\zeta^2)$,以及 $\zeta\ne0,1$。两值之差为 $\frac{(1+\zeta^2)+(1+\zeta+\zeta^2)}{\zeta}=1\ne0$,矛盾。等价地,偶长闭途径 $(1,2,3,1,4,5,1)$ 的交替积不等于 $1$。另一方面,蝶形图的圈只有两个三角形,不含偶圈,由定理 3.3,$\rho_t=r(\pi_t)=2\nu(\Gamma)=4$。∎

**命题 8.2（二部掩码图上的单字符亏差可以为负）。** 设 $n=5$,$\mathtt q\ge5$。取六个量子比特与二部图 $\Gamma=\{14,15,16,24,26,34,35\}$(两侧为 $\{1,2,3\}$ 与 $\{4,5,6\}$)。令量子比特 $1$ 位于第 $\mathtt q$ 方,量子比特 $2,3$ 位于第 $1$ 方,量子比特 $4,5,6$ 依次位于第 $2,3,4$ 方,并取 $t\in G$ 使 $t_1=1$、$t_2=2$、$t_3=3$、$t_4=4$。则 $H_t=\Gamma$ 是二部图,而 $\rho_t=4<6=r(\pi_t)$。

**证明。** 记 $z=\zeta$,这时 $z$ 是 $\mathbb F_{16}$ 中的本原 $5$ 次单位根,满足 $1+z+z^2+z^3+z^4=0$。$\lambda_1=1$,$\lambda_2=\lambda_3=z$,$\lambda_4,\lambda_5,\lambda_6=z^2,z^3,z^4$;七条边的端点取值都不同,故 $H_t=\Gamma$。按 $\{1,2,3\},\{4,5,6\}$ 排序,$M_t=\begin{pmatrix}0&W\\ W^{\mathsf T}&0\end{pmatrix}$、$\Gamma^{\pi_t}=\begin{pmatrix}0&B\\ B^{\mathsf T}&0\end{pmatrix}$,其中 $B$ 的行依次为 $(1,1,1)$、$(1,0,1)$、$(1,1,0)$,$W_{xy}=B_{xy}(\lambda_x+\lambda_y)$。故 $\rho_t=2\operatorname{rank}_FW$,$r(\pi_t)=2\operatorname{rank}_{\mathbb F_2}B$。使 $\prod_xB_{x\sigma(x)}=1$ 的双射 $\sigma:\{1,2,3\}\to\{4,5,6\}$ 恰有三个:$(2,3,1)\mapsto(4,5,6)$、$(2,3,1)\mapsto(6,4,5)$、$(2,3,1)\mapsto(6,5,4)$。于是 $\det_{\mathbb F_2}B=3\bmod2=1$,$r(\pi_t)=6$;而在特征 $2$ 中

$$
\det W=T_1+T_2+T_3,\qquad
\begin{aligned}
T_1&=(z+z^2)(z+z^3)(1+z^4)=z^2(1+z)^7,\\
T_2&=(z+z^4)(z+z^2)(1+z^3)=z^2(1+z)(1+z^3)^2,\\
T_3&=(z+z^4)(z+z^3)(1+z^2)=z^2(1+z)^4(1+z^3),
\end{aligned}
$$

这里用了 $z+z^4=z(1+z^3)$、$1+z^2=(1+z)^2$、$1+z^4=(1+z)^4$。令 $s=1+z\ne0$ 与 $g=1+z+z^2$,则 $1+z^3=sg$,

$$
\frac{T_1+T_2+T_3}{z^2s^3}=s^4+g^2+s^2g=(1+z^4)+(1+z^2+z^4)+(1+z^2)(1+z+z^2)=1+z+z^2+z^3+z^4=0 .
$$

故 $\det W=0$。$W$ 的第 $2,3$ 行与第 $4,5$ 列构成的子式为 $W_{24}W_{35}-W_{25}W_{34}=W_{24}W_{35}\ne0$($W_{25}=0$),所以 $\operatorname{rank}_FW=2$,$\rho_t=4$。∎

**注 8.7（命题 8.2 的范围）。** 命题 8.2 只涉及一个字符;它说明定理 5.1(c) 中偶圈分支的逐项非负性不能推广到一般的二部掩码图。该命题不断言这个态与着色的修正和 $\Delta$ 的符号。

**命题 8.3（所有图形式的修正和都非零的态）。** 设 $n\in\{5,7\}$,$\mathtt q=N=6$,第 $u$ 个量子比特位于第 $u$ 方($u=1,\dots,6$),$\Gamma_0=\{13,14,16,23,24,25\}$(四圈 $1$–$3$–$2$–$4$–$1$ 在两个相对顶点 $1,2$ 上各挂一条悬挂边)。则 $\Gamma_0$ 的局部补等价类恰含 $40$ 个图,每个都含偶圈;对其中每个图 $\Gamma$,修正和 $\Delta(\Gamma,\mathrm{col},n)$ 的取值集合为

$$
\{-1296,\ -912,\ -864,\ 48\}\quad(n=5),\qquad \{-10320,\ -9840,\ -1440,\ 240\}\quad(n=7),
$$

都不为零。因此 $|\Gamma_0\rangle$ 的每个图形式 $\Gamma$ 都满足 $S_n\ne S_n^{\mathrm{mask}}(\Gamma)$,并且 $S_n$ 严格位于 $S_n^{\mathrm{mask}}$ 在全部图形式上的最小值与最大值之间。

**证明。** 由 Van den Nest、Dehaene、De Moor 的局部补定理(第 9 节,文献步骤),两个图态在局部 Clifford 酉阵与相位下等价,当且仅当两图局部补等价;故 $|\Gamma_0\rangle$ 的图形式恰为 $\Gamma_0$ 的局部补等价类。该类由从 $\Gamma_0$ 出发反复作局部补得到,是有限集。由定理 7.1(b),$\sum_{t\ne0}\rho_t$ 在类上是常数;而 $\sum_{t\ne0}r_\Gamma(\pi_t)=\sum_{|\pi|\ge2}(n-1)_{|\pi|-1}r_\Gamma(\pi)$ 是 $\mathbb F_2$ 上的有限计算。第 10 节的代码以 $F=\mathbb F_{16}$($n=5$)与 $F=\mathbb F_8$($n=7$)上的精确有限域运算完成以下计算:生成该等价类(得 $40$ 个图并逐一检出偶圈);对 $\Gamma_0$ 与类中另外三个图分别计算 $\sum_{t}\rho_t$,得同一值($n=5$ 时 $12328$,$n=7$ 时 $66876$);对类中每个图计算 $\sum_{t\ne0}r_\Gamma(\pi_t)$,相减得上述取值集合。本命题的证明是计算机辅助的,其有限部分由第 10 节代码的断言覆盖。最后两句由 (2.1):$\Delta>0$ 的图形式给出 $S_n^{\mathrm{mask}}<S_n$,$\Delta<0$ 的图形式给出 $S_n^{\mathrm{mask}}>S_n$。∎

**注 8.8（与定理 7.2(c) 的对照）。** 命题 8.3 与定理 7.2(c) 对照:四个量子比特分属四方时总有修正和为零的图形式,而六个量子比特分属六方时可以没有。第 10 节代码另核验:$n=5$、$N\in\{4,5\}$、$\mathtt q=N$ 且每个量子比特独占一方时,每个局部补等价类都含修正和为零的图。$N\le3$ 且每个量子比特独占一方时,被占据方至多三个,由推论 3.2 每个图的修正和都为零;这一情形由推论 3.2 直接得到,不是代码核验。

**开放问题 8.4（零修正图形式的刻画）。** 对奇数 $n\ge5$、$\mathtt q\ge4$,哪些稳定子态与着色具有修正和为零的图形式?已知:有不含偶圈的图形式者都有(推论 3.4);四个量子比特分属四方者与推论 5.2 中的不交并都有(定理 7.2(c));命题 8.3 的态没有。缺少的是把「存在零修正图形式」与局部补等价类的组合不变量联系起来的判据。

**开放问题 8.5（修正和的符号）。** 对固定的图形式,$\Delta(\Gamma,\mathrm{col},n)$ 的符号由什么决定?已知:不含偶圈或至多占据三方的分支贡献为零,偶圈分支贡献非负(定理 5.1),完全多部型贡献非正(定理 6.2),四方单比特分支按 $N_2-N_3$ 定号(推论 5.2);二部性不能保证单字符亏差非负(命题 8.2);同一个态的不同图形式可以给出相反符号(定理 7.2、命题 8.3)。缺少的是一般分支上 $\operatorname{Pf}(M_t[S])$ 与其 $\mathbb F_2$ 约化之间的统一比较。

**开放问题 8.6（态不变量形式的开放问题 6.3）。** 对奇数 $n\ge5$、$\mathtt q\ge4$,$S_n$ 是否是集合 $\{\,(r_\Gamma(\pi))_{\pi\in\Pi(\mathtt q)}:\ \Gamma\ \text{是}\ \psi\ \text{的图形式}\,\}$ 的函数?该集合只依赖 $(\psi,\mathrm{col})$。定理 7.3 的构造不回答这一问:把 $\Gamma_A$ 的四圈分支换成同一个态的不含偶圈的图形式(定理 7.2(c))会把该分支在四个方分属四块的分割上的掩码秩由 $2$ 变为 $4$(由定理 7.1(c),两种图形式的修正和相差 $2D$,只能来自这些分割),从而改变掩码秩族。命题 8.3 表明 $S_n$ 一般不是该集合上 $S_n^{\mathrm{mask}}$ 的最小值或最大值,也不总等于其中某一个值。缺少的是在整个局部补等价类上比较掩码秩族的手段:或者找到两个态与着色,其全部图形式的掩码秩族集合相同而 $S_n$ 不同(定理 7.3 只比较了各取一个图形式的掩码秩族),或者给出用该集合表示 $\sum_{t\ne0}\rho_t$ 的公式。

## 9. 来源、文献状态与核验边界

**文献表态(第 3.7 条,三值之一)。**

| 来源 | 精确范围与使用边界 |
| --- | --- |
| 卷《Stabilizer multi-entropy at every odd replica index》(本仓理论卷) | 本卷的前提:约定 2.1–2.5、定理 3.1、注 3.2、命题 4.1、推论 4.2(含 $\mathtt q\le3$ 的情形)、第 5 节的 $S_n^{\mathrm{mask}}$ 与命题 5.1 的计数,按该卷第 8 节的表态引用;本卷不重述其证明。注 6.1 与开放问题 6.3、6.4 是本卷第 3–8 章所回应的问题。 |
| S. Akella, N. Iizuka, A. Miyata, *Genuine Multi-Entropy in the Toric Code*, arXiv:2607.06050v1, Appendix A | `literature-attested`:经母卷约定 2.2 引用的复本定义与归一化。本卷不从中取用其他结论。 |
| M. Van den Nest, J. Dehaene, B. De Moor, *Graphical description of the action of local Clifford transformations on graph states*, Phys. Rev. A 69 (2004) 022316, arXiv:quant-ph/0308151 | `literature-attested`:局部补可由局部 Clifford 酉阵实现,且两个图态局部 Clifford 等价当且仅当两图局部补等价。定位(按 arXiv:quant-ph/0308151v2 的 TeX 源;期刊版编号未逐一核对):局部补的局部 Clifford 实现是 §IV 定理 2;「当且仅当」是 §IV 定理 3,该文以「局部补生成图态邻接阵在局部 Clifford 群作用下的整个轨道」的形式陈述,并在定理 3 之前的正文中写成两图态局部 Clifford 等价当且仅当两图经有限次局部补互相得到。前一半在定理 7.2 证明第一步中重新验证并作为先例标注;后一半(「仅当」方向)只在命题 8.3 的证明中作为引用步骤使用,本卷未重证。经母卷约定 2.3 引用的「每个稳定子态都有图形式」也出自该文(§III 定理 1)。 |
| M. Hein, J. Eisert, H. J. Briegel, *Multiparty entanglement in graph states*, Phys. Rev. A 69 (2004) 062311, arXiv:quant-ph/0307130 | `literature-attested`:图态由 $K_w=X_w\prod_{u\in N(w)}Z_u$ 稳定且被其生成的稳定子群唯一确定(约定 2.5;该文 §II.B);图态上的局部补规则(该文 §III.E 命题 8「LU-equivalence」)。节号与命题号按 arXiv:quant-ph/0307130 v6 与 v7 的 TeX 源,两版一致,与母卷第 8 节所引的同文命题 3 编号体系相同;期刊版编号未逐一核对。本卷只把这些作为引用步骤。 |
| D. M. Cvetković, I. M. Gutman, *The algebraic multiplicity of the number zero in the spectrum of a bipartite graph*, Matematički Vesnik 9(24) (1972) 141–150;J. H. Bevis, G. S. Domke, V. A. Miller, *Ranks of trees and grid graphs*, J. Combin. Math. Combin. Comput. 18 (1995) 109–119 | `literature-attested`,只作中间步骤:树(从而森林)的邻接阵的秩等于其匹配数的两倍,以实数域上的形式陈述。出处按 arXiv:1806.02399 引言对这两篇文献的引用核对,原文未逐页核对;$\mathbb F_2$ 上的单独陈述的文献定位未核,本卷在特征 $2$ 下的证明见定理 3.3,不主张该无权特例的新颖性。以此为先例的无权特例:定理 3.3 与推论 3.4 中图为森林时的 $\operatorname{rank}_{\mathbb F_2}=2\nu$,命题 4.1(i) 边权全为 $1$ 时路的秩 $2\lfloor m/2\rfloor$。命题 4.1(ii)(iii) 边权全为 $1$ 时给出的圈 $C_L$ 的邻接阵在 $\mathbb F_2$ 上的秩($L$ 为奇数时 $L-1$,为偶数时 $L-2$)是循环矩阵的经典计算,本卷按已知事实作中间步骤使用,不主张其新颖性;其文献定位未核。 |
| S. Akella, A. Gadde, J. Pandey, arXiv:2601.16258v1;N. Iizuka, S. Lin, arXiv:2511.00905v2;B. Czech, Y. Feng, X. Wu, M. Xie, arXiv:2606.06582v2;S. Akella, arXiv:2510.08520v1 | 母卷第 8 节记录的相邻文献;按该节的范围记录,它们不含奇数 $n\ge5$、$\mathtt q\ge4$ 时 $\rho_t$ 与 $r(\pi_t)$ 的比较。母卷第 8 节记录的 Iizuka–Lin Eq. (64) 把三方掩码秩与可提取 GHZ 数联系起来;定理 7.1(a) 的三块情形与之相容,本卷的证明不依赖该式。 |
| — | `repo-derived`:定理 3.1、推论 3.2、定理 3.3 与命题 4.1(带权的特征 $2$ 形式;其无权经典特例见 Cvetković、Gutman 与 Bevis、Domke、Miller 一行)、命题 4.2、定理 6.1、定理 7.1(a)(c)、命题 8.1、命题 8.2;定理 7.1(b) 是母卷注 3.2 的重述,不计为本卷的新内容。其中定理 3.1(c)(d) 是带权图上用顶点缩放消去边权的判据,属于增益图平衡性一类的论证,本卷对其在 $\rho_t$ 上的应用表态,不主张该类判据本身的优先权;定理 7.1(a) 的二块情形也可由 Hein、Eisert、Briegel 的 Schmidt 秩公式(母卷注 3.3 所引)得到。作为行内步骤使用的标准事实:Pfaffian 的完美匹配展开、Cayley 恒等式、交错阵的秩等于非奇异主子阵的最大阶、两个完美匹配的对称差是偶圈之并、$\mathbb F_2$ 上 $J_k-I_k$ 的秩、有限域中平方映射的双射性、Pauli 矩阵的共轭关系。 |
| — | `suspected-novel`:推论 3.4、定理 5.1、推论 5.2、定理 6.2、定理 7.2、定理 7.3、命题 8.3。检索范围:母卷第 8 节对上述五篇 arXiv 来源 TeX 源文件的范围记录;本卷撰写时的网络检索,检索词组合「multi-entropy」「Rényi multi-entropy」与「stabilizer」「graph state」「rank formula」「local complementation」「four parties」「odd replica index」;arXiv:2608.29627 的摘要页(该文研究 Abelian Chern–Simons 理论的链态,不涉及稳定子态的掩码秩)。检索结果中没有奇数 $n\ge5$、$\mathtt q\ge4$ 时掩码秩修正和的闭式、符号或图形式依赖的陈述;这不确立检索范围之外的优先权。 |

**依赖次序。** 定理 3.1 用约定 2.2–2.4;推论 3.2 用定理 3.1 与母卷命题 4.1 的证明;定理 3.3 用约定 2.4;推论 3.4 用定理 3.1(a) 与定理 3.3;命题 4.1 用定理 3.3 的证明;命题 4.2 用约定 2.4;定理 5.1 用定理 3.1、推论 3.2、定理 3.3、推论 3.4、命题 4.1、命题 4.2;推论 5.2 用定理 5.1 与 (2.1)(2.2);定理 6.1 用约定 2.2、2.4 与命题 4.2;定理 6.2 用约定 2.2;定理 7.1 用母卷定理 3.1、注 3.2、推论 4.2;定理 7.2 用约定 2.5、推论 3.4、定理 5.1、命题 4.2、定理 7.1;定理 7.3 用定理 3.3、命题 4.2、定理 5.1、定理 7.1(a) 证明的第一句与母卷第 5 节;命题 8.1 用定理 3.3;命题 8.2 用约定 2.2;命题 8.3 用定理 7.1(b)、(2.1)、Van den Nest–Dehaene–De Moor 的局部补定理与第 10 节的有限计算。

**核验边界。** 第 10 节代码以精确有限域运算核验以下有限情形:(4.2) 与定理 5.1(d) 在 $n\in\{5,7,9\}$、$\mathtt q=4$ 时对 $\{1,2,3,4\}$ 上全部 $64$ 个图与全部字符逐字符成立,即代码断言每个字符的 $\rho_t-r(\pi_t)$ 等于 (4.2) 给出的值(四值字符)或 $0$(其余字符),其中 $\lambda$ 只取 $\zeta$ 的幂;命题 4.2 的两张秩表本身与任意两两不同的 $\lambda$ 未被代码断言;定理 7.3 的两个 $32$ 比特图态在 $\mathtt q\in\{4,5\}$ 时全部分割上的掩码秩相同,且 $n=5$、$\mathtt q=4$ 时 $\sum_t\rho_t$ 之差为 $2D=48$;定理 7.2 的两条局部补链、局部补的酉实现(对全部 $64$ 个四顶点图各取一个顶点,以高斯整数精确比较态矢量的共线性)、$\{1,2,3,4\}$ 上每个图的局部补等价类都含不含偶圈的图,以及 $n\in\{5,7\}$、$\mathtt q=4$ 时四个图形式的修正和;命题 8.1、8.2 的单字符断言;定理 6.2 在 $(n,p)\in\{(5,4),(5,5),(5,6),(7,4),(7,5)\}$、$\mathtt q=p$ 时的逐字符秩与 (6.1);定理 5.1(c) 在六圈、$n=5$、$\mathtt q=6$ 时的逐项值域与正性;命题 8.3 的全部有限断言;以及 $n=5$、$N\in\{4,5\}$、$\mathtt q=N$、每个量子比特独占一方时每个局部补等价类都含修正和为零的图($N\le3$ 的情形由推论 3.2 直接得到,不在代码中)。这些有限运行不证明任何全称陈述;除命题 8.3 外,本卷各条目的成立依据是正文证明,代码只是独立复核。命题 8.3 的有限部分以代码为证明,其余部分依赖所引的局部补定理。代码不核验母卷的定理 3.1 本身,也不核验偶数 $n$。

## 10. 有限精确核验

```python
import itertools

def order2(n):
    m, x = 1, 2 % n
    while x != 1:
        x, m = x * 2 % n, m + 1
    return m

class Field:
    def __init__(self, n):
        m = order2(n)
        self.n, self.m, self.size = n, m, 1 << m
        for poly in range(self.size + 1, 2 * self.size, 2):
            exp, x = [], 1
            for _ in range(self.size - 1):
                exp.append(x)
                x <<= 1
                if x >> m & 1:
                    x ^= poly
            if x == 1 and len(set(exp)) == self.size - 1:
                break
        self.exp = exp + exp
        self.log = {v: i for i, v in enumerate(exp)}
        self.zeta = exp[(self.size - 1) // n]

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        return self.exp[(self.size - 1 - self.log[a]) % (self.size - 1)]

    def power(self, a, e):
        return self.exp[self.log[a] * e % (self.size - 1)]

    def rank(self, rows):
        rows = [r[:] for r in rows]
        rk = 0
        for c in range(len(rows[0]) if rows else 0):
            piv = next((i for i in range(rk, len(rows)) if rows[i][c]), None)
            if piv is None:
                continue
            rows[rk], rows[piv] = rows[piv], rows[rk]
            iv = self.inv(rows[rk][c])
            rows[rk] = [self.mul(iv, x) for x in rows[rk]]
            for i in range(len(rows)):
                if i != rk and rows[i][c]:
                    f = rows[i][c]
                    rows[i] = [x ^ self.mul(f, y) for x, y in zip(rows[i], rows[rk])]
            rk += 1
        return rk

def rank2(rows):
    vecs = [sum(b << j for j, b in enumerate(r)) for r in rows]
    rk = 0
    for c in range(len(rows)):
        piv = next((i for i in range(rk, len(vecs)) if vecs[i] >> c & 1), None)
        if piv is None:
            continue
        vecs[rk], vecs[piv] = vecs[piv], vecs[rk]
        for i in range(len(vecs)):
            if i != rk and vecs[i] >> c & 1:
                vecs[i] ^= vecs[rk]
        rk += 1
    return rk

def adjacency(N, edges):
    A = [[0] * N for _ in range(N)]
    for a, b in edges:
        A[a][b] = A[b][a] = 1
    return A

def characters(n, q):
    return itertools.product(range(n), repeat=q - 1)

def fvalue(t, q, c):
    return t[c - 1] if c < q else 0

def rho_and_r(F, A, col, t, q):
    N = len(A)
    lam = [F.exp[F.log[F.zeta] * fvalue(t, q, col[u]) % (F.size - 1)] for u in range(N)]
    M = [[(lam[u] ^ lam[v]) if A[u][v] else 0 for v in range(N)] for u in range(N)]
    G = [[A[u][v] if lam[u] != lam[v] else 0 for v in range(N)] for u in range(N)]
    return F.rank(M), rank2(G)

def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p

def masked_rank(A, col, blocks):
    where = {c: i for i, b in enumerate(blocks) for c in b}
    N = len(A)
    return rank2([[A[u][v] if where[col[u]] != where[col[v]] else 0 for v in range(N)] for u in range(N)])

def falling(a, k):
    out = 1
    for i in range(k):
        out *= a - i
    return out

def has_even_cycle(N, edges):
    adj = {u: set() for u in range(N)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    def dfs(path):
        u = path[-1]
        for w in adj[u]:
            if w == path[0] and len(path) >= 4 and len(path) % 2 == 0:
                return True
            if w not in path and dfs(path + [w]):
                return True
        return False
    return any(dfs([s]) for s in range(N))

def local_complement(edges, v):
    nb = sorted({a if b == v else b for a, b in edges if v in (a, b)})
    out = set(edges)
    for a, b in itertools.combinations(nb, 2):
        out ^= {(a, b)}
    return frozenset(out)

def lc_orbit(edges, N):
    seen, stack = {edges}, [edges]
    while stack:
        g = stack.pop()
        for v in range(N):
            h = local_complement(g, v)
            if h not in seen:
                seen.add(h)
                stack.append(h)
    return seen

def E(*pairs):
    return frozenset((min(a, b) - 1, max(a, b) - 1) for a, b in pairs)

FIELDS = {n: Field(n) for n in (5, 7, 9)}
for n, F in FIELDS.items():
    z = F.zeta
    assert F.power(z, n) == 1 and all(F.power(z, d) != 1 for d in range(1, n))

PAIRS4 = list(itertools.combinations(range(4), 2))
MATCHINGS4 = [{(0, 1), (2, 3)}, {(0, 2), (1, 3)}, {(0, 3), (1, 2)}]

# Equation (4.2) character by character and Theorem 5.1(d): all 64 graphs on four qubits in four parties.
for n in (5, 7, 9):
    F, q, col = FIELDS[n], 4, [1, 2, 3, 4]
    D = (n - 1) * (n - 2) * (n - 3) * n ** (q - 4)
    for mask in range(64):
        edges = {PAIRS4[i] for i in range(6) if mask >> i & 1}
        p = sum(m <= edges for m in MATCHINGS4)
        expect = {2: 2, 3: -2}.get(p, 0)
        total = 0
        for t in characters(n, q):
            rho, r = rho_and_r(F, adjacency(4, edges), col, t, q)
            vals = {fvalue(t, q, c) for c in col}
            assert rho - r == (expect if len(vals) == 4 else 0)
            total += rho - r
        assert total == expect * D

# Theorem 7.3: equal masked-rank families, different S_n.
STAR, PFLAT, PSHARP, ZC = E((1, 2), (1, 3), (1, 4)), E((1, 2), (1, 4), (2, 3)), E((1, 2), (1, 3), (2, 4)), E((1, 3), (1, 4), (2, 3), (2, 4))
V = [E((1, 2), (1, 3)), E((1, 2), (1, 4)), E((1, 3), (1, 4)), E((2, 3), (2, 4))]

def disjoint_union(components, isolated_per_party=0):
    edges, col, base = set(), [], 0
    for comp in components:
        edges |= {(a + base, b + base) for a, b in comp}
        col += [1, 2, 3, 4]
        base += 4
    col += [c for c in (1, 2, 3, 4) for _ in range(isolated_per_party)]
    return adjacency(len(col), edges), col

A_adj, A_col = disjoint_union([STAR] * 3 + [PFLAT, PSHARP, ZC], isolated_per_party=2)
B_adj, B_col = disjoint_union([V[0], V[1], V[2], V[3]] * 2)
assert len(A_col) == len(B_col) == 32
for q in (4, 5):
    for blocks in set_partitions(list(range(1, q + 1))):
        if len(blocks) >= 2:
            assert masked_rank(A_adj, A_col, blocks) == masked_rank(B_adj, B_col, blocks)
F, q, n = FIELDS[5], 4, 5
diff_rho = diff_r = 0
for t in characters(n, q):
    ra, ma = rho_and_r(F, A_adj, A_col, t, q)
    rb, mb = rho_and_r(F, B_adj, B_col, t, q)
    diff_rho += ra - rb
    diff_r += ma - mb
assert diff_r == 0 and diff_rho == 2 * (n - 1) * (n - 2) * (n - 3)

# Theorem 7.2: local complementation chains and the local Clifford step.
def gauss_mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

def apply_one(state, N, k, U):
    out = [(0, 0)] * len(state)
    for x, amp in enumerate(state):
        bit = x >> (N - 1 - k) & 1
        for nb in (0, 1):
            c = U[nb][bit]
            if c != (0, 0):
                y = x ^ ((bit ^ nb) << (N - 1 - k))
                prod = gauss_mul(c, amp)
                out[y] = (out[y][0] + prod[0], out[y][1] + prod[1])
    return out

def graph_state(N, edges):
    vec = []
    for x in range(1 << N):
        bits = [x >> (N - 1 - k) & 1 for k in range(N)]
        sign = sum(bits[a] * bits[b] for a, b in edges) % 2
        vec.append((-1, 0) if sign else (1, 0))
    return vec

def parallel(u, w):
    i = next(k for k, a in enumerate(u) if a != (0, 0))
    return all(gauss_mul(u[i], w[j]) == gauss_mul(w[i], u[j]) for j in range(len(u))) and w[i] != (0, 0)

ROOT_X = [[(1, 0), (0, 1)], [(0, 1), (1, 0)]]
PHASE_S = [[(1, 0), (0, 0)], [(0, 0), (0, 1)]]

def lc_by_unitary(N, edges, v):
    state = apply_one(graph_state(N, edges), N, v, ROOT_X)
    for u in sorted({a if b == v else b for a, b in edges if v in (a, b)}):
        state = apply_one(state, N, u, PHASE_S)
    return parallel(state, graph_state(N, local_complement(edges, v)))

K4 = E((1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4))
C4, P4 = E((1, 2), (2, 3), (3, 4), (1, 4)), E((1, 3), (2, 3), (2, 4))
assert local_complement(STAR, 0) == K4 and lc_by_unitary(4, STAR, 0)
g1 = local_complement(C4, 0)
g2 = local_complement(g1, 1)
g3 = local_complement(g2, 2)
assert g3 == P4 and lc_by_unitary(4, C4, 0) and lc_by_unitary(4, g1, 1) and lc_by_unitary(4, g2, 2)
for mask in range(64):
    edges = frozenset(PAIRS4[i] for i in range(6) if mask >> i & 1)
    assert lc_by_unitary(4, edges, mask % 4)
    assert any(not has_even_cycle(4, g) for g in lc_orbit(edges, 4))

def delta(F, N, edges, col, q):
    A = adjacency(N, edges)
    return sum(a - b for a, b in (rho_and_r(F, A, col, t, q) for t in characters(F.n, q)))

for n in (5, 7):
    D = (n - 1) * (n - 2) * (n - 3)
    F = FIELDS[n]
    assert delta(F, 4, STAR, [1, 2, 3, 4], 4) == 0 and delta(F, 4, K4, [1, 2, 3, 4], 4) == -2 * D
    assert delta(F, 4, P4, [1, 2, 3, 4], 4) == 0 and delta(F, 4, C4, [1, 2, 3, 4], 4) == 2 * D

# Proposition 8.1 (bowtie) and Proposition 8.2 (bipartite, n = 5).
F = FIELDS[5]
z = F.zeta
z2, z3 = F.mul(z, z), F.mul(F.mul(z, z), z)
beta_a = F.mul(F.mul(1 ^ z, 1 ^ z2), F.inv(z ^ z2))
beta_b = F.mul(F.mul(1 ^ z, 1 ^ z3), F.inv(z ^ z3))
assert beta_a ^ beta_b == 1
bowtie = adjacency(5, [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)])
assert rho_and_r(F, bowtie, [4, 1, 2, 1, 3], (1, 2, 3), 4) == (4, 4)
bip = adjacency(6, [(0, 3), (0, 4), (0, 5), (1, 3), (1, 5), (2, 3), (2, 4)])
assert rho_and_r(F, bip, [5, 1, 1, 2, 3, 4], (1, 2, 3, 4), 5) == (4, 6)

# Theorem 6.2: complete graphs K_p with one qubit in each party.
def stirling2(p, k):
    if p == k:
        return 1
    if k == 0 or k > p:
        return 0
    return k * stirling2(p - 1, k) + stirling2(p - 1, k - 1)

for n, p in ((5, 4), (5, 5), (5, 6), (7, 4), (7, 5)):
    F, q = FIELDS[n], p
    A = adjacency(p, list(itertools.combinations(range(p), 2)))
    col = list(range(1, p + 1))
    total = 0
    for t in characters(n, q):
        k = len({fvalue(t, q, c) for c in col})
        rho, r = rho_and_r(F, A, col, t, q)
        assert rho == (2 if k >= 2 else 0) and r == 2 * (k // 2)
        total += rho - r
    formula = -2 * sum(stirling2(p, k) * falling(n - 1, k - 1) * (k // 2 - 1) for k in range(4, min(p, n) + 1))
    assert total == formula < 0

# Theorem 5.1(c): the six-cycle in six parties, n = 5.
F, q = FIELDS[5], 6
cyc = adjacency(6, [(i, (i + 1) % 6) for i in range(6)])
terms = [a - b for a, b in (rho_and_r(F, cyc, [1, 2, 3, 4, 5, 6], t, q) for t in characters(5, q))]
assert set(terms) <= {0, 2} and sum(terms) > 0

# Proposition 8.3: a six-qubit orbit without a zero-correction graph form, n = 5 and n = 7.
def masked_total(N, edges, n):
    A = adjacency(N, edges)
    col = list(range(1, N + 1))
    return sum(falling(n - 1, len(b) - 1) * masked_rank(A, col, b)
               for b in set_partitions(list(range(1, N + 1))) if len(b) >= 2)

N = 6
G0 = E((1, 3), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5))
orbit = sorted(lc_orbit(G0, N), key=sorted)
assert len(orbit) == 40 and all(has_even_cycle(N, g) for g in orbit)
col = list(range(1, N + 1))
EXPECTED = {5: (12328, [-1296, -912, -864, 48]), 7: (66876, [-10320, -9840, -1440, 240])}
for n, (rho_expected, delta_expected) in EXPECTED.items():
    F = FIELDS[n]
    for g in orbit[:3] + [G0]:
        assert sum(rho_and_r(F, adjacency(N, g), col, t, N)[0] for t in characters(n, N)) == rho_expected
    assert sorted({rho_expected - masked_total(N, g, n) for g in orbit}) == delta_expected

# N in {4, 5}, q = N, one qubit per party, n = 5: every orbit contains a zero-correction form.
for N in (4, 5):
    pairs = list(itertools.combinations(range(N), 2))
    seen = set()
    for mask in range(1 << len(pairs)):
        g = frozenset(pairs[i] for i in range(len(pairs)) if mask >> i & 1)
        if g in seen:
            continue
        orb = lc_orbit(g, N)
        seen |= orb
        col = list(range(1, N + 1))
        rho_total = sum(rho_and_r(FIELDS[5], adjacency(N, g), col, t, N)[0] for t in characters(5, N))
        assert any(rho_total == masked_total(N, h, 5) for h in orb)

print("ALL_FINITE_CHECKS_PASSED")
```

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）

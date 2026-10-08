# FIB 合法边负载的增长常数：对偶、Cartesian 可加性与硬核测度界

> **本卷的机器契约（逐条可查，落地后不改）。** 消化器 `generic-v1`；地址只由本文件字节计算，不查词表。本卷研究合法词图上的平方负载最小最大值，正文按定义、约定、定理与证明排列。卷首恒定区与既有各章一经合入即不再改动；勘误、改判与增补一律写在文末追加锚之后的新章，并点名被改判条目的编号。

## 1. 定位、状态与产地

**本卷的定位。** 本卷是 trureturing 的参考输入，不是真源。它接在 [FIB 合法边误差分配卷][Minimax]（下称母卷）之后：母卷把完整合法词域上的 minimax 首项系数归结为有限图量 $\kappa_n$（母卷定义 1.5、式（1.2）、定理 2.1(B)），并在开放问题 5.4 中留下两个缺口：没有 $\kappa_n$ 随 $n$ 增长的一致估计；严格不等式 $\kappa_n>C_n$ 只是逐个 $n$ 的定性结论，没有给出两者之差随 $n$ 的增长。本卷把 $\kappa$ 当作任意有限图上的组合优化量来研究，给出对偶式、Cartesian 积可加性、合法词图上的近可加性与增长常数 $c_\star=\lim_n\kappa_n/n$ 的存在性，并用显式分配和硬核测度把 $c_\star$ 夹在两个显式常数之间。全卷只用图、测度与分配的语言，不引入母卷的物理来源或服务解释；与母卷量子模型的联系只在第 8 章经母卷定理 2.1 的已证结论传递。任何形式化工件不得反向绑定到本卷的章节号或定理号。

**证明状态。** 本卷给出 ZFC 内的普通数学证明，外加第 11 章一个固定输入的有限精确核验。本卷未经 Lean kernel 验证，也不声称任何内核核验状态；任何条目是否被形式化，以冻结账本为准，不以本卷自述为准。命题 6.3 的证明，以及定理 7.3 中 $g(r_\star)$ 的八位小数区间（连同由它写出的定理 8.1(ii)(iii) 的小数界），依赖第 11 章代码块的精确有理数核验；其余结论，包括 $c_\star\ge1800/12559$ 与全部结构定理，其证明不依赖该代码块。

**产地（三项与恢复指针）。** ① skill 上下文：`consensus-rnd:sshx`。② 载体与分工：本卷正文由实施席 Claude Code subagent（Opus 5.5）产出；选题由六席思考面板（Opus 5.5 三席、Fable 5.1 三席）收敛；评审三席为 Claude Code subagent（Opus 5.5 与 Fable 5.1 混合）。全部席位属同一载体族，不冒充跨厂商的模型多样性。③ 混合方式：三席并发盲评。创建会话 ID 为 `02860e2e-a1ec-4fd1-b72b-435e73e0a63d`，恢复命令为 `claude --resume 02860e2e-a1ec-4fd1-b72b-435e73e0a63d`；会话 ID 只是宿主本地的恢复指针，本卷结论不依赖恢复会话才能读懂。

**读法。** 第 2 章固定记号。第 3–4 章是一般有限图上的结构理论；第 5–7 章把它用于合法词图 $\Gamma_n$；第 8 章汇总对母卷量的推论；第 9 章写反例、不能推广的边界与开放问题；第 10 章是文献表态与核验边界；第 11 章是唯一代码块。基线叙述中的「本卷」指写下基线的那一次工作，后续增补不改写它。

## 2. 记号与约定

**约定 2.1（有限图与分配）。** 图 $G=(V,E)$ 恒指顶点集非空的有限简单无向图。$b\sim c$ 表示 $\{b,c\}\in E$，$d_b$ 为顶点 $b$ 的度数，$\Delta(G)=\max_bd_b$。一个分配 $a$ 对每个有序邻接对 $(b,c)$ 给出实数 $a_{c\leftarrow b}$，满足

$$
0\le a_{c\leftarrow b}\le1,\qquad a_{c\leftarrow b}+a_{b\leftarrow c}=1\qquad(b\sim c).
$$

全体分配记为 $\mathcal A(G)$。对每条边任选一个方向后，$\mathcal A(G)$ 与 $[0,1]^{E}$ 线性同胚，故它是有限维欧氏空间中的非空紧凸集。顶点负载与负载最小最大值为

$$
L_b^G(a)=\sum_{c\sim b}a_{c\leftarrow b}^{2},\qquad
\kappa(G)=\min_{a\in\mathcal A(G)}\max_{b\in V}L_b^G(a).
\tag{2.1}
$$

每个 $L_b^G$ 是连续凸函数，最大值连续，所以最小值在紧集上取到。无边图的唯一分配是空族，此时 $\kappa(G)=0$。$\kappa$ 是图同构不变量。另记 $C(G)=|E|/(2|V|)$。

**约定 2.2（调和项与对偶函数）。** 对 $s,t\ge0$ 置

$$
h(s,t)=\begin{cases}\dfrac{st}{s+t},&s+t>0,\\ 0,&s=t=0.\end{cases}
$$

$\mathcal P(V)$ 为 $V$ 上全体概率向量 $\mu=(\mu_b)_{b\in V}$（$\mu_b\ge0$，$\sum_b\mu_b=1$）。对偶函数为

$$
\Phi_G(\mu)=\sum_{\{b,c\}\in E}h(\mu_b,\mu_c),\qquad \mu\in[0,\infty)^V.
\tag{2.2}
$$

**约定 2.3（Cartesian 积与不交并）。** $G\mathbin{\square}H$ 的顶点集为 $V(G)\times V(H)$，$(g,x)\sim(g',x')$ 当且仅当 $g=g'$ 且 $x\sim x'$，或 $x=x'$ 且 $g\sim g'$。前一类边称 $H$ 型边，后一类称 $G$ 型边；每条边恰属其一。$G\sqcup H$ 为不交并。$K_2$ 为单边图，$Q_d=K_2^{\square d}$ 为 $d$ 维方体（$d\ge1$），$K_{1,m}$ 为有 $m$ 片叶的星图。

**约定 2.4（合法词与合法词图）。** 对整数 $n\ge0$，$B_n$ 为长 $n$、无两个相邻 $1$ 的二进制词全体，$B_0$ 只含空词。以 $B_n$ 为顶点、Hamming 距离为一时连边，得到图 $\Gamma_n$；$\Gamma_0$ 是单点图，$\Gamma_1=K_2$，$\Gamma_2=K_{1,2}$。置

$$
\kappa_n=\kappa(\Gamma_n),\qquad C_n=C(\Gamma_n)\quad(n\ge1),\qquad \kappa_0=0.
$$

当 $n=3N$ 时，$B_n$、$\Gamma_n$ 即母卷定义 1.2、1.4 中的完整合法词集与完整合法词图，本卷的 $\kappa_n$ 即母卷式（1.2）的量，$C_n$ 即母卷式（1.1）的量；约定 2.1 的分配与负载即母卷定义 1.5 对一般图的同字推广。本卷对一切 $n\ge0$ 使用这些记号，母卷中与物理来源有关的结论只对 $n=3N$ 引用。

**约定 2.5（位置记号）。** 对 $b\in B_n$，$b_i$ 为第 $i$ 位，并约定 $b_0=b_{n+1}=0$。$k(b)$ 为 $b$ 中 $1$ 的个数。位置 $i$ 称为 $b$ 的可翻转零，若 $b_{i-1}=b_i=b_{i+1}=0$；可翻转零的个数记为 $u(b)$。$b+e_i$ 表示把第 $i$ 位由 $0$ 改为 $1$ 所得的词，$b-e_i$ 表示把第 $i$ 位由 $1$ 改为 $0$ 所得的词。Fibonacci 数取 $F_0=0$，$F_1=1$，$F_{j+2}=F_{j+1}+F_j$；$\varphi=(1+\sqrt5)/2$。

**约定 2.6（硬核测度与参数化）。** 对 $\lambda>0$，置

$$
Z_n(\lambda)=\sum_{b\in B_n}\lambda^{k(b)},\qquad
\mu^{(n)}_\lambda(b)=\frac{\lambda^{k(b)}}{Z_n(\lambda)},
$$

$\mathbb E^{(n)}_\lambda$ 为关于 $\mu^{(n)}_\lambda$ 的期望。每个 $\lambda>0$ 唯一对应 $r=\bigl(1+\sqrt{1+4\lambda}\bigr)/2>1$，反之 $\lambda=r(r-1)$；记 $s=1-r$、$\vartheta=(r-1)/r\in(0,1)$，并令

$$
g(r)=\frac{r-1}{(r^2-r+1)(2r-1)},\qquad
p(r)=4r^3-9r^2+6r-2\qquad(r>1).
\tag{2.3}
$$

## 3. 对偶式与最优分配的结构

**引理 3.1（调和项的变分式）。** 对一切 $s,t\ge0$，下列结论成立。

(i) $\min_{\alpha\in[0,1]}\bigl[s\alpha^2+t(1-\alpha)^2\bigr]=h(s,t)$；若 $s+t>0$，最小点唯一，等于 $\alpha=t/(s+t)$。

(ii) $0\le h(s,t)\le\min\{s,t\}$；$h$ 在 $[0,\infty)^2$ 上连续且凹；对每个 $\gamma\ge0$ 有 $h(\gamma s,\gamma t)=\gamma\,h(s,t)$。

**证明。** 若 $s+t>0$，展开可得恒等式

$$
s\alpha^2+t(1-\alpha)^2=(s+t)\left(\alpha-\frac{t}{s+t}\right)^2+\frac{st}{s+t}\qquad(\alpha\in\mathbb R).
\tag{3.1}
$$

右边第一项非负，且仅在 $\alpha=t/(s+t)\in[0,1]$ 处为零，故 (i) 成立。若 $s=t=0$，目标恒为零，等于 $h(0,0)$。

(ii) 取 $\alpha=0$ 与 $\alpha=1$ 得目标值 $t$ 与 $s$，故 $h\le\min\{s,t\}$；非负性显然。由 (i)，$h$ 是一族关于 $(s,t)$ 的线性函数 $(s,t)\mapsto s\alpha^2+t(1-\alpha)^2$（$\alpha\in[0,1]$）的逐点最小值，故凹。在 $\{s+t>0\}$ 上 $h$ 是连续函数之商；在原点，$0\le h(s,t)\le\min\{s,t\}$ 给出连续性。$\gamma=0$ 时两边都为零；$\gamma>0$ 时直接代入定义得齐次性。

**定理 3.2（对偶式与鞍点结构）。** 对每个有限图 $G=(V,E)$，$\Phi_G$ 在 $[0,\infty)^V$ 上连续且凹，并且

$$
\kappa(G)=\max_{\mu\in\mathcal P(V)}\Phi_G(\mu),
\tag{3.2}
$$

右边最大值取到。进一步，对式（2.1）的任一最小点 $a^\star$ 与式（3.2）的任一最大点 $\mu^\star$：

(i) $\sum_b\mu^\star_bL_b^G(a^\star)=\kappa(G)$，且凡 $\mu^\star_b>0$ 的顶点都有 $L_b^G(a^\star)=\kappa(G)$；

(ii) 凡 $\mu^\star_b+\mu^\star_c>0$ 的边 $\{b,c\}$ 都有 $a^\star_{c\leftarrow b}=\mu^\star_c/(\mu^\star_b+\mu^\star_c)$；

(iii) 对任意 $a\in\mathcal A(G)$ 与 $\mu\in\mathcal P(V)$ 有 $\Phi_G(\mu)\le\kappa(G)\le\max_bL_b^G(a)$。

**证明。** 定义 $f:\mathcal A(G)\times\mathcal P(V)\to\mathbb R$，

$$
f(a,\mu)=\sum_b\mu_bL_b^G(a)
=\sum_{\{b,c\}\in E}\bigl[\mu_b\,a_{c\leftarrow b}^2+\mu_c\,a_{b\leftarrow c}^2\bigr].
\tag{3.3}
$$

第二个等号把每条边的两个有向项归到这条边上。固定 $\mu$，(3.3) 对各边的变量分离，每条边的项是 $\mu_b\alpha^2+\mu_c(1-\alpha)^2$，$\alpha=a_{c\leftarrow b}\in[0,1]$。由引理 3.1(i)，

$$
\min_{a\in\mathcal A(G)}f(a,\mu)=\Phi_G(\mu)\qquad(\mu\in\mathcal P(V)).
\tag{3.4}
$$

连续性与凹性由引理 3.1(ii) 逐项得到（有限个连续凹函数之和）。

弱对偶：对任意 $a,\mu$，$\Phi_G(\mu)\le f(a,\mu)\le\max_bL_b^G(a)$，最后一步因为 $f(a,\cdot)$ 是负载的凸组合。对 $a$ 取最小、对 $\mu$ 取上确界，得 $\sup_\mu\Phi_G(\mu)\le\kappa(G)$，这同时给出 (iii)。

强对偶：$\mathcal A(G)$ 与 $\mathcal P(V)$ 都是有限维欧氏空间中的非空紧凸集；$f$ 在乘积上连续；对每个固定 $\mu$，$f(\cdot,\mu)$ 是凸二次函数的非负组合，因而凸；对每个固定 $a$，$f(a,\cdot)$ 线性，因而凹。这正是 Sion minimax 定理的全部前提（文献步骤，见第 10 章），故

$$
\inf_{a}\sup_{\mu}f(a,\mu)=\sup_{\mu}\inf_{a}f(a,\mu).
$$

左边内层是线性函数在单纯形上的最大值，在某个顶点 $\mu=\mathbf 1_{\{b\}}$ 处取到，等于 $\max_bL_b^G(a)$，于是左边是 $\kappa(G)$。右边由 (3.4) 等于 $\sup_\mu\Phi_G(\mu)$；$\Phi_G$ 连续而 $\mathcal P(V)$ 紧，上确界取到。这证明 (3.2)。

鞍点结构：取最小点 $a^\star$ 与最大点 $\mu^\star$，则

$$
\kappa(G)=\max_bL_b^G(a^\star)\ge f(a^\star,\mu^\star)\ge\min_af(a,\mu^\star)=\Phi_G(\mu^\star)=\kappa(G),
$$

所以全部取等。由 $\sum_b\mu^\star_b\bigl(\kappa(G)-L_b^G(a^\star)\bigr)=0$ 且各项非负，凡 $\mu^\star_b>0$ 都有 $L_b^G(a^\star)=\kappa(G)$，得 (i)。又 $f(a^\star,\mu^\star)=\min_af(a,\mu^\star)$；由于 (3.3) 按边分离，而每条边的项不小于其最小值，总和取等迫使每条边的项都取到最小值。对 $\mu^\star_b+\mu^\star_c>0$ 的边，引理 3.1(i) 的唯一性给出 (ii)。

**推论 3.3（对称的最优解）。** 设 $\mathcal G$ 是 $G$ 的一个自同构群。则存在 $\mathcal G$ 不变的最大点 $\mu^\star$（$\mu^\star_{\sigma b}=\mu^\star_b$），也存在 $\mathcal G$ 不变的最小点 $a^\star$（$a^\star_{\sigma c\leftarrow\sigma b}=a^\star_{c\leftarrow b}$），$\sigma\in\mathcal G$。特别地，对每个 $n\ge1$，词反转 $\rho(b)_i=b_{n+1-i}$ 是 $\Gamma_n$ 的自同构，故 $\Gamma_n$ 有反转不变的最大测度与反转不变的最优分配。

**证明。** 有限图的自同构群有限，故 $\mathcal G$ 有限。对 $\sigma\in\mathcal G$ 置 $(\sigma\mu)_b=\mu_{\sigma^{-1}b}$。$\sigma$ 置换边集，故 $\Phi_G(\sigma\mu)=\Phi_G(\mu)$。若 $\mu^\star$ 是最大点，平均 $\bar\mu=|\mathcal G|^{-1}\sum_{\sigma}\sigma\mu^\star$ 属于 $\mathcal P(V)$ 且 $\mathcal G$ 不变；由 $\Phi_G$ 的凹性，$\Phi_G(\bar\mu)\ge|\mathcal G|^{-1}\sum_\sigma\Phi_G(\sigma\mu^\star)=\kappa(G)$，所以 $\bar\mu$ 也是最大点。

对分配置 $(\sigma a)_{c\leftarrow b}=a_{\sigma^{-1}c\leftarrow\sigma^{-1}b}$，它仍属于 $\mathcal A(G)$，且 $L_b^G(\sigma a)=L_{\sigma^{-1}b}^G(a)$。若 $a^\star$ 是最小点，$\bar a=|\mathcal G|^{-1}\sum_\sigma\sigma a^\star$ 是可行分配的凸组合，可行且 $\mathcal G$ 不变；由 $L_b^G$ 的凸性，$L_b^G(\bar a)\le|\mathcal G|^{-1}\sum_\sigma L_{\sigma^{-1}b}^G(a^\star)\le\kappa(G)$，故 $\bar a$ 是最小点。

最后，「无两个相邻 $1$」在反转下不变，两词的 Hamming 距离也在反转下不变，故 $\rho$ 是 $B_n$ 上保持邻接与非邻接的双射。

## 4. 一般图的结构律

**定理 4.1（子图单调、边并次可加与不交并）。** 设 $G,H$ 为有限图。

(i) 若 $H$ 同构于 $G$ 的一个子图（顶点子集连同其间的部分边），则 $\kappa(H)\le\kappa(G)$。

(ii) 若 $E_1\cap E_2=\varnothing$，则 $\kappa\bigl((V,E_1\cup E_2)\bigr)\le\kappa\bigl((V,E_1)\bigr)+\kappa\bigl((V,E_2)\bigr)$。

(iii) $\kappa(G\sqcup H)=\max\{\kappa(G),\kappa(H)\}$。

**证明。** (i) 由同构不变性，可设 $V(H)\subseteq V(G)$、$E(H)\subseteq E(G)$。取 $\Phi_H$ 的最大点 $\mu$，补零得 $\tilde\mu\in\mathcal P(V(G))$。$h\ge0$ 且在 $E(H)$ 的边上两者取值相同，故 $\Phi_G(\tilde\mu)\ge\Phi_H(\mu)=\kappa(H)$；由定理 3.2(iii)，$\kappa(G)\ge\Phi_G(\tilde\mu)$。

(ii) 取 $(V,E_1)$ 与 $(V,E_2)$ 的最小点 $a^1,a^2$。因边集不交，在 $E_1$ 上用 $a^1$、在 $E_2$ 上用 $a^2$ 得到 $(V,E_1\cup E_2)$ 的可行分配，其负载为 $L_b^{(V,E_1)}(a^1)+L_b^{(V,E_2)}(a^2)\le\kappa((V,E_1))+\kappa((V,E_2))$。

(iii) 由 (i)，左边不小于右边。反向，把 $G$ 与 $H$ 的最小点拼成 $G\sqcup H$ 的分配；两部分之间无边，每个顶点的负载等于它在所属部分中的负载，故最大负载不超过 $\max\{\kappa(G),\kappa(H)\}$。

**定理 4.2（Cartesian 积可加）。** 对任意有限图 $G,H$，

$$
\kappa(G\mathbin{\square}H)=\kappa(G)+\kappa(H).
\tag{4.1}
$$

**证明。** 上界：$G\mathbin{\square}H$ 的边集是 $G$ 型边集 $E_G$ 与 $H$ 型边集 $E_H$ 的不交并，二者共用顶点集 $V(G)\times V(H)$。图 $(V(G)\times V(H),E_G)$ 是 $|V(H)|$ 个 $G$ 的副本之不交并，由定理 4.1(iii) 其 $\kappa$ 等于 $\kappa(G)$；同理 $(V(G)\times V(H),E_H)$ 的 $\kappa$ 等于 $\kappa(H)$。定理 4.1(ii) 给出 $\kappa(G\mathbin{\square}H)\le\kappa(G)+\kappa(H)$。

下界：取 $\Phi_G$ 的最大点 $\mu$ 与 $\Phi_H$ 的最大点 $\nu$，令 $\pi_{(g,x)}=\mu_g\nu_x$，则 $\pi\in\mathcal P(V(G)\times V(H))$。按边的两种类型分开求和，并用引理 3.1(ii) 的齐次性：

$$
\begin{aligned}
\Phi_{G\square H}(\pi)
&=\sum_{x\in V(H)}\sum_{\{g,g'\}\in E(G)}h(\mu_g\nu_x,\mu_{g'}\nu_x)
+\sum_{g\in V(G)}\sum_{\{x,x'\}\in E(H)}h(\mu_g\nu_x,\mu_g\nu_{x'})\\
&=\sum_{x}\nu_x\,\Phi_G(\mu)+\sum_{g}\mu_g\,\Phi_H(\nu)
=\kappa(G)+\kappa(H).
\end{aligned}
$$

由定理 3.2(iii)，$\kappa(G\mathbin{\square}H)\ge\Phi_{G\square H}(\pi)$。两向合并得 (4.1)。

**推论 4.3（度数两侧界与等号刻画）。** 对每个有限图 $G$：

(i) $C(G)\le\kappa(G)\le\Delta(G)/4$；

(ii) $\kappa(G)=C(G)$ 当且仅当 $G$ 正则；

(iii) $\kappa(G)=\Delta(G)/4$ 当且仅当 $G$ 有一个 $\Delta(G)$ 正则的连通分支；

(iv) $d$ 正则图满足 $\kappa=d/4$；特别地 $\kappa(K_2)=1/4$，$\kappa(Q_d)=d/4$。

**证明。** (i) 均匀测度 $\mu_b=1/|V|$ 给出 $\Phi_G(\mu)=|E|\cdot h(1/|V|,1/|V|)=|E|/(2|V|)$，由定理 3.2(iii) 得下界。全部份额取 $1/2$ 的分配给出 $L_b^G=d_b/4$，得上界。

(ii) 对每个分配，每条边任选一个方向并记该向份额为 $x_e$，由 $x^2+(1-x)^2=\tfrac12+2(x-\tfrac12)^2$ 得

$$
\sum_bL_b^G(a)=\frac{|E|}{2}+2\sum_{e\in E}\Bigl(x_e-\frac12\Bigr)^2.
\tag{4.2}
$$

若 $\kappa(G)=C(G)$，取最小点 $a^\star$，则 $|V|\kappa(G)\ge\sum_bL_b^G(a^\star)\ge|E|/2=|V|C(G)$，故 (4.2) 中每个平方为零，全部份额为 $1/2$，$L_b^G(a^\star)=d_b/4$。于是每个 $d_b/4\le\kappa(G)=|V|^{-1}\sum_cd_c/4$，即每个度数不超过平均度数，所有度数相等。反之，$d$ 正则时 $C(G)=d/4=\Delta(G)/4$，由 (i) 得等号。这一平均负载论证与母卷 §3.1 对 $\Gamma_n$ 的论证相同，此处推广到一般图。

(iii) 若某连通分支 $H$ 是 $\Delta$ 正则的，由 (ii) 与定理 4.1(i)，$\kappa(G)\ge\kappa(H)=\Delta/4$，结合 (i) 得等号。反之，设没有连通分支是 $\Delta$ 正则的，$\Delta=\Delta(G)$。若 $\Delta=0$，每个分支是 $0$ 正则的单点，与假设矛盾，故 $\Delta\ge1$。对每个分支 $D$ 构造分配如下。若 $D$ 中没有度数为 $\Delta$ 的顶点，全部份额取 $1/2$，$D$ 中负载至多 $(\Delta-1)/4$。否则 $D$ 连通且不是 $\Delta$ 正则，含度数小于 $\Delta$ 的顶点；令 $\ell(b)$ 为 $b$ 到 $D$ 中度数小于 $\Delta$ 的顶点集的图距离，它有限，且相邻顶点的 $\ell$ 值至多相差一。取 $\varepsilon_1=1/(16\Delta)$，$\varepsilon_{j+1}=\varepsilon_j/(8\Delta)$。对 $\ell(c)=\ell(b)-1=j-1$ 的边令

$$
a_{c\leftarrow b}=\frac12-\varepsilon_j,\qquad a_{b\leftarrow c}=\frac12+\varepsilon_j,
$$

两端 $\ell$ 值相等的边两向都取 $1/2$。设 $\ell(b)=j\ge1$。$b$ 至少有一个 $\ell$ 值为 $j-1$ 的邻点，每个这样的邻点贡献 $\tfrac14-\varepsilon_j+\varepsilon_j^2\le\tfrac14-\varepsilon_j/2$；$\ell$ 值为 $j+1$ 的邻点至多 $\Delta-1$ 个，每个贡献 $\tfrac14+\varepsilon_{j+1}+\varepsilon_{j+1}^2\le\tfrac14+2\varepsilon_{j+1}$；其余邻点贡献 $\tfrac14$。故

$$
L_b^G(a)\le\frac{d_b}{4}-\frac{\varepsilon_j}{2}+2(\Delta-1)\varepsilon_{j+1}
\le\frac{\Delta}{4}-\frac{\varepsilon_j}{2}+\frac{\varepsilon_j}{4}<\frac{\Delta}{4}.
$$

若 $\ell(b)=0$，则 $d_b\le\Delta-1$，各邻点至多贡献 $\tfrac14+2\varepsilon_1$，所以 $L_b^G(a)\le(\Delta-1)(\tfrac14+2\varepsilon_1)\le\tfrac{\Delta-1}{4}+\tfrac18<\tfrac\Delta4$。所有顶点负载严格小于 $\Delta/4$，顶点有限，故 $\kappa(G)<\Delta/4$。

(iv) $d$ 正则时由 (ii) 得 $\kappa=C(G)=d/4$。$K_2$ 是 $1$ 正则的，$Q_d$ 是 $d$ 正则的；后者也可由定理 4.2 对 $\kappa(K_2)=1/4$ 归纳得到。

**命题 4.4（星图与最大度下界）。** 对 $m\ge1$，

$$
\kappa(K_{1,m})=\frac{m}{(1+\sqrt m)^2},
\tag{4.3}
$$

中心向每片叶分配份额 $1/(1+\sqrt m)$ 的分配与测度 $\mu_{\mathrm{ctr}}=1/(1+\sqrt m)$、每片叶 $\mu=1/(\sqrt m(1+\sqrt m))$ 分别达到最小与最大。因此每个 $\Delta(G)\ge1$ 的图满足 $\kappa(G)\ge\Delta(G)/(1+\sqrt{\Delta(G)})^2$。特别地 $\kappa(K_{1,2})=2(3-2\sqrt2)$。

**证明。** 令 $t=1/(1+\sqrt m)$，则 $1-t=\sqrt m\,t$。所述分配中，中心负载为 $mt^2$，每片叶的负载为 $(1-t)^2=mt^2$，故 $\kappa(K_{1,m})\le mt^2=m/(1+\sqrt m)^2$。所述测度的总质量为 $1/(1+\sqrt m)+m/(\sqrt m(1+\sqrt m))=1$，且中心与一片叶的质量之和为 $1/\sqrt m$、乘积为 $1/(\sqrt m(1+\sqrt m)^2)$，所以每条边的调和项为 $1/(1+\sqrt m)^2$，$\Phi=m/(1+\sqrt m)^2$。由定理 3.2(iii) 得等号。最大度为 $\Delta$ 的顶点与其全部邻点及关联边构成 $K_{1,\Delta}$ 子图，由定理 4.1(i) 得下界。最后 $2/(1+\sqrt2)^2=2/(3+2\sqrt2)=2(3-2\sqrt2)$。

## 5. 合法词图的近可加性与增长常数

**引理 5.1（三个嵌入）。** 对整数 $n,m\ge0$：

(i) 映射 $w\mapsto(w_1\cdots w_n,\;w_{n+1}\cdots w_{n+m})$ 把 $\Gamma_{n+m}$ 同构地映为 $\Gamma_n\mathbin{\square}\Gamma_m$ 的一个子图；

(ii) 映射 $(b,c)\mapsto b\,0\,c$（在 $b$ 与 $c$ 之间插入一个 $0$）把 $\Gamma_n\mathbin{\square}\Gamma_m$ 同构地映为 $\Gamma_{n+m+1}$ 的一个子图；

(iii) $\Gamma_n$ 同构于 $\Gamma_{n+1}$ 的子图。

**证明。** (i) 合法词的前缀与后缀仍无相邻的 $1$，故像落在 $B_n\times B_m$ 中；映射显然单射。若 $w,w'$ 只在一个位置不同，该位置落在前 $n$ 位或后 $m$ 位之一，另一段相同，于是像在 $\Gamma_n\mathbin{\square}\Gamma_m$ 中相邻。

(ii) $b$、$c$ 各自合法，插入的 $0$ 隔开两段，故 $b0c\in B_{n+m+1}$；由固定的中间位与两段长度可读回 $(b,c)$，映射单射。$\Gamma_n\mathbin{\square}\Gamma_m$ 中的一条边改变 $b$ 或 $c$ 中的恰好一位，像也只差一位，故边映为边。

(iii) 是 (ii) 取 $m=0$ 的情形：$b\mapsto b0$。

**定理 5.2（近可加性与增长常数）。** 对一切整数 $n,m\ge0$，

$$
\kappa_{n+m}\le\kappa_n+\kappa_m\le\kappa_{n+m+1}.
\tag{5.1}
$$

极限 $c_\star=\lim_{n\to\infty}\kappa_n/n$ 存在，且

$$
c_\star=\inf_{n\ge1}\frac{\kappa_n}{n}=\sup_{n\ge0}\frac{\kappa_n}{n+1}.
\tag{5.2}
$$

因此对每个 $n\ge0$，

$$
c_\star\,n\le\kappa_n\le c_\star\,(n+1).
\tag{5.3}
$$

**证明。** 由引理 5.1(i)、定理 4.1(i) 与定理 4.2，$\kappa_{n+m}\le\kappa(\Gamma_n\mathbin{\square}\Gamma_m)=\kappa_n+\kappa_m$；由引理 5.1(ii) 与同样两条定理，$\kappa_n+\kappa_m=\kappa(\Gamma_n\mathbin{\square}\Gamma_m)\le\kappa_{n+m+1}$。$n$ 或 $m$ 为零时，$\Gamma_0$ 是单点、$\Gamma_0\mathbin{\square}\Gamma_m\cong\Gamma_m$，上述论证照样成立。这证明 (5.1)。

数列 $(\kappa_n)_{n\ge1}$ 非负且次可加。Fekete 引理（文献步骤，见第 10 章）给出 $\lim_n\kappa_n/n$ 存在并等于 $\inf_{n\ge1}\kappa_n/n$；该下确界在 $[0,\kappa_1]=[0,1/4]$ 中，故有限，记为 $c_\star$。

再令 $\beta_j=\kappa_{j-1}$（$j\ge1$）。由 (5.1) 右半，$\beta_{j+l}=\kappa_{(j-1)+(l-1)+1}\ge\kappa_{j-1}+\kappa_{l-1}=\beta_j+\beta_l$，即 $(\beta_j)$ 超可加。对 $(-\beta_j)$ 用 Fekete 引理，$\lim_j\beta_j/j=\sup_j\beta_j/j$。又 $\beta_j/j=\kappa_{j-1}/j=\bigl(\kappa_{j-1}/(j-1)\bigr)\cdot\bigl((j-1)/j\bigr)\to c_\star$（$j\ge2$）。于是 $\sup_{n\ge0}\kappa_n/(n+1)=c_\star$，得 (5.2)。(5.3) 是 (5.2) 中下确界与上确界的直接改写；$n=0$ 时两边为 $0\le0\le c_\star$。

**推论 5.3（逐步增量与首批数值）。** 对一切 $n\ge0$：

(i) $\kappa_n\le\kappa_{n+1}\le\kappa_n+\tfrac14$ 且 $\kappa_{n+2}\ge\kappa_n+\tfrac14$；

(ii) $\kappa_0=0$，$\kappa_1=\tfrac14$，$\kappa_2=2(3-2\sqrt2)$；

(iii) $\tfrac18\le c_\star\le3-2\sqrt2$；

(iv) 对 $n\ge2$ 有 $\kappa_n<n/4$。

**证明。** (i) 在 (5.1) 中分别取 $m=0$（右半）、$m=1$（左半）、$m=1$（右半），并用 $\kappa_0=0$、$\kappa_1=1/4$。(ii) $\Gamma_0$ 无边；$\Gamma_1=K_2$，由推论 4.3(iv)；$\Gamma_2=K_{1,2}$，由命题 4.4。(iii) 在 (5.3) 中取 $n=1$ 得 $c_\star\ge\kappa_1/2=1/8$，取 $n=2$ 得 $c_\star\le\kappa_2/2=3-2\sqrt2$。(iv) $\Gamma_n$ 连通：每个合法词逐个删去 $1$ 可沿边走到全零词。$n\ge2$ 时全零词度数为 $n=\Delta(\Gamma_n)$，而词 $10\cdots0$ 的度数为 $n-1$，故 $\Gamma_n$ 唯一的连通分支不是 $\Delta$ 正则的，推论 4.3(iii) 给出严格不等式。

推论 5.3(iv) 对 $n=3N$ 弱于母卷式（2.3）的显式界；它表明对一般 $n\ge2$ 的严格不等式已由 $\Gamma_n$ 的不规则性推出。式（5.3）回答了母卷开放问题 5.4 中「随 $n$ 增长的一致估计」的形状部分：$\kappa_n$ 与线性函数 $c_\star n$ 之差恒在 $[0,c_\star]$ 中，未定的只剩常数 $c_\star$ 本身。

## 6. 显式上界

**引理 6.1（可翻转零与 $1$ 的计数）。** 对 $n\ge1$ 与 $b\in B_n$，$\Gamma_n$ 中 $b$ 的度数为 $d_b=u(b)+k(b)$，并且

$$
u(b)+2k(b)\le n+1,
\tag{6.1}
$$

等号成立当且仅当 $n$ 为奇数且 $b$ 是以 $1$ 开头、以 $1$ 结尾、$1$ 与 $0$ 交替的词 $1010\cdots01$（$n=1$ 时即词 $1$）。

**证明。** $b$ 的邻点恰为 $b+e_i$（$i$ 为可翻转零）与 $b-e_i$（$b_i=1$）；删去一个 $1$ 总保持合法，添加一个 $1$ 保持合法当且仅当该位置是可翻转零。故 $d_b=u(b)+k(b)$。

若 $k(b)=0$，则每个位置都是可翻转零，$u=n<n+1$。设 $k=k(b)\ge1$，$1$ 的位置为 $p_1<\cdots<p_k$，合法性给出 $p_{j+1}-p_j\ge2$。称与某个 $1$ 相邻的 $0$ 位为受阻零。位置 $p_j+1$（$1\le j<k$）是 $k-1$ 个互不相同的受阻零；若 $p_1\ge2$，$p_1-1$ 是另一个受阻零；若 $p_k\le n-1$，$p_k+1$ 又是另一个受阻零。每个位置恰是 $1$、受阻零或可翻转零之一；以 $[\,\cdot\,]$ 记命题的示性值（真为 $1$、假为 $0$），得

$$
u(b)\le n-k-(k-1)-[p_1\ge2]-[p_k\le n-1]\le n-2k+1,
$$

得 (6.1)。等号要求 $p_1=1$、$p_k=n$ 且受阻零恰为上述 $k-1$ 个；若某个间隔 $p_{j+1}-p_j\ge3$，则 $p_{j+1}-1$ 是不同于 $p_j+1$ 的第 $k$ 个受阻零，故所有间隔都等于 $2$，即 $b=1010\cdots01$ 且 $n=2k-1$ 为奇数。反之该词有 $u=0$、$k=(n+1)/2$，等号成立。

**定理 6.2（显式分配与增长常数上界）。** 令 $t=\sqrt2-1$。对 $n\ge1$，在 $\Gamma_n$ 的每条边 $\{b,b+e_i\}$ 上取

$$
a_{b+e_i\leftarrow b}=t,\qquad a_{b\leftarrow b+e_i}=1-t,
$$

则每个顶点的负载为 $L_b^{\Gamma_n}(a)=(3-2\sqrt2)\bigl(u(b)+2k(b)\bigr)$，最大负载等于 $(3-2\sqrt2)\max_b(u(b)+2k(b))$，奇数 $n$ 时恰为 $(3-2\sqrt2)(n+1)$。于是

$$
\kappa_n\le(3-2\sqrt2)(n+1)\quad(n\ge0),\qquad c_\star\le3-2\sqrt2=0.17157\ldots,
\tag{6.2}
$$

并且当且仅当 $n\ge5$ 时有

$$
(3-2\sqrt2)(n+1)<\max\Bigl\{\frac{49n}{256},\ \frac n4-\frac{47}{256}\Bigr\}.
\tag{6.3}
$$

**证明。** $b$ 有 $u(b)$ 条向上的边，$b$ 是其低端，各贡献 $t^2$；有 $k(b)$ 条向下的边，$b$ 是其高端，各贡献 $(1-t)^2$。由 $t^2=3-2\sqrt2$ 与 $(1-t)^2=(2-\sqrt2)^2=6-4\sqrt2=2t^2$，得 $L_b=t^2(u+2k)$。引理 6.1 给出最大负载的表达式及奇数 $n$ 的取值，并给出 $\kappa_n\le t^2(n+1)$；$n=0$ 时两边为 $0\le t^2$。由 (5.2)，$c_\star=\sup_n\kappa_n/(n+1)\le t^2$。

比较 (6.3)：$n\ge4$ 时 $\frac n4-\frac{47}{256}\ge\frac{49n}{256}$（等价于 $15n\ge47$）。令 $D(n)=\frac n4-\frac{47}{256}-(3-2\sqrt2)(n+1)$，则 $D(n+1)-D(n)=2\sqrt2-\frac{11}4>0$（因 $8\cdot16>11^2$）。又

$$
D(5)=12\sqrt2-\frac{4335}{256}>0\iff 288\cdot256^2>4335^2,
$$

后者为 $18874368>18792225$，故 $n\ge5$ 时 (6.3) 成立。对 $n\le4$ 反向成立：$n=4$ 时需 $5(3-2\sqrt2)\ge\frac{209}{256}$，即 $\frac{3631}{256}\ge10\sqrt2$，等价于 $3631^2=13184161\ge200\cdot256^2=13107200$；$n=3$ 时需 $4(3-2\sqrt2)\ge\frac{147}{256}$，即 $\frac{2925}{256}\ge8\sqrt2$，等价于 $2925^2=8555625\ge128\cdot256^2=8388608$；$n=1,2$ 时左边分别为 $0.343\ldots$ 与 $0.514\ldots$，右边的最大值分别为 $\frac{49}{256}<0.2$ 与 $\frac{98}{256}<0.39$。

定理 6.2 的分配是星图 $\Gamma_2=K_{1,2}$ 的最优分配（命题 4.4，$m=2$ 时份额 $1/(1+\sqrt2)=t$）在每个局部的照搬；它对 $n=2$ 最优，对 $n=1$ 与 $n=3$ 不最优（命题 9.3(iv)）。母卷式（2.3）只对 $n=3N$ 陈述，(6.3) 对这些 $n$ 全部成立（$n\ge6$）。

**命题 6.3（$n=12$ 的有理证书）。** 存在 $\Gamma_{12}$ 上分母为 $2^{40}$ 的有理分配 $a$ 与有理概率测度 $\mu$，使

$$
\frac{180487}{100000}\le\Phi_{\Gamma_{12}}(\mu)\le\kappa_{12}\le\max_bL_b^{\Gamma_{12}}(a)\le\frac{180488}{100000}.
$$

因此 $c_\star\le\kappa_{12}/12\le\frac{180488}{1200000}<0.150407$。

**证明。** 中间两个不等号是定理 3.2(iii)。第 11 章代码块第 7 段以一个固定的确定性迭代产生候选 $a$ 与 $\mu$，再把它们取整为有理数并以精确有理算术核验首尾两个不等式；浮点迭代只用于提出候选，结论只依赖精确核验。最后一句由 (5.3) 的左半不等式 $c_\star\le\kappa_{12}/12$ 与 $180488/1200000=0.1504066\ldots$ 得到。

由 (5.3) 的右半不等式，命题 6.3 同时给出 $c_\star\ge\kappa_{12}/13\ge0.13883$；在 $n=12$ 处，这一下界弱于第 7 章的硬核下界。

## 7. 硬核测度下界

**命题 7.1（硬核测度的对偶值）。** 对 $n\ge1$ 与 $\lambda>0$，

$$
\Phi_{\Gamma_n}\bigl(\mu^{(n)}_\lambda\bigr)=\frac{\lambda}{1+\lambda}\,\mathbb E^{(n)}_\lambda[u],
\qquad\text{因而}\qquad
\kappa_n\ge\frac{\lambda}{1+\lambda}\,\mathbb E^{(n)}_\lambda[u].
\tag{7.1}
$$

**证明。** 简记 $\mu_\lambda=\mu^{(n)}_\lambda$。$\Gamma_n$ 的每条边可唯一写成 $\{b,b+e_i\}$，其中 $b$ 是低端、$i$ 是 $b$ 的可翻转零；反之每个这样的对 $(b,i)$ 给出一条边。由 $\mu_\lambda(b+e_i)=\lambda\mu_\lambda(b)$ 与引理 3.1(ii) 的齐次性，$h(\mu_\lambda(b),\lambda\mu_\lambda(b))=\mu_\lambda(b)\,h(1,\lambda)=\frac{\lambda}{1+\lambda}\mu_\lambda(b)$。按低端求和得等式，不等式来自定理 3.2(iii)。

$\lambda=1$ 时 (7.1) 的右边是 $\frac12\mathbb E_1^{(n)}[u]=e_n/(2F_{n+2})=C_n$，即推论 4.3(i) 的均匀下界；$\lambda<1$ 时测度把质量移向 $1$ 较少的词。

**引理 7.2（配分函数与窗口计数）。** 固定 $\lambda>0$ 及约定 2.6 的 $r,s,\vartheta$，记 $Z_m=Z_m(\lambda)$。

(i) $Z_0=1$，$Z_1=1+\lambda$，$Z_m=Z_{m-1}+\lambda Z_{m-2}$（$m\ge2$）。

(ii) 对 $m\ge0$，$Z_m=\dfrac{r^{m+2}-s^{m+2}}{r-s}$，且

$$
\frac{r^{m+2}(1-\vartheta^{m+2})}{2r-1}\le Z_m\le\frac{r^{m+2}(1+\vartheta^{m+2})}{2r-1}.
\tag{7.2}
$$

(iii) 对 $n\ge3$ 与 $2\le i\le n-1$，

$$
\sum_{b\in B_n:\ b_{i-1}=b_i=b_{i+1}=0}\lambda^{k(b)}=Z_{i-2}\,Z_{n-i-1}.
\tag{7.3}
$$

**证明。** (i) $B_0$ 只含空词，$B_1=\{0,1\}$。$m\ge2$ 时按末位分类：末位为 $0$ 的合法词是 $B_{m-1}$ 的词后接 $0$；末位为 $1$ 的合法词其倒数第二位必为 $0$，是 $B_{m-2}$ 的词后接 $01$。两类的权和分别为 $Z_{m-1}$ 与 $\lambda Z_{m-2}$。

(ii) $r,s$ 是 $x^2=x+\lambda$ 的两根，所以右边满足 (i) 的递推；$m=0$ 时右边为 $r+s=1$，$m=1$ 时为 $r^2+rs+s^2=(r+s)^2-rs=1+\lambda$。两者在 $m=0,1$ 一致且满足同一二阶递推，故处处相等。由 $r-s=2r-1>0$、$|s|=r-1=\vartheta r$，得 $s^{m+2}=\pm\vartheta^{m+2}r^{m+2}$，即 (7.2)。

(iii) 满足条件的词唯一地写成 $b'\,000\,b''$，$b'\in B_{i-2}$，$b''\in B_{n-i-1}$；中间三个零使任意 $b'$、$b''$ 的拼接仍合法，权重相乘。

**定理 7.3（增长常数的硬核下界）。** 对每个 $r>1$ 与每个 $n\ge1$，

$$
\kappa_n\ge g(r)\,\frac{n-2-2(r-1)^2/r}{1+\vartheta^{n+2}},\qquad \vartheta=\frac{r-1}{r}.
\tag{7.4}
$$

因此 $c_\star\ge g(r)$ 对每个 $r>1$ 成立。多项式 $p$ 在 $(1,\infty)$ 中恰有一个根 $r_\star$，$1.4<r_\star<1.5$；$g$ 在 $(1,r_\star]$ 上严格递增、在 $[r_\star,\infty)$ 上严格递减，于是

$$
c_\star\ge\sup_{r>1}g(r)=g(r_\star),\qquad
\frac{1800}{12559}=g\Bigl(\frac{29}{20}\Bigr)\le g(r_\star),\qquad
0.14333115<g(r_\star)<0.14333116.
\tag{7.5}
$$

并且对每个 $n\ge0$，$\kappa_n\ge g(r_\star)\,n\ge\frac{1800}{12559}\,n$。

**证明。** 取 $\lambda=r(r-1)$，则 $\frac{\lambda}{1+\lambda}=\frac{r(r-1)}{r^2-r+1}$。只计内部可翻转零（$2\le i\le n-1$；端点 $i=1,n$ 的贡献非负，略去），由 (7.3)，

$$
\mathbb E^{(n)}_\lambda[u]\ge\sum_{i=2}^{n-1}\frac{Z_{i-2}Z_{n-i-1}}{Z_n}.
$$

令 $j=i-2\in\{0,\ldots,n-3\}$，则 $(i-2)+2=j+2$，$(n-i-1)+2=n-1-j$。由 (7.2)，

$$
\frac{Z_{i-2}Z_{n-i-1}}{Z_n}
\ge\frac{r^{(j+2)+(n-1-j)}(1-\vartheta^{j+2})(1-\vartheta^{n-1-j})}{(2r-1)^2}\cdot\frac{2r-1}{r^{n+2}(1+\vartheta^{n+2})}
=\frac{(1-\vartheta^{j+2})(1-\vartheta^{n-1-j})}{r(2r-1)(1+\vartheta^{n+2})}.
$$

对 $x,y\in[0,1]$ 有 $(1-x)(1-y)\ge1-x-y$，且 $\sum_{j=0}^{n-3}\vartheta^{j+2}\le\vartheta^2/(1-\vartheta)$、$\sum_{j=0}^{n-3}\vartheta^{n-1-j}\le\vartheta^2/(1-\vartheta)$，而 $\vartheta^2/(1-\vartheta)=(r-1)^2/r$。于是对 $n\ge3$，

$$
\mathbb E^{(n)}_\lambda[u]\ge\frac{n-2-2(r-1)^2/r}{r(2r-1)(1+\vartheta^{n+2})}.
$$

乘以 $\frac{\lambda}{1+\lambda}$ 并用 $\frac{r(r-1)}{r^2-r+1}\cdot\frac1{r(2r-1)}=g(r)$ 及命题 7.1，得 $n\ge3$ 时的 (7.4)。$n=1,2$ 时 (7.4) 右边的分子 $n-2-2(r-1)^2/r\le0$，不等式由 $\kappa_n\ge0$ 成立。

(7.4) 两边除以 $n$ 并令 $n\to\infty$，$\vartheta^{n+2}\to0$，由定理 5.2 得 $c_\star=\lim\kappa_n/n\ge g(r)$。

对 $r>1$，对数求导并乘以正数 $(r-1)(r^2-r+1)(2r-1)$：

$$
\frac{g'(r)}{g(r)}(r-1)(r^2-r+1)(2r-1)
=(r^2-r+1)(2r-1)-(2r-1)^2(r-1)-2(r-1)(r^2-r+1)=-p(r).
$$

又 $p'(r)=12r^2-18r+6=6(2r-1)(r-1)>0$（$r>1$），$p(1)=-1$，$p(1.4)=-0.264$，$p(1.5)=0.25$，故 $p$ 在 $(1,\infty)$ 上严格递增，恰有一个根 $r_\star\in(1.4,1.5)$，$g'$ 在 $(1,r_\star)$ 上为正、在 $(r_\star,\infty)$ 上为负。由此 $\sup_{r>1}g=g(r_\star)$。代入 $r=29/20$：$r-1=9/20$，$r^2-r+1=661/400$，$2r-1=19/10$，$g=\frac{9}{20}\cdot\frac{4000}{661\cdot19}=\frac{1800}{12559}$。数值区间：若有理数 $\rho_-<r_\star<\rho_+$ 且 $\rho_->1$，则 $g(\rho_-)\le g(r_\star)$；又 $g(r_\star)$ 的分子在 $r_\star$ 处不超过 $\rho_+-1$、分母的两个因子在 $r>1/2$ 上递增，故 $g(r_\star)\le(\rho_+-1)/((\rho_-^2-\rho_-+1)(2\rho_--1))$。第 11 章代码块第 5 段以 $p$ 的符号在有理数上二分 40 次得到宽 $2^{-40}/10$ 的括号，并以精确有理算术核验两侧界落在 $(0.14333115,\,0.14333116)$ 内。

最后，由 (5.3) 左半与 $c_\star\ge g(r_\star)$，$\kappa_n\ge c_\star n\ge g(r_\star)n$。

**推论 7.4（与均匀系数的线性分离）。** $C_n/n\to\frac{5-\sqrt5}{20}=g(\varphi)=0.13819\ldots$，并且：

(i) 对 $n\ge2$，$C_n\le\frac{7n+4}{50}$，从而 $\kappa_n-C_n\ge\frac{2087}{627950}\,n-\frac{2}{25}$；

(ii) $\liminf_n(\kappa_n-C_n)/n\ge g(r_\star)-g(\varphi)>0.0051$；

(iii) $\kappa_n/C_n\to\frac{20\,c_\star}{5-\sqrt5}$。

**证明。** 由母卷式（1.1）所复用的边数公式 $e_n=\bigl(nF_{n+1}+2(n+1)F_n\bigr)/5$（对每个 $n\ge1$ 成立的 Fibonacci 立方计数，文献步骤见第 10 章，第 11 章对 $n\le16$ 逐一核对）与 $|B_n|=F_{n+2}$，

$$
C_n=\frac{e_n}{2F_{n+2}}=\frac{n\,(F_{n+2}+F_n)+2F_n}{10\,F_{n+2}}.
\tag{7.6}
$$

Binet 公式给出 $F_n/F_{n+2}\to\varphi^{-2}=(3-\sqrt5)/2$，故 $C_n/n\to\bigl(1+\frac{3-\sqrt5}2\bigr)/10=\frac{5-\sqrt5}{20}$。又 $\varphi^2-\varphi=1$、$2\varphi-1=\sqrt5$，所以 $g(\varphi)=\frac{\varphi-1}{2\sqrt5}=\frac{5-\sqrt5}{20}$。

(i) $F_n/F_{n+2}\le2/5$ 对 $n\ge2$ 成立：它等价于 $3F_n\le2F_{n+1}$，即 $\rho_n=F_{n+1}/F_n\ge3/2$；$\rho_2=2$，且若 $\rho_n\in[3/2,2]$ 则 $\rho_{n+1}=1+1/\rho_n\in[3/2,5/3]$。代入 (7.6) 得 $C_n\le(7n/5+4/5)/10=(7n+4)/50$。与定理 7.3 的 $\kappa_n\ge\frac{1800}{12559}n$ 相减，$\frac{1800}{12559}-\frac7{50}=\frac{90000-87913}{627950}=\frac{2087}{627950}$。

(ii) 由定理 5.2 与上面的极限，$\lim(\kappa_n-C_n)/n=c_\star-g(\varphi)\ge g(r_\star)-g(\varphi)$；又 $g(r_\star)>0.14333$，而 $g(\varphi)=\frac{5-\sqrt5}{20}<0.1382$ 等价于 $\sqrt5>2.236$，即 $5>4.999696$。

(iii) 两个极限之比，分母极限为正。

由推论 7.4(i)，$n\ge25$ 时 $\kappa_n-C_n>0$ 的线性下界本身已为正；对一切 $n\ge2$ 的严格性 $\kappa_n>C_n$ 另由推论 4.3(ii) 与 $\Gamma_n$ 的不规则性得到，与母卷 §3.1 一致。

## 8. 对母卷 minimax 首项系数的推论

**定理 8.1（minimax 首项系数的增长律）。** 设 $n=3N$（$N\ge1$），$x$、$\delta_n(L,q)$、$\beta_n(L,q)$、$\beta_n^{\mathrm{mm}}(L,q)$ 按母卷定义 1.3–1.4，$C_n$ 按母卷式（1.1）。则：

(i) 对每个固定 $N$，沿母卷定理 2.1(B) 的参数族，

$$
\delta_n(L,q)=\kappa_nx^2+O_n(x^3),\qquad \kappa_n=c_\star n+\theta_n,\quad 0\le\theta_n\le c_\star;
$$

(ii) $0.14333115<c_\star<0.150407$；

(iii) $\kappa_n/C_n\to20c_\star/(5-\sqrt5)\in(1.0371,\,1.0884)$，且 $\kappa_n/(n/4)\to4c_\star\in(0.5733,\,0.6017)$；

(iv) 对每个原整数合同（母卷定义 1.3 的任意 $L\ge1$ 与 $0\le q\le L$），记 $\gamma=1800/12559$，

$$
\delta_n(L,q)\ge x\,\frac{\sqrt{1+4\gamma nx}-1}{\sqrt{1+4\gamma nx}+1}
=x-\frac{2x}{1+\sqrt{1+4\gamma nx}};
\tag{8.1}
$$

(v) 对每个固定 $N$，$\beta_n(L,q)-\beta_n^{\mathrm{mm}}(L,q)=(\kappa_n-C_n)x^2+O_n(x^3)$，其中 $\kappa_n-C_n\ge\frac{2087}{627950}n-\frac2{25}$，且 $\lim_n(\kappa_n-C_n)/n>0.0051$。

(i) 与 (v) 中的 $O_n$ 常数与适用邻域只对固定 $n$ 成立，不承诺对增长的 $n$ 一致；(iv) 对一切 $n=3N$ 与一切合同一致成立。

**证明。** (i) 第一式是母卷定理 2.1(B) 的式（2.2）；第二式是 (5.3)。

(ii) 下界是 (7.5)；上界是命题 6.3。

(iii) 极限由推论 7.4(iii) 与定理 5.2 得到。区间：$5-\sqrt5\in(2.7639,\,2.76394)$，因为 $2.23606^2=4.99996\ldots<5<5.00014\ldots=2.2361^2$；于是 $20c_\star/(5-\sqrt5)>20\cdot0.14333115/2.76394>1.0371$，且 $<20\cdot0.150407/2.7639<1.0884$。$4c_\star$ 的区间由 (ii) 直接得到。

(iv) 母卷式（2.1）对每个合同给出 $\delta_n(L,q)\ge v_n(x)=4\kappa_nx^2/(1+\sqrt{1+4\kappa_nx})^2$。置 $S=\sqrt{1+4\kappa_nx}$，则 $4\kappa_nx=(S-1)(S+1)$，故 $v_n(x)=x(S-1)/(S+1)=x-2x/(1+S)$。函数 $y\mapsto1-2/(1+\sqrt{1+y})$ 在 $y\ge0$ 上不减；由定理 7.3，$\kappa_n\ge\gamma n$，又 $x\ge0$，所以 $4\kappa_nx\ge4\gamma nx$，得 (8.1)。

(v) 第一式是母卷式（2.4）；系数下界是推论 7.4(i)；极限由推论 7.4(ii)。

定理 8.1(iii) 的第二个极限与母卷定理 2.1(D) 合读：任一 Bayes 首项最优的参数族，其最坏来源错误首项为 $(n/4)x^2$，而 minimax 首项为 $\kappa_nx^2$，两者之比的极限 $4c_\star$ 小于 $0.6017$。(8.1) 表明：对固定的 $x\in(0,1]$，当 $n\to\infty$ 时，最坏来源整词错误的下界趋于 $x$；这一下界对 $N$ 一致，而母卷的可达首项只对固定 $N$ 成立。

## 9. 反例与不能推广的边界

**命题 9.1（式（5.1）的两个平移都不可去）。** $\kappa_2<\kappa_1+\kappa_1$ 且 $\kappa_3>\kappa_1+\kappa_1$。因此「$\kappa_{n+m}\ge\kappa_n+\kappa_m$ 对一切 $n,m$ 成立」与「$\kappa_{n+m+1}\le\kappa_n+\kappa_m$ 对一切 $n,m$ 成立」都为假，(5.1) 不能改成等式，也不能互换两侧的指标平移。

**证明。** $\kappa_2=2(3-2\sqrt2)=0.343\ldots<\tfrac12=2\kappa_1$（推论 5.3(ii)）。由命题 9.3(iii)，$\kappa_3\ge\tfrac{13}{25}>\tfrac12=2\kappa_1$；这与母卷定理 2.1(E) 的 $\kappa_3=\tau^2>\tfrac12$ 一致。

**命题 9.2（可加性只属于 Cartesian 积）。** (i) $K_{1,2}$ 是两个不交边集的生成子图之并，每个生成子图同构于 $K_2\sqcup K_1$，其 $\kappa$ 为 $\tfrac14$；但 $\kappa(K_{1,2})=2(3-2\sqrt2)<\tfrac12$，故定理 4.1(ii) 的不等号可以严格。(ii) $\kappa(K_2\sqcup K_2)=\tfrac14\ne\kappa(K_2)+\kappa(K_2)$，故不交并不可加。

**证明。** (i) $K_{1,2}$ 的两条边各自构成一个三顶点生成子图，同构于 $K_2\sqcup K_1$；由定理 4.1(iii) 与推论 4.3(iv)，其 $\kappa=\max\{\tfrac14,0\}=\tfrac14$。命题 4.4 给出 $\kappa(K_{1,2})$。(ii) 由定理 4.1(iii)。

**命题 9.3（硬核族的精确与不精确）。** 记 $H_n=\sup_{\lambda>0}\frac{\lambda}{1+\lambda}\mathbb E^{(n)}_\lambda[u]$，它是命题 7.1 在硬核族上能给出的最好下界。

(i) $H_1=\kappa_1=\tfrac14$，在 $\lambda=1$ 处取到。

(ii) $H_2=\kappa_2=2(3-2\sqrt2)$，在 $\lambda=1/\sqrt2$ 处取到。

(iii) $H_3<\tfrac{507}{1000}<\tfrac{13}{25}\le\kappa_3$；即 $n=3$ 时没有硬核测度是 $\Phi_{\Gamma_3}$ 的最大点。

(iv) 定理 6.2 的分配在 $n=2$ 最优，在 $n=1$ 与 $n=3$ 不最优。

**证明。** (i) $B_1=\{0,1\}$，$u(0)=1$，$u(1)=0$，$Z_1=1+\lambda$，故所求为 $\lambda/(1+\lambda)^2\le\tfrac14$（因 $(1+\lambda)^2\ge4\lambda$），等号仅在 $\lambda=1$。

(ii) $B_2=\{00,10,01\}$，只有 $u(00)=2$ 非零，$Z_2=1+2\lambda$，所求为 $2\lambda/\bigl((1+\lambda)(1+2\lambda)\bigr)$。由 $1+2\lambda^2\ge2\sqrt2\,\lambda$（等号仅在 $\lambda=1/\sqrt2$），$(1+\lambda)(1+2\lambda)=1+3\lambda+2\lambda^2\ge(3+2\sqrt2)\lambda$，故所求至多 $2/(3+2\sqrt2)=2(3-2\sqrt2)=\kappa_2$，并在 $\lambda=1/\sqrt2$ 取等。

(iii) $B_3=\{000,100,010,001,101\}$ 的 $u$ 值依次为 $3,1,0,1,0$，$k$ 值依次为 $0,1,1,1,2$，故 $Z_3=1+3\lambda+\lambda^2$，所求为 $\psi(\lambda)=\lambda(3+2\lambda)/\bigl((1+\lambda)(1+3\lambda+\lambda^2)\bigr)$。令 $\eta=\tfrac{507}{1000}$，

$$
P(\lambda)=\eta(1+\lambda)(1+3\lambda+\lambda^2)-\lambda(3+2\lambda)=\eta\lambda^3+(4\eta-2)\lambda^2+(4\eta-3)\lambda+\eta.
$$

取 $\xi=\tfrac{39}{50}$，由三项算术–几何平均，$\lambda^3+2\xi^3\ge3\xi^2\lambda$（$\lambda\ge0$），于是 $P(\lambda)\ge q_2\lambda^2+q_1\lambda+q_0$，其中

$$
q_2=4\eta-2=\frac7{250},\qquad q_1=3\eta\xi^2+4\eta-3=-\frac{116559}{2500000},\qquad q_0=\eta-2\eta\xi^3=\frac{1612767}{62500000},
$$

且 $q_1^2-4q_2q_0=-\frac{4476989919}{6250000000000}<0$、$q_2>0$，故 $P(\lambda)>0$，即 $\psi(\lambda)<\eta$ 对一切 $\lambda>0$ 成立，$H_3\le\eta$。为得到严格不等号，再由 $\psi(\lambda)\to0$（$\lambda\to0$ 或 $\lambda\to\infty$）与连续性，$\psi$ 在 $(0,\infty)$ 上取到最大值，故 $H_3<\eta$。另一方面，取 $\Gamma_3$ 上的测度

$$
\mu(000)=\frac{249}{1000},\quad \mu(100)=\mu(001)=\frac{221}{1000},\quad \mu(101)=\frac{213}{1000},\quad \mu(010)=\frac{96}{1000}.
$$

$\Gamma_3$ 的边为 $000\text{–}100$、$000\text{–}001$、$000\text{–}010$、$100\text{–}101$、$001\text{–}101$，所以

$$
\Phi_{\Gamma_3}(\mu)=\frac1{1000}\Bigl(\frac{55029}{235}+\frac{7968}{115}+\frac{47073}{217}\Bigr)=\frac{76293117}{146610625}=0.52037\ldots\ge\frac{13}{25},
$$

由定理 3.2(iii) 得 $\kappa_3\ge\tfrac{13}{25}$。若某个硬核测度是最大点，则 $H_3\ge\kappa_3\ge\tfrac{13}{25}$，矛盾。

(iv) 由定理 6.2，$n=1$ 时最大负载为 $2t^2=2(3-2\sqrt2)>\tfrac14=\kappa_1$；$n=2$ 时最大负载为 $2t^2=\kappa_2$；$n=3$ 时词 $101$ 的负载为 $4t^2=4(3-2\sqrt2)$，而母卷式（2.7）给出 $\kappa_3<\tfrac9{16}$，且 $4(3-2\sqrt2)>\tfrac9{16}$ 等价于 $\tfrac{183}{16}>8\sqrt2$，即 $183^2=33489>32768=64\cdot512$。

命题 9.3(iii) 是有限 $n$ 的边界现象，它不判定 $c_\star$ 是否等于 $g(r_\star)$。

**开放问题 9.4（$c_\star$ 的精确值与硬核渐近最优性）。** 确定 $c_\star\in(0.14333115,\,0.150407)$ 的精确值；特别地，是否有 $c_\star=g(r_\star)$。缺的一步在两侧之一：上侧需要一族分配，其最大负载为 $g(r_\star)n+o(n)$，并对全部合法词有一致的最坏情形估计；下侧需要一族平移不变而非硬核的测度，其 $\lim_n\Phi_{\Gamma_n}/n$ 严格大于 $g(r_\star)$。本卷两者都未证明。$\kappa_n$ 是否有 Fibonacci 型闭式（母卷开放问题 5.4 的剩余部分）同样未解决。

**开放问题 9.5（常数项与最优测度的结构）。** 由 (5.3)，$\theta_n=\kappa_n-c_\star n\in[0,c_\star]$。$\theta_n$ 是否收敛，是否沿 $n$ 的奇偶分别收敛，均未确定。$\Phi_{\Gamma_n}$ 的最大点是否唯一、是否满支撑、是否关于 $k(b)$ 单调也未确定；$h$ 沿射线是线性的，所以 $\Phi_{\Gamma_n}$ 的凹性不自动给出唯一性，推论 3.3 只给出反转不变最大点的存在。

**开放问题 9.6（首项余项的一致性）。** 母卷式（2.2）的 $O_n(x^3)$ 只对固定 $n$ 成立，定理 8.1(i) 不涉及 $n$ 与 $x$ 同时变化的区域。(8.1) 是一致下界；是否存在一致的上界，例如在 $nx\to0$ 的区域内有 $\delta_n=c_\star nx^2(1+o(1))$，本卷没有证明。

## 10. 来源、文献状态与核验边界

**文献表态（第 3.7 条，三值之一）。**

| 来源 | 精确范围与使用边界 |
| --- | --- |
| [母卷][Minimax] 定义 1.2–1.5，式（1.1）（1.2）（2.1）（2.2）（2.3）（2.4）（2.7），定理 2.1(A)–(E)，§3.1，开放问题 5.4 | 仓内既有结果，本卷第 8 章、命题 9.1 与命题 9.3(iv) 按编号引用，不重证；本卷不改判母卷的任何条目。 |
| [Correlated Word Recovery 卷][Recovery] 式（2.4）–（2.5） | 仓内既有结果：合法词图边数与均匀系数，经母卷式（1.1）复用于推论 7.4。 |
| [Klavžar、Mollard、Petkovšek，*The degree sequence of Fibonacci and Lucas cubes*][KMP]，§§1–2 | `literature-attested`：Fibonacci 立方的计数，即式（7.6）所用边数闭式的来源背景；不供应 $\kappa$。 |
| [W.-J. Hsu，*Fibonacci cubes—a new interconnection topology*][Hsu]，IEEE Trans. Parallel Distrib. Syst. 4（1993）3–12 | `literature-attested`：图 $\Gamma_n$ 即 Fibonacci 立方的定义与命名；不供应负载量。 |
| [S. Klavžar，*Structure of Fibonacci cubes: a survey*][Survey]，J. Comb. Optim. 25（2013）505–522 | `literature-attested`：$\Gamma_0=K_1$ 的约定、$\Gamma_n$ 的连通性等背景。引理 5.1 的两个积嵌入在本卷检索范围内未定位到逐字先例（该综述全文未取得核对），本卷以初等证明给出，作为中间步骤，不列为新增承重内容。 |
| [M. Sion，*On general minimax theorems*][Sion]，Pacific J. Math. 8（1958）171–176 | `literature-attested`：定理 3.2 强对偶一步所用的 minimax 定理；其前提（两侧紧凸、目标连续、对 $a$ 凸、对 $\mu$ 凹）在证明中逐条核对。 |
| M. Fekete，*Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit ganzzahligen Koeffizienten*，Math. Z. 17（1923）228–249 | `literature-attested`：定理 5.2 所用的次可加数列引理（Fekete 引理）。 |
| [A. D. Scott、A. D. Sokal，*The repulsive lattice gas, the independent-set polynomial, and the Lovász local lemma*][ScottSokal]（仓内 `Library/Arith/scottsokal2003repulsive.md`） | `literature-attested` 背景：独立集多项式即硬核配分函数的框架。路径上的递推与闭式（引理 7.2）是经典结果，本卷给出完整证明以便自足，不依赖该文。 |
| S. L. Hakimi，*On the degrees of the vertices of a directed graph*，J. Franklin Inst. 279（1965）290–308 | 类比引用：线性负载的定向与分数定向问题。本卷的平方份额负载、调和对偶与增长常数不由该文供应。 |
| [N. Devanur、U. Feige，*An $O(n\log n)$ algorithm for a load balancing problem on paths*][DF]；[动态定向的平方和度量][DynOri] | 类比引用：把边负载分给端点的平方型目标，其目标是全体顶点负载的平方和，与本卷「每个顶点的份额平方和的最大值」不同；不供应 $\kappa$、对偶式或增长常数。 |
| — | `repo-derived`：定理 3.2、推论 3.3、定理 4.1、定理 4.2、推论 4.3、命题 4.4、定理 5.2、推论 5.3、定理 6.2、命题 6.3、命题 7.1、定理 7.3、推论 7.4、定理 8.1、命题 9.1–9.3。其中承重条目为定理 3.2、4.2、5.2、6.2、7.3、8.1。引理 3.1（调和平均的变分式）、引理 5.1、引理 6.1、引理 7.2 是初等或经典的中间步骤，不计为新增承重内容。 |
| — | `suspected-novel`：作为一般有限图不变量的平方份额负载最小最大值 $\kappa(G)$ 及其调和对偶式（3.2）、Cartesian 积可加性（4.1），以及合法词图增长常数 $c_\star$ 的存在、夹逼（5.3）与两侧界（6.2）（7.5）。检索范围：三组网络检索（Fibonacci 立方与 Cartesian 积子图；平方份额最小最大定向、负载均衡与调和平均对偶；Fibonacci 立方、硬核测度与最小最大负载）；仓内 `docs/develop/theory/` 与 `Library/` 对 $\kappa_n$ 与 Fibonacci 立方的检索，$\kappa_n$ 只出现于母卷；Klavžar 2013 综述的主题范围。范围内未见此量；不据此声称世界优先性。 |

**核验边界。** 第 11 章代码块只用 Python 标准库，固定输入，无随机性，各段覆盖如下：第 1 段对 $1\le n\le16$ 核对 $|B_n|=F_{n+2}$、边数闭式、词反转保持边、$d_b=u(b)+k(b)$ 以及引理 6.1 的不等式与等号情形；第 2 段对 $0\le n,m\le6$ 核对引理 5.1 两个顶点映射的落点（边的保持由引理 5.1 的证明负责）；第 3 段对 $\lambda\in\{1/3,1/2,1,2,5\}$ 与 $1\le n\le12$ 以精确有理算术核对引理 7.2(i)(iii) 与命题 7.1 的等式；第 4 段对 $m\in\{1,4,9,16,25\}$ 核对命题 4.4 的原始值与对偶值相等；第 5 段核对定理 6.2、推论 7.4 中的整数不等式，以及 $r_\star$ 的有理括号与 $g(r_\star)$ 的区间；第 6 段核对命题 9.3(iii) 的多项式证书与显式测度；第 7 段是命题 6.3 的证书。

有限核验不证明任何全称命题。命题 6.3 与定理 7.3 中 $g(r_\star)$ 的八位小数区间以第 5、7 段为证明的一部分；其余定理的证明都是正文中的普通证明，代码只复核其中有限可算的数值与恒等式。第 7 段的浮点迭代只产生候选；候选在其它平台上的逐位取值未测，结论只依赖随后的精确有理核验；本机运行中候选的最大负载与上界 $1.80488$ 的差距约为 $1.6\times10^{-6}$，测度值与下界 $1.80487$ 的差距约为 $8.4\times10^{-6}$，均远大于分母 $2^{40}$ 取整引起的变化。母卷与 Recovery 卷的结论按其自身证明使用，本卷未重新核验。本卷没有任何 Lean 形式化。

## 11. 有限精确核验

以下代码只用 Python 标准库，固定输入，末行打印哨兵。段号与第 10 章「核验边界」的段号一致。

```python
from fractions import Fraction as Q
import math


def legal(n):
    return [w for w in range(1 << n) if not (w & (w >> 1))]


def flipmask(w, n):
    return ~(w | (w << 1) | (w >> 1)) & ((1 << n) - 1)


def edges(n):
    return [(w, w | (1 << i)) for w in legal(n) for i in range(n)
            if (flipmask(w, n) >> i) & 1]


def fib(k):
    a, b = 0, 1
    for _ in range(k):
        a, b = b, a + b
    return a


def ones(w):
    return bin(w).count("1")


def rev(w, n):
    return int(format(w, "0%db" % n)[::-1], 2) if n else 0


def h(s, t):
    return s * t / (s + t) if s + t else 0


def phi(E, mu):
    return sum(h(mu[b], mu[c]) for b, c in E)


# 1. counts, edge formula, reversal, degree = u + k, u + 2k <= n + 1
for n in range(1, 17):
    V, E = legal(n), edges(n)
    S, ES = set(V), set(E)
    assert len(V) == fib(n + 2)
    assert 5 * len(E) == n * fib(n + 1) + 2 * (n + 1) * fib(n)
    deg = dict.fromkeys(V, 0)
    for b, c in E:
        assert c in S and ones(c) == ones(b) + 1
        deg[b] += 1
        deg[c] += 1
        x, y = rev(b, n), rev(c, n)
        assert (min(x, y), max(x, y)) in ES
    alt = sum(1 << i for i in range(0, n, 2)) if n % 2 else None
    for w in V:
        u, k = ones(flipmask(w, n)), ones(w)
        assert deg[w] == u + k
        assert u + 2 * k <= n + 1 and ((u + 2 * k == n + 1) == (w == alt))

# 2. b0c lands in B_{n+m+1}; a word of B_{n+m} splits into B_n x B_m
for n in range(0, 7):
    for m in range(0, 7):
        Sb, Sn, Sm = set(legal(n + m + 1)), set(legal(n)), set(legal(m))
        assert all((b | (c << (n + 1))) in Sb for b in Sn for c in Sm)
        assert all((w & ((1 << n) - 1)) in Sn and (w >> n) in Sm
                   for w in legal(n + m))

# 3. hard-core measure: partition function, dual value, window counts
for lam in [Q(1, 3), Q(1, 2), Q(1, 1), Q(2, 1), Q(5, 1)]:
    Z = [Q(1), 1 + lam]
    for k in range(2, 13):
        Z.append(Z[-1] + lam * Z[-2])
    for n in range(1, 13):
        V, E = legal(n), edges(n)
        assert sum(lam ** ones(w) for w in V) == Z[n]
        mu = {w: lam ** ones(w) / Z[n] for w in V}
        Eu = sum(mu[w] * ones(flipmask(w, n)) for w in V)
        assert phi(E, mu) == lam / (1 + lam) * Eu
        for i in range(1, n - 1):
            win = sum(lam ** ones(w) for w in V if not (w >> (i - 1)) & 7)
            assert win == Z[i - 1] * Z[n - i - 2]

# 4. stars K_{1,m}, m = k^2: primal and dual values coincide
for k in range(1, 6):
    m, t, val = k * k, Q(1, 1 + k), Q(k * k, (1 + k) ** 2)
    assert m * t * t == val and (1 - t) ** 2 == val
    mc, ml = Q(1, 1 + k), Q(1, k * (1 + k))
    assert mc + m * ml == 1 and m * h(mc, ml) == val

# 5. exact inequalities and the maximiser of g
assert 5 * 12559 ** 2 > 26795 ** 2 and 1800 * 50 - 7 * 12559 == 2087
assert 4335 ** 2 < 288 * 256 ** 2 and 8 * 16 > 11 ** 2
assert 3631 ** 2 > 200 * 256 ** 2 and 2925 ** 2 > 128 * 256 ** 2
assert 183 ** 2 > 64 * 512 and 223606 ** 2 < 5 * 10 ** 10 < 22361 ** 2 * 100
p = lambda r: 4 * r ** 3 - 9 * r ** 2 + 6 * r - 2
g = lambda r: (r - 1) / ((r * r - r + 1) * (2 * r - 1))
lo, hi = Q(14, 10), Q(15, 10)
assert p(lo) < 0 < p(hi)
for _ in range(40):
    mid = (lo + hi) / 2
    lo, hi = (mid, hi) if p(mid) < 0 else (lo, mid)
glo, ghi = g(lo), (hi - 1) / ((lo * lo - lo + 1) * (2 * lo - 1))
assert Q(14333115, 10 ** 8) < glo <= ghi < Q(14333116, 10 ** 8)
assert g(Q(29, 20)) == Q(1800, 12559)

# 6. n = 3: hard-core values stay below 507/1000, explicit measure reaches 13/25
eta, xi = Q(507, 1000), Q(39, 50)
q2, q1, q0 = 4 * eta - 2, 3 * eta * xi * xi + 4 * eta - 3, eta - 2 * eta * xi ** 3
assert q2 > 0 and q1 * q1 - 4 * q2 * q0 == Q(-4476989919, 6250000000000)
assert (q2, q1, q0) == (Q(7, 250), Q(-116559, 2500000), Q(1612767, 62500000))
mu3 = {0: Q(249, 1000), 1: Q(221, 1000), 4: Q(221, 1000),
       5: Q(213, 1000), 2: Q(96, 1000)}
assert sum(mu3.values()) == 1
assert phi(edges(3), mu3) == Q(76293117, 146610625) >= Q(13, 25)

# 7. n = 12: an explicit allocation and an explicit measure, checked exactly
n, T = 12, 6000
V, E = legal(n), edges(n)
ix = {x: i for i, x in enumerate(V)}
P = [(ix[b], ix[c]) for b, c in E]
mu = [1.0 / len(V)] * len(V)
acc = [0.0] * len(E)
for t in range(T):
    L = [0.0] * len(V)
    sh = [mu[j] / (mu[i] + mu[j]) for i, j in P]
    for (i, j), x in zip(P, sh):
        L[i] += x * x
        L[j] += (1 - x) * (1 - x)
    if t >= T // 2:
        acc = [x + y for x, y in zip(acc, sh)]
    top = max(L)
    mu = [x * math.exp(0.5 * (y - top)) for x, y in zip(mu, L)]
    tot = sum(mu)
    mu = [x / tot for x in mu]
D = 2 ** 40
alloc = [Q(round(x / (T - T // 2) * D), D) for x in acc]
load = [Q(0)] * len(V)
for (i, j), x in zip(P, alloc):
    assert 0 <= x <= 1
    load[i] += x * x
    load[j] += (1 - x) * (1 - x)
assert max(load) <= Q(180488, 100000)
qm = [Q(round(x * D), D) for x in mu]
tot = sum(qm)
assert phi(E, {V[i]: x / tot for i, x in enumerate(qm)}) >= Q(180487, 100000)
print("FIB_LEGAL_EDGE_LOAD_CHECKS_PASSED")
```

[Minimax]: https://github.com/the-omega-institute/trureturing/blob/ae7d7572bd7f0d638e32e9fd724b64dae592b0f9/docs/develop/theory/FIB_ATOM_WHITEBOX_LEGAL_EDGE_MINIMAX.md
[Recovery]: https://github.com/the-omega-institute/trureturing/blob/ae7d7572bd7f0d638e32e9fd724b64dae592b0f9/docs/develop/theory/FIB_ATOM_WHITEBOX_CORRELATED_WORD_RECOVERY.md
[KMP]: https://users.fmf.uni-lj.si/klavzar/preprints/DegSeqRevised.pdf
[Hsu]: https://doi.org/10.1109/71.205649
[Survey]: https://doi.org/10.1007/s10878-011-9433-z
[Sion]: https://doi.org/10.2140/pjm.1958.8.171
[ScottSokal]: https://arxiv.org/abs/cond-mat/0309352
[DF]: https://www.microsoft.com/en-us/research/publication/log-n-algorithm-load-balancing-problem-paths/
[DynOri]: https://arxiv.org/abs/2504.16720

## 追加锚（本行以下为增补区）

# 素数双页 k-bonacci 编码：有限最优性与全局冗余

## 1. 有限窗口与两页容量

### 定义 1.1（分类、序号与固定宽度合同）

记 $\mathbb N_0=\{0,1,2,\ldots\}$。固定整数 $N\ge2$，令

$$
X_N=\{0,1,\ldots,N\},\qquad
\chi(n)=
\begin{cases}
1,&n\text{ 是素数},\\
0,&n\text{ 不是素数}.
\end{cases}
$$

其中 $0,1$ 都不是素数。对 $b\in\{0,1\}$，把同一类别按通常整数序排列为

$$
X_{N,b}=\{n\in X_N:\chi(n)=b\}
       =\{x_{b,0}<x_{b,1}<\cdots<x_{b,M_b-1}\},
\qquad A=A_N=M_0,\quad P=P_N=M_1.
$$

于是 $A+P=N+1$。页标 $b$ 与从零开始的页内序号 $r$ 共同指定原数 $x_{b,r}$。

固定整数 $k\ge2$。长度为 $m\ge1$ 的合同要求编码 $E:X_N\to\{0,1\}^m$ 为单射，每个码字不含连续 $k$ 个一，且第一位恰为 $\chi(n)$。允许前导零；解码器只在实际像 $E(X_N)$ 上定义。码长目标不计编码生成、素数枚举或完整整数解码的成本。只读第一位的判素任务以输入已经属于实际像为前提，未把任意位串的有效性判定包括在内。

按算术基本定理，对 $n\ge1$ 写 $n=\prod_p p^{v_p(n)}$，则 $\chi(n)=1$ 当且仅当 $\sum_pv_p(n)=1$：指数和为一恰表示只有一个素因子且指数为一。因此素数页也可称为乘法原子页；此解释不用于 $n=0$。

### 定义 1.2（整数位权与地址）

定义

$$
G_j^{(k)}=2^j\quad(0\le j<k),\qquad
G_j^{(k)}=\sum_{h=1}^kG_{j-h}^{(k)}\quad(j\ge k).
$$

固定 $k$ 时简记为 $G_j$。令 $\mathcal W_m^{(k)}$ 为长度恰为 $m$、不含 $1^k$ 的二进制词集，$\mathcal W_0^{(k)}=\{\varepsilon\}$，并置 $\mathcal W_*^{(k)}=\bigcup_{m\ge0}\mathcal W_m^{(k)}$。对高位在前的词 $w=b_{m-1}\cdots b_0$，令

$$
\operatorname{val}_k(w)=\sum_{j=0}^{m-1}b_jG_j,
\qquad \operatorname{val}_k(\varepsilon)=0.
$$

采用 [《递归关系观察与有效分辨率》](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md) 第 1.2 节式 TM.374–TM.384 的归一化与区间双射，记其逆为

$$
Z_{k,m}:\{0,\ldots,G_m-1\}\longrightarrow\mathcal W_m^{(k)}.
$$

所用区间归纳在定理 1.3 的证明中重述。这里的 $\operatorname{val}_k$ 计算整数地址，不是原数的解码器，也不是以增长根负幂为权的实数展开。

### 定理 1.3（有限双页编码、精确最短宽度与配对）

对 $N\ge2$、$k\ge2$，有 $A\ge P\ge1$。对 $m\ge1$，记首位为 $b$ 的合法词数为 $C_b(k,m)$，则

$$
C_0(k,m)=G_{m-1},\qquad C_1(k,m)=G_m-G_{m-1},
\qquad 1\le C_1(k,m)\le C_0(k,m).
$$

两页的地址区间分别为

$$
[0,G_{m-1})\cap\mathbb Z,\qquad [G_{m-1},G_m)\cap\mathbb Z.
$$

合同可行当且仅当 $A\le C_0(k,m)$ 且 $P\le C_1(k,m)$。集合非空，故可定义

$$
m_*(N,k)=\min\{m\ge1:A\le G_{m-1},\ P\le G_m-G_{m-1}\}.
$$

在任意可行宽度 $m$，令

$$
E_{N,k,m}(x_{b,r})=Z_{k,m}(r+bG_{m-1}),\qquad
\mathcal C_{N,k,m}=E_{N,k,m}(X_N).
$$

对 $w\in\mathcal C_{N,k,m}$，置 $t=\operatorname{val}_k(w)$，定义

$$
D_{N,k,m}(w)=
\begin{cases}
x_{0,t},&0\le t<A,\\
x_{1,t-G_{m-1}},&G_{m-1}\le t<G_{m-1}+P.
\end{cases}
$$

这两个分支恰好给出实际像上的解码，且

$$
D_{N,k,m}\circ E_{N,k,m}=\operatorname{id}_{X_N},\qquad
E_{N,k,m}\circ D_{N,k,m}=\operatorname{id}_{\mathcal C_{N,k,m}}.
$$

编码合法且首位为 $\chi$，其最小宽度 $m_*(N,k)$ 在所有满足定义 1.1 合同的编码中最优，不限于页内保序的编码。在 $m=m_*(N,k)$ 时简记为 $E_{N,k}$、$D_{N,k}$、$\mathcal C_{N,k}$。

若只要求合法词保存完整身份，最小宽度为

$$
m_0(N,k)=\min\{m\ge0:G_m\ge N+1\}.
$$

它满足

$$
m_0(N,k)\le m_*(N,k)\le m_0(N,k)+1,
$$

并有精确二择一公式（下式 $m_0=m_0(N,k)$）：

$$
m_*(N,k)=
\begin{cases}
m_0,&A\le G_{m_0-1}\ \text{且}\ P\le G_{m_0}-G_{m_0-1},\\
m_0+1,&\text{其余情形}.
\end{cases}
$$

随着 $k$ 增大，$m_0(N,k)$ 与 $m_*(N,k)$ 均不增，且

$$
\min_{k\ge2}m_*(N,k)=m_{\mathrm{bin}}^*(N)
=1+\lceil\log_2 A\rceil.
$$

达到该宽度的最小阶数为

$$
k_{\min}(N)=\min\left\{k\ge2:
A\le G_{m_{\mathrm{bin}}^*(N)-1}^{(k)},\quad
P\le G_{m_{\mathrm{bin}}^*(N)}^{(k)}-G_{m_{\mathrm{bin}}^*(N)-1}^{(k)}
\right\}.
$$

对任意可行 $m$ 和 $0\le r<P$，还有精确配对

$$
E_{N,k,m}(x_{0,r})=0Z_{k,m-1}(r),\qquad
E_{N,k,m}(x_{1,r})=1Z_{k,m-1}(r).
$$

因此这对码字的 Hamming 距离为一。翻转首位的映射 $J$ 在这 $2P$ 个配对词组成的集合上是对合。对未配对的非素数序号 $P\le r<A$，翻转结果在 $r<C_1(k,m)$ 时合法但未分配，在 $r\ge C_1(k,m)$ 时含禁串；不能据此把 $J$ 当作整个实际码集的对合。

在确定性、零错误、按位读取、只给定有效码字而不预先给定页标的模型中，判素所需的最坏读取次数恰为一。

**证明。** 首先，$2\in X_N$，故 $P\ge1$。除 $2$ 外的素数都是大于等于 $3$ 的奇数，所以

$$
P\le1+\left\lfloor\frac{N-1}{2}\right\rfloor
=\left\lfloor\frac{N+1}{2}\right\rfloor,
\qquad A=N+1-P\ge P.
$$

又因 $0,1$ 均非素数，$A\ge2$。

为明确所引用的地址双射，对词长作强归纳。若 $m<k$，位权全为二的幂，结论为普通固定长度二进制表示；$m=0$ 的空词表示零。若 $m\ge k$，合法词唯一写作 $1^j0v$，其中 $0\le j<k$、$|v|=m-j-1$。令

$$
S_0=0,\qquad S_j=\sum_{h=1}^{j}G_{m-h}\quad(1\le j\le k).
$$

归纳假设说明，前缀 $1^j0$ 的全部尾词恰好按字典序表示

$$
[S_j,S_j+G_{m-j-1})\cap\mathbb Z
=[S_j,S_{j+1})\cap\mathbb Z.
$$

这些区间依次相接，且 $S_k=G_m$。组内保序来自归纳假设，组间保序来自前缀的字典序，故 $\operatorname{val}_k$ 是到 $[0,G_m)\cap\mathbb Z$ 的保序双射，特别地 $|\mathcal W_m^{(k)}|=G_m$。这是定义 1.2 所引已有区间结论的推导。

首位为零的词恰为 $0v$，其中 $v\in\mathcal W_{m-1}^{(k)}$，故其地址为 $[0,G_{m-1})\cap\mathbb Z$，数量为 $G_{m-1}$。首位为一的词占据剩余区间，给出 $C_1=G_m-G_{m-1}$。把首位一改成零不会产生禁串，且是单射，故 $C_1\le C_0$。词 $10^{m-1}$ 给出 $C_1\ge1$；当 $m\ge2$ 时，整个词族 $10v$ 给出

$$
C_1(k,m)\ge G_{m-2},\qquad G_m=C_0+C_1\le2G_{m-1}.
$$

初始段 $G_j=2^j$ 严格增长；在 $j\ge k$ 时，递推包含 $G_{j-1}$ 及至少一个正项，仍有 $G_j>G_{j-1}$。因此这列正整数无界。由 $C_0=G_{m-1}$ 和 $C_1\ge G_{m-2}$，两页容量都趋于无穷，最小可行宽度存在。

必要性由两页各自的单射计数得到。满足两项容量条件时，地址 $r+bG_{m-1}$ 分别落在对应页的合法区间内，且互不相同。区间双射立即给出合法性、首位条件和单射性；按页取回序号给出所写的两条逆恒等式。合法但地址不在两个已分配区间内的词不属于 $D$ 的定义域。尤其

$$
\operatorname{val}_k(E_{N,k,m}(x_{b,r}))=r+bG_{m-1},
\qquad D_{N,k,m}(E_{N,k,m}(x_{b,r}))=x_{b,r},
$$

前一个量是地址，后一个量才是原数。此处使用按词集序号编码的枚举方法，可参见 Cover, *Enumerative source encoding*, IEEE Transactions on Information Theory 19(1), 73–77 (1973), §I Proposition 1 及其逆算法，[DOI:10.1109/TIT.1973.1054929](https://doi.org/10.1109/TIT.1973.1054929)；该方法的引用不承担素数枚举的复杂度结论。

任意长度 $m$ 的合法单射需要 $G_m\ge N+1$，故 $m_*\ge m_0$。因为 $N+1\ge3$ 而 $G_0=1,G_1=2$，有 $m_0\ge2$。在宽度 $m_0+1$，第一项容量条件来自

$$
A\le N+1\le G_{m_0}=C_0(k,m_0+1).
$$

第二项则由完整的不等式链

$$
P\le\frac{N+1}{2}
\le\frac{G_{m_0}}{2}
\le G_{m_0-1}
\le C_1(k,m_0+1)
$$

得到。因此 $m_*\le m_0+1$，再在宽度 $m_0$ 检查两页条件即得二择一公式。

若 $k'\ge k$，不含 $1^k$ 的词必不含 $1^{k'}$，这在每个首位分支内也成立，所以两个容量和总容量随阶数不减。对任意二进制固定宽度 $m$，首位为零的位置只有 $2^{m-1}$ 个，故 $A\le2^{m-1}$ 必须成立，给出 $m\ge1+\lceil\log_2A\rceil$。反之取任意 $k>m_{\mathrm{bin}}^*(N)$，此宽度没有禁串，两页均有 $2^{m-1}\ge A\ge P$ 个位置，所以下界达到。达到集合非空且向上封闭，最小达到阶数遂由所写容量条件给出。

对首位为一的词 $1v$，有 $\operatorname{val}_k(1v)=G_{m-1}+\operatorname{val}_k(v)$。其尾地址恰遍历 $[0,C_1)\cap\mathbb Z$；长度 $m-1$ 的唯一性说明尾词正是 $Z_{k,m-1}(r)$。首位零的尾词同样如此，故 $r<P$ 时两页共用尾码。翻两次首位恢复原词，证明配对集合上的对合。若 $r\ge C_1$ 而 $1Z_{k,m-1}(r)$ 仍合法，其地址将大于等于 $G_m$，与区间双射矛盾；若 $P\le r<C_1$，该词合法但素数页没有此序号。这也证明未配对情形的完整分类。

读第一位足够判素。零次读取的确定性过程对所有输入给同一输出，但 $0$ 与 $2$ 分别属于两页，因此零次读取不可能。

作为逆恒等式的直接后果，若 $N\le M$、$k,h\ge2$，可在精确的定义域 $\mathcal C_{N,k}$ 上置

$$
R_{N,k}^{M,h}=E_{M,h}\circ D_{N,k}:
\mathcal C_{N,k}\longrightarrow E_{M,h}(X_N)\subseteq\mathcal C_{M,h}.
$$

于是 $D_{M,h}R_{N,k}^{M,h}=D_{N,k}$，且重编码保留首位；若 $M\le L$、$j\ge2$，还有

$$
R_{M,h}^{L,j}\circ R_{N,k}^{M,h}=R_{N,k}^{L,j}.
$$

这些式子分别在复合中消去 $D_{M,h}E_{M,h}$ 即得。对任意整数 $q\ge1$ 和部分运算 $T:S\subseteq X_N^q\to X_N$，其运输

$$
\widehat T=E_{N,k}\circ T\circ D_{N,k}^{\times q}
$$

的定义域恰为 $\{\mathbf w\in\mathcal C_{N,k}^q:D_{N,k}^{\times q}(\mathbf w)\in S\}$；消去 $D_{N,k}E_{N,k}$ 得 $D_{N,k}\widehat T=T D_{N,k}^{\times q}$。这只保存整数语义，不给出运算的首位读取算法，也不保证不同窗口的字面前缀相容。证毕。

## 2. 一个精确有限窗口

### 定理 2.1（$N=255$ 的容量与小序号配对）

在 $X_{255}$ 上，$A=202$、$P=54$，且有下表；“无禁串”指普通二进制的相应固定宽度问题。

| 阶数或语言 | $m_0$ | $m_*$ | 最优宽度处 $(C_0,C_1)$ |
|---|---:|---:|---:|
| $k=2$ | 12 | 12 | $(233,144)$ |
| $k=3$ | 9 | 10 | $(274,230)$ |
| $k=4$ | 9 | 9 | $(208,193)$ |
| $k=5$ | 9 | 9 | $(236,228)$ |
| 无禁串 | 8 | 9 | $(256,256)$ |

特别地 $k_{\min}(255)=4$，而 $G_8^{(4)}=208$。对 $k=4$，下表给出四组共同尾码的末三位 $t_r$：

| $r$ | $x_{0,r}$ | $x_{1,r}$ | $t_r=Z_{4,3}(r)$ |
|---:|---:|---:|---|
| 2 | 4 | 5 | $010$ |
| 3 | 6 | 7 | $011$ |
| 4 | 8 | 11 | $100$ |
| 5 | 9 | 13 | $101$ |

在 $N=255$ 的最优九位码中，$Z_{4,8}(r)=0^5t_r$，故各对码字分别是 $0\,0^5t_r$ 与 $1\,0^5t_r$。在 $N=13,k=4$ 的最优四位码中，同四对直接是 $0t_r$ 与 $1t_r$。

**证明。** 不超过 $255$ 的素数逐区间如下：

$$
\begin{aligned}
[2,99]:\;&2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,\\
         &53,59,61,67,71,73,79,83,89,97;\\
[100,149]:\;&101,103,107,109,113,127,131,137,139,149;\\
[150,199]:\;&151,157,163,167,173,179,181,191,193,197,199;\\
[200,255]:\;&211,223,227,229,233,239,241,251.
\end{aligned}
$$

列表的完全性可由有限除法直接确认：若 $2\le n\le255$ 为合数，则最小素因子不超过 $\sqrt{255}<16$，所以在 $2,3,5,7,11,13$ 中。保留这六个素数，并从其余整数中删除被其中任一数整除者，恰得到上述四行；每行分别有 $25,10,11,8$ 个。故 $P=54$、$A=256-54=202$。

按定义 1.2 逐项求和，所需的权重为

$$
\begin{aligned}
k=2:\;&1,2,3,5,8,13,21,34,55,89,144,233,377;\\
k=3:\;&1,2,4,7,13,24,44,81,149,274,504;\\
k=4:\;&1,2,4,8,15,29,56,108,208,401;\\
k=5:\;&1,2,4,8,16,31,61,120,236,464.
\end{aligned}
$$

例如 $G_8^{(4)}=108+56+29+15=208$。对 $k=2$，$233<256\le377$，宽度 $12$ 的两页容量 $(233,144)$ 足够。对 $k=3$，$149<256\le274$，但九位的零页容量 $149<202$，十位的 $(274,230)$ 才足够。对 $k=4,5$，分别有 $208<256\le401$、$236<256\le464$，九位处的两页容量已足够。无禁串时身份需要八位，而两页需要 $1+\lceil\log_2 202\rceil=9$ 位。因 $k=2,3$ 未达到九位而 $k=4$ 达到，最小阶数为四。

前几个非素数为 $0,1,4,6,8,9$，前几个素数为 $2,3,5,7,11,13$；三位权重为 $1,2,4$，故表中尾码的地址分别为 $2,3,4,5$。在高位补五个零保持地址，再用定理 1.3 的唯一性得到九位配对。$X_{13}$ 有六个素数和八个非素数，四位的容量为 $(8,7)$，且三位总容量不足十四，故其最优宽度为四。

此外，九位 $k=4$ 码中，未配对的 $r=54$ 翻首位后仍合法但未分配，而 $r=193$ 翻首位后含禁串：分别代入 $P=54,C_1=193,A=202$ 和定理 1.3 的分类即可。证毕。

## 3. 全体自然数的显式自定界帧

### 定义 3.1（无限两页与长度字段）

把非素数和素数分别递增枚举为 $a_0<a_1<\cdots$ 与 $p_0<p_1<\cdots$，记

$$
B(0,r)=a_r,\qquad B(1,r)=p_r.
$$

两类都无限：$4,6,8,\ldots$ 均为非素数；若素数只有有限个，其乘积加一的最小大于一的因子为素数，却不在原列表，矛盾。故 $B:\{0,1\}\times\mathbb N_0\to\mathbb N_0$ 为双射，且 $\chi(B(b,r))=b$。逐个自然数用有限试除可得到两种枚举及任意给定自然数的页标与序号。

固定 $k\ge2$，定义最短地址长度与其规范正文

$$
\ell_k(r)=\min\{\ell\ge0:r<G_\ell^{(k)}\},\qquad
z_k(r)=Z_{k,\ell_k(r)}(r).
$$

严格增长与无界性保证定义存在。零序号满足 $\ell_k(0)=0$、$z_k(0)=\varepsilon$；当 $r>0$ 时，$\ell=\ell_k(r)$ 等价于

$$
G_{\ell-1}^{(k)}\le r<G_\ell^{(k)},\qquad \ell\ge1.
$$

定义等长替换 $h(0)=00$、$h(1)=01$，并按拼接延拓到所有有限二进制词，$h(\varepsilon)=\varepsilon$。对正整数 $t$ 写通常二进制表示

$$
\operatorname{bin}(t)=1u,\qquad |u|=q=\lfloor\log_2t\rfloor,
$$

置

$$
\gamma(t)=0^q1u,\qquad \eta(t)=0^q1h(u).
$$

$\gamma$ 是经典 Elias gamma 码；书目来源为 Peter Elias, *Universal codeword sets and representations of the integers*, IEEE Transactions on Information Theory 21(2), 194–203 (1975), [DOI:10.1109/TIT.1975.1055349](https://doi.org/10.1109/TIT.1975.1055349)。以下只使用这里明确定义并直接证明的长度与解析性质。

### 定理 3.2（$\eta$ 帧、逆解析与串流）

令 $\ell=\ell_k(r)$，定义

$$
U_k(b,r)=b\,0\,\eta(\ell+1)\,0\,z_k(r).
$$

则 $U_k$ 是从 $\{0,1\}\times\mathbb N_0$ 到 $\mathcal W_*^{(k)}$ 的单射，实际码集前缀自由，首位为 $b$。同序号的两页码字只差第一位。其长度精确为

$$
|U_k(b,r)|=\ell+3\lfloor\log_2(\ell+1)\rfloor+4.
$$

映射 $U_k\circ B^{-1}$ 因而为全体自然数提供首位等于 $\chi$ 的编码，逆映射只定义在实际像上。相对于指定旧帧

$$
V_k(b,r)=b\,0\,h(\gamma(\ell+1))\,0\,z_k(r),
$$

新帧逐词节省 $q+1$ 位，其中 $q=\lfloor\log_2(\ell+1)\rfloor$，因为 $|V_k(b,r)|=\ell+4q+5$。此比较只涉及这两个帧格式。

末尾增加一位零所得 $\widehat U_k(b,r)=U_k(b,r)0$ 仍为前缀自由配对码；任意有限或无限顺序拼接都不含 $1^k$，并可按帧边界唯一解析。

**证明。** 在 $\gamma(t)$ 中，数前导零得 $q$，读到一后再取恰好 $q$ 位，即恢复 $u$ 和 $t$。不同的 $q$ 在较短的前导零段末端已有不同位，相同的 $q$ 对应等长词；故 $\gamma$ 前缀自由，长度为 $2q+1$。

对 $\eta(t)$，同样先数 $q$ 个零并读取一，再读取恰好 $q$ 个二位块，每块必须是 $00$ 或 $01$。逆替换恢复 $u$，所以可恢复 $t$。不同 $q$ 的词不能互为前缀；相同 $q$ 的词长度同为 $3q+1$，也不能为真前缀。标记一后若还有内容，其下一位为零；每块以零开始且块内没有 $11$，所以 $\eta(t)$ 不含 $11$。特别地 $\eta(1)=1$，这包括 $q=0$ 的情形。$h(\gamma(t))$ 也不含 $11$，且因 $h$ 为逐块单射，若两个替换后词存在前缀关系，逆替换就给出两个 $\gamma$ 词的前缀关系；故旧字段亦前缀自由。

在 $U_k$ 中，页标后的零把状态重置为末尾没有一；$\eta$ 字段自身无 $11$，因而对每个 $k\ge2$ 都合法；字段后的零又把状态重置，接上的 $z_k(r)$ 按定义合法。于是所有连接处都不会产生 $1^k$。

精确的逆解析依次检查页标 $b$、第一个重置零，按上述规则解析 $\eta$ 的前导零、标记及二位块，恢复正整数 $t=\ell+1$，再检查第二个重置零并取恰好 $\ell$ 位正文 $z$。须验证 $z\in\mathcal W_\ell^{(k)}$，计算 $r=\operatorname{val}_k(z)$，并验证 $\ell_k(r)=\ell$；在 $\ell=0$ 时这强制 $r=0,z=\varepsilon$，在 $\ell>0$ 时要求 $G_{\ell-1}\le r<G_\ell$。对一个单独的有限词，还要求其恰在正文后结束。于是 $z=Z_{k,\ell}(r)=z_k(r)$，原词确为 $U_k(b,r)$。反之实际像中的词均通过这些条件，故它们恰刻画解码器的定义域，且解码后再编码、编码后再解码均恢复输入。若要恢复原自然数，最后取 $B(b,r)$。

若两个整帧存在前缀关系，则页标必须相同，随后前缀自由的 $\eta$ 字段必须相同。两正文因此等长；继续比较可知正文相同，由区间双射得到相同序号。这证明整帧前缀自由和单射性。页标外的全部内容只依赖 $r$，所以同序号两页的 Hamming 距离为一。

新帧长度为 $1+1+(3q+1)+1+\ell=\ell+3q+4$；旧字段长 $2(2q+1)=4q+2$，故旧帧长度为 $\ell+4q+5$，差为 $q+1$。

若在前缀自由码的每词末尾附加同一个零，新词仍前缀自由：新词间的前缀关系会使原词间存在前缀关系，从而原词相同。终止零不破坏单帧合法性，并切断跨帧的一串连续一。解析完正文后必须再读一个零才开始下一帧；前缀自由性保证每一步边界唯一。在无限拼接中，每帧有限且长度至少五，反复执行这一规则就逐帧恢复整个序列。证毕。

## 4. 约束前缀码的全局冗余判据

### 定义 4.1（配对码与统一长度包络）

固定 $k\ge2$。称单射

$$
F:\{0,1\}\times\mathbb N_0\longrightarrow\mathcal W_*^{(k)}
$$

为配对前缀码，如果其像前缀自由、$F(b,r)$ 的首位是 $b$，且对每个 $r$，$F(0,r)$ 与 $F(1,r)$ 只在首位不同。这里前缀自由指任意两个不同码字均不是真前缀关系；配对特别保证同序号两词等长。

给定实值函数 $g:\mathbb N_0\to\mathbb R$，称该码具有相对于 $g$ 的统一长度包络，如果存在一个有限实常数 $C$，使

$$
\forall b\in\{0,1\}\ \forall r\in\mathbb N_0,\qquad
|F(b,r)|\le\ell_k(r)+g(\ell_k(r))+C.
$$

“最终统一包络”指同一个 $C$ 对所有 $\ell_k(r)\ge L$ 的两页序号成立，其中 $L$ 固定。若每个序号可另取常数，则只是逐点界，不能替代这里的统一包络。

### 定理 4.2（任意实值冗余函数的充要条件）

设 $g:\mathbb N_0\to\mathbb R$。存在满足定义 4.1 的统一长度包络的配对前缀码，当且仅当

$$
\sum_{\ell\ge2}\lambda^{-g(\ell)}<\infty,
\qquad
\sum_{h=1}^k\lambda^{-h}=1,\quad 1<\lambda<2.
$$

根 $\lambda=\lambda_k$ 唯一。对任何具有包络常数 $C$ 的这样的码，必要性还给出

$$
\sum_{\ell\ge2}\lambda^{-g(\ell)}\le\frac{\lambda^{C+3}}{2}.
$$

如果包络仅要求在一个指定页上成立，则相同论证给出该和不超过 $\lambda^{C+3}$。若只要求最终统一包络，则相应尾和收敛，因有限个初始值不影响收敛性，存在性的充要条件不变。

当级数收敛时，置

$$
S=\sum_{\ell\ge0}\lambda^{-g(\ell)}\in(0,\infty).
$$

存在满足

$$
|F(b,r)|\le\ell_k(r)+g(\ell_k(r))+\log_\lambda(2S)+4
$$

的配对前缀码。每词再添终止零可得到安全拼接的同类码，包络常数只增加一；因此要求任意顺序拼接仍无 $1^k$ 时，存在性的充要条件也不变。这是任意实值 $g$ 下的存在性命题，不要求从任意实数数据统一计算编码器或解码器。

**证明。** 函数 $f(x)=\sum_{h=1}^kx^{-h}$ 在 $[1,2]$ 上连续且严格递减，$f(1)=k>1$、$f(2)=1-2^{-k}<1$，所以唯一根存在于 $(1,2)$。以下采用 [《递归关系观察与有效分辨率》](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md) 第 1.4.8 节固定初态零的柱权计算，并在此写出所需的守恒步骤；它不要求移位平稳的 Parry 初始分布。

对合法词 $w$，令 $s(w)\in\{0,\ldots,k-1\}$ 为末尾连续一的个数，$s(\varepsilon)=0$。置

$$
v_s=\sum_{h=1}^{k-s}\lambda^{-h},\qquad
v_0=1,\quad \min_s v_s=v_{k-1}=\lambda^{-1},\quad
\mu(w)=\lambda^{-|w|}v_{s(w)}.
$$

直接移项得

$$
\lambda v_s=
\begin{cases}
1+v_{s+1},&0\le s<k-1,\\
1,&s=k-1.
\end{cases}
$$

所以当 $s<k-1$ 时，$w$ 的两个合法孩子 $w0,w1$ 的质量之和为 $\mu(w)$；当 $s=k-1$ 时，唯一合法孩子 $w0$ 的质量就等于 $\mu(w)$。根的质量为一，反复展开得到每个完整深度的总质量为一。

空反链的质量和为零。对非空有限前缀反链 $Q\subseteq\mathcal W_*^{(k)}$，把每个词展开到一个共同深度 $n\ge\max_{w\in Q}|w|$。质量守恒，而反链的后继集合互不相交，故 $\sum_{w\in Q}\mu(w)\le1$。任意可数前缀反链的每个有限子集都满足此式，取非负级数的有限部分和上确界便得

$$
\sum_{w\in Q}\mu(w)\le1,\qquad
\sum_{w\in Q}\lambda^{-|w|}\le\lambda.
$$

第二个界使用 $v_s\ge\lambda^{-1}$；无权和的右端是 $\lambda$，不是一。对完整深度 $m$，每项质量介于 $\lambda^{-m-1}$ 与 $\lambda^{-m}$，且词数为 $G_m$，因此

$$
G_m\lambda^{-m-1}\le1\le G_m\lambda^{-m},
\qquad \lambda^m\le G_m\le\lambda^{m+1}.
$$

接着证明必要性。令 $d_\ell$ 为最短地址长度恰为 $\ell$ 的序号数量。严格增长与定义给出

$$
d_0=1,\qquad d_\ell=G_\ell-G_{\ell-1}\quad(\ell\ge1).
$$

定理 1.3 证明中的 $10v$ 计数及上面的增长下界说明，对 $\ell\ge2$，

$$
d_\ell\ge G_{\ell-2}\ge\lambda^{\ell-2}.
$$

若两页全部序号满足包络，则利用单射性使所有码字各计一次，并把反链不等式用于码的实际像，得到

$$
\begin{aligned}
\lambda
&\ge\sum_{b\in\{0,1\}}\sum_{r\ge0}\lambda^{-|F(b,r)|}\\
&\ge2\sum_{\ell\ge2}d_\ell\lambda^{-\ell-g(\ell)-C}\\
&\ge2\lambda^{-C-2}\sum_{\ell\ge2}\lambda^{-g(\ell)}.
\end{aligned}
$$

所有无限和的比较都可先在有限层集合上进行，再取上确界，故不预设收敛。整理即得必要界。只取一个页会去掉系数二；只在 $\ell\ge L$ 假设包络则得到从 $\max\{2,L\}$ 开始的相同尾和界。这一步需要一个常数同时控制该范围内的全部序号，不能由各点独立的有限长度推出。

充分性使用区间中点方法，其经典二进制形式见 Gilbert 与 Moore, *Variable-Length Binary Encodings*, Bell System Technical Journal 38(4), 933–967 (1959), §III Theorem 1, pp. 938–939，[DOI:10.1002/j.1538-7305.1959.tb01583.x](https://doi.org/10.1002/j.1538-7305.1959.tb01583.x)。以下直接构造可数输入和禁串树上的版本。

由于 $g(0),g(1)$ 为有限实数，$S$ 有限且严格正。置

$$
p_\ell=\frac{\lambda^{-g(\ell)}}{S},\qquad
q_\ell=\sum_{j<\ell}p_j,\qquad
J_\ell=[q_\ell,q_\ell+p_\ell).
$$

这些相邻的半开区间互不相交，总长为一，并覆盖 $[0,1)$：对任意 $x<1$，部分和最终超过 $x$，所以 $x$ 属于某个区间。

独立于这份源划分，实现一棵带区间的合法词树。令 $I(\varepsilon)=[0,1)$；若 $I(w)$ 已定义，就按位序把它分成合法孩子的相邻半开区间 $I(w0)$、$I(w1)$，各自长度为 $\mu(w0)$、$\mu(w1)$。在状态 $k-1$ 只有零孩子，置 $I(w0)=I(w)$。质量守恒保证此定义成立。因此每个深度的区间构成 $[0,1)$ 的有限划分，$|I(w)|=\mu(w)$；词的前缀关系蕴含区间包含。强制零边可能保留整个父区间，但不会破坏任何这些性质。

对每个 $\ell$，取

$$
n_\ell=\left\lceil\log_\lambda\frac{2}{p_\ell}\right\rceil,
\qquad c_\ell=q_\ell+\frac{p_\ell}{2}.
$$

深度 $n_\ell$ 的每个区间长度至多 $\lambda^{-n_\ell}\le p_\ell/2$。令 $I(H(\ell))$ 为此深度唯一包含 $c_\ell$ 的区间。若该区间为 $[a,a+L)$，则 $a\le c_\ell<a+L$ 且 $L\le p_\ell/2$，于是

$$
a\ge c_\ell-L\ge q_\ell,\qquad
a+L\le c_\ell+L\le q_\ell+p_\ell.
$$

故 $I(H(\ell))\subseteq J_\ell$。不同 $\ell$ 的所选区间互不相交且长度正；若某个所选标签是另一个的前缀，相应区间便会包含而相交，矛盾。因此所有 $H(\ell)$ 是互异且前缀自由的合法词，即使它们来自不同深度、树中含强制零边也是如此。其长度满足

$$
|H(\ell)|=n_\ell
\le\log_\lambda\frac{2}{p_\ell}+1
=g(\ell)+\log_\lambda(2S)+1.
$$

现在定义

$$
F(b,r)=b\,0\,H(\ell_k(r))\,0\,z_k(r).
$$

页标后的零让 $H$ 从状态零开始，$H$ 后的零让正文从状态零开始，所以整个词合法。前缀自由的头字段唯一识别 $\ell$，正文恰取 $\ell$ 位，其规范条件为 $\ell_k(\operatorname{val}_k(z))=\ell$。同一 $\ell$ 的不同序号由区间双射区分；不同 $\ell$ 由头字段区分。若两个整帧有前缀关系，则先有相同页标，再有相同头字段，最后有相同长度的正文，因而整帧相同。这证明单射性与前缀自由性。页标外的尾部只依赖 $r$，故配对条件成立。

该码在实际像上的逆映射取出 $b$、由所选头字段确定 $\ell$、由正文恢复 $r$。这个数学逆映射存在，不意味着对任意实值 $g$ 都有统一有效的头字段识别或生成程序。实际像外的合法词不另行赋予语义。长度由

$$
|F(b,r)|=\ell_k(r)+|H(\ell_k(r))|+3
\le\ell_k(r)+g(\ell_k(r))+\log_\lambda(2S)+4
$$

给出。有限个初始层只含有限个序号，故最终统一包络可扩大常数而延伸至全部序号。

最后，在这些码字末尾添加零，合法性、配对性、前缀自由性和跨边界的唯一解析与定理 3.2 的终止零论证相同：先按头字段与正文长度确定原帧，再读终止零；该零切断跨帧禁串。长度只加一。反向的必要性已对所有配对前缀码成立，当然也对安全拼接的子类成立，故充要条件不变。证毕。

### 定理 4.3（统一包络的临界级数）

对任何配对前缀码 $F$ 和任何有限实常数 $C$，都有无穷多个序号 $r$ 满足

$$
|F(0,r)|-\ell_k(r)=|F(1,r)|-\ell_k(r)>C.
$$

因此不存在最终对全部序号成立的常数冗余上界。

给定实数 $\alpha$，若对 $\ell\ge2$ 有

$$
g(\ell)=\alpha\log_\lambda\ell+O(1),
$$

且有限个初始值均为有限实数，则相对于此 $g$ 的统一长度包络存在，当且仅当 $\alpha>1$。更精细地，给定实数 $\alpha,\beta$，若对 $\ell\ge3$ 有

$$
g(\ell)=\alpha\log_\lambda\ell
       +\beta\log_\lambda(\log\ell)+O(1),
$$

其中 $\log$ 表示自然对数，$O(1)$ 表示随 $\ell$ 一致有界的实误差，则统一长度包络存在当且仅当

$$
\alpha>1\quad\text{或}\quad(\alpha=1\ \text{且}\ \beta>1).
$$

这些结论也适用于最终统一包络及带终止零的安全拼接码。

**证明。** 若对某个 $C$ 只有有限个序号超出常数冗余界，则除去它们所处的有限个层后，两页所有序号都满足最终包络 $g=0$。定理 4.2 将要求 $\sum_{\ell\ge L}1$ 收敛，矛盾。配对条件使同序号两页等长，故无穷多个超界序号在两页同时出现。

一致有界的加性误差在 $\lambda^{-g(\ell)}$ 中只产生上下有界的正乘因子。因此第一种包络的级数与 $\sum\ell^{-\alpha}$ 同敛散。若 $\alpha\le0$，其项不趋于零；若 $\alpha>0$，与 $\int_1^\infty x^{-\alpha}\,dx$ 作上下和比较，积分恰在 $\alpha>1$ 时有限。这证明第一项判据。

第二种包络的级数与

$$
\sum_{\ell\ge3}\ell^{-\alpha}(\log\ell)^{-\beta}
$$

同敛散。对任意 $\epsilon>0$，由 $\log\log x/\log x\to0$，充分大的 $x$ 满足

$$
x^{-\epsilon}\le(\log x)^{-\beta}\le x^\epsilon.
$$

这里所用极限可令 $y=\log x$，再用 $\log y/y\to0$ 得到。若 $\alpha>1$，取 $\epsilon=(\alpha-1)/2$，级数被指数大于一的幂级数从上控制；若 $\alpha<1$，取 $\epsilon=(1-\alpha)/2$，级数从下控制一个指数小于一的发散幂级数。当 $\alpha=1$ 时，函数 $1/[x(\log x)^\beta]$ 最终递减，积分代换 $u=\log x$ 给出

$$
\int_3^\infty\frac{dx}{x(\log x)^\beta}
=\int_{\log3}^\infty\frac{du}{u^\beta},
$$

恰在 $\beta>1$ 时有限。积分与级数的上下和比较遂给出剩余边界。代入定理 4.2 即得全部存在性结论；有限初始项、最终包络以及固定终止位不改变判据。证毕。

## 5. 可计算嵌套字段与一阶最优性

### 定义 5.1（用规范地址编码长度）

对正整数 $t$，置 $d=\ell_k(t-1)$，定义

$$
H_k(t)=\eta(d+1)\,0\,z_k(t-1).
$$

这里 $H_k$ 是明确的整数编码，与定理 4.2 按实区间选择的 $H(\ell)$ 不同。对 $r\in\mathbb N_0$，令 $\ell=\ell_k(r)$，再定义

$$
F_k(b,r)=b\,0\,H_k(\ell+1)\,0\,z_k(r),\qquad
\widehat F_k(b,r)=F_k(b,r)0.
$$

### 定理 5.2（嵌套帧的精确长度与逆映射）

$H_k$ 在正整数上是合法、单射、前缀自由的编码，且

$$
|H_k(t)|=d+3\lfloor\log_2(d+1)\rfloor+2,
\qquad d=\ell_k(t-1).
$$

$F_k$ 是可计算的配对前缀码。若 $\ell=\ell_k(r)$、$d=\ell_k(\ell)$，则

$$
|F_k(b,r)|=\ell+d+3\lfloor\log_2(d+1)\rfloor+5.
$$

它通过 $B(b,r)$ 恢复原自然数，编码 $F_k\circ B^{-1}$ 的首位为 $\chi$。编码与逆解析均只使用有限整数运算；逆映射的语义域是实际像。每词末尾加零后仍前缀自由，任意有限或无限拼接都合法，并能逐帧恢复原自然数序列。

对 $r\ge1$，有

$$
\log_\lambda r-1<\ell_k(r)\le\log_\lambda r+1.
$$

因此当 $\ell\to\infty$ 时，嵌套帧的冗余满足

$$
|F_k(b,r)|-\ell
=\log_\lambda\ell+O_k(\log\log\ell),
\qquad \ell=\ell_k(r).
$$

对每个固定 $k$，它在充分大的 $\ell$ 上严格短于定理 3.2 的 $\eta$ 帧；但在 $\ell=0$ 时，新帧长五而 $\eta$ 帧长四，所以没有逐序号支配关系。

**证明。** $H_k$ 的 $\eta$ 字段不含 $11$，其后零把状态重置，随后规范正文合法，故 $H_k(t)$ 合法。解析时先从 $\eta(d+1)$ 恢复 $d$，检查零，再读取 $d$ 位正文 $z$；检查正文合法并满足 $\ell_k(\operatorname{val}_k(z))=d$，恢复

$$
t=\operatorname{val}_k(z)+1.
$$

若 $d=0$，正文必须为空，得 $t=1$，且 $H_k(1)=10$。若 $d>0$，规范检查给出 $G_{d-1}\le t-1<G_d$。这些条件既为所有实际头字段满足，也反过来强制词为 $H_k(t)$。两个头字段若有前缀关系，前面的 $\eta$ 字段必相同，从而 $d$ 相同；随后等长正文必须相同，故 $t$ 相同。这证明单射性与前缀自由性。字段长度为 $(3\lfloor\log_2(d+1)\rfloor+1)+1+d$。

整帧 $F_k$ 的第一个零隔开页标与头字段，第二个零隔开头字段与正文，因此两次连接都从状态零开始。解析先读取页标和第一个零，再按上述有限步骤解出 $H_k$ 的正整数值 $t$，置 $\ell=t-1$；检查第二个零后读取恰好 $\ell$ 位正文 $z$，检查合法性及 $\ell_k(\operatorname{val}_k(z))=\ell$，最后得 $r=\operatorname{val}_k(z)$。单独词须在此结束，原自然数为 $B(b,r)$。逆向代入所有字段的定义可重建原词，故条件恰刻画实际像，两个方向的复合都是相应域上的恒等映射。

这一过程可计算：$G_j$ 由整数递推生成，严格增长使每个长度搜索在有限步结束；$Z_{k,m}$ 可按定理 1.3 的相邻区间递归求出，$\eta$ 只需二进制展开与固定替换。头字段自身也只包含有限次同类运算；页内自然数的枚举按定义 3.1 的试除在每个指定序号上终止。这些事实说明有效性，不把运算成本算作一位读取。

若两个整帧有前缀关系，页标相同，前缀自由的 $H_k$ 字段相同，因而正文长度相同，最终正文也相同。故整帧前缀自由。所有页标以外的字段均只依赖 $r$，证明配对及 Hamming 距离一。长度把头字段的公式代入 $1+1+|H_k(\ell+1)|+1+\ell$ 即得。对末尾附零的词，先完成上述解析再检查终止零；原码前缀自由保证新码仍前缀自由，终止零切断跨帧连续一，所以任意拼接合法且边界唯一。

若 $r\ge1$，令 $\ell=\ell_k(r)\ge1$。用定理 4.2 证明中的完整层界，得到

$$
\lambda^{\ell-1}\le G_{\ell-1}\le r<G_\ell\le\lambda^{\ell+1}.
$$

取对数正好给出所称的严格下界和非严格上界。再对整数 $\ell\ge1$ 应用同式，得

$$
\log_\lambda\ell-1<d\le\log_\lambda\ell+1,
\qquad d=\ell_k(\ell).
$$

因此 $d=\log_\lambda\ell+O(1)$，而 $\log_2(d+1)=O_k(\log\log\ell)$，代入精确长度公式即得冗余估计。

为比较两个显式帧，令 $\varphi=(1+\sqrt5)/2$。因为 $\varphi^{-1}+\varphi^{-2}=1$，对每个 $k\ge2$ 有 $\sum_{h=1}^k\varphi^{-h}\ge1$。根方程左侧严格递减，故 $\lambda_k\ge\varphi$。又 $\varphi>3/2$ 且 $(3/2)^3>2$，所以

$$
\frac1{\log_2\lambda_k}\le\frac1{\log_2\varphi}<3.
$$

嵌套帧冗余为 $(1/\log_2\lambda_k)\log_2\ell+O_k(\log\log\ell)$，$\eta$ 帧冗余为 $3\log_2\ell+O(1)$。后者减前者趋于正无穷，故充分大时前者严格较短。在 $\ell=0$，有 $d=0,z_k(0)=\varepsilon$、$H_k(1)=10$，从而 $F_k(b,0)=b0100$ 长五，而 $U_k(b,0)=b010$ 长四，证明小序号处的反向比较。证毕。

### 定理 5.3（全体配对前缀码的一阶冗余最优值）

对任一配对前缀码 $F$，定义每层最大冗余

$$
R_F(j)=\max\{|F(b,r)|-j:
 b\in\{0,1\},\ \ell_k(r)=j\}\qquad(j\ge2),
$$

并在扩充实数中定义

$$
L(F)=\limsup_{j\to\infty}\frac{R_F(j)}{\log_\lambda j}.
$$

则

$$
\inf_F L(F)=1,
$$

其中下确界遍历定义 4.1 的全部配对前缀码；定理 5.2 的 $F_k$ 达到该值。若把代码限制为任意顺序拼接都合法的配对前缀码，结论仍为一，由 $\widehat F_k$ 达到。

**证明。** 对每个 $j\ge2$，具有最短长度 $j$ 的序号有 $d_j=G_j-G_{j-1}\ge G_{j-2}>0$ 个，故最大值是非空有限集合上的有限数，扩充实数上极限有定义。

若某码 $F$ 满足 $L(F)<1$，可取有限实数 $a<1$ 且 $L(F)<a$；即使 $L(F)=-\infty$ 也能如此选取。上极限的定义给出一个 $J$，使所有 $j\ge J$ 都有 $R_F(j)\le a\log_\lambda j$。这就是同一系数对两页每层全部序号成立的最终统一包络。定理 4.2 的必要性要求 $\sum_{j\ge J}j^{-a}<\infty$，而 $a<1$ 时该级数发散，矛盾。因此每个这样的码都有 $L(F)\ge1$。

对显式 $F_k$，同一层的长度公式只依赖 $j$，定理 5.2 给出

$$
R_{F_k}(j)=\log_\lambda j+O_k(\log\log j).
$$

因为 $\log\log j/\log_\lambda j\to0$，有 $L(F_k)=1$。末尾添加零只把每层最大冗余增加一，不改变上述极限，故 $L(\widehat F_k)=1$。安全拼接码属于同一个必要性范围，所以下界也适用。这证明一阶系数的精确最优性，不断言常数项或更低阶项最优。证毕。

## 追加锚（本行以下为增补区）

## 6. 双页区域编码的精确容量与信息面积

### 定义 6.1（全矩阵隐藏合同）

固定 $N\ge2$、$k\ge2$，沿用定义 1.1 的 $x_{b,r}$、$M_0=A_N$、$M_1=P_N$。逻辑空间及其页投影为

$$
\mathcal H_L=\bigoplus_{b=0}^1\mathbb C^{M_b},\qquad
|b,r\rangle=|x_{b,r}\rangle,\qquad
\Pi_b=\sum_{r=0}^{M_b-1}|b,r\rangle\langle b,r|.
$$

取 $m_X,m_Y\ge1$。物理空间是环境 qubit 张量积

$$
\mathcal H_X=(\mathbb C^2)^{\otimes m_X},\qquad
\mathcal H_Y=(\mathbb C^2)^{\otimes m_Y}.
$$

其中 $\mathcal H_{X,b}$ 是所有首位为 $b$ 的合法长度 $m_X$ 词的计算基张成空间，投影为 $Q_{X,b}$，维数为 $c_{X,b}=C_b(k,m_X)$；$\mathcal H_{Y,b}$、$Q_{Y,b}$、$c_{Y,b}=C_b(k,m_Y)$ 同理。合法词空间本身不假定具有逐位张量分解。

区域编码是等距映射 $J:\mathcal H_L\to\mathcal H_X\otimes\mathcal H_Y$，满足

$$
(Q_{X,b}\otimes I)J=J\Pi_b=(I\otimes Q_{Y,b})J
$$

以及对每个 $A\in\operatorname{End}(\mathcal H_L)$ 成立的精确通道恒等式

$$
\mathcal N_X(A):=\operatorname{Tr}_Y(JAJ^\dagger)
=\bigoplus_{b=0}^1\operatorname{Tr}(\Pi_bA)\,\sigma_b,
\tag{6.1}
$$

其中 $\sigma_b$ 是支撑在 $\mathcal H_{X,b}$ 上、与 $A$ 无关的密度算符。右侧直和按两个正交页嵌入 $\mathcal H_X$，未使用的空间上取零。合同保留页标而完全隐藏页内逻辑矩阵；只验证计算基输入不足以保证式（6.1）。等价地，可以对全部密度矩阵要求它，再用任意 Hermitian 矩阵的正负部分及复线性分解延拓到全部矩阵。

以下熵统一使用自然对数：$S(\rho)=-\operatorname{Tr}(\rho\log\rho)$、$H(q)=-\sum_iq_i\log q_i$，并约定 $0\log0=0$。这里 $J$ 表示新的区域等距，与定理 1.3 只在配对词上定义的首位翻转映射不同。

### 定理 6.2（指定谱的可行性与双页同时最优值）

对指定的 $\sigma_b$，置 $d_b=\operatorname{rank}\sigma_b$。定义 6.1 的合同可行，当且仅当每页满足

$$
d_b\le c_{X,b},\qquad M_bd_b\le c_{Y,b}.
\tag{6.2}
$$

若允许选择 $\sigma_b$，则合同可行当且仅当

$$
D_b:=\min\left(c_{X,b},\left\lfloor\frac{c_{Y,b}}{M_b}\right\rfloor\right)\ge1
\qquad(b=0,1).
\tag{6.3}
$$

在可行情形，每页的最大辅助熵为 $\log D_b$，两个最大值可以在同一个 $J$ 中同时达到。

**证明。** 固定一页，暂略下标 $b$，把指定态写成

$$
\sigma=\sum_{j=0}^{d-1}\lambda_j|e_j\rangle\langle e_j|,
\qquad \lambda_j>0,\qquad \sum_j\lambda_j=1.
$$

对每个 $r$，式（6.1）的对角矩阵单位说明 $J|b,r\rangle$ 是 $\sigma$ 的纯化。它在 $\ker\sigma$ 方向的分量范数为零，故可写为

$$
J|b,r\rangle=\sum_{j=0}^{d-1}\sqrt{\lambda_j}\,|e_j\rangle|v_{rj}\rangle,
\qquad |v_{rj}\rangle\in\mathcal H_{Y,b}.
\tag{6.4}
$$

把所有矩阵单位 $|b,r\rangle\langle b,s|$ 代入式（6.1），并逐个比较 $|e_j\rangle\langle e_l|$ 的系数，得到

$$
\sqrt{\lambda_j\lambda_l}\,\langle v_{sl}|v_{rj}\rangle
=\delta_{rs}\delta_{jl}\lambda_j,
\qquad
\langle v_{sl}|v_{rj}\rangle=\delta_{rs}\delta_{lj}.
\tag{6.5}
$$

所以 $Md$ 个 $Y$ 向量两两正交，必须有 $Md\le c_Y$；$d\le c_X$ 则来自 $\sigma$ 的支撑。反之，在对应 $Y$ 页任选 $Md$ 个正交向量，使用指定的谱和特征基按式（6.4）定义编码。式（6.5）给出等距和页内通道恒等式；不同页的 $Y$ 支撑正交，跨页矩阵单位的 $X$ 偏迹为零。两页一起满足整个合同。

这正是 Braunstein–Pati 的 no-hiding 机制在每个页内的应用，参见 *Quantum information cannot be completely hidden in correlations: implications for the black-hole information paradox*, [arXiv:gr-qc/0603046](https://arxiv.org/abs/gr-qc/0603046)，式（2）—（4）。这里用它计算受合法词页容量限制的精确维数，不将一般 no-hiding 结论另作新机制。

由式（6.2），可选秩恰为 $1\le d_b\le D_b$。对任意正谱，用对数的凹性得

$$
H(\lambda)=\sum_j\lambda_j\log\frac1{\lambda_j}
\le\log\left(\sum_j\lambda_j\frac1{\lambda_j}\right)=\log d_b.
$$

在 $d_b=D_b$ 上取均匀谱即达到 $\log D_b$。不同页的选择互不占用对方空间，故可同时达到。证毕。

### 推论 6.3（规范地址实现与原整数码的重编码）

假设 $D_0,D_1\ge1$。令

$$
\begin{aligned}
X(b,j)&=Z_{k,m_X}(bG_{m_X-1}+j),\\
Y(b,r,j)&=Z_{k,m_Y}(bG_{m_Y-1}+rD_b+j),\\
J|b,r\rangle&=\frac1{\sqrt{D_b}}\sum_{j=0}^{D_b-1}
|X(b,j)\rangle|Y(b,r,j)\rangle.
\end{aligned}
\tag{6.6}
$$

这给出同时最优的区域编码。它使用同一页标和页内序号数据构造新的物理码，原数语义仍为 $x_{b,r}$。对定理 1.3 在任一可行宽度给出的原编码 $E$，在其承诺码空间上存在重编码等距

$$
V:\operatorname{span}\{|E(x_{b,r})\rangle\}\longrightarrow J\mathcal H_L,
\qquad V|E(x_{b,r})\rangle=J|b,r\rangle.
\tag{6.7}
$$

这不是将原 $E$ 的首位／尾部划分改名。在式（6.6）的实际 $Y$ 支撑上，若测得词地址 $t$，则

$$
r=\left\lfloor\frac{t-bG_{m_Y-1}}{D_b}\right\rfloor,
\qquad j=t-bG_{m_Y-1}-rD_b.
$$

**证明。** 两个地址分别落在定理 1.3 的对应页区间内，因为 $D_b\le c_{X,b}$、$M_bD_b\le c_{Y,b}$。$X$ 标签在每页内互异，$Y$ 标签在全部 $(b,r,j)$ 上互异，故式（6.6）是定理 6.2 的均匀构造。原承诺码基和新码基均正交归一，按基定义的 $V$ 因而等距。商与余数公式直接恢复地址的两项；实际支撑外不赋予新的整数语义。这些是精确有限编码和解码关系，不给出门复杂度、素数生成或素数枚举的复杂度界。证毕。

### 定理 6.4（互补通道、最大恢复代数与面积算符）

对任一定义 6.1 的编码，沿用式（6.4）的页内谱，记 $\Lambda_b=\operatorname{diag}(\lambda_{b,0},\ldots,\lambda_{b,d_b-1})$。存在与输入无关的 $Y$ 支撑等距

$$
W:\bigoplus_b(\mathbb C^{M_b}\otimes\mathbb C^{d_b})\longrightarrow\mathcal H_Y,
\qquad W|b,r,j\rangle=|v_{b,rj}\rangle.
$$

对每个逻辑矩阵 $A$，置 $A_{bb}=\Pi_bA\Pi_b$，按页内基视为 $M_b$ 阶矩阵，则两个通道为

$$
\mathcal N_X(A)=\bigoplus_b\operatorname{Tr}(A_{bb})\sigma_b,
\qquad
\mathcal N_Y(A):=\operatorname{Tr}_X(JAJ^\dagger)
=W\left[\bigoplus_b A_{bb}\otimes\Lambda_b\right]W^\dagger.
\tag{6.8}
$$

对密度矩阵 $\rho$，令 $p_b=\operatorname{Tr}\rho_{bb}$；只在 $p_b>0$ 时定义 $\rho_b=\rho_{bb}/p_b$，所有零权项省略。则

$$
\begin{aligned}
S(\rho_X)&=H(p)+\sum_b p_bS(\sigma_b),\\
S(\rho_Y)&=H(p)+\sum_b p_bS(\rho_b)+\sum_b p_bS(\sigma_b).
\end{aligned}
\tag{6.9}
$$

两侧最大精确可恢复逻辑代数分别为

$$
\mathcal Z=\bigoplus_b\mathbb C I_{M_b},\qquad
\mathcal Z'=\bigoplus_b\operatorname{Mat}_{M_b}(\mathbb C),
\tag{6.10}
$$

其中撇号确为在 $\operatorname{End}(\mathcal H_L)$ 中的交换子代数。采用分块代数熵

$$
S_{\mathcal Z}(\rho)=H(p),\qquad
S_{\mathcal Z'}(\rho)=H(p)+\sum_b p_bS(\rho_b),
$$

式（6.9）具有共同中心面积项

$$
\mathcal L=\bigoplus_bS(\sigma_b)I_{M_b},\qquad
S(\rho_X)=S_{\mathcal Z}(\rho)+\operatorname{Tr}(\rho\mathcal L),\qquad
S(\rho_Y)=S_{\mathcal Z'}(\rho)+\operatorname{Tr}(\rho\mathcal L).
\tag{6.11}
$$

只有均匀最优选择才使相应特征值等于 $\log D_b$；一般谱必须使用 $S(\sigma_b)$。

**证明。** 页内偏迹用式（6.5）和 $e_{b,j}$ 的正交性直接得到式（6.8）。跨页项在两个偏迹中均为零，因为两侧的页支撑都正交。固定坐标 $W$ 由 $J$ 和所选特征基确定，未随 $\rho$ 改变。每个正权块的 $X$ 特征值为 $p_b\lambda_{b,j}$，$Y$ 特征值为 $p_b\nu_{b,r}\lambda_{b,j}$，其中 $\nu_{b,r}$ 是 $\rho_b$ 的谱。展开 $-\sum t\log t$ 即得式（6.9）。正的 $\rho_{bb}$ 在迹为零时必为零，故零权项确可省略。

精确恢复取如下含义：逻辑算符 $O$ 及 $O^\dagger$ 都有区域代表，在码空间上分别满足 $(O_X\otimes I)J=JO$ 及其伴随版本，或相应的 $Y$ 版本。对 $z=\bigoplus_bz_bI_{M_b}$，取 $z_X=\sum_bz_bQ_{X,b}$；对 $T=\bigoplus_bT_b$，取

$$
T_Y=W\left[\bigoplus_b(T_b\otimes I_{d_b})\right]W^\dagger.
\tag{6.12}
$$

未使用支撑上可置零。把它们作用到式（6.4），分别得到 $Jz$、$JT$，对伴随同样成立。

为证明最大性，通道伴随就是局部算符压缩：$\mathcal N_X^\dagger(R)=J^\dagger(R\otimes I)J$。由式（6.8），

$$
\mathcal N_X^\dagger(R)=\bigoplus_b\operatorname{Tr}(\sigma_bR)I_{M_b},
\qquad
\operatorname{ran}\mathcal N_X^\dagger=\mathcal Z.
$$

同式说明 $\mathcal N_Y^\dagger$ 的像没有跨页矩阵元，而式（6.12）实现任意页内矩阵，所以 $\operatorname{ran}\mathcal N_Y^\dagger=\mathcal Z'$。任何精确区域代表经压缩必在对应像内，故不存在更大的可恢复代数。两代数互为交换子，且共享中心 $\mathcal Z$。跨页相干由全局等距 $J$ 保存，只是不出现在任一单侧边缘态中。

式（6.11）采用已知的算子代数互补恢复机制：D. Harlow, *The Ryu–Takayanagi Formula from Quantum Error Correction*, [arXiv:1607.03901](https://arxiv.org/abs/1607.03901)，定理 5.1、式（5.22）、（5.24）—（5.28）；仓内对应的固定辅助纠缠构造见 [《算术全息 RT》](ARITHMETIC_HOLOGRAPHIC_RT.md) 第 18 节。此处的具体内容是双页合法地址下的精确实现及容量，而不是另行认领一般熵分解。

最后，插入固定零位的映射 $|x\rangle|y\rangle\mapsto|x0y\rangle$ 将整个乘积合法支撑送进长度 $m_X+m_Y+1$ 的合法词空间：零切断跨界的连续一。把该纯零位归入任一侧，只是局部添加固定纯态，两个熵均不变。证毕。

### 推论 6.5（柱权给出的地址分辨率界）

令 $\lambda=\lambda_k\in(1,2)$ 为定理 4.2 的根，置

$$
a_0=\lambda^{-1},\qquad a_1=\frac{\lambda-1}{\lambda}.
$$

对 $m\ge1$，有

$$
a_b\lambda^m\le C_b(k,m)\le a_b\lambda^{m+1}.
\tag{6.13}
$$

因此，若

$$
T_b=a_b\min\left(\lambda^{m_X},\frac{\lambda^{m_Y}}{M_b}\right),
$$

则

$$
\lfloor T_b\rfloor\le D_b\le\lfloor\lambda T_b\rfloor.
\tag{6.14}
$$

在 $T_b\ge2$ 时特别有

$$
\log T_b-\log2\le\log D_b\le\log T_b+\log\lambda.
\tag{6.15}
$$

**证明。** 定理 4.2 的固定根柱权为 $\mu(w)=\lambda^{-|w|}v_{s(w)}$，其中 $\lambda^{-1}\le v_s\le1$。首位零的质量是 $\mu(0)=\lambda^{-1}$；由 $\lambda v_0=1+v_1$、$v_0=1$，首位一的质量是 $\mu(1)=\lambda^{-1}v_1=(\lambda-1)/\lambda$。各页在深度 $m$ 的总柱权仍为 $a_b$，每个词的质量介于 $\lambda^{-m-1}$ 和 $\lambda^{-m}$，所以

$$
C_b(k,m)\lambda^{-m-1}\le a_b\le C_b(k,m)\lambda^{-m},
$$

即式（6.13）。又因 $c_{X,b}$ 是整数，

$$
D_b=\left\lfloor\min\left(c_{X,b},\frac{c_{Y,b}}{M_b}\right)\right\rfloor,
$$

代入两侧的柱权界即得式（6.14）。当 $T_b\ge2$ 时，$\lfloor T_b\rfloor\ge T_b/2$，上界又不超过 $\lambda T_b$，取自然对数即得式（6.15）。证毕。

这里 $a_b$ 是合法词树的固定柱权，与逻辑输入决定的 $p_b$ 不同。这些长度和熵界计量地址分辨率及编码信息面积，不定义时钟、径向度量或真实视界面积。

## 7. 无分隔位直接拼接的联合支撑最优值

### 定义 7.1（共同合法支撑与接口计数）

在定义 6.1 的全部合同之外，要求 $J\mathcal H_L$ 的计算基支撑只含满足 $xy\in\mathcal W_{m_X+m_Y}^{(k)}$ 的 $|x\rangle|y\rangle$，即所有非法拼接的振幅对每个逻辑输入都为零。这里不插入重置位。

首位零页的 $y$ 以零开始，故两段各自合法就保证拼接合法。首位一页则固定记

$$
M=M_1,\qquad c=C_1(k,m_X),\qquad
x_s=\#\{w\in\mathcal W_{m_X}^{(k)}:w\text{ 以 }1\text{ 开头},\ s(w)=s\},
\qquad a_s=\sum_{u<s}x_u
\quad(0\le s<k).
$$

这里 $s(w)$ 是末尾连续一的长度。为避免混淆，本节的 $a_s$ 是整数行数，不是推论 6.5 的柱权。令 $B_s$ 为首位一的合法长度 $m_Y$ 词中、开头连续一长度严格小于 $k-s$ 的词集，置

$$
n_s=|B_s|,\qquad B_0\supseteq B_1\supseteq\cdots\supseteq B_{k-1}=\varnothing.
$$

末态为 $s$ 的 $X$ 词恰能连接 $B_s$ 中的 $Y$ 词。以下同时优化 $\sigma_b$ 的支撑、谱与 $J$，不固定其特征基。

### 定理 7.2（直接拼接的精确秩与熵）

定义

$$
d_*=
\min\left(c,\ \min_{0\le s<k}\left(a_s+\left\lfloor\frac{n_s}{M}\right\rfloor\right)\right).
\tag{7.1}
$$

在直接拼接合同下，首位零页的最大可用辅助秩仍为 $D_0$；首位一页的最大可用辅助秩为 $d_*$。这里辅助秩即该页任一纯逻辑输入的编码态 Schmidt 秩。整个合同可行当且仅当 $D_0\ge1$ 且 $d_*\ge1$，可行时两页的最大辅助熵 $\log D_0$、$\log d_*$ 能由同一个 $J$ 同时达到。上界覆盖任意 Schmidt 特征基，不限于计算基编码。对预先指定的 $\sigma_1$，式（7.1）不声称仅凭其秩就足以判定可行性。

**证明。** 首位零页的连接无额外限制，直接使用定理 6.2。对首位一页的任意可行编码，设 $d=\operatorname{rank}\sigma_1$。式（6.4）—（6.5）提供等距

$$
W:\mathbb C^M\otimes\mathbb C^d\longrightarrow\mathcal H_{Y,1},
\qquad W(|r\rangle\otimes|j\rangle)=|v_{rj}\rangle.
$$

令 $A_s$ 为首位一且末态至少为 $s$ 的 $X$ 计算基词集。对每个这样的词定义系数向量

$$
q_x=\sum_{j=0}^{d-1}\sqrt{\lambda_j}\langle x|e_j\rangle|j\rangle,
\qquad V_s=\operatorname{span}\{q_x:x\in A_s\}.
$$

全体 $X$ 行构成的系数矩阵列秩为 $d$，因为特征向量正交且所有 $\lambda_j$ 正。去掉末态小于 $s$ 的 $a_s$ 行至多使秩下降 $a_s$，故

$$
\dim V_s\ge d-a_s.
\tag{7.2}
$$

在 $J|1,r\rangle$ 的计算基行 $x$ 上，$Y$ 向量正是 $W(|r\rangle\otimes q_x)$。共同支撑合法性使此向量属于 $\operatorname{span}B_{s(x)}$；对 $x\in A_s$，该空间包含于 $\operatorname{span}B_s$。因此

$$
W(\mathbb C^M\otimes V_s)\subseteq\operatorname{span}B_s,
\qquad M\dim V_s\le n_s.
\tag{7.3}
$$

这使用每个计算基行的总振幅，已经容纳 Schmidt 项之间的相消；未假设每个特征向量分别具有某个计算基支撑。合并式（7.2）—（7.3），得到 $d\le a_s+\lfloor n_s/M\rfloor$，再用 $d\le c$ 即得全部上界。

在 $D_0,d_*\ge1$ 时，为达到该界，按末态从小到大选择 $d_*$ 个 $X$ 词，同末态按字典序排列。对每个阈值 $s$，所选词中末态至少为 $s$ 的数量恰为

$$
\max(0,d_*-a_s).
$$

每个所选词需要 $M$ 个互异的 $Y$ 标签，并要求不同所选词使用的标签也互异。从最大末态开始向下分配。处理状态 $s$ 时，此前使用的全部标签都属于 $B_s$；而包括当前状态的累计需求满足

$$
M\max(0,d_*-a_s)\le n_s.
\tag{7.4}
$$

故 $B_s$ 内剩余标签足以完成这一状态的分配。逐状态归纳即可完成全部分配。这是嵌套邻域的初等匹配原则在当前接口上的应用：共同邻域按包含关系排列，全部阈值需求即保证上述贪心分配成功。

记选出的 $X$ 词为 $x_j$，分给它的 $M$ 个 $Y$ 词为 $y_{rj}$，置

$$
J|1,r\rangle=\frac1{\sqrt{d_*}}\sum_{j=0}^{d_*-1}|x_j\rangle|y_{rj}\rangle.
\tag{7.5}
$$

所有 $y_{rj}$ 互异，故码字正交归一，且页内矩阵单位的 $X$ 偏迹为 $\delta_{rs}d_*^{-1}\sum_j|x_j\rangle\langle x_j|$。每个分配标签都在相应邻域内，故每项 $x_jy_{rj}$ 合法。与零页构造合并时，两侧页支撑正交，跨页偏迹为零，所以整个通道合同成立。均匀谱达到 $\log d_*$；任意谱的熵不超过其秩的对数，证明最优性。若任一页最大秩为零，该页非零逻辑空间不可能编码，亦得可行性判据。证毕。

### 命题 7.3（原生递推与充分的连接状态）

在状态集 $\{0,\ldots,k-1\}$ 上，取带标签的转移 $0:s\to0$，以及在 $s<k-1$ 时的 $1:s\to s+1$。令 $T$ 为按这些转移计数的行到列矩阵，即

$$
T_{s,t}=\mathbf1_{t=0}+\mathbf1_{s<k-1}\mathbf1_{t=s+1}.
$$

从末态 $s$ 出发可接续的长度 $t$ 词数 $F_s(t)$ 满足

$$
F_s(0)=1,\qquad
F_s(t+1)=F_0(t)+\mathbf1_{s<k-1}F_{s+1}(t),
\tag{7.6}
$$

其中缺少的 $s+1=k$ 项直接省略。定义 7.1 的计数因而精确为

$$
x_s=(T^{m_X-1})_{1,s},\qquad
n_s=
\begin{cases}
F_{s+1}(m_Y-1),&s<k-1,\\
0,&s=k-1.
\end{cases}
\tag{7.7}
$$

末态是对任意后续词合法性充分的边界；若需要区分从全部可达合法历史出发的接续合法性，这 $k$ 个状态不能合并。

**证明。** 接续第一位若为零，状态重置为零；若为一，则必须有 $s<k-1$，并转到 $s+1$。按首位分类即得式（7.6）。$X$ 页一的首位使状态为一，其余 $m_X-1$ 步的路径数给出式（7.7）的第一式。$Y$ 页一也必须先读一，从先前末态 $s$ 转到 $s+1$，其后有 $F_{s+1}(m_Y-1)$ 个合法选择；在 $s=k-1$ 时第一步已非法。这恰与开头一串的阈值定义一致。

所有跨界禁串只由左段末尾一串和右段开头一串组成，因此末态记录了全部跨界约束，路径矩阵相乘是在同一个中间状态上求和，每个词对应唯一标签路径。它实现 [《递归关系观察：动态充分边界与内部观察者》](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md) 第 3 节的共同边界响应：这里使用计数加法、乘法，每条约束恰检查一次。式（7.3）的共同合法支撑不能用两个分别可行的边缘容量替代。

每个状态 $s$ 可由词 $1^s$ 到达。若 $s<t<k$，接续词 $1^{k-t}$ 从 $t$ 出发产生 $1^k$，从 $s$ 出发则总长 $s+k-t<k$，仍合法。因此任何保持全部接续合法性的确定性表示都必须区分 $s,t$。这个最小性只针对接续合法性，不涉及量子态层析或固定有限长度窗口内所有状态都可达的断言。证毕。

### 命题 7.4（乘积容量可以严格高估直接拼接）

取 $N=2,k=4,m_X=m_Y=3$，则乘积合同的 $D_1=4$，而直接拼接的 $d_*=3$。

**证明。** 此时 $M_0=2,M_1=1$，两侧每页容量均为四。页一词为 $100,101,110,111$，给出

$$
(x_0,x_1,x_2,x_3)=(2,1,0,1),\qquad
(a_0,a_1,a_2,a_3)=(0,2,3,3),\qquad
(n_0,n_1,n_2,n_3)=(4,3,2,0).
$$

式（7.1）为 $\min(4,4,5,5,3)=3$，而式（6.3）给 $D_1=4$。尤其 $111$ 不能接任何以一开始的 $Y$ 词。零页仍有 $D_0=2$，所以差别确来自页一接口。插入固定零时定理 6.2 的乘积界仍精确；直接拼接必须使用定理 7.2 的联合界。证毕。

## 8. 一个固定编码上的全部嵌套前缀划分

### 定义 8.1（计算基 Schmidt 支撑与前缀计数）

固定一个编码

$$
J|b,r\rangle=\frac1{\sqrt{d_b}}\sum_{j=0}^{d_b-1}
|x_{b,j}\rangle|y_{b,r,j}\rangle,
\qquad d_b\ge1,
\tag{8.1}
$$

其中 $x_{b,j}$ 是长度 $m_X$、首位为 $b$ 的互异合法词；$y_{b,r,j}$ 是长度 $m_Y$、首位为 $b$ 的合法词，在全部 $(b,r,j)$ 上两两互异。包括推论 6.3 的规范编码，也包括定理 7.2 的贪心分配编码；若需要直接拼接，另要求各项 $x_{b,j}y_{b,r,j}$ 合法。

对 $1\le\ell\le m_X$，令 $A_\ell$ 是前 $\ell$ 个环境 $X$ qubit，$B_\ell$ 是余下 $m_X-\ell$ 个 $X$ qubit 连同全部 $Y$。这是环境张量积的划分，不假定合法词空间在此划分处因子化。对长度 $\ell$ 的词 $u$，定义

$$
n_{b,u}=\#\{j<d_b:x_{b,j}\text{ 以 }u\text{ 开头}\},\qquad
q_{b,u}=\frac{n_{b,u}}{d_b},\qquad
U_{b,\ell}=\{u:n_{b,u}>0\}.
$$

长度由 $u$ 指明，故 $n_{b,u}$ 不另写 $\ell$ 下标。令

$$
\tau_{b,\ell}=\sum_{u\in U_{b,\ell}}q_{b,u}|u\rangle\langle u|,
\qquad a_b(\ell)=H((q_{b,u})_{u\in U_{b,\ell}}).
\tag{8.2}
$$

这里 $a_b(\ell)$ 是随划分变化的信息面积，与第 6 节的常数柱权 $a_b$ 区别使用。

### 定理 8.2（同一等距的互补通道与递归面积谱）

对定义 8.1 的同一个 $J$，每个 $\ell$ 都存在与输入无关的支撑等距

$$
W_\ell:\bigoplus_b\left(\mathbb C^{M_b}\otimes\mathbb C^{U_{b,\ell}}\right)
\longrightarrow\mathcal H_{B_\ell}
$$

使对全部逻辑矩阵 $A$ 有

$$
\begin{aligned}
\operatorname{Tr}_{B_\ell}(JAJ^\dagger)
&=\bigoplus_b\operatorname{Tr}(A_{bb})\tau_{b,\ell},\\
\operatorname{Tr}_{A_\ell}(JAJ^\dagger)
&=W_\ell\left[\bigoplus_b A_{bb}\otimes
\operatorname{diag}((q_{b,u})_{u\in U_{b,\ell}})\right]W_\ell^\dagger.
\end{aligned}
\tag{8.3}
$$

最大恢复代数在每个划分上分别仍为 $\mathcal Z$ 和 $\mathcal Z'$。对每个密度矩阵 $\rho$，按定理 6.4 的正权约定，

$$
\begin{aligned}
S(\rho_{A_\ell})&=H(p)+\sum_b p_ba_b(\ell),\\
S(\rho_{B_\ell})&=H(p)+\sum_b p_bS(\rho_b)+\sum_b p_ba_b(\ell),\\
\mathcal L_\ell&=\bigoplus_ba_b(\ell)I_{M_b}.
\end{aligned}
\tag{8.4}
$$

端点与相邻增量满足

$$
a_b(1)=0,\qquad a_b(m_X)=\log d_b,
\tag{8.5}
$$

$$
a_b(\ell+1)-a_b(\ell)
=\sum_{u\in U_{b,\ell}}\frac{n_{b,u}}{d_b}
h_2\left(\frac{n_{b,u1}}{n_{b,u}}\right)
\in[0,\log2],
\qquad 1\le\ell<m_X,
\tag{8.6}
$$

其中 $h_2(t)=-t\log t-(1-t)\log(1-t)$，缺少的孩子计数为零。

**证明。** 对 $u\in U_{b,\ell}$，定义实际的互补向量

$$
|v_{b,r,u}^{(\ell)}\rangle=
\frac1{\sqrt{n_{b,u}}}
\sum_{j:\,\operatorname{prefix}_\ell(x_{b,j})=u}
|\operatorname{suffix}_\ell(x_{b,j})\rangle|y_{b,r,j}\rangle.
\tag{8.7}
$$

这里 $\operatorname{prefix}_\ell$ 取前 $\ell$ 位，$\operatorname{suffix}_\ell$ 删除前 $\ell$ 位。同一向量内的项因 $Y$ 标签互异而正交。不同 $(b,r)$ 的项也因 $Y$ 标签不同而正交；固定 $(b,r)$ 而 $u\ne u'$ 时，两组 $j$ 不交。因此这些向量在全部 $(b,r,u)$ 上正交归一，可以取 $W_\ell|b,r,u\rangle=|v_{b,r,u}^{(\ell)}\rangle$。

按前缀重新分组式（8.1），恰得

$$
J|b,r\rangle=\sum_{u\in U_{b,\ell}}\sqrt{q_{b,u}}
|u\rangle|v_{b,r,u}^{(\ell)}\rangle.
\tag{8.8}
$$

$\ell\ge1$ 保证不同页的前缀基也互不相同。对所有矩阵单位偏迹即得式（8.3），同一固定 $W_\ell$ 适用于全部输入。其谱与式（6.8）相同结构，逐块展开熵即得式（8.4）。

确切的区域代表也可直接写出。对 $z=\bigoplus_bz_bI_{M_b}$ 和 $T=\bigoplus_bT_b$，取

$$
z_{A_\ell}=\sum_bz_b\sum_{u\in U_{b,\ell}}|u\rangle\langle u|,
\qquad
T_{B_\ell}=W_\ell\left[\bigoplus_bT_b\otimes I_{U_{b,\ell}}\right]W_\ell^\dagger.
$$

式（8.8）给出两个交织恒等式及其伴随版本。由式（8.3），两个通道伴随的像分别恰为 $\mathcal Z$、$\mathcal Z'$，故按定理 6.4 的压缩论证，它们就是最大恢复代数，而不是只列出的一组可恢复观测。

在 $\ell=1$ 时每页只有前缀 $b$，概率为一；在 $\ell=m_X$ 时所选 $X$ 标签互异，每个前缀概率为 $1/d_b$，故式（8.5）成立。每个父计数满足

$$
n_{b,u}=n_{b,u0}+n_{b,u1}.
\tag{8.9}
$$

将两个孩子的熵项减去父项，得到

$$
-\sum_{v\in\{u0,u1\}}\frac{n_{b,v}}{d_b}\log\frac{n_{b,v}}{d_b}
+\frac{n_{b,u}}{d_b}\log\frac{n_{b,u}}{d_b}
=\frac{n_{b,u}}{d_b}h_2\left(\frac{n_{b,u1}}{n_{b,u}}\right).
$$

求和即得式（8.6）；$0\le h_2\le\log2$ 且父权之和为一，给出增量界。所有计算只是对同一式（8.1）重新分组：$A_{\ell+1}$ 偏迹最后一位得到 $A_\ell$，$B_\ell$ 偏迹移出的那一位得到 $B_{\ell+1}$。所以这些通道与面积来自相容的嵌套划分，没有在不同划分处更换编码。证毕。

式（8.6）给出固定编码的递归信息面积剖面；它既未将面积定义为某个割的最小值，也未断言这个 $J$ 在全部划分上同时优于所有其他编码。

### 命题 8.3（规范连续地址的前缀区间）

仅对推论 6.3 的连续 $X$ 地址选择，$d_b=D_b$。对任意合法长度 $\ell$ 前缀 $u$，置 $s=s(u)$ 及

$$
L_u=\operatorname{val}_k(u0^{m_X-\ell}).
$$

则其精确前缀计数为

$$
n_{b,u}=\#\left(
[bG_{m_X-1},bG_{m_X-1}+D_b)
\cap[L_u,L_u+F_s(m_X-\ell))\cap\mathbb Z
\right).
\tag{8.10}
$$

**证明。** 以 $u$ 开头的全部合法长度 $m_X$ 词在字典序中连续，最小者为 $u0^{m_X-\ell}$，数量由命题 7.3 等于 $F_s(m_X-\ell)$。定理 1.3 的地址是字典序保序双射，故这些词恰占第二个半开整数区间。与本编码选择的第一个地址区间求交，正好数出前缀为 $u$ 的已选词。证毕。

定理 7.2 按末态选择的 $X$ 支撑一般不连续，不能自动使用式（8.10）的第一个区间；应与实际所选地址集合相交。无论支撑是否连续，式（8.9）的父子计数关系和定理 8.2 都成立。

## 9. 联合有限实例与动态上下文几何

### 命题 9.1（素数窗口 $255$ 的同一码面积剖面）

取 $N=255,k=4,m_X=3,m_Y=9$。则

$$
(M_0,M_1)=(202,54),\qquad
(c_{X,0},c_{X,1})=(4,4),\qquad
(c_{Y,0},c_{Y,1})=(208,193),\qquad
(D_0,D_1)=(1,3).
$$

推论 6.3 的编码具体为

$$
\begin{aligned}
J|0,r\rangle&=|000\rangle|Z_{4,9}(r)\rangle
&& (0\le r<202),\\
J|1,r\rangle&=\frac1{\sqrt3}\bigl(
|100\rangle|Z_{4,9}(208+3r)\rangle
+|101\rangle|Z_{4,9}(209+3r)\rangle
+|110\rangle|Z_{4,9}(210+3r)\rangle\bigr)
&& (0\le r<54).
\end{aligned}
\tag{9.1}
$$

此编码已经满足无分隔位的直接拼接合同，而且在两页同时达到其最优辅助熵。若记 $\Pi_{\rm prime}=\Pi_1$，则同一 $J$ 上的三个前缀划分具有

$$
\mathcal L_1=0,\qquad
\mathcal L_2=h_2(1/3)\Pi_{\rm prime},\qquad
\mathcal L_3=(\log3)\Pi_{\rm prime}.
\tag{9.2}
$$

**证明。** 定理 2.1 给出 $M_b$、九位页容量和 $G_8=208$。三位无禁串，两页各四词；$\lfloor208/202\rfloor=1$、$\lfloor193/54\rfloor=3$，得到所列 $D_b$。零页 $Y$ 地址为 $0,\ldots,201$；一页地址为 $208+3r+j$、$0\le j<3$，最大为 $208+3\cdot53+2=369$。

对直接拼接，三位一页的末态计数以及累计计数为

$$
(x_0,x_1,x_2,x_3)=(2,1,0,1),\qquad
(a_0,a_1,a_2,a_3)=(0,2,3,3).
$$

九位一页中，前缀 $111$ 后必须先接零，其余五位有 $G_5=29$ 种；前缀 $10$ 后有 $G_7=108$ 种。因此

$$
(n_0,n_1,n_2,n_3)=(193,193-29,108,0)=(193,164,108,0).
$$

式（7.1）给

$$
d_*=\min\left(4,\left\lfloor\frac{193}{54}\right\rfloor,
2+\left\lfloor\frac{164}{54}\right\rfloor,
3+\left\lfloor\frac{108}{54}\right\rfloor,3\right)=3.
$$

还须检查式（9.1）本身的联合合法性，不能仅由最优秩相同推出。已选 $X$ 中只有 $101$ 以一结束，其末态为一；$100,110,000$ 末态为零。九位词前缀 $111$ 的首地址是

$$
\operatorname{val}_4(111000000)=G_8+G_7+G_6=208+108+56=372.
$$

全部已用一页 $Y$ 地址至多 $369<372$，故开头一串长度至多二。它与 $101$ 的末尾一相接也只有至多三个一，其余所选 $X$ 在边界处重置。因此式（9.1）的每个计算基项均可直接拼接。

零页的 $X$ 标签只有 $000$，每层前缀分布均为单点。一页标签 $100,101,110$ 的三层正计数依次为 $(3)$、$(2,1)$、$(1,1,1)$。代入式（8.2）得式（9.2）。证毕。

这里的面积是依赖编码的信息面积。素数任务指定了两页语义与基向量的原数标签；任意具有相同两类基数的有限分类任务都允许相同构造，面积公式不额外使用素数分布性质。

### 命题 9.2（原码的尾部歧义与有限后继不闭合）

对定理 1.3 的原编码 $E$，只给定尾部不能在全部有效码字上零错误地恢复页标。另一方面，有限后继

$$
T:\{0,\ldots,N-1\}\to X_N,\qquad T(n)=n+1
$$

不能下降为仅依赖当前首位 $\chi(n)$ 的后继页标规则，对每个 $N\ge2$ 都如此。

**证明。** 对任意 $r<P_N$，定理 1.3 给出两条相同尾部 $Z_{k,m-1}(r)$，但它们的页标分别为零、一。因此不存在对全部承诺输入正确的尾部判页函数。这不表示每个尾部都没有任务信息：当 $P_N\le r<A_N$ 时，承诺码中该尾部只分配给非素数页，故它确定页标为零。

对后继，$0$ 与 $1$ 都在定义域内且 $\chi(0)=\chi(1)=0$，但 $\chi(T(0))=\chi(1)=0$，$\chi(T(1))=\chi(2)=1$。同一当前页标有不同后继页标，故所称下降不存在。编码运输 $E\circ T\circ D$ 保留这个反例；不需要任何无限素数轮廓命题。证毕。

### 命题 9.3（同一新码中的相同边缘态与相反面积速度）

固定命题 9.1 的 $J$ 及一个 $0\le r<54$，记逻辑态

$$
|\psi_\pm\rangle=\frac{|0,r\rangle\pm i|1,r\rangle}{\sqrt2}.
$$

它们编码后的 $X$、$Y$ 边缘态完全相同，并且在定理 8.2 的每个前缀划分上，两侧边缘态也分别相同。取实数 $\Omega\ne0$，以 $\hbar=1$ 定义

$$
h=\frac\Omega2\left(|0,r\rangle\langle1,r|+|1,r\rangle\langle0,r|\right),
\qquad \rho(t)=e^{-ith}\rho(0)e^{ith},
\tag{9.3}
$$

其中 $h$ 在其余逻辑方向上为零。编码空间上的实现是 $JhJ^\dagger$，在正交补上为零；此实现一般跨越 $X|Y$。两态的素数页概率及全 $X$ 面积期望为

$$
p_1^\pm(t)=\frac{1\mp\sin(\Omega t)}2,\qquad
\mathcal A_\pm(t):=\operatorname{Tr}(\rho_\pm(t)\mathcal L_3)
=(\log3)p_1^\pm(t),
$$

$$
\dot{\mathcal A}_\pm(t)=\mp\frac{\Omega\log3}{2}\cos(\Omega t),
\qquad \dot{\mathcal A}_\pm(0)=\mp\frac{\Omega\log3}{2}.
\tag{9.4}
$$

因此，在这个指定更新下，当前两侧区域态的有序对不足以确定其未来区域态，亦不足以确定面积速度。

**证明。** 两个逻辑密度矩阵的对角页块都为 $\rho_{bb}=\tfrac12|b,r\rangle\langle b,r|$，只在跨页相干上不同。式（6.8）、（8.3）消去跨页块，故全部所列初始边缘态相同。编码等距满足 $(JhJ^\dagger)J=Jh$，因此所给物理算符确实实现同一个逻辑演化；没有据此取得区域局域性。

在这两个基向量的空间上，$h=(\Omega/2)\sigma_x$，所以

$$
e^{-ith}=\cos(\Omega t/2)I-i\sin(\Omega t/2)\sigma_x.
$$

作用到 $\psi_\pm$ 并取第二个振幅模平方，得到所列 $p_1^\pm(t)$。用式（9.2）再微分即得式（9.4）。在 $t=0$ 相同的区域态对，经过同一个更新后具有不同页概率，故不可能由该态对唯一决定后继；同读数而速度不同也排除了仅以该读数为状态的自治速度规则。证毕。

这是 [《算术全息 RT》](ARITHMETIC_HOLOGRAPHIC_RT.md) 第 27—28 节、尤其构造 28.4 的面积—相位机制在本双页码中的具体实现，并按 [动态充分边界卷](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md) 定理 2.1 的纤维判据判断闭合。反例针对式（9.3）的更新和当前区域态表示，不是否定任意量子动力学的闭合性。

### 定理 9.4（指定未来读出的精确行为商与距离）

继续固定命题 9.3 的逻辑二维子空间，允许其中的全部密度矩阵。上下文恰为按式（9.3）演化任意 $t\ge0$，随后读取首位的两结果概率律；不包含中途测量或其他控制。令

$$
z=\rho_{00}-\rho_{11},\qquad y=-2\operatorname{Im}\rho_{01},
$$

其中矩阵元按 $|0,r\rangle,|1,r\rangle$ 取。则

$$
\dot z=\Omega y,\qquad \dot y=-\Omega z,\qquad
p_1(t)=\frac{1-z\cos(\Omega t)-y\sin(\Omega t)}2.
\tag{9.5}
$$

对任意两态 $\rho,\widetilde\rho$，其未来概率律的上确界全变差距离精确为

$$
d_{\rm future}(\rho,\widetilde\rho)
 :=\sup_{t\ge0}d_{\rm TV}\bigl((1-p_1(t),p_1(t)),
 (1-\widetilde p_1(t),\widetilde p_1(t))\bigr)
 =\frac12\sqrt{(z-\widetilde z)^2+(y-\widetilde y)^2}.
\tag{9.6}
$$

相应面积期望读出的上确界距离为

$$
d_{\rm area}(\rho,\widetilde\rho)
:=\sup_{t\ge0}|\mathcal A_\rho(t)-\mathcal A_{\widetilde\rho}(t)|
=(\log3)d_{\rm future}(\rho,\widetilde\rho).
\tag{9.7}
$$

零距离当且仅当 $(z,y)=(\widetilde z,\widetilde y)$。因此这些上下文的精确行为商是闭单位圆盘 $\{(z,y):z^2+y^2\le1\}$，带二分之一欧氏距离；未来演化在商上闭合为式（9.5）的旋转。

**证明。** 从 $\dot\rho=-i[h,\rho]$ 直接得到式（9.5）的两条微分方程。解线性系统有

$$
z(t)=z\cos(\Omega t)+y\sin(\Omega t),\qquad
y(t)=y\cos(\Omega t)-z\sin(\Omega t).
$$

迹为一给 $p_1(t)=(1-z(t))/2$。对二结果律，按 $d_{\rm TV}(p,q)=\tfrac12\sum_i|p_i-q_i|$ 的约定，全变差就是 $|p_1-\widetilde p_1|$。置 $\Delta z=z-\widetilde z$、$\Delta y=y-\widetilde y$，它等于

$$
\frac12|\Delta z\cos(\Omega t)+\Delta y\sin(\Omega t)|.
$$

Cauchy–Schwarz 给出振幅上界 $\tfrac12\sqrt{(\Delta z)^2+(\Delta y)^2}$。由于 $\Omega\ne0$，非负时间遍历全部圆周相位，可以令 $(\cos(\Omega t),\sin(\Omega t))$ 与 $(\Delta z,\Delta y)$ 同向或反向；零向量情形恒为零。因此上界达到，得到式（9.6）。面积期望始终是 $(\log3)p_1$，故式（9.7）随之成立。

量子比特的正性要求 $(2\operatorname{Re}\rho_{01})^2+y^2+z^2\le1$，所以商像在闭圆盘内；反之圆盘内任一点都由

$$
\rho(z,y)=\frac12
\begin{pmatrix}
1+z&-iy\\
iy&1-z
\end{pmatrix}
$$

实现，其特征值为 $(1\pm\sqrt{z^2+y^2})/2$。式（9.6）把零距离恰识别为相同 $(z,y)$；式（9.5）同时说明未来读数及后继坐标都由该对唯一决定。任意能确定全部这些未来律的表示都必须区分不同 $(z,y)$，故必因子化到此行为商。

这也是 [《递归关系观察：上下文几何》](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) 第 1—2 节的最小上下文伪度量在当前编码上的显式求值：取演化上下文增益为一，以两结果律全变差作为基础输出距离。演化相加形成相同的上下文族，式（9.6）的距离在旋转下不变并控制当前读数。任何同样使演化不扩张、当前读数为 $1$-Lipschitz 的伪度量都必须控制每个未来实验，因而至少等于式（9.6）的上确界。这给出该距离的最小性。证毕。

行为商只对应这里声明的上下文：不同的 $2\operatorname{Re}\rho_{01}$ 可以具有同一 $(z,y)$，所以它不是完整态层析；概率律和精确期望是数学输入输出，并不授予从一个未知态单次测量取得精确期望的能力。上述面积、递归划分和行为距离均定义于有限编码及指定更新，不构成物理时空、引力或引力 AdS/CFT 的结论。

## 追加锚（本行以下为增补区）

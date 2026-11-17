# AURIC_R5_024：标记树上的主子式纤维与实际六五塔的精确分类

本卷固定特征零域 $F$ 及其代数闭包 $K$。原域中的商集沿用既有约定

$$
Q_U=\{u/v:u,v\in U,\ v\ne0\},\qquad
Q_U^{\times}=Q_U\cap D^{\times},\qquad
d_U(r)=\dim_F(U\cap rU)\quad(r\in D^{\times}),
$$

所以 $0\in Q_U$ 对每个非零 $U$ 都成立；若把 $d_U$ 延到零，另规定 $d_U(0)=0$。所有原标签均是同一个固定域 $D$ 中的字面元素，不对标签作自同构置换。第 46 节提供实际六维中心、五次相对提升、对偶封闭性和完整交维传递；本卷补上任意有限树的几何穷尽、任意竞争空间的半维迫使、内部 torso 的递归恢复以及从分裂对角等价到原 $D^\times$ 标量的下降。

## 47. 一棵六端口标记树

**定义 47.1（六端口 torso 与树空间）。** 设 $T$ 是有 $N\ge1$ 个顶点的有限树。每个顶点 $v$ 带有一个六元端口集 $P_v$，不同顶点的端口集不交；每条边 $e=vw$ 选择两个不同的端口 $p_{v,e}\in P_v$、$p_{w,e}\in P_w$，且同一顶点的不同边使用不同端口。未被边使用的端口组成外部标签集

$$
\Sigma=\bigsqcup_{v\in V(T)}B_v,\qquad
B_v=P_v\setminus\{p_{v,e}:e\ni v\}.
$$

每个 torso 是 $K^{P_v}$ 中的三平面 $L_v$，满足：

1. 任意三个坐标投影在 $L_v$ 上都是同构，即其标记行拟阵是 $U_{3,6}$；
2. $L_v$ 与其普通点积正交补 $L_v^\perp$ 不由任何可逆标记对角矩阵相连；
3. $L_v$ 的每个坐标投影满射，且不含坐标轴。

令 $L_v^0=L_v$、$L_v^1=L_v^\perp$。给定位串 $\varepsilon=(\varepsilon_v)_{v\in V(T)}\in\{0,1\}^{V(T)}$，令 $\widetilde W_\varepsilon$ 为所有族 $(x_v)_v$、其中 $x_v\in L_v^{\varepsilon_v}$，并满足每条边的两个端口坐标相等；删去边端口后得到外部空间 $W_\varepsilon\le K^\Sigma$。这就是沿树边作一维接合的标记树空间。

**引理 47.2（坐标数、维数与树拟阵）。** 对定义 47.1，

$$
|\Sigma|=6N-2(N-1)=4N+2,\qquad
\dim_K W_\varepsilon=3N-(N-1)=2N+1.
\tag{47.1}
$$

每个 $W_\varepsilon$ 的标记行拟阵是把 $N$ 个 $U_{3,6}$ 沿不同端口作 $2$-和所得的连通、自对偶拟阵；其与 $\varepsilon$ 无关。

**证明。** 每条边给出一个独立的一维接合条件。独立性来自端口投影满射：先在一片叶上任意指定接合坐标，再沿树逐片延伸，故 $N-1$ 个条件的秩正好为 $N-1$，得到 (47.1)。

六端口均匀三拟阵是 $U_{3,6}$，而 $U_{3,6}$ 与其对偶相同。表示上的接合正是拟阵 $2$-和；删去接合端口后，两个侧面的秩公式相加并减去“双方都张成接合线”的一项。归纳于顶点数，连通性和自对偶性均由此保持。对偶 $L_v\leftrightarrow L_v^\perp$ 不改变任何局部独立集，故全局拟阵不依赖 $\varepsilon$。$\square$

**定义 47.3（互补主子式多项式）。** 取 $W\le K^\Sigma$ 的满秩帧 $Z_W$（行数 $4N+2$，列数 $n=2N+1$），置

$$
P_W(t)=\det[\,Z_W\mid \operatorname{diag}(t)Z_W\,],\qquad
t=(t_\sigma)_{\sigma\in\Sigma}.
\tag{47.2}
$$

更换帧只把 $P_W$ 乘以非零常数，故记 $[P_W]$ 为其标量类。称 $U$ 为 split 半维空间，若 $\dim U=n$ 且 $P_U\ne0$。

按右半的 $n$ 列作 Laplace 展开，

$$
P_W(t)=\sum_{|I|=n}\varepsilon_I\,p_I(W)p_{I^c}(W)\prod_{i\in I}t_i.
\tag{47.3}
$$

因此 (47.2) 的支撑正是全局拟阵的基，带有原标签而没有坐标置换。

**引理 47.4（连通支撑给出绝对不可约性与原商稠密性）。** 设 $W$ 是定义 47.1 的任一 $W_\varepsilon$。则 $P_W$ 在任意特征零扩域上绝对不可约。并且，若把

$$
\rho:W_K\times W_K\supset\mathcal U\longrightarrow K^\Sigma,\qquad
(a,b)\longmapsto(a_\sigma/b_\sigma)_\sigma
\tag{47.4}
$$

定义在 $b$ 的所有坐标非零的开集上，则 $\rho(\mathcal U)$ 在超曲面 $V(P_W)$ 中稠密。若 $W$ 来自实际域 $D/F$，其原商集 $Q_W$ 在同一超曲面中稠密。

**证明。** 若 $P_W=GH$ 是非平凡分解，齐次性使 $G,H$ 可取齐次；每个变量在 $P_W$ 中次数至多一，故每个变量只能出现在一个因子中。设 $S$ 是 $G$ 所含变量集，则每个支撑基在 $S$ 中都有相同大小。这正给出一个非平凡一分离，与引理 47.2 的连通拟阵矛盾。故 $P_W$ 绝对不可约。

每个变量都确实出现。由特征零与多仿射性，每个偏导 $\partial_iP_W$ 都是非零且次数小于 $P_W$ 的多项式，故不可约性保证它在 $V(P_W)$ 上不恒为零。这个不可约超曲面中，有限个开集 $\partial_iP_W\ne0$ 因而有共同非空交集 $\Omega$。令 $Z=Z_W$、$M(t)=[Z,\operatorname{diag}(t)Z]$。在 $\Omega$ 上不可能有余秩至少二，否则伴随矩阵及所有一阶偏导均为零；故 $M(t)$ 余秩恰为一。

取系数空间中的非零右核向量 $(u,v)\in K^n\oplus K^n$ 和非零左核向量 $\ell\in K^{2n}$，则存在 $c\in K^\times$ 使

$$
\operatorname{adj}(M)=c\binom{u}{v}\ell^{\mathsf T},\qquad
\partial_iP_W=c\ell_i(Zv)_i.
$$

第二式由 Jacobi 公式得到：只有右半矩阵的第 $i$ 行随 $t_i$ 变化。所有偏导非零，因此窗口幅度向量 $b=Zv\in W_K$ 的每个坐标都非零。右核关系给出

$$
a=-Zu=\operatorname{diag}(t)Zv=\operatorname{diag}(t)b\in W_K.
$$

所以 $t=a/b$，而不是把系数向量 $u,v$ 或左核向量 $\ell$ 当成窗口幅度；也不要求 $u,v$ 的每个系数分别非零。这证明 (47.4) 的像包含 $\Omega$，从而支配 $V(P_W)$。

若 $W$ 来自实际域 $D/F$，记原 $F$-空间为 $W_F$。商映射定义在仿射空间 $W_F\times W_F$ 的非空 $F$-有理开集

$$
\mathcal U_F=\{(a,b):\operatorname{Norm}_{D/F}(b)\ne0\}.
$$

分裂后范数是各坐标的乘积，故它的基变换正是 (47.4) 的定义域。无限域 $F$ 的有理点在这个仿射开集中几何 Zariski 稠密。超曲面的任意非空开集在支配映射下有非空开逆像，逆像遂与 $\mathcal U_F(F)$ 相交。因此实际 $a,b\in W_F$ 的商在 $V(P_W)$ 中稠密；所用的是定义域有理点的稠密性，而没有预先假定每个目标开集都有 $F$-点。$\square$

此外 $Q_W\subset V(P_W)$，而 $D$ 在 $D\otimes_FK\simeq K^\Sigma$ 中 Zariski 稠密；由于 $P_W\ne0$，故 $Q_W\ne D$。

**引理 47.5（矩阵切口恰是树边）。** 取 $W=W_\varepsilon$，选互补行基 $I,J$ 并写

$$
W_K=\operatorname{col}\binom{I_n}{A},\qquad
A\in\operatorname{GL}_n(K),\qquad
C_A=\begin{pmatrix}0&A^{-1}\\ A&0\end{pmatrix}.
\tag{47.5}
$$

则 $C_A$ 的每一个非平凡秩一切口正好是树的一条显示边的两侧；反之每条树边都给出这样的切口。

**证明。** 设 $S=I_1\sqcup J_1$，补集为 $I_2\sqcup J_2$，令

$$
p=|I_1|,\quad q=|J_1|,\quad
\rho=\operatorname{rank}A[J_1,I_2],\quad
\sigma=\operatorname{rank}A[J_2,I_1].
$$

图表示给出

$$
r(S)=p+\rho,\qquad r(S^c)=n-p+\sigma,\qquad
\lambda(S)=r(S)+r(S^c)-n=\rho+\sigma.
\tag{47.6}
$$

而逆矩阵的相应子块满足

$$
\operatorname{rank}A^{-1}[I_1,J_2]=\rho+p-q,\qquad
\operatorname{rank}A^{-1}[I_2,J_1]=\sigma+q-p.
\tag{47.7}
$$

全局拟阵自对偶给出 $p-q=\sigma-\rho$。因此 $C_A$ 两个交叉块的秩都等于 $\lambda(S)$。秩一切口于是正好对应 $\lambda(S)=1$ 的非平凡 $2$-分离；在这种情形

$$
(\rho,\sigma,p-q)=(0,1,1)\quad\text{或}\quad(1,0,-1).
\tag{47.8}
$$

还需证明这些 $2$-分离没有隐藏的切口。对一个叶块 $B$（它含五个外部坐标）和接合端口 $e$，把其余带端口的树拟阵记为 $R$，并令 $S_R,T_R$ 为 $S,S^c$ 在 $R\setminus e$ 上的部分。若 $a=|S\cap B|$，并令

$$
\gamma=r_R(S_R)+r_R(T_R)-r_R(R),\qquad
\sigma=\mathbf1_{e\in\operatorname{cl}(S_R)},\qquad
\tau=\mathbf1_{e\in\operatorname{cl}(T_R)},
$$

则表示 $2$-和的秩公式给出

$$
\lambda(S)=g(a)+\gamma+1
-\mathbf1_{a\ge3}\sigma-\mathbf1_{a\le2}\tau,\qquad
g(a)=\min(a,3)+\min(5-a,3)-3.
\tag{47.9}
$$

由于 $e$ 不是 $R$ 的桥元（coloop），$r_R(R\setminus e)=r_R(R)$，故 $\gamma\ge0$。当 $a=2,3$ 时 (47.9) 右侧至少为 $2$。当 $a=1,4$ 时等号为一要求 $\gamma=0$。但 $R\setminus e$ 连通：含 $e$ 的 torso 删去 $e$ 后是连通的 $U_{3,5}$，再与余下连通 torso 作 $2$-和。因此 $S_R$ 或 $T_R$ 必为空。

当 $a=1$ 时，(47.9) 为 $\gamma+2-\tau$。若 $S_R=\varnothing$，则 $\tau=1$，所得 $\lambda=1$ 只有 $S$ 为单点；若 $T_R=\varnothing$，则 $\tau=0$，所得 $\lambda=2$。当 $a=4$ 时，(47.9) 为 $\gamma+2-\sigma$。若 $T_R=\varnothing$，则 $\sigma=1$，所得 $\lambda=1$ 只有 $S^c$ 为单点；若 $S_R=\varnothing$，则 $\sigma=0$，所得 $\lambda=2$。所以这两种 $a$ 都不能给出两侧至少含两个坐标的切口。

边界 $a=0$ 或 $5$ 不能跳过。把单色叶块收缩为接合标记 $e$，(47.9) 分别变为

$$
\lambda_M(S)=\gamma+1-\tau\quad\text{或}\quad
\lambda_M(S)=\gamma+1-\sigma,
\tag{47.10}
$$

具体地，$a=0$ 时删叶后的两侧是 $S_R$ 与 $T_R\cup\{e\}$，$a=5$ 时是 $S_R\cup\{e\}$ 与 $T_R$。因此 (47.10) 正是删叶后带标记树 $R$ 的分离函数。两侧不可能为空；若删叶后有一个单点侧，原坐标组成的单点侧已经被原切口的大小条件排除，唯一剩下的是仅含新标记 $e$ 的一侧。对 $a=0$，这就是 $T_R=\varnothing$；对 $a=5$，这就是 $S_R=\varnothing$。两者都恰是原叶块 $B$ 与余树的显示边，必须保留。

其余情形在删叶后仍是两侧至少含两个坐标的分离，故可归纳于顶点数。归纳所得的显示边提升回原树时，把标记 $e$ 换回同侧的整个叶块 $B$，仍是同一条未删树边。每次删叶都把接合标记恢复成余树 torso 的一个普通第六端口，不会累积缺端口的 torso。单个 torso 时

$$
\lambda_{U_{3,6}}(S)=\min(|S|,3)+\min(6-|S|,3)-3\ge2
$$

对两侧都至少含两个坐标，归纳起点成立。反向由 $2$-和的定义直接给出每条显示边的 $\lambda=1$。$\square$

**引理 47.6（矩形切转置是一个组件对偶）。** 在引理 47.5 的一条边切口上，按两侧排列块矩阵。交换两侧可假定矩形差为一；适配的秩一分解可归一化为

$$
A=\begin{pmatrix}P&0\\ ab^{\mathsf T}&Q\end{pmatrix},\qquad
A^{-1}=\begin{pmatrix}R&cd^{\mathsf T}\\0&S\end{pmatrix},\qquad
b^{\mathsf T}c=d^{\mathsf T}a=1.
\tag{47.11}
$$

逆矩阵等式给出

$$
Pc=0,\quad b^{\mathsf T}R=0,\quad d^{\mathsf T}Q=0,\quad Sa=0,\qquad
PR=I,\ SQ=I,\ RP+cb^{\mathsf T}=I,\ QS+ad^{\mathsf T}=I.
\tag{47.12}
$$

按 CGGR 的 cut-transpose 定义直接代入，得到

$$
\operatorname{ct}(C_A,S)=C_{A'},\qquad
A'=\begin{pmatrix}P&0\\ db^{\mathsf T}&S^{\mathsf T}\end{pmatrix},\qquad
(A')^{-1}=\begin{pmatrix}R&ca^{\mathsf T}\\0&Q^{\mathsf T}\end{pmatrix}.
\tag{47.13}
$$

它的几何含义是：若两侧的增广空间写成

$$
L_X=\{(t,x_1,y_1):t=b^{\mathsf T}x_1,\ y_1=Px_1\},\qquad
L_Y=\{(t,x_2,y_2):y_2=at+Qx_2\},
\tag{47.14}
$$

则 $L_X$ 不变，而 $[a\ Q]^{-1}$ 的两行正是 $d^{\mathsf T}$ 与 $S$，故

$$
L_Y^\perp=\{(t,x_2,y_2):y_2=-dt-S^{\mathsf T}x_2\}.
\tag{47.15}
$$

固定输出坐标的符号后，(47.13) 正是把一侧增广组件逐个 torso 取对偶。反向矩形差交换两侧即可。秩一分解的重标

$$
(p,q,u,v)\mapsto(\lambda p,\lambda^{-1}q,\mu u,\mu^{-1}v)
$$

只改变一个分块对角相似；这是 CGGR Remark 2.11 的因子选择不变性。树没有环，沿边出现的非零接合常数可从根开始递归吸收到顶点与端口的对角标度中。因此任意一次切转置都仍是同一棵标记树，只把一个连通组件的 torso 位翻转。

更一般地，若 $D=\operatorname{diag}(D_I,D_J)$ 是任意标记对角矩阵，则

$$
D C_A D^{-1}=C_{D_J A D_I^{-1}}.
$$

所以全局对角相似只改变图表示的端口标度，不改变 torso 位或树边集合。

**定理 47.7（标记树的完整 split 主子式纤维）。** 设 $T$、$W_0$ 满足定义 47.1，$N=|V(T)|$。令

$$
\mathscr F_T(W_0)=\{U\le K^\Sigma:
\dim U=2N+1,\ [P_U]=[P_{W_0}]\}.
$$

则：

1. 每个 $U\in\mathscr F_T(W_0)$ 都与唯一的某个 $W_\varepsilon$ 在整个标记对角群 $(K^\times)^\Sigma$ 下等价；
2. 不同 $\varepsilon\in\{0,1\}^{V(T)}$ 给出不同的标记对角类；
3. 因而

$$
\#\bigl(\mathscr F_T(W_0)/(K^\times)^\Sigma\bigr)=2^N.
\tag{47.16}
$$

这里的等价保持每一个原坐标标签；不把全局转置另算成一个额外类。

**证明。** 先由引理 47.4 及 (47.2) 的支撑展开，$P_{W_0}$ 绝对不可约。任取 $U$ 使 $[P_U]=[P_{W_0}]$。选择 $W_0$ 的互补基 $I,J$，其互补 Plücker 系数非零；同一系数在 $U$ 上也非零，故两者均可写成

$$
W_0=\operatorname{col}\binom{I}{A},\qquad
U=\operatorname{col}\binom{I}{B},\qquad A,B\in\operatorname{GL}_n(K).
$$

归一化 $y_1\cdots y_n$ 系数后，

$$
F_A(x,y)=\det(\operatorname{diag}(y)-A\operatorname{diag}(x)A^{-1})
$$

与 $F_B$ 相等。对 $C_A,C_B$ 定义如 (47.5)，Schur 补给出

$$
\det(\operatorname{diag}(s,t)+C_A)
=\Bigl(\prod_i s_i\Bigr)F_A(s^{-1},t),
\tag{47.17}
$$

所以 $C_A,C_B$ 的所有带标签主子式相等。部分反演保持 Laurent 多项式不可约；(47.17) 的常数项非零，故普通行列式多项式也不可约。Al Ahmadieh 的 Lemma 5.1 正好把这一步与矩阵不可约性等价起来，因此 $C_A,C_B$ 都不可约。

CGGR 的 Theorem 1.1（其 Definition 2.5、Definition 2.10、Remark 2.11 给出 cut、cut-transpose 及分解选择不变性）现在适用：两个不可约主子式等价矩阵由有限次切转置和末端对角等价连接。引理 47.5 和 47.6 的归纳说明每一步仍在同一棵树的 torso 对偶族中，且下一步的全部切口仍是原来的树边。若采用允许末端全局转置的等价约定，则

$$
C_A^{\mathsf T}=C_{A^{-\mathsf T}},\qquad
W_{A^{-\mathsf T}}=\operatorname{diag}(I,-I)W_A^\perp,
\tag{47.18}
$$

它就是所有 torso 同时取对偶，因而不产生第 $N+1$ 个方向。于是任意 $U$ 落在某个 $W_\varepsilon$ 的标记对角类中。

反之，一条树边的切转置翻转该边一侧的所有位。选根后，边以下子树的指示向量与全树指示向量在 $\mathbf F_2$ 上生成全部顶点指示向量，因为

$$
\mathbf1_{\{v\}}=\mathbf1_{T_v}+\sum_{w\text{ 为 }v\text{ 的子}}\mathbf1_{T_w}.
\tag{47.19}
$$

所以每个 $\varepsilon$ 都确实出现。

最后证明没有两个位串被同一标记对角矩阵识别。若 $N=1$，这就是定义 47.1 的局部非自对偶性。设 $N>1$，取一片叶的五个外部坐标 $B$，令

$$
M_B=\operatorname{pr}_B(W),\qquad N_B=W\cap K^B.
$$

均匀性和接合端口满射给出 $\dim M_B=3,\dim N_B=2$。叶向量在其接合端口的值可由余树延伸；反过来，余树中只支撑在该接合端口的向量经逐叶消去必为零。因此叶被窗口本身恢复为

$$
L_{\mathrm{leaf}}=\{(\ell(x),x):x\in M_B\},\qquad \ker\ell=N_B.
\tag{47.20}
$$

具体地，映射 $w\mapsto(w_{\Sigma\setminus B},[w_B])$ 的核正是 $N_B$，把 $W/N_B$ 识别为 $K^{\Sigma\setminus B}\oplus(M_B/N_B)$ 中的删叶树空间；一维商线就是恢复的接合标记 $e$。任何全局标记对角等价都必须保持 (47.20) 的旗标，并在这条标记线上给出一个非零标量。若两个叶位不同，则得到 $L_v$ 与 $L_v^\perp$ 的标记对角等价，违反定义 47.1；位相同则把等价下降到含此标记的删叶树。重复这个过程，内部 torso 在没有原始外部坐标时也会成为叶并被同一旗标恢复。树无环，所有边标度都可递归吸收，故没有额外接合模数。于是位串唯一，得到 (47.16)。$\square$

**命题 47.8（几何图景的完整中文说明）。** 在定理 47.7 中，每个 torso 是一个带六个固定标签端口的三维平面；一条树边只把两个端口接成一条一维通道，所以总外部坐标为 $4N+2$，总维数为 $2N+1$。一个切转置只把一侧连通组件换成其正交补。由于图是树，沿边传递的符号和非零常数可以从根向外逐条消掉；若图有环，才会出现无法这样消掉的环乘积。

**证明。** (47.1) 给出第一段的两个计数。引理 47.6 的 (47.14)–(47.15) 说明组件对偶不是抽象的“重新命名”：它把接合坐标保留在同一条通道上，只把该组件的局部三平面换成点积正交补。引理 47.5 保证任何可能的非平凡秩一切口都已画在树上。式 (47.20) 说明剪掉一片叶后留下的二维核和三维投影是窗口内部可见的旗标，故可以反复剪到根；这同时解释为什么内部 torso 也会被恢复。局部非自对偶性使每个恢复步骤只能选择原 torso 或其对偶，正好一位比特。$\square$

## 48. 实际六次—五次塔的原商支持与完整交维纤维

**定义 48.1（实际塔的树与深度位）。** 固定实际特征零域塔

$$
F\subset E_0\subset E_1\subset\cdots\subset E_h,\qquad
[E_0:F]=6,\qquad [E_j:E_{j-1}]=5.
\tag{48.1}
$$

令 $D=E_h$、$n=\frac12[D:F]=3\cdot5^h$，并取第 46 节构造的实际窗口。其分裂标签树 $T_h$ 有一个根顶点；第 $j$ 层（$1\le j\le h$）的顶点由 $\operatorname{Hom}_F(E_{j-1},K)$ 标记，$\sigma$ 的父顶点是 $\sigma|_{E_{j-2}}$（$j\ge2$），而第 1 层顶点接到根。每个此类顶点对应一个相对五次窗口。故

$$
N_h=1+6(1+5+\cdots+5^{h-1})=\frac{3\cdot5^h-1}{2},\qquad
|\Sigma_h|=4N_h+2,\qquad
\dim_F W_{h,\varepsilon}=n.
\tag{48.2}
$$

根位和各层位是将要保留下来的深度位；分裂后每个具体 torso 仍有一个独立的几何位。

**定理 48.2（实际塔的精确原支持与完整交维分类）。** 假设第 46 节的实际参数满足其好叶条件。对每个深度位串

$$
\varepsilon=(\varepsilon_0,\ldots,\varepsilon_h)\in\{0,1\}^{h+1},
$$

记 $W_{h,\varepsilon}\le_F D$ 为第 46 节的窗口。则对每个非零 $F$-子空间 $Y\le_FD$，有

$$
\boxed{
Q_Y=Q_{W_{h,0}}
\iff
\bigl(d_Y(r)=d_{W_{h,0}}(r)\ \forall r\in D^\times\bigr)
\iff
Y=aW_{h,\varepsilon}
}
\tag{48.3}
$$

其中 $a\in D^\times$，且 $\varepsilon$ 唯一；固定 $\varepsilon$ 后，$a$ 唯一模 $F^\times$。因此原 $D^\times$ 标量等价下，完整原商支持纤维和完整交维纤维都恰有

$$
2^{h+1}
\tag{48.4}
$$

个类。未取商时，纤维是 $2^{h+1}$ 个互不相交的 $D^\times/F^\times$ 拷贝。

**证明。** 先处理任意竞争者的维数，不能预先假定 $Y$ 半维。令 $W=W_{h,0}$。由第 46 节及树展开，$P_W$ 的支撑是连通自对偶树拟阵的全部基，故引理 47.4 适用；原商 $Q_W$ 在 $V(P_W)$ 中稠密，且不是整个 $D$。若 $m=\dim_FY>n$，则对每个 $r\in D^\times$

$$
\dim_F(Y\cap rY)\ge 2m-2n>0,
$$

从而 $Q_Y=D$，矛盾。若 $m<n$，商映射 $(u,v)\mapsto u/v$ 在每个非零坐标片上有共同的一维标量纤维，故其像闭包维数至多 $2m-1<2n-1$，不能等于稠密于不可约超曲面 $V(P_W)$ 的 $Q_W$。所以 $m=n$。

此时 $P_Y\ne0$，且 $P_Y$ 在 $Q_W$ 上为零。稠密性和 $P_W$ 的绝对不可约性给出 $P_W\mid P_Y$；两者都是次数 $n$ 的齐次多项式，故

$$
P_Y=cP_W,\qquad c\in F^\times.
\tag{48.5}
$$

这里先得出半维和行列式比例，再选择任何公共互补坐标图，正是避免把候选者的维数、拟阵或塔形状当作前件。于是定理 47.7 适用于 $Y_K$：存在唯一的全局几何位串 $\widetilde\varepsilon\in\{0,1\}^{V(T_h)}$ 和可逆分裂对角元 $t$，使

$$
Y_K=t\,(W_{h,\widetilde\varepsilon})_K.
\tag{48.6}
$$

现在施加 Galois 固定性。取第 46 节实际参数给出的全零参考树；Galois 只置换共轭顶点，并与迹正交补交换，所以在位串上的作用是纯粹的顶点置换，没有仿射扭曲。$Y$ 定义在 $F$ 上，故 (48.6) 的标记对角类在 Galois 下固定。由定理 47.7 的唯一性，$\widetilde\varepsilon$ 本身必须固定。顶点轨道正好是

$$
\{\text{根}\},\qquad
\operatorname{Hom}_F(E_{j-1},K)\quad(1\le j\le h).
\tag{48.7}
$$

每个嵌入集在绝对 Galois 群作用下传递，故固定位串恰是每一深度恒定的位串，即 $h+1$ 位。这里数的是固定的位向量，而不是任意位向量的 Galois 轨道。第 46 节的 $W_{h,\varepsilon}$ 正好实现所有这些深度位。

还需把分裂对角元降回原标量。令 $Z=W_{h,\varepsilon}$，定义原 $F$-线性 transporter

$$
H=\{a\in D:aZ\subseteq Y\}
=\ker\bigl(D\longrightarrow\operatorname{Hom}_F(Z,D/Y)\bigr).
\tag{48.8}
$$

核形成与基变换相容，故

$$
H\otimes_FK=\{b\in D\otimes_FK:bZ_K\subseteq Y_K\}.
\tag{48.9}
$$

(48.6) 中的 $t$ 属于右端，故 $H\ne0$。取 $0\ne a\in H$；因为 $D$ 是域，$a$ 可逆，而 $\dim_F(aZ)=\dim_FY=n$，所以 $Y=aZ$。这一步只下降线性核中的“存在非零原乘数”，没有把分裂对角向量逐项识别为某个嵌入像。

最后处理完整 $d$ 函数。第 46.2–46.5 节的相对像公式对任意偶数中心次数成立：记 $e=[E:F]$，对 $U=V$ 或 $V^\perp$，

$$
d_{W(C,U)}(r)=e\kappa_r(U)+\dim_F(R_r(U)\cap C^2),
\tag{48.10}
$$

并逐项覆盖零像、全像、两条轴、非轴直线以及交维为零的情形；半维迹对偶满足 $d_{C^\perp}=d_C$，且

$$
W(C,V)^\perp=W(C^\perp,V^\perp).
\tag{48.11}
$$

因此把任一深度位翻转都保持每个原 $r\in D^\times$ 的完整交维。归纳得到所有 $W_{h,\varepsilon}$ 的 $d$ 相同；再由

$$
d_{aW_{h,\varepsilon}}(r)=d_{W_{h,\varepsilon}}(r)
$$

得到 (48.3) 的右侧蕴含左侧和中间项。中间项蕴含支持相等，因为

$$
Q_U=\{0\}\cup\{r\in D^\times:d_U(r)>0\}.
$$

反向包含已由 (48.5)–(48.9) 得到。若 $aW_{h,\varepsilon}=bW_{h,\varepsilon}$，则 $b^{-1}a$ 是该窗口的原稳定子。树拟阵连通，任一标记对角稳定子在所有基上的坐标乘积相等，沿回路交换逐项比较即得所有坐标相同；其在所有 $F$-嵌入下的值相同，故可分性给出原稳定子恰为 $F^\times$。故 $a$ 唯一模 $F^\times$，并得 (48.4)。$\square$

**命题 48.3（指定特征零数域族）。** 令

$$
\theta_h=2^{1/(6\cdot5^h)}>0,\qquad D_h=\mathbb Q(\theta_h),\qquad
\theta_{h-1}=\theta_h^5.
\tag{48.12}
$$

则 $X^{6\cdot5^h}-2$ 在素数 $2$ 处满足 Eisenstein 判据，故

$$
[D_h:\mathbb Q]=6\cdot5^h,\qquad [D_h:D_{h-1}]=5.
$$

对每个固定 $h$，第 46 节的实际参数存在性给出窗口族；结合定理 48.2，$D_h$ 中的完整原商支持纤维与完整交维纤维均恰有 $2^{h+1}$ 个原标量类。这里系数只由第 46.3 节的实际非空开集存在性选取，不给出显式参数表，也不声称次数最小性。

**证明。** Eisenstein 判据给绝对次数；正根的相容关系给实际包含 $D_{h-1}\subset D_h$，域塔公式给相对次数五。第 46 节在每个固定塔中给出满足好叶条件的实际窗口和完整交维传递，定理 48.2 随即给出精确纤维。$\square$

## 49. 来源、几何边界与术语归属

**命题 49.1（本卷证明所用来源的精确范围）。** 本卷的外部主子式输入只有下列两项：

1. Chatterjee–Ghosh–Gurjar–Raj，*Characterizing and Testing Principal Minor Equivalence of Matrices*，arXiv:2410.01961v1，Theorem 1.1、Definition 2.5、Definition 2.10、Remark 2.11。它给出不可约矩阵的主子式等价由有限 cut-transpose 序列和末端对角等价刻画，并规定 cut 与分解因子选择的相似不变性。本卷的树边识别、矩形归一化和组件对偶闭包是引理 47.5–47.6 的独立推导，不把 CGGR 冒充为树分类本身。
2. A. Al Ahmadieh，*The Fiber of the principal minor map*，arXiv:2309.00806v2，Lemma 5.1、Theorem 5.2。这里仅使用 Lemma 5.1 的“行列式多项式不可约当且仅当矩阵不可约”方向；本卷不使用其余纤维分类作为黑箱。

树的 $2$-和、split 与 $2$-分离术语承接 Cunningham–Edmonds，*A Combinatorial Decomposition Theory*，Canadian Journal of Mathematics 32 (1980)，Theorems 16、18、19；表示接合的标准背景可参见 Baker–Lorscheid–Walsh–Zhang，*The foundation of generalized parallel connections, 2-sums, and segment-cosegment exchanges of matroids*，Combinatorial Theory 5(4) (2025)，Theorem C 与 Theorem 4.2。本卷没有把这些一般性结果当作替代证明：需要的特殊树边结论已在 (47.9)–(47.10) 中逐叶证明。

第 46 节已记录有限域线性集先例：Csajbók–Marino–Polverino，arXiv:1607.06962v1，Result 2.1 与 Definitions 2.3–2.4；Zullo，arXiv:2112.08781v2，Theorem 3.5；Pepe，arXiv:2403.01551v2，Theorems 8、24；以及 Van de Voorde–Zullo，arXiv:2511.20057v1，Theorem 5.1 与 §5.2。它们分别提供有限域迹对偶、Cartesian 权重、Dickson 主子式和迭代权重传递的中间先例；本卷的特征零原标签穷尽、深度 Galois 固定和原标量下降不由这些有限域结果推出。

本卷的数学边界是：定理 47.7 只断言 split 半维空间的主子式多项式纤维恰有 $2^N$ 个标记对角类；它不把主子式或支持相等误当作所有 split 高余秩函数相等。实际塔中的完整 $d$ 相等只来自第 46.2–46.5 节的相对像公式和迹对偶传递。全程固定原始标签和原 $D^\times$ 标量等价，不引入标签自同构、半线性等价、量子或 H10 结论，也不主张全局文献新颖性或任何指定系数已经被形式系统认证。

**命题 49.2（迭代问题的结算）。** 在定理 48.2 的假设下，完成全部树切口、任意竞争者的半维迫使、内部旗标恢复、Galois 深度固定和 transporter 下降后，不存在第 $2^{h+1}+1$ 个实际原标量类；任何声称的额外类都必须先违反其中一个已证明的步骤。

**证明。** 任意额外类先给出一个非零原空间 $Y$；定理 48.2 先迫使其半维，再迫使其分裂对角类落在唯一深度位串，最后迫使其为一个 $W_{h,\varepsilon}$ 的原域标量倍。稳定子计算只允许 $F^\times$ 的标量歧义，故额外类不存在。$\square$

## 追加锚（本行以下为增补区）

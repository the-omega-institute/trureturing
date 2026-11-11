# R5 续卷：特征零半维窗口的最小交叠与原标量轨道恢复

## 26　任意特征零有限扩张中的实际半维窗口

**定义 26.1（实际窗口与原标签观察）。** 固定特征为零的域 $F$、其有限域扩张 $L/F$、正整数 $m$，满足 $[L:F]=2m$。窗口是原 $L$ 中满足 $\dim_F W=m$ 的 $F$-线性子空间。所有乘积、商及标量作用均使用这个 $L$ 的原乘法。对原标签 $r,s\in L^\times$，定义

$$
\begin{aligned}
d_W(r)&=\dim_F(W\cap rW),\\
J_W(r,s)&=\dim_F(W\cap rW\cap sW),\\
E_W&=\{a\in L:aW\subseteq W\},\\
\delta_W&=\min\{d_W(r):r\in L^\times,\ d_W(r)>0\}.
\end{aligned}
\tag{26.1}
$$

由于 $d_W(1)=m>0$，最小值存在。称 $d_W(r_0)=\delta_W$ 的 $r_0\in L^\times$ 为最小正行标签，并定义仅使用该行正支持的集合

$$
T_{W,r_0}=\{0\}\cup
\{s^{-1}:s\in L^\times,\ J_W(r_0,s)>0\}\subseteq L.
\tag{26.2}
$$

本定义将 [《原有向面积与三重返回》§25](AURIC_R5_022_ORIENTED_AREA_AND_TERNARY_RETURN.md) 的同名观察用于任意上述 $L/F$；标签仍是原 $L^\times$ 的元素，不对标签作域自同构重排。这里的等价关系只允许 $V=xW$、$x\in L^\times$。

**定理 26.2（特征零半维窗口的全量词恢复）。** 对定义 26.1 中任意实际 $F,L,m,W$，$E_W$ 是包含 $F$ 的子域。记 $e=[E_W:F]$，则 $e\mid m$，并且

$$
\delta_W=e.
\tag{26.3}
$$

更具体地，存在原 $W$ 中的非零元素 $u,v$，满足

$$
W\cap (u/v)W=E_Wu.
\tag{26.4}
$$

任取最小正行标签 $r_0$ 及任一 $0\ne z\in W\cap r_0W$，都有

$$
W\cap r_0W=E_Wz,\qquad T_{W,r_0}=z^{-1}W.
\tag{26.5}
$$

对原 $L$ 中每个满足 $\dim_F V=m$ 的竞争窗口 $V$，即使不假设 $r_0$ 对 $V$ 也是最小正行，仍有

$$
\begin{aligned}
&\bigl[\ \forall s\in L^\times,\quad
J_V(r_0,s)>0\ \Longleftrightarrow\ J_W(r_0,s)>0\ \bigr]\\
&\hspace{35mm}\Longleftrightarrow\quad
\exists x\in L^\times,\quad V=xW.
\end{aligned}
\tag{26.6}
$$

因此完整的原标签三重观察恰好恢复原非零标量轨道：

$$
\bigl[\ \forall(r,s)\in(L^\times)^2,\quad J_V(r,s)=J_W(r,s)\ \bigr]
\quad\Longleftrightarrow\quad
\exists x\in L^\times,\quad V=xW.
\tag{26.7}
$$

证明。先证明 (26.3)–(26.4)，再消费前卷 §25 的支持恢复机制。辅助域与辅助向量只用于证明存在性，最终的见证及 (26.2) 的集合都在原 $L$ 中。

先缩写 $E=E_W$。有限维乘法稳定子的通常事实给出 $E$ 成域：它包含 $F$，对加法、减法、乘法封闭；若 $0\ne a\in E$，则乘以 $a$ 在有限维 $W$ 上单射，故 $aW=W$，从而 $a^{-1}W=W$。这里消费的事实见 Bachoc–Serra–Zémor，[*Revisiting Kneser's Theorem for Field Extensions*，arXiv:1510.01354v2，§2.3，Lemma 13 后的有限维说明](https://arxiv.org/pdf/1510.01354v2)。于是 $W$ 为 $E$-向量空间。设

$$
k=\dim_E W=m/e,\qquad N=[L:E]=2k.
\tag{26.8}
$$

每个 $W\cap rW$ 都是 $E$-线性的，因为原乘法交换。因此每个正的 $d_W(r)$ 均为 $e$ 的正倍数，已经有 $\delta_W\ge e$。若 $k=1$，任取 $u=v\in W\setminus\{0\}$，便有 $W=Eu$，直接得到 (26.3)–(26.4)。以下设 $k\ge2$。

在辅助底域 $E$ 上，$W$ 的乘法稳定子恰为 $E$ 本身。为严格控制分裂时是否产生新稳定方向，考虑有限维 $E$-线性映射

$$
\begin{aligned}
\Phi:L&\longrightarrow\operatorname{Hom}_E(W,L/W),\\
a&\longmapsto\bigl(w\longmapsto aw+W\bigr).
\end{aligned}
\tag{26.9}
$$

其核恰为 $E$。对任意扩域 $K/E$，取基后 $\Phi$ 是一个 $E$ 上的有限矩阵；非零子式在扩域后仍非零，矩阵秩不变。等价地，向量空间扩底保持这条核的正合性，所以

$$
\ker(\Phi\otimes_E K)=(\ker\Phi)\otimes_E K=E\otimes_E K.
\tag{26.10}
$$

这里同时使用有限维下的自然同构

$$
\operatorname{Hom}_E(W,L/W)\otimes_E K
\simeq
\operatorname{Hom}_K(W\otimes_E K,(L/W)\otimes_E K)
$$

以及 $(L/W)\otimes_E K\simeq(L\otimes_E K)/(W\otimes_E K)$。因此 (26.10) 控制的是整个乘法稳定子核，包含所有扩底后可能出现的线性组合，而非仅控制原来逐个列出的稳定元素。

特征零使 $L/E$ 可分。取其有限正规闭包 $K/E$，令

$$
\Omega=\operatorname{Hom}_E(L,K),\qquad |\Omega|=N.
$$

分裂同构是 $K$-代数同构

$$
\begin{aligned}
\iota:L\otimes_E K&\overset{\sim}{\longrightarrow}K^\Omega,\\
a\otimes c&\longmapsto(c\sigma(a))_{\sigma\in\Omega}.
\end{aligned}
\tag{26.11}
$$

这就是可分扩张的标准分裂：取 $L/E$ 的本原元后，其最小多项式在 $K$ 中分成 $N$ 个互异一次因子，中国剩余同构给出 (26.11)。乘法在右边逐坐标进行。

置 $U=\iota(W\otimes_E K)$。将 (26.10) 通过 (26.11) 传递，得到精确的对角稳定代数等式

$$
\{c\in K^\Omega:\operatorname{diag}(c)U\subseteq U\}
=K\boldsymbol 1,\qquad
\boldsymbol 1=(1)_{\sigma\in\Omega}.
\tag{26.12}
$$

原因是 $E\otimes_E K$ 在 (26.11) 下恰为公共标量的对角线。至此非平凡的原稳定子已通过改用 $E$ 完整计入，并没有被假设为 $F$；分裂后也没有遗失额外稳定方向。

取原 $W$ 的一个 $E$-基 $w_1,\ldots,w_k$。以

$$
B=(\sigma(w_j))_{\sigma\in\Omega,\ 1\le j\le k},\qquad
b_\sigma=(\sigma(w_1),\ldots,\sigma(w_k))\in K^k
\tag{26.13}
$$

表示 $U$ 的列空间。$B$ 的列秩为 $k$，各行都非零：例如 $w_1\ne0$，任何域嵌入均满足 $\sigma(w_1)\ne0$。定义行拟阵 $M$ 的秩函数

$$
\rho(S)=\dim_K\operatorname{span}_K\{b_\sigma:\sigma\in S\},
\qquad S\subseteq\Omega.
\tag{26.14}
$$

它无环，且 $\rho(\Omega)=k$。

先核对该拟阵连通。若不连通，就存在非空真子集 $S\subsetneq\Omega$ 及 $S^c=\Omega\setminus S$，满足

$$
\rho(S)+\rho(S^c)=k.
$$

这里使用线性拟阵直和的通常判据。坐标限制映射

$$
U\longrightarrow \pi_S U\oplus\pi_{S^c}U
$$

是单射，右边维数为 $\rho(S)+\rho(S^c)=k=\dim_K U$，故它满射。这说明将 $U$ 的一个向量在 $S^c$ 上置零后，结果仍属于 $U$。于是非平凡坐标投影 $\operatorname{diag}(\boldsymbol 1_S)$ 稳定 $U$，与 (26.12) 矛盾，因为 $\boldsymbol 1_S$ 不是公共标量。因此 $M$ 连通。这一步把“唯一对角稳定方向”实质地转换成了拟阵连通性。

再核对严格秩界。$G=\operatorname{Gal}(K/E)$ 在 $\Omega$ 上传递作用。对 $g\in G$，

$$
g(b_\sigma)=b_{g\circ\sigma}.
$$

域自同构保持一个矩阵的零与非零子式，因此

$$
\rho(gS)=\rho(S)\qquad(S\subseteq\Omega).
\tag{26.15}
$$

这验证的是同一个 $W$ 所给行拟阵的对称性，不是假设 $W$ 在嵌入之间一般位置。对 $M$ 的全部基赋予均匀概率测度 $\mu$。基的集合非空且有限，$\mu$ 对每个基都严格为正；(26.15) 及传递性使 $\mu\{A:\sigma\in A\}$ 与 $\sigma$ 无关。每个基有 $k$ 个元素，故这些边缘概率均为 $k/N=1/2$。

此时直接应用 Devriendt–Mulas，[*Uniform density in matroids, matrices and graphs*，arXiv:2306.15267v3，Theorem 2.10 的 (3)$\Rightarrow$(2)](https://arxiv.org/pdf/2306.15267v3)：全支撑的等边缘基测度给出均匀密度，且凡不是连通分量之并的子集都满足严格密度不等式。由于刚才已经证明 $M$ 连通，每个非空真子集均不可能是连通分量的并。因此

$$
\frac{|S|}{\rho(S)}<\frac{N}{k}=2,
\qquad \varnothing\ne S\subsetneq\Omega,
$$

即

$$
2\rho(S)\ge |S|+1
\qquad(\varnothing\ne S\subsetneq\Omega).
\tag{26.16}
$$

这里完整使用了正测度的全支撑条件及连通性；仅有非严格的均匀密度不足以推出 (26.16)。该成熟密度定理只在本推导内部消费，不另作新的密度基础。

现在把 (26.16) 接到一刀超平面。对每个 $\sigma\in\Omega$，在 $K^k\oplus K^k$ 中取二维子空间

$$
A_\sigma=K(b_\sigma,0)\oplus K(0,b_\sigma).
\tag{26.17}
$$

各 $A_\sigma$ 非零，且对任意 $S\subseteq\Omega$，

$$
\dim_K\sum_{\sigma\in S}A_\sigma=2\rho(S).
\tag{26.18}
$$

由 (26.16)，$k\ge2$ 时两条不同行不可能成比例：若成比例，则它们构成的二元真子集秩一，违反 (26.16)。所以这里各 $A_\sigma$ 也互异，可以直接作为通常的有限子空间族使用。

引入在 $K$ 上代数独立的 $2k$ 个参数

$$
X=(X_1,\ldots,X_k),\qquad Y=(Y_1,\ldots,Y_k),\qquad
K'=K(X_1,\ldots,X_k,Y_1,\ldots,Y_k),
$$

并在扩底后的 $K'^{\,k}\oplus K'^{\,k}$ 中令

$$
H_{X,Y}=\{(a,b):X\cdot a-Y\cdot b=0\}.
\tag{26.19}
$$

法向量 $(X,-Y)$ 的坐标代数独立，故这是整个超平面参数空间的泛点，不是某个额外受限的超平面族。Raz–Wigderson，[*Subspace arrangements, graph rigidity and derandomization through submodular optimization*，arXiv:1901.09423v1，Definition 5.1、Theorems 7.1、5.2 及 §2 式 (3)](https://arxiv.org/pdf/1901.09423v1)，在特征零下给出：此泛超平面对固定有限族 $\{A_\sigma\}$ 满足 Definition 5.1 的一般位置前件，且

$$
\dim_{K'}\operatorname{span}_{K'}\{(A_\sigma\otimes_K K')\cap H_{X,Y}:\sigma\in\Omega\}
=\min_{\mathcal P}\sum_{S\in\mathcal P}(2\rho(S)-1),
\tag{26.20}
$$

其中 $\mathcal P$ 遍历 $\Omega$ 的非空块分拆。(26.18) 保证式中恰是该定理的子族跨度维数；(26.20) 是“各自切过后共同张成”的维数，不是先共同张成再切的无条件替换。

单块分拆的代价为 $2k-1=N-1$。任何至少两块的分拆中，每一块都是非空真子集，(26.16) 给出

$$
\sum_{S\in\mathcal P}(2\rho(S)-1)
\ge\sum_{S\in\mathcal P}|S|=N.
$$

所以 (26.20) 的最小值恰为 $N-1$，且只有单块分拆能达到它。这里排除过密真子集所需的严格性，正是由稳定子核、连通性与 Galois 对称性共同提供的。

为把该维数解释为原乘法的一个矩阵秩，记

$$
u(X)=\sum_{j=1}^kX_jw_j,\qquad
v(Y)=\sum_{j=1}^kY_jw_j.
\tag{26.21}
$$

在分裂坐标下，这两个形式向量的 $\sigma$ 坐标分别是 $b_\sigma\cdot X$ 与 $b_\sigma\cdot Y$，均为非零多项式。于是 (26.17)–(26.19) 直接给出

$$
(A_\sigma\otimes_K K')\cap H_{X,Y}
=K'\bigl((b_\sigma\cdot Y)b_\sigma,
             (b_\sigma\cdot X)b_\sigma\bigr).
\tag{26.22}
$$

确实，$(\lambda b_\sigma,\eta b_\sigma)$ 属于该超平面，当且仅当 $\lambda(b_\sigma\cdot X)=\eta(b_\sigma\cdot Y)$；两系数均非零，故解空间就是 (26.22) 的一条线。这些行共同构成矩阵

$$
\mathcal B(X,Y)=
\left[\operatorname{diag}(BY)B\ \middle|\ \operatorname{diag}(BX)B\right],
\qquad \operatorname{rank}_{K'}\mathcal B(X,Y)=N-1.
\tag{26.23}
$$

这是 Antolini–Dewar–Tanigawa，[*Dilworth truncations and Hadamard products of linear spaces*，arXiv:2508.04798v1，§3.2 式 (7)–(9)](https://arxiv.org/pdf/2508.04798v1) 的二因子行与超平面对应在本对象上的代入；两个因子使用独立参数 $X,Y$。其复数域上的二因子公式，以及 Bernstein [arXiv:2003.10529v4，Theorem 3.1](https://arxiv.org/pdf/2003.10529v4)，已在 [《QUANTUM-REALITY》定理 410.1](QUANTUM-REALITY.md) 中消费。这里没有把复数域结论直接移植到任意 $F$，也没有新增一般 Hadamard 公式；任意特征零辅助域上的 (26.20) 由上述 Raz–Wigderson 原定理承担，而 (26.22) 是同一个原乘法矩阵的具体接口。

最后实质地返回原域。固定 $L$ 的一个 $E$-基 $\ell_1,\ldots,\ell_N$，在此基下以

$$
\mathcal C(X,Y)=
\left[
v(Y)w_1\ \cdots\ v(Y)w_k\ \middle|\ u(X)w_1\ \cdots\ u(X)w_k
\right]
\in\operatorname{Mat}_{N\times 2k}(E[X,Y])
\tag{26.24}
$$

表示各列的坐标。系数确实在 $E$ 中，因为这只是原 $L/E$ 的乘法在固定 $E$-基下的结构常数。矩阵

$$
D=(\sigma(\ell_i))_{\sigma\in\Omega,\ 1\le i\le N}
\in\operatorname{GL}_N(K)
$$

由 (26.11) 可逆，且逐列应用嵌入给出

$$
D\mathcal C(X,Y)=\mathcal B(X,Y).
\tag{26.25}
$$

所以 (26.23) 蕴含 $\mathcal C$ 的某个 $(N-1)$ 阶子式 $f(X,Y)\in E[X,Y]$ 是非零多项式。这不是仅在 $K$ 上定义的存在条件：它是原乘法矩阵本身的一个原 $E$ 系数子式。

域 $E$ 无限，故存在 $x,y\in E^k$ 使

$$
f(x,y)x_1y_1\ne0.
\tag{26.26}
$$

这里所用多项式事实不需任何代数闭性：非零多元多项式在无限域上有非零值。其证明按变量数归纳，将多项式视为最后一个变量的一元多项式；先令某个非零系数在其余变量上非零，再避开最后变量的有限多个根即可。由于 $E[X,Y]$ 是整环，$fX_1Y_1$ 非零，故该事实确实适用于 (26.26)。

置 $u=u(x),v=v(y)$。由 $x_1y_1\ne0$ 及 $w_j$ 的 $E$-线性无关性，$u,v\in W\setminus\{0\}$。这些都是原 $L$ 中的元素。矩阵 $\mathcal C(x,y)$ 的列空间为 $vW+uW$，且 (26.26) 使其 $E$-维数至少为 $N-1$。另一方面，原乘法给出公共非零元素 $uv\in uW\cap vW$，而 $uW,vW$ 各为 $k$ 维，故

$$
\dim_E(uW+vW)\le2k-1=N-1.
$$

于是两边相等，并且

$$
\dim_E(uW\cap vW)=1,\qquad uW\cap vW=Euv.
\tag{26.27}
$$

乘以原 $v^{-1}$ 得到 (26.4)。它给出 $d_W(u/v)=e$，与先前的 $\delta_W\ge e$ 合起来证明 (26.3)。返回的是 $E$ 中的参数及原 $W$ 中的 $u,v$，从而也是原 $F,L,W$ 的合法见证；未把扩域参数或嵌入位置当作原域解。

以下直接消费前卷定理 25.2 证明中的支持取逆及包含—等维机制，其所需参数在这里为 $F,L,W,E,e,m$，不依赖前卷的特殊八次域。由 (26.3)，任意最小正行满足 $W\cap r_0W=Ez$。对于每个原 $s\in L^\times$，

$$
\begin{aligned}
J_W(r_0,s)>0
&\Longleftrightarrow Ez\cap sW\ne\{0\}\\
&\Longleftrightarrow \exists c\in E^\times,\quad cz/s\in W\\
&\Longleftrightarrow z/s\in W.
\end{aligned}
\tag{26.28}
$$

最后一步只用 $W$ 的 $E$-线性及 $c^{-1}\in E$。将原标签 $s$ 取逆即得到 (26.5) 的第二式；$z$ 并未成为 (26.2) 的额外输入。

为明确核对所有竞争窗口，设 (26.6) 左边成立。由 $J_W(r_0,1)>0$ 得 $V\cap r_0V\ne\{0\}$，在证明中任取其中的 $y\ne0$。对任意 $v'\in V\setminus\{0\}$，原标签 $s=y/v'$ 满足 $y\in V\cap r_0V\cap sV$，故支持相等与 (26.28) 给出

$$
v'/y=s^{-1}\in z^{-1}W.
$$

于是 $y^{-1}V\subseteq z^{-1}W$。两边都是 $m$ 维 $F$-子空间，故相等，$V=(y/z)W$。这里既未使用 $V$ 的最小正行，也未假设 $E_V=E$。反方向由原乘法的交换性立即给出：乘以 $x\in L^\times$ 同构每一个 $W\cap rW\cap sW$ 与 $xW\cap r(xW)\cap s(xW)$，所以保持完整 $J$，尤其保持该行正支持。这证明 (26.6)。最后 $d_W(r)=J_W(r,1)$，完整 $J$ 因而决定最小正值及其标签集合；若两份完整 $J$ 相同，可为 $W$ 选任一这样的 $r_0$ 并应用 (26.6)，得到 (26.7)。$\square$

本定理的文献对应与实质范围。有限维稳定子成域、可分扩张的分裂、严格均匀密度及一般超平面的分拆秩公式均为上述成熟工具；支持取逆与包含—等维恢复机制已由前卷 §25 给出，这些机制不作为新增基础。Csajbók–Marino–Pepe，[*On the maximum field of linearity of linear sets*，arXiv:2306.07488v2，Theorem 1](https://arxiv.org/pdf/2306.07488v2)，承担有限域最大秩线性集的最小正权结论；该定理的底域为有限域，不能直接代入本定理的任意特征零 $F$。Bachoc–Serra–Zémor 的 Theorems 2–3 控制普通乘积张成 $ST$ 的维数与其稳定子，也没有直接给出这里两个可变原乘法像 $uW,vW$ 的最小交叠。

相对于这些指定原文、前卷 §25 及《QUANTUM-REALITY》§§409–410，本定理的仓内推导（repo-derived）差额是 (26.9)–(26.27) 的同一对象桥梁：完整稳定子核扩底，Galois 传递行拟阵的连通与严格秩前件，以及原 $E$ 系数非零子式的原域返回。它将固定有理数八次域的全窗口结论扩大到全部特征零有限扩张的实际半维窗口，包括 $E_W\ne F$ 的分支；不需要选取特殊良素数，不将所列来源范围内的未覆盖解释为全球首次性。

白话说，先把窗口天然容许的标量全部算进底域，分裂后就只剩“所有坐标一起缩放”这一种稳定方向。若某一批坐标能独立保存窗口，便会产生一个额外稳定投影，因此这种分块被排除；Galois 对称性再保证每批真子坐标都付得起严格秩代价。一般超平面的一刀因而恰好只留下必然的共同一线。最后用原乘法矩阵的一个非零子式在无限原域中取值，将这条线真正带回原窗口。最小行的正支持只负责把它写成某个共同缩放后的集合，隐藏向量从未交给观察者。

本定理讨论完整、无限、无噪声、逐原标签精确读数的集合论可识别性。(26.2) 没有附送稳定子基、嵌入坐标、公共向量或扩域标量；(26.4) 的存在性也不是有限查询或有效寻找最小正行的算法。定理不提供有限标签菜单、噪声鲁棒性或实际取得成本；其量词限于特征零及半维条件，不扩大为任意特征、非半维、三维二元恢复或最小观察阶数，也不推出量子概率、复 Hilbert 空间、测量与控制公理，以及 $\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义或 $H10(\mathbb Q)$。

## 追加锚（本行以下为增补区）

## 27　三维实际窗口的比值域分支与原标签轨道恢复

**定义 27.1（三维窗口、比值域与观察）。** 固定特征为零的域 $F$ 及有限域扩张 $L/F$。窗口是原 $L$ 中满足 $\dim_F W=3$ 的 $F$-线性子空间。所有乘积、商与标量作用均使用原 $L$ 的乘法。对原标签 $r,s\in L^\times$，记

$$
\begin{aligned}
J_W(r,s)&=\dim_F(W\cap rW\cap sW),\\
d_W(r)&=J_W(r,1)=\dim_F(W\cap rW),\\
D_W&=F\bigl(\{u/v:u,v\in W,\ v\ne0\}\bigr)\subseteq L,\\
E_W&=\{a\in L:aW\subseteq W\},\\
\delta_W&=\min\{d_W(r):r\in L^\times,\ d_W(r)>0\}.
\end{aligned}
\tag{27.1}
$$

最小值因 $d_W(1)=3$ 而存在。对任一满足 $d_W(r_0)=\delta_W$ 的原标签，定义

$$
T_{W,r_0}=\{0\}\cup
\{s^{-1}:s\in L^\times,\ J_W(r_0,s)>0\}.
\tag{27.2}
$$

观察输入只有固定原域上的完整函数 $J_W$；$D_W,E_W$ 是由 $W$ 定义的证明对象，(27.2) 则只使用指定行的正支持。竞争窗口始终是同一个原 $L$ 内的三维 $F$-子空间；等价关系只允许 $V=xW$、$x\in L^\times$，不重标原标签。

**定理 27.2（全部三维窗口的分类与单行分离）。** 对定义 27.1 中每一个 $W$，$E_W$ 是包含 $F$ 的子域，且 $E_W\subseteq D_W$。置 $h=[D_W:F]$、$e=[E_W:F]$，则 $h\ge3$、$h\mid[L:F]$，精确分类为

$$
(e,\delta_W)=
\begin{cases}
(3,3),&h=3,\\
(1,2),&h=4,\\
(1,1),&h\ge5.
\end{cases}
\tag{27.3}
$$

任取 $w\in W\setminus\{0\}$，都有 $w^{-1}W\subseteq D_W$ 及 $F(w^{-1}W)=D_W$，并存在原 $\theta\in w^{-1}W$ 满足 $F(\theta)=D_W$。特别地，$\theta=(w\theta)/w$ 是原窗口比值。任意正交叠标签都属于 $D_W^\times$，而且

$$
D_W=F\bigl(\{r\in L^\times:d_W(r)>0\}\bigr),\qquad
E_W=\{0\}\cup\{r\in L^\times:d_W(r)=3\}.
\tag{27.4}
$$

三次分支有 $W=wD_W$，且 $d_W(r)=3$ 对全部 $r\in D_W^\times$ 成立；四次分支有 $w^{-1}W$ 为 $D_W$ 的 $F$-超平面，且

$$
d_W(r)=
\begin{cases}
3,&r\in F^\times,\\
2,&r\in D_W^\times\setminus F^\times,\\
0,&r\in L^\times\setminus D_W^\times.
\end{cases}
\tag{27.5}
$$

在三次分支及次数至少五的分支，存在原 $u,v\in W\setminus\{0\}$，使 $W\cap(u/v)W=E_Wu$。四次分支的最小正交叠为二，严格大于稳定子次数一。

任取 $W$ 的最小正行标签 $r_0$，有

$$
T_{W,r_0}=
\begin{cases}
D_W,&h\in\{3,4\},\\
z^{-1}W,&h\ge5,\quad 0\ne z\in W\cap r_0W.
\end{cases}
\tag{27.6}
$$

尽管四次分支的 $T_{W,r_0}$ 为四维而不是窗口的标量倍，任意这样的行仍分离全部三维竞争窗口：对每个 $V\le_F L$、$\dim_F V=3$，不假设 $r_0$ 对 $V$ 最小，仍有

$$
\begin{aligned}
&\bigl[\ \forall s\in L^\times,\quad
J_V(r_0,s)>0\ \Longleftrightarrow\ J_W(r_0,s)>0\ \bigr]\\
&\hspace{30mm}\Longleftrightarrow\quad
\exists x\in L^\times,\quad V=xW.
\end{aligned}
\tag{27.7}
$$

因此完整原标签恰好恢复原标量轨道：

$$
\bigl[\ \forall(r,s)\in(L^\times)^2,\quad J_V(r,s)=J_W(r,s)\ \bigr]
\quad\Longleftrightarrow\quad
\exists x\in L^\times,\quad V=xW.
\tag{27.8}
$$

证明。固定任意 $w\in W\setminus\{0\}$，缩写 $D=D_W$、$E=E_W$，令 $U=w^{-1}W$。原乘法的交换性给出 $J_U=J_W$ 及 $E_U=E_W$。因为 $1\in U$，且每个 $u\in U$ 都是原窗口中某个元素与 $w$ 的比值，故 $U\subseteq D$。反之，原窗口任一比值均为两个 $U$ 元素之商，因而

$$
D=F(U).
\tag{27.9}
$$

这同时表明 $D$ 是包含某个窗口标量倍的最小子域：若 $xW\subseteq K$，其中 $K$ 是原 $L$ 中包含 $F$ 的子域、$x\in L^\times$，则窗口比值均属于 $K$，故 $D\subseteq K$。由 $\dim_F U=3$ 得 $h\ge3$，域塔公式给 $h\mid[L:F]$。对每个原 $r\ne0$，

$$
d_W(r)>0
\quad\Longleftrightarrow\quad
r=u/v\quad\text{对某些 }u,v\in W\setminus\{0\}.
\tag{27.10}
$$

确实，非零公共向量可以写成 $u=rv$；反向该等式本身给出公共向量。这证明 (27.4) 的第一式，并说明 $D$ 外的所有二重及三重交叠均为零。特别是当 $D\subsetneq L$ 时，证明没有丢弃原 $L$ 中的其余标签。

消费有限维乘法稳定子的通常事实：$E$ 包含 $F$，对加、减、乘封闭；若 $0\ne a\in E$，则乘以 $a$ 在有限维 $W$ 上单射，故 $aW=W$，从而 $a^{-1}W=W$。所以 $E$ 为域，$W$ 为 $E$-空间，$e\mid3$。又因 $aw\in W$，每个 $a\in E$ 均属于 $D$。$d_W(r)=3$ 恰好表示 $rW=W$，于是得到 (27.4) 的第二式。这些稳定子事实与前节相同，见 Bachoc–Serra–Zémor，[*Revisiting Kneser's theorem for field extensions*，arXiv:1510.01354v2，§2.3 的有限维稳定子说明](https://arxiv.org/pdf/1510.01354v2)，只在此应用内部使用。

若 $e=3$，则 $W=wE$，原比值域就是 $E$，所以 $h=3$。反之，若 $h=3$，则 $U\subseteq D$ 的两边都是三维，故 $U=D$、$W=wD$，稳定子为 $D$。此时 $D^\times$ 中所有标签保持窗口，$D$ 外交叠为零，因而 $\delta_W=3$；取 $u=v=w$ 就有 $W=E_Wu$。这证明三次分支，并排除 $h\ge4$ 时 $e=3$ 的可能，故此后 $E=F$。

对所有 $h\ge3$，为把本原元真正选在原窗口比值内，取 $U$ 的一个 $F$-基 $1,a,b$。由 (27.9)，$D=F(a,b)$。特征零使 $D/F$ 可分；在它的有限正规闭包中，考虑 $D$ 的 $h$ 个 $F$-嵌入。任意两个不同嵌入不可能同时在 $a,b$ 上相等。因而使这两个嵌入在 $a+tb$ 上相等的 $t\in F$ 至多一个。所有嵌入对只排除有限多个 $t$，而 $F$ 无限，故可取原 $t\in F$，使 $\theta=a+tb$ 在这 $h$ 个嵌入下的像两两不同。其最小多项式遂有至少 $h$ 个不同的根，次数又至多 $h$，故 $[F(\theta):F]=h$，即 $F(\theta)=D$。这里是本原元定理的标准有限避集论证；所得 $\theta\in U$、$w\theta\in W$ 都在原域中，正规闭包仅用于证明这次原域选择存在。

若 $h=4$，$U$ 是四维 $D$ 中的三维超平面。对每个 $r\in D^\times$，两个三维空间 $U,rU\subseteq D$ 的交维至少 $3+3-4=2$。交维为三恰好表示 $r\in E^\times=F^\times$；其余 $r\in D^\times$ 的交维因此恰为二。结合 (27.10) 得到 (27.5) 及 $\delta_W=2$。例如刚选出的原 $\theta$ 满足 $\theta\in D\setminus F$，故 $r=\theta=(w\theta)/w$ 就是原域最小正行标签。这一分支不把二维交叠解释成稳定子线。

以下设 $h\ge5$。原 $\theta$ 的次数为 $h$，且 $\theta\in U\cap\theta U$，所以 $d_W(\theta)>0$。因为 $\theta\notin E=F$，该值只能是一或二。若它是一，则

$$
W\cap\theta W=F(w\theta),\qquad
\theta=(w\theta)/w,
\tag{27.11}
$$

已给出所需原域见证 $u=w\theta,v=w$。

若 $d_W(\theta)=2$，则维数公式给出

$$
\dim_F(U+\theta U)=3+3-2=4.
\tag{27.12}
$$

此时直接应用 Napolitano–Polverino–Santonastaso–Zullo，[*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，§6，第 18 页，Proposition 6.3](https://arxiv.org/pdf/2201.02003v1)。将该命题的环境扩张取为原 $L$ 内的子域扩张 $D/F$，取 $S=U$、$k=3$、$T=\operatorname{span}_F\{1,\theta\}$、$\mu=\theta$。逐项有 $\theta\notin F$、$\theta$ 在 $F$ 上代数、$k+2=5\le h=\dim_FD$，且乘积张成 $\langle ST\rangle_F=U+\theta U$ 的维数正是 $k+1$。由于 $[F(\theta):F]=h>k$，该成熟命题的第一分支给出原 $c\in D^\times$，满足

$$
U=c\operatorname{span}_F\{1,\theta,\theta^2\}.
\tag{27.13}
$$

这里使用的是原文明确允许一般域扩张的 Proposition 6.3，不借有限域中的三维分类替代它。选择了生成整个 $D$ 的原 $\theta$，所以该命题中低次数的另一分支无需额外假设就被排除。

因 $h\ge5$，原 $1,\theta,\theta^2,\theta^3,\theta^4$ 在 $F$ 上线性无关。比较这五个系数，(27.13) 便给出

$$
U\cap\theta^2U=Fc\theta^2,\qquad
W\cap\theta^2W=Fwc\theta^2.
\tag{27.14}
$$

取原 $u=wc\theta^2$、$v=wc$，两者都在 $W\setminus\{0\}$，且 $u/v=\theta^2$。因此 $d_W(u/v)=1$，交叠恰为 $E_Wu$。连同 (27.11)，这证明所有 $h\ge5$ 分支的 $\delta_W=1$ 及原窗口见证，完成 (27.3)。该论证不要求 $D=L$；即使 $D$ 是真子域，也只在这同一个原 $D$ 中应用成熟命题，再使用原 $L$ 的合法标签 $\theta$ 或 $\theta^2$。

接着证明 (27.6)。若 $h\ge5$，任意最小正行都有 $W\cap r_0W=Fz$，$z\ne0$。对任一原 $s\ne0$，

$$
\begin{aligned}
J_W(r_0,s)>0
&\Longleftrightarrow Fz\cap sW\ne\{0\}\\
&\Longleftrightarrow z/s\in W.
\end{aligned}
\tag{27.15}
$$

最后一步用 $W$ 的 $F$-线性消去公共非零 $F$ 系数。对原标签取逆，便得 $T_{W,r_0}=z^{-1}W$。这是前卷 §25、前节 (26.28) 已使用的支持取逆机制在一维交叠上的直接消费。

若 $h\in\{3,4\}$，由 (27.10) 知 $r_0\in D^\times$。置 $A=U\cap r_0U$，则 $\dim_FA=\delta_W$。对于 $s\in D^\times$，$A,sU$ 均包含于 $D$，故

$$
\dim_F(A\cap sU)\ge\delta_W+3-h>0.
\tag{27.16}
$$

严格正性在 $h=3$ 时为 $3$，在 $h=4$ 时为 $1$。对于 $s\notin D$，$D\cap sD=\{0\}$：否则非零等式 $a=sb$、$a,b\in D$ 会迫使 $s=a/b\in D$。因此此时 $A\cap sU=\{0\}$。由于整体乘以 $w$ 不改变交维，得到

$$
\{s\in L^\times:J_W(r_0,s)>0\}=D^\times,
\tag{27.17}
$$

而 $D^\times$ 对取逆封闭，故 $T_{W,r_0}=D$。这也解释四次分支为何不能沿用 $T=z^{-1}W$：两边维数分别为四与三。

现在设 (27.7) 左边成立，完整处理全部竞争 $V$。因为 $J_W(r_0,1)>0$，支持相等给出 $V\cap r_0V\ne\{0\}$。仅在证明中取 $0\ne y\in V\cap r_0V$。对每个 $v\in V\setminus\{0\}$，原标签 $s=y/v$ 满足 $y\in V\cap r_0V\cap sV$，故支持相等蕴涵 $s^{-1}=v/y\in T_{W,r_0}$。于是统一得到

$$
y^{-1}V\subseteq T_{W,r_0}.
\tag{27.18}
$$

推导 (27.18) 没有使用 $V$ 的稳定子、比值域、最小正值或 $V\cap r_0V$ 的维数。

若 $h\ge5$，(27.6) 及 (27.18) 给 $y^{-1}V\subseteq z^{-1}W$，两边同为三维，因而相等，$V=(y/z)W$。若 $h=3$，它们给 $y^{-1}V\subseteq D$，同维又给 $V=yD=(y/w)W$。两种情形的标量均属于原 $L^\times$。

若 $h=4$，则 (27.18) 只先给出 $B=y^{-1}V\subseteq D$，其中 $B$ 与 $U$ 都是原四次域 $D/F$ 的 $F$-超平面。这里直接消费前卷 §§20、22、23 已用的乘法配对及超平面的原标量传递性：写 $U=\ker\lambda$、$B=\ker\eta$，其中 $\lambda,\eta:D\to F$ 为非零 $F$-线性泛函。配对 $\lambda(ab)$ 非退化，因为 $a\ne0$ 时可取 $b=t/a$、$\lambda(t)\ne0$。故映射

$$
D\longrightarrow\operatorname{Hom}_F(D,F),\qquad
c\longmapsto\bigl(b\longmapsto\lambda(cb)\bigr)
\tag{27.19}
$$

是四维空间间的线性同构。于是存在原 $c\in D^\times$ 使 $\eta(b)=\lambda(cb)$，从而 $B=c^{-1}U$，得到

$$
V=yB=\frac{y}{cw}W.
\tag{27.20}
$$

所用成熟配对见上述 Bachoc–Serra–Zémor 原文 §2.2；它不要求正规性，也不把超平面等价改成一般线性或半线性等价。这里的 $c$ 位于原 $D\subseteq L$，(27.20) 正是所需原标量轨道。因此四次分支同样完成 (27.7) 的充分方向。

反向，若 $V=xW$、$x\in L^\times$，则乘以 $x$ 将每个 $W\cap rW\cap sW$ 同构到 $V\cap rV\cap sV$，因为原乘法交换；故逐原标签保持全部维数，尤其保持指定行的正支持。这证明 (27.7) 的必要方向及 (27.8) 的反向。若两份完整 $J$ 相等，取 $s=1$ 即得 $d_V=d_W$，可以为 $W$ 选任一最小正行标签，再由 (27.7) 得 $V=xW$。这完成 (27.8) 的证明。$\square$

本定理的文献对应与数学差额。Castello–Polverino–Zullo，[*On one-orbit cyclic subspace codes of $G_q(n,3)$*，arXiv:2405.01652v1，Lemma III.1、Theorem III.2、Lemma III.3、Proposition III.4](https://arxiv.org/pdf/2405.01652v1)，已给有限域中的低交余维结构、三维平方张成分类及四次域超平面的标量等价；这些不作为新的基础。其 Definition II.1 允许域自同构参与半线性等价，而 (27.7)–(27.8) 始终固定每个原标签。该文的码最小距离由 $6-2\dim_F(W\cap rW)$ 对不同轨道点取最小，控制的是相应交叠的最大值，不能直接充当这里的最小正交叠。

同作者 [*Full weight spectrum one-orbit cyclic subspace codes*，arXiv:2405.19911v1，Definition 2.2、Theorem 5.2](https://arxiv.org/pdf/2405.19911v1)，已定义有限域窗口标量倍的最小容纳域，并在 Theorem 5.2 原样调用一般域扩张的 critical-pair 分类。这里的 (27.9) 将该容纳对象落实为原比值域，(27.12)–(27.14) 只消费被该文引用的原 Proposition 6.3。有限域的唯一子域结构、有限域计数及半线性分类均未被当作任意特征零域的前件。

相对于这些指定原文、前卷 §§20、22、23、25 及本卷 §26，本定理的仓内应用推导（repo-derived）差额是全部三维实际窗口的统一连接：原窗口比值内本原元的选择把次数至少五的最小正交叠接到已有 critical-pair 结构；三次、四次与更高次数由 (27.3) 完整分流；四次拥挤分支的行支持虽扩大为整个 $D_W$，却仍由 (27.18) 迫使每个竞争窗口成为同一原四次域中的超平面，进而接回已有的原标量传递性。§26 的半维结论不被用来预设这些非半维分支。这里不主张全球首次性。

白话说，高次数时能在原窗口的两个比值方向中避开有限的重合，使一个原比值生成整个容纳域；一旦交叠只差一维，成熟结构便提供另一个只留一线的原比例。四次时三个方向放在四个位置中，任意最小行的正支持铺满整个容纳域；这虽多出一个方向，却没有多出标量轨道，因为该域内所有超平面都能由原乘法互移。恢复结果因此是窗口的原标量轨道，而不是某个唯一的窗口集合。

本定理仅讨论无限、无噪声、逐原标签精确观察的集合论可识别性。证明中的 $w,\theta,c,y,z$、正规闭包及各超平面泛函均不作为新增观察输入；最终标量始终属于原 $L^\times$。它不提供有限查询、有效恢复算法、噪声结论、二元观察的充分性或三重观察的最小性，也不推出量子公理、$\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义或 $H10(\mathbb Q)$。

## 追加锚（本行以下为增补区）

## 28　全部四维实际窗口的最小交叠与原标签三重恢复

**定义 28.1（四维窗口与固定原标签）。** 固定特征为零的域 $F$ 及有限域扩张 $L/F$。窗口是原 $L$ 中任意满足 $\dim_F W=4$ 的 $F$-线性子空间。全部乘积、商与标量作用均使用这个 $L$ 的原乘法。对原标签 $r,s\in L^\times$，定义

$$
\begin{aligned}
J_W(r,s)&=\dim_F(W\cap rW\cap sW),\\
d_W(r)&=J_W(r,1)=\dim_F(W\cap rW),\\
D_W&=F\bigl(\{u/v:u,v\in W,\ v\ne0\}\bigr)\subseteq L,\\
E_W&=\{a\in L:aW\subseteq W\},\\
N&=[D_W:F],\qquad e=[E_W:F],\\
\delta_W&=\min\{d_W(r):r\in L^\times,\ d_W(r)>0\}.
\end{aligned}
\tag{28.1}
$$

稳定子 $E_W$ 成域的通常事实亦在下述证明中核对；最小值因 $d_W(1)=4$ 而存在。观察输入只有全部原标签上的函数 $J_W$，不附送 $D_W,E_W$、窗口基或共同非零向量。竞争窗口始终为同一原 $L$ 中的四维 $F$-子空间；等价关系仅为 $V=xW$、$x\in L^\times$，不允许重标、半线性或一般线性替换。

**定理 28.2（全部四维窗口的精确结算）。** 对定义 28.1 的每个实际窗口，$F\subseteq E_W\subseteq D_W\subseteq L$，$N\ge4$、$N\mid[L:F]$、$e\mid4$、$e\mid N$，并有

$$
\boxed{\delta_W=\max\{e,\,8-N\}.}
\tag{28.2}
$$

各分支的完整范围为

$$
(e,N,\delta_W)=
\begin{cases}
(4,4,4),&N=4,\\
(2,2n,2),&n\ge3,\\
(1,5,3),&N=5,\\
(1,6,2),&N=6,\\
(1,N,1),&N\ge7.
\end{cases}
\tag{28.3}
$$

这里的范围列出实际窗口可能具有的次数，不断言一份指定 $L/F$ 具有表中所有中间域。存在原 $p,q\in W\setminus\{0\}$，使 $d_W(p/q)=\delta_W$。当 $\delta_W=e$ 时，还可取到

$$
W\cap(p/q)W=E_Wp.
\tag{28.4}
$$

任取 $w\in W\setminus\{0\}$，都有 $U=w^{-1}W\subseteq D_W$ 及 $F(U)=D_W$。原标签直接满足

$$
\begin{aligned}
D_W&=F\bigl(\{r\in L^\times:d_W(r)>0\}\bigr),\\
E_W&=\{0\}\cup\{r\in L^\times:d_W(r)=4\}.
\end{aligned}
\tag{28.5}
$$

当 $r\notin D_W$ 或 $s\notin D_W$ 时，$J_W(r,s)=0$。特别地，$D_W\subsetneq L$ 的情形包含在结论内。

对每一个四维竞争窗口 $V\le_F L$，有

$$
\boxed{
\bigl[\ \forall(r,s)\in(L^\times)^2,\quad J_V(r,s)=J_W(r,s)\ \bigr]
\quad\Longleftrightarrow\quad
\exists x\in L^\times,\quad V=xW.}
\tag{28.6}
$$

证明。先落实比值域、稳定子及次数，再求最小交叠，最后在同一个原域中处理每个竞争窗口。所用分裂、分拆秩公式及乘法配对均只在本四维应用内部消费。

取任意 $w\in W\setminus\{0\}$，缩写 $D=D_W$、$E=E_W$，并令 $U=w^{-1}W$。整体乘原标量不改变 $J,d,E$。由 $1\in U$ 及原比值的定义，$U\subseteq D$，而所有窗口比值又是两个 $U$ 元素之商，故 $D=F(U)$。因此 $N\ge4$，且域塔给出 $N\mid[L:F]$。非零交叠向量恰可写成 $u=rv$、$u,v\in W\setminus\{0\}$，所以

$$
d_W(r)>0\quad\Longleftrightarrow\quad
r=u/v\quad\text{对某些 }u,v\in W\setminus\{0\}.
\tag{28.7}
$$

这给出 (28.5) 的第一式。若 $r\notin D$，则 $D\cap rD=\{0\}$，因为非零等式 $a=rb$、$a,b\in D$ 会迫使 $r=a/b\in D$。对 $U,rU,sU$ 使用此事实，便得所有域外原标签的三重读数为零；没有把这些标签从观察中删去。

消费与 §§26–27 相同的有限维稳定子事实：$E$ 包含 $F$，对加、减、乘封闭；$0\ne a\in E$ 时，乘 $a$ 在有限维 $W$ 上单射，故 $aW=W$、$a^{-1}W=W$，于是 $E$ 是子域。又由 $aw\in W$ 得 $E\subseteq D$。$W$ 为 $E$-空间，所以 $e\mid4$；域塔给 $e\mid N$。$d_W(r)=4$ 恰为 $rW=W$，这证明 (28.5) 的第二式。这些成熟事实的原文为 Bachoc–Serra–Zémor，[*Revisiting Kneser's theorem for field extensions*，arXiv:1510.01354v2，§2.3，Lemma 13 后、Corollary 14 前的有限维说明](https://arxiv.org/pdf/1510.01354v2)；不需要将其饱和空间的特殊对偶结论用于任意窗口。

若 $e=4$，则 $W=wE$，因而 $D=E$、$N=4$。反之，$N=4$ 时 $U=D$，稳定子也为 $D$。若 $e=2$，则 $N$ 是偶数且不能为四，故 $N=2n$、$n\ge3$；余下 $e=1$ 时 $N\ge5$。每个 $W\cap rW$ 都是 $E$-线性的；正交叠的标签属于 $D$，在 $D$ 内两四维空间的交维又至少为 $8-N$。于是所有分支统一具有下界

$$
\delta_W\ge\max\{e,8-N\}.
\tag{28.8}
$$

先完成非平凡稳定子分支。$e=4$ 时，取 $p=q=w$ 即得 $W=Ep$。$e=2$ 时，$U$ 为二维 $E$-空间且含 $1$，写作 $U=E+Et$、$t\notin E$。由 $D=F(U)$、$E\subseteq U$ 得 $D=E(t)$，故 $[E(t):E]=n\ge3$。原 $1,t,t^2$ 在 $E$ 上独立，所以

$$
U\cap tU=Et,\qquad W\cap tW=Ewt.
\tag{28.9}
$$

取原 $p=wt,q=w$，便得 $d_W(p/q)=2$ 及 (28.4)。连同 (28.8)，这结算了 $e=2,4$ 的全部次数，无需对环境 $L$ 作半维假设。

以下设 $e=1$。只在此分支应用 §26 已用的分裂与原系数子式接口，将其中的原乘法空间改为 $D/F$、窗口改为 $U$；不要求 $N=8$。为明确所有前件，取 $D/F$ 的有限正规闭包 $K/F$，令

$$
\Omega=\operatorname{Hom}_F(D,K),\qquad |\Omega|=N,\qquad
D\otimes_F K\simeq K^\Omega.
\tag{28.10}
$$

可分性由特征零给出，右边乘法逐坐标进行。取 $U$ 的 $F$-基 $a_1=1,a_2,a_3,a_4$，令

$$
B=(\sigma(a_j))_{\sigma\in\Omega,\,1\le j\le4},\qquad
b_\sigma=(\sigma(a_1),\ldots,\sigma(a_4)),\qquad
\rho(S)=\dim_K\langle b_\sigma:\sigma\in S\rangle_K.
\tag{28.11}
$$

行拟阵的总秩为四。各行首坐标为一，故无零行；两行若成比例就必相等，进而两个嵌入在 $U$ 上一致，由 $D=F(U)$ 得它们在 $D$ 上一致。因此行拟阵简单：非空秩一子集只能是单点。这一前件来自同一个原比值域，不能以任意抽象拟阵替代。

其连通性仍由 §26 的完整稳定子核接口给出。具体地，原 $F$-线性映射

$$
\Phi:D\longrightarrow\operatorname{Hom}_F(U,D/U),\qquad
c\longmapsto(u\longmapsto cu+U)
\tag{28.12}
$$

的核恰为 $F$。有限矩阵扩底保持核，有限维的 $\operatorname{Hom}$ 与商也同扩底相容，故在 (28.10) 中，$\widetilde U=\operatorname{im}(U\otimes_F K)$ 的整个对角稳定代数为 $K\boldsymbol1$。若存在非空真子集 $S\subsetneq\Omega$ 使 $\rho(S)+\rho(S^c)=4$，则坐标限制

$$
\widetilde U\longrightarrow\pi_S\widetilde U\oplus\pi_{S^c}\widetilde U
$$

单射且两边同维，故满射。将 $S^c$ 坐标置零便保持 $\widetilde U$，产生不属于 $K\boldsymbol1$ 的稳定投影，矛盾。因此不存在这样的直和分解，即行拟阵连通。这控制了扩底后的全部稳定方向，而非仅逐个原标量。

$G=\operatorname{Gal}(K/F)$ 在 $\Omega$ 上传递，且 $g(b_\sigma)=b_{g\sigma}$。域自同构保持子式的零与非零，因此 $\rho(gS)=\rho(S)$。下面只将这种传递性用于同一行族的最优分拆，不假设原窗口一般位置。

在 $K^4\oplus K^4$ 中，对每个 $\sigma$ 取

$$
A_\sigma=K(b_\sigma,0)\oplus K(0,b_\sigma).
$$

由行的简单性，这些二维子空间彼此不同，且 $\dim_K\sum_{\sigma\in S}A_\sigma=2\rho(S)$。令 $X,Y$ 为相互独立的四元不定元，取泛超平面 $H_{X,Y}=\{(a,b):X\cdot a-Y\cdot b=0\}$。直接消费 Raz–Wigderson，[*Subspace arrangements, graph rigidity and derandomization through submodular optimization*，arXiv:1901.09423v1，Definition 5.1、Theorems 5.2、7.1 与 §2 式 (3)](https://arxiv.org/pdf/1901.09423v1)，得到

$$
\begin{aligned}
R&=\dim_{K(X,Y)}\operatorname{span}\{(A_\sigma\otimes_K K(X,Y))\cap H_{X,Y}:\sigma\in\Omega\}\\
 &=\min_{\mathcal P}\sum_{S\in\mathcal P}(2\rho(S)-1).
\end{aligned}
\tag{28.13}
$$

分拆块均非空。法向量 $(X,-Y)$ 是整个超平面空间的泛点，故满足该原文的一般位置前件；这里切的是每个 $A_\sigma$ 后再共同张成。

本四维应用的分拆代价可统一确定。上述原文 Definition 2.1 和 Corollary 3.2 保证：在达到 (28.13) 最小值的分拆中，块数最少者唯一。记它为 $\mathcal P_*$。每个 $g\in G$ 保持代价和块数，故由唯一性得 $g\mathcal P_*=\mathcal P_*$。地集上传递的作用因而在块上也传递：给定两块，取各自的一个元素，再将前者送到后者即可。因此若 $c=|\mathcal P_*|$，各块具有共同秩 $q$，代价为 $c(2q-1)$。

若 $c=1$，代价为七。若 $q=1$，简单性使所有块为单点，代价为 $N$。其余情形 $c,q\ge2$：当 $c=2$ 时，$q=2$ 会使两块秩之和等于总秩四，违反已经验证的连通性，故 $q\ge3$、代价至少十；当 $c\ge3$ 时，代价至少九。而单块分拆已有代价七，这些情形不可能最优。单块及全单点分拆本来都允许，遂有

$$
R=\min\{N,7\}.
\tag{28.14}
$$

这里使用的是成熟的最少块最优分拆唯一性，四维秩、简单性与原稳定子连通性共同排除了其余最优形状；没有枚举原窗口或假设每个抽象拟阵能在原域实现。

最后将 (28.14) 接回原窗口中的原比值。令 $u(X)=\sum X_ja_j$、$v(Y)=\sum Y_ja_j$。直接解超平面上的两个系数，得到

$$
(A_\sigma\otimes_K K(X,Y))\cap H_{X,Y}
=K(X,Y)\bigl((b_\sigma\cdot Y)b_\sigma,(b_\sigma\cdot X)b_\sigma\bigr).
\tag{28.15}
$$

故矩阵 $[\operatorname{diag}(BY)B\mid\operatorname{diag}(BX)B]$ 的秩为 $R$。这正是 Antolini–Dewar–Tanigawa，[*Dilworth truncations and Hadamard products of linear spaces*，arXiv:2508.04798v1，§3.2 式 (7)–(9)](https://arxiv.org/pdf/2508.04798v1) 已有的二因子行与超平面接口在此处的代入；任意特征零底域上的秩公式则由上引 Raz–Wigderson 定理承担，不用复数域的结论冒代原域返回。

固定 $D/F$ 的一个基 $\ell_1,\ldots,\ell_N$，以原乘法坐标组成

$$
\mathcal C(X,Y)=
[\ v(Y)a_1\ \cdots\ v(Y)a_4\mid u(X)a_1\ \cdots\ u(X)a_4\ ]
\in\operatorname{Mat}_{N\times8}(F[X,Y]).
\tag{28.16}
$$

可逆嵌入矩阵 $(\sigma(\ell_i))_{\sigma,i}$ 将它变为 (28.15) 的行矩阵，所以 $\mathcal C$ 有一个非零 $R$ 阶子式 $f\in F[X,Y]$。因 $F$ 无限，非零多项式 $fX_1Y_1$ 可在某个 $x,y\in F^4$ 取非零值。所用无限域多项式事实及其归纳证明与 §26 相同。置原 $u=u(x),v=v(y)\in U\setminus\{0\}$，便有 $\dim_F(vU+uU)\ge R$。另一方面，两者均在 $N$ 维 $D$ 中，且共同含有非零 $uv$，所以该维数至多 $\min\{N,7\}=R$。于是

$$
\dim_F\bigl(U\cap(u/v)U\bigr)
=\dim_F(uU\cap vU)=8-R=\max\{1,8-N\}.
\tag{28.17}
$$

取原 $p=wu,q=wv$，其比值仍为 $u/v$；整体乘 $w$ 得到 $d_W(p/q)=8-R$，与 (28.8) 一起证明 $e=1$ 的 (28.2)。当 $N\ge7$ 时该交为一维，且包含 $p$，故等于 $Fp=Ep$。加上 (28.9) 与四次分支，(28.3)–(28.4) 全部成立。非零子式的系数和取值分别在原 $F$ 与 $F^4$，所以不是把正规闭包中的一般点充作原窗口见证。

(28.3) 的次数范围也确可实现，而非只有形式上的整除条件。在所有窗口的范围内，取 $F=\mathbb Q$、$\theta=2^{1/N}>0$、$D=L=\mathbb Q(\theta)$；$X^N-2$ 的 Eisenstein 判据给 $[D:F]=N$。$N=4$ 时取 $W=D$。每个 $N\ge5$ 时取 $W=\langle1,\theta,\theta^2,\theta^3\rangle_F$，其比值域为 $D$，稳定子为 $F$：稳定元素因 $1\in W$ 可写成次数至多三的多项式；若最高非零次数为 $j\ge1$，乘以窗口中的 $\theta^{4-j}$ 就产生非零的四次项，且 $4<N$，不能仍在 $W$。每个偶数 $N=2n\ge6$ 时，取 $E_0=\mathbb Q(\theta^n)$ 及 $W=E_0+E_0\theta$，则 $[E_0:F]=2$、$[D:E_0]=n\ge3$、$\dim_FW=4$、$D_W=D$。其稳定子包含 $E_0$，次数只能为二或四；次数四已被证明会强迫 $N=4$，故恰为二。这些是纸面构造；在任意包含它们的有限原扩域中，域外零交叠仍由 (28.7) 保证。

现在证明 (28.6)，完整处理竞争窗口。原乘法交换，所以 $V=xW$ 时，乘 $x$ 同构每个对应的二重及三重交叠，因而保持每个原标签的 $J$。以下设两份完整 $J$ 相等。取 $s=1$ 得 $d_V=d_W$，由 (28.5) 得

$$
D_V=D_W=D,\qquad E_V=E_W.
\tag{28.18}
$$

因此竞争窗口也能在同一原 $D$ 内归一化；此结论来自观察相等，不是额外输入或对竞争窗口的限制。

若 $\delta_W=e$，直接消费前卷 §25、本卷 §§26–27 的稳定子线支持恢复。任取最小正行 $r_0$ 及 $0\ne z\in W\cap r_0W$，则 $W\cap r_0W=Ez$。对每个原 $s\ne0$，$W$ 的 $E$-线性给出

$$
J_W(r_0,s)>0
\quad\Longleftrightarrow\quad Ez\cap sW\ne\{0\}
\quad\Longleftrightarrow\quad z/s\in W.
\tag{28.19}
$$

由观察相等可取 $0\ne y\in V\cap r_0V$。任意 $v'\in V\setminus\{0\}$ 给出原标签 $s=y/v'$，使 $y\in V\cap r_0V\cap sV$。由 (28.19) 得 $v'/y\in z^{-1}W$，故 $y^{-1}V\subseteq z^{-1}W$。两边均为四维，遂相等，$V=(y/z)W$。这已经处理 $N=4$、所有 $e=2$ 及 $e=1,N\ge7$，且最终标量属于原 $L^\times$。

尚余且仅余 $e=1,N=5,6$。取任意原 $w\in W\setminus\{0\}$、$y\in V\setminus\{0\}$，令 $U=w^{-1}W$、$B=y^{-1}V$。由 (28.18)，$U,B\subseteq D$ 都是四维空间，且 $d_U=d_B$。以下只在这同一原域 $D$ 中使用成熟乘法配对。取任意非零 $F$-线性泛函 $\lambda:D\to F$，则

$$
\langle a,b\rangle=\lambda(ab)
\tag{28.20}
$$

非退化：若 $a\ne0$，取 $t\in D$ 满足 $\lambda(t)\ne0$，再令 $b=t/a$ 即可。乘法自伴随性给出 $(cA)^\perp=c^{-1}A^\perp$，有限维性给出 $(A^\perp)^\perp=A$。这正是上述 Bachoc–Serra–Zémor 原文 §2.2 式 (2) 的 Frobenius 配对，亦为前卷 §§20、22–24 和本卷 §27 已消费的同一工具；$\perp$ 指通常正交补，不是原文另定义的饱和对偶 $X^*=(XS)^\perp$。

若 $N=5$，$U,B$ 是 $D$ 的两个 $F$-超平面。与 §27 的超平面原标量传递性相同，取 $U=\ker\mu$、$B=\ker\eta$。非退化乘法配对使

$$
D\longrightarrow\operatorname{Hom}_F(D,F),\qquad
c\longmapsto(b\longmapsto\mu(cb))
$$

成为线性同构。故某个原 $c\in D^\times$ 满足 $\eta(b)=\mu(cb)$，于是 $B=c^{-1}U$、$V=(y/(cw))W$。虽然 $\delta_W=3>e$，该分支仍恢复原标量轨道。

若 $N=6$，置 $A=U^\perp$、$C=B^\perp$，它们在原 $D$ 中均为二维。对每个原 $r\in D^\times$，正交补及维数公式给出

$$
\begin{aligned}
d_U(r)
 &=6-\dim_F(A+r^{-1}A)
  =2+\dim_F(A\cap r^{-1}A),\\
d_B(r)
 &=6-\dim_F(C+r^{-1}C)
  =2+\dim_F(C\cap r^{-1}C).
\end{aligned}
\tag{28.21}
$$

由 $d_U=d_B$，并让 $r^{-1}$ 遍历原 $D^\times$，得到 $d_A(t)=d_C(t)$ 对每个 $t\in D^\times$ 成立。取 $C$ 的一个 $F$-基 $c_0,c_1$，令 $t=c_1/c_0\notin F$。则 $c_1\in C\cap tC$，所以 $d_C(t)>0$，进而 $d_A(t)>0$。因此存在原 $a_0,a_1\in A\setminus\{0\}$ 满足 $a_1=ta_0$。由于 $t\notin F$，$a_0,a_1$ 独立，正好组成 $A$ 的基；从而

$$
C=c_0\langle1,t\rangle_F
 =\kappa A,\qquad \kappa=c_0/a_0\in D^\times.
\tag{28.22}
$$

再次取同一配对的正交补得 $B=\kappa^{-1}U$，故 $V=(y/(\kappa w))W$。这没有要求 $F(A)=D$，也没有遗漏 $A$ 的比值域为真子域或其稳定子非平凡的可能；只用了二维基、同一个原比值标签与 (28.21)。因此六次拥挤分支的全部竞争窗口也由原标量连接。所有分支至此穷尽，(28.6) 得证。$\square$

本定理的来源对应与应用差额。Raz–Wigderson 的 Definition 2.1、Corollary 3.2、Definition 5.1、Theorems 5.2、7.1 已分别给出最少块最优分拆的定义及唯一性、一般位置与一刀超平面的分拆秩公式；Antolini–Dewar–Tanigawa 的 §3.2 已给二因子矩阵与超平面的接口。这些结构不作为新基础。可分分裂、完整稳定子核扩底和原系数子式返回已在 §26 使用；乘法配对、正交补、超平面的原标量传递性及稳定子线的支持恢复已在前卷 §§20、22–25 与本卷 §§26–27 使用。《QUANTUM-REALITY》§410 的复记录射线应用也已消费二因子 Dilworth 公式，不承担这里任意特征零原域的返回或窗口轨道结论。

Castello–Polverino–Zullo，[*On one-orbit cyclic subspace codes of $G_q(n,3)$*，arXiv:2405.01652v1，Definition II.1、Lemma III.1、Theorem III.2](https://arxiv.org/pdf/2405.01652v1)，研究有限域的三维结构及允许自同构的等价；其 [*Full weight spectrum one-orbit cyclic subspace codes*，arXiv:2405.19911v1，Definition 2.2、Theorem 5.2](https://arxiv.org/pdf/2405.19911v1) 已给最小容纳域对象，并原样调用 Napolitano–Polverino–Santonastaso–Zullo，[*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，Proposition 6.3](https://arxiv.org/pdf/2201.02003v1) 的一般域 critical-pair 分类。本定理不重立这些工具，也不需要按 critical pair 逐类展开四维窗口。

Shi–Özbudak，[*Linear equivalence of full weight spectrum cyclic orbit codes*，arXiv:2611.04947v1，Theorem 1.1、§2](https://arxiv.org/pdf/2611.04947v1)，分类有限域中两族 full weight spectrum 码的线性等价，并处理真子域参数；其等价允许环境线性同构，结论不覆盖任意四维窗口的逐原标签 $J$。Clarke–Dewar–Gallet–Grasegger–Green Tripp–Smith，[*Counting fibres of the Hadamard product using Bergman fans*，arXiv:2511.22646v1，Problem 1.1、Theorem 1.3](https://arxiv.org/pdf/2511.22646v1)，研究复线性空间 Hadamard 映射的一般纤维及自然环面商；一般纤维的点数不等于全部原窗口的标签恢复。上述有限域结果或一般复纤维结果均不被当作 (28.6) 的替代前提。

相对于这些指定原文和仓内既有结论，本条的仓内应用推导（repo-derived）差额是全部四维实际窗口的完整连接：(28.11) 的简单性由原比值域支付，最优分拆的唯一性与 Galois 传递性把四维的代价压到 (28.14)，原系数子式给出每个次数分支的原窗口见证；低容纳域则由五次超平面和六次二维正交补接回每个竞争窗口的原标量轨道。半维结论没有被扩用成非半维前提，三维结论也没有被当作六次拥挤分支的现成恢复定理。这里不据指定来源中的整体未覆盖主张全球首次性。

白话说，四个方向挤进五个或六个域方向时，最小共享部分会被容量分别托到三维或二维；七个及更多方向时，稳定子之外不再必然多留共享方向。证明把嵌入坐标中“哪些块最合算”交给已有分拆定理，再用同一原域的对称性排除不合适的块，而不是逐个窗口试验。共享部分是一条稳定子域直线时，一行三重支持即可读出共同缩放后的窗口。六次拥挤时这条路线失去条件，但窗口的二维正交补仍能用一个共同原比值连接两组基，再通过同一乘法配对返回窗口。因此“最小交叠大于稳定子次数”不构成恢复反例。

本条只断言全部无限、无噪声、原标签精确读数下的集合论轨道识别。$D,E$、正规闭包、泛参数、子式、配对、正交补和见证向量都是证明对象，不是额外观察，也不改变原 $L^\times$ 的标量群。除 (28.19) 的适用分支外，没有主张一行支持统一足够；(28.21) 仅服务六次分支，不声称完整二元观察对所有四维窗口充分。不提供有限查询、有效算法、噪声结论或三重观察最小性，不扩展到任意维数的同式或任意维数的 $J$ 恢复，也不推出量子公理、$\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义或 $H10(\mathbb Q)$。

## 追加锚（本行以下为增补区）

## 29　最小正交叠的中间域公式与六维、七维分界

**定义 29.1（原标签与中间域张成）。** 设 $F$ 为特征零域，$L/F$ 为有限扩张，$0\ne W\le_F L$，$m=\dim_F W$。沿用 §§26–28 的原乘法、比值域和稳定子，记

$$
\begin{aligned}
D&=F\bigl(\{p/q:p\in W,\ q\in W\setminus\{0\}\}\bigr),&
E&=\{a\in L:aW\subseteq W\},\\
N&=[D:F],& e&=[E:F],\\
d_W(r)&=\dim_F(W\cap rW)\qquad(r\in L^\times),&
\delta&=\min\{d_W(r):r\in L^\times,\ d_W(r)>0\}.
\end{aligned}
\tag{29.1}
$$

对每个实际中间域 $F\subseteq A\subseteq D$，记 $AW=\operatorname{span}_A W\subseteq L$。令 $a(A)=[A:F]$、$t(A)=\dim_F AW-m$。两个端点下界指由 $A=E$ 和 $A=D$ 给出的 $e$ 和 $2m-N$。所有标签均取自原 $L^\times$；由于 $d_W(1)=m>0$，最小值存在。

**定理 29.2（中间域最优值及首个超出端点的维数）。** 对定义 29.1 的每个窗口，

$$
\boxed{\displaystyle
\delta=\max_{F\subseteq A\subseteq D}\bigl(a(A)-2t(A)\bigr).
}
\tag{29.2}
$$

每个中间域项都下界所有正交叠；存在原 $p,q\in W\setminus\{0\}$ 使 $d_W(p/q)=\delta$。特别地，$1\le m\le6$ 时，

$$
\delta=\max\{e,\,2m-N\}.
\tag{29.3}
$$

$m=7$ 时有精确判据

$$
\boxed{\displaystyle
\delta>\max\{e,\,14-N\}
\quad\Longleftrightarrow\quad
N\ge16\quad\text{且存在 } F\subseteq A\subseteq D
\text{ 使 } [A:F]=4,\ \dim_F AW=8 .
}
\tag{29.4}
$$

在 (29.4) 的两端成立时，$e=1$ 且 $\delta=2$；否则 $\delta=\max\{e,14-N\}$。次数条件不保证给定的 $D/F$ 有四次中间域；右端要求原域中确实有满足张成条件的那个域。

**证明。** 先在原域中统一处理所有标签。按 (28.7)，$d_W(r)>0$ 当且仅当 $r=p/q$ 为两个非零窗口元素的原比值；特别是 $D$ 外的原标签交叠皆为零。任取 $w_0\in W\setminus\{0\}$，置 $U=w_0^{-1}W$。和 §28 一样，$1\in U\subseteq D$，$F(U)=D$，而 $d_U=d_W$、$E_U=E$、$\dim_F AU=\dim_F AW$。稳定子成域用 Bachoc–Serra–Zémor [arXiv:1510.01354v2，§2.3，Lemma 13 后的有限维说明](https://arxiv.org/pdf/1510.01354v2)：非零稳定元素在 $W$ 上给出单射，有限维使它满射，故逆元也稳定。由 $a w_0/w_0=a$ 对 $a\in E$ 得 $E\subseteq D$；$W$ 的 $E$-线性及域塔分别给出 $e\mid m$ 和 $e\mid N$。还有 $DW=w_0D$，因为 $1\in U\subseteq D$。这里既不把 $D$ 预设为 $L$，也不把 $E$ 预设为 $F$。

若 $d_W(r)>0$，则 $AW\cap rAW$ 是含非零向量的 $A$-空间，故 $\dim_F(AW\cap rAW)\ge a(A)$。由 $W+rW\subseteq AW+rAW$ 得

$$
d_W(r)=2m-\dim_F(W+rW)
\ \ge\ 2m-\dim_F(AW+rAW)
\ \ge\ a(A)-2t(A).
\tag{29.5}
$$

$A=E$ 时 $t(E)=0$，$A=D$ 时 $t(D)=N-m$，确得两个端点下界。此下界的维数机制见下文 Castello–Polverino–Zullo 的式 (13)。

为证明一个中间域项给出准确值，使用 §§26、28 的分裂与原系数矩阵接口。取 $D/F$ 的有限正规闭包 $K/F$，包含原 $D$；$G=\operatorname{Gal}(K/F)$ 在 $\Omega=\operatorname{Hom}_F(D,K)$ 上按左复合传递作用，$|\Omega|=N$。取 $U$ 的 $F$-基 $u_1=1,u_2,\ldots,u_m$，记 $b_\sigma=(\sigma(u_1),\ldots,\sigma(u_m))$，$\rho(S)=\dim_K\langle b_\sigma:\sigma\in S\rangle_K$。特征零保证可分分裂 $D\otimes_F K\simeq K^\Omega$，故 $\rho(\Omega)=m$。各行首坐标为一；若两行成比例，则两嵌入在 $U$ 上相同，因 $F(U)=D$ 而是同一嵌入。因而 $P_\sigma=K(b_\sigma,0)\oplus K(0,b_\sigma)$ 是一族不同的二维子空间，非空子族 $S$ 的张成维数为 $2\rho(S)$。

取独立的 $m$ 元不定元组 $X,Y$。在 $K(X,Y)$ 上，法向量为 $(X,-Y)$ 的超平面切每个 $P_\sigma$，所得直线的行向量为 $((b_\sigma\cdot Y)b_\sigma,(b_\sigma\cdot X)b_\sigma)$，即 (28.15) 的二因子接口。它们的秩为

$$
R=\min_{\mathcal P}\ \sum_{S\in\mathcal P}(2\rho(S)-1),
\tag{29.6}
$$

其中 $\mathcal P$ 遍历 $\Omega$ 的非空块分拆。这里直接使用 Raz–Wigderson [arXiv:1901.09423v1，式 (3)、Definition 5.1、Theorems 5.2、7.1](https://arxiv.org/pdf/1901.09423v1) 的 Lovász 超平面公式：有限非零子空间族在特征零的 $K$ 上，两个独立参数组给出整个超平面参数空间的泛法向量，故满足 Definition 5.1 的一般位置条件。每块的代价是它所含子空间的总张成维数减一。

由同一原文 Definition 2.1、Corollary 3.2，达到 (29.6) 且块数最少的分拆 $\mathcal P_*$ 唯一。对 $g\in G$，$g(b_\sigma)=b_{g\sigma}$，故 $\rho(gS)=\rho(S)$；于是 $g\mathcal P_*=\mathcal P_*$。现在把这个不变分拆接到原中间域。令 $S_0$ 为包含原包含嵌入 $\iota:D\hookrightarrow K$ 的块，$H=\{g\in G:gS_0=S_0\}$。任何固定 $\iota$ 的 $g$ 都保持 $S_0$，故 $\operatorname{Gal}(K/D)\subseteq H$。反过来，任一 $\sigma\in S_0$ 可写成 $g\iota$；此时 $gS_0$ 和 $S_0$ 同含 $\sigma$，从而 $g\in H$。由 Galois 对应，

$$
A=K^H,\qquad F\subseteq A\subseteq D,\qquad
S_0=\{g\iota:g\in H\}=\operatorname{Hom}_A(D,K).
\tag{29.7}
$$

最后一个等式中，$A$ 在 $K$ 内按原包含嵌入，固定 $A$ 的嵌入可延拓到 $K$ 的自同构。其余块是 $S_0$ 的 $G$-平移，故块数是 $[G:H]=[A:F]$，且各块秩相等。

为计算该秩，对 $D/A$ 使用同一个分裂 $D\otimes_A K\simeq K^{S_0}$。矩阵 $(\sigma(u_j))_{\sigma\in S_0,j}$ 的列空间正是 $AU\otimes_A K$ 的像：$u_j$ 张成 $AU$，每个 $\sigma$ 在 $A$ 上都是包含嵌入，扩底后 $A$ 系数成为 $K$ 系数。由扩底保持包含及行列秩相等，$\rho(S_0)=\dim_A AU$。写 $a=[A:F]$、$k=\dim_A AU$，则

$$
R=a(2k-1),\qquad
2m-R=a-2(ak-m)=a(A)-2t(A).
\tag{29.8}
$$

因此最优分拆给出的值来自原 $D$ 内的实际中间域及同一窗口的张成，不是用可整除次数代替域。

为取得原标签，记 $u(X)=\sum_j X_j u_j$、$v(Y)=\sum_j Y_j u_j$。以任一 $D/F$ 基记下各列 $v(Y)u_j$ 和 $u(X)u_j$ 的原乘法矩阵。其系数在 $F[X,Y]$；左乘可逆的嵌入矩阵就得到 (29.6) 所用的行矩阵。因此原矩阵有非零 $R$ 阶子式 $f\in F[X,Y]$，且更高阶子式恒零。按 §26 的无限域子式返回，$fX_1Y_1$ 在某个 $x,y\in F^m$ 非零。取 $u=u(x),v=v(y)$，均为原 $U$ 中的非零向量，有 $\dim_F(vU+uU)=R$。乘 $v^{-1}$ 接回原比值，得 $d_U(u/v)=2m-R$，为正是因为 $uv\in vU\cap uU$ 非零。令 $p=w_0u$、$q=w_0v$，则 $p/q=u/v$ 且 $d_W(p/q)=2m-R$。这与 (29.5)、(29.8) 合起来证明 (29.2) 和原域可达性。

接下来设某个 $m$ 发生 $\delta>\max\{e,2m-N\}$，取 (29.2) 的取等中间域 $A$，仍写 $a=[A:F]$、$k=\dim_A AU$，并令 $t=ak-m$。若 $t=0$，则 $AW=W$，$A\subseteq E$，该项至多 $e$；故 $t\ge1$。若 $k=1$，则 $1\in U$ 使 $AU=A$，由 $F(U)=D$ 得 $A=D$，该项是 $2m-N$；故 $k\ge2$。严格超过 $e\ge1$ 给出 $a-2t\ge2$。从而

$$
m=ak-t\ \ge\ 2a-t\ \ge\ 3t+4\ \ge\ 7 .
\tag{29.9}
$$

这证明 (29.3)，包括非平凡稳定子及真比值子域。若 $m=7$，(29.9) 处处取等，强制 $t=1$、$a=4$、$k=2$，于是 $\dim_F AW=8$、$\delta=2$、$e=1$。又因 $2>14-N$，有 $N>12$；$4\mid N$ 便给出 $N\ge16$。反之，若右端的实际中间域存在，$t(A)=1$，由 (29.5) 每个正交叠至少为二。因 $e\mid7$，若 $e\ne1$ 则 $W=w_0E$，进而 $D=E$、$N=7$，与 $N\ge16$ 矛盾。所以 $e=1$，且 $14-N\le-2$，二严格超过端点。已经证明的取等分析随即给出 $\delta=2$。$\square$

**命题 29.3（同一十六次域内的同参数分离）。** 取 $\alpha^{16}=2$，$F=\mathbb Q$、$L=\mathbb Q(\alpha)$，令 $\beta=\alpha^4$、$A=\mathbb Q(\beta)$。设

$$
B=\ker\operatorname{Tr}_{A/\mathbb Q},\qquad
W=B\oplus A\alpha,\qquad
V=\langle 1,\alpha,\ldots,\alpha^6\rangle_{\mathbb Q}.
\tag{29.10}
$$

两者的 $(m,N,e)$ 都是 $(7,16,1)$，但 $\delta_W=2$、$\delta_V=1$。所有原正交叠标签分别满足 $d_W(r)\ge2$ 和 $d_V(r)\ge1$，且两个界都在 $L^\times$ 中取到。具体地，

$$
r_0=\frac{\alpha^4}{\alpha^8+\alpha},\qquad
W\cap r_0W=\langle\alpha^4,\alpha^8\rangle_{\mathbb Q},
\qquad
V\cap\alpha^6V=\mathbb Q\alpha^6 .
\tag{29.11}
$$

**证明。** $x^{16}-2$ 和 $x^4-2$ 在素数二处满足 Eisenstein 判据，故 $[L:\mathbb Q]=16$、$[A:\mathbb Q]=4$，$[L:A]=4$。在 $A$ 的幂基 $1,\beta,\beta^2,\beta^3$ 中，乘 $\beta^j$（$1\le j\le3$）的矩阵对角线全为零，因为 $\beta^4=2$ 且指数模四移位；乘 $1$ 的迹为四。故 $B=\langle\beta,\beta^2,\beta^3\rangle_{\mathbb Q}$。$1,\alpha,\alpha^2,\alpha^3$ 在 $A$ 上独立，因而 $W$ 为直和，维数七，$AW=A\oplus A\alpha$ 的 $\mathbb Q$-维数八。$V$ 的七个幂向量亦独立。

$W$ 的比值域含 $\alpha^5/\alpha=\beta$ 和 $\alpha/\beta$，因为 $\alpha,\alpha^5\in A\alpha$ 且 $\beta\in B$，故含 $\alpha$；$V$ 的比值域也含 $\alpha/1$。两者都等于原 $L$。由 $e\mid m$ 与 $e\mid N$，两稳定子均为 $\mathbb Q$。对于每个原 $r$，若 $W\cap rW\ne\{0\}$，在 (29.5) 取这个 $A$ 给出 $d_W(r)\ge4-2(8-7)=2$。而 $V$ 的每个非零交维至少为一。

对 $W$，设 $q_0=\beta^2+\alpha\in W\setminus\{0\}$，则 $r_0=\beta/q_0\in L^\times$，且对任一 $x=b+c\alpha\in W$（$b\in B,c\in A$），$x\in r_0W$ 等价于 $q_0x\in\beta W$。展开得

$$
q_0 x=\beta^2 b+(b+\beta^2 c)\alpha+c\alpha^2,\qquad
\beta W=\beta B\oplus A\alpha .
\tag{29.12}
$$

由 $1,\alpha,\alpha^2$ 在 $A$ 上独立，条件等价于 $c=0$ 且 $\beta b\in B$。在 $B$ 的基 $\beta,\beta^2,\beta^3$ 中，只有最后一个方向乘 $\beta$ 会产生非零常数项，故 $b\in\langle\beta,\beta^2\rangle_{\mathbb Q}$。这证明 (29.11) 的第一个交叠等式。对 $V$，$\alpha^6V=\langle\alpha^6,\ldots,\alpha^{12}\rangle_{\mathbb Q}$，原域的十六个幂基向量中两组只共用 $\alpha^6$，故得第二个等式。两者各自达到全体正标签的下界。$\square$

**原文对应与应用差额。** §§26–28 已给出半维、三维和全部四维的最小交叠，且 (28.10)–(28.16) 已将同一原乘法矩阵接到分拆秩、最少块唯一性与原系数子式。Raz–Wigderson 的 Definition 2.1 和 Corollary 3.2 保证的是最少块最优分拆的唯一性；Definition 5.1 与 Theorems 5.2、7.1 给出超平面的前件、维数及其泛性。Antolini–Dewar–Tanigawa [arXiv:2508.04798v1，§3.2，式 (7)–(9)](https://arxiv.org/pdf/2508.04798v1) 对两个复线性空间的基矩阵与各自泛点给出二因子行和超平面对应；这里两基矩阵均为 $(\sigma(u_j))_{\sigma,j}$，而两个参数组仍独立。Bernstein [arXiv:2003.10529v4，Theorem 3.1](https://arxiv.org/pdf/2003.10529v4) 给出两个不落在坐标超平面内的复线性空间的 Hadamard 像的代数拟阵，即相应秩和减一的 Dilworth 拟阵；这里首基向量 $1$ 满足无零坐标投影条件。在任意特征零辅助域上的秩等式使用 Raz–Wigderson 的原定理。上述原文中的超平面、分拆和二因子公式均是先例；从最优块到原比值域的固定域、再到张成维数的 (29.7)–(29.8) 才给出此处的域解释。Bachoc–Serra–Zémor 除有限维稳定子事实外，Theorems 2–3 控制的是普通乘积张成 $ST$ 及其稳定子，未给出对所有正比值取最小的 (29.2)。

De Beule–Demuys–Polverino–Zullo，[*Few-Weight Linear Sets and Divisibility of Rank-Metric Codes*，arXiv:2611.08044v1，Theorem 3.7](https://arxiv.org/pdf/2611.08044v1)，给出直接的有限域对应。具体地，改在 $F=\mathbb F_q$、$D=\mathbb F_{q^N}$，取归一化的 $m$ 维窗口 $X\le_F D$，原文的环境向量空间 $V_{\mathrm{src}}$ 取 $D^2$，定义空间 $U_{\mathrm{src}}=X\times X$。原文的 $S=\langle U_{\mathrm{src}}\rangle_D=D^2$，因为两个坐标轴均有非零窗口向量，所以 $h=2$。原文扩张次数 $m_{\mathrm{src}}=N$、秩 $N_{\mathrm{src}}=2m$；其 $q\ge m_{\mathrm{src}}$、$N_{\mathrm{src}}\le(h-1)m_{\mathrm{src}}$ 分别成为 $q\ge N$、$2m\le N$。原文点权是与一条 $D$-直线的 $F$-交维：对 $D(r,1)$，以第一坐标同构到 $X\cap rX$，非零斜率的权就是 $d_X(r)$；两轴权皆为 $m$，不降低最小正权，故原文的 $a_{\mathrm{src}}=\delta_X$。若另有原环境扩域，域外比值标签仍全为零。

在这些假设及 $a_{\mathrm{src}}>1$ 下，原文给出实际子域 $A=\mathbb F_{q^t}\subseteq D$，$t\mid N$，使 $W_{\mathrm{src}}=\langle U_{\mathrm{src}}\rangle_A=(AX)\times(AX)$ 定义相同的点集，并可取到相对 $A$ 权一的点。原文证明先保持点集而逐步扩大定义域，再用相对权一的点集基数下界与原最小权的基数上界，最后在原最小权点将交的商空间嵌入 $W_{\mathrm{src}}/U_{\mathrm{src}}$，得到精确秩
$\dim_F W_{\mathrm{src}}=N_{\mathrm{src}}+t-a_{\mathrm{src}}$，且 $t\mid(N_{\mathrm{src}}-a_{\mathrm{src}})$、$a_{\mathrm{src}}\le t\le N_{\mathrm{src}}-a_{\mathrm{src}}$。代入即得 $\delta_X=t-2(\dim_F AX-m)$；再合用 (29.5) 的维数下界，就得到这个有限域范围内的同一个取等极值。$\delta_X=1$ 时，$A=F$ 已取等。Csajbók–Marino–Pepe [arXiv:2306.07488v2，Theorems 1–2](https://arxiv.org/pdf/2306.07488v2) 的 Theorem 1 在秩为扩张次数整数倍且最小正权 $w\ge2$ 时，给出 $w$ 整除扩张次数且原定义空间本身为 $\mathbb F_{q^w}$-线性。其 Theorem 2 在 $q\ge m_{\mathrm{src}}$、秩至多 $(h-1)m_{\mathrm{src}}$、最小正权至少二时给出保持点集的子域张成；后者正是上述放大步骤所用的原文结果。有限域的点数论证不适用于 (29.1) 的任意特征零底域，且其秩前提不含 $2m>N$。这里求的是交维极值，不声称保持放大后的整个点集。

Castello–Polverino–Zullo 的 [arXiv:2405.19911v1，Definition 2.2、Theorems 4.4、5.2、6.3(ii) 及式 (13)](https://arxiv.org/pdf/2405.19911v1) 已在有限域定义相应的中间域张成维数，最小可容纳标量倍窗口的子域正是归一化窗口的生成域。Theorem 6.3(ii) 的条件是 $S=\overline S\oplus b\langle1,\lambda,\ldots,\lambda^{j-1}\rangle_{\mathbb F_q}$，其中 $\overline S$ 是 $\mathbb F_{q^t}$-空间，$\overline S\cap b\mathbb F_{q^t}=0$，$\mathbb F_q(\lambda)=\mathbb F_{q^t}\subseteq\mathbb F_{q^n}$，且 $(t+1)/2<j<t$（$j$ 对应原文的截短维数 $m$）。对应 (29.10) 的形状是 $t=4$、$j=3$、$\dim_A\overline S=1$、$\overline S=A\alpha$、$b=\lambda=\beta$，因为 $B=\beta\langle1,\beta,\beta^2\rangle_F$；原文的 $Y=\langle S\rangle_{\mathbb F_{q^t}}$ 对应 $AW$。式 (13) 的 $2j-2t+\dim_F(Y\cap rY)$ 在此给出正交叠至少二，正是 (29.5) 的同一维数机制。Theorem 4.4 已给有限域幂基窗口的完整距离分布；其 $k=7$、生成域次数 $t=16$ 满足 $1<k<t$ 及 $k\le t/2$，交维一对应距离 $2(k-1)$，在原公式中确实出现。它与 (29.11) 的幂基取等同型。

上述 Theorem 5.2 引自 Napolitano–Polverino–Santonastaso–Zullo [arXiv:2201.02003v1，Proposition 6.3](https://arxiv.org/pdf/2201.02003v1)。这是一般域上的临界对分类，前提为 $\mu\notin F$ 且 $\mu$ 在 $F$ 上代数、$\dim_F L\ge k+2$ 及 $\dim_F(S+\mu S)=k+1$，其中 $k=\dim_F S$；它分类的是已给出一个交维 $k-1$ 的标签的形状。对 (29.10)，分别取 $\mu=\beta$ 和 $\mu=\alpha$，两个和空间都为八维：前者 $B+\beta B=A$ 且 $A\alpha$ 保持，后者是 $1$ 到 $\alpha^7$ 的幂张成。因而两种形状本身都落在该原文的分类内，分类前提并不结算最小正交叠。

Castello–Polverino–Zullo [arXiv:2405.01652v1，Definition II.1、Lemma III.1、Theorem III.2、Lemma III.3、Proposition III.4](https://arxiv.org/pdf/2405.01652v1) 的交维 $k$ 或 $k-1$ 的结构、三维平方张成和超平面标量等价属于有限域；三维分类的半线性等价容许域自同构。Shi–Özbudak [arXiv:2611.04947v1，Theorem 1.1、§2](https://arxiv.org/pdf/2611.04947v1) 分类有限域两个全重量谱族各自的线性等价，分别有幂基次数条件及二次子域加一维的条件；§2 的生成域约化处理真子域。两者均未在任意特征零的原域中给出这里的七维充要条件。Clarke–Dewar–Gallet–Grasegger–Green Tripp–Smith [arXiv:2511.22646v1，Theorem 1.3](https://arxiv.org/pdf/2511.22646v1) 计数复线性空间 Hadamard 映射在泛目标处模环面缩放的纤维，所计对象是乘积的分解类，未给出原域商标签的交叠极值。

本节相对于上述指定原文及 §§26–28 的仓内推导（repo-derived）是：在全部特征零窗口中将最优分拆下降为实际中间域，并取到原比值；把端点首次失效精确定位为 (29.4) 的四次域条件；在同一原数域给出 (29.11) 的两个不同最小值及其具体交空间。中间域放大的维数下界、有限域的取等公式与两类窗口的形状均有上述先例。这里的文献对应不主张全球优先权。

白话说，原窗口在一个中间域下补齐以后，只要两份有任何交叠，补齐后的交叠便至少含一条该域上的直线。这条直线给出域次数那么多的底域方向；从两份空间各减去补入的方向，仍能得到原交叠的下界。分拆定理保证总有一个实际中间域的下界能在原窗口取到。要压过两个端点，至少要补一个方向，域次数至少为四，补齐后的窗口还至少要有两条该域上的独立方向。这首次用得上七维窗口：八个方向缺一个，最小仍须共享两个；在同一十六次域里的七维幂基窗口却只须共享一个。

本节只讨论精确的原标签交维及其最小正值，不给出任意维数的三重观察恢复、有限查询、算法或噪声结论。

## 追加锚（本行以下为增补区）

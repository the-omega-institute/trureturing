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

为把本原元真正选在原窗口比值内，取 $U$ 的一个 $F$-基 $1,a,b$。由 (27.9)，$D=F(a,b)$。特征零使 $D/F$ 可分；在它的有限正规闭包中，考虑 $D$ 的 $h$ 个 $F$-嵌入。任意两个不同嵌入不可能同时在 $a,b$ 上相等。因而使这两个嵌入在 $a+tb$ 上相等的 $t\in F$ 至多一个。所有嵌入对只排除有限多个 $t$，而 $F$ 无限，故可取原 $t\in F$，使 $\theta=a+tb$ 在这 $h$ 个嵌入下的像两两不同。其最小多项式遂有至少 $h$ 个不同的根，次数又至多 $h$，故 $[F(\theta):F]=h$，即 $F(\theta)=D$。这里是本原元定理的标准有限避集论证；所得 $\theta\in U$、$w\theta\in W$ 都在原域中，正规闭包仅用于证明这次原域选择存在。

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

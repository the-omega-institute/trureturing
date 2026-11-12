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

## 30. 不同实际窗口的中间域公式与首个八维混合结构

**定义 30.1（两窗口、独立归一化与原标签）。** 设 $F$ 为特征零域，$L/F$ 为有限扩张，$W,V\le_F L$ 非零，$m=\dim_F W$、$n=\dim_F V$。乘除和张成始终使用这个原 $L$ 的运算。记

$$
\begin{aligned}
D_W&=F(W/W),&D_V&=F(V/V),&D&=F(W/W,V/V),&N&=[D:F],\\
E_W&=\{c\in L:cW\subseteq W\},&
E_V&=\{c\in L:cV\subseteq V\},&E&=E_W\cap E_V,&e&=[E:F],\\
d_{W,V}(r)&=\dim_F(W\cap rV)\quad(r\in L^\times),&&&
\delta&=\min\{d_{W,V}(r):r\in L^\times,\ d_{W,V}(r)>0\}.
\end{aligned}
\tag{30.1}
$$

这里 $W/W$、$V/V$ 的分母只取非零元素；$D$ 是两个实际比值域在 $L$ 内的合成域。最小值存在，因为任取 $p\in W\setminus\{0\}$、$q\in V\setminus\{0\}$，都有 $p\in W\cap(p/q)V$。对每个实际中间域 $F\subseteq A\subseteq D$，定义

$$
\begin{aligned}
AW&=\operatorname{span}_A W\subseteq L,&AV&=\operatorname{span}_A V\subseteq L,\\
a(A)&=[A:F],&t_W(A)&=\dim_F AW-m,&t_V(A)&=\dim_F AV-n,\\
\Lambda(A)&=a(A)-t_W(A)-t_V(A).
\end{aligned}
\tag{30.2}
$$

独立选取原 $w_0\in W\setminus\{0\}$、$v_0\in V\setminus\{0\}$ 后，置 $X=w_0^{-1}W$、$Y=v_0^{-1}V$。于是 $1\in X\cap Y$、$X,Y\subseteq D$、$F(X,Y)=D$，而原标签 $r$ 的归一化标签为

$$
\rho=(v_0/w_0)r,\qquad
W\cap rV=w_0(X\cap\rho Y).
\tag{30.3}
$$

因此独立缩放保持最小正值和两个个别稳定子，改变的却是标签与原标量的对应。对于原 $L$ 中的每个 $r\ne0$，

$$
\begin{aligned}
d_{W,V}(r)>0
&\Longleftrightarrow r=p/q\text{，其中 }p\in W\setminus\{0\},\ q\in V\setminus\{0\}\\
&\Longleftrightarrow \rho=x/y\text{，其中 }x\in X\setminus\{0\},\ y\in Y\setminus\{0\}.
\end{aligned}
\tag{30.4}
$$

正交叠迫使 $\rho\in D^\times$，并不迫使 $r\in D$。所有正原标签位于 $(w_0/v_0)D^\times$；这个陪集之外的原标签交维全为零。$D\subsetneq L$ 仍在定义范围内。

**定理 30.2（两实际窗口的精确中间域极值）。** 对定义 30.1 的全部窗口对，包括 $W\ne V$、$m\ne n$ 及非平凡个别稳定子的情形，

$$
\boxed{\displaystyle
\delta=\max_{F\subseteq A\subseteq D}
\left([A:F]-(\dim_F AW-m)-(\dim_F AV-n)\right).
}
\tag{30.5}
$$

每个中间域项都下界每一个正原标签的交维；且存在原 $p\in W\setminus\{0\}$、$q\in V\setminus\{0\}$ 使 $d_{W,V}(p/q)=\delta$。特别地，

$$
\delta\ge\max\{e,m+n-N\}.
\tag{30.6}
$$

证明。按 §§26–29 已用的有限维稳定子事实，$E_W,E_V$ 是域：非零稳定元素在相应有限维空间上单射，故满射，逆元也稳定。又 $c\in E_W$ 蕴含 $c=(cw_0)/w_0\in D_W$，同理 $E_V\subseteq D_V$；所以 $E\subseteq D$，$e$ 整除 $m,n,N$。两个原空间及其每个交叠都是 $E$-线性的。由 (30.3)，只须对含 $1$ 的 $X,Y\subseteq D$ 建立极值与原域见证；$\dim_F AX=\dim_F AW$、$\dim_F AY=\dim_F AV$，因为原标量乘法给出对应的线性同构。

先保留每个原标签。若 $W\cap rV\ne\{0\}$，则 $AW\cap rAV$ 是非零 $A$-空间，故其 $F$-维数至少为 $a(A)$。由 $W+rV\subseteq AW+rAV$ 及维数公式，

$$
\begin{aligned}
d_{W,V}(r)
&=m+n-\dim_F(W+rV)\\
&\ge m+n-\dim_F(AW+rAV)\\
&\ge m+n-\dim_F AW-\dim_F AV+a(A)=\Lambda(A).
\end{aligned}
\tag{30.7}
$$

这一步允许 $r\notin D$。取 $A=E$ 时两项损失均为零，取 $A=D$ 时 $DW=w_0D$、$DV=v_0D$，分别得到 $e$、$m+n-N$。这是 §29 的中间域维数下界在两个空间上的同一用法。

以下消费 §29 的可分分裂、最少块最优分拆及原系数子式接口，明确两组不同空间所需的对应。取包含原 $D$ 的有限正规闭包 $K/F$，令 $G=\operatorname{Gal}(K/F)$、$\Omega=\operatorname{Hom}_F(D,K)$。选 $X,Y$ 的 $F$-基 $x_1=1,x_2,\ldots,x_m$ 及 $y_1=1,y_2,\ldots,y_n$，写

$$
\begin{aligned}
b_\sigma&=(\sigma(x_1),\ldots,\sigma(x_m)),&
c_\sigma&=(\sigma(y_1),\ldots,\sigma(y_n)),\\
\rho_X(S)&=\dim_K\langle b_\sigma:\sigma\in S\rangle_K,&
\rho_Y(S)&=\dim_K\langle c_\sigma:\sigma\in S\rangle_K.
\end{aligned}
\tag{30.8}
$$

可分分裂 $D\otimes_F K\simeq K^\Omega$ 给出总秩 $m,n$。在 $K^m\oplus K^n$ 中令 $P_\sigma=K(b_\sigma,0)\oplus K(0,c_\sigma)$。每个 $P_\sigma$ 二维，且这些空间互异：若 $P_\sigma=P_\tau$，限制到两个直和因子分别使 $b_\sigma,b_\tau$ 及 $c_\sigma,c_\tau$ 成比例；两基的首项均为 $1$，比例只能为一。两嵌入因而在 $X,Y$ 上一致，$F(X,Y)=D$ 再使 $\sigma=\tau$。这里不要求任意一个空间单独生成 $D$。

取独立的不定元组 $z=(z_1,\ldots,z_m)$、$h=(h_1,\ldots,h_n)$，令 $\mathcal K=K(z,h)$、$u(z)=\sum z_jx_j$、$v(h)=\sum h_jy_j$。对子空间族 $\{P_\sigma\}$ 使用泛超平面 $z\cdot a-h\cdot b=0$，切出的直线由

$$
\bigl((c_\sigma\cdot h)b_\sigma,\ (b_\sigma\cdot z)c_\sigma\bigr)
\tag{30.9}
$$

张成。各点积均为非零多项式。两组参数的合并法向量是整个超平面参数空间的泛点，故满足 Raz–Wigderson [arXiv:1901.09423v1，Definition 5.1、Theorems 5.2、7.1](https://arxiv.org/pdf/1901.09423v1) 的前件；特征零是其泛性结论允许的特征。非空子族 $S$ 的总张成维数恰为 $\rho_X(S)+\rho_Y(S)$。因此 (30.9) 所成行矩阵的秩为

$$
R=\min_{\mathcal P}\sum_{S\in\mathcal P}
\bigl(\rho_X(S)+\rho_Y(S)-1\bigr),
\tag{30.10}
$$

其中块非空。这里正是 Antolini–Dewar–Tanigawa [arXiv:2508.04798v1，§3.2，式 (7)–(9)](https://arxiv.org/pdf/2508.04798v1) 的两个不同基矩阵接口；一般超平面的秩结论直接由上引特征零定理承担。

原文 Raz–Wigderson 的 Definition 2.1、Corollary 3.2 保证最优分拆中块数最少者 $\mathcal P_*$ 唯一。$G$ 同时半线性地置换两组行，保持 $\rho_X,\rho_Y$，故保持 $\mathcal P_*$。按 (29.7) 的固定域构造，令 $S_0$ 为包含原包含嵌入的块，$H=\{g\in G:gS_0=S_0\}$。则 $\operatorname{Gal}(K/D)\subseteq H$，且

$$
A=K^H\subseteq D,\qquad
S_0=\operatorname{Hom}_A(D,K),\qquad
|\mathcal P_*|=[A:F].
\tag{30.11}
$$

为核对该构造并未制造子域，若 $\sigma\in S_0$，取 $g\in G$ 使 $g\iota=\sigma$，则 $gS_0$ 与 $S_0$ 相交，因而相等，所以 $g\in H$；反方向由 $H$ 稳定该块立即成立。其余块为 $S_0$ 的平移。对子扩张 $D/A$ 使用同一个分裂，分别得到

$$
\rho_X(S_0)=\dim_A AX=k,\qquad
\rho_Y(S_0)=\dim_A AY=\ell.
\tag{30.12}
$$

理由与 (29.8) 相同：在固定 $A$ 的各嵌入上，原基向量列的 $K$-张成分别是 $AX\otimes_A K$、$AY\otimes_A K$ 的分裂像。扩底保持维数。各块的两个秩也分别相同，所以写 $a=[A:F]$ 后，

$$
R=a(k+\ell-1),\qquad
m+n-R=a-(ak-m)-(a\ell-n)=\Lambda(A).
\tag{30.13}
$$

最后落实原域可达性。在原 $D/F$ 的任一固定基下，写出列为 $v(h)x_1,\ldots,v(h)x_m,u(z)y_1,\ldots,u(z)y_n$ 的矩阵 $\mathcal C(z,h)$。其系数在 $F[z,h]$；可逆的嵌入矩阵将其变为 (30.9) 的行矩阵，故原矩阵有一个非零 $R$ 阶子式 $f\in F[z,h]$，更高阶子式恒零。$F$ 无限，§26 已用的非零多元多项式取值事实使 $fz_1h_1$ 在某个 $(z^0,h^0)\in F^m\times F^n$ 非零。于是原 $u=u(z^0)\in X\setminus\{0\}$、$v=v(h^0)\in Y\setminus\{0\}$ 满足

$$
\dim_F(vX+uY)=R,\qquad
\dim_F\bigl(X\cap(u/v)Y\bigr)=m+n-R>0.
\tag{30.14}
$$

末项为正，因为 $uv\in vX\cap uY$ 非零。取原 $p=w_0u$、$q=v_0v$，则其原标签为 $p/q=(w_0/v_0)(u/v)$，(30.3) 给出 $d_{W,V}(p/q)=m+n-R$。结合 (30.7)、(30.13)，有

$$
\max_B\Lambda(B)\le\delta\le m+n-R=\Lambda(A)
\le\max_B\Lambda(B),
$$

故所有不等式取等，(30.5) 及原窗口比值见证均成立。最大值由 (30.11) 的一个实际中间域达到。$\square$

本定理保留几个退化接口。若 $m=1$ 或 $n=1$，每个正交维都为一，故 $\delta=1$，且 (30.5) 的 $A=F$ 已取等。若两窗口分别为同一个实际子域 $B/F$ 的标量倍，则归一化后 $X=Y=B$、$D=E=B$，正原标签恰为 $(w_0/v_0)B^\times$，其交维全为 $[B:F]$。若只知道共同稳定子 $E$，(30.6) 仍保留该域所强制的整倍数与下界，但不把它当作完整极值。取 $W=V$ 并用相同归一化，(30.5) 还原 (29.2)；不同窗口使用的两个损失则可不相等。

**定理 30.3（严格超过两端点的最小总维数及全部取等结构）。** 在定义 30.1 的所有实际窗口对中，发生

$$
\delta>\max\{e,m+n-N\}
\tag{30.15}
$$

所需的最小总维数为 $m+n=8$。对 $m+n=8$，(30.15) 当且仅当：原 $D$ 内存在实际中间域 $A$，$[A:F]=3$，且交换两窗口并分别归一化后，属于下列两种形状之一：

$$
\begin{array}{ll}
(m,n)=(2,6):&1\in X\subseteq A,\quad\dim_F X=2,\quad Y=A\oplus A\beta;\\[2mm]
(m,n)=(3,5):&X=A,\quad
1\in Y\subseteq A\oplus A\beta,\quad
Y\text{ 是其中的 }F\text{-超平面}.
\end{array}
\tag{30.16}
$$

两支均要求 $\beta\in D\setminus A$、$D=A(\beta)$、$[D:A]\ge3$。这些条件是原域中的存在条件，不能用 $3\mid N$、$N\ge9$ 替代。在且仅在这些情形，$\delta=2$、$e=1$，(30.5) 的取等中间域唯一，恰为此 $A$。归一化不改个别稳定子；按 (30.16) 的顺序，它们分别为

$$
(E_W,E_V)=(F,A)\quad\text{或}\quad(A,F).
\tag{30.17}
$$

证明。令 $s=m+n$，假设 (30.15)，取 (30.5) 的一个取等域 $A$，并写

$$
a=[A:F],\quad k=\dim_A AX,\quad\ell=\dim_A AY,\quad
t=ak-m,\quad u=a\ell-n,\quad T=t+u.
\tag{30.18}
$$

损失 $t,u$ 为非负整数。若 $T=0$，两空间都被 $A$ 稳定，故 $A\subseteq E$、$\Lambda(A)=a\le e$，矛盾。因此 $T\ge1$。若 $k+\ell=2$，两者只能各为一；$1\in X\cap Y$ 使 $AX=AY=A$，从 $F(X,Y)=D$ 得 $A=D$，于是 $\Lambda(A)=s-N$，也矛盾。因此 $k+\ell\ge3$。又 $\Lambda(A)=a-T=\delta\ge2$，所以

$$
s=a(k+\ell)-T\ge3a-T
\ge3(T+2)-T=2T+6\ge8.
\tag{30.19}
$$

这排除一切总维数小于八的实际窗口，不依赖次数表或窗口枚举。若 $s=8$，(30.19) 处处取等，强制

$$
T=1,\quad a=3,\quad k+\ell=3,\quad\delta=2,\quad e=1.
\tag{30.20}
$$

交换窗口后令 $k=1,\ell=2$。$t+u=1$ 只有 $(t,u)=(1,0)$、$(0,1)$ 两种，分别给 $(m,n)=(2,6)$、$(3,5)$。$AX=A$，故 $X\subseteq A$；第一种中 $Y=AY$，第二种中 $X=A$、$Y$ 是 $AY$ 的 $F$-超平面。$AY$ 含 $1$ 且在 $A$ 上二维，故可写成 $A\oplus A\beta$。

第一种的 $X$ 含某个 $x\notin F$。三次域没有非平凡真中间域，故 $F(X)=A$。第二种已有 $X=A$。因此两种均由 $F(X,Y)=D$ 得 $D=A(\beta)$：$Y$ 的 $A$-张成包含 $\beta$，而 $X,Y\subseteq A(\beta)$。严格不等式还给出 $2>8-N$，即 $N>6$；由实际域塔 $3\mid N$ 得 $N\ge9$、$[D:A]\ge3$。这证明必要性，而非只构造充分例子。

反过来，设原域中具有 (30.16) 的某种形状及所列域条件。$1,\beta,\beta^2$ 在 $A$ 上独立。令 $Z=A\oplus A\beta$，其乘法稳定子恰为 $A$：若 $cZ\subseteq Z$，由 $1\in Z$ 可写 $c=a_0+a_1\beta$；再用 $c\beta\in Z$ 及上述独立性得 $a_1=0$。任何稳定 $Y$ 的原元素也稳定 $AY=Z$，所以 $E_Y\subseteq A$。在 $(2,6)$ 分支，$Y=Z$，故 $E_Y=A$；$E_X\subseteq A$ 的次数同时整除二与三，故 $E_X=F$。在 $(3,5)$ 分支，$E_X=A$，而 $E_Y\subseteq A$ 的次数同时整除五与三，故 $E_Y=F$。这证明 (30.17)，尤其共同稳定子为 $F$。上述次数约束仅用于已经存在的稳定子域。

两个分支都有 $T=1$、$\Lambda(A)=3-1=2$，由 (30.7) 得每个正原标签交维至少二。又 $N\ge9$，两端点的最大值为一，故已经严格超过端点。将已证的必要性 (30.20) 用于这同一个窗口对，得到准确的 $\delta=2$。

最后证明取等域唯一，而非仅选定一个域。若另一个实际中间域 $B$ 在 (30.5) 取等，则对 $B$ 重复 (30.18)–(30.20)，也有 $[B:F]=3$、总损失一、两边 $B$-秩之和三。在 (30.16) 的既定顺序中，$m\le3<n$；若小空间的 $B$-秩为二，其维数至少为 $2\cdot3-1=5$，矛盾。因此 $BX=B$，即 $X\subseteq B$。$(2,6)$ 支中 $F(X)=A$，$(3,5)$ 支中 $X=A$，所以均有 $A\subseteq B$。两者次数同为三，遂 $A=B$。下一个命题在同一原数域内实现两种形状，因而八确实是可达的最小总维数。$\square$

**命题 30.4（同一十八次原域中的两支及全部原标签）。** 取实正根 $\eta^{18}=2$，令

$$
\begin{aligned}
F&=\mathbb Q,&L&=\mathbb Q(\eta),&\alpha&=\eta^2,&t&=\alpha^3,\\
A&=\mathbb Q(t),&D&=\mathbb Q(\alpha),&
H&=\langle1,t\rangle_{\mathbb Q},&Z&=A\oplus\alpha A,\\
W&=\eta A,&V&=A\oplus\alpha H,&
W'&=\eta H,&V'&=Z.
\end{aligned}
\tag{30.21}
$$

这是同一个原 $L/F$ 内的实际构造，$[L:F]=18$、$[D:F]=9$、$[A:F]=3$、$[D:A]=3$、$D\subsetneq L$。$(W,V)$ 的维数为 $(3,5)$、个别稳定子为 $(A,\mathbb Q)$、个别比值域为 $(A,D)$；$(W',V')$ 的相应数据为 $(2,6)$、$(\mathbb Q,A)$、$(A,D)$。两对的合成比值域都是 $D$、共同稳定子都是 $\mathbb Q$、最小正交维都是二。

对于每个原 $r\in L^\times$，令 $s=\eta/r$。第一对的完整原标签公式为

$$
d_{W,V}(r)=
\begin{cases}
0,&s\notin Z,\\
3,&s\in A^\times,\\
2,&s\in Z\setminus A.
\end{cases}
\tag{30.22}
$$

更准确地，当 $s=c+\alpha d\in Z\setminus A$、$c,d\in A$、$d\ne0$ 时，$W\cap rV=\eta d^{-1}H$；当 $s\in A^\times$ 时，该交为 $\eta A$。特别地，

$$
r=\eta/\alpha=1/\eta\notin D,\qquad
W\cap rV=\eta H.
\tag{30.23}
$$

第二对的完整公式为

$$
W'\cap rV'=
\begin{cases}
\{0\},&s\notin Z,\\
\eta H,&s\in Z\setminus\{0\}.
\end{cases}
\tag{30.24}
$$

所以第二对所有正原标签的交维均为二。两对的全部正原标签集合都恰为 $\{\eta/s:s\in Z\setminus\{0\}\}$，且其中每一个都在 $D$ 外。

证明。$x^{18}-2$、$x^9-2$、$x^3-2$ 都在素数二处满足 Eisenstein 判据，分别给出 $L,D,A$ 的次数。原包含关系 $A\subseteq D\subseteq L$ 及域塔给出 $[D:A]=3$、$[L:D]=2$，所以 $\eta\notin D$，且 $1,\alpha,\alpha^2$ 在 $A$ 上独立。由此 $Z$ 是六维直和，$V$ 是五维直和；$W,W'$ 分别为三维、二维。$H$ 含 $1,t$，所以 $F(H)=A$，且其稳定子 $E_H\subseteq A$ 的次数整除二和三，故为 $\mathbb Q$。$A$ 自身的稳定子为 $A$；整体乘 $\eta$ 不改稳定子，故 $E_W=A$、$E_{W'}=\mathbb Q$。

按定理 30.3 证明中 $Z$ 的稳定子计算，$E_Z=A$。若 $cV\subseteq V$，则 $cAV\subseteq AV$，而 $AV=Z$，故 $c\in A$。此时 $cV\subseteq V$ 又要求 $cH\subseteq H$，因此 $c\in\mathbb Q$。于是 $E_V=\mathbb Q$、$E_{V'}=A$。所有稳定子都在原 $L$ 中计算，没有只在 $D$ 中检验而漏掉原环境元素。

两小窗口的比值域分别为 $F(A/A)=A$ 和 $F(H/H)=A$，因子 $\eta$ 在比值中消去。$V,V'$ 都含 $1$ 和 $\alpha$，且都包含于 $D$，所以其比值域恰为 $D$。合成比值域因而确为九次真子域 $D$。用 $w_0=\eta$、$v_0=1$ 作独立归一化，第一对成为 $(A,A\oplus\alpha H)$，第二对成为 $(H,Z)$，两种 (30.16) 均在同一原域内实现。此处归一化标签是 $\rho=r/\eta=1/s$。

为逐原标签证明 (30.22)，对任意原 $r\ne0$ 有精确等式

$$
W\cap rV=\eta\{a\in A:sa\in A\oplus\alpha H\}.
\tag{30.25}
$$

若右侧有非零 $a$，则 $s=a^{-1}(sa)\in AV=Z$；因此 $s\notin Z$ 时交为零，包括 $s\notin D$ 的所有情形。若 $s=c+\alpha d\in Z\setminus\{0\}$，则

$$
sa=ca+\alpha da\in A\oplus\alpha H
\quad\Longleftrightarrow\quad da\in H.
\tag{30.26}
$$

这里直和性保证条件等价。$d=0$ 时 $s\in A^\times$，任意 $a\in A$ 都满足；$d\ne0$ 时允许的 $a$ 恰为 $d^{-1}H$，维数二。代入 $s=\alpha$ 即得 (30.23) 的交空间；若 $1/\eta\in D$，取逆会给出 $\eta\in D$，与次数矛盾。这证明第一对所有原标签的公式与域外取等见证。

第二对同样满足

$$
W'\cap rZ=\eta\{h\in H:sh\in Z\}.
\tag{30.27}
$$

若有非零 $h$，则 $h\in A^\times$、$s=h^{-1}(sh)\in Z$。反之，若 $s\in Z\setminus\{0\}$，$Z$ 的 $A$-线性使 $sH\subseteq Z$，故整个 $H$ 都满足。这证明 (30.24)。两对全部正标签都有 $s\in Z\setminus\{0\}\subseteq D^\times$；若其中某个 $r=\eta/s$ 也在 $D$，则 $\eta=rs\in D$，矛盾。因而正原标签在这两个例子中全部位于 $D$ 外，尽管归一化后的每个正标签都在 $D$ 内。$\square$

**原文对应与应用差额。** 定理 30.2 使用的两空间分拆秩已有完整先例：Bernstein [*Generic symmetry-forced infinitesimal rigidity: translations and rotations*，arXiv:2003.10529v4，Theorem 3.1](https://arxiv.org/pdf/2003.10529v4) 对两个不包含于任何坐标超平面的复线性空间给出 $M(U\star V)=M(r_U+r_V-1)$；Antolini–Dewar–Tanigawa 的 [*Dilworth truncations and Hadamard products of linear spaces*，arXiv:2508.04798v1，Theorem 1.1、§3.2](https://arxiv.org/pdf/2508.04798v1) 已用两个不同基矩阵及独立泛参数给出 (30.9) 的接口。本节的首基向量 $1$ 保证各坐标投影非零，并不要求两个空间相同。该文 §4 反驳的是一般三个或更多因子的猜想，不否定二因子定理。任意特征零 $F$ 上使用的泛超平面秩与最少块唯一性，分别由 Raz–Wigderson [*Subspace arrangements, graph rigidity and derandomization through submodular optimization*，arXiv:1901.09423v1，Theorems 5.2、7.1 及 Corollary 3.2](https://arxiv.org/pdf/1901.09423v1) 承担。它们不是本节新增的基础。

有限域也已有整体取等公式，而非只有若干 mixed 例子。De Beule–Demuys–Polverino–Zullo [*Few-Weight Linear Sets and Divisibility of Rank-Metric Codes*，arXiv:2611.08044v1，Theorem 3.7](https://arxiv.org/pdf/2611.08044v1) 的原假设为：$q\ge M$，$U\le_{\mathbb F_q}\mathcal V$，$S=\langle U\rangle_{\mathbb F_{q^M}}$，$h=\dim_{\mathbb F_{q^M}}S\ge2$，$R_0=\dim_{\mathbb F_q}U\le(h-1)M$，最小正点权 $a_0>1$。它对任意这样的 $h$ 给出实际子域 $B=\mathbb F_{q^b}\subseteq\mathbb F_{q^M}$，使 $U_B=\langle U\rangle_B$ 定义相同点集、具有相对 $B$ 权一的点，并且

$$
\dim_{\mathbb F_q}U_B=R_0+b-a_0,\qquad
b\mid(R_0-a_0),\qquad a_0\le b\le R_0-a_0.
\tag{30.28}
$$

对原点集的每个正点 $P$，$U_B\cap P$ 至少有 $b$ 个底域方向，而 $(U_B\cap P)/(U\cap P)$ 嵌入 $U_B/U$，所以点权至少为 $b-(\dim_{\mathbb F_q}U_B-R_0)$。该论证对每个实际中间域成立，(30.28) 又给出一个取等域；故原文已经推出其整个适用范围内的最小正点权中间域最大值公式。$a_0=1$ 时底域本身取等，无须应用其 $a_0>1$ 的结论。这一先例不限于 $h=2$，本节不将它作为新定理。

具体对 mixed 窗口改用 $D=\mathbb F_{q^N}$、$U=X\times Y\subseteq D^2$，有 $M=N$、$h=2$、$R_0=m+n$。点 $D(\rho,1)$ 的权由第一坐标同构到 $X\cap\rho Y$；两个坐标轴的权分别为 $m,n$，均不小于 $\delta$，所以最小正点权恰为 $\delta$。上述原假设成为 $q\ge N$、$m+n\le N$。$U_B=(BX)\times(BY)$，代入 (30.28) 正好得到 $\delta=b-(\dim_F BX-m)-(\dim_F BY-n)$；合用逐点的商空间下界即得这个有限域范围内完整的 mixed 公式。Van de Voorde–Zullo [*On the weight distribution of linear sets with complementary weights and related constructions*，arXiv:2511.20057v1，Theorem 3.2、Corollary 3.3、Lemma 3.6](https://arxiv.org/pdf/2511.20057v1) 已给 Cartesian 定义空间的逐权集合刻画及交维接口。若其约定要求先列较大空间，可以交换两个坐标。两轴始终保留其各自权；例如 $(2,6)$ 分支的轴权是二与六，不能将 mixed 非轴点常权二说成所有点都常权二。

Jena–Van de Voorde [*On linear sets of minimum size*，arXiv:2005.10931v2，Theorem 2.7](https://arxiv.org/pdf/2005.10931v2) 已构造可规定重权的有限域最小大小线性集并计算其权分布。Zullo–Polverino–Santonastaso–Sheekey [*Two-weight rank-metric codes*，arXiv:2405.02841v1，Corollary III.3、Remark III.4、Theorem IV.8](https://arxiv.org/pdf/2405.02841v1) 区分常正点权、权皆为某整数的倍数及两重量码；Remark III.4 的 Cartesian 例子已有不同正权，常权结论不能移用于不同轴权的本节构造。有限域的计点、保持点集及码分类假设不承担定理 30.2 在任意特征零原域中的返回。

部分子域方向与截短方向的结构同样已有一般域先例。Napolitano–Polverino–Santonastaso–Zullo [*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，Examples 6.2、6.4、Proposition 6.3](https://arxiv.org/pdf/2201.02003v1) 构造并分类 $S+\mu S$ 仅比 $S$ 多一维的临界对；其中 $\mu$ 在底域上代数，Proposition 6.3 另要求 $\dim_F L\ge\dim_F S+2$。Example 6.4 已明确使用三次域 $\mathbb Q(\sqrt[3]{2})$ 及其完整方向加截短方向。命题 30.4 的 $A\oplus\alpha H$ 正属此类形状：$\mu=t$、$S=A\oplus\alpha H$ 时，$S+tS=Z$ 为六维，且原 $L$ 十八维满足该维数前件。Castello–Polverino–Zullo [*Full weight spectrum one-orbit cyclic subspace codes*，arXiv:2405.19911v1，Definition 2.2、Theorem 5.2、式 (13)](https://arxiv.org/pdf/2405.19911v1) 已使用中间域张成、同一一般域临界对分类和补维损失下界。它们给出这些形状及维数机制的先例，不能把本节的窗口构造本身称作首次发现。

相对于这些原文和固定的 §§28–29，本节的仓内应用推导（repo-derived）差额为：在同一原特征零扩张中将两组不同窗口的最优分拆下降到共同的实际中间域，分别计算两边损失并取到原 $W/V$ 见证；由此穷尽总维数八的两种取等形状，确定唯一取等域及不同的个别稳定子；在一个九次真比值子域和十八次原环境中，给出 (30.22)、(30.24) 的全原标签公式。两个独立归一化标签的关系由 (30.3) 保留，域外原标签由 (30.23) 实现。这里不以指定文献中的未覆盖推断全球优先权。

白话说，两扇不同窗口可以借用同一个较大的标量域来补齐，但两边付出的补齐代价不必一样。八维是第一次能够以一个三次域提供三个共同方向、只花一个补维方向、最后强制留下两个共享方向的总规模。这个唯一的一份损失放在小窗口，就得到二维对六维；放在大窗口，就得到三维对五维。分拆秩保证这种补齐下界确实可达，取等分析保证没有遗漏同规模的其他结构。原窗口各自带着的缩放因子仍留在原标签上，因此归一化标签属于比值域，并不妨碍真正取等的原标签在比值域之外。

本节仅讨论精确的原标签交维及其最小正值。所有中间域与张成都取自同一个实际对象，不以次数条件制造子域；可分分裂与泛参数只用于证明，原域非零子式提供合法见证。本节不处理完整窗口轨道或 $J$ 恢复，不给出有限查询、算法、噪声、物理或量子结论，也不外推至 $\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义或 $H10(\mathbb Q)$。

## 追加锚（本行以下为增补区）

## 31. 同一窗口的三元阈值与同原域的最小值分离

**定义 31.1（共同见证、独立缩放与端点）。** 设 $F$ 为特征零域，$L/F$ 为有限扩张，$h\ge1$ 为整数，$W_i\le_F L$ 为非零窗口，$m_i=\dim_F W_i$。令

$$
\begin{aligned}
D_i&=F(W_i/W_i),&D&=F(W_i/W_i:1\le i\le h),&N&=[D:F],\\
E_i&=\{c\in L:cW_i\subseteq W_i\},&E&=\bigcap_{i=1}^h E_i,&e&=[E:F].
\end{aligned}
\tag{31.1}
$$

比值的分母只取非零元素，所有域和窗口均取自原 $L$。对任意原标签元组 $r=(r_2,\ldots,r_h)\in(L^\times)^{h-1}$，约定 $r_1=1$，记 $I(r)=\bigcap_i r_iW_i$、$d(r)=\dim_F I(r)$、$\delta_h=\min_{d(r)>0}d(r)$。正标签存在；事实上 $d(r)>0$ 当且仅当有同一组非零 $p_i\in W_i$ 使 $r_i=p_1/p_i$ 对每个 $i\ge2$ 成立。此时 $p_1\in I(r)$。当 $h=1$ 时标签为空元组、交空间就是 $W_1$。当各 $W_i$ 都等于 $W$ 时写 $\delta_h(W)$。

若独立替换 $W_i$ 为 $c_iW_i$，其中 $c_i\in L^\times$，原元组 $r$ 对应新元组 $((c_1/c_i)r_i)_{i\ge2}$，新交空间恰为 $c_1 I(r)$。特别地，任取非零 $b_i\in W_i$，置 $X_i=b_i^{-1}W_i$，则 $1\in X_i\subseteq D_i$、$F(X_i)=D_i$（$W_i/W_i=X_i/X_i$），且对所有原标签，包括零交叠的标签，有

$$
\rho_i=(b_i/b_1)r_i,\qquad
I(r)=b_1\bigcap_{i=1}^h \rho_iX_i,\qquad
r_i=(b_1/b_i)\rho_i
\quad(\rho_1=1).
\tag{31.2}
$$

若交叠为正，则由同一见证 $p_1$ 得 $\rho_i=(p_1/b_1)/(p_i/b_i)\in D^\times$。这只限制归一化标签；原标签在相应的 $(b_1/b_i)D^\times$ 中，不必在 $D$ 中。各 $E_i$ 是子域：非零稳定元素在 $W_i$ 上的乘法单射故满射，逆元也稳定；又 $c=(cb_i)/b_i\in D_i$ 对 $c\in E_i$ 成立。独立缩放不改各 $E_i$，也不改 $D_i$。每个 $I(r)$ 是 $E$-空间，故正维数是 $e$ 的正倍数。

对实际中间域 $F\subseteq A\subseteq D$，记 $AW_i=\operatorname{span}_A W_i$、$a(A)=[A:F]$、$t_i(A)=\dim_F AW_i-m_i$、$\Lambda_h(A)=a(A)-\sum_i t_i(A)$。独立缩放保持各损失，因为 $A X_i=b_i^{-1}AW_i$。$A=E$ 和 $A=D$ 分别给出 $\Lambda_h(E)=e$ 和 $\Lambda_h(D)=\sum_i m_i-(h-1)N$；后一式用 $DW_i=b_iD$。

**定理 31.2（三份同一窗口的首次严格超额）。** 在定义 31.1 中取三份同一窗口 $W$，记 $m=\dim_F W$、$D=F(W/W)$、$E=E_W$。当 $m\le8$ 时，

$$
\delta_3(W)=\max\{e,3m-2N\}.
\tag{31.3}
$$

当 $m=9$ 时，$\delta_3(W)>\max\{e,27-2N\}$ 当且仅当 $N\ge15$，且在原 $D$ 内存在实际中间域 $F\subseteq A\subseteq D$，使 $[A:F]=5$、$\dim_F AW=10$。在这两条件成立时，$e=1$、$\delta_3(W)=2$；其余九维窗口仍满足 (31.3)。

证明。先把 §§29–30 的中间域极值用到共同见证。对任意有限个窗口，只要 $w\in I(r)\setminus\{0\}$，就有 $Aw\subseteq r_i AW_i$ 对每个 $i$ 成立。考虑同时取商类的 $F$-线性映射

$$
Aw\longrightarrow \bigoplus_{i=1}^h r_i AW_i/r_iW_i,\qquad
x\longmapsto(x+r_iW_i)_i.
$$

其核为 $Aw\cap I(r)$，值域所在空间的维数为 $\sum_i t_i(A)$，而 $\dim_F Aw=a(A)$。因此每个正原标签元组都满足

$$
d(r)\ge\Lambda_h(A)\qquad(F\subseteq A\subseteq D).
\tag{31.4}
$$

同一个 $w$ 同时支撑所有商空间约束；分别取得的二元最小值不能代替它。

为在原域中取等，沿用 §29 的可分分裂与最优块下降、§30 的独立归一化，但用同一个核约束所有份额。$h=1$ 时，(31.4) 的 $A=D$ 一项已经等于 $m_1$，任意非零原 $p_1\in W_1$ 都见证正交叠。以下设 $h\ge2$。令 $M=\sum_i m_i$，取 $D/F$ 的有限正规闭包 $K$，记 $G=\operatorname{Gal}(K/F)$、$\Omega=\operatorname{Hom}_F(D,K)$。对各 $X_i$ 取 $F$-基 $x_{i1}=1,x_{i2},\ldots,x_{im_i}$。令 $b_{i,\sigma}=(\sigma(x_{ij}))_j$ 为第 $i$ 个坐标块中的行，令 $\widetilde b_{i,\sigma}$ 为在 $K^M$ 的该块外补零的行。对非空 $S\subseteq\Omega$ 记

$$
P_\sigma=\bigoplus_{i=1}^h K\widetilde b_{i,\sigma},\qquad
q_i(S)=\dim_K\langle b_{i,\sigma}:\sigma\in S\rangle_K,\qquad
\dim_K\sum_{\sigma\in S}P_\sigma=\sum_i q_i(S).
\tag{31.5}
$$

每个 $P_\sigma$ 维数为 $h$。若两空间相等，则逐块的两行成比例，且首坐标为 $1$ 使比例为一。因 $F(X_1,\ldots,X_h)=D$，对应嵌入相等，故这是一族互异的子空间。

取全部代数独立的不定元 $z=(z_{ij})$，写 $u_i(z)=\sum_j z_{ij}x_{ij}$，并在 $K(z)^M$ 中用法向量 $z$ 的一个超平面 $H_z$。在第 $\sigma$ 处，记 $U_{i,\sigma}=\sum_j z_{ij}\sigma(x_{ij})$；每个 $U_{i,\sigma}$ 非零。切面 $(P_\sigma\otimes_K K(z))\cap H_z$ 的一组基是

$$
U_{1,\sigma}\widetilde b_{i,\sigma}
  -U_{i,\sigma}\widetilde b_{1,\sigma},
\qquad 2\le i\le h.
\tag{31.6}
$$

确实，在 $P_\sigma$ 的系数坐标中，唯一方程是 $\sum_i U_{i,\sigma}c_i=0$，且 $U_{1,\sigma}\ne0$，可用后 $h-1$ 个坐标自由表示。这里切面是共同核方程的行空间来源。Raz–Wigderson [arXiv:1901.09423v1，Definition 5.1、Theorems 5.2、7.1](https://arxiv.org/pdf/1901.09423v1) 给出其张成的分拆秩：该子空间族在 $K$ 上定义，法向量取整个参数空间的泛点，特征零下满足该一般位置条件。由 (31.5)，(31.6) 全部行的秩为

$$
R=\min_{\mathcal P}\sum_{S\in\mathcal P}
       \left(\sum_i q_i(S)-1\right),
\tag{31.7}
$$

其中 $\mathcal P$ 遍历 $\Omega$ 的非空块分拆。两份时，(31.6) 在第一块改符号后正是 §30 的两块行式；这里没有迭代取 Hadamard 积。

由同一原文 Definition 2.1、Corollary 3.2，(31.7) 的最少块取等分拆唯一。$G$ 传递地作用于嵌入，并同时半线性地置换各窗口的行，所以保持各 $q_i$ 及该分拆。依 (29.7)、(30.11)，令 $S_0$ 为含原包含嵌入 $\iota$ 的块，$J_0=\{g\in G:gS_0=S_0\}$。固定 $\iota$ 的 $g$ 保持 $S_0$，所以 $\operatorname{Gal}(K/D)\subseteq J_0$。若 $\sigma=g\iota\in S_0$，则 $gS_0$ 与 $S_0$ 相交从而相等；反之 $g\in J_0$ 蕴含 $g\iota\in S_0$。因此 $A=K^{J_0}$ 是原 $D$ 中的实际中间域，$S_0=\operatorname{Hom}_A(D,K)$；其他块是它的平移，块数为 $[G:J_0]=[A:F]$。

在 $S_0$ 上，$D\otimes_A K\simeq K^{S_0}$ 的分裂把 $(AX_i)\otimes_A K$ 的像张成在列 $(\sigma(x_{ij}))_{\sigma\in S_0}$ 上。这是因为原 $x_{ij}$ 张成 $AX_i$ 作为 $A$-空间，并且扩底保持其维数。因此 $q_i(S_0)=\dim_A AX_i$，每个平移块也有相同的各 $q_i$。代入 (31.7)，得

$$
R=[A:F]\left(\sum_i\dim_A AX_i-1\right),\qquad
M-R=\Lambda_h(A).
\tag{31.8}
$$

接下来在 $D/F$ 的固定 $F$-基下，写出下列映射对原系数向量 $(v_i)_i$ 的矩阵：

$$
\bigoplus_{i=1}^h X_i\longrightarrow D^{h-1},\qquad
(v_i)_i\longmapsto (u_1(z)v_i-u_i(z)v_1)_{i=2}^h .
\tag{31.9}
$$

这里以多项式 $z$ 为系数；矩阵条目在 $F[z]$。在每个输出块改用 $D\otimes_F K\simeq K^\Omega$ 的嵌入坐标，所得行恰为 (31.6)。这是可逆的扩底坐标变换，因此 (31.9) 有一个非零 $R$ 阶子式 $f\in F[z]$，且更高阶子式恒零。特征零使 $F$ 无限，非零多元多项式 $f\prod_i z_{i1}$ 在某个原 $F$ 系数元组上非零（逐变量用非零一元多项式根数有限）。在该元组处，各 $u_i\in X_i$ 非零、秩仍为 $R$。此时 (31.9) 的核经第一坐标同构于

$$
X_1\cap\bigcap_{i=2}^h(u_1/u_i)X_i,\qquad
v_1\longmapsto\bigl(v_1,\bigl((u_i/u_1)v_1\bigr)_{i=2}^h\bigr).
$$

确切地说，后 $h-1$ 个坐标各为 $(u_i/u_1)v_1$，而条件正是它们分别落在 $X_i$。核含非零元组 $(u_i)_i$。返回原域取 $p_i=b_i u_i\in W_i\setminus\{0\}$，所有原标签同时取 $r_i=p_1/p_i$，由 (31.2) 得 $d(r)=M-R>0$。连同 (31.4)、(31.8)，这给出本应用所需的精确等式及取等：

$$
\delta_h=\max_{F\subseteq A\subseteq D}
   \left([A:F]-\sum_{i=1}^h(\dim_F AW_i-m_i)\right).
\tag{31.10}
$$

特别地，$h=2$ 还原 (30.5)。对任意 $h$，若有一个窗口一维，则每个正交维都为一、$F$ 已取等。不同稳定子只通过实际交域 $E$ 给出共同线性，$D$ 可以是 $L$ 的真子域。

现在令三份窗口相同。若严格超出 (31.3) 的右端，取 (31.10) 中一个取等域 $A$。写 $a=[A:F]$、$k=\dim_A AW$、$t=ak-m$。若 $t=0$，则 $AW=W$，所以 $A\subseteq E$，其项至多为 $e$。若 $k=1$，归一化的 $X=b_1^{-1}W$ 含 $1$，故 $AX=A$，从 $D=F(X)$ 得 $A=D$，其项是 $3m-2N$。两种情况均不能严格超额，因而 $t\ge1$、$k\ge2$。又 $a-3t=\delta_3(W)\ge2$，从而

$$
m=ak-t\ge2a-t\ge 2(3t+2)-t=5t+4\ge9.
\tag{31.11}
$$

所以 $m\le8$ 时只能等于端点最大值。若 $m=9$ 而严格超额，(31.11) 各步必须取等，故 $t=1$、$a=5$、$k=2$、$\delta_3(W)=2$，并由 $1\le e<2$ 得 $e=1$。严格超出 $27-2N$ 给出 $2N>25$；实际域塔给出 $5\mid N$，所以 $N\ge15$。

反之，若 $m=9$、$N\ge15$ 且所述实际 $A$ 存在，$W$ 和 $AW$ 都是 $E$-空间：若 $c\in E$，交换乘法给出 $cAW\subseteq AW$。所以 $e$ 同时整除 $9$ 和 $10$，即 $e=1$。两端点的最大值为一，而 (31.4) 对每个正原标签给出 $5-3(10-9)=2$ 的下界，故严格超额。上面取等分析又给出准确值二。这证明了必要及充分两向；次数整除只用于已有的实际域塔。下一个命题在原数域内实现严格超额，故首次维数确为九。$\square$

**命题 31.3（同原域、同二元最小值的严格三元分离）。** 取实正根 $\alpha^{15}=2$，令

$$
F=\mathbb Q,\quad L=\mathbb Q(\alpha),\quad
\beta=\alpha^3,\quad A=\mathbb Q(\beta),\quad
B=\ker\operatorname{Tr}_{A/\mathbb Q},\quad
W=B\oplus A\alpha,\quad V=\langle 1,\alpha,\ldots,\alpha^8\rangle_{\mathbb Q}.
\tag{31.12}
$$

两个窗口的 $(m,N,e)$ 都是 $(9,15,1)$，且 $\delta_2(W)=\delta_2(V)=3$、$\delta_3(W)=2$、$\delta_3(V)=1$。令 $u=\beta+\alpha$、$v=\beta^2+\alpha$、$w=\beta^3+\alpha$。取等的原标签和精确交空间为

$$
\begin{aligned}
W\cap(u/v)W &= u\langle1,\beta,\beta^2\rangle_{\mathbb Q},&
W\cap(u/v)W\cap(u/w)W &= u\langle1,\beta\rangle_{\mathbb Q},\\
V\cap\alpha^6 V &= \langle\alpha^6,\alpha^7,\alpha^8\rangle_{\mathbb Q},&
V\cap\alpha^6 V\cap\alpha^8 V &= \mathbb Q\alpha^8.
\end{aligned}
\tag{31.13}
$$

逐原标签的二元函数并不相同，例如标签 $\beta$ 在 $W$、$V$ 上的交维分别为八和六。

证明。$x^{15}-2$ 和 $x^5-2$ 在素数二处满足 Eisenstein 判据，故原 $L$、$A$ 的次数分别为十五和五，$1,\alpha,\alpha^2$ 是 $L/A$ 的基。对 $1\le j\le4$，在 $A$ 的幂基中乘 $\beta^j$ 将每个基向量送到不同幂次的方向（用 $\beta^5=2$ 降幂），故迹为零；$\operatorname{Tr}_{A/\mathbb Q}(1)=5$。所以 $B=\langle\beta,\beta^2,\beta^3,\beta^4\rangle_{\mathbb Q}$。$W$、$V$ 都是九维，$AW=A\oplus A\alpha=:Z$ 是十维。$W/W$ 含 $(\beta\alpha)/\alpha=\beta$ 和 $\alpha/\beta$，故 $D_W=L$；$V/V$ 含 $\alpha/1$，故 $D_V=L$。$W$ 的稳定子次数整除九和十（它稳定 $AW$），所以 $E_W=\mathbb Q$。对 $V$，若 $cV\subseteq V$，由 $1\in V$ 可写 $c=\sum_{j=0}^8 c_j\alpha^j$。若有最高非零正次 $k\in[1,8]$，则 $c\alpha^{9-k}$ 的最高次为九，未经降幂，故不在 $V$，而 $\alpha^{9-k}\in V$。矛盾，故 $c\in\mathbb Q$，证明 $E_V=\mathbb Q$。

任意原 $r\in L^\times$ 下，$W,rW$ 和 $V,rV$ 分别是十五维空间中的两个九维子空间，二元交维都至少为三。对任意正原三元标签 $(r,s)$，$W$ 的交维由 (31.4) 取 $A$ 至少为二；$V$ 的交维至少为一。下面计算 (31.13)，以同一原域中的实际取等结算这些下界。

对 $W$，$u,v,w$ 都在 $W\setminus\{0\}$。$u/v\notin A$，因为若 $u=cv$ 且 $c\in A$，比较 $\alpha$ 的系数得到 $c=1$，再比较常数项就得到 $\beta=\beta^2$，与五次幂基矛盾。$Z$ 在原 $L$ 内的稳定子恰是 $A$：若 $cZ\subseteq Z$，由 $1\in Z$ 写 $c=c_0+c_1\alpha$，再用 $c\alpha\in Z$ 及 $1,\alpha,\alpha^2$ 的独立性得 $c_1=0$。因此 $Z$ 与 $(u/v)Z$ 是不同的 $A$-二维空间，且共同含 $u$，所以交空间恰是 $Au$。同一个 $Au$ 也在 $(u/w)Z$ 中，因为 $(u/w)w=u$。

在 $Au$ 上写元素为 $a u$，$a=\sum_{j=0}^4 a_j\beta^j\in A$。落在 $W$ 等价于 $a\beta\in B$；落在 $(u/v)W$ 等价于 $av\in W$，即 $a\beta^2\in B$；落在 $(u/w)W$ 等价于 $aw\in W$，即 $a\beta^3\in B$。从 $B$ 的迹计算及 $\beta^5=2$，

$$
\operatorname{Tr}_{A/\mathbb Q}(a\beta)=10a_4,\qquad
\operatorname{Tr}_{A/\mathbb Q}(a\beta^2)=10a_3,\qquad
\operatorname{Tr}_{A/\mathbb Q}(a\beta^3)=10a_2.
$$

前两个条件切出 $\langle1,\beta,\beta^2\rangle_{\mathbb Q}$，三个同时切出 $\langle1,\beta\rangle_{\mathbb Q}$，得 (31.13) 第一行。

对 $V$，$\alpha^6 V$ 的幂基范围为六至十四，与 $V$ 共同的幂次为六、七、八。$\alpha^8 V$ 则由八至十四次幂及 $1,\alpha$ 张成，因为十五、十六次幂分别等于 $2,2\alpha$。因此三者仅共有八次幂方向，得 (31.13) 第二行。最后，$\beta W=\beta B\oplus A\alpha$，而 $B\cap\beta B=\langle\beta^2,\beta^3,\beta^4\rangle_{\mathbb Q}$，故在标签 $\beta$ 的交维为 $3+5=8$；$\beta V=\alpha^3V$ 与 $V$ 共有三至八次幂，交维为六。相等的是二元最小正值，不是两条逐标签函数。$\square$

**原文对应与应用差额。** §29 的 (29.5)–(29.8) 已用子域维数下界、唯一最少块分拆与 Galois 下降；§30 的 (30.3)、(30.8)–(30.14) 已给两窗口各自的缩放及原系数子式返回。Raz–Wigderson 的 [*Subspace arrangements, graph rigidity and derandomization through submodular optimization*，arXiv:1901.09423v1](https://arxiv.org/pdf/1901.09423v1) 中，Definition 2.1 指定最少块取等分拆，Corollary 3.2 给唯一性，Definition 5.1 给超平面一般位置条件，Theorems 5.2、7.1 分别给一刀切面的分拆秩及其在特征零下的泛性。Antolini–Dewar–Tanigawa 的 [*Dilworth truncations and Hadamard products of linear spaces*，arXiv:2508.04798v1，§3.2，式 (7)–(9)](https://arxiv.org/pdf/2508.04798v1) 给二因子切面与矩阵的对应。其 §4.1 的图拟阵反例推翻不受限的三因子 Hadamard 猜想；§4.2 的分拆拟阵反例还排除了以各种二因子迭代次序的秩上界取最小来得到一般等式。这里 (31.6)–(31.9) 切出的是同一个超平面内的共同核约束，每个嵌入给 $h-1$ 行；没有识别多因子 Hadamard 像的拟阵。

De Beule–Demuys–Polverino–Zullo 的 [*Few-Weight Linear Sets and Divisibility of Rank-Metric Codes*，arXiv:2611.08044v1，Theorem 3.7](https://arxiv.org/pdf/2611.08044v1) 已在任意 $h\ge2$ 的相应有限域范围内给出整体公式的取等域。具体取 $F=\mathbb F_q$、$D=\mathbb F_{q^N}$、$U=\prod_i X_i\subseteq D^h$，其 $D$-张成是 $D^h$（每个 $X_i$ 含 $1$），原文的扩张次数、底域秩分别为 $N$、$M=\sum_i m_i$。对无零坐标的点 $P=D(\rho_1^{-1},\ldots,\rho_h^{-1})$，其中 $\rho_1=1$，第一坐标把 $U\cap P$ 同构到 $\bigcap_i \rho_i X_i$。若一个正点有零坐标，取 $U\cap P$ 中一个非零代表元，并将其零坐标各补入相应 $X_i$ 的一个非零元素。在原有非零坐标上，沿新代表元的乘数仍须满足同样条件；新增坐标只增加约束。所以新点有正权、无零坐标且权不大于旧点，全部正点的最小权正是 $\delta_h$。这一逐点接口在二元情形由 Van de Voorde–Zullo [*On the weight distribution of linear sets with complementary weights and related constructions*，arXiv:2511.20057v1，Theorem 3.2、Corollary 3.3、Lemma 3.6](https://arxiv.org/pdf/2511.20057v1) 给出：原文刻画 Cartesian 定义空间的至少及恰好某权的点，并有 $w(\langle(1,\gamma)\rangle)=\dim_{\mathbb F_q}(X_1\cap\gamma^{-1}X_2)$，坐标轴仍保留其各自权。

Theorem 3.7 的条件在上述对应下是 $q\ge N$、$M\le(h-1)N$。最小正权 $\delta_h>1$ 时，原文给实际子域 $C=\mathbb F_{q^c}\subseteq D$，使 $\langle U\rangle_C=\prod_i CX_i$ 定义同一线性集、具有相对 $C$ 权一的点，且 $\dim_F\langle U\rangle_C=M+c-\delta_h$。代入即得 $\Lambda_h(C)=\delta_h$；(31.4) 的商空间论证不依赖特征，可用于所有实际中间域。若 $\delta_h=1$，则 $C=F$ 已取等。因此该原文确实蕴含上述有限域范围的整个 Cartesian 极值公式；它还保有同点集结论。这里的特征零证明依赖可分分裂与原域非零子式，不以有限域计点为前提，也不声称放大后仍定义相同点集。

Napolitano–Polverino–Santonastaso–Zullo 的 [*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，Examples 6.2、6.4、Proposition 6.3](https://arxiv.org/pdf/2201.02003v1) 给一般域中已有临界关系 $\dim_F(S+\mu S)=\dim_F S+1$ 的形状分类，要求 $\mu\notin F$ 在 $F$ 上代数且 $\dim_F L\ge\dim_F S+2$。这里 $(S,\mu)=(W,\beta)$、$(V,\alpha)$ 都满足该前提：前者的和是 $Z$，后者的和由零至九次幂张成。对应前者的完整方向是 $A\alpha$，截短方向是 $B=\beta\langle1,\beta,\beta^2,\beta^3\rangle_{\mathbb Q}$；后者是长度九的单幂窗口。Castello–Polverino–Zullo 的 [*Full weight spectrum one-orbit cyclic subspace codes*，arXiv:2405.19911v1，Definition 2.2、Theorems 4.4、5.2、6.3(ii) 及式 (13)](https://arxiv.org/pdf/2405.19911v1) 已使用子域张成维数并引用该临界对分类。式 (13) 的二元补维下界在截短长度四、子域次数五时是 $2\cdot4-5=3$；其有限域幂窗口分布在原环境与生成域均为十五次、窗口长度九时也有最小交维三（最大子空间距离为十二）。这些是窗口形状与二元下界的先例；(31.13) 的原标签、三元交空间和 (31.11) 的全体窗口阈值由本节推导。

相对于指定原文及 §§29–30，本节的仓内应用差额（repo-derived）是三份同一窗口的九维充要条件，以及同一原数域、同 $(m,N,e)$、同二元最小值下的严格三元分离。定理 30.3 的八维是两个可不同窗口的总维数；(31.11) 的九维按同一窗口的单份维数计。共同核的分拆秩只作为本应用的取等工具。结论限于实际中间域、原标签的精确共同交维及最小正值，不涉及完整逐标签函数的恢复；文献对应不主张全球优先权。

白话说，三份窗口要分享的是同一个方向。把窗口在较大的标量域上补齐后，一个共同见证能带来整条域直线；再回到三个原窗口，各自删去自己没有保留的方向。维数九第一次能让五次域先给出五个方向、三份窗口各花一维，最后留下两个，超过原先两个端点给出的保证。在同一个十五次域里，两个窗口只看单窗口参数和两份的最小交叠都分不出来，第三份加入才显出差别：一个最少还剩两个方向，另一个只剩一个。

## 追加锚（本行以下为增补区）

## 32. 任意阶首次前缀超额的尖锐阈值与同原域嵌套见证

**定义 32.1（最小正共同交维的首次前缀超额）。** 沿用定义 31.1 的原有限特征零扩张 $L/F$，现在每一份窗口都取同一个非零 $F$-子空间 $W\le_F L$。记

$$
\begin{aligned}
m&=\dim_F W,&D&=F(W/W),&N&=[D:F],\\
E&=\{c\in L:cW\subseteq W\},&e&=[E:F],\\
I_j(r)&=W\cap r_2W\cap\cdots\cap r_jW,&
d_j(r)&=\dim_F I_j(r),\\
\delta_j(W)&=\min_{r\in(L^\times)^{j-1},\ d_j(r)>0}d_j(r),&
b_j(W)&=\max\{e,jm-(j-1)N\}.
\end{aligned}
\tag{32.1}
$$

$j=1$ 时元组为空、$I_1=W$、$\delta_1=b_1=m$。正元组总存在，例如所有标签都为一。对指定整数 $h\ge3$，称 $W$ 在第 $h$ 阶首次前缀超额，指

$$
\delta_j(W)=b_j(W)\quad(1\le j<h),\qquad
\delta_h(W)>b_h(W).
\tag{32.2}
$$

这里比较的是各阶最小正值；不要求、也不推断不同窗口在每个相同原标签上的低阶交维相等。若给出一个无限原标签列 $r_2,r_3,\ldots$，其第 $j$ 个前缀始终指同一个 $I_j(r)$，不得为不同阶更换已选标签。

以下只把 §31 证明中的 (31.4)、(31.10) 作为已有共同见证桥使用。对每个实际中间域 $F\subseteq C\subseteq D$，置 $c=[C:F]$、$t_C=\dim_F CW-m$，则

$$
\begin{aligned}
d_j(r)&\ge c-jt_C&&\text{对每一个 }d_j(r)>0\text{ 的原元组},\\
\delta_j(W)&=\max_{F\subseteq C\subseteq D}(c-jt_C).
\end{aligned}
\tag{32.3}
$$

第一行是原共同非零向量 $w\in I_j(r)$ 上的商映射 $Cw\longrightarrow\bigoplus_{i=1}^j r_iCW/r_iW$ 的核维数下界，$r_1=1$；它不是分别选择 $j$ 个共同向量的结论。第二行的原域取等已由 §31 的同一泛超平面、实际域下降及原系数非零子式给出，本节不另立一般秩定理。任取 $b\in W\setminus\{0\}$ 后，$X=b^{-1}W\subseteq D$ 含 $1$ 且 $F(X)=D$；若原交叠为正，则 $r_i=p_1/p_i\in D^\times$，其中所有 $p_i\in W\setminus\{0\}$ 来自同一个共同向量。因此全部正原元组的窗口都位于同一个 $bD$ 中，另有环境下界 $d_j(r)\ge jm-(j-1)N$。稳定子下界 $d_j(r)\ge e$ 则来自 $I_j(r)$ 的 $E$-线性。这些下界均覆盖原 $L^\times$ 中的全部正元组，不只覆盖构造所选的标签。

**定理 32.2（任意阶首次前缀超额的最小维数及全部取等结构）。** 对每个整数 $h\ge3$，定义

$$
M_h=h^2+h-3,\qquad N_h=h(h+2),\qquad q_h=h+3.
\tag{32.4}
$$

任何满足 (32.2) 的原窗口都满足 $m\ge M_h$，且这个下界对每个 $h$ 都能达到。当 $m=M_h$ 时，(32.2) 成立当且仅当

$$
N=N_h,\qquad
\text{存在实际 }F\subseteq A\subseteq D\text{，使 }
[A:F]=h+2,\quad \dim_F AW=M_h+1.
\tag{32.5}
$$

在 (32.5) 下，$E=F$；$A$ 是 (32.3) 在第 $h$ 阶的唯一取等域，且整个最小正值序列为

$$
\delta_j(W)=
\begin{cases}
N_h-jq_h,&1\le j\le h-1,\\
2,&j=h,\\
1,&j\ge h+1.
\end{cases}
\tag{32.6}
$$

特别地，$\delta_{h-1}=3$、$b_h=1$。条件 (32.5) 要求原 $D$ 中的实际子域，次数整除条件不能替代它。$h=3$ 的九维严格三元阈值继承定理 31.2；在该情形附加二元端点相等才把其允许的 $N\ge15$ 精确收紧到 $N=15$。这里任意 $h\ge4$ 的阈值与全部较低阶前缀条件由下面的统一论证承担。

证明。假设 (32.2) 成立。由 (32.3)，选择一个第 $h$ 阶取等的实际中间域 $A$，写

$$
a=[A:F],\qquad k=\dim_A AW,\qquad
n=[D:A],\qquad t=ak-m.
\tag{32.7}
$$

若 $t=0$，则 $AW=W$，故 $A\subseteq E$，其项 $a-ht=a\le e$，不能严格超额。若 $k=1$，对含 $1$ 的 $X=b^{-1}W$ 有 $AX=A$，于是 $D=F(X)\subseteq A$，即 $A=D$；该项正是环境端点，仍不能严格超额。因此 $t\ge1$、$k\ge2$。若 $k=n$，则 $t=N-m$，从而 $a-ht\le N-h(N-m)$，也不能严格超额。因此

$$
s=n-k\ge1.
\tag{32.8}
$$

严格超额及整数性给出 $a-ht>e\ge1$，所以 $a\ge ht+2$。又 $a-(h-1)t=\delta_h+t>e$。由第 $h-1$ 阶前缀等式，支配该项的只能是环境端点，因而

$$
\begin{aligned}
a-(h-1)t&\le(h-1)m-(h-2)N,\\
a-ht&>hm-(h-1)N.
\end{aligned}
\tag{32.9}
$$

代入 $m=ak-t$、$N=an=a(k+s)$ 并约去正数 $a$，两式分别成为

$$
(h-2)s+1\le k\le(h-1)s.
\tag{32.10}
$$

尤其 $k\ge h-1$。这给出对全部原窗口的统一必要下界

$$
\begin{aligned}
m=ak-t
&\ge(h-1)(ht+2)-t\\
&=(h^2-h-1)t+2h-2\\
&\ge h^2+h-3=M_h.
\end{aligned}
\tag{32.11}
$$

这里没有对某一组标签作一般位置假设；选出的实际 $A$ 来自适用于全部原窗口的 (32.3)。若 $m=M_h$，(32.11) 每步都取等，故

$$
t=1,\quad a=h+2,\quad k=h-1.
\tag{32.12}
$$

再由 (32.10) 及 $h\ge3$ 得 $s=1$、$n=h$，故 $N=N_h$，得到 (32.5)。所选取等项为 $a-ht=2$。稳定子 $E$ 同时稳定 $W$ 和 $AW$，因为乘法交换；所以 $e$ 同时整除 $m$ 和 $m+1$，即 $e=1$。这证明必要性。

反过来，假设 $m=M_h$ 且 (32.5) 成立。仍由 $E$ 同时稳定 $W,AW$ 得 $E=F$。归一化为 $X=b^{-1}W\subseteq D$，置

$$
a=h+2,\quad q=h+3=a+1,\quad
Z=AX,\quad \dim_F Z=N-a=M_h+1.
\tag{32.13}
$$

$Z$ 是 $D$ 中的 $A$-超平面，而 $X$ 是 $Z$ 中的 $F$-超平面。$Z$ 的稳定子恰为 $A$：设该稳定子为 $H$。因为 $1\in Z$，有 $H\subseteq D$；又 $A\subseteq H$，且 $[H:F]$ 同时整除 $N=ha$ 和 $\dim_F Z=(h-1)a$，所以 $[H:F]=a$、$H=A$。

现在逐类控制原 $D$ 中的每个实际中间域 $C$。记 $c=[C:F]$、$u=\dim_F CX-M_h$。若 $C=F$，其项为一。若 $F\subsetneq C\subseteq A$，则 $X\subseteq CX\subseteq Z$；若 $CX=X$，就会有 $C\subseteq E=F$，矛盾。因此 $CX=Z$、$u=1$，其项为 $c-j\le a-j$，且 $C=A$ 给出 $a-j$。若 $C=D$，则 $CX=D$、$u=q$，其项为 $N-jq$。

最后设 $C\not\subseteq A$ 且 $C\ne D$。取 $c_0\in C\setminus A$。$c_0$ 不稳定 $Z$，故 $Z$ 与 $c_0Z$ 是不同的 $A$-超平面，从而 $Z+c_0Z=D$。商映射给出

$$
\dim_F D/(X+c_0X)
\le\dim_F Z/X+\dim_F c_0Z/c_0X=2.
\tag{32.14}
$$

由于 $X+c_0X\subseteq CX$，得 $u\ge N-2-M_h=q-2=h+1$。实际域塔给出 $c\le N/2$，所以所有这类域都满足

$$
c-ju\le N/2-j(h+1).
\tag{32.15}
$$

当 $1\le j\le h-1$ 时，$N/2>2(h-1)\ge2j$，故 (32.15) 严格小于 $N-j(h+3)$。当 $j\ge h$ 时，其右端至多 $N/2-h(h+1)=-h^2/2<0$。这覆盖了所有不包含于 $A$ 的真中间域，不要求 $A$ 与 $C$ 可比，也没有以子域次数表代替实际域。

因此 (32.3) 精确化为

$$
\delta_j(W)=\max\{1,a-j,N-jq\}\qquad(j\ge1).
\tag{32.16}
$$

三个下界对每一个正原元组都成立：分别由正维数、$A$ 上的共同见证商映射和原 $bD$ 中的环境维数给出。上面的全部中间域控制及 §31 的取等桥给出匹配的上界。对 $j\le h-1$，

$$
(N-jq)-(a-j)=(h-1-j)a\ge0,\qquad
N-(h-1)q=3.
$$

对 $j=h$，$a-j=2$、$N-jq=-h$；对 $j\ge h+1$，$a-j\le1$，而环境项继续下降。这就得到 (32.6) 和 (32.2)。第 $h$ 阶，$C=F$ 的项为一，$C=D$ 的项为 $-h$，(32.15) 排除所有 $C\not\subseteq A$ 的真中间域；在 $C\subseteq A$ 中，$c-h=2$ 迫使 $c=a$、$C=A$。故取等域唯一。下一个命题给出每个 $h$ 的原数域实现，从而证明下界尖锐。$\square$

**命题 32.3（同原数域、同全部低阶最小值的首次分离及单列嵌套取等）。** 固定 $h\ge3$，简写 $M=M_h$、$N=N_h$、$a=h+2$、$q=h+3$。取正实根 $\alpha^N=2$，在同一个原数域中定义

$$
\begin{aligned}
F&=\mathbb Q,&L&=\mathbb Q(\alpha),&
\beta&=\alpha^h,&A&=\mathbb Q(\beta),\\
B&=\ker\operatorname{Tr}_{A/\mathbb Q},&
W&=B\oplus\bigoplus_{\ell=1}^{h-2}A\alpha^\ell,&
V&=\langle1,\alpha,\ldots,\alpha^{M-1}\rangle_{\mathbb Q}.
\end{aligned}
\tag{32.17}
$$

两窗口都有 $(m,N,e)=(M,h(h+2),1)$、$D_W=D_V=L$。它们满足

$$
\begin{aligned}
\delta_j(W)=\delta_j(V)&=N-jq&& (1\le j<h),\\
\delta_h(W)&=2,&\delta_h(V)&=1,\\
\delta_j(W)=\delta_j(V)&=1&& (j\ge h+1).
\end{aligned}
\tag{32.18}
$$

以下每个窗口只选一列标签，全部阶都使用该列的嵌套前缀。对 $W$，在原 $W$ 内取

$$
\begin{aligned}
u_1&=\beta,\\
u_i&=\beta^i+\alpha^{i-1}&& (2\le i\le h-1),\\
u_h&=\beta^h+\alpha,\qquad
u_{h+1}=\beta^{h+1}+\alpha,\\
r_i&=\beta/u_i&& (2\le i\le h+1),\qquad
r_i=r_{h+1}\quad(i\ge h+2).
\end{aligned}
\tag{32.19}
$$

记

$$
K_j=\langle1,\beta,\ldots,\beta^{a-j-1}\rangle_{\mathbb Q}
\quad(1\le j\le h+1).
\tag{32.20}
$$

则其准确交空间为

$$
I_j^W=
\begin{cases}
\displaystyle\beta\left(K_j\oplus\bigoplus_{\ell=1}^{h-j-1}A\alpha^\ell\right),
 &1\le j\le h-1,\\
\beta\langle1,\beta\rangle_{\mathbb Q},&j=h,\\
\mathbb Q\beta,&j\ge h+1.
\end{cases}
\tag{32.21}
$$

空直和按零空间解释。对 $V$，取原标签 $s_i=\alpha^{v_i}$，其中

$$
v_1=0,\qquad v_i=(i-1)q\ (2\le i\le h-1),\qquad
v_i=M-1\ (i\ge h).
\tag{32.22}
$$

相应的准确交空间为

$$
I_j^V=
\begin{cases}
\langle\alpha^{(j-1)q},\alpha^{(j-1)q+1},\ldots,\alpha^{M-1}\rangle_{\mathbb Q},
 &1\le j\le h-1,\\
\mathbb Q\alpha^{M-1},&j\ge h.
\end{cases}
\tag{32.23}
$$

证明。$x^N-2$ 与 $x^a-2$ 均在素数二处满足 Eisenstein 判据，故 $[L:\mathbb Q]=N$、$[A:\mathbb Q]=a$、$[L:A]=h$，且 $1,\alpha,\ldots,\alpha^{h-1}$ 是 $L/A$ 的基。因为 $\beta^a=2$，在 $A$ 的幂基中，乘以 $\beta^d$（$1\le d\le a-1$）没有对角项；因此

$$
\operatorname{Tr}(1)=a,\qquad
\operatorname{Tr}(\beta^d)=0\ (1\le d\le a-1),\qquad
B=\langle\beta,\ldots,\beta^{a-1}\rangle_{\mathbb Q}.
\tag{32.24}
$$

于是 $\dim_F W=(a-1)+(h-2)a=(h-1)a-1=M$，而 $AW=\bigoplus_{\ell=0}^{h-2}A\alpha^\ell$ 为 $M+1$ 维。$V$ 也为 $M$ 维。$W/W$ 含 $(\beta\alpha)/\alpha=\beta$ 及 $\alpha/\beta$，所以 $D_W=L$；$V/V$ 含 $\alpha/1$，所以 $D_V=L$。$E_W$ 的次数同时整除 $M$ 和 $M+1$，故 $E_W=\mathbb Q$。若 $cV\subseteq V$，由 $1\in V$ 写 $c=\sum_{d=0}^{M-1}c_d\alpha^d$。若最高非零正次为 $k$，则 $\alpha^{M-k}\in V$，但 $c\alpha^{M-k}$ 的最高次恰为 $M<N$，不发生降幂，故不在 $V$。所以 $c\in\mathbb Q$，即 $E_V=\mathbb Q$。

先给出覆盖全部原正元组的下界。对 $W$，定理 32.2 已控制了每个实际中间域；更直接地，(32.3) 取 $C=A$ 给出 $d_j(r)\ge a-j$，原环境给出 $d_j(r)\ge N-jq$，正维数给出 $d_j(r)\ge1$。对 $V$，任意原正元组也有 $d_j(s)\ge\max\{1,N-jq\}$。因此 $W$ 在 $j<h$ 的下界是 $N-jq$、在 $j=h$ 的下界是二、在 $j\ge h+1$ 的下界是一；$V$ 在 $j<h$ 的下界是 $N-jq$、在 $j\ge h$ 的下界是一。下面用 (32.19)、(32.22) 的固定嵌套列同时达到它们，不拼接逐阶优化元组。

(32.19) 中每个 $u_i$ 都在 $W\setminus\{0\}$：常数系数 $\beta^i$ 的次数在一至 $a-1$ 之间，故属于 $B$；其他项是允许的 $A\alpha^\ell$ 方向。$u_1=\beta$ 属于每个前缀交空间，因为 $r_iu_i=\beta$。将交空间中的元素统一写为 $\beta x$；其属于 $r_iW$ 当且仅当 $xu_i\in W$，其中也把 $i=1$ 的条件包括在内。

在 $L/A$ 的固定幂基中写 $x=\sum_{\ell=0}^{h-1}x_\ell\alpha^\ell$，$x_\ell\in A$。属于 $W$ 的两个条件是 $\alpha^{h-1}$ 系数为零、常数系数的迹为零。对 $1\le j\le h-1$，前 $j$ 个 $xu_i$ 的第一类条件恰为

$$
\beta x_{h-1}=0,\qquad
\beta^i x_{h-1}+x_{h-i}=0\quad(2\le i\le j).
\tag{32.25}
$$

这些等价于 $x_{h-j}=\cdots=x_{h-1}=0$。确实，$x\alpha^{i-1}$ 的最高幂至多为 $2h-3$，只有原幂次 $h-1$ 能贡献到 $\alpha^{h-1}$，降幂不会再产生该方向。在这些条件下，剩余的 $x$ 只含零至 $h-j-1$ 次幂，故 $x\alpha^{i-1}$ 的最高次至多为 $h-2$；其常数项也为零。于是前 $j$ 个 $xu_i$ 的第二类条件精确成为

$$
\operatorname{Tr}_{A/\mathbb Q}(\beta^i x_0)=0
\quad(1\le i\le j).
\tag{32.26}
$$

若 $x_0=\sum_{d=0}^{a-1}z_d\beta^d$，则由 (32.24) 及 $\beta^a=2$，

$$
\operatorname{Tr}_{A/\mathbb Q}(\beta^i x_0)=2a\,z_{a-i}
\qquad(1\le i\le a-1).
\tag{32.27}
$$

因此 (32.26) 切出的正是 $K_j$，其余 $x_1,\ldots,x_{h-j-1}$ 任意。这证明 (32.21) 的第一行，维数为 $(h-j-1)a+(a-j)=N-jq$。当 $j=h-1$ 时，$x\in A$ 已被迫成立，且 $x\in\langle1,\beta,\beta^2\rangle_{\mathbb Q}$。接着 $u_h=\beta^h+\alpha$、$u_{h+1}=\beta^{h+1}+\alpha$ 的 $A$-系数条件自动成立，它们的迹条件依 (32.27) 依次消去 $z_2,z_1$，留下 $\langle1,\beta\rangle_{\mathbb Q}$ 及 $\mathbb Q$。重复最后标签不再改变交空间，得到 (32.21) 全部各行。

对 $V$，以原 $\mathbb Q$-幂基 $\{\alpha^d:0\le d<N\}$ 为坐标。乘以 $\alpha^v$ 把方向指数模 $N$ 平移，越过 $N$ 只产生非零有理因子二，不改变方向。$V$ 缺少的方向是长度 $q$ 的区间 $[M,N-1]$。对 $2\le i\le h-1$，$s_iV$ 缺少的模 $N$ 区间恰为

$$
[(i-2)q,(i-1)q-1].
\tag{32.28}
$$

这些区间彼此不交，且与 $V$ 自己缺少的尾区间不交。前 $j$ 个空间剩下的方向正是 $[(j-1)q,M-1]$，得到 (32.23) 的第一行；在 $j=h-1$ 时剩下 $M-3,M-2,M-1$ 三个方向。$s_h=\alpha^{M-1}$ 的缺失区间为 $[M-q-1,M-2]$，其中左端非负，且 $q\ge6$。它删去前两个剩余方向而保留 $M-1$，故得到第二行。所有前缀都含同一个非零原向量 $\alpha^{M-1}$；其在第 $i$ 份窗口中的原像为 $\alpha^{M-1-v_i}\in V\setminus\{0\}$。因此这也是一列原实现内的共同见证。比较全正元组下界与 (32.21)、(32.23)，便同时得到 (32.18)。

这里相等的仅是最小值序列的前缀。例如同一原标签 $\beta$ 给出 $\dim_F(W\cap\beta W)=M-1$，因为 $B\cap\beta B$ 少一个 $B$ 方向，而各完整 $A\alpha^\ell$ 方向不变；$V\cap\beta V=\langle\alpha^h,\ldots,\alpha^{M-1}\rangle_{\mathbb Q}$ 则为 $M-h$ 维。故这对窗口并没有相同的完整逐标签二元函数。

这些形状与公式的已知范围须分开。Napolitano–Polverino–Santonastaso–Zullo 的 [*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，Examples 6.2、6.4、Proposition 6.3](https://arxiv.org/pdf/2201.02003v1) 已给一般域中完整子域方向加截短幂方向、以及单幂窗口的临界对形状。其 Proposition 6.3 要求 $\mu\notin F$ 在 $F$ 上代数、$\dim_F L\ge\dim_F S+2$，并假设 $\dim_F(S+\mu S)=\dim_F S+1$。对本命题，$(S,\mu)=(W,\beta)$ 时 $W+\beta W=AW$，截短方向是 $B=\beta\langle1,\beta,\ldots,\beta^{a-2}\rangle_{\mathbb Q}$；$(S,\mu)=(V,\alpha)$ 时 $V+\alpha V=\langle1,\ldots,\alpha^M\rangle_{\mathbb Q}$。两者都有 $N-M=q\ge6$，满足该原文前件，故不把窗口形状本身列为新发现。

De Beule–Demuys–Polverino–Zullo 的 [*Few-Weight Linear Sets and Divisibility of Rank-Metric Codes*，arXiv:2611.08044v1，Theorem 3.7](https://arxiv.org/pdf/2611.08044v1) 已有任意因子数的相应有限域整体公式，§31 已给逐点接口。精确地，在 $D=\mathbb F_{q_0^N}$、$U=X^j\subseteq D^j$、$\dim_{\mathbb F_{q_0}}X=m$ 下，其条件是 $j\ge2$、$q_0\ge N$、$jm\le(j-1)N$；最小正点权 $d>1$ 时，原文给实际子域 $\mathbb F_{q_0^c}$，使该子域张成仍定义同一线性集，具有相对该子域权一的点，且张成维数为 $jm+c-d$。这承担该范围内中间域最大值取等的先例；$d=1$ 时底域取等。本命题在原数域中的前缀取等直接由 (32.19)–(32.28) 证明，不将有限域保持点集的结论移用于数域。

(32.3) 的特征零取等机制已经属于 §31 使用的成熟一刀切面方法：Raz–Wigderson [*Subspace arrangements, graph rigidity and derandomization through submodular optimization*，arXiv:1901.09423v1，Corollary 3.2、Definition 5.1、Theorems 5.2、7.1](https://arxiv.org/pdf/1901.09423v1) 给最少块分拆唯一性、一般位置切面秩及特征零泛性；Antolini–Dewar–Tanigawa [*Dilworth truncations and Hadamard products of linear spaces*，arXiv:2508.04798v1，§3.2，式 (7)–(9)](https://arxiv.org/pdf/2508.04798v1) 给二因子矩阵与切面的接口。这些不是本节新增的机制，也不蕴含不受限的多因子 Hadamard 秩猜想。本节相对于这些指定原文与 §§29–31 的仓内新增推导（repo-derived）是任意 $h\ge4$ 的首次前缀阈值 (32.11)、最小维数时的实际域充要结构及全部竞争域控制 (32.12)–(32.16)，以及同一原数域中同时达到完整序列的两列嵌套原标签。$h=3$ 使用既有三元结果；上述出处对应不宣称全球优先权。

白话说，较低阶最小值确实能任意长时间掩盖中间域留下的额外交叠，但必须付出精确的窗口维数。每加入一份，环境端点先按固定速度下降；直到第 $h-1$ 份，两种窗口都最少剩三个方向。第 $h$ 份加入时，部分域窗口因同一个实际子域还必须留下两个方向，普通幂窗口只剩一个。两列标签从头到尾各自保持同一个共同非零向量，因此每一步都在同一个原实现内发生；这不是把不同阶各自存在的例子拼在一起。

结论限于有限特征零扩张、实际中间域及原标签的精确共同交维与最小正值。它不把次数整除当成子域存在，不把最小值前缀相等当成完整低阶关系相等，也不给出有限查询、噪声、物理、量子或 $H10(\mathbb Q)$ 的结论。$\square$

## 追加锚（本行以下为增补区）

## 33. 全部最小交维序列的剖面损失与首个规模的实际域充要条件

**定义 33.1（同原比值域上的剖面逆问题）。** 设 $F$ 为特征零域，$L/F$ 为有限扩张，$0\ne X\le_F L$。沿用 (32.1) 的 $m=\dim_F X$、$D_X=F(X/X)$、$E_X=\{c\in L:cX\subseteq X\}$、$N=[D_X:F]$、$e=[E_X:F]$ 及最小正共同交维 $\delta_j(X)$。对每个实际中间域 $F\subseteq A\subseteq D_X$，定义函数

$$
\mathcal T_X(A)=t_X(A)=\dim_F AX-m,
\qquad AX=\operatorname{span}_A X\subseteq L.
\tag{33.1}
$$

比较 $W,V$ 时，要求 $D_W=D_V=D$ 为原 $L$ 中同一个子域，并有相同的 $m,N,e$。剖面相等指对每一个实际 $A\subseteq D$ 逐项相等；只比较子域次数不构成这项条件。问题是全部序列 $(\delta_j)_{j\ge1}$ 相等能否强制 $\mathcal T_W=\mathcal T_V$。规模按先 $m$ 后 $N$ 的字典序比较。

任取 $x\in X\setminus\{0\}$，已有的归一化给出 $U=x^{-1}X\subseteq D_X$、$1\in U$、$F(U)=D_X$；整体缩放不改变上述维数或稳定子。若原共同交空间 $I_j=X\cap r_2X\cap\cdots\cap r_jX$ 非零，则从同一个 $z\in I_j\setminus\{0\}$ 得 $r_i=z/(z/r_i)\in D_X$，所以这些空间全在同一个 $xD_X$ 中。以下只消费 (31.4)、(32.3) 已有的全正元组下界：对每个实际 $A\subseteq D_X$、$a=[A:F]$，

$$
\dim_F I_j\ge
\max\{e,\,jm-(j-1)N,\,a-jt_X(A)\}
\quad\text{只要 }I_j\ne\{0\}.
\tag{33.2}
$$

其中第三项来自同一条 $Az$ 上的映射 $Az\longrightarrow\bigoplus_{i=1}^j r_iAX/r_iX$，$r_1=1$：其核为 $Az\cap I_j$，各商空间维数均为 $t_X(A)$。前两项分别来自 $E_X$-线性与 $xD_X$ 中的余维和。域外标签的交空间为零。这是已有共同见证的维数机制，不另提出秩公式。

**定理 33.2（固定实际六次域的完整剖面表与精确分离判据）。** 固定原 $F\subseteq D\subseteq L$，$[D:F]=6$。对每一个三维窗口 $X\le_F L$、$D_X=D$，都有 $E_X=F$，且

$$
\delta_1(X)=3,\qquad \delta_j(X)=1\quad(j\ge2).
\tag{33.3}
$$

每个这样的 $X$ 均有一列原标签，使所有阶的嵌套前缀同时达到 (33.3)。它在每一个实际中间域上的剖面恰为下表；没有相应子域时不产生该行的条目。

| 实际域 $A\subseteq D$ | $\dim_A AX$ | $t_X(A)$ |
| --- | --- | --- |
| $A=F$ | $3$ | $0$ |
| $[A:F]=2$，且 $\dim_A AX=2$ | $2$ | $1$ |
| $[A:F]=2$，且 $\dim_A AX=3$ | $3$ | $3$ |
| $[A:F]=3$，每一个这样的实际域 | $2$ | $3$ |
| $A=D$ | $1$ | $3$ |

因此对任何两个这样的 $W,V$，

$$
\mathcal T_W\ne\mathcal T_V
\quad\Longleftrightarrow\quad
\exists A\subseteq D:\ [A:F]=2,\quad
\{\dim_A AW,\dim_A AV\}=\{2,3\}.
\tag{33.4}
$$

若该实际二次域存在，它唯一。一个固定实际六次域中存在剖面不同的窗口对，当且仅当它包含这个实际二次域；存在时，两种表列剖面都能实现。将 (33.4) 中的窗口排序为 $\dim_A AW=2$、$\dim_A AV=3$ 后，对任一原 $\gamma\in A\setminus F$，

$$
\dim_F(W\cap\gamma W)=2,\qquad
\dim_F(V\cap\gamma V)=0.
\tag{33.5}
$$

所以同一条实际二次标签已分离它们的完整二元函数；(33.3) 相等的是全部最小值，绝非完整逐标签函数相等。

证明。归一化为 $1\in U=x^{-1}X\subseteq D$。消费 §§27、29 的稳定子事实，$E_X\subseteq D$ 成域，其次数整除三。若该次数为三，则 $X=xE_X$，其比值域就是 $E_X$，与 $[D:F]=6$ 矛盾。因此 $E_X=F$。

定理 27.2 的次数至少五分支已给原 $p,q\in X\setminus\{0\}$，满足 $X\cap(p/q)X=Fp$。固定 $r_2=p/q$，并对所有 $i\ge3$ 取 $r_i=r_2$。于是同一列标签的每个 $j\ge2$ 前缀交空间都是 $Fp$；$p$ 在每份后续缩放窗口中的原像均为 $q$。另一方面，每个原正元组的交维至少为一，由 (33.2) 亦可直接读出。这证明全部窗口的 (33.3) 及单列嵌套取等，不需要另一个高阶取等公式，也没有拼接分别最优的元组。

域塔使实际中间域的次数只能为一、二、三、六。$F$ 行显然，$DU=D$ 给出 $D$ 行。若 $[C:F]=3$，则 $\dim_C CU\le[D:C]=2$；若它等于一，由 $1\in U$ 得 $U\subseteq C$，从而 $D=F(U)\subseteq C$，矛盾。因此每一个实际三次域都给 $CU=D$、$t_X(C)=6-3=3$，无论这样的域有几个。若 $[A:F]=2$，三维 $U$ 不可能容在一条二维的 $A$-直线上，而 $\dim_A D=3$，故 $\dim_A AU$ 恰为二或三，对应 $t_X(A)=1$ 或三。表已穷尽全部实际域，因而立即得到 (33.4)。

两个不同二次域 $A_1,A_2\subseteq D$ 的合成域在 $A_1$ 上次数为二，在 $F$ 上次数为四；它不能容在六次域 $D$ 内。因此实际二次域至多一个。这里先有实际子域，才使用域塔，并未从 $2\mid6$ 推出其存在。

若实际二次域 $A$ 存在，特征零的本原元定理给原 $\theta\in D$、$F(\theta)=D$。于是 $A(\theta)=D$、$[D:A]=3$，原 $1,\theta,\theta^2$ 在 $A$ 上独立。采用已有的部分域与幂窗口形状，取

$$
W_0=A\oplus F\theta,\qquad
V_0=\langle1,\theta,\theta^2\rangle_F.
\tag{33.6}
$$

两者三维、含 $1$，分别生成 $A(\theta)=D$ 与 $F(\theta)=D$，故比值域都是这个原 $D$。已有的稳定子论证给 $E_{W_0}=E_{V_0}=F$。它们的 $A$-秩分别为二和三，故两种剖面均实现；而没有实际二次域时，上表对所有窗口完全相同，不能分离。

这些存在见证也能显式选单列标签。在 $1,\theta,\theta^2$ 的 $A$-坐标中比较系数得 $W_0\cap\theta W_0=F\theta$；原 $1,\theta,\ldots,\theta^4$ 在 $F$ 上独立，又给 $V_0\cap\theta^2 V_0=F\theta^2$。分别从第二项起重复原标签 $\theta$、$\theta^2$，所有前缀便保持所示一线。

最后证明适用于全部窗口的 (33.5)，不要求它们是 (33.6) 的形状。$AW$ 为四维 $F$-空间，且被 $\gamma$ 保持，故其中两个三维空间 $W,\gamma W$ 的交维至少为二；等于三会使 $\gamma\in E_W=F$，矛盾，故恰为二。若 $\dim_A AV=3$，$V$ 的任一 $F$-基 $v_1,v_2,v_3$ 同时是 $AV$ 的 $A$-基。等式 $\sum_i f_iv_i=\gamma\sum_i g_iv_i$、$f_i,g_i\in F$，迫使 $f_i=\gamma g_i$ 对每个 $i$ 成立。因 $\gamma\notin F$，所有系数为零，故 $V\cap\gamma V=\{0\}$。定理得证。$\square$

**命题 33.3（原有理六次域中的准确反恢复见证）。** 取 $\alpha$ 为 $x^6-2$ 的正实根，在同一个原域中令

$$
F=\mathbb Q,\quad L=D=\mathbb Q(\alpha),\quad
A=\mathbb Q(\alpha^3),\quad
W=\langle1,\alpha,\alpha^3\rangle_{\mathbb Q},\quad
V=\langle1,\alpha,\alpha^2\rangle_{\mathbb Q}.
\tag{33.7}
$$

两者共同的 $(m,N,e)$ 为 $(3,6,1)$，原稳定子都是 $\mathbb Q$，全部序列均为 $(3,1,1,\ldots)$，但 $t_W(A)=1$、$t_V(A)=3$。取一列 $r_i=\alpha$、另一列 $s_i=\alpha^2$（$i\ge2$），则准确的嵌套前缀为

$$
I_1^W=W,\quad I_j^W=\mathbb Q\alpha\ (j\ge2),\qquad
I_1^V=V,\quad I_j^V=\mathbb Q\alpha^2\ (j\ge2).
\tag{33.8}
$$

原标签 $\beta=\alpha^3\in A\setminus\mathbb Q$ 则给

$$
W\cap\beta W=\langle1,\beta\rangle_{\mathbb Q}=A,
\qquad V\cap\beta V=\{0\}.
\tag{33.9}
$$

证明。$x^6-2$ 及 $x^2-2$ 在素数二处满足 Eisenstein 判据，故 $[L:\mathbb Q]=6$、$[A:\mathbb Q]=2$。原 $1,\alpha,\ldots,\alpha^5$ 为有理基，$W,V$ 均三维且都含 $1,\alpha$，所以两比值域同为 $L$。定理 33.2 给两稳定子均为 $\mathbb Q$。用 $L/A$ 的基 $1,\alpha,\alpha^2$，有 $AW=A\oplus A\alpha$、$AV=L$，故两个损失分别为 $4-3=1$ 和 $6-3=3$。

在原有理幂基中，$\alpha W=\langle\alpha,\alpha^2,\alpha^4\rangle_{\mathbb Q}$，与 $W$ 只共用 $\alpha$ 方向；$\alpha^2V=\langle\alpha^2,\alpha^3,\alpha^4\rangle_{\mathbb Q}$，与 $V$ 只共用 $\alpha^2$ 方向。重复各自标签得到 (33.8)；共同原向量分别是 $\alpha$、$\alpha^2$，在每一份缩放窗口中的原像都是 $1$。对任意其他原正元组，交维仍至少为一；它们与 (33.8) 的取等共同证明全部阶数的最小值。最后 $\beta W=\langle\beta,\alpha^4,2\rangle_{\mathbb Q}$、$\beta V=\langle\alpha^3,\alpha^4,\alpha^5\rangle_{\mathbb Q}$，直接给出 (33.9)。$\square$

**定理 33.4（剖面不恢复的字典序首个规模）。** 在定义 33.1 的全部窗口对中，全部最小值序列相同而实际中间域张成剖面不同的首个规模恰为 $(m,N)=(3,6)$。这包括排除任意比值域次数下的 $m=1,2$，以及排除 $m=3$、$N<6$；首个规模中每一个固定实际 $D/F$ 的全部分离，恰由 (33.4) 描述。

证明。以下在相同实际 $D$ 上证明更强的结论：较早规模的任意窗口都有相同剖面，甚至不必先假设最小值序列相同。

若 $m=1$，$X=xF$，故 $D=F$，唯一条目 $t_X(F)=0$。若 $m=2$，归一化写 $x^{-1}X=F+F\theta$，其中 $\theta\notin F$、$D=F(\theta)$。对每个实际真中间域 $F\subseteq A\subsetneq D$，必有 $\theta\notin A$，否则 $D\subseteq A$。所以 $1,\theta$ 在 $A$ 上独立，而 $D$ 张成的秩为一，得

$$
t_X(A)=
\begin{cases}
2[A:F]-2,&A\subsetneq D,\\
N-2,&A=D.
\end{cases}
\tag{33.10}
$$

这对任意次数 $N$ 成立，完全由同一实际域 $D$ 及其实际中间域决定。

若 $m=3$，归一化的三维空间容在 $D$ 内，故 $N\ge3$。$N=3$ 时空间就是 $D$，所有条目为零。$N=4$ 时，$F$ 条目为零，$D$ 条目为一；每个实际真非平凡中间域都为二次，三维空间的 $A$-张成不可能只有二维，故必为整个 $D$，条目也是一。$N=5$ 为素数，没有真非平凡中间域，只有 $t_X(F)=0$、$t_X(D)=2$。这些剖面均与窗口无关，因此排除了全部较早规模。命题 33.3 在 $(3,6)$ 取到分离；定理 33.2 已给这个规模的完整实际域充要条件。$\square$

上述逆问题与既有形状须分别归属。Castello–Polverino–Zullo，[*On one-orbit cyclic subspace codes of $\mathcal G_q(n,3)$*，arXiv:2405.01652v1，Definition II.3、Theorem III.2(3.1)–(3.2)](https://arxiv.org/html/2405.01652v1)，已定义子域张成的相对维数，并在有限域的三维平方张成分类中区分幂窗口的二次域秩三与部分二次域窗口的秩二。其记号 $\delta_t(S)$ 是子域张成秩，不是这里的第 $j$ 阶最小交维；在该有限域对应中，$t_X(\mathbb F_{q^t})=t\delta_t(X)-m$。这些秩分支及窗口形状不是本节新增的分类。

Napolitano–Polverino–Santonastaso–Zullo，[*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，Examples 6.2、6.4、Proposition 6.3](https://arxiv.org/html/2201.02003v1)，已给一般域的部分子域方向与幂窗口的临界对形状。对 (33.6)，$W_0+\gamma W_0=AW_0$（$\gamma\in A\setminus F$）及 $V_0+\theta V_0=\langle1,\theta,\theta^2,\theta^3\rangle_F$ 均为四维；其 $k=3$、环境维数六满足 Proposition 6.3 的 $k+2\le\dim_F D$，分别属于其二次域部分方向与次数六的幂方向。这里直接采用这些形状作存在见证，不重立临界对定理。

Castello–Polverino–Zullo，[*Full weight spectrum one-orbit cyclic subspace codes*，arXiv:2405.19911v1，Definition 2.2、Theorem 4.4、Proposition 4.8、Corollary 4.11、Theorem 5.2](https://arxiv.org/html/2405.19911v1)，已给子域张成与最小容纳域、有限域幂窗口分布和部分二次域族，并直接引用上述一般域 Proposition 6.3。取其幂窗口参数 $k=3,t=n=6$，及部分二次域族参数 $\ell=1,[\mathbb F_{q^2}(\theta):\mathbb F_{q^2}]=3$，已有正交维一的标签。重复同一标签即延续到全部阶；这个延续不构成新的高阶机制。Shi–Özbudak，[*Linear equivalence of full weight spectrum cyclic orbit codes*，arXiv:2611.04947v1，Theorem 1.1、§2](https://arxiv.org/html/2611.04947v1)，进一步给这两类有限域码各自的线性等价判据，包括真子域参数：幂族用分式线性变换及 Frobenius，部分二次域族用二次域仿射变换及 Frobenius。其分类不作为本节的窗口标量轨道分类；本节也没有断言秩三的全部窗口均为幂窗口。

仓内定理 27.2 已承担特征零三维窗口的原域单线取等；(29.2)、(31.4)、(32.3) 已承担剖面到极小值的正向关系、共同见证下界及一般超平面的取等桥。本节不重立这些机制。相对于上述指定原文与这些既有结论，本节的仓内推导（repo-derived）差额是反向信息损失的精确结算：全部最小值仍不能恢复实际域剖面，首个字典序规模为 $(3,6)$，且每一个固定实际六次域上的全部剖面差异恰为唯一实际二次域的秩二与秩三之别。有限域中两类已知形状的秩差与单线取等本身已有先例；这些来源对应不推出全球优先权。

白话说，把每一阶最少还能相交多少个方向全部列出，仍会丢掉窗口在某个实际子域下需要补几个方向的信息。六次域里的三维窗口已经发生这种损失：两种窗口都能在第二份加入时只剩一线，此后重复它便永远只剩这一线；但二次域补齐一个窗口只添一维，补齐另一个却添三维。这个尺度没有其他域条目可以分离它们，而且二次域若存在便只有一个。保留该域中任一非底域的实际标签，交维二与零就能重新显出差异。完整标签关系因此保留了被全部最小值汇总删掉的信息。

## 追加锚（本行以下为增补区）

## 34. 完整原标签二元函数的实际域剖面损失与半维尖锐边界

**定义 34.1（完整二元函数的剖面逆问题）。** 固定特征零域 $F$ 及实际有限扩张 $D/F$，$[D:F]=2m$。对每个 $m$ 维窗口 $X\le_F D$，沿用 $d_X(r)=\dim_F(X\cap rX)$、$J_X(r,s)=\dim_F(X\cap rX\cap sX)$、$D_X=F(X/X)$、$E_X=\{c\in D:cX\subseteq X\}$，以及 (33.1) 在每个实际中间域 $F\subseteq A\subseteq D$ 上的 $t_X(A)=\dim_F AX-m$。比较的是全部原 $r\in D^\times$ 上的函数 $d_X$，包含零交读数，不重标标签。记 $X^\perp$ 为乘法迹配对 $\operatorname{Tr}_{D/F}(xy)$ 的正交补。第 $j$ 阶最小正共同交维 $\delta_j(X)$ 仍允许重复原标签，且第一份窗口的标签为 $1$。

**定理 34.2（十二次原数域中的完整二元同读数与实际三次域分离）。** 取正实根 $\alpha^{12}=2$，在同一个原域中置

$$
\begin{aligned}
F&=\mathbb Q,&D&=\mathbb Q(\alpha),&A&=\mathbb Q(\alpha^4),\\
P&=\langle1,\alpha,\alpha^2,\alpha^3,\alpha^4,\alpha^8\rangle_{\mathbb Q}
=A\oplus\mathbb Q\alpha\oplus\mathbb Q\alpha^2\oplus\mathbb Q\alpha^3,\\
Q_0&=\langle\alpha,\alpha^2,\alpha^3,\alpha^5,\alpha^6,\alpha^7\rangle_{\mathbb Q}.
\end{aligned}
\tag{34.1}
$$

则 $[D:F]=12$、$[A:F]=3$，且

$$
\begin{gathered}
Q_0=P^\perp,\qquad D_P=D_{Q_0}=D,\qquad E_P=E_{Q_0}=\mathbb Q,\\
(m,N,e)=(6,12,1),\qquad
 d_P(r)=d_{Q_0}(r)\quad\text{对每个原 }r\in D^\times,\qquad P/P=Q_0/Q_0.
\end{gathered}
\tag{34.2}
$$

实际域剖面却满足

$$
\begin{aligned}
AP&=D,&AQ_0&=A\alpha\oplus A\alpha^2\oplus A\alpha^3,
&t_P(A)&=6,&t_{Q_0}(A)&=3,\\
BP&=BQ_0=D&&\text{对每个实际 }B\subseteq D\text{， }[B:\mathbb Q]=4,
&t_P(B)&=6,&t_{Q_0}(B)&=6.
\end{aligned}
\tag{34.3}
$$

这里四次域确实存在，例如 $\mathbb Q(\alpha^3)$；第二行量化全部实际四次域。

同一个原标签及其准确交空间为

$$
 r_* =\frac{\alpha^8}{1+\alpha^3},\qquad
 P\cap r_*P=\mathbb Q\alpha^8,\qquad
 Q_0\cap r_*Q_0=\mathbb Q\cdot(\alpha^3-\alpha^6).
\tag{34.4}
$$

对两个窗口共用一列 $r_1=1$、$r_i=r_*$（$i\ge2$），记 $I_j^X=\bigcap_{i=1}^j r_iX$。则

$$
\begin{aligned}
I_1^P&=P,&I_j^P&=\mathbb Q\alpha^8&&(j\ge2),\\
I_1^{Q_0}&=Q_0,&I_j^{Q_0}&=\mathbb Q\cdot(\alpha^3-\alpha^6)&&(j\ge2),\\
\delta_1(P)&=\delta_1(Q_0)=6,&
\delta_j(P)&=\delta_j(Q_0)=1&&(j\ge2).
\end{aligned}
\tag{34.5}
$$

而指定的同原三元标签给出

$$
\begin{aligned}
P\cap\alpha P\cap\alpha^2P
 &=\langle\alpha^2,\alpha^3,\alpha^4\rangle_{\mathbb Q},\\
Q_0\cap\alpha Q_0\cap\alpha^2Q_0
 &=\langle\alpha^3,\alpha^7\rangle_{\mathbb Q}.
\end{aligned}
\tag{34.6}
$$

特别地 $J_P(\alpha,\alpha^2)=3$、$J_{Q_0}(\alpha,\alpha^2)=2$，且不存在原 $x\in D^\times$ 使 $Q_0=xP$。

证明。$x^{12}-2$、$x^3-2$、$x^4-2$ 均在素数二处 Eisenstein，分别给出 $D$、$A$、$\mathbb Q(\alpha^3)$ 的实际次数。原幂基 $1,\alpha,\ldots,\alpha^{11}$ 线性独立，故两个窗口均为六维。$D_P$ 含原比值 $\alpha/1$，$D_{Q_0}$ 含原比值 $\alpha^2/\alpha$，所以两比值域均为 $D$。

先直接复用成熟乘法对偶机制，不将其另立为新定理。Bachoc–Serra–Zémor，[*Revisiting Kneser's theorem for field extensions*，arXiv:1510.01354v2，§2.2，式 (2)](https://arxiv.org/pdf/1510.01354v2)，给出非零泛函 $\lambda$ 所诱导的非退化结合配对 $\lambda(xy)$；Ueoka–Nagi–Akari–Sui，[*Weak Vishik Equivalence and Linear 2-Basis Blindness for Totally Singular Quadratic Forms*，Zenodo 21758447，Lemma 4.1、Theorem 4.2](https://zenodo.org/records/21758447)，已经证明任意有限域扩张中的半维正交补具有相同全部标量交维。对定义 34.1，$\lambda=\operatorname{Tr}_{D/F}$ 非零，因为 $\lambda(1)=2m\ne0$。对任意半维 $X$、$Y=X^\perp$ 及任意原 $r\ne0$，其维数推导正是

$$
\begin{aligned}
(X+rX)^\perp&=Y\cap r^{-1}Y,\\
d_X(r)&=2m-\dim_F(X+rX)
=\dim_F(Y\cap r^{-1}Y)
=\dim_F(Y\cap rY)=d_Y(r).
\end{aligned}
\tag{34.7}
$$

末一步由乘以同一个 $r$ 给出，故最终是同原标签 $r$ 的相等。推导没有正交叠前件，包含全部零读数。

在 (34.1) 的原幂基上，乘以 $\alpha^k$（$1\le k\le11$）没有对角项，故 $\operatorname{Tr}(\alpha^k)=0$，而 $\operatorname{Tr}(1)=12$、$\operatorname{Tr}(\alpha^{12})=24$。对 $0\le i,j\le11$，配对 $\operatorname{Tr}(\alpha^{i+j})$ 仅在 $i+j=0$ 或 $12$ 时非零；较高次用 $\alpha^{12}=2$ 降幂即可。于是 $z=\sum_{i=0}^{11}c_i\alpha^i$ 与 $P$ 正交恰好要求

$$
c_0=c_{11}=c_{10}=c_9=c_8=c_4=0.
\tag{34.8}
$$

剩下的六个方向正是 $Q_0$，从而 $Q_0=P^\perp$，(34.7) 给出全部原标签的二元相等。对任何窗口 $X$，$X/X=\{0\}\cup\{r\in D^\times:d_X(r)>0\}$，因为非零交向量恰写成 $u=rv$、$u,v\in X\setminus\{0\}$。这也证明 (34.2) 的实际比值集合等式，包括零。

下面独立核对实际域的干扰。由 $[D:A]=4$，$1,\alpha,\alpha^2,\alpha^3$ 是 $A$-基；因此 $AP=D$，而 $AQ_0$ 恰为 (34.3) 的三个直和方向，维数为九。对任意已经存在的实际四次域 $B\subseteq D$，合成域 $BA\subseteq D$ 的次数同时被三和四整除，故只能为十二，即 $BA=D$。因 $A\subseteq P$，有 $BP\supseteq BA=D$。另一方面 $[D:B]=3$ 且 $B(\alpha)=D$，所以 $1,\alpha,\alpha^2$ 在 $B$ 上构成基；$Q_0$ 包含 $\alpha,\alpha^2,\alpha^3$，故 $BQ_0\supseteq\alpha(B+B\alpha+B\alpha^2)=D$。这证明全部四次域的饱和，而没有从次数整除假造子域，也不需要列举这些域。剖面数值由减去六得到。

为证明 (34.4)，令 $v=1+\alpha^3$。对 $x\in P$，条件 $x\in r_*P$ 等价于 $vx\in\alpha^8P$，而

$$
\alpha^8P=\langle1,\alpha^4,\alpha^8,\alpha^9,\alpha^{10},\alpha^{11}\rangle_{\mathbb Q}.
$$

写 $x=c_0+c_1\alpha+c_2\alpha^2+c_3\alpha^3+c_4\alpha^4+c_8\alpha^8$。比较 $vx$ 的 $\alpha,\alpha^2,\alpha^6,\alpha^7,\alpha^3$ 系数，依次强制 $c_1=c_2=c_3=c_4=c_0=0$；$c_8$ 任意，且 $v\alpha^8=\alpha^8+\alpha^{11}$ 确属目标空间。因此第一条交空间准确成立。

对 $x\in Q_0$，同样要求 $vx\in\alpha^8Q_0=\langle\alpha,\alpha^2,\alpha^3,\alpha^9,\alpha^{10},\alpha^{11}\rangle_{\mathbb Q}$。写 $x=b_1\alpha+b_2\alpha^2+b_3\alpha^3+b_5\alpha^5+b_6\alpha^6+b_7\alpha^7$，比较 $vx$ 的 $\alpha^4,\alpha^8,\alpha^7,\alpha^5,\alpha^6$ 系数，所得全部约束恰为

$$
b_1=b_5=b_7=b_2=0,\qquad b_6=-b_3.
\tag{34.9}
$$

故第二条交空间也准确成立。两个非零生成元在同一份原窗口中的缩放前像分别为

$$
\frac{\alpha^8}{r_*}=1+\alpha^3\in P,\qquad
\frac{\alpha^3-\alpha^6}{r_*}=\tfrac12\alpha^7-\alpha\in Q_0.
\tag{34.10}
$$

因此重复同一个 $r_*$ 保持各自同一个原非零向量，得到 (34.5) 的全部前缀；任意正共同交维至少为一，故这些前缀同时达到全部正最小值。若 $c\in E_X$、$X=P$ 或 $Q_0$，交换乘法使 $c$ 稳定 $X\cap r_*X$；该交是一条非零有理直线，故 $c\in\mathbb Q$。反向包含显然，于是两稳定子均为 $\mathbb Q$，共同参数全部得证。

最后，在原幂基上逐方向相交，有

$$
\begin{aligned}
P\cap\alpha P&=\langle\alpha,\alpha^2,\alpha^3,\alpha^4\rangle_{\mathbb Q},&
P\cap\alpha^2P&=\langle\alpha^2,\alpha^3,\alpha^4\rangle_{\mathbb Q},\\
Q_0\cap\alpha Q_0&=\langle\alpha^2,\alpha^3,\alpha^6,\alpha^7\rangle_{\mathbb Q},&
Q_0\cap\alpha^2Q_0&=\langle\alpha^3,\alpha^5,\alpha^7\rangle_{\mathbb Q}.
\end{aligned}
\tag{34.11}
$$

每行两空间再相交即为 (34.6)。原标量整体缩放保持每个 $J_X(r,s)$；也保持每个 $\dim_F AX$，因为 $A(xX)=x(AX)$。所以三元读数差异或 (34.3) 的剖面差异都独立排除 $Q_0=xP$。$\square$

**定理 34.3（任意半维窗口对的尖锐剖面恢复边界）。** 对任意特征零实际有限扩张 $D/F$，$[D:F]=2m$、$m\le5$，以及任意两个 $m$ 维窗口 $X,Y\le_F D$，若 $d_X(r)=d_Y(r)$ 对全部原 $r\in D^\times$ 成立，则 $t_X(A)=t_Y(A)$ 对每个实际中间域 $F\subseteq A\subseteq D$ 成立。这里不要求 $Y=X^\perp$，也不要求 $D_X=D_Y=D$。定理 34.2 因而使 $(m,[D:F])=(6,12)$ 成为整个半维类中完整二元函数不能恢复实际域剖面的首个规模，特别也是半维迹对偶家族内的首个规模。

证明。$E_X=\{0\}\cup\{r\in D^\times:d_X(r)=m\}$，因为等维空间的交维为 $m$ 恰好表示 $rX=X$；因此 $E_X=E_Y$。若实际 $A/F$ 为二次，任取原 $\gamma\in A\setminus F$，有 $A=F+F\gamma$，从而

$$
AX=X+\gamma X,\qquad t_X(A)=m-d_X(\gamma).
\tag{34.12}
$$

故全部实际二次域的条目均由原标签函数决定。

若实际 $[D:A]=2$，则 $[A:F]=m$，$AX$ 的 $A$-维数只能为一或二。它等于一时，$X$ 与包含它的那条 $A$-直线同为 $m$ 维，故两者相等，即 $AX=X$、$A\subseteq E_X$；反之 $A\subseteq E_X$ 显然给出此情形。否则 $AX=D$。因此

$$
t_X(A)=
\begin{cases}
0,&A\subseteq E_X,\\
m,&A\not\subseteq E_X.
\end{cases}
\tag{34.13}
$$

这些条目同样由 $d_X$ 决定。对 $2m\in\{2,4,6,8,10\}$，域塔表明每个实际非平凡真中间域的次数要么为二，要么为 $m$；后者正是指数二的情形。端点恒为 $t_X(F)=0$、$t_X(D)=m$。这就穷尽全部实际域，证明对任意窗口对的恢复；没有用次数列表断言任何子域存在。定理 34.2 在半维六的实际域中给出反例，故边界尖锐。

这一结论的范围区别于 §33：那里全部最小值序列已在 $(3,6)$ 丢失剖面，但 (33.5) 的同一实际二次标签会区分完整二元函数。本条恢复的是剖面，不是窗口轨道；前卷 [R5_022 命题 24.2](AURIC_R5_022_ORIENTED_AREA_AND_TERNARY_RETURN.md) 已有 $(4,8)$ 的完整原标签二元碰撞及指定三元分离。Zenodo 21758447 的 Lemma 6.1、Proposition 6.5 更已有特征二实际十六次扩张中的八维对偶对，以及实际四次域 $k(t,su)$ 上的张成秩四与三；故“对偶二元碰撞仍丢失域剖面”这一机制也不是新增。

有限域线性集与轨道码中的相关不变量同样直接复用：Castello–Polverino–Zullo，[*Full weight spectrum one-orbit cyclic subspace codes*，arXiv:2405.19911v1，Definition 2.2、Remark 3.2](https://arxiv.org/html/2405.19911v1)，已分别定义子域张成秩 $\delta_a(X)=\dim_{\mathbb F_{q^a}}\mathbb F_{q^a}X$ 并说明迹正交补保持子域线性；此处的数值对应为 $t_X(\mathbb F_{q^a})=a\delta_a(X)-m$。本节相对于这些指定原文及仓内结果的推导差额（repo-derived）仅是特征零十二次原域中的 (34.1)–(34.6) 精确联合实现，以及 (34.12)–(34.13) 导出的整个半维类尖锐边界；不将已知配对、二元碰撞、域剖面盲性或最小值汇总再列为新机制。这里没有确定全球文献优先权，也没有解决任意 $N$ 下完整二元函数丢失剖面的最小窗口维数；尤其更高次数中的三维情形仍未由本条结算。$\square$

白话说，即使每个原比例都有名字，并且把所有零读数一并保留，逐次问“与这份倍乘窗口共享几维”仍会漏掉一个实际子域同时补齐窗口时需要多少方向。这对六维窗口的全部二元答案相同，同一个固定比例还能让两者从第二份起永远只剩一线；但实际三次域补齐一个要添六维，补齐另一个只添三维。同一个原向量同时通过 $\alpha$、$\alpha^2$ 两次要求时，剩下三维与二维，便切开这个二元观察纤维。Grimm–Baake，[*Homometric Point Sets and Inverse Problems*，arXiv:0808.0094v1，§§2、2.1](https://arxiv.org/pdf/0808.0094v1)，讨论完整差向量重数及 $\operatorname{vol}(K\cap(x+K))$ 仍不能唯一恢复集合；那是对这种信息损失的类比，这里没有把平移体积自相关与乘法交维建立为同一个数学问题。

## 追加锚（本行以下为增补区）

## 35. 三维窗口的完整原商支持恢复每个实际三次域的张成秩

**定义 35.1（原商支持与辅助射影边界）。** 设 $F$ 为特征零域，$D/F$ 为同一个实际有限域扩张，$N=[D:F]$。对三维 $F$-子空间 $W\le_F D$，要求 $F(W/W)=D$，并记

$$
Q_W=\{x/y:x,y\in W,\ y\ne0\}\subseteq D,\qquad
r_W(A)=\dim_A AW,\qquad t_W(A)=3r_W(A)-3,
\tag{35.1}
$$

其中 $A$ 始终是已经存在的实际中间域，$[A:F]=3$，$AW=\operatorname{span}_A W\subseteq D$。$Q_W$ 包含零；比较两个支持时逐个固定原 $D$ 元素，不允许重标记。

取包含原 $D$ 的有限正规闭包 $K/F$，固定代数闭包 $k\supseteq K$，令 $\Omega=\operatorname{Hom}_F(D,K)$。选原 $w_0\in W\setminus\{0\}$，置 $U=w_0^{-1}W$，取 $U$ 的 $F$-基 $u_1=1,u_2,u_3$。定义

$$
B_W=(\sigma(u_j))_{\sigma\in\Omega,\,1\le j\le3},\qquad
h_\sigma=(\sigma(u_1),\sigma(u_2),\sigma(u_3)),\qquad
H_W=B_WK^3,\qquad
\rho_W(S)=\dim_K\langle h_\sigma:\sigma\in S\rangle_K.
\tag{35.2}
$$

记 $\overline H_W=B_Wk^3$，在固定嵌入坐标的 $\mathbb P(k^\Omega)$ 中定义

$$
\begin{aligned}
Y_W&=\overline{\left\{\left[(u_\sigma/v_\sigma)_{\sigma\in\Omega}\right]:
0\ne u\in\overline H_W,\quad v\in\overline H_W\cap(k^\times)^\Omega\right\}}^{\mathrm{Zar}},\\
T_S&=\{[q]\in\mathbb P(k^\Omega):q_\sigma=0\ \Longleftrightarrow\ \sigma\in S\}
\qquad(\varnothing\ne S\subsetneq\Omega).
\end{aligned}
\tag{35.3}
$$

$Y_W$ 是扩底后的射影商像闭包，区别于实际集合 $Q_W$。对每个 $\tau\in\operatorname{Hom}_F(A,K)$，固定坐标块

$$
S_\tau=\{\sigma\in\Omega:\sigma|_A=\tau\}.
\tag{35.4}
$$

这些块只由同一实际包含关系 $F\subseteq A\subseteq D\subseteq K$ 决定。

**引理 35.2（三个等大秩二块必为平坦）。** 设 $M$ 为有限简单秩三拟阵，地集分拆为三个大小同为 $b\ge2$ 的秩二块 $B_1,B_2,B_3$。若一群拟阵自同构在地集上传递并保持此块分拆，则每个 $B_i$ 都是平坦（flat），即 $\operatorname{cl}_M(B_i)=B_i$。

证明。令 $L_i=\operatorname{cl}_M(B_i)$。地集传递性蕴含块上传递性。关系 $i\sim j\Longleftrightarrow L_i=L_j$ 是块集上的不变等价关系，其等价类等大；三个块使等价类只能全为单点或只有一个。后一种情形使整个地集落在一个秩二平坦中，与总秩三矛盾。因此三个 $L_i$ 两两不同，并非预设它们不同。

两个不同的秩二平坦至多共有一个元素：若交集含两个不同元素，简单性使其秩至少为二，秩的次模性便使两平坦的并仍为秩二，因而两平坦相等。令 $T$ 为至少属于两个 $L_i$ 的地集元素所成的集合。它是群不变集，且

$$
|T|\le\sum_{1\le i<j\le3}|L_i\cap L_j|\le3.
$$

若某个 $L_i$ 含有块外元素 $e\in B_j$，则 $e\in L_i\cap L_j$，故 $T$ 非空。传递性迫使 $T$ 为整个地集，却有 $3b\ge6>3$，矛盾。因此每个 $L_i$ 恰为 $B_i$。此论证适用于抽象简单拟阵，不使用域实现假设。$\square$

**定理 35.3（任意扩张次数下的实际三次域秩恢复）。** 对定义 35.1 中的每个实际三次域 $A$，若 $N=3$，则 $A=D$、$r_W(A)=1$。若 $N>3$，则 $r_W(A)\in\{2,3\}$，并且对任一块 $S_\tau$ 都有完整判据

$$
\boxed{\quad
r_W(A)=2\ \Longleftrightarrow\ Y_W\cap T_{S_\tau}\ne\varnothing,
\qquad
r_W(A)=3\ \Longleftrightarrow\ Y_W\cap T_{S_\tau}=\varnothing.
\quad}
\tag{35.5}
$$

特别地，$N=6$ 时每个这样的 $A$ 均有 $r_W(A)=2$。对同一个原 $D$ 中任意三维 $F$-子空间 $X,Z$，只要 $F(X/X)=D$，就有

$$
\boxed{\quad Q_X=Q_Z\quad\Longrightarrow\quad
\dim_A AX=\dim_A AZ\quad
\text{对每个实际 }A\subseteq D\text{， }[A:F]=3.\quad}
\tag{35.6}
$$

因此这些域上的 $t_X(A)$ 与 $t_Z(A)$ 也逐项相同。没有实际三次域时，最后的全称命题为空；$3\mid N$ 本身不制造子域。

证明。先沿用 §§26–28 的归一化、可分分裂与半线性行拟阵接口，在本三维参数下写明其前件。整体乘原标量给出 $Q_U=Q_W$、$\dim_A AU=\dim_A AW$，且 $1\in U\subseteq D$、$F(U)=D$。标准可分分裂给出

$$
D\otimes_F K\simeq K^\Omega,\qquad
G=\operatorname{Gal}(K/F),\qquad
g(h_\sigma)=h_{g\circ\sigma},\qquad
\rho_W(gS)=\rho_W(S).
\tag{35.7}
$$

分裂同构将 $U\otimes_F K$ 单射到 $K^\Omega$，像为 $H_W$，所以 $\rho_W(\Omega)=3$。每行首坐标为一；两行若成比例就必相等，两个嵌入遂在 $U$ 上相同，由 $F(U)=D$ 在整个 $D$ 上相同。因此行拟阵简单。正规闭包使每个 $F$-嵌入 $D\to K$ 延拓成 $K/F$ 的自同构，故 $G$ 在 $\Omega$ 上传递。式 (35.7) 是半线性等式；域自同构保持子式的零与非零，故它确实给出同一个行拟阵的自同构，未假设嵌入行一般位置。

$A/F$ 可分且次数为三，每个 $F$-嵌入 $A\to K$ 可延拓到 $D$。限制映射因此给出恰好三个非空块，$G$ 保持该分拆并在块上传递，各块大小为 $b=N/3=[D:A]$。取原包含嵌入 $\iota:A\hookrightarrow K$。对 $D/A$ 的同一分裂

$$
D\otimes_A K\simeq K^{S_\iota}
$$

把 $AU\otimes_A K$ 单射到右边，其像由 $u_1,u_2,u_3$ 的嵌入列张成。扩底保维及行列秩相等给出 $\rho_W(S_\iota)=\dim_A AU$；再由 (35.7) 将此等式传至其余两块，得到

$$
\rho_W(S_\tau)=r_W(A)\qquad\text{对全部三个 }\tau.
\tag{35.8}
$$

这复用的是 §29 中实际域张成与嵌入块秩的对应。若该秩为一，$1\in U$ 迫使 $AU=A$，从而 $D=F(U)\subseteq A$，故只能 $D=A$、$N=3$。反之 $N=3$ 时 $W=D$，结论成立。此后 $N>3$，所以 $b\ge2$，且 $2\le r_W(A)\le3$；$N=6$ 时还有 $r_W(A)\le[D:A]=2$，这也核对了既有 §33 的三次域条目。

现在建立从原商到几何闭包的一向桥。由于 $F$ 无限，$F^n$ 在 $k^n$ 中 Zariski 稠密：若一个 $k$ 系数多项式在全部 $F^n$ 上消失，按变量数归纳，一元多项式在无限子域上有无限多个根就为零，逐个系数也为零。将六个坐标都限制在无限集 $F^\times$ 上，同一归纳仍成立，故 $a,b\in F^3\setminus\{0\}$ 的点对在 $k^6$ 中稠密。考虑非空开集

$$
\mathcal O=\{(a,b)\in k^3\times k^3:a\ne0,\ \prod_{\sigma\in\Omega}(h_\sigma b)\ne0\}
$$

上的态射 $\phi(a,b)=[((h_\sigma a)/(h_\sigma b))_\sigma]$。总秩三保证 $B_Wa\ne0$。对每一对 $a,b\in F^3\setminus\{0\}$，原元素 $\sum a_ju_j$、$\sum b_ju_j$ 均非零；域嵌入使分母的所有坐标非零，故这些点全在 $\mathcal O$。它们的像恰是 $\{[(\sigma(r))_\sigma]:r\in Q_W\setminus\{0\}\}$。任何包含这些像的射影闭集，其在 $\mathcal O$ 中的逆像都是包含稠密点集的闭集，因而包含整个 $\mathcal O$。由 $Y_W$ 的定义遂得

$$
Y_W=\overline{\{[(\sigma(r))_{\sigma\in\Omega}]:r\in Q_W\setminus\{0\}\}}^{\mathrm{Zar}}.
\tag{35.9}
$$

所以原商相等蕴含同一固定坐标中的 $Y_X=Y_Z$；这里不使用闭包相等推出原商相等的逆命题。式 (35.9) 也表明 $Y_W$ 不依赖归一化或基的选择。

若 $r_W(A)=2$，由 (35.8) 三个块都是秩二。引理 35.2 使它们各自为平坦。固定 $S=S_\tau$，取非零列向量 $a\in K^3$，使 $h_\sigma a=0$ 对 $\sigma\in S$ 成立。块秩二使该公共核为一维；平坦性说明任何块外的行都不在块内行的张成中，所以 $h_\sigma a\ne0$ 对全部 $\sigma\notin S$ 成立。取 $b=(1,0,0)^{\mathsf T}$，则 $B_Wb=\boldsymbol1$。于是 $[B_Wa]=\phi(a,b)$ 已在几何商像中，并且恰好在 $S$ 上为零。这证明 $Y_W\cap T_S\ne\varnothing$。这里的 $a$ 可以在 $K^3$ 中选择，但未声称能在 $F^3$ 中选择。

余下的排除只需一个必要行列式。对射影坐标的任一代表 $q$，置

$$
M_W(q)=[\,B_W\mid-\operatorname{diag}(q)B_W\,].
\tag{35.10}
$$

在几何商像的代表 $q_\sigma=(h_\sigma a)/(h_\sigma b)$ 上，$M_W(q)(a,b)^{\mathsf T}=0$，其中 $b\ne0$，故这是非零核向量。因而每个六阶子式均为零。这样的子式在 $q$ 中齐次三次，因为每一行列式项恰从后三列取三个含 $q$ 的因子；故其零集是射影闭集，包含整个 $Y_W$。这仅为必要方程，不要求这些子式完整定义 $Y_W$。

若一个子集 $S$ 及其补集都为秩三，分别选三行基 $I\subseteq S$、$J\subseteq\Omega\setminus S$。在 $T_S$ 上，按先 $I$ 后 $J$ 排列所选六行，矩阵 (35.10) 的右上三阶块为零，故其六阶子式为

$$
\det\!\left((M_W(q))_{I\cup J}\right)
=\pm\det\!\left((B_W)_I\right)\det\!\left((B_W)_J\right)\prod_{\sigma\in J}q_\sigma\ne0.
\tag{35.11}
$$

两个三阶行子式及全部补集坐标都非零，故 $Y_W\cap T_S=\varnothing$。当 $r_W(A)=3$ 时，(35.8) 使 $S_\tau$ 为秩三，而其补集含另一整个秩三块，也为秩三，恰好满足此排除前件。结合秩一已排除及秩二的可达性，得到 (35.5)。没有将块秩三直接替代补集秩的核对。

最后设 $Q_X=Q_Z$。集合相等先给出 $F(Z/Z)=F(X/X)=D$，所以两个窗口都满足上述全部前件。独立归一化不改变各自的原商或 $A$-张成秩。固定同一个 $K,\Omega,A$ 及同一个块 $S_\tau$，(35.9) 给 $Y_X=Y_Z$；$N=3$ 的既有分支或 $N>3$ 的 (35.5) 随即给出 $r_X(A)=r_Z(A)$。任取实际 $A$ 都可如此处理，故结论是逐个原有子域的相等，并非只比较可能的次数或无标签的秩集合。式 (35.1) 给损失相等。$\square$

本定理的文献对应与推导范围。归一化、可分分裂和正规闭包的半线性行对称性已在 §§26–28 使用；(35.8) 的实际域接口已见 (29.7)–(29.8)，$N=3,6$ 的秩结算分别属于 §§27、33。无限域的多项式稠密性也是标准中间工具，这些均不作为新增基础。

Bernstein，[*Generic symmetry-forced infinitesimal rigidity: translations and rotations*，arXiv:2003.10529v4，Definition 2.10、Theorem 3.1](https://arxiv.org/html/2003.10529v4)，定义 Hadamard 乘积为逐坐标乘积像的 Zariski 闭包，并对两个不落在坐标超平面内的复线性空间给出 $\mathcal M(U\star V)=\mathcal M(r_U+r_V-1)$。Antolini–Dewar–Tanigawa，[*Dilworth truncations and Hadamard products of linear spaces*，arXiv:2508.04798v1，Examples 2.2–2.3、§3.2 式 (7)–(9)](https://arxiv.org/html/2508.04798v1)，给出秩函数和线性子空间族的对应，以及两个线性因子的泛切面矩阵接口。这些成熟的拟阵与 Hadamard 工具已有先例；此处商像的第二因子经过逐坐标取逆，不能预设为第二个线性空间而直接套用两线性因子公式。证明 (35.5) 只用三个块的平坦性和必要行列式，不要求窗口一般位置、完整消元方程或热带化的完整描述。

Napolitano–Polverino–Santonastaso–Zullo，[*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，§2.1](https://arxiv.org/html/2201.02003v1)，分别定义线性集的点支持、相对于定义空间的点权及几何线性域；Castello–Polverino–Zullo，[*Full weight spectrum one-orbit cyclic subspace codes*，arXiv:2405.19911v1，Definition 2.2](https://arxiv.org/html/2405.19911v1)，已定义子域张成秩 $\delta_t(S)=\dim_{\mathbb F_{q^t}}\langle S\rangle_{\mathbb F_{q^t}}$。在相应有限域记号中，取定义空间 $W\times W\subseteq D^2$，其线性集的有限斜率支持正是 $Q_W$；非零斜率 $r$ 的点权是 $\dim_F(W\cap rW)$，零斜率和无穷远点的权均为三。这里保留的是支持，没有附送点权；也不把有限域计数或其唯一子域性质移用于特征零。

相对于这些指定定义、定理及 §§26–28、33–34，仓内新增推导（repo-derived）是引理 35.2 与 (35.5)–(35.6) 的连接：三块对称性排除块闭包中的额外行，精确零坐标层区分实际三次域的秩二与秩三，再由原商的稠密性将该判据接回固定标签支持。上述先例归属不主张全球文献优先权。

白话说，同一个三次子域把所有嵌入分成三组。若窗口在这个子域下只需两条方向，每组都能出现一个恰好在该组消失的几何边界点；若需要三条方向，一个行列式便排除这种边界。完整原商支持确定同一份几何闭包，因此两份相同支持不能对这个三次子域给出不同张成秩。这些零坐标点只是证明工具：非零原域元素的每个嵌入都非零，不能把边界点冒作原域非零商。

结论只恢复每个实际三次域的张成秩，不恢复全部中间域剖面，也未判定三维窗口是否由 $Q_W$ 决定原标量轨道。§33 的最小值序列损失与 §34 的六维窗口反例仍保持原范围；§34 留下的任意 $N$ 下完整二元函数丢失全部实际域剖面的最小窗口维数仍为 open，本节只排除三维窗口在三次域条目上的此种损失，其它次数的域条目不在此结算。式 (35.9) 不给出几何闭包相等到原商相等的逆桥，也不提供有限查询、有效算法或噪声结论；它不推出量子起源、$\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义或 $H10(\mathbb Q)$。

## 追加锚（本行以下为增补区）

## 36. 完整三维原商支持的全实际中间域秩反单调性

**定义 36.1（固定实际域上的支持与秩剖面）。** 设 $F$ 为特征零域，$D/F$ 为同一个实际有限域扩张，$N=[D:F]$。对三维 $F$-子空间 $W\le_F D$，记

$$
\begin{aligned}
Q_W&=\{x/y:x,y\in W,\ y\ne0\}\subseteq D,\\
r_W(A)&=\dim_A AW,\qquad AW=\operatorname{span}_A W\subseteq D,\\
\mathcal R_W&:\{A:F\subseteq A\subseteq D\}\longrightarrow\{1,2,3\},
\qquad A\longmapsto r_W(A).
\end{aligned}
\tag{36.1}
$$

定义域中的 $A$ 均为原 $D$ 中已经存在的实际中间域。$Q_W$ 包含零；支持的包含或相等都逐个固定原 $D$ 元素，剖面的比较也逐个固定原子域。输入只有完整原商支持，不附加点权、窗口基或扩底后的新观察。

**引理 36.2（传递秩三拟阵的整块避让）。** 设 $M$ 为地集 $E$ 上的有限简单秩三拟阵，群 $\Gamma$ 在 $E$ 上传递地作用为拟阵自同构，并保持分拆 $\mathcal B=\{B_1,\ldots,B_m\}$。假设每个原块大小均为 $b$、秩均为二。则对每个 $B\in\mathcal B$，存在 $C\in\mathcal B$ 使

$$
C\cap\operatorname{cl}_M(B)=\varnothing.
\tag{36.2}
$$

证明。记 $L_i=\operatorname{cl}_M(B_i)$。两个不同的秩二平坦至多共有一个地集元素：简单性使两个不同元素张成秩二，含有它们的秩二平坦只能是它们的闭包。点上传递及分拆不变蕴含原块上传递，故不同闭包构成的集合 $\mathcal L$ 也传递；每个 $L\in\mathcal L$ 恰为同样数量 $c$ 个原块的闭包。$|\mathcal L|\ge2$，否则全部地集落在一个秩二平坦中。

固定 $L=\operatorname{cl}_M(B)$。若 $c\ge2$，任取不同于 $L$ 的 $L'\in\mathcal L$。闭包为 $L'$ 的 $c$ 个原块两两不交，全部包含在 $L'$ 中；因 $|L\cap L'|\le1$，至多一个这样的原块与 $L$ 相交，其余便满足 (36.2)。这已处理闭包重复的情形。

以下 $c=1$，所以 $L_1,\ldots,L_m$ 互异。反设每个原块都与固定的 $L$ 相交。由 $\Gamma$ 的传递性，每个 $L_i$ 都与每个 $B_j$ 相交；$i\ne j$ 时交集恰有一个元素。因此每个 $L_i$ 含 $k=b+m-1$ 个地集元素。点传递性又使每个元素属于同样数量 $d$ 个不同闭包。固定 $B_i$，计数其中元素与除 $L_i$ 外各闭包的关联；固定 $L_i$，计数其中元素与其余闭包的关联，分别得到

$$
b(d-1)=m-1,\qquad k(d-1)=m-1,\qquad k=b+m-1.
\tag{36.3}
$$

第二个计数成立，是因为每个 $L_j$（$j\ne i$）都与 $L_i$ 恰交一点。两式相减给出 $(m-1)(d-1)=0$。已有 $m\ge2$，故 $d=1$，再代入第一式却得 $m=1$，矛盾。同一点属于多条闭包时，每条关联各计一次；此处未假设各对闭包的交点互异。秩二及简单性已保证 $b\ge2$；空块、单点块及只有一个闭包的退化情形均由前件排除。故 (36.2) 对全部原块成立，不要求原块本身为平坦。$\square$

**定理 36.3（原商包含反向支配全部实际域上的张成秩）。** 设 $X,Z\le_F D$ 均为三维 $F$-子空间，且 $F(Q_X)=D$。则

$$
\boxed{\quad
Q_X\subseteq Q_Z
\quad\Longrightarrow\quad
r_Z(A)\le r_X(A)
\quad\text{对每个实际 }F\subseteq A\subseteq D.
\quad}
\tag{36.4}
$$

这里不限制 $N$、$[A:F]$ 或 $[D:A]$，不假定 $D/F$ 或 $A/F$ 正规。

证明。支持包含先给出 $D=F(Q_X)\subseteq F(Q_Z)\subseteq D$，故 $Z$ 也生成同一比值域。分别选原 $x_0\in X\setminus\{0\}$、$z_0\in Z\setminus\{0\}$，置 $U=x_0^{-1}X$、$V=z_0^{-1}Z$。沿用 §§26–29 的归一化，两个原支持及各自所有 $A$-张成秩都不变，且 $1\in U,V\subseteq D$、$F(U)=F(V)=D$：归一化窗口包含一，因而包含在自己的商支持中，而全部商又属于它生成的域。

取包含原 $D$ 的有限正规闭包 $K/F$，置 $\Omega=\operatorname{Hom}_F(D,K)$、$G=\operatorname{Gal}(K/F)$。分别取 $U,V$ 的原 $F$-基 $u_1=1,u_2,u_3$ 与 $v_1=1,v_2,v_3$。记

$$
B_X=(\sigma(u_j))_{\sigma,j},\qquad
B_Z=(\sigma(v_j))_{\sigma,j},\qquad
\rho_W(S)=\operatorname{rank}_K(B_W)_S\quad(W=X,Z).
\tag{36.5}
$$

特征零保证可分分裂 $D\otimes_F K\simeq K^\Omega$。它将 $U\otimes_F K$、$V\otimes_F K$ 单射到右边，所以两个矩阵都为列秩三。每行首坐标为一，故无零行；两行若成比例便相等，对应嵌入遂在归一化窗口上相同，由生成域条件在整个 $D$ 上相同。因此两个行拟阵均为有限简单秩三拟阵。

每个 $F$-嵌入 $D\to K$ 可延拓为 $K/F$ 自同构，所以 $G$ 在 $\Omega$ 上传递。对任一 $g\in G$，逐项作用给出

$$
g\bigl((\sigma(u_j))_j\bigr)=((g\circ\sigma)(u_j))_j,
\qquad \rho_W(gS)=\rho_W(S).
\tag{36.6}
$$

这是半线性行置换；域自同构保持子式的零与非零，故确实保持行拟阵。没有要求置换作用二重传递、基传递或具有任何额外的置换秩。

固定一个实际 $A$。对每个 $\tau\in\operatorname{Hom}_F(A,K)$，令 $S_\tau=\{\sigma:\sigma|_A=\tau\}$。可分性及嵌入延拓使这些集合构成 $G$ 保持的分拆，恰有 $[A:F]$ 个块，各含 $[D:A]$ 个元素。对原包含嵌入 $\iota:A\hookrightarrow K$，分裂 $D\otimes_A K\simeq K^{S_\iota}$ 将 $AU\otimes_A K$ 的像识别为 $u_1,u_2,u_3$ 的嵌入列张成；$V$ 同理。扩底保维及行列秩相等，再由 (36.6) 传至其余块，给出

$$
\rho_X(S_\tau)=r_X(A),\qquad
\rho_Z(S_\tau)=r_Z(A)\qquad\text{对每个 }\tau.
\tag{36.7}
$$

这正是 (29.7)–(29.8) 的实际域限制块接口，未从次数整除制造子域。端点为 $r_W(F)=3$、$r_W(D)=1$。若 $r_W(A)=1$，归一化后 $1\in U$（或 $V$）使其 $A$-张成为 $A$，故生成域条件迫使 $A=D$。因此真中间域 $F\subsetneq A\subsetneq D$ 上，两边秩都在 $\{2,3\}$ 内，并且不超过 $[D:A]$；特别是 $[D:A]=2$ 时两边均为二。$N\ge3$；$N=3,5$ 无真中间域，$N=4$ 的真中间域若存在则满足 $[D:A]=2$，所以这些小次数已由上述分支处理。

余下只须排除同一个实际 $A$ 上 $r_X(A)=2$、$r_Z(A)=3$。此时每个限制块在 $X$ 的行拟阵中秩二，在 $Z$ 的行拟阵中秩三，因而块大小至少为三、块数至少为二，特别是 $N\ge6$。

先把原支持包含转成原参数上的必要方程。任取 $D/F$ 的原基 $e_1,\ldots,e_N$；以此基的坐标列记原乘法矩阵

$$
\begin{aligned}
u(\alpha)&=\sum_{j=1}^3\alpha_j u_j,\qquad
u(\beta)=\sum_{j=1}^3\beta_j u_j,\\
L(\alpha,\beta)&=
[\,u(\beta)v_1\ \ u(\beta)v_2\ \ u(\beta)v_3
\mid -u(\alpha)v_1\ \ -u(\alpha)v_2\ \ -u(\alpha)v_3\,]
\in\operatorname{Mat}_{N\times6}(F[\alpha,\beta]).
\end{aligned}
\tag{36.8}
$$

对每个原 $\alpha\in F^3$、$\beta\in F^3\setminus\{0\}$，基的独立性保证 $u(\beta)\ne0$。由 $u(\alpha)/u(\beta)\in Q_U=Q_X\subseteq Q_Z=Q_V$，存在原 $p,q\in V$、$q\ne0$，使 $u(\beta)p-u(\alpha)q=0$。将 $p,q$ 在 $v_j$ 中展开，就得到 $L(\alpha,\beta)$ 的一个非零 $F$-核向量，其后三个系数不全为零。因此每个六阶子式在这些原参数上都为零。

矩阵恰有六列，故任一六阶子式使用全部列，是 $F[\alpha,\beta]$ 中关于两组参数分别齐次三次的多项式。特征零使 $F$ 无限；多项式若在 $(F^\times)^6$ 上恒零，逐变量使用一元多项式的根数界，再对系数归纳，便是零多项式。上段包含全部这些参数，故所有六阶子式都是恒零多项式。于是对任意辅助 $\alpha,\beta\in K^3$ 仍有

$$
\operatorname{rank}_K L(\alpha,\beta)\le5.
\tag{36.9}
$$

这里延拓的是已经在原 $F$ 参数上证明的多项式恒等式，没有将扩底后的商支持当作额外输入。

分裂同构的矩阵 $T=(\sigma(e_\ell))_{\sigma,\ell}$ 在 $K$ 上可逆。左乘整个原矩阵得到

$$
TL(\alpha,\beta)=
[\,\operatorname{diag}(B_X\beta)B_Z
\mid-\operatorname{diag}(B_X\alpha)B_Z\,].
\tag{36.10}
$$

左乘 $T$ 保持整个矩阵的秩，所以 (36.9) 保证 (36.10) 的每个六阶子式也为零；不需要将某个指定原子式误认作同一个分裂子式。特别地，取 $\beta=(1,0,0)^{\mathsf T}$，有 $B_X\beta=\boldsymbol1$。记 $q=B_X\alpha$，所得矩阵为 $[\,B_Z\mid-\operatorname{diag}(q)B_Z\,]$，其六阶子式关于 $q$ 齐次三次，每项恰从后三列取得三个 $q$ 因子。这些只作为必要方程，未宣称它们完整刻画原商支持或商像闭包。

现在固定一个原限制块 $B=S_\tau$。由 (36.7) 及引理 36.2，存在另一个完整原限制块 $C$，使 $C\cap\operatorname{cl}_X(B)=\varnothing$。在 $X$ 的行拟阵中，$B$ 秩二；取它的行张成的一个非零公共核向量 $\alpha\in K^3$。该公共核为一维；在行向量空间中，求值映射 $h\mapsto h\alpha$ 的二维核正是 $B$ 的行张成，故其零行集合恰为闭包。因此

$$
q_\sigma=(B_X\alpha)_\sigma=0\quad(\sigma\in B),
\qquad q_\sigma\ne0\quad(\sigma\in C).
\tag{36.11}
$$

闭包可含其他块的部分或全部元素；这里只使用 $C$ 完全避开它，不要求闭包恰等于 $B$，也不要求不同块闭包互不相交。

在 $Z$ 的行拟阵中，$B,C$ 都为秩三，故可分别选三行基 $I\subseteq B$、$J\subseteq C$。六行互异。按先 $I$ 后 $J$ 排列，(36.10) 在这些行及全部六列上的子式是块三角行列式，满足

$$
\det\begin{pmatrix}
(B_Z)_I&0\\
(B_Z)_J&-\operatorname{diag}(q_J)(B_Z)_J
\end{pmatrix}
=\pm\det((B_Z)_I)\det((B_Z)_J)\prod_{\sigma\in J}q_\sigma
\ne0.
\tag{36.12}
$$

最后的不等式由两组三行基及 (36.11) 保证，与 (36.9)–(36.10) 矛盾。因此 $r_X(A)=2$ 时 $r_Z(A)$ 不能为三；连同端点及其余秩分支，得到 (36.4)。$A$ 从始至终是任取的原实际中间域，所以结论同时覆盖整个逐域剖面。

向量 $\alpha$ 与零坐标向量 $q$ 只在 $K$ 中用于恒等式反证；没有从它们返回原 $F$ 参数的要求，也没有把带零嵌入坐标的非零 $q$ 冒作非零原域元素的嵌入像。证明未使用正交补、线性第二因子或任何扩底观察。$\square$

**推论 36.4（相等支持恢复整个带实际域标签的秩剖面）。** 在定理 36.3 的条件下，

$$
\boxed{\qquad Q_X=Q_Z\quad\Longrightarrow\quad
\mathcal R_X=\mathcal R_Z.\qquad}
\tag{36.13}
$$

证明。相等先使两边都生成 $D$，然后对两个方向分别应用 (36.4)。因此每一个原实际 $A$ 都有 $r_X(A)=r_Z(A)$。若用 §§29、33 的张成损失记号，则 $t_W(A)=\dim_F AW-3=[A:F]r_W(A)-3$，故这些损失也逐域相等；系数为实际的 $[A:F]$。$\square$

数学引文与推导差额。§§26–29 的归一化、可分分裂、原系数子式及无限域恒等延拓在此复用；(29.7)–(29.8) 已给实际域与限制块秩的接口。§27 的三维轨道恢复使用三元支持，§33 的六次域结算区分最小值序列与完整二元读数，§34 的反例使用六维窗口；它们均不直接给出 (36.4)。§35 的三次域判据保留原陈述，本节补足其未覆盖的全部实际域条目，并给出支持包含的方向。

Bernstein，[*Generic symmetry-forced infinitesimal rigidity: translations and rotations*，arXiv:2003.10529v4，Definition 2.10、Theorem 3.1](https://arxiv.org/html/2003.10529v4)，给逐坐标乘积像闭包的定义及不落在坐标超平面内的两个复线性空间的 Hadamard 乘积拟阵公式。Antolini–Dewar–Tanigawa，[*Dilworth truncations and Hadamard products of linear spaces*，arXiv:2508.04798v1，Examples 2.2–2.3、§3.2 式 (7)–(9)](https://arxiv.org/html/2508.04798v1)，给秩函数的线性子空间实现及两个复线性因子的切面矩阵接口。这些是已有工具的文献先例；本证明的 (36.8) 来自原乘法和支持包含，未将逐坐标取逆后的因子认作线性空间，也不调用 Hadamard 秩公式来刻画商支持。

Napolitano–Polverino–Santonastaso–Zullo，[*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，§2.1](https://arxiv.org/html/2201.02003v1)，分别定义线性集的点支持、相对于定义空间的点权及几何线性域。Castello–Polverino–Zullo，[*Full weight spectrum one-orbit cyclic subspace codes*，arXiv:2405.19911v1，Definition 2.2](https://arxiv.org/html/2405.19911v1)，定义子域张成秩 $\delta_t(S)=\dim_{\mathbb F_{q^t}}\langle S\rangle_{\mathbb F_{q^t}}$。对定义空间 $W\times W$，有限斜率的点支持对应 $Q_W$，非零斜率的点权对应 $\dim_F(W\cap rW)$；这里仅保留支持。上述有限域定义提供记号及问题背景，不将有限域的计数或唯一子域性质移用于特征零的实际域。

相对于这些指定原文条目与仓内 §§26–29、33–35，仓内推导（repo-derived）的差额是引理 36.2 的整块避让及其与 (36.7)、必要子式 (36.12) 的全实际域连接。无需逐次数证明原块为平坦；一个关于所有原块的关联约束已足够。标准行列式、稠密性、归一化与分裂不另计新内容。此处的对应范围限于所列原文条目；新连接的外部精确重合与全球文献优先权未确定。

白话说，一个实际中间域把全部嵌入按“在这个子域上的取值相同”分组。窗口若在该子域下只需两个方向，某组的行就能被一个辅助线性函数全部消去；虽然它还可能消去别组的部分行，传递对称性仍保证至少有一整组完全避开零点。若支持更大的另一个三维窗口在同一子域下反而需要三个方向，这两整组各自便能选出三条独立行，拼出一个非零行列式。可是原商支持包含已经迫使这个行列式在所有原参数上恒零，因而在辅助域上也恒零，矛盾。所以原商支持增大时，每个实际中间域上的张成秩只能减小或不变；支持相等时，逐个原子域的秩便全部相等。辅助域与零坐标只用于证明，不是额外可读取的数据，也不是原域中的非零商。

结论止于完整原商支持的包含方向及整个实际中间域张成秩剖面的恢复；不声称恢复三维窗口的原标量轨道、全部点权或完整二元交维函数，不给有限查询、有效算法或噪声结论，也不判定最小反例规模。§§33–34 的序列损失与六维反例保留原范围；本定理不推出物理量子起源、$\mathbb Z$ 在 $\mathbb Q$ 中的丢番图定义或 $H10(\mathbb Q)$。

## 追加锚（本行以下为增补区）

## 37. 四维窗口在实际三次域上的逐原标量秩二判据

**定义 37.1（固定实际三次域与四维窗口）。** 固定特征零域 $F$、实际有限扩张 $D/F$ 及已经存在的实际中间域 $F\subseteq A\subseteq D$，$[A:F]=3$。对四维 $F$-子空间 $W\le_F D$，沿用 §§28–29、36 的记号

$$
d_W(r)=\dim_F(W\cap rW)\quad(r\in D^\times),\qquad
AW=\operatorname{span}_A W\subseteq D,\qquad
r_W(A)=\dim_A AW.
\tag{37.1}
$$

所有标量与张成都使用原 $D$ 的乘法；不要求 $F(W/W)=D$，也不要求稳定子 $E_W=\{c\in D:cW\subseteq W\}$ 等于 $F$。

**定理 37.2（一次原三次标量交叠判别秩二）。** 在定义 37.1 的条件下，$2\le r_W(A)\le\min\{4,[D:A]\}$，且对每个原 $a\in A\setminus F$，

$$
\boxed{\qquad d_W(a)\ge2\quad\Longleftrightarrow\quad r_W(A)=2.\qquad}
\tag{37.2}
$$

因此秩二时每个这样的原标量都给交维至少二；秩三或四时每个这样的原标量都给交维至多一。

证明。$[A:F]=3$ 为素数，故 $F(a)=A$，且 $1,a,a^2$ 是 $A/F$ 的基。$W$ 不可能容在一条只有三维的 $A$-直线上，而它的四个 $F$-基向量也张成 $AW$，所以秩具有所述上下界。若 $r_W(A)=2$，则 $\dim_F AW=6$；因 $W+aW\subseteq AW$，维数公式给出

$$
d_W(a)=8-\dim_F(W+aW)\ge8-6=2.
\tag{37.3}
$$

反之，设 $d_W(a)\ge2$。乘以 $a$ 将 $U=W\cap a^{-1}W$ 同构地映到 $W\cap aW$，故可取 $F$-线性独立的 $u,v\in U$。于是 $u,au,v,av$ 都在 $W$ 中。

若 $u,v$ 在 $A$ 上独立，则任何关系

$$
(c_0+c_1a)u+(c_2+c_3a)v=0\qquad(c_i\in F)
$$

先由 $A$-独立性，再由 $1,a$ 的 $F$-独立性，迫使所有 $c_i=0$。这四个向量因而是 $W$ 的 $F$-基，$AW=Au\oplus Av$，秩为二。

若 $u,v$ 在 $A$ 上依赖，则二者都在同一条 $Au$ 中。令 $S=Fu+Fv$，有 $\dim_F S=2$ 及

$$
S+aS\subseteq W\cap Au,\qquad 2\le\dim_F(S+aS)\le3.
$$

若中间维数为二，则 $aS=S$，故 $F[a]S=AS=S$，这使二成为三的倍数，矛盾。因此 $S+aS=Au\subseteq W$。取 $w\in W\setminus Au$，则 $W=Au\oplus Fw$、$AW=Au\oplus Aw$，秩仍为二。这也包含交叠向量全部落在同一条 $A$-直线上的情形。

若 $d_W(a)=4$，则 $aW=W$，同样会有 $AW=W$，与三不整除四矛盾；这里没有排除其它非平凡稳定子。环境的低次数也已包含：$[D:A]=1$ 时不存在四维 $W$；$[D:A]=2$ 时上述秩界迫使 $AW=D$、秩为二。全部论证在原 $D$ 内完成。$\square$

**推论 37.3（完整同原标签函数排除秩二与高秩混同）。** 固定同一个特征零实际有限扩张 $D/F$。若四维窗口 $X,Z\le_F D$ 满足

$$
d_X(r)=d_Z(r)\quad\text{对全部原 }r\in D^\times\text{，包括交维为零的读数},
\tag{37.4}
$$

则对每一个已经存在的实际三次中间域 $A\subseteq D$，

$$
r_X(A)=2\quad\Longleftrightarrow\quad r_Z(A)=2.
\tag{37.5}
$$

证明。固定该实际 $A$，取任一原 $a\in A\setminus F$，将 (37.4) 代入两次 (37.2) 即得。因此同一个实际 $A$ 上不能出现一方秩二、另一方秩三或四；没有这样的实际域时，全称结论为空。这个推论未判定秩三与四能否由完整函数区分，该问题仍未解决；也未给出其它次数域上的秩分类。已给定实际 $A$ 及其中一个标签时的充分读数，不提供寻找或取得 $A$、该标签的算法。$\square$

数学引文与推导范围。§§28–29 已给原交维、稳定子及实际域张成的接口，§§33–34 已区分最小值序列与完整逐标签函数；这些定义和维数工具在此直接复用。§§35–36 的恢复结论针对三维窗口，§34 的半维恢复结论也不涵盖任意环境次数下的 (37.2)。本节只接出四维窗口在固定实际三次域上的阈值及其逐标签推论。

Napolitano–Polverino–Santonastaso–Zullo，[*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，Proposition 6.3](https://arxiv.org/html/2201.02003v1)，在 $k+2\le\dim_F D$ 下分类 $\dim_F(W+aW)=k+1$ 的一般域临界对。这里 $k=4$ 时对应 $d_W(a)=3$；取 $[F(a):F]=3$，其形状为一条完整 $A$-直线加一条 $F$-方向。Castello–Polverino–Zullo，[*Full weight spectrum one-orbit cyclic subspace codes*，arXiv:2405.19911v1，Definition 2.2、Theorem 5.2](https://arxiv.org/html/2405.19911v1)，分别给子域张成秩的有限域记号及上述临界对结果的引用。Bachoc–Serra–Zémor，[*Revisiting Kneser's theorem for field extensions*，arXiv:1510.01354v2，§2.3，Lemma 13 后的有限维说明](https://arxiv.org/html/1510.01354v2)，给有限维稳定子成域的成熟事实。临界形状、张成秩与稳定子事实均不另计新内容；所列临界对条目没有给出一般 $d_W(a)=2$ 时的反向蕴含。相对于这些指定原文与仓内 §§28–29、33–36，本节属于仓内推导的应用桥（repo-derived）：用两个原交叠方向补足该蕴含，再得到 (37.5)。标准维数公式与域塔不计新内容；外部精确重合及全球文献优先权未确定。

白话说，固定一个确实存在的三次子域后，把窗口里的向量允许用该子域的数作系数，所需方向数只能是二、三或四。任选其中一个不属于底域的原数来倍乘窗口，只要交叠还有两个独立的底域方向，就能锁定这个数目为二：这两个方向若在子域上独立，它们及各自的倍乘已经填满四维窗口；若在子域上依赖，它们与倍乘会填满一条三维的子域直线，窗口只剩一个底域方向可补。反过来，两个子域方向总共只有六个底域维度，两份四维窗口放进去必共享至少两维。因此完整同标签答案相同的两个窗口，在这个实际三次域上不会一个秩二而另一个秩三或四；这没有回答三与四的区别，也没有替我们找到那个子域或可用的标签。

## 追加锚（本行以下为增补区）

## 38. 四维窗口在实际三次域上的秩三对四原标签分离

**定义 38.1（固定实际域与完整交维函数）。** 设 $F$ 为特征零域，$D/F$ 为实际有限域扩张，$F\subseteq A\subseteq D$ 为已经存在的实际中间域，$[A:F]=3$。对四维 $F$-子空间 $W\le_F D$，沿用

$$
d_W(r)=\dim_F(W\cap rW)\quad(r\in D^\times),\qquad
r_W(A)=\dim_A AW,\qquad AW=\operatorname{span}_A W\subseteq D.
\tag{38.1}
$$

完整函数保留全部同一原标签及零读数。这里不要求 $F(W/W)=D$，也不预设稳定子 $E_W=\{c\in D:cW\subseteq W\}$ 等于 $F$。

**定理 38.2（高秩分离及三次域条目的纤维不变性）。** 在定义 38.1 的条件下，若四维窗口 $X,Z\le_F D$ 满足 $r_X(A)=3$、$r_Z(A)=4$，则

$$
\boxed{\qquad \exists r\in D^\times:\quad d_X(r)>d_Z(r).\qquad}
\tag{38.2}
$$

因此完整同原标签函数的一个纤维不能同时含有在同一个实际 $A$ 上秩三与秩四的窗口。结合定理 37.2，对任意四维窗口 $X,Z\le_F D$，

$$
\bigl[\ \forall r\in D^\times,\ d_X(r)=d_Z(r)\ \bigr]
\quad\Longrightarrow\quad
r_X(A)=r_Z(A)
\quad\text{对每个实际三次中间域 }A\subseteq D.
\tag{38.3}
$$

证明。先证明 (38.2)，不使用 §37。令 $N=[D:F]$。由 $r_Z(A)=4$ 得 $[D:A]\ge4$、$N\ge12$；低于十二的环境次数不能满足这两个秩前件。

取 $X$ 的一个 $F$-基 $x_1,\ldots,x_4$。映射 $A^4\to AX$、$(c_i)\mapsto\sum c_ix_i$ 的核为一维 $A$-空间。选其非零向量 $\lambda=(\lambda_i)$，记 $s=\dim_F\langle\lambda_1,\ldots,\lambda_4\rangle_F$。若 $s=1$，除去一个共同非零 $A$ 因子就得到非零 $F$-关系，与基的独立性矛盾；故 $s=2$ 或三。

当 $s=2$ 时，先缩放关系使其系数张成 $F+Fa$，其中 $a\in A\setminus F$；当 $s=3$ 时，系数张成整个 $A$，任选 $a\in A\setminus F$，则 $1,a,a^2$ 是其 $F$-基。将系数向量按这两组基展开，所得两个或三个 $F^4$ 向量线性独立；把它们补成 $F^4$ 的基并相应更换 $x_i$，便分别得到

$$
\begin{array}{ll}
s=2:&\lambda=(1,a,0,0),\qquad x_1+ax_2=0,\\
s=3:&\lambda=(1,a,a^2,0),\qquad x_1+ax_2+a^2x_3=0.
\end{array}
\tag{38.4}
$$

这是基变换与关系的缩放，没有更换原域、窗口或观察标签。

复用 §§28–29、36 的可分分裂及限制块秩接口。取包含原 $D$ 的有限正规闭包 $K/F$，令 $\Omega=\operatorname{Hom}_F(D,K)$，并记

$$
S_\tau=\{\sigma\in\Omega:\sigma|_A=\tau\},\qquad
B_X=(\sigma(x_j))_{\sigma,j},\qquad
B_Z=(\sigma(z_j))_{\sigma,j},
\tag{38.5}
$$

其中 $z_1,\ldots,z_4$ 是 $Z$ 的任意 $F$-基。三个 $S_\tau$ 是非空互不相交的原限制块。由 $D\otimes_{A,\tau}K\simeq K^{S_\tau}$ 扩底保维，每块的 $B_X$ 行秩为三，$B_Z$ 行秩为四；这不要求归一化窗口生成 $D$，也不要求行拟阵简单。令 $\iota:A\hookrightarrow K$ 为原包含嵌入，置

$$
h_\sigma=\sum_{j=1}^4\lambda_j\sigma(x_j).
\tag{38.6}
$$

当 $\sigma\in S_\iota$ 时，$\sigma$ 固定全部 $\lambda_j$，故 $h_\sigma=0$。当 $s=2$ 且 $\sigma\notin S_\iota$ 时，由 (38.4) 得 $h_\sigma=(a-\sigma(a))\sigma(x_2)\ne0$；这里 $F(a)=A$，所以两种限制确实给不同的 $a$ 像。

先处理 $s=3$ 且存在块外额外零点的情形。设 $\sigma\notin S_\iota$、$h_\sigma=0$。在原 $D[T]$ 中置

$$
P(T)=x_1+x_2T+x_3T^2=x_3(T-a)(T-b),\qquad
b=-x_2/x_3-a\in D.
\tag{38.7}
$$

因 $P(a)=0$，上述分解成立。对系数施加 $\sigma$ 后，$\sigma(P)(a)=h_\sigma=0$，而 $a\ne\sigma(a)$，所以 $\sigma(b)=a$。若 $p(T)=T^3-s_1T^2+s_2T-s_3\in F[T]$ 是 $a$ 的最小多项式，则 $\sigma(p(b))=p(a)=0$；嵌入的单射性给出 $p(b)=0$。若 $b\in A$，则 $x_1/x_3=ab$、$x_2/x_3=-(a+b)$ 都在 $A$ 中，使 $AX\subseteq Ax_3+Ax_4$，与秩三矛盾。因此 $b\notin A$，特别是 $b\ne a$。

第三个根为 $c=s_1-a-b\in D$；可分性使三根互异。若 $c\in A$，又会有 $b\in A$，故 $c\notin A$。于是实际子域 $B=F(c)\subseteq D$ 为三次域，而 $c$ 在 $A$ 上满足 $p(T)/(T-a)$ 且不在 $A$ 中，给出 $[AB:A]=2$。由根与系数的关系，

$$
x_2/x_3=c-s_1,\qquad
x_1/x_3=ab=c^2-s_1c+s_2,\qquad
X=x_3B\oplus Fx_4.
\tag{38.8}
$$

最后一个等式使用 $1,c,c^2$ 的 $F$-独立性及原 $x_i$ 的基性质。特别是 $r_X(A)=3$ 还保证 $x_4\notin x_3AB$。这一步取得的是原 $D$ 内的三次域；没有假定原 $A$ 正规，若 $A$ 正规则此额外零点情形已被 $b\notin A$ 排除。

任取原 $\gamma\in B\setminus F$，则 $F(\gamma)=B$，而 $x_3B\subseteq X\cap\gamma X$。对任何四维窗口 $Y$，$d_Y(\gamma)=4$ 都会使 $\gamma Y=Y$，进而使 $Y$ 成为 $B$-空间，与三不整除四矛盾。因此 $d_X(\gamma)=3$、$d_Z(\gamma)\le3$。若 $d_Z(\gamma)=3$，就有 $\dim_F(Z+\gamma Z)=5$。直接应用 Napolitano–Polverino–Santonastaso–Zullo，[*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，Proposition 6.3](https://arxiv.org/html/2201.02003v1)：取其 $L=D$、$S=Z$、$T=\langle1,\gamma\rangle_F$、$k=4$、$t=[F(\gamma):F]=3$，且 $k+2=6\le N$。其第二分支的 $4=3\cdot1+1$ 给出 $Z=zB\oplus Fh$，其中 $z,h\in D^\times$、$hB\cap zB=\{0\}$。因而

$$
r_Z(A)\le\dim_A(zAB)+1=3,
\tag{38.9}
$$

矛盾。故 $d_Z(\gamma)\le2$，取同一个原 $r=\gamma$ 即得 (38.2)。临界形状在此只作为已有定理使用。

余下包括全部 $s=2$，以及 $s=3$ 无块外额外零点的情形；此时 $h_\sigma=0$ 恰当且仅当 $\sigma\in S_\iota$。取两组四元不定元 $t,y$，置 $u(t)=\sum t_jx_j$、$v(y)=\sum y_jx_j$。以 $D/F$ 的任一原基 $e_1,\ldots,e_N$ 记乘法坐标矩阵

$$
C(t,y)=[\ v(y)z_1\ \cdots\ v(y)z_4
\mid -u(t)z_1\ \cdots\ -u(t)z_4\ ]
\in\operatorname{Mat}_{N\times8}(F[t,y]).
\tag{38.10}
$$

可逆分裂矩阵 $T=(\sigma(e_\ell))_{\sigma,\ell}$ 给出

$$
TC(t,y)=[\operatorname{diag}(B_Xy)B_Z
\mid-\operatorname{diag}(B_Xt)B_Z].
\tag{38.11}
$$

只在辅助域中取 $t=\lambda$、$y=(1,0,0,0)^{\mathsf T}$。在 $S_\iota$ 中选 $B_Z$ 的四行基 $I$，在任一其它限制块中选四行基 $J$。按先 $I$ 后 $J$ 排列，(38.11) 的这八行形成块三角子式，其行列式为

$$
\pm\det((B_Z)_I)\det((B_Z)_J)
\prod_{\sigma\in I}\sigma(x_1)
\prod_{\sigma\in J}h_\sigma\ne0.
\tag{38.12}
$$

各因子非零分别由所选行基、$x_1\ne0$ 及无块外额外零点保证。故辅助取值处 $C$ 的秩为八，原坐标矩阵 (38.10) 必有一个非零八阶子式 $f\in F[t,y]$；这里用的是整个可逆矩阵 $T$ 保秩，不把分裂子式误认成同一个原子式。

$F$ 无限，非零多项式 $f(t,y)t_1y_1$ 可在某组原 $t,y\in F^4$ 取非零值；这是 §§28–29 已用的无限域多项式返回。于是原 $u=u(t),v=v(y)\in X\setminus\{0\}$ 满足 $\dim_F(vZ+uZ)=8$。取原 $r=u/v\in D^\times$，有

$$
d_Z(r)=\dim_F(vZ\cap uZ)=0,\qquad
u\in X\cap rX\setminus\{0\},\qquad d_X(r)\ge1.
\tag{38.13}
$$

这也证明 (38.2)。辅助零坐标和 $K$ 参数仅证明原系数子式非零；最终见证是同一原 $D$ 中的 $u/v$，两窗口在它处直接比较。两种系数维数及有无额外零点已经穷尽。

若两完整函数相等，(38.2) 排除同一实际 $A$ 上的秩三对四，交换窗口名也排除秩四对三。四维窗口的三次域张成秩只能为二、三或四；定理 37.2 已排除秩二与另外两种秩在同一纤维混同。故对每一个实际 $A$ 得 (38.3)；没有实际三次域时该全称结论为空。整个论证没有使用比值生成条件或平凡稳定子条件。$\square$

数学引文与推导范围。§§28–29、36 的可分分裂、实际域限制块秩、原乘法矩阵及无限域子式工具在此直接复用；§§35–36 的承重恢复结论针对三维窗口，§34.3 则要求环境次数为窗口维数的两倍，均不提供这里环境次数至少十二的四维高秩分离。§37 的秩二阈值只用于 (38.3) 的最后拼接。上述 Proposition 6.3 的一般域临界对形状已有先例；Castello–Polverino–Zullo，[*Full weight spectrum one-orbit cyclic subspace codes*，arXiv:2405.19911v1，Definition 2.2、Theorem 5.2](https://arxiv.org/html/2405.19911v1)，分别给有限域子域张成秩记号及该一般域命题的引用。它们不提供本条的同原标签高秩分离接口。相对于所列原文条目及仓内既有结果，本节的仓内推导（repo-derived）差额是：唯一三次关系的块外零点强制原域内的共轭根与实际三次域形状，再以临界交维和无额外零点的原参数子式两支闭合 (38.2)。标准域论、临界形状及子式返回不另列为新成果；该连接的外部精确重合与全球文献优先权未核实。

白话说，四个底域方向在三次子域下只需三个方向时，恰有一条子域系数的关系。把同一个实际域的嵌入按子域取值分成三组，这条关系会消掉其中一整组。如果它还消掉别组的某个位置，三次方程就迫使另两个共轭根也落在原域，窗口的三个方向因此正好拼成另一实际三次域的一条完整直线。取这个域里一个原数来倍乘，原窗口共享三维；秩四的竞争窗口若也共享三维，已有临界对定理便迫使它在原来的子域下至多秩三，矛盾。如果没有额外零点，两整组各选四条独立行便给出非零八阶行列式，再返回底域参数，取得一个原窗口确有交叠而竞争窗口交叠为零的同一原比例。因此全部同标签交维答案相同的窗口，对每一个已经存在的实际三次域都具有相同张成秩。

结论只排除上述秩差造成的完整函数碰撞，并不恢复窗口本身或其原标量轨道。严格不等式只需一个方向；共轭根分支给出 $d_X(r)=3$、$d_Z(r)\le2$，没有排除 $d_Z(r)>0$，所以它不把正支持当作完整函数，也不声称正支持必能分离。不结算其它次数域上的任意四维剖面，不给有限查询、有效算法、噪声结论或物理量子、$\mathbb Z/\mathbb Q$、$H10(\mathbb Q)$ 的推论。

## 追加锚（本行以下为增补区）

## 39. 单侧交维支配下的四维窗口标量刚性

**定义 39.1（原商支持与交维函数）。** 设 $F$ 为特征零域，$D/F$ 为有限扩张。对非零有限维 $F$-子空间 $W\le_F D$，定义

$$
 d_W(r)=\dim_F(W\cap rW)\quad(r\in D^\times),
 \qquad
 Q(W)=\left\{\frac uv:u,v\in W\setminus\{0\}\right\}\subseteq D^\times .
\tag{39.1}
$$

这里的商和标签都在同一个原域 $D$ 内。于是

$$
 r\in Q(W)\quad\Longleftrightarrow\quad d_W(r)>0.
\tag{39.2}
$$

若 $E(W)=\{c\in D:cW\subseteq W\}$，则 $E(W)$ 是含 $F$ 的子域，且

$$
 [E(W):F]\mid \dim_F W.
\tag{39.3}
$$

事实上，$cW\subseteq W$ 且 $c\ne0$ 时，乘法在有限维空间 $W$ 上单射，故 $cW=W$，再得 $c^{-1}W=W$。此外，对任意 $\gamma\in D^\times$，

$$
 d_{\gamma W}(r)=d_W(r),\qquad Q(\gamma W)=Q(W).
\tag{39.4}
$$

**定理 39.2（单侧支配刚性）。** 设 $X,Z\le_F D$ 且

$$
 \dim_F X=\dim_F Z=4,
 \qquad d_X(r)\le d_Z(r)\quad\text{对全部 }r\in D^\times .
\tag{39.5}
$$

若存在 $\mu\in D\setminus F$ 使 $d_X(\mu)\ge3$，则存在 $\gamma\in D^\times$ 使

$$
 \boxed{Z=\gamma X}.
\tag{39.6}
$$

因此实际上 $d_X(r)=d_Z(r)$ 对每一个原标签 $r$ 都成立。定理只使用同一 $D$ 内的逐标签交维支配；它不把商支持包含单独提升为完整交维支配。

**引理 39.3（四维窗口的高交叠形状）。** 设 $\mu\in D\setminus F$，$W\le_F D$ 且 $\dim_F W=4$；令 $K=F(\mu)$、$t=[K:F]$。

1. 若 $d_W(\mu)=4$，则 $W$ 是 $K$-空间，因而 $t\in\{2,4\}$。
2. 若 $d_W(\mu)=3$，则只有两种形状：

$$
\begin{array}{ll}
 t\ge5:& W=w\langle1,\mu,\mu^2,\mu^3\rangle_F,\\[2pt]
 t=3:& W=wK\oplus Fb,qquad b\notin wK,
\end{array}
\tag{39.7}
$$

其中 $w\in D^\times$。特别地，$t=2,4$ 时交维恰为三不可能。

**证明。** 若 $d_W(\mu)=4$，则 $\mu W=W$，所以 $W$ 是 $K=F[\mu]$-空间，$t$ 必须整除四；因 $\mu\notin F$，得到 $t=2$ 或 $4$。

以下设 $d_W(\mu)=3$。置

$$
 W_i=\{w\in W:\mu^jw\in W\text{ 对 }0\le j\le i\}.
$$

则 $W_0=W$。乘以 $\mu$ 将 $W\cap\mu^{-1}W$ 同构地送到 $\mu W\cap W$，所以 $\dim_F W_1=d_W(\mu)=3$。对 $i\ge1$，映射
$W_{i-1}\to W/W_1$、$w\mapsto\mu^{i-1}w+W_1$ 的核为 $W_i$，所以每次下降至多一维；从而

$$
 \dim_F W_2\ge2,\qquad \dim_F W_3\ge1.
\tag{39.8}
$$

若 $t\ge4$，取 $0\ne w\in W_3$。因为 $1,\mu,\mu^2,\mu^3$ 在 $F$ 上独立，四个向量 $w,\mu w,\mu^2w,\mu^3w$ 构成 $W$ 的基，得到第一种形状。$t=4$ 时它等于 $wK$，于是 $\mu W=W$，与交维三矛盾，故只能有 $t\ge5$。

若 $t=2$，$W_1$ 在乘以 $\mu$ 下稳定：$\mu^2$ 是 $1,\mu$ 的 $F$-线性组合。因此 $W_1$ 是 $K$-空间，三维不可能。若 $t=3$，同理 $W_2$ 在乘以 $\mu$ 下稳定。由 (39.8) 及 $W_2\subseteq W_1$，其维数介于二和三之间，又必须是三的倍数，故 $\dim_F W_2=3$。于是 $W_2=wK$，补上一条 $F$-方向即得第二种形状。证毕。

**引理 39.4（同一三次子域的两标签支持刚性）。** 设 $F\subsetneq K\subseteq D$，$[K:F]=3$，并令

$$
 U=K\oplus Fa,qquad V=K\oplus Fb,qquad a,b\notin K.
\tag{39.9}
$$
固定 $\kappa_0\in K\setminus F$。若

$$
 a\in Q(V),\qquad a+\kappa_0\in Q(V),
\tag{39.10}
$$
则存在 $\lambda\in K^\times$ 使 $V=\lambda U$。特别地，$Q(U)\subseteq Q(V)$ 足以推出这一结论。

**证明。** 由 $a\in Q(V)$，可写成

$$
 a=\frac{u+sb}{v+tb},qquad u,v\in K,\quad s,t\in F,\quad v+tb\ne0.
\tag{39.11}
$$
若 $t=0$，则 $s\ne0$，否则 $a\in K$。于是

$$
 b=\frac vs a-\frac us,qquad
 V=\frac vs(K+Fa)=\frac vs\,U.
\tag{39.12}
$$

若 $t\ne0$，置 $c=s/t\in F$、$A=a-c$。则 $A\notin K$，并且由 (39.11)

$$
 b=h+\frac gA,qquad h=-\frac vt\in K,\quad g=\frac{u-cv}{t}\in K^\times.
\tag{39.13}
$$

故

$$
 U=K+FA,qquad g^{-1}V=K+FA^{-1}.
\tag{39.14}
$$

第二个原标签仍然是 $a+\kappa_0=A+\kappa$，其中 $\kappa=\kappa_0+c\in K\setminus F$。由其属于 $Q(V)=Q(g^{-1}V)$，存在 $p,q\in K$、$e,f\in F$ 使

$$
 A+\kappa=\frac{p+eA^{-1}}{q+fA^{-1}}=\frac{pA+e}{qA+f},qquad qA+f\ne0.
\tag{39.15}
$$

交叉相乘得到

$$
 qA^2+(q\kappa+f-p)A+(f\kappa-e)=0.
\tag{39.16}
$$

若 $1,A,A^2$ 在 $K$ 上独立，则 $q=0$、$p=f$、$f\kappa=e$。分母条件给 $f\ne0$，遂有 $\kappa=e/f\in F$，矛盾。因此 $A$ 在 $K$ 上的次数为二；写成

$$
 A^2+\rho A+\sigma=0,qquad \rho,\sigma\in K,\quad \sigma\ne0.
\tag{39.17}
$$
于是 $A^{-1}=-\sigma^{-1}A-\rho/\sigma$，从 (39.14) 得

$$
 V=g(K+FA^{-1})=-\frac g\sigma(K+FA)=-\frac g\sigma U.
\tag{39.18}
$$
证毕。

**定理 39.2 的证明。** 由 (39.5) 先得

$$
 Q(X)\subseteq Q(Z).
\tag{39.19}
$$
固定一个 $\mu$ 使 $d_X(\mu)\ge3$，置 $K=F(\mu)$、$t=[K:F]$。

若 $d_X(\mu)=4$，则 (39.5) 及维数上界给 $d_Z(\mu)=4$。引理 39.3 说明 $X,Z$ 都是 $K$-空间，且 $t=2$ 或 $4$。当 $t=4$ 时二者都是一维 $K$-空间，立即互为标量倍。设 $t=2$，取 $X$ 的 $K$-基 $x,y$，令 $\nu=y/x\notin K$。则 $\nu\in Q(X)\subseteq Q(Z)$，故存在 $0\ne z\in Z$ 使 $z\nu\in Z$。由于 $Z$ 是 $K$-空间，$z(K+K\nu)\subseteq Z$；$1,\nu$ 的 $K$-独立性使左边的 $K$-维数为二，故 $Z=z(K+K\nu)=(z/x)X$。

若 $d_X(\mu)=3$，则 $d_Z(\mu)\ge3$。引理 39.3 排除了 $t=2,4$。同时 $d_Z(\mu)=4$ 不可能：那会使 $Z$ 成为 $K$-空间，要求 $t\mid4$，而此处 $t=3$ 或 $t\ge5$。所以 $d_Z(\mu)=3$。

当 $t\ge5$ 时，引理 39.3 给出

$$
 X=x\langle1,\mu,\mu^2,\mu^3\rangle_F,qquad
 Z=z\langle1,\mu,\mu^2,\mu^3\rangle_F,
$$
故 $Z=(z/x)X$。当 $t=3$ 时，引理 39.3 给出

$$
 X=x(K+Fa),qquad Z=z(K+Fb),qquad a,b\notin K.
$$
由 (39.4) 可分别缩放两端并保持 (39.19)，得到 $Q(K+Fa)\subseteq Q(K+Fb)$。引理 39.4 应用于 $a$ 及 $a+\kappa_0$（这两个元素都属于 $Q(K+Fa)$），得到 $K+Fb=\lambda(K+Fa)$，从而 $Z=(z\lambda/x)X$。所有情形均已覆盖。最后使用 (39.4) 得到逐标签等式 $d_Z=d_X$。证毕。

**边界 39.5（环境次数四、五以及稳定子）。** 若 $[D:F]=4$，四维窗口只能是 $D$ 本身，故所有四维窗口相同。若 $[D:F]=5$，任意四维窗口 $W$ 与 $rW$ 的交维至少为三；对 $r\notin F$，有 $F(r)=D$，而交维四会使 $W$ 成为 $D$-空间，矛盾。因此交维三，且引理 39.3 对任意 $\mu\notin F$ 给出

$$
 W=w\langle1,\mu,\mu^2,\mu^3\rangle_F.
\tag{39.20}
$$
所以次数五中全部四维窗口互为标量倍。若 $E(W)\ne F$，(39.3) 给出 $[E(W):F]\in\{2,4\}$。一般地，$E(W)$ 也保持 $W\cap rW$，故其次数同时整除四维窗口和交维；交维恰三时由 $\gcd(4,3)=1$ 得 $E(W)=F$。在更高环境次数中，非平凡稳定子可能与交维二同时出现，但不影响定理 39.2；交维四的稳定子分支已在定理的第一种情形中处理。

**反例 39.6（纯支持包含的最小环境边界）。** 仅知道一端具有三次子域加一条方向的形状，并把 $Q(X)\subseteq Q(Z)$ 作为唯一比较，不能推出标量等价。取

$$
 F=\mathbb Q,qquad D=\mathbb Q(\alpha),\quad \alpha^6=2,qquad K=\mathbb Q(\alpha^2),
$$

由 $T^6-2$ 及 $T^3-2$ 的 Eisenstein 判别法，$[D:F]=6$、$[K:F]=3$。令

$$
 X=K+\mathbb Q\alpha=\langle1,\alpha,\alpha^2,\alpha^4\rangle_{\mathbb Q},qquad
 Z=\langle1,\alpha,\alpha^2,\alpha^3\rangle_{\mathbb Q}.
\tag{39.21}
$$

对每个 $r\in D^\times$，维数公式给出
$\dim_F(X\cap rX),\dim_F(Z\cap rZ)\ge4+4-6=2$，所以

$$
 Q(X)=Q(Z)=D^\times.
\tag{39.22}
$$

但由 $1,\alpha,\ldots,\alpha^5$ 的 $F$-独立性和 $\alpha^6=2$，有

$$
\begin{array}{c|cc}
 r&d_X(r)&d_Z(r)\\
\hline
 \alpha&2&3\\
 \alpha^2&3&2
\end{array}
\tag{39.23}
$$

具体地，$X\cap\alpha X=\operatorname{span}_F\{\alpha,\alpha^2\}$、$Z\cap\alpha Z=\operatorname{span}_F\{\alpha,\alpha^2,\alpha^3\}$，而 $X\cap\alpha^2X=\operatorname{span}_F\{1,\alpha^2,\alpha^4\}$、$Z\cap\alpha^2Z=\operatorname{span}_F\{\alpha^2,\alpha^3\}$。次数小于四时不存在四维窗口；环境次数四、五已由边界 39.5 排除，故次数六是这种纯支持失败的最小环境次数。

Napolitano–Polverino–Santonastaso–Zullo，[*Classifications and constructions of minimum size linear sets*，arXiv:2201.02003v1，Proposition 6.3](https://arxiv.org/html/2201.02003v1)，给出一般域版本的临界对分类：若 $T=\langle1,\mu\rangle_F$、$\mu\in L\setminus F$ 在 $F$ 上代数、$k=\dim_F S$、$k+2\le [L:F]$ 且 $\dim_F\langle ST\rangle_F=k+1$，令 $K=F(\mu)$、$t=[K:F]$，则 $t>k$ 时 $S$ 是 $\mu$ 的 $k$ 项幂链标量倍；$t\le k-1$ 时写 $k=t\ell+m$、$0<m<t$，有 $S=\bar S\oplus b\langle1,\mu,\ldots,\mu^{m-1}\rangle_F$，其中 $\bar S$ 是 $K$-空间且与 $bK$ 直和。本节的引理 39.3 直接证明所需四维特例，并与该命题的两种形状相合；本卷的分式支持引理及逐原标签拼接是该引用之外的应用推导。该引用不承担本定理的全球优先权，也不把特征零环境改成有限域或自动产生可计算恢复算法。

白话说，四维窗口如果被同一个原数平移后仍重合三维，窗口的形状已经很窄：要么是四项连续幂，要么是一个完整三次子域再加一条底域方向。前一种形状两个窗口只有整体缩放的差别。后一种形状里，第一个窗口的两条原商标签被第二个窗口支持，就把第二个附加方向写成一个分式；如果分母真的含有附加方向，那么第二条标签会迫使这个分式中的新量满足二次关系，倒数重新变成同一条仿射方向，仍然只剩整体缩放。若只看“有没有某个商”，而不看每个标签的交维大小，六次扩张中的两个四维窗口可以拥有完全相同的支持，却在 $\alpha$ 与 $\alpha^2$ 处给出相反的交维大小；所以支持是入口，逐标签交维才是刚性所需的关系。

本定理的结论范围是同一有限扩张内的四维 $F$-窗口和原标签逐点支配。它不声称一般维数、非有限环境、有限查询算法、噪声稳定性、量子起源或 $\mathbb Z/\mathbb Q$、$H10(\mathbb Q)$ 的推论；反例只说明删去交维大小后会丢失刚性。

## 追加锚（本行以下为增补区）

## 40. 低交维区的七次刚性与八次正交双胞胎

**定义 40.1（非标量低交维）。** 对四维窗口 $W\le_F D$，只在非标量标签
$$
r\in D^\times\setminus F^\times
$$
上称 $d_W(r)$ 为非标量交维。这个排除不可省略：每个 $c\in F^\times$ 都满足 $cW=W$ 及 $d_W(c)=4$。称 $W$ 为低交维窗口，若
$$
d_W(r)\le2\qquad(r\in D^\times\setminus F^\times).
\tag{40.1}
$$

**引理 40.2（迹正交补的交维公式）。** 设 $[D:F]=n$，$W\le_F D$ 的维数为 $k$，并以非退化结合配对
$$
\langle x,y\rangle=\operatorname{Tr}_{D/F}(xy)
$$
定义 $U=W^\perp$。则
$$
\boxed{d_W(r)=2k-n+d_U(r)}
\qquad(r\in D^\times).
\tag{40.2}
$$

**证明。** 由 $(rW)^\perp=r^{-1}U$，以及
$$
d_U(r^{-1})=d_U(r),
$$
有
$$
\begin{aligned}
d_U(r^{-1})
&=\dim_F(U\cap r^{-1}U)\\
&=n-\dim_F(W+rW)\\
&=n-2k+d_W(r).
\end{aligned}
$$
整理即得 (40.2)。最后一个对称性由乘以 $r$ 在 $U\cap r^{-1}U$ 与 $rU\cap U$ 之间的同构给出。$\square$

**引理 40.3（七次环境中的三维低秩商刚性）。** 设 $[D:F]=7$，且 $F$ 为特征零域。若 $U,V\le_F D$ 都是三维空间，并满足
$$
d_U(r)\le1\quad(r\in D^\times\setminus F^\times),
\qquad Q(U)\subseteq Q(V),
\tag{40.3}
$$
则存在 $\gamma\in D^\times$ 使
$$
V=\gamma U.
\tag{40.4}
$$

**证明。** 先证
$$
6\le\dim_F(UV)\le7,
\tag{40.5}
$$
其中 $UV$ 是所有 $uv$ 的 $F$-张成。若 $\dim_F(UV)\le5$，可在 $(UV)^\perp$ 中取线性无关的 $p,q$。则 $pU,qU\subseteq V^\perp$，而 $\dim_FV^\perp=4$，故
$$
\dim_F(pU\cap qU)\ge3+3-4=2.
$$
非零交向量给出 $d_U(q/p)\ge2$，且 $q/p\notin F^\times$，矛盾。于是只剩下维数六或七。

设
$$
K=\ker(U\otimes_FV\longrightarrow D),\qquad
u\otimes v\longmapsto uv.
$$
若 $\dim_F(UV)=7$，则 $\dim_FK=2$。对每个平面 $H=\ker\ell\subset U$，取独立的 $u,v\in H$。由 $Q(U)\subseteq Q(V)$，存在独立的 $c,d\in V$ 使 $u/v=c/d$，从而
$$
0\ne u\otimes d-v\otimes c\in K\cap(H\otimes_FV).
\tag{40.6}
$$
因此每个收缩
$$
M(\ell):K\longrightarrow V,\qquad
k\longmapsto(\ell\otimes1)k
$$
都有非零核。取 $K$ 的基，把它们看作 $A,B:U^*\to V$。它们的秩至少为二，否则相应张量为零或可分解张量。又 $A\ell,B\ell$ 对每个 $\ell$ 线性相关。一个初等事实是：若两个线性映射 $A,B:E\to V$ 满足这一点且 $\operatorname{rank}A\ge2$，则 $B=cA$；取两个使 $Ax,Ay$ 独立的向量，再比较 $x,y,x+y$ 即得。于是 $A,B$ 对应的两个张量相关，和 $\dim K=2$ 矛盾。因此
$$
\dim_F(UV)=6,\qquad\dim_FK=3.
\tag{40.7}
$$

取 $K$ 的基，令 $M(x)$ 为其三个收缩列组成的 $3\times3$ 矩阵，$x\in U^*$。式 (40.6) 给出 $\det M(x)\equiv0$。其在 $F(x)$ 上的秩恰为二：秩至多一会使任意两列映射逐点相关，应用上面的初等事实后使 $K$ 维数至多一，或直接产生可分解张量。

该矩阵没有非零的常值右核；否则 $K$ 中有一个张量被所有收缩消掉。它也没有非零的常值左核。事实上，若 $V_0$ 是相应的二维子空间，则 $K\subseteq U\otimes V_0$，而
$$
\dim_F(UV_0)=6-\dim_FK=3.
$$
对独立的 $v,w\in V_0$，这迫使 $vU=wU$，从而 $d_U(w/v)=3$，再次矛盾。

因此 $\operatorname{adj}M$ 是非零秩一矩阵。把它在多项式唯一分解域中写成
$$
\operatorname{adj}M=h\,a(x)b(x)^{\mathsf T},
\tag{40.8}
$$
其中 $a,b$ 是本原齐次向量。常值的 $a$ 或 $b$ 会分别给出常值右核或左核；由于 $\operatorname{adj}M$ 的总次数为二，故 $a,b$ 都是一次向量，$h$ 为常数。写 $a(x)=Lx$。矩阵 $L$ 不能有秩一：否则有常值右核；若秩二，经基变换可写成 $a(x)=(x_1,x_2,0)^{\mathsf T}$，而
$$
x_1\operatorname{col}_1(M)+x_2\operatorname{col}_2(M)=0
$$
会使第一或第二个核张量为零或可分解。故 $L$ 可逆，再作基变换得到
$$
M(x)x=0.
\tag{40.9}
$$

设相应的 $U$ 基为 $u_1,u_2,u_3$。比较 (40.9) 的二次系数，可把 $K$ 的一组基写成
$$
\begin{aligned}
k_1&=-u_2\otimes p-u_3\otimes q,\\
k_2&=u_1\otimes p-u_3\otimes s,\\
k_3&=u_1\otimes q+u_2\otimes s,
\end{aligned}
\qquad p,q,s\in V.
\tag{40.10}
$$
其乘积为零，所以
$$
u_1p=u_3s,\qquad u_1q=-u_2s.
$$
必有 $s\ne0$，否则 $p=q=0$。于是
$$
p=\frac{s}{u_1}u_3,\qquad
q=-\frac{s}{u_1}u_2,
$$
且 $s=(s/u_1)u_1$。故 $V$ 包含三维空间 $(s/u_1)U$，维数相同即得 (40.4)。$\square$

**定理 40.4（低交维问题的四至七次边界）。** 设 $X,Z\le_F D$ 都是四维窗口，满足逐原标签支配
$$
d_X(r)\le d_Z(r)\qquad(r\in D^\times)
\tag{40.11}
$$
及低交维条件 (40.1)。则在 $[D:F]\le7$ 时存在 $\gamma\in D^\times$ 使
$$
Z=\gamma X.
\tag{40.12}
$$

**证明。** 次数四时四维窗口只能是 $D$ 本身。次数五时，两个四维窗口的迹正交补都是直线，因而互为标量倍；低交维窗口本身也不存在，因为维数公式给出每个非标量交维至少三。

次数六时，令 $U=X^\perp$，则 $\dim_FU=2$。取独立的 $u,v\in U$，令 $r=u/v\notin F^\times$。由 $u\in U\cap rU$ 及 (40.2)，
$$
d_X(r)=2+d_U(r)\ge3,
$$
与 (40.1) 矛盾。因此低交维分支为空。

次数七时，令 $U=X^\perp$、$V=Z^\perp$。由 (40.2) 及 $d_U(r)=d_U(r^{-1})$，
$$
d_X(r)=1+d_U(r),\qquad d_Z(r)=1+d_V(r).
\tag{40.13}
$$
于是 $d_U\le d_V$，低交维给出 $d_U(r)\le1$；同时 $Q(U)\subseteq Q(V)$。引理 40.3 得 $V=\gamma U$，取迹正交补即得 $Z=\gamma^{-1}X$。$\square$

**定理 40.5（八次扩张的最小正交双胞胎反例）。** 令
$$
F=\mathbb Q,\qquad D=\mathbb Q(\alpha),\qquad \alpha^8=2,
$$
并定义
$$
X=\langle1,\alpha,\alpha^3,\alpha^4\rangle_{\mathbb Q},
\qquad
Z=\langle\alpha,\alpha^2,\alpha^3,\alpha^6\rangle_{\mathbb Q}.
\tag{40.14}
$$
则
$$
d_X(r)=d_Z(r)\le2\quad(r\in D^\times\setminus\mathbb Q^\times),
\qquad
Z\ne\gamma X\quad(\gamma\in D^\times).
\tag{40.15}
$$
因此八次是 corrected low-overlap 问题出现反例的最小环境次数。

**证明。** $T^8-2$ 的 Eisenstein 判别给出 $1,\alpha,\ldots,\alpha^7$ 的有理基。记
$$
S=\{0,1,3,4\},\qquad S^c=\{2,5,6,7\}.
$$
由
$$
\operatorname{Tr}_{D/\mathbb Q}(\alpha^j)=0
\quad(1\le j\le7)
$$
及 $\operatorname{Tr}(\alpha^8)\ne0$，可直接核对
$$
Z=X^\perp.
\tag{40.16}
$$
将 (40.2) 用于 $n=8,k=4$，得到
$$
d_X(r)=d_Z(r)\qquad(r\in D^\times).
\tag{40.17}
$$

写 $r=\sum_{i=0}^7c_i\alpha^i$。把乘法后投影到
$\operatorname{span}_{\mathbb Q}\{\alpha^2,\alpha^5,\alpha^6,\alpha^7\}$，相对于 $X$ 的基 $(1,\alpha,\alpha^3,\alpha^4)$，矩阵为
$$
M_r=
\begin{pmatrix}
c_2&c_1&2c_7&2c_6\\
c_5&c_4&c_2&c_1\\
c_6&c_5&c_3&c_2\\
c_7&c_6&c_4&c_3
\end{pmatrix},
\tag{40.18}
$$
故 $d_X(r)=4-\operatorname{rank}M_r$。若 $d_X(r)\ge3$，所有二阶子式均为零。由行 $1,3$、列 $1,4$ 的子式得
$$
c_2^2=2c_6^2,
$$
故 $c_2=c_6=0$。此时行 $1,4$、列 $1,3$ 的子式给 $c_7=0$，行 $1,2$、列 $2,4$ 的子式给 $c_1=0$；再由行 $2,3$、列 $1,2$ 的子式得 $c_5=0$，由行 $2,4$、列 $2,3$ 及行 $3,4$、列 $3,4$ 依次得 $c_4=c_3=0$。所以 $r\in\mathbb Q^\times$，证明非标量时 $d_X(r)\le2$。结合 (40.17) 即得第一部分。

若 $\gamma X=Z$，因 $1\in X$，有
$$
\gamma=a\alpha+b\alpha^2+c\alpha^3+d\alpha^6.
$$
条件 $\alpha\gamma\in Z$ 迫使 $c=d=0$；再由 $\alpha^3\gamma\in Z$ 迫使 $a=b=0$，与 $\gamma\ne0$ 矛盾。故 $Z$ 与 $X$ 不在同一标量轨道。$\square$

**边界与范围。** 对次数六和七，维数公式还给出所有四维窗口的商支持都是 $D^\times$，所以只看 $Q(W)$ 在这些次数中完全没有区分力。七次刚性使用了完整的逐标签支配和低交维，而不是纯支持包含。八次反例的秩矩阵是本卷本轮的纸面构造；迹正交补和非退化配对沿用前卷工具。这里没有使用 Lean、CAS、数值实验或有限域枚举，不作全球优先权声明，也不把该结果外推为量子力学、$\mathbb Z\subset\mathbb Q$ 的丢番图定义或 Hilbert 第十问题结论。

白话说：把“高交叠”排除后，四到六次其实没有可用的低交维窗口，七次仍能用正交补把问题降成三个方向的商关系，并证明两个窗口只能整体缩放。到了八次，四维空间和它的迹正交补各自只在非标量标签上重合至多两维，却对所有标签给出同一份交维表；这两个空间又不是整体乘数的关系。因此低交维本身不是最后的刚性来源，八维中的正交对偶是必须额外打破的隐藏关系。

## 追加锚（本行以下为增补区）

## 41. 八次完整商纤维的不可约方程与两种嵌入拟阵

**定义 41.1（原支持、分裂坐标与既有前件）。** 固定正实根 $\alpha=2^{1/8}$、原域 $D=\mathbb Q(\alpha)$，以及式 (40.14) 的 $X,Z$。对四维有理窗口 $W\le_{\mathbb Q}D$，记

$$
Q_W=\{u/v:u,v\in W,\ v\ne0\},\qquad
\mathscr F_Q(X)=\{W:\dim_{\mathbb Q}W=4,\ Q_W=Q_X\}.
\tag{41.1}
$$

$Q_W$ 包含零；等式逐个保留原 $D$ 元素。取 $\zeta=e^{\pi i/4}$、$K=D(\zeta)$ 及代数闭包 $k\supseteq K$，将嵌入编号为

$$
\sigma_i(\alpha)=\alpha\zeta^i,\qquad i\in E=\mathbb Z/8\mathbb Z.
$$

选 $W$ 的有理基 $w_1,\ldots,w_4$，定义

$$
B_W=(\sigma_i(w_j))_{i\in E,\,1\le j\le4},\quad
p_I(W)=\det(B_W)_I\quad(|I|=4),\quad
\mathcal N(W)=\{I\subset E:|I|=4,\ p_I(W)=0\}.
\tag{41.2}
$$

行按 $0,\ldots,7$ 排序。$\mathcal N(W)$ 是固定嵌入标签的行拟阵非基集合，不因更换有理基而变。令

$$
\begin{aligned}
\mathcal A&=\{\{t,t+1,t+2,t+5\}:t\in E\},\\
\mathcal C&=\{\{t,t+1,t+3,t+4\}:t\in E\},\\
\mathcal B&=\{\{0,2,4,6\},\{1,3,5,7\}\}.
\end{aligned}
\tag{41.3}
$$

这些集合中的加法均模八；$\mathcal C=\{I^c:I\in\mathcal A\}$，$\mathcal B$ 在取补下不变。

这里沿用的扩张均为特征零有限域扩张；定理 40.4 也在此前件下使用。式 (40.2) 的迹对偶恒等式是 §34 式 (34.7) 及其所引来源的重述。取前卷 [《原有向面积与三重返回》命题 24.2](AURIC_R5_022_ORIENTED_AREA_AND_TERNARY_RETURN.md) 的 $\theta=\alpha$，则其 $U=X$、$\alpha V=Z$；成对反例及其三重分离均是既有输入。以下要限制的是同一原支持的全部窗口，不重新断言这对窗口的发现。

**定理 41.2（完整原商支持只容许两种分裂非基集合）。** 对每个 $Y\in\mathscr F_Q(X)$，都有

$$
\boxed{\quad
\mathcal N(Y)=\mathcal A\cup\mathcal B
\quad\text{或}\quad
\mathcal N(Y)=\mathcal C\cup\mathcal B.
\quad}
\tag{41.4}
$$

两种集合分别就是 $\mathcal N(X)$ 与 $\mathcal N(Z)$。特别地，完整逐原标签交维函数满足 $d_Y=d_X$ 时，结论仍成立。

证明。对分裂坐标 $q=(q_0,\ldots,q_7)$，置

$$
P_W(q)=\det[\,B_W\mid\operatorname{diag}(q)B_W\,].
\tag{41.5}
$$

这是次数四、每个变量次数至多一的多项式。按右侧四列作 Laplace 展开，得到经典互补子式公式

$$
P_W(q)=\sum_{|I|=4}\epsilon_Ip_I(W)p_{I^c}(W)\prod_{i\in I}q_i,
\qquad \epsilon_I\in\{1,-1\}.
\tag{41.6}
$$

该公式只作为行列式展开的中间工具。对原 $r\in D^\times$，可分分裂及扩底保秩给出

$$
P_W((\sigma_i(r))_i)=0
\quad\Longleftrightarrow\quad d_W(r)>0.
\tag{41.7}
$$

确实两组列的张成分别是 $W\otimes k$ 与 $rW\otimes k$，均为四维；八列相关恰好表示它们有非零交集。

先计算 $X$ 的系数零集。其嵌入行是

$$
(1,t_i,t_i^3,t_i^4),\qquad t_i=\alpha\zeta^i.
$$

对四个不同的指标 $I$，行子式为零当且仅当存在非零的 $c_0+c_1T+c_3T^3+c_4T^4$ 在这四个 $t_i$ 上消失。此时 $c_4\ne0$，否则一个次数至多三的非零多项式有四个根。因此该多项式是 $c_4\prod_{i\in I}(T-t_i)$，缺少二次项恰好等价于

$$
p_I(X)=0\quad\Longleftrightarrow\quad
\sum_{i<j,\ i,j\in I}\zeta^{i+j}=0.
\tag{41.8}
$$

为完整核对 (41.8)，将四点沿八边形的相邻间隔写成四个正整数，其和为八。按循环排列归并，恰有下表十类。平移 $t$ 只给右列乘以非零因子 $\zeta^{2t}$。

| 四点代表 | 平移轨道大小 | $\sum_{i<j}\zeta^{i+j}$ |
| --- | --- | --- |
| $\{0,1,2,3\}$ | $8$ | $-1+\zeta^2+2\zeta^3$ |
| $\{0,1,2,4\}$ | $8$ | $-1+\zeta^3$ |
| $\{0,1,2,6\}$ | $8$ | $1+\zeta$ |
| $\{0,1,3,4\}$ | $8$ | $-2$ |
| $\{0,1,2,5\}$ | $8$ | $0$ |
| $\{0,1,4,5\}$ | $4$ | $-1-\zeta^2$ |
| $\{0,1,3,5\}$ | $8$ | $\zeta^3-\zeta^2$ |
| $\{0,1,3,6\}$ | $8$ | $-1+2\zeta-\zeta^2$ |
| $\{0,1,4,6\}$ | $8$ | $-1-\zeta^3$ |
| $\{0,2,4,6\}$ | $2$ | $0$ |

完整性也可由间隔的五种无序形状核对：$(1,1,1,5)$ 给一类，$(1,1,2,4)$ 给三类，$(1,1,3,3)$ 给两类，$(1,2,2,3)$ 给三类，$(2,2,2,2)$ 给一类。表中轨道大小合计七十，且 $1,\zeta,\zeta^2,\zeta^3$ 在 $\mathbb Q$ 上独立。故

$$
\mathcal N(X)=\mathcal A\cup\mathcal B,
\qquad
\#\{I:[q_I]P_X=0\}=8+8+2=18,
\tag{41.9}
$$

其中 $q_I=\prod_{i\in I}q_i$。其余五十二个系数均非零。

接着证明 $P_X$ 在 $k[q_0,\ldots,q_7]$ 中不可约。若 $P_X=FG$ 为两个非常数因子的乘积，则多重次数相加使每个变量至多出现在一个因子中。因子也可取为齐次因子；否则比较最低与最高总次数便与乘积齐次矛盾。因此变量被分到两个不交非空集合 $H,H^c$，每个非零单项式 $q_I$ 都满足同一个条件 $|I\cap H|=\deg F$。

取 $i\in H$、$j\notin H$。其余六个指标有二十个三元子集 $T$。若每个 $T$ 都使 $T\cup\{i\}$、$T\cup\{j\}$ 至少一个对应零系数，就至少需要二十个不同的零四元组：两类四元组分别不含 $j$ 和不含 $i$，而每类内部由 $T$ 唯一确定。式 (41.9) 只有十八个零系数。因此存在 $T$ 使两个系数同时非零；这两个四元组的 $|I\cap H|$ 相差一，矛盾。故

$$
P_X\text{ 绝对不可约。}
\tag{41.10}
$$

现在把原支持相等传到同一多项式方程。记 $H_X=B_Xk^4$，在 $H_X\times H_X$ 的非空开集上考虑逐坐标商态射

$$
\phi(u,v)=(u_i/v_i)_{i\in E},\qquad \prod_i v_i\ne0.
\tag{41.11}
$$

有理系数的原点对在此开集中 Zariski 稠密，理由与式 (35.9) 相同：无限子域上的非零多项式不能在全部原坐标上消失，而原域非零分母的每个嵌入都非零。因此原 $Q_X$ 的嵌入像与 $\phi$ 的几何像具有同一闭包。

这个闭包的维数恰为七。取原点对 $(u,v)=(\alpha^3,\alpha)$，商为 $\alpha^2$。由幂基直接得到

$$
X\cap\alpha^2X=\mathbb Q\alpha^3.
\tag{41.12}
$$

在该点的微分是

$$
(h,k)\longmapsto\alpha^{-1}(h-\alpha^2k),
$$

其秩为 $\dim(X+\alpha^2X)=7$。特征零下的 Jacobian 秩与像维数判据给出像维数至少七；该像由 (41.5) 消去且 $P_X\ne0$，所以维数至多七。这是普通代数几何的维数工具，不把扩底后的点当作原商。结合 (41.10)，得到

$$
\overline{\sigma(Q_X)}^{\mathrm{Zar}}=V(P_X)\subseteq k^8.
\tag{41.13}
$$

若 $Q_Y=Q_X$，则 (41.7) 使 $P_Y$ 在这个闭包上消失。它不是零多项式：非零的 $P_X$ 不能在全部原 $D$ 坐标上消失，故存在非零原 $r$ 不属于 $Q_X=Q_Y$，再用 (41.7)。不可约性、零点定理及同为四次遂给出

$$
\boxed{P_Y=cP_X\quad(c\in k^\times).}
\tag{41.14}
$$

式 (41.14) 特别说明 $p_I(Y)p_{I^c}(Y)$ 只在 $\mathcal A\cup\mathcal C\cup\mathcal B$ 上为零，其余均非零。

还须使用同一原域的 Galois 约束，不能对十八个零乘积各自自由选择因子。由于 $\alpha$ 为实数且 $\zeta=(1+i)/\alpha^4$，有 $K=D(i)$ 及 $[K:\mathbb Q]=16$，从而 $[K:\mathbb Q(\zeta)]=4$。因此有固定 $\zeta$、发送 $\alpha\mapsto i\alpha$ 的自同构，它在 $E$ 上作平移二。将 $\zeta\mapsto\zeta^3$ 延拓到正规域 $K$ 的自同构，记其 $\alpha\mapsto\alpha\zeta^b$；由 $\alpha^4=\sqrt2$ 及 $\sqrt2\mapsto-\sqrt2$ 可知 $b$ 为奇数。它在嵌入指标上作

$$
i\longmapsto3i+b.
$$

乘三将 $\{0,1,2,5\}$ 送到其平移六，故这个仿射作用与平移二共同在 $\mathcal A$ 上传递，也在补集轨道 $\mathcal C$ 上传递，并交换 $\mathcal B$ 的两个成员。

$Y$ 有有理基，域自同构保持其行子式的零与非零，所以 $\mathcal N(Y)$ 在上述作用下不变。式 (41.14) 因而迫使两个交替四元组都在 $\mathcal N(Y)$，并迫使 $\mathcal A$、$\mathcal C$ 至少整组出现一组，除此之外没有非基。

两组不能同时出现。否则 $\{0,1,2,5\}$ 和 $\{1,2,4,5\}$ 都为非基，而 $\{1,2,3,5\}$ 与 $\{0,1,2,4\}$ 都为基，后两者的互补系数由表确为非零。第一份基说明行 $1,2,5$ 独立；前两份非基便分别迫使行 $0$ 和行 $4$ 落入这三个行的张成。因此 $\{0,1,2,4\}$ 也相关，矛盾。这证明 (41.4)。

最后，迹配对在分裂坐标中是 $\sum_i x_iy_i$；式 (40.16) 给出 $Z=X^\perp$。标准正交补的互补基对应遂给出 $\mathcal N(Z)=\{I:I^c\in\mathcal N(X)\}=\mathcal C\cup\mathcal B$。若 $d_Y=d_X$，则正交维的正支持相同，直接得到 $Q_Y=Q_X$，故也适用。$\square$

**定理 41.2 的适用范围。** 式 (41.4) 只限制分裂行拟阵，式 (41.14) 还保留全部互补子式乘积。要证明完整纤维恰为两个原标量轨道，仍须证明：满足这些固定乘积及同一 Galois 下降条件的所有表示，都由 $X$ 或 $Z$ 乘原 $D^\times$ 元素得到。相同拟阵不自动等于相同射影表示，分裂后的对角等价也不自动给出已经取得的原域乘数；这两条桥在此不作假定。

行拟阵、互补子式、射影表示与正交对偶采用既有的线性拟阵和 Grassmann 几何含义。相关文献接口沿用前卷 §18 所引 Ghorpade–Patil–Pillai，[*Decomposable Subspaces, Linear Sections of Grassmann Varieties, and Higher Weights of Grassmann Codes*，arXiv:0710.5161](https://arxiv.org/abs/0710.5161)，§§1–2；原商的稠密桥沿用本卷 §35。这里的仓内新增推导是特定八次窗口的十八个零互补系数、不可约方程 (41.10)–(41.14)，以及同一原支持的全部窗口只能采用两种非基集合的结论 (41.4)，不将一般行列式、稠密性或对偶工具另列为新定理。

白话说，这张二元关系表至少锁住了一张完整四次方程。方程的十八处零项不能被候选窗口随意拆开：原域的共轭关系要求它们成组出现，线性相容性又排除两组一起出现。于是所有候选只剩两种嵌入依赖图，恰好对应原窗口和其正交双胞胎。剩下要问的是，同一张依赖图和同一份系数是否还能有不同的实现；本定理尚未把这个表示问题等同于两个标量轨道。

## 追加锚（本行以下为增补区）

## 42. 八次完整原商支持纤维恰为两个原标量轨道

**定义 42.1（共同标签下的表示与乘数空间）。** 沿用定义 41.1 的原域 $D$、窗口 $X,Z$、分裂域 $K$ 和全部八个嵌入。对任意非零有理子空间 $W\le D$，$Q_W$ 仍由式 (41.1) 定义，不预设 $W$ 为四维。对同维子空间 $W,Y\le D$，定义原乘数空间

$$
T(W,Y)=\{c\in D:cW\subseteq Y\}
=\ker\bigl(D\longrightarrow\operatorname{Hom}_{\mathbb Q}(W,D/Y)\bigr),
\tag{42.1}
$$

其中 $c$ 对应的映射为 $w\mapsto cw+Y$。分裂嵌入矩阵的表示等价指更换其列基并独立缩放每一行；两份矩阵始终使用同一行标签。

**定理 42.2（全部原子空间的完整纤维分类）。** 对原 $D$ 中每个非零有理子空间 $Y$，下列条件等价：

$$
\begin{aligned}
&Q_Y=Q_X;\\
&d_Y(r)=d_X(r)\qquad\text{对每个原 }r\in D^\times;\\
&Y=\gamma X\quad\text{或}\quad Y=\gamma Z
\qquad\text{对某个原 }\gamma\in D^\times.
\end{aligned}
\tag{42.2}
$$

这两个原标量轨道彼此不同。因此完整商支持纤维与完整交维函数纤维均恰好由这两个轨道组成。进一步，在 $Q_Y=Q_X$ 的条件下，单个共同见证读数满足

$$
\begin{aligned}
J_Y(\alpha,\alpha^3)=1&\quad\Longleftrightarrow\quad Y=\gamma X,\\
J_Y(\alpha,\alpha^3)=0&\quad\Longleftrightarrow\quad Y=\gamma Z,
\end{aligned}
\qquad\gamma\in D^\times.
\tag{42.3}
$$

证明。先由支持确定维数。式 (41.13) 给出原 $Q_X$ 的嵌入闭包维数为七，且 $Q_X\ne D$。若 $m=\dim_{\mathbb Q}Y\le3$，其逐坐标商参数 $[u:v]$ 共有至多 $2m-1\le5$ 个独立参数：在分母的任一非零基坐标片上，公共缩放可将该坐标置为一。因此 $Q_Y$ 的几何闭包维数至多五，不能等于 $Q_X$ 的闭包。若 $m\ge5$，则对每个 $r\in D^\times$ 都有

$$
\dim(Y\cap rY)\ge2m-8>0,
$$

所以 $Q_Y=D$，也不可能。故 $Q_Y=Q_X$ 强制 $m=4$。

现在应用定理 41.2。其第一种非基集合 $\mathcal A\cup\mathcal B$ 是经典拟阵 $P_8$ 的一个固定标签版本。精确对应为

$$
\begin{array}{c|rrrrrrrr}
\text{原嵌入标签}&0&1&2&3&4&5&6&7\\\hline
P_8\text{ 标签}&1&2&8&6&4&3&5&7.
\end{array}
\tag{42.4}
$$

在此对应下，十个非基依次成为

$$
\begin{gathered}
1238,\ 2568,\ 4678,\ 1346,\ 2345,\\
3578,\ 1567,\ 1247,\ 1458,\ 2367,
\end{gathered}
\tag{42.5}
$$

其中 $1238$ 表示 $\{1,2,3,8\}$。这正是 Pendavingh–van Zwam，[*Confinement of matroid representations to subsets of partial fields*，arXiv:0806.4487v2，Theorem 4.18、式 (81)、Lemma 5.2](https://arxiv.org/html/0806.4487v2) 所用 $P_8$ 的十个非基。其标准表示为

$$
[\,I_4\mid A_8\,],\qquad
A_8=\begin{pmatrix}
0&1&1&2\\
1&0&1&1\\
1&1&0&1\\
2&1&1&0
\end{pmatrix}.
\tag{42.6}
$$

这里直接消费该成熟结果的特征零有标签表示唯一性，不将 $P_8$ 或其唯一性列作新定理。为明确所用的等价关系，原文 Theorem 4.18 的固定基和树归一化把任意表示化为

$$
\left[\,I_4\ \middle|\
\begin{matrix}
0&1&1&x\\
1&0&1&1\\
y&z&0&1\\
u&v&1&0
\end{matrix}\right].
$$

其中五个变量均非零；非基 $1458,2367$ 给出 $y=v=1$，非基 $4678,1567,2568,3578$ 给出原文式 (57)–(60)：

$$
2-x=0,\qquad z+1-zu=0,\qquad
u+x(1-zu)=0,\qquad u+x(1-u)=0.
$$

因此 $x=u=2$、$z=1$，全部归一化参数唯一，恰得 (42.6)。这些变换只使用行基变换与各列的非零缩放；转置回八行嵌入矩阵，便是列基变换与八行的独立缩放。式 (42.4) 对两份配置使用同一个置换，比较后消去该置换，故没有改变任何原域标签。

若 $\mathcal N(Y)=\mathcal N(X)$，该唯一性于是给出

$$
Y\otimes K=t(X\otimes K)
\quad\text{对某个 }t\in(K^\times)^8
\simeq(D\otimes K)^\times,
\tag{42.7}
$$

乘法在分裂坐标中逐坐标进行。若 $\mathcal N(Y)=\mathcal N(Z)$，取标准点积的正交补后，两份配置的非基集合都成为 $\mathcal N(X)$。应用同一唯一性，再取正交补，得到 (42.7) 中以 $Z$ 替换 $X$ 的结论；这是因为 $(tH)^\perp=t^{-1}H^\perp$。

最后将这个分裂乘数返回原域。对 $W=X$ 或 $Z$，式 (42.1) 是原域上的有限线性方程组，扩域保核给出

$$
T(W,Y)\otimes_{\mathbb Q}K
=\{c\in D\otimes K:c(W\otimes K)\subseteq Y\otimes K\}.
\tag{42.8}
$$

这是 §26 式 (26.9)–(26.10) 使用的同一核扩底事实。式 (42.7) 的非零 $t$ 使右边非零，因此原 $T(W,Y)$ 也非零。选 $0\ne\gamma\in T(W,Y)$；由于 $D$ 为域，乘 $\gamma$ 单射，$\gamma W\subseteq Y$ 又与 $Y$ 同为四维，故 $Y=\gamma W$。至此证明支持相等推出式 (42.2) 的第三项，未将分裂后的任意等价直接冒作原域等价。

反向，原域乘法交换，故整体乘 $\gamma\ne0$ 保持每一个原标签下的二重、三重交维。式 (40.17) 已给出 $d_Z=d_X$，所以第三项推出第二项。交维的正支持恰为非零原商，故第二项推出第一项。两轨道不同由定理 40.5；式 (42.3) 则消费前卷命题 24.2 的已知读数 $J_X(\alpha,\alpha^3)=1$、$J_Z(\alpha,\alpha^3)=0$，再用整体标量不变性。$\square$

**定理 42.2 的适用范围。** 本条补足定理 41.2 适用范围中保留的表示与原域乘数步骤；不修改 (41.4) 或此前任何条目的前件。$P_8$ 的归一化唯一性和有限线性方程组的扩底保核均为既有工具，新增结论是将它们与 (41.4) 连接，得到这个实际八次域内的全部支持纤维及交维纤维分类。结论量化原 $D$ 的全部子空间和全部精确原标签，不要求竞争窗口由幂基子集张成；也不提供有限查询、噪声或任意八次域的同式分类。

白话说，在这个八次域里，完整二元关系表确实只藏着两个整体形状：原窗口和它的正交双胞胎，第三种形状已被排除。两种依赖图各自的实现由经典 $P_8$ 刚性锁住，而一个原域线性方程组把分裂表示收回同一来源中的实际乘数。再问一次“三份关系是否共享同一个非零见证”，就能在这两个形状之间作出选择。

## 追加锚（本行以下为增补区）

## 43. 任意实际八次域的四平面原商支持纤维

**定义 43.1（固定原域、四平面与迹对偶）。** 固定特征零域 $F$ 及同一个实际域扩张 $D/F$，$[D:F]=8$。本节的窗口与竞争窗口始终都是四维 $F$-子空间 $W,Y\le_F D$，并定义

$$
\begin{aligned}
Q_W&=\{u/v:u,v\in W,\ v\ne0\},\\
d_W(r)&=\dim_F(W\cap rW)\qquad(r\in D^\times),\\
E_W&=\{c\in D:cW\subseteq W\},\\
W^\perp&=\{z\in D:\operatorname{Tr}_{D/F}(zw)=0\text{ 对每个 }w\in W\}.
\end{aligned}
\tag{43.1}
$$

$Q_W$ 包含零，$d_W$ 仅在非零原标签上使用。乘除、标签与整体标量均属于这个原 $D$；不允许域自同构重标标签。可分性使迹配对非退化，故 $W^\perp$ 也是四平面。

**定理 43.2（一般八次域的支持、交维与至多两个标量轨道）。** 对定义 43.1 中任意 $F,D,W,Y$，有

$$
\boxed{\quad
Q_Y=Q_W
\quad\Longleftrightarrow\quad
\bigl[\ \forall r\in D^\times,\ d_Y(r)=d_W(r)\ \bigr]
\quad\Longleftrightarrow\quad
\bigl[\ Y=\gamma W\ \text{或}\ Y=\gamma W^\perp
\text{，某个 }\gamma\in D^\times\ \bigr].
\quad}
\tag{43.2}
$$

因而在四平面类内，完整原商支持纤维与完整原交维函数纤维相同，均至多包含两个原标量轨道；两轨道允许重合。进一步，若 $E_W\ne F$，则有更强的单侧结论

$$
Q_Y\subseteq Q_W\quad\Longrightarrow\quad
Y=\gamma W\quad\text{对某个 }\gamma\in D^\times.
\tag{43.3}
$$

这里没有预设竞争窗口 $Y$ 对 $E_W$ 线性。因此非平凡乘子域分支的相等支持纤维恰有一个标量轨道。

证明。使用定理 26.2 的实际域结论：$E_W$ 是中间域，$[E_W:F]\mid4$，最小正交维等于 $[E_W:F]$；在 $E_W=F$ 时，其证明中的分裂行拟阵连通性及严格秩界 (26.16) 也直接适用。迹对偶的交维恒等式直接使用 (34.7)、引理 40.2。以下补足一般八次域的支持与表示桥梁。

（一）非平凡乘子域，以及竞争窗口的自动线性性。设 $E=E_W$，$e=[E:F]>1$，则 $e=2$ 或 $4$。对两个窗口各自整体缩放不会改变各自的商支持或乘子域。

若 $e=4$，可将 $W$ 归一化为 $E$，并独立将 $Y$ 归一化为包含 $1$。于是 $Y\subseteq Q_Y\subseteq Q_W=E$；两边的 $F$-维数都是四，所以 $Y=E$，还原缩放即得 (43.3)。

若 $e=2$，将 $W$ 归一化为 $E+Ez$，并仍将 $Y$ 归一化为包含 $1$。由 $[D:E]=4$，$z$ 在 $E$ 上的次数只能为二或四；若为二，则 $W=E(z)$，其乘子域为这个四次于 $F$ 的域，与 $E_W=E$ 矛盾。因此 $D=E(z)$，且 $1,z,z^2,z^3$ 是 $E$-基。写成

$$
z^4=b_0+b_1z+b_2z^2+b_3z^3,\qquad
 t=t_0+t_1z+t_2z^2+t_3z^3,\qquad b_i,t_i\in E.
$$

在 $W$ 的基 $1,z$ 及 $D/W$ 的基 $z^2,z^3$ 下，乘以 $t$ 再投影到 $D/W$ 的矩阵为

$$
\begin{pmatrix}
t_2&t_1+b_2t_3\\
t_3&t_2+b_3t_3
\end{pmatrix}.
$$

所以对非零原 $t$，

$$
t\in Q_W\quad\Longleftrightarrow\quad q(t)=0,
\qquad
q(t)=t_2^2+b_3t_2t_3-t_1t_3-b_2t_3^2.
\tag{43.4}
$$

这是 $D$ 上的 $E$-值二次型，其根基恰为 $E\cdot1$：在 $t_1,t_2,t_3$ 上的对称矩阵是

$$
\begin{pmatrix}
0&0&-1/2\\
0&1&b_3/2\\
-1/2&b_3/2&-b_2
\end{pmatrix},\qquad \det=-1/4.
$$

模去根基后得到三维非退化二次空间。若其中一个子空间全迷向，则它包含于自己的正交补，故维数至多一；因此原二次空间的全迷向 $E$-子空间维数至多二。

由 $1\in Y$ 及支持包含，对每个 $y\in Y$ 有 $q(y)=0$，其中 $y=0$ 时直接使用二次型的零值。令 $B_q(x,y)=(q(x+y)-q(x)-q(y))/2$；又因 $y+y'\in Y$，极化给出 $B_q(y,y')=0$。二次型的 $E$-齐次性及极化型的 $E$-双线性表明 $EY=\operatorname{span}_E Y$ 仍全迷向。因此

$$
4=\dim_F Y\le\dim_F(EY)=2\dim_E(EY)\le4,
\qquad Y=EY.
\tag{43.5}
$$

这证明了所需的自动 $E$-线性性，而不是将它加入前件。现在写 $Y=E+Ey$，$y\notin E$。因 $y\in Q_W$，存在 $a,b,c,d\in E$，使

$$
y=\frac{a+bz}{c+dz},\qquad c+dz\ne0.
$$

$y\notin E$ 迫使 $ad-bc\ne0$，故

$$
(c+dz)Y=\operatorname{span}_E\{c+dz,a+bz\}=E+Ez=W.
$$

还原归一化便得 (43.3)，没有用到 $Y$ 的任何额外乘子假设。

（二）平凡乘子域的归一化矩阵。以下设 $E_W=F$。先找原 $a\in D^\times\setminus Q_W$。将 $D$ 看成八维仿射 $F$-空间，商映射

$$
\phi:W\times W\dashrightarrow D,\qquad (u,v)\longmapsto u/v
\tag{43.6}
$$

在分母范数非零处为有理映射。分母的每个非零基坐标片上，可以同时缩放分子、分母，将该坐标置为一，故其几何像闭包维数至多 $4+3=7$。这给出一个在 $F$ 上定义的真闭子集，包含全部原商；无限域 $F$ 的原坐标点在八维仿射空间中 Zariski 稠密。因此可取上述原 $a$。这一论证也说明并非先假定行列式非零。

记 $i_W:W\hookrightarrow D$、$\pi_W:D\to D/W$，并令 $M_t$ 为原乘法算子。取两端的 $F$-基，置

$$
A_W(t)=\pi_W M_t i_W,\qquad f_W(t)=\det A_W(t).
\tag{43.7}
$$

$f_W$ 是原八个线性坐标上的齐次四次多项式。对非零原 $t$，乘以 $t$ 把 $\ker A_W(t)=W\cap t^{-1}W$ 同构到 $W\cap tW$，从而

$$
\dim_F\ker A_W(t)=d_W(t),\qquad
f_W(t)=0\ \Longleftrightarrow\ t\in Q_W.
\tag{43.8}
$$

$t=0$ 时 $A_W(0)=0$ 的核维数为四，而 $W\cap0W=\{0\}$；不将这个核维数当作零标签的交维。由所选 $a$，$A_W(a)$ 可逆。定义原 $F$-线性算子

$$
N_W=i_W A_W(a)^{-1}\pi_W.
$$

因为 $\pi_W i_W=0$，且两端的嵌入、商映射分别单射、满射，有

$$
N_W^2=0,\qquad
\operatorname{im}N_W=\ker N_W=W,\qquad
\operatorname{rank}N_W=4.
\tag{43.9}
$$

取有限 Galois 正规闭包 $K/F$，固定分裂同构 $D\otimes_F K\simeq K^\Omega$，其中 $\Omega=\operatorname{Hom}_F(D,K)$、$|\Omega|=8$。以下两窗口使用同一套嵌入标签。以 $V$ 表示 $W_K$ 的 $8\times4$ 列基矩阵，以 $U$ 表示商映射的 $4\times8$ 矩阵；于是

$$
UV=0,\qquad A_0=U\operatorname{diag}(\sigma(a))V,\qquad
N=VA_0^{-1}U.
\tag{43.10}
$$

这里 $N$ 就是 $N_W$ 的分裂坐标矩阵。Sylvester 行列式恒等式给出

$$
\frac{f_W(a+x)}{f_W(a)}
=\det\bigl(I_4+A_0^{-1}U\operatorname{diag}(x)V\bigr)
=\det\bigl(I_8+N\operatorname{diag}(x)\bigr).
\tag{43.11}
$$

$x$ 在右边是八个独立的分裂坐标，左边经同一个可逆线性坐标变换理解。$G=\operatorname{Gal}(K/F)$ 在 $\Omega$ 上传递，这是原 $D$ 为域且 $D/F$ 可分的结果。$N_W$ 在原 $F$ 上定义，故

$$
N_{g\sigma,g\tau}=g(N_{\sigma,\tau})\qquad(g\in G).
\tag{43.12}
$$

因此其有向零模式与全部带标签子矩阵的秩均被该半线性作用保持。

（三）原支持到不可约四次方程。令 $M$ 为 $V$ 的行拟阵，秩函数为

$$
\rho(S)=\dim_K\operatorname{pr}_S W_K.
$$

$E_W=F$ 时，直接由 §26 的 (26.12)–(26.16)，$M$ 连通且

$$
2\rho(S)\ge |S|+1\qquad
(\varnothing\ne S\subsetneq\Omega).
\tag{43.13}
$$

这些结论控制整个分裂稳定子，不只控制原来逐个列出的乘数。这里使用的是同一原八次域的实际窗口，不另加拟阵一般位置假设。

先证 $N$ 为不可约矩阵，即其非零条目有向图强连通。由 (43.12)，$G$ 传递地置换其强连通分量。分量缩并图是有限有向无环图；它有汇点，而顶点传递性使每个顶点都是汇点，故没有边。若存在多个分量，$N$ 就在这些坐标块上分块对角，由 $\operatorname{im}N=W_K$ 可知 $W_K$ 也按这些块直和分解；于是 $M$ 不连通，矛盾。

现使用 Al Ahmadieh，[*The Fiber of the principal minor map*，arXiv:2309.00806v2，Lemma 5.1](https://arxiv.org/html/2309.00806v2)：在任意域上，矩阵 $N$ 不可约当且仅当

$$
g(y)=\det\bigl(\operatorname{diag}(y)+N\bigr)
$$

不可约。非零条目图在扩域后不变，故将该引理应用于代数闭包可知 $g$ 绝对不可约。置 $h(x)=\det(I_8+N\operatorname{diag}(x))$。有

$$
g(y)=\Bigl(\prod_{\sigma\in\Omega}y_\sigma\Bigr)
 h\bigl((y_\sigma^{-1})_\sigma\bigr).
\tag{43.14}
$$

变量取逆是 Laurent 多项式环的自同构，$g$ 也不是坐标因子；因此 $h$ 在 Laurent 环中不可约。又 $h(0)=1$，排除了将多项式因子在该环中变成单位的非平凡单项式因子。故 $h$ 绝对不可约，(43.11) 遂给出 $f_W$ 的几何不可约性。

还必须证明原商足够稠密，而非将原标签上的零集直接等同于全部几何零集。由定理 26.2 及 $E_W=F$，存在原 $u,v\in W\setminus\{0\}$，使 $r=u/v$ 满足 $d_W(r)=1$。在该原点对处，(43.6) 的微分为

$$
(h,k)\longmapsto v^{-1}(h-rk),\qquad
\operatorname{rank}d\phi_{(u,v)}=\dim_F(W+rW)=7.
\tag{43.15}
$$

特征零下的 Jacobian 像维数判据及前述七维上界说明商映射的几何像闭包恰为七维。它包含于不可约七维超曲面 $V(f_W)$，所以两者相等。这是 §41 的像维数论证，在这里以定理 26.2 提供原域中的秩七点。原 $F$-坐标点在映射定义域中 Zariski 稠密，理由是无限域上的非零多项式不能在全部原坐标上消失；分母非零的原 $D$ 元素在每个嵌入下均非零。因此即使在代数闭包中取闭包，也有

$$
\overline{\sigma(Q_W)}^{\mathrm{Zar}}=V(f_W).
\tag{43.16}
$$

现在设 $Q_Y=Q_W$。同一原 $a$ 也在 $Q_Y$ 外，所以 $f_Y(a)\ne0$。$f_Y$ 在 (43.16) 的稠密原商上消失，零点定理及 $f_W$ 的几何不可约性给出 $f_W\mid f_Y$。二者同为四次，从而

$$
f_Y=c f_W,\qquad
c=f_Y(a)/f_W(a)\in F^\times.
\tag{43.17}
$$

分别对 $W,Y$ 在这个同一原 $a$ 处归一化，由 (43.11)、(43.17) 得

$$
\det(I_8+N_Y\operatorname{diag}(x))
=\det(I_8+N_W\operatorname{diag}(x)).
\tag{43.18}
$$

$\prod_{\sigma\in S}x_\sigma$ 的系数恰为 $S$ 对应的主子式，故两矩阵的全部对应主子式相等。至此只得到了行列式与主子式信息，没有从支持预先推断各点的精确核维数。

（四）Galois 传递性排除八阶矩阵的切口。称 $S\sqcup T=\Omega$ 为 $N$ 的切口，若

$$
2\le |S|\le6,\qquad
\operatorname{rank}N[S,T]\le1,\qquad
\operatorname{rank}N[T,S]\le1.
\tag{43.19}
$$

这正是下述主子式重建文献使用的 cut。设存在这样的切口。由 $\ker N=W_K$，

$$
\dim N(K^T)=|T|-\dim(W_K\cap K^T)
=|T|-4+\rho(S).
$$

$N(K^T)$ 在 $K^S$ 上的投影秩至多一；该投影的核包含于 $\operatorname{im}N\cap K^T=W_K\cap K^T$，维数至多 $4-\rho(S)$。因此

$$
|T|-4+\rho(S)\le1+4-\rho(S),\qquad
2\rho(S)\le |S|+1.
$$

交换 $S,T$ 得相同的另一条上界。结合已有的严格下界 (43.13)，两边必须分别取等：

$$
2\rho(S)=|S|+1,\qquad 2\rho(T)=|T|+1.
\tag{43.20}
$$

所以两边大小均为奇数，只能为三和五。设三元侧为 $C$，则

$$
\rho(C)=2,\qquad \rho(C^c)=3,\qquad
\rho^*(C)=|C|-4+\rho(C^c)=2,
\tag{43.21}
$$

其中 $\rho^*$ 是对偶拟阵的标准秩函数。

由 (43.13)，每个二元集 $H$ 都满足 $\rho(H)=2$，其六元补集满足 $\rho(H^c)=4$，故 $\rho^*(H)=2-4+4=2$。所以 $M$ 及其对偶都简单。式 (43.21) 表明 $C$ 同时是三元回路和三元余回路。

考察两个不同的 Galois 共轭 $C,C'$。它们不可能只交一个元素，因为回路与余回路不能恰交一个元素：在线性表示中，两者分别给出相互正交的依赖向量与行空间向量，若支持只交一点，点积就只有一个非零项。它们也不可能交两个元素：此时二元交集秩二，秩的次模性给出

$$
\rho(C\cup C')\le\rho(C)+\rho(C')-\rho(C\cap C')=2,
$$

而四元并集由 (43.13) 必须秩至少三，矛盾。故不同共轭只能互不相交。全部共轭之并是非空的 $G$-不变集合，$G$ 在八个嵌入上传递，所以这些三元组必须分拆全部八个标签，与 $3\nmid8$ 矛盾。这证明 $N_W$ 无切口。

（五）成熟主子式重建与原域乘数下降。现在应用 Loewy 的无切口重建结论，精确采用 Al Ahmadieh 上引文 Theorem 4.1 的无切口方向；相同充分条件也见 Chatterjee–Ghosh–Gurjar–Raj，[*Characterizing and Testing Principal Minor Equivalence of Matrices*，arXiv:2410.01961v1，Lemma 2.8(2)](https://arxiv.org/html/2410.01961v1)。其陈述是：不可约且无切口的矩阵，其全部对应主子式确定矩阵至可逆对角共轭或转置后的可逆对角共轭。这里的 diagonal equivalence 包含转置，不能删去这一支。

由（三）（四），该定理的前件已满足；(43.18) 给出其主子式相等前件。因此存在分裂域上的可逆对角矩阵 $\Lambda$，使

$$
N_Y=\Lambda N_W\Lambda^{-1}
\quad\text{或}\quad
N_Y=\Lambda N_W^{\mathsf T}\Lambda^{-1}.
\tag{43.22}
$$

取像空间，使用 (43.9)，得到

$$
Y_K=\Lambda W_K
\quad\text{或}\quad
Y_K=\Lambda\operatorname{im}N_W^{\mathsf T}
=\Lambda(W^\perp)_K.
\tag{43.23}
$$

最后一个等式来自 $\operatorname{im}N_W^{\mathsf T}=(\ker N_W)^\perp$，以及分裂坐标中原迹配对恰为标准点积 $\sum_\sigma x_\sigma y_\sigma$。因此转置分支准确对应原迹对偶，没有引入新的标签置换。

为将分裂对角乘数收回原域，直接使用 §26、§42 的有限线性核扩底事实。对 $A=W$ 或 $W^\perp$，在原 $F$ 上置

$$
T(A,Y)=\ker\bigl(D\longrightarrow\operatorname{Hom}_F(A,D/Y)\bigr),
\qquad c\longmapsto(z\longmapsto cz+Y).
$$

式 (42.8) 的同一扩底保核事实对任意当前 $F$ 给出

$$
T(A,Y)\otimes_F K
=\{c\in D\otimes_F K:cA_K\subseteq Y_K\}.
\tag{43.24}
$$

(43.23) 的对角向量是右边的一个非零元素，故原 $T(A,Y)$ 非零。取原 $0\ne\gamma\in T(A,Y)$，原 $D$ 为域使乘 $\gamma$ 单射；$\gamma A\subseteq Y$ 及两边同为四维便给出 $Y=\gamma A$。这里并未断言任意分裂对角向量本身是某个原元素的嵌入像，只利用非零线性核下降取得一个原乘数。

这完成了 $E_W=F$ 时从支持相等到第三项的证明；$E_W\ne F$ 时已由（一）给出更强结论。反向，整体原标量不变性与引理 40.2 在 $n=8,k=4$ 时直接给出

$$
d_{\gamma W}(r)=d_W(r),\qquad
d_{\gamma W^\perp}(r)=d_{W^\perp}(r)=d_W(r)
\qquad(r\in D^\times).
\tag{43.25}
$$

因此标量或迹对偶关系推出全部精确交维相等；交维相等再由 $Q_W=\{0\}\cup\{r\in D^\times:d_W(r)>0\}$ 推出支持相等。若 $E_W\ne F$，将 $Y=W^\perp$ 代入（一）还说明两种轨道必然重合。这证明全部结论。$\square$

本定理区分三层信息：支持只记录哪些非零原标签的交维为正；四次行列式还记录一份代数方程；精确交维是各原标签处的核维数。一般行列式相等并不直接给出核维数相等。这里先以原商稠密性取得方程，再由实际域的 Galois 约束排除矩阵切口，应用既有主子式重建并下降到原标量或迹对偶，最后才用 (43.25) 恢复精确交维。

八点分裂几何本身也有精确先例。Howard–Millson–Snowden–Vakil，[*The geometry of eight points in projective space: Representation theory, Lie theory, dualities*，arXiv:1103.5255v1，§8、Propositions 8.1–8.2](https://arxiv.org/html/1103.5255v1)，证明八个带标签的 $\mathbb P^3$ 点配置的不变量环中，由一次不变量生成的子环给出 Gale 对偶的商。这些一次不变量由互补括号积 $p_Ip_{I^c}$ 张成，正是 (41.6) 的系数；行基变换与逐行缩放对应配置的射影等价，取正交补对应 Gale 对偶。式 (43.13) 是等权配置的严格稳定条件，因此稳定分裂配置中“至多原配置与 Gale 对偶”已有该不变量论表述。本节不将这个几何二重性列作新发现；上述原文也不替代从完整原商到几何方程的稠密桥、原乘数下降及非平凡乘子域分支的自动线性性。

所用的矩阵不可约性判据、无切口主子式重建、Sylvester 恒等式、拟阵对偶及回路与余回路正交性都是既有工具。本节的综合推导将它们接到 §26 的实际域严格秩界与最小正交维、§§34、40 的迹对偶和 §42 的原线性核下降，取得同一原八次域中全部四平面的字面支持与交维纤维结论，不依赖特定 $P_8$ 表示。本条只量化固定八次域中的四平面，不将 §42 特定例子中对全部竞争维数的结论扩张到这里。

白话说，完整的原商表在任意特征零八次域中至多留下两种整体形状：窗口本身与它的迹正交补。若窗口有较大的乘子域，同支持的竞争四平面会被迫继承该域的线性结构，两种形状合成一个标量轨道；否则，可能产生额外歧义的矩阵切口会要求把八个共轭标签分成三元组，因而被排除。这个结论保留每一个原标签，且只比较四维窗口。

## 追加锚（本行以下为增补区）

## 44. 互补基单交换条件下的一般次数原商纤维

**定义 44.1（同一原域与互补基单交换条件）。** 固定特征零域 $F$、同一个实际域扩张 $D/F$ 及整数 $m\ge4$，满足 $[D:F]=2m$。对每个非零 $F$-子空间 $U\le_F D$，沿用

$$
Q_U=\{u/v:u,v\in U,\ v\ne0\},\qquad
d_U(r)=\dim_F(U\cap rU)\quad(r\in D^\times).
\tag{44.1}
$$

原商集包含零。所有商、标签与整体乘数均使用这个原 $D$ 的乘法，不作标签自同构重排。$U^\perp$ 表示原迹配对 $\operatorname{Tr}_{D/F}(uv)$ 的正交补。

取有限正规闭包 $K/F$，以 $\Omega=\operatorname{Hom}_F(D,K)$ 标记分裂同构 $D\otimes_F K\simeq K^\Omega$，并将 $W_K=W\otimes_F K$ 视为其中的 $m$-平面。选择原 $W$ 的一个 $F$-基 $w_1,\ldots,w_m$，令 $B_W=(\sigma(w_j))_{\sigma,j}$。称 $W$ 满足条件 $\mathrm H$，若存在分拆 $\Omega=E\sqcup E^c$，使 $E,E^c$ 都是 $B_W$ 的行基，且

$$
E-\{e\}+\{f\},\qquad E^c-\{f\}+\{e\}
\quad\text{均为行基}\qquad(e\in E,\ f\in E^c).
\tag{44.2}
$$

这只涉及带标签行拟阵，不依赖所选列基或进一步扩域。将 $E$ 的行排在前面并归一化列基，等价地写成

$$
W_K=\operatorname{colspan}\begin{pmatrix}I_m\\ A\end{pmatrix},
\qquad A\in\operatorname{GL}_m(K),\qquad
a_{ji}\ne0,\quad (A^{-1})_{ij}\ne0\quad(1\le i,j\le m).
\tag{44.3}
$$

确实，以 $E$ 为基时的单交换子式是 $A$ 的条目；以 $E^c$ 为基时的单交换子式是 $A^{-1}$ 的条目，均只差非零基子式及符号。统一行拟阵，即每个 $m$ 元行集都是基，蕴含 $\mathrm H$；$\mathrm H$ 只要求这两组互补基及其单交换。

**定理 44.2（单交换条件下的完整原支持与交维纤维）。** 在定义 44.1 的同一原 $F,D$ 中，设 $W$ 为满足 $\mathrm H$ 的 $m$-平面。则对每个非零 $F$-子空间 $Y\le_F D$，不预设其维数，有

$$
\boxed{\quad
Q_Y=Q_W
\ \Longleftrightarrow\
\bigl[\ \forall r\in D^\times,\ d_Y(r)=d_W(r)\ \bigr]
\ \Longleftrightarrow\
\bigl[\ Y=\gamma W\ \text{或}\ Y=\gamma W^\perp,\
             \gamma\in D^\times\ \bigr].
\quad}
\tag{44.4}
$$

支持相等因而强制 $\dim_FY=m$。其纤维至多有两个原非零标量轨道，允许重合。此外，$W$ 的原商行列式绝对不可约，原 $Q_W$ 在它的超曲面中 Zariski 稠密，闭包维数为 $2m-1$，且 $Q_W\ne D$。存在原 $r_0\in D^\times$ 满足 $d_W(r_0)=1$。

证明。（一）原行列式与单交换系数。固定原 $D$ 的一个 $F$-基。对任意 $m$-平面 $U$，令 $B_U^F$ 为其包含矩阵，$M_q$ 为原乘法算子，并置

$$
\Delta_U(q)=\det[\,B_U^F\mid M_qB_U^F\,].
\tag{44.5}
$$

这是原 $2m$ 个坐标上的齐次 $m$ 次多项式，暂允许它恒为零。对每个原 $q\in D$，包括零，都有

$$
\Delta_U(q)=0\quad\Longleftrightarrow\quad q\in Q_U.
\tag{44.6}
$$

左边等价于存在不全为零的 $a,b\in U$ 满足 $a+qb=0$；因包含映射单射，必有 $b\ne0$，故 $q=-a/b$。反向由商表示给出。这里实际使用了原 $D$ 为域。

在同一分裂坐标中，$\Delta_U$ 只差非零常数便成为

$$
P_U(q)=\det[\,B_U\mid\operatorname{diag}(q)B_U\,].
$$

按右侧 $m$ 列作 Laplace 展开，$q_I=\prod_{\sigma\in I}q_\sigma$ 的系数为带固定符号的互补 Plücker 积 $p_I(U)p_{I^c}(U)$。这是 (41.6) 的同一行列式展开。对 (44.3) 记分裂变量为 $(x_1,\ldots,x_m,y_1,\ldots,y_m)$，$D_x=\operatorname{diag}(x_i)$、$D_y=\operatorname{diag}(y_j)$，消去左下块得到

$$
\begin{aligned}
P_W(x,y)&=\det(D_yA-AD_x)=\det(A)\,g_A(x,y),\\
g_A(x,y)&=\det(D_y-AD_xA^{-1}).
\end{aligned}
\tag{44.7}
$$

$g_A$ 齐次且对每个变量次数至多一。其下列系数均非零：

$$
[y_1\cdots y_m]g_A=1,\qquad
\left[x_i\prod_{\ell\ne j}y_\ell\right]g_A
=-a_{ji}(A^{-1})_{ij}\ne0.
\tag{44.8}
$$

这些系数已足以证明绝对不可约。若在任意扩域中 $g_A=fg$ 非平凡分解，因乘积齐次，可取 $f,g$ 齐次；逐变量次数相加又使每个变量只属于其中一个因子。令 $S$ 为属于 $f$ 的变量集，则每个支撑单项式的 $S$-次数均为 $\deg f$。比较 (44.8) 中的 $y_1\cdots y_m$ 与将 $y_j$ 换成 $x_i$ 的单项式，得到

$$
\boldsymbol1_{\{x_i\in S\}}=\boldsymbol1_{\{y_j\in S\}}
\qquad\text{对所有 }i,j.
$$

于是所有变量都在同一因子中，另一因子为常数，矛盾。因此 $g_A$、$P_W$ 及原坐标中的 $\Delta_W$ 都绝对不可约。无限域上非零多项式有原坐标非零值，故 (44.6) 还给出 $Q_W\ne D$。

（二）分裂秩见证与实际原域返回。置 $V=W_K$，取

$$
u_0=\begin{pmatrix}e_1\\ Ae_1\end{pmatrix}\in V,
\qquad v_0\in V\cap(K^\times)^{2m},\qquad
q_0=(u_{0,\sigma}/v_{0,\sigma})_\sigma.
\tag{44.9}
$$

$v_0$ 存在，因为各坐标在 $V$ 上均非零，有限个真坐标超平面不能覆盖无限域上的 $V$。$u_0$ 的后 $m$ 个坐标均非零，前 $m$ 个坐标仅第一个非零。

若 $b\in V$ 且 $a=\operatorname{diag}(q_0)b\in V$，则 $a$ 的前块第 $2,\ldots,m$ 个坐标为零，由前块投影同构可知 $a=\lambda u_0$。后块中 $q_0$ 的坐标均非零，故 $b$ 的后块与 $\lambda v_0$ 相同；后块投影也是同构，所以 $b=\lambda v_0$。反向显然成立。因而

$$
\{b\in V:\operatorname{diag}(q_0)b\in V\}=Kv_0,\qquad
\operatorname{rank}[\,B_W\mid\operatorname{diag}(q_0)B_W\,]=2m-1.
\tag{44.10}
$$

这里 $q_0$ 有零分裂坐标，绝非原 $D^\times$ 元素的嵌入像；它只证明一个原系数秩条件不是恒等零。

具体地，取原点对参数 $(u,v)\in W\times W$，在范数 $N_{D/F}(v)\ne0$ 的开集 $\mathcal X$ 上，$\rho(u,v)=uv^{-1}$ 是原 $F$ 上的正则映射。原矩阵

$$
\mathcal M(u,v)=[\,B_W^F\mid M_{uv^{-1}}B_W^F\,]
\tag{44.11}
$$

的条目是原 $F$ 系数有理函数，分母为 $N_{D/F}(v)$ 的幂。对原坐标矩阵扩底并换成分裂坐标后，(44.10) 说明它的某个 $(2m-1)$ 阶子式不是零有理函数。清除范数分母，得到非零 $h\in F[W\times W]$。由于 $F$ 无限，可取原 $u,v\in W$ 使

$$
h(u,v)N_{D/F}(v)\ne0.
\tag{44.12}
$$

对这个实际点对，$r_0=u/v\in D$，(44.11) 的秩至少为 $2m-1$；由 (44.6) 其行列式为零，故秩恰为 $2m-1$。$r_0$ 不为零，因为零标签处 (44.11) 的秩只有 $m$。原 $r_0$ 可逆，两组列各有秩 $m$，所以

$$
d_W(r_0)=2m-\operatorname{rank}\mathcal M(u,v)=1.
\tag{44.13}
$$

这一步返回的是原 $F$ 参数及原 $W$ 元素，并未将 (44.9) 的零坐标向量当作域元素。按 §26 的乘子域结论，$W\cap r_0W$ 对 $E_W$ 线性，故 (44.13) 也给出 $E_W=F$。

（三）原支持稠密、竞争维数及方程相等。沿用 (43.15) 的商映射微分，在 (44.12) 的原点对处有

$$
d\rho_{(u,v)}(h,k)=v^{-1}(h-r_0k),\qquad
\operatorname{rank}d\rho_{(u,v)}=\dim_F(W+r_0W)=2m-1.
\tag{44.14}
$$

特征零下的像维数判据使几何像闭包维数至少为 $2m-1$。另一方面，像包含于绝对不可约超曲面 $V(\Delta_W)$，后者维数恰为 $2m-1$，故闭包就是该超曲面。

还须核对原点的稠密性。$\mathcal X$ 是原 $F$ 仿射空间中的非空开集，其原 $F$ 点在代数闭包上仍 Zariski 稠密：在无限子域上，任意扩域系数的非零多项式都不能在全部原坐标上消失，逐变量归纳即可；再乘开集的非零范数多项式可得开集版本。因此任何在 $\rho(\mathcal X(F))=Q_W$ 上消失的多项式，其拉回在整个 $\mathcal X$ 上消失。由此，在任一含 $K$ 的代数闭包中，

$$
\overline{Q_W}^{\,\mathrm{Zar}}=V(\Delta_W),\qquad
\dim\overline{Q_W}^{\,\mathrm{Zar}}=2m-1.
\tag{44.15}
$$

这里用固定原坐标理解左边，换成分裂坐标则得到同一等式的可逆线性像。

设 $Q_Y=Q_W$，记 $r=\dim_FY$。若 $r<m$，在商映射的分母各非零基坐标片上，可将分子、分母同时缩放，使该坐标为一；每片至多有 $2r-1$ 个参数。因此

$$
\dim\overline{Q_Y}^{\,\mathrm{Zar}}\le2r-1<2m-1,
$$

与 (44.15) 矛盾。若 $r>m$，则对每个原 $q\in D^\times$，

$$
\dim_F(Y\cap qY)\ge2r-2m>0,
$$

于是 $Q_Y=D$，也与 $Q_W\ne D$ 矛盾。因此 $r=m$，可使用 (44.5)。

$\Delta_Y$ 非零，否则 (44.6) 给出 $Q_Y=D$。它在稠密的 $Q_W$ 上消失，由绝对不可约性及零点定理，$\Delta_W\mid\Delta_Y$。二者次数同为 $m$，所以

$$
\Delta_Y=c\Delta_W,\qquad c\in F^\times.
\tag{44.16}
$$

常数属于 $F$，可比较任一非零原系数得到。分裂后便有 $P_Y\propto P_W$。$y_1\cdots y_m$ 的系数是带符号的 $p_Ep_{E^c}$，在 $W$ 上非零，故在 $Y$ 上也非零。于是同一 $E,E^c$ 也都是 $Y_K$ 的行基，可以写

$$
Y_K=\operatorname{colspan}\begin{pmatrix}I_m\\ A'\end{pmatrix},
\qquad A'\in\operatorname{GL}_m(K).
$$

将两边的 $y_1\cdots y_m$ 系数归一化为一，(44.7)、(44.16) 给出

$$
g_{A'}(x,y)=g_A(x,y).
\tag{44.17}
$$

（四）常数矩阵的全部主子式与既有重建定理。对 $I,J\subseteq\{1,\ldots,m\}$、$|I|=|J|=k$，用 Cauchy–Binet 展开 (44.7) 得

$$
[x_Iy_{J^c}]g_A
=(-1)^k\det A[J,I]\det A^{-1}[I,J].
\tag{44.18}
$$

令

$$
C_A=\begin{pmatrix}0&A^{-1}\\ A&0\end{pmatrix}.
\tag{44.19}
$$

其第一块取 $I$、第二块取 $J$ 的主子式，在 $|I|\ne|J|$ 时为零，在 $|I|=|J|=k$ 时恰为 (44.18)。这是交换两组 $k$ 列后所得两个方块行列式的乘积。因此 (44.17) 等价于 $C_A,C_{A'}$ 的全部带原坐标标签的对应主子式相等。

条件 $\mathrm H$ 使 $C_A$ 的有向非零条目图包含两块之间所有双向边，故 $C_A$ 不可约。还须排除切口。取其任一指标子集 $X$，满足 $2\le|X|\le2m-2$，并以 $I,J$ 表示它在两块中的部分。按两块排列行列后，

$$
\operatorname{rank}C_A[X,X^c]
=\operatorname{rank}A^{-1}[I,J^c]
 +\operatorname{rank}A[J,I^c].
\tag{44.20}
$$

若 $I,J,I^c,J^c$ 都非空，则由条目非零，两项各至少为一。否则 $X$ 或 $X^c$ 完全位于一个坐标块中，(44.20) 中相应部分是可逆矩阵 $A$ 或 $A^{-1}$ 的一组完整行或完整列，其秩等于该侧指标数，至少为二。因此每个这样的 $X$ 都满足 $\operatorname{rank}C_A[X,X^c]\ge2$，尤其不存在双向跨块秩都至多一的切口。

现在消费经典主子式重建：一个不可约且无切口的矩阵，由全部对应主子式确定至可逆对角共轭或转置后的可逆对角共轭。精确引用是 Al Ahmadieh，[*The Fiber of the principal minor map*，arXiv:2309.00806v2，Theorem 4.1 的无切口充分方向](https://arxiv.org/html/2309.00806v2)，该方向归于 Loewy，*Principal minors and diagonal similarity of matrices*，Linear Algebra and its Applications 78，23–64，Theorem 1；同一充分条件见 Chatterjee–Ghosh–Gurjar–Raj，[*Characterizing and Testing Principal Minor Equivalence of Matrices*，arXiv:2410.01961v1，Lemma 2.8(2)](https://arxiv.org/html/2410.01961v1)。这里的 diagonal equivalence 包含转置分支。

该已知定理应用于 (44.19)，给出可逆对角 $R,S$，使

$$
A'=SAR^{-1}\quad\text{或}\quad A'=SA^{-\mathsf T}R^{-1}.
\tag{44.21}
$$

第一支给出 $Y_K=\operatorname{diag}(R,S)W_K$。分裂迹配对为标准点积，且

$$
(W^\perp)_K
=\operatorname{colspan}\begin{pmatrix}I_m\\-A^{-\mathsf T}\end{pmatrix},
$$

故第二支给出 $Y_K=\operatorname{diag}(R,-S)(W^\perp)_K$。所有指标保持同一嵌入标签，没有坐标置换。

（五）原乘数与完整交维。直接复用 (43.24) 的有限线性核扩底桥。对原 $U=W$ 或 $W^\perp$，置

$$
\begin{aligned}
T(U,Y)&=\ker\bigl(D\longrightarrow\operatorname{Hom}_F(U,D/Y)\bigr),\\
c&\longmapsto(z\longmapsto cz+Y).
\end{aligned}
$$

则

$$
T(U,Y)\otimes_FK
=\{c\in D\otimes_FK:cU_K\subseteq Y_K\}.
\tag{44.22}
$$

上一段相应的分裂对角向量使右边非零，故原 $T(U,Y)$ 非零。取原 $0\ne\gamma\in T(U,Y)$；原 $D$ 为域使 $\gamma$ 可逆，$\gamma U\subseteq Y$ 及两边维数同为 $m$ 给出 $Y=\gamma U$。下降的是“存在非零乘数”这个线性核条件，不是断言选中的分裂对角向量逐项来自同一个原域元素。

反向使用 §34 的 (34.7)、引理 40.2 的半维迹对偶恒等式。对任意原 $r\in D^\times$，

$$
\begin{aligned}
d_W(r)
&=2m-\dim_F(W+rW)\\
&=\dim_F(W^\perp\cap r^{-1}W^\perp)
=\dim_F(rW^\perp\cap W^\perp)
=d_{W^\perp}(r).
\end{aligned}
\tag{44.23}
$$

第三项的等维来自乘以原 $r$。整体乘以原 $\gamma\ne0$ 也保持每个标签的交维。故 (44.4) 的第三项推出第二项；第二项由

$$
Q_U=\{0\}\cup\{r\in D^\times:d_U(r)>0\}
$$

推出第一项，完成全部等价。$\square$

本定理的来源边界。互补 Plücker 积到 (44.18) 的对应是行列式恒等式，(44.19) 的重建是上述经典主子式定理的直接应用，均不作为新的矩阵重建结论。八点情形中互补括号积给出 Gale 对偶商的精确先例，已由 §43 对应到 Howard–Millson–Snowden–Vakil，[*The geometry of eight points in projective space: Representation theory, Lie theory, dualities*，arXiv:1103.5255v1，§8、Propositions 8.1–8.2](https://arxiv.org/html/1103.5255v1)；该先例的范围是八点配置及其不变量商。

这里的仓内综合推导（repo-derived）是把单交换系数的不可约性、实际原商稠密性、竞争维数排除与既有线性核下降接到常数矩阵重建，得到 (44.4) 的一般次数、同一原域、全部竞争子空间结论。它不以统一行拟阵为前件，也不把这些指定文献未陈述的组合解释为全球首次性。$\mathrm H$ 是本定理的充分条件；本条不分类其外的全部半维窗口。

**命题 44.3（每个半维次数的非统一实际域族与单轨道纤维）。** 对每个 $m\ge4$，令 $\zeta$ 为本原 $2m$ 次单位根、$t$ 为超越元，并在实际域中置

$$
F=\mathbb Q(\zeta)(t),\qquad
D=F(\alpha),\qquad \alpha^{2m}=t,\qquad
W=\operatorname{span}_F\{1,\alpha,\ldots,\alpha^{m-2},\alpha^m\}.
\tag{44.24}
$$

则 $[D:F]=2m$，$W$ 满足 $\mathrm H$，其嵌入行拟阵却不统一，并且

$$
W^\perp=\alpha W,\qquad
\{0\ne Y\le_FD:Q_Y=Q_W\}
=\{\gamma W:\gamma\in D^\times\}.
\tag{44.25}
$$

证明。$X^{2m}-t$ 在 $\mathbb Q(\zeta)[t][X]$ 中对素元 $t$ 满足 Eisenstein 判据，故在 $F[X]$ 中不可约，给出所述次数及幂基。因 $F$ 已含全部 $2m$ 次单位根，全部嵌入在 $D$ 中为

$$
\sigma_j(\alpha)=\alpha\zeta^j,\qquad 0\le j<2m.
$$

对任意 $m$ 个不同的根 $z_1,\ldots,z_m\in\mu_{2m}$，相应的行子式除去公共非零列因子后为

$$
\det
\begin{pmatrix}
1&z_1&\cdots&z_1^{m-2}&z_1^m\\
\vdots&\vdots&&\vdots&\vdots\\
1&z_m&\cdots&z_m^{m-2}&z_m^m
\end{pmatrix}
=\prod_{i<j}(z_j-z_i)\sum_{i=1}^m z_i.
\tag{44.26}
$$

这是经典 alternant 恒等式在一阶对称因子上的情形，也可直接核对：在各 $z_i$ 处，$\prod_{\ell=1}^m(T-z_\ell)=0$ 将最后一列 $z_i^m$ 写成 $(\sum_\ell z_\ell)z_i^{m-1}$ 加上前 $m-1$ 列的线性组合，行列式即为右边。因此该行集为基当且仅当所选根之和非零。

取互补半圆根集

$$
E=\{1,\zeta,\ldots,\zeta^{m-1}\},\qquad E^c=-E,\qquad
s=\sum_{z\in E}z=\frac{2}{1-\zeta}.
\tag{44.27}
$$

在复嵌入 $\zeta\mapsto e^{\pi i/m}$ 下，

$$
|s|=\frac1{\sin(\pi/(2m))}>2,
\tag{44.28}
$$

因为 $m\ge4$ 使 $0<\pi/(2m)\le\pi/8<\pi/6$。两组根之和为 $s,-s$，故它们都是行基。任取 $a\in E,b\in E^c$，交换后的根和为 $s-a+b$；由

$$
|s-a+b|\ge|s|-|a-b|\ge|s|-2>0
$$

知该行集仍为基。全部 $2m$ 个根之和为零，其互补交换行集的根和就是 $-(s-a+b)$，也非零。这证明 $\mathrm H$，无须对其他高阶子式加条件。

但 $m$ 元根集

$$
\{1,\zeta^2,\zeta^4,\ldots,\zeta^{2m-2}\}
$$

恰为全部 $m$ 次单位根，根和为零。由 (44.26)，其行子式为零，故该实际域族不统一。这也证明 $\mathrm H$ 在实际原域窗口中严格弱于统一性，而非仅有抽象分裂矩阵的区别。

最后，对任意非负整数 $k$，

$$
\operatorname{Tr}_{D/F}(\alpha^k)
=\alpha^k\sum_{j=0}^{2m-1}\zeta^{jk}
=\begin{cases}
2m\,\alpha^k,&2m\mid k,\\
0,&2m\nmid k.
\end{cases}
\tag{44.29}
$$

对指数集 $S=\{0,1,\ldots,m-2,m\}$，在模 $2m$ 意义下，$-S$ 的补集恰为

$$
T=\{1,2,\ldots,m-1,m+1\}.
$$

因此幂基迹配对使 $\operatorname{span}_F\{\alpha^j:j\in T\}$ 与 $W$ 正交；两者各为 $m$ 维，迹配对非退化，故

$$
W^\perp
=\operatorname{span}_F\{\alpha,\alpha^2,\ldots,\alpha^{m-1},\alpha^{m+1}\}
=\alpha W.
\tag{44.30}
$$

将所证 $\mathrm H$ 与 (44.30) 代入定理 44.2，两种原标量轨道重合，得到 (44.25)。$\square$

白话说，不必要求任取一半嵌入都独立：只要先找到两组互补的基，任意交换它们之间的一个成员后，两边仍然是基，就足以锁住整个原商纤维。支撑表先确定一张不可约方程并强制候选维数，再由经典主子式重建留下窗口及其迹对偶两种形状；原域线性核保证这些形状之间的整体乘数确实属于原 $D$。分裂证明中出现的零坐标向量只负责证明某个多项式非零，不能充当原域元素。

命题 44.3 给出每个 $m\ge4$ 的实际例子：某些一半根集确实线性相关，然而所选两组互补半圆及全部单交换都独立。这些窗口的迹对偶又恰是整体乘以 $\alpha$，所以完整原商表只对应一个原标量轨道。结论始终使用全部精确原标签与原标量等价；根和公式、迹计算和所引重建各自只承担上述明确步骤。

## 追加锚（本行以下为增补区）

## 45. 相对二维传递与固定三十次域中的四个同交维轨道

**定义 45.1（中心、相对窗口与原标签）。** 固定特征零域塔

$$
F\subset E\subset D,\qquad [E:F]=6,\qquad [D:E]=5.
\tag{45.1}
$$

所有窗口都是这个原 $D$ 的 $F$-子空间；原标量等价只指乘以 $D^\times$ 的元素。取 $C\le_F E$、$\dim_F C=3$，以及 $V\le_E E\oplus D$、$\dim_E V=3$。分别使用非退化对称配对

$$
\langle a,b\rangle_E=\operatorname{Tr}_{E/F}(ab),\qquad
\beta((a,x),(b,y))=ab+\operatorname{Tr}_{D/E}(xy)
\tag{45.2}
$$

定义 $C^\perp$ 和 $V^\perp$；两者仍分别为三维 $F$-空间和三维 $E$-空间。记 $C^0=C,C^1=C^\perp$，$V^0=V,V^1=V^\perp$。称 $V$ 可用，若对 $U=V,V^\perp$，投影 $p_D:U\to D$ 都单射，投影 $p_E:U\to E$ 都满射。置

$$
W_{ef}=W(C^e,V^f)
=\{x\in D:\ \exists a\in C^e,\ (a,x)\in V^f\},
\qquad e,f\in\{0,1\}.
\tag{45.3}
$$

仍在逐字相同的原标签上定义 $d_W(r)=\dim_F(W\cap rW)$，$r\in D^\times$；中心的 $d_C(t)$ 同样使用原 $t\in E^\times$。若另容许标签零，则约定 $d_W(0)=d_C(0)=0$。

**定理 45.2（相对 $E^2$ 像公式与两次对偶传递）。** 在定义 45.1 中若 $V$ 可用，则四个 $W_{ef}$ 都为十五维。对任意 $f$、任意原 $r\in D^\times$，令 $U=V^f$，并在 $U\times U$ 中定义 $E$-线性关系及其像

$$
\begin{aligned}
T_r(U)&=\{((a,x),(b,y))\in U\times U:x=ry\},\\
\rho_r:T_r(U)&\longrightarrow E^2,\qquad
((a,x),(b,y))\longmapsto(a,b),\\
R_r(U)&=\operatorname{im}\rho_r,\qquad
\kappa_r(U)=\dim_E\ker\rho_r.
\end{aligned}
\tag{45.4}
$$

则完整交维由下式给出，而非仅给出其正支持：

$$
\boxed{\ d_{W_{ef}}(r)=6\kappa_r(U)
 +\dim_F\bigl(R_r(U)\cap(C^e\times C^e)\bigr).\ }
\tag{45.5}
$$

写 $A=C^e$、$R=R_r(U)$，第二项的所有秩层及零坐标边界恰为

$$
\dim_F(R\cap A^2)=
\begin{cases}
0,&R=0,\\
6,&R=E^2,\\
3,&R=E(1,0)\ \text{或}\ R=E(0,1),\\
d_A(u/v),&R=E(u,v),\quad uv\ne0.
\end{cases}
\tag{45.6}
$$

因此在同一个原 $D$ 中，对每个原 $r\in D^\times$ 都有

$$
\boxed{\ d_{W_{00}}(r)=d_{W_{10}}(r)
=d_{W_{01}}(r)=d_{W_{11}}(r).\ }
\tag{45.7}
$$

此外，限制到实际中间域标签时有

$$
d_{W_{ef}}(s)=12+d_{C^e}(s)\qquad(s\in E^\times).
\tag{45.8}
$$

证明。对 $U=V^f$，$p_E$ 的核为二维 $E$-空间。$p_E^{-1}(C^e)$ 因而为 $12+3=15$ 维 $F$-空间，而 $p_D$ 将它单射到 $W_{ef}$，证明维数断言。

固定 $r\ne0$。映射 $((a,x),(b,y))\mapsto x$ 给出 $F$-线性同构

$$
\rho_r^{-1}(C^e\times C^e)\ \simeq\ W_{ef}\cap rW_{ef}.
\tag{45.9}
$$

确实，交叠元素 $x$ 唯一确定 $y=r^{-1}x$；$p_D$ 的单射性又唯一确定两个提升中的 $a,b$。反向由 (45.3) 立即给出。因此限制后的正合列

$$
0\longrightarrow\ker\rho_r
\longrightarrow\rho_r^{-1}(C^e\times C^e)
\overset{\rho_r}{\longrightarrow}
R_r(U)\cap(C^e\times C^e)\longrightarrow0
\tag{45.10}
$$

给出 (45.5)。像的 $E$-维数只能是零、一、二。零空间、全平面和两条坐标轴分别给 (45.6) 的前三行。剩下的直线以 $t\mapsto(tu,tv)$ 参数化，其所需参数为 $u^{-1}A\cap v^{-1}A$；乘以 $u$ 将它同构到 $A\cap(u/v)A$，得到最后一行。即使这个交叠为零，等式也仍成立。于是 $\kappa=0$、$R=0$、轴线、非轴线零交叠等边界均未被删去。

这里的直线交维是线性集的带点标签权重接口：一般地，对 $A\times A\subset E^2$，点 $E(u,v)$ 的权重就是 $\dim_F((A\times A)\cap E(u,v))$。Zullo，[*Multi-orbit cyclic subspace codes and linear sets*，arXiv:2112.08781v2，§2.2、Theorem 3.5](https://arxiv.org/html/2112.08781v2)，在有限域中以乘积子空间的点权联系商与标量交叠。本证明使用上面的直接同构，不把该有限域定理当作特征零传递定理。

中心对偶直接消费 §34 式 (34.7)、引理 40.2 的半维迹恒等式。具体地，对每个原 $t\in E^\times$，

$$
\begin{aligned}
\dim_F(C^\perp\cap t^{-1}C^\perp)
&=6-\dim_F(C+tC)=d_C(t),\\
d_{C^\perp}(t^{-1})&=d_{C^\perp}(t).
\end{aligned}
\tag{45.11}
$$

第二个等式由乘以 $t$ 的同构给出，故所得是同一标签 $t$ 下的 $d_C(t)=d_{C^\perp}(t)$。结合配对及其非退化性是既有 Frobenius 工具，见 Bachoc–Serra–Zémor，[*Revisiting Kneser's theorem for field extensions*，arXiv:1510.01354v2，§2.2，式 (2)](https://arxiv.org/html/1510.01354v2)。Csajbók–Marino–Polverino，[*Classes and equivalence of linear sets in PG(1,q^n)*，arXiv:1607.06962v1，Result 2.1](https://arxiv.org/html/1607.06962v1)，已有有限域迹辛对偶逐点保权的先例；这里的对称迹计算由 (45.11) 自身承担。由于 (45.4) 的 $R,\kappa$ 只依赖 $U,r$，(45.6) 给出 $d_{W_{0f}}=d_{W_{1f}}$，包含全部零值。

再对原 $D/F$ 使用迹传递。若 $(a,x)\in V$、$(b,z)\in V^\perp$，则

$$
\operatorname{Tr}_{D/F}(xz)
=\operatorname{Tr}_{E/F}\bigl(\operatorname{Tr}_{D/E}(xz)\bigr)
=-\operatorname{Tr}_{E/F}(ab).
\tag{45.12}
$$

当 $a\in C,b\in C^\perp$ 时右边为零。因此 $W_{11}\subseteq W_{00}^\perp$；两边均为十五维，故

$$
W_{11}=W_{00}^\perp,\qquad W_{01}=W_{10}^\perp,
\tag{45.13}
$$

其中正交补使用原 $\operatorname{Tr}_{D/F}(xz)$。引理 40.2 在 $[D:F]=30$、半维十五时给 $d_{W_{00}}=d_{W_{11}}$。与两组中心等式拼接即得 (45.7)，没有对 $r$ 作域自同构或其他重标记。

最后，$U$ 的 $E$-线性性及唯一提升给 $sW(A,U)=W(sA,U)$，并使 $W(A,U)\cap W(sA,U)=W(A\cap sA,U)$。其维数为 $12+\dim_F(A\cap sA)$，证明 (45.8)。所以原 $E^\times$ 上的限制还可由减去十二恢复中心的完整 $d$ 函数；(45.5) 则控制 $E$ 外的全部原标签。标签零单独满足 $W\cap0W=0$，不能将 $r=0$ 代入 (45.9)，因为此时 $x$ 不再决定 $y$；也不能将 $s=0$ 代入 (45.8)。若将函数延至零，四者在零处仍共同为零。$\square$

**定理 45.3（每个固定 $6\times5$ 域塔中的四个实际轨道）。** 对满足 (45.1) 的每一个固定域塔，都存在实际参数 $C\le_F E$、$V\le_E E\oplus D$，使 $V$ 可用，且 (45.3) 的四个十五维窗口两两不属于同一原 $D^\times$ 轨道，并满足 (45.7)。更强地，取 $D/F$ 的有限正规分裂域 $K$，以原嵌入集合 $\Omega=\operatorname{Hom}_F(D,K)$ 标记 $D\otimes_F K\simeq K^\Omega$；对 $K$ 的任意扩域 $K'$，四个 $W_{ef}\otimes_F K'$ 在保持这些标签的整个对角群 $(K'^\times)^\Omega$ 下仍两两不等价。

证明。先建立同时容许对偶的非空好开集，再返回原域参数，最后从窗口恢复旗标以排除等价。

将 $E$ 的六个嵌入记为 $\sigma_i$，并置 $B_i=\{\tau\in\Omega:\tau|_E=\sigma_i\}$，每个 $B_i$ 有五个元素。分裂后有

$$
E\otimes_F K=K^6,\qquad
D\otimes_F K=\bigoplus_{i=1}^6K^{B_i}.
\tag{45.14}
$$

中心 $C_K$ 是 $K^6$ 中的三平面；相对窗口 $V$ 分裂为六个叶平面 $L_i\le_K K\oplus K^{B_i}$，各有维数三。叶平面的第一个坐标称为接合坐标，其余五个为外部坐标。迹是各嵌入值之和，故 (45.2) 在中心及每一叶上都成为普通点积，$V^\perp$ 的叶平面恰为 $L_i^\perp$。

对任意三平面 $L\le K^6$，选择六行三列的帧 $H$，行向量为 $h_j$。先要求每个三阶行子式非零，并要求线性映射

$$
\Phi_L:K^6\longrightarrow\operatorname{Sym}_3(K),\qquad
z\longmapsto H^{\mathsf T}\operatorname{diag}(z)H
=\sum_{j=1}^6z_jh_j^{\mathsf T}h_j
\tag{45.15}
$$

可逆。这两条是开条件；更换列基只使右边作可逆合同变换，故不依赖帧。若某可逆对角矩阵 $\delta$ 满足 $\delta L=L^\perp$，则 $H^{\mathsf T}\delta H=0$，与 (45.15) 的单射性矛盾。因此该开条件排除叶或中心的带标签对角自对偶，而非只排除原域的某些乘数。

这个开集 $\mathcal U\subset\operatorname{Gr}(3,6)$ 非空的手工见证为

$$
H=\begin{pmatrix}I_3\\ A\end{pmatrix},\qquad
A=\begin{pmatrix}1&1&1\\1&2&3\\1&4&9\end{pmatrix}.
\tag{45.16}
$$

$A$ 的列由 $x=1,2,3$ 的 $(1,x,x^2)^{\mathsf T}$ 给出。其条目非零；任意二阶子式为 $y-x$、$y^2-x^2$ 或 $xy(y-x)$，其中 $x,y$ 是不同的上述正整数；$\det A=(2-1)(3-1)(3-2)=2$。所以 $A$ 的所有方形子式非零，这恰使 $[I_3;A]$ 的全部三阶行子式非零。前三个行平方张成对角对称矩阵，后三个行平方模去它们后，以三个非对角条目表示为

$$
\begin{pmatrix}1&1&1\\2&3&6\\4&9&36\end{pmatrix},
\qquad
\det= (3-2)(6-2)(6-3)=12\ne0.
\tag{45.17}
$$

因此 (45.15) 可逆。这些非零整数在每个特征零域中都非零。

为使好条件也在取对偶后保持，令 $\iota(L)=L^\perp$，取

$$
\mathcal G=\mathcal U\cap\iota(\mathcal U).
\tag{45.18}
$$

Grassmannian 几何不可约，$\iota$ 为代数自同构，所以两个非空开集的交仍非空。$\mathcal G$ 在对偶、坐标置换和可逆对角变换下不变：后两者分别置换行平方或将它们乘以非零平方，而 $(\delta L)^\perp=\delta^{-1}L^\perp$。在 $\mathcal G$ 内，$L,L^\perp$ 都统一，即全部三阶行子式非零，并且二者不能由任何带标签对角矩阵相连。

本处使用 Grassmannian 的标准仿射图及其不可约性，不将其另立为新几何定理；图的构造见 Stacks Project，[§27.22，Tag 089R，Lemma 27.22.1 的证明](https://stacks.math.columbia.edu/tag/089R)。对整个参数空间使用限制标量的标准构造，见同书 [§97.11，Tag 05Y8](https://stacks.math.columbia.edu/tag/05Y8)：

$$
\mathcal X=\operatorname{Gr}_F(3,E)\times
\operatorname{Res}_{E/F}\operatorname{Gr}_E(3,E\oplus D),
\qquad
\mathcal X_K\simeq\operatorname{Gr}_K(3,6)^7.
\tag{45.19}
$$

要求中心及六个叶均属于 $\mathcal G$，得到几何非空开集 $\mathcal O_K=\mathcal G^7$。Galois 作用只置换六个中心坐标、六个叶及各 $B_i$ 内的坐标，故 $\mathcal O_K$ 不变。它也在各因子的带标签对角作用及对偶下不变。叶及其对偶的统一性保证：投影到五个外部坐标单射，因为其中任意三行已满秩；接合投影满射，因为该行非零。投影的秩在扩域前后相同，故这些条件对实际参数也给出原 $V,V^\perp$ 的可用性。

下面取得实际的 $F$-参数，而不将任意七个分裂矩阵误称为下降的窗口。选取 $E$ 的一个 $F$-基，以及 $E\oplus D$ 的一个 $E$-基，(45.19) 有定义在 $F$ 上的稠密大胞

$$
\mathcal B\simeq\mathbb A_F^9\times
\operatorname{Res}_{E/F}\mathbb A_E^9
\simeq\mathbb A_F^{63}.
\tag{45.20}
$$

由于 $\mathcal X_K$ 几何不可约，$\mathcal O_K\cap\mathcal B_K$ 非空。在 $\mathcal B_K=\mathbb A_K^{63}$ 中取非零多项式 $h\in K[t_1,\ldots,t_{63}]$，使其主开集 $D(h)$ 包含于这个交；这是仿射空间中开集含主开集的标准性质，也可由各子式和 (45.15) 的行列式非消失条件取得。作系数范数

$$
P(t)=\prod_{g\in\operatorname{Gal}(K/F)}g(h)(t)
\in F[t_1,\ldots,t_{63}]\setminus\{0\}.
\tag{45.21}
$$

整环性使此积非零，Galois 不变性使其系数属于 $F$。无限域 $F$ 上的非零多项式不能处处为零：按变量数归纳，先使一个非零系数非零，再避开最后一个变量的有限个根。因此存在 $t\in F^{63}$ 满足 $P(t)\ne0$，尤其 $h(t)\ne0$。此 $t$ 对应实际的 $C\le_F E,V\le_E E\oplus D$，且全部七个分裂因子在 $\mathcal G$ 内。(45.16) 只证明几何开集非空，(45.20)–(45.21) 才给出原域中的存在性。

固定如此取得的实际参数，以下论证在 $K$ 的任意扩域 $K'$ 中均成立，暂仍写 $K$。记 $L_i^0=L_i,L_i^1=L_i^\perp$。外部投影的单射性使每个叶可唯一写成图形

$$
L_i^f=\{(\lambda_i^f(x),x):x\in E_i^f\},\qquad
E_i^f=\operatorname{pr}_{B_i}L_i^f,\qquad
N_i^f=\ker\lambda_i^f,
\tag{45.22}
$$

其中 $\dim E_i^f=3$、$\dim N_i^f=2$，$\lambda_i^f:E_i^f\to K$ 满射。域扩张保持线性核与像，故 (45.3) 分裂后恰为

$$
W_{ef,K}=\{(x_i)_i:x_i\in E_i^f,\
(\lambda_i^f(x_i))_{i=1}^6\in C_K^e\}.
\tag{45.23}
$$

中心及其对偶统一，故 $C_K^e\cap Ke_i=0$ 且 $\operatorname{pr}_iC_K^e=K$。前者因为其余五行包含一个满秩三行集，后者因为第 $i$ 行非零。由此可从窗口本身恢复每一已标记块内的旗标：

$$
W_{ef,K}\cap K^{B_i}=N_i^f,
\qquad
\operatorname{pr}_{B_i}W_{ef,K}=E_i^f.
\tag{45.24}
$$

第一式由中心没有单坐标支撑的向量得到；反向任取 $x_i\in N_i^f$，其余块置零即可。对第二式，任取 $x_i\in E_i^f$，先选中心向量的第 $i$ 坐标为 $\lambda_i^f(x_i)$，再利用其余 $\lambda_j^f$ 的满射性逐块提升，便得到所需的窗口向量。这证明恢复的是二维核包含于三维投影的整个旗标。

若外部可逆对角矩阵 $\Delta=\bigoplus_i\Delta_i$ 满足 $\Delta W_{ef,K}=W_{e'f',K}$，则 (45.24) 强制 $\Delta_iN_i^f=N_i^{f'}$、$\Delta_iE_i^f=E_i^{f'}$。两个非零泛函的核相同，故存在 $s_i\in K^\times$ 使

$$
\lambda_i^{f'}\Delta_i=s_i\lambda_i^f,
\qquad
\operatorname{diag}(s_i,\Delta_i)L_i^f=L_i^{f'},
\qquad
\operatorname{diag}(s_1,\ldots,s_6)C_K^e=C_K^{e'}.
\tag{45.25}
$$

最后一式还使用 (45.23) 的接合像恰为整个 $C_K^e$，因为所有叶泛函均满射。若 $f\ne f'$，中间一式立即违反叶的对角非自对偶性，故必有 $f=f'$。

此时中间一式是统一三平面的对角稳定式。Plücker 子式坐标是标准工具，见 Devriendt–Mulas，[*Uniform density in matroids, matrices and graphs*，arXiv:2306.15267v3，§4.3](https://arxiv.org/html/2306.15267v3)；这里只用子式定义及其对角作用，不调用该文的实域密度结论。设对角条目为 $z_1,\ldots,z_6$。全部三阶 Plücker 坐标非零，故每个三元集 $I$ 的 $\prod_{j\in I}z_j$ 都等于同一个数。对任意不同的 $a,b$，选另外两个坐标组成 $J$，比较 $J\cup\{a\}$ 与 $J\cup\{b\}$，得 $z_a=z_b$。所以稳定子只有公共标量，(45.25) 给出 $\Delta_i=s_iI_5$。若 $e\ne e'$，最后一式又违反中心的对角非自对偶性，故 $e=e'$。这证明四个窗口在整个带标签分裂对角群下两两不等价；上述子式及线性独立性在扩域后保持，故结论也对 $K'$ 成立。

原 $\gamma\in D^\times$ 的乘法在 (45.14) 中是 $\operatorname{diag}(\tau(\gamma))_{\tau\in\Omega}$，其条目全部非零。因此原标量等价是刚被排除的对角等价的特例；这里不需要将任意分裂对角矩阵下降为原乘数。定理 45.2 最后给出四者的完整原标签交维相等。

白话说，每个原比例的两份窗口交叠，都先压到同一个 $E^2$ 像；中心取对偶不改直线上的交维，整个窗口取迹对偶也不改交维，所以四份完整表相同。但整体形状仍记着六个块里的二维核和三维投影：任何整体等价必须先保留这些旗标，再变成七个局部三平面的对角等价，而好条件逐一排除了改变中心或叶的可能。几何坐标负责显露这些形状，原域大胞负责保证它们确实存在于最初固定的域塔。$\square$

**命题 45.4（指定数域、先例与恢复边界）。** 令 $\theta>0$ 为 $T^{30}-2$ 的实根，取同一个实际数域塔

$$
F=\mathbb Q,\qquad E=\mathbb Q(\theta^5),\qquad
D=\mathbb Q(\theta).
\tag{45.26}
$$

此塔中存在四个十五维有理窗口，具有同一个完整带原标签交维函数，却属于四个不同的原标量轨道。它们均不满足定义 44.1 的充分条件 $\mathrm H$。对其中任意两个不同轨道，其完整共同见证三重函数 $J_W(r,s)$ 不同。

证明。$T^{30}-2$ 与 $T^6-2$ 均在素数二处满足 Eisenstein 判据，故 $[D:\mathbb Q]=30$、$[E:\mathbb Q]=6$，再由域塔公式得 $[D:E]=5$。应用定理 45.3 即得所述四个实际窗口。(45.26) 明确指定环境数域；窗口参数由 (45.20)–(45.21) 存在性选取，此处没有指定四组基向量的系数。结论给出同一完整纤维内至少四个轨道，不断言纤维恰有四个轨道，也不比较其他次数的最小性。

若其中任一窗口满足 $\mathrm H$，定理 44.2 会将其完整交维纤维限制为至多两个原标量轨道，与已经证明的四个轨道矛盾。因此四者都在该充分条件之外，这不改变定理 44.2 的假设或结论。另一方面，定理 26.2 的 (26.7) 保证任意两个不同轨道的完整 $J$ 函数不同。这里是逐对存在原标签 $(r,s)$ 的分离，不断言一对标签同时分离四者。三重交叠要求三份关系共享同一个非零元素，故它承载的联合条件并未由两两交维表给出。

与有限域文献的对应须保持这一边界。Csajbók–Marino–Polverino 的上述 Result 2.1 已有对偶逐点保权，Proposition 3.9 在 $q>4,n>4$ 给出非简单线性集；Zullo 的上述 Theorem 3.5 已联系乘积线性集权重、商与标量交叠。Pepe，[*On subspaces defining linear sets of maximum rank*，arXiv:2403.01551v2，Theorems 8、24](https://arxiv.org/html/2403.01551v2)，进一步在有限域最大秩射影直线框架下，将相同线性集联系到 Dickson 矩阵对应主子式相等，并通过子域迹项描述提升。这些是保权、非唯一表示及子域提升的重要先例，不能把一般提升想法或迹对偶重新命名为新机制。它们的 Frobenius、Dickson 矩阵和有限域假设不直接证明 (45.26) 的特征零结论，也不能从相同零集自动推出本节的全部交维。

本节的仓内综合推导将 (45.5) 的精确维数传递、两级迹对偶、七因子好开集的实际参数存在性及 (45.24) 的旗标恢复连接起来，在每个固定 $6\times5$ 特征零塔内取得四个不同原标量轨道；所引迹、线性集、Grassmannian 与 Plücker 工具各只承担证明中明确的一步。不据此作全球文献优先权判断，亦不从完整精确标签结论推出有限查询或误差下的恢复结论。$\square$

## 追加锚（本行以下为增补区）

## 46. 任意有限高度的实际域塔与同交维标量类倍增

**定义 46.1（保持原标签的归纳条件）。** 固定特征零域 $F$ 及其代数闭包 $K$。对实际有限扩张 $B/F$，始终按同一个原嵌入集合 $\Omega_B=\operatorname{Hom}_F(B,K)$ 识别 $B\otimes_F K=K^{\Omega_B}$。原标量等价只指 $U'=\gamma U$，其中 $\gamma\in B^\times$；完整函数仍为 $d_U(r)=\dim_F(U\cap rU)$，其自变量是逐字相同的原 $r\in B^\times$。若延至零，单独规定 $d_U(0)=0$。

称分裂空间 $C\le K^I$ 满足条件 $\mathcal P$，若

$$
\operatorname{pr}_i C=K,\qquad C\cap Ke_i=0\quad(i\in I),
\qquad
\operatorname{Stab}_{(K^\times)^I}(C)=\{tI:t\in K^\times\}.
\tag{46.1}
$$

三项分别是满坐标投影、无坐标轴及仅有公共标量的对角稳定子。这里的对角作用保持每一个坐标标签，不容许置换。称 $m$ 维平面 $L\le K^J$ 均匀，若其 $|J|$ 行 $m$ 列帧的全部 $m$ 阶行子式非零；下文的均匀性假设只施于三维叶平面和初始中心，不作为后续中心的归纳假设。

**定理 46.2（偶数中心次数的精确传递与对偶封闭族）。** 设实际域塔 $F\subset E\subset D$ 满足 $n=[E:F]$ 为偶数、$[D:E]=5$。令 $C\le_F E$ 为 $n/2$ 维，$V\le_E E\oplus D$ 为三维，并沿用定义 45.1 的配对、可用性和 $W(C,V)$，仅将中心维数三改为 $n/2$。则 $W(C,V)$ 为 $5n/2$ 维。对原 $r\in D^\times$，仍以 (45.4) 定义 $T_r(U),\rho_r,R_r(U),\kappa_r(U)$，其中 $U=V$ 或 $V^\perp$，有

$$
d_{W(C,U)}(r)=n\kappa_r(U)+\dim_F(R_r(U)\cap C^2),
\qquad
\dim_F(R\cap C^2)=
\begin{cases}
0,&R=0,\\
n,&R=E^2,\\
n/2,&R=E(1,0)\ \text{或}\ E(0,1),\\
d_C(u/v),&R=E(u,v),\ uv\ne0.
\end{cases}
\tag{46.2}
$$

特别地，若一个半维中心族 $\mathscr C$ 的所有成员具有相同的完整原标签 $d_C$，并且在原 $\operatorname{Tr}_{E/F}$ 正交补下封闭，则

$$
\{W(C,V),W(C,V^\perp):C\in\mathscr C\}
\quad\text{具有相同的完整原标签交维函数，}
\qquad
W(C,V)^\perp=W(C^\perp,V^\perp).
\tag{46.3}
$$

最后的正交补使用原 $\operatorname{Tr}_{D/F}$ 配对。

证明。投影 $p_E:U\to E$ 的核为二维 $E$-空间；$p_D$ 将 $p_E^{-1}(C)$ 单射到窗口，故维数为 $2n+n/2$。(45.9) 的唯一提升同构和 (45.10) 的正合列不使用 $n=6$，核的 $F$-维数改为 $n\kappa_r(U)$ 即得第一式。像的 $E$-秩只能为零、一、二；全像时 $C^2$ 的维数为 $n$，两条轴各给 $n/2$。非轴线的参数集仍为 $u^{-1}C\cap v^{-1}C$，乘以 $u$ 将它同构到 $C\cap(u/v)C$，给出最后一行。因此全部秩层、$\kappa=0$、零像、轴线和非轴线上的零交维都保留在 (46.2) 中；不存在仅比较正支持的步骤。

可分迹的非退化性和传递性沿用 (45.11)–(45.12)，也可在分裂后由坐标点积直接得到。对任意偶数次数 $N=[B:F]$ 的实际扩张及半维空间 $H\le_F B$，有 $(rH)^\perp=r^{-1}H^\perp$，从而

$$
\begin{aligned}
d_{H^\perp}(r)
&=N-\dim_F(H+r^{-1}H)
=d_H(r^{-1})=d_H(r)\qquad(r\in B^\times).
\end{aligned}
\tag{46.4}
$$

末步由乘以 $r$ 给出交叠的同构。这是 §34、引理 40.2 已用的半维迹恒等式在一般偶数次数上的同一计算。对 $(a,x)\in V$、$(b,y)\in V^\perp$，(45.12) 仍给 $\operatorname{Tr}_{D/F}(xy)=-\operatorname{Tr}_{E/F}(ab)$。取 $a\in C,b\in C^\perp$，再比较两个半维空间，便得 (46.3) 的正交补等式。

固定 $U=V$ 时，(46.2) 使 $d_{W(C,V)}$ 与 $C\in\mathscr C$ 的选择无关。相反叶选择之间使用

$$
W(C,V^\perp)=W(C^\perp,V)^\perp.
\tag{46.5}
$$

由于 $C^\perp\in\mathscr C$，右边由固定叶传递和 (46.4) 连接到同一个函数。这一步需要旧族的对偶封闭性，不能单凭固定 $U$ 的公式比较两种叶。若容许标签零，两边另外都为零；不把零代入含 $r^{-1}$ 的证明。$\square$

**引理 46.3（实际六维 étale 参数中的好叶）。** 设 $k$ 为特征零域，$A$ 为六维有限 étale $k$-代数。存在实际 $k$-三平面 $L\le_k A$，使任一分裂下的 $L$ 与其迹正交补 $L^\perp$ 都均匀、满足 $\mathcal P$，且二者不由任何可逆对角矩阵相连。特别地，对每个实际有限塔 $F\subset E\subset D$，若 $[D:E]=5$，则可在 $A=E\times D$ 中取得一个实际 $E$-三平面 $V$，它对配对 $ab+\operatorname{Tr}_{D/E}(xy)$ 可用，且沿每个原 $F$-嵌入分裂的叶均有上述性质。

证明。在 $G=\operatorname{Gr}_k(3,A)$ 上，对三平面 $L$ 内在地定义

$$
\mu_L:A\longrightarrow\operatorname{Sym}^2(L^*),\qquad
\mu_L(z)(u,v)=\operatorname{Tr}_{A/k}(zuv).
\tag{46.6}
$$

源与靶的维数都为六；这里将对称双线性型记为 $\operatorname{Sym}^2(L^*)$。局部帧下各系数都是正则函数，所以 $\mu_L$ 可逆给出定义在 $k$ 上的开集。取有限 Galois 分裂域 $k'/k$，有 $A\otimes_k k'=(k')^6$；若六个坐标在 $L$ 上的限制为 $\ell_i$，则

$$
\mu_L(z)=\sum_{i=1}^6z_i\ell_i^2.
\tag{46.7}
$$

这个可逆开集几何非空：取六个行泛函为 $x_1,x_2,x_3,x_1+x_2,x_1+x_3,x_2+x_3$。六个平方的线性关系先比较三个混合项，后三个系数因 $2\ne0$ 而为零；再比较三个平方项，前三个也为零。这些行给一个秩三帧，故确为 Grassmannian 上的一点。

均匀条件是另一个几何非空开集：六行取 $(1,t_i,t_i^2)$，其中 $t_i\in k'$ 两两不同，任取三行的 Vandermonde 行列式均非零。它定义在 $k$ 上，因为 Galois 作用只置换六个分裂坐标，保持“所有三阶子式非零”。具体在一个 $k$-有理图上，分裂子式的乘积及其全部 Galois 共轭的乘积给出 $k$ 系数多项式的非消失条件，故没有把分裂参数误当实际参数。

Grassmannian 几何不可约：秩三的六行三列矩阵构成不可约仿射空间中的非空开集，并满射到它。故上述两个几何非空开集的交 $\mathcal O$ 非空。标准图 $\mathcal B\simeq\mathbb A_k^9$ 稠密，其构造见 Stacks Project，[§27.22，Lemma 27.22.1，Tag 089R](https://stacks.math.columbia.edu/tag/089R)。于是 $\mathcal O\cap\mathcal B$ 是非空 $k$-开集，含某个非零 $k$-多项式 $P$ 的主开集。无限域上的非零多项式不在全部 $k^9$ 上消失：按变量数归纳，先使一个非零系数取非零值，再避开末变量的有限个根。因此存在 $t\in k^9$ 满足 $P(t)\ne0$，这才取得实际 $k$-平面 $L$；前面的两个帧仅证明几何非空，未承担有理点存在性。

若 $\operatorname{diag}(z_i)L=L^\perp$ 且所有 $z_i\ne0$，则 (46.7) 为零，与 $\mu_L$ 单射矛盾。反向的对角等价取逆也被排除。互补 Plücker 子式使 $L^\perp$ 同样均匀。均匀三平面有满坐标投影、无坐标轴；其对角稳定子仅为公共标量，直接复用定理 45.3 在 (45.25) 后的子式比较：全部三元集的对角条目乘积相等，比较只差一个元素的两个三元集，得任意两个条目相等。这些结论在扩域后保持。此处没有要求 $\mu_{L^\perp}$ 可逆。

对 $A=E\times D$，étale 代数迹恰给 $ab+\operatorname{Tr}_{D/E}(xy)$。均匀性使接合投影满射，向五个外坐标的投影单射；对正交补也成立，所以 $V$ 可用。上述开条件与嵌入后的基变换相容，每个实际 $E$-嵌入所得叶都满足它们。它们是同一个实际 $E$-参数的共轭叶，不能独立指定。$\square$

**引理 46.4（非均匀中心的五坐标块旗标恢复）。** 在 $K$ 上固定非空有限指标集 $I$，以及两两不交、各有五个带原标签坐标的块 $B_i$。设 $C,C'\le K^I$ 均有满坐标投影且无坐标轴，不要求均匀。对每个 $i$，设 $L_i\le K\oplus K^{B_i}$ 为引理 46.3 所得的好叶。写 $L_i^0=L_i,L_i^1=L_i^\perp$，以外部投影将其写成图形

$$
L_i^e=\{(\ell_i^e(x),x):x\in M_i^e\},\qquad
N_i^e=\ker\ell_i^e,\qquad
\dim M_i^e=3,\quad\dim N_i^e=2,
\tag{46.8}
$$

其中 $\ell_i^e$ 满射，$e\in\{0,1\}$ 是所有块共同的新位。定义

$$
\mathcal W_e(C)=
\{(x_i)_i\in\bigoplus_i M_i^e:(\ell_i^e(x_i))_i\in C\}.
\tag{46.9}
$$

则从窗口本身恢复

$$
\mathcal W_e(C)\cap K^{B_i}=N_i^e,
\qquad \operatorname{pr}_{B_i}\mathcal W_e(C)=M_i^e.
\tag{46.10}
$$

可逆对角矩阵 $\Delta=\bigoplus_i\Delta_i$ 满足 $\Delta\mathcal W_e(C)=\mathcal W_{e'}(C')$，当且仅当 $e=e'$ 且存在 $t_i\in K^\times$ 使

$$
\Delta_i=t_iI_5\quad(i\in I),\qquad
\operatorname{diag}(t_i)C=C'.
\tag{46.11}
$$

若 $C$ 另有仅含公共标量的对角稳定子，则 $\mathcal W_e(C)$ 满足 $\mathcal P$。这些断言对任意这样的中心成立，包括非均匀中心。

证明。(46.10) 第一式中，支撑在 $B_i$ 内的窗口向量，其接合像支撑在单个中心坐标上；中心无坐标轴迫使该接合像为零。反之，$N_i^e$ 中的向量用其余块为零即可提升。第二式中，给定任意 $x_i\in M_i^e$，利用中心满坐标投影，选一个中心向量的第 $i$ 项为 $\ell_i^e(x_i)$，再由其余叶泛函的满射性逐块提升。故恢复的正是二维核包含于三维投影的旗标。

任何这样的 $\Delta$ 都保持固定标签块，因而将两个恢复的旗标相互送到。比较商 $M_i^e/N_i^e$ 上的非零泛函，得到唯一 $t_i\ne0$，满足

$$
\ell_i^{e'}\Delta_i=t_i\ell_i^e,
\qquad
\operatorname{diag}(t_i,\Delta_i)L_i^e=L_i^{e'},
\qquad
\operatorname{diag}(t_i)C=C'.
\tag{46.12}
$$

最后一式使用 (46.9) 的接合像恰为整个中心。若 $e\ne e'$，中间一式违反叶的对角非自对偶性；故 $e=e'$。此时该式是叶的对角稳定式，其稳定子仅有公共标量，故 $\Delta_i=t_iI_5$，得到 (46.11)。反向对各块乘以 $t_i$，由 $\ell_i^e(t_ix)=t_i\ell_i^e(x)$ 立即给出窗口等式。

因此新窗口的对角稳定子精确等于由中心稳定子提升的块标量群；中心稳定子仅有公共标量时，新稳定子也如此。新窗口的每个外坐标投影非零，因为 (46.10) 的块投影为 $M_i^e$，而均匀叶的每行非零。若新窗口含某外坐标轴，则由 (46.10) 该轴位于 $N_i^e$，使叶 $L_i^e$ 含一个外坐标轴，违反均匀性。三项归纳条件遂全部传播。$\square$

**定理 46.5（每个固定有限塔内的逐层倍增）。** 对任意固定 $h\ge0$ 及实际特征零域塔

$$
F\subset E_0\subset E_1\subset\cdots\subset E_h,
\qquad [E_0:F]=6,\qquad [E_j:E_{j-1}]=5\ (1\le j\le h),
\tag{46.13}
$$

存在实际 $F$-子空间 $W_{j,\varepsilon}\le E_j$，$0\le j\le h$、$\varepsilon\in\{0,1\}^{j+1}$，使

$$
\begin{gathered}
\dim_F W_{j,\varepsilon}=3\cdot5^j=\tfrac12[E_j:F],\\
d_{W_{j,\varepsilon}}(r)=d_{W_{j,\varepsilon'}}(r)
\quad\bigl(r\in E_j^\times,\ \varepsilon,\varepsilon'\in\{0,1\}^{j+1}\bigr),\\
W_{j,\varepsilon}^{\perp_j}=W_{j,\mathbf1-\varepsilon},
\qquad
\langle x,y\rangle_j=\operatorname{Tr}_{E_j/F}(xy).
\end{gathered}
\tag{46.14}
$$

在同一个原嵌入集合 $\Omega_j=\operatorname{Hom}_F(E_j,K)$ 上，各 $W_{j,\varepsilon}\otimes_F K$ 满足 $\mathcal P$ 且两两不在同一可逆对角轨道。因此同一个完整原标签交维纤维中至少有 $2^{j+1}$ 个原 $E_j^\times$ 标量类；原迹正交补翻转全部 $j+1$ 位。

证明。先把引理 46.3 用于 $k=F,A=E_0$，取实际三平面 $C\le_F E_0$，置 $W_{0,0}=C,W_{0,1}=C^\perp$。引理给出分裂后的 $\mathcal P$ 和两个不同对角类，(46.4) 给出相同完整原标签函数。非退化配对给 $C^{\perp\perp}=C$，故初始一位翻转成立。

假定第 $j-1$ 层已经成立。记 $E=E_{j-1},D=E_j,n=[E:F]=6\cdot5^{j-1}$。在实际六维 $E$-代数 $E\times D$ 中用引理 46.3 选择一个 $V_j$，并对整个旧族共用此参数，定义

$$
V_j^0=V_j,\qquad V_j^1=V_j^\perp,\qquad
W_{j,(\eta,e)}=W(W_{j-1,\eta},V_j^e).
\tag{46.15}
$$

这里 $V_j^\perp$ 使用 $ab+\operatorname{Tr}_{D/E}(xy)$，$(\eta,e)$ 表示在旧位串后追加新位。定理 46.2 给出半维数和完整交维的相等；旧族的原迹对偶封闭正是 (46.5) 连接新位零与一所需的条件。其正交补公式还给出实际空间的精确等式

$$
W_{j,(\eta,e)}^{\perp_j}
=W(W_{j-1,\eta}^{\perp_{j-1}},V_j^{1-e})
=W_{j,(\mathbf1-\eta,1-e)},
\tag{46.16}
$$

所以所有旧位和新位同时翻转，而非只在标量等价意义下翻转。

为排除类碰撞，固定原标签块

$$
B_\sigma=\{\tau\in\Omega_j:\tau|_E=\sigma\},\quad
\sigma\in\Omega_{j-1},\qquad
D\otimes_F K=\bigoplus_\sigma K^{B_\sigma}.
\tag{46.17}
$$

每块大小五。$V_j$ 沿各 $\sigma$ 分裂为好叶 $L_\sigma$，相对迹配对分裂为各叶的点积，故 $V_j^\perp$ 的叶恰为 $L_\sigma^\perp$。核与像在域扩张下保持，(46.15) 分裂后正是 (46.9)，中心为 $W_{j-1,\eta}\otimes_F K$，共同新位为 $e$。

旧中心满足 $\mathcal P$，引理 46.4 因而适用。若两个新窗口对角等价，(46.12) 首先强制新位相同；随后 (46.11) 给出两个旧中心的对角等价，归纳假设再强制旧位串相同。故 $2\cdot2^j=2^{j+1}$ 个窗口两两对角不等价，且引理的传播结论使每个新窗口继续满足 $\mathcal P$。

这些新中心确实非均匀：由 (46.10) 每个五坐标块中都有二维交叠；但若 $K^{5n}$ 中的 $5n/2$ 维平面均匀，块外的 $5n-5\ge5n/2$ 个坐标含一个满秩行集，故它与该块的交只能为零。归纳依靠的是 (46.1)，并未要求新中心保持初始均匀性。

最后，原 $\gamma\in E_j^\times$ 的乘法在 (46.17) 中为 $\operatorname{diag}(\tau(\gamma))_{\tau\in\Omega_j}$，所有条目非零。分裂对角不等价遂蕴含原标量不等价，不需要将任意分裂对角元下降为原域乘数。读数相等始终由实际域中的 (46.2)–(46.5) 给出，没有对原 $r$ 作嵌入置换或域自同构。归纳完成。$\square$

**命题 46.6（指定数域族与线性集先例的精确对应）。** 对每个 $h\ge0$，令 $\theta_h=2^{1/(6\cdot5^h)}>0$，所有正根均取自 $\mathbb R$，并令

$$
D_h=\mathbb Q(\theta_h),\qquad
\theta_{h-1}=\theta_h^5\ (h\ge1).
\tag{46.18}
$$

则 $[D_h:\mathbb Q]=6\cdot5^h$，且 $[D_h:D_{h-1}]=5$（$h\ge1$）。每个固定 $D_h$ 中存在至少 $2^{h+1}$ 个 $3\cdot5^h$ 维原标量类，具有完全相同的完整原标签交维函数，并由原迹正交补配成全部位翻转。这里明确指定的是环境数域；窗口的系数由引理 46.3 的实际有理点存在性选取。这个下界随有限高度无界，不给出固定 $D_h$ 内的精确纤维大小或次数最小性。

证明。$X^{6\cdot5^h}-2$ 在素数二处满足 Eisenstein 判据，故得到所述绝对次数。兼容正根的等式给出实际包含 $D_{h-1}\subset D_h$，再用域塔公式取得相对次数五；于是对 $F=\mathbb Q,E_j=D_j$ 应用定理 46.5 即得结论。每个高度只有有限次实际参数选择，不以独立指定的分裂坐标代替这些选择。

为精确比较已有线性集语言，对任意实际 $W\le_F B$ 定义 Cartesian 平方 $U_W=W\times W\subset B^2$，在射影点上的权重为 $w_{U_W}([u:v])=\dim_F(U_W\cap B(u,v))$。于是

$$
w_{U_W}([r:1])
=\dim_F\{y\in W:ry\in W\}
=d_W(r)\qquad(r\in B^\times).
\tag{46.19}
$$

第二步由 $y\mapsto ry$ 给出；两坐标轴的权重均为 $\dim_F W$。因此本节的同交维族也给出同一完整逐点权重函数的 Cartesian 平方。且 $U_{W'}=\gamma U_W$ 当且仅当 $W'=\gamma W$，由任一坐标投影即可验证，故所计数的正是原标量定义类。

有限域中，Csajbók–Marino–Polverino，[*Classes and equivalence of linear sets in PG(1,q^n)*，arXiv:1607.06962v1，Result 2.1、Definitions 2.3–2.4](https://arxiv.org/html/1607.06962v1)，已给出迹辛对偶在射影直线固定点上的保权，并分别定义按标量和按较大半线性群计数的定义类。这里采用前一种等价关系；本节不把原标量类下界扩张为半线性类下界。Zullo 的 [arXiv:2112.08781v2，Theorem 3.5](https://arxiv.org/html/2112.08781v2) 已联系 Cartesian 乘积的点权、商集和标量交叠，(46.19) 则直接给出当前所需对应。

Van de Voorde–Zullo，[*On the weight distribution of linear sets with complementary weights and related constructions*，arXiv:2511.20057v1，§4.3、Proposition 4.7、Theorem 5.1、§5.2](https://arxiv.org/html/2511.20057v1)，明确研究 Cartesian 平方；其 Theorem 5.1 在二次有限域扩张及相应可逆性条件下给出旧、新点权的逐点传递，§5.2 迭代得到具有多种不同权重的线性集。本节的目标则是同一个完整权重函数所容许的多个标量定义类。该区别只界定这里的结论，不断言该文没有其他相关结果，也不将一般权重传递或迭代想法称为新概念。

Pepe 的 [arXiv:2403.01551v2，Theorems 8、24](https://arxiv.org/html/2403.01551v2) 分别在其有限域最大秩条件下联系同线性集与 Dickson 对应主子式，并研究中间迹项的提升；这些与 §45 所引的迹对偶、Grassmannian 和 Plücker 工具都是中间先例。本节的仓内综合推导是将偶数次数的实际传递、实际 $E$-参数和非均匀中心的旗标归纳连接为 (46.14) 的任意有限高度下界；不作全球文献优先权判断。$\square$

## 追加锚（本行以下为增补区）
## 47. 定理 42.2 的有标签归一化子式更正

**命题 47.1（归一化子式与消元）。** 设 $k$ 为特征零域，$x,y,z,u,v\in k^\times$，并令

$$
M=[\,I_4\mid A\,],\qquad
A=\begin{pmatrix}
0&1&1&x\\
1&0&1&1\\
y&z&0&1\\
u&v&1&0
\end{pmatrix}.
\tag{47.1}
$$

$M$ 的列依次标为 $1,\ldots,8$，与原嵌入标签 $0,\ldots,7$ 的对应依次为 $1,2,8,6,4,3,5,7$，即式 (42.4)。对递增列标签 $i<j<\ell<m$，记 $\Delta_{ij\ell m}=\det M[:,\{i,j,\ell,m\}]$。若 $1458,2367,4678,1567,2568,3578$ 均为非基，则

$$
y=v=z=1,\qquad x=u=2,
\tag{47.2}
$$

故 $M$ 就是式 (42.6) 的有标签表示。在定理 42.2 的证明中，$4678$ 在 $y=v=1$ 后直接给出的等式应为 $1+z-xz=0$；这替代该处直接写出的 $2-x=0$，后者须在消元得到 $z=1$ 后使用。

证明。首先，按递增列序展开给出

$$
\Delta_{1458}=1-y,\qquad \Delta_{2367}=1-v,
$$

所以 $y=v=1$。在此代入下，四个其余子式的准确符号为

$$
\begin{aligned}
\Delta_{4678}&=-(1+z-xz),\\
\Delta_{1567}&=z+1-zu,\\
\Delta_{2568}&=-\bigl(u+x(1-zu)\bigr),\\
\Delta_{3578}&=u+x(1-u).
\end{aligned}
\tag{47.3}
$$

特别地，$M$ 的第 $4$ 列为第四个标准基向量，沿 $4678$ 的第一列展开便得

$$
\Delta_{4678}
=-\det\begin{pmatrix}1&1&x\\0&1&1\\z&0&1\end{pmatrix}
=-(1+z-xz).
$$

四个非基条件因此恰好给出

$$
1+z-xz=0,\qquad z+1-zu=0,\qquad
u+x(1-zu)=0,\qquad u+x(1-u)=0.
\tag{47.4}
$$

后两个左端之差为

$$
\bigl(u+x(1-zu)\bigr)-\bigl(u+x(1-u)\bigr)=xu(1-z).
$$

由 $x,u\ne0$ 得 $z=1$；第二式随即为 $2-u=0$，第一式为 $2-x=0$。这些值也满足后两式，证明了 (47.2)。$\square$

归一化矩阵与所用非基条件见 Pendavingh–van Zwam，[*Confinement of matroid representations to subsets of partial fields*，arXiv:0806.4487v2，Theorem 4.18 的证明](https://arxiv.org/html/0806.4487v2#S4.Thmtheorem18)：HTML 式 (57)–(60) 对应 [PDF 第 25 页式 (44)–(47)](https://arxiv.org/pdf/0806.4487v2#page=25)，其第一式也写为 $1+(1-x)=0$，须以 (47.4) 的第一式替代。标准矩阵 $A_8$ 见 HTML 式 (81)、PDF 第 31 页式 (58)；Lemma 5.2 的唯一性陈述针对部分域 $\mathbb D$。这里所需的特征零域上归一化结论由上述消元直接给出。

此更正只替代定理 42.2 证明中的该步子式计算。两份表示仍共用式 (42.4) 的标签对应；转回嵌入矩阵时仍只作列基变换与逐行非零缩放。对 $W=X$ 或 $Z$，所得分裂乘数仍经式 (42.8) 的原有理线性核扩底下降到某个原 $\gamma\in D^\times$，并由四维性得到 $Y=\gamma W$；式 (42.2)–(42.3) 的前件、原标签和结论均保持原义。

## 追加锚（本行以下为增补区）

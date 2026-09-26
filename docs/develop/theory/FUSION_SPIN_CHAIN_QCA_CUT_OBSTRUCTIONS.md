# 融合自旋链 QCA 的拓扑分类：双 Fibonacci 反向平移与切口障碍

> 理论推导稿，2026-09-26；按 generic-v1 组织。本卷以 Jones–Lim 问题 6.1 为唯一主目标。本文给出固定融合链、严格有限深度局部酉电路等价关系下的反例证明稿，并构造相应的群同态值不变量。普通数学证明、已发表的输入定理、有限算术检错与 Lean 核验严格区分：本次没有 Lean 证明项，没有独立同行审定，不认领全球优先权。

核心对象是 $B=A(\mathrm{Fib},\tau)$、$A=B\otimes B$ 及右平移 $T$。本文证明稿的主要结论是

$$
\alpha=T\otimes T^{-1},\qquad
\mathrm{Ind}(\alpha)=1,\qquad
\mathrm{DHR}(\alpha)\simeq\mathrm{id},\qquad
\alpha\notin\mathrm{FDQC}(A).
\tag{QCA.1}
$$

反例的区别不在净信息流，也不在扇区名称置换，而在半链嵌入留下的相对交换子代数。对所有 $n\ge2$，相应复向量空间维数相差恰好 $1$；任何有限深度电路都必须使这些维数在足够远的尾部完全一致。第 5 节另外核对完整 DHR 编织张量作用，而不是以“没有交换粒子名字”替代这个前提。

这个结论若通过独立复核，将给问题 6.1 的一般充分性一个否定回答；它不等于完成全部融合链的 QCA 分类。本卷后续研究继续在本文件追加，不另造同目标分卷。

## 1. 对象、窗口嵌入与等价关系

### 1.1 公开问题及本卷的操作权限

Jones–Lim [JL24, §6, Question 6.1] 问 $(\mathrm{Ind},\mathrm{DHR})$ 是否完整，以及不足时还需要何种不变量。这里采用该文的严格约定：QCA 及其逆有统一有界传播；一个电路层由两两不交、长度统一有界的区间上的局部酉元给出；FDQC 是有限多个这样的层的复合。

允许电路门混合两条链。并未额外要求逐层分别保持两个张量因子。但是，门必须属于指定窗口代数的酉群；不把该代数的任意抽象自同构、交换外部范畴因子的操作或者无限深电路算作合法局部门。也不预先扩大局部可观测代数。

问题的完整性等价于

$$
\ker(\mathrm{Ind})\cap\ker(\mathrm{DHR})=\mathrm{FDQC}(A).
\tag{QCA.2}
$$

DHR 的核指完整编织酉张量自等价在酉单子自然同构意义下平凡。本文始终使用这个强条件。

### 1.2 实际窗口代数，不只保留维数

取一个已存在的酉融合范畴 $\mathcal C$，包括其结合结构，及自对偶、强张量生成对象 $X$。按 [JL24, Example 2.3] 在固定严格化中定义

$$
A_{[a,b]}=\operatorname{End}_{\mathcal C}(X^{\otimes(b-a+1)}).
$$

对于 $I=[a,b]\subset J=[c,d]$，实际嵌入是

$$
\iota_{I,J}(f)=1_X^{\otimes(a-c)}\otimes f\otimes
1_X^{\otimes(d-b)}.
\tag{QCA.3}
$$

**命题 1.1（窗口相容性）。** 这些映射是单射保单位的星同态，并满足 $\iota_{J,K}\iota_{I,J}=\iota_{I,K}$。不交窗口的像彼此对易。

**证明。** 张量积保持复合、单位及伴随。与非零对象张量的函子在酉融合范畴中忠实：可用对偶评价与余评价收回原态射，收回的正标量为对象的非零量子维数。故嵌入单射。两次在左右补单位等于一次补足单位；不交窗口中的两个态射作用于互不重叠的张量位置，交换律来自张量函子的 interchange law。证毕。

在非严格表示中，令 $U_{I,J}$ 为固定括号形式到“左补位、原窗口、右补位”的结合酉同构，将右式替换成 $U_{I,J}^{\dagger}(1\otimes f\otimes1)U_{I,J}$。结合相容性保证同一嵌入，不是逐窗口任意选一个同维矩阵代数同构；严格化与结合相容性使用 [EGNO15, §§2.8–2.9] 的标准基础。

取这个有向系统的 C*-归纳极限 $A$。本卷输入的 Fib 是完整酉融合范畴，不是仅凭 $\tau^2=1+\tau$ 就假造出来的物理范畴。

### 1.3 半链、迹与传播预算

在唯一迹的 GNS 表示中写 $M=A''$，并定义

$$
M_t=\left(\bigcup_{I\subset(-\infty,t]}A_I\right)''.
\tag{QCA.4}
$$

[JL24, Theorem 3.9、Remark 3.10] 提供本卷使用的有限指数半链因子，以及自对偶强生成情况下的关键识别

$$
M_s'\cap M_t=A_{(s,t]}\cong
\operatorname{End}_{\mathcal C}(X^{\otimes(t-s)}),\qquad s<t.
\tag{QCA.5}
$$

这是在指定 GNS 表示中的相对交换子恒等式，不只是两边增长率相同。它是外部子因子理论输入，不是本卷新证明的定理。

每个 QCA 保持唯一迹，故正常延拓到 $M$。若传播半径为 $r$，则

$$
M_{t-r}\subset\alpha(M_t)\subset M_{t+r}.
\tag{QCA.6}
$$

右侧由局部性及闭包得到，左侧对逆 QCA 使用相同论证。

## 2. 有限深度电路在切口处的严格局部化

### 2.1 适用对象不限于标准半链

称 $P\subset M$ 为有限切口带内的半链型子因子，若存在有限整数 $a\le b$ 使

$$
M_a\subset P\subset M_b.
\tag{QCA.7}
$$

这个类包含 $M_0$ 和每个 $\alpha(M_0)$。以下引理处理整个类，因而也处理在另一个 QCA 之后追加电路的情形。

**引理 2.1（一个电路层的切口局部化）。** 若 $\gamma$ 是区间长度至多 $w$ 的一个电路层，且 $P$ 满足式（QCA.7），则存在 $u\in\mathcal U(A_{[a-w,b+w]})$，使 $\gamma(P)=uPu^{\dagger}$。

**证明。** 将本层的互不相交门区间分为三类。完全位于 $(-\infty,a]$ 的门属于 $M_a\subset P$，它们的内自同构保持 $P$。完全位于 $(b,\infty)$ 的门与 $P\subset M_b$ 对易。其余门只有有限多个，并全部包含在 $[a-w,b+w]$ 中；令它们的乘积为 $u$。

这里不能把无限多个左侧门的乘积直接写成一个属于 $P$ 的酉元。正确的处理是：对左侧门取有限子集，其酉乘积确实属于 $P$，其共轭保持 $P$。在每个局部算符上，这些共轭最终稳定为该子层的作用；由迹保持及局部代数在 $L^2(M)$ 中的稠密性，它们在任意有界算符上依迹二范数收敛，因而强收敛。$P$ 强闭，故整个左子层把 $P$ 映入 $P$；对逆子层再用一次论证得等号。右子层同样正常延拓为对 $P$ 恒等。三类子层彼此交换，于是只剩有限乘积 $u$ 的共轭。证毕。

**引理 2.2（任意有限深度与显式支撑预算）。** 设 $\gamma=\gamma_d\cdots\gamma_1$，第 $j$ 层区间长度至多 $w_j$，$W=\sum_{j=1}^d w_j$。若 $P$ 满足式（QCA.7），则存在

$$
u\in\mathcal U(A_{[a-W,b+W]}),\qquad \gamma(P)=uPu^{\dagger}.
\tag{QCA.8}
$$

**证明。** 对固定的 $P$ 分别由引理 2.1 取 $u_j$，满足 $\gamma_j(P)=u_jPu_j^{\dagger}$。复合两个层时，实现酉元为 $\gamma_2(u_1)u_2$；归纳得到

$$
u=\gamma_d\cdots\gamma_2(u_1)\,
\gamma_d\cdots\gamma_3(u_2)\cdots\gamma_d(u_{d-1})u_d.
$$

每个 $\gamma_j$ 将局部支撑至多扩大 $w_j$。所有因子都落在式（QCA.8）的同一有限区间，乘积也在其中。证毕。

该预算只依赖电路自身及切口带，不随后来选取的窗口长度 $n$ 增长。没有在不同窗口中重新选择越来越宽的“电路”。

### 2.2 电路必须保持切口尾部的代数

**推论 2.3（相对交换子尾部障碍）。** 对任意 $\gamma\in\mathrm{FDQC}(A)$，存在 $N$，使全部 $n\ge N$ 都有保迹星同构

$$
M_{-n}'\cap\gamma(M_0)\cong M_{-n}'\cap M_0.
\tag{QCA.9}
$$

这些同构还与 $n\mapsto n+1$ 的包含相容。

**证明。** 引理 2.2 给出 $\gamma(M_0)=uM_0u^{\dagger}$，其中 $u$ 支撑于 $[-W,W]$。对所有 $n>W$，$u$ 与 $M_{-n}$ 对易，故同一个 $\operatorname{Ad}_u$ 在每层给出所需同构。它保迹且不随 $n$ 改变，因此包含方块相容。证毕。

有限几个小窗口出现差异不能单独排除任意宽门的电路；证明需要差异存在于任意远的尾部。第 6 节给出的正是后一种障碍。

## 3. 从可计算诊断到真正的群同态值不变量

### 3.1 切口相对交换子图的尾部

对半链型 $P$ 定义

$$
R_P(n)=M_{-n}'\cap P
\quad\text{以及}\quad
R_P(n)\hookrightarrow R_P(n+1),
\tag{QCA.10}
$$

其中 $n$ 取足够大，使 $M_{-n}\subset P$。由于 $P\subset M_b$，式（QCA.5）保证每个 $R_P(n)$ 有限维。保留代数、限制迹和实际包含，得到一个有向图；允许删去有限个初始层，但同构须在相同 $n$ 上且与包含相容。称之为尾部图。维数序列的尾部是它的一个较弱读数。

**命题 3.1（局部共轭与左右电路不变性）。** 若 $Q=uPu^{\dagger}$，其中 $u$ 为严格局部酉元，则 $P,Q$ 有相同尾部图。因此 $R_{\alpha(M_0)}$ 的尾部图及其维数尾部均在 $\alpha$ 的左、右 FDQC 复合下不变。

**证明。** 充分向左取 $-n$ 后，$u$ 与 $M_{-n}$ 对易，使用与推论 2.3 相同的共轭。左复合时对 $P=\alpha(M_0)$ 用引理 2.2。右复合时，若 $\gamma(M_0)=vM_0v^{\dagger}$，则

$$
(\alpha\gamma)(M_0)=\alpha(v)\alpha(M_0)\alpha(v)^{\dagger};
$$

$\alpha(v)$ 仍严格局部。证毕。

这个诊断没有被证明可乘，也不被叫作一个新的数值指数。特别地，第 6 节的维数序列对正、反方向的反向平移给相同数值，不能凭这个序列直接恢复方向。

### 3.2 切口类上的群作用

令 $\mathscr H_A$ 为满足式（QCA.7）的全部子因子的集合。以严格局部酉共轭定义等价关系 $\sim_{\mathrm{loc}}$。局部酉的乘积及逆仍局部；局部共轭之后仍可扩大 $[a,b]$ 保持式（QCA.7），所以这个商有定义。

**定理 3.2（切口作用不变量）。** 下式定义群同态

$$
\Theta_A:\mathrm{QCA}(A)\longrightarrow
\operatorname{Sym}(\mathscr H_A/\!\sim_{\mathrm{loc}}),
\qquad
\Theta_A(\alpha)[P]=[\alpha(P)],
\tag{QCA.11}
$$

并且 $\mathrm{FDQC}(A)\subset\ker\Theta_A$。

**证明。** 式（QCA.6）保证 QCA 把半链型子因子送到同类对象。若 $Q=uPu^{\dagger}$，则 $\alpha(Q)=\alpha(u)\alpha(P)\alpha(u)^{\dagger}$，且 $\alpha(u)$ 严格局部，所以作用在商上良定义。逆 QCA 给出逆置换，复合律直接给群同态。引理 2.2 对每一个 $P\in\mathscr H_A$ 都成立，故任意 FDQC 在整个商集合上恒等。证毕。

这符合 [JL24, §6] 对拓扑不变量的群同态定义，而不是仅给一个任意集合值标签。构造所取的商是子因子的严格局部酉共轭，不是先把 QCA/FDQC 本身重新命名。尾部图提供无需解决整个共轭判定就能检测某些不同切口类的具体手段。

本文不证明 $\Theta_A$ 是完整不变量，也不证明它能压缩成有限个易计算数值。区分一个例子只需证明 $\Theta_A(\alpha)[M_0]\ne[M_0]$。

## 4. Fibonacci 精确数据与双链反向平移

### 4.1 量子维数和算符代数维数不是同一个数

在 Fib 中，$\tau\otimes\tau\cong\mathbf1\oplus\tau$，正量子维数满足 $d_\tau^2=1+d_\tau$，故 $d_\tau=\varphi=(1+\sqrt5)/2$。另一方面，窗口可观测代数的复向量空间维数是一个整数。

取 $F_0=0,F_1=1$。

**命题 4.1（有限融合空间）。** 对 $n\ge1$，

$$
\tau^{\otimes n}\cong F_{n-1}\mathbf1\oplus F_n\tau,
\qquad
\operatorname{End}(\tau^{\otimes n})
\cong M_{F_{n-1}}(\mathbb C)\oplus M_{F_n}(\mathbb C),
$$

其中零大小的块省略。因此

$$
D(n):=\dim_{\mathbb C}\operatorname{End}(\tau^{\otimes n})
=F_{n-1}^2+F_n^2=F_{2n-1}.
\tag{QCA.12}
$$

**证明。** 张量乘以 $\tau$ 将重数向量 $(a,b)$ 变成 $(b,a+b)$；从 $(0,1)$ 归纳得到分解。半单性和简单对象间 Hom 为零给矩阵块。Fibonacci 加法式 $F_{r+s}=F_{r-1}F_s+F_rF_{s+1}$ 可由递推归纳；取 $r=n,s=n-1$ 得最后等式，$n=1$ 直接检查。证毕。

**命题 4.2（精确偏移恒等式）。** 对整数 $k$ 及 $n>|k|$，

$$
D(n+k)D(n-k)-D(n)^2=F_{2|k|}^2.
\tag{QCA.13}
$$

**证明。** 对正奇数 $m$，Binet 式为 $F_m=(\varphi^m+\varphi^{-m})/\sqrt5$。令 $a=\varphi^{2n-1}, b=\varphi^{2k}$，左式等于

$$
\frac{(ab+a^{-1}b^{-1})(ab^{-1}+a^{-1}b)
-(a+a^{-1})^2}{5}
=\frac{(b-b^{-1})^2}{5}=F_{2|k|}^2.
$$

$k=0$ 也成立。Binet 式本身由递推的两个特征根及初值验证。证毕。

这些 Fibonacci 恒等式是已有基础数学；本卷的研究结论在于将它们接入真实切口代数与 FDQC 必要条件，而非认领数列恒等式的新颖性。

### 4.2 产品网与半链

取 $B=A(\mathrm{Fib},\tau)$，其半链记为 $N_t$。Deligne 乘积的 Hom、复合和伴随按因子分解，所以实际的网同构是

$$
A(\mathrm{Fib}\boxtimes\mathrm{Fib},\tau\boxtimes\tau)_I
\cong B_I\otimes B_I.
\tag{QCA.14}
$$

这个同构与式（QCA.3）的左右补单位嵌入相容；同窗口的乘积系统在独立窗口乘积系统中共尾。因此全局准局部代数为 $A=B\otimes_{\min}B$，其迹为乘积迹，半链为

$$
M_t=N_t\,\overline\otimes\,N_t.
$$

$X=\tau\boxtimes\tau$ 自对偶，$X^{\otimes2}=(\mathbf1\oplus\tau)\boxtimes(\mathbf1\oplus\tau)$ 包含四个简单对象，故确属原问题允许的强张量生成情形。

令 $T$ 为把区间向右平移一格的网自同构。定义

$$
\alpha_k=T^k\otimes T^{-k},\qquad k\in\mathbb Z.
\tag{QCA.15}
$$

每个因子的窗口像都包含于统一扩大 $|k|$ 的窗口，逆同样成立，故这是真正的 QCA，而非仅在有限链上定义的置换。其半链像为

$$
\alpha_k(M_0)=N_k\,\overline\otimes\,N_{-k}.
\tag{QCA.16}
$$

### 4.3 指数计算

[JL24, Proposition 4.1] 给出 $\mathrm{Ind}(T)=\varphi$。由定义及半链塔可得 $[N_t:N_s]=\varphi^{2(t-s)}$。有限指数的空间张量积指数相乘：其标准 $L^2$ 模是两个标准模的外张量积，维数为乘积。

因此对 $n>|k|$，

$$
[\alpha_k(M_0):M_{-n}]
=\varphi^{2(n+k)}\varphi^{2(n-k)}
=\varphi^{4n}=[M_0:M_{-n}],
$$

从 Jones–Lim 的平方根比值定义得到

$$
\mathrm{Ind}(\alpha_k)=1.
\tag{QCA.17}
$$

这里计算的是 Jones 指数，不把 $D(n)$ 的复向量空间维数直接当作 Jones 指数。

## 5. 完整 DHR 作用的乘积相容性

### 5.1 不能只检查简单对象的名字

本节补足反例中最容易漏掉的前提。引用 [J24, Theorems 3.4、3.15、4.19]：QCA 通过扭转双模作用诱导编织酉张量自等价；融合链的 DHR 范畴与其融合范畴的 Drinfeld 中心等价。以下乘积相容性不是把两张数值表相乘。

**引理 5.1（融合链的 DHR 外张量相容性）。** 对两条满足上述自对偶强生成条件的融合链 $A_1,A_2$，存在由双模外张量积给出的编织酉等价

$$
E:\mathrm{DHR}(A_1)\boxtimes\mathrm{DHR}(A_2)
\simeq\mathrm{DHR}(A_1\otimes A_2).
\tag{QCA.18}
$$

对 QCA $\beta_i$，在包含张量子和编织的意义下，

$$
(\beta_1\otimes\beta_2)_* E
\simeq E(\beta_{1*}\boxtimes\beta_{2*}).
\tag{QCA.19}
$$

**证明。** 先核对 $E$ 的满性，而不是仅构造一些乘积扇区。对 $q=b-a+1$，Jones 的 AF 双模模型 [J24, §4.2, printed pp.35–36] 在有限层写成

$$
F^r_{a,b}(Z,\sigma)
=\mathcal C(X^{\otimes(2r+q)},
X^{\otimes(r+q)}\otimes Z\otimes X^{\otimes r}).
\tag{QCA.20}
$$

在 $\mathcal C=\mathcal C_1\boxtimes\mathcal C_2$、$X=X_1\boxtimes X_2$、$Z=Z_1\boxtimes Z_2$ 下，式（QCA.20）恰为两个有限层空间的外张量积。内积由 $f^{\dagger}g$ 给出，右作用由预复合给出，左作用及张量子由半编织与复合给出；这些运算全部按两因子分解。扩展映射 $f\mapsto1_X\otimes f\otimes1_X$ 同样分解。故在共尾的相同窗口上取归纳极限，得到 Jones 实现函子与双模外张量积的相容。

使用标准中心乘积等价 $\mathcal Z(\mathcal C_1\boxtimes\mathcal C_2)\simeq\mathcal Z(\mathcal C_1)\boxtimes\mathcal Z(\mathcal C_2)$：外积半编织逐因子给出；Hom 的两套半编织约束分别作用，故该函子全忠实；由 [EGNO15, Theorem 7.16.6]，中心的 Frobenius–Perron 维数等于原范畴维数的平方。Deligne 乘积的维数相乘，故这个全忠实函子的像与目标维数相同，在半单情形于是本质满。结合 [J24, Theorem 4.19] 的中心实现等价，式（QCA.18）本质满且全忠实。没有遗漏一个仅因因子分开观察而看不见的“混合扇区”。

再核对 QCA 作用。Jones 的扭转定义在原双模向量空间上为

$$
a\triangleright_{\beta}\xi\triangleleft_{\beta}b
=\beta^{-1}(a)\xi\beta^{-1}(b),
\qquad
\langle\xi,\eta\rangle_{\beta_*H}
=\beta(\langle\xi,\eta\rangle_H).
\tag{QCA.21}
$$

把 $a,b,\xi,\eta$ 都取为纯张量，式（QCA.21）逐项等于两个分别扭转的双模的外张量积。其张量子在平衡张量积的简单向量上是同一个恒等重排；外积的张量子把 $(\xi_1\otimes\xi_2)\boxtimes(\eta_1\otimes\eta_2)$ 送到 $(\xi_1\boxtimes\eta_1)\otimes(\xi_2\boxtimes\eta_2)$，也与扭转相容。选取左右分离的局部化基时，DHR 编织按两个因子分解。完成化、有限直和及子对象不改变这些等式。故式（QCA.19）是完整编织酉单子函子的相容，而非简单对象层面的相容。证毕。

**命题 5.2（反向平移的完整 DHR 平凡性）。** 对式（QCA.15）的每个 $k$，$\mathrm{DHR}(\alpha_k)\simeq\mathrm{id}$。

**证明。** [JL24, §6] 明确指出 $\operatorname{Aut}_{br}(\mathcal Z(\mathrm{Fib}))$ 为平凡群。这个群已按酉单子自然同构取等价类。因此 $(T^k)_*$ 和 $(T^{-k})_*$ 各有完整酉单子自然同构 $\eta^+,(\eta^-)$ 到恒等函子。通过引理 5.1，在外积对象上的同构取 $\eta^+_{H_1}\otimes\eta^-_{H_2}$。张量子、单位和编织的相容由同一引理及两个 $\eta$ 的相容性得到；由 $E$ 本质满，延拓到全部 DHR 对象。证毕。

双 Fib 的中心本身可以有交换等价因子等非平凡自等价；本证明没有声称其全部自等价群平凡。这里仅证明特定的独立反向平移作用平凡。

## 6. 双 Fibonacci 反例及不可局部消去的精确差异

**引理 6.1（乘积相对交换子）。** 对空间张量积中的包含 $P_i\subset Q_i$，

$$
(P_1\overline\otimes P_2)'\cap(Q_1\overline\otimes Q_2)
=(P_1'\cap Q_1)\overline\otimes(P_2'\cap Q_2).
\tag{QCA.22}
$$

**证明。** 与 $P_1\otimes1$ 对易的元素，其全部第二因子正常切片都属于 $P_1'\cap Q_1$，因此落在 $(P_1'\cap Q_1)\overline\otimes Q_2$。再对 $1\otimes P_2$ 使用同一切片判据得到右式。反包含逐纯张量直接验证并取弱闭包。证毕。

**定理 6.2（反向平移的切口障碍）。** 对 $A=A(\mathrm{Fib}\boxtimes\mathrm{Fib},\tau\boxtimes\tau)$ 和任意非零整数 $k$，

$$
\mathrm{Ind}(\alpha_k)=1,\qquad
\mathrm{DHR}(\alpha_k)\simeq\mathrm{id},\qquad
\alpha_k\notin\mathrm{FDQC}(A).
\tag{QCA.23}
$$

另外，$\Theta_A(\alpha_k)[M_0]\ne[M_0]$。

**证明。** 前两个等式分别是式（QCA.17）与命题 5.2。由式（QCA.5）、式（QCA.16）及引理 6.1，所有 $n>|k|$ 都有

$$
\begin{aligned}
R_{M_0}(n)&\cong\operatorname{End}(\tau^{\otimes n})
\otimes\operatorname{End}(\tau^{\otimes n}),\\
R_{\alpha_k(M_0)}(n)&\cong\operatorname{End}(\tau^{\otimes(n+k)})
\otimes\operatorname{End}(\tau^{\otimes(n-k)}).
\end{aligned}
\tag{QCA.24}
$$

因而

$$
\dim_{\mathbb C}R_{\alpha_k(M_0)}(n)
-\dim_{\mathbb C}R_{M_0}(n)=F_{2|k|}^2>0.
\tag{QCA.25}
$$

若 $\alpha_k$ 是 FDQC，推论 2.3 强制两维数对所有充分大的 $n$ 相同，与式（QCA.25）矛盾。若两个半链型子因子严格局部酉共轭，命题 3.1 同样强制尾部维数一致，故 $\Theta_A(\alpha_k)$ 确实移动 $[M_0]$。证毕。

对于 $k=1$，差值恒为 $1$。最初几项是：

| 窗口参数 $n$ | 恒等演化的切口代数维数 | 反向平移的切口代数维数 | 差值 |
| --- | ---: | ---: | ---: |
| 2 | 4 | 5 | 1 |
| 3 | 25 | 26 | 1 |
| 4 | 169 | 170 | 1 |
| 5 | 1156 | 1157 | 1 |
| 6 | 7921 | 7922 | 1 |

表格不是无限链证明；式（QCA.25）才使论证不依赖电路门宽的未知上限。这是算符代数的复维数差，不是“额外一个量子比特”或“额外一个粒子”的结论。

当 $n\to\infty$，这个固定差值除以 $D(n)^2$ 趋于零。因而只保留主导增长率会丢掉本例的障碍。指数的精确计算已在第 4.3 节独立给出；这里的增长率观察只解释为什么很小的次阶离散差异仍能阻止严格局部实现。

## 7. 不止一个例子：无穷阶与多层格

**推论 7.1（联合核中的无穷循环子群）。** $k\mapsto[\alpha_k]$ 给出

$$
\mathbb Z\hookrightarrow
\frac{\ker\mathrm{Ind}\cap\ker\mathrm{DHR}}{\mathrm{FDQC}(A)}.
\tag{QCA.26}
$$

$\Theta_A(\alpha_1)$ 也有无穷阶。

**证明。** $\alpha_k\alpha_l=\alpha_{k+l}$。任意非零 $k$ 由定理 6.2 非平凡，故该群同态单射。若 $\Theta_A(\alpha_1)$ 有有限阶，某个非零幂必须固定全部切口类，特别固定 $[M_0]$，再次与定理 6.2 矛盾。证毕。

**定理 7.2（多条 Fibonacci 链的平移格）。** 在 $A_m=B^{\otimes m}$，$m\ge2$，定义

$$
\alpha_{\mathbf k}=\bigotimes_{i=1}^mT^{k_i},
\qquad\mathbf k\in\mathbb Z^m.
$$

则 $\mathbf k\mapsto[\alpha_{\mathbf k}]$ 将 $\mathbb Z^m$ 单射到 $\mathrm{QCA}(A_m)/\mathrm{FDQC}(A_m)$。在这个显式平移子群上，指数为 $\varphi^{\sum_i k_i}$，DHR 作用平凡，故联合核包含 $\mathbb Z^{m-1}$。

**证明。** 产品指数与第 5 节的归纳应用给前述两项不变量。若 $\sum_i k_i\ne0$，指数排除 FDQC。若和为零但 $\mathbf k\ne0$，选 $n>\max_i|k_i|$，切口代数维数分别为 $\prod_iD(n+k_i)$ 与 $D(n)^m$。

令 $c=\log\varphi$，将整数上的 $D$ 延拓为正函数

$$
D(t)=\frac{2}{\sqrt5}\cosh((2t-1)c),\qquad t>0.
$$

其对数严格凸，因为

$$
\frac{d^2}{dt^2}\log D(t)
=4c^2\operatorname{sech}^2((2t-1)c)>0.
$$

各 $n+k_i$ 的平均为 $n$，且不全相同，故严格 Jensen 不等式给 $\prod_iD(n+k_i)>D(n)^m$。这个差异对任意足够大的 $n$ 成立，推论 2.3 排除 FDQC。对两个向量的差再用同一论证，得到单射；零和整格同构于 $\mathbb Z^{m-1}$。证毕。

这里分类的是指定平移子群，不声称整个多 Fib QCA 群就是 $\mathbb Z^m$，也没有把不同层的置换或其他范畴自等价遗漏后宣布完整分类。

**推论 7.3（普通有限维静止辅助链不能消去本障碍）。** 对任意固定有限 $q\ge1$，张量一个每格为 $M_q(\mathbb C)$ 的普通链 $C_q$，取 $\alpha_k\otimes\mathrm{id}_{C_q}$。当 $k\ne0$ 时，这仍不是扩大后的指定代数网上的 FDQC。

**证明。** 辅助半链的长度 $n$ 相对交换子为 $M_{q^n}(\mathbb C)$，复维数 $q^{2n}$。式（QCA.25）的差值因此变成 $q^{2n}F_{2|k|}^2$，对每个充分大 $n$ 仍严格为正。引理 2.2 允许扩大后的局部门任意混合三个因子，所以结论并未限制辅助链只能旁观。证毕。

这不涉及无限维局部 Hilbert 空间、替换融合对称性或其他未声明的稳定化等价关系。

## 8. 与既有运输、共同实现及预测理论的精确接口

### 8.1 运输卷的“数学可逆”与“允许执行”

本轮读取的 [运输、任务记忆与完成化卷](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) 第 1 章区分形式逆运输和实际操作权限，并用保持共同参考的换基判断相位场。

本卷的对应对象不是一个任意图上的标量相位，而是窗口代数网及其嵌入；允许的消去不是任意全局同构，而是指定代数内的有界深度酉门。式（QCA.8）将“合法局部操作”落实成一个可检验必要条件。式（QCA.25）给出违反该条件的严格对象。

因此，可复用的是组织证明的接口：先固定对象和合法变换，再寻找其不变量。运输卷的生成树相位定理本身并不推出这里的 von Neumann 相对交换子定理；后者由本卷的切口引理和 [JL24] 的真实子因子输入承担。

### 8.2 预测卷的交换方块与本卷的额外可实现性问题

[统一预测几何主卷 §2，PR #8891 的固定提交](https://github.com/the-omega-institute/trureturing/blob/81a2dcedc3ffcda89cc1fd5b3d150773f44e2b35/docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md) 使用 $OA=KO$ 表达观察与演化的相容，并进一步保留提升与能量结构。

这里把相容性写在真实局部代数上：若 $\alpha_I:A_I\to A_{I^{+r}}$ 是同一 QCA 的限制，则

$$
\alpha_J\iota_{I,J}
=\iota_{I^{+r},J^{+r}}\alpha_I.
\tag{QCA.27}
$$

这与预测卷的交换方块具有相同的组织形式，但载体、映射种类及证明前提不同。反向平移满足式（QCA.27），也满足完整 DHR 平凡和指数抵消，却仍不在合法局部门生成的群里。

因而这里补出的严格区别是：相容的全局自同构已经存在，不代表存在有限深度的局部酉实现。它不是“每个有限维矩阵都能求逆”的问题，更不是从 $OA=KO$ 直接推出 QCA 分类。

### 8.3 物理解释与不能跳过的边界

在该固定融合边界上，两条相反的信息流抵消后，切口附近仍保留不同的融合通道代数组织。$\Theta_A$ 记录半链子因子在实际全局代数中的局部酉共轭类型；相对交换子图是它的一个离散诊断。它比仅保留净流量更细，也不是再次给 DHR 扇区改名。

融合链与拓扑系统边界的联系属于 [JL24、JSW26] 的既有物理背景。本卷没有证明引力 RT 面积公式、构造连续时空或统一相对论与量子力学。返回 RT 研究的可复用内容，是检查边界变换是否具有共同局部实现的一个严格障碍，而非把这个障碍改名为面积。

黄金比例在这里由融合维数强制产生；真正用于否定证明的是融合空间重数和实际嵌入。相同的二次多项式本身不建立与黄金编码、WSS 算术或其他项目主张的推论关系。

## 9. 文献覆盖、证明复核点与剩余问题

### 9.1 与已知分类结果的范围比较

[JL24] 的单条 $A(\mathrm{Fib},\tau)$ 分类不涵盖本卷的乘积范畴。[JSW26, Corollary 1.4] 的完整性结论针对有限群的正则表示，并保留一般融合链分类问题；本例不是该正则群表示情形。[Z23] 已提醒强等价、稳定等价与附加对称不变量之间的区别，因此本卷不认领“限制局部门可能产生额外不变量”这个一般思想的优先权。

[BJ26] 的无限维局部 Hilbert 空间和稳定局域等价采用不同操作环境，不是本卷固定有限窗口代数上的 FDQC 结论。不能用其中的等价关系替换式（QCA.2）。

截至 2026-09-26 的本轮定向检索，没有检出与本卷式（QCA.23）及切口证明相同的已发表结论；这不是穷尽检索或全球首次证明的证书。

### 9.2 独立复核应攻击的具体环节

| 复核对象 | 本卷的依据 | 不能用什么替代 |
| --- | --- | --- |
| 电路定义与支撑预算 | 第 1.1 节、引理 2.1–2.2 | 允许深度随窗口增长的电路 |
| 无限门作用在半链上的闭包 | 引理 2.1 的迹二范数与强闭性论证 | 形式书写一个不存在的无限酉乘积 |
| 相对交换子识别 | [JL24, Remark 3.10]，原文 printed pp.8–9 | 仅凭窗口代数维数猜测半链交换子 |
| 全部 DHR 扇区及张量子 | 引理 5.1、命题 5.2；[J24, §4.2] | 仅验证简单对象名称或融合表 |
| 无限尾部的维数差 | 命题 4.2、定理 6.2 | 表格或有限次数值实验 |
| 新不变量的群同态性质 | 定理 3.2 | 未证明可乘的一个标量序列 |
| 新颖性与学界地位 | 本轮定向文献比较，待外部审定 | 把本仓普通证明稿称为已发表定论 |

本次没有独立模型评审、Lean 编译、Scribe 发射、消化结算或 CI 通过声明。已有文献的子因子与 DHR 定理未在仓内重新形式化；不能因这份理论正文存在就视为机器真值。

### 9.3 更窄而真实的下一问题

定理 6.2 针对原来两个不变量的不足；它没有证明 $\Theta_A$ 的完备性。后续应研究切口尾部图中哪些数据能压缩成有限、可计算的不变量，以及这些数据一致时是否能构造统一有界、彼此相容的切口酉元，最终拼成电路。

对一般 QCA，单个切口存在某个共轭、所有切口各自存在共轭，以及存在统一支撑预算且能拼合的共轭族，是三个不同要求。任何新的充分性定理必须分别处理它们。也应比较本卷的切口数据与标准不变量、双模及已有对称保护指数的关系，而非只给同一障碍增加新名字。

## 10. 参考文献与精确使用位置

[JL24] Corey Jones and Junhwi Lim, *An index for quantum cellular automata on fusion spin chains*, Annales Henri Poincaré 25 (2024), 4399–4422. [arXiv:2309.10961v2](https://arxiv.org/pdf/2309.10961v2), [DOI](https://doi.org/10.1007/s00023-024-01429-y). 使用 Example 2.3、Definitions 2.4–2.5、Theorem 3.9、Remark 3.10、Proposition 4.1 和 §6。本文的 printed 页码按 arXiv v2；相对交换子原式位于 printed p.9，问题位于 printed p.17。

[J24] Corey Jones, *DHR bimodules of quasi-local algebras and symmetric quantum cellular automata*. [arXiv:2304.00068](https://arxiv.org/pdf/2304.00068), Quantum Topology. 使用 Theorems 3.4、3.15、4.19，Corollary 4.22，以及 §4.2 printed pp.35–36 的实际 AF 双模与张量子公式。本文对乘积网的相容推导在第 5 节，不冒充原文中已经声明了本卷反例。

[EGNO15] Pavel Etingof, Shlomo Gelaki, Dmitri Nikshych and Victor Ostrik, *Tensor Categories*, Mathematical Surveys and Monographs 205, American Mathematical Society, 2015. [作者获准公开的终稿](https://math.mit.edu/~etingof/egnobookfinal.pdf). 使用 §§2.8–2.9 的严格化与结合相容性、§4.6 的 Deligne 乘积基础及 Theorem 7.16.6（printed p.168）的中心 Frobenius–Perron 维数公式。

[JSW26] Corey Jones, Kylan Schatz and Dominic J. Williamson, *Quantum Cellular Automata and Categorical Dualities of Spin Chains*, Communications in Mathematical Physics 407, article 66 (2026), published 9 March 2026. [期刊全文](https://link.springer.com/article/10.1007/s00220-026-05571-y), [arXiv:2410.08884](https://arxiv.org/abs/2410.08884). 使用 Corollary 1.4 的有限群正则表示范围及引言的未决范围；2026 期刊版本与 2025 arXiv v3 的版本日期不混淆。

[Z23] Carolyn Zhang, *Note on quantum cellular automata and strong equivalence*, [arXiv:2306.03171](https://arxiv.org/abs/2306.03171), first submitted 5 June 2023. 仅用于强等价、稳定等价与已有附加对称不变量的范围比较，不作为双 Fib 反例的证明。

[BJ26] Ian Bunner and Corey Jones, *Universal fusion category symmetries on tensor products of infinite-dimensional Hilbert spaces*, [arXiv:2605.21327](https://arxiv.org/abs/2605.21327), 20 May 2026. 本轮使用摘要层面的模型与等价关系范围，不依赖其未在本轮逐项复核的证明。

## 11. 可复现算术检错

配套程序：[`verify.py`](../../reports/fusion-qca-cut-obstruction/verify.py)；输出：[`results.json`](../../reports/fusion-qca-cut-obstruction/results.json)。执行：

```bash
python docs/reports/fusion-qca-cut-obstruction/verify.py
```

本次实际以 Python 任意精度整数运行 7302 个参数案例：150 个窗口维数公式、5730 个正负偏移恒等式、972 个多层零和平移严格不等式、450 个有限维普通辅助链缩放等式，全部通过。多层检查包含 486 个不同非零零和向量，每个用两个窗口检验。结果只是有限算术检错；任意 $n$ 的证明在正文。程序不验证 von Neumann 代数、DHR 自然同构或 FDQC 排除引理。

## 追加锚（本行以下为增补区）

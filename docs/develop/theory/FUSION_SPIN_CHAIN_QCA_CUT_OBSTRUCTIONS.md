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

## 12. 从“遗传树”到有限融合空间：对象与实际嵌入

本批日期为 2026-09-27，接续原 PR #10310。研究时读取 dev `4ee641fd06f6475715eef02ecf4e817e401a3012`，修改基点为本 PR 的 `a9a5771cc061b8a4d806036dba9a5e4ddc6fac6d`。以下“树”均指有序融合树或带标签路径；不假设生物遗传过程与量子动力学等价。全部新增结论给出普通数学证明，尚未 Lean 核验；原第 6 节反例的独立审定状态不因本批有限矩阵推导而升级。

### 12.1 类型、合法路径与密度矩阵

**定义 12.1（融合类型与路径）。** 令 $L=\{\mathbf1,\tau\}$，允许输出集合为

$$
\mathsf N(\mathbf1,a)=\mathsf N(a,\mathbf1)=\{a\},\qquad
\mathsf N(\tau,\tau)=\{\mathbf1,\tau\}.
\tag{FT.1}
$$

对 $n\in\mathbb N$、$c\in L$，定义有限集合

$$
\mathsf P_n(c)=\{x:\{0,\ldots,n\}\to L:
 x_0=\mathbf1,\ x_n=c,\ x_{j+1}\in\mathsf N(x_j,\tau)\ (0\le j<n)\}.
\tag{FT.2}
$$

$\tau$ 是每片叶的类型，$x_j$ 是前 $j$ 片叶的总类型。$n=0$ 时只有终点为 $\mathbf1$ 的空路径。编码 $\mathbf1\mapsto0,\tau\mapsto1$ 后，合法路径具有固定起点、固定终点且相邻位置不出现 $00$；这是路径集合的双射，不携带振幅、结合结构或空间操作权限。

令 $H_n^c=\mathbb C^{\mathsf P_n(c)}$，内积为有限求和，标准基记 $|p\rangle$。令 $H_n=\bigoplus_c H_n^c$，并取保持终点类型的块对角代数

$$
\mathfrak A_n=\bigoplus_{c:\mathsf P_n(c)\ne\varnothing}\operatorname{End}_{\mathbb C}(H_n^c)
\subset\operatorname{End}_{\mathbb C}(H_n).
\tag{FT.3}
$$

$n=0$ 时 $\mathfrak A_0=\mathbb C$。这个有限模型与既定 Fib 范畴的 $\operatorname{End}(\tau^{\otimes n})$ 通过选定的正交融合基对应；该对应使用 [TTWL09] 的完整 $F$ 数据，不能仅由相同维数推出。

状态用块密度矩阵 $\rho=(\rho_c)_c$ 表示：每块 Hermitian、半正定，且 $\sum_c\operatorname{Tr}\rho_c=1$。可观测量是 $O=O^\dagger\in\mathfrak A_n$，期望为 $\sum_c\operatorname{Tr}(\rho_cO_c)$。这里使用普通矩阵迹表示状态；第 12.3 节的特定迹态另行指定。

在固定总类型 $c$ 中，$\rho(p,q)$ 同时保留两条路径的关系，满足 $\rho(q,p)=\overline{\rho(p,q)}$。只保留 $\rho(p,p)$ 会删除相干性。实际酉门 $U$ 的更新是有限双重求和

$$
\rho'(p,q)=\sum_{r,s}U(p,r)\rho(r,s)\overline{U(q,s)}.
\tag{FT.4}
$$

因此，完整的线性状态载体是同一终点类型下的“路径对”，不是单条已实现历史。跨不同总类型的相干在所选代数中不被观测，本卷不额外引入能混合这些类型的外部装置。

### 12.2 矩阵单位上的右扩展

令 $E^c_{pq}=|p\rangle\langle q|$。对 $d\in\mathsf N(c,\tau)$，以 $p d$ 表示在路径末尾补 $d$。

**命题 12.2（实际后代嵌入）。** 下式唯一线性延拓为保单位、单射、保持伴随的代数同态：

$$
j_n(E^c_{pq})=\sum_{d\in\mathsf N(c,\tau)}E^d_{p d,q d}.
\tag{FT.5}
$$

多次扩展等于对全部合法后缀求和，并且不依赖把后缀分成几批。

**证明。** 矩阵单位乘法为 $E^c_{pq}E^{c'}_{rs}=\delta_{c,c'}\delta_{q,r}E^c_{ps}$。扩展后，非零乘积必须具有相同末尾类型和相同完整中间路径，所以恰为同一乘法的扩展；伴随把 $p,q$ 互换。目标每条路径有唯一前缀，故源单位的像是目标单位。每个源类型至少有一个后继，固定一个后继即可从像恢复每个系数，故单射。两段后缀的连接与一次后缀枚举之间有保持初末点的双射，给复合相容性。证毕。

第 4.1 节的递推现在有一个显式集合来源：$\mathsf P_{n+1}(\mathbf1)\cong\mathsf P_n(\tau)$，$\mathsf P_{n+1}(\tau)\cong\mathsf P_n(\mathbf1)\sqcup\mathsf P_n(\tau)$。有限 $n$ 的全空间不能当作 $n$ 个独立两维粒子的张量积。

### 12.3 迹权重随扩展相容

记 $d_{\mathbf1}=1,d_\tau=\varphi$，其中 $\varphi>0$ 且 $\varphi^2=\varphi+1$。

**命题 12.3（相容的有限迹态）。**

$$
t_n(A)=\varphi^{-n}\sum_c d_c\operatorname{Tr}(A_c)
\tag{FT.6}
$$

是 $\mathfrak A_n$ 上的忠实归一化迹态，并且 $t_{n+1}j_n=t_n$。

**证明。** 融合表给 $\sum_{d\in\mathsf N(c,\tau)}d_d=\varphi d_c$。对矩阵单位代入式（FT.5），直接得到相容性。$t_0(1)=1$，配合保单位扩展归纳得到归一化。各块系数严格正，普通矩阵迹的正性、忠实性和循环性分别给三项性质。证毕。

这是进入无限代数网之前的有限接口；本命题不单独证明极限迹的唯一性、半链因子性或 DHR 识别。

## 13. 树形重组的全部有限相容条件

### 13.1 有序树、标签与 $F$ 系数

**定义 13.1（带类型的有序二叉树）。** 树由有类型的叶和有序连接 $T=(T_L,T_R)$ 递归生成。给定叶类型序列和根类型 $c$，内部节点标记必须满足“父类型属于两子类型的 $\mathsf N$”。标签集合递归为

$$
\mathsf{Lab}((T_L,T_R),c)
=\coprod_{a,b:\ c\in\mathsf N(a,b)}
\mathsf{Lab}(T_L,a)\times\mathsf{Lab}(T_R,b).
\tag{FT.7}
$$

叶的标签集合在叶类型等于根类型时为单点，否则为空。取 $\mathbb C^{\mathsf{Lab}(T,c)}$ 得树基空间。式（FT.7）明确了节点胶合的直和、张量与边界类型。

令 $r=\varphi^{-1}$、$s=\sqrt r>0$，则 $r^2+r=1$、$s^2=r$。$F^{abc}_z(e,h)$ 表示把左括号 $((ab)_e c)_z$ 变为右括号 $(a(bc)_h)_z$ 的系数。若任一所列融合不合法，系数定义为零。其余所有一维块为 $1$，唯一二维块为

$$
F^{\tau\tau\tau}_{\tau}=
\begin{pmatrix}r&s\\s&-r\end{pmatrix},
\qquad e,h\text{ 按 }(\mathbf1,\tau)\text{ 排序}.
\tag{FT.8}
$$

这是 [TTWL09, PDF Eq. (2.4)] 的固定规范数据，不作为新发现。每个非空块都是酉矩阵：唯一二维检查化为 $r^2+s^2=1$ 和交叉项 $rs-rs=0$。

**命题 13.2（完整有限五边形恒等式）。** 对任意 $a,b,c,d,z\in L$，任意合法左路径 $(e,f)$ 和右路径 $(h,g)$，都有

$$
\sum_{j\in L}
 F^{abc}_{f}(e,j)F^{ajd}_{z}(f,g)F^{bcd}_{g}(j,h)
 =F^{ecd}_{z}(f,h)F^{abh}_{z}(e,g).
\tag{FT.9}
$$

**证明。** 外部五个类型只有 $32$ 种。按两端标签空间的维数，完整划分为：$5$ 个零维情形；$21$ 个一维情形，两边均为 $1$；$5$ 个二维情形；$1$ 个三维情形。二维中的四个情形为四片叶恰有一片 $\mathbf1$、根为 $\tau$，删除单位叶后两路都给式（FT.8）；剩下一个为四片叶全 $\tau$、根为 $\mathbf1$，两路都为 $I_2$，使用 $F^2=I_2$。

最后一个情形四片叶及根全为 $\tau$。两端均按 $(\mathbf1,\tau),(\tau,\mathbf1),(\tau,\tau)$ 排序，逐项代入式（FT.8），两边同为

$$
\begin{pmatrix}
0&r&s\\
r&r&-rs\\
s&-rs&r^2
\end{pmatrix}.
\tag{FT.10}
$$

简化只使用 $s^2=r$、$r^2=1-r$。以上穷尽全部合法源、靶标签，包括空情形，故证明式（FT.9）。证毕。

相互分离子树上的 $F$ 作用由张量乘法交换。将这些方块及五边形提升为任意重括号路径的一致性，使用 [EGNO15, §§2.8–2.9] 的结合相容定理。将该定理实例化成具体的库中范畴仍是后续形式化任务，不能把 Python 有限检查称作已经构造了完整无限范畴。

只有同一棵树的维数和每个 $F$ 的酉性仍不足以保证五边形：保持其余标量块而把二维块改成 $\operatorname{diag}(1,-1)$，五边形要求中的 $F_{00}=F_{01}F_{10}$ 变为 $1=0$。这给“同树、同维、局部可逆”不足以保证共同结合结构的明确反例。

### 13.2 换基与主动门的类型区别

**命题 13.3（坐标运输保持预测）。** 若 $W:H_T^c\to H_{T'}^c$ 为上述酉换基，令 $\rho'=W\rho W^\dagger$、$O'=WOW^\dagger$，则 $\operatorname{Tr}(\rho'O')=\operatorname{Tr}(\rho O)$。

**证明。** 将 $W^\dagger W=I$ 代入乘积，再对有限矩阵迹使用循环性。证毕。

这个操作同时改写状态和读数。主动门则在固定读数下改变状态。数值上同为式（FT.8）不能混同两个类型。例如 $\mathfrak A_3\cong\mathbb C\oplus M_2(\mathbb C)$ 中的 $\widehat F=1\oplus F$ 可以被另行指定为理想三位置局部门；这项指定是实际电路操作，和被动重括号有不同的物理解释。编织还需要满足六边形的 $R$ 数据，本批不由 $F$ 单独推出编织或通用量子计算。

## 14. 局部相互作用的任意长度矩阵构造

### 14.1 可复用的带权路径引理

**定理 14.1（路径投影子的 Temperley–Lieb 关系）。** 设有限标签集 $L$ 有对称的零一邻接关系 $a\sim b$，允许自环；给定 $\delta>0$ 和严格正权重 $d_a$，满足

$$
\sum_{b:\ a\sim b}d_b=\delta d_a.
\tag{FT.11}
$$

固定长度 $n$ 与两个端点，在合法路径 $x_0\sim x_1\sim\cdots\sim x_n$ 的正交基上，对 $1\le i<n$ 定义 $P_i$：除 $x_i$ 外的坐标必须相同；若 $x_{i-1}\ne x_{i+1}$，系数为零；若共同值为 $a$，则

$$
\langle\ldots,b',\ldots|P_i|\ldots,b,\ldots\rangle
=\frac{\sqrt{d_{b'}d_b}}{\delta d_a}.
\tag{FT.12}
$$

则

$$
P_i^\dagger=P_i,\quad P_i^2=P_i,\quad
P_iP_{i+1}P_i=\delta^{-2}P_i,\quad
[P_i,P_j]=0\quad(|i-j|\ge2).
\tag{FT.13}
$$

**证明。** 固定除第 $i$ 位外的坐标。非零块为 $vv^T/(\delta d_a)$，$v_b=\sqrt{d_b}$；式（FT.11）给 $v^Tv=\delta d_a$，故为正交投影。空路径空间上所有式子均为空矩阵恒等式。

对相邻三乘积，只有输入局部段 $(a,b,a,d)$ 可能非零。右边第一个 $P_i$ 把 $b$ 改成中间值 $t$；随后 $P_{i+1}$ 非零强制 $t=d$；最后一个 $P_i$ 非零又强制第 $i+1$ 位回到 $a$。所以求和只剩唯一项，其输入 $b$、输出 $b'$ 的系数是

$$
\frac{\sqrt{d_bd_d}}{\delta d_a}
\frac{d_a}{\delta d_d}
\frac{\sqrt{d_dd_{b'}}}{\delta d_a}
=\delta^{-2}\frac{\sqrt{d_bd_{b'}}}{\delta d_a}.
$$

对称邻接确保强制出的中间路径合法。其他输入两边均为零。这给相邻关系；反向关系同样计算。距离至少二的两次操作改变不同坐标，也不改变对方系数依赖的邻居标签，故逐项交换。证毕。

因此 $e_i=\delta P_i$ 满足 $e_i^2=\delta e_i$、$e_ie_{i+1}e_i=e_i$。这是已知带权路径表示的直接证明，[FK07、TTWL09] 使用其 RSOS/Temperley–Lieb 形式；不认领该表示的原创性。

### 14.2 Fibonacci 局部真空通道的完整块

取邻接关系 $b\in\mathsf N(a,\tau)$，$d=(1,\varphi)$，$\delta=\varphi$。式（FT.11）由 $\varphi^2=1+\varphi$ 得到。在第 12 节的路径中，固定 $(x_{i-1},x_{i+1})$ 后，$P_i$ 的全部情形为

$$
\begin{array}{c|c}
(x_{i-1},x_{i+1})&P_i\text{ 在允许的 }x_i\text{ 上的块}\\\hline
(\mathbf1,\mathbf1)&(1)\\
(\mathbf1,\tau)\text{ 或 }(\tau,\mathbf1)&(0)\\
(\tau,\tau)&\begin{pmatrix}r^2&rs\\rs&r\end{pmatrix}.
\end{array}
\tag{FT.14}
$$

对最后一块，$P_i=F\operatorname{diag}(1,0)F^\dagger$；其余块由唯一通道或禁止通道得到。因此它就是先重括号使第 $i,i+1$ 两片叶相邻融合、投影到总类型 $\mathbf1$、再返回原基的操作，[TTWL09, §3.1] 给同一物理相互作用。该投影在真实网中属于位置 $[i,i+1]$ 的窗口代数。路径坐标 $x_i$ 是前缀总类型，不能把“改变一个 $x_i$”误当作物理上独立的一位量子比特操作。

在右扩展下，原有 $P_i$ 的系数不依赖新加的末尾标签；式（FT.5）于是将它精确送入更大窗口的同一个 $P_i$。左侧扩展及其他括号形式使用第 13 节的相容运输，不任意重选矩阵。

## 15. 从局部能量到门、可观测量与严格传播

**命题 15.1（投影脉冲的完整代数律）。** 对任意有限维正交投影 $P$ 和 $z\in\mathbb C$、$|z|=1$，定义

$$
U_P(z)=I+(z-1)P.
\tag{FT.15}
$$

则 $U_P(z)^\dagger=U_P(\overline z)$、$U_P(z)U_P(w)=U_P(zw)$，故 $U_P(z)$ 酉。对固定读数 $O$，相应 Heisenberg 更新为

$$
U_P(z)^\dagger O U_P(z)
=O+(z-1)OP+(\overline z-1)PO+|z-1|^2POP.
\tag{FT.16}
$$

**证明。** 展开两个因子并使用 $P^2=P$；一次项系数为 $(z-1)+(w-1)+(z-1)(w-1)=zw-1$。取 $w=\overline z$ 得酉性。三因子直接展开得最后一式。证毕。

取物理 Hamiltonian $H=-JP$、$J\in\mathbb R$、$\hbar>0$，$z=e^{iJt/\hbar}$，幂级数给 $e^{-itH/\hbar}=U_P(z)$。可先形式化式（FT.15）这个有限多项式引理，再连接矩阵指数；不必把矩阵指数计算当作基础定义。这里是给定相互作用的理想模型，不代表任何装置已实现任意门。

**命题 15.2（两层局部门产生严格 QCA）。** 在无限 Fibonacci 链上，先对所有不交的奇数键 $[2j-1,2j]$ 施加任意 $U_{P_{2j-1}}(z_j)$，再对不交的偶数键施加同类门。这定义一个两层 FDQC，其演化及逆的传播半径均至多二。

**证明。** 每一层内不交窗口代数对易。对有限支撑可观测量，只有有限多个门有作用，其支撑最多向两侧扩大一格；两层后最多扩大二格。对同一可观测量在更大窗口计算给相同答案，因此定义在局部代数并上的保范数星同构，延拓到 C*-闭包。逆使用逆序两层和共轭相位，具有同一预算。证毕。

本命题给出了实际可观测量变换的构造。有限时间的整个非交换 Hamiltonian $-\sum_iJ_iP_i$ 的精确连续演化不被本命题认作这两层电路；把它们比较还需要单独的逼近及误差分析。

## 16. 何时可以只保留“分支概率”？

### 16.1 一个必要且充分的有限矩阵判据

**定理 16.1（概率独立演化判据）。** 设 $H=\mathbb C^m$、$m\ge1$，固定基及酉矩阵 $U$。记 $\pi(\rho)=(\rho_{jj})_j$。以下等价：

一、存在列随机矩阵 $K$，对所有密度矩阵 $\rho$ 都有 $\pi(U\rho U^\dagger)=K\pi(\rho)$。

二、$U$ 每行每列恰有一个非零元，该元模为一，即 $U$ 是置换矩阵与对角相位矩阵的乘积。

三、$U$ 通过共轭保持该基的对角代数。

**证明。** 取 $\rho=|j\rangle\langle j|$，条件一强制 $K_{aj}=|U_{aj}|^2$。对 $j\ne k$，取 $(|j\rangle\pm|k\rangle)/\sqrt2$ 两个纯态，它们具有相同 $\pi$，故输出第 $a$ 个概率相同，得到 $\operatorname{Re}(U_{aj}\overline{U_{ak}})=0$。再取 $(|j\rangle\pm i|k\rangle)/\sqrt2$ 得虚部为零。因此同一行两个不同位置不能同时非零。酉性使每行范数一，且不同的行不能占据相同列，于是条件二成立。条件二直接给条件一及三。条件三把对角代数的秩一极小投影置换，故每个 $U|j\rangle$ 是某个基向量的相位倍数，给条件二。证毕。

这属于对角代数正规化子的标准性质；本卷给出完整证明及融合链实例，不将它登记为新的普遍量子定理。量词“所有密度矩阵”不能弱化后保留这个结论：如果只允许对角初态，一次操作总能写成 $|U_{aj}|^2$ 的随机转移；后续无测量演化未必继续满足这一公式。

定义 $\mathsf S(U)_{aj}=|U_{aj}|^2$。对式（FT.8），$F^2=I$，但

$$
\mathsf S(F)=\begin{pmatrix}r^2&r\\r&r^2\end{pmatrix},
\qquad [\mathsf S(F)^2]_{01}=2r^3>0.
\tag{FT.17}
$$

所以“先丢掉相位，再把每步看成随机分支”不保持实际操作的复合与逆。若每步确实插入去相干测量，这个随机模型可以描述另一套已改变的实验；该实验权限须明示。

### 16.2 三任意子的尖锐预测损失

固定 $H_3^\tau\cong\mathbb C^2$，并设

$$
P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\quad
Q=FPF^\dagger=\begin{pmatrix}r^2&b\\b&r\end{pmatrix},\quad
b=rs=\varphi^{-3/2}>0.
\tag{FT.18}
$$

$P,Q$ 分别测量第一对和第二对任意子的真空融合通道。取

$$
\rho=\begin{pmatrix}p&x+iy\\x-iy&1-p\end{pmatrix},\qquad
0\le p\le1,\quad x^2+y^2\le p(1-p).
\tag{FT.19}
$$

后一个不等式与两阶 Hermitian 矩阵的半正定性等价。

**定理 16.2（仅知分支概率的最优最坏误差）。** 只给定 $p=\operatorname{Tr}(P\rho)$ 时，预测第二对读数的精确范围是

$$
\operatorname{Tr}(Q\rho)\in
\left[r+(r^2-r)p-2b\sqrt{p(1-p)},\ 
      r+(r^2-r)p+2b\sqrt{p(1-p)}\right].
\tag{FT.20}
$$

在这个固定 $p$ 的状态类上，任意预测值的最坏绝对误差至少为 $2b\sqrt{p(1-p)}$，区间中点达到该下界。$p=1/2$ 时该最优误差是 $b=\varphi^{-3/2}$。

**证明。** 直接取迹得到 $r+(r^2-r)p+2bx$。式（FT.19）给 $|x|\le\sqrt{p(1-p)}$，两个端点均由 $y=0$、等号成立的纯态实现。任何实数到区间两端至少有一边距离不小于半区间宽；中点到全部允许值的距离不超过该半宽。证毕。

同一常数还满足 $\|[P,Q]\|=b$，因为 $[P,Q]=\left(\begin{smallmatrix}0&b\\-b&0\end{smallmatrix}\right)$，其伴随乘积是 $b^2I$。因此本模型给出一个精确联系：局部读数的不相容程度，等于平衡分支状态中丢掉相干后不可消除的最坏预测误差。该等式仅针对上述模型和误差任务。

**推论 16.3（单次指定脉冲的转移限度）。** 从 $|0\rangle$ 出发，只施加一个 $U_Q(e^{i\theta})$，测得第二个路径基态的概率为

$$
4\varphi^{-3}\sin^2(\theta/2)\le4\varphi^{-3}<1.
\tag{FT.21}
$$

**证明。** 转移振幅为 $(e^{i\theta}-1)b$；平方模即得。最后严格不等式等价于 $(r^2-r)^2=1-4r^3>0$。证毕。

这是单个已指定相互作用脉冲的限制，不是所有多门电路的可达性上界。

## 17. 最小预测状态与可执行的三读数恢复

### 17.1 有限可观测空间的严格完成

**定理 17.1（受控观察的最小线性完成）。** 在 $\mathbb C^m$ 上固定有限族 Hermitian 控制 Hamiltonian $H_a$ 和读数 $E_b$。允许任意有限控制词，每段时长非负，在末尾读出期望；不同词以同一初态的独立制备比较。定义实线性映射 $\mathcal D_a(O)=i[H_a,O]$，以及

$$
W_0=\operatorname{span}_{\mathbb R}\{I,E_b\},\qquad
W_{k+1}=W_k+\sum_a\mathcal D_a(W_k).
\tag{FT.22}
$$

则某个 $k\le m^2-\dim W_0$ 使 $W_k=W_{k+1}=:W$；此后稳定。两个密度矩阵对全部上述实验不可区分，当且仅当

$$
\operatorname{Tr}((\rho-\sigma)O)=0\quad\text{对全部 }O\in W.
\tag{FT.23}
$$

在任意实线性期望坐标摘要中，若其相等保证全部实验预测相等，则在迹一状态的仿射空间上至少需要 $\dim W-1$ 个独立实坐标；$W$ 的一组去常数基坐标达到这个下界。

**证明。** $\operatorname{Herm}(m)$ 的实维数为 $m^2$。每次严格增长至少增加一维，若某步相等便对全部 $\mathcal D_a$ 不变，故不会再增长，得到界。由递推，$W$ 是包含初始读数并在全部这些映射下不变的最小空间。

若式（FT.23）成立，每段 Heisenberg 演化为 $e^{t\mathcal D_a}$，其级数保持有限维闭子空间 $W$，因而任意有限复合也保持它，给相同末尾读数。反向，对任意控制词的各段时长在零点逐次取右导数，得到所有迭代交换子读数相同。有限矩阵指数解析，右导数与通常导数相同；这些交换子张成 $W$，给式（FT.23）。本证明不把负时间偷偷加入合法控制集。

最后令 $V=\operatorname{Herm}_0(m)$。任何 $D\in V$ 在充分小 $\epsilon>0$ 下使 $I/m\pm\epsilon D$ 都为密度矩阵。因此摘要在线性方向上的核必须包含于 $W$ 在 $V$ 上的消去子。该消去子的余维为 $\dim W-1$，因为 $I\in W$ 且迹配对非退化。秩零度公式给下界；取 $W$ 基底的期望则达到。证毕。

这是 [DA03, §2, Theorem 1] 的有限受控可观测空间机制，本卷采用显式非负时长与归一化状态的版本。它与原统一预测主卷的 $OA=KO$ 在密度矩阵和交换子生成元上形成具体接口。下界限于线性期望摘要，不能声称排除了任意病态集合编码。

对式（FT.18），即使初始只读 $P$，控制采用 $-P,-Q$，也有

$$
W_0=\operatorname{span}\{I,P\},\quad
 i[Q,P]=\begin{pmatrix}0&-ib\\ib&0\end{pmatrix},\quad
 i[P,i[Q,P]]=\begin{pmatrix}0&b\\b&0\end{pmatrix}.
\tag{FT.24}
$$

四个矩阵实线性独立，故 $W_2=\operatorname{Herm}(2)$。因此需要三个独立的归一化状态实坐标，分别可以取 $p,x,y$；只有 $p$ 不能形成相同任务下的自治预测状态。

### 17.2 三种具体设置与恢复误差

以下更明确地允许测量两对相邻任意子的真空通道 $P,Q$，并允许第一对的相位脉冲。此权限与上一节“只读 $P$”的最小完成论证分开声明。

**定理 17.2（三设置精确恢复与尖锐噪声界）。** 对式（FT.19）的任意状态，取 $V=U_P(i)=\operatorname{diag}(i,1)$，定义独立制备实验的三个期望

$$
m_0=\operatorname{Tr}(P\rho),\quad
m_1=\operatorname{Tr}(Q\rho),\quad
m_2=\operatorname{Tr}(QV\rho V^\dagger).
$$

写 $h=r^2-r$，则

$$
p=m_0,\quad
x=\frac{m_1-r-hm_0}{2b},\quad
y=\frac{r+hm_0-m_2}{2b}.
\tag{FT.25}
$$

若三个实测期望各自误差绝对值不超过 $\epsilon$，按这个线性公式重建 $\widehat\rho$，则

$$
\frac12\|\widehat\rho-\rho\|_1
\le\sqrt{1+2\varphi}\,\epsilon.
\tag{FT.26}
$$

对原始线性重建，该常数不能减小。

**证明。** 第一个式子直接；第二个来自第 16.2 节取迹。$V$ 将 $x+iy$ 变为 $-y+ix$，所以 $m_2=r+hp-2by$，解线性方程即得式（FT.25），分母 $b>0$。

令读数误差为 $\eta_j$。则 $\delta p=\eta_0$，$\delta x=(\eta_1-h\eta_0)/(2b)$，$\delta y=(h\eta_0-\eta_2)/(2b)$。因 $h=1-2r<0$ 且 $(1+|h|)/(2b)=1/s=\sqrt\varphi$，有 $|\delta p|\le\epsilon$，$|\delta x|,|\delta y|\le\sqrt\varphi\epsilon$。迹零两阶 Hermitian 差矩阵的特征值为 $\pm\sqrt{\delta p^2+\delta x^2+\delta y^2}$，给式（FT.26）。取 $\eta_0=\eta_1=\eta_2=\epsilon$，上述三个界同时达到。对真实态 $I/2$ 及足够小的 $\epsilon$，读数仍在 $[0,1]$ 且重建态仍半正定，因此尖锐性也可在物理状态附近达到。证毕。

一般有噪线性重建未必半正定。将 $(\widehat p-1/2,\widehat x,\widehat y)$ 欧氏投影到半径 $1/2$ 的闭球可强制半正定；球投影到真实球内点的距离不增加，故式（FT.26）仍成立。此处三个数是期望，不是三次单样本结果；实际统计精度需要重复制备、测量及独立的误差预算，本批未报告硬件实验。

## 18. 从局部谱系返回切口分类：哪些区别已经保留？

### 18.1 中心给出“画图交换”不能直接当作量子门的有限证据

**命题 18.1（整窗口层交换通常为外自同构）。** 对 $n\ge2$，$\mathfrak A_n$ 有两个非零总类型块。记它们的中心单位为 $z_{\mathbf1},z_\tau$。在 $\mathfrak A_n\otimes\mathfrak A_n$ 上，因子交换 $\mathsf{Flip}(a\otimes b)=b\otimes a$ 不能由这个同一窗口代数内的酉元共轭实现。

**证明。** $z_{\mathbf1}\otimes z_\tau$ 与 $z_\tau\otimes z_{\mathbf1}$ 是不同的非零正交中心投影；交换把前者送到后者。任何代数内酉共轭都逐点固定中心，矛盾。证毕。

允许的两层混合门可以改变固定总类型对内的融合重数空间，仍须保持整个窗口的中心。这个命题只排除同窗口的直接交换门，不能单独排除借助更宽窗口和更多层的所有实现。后一问题仍须第 2 节的统一切口局部化及第 6 节的无限尾部障碍。

### 18.2 两条相互独立的结构要求

第 16–17 节说明：预测局部相互作用后的读数，需要保留路径对的相干数据；这属于状态与观察任务。第 6 节的 $D(n+k)D(n-k)-D(n)^2$ 则比较实际半链嵌入的相对交换子代数，属于动力学的局部实现类型。两者不被识别成同一个不变量。

式（FT.5）使“后代”具有真实代数嵌入，第 13 节给括号重组的相容性，第 14–15 节给物理局部门及统一传播预算，第 16–17 节给足以预测这些门的状态表示。这个链条为后续形式化第 3 节切口作用提供有限基础；它没有重新验证原反例的完整 DHR 产品相容性，也没有证明新增切口作用的完备性。

## 19. 后续形式化的陈述与依赖顺序

以下为待实施的数学接口，均不是已经编译的 Lean 模块名或已通过的核验证据。每一步都保留原量词和退化情形，不把目标结论作为结构字段输入。

| 次序与候选接口 | 完整输入类型及约束 | 要保留的结论与主要证明 |
| --- | --- | --- |
| FTpath | 二元素有限类型；$n\in\mathbb N$；终点 $c$；合法性谓词 | 构造有限路径与后缀双射；包含 $n=0$、空终点扇区；递推证明计数 |
| FTmatrixEmbedding | 按非空终点分块的有限复矩阵；矩阵单位 | 式（FT.5）的乘法、伴随、单位、单射和复合；由系数逐项证明 |
| FTassociator | $r,s\in\mathbb R$，$r>0,s>0,r^2+r=1,s^2=r$；所有类型与合法标签 | 明确定义全表 $F$；酉性、32 种边界的五边形；有限分类及多项式恒等式 |
| FTweightedProjector | 有限对称零一图、正权重、$\delta>0$、式（FT.11）；固定端点；$1\le i<n$ | 定理 14.1 对任意 $n$ 的投影、相邻 TL 和远距交换；唯一中间项计算 |
| FTpulse | 有限复内积空间；$P=P^\dagger=P^2$；$|z|=|w|=1$ | 多项式门律、Heisenberg 公式；另接矩阵指数和物理 $\hbar>0$ |
| FTclassicalShadow | $m\ge1$；酉矩阵；全体半正定迹一密度矩阵 | 定理 16.1 的双向判据；四个相位测试态和对角极小投影 |
| FTpredictionRisk | 两阶 Hermitian 状态、正系数 $b$、固定 $p\in[0,1]$ | 精确输出区间、极值态、最小最坏误差；含 $p=0,1$ |
| FTobservableCompletion | 有限 Hermitian 控制族与读数族；所有有限非负时长词 | 子空间递推终止、实验等价、迹一仿射维数下界；有限维与矩阵指数导数 |
| FTtomography | 已知 $r,s,b$；同一初态的三独立制备设置；逐读数误差上界 | 完整反演、半正定条件、迹距离界和达到性；二阶特征值 |
| FTnetAdapter | 已给 Fib 范畴及两侧窗口嵌入；统一有界门层 | 将上述具体矩阵接到真实无限网；归纳极限和正常延拓另证 |

符号运算可以使用 $s^4+s^2-1=0$ 的精确多项式约化；正性、平方根的指定实嵌入和所有分母非零仍须证明。一般 $n$ 的陈述由路径归纳与局部系数证明承担，不能从 $n\le9$ 的矩阵核对外推。

目前没有新增 Lean/Scribe 文件。新形式化实施应先建立这些可复用对象与引理，再提供原具体融合链的实例映射。仅把已知公式改名、只交伪代码、或以假设“存在相容实现”换取目标结论，均不构成本卷的完成。

## 20. 本批来源、实际检查与未决边界

[TTWL09] Simon Trebst, Matthias Troyer, Zhenghan Wang and Andreas W. W. Ludwig, *A short introduction to Fibonacci anyon models*, Progress of Theoretical Physics Supplement 176, 384–407 (2008); arXiv v1 submitted 2009. [arXiv:0902.3275v1](https://arxiv.org/html/0902.3275v1). 使用 §§2.3–2.5、§3.1；PDF 第 7、10 页的 $F$ 系数和坐标/编织区别已视觉核对。路径模型、$F$ 表和黄金链相互作用属于已有文献；本批按明确边界重新给出有限推导。

[FK07] Adrian Feiguin, Simon Trebst, Andreas W. W. Ludwig, Matthias Troyer, Alexei Kitaev, Zhenghan Wang and Michael H. Freedman, *Interacting anyons in topological quantum liquids: The golden chain*, Physical Review Letters 98, 160409 (2007). [arXiv:cond-mat/0612341](https://arxiv.org/abs/cond-mat/0612341). 使用相邻真空通道相互作用与 RSOS/TL 表示的来源归属；本轮读取摘要及 TTWL09 中的展开，不以此声称重新验证其临界理论结论。

[DA03] Domenico D'Alessandro, *On Quantum State Observability and Measurement*, Journal of Physics A: Mathematical and General 36, 9721–9735 (2003). [arXiv:quant-ph/0307127](https://arxiv.org/pdf/quant-ph/0307127). 已读取 §2 的可观测空间、终止算法及 Theorem 1 的证明。定理 17.1 明确复用该机制；本批不认领一般量子可观测性理论的原创性。

配套新程序为 [`fusion_tree_checks.py`](../../reports/fusion-qca-cut-obstruction/fusion_tree_checks.py)，实际输出为 [`fusion_tree_results.json`](../../reports/fusion-qca-cut-obstruction/fusion_tree_results.json)。运行命令：

```bash
python docs/reports/fusion-qca-cut-obstruction/fusion_tree_checks.py
```

实际执行使用 Python 标准库的有理数和商环 $\mathbb Q[s]/(s^4+s^2-1)$，不使用浮点近似判等。完成 32 个五边形外部类型情形的全部 50 个合法系数等式、15 个 $F$ 酉性系数；任意长度公式的有限诊断覆盖 $n\le15$ 的路径计数，以及 $2\le n\le9$ 两总类型扇区的 72 个投影关系、112 个相邻 TL 关系、112 个远距交换关系。另检查 10857 个实际右扩展系数和 199 个矩阵单位乘积。

门与预测部分实际检查 12 个复相位门的酉性、72 个门复合、6 个转移概率、29 个合法密度矩阵的三设置恢复、尖锐误差系数及两个相干方向。故意错误的酉 $F$ 表确实被五边形检查拒绝。计数中边界实例与其中的系数检查互有包含，不把它们相加当作独立理论结果数。旧 `verify.py/results.json` 保留不动，旧批检查没有在本批冒领为重新运行。

这些是有限代数检错。一般长度、最小误差、全体状态量词及有限维闭合由正文证明；尚无 Lean 编译、独立同行评审、硬件实验或本批 CI 通过声明。新增内容不改变 Jones–Lim 原问题或第 6 节反例稿的审定状态，不以有限模型确认替代一般 QCA 分类。

## 追加锚（本行以下为后续增补区，FT 批次结束）

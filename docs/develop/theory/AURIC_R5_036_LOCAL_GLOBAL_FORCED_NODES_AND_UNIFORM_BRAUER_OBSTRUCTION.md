# 原二十八强制节点的处处局部性与一致四元数障碍

## 96. 同一原域、同一目标与实际族定理

**定义 96.1（原无序对、局部点与配对）。** 固定代数闭包 $\overline{\mathbb Q}$。对其中的八次可分域 $D/\mathbb Q$，令 $\Sigma_D=\operatorname{Hom}_{\mathbb Q}(D,\overline{\mathbb Q})$，并采用 source034 定义 90.1 的原无序异元对概形

$$
P=\mathscr P_2(D/\mathbb Q)
=\bigl((\operatorname{Spec}D\times_{\mathbb Q}\operatorname{Spec}D)
\setminus\Delta\bigr)/\mathfrak S_2.
\tag{96.1}
$$

其几何点是 $\Sigma_D$ 的二元子集，次数为二十八；商中的换位只忘记一对嵌入的次序，不更换原来的嵌入。source034 定理 90.2 的有限 étale 下降与闭浸入将作为本卷的几何输入。

对有限 étale $\mathbb Q$-概形 $Z$，$\operatorname{Br}Z$ 表示其 Brauer 群，$\operatorname{Br}_0 Z$ 表示结构态射拉回 $\operatorname{Br}\mathbb Q$ 的像。若 $Z=\coprod_a\operatorname{Spec}K_a$，则 $\operatorname{Br}Z=\prod_a\operatorname{Br}K_a$，每个因子都是域的中心单代数的 Brauer 群。称 $\gamma\notin\operatorname{Br}_0 Z$ 为非恒定类。次数二 Azumaya 代数指在每个分支上秩为四的 Azumaya 代数，包括分裂的二阶矩阵代数。

以 $v$ 遍历 $\mathbb Q$ 的有限地方及实地方，$\mathbb Q_\infty=\mathbb R$。有限概形 proper，故

$$
Z(\mathbb A_{\mathbb Q})=\prod_v Z(\mathbb Q_v).
\tag{96.2}
$$

对 $x_v:\operatorname{Spec}\mathbb Q_v\to Z$ 和 $\gamma\in\operatorname{Br}Z$，写 $\gamma(x_v)=x_v^*\gamma$，并定义经典 Brauer–Manin 配对

$$
\langle(x_v),\gamma\rangle
=\sum_v\operatorname{inv}_v\gamma(x_v)\in\mathbb Q/\mathbb Z,
\qquad
Z(\mathbb A_{\mathbb Q})^{\gamma}
=\{x:\langle x,\gamma\rangle=0\}.
\tag{96.3}
$$

有限地方的局部不变量为 $\operatorname{Br}\mathbb Q_v\simeq\mathbb Q/\mathbb Z$；实地方的像为 $\{0,1/2\}$，复地方的 Brauer 群为零。配对中只有有限项非零。这里使用局部 Brauer 群及数域互反律的经典定义；所需精确正合列见证明中的 (98.5)。

几何对象始终取自原 $D$。固定其一个 $\mathbb Q$-基与体积形式，令 $X_D=\operatorname{Gr}_{\mathbb Q}(4,D)$。对实际四维子空间 $A\subset D$，包含帧记为 $B_A$，原乘法 $x\cdot-$ 的矩阵记为 $M_x$，置

$$
P_A(x)=\det[B_A,M_xB_A].
\tag{96.4}
$$

换帧不改变系数线 $[P_A]$。沿用 source033 定义 81.1 的系数空间 $H_D$、系数映射 $\phi:A\mapsto[P_A]$ 及其约化像闭包 $\Gamma_D\subset\mathbb P(H_D)$。一个允许的实际目标是 $C\in X_D(\mathbb Q)$，满足以下两个分别列出的条件：对原嵌入限制到 $C_{\overline{\mathbb Q}}$ 所得的八行 $c_\sigma$，任意四行独立；并且

$$
[P_C]\in(\Gamma_D)_{\mathrm{sm}}(\mathbb Q).
\tag{96.5}
$$

前一个条件称统一性，后一个是系数像点的光滑性。设 $\mathcal G_C=\operatorname{Gr}_{\mathbb Q}(2,C)$，$\mathcal S$ 为其 tautological 秩二子丛。对实际窗口 $W\in X_D(\mathbb Q)$，原乘法给出

$$
\mu_W:\mathcal S\otimes_{\mathbb Q}W\longrightarrow
D\otimes_{\mathbb Q}\mathcal O_{\mathcal G_C},
\qquad u\otimes w\longmapsto uw,
\qquad T_W=V(\det\mu_W)\subset\mathcal G_C.
\tag{96.6}
$$

对统一目标，source034 定理 90.2 给规范闭浸入及其像

$$
\nu_C:P\xrightarrow{\ \sim\ }N_C\hookrightarrow\mathcal G_C,
\qquad
\{\sigma,\tau\}\longmapsto
\ker c_\sigma\cap\ker c_\tau.
\tag{96.7}
$$

$N_C$ 是带此概形结构的像；它不依赖 $W$。在 source034 定理 89.3 的非空实际窗口开集上，(96.7) 的二十八个几何点都是同一个 $T_W$ 的强制普通二重点。$N_C$ 不被定义为全部奇异概形。

**定义 96.2（递归素数与原符号翻转）。** 取三个不同的正素数，满足

$$
p_1\equiv1\pmod8,\qquad
p_2\equiv1\pmod{8p_1},\qquad
p_3\equiv1\pmod{8p_1p_2},
\qquad
D=\mathbb Q(\sqrt{p_1},\sqrt{p_2},\sqrt{p_3})
\subset\overline{\mathbb Q}.
\tag{96.8}
$$

在 $G=\operatorname{Gal}(D/\mathbb Q)$ 中，$h_i$ 指只将原生成元 $\sqrt{p_i}$ 变号、保持另外两个原生成元的自同构。对 $1\ne h\in G$，令 $E_h=D^{\langle h\rangle}$ 为实际固定子域，并写

$$
E=E_{h_1}=\mathbb Q(\sqrt{p_2},\sqrt{p_3}).
\tag{96.9}
$$

**定理 96.3（原二十八强制节点族的一致四元数障碍）。** 对每个满足 (96.8) 的素数三元组，原扩张 $D/\mathbb Q$ 次数为八，$G\simeq(C_2)^3$。存在定义 96.1 的允许实际目标 $C$。对每个这样的固定 $C$，存在一个非空 $\mathbb Q$-开集 $\mathcal U_C\subset X_D$，且 $\mathcal U_C(\mathbb Q)\ne\varnothing$，使以下结论对每个 $W\in\mathcal U_C(\mathbb Q)$ 同时成立。

第一，$T_W$ 是原乘法 (96.6) 的几何整、几何正规三维除子，$N_C\subset T_W$ 是 (96.7) 的二十八次有限 étale 强制节点子概形。每个强制几何点都是普通二重点。$C$ 和 $W$ 均为同一原 $D$ 内的子空间，不随地方改变。

第二，存在由原嵌入对给出的规范分解

$$
P\simeq\coprod_{1\ne h\in G}\operatorname{Spec}E_h,
\qquad [E_h:\mathbb Q]=4.
\tag{96.10}
$$

对 $D$ 中 $v$ 上方任一地方的完整分解群 $H_v$，局部点数在 $H_v=1$ 时为二十八，在 $H_v=\langle h\rangle$ 时为四；后一情形只有 $\operatorname{Spec}E_h$ 这一分支可见。在本族每个地方都有 $|H_v|\le2$，具体为

$$
\begin{aligned}
D\otimes_{\mathbb Q}\mathbb Q_{p_i}
&\simeq\prod_{a=1}^{4}\mathbb Q_{p_i}(\sqrt{p_i}),
&H_{p_i}=I_{p_i}&=\langle h_i\rangle,\\
D\otimes_{\mathbb Q}\mathbb Q_2&\simeq\mathbb Q_2^{\,8},
&D\otimes_{\mathbb Q}\mathbb R&\simeq\mathbb R^{8}.
\end{aligned}
\tag{96.11}
$$

其中 $I_{p_i}$ 是完整惯性群，三个二次局部扩张均完全分歧，$D$ 的有限分歧素数恰为 $\{p_1,p_2,p_3\}$。因此

$$
\begin{aligned}
P(\mathbb Q_v)&\ne\varnothing\quad(\text{每个 }v),&
P(\mathbb A_{\mathbb Q})&\ne\varnothing,&P(\mathbb Q)&=\varnothing,\\
N_C(\mathbb Q_v)&\ne\varnothing\quad(\text{每个 }v),&
N_C(\mathbb A_{\mathbb Q})&\ne\varnothing,&N_C(\mathbb Q)&=\varnothing.
\end{aligned}
\tag{96.12}
$$

第三，$p_1$ 在 $E$ 中完全分裂。有唯一 $\alpha\in\operatorname{Br}E$ 满足

$$
\operatorname{inv}_w\alpha=
\begin{cases}
1/2,&w\mid p_1,\\
0,&w\nmid p_1,
\end{cases}
\qquad(w\text{ 遍历 }E\text{ 的全部地方}).
\tag{96.13}
$$

它由一个四元数代数 $B/E$ 代表。在分解 (96.10) 上令

$$
\beta|_{\operatorname{Spec}E}=\alpha,
\qquad
\beta|_{\operatorname{Spec}E_h}=0\quad(h\ne h_1).
\tag{96.14}
$$

则 $\beta$ 由次数二 Azumaya 代数代表，且 $\beta\notin\operatorname{Br}_0P$。经同构 (96.7) 唯一传送得到

$$
\beta_C=(\nu_C^{-1})^*\beta\in\operatorname{Br}N_C,
\qquad \nu_C^*\beta_C=\beta.
\tag{96.15}
$$

$\beta_C$ 也由次数二 Azumaya 代数代表，且非恒定。对所有 adelic 点，同时有

$$
\begin{aligned}
\langle x,\beta\rangle&=1/2
&&\bigl(x\in P(\mathbb A_{\mathbb Q})\bigr),\\
\langle z,\beta_C\rangle&=1/2
&&\bigl(z\in N_C(\mathbb A_{\mathbb Q})\bigr).
\end{aligned}
\tag{96.16}
$$

特别地，两个非空 adelic 集合各被一个预先固定的四元数 Brauer 类全部排除：$P(\mathbb A_{\mathbb Q})^\beta=N_C(\mathbb A_{\mathbb Q})^{\beta_C}=\varnothing$。$\beta$ 在选择任何 $x$ 之前只由 (96.8) 的原算术数据确定；$N_C$ 和 $\beta_C$ 对同一 $\mathcal U_C$ 中的所有 $W$ 均不变。

最后，固定任一允许的 $p_1,p_2$，再让 $p_3$ 遍历 (96.8) 的素数，得到无穷多个两两不同构的原八次域，每个都满足上述全部结论。

证明。下面 §§97–99 给出同一定理的三个证明部分：先把经典有限 étale 局部判据精确用于原无序对，再在原递归素数族中构造同一个障碍类，最后沿原几何同构传送。经典输入只承担相应中间步骤；承重结论是它们在这个原乘法强制节点族中的共同实现。

## 97. 实际族证明中的原无序对与完整局部读数

**定义 97.1（完整分解群与局部因子次数）。** 暂令 $D/\mathbb Q$ 为任意八次可分域，$L$ 为其在 $\overline{\mathbb Q}$ 中的正规闭包。对 $v$ 选 $L$ 中的一个上方地方 $\widetilde v$，令

$$
H_v=\operatorname{Gal}(L_{\widetilde v}/\mathbb Q_v)
\subset\operatorname{Gal}(L/\mathbb Q).
\tag{97.1}
$$

更换 $\widetilde v$ 只共轭这个群。有限地方有完整局部分解

$$
D\otimes_{\mathbb Q}\mathbb Q_v=\prod_{a=1}^{r_v}K_{v,a},
\qquad d_{v,a}=[K_{v,a}:\mathbb Q_v]=e_{v,a}f_{v,a}.
\tag{97.2}
$$

$e_{v,a}$、$f_{v,a}$ 分别为分歧指数与剩余次数。定义 $n_j(v)=\#\{a:d_{v,a}=j\}$；在实地方则直接按局部因子 $\mathbb R$、$\mathbb C$ 的实次数一、二定义同一记号。$H_v$ 包含惯性作用，不以 Frobenius 循环群或剩余次数替代。

定理 96.3 的证明，第一部分。这里使用的有限 étale–Galois 对应为经典结果（Stacks Project，Tag 0BNE）。地方点对应完整分解群的不动点，正是 Jahnel–Loughran，*The Hasse principle for lines on del Pezzo surfaces*，arXiv:1410.5671v2，Lemma 2.1 的判据。应用到 (96.1)，得

$$
P(\mathbb Q_v)
\longleftrightarrow
\{A\subset\Sigma_D:|A|=2,\ H_vA=A\}.
\tag{97.3}
$$

完整 $H_v$ 在 $\Sigma_D$ 上的轨道与 (97.2) 的局部域因子对应，轨道长度为 $d_{v,a}$。一个二元不变子集只能是一条长度二的完整轨道，或两条长度一的轨道之并；反过来两种集合都不变。因此在本定理证明内部取得精确读数

$$
\#P(\mathbb Q_v)=n_2(v)+\binom{n_1(v)}2.
\tag{97.4}
$$

此式不要求 $D/\mathbb Q$ 为 Galois，分歧地方也包含在内。例如一个 $e=2,f=1$ 的二次因子贡献一条二元轨道；它不能因 $f=1$ 而被计作固定嵌入。另一方面，$D$ 是域，绝对 Galois 群在 $\Sigma_D$ 上传递；其不变子集只能为空集或全部八个嵌入，所以 $P(\mathbb Q)=\varnothing$。这也直接复用了 source034 定理 90.2 的原域不可见性。

现在在此证明中限定 $D/\mathbb Q$ 为 Galois，令 $G=\operatorname{Gal}(D/\mathbb Q)$，不再使用正规闭包的更大群。原嵌入集是 $G$ 的正则集。若某个子群 $H$ 保持一个二元子集，它到该二元集的置换群的作用是忠实的：作用核中的元素固定一个原嵌入，而正则作用的点稳定子平凡。故 $|H|\le2$。反之，$H=1$ 保持全部二十八对；当 $|H|=2$ 时，非平凡元素在八个嵌入上恰有四个二循环，只有它们各自的支撑是二元不变子集。于是

$$
\#P(\mathbb Q_v)=
\begin{cases}
28,&|H_v|=1,\\
4,&|H_v|=2,\\
0,&|H_v|>2.
\end{cases}
\tag{97.5}
$$

为判明本族处在何种经典局部结构中，还需应用几乎处处判据。Jahnel–Loughran 的 Lemma 2.2 使用 Chebotarev 定理，将几乎处处局部点条件化为每个循环子群都有不动点。在这里，也可直接代入 (97.5)：每个 $g\in G$ 的共轭类在无穷多个非分歧素数处成为 Frobenius 类，该处分解群的阶为 $\operatorname{ord}(g)$。因此，几乎处处有 $P(\mathbb Q_v)\ne\varnothing$ 当且仅当 $G$ 的每个元素阶至多为二。这样的群交换，因为对任意 $a,b$ 有 $ab=(ab)^{-1}=b^{-1}a^{-1}=ba$；再用 $|G|=8$，恰得 $G\simeq(C_2)^3$。

在这个群中，所有非分歧分解群循环且阶至多二，实地方的分解群也阶至多二。合用完整的 (97.5)，得到本应用所需的精确区分

$$
\begin{aligned}
P(\mathbb Q_v)\ne\varnothing\text{ 几乎处处}
&\Longleftrightarrow G\simeq(C_2)^3,\\
P(\mathbb Q_v)\ne\varnothing\text{ 处处}
&\Longleftrightarrow G\simeq(C_2)^3
\ \text{且每个分歧素数处 }|H_v|\le2.
\end{aligned}
\tag{97.6}
$$

(97.5)–(97.6) 的八次正则作用限制明确要求 $D/\mathbb Q$ 为 Galois；对非 Galois 八次域仍使用 (97.3)–(97.4)，不以 (97.6) 分类。这里并未把经典有限 étale 判据另立为新的独立定理，而是在原二十八对的作用中算出其适用形式。

进一步令 $G=(C_2)^3$。利用原包含 $D\subset\overline{\mathbb Q}$，把原嵌入识别为 $G$。每一对确定唯一的差元 $h\ne1$，并可写成 $\{\sigma,\sigma h\}$；$\sigma$ 可取这一对的任一成员，而 $h^{-1}=h$ 使差元不受交换次序影响。$G$ 交换，故左平移保持 $h$；固定 $h$ 的四对构成一个轨道，其稳定子是 $\langle h\rangle$。有限 étale–Galois 对应于是把这个轨道识别为实际固定域 $E_h$ 的谱，得到 (96.10)。也可内在地描述该对应：$E_h$ 的一个嵌入恰有两个向 $D$ 的延拓，它们构成这一对原嵌入。这说明分解不依赖嵌入编号。

每个 $E_h$ 都是原 $D$ 内的四次域，七个分支各自连通，整个 $P$ 是它们的不交并。当 $H_v=\langle h\rangle$ 时，$\operatorname{Spec}E_k$ 有局部点当且仅当 $H_v$ 包含在 $\langle k\rangle$ 中；由于群交换，这等价于 $k=h$。此时 $H_v$ 在 $G/\langle h\rangle$ 上作用平凡，故 $E_h\otimes\mathbb Q_v\simeq\mathbb Q_v^4$，恰有四个局部点。若 $H_v=1$，七个分支各贡献四点；若 $|H_v|>2$，没有任何分支可见。这完成原二十八对的全部群论读数，并将所需地方性归结为对 (96.8) 的完整局部计算。

## 98. 原递归素数族与预先固定的四元数类

定理 96.3 的证明，第二部分。先验证原域和每个地方，再在这些同一地方上构造类。

三个素数的平方类在 $\mathbb Q^\times/\mathbb Q^{\times2}$ 中独立：若 $p_1^{a_1}p_2^{a_2}p_3^{a_3}$ 为平方，$a_i\in\{0,1\}$，在 $p_i$ 处取赋值就有 $a_i=0$。经典多二次扩张对应因此给 $[D:\mathbb Q]=8$、$G=(C_2)^3$，且 $h_1,h_2,h_3$ 正是独立的原符号翻转。

对 $i<j$，(96.8) 给 $p_j\equiv1\pmod{p_i}$，所以 Legendre 符号 $(p_j/p_i)=1$。全部素数都为 $1\bmod4$，二次互反律给 $(p_i/p_j)=(p_j/p_i)=1$。由此

$$
\left(\frac{p_j}{p_i}\right)=1\quad(i\ne j),
\qquad
p_j\in\mathbb Q_{p_i}^{\times2}\quad(i\ne j).
\tag{98.1}
$$

第二式由奇素数处 Hensel 引理提升非零平方根。于是 $p_i$ 处另外两个平方根均已在底域中，而 $X^2-p_i$ 为 Eisenstein 多项式，给一个完全分歧二次域。原扩张的一个局部完备化恰为 $\mathbb Q_{p_i}(\sqrt{p_i})$；总次数八，故有四个这样的因子，即 (96.11) 第一行。完整局部自同构只能将 $\sqrt{p_i}$ 变号，并且这种变号确实存在，所以完整分解群与惯性群同时等于 $\langle h_i\rangle$。这里没有略掉分歧作用。

每个 $p_i\equiv1\pmod8$，经典 $2$ 进平方判据使 $p_i$ 为 $\mathbb Q_2$ 中的平方，故在 $2$ 处分裂成八份。三个素数均正，在实地方也分裂成八份。

再取奇素数 $\ell\notin\{p_1,p_2,p_3\}$。每个 $p_i$ 是 $\ell$ 进单位；相应二次扩张或平凡，或为唯一的非分歧二次扩张。它们的局部复合仍包含在这个非分歧二次域中。因此 $D$ 在 $\ell$ 处非分歧，其完整分解群阶至多二。这同时证明有限分歧集合恰为三个指定素数，并穷尽全部地方。代入 (97.5)，立即得到 $P$ 处处有局部点；在 $p_i$ 处四个点恰位于 $E_{h_i}$ 分支，在 $2$ 和实地方各有二十八个点。

存在局部点也确实给非空 adelic 集合。具体地，$P$ 在去掉有限个素数后有有限 étale 整模型，任一 $\mathbb Q_\ell$-点均延伸为 $\mathbb Z_\ell$-点：整模型有限，点所取的坐标整于 $\mathbb Z_\ell$，而 $\mathbb Z_\ell$ 在其分式域中整闭。故 (96.2) 没有额外的几乎处处整性障碍，选择每个地方的任一点便得 $P(\mathbb A_{\mathbb Q})\ne\varnothing$。结合第一部分的传递性论证，得 $P(\mathbb Q)=\varnothing$。

族的无穷性使用经典 Dirichlet 算术级数素数定理。先选定 $p_1\equiv1\pmod8$，再选定 $p_2\equiv1\pmod{8p_1}$；模数 $8p_1p_2$ 与剩余类 $1$ 互素，所以有无穷多个允许的 $p_3$。不同 $p_3$ 给不同的有限分歧素数集合，因而给两两不同构的 $\mathbb Q$-域。这些域共同含有 $\mathbb Q(\sqrt{p_1},\sqrt{p_2})$；无穷性来自分歧集合，绝不要求它们线性无交。

这些局部条件的总体框架已有明确先例：Sonn，arXiv:math/0612528v4，Proposition 2.1 用完整分解群包含于点稳定子的条件描述处处局部根；Theorem 2.2 通过可解群的局部循环实现给出一般存在性。Jahnel–Loughran 的 Lemmas 2.7–2.8 给相应有限 étale 反例与二次互反构造。Dummit–Kisilevsky，arXiv:1707.02493v1，Definition 3.3 与 Theorem 3.4 将分歧处惯性群等于分解群称为 tame split decomposition configuration，并给阿贝尔群的实现；Kim–König，arXiv:1911.08742v3，Theorem 5.1 归于 Shafarevich 的一般可解实现也提供局部循环性。这里的 (98.1) 及 (96.11) 是把这些既有机制直接落实到指定原生成元和三个指定分歧地方，未借用一般实现定理更换 $D$。

下面固定一个 (96.8) 的 $D$，构造只依赖它及 $p_1,h_1$ 的类。由 $H_{p_1}=\langle h_1\rangle$ 以及 $E=D^{\langle h_1\rangle}$，

$$
E\otimes_{\mathbb Q}\mathbb Q_{p_1}
\simeq\mathbb Q_{p_1}^{4}.
\tag{98.2}
$$

令 $S_E$ 为 $E$ 中 $p_1$ 上方的全部四个地方。每个 $w\in S_E$ 都是有限地方，$E_w=\mathbb Q_{p_1}$。对 $E$ 的每个地方指定局部类 $a_w$，使

$$
\operatorname{inv}_w(a_w)=
\begin{cases}
1/2,&w\in S_E,\\
0,&w\notin S_E.
\end{cases}
\tag{98.3}
$$

有限地方的不变量同构唯一确定这些局部类；实地方指定零类，复地方也为零。它们仅有四项非零，且

$$
\sum_{w\in\operatorname{Val}(E)}\operatorname{inv}_w(a_w)
=4\cdot\frac12=2=0\quad\text{于 }\mathbb Q/\mathbb Z.
\tag{98.4}
$$

采用 Albert–Brauer–Hasse–Noether 定理，精确出处为 Milne，*Class Field Theory* v4.03，Chapter IV，Example 2.14(d),(e)。其对数域 $E$ 的正合列为

$$
0\longrightarrow\operatorname{Br}E
\longrightarrow\bigoplus_w\operatorname{Br}E_w
\xrightarrow{\ \sum_w\operatorname{inv}_w\ }\mathbb Q/\mathbb Z
\longrightarrow0.
\tag{98.5}
$$

正合性与 (98.4) 给存在性，左端单射给唯一性，故恰有 (96.13) 的 $\alpha$。它非零，因为四个局部不变量非零；又 $2\alpha$ 的全部局部不变量为零，故 $2\alpha=0$。

为得到次数二代表，使用 Voight，*Quaternion Algebras* v1.0.5 的 **Main Theorem 14.6.1**：对任意全局域，四元数代数的同构类与非复地方的有限偶数基数分歧集合一一对应。$E$ 是数域，$S_E$ 是由四个非复地方构成的有限集合，故有一个 $E$ 上的四元数代数 $B$，其分歧集合恰为 $S_E$。四元数的局部分歧类不变量为 $1/2$，局部分裂类不变量为零，因此 $[B]$ 与 $\alpha$ 的全部局部像一致；由 (98.5) 的单射，$[B]=\alpha$。这里应用的是任意全局域的 14.6.1，适用底域是四次域 $E$；只针对 $\mathbb Q$ 的 14.1.3 不能替代它。

现在在实际分解 (96.10) 上定义 Azumaya 代数

$$
\mathcal A|_{\operatorname{Spec}E}=B,
\qquad
\mathcal A|_{\operatorname{Spec}E_h}=M_2(E_h)\quad(h\ne h_1).
\tag{98.6}
$$

这些是不交分支上的代数，因而唯一组成 $P$ 上的 Azumaya 代数；每个分支的模秩均为四，次数均为二。令 $\beta=[\mathcal A]$，便是 (96.14) 的一个确定的二阶类。

任取 $x=(x_v)\in P(\mathbb A_{\mathbb Q})$，保持上述 $\beta$ 不变。§97 已证明，$p_1$ 处只有 $\operatorname{Spec}E$ 分支可见，其四个 $\mathbb Q_{p_1}$-点分别对应 $S_E$ 的四个地方。无论 $x_{p_1}$ 选哪一点，(98.3) 都给

$$
\operatorname{inv}_{p_1}\beta(x_{p_1})=1/2.
\tag{98.7}
$$

对 $v\ne p_1$，若 $x_v$ 落在其他分支，(96.14) 直接给零；若落在 $\operatorname{Spec}E$，该点对应一个满足 $E_w=\mathbb Q_v$ 的地方 $w\mid v$，而 $w\notin S_E$，所以也给零。因此

$$
\operatorname{inv}_v\beta(x_v)=
\begin{cases}
1/2,&v=p_1,\\
0,&v\ne p_1,
\end{cases}
\qquad
\langle x,\beta\rangle=1/2
\quad\text{对所有 }x.
\tag{98.8}
$$

(98.4) 在 $E$ 的全部地方上求和，包含 $p_1$ 上方的四项；(98.8) 在 $\mathbb Q$ 的地方上求和，一个局部点在 $p_1$ 处只选择其中一个 $E_w=\mathbb Q_{p_1}$ 分支。四个候选值全部相等，使这个单次选择无论如何都给 $1/2$。这正是两种求和相容、而配对仍恒非零的原因。

非恒定性也从同一读数得出。若 $\beta$ 是某个 $b\in\operatorname{Br}\mathbb Q$ 的结构拉回，则对任一 adelic 点 $x$，都有 $\beta(x_v)=b|_{\mathbb Q_v}$。将 (98.5) 用于 $\mathbb Q$，互反律给

$$
\langle x,\beta\rangle=\sum_v\operatorname{inv}_v b=0,
\tag{98.9}
$$

与非空 adelic 集合上的 (98.8) 矛盾。故 $\beta\notin\operatorname{Br}_0P$。这一论证判定的是整个分支元组 $\beta$，没有断言 $\alpha$ 本身不能由 $\operatorname{Br}\mathbb Q$ 限制而来。

同样由互反律，有理点的对角 adelic 像必与任一 Brauer 类正交。因此 (98.8) 也独立说明 $P(\mathbb A_{\mathbb Q})^\beta=\varnothing$，并解释其无有理点。Jahnel–Loughran 的 Remark 2.6 已给出有限 étale 概形失去 Hasse 原理时的一般 Brauer–Manin 解释；其中先给一个 adelic 点，再选择用来排除该点的类。本证明所需的量词更强，已由 (98.2)–(98.8) 单独完成：先固定 $\beta$，再对所有 $x$ 得到同一个非零值，未从一般解释中交换这两个量词。

## 99. 同一个实际目标与窗口中的强制节点传送

定理 96.3 的证明，第三部分。对每个已经构造的原 $D$，直接使用 source033 定理 85.7：在 $X_D$ 中有非空 $\mathbb Q$-开集，其实际点同时满足统一行条件及 (96.5)。该定理还可同时给 $C^2=D$；这里不用这一附加性质。取其中一个实际目标 $C$，便满足 source034 约定 86.1 的全部目标假设。这个存在性调用保留两个独立条件，未以统一性推出系数像点光滑，也未将 source033 命题 85.6 的特殊一参数目标族当作光滑性见证；其 §85.8 指明的特殊族光滑性缺口不承担这里的推理。

对任何如此固定的 $C$，source034 定理 89.3 给原窗口空间 $X_D$ 中的非空 $\mathbb Q$-开集 $\mathcal U_C=\mathcal U_{\mathrm{node}}$。在这个开集上，$[P_W]\ne[P_C]$，原行列式截面非零，$T_W$ 几何整且几何正规，二十八个原对处同时满足该卷定义 89.1 的结构化节点条件。此处复用的是同一个实际参数开集的非空性；没有从任意一组分裂行另造一个窗口。

还须明确这一开集给出实际 $W$。$X_D$ 有定义在 $\mathbb Q$ 上的稠密 Grassmann 大胞腔 $\mathbb A_{\mathbb Q}^{16}$，它与 $\mathcal U_C$ 相交为非空开集。交中含一个由非零有理系数多项式的非消失定义的主开集；非零多项式在无限域 $\mathbb Q$ 上不能处处为零，故该交有 $\mathbb Q$-点。于是可以在考察任何地方点之前，选择一次 $W\in\mathcal U_C(\mathbb Q)$。事实上同一论证适用于其任何非空 $\mathbb Q$-开子集，且以下结论对全部这些实际窗口成立。这是存在性论证，不提供搜索的有效性或高度界。

对这样选定的 $C,W$，(96.6) 中两边向量丛的秩均为八，乘法就是原域的 $uw$。source034 约定 86.1 将其行列式识别为目标 Grassmannian 上的指定测试除子。$\dim\mathcal G_C=4$，所以非零 Cartier 除子 $T_W$ 维数为三。定理 89.4 给全部强制几何点的非退化四元二次初始式；在代数闭包上，它们的完备局部环为

$$
\overline{\mathbb Q}[[z_1,z_2,z_3,z_4]]/(z_1z_2-z_3z_4).
\tag{99.1}
$$

source034 定理 90.2 进一步保证 (96.7) 是原 $\mathbb Q$ 上的闭浸入，且为 $P$ 到其强制节点像 $N_C$ 的概形同构。这里每个几何点正是原 $\{\sigma,\tau\}$ 的共同核；没有改换成另一个有限覆盖，也没有把节点重新贴到一个不同的测试除子上。

同构的逆像传送使 (96.15) 良定义，并把 $\mathcal A$ 传成 $N_C$ 上的次数二 Azumaya 代数。对任一 $z_v:\operatorname{Spec}\mathbb Q_v\to N_C$，令 $x_v=\nu_C^{-1}\circ z_v$，则 Brauer 拉回的函子性给

$$
z_v^*\beta_C=x_v^*\beta.
\tag{99.2}
$$

同构同时给所有地方点、adelic 点及有理点的双射。因此 §98 的非空局部集、非空 adelic 集、无有理点以及 (98.8) 的恒定非零配对，逐项传到原节点概形 $N_C$。若 $\beta_C$ 为常数拉回，沿 $\nu_C$ 拉回就使 $\beta$ 为常数拉回，矛盾。故 $\beta_C$ 非恒定。

$P$ 只依赖 $D$；$N_C$ 与 $\nu_C$ 只依赖 $D,C$；$\beta$ 只依赖固定的算术选择 $p_1,h_1$；因此 $\beta_C$ 在整个 $\mathcal U_C$ 上与 $W$ 无关。所有局部点是在同一个选定的 $T_W$ 上取值，其共同的强制节点概形没有随地方改变。结合原域族的无穷性，定理 96.3 的全部存在量词、统一量词和配对量词均得到证明。$\square$

**定义 99.1（本定理的障碍所在）。** 定理 96.3 的类所在是 $\operatorname{Br}P$ 与经 (96.7) 同构的 $\operatorname{Br}N_C$。闭浸入 $N_C\hookrightarrow T_W$ 只给出限制映射 $\operatorname{Br}T_W\to\operatorname{Br}N_C$，不提供反向延拓。因此该定理不包含 $\beta_C$ 延拓到 $\operatorname{Br}T_W$ 的断言，其空集结论指 $N_C(\mathbb Q)$ 和 $N_C(\mathbb A_{\mathbb Q})^{\beta_C}$，不指 $T_W(\mathbb Q)$ 或整个 $T_W$ 的 adelic 正交集。其几何输入只识别强制节点子概形，不将其认作完整奇异 locus。

同样，[source032 定义 76.1](https://github.com/the-omega-institute/trureturing/blob/57d62a7f36041958c458ba04858a5d6a147f8b90/docs/develop/theory/AURIC_R5_032_RELATIVE_BRAUER_ACTUAL_LIFTING.md) 的相对圆锥类属于 $\ker(\operatorname{Br}(\mathbb Q)[2]\to\operatorname{Br}(D)[2])$；本卷的 $\beta$ 属于七个实际四次分支的 Brauer 群乘积，并且不在常数拉回像中。两者的底概形与作用问题不同，不作同一类的识别。

## 100. 原强制节点的一致障碍：完整白话定理

**定理 100.1（处处能选节点，而一个固定四元数规则排除所有全局拼合）。** 取正素数 $p_1,p_2,p_3$，分别满足“除以八余一”“除以 $8p_1$ 余一”“除以 $8p_1p_2$ 余一”，并取原来的域 $D=\mathbb Q(\sqrt{p_1},\sqrt{p_2},\sqrt{p_3})$。在这个八次域中，存在一个实际四维目标，使八个原嵌入在它上面的任意四行独立，并且它的原乘法系数点位于系数像的光滑部分。固定任一这样的目标后，可在原域中一次选定一个实际四维竞争窗口，使原乘法在目标二平面 Grassmannian 上的行列式除子几何整、正规，而且由两个原嵌入共同消失强制产生的二十八个几何点全部为普通二重点。

这二十八个强制节点作为整体，是原来八个域嵌入的无序不同二元对概形，与七个实际四次固定子域的谱的不交并同构。在每个有理数完备化上，都能从同一组节点中选到局部有理节点；完整分解群平凡时有二十八种选择，完整分解群非平凡时在本族恰为二阶，有四种选择，而且全部在唯一对应的四次分支中。尤其在 $p_i$ 处，完整分解群和惯性群就是只翻转 $\sqrt{p_i}$ 符号的原自同构所生成的群。三个指定素数是全部有限分歧素数；在二进与实地方八个原嵌入全分裂。因而节点的 adelic 集合非空，但没有任何一个强制节点能成为有理数域上的点。

更强的是，可以在选择所有局部节点之前，先固定一个次数二 Azumaya 代数类：在实际四次域 $\mathbb Q(\sqrt{p_2},\sqrt{p_3})$ 分支，取恰在 $p_1$ 上方四个地方分歧、其余地方全分裂的四元数类；在另外六个分支取分裂矩阵代数。把它沿原节点同构传送到强制节点概形，就得到一个非恒定的 Brauer 类。无论在各个完备化上怎样选择节点，其局部不变量在 $p_1$ 处总为二分之一，其余地方总为零。因此每个 adelic 节点选择的总配对都是二分之一，被这同一个类排除。四次域中四个二分之一相加满足互反律；这里一个局部节点在 $p_1$ 处只选中其中一个分支，所以不与互反律冲突。

固定前两个素数而让第三个素数变化，存在无穷多个两两不同构的原八次域，以上结论对每个都成立。对每个固定目标，强制节点概形及这个障碍类在一个非空有理窗口开集上都保持不变。结论是关于原除子内部指定强制节点的局部与全局差异，以及其全部 adelic 点受到的一个共同障碍；不据此排除除子其他位置的有理点，也不要求该类能延拓到整个除子。

证明。定理 96.3 给原域族、实际目标及同一个实际窗口开集。其 §97 证明将原无序对的完整分解群不动点读数落实为七个实际四次分支；§98 证明每个分歧和非分歧地方的局部结构，并在全部四个 $p_1$ 分支上同时指定二分之一的不变量；§99 只沿原共同核的概形同构传送这个类及其评价。这些步骤保持同一原 $D$、同一实际 $C,W$ 和同一有限节点概形。配对非零对所有局部选择同时成立，故不是逐个选择节点之后再改变四元数类。原域无穷性由不同第三素数给出的不同分歧集合保证。$\square$

定理 96.3 与定理 100.1 的数学归属为 `repo-derived` 的实际族综合推导：在原乘法的同一个强制节点子概形上，联结原分解群、七个实际固定域、递归素数的完整局部数据以及一个选择无关的四元数评价。有限 étale 的局部—整体框架、局部循环扩张的存在框架、Brauer 互反律和四元数分类均为 `literature-attested`，只作为上述定理证明中的中间输入，不作为新的经典定理发表；这里不作全球原创性声明。精确引用及承担的步骤如下。

| 数学来源 | 在同一实际族证明中承担的范围 |
| --- | --- |
| [source033，§81、定理 85.7 与 §85.8](https://github.com/the-omega-institute/trureturing/blob/974984733cb1d619221ff97000612a9194bc8828/docs/develop/theory/AURIC_R5_033_ALL_DEGREE_ARITHMETIC_POSITIVE_CERTIFICATES.md) | 原系数空间、系数像和实际目标存在性；统一性与系数像点光滑性同时可满足。特殊一参数目标族的光滑性不作为前提。 |
| [source034，约定 86.1、定理 89.3、89.4、90.2](https://github.com/the-omega-institute/trureturing/blob/cb61604ce58708feb5f804ed1f9370dd48acca48/docs/develop/theory/AURIC_R5_034_NORMAL_ANTICANONICAL_TESTS_AND_FORCED_NODES.md) | 保留全部目标假设的原乘法行列式族、实际非空节点开集、普通二重点及原无序对到强制节点像的闭浸入和同构。 |
| Stacks Project，[Tag 0BNE](https://stacks.math.columbia.edu/tag/0BNE)；Jahnel–Loughran，[arXiv:1410.5671v2，Lemmas 2.1、2.2](https://arxiv.org/pdf/1410.5671v2) | 有限 étale–Galois 对应、完整分解群的局部不动点判据、Chebotarev 的几乎处处判据；在本证明中用于原二元子集并导出 (97.4)–(97.6)。 |
| Jahnel–Loughran，同文 Lemmas 2.7、2.8、Remark 2.6 | 局部循环实现与二次互反构造的先例，以及有限 étale Brauer–Manin 障碍的一般解释。Remark 2.6 的逐 adelic 点选类不代替 (98.8) 的单个固定类全称证明。 |
| Sonn，*Polynomials with roots in $\mathbb Q_p$ for all $p$*，[arXiv:math/0612528v4，Proposition 2.1、Theorem 2.2](https://arxiv.org/pdf/math/0612528v4) | 完整分解群包含于点稳定子的局部根判据与可解群的局部循环实现框架。 |
| Dummit–Kisilevsky，*Decomposition configuration types in minimally tamely ramified extensions of $\mathbb Q$*，[arXiv:1707.02493v1，Definition 3.3、Theorem 3.4 及其前的证明](https://arxiv.org/pdf/1707.02493v1)；Kim–König，*On Galois extensions with prescribed decomposition groups*，[arXiv:1911.08742v3，Theorem 5.1](https://arxiv.org/pdf/1911.08742v3) | 惯性等于完整分解群的分歧配置、阿贝尔及一般可解群局部循环实现的既有框架。指定素数族的全部局部计算由 (98.1) 给出；无穷不同构不借用固定前两素数时的线性无交性。 |
| Milne，*Class Field Theory*，[v4.03，Chapter IV，Example 2.14(d),(e)](https://www.jmilne.org/math/CourseNotes/CFT.pdf) | 局部 Brauer 不变量与 Albert–Brauer–Hasse–Noether 正合列，给 (96.13) 的存在唯一性及常数类的互反律零配对。实、复地方采用该章相邻的经典 Brauer 群描述。 |
| Voight，*Quaternion Algebras*，[v1.0.5，Main Theorem 14.6.1](https://jvoight.github.io/quat-book-v1.0.5.pdf) | 任意全局域上，有限偶数个非复地方恰为一个四元数代数的分歧集合；用于四次域 $E$ 上的次数二代表。 |
| Dirichlet 算术级数素数定理、二次互反律、Hensel 引理及 $2$ 进单位平方判据 | 保证递归素数的无穷选择，验证不同原生成元在指定分歧地方已为平方，以及二进完全分裂；均是 (96.8) 的经典算术输入。 |

## 追加锚（本行以下为增补区）

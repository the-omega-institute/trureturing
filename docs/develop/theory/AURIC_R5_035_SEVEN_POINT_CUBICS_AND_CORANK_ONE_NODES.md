# 七点三次桥与原域八次族的二十四个余秩一结点

## 91. 固定实际域、原嵌入与标记七点问题

**定义 91.1（固定对象与原八次除子）。** 设 $F$ 为特征零域，$D/F$ 为固定的实际可分域扩张，$[D:F]=8$。固定原 $F$-基、体积形式及实际四维目标 $C\subset D$。令 $K=\overline F$，按八个原嵌入分裂 $D_K=K^8$。取 $C$ 的帧，记评价行为 $c_1,\ldots,c_8\in C_K^\vee$，假设任意四行独立。以下所有竞争窗口均来自同一个

$$
\mathscr B=\operatorname{Gr}_F(4,D),
\qquad G=\operatorname{Gr}_F(2,C).
\tag{91.1}
$$

对窗口 $W$ 置 $E_W=W^\vee$。第 $j$ 个原嵌入在 $W_K$ 上的评价记为 $\varepsilon_j\in E_{W,K}$；它是对偶空间中的向量。窗口帧的第 $j$ 行 $w_j$ 是这个泛函的坐标行，$\varepsilon_j$ 的列坐标为 $w_j^{\mathsf t}$。称 $W$ 统一，如果任意四个 $\varepsilon_j$ 独立。统一性给出 $\mathscr B$ 的非空 $F$-开集 $\mathscr B^{\mathrm u}$。

沿用 [source033 的固定版本，§§81–83](https://github.com/the-omega-institute/trureturing/blob/2effd40af56f54ba1456685325be516b1bd311eb/docs/develop/theory/AURIC_R5_033_ALL_DEGREE_ARITHMETIC_POSITIVE_CERTIFICATES.md) 的

$$
P_W(x)=\det[B_W,M_xB_W],\qquad
T_W=V(s_{P_W})\subset G,
\tag{91.2}
$$

其中 $M_x$ 是原域乘法。若 $U\in G_K$ 的帧为 $(u,v)$，则定义 $T_W$ 的原矩阵为

$$
K_U=[\operatorname{diag}(u)B_W,\operatorname{diag}(v)B_W].
\tag{91.3}
$$

由 source033 的 (83.4)，$\det K_U$ 与 $s_{P_W}(U)$ 只差固定非零常数。这是 [source031 定理 72.3](AURIC_R5_031_TARGET_OWNED_POSITIVE_GRASSMANN_GEOMETRY.md) 的指定 Grassmann 线性系，截面属于 $\mathcal O_G(4)$；在 Plücker 嵌入中 $G$ 是 $\mathbb P^5$ 的光滑二次超曲面，所以非零的 $T_W$ 是次数八的三维除子。这里的八次族始终是 (91.2)，不是任意矩阵丛映射的退化族。

本卷仅要求固定 $C$ 统一。source033 假设 81.2 另有 $[P_C]\in(\Gamma_D)_{\mathrm{sm}}(F)$；其 §85 还讨论 $C^2=D$、数域和 Hilbert 特化。这些更强条件在下述结点及下降定理中均不使用。若目标同时满足它们，以下结论当然仍适用。所需重合输入是指定线性系、完整核关联以及 (83.6) 的核图同构。

**定义 91.2（完整关联与标记空间）。** 对统一 $W$，令

$$
Y_W=\{[A]\in\mathbb P\operatorname{Hom}_K(E_{W,K},C_K):
\operatorname{rank}A\le2,\quad c_jA\varepsilon_j=0\ (1\le j\le8)\}.
\tag{91.4}
$$

其非零映射全为秩二：若 $A=a\otimes b$ 为秩一，$c_ja=0$ 至多占三个指标，$b(\varepsilon_j)=0$ 也至多占三个，不能覆盖八个方程。因此取像给出 source033 引理 83.1 的态射 $Y_W\to T_W$，其在 $U$ 上的完整概形纤维为 $\mathbb P(\ker K_U)$。

对一个原标记 $i$ 定义

$$
H_i=\ker c_i\subset C_K,\quad
V_i=E_{W,K}/K\varepsilon_i,\quad
G_i=\operatorname{Gr}(2,H_i),\quad
X_i=\mathbb P_{G_i}(\operatorname{Hom}(V_i,\mathcal S_i)),
\tag{91.5}
$$

其中 $\mathcal S_i$ 为秩二 tautological 子丛。射影化取一维子空间约定，$\mathcal O_{X_i}(-1)$ 是 tautological 线；$\dim G_i=2$，$\dim X_i=7$。置

$$
\alpha_j=c_j|_{H_i}\in H_i^\vee,\qquad
v_j=\varepsilon_j\bmod K\varepsilon_i\in V_i\quad(j\ne i).
\tag{91.6}
$$

任意三个 $\alpha_j$ 独立；统一 $W$ 还使任意三个 $v_j$ 独立。$X_i$ 上的七个结构除子为

$$
D_j=V(\alpha_jBv_j),\qquad j\ne i,
\tag{91.7}
$$

这里 $[B:V_i\to U]$ 为射影丛的点，$U\in G_i$。七方程给出闭概形 $Z_i$。它保留全部原乘法方程：标记方程 $c_iA\varepsilon_i=0$ 自动成立，另外七个正是 (91.7)；对应的 $A$ 是 $E_{W,K}\twoheadrightarrow V_i\xrightarrow B U\hookrightarrow C_K$。

**定义 91.3（避让集合及已指定的两点平面）。** 识别

$$
G_i=\mathbb P(H_i^\vee),\qquad U=\ker n.
$$

对 $j,l\ne i$、$j\ne l$，置

$$
\mathcal L_{jl}=\mathbb P\langle\alpha_j,\alpha_l\rangle\subset G_i.
\tag{91.8}
$$

这是 $c_j|_U,c_l|_U$ 线性相关的精确条件：$H_i^\vee\to U^\vee$ 的核为 $Kn$，而 $\alpha_j,\alpha_l$ 独立。它包括某一限制为零的情形。需要避让的边界为 $\operatorname{rank}B\le1$、$U\in\bigcup\mathcal L_{jl}$ 及 $Bv_j=0$。八个平面 $G_i\subset G_K$ 两两相交于

$$
U_{ab}=H_a\cap H_b\in G_K\qquad(a<b).
\tag{91.9}
$$

这二十八点彼此不同：若不同指标对给同一二平面，至少三个独立的 $c$ 行都会在该平面上消失，但三个核的交仅为一维。每个 $U_{ab}$ 都在 $T_W$ 上，因为 (91.3) 的第 $a,b$ 行为零。下文的“额外”仅指与这些已指定点不相交。

## 92. 固定七个左行的三次交与实际避让

**定理 92.1（固定左行的七点桥）。** 设 $k$ 是特征零代数闭域，$H,V$ 为三维空间，固定七个 $\alpha_j\in H^\vee\setminus0$，其中任意三个独立。令

$$
X=\mathbb P_{\operatorname{Gr}(2,H)}\operatorname{Hom}(V,\mathcal S).
$$

在 $(\mathbb P(V))^7$ 中存在非空开集 $\mathcal Q_\alpha$，使其每个七元组 $(v_j)$ 满足：任意三个 $v_j$ 独立；七个除子 $\alpha_jBv_j=0$ 的完整概形交是三个不同的约化点；这些点全为秩二，像平面互不相同，且均避开定义 91.3 的所有边界。结论对每组已固定的统一左行成立。

证明。先计算经典交数，但暂不由此断言交的适当性。令 $h=c_1(\mathcal S^\vee)$；在 $\operatorname{Gr}(2,H)\simeq\mathbb P^2$ 上

$$
c(\mathcal S)=1-h+h^2,\qquad \int h^2=1.
$$

对 $\mathcal E=\operatorname{Hom}(V,\mathcal S)\simeq\mathcal S^{\oplus3}$ 有

$$
c_1(\mathcal E)=-3h,\qquad c_2(\mathcal E)=6h^2.
$$

若 $\xi=c_1(\mathcal O_X(1))$，射影丛公式因而给

$$
\int_X\xi^7
=\int_{\mathbb P^2}\bigl(c_1(\mathcal E)^2-c_2(\mathcal E)\bigr)=3.
\tag{92.1}
$$

这里使用经典射影丛公式及 Chern 关系，见 Stacks [02TX](https://stacks.math.columbia.edu/tag/02TX)、[02U6](https://stacks.math.columbia.edu/tag/02U6)。这些文献取商线约定，故在应用时使用其 $\mathcal E^\vee$，与此处子线约定一致。具体地，秩六关系为 $\xi^6+c_1(\mathcal E)\xi^5+c_2(\mathcal E)\xi^4+\cdots=0$；纤维积分 $\pi_*\xi^5=1$ 给 $\pi_*\xi^6=-c_1(\mathcal E)$ 和 $\pi_*\xi^7=c_1(\mathcal E)^2-c_2(\mathcal E)$。式 (92.1) 只说明交循环次数，尚不说明七个指定除子给有限约化交。

秩一可以直接排除：若 $B=a\otimes b\ne0$，方程为 $(\alpha_ja)b(v_j)=0$。左边第一因子至多在两个指标为零；当任意三右行独立时，第二因子也至多在两个指标为零，不能覆盖七个指标。以下构造同时保证右行统一及其他所有要求，左行始终固定。

记 $a_j=[\alpha_j]\in\mathbb P(H^\vee)$。七个 $a_j$ 对三次齐次式施加七个独立条件：对任意 $a_j$，将其他六点分成三对，三条连接线均不经过 $a_j$，其方程乘积在其他六点为零而在 $a_j$ 非零。因此通过七点的三次式向量空间 $\mathcal C$ 恰为三维。

可取三个有序点 $n_1,n_2,n_3\in\mathbb P(H^\vee)$，使下列条件同时成立：三点不共线；它们不在任何 $\overline{a_ja_l}$ 上；任一 $a_j$ 不在任一 $\overline{n_an_b}$ 上；以及

$$
\mathcal C\longrightarrow\bigoplus_{a=1}^3\mathcal O(3)|_{n_a}
\quad\text{是同构}.
\tag{92.2}
$$

还可以同时要求，对任意三个原点 $a_j,a_l,a_r$，不存在通过这三点及 $n_1,n_2,n_3$ 的非零二次式。

逐一说明非空性。对任意三维的非零齐次式空间，可依次选点：第一个点使评价非零，第二个点使第一次评价的二维核上评价非零，第三个点使剩余一维核上评价非零。这证明三个评价独立的条件是非空开条件，适用于 $\mathcal C$。对任意固定三点 $a_j,a_l,a_r$，通过它们的二次式空间也恰为三维：逐点用两条不经过该点的直线乘积分离这三点评价。因此同一选点论证给出二次式所需的非空开条件。其余有限个不共线和不落线条件各自也是非空开条件。参数空间 $(\mathbb P^2)^3$ 不可约，故这些有限个非空开集有非空交。这证明上述同时选择，未对固定的 $a_j$ 作一般性假设。

以 $n_1,n_2,n_3$ 为坐标点，写 $a_j=(x_{1j}:x_{2j}:x_{3j})$。各 $x_{aj}$ 均非零。选 $V$ 的坐标，定义

$$
v_j=(x_{2j}x_{3j},\ x_{1j}x_{3j},\ x_{1j}x_{2j})^{\mathsf t},
\qquad
\ell=\{B(s,t)=\operatorname{diag}(s,t,-s-t)\}.
\tag{92.3}
$$

这是标准二次 Cremona 变换与其矩阵铅笔。该变换的经典公式见 Connelly–Thomas–Vinzant，[arXiv:2308.02757v2](https://arxiv.org/abs/2308.02757v2)，§2.1 的 (1)；矩阵铅笔和左右基点的对应见其 Lemmas 3.7、3.9。此处直接证明固定左行所需的评价性质。

若三个 $v_j$ 共线，存在非零 $(b_1,b_2,b_3)$，使二次式

$$
b_1x_2x_3+b_2x_1x_3+b_3x_1x_2
$$

在相应三个 $a_j$ 处为零。它还在 $n_1,n_2,n_3$ 处为零，与选择矛盾。因此任意三个 $v_j$ 独立。

七个线性方程 $\alpha_jBv_j=0$ 在九维矩阵空间中独立。事实上，其九个系数位置作为 $a_j$ 的函数，仅出现七个不同三次单项式：$x_1x_2x_3$ 及六个 $x_a^2x_b$（$a\ne b$）。它们张成通过三个坐标点的全部三次式，维数七。若它们在七个 $a_j$ 的评价不独立，就有非零三次式同时通过七个 $a_j$ 和三个 $n_a$，这与 (92.2) 矛盾。又逐项代入 (92.3) 得 $\alpha_jB(s,t)v_j=0$，所以七方程的共同射影核恰为 $\ell\simeq\mathbb P^1$。

在这条直线上

$$
\det B(s,t)=-st(s+t).
\tag{92.4}
$$

因此它与三阶行列式超曲面的概形交恰为三个单点，均为秩二。三者的左核分别为 $n_1,n_2,n_3$，故像平面不同，并避开所有 $\mathcal L_{jl}$。各 $v_j$ 的三个坐标均非零，每个根矩阵有两个非零对角元，所以在每个根处 $Bv_j\ne0$。

映射 $X\to\mathbb P\operatorname{Hom}(V,H)$ 忘去像平面，其像为秩至多二的行列式超曲面；在秩二开层是同构，逆映射为取像。对上述参数，三个交点均在此开层，七个除子的交概形便是 (92.4) 的三个约化点，没有其他点。于是交是适当的，长度为三；在光滑七维 $X$ 的每个交点处，七个局部方程的微分独立。也可由局部商为域看出：七个方程生成极大理想，其线性项必张成七维余切空间。

最后说明这些性质确实保持在右行参数的非空开集上。七个线性方程独立是子式开条件；其二维核形成矩阵铅笔丛。行列式在这个铅笔上非恒零且有三个单根是非零判别式条件。秩一、$U\in\bigcup\mathcal L_{jl}$、$Bv_j=0$ 都是 $X\times(\mathbb P(V))^7$ 中的闭条件；对闭的通用交限制后，其参数像因 $X$ 射影而闭。移走这些像，再与任意三右行独立的开集取交，得到包含上述参数的 $\mathcal Q_\alpha$。每个参数的交仍是三个约化秩二点。

若这三个点中两个具有同一像 $U$，线性空间 $\mathbb P\{B:V\to U:\alpha_jBv_j=0\}$ 就至少含一条射影直线，全在七除子的交中，违反有限性。这也给出不依赖所选坐标的像互异证明。$\square$

式 (92.4) 的三次行列式与经典七点算法的次数三是同一经典事实，见 Agarwal–Lee–Sturmfels–Thomas，[arXiv:1510.01401v1](https://arxiv.org/abs/1510.01401v1)，§1.5、(2.1)–(2.4)、§2.3。其 Example 2.1 的铅笔满足 $\det(sI+tA)=(s+5t)^3$，唯一退化矩阵为秩一；所以次数三本身既不排除秩一，也不保证约化。本定理的固定左行评价构造、边界避让和后续实际提升承担这些额外结论，而不把经典三次次数作为新结论。

## 93. 受限秩五、匹配子式与同一实际窗口开集

**定理 93.1（精确提升判据）。** 固定标记 $i$，取定理 92.1 的一个七元组 $(v_j)$ 和其中任一解 $[B:V_i\to U]$。选择 $U$ 的基，写

$$
r_j=\alpha_j|_U=(a_j,b_j),\qquad
L=(r_j\otimes v_j^{\mathsf t})_{j\ne i}.
\tag{93.1}
$$

则 $L$ 是秩恰为五的 $7\times6$ 受限行矩阵。取其左核的任一基，组成秩二矩阵

$$
\Lambda=\begin{pmatrix}p_1&\cdots&p_7\\q_1&\cdots&q_7\end{pmatrix},
\qquad \Lambda L=0;
\tag{93.2}
$$

此处七个位置按 $j\ne i$ 的顺序排列，$q_l$ 可以为零。以 $E=Ke_0\oplus V_i$，$\varepsilon_i=e_0$，对七个实际行的提升写

$$
\varepsilon_j=t_je_0+v_j.
\tag{93.3}
$$

记 $R$ 为七行 $r_j$ 组成的 $7\times2$ 矩阵。则原 $K_U$ 秩七的充要条件恰为

$$
\det M_B(t)\ne0,\qquad M_B(t)=\Lambda\operatorname{diag}(t_j)R,
\tag{93.4}
$$

并有不需任何坐标相除的恒等式

$$
\det M_B(t)=
\sum_{j<l}(p_jq_l-p_lq_j)(a_jb_l-a_lb_j)t_jt_l.
\tag{93.5}
$$

这是非零多项式。对七点交的全部三个解，可以同时选择提升，使所有原行统一且所有三个原矩阵 $K_U$ 均秩七。

证明。$L$ 的核包含 $B$。若核维数大于一，其射影化将给出七除子交中的正维线性空间，像平面固定为 $U$，与定理 92.1 的有限性矛盾。因此 $\dim\ker L=1$，$\operatorname{rank}L=5$。

将 $\operatorname{Hom}(E,U)$ 的变量分成 $\operatorname{Hom}(V_i,U)$ 的六个变量与 $z=Ae_0\in U$ 的两个变量。$K_U$ 的第 $i$ 行为零，剩余七行所定义的线性映射，在列置换后正是

$$
[L\mid\operatorname{diag}(t_j)R].
\tag{93.6}
$$

矩阵 $\Lambda$ 的核是 $\operatorname{im}L$：二者维数都为五，且前者包含后者。因此 (93.6) 满行秩七，恰当且仅当其末两列到 $K^7/\operatorname{im}L$ 的映射为同构，也就是 (93.4)。这不仅是一个充分条件。

对两个矩阵列作二阶 Cauchy–Binet 展开即得 (93.5)。因为 $U$ 避开所有比例线，任意两个 $r_j,r_l$ 独立，故每个 $a_jb_l-a_lb_j$ 均非零。$\Lambda$ 秩二，至少有一对列的 $p_jq_l-p_lq_j$ 非零；相应单项式的系数非零，且不同指标对给不同单项式。因此整个多项式非零。这个论证容许任意若干 $q_l=0$，也不要求每列 $\Lambda_l$ 非零；只使用一个非零匹配子式，绝不通过除以某个 $q_l$ 排除合法情形。同样，不要求 $v_j$、$r_j$ 的每个坐标或每个 $t_j$ 非零；完整判据只涉及所列秩与子式。换 $\Lambda$ 的基仅使行列式乘非零常数。

还须检验 (93.3) 是原四维行空间中的统一行。包含 $\varepsilon_i$ 的任意四行独立，正由对应三个 $v_j$ 独立保证。对不含 $i$ 的任意四元集 $J$，四阶行列式为

$$
\sum_{j\in J}\pm t_j\det(v_l:l\in J\setminus\{j\}).
\tag{93.7}
$$

每个系数都非零，所以这是非零的一次多项式。将这些有限个多项式与三个解各自的非零 (93.5) 相乘，在整环 $K[t_j:j\ne i]$ 中仍非零。无限域中其非零开集非空。在这个同一个开集选取 $t$，便同时得到统一原行与全部三个解的秩七。这些八个向量组成一个秩四 $8\times4$ 帧，给出原窗口参数空间 $\mathscr B_K$ 的几何点，而非另一个不相关的矩阵族。此处用于证明原参数开集非空；实际 $F$-窗口由下一定理取得。$\square$

**定理 93.2（全部原标记共用的非空原域开集）。** 对定义 91.1 中每一个固定统一目标 $C$，存在非空 $F$-开集

$$
\mathscr B^\circ\subset\mathscr B^{\mathrm u}
\tag{93.8}
$$

使 $s_{P_W}\ne0$，且对其上每个几何窗口 $W$ 和全部八个原标记 $i$，$Z_i$ 都是有限约化长度三的横截交，满足定理 92.1 的全部避让，三个像互异，并且其每个像处的原矩阵 $K_U$ 秩七。此开集含几何稠密的实际 $F$-窗口。

证明。先在 $K$ 上固定一个 $i$。在原八行帧空间中，$\varepsilon_i\ne0$；局部选基将其化为 $e_0$，其余行可用 (93.3) 表示。商向量七元组任意变化；定理 92.1 给出其非空好开集，定理 93.1 说明每个好七元组上都有非空的统一且秩七的提升开集。因此对这个固定 $i$，所需性质在原帧空间中给出非空开集。

开性中的“所有三个解”可由完整射影关联检查：在七点横截的开集上，其交为有限 étale 三点族；秩至多六的 $K_U$ 条件是该有限族中的闭条件，向参数的像闭。移走此像，便同时保留全部根的秩七。其余避让也是定理 92.1 中相同的射影闭像论证。这些性质不依赖 $W$ 的帧。原帧空间到 $\operatorname{Gr}(4,D_K)$ 是 $\operatorname{GL}_4$-主丛，其局部平凡性使上述不变开集下降为 Grassmannian 上的非空开集 $\mathscr U_i$。

现在才取八个 $\mathscr U_i$ 的交。原 Grassmannian 几何不可约，每个 $\mathscr U_i$ 非空开，故其有限交非空。Galois 同时置换原嵌入、目标行、评价向量及相应方程，因而置换这些开集；交集在 $F$ 上定义。具体可在一个有限 Galois 分裂域上完成全部构造，然后用不变开子概形的有限忠实平坦下降。这一步没有要求八个各自选出的特殊提升相等；它使用八个已证明非空的开集在同一个不可约原参数空间中相交。

最后去掉 $[P_W]=[P_C]$ 的闭条件。source033 引理 81.5 给 $s_{P_W}=0$ 当且仅当这两条系数线相等。由其 (81.4) 的系数张成性，$P_W$ 的系数线不恒等于一个点，所以该闭集为真闭集；再取交仍非空，得到 (93.8)。等价地，在一个结点候选的秩七核图中，$T_W$ 的非零局部方程也将在下一节直接显现。

任一固定 $F$-Grassmann 大胞腔是 $\mathbb A_F^{16}$，与 $\mathscr B^\circ$ 的交为非空 $F$-开集。无限域上非零多项式不能在所有 $F^{16}$ 上消失：按变量归纳应用一元多项式有限根性质即可。因此这个开集有 $F$-点；对任何更小非空开集应用同一论证，得到几何稠密性。取得的 $F$-点就是同一个 $D$ 内的四维子空间 $W$。$\square$

## 94. 原矩阵余秩一图中的普通二重点

**定理 94.1（原八次除子的局部结点与像分离）。** 对定理 93.2 的每个几何 $W$，每个标记的三个解在 $T_W$ 上给出三个普通二重点；其原 $8\times8$ 矩阵 $K_U$ 余秩恰为一。全部八个标记得到的二十四点彼此不同，且与所有二十八个 $U_{ab}$ 不相交。每个几何结点的完备局部环为

$$
K[[x_1,x_2,z_1,z_2]]/(x_1z_1+x_2z_2).
\tag{94.1}
$$

证明。取标记 $i$ 的一个解，记其对应秩二映射为 $A_0:E\to C_K$，像为 $U_0\subset H_i$，且 $A_0\varepsilon_i=0$。在秩二映射的射影光滑层上，使用“像平面加满秩映射”坐标。这一层是 $\mathbb P\operatorname{Hom}(E,\mathcal S)$ 的满秩开集，维数为 $4+7=11$。

选 $U_0$ 的基 $h_1,h_2$，补为 $H_i$ 的基 $h_1,h_2,h_3$，再选 $h_4$ 使 $c_i(h_4)=1$。在 Grassmann 图中像平面具有规范基

$$
u_1=h_1+y_1h_3+x_1h_4,\qquad
u_2=h_2+y_2h_3+x_2h_4.
\tag{94.2}
$$

于是 $c_i|_U=(x_1,x_2)$，$G_i$ 的局部方程为 $x_1=x_2=0$。固定分裂 $E=K\varepsilon_i\oplus V_i$，写

$$
A\varepsilon_i=z_1u_1+z_2u_2.
\tag{94.3}
$$

在一个 $A_0|_{V_i}$ 的非零矩阵元处作射影归一化。上述十一维光滑层的其余七个坐标记为 $\eta$：两个 $y$ 坐标及归一化后的五个映射坐标。嵌入的 $X_i$ 在此恰由 $x_1=x_2=z_1=z_2=0$ 定义。令 $f_j=c_jA\varepsilon_j$。对 $j\ne i$，七个 $f_j$ 在 $X_i$ 上就是 (91.7)，其交已由定理 92.1 证明横截。因此七阶 Jacobian

$$
\det\left(\frac{\partial(f_j)_{j\ne i}}{\partial\eta}\right)_{A_0}\ne0.
\tag{94.4}
$$

代数隐函数定理给出：先只施加这七个方程所得的局部概形 $M$ 光滑四维，$(x_1,x_2,z_1,z_2)$ 是其 étale 局部坐标；在完备局部环中，其余七坐标唯一成为这四个坐标的形式幂级数。剩下的第 $i$ 个原方程不是近似式，而逐字为

$$
f_i=c_iA\varepsilon_i=x_1z_1+x_2z_2.
\tag{94.5}
$$

所以完整 $Y_W$ 在 $[A_0]$ 的完备局部环就是 (94.1)。这个二次式的 Hessian 非退化，故为三维普通二重点。这里七个未标记的原乘法方程全部参与了 (94.4)；只施加 $c_iA=0$ 与 $A\varepsilon_i=0$ 不会给出这个局部概形。

必须再从关联传回原 $T_W$。定理 93.1 已证明 $K_{U_0}$ 秩七。选一个可逆七阶子块，在 $U_0$ 的邻域写

$$
K_U=\begin{pmatrix}M_7&b\\d&a\end{pmatrix},\qquad
\det K_U=\det M_7\,(a-dM_7^{-1}b).
\tag{94.6}
$$

每个非零核向量的最后坐标必非零：若为零，可逆 $M_7$ 迫使整向量为零。因此射影核唯一归一化为 $(-M_7^{-1}b,1)$，余下方程正是 $a-dM_7^{-1}b=0$。这给出核关联与原行列式除子的概形同构，正是 source033 的 (83.6)，此处用于指定结点而非仅用于泛点。定义 91.2 已排除秩一，因此该核关联确实就是 $Y_W$ 的相应开图。故 (94.1) 是原 $T_W$ 的局部环；这不是另一个行列式族的结点计算。

同一标记内的三个像互异已由定理 92.1 证明。若两个不同标记 $i,j$ 的像相同，它同时包含于 $H_i,H_j$，必为 $U_{ij}$；在 $G_i$ 的对偶坐标中其法向为 $\alpha_j$，属于比例线并已被排除。对任意 $U_{ab}$，若 $i\in\{a,b\}$，同一避让排除它；若 $i\notin\{a,b\}$，则 $H_i\cap H_a\cap H_b$ 仅一维，$U_{ab}$ 不可能属于 $G_i$。因此二十四点全部不同且避开二十八个指定点。$\square$

## 95. 保留原乘法的三重有限 étale 下降与白话定理

**定义 95.1（内在标记与完整下降关联）。** 令 $\Sigma=\operatorname{Spec}D$，其扩底到 $K$ 的八个点才是上述八个原标记。记 $\mathcal W$ 为 $\mathscr B^\circ$ 上的原 tautological 窗口丛。在 $\Sigma\times_F\mathscr B^\circ$ 上，原乘法给出评价

$$
\varepsilon_C:C\otimes_FD\to D,\quad c\otimes d\mapsto cd,
\qquad
\varepsilon_{\mathcal W}:\mathcal W\otimes_FD\to D.
\tag{95.1}
$$

第二个评价是 $\mathcal E=(\mathcal W\otimes_FD)^\vee$ 的一个处处非零截面，绝不是 $\mathcal W\otimes_FD$ 的向量。令

$$
\mathcal H=\ker\varepsilon_C,\qquad
\mathcal V=\mathcal E/D\varepsilon_{\mathcal W},\qquad
\mathcal G=\operatorname{Gr}_{\Sigma\times\mathscr B^\circ}(2,\mathcal H),
\qquad
\mathcal X=\mathbb P_{\mathcal G}\operatorname{Hom}(\mathcal V,\mathcal S).
\tag{95.2}
$$

这里 $\mathcal H,\mathcal V$ 均秩三。将所有丛拉回到 $\mathcal X$，tautological 线给出

$$
\mathcal O_{\mathcal X}(-1)\hookrightarrow\operatorname{Hom}(\mathcal V,\mathcal S),
\qquad
\mathcal A:\mathcal E\longrightarrow
(C\otimes_FD)\otimes\mathcal O_{\mathcal X}(1),
$$

后一个带线丛值的映射由先取商再包含像得到。等价地，它给出张量丛 $(C\otimes_F\mathcal W)\otimes_FD$ 中的 tautological 子线。定义 $\mathcal Z\subset\mathcal X$ 为原乘法映射

$$
\mu_D:(C\otimes_F\mathcal W)\otimes_FD\longrightarrow D\otimes_FD,
\qquad (c\otimes w)\otimes d\longmapsto cw\otimes d
\tag{95.3}
$$

在这条线上为零的闭概形。目标 $D\otimes_FD$ 作为右边 $D$ 上的模秩八，所以这是全部八个原方程的内在写法。

由于 $D/F$ 有限可分，乘法 $m:D\otimes_FD\to D$ 对应有限 étale 对角分量，$\ker m$ 是秩七直和因子。在 $\mathcal X$ 上，$m\mu_D(\mathcal A)=\varepsilon_C\mathcal A\varepsilon_{\mathcal W}=0$ 自动成立，故实际的零截面条件取值于 $\ker m\otimes\mathcal O_{\mathcal X}(1)$。分裂后，基标记为 $i$ 时 (95.2) 正是 $X_i$，(95.3) 正是全部 (91.7)。两项标记限制确定环境 $\mathcal X$；它们自身不定义 $\mathcal Z$。

**定理 95.2（原嵌入概形上的三重覆盖）。** 可取定理 93.2 的同一个非空原域开集 $\mathscr B^\circ$，使

$$
\mathcal Z\longrightarrow\Sigma\times_F\mathscr B^\circ
\tag{95.4}
$$

为有限 étale、局部自由秩三的态射。它对 $\mathscr B^\circ$ 的总次数为二十四，并有原域上的闭浸入

$$
\jmath:\mathcal Z\hookrightarrow\mathcal T\subset G\times_F\mathscr B^\circ,
\qquad (\mathcal T)_W=T_W,
\tag{95.5}
$$

由取像平面定义。对每个 $W\in\mathscr B^\circ(F)$，令 $Z_W=\mathcal Z\times_{\mathscr B^\circ}\operatorname{Spec}F$，则 $Z_W\to\operatorname{Spec}D$ 有限 étale 秩三，$\deg_FZ_W=24$；$\jmath(Z_W)$ 的几何点正好是定理 94.1 的二十四个结点，且

$$
Z_W(F)=\varnothing,\qquad \jmath(Z_W)(F)=\varnothing.
\tag{95.6}
$$

不要求 $Z_W$ 连通，也不要求它的有限 étale 代数为一个域。

证明。构造 (95.1)–(95.3) 完全在原 $F$、原 $D$ 和原乘法上定义，故分裂后所有方程、取像和标记映射都对原 Galois 作用等变。由定理 93.2，每个几何底点 $(i,W)$ 上的完整纤维是三个约化点，且七方程在光滑相对七维 $\mathcal X$ 中横截。局部平凡化秩七的 $\ker m$ 后，七个截面的相对 Jacobian 可逆，故 $\mathcal Z\to\Sigma\times\mathscr B^\circ$ 在每一点 étale。这是相对 Jacobian 判据的直接应用，未以仅有约化纤维代替平坦性。

该态射又是射影且纤维有限，由 Stacks [02LS](https://stacks.math.columbia.edu/tag/02LS) 的“proper 且有限纤维等价于 finite”，它有限。因此是有限 étale；每个几何纤维有三个点，局部自由秩恰为三。与秩八有限 étale 的 $\Sigma\times\mathscr B^\circ\to\mathscr B^\circ$ 复合，得到总秩二十四的有限 étale 态射。

取像平面在 $\mathcal X$ 上已由 tautological $U$ 给出，限制为 $\mathcal Z\to G\times\mathscr B^\circ$。每个纤维上的 $\mathcal A$ 都非零且秩二；乘法方程全部为零，所以由完整核关联落在 $\mathcal T$。概形上的因子化也可直接看出：在局部取 $U$ 的基和 $\mathcal A$ 的射影代表，其两行给 (91.3) 的非零核向量；取一个非零坐标并用伴随矩阵恒等式，便有 $\det K_U=0$，故不是仅在点集上落入 $\mathcal T$。

证明它为闭浸入，须分别检查三个条件。首先 $\mathcal Z$ 对底 $\mathscr B^\circ$ 有限，$\mathcal T$ 对该底分离，因此取像映射 proper：它的图是闭的，图到 $\mathcal T$ 的投影是有限态射的基变换。其次 $\Omega_{\mathcal Z/\mathscr B^\circ}=0$，相对微分正合列使 $\Omega_{\mathcal Z/\mathcal T}=0$；映射有限型，故 unramified。最后定理 94.1 对任意代数闭扩域和任意几何窗口成立，每个几何纤维上二十四个像都不同，所以每个几何纤维至多一点，映射 universally injective。于是 Stacks [04XV](https://stacks.math.columbia.edu/tag/04XV) 的“proper、unramified、universally injective 蕴含 closed immersion”适用，给出 (95.5)。特别地，这不是仅有 Galois 不变的点集，而是原域上定义的闭子概形。

定理 94.1 已证明这些几何像全为所指定的结点，其计数为 $8\cdot3=24$。若 $Z_W$ 有 $F$-点，复合原标记映射 $Z_W\to\operatorname{Spec}D$，便有 $F$-代数同态 $D\to F$。域同态单射，而一个八维 $F$-空间不能线性单射到一维 $F$-空间，矛盾。闭浸入把 $Z_W$ 同构到其像，所以其像同样无 $F$-点。这一论证只使用原标记域的域性，没有使用三重覆盖的连通性或不可约性。$\square$

**定理 95.3（中文白话形式与结论边界）。** 固定同一个特征零原域、其中一个次数为八的实际可分扩张域，以及扩张域内一个任意四个原嵌入评价都独立的实际四维目标窗口。则在实际竞争四维窗口的一个非空原域开集中，每个竞争窗口的原八次测试除子都有二十四个指定的额外普通二重点。每个原嵌入标记贡献三个；这三个来自一个七点三次问题，但它们的有限性、互异性和局部二重点性质是在同一个原结构族中证明的。每个点的原矩阵只有一维核，全部二十四点互不重合，也不等于任何由两个评价核相交得到的二十八个指定点。

这二十四个几何点在原域上合成一个有限 étale 概形，它在原嵌入概形 $\operatorname{Spec}D$ 上的次数为三，在 $F$ 上的总次数为二十四，并闭浸入原测试除子。它没有原域有理点，因为它的每个原域点都必须先给八次扩张域的一个原域点，而后者不存在。三重覆盖可以分裂；这里不把二十四个点宣称为单一 Galois 轨道，也不指定各个闭点的剩余域次数。

证明。固定标记以后，目标的另外七行在三维超平面上仍任意三行独立。定理 92.1 保持这七行不动，通过选取 Cremona 基点使七个线性条件恰留一条行列式铅笔，并使其三次式有三个简单秩二根；同时避开会使后续行条件相关的比例线和强制边界。定理 93.1 证明六列受限矩阵秩五，用匹配的二阶子式写出精确提升条件；其非零性允许在原四维行空间中一次选择统一提升，使三个根全部具有原矩阵秩七。定理 93.2 在同一个不可约窗口空间中取八个好开集的交，保证全部标记的结论同时成立，且确有实际原域窗口。

在每个候选处，另外七个乘法方程先消去七个局部变量，剩下的标记方程精确成为两个双线性项之和；它的非退化二次项就是普通二重点。原矩阵秩七使核图与原除子概形同构，所以这个局部计算确实属于原八次测试除子。像分离及与二十八点不交由定理 94.1 给出。最后定理 95.2 用原乘法写出完整有限关联，保留原标记并下降为三重有限 étale 覆盖；原域点不可能存在的论证随标记映射直接成立。$\square$

本定理只指定这二十四个额外结点及其有限子概形，不分类整个奇异集，不给总节点数、光滑 Calabi–Yau 结论、crepant 解消、物理解释或标签取得预算。关于固定目标系数点的光滑性、平方张满或数域特化，也没有由本定理增加任何蕴含。

上述推导中，七点三次次数、标准 Cremona 变换、射影丛交理论及有限 étale 的下降准则属于明确引用的经典数学；固定左行的同时避让、实际原行提升、原核图中的结点与原标记三重覆盖的组合推导为 `repo-derived`，不作全球原创性声明。source033 的已给定义与核图作为输入复用；这里没有从其他后续理论卷引入新前提。G. Kapustka–M. Kapustka，*A Cascade of Determinantal Calabi–Yau Threefolds*，[arXiv:0802.3669v3](https://arxiv.org/abs/0802.3669v3)，Theorem 3.8 使用一般 $\mathbb P^7$ 线性截面；L. Borisov–H. Nuer，*On (2,4) Complete Intersection Threefolds that Contain an Enriques Surface*，[arXiv:1210.1903v2](https://arxiv.org/abs/1210.1903v2) 使用其 Enriques 曲面关联族。它们具有各自的参数及一般性条件，不提供本卷固定 $c$、原统一 $W$ 的横截性、结点数或算术下降；本卷没有据此转移任何结论。

## 追加锚（本行以下为增补区）

# AURIC Ω：五模式 SO5 路径、十四维恢复与 Hecke 续卷

## 66. 同一固定门菜单中的无限路径族

**定义 86.1（曲线、菜单与三种遗忘数据）。** 固定一条平滑射影连通复曲线 $X$、基点 $x$ 及一个亏格三的拓扑标记

$$
\Pi=\pi_1(X^{\mathrm{an}},x)
=\langle a_1,b_1,a_2,b_2,a_3,b_3\mid
[a_1,b_1][a_2,b_2][a_3,b_3]=1\rangle,
\qquad [a,b]=aba^{-1}b^{-1}.
$$

局部系统的同构均覆盖 $X$ 的恒等，不允许通过曲线自同构或更换标记识别它们。取 [主卷 §21、命题 45](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md) 的同一被动实帧，坐标编号为 $0,1,2,3,4$，并固定

$$
\begin{aligned}
J_{ij}&=E_{ij}-E_{ji},&
A_1&=J_{01}-J_{34},& A_2&=J_{02},& A_3&=J_{03}-J_{14},\\
\theta&=\pi\sqrt2,& U_j&=\exp(\theta A_j),&
\mathscr M&=\{U_1^{\pm1},U_2^{\pm1},U_3^{\pm1}\},&
\Gamma&=\langle U_1,U_2,U_3\rangle.
\end{aligned}
$$

只允许 $\mathscr M$ 的有限字；空字表示恒等。三个独立控制是相对于主卷固定总 Hamiltonian 等待菜单的额外权限；此处不增加第四枚门，也不调用新的连续参数。给定的曲线、标记及下述张量态射也都是模型数据，不从 FIB 计数产生。

置 $G=SO_5(\mathbb C)$、$K=SO(5)$，并令

$$
W=\{S\in M_5(\mathbb C):S^t=S,\ \operatorname{tr}S=0\},
\qquad \dim_{\mathbb C}W=14,\qquad R(g)S=gSg^t.
$$

对表示 $\rho:\Pi\to G$，记主局部系统为 $E_\rho$，伴随向量局部系统为 $L_\rho=E_\rho(W)$。令 $\mathcal C_\rho=\langle L_\rho\rangle_\otimes$ 为 $\operatorname{Loc}_{\mathbb C}(X)$ 中由单位、$L_\rho$、对偶、有限直和、张量积和子商生成的严格满范畴，$\omega_x$ 为基点评价。抽象数据指三元组 $(\mathcal C_\rho,\omega_x,L_\rho)$；路径数据还指定其到 $\operatorname{Loc}_{\mathbb C}(X)$ 的嵌入及全部平行输运。十四维向量局部系统本身属于后一种数据。

**定理 86.2（同群同纤维函子的无限个不同路径实现）。** 对每个 $n\in\mathbb Z_{\geq0}$，规定

$$
\rho_n(a_1)=U_1,\quad \rho_n(a_2)=U_2,\quad \rho_n(a_3)=U_3,
\qquad \rho_n(b_1)=U_1^n,\quad \rho_n(b_2)=\rho_n(b_3)=I.
$$

这些表示在同一个 $\mathscr M$ 内定义，其像全部恰为 $\Gamma$，在 $K$ 中拓扑稠密，在 $G$ 中 Zariski 稠密。主局部系统 $E_n=E_{\rho_n}$ 两两不同构，均无非恒等主局部系统自同构。但全部抽象三元组 $(\mathcal C_{\rho_n},\omega_x,L_{\rho_n})$ 等价于同一个

$$
(\operatorname{Rep}_{\mathbb C}(G),\operatorname{forget},W).
$$

这些等价保留十四维生成对象、纤维函子及全部张量态射，不保留路径嵌入。

**证明。** 本定理以及定理 87.1、88.2、90.2 是针对这些指定门与表示的综合推导（`repo-derived`）；所引 Tannaka、群自同构、Riemann–Hilbert 和 GLC 结果只作有文献依据的中间输入（`literature-attested`）。$U_1$ 与 $U_1^n$ 交换，另两个 $b$ 的像为恒等，故曲面群的唯一关系成立。每个生成元像是允许的有限字，而 $a_1,a_2,a_3$ 的像已经生成 $\Gamma$，所以全部像恰为 $\Gamma$。

主卷命题 45 已给 $\operatorname{Lie}_{\mathbb R}(A_1,A_2,A_3)=\mathfrak{so}(5)$，此处直接复用。每个 $A_j$ 的旋转块角速度为 $\pm1$，其指数周期为 $2\pi$。由于 $\theta/(2\pi)=\sqrt2/2$ 无理，$\{U_j^m:m\in\mathbb Z\}$ 在对应一参数圆群中稠密：圆周上由无理角生成的子群若不稠密，其闭包将是有限圆周子群，从而角度为有理倍 $2\pi$，矛盾。因此 $\overline\Gamma^{\mathrm{top}}$ 包含三个完整圆群；其 Lie 代数为 $\mathfrak{so}(5)$。闭子群定理及 $SO(5)$ 连通性给 $\overline\Gamma^{\mathrm{top}}=K$。复 Zariski 闭包的 Lie 代数包含 $\mathfrak{so}(5)$ 的复张成，又包含于 $\mathfrak{so}_5(\mathbb C)$；由 $G$ 连通，闭包就是 $G$。

$A_1$ 有两个旋转块及一个零方向，故

$$
\operatorname{tr}\rho_n(b_1)=1+4\cos(n\theta).
$$

若 $\cos(n\theta)=\cos(m\theta)$，则 $(n-m)\theta$ 或 $(n+m)\theta$ 属于 $2\pi\mathbb Z$。无理性与 $m,n\geq0$ 迫使 $m=n$。这些迹是主 $G$ 共轭不变量，所以主局部系统两两不同构。主自同构是 $Z_G(\rho_n(\Pi))=Z(G)$。标准五维表示的交换代数为标量，$G$ 中的标量满足 $\lambda^2=\lambda^5=1$，所以 $Z(G)=1$。

为核对张量生成性，若 $R(g)=I$，则 $g$ 固定迹零对称矩阵及 $I$，从而与全部对称矩阵交换。与 $E_{ii}$ 交换使 $g$ 对角，与 $E_{ij}+E_{ji}$ 交换使对角元相同；上面的标量论证给 $g=I$。该论证在任意交换 $\mathbb C$-代数上成立，故表示的群概形核也平凡。特征零代数群的忠实表示给闭浸入 $R:G\hookrightarrow GL(W)$。这一标准输入使用 [Milne, *Algebraic Groups*, §5，同态的核与像](https://jmilne.org/math/Books/iAG2022.pdf)。

对每个 $n$，限制函子 $F_n:\operatorname{Rep}(G)\to\operatorname{Loc}_{\mathbb C}(X)$ 把 $V$ 送到单值 $V\circ\rho_n$。子空间不变性及交织等式都是矩阵系数的代数等式；单值稠密使它们对 $\rho_n(\Pi)$ 成立当且仅当对 $G$ 成立。因此 $F_n$ 充分忠实，且混合张量内的子商没有额外的局部系统子商。忠实有限维表示的混合张量子商生成 $\operatorname{Rep}(G)$；直接应用 [Deligne–Milne, *Tannakian Categories*, 2.20–2.21](https://www.jmilne.org/math/xnotes/tc2022.pdf) 得到 $F_n$ 的像正是 $\mathcal C_{\rho_n}$。基点纤维有来自表示构造的自然识别，故 $\omega_xF_n\simeq\operatorname{forget}$，且 $F_n(W)=L_{\rho_n}$。中性重构 2.11 只作为这里识别同一抽象群的中间输入。

若这些等价还能与 $\operatorname{Loc}(X)$ 中的嵌入相容，就会给 $L_{\rho_n}\simeq L_{\rho_m}$；定理 87.1 将证明这迫使 $E_n\simeq E_m$，与迹区分矛盾。故遗失的正是沿固定曲线的路径实现，而不是抽象张量运算。以上构造的解析局部系统通过射影曲线上的 Riemann–Hilbert 对应与 GAGA 给代数平坦局部系统；平行正交形式和体积形式同时代数化，保留主 $SO_5$ 约化。这一成熟输入采用 Deligne, *Équations différentielles à points singuliers réguliers*, LNM 163，II §5；不从裸统计坐标断言存在连接。$\square$

## 67. 十四维局部系统在稠密域的精确恢复

**定理 87.1（同构类恢复及全部交织映射）。** 设 $\rho,\sigma:\Pi\to G$ 均 Zariski 稠密。定义

$$
\begin{aligned}
\operatorname{Iso}_G(\rho,\sigma)
&=\{h\in G:h\rho(\gamma)h^{-1}=\sigma(\gamma)\quad(\gamma\in\Pi)\},\\
\operatorname{Iso}_W(\rho,\sigma)
&=\{T\in GL(W):TR(\rho(\gamma))=R(\sigma(\gamma))T\quad(\gamma\in\Pi)\}.
\end{aligned}
$$

映射

$$
\mathbb C^\times\times\operatorname{Iso}_G(\rho,\sigma)
\longrightarrow\operatorname{Iso}_W(\rho,\sigma),\qquad (c,h)\longmapsto cR(h)
$$

是双射；非空时 $h$ 唯一。因而 $E_\rho(W)\simeq E_\sigma(W)$ 当且仅当 $E_\rho\simeq E_\sigma$，但

$$
\operatorname{Aut}(E_\rho)=1,\qquad
\operatorname{Aut}_{\operatorname{Loc}}(E_\rho(W))=\mathbb C^\times.
$$

全部线性交织映射也由此确定：不同构时为零空间，同构时为一维空间 $\mathbb C R(h)$。

**证明。** 先在本例内部验证 $W$ 不可约。令 $D\subset SO(5)$ 为行列式一的对角符号矩阵群。$F_{ij}=E_{ij}+E_{ji}$ 上的特征为 $\varepsilon_i\varepsilon_j$；五个坐标的偶符号约束下，十个无序对给彼此不同且非平凡的特征。对 $D$ 的特征投影把任意非零不变子空间中出现的非对角系数隔离成某个 $F_{ij}$。行列式一的带符号置换随即给全部 $F_{kl}$，平面旋转给全部 $E_{kk}-E_{ll}$，于是子空间为 $W$。若一个非零不变子空间只有对角矩阵，取其中非零迹零 $S=\operatorname{diag}(s_i)$，必有 $s_i\ne s_j$；微分作用 $[J_{ij},S]$ 给非零 $F_{ij}$，归入前一种情形。因此 $W$ 不可约，Schur 引理给 $\operatorname{End}_G(W)=\mathbb C I$。稠密性使两种单值的交换代数同样为标量，非零交织映射必为同构。

若 $T\in\operatorname{Iso}_W(\rho,\sigma)$，取 Zariski 闭包得

$$
TR(G)T^{-1}=R(G).
$$

定理 86.2 证明中的闭浸入使 $T$ 在 $G$ 上诱导代数群自同构 $\alpha$。连通伴随半单群的外自同构由带基根数据自同构给出；此处只应用 [Conrad, *Reductive Group Schemes*, §1.5，式 (1.5.2)](https://math.stanford.edu/~conrad/papers/luminysga3.pdf) 与 [Milne, §23.44–23.47](https://jmilne.org/math/Books/iAG2022.pdf)。$G$ 的根数据是伴随型 $B_2$，两顶点根长不同，保持 Cartan 配对的图自同构平凡。因此 $\alpha=\operatorname{Int}(h)$，其中 $h\in G$ 唯一，唯一性使用 $Z(G)=1$。

于是 $R(h)^{-1}T$ 与 $R(G)$ 交换，故为某个 $cI$，$c\ne0$。原交织等式再由 $R$ 忠实性给 $h\rho h^{-1}=\sigma$。反向构造显然成立。若 $cR(h)=c'R(h')$，则 $R(h'^{-1}h)$ 是标量，所以 $h'^{-1}h$ 对 $G$ 的内自同构平凡，由中心平凡得 $h=h'$、$c=c'$。同一个稠密表示的主中心化子仍为中心，得到全部自同构及线性交织结论。

这证明的是具有路径输运的十四维向量局部系统决定主同构类；定理 86.2 的抽象三元组没有给出这样的路径局部系统，两项结论不矛盾。$\square$

## 68. 两个平行张量消除剩余标量

**定义 88.1（固定数值的二次与三次张量）。** 在 $W$ 上指定两个协变张量

$$
b(S,T)=\operatorname{tr}(ST),\qquad
d(S,T,U)=\operatorname{tr}(STU).
$$

它们分别属于 $\operatorname{Sym}^2(W^\vee)$、$\operatorname{Sym}^3(W^\vee)$。对称性由迹的循环性及对称矩阵的转置得到；$b$ 非退化，$d$ 非零，例如

$$
S_0=\operatorname{diag}(1,1,-2,0,0),\qquad
b(S_0,S_0)=6,\qquad d(S_0,S_0,S_0)=-6.
$$

两张量被 $R(G)$ 固定，故在每个 $L_\rho$ 上给出平行张量 $b_\rho,d_\rho$。增强同构必须逐一保持张量的实际数值，不只是保持其张成的直线。

**定理 88.2（稠密域的有限张量恢复及自同构）。** 设 $E,E'$ 为已知由 Zariski 稠密表示 $\rho,\sigma:\Pi\to G$ 定义的主 $G$ 局部系统。映射

$$
\operatorname{Iso}_G(E,E')\longrightarrow
\operatorname{Iso}\big((E(W),b_E,d_E),(E'(W),b_{E'},d_{E'})\big)
$$

是双射，且与复合相容。增强后的自同构群为平凡群，恢复同时保留这些稠密系统的同构类和自同构。所需增强只有定义 88.1 的两个有限次数平行张量。

**证明。** 对稠密的 $E,E'$，定理 87.1 将任意可逆交织映射唯一写为 $cR(h)$。保持 $b$ 等价于 $c^2=1$，保持 $d$ 等价于 $c^3=1$，两式合起来迫使 $c=1$。主同构的像当然保持两张量，已经得到稠密域所需的双射。单独保留 $b$ 留下 $\mu_2$，单独保留 $d$ 留下 $\mu_3$；两者同时保留才消除全部额外标量。

为给出上述稠密域有限增强的一个直接中间见证，在本例中求共同稳定子。定义

$$
S\star T=\frac{ST+TS}{2}-\frac{b(S,T)}5I\in W.
$$

迹配对在全部对称矩阵上非退化，且 $\mathbb C I$ 与 $W$ 正交、$b(I,I)=5\ne0$，所以在 $W$ 上亦非退化。有 $b(S\star T,U)=d(S,T,U)$。所以保持 $b,d$ 的 $T_0\in GL(W)$ 保持 $\star$。将其唯一延拓到 $\mathcal J=\mathbb C I\oplus W=\operatorname{Sym}_5(\mathbb C)$ 并令 $T_0(I)=I$，则它保持 Jordan 乘积

$$
(aI+S)\circ(a'I+T)
=\left(aa'+\frac{b(S,T)}5\right)I+aT+a'S+S\star T.
$$

现直接确定这种 Jordan 自同构。对称幂等矩阵的像与核关于标准对称形式正交且非退化，故可在其像上选正交基；它是若干两两正交秩一对称投影的和。因此 $\mathcal J$ 的本原幂等元恰为秩一对称投影。Jordan 自同构把 $E_{ii}$ 送到五个本原幂等元 $P_i$，满足 $\sum P_i=I$、$P_i\circ P_j=0$。两个幂等元满足 $PQ+QP=0$ 时，以 $P$ 为像核分块，立即得到 $PQ=QP=0$。故可写 $P_i=v_iv_i^t$，其中 $v_i^tv_j=\delta_{ij}$。令 $q$ 以 $v_i$ 为列，则 $q\in O_5(\mathbb C)$。

用 $q^{-1}$ 共轭后，自同构固定所有 $E_{ii}$。同时满足 $E_{ii}\circ S=E_{jj}\circ S=S/2$ 的一维联合 Peirce 空间是 $\mathbb C F_{ij}$，所以 $F_{ij}$ 被送到 $\epsilon_{ij}F_{ij}$。由

$$
F_{ij}\circ F_{ij}=E_{ii}+E_{jj},\qquad
F_{ij}\circ F_{jk}=\frac12F_{ik}\quad(i,j,k\ \text{互异})
$$

得 $\epsilon_{ij}^2=1$、$\epsilon_{ij}\epsilon_{jk}=\epsilon_{ik}$。固定一个坐标 $r$，置 $s_r=1$、$s_i=\epsilon_{ri}$，则 $\epsilon_{ij}=s_is_j$，故此自同构正是 $\operatorname{diag}(s_i)$ 的共轭。恢复 $q$ 后，原自同构是某个 $q'\in O_5$ 的共轭。五维为奇数，$q'$ 与 $-q'$ 共轭作用相同，二者中恰有一个行列式为一。又因 $R$ 忠实，该 $SO_5$ 元素唯一。因此

$$
\operatorname{Stab}_{GL(W)}(b,d)=R(SO_5(\mathbb C)).
$$

回到本定理中已知来自稠密表示的 $E,E'$，其增强平行同构在基点选择两个主纤维的点后，给出上述稳定子中的矩阵，故唯一等于 $R(h)$；平行性交织各闭路单值，由忠实性得 $h\rho h^{-1}=\sigma$，所以唯一回升为主局部系统同构。基点纤维选择的改变只共轭此描述，双射本身与选择无关。复合相容性由 $R(h'h)=R(h')R(h)$ 给出。共同稳定子的计算只是本例恢复证明的中间步骤；Jordan 代数自同构的经典背景不另列为本卷的新一般定理。$\square$

## 69. 稠密性、忠实性与路径数据的边界

**命题 89.1（三个不能省略的区别）。** 下列现象都发生在定义 86.1 的同一曲线上。

第一，遗忘路径嵌入的抽象张量三元组不能确定 $SO_5$ 主局部系统，即使其生成对象为十四维且单值稠密。

第二，定理 87.1 关于全部交织同构及剩余标量的描述不能直接用于非稠密表示；仅给向量局部系统也不保留主自同构。

第三，对一般忠实代数表示，即使两个主单值均 Zariski 稠密，向量局部系统的同构也不必决定主局部系统同构类。

**证明。** 第一项已由定理 86.2 的显式无限族证明，并且定理 87.1 说明这族的十四维路径局部系统也两两不同构；它们的抽象三元组却全部等价。

第二项取平凡 $SO_5$ 局部系统。其主自同构群为 $SO_5$，向量局部系统是平凡十四维系统，自同构群为 $GL_{14}$；后者的维数为 $196$，严格大于 $\mathbb C^\times R(SO_5)$ 的维数 $11$。稠密域的 Schur 与闭包正规化步骤在此不成立。在稠密域仅忘记这些张量也已有额外 $\mathbb C^\times$，故同构类恢复与保留自同构是不同要求。

第三项取 $H=\mathbb G_m$ 及忠实闭浸入

$$
V(t)=\begin{pmatrix}t&0\\0&t^{-1}\end{pmatrix}.
$$

令 $\chi(a_1)=2$、其他标准生成元取一。由于 $H$ 交换，这定义群同态；$\chi(\Pi)=2^{\mathbb Z}$ 为 $\mathbb G_m$ 的 Zariski 稠密子群。$\chi^{-1}$ 同样稠密。两者作为主 $H$ 局部系统不同构，因为 $H$ 的共轭平凡且 $2\ne1/2$；但交换两个坐标的矩阵交织 $V\circ\chi$ 与 $V\circ\chi^{-1}$。失效原因是可被表示正规化子实现的外自同构 $t\mapsto t^{-1}$。定理 87.1 使用的是具体 $SO_5$ 的外自同构平凡及 $W$ 不可约，不能把忠实性单独当作同构类恢复定理。$\square$

## 70. 固定规范下这族谱点的 Sp4 本征对象

**定义 90.1（半扭曲、theta 与本征范畴）。** 继续固定同一个 $X$，并选定 theta characteristic $\eta$ 及同构 $\eta^{\otimes2}\simeq\omega_X$。令自动侧 $G_{\mathrm a}=Sp_4(\mathbb C)$，谱侧为 $\check G_{\mathrm a}=SO_5(\mathbb C)=G$。采用 [Gaitsgory–Raskin, GLC I, arXiv:2405.03599v2](https://arxiv.org/html/2405.03599v2) §1.1.1–1.1.6 的规范：$\operatorname{Dmod}_{1/2}(\operatorname{Bun}_{G_{\mathrm a}})$ 是归一化行列式线丛

$$
\det R\Gamma(X,\mathfrak g_{\mathcal P})\otimes
\det R\Gamma(X,\mathfrak g_{\mathcal P^0})^{-1}
$$

之平方根 $\mu_2$-gerbe 的扭曲 $D$-模范畴。$\eta$ 指定其平方根；Hecke 函子仍按半扭曲范畴解释，不在未经配套修改 Hecke 标签的情形下改用普通 $D$-模。

固定标准 Borel、torus 及 pinning，令 $\varrho$ 为正余根半和，并置 $\mathcal P_T=(2\varrho)(\eta)=\varrho(\omega_X)$。按 I §1.3.2–1.3.8，采用该 $T$-丛上的 Whittaker 规范，指数 $D$-模满足 $\operatorname{add}^*\operatorname{exp}\simeq\operatorname{exp}\boxtimes\operatorname{exp}$。写

$$
\begin{aligned}
\mathcal D&=\operatorname{Dmod}_{1/2}(\operatorname{Bun}_{Sp_4}(X)),&
\mathcal A&=\operatorname{QCoh}(\operatorname{LocSys}_{SO_5}^{\mathrm{dR}}(X)),\\
\mathcal D_{\mathrm{Hecke},E}
&=\mathcal D\underset{\mathcal A}{\otimes}\operatorname{Vect}_{\mathbb C},&
\mathcal A\curvearrowright\operatorname{Vect}_{\mathbb C}&\text{ 由 }E^*\text{ 给出}.
\end{aligned}
$$

本征结构按 I §6.1.1 的这个导出 DG 范畴基变换定义；忘却函子是原文由 $E_*:\operatorname{Vect}\to\mathcal A$ 给出的 $\operatorname{oblv}_{\mathrm{Hecke},E}$。此处的模块范畴、相对张量积及谱作用均保留原文的高阶相容数据，不将其换成三角范畴层面的一组孤立同构。

**定理 90.2（同一门族的实际非零 Sp4 本征对象）。** 对定理 86.2 的每个 $E_n$，定义 90.1 的规范给出本征对象 $\widetilde{\mathcal F}_n$，其实际忘却对象

$$
\mathcal F_n=\operatorname{oblv}_{\mathrm{Hecke},E_n}(\widetilde{\mathcal F}_n)\in\mathcal D
$$

非零，并且是 heart 内的简单、正则 holonomic 对象，奇异支撑包含于全局 nilpotent cone。对所有 $B\in\operatorname{Rep}(SO_5)$，有原文规范化的

$$
\mathsf H_B(\mathcal F_n)\simeq (E_n)_B\boxtimes\mathcal F_n,
$$

连同态射、单位、张量、交换、不同点的外积、对角融合及导出高阶相容性。$\widetilde{\mathcal F}_n$ 精确指定为 I §6.1.1 的等价 $\mathbb L_{Sp_4,E_n}:\mathcal D_{\mathrm{Hecke},E_n}\simeq\operatorname{Vect}$ 下对应

$$
\mathbb C[-\dim\operatorname{Bun}_{Sp_4}
+\dim\operatorname{Bun}_{N,\mathcal P_T}]
=\mathbb C[-40]
$$

的对象。等价下的指定按同构理解，不声称选择空间中的标量自同构消失。

**证明。** $Sp_4$ 的全根数据与伴随型 $SO_5$ 对偶，而不只是 Lie 代数互换。在标准 $Sp_4$ torus 的 $\mathbb Z^2$ 格中，根为 $\pm e_1\pm e_2,\pm2e_i$，余根为 $\pm e_1\pm e_2,\pm e_i$，交换格及根、余根即得 $SO_5$ 的根数据。每个 $E_n$ 的单值 Zariski 稠密，所以若有水平真抛物约化，全部单值将包含于一个共轭的真 Zariski 闭抛物子群，与稠密性矛盾。故 $E_n$ 是 I §6.1.1 所需的不可约谱点；其非导出自同构群 $S_{E_n}$ 由定理 86.2 等于一。

采用 [GLC V, arXiv:2409.09856v3, §5.5](https://arxiv.org/html/2409.09856v3#S5.SS5) 完成证明的几何朗兰兹等价作为外部输入。其 §5.5 通过前文归约处理亏格至少二、almost simple、simply connected 且非 $SL_2$ 的群；本例亏格三与 $Sp_4$ 正在该范围内。因此 I §6.1.1 中以 GLC 成立为条件的等价适用，可按陈述中的移位指定 $\widetilde{\mathcal F}_n$。

移位的数值可直接核对。$\dim Sp_4=10$，所以 $\dim\operatorname{Bun}_{Sp_4}=(3-1)10=20$。相对于选定 Borel，四个正根高度为 $1,1,2,3$，相应的 $\mathfrak n_{\mathcal P_T}$ 分次线丛为 $\omega_X,\omega_X,\omega_X^2,\omega_X^3$。Riemann–Roch 给 $\chi(\omega_X^h)=(2h-1)(3-1)$，故这些 Euler 数之和为 $2+2+6+10=20$。unipotent 丛堆的维数为该 Euler 数的负数，即 $\dim\operatorname{Bun}_{N,\mathcal P_T}=-20$，原文移位恰为 $-40$。

现在必须验证 $\mathcal F_n\ne0$，不能仅从 $\widetilde{\mathcal F}_n\ne0$ 或 $\operatorname{Vect}\ne0$ 推出。直接应用 [I, Theorem 6.1.3(1)–(4)](https://arxiv.org/html/2405.03599v2#S6.SS1.SSS3)：(1) 给实际忘却对象的正则 holonomicity，(2) 给 nilpotent 奇异支撑，(3) 给 heart，(4) 对该实际对象给出

$$
\mathcal F_n\simeq
\bigoplus_{\tau\in\operatorname{Irrep}(S_{E_n})}
\mathcal F_{n,\tau}^{\oplus\dim\tau},
$$

其中每个 $\mathcal F_{n,\tau}$ 是非零简单对象。$S_{E_n}=1$ 只有一个一维不可约表示，故 $\mathcal F_n$ 本身就是非零简单对象。这补足了忘却后非零的独立逻辑环节。

最后，定义 90.1 沿用完整谱作用的 DG 模块基变换，因而 $\widetilde{\mathcal F}_n$ 携带的正是原文的完整 Hecke 本征数据。将其以同一个原文忘却函子送到 $\mathcal D$，得到所列全标签本征同构及其全部相容性；这里不是逐个任取同构后再声称相容。几何 Satake 只作为这一原文 Hecke 作用把 $B\in\operatorname{Rep}(SO_5)$ 变成几何核的中间输入。

$Z(Sp_4)=\mu_2$ 不连通，故 I Theorem 6.1.3(5) 的中心连通前提不满足，本结论不包含其特征循环等式。谱侧 $S_{E_n}=1$ 不能替代自动侧中心连通。该应用给本征对象的精确范畴指定及存在性，不给有限闭式、物理制备或复杂度界，也没有由抽象三元组唯一选择 $E_n$；选择仍依赖定义 86.1 的路径数据。各引述成熟定理仅承担所标注中间输入，本卷的构造与恢复证明不主张文献首创。$\square$

## 追加锚（本行以下为增补区）

## 71. 可取得预测商接入路径输运的条件

**定义 91.1（效果列、观测核与原连接）。** 取[可取得预测丛卷定义 1.1、2.1](AURIC_FIB_OBTAINABLE_PREDICTIVE_BUNDLE_THEORY.md)的固定许可效果与资源合同。在一个常秩参数域 $B$ 上，令 $E=\operatorname{Herm}_0(\mathscr H)$，内积为 $\operatorname{tr}(XY)$，$C_{\mathrm{sup}}:\mathbb R^m\to E$ 的列为中心化效果。此处的观测映射、隐藏核与可见子丛为

$$
C_{\mathrm{VI}}=C_{\mathrm{sup}}^{\mathsf T}:E\longrightarrow B\times\mathbb R^m,
\qquad N=\ker C_{\mathrm{VI}}=\ker C_{\mathrm{sup}}^{\mathsf T},
\qquad W=N^\perp=\operatorname{ran}C_{\mathrm{sup}}.
$$

因此实际概率偏移为 $C_{\mathrm{VI}}(\rho-I/d)$，不是 $C_{\mathrm{sup}}(\rho-I/d)$。固定正定数据权重不改变 $N$。设 $q:E\to Q=E/N$，$P:E\to W$ 为正交投影，另给环境连接 $\nabla^E$，定义下降缺陷

$$
\mathcal B_N(n)=(\operatorname{id}_{T^*B}\otimes q)\nabla^E n,
\qquad n\in\Gamma(N).
$$

Leibniz 法则及 $qn=0$ 使它属于 $\Omega^1(B;\operatorname{Hom}(N,Q))$。若所用效果列张成全部允许未来事件，才把 $Q$ 解释为该合同的全未来商；输出分支的归一化后验仍只在该分支概率严格正时定义。这里消费[关系丛卷定理 8.6](AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md)的常秩像核丛及分支更新，不把参数路径输运加入原许可菜单。

**命题 91.2（指定预测商的连续泄漏与有限拉回障碍）。** 对定义 91.1 的同一观测核，原连接能唯一下降为

$$
\nabla^Q(qs)=(\operatorname{id}\otimes q)\nabla^E s
$$

当且仅当 $\mathcal B_N=0$。在度量相容情形，这等价于 $\nabla^E P=0$；环境连接平坦时，能够下降的商连接也平坦。在同一度量相容条件下，若 $T(t,0)$ 是一条 $C^1$ 参数路径 $\gamma:[0,a]\to B$ 上的环境平行输运，则对每个 $h\in N_{\gamma(0)}$ 及 $0\le t\le a$，

$$
\|P_{\gamma(t)}T(t,0)h\|
\le \|h\|\int_0^t
\|\nabla^E_{\dot\gamma(s)}P\|_{\mathrm{op}}\,ds.
\tag{91.1}
$$

若 $(\nabla^E_{\dot\gamma(0)}P)h\ne0$，在初始纤维的平行识别中，可见分量为
$t(\nabla^E_{\dot\gamma(0)}P)h+o(t)$，因而小正时间已有非零泄漏。

特别地，对[可取得预测丛卷命题 2.13](AURIC_FIB_OBTAINABLE_PREDICTIVE_BUNDLE_THEORY.md#obsq:prop:tangent)的球面菜单，保留向外取向、$W_n=n^\perp$ 及复结构 $J_n v=n\times v$。其两个正观测奇异值均为 $1/\sqrt2$，而作为这个指定的复线丛有

$$
F_{P d}=-i\omega_{S^2},\qquad \deg(W,J)=2.
$$

对任意光滑连通紧复曲线间的非恒定有限映射 $f:Y\to X$、次数 $d\ge1$，任一复可见子丛满足

$$
\deg(f^*W)=d\deg W.
\tag{91.2}
$$

因此上述球面复线及其正次数有限拉回的次数分别为 $2$、$2d$，均不承载平坦复连接。这里排除的是保留该复结构的谱接口；观测谱隙、平坦性和可执行输运是分别需要的条件。

**证明。** [关系丛卷定理 7.3–7.4](AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md#thm-parallel-kernel)已把单路径下降等同于 $T_\gamma N_b\subseteq N_c$，并把全部可逆路径下降等同于核平行。将其中 $L,K,D$ 分别取为 $C_{\mathrm{VI}},N,\nabla^E$。具体到此商，下降公式对 $s$ 与 $s+n$ 的差恰为 $q\nabla^E n$，所以它良定义的充要条件正是显示的缺陷消失；Leibniz 法则给连接，$q$ 满射给唯一性。曲率满足

$$
F_{\nabla^Q}(qs)=q(F_{\nabla^E}s).
$$

度量相容时，$N$ 平行也使 $N^\perp$ 平行，因为对 $w\perp n$ 微分 $\langle w,n\rangle=0$。这等同于 $\nabla^E P=0$。在平凡环境丛 $(B\times E_0,d)$ 中，此条件要求 $P$ 在每个连通分支上为常矩阵；它不能由一个正观测谱隙推出。

为得到本观测商的连续误差量，将所有纤维平行识别回初始纤维，置 $\bar P(t)=T(0,t)P_{\gamma(t)}T(t,0)$。于是

$$
\bar P'(t)=T(0,t)(\nabla^E_{\dot\gamma(t)}P)T(t,0),
\qquad \bar P(0)h=0.
$$

积分并用输运保范数得到 (91.1)；在零点微分得到所述首阶项。这测量的是实际另行允许的路径对隐藏输入的作用；原球面菜单只允许恒等动力学，故数学上的 $T$ 不自动成为其可调用操作。

对曲率和整数障碍，只需在该消费者中使用经典特征类自然性，[Hatcher, *Vector Bundles and K-Theory*, 第 3 章、定理 3.2(a)](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf)。关系丛定理 8.6 给投影连接与

$$
F_{P d}=P(dP\wedge dP)|_W,\qquad
\deg W=\frac{i}{2\pi}\int_X\operatorname{tr}F_{P d}.
$$

该整数与连接无关：两个连接相差全局 $\operatorname{End}(W)$ 值一形式 $A$，曲率迹之差为 $d\operatorname{tr}A$，积分不变。平坦连接的曲率迹为零。拉回连接的曲率是拉回曲率，且 $f_*[Y]=d[X]$，得到 (91.2)，允许有限分歧。球面菜单的曲率、谱隙和次数直接采用上述命题 2.13，不重算其效果菜单。其指定复线可由复线性映射 $v\mapsto v-iJ_nv$ 嵌入平凡 $\mathbb C^3$ 丛；这是 $J_n$ 对应的复线，而不是把实切丛整体复化后所得的秩二复丛。非零次数排除的是这同一对象的平坦化，不影响原固定参数统计任务。$\square$

## 72. 标准型增强十四维路径接口

**定义 92.1（标准型与精确有限路径数据）。** 令 $G=SO_5(\mathbb C)$，沿用定义 86.1、88.1 的

$$
W_{14}=\operatorname{Sym}^2_0(\mathbb C^5),\quad
R(g)S=gSg^{\mathsf T},\quad
b_0(S,T)=\operatorname{tr}(ST),\quad
 d_0(S,T,U)=\operatorname{tr}(STU).
$$

设 $X$ 连通、局部路径连通且半局部单连通。标准型增强局部系统是三元组 $(L,b,d)$：$L$ 为秩十四复局部系统，$b,d$ 是平行的对称二次、三次协变张量，且在一点有

$$
(W_{14},b_0,d_0)\simeq(L_x,b_x,d_x).
$$

平行性与连通性使每点均为该型。态射是保持张量实际数值的平行同构；只保持两条张量直线，或仅给 $b$ 非退化和 $d\ne0$，均非此定义。主局部系统的同构覆盖 $X$ 的恒等。

对标记闭曲面，使用

$$
\pi_1(X,x)=\langle a_1,b_1,\ldots,a_g,b_g\mid
\prod_{i=1}^g[a_i,b_i]=1\rangle.
$$

在一个校准到标准型的纤维内，有限路径输入是 $2g$ 个实际输运矩阵 $T_{a_i},T_{b_i}\in GL(W_{14})$。静态态的十四个坐标不等于这些路径矩阵。

**定理 92.2（标准型接口的对象、态射和自同构下降）。** 关联构造 $E\mapsto(E(W_{14}),b_E,d_E)$ 给主 $G$ 局部系统与定义 92.1 的增强局部系统之间的群胚等价，无单值稠密性要求。有限路径输入定义这样的系统，当且仅当

$$
T_s^*b_0=b_0,\qquad T_s^*d_0=d_0\quad(s=a_i,b_i),
\qquad \prod_i[T_{a_i},T_{b_i}]=I.
\tag{92.1}
$$

这里 $T^*$ 表示协变张量的拉回。此时存在唯一 $A_i,B_i\in G$，满足 $R(A_i)=T_{a_i}$、$R(B_i)=T_{b_i}$，而 $\prod_i[A_i,B_i]=1$。增强同时共轭正好对应主局部系统同构，全部自同构群也由此恢复。

**证明。** 定理 88.2 中已有的共同稳定子计算给

$$
\operatorname{Stab}_{GL(W_{14})}(b_0,d_0)=R(G),
\qquad R:G\hookrightarrow GL(W_{14})\text{ 为忠实闭浸入}.
\tag{92.2}
$$

此处消费该计算。具体标架证明是经典张量稳定子重构在此标准型的应用；背景见 [Deligne–Milne, *Tannakian Categories*, §2，定理 2.11、命题 2.20–2.21](https://www.jmilne.org/math/xnotes/tc2022.pdf)。对每点取

$$
\mathscr P_x=\operatorname{Isom}((W_{14},b_0,d_0),(L_x,b_x,d_x)),
\qquad \phi\cdot g=\phi\circ R(g).
$$

标准型保证非空，(92.2) 保证右作用自由且传递。$L$ 的平行输运保持张量，将 $\mathscr P_x$ 等变地送到 $\mathscr P_y$，且保持路径合成、恒等和同伦。因此 $\mathscr P$ 是主 $G$ 局部系统，评价给自然同构

$$
\mathscr P\times^G W_{14}\longrightarrow L,\qquad [\phi,v]\longmapsto\phi(v).
$$

反向从 $E$ 的主标架得到 $E(W_{14})$ 的增强标架；(92.2) 和忠实性说明得到全部标架并唯一还原 $E$。一个增强平行同构 $T:L\to L'$ 在标架上作用为 $\phi\mapsto T\phi$，给唯一的主同构；关联构造给反向，二者互逆且保持复合。这同时证明对象、全部同构及自同构的对应；例如平凡系统的增强自同构是 $G$，无需使用稠密域的 Schur 论证。

在标记曲面上，(92.2) 给每个 $T_s$ 的唯一原像。关系式经 $R$ 等于恒等，由忠实性原群中的关系也等于恒等，因此自由群赋值下降为曲面群表示。反向由局部系统输运的同伦相容性给出。群胚中的同构在校准纤维内正是 (92.2) 内的同时共轭，得到 (92.1) 的全部断言。

同一构造还给该接口所需的连接计算。若光滑丛上的 $b,d$ 处处标准型，则增强标架是光滑主 $G$ 丛：把普通标架下的张量对视为 $GL(W_{14})/R(G)$ 中的光滑截面，局部提升即给增强标架。若 $\nabla b=\nabla d=0$，在这些标架内连接形式取值于共同无穷小稳定子，所以唯一写成

$$
A=R_*(a),\qquad a\in\Omega^1(X;\mathfrak{so}_5(\mathbb C)).
$$

微分表示保持 Lie 括号，故

$$
F_\nabla=dA+A\wedge A
=R_*(da+a\wedge a)=R_*(F_a).
\tag{92.3}
$$

标架变换律由 $R$ 传回主连接变换律；$R_*$ 单射给唯一性和两侧平坦性等价。这是该标准型消费者的支持计算，并未从静态读数产生一个连接或输运服务。射影复曲线上的路径系统可再按定理 86.2 所用的 Riemann–Hilbert 与 GAGA 供应解释为代数平坦系统；不在此改变其来源和适用范围。$\square$

## 73. 两参考来源的输运取得

**定义 93.1（附加参考制备合同）。** 令 $K=SO(5,\mathbb R)$。另行供应两个已知实密度矩阵的独立制备及同一个确定性未知 $U\in K$ 的输运服务：

$$
S_0=\frac15I+\frac1{50}\operatorname{diag}(-2,-1,0,1,2),\qquad
T_0=\frac15I+\frac1{50}(\mathbf1\mathbf1^{\mathsf T}-I),\qquad
\mathbf1=(1,1,1,1,1)^{\mathsf T}.
$$

允许对两个输出取得完整实对称矩阵。记

$$
\Phi(U)=(US_0U^{\mathsf T},UT_0U^{\mathsf T}),\qquad
\varepsilon(U,V)=\max_{H\in\{S_0,T_0\}}
\|UHU^{\mathsf T}-VHV^{\mathsf T}\|_F.
$$

原固定未知来源接口不供应这两个已知参考态。若输运由指定原始门词实现，其内部执行另按该词计费。

**定理 93.2（该参考合同的最小数量与全局逆常数）。** $S_0,T_0$ 严格正定且迹为一，$\Phi$ 在 $K$ 上单射，并且对所有 $U,V\in K$，

$$
\|U-V\|_F\le1600\,\varepsilon(U,V).
\tag{93.1}
$$

在只读固定实密度参考态的完整共轭输出这一合同内，单个参考不能辨认全部 $U\in K$，因此两个是最少数量。常数为一个全局上界，不要求最优。

**证明。** 两参考的谱分别为 $(.16,.18,.20,.22,.24)$ 和 $(.28,.18,.18,.18,.18)$。若 $C=V^{\mathsf T}U$ 同时固定它们，$S_0$ 的简单谱使 $C$ 为对角符号矩阵，$T_0$ 的非零非对角项使全部符号相同；五维行列式一排除 $-I$，故 $C=I$。

令 $\varepsilon=\varepsilon(U,V)$。第一输出差的 Frobenius 范数等于 $CS_0-S_0C$ 的范数，谱间距至少 $1/50$，所以

$$
a=\|\operatorname{offdiag}C\|_F\le50\varepsilon.
$$

当 $\varepsilon\le1/400$ 时 $a\le1/8$。正交性给 $|c_{ii}|=\sqrt{1-\sum_{j\ne i}c_{ij}^2}>0$。取 $D=\operatorname{diag}(\operatorname{sgn}c_{ii})$，由 $1-\sqrt{1-t}\le t$ 得

$$
\|C-D\|_F^2\le a^2+a^4,\qquad
\|C-D\|_F\le\frac98a\le\frac9{64}.
$$

不同行列式分支的实正交矩阵间距离至少为二：其比有特征值 $-1$。因此 $D\in K$。若 $D\ne I$，负号数为二或四；跨符号的有序非对角项至少八个，每项在 $DT_0D-T_0$ 内绝对值为 $1/25$，故

$$
\|DT_0D-T_0\|_F\ge\frac{2\sqrt2}{25}.
$$

但 $\|T_0\|_{\mathrm{op}}=7/25$，三角不等式给

$$
\|DT_0D-T_0\|_F
\le\varepsilon+\frac{14}{25}\|C-D\|_F
\le\frac1{400}+\frac{14}{25}\frac9{64}
=\frac{13}{160}<\frac{2\sqrt2}{25},
$$

矛盾。所以 $D=I$，$\|C-I\|_F\le(225/4)\varepsilon$。当 $\varepsilon\ge1/400$ 时，奇数维 $C\in SO(5)$ 至少有一个特征值一，其余四个特征值到一的平方距离总和至多十六，故
$\|C-I\|_F\le4\le1600\varepsilon$，得到 (93.1)。

任一单独实对称参考可在正交本征基内同时翻转两个坐标，产生非恒等的 $K$ 稳定子元素。因而它的全部共轭输出也不能确定 $U$。这个数量下界只针对定义 93.1 的合同。$\square$

**推论 93.3（有限参考记录的置信界与资源）。** 对每个输出使用五个效果 $e_ie_i^{\mathsf T}$ 及十个效果 $(e_i+e_j)(e_i+e_j)^{\mathsf T}/2$，每设置独立制备并输运 $N\ge1$ 次。设 $0<\delta<1$、$\tau\ge0$。以至少 $1-\delta$ 的概率，两个矩阵估计 $\widehat H_S,\widehat H_T$ 各有 Frobenius 误差至多

$$
\zeta=\sqrt{\frac{85\log(60/\delta)}{2N}}.
$$

任一 $\widehat U\in K$ 若其最大两输出拟合残差不超过最小残差加 $\tau$，则同一事件上

$$
\|\widehat U-U\|_F\le1600(2\zeta+\tau).
\tag{93.2}
$$

费用为 $30N$ 次参考制备和输运；若每次输运词长为 $\ell$，另有 $30N\ell$ 次原始门执行。$\tau$ 是优化容差；此处没有最优位复杂度或精确有限数字优化器的断言。

**证明。** 三十个 Bernoulli 设置的 Hoeffding 不等式及并合界给每个概率同时误差至多
$t=\sqrt{\log(60/\delta)/(2N)}$。这里使用 [Hoeffding, *Probability inequalities for sums of bounded random variables*, 定理 2](https://doi.org/10.1080/01621459.1963.10500830) 的经典浓缩界。对角元误差至多 $t$；非对角元由加号效果概率减去两对角元之半得到，误差至多 $2t$。因此每个输出的平方 Frobenius 误差至多

$$
5t^2+2\binom52(2t)^2=85t^2.
$$

真实 $U$ 的最大残差不超过 $\zeta$；紧群上连续残差达到最小值，故任意所述拟合的残差不超过 $\zeta+\tau$。将拟合输出和真实输出经同一估计矩阵比较，差至多 $2\zeta+\tau$，代入 (93.1)。该单副本已知参考合同的 $N^{-1/2}$ 输出误差与[量子边界卷](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md)未知反对称态的实两副本合同不同，不能互换来源与资源。$\square$

## 74. 十四维近似路径的正则修正

**定义 94.1（实张量缺陷与曲面关系）。** 在 $W_{14,\mathbb R}=\operatorname{Sym}^2_0(\mathbb R^5)$ 的迹内积中固定正交基，张量范数为该基诱导的欧氏范数，记 $\mathcal K=R(K)\subset O(14)$。对实可逆矩阵 $M$ 及 $z=(A_1,B_1,\ldots,A_g,B_g)\in K^{2g}$，置

$$
\mathcal D(M)=(M^*b_0-b_0,M^*d_0-d_0),\qquad
\mathcal R(z)=\prod_i[A_i,B_i],
$$

$$
\mathfrak z_z=\{Z\in\mathfrak{so}(5):[Z,A_i]=[Z,B_i]=0\ (1\le i\le g)\}.
$$

对 $2g$ 个实可逆十四维矩阵，定义

$$
\operatorname{Def}(M)=\max_s\|\mathcal D(M_s)\|
+\left\|\prod_i[M_{a_i},M_{b_i}]-I\right\|_F.
\tag{94.1}
$$

**定理 94.2（该有限路径接口的局部线性修正）。** 设 $g\ge1$，固定 $z_0\in K^{2g}$，$\mathcal R(z_0)=I$ 且 $\mathfrak z_{z_0}=0$。在 $R(z_0)$ 的一个邻域上存在光滑修正选择 $M\mapsto\widehat z\in\mathcal R^{-1}(I)$，以及有限常数 $C_{z_0}$，使

$$
\max_s\|M_s-R(\widehat z_s)\|_F
\le C_{z_0}\operatorname{Def}(M).
\tag{94.2}
$$

这些常数和邻域是局部的。修正给一个真正 $K$ 曲面表示，不要求该表示唯一，也不辨认未知来源的精确表示。

**证明。** 先在本消费者内建立紧实张量投影估计。由 (92.2)，若一个实矩阵固定两个张量，其唯一复原像 $g\in G$ 满足 $R(\bar g)=R(g)$，故 $g=\bar g\in K$。于是
$\mathcal D^{-1}(0)=\mathcal K$。在 $p\in\mathcal K$，$D\mathcal D_p$ 的核恰为 $T_p\mathcal K$：平移到单位元后，无穷小张量稳定子的元素经指数形成固定张量的一参数群，反向由微分成立。因此导数在法空间单射。紧致的法单位球丛给统一正下界 $c_0$。取紧子流形的管状邻域与光滑最近点投影 $\Pi$，写 $M=p+n$、$n\perp T_p\mathcal K$，统一 Taylor 估计为

$$
\|\mathcal D(M)\|\ge c_0\|n\|_F-C\|n\|_F^2.
$$

缩小管状邻域后，得到

$$
\|M-\Pi(M)\|_F\le c\|\mathcal D(M)\|.
\tag{94.3}
$$

而张量缺陷充分小的全部实矩阵都在这个邻域：否则取缺陷趋零但远离邻域的序列，二次缺陷就是 $M^{\mathsf T}M-I\to0$，使矩阵及其逆有统一界；收敛子列的极限固定两个张量，属于 $\mathcal K$，矛盾。这里实数和紧致性不可用一般复矩阵替代。

再计算曲面关系的精确导数。取 $\mathfrak{so}(5)$ 的 Ad 不变内积，用 $\delta A_i=X_iA_i$、$\delta B_i=Y_iB_i$ 平凡化切向量，置 $C_i=[A_i,B_i]$、$P_i=C_1\cdots C_{i-1}$。在 $\mathcal R(z)=I$ 处，逐项乘法微分给

$$
D\mathcal R_z(X,Y)=\sum_i\operatorname{Ad}_{P_i}
\left[(I-\operatorname{Ad}_{A_iB_iA_i^{-1}})X_i
+(\operatorname{Ad}_{A_i}-\operatorname{Ad}_{C_i})Y_i\right].
\tag{94.4}
$$

其像的正交补恰为 $\mathfrak z_z$，从而给余核的自然识别。为直接验证，若 $Z$ 与像正交，写 $Z_i=\operatorname{Ad}_{P_i^{-1}}Z$，则

$$
\operatorname{Ad}_{A_iB_iA_i^{-1}}Z_i=Z_i,
\qquad \operatorname{Ad}_{A_i^{-1}}Z_i
=\operatorname{Ad}_{C_i^{-1}}Z_i.
$$

第一式及 $A_iB_iA_i^{-1}=C_iB_i$ 又给右侧等于 $\operatorname{Ad}_{B_i}Z_i$。令 $V_i=\operatorname{Ad}_{A_i^{-1}}Z_i$，第一式还说明 $\operatorname{Ad}_{B_i}V_i=V_i$；连同 $V_i=\operatorname{Ad}_{B_i}Z_i$ 得 $V_i=Z_i$。因此 $Z_i$ 被 $A_i,B_i,C_i$ 固定，$Z_{i+1}=Z_i$，归纳得到 $Z$ 同时中心化全部生成元。反向把共同固定的 $Z$ 代入 (94.4) 即得正交性。故零共同 Lie 中心化子恰使导数满射；这是曲面表示经典形变计算在此门群的具体形式。

对每个 $M_s$ 用 (94.3)，得 $\Pi(M_s)=R(\widetilde U_s)$。闭嵌入 $R:K\to\mathcal K$ 的逆光滑。在固定小邻域内，乘法、求逆及有限关系词的导数有统一界，故

$$
\|R(\mathcal R(\widetilde U))-I\|_F\le C_1\operatorname{Def}(M),
\qquad
\|\log\mathcal R(\widetilde U)\|\le C_2\operatorname{Def}(M).
$$

第二式用 $R_*$ 在恒等处单射及局部矩阵对数。$\log\circ\mathcal R$ 在 $z_0$ 的导数满射，取其核的补空间，经典隐函数定理给局部坐标 $(v,w)$，其中 $w=\log\mathcal R$；将 $(v,w)$ 送到 $(v,0)$ 得光滑局部回缩，改变量至多 $C_3\|w\|$。这给精确元组 $\widehat z$，合并两次修正得到 (94.2)。隐函数与管状邻域只承担上述支持步骤，没有提供全局修正模。$\square$

**命题 94.3（该修正的奇异边界与不可约开条件）。** 在平凡表示附近，存在精确固定 $b_0,d_0$ 的十四维元组，关系缺陷为 $\Theta(t^2)$，而到精确关系集的距离为 $\Theta(t)$。另方面，五维复表示不可约是有限生成元元组的开条件；从这样的正则基点出发，充分小的定理 94.2 修正保留它。共同 Lie 中心化子为零本身不等同于五维复不可约。

**证明。** 取 $X=J_{12}$、$Y=J_{23}$，则 $[X,Y]=J_{13}\ne0$。令

$$
A_1(t)=e^{tX},\quad B_1(t)=e^{tY},\qquad
A_i(t)=B_i(t)=I\quad(i>1).
$$

其十四维像都在 $\mathcal K$，张量缺陷为零，而乘法的二阶展开为

$$
\mathcal R(z(t))=I+t^2[X,Y]+O(t^3).
$$

$R_*$ 单射使十四维关系缺陷也为 $\Theta(t^2)$。到平凡元组距离 $O(t)$ 给上界。若无 $\Omega(t)$ 下界，可取 $t_j\downarrow0$ 与精确表示元组 $\widehat z_j$，距离为 $o(t_j)$。在恒等附近取矩阵对数并除以 $t_j$；第一对趋于 $X,Y$，其余对趋零。精确关系的二阶展开迫使 $[X,Y]=0$，矛盾。$R$ 的光滑局部逆将两种矩阵距离互相控制，得所述十四维反例。

对于每个 $1\le k\le4$，共同不变 $k$ 维子空间与元组构成闭关联集；复 Grassmann 流形紧致，使其到有限元组空间的投影闭。取这四个闭集的并，便得可约元组闭，故不可约开。五维复不可约由 Schur 引理排除非零共同 Lie 中心化子；逆向不成立，见命题 97.3 的具体元组。这里不在自守 $D$-模上定义数值误差范数，也不从 (94.2) 推出 Hecke 对象的数值 Lipschitz 界。$\square$

## 75. 选层、全局取向和 Spin 存在性的共同覆盖

**定义 95.1（固定投影、中心缺陷与来源选择）。** 令 $X$ 为亏格 $g\ge1$ 的光滑连通射影复曲线，给定定义 92.1 的标记及

$$
\rho:\pi_1(X)\to SO_5(\mathbb C),\qquad
p:\operatorname{Spin}_5(\mathbb C)\simeq Sp_4(\mathbb C)\to SO_5(\mathbb C).
$$

对各生成元像 $A_i,B_i$ 任取提升 $\widetilde A_i,\widetilde B_i$，记

$$
\kappa(\rho)=\prod_i[\widetilde A_i,\widetilde B_i]\in\ker p=\mu_2=\{\pm1\}.
\tag{95.1}
$$

另按[退化与分歧卷定义 5.1](AURIC_LANGLANDS_DEGENERATION_RAMIFICATION_AND_STABLE_RECOVERY_THEORY.md)给定完整来源的有限 étale 覆盖 $C\to U=X\setminus D$，$D$ 有限，及基点处合法取得的指定来源 $\omega$。其整个纤维的置换单值为 $\nu:\pi_1(U)\to F\le S_n$，置

$$
H=F_\omega,\qquad m=[F:H],\qquad
\varepsilon=\operatorname{sgn}\circ\nu.
$$

选择 $\omega$ 的最小带锚连通覆盖 $U_0\to U$ 对应 $\nu^{-1}(H)$；令 $Y_0$ 为光滑射影紧化，$\varepsilon_0$ 为 $\varepsilon$ 在 $\pi_1(U_0)$ 上的限制。共同任务要求指定来源有水平选择、整个取向字符平凡，且拉回的给定 $\rho$ 在覆盖紧化上存在某个 Spin 提升。没有预先规定穿孔曲线上的提升。

**定理 95.2（该来源与谱系统共同任务的精确次数）。** 在定义 95.1 下，共同任务在连通有限 étale 覆盖 $U'\to U$ 中的最小次数为

$$
D_{\min}=\begin{cases}
m,&\varepsilon_0=1\text{ 且 }(\kappa(\rho)=1\text{ 或 }m\text{ 为偶数}),\\
2m,&\text{其余情形}.
\end{cases}
\tag{95.2}
$$

紧化映射允许在删点上方分歧。所用中心数据满足：$\kappa$ 与生成元提升选择无关且共轭不变；给定 $\rho$ 的 Spin 提升存在当且仅当 $\kappa=1$。存在时，保留到该五维系统的投影识别的提升同构类构成 $H^1(X;\mu_2)$ 挠集，恰有 $2^{2g}$ 类。任意次数 $d$ 的非恒定有限映射 $f:Y\to X$ 满足

$$
\kappa(f^*\rho)=\kappa(\rho)^d.
\tag{95.3}
$$

**证明。** 先在这个共同覆盖消费者内给出经典中心提升的具体矩阵计算；一般 Spin 障碍与选择的归属为 [Perutz, *Smooth 4-manifolds and the Seiberg–Witten equations*, 定理 17.3](https://web.ma.utexas.edu/users/perutz/GaugeTheory/FullCourse.pdf)。曲面关系使 (95.1) 落在中心核，乘任一提升以 $-1$ 不改变其交换子，同时共轭也不改变中心乘积。若表示已有提升，其生成元满足关系，故 $\kappa=1$；反之 $\kappa=1$ 使任取的生成元提升满足唯一关系，因而从自由群下降为曲面群表示。

固定一个提升 $\widetilde\rho_0$，其他同一投影的提升唯一形如 $\chi\widetilde\rho_0$。中心性使同态条件等价于 $\chi:\pi_1(X)\to\mu_2$ 为字符，作用自由传递。曲面群的 $2g$ 个生成元符号任意，故数目为 $2^{2g}$。相对同构投影为恒等，只能取中心核的平行规范变换，不能把不同字符合并；若忘记到给定 $\rho$ 的投影识别，则不能无条件保留这个计数。

用好覆盖上的转移函数提升，三重交集的中心差给 $o(\rho)\in H^2(X;\mu_2)$；改变提升只改变余边界，拉回保持其余循环。曲面唯一二维胞腔沿交换子乘积粘贴，所以基本类评价是 (95.1) 的符号。紧实约化时它是正交五维丛的 $w_2$，不是底层实十维丛的 $w_2$。自然性与 $f_*[Y]=d[X]$ 给

$$
\langle o(f^*\rho),[Y]\rangle
=\langle o(\rho),d[X]\rangle\quad\text{于 }\mathbb Z/2,
$$

即 (95.3)；分歧点不改变拓扑次数。正亏格曲线有非平凡 $\mu_2$ 字符，因此有连通无分歧二重覆盖。于是单独消去提升存在性障碍的最小次数在 $\kappa=1$ 时为一，在 $\kappa=-1$ 时为二。

现在用退化与分歧卷定理 5.2 的选层/全取向供应。任何带同一锚点来源选择的覆盖因子化经过 $U_0$，故次数是 $m$ 的正整数倍。如果 $\varepsilon_0\ne1$，它在 $U_0$ 上的核给最小二重进一步覆盖，总次数为 $2m$。此总次数为偶，由 (95.3)，紧化上的 $\rho$ 也有提升，因而达到共同任务的下界。

若 $\varepsilon_0=1$，在 $Y_0$ 上的障碍为 $\kappa^m$。它为一时 $m$ 已足够；它为负一时 $m$ 奇且 $\kappa=-1$，任何成功总次数都须为偶，因而至少 $2m$。Riemann–Hurwitz 给 $g(Y_0)\ge1$，可取 $Y_0$ 的连通无分歧二重覆盖，限制到 $U_0$ 仍连通，既消去障碍又保留已平凡的取向，达到 $2m$。这也说明取向所需的那个因子二可以同时消去 Spin 存在性障碍，无须把次数再乘成 $4m$。

若任务改成延拓事先指定的穿孔曲线提升 $\widetilde\rho_U$，还须逐个满足

$$
\widetilde\rho_U(\delta_x)^{e_y}=1\qquad(y\mid x\in D),
\tag{95.4}
$$

因为紧化基本群的核由外围圈正规生成。在退化与分歧卷定理 5.3 的原提升及取向扭曲情形，(95.4) 正是其 $\varepsilon(\delta_x)^{e_y}=1$ 条件。外围值全平凡后仍可能有该卷 (5.6) 的剩余 Picard 二阶类；它也平凡才使整个取向字符平凡。这些判据仍归该供应负责。存在某个紧化提升不等于延拓给定穿孔提升。$\square$

**命题 95.3（稠密无提升的门扩充例与既有族的六十四提升）。** 允许在定义 86.1 的三个门之外另加下述两个确定半周门时，存在稠密 $SO(5)$ 曲面表示而没有 Spin 提升。相反，定理 86.2 的每个亏格三 $\rho_n$ 有 $\kappa=1$，在给定投影识别下恰有 $64$ 个提升类。

**证明。** 将既有三个稠密门重标号到坐标 $1,\ldots,5$，仍记为 $U_1,U_2,U_3$。新增门为

$$
P_0=\operatorname{diag}(-1,-1,1,1,1),\qquad
Q_0=\operatorname{diag}(1,-1,-1,1,1).
$$

在紧实 Clifford 约定 $e_i^2=-1$ 下，$e_1e_2$ 与 $e_2e_3$ 分别提升它们且反对易，交换子为 $-1$。在亏格四曲面令

$$
\rho(a_1)=P_0,\quad\rho(b_1)=Q_0,\qquad
\rho(a_{j+1})=U_j,\quad\rho(b_{j+1})=I\quad(1\le j\le3).
$$

所有正交交换子为恒等，故关系成立；像包含定理 86.2 的稠密门群，而提升交换子乘积为 $-1$，所以没有提升。此例的新增两个门是明确的额外权限，没有证明它们是原三门菜单的精确有限字。

对既有 $\rho_n$，任选 $\widetilde U_j$，令 $\widetilde\rho_n(a_j)=\widetilde U_j$、$\widetilde\rho_n(b_1)=\widetilde U_1^n$、另两个 $b$ 像为一。每个交换子为一，得一个提升。定理 95.2 给 $2^{2\cdot3}=64$ 个相对类。稠密正交像的中心化子为一，所以即使允许普通 Spin 主共轭，不同字符也不合并；不同 $n$ 的投影已不同构，故其提升也不合并。提升像的 Zariski 闭包映满 $SO_5$，有限核给相同维数，故它是连通的 $\operatorname{Spin}_5$，中心化子为 $\mu_2$，每个提升有这个中心自同构群。这里的 $64$ 是原亏格三族的数目。

谱侧 $SO_5$ 对应自守侧 $Sp_4$，无需先选 Spin 提升；另行细化为 $\operatorname{Spin}_5\simeq Sp_4$ 谱系统时，自守对偶改为 $SO_5$。这两种消费不构成自守侧基变换函子。[实际全局端口取向卷定义 1.1–1.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md)中的付费持久双射 $\{a,b\}\to\{L,R\}$ 是绑定实际来源的端口数据，来源取向是 $H^1(U;\mu_2)$ 字符，提升障碍是 $H^2(X;\mu_2)$ 类，障碍消失后的提升标签又是一个 $H^1(X;\mu_2)$ 挠集；没有额外映射时，二值性不识别这些对象。$\square$

## 76. 全生成元参考记录、修正与局部 Spin 数据

**推论 96.1（同一置信事件上的精确拟合谱接口）。** 固定定理 94.2 的正则元组 $z_0$ 和一个充分小的修正图，设真正未知的 $K$ 曲面元组 $z$ 位于一个较小图内。对每个 $2g$ 生成元输运，按定义 93.1、推论 93.3 使用每设置 $N$ 次参考制备，且拟合优化容差至多 $\tau$。定义

$$
\zeta_g=\sqrt{\frac{85\log(120g/\delta)}{2N}},\qquad
 a_N=1600(2\zeta_g+\tau).
$$

若 $a_N$ 小于图的固定余量，则以至少 $1-\delta$ 的概率，全部拟合 $\widehat U_s\in K$ 同时满足 $\|\widehat U_s-z_s\|_F\le a_N$，并可修正为精确表示 $\rho^\sharp:\pi_1(X)\to K$，使

$$
\max_s\|R(\rho^\sharp(s))-R(z_s)\|_F\le C_{\mathrm{chart}}a_N.
\tag{96.1}
$$

费用为 $60gN$ 次参考制备与输运。若给定生成元词长为 $\ell_s$，内部原始门调用总数为 $30N\sum_s\ell_s$。修正后的共同 Lie 中心化子仍为零，且

$$
\kappa(\rho^\sharp)=\kappa(z)=\kappa(z_0).
\tag{96.2}
$$

固定定义 95.1 的来源覆盖、候选与取向时，修正前后的共同最小覆盖次数 (95.2) 不变。若 $z_0$ 的五维复表示不可约，还可缩图使拟合精确表示保留它。

**证明。** 对每个生成元在推论 93.3 取失败概率 $\delta/(2g)$，并合界给所有误差同时至多 $a_N$；不需要不同生成元的失败事件独立。对 $U,V\in K$，任一单位 Frobenius 范数的 $S\in W_{14,\mathbb R}$ 满足

$$
\|USU^{\mathsf T}-VSV^{\mathsf T}\|_F
\le2\|U-V\|_{\mathrm{op}}\le2\|U-V\|_F,
$$

所以在十四维正交基上

$$
\|R(U)-R(V)\|_F\le2\sqrt{14}\|U-V\|_F.
$$

取 $M_s=R(\widehat U_s)$，其张量缺陷为零，有限关系词在固定图内 Lipschitz，真实关系为一，故 $\operatorname{Def}(M)\le C a_N$。用定理 94.2 并合并到真实矩阵的距离，得 (96.1)。共同 Lie 中心化子是一个连续系数线性映射的核；在 $z_0$ 处核为零，某个最大阶子式非零，缩图后仍非零。不可约性的保持则用命题 94.3。

最后，Spin 双覆盖在每个 $z_{0,s}$ 周围有连续局部分支。选择各生成元的局部提升，在全部附近元组上形成连续乘积
$\prod_i[\widetilde A_i,\widetilde B_i]$，其在 $z_0$ 的值为 $\kappa(z_0)$。先将整个图缩小，使此乘积的像位于不含另一个中心符号的邻域；对其中每个精确关系元组，乘积属于 $\mu_2$，故只能取原符号。真实 $z$ 和修正元组都在这个图中，得到 (96.2)，无需假设精确关系集连通。来源、候选、取向固定后 $m,\varepsilon_0$ 固定，(95.2) 随之不变。

此推论产生附近的精确拟合对象及矩阵误差，既不从有限噪声记录取得未知来源的精确同构类，也不选出 $H^1$ 挠集的某个标签，更不识别拟合对象与原对象的实际 Hecke 层。对既有 $\rho_n$ 的充分小图，(96.2) 保持 $\kappa=1$ 和每个拟合对象的 $64$ 个相对提升类；其简单 Hecke 消费条件由下一节给出。$\square$

## 77. 精确接口的半扭 Sp4 Hecke 消费

**定义 97.1（一般亏格的固定规范及对象边界）。** 取亏格 $g\ge2$ 的光滑连通射影复曲线，沿用定义 90.1 的 theta characteristic、半扭行列式 gerbe、Borel、torus、pinning 与 Whittaker 规范，不将其换为普通 $D$-模。记

$$
\mathcal D=\operatorname{Dmod}_{1/2}(\operatorname{Bun}_{Sp_4}(X)),\qquad
\mathcal A=\operatorname{QCoh}(\operatorname{LocSys}^{\mathrm{dR}}_{SO_5}(X)),
\qquad
\mathcal D_{\mathrm{Hecke},E}=\mathcal D\underset{\mathcal A}{\otimes}\operatorname{Vect}_{\mathbb C}.
$$

这里 $E^*$ 给 $\mathcal A$ 对 $\operatorname{Vect}$ 的作用，$E_*$ 给原文的忘却函子；相对张量积与谱作用均按完整导出 DG 模块范畴解释。称 $E$ 无真抛物约化，当且仅当其单值不包含于 $SO_5$ 的任一共轭真抛物子群。$S_E$ 是非导出的谱自同构群。

本接口的载体是曲线上的局部系统；[中央噪声卷定义 11.2、定理 9.2、推论 9.3、定理 10.2](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md)所用载体则是固定源、原始测度、原时钟和两吸收壁的扩散。后者的固定正中央噪声合同排除精确局部常扩散符号读出、精确局部欧氏动能长度/距离和原时钟的全起点全测试杀死响应对应。单一极点的拟合等式不等于这些全测试合同。这些既有排除不被这里的有限矩阵输运或 Hecke 谱点替代；匹配 Green 吸引形式的谱底和完整自场占用也不是 $E$ 或其自守对象。

**定理 97.2（紧实正则接口的实际半单本征对象）。** 若定理 92.2 的精确接口给 $K$ 值曲面表示，且其共同实 Lie 中心化子为零，则其复化谱局部系统 $E$ 无真抛物约化，$S_E$ 为有限群。在定义 97.1 的规范下，取 [Gaitsgory–Raskin I, §6.1.1](https://arxiv.org/html/2405.03599v3#S6.SS1.SSS1) 的等价下对应于

$$
\mathbb C[-20(g-1)]\in\operatorname{Vect}_{\mathbb C}
\tag{97.1}
$$

的本征范畴对象 $\widetilde{\mathcal F}_E$。其实际忘却对象 $\mathcal F_E$ 非零、正则 holonomic、位于半扭 $D$-模的 heart，且奇异支撑包含于全局 nilpotent cone，并有

$$
\mathcal F_E\simeq
\bigoplus_{\tau\in\operatorname{Irrep}(S_E)}
\mathcal F_{E,\tau}^{\oplus\dim\tau},
\tag{97.2}
$$

每个 $\mathcal F_{E,\tau}$ 是非零简单对象，彼此不同构。它携带对每个 $B\in\operatorname{Rep}(SO_5)$ 的

$$
\mathsf H_B(\mathcal F_E)\simeq E_B\boxtimes\mathcal F_E,
\tag{97.3}
$$

以及态射、单位、张量、交换、不同点外积、对角融合与导出高阶相容性。紧实正则条件本身不保证 $S_E=1$ 或 $\mathcal F_E$ 简单。

**证明。** 在标准 $\mathbb C^5$ 内写对称形式 $b(v,w)=v^{\mathsf T}w$，实单值还保持共轭和正 Hermitian 形式 $b(v,\bar v)$。若有非零不变全迷向子空间 $L$，则 $L\cap\bar L=0$：否则某个非零 $v$ 的 $v,\bar v$ 同在 $L$，与 $b(v,\bar v)>0$ 矛盾。$L$ 与 $\bar L$ 的交叉配对非退化，因其 Hermitian Gram 矩阵正定，故

$$
\mathbb C^5=(L\oplus\bar L)\oplus(L\oplus\bar L)^\perp
$$

是单值不变且共轭相容的正交分解。令 $J$ 在 $L$ 上为 $i$，在 $\bar L$ 上为 $-i$，在余项上为零。它与共轭交换，是非零实算子；由 $L,\bar L$ 各自全迷向且交叉特征值之和为零，$b(Jv,w)+b(v,Jw)=0$。因此 $J\in\mathfrak{so}(5)$ 且中心化全部单值，矛盾。正交群真抛物子群稳定一个非零全迷向子空间，反向相应稳定子为抛物，故无真抛物约化。这一步用紧实实形式，不能对任意复单值仅凭一个实中心化子断言同样结论。

由于各生成元实，复 Lie 中心化子是实 Lie 中心化子的复化，故为零。代数中心化子 $S_E\subset SO_5(\mathbb C)$ 是零维代数群，特征零下为有限群。路径系统按定理 86.2 所用的 Riemann–Hilbert/GAGA 解释为代数 de Rham 谱点。

后续消费已有的外部 GLC 供应，归属和规范不变：[Gaitsgory–Raskin V, §5.5](https://arxiv.org/html/2409.09856v3#S5.SS5)完成的全局等价适用于 $g\ge2$、almost simple、simply connected 且非 $SL_2$ 的 $Sp_4$；[I, §6.1.1、定理 6.1.3(1)–(4)](https://arxiv.org/html/2405.03599v3#S6.SS1.SSS2)对无真抛物约化的谱点给所述本征范畴等价、实际对象性质和分解。这里“不可约谱点”是原文的无真抛物约化条件，而非另行假设五维复不可约。

规范化移位沿用定理 90.2 的计算，在一般 $g$ 为

$$
\dim\operatorname{Bun}_{Sp_4}=10(g-1),\qquad
\dim\operatorname{Bun}_{N,\varrho(\omega_X)}=-10(g-1).
$$

具体地，四个正根高度 $1,1,2,3$ 给分次线丛 $\omega_X,\omega_X,\omega_X^2,\omega_X^3$，Riemann–Roch 的 Euler 数之和为 $[1+1+3+5](g-1)=10(g-1)$，unipotent 丛堆维数为其负数。因此 I §6.1.1 的移位恰为 (97.1)。实际忘却对象的正则性、nilpotent 奇异支撑、heart 性和 (97.2) 来自 I 定理 6.1.3(1)–(4)；简单项非零，故实际对象非零，不能只从本征范畴对象非零推出这一点。完整 Hecke 相容性由定义 97.1 的 DG 基变换与原文忘却函子保留，而非逐个任取孤立本征同构。$Z(Sp_4)=\mu_2$ 不连通，所以不使用 I 定理 6.1.3(5) 的额外特征循环等式。$\square$

**命题 97.3（正则与简单性的有限单值区别）。** 在亏格二曲面将四个标准生成元依次送到

$$
\begin{aligned}
D_1&=\operatorname{diag}(-1,-1,1,1,1),&
D_2&=\operatorname{diag}(-1,1,-1,1,1),\\
D_3&=\operatorname{diag}(-1,1,1,-1,1),&
D_4&=\operatorname{diag}(-1,1,1,1,-1).
\end{aligned}
$$

这给 $K$ 表示，公共 Lie 中心化子为零，但五维复表示可约；无真抛物约化，而 $S_E\simeq\mu_2^4$ 有十六个元素。定理 97.2 的实际规范对象恰有十六个彼此不同构的非零简单直和项，各出现一次。

**证明。** 四矩阵对角、行列式为一且交换，曲面关系成立。它们独立生成整个行列式一对角符号群。五个坐标的共同特征依次为 $(-,-,-,-)$、$(-,+,+,+)$、$(+,-,+,+)$、$(+,+,-,+)$、$(+,+,+,-)$，彼此不同。因此任一共同交换矩阵为对角矩阵；对角反对称矩阵为零，给零 Lie 中心化子。$SO_5(\mathbb C)$ 中对角交换元满足各对角元平方为一且乘积为一，故中心化子恰为 $\mu_2^4$。每个不变子空间为若干不同特征坐标线的和，标准对称形式在其上非退化，故不存在非零全迷向不变子空间，同时每条坐标线不变，五维表示可约。有限交换群 $\mu_2^4$ 有十六个一维不可约表示，代入 (97.2) 即得最后结论。$\square$

**推论 97.4（五维复不可约精确接口的简单对象）。** 若定义 92.1 的精确增强路径输入在光滑射影 $X$、$g\ge2$ 上给五维复不可约的 $SO_5(\mathbb C)$ 单值，则 $S_E=1$，定义 97.1 下对应 $\mathbb C[-20(g-1)]$ 的本征对象，其实际忘却对象本身是非零简单、正则 holonomic 的半扭 $Sp_4$ 本征层，位于 heart 且有 nilpotent 奇异支撑，并保留 (97.3) 的全部高阶相容数据。此结论无需 Spin 提升，也无需单值稠密。

**证明。** 任一真抛物约化给非零真全迷向不变子空间，与五维复不可约矛盾。Schur 引理使标准表示的全部交换算子为标量；$SO_5$ 中的标量满足 $c^2=c^5=1$，所以 $c=1$，即 $S_E=1$。使用定理 97.2 证明中已列的同一外部 GLC 供应及一般亏格的移位计算；其中外部应用只需无真抛物约化，不依赖该定理前半部的紧实推导。分解 (97.2) 于是只有一个非零简单项。定理 94.2 的修正若从五维复不可约基点出发，可由命题 94.3 缩图保留这一假设。对既有亏格三稠密 $\rho_n$，标准五维表示不可约，本推论直接复用定理 90.2 的 $-40$ 对象；不另构造第二份该族。有限记录的附近精确拟合对象也只在它自己的谱点消费这一结论，没有由矩阵误差产生自守范畴误差范数、有限闭式、物理制备或复杂度界。$\square$

## 追加锚（本行以下为增补区）

## 78. 有限交叉 Gram 到带校准的紧实路径接口

**定义 98.1（同一来源的有限相干路径数据）。** 对 $2g$ 个标记生成元 $s$，供应同一有标架复向量空间内的矩阵 $G=G^*>0$、$C_s$，其中星号表示 Hermitian 伴随，并要求

$$
\mathcal B_s=\begin{pmatrix}G&C_s\\C_s^*&G\end{pmatrix}\succeq0,
\qquad \operatorname{rank}\mathcal B_s=d.
\tag{98.1}
$$

两组标签分别指输运前、后的同一组生成向量；各生成元的上方 Gram 都是同一个 $G$。标签、交叉相位及共同实现是输入，不由单来源的静态概率菜单自动取得。用于 §74 的共同校准紧实实标架，另指一个已供应的复线性同构 $F:W_{14}\to\mathbb C^{14}$：拉回增强张量为 $(b_0,d_0)$，而所用输运在该标架内保持 $W_{14,\mathbb R}$。范数按该实标架中的标准 Frobenius 结构计量；标架及其条件数必须与记录一起给定或另行认证。

**定理 98.2（有限 Gram 的恢复、误差及增强路径下降）。** 定义 98.1 唯一恢复

$$
T_s=G^{-1}C_s,\qquad T_s^*GT_s=G.
\tag{98.2}
$$

反向，每个 $G$-酉矩阵都满足 (98.1)。若 $\lambda_{\min}(G)\ge a>0$，且

$$
\|\widehat G-G\|_{\mathrm{op}}\le\varepsilon,
\quad \|\widehat C_s-C_s\|_{\mathrm{op}}\le\varepsilon,
\quad \varepsilon<a/2,
$$

则 $\widehat T_s=\widehat G^{-1}\widehat C_s$ 存在，且

$$
\|\widehat T_s-T_s\|_{\mathrm{op}}
\le\frac{2\varepsilon}{a}
\left(1+\sqrt{\frac{\lambda_{\max}(G)}a}\right).
\tag{98.3}
$$

当 $d=14$，输入还供应定义 92.1 的标准型增强张量时，保持两张量且满足曲面关系的 $T_s$，经定理 92.2 唯一给一个有标架 $SO_5(\mathbb C)$ 曲面表示。若再供应定义 98.1 的共同校准紧实实标架，则该表示在此标架内取值于 $K$。近似输入必须先在这个共同实标架中作 §74 的张量修正，再对所得 $K$ 元组使用定理 99.4 的显式关系修正；(98.3) 本身不认证张量、实结构或曲面关系。

**证明。** 在本接口内使用经典 Schur 补恒等式：对 (98.1) 左右作互为伴随的可逆块三角合同，得到

$$
\operatorname{diag}(G,G-C_s^*G^{-1}C_s),\qquad
\operatorname{rank}\mathcal B_s
=d+\operatorname{rank}(G-C_s^*G^{-1}C_s).
$$

秩条件使第二块为零，代入 $T_s$ 即得 (98.2)。有限维等距可逆；$GT_s=C_s$ 的唯一性由 $G$ 可逆给出。反向对任意 $G$-酉 $T$，取 $C=GT$，上式合同得到 $\operatorname{diag}(G,0)$，同时给正性和秩。

最小奇异值扰动给 $\|\widehat G^{-1}\|_{\mathrm{op}}\le(a-\varepsilon)^{-1}<2/a$，而

$$
\widehat G(\widehat T_s-T_s)
=(\widehat C_s-C_s)-(\widehat G-G)T_s.
$$

又 $G^{1/2}T_sG^{-1/2}$ 为通常酉矩阵，故
$\|T_s\|_{\mathrm{op}}\le\sqrt{\lambda_{\max}(G)/\lambda_{\min}(G)}$，合并即得 (98.3)。此论证甚至不要求带噪 $\widehat G$ 恰为 Hermitian。

增强下降直接消费 (92.2) 的忠实稳定子与定理 92.2 的关系下降。在共同实标架内，$R(u_s)=F^{-1}T_sF$ 为实矩阵，所以 $R(\bar u_s)=R(u_s)$；忠实性给 $u_s=\bar u_s\in K$。近似矩阵的实性必须同样供应；仅近似实的输入可先取实部，但须计入这一步误差。定理 94.2 证明的紧实管状估计 (94.3) 将小张量缺陷的实矩阵送入 $R(K)$，其逆再给 $K$ 元组。改变标架时，(98.3) 的误差至多乘 $\|F^{-1}\|_{\mathrm{op}}\|F\|_{\mathrm{op}}$；十四维算子范数转 Frobenius 范数再至多乘 $\sqrt{14}$。这些固定接口损失与关系修正的残差均须实际计入。

这里 $14=\dim\operatorname{Sym}^2_0(\mathbb C^5)$ 是表示维数，不是原生五模式的数量。本定理是 Schur 补、§72 的增强稳定子和 §74 的实修正接口的综合应用，不主张 Schur 补或张量重构本身的新意。$\square$

**命题 98.3（复 Gram 条件不交付指定实标架）。** 同时 $G$-酉且保持标准增强张量的矩阵，在指定标准标架中仍可非实。因此从一般复 Gram 恢复直接进入 §74 的实紧实估计，需要独立的共同标架供应。

**证明。** 取 $u\in\mathbb R\setminus\{0\}$，$h=\exp(iuJ_{12})\in SO_5(\mathbb C)$，及
$k=\operatorname{diag}(-1,1,-1,1,1)\in K$。$hkh^{-1}$ 的 $12$ 块有非零纯虚非对角元。置

$$
H=R(h),\qquad T=HR(k)H^{-1},\qquad
G=(H^{-1})^*H^{-1},\qquad C=GT.
$$

则 $T^*GT=G$，$T$ 保持 $(b_0,d_0)$，且 $(G,C)$ 满足 (98.1)。若 $T$ 在标准标架中为实，$R(\overline{hkh^{-1}})=R(hkh^{-1})$ 会由忠实性迫使 $hkh^{-1}$ 为实，矛盾。本例有另一个实标架 $F=H$，但这不使原标架中的矩阵变实，也不免费供应未知标架或其误差。一般紧子群的可共轭紧实约化是另一个存在性命题，不能替代一个带数值误差控制的共同校准实标架。$\square$

## 79. 两个交换子谱隙和离关系面的显式修正

**定义 99.1（实 Lie 谱隙、复标准谱隙及两种距离）。** 在 $K$ 上取 Frobenius 内积诱导的双不变测地距离 $d_K$。对 $z=(A_1,B_1,\ldots,A_g,B_g)\in K^{2g}$，令

$$
\mathscr C_zX=([z_s,X])_{s=1}^{2g},\qquad
\sigma_{10}(z)=\inf_{\substack{X\in\mathfrak{so}(5)\\\|X\|_F=1}}\|\mathscr C_zX\|,
\qquad
\sigma_{24}(z)=\inf_{\substack{X\in\operatorname{End}_0(\mathbb C^5)\\\|X\|_F=1}}\|\mathscr C_zX\|.
\tag{99.1}
$$

余域使用各分量平方和范数，复空间用 Hermitian Frobenius 内积；下标 $10$ 是实维数，下标 $24$ 是复维数。定义

$$
e_2(z,w)^2=\sum_s\|z_s-w_s\|_{\mathrm{op}}^2,
\qquad d_2(z,w)^2=\sum_s d_K(z_s,w_s)^2.
\tag{99.2}
$$

沿群内曲线积分给 $e_2\le d_2$。因 $[z_s,X]z_s^{-1}=(\operatorname{Ad}_{z_s}-I)X$，交换子与 Ad 差的分量范数相等。

**定理 99.2（有限谱隙的含义与严格误差认证）。** 对任意上述元组，包括不满足曲面关系的元组，有

$$
0\le\sigma_{24}(z)\le\sigma_{10}(z)\le2\sqrt{2g},
\tag{99.3}
$$

$$
\sigma_{10}(z)>0\iff\mathfrak z_z=0,
\qquad
\sigma_{24}(z)>0\iff\mathbb C^5\text{ 的共同复表示不可约}.
\tag{99.4}
$$

对于 $j=10,24$，

$$
|\sigma_j(z)-\sigma_j(w)|\le2e_2(z,w)\le2d_2(z,w).
\tag{99.5}
$$

若 $E_\alpha$ 是相应定义域的正交基，有限 Gram 矩阵

$$
\Gamma_j(z)_{\alpha\beta}
=\sum_s\operatorname{tr}([z_s,E_\alpha]^*[z_s,E_\beta])
\tag{99.6}
$$

的最小特征值恰为 $\sigma_j(z)^2$；实 Lie 域取实内积，迹在此已实。因而误差证书 $e_2(z,w)\le a$ 与 $\sigma_j(w)>2a$ 认证对应的真实严格性质。$\sigma_{10}$ 只认证 Lie 正则；不能代替 $\sigma_{24}$ 的五维复不可约认证。

**证明。** 实反对称矩阵包含于复无迹矩阵，且每个交换子范数至多 $2\|X\|_F$，得 (99.3)。有限维紧单位球使最小值取得，故第一个等价是核为零。第二个等价的不可约方向用 Schur 引理；反向若有真复不变子空间，酉性使其正交补不变，正交投影减去其迹除以五倍恒等，给非零无迹交换算子。

对任意单位 $X$，

$$
\|(\mathscr C_z-\mathscr C_w)X\|^2
\le4\sum_s\|z_s-w_s\|_{\mathrm{op}}^2.
$$

取下确界并交换两元组，得到 (99.5)；(99.6) 是此线性映射的伴随平方矩阵。这些有限维事实在此共同服务于定理 99.4 的可用输入与定理 100.1 的分层计数。$\square$

**引理 99.3（不预设关系的伴随下界）。** 把 $D\mathcal R_z$ 的目标右平凡化为 $\mathfrak{so}(5)$，记为 $D_z$，源用 $\delta A_i=X_iA_i$、$\delta B_i=Y_iB_i$ 平凡化。对所有 $z\in K^{2g}$ 及 $Z\in\mathfrak{so}(5)$，

$$
\|\mathscr C_zZ\|\le8g\|D_z^*Z\|,
\qquad
\|D_z^*Z\|\ge\frac{\sigma_{10}(z)}{8g}\|Z\|_F.
\tag{99.7}
$$

若 $\sigma_{10}(z)>0$，$D_z$ 满射且其最小范数右逆
$H_z=D_z^*(D_zD_z^*)^{-1}$ 满足 $\|H_z\|\le8g/\sigma_{10}(z)$。

**证明。** 令 $C_i=[A_i,B_i]$、$P_i=C_1\cdots C_{i-1}$。逐项用
$\delta(MN)(MN)^{-1}=\delta M M^{-1}+\operatorname{Ad}_M(\delta N N^{-1})$
和 $\delta M^{-1}=-M^{-1}(\delta M)M^{-1}$，得到在全部元组上成立的公式

$$
D_z(X,Y)=\sum_i\operatorname{Ad}_{P_i}
\left[(I-\operatorname{Ad}_{A_iB_iA_i^{-1}})X_i
+(\operatorname{Ad}_{A_i}-\operatorname{Ad}_{C_i})Y_i\right].
\tag{99.8}
$$

这是 (94.4) 的右平凡化版本，不要求 $\mathcal R(z)=I$。置
$Z_i=\operatorname{Ad}_{P_i^{-1}}Z$、$U_i=\operatorname{Ad}_{A_i}$、$V_i=\operatorname{Ad}_{B_i}$、$W_i=U_iV_iU_i^{-1}$。写伴随的两个分量及其范数为

$$
Q_i=(I-W_i^{-1})Z_i,\quad
P'_i=(U_i^{-1}-\operatorname{Ad}_{C_i^{-1}})Z_i,
\quad q_i=\|Q_i\|,\quad p_i=\|P'_i\|,\quad v_i=p_i+q_i.
$$

于是 $h^2:=\|D_z^*Z\|^2=\sum_i(p_i^2+q_i^2)$，$\|v\|_2\le\sqrt2h$。所有 Ad 为等距。固定 $i$ 并置 $a_i=U_i^{-1}Z_i$。由 $W_i=U_iV_iU_i^{-1}$ 及 $C_i^{-1}=B_i(A_iB_iA_i^{-1})^{-1}$，有

$$
\|(I-V_i^{-1})a_i\|=q_i,
\quad \|a_i-\operatorname{Ad}_{C_i^{-1}}Z_i\|=p_i,
\quad \|\operatorname{Ad}_{C_i^{-1}}Z_i-V_iZ_i\|=q_i.
$$

因此 $\|a_i-V_iZ_i\|\le p_i+q_i$。再用 $V_i^{-1}$，得到

$$
\begin{aligned}
\|a_i-Z_i\|
&\le\|a_i-V_i^{-1}a_i\|+\|V_i^{-1}a_i-Z_i\|
\le p_i+2q_i,\\
\|(U_i-I)Z_i\|&\le p_i+2q_i\le2v_i,\\
\|(V_i-I)Z_i\|&\le2p_i+3q_i\le3v_i,\\
\|\operatorname{Ad}_{C_i^{-1}}Z_i-Z_i\|&\le2p_i+2q_i=2v_i.
\end{aligned}
\tag{99.9}
$$

由于 $Z_{i+1}=\operatorname{Ad}_{C_i^{-1}}Z_i$，归纳给
$\|Z_i-Z\|\le2\sum_{j<i}v_j$。$\|U_i-I\|,\|V_i-I\|\le2$，故

$$
\|(U_i-I)Z\|\le2v_i+4\sum_{j<i}v_j,
\quad
\|(V_i-I)Z\|\le3v_i+4\sum_{j<i}v_j.
\tag{99.10}
$$

令 $Sv=(\sum_{j<i}v_j)_i$。其严格下三角全一矩阵的行和、列和均至多 $g-1$，所以 $\|S\|_{2\to2}\le g-1$，$g=1$ 时它为零。对 (99.10) 的两组分量用平方和三角不等式，得到

$$
\|\mathscr C_zZ\|
\le\sqrt{13}\|v\|_2+4\sqrt2\|Sv\|_2
\le\bigl(\sqrt{26}+8(g-1)\bigr)h
\le8g h.
$$

这证明 (99.7)。正下界使 $D_z^*$ 单射，有限维对偶性给 $D_z$ 满射；对奇异值取倒数即得右逆界。$\square$

**定理 99.4（当前残差到精确平坦元组的显式证书）。** 对当前 $z\in K^{2g}$，供应严格下界 $0<s\le\sigma_{10}(z)$，记

$$
r=d_K(I,\mathcal R(z)).
$$

若 $r<s^2/(64g)$，则存在 $z^\sharp\in K^{2g}$，满足

$$
\mathcal R(z^\sharp)=I,\qquad
d_2(z,z^\sharp)\le\frac{16g}{s}r<\frac s4,
\qquad \sigma_{10}(z^\sharp)>s/2.
\tag{99.11}
$$

若还有 $s\le\sigma_{24}(z)$，同一修正满足 $\sigma_{24}(z^\sharp)>s/2$。无需预先知道附近某个正则精确点。$r=0$ 时取 $z^\sharp=z$。

**证明。** 在开球 $d_2(z,w)<s/4$ 上，(99.5) 给
$\sigma_{10}(w)\ge\sigma_{10}(z)-2d_2(z,w)>s/2$，故引理 99.3 的光滑最小范数右逆 $H_w$ 满足 $\|H_w\|<16g/s$。紧群的双不变度量下，取最短对数 $\eta\in\mathfrak{so}(5)$，使 $e^\eta=\mathcal R(z)$、$\|\eta\|_F=r$。目标路径为 $\gamma(t)=e^{(1-t)\eta}$，右平凡化速度恒为 $-\eta$。

从 $z(0)=z$ 解源流形上的光滑常微分方程，其右平凡化速度为 $H_{z(t)}(-\eta)$。在存在区间内，(99.8) 和右逆恒等式说明 $\mathcal R(z(t))$ 与 $\gamma(t)$ 满足相同初值和目标右速度，故二者相等。其长度满足

$$
\operatorname{length}(z|_{[0,t]})
\le\frac{16g}{s}rt\le\frac{16g}{s}r<s/4.
$$

取 $\ell_0=(16g/s)r<s/4$。曲线始终位于紧流形 $K^{2g}$ 中的闭球 $\overline B(z,\ell_0)$，它完整包含于右逆光滑的开球内。该紧集上的向量场及其局部 Lipschitz 常数有界，故常微分方程的延拓定理排除任何小于一的最大存在时刻。令 $z^\sharp=z(1)$ 即得关系和距离。再次用 (99.5)，
$\sigma_{10}(z^\sharp)\ge s-2d_2(z,z^\sharp)>s/2$；对 $\sigma_{24}$ 用同一计算。

所有三个数值 $8g$、$s^2/(64g)$、$16g/s$ 分别来自 (99.7)、留在半谱隙球的长度判据、及球内右逆界。这是存在性、修正距离和条件数结论；不包括免费精确 ODE 求解。若输入尚非 $K$ 元组，先作定义 98.1 和 (94.3) 所要求的实标架及张量修正，或另行认证投影到 $K$ 的误差，再重新量取这里的 $s,r$。$\square$

## 80. 紧实正则层的有限中心化子与实际项数

**定理 100.1（交换子核维数控制忘却对象的简单项数）。** 设 $z\in K^{2g}$、$\sigma_{10}(z)>0$，令

$$
q(z)=\dim_{\mathbb C}\ker(\mathscr C_z|_{\operatorname{End}_0(\mathbb C^5)}).
$$

则 $0\le q\le4$，并有复代数群同构

$$
Z_{SO_5(\mathbb C)}(z)\simeq\mu_2^{q(z)}.
\tag{100.1}
$$

若 $z$ 满足曲面关系且 $g\ge2$，在定义 97.1 的同一曲线与半扭规范下，实际规范忘却对象 $\mathcal F_{E_z}$ 恰有 $2^{q(z)}$ 个非零、彼此不同构的简单直和项，各重数一。故项数只能属于 $\{1,2,4,8,16\}$；不由此断言任一固定取得菜单实现所有五种数目。

**证明。** 记复交换代数为 $\mathfrak A_z$。实正交性使它对转置及 Hermitian 伴随都封闭。若 $X\in\mathfrak A_z$，则 $(X-X^{\mathsf T})/2$ 属于复 Lie 中心化子；其实部、虚部都属于零的实 Lie 中心化子，所以 $X=X^{\mathsf T}$。对于 $X,Y\in\mathfrak A_z$，$XY-YX$ 仍在此代数且反对称，故为零。因此 $\mathfrak A_z$ 是有限维交换 $C^*$-代数，谱分解给

$$
\mathfrak A_z=\bigoplus_{j=1}^{r}\mathbb CP_j,\qquad
P_jP_k=0\ (j\ne k),\qquad \sum_jP_j=I.
$$

这里使用有限维交换正规算子的同时酉对角化这一经典线性代数输入。最小投影 $P_j$ 既 Hermitian 又对称，所以为实正交投影。各块的复交换代数只有标量，因此各块绝对不可约；若两块同构，非对角交织算子会属于 $\mathfrak A_z$，与此分解矛盾。故得到重数一、两两不同构的实正交块。令 $d_j=\operatorname{rank}P_j\ge1$，则 $\sum_jd_j=5$，$r\le5$。迹在 $\mathfrak A_z$ 上是非零线性泛函，所以 $q=r-1$。

每个正交交换元唯一为 $\sum_j\varepsilon_jP_j$，其中 $\varepsilon_j^2=1$；特殊正交条件为

$$
\prod_j\varepsilon_j^{d_j}=1.
$$

至少一个 $d_j$ 为奇数，故这是 $\mu_2^r$ 上一个非平凡字符的核，作为复代数群同构于 $\mu_2^{r-1}$。这证明 (100.1)。

实际对象的应用直接复用定理 97.2：紧实 Lie 正则使谱点无真抛物约化，$S_E$ 就是 (100.1)。[Gaitsgory–Raskin I，定理 6.1.3(1)–(4)](https://arxiv.org/html/2405.03599v3#S6.SS1.SSS2) 的条件是这种无真抛物约化，而不是标准五维不可约；GLC 的 $Sp_4$ 输入由 [V，§5.5](https://arxiv.org/html/2409.09856v3#S5.SS5) 及 §77 的规范供应。$\mu_2^q$ 恰有 $2^q$ 个一维不可约表示，代入 (97.2)，每个简单项非零、互不相同，得所述数目与重数。本条是精确交换子核与该实际对象供应的综合推论，不将有限群表示分解当作另一个几何朗兰兹定理。$\square$

**命题 100.2（有限精度只能给所述项数上界）。** 将 $\mathscr C_w$ 在复无迹空间的奇异值升序写为 $\lambda_1(w),\ldots,\lambda_{24}(w)$。若 $e_2(z,w)\le a$，则对 $0\le q\le23$，

$$
\lambda_{q+1}(w)>2a\quad\Longrightarrow\quad
\dim_{\mathbb C}\ker(\mathscr C_z|_{\operatorname{End}_0(\mathbb C^5)})\le q.
\tag{100.2}
$$

若真实 $z$ 的曲面关系和 Lie 正则另已认证，则其实际简单项数至多 $2^q$；也可合并 $q(z)\le4$ 改为 $2^{\min(q,4)}$。有限误差并不自动认证精确零奇异值的个数。

**证明。** (99.5) 的算子差估计实际上给所有奇异值的相同 $2a$ 扰动界：由极小极大刻画，在每个固定维数子空间上比较映射范数，再取对应极值即可。若真实核维数至少 $q+1$，则 $\lambda_{q+1}(z)=0$，与假设矛盾。最后使用 (100.1) 及实际分解计数。下一节的连续族在统一 Lie 正则域中有精确核维数跳变，因而也给最后一句的具体边界。$\square$

## 81. 同一 Spin 类中的十六到一跳变和线性小谱隙

**定理 101.1（显式一致正则的曲面族）。** 在同一亏格三的光滑射影复曲线及标记上，令全部 $B_i(t)=I$，并取

$$
\begin{aligned}
D_1&=\operatorname{diag}(-1,-1,1,1,1),\\
D_2&=\operatorname{diag}(-1,1,-1,1,1),\\
D_3&=\operatorname{diag}(-1,1,1,-1,1),\\
A_1(t)&=R_{12}(\pi+t)R_{34}(2t),\\
A_2(t)&=\exp\bigl(t(J_{25}+J_{45})\bigr)D_2,\qquad
A_3(t)=D_3,\qquad 0\le t\le1/10,
\end{aligned}
\tag{101.1}
$$

其中 $R_{ij}(\theta)=\exp(\theta J_{ij})$、$J_{ij}=E_{ij}-E_{ji}$。这些连续门是本族明示的参数权限，不声称为定义 86.1 固定三门菜单的精确有限字。写对应元组为 $z(t)$，则

$$
\mathcal R(z(t))=I,\quad\kappa(z(t))=1,\quad
\sigma_{10}(z(t))\ge2-2\sqrt{14}\,t>1,
\tag{101.2}
$$

$$
q(z(0))=4,\qquad q(z(t))=0\quad(0<t\le1/10),\qquad
\sigma_{24}(z(t))=\Theta(t)\quad(t\downarrow0).
\tag{101.3}
$$

所以同一族的规范实际忘却对象在零点有十六个互不同构的非零简单项，而在每个正参数处自身简单。

**证明。** $B_i=I$ 使关系精确成立；取这些 $B_i$ 的 Spin 提升为一，每个提升交换子也为一，故定义 95.1 的 $\kappa=1$。这只固定提升存在性的障碍类；仍不选定 $H^1(X;\mu_2)$ 挠集中的一个提升标签。

在零点，五个坐标的联合符号依次为

$$
(-,-,-),\quad(-,+,+),\quad(+,-,+),\quad(+,+,-),\quad(+,+,+).
$$

彼此不同使全部复交换算子恰为对角矩阵，故 $q=4$。在 Lie 正交基 $J_{ij}/\sqrt2$ 中，$\mathscr C_{z(0)}^*\mathscr C_{z(0)}$ 对角，相应值为四倍的上述两个符号列的 Hamming 距离。最小距离为一，得 $\sigma_{10}(z(0))=2$。

$A_1(t)=D_1\exp(t(J_{12}+2J_{34}))$ 的 Frobenius 速度为 $\sqrt{10}$，$A_2$ 的为 $\|J_{25}+J_{45}\|_F=2$。在所给角度范围内这些一参数段是最短测地线，故

$$
d_2(z(t),z(u))=\sqrt{14}\,|t-u|\qquad(0\le t,u\le1/10).
\tag{101.4}
$$

也可只用其长度上界推出全部下述估计。由 (99.5)，得到 (101.2)，因为 $2-\sqrt{14}/5>1$。

当 $0<t\le1/10$，$A_1(t)$ 的五个特征值
$-e^{it},-e^{-it},e^{2it},e^{-2it},1$ 两两不同，其特征向量可选为 $e_1\pm ie_2,e_3\pm ie_4,e_5$。同时

$$
A_2(t)e_5=\cos(\sqrt2t)e_5+
\frac{\sin(\sqrt2t)}{\sqrt2}(e_2+e_4).
$$

后者在前四个特征方向上全有非零系数。与 $A_1$ 交换的任意复算子在此特征基中对角；将它与 $A_2$ 交换的等式作用于 $e_5$，每个非零系数使对应对角元等于第五个。因此共同交换代数为标量，$q=0$，并由 (99.4) 得 $\sigma_{24}>0$。

现给线性阶的完整下界。上界由 $\sigma_{24}(z(0))=0$ 和 (99.5)、(101.4) 给出
$\sigma_{24}(z(t))\le2\sqrt{14}\,t$。若不存在正的局部线性下界，则可取 $t_n\downarrow0$ 和单位无迹复矩阵 $X_n$，使
$\|\mathscr C_{z(t_n)}X_n\|=o(t_n)$。有限维紧致性给子列 $X_n\to X$，$\|X\|_F=1$、$\operatorname{tr}X=0$。零阶交换式使 $X$ 与 $D_1,D_2,D_3$ 交换，所以 $X=\operatorname{diag}(x_1,\ldots,x_5)$。

关键是不能把 $[D_i,X_n]/t_n$ 全部丢掉。只读取 $D_1$ 同号的 $12,34$ 通道，以及 $D_2$ 同号的 $25,45$ 通道；在这四个通道中，对每个 $n$，零阶交换子恰为零，不依赖 $X_n$ 的收敛速率。展开

$$
A_1(t)=D_1+tD_1(J_{12}+2J_{34})+O(t^2),\qquad
A_2(t)=D_2+t(J_{25}+J_{45})D_2+O(t^2).
$$

将上述四个交换子矩阵元除以 $t_n$ 再取极限，分别得到

$$
x_1=x_2,\qquad x_3=x_4,\qquad x_2=x_5,\qquad x_4=x_5.
$$

四条边连通全部五个坐标，故 $X$ 为标量；无迹使 $X=0$，与单位范数矛盾。这证明存在 $c,t_0>0$ 使 $\sigma_{24}(z(t))\ge ct$ 于 $(0,t_0]$。在 $[t_0,1/10]$ 上，连续正函数 $\sigma_{24}(z(t))/t$ 取得正最小值，故可将下界延伸到整个参数区间。项数结论来自定理 100.1。$\square$

## 82. 特征循环比较与完整 Hecke 投影的障碍

**定理 102.1（显式跳变族的共同特征循环）。** 沿用定义 97.1 的半扭、theta characteristic、Whittaker 和同一曲线规范。定理 101.1 的全部谱点 $E_t$ 都在无真抛物约化域的同一个 Betti 连通分支上，且处于同一 Betti 不可约分支。相应实际忘却对象满足

$$
\operatorname{CC}(\mathcal F_{E_t})
=\operatorname{CC}(\mathcal F_{E_0})
=\sum_{\chi\in\widehat{\mu_2^4}}
\operatorname{CC}(\mathcal F_{E_0,\chi})
\qquad(0\le t\le1/10).
\tag{102.1}
$$

这是特征循环的比较，不无条件宣称其共同值等于 $[\operatorname{Nilp}]$。

**证明。** (101.2) 使全程共同实 Lie 中心化子为零，故定理 97.2 的紧实论证使每个 $E_t$ 都无真抛物约化。零点虽然五维可约，仍在这个域内；外部供应的 “irreducible local system” 正是无真抛物约化。亏格为三，符合比较所需的 $g\ge2$。

先核对分支而非从连续参数直接冒认某个 de Rham 分支。矩阵公式 (101.1) 给 $\operatorname{Hom}(\pi_1(X),SO_5(\mathbb C))$ 的连续实解析路径；取商后整个像在 Betti 无真抛物约化域，故在其中同一连通分支。也可直接检查此路径上的局部光滑性：复化 (99.8)，$D\mathcal R$ 满射，因为复 Lie 中心化子是零实 Lie 中心化子的复化；精确关系空间在这些点光滑，除以光滑的 $SO_5(\mathbb C)$ 得光滑局部堆。因此每点有唯一局部不可约分支，一条连续路径不能在这些光滑点之间跨越不同不可约分支的交点。与 [Gaitsgory–Raskin I，§6.3.4](https://arxiv.org/html/2405.03599v3#S6.SS3.SSS4) 中 Betti 无真抛物约化域光滑、其连通分支对应 Betti 全空间不可约分支的结论一致；此处具体路径的分支条件已逐项满足。$\kappa=1$ 是额外的固定拓扑数据，不用它单独推定分支。

外部比较的精确表述是 [I，定理 6.2.2](https://arxiv.org/html/2405.03599v3#S6.SS2.SSS2)：在同一不可约分支的两个无真抛物约化谱点，其规范对象的特征循环相等。这里使用其 §6.3.3–6.3.4 的 Betti 证明：对 nilpotent cone 各不可约分支的一般光滑余切点 $\xi$，相应谱侧完美对象在 Betti 无真抛物约化域上的纤维 Euler 数局部常值，而其值给 $\operatorname{ord}_\xi\operatorname{CC}(\mathcal F_E)$。这些 multiplicity 函数在上述路径上常值，故全部循环系数相同。正则 holonomic 对象经 Riemann–Hilbert 对应的 Betti 版本与定义 97.1 的实际对象采用 §6.1.1 的同一移位，所以这正是 (102.1) 左边所比较的特征循环，不要求此路径为 de Rham 代数族。右边由零点的十六项直接和及特征循环的可加性给出。

I §6.2.1 明确允许任意自守群 $G$，比较定理与 §6.3.4 不要求 $Z(G)$ 连通。相反，I 定理 6.1.3(5) 给所有此类点的 $\operatorname{CC}=[\operatorname{Nilp}]$ 时另要求 $g\ge2$ 且 $Z(G)$ 连通；这里自守群 $Sp_4$ 的中心为不连通的 $\mu_2$，不能直接用该项。若另行核定同一分支内一个点的该等式，则比较会传递它；本文只使用已核定的比较域与分支，不补入这样的锚点。$\square$

**定理 102.2（每个非平凡忘却投影均无完整 Hecke 提升）。** 对定理 101.1 中每个 $t$，规范完整 Hecke 对象 $\widetilde{\mathcal F}_{E_t}$ 满足

$$
\operatorname{End}^0_{\mathcal D_{\mathrm{Hecke},E_t}}
(\widetilde{\mathcal F}_{E_t})=\mathbb C.
\tag{102.2}
$$

在 $t=0$，十六项分解的任意非空真子集投影，均不能提升为这个完整 Hecke 对象的零次自同态。特别地，不存在保持原完整 Hecke 结构的非平凡直和分解。

**证明。** (101.2) 和定理 97.2 使 [I，§6.1.1](https://arxiv.org/html/2405.03599v3#S6.SS1.SSS1) 的本征范畴等价适用；其规范对象对应 $\mathbb C[-20(g-1)]=\mathbb C[-40]$。等价保全部映射复形，故零次自同态为 $\mathbb C$。忘却函子是 $\mathbb C$-线性并保恒等，因此任意零次自同态的像只能是 $\lambda\operatorname{id}_{\mathcal F_E}$。一个非零非恒等投影既不等于零，也不等于恒等，若等于标量恒等，其幂等性会强迫 $\lambda\in\{0,1\}$，矛盾。故每个这样的投影都没有提升，甚至不可能先提升成一个未要求幂等的零次态射。这比“不能全部提升”更强。十六个简单项是实际忘却半扭 $D$-模的项；不自动逐项继承原对象的全部 Hecke、融合与导出高阶相容性。$\square$

## 83. 有界路径张量任务、完备度量与紧共轭

**定义 103.1（有标架有限任务距离）。** 固定曲线的生成元和基点，令 $\mathcal X_g=\operatorname{Hom}(\pi_1(X),K)$，以有标架表示理解。对 $\rho,\sigma\in\mathcal X_g$，置

$$
\delta(\rho,\sigma)=\max_s\|\rho(s)-\sigma(s)\|_{\mathrm{op}},\qquad
\Delta_{D,L}(\rho,\sigma)
=\max_{\substack{1\le d\le D\\ |w|\le L}}
\|\rho(w)^{\otimes d}-\sigma(w)^{\otimes d}\|_{\mathrm{op}},
\tag{103.1}
$$

其中 $D,L\ge1$ 为整数，字母包括生成元及其逆，空字也允许。各任务用标准表示、固定等距嵌入及固定范数至多一的交织消费；不能针对两个来源任意换用不同标架或不同嵌入。

**定理 103.2（两种有限任务界及任意指定代数表示）。** 对 (103.1)，

$$
\Delta_{D,L}(\rho,\sigma)\le\min\{2,DL\delta(\rho,\sigma)\}.
\tag{103.2}
$$

若有若干外积因子，第 $j$ 个因子的张量阶与路径长分别为 $d_j,\ell_j$，其总误差至多

$$
\min\left\{2,\delta(\rho,\sigma)\sum_j d_j\ell_j\right\}.
\tag{103.3}
$$

固定等距压缩、直和及两侧范数至多一的固定交织算子不放大相应界。每个指定的有限维代数 $SO_5(\mathbb C)$-表示，在固定酉实现下具有某个有限张量预算，因而其指定有限路径任务享有上述控制；不包含只能定义在 Spin 双覆盖上的表示。

**证明。** 酉性给 $\|U^{-1}-V^{-1}\|=\|U-V\|$。对一个长度为 $\ell$ 的词作有序乘积望远镜展开，每项的左右乘子范数均一，故 $\|\rho(w)-\sigma(w)\|\le\ell\delta$。对 $d$ 个张量因子再次望远镜展开，给 $d\ell\delta$。多点外积采用每个因子自身的差界再展开，得各 $d_j\ell_j$ 的和；两酉算子的距离恒不超过二。直和的算子范数取最大，等距压缩及所述交织算子均为压缩，因此不放大。

张量生成的确切外部输入为 [Deligne–Milne，*Tannakian Categories*，命题 2.20(b)、2.21(b)](https://www.jmilne.org/math/xnotes/tc2022.pdf)：仿射代数群的忠实有限维表示连同其对偶给张量生成子，闭浸入对应所有表示均为限制表示的子商。标准 $SO_5$ 表示忠实、自对偶，故每个代数表示是有限个标准张量幂直和的子商。这里“子商”到“等距直和项”的步骤还使用紧群酉性：任意有限维 $K$-不变子空间的正交补也不变，商可用此补空间等距实现。固定一个这样的实现并给表示空间配上所得酉度量后，任务就是已估计的张量幂直和的固定等距压缩。等价的经典论证是对 $K$ 平均 Hermitian 形式；不从张量生成自动取得一个可执行的路径服务，也不对未指定的无限表示阶给统一常数。$\square$

**定理 103.3（加权有限任务度量的拓扑、完备性和紧共轭分离）。** 定义

$$
d_{\mathrm{fin}}(\rho,\sigma)
=\sum_{D,L\ge1}2^{-(D+L)}\min\{1,\Delta_{D,L}(\rho,\sigma)\}.
\tag{103.4}
$$

它是 $\mathcal X_g$ 上的度量，且

$$
\frac14\min\{1,\delta\}\le d_{\mathrm{fin}}\le4\delta.
\tag{103.5}
$$

$\mathcal X_g$ 在此度量下紧致、完备。共同紧共轭的商距离

$$
\overline d_{\mathrm{fin}}([\rho],[\sigma])
=\min_{k\in K}d_{\mathrm{fin}}(\rho,k\sigma k^{-1})
\tag{103.6}
$$

是 $\mathcal X_g/K$ 上的紧致完备度量，并且分离这些紧实谱点作为复 $SO_5$ 局部系统的同构类。正则域或五维不可约域自身是开子空间，不能由全空间完备性推出它们自身完备。

**证明。** 每个 $\Delta_{D,L}$ 是伪度量：算子范数三角不等式在共同任务上成立，取最大仍成立。$x\mapsto\min(1,x)$ 保次可加性，因此 (103.4) 三角不等式成立。级数由权重总和一统一控制；$D=L=1$ 时恰有 $\Delta_{1,1}=\delta$，得正定性及下界。上界由 (103.2) 和

$$
\sum_{D,L\ge1}2^{-(D+L)}DL
=\left(\sum_{n\ge1}n2^{-n}\right)^2=4
$$

给出。又 $0\le\delta\le2$，故 $\delta/8\le d_{\mathrm{fin}}\le4\delta$；两度量拓扑与 Cauchy 列相同。曲面关系集是紧空间 $K^{2g}$ 内连续关系映射的闭纤维，因而紧致，并在 $\delta$、继而 $d_{\mathrm{fin}}$ 下完备。

共同 $K$ 共轭在每个任务上保持算子范数，故等距作用。紧致性使 (103.6) 的最小值取得；零距离使两表示由某个 $k$ 精确共轭。将两次最小化的共轭元相乘并用等距性及三角不等式，给商的三角不等式。商为紧空间的连续像，故紧致；度量紧致蕴含完备。

还须核对复同构是否把不同紧轨道合并。若某个 $h\in SO_5(\mathbb C)$ 交织两个实正交元组，写 $h=U+iV$，则实矩阵 $U,V$ 各自交织。实系数多项式 $\det(U+\lambda V)$ 不恒为零，因为在 $\lambda=i$ 处为 $\det h=1$。选一个实 $\lambda$ 使 $T=U+\lambda V$ 可逆。由 $T\rho(s)=\sigma(s)T$ 及正交性，$T^{\mathsf T}T$ 与全部 $\rho(s)$ 交换；其正定平方根也交换。故

$$
k=T(T^{\mathsf T}T)^{-1/2}\in O(5,\mathbb R)
$$

仍交织。若 $\det k=-1$，以 $-k$ 代之；五维奇数性使新行列式为一，且交织关系不变。因此复同构恰对应一个 $K$ 轨道，得到分离。这里的距离仍来自紧代表与紧共轭最小化，不宣称任意复标架变换保持算子范数。

最后，开子空间确实可能不完备。取定义 86.1 的三个 Lie 生成元，另以 $u_j(t)=\exp(tA_j)$、$B_j=I$，$0<t\le1/10$，构成精确表示。各 $A_j$ 的谱在 $\{0,i,-i\}$，在此角度范围内主对数为 $tA_j$，且在有限谱上为 $u_j(t)$ 的多项式。任一共同复不变子空间因而也被所有 $A_j$ 保持，由既有的 Lie 生成性被整个 $SO_5$ 保持，所以只有零和全空间。故这些表示五维复不可约、Lie 正则，却在 $t\downarrow0$ 时收敛于平凡表示；它们是开域内无域内极限的 Cauchy 列。$\square$

## 84. 无预算统一性的反例与同族三种现象

**命题 104.1（无界路径和无界张量阶的两个反例）。** 在亏格四，令所有 $B_i=I$，固定 $a_2,a_3,a_4$ 为定义 86.1 中的同一稠密门组（坐标重标为 $1,\ldots,5$），并取 $n\ge2$、

$$
\rho_n(a_1)=I,\qquad \sigma_n(a_1)=R_{12}(\pi/n).
\tag{104.1}
$$

则两族都精确平坦、像稠密且 $\kappa=1$，并有

$$
\delta_n=2\sin\frac{\pi}{2n}\longrightarrow0,
\quad \Delta_{1,n}(\rho_n,\sigma_n)=2,
\quad \Delta_{n,1}(\rho_n,\sigma_n)=2.
\tag{104.2}
$$

故有限预算稳定性不能提升为全部路径或全部张量阶的未加权一致稳定性；共同紧共轭后也不能消除此反例。

**证明。** 全部 $B_i=I$ 保证关系；其 Spin 提升取一，得 $\kappa=1$。三个固定门已生成稠密子群，增加第四个门不损失稠密性。唯一生成元差是 $R_{12}(\pi/n)-I$，其算子范数为 $2\sin(\pi/(2n))$。长度 $n$ 的词 $a_1^n$ 在两侧分别为 $I$ 和 $R_{12}(\pi)$，差范数二，证明第一个无界预算例。对长度一的词，取标准复表示中 $R_{12}(\pi/n)$ 的 $e^{i\pi/n}$ 特征向量 $v$，则 $v^{\otimes n}$ 的特征值为 $-1$，所以第 $n$ 张量幂到恒等的距离也为二，证明第二个。任何共同紧共轭都保持另一侧 $a_1$ 的像为恒等，旋转的幂和张量幂仍有 $-1$ 特征值，所以同样下界在共轭最小化后成立。这些新增连续旋转是反例的权限，未声称它们可由原三门菜单免费精确合成。$\square$

**定理 104.2（同一显式族的有限稳定、项数跳变与特征循环不变）。** 对定理 101.1 的同一个 $z(t)$，在 $W_{14,\mathbb R}$ 固定正交基，供应

$$
G(t)=I_{14},\qquad C_s(t)=R(z_s(t)).
\tag{104.3}
$$

则它们满足定义 98.1 的共同实校准 Gram 合同，增强张量 $(b_0,d_0)$ 与曲面关系精确保持。对于任意 $t,u\in[0,1/10]$，

$$
\begin{aligned}
\max_s\|C_s(t)-C_s(u)\|_{\mathrm{op}}
&\le2\sqrt{14}|t-u|,\\
\Delta_{D,L}(z(t),z(u))
&\le\min\{2,DL\sqrt{14}|t-u|\},\\
d_{\mathrm{fin}}(z(t),z(u))&\le4\sqrt{14}|t-u|.
\end{aligned}
\tag{104.4}
$$

以 $W_{14}$ 为因子的 $D$ 阶、长度 $L$ 任务同样至多为 $\min\{2,2DL\sqrt{14}|t-u|\}$；任意指定有限代数表示与多点任务按定理 103.2 传递。与此同时，实际忘却对象的简单项数在零点为十六、每个正参数处为一，特征循环则全程等于 (102.1) 的同一个循环，且不存在定理 102.2 排除的完整 Hecke 投影提升。这些现象由同一族同时实现。

**证明。** $R(K)$ 是十四维实正交表示，所以 (98.2) 的反向立即给 (104.3) 的块正性和秩恰十四；$F=I$ 是同一已知实标架。定理 92.2 给增强张量和关系。对单位 Frobenius 范数的 $S\in W_{14}$，

$$
\|USU^{\mathsf T}-VSV^{\mathsf T}\|_F
\le2\|U-V\|_{\mathrm{op}}\|S\|_F.
$$

因此 $\|R(U)-R(V)\|_{\mathrm{op}}\le2\|U-V\|_{\mathrm{op}}$。由 (101.4) 得
$\delta(z(t),z(u))\le\sqrt{14}|t-u|$，遂给第一个界；其余两个分别为 (103.2)、(103.5)。$W_{14}$ 是标准表示二次张量幂的固定等距子表示，故其 $D$ 次张量任务只需标准张量预算 $2D$。余下结论直接合并 (101.3)、(100.1)、(102.1)、(102.2)。

这里所有有限界以真实供应的路径矩阵、共同相位/实标架和指定预算为前提；定义 93.1 的参考制备服务或其他实际取得程序及其费用仍须另行提供。矩阵范数没有被转成自守 $D$-模范数，特征循环不变也不提供对象同构、简单项的连续标记或免费路径取得。这一综合结论区分有限任务的连续量、精确核的离散分层与实际对象的循环不变量；不作历史优先性主张。$\square$

## 追加锚（本行以下为增补区）

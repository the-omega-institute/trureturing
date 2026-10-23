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

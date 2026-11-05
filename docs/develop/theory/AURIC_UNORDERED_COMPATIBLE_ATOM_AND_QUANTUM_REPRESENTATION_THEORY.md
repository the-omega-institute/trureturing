# AURIC 无序相融原子与量子表示理论

## 1. 五端口关系、来源与完成纤维

**定义 1.1（带类型的无序原子）。** 令 $V=\{0,1,2,3,13\}$，每个端口有值域 $X_v$。原子是一个关系

$$
\mathcal A\subseteq\prod_{v\in V}X_v.
$$

若有约束族 $C_\lambda\subseteq\prod_{v\in S_\lambda}X_v$，则其解集为

$$
\mathcal A=\{x:x|_{S_\lambda}\in C_\lambda\text{ 对每个 }\lambda\}.
$$

$S_\lambda$ 是该约束的完整支撑。这里的“无序”指共同满足关系，不把端口的书写次序当作运算次序，也不取消端口标签和来源类型。

给定边界 $B\subseteq V$，记实际像 $Y_B=\pi_B(\mathcal A)$，并对 $b\in Y_B$ 定义非空完成纤维

$$
\mathcal A_b=\{x\in\mathcal A:\pi_B(x)=b\}.
$$

只在实际像上讨论由边界决定的目标；无解的边界不提供唯一性见证。

**命题 1.2（目标锁定与因子化）。** 对目标函数 $f:\mathcal A\to Z$，下列条件等价：同一边界的所有实际完成具有相同目标值；每个 $\mathcal A_b$ 上 $f$ 为常数；存在唯一 $\bar f:Y_B\to Z$ 使

$$
f=\bar f\circ\pi_B.
$$

边界决定完整内部赋值，当且仅当每个纤维至多含一点。约束求交的枚举次序以及对不同内部变量作存在量词消元的次序，不改变投影关系。

证明。若纤维上为常数，就把该常值定义为 $\bar f(b)$；非空性给存在性，实际像给唯一性。反向直接代入。对完整赋值取 $f$ 为恒等映射便得第二结论。约束求交由合取的交换律和结合律给出；对两个内部变量，$\exists x\exists y\,C$ 与 $\exists y\exists x\,C$ 同真，有限次迭代即得消元结论。这些等式比较的是同一个关系的投影。

**命题 1.3（完整支撑粘合）。** 设 $V=\bigcup_i V_i$，局部赋值 $x_i$ 在交叠上相同。若每个 $S_\lambda$ 完整包含在某个 $V_i$ 中，并且该 $x_i$ 满足此约束，则存在唯一全局赋值 $x$ 限制为各个 $x_i$，且 $x\in\mathcal A$。

证明。对端口 $v$，选含它的块，令 $x_v=(x_i)_v$；交叠一致使定义无歧义。每条约束都能在一个完整容纳其支撑的块上检查，因此全局满足。所有端口都已指定，故唯一。这是固定来源 [Static] §5 的支撑粘合在五端口上的应用。

完整支撑不能换成所有二元投影一致。例如在 $\{0,1\}^3$ 上要求 $x\oplus y\oplus z=0$。它的三个二元投影都是满关系；$(0,0,1)$ 的二元限制相融，却不满足三元约束。丢失的共同实现信息不能由已投影的二元读数补回。

**定义 1.4（有序来源语法）。** 自由有序树有叶 $\alpha,\beta$ 及二元构造 $\langle s,t\rangle$，两子槽有别。原生替换为

$$
\varrho(\alpha)=\beta,\qquad
\varrho(\beta)=\langle\beta,\alpha\rangle,\qquad
\varrho\langle s,t\rangle=\langle\varrho(s),\varrho(t)\rangle.
$$

这是 [Foundation] §§1–4 的来源类型。关系消元不改变语法中的左右槽，尤其不推出 $\langle s,t\rangle=\langle t,s\rangle$。把树、几何端点和数值关联起来，需要另给类型相容的读出映射。原生 $[2,5]$ 的数量为 $7$；不能仅因五端口几何而改读为别的代数运算。

## 2. 三个端点、正交原点与对角完成

**定理 2.1（三端点的完整非退化分类）。** 给定非共线 $p_1,p_2,p_3\in\mathbb R^d$，定义

$$
\alpha_i=\frac{\|p_i-p_j\|^2+\|p_i-p_k\|^2-\|p_j-p_k\|^2}{2}
\quad(\{i,j,k\}=\{1,2,3\}).
$$

存在 $o$ 使三个 $p_i-o$ 非零且两两正交，当且仅当三角形严格锐角且 $d\ge3$。此时令

$$
s=\sum_i\alpha_i^{-1},\qquad
w_i=\frac1{s\alpha_i},\qquad
H=\sum_iw_ip_i,\qquad E_0=\operatorname{span}(p_2-p_1,p_3-p_1).
$$

全部原点恰为

$$
o=H+u,\qquad u\in E_0^\perp,\qquad \|u\|^2=\frac1s.
$$

$H$ 是三角形在其仿射平面内的垂心。解集是半径 $1/\sqrt s$ 的 $S^{d-3}$；在三维恰有两个镜像解。

证明。若已有原点，写 $l_i=p_i-o$，则边长平方为 $\|l_i\|^2+\|l_j\|^2$，从而 $\alpha_i=\|l_i\|^2>0$。余弦公式说明这等价于三个角都锐。三个非零正交向量线性无关，故 $d\ge3$。

反向设 $\alpha_i>0$。由定义可得 $\|p_i-p_j\|^2=\alpha_i+\alpha_j$。置 $C=\sum_iw_i\|p_i-H\|^2$，加权方差恒等式给出

$$
\|p_i-H\|^2+C=\sum_jw_j\|p_i-p_j\|^2
=\alpha_i+\frac1s.
$$

对 $i$ 再加权求和，使用 $\sum_iw_i\alpha_i=3/s$，得到 $C=2/s$。所以

$$
\|p_i-H\|^2=\alpha_i-\frac1s,\qquad
\langle p_i-H,p_j-H\rangle=-\frac1s\quad(i\ne j).
$$

因此任意所述 $u$ 给出 $\langle p_i-o,p_j-o\rangle=0$，且腿长平方为 $\alpha_i$。还由
$\langle H-p_i,p_j-p_k\rangle=0$ 得到垂心性质。

最后，任一解的腿长平方已被强制为 $\alpha_i$。写 $o-H=t+u$，其中 $t\in E_0$、$u\perp E_0$。比较三个 $\|p_i-o\|^2=\alpha_i$ 与上述距离式并两两相减，得到 $\langle t,p_i-p_j\rangle=0$，故 $t=0$；任一距离式继而给 $\|u\|^2=1/s$。$E_0^\perp$ 的维数为 $d-2$，于是球面维数为 $d-3$。

**推论 2.2（手性及退化边界）。** 在已定向的 $\mathbb R^3$ 中，规定

$$
\operatorname{sgn}\det(p_1-o,p_3-o,p_2-o)=\chi\in\{+1,-1\}
$$

从两个原点中选出唯一一个。反射端点平面交换二解，并反转该行列式，故此选择确实唯一。这里的手性用固定有标号的三腿定义，不能用未标号图形替代。

直角三角形有一个 $\alpha_i=0$，因而没有三条非零正交腿；若允许零腿，唯一原点是直角顶点，其余两腿正交，任意更高维也不增加解。钝角三角形有负的 $\alpha_i$，即使允许零腿也无解。三个非零正交腿必产生非共线端点，故重合或共线端点不可能给本定理的非退化解。若放宽到零腿，三个不同共线端点仍不可能；恰有两个不同端点时，重复端点必须等于原点，另一端点给唯一非零腿；三个端点重合时原点也只能是该点。确因两个相等非零腿不可能正交，而两个非零正交腿与原点必不共线。少于三个指定端点一般不能固定三腿原点。二维锐角三角形也无解，不能把垂心误当作已满足正交条件的原点。

**定理 2.3（三平面对角闭合）。** 在三维选定原点后，置

$$
a=p_1-o,\qquad b=p_3-o,\qquad c=p_2-o.
$$

以下三个平面的共同点唯一：

$$
\langle c,q-o\rangle=0,\qquad
\langle a,q-p_1\rangle=0,\qquad
\langle b,q-p_3\rangle=0.
$$

它是 $q=o+a+b=p_1+p_3-o$。

证明。三条非零正交腿构成基。将 $q-o$ 写成 $ra+tb+uc$，三式分别给 $u=0,r=1,t=1$。反向代入即满足。在 $d>3$，这些式子仅固定三腿方向的分量，解为 $o+a+b+\operatorname{span}\{a,b,c\}^\perp$；若另要求 $q-o$ 属于三腿张成空间，才仍唯一。若另行允许零腿，设非零腿数为 $k$，三个方程在这些正交方向上仍独立，解集为 $o+a+b+\operatorname{span}\{a,b,c\}^{\perp}$、维数 $d-k$；它在三腿张成空间内仍只含 $o+a+b$，但零法向方程已不再定义一个平面。

因此严格锐角端点、三维手性和这三个平面条件给出整个五点几何原子的唯一完成。先证明原点再证明对角点只是证明顺序；最终对象是全部方程的共同唯一解，不规定端点的发生顺序。两个都过 $o$ 的平面，其交集必含 $o$，不可能单独交于另一点 $q$；三维中两个不同且不平行的平面交成直线。仅给两个点也只确定一条直线。两个平移侧面所携带的仿射位置条件不可省略。任意正腿长 $a_0,b_0,c_0$ 都可用 $o=0,p_1=a_0e_1,p_3=b_0e_2,p_2=c_0e_3,q=a_0e_1+b_0e_2$ 实现，故这不是空条件。

**命题 2.4（几何与语义分离）。** 唯一的 $q$ 不决定任意语义函数 $f(q)$。即使已给 $f(o),f(p_1),f(p_2),f(p_3)$，仍可在 $q$ 处独立赋任意值。若另外规定 $f$ 是取值于实向量空间的仿射映射，则

$$
f(q)=f(p_1)+f(p_3)-f(o).
$$

证明。五个点互异，在有限点集上可任意定义函数。仿射情形则把 $q=p_1+p_3-o$ 代入仿射组合即可。由几何锁定推到数值锁定，承重的是这一附加读出合同。

## 3. 共同距离的最小表示与三维乘积条件

**定理 3.1（五端口共同距离的 Gram 表示）。** 设集合 $X$ 含锚点 $x_*$，$d:X^2\to[0,\infty)$ 对称且 $d(x,x)=0$。定义

$$
G(x,y)=\frac{d(x,x_*)^2+d(y,x_*)^2-d(x,y)^2}{2}.
$$

存在实 Hilbert 空间及 $\phi(x_*)=0$、$\|\phi(x)-\phi(y)\|=d(x,y)$ 的表示，当且仅当每个有限 Gram 矩阵半正定。可选 $\phi(X)$ 的线性包稠密；这样的最小表示在保持全部标签的唯一等距同构下唯一。有限 $X$ 的最小实维数为 $\operatorname{rank}G$。

证明。表示存在时，极化恒等式给 $G(x,y)=\langle\phi(x),\phi(y)\rangle$，故半正定。反向在以符号 $[x]$ 为基的有限支撑实向量空间上设

$$
\Big\langle\sum_xa_x[x],\sum_yb_y[y]\Big\rangle=\sum_{x,y}a_xb_yG(x,y).
$$

半正定和二次多项式的判别式给 Cauchy–Schwarz；因此零范数向量与所有向量正交。商去零空间后是内积空间，完备化得到所需 Hilbert 空间，$\phi(x)=[x]$。$G(x_*,y)=0$，而 $G(x,x)+G(y,y)-2G(x,y)=d(x,y)^2$。任何另一个稠密表示在有限线性组合上由标签对应决定等距映射，再唯一延拓到完备化。有限情形商维数就是矩阵秩。

这是 [ThreeAxis] §2 所消费的经典锚定 Gram 商构造在共同端口读数上的应用。辅助锚点可为任意已知端点，不必是待反求的原点。若不同标签间距离为零，表示会识别它们；只有 $d$ 分离点时才是嵌入。构造使用实标量及完备化，不能从有限关系本身推出所有实系数的制备可取得性。稠密线性包也不等于每个线性组合都是物理允许的制备。

**定理 3.2（完整面积律与 Jacobi 的三维条件）。** 设有限维正定实内积空间 $K$ 的维数至少为二，双线性 $B:K\times K\to K$ 满足：$\langle B(u,v),w\rangle$ 是交替三线性式；对所有 $u,v$，

$$
\|B(u,v)\|^2=\|u\|^2\|v\|^2-\langle u,v\rangle^2;
$$

并对所有三元组满足 Jacobi 恒等式。则 $\dim K=3$；在固定定向下 $B$ 恰为叉积或其负号。

证明。令 $L_uv=B(u,v)$。交替性给 $L_u^\dagger=-L_u$；面积律极化给

$$
L_u^2v=\langle u,v\rangle u-\|u\|^2v.
$$

取单位正交 $u,v$，则 $c=B(u,v)$ 为与二者正交的单位向量，故维数至少三。假设还有单位 $z\perp u,v,c$。对上式关于 $u,v$ 极化，得

$$
(L_uL_v+L_vL_u)z=0.
$$

Jacobi 给 $[L_u,L_v]=L_{B(u,v)}=L_c$，所以 $L_cz=2L_uL_vz$。左边范数为一。右边中 $\|L_vz\|=1$，且

$$
\langle u,L_vz\rangle=\langle B(u,v),z\rangle=0,
$$

故 $\|L_uL_vz\|=1$，右边范数为二，矛盾。因此维数为三。三维交替三形式是一维空间，面积律把相对于定向体积形式的系数限制为 $\pm1$，得到结论。标准三维叉积满足这些条件，故条件也可实现。

这里消费 [ThreeAxis] §5 的全域条件论证及其 Darpö、Baez 向量积文献归属。若把 $B$ 忠实表示为某结合代数的交换子，展开结合律会使 Jacobi 的十二项成对抵消；但结合性不会自动提供上述面积律。有限五点上的几次数值核对不能代替“所有 $u,v,w$”的量词。没有 Jacobi 的面积型向量积不能用本结论排除其他维数。

## 4. 正交复合、中心复单位与三种载体

**定义 4.1（选定的 Clifford 复合）。** 对正定三维 $K$，取实张量代数按 $x\otimes x=\|x\|^2 1$ 商掉的含幺结合代数 $\mathrm{Cl}_{3,0}$。其乘法满足

$$
xy+yx=2\langle x,y\rangle1.
$$

这是额外的复合规则；它与第 1 节的合取、树替换以及第 2 节的向量相加各有不同类型。以下 Clifford、Pauli 和旋子公式消费 Lachièze-Rey [Clifford] §§1.6–1.8、3.3 的标准构造，用于三轴原子的具体表示。

**命题 4.2（中心复单位与忠实 Pauli 表示）。** 取正向单位正交基 $(u,v,n)$，令 $\iota=uvn$。则 $\iota$ 与全代数对易且 $\iota^2=-1$。实代数同构

$$
\mathrm{Cl}_{3,0}\cong M_2(\mathbb C)
$$

把 $(u,v,n)$ 送到

$$
\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
\sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

中心是 $\mathbb R1\oplus\mathbb R\iota\cong\mathbb C$；固定向量并反转乘积次序的 reversion 对应矩阵伴随。

证明。交换两个不同正交基向量变号，各基向量平方为一。把基向量移过另外两项不变号，故 $\iota$ 中心；平方中共三次交换，得 $-1$。任一单词可化为

$$
1,u,v,n,uv,vn,nu,uvn
$$

的实线性组合。Pauli 矩阵满足同样关系，其八个像是 $I,\sigma_x,\sigma_y,\sigma_z,i\sigma_z,i\sigma_x,i\sigma_y,iI$，实线性无关且张成 $M_2(\mathbb C)$，故没有隐藏核。与三个 Pauli 矩阵都对易的矩阵只能为复标量，得中心。生成向量的像为 Hermitian，反转乘法恰是伴随。换成反向三基会把 $\iota$ 换成 $-\iota$；这涉及手性，未指定时间演化。

**命题 4.3（法向量、面积与平面复结构）。** 在 $P=\operatorname{span}(u,v)$ 上置 $B_0=uv=\iota n$。则 $B_0^2=-1$，

$$
J_nx=xB_0=n\times x,
\qquad J_n(au+bv)=av-bu,
\qquad J_n^2=-I_P.
$$

$J_n$ 保持内积。因此 $P$ 成为复一维空间。给定单位法向 $n$ 及空间定向，$P=n^\perp$ 的有向单位面积元 $\iota n$ 和 $J_n$ 都唯一确定，不依赖其中另选哪一组正向正交单位基。对一般非零正交 $a,b$，

$$
ab=\iota(a\times b),\qquad (ab)^2=-\|a\|^2\|b\|^2.
$$

故仅有法线方向还不足以给未归一化二向量的面积系数。

证明。直接用 $u^2=v^2=1$、$uv=-vu$ 算得 $uB_0=v,vB_0=-u$，再作线性延拓。面积公式对 $a=\|a\|u,b=\|b\|v$ 成立；换正向基不改变两边的双线性形式。

**命题 4.4（二向量不是对角点）。** 同一平面中的旋转基

$$
u_t=\cos t\,u+\sin t\,v,\qquad
v_t=-\sin t\,u+\cos t\,v
$$

满足 $u_tv_t=uv$，但 $u_t+v_t$ 随 $t$ 改变。

证明。展开乘积，标量项抵消，二向量系数为 $\cos^2t+\sin^2t$。而 $t=0$ 的和为 $u+v$，$t=\pi/2$ 的和为 $v-u$。故定向面积数据不能替代第 2 节的平移侧面和对角点。

**命题 4.5（旋量、事件与原生模式）。** $p=(1+n)/2$ 是幂等元，左理想 $\mathrm{Cl}_{3,0}p$ 在上述表示下为 $\mathbb C^2$。这与平面的 $\mathbb C^1$、五个原生模式所张成的 $\mathbb C^5$ 是三个不同载体。

证明。$p$ 映到 $\operatorname{diag}(1,0)$；$M_2(\mathbb C)p$ 的第二列为零，第一列任意，故为二维复模。几何方向 $x\perp y$ 意味着对应 Pauli 算子反对易，却不意味着其正本征事件互斥。事实上对单位方向 $x,y$，置 $P_x=(I+x\cdot\sigma)/2$，则

$$
\operatorname{tr}(P_xP_y)=\frac{1+x\cdot y}{2}.
$$

正交轴给 $1/2$，而互斥投影要求乘积为零。几何正交、投影事件互斥和算子反对易不能互换。

**命题 4.6（旋子与半角）。**

$$
R_\theta=\cos(\theta/2)-B_0\sin(\theta/2)
$$

满足 $R_\theta^\dagger R_\theta=1$，其共轭作用把 $u$ 送到 $\cos\theta\,u+\sin\theta\,v$，把 $v$ 送到 $-\sin\theta\,u+\cos\theta\,v$，并固定 $n$。$R_{2\pi}=-1$，但其向量共轭作用为恒等。

证明。$B_0^\dagger=-B_0$、$B_0^2=-1$ 给归一化；把 $(c-B_0s)u(c+B_0s)$ 展开为 $(c^2-s^2)u+2cs\,v$，其余同算。此处参数角和连续旋转控制是另给的操作能力；一个有限正交三轴自身不供应全部 $\theta$。

## 5. 定向拼接、相位回路与奇数维障碍

**定理 5.1（平面复结构的拼接判据）。** 给非空连通图，每个顶点有定向欧氏二维空间及正向四分之一转 $J_v$。每条定向边有正交运输 $T_e$，反边为其逆，记 $\varepsilon_e=\det T_e\in\{\pm1\}$。存在符号 $s_v\in\{\pm1\}$ 使

$$
T_e(s_vJ_v)=(s_wJ_w)T_e\quad(e:v\to w)
$$

当且仅当每条闭行走的 $\varepsilon_e$ 乘积为 $+1$。条件成立时恰有两个全局符号选择。

证明。二维正交映射满足 $T_eJ_v=\varepsilon_eJ_wT_e$，所以方程等价于 $s_w=\varepsilon_es_v$。沿闭行走相乘给必要性。反向选根符号，沿任意路径传播；两路径差为闭行走，所给条件保证无歧义。连通性表明只剩根处两个选择。若图不连通，则每个连通分支各有一个独立符号选择。

**命题 5.2（复相容不等于零回路相位）。** 在有限连通图上，已复线性的单位运输仍可有非平凡 $U(1)$ holonomy。顶点相位规范可使任一生成树的边相位全为一；剩余独立边数为 $|E|-|V|+1$，其基本回路相位不由定向判据确定。

证明。沿树从根逐个选顶点规范，即消去所有树边相位。每条非树边闭合一个基本回路；阿贝尔相位在回路上的乘积不受顶点规范改变。反向可任意指定这些边相位，故独立自由度数如上。

[Foundation] 的金字塔骨架有五顶点、八棱，故图的回路秩为四；其五个面若作为填充二维胞腔，并另要求各面平坦，边界球面的单连通性才迫使全部回路 holonomy 平凡。原生耦合边 $01,02,03,1\!-!13,3\!-!13$ 则是五顶点五边的另一个图，回路秩为一。按实际记录组成的历史 DAG 又是第三种图。骨架、耦合图与历史图不能共用未经声明的“回路”条件；有向无环也不自动排除底层无向图的回路。

**命题 5.3（奇数维载体的两种障碍）。** 奇数维实空间没有 $J^2=-I$ 的线性复结构。奇数维复空间没有两个可逆且反对易的算子。因此 $\mathbb C^5$ 上不存在平方均为 $I_5$ 的完整 Pauli 三元组。

证明。实维数 $d$ 为奇数时，$\det(J)^2=\det(-I)=(-1)^d=-1$ 矛盾。复维数 $d$ 为奇数且 $AB=-BA$ 时，行列式给 $\det(AB)=-\det(BA)$；可逆性又使两者同为非零数，矛盾。Pauli 算子的平方为单位，故可逆。

给五个标签各加一个 $\mathbb C^2$ 旋量纤维可形成 $\mathbb C^5\otimes\mathbb C^2$，但这是新增载体。五个标签也不可能本身就是实维数八的完整 Clifford 代数。在三维载体上，$\sigma_i\oplus0$ 平方为 $P_+=I_2\oplus0$，不是 $I_3$；它们不可逆，所以 $M_2(\mathbb C)\oplus\mathbb C$ 的实现不违反上述障碍。

## 6. 幅度贡献与所有效果上的预测赋值

**定理 6.1（非负正交可加权重的自动平方律）。** 在维数至少二的实欧氏空间上，设 $Q$ 取非负实值，$Q(0)=0$，在旋转群 $SO(d)$ 下不变，并满足

$$
x\perp y\ \Longrightarrow\ Q(x+y)=Q(x)+Q(y).
$$

则存在 $c\ge0$ 使 $Q(x)=c\|x\|^2$。若任一单位向量的权重校准为一，则 $c=1$；不需要另设连续性。

证明。旋转群在每个球面上传递，故存在 $f:[0,\infty)\to[0,\infty)$ 使 $Q(x)=f(\|x\|^2)$。对任意 $a,b\ge0$，可取正交向量范数平方分别为 $a,b$，因而 $f(a+b)=f(a)+f(b)$。非负性推出单调性：$b\ge a$ 时 $f(b)-f(a)=f(b-a)\ge0$。加性给 $f(r)=rf(1)$ 对非负有理 $r$ 成立；以有理数上下夹任一实数并用单调性，得到 $f(t)=tf(1)$。

这里只要旋转不变而不要正交可加，$Q(x)=\|x\|^p$ 对任意 $p>0$ 都可行。平方公式也给自动连续性；但实欧氏标量已经是前提，不能由这份连续性倒推实数域。这里相加的是正交幅度贡献；第 4 节的正交 Bloch 轴所对应正投影并不互斥，不能把两种“正交可加”混为一谈。

**定义 6.2（完整效果域的相融赋值）。** 对已供应的有限维复载体 $\mathbb C^d$，定义

$$
\operatorname{Eff}_d=\{E\in M_d(\mathbb C):0\le E\le I\}.
$$

相融赋值是单一函数 $\mu:\operatorname{Eff}_d\to[0,\infty)$，满足 $\mu(I)=1$，以及当 $E+F\le I$ 时

$$
\mu(E+F)=\mu(E)+\mu(F).
$$

“单一”要求同一效果在不同细分、不同 POVM 中取同一值。每个有限 POVM 的效果和为 $I$，于是其赋值之和为一。这是完整效果域的合同，不只是有限菜单或每次测量各选一个状态。

**定理 6.3（五端口预测接口的有限维 Born 表示）。** 对每个有限 $d\ge1$，定义 6.2 的赋值当且仅当存在唯一密度矩阵 $\rho\ge0$、$\operatorname{tr}\rho=1$ 使

$$
\mu(E)=\operatorname{tr}(\rho E).
$$

赋值自动满足

$$
|\mu(E)-\mu(F)|\le\|E-F\|_{\mathrm{op}}.
$$

证明。先由 $0+0=0$ 得 $\mu(0)=0$。$E\le F\le I$ 时 $F-E$ 是效果，故 $\mu(E)\le\mu(F)\le1$。把效果分成 $n$ 个相同部分，得到有理齐次性；再用 $aE\le tE\le bE$ 的有理上下夹逼，得到 $\mu(tE)=t\mu(E)$ 对 $0\le t\le1$ 成立。这同时给所有缩放后仍为效果的实数齐次性。

对任意正矩阵 $A$，选 $r\ge\|A\|_{\mathrm{op}}$、$r>0$，置 $\ell_+(A)=r\mu(A/r)$。用前述齐次性比较两个尺度，表明定义无关。对 $A,B\ge0$，选共同尺度 $r\ge\|A+B\|$，效果可加性给

$$
\ell_+(A+B)=\ell_+(A)+\ell_+(B).
$$

它也为非负实齐次。每个 Hermitian 矩阵可写为正矩阵之差，定义 $\ell(A-B)=\ell_+(A)-\ell_+(B)$。若 $A-B=C-D$，则 $A+D=C+B$，正锥加性使两种定义相同。因此 $\ell$ 是 Hermitian 空间上的实线性泛函。

有限维迹配对非退化，存在唯一 Hermitian $\rho$ 表示此泛函。对任意向量 $x$，

$$
\langle x,\rho x\rangle=\ell(|x\rangle\langle x|)\ge0,
\qquad \operatorname{tr}\rho=\ell(I)=1.
$$

这给正性、归一性和唯一性。反向由迹的线性和正性立即满足赋值公理。最后置 $\delta=\|E-F\|_{\mathrm{op}}$，有 $-\delta I\le E-F\le\delta I$。对正归一线性泛函应用此序关系便得 Lipschitz 界。它所给连续性是结论，不是前提。

这是 Busch [Busch] 的效果版 Gleason 论证在本预测接口中的有限维应用；POVM 与二维载体的相应文献归属见 [Caves]。投影域上的传统结论不能不加说明地替代完整效果域。效果、制备及概率读出的物理校准仍由合同供应，数学表示不替它们建立经验同一性。

**推论 6.4（三轴预测与半角）。** 在 Pauli 载体上，每个状态唯一写成

$$
\rho=\frac{I+r\cdot\sigma}{2},\qquad r\in\mathbb R^3,\quad\|r\|\le1.
$$

纯态为 $\|r\|=1$。单位纯态方向 $m$ 对效果 $P_n=(I+n\cdot\sigma)/2$ 的赋值为

$$
\mu(P_n)=\frac{1+m\cdot n}{2}=\cos^2(\theta/2),
\qquad m\cdot n=\cos\theta.
$$

证明。Hermitian $2\times2$ 矩阵在 $I,\sigma_x,\sigma_y,\sigma_z$ 中实展开，迹一固定 $I$ 系数。$(r\cdot\sigma)^2=\|r\|^2I$，故特征值是 $(1\pm\|r\|)/2$；正性和秩一条件如上。迹乘积给概率公式。对任意载体的纯态 $|\psi\rangle$ 及正交投影 $P$，同一表示给 $\mu(P)=\langle\psi,P\psi\rangle=\|P\psi\|^2$。

**命题 6.5（所有局部三轴可拟合的反模型）。** 在二维复载体的秩一投影上定义

$$
\nu(P_n)=\frac{1+n_z^3}{2},\qquad \nu(0)=0,\qquad\nu(I)=1.
$$

它连续、非负，且 $\nu(P_n)+\nu(P_{-n})=1$。对每个几何正交三轴 $(n_1,n_2,n_3)$，存在一个依赖于该三轴的 Bloch 状态拟合这三个值；却不存在同一个密度矩阵拟合全部方向，也没有满足定义 6.2 的效果扩张。

证明。设局部 $r=\sum_i(n_{i,z})^3n_i$。由于 $\sum_i(n_{i,z})^2=1$，

$$
\|r\|^2=\sum_i(n_{i,z})^6\le1,
$$

且 $r\cdot n_i=(n_{i,z})^3$，所以局部可拟合。若存在全局 $r$，三个坐标轴读数迫使 $r=(0,0,1)$。但 $n_z=1/2$ 时，本函数给 $9/16$，该 Bloch 状态给 $3/4$，矛盾。定理 6.3 因而排除效果扩张。更一般 $\nu_\lambda(P_n)=(1+(\lambda\cdot n)^3)/2$ 对单位 $\lambda$ 给同类反模型，且同时旋转 $\lambda,n$ 保持赋值；这种联合协变性也不能替代全效果相融性。

## 7. 制备更新、合法路径与门切分

**命题 7.1（仿射态更新的唯一正保迹扩张）。** 设 $T:\mathcal D_d\to\mathcal D_e$ 对全部密度矩阵定义，并保持任意实混合：

$$
T(t\rho+(1-t)\sigma)=tT(\rho)+(1-t)T(\sigma)
\quad(0\le t\le1).
$$

则它唯一扩张为 Hermitian 矩阵空间上的正保迹实线性映射，再唯一复线性扩张为 $M_d(\mathbb C)\to M_e(\mathbb C)$。

证明。对非零 $A\ge0$ 定义 $\widetilde T(A)=\operatorname{tr}(A)T(A/\operatorname{tr}A)$，在零处取零。仿射性对权重 $\operatorname{tr}A/(\operatorname{tr}A+\operatorname{tr}B)$ 给正锥加性，实齐次性直接成立。按正矩阵之差扩张，良定义性同定理 6.3；所得映射正且保迹。密度矩阵张成 Hermitian 空间，故唯一。每个复矩阵唯一写成 $A+iB$、$A,B$ Hermitian，给唯一复扩张。

若还要求此同一局部映射与任意未触及参考系统并置时均正，条件正是完全正性。只有单系统的正性并不够。例如转置 $X\mapsto X^{\mathsf T}$ 正且保迹；对纠缠态 $|\Omega\rangle=(|00\rangle+|11\rangle)/\sqrt2$ 作一侧转置，得到交换算子的一半，在反对称向量上有特征值 $-1/2$。即便同时转置任意多份仍为总转置而正，也不能替代“任意参考且只作用本地”的范围。

**定理 7.2（合法菱形与固定端点路径独立）。** 设有限偏序事件集的全部合法配置是其下闭子集。每次合法添加一个事件都有类型相容的映射。则所有同起终点合法路径的复合相同，当且仅当每个合法添加两个不可比事件的菱形可交换。

证明。路径独立直接用于长度二路径给菱形交换。反向，固定配置 $C\subseteq D$，路径恰是 $D\setminus C$ 的线性扩张。任意两个线性扩张可以通过交换相邻不可比元素连接：把目标扩张的首个元素向前移，它前面的元素既不能是其前驱，也不能是其后继，故均不可比；再对余下部分归纳。下闭合法性保证每次交换的两条路径和整个菱形都合法。逐次用交换菱形就得复合相等。这消费 [Static] §3 的合法路径结论。若合法配置只给一个非遗传的子族，上述中间菱形可能被删去，不能直接使用本结论。

**命题 7.3（固定张量网络与串行门次序）。** 固定有限张量网络的内部指标收缩次序不改变值；这不推出同一载体上的两个串行门可交换。

证明。固定网络每个输出分量是有限多个系数乘积的有限和，交换求和次序、结合乘法不会改值。交换串行门则改变连接到输入输出槽的因子顺序，已经是另一个网络。例如 $P_z=|0\rangle\langle0|$、$P_x=|+\rangle\langle+|$，$|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$，对输入 $|0\rangle$ 有

$$
\|P_xP_z|0\rangle\|^2=\frac12,
\qquad
\|P_zP_x|0\rangle\|^2=\frac14.
$$

因此无序关系求解、固定网络收缩与可执行门交换分别需要自己的条件。

**命题 7.4（静态相融不决定干预）。** 两个结构模型可以有相同全部观测联合分布而有不同干预后果。

证明。取均匀位 $U$。模型一为 $X=U,Y=X$，模型二为 $Y=U,X=Y$。两者观测分布均集中在 $(0,0),(1,1)$，各占一半。用替换结构方程的干预 $\operatorname{do}(X=c)$，模型一给 $Y=c$，模型二仍给 $Y=U$。观测关系没有携带被替换的因果生成规则。

**定义 7.5（带切分的关系张量门）。** 只有在指定输入、输出载体及内积后，张量

$$
\tau\in H_{\mathrm{out}}\otimes H_{\mathrm{in}}^*
$$

才对应线性映射 $T:H_{\mathrm{in}}\to H_{\mathrm{out}}$。它为等距当且仅当 $T^\dagger T=I_{\mathrm{in}}$；为酉当且仅当再有 $TT^\dagger=I_{\mathrm{out}}$。

这些恒等式分别等价于内积保持以及同时满射。复制张量 $\sum_i|i i i\rangle$ 在一个输入、两个输出的切分上给 $|i\rangle\mapsto|ii\rangle$，是等距；当单腿维数大于一时维数不同，所以不是酉门。改切分会改变映射类型。五点几何、边的存在或“边界”一词不指定系数、内积或切分，不能单独选出一个更新门；同一几何容许多种更新。

## 8. 五维观察代数与穷尽锐事件

**定理 8.1（五维分块代数的两种类型）。** 在明确给定有限维复 $C^*$ 分块合同

$$
\mathfrak B\cong\bigoplus_jM_{n_j}(\mathbb C),\qquad
\dim_{\mathbb C}\mathfrak B=5
$$

时，$\mathfrak B$ 只有 $\mathbb C^5$ 与 $M_2(\mathbb C)\oplus\mathbb C$ 两种类型。

证明。复维数为 $\sum_jn_j^2=5$。若全为一则五块；若有二则余下一块一；三及更大不可能。这是有限分块结构在五坐标接口中的直接计数，不把五个原生标签先验量子化。

非交换类型用通常块迹的态恰为

$$
\rho_{t,v}=\frac{tI_2+v\cdot\sigma}{2}\oplus(1-t),
\qquad 0\le t\le1,\quad v\in\mathbb R^3,\quad\|v\|\le t.
$$

确因二阶块的特征值为 $(t\pm\|v\|)/2$，一阶块为 $1-t$。该代数的 Hermitian 空间实维数五，归一态空间仿射维数四，是三维 Bloch 球与一个经典顶点的凸包。这里“五维”指代数复维数，也等于 Hermitian 实维数；不是载体维数，也不是五个两两排斥的量子结果数。

**命题 8.2（五个穷尽锐事件强制交换）。** 若复维数五的含幺结合代数含五个非零两两正交幂等元 $p_i$，且 $\sum_ip_i=1$，则它同构于 $\mathbb C^5$。

证明。若 $\sum_i a_ip_i=0$，乘 $p_j$ 得 $a_jp_j=0$，故每个系数为零。五个幂等元构成全代数的基，并且 $p_ip_j=\delta_{ij}p_i$，所以乘法是逐坐标乘法。

五结果 PVM 可以作用于 $\mathbb C^5$，其完整算子代数却是 $M_5(\mathbb C)$、复维数二十五。非交换五维代数的三个方向 $\sigma_i\oplus0$ 只在二阶块上实现 Pauli 关系。原生五函数代数、五标签载体与此混合块代数之间的对应，必须由明确的观察映射供应。[Foundation] §§3–4 与 [Static] §§6–8 的原生菜单不自动含后文另给的编码和解码操作。

## 9. 实际测量来源、共同坐标与相干校正圆盘

**定义 9.1（实际来源和三个不同空间）。** 本节固定 [Retained] §§1、5、8–12 的来源。物理输出空间为 $H=\mathbb C^5$，基为 $e_0,\ldots,e_4$。令

$$
u_H=\frac{e_0+e_3}{\sqrt2},\qquad
v_H=\frac{e_1+e_4}{\sqrt2},\qquad z_H=e_2,
\qquad B(x_0,x_1,x_2)=x_0u_H+x_1v_H+x_2z_H.
$$

于是 $B:\mathbb C^3\to H$ 是等距，像为 $R_H$。这里 $u_H,v_H,z_H$ 不是第 4 节的三维实几何轴。新环境为 $\mathbb C^2$，基 $f_0,f_1$；实际相互作用的等距 $\mathscr V:H\to H\otimes\mathbb C^2$ 为

$$
\begin{aligned}
\mathscr Ve_0&=u_H\otimes f_0,&\mathscr Ve_1&=u_H\otimes f_1,\\
\mathscr Ve_2&=v_H\otimes(f_0+f_1)/\sqrt2,\\
\mathscr Ve_3&=z_H\otimes f_1,&\mathscr Ve_4&=z_H\otimes f_0.
\end{aligned}
$$

五个像两两正交且范数一。对固定已校准实角 $\theta$，在环境基

$$
g_0=\cos\theta f_0-i\sin\theta f_1,\qquad
g_1=-i\sin\theta f_0+\cos\theta f_1
$$

中作实际测量，记录 $j\in\{0,1\}$ 后丢弃环境。取环境内积所得两个实际物理 Kraus 矩阵为

$$
\begin{aligned}
K_0&=|u_H\rangle\langle e_0|+2^{-1/2}|v_H\rangle\langle e_2|+|z_H\rangle\langle e_4|,\\
K_1&=|u_H\rangle\langle e_1|+2^{-1/2}|v_H\rangle\langle e_2|+|z_H\rangle\langle e_3|,\\
A_0&=\cos\theta K_0+i\sin\theta K_1,
\qquad A_1=i\sin\theta K_0+\cos\theta K_1.
\end{aligned}
$$

在 qutrit 的原始坐标中，$U_0$ 交换第二、第三坐标，$W$ 交换第一、第二坐标，且

$$
A_jB=\frac1{\sqrt2}BV_j,\qquad
V_0=U_0e^{i\theta W},\qquad V_1=V_0W.
$$

这条限制恒等式只在 $R_H$ 上使用，不能替代 $A_j$ 在全部 $H$ 上的作用。

**定义 9.2（共同任务基）。** 在原始 qutrit 坐标中置

$$
\xi=(1,1,1)/\sqrt3,\qquad e=(1,1,-2)/\sqrt6,\qquad f=(1,-1,0)/\sqrt2,
\qquad v=(\xi+e)/\sqrt2,\quad r=(\xi-e)/\sqrt2.
$$

$e,f$ 是此处 qutrit 向量，不是 $H$ 的基 $e_i$ 或环境的基 $f_j$。在 $(\xi,e,f)$ 基中，

$$
U_0=1\oplus\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},
\qquad W=\operatorname{diag}(1,1,-1).
$$

基变换矩阵和在后文统一使用的 $(v,r,f)$ 基中的实际 $U_0$ 为

$$
S=\begin{pmatrix}1/\sqrt2&1/\sqrt2&0\\1/\sqrt2&-1/\sqrt2&0\\0&0&1\end{pmatrix},
\qquad
U_0=S^{\mathsf T}U_0|_{(\xi,e,f)}S
=\frac14\begin{pmatrix}1&3&\sqrt6\\3&1&-\sqrt6\\\sqrt6&-\sqrt6&2\end{pmatrix}.
$$

$U_0$ 自伴且正交，$W$ 在此基仍为 $\operatorname{diag}(1,1,-1)$。这样，来源置换、任务效果和下面的分块都已处在同一坐标中。

**命题 9.3（实际无标签后继）。** qutrit 实际分支与擦去新标签的通道为

$$
\mathcal J_j(X)=\frac12V_jXV_j^\dagger,\qquad
\mathcal F(X)=\sum_j\mathcal J_j(X)
=U_0\Delta(X)U_0^\dagger,
$$

其中

$$
P_+=\operatorname{diag}(1,1,0),\quad P_-=\operatorname{diag}(0,0,1),\qquad
\Delta(X)=P_+XP_++P_-XP_-.
$$

实际标签在每个 qutrit 输入上各有概率 $1/2$；连同未触及参考系统，每个标签的参考边缘也是原参考边缘的一半。若即时任务是 $E=|v\rangle\langle v|$，则其一次实际无标签后继效果为

$$
E=\begin{pmatrix}1&0&0\\0&0&0\\0&0&0\end{pmatrix},\qquad
G=\mathcal F^\dagger(E)
=\frac1{16}\begin{pmatrix}1&3&0\\3&9&0\\0&0&6\end{pmatrix}.
$$

证明。$V_j$ 酉，故分支的迹为输入迹的一半。$V_1=V_0W$，平均 $X$ 与 $WXW$ 给 $\Delta(X)$；$e^{i\theta W}$ 在两块上为标量，因此在 $\Delta(X)$ 上共轭为恒等，得所述实际 $\mathcal F$，与 $\theta$ 无关。对偶为 $\Delta\operatorname{Ad}_{U_0^\dagger}$；把共同基中的 $U_0$ 第一行外积并去跨块项即得 $G$。限制的 Kraus 恒等式、酉性及部分迹也直接给参考版本。

**定义 9.4（两任务的共同校正合同）。** 固定一个 CPTP 映射 $\mathcal T:M_3\to M_3$，在输入未知且任务选择尚未给出时先作用。输出仍是同一个 qutrit。要求对每个密度矩阵 $\rho$ 同时有

$$
\operatorname{tr}(E\mathcal T(\rho))=\operatorname{tr}(E\rho),\qquad
\operatorname{tr}(G\mathcal T(\rho))=\operatorname{tr}(G\rho).
$$

第二式是实际 $\mathcal F$ 之后测 $E$ 的二元概率要求，不是任意指定的后继，也不是一次输入上的层析。

**定理 9.5（两任务的全部校正族）。** 定义 9.4 的通道恰为唯一参数 $|z|\le1$ 的

$$
\mathcal D_z(X)=P_+XP_++P_-XP_-+zP_+XP_-+\bar zP_-XP_+.
$$

其对偶固定空间精确为

$$
\operatorname{Fix}(\mathcal D_z^\dagger)=
\begin{cases}
\mathfrak A=P_+M_3P_+\oplus\mathbb CP_-\cong M_2(\mathbb C)\oplus\mathbb C,&z\ne1,\\
M_3(\mathbb C),&z=1.
\end{cases}
$$

而且 $\mathcal F\mathcal D_z=\mathcal F$。

证明。令 $\Phi=\mathcal T^\dagger$。所有输入概率相等，借 Hermitian 迹配对的非退化性，等价于 $\Phi(E)=E,\Phi(G)=G$。对实际任意 Kraus 家族 $\mathcal T(X)=\sum_\ell L_\ell XL_\ell^\dagger$，固定投影 $E$ 迫使每项与 $E$ 对易：若 $x\in\ker E$，则

$$
0=\langle x,\Phi(E)x\rangle=\sum_\ell\|EL_\ell x\|^2;
$$

若 $x\in\operatorname{ran}E$，对固定的 $I-E$ 同理。于是每项保持 $E$ 的像和核，且

$$
\Phi(EX)=E\Phi(X),\qquad \Phi(XE)=\Phi(X)E.
$$

置 $R=|r\rangle\langle r|,N=|f\rangle\langle f|$。$I-E=R+N$ 和 $(I-E)G(I-E)=9R/16+3N/8$ 均固定，两个系数不同，解线性方程得 $R,N$ 分别固定。$EG(I-E)=3|v\rangle\langle r|/16$ 也固定，共轭项亦然。因此 $\Phi$ 固定 $\mathfrak A$ 的所有矩阵单位及其中每个投影。对每个此类投影用同一零范数论证，所有 $L_\ell$ 都在 $\mathfrak A$ 的交换子代数中，即

$$
L_\ell=\alpha_\ell P_++\beta_\ell P_-,\qquad
\sum_\ell|\alpha_\ell|^2=\sum_\ell|\beta_\ell|^2=1.
$$

代回得 $z=\sum_\ell\alpha_\ell\bar\beta_\ell$，Cauchy–Schwarz 给 $|z|\le1$；在一个非零跨块矩阵单位上求值即给唯一性。反向取

$$
K_1=P_++\bar zP_-,\qquad K_2=\sqrt{1-|z|^2}P_-,
$$

有 $\sum K_i^\dagger K_i=I$，其 Kraus 和恰是 $\mathcal D_z$，并保持两对角块。对偶在跨块上分别乘 $\bar z,z$，故除 $z=1$ 外没有跨块固定元，得到精确固定空间。最后 $\Delta\mathcal D_z=\Delta$，给出实际后继恒等式。

这是 [Retained] 定理 8.2 的指定矩阵应用及其证明。Heisenberg 观察代数纠错的背景见 [BKK]；本圆盘由实际 $G$ 的系数强制，不能作为任意两项观察的通则。通道等式可张量任意未触及参考；它也不声称保持一次即时破坏性测量之后的全部状态，或保持所有直接跨块读出。

## 10. 守恒代数的完成纤维与精确目标区间

**定义 10.1（比两个概率更强的边界资料）。** 现在声明观察合同为已知状态在整个 $\mathfrak A$ 上的限制。它等价于给定

$$
A\in M_2(\mathbb C),\quad A\ge0,\qquad b\ge0,\qquad \operatorname{tr}A+b=1.
$$

此处 $A$ 是 qutrit 的二阶对角块，不是物理 Kraus 矩阵 $A_j$。未知量是跨块列 $c\in\mathbb C^2$。仅知两个数 $\operatorname{tr}(E\rho),\operatorname{tr}(G\rho)$ 不等价于此合同。

**定理 10.2（全部状态完成及尖锐目标范围）。** 定义 10.1 的非空完成纤维恰为

$$
\rho_c=\begin{pmatrix}A&c\\c^\dagger&b\end{pmatrix},\qquad
c\in\operatorname{ran}A,\quad c^\dagger A^+c\le b,
$$

其中 $A^+$ 为 Moore–Penrose 逆。等价地，$c=\sqrt b\,A^{1/2}k$、$\|k\|\le1$。对任意 Hermitian 目标

$$
H_0=\begin{pmatrix}H_+&h\\h^\dagger&h_-\end{pmatrix},\qquad
m=\operatorname{tr}(AH_+)+bh_-,
$$

其在此纤维上的全部期望值恰为闭区间

$$
\left[m-2\sqrt{b\,h^\dagger Ah},\quad m+2\sqrt{b\,h^\dagger Ah}\right].
$$

证明。若 $\rho_c\ge0$，对 $x\in\ker A$ 与标量 $t$ 考察二次型 $(x,t)^\dagger\rho_c(x,t)$，可令 $t$ 的相位和大小使线性项为负；因此必须 $x^\dagger c=0$，即 $c\in\operatorname{ran}A$。在 $A$ 的支撑上配方得

$$
\begin{pmatrix}x\\t\end{pmatrix}^{\dagger}\rho_c
\begin{pmatrix}x\\t\end{pmatrix}
=(x+tA^+c)^\dagger A(x+tA^+c)
+|t|^2(b-c^\dagger A^+c).
$$

故正性当且仅当所述条件。用 $A$ 的非零谱值逐项开平方，条件等价于 $c=\sqrt b A^{1/2}k$、$\|k\|\le1$；$b=0$ 时强制 $c=0$，该写法仍有效。

目标为 $m+2\operatorname{Re}(h^\dagger c)$。Cauchy–Schwarz 给偏差不超过 $2\sqrt b\|A^{1/2}h\|$。若该范数非零，取 $k=\pm A^{1/2}h/\|A^{1/2}h\|$ 达到两端；为零则所有偏差为零。允许球和仿射目标均凸，故两端之间每个值也达到。证明覆盖 $A$ 奇异、$A=0$ 及 $b=0$，不需要严格正定假设。

**推论 10.3（纤维锁定与校正轨道的区别）。** 某个纤维锁定 $H_0$ 当且仅当 $b\,h^\dagger Ah=0$。完成纤维本身为单点当且仅当 $b=0$ 或 $A=0$。在所有可能纤维上都锁定的 Hermitian 目标恰是 $h=0$，即 $H_0\in\mathfrak A$。

证明。前两项由定理直接得。若 $b>0$ 且 $A\ne0$，支撑中存在非零可行 $c$ 及其负值，故非单点。若 $h\ne0$，选 $A$ 在 $h$ 方向有正权、并取 $0<b<1$，则目标区间宽度非零，故不可能全纤维锁定。

当 $b>0$，完成纤维的实仿射维数为 $2\operatorname{rank}A$。相反，从某个固定 $\rho_c$ 出发的通道轨道 $\{\mathcal D_z(\rho_c):|z|\le1\}$ 只把 $c$ 变为 $zc$，维数至多二；$c=0$ 时轨道单点，即使整个边界纤维仍含许多非零完成。守恒代数的状态纤维与一个输入的校正圆盘不能混称为同一个对象。

**命题 10.4（同一边界的可分辨完成）。**

$$
|\psi_\pm\rangle=(|v\rangle\pm|f\rangle)/\sqrt2
$$

是正交态，具有同一 $A=\operatorname{diag}(1/2,0)$、$b=1/2$，同一 $(E,G)$ 概率 $(1/2,7/32)$ 和同一实际 $\mathcal F$ 输出；但效果 $|\psi_+\rangle\langle\psi_+|$ 的概率分别为一和零。

证明。两态只差跨块列的符号。$\Delta$ 删除该列，$E,G$ 均在 $\mathfrak A$ 中。相干效果则投影到两个正交态之一，得到所述极值，亦实现定理 10.2 的两端。

两个任务数值甚至不决定 $\mathcal F$ 输出：取 $Y=i(|r\rangle\langle v|-|v\rangle\langle r|)$，$\rho_\pm=I_3/3\pm tY$、$0<t\le1/3$。二者正且迹一，$E,G$ 的实矩阵与纯虚反对称 $Y$ 迹配对为零，所以两概率均为 $(1/3,1/3)$；但 $Y\in\mathfrak A$ 且非零，$\mathcal F(Y)=U_0YU_0^\dagger\ne0$，故后继不同。定理 9.5 的“一个通道对所有输入保持两任务”不能换成“任意两个具有相同两数值的输入有相同后继”。

## 11. 有限旗标存储、附加读出与精确维数阈值

**定义 11.1（固定有限旗标存储合同）。** 所有未知 qutrit 输入的信息必须经过

$$
\operatorname{Enc}:M_3\longrightarrow\bigoplus_{\ell\in L}M_q,
\qquad \operatorname{Dec}_\ell:M_q\longrightarrow M_3,
$$

其中 $L$ 有限，总编码 CPTP，每个解码器在整个 $M_q$ 上 CPTP。编码、解码均在输入及晚选任务之前固定；没有原态副本、量子环境旁路、其他量子存储或预共享纠缠。$\ell$ 是由该份标本实际产生的完整经典解码旗标，允许依赖输入。合成 qutrit 通道为

$$
\mathcal T=\sum_\ell\mathcal K_\ell,\qquad
\mathcal K_\ell=\operatorname{Dec}_\ell\operatorname{Enc}_\ell.
$$

维数 $q$ 只计相干量子端口，经典旗标另计；默认解码后消耗或丢弃旗标。保留其联合输出需另写合同。该有限直和模型及秩分解使用 [BRW] 的测量相对压缩接口，具体圆盘端口结论为 [Retained] 定理 10.2 的应用。

**定理 11.2（规定圆盘通道的精确维数跳变）。** 在定义 11.1 下，

$$
q_{\min}(\mathcal D_z)=
\begin{cases}2,&z=0,\\3,&z\ne0.\end{cases}
$$

证明。写编码 Kraus 为 $B_{\ell a}:\mathbb C^3\to\mathbb C^q$、解码 Kraus 为 $C_{\ell b}:\mathbb C^q\to\mathbb C^3$。每个实际合成 Kraus

$$
L_{\ell ba}=C_{\ell b}B_{\ell a}
$$

秩至多 $q$。定理 9.5 的固定投影证明适用于这个实际家族，故每项都为 $\alpha_{\ell ba}P_++\beta_{\ell ba}P_-$。归一性要求至少一项 $\alpha\ne0$，其秩至少二，故 $q\ge2$。若 $z\ne0$，$z=\sum\alpha\bar\beta$ 中至少一项两系数均非零；该项秩为三，所以 $q\ge3$。

为达到 $z=0$，选固定等距 $J:\mathbb C^2\to P_+\mathbb C^3$，用两个旗标编码

$$
\operatorname{Enc}_+(X)=J^\dagger XJ,\qquad
\operatorname{Enc}_-(X)=\langle f,Xf\rangle|0\rangle\langle0|.
$$

两分支为 CP，迹和为 $\operatorname{tr}X$。整块解码取

$$
\operatorname{Dec}_+(Y)=JYJ^\dagger,\qquad
\operatorname{Dec}_-(Y)=\operatorname{tr}(Y)|f\rangle\langle f|.
$$

两者在全部 $M_2$ 上 CPTP，合成恰为 $\Delta=\mathcal D_0$。任意非零 $z$ 可用三维恒等编码、单旗标解码 $\mathcal D_z$ 实现。上下界相合。

**定理 11.3（附加效果的精确敏感度）。** 额外声明一个可用效果 $0\le H_0\le I_3$，写成

$$
H_0=\begin{pmatrix}H_+&h\\h^\dagger&h_-\end{pmatrix},\qquad c_H=\|h\|.
$$

在全部输入上的最坏概率误差精确为

$$
\sup_{\rho\in\mathcal D_3}
\left|\operatorname{tr}(H_0\mathcal D_z(\rho))-\operatorname{tr}(H_0\rho)\right|
=|1-z|c_H.
$$

因此块对角效果不增加约束；任何 $h\ne0$ 的效果若被精确保留，就强制 $z=1$、$\mathcal D_z=\operatorname{id}$。

证明。对偶残差为 Hermitian 矩阵

$$
\mathcal D_z^\dagger(H_0)-H_0
=\begin{pmatrix}0&(\bar z-1)h\\(z-1)h^\dagger&0\end{pmatrix}.
$$

若 $h\ne0$，在 $\operatorname{span}\{(h,0),(0,1)\}$ 上其特征值为 $\pm|1-z|\|h\|$，其余一个特征值为零；$h=0$ 时全零。Hermitian 期望在密度矩阵上的绝对最大值就是最大绝对特征值，且由相应纯态达到，故等式精确。增加未触及参考、仍只读本地效果 $H_0$ 时只涉及本地约化态，同一极值不变。这里不是对其他联合观察合同的距离断言。

**推论 11.4（两任务精确时的附加效果容差阈值）。** 固定 $\varepsilon\ge0$，继续要求 $E,G$ 在所有输入上精确保留，只把新效果 $H_0$ 的所有输入误差允许为至多 $\varepsilon$。定义 11.1 下的最小相干端口为

$$
q_{\min}(E,G;H_0,\varepsilon)=
\begin{cases}2,&\varepsilon\ge c_H,\\3,&0\le\varepsilon<c_H.\end{cases}
$$

证明。定理 9.5 把任意合格通道限定在圆盘内。$q=1$ 已被定理 11.2 排除；$q=2$ 只能给 $z=0$，其附加误差恰为 $c_H$，且已有达到构造。$q=3$ 可用恒等通道，误差为零。特别地 $c_H=0$ 时对每个非负容差均为二。该阈值保持两个原任务精确，不处理同时放松 $E,G$ 的近似压缩问题；附加效果的取得是新增观察合同，不能从原生菜单自动推得。

**命题 11.5（新旗标的一般联合输出）。** 对任意实现 $\mathcal D_z$ 的定义 11.1 编码解码，每个分支具有形式

$$
\begin{aligned}
\mathcal K_\ell(X)={}&a_\ell P_+XP_++b_\ell P_-XP_-\\
&+c_\ell P_+XP_-+\bar c_\ell P_-XP_+,\\
a_\ell,b_\ell&\ge0,\quad |c_\ell|^2\le a_\ell b_\ell,\qquad
\sum_\ell a_\ell=\sum_\ell b_\ell=1,\quad \sum_\ell c_\ell=z.
\end{aligned}
$$

旗标概率为 $\operatorname{tr}((a_\ell P_++b_\ell P_-)\rho)$，通常依赖输入。若保留旗标后再作实际无标签后继，联合输出为

$$
\sum_\ell|\ell\rangle\langle\ell|\otimes
\mathcal F(a_\ell P_+XP_++b_\ell P_-XP_-).
$$

证明。将固定 $\ell$ 的 $\alpha,\beta$ 系数分别平方求和定义 $a_\ell,b_\ell$，交叉内积定义 $c_\ell$；Cauchy–Schwarz 和总归一化给全部约束。跨块矩阵迹为零，所以得旗标概率；$\mathcal F$ 删除跨块项，得联合公式。与参考张量的版本由同一 CP 分支恒等式给出。这一般不是“一个输入无关的旗标”张量“$\mathcal F(X)$”。

**定理 11.6（二维端口的完整旗标必须分离扇区）。** 在定义 11.1 中取 $q=2$，并要求精确保留 $E,G$。那么每个完整解码旗标满足

$$
a_\ell b_\ell=0.
$$

忽略零分支后，旗标分成纯 $+$ 与纯 $-$ 两族，分别有系数和一；完整旗标必定确定标本落入哪个块，至少有两个正旗标值。反向，每个满足此纯扇区形式及归一化的有限分支族都可用二维端口实现。

证明。每个实际 $C_{\ell b}B_{\ell a}=\alpha_{\ell ba}P_++\beta_{\ell ba}P_-$ 秩至多二，所以单项不能同时有非零 $\alpha,\beta$。但还须排除同一旗标中不同项分别承担两块。

固定旗标并假设 $a_\ell>0$。选 $a_0,b_0$ 使 $\alpha_{\ell b_0a_0}\ne0$。从

$$
C_{\ell b_0}\bigl(B_{\ell a_0}|_{P_+\mathbb C^3}\bigr)
=\alpha_{\ell b_0a_0}I_{P_+\mathbb C^3}
$$

可知 $A_*=B_{\ell a_0}|_{P_+\mathbb C^3}:P_+\mathbb C^3\to\mathbb C^2$ 为同维可逆映射。对同旗标的每个解码 Kraus，

$$
C_{\ell b}A_*=\alpha_{\ell ba_0}I_{P_+\mathbb C^3}.
$$

因 $A_*$ 满射，这使每个 $C_{\ell b}$ 的全部像均在 $P_+\mathbb C^3$ 内，系数为零时该 $C_{\ell b}$ 就全零。因此对任意编码索引 $a$，$C_{\ell b}B_{\ell a}$ 都不可能含非零 $P_-$ 分量；所有 $\beta$ 为零，即 $b_\ell=0$。若 $a_\ell=0$，则所有 $\alpha$ 已为零，$c_\ell=0$，仅余纯负扇区。两族系数和分别为一，保证各族非空。

反向，把定理 11.2 的 $+$ 编码按各 $a_\ell$ 随机拆分标签，$-$ 编码按各 $b_\ell$ 拆分，沿用相应整块解码；总编码保持迹，得到任意所述有限纯扇区分支族。

**推论 11.7（完整旗标输入无关的维数后果）。** 若定义 11.1 还要求每个完整解码旗标的分布对所有输入都相同，则精确保留 $E,G$ 所需 $q\ge3$，且三维单旗标恒等存储达到下界。

证明。输入无关要求 $a_\ell P_++b_\ell P_-=p_\ell I$，所以 $a_\ell=b_\ell=p_\ell$。二维时定理 11.6 强制 $p_\ell=0$ 对所有旗标成立，与总概率一矛盾。一维已经排除，三维恒等编码解码且只有一个旗标可行。此结论只针对解码器使用的完整旗标；公开一个忘掉扇区的粗粒化子记录可以输入无关，不能据此反驳或套用本推论。

## 12. 旧历史、采集切口与保留标签的另一任务

**定义 12.1（实际历史与旧记录）。** $n$ 次原始采集的实际标签序列为 $h=(j_1,\ldots,j_n)$，按时间顺序的酉乘积为

$$
Q_h=V_{j_n}\cdots V_{j_1}.
$$

每条历史概率 $2^{-n}$，与 qutrit 输入及未触及参考无关。实际保留的旧记录 $a$ 由完整经典核 $r(a\mid h)$ 得到，旗标可有限或可数。定义 $p_{h,a}=2^{-n}r(a\mid h)$。旧记录是实际采集或其实际后处理所得，不能将未安装的全历史作为后续控制 oracle。

[Retained] §§1–3 的固定长度来源结论如下：记全酉字的射影类数量为 $m_n(\theta)=|\{[Q_h]\}|$，即时锐任务的效果纤维满足

$$
Q_hEQ_h^\dagger=Q_gEQ_g^\dagger
\quad\Longleftrightarrow\quad Q_h=Q_g\text{ 或 }Q_h=Q_gW.
$$

固定长度的共同 spectator 相位使右边可用实际矩阵等式；不抹去该相位来另作字分类。具体地，每个 $Q_h$ 把 $\xi$ 送到 $e^{in\theta}\xi$，且在 $\operatorname{span}(e,f)$ 上的行列式为 $\pm1$。效果相等先给 $Q_hv$ 与 $Q_gv$ 仅差相位，比较其非零 $\xi$ 分量就固定该相位为一；于是 $Q_he=Q_ge$。$Q_g^\dagger Q_h$ 在该二维空间内固定 $e$，酉性使另一方向只乘单位相位，行列式又迫使该相位为 $\pm1$，因此只有 $I,W$ 两种。反向由 $WEW=E$ 立即成立。$n\ge1$ 时即时效果类数为 $m_n/2$，$n=0$ 时为一。共同即时校正存在，当且仅当每个正记录纤维都包含于一个效果纤维；来源已有代表逆控制达到此界。全字恢复则要求每个正记录纤维细分 $[Q_h]$，最小记录值数 $m_n$。这些是指定来源的已供应字分类及控制接口，不是任意历史模型的结论。

**命题 12.2（输入无关旧记录的分支守恒）。** 设 $p_\lambda$ 为固定有限或可数概率，与输入无关，$S_\lambda:M_3\to M_3$ 每项 CPTP，且平均 $\sum p_\lambda S_\lambda$ 精确保留 $E,G$。则每个正权项都是某个 $\mathcal D_{z_\lambda}$。因此对任意参考态 $\rho$，

$$
\sum_\lambda p_\lambda|\lambda\rangle\langle\lambda|\otimes
((\mathcal FS_\lambda)\otimes\operatorname{id})(\rho)
=\sum_\lambda p_\lambda|\lambda\rangle\langle\lambda|\otimes
(\mathcal F\otimes\operatorname{id})(\rho).
$$

即时 $E$ 结果及参考条件态也逐分支相同。

证明。平均通道由定理 9.5 固定 $\mathfrak A$ 的每个投影。若 $P$ 是投影，且正收缩的凸和 $\sum p_\lambda S_\lambda^\dagger(P)=P$，则在 $\ker P$ 上零期望和迫使每项为零，在 $\operatorname{ran}P$ 上对补投影同理，故每个正权项都固定 $P$。有限个投影即可线性张成 $\mathfrak A$，于是每个 $S_\lambda$ 固定 $E,G$，应用定理 9.5。可数和中每个非负项仍必须为零。通道和效果恒等式张量参考后给联合结论。

凡后续有限续接只由实际可读的子记录控制，就可对联合式逐块应用同一后续 CP 映射，保持相等。这不授权访问反事实全记录，也不要求新存储旗标输入无关。新旗标属于命题 11.5，其分支未必 CPTP，不能套用本命题的凸组合论证。

**命题 12.3（同一标本上的采集切口与存储切口）。** 对即时任务与擦标签后继任务，既有最小效果记录 $m_n/2$（$n\ge1$）与二维存储上界可以在同一次运行达到。旧记录必须保留到代表逆调用完毕；存储编码在该逆之后开始。此后只有不再被任务使用的旧记录才可释放。

证明。来源的代表逆使每条相容历史的剩余态为 $\rho$ 或 $W\rho W$。二者即时 $E$ 概率相同，且 $\Delta\operatorname{Ad}_W=\Delta$，所以插入定理 11.2 的编码解码后逐历史都为 $\Delta(\rho)$，实际后继也相同。即时任务的原有必要性保留，给最小旧记录数。若保留完整历史、旧记录和新扇区旗标 $s$，实际联合无标签后继是

$$
\sum_{h,a,s}2^{-n}r(a\mid h)|h,a,s\rangle\langle h,a,s|
\otimes\mathcal F(P_s\rho P_s),
$$

参考版本逐块张量恒等。对可取得子记录作实际后处理即可，不能把新 $s$ 与旧 $a$ 当成同一种存储资源。

规定非零 $z$ 时，一个已供应的同运行上界是先用完整字类记录及其逆恢复原输入，再用三维端口实现 $\mathcal D_z$。没有证明最小效果记录已丢失的相干还能在其后装回；所以不把该上界的旧记录数改写为 $m_n/2$。

在 $\theta=\pi/6$，来源供应全字单射 $m_n=2^n$：效果路线保留实际后缀的 $n-1$ 位，调用 $n$ 次逆字母（$n\ge1$）；完整字路线保留 $n$ 个实际标签并调用 $n$ 次逆字母。在 $\theta=0$，来源给三位置任务累加器与六状态完整置换累加器，各用一次选定逆置换；在 $n=0,1,2,n\ge3$ 四种范围，完整字类数分别为 $1,2,4,6$，即时任务类数分别为 $1,1,2,3$，其固定二进制负载分别为 $0,0,1,2$ 位。任务累加器跟踪 $Q_he$ 中唯一负坐标的位置，实际标签按置换更新，初始及头两步的可达集为 $\{2\},\{1\},\{0,2\}$，第三步起为全部三位置；完整字累加器则跟踪整个位于 $S_3$ 的置换。$n=0$ 不需历史采集或逆。一般固定实校准只给相应有限表的存在性，不给未知角采集或精确实数比较、控制合成的一致有效算法。

每次原运行有 $n$ 次新环境制备、相互作用、环境测量和实际标签取得。无标签后继再加各一次并擦去新标签，终端另作一次二元测量。编码、解码、校准、存储旗标及寻址和计时装置是额外资源；这些达到构造不声称联合硬件或控制总成本最优。以上取得与控制结论均按 [Retained] §10 供应的权限消费，不扩张原生五模式菜单。

**命题 12.4（qutrit 输出且保留新标签的刚性）。** 把定义 9.4 的第二任务换成实际新标签与二元结果 $(j,y)$ 的联合概率，仍要求同一 qutrit 输出的 CPTP 校正在任务晚选前作用、对所有输入正确。则校正只能为恒等通道。

证明。标签分支在 qutrit 上公平，故联合任务等价于固定 $E$ 和两个投影 $F_j=V_j^\dagger EV_j$。在 $(\xi,e,f)$ 基中，忽略不影响投影的共同相位，可写

$$
w_\pm=\frac1{\sqrt2}\left(\xi-\frac12e\pm\frac{\sqrt3}{2}e^{2i\theta}f\right),
\qquad F_0=|w_+\rangle\langle w_+|,\quad F_1=|w_-\rangle\langle w_-|.
$$

$v,w_+,w_-$ 均为单位向量，两两内积为 $1/4$，并张成 qutrit：差向量给 $f$，和向量及 $v$ 张成 $\xi,e$。每个校正 Kraus 都与这三个投影对易。若一个矩阵 $L$ 与 $|x\rangle\langle x|$ 对易，则 $Lx=\lambda_xx$ 且 $\langle x|L=\lambda_x\langle x|$；对非正交 $x,y$ 比较 $\langle x,Ly\rangle$ 得 $\lambda_x=\lambda_y$。三个向量张成，故 $L$ 为标量单位。迹保持给合成恒等。此为 [Retained] §5 的实际标签刚性应用。

因此在同一有限旗标模型中，即时 $E$ 单任务可用纯经典测量制备、$q=1$；即时加无标签后继需 $q=2$；即时加记录 $(j,y)$ 且 qutrit 输出需 $q=3$。最后一项的下界由恒等通道每个非零 Kraus 秩三及因子分解给出，上界为恒等存储。这三种合同不是同一观察域。

## 13. 不限于 qutrit 子空间的实际输出合同

**定义 13.1（全 $H$ 解码与联合未来）。** 保持定义 9.1 的实际 $A_j$ 与定义 12.1 的来源、旧记录核，改允许共同解码器 $\mathcal D_a:M_5\to M_5$ 的输出落在任意 $H$ 中。令 $\widehat E=BE B^\dagger$，$\widehat E^{(1)}=\widehat E$、$\widehat E^{(0)}=I_5-\widehat E$。晚选两任务分别是即时二元测试，以及一次进一步实际采集并保留联合 $(j,y)$。没有新采集之后的额外校正。要求每个 qutrit 输入都满足

$$
\begin{aligned}
\sum_{h,a}p_{h,a}\operatorname{tr}\bigl(\widehat E\mathcal D_a(BQ_h\rho Q_h^\dagger B^\dagger)\bigr)
&=\operatorname{tr}(E\rho),\\
\sum_{h,a}p_{h,a}\operatorname{tr}\bigl(\widehat E^{(y)}A_j
\mathcal D_a(BQ_h\rho Q_h^\dagger B^\dagger)A_j^\dagger\bigr)
&=\operatorname{tr}\bigl(\widehat E^{(y)}A_jB\rho B^\dagger A_j^\dagger\bigr)
\quad(j,y\in\{0,1\}).
\end{aligned}
$$

所比较的是每个晚选查询，不是对一个查询分布的平均。原历史仍公平，但一般泄漏态上的 $A_j^\dagger A_j$ 不是 $I_5/2$；未来效果也不能在全部 $H$ 上换成公平 qutrit 投影。例如物理输入 $|e_0\rangle$ 的新标签零概率是 $\cos^2\theta$，不是由 qutrit 公平性强制的一半。

**定理 13.2（实际全 $H$ 任务的记录存在性）。** 对任意固定实 $\theta$ 与 $n\ge0$，定义 13.1 的解码器存在，当且仅当

$$
r(a\mid h)r(a\mid g)>0\quad\Longrightarrow\quad[Q_h]=[Q_g].
$$

因而最小旧记录值数是已供应的 $m_n(\theta)$，固定二进制负载为 $\lceil\log_2m_n(\theta)\rceil$；$n=0$ 是一个值、零位。若任务还保留实际旧记录，存在性判据不变。

证明。这里消费并展开 [Retained] 定理 11.2 的正支撑论证。取 $p=Bv$、$P=|p\rangle\langle p|=\widehat E$，$t_j=A_j^\dagger p$，实际全 $H$ 后继效果为

$$
G_j^H=|t_j\rangle\langle t_j|=A_j^\dagger PA_j,
\qquad B^\dagger G_j^HB=\tfrac12F_j.
$$

对固定记录 $a$，写 $X\mapsto\mathcal D_a(BXB^\dagger)$ 的矩形 Kraus 为 $L_{a\nu}:\mathbb C^3\to H$，满足 $\sum_\nu L_{a\nu}^\dagger L_{a\nu}=I_3$，并置

$$
H_a=\sum_\nu L_{a\nu}^\dagger PL_{a\nu},\qquad
M_{a,j}=\sum_\nu L_{a\nu}^\dagger G_j^HL_{a\nu}.
$$

即时等式是 $\sum p_{h,a}Q_h^\dagger H_aQ_h=E$。各项为正收缩且权重总和为一，锐投影的零范数及补投影论证给每个正 $(h,a)$ 都有 $H_a=Q_hEQ_h^\dagger$。因此同记录的 $h,g$ 必在来源的即时效果纤维中：$Q_h=Q_g$ 或 $Q_h=Q_gW$，使用命题 12.1 的固定长度来源结论。

未来的 $j=0,y=1$ 等式给

$$
\sum_{h,a}p_{h,a}Q_h^\dagger M_{a,0}Q_h=\tfrac12|w_+\rangle\langle w_+|.
$$

在 $w_+^\perp$ 上，左侧非负二次型之和为零，所以每个正项支撑于 $\mathbb Cw_+$；再展开 Kraus，得到

$$
L_{a\nu}^\dagger t_0\in\mathbb C Q_hw_+
\quad\text{只要 }r(a\mid h)>0.
$$

可数记录同样成立，因为非负级数为零时每项为零。假设同一个正记录同时含不等的 $Q_h=Q_gW$。$Ww_+=w_-$，且 $w_+,w_-$ 是不同直线；故每个 $L_{a\nu}^\dagger t_0$ 同时落在两条不同的一维子空间内，必须为零，因而 $M_{a,0}=0$。

另一方面 $H_a=Q_gEQ_g^\dagger$ 使解码态
$\sigma=\mathcal D_a(BQ_gEQ_g^\dagger B^\dagger)$ 满足 $\operatorname{tr}(P\sigma)=1$。正迹一矩阵在秩一投影上期望为一，只能是 $\sigma=P$：补空间的迹为零，正性使所有交叉项亦零。实际源的非零重叠为

$$
|\langle p,A_0p\rangle|^2
=\frac12|\langle v,V_0v\rangle|^2
=\frac1{32}.
$$

最后一步由 $V_0^\dagger v=e^{-i\theta}w_+$ 及 $\langle w_+,v\rangle=1/4$。故该解码态的 $G_0^H$ 概率为 $1/32$，但 $M_{a,0}=0$ 又强制它为零，矛盾。排除第二种纤维可能，得到完整字类细分。这里仅用未来正效果的支撑，不把不锐的平均等式冒充逐分支等式。

反向若已细分字类，每个正记录选代表 $Q_a$，用全 $H$ 酉

$$
D_a=BQ_a^\dagger B^\dagger+(I_5-P_{R_H}),\qquad
\mathcal D_a=\operatorname{Ad}_{D_a}.
$$

两个正交块均酉，且 $Q_a^\dagger Q_h$ 为标量，逐历史恢复 $B\rho B^\dagger$，也恢复与任意未触及参考的联合态。之后实际 $A_j$ 及二元测试自然给全部即时和未来等式。每个历史原概率正，不同字类需要不相交的正记录值，记录字类即可达到最小值。$n=0$ 用空字及恒等解码，不作除二。

这个上界还能保留全部已取得旧记录。若 $\rho$ 包含参考，进一步实际采集后的联合态为

$$
\sum_{h,a,j}2^{-n}r(a\mid h)|h,a,j\rangle\langle h,a,j|\otimes
\tfrac12(BV_j\otimes I)\rho(V_j^\dagger B^\dagger\otimes I).
$$

逐块加终端测试或后续实际操作给相应联合输出；必要性则由忘掉记录回到定义 13.1。因此保留旧记录不改变存在性判据。

此定理不分类每个成功的矩形校正映射 $M_3\to M_5$，也不把定理 11.2 的 qutrit 输出端口最小值运输到此合同。上述上界逐分支恢复原态，不意味着每个满足定义 13.1 的解码器都满足该强联合态等式。保留标签的后继另加一次实际环境制备、相互作用、环境测量、标签取得及终端二元测试；即时分支只加终端测试。全字采集和逆的资源仍如第 12 节，不产生总硬件最优性结论。

## 14. 独立性、共同模型与分层重构

**命题 14.1（有限原子不强制连续标量）。** 第 2 节五点原子有整数坐标模型，并不要求全部实数可取得或标量完备。

证明。在已定向标准三维中取

$$
o=0,\quad p_1=e_1,\quad p_3=e_2,\quad p_2=e_3,\quad q=e_1+e_2.
$$

三腿非零正交，三端点两两距离平方均为二，手性为正，全部平面闭合成立。取平面 $\operatorname{span}(e_1,e_2)$ 的 $J(e_1)=e_2,J(e_2)=-e_1$，它保持整数格；以 $J$ 充当乘 $i$ 仅给高斯整数模，不自动给全部复数标量。若供应有序实代数数域，则有限正交归一化所需平方根仍在域中，但该域可数且不完备。因此有限精确几何、归一化、连续参数可取得性与 Hilbert 完备性是不同合同。

**命题 14.2（有限原子不强制非交换概率理论）。** 同一五标签事件结构允许交换的经典赋值和丢信息粗粒化。

证明。取五函数代数 $\mathbb R^{\mathcal M}$，$|\mathcal M|=5$，逐点乘法。任意概率向量 $p_m\ge0$、$\sum_mp_m=1$ 给正归一泛函 $f\mapsto\sum_mp_mf(m)$。任意合并标签的确定性映射给经典粗粒化，可以使不同分布具有相同读数；它不产生 Pauli 反对易。把该赋值与命题 14.1 的几何一起取直积即可同时实现关系和经典概率。原生来源树仍可独立按定义 1.4 生成。故有限几何及无序闭合不足以强制量子非交换性。

**定理 14.3（带类型的分层重构）。** 对五端口关系，分别供应下列条件，就分别得到对应结论。

| 条件与量词范围 | 对应结论 |
| --- | --- |
| 锚定距离的全部有限 Gram 矩阵半正定，并允许实线性商与完备化 | 保持共同距离的最小实 Hilbert 表示；有限最小维数为 Gram 秩 |
| 严格锐角的三个共同端点、三维定向、固定有标号三腿手性 | 唯一非退化内生原点 |
| 该原点的基平面及两个平移侧面闭合 | 唯一对角点；高维需限制在三腿空间 |
| 全域交替面积双线性积及 Jacobi | 三维及有符号叉积 |
| 正交三轴的指定 Clifford 结合复合 | 中心复单位、Pauli 代数和复二维旋量模 |
| 平面正交运输及每条闭行走定向乘积为正 | 相容局部复结构；不额外消除回路相位 |
| 非负旋转不变且对所有正交贡献可加 | 平方范数权重，单位校准固定系数 |
| 给定复载体上所有效果的单值、正归一、细分可加赋值 | 唯一密度矩阵、Born 形式及自动 Lipschitz 连续性 |
| 所有混合的仿射态更新 | 唯一正保迹扩张；任意本地参考正性才进一步给完全正性 |
| 下闭合法配置及全部合法交换菱形 | 固定起终点的路径独立 |
| 固定张量、端口切分、内积与等距或酉恒等式 | 相应切分的等距或酉门 |
| 实际 qutrit 来源及两个所有输入任务 | 守恒 $M_2\oplus\mathbb C$ 的校正圆盘，恒等点有更大固定空间 |
| 整个守恒代数的状态限制 | 定理 10.2 的完成纤维及尖锐目标区间 |
| 有限旗标存储及明确的附加效果误差合同 | 精确端口跳变、定理 11.4 的阈值及完整二维旗标的扇区必要性 |

证明。关系层的因子化由命题 1.2，几何由定理 2.1、2.3，表示由定理 3.1、3.2 和第 4 节，运输由第 5 节，权重及预测由第 6 节，更新与门由第 7 节。第 9–13 节以明示的实际来源和输出域给后面各结论。各步只用该行合同以及所引用的先行定义，不把 $\mathbb R^3$、平面 $\mathbb C^1$、旋量 $\mathbb C^2$、原生模式 $\mathbb C^5$、qutrit 与物理 $H$ 识别。特别地，“全部关系锁定”必须相对于声明目标的完成纤维或守恒代数解释，不能解释为所有语义读数都已确定。

**命题 14.4（共同模型非空）。** 分层重构中的几何、表示、概率与实际来源条件有共同实现；各存储合同在其已证可行维数实现，且不需混淆各载体的类型。

证明。采用命题 14.1 的标准 $\mathbb R^3$ 五点，并供应全部实标量及其完备性，距离取欧氏距离；正向手性选出 $o=0$，其镜像原点被排除。取标准叉积及 $\mathrm{Cl}_{3,0}$、标准 Pauli 模；每个图顶点用同一欧氏平面，边运输取恒等，或在保向条件下任取 $U(1)$ 相位。赋值任选密度矩阵并设 $\mu(E)=\operatorname{tr}(\rho E)$，幅度权重取平方范数。若需要门，取已归一化的 $R_\theta$ 和已声明的输入输出切分；这些操作满足各自恒等式。

另以定义 9.1 的 $H$、环境和实际测量实现 qutrit 应用，固定 $B$、共同坐标、$E,G$，取任意 $\mathcal D_z$ 及其已给有限旗标存储构造；若另外要求完整旗标输入无关，则采用三维恒等构造。二维端口与该附加要求不能同时成立，正是推论 11.7 的排除结论。原生五模式载体及树来源另按自身定义实现。它们可以在类型直积中共存；共同模型不要求把两个都含数字“五”的对象当成同一空间。

各反模型同时标出不能省略的桥梁：二元相融不保完整支撑，几何唯一不保任意语义，有限坐标不保标量完备，局部三轴拟合不保全效果赋值，正映射不保本地参考正性，固定网络不保串行门交换，观测分布不保干预，两个任务数值不保完整状态，旧历史无关性不保新旗标无关性。原生 $\varrho$、合法窗口或实际延拓要承担更强结论，必须逐项供应相应全域复合、细分、校准、参考和可取得控制的对应；有限原子核对不能替代这些量词。

空间取得、物理持续时间以及原生 $\alpha/\beta$ 过程与本实际测量源的同一性，还分别需要独立采集、时间标定、共同初始化、合法选择器、已安装的保留记录使用及资源和后继对应。本卷的条件表示、校正和存储结果不把这些未供应的接口变为经验主张，也不识别独立的等待、过滤或五模式实验菜单。

## 15. 引用与所消费的结果

[Foundation]：[FIB-ATOM 金字塔基础公式与关系，§§1–4](https://github.com/the-omega-institute/trureturing/blob/424ceebcee83a8165d49a535eafa85c16acbaa19/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)。用于有序来源、五函数代数、五顶点八棱的结构和原生数量读出。

[ThreeAxis]：[观察者内生三轴几何与预测接口，§§2、5–9](https://github.com/the-omega-institute/trureturing/blob/424ceebcee83a8165d49a535eafa85c16acbaa19/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)。用于共同三轴几何、Gram 商、全域面积与 Jacobi 的条件推导，以及实际取得和表示范围的区分。

[Static]：[AURIC Omega 静态相融纤维理论，§§1、3、5–8](https://github.com/the-omega-institute/trureturing/blob/424ceebcee83a8165d49a535eafa85c16acbaa19/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。用于关系纤维、完整支撑粘合、合法菱形、效果表示及五模式菜单的边界。

[Retained]：[Sharp task retained environment memory，§§1、5、8–12](https://github.com/the-omega-institute/trureturing/blob/424ceebcee83a8165d49a535eafa85c16acbaa19/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md)。用于本卷完整写出的实际来源、字与效果记录纤维、校正圆盘、有限旗标维数、保留记录及全 $H$ 输出合同；其引用的原始取得和逆控制结果在本卷仅按明确的既有供应接口消费。状态完成、附加效果和完整二维旗标结论均以这些指定接口为前提。

[Clifford]：Marc Lachièze-Rey，*Spin and Clifford algebras, an introduction*，[arXiv:1007.2481v1，§§1.6–1.8、3.3](https://arxiv.org/html/1007.2481v1)。用于实 Clifford 代数、Pauli 表示、reversion、旋量与旋子。

[Busch]：Paul Busch，*Quantum states and generalized observables: a simple proof of Gleason's theorem*，[arXiv:quant-ph/9909073v3](https://arxiv.org/html/quant-ph/9909073v3)。完整效果域的正归一可加赋值给密度算子；本卷在预测接口内给出有限维证明。

[Caves]：Carlton M. Caves、Christopher A. Fuchs、Kiran K. Manne、Joseph M. Renes，*Gleason-Type Derivations of the Quantum Probability Rule for Generalized Measurements*，[arXiv:quant-ph/0306179](https://arxiv.org/abs/quant-ph/0306179)。用于 POVM 与二维概率重构的文献归属。

[BRW]：Andreas Bluhm、Thomas Rauber、Michael M. Wolf，*Quantum compression relative to a set of measurements*，[arXiv:1708.04898v4](https://arxiv.org/abs/1708.04898v4)。有限经典侧信息压缩、Kraus 秩分解和分块上界构造；一般生成代数的最大块上界并不自动成为任意任务的精确最小值，本卷的下界另由指定圆盘每个实际 Kraus 的秩给出。

[BKK]：Cédric Bény、Achim Kempf、David W. Kribs，*Quantum Error Correction of Observables*，[arXiv:0705.1574v1](https://arxiv.org/abs/0705.1574v1)。用于守恒观察代数与混合量子经典信息纠错的背景；实际全 $H$ 不锐效果的正支撑证明仍依赖定义 9.1 的矩阵，不能由背景结果改成公平分支。

## 追加锚（本行以下为增补区）

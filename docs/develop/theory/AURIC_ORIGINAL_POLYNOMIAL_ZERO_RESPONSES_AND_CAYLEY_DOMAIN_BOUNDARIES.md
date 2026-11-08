# AURIC：原多项式零响应与 Cayley 原域边界

## 1. 原界面、记号与来源范围

**定义 1.1（原对象与外卷引用）。** 称 [《配平三角的共同取向与秩一响应续卷》](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) 为配平主卷，称 [《任意维小窗口单位桥》](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md) 为单位桥卷，称 [《任意维静态量子重构》](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md) 为静态重构卷。本卷的编号为 §§1–3；配平主卷的 128–234、单位桥卷及静态重构卷的编号均只指相应外卷条目。

取配平主卷定义 128.1、183.1 的同一原实 Archimedean 序单位空间 $(E,C,u,N)$、原正实线性评价族 $\mathcal P$ 及总映射 $S,D:E^2\to E$。原 A1 要求全部原有向 Hermitian 二表正性；原 A2 要求相加三表 $(a+b,a,b)$ 及其排列的实部半正定，且指定向量 $(1,-1,-1)$ 的二次值为零；原 A3 为 $S(u,u)=u$，并对同一固定有理 $0<\theta\le1$ 要求 $0\le e\le\theta u\Rightarrow S(e,e)\le e$。消费其既有无 $R$ 的 Jordan 接口 $S(a,b)=a\circ b$。$E$ 是任意含单位实 JB 完成 $X$ 中含单位、范数稠密的实 Jordan 子代数，$C=E\cap X_+$，$N=\|\cdot\|_X|_E$。原评价分离 $E$ 并准确决定 $C$，质量为 $m_\alpha=\alpha(u)$。原 P2、完整 PB 及其元素式准确取配平主卷式 (128.3)、(128.4)、(128.6)，保留全部原输入、原评价和零／不等／次归一质量；数学正读取不自动成为实际准备。

$\mathsf T$、$\mathsf F$ 与 $R$ 分别指配平主卷式 (185.2)、(178.2)、(128.5)。$\mathsf F$ 及其与双线性的等价只在配平主卷定义 178.1 的完整复 C* 自伴载体前件下使用。除 §2 明确给定的交换模型外，不预设一般 JB 的特殊表示，亦不预设未知 $D$ 的可加、齐次、连续、可测、协变或完成延拓。原全单位行与标签对称性按配平主卷 §§183–185 复用，实际来源与全部量子消费者的未付条件保持原量词。

## 2. 完整原界面上的 Cayley 全前向零核

**定义 2.1（一个完整原域接口模型）。** 令 $I=[-1,1]$，$X=C(I,\mathbb R)$ 取逐点乘法、单位 $u=1$ 和上确界范数，令

$$
E=\{p|_I:p\in\mathbb R[t]\},\qquad C=E\cap X_+,\qquad S(a,b)=ab,\qquad D(a,b)=0.
$$

于是 $E$ 是含单位的实 Jordan 子代数，并由 Weierstrass 逼近定理在 $X$ 中范数稠密。取全部数学正读者

$$
\mathcal P=\{\alpha:E\to\mathbb R:\alpha\text{ 为实线性且 }\alpha(C)\subseteq[0,\infty)\}.
$$

点评价及其任意非负倍数属于 $\mathcal P$，所以它们分离 $E$ 并准确决定 $C$；每个 $\alpha\in\mathcal P$ 的质量 $m_\alpha=\alpha(u)$ 同时允许零、不等和次归一值。固定任意原候选所要求的正有理数 $0<\theta\le1$。对 $0\le e\le\theta u$ 有逐点 $e^2\le e$，故 $S(e,e)=e^2\le e$。对任意 $a,b$ 和任意 $\alpha\in\mathcal P$，P2 读成

$$
\begin{pmatrix}
\alpha(a^2)&\alpha(ab)\\
\alpha(ab)&\alpha(b^2)
\end{pmatrix}\succeq0,
$$

因为对任意复数 $z_1,z_2$，其二次型等于 $\alpha(|z_1a+z_2b|^2)\ge0$。$(a+b,a,b)$ 的实三表同样由 $\alpha$ 读到非负平方和，指定向量 $(1,-1,-1)$ 给出零平方。因此这里保留完整原 A1–A3、P2 及全部数学正读者和质量。

**命题 2.2（双线性且满足 $R$ 仍可有零完整前向原核）。** 在定义 2.1 的同一原域上，完整 PB 对所有原 $a,b,c$ 和全部 $\alpha\in\mathcal P$ 成立，$D$ 已经实双线性，并满足原换括号关系 $R$。令 $\tau(t)=t$ 为原元，置

$$
F_\tau(x,y)=\bigl(D(\tau,x)-\tau y,\ \tau x+D(\tau,y)\bigr)=(-\tau y,\tau x).
$$

在完成的复化 $C(I,\mathbb C)$ 中用 $x+\mathrm i y$ 识别 $E\oplus E$，并定义完成上的 Cayley 变换

$$
T_\tau=(I+F_\tau)(I-F_\tau)^{-1},\qquad
T_\tau p=\frac{1+\mathrm i\tau}{1-\mathrm i\tau}\,p.
$$

其完整前向原核

$$
\mathcal K_\tau=\{p\in E+\mathrm iE:T_\tau^n p\in E+\mathrm iE\text{ 对所有 }n\ge0\}
$$

恰为 $\{0\}$。但是对每个有限 $N\ge0$，非零原元 $p_N=(1-\mathrm i\tau)^N$ 满足

$$
T_\tau^n p_N=(1+\mathrm i\tau)^n(1-\mathrm i\tau)^{N-n}\in E+\mathrm iE
\qquad(0\le n\le N),
$$

所以任意有限合法前缀仍然存在。这里的种子 $p_N$ 随 $N$ 选择；每个有限 $N$ 都存在非零种子，不等于存在同一个非零种子适用于全部 $N$。

证明。先核对完整配平。对任意 $a,b,c\in E$，在配平主卷定义 128.1 的配平记号中，此处 $D=0$ 使

$$
r_+=b-ac,\quad s_+=c+ab,\qquad
r_-=b+ac,\quad s_-=c-ab.
$$

逐点交换乘法给出

$$
r_+^2+s_+^2=r_-^2+s_-^2=(1+a^2)(b^2+c^2).
$$

每个 $\alpha\in\mathcal P$ 因而读到相同的两侧，这正是全部原 PB；没有调用完成中的新输入。$D=0$ 显然为实双线性，且原 $R$ 的两侧都等于 $abc$，因为逐点乘法结合。故命题的完整数学入口，包括所有正读者、全部质量、零及重复标签，均已满足。

再证明 Cayley 断言。$1-\mathrm i t$ 在 $I$ 上处处非零，所以它在 $C(I,\mathbb C)$ 中可逆，且 $F_\tau$ 在 $x+\mathrm i y$ 坐标下就是乘以 $\mathrm i\tau$。若 $p\ne0$ 且某个 $n$ 使 $T_\tau^n p=q$ 属于 $E+\mathrm iE$，则在区间 $I$ 上有

$$
(1+\mathrm i t)^n p(t)=(1-\mathrm i t)^n q(t).
$$

两边是复系数多项式，区间上的相等即为多项式恒等式。线性因子 $1-\mathrm i t$ 与 $1+\mathrm i t$ 互素，故 $(1-\mathrm i t)^n$ 必整除 $p$。若这对所有 $n$ 成立，非零多项式 $p$ 将被任意高次的同一线性因子整除，矛盾；所以 $\mathcal K_\tau=\{0\}$。另一方面，显示的 $p_N$ 对 $0\le n\le N$ 的公式是多项式恒等式，给出每个有限前缀。整个证明中 $D$ 的调用只有原 $E$ 中的零值；逆元和 $T_\tau$ 只在完成的数学复化中使用。∎

**定义 2.3（几何、来源与消费者边界）。** 受影响的最小结构是两个原输入槽的实直和 $E\oplus E$，通过 $(x,y)\mapsto x+\mathrm i y$ 识别为 $E+\mathrm iE\subset C(I,\mathbb C)$：演员是坐标元 $\tau$，作用是 $(x,y)\mapsto(-\tau y,\tau x)$，而前向要求把两个互素多项式因子 $(1-\mathrm i\tau)$、$(1+\mathrm i\tau)$ 的整条迭代链同时留在原多项式域。这里的“二元”指两个标签槽，不指总实维数为二；本例的标签空间为无限维，不是物理二维或三维空间。原 $E$ 对 Jordan 乘法闭合，所识别的 $E+\mathrm iE$ 对逐点复乘法也闭合，但它们在相应上确界范数下不完备。Weierstrass 稠密性与互素多项式的整除判据是成熟工具；单位桥卷 §4、119.6、静态重构卷 §2.3、§§32–33、§61、§72.1 及配平主卷 §§163–164 已记录多项式根与逆元非闭性、原投影供应边界及已付有限／理想运输的准确前件，配平主卷 183.2–185.1、§§178–199 的单位行、条件消费者和跨输入限制均只作复用，配平主卷 §§200–215 的指定 C* 分支、原圆及局部比较保留其已证范围；配平主卷 §§216–222 的正交响应平方细化保留其定义 216.1 的指定复载体包含前件，不要求 $X=A_{\rm sa}$，亦不供应一般 JB 的该包含。配平主卷 §§223–228 的单一非标量 Gram 坐标、共同加权三轴响应和实际外层预算接口保持各自指定复 C* 前件，并保留径向、可加性及一般 JB 桥；配平主卷 §§229–234 则在其指定复 C* 背景中给出非零共享响应的准确平方、非负平方缺陷、该缺陷为零与径向齐次的准确等价，以及有限预算接口仍容许严格正缺陷的限制，保留一般径向、可加性和一般 JB 复载体来源的缺口；这些结论不涉及本条指定 Cayley 变换的完整前向原核。多项式模型本身不是新的一般非闭性定理；本条的局部增量是把同一完整原 A1–A3/P2/PB 接口和已成立的双线性、$R$，接到指定签名 Cayley 消费者的全前向量词，得到非零核为空而有限前缀不为空。

因此，若原域群路线要求一个非零集合对该 Cayley 变换的所有正向迭代都保持原性，单靠完整 P2、PB、双线性和 $R$ 不能普遍供应这一步。本例只限制这个指定 $T_\tau$ 的完整前向原核，不排除其他演员或其他 Cayley 方法。这个例子不是平移、可加性或 $R$ 的总 $D$ 反模型；任意实 JB 完成中由原 P2+PB 推出跨轴单位平移、一般原域可加性及更广量子消费者的桥仍未支付。原 $\Omega$/native、全词与父位置、全部准备和效果菜单、共同记录与真实分组、完整仪器及所有输出、实际复合与参考、全部合法历史和未来、停止拒绝销毁、真实返回、无限或非离散计数、正常性与前对偶、物理钟、能量和共同作用量尺度 $\hbar$ 均保持原来源义务。

**定义 2.4（完整白话）。** 这里把同一个有单位的多项式世界当作原输入域，响应故意取零，所以所有正表、三点零关系、正反平方配平、双线性和换括号都确实成立。可是把一个原输入演员写成完成复化中的 Cayley 变换后，分母和分子产生两条互素的多项式因子；要让一次、两次直到任意多次的结果都回到原多项式域，初始多项式必须含有任意高次的分母因子，非零多项式做不到。每个有限长度仍可用相应有限次分母因子开头的多项式实现，所以被排除的是“所有未来都返回原域”的非零核心，而不是有限步骤。这个有两个输入槽的无限维空间只是标签的几何；它没有制造物理空间、准备、仪器、联合、参考、历史、真实返回、计数、时钟、能量或作用量。该边界说明完整 P2 与 PB 即使已经伴随 $D$ 的双线性和 $R$，也不足以把完成上的 Cayley 公式自动解释成原域上的非零群作用；一般任意 JB 原域的平移、纤维、可加性和量子起源桥仍须由原条件另行证明。

## 3. 同一原生成元的全部多项式零响应

**定理 3.1（任意 JB 完成中的原多项式零值）。** 沿用配平主卷定义 128.1、183.1 的同一原 $E,C,u,N,\mathcal P,S,D$、原 A1–A3 及其无 R 的 Jordan 接口：$E$ 是任意含单位实 JB 完成 $X$ 中的含单位范数稠密实 Jordan 子代数，$C=E\cap X_+$，原评价分离并准确决定原锥。对同一个总映射 $D:E^2\to E$，只取原 P2（配平主卷式 (128.3)）和完整 PB（配平主卷式 (128.4)），保留全部原评价、零／不等／次归一质量及来源量词。则对每个原 $x\in E$ 和任意两个实系数多项式 $p,q\in\mathbb R[T]$，有

$$
\boxed{D(p(x),q(x))=0.}
\tag{3.1}
$$

其中 $x^0=u$，其余为 Jordan 幂。这里不要求有限谱、原域完备、原根／逆／投影闭合或一般 JB 的特殊表示；不预设 $D$ 的可加、齐次、连续、可测、协变或完成延拓。

证明。直接复用配平主卷 §§183–184 的全单位行及配平主卷定义 185.1 的 SO$(2)$ 标签旋转、每槽奇性和同轴仿射零行，不重证这些前置。单生成 Jordan 幂的成熟幂结合律给

$$
x^j\circ x^k=x^{j+k}\quad(j,k\ge0),\qquad
\mathcal A_x=\mathbb R[x]=\{f(x):f\in\mathbb R[T]\}\subset E
\tag{3.2}
$$

为含单位交换结合实代数。具体出处是 van de Wetering，[*Commutativity in Jordan Operator Algebras*，arXiv:1912.01903v1](https://arxiv.org/html/1912.01903v1)，Corollaries 2.9–2.10；零次幂由单位律补入。这里只使用这个原子代数的已知 Jordan 乘法，未给未知 $D$ 添加任何线性。特别，实多项式求值保持加法、实数乘法和乘积；这三项是已知求值映射的性质。

对形式多项式 $H=h+\mathrm i k\in\mathbb C[T]$，其中 $h,k\in\mathbb R[T]$，记

$$
\Phi_x(H)=D(h(x),k(x)).
$$

$\overline H$ 表示系数逐个取共轭。复数在此只记录两个原实标签；需要乘法时只在已知结合代数的代数复化 $\mathcal A_x+\mathrm i\mathcal A_x$ 中计算，$D$ 从不接收复输入。配平主卷式 (185.1) 准确给出

$$
\Phi_x(e^{\mathrm i\theta}H)=\Phi_x(H),\qquad
\Phi_x(-H)=\Phi_x(H),\qquad
\Phi_x(\overline H)=-\Phi_x(H).
\tag{3.3}
$$

第一式是实际标签旋转；第三式只用第二槽奇性。这些等式不宣称 $\Phi_x$ 对加法或任意复数乘法线性。

约定形式零多项式的次数为 $-\infty$。对 $n=\max(\deg p,\deg q)$ 归纳，次数始终指所给形式多项式，不能用求值后的关系暗中降次。$n\le1$ 时，两标签都在 $\operatorname{span}_{\mathbb R}\{u,x\}$，由配平主卷定义 185.1 的仿射零行得结论，包含两个常数、一个或两个零多项式。设 $n\ge2$，且所有次数至多 $n-1$ 的实多项式对已经成立。固定当前 $p,q$，置 $P=p+\mathrm i q$。因最高次的实部与虚部不能互相抵消，$\deg P=n$。由普通复标量多项式的代数基本定理，写成

$$
P(T)=\kappa\prod_{\ell=1}^{n}(T-z_\ell),\qquad
\kappa\in\mathbb C\setminus\{0\}.
\tag{3.4}
$$

这里根按重数逐个占据一个索引位置，允许重复根及实根。令 $I=\{\ell:\operatorname{Im}z_\ell\ne0\}$，将这个有限索引集列为 $i_1,\ldots,i_m$，$0\le m\le n$。定义 $z_\ell^{(j)}$：若 $\ell\in\{i_1,\ldots,i_j\}$ 就取 $\overline{z_\ell}$，否则取 $z_\ell$，并置

$$
P_j(T)=\kappa\prod_{\ell=1}^{n}(T-z_\ell^{(j)})
\quad(0\le j\le m).
\tag{3.5}
$$

每步只改一个指定位置的非实根，首项系数始终是同一个 $\kappa$。即使两个根相同，或一对根本来互为共轭，也分别处理其索引位置，不约去或识别不同位置。

固定第 $j$ 步，$1\le j\le m$，记尚未改变的该根 $z_{i_j}=r_j+\mathrm i t_j$，其中 $r_j,t_j\in\mathbb R$、$t_j\ne0$。取形式多项式和原标签

$$
\begin{aligned}
a_j(T)&=(T-r_j)/t_j,\\
W_j(T)&=-\mathrm i t_j\kappa
       \prod_{\ell\ne i_j}(T-z_\ell^{(j-1)}),\\
A_j&=a_j(x),\qquad
B_j=(\operatorname{Re}W_j)(x),\qquad
C_j=(\operatorname{Im}W_j)(x).
\end{aligned}
\tag{3.6}
$$

$A_j,B_j,C_j$ 全在原 $\mathcal A_x$。$\deg a_j=1\le n-1$，$\deg W_j=n-1$，其实部、虚部的次数均至多 $n-1$；其中任一实部或虚部可以为零。因此归纳假设确实支付两个实际内层值

$$
D(A_j,B_j)=D(A_j,C_j)=0.
\tag{3.7}
$$

现在只调用原三元组 $(A_j,B_j,C_j)$ 的完整 PB 元素式（配平主卷式 (128.6)）。此时 $v=-A_j\circ C_j$、$w=A_j\circ B_j$，右端准确为

$$
2B_j\circ(A_j\circ C_j)-2C_j\circ(A_j\circ B_j)=0,
$$

因为三者都属于已知结合的 $\mathcal A_x$。故两个实际外层值满足

$$
D(B_j-A_j\circ C_j,\ C_j+A_j\circ B_j)
=D(B_j+A_j\circ C_j,\ C_j-A_j\circ B_j).
\tag{3.8}
$$

没有展开这些未知外层响应。它们的两标签记录分别是 $(u+\mathrm i A_j)(B_j+\mathrm i C_j)$ 和 $(u-\mathrm i A_j)(B_j+\mathrm i C_j)$。在形式多项式中直接有

$$
\begin{aligned}
(1+\mathrm i a_j(T))(-\mathrm i t_j)&=T-z_{i_j},\\
(1-\mathrm i a_j(T))(-\mathrm i t_j)&=-(T-\overline{z_{i_j}}).
\end{aligned}
$$

结合其余同一组因子，两个外层记录准确为 $P_{j-1}(x)$ 和 $-P_j(x)$。所以 (3.8) 及已付的同时反号旋转给

$$
\Phi_x(P_{j-1})=\Phi_x(-P_j)=\Phi_x(P_j).
\tag{3.9}
$$

有限次改变所有非实根后，实根本身不变，故普通标量多项式恒等式给

$$
P_m=\frac{\kappa}{\overline\kappa}\,\overline P,
\qquad \left|\frac{\kappa}{\overline\kappa}\right|=1.
$$

这个标量是某个 $e^{\mathrm i\theta}$。由 (3.3) 和整条 (3.9)，

$$
\Phi_x(P)=\Phi_x(P_m)=\Phi_x(\overline P)=-\Phi_x(P).
\tag{3.10}
$$

$E$ 是实向量空间，因而 $\Phi_x(P)=0$，归纳完成。若 $m=0$，没有 PB 步骤，$P_0=P=(\kappa/\overline\kappa)\overline P$ 本身就给同一端点反号，仍然成立。实根从不造成除法；重复非实根只被逐次反射，唯一的除法是除以非零实标量 $t_j$ 及非零复标量 $\overline\kappa$。没有在 $E$ 中求根、求逆或约去某个多项式因子。

即使求值映射有核、$x$ 满足代数关系、$p(x)$ 或 $q(x)$ 为零，以上形式次数下降及原调用仍全部有效；$x$ 为标量单位倍数、线性窗口退化和零代数也包含在结论内。所有内层和外层标签只由原线性组合及原 Jordan 乘法生成。证明不使用未知 $D$ 的齐次性、可加性、连续性、输入极限、额外根／逆／投影闭合、共同实现者或完成上的新 $D$。∎

**直接消费者。** 若原 $a=p(x),b=q(x)$ 共用一个原多项式生成元，则对彼此独立的任意 $s,t\in\mathbb R$，将定理用于 $p+s,q+t$，得到实际原单位铅笔 $d_{a,b}(s,t):=D(a+su,b+tu)=0$；特别，对完全任意原 $a\in E$、实数 $s$ 及实多项式 $p$，以生成元 $x=a$、两个多项式 $T+s,p(T)$ 得 $D(a+su,p(a))=0$。因此比较任意 $a$ 与 $a+\lambda u$ 时，每个原 $c=p(a)$ 都是两者共同的零辅助行。这只支付这些实际零值；一般混合演员 PB 的外层响应仍须按其真实输入比较，未由此消去它们的残差。

**定义 3.2（最小线性窗口与原多项式并）。** 对所选输入对 $p(x),q(x)$，包含单位及这两个输入的最小实线性空间准确为 $V_{p,q}(x)=\operatorname{span}_{\mathbb R}\{u,p(x),q(x)\}$，维数至多三。它未必包含 $x$，亦未必对 Jordan 乘法闭合；证明中的辅助标签不必留在这个窗口。超过配平主卷定义 185.1 仿射范围的首个完整次数窗口是 $V_2(x)=\operatorname{span}_{\mathbb R}\{u,x,x^2\}$，同样至多三维，且是包含这三个指定标签的最小线性空间。若 $x^2\in\operatorname{span}\{u,x\}$，它退化而没有第三个独立方向；若 $x^3\notin V_2(x)$，则 $x\circ x^2=x^3$ 已证明它不闭合。本卷定义 2.1 的坐标元 $\tau$ 就有后一性质，因为区间上的多项式恒等式不可能把 $T^3$ 表为二次多项式。更大的共同结构是

$$
V_n(x)=\operatorname{span}_{\mathbb R}\{u,x,\ldots,x^n\},\qquad
\mathcal A_x=\bigcup_{n\ge0}V_n(x).
\tag{3.11}
$$

这个并对乘法闭合，因为 $V_j(x)\circ V_k(x)\subseteq V_{j+k}(x)$，并由幂结合律成为原域中的交换结合子代数。它可以无限维且不完备。上述至多三维窗口是输入标签的线性几何，不是物理三空间；标量根的共轭是有限因子的代数操作，不生成物理投影、测量或返回。

**失败判据及其证明。** 在相同 Jordan 接口上，任何保留配平主卷定义 185.1 全部对称性及仿射零行、却在某个 $\mathcal A_x$ 上响应非零的总映射，都必违反某一次有限原 PB。事实上，取形式次数最小的非零多项式响应，其次数至少为二；所有 (3.7) 已由最小性成立，端点又由对称性反号，故若有限链中每个原 PB 都成立就会得到 (3.10) 的矛盾。于是至少一份明确形如 (3.6) 的原三元组不能满足其 PB。这是较弱条件候选的排除判据，没有提供完整 P2+PB 的反模型。在真正满足完整 P2+PB 的总模型中，任何非零单位平移缺陷 $D(a+\lambda u,b)-D(a,b)$ 都要求不存在原 $x$ 与实多项式 $p,q$ 使 $a=p(x),b=q(x)$，否则直接消费者使两项同时为零。

**定义 3.3（来源、原目标与完整来源边界）。** (3.1) 的有限根共轭归纳归为 $\texttt{repo-derived}$；承重前置是原 PB 元素式（配平主卷式 (128.6)）与配平主卷定义 185.1，配平主卷 §§183–184 的一般全单位行只作复用。单生成幂结合的准确成熟来源是上述 van de Wetering Corollaries 2.9–2.10；复标量多项式的有限因子分解及系数共轭为普通代数基本定理的成熟工具，不是原 $E$ 的根闭合假设。不主张历史优先权或文献穷尽。配平主卷 §§200–215 的面积、Peirce 圆及标量平方结果保持其指定复 C* 前件，不被用来预付一般 JB 的特殊性；配平主卷 §§216–222 的正交响应平方细化保留其定义 216.1 的指定复载体包含前件，不要求 $X=A_{\rm sa}$，也不由此覆盖任意 JB 的全部原多项式对；配平主卷 §§223–228 的单一非标量 Gram 坐标、共同加权三轴响应及完整外层预算接口也保持各自指定复 C* 前件，并保留径向、可加性与一般 JB 桥，不被用作本定理的前提；配平主卷 §§229–234 的非零共享平方、非负缺陷、缺陷为零的准确径向等价和有限预算限制也各按其指定复 C* 前件复用，并未补齐一般径向、可加性或一般 JB 桥，也未覆盖本定理的任意原多项式对；它们不作为本定理的前提。本卷 §2 的 Cayley 全前向边界保持其指定模型与量词。

一般跨轴单位平移 $\mathsf T$（配平主卷式 (185.2)）、纯态输入作用纤维 $\mathsf F$（配平主卷式 (178.2)）、原 $D$ 的分别可加／实双线性及原 $R$（配平主卷式 (128.5)） 仍未由此证明。配平主卷定理 179.1 的 $\mathsf F\Longleftrightarrow$ 实双线性只在配平主卷定义 178.1 明定的完整复 C* 自伴载体上使用；一般 JB 到该载体且保持同一旧关系的桥仍须支付。配平主卷定义 180.1 与静态重构卷 32–33 的全有限正表、同一结合乘法 $\star=\circ-\mathrm iD$、Hilbert 表示及其量子消费者继续保留各自前件。本条不把一般混合演员的四次外层调用残差置零，也不从 $b\circ h=0$ 推出 $h=0$。任意两个原输入未必有共同原多项式生成元；任意通勤对未被本定理全部覆盖。也未由稠密性将零值运送到连续或 Borel 函数，因为未知 $D$ 的这种输入运输性质尚未证明。独立公理条件数不变，没有增加额外公理。

原 $\Omega/\mathrm{native}$、全词 $K/J/q$、父位置和 ready 类型、原中心与不等维块、全部零／不等／次归一质量、实际准备与完整效果菜单、共同记录与真正分组遗忘、全仪器及其环境和全部输出、实际相关联合与递归同源参考、全部合法顺序／自适应／并行历史及每个仍合法未来、停止／拒绝／销毁、同数两侧与真实逆向返回，均保留配平主卷定义 128.1 的原来源和量词。数学多项式与因子操作不供应这些实际来源。Born 比例仍只用于原实际完整菜单及严格正质量 $\alpha(e_r)/m_\alpha$，零质量不归一；完整 CountRead 无穷、非离散记录、可数可加、正常性与前对偶、物理钟、能量、作用量及共同 $\hbar$ 均守原来源义务。

**定义 3.4（完整白话）。** 两个原输入只要都是同一个原对象的实多项式，它们在同一份旧响应下就必为零，各自独立加上任意单位倍数也仍为零。证明先把两个多项式记成一个复多项式，复数只帮助记录两个实标签。按照形式次数归纳，每次挑出一个非实标量根，把它换成共轭根；其余因子给出两个低一次的原标签，所挑根则给一个原仿射演员。归纳已经证明演员与两个低次标签之间的响应为零，所以可以真正调用这一次原配平。已知的单生成 Jordan 乘法是结合的，使配平右侧准确抵消，从而换根前后同一个实际外层响应保持不变。有限次处理完所有非实根，末端却成为原标签对的整体旋转加第二槽反号；响应既要保持又要反号，只能为零。实根不需改变，重根按出现次数逐个处理，常数、零输入及所有退化情形都包含，不需在原域里开根或求逆，也不拆开未知响应。

对任一输入对，单位和两个标签张成的最小线性窗口至多三维；首个新的次数窗口由单位、原对象和它的平方张成，但乘起来可能走到三次方而离开窗口。全部有限次数窗口的并才是原域中的结合多项式代数，它可以无限维且不完备；这不是物理三维空间。对任意对象及它加单位后的对象，现在有整族共同的多项式零辅助行，但面对另一个一般对象，混合配平的外层值仍未被消去。因此一般单位平移、输入作用纤维、可加性和原换括号关系的主缺口继续保留，已有量子推导仍等待这些前件。实际准备、完整菜单、仪器全部输出、联合与参考、全部合法历史未来和真实返回，以及计数、物理钟、能量和共同作用量，仍须由同一原世界供应。

## 追加锚（本行以下为增补区）

## 4. 任意 JB 同态像中的原标量行吸收

**定义 4.1（同态只读取已知结构）。** 保持定义 1.1 的同一原 $E,C,u,N,\mathcal P,S,D$、原 A1–A3、准确锥、全部原 P2 与完整 PB。取含单位实 JB 代数 $Y$ 及连续含单位 Jordan 同态

$$
q:X\longrightarrow Y,\qquad \overline{q(X)}^{\|\cdot\|}=Y.
\tag{4.1}
$$

于是 $q(E)$ 在 $Y$ 中范数稠密。$q$ 只保持已知实线性、单位及 Jordan 乘法；不在 $q(E)$ 上定义响应，不将同像原代表视为可互换。Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，Proposition 3.4.3（印刷页 85）还给 $q(X)$ 闭，故这里 $q$ 实际满射；$q(E)$ 则不要求满射。任意同态的闭含单位 JB 像均可作为这里的 $Y$。零目标单独按零映射处理。

若 $\beta$ 是 $Y$ 上数学正实线性泛函，则 $\beta\circ q|_E$ 在原准确锥上正，故配平主卷引理 129.1 使其读取每张实际原 P2；PB 的原元素等式亦可由它读取。准确预算是

$$
|\beta(qD(v,w))|^2
\le \beta((qv)^2)\beta((qw)^2)-\beta(qv\circ qw)^2
\qquad(v,w\in E).
\tag{4.2}
$$

这种拉回是数学读取，不增加实际准备或改变其质量。尤其 $qv=0$ 使第一对角为零，所有正 $\beta$ 都读到 $qD(v,w)=0$；正泛函分离 $Y$ 给

$$
qv=0\quad\Longrightarrow\quad qD(v,w)=0.
\tag{4.3}
$$

反对称性处理第二槽。这个零像吸收是配平主卷 241.1 的零对角机制在任意 JB 像中的直接应用，不包含 $qD(v+k,w)=qD(v,w)$ 的一般纤维断言。

**定理 4.2（一般标量像吸收）。** 在定义 4.1 的全部原域上，对任意原 $a,b\in E$、任意 $\mu\in\mathbb R$，有

$$
\boxed{q(a)=\mu1_Y\quad\Longrightarrow\quad qD(a,b)=0.}
\tag{4.4}
$$

$E$ 可以无限维、不可分且不完备，$X$ 与 $Y$ 无须有非零最小投影；没有原谱投影、原根或原逆元闭合的前件。

证明。$Y=0$ 时直接成立；$\mu=0$ 由 (4.3)。以下固定 $\mu\ne0$，记真正的原输出及其数学像

$$
H=D(a,b)\in E,\qquad B=q(b),\qquad h=q(H).
$$

先证明第二输入像半定时的结论。若 $h\ne0$，同书 Lemma 3.6.8（页 89）的范数支撑态给状态 $\beta$，令 $Z=\beta(h)$，满足 $|Z|=\|h\|>0$。由 Schwarz 不等式和 $h^2\le\|h\|^2 1_Y$，

$$
\beta((h-Z1_Y)^2)=0.
\tag{4.5}
$$

选择实际比例标签 $c=ka\in E$，其中 $k=Z/(1+\mu^2)$。原比例零值给 $D(a,c)=0$。在原 PB $(a,b,c)$ 中，保留实际外层 $r_\pm,s_\pm$；其像为

$$
\begin{aligned}
R_\pm:=q(r_\pm)&=B\pm h\mp k\mu^2 1_Y,\\
S_\pm:=q(s_\pm)&=k\mu1_Y\pm\mu B,\\
S_+-\mu R_+&=S_-+\mu R_-=\mu(Z1_Y-h).
\end{aligned}
\tag{4.6}
$$

在半内积 $\langle v,w\rangle_\beta=\beta(v\circ w)$ 中，(4.5) 使两组像向量分别成比例。因此 (4.2) 使两个实际外层输出的 $\beta\circ q$ 读取都为零。PB 右端的像准确为

$$
-2B\circ(h-k\mu^2 1_Y)-2k\mu1_Y\circ(\mu B)
=-2B\circ h.
$$

又由 (4.5) 的 Schwarz 不等式，$\beta(B\circ h)=Z\beta(B)$，故 $Z\beta(B)=0$。若 $B\ge0$ 或 $B\le0$，则 $\beta(B)=0$ 及 $0\le B^2\le\|B\|(\pm B)$ 给 $\beta(B^2)=0$。原 $(a,b)$ 的 (4.2) 随即给 $Z=0$，矛盾。于是已经证明

$$
q(c)\in Y_+\cup(-Y_+)\quad\Longrightarrow\quad qD(a,c)=0
\qquad(c\in E).
\tag{4.7}
$$

现在处理一般 $B$。只为数学读取，取 $M=Y^{**}$，将 $\beta\in Y^*$ 正常延伸到 $M$。同书 Theorem 4.4.3（页 104）供应此 JBW 结构。Hamhalter，[*Pure states on Jordan algebras*](https://dml.cz/bitstream/handle/10338.dmlcz/133911/MathBohem_126-2001-1_7.pdf)，Mathematica Bohemica 126 (2001)，81–91，§1 页 82–83，供应每个纯态的最小非零支撑投影 $p\in M$，满足 $U_p(v)=\beta(v)p$；由正常性和弱星稠密性，该式从 $Y$ 延至 $M$。这里 $U_v=2L_v^2-L_{v^2}$，$L_vw=v\circ w$。

固定满足 $\beta(h)\ne0$ 的纯态，令

$$
K=\frac{\mu h}{1+\mu^2},\qquad r=\beta(K)\ne0,
\qquad C_0=\frac{U_K(p)}r\in M.
\tag{4.8}
$$

$U_K$ 保正，故 $C_0$ 按 $r$ 的符号半定。最小支撑给 $M_1(p)=\mathbb Rp$、$\beta(p)=1$、$\beta=\beta\circ U_p$。将 $K=rp+v+w$ 按 Peirce 特征值 $1,1/2,0$ 分解；同书 Lemma 2.6.3（页 48）的乘法规则给

$$
U_K(p)=r^2p+rv+(v^2)_0,\qquad
C_0-K=(v^2)_0/r-w\in M_0(p).
\tag{4.9}
$$

所以 $\beta((C_0-K)^2)=0$。支撑、$C_0$ 及其根都只用于已知 Jordan 结构，不输入 $D$。

同书 Lemma 4.1.9（页 96–97）给有界集上乘法联合强连续性；Theorem 4.5.12（页 115）的 Kaplansky 密度给有界强逼近。具体地，$Y$ 在 $M$ 中弱星稠密，弱与强拓扑在凸集上有相同闭包，故 $Y$ 强稠密；再用 $q(E)$ 在 $Y$ 中范数稠密，可以选择实际原 $e_i\in E$，使 $q(e_i)$ 一致范数有界且强收敛到 $|C_0|^{1/2}$。这里不要求提升 $e_i$ 在 $X$ 中范数有界。令

$$
c_i=\operatorname{sgn}(r)e_i^2\in E,\qquad C_i=q(c_i).
$$

于是 $C_i$ 一致有界、半定并强收敛到 $C_0$。(4.7) 已经支付 $qD(a,c_i)=0$。定义

$$
\delta_i=(1+\mu^2)C_i-\mu h,\qquad
\varepsilon_i=\beta(\delta_i^2)^{1/2}\longrightarrow0.
\tag{4.10}
$$

最后的收敛由 $\delta_i\to(1+\mu^2)(C_0-K)$ 强收敛及 (4.9) 的零平方读取得到。

对每个 $i$，完整 PB 仍准确使用原标签

$$
\begin{aligned}
r_\pm^{(i)}&=b\pm H\mp a\circ c_i,\\
s_\pm^{(i)}&=c_i\pm a\circ b\pm D(a,c_i).
\end{aligned}
\tag{4.11}
$$

即使 $qD(a,c_i)=0$，也不在这些原标签里删除 $D(a,c_i)$。仅在计算像时，得

$$
\begin{aligned}
R_\pm^{(i)}&=B\pm h\mp\mu C_i,&
S_\pm^{(i)}&=C_i\pm\mu B,\\
S_+^{(i)}-\mu R_+^{(i)}
&=S_-^{(i)}+\mu R_-^{(i)}=\delta_i.
\end{aligned}
\tag{4.12}
$$

给第二向量加第一向量的实倍数不改实 Gram 行列式。故每张实际外层 P2 分别给

$$
|\beta(qD(r_\pm^{(i)},s_\pm^{(i)}))|
\le\beta((R_\pm^{(i)})^2)^{1/2}\varepsilon_i
\le M_0\varepsilon_i,
\tag{4.13}
$$

其中 $M_0<\infty$ 只依赖 $B,h,\mu$ 和 $C_i$ 的一致像范数界。PB 右端的像却始终是固定元素

$$
-2B\circ(h-\mu C_i)-2C_i\circ(\mu B)=-2B\circ h.
$$

于是 $2|\beta(B\circ h)|\le2M_0\varepsilon_i$，从而 $\beta(B\circ h)=0$。若这个固定读取非零，一个足够准确的实际 $c_i$、一次原 PB 和两张原 P2 就已给出矛盾；没有对任何变动的未知输出取极限。

若纯态 $\beta(h)=0$ 且 $\beta(h^2)=0$，Schwarz 不等式直接给 $\beta(B\circ h)=0$。若 $\beta(h)=0$ 而 $\beta(h^2)>0$，则对足够小的非零实 $t$，$1_Y+th$ 正且可逆。$U_{1_Y+th}$ 是正锥自同构，其对偶保持正极射线，故

$$
\beta_t(v)=\frac{\beta(U_{1_Y+th}v)}{\beta((1_Y+th)^2)}
$$

仍为纯态。二次表示的保正性及逆来自同书 Proposition 3.3.6、§3.2.10（页 83、96 的引用）。已知单生成演算和 $\beta(h)=0$ 给

$$
\beta_t(h)=\frac{2t\beta(h^2)+t^2\beta(h^3)}{1+t^2\beta(h^2)}\ne0
\tag{4.14}
$$

对足够小的非零 $t$ 成立。已证情形使 $\beta_t(B\circ h)=0$；$U_{1_Y+th}=I+2tL_h+t^2U_h$ 使 $\beta_t\to\beta$ 范数收敛，所以固定元素仍读为零。纯态分离 $Y$，得到

$$
B\circ h=0.
\tag{4.15}
$$

这只是读取的变形，不是实际准备或原输入的变形。

下一步取得第二张固定表。准确调用原 PB $(b,a,\mu b)$，比例零值给 $D(b,\mu b)=0$，反对称性给 $D(b,a)=-H$。定义实际原标签

$$
x=a-H-\mu b^2,\qquad y=\mu b+b\circ a,
\qquad x_-=a+H+\mu b^2,\qquad y_-=\mu b-b\circ a.
$$

$y_-$ 不必是原零，但 $q(y_-)=0$，所以只能由已经证明的 (4.3) 消去 $qD(x_-,y_-)$。PB 右端的像为

$$
2\mu h+2\mu^2B^2-2\mu^2B^2=2\mu h.
$$

因而两张固定实际表的像准确为

$$
\begin{array}{c|c|c}
\text{第一输入像}&\text{第二输入像}&\text{旧输出像}\\ \hline
\mu1_Y&B&h\\
X_0:=\mu(1_Y-B^2)-h&Y_0:=2\mu B&2\mu h
\end{array}
\qquad qD(x,y)=2\mu h.
\tag{4.16}
$$

这些不是在像上定义的新表函数，只是两次固定原调用的三个像。

令 $J=\operatorname{JB}(1_Y,B,h)\subseteq Y$。同书 Theorem 7.2.5（页 156），亦见 van de Wetering，[*Commutativity in Jordan Operator Algebras*](https://arxiv.org/html/1912.01903v1)，Theorem 3.5，给两生成 $J$ 的忠实含单位 JC 表示。正锥由单生成谱演算准确保留。(4.15) 在其生成的复 C* 环境中成为 $Bh=-hB$，所以 $B^2$ 与 $h$ 交换。两张固定表的每个 P2 二次型像都属于 $J\cap Y_+=J_+$，因此环境中的向量态可合法读取它们；若需要拉回到整个 $Y$，这些 $J$ 上正泛函由序单位 Hahn–Banach 正延拓得到。这里只读取 (4.16) 的固定调用，不要求其他原调用的输出像属于 $J$。

取交换 C* 子代数 $C^*(1_Y,B^2,h)$ 的任意字符 $\chi$，记 $t=\chi(B^2)\ge0$、$z=\chi(h)$。$z=0$ 已满足所需谱关系。若 $z\ne0$，将字符延为环境 C* 态；其 GNS 循环单位向量 $\xi$ 满足 $h\xi=z\xi$、$B^2\xi=t\xi$。第一张表给 $|z|\le|\mu|\sqrt t$，故 $t>0$。反交换给 $hB\xi=-zB\xi$，所以 $\xi$ 与 $B\xi/\sqrt t$ 正交。它们张成的二维不变空间上，

$$
B=\sqrt t\,\sigma_x,\quad h=z\sigma_z,\quad
X_0=\mu(1-t)I-z\sigma_z,\quad Y_0=2\mu\sqrt t\,\sigma_x.
$$

用实单位向量 $(\cos\theta,\sin\theta)$ 读第二张固定表，写 $\eta=\cos2\theta$。其旧输出读取为 $2\mu z\eta$，两个输入作用向量的有向面积为 $2\mu\sqrt t[\mu(1-t)\eta-z]$。故

$$
|z\eta|\le\sqrt t\,|\mu(1-t)\eta-z|
\quad(-1\le\eta\le1),\qquad |z|\le|\mu|\sqrt t.
\tag{4.17}
$$

为完整排除残余谱，令 $A_0=\mu(1-t)\ne0$。若 $0<|z|\le|A_0|$，取 $\eta=z/A_0$，右端零而左端非零。若 $|z|>|A_0|$，取 $\eta=\operatorname{sgn}(A_0z)$，得到 $|z|\le\sqrt t(|z|-|A_0|)$。$t<1$ 时右端严格小于左端；$t>1$ 时则推出

$$
|z|\ge\frac{\sqrt t|A_0|}{\sqrt t-1}
=|\mu|\sqrt t(\sqrt t+1),
$$

违反 (4.17) 的第二界。因此非零 $z$ 只能位于 $t=1$。字符分离交换子代数，包括 $t=0,z=0$ 的退化情形，给

$$
(B^2-1_Y)\circ h=0.
\tag{4.18}
$$

还需排除 $t=1$ 上的残余，不能由 (4.15) 单独断言 $h=0$。取实际原 $d=D(y,x)$、$g=y\circ x$。由 (4.16) 及已知乘法，

$$
q(d)=-2\mu h,\qquad G:=q(g)=2\mu^2(B-B^3).
$$

在上述 JC 环境中，(4.15)、(4.18) 给 $Gh=hG=0$，故 $U_h(G^2)=0$；并有 $X_0\circ h=-h^2$。最后准确调用原 PB $(y,x,0)$：

$$
D(x+d,g)-D(x-d,-g)=-2x\circ d.
\tag{4.19}
$$

对任意 $Y$ 上正 $\rho$，$\phi=\rho\circ U_h\circ q|_E$ 是数学正读取。两个实际外层 P2 的第二对角均为 $\phi(g^2)=\rho(U_h(G^2))=0$，故两输出的 $\phi$ 读取均为零。(4.19) 于是给

$$
0=4\mu\rho(U_h(X_0\circ h))
=-4\mu\rho(h^4).
\tag{4.20}
$$

全部正 $\rho$ 分离正锥，故 $h^4=0$；JB 范数恒等式给 $\|h\|^4=\|h^4\|=0$。于是 $h=0$。所有未知调用从头至尾只接收实际原 $E$ 标签；既未构造商响应，也未使用它的输入连续性。∎

## 5. 仿射像、闭理想与原中心的零行

**推论 5.1（仿射比例像与逐理想约束）。** 在定义 4.1 下，对任意原 $a,b$ 及实 $\kappa,\mu$，有

$$
q(a)=\kappa q(b)+\mu1_Y\quad\Longrightarrow\quad qD(a,b)=0.
\tag{5.1}
$$

特别，对任意闭 Jordan 理想 $I\lhd X$，

$$
a-\kappa b-\mu u\in I\quad\Longrightarrow\quad D(a,b)\in I.
\tag{5.2}
$$

若 $I_{\kappa,\mu}$ 是由 $a-\kappa b-\mu u$ 生成的最小闭 Jordan 理想，则

$$
D(a,b)\in\bigcap_{\kappa,\mu\in\mathbb R}I_{\kappa,\mu}.
\tag{5.3}
$$

证明。对真正的原标签作配平主卷定义 185.1 已付的 SO$(2)$ 旋转，取 $\cos\theta=(1+\kappa^2)^{-1/2}$、$\sin\theta=\kappa(1+\kappa^2)^{-1/2}$。旋转后的第一标签像为 $\mu(1+\kappa^2)^{-1/2}1_Y$，同一个实际旧响应由旋转保持，故定理 4.2 给 (5.1)。这没有使用未知 $D$ 的齐次性。对真商 $q_I:X\to X/I$ 应用 (5.1) 即得 (5.2)；闭商为 JB 的准确来源是 Hanche-Olsen–Størmer Theorem 3.4.2（页 85）。$I=X$ 时结论直接成立。逐个取 $I=I_{\kappa,\mu}$ 得 (5.3)。这些是任意原代表的受限相容性，并非一般商纤维不变性。∎

**推论 5.2（中心像模任意闭理想的零行）。** 在同一原完整候选下，对任意闭 Jordan 理想 $I\lhd X$，若原 $a\in E$ 满足 $q_I(a)\in Z(X/I)$，则

$$
D(a,b)\in I\qquad(b\in E).
\tag{5.4}
$$

这里 $Z(Y)=\{z\in Y:[L_z,L_y]=0\text{ 对所有 }y\in Y\}$ 是 Jordan 算子中心。特别，$z\in E\cap Z(X)$ 给 $D(z,b)=0$；若原 $x\in E$ 的 $q_I(x)$ 中心，则任意实多项式 $p$ 和任意原 $b$ 满足 $D(p(x),b)\in I$。

证明。先支付商的载体，而不假设旧响应下降。配平主卷定理 247.1 已排除 $X$ 的满 Albert 商。若 $Y=X/I\ne0$ 有满 Albert 商，复合 $q_I$ 就给 $X$ 的同一禁商，故 $Y$ 也没有满 Albert 商。同书 Lemma 7.2.2、Theorem 7.2.3、Theorem 7.2.5 的证明（页 155–156），连同 Corollary 4.5.8、Proposition 4.6.4（页 114、116），给成熟后果：非 JC 的 JB 代数有满 Albert 表示。具体地，非 JC 时存在非零纯例外闭理想；其非零因子表示满到 Albert，目标有限维因而为 JBW，理想表示遂延到整个代数且仍满射。因此 $Y$ 必有忠实、含单位、等距、锥准确的 JC 包含 $j_I:Y\to(A_I)_{\rm sa}$，其中 $A_I=C^*(j_I(Y))$；单位支撑压缩与锥反映按配平主卷 248.1 的已知表示论步骤处理。$I=0$ 时这正是该节已有的载体。

van de Wetering Proposition 3.2 给 JC 子代数中 Jordan 算子通勤与环境算子通勤的等价。因此 $j_I(q_I(a))$ 与每个 $j_I(y)$ 通勤，属于 $Z(A_I)$。取 $A_I$ 的任意不可约复 C* 表示 $\pi$；Schur 引理使

$$
\pi j_Iq_I(a)=\mu_\pi 1,\qquad \mu_\pi\in\mathbb R.
$$

将复合 $q_\pi=\pi\circ j_I\circ q_I$ 的目标准确取为其闭含单位 Jordan 像 $Y_\pi\subseteq B(\mathcal H_\pi)_{\rm sa}$。这是 JB 代数，$q_\pi$ 保单位且有稠密像；实际上像闭性仍由 Proposition 3.4.3 给出。定理 4.2 直接作用于原调用 $(a,b)$，给 $q_\pi D(a,b)=0$。不可约 C* 表示分离 $A_I$，$j_I$ 又单射，故 $q_I D(a,b)=0$，得到 (5.4)。全理想及零代数情形无需选表示。中心对实多项式闭合，且 $p(x)\in E$，所以最后的多项式后果成立。这里没有在 $Y$ 上建立总响应，更没有用它套中心行定理。∎

## 6. 四份独立平方根预算的严格正下确界

**定义 6.1（共同多项式辅助行的带符号比较）。** 对任意原 $a,b$、实 $s$，令 $\tau\in\{0,s\}$，记

$$
a_\tau=a+\tau u,\qquad d_\tau=D(a_\tau,b),\qquad
\delta=d_s-d_0.
$$

取原 $c=p(a)$，$p\in\mathbb R[T]$。定理 3.1 已支付 $D(a_\tau,c)=0$。准确外层及其带符号差记为

$$
\begin{aligned}
R_{\tau,\pm}&=b\pm d_\tau\mp(a_\tau\circ c),&
S_{\tau,\pm}&=c\pm(a_\tau\circ b),\\
\mathcal B_\tau(c)
&=D(R_{\tau,+},S_{\tau,+})-D(R_{\tau,-},S_{\tau,-}).
\end{aligned}
\tag{6.1}
$$

原 PB 直接给

$$
\begin{aligned}
\mathcal B_\tau(c)
&=-2b\circ d_\tau
 +2\bigl[b\circ(a_\tau\circ c)-c\circ(a_\tau\circ b)\bigr],\\
\mathcal B_s(c)-\mathcal B_0(c)&=-2b\circ\delta.
\end{aligned}
\tag{6.2}
$$

第二式中 $s$ 的两个已知项准确抵消；未在任何未知输入和上展开 $D$。对正数学读取 $\beta$，定义

$$
\begin{aligned}
\Delta_{\tau,\pm}(c)
&=\beta(R_{\tau,\pm}^2)\beta(S_{\tau,\pm}^2)
  -\beta(R_{\tau,\pm}\circ S_{\tau,\pm})^2,\\
W_\beta(c)&=\sum_{\tau\in\{0,s\},\,\epsilon\in\{+,-\}}
                 \sqrt{\Delta_{\tau,\epsilon}(c)}.
\end{aligned}
\tag{6.3}
$$

和式按两个演员位置计数；$s=0$ 时即使标签重合也保留两次。四张独立 P2 加三角不等式只供应

$$
2|\beta(b\circ\delta)|\le W_\beta(c).
\tag{6.4}
$$

(6.1)–(6.4) 是现有原接口在当前消费者中的直接代入，不另计为新增刚性结论。下述模型也允许 $c$ 遍历整个共同零辅助行，而不仅是 $\mathbb R[a]$。

**命题 6.2（完整接口、无最小投影模型中的尖锐预算底）。** 存在同一个不完备原域、无非零最小 Jordan 投影的总 P2/PB 模型，使对每个 $s\ne0$，一份固定正数学读取满足

$$
\delta=0,\qquad
\inf_{c\in\mathbb R[a]}W_\beta(c)
=\inf_{\substack{c\in E:\ D(a,c)=0\\ D(a+su,c)=0}}W_\beta(c)
=2|s|>0.
\tag{6.5}
$$

这反驳的是以这四份独立预算普遍趋零为中间证书的证明步骤，不是单位平移或完整量子起源的反例。

证明。取 $t\in[0,1]$，定义

$$
\begin{aligned}
E&=\left\{F(t)=\sum_{k=0}^n t^k A_k:
                   A_k\in M_2(\mathbb C)_{\rm sa}\right\},\\
X&=C([0,1],M_2(\mathbb C))_{\rm sa},\qquad u=I,\\
F\circ G&=(FG+GF)/2,\qquad C=E\cap X_+,\qquad
D(F,G)=\frac{\mathrm i}{2}(FG-GF).
\end{aligned}
\tag{6.6}
$$

范数取限制的上确界算子范数。逐项 Weierstrass 逼近给 $E$ 在 $X$ 中稠密；连续非多项式 $|t-1/2|I$ 不属于 $E$，故这个稠密真子空间不完备。原评价取所有正点向量评价及其任意非负质量倍数，它们分离 $E$ 并准确决定 $C$，包括零、不等及次归一质量。任意固定原 $0<\theta\le1$ 保持不变。

逐点有 $F\circ G-\mathrm iD(F,G)=FG$，所以每张原 P2 就是两个向量 $F(t)\xi,G(t)\xi$ 的普通复 Gram 表。相加三表的实部是相同向量的实 Gram 表，相加指定向量给零，因此 A2 成立。$S(u,u)=u$，且 $0\le e\le\theta u$ 给 $e^2\le e$，故 A3 成立。由准确锥，所有数学正读取亦可读取这些 P2。

再核对所有原三元组的完整 PB。令 $Z=B+\mathrm iC$ 只记录两个原自伴标签，$A,B,C\in E$。使用 (6.6) 的同一符号，实际外层满足

$$
r_\pm+\mathrm i s_\pm=(u\pm\mathrm iA)Z,\qquad
r_\pm^2+s_\pm^2+2D(r_\pm,s_\pm)
=Z^*(u+A^2)Z.
\tag{6.7}
$$

两侧完全相同，故 PB 在 $E$ 中作为元素恒等式对全部原三元组成立，再由每份原评价读取。这里只在已知多项式复化中计算乘法，没有缩小 PB 的输入范围。

若 $p$ 是 $E$ 或 $X$ 中非零 Jordan 投影，连续整数值 $\operatorname{rank}p(t)$ 在连通区间上常数且非零。$p$ 与 $tp$ 都属于 $U_p(E)$（或 $U_p(X)$），并且实线性独立：$(\lambda+\nu t)p(t)=0$ 对全部 $t$ 成立只能有 $\lambda=\nu=0$。所以 $U_p(E)\ne\mathbb Rp$，$U_p(X)\ne\mathbb Rp$；原域和完成都没有非零最小 Jordan 投影。点纤维的矩阵投影不是这种全局最小投影。

取常值 Pauli 元

$$
a=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
b=\begin{pmatrix}0&-\mathrm i\\\mathrm i&0\end{pmatrix},\quad
z_0=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
\beta(F)=\frac12\int_0^1\operatorname{Tr}(F(t))\,dt.
\tag{6.8}
$$

$\beta$ 是固定忠实数学态，不认作新增实际准备。因为 $a\circ b=0$、$[a,b]=2\mathrm i z_0$，同一个总 $D$ 给 $d_\tau=-z_0$，所以 $\delta=0$。$a^2=u$，故每个 $c\in\mathbb R[a]$ 都形如 $ru+qa$，$r,q\in\mathbb R$。更一般，(6.6) 中 $D(a,c)=D(a+su,c)=0$ 恰好要求 $[a,c]=0$，因此每个这样的原标签准确写为

$$
c(t)=r(t)u+q(t)a,\qquad r,q\in\mathbb R[t].
\tag{6.9}
$$

这是 $a$ 的点态自伴通勤子空间；系数由 $r(t)=\operatorname{Tr}(c(t))/2$、$q(t)=\operatorname{Tr}(ac(t))/2$ 给出，确为实多项式，反向亦直接成立。

在实内积 $\langle F,G\rangle_\beta=\beta(F\circ G)$ 中，$z_0$ 是单位向量，并逐点正交于 $u,a,b$。对移位演员，

$$
S_{s,\pm}=c\pm sb,\qquad
R_{s,\pm}=R'_{s,\pm}\pm d_s,\qquad
R'_{s,\pm}=b\mp(a_s\circ c).
$$

因为 $a_s\circ c=(q+sr)u+(r+sq)a$，$d_s=-z_0$ 同时正交于 $S_{s,\pm}$ 和 $R'_{s,\pm}$，且 $\|d_s\|_\beta=1$。于是每个符号都准确给

$$
\begin{aligned}
\Delta_{s,\pm}(c)
&=\|S_{s,\pm}\|_\beta^2
 +\left(\|R'_{s,\pm}\|_\beta^2\|S_{s,\pm}\|_\beta^2
        -\langle R'_{s,\pm},S_{s,\pm}\rangle_\beta^2\right)\\
&\ge\|S_{s,\pm}\|_\beta^2
 =\int_0^1(r(t)^2+q(t)^2)\,dt+s^2
 \ge s^2.
\end{aligned}
\tag{6.10}
$$

括号非负仅用实 Schwarz 不等式。其余两份行列式也非负，故对整个共同零行的每个 $c$，无论次数、系数或范数，均有 $W_\beta(c)\ge2|s|$。

$c=0$ 是合法共同零辅助标签。此时 $S_{0,\pm}=0$，故 $\Delta_{0,\pm}=0$；而 $R_{s,\pm}=b\pm d_s$、$S_{s,\pm}=\pm sb$ 给

$$
\Delta_{s,\pm}(0)=2s^2-s^2=s^2.
$$

所以 $W_\beta(0)=2|s|$，两个下确界都达到这个值，得到 (6.5)。$s=0$ 时同一选择给零，尖锐正底仅针对 $s\ne0$。这个模型的 $D$ 已是显式双线性交换子，只用于检验一个普遍证明证书，未用来认回一般原候选的未知响应。∎

## 7. 同一旧关系的剩余比较与完整来源范围

**定义 7.1（承重关系与尚缺的带符号接头）。** 定理 4.2 的 $\texttt{repo-derived}$ 综合，将配平主卷 §§183–184 的原单位行机制和 §§241–242 的有限自旋像机制接到任意含单位 JB 同态像；新增量词是一般 $Y$、任意实际原代表及仅在像中有界的逼近。所列成熟 JB 支撑、二次表示、密度、同态与 JC 工具是中间前置，不另计为新增定理。推论 5.1–5.2 是它在仿射像、闭理想及中心像中的直接消费者；中心模理想额外消费配平主卷 247–248 的 Albert 障碍与成熟表示论，没有假设商响应。命题 6.2 的承重内容是当前 (6.1) 四次原调用消费者中的精确预算下确界，模型构造及普通 Gram/Pauli 计算不作历史优先权或文献穷尽声明。这里的结论为纸面数学推导，不是冻结真值或新增模型公理。

对定义 6.1 的一般原 $a,b,s$，即使所有多项式辅助行已知为零，仍未证明

$$
\beta\bigl(\mathcal B_s(c)-\mathcal B_0(c)\bigr)=0
\quad\text{对全部数学正读取 }\beta.
\tag{7.1}
$$

由 (6.2)，这与 $b\circ\delta=0$ 等价，任一合法共同辅助标签的该等式都支付同一个固定缺陷的这份 Jordan 读取。命题 6.2 表明，不能把普遍支付 (7.1) 的步骤设为四份无关联绝对预算的总和趋零，扩大到该模型的整个共同零行亦不够。沿这个消费者继续证明时，须保留四次实际旧输出间的符号或共同约束，而不是只让四个独立上界相加。(7.1) 本身尚未证明；即使取得 $b\circ\delta=0$，也仍需排除非零反交换残余，不能直接得到 $\delta=0$。

标量像吸收不比较一般非标量像的不同原代表；它不推出 $D(a+z,b)=D(a,b)$，即使 $z$ 是原单位倍数或原中心元。任意通勤对的零值、一般商下降、原域可加／齐次／连续、共同取向、$\mathsf F$、原 R 及与某个环境交换子的全域识别仍未由这些结论取得。本卷定理 3.1 的全部同生成元多项式零值和 §2 的完整前向 Cayley 边界各守原量词。配平主卷 §§178–179 的 $\mathsf F$ 等价仍仅在其完整 $E=A_{\rm sa}$ 分支使用；[《中央响应平方与径向一致》](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) §§6–10 则保持原 $E$ 稠密于整个指定 $A_{\rm sa}$ 的分支，不能用一般 JC 包含替代。这里既未增加原子分离，也未以已经正且实线性的返回映射预付 $D$ 的线性。

**定义 7.2（来源合同与几何解释）。** 原 $\Omega/\mathrm{native}$、原 $E/D$、全词 $K/J/q$、父位置和 ready 类型、原中心与经典静默部分及不等维块、全部零／不等／次归一质量、实际准备与完整效果菜单、共同记录与真正分组遗忘、全仪器及其环境和全部输出、实际相关联合与递归同源参考，继续保持配平主卷定义 128.1、§§250–251 的同一来源。全部合法顺序／自适应／并行历史、每个仍合法未来、停止／拒绝／销毁、同数两侧与真实双向返回，均未被数学像或反例模型替换。Born 比例仍只用于原实际完整菜单和严格正质量；零质量不归一。完整 CountRead 无穷及非离散记录、可数可加、正常性与前对偶、物理钟、能量、作用量及共同正 $\hbar$ 仍须各自原来源。

几何上，原标签即使不是单位，只要某份保 Jordan 乘法的数学读取把它照成单位倍数，它与任意另一原标签的旧响应就不能留下可见像。半定辅助像、纯态支撑和两张固定表限制的是同一旧输出；它们没有把完成里的投影变成原对象。中心元在每份不可约算子读取中变成标量，所以中心行及中心模理想行也被吸收。另一方面，完整模型中旧输出的真实差已经为零，四个独立面积上界仍能留下严格正底；这幅面积几何说明必须检验输出之间的实际关联。数学像、双对偶、纯态、字符、表示与预算模型都不制造实际准备、完整菜单、仪器、联合、参考、历史、未来、返回或物理尺度，也不完成完整量子起源目标。

## 追加锚（本行以下为增补区）

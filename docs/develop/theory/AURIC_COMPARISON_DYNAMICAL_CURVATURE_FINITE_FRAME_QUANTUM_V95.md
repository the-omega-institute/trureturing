# AURIC：比较曲率与变化曲率的内生相容、有限标架缺陷及量子结构

## 1. 两种二元关系与一个相容条件

**定义 1.1（有限正比较场）。** 设 $A$ 是非零有限维实向量空间，$1\in A$，$g$ 是正定内积，$\circ:A\times A\to A$ 是对称双线性运算，满足

$$
1\circ a=a,\qquad g(a\circ b,c)=g(b,a\circ c).
$$

记 $L_ab=a\circ b$。另给线性映射

$$
D:A\longrightarrow\operatorname{Der}(A,\circ),\qquad a\longmapsto D_a,
$$

其中导子条件是

$$
D_a(b\circ c)=(D_ab)\circ c+b\circ(D_ac).
$$

$L_a$ 表达 $a$ 与另一个元怎样共同参与对称比较；$D_a$ 表达由同一个元 $a$ 索引的有向变化。两者的参数、被作用对象和结果均留在 $A$ 内。此定义不预设复数、Jordan 恒等式、$D_aa=0$、$D_a$ 的斜伴随性或量子概率公式。有限维、实线性、正定比较以及线性的逐元生成元指派是定义的实质条件。

**定义 1.2（候选 C95：双曲率抵消）。** 在定义 1.1 的场上，令

$$
\mathcal E(a,c)=[L_a,L_c]+[D_a,D_c].
$$

候选的相容条件为

$$
\boxed{\mathcal E(a,c)=0\quad\text{对所有 }a,c\in A.}\tag{C95}
$$

这里 $[S,T]=ST-TS$。两个索引 $a,c$ 先给一个算子关系；作用到第三元 $b$ 后，得到可比较的三元结果 $\mathcal E(a,c)b$。对线性算子 $S,T$，小参数回路

$$
e^{sS}e^{tT}e^{-sS}e^{-tT}=I+st[S,T]+O\bigl(|st|(|s|+|t|)\bigr)
$$

的二阶项固定了本定义所用的曲率含义；并未要求两个有限回路逐参数互逆。

**定义 1.3（复记账及其完整内部解释）。** 令 $A_{\mathbb C}=A\oplus iA$，先只把 $i$ 当作分开记录对称部分与有向部分的形式符号。对实元定义

$$
a\cdot b=a\circ b-iD_ab,\qquad (a+ib)^*=a-ib,
$$

再复双线性延拓乘法。若此乘法构成有限维复 $C^*$ 代数，则取其正锥、正归一线性泛函及区间 $[0,1]$ 分别作为正记录、状态和效果。把全部这些数学状态和效果纳入菜单，称为完整内部解释；受限菜单另以其实际子集表示。

独立并置的解释要求局部代数含幺嵌入且互相交换，局部乘积张成联合代数，并且每对局部状态均有乘积态延拓。过程是对状态凸混合线性的映射，必须在每个允许的有限内部参考上保正；有结果的过程另外保留互斥记录标签。全部参考、结果记录、时钟及生成元均是同一理论的内部对象。这里的完整性和参考供应是明确的理论范围，不能仅由一个单体乘法推出。

## 2. 有限正比较下，自守与复乘法成为结论

**定理 2.1（自守冗余与精确三元障碍）。** 在定义 1.1 的有限正比较场中：

1. 每个 $\circ$ 的实导子自动对 $g$ 斜伴随。
2. 若 C95 成立，则 $D_ab=-D_ba$，特别地 $D_aa=0$、$D_1=0$。
3. 对任何另已满足 $D_ab=-D_ba$ 的此类场，不要求 C95，定义 1.3 的结合子恰为

$$
\boxed{(a\cdot b)\cdot c-a\cdot(b\cdot c)=-\mathcal E(a,c)b.}\tag{2.1}
$$

因而 C95 等价于该复乘法的结合性；C95 下的乘法具有忠实的有限维正 $*$ 表示，其自伴随部恰为 $A$。该有限正比较合同由此不需要再把自守 $D_aa=0$ 独立输入。

证明。先令 $\delta$ 是任意导子。含幺性给 $\delta1=0$，Leibniz 律给

$$
[\delta,L_b]=L_{\delta b}.
$$

右端自伴随，对左端取伴随，得到 $E=\delta+\delta^\dagger$ 与全部 $L_b$ 交换。置 $e=E1=\delta^\dagger1$，由

$$
Eb=EL_b1=L_bE1=L_be=L_eb
$$

得到 $E=L_e$，且 $e$ 属于

$$
C=\{c\in A:[L_c,L_b]=0\text{ 对所有 }b\in A\}.
$$

对 $c,d\in C$，交换关系给 $L_{c\circ d}=L_cL_d$，故 $C$ 是含幺交换结合子代数。其乘法算子实自伴随且可同时对角化，$c\mapsto L_c$ 又由 $L_c1=c$ 忠实，故 $C$ 同构于有限个 $\mathbb R$ 的直积。亦可直接用共同谱投影得到其正交幂等元分解。导子恒等式及 Jacobi 恒等式给

$$
[L_{\delta c},L_b]=[\delta,[L_c,L_b]]-[L_c,[\delta,L_b]]=0,
$$

所以 $\delta C\subset C$。实有限直积上的导子为零：对每个幂等元 $p$，$\delta p=2p\circ\delta p$ 逐坐标迫使 $\delta p=0$。于是 $\delta e=0$，从而

$$
g(e,e)=g(\delta^\dagger1,e)=g(1,\delta e)=0.
$$

正定性给 $e=0$、$E=0$，第一项成立。

为从 C95 推出反对称性，使用另一正定双线性型

$$
q(a,b)=\operatorname{Tr}_{\mathbb R}(L_aL_b).
$$

因为 $L_a$ 自伴随且 $L_a1=a$，非零 $a$ 满足 $q(a,a)=\|L_a\|_{\mathrm{HS}}^2>0$。矩阵迹恒等式使

$$
\begin{aligned}
T(a,b,c)&=\operatorname{Tr}_{\mathbb R}(D_a[D_b,D_c])\\
&=-\operatorname{Tr}_{\mathbb R}(D_a[L_b,L_c])\\
&=-\operatorname{Tr}_{\mathbb R}([D_a,L_b]L_c)\\
&=-q(D_ab,c)
\end{aligned}
$$

在三个变量中全交替。$q$ 非退化遂给 $D_ab=-D_ba$。又 $D_a1=0$，所以 $D_1a=0$。

现在只使用反对称性及 Leibniz 律展开定义 1.3。结合子的虚部为零，其实部为

$$
\begin{aligned}
&(a\circ b)\circ c-a\circ(b\circ c)\\
&\hspace{1em}-D_{D_ab}c+D_a(D_bc)\\
&=-[L_a,L_c]b-[D_a,D_c]b,
\end{aligned}
$$

即 (2.1)。这里尚未预设有向运算的 Jacobi 律。

在 C95 下，$(xy)^*=y^*x^*$ 由实乘法的对称、反对称分解成立。把 $g$ Hermitian 延拓到 $A_{\mathbb C}$，左乘实元 $a$ 的算子为

$$
\lambda_a=L_a-iD_a.
$$

第一项自伴随、第二项亦自伴随，所以 $\lambda_a^\dagger=\lambda_a$。结合性给 $\lambda_{xy}=\lambda_x\lambda_y$，含幺性给 $\lambda_x1=x$；因而 $\lambda$ 是忠实 $*$ 表示。其有限维像是闭的含幺 $*$ 子代数，以算子范数成为 $C^*$ 代数。其 Hermitian 元恰为 $A$。复结合代数的交换子还推出 $D$ 的 Jacobi 律，故不必把它预设给精确候选。

本证明中“动力对应产生复结合乘法”的步骤复用 Alfsen–Shultz 的动力对应路线及 [Niestegge，§5 Definition 1、Theorem 1、Corollary 1](https://arxiv.org/html/1402.0158v2)，DOI [10.1007/s10701-015-9881-x](https://doi.org/10.1007/s10701-015-9881-x)。这里额外给出的有限迹论证依赖正 Frobenius 比较合同，从双曲率条件推出自守；它不把该合同从 Niestegge 的更一般有序空间中免费取得，也不向无限维外推。∎

**命题 2.2（删去关系的不同后果）。** 以下合同分别允许不能完成定理 2.1 正重构的对象。

- 保留有限正比较与导子，删去 C95：取 $A=\operatorname{Sym}_2(\mathbb R)$、$a\circ b=(ab+ba)/2$、$g(a,b)=\operatorname{Tr}(ab)$、$D=0$。
- 保留曲率等式及反对称指派，删去导子条件：取 $A=\mathbb R^3$ 逐坐标乘法，基 $u=(1,1,1)$、$v=(1,0,0)$、$w=(0,1,0)$，规定 $D_vw=u$、$D_wv=-u$，其余基对的有向运算为零。
- 保留含幺、结合及非退化 Frobenius 比较，删去正定性：取 $A=\mathbb R[\epsilon]/(\epsilon^2)$、$D=0$，令 $g(a,b)=t(ab)$，其中 $t(1)=0,t(\epsilon)=1$。
- 保留正定内积但删去其与比较乘法的相容：取实代数 $A=\mathbb C$、$D=0$，把复单位视为实自伴随候选元。

证明。第一例中取

$$
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

有 $(Z\circ X)\circ X=0$，而 $Z\circ(X\circ X)=Z$，故不是可合并的结合乘法。它仍是一致的实 Jordan 模型；失败的是本定理指定的复结合合并。

第二例的全部 $L_a$ 对易，全部 $D_a$ 亦对易，因为有向运算两步后落入被全部 $D$ 消去的 $\mathbb Ru$。故曲率等式成立，但

$$
D_v(w^2)=u\ne2w=2w\circ D_vw.
$$

其复乘法满足 $(v\cdot v)\cdot w=-iu$、$v\cdot(v\cdot w)=-iv$，结合性失败。第三例中非零自伴随元 $\epsilon$ 平方为零，而忠实 $C^*$ 表示中自伴随平方为零只能是零。第四例中自伴随的复单位若有正表示，其平方应为 $-I$，与自伴随算子平方非负矛盾。∎

## 3. 有限关系球的完整标架缺陷

**定义 3.1（自洽有向关系球）。** 给定有限维 Euclidean 空间 $V$，维数 $n$，令

$$
A=\mathbb R1\oplus V,\quad
(\alpha,u)\circ(\beta,v)
=(\alpha\beta+\langle u,v\rangle,\alpha v+\beta u).
$$

比较内积为 $g((\alpha,u),(\beta,v))=\alpha\beta+\langle u,v\rangle$。给定交替双线性括号 $B(u,v)=[u,v]$，满足 Jacobi 律与度量不变性

$$
\langle[u,v],w\rangle=\langle u,[v,w]\rangle.
$$

令 $D_{(\alpha,u)}(\beta,v)=(0,[u,v])$。这些 $D$ 是比较运算的斜伴随导子。这里“自洽”精确包含 Jacobi、交替性及度量不变性；下述非零误差结论不将它们弱化成未经控制的近似关系。精确 C95 的这些性质由定理 2.1 推出。

对 $u,v\in V$，定义

$$
K_{u,v}w=\langle v,w\rangle u-\langle u,w\rangle v,
\qquad E_{u,v}=\operatorname{ad}_{[u,v]}+K_{u,v}.
$$

直接计算给 $[L_u,L_v](0,w)=(0,K_{u,v}w)$、$[D_u,D_v]=D_{[u,v]}$，所以 $E_{u,v}w$ 正是第三元上的双曲率偏差。

**定义 3.2（有限完整标架残差）。** 对 $V$ 的完整正交单位基 $e_1,\ldots,e_n$，令

$$
\mathfrak F^2=\sum_{i<j}\sum_k\|E_{e_i,e_j}e_k\|^2,
\qquad Q=-\sum_i\operatorname{ad}_{e_i}^2.
$$

所有和均为有限和。不把残差除以维数或测试次数，阈值使用这个未平均的规范化。$\Lambda^2V$ 采用 $e_i\wedge e_j$ 为正交单位基的内积。

**定理 3.3（完整标架恒等式与中心的不可消去项）。** 定义 3.1 的任意自洽有向关系球满足

$$
\boxed{\mathfrak F^2
=n(n-1)-2\operatorname{tr}Q+\tfrac12\operatorname{tr}Q^2
=\tfrac12\|Q-2I\|_{\mathrm{HS}}^2+n(n-3).}\tag{3.1}
$$

$\mathfrak F$ 与正交标架无关。若括号中心的维数为 $z_0$，则

$$
\boxed{\mathfrak F^2\ge n(n-3)+2z_0,}\tag{3.2}
$$

等号恰当且仅当 $Q=2I$ 在中心正交补上成立。

证明。度量不变性给 $\operatorname{ad}_u^\dagger=-\operatorname{ad}_u$。令 $T:\Lambda^2V\to V$，$T(u\wedge v)=[u,v]$。结构常数 $\langle[e_i,e_j],e_k\rangle$ 是全交替三形式，故

$$
TT^*=Q/2,\qquad
\sum_{i<j}\|[e_i,e_j]\|^2=\tfrac12\operatorname{tr}Q.
$$

逐对计算得

$$
\|K_{e_i,e_j}\|_{\mathrm{HS}}^2=2,\qquad
\langle K_{e_i,e_j},\operatorname{ad}_{[e_i,e_j]}\rangle_{\mathrm{HS}}
=-2\|[e_i,e_j]\|^2.
$$

另有

$$
\begin{aligned}
\sum_{i<j}\|\operatorname{ad}_{[e_i,e_j]}\|_{\mathrm{HS}}^2
&=\sum_{i<j}\langle Q[e_i,e_j],[e_i,e_j]\rangle\\
&=\operatorname{tr}(QTT^*)=\tfrac12\operatorname{tr}Q^2.
\end{aligned}
$$

平方展开的交叉项是 $-4\sum_{i<j}\|[e_i,e_j]\|^2$。合并三项，得到 (3.1)。$\mathfrak F$ 是线性映射 $u\wedge v\mapsto E_{u,v}$ 从 $\Lambda^2V$ 到 $\mathfrak{so}(V)$ 的 Hilbert–Schmidt 范数，因而不依赖所选正交基。

最后

$$
\langle Qu,u\rangle=\sum_i\|[e_i,u]\|^2
$$

给 $\ker Q=Z(V)$。在中心上 $Q-2I=-2I$，给平方和贡献 $4z_0$；其余部分非负，得到 (3.2) 及等号条件。∎

## 4. 三维被选出，标定误差得到精确控制

**定理 4.1（尖锐有限证书与 Pauli 端点）。** 对定义 3.1 的关系球，设 $n\ge2$。若

$$
\boxed{\mathfrak F^2<2,}\tag{4.1}
$$

则 $n=3$。在选定的正交定向下，存在实数 $c$ 使

$$
[u,v]=c\,u\times v,\qquad
\mathfrak F^2=6(c^2-1)^2.\tag{4.2}
$$

置 $\delta=\mathfrak F/\sqrt6$，则 $0\le\delta<1/\sqrt3$，$c\ne0$，并有精确误差及其尖锐一致上界

$$
\boxed{
\min_{\varepsilon\in\{1,-1\}}
\|B-\varepsilon\times\|_{\mathrm{bil}}
=\bigl||c|-1\bigr|
=\frac{\delta}{1+|c|}
\le1-\sqrt{1-\delta}.}\tag{4.3}
$$

其中双线性范数在两个闭单位球上取上确界。阈值 $2$ 不能在统一的维数判据中增大。零残差时，所得单球复代数是 $M_2(\mathbb C)$；允许 $n=0,1$ 时，还分别有纯标量与经典二值端点，故 C95 单独不保证非经典性。

证明。$n\ge4$ 时 (3.1) 给 $\mathfrak F^2\ge n(n-3)\ge4$。$n=2$ 时全交替三形式为零，所以 $B=0$、$\mathfrak F^2=2$。因此 (4.1) 迫使 $n=3$。三维交替三形式只有一个自由系数，给 $B=c\times$。叉积恒等式给

$$
[[u,v],w]=-c^2K_{u,v}w,\quad
E_{u,v}=(1-c^2)K_{u,v},\quad Q=2c^2I.
$$

于是 (4.2) 成立。$\delta=|c^2-1|$，配方给 (4.3)；取 $c=\sqrt{1-\delta}$ 达到一致上界。二维零括号达到残差平方 $2$，故任何严格大于 $2$ 的统一阈值均会纳入二维对象。

零残差给 $c=\varepsilon\in\{1,-1\}$。把定向换为使 $B=-\times$ 的一种，使用 Pauli 矩阵 $\sigma_1=X,\sigma_2=Y,\sigma_3=Z$，则

$$
(\alpha,u)\longmapsto\alpha I+u\cdot\sigma
$$

把 $\circ$ 变成矩阵反对易积的一半，把 $D_ab$ 变成 $i[\widehat a,\widehat b]/2$；因此定义 1.3 的复乘法就是通常矩阵乘法。另一种手性给相反代数，亦同构于 $M_2(\mathbb C)$。这一步采用标准 Pauli 恒等式，不把它算作新的重构结果；其与项目三轴及手性的对应参见 [V48，§§3、5](AURIC_ISOTROPY_CHIRALITY_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V48.md)。这里没有预设 $\operatorname{SO}(3)$ 各向同性来选择维数，维数来自完整标架残差。

$n=0$ 时 $A=\mathbb R$。$n=1$ 时 $B=0$，映射 $(\alpha,u)\mapsto(\alpha+u,\alpha-u)$ 给 $\mathbb R\oplus\mathbb R$，复化后分别为 $\mathbb C$、$\mathbb C\oplus\mathbb C$。∎

**定理 4.2（隐藏方向与不完整证书）。** 令 $V=\mathbb R^3\oplus\mathbb R^k$，$k\ge1$，只在第一块使用单位叉积，第二块为中心，交叉括号为零。仅使用第一块三个轴的三元测试全部满足 C95，但完整残差为

$$
\boxed{\mathfrak F^2=k(k+5).}\tag{4.4}
$$

因此三条已观察轴的全部内部测试不能排除隐藏方向。

证明。这是正交直和的度量 Lie 括号，$Q=2I$ 于前三维、$Q=0$ 于其余 $k$ 维。在前三维 $E_{u,v}w=0$。代入 (3.1)，得到

$$
\mathfrak F^2=(k+3)k+2k=k(k+5).
$$

也可逐对求和：三个旧轴与 $k$ 个中心轴给 $6k$，中心轴互相之间给 $k(k-1)$。当 $k=1$ 时，全部已测三轴精确相容，完整残差却是 $6$。∎

**命题 4.3（曲率只能标定大小，不能选择手性）。** 变换 $B\mapsto-B$ 保持 $Q$、$\mathfrak F$、比较运算及单体正锥不变。在定理 4.1 的三维情形，任何只依赖这些量的判据都不能区分 $c$ 与 $-c$；有向三元量

$$
\chi(u,v,w)=\langle[u,v],w\rangle
$$

在相同变换下反号。

证明。$Q$ 与曲率的有向部分均对 $B$ 二次，比较正锥只由 $\circ$ 的平方决定。相反，$\chi$ 对 $B$ 一次。若一个判据只使用前一组不变数据，则其在两个对象上的输入相同，输出必相同。∎

## 5. 从同一候选到完整有限量子理论的解释

**定义 5.1（量子解释所需的三类闭合）。** 对 C95 的任意有限正比较场采用定义 1.3 的完整内部解释，并分别声明：

- 完整状态与效果：使用全部正归一泛函及 $[0,1]$；
- 独立并置：使用定义 1.3 中的交换嵌入、乘积张成与全部乘积态延拓；
- 完整参考与过程：允许任意有限参考，联合保正且归一；结果标签保留到联合记录。

可逆时间族另外指定为连续的一参数自同构族，时间与能量的共同物理单位另行标定。这些闭合约定说明数学理论的范围，并不声称受限原生菜单已经供应其全部元素。

**定理 5.2（有限证书的精确端点与理论合同的联合完成）。** 定义 1.1 的场满足 C95，并采用定义 5.1 的完整解释时，其完整有限数学理论由有限直和复矩阵代数给出；其状态、概率、独立组合、有标签过程及连续可逆演化分别具有密度矩阵、Born、张量积、量子仪器及 Hamilton 形式。对其中任何满足定义 3.1、$n\ge2$ 的单球，有限残差证书在精确端点只保留三维 $M_2(\mathbb C)$，而非任意维关系球；非零残差的可解释范围及误差仍严格受定理 4.1 的自洽前提限制。

证明。新的联立限制是定理 3.3–4.2 的有限标架结论；以下使用标准有限 $C^*$ 代数与完全正映射理论，把这一端点接到完整操作合同，不另把标准表示结果当作新增公理推导。

由定理 2.1 得到忠实有限 $C^*$ 代数 $\mathcal A$。有限 $C^*$ 代数结构定理给

$$
\mathcal A\cong\bigoplus_sM_{d_s}(\mathbb C),\qquad
A\cong\bigoplus_s\operatorname{Herm}_{d_s}(\mathbb C).
$$

其自伴随正元均有自伴随平方根，所以由实平方生成的锥恰是矩阵正锥。每个正归一泛函唯一表示为

$$
\omega(a)=\sum_s\operatorname{Tr}(\rho_sa_s),\qquad
\rho_s\ge0,\quad\sum_s\operatorname{Tr}\rho_s=1.
$$

这是有限维迹配对与正锥自对偶；极点恰是某个单一扇区中的秩一投影。效果族 $e_j\ge0$、$\sum_je_j=1$ 因而给

$$
p(j\mid\omega)=\omega(e_j)=\sum_s\operatorname{Tr}(\rho_se_{j,s}).
$$

在一个纯态与秩一效果之间，它化为 $|\langle\phi,\psi\rangle|^2$。概率可加与归一来自正归一泛函的定义；复数平方形式则来自前面由两个实关系构造的矩阵表示，二者的逻辑角色不同。

对并置，局部交换嵌入给乘法同态

$$
\pi:\mathcal A\otimes_{\mathrm{alg}}\mathcal B\longrightarrow\mathcal C,
\qquad a\otimes b\longmapsto\iota_A(a)\iota_B(b).
$$

乘积张成给满射。若 $\pi(x)=0$，所有乘积态延拓给 $(\omega_A\otimes\omega_B)(x)=0$。局部状态线性张成全部自伴随对偶，复线性延拓后分离代数张量积，所以 $x=0$。故 $\pi$ 为同构；有限维时正张量范数唯一，得到通常复张量积及各扇区直和。这个论证明确使用乘积态供应；仅有“局部读数能区分已有联合态”不能替代它。

设状态过程的对偶为 $\Phi^*$。对每个有限参考保正，正是矩阵层上 $\Phi^*\otimes\mathrm{id}_r$ 保正，即完全正；归一给含幺性，对偶状态映射保迹。在单矩阵块之间，由 Choi 正矩阵谱分解得到

$$
\Phi(\rho)=\sum_\mu K_\mu\rho K_\mu^*,\qquad
\sum_\mu K_\mu^*K_\mu=I.
$$

直和情形按输入输出块分别给这样的 Kraus 族。保留结果标签 $j$ 时，同一论证给完全正分支 $\Phi_j$，总和保迹，联合记录为

$$
\rho\longmapsto\sum_j\Phi_j(\rho)\otimes|j\rangle\langle j|.
$$

若先丢弃标签，只能得到总过程，不能从中唯一恢复仪器。共同输入—输出过程存在性的条件直接使用 [V94，定义 1.2、定理 2.1](AURIC_COMMON_PROCESS_CONDITIONAL_RELATIONS_LATITUDE_FRAMES_V94.md) 的同源条件相容判据；本候选补上该判据所继承的有限复代数载体，不重证其信道插值。

C95 的 $D_h$ 在构造的代数中满足

$$
D_ha=\tfrac i2[h,a],\qquad
e^{tD_h}a=e^{ith/2}ae^{-ith/2}.
$$

更一般的连续一参数 $*$ 自同构不能连续置换有限个中心扇区；每个矩阵块内的导子都是内导子，所以也有此 Hamilton 形式。对偶态演化为 $\dot\rho=-i[h,\rho]/2$。使用物理时间 $t_{\rm phys}$、能量 $H$ 时，$h=2H/\hbar$ 的共同标定给 $i\hbar\dot\psi=H\psi$；$\hbar$ 的数值不是由无量纲曲率恒等式推出。扇区之间的相对时间单位也不能仅由互不作用的单体结论固定。

最后，单球满足精确 C95 时 $\mathfrak F=0$，定理 4.1 排除 $n=2$ 及 $n\ge4$，取得三维 Pauli 端点。定理 4.2 保证此步骤没有用局部三轴检验冒充完整维数检验。标准复代数表示、Kraus 与动力对应作为上述联立推导的中间工具使用；全维 SIC 存在性、某个指定 Hamiltonian、无限维极限及连续时空未进入该结论。∎

## 6. 对称测量的极值不能代替有向相容

**定义 6.1（四面体比较与其 Lüders 读）。** 在定理 4.1 的精确三维端点，令 $n_1,\ldots,n_4$ 是单位向量，满足 $\sum_jn_j=0$、$n_j\cdot n_k=-1/3$（$j\ne k$）。置

$$
P_j=\tfrac12(I+n_j\cdot\sigma),\qquad E_j=P_j/2.
$$

其 Lüders 总过程为 $\mathcal L(\rho)=\sum_j\sqrt{E_j}\rho\sqrt{E_j}$。此定义沿用 SIC 的标准四面体模型；不以其存在性反向假设 C95。

**命题 6.2（同一极值读数不能固定曲率尺度）。** 对每个实数 $c$，使用同一个三维比较运算、同一正锥及定义 6.1 的状态—效果—Lüders 读，但将有向括号置为 $B_c=c\times$。所有这些对象的静态 Born 概率与纯输入 Lüders 输出熵相同，且

$$
\mathcal L(\rho)=\tfrac13(\rho+I),\qquad
S(\mathcal L(P))=\log3-\tfrac23\log2
$$

对任意秩一输入 $P$ 成立；它们的完整有向相容残差却为

$$
\mathfrak F(c)^2=6(c^2-1)^2.
$$

所以即使取得该测量熵极值，仍不能从这一读数判定 C95；例如 $c=0$ 与 $c=1$ 的全部这些读数相同，残差平方分别为 $6$ 与 $0$。

证明。比较锥及状态—效果配对不含 $c$。对 $\rho=(I+r\cdot\sigma)/2$，有 $\sqrt{E_j}=P_j/\sqrt2$、$P_j\rho P_j=\operatorname{Tr}(P_j\rho)P_j$。四面体的二阶矩 $\sum_jn_jn_j^T=4I/3$ 给

$$
\sum_j\tfrac12\operatorname{Tr}(P_j\rho)P_j
=\tfrac12I+\tfrac16r\cdot\sigma
=\tfrac13(\rho+I).
$$

纯输入的两个输出特征值为 $2/3,1/3$，得到所给熵。$B_c$ 均是保持比较的度量 Lie 括号，而定理 4.1 给其残差公式。此处对于 $c\ne\pm1$，Lüders 读是另已给定且所有模型共享的对称读出合同，不声称它由不结合的 $\cdot_c$ 自动产生。

此命题把熵极值与有向生成元的不可识别性放在同一批对象上。SIC Lüders 过程的标准结论见 [DeBrota–Stacey，Theorems 1–2](https://arxiv.org/html/1907.10999v2)，DOI [10.1103/PhysRevA.100.062327](https://doi.org/10.1103/PhysRevA.100.062327)；项目的 [Lüders 熵饱和结果](../../../Blueprint/D5/S3/Quantum/Measurements/LudersEntropySaturationSIC.md)在指定的复矩阵、MIC 与 Haar 解释下由平均熵等号推出 SIC 存在。该条件结论不反向给出未参与熵读数的有向对应。∎

## 7. 内生约束的范围

**定义 7.1（内生的严格含义）。** 本候选中，内生指一个关系场的比较元、变化生成元、被作用元和记录都在同一个已定义整体内，候选只约束这些定义间能否共同组成定理 2.1 的乘法。若以所有满足定义 1.1 与 C95 的有限场作为一个模型类，该模型类包含经典端点、复矩阵块及其直和。它的定义不从一个没有任何关系的集合推出正定性、线性、有限性、非经典性、全部参考或物理实现。

**命题 7.2（约束的辨别力与未被消去的自由度）。** 在前述模型类中，比较与变化不再能任意独立选择：定理 2.1 强制其共同结合性，定理 3.3–4.1 在自洽关系球中给出有限维数及尺度约束。但非经典维数的实际选取、可制备菜单、中心扇区数、共同物理单位及所实现的能量函数，不由该约束唯一固定。

证明。前一断言由 (2.1)、(3.1)、(4.2) 给出。经典标量模型与 $M_2(\mathbb C)$ 均满足候选，表明非经典性不是必然。对任一满足候选的场，限制状态—效果菜单不改 $L,D$，所以全菜单不可由其恢复。有限个模型的直和仍满足定义与候选，所以中心扇区数不固定。对任意固定代数，不同自伴随元 $h$ 给不同的允许生成元 $D_h$；而无量纲等式不指定外部给定的秒与能量单位的比例，故不能唯一固定物理 $\hbar$ 或 Hamiltonian。∎

## 追加锚（本行以下为增补区）

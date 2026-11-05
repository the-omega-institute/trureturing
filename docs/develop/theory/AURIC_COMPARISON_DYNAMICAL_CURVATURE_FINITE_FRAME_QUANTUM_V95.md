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

独立并置的解释要求局部代数经含幺 $*$ 嵌入且互相交换，局部乘积张成联合代数，并且每对局部状态均有乘积态延拓。过程是对状态凸混合线性的映射，必须在每个允许的有限内部参考上保正；有结果的过程另外保留互斥记录标签。全部参考、结果记录、时钟及生成元均是同一理论的内部对象。这里的完整性和参考供应是明确的理论范围，不能仅由一个单体乘法推出。

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

在一个纯态与秩一投影效果之间，它化为 $|\langle\phi,\psi\rangle|^2$。概率可加与归一来自正归一泛函的定义；复数平方形式则来自前面由两个实关系构造的矩阵表示，二者的逻辑角色不同。

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

直和情形按输入输出块给 Kraus 族，保迹归一跨全部输出块求和：

$$
\Phi(\rho)_t=\sum_{s,\mu}K_{ts\mu}\rho_sK_{ts\mu}^*,\qquad
\sum_{t,\mu}K_{ts\mu}^*K_{ts\mu}=I_{d_s}\quad\text{对每个输入块 }s.
$$

保留结果标签 $j$ 时，同一论证给完全正分支 $\Phi_j$，总和保迹，联合记录为

$$
\rho\longmapsto\sum_j\Phi_j(\rho)\otimes|j\rangle\langle j|.
$$

若先丢弃标签，只能得到总过程，不能从中唯一恢复仪器。共同输入—输出过程存在性的条件直接使用 [V94，定义 2.2、定理 3.2](AURIC_COMMON_PROCESS_CONDITIONAL_RELATIONS_LATITUDE_FRAMES_V94.md) 的同源条件相容判据；本候选补上该判据所继承的有限复代数载体，不重证其信道插值。

对保持全部可见读数、合并全部同资料态并固定忠实参照的全域回缩，另直接复用[二元参考与充分约化 V94，定理 4.2、9.1](AURIC_BINARY_REFERENCE_ENDOGENOUS_SUFFICIENT_REDUCTION_AND_QUANTUM_VISIBLE_ALGEBRA_V94.md#thm-c94-main)：在该卷声明的有限矩阵合同中，一个二元参考上的全部联合正性连同这些回缩条件，已足以给出唯一、完全正的块重置，并锁定可见代数与参照的模相容。这里的完全正性依赖整组回缩前件，不能把前面的任意过程参考条件一律降成二正性。

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

证明。前一断言由 (2.1)、(3.1)、(4.2) 给出。经典标量模型与 $M_2(\mathbb C)$ 均满足候选，表明非经典性不是必然。对任一满足候选的场，限制状态—效果菜单不改 $L,D$，所以全菜单不可由其恢复。有限个模型的直和仍满足定义与候选，所以中心扇区数不固定。在非交换矩阵块中，不差中心元的自伴随元 $h$ 给不同的允许生成元 $D_h$，而中心能量偏置不改变 $D_h$；无量纲等式不指定秒与能量单位的比例，故不能唯一固定物理 $\hbar$ 或 Hamiltonian。∎

## 追加锚（本行以下为增补区）

## 8. C120：同一整体中的原生响应载体与实际供应

**定义 8.1（同一 $\Omega$、原对象与完整响应词）。** 设 $\Omega$ 是定义 1.1–1.3、C95 和定理 2.1 所规定的同一个整体。它同时包含对象集合 $\mathsf O$、原准备 $\mathsf P_0$、原效果 $\mathsf E_0$、原事件 $\mathsf X_0$、合法有限历史 $\mathsf H$、实现身份 $\iota$、记录端口 $\mathsf R$ 以及每个非零支的命名支撑和返回资料 $\mathsf S$。一个历史

$$
h=(o_0,p_0,e_1,x_1,r_1,\ldots,x_n,r_n,o_n)\in\mathsf H
$$

保留原对象、原准备、原读口、原标签、每次成功或失败、实现身份和全部后继；不以等价映射替换任一原实现。对有限原词 $w$，$\operatorname{Resp}_\Omega(h,w)$ 是带有顺序标签、记录端口、合法性和终端类型的原始响应。成功、拒绝、不可用、终止和空输出是不同的响应值。原词的定义域是原系统实际允许的定义域，不能以一个矩阵表示的全域词替换它。

**定义 8.2（矩阵重构以前的有限响应几何）。** C120 的有限几何前件由下列同一组资料组成。

1. 每个非零对象有有限维实响应空间 $V$、效果空间 $V^*$、闭尖锥 $V_+$、效果锥 $V^*_+$、内部单位 $u\in V^*_+$ 和配对 $\langle e,s\rangle$。原准备锥定义为
   $$
   V_{+,{\rm act}}=\left\{\sum_{k=1}^m a_kp_k:m<\infty,\ a_k\ge0,\ p_k\in\mathsf P_0\right\};
   $$
   C120 的共同载体前件要求这个有限锥恰为 $V_+$（即原准备有限生成且序生成）；不加入极限准备。原效果菜单 $\mathsf E_0$ 是 $[0,u]$ 中被实际命名的子集，而完整数学效果空间是整个区间 $[0,u]$；两者不混同。
2. 每一个非零面 $F$ 都有原滤波器 $P_F$。其定义严格采用 Barnum–Müller–Ududec [BMU14, Definitions 13–14](https://arxiv.org/html/1403.4147)：$P_F$ 是正线性投影，具有正互补、伴随的正互补并满足 $u(P_Fs)\le u(s)$。有限维 projectivity 要求 $\operatorname{im}_+P_F$ 恰为该面。因而 [BBKM15, Proposition 3.1](https://arxiv.org/html/1508.03107) 的面、filter、projective unit 三者双射可以直接用于每个原面；不把选中的 $B$ 映射误当成别的 filter 定义。
3. 原子态与原子效果满足对称转移概率（STP）。[BBKM15, Proposition 5.1] 的有限谱展开和 [BBKM15, Theorem 6.1 及 Appendix B] 的原子映射因此作为同一效果空间上的运输定理使用。这里不加入 BMU17 的强对称性、signed spectrality 或一个任意自对偶化内积。BMU14 Theorem 16 只在另行给出“filters 保持纯性”时作为 Jordan 一致性桥梁；它保留不等大小的非经典直和，并不替换 C95 的复乘法结论。
4. 对每个简单块和每个有限秩 $r$，有足够的秩二原参考副本 $R_{r,\ell}$（至少覆盖该块每一对原子方向的有限链，$\ell=1,\ldots,r-1$），并有保持原产品输入作用的参考延伸
   $$
   T^{(r)}=T\otimes{\rm id}_{R_r}.
   $$
   这些延伸在完整的实际联合准备锥 $V_{+,{\rm act}}\otimes V_{+,R_r}$ 上取正，且保留原记录端口和实现身份。单独一个 qubit 试验不满足此量词。确定性参考准备输出的滤波系数为一，并与只用于检验正性的参考资源分开记录。
5. $D$ 是原效果空间上的给定变化生成元；它不是从选定矩阵坐标的交换子倒定义。原 F、原返回、原校准、原控制和原记录供应是独立前件，不能从几何滤波或数学 Kraus 标签推回。

**定义 8.3（规范原子运输与单位归一）。** 令 $J:V^*\to V$ 为 [BBKM15, Theorem 6.1] 的原子映射，并令

$$
(e,f)_{\rm BBKM}:=\langle e,Jf\rangle .
$$

STP 与 Appendix B 给出 $J$ 的线性、正性、对称性和正定性。把原单位送成 $1_V:=J(u)$，并把 $\tau(s):=u(s)$ 固定为唯一的归一化迹配对。于是

$$
J(u)=1_V,\qquad \tau(1_V)=\dim_{\rm rank}(\Omega),\qquad
\langle e,s\rangle=\tau(E_eS_s),
$$

其中 $E_e$、$S_s$ 是下述 C95 乘法中的对应元素。这个单位和迹不是任意选择的自对偶内积的缩放；它由原效果单位和原子转移概率共同钉住。

**定理 8.4（从原生几何到同一有限复载体）。** 在定义 8.1–8.3、C95 及所有原准备和原效果的有限性前件下，每个非零对象有一个由 $J,u$ 和原记录身份唯一确定到保持这些资料的 $*$-同构的有限复 $C^*$ 载体

$$
\mathcal A=\bigoplus_{s\in S}M_{d_s}(\mathbb C),\qquad
A=\mathcal A_{\rm sa},\qquad
A_+=\bigoplus_sM_{d_s}(\mathbb C)_+,
$$

且 $S_s\mapsto\rho_s\ge0$、$E_e\mapsto 0\le E_e\le I$ 给出

$$
u(s)=\sum_s{\rm Tr}(\rho_s),\qquad
\langle e,s\rangle=\sum_s{\rm Tr}(E_{e,s}\rho_s).
\tag{8.1}
$$

证明。定理 2.1 已由 C95 给出结合的有限复 $C^*$ 乘法及其自伴部，故有限维 $C^*$ 结构定理给出不等大小的矩阵直和。有限 projectivity 使每个面由定义 8.2(2) 的原 filter 表示；BBKM Proposition 3.1 将它与同一原面的一一对应固定。再用 Proposition 5.1 的有限谱展开，把每个效果写成有限个互相正交原子效果的实线性组合。Theorem 6.1 的 $J$ 把这些原子逐一送到原子态，并由 Appendix B 的 STP 得到正定、对称且正的配对。原单位 $u$ 送到各块单位矩阵，因而 (8.1) 的迹系数由原归一化而非任意 Frobenius 选择确定。定义 8.2(1) 的序生成性把参考正性提升为整个矩阵正锥，故数学效果为 $0\le E\le I$。BMU Theorem 16 若在额外纯性前件下使用，只说明同一几何的 Jordan 兼容性；它没有加入强对称性，也没有删去任意不等直和。∎

**命题 8.5（原词概率恒等式）。** 对任意 $h\in\mathsf H$、原成功词 $w=x_1\cdots x_n$ 及其原记录标签 $\lambda=(\lambda_1,\ldots,\lambda_n)$，令 $T_{w,\lambda}$ 为同一实现的未归一化成功后继。则

$$
p_\Omega(w,\lambda\mid s)=\operatorname{Prob}\!\left(\operatorname{Resp}_\Omega(h,w;\lambda)\right)
=\tau\!\left(T_{w,\lambda}(\rho_s)\right).
\tag{8.2}
$$

若 $w$ 在某一步失败，则该叶记为 $\bot$，保留失败标签、实现身份和后继；其成功分支不被条件归一化后重新命名。

证明。单步时，(8.1) 是原效果的概率坐标。假设 (8.2) 对长度 $n$ 成立；原第 $n+1$ 步的记录端口决定唯一的原分支，故其未归一化后继为 $T_{x_{n+1},\lambda_{n+1}}T_{w,\lambda}$，迹配对给出乘法递推。失败端是同一原事件的补充记录，不能改写成成功词。归纳得到任意有限历史，包括重复、分支、空词和所有失败叶。∎

**定义 8.6（联合产品与参考稳定）。** 对两个原对象 $A,B$，C120 只在原系统已经声明产品输入、共同记录和空间边时取标准复合

$$
\mathcal A_{AB}=\mathcal A_A\otimes\mathcal A_B
\cong\bigoplus_{s,t}M_{d_sd_t}(\mathbb C).
$$

产品准备是原准备的有限正组合，产品事件在原记录端口上作用为同一个原映射的张量延伸。参考延伸不得改变产品输入作用，且必须在整个实际联合准备锥上正；它不是一个只在选定矩阵态上成立的兼容映射。

**定理 8.7（原复合的张量对应）。** 若定义 8.6 的产品准备和原空间边均有供应，则原复合的乘法、单位、迹和效果满足

$$
(a\otimes b)(c\otimes d)=ac\otimes bd,\qquad
\tau_{AB}=\tau_A\otimes\tau_B,\qquad
p(e\otimes f\mid\rho\otimes\sigma)=p(e\mid\rho)p(f\mid\sigma).
\tag{8.3}
$$

并且原联合代数就是上述直和张量，而非只在某一固定矩阵块中的局部兼容。

证明。局部含幺嵌入交换，产品态延拓和有限正参考使乘积张成的代数被所有产品态分离。若代数张量中的 $z$ 被所有产品态消去，则其每个块系数都被局部状态—效果配对消去，故 $z=0$；乘法同态因此既单又满。定理 8.4 的单位和迹按块张量相乘，得到 (8.3)。若产品准备、参考延伸或空间边未实际供应，这个结论只保留为未取得的条件命题。∎

**定义 8.8（全原事件的 CP/TNI 供应）。** 原事件 $x\in\mathsf X_0$ 的实际后继 $T_x$ 要满足：对每个定义 8.2(4) 的有限参考，$T_x\otimes{\rm id}_{R_r}$ 在整个实际联合准备锥上正；其成功效果为

$$
E_x=T_x^\dagger(I),\qquad 0\le E_x\le I.
$$

确定性原事件另要求 $E_x=I$。全体原事件、原标签、原遗忘和全部合法有限接续都在该量词内。

**定理 8.9（全部原事件的完全正表示）。** 定义 8.8 给出每个原事件的 CP、迹不增表示。在块记号下

$$
T_x(\rho)_t=\sum_{s,\mu}K^{x}_{ts\mu}\rho_sK^{x*}_{ts\mu},\qquad
\sum_{t,\mu}K^{x*}_{ts\mu}K^{x}_{ts\mu}\le I_{d_s}.
\tag{8.4}
$$

证明。给定有限输入维 $d$，定义 8.2 的参考族包含足够的有限参考块，使 $T_x\otimes{\rm id}_{d}$ 在正锥上正。有限 Choi 判据遂给完全正性；这正是 [Watrous, *The Theory of Quantum Information*, Definition 1.124 and Theorem 2.22](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf) 的适用接口。Choi 正矩阵的有限谱分解逐块给 (8.4)，而 $E_x\le I$ 给迹不增。这里的数学指标 $\mu$ 只是表示指标；它没有自动成为可访问记录端口。∎

**定义 8.10（原 F 的细标签合同）。** 保留 C118 定义 120.1、120.2、140.1 以及定理 122.1、143.1、144.1 的原 F：每个非零原成功箭头 $T_x$ 有同一原实现的有限联合细标签箭头 $\widehat T_x$，原记录遗忘满足 $d(\widehat T_x)=T_x$，每个非零细支有原命名支撑、原返回和原实现身份。结构存储图册的命题 2.1 与定理 2.2 另外保证原始端口、历史和实现身份的提取与一致性；它们不制造新的读口。C120 进一步要求 F 的原细标签已经细到

$$
\widehat T_x(\rho)=\sum_{\lambda\in\Lambda_x}T_{x,\lambda}(\rho),\qquad
T_{x,\lambda}(\rho)=K_{x,\lambda}\rho K_{x,\lambda}^*.
\tag{8.5}
$$

其中 $\lambda$ 是原记录端口的实际标签；若同一数学通道另有未观察的 Kraus 指标，它们不能冒充 $\lambda$。这是真实供应条件，不能由 (8.4) 的任意分解替代。

**定理 8.11（原标签的一 Kraus 分支）。** 在定义 8.10 的 F 下，每个原非零细标签分支是一个实际一 Kraus 设备，且其原标签统计满足

$$
p(\lambda\mid\rho)=\tau(K_{x,\lambda}\rho K_{x,\lambda}^*),\qquad
E_{x,\lambda}=K_{x,\lambda}^*K_{x,\lambda}.
\tag{8.6}
$$

标签遗忘得到原同一实现的 $\widehat T_x$，而不是另造一个相等通道。证明是对原标签记录逐支读取 (8.5)；完全正性保证每支合法，F 的遗忘等式保证总和仍是原过程。若原记录只给出不可再分的多 Kraus 分支，(8.5) 是额外未满足的供应，C120 不得声称一 Kraus 结论。∎

**定义 8.12（精确原始成功滤波词与失败叶）。** 设 $\mathsf F_0\subseteq\mathsf E_0$ 是实际可调用滤波效果。一个原始成功词是

$$
w=((E_1,\lambda_1),\ldots,(E_n,\lambda_n))\in\mathsf W_{\rm suc}
$$

其中每个 $T_{E_i,\lambda_i}$ 是定义 8.10 的原细支，前一步的实际输出记录、支撑和权限与下一步完全相容。其原始成功值定义为

$$
T_w=T_{E_n,\lambda_n}\circ\cdots\circ T_{E_1,\lambda_1},\qquad
p_{\rm raw}(w\mid\rho)=\tau(T_w(\rho)).
\tag{8.7}
$$

不除以 $p_{\rm raw}$，不把条件输出变成新准备。每一个节点同时列出所有原失败叶 $f\in\mathsf F_{\rm fail}$：拒绝、禁用、记录不可达、支撑不相容、返回失败和终止各保留其原标签与实现身份，并记其未归一化失败后继 $T_f$；若总事件为确定性，则

$$
T_{\rm fail}=T_{\rm total}-\sum_{\lambda\ {\rm success}}T_\lambda,\qquad
\sum_{\lambda\ {\rm success}}p_\lambda+p_{\rm fail}=1.
\tag{8.8}
$$

**命题 8.13（滤波词的合法组合闭包）。** $\mathsf W_{\rm suc}$ 含空词 $\varepsilon$，满足 $T_\varepsilon={\rm id}$；若 $w,v$ 的相接记录、支撑返回和原权限相容，则 $wv\in\mathsf W_{\rm suc}$ 且 $T_{wv}=T_vT_w$。所有不相容接续都落在明确失败叶而不被删去。对有限并置、有限标签遗忘、原产品张量和原确定性丢弃，闭包仍保留原记录端口和原实现身份。

证明。每一步只使用原合同允许的下一步，故接续后的输出仍在实际联合准备锥中；TNI 性给 (8.8)，而原记录端口的串接给标签的唯一拼接。非法接续没有原实现，因而只能是失败叶，不可由一个相等矩阵映射补造。空词和结合律来自映射复合。∎

**定义 8.14（非零与零、奇异效果的分案）。** 若原对象的 C95 载体非零，以上定理对每个非零块成立。若 $\Omega$ 只含零对象，则另取只有零响应和失败叶的退化模型，不调用 V95 的非零载体定理。零效果、零细支和零准备单独记为零映射并无返回；它们没有伪逆、原子方向或条件态。对非零但奇异的 $K$，令

$$
P_K=\operatorname{supp}(K^*K),\qquad Q_K=\operatorname{supp}(KK^*),\qquad
c_K=\lambda_{\min}^+(KK^*),
$$

并定义原支撑返回

$$
R_K(X)=c_KK^+XK^{+*},\qquad
R_K\circ{\rm Ad}_K(X)=c_KP_KXP_K.
\tag{8.9}
$$

这里 $K^+$ 是 Moore–Penrose 逆，$c_K>0$ 是非零输出支撑上的最小正特征值；于是 $R_K^\dagger(I)\le Q_K$，返回是 TNI 且只在命名支撑上工作。若 $K=0$，采用零分案而不套用 (8.9)。

**定义 8.15（完整满足族与实际闭包）。** 对任意有限指标集 $S$ 和任意正整数族 $(d_s)_{s\in S}$，取

$$
\mathcal Q_{S,d}=\bigoplus_{s\in S}M_{d_s}(\mathbb C).
$$

其数学态为全部 $\rho\ge0,\ {\rm Tr}\rho=1$，数学效果为全部 $0\le E\le I$；原准备只取原子秩一态和它们的有限正组合，原效果菜单由一个指定的实际子集给出。每个 CP/TNI 映射选取透明有限 Kraus 设备，每个 $K_{x,\lambda}$ 带原记录标签、记录端口、命名支撑、(8.9) 的缩放返回和密封实现身份；标签遗忘使用同一设备的原遗忘端口。设备族对有限复合、标签遗忘、确定性丢弃、标准张量复合、空词和所有原始滤波成功词闭合，并把每个失败叶加入记录语言。产品输入的作用恒为原作用，参考延伸恒为 $T\otimes{\rm id}$，并作用于整个有限正准备锥。

**定理 8.16（全有限直和的 C120 满足族）。** 所有 $\mathcal Q_{S,d}$ 及上述透明设备、原记录、支撑返回和闭包组成一族满足 C95、定义 8.2–8.15 的模型。它覆盖任意有限复矩阵直和及其声明的标准复合，保留不等大小非经典扇区、所有原准备和原效果的统计、全部原事件和有限历史。证明。C95 取每个矩阵直和的自伴部与其内导子；定义 8.2 的几何由矩阵正锥、迹配对、标准 filter 和 STP 给出，且 BBKM 的单位运输正好是 $I$ 与 $\operatorname{Tr}$。秩二参考副本按有限块的全部原子对配备，再以有限直和和张量复合得到需要的每个参考维数。每个透明 Kraus 设备由 (8.4) 正、TNI；(8.5) 和原遗忘保留实际记录。有限复合乘积仍有有限 Kraus 列表，(8.9) 给每个非零支的正确缩放返回，零支按定义 8.14 处理。故所有有限词及失败叶均在同一实现语言中，且 (8.2) 对全部历史成立。此为条件满足族，不声称某一给定 $\Omega$ 已实际提供这些设备。∎

**命题 8.17（局部转置障碍的精确范围）。** 在 $M_2(\mathbb C)$ 上，$\vartheta(\rho)=\rho^{\mathsf T}$ 保正、保迹且在单系统效果上给合法标量响应，但对 Bell 正元的参考延伸 $(\vartheta\otimes{\rm id}_2)$ 不保正，故它违反定义 8.8 的参考合同。该命题只否定“单系统正性足够”这一局部替代；它不声称删除 C120 其他前件后得到完整模型。

**命题 8.18（局部测量—准备障碍的精确范围）。** 映射

$$
M(\rho)=\sum_j{\rm Tr}(E_j\rho)\sigma_j
$$

在给定有限效果表上可以是 CP/TNI，并可提供一个局部成功标签；但它通常没有原细记录的一 Kraus 细化、原命名支撑返回或任意后续滤波词的同一实现。故它只能作为“一个事件的统计可实现”反例，不能作为 C120 全菜单、全历史或 F 的删除模型。

**命题 8.19（密封设备语言的局部删除证据）。** 令 $L_{\rm id}$ 是透明 CP 设备及其原记录端口的有限词语言；在一个密封扩展中加入一台 $\Theta$，其接口只暴露输入、输出和一个不可读密封记录，不暴露原 F 端口。令 $L_{\rm id}^{\Theta}$ 对有限复合和张量闭合，并规定凡词触及密封端口即返回密封失败叶。则 $L_{\rm id}^{\Theta}$ 保持每台原透明设备的实现身份，且含 $\Theta=\vartheta$ 的局部正而非 CP 事件。它证明删除“全称 F 细记录”会留下局部漏洞；由于 $\Theta$ 也违反定义 8.8 的任意参考延伸，本文不把 $L_{\rm id}^{\Theta}$ 宣称为删除 F 后仍满足其余全部 C120 条款的全域模型。

**定义 8.20（量子接口、独立输入与白话解释）。** 在 C120 中，Hilbert 空间和密度矩阵来自定理 8.4 的有限 $C^*$ 表示；Born 公式是 (8.1)；数学 CP/Kraus 来自定理 8.9；原记录 Kraus 还必须使用 F 和 (8.5)；选定效果 $E$ 的平方根更新只在原菜单实际供应 $K=\sqrt E$、其确定性参考输出和理想支撑返回时成立：

$$
\rho\longmapsto\frac{\sqrt E\,\rho\,\sqrt E}{\operatorname{Tr}(\rho E)}.
\tag{8.10}
$$

一个可调用滤波集合不自动供应任意 POVM 仪器；要把若干效果装配为同一仪器，还要另供共同控制、互斥记录、标签遗忘和原接续。空间张量必须消费定义 8.6 的产品准备、共同参考和空间边。连续 Schrödinger、von Neumann 或 Hamilton 形式只在另行实际供应连续可逆确定性一参数群时成立；C95 和 $D$ 的代数存在不产生这样的时间族，也不确定 $\hbar$。

白话说：同一个 $\Omega$ 先保留每一次原来的准备、读口、标签、失败和返回，把它们看成一条带名字的响应词；几何条件只负责证明这些响应可以放进同一套有限复矩阵坐标，而且单位和迹的刻度由原效果本身固定。参考副本把一个事件是否真的保正检查到所有有限矩阵层，原 F 再保证数学分解中的细标签就是设备真正留下的记录。成功的滤波词只在原设备确实允许下一步时连接，失败叶也留下；奇异支用支撑上的正确缩放伪逆返回，零支另案处理。这样得到的是“如果这些原设备、参考和记录确实供应，则量子载体与实际原操作同时出现”的条件候选，不是把兼容矩阵当成已经存在的设备。

**命题 8.21（依赖分栏与边界）。** C120 的派生结论及保留输入如下。

| 内容 | 直接派生的条件 | 仍独立保留的输入 |
| --- | --- | --- |
| 复载体、单位、锥、Born | C95、有限 projectivity、STP、BBKM Proposition 3.1、Proposition 5.1、Theorem 6.1 | 原效果单位和原子转移概率确实属于同一 $\Omega$ |
| 不等直和与空间复合 | V95 定理 2.1、定义 8.6 的产品态、共同参考和空间边 | 产品准备、产品记录、空间边的实际供应 |
| 全原事件 CP/TNI | 全部有限参考延伸、定义 8.8、Watrous Theorem 2.22 | 参考准备和事件延伸对整个实际联合锥可调用 |
| 原记录的一 Kraus | C118 F、原细标签、(8.5) | 原标签端口、遗忘、返回和实现身份，不以数学指标替换 |
| 平方根/Lüders | 选定 $K=\sqrt E$、确定性参考输出、理想返回 | 该效果的原实际滤波设备和控制 |
| 原始成功词及失败叶 | 定义 8.12–8.14、C118 的原记录与支持返回 | 每一步的实际合法性、拒绝、密封和终止行为 |
| 连续 Hamilton 形式 | 独立的连续可逆一参数实现 | 时间、能量、共同单位和 $\hbar$ |

该表不把数学条件命名成物理实现，也不把 $\mathcal Q_{S,d}$ 的满足族当成给定 $\Omega$ 已满足 C120 的证明；给定整体若缺少任一列的实际供应，结论停在相应的条件边界。

**注记 8.22（项目结果与外部定理的精确接回）。** V95 定理 2.1 提供 C95 下的结合复乘法，V95 定理 5.2 提供其完整有限 $C^*$ 解释及有限张量—Kraus 接口；C120 只消费这些数学结论，并另外量化原准备、原效果和实际事件。C118 定义 120.1–120.2 给出原过程、原标签和 F，定理 122.1 给出实际细支的 CP 正常形，定义 140.1–141.2 给出原支撑返回、固定控制和有限校准，定理 143.1–143.2 给出有限闭行走的相容取向，定理 144.1 给出透明 CP 满足族，推论 147.1 给出在这些前件下的量子接口；C120 不把它们改写成新的分类定理。结构存储图册 [Native structural storage, support, and the terminal-boundary atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md) 的命题 2.1 和定理 2.2 只消费保留材料上的原端口、历史和实现身份提取。BBKM15 Proposition 3.1 的有限 projectivity、Proposition 5.1 的有限谱展开、Theorem 6.1/Appendix B 的同一效果空间原子映射，分别对应定义 8.2(2)、8.2(3)、8.3；BMU14 Definitions 13–14 和 Theorem 16 只在其逐项 purity 前件满足时消费；Watrous Definition 1.124、Theorem 2.22 只在定义 8.8 的全部有限参考正性和序生成准备锥满足时消费。

## 追加锚（本行以下为增补区）

## 9. C120 的完整原生合同：几何、参考与原实现

**定义 9.1（联合候选及第八节的条件范围）。** 本章至第十三章的 C120 指以下 A–F 的一个联合条件，量化同一整体 $\Omega$ 的全部原对象、原准备、原效果、原事件、原实现身份、原记录端口和全部合法有限历史。其起点是原响应，不是已经满足定义 1.1 的矩阵或比较场。定义 1.1 的全部条件将在同一原效果空间上取得后才调用定理 2.1。

第八节的载体、参考、原记录和滤波简写在这里分别具有以下确切条件：Jordan 桥必须消费纯射线保持；规范配对必须与原单位一起运输；参考正性作用于完整联合锥而非仅可分锥；一 Kraus 结论由原 F 的双侧支撑返回推出，不能把式 (8.5) 再当前提；平方根更新由第十一章的原词供应，不先假定它已在菜单内。第八节的唯一性只在固定原 Jordan 运算及原 $D$ 后成立，不由记录身份或 $J,u$ 单独决定。所谓准备的有限正组合不要求原准备集合有限；非经典矩阵锥不能由预选的有限条射线生成。非法接续不因有矩阵公式而成为原历史，也不自动成为实际失败事件。

**定义 9.2（A：原响应商、实际锥与合法性）。** 每个非零原对象 $o$ 的准备以其对全部原合法未来上下文的响应等价作商；未来上下文包括原读口、记录、控制、失败及可用性。设这个商的实线性包为有限维 $V_o$，原准备 $p$ 的未归一化响应为 $v_p$。要求

$$
C_o=\operatorname{cone}_{\rm fin}\{v_p:p\in\mathsf P_o\}
=\left\{\sum_{j=1}^m c_jv_{p_j}:m<\infty,\ c_j\ge0\right\}
\tag{9.1}
$$

是闭、尖、生成的凸锥。原确定终端效果延拓为严格正的 $u_o\in V_o^*$；$K_o=\{v\in C_o:u_o(v)=1\}$ 是数学归一化基。原效果给出的泛函分离 $V_o$，故张成 $E_o:=V_o^*$；$C_o^*$ 是其全对偶锥。原实际效果菜单只是一组有名字、有实现和读口的 $\mathsf E_o\subseteq[0,u_o]$，不把整个数学区间声明为一个实际测量菜单。

每个原事件 $x:o\to p$ 保持响应等价、凸混合与强度，诱导正线性映射 $T_x:V_o\to V_p$，满足 $u_pT_x\le u_o$；原确定事件取等号。每条原记录分支也满足这些条件。同一原设备的互斥分支求和、原标签遗忘和原合法复合在这些映射下保持。原合法有限历史集合 $\mathsf H$ 及各实现身份 $\iota$ 仍独立保留，映射相等不产生身份等式、端口或新合法接续。若操作依赖历史，历史与控制状态属于原事件的索引；不能把不同上下文压成一个无条件箭头。

式 (9.1) 是实质的完备响应假设：不以加上极限准备使锥闭合。数学上把一个非零响应除以其强度，只定义 $K_o$ 中的点，不宣称该归一化点已有系数一的实际准备。每个实际终止设备的全部失败分支、输出类型、标签和原终端效果留在签名中。只有原设备确实含拒绝分支时，拒绝才是一条实际历史。

**定义 9.3（B：实际双侧面滤子）。** 对 $C_o$ 的每个面 $F$，包括零面与全面，选择同一原系统中的实际成功事件 $\mathsf p_F$，其响应映射为 $P_F$。存在正幂等映射 $Q_F$，使

$$
\begin{gathered}
P_F^2=P_F,\quad Q_F^2=Q_F,\quad
\operatorname{im}_+P_F=F=\ker_+Q_F,\qquad
\operatorname{im}_+Q_F=\ker_+P_F,\\
\operatorname{im}_+P_F^*=\ker_+Q_F^*,\qquad
\operatorname{im}_+Q_F^*=\ker_+P_F^*,\\
u_oP_F\le u_o,\quad u_oQ_F\le u_o,\quad
P_F^*u_o+Q_F^*u_o=u_o.
\end{gathered}
\tag{9.2}
$$

这里 $\operatorname{im}_+P=\operatorname{im}P\cap C_o$，$\ker_+P=\ker P\cap C_o$，对偶式在 $C_o^*$ 上解释；$P^*e=e\circ P$。每个 $P_F$ 把纯态射线送到纯态射线或零。要求的是纯射线保持，不是把 $P_F$ 作为过程锥的极射线；特别不排除跨多个中心扇区的面。

$\mathsf p_F$ 是一个实际可调用、已终止设备的成功分支，设备的所有失败叶均有原记录。其两种使用——单独调用及下文指定的参考接续——在 $\mathsf H$ 中。式 (9.2) 不要求 $P_F+Q_F=I$，也不声称两个分别可调用的面分支已经装在同一个实际测试中。原参考旁的行动在未归一化层面按张量恒等解释，不把相关旁观系统替换为乘积态。

**定义 9.4（C：原子互易）。** 对数学归一化纯态 $\omega$，令 $F_\omega=\mathbb R_+\omega$。幂等性给

$$
P_{F_\omega}v=e_\omega(v)\omega,\qquad
 e_\omega=P_{F_\omega}^*u_o,\qquad e_\omega(\omega)=1.
$$

要求所有纯态对满足 $e_\omega(\nu)=e_\nu(\omega)$。这里的纯态与原子效果属于原响应商与全数学对偶；不增加强对称、跨不等扇区的传递性或独立 signed spectrality。

**命题 9.5（选定 B 恰好覆盖源定理的滤子量词）。** A–C 满足 [Barnum–Müller–Ududec，arXiv:1403.4147v4，Definitions 13–14 及 Theorem 16](https://arxiv.org/html/1403.4147v4) 的有限 projectivity、对称转移概率及全部滤子的纯性保持。

证明。有限维闭尖生成锥及严格正单位给出该文的 base-norm state space。对正幂等 $P$，$P(C_o)=\operatorname{im}_+P$：一个方向由正性，反向由 $Py=y$。式 (9.2) 的前两行正是 Definition 13 的互补与 dual-complemented；第三行给 Definition 14 的 normalization，因而每个 $P_F$ 都是该定义的 filter，每个面由它覆盖，得到 projectivity。

现在直接消费 [Barnum–Barrett–Krumm–Müller，arXiv:1508.03107v2，§3.1 Proposition 3.1](https://arxiv.org/html/1508.03107v2)：有限 projective 系统的面、滤子及 projective unit 一一对应。故任何源定义下的 filter 都等于它的面上已选的 $P_F$，不是另有一族未经 B 约束的滤子。B 的纯射线保持已覆盖它们全部，无须再添一个全称纯性前件。该双射也把纯态 $\omega$ 与原子 projective unit $e_\omega$ 配对，C 就是 BMU16 的 STP。零输出符合 BMU16 中“非负倍纯态”的定义。BMU16 因而适用；不调用其 Theorem 17 的强对称路线。∎

**定义 9.6（D：原效果上的有向三元相容）。** 由命题 9.5 的 Jordan 桥及定理 10.1 的规范运输，在原效果空间 $E_o$ 上记单位为 $u_o$、Jordan 乘法为 $\circ_o$。原有向关系另供实线性指派

$$
D^o:E_o\longrightarrow\operatorname{Der}(E_o,\circ_o),\qquad
([L_a,L_c]+[D_a,D_c])b=0\quad(a,b,c\in E_o).
\tag{9.3}
$$

这是对尚未选择矩阵坐标的原关系之条件。$D$ 不是从重构后的矩阵交换子回填。导子性质与式 (9.3) 是独立输入；反对称、自守及正 Frobenius 配对不是另加输入。

**定义 9.7（E：原复合、原产品作用与两类参考资源）。** 每个已声明原独立复合 $op$ 及其有限迭代自身满足 A–D。原局部效果的嵌入延拓为含幺实 Jordan 嵌入 $j_o:E_o\to E_{op}$、$j_p:E_p\to E_{op}$，在局部保留 $D$，且

$$
D_{j_o(a)}j_p(b)=D_{j_p(b)}j_o(a)=0.
\tag{9.4}
$$

局部 Jordan 乘积 $j_o(a)\circ j_p(b)$ 实线性张成 $E_{op}$。原产品准备与产品读口保留其名字和强度，双线性延拓为 $v\boxtimes w$，满足

$$
\langle j_o(a)\circ j_p(b),v\boxtimes w\rangle
=\langle a,v\rangle\langle b,w\rangle.
\tag{9.5}
$$

产品准备的存在首先对原准备给定，再由有限正组合延拓；联合准备锥自身仍为式 (9.1)，一般严格包含产品准备生成的可分锥。不同括号及置换的实际比较若已声明，必须保留同名产品统计和原端口。

正性测试资源为一个原不可约秩二非经典参考 $R$ 及任意有限多个独立副本 $R^{\boxtimes n}$。每个原事件——包括复合对象事件、标签分支、原遗忘及指定返回——均有原实现的实际旁置延伸 $x\parallel\operatorname{id}_{R^{\boxtimes n}}$。它保留全部原记录及原产品输入作用：

$$
T_{x\parallel\mathrm{id}}(v\boxtimes w)=T_x(v)\boxtimes w.
\tag{9.6}
$$

延伸在整个实际联合准备锥 $C_{oR^{\boxtimes n}}=\operatorname{cone}_{\rm fin}\mathsf P_{oR^{\boxtimes n}}$ 上保正；不只在可分输入上保正。此条件对每个有限 $n$ 成立，绝非只检验一个 qubit。

滤波词资源另要求 $R$ 有原确定性纯准备 $b_0$，$u_R(b_0)=1$，及原确定性丢弃。对任意目标对象，接入 $b_0$、调用 B 在目标与 $R$ 上的两次指定面设备、再丢弃参考及原条件分支控制，均为实际合法接续；对已声明旁观系统也有保持原产品作用的局部延伸。系数一准备与前段的全锥正性资源是不同要求，不能用一个仅有非零成功率的参考准备替代。

**定义 9.8（F：同一实现的原细记录与指定双返回）。** 在定理 10.2 的载体上，支撑、中心及角均按同一原效果空间的运输解释。每个原实际成功箭头 $x:o\to p$ 有同一实现的原有限细标签端口及实际遗忘

$$
\widehat T_x(v)=(S_{x,\lambda}v)_{\lambda\in\Lambda_x},\qquad
 d_p\widehat T_x=T_x=\sum_{\lambda\in\Lambda_x}S_{x,\lambda}.
\tag{9.7}
$$

每个非零 $S=S_{x,\lambda}$ 有原指定实际返回 $U$、原正数 $q$ 以及位于单一原中心块内的非零支撑 $P,Q$，与 [C118，定义 140.1，式 (140.2)–(140.5)](AURIC_COMPOSITE_COMPARISON_REFERENCE_FREE_FILTER_RELATIONS_V96_CONTINUATION.md) 完全相同：

$$
\begin{gathered}
P=\operatorname{supp}S^\dagger(I),\quad
Q=\operatorname{supp}S(I),\quad
S(X)=QS(PXP)Q,\quad U(Y)=PU(QYQ)P,\\
US(X)=qX\ (X\in P\mathcal A_oP),\qquad
SU(Y)=qY\ (Y\in Q\mathcal A_pQ).
\end{gathered}
\tag{9.8}
$$

$U$ 是原 TNI 事件；反向资料也留在指定族中。F 量化原标签箭头、遗忘、返回及全部合法有限接续。零支不需返回。它没有预设 Kraus 秩，也不把数学 Kraus 指标当作原记录。

所有继承的指定返回、准确校准、控制词及有限回路资料连同其原实现、原成功因素和读口均保留。它们原来声明的等式或统计条件仍按同一原词解释；不能用另一台同效果设备顶替。新构造词拥有自己的实现身份。这个保留条件不由“两个矩阵相等”产生新的原端口，也不要求原先未供应的 C118 校准包已经存在。

## 10. 规范运输、原张量与全原事件

**定理 10.1（原单位及规范 Frobenius 配对）。** A–C 在同一个原效果空间 $E_o$ 上给出 Euclidean Jordan 代数结构，单位恰为 $u_o$，平方锥恰为 $C_o^*$。存在规范序同构 $\phi_o:E_o\to V_o$，使

$$
\phi_o(e_\omega)=\omega,\qquad
g_o(a,b)=\langle a,\phi_o(b)\rangle
=\tau_J(a\circ b),\qquad \tau_J(a)=g_o(u_o,a),
\tag{10.1}
$$

其中 $\tau_J$ 是每个原始幂等元迹为一的 Jordan 迹。$g_o$ 正定，并满足 $g_o(a\circ b,c)=g_o(b,a\circ c)$。对原准备 $v$，其 Jordan 密度为 $r_v=\phi_o^{-1}v$，且

$$
r_v\in C_o^*,\quad u_o(v)=\tau_J(r_v),\qquad
\langle a,v\rangle=\tau_J(a\circ r_v).
\tag{10.2}
$$

证明。命题 9.5 逐项满足 BMU16 的 (a) projectivity、(b) STP、(c) purity preservation，直接得到 formally real Jordan state space。取其保归一化基的序表示，对偶为含幺序表示 $\theta:E_o\to J$，把原 $u_o$ 送到 $1_J$，把全对偶锥送到 Jordan 平方锥。Jordan 的规范谱理论把 projective units 送到幂等元；原滤子的唯一性来自 BBKM Proposition 3.1，因而原子 $e_\omega$ 送到原始幂等元 $p$。该原子的唯一归一化支持态就是 $a\mapsto\tau_J(\theta(a)\circ p)$。这准确对应原 $\omega$，没有扇区权重的自由缩放。

BBKM Proposition 5.1 在有限 projectivity 下给效果的正交 projective-unit 谱展开；把每个单位有限细分为原子，原子张成 $E_o$。BBKM Theorem 6.1 及其 Appendix B 给唯一线性正映射 $\phi_o(e_\omega)=\omega$，并证明它是序同构、$g_o$ 为正定对称内积、全部 compressions 对它自伴随。其假设只是有限 projectivity 与 STP，不需要额外 state spectrality。令 $R_J$ 为规范 Jordan 迹的 Riesz 映射，刚才的原子对应表明

$$
\phi_o=\theta^*R_J\theta.
$$

等式在原子上成立，故在整个 $E_o$ 成立。这给出 (10.1)，而非只取得一个任意自对偶内积。特别 $\phi_o(u_o)$ 对应未归一化的 Jordan 单位，$u_o(\phi_o(u_o))=\tau_J(1_J)$ 为总秩。原归一化泛函仍是原 $u_o$，不是把此总秩误当作准备成功率。Jordan 迹的结合性给 Frobenius 恒等式，(10.2) 随之成立。

此处的乘法可通过幂等谱平方与极化在 $E_o$ 上运输：$a=\sum_i\lambda_ip_i$ 时 $a^2=\sum_i\lambda_i^2p_i$，再取 $a\circ b=((a+b)^2-a^2-b^2)/2$。保幺序表示保持这些谱投影，故结构不依赖 $\theta$ 的选择。这里的谱展开与 Jordan 分类均直接消费所引成熟定理，不另立强对称或 signed spectrality。∎

**定理 10.2（同一原响应的有限复载体）。** A–D 对每个非零原对象给出

$$
\mathcal A_o=\bigoplus_{s\in S_o}M_{d_s}(\mathbb C),\qquad
\kappa_o:E_o\longrightarrow(\mathcal A_o)_{\rm sa},\qquad
\sigma_o=\kappa_o\phi_o^{-1}:V_o\longrightarrow(\mathcal A_o)_{\rm sa}.
\tag{10.3}
$$

$\kappa_o$ 保单位与锥，$\sigma_o$ 保准备锥，$\tau_o=\sum_s\operatorname{Tr}_{d_s}$ 满足

$$
\begin{gathered}
\kappa_o(u_o)=I_o,\quad \sigma_o(C_o)=(\mathcal A_o)_+,\quad
\kappa_o([0,u_o])=[0,I_o],\\
u_o(v)=\tau_o(\sigma_o v),\qquad
\langle a,v\rangle=\tau_o\bigl(\kappa_o(a)\sigma_o(v)\bigr).
\end{gathered}
\tag{10.4}
$$

任意有限个不等阶非经典块均被允许。固定 $E_o,\circ_o,u_o,D^o$ 后载体唯一到其保资料 $*$-同构；表示同构不认同任何两个原实现。

证明。把定理 10.1 的 $(E_o,u_o,g_o,\circ_o)$ 和原 $D^o$ 逐项代入本卷定义 1.1：非零、有限维、含幺、正定、Frobenius、线性导子指派全部已满足。定义 9.6 正是 C95，故直接消费本卷定理 2.1，得到

$$
a\cdot b=a\circ b-iD_ab,\qquad D_ab=-D_ba,
$$

以及忠实有限维正 $*$ 表示。有限维复 $C^*$ 结构定理给 (10.3)。其自伴随平方就是 Jordan 平方，故同一个 $C_o^*$ 成为矩阵正锥。原始 Jordan 幂等元在每个矩阵块中为秩一投影，所以定理 10.1 的规范迹正是未加扇区权重的 $\sum_s\operatorname{Tr}_{d_s}$；(10.4) 从 (10.2) 运输而来。没有用一个任意 Frobenius 配对来猜原单位或 Born 评价。本卷定理 2.1 的乘法与表示结论在这里直接应用，不重新证明其曲率论证。∎

**命题 10.3（每个原选面设备的运输）。** A–D 下，令 $p_F=\kappa_o(P_F^*u_o)$，则 $p_F$ 是投影，且

$$
\sigma_oP_F\sigma_o^{-1}(X)=p_FXp_F.
\tag{10.5}
$$

$Q_F$ 对应 $(I-p_F)X(I-p_F)$。这包括跨中心的面、零面和全面；原实现仍分别为指定的 $\mathsf p_F$ 及其原失败设备。

证明。BBKM Theorem 6.1/Appendix B 的 compression 对规范配对自伴随，给 $P_F\phi_o=\phi_oP_F^*$。Jordan 表示中的面滤子为 Peirce 二次压缩 $2L_{p_F}^2-L_{p_F}$，由 Proposition 3.1 的双射它恰是原选中的滤子，而非另一个同面过程。在定理 10.2 的 special Jordan 代数中该二次压缩就是 $X\mapsto p_FXp_F$。这是标准 Jordan compression calculus，亦见 [原生切分 Atlas，定义 28.1、定理 28.2 的 slit 合同](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md)。这里只消费其压缩公式，不消费该定理的强对称与简单性分类。∎

**定理 10.4（原空间复合及统计相干性）。** A–E 下，每条已声明原空间边有保持原单位、原产品统计与全中心的 $*$-同构

$$
\mathcal A_{op}\simeq\mathcal A_o\otimes_{\mathbb C}\mathcal A_p
=\bigoplus_{s,t}M_{d_sd_t}(\mathbb C),\quad
\sigma_{op}(v\boxtimes w)=\sigma_o(v)\otimes\sigma_p(w).
\tag{10.6}
$$

原产品事件的延伸在整个联合空间上是同一个 $\mathcal T_x\otimes\mathrm{id}$，其中 $\mathcal T_x=\sigma_pT_x\sigma_o^{-1}$。原记录、产品输入作用及既有括号比较都被保留。

证明。E 的局部 Jordan 嵌入保留 $D$，所以由定理 10.2 的乘法公式延拓成复含幺 $*$-嵌入；式 (9.4) 使两像交换。E 的张成性和式 (9.5) 正好是本卷定义 1.3、定理 5.2 张量论证的“交换、生成、产品态分离”三项前件。对数学局部态，式 (9.1) 将原产品准备有限线性延拓为相应产品正泛函，足以消费该分离论证，取得 (10.6)，不另重证分类或复张量唯一性。规范迹及 (9.5) 给密度的产品公式。

产品密度线性张成联合自伴部，因此原延伸式 (9.6) 唯一确定整个延伸，而非仅给一个任意的局部兼容映射。迭代复合的产品效果仍按同一因子表标记；既有括号比较保持这些统计。直接消费 [Atlas 命题 30.1](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md)，它的局部 tomography 在此由 E 的张成性给出，故全部已给比较相干，包括五边形。维数相等不替代这一条件，也不凭同构创造实际比较设备。∎

**定理 10.5（全部原事件的 CP、TNI 与数学 Kraus）。** A–E 下，每个原事件及其原标签分支在 (10.3) 的同一取向中完全正且迹不增：

$$
\mathcal T_x(X)_t=\sum_{s,\mu}K^x_{ts\mu}X_sK^{x*}_{ts\mu},\qquad
\sum_{t,\mu}K^{x*}_{ts\mu}K^x_{ts\mu}\le I_{d_s}.
\tag{10.7}
$$

原确定事件取等号。$\mu$ 是数学指标，其可访问性尚未由本定理给出。

证明。不可约秩二参考在定理 10.2 下为 $M_2(\mathbb C)$；定理 10.4 把 $n$ 个原副本送到 $M_{2^n}(\mathbb C)$。给定任一输入块维数 $d_s$，选有限 $n$ 使 $2^n\ge d_s$。原延伸在整个实际联合锥上正，(9.1)、(10.4) 把该锥精确送到全矩阵正锥，所以 $\mathcal T_x\otimes\mathrm{id}_{2^n}$ 保正；限制到参考的一个 $d_s$ 维角，便得每个输入输出块的 $d_s$-positive 映射。

这恰满足 [Watrous，*The Theory of Quantum Information*，§1.1.2 式 (1.124) 的 CP 定义及 Theorem 2.22](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf) 的有限输入维判据。原文 (1.124) 是定义中的公式号，不是独立编号 Definition 1.124。Theorem 2.22 对每个非零块给 CP、Choi 正性和有限 Kraus 表示；零块用空和。A 的 $u_pT_x\le u_o$ 经 (10.4) 给式 (10.7) 的效果不等式。本证明需要任意有限多个参考及全联合锥；仅产品准备正性，或只一份二阶参考，不满足这个判据。∎

**定理 10.6（由原 F 返回导出的原标签一 Kraus）。** A–F 下，每个非零原细标签有一个从原单一输入块到原单一输出块的算子 $K_{x,\lambda}$，使

$$
S_{x,\lambda}(X)=K_{x,\lambda}XK_{x,\lambda}^*,\qquad
U(Y)=qK_{x,\lambda}^{+}Y K_{x,\lambda}^{+*}.
\tag{10.8}
$$

在支撑外均补零，$P=K^+K$、$Q=KK^+$，原 $q$ 满足 $0<q\le\lambda_{\min}^+(KK^*)$。原同一设备的遗忘仍为式 (9.7)，没有增加不可读的数学标签。

证明。定理 10.5 适用于 $S$ 和原 $U$。式 (9.8) 完全是 C118 定义 140.1 的指定单中心双侧返回资料，故直接消费该卷定理 121.1、式 (140.4) 的支撑正常形：两角同阶，$G=S(I)$ 在输出角内正定，$S=\operatorname{Ad}_{G^{1/2}}\beta$，$\beta$ 是两角间的含幺 Jordan 保星同构。CP 的 $S$ 使 $\beta$ CP；阶数至少二的反乘法方向含转置，其 Choi 算子在反对称子空间为负，因而被 Watrous Theorem 2.22 排除。一阶无可分方向。因此 $\beta$ 是矩阵保星同构，由支撑间酉算子 $W$ 实现，$K=G^{1/2}W$ 给第一式。此处消费 C118 的正常形，不重做其正逆分类。

式 (9.8) 把原 $U$ 唯一固定为第二式；它的 TNI 条件是 $q(K^+)^*K^+\le Q$，等价于上述特征值界。原记录 $\lambda$ 在调用 F 时已给，(10.8) 只是其响应表示，故式 (9.7) 保持同一实现、同一细标签与原分组。原 $q$ 不被换成某个较方便的缩放数。∎

**定理 10.7（全部原词、记录与原始成功的运输）。** 在 A–F 下，对每条原合法有限历史 $h$、每组原标签 $\boldsymbol\lambda$、每个原终端效果 $e$，包括成功和失败，均有

$$
p_\Omega(h,\boldsymbol\lambda,e\mid v)
=\tau_{o_n}\!\left[\kappa_{o_n}(e)\,
\mathcal T_{x_n,\lambda_n}\cdots\mathcal T_{x_1,\lambda_1}\sigma_{o_0}(v)\right].
\tag{10.9}
$$

命名原支持、返回因素、校准、控制词及有限回路的原概率也保持。原词是否合法、哪个设备产生记录，仍由 $\Omega$ 给定。

证明。每个运输映射定义为 $\mathcal T_x=\sigma_{\rm out}T_x\sigma_{\rm in}^{-1}$，合法接续的中间 $\sigma^{-1}\sigma$ 消去，末端用 (10.4)。这就是 C118 定理 143.1、147.1 的原记录与有限词运输论证在同一个原响应实现中的直接应用；对原标签求和与遗忘由 A、F 保持。它适用于任意有限长度及所有原失败叶，不按长度截断。正概率下的条件概率可事后相除，但不改变式 (10.9) 的原始成功系数；零概率不定义条件态。

这里没有重新选择各箭头的相容取向。原 $D$ 与 E 的嵌入已经固定同一复乘法，参考合同使原事件在这个乘法中 CP。所有指定返回因此为保乘法方向，有限闭行走的符号积为正；若一个原 C118 包已实际满足其定义 141.1–141.2，便可直接消费 C118 定理 143.1 及 142.2 的相应回路结论。CP 表示自身不供应未给的校准准备、控制词、端口或包；已经命名的同效果设备仍需其原校准。∎

## 追加锚（本行以下为增补区）

## 11. 实际精确效果滤波、原失败树与支撑返回

**定理 11.1（由原面设备组成的系数一效果滤波）。** A–E 下，对每个原非零对象及每个数学效果 $0\le E\le I_o$，同一个 $\Omega$ 内有一个由原设备组成的合法有限成功词 $W_E$，其原始成功映射精确为

$$
\mathcal W_E(X)=\sqrt E\,X\sqrt E,\qquad
p_{\rm raw}(W_E\mid X)=\tau_o(EX).
\tag{11.1}
$$

这是对所有效果、所有输入块与每次原合法使用成立的实际词供应，不是先给定矩阵载体后的一个局部兼容声明。词有自己的原实现身份；不会把已命名的另一台同效果设备改成它。

证明。使用 E 的确定性参考准备 $b_0$，在定理 10.2 的 $M_2(\mathbb C)$ 表示中把它记为 $|0\rangle\langle0|$。在已由定理 10.4 识别的原对象 $oR$ 中，令

$$
 a=\sqrt E,\qquad b=\sqrt{a(I-a)},\qquad
 p=\begin{pmatrix}a&b\\ b&I-a\end{pmatrix},\qquad
 q=I_o\otimes|0\rangle\langle0|.
\tag{11.2}
$$

$a,b$ 是同一个 $a$ 的连续函数，故相互交换。块乘法给

$$
 p^*=p,\quad
 p^2=\begin{pmatrix}a^2+a(I-a)&ab+b(I-a)\\
ba+(I-a)b&a(I-a)+(I-a)^2\end{pmatrix}=p.
$$

这里是在重构后定位两个原面的参数；实际调用的是 B 已给的原面事件，未另加一台矩阵设备。由命题 10.3，它们分别为 $Y\mapsto pYp$ 与 $Y\mapsto qYq$。调用 E 明确允许的原词

$$
 W_E=(\text{接入 }b_0)\ ;\ \mathsf p_{F_p}\ ;\
 \mathsf p_{F_q}\ ;\ (\text{丢弃 }R),
\tag{11.3}
$$

两次取原成功分支。由于

$$
 p(X\otimes|0\rangle\langle0|)p
 =\begin{pmatrix}aXa&aXb\\bXa&bXb\end{pmatrix},\qquad
 q\,p(X\otimes|0\rangle\langle0|)p\,q
 =aXa\otimes|0\rangle\langle0|,
$$

原确定性丢弃给 (11.1)。整个构造逐原中心块成立；$p$ 可以跨多个不等大小块，而 B 没有要求它是极过程。式 (11.2) 是标准投影膨胀的一个块构造，投影膨胀本身不作新内容；这里的承重对应是两块投影恰有 B 的原面设备，并由 E 供应同一原合法词、系数一准备及丢弃。

若只给成功率为 $\eta$ 的原参考准备，第一步为 $X\mapsto\eta X\otimes|0\rangle\langle0|$，同词的成功映射就是 $\eta\sqrt E X\sqrt E$。事后条件归一化不能消掉原始成功率中的 $\eta$。∎

**命题 11.2（相关旁观者、零效果与奇异效果）。** 对已声明原旁观对象 $z$，定理 11.1 的局部延伸在每个实际相关输入 $X_{oz}$ 上为

$$
 (\mathcal W_E\otimes\mathrm{id}_z)(X_{oz})
 =(\sqrt E\otimes I_z)X_{oz}(\sqrt E\otimes I_z).
\tag{11.4}
$$

$E=0$ 时成功映射为零；$E=I_o$ 时为恒等。奇异 $E$ 不需正则化，仍由式 (11.2) 定义。成功概率为零时没有条件态。

证明。E 已要求该词的实际局部延伸保持原产品输入作用；定理 10.4 的张成性使其在整个联合空间上就是张量恒等延伸，故式 (11.4) 对相关输入成立。旁观者的未归一化边缘可随筛选改变，不能把此结论说成筛选后旁观者密度不变。$a=0$、$a=I_o$ 或 $a$ 有零特征值时，式 (11.2) 仍为投影，前一证明的多项式恒等式不变。∎

**定义 11.3（同词的完整实际失败树）。** 设 (11.3) 第一台原面设备的失败分支为 $A_\alpha$，第二台的失败分支为 $B_\beta$，各有其原输出类型与终端效果。令 $i_0$ 为原确定性参考接入。这个词的叶包括：

- 第一台失败：$A_\alpha i_0$，记录原 $\alpha$，不调用第二台；
- 第一台成功、第二台失败：$B_\beta P_{F_p}i_0$，保留顺序成功标记及原 $\beta$；
- 两台成功：$\operatorname{discard}_R P_{F_q}P_{F_p}i_0$，即 $\mathcal W_E$。

任何实际细标签也保留在所属叶中，只有原供应的遗忘端口能合并它们。失败设备不被替换为数学补滤子。终止设备的“全部叶”还包括它原有的其他终止结果；不以 $Q_F$ 的存在声称两次面测试有共同二元仪器。原准备若另有失败，接入准备的失败叶也须在树首保留。

**命题 11.4（原始成功与失败树的有限闭包）。** 对任意由 E 指定允许接续的有限效果词 $W_{E_n}\cdots W_{E_1}$，成功映射为

$$
 X\longmapsto A_wXA_w^*,\qquad
 A_w=\sqrt{E_n}\cdots\sqrt{E_1},\qquad
 p_{\rm raw}(w\mid X)=\tau_o(A_wXA_w^*).
\tag{11.5}
$$

所有首个失败位置及该处原失败标签都在原树中；归一化输入的全部终止叶概率之和为一。原词的记录组合、旁置、有限分组和原遗忘保持原身份及各叶强度。

证明。成功支是实际映射的复合，式 (11.1) 给 (11.5)，没有在中间除以成功概率。每次原终止设备的所有分支在终端效果下守恒；按第一失败位置展开有限树，逐节点以输入强度等于各子叶强度之和代入，便得总叶强度等于根强度。失败可能有不同输出类型，用各自原终端效果求强度，不把不同类型的失败映射相减。记录复合与遗忘直接消费 A 的原闭包及 C118 的同记录有限词论证。

若两个词的原控制、端口、支撑或权限不容许接续，它们不在 $\mathsf H$，本命题不供应这个接续。只有实际定义了“非法请求的拒绝设备”时才多一条拒绝叶。这样保留全部合法有限历史与全部实际失败，而不通过一个矩阵延拓扩大原操作域。∎

**定理 11.5（实际效果滤波的正确缩放双侧支撑返回）。** 对非零效果 $E$，令 $p_E=\operatorname{supp}E$，选任意

$$
 0<c\le\min\bigl(\operatorname{spec}(E)\setminus\{0\}\bigr),\qquad
 H=cE^+\le p_E\le I_o.
$$

定理 11.1 对 $H$ 供应原成功词 $W_H$，并有

$$
 \mathcal W_H\mathcal W_E=\mathcal W_E\mathcal W_H
 =c\,\operatorname{Ad}_{p_E}.
\tag{11.6}
$$

两词及其所有失败叶均实际供应。$E=0$ 单独取零成功支，不给正返回因素。这个构造给新词的支撑返回，不替代任何已命名原设备的原指定返回。

证明。$\sqrt H=\sqrt c\,E^{+1/2}$ 为收缩，且它与 $\sqrt E$ 的两个乘积均为 $\sqrt c\,p_E$，所以 (11.6) 成立。$H$ 在全部中心块上是合法效果，故可再次用定理 11.1；原词接续由 E 供应。奇异时只在支持角上回到原输入并带因素 $c$，不是对核的逆，也不是成功率一的全空间逆。

对一般原细支，定理 10.6 保留的是其已给 $q$ 与 $U=q\operatorname{Ad}_{K^+}$；合法范围为 $q\le\lambda_{\min}^+(KK^*)$。即使另能构造同一个返回映射，也不能把原 $U$ 的实现身份换成新词。∎

## 12. 全有限直和满足族与身份保持的 F 删除模型

**定义 12.1（透明有限 Kraus 原设备语言）。** 对每个有限正整数列表 $(d_s)_{s\in S}$ 纳入一个原对象

$$
 \mathcal Q_{S,d}=\bigoplus_{s\in S}M_{d_s}(\mathbb C),
$$

并纳入其全部声明的标准复张量对象、有限经典标签直和及标量终端对象。列表允许不等阶块。原准备含每个单块的全部归一化秩一态；原有限混合也可作有独立名字的准备。对每个数学效果供应一个有名字的原二元读口；这只是本满足族的菜单选择，不反向强化 A 的一般效果假设。

一个透明基本设备由独立实现名 $\iota$、有限结果集合、各结果输出类型、有限算子表

$$
 K_{j,t,s,\mu}:\mathbb C^{d_s}\to\mathbb C^{e_{j,t}},\qquad
 \sum_{j,t,\mu}K_{j,t,s,\mu}^*K_{j,t,s,\mu}=I_{d_s}
\tag{12.1}
$$

以及实际端口组成。它真实暴露原细标签 $(j,t,s,\mu)$，也有指定分组 $j$ 及标签遗忘端口。只看 $j$ 的设备仍是这同一实现，原细端口可在其原记录处访问；不是事后找另一份 Kraus 分解。每个有限 CP/TNI 成功映射都可选这种透明实现：取其有限块 Kraus 表，把剩余正效果作为一个到标量失败终端的效果分支，得到式 (12.1)。这一步直接消费 Watrous Theorem 2.22 的数学表和这里明定的透明原端口供应。

语言由这些基本设备、确定性纯准备、原记录视图及遗忘、原条件控制、有限合法顺序复合、独立标准张量、确定性丢弃及恒等生成。每个语法节点都有原身份与所属端口；语言不对“响应映射相等”取商。复合节点的细记录为各步原记录的有限树，分组及忘记仅作用于已有端口。对每个非零细分支算子 $K$，指定其原支持 $P=K^+K$、$Q=KK^+$，并在基本设备集中纳入实际返回

$$
 U_K=q_K\operatorname{Ad}_{K^+},\qquad
 0<q_K\le\lambda_{\min}^+(KK^*),
\tag{12.2}
$$

及其原终止失败设备、反向资料和返回的透明细端口。对新复合细分支的非零算子积与张量积同样指定 (12.2)。这项闭包是集合的定义，不是有限算法或枚举要求；每台设备、每条原历史及每次所用的记录表仍有限。

原丢弃可以选为有实际有限细记录并最终遗忘的透明迹设备。每个 $P_F$ 取逐原中心块的 $p_sXp_s$，细记录暴露原中心块；其粗成功分支仍是整个 $pXp$，不要求它是一个极过程。参考延伸是带原节点名的指定语法构造，算子表为 $K_{j,t,s,\mu}\otimes I_R$，原设备的标签与分组完全不变。

**定理 12.2（所有有限复矩阵直和及标准复合的满足族）。** 定义 12.1 的原系统满足 A–F，保留其全部原设备、原记录和有限合法历史，并实际实现定理 11.1–11.5。可另纳入 C118 已有完整 CP 模型的准确校准、控制和返回资料；这些原实现及其所有有限闭环保持原统计。

证明。秩一态的有限正组合恰为矩阵正锥，这是有限维谱定理的直接应用，不增补极限准备。全原效果分离密度矩阵，故 A 的原响应商就是各对象的自伴随部；其原单位为迹。每个正锥面由一个块投影 $p$ 支撑，$P_F=\operatorname{Ad}_p$、$Q_F=\operatorname{Ad}_{I-p}$ 为 BMU Definitions 13–14 的滤子，满足 (9.2)。它们对单扇区秩一态输出秩一或零，STP 为两个秩一投影的迹配对对称性。故 B、C 全部成立。

在模型的原效果空间上明确给 $a\circ b=(ab+ba)/2$、$D_ab=i[a,b]/2$。这是验证满足性的原关系选择，不是在一般重构中回填 $D$。这些关系满足本卷定义 1.1 和 C95；可直接消费本卷定理 2.1、5.2 的矩阵端点。标准局部嵌入与张量产品满足 E 的乘法、$D$、交叉零、张成和原产品统计。$R=M_2(\mathbb C)$ 的任意有限副本全在对象集中；原全部联合纯准备的有限正锥是完整联合正锥，透明 $K\otimes I$ 延伸在该锥正且保持原记录。纯参考准备与丢弃确定性，故 E 的两类资源分别成立。

每个透明原细标签的 $K$ 只连一个输入与一个输出中心块，(12.2) 是 CP/TNI。Moore–Penrose 恒等式给

$$
 U_K\operatorname{Ad}_K=q_K\operatorname{Ad}_P,\qquad
 \operatorname{Ad}_KU_K=q_K\operatorname{Ad}_Q,
$$

准确保留原 $q_K$，满足 F。零算子保留零标签而无正返回。两个细分支复合的算子为 $LK$，张量为 $K\otimes L$，有限分组仍是原有限 Kraus 和，所有实际失败分支由 (12.1) 保留。对这些新词，定义 12.1 已供应其原细树及相应返回，所以 F 对整个闭包成立，不只对基本设备成立。

原标签遗忘从每个原标签副本回原块的限制为恒等；它自身有按输入标签及原中心块的透明细记录与支撑返回。准备、丢弃和条件控制也取同类透明实现，故量词没有漏掉这些箭头。所有同名原记录和失败叶的统计由定理 10.7 保持。C118 的完整透明 CP 满足族直接见该卷定理 144.1；若把其准确校准和控制词作为本模型的原语或原复合词纳入，原同设备条件及有限回路照原定理消费，不移植 C113 的近似或单正支校准。∎

**命题 12.3（全部前件可保留的 F 删除模型）。** 从 A–F 删除“每个原实现均有 F 的细端口与返回”这一全称要求，可保留 A–E、全部已指定透明返回、校准、控制、原合法闭包与原参考延伸，而有一台原设备缺少 F。其反例是实现身份与端口供应的反例，不含非 CP 事件。

证明。在定理 12.2 的整个透明系统中加入一个新原基本设备 $\Theta$，身份与任何透明实现均不同。它是 qubit 上的确定性振幅阻尼通道，取 $0<\gamma<1$，

$$
 A_0=|0\rangle\langle0|+\sqrt{1-\gamma}|1\rangle\langle1|,
 \quad A_1=\sqrt\gamma|0\rangle\langle1|,\qquad
 \Theta(X)=A_0XA_0^*+A_1XA_1^*.
\tag{12.3}
$$

该原基本设备只暴露一个确定结果和量子输入输出，没有原可访问内部细端口。式 (12.3) 的两个数学指标不是其设备端口。对它及其所有旁置延伸，密封属性随该原语节点保留；参考延伸为同一节点的 $\Theta\otimes\mathrm{id}$，其外部原记录仍只有确定结果。

将语言按定义 12.1 的所有有限语法构造闭合，严格保留构造树与每个节点的实现名。可访问端口的归纳规则只有：读基本透明节点的已给端口；读复合、测试或条件控制新产生的外部端口；对已可访问端口重标记、分组或遗忘。不存在从映射矩阵提取端口的规则，也不存在把节点换成同映射透明节点的等式。因而归纳于构造树，没有任何规则产生一个归属于密封 $\Theta$ 节点的细端口。前后加测试、随机标签或反馈会产生不同实现树；它们不是 $\Theta$ 自身的原细记录视图。这给出身份保持的语言闭包证明，而不只是“环境不可见”的口头说法。

所有语言节点仍为 CP/TNI，有限量子对象、原效果及全联合准备锥不变，故 A–E 及全部参考延伸保持。全部原透明面设备、其失败、原参考确定准备和指定透明返回资料均未被替换；新语言不强迫对 $\Theta$ 命名一份不存在的支撑返回。原透明控制词与校准包仍逐字为同一节点树，所以它们的全部已指定有限回路统计保持。

$\Theta$ 不能以其唯一可见分支履行 F：$\Theta(|1\rangle\langle1|)$ 在两条正交射线上都有严格正权重，故不是一 Kraus 映射；它在单块的输入、输出支持均为全 qubit。若存在 (9.8) 的原 CP 双返回，定理 10.6 的支撑正常形会强制一 Kraus，与此矛盾。任何透明的同通道实现拥有自己的两个实际端口，不能打开 $\Theta$ 的原端口。故该扩展满足删除 F 后的其余条款，而 $\Theta$ 违反 F。它不证明 F 的全局最小性，也不声称 B、E 或其他条件独立。∎

**命题 12.4（转置与测量—准备的局部障碍范围）。** 以下两个纸笔例子只针对各自所说的替代推理，不是其他全称条款的删除模型。

第一，在单块 $M_d(\mathbb C)$、$d\ge2$ 上，转置正且保迹，但不能满足 E 的完整参考稳定性。令 $|\Omega_d\rangle=\sum_j|j\rangle\otimes|j\rangle$，则

$$
 (\mathrm{transpose}\otimes\mathrm{id}_d)
 (|\Omega_d\rangle\langle\Omega_d|)=\mathrm{Swap}.
$$

交换算子在非零反对称向量上的二次型严格为负，所以此延伸不保正。它只驳斥“局部正性足够推出 CP”。

第二，qubit 上的原 Z 测量后遗忘设备

$$
 M(X)=|0\rangle\langle0|X|0\rangle\langle0|
      +|1\rangle\langle1|X|1\rangle\langle1|
$$

与恒等设备同效果 $I$，却在有非零非对角元的纯态上改变状态。因此“已知成功效果”不推出该原设备就是 $\operatorname{Ad}_{\sqrt E}$。这个例子本身可以透明且有 F，不能拿它证明缺少原细记录。只允许测量—准备的局部菜单也不能据此声称满足全部复合上的 B。两例证明分别由上述二次型及非对角元公式直接给出；不对未核对的其余全称条款作满足性声明。∎

## 13. 完整条件结论、量子接口与未消去的供应

**定义 13.1（零对象的独立约定）。** 若原签名允许零对象 $0$，单独取 $V_0=E_0=\{0\}$、$u_0=0$、$C_0=\{0\}$ 与零代数。它没有归一化基、纯态或非零返回，不调用本卷定义 1.1 的非零定理。含零因子的原复合为零；出入零对象的响应箭头为零映射，但原实现、原记录和合法性仍保留。非零对象到零对象的零箭头不是确定性终端丢弃，因为 $u_0T=0\ne u_o$；实际终端为标量对象。定义 12.1 的族可按此约定加入零对象。

B 的零面滤子是零事件，不是额外零对象。非零对象上的零效果、零准备和零细支仍由前文零映射分案处理；奇异非零效果保留支持及全部零特征方向。参考“秩二、不可约”在矩阵重构前指 projective-unit 正交格的最大原子分解长度为二且无非平凡中心分解，非预先声明一个复 Hilbert 维数。

**定理 13.2（一个完整的原生载体—实际供应条件候选）。** 对同一 $\Omega$ 的 A–F 及定义 13.1，存在对全部原非零对象共同给定的有限复直和载体及原响应运输，使：

1. 全部原准备、效果和单位按 (10.3)–(10.4) 表示，完整数学密度、正锥和 Born 配对成立；实际菜单、原强度与可用性仍各自保留。
2. 每个已声明原复合为 (10.6) 的标准复张量，对全部原有限参考和原相关输入成立；既有同产品统计的括号比较相干。
3. 全部原事件在此同一乘法中 CP/TNI；数学 Kraus 不增加记录。F 的每个原非零细标签有 (10.8) 的单算子、原支撑和原双返回因素；全部原有限合法词及失败叶满足 (10.9)。
4. 每个数学效果有实际原成功词 (11.3)，精确供应系数一的平方根滤波、全部失败树以及 (11.6) 的缩放支撑返回。它供应新词，不理想化另一台已命名同效果设备。
5. 定义 12.1–12.2 为所有有限复矩阵直和及其标准复合的完整满足族；命题 12.3 是保留其余明确条款的原 F 删除模型，命题 12.4 的两例只有所述局部范围。

证明。前四项分别是定理 10.1–10.7、11.1–11.5 的同一组运输与原词构造，所有中间对象都在同一 $\Omega$ 的声明域内；不存在把几个不同模型的分别可达结论拼作共同实现的步骤。第五项由定理 12.2 与命题 12.3–12.4 给出。零对象按定义 13.1 分案，故没有对它误用非零 V95。∎

**命题 13.3（量子接口与条件依赖）。** 定理 13.2 的依赖精确如下；表中“所得”均为所列前件下的数学或原词结论。

| 接口 | 消费的前件与源结果 | 所得及仍保留的独立输入 |
| --- | --- | --- |
| 原生 Jordan 几何 | A、B、C；BMU Definitions 13–14/Theorem 16；BBKM Proposition 3.1 | 所选 B 已穷尽全部滤子；任意有限 Jordan 直和可进入下一步。强对称不作输入 |
| 原单位、迹及正比较 | 同一 $E_o,u_o$；BBKM Proposition 5.1、Theorem 6.1/Appendix B 与规范 Jordan 迹 | 取得 $\phi_o,g_o$、Frobenius 和式 (10.2)，不另供任意内积、扇区迹权或 signed spectrality |
| Hilbert、密度与 Born | 上行及原 D 的导子/曲率合同；V95 定理 2.1 | $\bigoplus_s\mathbb C^{d_s}$、块密度和迹配对；扇区数量、大小及 $D$ 仍由原资料给定 |
| 原空间复合 | E 的局部乘法/有向嵌入、跨项零、产品统计和张成；V95 定理 5.2 | 原标准复张量与全中心对应；原空间边、产品准备与实际比较不能从单体几何制造 |
| 原事件 CP 与数学 Kraus | E 的任意有限参考副本、原产品输入作用及全实际联合锥；Watrous 式 (1.124)、Theorem 2.22 | 全部原事件 CP/TNI；数学 $\mu$ 未被声明为原记录 |
| 原标签一 Kraus | 上行加原 F、单中心支撑及指定实际双返回；C118 定理 121.1、定义 140.1 | 原每个非零细标签为一 Kraus，并保持原 $q,U$、遗忘和分组；F 没有从 CP 单独导出 |
| 平方根/Lüders | B 在原目标—参考复合上的面供应；E 的系数一纯参考准备、丢弃和指定合法接续 | 所有 $E$ 的新原词 $W_E$ 精确为 $\sqrt E(\cdot)\sqrt E$，条件态只在正成功概率时定义 |
| 已命名同效果设备 | 该原设备的原效果、设计准备、原读回和准确校准合同，例如 C118 定义 141.1 | 能消费相应准确校准定理；新词的存在不证明这个旧设备的更新或端口 |
| 原有限词及指定回路 | A、F 的原实现与合法域；C118 的同记录/有限词运输 | 全部原概率和原成功因素保持；消费 C118 分数结论时仍须该包的原控制与校准 |
| 连续时间 | 另供实际连续可逆确定性一参数群及物理时间标定；C118 定理 147.1 的时间接口 | 有限块酉共轭和 Hamilton 形式；D 的代数存在不供应实际连续时间 |

证明。每行逐项是被引定理的前提对应。特别，原始内积、强对称、自守、反对称、数学 Kraus、原 Kraus 端口和系数一参考各有不同地位；表中没有把一个数学结论的存在改写为其原设备供应。∎

**命题 13.4（POVM 仪器与实际时间的额外条件）。** 个别 $W_{E_j}$ 的可调用性不自动把一个 $\sum_jE_j=I_o$ 的效果列表装配成同一原仪器。若另供一个原共同测试，其互斥结果 $j$ 的原分支正是这些指定 $W_{E_j}$，并有原条件控制、共同记录及遗忘，则其 Lüders 仪器为

$$
 X\longmapsto\bigl(\sqrt{E_j}X\sqrt{E_j}\bigr)_j,
\qquad p(j\mid X)=\tau_o(E_jX).
\tag{13.1}
$$

另若一个原对象上有实际连续可逆确定性一参数群 $t\mapsto T_t$，其逆也属原事件，则在同一载体的每个块上存在自伴 $H_s$，使

$$
 \mathcal T_t(X)_s=e^{-itH_s/\hbar}X_se^{itH_s/\hbar},\qquad
 \dot X_s=-\frac{i}{\hbar}[H_s,X_s].
\tag{13.2}
$$

单扇区纯态的向量代表可选为满足 $i\hbar\dot\psi_s=H_s\psi_s$ 的相位规范；一般直和态不因此有跨超选择扇区的可观测相干。

证明。第一项把另供原共同测试的分支应用定理 11.1 后求和；效果和为单位给保迹，原互斥端口给仪器的实际身份。式 (13.1) 自身只是数学 CP 仪器，只有所说共同测试供应才成为原设备。第二项直接消费 C118 定理 147.1 的连续时间步骤：正反方向在本表示都 CP、确定且互逆，连续性排除有限中心置换，逐块为酉共轭一参数群，有限维生成元给 (13.2)。具体 $H_s$、实际时间、能量单位及 $\hbar$ 的物理标定没有从 (9.3) 推出。∎

**定义 13.5（完整白话释义与候选边界）。** 白话说：先把同一个整体里原来所有准备、读口、设备、细记录、失败和有限接续都保住，只把它们的全部未来响应放进一个有限的实空间。我们假定每个几何面真有一台能压入该面、带实际失败记录的原设备，并要求纯状态通过它后仍是纯射线或零；纯射线之间的转移读数还要互相对称。成熟的 Jordan 结果和规范原子对应于是把原单位、正锥、态与效果配成同一套尺度，再用原有向三元关系及本卷的曲率定理取得任意有限复矩阵直和。独立复合要真的保留原产品作用与全部联合准备；任意有限多个二阶参考把原事件的正性检查到足够大的矩阵层，所以得到完全正。原设备的细标签和双侧支撑返回仍须实际供应，才能把数学单算子认作设备真正留下的那条原记录。为了供应一个效果的平方根更新，我们确定性地接入一份纯参考，连续调用两台原面设备，再丢掉参考，成功支就恰好是所需滤波，没有偷偷乘上参考准备的成功损耗；每一个失败叶也仍是原来的叶。奇异效果只在支撑内带正确缩放返回，零效果没有条件态。这样桥接的是同一个整体的共同载体与一套实际精确操作词；它没有把另一台同效果设备变成理想设备，也没有凭各个滤波器就制造任意共同测量或连续时间。

这里的独立输入仍包括有限维闭原响应锥及有限正组合完备性、实际全脸压缩与纯性、原子互易、原 $D$ 的导子/曲率关系、原空间嵌入与产品供应、全联合参考稳定性、确定性纯参考及指定接续、原 F 与指定返回、已有原控制/校准/回路资料。B 与 C 导出 projectivity、源定理的全滤子纯性、规范正比较与 Jordan 结构；与 D 合用才导出复载体、自守和反对称。E 导出 CP 并实际供应第十一章的词，F 再接回原可访问细记录。没有声称这些输入全都彼此独立、严格弱于别的候选，或具有全局最小资源。

**定义 13.6（来源、综合范围及未解决问题）。** 本候选直接消费 BMU16 的有限 Jordan 分类，BBKM Proposition 3.1 的 face/filter/projective-unit 双射、Proposition 5.1 的有限效果谱展开与 Theorem 6.1/Appendix B 的原子正内积，Watrous Theorem 2.22 的 CP/Choi/Kraus 对应，以及本卷定理 2.1、5.2、C118 支撑正常形与原记录有限词论证、Atlas30 的统计相干性。引用 Alfsen–Shultz 的间接源只限这些已明确转述并消费的结果；这里不以其书中 Theorem 9.33 的原文为证据。Atlas26 的 S/Sp 和 Atlas28 的强对称简单性路线不作本候选的额外前提，Atlas29 的简单自复合排除不拿来删除任意不等超选择直和。

这里的综合结果是：从原响应几何及原有向关系运输共同载体，同时把全复合上的实际面供应接成精确原始成功效果词，并以原 F 保持原记录、指定支持返回和全部有限原历史。成熟分类、投影膨胀、矩阵函数演算、Kraus 表示及同构本身不作为新发现或优先权主张。

A–F 是可满足的条件候选，不是给定物理 $\Omega$ 已满足它们的证明。由更少原生关系取得闭锥完备性、实际全脸供应、全参考稳定性和原 F 的任务仍未解决；把已有设备精确校准到理想更新、实际共同 POVM 测试以及连续物理时间也各须所列供应。全脸及全复合的要求可比指定有限配方需要更多实际资源，这里没有数值成本、严格弱化、经验实现或整体目标已完成的结论。C120 的论证不以任何独立候选草稿为前提。

## 追加锚（本行以下为增补区）

## 14. 原单位与原身份的明确运输约定

**定义 14.1（定理 10.1 中保原归一化基的表示）。** 即使把 BMU16 的输出只读作 Jordan 锥的序同构，而不先把原归一化单位包含在该输出中，定理 10.1 所用的保基表示也按以下规则取得。设 $f:V_o\to J$ 是该锥同构，$\tau_J$ 为规范 Jordan 迹。原严格正单位唯一写成

$$
 u_o(v)=\tau_J(w\circ f(v)),\qquad w\in\operatorname{int}J_+.
$$

以标准 Jordan 二次表示 $\mathsf Q_z=2L_z^2-L_{z^2}$ 定义

$$
 f_0=\mathsf Q_{w^{1/2}}f,\qquad
 a(v)=\tau_J\bigl(\theta(a)\circ f_0(v)\bigr).
\tag{14.1}
$$

这里 $\theta:E_o\to J$ 是第二式唯一确定的对偶序同构。Jordan 正锥的标准二次表示是序自同构，$\mathsf Q_z$ 对规范迹配对自伴随且 $\mathsf Q_z1=z^2$，所以

$$
 \tau_J(f_0(v))=\tau_J(w\circ f(v))=u_o(v),\qquad
 \theta(u_o)=1_J.
$$

因此这一步不独立假定原 $u_o$ 恰是任意所选坐标中的标准迹，也没有引入一个自由的自对偶配对。原子 projective unit 的唯一支持归一态给 $\phi_o=f_0^{-1}\theta=\theta^*R_J\theta$；这就是 BBKM Theorem 6.1 的唯一原子映射。标准二次表示性质只作为原单位运输的中间工具使用；在 special 矩阵端点，$\mathsf Q_z(y)=zyz$，式 (14.1) 就是把原单位权重共同移入状态密度。原每个准备的强度与所有 Born 响应均保持，而不是把实际成功率重新定标。

**定义 14.2（不对原实现取商的表示对象）。** 定理 13.2 的表示保留带名字的数据

$$
 o\longmapsto(o,\mathcal A_o),\qquad
 x\longmapsto\bigl(\iota_x,\mathrm{type}(x),\mathsf R_x,
 \mathsf S_x,\mathcal T_x\bigr).
\tag{14.2}
$$

其中 $\mathsf S_x$ 包括全部已命名支持、返回、原因素、校准和控制/回路引用。组成词时原节点名与原端口按 $\mathsf H$ 的规则组成，只有映射分量做线性复合。两个映射分量相等不删除任何名字，不产生密封原端口，不改变可用性；原对象即使同构也不合并。这是原响应表示的身份约定，不是声称矩阵能唯一反推出物理装置。

式 (9.1) 对参考测试的作用也严格限于锥：每个联合正元可由实际原准备有限正组合得到，所以原延伸在这些准备上的正性延拓到该正元。即使其数学归一化态没有系数一准备，这个正性推理仍成立；定理 11.1 的原始成功系数一则另外且必须消费 E 的确定性 $b_0$。两种资源不能互相替代。

## 追加锚（本行以下为增补区）

# CONSTRAINED-GRAM: 匹配相关的 Newton--Hankel 二次型探针

## Q1. 首先固定循环禁区

**禁止用 `H0(R) PSD => R 全实根` 证明本轮的输出实根性。**
冻结 `NewtonHankelRealRootCriterion.newtonHankel_posSemidef_iff_roots_real`
是双向判据,不是新的保持性机制。本探针不使用其 PSD 到实根方向。
不先假设输出根为实数再把 Vandermonde 分解当成所求结论。
允许使用其独立的二次恒等式,但 `Re(z^2)` 不是 `|z|^2`。

产地: `skill: consensus-rnd:sshx`; 单席 codex-cli thinking 探针;
`repo-prior-exposed`; 零子席、零评审席、独立来源数 1。
输入是本轮 brief、完整 CLAUDE.md、当前源码与状态片及上一轮留档报告。
报告不作数学前提。不 deposit、不冻结、不修改覆盖账、不创建 PR;仅推本席分支。

**判词: revise。找到 m=2 的匹配加权块 Gram,但为 bind-only; m=3 的完整有理 Gram
也为 bind-only。没有找到一般 m 的匹配加权 Gram,没有可立即派实施席的新增命题。**

这里的 `gram_form_found=true` 只指下面明确展示的低阶形态;
`general_m_gram_form_found=false`。不把低阶绑定改称新的实根机制。
本报告是第三档研究线 #6377 / #6160 的有界探针,不是数学模块交付。
全部候选在计算前登记于本文件初稿和 attempt 的 `preregistered.md`;
每条先试钉版 Mathlib、冻结投影、规范化,成功即停手。

## 对象与前提身份

工作树基线 `e5e608c6f672b68921a33964667e270a04041d7b`;
Lean `v4.33.0`; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。
所有状态只对本树负责。`ls Golden/Frozen/state/D5/S3/Zeros/Convolution`
实际列出了 `MatchingFiber`、`MatchingPolynomial`、`FiniteConvolutionCoefficients`、
`FiniteFreeCommutatorDegreeSix` 的状态片。**本次 brief 要求仍将 #6433/#6450/#6481
按未冻结件引用,本席遵守这个更保守的前提口径。** 物理状态与可用前提身份分列,
不依据旧报告升级它们,不为本次探针补冻。

冻结前提的实际查询还包括
`ls Golden/Frozen/state/D5/S3/Zeros/CoefficientBounds` 和
`ls Golden/Frozen/state/D5/S3/Constants/NewtonHankelRealRootCriterion.lean.json`。
下表哈希是模块状态片的 `statement_id`,不是逐声明哈希,均带 `sha256:` 前缀。

| 简称与冻结声明 | 模块状态片身份 |
| --- | --- |
| F4: `FiniteFreeCommutatorDegreeFour` 的定义、`centered_quartic_invariant_bounds` | `e4f15f5c0461a866887270b3ea9714ad3cb9c7bf4a40afe95cc84c3488442c13` |
| SE: `SexticEnvelope.centered_real_sextic_envelope` | `33cfc49345ee9794259badf034e9f1f7eb39c5f7aa2b1e5a8f5a0687adb2b763` |
| SD: `SexticDiscriminant.centered_real_sextic_discriminant` | `965f0130d8e7df89d79c9e1b861fc553dc6292bed044099a9e26ca58b66a6a66` |
| NH: `NewtonHankelRealRootCriterion` 的二次恒等式与判据 | `18b030426106ba093ef4ec58fbba090c162f365f32ed6b291aaa0eeba9a358a9` |

SD 的源码历史直接定位到 `33a8590118b2fe84d8c1d309ecd348a4ce4c1f86`
`math: prove discriminant nonnegativity for two centered real sextics (#6345)`。
因此 B2 可以直接取 SD,**不需要把 #6481 的六次保持定理当冻结前提**。

源码地址:
[F4](../../../D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFour.lean),
[SE](../../../D5/S3/Zeros/CoefficientBounds/SexticEnvelope.lean),
[SD](../../../D5/S3/Zeros/CoefficientBounds/SexticDiscriminant.lean),
[NH](../../../D5/S3/Constants/NewtonHankelRealRootCriterion.lean),
[MatchingFiber](../../../D5/S3/Zeros/Convolution/MatchingFiber.lean),
[MatchingPolynomial](../../../D5/S3/Zeros/Convolution/MatchingPolynomial.lean)。

第三类资料是 [上一轮报告](image-cone-probe-0909.md),仅作定义、反例和检索线索。
下面的系数、主子式、负方向和匹配恒等式读数由本席精确计算,报告本身不承重。

### 两组根,不能压成自由边权

令 `n=2m`, `r,t in R^n`, `p_r=prod_i(X-r_i)`。
`Q=contract 2 (Sym(p_r))`, `T=contract 2 (Sym(p_t))`,
写 `b_k=e_k(Q)`, `d_k=e_k(T)`;这里 `d_k` 不是向量 `c`。
由任务允许使用、但按未冻结件列账的 `matching_identity`:

\[
b_k=\frac{M_k(r)}{(n)_k},\quad d_k=\frac{M_k(t)}{(n)_k},\qquad
M_k(r)=\sum_{M\in\operatorname{Match}(n,k)}w_M(r),\quad
w_M(r)=\prod_{\{i,j\}\in M}(r_i-r_j)^2.
\]

`(n)_k` 是下降阶乘。匹配定义明确要求无环、每个匹配内顶点不重复。
所有阶共用 `r`,另一个输入所有阶共用 `t`。
`omega_ij=r_i-r_j` 始终满足 `omega_ij+omega_jk=omega_ik`。
两色匹配 `(M,N)` 分别约束各自输入的顶点;不同匹配因子之间允许重复顶点,
不能把 Newton 展开中的多个匹配误合成一个全局不相交匹配。

输出与 kernel 的归一化是

\[
R=Q\boxtimes_m T\boxtimes_m K_m=Y^m-a_1Y^{m-1}+\cdots+(-1)^ma_m,
\quad a_k=\lambda_{2m,k}b_kd_k,
\quad\lambda_{n,k}=\frac{k!}{(n-k)_k}\frac{n+1-k}{n+1}.
\]

因此 `a_k` 是**两组同阶匹配**的正权和。系数非负的 bind-only 尝试立即成功:
`matching_identity` 后接 `sq_nonneg`、`Finset.prod_nonneg`、`Finset.sum_nonneg`、
`div_nonneg`。这项在本次口径下是“依赖未冻结恒等式的绑定后果”,不是冻结前提,
更不是矩阵 Gram,到此停手。

复根按重数列为 `rho_1,...,rho_m`,取 `s_j=sum rho_l^j`, `s_0=m`。
实系数保证这些和为实数;计算时由 Newton 恒等式得到它们,不先求实根。
`H0=(s_{i+j})_{0<=i,j<m}`;本仓 NH 使用除以 `m` 的归一化,
故 `H0=m*newtonHankel` (`m>0`)。本文所有子式均为未归一化版本。

### 已实际打开的论文

Campbell--Morales--Perales, *Even Hypergeometric Polynomials and Finite Free Commutators*,
<https://arxiv.org/pdf/2502.00254v2>。本席重新下载 PDF,用 `pypdf` 打开第 5、7、11、19、20 页;
物理页码与印刷页码一致。SHA-256:
`2d8db91f7f43604bbf56672abf3f14035897444a9ce7204bb30d49b90470bfdd`。
以下恢复提取文本的空格,公式转写,不改变参数。

p.5, Definition 2.9 原文:
> We define the finite free multiplicative convolution of p and q as the polynomial
> p ⊠_n q ∈ P_n with coefficients given by e_k(p ⊠_n q) = e_k(p)e_k(q)/binom(n,k)
> for 0 ≤ k ≤ n.

p.11, Notation 3.7 原文:
> For p ∈ P_n, the symmetrization of p is the polynomial Sym(p) := p ⊞_n (Dil_{−1}p).

p.20, Proposition 5.4 原文:
> For p, q ∈ P_{2m}(R), we have
> Q_m(p □_{2m} q) = Q_m(Sym(p)) ⊠_m Q_m(Sym(q)) ⊠_m
> Dil_{1/4} H_m[2,2 / (1−1/(2m)), (2+1/m)].

p.20, Remark 5.5 的相关原句:
> This means that to prove Conjecture 5.3, one must find some kind of “extra”
> real-rootedness in the symmetrizations Q_m(Sym(p)). It is unclear if this extra
> positivity holds in general.

p.7 Definition 2.16 原公式 `e_k(H_m[b/a])=binom(m,k)(mb)_k/(ma)_k`,
连同两次乘法卷积的除数,给
`e_k(K_m)=lambda_(2m,k)*binom(m,k)^2`。
也可从 p.19 Notation 5.1 的 `z_n` 系数独立消去 `(2k)!*binom(n,2k)=(n)_(2k)` 得到同一 lambda。
`K_m` 与 `z_(2m)` 不是同一多项式。本文不引用未打开的原始参考文献 [10] 的定理。

## Q2. 候选结算

### B0: 根上 Gram 与现成矩阵分解,有条件 bind-only

NH 的 `companion_trace_hankel_quadratic_identity` 直接给

\[
c^TH_0c=\sum_\ell\operatorname{Re}\bigl(f_c(\rho_\ell)^2\bigr),\qquad
f_c(z)=\sum_{i=0}^{m-1}c_i z^i.
\]

**恒等式 bind-only,但右侧不是非负平方和。** 输出根已实这一额外前提下,
它才是 `sum f_c(rho_l)^2`。Mathlib `Matrix.PosSemidef.dotProduct_mulVec_nonneg`、
`Matrix.LDL.lower_conj_diag` 也分别要求先有 PSD、正定性;
`Analysis/Matrix/Order.lean` 的平方根构造从矩阵非负性出发。
这些有条件绑定均停手。去掉条件恰是所缺数学,不能由换接口消去。

### B1: m=2 的 26 项匹配加权块 Gram,bind-only,停手

先给一般二阶配方。对任意 `m>=2`,首个块 `A=[[m,a1],[a1,a1^2-2a2]]` 满足

\[
(u,v)A(u,v)^T=m(u+a_1v/m)^2+(D_m/m)v^2,
\quad D_m=(m-1)a_1^2-2ma_2.
\]

二阶界的来源重新列清:中心化 `x_i=r_i-mean(r)`, `S_j=sum x_i^j`,
把 Sym 定义的前三、前五项卷积和与 Mathlib 的 Vieta/Newton 阶 2、4 实例规范化得

\[
b_1=S_2,\quad
b_2=\frac{n^2-3n+3}{2n(n-1)}S_2^2-\frac12S_4,\qquad
\beta_m b_1^2-b_2=\tfrac12(S_4-S_2^2/n),\quad
\beta_m=\frac{(m-1)^2}{m(2m-1)}.
\]

`sq_sum_le_card_mul_sum_sq` 实例于 `x_i^2` 给最后余量非负。
在 m=2 也可直接投影 F4 的 `centered_quartic_invariant_bounds`;
m=3 可投影 SE。两输入的界相乘、规范化给

\[
D_m\ge L_m b_1^2d_1^2,\quad
L_m=\frac{2(m-1)(2m^3-3m^2-2m+1)}
{m(2m-3)(2m-1)^2(2m+1)^2}>0.
\]

在 `m=t+2` 下,立方因子为 `2t^3+9t^2+10t+1`。
这是纸面 bind-only,没有新全阶约束;本次不重建上一轮的通用 B2 模块。

现在取 `m=2`,令 `B=b1`, `C=d1`, `x=r-mean(r)`, `y=t-mean(t)`。
令 `epsilon_r=B^2/6-b2`, `epsilon_t=C^2/6-d2`。有限和规范化给

\[
\epsilon_r=\frac18\sum_{i<j}(x_i^2-x_j^2)^2,\qquad
\epsilon_t=\frac18\sum_{i<j}(y_i^2-y_j^2)^2.
\]

先尝试直接配方,成功:

\[
D_2=\frac{B^2C^2}{225}+\frac25 B^2\epsilon_t+\frac{12}5 d_2\epsilon_r.
\]

`d2=M_2(t)/12`,故得到用户所允许的“保留根差相关性的 Gram”:

\[
\begin{aligned}
c^TH_0(R)c={}&2\left(c_0+\frac{2BC}{15}c_1\right)^2
+\frac1{450}(BCc_1)^2\\
&+\frac1{40}\sum_{i<j}\left[B(y_i^2-y_j^2)c_1\right]^2\\
&+\frac1{80}\sum_{M\in\operatorname{Match}(4,2)}w_M(t)
                  \sum_{i<j}\left[(x_i^2-x_j^2)c_1\right]^2.
\end{aligned}
\tag{G2}
\]

共有 `1+1+6+3*6=26` 个平方;所有权非负。
每个 `w_M` 是同一 t 上两个不相交边的平方积,并未自由化。
这是**块 Gram**,等价于带辅助 `i<j` 标签的匹配平方和;
不冒称“每个未加标签的匹配恰好对应一个 L_M”。
交换 r,t 后取两式平均可对称化,没有新数学,不继续制作。

G2 对零根、重根、全相等根均有效,没有分母为零的根条件。
它由二阶界余量的既有平方和改写得到,**bind-only,零模块**。
本次 Lean 验了二阶配方、余量分解与 `sq_nonneg`/`linarith only` 的非负推导;
G2 的实际根列表系数比较在 120 对样本上通过。未声称 G2 的整条根列表装配已在 Lean 内验完。

### B2: m=3 的完整有理 Gram,绑定 SD 后停手

写 `a=a1,b=a2,d=a3`, `D=2a^2-6b`,
`Delta=a^2*b^2-4b^3-4a^3*d-27d^2+18abd`,
`g=2a^3-7ab+9d`。Newton 恒等式及配方给 (`D>0`):

\[
c^TH_0c=
3\left(c_0+\frac a3c_1+\frac{a^2-2b}3c_2\right)^2
+\frac D3\left(c_1+\frac gD c_2\right)^2
+\frac{\Delta}{D}c_2^2.\tag{G3}
\]

`det H0=Delta`。最后主元不是来自前两矩。
本席的第一步绑定尝试已找到 SD:对中心化输入 p,q,令
`A=-p.coeff 4`, `B=(p.coeff 4)^2+5*p.coeff 2`,
`Z=-(2*p.coeff 0+2*p.coeff 4*p.coeff 2/15-(p.coeff 3)^2/20)`。
输入像系数正是 `(b1,b2,b3)=(2A,2B/5,Z)`,第二输入同理;
输出 `(a,b,d)=(24AA'/35,2BB'/105,4ZZ'/7)`。
**这逐字是 SD 的结论,直接 `exact` 得 Delta>=0。**
因此不重跑 SD 内部的包络/Bernstein 证书,也不把它改写为一个新模块。

非平凡输入下,前述严格余量给 D>0。D=0 时必有 `b1*d1=0`;
某个根列表的 `S2=0`,由 `sq_nonneg` 和和为零推出该列表全相等,
所有非空匹配权消失,`R=Y^3`,二次型是 `3c0^2`。
Delta=0 而 D>0 时 G3 仍成立,最后权为零,没有偷加单根假设。

G3 保留同一根参数导出的全部系数相关性,但**不是显式匹配索引公式**。
整条纸面推导为 bind-only;Lean 子片段验了清分母恒等式和 SD 的直接实例化。
其依赖链没有输出实根假设、没有 NH iff 的任何方向。

### C3: Hankel 直接 Schur 乘积,已排除

先尝试由 Mathlib 的 Gram/Schur 乘积工具绑定。
这要求被乘的矩阵非负且确有相应矩阵恒等式;两者均不能从系数乘法推出。
具体检验最自然的归一化候选
`H0(R) = (H0(Q) hadamard H0(T) hadamard H0(K_m))/m^2`:
它恰好对上 `(0,0)`、`(0,1)`,但在 `(1,1)` 已错。

| 合法输入 r=t=(-1)^m,(1)^m | 真 s2 | 候选 s2 | 真值减候选 |
| --- | --- | --- | --- |
| m=2 | `2176/225` | `-3584/2025` | `23168/2025` |
| m=3 | `19776/1225` | `4656/625` | `266256/30625` |
| m=4 | `439808/19845` | `2506240/194481` | `3006464/324135` |

这是实际根域内的恒等式反例,没有借助自由边权。
根因是 Newton 变换非线性:`s2=a1^2-2a2`,不与系数乘法交换。
本结果只排除这条明确公式,不排除带修正项的其他构造。

### C4: 根参数无关的匹配对角形式,已排除

候选是有限和 `sum_(M,N) kappa_(M,N) w_M(r)w_N(t) (u_(M,N) dot c)^2`,
其中 `kappa>=0` 为常数,所有向量 u 与根参数无关,允许空匹配。
先作 bind-only 检查:共同缩放实际根 `r,t -> h*r,h*t` 保持全部 cocycle 和匹配约束。
权缩放为 `h^(2|M|+2|N|)`。

`H00=m` 不随 h 变。比较 h=0 与 h=1,有限非负和为零迫使每个非空匹配项的
`w_M(r)w_N(t) u_0^2=0`。这个结论只用系数比较、平方非负和有限和为零。
因此所有非空项对 H01 的贡献也为零;空项不随 h 变。
但真实 `H01=a1` 随 h 缩放为 `h^4*a1`,在上表合法根例上 `a1>0`,矛盾。
**纸面 bind-only 反驳,停手。** G2 不受此排除,因为它的线性形式明确依赖根。
不排除归一化有理权、根相关 L、矩阵权或其他索引体系。

### C5: 一般 m 的根相关匹配 Gram,没找到

把 `w_M` 保留为真实根差平方积、允许 L 依赖根,本次没有得到统一构造,
也没有得到否定这整个形态的反例。下面是 m=4 的具体缺口。

分块 `H0=[[A,B],[B^T,E]]`,A 为前述首个 2x2 块。在非平凡输入上 A 正定,故

\[
c^TH_0c=(c_I+A^{-1}Bc_J)^TA(c_I+A^{-1}Bc_J)+c_J^TSc_J,
\quad S=E-B^TA^{-1}B.
\]

令 `Delta_j=det H0[0:j,0:j]`。纯恒等式给
`S00=Delta_3/Delta_2`, `det S=Delta_4/Delta_2`。
若记输出系数为 `(a,b,d,e)`,则

\[
\Delta_3=2a^2b^2-6a^3d-12a^2e+28abd-8b^3+32be-36d^2.
\]

它已涉及第三、第四系数的相关性;`Delta_4` 是 16 项四次判别式。
一般非退化情形需要 `Delta_3>0, Delta_4>=0`。
边界 `S00=0` 时还需 `S01=0,S11>=0`;不能仅查顺序主子式或在零主元上继续除法。
**缺的是这些量在真实匹配域上的非负证据,不是 LDL 的形式化工时。**
Mathlib 的正定 LDL 和 NH 的 iff 都不会供给它们。

因此一般 m 的可能性结算为 **open**:本次没有发现结构矛盾,
小 m 的通过不是一般存在定理。若不限制 W,L 的可构造内容,
把任意矩阵平方根的行随意叫作“匹配”没有新增信息,也不回答 Q2。
本轮不为 C5 派实施席:还没有一个已找到、可核对的全阶构造或符号证书。

## 精确有理读数

`exact_probe.py` 用 Python `Fraction` 与 SymPy **1.14.0**。
每个根列表分别通过“逐顶点枚举无重复顶点的匹配”和“由输入 elementary 系数按 Sym 定义卷积”
求 b,d,逐系数相等才进入矩阵计算;代码还逐三元组核对 cocycle。
所有 Hankel 元由 Newton 递推算出;具名样本又与有理 companion 矩阵的迹幂逐项相等。
没有浮点运算、近似根判词或自由非负边权输入。

枚举域为 `{-1,0,1}` 中长度 2m 的**全部非降根列表**;
两输入取所有无序对,包括不同输入。PSD 判读使用**所有非空主子式**,
不是只查首主块或只查顺序主子式。

| m | 根列表数 | 输入对数 | 不同输出系数 | 负矩阵数 | 矩阵秩: 对数 |
| --- | --- | --- | --- | --- | --- |
| 2 | 15 | 120 | 21 | 0 | 1:42, 2:78 |
| 3 | 28 | 406 | 74 | 0 | 1:81, 2:135, 3:190 |
| 4 | 45 | 1035 | 195 | 0 | 1:132, 2:237, 3:288, 4:378 |

合计 **1561** 对、**290** 个不同输出,仅此有界域。
G2 在全部 120 对上按 c 的系数核对,所以每个样本覆盖所有 c,没有抽几个 c 当恒等式检验。

下面**把 `(X^2-1)^m` 放在 Sym 之前**作为合法输入,不同于负校准一:

| m | b=d,省略首一项 | a,省略首一项 | 精确实根数,含重数 |
| --- | --- | --- | --- |
| 2 | `4,8/3` | `64/15,64/15` | 2 |
| 3 | `6,48/5,16/5` | `216/35,384/35,1024/175` | 3 |
| 4 | `8,144/7,128/7,128/35` | `512/63,768/35,16384/735,16384/2205` | 4 |

| m | 顺序主子式 Delta_1,...,Delta_m | 精确 LDL 主元 |
| --- | --- | --- |
| 2 | `2,256/225` | `2,128/225` |
| 3 | `3,12672/1225,56623104/7503125` | `3,4224/1225,49152/67375` |
| 4 | `4,149504/6615,52076478464/1531537875,18014398509481984/496425029113125` | `4,37376/6615,25427968/16901325,33554432/31441095` |

最后一例消去前两行后的块为

\[
S=\begin{pmatrix}
25427968/16901325&436207616/42591339\\
436207616/42591339&949691088896/13416271785
\end{pmatrix}.
\]

它只有**这个样本**的非负证据;符号一般式没有随之得证。
另对每个 m 测了两侧相同的 `(-m,...,-1,1,...,m)`、
`(0,...,0,1)`,以及不同有理输入
`r_i=i/(i+1), t_i=(-1)^i(i+1)/3`, `0<=i<2m`。
全部精确 PSD,具名非退化样本全部有 m 个实根(由有理区间隔离独立计数),完整系数/矩阵留在 `numerics.json`。
单离群根样本的 R 分别为
`Y(Y-3/20)`, `Y^2(Y-5/42)`, `Y^3(Y-7/72)`;
后两例秩为 2,说明零主元分支是实际输入,不能删除。

## Q3. 两条负校准

### 一: U=V=(X^2-1)^m 已在 Sym 之后

本校准 `Q=T=(Y-1)^m` 是乘法卷积单位,所以输出 **R=K_m**。
代入 `a_k=lambda_(2m,k)*binom(m,k)^2`,取
`c=(-a1/m,1,0,...,0)` 就直接有 `c^T H0 c=D_m/m`。
纯有理规范化给 (`m>=2`)

\[
D_m=-\frac{m^3(m-1)(8m^3+4m-1)}
{2(2m-3)(2m-1)^2(2m+1)^2}<0.
\]

| m | D_m | c | c^T H0 c |
| --- | --- | --- | --- |
| 2 | `-284/225` | `(-8/15,1)` | `-142/225` |
| 3 | `-2043/1225` | `(-18/35,1,0)` | `-681/1225` |
| 4 | `-16864/6615` | `(-32/63,1,0,0)` | `-4216/6615` |

与真匹配域相容的原因是单位输入不在该像中:
`b2-beta_m*b1^2=m(m-1)/(2(2m-1))>0`。
因此不能把 G2 或 G3 推广到所有非负实根的 Q,T。
这里直接展示二次型为负,没有通过 PSD 判据证明任何输出实根性。

### 二: 首个块为正的新反例

`Q=T=(Y-1)^2(Y-4)`, `(b1,b2,b3)=(6,9,4)`;
B2 余量为 `3/5`,但 B3-6 余量为 **-1134**。
本席精确算出

\[
R=Y^3-\frac{216}{35}Y^2+\frac{135}{14}Y-\frac{64}7,
\quad(\Delta_1,\Delta_2,\Delta_3)
=\left(3,\frac{22437}{1225},-\frac{662940477}{600250}\right).
\]

有理区间隔离给**实根数 1**。无需近似根,取

\[
c=\left(\frac{17425}{1939},-\frac{646988}{87255},1\right),\qquad
c^TH_0c=-\frac{24553351}{407190}<0.
\]

这正是消去前两个坐标后 `Delta_3/Delta_2` 的值。
该点违反 SE 投影的
`9b3(4b1^2-5b2)<=5b1*b2^2`,所以不存在需要的六个真实根的同源匹配见证。
它不反驳真正输入域的候选,却排除只用 B2 和 Q,T 非负实根性的全矩阵 SOS。

| 候选 | 校准一 | 校准二 |
| --- | --- | --- |
| B0 | 有符号 Re(f^2) 恒等式允许负值;实输出根前提未成立,不得改成绝对值平方 | 同理;显式负方向排除无条件 Vandermonde 非负解释 |
| B1/G2 | 单位输入违反 B2,无原始根见证;未落在 G2 域内 | m=3 不属于完整 G2 的域;B1 只保证首块,与其正子式相容,不能推整个 H0 |
| B2/G3 | 真输入域前提失败;形式 LDL 有负主元 | 代数恒等式仍成立,但末权 Delta/D<0;违反 SE,SD 不可实例化 |
| C3 | 单位情形恰返回 H0(K_m),但 kernel 不是 PSD,无法作非负 Schur 绑定 | kernel 条件仍失败;一般恒等式已在合法输入上被独立排除 |
| C4 | 不能延伸到有负方向的外域 | 同理;其否定更早在合法根域内由缩放证出 |
| C5 | 必须保留同源根见证以排除该外域点 | 必须保留超出 B2 的相关性;当前未找到构造,不报已通过正性证明 |

`negative_calibrations_passed` 指校准计算、域区分和候选筛查全部完成,
不表示给两个负矩阵找到了非负 Gram。

## Q4. 六栏表

`escapes=能` 指能由所列可消费前提实例化/投影/规范化得到;
`不能` 是本席搜索和数学分析下仍有缺口,不是对全部 Lean 证明的不可达性定理。
判形与前提是否冻结分开;给新结果换成已知结果的名称不创造逃逸。

| from | steps | gap: 数学缺陷 | escapes | payoff | cost_shape |
| --- | --- | --- | --- | --- | --- |
| 系数 SOS: **未冻结口径** MatchingPolynomial/MatchingFiber; Mathlib 有限和积非负 | 匹配恒等式、平方非负、除以正阶乘 | 无;结论只涉及系数符号 | **能,bind-only**,依赖未冻结件 | 明确两色同源输入;不是 Gram 机制 | 组合有限和;不展开平方 |
| B0: **冻结** NH 二次恒等式; **钉版** Matrix.PosSemidef、LDL、矩阵平方根 | 实例化;真实输出根下把 Re(f^2) 化为实平方 | 无条件非负性缺实输出根/PSD 前提;条件式本身无 gap | **能,条件 bind-only**;删前提则不能 | 排除循环或条件偷渡;不派席 | m 个评价平方,或矩阵结构;不需符号大展开 |
| B1/G2: **冻结** F4 定义及四次界; **钉版** Newton/Vieta/Cauchy; 写成匹配标签另用**未冻结口径** matching_identity | 两个二阶界、余量平方和、配方 | 无新数学缺口;作为全矩阵只覆盖 m=2 | **能,bind-only** | 得到真实根域的 26 项块 Gram;到此停手 | 26 个平方块;卷积系数和最多 5 项;不重展六变量/八变量根多项式 |
| B2/G3: **冻结** SE、SD;F4 定义;**钉版** 平方/商非负 | 中心化;输入前三系数规范化;SD 直接 exact;三次配方 | 无;限 m=3,不能外推 m=4 | **能,bind-only** | 完整控制 m=3,包括退化;零新模块 | 三个平方块;原二次型 13 单项式;清分母块至多 26 项的乘积展开上界;不重跑 SD 内部证书 |
| C3: **冻结** F4 系数卷积定义;**钉版** Gram/Schur 工具 | 尝试矩阵乘法绑定,核对 s2 | 候选恒等式为假;kernel PSD 前提亦假 | **不能,陈述被反驳** | 排除 Newton 变换与系数乘法可交换的误判 | 只需前 3 个矩,一个 s2 比较;3 个精确反例 |
| C4: 匹配定义(**未冻结口径**);**钉版** sq_nonneg、有限和为零、系数比较 | 对真实根共同缩放,比较 H00、H01 | 根无关 L 无法同时保持常数矩与非恒定一次矩 | **能,bind-only 反驳** | 强制有效构造保留根相关特征;不另立否定模块 | 结构性缩放论证;只比较 2 个矩阵位置 |
| C5: **未冻结口径** 全阶匹配恒等式;**冻结** F4 定义;**钉版** Newton 与分块代数 | 保留真实根,消去首块,求余块的匹配 Gram | m=4 的 Delta3、Delta4 与零主元边界非负证据缺失;不是形式化工作量 | **不能,open** | 唯一保留的研究目标;尚无可实施的分解 | 系数层 q 为 37 项、Delta3 为 7 项、Delta4 为 16 项;根域证书未找到,最大证明块未测 |

只有 `不能` 且陈述未被反驳的行可能成为后续研究入口。
C3 是假式,不派实施去证明;C5 尚缺构造,也不直接派实施席。
本轮新增可实施逃逸见证 **0**。

### 成本口径

实际匹配计数与输出单个系数中的两色匹配项数如下:

| m | 每阶匹配数 k=0,...,m | 单个 a_k 的最大两色匹配项数 |
| --- | --- | --- |
| 2 | `1,6,3` | `6^2=36` |
| 3 | `1,15,45,15` | `45^2=2025` |
| 4 | `1,28,210,420,105` | `420^2=176400` |

这些是**未展开的平方积项**,不是收集同类项后的单项式数。
例如 m=4 的 s6 在 a1,...,a4 中只有 **9** 项,完整二次型有 **37** 项;
转回根参数时系数相关性的证明不会自动随这两个小数字而变廉。
以用户给定 **degree 7 E6: 2829 项 / 峰值 28 GB** 为唯一成本标尺:
本席没有据 176400 或 37 外推内存、心跳或构建时间。
没有测过一般 Gram 证书的峰值,也没有生成该证书。
选择保持匹配和与 Schur 块结构,不投入全根单项式大展开。

## 检索、碰撞与验证

以下是仓内检索命令及匹配行数;`--files` 的计数是路径数。
没有 `git grep -E`。三条阴性均配同样词界、分组/分支的阳性;
含 `.*` 的阴性另配同样 `.*` 的 28 行阳性。
阴性仅指所搜拼写,不宣称不存在等价定理。实际读到了矩阵平方根和 LDL 的带前提声明,
故没有把猜测名称未命中当成“库无矩阵分解”。

```text
rg --files --hidden -g AGENTS.md -g '!**/.git/**' -g '!**/.lake/**'
1 path, exit 0
rg -n 'MatchingIdentity|matching_identity|newtonHankel_posSemidef_iff_roots_real' D5
7 lines, exit 0
rg -n '\b(Gram|gram|hankel|Hankel|SexticEnvelope)\b' D5/S3/Zeros/Convolution D5/S3/Constants/Moments
27 lines, exit 0
rg -n '\b(conjTranspose_mul_self|posSemidef_iff_eq_transpose_mul_self|isSymm_iff|dotProduct_mulVec_nonneg|posSemidef_iff)\b' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean
3 lines, exit 0
rg -n '\b(lean|push)\b' Makefile
15 lines, exit 0
rg --files D5 -g '*Sextic*' -g '*Vandermonde*' -g '*Stieltjes*'
10 paths, exit 0
rg -n '\b(posSemidef_iff_eq|eq_transpose_mul_self|eq_conjTranspose_mul_self|sqrt_mul_self)\b' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix
0 lines, exit 1
rg -n '\b(posSemidef_iff_dotProduct_mulVec|conjTranspose_mul_self|of_dotProduct_mulVec_nonneg)\b' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix
11 lines, exit 0
rg -n '\b(constrainedGram|constrained_gram|matchingGram|matching_gram|matching_hankel)\b' D5
0 lines, exit 1
rg -n '\b(matching_identity|centered_real_sextic_discriminant|companion_trace_hankel_quadratic_identity)\b' D5
10 lines, exit 0
rg -n '\b(sqrt_mul_sqrt|eq_sqrt_mul_self|mul_self_sqrt|exists.*mul_self)\b' .lake/packages/mathlib/Mathlib/Analysis/Matrix
0 lines, exit 1
rg -n '\b(PosSemidef|sqrt)\b' .lake/packages/mathlib/Mathlib/Analysis/Matrix -g '*Pos*'
12 lines, exit 0
rg -n '\b(eigenvalues.*nonneg|to.*Group)\b' .lake/packages/mathlib/Mathlib/Analysis/Matrix
28 lines, exit 0
rg -n '\b(sqrt|mul_self|conjTranspose_mul_self)\b' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean
1 line, exit 0
rg -n '\b(sqrt|exists|conjTranspose)\b' .lake/packages/mathlib/Mathlib/Analysis/Matrix/Order.lean
5 lines, exit 0
rg -n '\b(symmetrize|matching_identity|centered_real_sextic_discriminant)\b' D5/S3/Zeros/Convolution/MatchingFiber.lean D5/S3/Zeros/Convolution/MatchingPolynomial.lean D5/S3/Zeros/CoefficientBounds/SexticDiscriminant.lean
9 lines, exit 0
rg -n '\b(sq_sum_le_card_mul_sum_sq|prod_nonneg|sum_nonneg)\b' .lake/packages/mathlib/Mathlib/Algebra/Order/Chebyshev.lean
4 lines, exit 0
rg -n '^### (3\.|5\.)' CLAUDE.md
18 lines, exit 0
rg -n 'preflight|git commit|推送前|push 前|push前' CLAUDE.md
14 lines, exit 0
```

碰撞终检:fetch 后固定远端快照
`46a5df329cdd85e11c873e7dd40f7e19f55cfb2d`,不移动工作树基线。

```text
git grep -n -P '\b(constrainedGram|constrained_gram|matchingGram|matching_gram|matching_hankel)\b' 46a5df329cdd85e11c873e7dd40f7e19f55cfb2d -- D5
0 lines, exit 1
git grep -n -P '\b(matching_identity|centered_real_sextic_discriminant|companion_trace_hankel_quadratic_identity)\b' 46a5df329cdd85e11c873e7dd40f7e19f55cfb2d -- D5
10 lines, exit 0
git ls-tree -r --name-only 46a5df329cdd85e11c873e7dd40f7e19f55cfb2d -- docs/reports/convolution/constrained-gram-probe-0909.md docs/reports/convolution/constrained-gram-probe-0909-snippets.lean
0 paths, exit 0
git ls-tree -r --name-only 46a5df329cdd85e11c873e7dd40f7e19f55cfb2d -- docs/reports/convolution/image-cone-probe-0909.md docs/reports/convolution/image-cone-probe-0909-snippets.lean
2 paths, exit 0
git diff --name-only e5e608c6f672b68921a33964667e270a04041d7b 46a5df329cdd85e11c873e7dd40f7e19f55cfb2d -- D5/S3/Zeros/Convolution D5/S3/Zeros/CoefficientBounds D5/S3/Constants
0 paths, exit 0
```

所用数学源码在这次远端增量中没有变更。本次明确撞上的是已有低阶数学:
F4/SE/SD 的绑定能力,已经判掉,没有为其新建声明地址。

Lean 仅运行 `make lean`,缓存收据为 `status=present`,项目与 Mathlib 均 warm。
第三次 **exit 0**,`Build completed successfully (12643 jobs)`;任务数含缓存复用,
不是新编译模块数。前两次 exit 2:首轮矩阵记号作用域遗漏及嵌套分母未消去;
第二轮只剩嵌套分母规范化。最终改成等价清分母恒等式,由 `ring` 直接验过。
没有更改 `maxHeartbeats`、`maxRecDepth`、任何构建预算或既有常数。
存在原有重放警告及片段空白风格警告,没有把“exit 0”说成“零警告”。
临时 `D5/S3/Zeros/Convolution/ConstrainedGramProbe0909.lean` 经默认 glob 编译,
随后原样移到 [探针片段](constrained-gram-probe-0909-snippets.lean),不成为生产模块。

一次性工件目录,下称 ATTEMPT:
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/constrained-gram-probe-0909/attempt-1`。
包含 `preregistered.md`、`exact_probe.py`、`numerics.json`、`supplement.json`、
`searches.json`、`cmp-v2.pdf`、`lean-probe-1.log` 至 `lean-probe-3.log`。
精确算术两次命令分别为
`uv run --with sympy==1.14.0 python ATTEMPT/exact_probe.py` 与加 `--supplement` 的同命令,
两次 exit 0。`pdftotext` 本机不可用(exit 127),改由实际安装的 `pypdf` 读取,没有靠旧报告补引文。
这些脚本和日志由本 worker 产出,runner 不补造。

### 离线最小复算

下段只需 Python 与 SymPy 1.14.0,不联网、不依赖留档报告;
从真实根差枚举匹配,可复算平衡样本和两条负校准。完整 1561 对的循环在 attempt 脚本中。

```python
from fractions import Fraction as F
from math import factorial, comb
import sympy as S

def ff(n, k):
    return factorial(n) // factorial(n-k)
def lam(m, k):
    return F(factorial(k), ff(2*m-k, k))*F(2*m+1-k, 2*m+1)
def mats(v):
    if not v:
        yield (); return
    i, rest = v[0], v[1:]
    yield from mats(rest)
    for j in rest:
        for M in mats(tuple(k for k in rest if k != j)):
            yield ((i,j),)+M
def image(r):
    n = len(r); b = [F(0)]*(n//2+1)
    for M in mats(tuple(range(n))):
        w = F(1)
        for i,j in M:
            w *= (r[i]-r[j])**2
        b[len(M)] += w
    return [b[k]/ff(n,k) for k in range(n//2+1)]
def output(b, d):
    m = len(b)-1
    return [lam(m,k)*b[k]*d[k] for k in range(m+1)]
def hankel(a):
    m = len(a)-1; s = [S.Integer(m)]
    for k in range(1,2*m-1):
        v = -sum((-1)**j*a[j]*s[k-j] for j in range(1,min(k-1,m)+1))
        s.append(v-((-1)**k*k*a[k] if k <= m else 0))
    return S.Matrix(m,m,lambda i,j:s[i+j])
for m in (2,3,4):
    b = image(tuple([-1]*m+[1]*m)); H = hankel(output(b,b))
    print(m, b, [H[:k,:k].det() for k in range(1,m+1)])
    unit = [F(comb(m,k)) for k in range(m+1)]
    a = output(unit,unit); H = hankel(a)
    c = S.Matrix([-S.Rational(a[1])/m,1]+[0]*(m-2))
    assert (c.T*H*c)[0] < 0
b = list(map(F,[1,6,9,4])); H = hankel(output(b,b))
c = (-H[:2,:2].inv()*H[:2,2:]).col_join(S.Matrix([1]))
assert H[:2,:2].det() == S.Rational(22437,1225)
assert (c.T*H*c)[0] == -S.Rational(24553351,407190)
```

## 已排除形态与明确未主张

已排除:

- 无输出实根前提却把 `Re(f(rho)^2)` 换成 `|f(rho)|^2` 的“Gram”。
- 先假设 H0 PSD 或正定,取矩阵平方根/LDL,再把所得分解当成该假设的证明。
- 在所有非负实根 Q,T 上成立的非负 Gram;校准一已反驳。
- 只加 B2 就宣称上述全矩阵非负;校准二已反驳。
- C3 的归一化 Hankel Schur 乘积恒等式,合法根例直接反驳。
- C4 的原始匹配权、常系数 L(c) 形式,合法根缩放反驳。
- 把边差平方自由化的输入替换:违反题设,本轮未对那个域做搜索,不冒充数学反例。

明确未主张:

- 未证明一般 m 的 H0 PSD、一般输出实根性、CMP Conjecture 5.3,也未证明这些陈述为假。
- 未找到统一的根相关匹配 Gram;未排除所有多项式/有理式/矩阵权 Gram。
- G2 是 26 项块 Gram,不是每个无标签匹配恰一项的严格格式;G3 是系数有理 Gram。
- 未把 `escapes=不能` 当不可证明性定理,未把数值正例当一般认证或 degree-8 推进。
- 未把 SD 的冻结成果、B2 的 Cauchy 后果重新声明为本席逃逸见证。
- 未完整形式化 G2/G3 从任意根列表到最终矩阵的整条装配;片段与纸面绑定的边界已逐项说明。
- 未核验全部第三方生态或全部数学文献。未打开原论文参考文献 [10] 的原文,
  其独立核验为 `ASSUMED-UNVERIFIED`,不参与判词。其他未打开文献不作为前提。
- 未实测一般符号 Gram 证书的最大块或峰值内存;不从唯一 E6 标尺外推。
- 未获独立评审或多模型共识。技能采用本地 `1.0.0-beta.42/skills/sshx/SKILL.md`
  的 worker 结果与推理纪律,本轮没有启动完整多席编排。
- 未 deposit、未冻结、未开 PR、未更改覆盖账。只提交报告与旁置 Lean 片段并推本席分支;
  提交号由 worker 的 `result.json` 中 `pushed.commits` 给出。

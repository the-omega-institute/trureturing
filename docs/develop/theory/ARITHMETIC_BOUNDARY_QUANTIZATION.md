# 算术边界的量化: 5040、整数判据与回返核舍入

本卷是 `docs/develop/theory/` 下的**参考输入**,日期为 2026-09-08。文献定理、仓内纸面推导和 Arb 区间证据分别标注;它们都不因写入本卷或摄取为 atom 而成为 Lean/kernel-frozen 真值。本卷不主张数学新颖性,不主张 RH 进展。

## 1. 长期研究约定与本轮问题

用户的原标签是 **GH**。目前没有已识别的 GH 数学定义;根据用户关于 RH 等价判据的上下文及既有 `QUANTUM-RH.md`,本卷暂以经典黎曼假设 RH 为工作解释,即所有非平凡 ζ 零点满足实部为 \(1/2\)。这不把 GH 擅自解释成广义 RH。

目标是持续研究整数索引、严格不等号、等号、零余量与量化规则之间的关系,给出明确的算术与量子模型接口及其剩余义务。本轮只回答一条具体问题: **对单位向量的酉回返核逐项作最近网格舍入,是否必保正性?** 第 5 节给出任意分辨率的纸面反例,第 6 节给出实际 ξ 数据上的区间证据。

研究 lane 为 `lane/math/quantized-gh-boundaries-0908`,工作树为 `/Users/auricstudio/trureturing-qgh-boundaries`,intake base 为 `45e7b20dd95dd8b2d7b8784392c1814193b80515`。本轮保持该 Git 基线,只增加本卷及其 canonical ingestion 输出,不引入新形式根、私有公理或冻结声明。

这是用户指定的长期核心问题研究线。host 目标轮次无上限,每次载体调用及其重试仍有界;同一症状第二次出现时停止原样重试并查根因。连续两周没有边际数学或证据增益时修订方法,不以增加卷数、有限样本数或计算精度冒充成功。继续由现有 host 驱动,不运行无限 daemon。本次有限增量不完成长期目标 S6;评审、PR 三门与 MERGED 落地由 caller 后续承担,未合并工作仍为 open。

## 2. 5040 与小素数: 两种编码不要混在一起

先把用户的问题译成普通算术:

\[
5040=2^4\,3^2\,5\,7.
\]

指数向量 \((4,2,1,1)\) 的坐标名称是素数 \((2,3,5,7)\):用了四个 2、两个 3、一个 5 和一个 7。**9 是 \(3^2\),是素数幂,不是素数,也不是独立的素因数坐标。** 向量必须带坐标名称;仅有 \((4,2,1,1)\) 不能确定 5040,因为

\[
7920=2^4\,3^2\,5\,11
\]

也有同一指数向量。

记 \(\tau(n)\) 为正因数个数,\(\sigma(n)\) 为正因数之和。因数在每个素数方向独立选择指数,故

\[
\tau(5040)=(4+1)(2+1)(1+1)(1+1)=60,
\]
\[
\sigma(5040)=(1+2+4+8+16)(1+3+9)(1+5)(1+7)
=31\cdot13\cdot6\cdot8=19344.
\]

**整个整数的 Zeckendorf 表示**采用 Fibonacci 权重 \(1,2,3,5,8,\ldots\),相邻权重不能同时占用,这里是

\[
5040=4181+610+233+13+3.
\]

**仓内的素数-黄金表**则先分解素因数,再把每个指数逐行作 Zeckendorf 编码。按旧卷定义 2.4 与定理 2.5 [Z],前三个权重为 \((1,2,3)\):

| 素数坐标 | 指数 | 权重 1 的位 | 权重 2 的位 | 权重 3 的位 |
|---|---:|---:|---:|---:|
| 2 | \(4=1+3\) | 1 | 0 | 1 |
| 3 | \(2=2\) | 0 | 1 | 0 |
| 5 | \(1=1\) | 1 | 0 | 0 |
| 7 | \(1=1\) | 1 | 0 | 0 |

每列把占用该位的素数相乘,得到 \((70,3,2)\),于是

\[
70^1\,3^2\,2^3=5040.
\]

完整带素数标签的表可逆:逐行还原指数,再乘回整数;反向则用唯一素因数分解和 Zeckendorf 唯一性。它提供坐标,不额外证明 RH。上面的整数恒等式由第 6 节程序作精确检查;编码解释沿用 [Z],不是本卷新定理。

### 小素数为什么让因数较丰?

对正整数 \(n\),由 \(\sigma\) 的乘法性和有限几何级数,

\[
A(n):=\frac{\sigma(n)}n
=\prod_{p^a\parallel n}\left(1+\frac1p+\cdots+\frac1{p^a}\right)
=\prod_{p^a\parallel n}\frac{1-p^{-a-1}}{1-p^{-1}}.
\]

固定指数 \(a\ge1\) 时,素数越小,每个倒数项越大。5040 的比值为 \(403/105\)。这解释了小素数对相对因数和的影响,并不意味着所有 Robin 余量沿乘法单调。

更精确地,对任意正整数 \(n\)、素数 \(p\) 及 \(a=v_p(n)\ge0\),包括 \(p\nmid n\) 的 \(a=0\) 情况,

\[
\frac{A(np)}{A(n)}
=\frac{1-p^{-(a+2)}}{1-p^{-(a+1)}}.
\]

证明就是把上述乘积的 \(p\) 因子由指数 \(a\) 换成 \(a+1\);其余因子抵消。对于 \(a=0\),比值正是 \(1+1/p\)。Robin 的边界也随 \(n\) 改变。对 \(n\ge2\),令 \(R(n)=e^\gamma\log\log n-A(n)\),有精确恒等式

\[
R(np)-R(n)=e^\gamma\log\left(1+\frac{\log p}{\log n}\right)
-A(n)\left(\frac{1-p^{-(a+2)}}{1-p^{-(a+1)}}-1\right).
\]

右边两项都是正量相减,上式本身不给余量变化的统一符号。Robin 判据实际使用的域为 \(n\ge5041\)。

对于连续的素数支撑,设 \(p_j\) 为第 \(j\) 个素数,\(k\ge1\),

\[
n=\prod_{j=1}^k p_j^{a_j},\quad a_j\ge1,\qquad
P_k=\prod_{j=1}^k p_j,\quad \theta(x)=\sum_{p\le x}\log p.
\]

同一几何级数恒等式给出

\[
A(n)=\frac{P_k}{\phi(P_k)}\prod_{j=1}^k(1-p_j^{-a_j-1}),
\qquad \log P_k=\theta(p_k).
\]

这里 \(\phi\) 是 Euler 函数。**素数幂修正乘积不能丢掉。** Nicolas 的边界是 \(\log\log P_k=\log\theta(p_k)\),不是恒等于 \(\log p_k\);两者的渐近比较不能替代精确等式。以上是初等纸面恒等式与旧卷坐标的整理,不建立新的算术桥定理。

## 3. RH 等价判据的离散边界图谱

本节的等价定理标为 **literature-attested**。统一使用自然对数,\(\gamma\) 为 Euler 常数;\(n,k,N\) 均为整数。下表给出边界的类型,随后固定每条的定义及量词。

| 判据 | 离散变量 | 需要满足的条件 | 零与端点的语义 |
|---|---|---|---|
| Robin [L,R] | 每个整数 \(n\ge5041\) | 严格上界 | 5040 排除;等号也违反严格式 |
| Lagarias [L] | 每个整数 \(n\ge1\) | 非严格上界 | \(n=1\) 精确等号;RH 下其余项严格 |
| Nicolas [N] | 每个整数 \(k\ge1\) | primorial 上的严格下界 | \(k=1\) 右端负;\(k=0\) 未定义 |
| Li [S] | 每个整数 \(n\ge1\) | 实数系数非负 | 索引整数不代表值整数;\(\lambda_0=0\) 仅约定 |
| Nyman-Beurling-Baez-Duarte [B1] | 有限维数 \(N\to\infty\) | 平方距离趋零 | 下确界为零不等于某个有限距离为零 |
| Baez-Duarte 系数 [B2] | 整数 \(k\to\infty\) | 对每个 \(\varepsilon>0\) 的衰减估计 | 有限前缀或个别系数的零不判全局 |

### Robin 与 Lagarias

Robin 定理是

\[
\mathrm{RH}\iff
\forall n\in\mathbb Z,\ n\ge5041:
\quad \sigma(n)<e^\gamma n\log\log n.
\]

5040 是经典定理排除的小整数区间端点,[R] 列出了该区间的例外。它不是由“令两边相等”定义的数,也不是 ζ 的一个零点。指数分解解释因数丰度,却不能单凭它推出 cutoff 或处理所有更大的整数。

令 \(H_n=\sum_{j=1}^n1/j\),\(T_n=H_n+e^{H_n}\log H_n\)。Lagarias 定理给出

\[
\mathrm{RH}\iff\forall n\ge1:\quad \sigma(n)\le T_n.
\]

在 \(n=1\) 时,\(H_1=T_1=\sigma(1)=1\),等号无条件成立。RH 成立时对所有 \(n\ge2\) 有严格式 \(\sigma(n)<T_n\)。[L] 的 Problem E、定理 1.1 及其证明同时支持这些量词。**这不声称在不假设 RH 时,每个其它单独整数处都已知不取等号。**

### Nicolas

对第 2 节定义的 \(P_k\),作者引言 [N] 的原量词是

\[
\mathrm{RH}\iff\forall k\ge1:\quad
\frac{P_k}{\phi(P_k)}>e^\gamma\log\log P_k.
\]

当 \(k=1\) 时 \(P_1=2\),右端因 \(0<\log2<1\) 而为负,式子有定义且成立。不能在这里除以右端或取其对数。若约定 \(P_0=1\),则 \(\log\log P_0=\log0\) 仍未定义,所以 \(k=0\) 不在定理中。本卷不使用该来源其它辅助函数的差值恒等式。

### Li

固定正规化

\[
\xi(s)=\frac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
\qquad
\lambda_n=\left.\frac1{(n-1)!}\frac{d^n}{ds^n}
\bigl(s^{n-1}\log\xi(s)\bigr)\right|_{s=1},\quad n\ge1.
\]

在 \(s=1\) 邻域取与 \(\xi(1)=1/2>0\) 相容的解析对数;常数分支差不影响该导数。Li 判据为

\[
\mathrm{RH}\iff\forall n\ge1:\quad \lambda_n\ge0.
\]

[S] 引言核对的是同一 Li 正规化的经典零点和表达

\[
\lambda_n=\lim_{Y\to\infty}\sum_{|\operatorname{Im}\rho|\le Y}
\left[1-\left(1-\frac1\rho\right)^n\right],
\]

其中非平凡零点按重数计。Li 原文 DOI 仅作书目信息,本轮未取得其全文;不把二手核对写成亲读原文。第 6 节直接从导数定义核对本次使用的 Taylor 系数关系。这里 \(\lambda_n\) 为实数;\(\lambda_0=0\) 是后续差分的约定,不是上述导数公式在 \(n=0\) 的取值。

### Nyman-Beurling-Baez-Duarte

令 \(\{u\}=u-\lfloor u\rfloor\),在整个正半轴取

\[
\mathcal H=L^2((0,\infty),dx),\quad
\chi=\mathbf1_{(0,1]},\quad f_k(x)=\{1/(kx)\},\quad k\ge1.
\]

[B1] 定理 1.1 给出

\[
\mathrm{RH}\iff\chi\in\overline{\operatorname{span}\{f_k:k\ge1\}}^{\mathcal H}.
\]

令 \(N\ge1\),并定义**平方距离**

\[
D_N=\inf_{a_1,\ldots,a_N\in\mathbb C}
\int_0^\infty\left|\chi(x)-\sum_{k=1}^Na_k f_k(x)\right|^2dx.
\]

子空间递增给出 \(D_{N+1}\le D_N\),且 \(D_N\ge0\)。等价条件为 \(D_N\downarrow0\),即

\[
\forall\varepsilon>0\ \exists N\ge1\ \exists(a_1,\ldots,a_N)\in\mathbb C^N:
\quad\int_0^\infty\left|\chi-\sum_{k=1}^Na_kf_k\right|^2dx<\varepsilon.
\]

取实系数也等价,因为丢掉虚部不增大误差。不能未经换算把范数改成 \((0,1)\) 上的范数;当 \(x>1\) 时,\(f_k(x)=1/(kx)\),尾部仍贡献积分。

### Baez-Duarte 系数与 Gronwall 对照

为避免与第 6 节 Li 差分的 \(c_j\) 混名,本小节加上标 BD:

\[
c_k^{\mathrm{BD}}=\sum_{j=0}^k(-1)^j\binom{k}{j}\frac1{\zeta(2j+2)},\quad k\ge0.
\]

[B2] 定理 1.1 给出

\[
\mathrm{RH}\iff\forall\varepsilon>0:\quad
c_k^{\mathrm{BD}}=O_\varepsilon(k^{-3/4+\varepsilon})\quad(k\to\infty,\ k\ge1).
\]

准确含义是每个 \(\varepsilon>0\) 都有 \(C_\varepsilon>0,K_\varepsilon\ge1\),使所有整数 \(k\ge K_\varepsilon\) 满足 \(|c_k^{\mathrm{BD}}|\le C_\varepsilon k^{-3/4+\varepsilon}\)。不能删去绝对值、\(\varepsilon\) 或它对常数的依赖。

Gronwall 定理 [L,定理 2.2] 则是无条件的比较背景:

\[
\limsup_{n\to\infty}\frac{\sigma(n)}{n\log\log n}=e^\gamma.
\]

它不是又一行 RH 等价判据。任何有限前缀都不能单独证明本节的全称条件、闭包条件或渐近估计。

## 4. 整数取整、真实等号与区间判定

对整数 \(a\) 和任意实数 \(T\),有初等恒等关系

\[
a<T\iff a\le\lceil T\rceil-1,\qquad
a\le T\iff a\le\lfloor T\rfloor.
\]

证明:前式右边是严格小于 \(T\) 的最大整数,后式右边是不大于 \(T\) 的最大整数。因此 Robin 对应 \(\lceil e^\gamma n\log\log n\rceil-1-\sigma(n)\ge0\),Lagarias 对应 \(\lfloor T_n\rfloor-\sigma(n)\ge0\)。**取整余量为零表示落入一个格子,不表示实数余量为零。** 前者的零格为 \(\sigma(n)<T\le\sigma(n)+1\),后者为 \(\sigma(n)\le T<\sigma(n)+1\)。这些是记账事实,不是新数学或新的 RH 方法。[Z] 第 33 节已有 Lagarias floor 缺口,第 34 节另有价格正规化勘注;本卷不重做它的反驳或有限证书。

一个无条件、无需小数的见证是 \(n=2\):

\[
\sigma(2)=3,\quad H_2=3/2,\quad
3<T_2=\frac32+e^{3/2}\log(3/2)<4.
\]

简证所需的粗界:

\[
4<e^{3/2}<5,\qquad 3/8<\log(3/2)<1/2.
\]

指数级数前四项和为 \(67/16>4\);从第四次幂项 \(27/128\) 起,相邻项比不超过 \(3/10\),所以全和不超过 \(67/16+(27/128)/(1-3/10)=2011/448<5\)。对数由 \(\int_0^{1/2}(1+t)^{-1}dt\) 给出,用 \(1-t<(1+t)^{-1}<1\) 在区间内部积分即可。代回即得 \(3<T_2<4\),但 \(\lfloor T_2\rfloor-\sigma(2)=0\)。

有理区间只在端点充分时作判定。若已认证 \(L\le T\le U\),则:

| 待判命题 | true 的充分条件 | false 的充分条件 | 其它情况 |
|---|---|---|---|
| \(a<T\) | \(a<L\) | \(a\ge U\) | undecided |
| \(a\le T\) | \(a\le L\) | \(a>U\) | undecided |

若证书更强,给出的是**严格包围** \(L<T<U\),两行都可在 \(a\le L\) 判 true、在 \(a\ge U\) 判 false。端点开闭性必须随证书保留。对普通闭区间,要锁定 \(\lfloor T\rfloor=q\),可验 \(q\le L\le U<q+1\);要锁定 \(\lceil T\rceil=q\),可验 \(q-1<L\le U\le q\)。落在 undecided 时须加精度或作符号证明,不能按近似小数猜等号。

## 5. 纸面反例: 任意分辨率的最近网格舍入都不普遍保持回返正性

**状态: repo-derived 纸面构造,此处代数核对;非 kernel-frozen,未作全球新颖性主张。** 下面反驳的是一条具名全称规则,不是 RH。

**命题。** 对每个整数 \(m\ge1\),置 \(h=1/m\),定义

\[
Q_m(s)=\frac{\lfloor ms+1/2\rfloor}{m}\quad(s\in\mathbb R),
\]

即最近网格舍入,正中间的 tie 向 \(+\infty\)。存在五维酉算子 \(U\) 及单位向量 \(a\),使所有整数 \(k\) 的回返 \(r_k=\langle a,U^ka\rangle\) 为实数,\(r_0=1\),且

\[
T=(r_{j-i})_{0\le i,j\le2}\succeq\frac h{12}I_3,
\]

而逐项舍入的矩阵 \(Q_m[T]\) 不定。包括单位对角线在内的每一项都用同一个 \(Q_m\),对角线保持 1。对 \(v=(1,-2,1)^{\mathsf T}\),精确有

\[
v^{\mathsf T}Q_m[T]v=-2h,\qquad \det Q_m[T]=-h^2.
\]

**证明。** 内积取第二个变量线性。令

\[
\eta=h/12,\quad t=1-h/3,\quad\theta=\arccos t,\quad\omega=e^{2\pi i/3},
\]
\[
U=\operatorname{diag}(e^{i\theta},e^{-i\theta},1,\omega,\omega^2).
\]

取 \(a\) 的五个坐标为非负实数,平方依次为

\[
\left((1-\eta)/2,(1-\eta)/2,\eta/3,\eta/3,\eta/3\right).
\]

由于 \(0<h\le1\),所有权重正且和为 1;\(U\) 酉。对任意整数 \(k\),

\[
r_k=(1-\eta)\cos(k\theta)+\frac\eta3(1+\omega^k+\omega^{2k})
\]

为实数且 \(r_{-k}=r_k\)。三次单位根的和在 \(k=\pm1,\pm2\) 时为零,所以

\[
r_1=(1-\eta)t,\qquad r_2=(1-\eta)(2t^2-1).
\]

前三个历史向量 \(a,Ua,U^2a\) 的 Gram 矩阵正是 \(T\)。令 \(C_{ij}=\cos((j-i)\theta)\);它也是 Gram 矩阵,例如取平面单位向量 \((\cos(i\theta),\sin(i\theta))\)。于是

\[
T=(1-\eta)C+\eta I_3\succeq\eta I_3.
\]

另一方面直接展开得到

\[
\frac{1-r_1}{h}=\frac5{12}-\frac h{36}\in(0,1/2),
\qquad
\frac{1-r_2}{h}=\frac{17}{12}-\frac h3+\frac{h^2}{54}\in(1/2,3/2).
\]

第一式介于 \(7/18\) 与 \(5/12\) 之间;第二式至少 \(13/12>1/2\),且不超过 \(17/12+1/54=155/108<3/2\)。故两个数都严格位于各自舍入格内部,没有 tie。因 \(1=mh\),得

\[
Q_m(r_1)=1,\quad Q_m(r_2)=1-h,\qquad
Q_m[T]=\begin{pmatrix}1&1&1-h\\1&1&1\\1-h&1&1\end{pmatrix}.
\]

矩阵乘法给出 \(v^{\mathsf T}Q_m[T]v=6-8+2(1-h)=-2h\);展开行列式得 \(-h^2\)。同时标准基向量的二次型为 1,所以矩阵既有正方向也有负方向,是不定矩阵。证毕。

**端点、尺度和隐藏状态。** \(h=0\) 排除;本构造的输入模型依赖 \(m\),没有一个固定输入对所有分辨率失败的结论。若把核与网格同时乘以 \(b>0\),相应规则为 \(s\mapsto bQ_m(s/b)\),负二次型乘以 \(b\),不能因换单位而消失;这时对角线是 \(b\),不再伪称单位向量正规化为 1。

任何维数的 Gram 矩阵的主块都半正定。因此,只要保持上述**已舍入的三次观测块**不变,增加隐藏状态或扩大 Hilbert 空间都不能赋予它共同的酉回返实现。该结论限定于 unitary-return/Gram 实现,不覆盖所有量子可观测量。

第 6 节程序还对 \(m=1,2,10,200,1000000\) 用 `Fraction` 检查原矩阵的顺序主子式为正,舍入行列式为 \(-1/m^2\),二次型为 \(-2/m\),退出码 0。这些是精确抽查;全称命题由上面的构造和不等式证明承担。它本身没有证明实际 ξ 序列在每种分辨率上都失败。

## 6. 实际 ξ 的三阶专门化: Arb 严格区间证据

**状态: 数值库支持的严格区间证据加精确有理矩阵运算;不依赖 RH,不是 Lean/kernel 证书。** [Q] 已有 Li 差分回返定义、三观测 Schur 边界及未经区间认证的 \(r_1,r_2\) 小数。本节沿用其定义,新增严格包围及 \(Q_{200}\) 的实际算术假阴性,不把旧证明重报为新发现。

### 从 Taylor 系数到 Li 回返

沿用

\[
\lambda_0=0,\quad c_0=2\lambda_1,\quad
c_j=\lambda_{j+1}-2\lambda_j+\lambda_{j-1}\ (j\ge1),\quad r_j=c_j/c_0.
\]

这里 \(c_j\) 不是第 3 节的 \(c_k^{\mathrm{BD}}\)。写

\[
\log\frac{\xi(1+t)}{\xi(1)}=\sum_{q\ge1}b_qt^q.
\]

从 Li 的导数定义提取 \((1+t)^{n-1}\log\xi(1+t)\) 的 \(t^n\) 系数,得到

\[
\lambda_n=n\sum_{q=1}^n\binom{n-1}{q-1}b_q.
\]

常数 \(\log\xi(1)\) 乘以次数 \(n-1\) 的多项式,对该系数无贡献。因此

\[
\lambda_1=b_1,\quad\lambda_2=2b_1+2b_2,\quad
\lambda_3=3b_1+6b_2+3b_3,
\]
\[
c_0=2b_1,\quad c_1=2b_2,\quad c_2=2b_2+3b_3,\quad
r_1=\frac{b_2}{b_1},\quad r_2=\frac{2b_2+3b_3}{2b_1}.
\]

程序认证 \(b_1>0\),所以除法合法。取 \(s=1+t\),`zeta(deflate=True)` 表示 \(\zeta(s)-1/(s-1)\);因而

\[
1+t\,\zeta_{\rm deflated}(1+t)=t\zeta(1+t)
\]

在 \(t=0\) 正则。程序中的 `x` 正是 \(\xi(1+t)\),常数项含精确值 \(1/2\)。`ctx.cap=4` 保留到三次幂,已足够计算上面三项;这不是截取未知零点或假设尾部为零。

### 严格包围与舍入的精确失败

Python-FLINT 0.8.0 的 Arb,256 位精度,给出下列经球比较确认的严格有理包围。令 \(d=10^{18}\):

\[
\frac{999196806720852614}{d}<r_1<\frac{999196806720852615}{d},
\]
\[
\frac{996790337371607624}{d}<r_2<\frac{996790337371607625}{d},
\]
\[
\frac{1820249309832}{d}
<g:=r_2-(2r_1^2-1)
<\frac{1820249309833}{d}.
\]

这些不是把显示的小数四舍五入后当成区间。球算术单独比较了每个有理端点。原实对称矩阵

\[
T=\begin{pmatrix}1&r_1&r_2\\r_1&1&r_1\\r_2&r_1&1\end{pmatrix}
\]

的全部顺序主子式为

\[
1>0,\qquad 1-r_1^2>0,\qquad
\det T=(1-r_2)(1+r_2-2r_1^2)=(1-r_2)g>0.
\]

这里 \(0<r_1<1\)、\(r_2<1\)、\(g>0\) 全由包围推出,故 Sylvester 判据给出严格正定。程序还只用 \(r_1,r_2\) 的有理上下界验证 \(L_2-(2U_1^2-1)>0\),作为不依赖区间相关性的精确检查。

对于 \(m=200\),两个区间分别严格包含在最近网格的格子

\[
r_1\in(399/400,401/400),\qquad
r_2\in(397/400,399/400).
\]

所以 \(Q_{200}(r_1)=1\),\(Q_{200}(r_2)=199/200\),对角线仍为 1。直接有理运算给出

\[
\det Q_{200}[T]=-\frac1{40000},\qquad
(1,-2,1)Q_{200}[T](1,-2,1)^{\mathsf T}=-\frac1{100}.
\]

这是**舍入规则在实际算术数据上的假阴性**,即把一个正定观测块变成了不定块。负性是对已舍入矩阵的正确判定,不能转移为对原始矩阵或 RH 的反例。未舍入的有限正定性也不证明全阶正性。

### 可执行复现

在 `/tmp` 中执行下面完整命令即可复现。依赖固定为 `python-flint==0.8.0`;Python 标准库的 `Fraction` 负责精确有理运算。实施 worker 独立执行同一程序,退出码 0,最后输出 `python-flint=0.8.0 precision=256 cap=4 PASS`。信任边界包括 Python-FLINT 的接口、FLINT/Arb 特殊函数及级数球包围实现、Python 和运行环境;这没有生成 Lean 证明项。

```sh
uv run --with python-flint==0.8.0 python - <<'PY'
from fractions import Fraction as F
from math import floor, prod
import flint
from flint import arb, arb_series, ctx

def toeplitz(x, y):
    return [[F(1), x, y], [x, F(1), x], [y, x, F(1)]]

def det3(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))

def witness(a):
    v = [1, -2, 1]
    return sum(v[i] * a[i][j] * v[j] for i in range(3) for j in range(3))

def q(x, m):
    return F(floor(m * x + F(1, 2)), m)

assert prod(p**a for p, a in zip([2, 3, 5, 7], [4, 2, 1, 1])) == 5040
assert prod(a + 1 for a in [4, 2, 1, 1]) == 60
assert prod(sum(p**j for j in range(a + 1))
            for p, a in zip([2, 3, 5, 7], [4, 2, 1, 1])) == 19344
assert 4181 + 610 + 233 + 13 + 3 == 70 * 3**2 * 2**3 == 5040
assert 2**4 * 3**2 * 5 * 11 == 7920
print("arithmetic: 5040, tau=60, sigma=19344, both encodings, 7920 OK")

for m in [1, 2, 10, 200, 1000000]:
    h, eta, t = F(1, m), F(1, 12 * m), 1 - F(1, 3 * m)
    r1, r2 = (1 - eta) * t, (1 - eta) * (2 * t*t - 1)
    assert 0 < (1-r1)/h == F(5, 12)-h/36 < F(1, 2)
    assert F(1, 2) < (1-r2)/h == F(17, 12)-h/3+h*h/54 < F(3, 2)
    a = toeplitz(r1, r2)
    assert 1-r1*r1 > 0 and det3(a) > 0
    rounded = [[q(x, m) for x in row] for row in a]
    assert rounded == toeplitz(F(1), 1-h)
    assert det3(rounded) == -h*h and witness(rounded) == -2*h
    print("family", m, "PD=True", "det=", det3(rounded), "vTv=", witness(rounded))

ctx.prec, ctx.cap = 256, 4
t = arb_series([0, 1])
s = 1 + t
x = s * (-s * arb.pi().log() / 2).exp() * (s/2).gamma() * (1+t*s.zeta(deflate=True)) / 2
assert x[0].contains(arb(1)/2)
f = (x/x[0]).log()
assert f[1] > 0
r1, r2 = f[2]/f[1], (2*f[2]+3*f[3])/(2*f[1])
gap = r2 - (2*r1*r1-1)
d = 10**18
endpoints = [(999196806720852614, 999196806720852615),
             (996790337371607624, 996790337371607625),
             (1820249309832, 1820249309833)]
for name, value, (lo, hi) in zip(["r1", "r2", "gap"], [r1, r2, gap], endpoints):
    assert arb(lo)/d < value and value < arb(hi)/d
    print(name, str(lo)+"/"+str(d), "< value <", str(hi)+"/"+str(d))
bounds = [(F(lo, d), F(hi, d)) for lo, hi in endpoints]
assert 0 < bounds[0][0] < bounds[0][1] < 1
assert 0 < bounds[1][0] < bounds[1][1] < 1
assert bounds[1][0] - (2*bounds[0][1]**2-1) > 0
assert 1-r1*r1 > 0 and (1-r2)*gap > 0
for (lo, hi), expected in zip(bounds[:2], [F(1), F(199, 200)]):
    assert q(lo, 200) == q(hi, 200) == expected
rounded = toeplitz(F(1), F(199, 200))
assert q(F(1), 200) == 1
assert det3(rounded) == -F(1, 40000)
assert witness(rounded) == -F(1, 100)
print("actual xi: PD=True, Q_200 det=-1/40000, vTv=-1/100")
print("python-flint="+flint.__version__, "precision="+str(ctx.prec), "cap="+str(ctx.cap), "PASS")
PY
```

## 7. 障碍登记与下一步

本轮增加的证据是:一个指定普遍保正规则已被纸面构造反驳,并且它在实际 ξ 的一个严格认证三阶块上确实失败。它没有排除 RH 的任何未知情形。以下是本卷的研究义务,不是手写消化状态或新形式工单。

| 义务 | 当前边界 | 下一次能改变它的结果 |
|---|---|---|
| GH 的准确含义 | 只有用户字面标签,采用工作 RH 解释 | 用户提供可识别定义后,重新核对哪些结论仍适用 |
| 对实际序列的保正量化 | 不受约束的逐项最近网格舍入已失败 | 给出保正且有误差界的结构化规则;候选是在单位圆盘内舍入 Schur 参数,再精确传输回矩阵 |
| Schur 端点与历史依赖 | 中心和尺度依赖全部前序数据 | 处理奇异主块、零 pivot 和 \(\lvert\alpha\rvert=1\) 端点;证明误差不会因传输失控,不能只投影一个区间 |
| 算术桥 | 已有素数因子乘积恒等式 | 保留 \(\prod(1-p^{-a-1})\) 及 \(\log\theta(p_k)\),证明与实际回返核之间可使用的定量关系 |
| 全局正性与尾项 | 第 6 节只处理三阶 | 对全阶实际 Li 回返给出统一正性或可闭合的尾估计;有限检查不能替代 |
| 形式与发布 | 纸面和数值证据,未冻结、未合并 | caller 的独立评审、canonical PR 三门及 MERGED;形式化另按准入处理 |

不能把 Robin/Lagarias 余量放到一个对角算子上,再把其正性重命名为量子证明;那只重新编码目标不等式。即使构造了保正的近似核,也必须另外证明其与原实际序列的关系足以传递所需全称结论。本轮不重做相邻 #5908、#6160、#6298 所属的 Robin 有限证书、整数资源优化或物理响应 no-go 工作。

### PRO 提供的下一篇纸面目标: 距离的算子实现

以下留作后续附录目标,本轮不宣称已完成新的谱判据。使用第 3 节的 \(\mathcal H,\chi,f_k,D_N\),在 \(\ell^2(\mathbb N_0)\) 的标准基上设

\[
h_0=\chi,\quad h_k=f_k/k\ (k\ge1),\qquad T e_k=h_k.
\]

因为 \(\|f_k\|_{\mathcal H}^2=\|f_1\|_{\mathcal H}^2/k\),且 \(f_1\) 在 \((0,1]\) 有界、在 \((1,\infty)\) 等于 \(1/x\),候选合成算子 \(T:\ell^2\to\mathcal H\) 的 Hilbert-Schmidt 范数平方为

\[
1+\|f_1\|_{\mathcal H}^2\sum_{k\ge1}k^{-3}<\infty.
\]

正确的正迹类对象是 **\(A=T^*T\)**,作用在 \(\ell^2\);不能写成类型不匹配的 `A=TT`。若 \(P_N\) 投影到 \(e_0,\ldots,e_N\),令 \(A_N=P_NAP_N\) 视为有限矩阵,待系统写明的目标是

\[
D_N=\sup\{\delta\ge0:A_N-\delta e_0e_0^*\succeq0\},
\qquad \mathrm{RH}\iff\inf_{N\ge1}D_N=0.
\]

目标必须使用全半轴范数,并处理有限 Gram 块奇异时的距离与减秩阈值;不能依赖未经证明的可逆性。缩放 \(f_k\mapsto f_k/k\) 不改变任何有限线性张成空间。即使上述实现全部写成证明,\(A\succeq0\) 本来就由 \(T^*T\) 自动成立,RH 内容仍在距离阈值趋零的全局条件,不会因“已有正算子”自动解决。

## 8. 来源核对与产地

### 本轮实际核对的数学来源

下列六份外部预印本或论文已在本轮成功下载并核对,两个仓内引用则按钉版的本地文件读取。Li DOI 仅是书目链接,没有取得其全文。HTML 用数学 `alttext` 保留公式,PDF 按页提取核对。本地源字节与 SHA-256 收据保存在实施 attempt 工件中;这些下载和提取工具不承担数学正确性。

| 标记 | 已检查文本 | 本卷使用范围 |
|---|---|---|
| [L] | [Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis](https://arxiv.org/html/math/0008177v2) | Problem E、定理 1.1、式 (1.2)、定理 2.2 和第 3 节证明;弱式全称等价、RH 下严格性、Robin 域及 Gronwall |
| [N] | [Nicolas, Small values of the Euler function and the Riemann hypothesis](https://arxiv.org/html/1202.0729v2) | 引言在 primorial 定义之后的 \(\forall k\ge1\) 严格式;未使用其它差值辅助恒等式 |
| [S] | [Suzuki, Li coefficients as norms of functions in a model space](https://arxiv.org/html/2301.05779v2) | 引言式 (1.1)、全体正整数的非负条件、ξ 定义和参考文献 [8];Li 原文 [DOI 10.1006/jnth.1997.2137](https://doi.org/10.1006/jnth.1997.2137) 仅书目,未取得全文 |
| [B1] | [Baez-Duarte, A strengthening of the Nyman-Beurling criterion for the Riemann hypothesis, 2](https://arxiv.org/pdf/math/0205003v1) | PDF 第 1-2 页,全半轴空间、自然数生成族、定理 1.1 的闭包条件 |
| [B2] | [Baez-Duarte, A new necessary and sufficient condition for the Riemann hypothesis](https://arxiv.org/pdf/math/0307215) | PDF 第 1 页定理 1.1,系数定义及每个 \(\varepsilon>0\) 的指数 \(-3/4+\varepsilon\) |
| [R] | [Choie, Lichiardopol, Moree, Sole, On Robin's criterion for the Riemann hypothesis](https://www.numdam.org/article/JTNB_2007__19_2_357_0.pdf) | 期刊页 357-358 的判据和有限例外列表;DOI 10.5802/jtnb.591;未亲读 Robin 1984 原文 |
| [Q] | [钉版 QUANTUM-RH.md](https://github.com/the-omega-institute/trureturing/blob/45e7b20dd95dd8b2d7b8784392c1814193b80515/docs/develop/theory/QUANTUM-RH.md) | 本地同一 HEAD 的 Li 差分定义、三片 Schur 边界、实际 ξ 小数及“不是严格区间认证”的原限定;定位约 49898、50545、50849 行 |
| [Z] | [钉版 ZECKENDORF_EULER_5040.md](https://github.com/the-omega-institute/trureturing/blob/45e7b20dd95dd8b2d7b8784392c1814193b80515/docs/develop/theory/ZECKENDORF_EULER_5040.md) | 本地同一 HEAD 的定义 2.4、定理 2.5、第 33 节 floor 缺口及第 34 节价格正规化勘注 |

[Q,Z] 是参考源的出处,其文字不构成 kernel 状态证明。以上文献查询支持判据的准确陈述;不构成对第 5 节构造的全球新颖性检索或新颖性结论。

### 载体与独立性

本卷由 caller 的 `consensus-rnd:sshx` implementation brief 驱动的 Codex worker 写作,worker 未调用新的 skill 或派出子席。worker 独立读文献、核对纸面代数并运行第 6 节程序,没有读取本轮 thinking 日志或 peer review 工件。这里的“独立复算”指重新执行与核对,也不是实施者给自己签发独立评审批准。先验边界为 Codex `repo-prior-exposed`、oracle `external-prior-exposed`;同轮 peer 输出不作为实施输入,不声称先验无污染。

以下载体事实由 caller 提供,worker 未读取其私人运行日志。六个隔离 thinking 席最终均为 `revise`;caller 经元层收敛保留端点和正规化限制,选择了本卷的小型反驳及实际 ξ 区间证据。**这不表示六席一致批准一个未经修改的旧计划。** 有效 thinking 结果来自 oracle 回退失败后使用的 Codex,不能据此声称模型族多样性。

独立的实际 GPT PRO 咨询已完成,caller 提供的记录为:

| 字段 | 原记录 |
|---|---|
| task | `080f1df1-b4cf-4e0a-b1c4-d76dd21fcb1a` |
| conversation | `conv_b9e496c90a421437` |
| pool | `chrono-chatgpt-pro-pool` |
| dispatch model | `chatgpt-5.5-pro` |
| terminal model | 字面字符串 `6\nPro`,按 JSON 字符串表示为 `"6\\nPro"` |
| ChatGPT URL | <https://chatgpt.com/c/6a9fe809-5830-83ec-8008-2fa7d47d2d92> |

dispatch 与终态字段是两条不同观测,本卷不据此推断未见的精确后端型号。原 pool 的前两次尝试均以 `page.goto Page crashed` 失败,没有研究产出。另一个 PRO follow-up `e512bb9d-21ac-46f4-8209-9941632be445` 在本次 intake 中为 pending,不能引用为已完成回答。PRO 的建议仍是可错参考输入;第 7 节对 \(T^*T\) 的类型修正明确保留。

本卷的 canonical 摄取命令为:

```sh
make ingest BASE=45e7b20dd95dd8b2d7b8784392c1814193b80515 SOURCE=docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md
```

摄取计数、atom 样本和退出码以 worker 结果信封中的实测输出为准,不能把摄取成功写成定理冻结或 PR 已合并。后续评审纠正须明确记下被改判的结论及其证据,已摄取 atom 不手改、不删除。

## 9. 追加勘注: 终态字符串与本次来源

日期 2026-09-08。本次 implementation worker 按 `consensus-rnd:sshx` worker 模式执行,没有派出子席,没有读取 peer 日志,没有提交、推送或操作 PR。以下为参考输入中的纸面论证与数值库证据,不是独立评审批准,也不是 Lean-frozen 定理。长期研究目标保持 active。

**具体勘误,只追加不改旧文:** 第 8 节把 terminal model 当成含字面反斜杠的字符串,这是记录错误。caller 指定的 `pro-map-task-complete.json` 经本次 JSON 解析,其 model 字段的 Unicode codepoints 恰为 `[54,10,80,114,111]`:字符 `6`,一个实际 LF,再接 `Pro`。正确的 JSON 序列化是 `"6\nPro"`,其中只有一个换行转义序列;不是第 8 节所写的含两个反斜杠的序列化。原 JSON SHA256 为 `6274bc727c4a83f7056a8112edee31940604806de34a0c7d4d3413cb32f1c715`。本勘注不据此推断未见的后端型号,不改变第 5-6 节数学。

本次实际源 HEAD 为 `8698bf1a197adb887967cb6722261ea525ea9400`,已经包含 caller 提交的第一卷。`45e7b20dd95dd8b2d7b8784392c1814193b80515` 仅保留为历史 intake 与摄取 BASE。追加前本卷 598 行,源 SHA256 为 `1051e55d93ab1beae2cfc2f4fcee04a6f9c79b1a17792c5ce187286d20b44404`;原文及 62 个已摄入 atom 全部保留。以下使用 [Q]、[Z] 的当前 HEAD 字节,其 SHA256 分别为 `4d38746e7e83ef96bb8c5af3b58f2e6d7a51484f4cbdd673ca4e644fa34bf246`、`2c60183ac740a7426db7f9113b5d769f883382d75bb216e6dfa780c42fca11f7`。

## 10. 指数截面、距离与已有的算术损失

### 坐标独立不指定度量

固定非空有限素数集 \(P\),令 \(a=(a_p)_{p\in P}\)。素数指数是独立的坐标标签;选择内积 \(\langle a,b\rangle=\sum_{p\in P}a_pb_p\) 后,这些坐标轴才是欧氏正交轴。也可以选择正权内积 \(\sum_pc_pa_pb_p\),其中 \(c_p>0\);那是另一个明确的度量,不能默认为同一距离。

在上述欧氏度量中,设 \(w=(\log p)_{p\in P}\),\(t=\log n\)。连续超平面 \(w\cdot a=t\) 有正交分解

\[
a=\frac{t}{\|w\|^2}w+a_\perp,\quad w\cdot a_\perp=0,
\qquad \|a\|^2=\frac{t^2}{\|w\|^2}+\|a_\perp\|^2.
\]

这是正交投影与勾股定理的直接应用;非负指数松弛取此超平面与非负正交象限的交。对于精确的 \(t=\log n\),若 \(P\) 包含 \(n\) 的素数支撑,唯一分解定理使截面中只有一个非负整数指数向量;不包含时可以没有。它不是同一个 \(n\) 的许多整数编码解。因此实际整数搜索比较的是区间薄层 \(t_0\le w\cdot a\le t_1\) 或预算 \(w\cdot a\le t\),不能把连续截面的维数当成同一整数的自由度。

### 黄金位是编码,不会新增独立方向

逐素数的 Zeckendorf 编码把 \(a_p\) 写成 \(\sum_jF_jb_{pj}\),\(b_{pj}\in\{0,1\}\),且相邻位不能同时为 1。唯一编码没有增加指数的独立自由度。原指数度量拉回位坐标后是

\[
\|\delta a\|^2=\sum_p\left(\sum_jF_j\delta b_{pj}\right)^2.
\]

同一素数的不同比特间出现交叉项 \(2F_iF_j\delta b_{pi}\delta b_{pj}\)。若另把所有位视作欧氏正交轴,就更换了度量,不会保留原来的勾股距离。\(\sigma\) 的乘法性也要求互素,不能把同一素数的位相乘分开:

\[
\sigma(2^4)=31\ne\sigma(2)\sigma(2^3)=3\cdot15=45.
\]

### Robin 的函数曲率与已有 KL 恒等式

令 \(F(a)=\log(\sigma(n)/n)=\sum_pf_p(a_p)\)。对实指数 \(a_p\ge0\) 作同一有限支撑延拓,

\[
f_p(a)=\log\frac{1-p^{-a-1}}{1-p^{-1}},\qquad
f_p''(a)=-\frac{(\log p)^2p^{a+1}}{(p^{a+1}-1)^2}<0.
\]

Hessian 是对角的,但曲率随素数和指数变化。普通欧氏距离没有单独决定 Robin 符号的信息。已有 [Z] 第十二章定理 12.2、12.3 与推论 12.4(本次源约 2210-2460 行)给出了连续最优指数、精确 Bernoulli KL 损失及

\[
\Delta(n)=\mathfrak D(n)-\mathfrak Q(\log n),\qquad
\mathrm{RH}\iff\mathfrak D(n)>\mathfrak Q(\log n)\quad(n>5040).
\]

这里 \(\Delta(n)=\gamma+\log\log\log n-F(a)\),其符号与 Robin 的严格上界相同。本节引用已有损失公式,不声称重新发现连续优化器或 KL 分解。截面几何能组织搜索;仍须比较函数损失与连续超额,不能用距离替代这笔比较。

## 11. 三片 Schur 坐标的正交几何与量化

### 既有 Schur 条件的投影解释

沿用 [Q] 约 50545 行后的三片边界。三个单位历史向量 \(u_0,u_1,u_2\) 的相邻内积为实数 \(x\),两端内积为实数 \(y\)。投影到中间向量后,残差 \(r_0=u_0-xu_1\)、\(r_2=u_2-xu_1\) 都与 \(u_1\) 正交,且

\[
\|r_0\|^2=\|r_2\|^2=1-x^2,\qquad
\langle r_0,r_2\rangle=y-x^2.
\]

Cauchy-Schwarz 给出 \(|y-x^2|\le1-x^2\)。反过来,消去中间的单位块,Schur 余量为对角 \(1-x^2\)、非对角 \(y-x^2\) 的二阶矩阵,该不等式保证其 PSD,也就保证原矩阵 PSD。\(|x|=1\) 时残差为零,必须有 \(y=1\);\(|x|<1\) 时可定义

\[
\beta=\frac{y-x^2}{1-x^2},\qquad
y=x^2+(1-x^2)\beta,\qquad |\beta|\le1.
\]

这正是用户“沿截面取正交部分”的一个有用、精确的连接:中心分量与残差分量各自承载明确的内积约束。此解释复用既有 [Q],不增加全阶 RH 正性的结论。

### 两个不同的量化输出空间

对固定输入 \(x,y\) 采用 \(Q_m(t)=\lfloor mt+1/2\rfloor/m\),\(m\ge1\) 为整数,正负半格的平局都向正无穷取整。直接逐项舍入得到 \(x'=k_x/m,y'=k_y/m\),令

\[
B=m^2+mk_y-2k_x^2,\qquad
\det T(x',y')=\frac{(m-k_y)B}{m^3}.
\]

全部主子式给出 PSD 当且仅当 \(|k_x|\le m,|k_y|\le m,B\ge0\);PD 当且仅当 \(|k_x|<m,k_y<m,B>0\)。失败时因对角全为 1 而有正方向,所以非 PSD 就是不定。若 \(B<0\),精确负向量 \(v=(m,-2k_x,m)\) 满足 \(v^{\mathsf T}T v=2B\)。(这里只用 Python 任意精度整数形成行列式乘积。)

Schur 舍入则取 \(x'=k_x/m,\beta'=k_\beta/m\),再重建

\[
y'=x'^2+(1-x'^2)\beta'
=\frac{mk_x^2+(m^2-k_x^2)k_\beta}{m^3},
\quad \det T(x',y')=(1-x'^2)^2(1-\beta'^2).
\]

因为最近网格舍入把 \([-1,1]\) 映入自身,这对所有允许的输入与所有 \(m\) 都保 PSD;PD 恰当两个舍入坐标绝对值都严格小于 1。此普遍保正证明由代数给出,不依赖枚举。奇异输出是合法结果。重建 \(y'\) 的分母整除 \(m^3\),不必整除 \(m\):例如 \(m=2,x'=\beta'=1/2\) 给出 \(y'=5/8\)。所以两个方法并非同一逐项网格上的竞争规则。

## 12. 实际 xi 固定矩阵的全分辨率分类

### 输入认证与完整有限前缀

程序 `tools/scripts/agent/xi_quantization.py` 从第 6 节的 completed xi Taylor 公式自身计算 \(x,y,\beta\),不读取理论散文。Python-FLINT 0.8.0、Arb 256 位、`ctx.cap=4`;分母 \(d=10^{40}\) 的严格有理区间是 \(a/d<t<(a+1)/d\),其中:

| 量 | 下端分子 a |
|---|---:|
| x | 9991968067208526140634582694569946944348 |
| y | 9967903373716076242217823134230970513645 |
| beta | -9988664119479065813465651975246663407975 |
| gap | 18202493098329066925943959890095315 |

包围方法是对缩放 Arb 球求 `floor().unique_fmpz()`,再用 Arb 比较严格验证两个有理端点。无法认证时提高精度至最多 2048 位,仍失败则停止;不解析小数显示。程序也重新认证第 6 节全部 \(10^{18}\) 粗控制区间,结果一致。

对每一个计入完成的 \(m\),三个输入区间的两个端点都用

\[
\left\lfloor\frac{2ma+d}{2d}\right\rfloor,
\qquad\left\lfloor\frac{2mb+d}{2d}\right\rfloor
\]

作 Python 整数计算,相同才认证该 bin。不同则将该 \(m\) 记入 unresolved,不会猜测精确平局或只检查 GPU 负候选。实际运行请求并完成 \([1,1399999]\),expected、attempted、classified 均为 1399999;unresolved 为 0。每个已完成分辨率还核对 Schur 重建的整系数行列式恒等式。

| 精确方法 | 不定 | 奇异 PSD | PD | 首次 PD |
|---|---:|---:|---:|---:|
| 逐项舍入 | 298350 | 155 | 1101494 | 623 |
| Schur 舍入 | 0 | 622 | 1399377 | 623 |

逐项奇异恰为 \(m=1,\ldots,155\),Schur 奇异恰为 \(m=1,\ldots,622\)。逐项首负 \(m=156\),末负 \(m=1123639\),故分类不是从第一次 PD 起就单调。首负预测在开跑前已登记,此次枚举确认它;末负与计数是本次新测量。首负行列式为 \(-1/24336\),向量 \((156,-312,156)\) 的值为 \(-312\)。末负 bins 为 \((1122737,1120032)\),\(B=-503569\),行列式为 \(-165124853/128969711562487829\),向量 \((1123639,-2245474,1123639)\) 的值为 \(-1007138\)。首末奇异的零向量及各类首末记录都在生成报告内。

控制 \(m=200\) 仍为 bins \((200,199)\),行列式 \(-1/40000\),归一向量 \((1,-2,1)\) 的值为 \(-1/100\)。Schur 在此处给出 \(x'=1,\beta'=-1,y'=1\),是奇异 PSD。

### 真 MPS 候选与误差账

本次报告来自 Apple M3 Ultra、60 GPU 核、Metal 4、103079215104 字节内存,Python 3.12.13、Torch 2.8.0、NumPy 2.0.2。Torch 导入前设置 `PYTORCH_ENABLE_MPS_FALLBACK=0`,要求 MPS built/available,实际 tensors 位于 `mps:0`。bin 候选为 float32,索引与 \(B\) 符号运算为受支持的 int64;没有在 GPU 上用定宽整数乘行列式。先断言 \(m\le1400000<2^{24}\) 和 \(4(1400001)^2<2^{63}\),再按 65536 行分块分配。复用 `gpu5040.state_store.StateLocks`,在独立外部 state 目录先取 state 锁,再取 per-user GPU/verifier 锁;没有改动或停止既有 gpu5040 工作。

比较 naive `floor(m*t+0.5)` 与 centered-deficit `m-ceil(m*(1-t)-0.5)`。后者的 \(1-t\) 先由高精度有理数形成,再转 float32;仍然只是候选。

| MPS 候选 | 任一 x,y,beta bin 不同的 m 数 | 仅 x,y 任一不同的 m 数 | B 符号/逐项类别不同的 m 数 | Schur 类别不同 |
|---|---:|---:|---:|---:|
| naive | 131641 | 116459 | 50715 | 0 |
| centered | 61386 | 196 | 61 | 0 |

逐坐标 bin 差异为 naive `(x=64006,y=55539,beta=17380)`,centered `(x=55,y=141,beta=61201)`。beta 为负且靠近 -1,所规定的 centered 公式并没有同等改善它。精确不定而 GPU 报非负的数量为 naive 8314、centered 26;精确 PD 而 GPU 报不定分别为 42401、35。报告保留有界 bin/符号样本及完整三类混淆计数。例如 centered 在 \(m=188026\) 将精确 bins \((187875,187422)\) 算成 \((187875,187423)\),把不定报成 PD。因此即使 centered 也不能承担证书。

**历史控制保留:** caller 在派发中给出的旧 MPS smoke 于 \(m=1400000\) 得 naive \((1398876,1395507)\),而精确 bins 是 \((1398876,1395506)\)。这是旧观测,不因新跑而改写。本次当前源码重跑再次得到同一 naive 偏一结果,centered 得精确 bins;两者在这个控制上都报 PD,所以 bin 差异不一定改变类别。控制不计入有限前缀的计数或 digest。

最终主运行 UTC 为 `2026-09-08T12:14:36.796123+00:00` 至 `2026-09-08T12:14:45.828243+00:00`;两端 `torch.mps.synchronize()` 包围的分块总计 0.18041808810085058 秒,含分配/派发,不含 CPU 传输,全部枚举及比较耗时 7.707086249953136 秒。首轮实际 MPS 运行亦完整成功,最终报告是增加符号样本与混淆计数后的新运行,并非挪用旧计时。

### 解析尾界,不是数值外推

设 \(|x|\le1\),最近舍入误差满足 \(|d_x|,|d_y|\le1/(2m)\)。逐项舍入后的下抛物线余量有纸面恒等式和界

\[
g'=y+d_y-2(x+d_x)^2+1
=gap+d_y-4xd_x-2d_x^2
\ge gap-\frac5{2m}-\frac1{2m^2}.
\]

每个负项分别以上述误差界控制,两个误差项都随正整数 \(m\) 递减。取 \(M=1400000\),粗认证下端给出精确正数

\[
\frac{1820249309832}{10^{18}}-\frac5{2M}-\frac1{2M^2}
=\frac{211525460221}{6125000000000000000}>0.
\]

另由实际输入端点检查 \(L_x-1/(2M)>-1\)、\(U_x+1/(2M)<1\)、\(U_y+1/(2M)<1\)。所以每个 \(m\ge M\) 都有 \(|x'|<1,y'<1,g'>0\),由主子式得到 PD。这是普遍纸面不等式加精确端点运算,不是从有限样本外推。结合零 unresolved 的前缀,固定矩阵的每个正整数分辨率已分类;尤其逐项舍入对每个 \(m\ge1123640\) 都 PD,其中直到 \(M-1\) 的部分靠枚举,从 \(M\) 起靠尾界。

Schur 的全域 PSD 已由第 11 节代数证明。对本次实际输入,在 \(m=623\) 的端点就能严格检查 \(L_x-1/1246>-1,U_x+1/1246<1,L_\beta-1/1246>-1,U_\beta+1/1246<1\);误差继续下降,所以它对所有 \(m\ge623\) 都 PD。奇异数量 622 因而也是全分辨率的数量,不是只在扫描窗口内的猜想。

### 复现、状态与未履行义务

结构化全部证据位于 [xi-quantization-0908.md](../../reports/xi-quantization-0908.md),包括有理区间、程序及本地 import SHA256、实际 HEAD、依赖/硬件、逐块计时、范围与样本。程序仅在请求范围完整且无 unresolved 时原子发布报告;失败记录留在外部 state 目录,不能覆盖已有完整报告。CPU-only 模式明确写无 MPS 运行,不能向仓内发表 GPU 主报告。可执行入口为:

```sh
make -C tools xi-quantization XI_REPORT=/Users/auricstudio/trureturing-qgh-boundaries/docs/reports/xi-quantization-0908.md
make -C tools xi-quantization XI_MODE=cpu XI_CHUNK=50000 XI_REPORT=/tmp/qgh-xi-quantization-state/cpu-report.md
make -C tools xi-quantization-test
```

Make 配方固定 `uv run --python 3.12 --with torch==2.8.0 --with numpy==2.0.2 --with python-flint==0.8.0 python ...`,没有修改全局 Python 或 Codex 配置。主报告内记录展开后的精确命令。完整有序数学流的 SHA256 为 `81e77ccc81333be01c37c6fbb3a8168c37386f8293c18131ad45b9f7776e2b60`:对递增的每个完成 \(m\),以 ASCII 写 `m,kx,ky,kbeta,entrywise_class,schur_class` 后接 LF,无头行;类别字面值为 `indefinite`、`singular`、`pd`,控制另记。这个 digest 不含时间、设备、源码版本等运行元数据,不同设备可以复算比较。

完整 CPU-only 运行与主 MPS 运行的数学 digest 相同。另一份不导入分类实现的独立算式复核使用 512 位 Arb 比较、`divmod` 半格判定、缺额变量行列式及全部主子式,也复现同一计数和 digest,并以显式矩阵二次型核对首末负/零见证。这里的独立是算法与复算路径的独立,不是新增评审席或模型族独立性。9 个聚焦行为测试覆盖半格歧义、正负平局、奇异/不定、任意精度乘积、重建、覆盖缺口、序列化及 GPU 非负漏报;既有 ScriptTests 入口实际执行了这些测试。

本增量将“对这一固定三阶块的所有分辨率”从未执行登记变成有限完整枚举加尾界的数值库/纸面结论。它没有证明 RH,没有证明更高阶实际 xi 截面正性,没有解决全历史 Schur 误差传输、奇异 pivot 的高阶控制或统一尾估计。第 7 节其它算术桥、物理检测与 PRO 距离算子义务仍 open。caller 仍负责独立评审、PR 三门与发布;本次 worker 不把任何本地验证称为 MERGED 或 standing-goal satisfaction。

## 13. 实施收尾的追加记录

第 12 节已摄入的运行事实继续保留。随后修正报告发布失败的状态记录:即使数学覆盖已完成,发布异常也明确记为 `publication_failed` 并返回非零,保留已完成覆盖与已有报告,不把发布失败说成完整运行。新增的存储失败注入测试使聚焦行为测试总数成为 10;这不改变任何 bin、分类或数学 digest。

因此当前主报告采用终版程序的另一次完整 MPS 运行,UTC 为 `2026-09-08T12:26:31.783258+00:00` 至 `2026-09-08T12:26:40.339952+00:00`,同步 MPS 分块总计 0.162419916363433 秒,枚举/比较 7.136823707958683 秒。全部精确计数、混淆计数和 digest 与第 12 节所记运行相同。终版程序 SHA256 为 `52b0b82da67a608464b3acc189b1449e731e8c6ad4e9cef168978ca22a57908c`;本地 import `gpu5040/state_store.py` 为 `a1eda747e24ea792caac30da136e85ba0beac6dc6f08d53880624b8ac6b1f03a`,Make 入口为 `624482b96b758254c78d31c8dacfa330fd8a775d6beef6412248a17e9aed1cb9`。终版 CPU-only 完整运行也给出同一 digest,且明确没有 MPS 执行。此前的运行来源和计时只作为历史,没有拿来替代终版源码的实跑。

## 14. 评审勘误:发布边界与回归核验

本节是 `consensus-rnd:sshx` 实施修复的 repo-derived 工程证据,不追加数学定理。第 12 节“失败记录不能覆盖已有完整报告”和第 13 节“发布异常保留已有报告”的全称保证不成立,在此明确收窄:共享 `state_store.atomic_write` 先 `os.replace`,后同步目录;只有 replacement 之前的失败保留旧目标字节。quality 席在独立字节相同的夹具中注入 replacement 之后的目录同步错误,观察到非零退出、外部 `publication_failed`,同时目标已是新报告。此时新字节可以可见,掉电后的持久性不确定,没有回滚保证。该反例不表明第 13 节的历史实际 MPS 运行发生过 I/O 失败;其来源、计时和已有 atom 均继续保留。

修复后的报告 schema 为 2。`mathematical_status=complete` 只表示数学认证完成;写入 Markdown 的 `status=publication_unconfirmed` 是发布前快照,成功发布也不改写为自证成功。外部 runtime/stdout 的 `status=complete` 表示报告 writer 已返回,进程退出 0 还要求 runtime 写入返回。报告发布异常仍记 `publication_failed` 和异常类型/消息,保留覆盖、计数与完整数学 digest 并返回非零。若 runtime 记录本身也写失败,stdout 另带 `runtime_record_error` 并返回非零;此前可见的 runtime 同样不能自证自己的最终目录同步。此契约明确区分数学完成、可见字节和 I/O 结果,没有另造事务服务或改写共享 writer。

聚焦 Python 套件现为 11 项。实际共享 writer 的测试覆盖成功、replacement 前失败、replacement 后目录同步失败,以及失败/成功结果记录的目录同步失败;成功和失败两侧都核对三行合成覆盖及独立 CSV digest。尾界测试独立钉住 `error_at_M=7000001/3920000000000` 与 `gap_minus_error=211525460221/6125000000000000000`,并拒绝 `gap-error` 不严格为正、x/y/beta 严格端点达到等号或越界,及独立端点 PD 前提失败。预登记把尾界系数 5 改为 1,实得仅 `test_tail_rational_bound_and_strict_hypotheses` 失败,Python 退出 1 / Make 退出 2,无编译或导入错误;恢复后 11 项全绿。Make 的两个 `.PHONY` 和两条 help 配方合为各一条,已有 `ToolsTargets` 增列两个真实命令,保留并扩充严格 dispatch 断言。实际 `ToolsMakefileIsAThinCompleteDispatchTable` 先复现 `Assert.Single` 的两项失败;修复后该测试、根 Make 薄表、ScriptTests 入口及原有必需 check-fast filters 共 19 项通过,构建零警告、零错误;canonical selftest 通过。这些是本 worker 的执行证据,不冒充独立复审或 PR 准入。

修复终版只重跑一次实际 MPS 完整前缀,复用同一 per-user GPU/verifier 锁并使用独立外部 state;没有另做完整 CPU-only 扫描。UTC 为 `2026-09-08T13:39:56.700277+00:00` 至 `2026-09-08T13:40:04.933080+00:00`,同步 MPS 总计 0.1530874171294272 秒,枚举/比较 6.9315066249109805 秒;命令退出 0,外部 runtime 为 `complete`,无 publication/recording error。重现命令为:

```sh
make -C tools xi-quantization XI_MODE=mps XI_FIRST=1 XI_LAST=1399999 XI_CHUNK=65536 XI_PRECISION=256 XI_DIGITS=40 XI_STATE=/tmp/qgh-xi-quantization-i3-publication-contract XI_REPORT=/Users/auricstudio/trureturing-qgh-boundaries/docs/reports/xi-quantization-0908.md
```

相对 `309ff1c32e2ba45af38856c33059dbc5bbd13b55` 的报告,全部数学输入、尾界、1399999 项覆盖、精确计数、首末见证、控制和 GPU 混淆/差异记录均相同,有序 CSV digest 仍为 `81e77ccc81333be01c37c6fbb3a8168c37386f8293c18131ad45b9f7776e2b60`。变化仅为发布契约/schema、真实新运行的时刻/计时、运行路径和代码来源。报告的 `source_head` 是带未提交修复的该 HEAD,实际运行字节由 manifest 绑定:producer SHA256 `6bd7295216e998874ff2b9f47e7145f4224f0a7547e630d0157a295d10089a1d`,Make SHA256 `360891306af6257eaf4b4def814a9cd0ab73e77b452124277e8fe3ff107a63d4`,共享 writer 仍为第 13 节的 SHA256。新 Markdown 报告 SHA256 为 `cf8220d31dd7f878e0381b50527198868669ad9e485bdead5618597662817806`;旧报告留在上述提交,未把旧计时配给新代码。caller 继续负责 judge/content 分区、复制工程修复、独立复审和 PR 三门;此有界修复不宣称 MERGED、RH 进展或长期研究目标完成。

## 15. 均值与平方偏差的尖锐因数丰度上包络

**状态: PAPER_ARGUMENT / repo-derived 参考输入。** 本节落实第 10 节的距离问题,使用已完成实际 GPT PRO 的论证并由实施者逐步核对;产地见第 17 节。经典 Jensen、Hermite 插值和矩极值方法不是本线的发现。以下不是 Lean-frozen 定理,不主张新颖性或 RH 进展。GH 仍只有第 1 节的工作 RH 解释,没有另行定义。

### 固定素数标签、预算与加权度量

固定有限非空素数集 \(S\),\(k=|S|\),取 \(a_p\in\mathbb Z_{\ge0}\),允许零指数及 \(n=1\)。所有对数都是自然对数,定义

\[
n=\prod_{p\in S}p^{a_p},\quad T=\log n,\quad
x_p=(a_p+1)\log p>0,\quad
\mu=\frac1k\sum_{p\in S}x_p=\frac{T+\sum_{p\in S}\log p}{k},
\]
\[
B=e^\mu>1,\quad s_p=x_p-\mu,\quad V=\sum_{p\in S}s_p^2,\quad
E_S=\prod_{p\in S}(1-p^{-1})^{-1},\quad f(x)=\log(1-e^{-x}).
\]

\(V\) 是平方偏差之和,统计学的平均方差是 \(V/k\)。有限几何级数给出

\[
F:=\log\frac{\sigma(n)}n=\log E_S+\sum_{p\in S}f(x_p),\qquad
J:=\log E_S+kf(\mu)\ge F.
\]

零指数对应的真实局部因子为 1。这里的 \(S\) 可以比实际支撑大,不要求是连续素数前缀;必须保留准确的素数标签与 \(E_S\)。添加零指数素数虽不改变 \(F\),却改变 \(k,\mu,V,J\) 及下述包络,没有证书单调增强的结论。

本节在 \(x\) 坐标中选 Euclidean 内积。\(x=\mu\mathbf1+s\)、\(\mathbf1\cdot s=0\) 给出 \(\sum_px_p^2=k\mu^2+V\)。令 \(a_p^0=\mu/\log p-1\),则拉回指数空间得到明确的加权距离

\[
\langle u,v\rangle_w=\sum_p(\log p)^2u_pv_p,\qquad
V=\sum_p(\log p)^2(a_p-a_p^0)^2.
\]

这不同于第 10 节未经加权的原点法向投影;那个投影一般不是因数丰度的连续最优点。对两组位编码的差 \(\delta a_p=\sum_jF_j\delta b_{pj}\),同一度量拉回为

\[
\|\delta a\|_w^2=\sum_p(\log p)^2\left(\sum_jF_j\delta b_{pj}\right)^2.
\]

同一素数行的交叉项 \(2(\log p)^2F_iF_j\delta b_{pi}\delta b_{pj}\) 必须保留。中心 \(a^0\) 可以是实数,并不要求有整数位编码。关于精确 \(T\) 截面至多一个整数点及薄层才容纳多个配置,沿用第 10 节,不把编码当成新增正交方向。

### 强化的二次 Jensen 缺口

**命题。** 置 \(N_-=\sum_{s_p<0}s_p^2\),则

\[
J-F\ge\frac{BN_-}{2(B-1)^2}
\ge\frac{BV}{2k(B-1)^2}\ge\frac{V}{2kB}.
\]

**证明。** 对每个正数 \(x\),\(f(x)=-\sum_{q\ge1}e^{-qx}/q\) 绝对收敛。有限求和与级数相减合法,因为差级数的绝对值和被
\(\sum_{q\ge1}(\sum_pe^{-qx_p}+ke^{-q\mu})/q<\infty\) 控制。因此

\[
J-F=\sum_{q\ge1}\frac{\sum_pe^{-qs_p}-k}{qB^q}.
\]

每个括号由 Jensen 非负;负的 \(s_p\) 不妨碍收敛,实际衰减量是 \(e^{-qx_p}\)。对 \(s<0\),\(e^{-qs}\ge1-qs+q^2s^2/2\);对 \(s\ge0\),\(e^{-qs}\ge1-qs\)。求和消掉线性项,再用 \(\sum_{q\ge1}qB^{-q}=B/(B-1)^2\),得到第一步。

若 \(V>0\),负坐标数 \(h\) 满足 \(1\le h\le k-1\)。设 \(\ell=\sum_{s_p>0}s_p=-\sum_{s_p<0}s_p\),则正坐标平方和不超过 \(\ell^2\),而 Cauchy-Schwarz 给出 \(\ell^2\le hN_-\)。故 \(V\le(h+1)N_-\le kN_-\)。最后 \(B^2>(B-1)^2\) 给出第三步。证毕。

若 \(V=0\),全部坐标等于 \(\mu\),\(J=F\),全链取等;特别地 \(k=1\) 总如此。若 \(V>0\),存在负坐标,其指数函数二阶下界严格,所以 \(J-F\) 严格大于上述每一个二次下界。整数指数且 \(k\ge2\) 时,\(V=0\) 会要求两个不同素数的正整数幂相等,由唯一分解排除。因此包括最弱候选在内的上界

\[
\frac{\sigma(n)}n\le e^J\exp\!\left(-\frac{BV}{2k(B-1)^2}\right)
\le e^J\exp\!\left(-\frac{V}{2kB}\right)
\]

对这类整数配置严格。\(J\) 始终是上界;在固定 \(S,T\) 的实指数松弛中,只有 \(B\ge\max S\) 时等坐标点 \(a^0\) 才满足所有 \(a_p\ge0\),此时由严格凹性才可称 \(J\) 为可行连续最优值。若要求 \(a_p\ge1\),条件变为 \(B\ge(\max S)^2\)。

### Hermite 上包络及全部等号情形

**定理。** 对任意 \(k\ge2\) 个正实坐标 \(x_1,\ldots,x_k\),令 \(\mu,V\) 如上,并置

\[
r=\sqrt{\frac{V}{k(k-1)}},\quad L=\mu-r,\quad H=\mu+(k-1)r,\qquad
\Psi_k(\mu,V)=f(H)+(k-1)f(L).
\]

则 \(L>0\),且 \(\sum_if(x_i)\le\Psi_k(\mu,V)\)。这是指定 \(k,\mu,V\) 的正实坐标类中的最优上界。对整数指数因此有

\[
\frac{\sigma(n)}n\le E_S(1-e^{-H})(1-e^{-L})^{k-1}.
\]

**证明。** 正性及 \(k\ge2\) 给出 \(\sum_ix_i^2<(\sum_ix_i)^2\),所以 \(V<k(k-1)\mu^2\),即 \(r<\mu\)。又由 \(\sum_{j\ne i}(x_j-\mu)=-(x_i-\mu)\) 及 Cauchy-Schwarz,
\((x_i-\mu)^2\le(k-1)(V-(x_i-\mu)^2)\),故 \(x_i\le H\)。\(V=0\) 时全部坐标等于 \(\mu\),结论直接成立。

设 \(V>0\),则 \(0<L<H\)。取唯一次数至多二的多项式 \(P\),满足 \(P(L)=f(L),P'(L)=f'(L),P(H)=f(H)\)。直接求导得到

\[
f'(x)=\frac1{e^x-1},\quad f''(x)=-\frac{e^x}{(e^x-1)^2},\quad
f'''(x)=\frac{e^x(e^x+1)}{(e^x-1)^3}>0\quad(x>0).
\]

对任一实际坐标 \(x\notin\{L,H\}\),Hermite 余项为

\[
f(x)-P(x)=\frac{f'''(\xi)}6(x-L)^2(x-H)<0,
\]

其中 \(\xi\) 位于 \(x,L,H\) 所张成的正实区间。余项公式可直接由 Rolle 定理得到:取 \(K=(f(x)-P(x))/[(x-L)^2(x-H)]\),函数 \(f(t)-P(t)-K(t-L)^2(t-H)\) 在 \(x,L,H\) 为零,且在 \(L\) 导数为零;连续应用三次 Rolle 即得 \(f'''(\xi)=6K\)。特别地,即使 \(0<x<L\),这些点仍全在 \((0,\infty)\),平方项非负而 \(x-H<0\),符号不变。在节点上余项为零。

原向量与原型 \((H,L,\ldots,L)\) 均有 \(k\) 个坐标,一次和均为 \(k\mu\),二次和均为 \(k\mu^2+V\)(原型平方偏差为 \(((k-1)^2+k-1)r^2=V\))。二次多项式之和只依赖这三个矩,故

\[
\sum_if(x_i)\le\sum_iP(x_i)=P(H)+(k-1)P(L)=\Psi_k(\mu,V).
\]

\(V>0\) 时等号要求所有坐标属于 \(\{L,H\}\),由一次和恰有一个 \(H\)。反过来该原型确实取等,并且对每个 \(\mu>0,0\le V<k(k-1)\mu^2\) 都是可行正实向量,故上界尖锐。证毕。

\(V=0\) 的等号恰为全相等;\(k=2\) 时每个正实二元组本来就是原型的排列,总取等。不同素数的整数指数在 \(k\ge3\) 时不可能有至少两个相等的 \(L\),所以上界严格。\(k=1\) 单独定义 \(\Psi_1(\mu,0)=f(\mu)\),不使用含 \(k-1\) 的分母。这里的尖锐性只针对正实松弛,不声称在带素数标签的整数格上可达到。

令 \(\Lambda_k=kf(\mu)-\Psi_k(\mu,V)\)。将前述二次界应用于原型,得

\[
J-F\ge\Lambda_k\ge\frac{BV}{2k(B-1)^2}.
\]

固定 \(k,\mu\),在 \(V\to0\) 时对原型作 Taylor 展开,一次项相消、二次平方和为 \(V\),故
\(\Lambda_k=BV/[2(B-1)^2]+O_{k,\mu}(V^{3/2})\)。勾股分解本身不控制 \(F\);起作用的是 \(f'''\) 的符号及矩匹配。同半径的不同方向可有不同的 \(F\),本定理取其中的最大值。

## 16. 有限指数箱体与预算薄层的充分证书

**状态: 上一定理的 PAPER_ARGUMENT 推论,无新搜索实现。** 固定带准确标签的 \(S\),\(k\ge2\),每个指数限制在有限非空集合 \(A_p\subset\mathbb Z_{\ge0}\)。取有限实数 \(\log5040<T_0\le T_1\),只考虑 \(T_0\le T=\log n\le T_1\) 的配置。定义

\[
\mu_i=\frac{T_i+\sum_{p\in S}\log p}{k},\quad I=[\mu_0,\mu_1],\quad
C_p=\{(a+1)\log p:a\in A_p\},\quad
V_0=\sum_{p\in S}\operatorname{dist}(I,C_p)^2.
\]

距离是两个集合间距离的下确界,此处可取到。每个实际 \(\mu\in I,x_p\in C_p\),所以 \(|x_p-\mu|\ge\operatorname{dist}(I,C_p)\),从而 \(V\ge V_0\);不需枚举笛卡尔积。若 \(V_0\ge k(k-1)\mu_1^2\),结合 \(V<k(k-1)\mu^2\le k(k-1)\mu_1^2\) 知交集为空。否则 \(\mu_1>0\) 且 \(\mu_1-\sqrt{V_0/[k(k-1)]}>0\),才定义

\[
U=\log E_S+\Psi_k(\mu_1,V_0).
\]

在 \(\mu>0,0\le V<k(k-1)\mu^2\) 上,\(\Psi_k\) 对 \(\mu\) 严格递增,因为导数是 \(f'(H)+(k-1)f'(L)>0\);对 \(V>0\) 严格递减,因为对 \(r\) 的导数是 \((k-1)[f'(H)-f'(L)]<0\)。在 \(V=0\) 处连续。先增大 \(\mu\) 至 \(\mu_1\),再减小 \(V\) 至 \(V_0\),全程留在定义域,得 \(F\le U\)。

对 \(T>1\),Robin 的对数阈值是 \(R(T)=\gamma+\log(\log T)\),导数为 \(1/(T\log T)>0\)。因此充分条件

\[
U<\gamma+\log(\log T_0)
\]

证明箱体与薄层中每个整数满足严格 Robin 不等式。这里 \(T=\log n\),所以阈值对 \(n\) 是三层对数;\(T_0>\log5040\) 是全局预算条件。分离失败只表示未决,不是反例。\(V_0>0\) 时 \(U\) 严格小于同一薄层的 Jensen 上界 \(\log E_S+kf(\mu_1)\);这不比较其它剪枝器。

### 固定坐标的常数不能丢

若 \(S=S_{\rm fix}\sqcup S_{\rm free}\),固定指数为 \(b_p\),精确保留

\[
g_p(a)=\log\frac{1-p^{-a-1}}{1-p^{-1}},\quad
T_{\rm fix}=\sum_{p\in S_{\rm fix}}b_p\log p,\quad
F_{\rm fix}=\sum_{p\in S_{\rm fix}}g_p(b_p).
\]

令 \(h=|S_{\rm free}|\ge2\),并以残余预算端点 \(T_i-T_{\rm fix}\) 形成
\(\widetilde\mu_i=(T_i-T_{\rm fix}+\sum_{p\in S_{\rm free}}\log p)/h\)、\(\widetilde I\) 与仅在自由坐标上的 \(\widetilde V_0\)。若 \(\widetilde\mu_1\le0\),正实自由坐标不可能存在;否则同样先检查 \(\widetilde V_0<h(h-1)\widetilde\mu_1^2\),失败即交集为空。通过后完整目标的上界是

\[
F\le F_{\rm fix}+\log E_{S_{\rm free}}+
\Psi_h(\widetilde\mu_1,\widetilde V_0).
\]

仍与全局 \(\gamma+\log(\log T_0)\) 比较,绝不对可能非正的残余预算取 Robin 对数,也不删掉 \(F_{\rm fix}\)。此版本只覆盖 \(h\ge2\);\(h=0\) 直接检查唯一固定配置的总预算与 \(F_{\rm fix}\),\(h=1\) 对唯一自由行的有限允许指数直接计算总预算与 \(F_{\rm fix}+g_p(a)\)。维数下降不是无限素数尾部已受控。

## 17. 5040 证据、已有 KL 关系与未决比较

### 单个边界整数的有界复算

本次只核验 \(5040=2^4\,3^2\,5\,7\),由整数几何级数得 \(\sigma=19344\)、\(\sigma/n=403/105\)、\(E_S=35/8\)。[5040-variance-0908.md](../../reports/5040-variance-0908.md) 保存 Python-FLINT 0.8.0 / Arb 256 位的完整可执行计算与 \(10^{50}\) 分母的严格有理包围。球比较及包围端点的精确有理比较均认证

\[
\frac{403}{105}
<E_S(1-e^{-H})(1-e^{-L})^3
<e^J e^{-BV/[8(B-1)^2]}
<e^J.
\]

这些值依次约为 \(3.838095238095238\)、\(3.838655866895702\)、\(3.850047966183107\)、\(3.854387771992677\),仅作读数展示;证明依据不是解析 Arb 的显示字符串。\(\mu\) 约为 \(3.468067222945721\),\(V\) 约为 \(0.271331752493326\)。5040 不在 Robin 的 \(n>5040\) 域内,此例只展示界的收紧,没有证明 Robin 在 5040 或某个整数范围成立。

### 固定支撑损失不等于任意全局损失

第 10 节及 [Z] 第十二章的精确 Bernoulli-KL 分解是既有输入。定义
\(D_{\rm Ber}(u\Vert v)=u\log(u/v)+(1-u)\log((1-u)/(1-v))\)。这里的固定支撑同型恒等式为

\[
J-F=\frac1{1-B^{-1}}\sum_{p\in S}
D_{\rm Ber}(B^{-1}\Vert e^{-x_p}).
\]

逐项展开右边为 \(f(\mu)-f(x_p)+s_p/(B-1)\),线性项和为零。方差包络是用少量矩信息压缩这个精确损失,不增加它已有的信息;已给定全部指数时,直接 \(F\) 或精确 KL 保留更多信息。

为与 [Z] 定义 12.1、定理 12.3、推论 12.4 对齐,此处 \(F=W(n)\),\(g_p\) 取第 10 节的实指数解析延拓,并明确写

\[
\Phi(T)=\max_{\substack{u_p\in\mathbb R_{\ge0},\ u\text{ 有限支撑}\\\sum_pu_p\log p\le T}}
\sum_pg_p(u_p)\quad(T>0),\qquad
\mathfrak D(n)=\Phi(\log n)-F\quad(n>1),
\]
\[
\mathfrak Q(T)=\Phi(T)-\gamma-\log(\log T)\quad(T>1),\qquad
\Delta(n):=\gamma+\log(\log(\log n))-F
=\mathfrak D(n)-\mathfrak Q(\log n).
\]

最后一式在 \(\log n>1\) 上使用。任意 \(S\) 的 \(J\) 不一定等于 \(\Phi(T)\);正确的估计是
\(\mathfrak D(n)\ge\Phi(T)-\log E_S-\Psi_k(\mu,V)\),可与既有 \(\mathfrak D\ge0\) 取较强者。只有核对 [Z] 活跃集合及预算条件后,才能将 \(J-F\) 认作全局 \(\mathfrak D\)。

剩余全局义务仍是对**每个整数 \(n>5040\)** 证明 \(\mathfrak D(n)>\mathfrak Q(\log n)\)。本节没有在增长的支撑、指数和预算上给出足以压过 \(\mathfrak Q\) 的统一格距离估计。唯一分解排除精确等号,不提供所需的定量间隔;漏掉的素数也不能凭近似 Euler 乘积补回。

维数损失有一个仅在正实松弛中的限制:固定 \(\mu=2\),取 \(x=(k+1,1,\ldots,1)\),则 \(V=k(k-1)\),而

\[
J-F=kf(2)-f(k+1)-(k-1)f(1)=O(k),\qquad
\frac{e^2(J-F)}{V}\longrightarrow0.
\]

所以不能在所有维数的正实域上用某个正常数代替粗界中 \(1/k\) 的因子。这不是素数整数格的反例。尖锐连续包络已经达到其矩信息所能给出的最优值;RH 义务仍需额外的算术或全尺度误差信息。

### 离散对偶比较与来源边界

对于第 16 节的同一箱体,既有可分离离散 Lagrange 基线可写为

\[
U_{\rm dual}=\inf_{\lambda\ge0}
\left\{\lambda T_1+\sum_{p\in S}\max_{a\in A_p}
[g_p(a)-\lambda a\log p]\right\}.
\]

每个括号给所有预算不超过 \(T_1\) 的配置一个上界。距离证书相对这个最优对偶是否有实用优势仍 **OPEN**;比 Jensen 更紧是已经证明的较弱结论,不能升级为优于 \(U_{\rm dual}\)。caller 提供的两次后续任务 `949095a4-d3a7-4179-b842-f255db211159`、`db06ed96-26f3-47ff-90eb-db97ec4de9d6` 只有载体失败记录(`prompt_delivery_uncertain`;`page.goto Page crashed`),没有数学答案。它们既不证明也不否定优势。本增量未执行所提 GPU 窗口,不把预测当作结果,也不让新搜索依赖缺失结论。

主要研究输入是 caller 提供的实际 GPT PRO task `14803801-6a68-4b5a-8a76-f6615d838e88` 的 structured conclusion,完成时间 `2026-09-08T13:17:09.406+00:00`,返回 model `chatgpt-5.5-pro`;该输入没有单独提供 conversation id,不补造。实施 worker 没有打开 oracle transcript 或 opaque log_ref,没有新 oracle 调用。caller 的单点 256 位 Arb 读数是支持证据;本 worker 独立重算同一 5040 输入,结果一致。这里独立指证明核对和计算路径,不表示独立评审或模型族多样性;Codex 为 `repo-prior-exposed`。

文献尽调范围明确如下:实施者于 2026-09-08 读取 [Liao-Berg, Sharpening Jensen's Inequality](https://arxiv.org/abs/1707.08644) 与 [Rodin, Variance and the Inequality of Arithmetic and Geometric Means](https://arxiv.org/abs/1409.0162) 的摘要页及作者元数据。后者摘要已陈述普通乘积在同均值、方差下的一个大坐标极值形状。PRO 自报亲读前者 Theorem 1 / Corollary 1.1、后者 Theorem 1 / Remark 1,并提供前者 DOI `10.1080/00031305.2017.1419145`;本 worker 未独立取得这些正文或核对 DOI,不把转述写成亲验。PRO 另报 Pittenger 的 *Sharp mean-variance bounds for Jensen-type inequalities* 正文获取失败,其一般结果是否覆盖本特例未核实。以上不支持全球新颖性或文献穷尽声明;本节的函数特例由第 15 节完整短证承担。

本次是 `consensus-rnd:sshx` 的委派 implementation,无新增子席或独立评审判词。C17 允许的 continuation 工作树为 `/Users/auricstudio/trureturing-qgh-variance`,分支 `lane/math/quantized-gh-variance-0908`,封存起点 `0b8b5592d56d601d92db36b5f7ef331ef3ed33f1`;原 803 行前缀逐字节保留。源与报告之外仅由以下 canonical 命令生成新 atom/账目,计数由实施结果信封报告:

```sh
make ingest BASE=0b8b5592d56d601d92db36b5f7ef331ef3ed33f1 SOURCE=arithmetic-boundary-quantization
```

本轮不新建形式根或修改冻结 Lean,不重做既有有限扫描。独立复审、PR 三门和 MERGED 发布由 caller 负责,尚未交付的环节保持 open;有限追加不完成持续研究目标。

## 18. 相邻二点指数箱体:经典分数背包的精确对偶

**状态: PAPER_ARGUMENT / repo-derived 专门化,经典 LP 材料。** 本次追加日期为 2026-09-09,保留此前 1050 行。第 17 节的真实素数域比较仍 **OPEN**;这里消去价格下确界,证明三个充分条件,并给出一个仅在人工实数网格上的反向实例。GH 的未定义边界沿用第 1 节。

固定有限的不同素数标签集 \(S\),\(k=|S|\ge2\),及整数 \(b_p\ge0\),只允许
\(A_p=\{b_p,b_p+1\}\)。保留自然对数、\(g_p(a)=f((a+1)\log p)-\log(1-p^{-1})\)、\(f(x)=\log(1-e^{-x})\) 和准确的 \(E_S\)。设

\[
\log5040<T_0<T_1,\quad
\mathcal A=\{a\in\prod_p A_p:T_0\le\sum_pa_p\log p\le T_1\}.
\]

所问素数域要求 \(\mathcal A\) 至少含两个不同的**实际整数指数向量**;其素数乘积由唯一分解给出两个不同整数 \(n>5040\)。下面的 LP 归约只需 \(\mathcal A\ne\varnothing\),不以混合分布代替这个假设。记

\[
\ell_p=\log p,\quad c_p=(b_p+1)\ell_p,\quad d_p=c_p+\ell_p,
\quad \Delta_p=f(d_p)-f(c_p)>0,\quad\rho_p=\Delta_p/\ell_p,
\]
\[
T_b=\sum_pb_p\ell_p,\quad B=T_1-T_b,\quad
F_b=\sum_pg_p(b_p)=\log E_S+\sum_pf(c_p).
\]

本节 \(B\) 专指剩余预算,不是第 15 节的 \(e^\mu\)。非空性给出 \(T_b\le T_1\),故 \(B\ge0\)。第 17 节的同一个对偶精确化为

\[
U_{\rm dual}=\inf_{\lambda\ge0}Q(\lambda),\qquad
Q(\lambda)=F_b+\lambda B+\sum_p\max(0,\Delta_p-\lambda\ell_p).
\]

**命题。** 按 \(\rho_p\) 非增排序,相等时按素数大小递增固定顺序 \(p_1,\ldots,p_k\)。若 \(B\ge\sum_p\ell_p\),则
\(U_{\rm dual}=F_b+\sum_p\Delta_p\),可取 \(\lambda_*=0\)。否则令
\(q_m=\sum_{i=1}^m\ell_{p_i}\),\(q_0=0\),取唯一的 \(m\in\{0,\ldots,k-1\}\) 使 \(q_m\le B<q_{m+1}\),并置

\[
J=\{p_1,\ldots,p_m\},\quad j=p_{m+1},\quad
\theta=(B-q_m)/\ell_j\in[0,1).
\]

则有达到的原始 LP 值和对偶值

\[
\max_{\substack{0\le t_p\le1\\\sum_p\ell_pt_p\le B}}
\left(F_b+\sum_p\Delta_pt_p\right)
=U_{\rm dual}=F_b+\sum_{p\in J}\Delta_p+\theta\Delta_j.
\]

**证明及匹配证书。** 任意 LP 可行 \(t\) 与 \(\lambda\ge0\) 满足
\(F_b+\sum_p\Delta_pt_p\le Q(\lambda)\):先用预算控制 \(\lambda\sum_p\ell_pt_p\),再逐项用 \(t_p(\Delta_p-\lambda\ell_p)\le\max(0,\Delta_p-\lambda\ell_p)\)。全箱可行时取全部 \(t_p=1\) 和 \(\lambda_*=0\),两边相等。其余情形取 \(t_p=1\) 于 \(J\),\(t_j=\theta\),其它为零,预算恰好饱和。取 \(\lambda_* =\rho_j>0\),前缀的 \(\Delta_p-\lambda_*\ell_p\ge0\),后缀的该量 \(\le0\),第 \(j\) 项为零。于是每一步上界都取等,具体为

\[
Q(\lambda_*)=F_b+\sum_{p\in J}\Delta_p+
\lambda_*(B-\sum_{p\in J}\ell_p)
=F_b+\sum_{p\in J}\Delta_p+\theta\Delta_j.
\]

这同时证明最优性、无 LP 对偶间隙及下确界达到,不需要用数值相近证明相等。密度相等时上述非严格符号仍成立,固定排序给出至多一个分数坐标的最优解,不声称所有最优解都只有一个分数坐标。证毕。

\(B=0\) 时 \(J=\varnothing,\theta=0\),值为 \(F_b\);任意 \(\lambda\ge\max_p\rho_p\) 都给匹配证书。此时实际预算可行向量只有 \(b\),故不满足“至少两个”的完整问题域。\(0<B<\sum_p\ell_p\) 且 \(B=q_m\) 时仍有 \(\theta=0\),是整数最优解,不能称为真正分数解。\(B=\sum_p\ell_p\) 时全上端点恰好饱和;\(B>\sum_p\ell_p\) 时有松弛,全上端点的均值一般小于 \(\mu_1\)。

概率证书是:前缀取上端点,其余取下端点,第 \(j\) 行以概率 \(\theta\) 取上端点。\(0<\theta<1\) 时它由两个箱体配置混合而成,\(\theta=0\) 时退化为一个。任意满足期望预算的箱体分布,其上端点边际概率形成 LP 可行 \(t\);反过来任意 LP 可行 \(t\) 可用独立 Bernoulli 坐标实现。因此 LP 精确描述的是**期望预算**不超过 \(T_1\) 的混合最优值;它不要求支撑点各自在 \([T_0,T_1]\) 内,甚至不要求各自预算不超过 \(T_1\)。

**去重与文献边界。** [Z] `ZECKENDORF_EULER_5040.md` 第四十一章 **F-4:预算侧的反面见证** 已记录整数预算真最优值与价格对偶的严格差,含 \(\lambda_0=\rho(3,1)\)、预算 \(\log4\) 的例子。本节继承该区别,不新建第二个整数优化器,不称发现了该间隙。按密度排序的分数背包是经典算法;实施时读取的 [Continuous knapsack problem](https://en.wikipedia.org/wiki/Continuous_knapsack_problem) 的问题定义与算法段也给出同一归约和贪心规则。这里的匹配证书自含证明,网页仅为经典归属的有限核对,不支持文献穷尽或全球新颖性声明。

## 19. 对方差包络的三个充分占优条件

沿用第 16 节

\[
\mu_i=(T_i+\sum_p\ell_p)/k,\quad I=[\mu_0,\mu_1],\quad
\eta_p=\operatorname{dist}(I,\{c_p,d_p\}),\quad V_0=\sum_p\eta_p^2,
\]
\[
\mu=\mu_1>0,\quad 0\le V_0<k(k-1)\mu^2,\quad
U_{\rm var}=\log E_S+\Psi_k(\mu,V_0).
\]

非空性其实已保证上述定义域:取一个实际配置,其方差 \(V\ge V_0\) 且 \(V<k(k-1)\mu(a)^2\le k(k-1)\mu_1^2\)。为清楚起见仍将其写作前提。

**充分条件一:无真正分数坐标。** 第 18 节选出的最优解若为整数,则 \(U_{\rm dual}\le U_{\rm var}\)。

**证明。** 当 \(B<\sum_p\ell_p\) 且 \(\theta=0\) 时,该整数配置的预算为 \(T_1\),所以确在薄层内。全箱预算可行时,全上端点的预算至多 \(T_1\),且至少等于任一已有薄层配置的预算,因而至少为 \(T_0\),也在薄层内。两者的目标恰为 \(U_{\rm dual}\),故第 16 节直接给出结论。特别是有松弛的全箱情形,先用实际均值 \(\mu(a)\) 的第 15 节定理,再增加均值至 \(\mu_1\),最后减少方差至 \(V_0\);不可把 \(\mu(a)\) 写成 \(\mu_1\)。若预算有严格松弛,均值单调性使最终不等式严格;其余等号要求实际均值为 \(\mu_1\)、实际方差为 \(V_0\),并满足第 15 节原型的等号条件。证毕。

以下仅讨论**预算饱和**的第 18 节最优混合。令 \(X_p\in\{c_p,d_p\}\) 为其随机坐标,\(y_p=\mathbb E X_p\),则
\(\sum_py_p=T_1+\sum_p\ell_p=k\mu\)。置

\[
\overline V=\sum_p(y_p-\mu)^2<k(k-1)\mu^2.
\]

这是**均值向量的方差**,并非 \(\mathbb E\sum_p(X_p-\mu)^2\);后者在真正分数时还多出 \(\theta(1-\theta)\ell_j^2\)。

**充分条件二:\(\overline V\ge V_0\)。** 此时 \(U_{\rm dual}\le U_{\rm var}\)。

**证明。** 全部 \(y_p>0\)。逐行凹性、第 15 节及其方差单调性给出

\[
U_{\rm dual}-\log E_S=\sum_p\mathbb E f(X_p)
\le\sum_pf(y_p)\le\Psi_k(\mu,\overline V)
\le\Psi_k(\mu,V_0).
\]

均值固定为 \(\mu_1\),而两个方差都在有效定义域中;\(V_0=0\) 由连续端点涵盖。真正分数的 \(0<\theta<1\) 使第一步严格,因 \(f''<0\) 且 \(c_j<d_j\)。证毕。

**充分条件三。** 设唯一真正分数坐标为 \(j\),\(\overline V<V_0\),并且

\[
\delta=\eta_j,\qquad \delta^2\le\frac{k-1}{k}V_0.
\]

则仍有 \(U_{\rm dual}\le U_{\rm var}\)。

**证明:区间与正性。** 写 \(z=y_j\)、\(s=z-\mu\)、\(W=\sum_{p\ne j}(y_p-\mu)^2\)。其它坐标都是实际端点,且 \(\mu\in I\),所以 \(\sum_{p\ne j}\eta_p^2\le W\)。由
\(W+s^2=\overline V<V_0=\sum_{p\ne j}\eta_p^2+\delta^2\) 得到 \(\delta^2>s^2\),即 \(\delta>|s|\)。特别地 \(\delta>0\),两个端点都不在 \(I\) 中。如果二者都在 \(I\) 左边,则 \(\mu-z\ge\mu_0-d_j\ge\delta\);都在右边则 \(z-\mu\ge c_j-\mu\ge\delta\),均矛盾。因此

\[
c_j<\mu_0\le\mu<d_j,\quad
\delta=\min(\mu_0-c_j,d_j-\mu),\quad
0<c_j\le\mu-\delta<z<\mu+\delta\le d_j.
\]

左侧包含性来自 \(\mu-\delta\ge c_j+(\mu-\mu_0)\ge c_j>0\),右侧来自 \(\delta\le d_j-\mu\)。这既证明跨越整个 \(I\),也证明替代端点为正,不能只凭画图假定它们存在。

**证明:同均值替代。** 以 \(u=\mu-\delta\)、\(v=\mu+\delta\) 为新端点,令 \(Z_j\) 以概率 \(\alpha=(z-u)/(2\delta)\in(0,1)\) 取 \(v\),否则取 \(u\);其它 \(Z_p=y_p\)。令 \(h\) 为经过 \((c_j,f(c_j)),(d_j,f(d_j))\) 的仿射割线。由凹性及 \(u,v\in[c_j,d_j]\),有 \(f(u)\ge h(u),f(v)\ge h(v)\),故

\[
\mathbb E f(Z_j)\ge h(\mathbb E Z_j)=h(z)=\mathbb E f(X_j).
\]

替代保持 \(\sum_p\mathbb E Z_p=k\mu\),并有

\[
M:=\sum_p\mathbb E(Z_p-\mu)^2=W+\delta^2\ge V_0.
\]

这只是用于估计的正实混合,不要求新端点属于素数指数梯级或实际薄层。

**证明:只在有效支撑上用 Hermite 多项式。** 此情形 \(V_0>0\),置
\(r_0=\sqrt{V_0/[k(k-1)]}\)、\(L_0=\mu-r_0>0\)、\(H_0=\mu+(k-1)r_0\)。对原均值向量的零和偏差用 Cauchy-Schwarz,逐项有

\[
|y_p-\mu|^2\le\frac{k-1}{k}\overline V
<\frac{k-1}{k}V_0.
\]

故每个 \(p\ne j\) 的支撑 \(y_p<H_0\);本条件给出 \(\mu+\delta\le H_0\)。所有替代支撑均在 \((0,H_0]\) 内,包含阈值取等的端点。取第 15 节的插值多项式,明确写为

\[
P(x)=f(L_0)+f'(L_0)(x-L_0)+a(x-L_0)^2,\qquad
a=\frac{f(H_0)-f(L_0)-f'(L_0)(H_0-L_0)}{(H_0-L_0)^2}<0.
\]

严格负号来自 \(f''<0\):\(f(H_0)-f(L_0)=\int_{L_0}^{H_0}f'(t)\,dt<f'(L_0)(H_0-L_0)\)。Hermite 余项的 \(f'''>0\) 与 \((x-L_0)^2(x-H_0)\le0\) 只保证 \(0<x\le H_0\) 上 \(f(x)\le P(x)\),不把该多项式当作 \(H_0\) 以上的上包络。替代分布与原型 \((H_0,L_0,\ldots,L_0)\) 的总质量同为 \(k\)、一次矩同为 \(k\mu\),二次矩之差为 \(M-V_0\),故

\[
U_{\rm dual}-\log E_S
\le\sum_p\mathbb E f(Z_p)
\le\sum_p\mathbb E P(Z_p)
=\Psi_k(\mu,V_0)+a(M-V_0)
\le\Psi_k(\mu,V_0).
\]

证毕。各弱不等式包含 \(\delta^2=(k-1)V_0/k\) 与 \(M=V_0\)。全链等号只能在替代割线步骤取等、全部正概率支撑属于 \(\{L_0,H_0\}\)、且 \(M=V_0\) 时发生;在这里的严格薄层 \(\mu_0<\mu\) 下,\(u>c_j\) 且 \(u<d_j\),割线步骤实际严格。\(V_0=0\) 已由条件二覆盖,不使用退化的 Hermite 插值分母。

**适用域区别。** 三个充分条件的证明不使用素数性或“至少两个”配置。对任意正实二点网格 \(\{c_i,d_i\}\),\(0<c_i<d_i\),以**坐标和**薄层 \([Q_0,Q_1]\) 和预算 \(\sum_i x_i\le Q_1\) 定义 \(\mu_i=Q_i/k\)、\(I\)、\(V_0\),并假设薄层非空,相同证明成立。此时 LP 重量为 \(d_i-c_i\),剩余预算为 \(Q_1-\sum_i c_i\),目标为 \(\sum_i f(x_i)\),没有 \(\log E_S\)。算术情形的坐标和端点是 \(Q_i=T_i+\sum_p\log p\),绝不把人工坐标预算默认为素数指数预算。

## 20. 唯一分数坐标的精确剩余不等式

三个条件排除后,只余 \(0<\theta<1\)、\(\overline V<V_0\)、\(c_j<\mu_0\le\mu<d_j\) 且
\(\delta^2>(k-1)V_0/k\)。令

\[
D_j=f(z)-(1-\theta)f(c_j)-\theta f(d_j)>0,
\qquad z=(1-\theta)c_j+\theta d_j.
\]

其它坐标不随机,所以有**恒等式**

\[
U_{\rm dual}-U_{\rm var}
=\sum_pf(y_p)-\Psi_k(\mu,V_0)-D_j.
\]

因此在余域中,\(U_{\rm dual}\le U_{\rm var}\) 当且仅当
\(D_j\ge\sum_pf(y_p)-\Psi_k(\mu,V_0)\);等号也恰好对应。严格反向则精确否定该实例的占优。

**OPEN 的量词不可放宽。** 待证明或反驳的是:对每个不同素数标签集 \(S\)、每个 \(b_p\in\mathbb Z_{\ge0}\)、每对 \(\log5040<T_0<T_1\),若相邻梯级严格是 \(c_p=(b_p+1)\log p,d_p=(b_p+2)\log p\),且存在 \(a\ne a'\in\prod_p\{b_p,b_p+1\}\) 使两者都满足实际 \(T_0\le\sum_pa_p\log p\le T_1\),则上述剩余不等式是否总成立? 原有的 \(E_S\)、均值归一化、有效 \(V_0\) 域和第 18 节最优排序也全部保留。尚未证明素数对数步长和两个实际整数配置强制此式,也未取得严格违反它的真实素数箱体。这里消除了对 \(\lambda\) 的求下确界,没有消除算术义务。

## 21. 人工实数网格的反向实例与有界证据

**状态: repo-derived PAPER_ARGUMENT + 单网格 Arb 证据。** 这是一般实数几何论证的边界,不是素数指数反例,不是 Robin 证书。取三行

\[
C_1=\{99/10,101/10\},\quad C_2=C_3=\{249/25,507/50\},\quad
[Q_0,Q_1]=[29999997/10^6,30].
\]

本例预算是 \(\sum_i x_i\le30\),目标是 \(\sum_i f(x_i)\),无 \(\log E_S\) 项。于是 \(I=[9999999/10^6,10]\)、\(\mu=10\),三行距离为 \((99999,39999,39999)/10^6\),且

\[
V_0=13199640003/10^{12}=0.013199640003.
\]

下表以 0/1 表示各行下/上端点,列全 \(2^3=8\) 个状态;可行性同时检查薄层的两个闭端点。

| 状态 | 精确坐标和 | 在 \([Q_0,Q_1]\) 内 |
|---|---:|---|
| 000 | 1491/50 | 否 |
| 001 | 30 | 是 |
| 010 | 30 | 是 |
| 011 | 1509/50 | 否 |
| 100 | 1501/50 | 否 |
| 101 | 151/5 | 否 |
| 110 | 151/5 | 否 |
| 111 | 1519/50 | 否 |

两个可行配置恰为 \((99/10,249/25,507/50)\) 与 \((99/10,507/50,249/25)\),和都为 30。它们是实数配置,不是两个实际整数指数配置。

**最优对偶的解析证书。** 令 \(\lambda_*=5[f(101/10)-f(99/10)]>0\)。第 1 行的两端点价格目标之差为
\(f(d_1)-f(c_1)-\lambda_*(d_1-c_1)=0\),是代数恒等式。其它两行割线斜率严格较小:将割线写成 \(\int_0^1f'(c_i+t(d_i-c_i))\,dt\),其积分自变量相对第 1 行右移 \(3/50-t/50>0\);\(f'\) 严格递减。故第 2、3 行的价格最大值唯一在下端点取得,第 1 行两端并列。

以概率 \(1/10,9/10\) 混合 000 与 100,期望坐标和为
\((1491/50)/10+9(1501/50)/10=30\)。两个支撑预算 29.82 与 30.02 都不在薄层内,而该混合满足期望预算。令 \(\theta=9/10\);在已知最大端点上求价格对偶得

\[
\lambda_*30+\sum_{i=1}^3[f(c_i)-\lambda_*c_i]
=\sum_i f(c_i)+\lambda_*\frac9{50}
=\tfrac1{10}f(99/10)+\tfrac9{10}f(101/10)+2f(249/25)
=U_{\rm dual}.
\]

弱对偶与此匹配的原始混合共同证明最优性,不靠两个 Arb 球重叠证明相等。均值向量为 \((252/25,249/25,249/25)\),\(\overline V=6/625=0.0096<V_0\),且 \((99999/10^6)^2>2V_0/3\),确在未被三个充分条件覆盖的区域。

记 \(r=\sqrt{V_0/6}\),则 \(U_{\rm var}=\Psi_3(10,V_0)=f(10+2r)+2f(10-r)\)。[real-grid-dual-0909.md](../../reports/real-grid-dual-0909.md) 保存自含程序、完整输入、8 状态/2 可行的清单和执行身份。其 Python-FLINT 0.8.0 / Arb 256 位计算保持原给定包围,以精确有理端点和严格球比较认证下表,不是读取打印近似值作证明。

| 量 | 严格下界 | 严格上界 |
|---|---:|---:|
| \(\Psi_3(10,V_0)\) | \(-136498016563252/10^{18}\) | \(-136498016563251/10^{18}\) |
| \(U_{\rm dual}\) | \(-136497658176917/10^{18}\) | \(-136497658176916/10^{18}\) |
| \(U_{\rm dual}-\Psi_3(10,V_0)\) | \(358386335/10^{18}\) | \(358386336/10^{18}\) |

所以人工网格上 \(U_{\rm dual}>U_{\rm var}\)。正性、二点网格与两个薄层可行点不足以推出普遍占优;算术结论仍需第 20 节的素数标签和梯级约束。本例不是 prime-lattice 证据,不认证任何 Robin 整数,也不提供新 GPU 搜索方向。

**本次产地及保留义务。** 主输入是 caller 提供的实际 browser-PRO task `84963abe-485a-4093-901b-03acf69dc52e`,conversation `conv_fc5fcce44d2bc103`,载体 `company-chatgpt-pro` browser Work,实际返回模型 `GPT-6 Astra`,完成时间 `2026-09-08T15:45:56.133+00:00`。这不同于第 17 节返回 `chatgpt-5.5-pro` 的任务;此前两个失败任务保持失败,不复活。实施者在 caller 已应用的 `consensus-rnd:sshx` 下核对纸面证明和这个固定网格,为 `repo-prior-exposed`,无 sterile-prior、模型族多样性或独立评审批准声明。未打开 opaque primary log_ref 或 oracle transcript;结构化主结论是输入,不是批准票。

本次使用已隔离且清洁复用的 `/Users/auricstudio/trureturing-qgh-variance`,分支 `lane/math/quantized-gh-dual-0909`,起点 `fa198bc9a4e5da392e3f2a6f826f73f2ea672c3c`。源与报告之外,仅由 `make ingest BASE=fa198bc9a4e5da392e3f2a6f826f73f2ea672c3c SOURCE=arithmetic-boundary-quantization` 生成 atoms/消化条目,全部历史保留。没有 CPU 候选生成、GPU 工作、xi/5040 实验重跑、工具改动、Lean 重建或冻结;无无限覆盖、新颖性或 RH 进展声明。独立复审、git/PR 三门及 MERGED 落地仍由 caller 承担,未合并即 open;本次追加不完成持续目标。

## 22. 正实二点网格的二坐标全域占优与等号分类

**状态: PAPER_ARGUMENT / repo-derived 参考输入,后续结算。** 本次于 2026-09-09 追加,完整保留 I5 的 1297 行及其中历史 OPEN 陈述。这里解决第 18-20 节相邻二点问题的整个 \(k=2\) 参数族,并加强到任意正实二点坐标网格;不是把第 17 节的任意有限指数集合问题一并关闭。一般真实素数 \(k\ge3\) 比较仍 **OPEN**,第 21 节人工 \(k=3\) 反例及其原有适用范围保持有效。GH 的未定义边界沿用第 1 节。

**定理。** 取 \(C_i=\{c_i,d_i\}\subset\mathbb R\),\(0<c_i<d_i\),\(i=1,2\),以及有限实数 \(M_0<M_1\)。假设四个角点中至少两个不同的**实际角点**属于

\[
\mathcal C=\{(x_1,x_2)\in C_1\times C_2:
M_0\le x_1+x_2\le M_1\}.
\]

不同角点的坐标和允许相等,也允许不等;要求的是 \(|\mathcal C|\ge2\),不是两个满足期望预算的混合。所有对数为自然对数,定义

\[
f(x)=\log(1-e^{-x})\quad(x>0),\qquad
\mu_j=M_j/2\ (j=0,1),\quad I=[\mu_0,\mu_1],
\]
\[
\operatorname{dist}(I,C_i)=\min_{u\in I,\,x\in C_i}|u-x|,
\quad V_0=\sum_{i=1}^2\operatorname{dist}(I,C_i)^2,
\]
\[
D(M_1)=\inf_{\lambda\ge0}
\left\{\lambda M_1+\sum_{i=1}^2\max_{x\in C_i}[f(x)-\lambda x]\right\}.
\]

对 \(m>0\)、\(0\le V<2m^2\),明确使用第 15 节的归一化

\[
r=\sqrt{V/2},\qquad \Psi_2(m,V)=f(m-r)+f(m+r).
\]

这里 \(V\) 是两个坐标的平方偏差**之和**,不是平均方差。则

\[
\mu_1>0,\qquad 0\le V_0<2\mu_1^2,\qquad
D(M_1)\le\Psi_2(\mu_1,V_0),
\]
\[
D(M_1)=\Psi_2(\mu_1,V_0)
\quad\Longleftrightarrow\quad (\mu_1,\mu_1)\in C_1\times C_2.
\]

### 定义域、精确 LP 与整数最优解

**证明。** 取任一 \(x\in\mathcal C\),令 \(m=(x_1+x_2)/2\in I\)、\(V=\sum_i(x_i-m)^2\)。正性给出
\(m>0\)、\(V=2m^2-2x_1x_2<2m^2\)。集合距离给出 \(V_0\le V\),而 \(m\le\mu_1\),所以 \(\mu_1>0\) 且 \(V_0<2\mu_1^2\)。不额外假设 \(\mu_0>0\)。由 \(f'>0,f''<0\),\(\Psi_2\) 对均值严格递增、对正方差严格递减,并在 \(V=0\) 连续;这也使包含零端点的方差比较严格,与第 16 节一致。

令 \(h_i=d_i-c_i>0\)、\(\Delta_i=f(d_i)-f(c_i)>0\)、\(\rho_i=\Delta_i/h_i\)、\(R=M_1-c_1-c_2\ge0\)。第 18 节的逐项弱对偶及匹配证书,将重量 \(\ell_p\) 换成 \(h_i\),即给出

\[
D(M_1)=\max_{\substack{0\le\alpha_i\le1\\
h_1\alpha_1+h_2\alpha_2\le R}}
\sum_{i=1}^2[f(c_i)+\alpha_i\Delta_i].
\]

这里只引用其已证的分数背包机制,不另假定 LP 强对偶。\(R\ge h_1+h_2\) 时全上端点与 \(\lambda_*=0\) 匹配;\(R=0\) 时可取 \(\lambda_*\ge\max_i\rho_i\)。中间预算按 \(\rho_i\) 非增填充,真正分数行取 \(\lambda_*\) 为该行密度,整数断点可取相邻密度之间的乘子。并列时该区间可退化,任何固定排序仍给出匹配值和至多一个真正分数坐标的最优解。

现在**任选一个至多一个真正分数坐标的 LP 最优解**;后证不依赖并列时选了哪一个,也不声称所有最优解均如此。若 \(R<h_1+h_2\),每个最优解都饱和预算:否则尚有未填满的行,因 \(\Delta_i>0\) 可增加目标。若 \(R\ge h_1+h_2\),正增益使全上端点为唯一最优解,预算可能有松弛。

若所选解为角点 \(x^*\),它确在实际薄层内。预算饱和时 \(x_1^*+x_2^*=M_1>M_0\);全箱预算可行时 \(x^*=(d_1,d_2)\),其和不超过 \(M_1\),又不小于任一已有薄层角点的和,所以至少为 \(M_0\)。置

\[
m^*=(x_1^*+x_2^*)/2,\qquad V^*=\sum_{i=1}^2(x_i^*-m^*)^2.
\]

二元组本来就是 \(m^*\pm\sqrt{V^*/2}\) 的排列,故

\[
D(M_1)=\sum_i f(x_i^*)=\Psi_2(m^*,V^*)
\le\Psi_2(\mu_1,V^*)\le\Psi_2(\mu_1,V_0).
\]

第一步先增大均值,第二步用 \(V_0\le V^*\) 减小方差,全程留在正实定义域;松弛时不能把 \(m^*\) 写成 \(\mu_1\)。整数情形的等号稍后分类。

### 两个实际角点引理与均值方差情形

若所选解有唯一真正分数行,交换行标签后记该行端点为 \(c<d\),另一行固定端点为 \(t>0\),另一可选端点为 \(t'\ne t\)。记 \(\mu=\mu_1\),上端点权重为 \(\theta\in(0,1)\),则

\[
z=(1-\theta)c+\theta d=2\mu-t,\quad c<z<d,\quad
D(M_1)=(1-\theta)f(c)+\theta f(d)+f(t).
\]

**实际两角点引理。** 在上述条件下,\((c,t)\) 必须属于实际薄层,特别是 \(\mu_0\le(c+t)/2\)。

**引理证明。** 预算饱和给出 \(c+t<M_1<d+t\)。假设 \(c+t<M_0\):若 \(t'<t\),则 \(c+t'<M_0\),四角点中 \((c,t),(c,t'),(d,t)\) 均不可行,只剩 \((d,t')\) 一个可能可行;若 \(t'>t\),则 \(d+t'>M_1\),四角点中 \((c,t),(d,t),(d,t')\) 均不可行,只剩 \((c,t')\) 一个可能可行。两种次序都与 \(|\mathcal C|\ge2\) 矛盾。故 \(M_0\le c+t<M_1\),包括 \(c+t=M_0\) 的边界。此计数不依赖两个可行角点的预算是否相等。证毕。

写 \(z=\mu+s,t=\mu-s\),均值向量的平方偏差为 \(\overline V=2s^2<2\mu^2\)。若 \(\overline V\ge V_0\),真正分数行的严格凹性给出

\[
D(M_1)<f(z)+f(t)=\Psi_2(\mu,\overline V)
\le\Psi_2(\mu,V_0).
\]

这里 \(\overline V\) 不包含分数行的随机方差,不能与混合的二阶矩混同。

### 剩余情形的内侧割线与 Hermite 上包络

只余 \(2s^2<V_0\)。置 \(v=\operatorname{dist}(I,\{c,d\})\)、\(e=\operatorname{dist}(I,\{t,t'\})\)。因 \(\mu\in I\) 且 \(t\) 是实际端点,\(e\le|t-\mu|=|s|\),所以

\[
2s^2<V_0=v^2+e^2\le v^2+s^2,\qquad v>|s|.
\]

于是两个分数行端点都不在 \(I\)。它们不能同在左侧:若 \(d<\mu_0\),则 \(|s|=\mu-z>\mu-d\ge\mu_0-d\ge v\);也不能同在右侧:若 \(c>\mu\),则 \(|s|=z-\mu>c-\mu\ge v\)。故

\[
c<\mu_0\le\mu<d,\qquad v=\min(\mu_0-c,d-\mu).
\]

实际两角点引理使 \(v\le\mu_0-c\le(t-c)/2\),故 \(c\le t-2v=\mu-2v-s\),且 \(d\ge\mu+v\)。定义

\[
c'=\mu-2v-s,\qquad d'=\mu+v.
\]

由 \(z-c'=2(v+s)>0\)、\(d'-z=v-s>0\),得到所需的完整包含和正性

\[
0<c\le c'<z<d'\le d.
\]

在 \(c',d'\) 间保持同一期望 \(z\),其**上端点权重**为

\[
\theta'=\frac{z-c'}{d'-c'}=\frac{2(v+s)}{3v+s}\in(0,1).
\]

令 \(A(x)\) 为原端点 \((c,f(c)),(d,f(d))\) 的仿射割线。凹性给出 \(f(c')\ge A(c'),f(d')\ge A(d')\),因此内侧割线抬高同均值处的目标:

\[
(1-\theta)f(c)+\theta f(d)=A(z)
\le(1-\theta')f(c')+\theta'f(d').
\]

这些内点及后面的三点混合只是解析比较工具,不是新的离散状态,也不要求各自落在原实际薄层。保留固定坐标 \(t\),对函数 \(\phi\) 记加权和

\[
\mathcal M(\phi)=(1-\theta')\phi(c')+\theta'\phi(d')+\phi(t).
\]

它的总质量为 2,不是质量为 1 的三点概率分布。由于 \(c'-\mu=-2v-s,d'-\mu=v,t-\mu=-s\),直接得到

\[
(1-\theta')(-2v-s)^2+\theta'v^2=2v^2-s^2,
\]
\[
\mathcal M(1)=2,\qquad\mathcal M(x)=z+t=2\mu,\qquad
\mathcal M((x-\mu)^2)=2v^2.
\]

令 \(L=\mu-v,H=\mu+v\)。由 \(c'>0\) 及 \(L-c'=v+s>0\),有 \(L>0\);又 \(|s|<v\),所以全部比较支撑 \(c',d',t\) 均为正且不超过 \(H\)。取唯一的至多二次 Hermite 多项式

\[
P(L)=f(L),\qquad P'(L)=f'(L),\qquad P(H)=f(H).
\]

因 \(f'''(x)=e^x(e^x+1)/(e^x-1)^3>0\),第 15 节由 Rolle 推出的余项在每个非节点支撑上满足

\[
f(x)-P(x)=\frac{f'''(\xi)}6(x-L)^2(x-H)\le0,
\]

其中 \(\xi\) 在 \(x,L,H\) 张成的正实区间内;节点上余项为零。即使 \(c'<L\) 也有正确的上界符号,但没有在 \(H\) 以上使用它。\(\mathcal M\) 与两个单位质量节点 \(L,H\) 的总质量、一次矩及中心二次矩完全相同,故

\[
D(M_1)\le\mathcal M(f)\le\mathcal M(P)
=P(L)+P(H)=\Psi_2(\mu,2v^2).
\]

最后 \(L>0\) 给出 \(v<\mu\),而前面的距离估计给出

\[
V_0\le v^2+s^2<2v^2<2\mu^2.
\]

由方差严格单调性,\(D(M_1)\le\Psi_2(\mu,2v^2)<\Psi_2(\mu,V_0)\)。这完成全部真正分数情形的严格占优,不需要第三个充分条件的额外距离比例假设。

### 等号恰为上预算的等坐标角点

真正分数的所选最优解已经严格。整数情形若 \(m^*<\mu_1\),均值严格单调性也使不等式严格。若 \(m^*=\mu_1\) 而两坐标不等,选较小坐标 \(x_i^*<\mu_1\)。严格薄层宽度 \(\mu_0<\mu_1\) 给出

\[
\operatorname{dist}(I,C_i)\le\operatorname{dist}(I,\{x_i^*\})
=\max(\mu_0-x_i^*,0)<\mu_1-x_i^*.
\]

另一坐标的距离至多是其偏差绝对值,所以 \(V_0<V^*\),方差比较仍严格。因此等号要求所选整数最优角点为 \((\mu_1,\mu_1)\)。

反过来,若该角点存在,它的和为 \(M_1\),确在薄层中,并有 \(V_0=0\)。对任意 LP 可行混合,逐行及二元 Jensen 给出
\(\sum_i\mathbb E f(X_i)\le2f((\mathbb E X_1+\mathbb E X_2)/2)\le2f(\mu_1)\),该角点取得此值。还可直接匹配价格端:取 \(\lambda=f'(\mu_1)>0\),凹函数的支撑切线给出
\(f(x)-\lambda x\le f(\mu_1)-\lambda\mu_1\),每行因含 \(\mu_1\) 而取到最大值。于是该价格值为 \(2f(\mu_1)\),与角点的弱对偶下界匹配,故 \(D(M_1)=2f(\mu_1)=\Psi_2(\mu_1,0)\)。等号分类不依赖未证明的强对偶。证毕。

## 23. 两个不同素数的严格专门化与本次来源边界

**推论。** 在第 18 节完整素数域中取 \(S=\{p,q\}\),\(p\ne q\) 为素数,\(b_p,b_q\in\mathbb Z_{\ge0}\),\(A_i=\{b_i,b_i+1\}\)。保留有限的 \(\log5040<T_0<T_1\),并要求至少两个不同的实际指数配置满足 \(T_0\le a_p\log p+a_q\log q\le T_1\)。则同一箱体和薄层的最优离散可分离对偶满足

\[
U_{\rm dual}<U_{\rm var}.
\]

**证明:预算与常数的精确平移。** 对 \(i\in\{p,q\}\) 置

\[
\ell_i=\log i,\quad x_i=(a_i+1)\ell_i,\quad
c_i=(b_i+1)\ell_i>0,\quad d_i=(b_i+2)\ell_i>c_i,
\]
\[
M_j=T_j+\ell_p+\ell_q\quad(j=0,1),\qquad
E_S=(1-p^{-1})^{-1}(1-q^{-1})^{-1}.
\]

因 \(a_p\ell_p+a_q\ell_q=x_p+x_q-\ell_p-\ell_q\),指数薄层与 \(M_0\le x_p+x_q\le M_1\) 的实际角点一一对应;两个实际配置和严格宽度都保留。\(\mu_j=M_j/2\)、\(I\)、\(V_0\) 恰是第 16/19 节原来的量,没有另换度量或方差归一化。又 \(g_i(a)=f((a+1)\ell_i)-\log(1-i^{-1})\),对每个 \(\lambda\ge0\) 都逐项精确有

\[
\lambda T_1+\sum_{i\in S}\max_{a\in A_i}[g_i(a)-\lambda a\ell_i]
=\log E_S+\lambda M_1+\sum_{i\in S}\max_{x\in C_i}[f(x)-\lambda x].
\]

取下确界得到

\[
U_{\rm dual}=\log E_S+D(M_1),\qquad
U_{\rm var}=\log E_S+\Psi_2(\mu_1,V_0).
\]

第 22 节给出弱占优,等号则要求某个允许指数对满足

\[
(a_p+1)\log p=(a_q+1)\log q=\mu_1,
\qquad p^{a_p+1}=q^{a_q+1}.
\]

两个幂指数都是正整数,与不同素数的唯一分解矛盾,所以严格。允许相邻指数选择包含零,因为 \(a_i+1\ge1\)、\(x_i>0\),且 \(g_i(0)=0\) 无需例外。假设 \(T_0>\log5040\) 完整继承,其具体数值不是这条比较所需的额外条件。证明只用两个不同配置确实落在薄层内,不要求它们预算相等;一般实数定理允许等预算角点。证毕。

**本次来源与核验限度。** 主输入是 caller 提供的已完成 browser-PRO structured conclusion:task `6f6085dc-6f5a-473f-a229-072469c98c75`,conversation `conv_fc5fcce44d2bc103`,载体 `company-chatgpt-pro` browser Work,实际返回模型 `GPT-6 Astra`,完成时间 `2026-09-08T16:20:22.227+00:00`,opaque primary log_ref `qgh0909:k2-dominance:14c8e7b2`。这些是该次调用的来源记录,不是新的模型调用或独立批准票;该 opaque 引用及原始对话均未打开。主输入自报 `external-prior-exposed; sterile-context-unverified`。实施者是 caller 已应用的 `consensus-rnd:sshx` 下的委派 Codex implementation,为 `repo-prior-exposed`,没有新面板、子席、独立模型或 sterile-prior 声明。I5 的源和报告作为实施输入读取,不充作独立评审证据;caller 已有核对也只作支持。

本次纸面审核展开了实际角点计数、内点正性、上端权重、质量为 2 的矩匹配、Hermite 余项符号及等号的双向证明,并将整数情形统一记为 \(m^*,V^*\)。经典分数背包归属沿用第 18 节;实施时还读取 [Hermite interpolation](https://en.wikipedia.org/wiki/Hermite_interpolation) 的摘要接口,仅核对以函数值和导数值插值的经典方法归属,没有从摘要取得本定理。所需余项的自含 Rolle 证明已在第 15 节。本次是具体函数与网格条件下的仓内纸面推导,不主张文献穷尽、全球新颖性、RH 进展或 Lean 冻结。

工作树仍为 `/Users/auricstudio/trureturing-qgh-variance`,分支 `lane/math/quantized-gh-dual-0909`。本次唯一摄入基线是已终态提交的 I5 `ba80db594e632ae67aad496a3d68bab506769478`;其完整前缀为 1297 行、81750 字节、SHA256 `c112c2a0f0aa190845d05e80b67ad36e784aa894730c3b4d0e5ec017277713d0`。除追加本卷,新 atom 与消化条目只通过以下 canonical 命令生成,所有历史 atoms/条目保留:

```sh
make ingest BASE=ba80db594e632ae67aad496a3d68bab506769478 SOURCE=arithmetic-boundary-quantization
```

本次无 CPU/GPU 候选搜索,不重跑 xi、5040 或人工网格实验,不修改既有报告、数值证据、工具、测试套件、其它理论、形式根或冻结状态。一般真实素数 \(k\ge3\) 仍 **OPEN**;未将另行进行的 primary follow-up 结论纳入本增量。反驳本结算须在完整二点域内给出 \(D>\Psi_2\),或在无等坐标角点时给出等号;真实二素数域中经精确匹配证书认证的 \(U_{\rm dual}\ge U_{\rm var}\) 也会反驳严格推论,只有一个实际薄层角点的例子不在定理域内。

这关闭的是一个二坐标参数族的纸面比较,不产生新的 Robin 有限证书或无限整数覆盖,也不完成长期研究目标。I5/I6 组合源的独立复审、CI 三门和 PR MERGED 落地仍由 caller 承担;本次实施不声明这些义务已履行,也不为已解决的二素数比较安排 GPU 搜索。

## 24. 实际下端角点可行时的全维条件占优

**24.1 状态与精确问题域。** 本节是 2026-09-09 的 S12 后续结算,状态为 **PAPER_ARGUMENT / repo-derived 参考输入**。沿用第 15-23 节的函数、平方偏差之和及预算约定。第 22-23 节的二坐标全域结算、第 21 节的人工实数网格反例和所有历史记录保持有效;一般真实素数 \(k\ge3\) 的无条件比较仍 **OPEN**。GH 仍只有第 1 节的工作 RH 解释,不另造 GH 定义,不主张 RH 进展、全球新颖性或 Lean 冻结。

取整数 \(k\ge2\),每行恰为正实二点网格

\[
C_i=\{c_i,d_i\},\qquad 0<c_i<d_i<\infty\quad(1\le i\le k),
\qquad -\infty<M_0<M_1<\infty.
\]

要求至少两个不同的**实际角点**属于闭端点、严格正宽度的薄层

\[
\mathcal C=\left\{x\in\prod_{i=1}^k C_i:
M_0\le\sum_i x_i\le M_1\right\},\qquad |\mathcal C|\ge2.
\]

不同角点的坐标和可以相等,不能用两个混合分布或两个满足期望预算的点替代这个计数要求。所有对数为自然对数,定义

\[
f(x)=\log(1-e^{-x})\quad(x>0),\qquad
\mu_0=M_0/k,\quad \mu=M_1/k,\quad I=[\mu_0,\mu],
\]
\[
\eta_i=\operatorname{dist}(I,C_i)
=\min_{u\in I,\,x\in C_i}|u-x|,\qquad V_0=\sum_i\eta_i^2,
\]
\[
D(M_1)=\inf_{\lambda\ge0}\left\{\lambda M_1+
\sum_i\max_{x\in C_i}[f(x)-\lambda x]\right\}.
\]

对 \(m>0,0\le V<k(k-1)m^2\),始终使用

\[
r=\sqrt{\frac{V}{k(k-1)}},\qquad
\Psi_k(m,V)=f(m+(k-1)r)+(k-1)f(m-r).
\]

这里 \(V\) 不是平均方差 \(V/k\);\(M_i\) 是坐标和预算,不是未平移的素数指数预算。

**24.2 条件定理与存在量词。** 在 24.1 的完整域中,进一步假设:**存在某个最优且真正分数的基本解,它对应的实际下端角点属于 \(\mathcal C\)**。更明确地,24.4 的 LP 有一个最优基本解,唯一真正分数行为 \(j\),其上端点权重 \(\theta\in(0,1)\),其它行固定在实际端点 \(t_i\in C_i\)。该解预算饱和,写成

\[
z=(1-\theta)c_j+\theta d_j=\mu+s\in(c_j,d_j),
\qquad z+\sum_{i\ne j}t_i=k\mu,
\]
\[
x^-=(c_j,t_{-j}),\qquad M_0\le\sum_i x_i^-<M_1.
\]

则

\[
\mu>0,\qquad 0\le V_0<k(k-1)\mu^2,\qquad
\boxed{D(M_1)<\Psi_k(\mu,V_0)}.
\]

只需能选到**一个**满足附加条件的最优基本解,不要求每个最优解或每个最优基本解都满足,也不要求预先固定的并列排序恰好选到它。对 \(k\ge3\),不从 \(|\mathcal C|\ge2\) 推出这项附加条件。在真正分数分支中,\(x^-\in\mathcal C\) 本身已保证非空;下述证明不再另用两个角点的计数,但定理保留原问题的完整计数假设。

### 定义域、基本解与未使用分数假设的边界

**24.3 正定义域与单调性。** 取任一实际 \(x\in\mathcal C\),令 \(m=\sum_i x_i/k\in I\)、\(V(x)=\sum_i(x_i-m)^2\)。正坐标且 \(k\ge2\) 给出

\[
0\le V_0\le V(x)=\sum_i x_i^2-km^2
<(\sum_i x_i)^2-km^2=k(k-1)m^2\le k(k-1)\mu^2.
\]

故 \(\mu\ge m>0\),不额外要求 \(\mu_0>0\)。第 15 节的包络以及第 16 节的均值严格递增、方差严格递减性均在这个正定义域内使用。方差比较包括零端点:在正方差区间严格递减并于零连续,所以 \(0\le V_a<V_b<k(k-1)m^2\) 仍给出 \(\Psi_k(m,V_b)<\Psi_k(m,V_a)\)。

**24.4 精确 LP、并列与期望预算。** 置 \(h_i=d_i-c_i>0\)、\(\Delta_i=f(d_i)-f(c_i)>0\)、\(\rho_i=\Delta_i/h_i>0\)、\(R=M_1-\sum_i c_i\ge0\)。按第 18 节已证的逐项弱对偶与匹配乘子机制,有达到的精确值

\[
D(M_1)=\max_{\substack{0\le\alpha_i\le1\\\sum_i h_i\alpha_i\le R}}
\sum_i[f(c_i)+\alpha_i\Delta_i].
\]

可行域非空且紧,故存在最优基本解。基本解至多一行真正分数:若两行都严格处于 \((0,1)\),沿保持 \(\sum_i h_i\alpha_i\) 的非零双向微扰仍可行,该点便不是极点。若预算未饱和而存在分数行,单行双向小扰动也排除极点;更强地,由于每个 \(\Delta_i>0\),任何有预算松弛且未全满的点都不是最优。因而真正分数的最优解必预算饱和,而 \(R\ge\sum_i h_i\) 时全上端点是唯一最优解。

按 \(\rho_i\) 非增填充、并列时任意固定排序,给出至多一行分数的匹配证书。对定理选出的其它最优分数基本解也可直接匹配:预算中性的两行交换说明,每个已满行满足 \(\rho_i\ge\rho_j\),每个空行满足 \(\rho_i\le\rho_j\),否则向密度更高行转移一小份预算会严格增加目标。因此 \(\lambda_* =\rho_j>0\) 使逐行价格最大值与该解匹配,精确达到 \(D(M_1)\)。密度并列不破坏这些非严格符号;并列的非基本最优解可能有多行分数,不把它们强行写成唯一分数行。

该 LP 的约束是**期望**坐标和不超过 \(M_1\),没有施加下预算 \(M_0\)。在定理的真正分数解中,实际两支撑角点满足

\[
M^-:=\sum_i x_i^-=M_1-\theta h_j<M_1,
\qquad M^+:=d_j+\sum_{i\ne j}t_i=M_1+(1-\theta)h_j>M_1.
\]

附加条件只使下角点 \(M^-\ge M_0\);上角点依然违反实际上预算。不能把期望可行说成整个支撑逐点可行。\(R=0\) 时唯一可行角点为全下端点,与至少两个实际薄层角点不相容,仍有 \(\lambda_*\ge\max_i\rho_i\) 的退化匹配证书。

**24.5 整数最优解与 inactive budget 分列。** 若选择到整数最优基本解 \(x^*\),预算饱和时它的和为 \(M_1\),故确在薄层内。若预算覆盖全箱,正增益使 \(x^*=(d_1,\ldots,d_k)\) 唯一最优,它的和不超过 \(M_1\),又不小于任一已有薄层角点的和,故也至少为 \(M_0\)。令 \(m^*=\sum_i x_i^*/k\)、\(V_{\rm int}=\sum_i(x_i^*-m^*)^2\),则

\[
D(M_1)=\sum_i f(x_i^*)\le\Psi_k(m^*,V_{\rm int})
\le\Psi_k(\mu,V_{\rm int})\le\Psi_k(\mu,V_0).
\]

这一路先增均值、再减方差,由实际角点保证 \(V_0\le V_{\rm int}\),全程正定义域有效,无需附加下角点假设。若 \(M_1>\sum_i d_i\),预算严格不活跃,取 \(\lambda_*=0\),且 \(m^*<\mu\) 使最终比较严格;不存在真正分数的最优解。\(M_1=\sum_i d_i\) 时仍取 \(\lambda_*=0\),但预算饱和,不称为严格松弛。

饱和的整数分支若不全等,存在 \(x_i^*<\mu\)。严格宽度 \(\mu_0<\mu\) 使
\(\eta_i\le\max(\mu_0-x_i^*,0)<\mu-x_i^*\),其它行 \(\eta_l\le|x_l^*-\mu|\),从而 \(V_0<V_{\rm int}\),比较仍严格。只有全等角点 \(x^*=\mu\mathbf1\) 可以取等:此时 \(V_0=0\),任意 LP 混合的逐行 Jensen 与总均值 Jensen 给出目标至多 \(kf(\mu)\),该角点达到它。这是整数分支的边界说明,不能把整数解称为满足 24.2 的真正分数解。

### Hermite 工具与真正分数分支

**24.6 有限支撑上的二次上界。** 对参考矩 \(0<V<k(k-1)\mu^2\),令 \(L=\mu-\sqrt{V/[k(k-1)]}>0\)、\(H=\mu+\sqrt{(k-1)V/k}>L\)。取

\[
P(x)=f(L)+f'(L)(x-L)+a(x-L)^2,\qquad
a=\frac{f(H)-f(L)-f'(L)(H-L)}{(H-L)^2}<0.
\]

负号由 \(f''<0\) 得到。第 15 节的 Rolle/Hermite 余项及 \(f'''(x)>0\) 给出

\[
f(x)-P(x)=\frac{f'''(\xi)}6(x-L)^2(x-H)\le0
\qquad(0<x\le H),
\]

节点上差为零,其余点的 \(\xi\) 位于 \(x,L,H\) 张成的正实区间内。特别是 \(0<x<L\) 仍合法;不在 \(x>H\) 使用这个上界。

若 \(\mathcal M\) 是正支撑不超过 \(H\) 的有限非负加权和,满足 \(\mathcal M(1)=k\)、\(\mathcal M(x)=k\mu\)、\(\mathcal M((x-\mu)^2)=V_{\mathcal M}\),则与原型 \((H,L,\ldots,L)\) 比较得到

\[
\mathcal M(f)\le\mathcal M(P)
=\Psi_k(\mu,V)+a(V_{\mathcal M}-V).
\]

因此 \(V_{\mathcal M}\ge V\) 时,因 \(a<0\),右边**不超过** \(\Psi_k(\mu,V)\)。质量是 \(k\),不是 1;不能把有多个加权支撑的对象未经矩核对直接当成 \(k\) 个实际坐标。此式只需参考矩 \(V\) 的正定义域,没有对 \(\Psi_k(\mu,V_{\mathcal M})\) 作求值要求。

**24.7 均值向量已满足方差下界。** 以下固定 24.2 存在的那个最优解,写 \(c=c_j,d=d_j\),并置

\[
y_j=z=\mu+s,\quad y_i=t_i\ (i\ne j),\qquad
W=\sum_{i\ne j}(t_i-\mu)^2,\quad
\overline V=\sum_i(y_i-\mu)^2=s^2+W.
\]

所有 \(y_i>0\),均值为 \(\mu\),故 \(\overline V<k(k-1)\mu^2\)。这是均值向量的平方偏差,不是原混合的中心二阶矩;后者为 \(\overline V+\theta(1-\theta)h_j^2\)。若 \(\overline V\ge V_0\),真正分数行的严格凹性与第 15 节给出

\[
D(M_1)=(1-\theta)f(c)+\theta f(d)+\sum_{i\ne j}f(t_i)
<\sum_i f(y_i)\le\Psi_k(\mu,\overline V)\le\Psi_k(\mu,V_0).
\]

这包括 \(\overline V=V_0\)、\(V_0=0\) 及 \(\overline V=V_0=0\)。严格性来自 \(c<d\)、\(0<\theta<1\),无需非零方差,也不使用退化的 Hermite 插值或除以零距离。

**24.8 剩余域中的实际下角点约束与内点正性。** 只余 \(\overline V<V_0\),令 \(v=\eta_j\)。其它行都是实际端点且 \(\mu\in I\),故

\[
s^2+W<V_0=v^2+\sum_{i\ne j}\eta_i^2\le v^2+W,
\qquad v>|s|\ge0.
\]

于是 \(c,d\) 都不在 \(I\)。若 \(d<\mu_0\),则 \(\mu-z>\mu-d\ge\mu_0-d=v\);若 \(c>\mu\),则 \(z-\mu>c-\mu=v\),都矛盾。因此

\[
c<\mu_0<\mu<d,\qquad v=\min(\mu_0-c,d-\mu)>0.
\]

实际下角点的下预算给出 \(k\mu_0\le c+\sum_{i\ne j}t_i=k\mu+c-z\),从而

\[
kv\le k(\mu_0-c)\le(k-1)(\mu-c)-s.
\]

令 \(n=k-1\ge1\),以及

\[
A=\frac{kv+s}{n},\qquad c'=\mu-A,\qquad d'=\mu+v.
\]

上述不等式给出 \(c'\ge c>0\),而 \(d'\le d\)。又

\[
z-c'=\frac{k(v+s)}{n}>0,\quad d'-z=v-s>0,
\quad (\mu-v)-c'=\frac{v+s}{n}>0.
\]

因此完整支撑关系为

\[
0<c\le c'<\mu-v<z<\mu+v=d'\le d.
\]

令 \(q\) 为原 \((c,f(c)),(d,f(d))\) 的仿射割线。凹性保证任意收缩到内部子区间且保持均值 \(z\) 的混合,其目标至少为 \(q(z)\)。收缩到对称点 \(\mu-v,\mu+v\) 时严格提高:左端 \(\mu-v\in(c,d)\),\(f(\mu-v)>q(\mu-v)\),且其权重 \((v-s)/(2v)>0\)。收缩到 \(c',d'\) 只需弱提高即可。所有这些点均是**解析上界工具**,不宣称属于原二点网格或构成新的实际可行配置。

**24.9 非集中距离域。** 若 \(v^2\le(k-1)V_0/k\),在分数行用对称支撑 \(\mu-v,\mu+v\),上端点权重 \(\alpha=(v+s)/(2v)\in(0,1)\),其它行保留原 \(t_i\)。对应加权和 \(\mathcal M_0\) 满足

\[
D(M_1)<\mathcal M_0(f),\qquad
\mathcal M_0(1)=k,\quad \mathcal M_0(x)=k\mu,\quad
\mathcal M_0((x-\mu)^2)=W+v^2\ge V_0.
\]

此域 \(V_0>0\),令 \(L_0=\mu-\sqrt{V_0/[k(k-1)]}>0\)、\(H_0=\mu+\sqrt{(k-1)V_0/k}\)。对原均值向量的零和偏差作 Cauchy-Schwarz,逐项得到

\[
|y_i-\mu|^2\le\frac{k-1}{k}\overline V
<\frac{k-1}{k}V_0.
\]

故每个固定支撑 \(t_i<H_0\),而 \(\mu+v\le H_0\);正性已由 24.8 保证。用 24.6 在参考矩 \(V_0\) 的多项式 \(P_0\) 及其 \(a_0<0\),得到

\[
D(M_1)<\mathcal M_0(f)\le\mathcal M_0(P_0)
=\Psi_k(\mu,V_0)+a_0(W+v^2-V_0)\le\Psi_k(\mu,V_0).
\]

阈值 \(v^2=(k-1)V_0/k\)、矩相等 \(W+v^2=V_0\) 及高节点上的支撑均包括在内;第一步的严格割线提升不消失。

### 集中距离域的两个完整证明与矩公式勘正

**24.10 先平均固定行并保持原来的 \(V_0\)。** 现在设 \(v^2>(k-1)V_0/k\)。因为 \(\sum_{i\ne j}(t_i-\mu)=-s\),固定行的算术平均为

\[
t=\frac1n\sum_{i\ne j}t_i=\mu-\frac{s}{n}>0,
\qquad \sum_{i\ne j}f(t_i)\le n f(t).
\]

严格凹性使等号恰在原固定行全相等时成立;\(n=1\) 时这一步恒等。再将分数行收缩到 \(c',d'\),保持其均值 \(z\)。新上端点权重精确为

\[
\theta'=\frac{A+s}{A+v}
=\frac{k(v+s)}{(2k-1)v+s}\in(0,1).
\]

分母正,且 \(1-\theta'=(v-s)/(A+v)>0\)。两步都给目标的合法上界:

\[
D(M_1)\le(1-\theta')f(c')+\theta'f(d')+n f(t)=:\mathcal M_*(f).
\]

平均后的 \(t\) 与内侧端点是解析替代点,不是原离散配置。**\(V_0\) 从始至终仍是原 \(I,C_1,\ldots,C_k\) 的距离平方和**,不对平均行重建网格,不重算或换掉距离证书。

**24.11 被拒绝的 caller 矩公式及正确方向。** 本任务早先 caller prompt 提出的行矩

\[
\frac{kv^2+2vs-(k-2)s^2}{k-1}
\]

是错误公式,已在任何源实施之前被主数学论证拒绝;它不是本卷已合入定理的撤回。正确的中心二阶矩由均值为 \(s\) 的两支撑 \(-A,v\) 直接算出:

\[
(1-\theta')A^2+\theta'v^2
=Av+s(v-A)
=\frac{kv^2-s^2}{k-1}.
\]

两个候选表达式之差为 \([2vs-(k-3)s^2]/(k-1)\),不是恒等于零;不能沿用被拒绝公式的符号担忧。平均固定行的中心二阶矩为 \(n(t-\mu)^2=s^2/n\),所以

\[
\mathcal M_*(1)=k,\qquad \mathcal M_*(x)=z+nt=k\mu,
\qquad \mathcal M_*((x-\mu)^2)=\frac{kv^2}{k-1}=:V_*.
\]

若保留原固定行,正确的总矩则是

\[
V_{\rm new}=\frac{kv^2}{k-1}+W-\frac{s^2}{k-1}
=V_*+W-\frac{s^2}{k-1}\ge V_*.
\]

最后一步是 Cauchy-Schwarz:
\(s^2=(\sum_{i\ne j}(t_i-\mu))^2\le(k-1)W\)。因此在相同总质量、一次矩下,24.6 的**负二次系数**乘上 \(V_{\rm new}-V_*\ge0\) 给非正修正项,方向正好有利于所需上界,不需要错误地把 \(V_{\rm new}\) 估成不大于 \(V_*\)。

**24.12 平均路线的精确矩匹配与严格性。** 对 \(V_*\) 置

\[
L=\mu-\frac{v}{k-1},\qquad H=\mu+v=d'.
\]

由 \(v>|s|\)、\(n\ge1\) 和 \(c'>0\),逐项有

\[
L-c'=v+\frac{s}{n}>0,\qquad
t-L=\frac{v-s}{n}>0,\qquad H-t=v+\frac{s}{n}>0.
\]

故 \(0<c'<L<t<H=d'\),所有替代支撑均在 \((0,H]\)。\(L>0\) 同时给出 \(v<(k-1)\mu\),所以

\[
V_0<V_*<k(k-1)\mu^2.
\]

第一步来自本域的集中条件,第二步确保包络正定义域。\(\mathcal M_*\) 与原型 \((H,L,\ldots,L)\) 的总质量、一次矩、中心二阶矩完全相同。用 24.6 的 Hermite 多项式得到

\[
D(M_1)\le\mathcal M_*(f)\le\mathcal M_*(P)
=f(H)+(k-1)f(L)=\Psi_k(\mu,V_*)
<\Psi_k(\mu,V_0).
\]

最后一步的严格性来自 \(V_*>V_0\),不依赖平均或内侧割线步骤是否取等。Hermite 在 \(c'<L\) 处仍有正确符号,并未跨过高节点使用上界。这完成集中域的第一条证明。

**24.13 不平均固定行的直接证明。** 同在集中域,令

\[
\mathcal M_{\rm dir}(\phi)=(1-\theta')\phi(c')+\theta'\phi(d')+
\sum_{i\ne j}\phi(t_i).
\]

内侧割线给出 \(D(M_1)\le\mathcal M_{\rm dir}(f)\),总质量和一次矩仍为 \(k,k\mu\),中心二阶矩恰为 24.11 的 \(V_{\rm new}\)。由 24.9 对原均值向量的坐标界和本域条件,

\[
0<t_i\le\mu+\sqrt{\frac{k-1}{k}\overline V}
<\mu+\sqrt{\frac{k-1}{k}V_0}<\mu+v=H.
\]

加上 \(0<c'<H\)、\(d'=H\),全部支撑仍在 Hermite 的有效范围。保持 24.12 的 \(L,H,V_*\),用正确的 \(V_{\rm new}\ge V_*\) 及 \(a<0\) 得到

\[
D(M_1)\le\mathcal M_{\rm dir}(f)\le\mathcal M_{\rm dir}(P)
=\Psi_k(\mu,V_*)+a\left(W-\frac{s^2}{k-1}\right)
\le\Psi_k(\mu,V_*)<\Psi_k(\mu,V_0).
\]

这是保留原固定行的第二条完整路线,不是把平均证明的矩等式误用于未平均的行。\(W=s^2/(k-1)\) 的边界允许,最后的方差严格比较仍在。24.7、24.9、24.12 或 24.13 穷尽真正分数分支;零方差与整数、inactive budget 已分别处理。24.2 的条件定理证毕。

### 素数平移、尚余区域与来源

**24.14 精确的素数下角点条件。** 取第 18 节完整素数域:有限不同素数标签集 \(S=\{p_1,\ldots,p_k\}\)、\(k\ge2\)、\(b_i\in\mathbb Z_{\ge0}\)、\(A_{p_i}=\{b_i,b_i+1\}\)、有限 \(\log5040<T_0<T_1\),且至少两个不同的实际允许指数向量落在 \([T_0,T_1]\) 内。令

\[
\ell_i=\log p_i,\quad c_i=(b_i+1)\ell_i,\quad d_i=(b_i+2)\ell_i,
\quad M_q=T_q+\sum_i\ell_i\quad(q=0,1).
\]

实际角点与指数向量一一对应,\(M_1-M_0=T_1-T_0\)。\(\mu_0,\mu,I,V_0\) 恰为第 16/19 节原来的量。零指数仍允许,因为 \(c_i\ge\log p_i>0\),\(g_{p_i}(0)=0\)。保留 \(E_S=\prod_{p\in S}(1-p^{-1})^{-1}\),对每个 \(\lambda\ge0\) 精确有

\[
\lambda T_1+\sum_i\max_{a\in A_{p_i}}[g_{p_i}(a)-\lambda a\ell_i]
=\log E_S+\lambda M_1+\sum_i\max_{x\in C_i}[f(x)-\lambda x],
\]
\[
U_{\rm dual}=\log E_S+D(M_1),\qquad
U_{\rm var}=\log E_S+\Psi_k(\mu,V_0).
\]

对某个最优真正分数基本解,记分数行 \(j\) 的权重为 \(\theta_j\in(0,1)\)。其实际下角点预算为

\[
M^-=M_1-\theta_j\ell_j,
\qquad T^-=T_1-\theta_j\log p_j.
\]

因为 \(M^-<M_1\),附加条件精确等价于

\[
\boxed{\theta_j\log(p_j)\le T_1-T_0}.
\]

等号表示实际下角点恰在下预算端点,仍在定理域内。因此,只要**存在一个**最优真正分数基本解满足这个条件,就有 \(U_{\rm dual}<U_{\rm var}\)。\(T_0>\log5040\) 完整保留,但其数值不是本条比较证明所需的新性质;该结论本身不证明任何 Robin 阈值。

**24.15 残余的一般素数问题与既有反例。** 对 \(k=2\),第 22 节的四角点引理已经从两个实际可行角点推出最优分数解的下角点可行,第 23 节的不同素数严格结算不变。对 \(k\ge3\),还没有证明总能选到满足 24.14 条件的最优基本解;不能把二行计数引理按维数直接外推。存在量词允许在密度并列时选择另一个最优基本解,但不提供这种选择一定成功的算术定理。

结合第 19 节既有充分条件,若真实素数箱体出现反向 \(U_{\rm var}<U_{\rm dual}\),它必须没有整数最优基本解,并且每个最优基本解的相关分数行都必须同时避开已证区域,即

\[
0<\theta_j<1,\qquad \overline V<V_0,\qquad
v^2>\frac{k-1}{k}V_0,\qquad
\theta_j\log p_j>T_1-T_0.
\]

最后一个条件就是实际下角点严格低于薄层。只要任一最优基本解满足已证的充分条件,其最优值就已受控;不能只找到一个不满足下角点条件的解便宣布反向。余域内第 20 节的精确分数行凹性缺口比较仍待解决,尚无本节提供的真实素数反例或普遍占优证明。

第 21 节的人工 \(k=3\) 网格完全保留。直接引用那里已记录的最优解,其实际下角点和为 \(29.82\),而 \(M_0=29.999997\),所以下角点假设失败。另两个实际角点的和均为 \(30\) 不改变这一事实。该人工实数例仍非素数格反例;这里没有重跑其八状态枚举或数值报告,没有新数值实例。

反驳 24.2 需要在完整正二点域中,给出由匹配 LP 解与支持乘子认证的真正分数最优基本解,且其实际下角点属于薄层,却有 \(D(M_1)\ge\Psi_k(\mu,V_0)\)。下角点低于 \(M_0\) 的例子不构成这条条件定理的反证。

**24.16 主数学来源、摄入边界与交付义务。** 主输入是 caller 提供的完成 structured conclusion:task `e96a5b22-8c16-4bd0-95ce-a06f1cf2413a`,conversation `conv_fc5fcce44d2bc103`,载体 `company-chatgpt-pro` browser Work,观测返回模型 `GPT-6 Astra`,完成时间 `2026-09-08T16:42:56.754+00:00`,opaque primary log_ref `qgh0909:lower-corner-all-k:73b2c9e4`。这是同一主数学对话的来源输入,不是独立评审、实施批准或投票。没有打开该 log_ref、原始对话、先前 worker 日志或同轮 peer 输出,没有新 PRO 调用。

本次是 caller 已应用 `consensus-rnd:sshx` 下的 I7 implementation 同载体重试,实施者为 Codex、`repo-prior-exposed`,纸面逐式核对是实施支持证据,不冒称独立复审、上下文无先验或模型多样性。经典分数背包、Jensen 与 Hermite 方法的归属沿用第 15/18/23 节;本次写作还读取 [Continuous knapsack problem](https://en.wikipedia.org/wiki/Continuous_knapsack_problem) 与 [Hermite interpolation](https://en.wikipedia.org/wiki/Hermite_interpolation) 的摘要接口,只核对经典方法归属,未从摘要取得本条件定理,不声称文献穷尽或全球新颖性。

工作树为 `/Users/auricstudio/trureturing-qgh-variance`,分支 `lane/math/quantized-gh-lower-corner-0909`,封存 HEAD 与唯一摄入 BASE 均为 `6fe2f015c1191dca86563a2e1292227af48ce9e0`。追加前实际核对 PR 6488 为 MERGED,merge commit `e03d7817c7d77eb896d5ef5522ab59eb19f297d7`。完整历史前缀为 1547 行、95444 字节、SHA256 `4ac0311a51f086e4ad587f30a73067fca0ebcac222a9499b3ed55af58a9dfaee`,逐字节保留。源之外的新 CAS blob 与 residual-open 条目仅由以下 canonical 命令产生:

```sh
make ingest BASE=6fe2f015c1191dca86563a2e1292227af48ce9e0 SOURCE=arithmetic-boundary-quantization
```

所有历史 CAS/条目及既有报告保留。此前 Q1/T1 advisory 关于约 18 行旧散文未被旧 CAS 切片保留的追溯边界仍在;本增量不修历史源或 producer。本节使用编号项与普通标题,但摄入退出成功本身不证明散文全覆盖:本次实际 emitted claims 的新散文覆盖范围与任何遗漏,由本次实施结果信封逐项报告,不对旧切片作穷尽摄入声明。canonical CAS 的空白/文件末尾格式归 generator 所有,与源 diff 的 whitespace 核验分开报告。

没有 CPU/GPU 候选生成,不重跑 xi、5040 或人工网格,不改工具、测试、其它理论、形式根或冻结状态,不重建 Lean。独立质量复审、CI 三门和 PR MERGED 落地仍由 caller 承担;本实施不宣布这些义务完成。有限的 S12 纸面追加不完成持续研究目标,余下一般素数 \(k\ge3\) 问题保持 **OPEN**。

## 25. 素数逼近的局部障碍与变形三素数族

**25.1 状态、归一化与三个不同的域。** 本节是 2026-09-09 的 S13 追加,状态为 **PAPER_ARGUMENT / repo-derived 参考输入**,另有一份既给人工网格的有界数值证据及一条 literature-attested 短区间素数定理。它们均不是独立数学批准、Lean 冻结、全局素数域定理、RH 进展或新颖性声明。第 1-24 节的全部结算保留;GH 仍未另行定义。

沿用 24.1:整数 \(k\ge2\),\(C_i=\{c_i,d_i\}\)、\(0<c_i<d_i<\infty\),有限 \(M_0<M_1\),闭薄层中的实际角点集 \(\mathcal C\) 至少有两个元素。定义

\[
f(x)=\log(1-e^{-x}),\quad
D(M_1)=\inf_{\lambda\ge0}\left\{\lambda M_1+
\sum_i\max_{x\in C_i}(f(x)-\lambda x)\right\},
\]
\[
\mu_0=M_0/k,\quad\mu=M_1/k,\quad I=[\mu_0,\mu],\quad
\eta_i=\operatorname{dist}(I,C_i),\quad V_0=\sum_i\eta_i^2,
\]
\[
r=\sqrt{V_0/[k(k-1)]},\quad L=\mu-r,\quad H=\mu+(k-1)r,
\quad\Psi_k(\mu,V_0)=f(H)+(k-1)f(L).
\]

所有对数为自然对数,\(V_0\) 是平方距离之和。取任一实际正角点,其均值 \(\bar x\in I\) 给出
\(0\le V_0\le\sum_i(x_i-\bar x)^2<k(k-1)\bar x^2\le k(k-1)\mu^2\),且 \(\mu\ge\bar x>0\),所以 \(H\ge L>0\)。不额外要求 \(\mu_0>0\)。下文的两条支撑引理只需各自明列的正定义域,不以混合支撑代替实际角点。

任意正二点网格、满足 \(c_i/(d_i-c_i)\in\mathbb Z_{\ge1}\) 的整数比网格、以及满足
\(c_i=(b_i+1)\log p_i,d_i=(b_i+2)\log p_i\)、\(b_i\ge0\) 整数且 \(p_i\) 两两不同的真正素数网格,是三个不同的约束层。最后一层还保留 \(\log5040<T_0<T_1\)、至少两个实际指数配置及
\(M_j=T_j+\sum_i\log p_i\)。精确地
\(U_{\rm dual}=\log E_S+D\)、\(U_{\rm var}=\log E_S+\Psi_k\),其中 \(E_S=\prod_{p\in S}(1-p^{-1})^{-1}\);比较差始终为 \(D-\Psi_k\)。零指数允许,其平移后坐标仍正。

**25.2 一个给定的整数比人工网格与八角点。** 本小节至 25.3 固定 \(k=3\),取

\[
(c_1,d_1)=(1000/101,1020/101),\qquad
(c_2,d_2)=(c_3,d_3)=(111650/11211,113680/11211),
\]
\[
h_1=d_1-c_1=20/101,\quad h_2=h_3=2030/11211,\quad
(c_1/h_1,c_2/h_2,c_3/h_3)=(50,55,55),
\]
\[
[M_0,M_1]=[29999997/1000000,30],\qquad
I=[10-10^{-6},10].
\]

按行次序以 0/1 选下/上端点,完整固定分类为

\[
\begin{array}{c|c|c}
\text{角点}&\text{坐标和}&\text{闭薄层分类}\\\hline
000&334300/11211&M<M_0\\
001&30&M=M_1\text{,可行}\\
010&30&M=M_1\text{,可行}\\
011&338360/11211&M>M_1\\
100&336520/11211&M>M_1\\
101&3050/101&M>M_1\\
110&3050/101&M>M_1\\
111&340580/11211&M>M_1
\end{array}
\]

证明只需从全下端点和 \(A=334300/11211\) 加所选宽度:允许增量为 \([h_2-3/10^6,h_2]\),而 \(0<h_2<h_1\)。于是只有 001、010 可行,二者预算都恰为 30。它们是两个不同实坐标向量;重复的第 2、3 行不是不同素数标签。有理宽度及整数下端点比不提供素数对数的实现,不能把此例升级为真正素数反例。本例为已给的单个人工见证,没有候选搜索。

**25.3 最优割线证书、精确矩与严格正号。** 令
\(\rho_i=[f(d_i)-f(c_i)]/h_i\)。由于 \(c_1<c_2=c_3\)、\(d_1<d_2=d_3\),对每个 \(v\in[0,1]\) 有
\(c_1+vh_1<c_2+vh_2\)。由 \(f'(x)=1/(e^x-1)>0\) 严格递减及
\(\rho_i=\int_0^1 f'(c_i+vh_i)\,dv\),得 \(\rho_1>\rho_2=\rho_3>0\)。置

\[
\theta=203/222,\quad\alpha=1-\theta=19/222,\quad
A+\theta h_1=A+h_2=30.
\]

混合 000、100,上端点权重为 \(\theta\),其它两行固定在 \(c_2,c_3\)。在价格 \(\lambda=\rho_1\) 下第 1 行两端点并列,其它行唯一下端点最大,故

\[
D(30)=\alpha f(c_1)+\theta f(d_1)+2f(c_2)
=30\lambda+\sum_{i=1}^3[f(c_i)-\lambda c_i].
\]

任意期望预算可行混合都不超过右端价格值,而此混合达到它,这就是最优性与无对偶间隙的精确证书。两个支撑角点均在实际薄层外;LP 的期望可行不等于逐点可行。

每行都跨越 \(I\),这里最近的均为下端点,故

\[
\eta_1=10/101-10^{-6},\quad
\eta_2=\eta_3=460/11211-10^{-6},\quad
V_0=\frac{1655254483717059563}{125686521000000000000}.
\]

取 \(r=\sqrt{V_0/6}\),有 \(c_1<L=10-r<c_2\),\(H=10+2r\)。均值向量平方偏差及混合的中心二阶矩分别为

\[
\overline V=\frac{423200}{41895507}<V_0,\qquad
\overline V+\theta(1-\theta)h_1^2=\frac{1655300}{125686521},
\]
\[
\frac{1655300}{125686521}-V_0
=\frac{4059966367}{11211000000000000}>0.
\]

还有 \(3\eta_1^2>2V_0\)、\(\theta h_1=h_2>3/10^6\),所以它避开第 19 节相关充分条件及第 24 节下角点条件。给定的 Python-FLINT 0.8.0 / Arb 256 位程序,以精确有理输入和严格球比较认证

\[
\boxed{10^{-10}<D(30)-\Psi_3(10,V_0)<10^{-9}}.
\]

[integer-ratio-grid-0909.md](../../reports/integer-ratio-grid-0909.md) 完整保留所供 2512 字节程序、1840 字节 JSON 证书、全部八项分类及其摘要、原始程序身份和可复现命令。显示近似 \(3.3666865560\ldots\times10^{-10}\) 不承担符号认证。该报告还分列 primary 的 \(2^{-384}\) 有理包围及其自报算法身份,不把两份支持计算当成两张独立评审票。本次实施只执行这一既给程序一次并核对输出;没有生成新网格、枚举素数或重跑第 21 节旧报告。

**25.4 一个低支撑点的充分条件。** 设整数 \(k\ge2\),\(0<L\le H\),且一个已匹配证明最优的混合写成

\[
D=\alpha f(c)+\sum_{q=1}^N w_qf(z_q),\qquad
0<\alpha\le1,\quad w_q>0,\quad
\alpha+\sum_qw_q=k,
\]

其中支撑有限、\(c,z_q>0\)。若 \(c<L\) 且 \(\alpha e^{L-c}\ge k\),则
\(D<f(H)+(k-1)f(L)\)。证明:用绝对收敛级数
\(f(x)=-\sum_{n\ge1}e^{-nx}/n\),差的第 \(n\) 项分子为

\[
e^{-nH}+(k-1)e^{-nL}-\alpha e^{-nc}-\sum_qw_qe^{-nz_q}
<ke^{-nL}-\alpha e^{-nc}\le0.
\]

最后一步用 \(\alpha e^{n(L-c)}\ge\alpha e^{L-c}\ge k\);严格性来自删去的正支撑项,\(k-\alpha>0\) 保证这些项存在。差级数绝对收敛,逐项严格负即得结论。充分条件阈值取等仍严格;失败时不推断反向。用作方差比较时,\(L,H\) 须是 25.1 的有效包络节点。

**25.5 明确的仿射邻域障碍及小尺度算术矛盾。** 以 25.2 的固定 \(c_i,d_i,M_j\) 为模板,置 \(\varepsilon=10^{-12}\)。定理的量词是:对每个 \(s>0\)、\(a\in\mathbb R\)、误差
\(|e_i|,|f_i|,|u_j|\le\varepsilon\) (\(i=1,2,3;j=0,1\)),令

\[
c'_i=a+s(c_i+e_i),\quad d'_i=a+s(d_i+f_i),\quad
M'_j=3a+s(M_j+u_j).
\]

这里 \(f_i\) 只是端点误差,不改变函数 \(f\)。要求 \(0<c'_i<d'_i\)、有限严格薄层及至少两个实际可行角点,按 25.1 对这些新数据定义 \(\mu',V'_0,L',H',D'\)。若
\(d'_i-c'_i=\log p_i\) 且 \(p_1,p_2,p_3\) 两两不同为素数,则不可能有
\(D'(M'_1)>\Psi_3(\mu',V'_0)\)。更明确地,\(0<s<80\) 时这种宽度实现本身不可能;\(s\ge80\) 时即使不要求素数宽度,也有严格 \(D'<\Psi_3\)。扰动上界是除以共同尺度 \(s\) 后的上界,不把它误写成实际端点的绝对误差上界。整数下端点比不是本定理前提,所以整数比子类也包含在内。

先证 \(0<s<80\)。第 2、3 行宽度差至多 \(4s\varepsilon<320\varepsilon\),且每个宽度小于
\(80(h_2+2\varepsilon)<15\)。于是 \(p_2,p_3<e^{15}<3^{15}\)。对不同正整数 \(p,q\),积分 \(\int_{\min(p,q)}^{\max(p,q)}dt/t\) 给出
\(|\log p-\log q|\ge1/\max(p,q)>3^{-15}\)。但
\(320\varepsilon<3^{-15}\),矛盾。这里只用整数间隔,没有素数密度或同时逼近假设。

**25.6 大尺度证明,含平移与闭扰动边界。** 设 \(s\ge80\)。端点严格次序保留:原下端点差为 \(650/11211\),上端点差为 \(460/11211\),均大于 \(2\varepsilon\)。所以新第 1 行割线密度严格最大。令
\(R'=M'_1-\sum_ic'_i\)、\(h'_1=d'_1-c'_1\),有

\[
|R'/s-h_2|\le4\varepsilon,\quad
|h'_1/s-h_1|\le2\varepsilon,\quad
0<R'<h'_1,\quad
\alpha'=1-R'/h'_1>2/25.
\]

末两项由固定有理不等式
\(h_2-4\varepsilon>0\) 及
\((h_2+4\varepsilon)/(h_1-2\varepsilon)<23/25\) 直接得出。故新最优值仍由第 1 行混合、其它行下端点及价格 \(\rho'_1\) 精确匹配。

将新均值区间与端点集合都减 \(a\) 再除 \(s\),二者的 Hausdorff 距离分别至多 \(\varepsilon/3\)、\(\varepsilon\)。集合距离的三角不等式于是给出

\[
|\eta'_i/s-\eta_i|\le4\varepsilon/3.
\]

这里不假定扰动后最近端点仍相同。25.3 的精确距离给出
\(\eta'_1/s<1/10\)、\(\eta'_2/s,\eta'_3/s<1/24\),所以

\[
(r'/s)^2<\frac{1/100+2/24^2}{6}<(49/1000)^2,
\qquad (\mu'-c'_1)/s>99/1000.
\]

从而 \(L'-c'_1>s/20\ge4\)。由于
\(e^4>\sum_{n=0}^5 4^n/n!=643/15\),有
\(\alpha'e^{L'-c'_1}>(2/25)(643/15)>3\)。正端点及实际非空保证 \(L'>0\),25.4 立即给出严格 \(D'<\Psi_3\)。所有估计与 \(a\) 无关,只需平移后端点正;\(s=80\) 与任一 \(|e_i|,|f_i|,|u_j|=\varepsilon\) 均包括,没有阈值等号情形。80 是足够的尺度,不声称最优。

**25.7 精确实现限制与局部结论的边界。** 零误差时 \(h_1/h_2=222/203\)。若这些缩放宽度是不同素数对数,必有 \(p_1^{203}=p_2^{222}\),违反唯一分解;重复宽度还强制 \(p_2=p_3\)。共同平移不改变宽度。25.5-25.6 进一步排除整个明确邻域中的反向素数实例,不是仅排除精确相等。

任意共同平移一般不保留整数下端点比。一个确实保留的子族是取 \(q=10/11211\)、\(a=sq\,45066N\)、\(N\in\mathbb Z_{\ge0}\),此时三个比为
\(50+203N,55+222N,55+222N\)。\(s\ge80\) 时这些平移也严格负。更一般地,对零误差仿射族,令模板节点为 \(L,H\),有

\[
A_f(t)=e^{-tH}+2e^{-tL}-\alpha e^{-tc_1}-\theta e^{-td_1}-2e^{-tc_2},
\quad D(s,a)-\Psi(s,a)=\sum_{n\ge1}\frac{e^{-na}A_f(ns)}n.
\]

正支撑保证绝对收敛,上述证明给出 \(A_f(t)<0\) 对每个 \(t\ge80\) 成立。固定 \(s>0\) 时,级数还给出
\(\lim_{a\to\infty}e^a[D(s,a)-\Psi(s,a)]=A_f(s)\);某个有限平移的正差并不单独证明此系数为正。此障碍只属于这个固定仿射邻域,不排除较大形变、随素数改变形状的网格或其它整数比见证。唯一分解也不证明任意多个倒数素数对数的线性独立,不偷渡这种同时逼近假设。

**25.8 所需短区间定理及 caller 核对的来源。** Literature-attested 输入为 R. C. Baker、G. Harman、J. Pintz, *The Difference Between Consecutive Primes, II*, *Proc. London Math. Soc.* (3) **83** (2001),532-562,DOI [10.1112/plms/83.3.532](https://doi.org/10.1112/plms/83.3.532),Theorem 1:存在 \(x_0\),对所有实数 \(x>x_0\),区间

\[
[x-x^{0.525},x]=[x-x^{21/40},x]
\]

含素数。Caller 独立下载并核对了 [大学镜像的原论文](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf),位置 PDF 第 1 页 / 期刊第 532 页,PDF SHA256 为 `d3b6011255c49e52b002e08faebb7d252ca1027e545b72fa097176e6285443a2`。这是 caller-checked 书目、区间方向及实数全称量词的 provenance,不声称这就是先前 primary invocation 所访问的 author-uploaded URL。本增量没有复核完整筛法证明,没有有效数值 \(x_0\)。

令 \(P\) 趋于无穷并遍历素数,\(X=P-P^{3/5}\),\(Q\) 为不大于 \(X\) 的最大素数,\(R\) 为 \(Q\) 的前一素数。足够大时在 \(X\) 应用定理得到
\(0\le X-Q\le X^{21/40}\)。再在实数 \(Q-1/2\) 应用,所得素数严格小于 \(Q\),从而不大于 \(R\),故

\[
0<Q-R\le\tfrac12+(Q-\tfrac12)^{21/40},\quad
P-Q=P^{3/5}+O(P^{21/40}),\quad Q-R=O(P^{21/40}).
\]

这同时证明所选 \(Q,R\) 足够大时存在且 \(P>Q>R\)。隐常数沿本选择规则统一,不把 \(Q-R\) 指定成未经定理提供的渐近主项。

**25.9 变形三素数族、精确薄层及八个分析角点。** 取 25.8 的素数规则,记

\[
h=\log P,\quad h_2=\log Q=h-\delta,\quad
h_3=\log R=h-\delta-\eta,\quad
\delta=\log(P/Q)>0,\quad\eta=\log(Q/R)>0,
\]
\[
m=\left\lfloor\frac{3h}{5\delta}\right\rfloor,\quad
(c_1,d_1)=(mh,(m+1)h),\quad
(c_2,d_2)=((m+1)h_2,(m+2)h_2),
\]
\[
(c_3,d_3)=((m+1)h_3,(m+2)h_3),\quad
A=c_1+c_2+c_3,\quad M_0=A+h_3,\quad M_1=A+h_2.
\]

下端点的平移后指数是 \((m,m+1,m+1)\),原指数是 \((m-1,m,m)\)。对所有足够大的 \(P\),\(m\ge1\),端点正且 \(h>h_2>h_3>0\)。允许的角点增量恰为 \([h_3,h_2]\),因而全部八种情况为

\[
\begin{array}{c|c|c}
000&A&<M_0\\
001&A+h_3&=M_0\text{,可行}\\
010&A+h_2&=M_1\text{,可行}\\
011&A+h_2+h_3&>M_1\\
100&A+h&>M_1\\
101&A+h+h_3&>M_1\\
110&A+h+h_2&>M_1\\
111&A+h+h_2+h_3&>M_1
\end{array}
\]

这是由严格宽度次序直接证明的全族分类,没有执行素数采样。与 25.2 不同,两可行角点有不同预算,精确平移回素数指数预算得到

\[
T_0=(m-1)h+mh_2+(m+1)h_3,\quad
T_1=(m-1)h+(m+1)h_2+mh_3,
\]

对应实际整数 \(P^{m-1}Q^mR^{m+1}\) 和 \(P^{m-1}Q^{m+1}R^m\)。有
\(T_1-T_0=M_1-M_0=\eta>0\),且最终 \(T_0>\log5040\)。两者均在闭薄层端点,不同素数的唯一分解保证整数不同。

**25.10 素数间距与取整误差的统一控制。** 下面的推导也条件性适用于 25.8 的两条间距估计中任意固定 \(0<\beta<3/5\) 代替 \(21/40\)。由 \(-\log(1-x)=x+O(x^2)\) 在统一的小 \(x\) 区间展开,

\[
\delta=P^{-2/5}\{1+O(P^{\beta-3/5}+P^{-2/5})\},\quad
\eta=O(P^{\beta-1}),\quad
m+1=O(h/\delta).
\]

引入精确变量

\[
\zeta=3h/5-m\delta\in[0,\delta),\quad
w=m\delta/3=h/5-\zeta/3,\quad E=(m+1)\eta,
\]
\[
u=c_2-c_1=h-(m+1)\delta=2h/5+\zeta-\delta,\quad
c_3=c_2-E,\quad\mu=M_1/3=c_2+w-E/3,\quad\mu_0=\mu-\eta/3.
\]

于是 \(E=O(hP^{\beta-3/5})\),尤其 \(E\to0\) 且 \(hE\to0\),后一个界是控制 \(1/h\) 尺度抵消所必需的。采用 BHP 的 \(\beta=21/40\),得到统一估计

\[
\delta=P^{-2/5}(1+O(P^{-3/40})),\quad
\eta=O(P^{-19/40}),\quad E=O(hP^{-3/40}).
\]

这些 \(O\) 常数不依赖素数 \(P\)、允许的间距波动或取整相位 \(\zeta\)。只用 \(0\le\zeta<\delta\),不假定它有极限或均匀分布;\(\zeta=0\) 包含在证明中。\(m\to\infty\) 也证明 25.9 的原指数最终非负及下预算趋于无穷。

**25.11 真素数族的最优混合与价格。** 足够大时

\[
c_2-c_1=u>0,\quad c_3-c_1=u-E>0,\quad
d_2-d_1=u-\delta>0,\quad
d_3-d_1=u-E-\delta-\eta>0.
\]

又 \(c_3<c_2,d_3<d_2\)。同 25.3 的割线积分证明
\(\rho_1>\rho_3>\rho_2>0\)。剩余预算恰为 \(M_1-A=h_2<h\),所以令

\[
\theta=h_2/h\in(0,1),\quad\alpha=1-\theta=\delta/h,\quad
D(M_1)=\alpha f(c_1)+\theta f(d_1)+f(c_2)+f(c_3).
\]

在 \(\lambda=\rho_1\) 处第 1 行并列、其它两行下端点唯一最大,且

\[
\lambda M_1+\sum_i[f(c_i)-\lambda c_i]
=\sum_i f(c_i)+\rho_1h_2
=\alpha f(c_1)+\theta f(d_1)+f(c_2)+f(c_3).
\]

期望和 \(A+\theta h=M_1\) 与逐项弱对偶证明这个匹配值精确最优。实际混合下角点 000 的和 \(A<M_0\),上角点 100 的和 \(A+h>M_1\);本族不满足第 24 节的可行下角点条件。乘回准确的 \(E_{\{P,Q,R\}}\) 后,\(U_{\rm dual}-U_{\rm var}=D-\Psi_3\) 的身份不变。

**25.12 最近端点的更正与精确包络。** 每行最终都严格跨越 \(I=[\mu-\eta/3,\mu]\)。依次列出到下/上端点的距离:

\[
\begin{array}{c|c|c}
1&\mu_0-c_1=h-v-\eta/3&d_1-\mu=v=2w+\delta+E/3\\
2&\mu_0-c_2=\ell_2=w-(E+\eta)/3&d_2-\mu=h-\delta-w+E/3\\
3&\mu_0-c_3=\ell_3=w+(2E-\eta)/3&d_3-\mu=h-\delta-\eta-w-2E/3
\end{array}
\]

每一对除以 \(h\) 的极限分别为 \((3/5,2/5)\)、\((1/5,4/5)\)、\((1/5,4/5)\),全部为正且两项严格分离。故最近端点依次是 **第 1 行上端点 \(d_1\)、第 2 行下端点 \(c_2\)、第 3 行下端点 \(c_3\)**。这明确纠正 caller 曾丢弃的“第 1 行下端点最近”预期;不能沿用人工见证 25.3 的选择。

因此真正的距离和及包络精确为

\[
V_0=v^2+\ell_2^2+\ell_3^2
=6w^2+4w\delta+2wE-\tfrac43w\eta+
\delta^2+\tfrac23\delta E+\tfrac23E^2-\tfrac29E\eta+\tfrac29\eta^2,
\]
\[
r=\sqrt{V_0/6},\quad L=\mu-r,\quad H=\mu+2r,\quad
\Psi_3(\mu,V_0)=f(H)+2f(L),\quad
V_0/h^2\longrightarrow6/25,\quad r/h\longrightarrow1/5.
\]

实际可行正角点按 25.1 保证 \(L>0\);下段还会证明它在最终范围内严格大于 \(c_1\)。本论证不把有限初段的端点选择或密度可能并列静默排除;所声称的是存在足够大的阈值使这些严格选择同时成立。

**25.13 抵消位置与负指数函数的精确余项。** 距离向量为

\[
(v,\ell_2,\ell_3)=(2w,w,w)+
(\delta+E/3,-(E+\eta)/3,(2E-\eta)/3).
\]

Euclidean 范数的逆三角不等式及 \(w>0\) 给出

\[
|r-w|\le\frac{\delta+4E/3+2\eta/3}{\sqrt6}
\le\delta+E+\eta.
\]

置 \(B=\delta+2E+\eta\),则 \(|L-c_2|\le B\)、\(E\le B\)、\(hB\to0\)。还有

\[
d_1-c_2=3w+\delta\ge3h/5,\quad
H-c_2=3w+2(r-w)-E/3\ge h/2
\]

最终成立,而 \(u/h\to2/5\) 及 \(B/h\to0\) 给出 \(L-c_1\ge u-B>0\)。因此 \(c_1\) 最终是混合及包络所有函数自变量的最小值。

暂置 \(g(x)=-e^{-x}\)。其 \(g'\) 也严格递减,所以相同割线次序、相同混合权重和相应价格证明 \(D_g\) 最优。写
\(G_g=D_g-[g(H)+2g(L)]\),精确有

\[
e^{c_2}G_g=2e^{c_2-L}-1-e^E+e^{c_2-H}
-\theta e^{c_2-d_1}-\alpha e^u.
\]

用 \(|e^x-1|\le|x|e^{|x|}\),前面三项的绝对值至多 \(3Be^B\);两个高端点项的绝对值和至多 \(2e^{-h/2}\)。由于 \(h\alpha=\delta\),得到

\[
\left|h e^{c_2}G_g+\delta e^u\right|
\le h[3Be^B+2e^{-h/2}].
\]

右边趋于零。取整误差的精确控制是

\[
\delta e^u=\delta P^{2/5}e^{\zeta-\delta},\qquad
-\delta\le\zeta-\delta<0,\qquad \delta e^u\longrightarrow1.
\]

这一等式包含所有 floor 余数,而非将 \(m\delta\) 直接当成 \(3h/5\)。

**25.14 回到 \(f\) 的统一误差与最终严格负号。** 对每个 \(x>0\),对数级数给出

\[
|f(x)+e^{-x}|=\sum_{n\ge2}\frac{e^{-nx}}n
\le\frac{e^{-2x}}{2(1-e^{-x})}.
\]

混合和包络的总权重各为 3,所有自变量最终至少为 \(c_1\),所以

\[
|(D-\Psi_3)-G_g|\le\frac{3e^{-2c_1}}{1-e^{-c_1}},
\]
\[
\boxed{\left|h e^{c_2}(D-\Psi_3)+\delta e^u\right|
\le h[3Be^B+2e^{-h/2}]
+\frac{3h e^{u-c_1}}{1-e^{-c_1}}.}
\]

这是在实际趋零差值尺度上的显式归一化余项,不只是不缩放的 \(f\to g\) 近似。因 \(u<h,c_1=mh\),最终 \(m\ge2\) 时最后一项至多
\(3hP^{-1}/(1-P^{-2})\),也趋于零。BHP 的统一间距界及完整的 floor 区间于是给出

\[
\boxed{\lim_{\substack{P\to\infty\\P\ {\rm prime}}}
h e^{c_2}[D(M_1)-\Psi_3(\mu,V_0)]=-1},\qquad
h e^{c_2}(D-\Psi_3)=-1+O(h^2P^{-3/40}),
\]
\[
D-\Psi_3=-\frac{1+o(1)}{\log P\,Q^{m+1}}.
\]

特别地,存在 \(P_*\),对每个素数 \(P>P_*\) 按上述精确规则选 \(Q,R,m\),完整素数薄层域成立且
\(D-\Psi_3<-e^{-c_2}/(2h)<0\)。罕见的第 1 行下端点质量 \(\alpha\) 在抵消后贡献主负项。没有建立有限数值 \(P_*\),没有声称分类了初段;\(R\) 不存在或 \(m=0\) 的小值不在定理所述最终域。最终无 \(D=\Psi_3\) 等号,其它网格的等号分类仍未解决。一个小 \(P\) 的反向值本身不会反驳最终定理。

**25.15 已由后续实际 PRO 更正的抵消引理。** 设整数 \(k\ge2\),正二点网格的精确最优基本混合只有一行真正分数,其端点为 \(0<c<d\)、下端点权重 \(\alpha\in(0,1)\),其它 \(k-1\) 行固定于正的实际端点 \(t_i\)。明确要求匹配原始/价格证书给出

\[
D=\alpha f(c)+(1-\alpha)f(d)+\sum_{i\ne j}f(t_i).
\]

令 \(\mu>0,0\le V_0<k(k-1)\mu^2\),按 25.1 定义 \(H\ge L>0\),并置 \(t=\max_{i\ne j}t_i\)。定义

\[
\boxed{K=\frac{(k-1)\max\{t-L,0\}\,e^{t-L}}{1-e^{-L}}
+\frac{e^{t-H}}{1-e^{-H}}.}
\]

第一项中 \((k-1)\)、正部 \(\max\{t-L,0\}\) 与 \(e^{t-L}\) 的相邻书写明确表示 **乘法**。若 \(\alpha e^{t-c}\ge K\),则严格 \(D<\Psi_k(\mu,V_0)\),包括条件阈值取等。这一公式采用 recovered primary payload 的 `K_correction`,更正先前纯文本歧义;恢复载体不构成独立评审票。

证明:由 \(f\) 递增及 \(f'\) 递减,当 \(t\ge L\) 时积分给出
\(f(t)-f(L)\le(t-L)/(e^L-1)\);当 \(t<L\) 时左边负而正部为零。因此统一有
\(f(t)-f(L)\le\max\{t-L,0\}/(e^L-1)\)。对数级数严格给出
\(f(c)<-e^{-c}\)、\(-f(H)<e^{-H}/(1-e^{-H})\),又 \(f(d)<0\)、\(f(t_i)\le f(t)\),故

\[
D-\Psi_k
< -\alpha e^{-c}+
\frac{(k-1)\max\{t-L,0\}}{e^L-1}
+\frac{e^{-H}}{1-e^{-H}}
=e^{-t}(K-\alpha e^{t-c}).
\]

\(\alpha>0\)、\(1-\alpha>0\) 和所有自变量有限且正确保上述严格步不会因阈值取等而消失。\(L>0\) 保证所有分母正;它来自明列的包络域,在实际非空薄层中由 25.1 证明,不是从图形假定。\(V_0=0\) 仍有效,此时 \(L=H=\mu>0\);不要求 \(t\le H\) 或 \(c<L\)。\(\alpha=0,1\) 或整数最优解不属于本条真正分数陈述,不另添端点结论。条件失败也不推出反向。

在上述三素数族取 \(t=c_2\)。由 \(|L-c_2|\le B\)、\(H-c_2\ge h/2\) 及 \(L,H\to\infty\),有
\(K=O(B)+O(e^{-h/2})=o(1/h)\),而
\(\alpha e^{t-c_1}=\delta e^u/h\sim1/h\),故该引理最终直接适用于 \(f\)。相反,25.4 的量
\(\alpha e^{L-c_1}=\delta e^u e^{L-c_2}/h\sim1/h\to0\),不能达到 3;抵消引理提供的是另一条充分条件。

**25.16 研究问题的变化、量词边界与未决义务。** 25.2-25.3 给出整数比正实网格上的一个严格正差,没有真正素数标签。25.5-25.7 证明从这个见证作任意精确缩放/共同平移并在指定 \(10^{-12}\) 归一化邻域内逼近素数的反向路线失败。25.8-25.14 解决一族随素数改变形状的真正三素数网格,其差最终严格负,但不外推到其它形状、所有 \(P\) 或所有 \(k\ge3\)。本族不满足可行下角点条件,所以它增加一个已处理域,没有证明那项条件总可安排。

原来无界的不同素数 \(k\ge3\) 比较仍 **OPEN**:对每个有限不同素数集、每个相邻非负整数指数箱体、每个 \(\log5040<T_0<T_1\) 且至少两个实际配置的闭薄层,是否总有 \(U_{\rm dual}\le U_{\rm var}\)? 在既有充分条件及本节已处理域外,选一个匹配最优基本解,令唯一分数行上权重为 \(\theta\)、均值为 \(y_j=(1-\theta)c_j+\theta d_j\),其余 \(y_i=t_i\),写

\[
J_j=f(y_j)-(1-\theta)f(c_j)-\theta f(d_j)>0,\quad
D-\Psi_k=\sum_i f(y_i)-\Psi_k(\mu,V_0)-J_j.
\]

仍需在剩余完整素数域证明 \(J_j\ge\sum_i f(y_i)-\Psi_k\),或给出同时具有两个实际薄层配置、精确最优混合/价格证书及严格负的该凹性余量的真正反例。等号也由这个恒等式精确决定,但一般素数域的等号分类未得。25.5 的邻域不能扩大,25.14 的存在阈值不能伪装成有效 cutoff;唯一分解与 BHP 也不提供未证明的倒数对数独立性或全实数薄层有限归约。

前瞻反驳标准也按域区分:满足 25.5 全部条件的严格反向素数实例会反驳邻域定理;满足 25.15 全部条件及阈值却有 \(D\ge\Psi_k\) 会反驳抵消引理。25.14 可直接检验的核心是所列距离选择、\(c_1\) 最小、节点界和匹配证书成立时的显式余项不等式。邻域之外的真正反例不会反驳局部障碍;孤立小素数反向值也不自动反驳最终负号。

**25.17 主来源、支持证据与恢复身份。** 本次只消费 caller 所供完成输入的 conclusion 及完成元数据,未追随任何 `log_ref`,未打开 worker 日志或另一 S12 worktree。两次主数学任务均来自 `company-chatgpt-pro` browser Work,pool ID `61e1f52e-a625-4e08-b426-43e25bbab449`,完成记录观测模型均为 `GPT-6 Astra`,不是按产品名猜测模型:

- 仿射障碍 task `c9caf71c-5b42-4d07-8de0-98540288eb7e`,conversation `conv_515ce9ddd365db68`,完成 `2026-09-08T17:49:38.119+00:00`。Envelope `pro-prime-bridge-retry-envelope-0909.json` SHA256 `1c8f5ae65d521ad567538a39a9623fcbbcdd6816f814307492682adada7cb515`;完成记录 `pro-prime-bridge-retry-complete-0909.json` SHA256 `862db73918aef78c101bd35ded76006783fa378d8cb53f483f5fad206ce554d9`。
- 变形素数族 task `69b53236-d65f-4a22-92d4-fae3fd47b58f`,同 conversation 的 follow-up,完成 `2026-09-08T18:14:16.718+00:00`。Envelope `pro-short-interval-primes-envelope-0909.json` SHA256 `5ee071939adcc75ee407f20cc254b4c4002941e9aeb032169bf5a3990097f9f3`;完成记录 `pro-short-interval-primes-complete-0909.json` SHA256 `1e0da2ce725a0ae90f6f507d9b70eea21a0bb1691ed66094246f1f462f41dbf7`。
- 两完成记录的 response 分别与给定 envelope 解析为相同对象。它们是 primary research 输入,不是相互独立的 review。原任务自报仿射论证核对一网格八角点、14 条固定有理不等式;短区间任务自报五项符号恒等式,零素数样本,这些自报与本次实际执行分列。
- `caller-short-interval-audit-0909.json` SHA256 `8fe87b0f14e0997aec9a8f52b2c07060cd277e9f0403ab7f7ea1744d14d22c02` 记录 caller 用 SymPy 1.14.0 核对 11 条精确恒等式、exit 0、零素数样本,是支持证据而非独立批准。其旧 notation-gap 字段由下项后续 correction 解决。
- `pro-prime-gpu-batch-recovered-input-0909.json` SHA256 `4bdcc8bae0a09e9303d968038f5f256055db717101270f3791755fcbfaff6252` 的 `K_correction` 是本节唯一采用的后续数学更正。`caller-prime-payload-recovery-0909.json` SHA256 `dc315e7fa8ff3d7a0e38754f09b10c3fffeb1bf10d46a1f536404f8d8a528f4f` 记录原 reply 需六处 JSON 反斜杠插入、caller 核对忠实身份及全部原 conclusion 字段保留;该恢复不是替代主数学或独立 review,不为其另造 invocation/model 身份。
- `caller-bhp-source-check-0909.json` SHA256 `9ce134f11bd5d7fae613893f0b8706bf07e68cbd019c828efe80563e9d392ba1` 是 25.8 所用来源核对。以上 basename 均指 caller 的 `/tmp/qgh-boundaries-0908/` 完成输入;其所含路径只是 provenance,不作为追读日志的指令。整数比程序及证书则已完整保存于本节链接的持久报告。

**25.18 摄入范围与交付边界。** 实施是 caller 已编排 `consensus-rnd:sshx` 的 I8 implementation,由 Codex 逐式审计和追加,`repo-prior-exposed`;无子 worker、无同轮独立评审票,不声称 sterile priors 或已证明模型族多样性。短区间定理、经典分数背包/弱对偶、对数级数及范数不等式按各自来源使用,本节组合是纸面推导,不声称文献穷尽。独立数学复审、普通 CI 三门及 MERGED 仍是 caller 的后续义务。

本树 `/Users/auricstudio/trureturing-qgh-prime-obstructions`,分支 `lane/math/quantized-gh-prime-obstructions-0909`,封存 HEAD 和唯一摄入 BASE 均为 `c6bf5faaf36deb301317ef393195be039e410656`。追加前完整源为 1932 行、116207 字节、SHA256 `47c5027509e1641f3cbedff7dd2c8b5fe4c660c78931e06dbcc1f8d2c74ac8d6`,逐字节保留。唯一 CAS/条目写者为

```sh
make ingest BASE=c6bf5faaf36deb301317ef393195be039e410656 SOURCE=arithmetic-boundary-quantization
```

本次实际新增 blob/entry、编号证明覆盖及格式例外在 implementation envelope 中报告;成功 exit 本身不证明散文覆盖。新命题只进入 residual-open,不代表 Lean 吸收或数学冻结。历史 Q1/T1 关于 18 行旧散文位于旧 CAS 之外的 advisory 继续披露,本次不修历史。canonical generator 所有的 LF/空白 EOF 变体与源 diff 的 whitespace 检查分列。

只增加本节、一个既有 `docs/reports/**` 约定下的给定见证报告及 canonical 摄入结果,保留全部历史 CAS/entry/report。不采用恢复 GPU 设计的 manifest 或歧义尾项,不修它们、不实现 kernel、不把设计计数称为执行计数;另一个仍在运行的全实数薄层有限归约 PRO 任务不在本节输入中。没有 CPU/GPU 候选生成、素数枚举、固定 xi 重放、Lean 重建、harness 或 workflow 改动,没有 commit/push/PR 操作。按 caller 最新交付上下文,S12 PR #6640 有三份 approve 但仍 OPEN,其外部 harness 修复 #6644 已 MERGED;这些是 caller 所供状态,不是本 worker 新取的 GitHub 读数。C22 只允许此隔离树提前实施,S12 MERGED 仍是 S13 delivery 依赖。有限的纸面追加不完成长期研究目标。

## 26. 固定素数箱体的全实数薄层有限归约

**26.1 状态与量词。** 本节为 2026-09-09 的 S14 参考输入,状态为 PAPER_ARGUMENT / repo-derived。两次已完成的实际 GPT PRO 主推导依次给出有限归约及其活跃切换点精化;它们是顺序 primary 输入,不是独立 review 共识。下面给出本问题的完整专门化证明,经典材料的准确归属见 26.28。本节不作新颖性或 Lean-frozen 声明。第 1-25 节的源字节和既有结算保留;本节把每个固定素数/指数箱体内不可数的实预算域归约为有限测试,不截断素数或指数的无界量词。GH 仍是用户的原标签,没有增添其数学定义,也没有泛化 RH 的主张。

**26.2 实际角点、闭薄层与预算平移。** 固定整数 \(k\ge2\)、两两不同的素数 \(p_1,\ldots,p_k\)、整数 \(b_i\ge0\),置

\[
h_i=\log p_i,\quad c_i=(b_i+1)h_i,\quad d_i=(b_i+2)h_i,\quad
C_i=\{c_i,d_i\},\quad A=\sum_i c_i,
\]
\[
P=\prod_i p_i,\qquad Q=\log P=\sum_i h_i,\qquad N=2^k.
\]

全部对数为自然对数。实际角点为 \(x_i=c_i+e_i h_i\),\(e_i\in\{0,1\}\)。唯一分解保证不同二进制向量给出不同乘积,故可严格排列

\[
R_s=\prod_i p_i^{\,b_i+e_i^{(s)}},\qquad
\beta_s=\sum_i(c_i+e_i^{(s)}h_i)=\log(PR_s),
\quad 0\le s<N,
\]
\[
R_0<\cdots<R_{N-1},\qquad
\beta_0=A<\cdots<\beta_{N-1}=A+Q.
\]

令 \(B_{\rm cut}=Q+\log5040\)。本节的可容许域 \(\mathscr S\) 是所有有限实数对
\((M_0,M_1)\),满足 \(B_{\rm cut}<M_0<M_1\),且闭区间
\([M_0,M_1]\) 至少含两个实际角点预算 \(\beta_s\)。原指数预算为
\(T_j=M_j-Q\),故严格 cutoff 恰为 \(\log5040<T_0<T_1\)。
两端预算均为实数,不要求 \(e^{T_j}\) 为整数;“两个实际角点”也不能用两个混合支撑点替代。

**26.3 同一对偶、同一方差和同一比较差。** 保留
\(f(x)=\log(1-e^{-x})\),对 \(u=M_1\) 定义

\[
D(u)=\inf_{\lambda\ge0}\left\{\lambda u+
\sum_i\max_{x\in C_i}\bigl(f(x)-\lambda x\bigr)\right\},
\]
\[
v_i=f(d_i)-f(c_i)>0,\qquad
D(u)=\sum_i f(c_i)+\inf_{\lambda\ge0}
\left\{\lambda(u-A)+\sum_i\max(0,v_i-\lambda h_i)\right\}.
\]

其精确分数背包形式将在 26.10-26.11 用匹配证书证明:

\[
D(u)=\max_{\substack{0\le y_i\le1\\\sum_i h_i y_i\le u-A}}
\sum_i\bigl((1-y_i)f(c_i)+y_i f(d_i)\bigr),\qquad u\ge A.
\]

对每个可容许薄层置

\[
I=[M_0/k,u/k],\quad
\delta_i(M_0,u)=\operatorname{dist}(I,C_i),\quad
V_0(M_0,u)=\sum_i\delta_i(M_0,u)^2,
\]
\[
\mu=u/k,\quad \rho=\sqrt{\frac{V_0}{k(k-1)}},\quad
H=\mu+(k-1)\rho,\quad L=\mu-\rho,\quad
\Psi(M_0,u)=f(H)+(k-1)f(L),\quad G(M_0,u)=D(u)-\Psi(M_0,u).
\]

\(V_0\) 仍是平方距离之和,没有除以 \(k\)。
记 \(E_S=\prod_i(1-p_i^{-1})^{-1}\),则
\(U_{\rm dual}=\log E_S+D\)、\(U_{\rm var}=\log E_S+\Psi\)。
共同的 \(\log E_S\) 精确抵消,所以 \(G=U_{\rm dual}-U_{\rm var}\);
这里没有更换第 18、19、24、25 节的归一化。

**26.4 包络的完整正定义域。** 置 \(c_{\min}=\min_i c_i\ge\log2\)。
取薄层内任一实际角点 \(x\),其均值
\(\bar x=k^{-1}\sum_i x_i\in I\)。因 \(x_i\in C_i\),有
\(\delta_i\le|x_i-\bar x|\)。令 \(y_i=x_i-c_{\min}\ge0\)、
\(s=\sum_i y_i=k(\bar x-c_{\min})\),则

\[
\begin{aligned}
V_0&\le\sum_i(x_i-\bar x)^2
=\sum_i y_i^2-\frac{s^2}{k}\\
&\le s^2-\frac{s^2}{k}
=k(k-1)(\bar x-c_{\min})^2 .
\end{aligned}
\]

中间不等式只用 \(2\sum_{i<l}y_i y_l\ge0\),不需要各个 \(y_i\) 严格正。
事实上某个 \(x_i=c_{\min}\) 时 \(y_i=0\) 完全允许。由
\(\bar x\le\mu\) 得
\(\rho\le\bar x-c_{\min}\le\mu-c_{\min}\),因此

\[
\boxed{H\ge L=\mu-\rho\ge c_{\min}\ge\log2>0.}
\]

这还给出 \(V_0<k(k-1)\mu^2\)。后面所有固定下预算的角点区间都保留实际角点,
故此证明逐点适用,包括 \(\rho=0\)、角点预算等于薄层端点和 \(b_i=0\)。

**26.5 二变量包络的严格性质。** 定义
\[
F(\mu,r)=f(\mu+(k-1)r)+(k-1)f(\mu-r),\qquad
\Omega=\{(\mu,r):r\ge0,\ \mu-r>0\}.
\]
这是凸定义域。对 \(x>0\),
\[
f'(x)=\frac1{e^x-1}>0,\qquad
f''(x)=-\frac{e^x}{(e^x-1)^2}<0.
\]
所以 \(F_\mu=f'(H)+(k-1)f'(L)>0\),
\(F_r=(k-1)(f'(H)-f'(L))\le0\),且 \(r>0\) 时后一式严格负。
固定 \(\mu\),任意 \(0\le r_1<r_2<\mu\) 之间积分仍给
\(F(\mu,r_2)<F(\mu,r_1)\),即使 \(r_1=0\),也不能把边界导数为零误作常值。
线性映射
\[
(\mu,r)\longmapsto(H,L)=(\mu+(k-1)r,\mu-r)
\]
的行列式为 \(-k\ne0\),因而单射。不同输入至少使 \(H,L\) 中一个不同;
对严格凹函数 \(f\) 的两个正权项应用 Jensen,即证 \(F\) 在 \(\Omega\) 上联合严格凹。

**26.6 下预算饱和及其精确等号。** 给定 \((M_0,u)\in\mathscr S\),令
\[
j=\max\{s:\beta_s\le u\},\qquad b=\beta_{j-1}.
\]
至少两个实际角点可行,故 \(j\ge1\),且第二大的可行角点给出
\(M_0\le b<\beta_j\le u\)。于是
\(B_{\rm cut}<b<u\),并且 \([b,u]\) 仍含 \(\beta_{j-1},\beta_j\)。
将 \(M_0\) 提至 \(b\) 只缩小均值区间,使所有非负距离弱增,
而 \(D(u),\mu\) 不变。26.5 的半径单调性给出
\[
\boxed{G(M_0,u)\le G(b,u).}
\]
其取等当且仅当
\[
V_0(M_0,u)=V_0(b,u)
\quad\Longleftrightarrow\quad
\delta_i(M_0,u)=\delta_i(b,u)\ \text{对每个 }i.
\]
后一等价用逐项非负且弱增;只要一项严格增加,平方和及半径严格增加,
\(\Psi\) 就严格下降。因此 \(M_0=b\) 是充分条件,不是取等的必要条件。

**26.7 距离的精确行公式与唯一凹折点。** 固定 \(b=\beta_{j-1}\)、\(a=b/k\),
令 \(\mu=u/k\ge a\),简记
\(\delta_i(\mu)=\operatorname{dist}([a,\mu],C_i)\)。
逐个取区间到两个点的较小距离,得到彼此兼容的公式
\[
\delta_i(\mu)=
\begin{cases}
a-d_i,&d_i\le a,\\
(c_i-\mu)_+,&a\le c_i,\\
\min\{a-c_i,(d_i-\mu)_+\},&c_i<a<d_i,
\end{cases}
\qquad t_+=\max(t,0).
\]
在中间几何情形 \(c_i<a<d_i\),若
\(a\ge(c_i+d_i)/2\),则 \((d_i-\mu)_+\le d_i-a\le a-c_i\),
整行就是 \((d_i-\mu)_+\)。若
\[
c_i<a<(c_i+d_i)/2,
\quad \mu_* = c_i+d_i-a>a,
\]
则精确分成
\[
\delta_i(\mu)=
\begin{cases}
a-c_i,&a\le\mu\le\mu_*,\\
(d_i-\mu)_+,&\mu\ge\mu_*.
\end{cases}
\]
唯一可能破坏凸性的向下斜率跳变是这个活跃最近端点切换
\(0\to-1\);其上预算为
\[
u_*=k\mu_*=k(c_i+d_i)-b.
\]
在 \(c_i,d_i\) 处的折点只可能是 \(-1\to0\),仍保持凸性。
\(a=c_i,a=d_i,a=(c_i+d_i)/2\) 都由上述兼容公式处理,
不产生额外的内部向下跳变。

**26.8 删除 \(kc_i,kd_i\) 分割点的理由。** 在没有活跃 \(\mu_*\) 位于内部的闭区间上,
每行距离都是非负凸函数:常数或正部仿射函数;若切换恰在端点,两式在该点相等。
因此允许跨越 \(c_i,d_i\) 的正部折点。对
\(\mu_t=t\mu_1+(1-t)\mu_2\)、\(0<t<1\),逐坐标有
\[
0\le\delta(\mu_t)\le t\delta(\mu_1)+(1-t)\delta(\mu_2).
\]
欧氏范数在非负正交象限逐坐标单调,再用三角不等式,得到
\[
\rho(\mu_t)=\frac{\|\delta(\mu_t)\|_2}{\sqrt{k(k-1)}}
\le t\rho(\mu_1)+(1-t)\rho(\mu_2).
\]
所以 \(\rho\) 在整个区间上凸。这里没有把通常凹的平方根直接与任意凸函数复合;
所用结构是“非负凸距离向量的欧氏范数”。

**26.9 包括零方差的严格 Jensen 证明。** 在 26.8 的区间上取不同的
\(\mu_1,\mu_2\),置 \(r_l=\rho(\mu_l)\)、
\(\bar r=tr_1+(1-t)r_2\)。26.4 给出
\[
\mu_t-\bar r
=t(\mu_1-r_1)+(1-t)(\mu_2-r_2)\ge c_{\min}>0,
\quad 0\le\rho(\mu_t)\le\bar r.
\]
实际点和插值点都在 \(\Omega\)。先用 \(F\) 对半径非增,
再对两个不同输入对用联合严格凹性,得
\[
\begin{aligned}
\Psi(b,k\mu_t)
&=F(\mu_t,\rho(\mu_t))\\
&\ge F(\mu_t,\bar r)\\
&>tF(\mu_1,r_1)+(1-t)F(\mu_2,r_2).
\end{aligned}
\]
不同均值保证输入对不同,即使两个半径都为零仍有严格步。
故 \(\Psi(b,u)\) 在这些非退化区间上严格凹。
这份证明不用 \(\rho'\) 或 \(\rho''\),没有在零方差处作未经许可的平方根微分。

**26.10 分数背包的匹配原始/价格证书。** 置 \(\sigma_i=v_i/h_i>0\),
选任意排列 \(\pi\) 使 \(\sigma_{\pi(1)}\ge\cdots\ge\sigma_{\pi(k)}\),
相等时任意固定次序。记
\[
q_m=A+\sum_{\ell=1}^m h_{\pi(\ell)},\qquad q_0=A.
\]
在 \(q_{m-1}\le u\le q_m\),取
\[
y_{\pi(\ell)}=
\begin{cases}
1,&\ell<m,\\
(u-q_{m-1})/h_{\pi(m)},&\ell=m,\\
0,&\ell>m.
\end{cases}
\]
它可行且 \(\sum_i h_i y_i=u-A\)。任意可行 \(y\) 和 \(\lambda\ge0\) 满足
\[
\sum_i y_i v_i
=\lambda\sum_i h_i y_i+\sum_i y_i(v_i-\lambda h_i)
\le\lambda(u-A)+\sum_i\max(0,v_i-\lambda h_i).
\]
对上列具体 \(y\),取 \(\lambda_*=\sigma_{\pi(m)}\),
前缀余值非负,后缀余值非正,第 \(m\) 项余值为零,
故所有不等式同时取等。这直接证明 26.3 的最大值和下确界均达到且相等,其值为
\[
\boxed{D(u)=\sum_i f(c_i)+\sum_{\ell<m}v_{\pi(\ell)}
+\sigma_{\pi(m)}(u-q_{m-1}).}
\]
排序是经典分数背包材料,本式的无间隙结论来自显式匹配证书,
没有先假定未证明的强对偶。

**26.11 并列斜率、整数最优解与角点间仿射性。** 若相邻 \(\sigma_i\) 相等,
26.10 的非严格余值符号仍成立,相邻公式拥有相同斜率且在共同端点相等,
故并列只消去折点,不会制造新折点。\(u=q_m\) 时可选整数最优解,
上一段的分数为 1、下一段的分数为 0,两式相同;
不要求所有最优解都是这种基本解。\(u=A\) 时全下端点最优,
任意 \(\lambda\ge\max_i\sigma_i\) 为证书。
若 \(u\ge A+Q=\beta_{N-1}\),全上端点 \(y_i=1\) 可行,
\(\lambda=0\) 与弱对偶匹配,故
\[
D(u)=\sum_i f(d_i).
\]
这包括预算恰饱和与有松弛两种情形。
每个 \(q_m\) 是实际前缀角点预算,属于 \(\{\beta_s\}\)。
所有可能斜率变化都在这些前缀角点,所以
\[
D\ \text{在每个闭区间 }[\beta_j,\beta_{j+1}]\text{ 上仿射}.
\]
其它实际角点即使不是排序前缀,也只是进一步划分同一条仿射线段。

**26.12 第一主推导的较大有限集仍有效。** 对 \(1\le j\le N-2\) 且
\(b=\beta_{j-1}>B_{\rm cut}\),定义
\[
\mathcal B_j=
\left(\{\beta_j,\beta_{j+1}\}\cup
\{kc_i,kd_i,k(c_i+d_i)-b:1\le i\le k\}\right)
\cap[\beta_j,\beta_{j+1}].
\]
第一主推导使用的 \(\mathcal K_{\rm broad}\) 由所有
\((b,u)\)、\(u\in\mathcal B_j\),以及通过 cutoff 的
\((\beta_{N-2},\beta_{N-1})\) 组成,按精确有序对去重。
26.7 的所有行斜率改变都在所列位置内;在相邻不同节点间距离向量仿射,
26.8-26.9 因而适用。结合 26.11,每段 \(G\) 严格凸,
由端点控制内部;最后一条上尾由 26.15 控制。
所列薄层都至少含 \(\beta_{j-1},\beta_j\),所以 admissibility 无缺口。
这证明较大集有效。下文的精化减少节点,不撤销第一主推导的结论。

**26.13 精化有限测试集。** 定义 \(\mathcal K_{\rm sharp}\) 为以下有序预算对之集合。
第一类保留所有通过 cutoff 的相邻实际角点对:
\[
(\beta_{s-1},\beta_s),\qquad
1\le s\le N-1,\quad \beta_{s-1}>B_{\rm cut}.
\]
第二类仅保留活跃且严格位于下一角点区间内部的反射点:
\[
(b,u_*),\quad b=\beta_{j-1},\ a=b/k,\ u_*=k(c_i+d_i)-b,
\]
\[
1\le j\le N-2,\quad 1\le i\le k,\quad
b>B_{\rm cut},\quad c_i<a<(c_i+d_i)/2,\quad
\beta_j<u_*<\beta_{j+1}.
\]
每个成员都可容许:第一类含其两个端角点,第二类含
\(\beta_{j-1},\beta_j\),宽度和 cutoff 均严格。
因此原始数量上界为
\[
|\mathcal K_{\rm sharp}|\le (N-1)+k(N-2).
\]
\(k=3,N=8\) 时为 \(7+6\cdot3=25\)。
25 是通过 guards 之前的每箱容量上界,不是每个箱体都留下 25 个节点的断言。

**26.14 分段严格凸性、外端点再饱和与有限支配。** 固定
\(1\le j\le N-2\)、\(b=\beta_{j-1}>B_{\rm cut}\)。
只用活跃反射点将 \([\beta_j,\beta_{j+1}]\) 划为有限个非退化闭线段。
每段 \([v,w]\) 上 \(D\) 仿射、\(\Psi(b,\cdot)\) 严格凹,
故 \(G(b,\cdot)\) 严格凸。对 \(v<u<w\),令
\(u=tv+(1-t)w\)、\(0<t<1\),则
\[
G(b,u)<tG(b,v)+(1-t)G(b,w)
\le\max\{G(b,v),G(b,w)\}.
\]
这是经典端点最大化在本函数上的严格形式,也表明内部点不可能成为全局最大者。
内部划分端点正是所保留的反射点;左外端点 \((b,\beta_j)\) 已是相邻对。
右外端点 \((b,\beta_{j+1})\) 可再将下预算提高至 \(\beta_j\):
两实际角点 \(\beta_j,\beta_{j+1}\) 保留,且
\(\beta_j>b>B_{\rm cut}\)。由 26.6,
\[
G(b,\beta_{j+1})\le G(\beta_j,\beta_{j+1}),
\]
取等恰为这次饱和的全部行距离不变。右侧已属第一类。
边界切换点不需另添非相邻对。因而每个饱和薄层在这一有限区间内,
都被 \(\mathcal K_{\rm sharp}\) 的一个成员弱支配。

**26.15 最大角点以后的严格递减上尾。** 当
\(j=N-1\),饱和下预算为 \(b=\beta_{N-2}\)。
对 \(u\ge\beta_{N-1}\),26.11 给出常值 \(D=\sum_i f(d_i)\)。
增加 \(\mu=u/k\) 扩大 \([b/k,\mu]\),故 \(\rho\) 非增。
若 \(\mu_2>\mu_1\)、半径为 \(\rho_2\le\rho_1\),则
\(\mu_2-\rho_1>\mu_1-\rho_1\ge c_{\min}\),所以比较中的中间点也在正域,并有
\[
F(\mu_2,\rho_2)\ge F(\mu_2,\rho_1)>F(\mu_1,\rho_1).
\]
因此 \(G(b,u)\) 在整个上尾严格递减,最后相邻对
\((\beta_{N-2},\beta_{N-1})\) 支配该尾。
结合下预算饱和与 26.14,得到本节的有限支配定理:
\[
\boxed{\forall s\in\mathscr S\ \exists v\in\mathcal K_{\rm sharp}:
G(s)\le G(v).}
\]

**26.16 非空性、达到的有限最大值及符号等价。** 存在可容许薄层当且仅当
\[
\boxed{\beta_{N-2}>B_{\rm cut}\quad\Longleftrightarrow\quad R_{N-2}>5040.}
\]
必要性来自 \(M_0\le\beta_{N-2}\),充分性取最后相邻对。
这也是 \(\mathcal K_{\rm sharp}\) 非空的充要条件。
非空时定义
\[
g_*=\max_{v\in\mathcal K_{\rm sharp}}G(v).
\]
有限集为 \(\mathscr S\) 的子集,而 26.15 支配整个 \(\mathscr S\),故
\[
\boxed{\max_{s\in\mathscr S}G(s)=g_*}
\]
并实际达到,尽管原域具有严格 cutoff 且上预算无界。
以下四组等价包括严格符号:
\[
\begin{array}{rcl}
(\forall s\in\mathscr S,\ G(s)\le0)&\Longleftrightarrow&
(\forall v\in\mathcal K_{\rm sharp},\ G(v)\le0),\\
(\forall s\in\mathscr S,\ G(s)<0)&\Longleftrightarrow&
(\forall v\in\mathcal K_{\rm sharp},\ G(v)<0),\\
(\exists s\in\mathscr S,\ G(s)>0)&\Longleftrightarrow&
(\exists v\in\mathcal K_{\rm sharp},\ G(v)>0),\\
(\exists s\in\mathscr S,\ G(s)\ge0)&\Longleftrightarrow&
(\exists v\in\mathcal K_{\rm sharp},\ G(v)\ge0).
\end{array}
\]
证明的一向用有限集包含关系,另一向用支配;严格全负一向还用有限最大值严格负。
若有限集非空且全部测试负,则 \(\eta=-g_*>0\) 给出
\(G(s)\le-\eta\) 对该固定箱体的所有实薄层成立。
不声称 \(\eta\) 跨不同素数/指数箱体统一。
若集合为空,上述全称式为空真、存在式为假,\(g_*\) 不定义,不声称存在达到的最大值。

**26.17 最大者、饱和等号和零薄层的准确分类。** 以下假设 \(\mathscr S\ne\varnothing\)。
对任意 \((M_0,u)\in\mathscr S\),重新按实际 \(u\) 定义
\(j=\max\{s:\beta_s\le u\}\)、\(b=\beta_{j-1}\)。则
\[
\boxed{G(M_0,u)=g_*\ \Longleftrightarrow\
\bigl[V_0(M_0,u)=V_0(b,u)\bigr]\ \land\
\bigl[(b,u)\in\mathcal K_{\rm sharp},\ G(b,u)=g_*\bigr].}
\]
必要性先由 26.6 得饱和取等。若 \(u>\beta_{N-1}\),严格上尾排除最大;
若 \(\beta_j<u<\beta_{j+1}\) 且不是活跃反射点,
26.14 的严格内部不等式排除最大。剩下 \(u=\beta_j\) 时,
使用这个实际 \(j\) 饱和,得到的正是相邻对。
故不会把上一段右端点处尚未再饱和的非相邻对误列为最大者。
充分性由饱和等号立即得到。等号允许 \(M_0<b\),但必须逐行距离不变。

若全部测试差非正,则零薄层恰是 \(g_*=0\) 时上列最大者;
此条件下存在零薄层当且仅当存在零测试节点。
撤掉全局非正假设,正确的存在性结论是
\[
\boxed{\exists s\in\mathscr S:\ G(s)=0\quad\Longleftrightarrow\quad g_*\ge0.}
\]
必要性由最大值给出。\(g_*=0\) 时取达到点。
若 \(g_*>0\),从一个正测试节点固定其下端点 \(b\),让上预算连续增加。
可容许性始终保持;距离因区间扩大而有界,\(\rho\) 有界,
故 \(L,H\to\infty\)、\(\Psi\to0\),而 \(D\) 最终恒等于
\(\sum_i f(d_i)<0\)。\(G\) 连续,由介值定理在有限上预算处过零。
因此正节点存在时,零测试节点本身不分类全部零薄层,
也不能把最大者的临界上端点条件强加给全部零点。
本节没有最小值或下界的有限归约。

**26.18 精确整数 guards 与预算端点。** 相邻对满足
\[
e^{T_0}=R_{s-1},\qquad e^{T_1}=R_s.
\]
反射对令
\[
X=PR_{j-1},\qquad E_i=p_i^{\,k(2b_i+3)}.
\]
由 \(b=\log X\)、\(u_*=k(c_i+d_i)-b\) 及 \(T_1=u_*-Q\),
精确得到
\[
e^{u_*}=\frac{E_i}{PR_{j-1}},\qquad
\boxed{e^{T_1}=\frac{p_i^{\,k(2b_i+3)}}{P^2R_{j-1}}},\qquad
e^{T_0}=R_{j-1}.
\]
指数函数严格递增,各因子为正,故反射点全部条件等价于下列纯整数比较:
\[
\boxed{\begin{gathered}
R_{j-1}>5040,\qquad p_i^{\,k(b_i+1)}<X,\qquad X^2<E_i,\\
P^2R_{j-1}R_j<E_i<P^2R_{j-1}R_{j+1}.
\end{gathered}}
\]
第二式来自 \(kc_i<b\),第三式来自 \(2b<k(c_i+d_i)\),
末行来自 \(\beta_j<u_*<\beta_{j+1}\)。
因此 eligibility、cutoff 和端点顺序不用浮点对数判断。
较大集中的额外端点也有精确形式
\(e^{kc_i-Q}=p_i^{k(b_i+1)}/P\)、
\(e^{kd_i-Q}=p_i^{k(b_i+2)}/P\),但精化集已不需要它们。
这些有理端点没有使 \(D,\rho,\Psi,G\) 变成有理数,也没有决定 \(G\) 的符号。

**26.19 反射上端点恒非整数与无重复对。** 反射 \(e^{T_1}\) 中素数 \(p_l\) 的指数为
\[
k(2b_i+3)\mathbf1_{\{l=i\}}-b_l-e_l^{(j-1)}-2.
\]
每个 \(l\ne i\) 的指数均为 \(-(b_l+e_l^{(j-1)}+2)\le-2\)。
因 \(k\ge2\),这样的素数存在,且分子只有 \(p_i\) 的幂,唯一分解禁止约消它。
因此反射 \(e^{T_1}\) 总是正的非整数有理数,包括每个通过 guards 的反射槽。
\(p_i\) 自己的指数为
\((2k-1)b_i+3k-e_i^{(j-1)}-2>0\)。
故反射上端点不能等于任一实际角点上端点。
不同下角点的反射对第一坐标不同;固定下角点,两行反射相等将迫使
\(p_i^{k(2b_i+3)}=p_l^{k(2b_l+3)}\),对不同素数不可能。
相邻对的下角点也互异,故同一固定素数箱体内没有幸存的重复预算对。
26.13 可直接作为集合使用,无需靠数值容差去重。

**26.20 常量角点次序证书。** PRO 选定的前瞻 \(k=3\) 范围使用素数列表
\([2,3,5,7,11,13,17,19]\),按列表指标递增的三元组取字典序,
共 \(\binom83=56\) 个。此处为槽布局将坐标改标 \(i=0,1,2\),
bit \(i\) 选择第 \(i\) 坐标的上端点,bit 0 是最低位。
对 \(p_0<p_1<p_2\),八个子集乘积的唯一未定比较是 \(p_2\) 与 \(p_0p_1\):
二者都大于 \(p_1\)、小于 \(p_0p_2\),且
\(p_0p_2<p_1p_2<p_0p_1p_2\),相等由唯一分解排除。因此
\[
\text{sorted masks}=
\begin{cases}
[0,1,2,4,3,5,6,7],&p_2<p_0p_1,\\
[0,1,2,3,4,5,6,7],&p_2>p_0p_1.
\end{cases}
\]
设常量子集乘积为 \(m_s=\prod_i p_i^{e_i^{(s)}}\),
任意指数箱体均有 \(R_s=B m_s\)、\(B=\prod_i p_i^{b_i}>0\)。
故这 56 个常量次序同时适用于全部指数,无须枚举指数箱体来验证次序。
[prime-slab-corner-order-0909.json](../../reports/prime-slab-corner-order-0909.json)
是给定输入的原样 6741 字节,SHA256
9d28055d5255580ed58274822359961483d1deecbb7b4e38ce497948a4808672。
它保存每个 triple、八个 mask 和严格递增的整数乘积,是常量输入证书而非搜索结果;
[prime-slab-finite-design-0909.md](../../reports/prime-slab-finite-design-0909.md)
给出逐行可复现的标准库 Python 检查。

**26.21 前瞻箱体、槽和稳定行号。** 对每个三元组独立取
\(b_0,b_1,b_2\in\{0,\ldots,15\}\)。三元组指标 \(0\le t<56\),定义
\[
\mathrm{box\_id}=4096t+256b_0+16b_1+b_2.
\]
这是混合进制编码,每个三元组有 \(16^3=4096\) 个不同箱体,
共 \(56\cdot4096=229376\) 个,box_id 从 0 到 229375。
每箱预留 25 个原始槽:
\[
\begin{array}{c|c|c}
\mathrm{slot}&\text{指标}&\text{预算对}\\\hline
0,\ldots,6&s=\mathrm{slot}+1&(\beta_{s-1},\beta_s)\\
7,\ldots,24&r=\mathrm{slot}-7,\ j=1+\lfloor r/3\rfloor,\ i=r\bmod3&
(\beta_{j-1},\,3(c_i+d_i)-\beta_{j-1})
\end{array}
\]
第一类只施加相邻 cutoff;第二类施加 26.18 的全部严格整数 guards。
定义
\[
\mathrm{row\_id}=25\,\mathrm{box\_id}+\mathrm{slot},
\qquad 0\le\mathrm{row\_id}\le5734399.
\]
批次、压缩和调度必须保留此含箱体身份的行号。
计数仅由布局乘法给出:
\[
\begin{aligned}
\text{相邻原始槽}&=229376\cdot7=1605632,\\
\text{反射原始槽}&=229376\cdot(6\cdot3)=4128768,\\
\text{原始槽合计}&=229376\cdot25=5734400.
\end{aligned}
\]
这些全是 guards 前的 RAW slots,没有统计幸存槽。
本次常量检查只遍历 56 个输入行,没有生成上述 229376 个指数箱体,
也没有执行这些 row_id 的解析差值计算。

**26.22 guards 的整数位宽与 carry 设计界。** 在 26.21 的范围内,
\(R_s\) 的每个素数指数至多 16,\(PR_s\) 至多 17,
\(P^2R_sR_l\) 和 \((PR_s)^2\) 每个素数指数至多 34。
\(E_i=p_i^{3(2b_i+3)}\) 的单素数指数至多 99,
\(p_i^{3(b_i+1)}\) 至多 48。因此每个 guard 操作数都至多
\[
19^{102}<2^{510}<2^{512};
\]
前一个严格不等式也直接由 \(19<2^5\) 得到。
前瞻表示可取 64 个 base-256 limbs,每 limb 放在 32 位整数 lane,
从 1 起至多作 102 次“小素数乘法加 carry”,比较时从最高 limb 向下。
若乘数 \(p\le19\)、旧 limb \(d\le255\)、输入 carry \(c\le p-1\),
则
\[
dp+c\le255p+(p-1)\le255\cdot19+18=4863,\qquad
\left\lfloor\frac{dp+c}{256}\right\rfloor\le p-1\le18.
\]
初始 carry 为 0,故归纳保持该界;512 位也容纳全部最终操作数。
这是整数表示的数学设计界,不是已验证的 MPS 指令、存储或 carry 行为。
常量证书检查可精确核对 \(19^{102}\) 的 bit_length 为 434,
该更小实测位数不改变预留 64 limbs 的设计。

**26.23 六个可行排列混合给出精确 \(D\)。** 仅在本条及以下级数设计取 \(k=3\)。
对六个排列 \(\pi\in S_3\) 的每一个,令 \(t=u-A\ge0\),
\[
y^\pi_{\pi(\ell)}
=\min\left\{1,\max\left\{0,
\frac{t-\sum_{m<\ell}h_{\pi(m)}}{h_{\pi(\ell)}}\right\}\right\},
\quad 1\le\ell\le3,
\]
\[
D_\pi(u)=\sum_i\left((1-y^\pi_i)f(c_i)+y^\pi_i f(d_i)\right).
\]
沿该排列依次填满,最多一行部分填充,其余为零;
故 \(\sum_i h_i y^\pi_i=\min(t,Q)\le t\),每个 \(D_\pi\) 都是可行原始目标。
由弱对偶 \(D_\pi\le D\),而六个排列中必有一个按 \(\sigma_i\) 非增排列,
26.10-26.11 给出它的匹配最优证书。因此
\[
\boxed{D(u)=\max_{\pi\in S_3}D_\pi(u).}
\]
这避免先用未认证的浮点斜率决定最优排列。
并列斜率、整数最优解、预算前缀端点及全上端点饱和都包括在内;
六个值不必互异,后续仍须严格包围每个 fraction、clip 和最大值运算。

**26.24 正质量总和为 3 的绝对收敛对数级数。** 任一上条混合
(特别是某个最优混合)可写成
\[
D_\pi=\sum_r w_r f(z_r),\qquad w_r>0,\quad \sum_r w_r=3,\quad z_r\in\{c_i,d_i\}.
\]
从每行的两个质量 \(1-y_i^\pi,y_i^\pi\) 删去零质量即可。
整数最优解每行留下一个质量 1,总质量仍为 3。
选经认证的共同下界
\[
\log2\le\ell\le\min\bigl(\{z_r:w_r>0\}\cup\{L,H\}\bigr).
\]
26.4 保证数学上总可取 \(\ell=c_{\min}\),也总可取 \(\ell=\log2\);
不同排列可以共用此下界。对 \(x>0\),几何级数积分给出
\[
f(x)=-\sum_{n=1}^{\infty}\frac{e^{-nx}}n .
\]
因 \(0<e^{-x}<1\),该级数绝对收敛;有限个正质量项可逐项相加。
于是
\[
Z_\pi=e^\ell(D_\pi-\Psi)
=\sum_{n=1}^{\infty}\frac{e^\ell}{n}
\left(e^{-nH}+2e^{-nL}-\sum_r w_r e^{-nz_r}\right).
\]
对最优混合即为 \(Z=e^\ell G\)。没有要求最优混合真正分数,
也没有附加混合均值等于 \(\mu\) 的前提。

**26.25 缩放后 24 项尾界与取最大值的稳定性。** 记 26.24 的前 24 项为 \(S_{\pi,24}\)。
由全部自变量至少为 \(\ell\) 及正质量总和为 3,
\[
\left|e^{-nH}+2e^{-nL}-\sum_r w_r e^{-nz_r}\right|
\le6e^{-n\ell}.
\]
所以
\[
\begin{aligned}
|Z_\pi-S_{\pi,24}|
&\le6e^\ell\sum_{n=25}^{\infty}\frac{e^{-n\ell}}n\\
&\le\frac{6e^\ell}{25}\frac{e^{-25\ell}}{1-e^{-\ell}}
=\tau(\ell):=\frac{6e^{-24\ell}}{25(1-e^{-\ell})}\\
&\le\frac{6\cdot2^{-23}}{25}
=\boxed{\frac3{104857600}}.
\end{aligned}
\]
最后一步使用 \(e^{-\ell}\le1/2\),乘法 \(6\cdot2^{-23}\) 明列,
不是把连写字符串解释为 \(62\) 的幂。
若用最优混合的 24 项和 \(S\),便直接有 \(|Z-S|\le\tau(\ell)\)。
若不先选最优排列,置 \(S=\max_\pi S_{\pi,24}\),
由每个排列都满足
\(S_{\pi,24}-\tau\le Z_\pi\le S_{\pi,24}+\tau\),
逐项取最大值得
\[
\boxed{|Z-S|\le\tau(\ell),\qquad Z=\max_\pi Z_\pi=e^\ell G.}
\]
因此同一个统一尾界穿过六排列最大值,无需已认证的斜率选择。
总质量与定义域保证其覆盖零质量删去、整数最优解、并列斜率和全上端点。

**26.26 区间符号、等号和未决。** 因 \(e^\ell>0\),\(Z\) 与 \(G\) 同号。
对精确的 \(S\) 和有效尾界 \(\tau\),
\[
\begin{array}{c|c}
S+\tau<0&G<0\\
S+\tau\le0&G\le0\\
S-\tau>0&G>0\\
S-\tau\ge0&G\ge0
\end{array}
\]
是四个不同的充分认证规则。
若实际计算给出向外包围 \(S_-\le S\le S_+\) 和
\(\tau_+\ge\tau\),则使用
\[
\mathcal I_Z=[S_--\tau_+,\,S_++\tau_+].
\]
上端点严格负才证严格负,下端点严格正才证严格正;
上端点为零只支持非正,下端点为零只支持非负。
单侧接触零不证明等号;横跨零的区间保持 unresolved。
若严格包围恰为单点 \(\{0\}\),才由双侧界推出零,
也可另以精确恒等式证明等号。
六排列和分别有包围时,取各下界与各上界的最大值包围 \(S\),再加统一尾界。
不能把未认证的 float32 部分和加上尾界就称作符号证书。

**26.27 截断之外的数值义务。** 26.25 只界定省略 \(n\ge25\) 项的误差。
未来实际 MPS 程序还须给出向外误差包围,或由 CPU 对已完成 GPU 输出作严格验证,
涵盖输入 \(\log p_i\)、角点和反射预算、\(a,\mu,\ell\);
距离中的 min/max、减法、平方和、平方根及 \(L,H\);
混合 fraction、0/1 clipping、六排列最大值;
乘除、消去、求和次序、reduction、融合运算和实际 roundoff;
下溢、subnormal 或 flush-to-zero 丢项;以及实际 log、exp、log1p 和平方根的误差。
在反射点处最近距离精确并列,浮点分支不能自行取消这种等号。
数学上的总质量 3 不是舍入质量和的自动保证。
直接算 \(e^{\ell-nz}\) 可避免先形成大 \(e^\ell\) 因子,仍须包围下溢与抵消。

每个原始 row_id 将来都须保留 active/inactive 及精确 guard 证据,
每个 active 行须有认证分类或 unresolved,完整结论还须验证 GPU 非候选和所有必要排除,
保留 GPU/CPU 分歧及完整分类摘要。CPU 可以认证已完成的 GPU 结果,
不能变成持续指数箱体候选生成器或 GPU 计算的 fallback kernel。
同一批次的域、输入/程序身份、范围、计数、未决项和复现命令必须随程序持久化;
运行 checkpoint 留在仓外。这里没有实现或执行这些数值步骤。

**26.28 经典材料归属及核对范围。** 本节专门化组合标为 repo-derived,
以下只归属实际用到的经典材料,不是这个素数差值定理的既有文献证明或穷尽新颖性调查。
HKUST [Lecture 14: Greedy Algorithms](https://home.cse.ust.hk/~dekai/271/notes/L14/L14.pdf)
slides 4-7 给出按 value/weight 递减的分数背包、至多最后一项部分选取及其正确性;
本节自行给出匹配价格、并列和端点证明。
Boyd/Vandenberghe [Convex functions](https://web.stanford.edu/class/ee364a/lectures/functions.pdf)
slides 3.4、3.14、3.24、3.25 分别支持范数凸性、Jensen 和受单调性控制的复合规则;
本节自行验证非负象限、插值正定义域、单射导致的严格性及零方差边界。
Doikov [Convex Functions](https://doikov.com/teaching/orie6365-s26/notes/lecture05_convex.pdf)
§5.1.3 Theorem 5.1.4 给出任意仿射扰动后的线段端点最大化,
取扰动系数为零得到这里的经典端点材料;本节的严格内部排除另由 26.14 证明。
caller 核对位置分别为 HKUST PDF pp.4-7、Boyd/Vandenberghe PDF pp.6,16,26,27、
Doikov 陈述 p.2 / 证明 p.3。I9 读取的是获准的核对 receipt 及文字摘录,
没有把 primary 无法访问仓库 URL 改写成已独立读 GitHub。

**26.29 当前调用的不可变来源事实。** 第一 primary task 为
ce312694-86a6-4a1b-8318-90c77dc28f75,conversation conv_264064eff69b5335,
实际完成模型 GPT-6 Astra,完成于 2026-09-09T13:25:33.673+00:00;
其 pro-real-slab-reduction-envelope-0909.json 的 SHA256 为
5f551e3062515163f220d7fce433908598f5147c5060d92e56ba1292e03ec77a。
第二 primary task 为 3609e6b0-ab4d-4891-9b0f-55c613d43942,
conversation conv_4c0b62a5e14b0f64,实际完成模型 GPT-6 Astra,
完成于 2026-09-09T13:47:33.577+00:00;
其 pro-real-slab-sharpening-envelope-0909.json 的 SHA256 为
8105875c946f2c693c8db6a6b1f789756aab75fbd4cd297293431f08f25dcc92。
两份完成记录分别绑定这些 envelope 身份;两次调用都未成功获取钉版仓库 URL,
使用完整的供给定义,caller 已将定义与交付源核对。
这两份顺序主输入不构成两票独立批准,也不证明模型族多样性或 sterile priors。

本实施为 caller 的 consensus-rnd:sshx 编排下的 Codex CLI I9,
repo-prior-exposed;未产生子 agent、额外 oracle 或独立 review 票。
只消费给定 conclusion、完成元数据及列明的 caller 数学/文献/常量/gate 输入,
不追读 log_ref、不消费 peer review 工件。
上述输入位于 caller 的 /tmp/qgh-boundaries-0908/;其完整字节身份见设计报告和实施信封。
较早恢复但 hash 不匹配的 GPU manifest 是历史,不属于本节输入。
本节用明确乘法核对 \(7+6\cdot3=25\)、
\(6\cdot2^{-23}/25=3/104857600\)、\(255\cdot19+18=4863\),
没有采用 primary 中压缩的乘法串。

**26.30 摄入、派发事实和剩余义务。** 本次指定树为
/Users/auricstudio/trureturing-qgh-variance,分支
lane/math/quantized-gh-real-slabs-0909,封存输入和 canonical ingest BASE 为
0ba660de65b4224b8734908f7d0dd178115fa377。
追加前源为 2410 行、144029 字节,SHA256
b9898b7df94a1d46bb2898a738b27f927b6136ea1eb7db240fafc428f84bbe36,
Git blob 41c4487989f5739f80e4098cd91a8b229f870891;完整前缀逐字节保留。
新增源段、常量输入文件和设计报告之外,只由下列 canonical 命令产生 CAS/消化条目:

~~~sh
make ingest BASE=0ba660de65b4224b8734908f7d0dd178115fa377 SOURCE=arithmetic-boundary-quantization
~~~

新条目属于参考输入的 residual-open,不表示 Lean 吸收或冻结。
本节每个实质内容单元均编号;新增 CAS/entry 身份、源覆盖和实际命令退出码
由本次 implementation envelope 给出。旧 18 行散文覆盖 advisory 及 generator 所有的
LF/EOF 变体均是历史,本次不重写、不手工规范化。
caller gate 所给派发事实为 S12 PR #6640 已 MERGED,
S13 的 sealed prefix 在派发时独立评审 pending;这里保留它的全部源字节,
不读取或改动其活跃评审工作树。这是此调用的 provenance,不改写第 25 节当时的状态记录。

本次执行的有界输入核验只有 56 个常量行及计数/位宽/carry/尾常数,
指数箱体执行数为 0、解析测试行执行数为 0,没有候选实验或 exponent sweep。
全素数、全非负指数、任意 \(k\ge3\) 的比较和 RH 均保持 OPEN。
下一数值义务是按另行登记的 MPS 窗口实现并认证所有必要分类,
本节不声称已有 GPU kernel、GPU 搜索、持续 CPU 候选生成、一般域符号结论、
新 formal root、axiom 或 Lean freeze。
S14 的独立数学评审、普通仓库门与 MERGED 尚属 caller 后续义务,
最终交付依赖 S13 MERGED;Git/PR 动作不属于 I9。
这次有限源追加不完成持续研究目标。

## 27. 坐标分离的全薄层严格排除与正整数射线边界

**27.1 本次命题、来源和追加边界。** 本节为 2026-09-09 的 S16 参考输入,
分类为 PAPER_ARGUMENT / repo-derived,承接已完成的实际 GPT PRO primary
task a9d1269e-64ae-4a9a-b90f-8982ff023ee6,conversation conv_224b6f5d1adc6409,
观测模型 GPT-6 Astra,完成于 2026-09-09T14:39:45.418+00:00。
第 26 节已有实际角点给出的正定义域、分数背包对偶和固定箱体的有限薄层归约;
这里复用这些事实,新增下包络端点的逐坐标单调性、无步宽损失的箱体下界、
两个严格排除阈值、三坐标整数 guard 和固定正整数方向的最终排除。
本地对照范围是本卷第 1-26 节,没有作全库或文献的穷尽新颖性断言。
GH 仍是用户的原标签;RH 等价判据只是工作背景,没有新增 GH 定义或 RH 结论。

本次 implementation-input HEAD / ingestion BASE 是
391f7355698085c6500b46838a093dad05947ffb,不是尚待 caller 形成的 review-candidate HEAD。
第 1-26 节的完整 176107 字节 / 3134 行前缀保持不变,SHA256 为
4bbc7e0bbcd387c52a73d362ab78b61d00faf810d45d58df98b426e6fc34a266。
既有 atoms、entries、报告和常量表均保留。独立评审、仓库门与 MERGED 尚未由本节取得;
最终 S16 交付还依赖 S14 MERGED。本节不含另行在研的 relative-spread PRO 问题。

**27.2 较弱分析域与原可容许域。** 全部对数均为自然对数。
先取整数 \(k\ge2\) 和有限正二点网格
\[
0<c_i<d_i<\infty,\qquad h_i=d_i-c_i>0,\qquad C_i=\{c_i,d_i\},
\qquad A=\sum_i c_i.
\]
本节所需的分析薄层域 \(\mathscr S_+\) 只要求有限实预算
\(M_0\le M_1\),且至少有一个**实际角点**
\(x\in\prod_i C_i\) 满足 \(M_0\le\sum_i x_i\le M_1\)。
角点可在任一端点,也允许 \(M_0=M_1\)。混合权重非整数的点不能冒充该实际角点。
存在角点保证 \(M_1\ge A>0\),但无需假定 \(M_0>0\)。没有实际角点时,
下面从角点推出 \(L\ge\ell(c)\) 的薄层应用不作断言。

原素数域另要求两两不同的素数 \(p_i\)、整数 \(b_i\ge0\),并置
\[
h_i=\log p_i,\quad c_i=(b_i+1)h_i,\quad d_i=(b_i+2)h_i,
\quad Q=\sum_i h_i,\quad T_j=M_j-Q.
\]
实际指数是 \(b_i+e_i\ge0\),其中 \(e_i\in\{0,1\}\);
平移坐标中的素数幂指数 \(b_i+1\)、\(b_i+2\) 则严格正。
原可容许域 \(\mathscr S\) 保留
\[
Q+\log5040<M_0<M_1<\infty
\quad\Longleftrightarrow\quad \log5040<T_0<T_1<\infty,
\]
以及闭薄层内至少两个不同实际角点的要求。因此 \(\mathscr S\subseteq\mathscr S_+\)。
严格宽度、两个角点和 5040 cutoff 不用于排除证明,但匹配原问题时不可撤掉。

**27.3 同一目标与欧氏归一化。** 在 27.2 的分析域中定义
\[
f(z)=\log(1-e^{-z})\quad(z>0),\qquad
D(M_1)=\max_{\substack{0\le y_i\le1\\\sum_i h_i y_i\le M_1-A}}
\sum_i\bigl((1-y_i)f(c_i)+y_i f(d_i)\bigr).
\]
可行域是非空紧集,目标有限连续。它也等于
\[
\inf_{\lambda\ge0}\left\{\lambda M_1+
\sum_i\max_{z\in C_i}\bigl(f(z)-\lambda z\bigr)\right\}.
\]
这是 26.10-26.11 的同一匹配原始/价格证书:那些证明只用 \(h_i>0\)、
\(f(d_i)-f(c_i)>0\) 和 \(M_1\ge A\),故逐字适用于本分析域,
包括并列价格、端点饱和及上预算松弛。
继续置
\[
I=[M_0/k,M_1/k],\quad \mu=M_1/k,\quad
\delta_i=\operatorname{dist}(I,C_i),\quad V_0=\sum_i\delta_i^2,
\]
\[
\rho=\sqrt{\frac{V_0}{k(k-1)}},\quad L=\mu-\rho,\quad
H=\mu+(k-1)\rho,\quad \Psi=f(H)+(k-1)f(L),\quad G=D-\Psi.
\]
27.5 将先保证 \(L,H>0\),然后才使用 \(f(L),f(H)\)。
\(V_0\) 没有额外除以 \(k\)。在素数域仍有
\(G=U_{\rm dual}-U_{\rm var}\),共同常数 \(\log E_S\) 精确抵消。
对所有 \(x\in\mathbb R^k\),在通常欧氏内积下定义
\[
\bar x=\frac1k\sum_i x_i,\qquad
\Pi=\operatorname{Id}-\frac1k\mathbf1\mathbf1^{\mathsf T},\qquad
\ell(x)=\bar x-\frac{\|\Pi x\|_2}{\sqrt{k(k-1)}}.
\]
这是同一平方偏差几何;给素数贴坐标标签本身没有证明新的正交关系。

**27.4 定理 A:全 \(\mathbb R^k\) 的单调性及精确增量等号。** 对任意
\(x\in\mathbb R^k\)、坐标 \(i\)、实数 \(u\ge0\),有
\[
\boxed{\ell(x+u e_i)\ge\ell(x).}
\]
\(u=0\) 时恒等;\(u>0\) 时取等当且仅当
\[
\Pi x=\lambda\Pi e_i\quad\text{对某个 }\lambda\ge0
\quad\Longleftrightarrow\quad x=a\mathbf1+\lambda e_i
\quad\text{对某个 }a\in\mathbb R,\ \lambda\ge0.
\]
这里 \(a\) 是自由平移量,不必是 \(\bar x\)。

证明。直接计算
\[
\|\Pi e_i\|_2^2=(1-1/k)^2+(k-1)/k^2=(k-1)/k,
\qquad \frac{\|\Pi e_i\|_2}{\sqrt{k(k-1)}}=1/k.
\]
为使所用范数论证自足,对 \(w\ne0\) 将
\(\|v-tw\|_2^2\ge0\) 取 \(t=\langle v,w\rangle/\|w\|_2^2\),
得到 Cauchy-Schwarz;继而
\[
\|v+w\|_2^2=\|v\|_2^2+2\langle v,w\rangle+\|w\|_2^2
\le(\|v\|_2+\|w\|_2)^2.
\]
两边非负,开方即三角不等式。\(w\ne0\) 时取等恰要求
\(v=\lambda w\)、\(\lambda\ge0\),包括 \(v=0\)。
用于 \(v=\Pi x,w=u\Pi e_i\),均值增加量 \(u/k\) 恰抵消范数增长上界,
所以
\[
\ell(x+u e_i)-\ell(x)
=\frac uk-\frac{\|\Pi x+u\Pi e_i\|_2-\|\Pi x\|_2}{\sqrt{k(k-1)}}\ge0.
\]
\(u>0\) 时 \(w\ne0\),三角等号给出所述非负共线条件;
再用 \(\ker\Pi=\mathbb R\mathbf1\) 得等价表示。
逐个增加坐标即证 \(x\le x'\Rightarrow\ell(x)\le\ell(x')\)。
因此是非减而非每个方向严格增加,零方差 \(\Pi x=0\) 也在等号内。
这一定理自身不需要正性、素性或互异性。证毕。

**27.5 一个实际角点足以给出箱体下界。** 记
\(E=\ell(c)\)、\(c_{\min}=\min_i c_i\)。对 27.2 中任一实际可行角点 \(x\),
\(\bar x\in I\)、\(\mu\ge\bar x\),故逐项
\(0\le\delta_i\le|x_i-\bar x|\)。于是
\[
\rho\le\frac{\|\Pi x\|_2}{\sqrt{k(k-1)}},\qquad
L\ge\ell(x)\ge\ell(c)=E\ge\ell(c_{\min}\mathbf1)=c_{\min}>0.
\]
第二、三步用 27.4,因为 \(x\ge c\ge c_{\min}\mathbf1\)。这证明
\[
\boxed{H\ge L\ge E\ge c_{\min}>0;}
\]
素数域还给 \(c_{\min}\ge\log2\)。没有 \(\max h_i\) 或其它步宽罚项。
对该固定角点,\(L=\ell(x)\) 当且仅当
\(\mu=\bar x\) 且全部 \(\delta_i=|x_i-\bar x|\),因为两项非负差之和为零。
故 \(L=E\) 恰要求再有 \(\ell(x)=\ell(c)\);
后者可沿实际增加的坐标逐次用 27.4 的等号条件判定,不强称严格。

另有 \(E=c_{\min}\) 当且仅当 \(c\) 至多一个坐标严格高于 \(c_{\min}\):
令 \(z_i=c_i-c_{\min}\ge0\)、\(s=\sum_i z_i\),则
\(\|\Pi c\|_2^2=\sum_i z_i^2-s^2/k\le(k-1)s^2/k\);
取等恰为 \(\sum_{i<j}z_i z_j=0\)。这包含 \(s=0\)。
\(H=L\) 当且仅当 \(\rho=0\),等价于 \(V_0=0\),又等价于每行距离为零。
此时 \(\Psi=kf(\mu)\),所有论证仍成立;本节不在零方差处微分平方根。证毕。

**27.6 定理 B:初等阈值的严格排除。** 令
\[
d=\min_i d_i>0,\qquad S_d=\sum_i f(d_i)<0.
\]
若 \(E\ge d+\log k\),则每个 \((M_0,M_1)\in\mathscr S_+\) 均有 \(G<0\),
包括阈值等号 \(E=d+\log k\)。因此结论也对原可容许域 \(\mathscr S\) 全称成立。

证明。\(f'(z)=1/(e^z-1)>0\),且有限正 \(z\) 给 \(f(z)<0\)。
每个坐标混合不超过 \(f(d_i)\),所以 \(D\le S_d\)。选 \(d_j=d\),
其余 \(k-1\ge1\) 项严格负,故 \(S_d<f(d)\)。
另一方面 27.5 和 \(H-L=k\rho\ge0\) 给
\[
\Psi\ge kf(L)\ge kf(E).
\]
置 \(z=e^{-E},q=e^{-d}\)。假设给 \(q\ge kz\),且 \(0<kz\le q<1\)。
以下有限恒等式直接给严格 Bernoulli 步:
\[
1-(1-z)^k=z\sum_{j=0}^{k-1}(1-z)^j<kz,
\]
因为 \(0<z<1\)、第一个求和项为 1、其余 \(k-1\) 项均小于 1。
所以 \(0<1-q\le1-kz<(1-z)^k\),对正量取对数得到
\(f(d)<kf(E)\)。合并为
\[
\boxed{D\le S_d<f(d)<kf(E)\le\Psi,\qquad G<0.}
\]
在 \(q=kz\) 时 Bernoulli 严格步不消失。
这里 \(D=S_d\) 恰当 \(M_1\ge\sum_i d_i\):取全上端点充分,
反向则由每个增益严格正知取到 \(S_d\) 必须全部 \(y_i=1\)。
\(\Psi=kf(L)\) 恰当 \(V_0=0\),\(kf(L)=kf(E)\) 恰当 \(L=E\);
这些可能等号均不会抵消中间的严格性。证毕。

**27.7 更尖锐的标量阈值及箱体负裕量。** 对有限 \(d>0\) 定义精确实数
\[
\boxed{T_k(d)=-\log\!\left(1-(1-e^{-d})^{1/k}\right).}
\]
根号内的 \(1-e^{-d}\) 严格在 \((0,1)\),外层对数的自变量也严格在 \((0,1)\),
所以 \(T_k(d)\) 有限且正。定义直接给
\(kf(T_k(d))=f(d)\)。因此较弱条件 \(E\ge T_k(d)\) 已足以给
\[
D\le S_d<f(d)\le kf(E)\le\Psi,\qquad G<0.
\]
在 \(E=T_k(d)\) 时标量比较取等,严格性由其它上端点的负项
\(S_d<f(d)\) 保证,不需排除零方差。

令 \(a=(1-e^{-d})^{1/k}\in(0,1)\),由
\(e^{-d}=1-a^k=(1-a)\sum_{j=0}^{k-1}a^j\) 得
\[
T_k(d)=d+\log\!\left(\sum_{j=0}^{k-1}a^j\right),
\qquad \boxed{d<T_k(d)<d+\log k}.
\]
两端都严格,因为 \(1<\sum a^j<k\)。在任一充分阈值下定义
\[
\boxed{\varepsilon_{\rm box}=kf(E)-S_d>0.}
\]
它只依赖该固定箱体,所有 \(\mathscr S_+\) 中的薄层满足
\(G\le-\varepsilon_{\rm box}\)。即使原 \(\mathscr S\) 为空,此常数仍按公式为正,
但原域上的全称符号结论是空真,不能据此声称有可容许薄层。证毕。

**27.8 阈值最优性的有限含义与二坐标空前提。** 由于 \(f\) 严格递增,
\[
E\ge T_k(d)\quad\Longleftrightarrow\quad f(d)\le kf(E)
\quad(E,d>0).
\]
当 \(d\to\infty\),27.7 中 \(a\to1\),从而
\(T_k(d)-d\to\log k\)。所以任何 \(C<\log k\) 都不能使
“\(E\ge d+C\Rightarrow f(d)\le kf(E)\)”在全部正 \(E,d\) 上成立:
取充分大的 \(d\) 使 \(d+C>0\) 且 \(T_k(d)-d>C\),再取 \(E=d+C\) 即反驳。
这是只用 \(E,d,k\) 的该**标量比较**的边界,不是全目标 \(D\) 对 \(\Psi\) 的最优性,
也不是素数分离常数的最优性;全目标还含 \(S_d,H,L\) 等信息。

\(k=2\) 时
\(\ell(c)=(c_1+c_2-|c_1-c_2|)/2=\min_i c_i\)。
取达到 \(d=\min_i d_i\) 的标签 \(j\),则
\(E\le c_j<d_j=d<T_2(d)<d+\log2\)。
因此本节两个充分阈值在正二点网格的 \(k=2\) 域里都具有空前提,
不提供也不替代第 22-23 节的二坐标全域定理。阈值未通过本身不建立任何符号。

**27.9 定理 C 的有序三坐标几何。** 当 \(k=3\),按值排列
\(c_{(1)}\le c_{(2)}\le c_{(3)}\),置
\(s=c_{(2)}-c_{(1)}\)、\(t=c_{(3)}-c_{(1)}\),故 \(0\le s\le t\)。则
\[
\boxed{E-c_{(1)}=\frac{s+t-\sqrt{s^2-st+t^2}}3\ge\frac s3.}
\]
证明。\(\ell(x+a\mathbf1)=\ell(x)+a\),故只需计算 \((0,s,t)\)。
其均值为 \((s+t)/3\),中心化平方范数为
\(\frac23(s^2-st+t^2)\),代入定义即等式。
又
\(t^2-(s^2-st+t^2)=s(t-s)\ge0\),两边可开平方,故根式不超过 \(t\)。
取等恰为 \(s=0\) 或 \(t=s\),包括全相等的零方差边界;
\(0<s<t\) 时严格大于 \(s/3\)。
系数 \(1/3\) 对任意有序实三元组不能增大,因为 \(t=s>0\) 已取等;
严格有序三元组 \((a,a+s,a+s+\eta)\)、\(s>0,\eta\downarrow0\) 也趋于该边界。
这不是素数域 guard 常数的最优性证明。证毕。

**27.10 不同素数的精确整数 guard 与不可能的等号。** 在原三素数箱体中,
记 \(X_i=p_i^{b_i+1}=e^{c_i}\)。不同标签若有 \(c_i=c_j\),便有两个不同素数的
正整数幂相等,违反唯一分解。因此存在唯一标签顺序
\[
X_{i_1}<X_{i_2}<X_{i_3},\qquad c_{(l)}=c_{i_l}.
\]
**最小坐标的标签必须连同步长移动**:记 \(p_*=p_{i_1}\),
\(h_{i_1}=\log p_*\),它不必是三元组中最小的素数。
虽然最小上端点的标签可以另属一行,总有
\(d=\min_i d_i\le d_{i_1}=c_{(1)}+\log p_*\)。于是
\[
s\ge3\log(3p_*)
\ \Longrightarrow\ E\ge c_{(1)}+s/3
\ge c_{(1)}+\log p_*+\log3\ge d+\log3.
\]
27.6 因而对箱内每个可容许实薄层给 \(G<0\),并可用 27.7 的箱体裕量。
用严格递增的指数函数,条件精确等价于
\[
\boxed{p_{i_2}^{b_{i_2}+1}\ge27p_{i_1}^{b_{i_1}+4}
=27p_*^3X_{i_1}.}
\]
本证明的非严格 guard 已足够;推广到一般正网格时,分离阈值取等也不损失严格结论。
但在不同素数域,上式的**等号不可能发生**:右侧含正次 \(p_{i_1}\) 因子,
左侧是不同素数 \(p_{i_2}\) 的纯幂。即使其中一个标签为 3,此矛盾仍在。
同时 \(0<s<t\) 使 27.9 的几何不等式本身严格。
此 guard 是充分排除,不是必要充分符号判据;失败不能推出 \(G\ge0\),也不能推出 \(G<0\)。

**27.11 定理 D:每条固定正整数指数射线的精确截断。** 固定不同素数三元组
\(p\)、\(m\in\mathbb Z_{\ge1}^3\)、\(r\in\mathbb Z_{\ge0}^3\)。
对整数 \(n\ge0\),置
\[
b_i(n)=m_i n+r_i,\quad
\alpha_i=m_i\log p_i>0,\quad \gamma_i=(r_i+1)\log p_i>0,
\quad c_i(n)=\alpha_i n+\gamma_i.
\]
斜率两两不同,因为 \(\alpha_i=\alpha_j\) 将迫使
\(p_i^{m_i}=p_j^{m_j}\),与不同素数及 \(m_i,m_j\ge1\) 矛盾。
令 \(\sigma\) 严格排列斜率,定义
\[
\alpha_{\sigma_1}<\alpha_{\sigma_2}<\alpha_{\sigma_3},\quad
\Delta_{12}=\alpha_{\sigma_2}-\alpha_{\sigma_1}>0,\quad
\Delta_{23}=\alpha_{\sigma_3}-\alpha_{\sigma_2}>0,
\]
\[
\eta_{12}=\gamma_{\sigma_2}-\gamma_{\sigma_1},\quad
\eta_{23}=\gamma_{\sigma_3}-\gamma_{\sigma_2},\quad
S=3\log(3p_{\sigma_1}),
\]
\[
N_{\rm order}=\max\left\{0,
\left\lfloor\frac{-\eta_{12}}{\Delta_{12}}\right\rfloor+1,
\left\lfloor\frac{-\eta_{23}}{\Delta_{23}}\right\rfloor+1\right\},
\quad N_{\rm gap}=\max\left\{0,
\left\lceil\frac{S-\eta_{12}}{\Delta_{12}}\right\rceil\right\},
\qquad \boxed{N=\max\{N_{\rm order},N_{\rm gap}\}.}
\]
则对每个整数 \(n\ge N\) 和该箱体的每个原可容许实薄层,均有 \(G<0\)。

证明。对任意实数 \(a\),整数 \(n\ge\lfloor a\rfloor+1\) 蕴含 \(n>a\),
而整数 \(n\ge\lceil a\rceil\) 蕴含 \(n\ge a\)。所以
\(n\ge N_{\rm order}\) 给两个相邻坐标差均严格正,即
\(c_{\sigma_1}(n)<c_{\sigma_2}(n)<c_{\sigma_3}(n)\)。
floor 加一保留了在精确实交点处的严格要求,不能换成未经处理的 ceiling。
\(n\ge N_{\rm gap}\) 则给最小两坐标差
\(\Delta_{12}n+\eta_{12}\ge S\),故 27.10 适用。
分离阈值的非严格等号是安全的,虽然实际不同素数域不会取等。
所有分母严格正,数据有限,所以 \(N\) 是有限非负整数。证毕。
这些是精确数学 floor/ceiling 公式,不是已经计算并认证的有效数值 cutoff。

**27.12 可选非空域界及射线量词的限制。** 令 \(Q=\sum_i\log p_i\) 固定,
另定义
\[
N_{\rm domain}=\max\left\{0,
\left\lfloor\frac{Q+\log5040-\sum_i\gamma_i}{\sum_i\alpha_i}\right\rfloor+1\right\}.
\]
当 \(n\ge N_{\rm domain}\),有
\(A(n)=n\sum_i\alpha_i+\sum_i\gamma_i>Q+\log5040\)。
取 \(M_0=A(n)\)、\(M_1=A(n)+\min_i h_i\),便得到严格正宽度的原可容许薄层:
下角点在下端点,将任意一个最小步长坐标升高一次的实际角点在上端点。
因此 \(n\ge\max\{N,N_{\rm domain}\}\) 同时保证原域非空和全域严格排除。
这里只给一个非空性的充分界,不替代 26.16 的精确非空性判据。

量词顺序是 \(\forall(p,m,r)\ \exists N(p,m,r)\ \forall n\ge N\ \forall\) 可容许薄层;
不是对所有指数三元组共用一个 \(N\)。每箱裕量为正,没有声称沿整条射线存在远离零的统一裕量。
本推导只覆盖每个 \(m_i\ge1\) 的固定方向;有零分量的射线不在此定理范围内,
任意无界指数序列也不必最终落在某个固定正整数方向上。

**27.13 逃避该充分 guard 的无界箱体:无理对数与抽屉证明。** 固定任意不同素数三元组,
先取两个不同标签 \(a,b\),记 \(\alpha=\log p_a/\log p_b>0\)。
若 \(\alpha\) 有理,写为正整数比 \(v/u\),就有 \(p_a^u=p_b^v\),
违反唯一分解,所以 \(\alpha\) 无理。
对每个整数 \(J\ge1\),将 \([0,1)\) 分成 \(J\) 个长度为 \(1/J\) 的半开区间。
\(0,\alpha,\ldots,J\alpha\) 的 \(J+1\) 个小数部分中有两个在同一区间,
相减便得整数 \(1\le u_J\le J\) 和 \(v_J\),使
\[
0<|u_J\alpha-v_J|<1/J.
\]
这里非零来自无理性。对任意固定整数 \(B\ge1\),有限集
\(\{\operatorname{dist}(u\alpha,\mathbb Z):1\le u\le B\}\) 的最小值严格正;
所以误差趋零迫使 \(u_J\to\infty\),继而
\(v_J=\alpha u_J+o(1)\to\infty\)。丢弃有限前缀可令两者都是正整数。
于是
\[
0<|u_J\log p_a-v_J\log p_b|\longrightarrow0.
\]
对剩下的标签 \(c\),取
\[
w_J=1+\left\lceil\frac{\max\{u_J\log p_a,v_J\log p_b\}}{\log p_c}\right\rceil.
\]
此正整数满足 \(w_J\log p_c\) 严格大于前两个坐标,包括 quotient 恰为整数的情形。
令实际下指数
\[
b_a=u_J-1,\qquad b_b=v_J-1,\qquad b_c=w_J-1.
\]
它们非负且全部趋于无穷;平移后幂指数 \(u_J,v_J,w_J\) 都正。
前两标签恰为最小两个坐标,其顺序可以随 \(J\) 改变,但差值
\(s_J=|u_J\log p_a-v_J\log p_b|\to0\)。
无论哪一个是最小标签,分离阈值至少为
\(3\min\{\log(3p_a),\log(3p_b)\}>0\)。所以这些箱体最终都不满足 27.10 的 guard。
又 \(A\to\infty\),最终可按 27.12 的同一两角点薄层取法得到非空原可容许域。
这是抽屉原理的纸面构造,没有生成、搜索或数值评价其中任何一列箱体。证毕。

**27.14 剩余问题的准确含义。** 对固定素数三元组,若某箱体存在原可容许薄层使
\(G\ge0\),27.10 的逆否命题给出必要条件
\[
\boxed{0<c_{(2)}-c_{(1)}<3\log(3p_*),
\qquad X_{i_2}<27p_*^3X_{i_1}.}
\]
它不是充分条件。27.13 的无界箱体说明这条 guard 留下的区域不具有有限补集,
不说明这些箱体有 \(G\ge0\),也不声称其它阈值或其它方法不能排除它们。
固定素数的任意非负指数全域比较、一般素数域 \(k\ge3\) 的占优以及 RH 都仍 OPEN。
正整数射线定理没有把无界问题化成有限扫描,更没有完成长期研究目标。
另行在研的相对展宽问题没有进入本节的证明或结论。

**27.15 前瞻整箱过滤与第一处压缩记号订正。** 以下仅是未来设计的数学依据。
对每箱可先精确构造 \(X_i=p_i^{b_i+1}\),排序保留标签 \(i_1,i_2,i_3\),
再比较 \(X_{i_2}\) 与 \(R=27p_{i_1}^{b_{i_1}+4}\)。若精确认证 \(X_{i_2}\ge R\),
27.10 给整箱所有可容许薄层的严格负号。若比较失败或未决,箱体留给既有 eligibility
和符号程序,不得从浮点对数的近似次序直接宣布排除。

等价的带符号指数表示使用去重素数基
\(\mathcal B=\{p_1,p_2,p_3\}\cup\{3\}\),定义
\[
z_q=(b_{i_2}+1)\mathbf1_{\{q=p_{i_2}\}}
-(b_{i_1}+4)\mathbf1_{\{q=p_{i_1}\}}-3\,\mathbf1_{\{q=3\}}.
\]
primary 的压缩串 `-31[q=3]` 明确应读为
`-3 * indicator(q=3)`,因为 \(27=3^3\),绝不是减去 31。
若已有标签为 3,其全部贡献在同一 \(q=3\) 坐标相加。
由 \(X_{i_2}/R=\prod_{q\in\mathcal B}q^{z_q}\),guard 精确等价于
\[
\prod_{q\in\mathcal B}q^{\max(z_q,0)}
\ge\prod_{q\in\mathcal B}q^{\max(-z_q,0)}.
\]
这种向量以乘法表示正有理数,逐坐标或字典序比较指数不能决定该有理数与 1 的大小。
它不是允许实际素数指数为负;负号只属于这个比值表示。

**27.16 前瞻有限容量与第二处压缩记号订正。** 若另行预登记
\(0\le b_i\le U_i\)、整数 \(U_i\ge0\),令 \(\lambda_i\) 为 \(p_i\) 的精确二进制位长,
故 \(p_i<2^{\lambda_i}\)。置
\[
B=5+\max_i\{\lambda_i(U_i+4)\},\qquad
\boxed{W=\lceil B/8\rceil.}
\]
因为 \(27<2^5\),每个 \(X_i\) 及任一可能右端
\(27p_i^{b_i+4}\) 都严格小于 \(2^B\le256^W\),所以 \(W\) 个 base-256 limbs
足以容纳这些最终操作数。沿用第 26 节固定窗口 \(p_i\le19,U_i=15\) 时,
这条**新比较本身**可取 \(B=100,W=13\);不替换既有其它 guards 的容量或常量表。

未来逐内积立即处理进位的标准乘法,若两输入 limb、已有输出 limb 和 carry
都在 \(0,\ldots,255\),则临时值上界为
\[
\boxed{255\cdot255+255+255=65535=2^{16}-1.}
\]
primary 的 `255255+255+255` 明确应读为
`255*255+255+255=65535`,不是整数 255255 再加两次 255。
新 carry 是该临时值除以 256 的整商,仍至多 255,余数亦在 \(0,\ldots,255\),
从零 carry 起给出这一步的归纳界。此论证依赖“每次内积后立即进位”,
不能用于未经约束的一长串未进位累加。
比较可从最高 limb 向下进行;完整幂构造、中间乘积、指数计数器、索引和进位传播
仍须在真实实现中证明不越界。溢出、次序未认证或精确比较不可用只能返回 unresolved,
不能排除箱体。这里没有认证任何 MPS 指令或 kernel。

**27.17 保留第 26 节的稳定 25 槽,不采纳另一排列。** 对原登记的
\(0\le t<56\)、\(0\le b_0,b_1,b_2\le15\),继续精确使用
\[
\mathrm{box\_id}=4096t+256b_0+16b_1+b_2,\qquad
\mathrm{row\_id}=25\,\mathrm{box\_id}+\mathrm{slot}.
\]
这里只为槽布局使用 \(i=0,1,2\),坐标与素数标签始终成对。
槽 \(0,\ldots,6\) 是相邻对,令 \(s=\mathrm{slot}+1\),对应
\((\beta_{s-1},\beta_s)\)。槽 \(7,\ldots,24\) 继续为
\[
r=\mathrm{slot}-7,\quad j=1+\lfloor r/3\rfloor,\quad i=r\bmod3,
\qquad (\beta_{j-1},\,3(c_i+d_i)-\beta_{j-1}),
\]
即 \(\mathrm{slot}=7+3(j-1)+i\)、\(j=1,\ldots,6\)。全部 eligibility 条件仍是 26.18/26.21 的原条件。
primary 另写的 `7+6*(i-1)+(j-1)` 使用 \(i=1,2,3\)、\(j=1,\ldots,6\),
是同一对集合的另一种排列,本次只披露为**未采用的呈现**,不替换任何既有 raw ID。
例如同一坐标行 \(i=0\)、\(j=2\) 在稳定布局为 slot 10,
在该替代呈现以 \(i=1\) 表示时为 slot 8;两种编号不能互换而不说明。

**27.18 条件覆盖的记账语义与本轮零执行。** 未来若认证一个箱体的分离 guard,
一个箱证书可覆盖它的全部 25 个既有 raw IDs,
即 \([25\,\mathrm{box\_id},25\,\mathrm{box\_id}+24]\)。
语义必须是“**若该 raw slot 可容许,则解析排除**”;eligibility 可以尚未求值,
所以不能记作 25 个可容许薄层或 25 次数值符号评价。
证书应绑定素数/指数三元组、带标签的精确坐标次序、guard 比较、定理身份与版本及 raw-ID 范围。
压缩范围只有在规范展开逐一覆盖这些原始 ID 时才构成完整覆盖。
未来一批中每个 raw slot 恰归一类:箱证书条件覆盖、ineligible、符号认证负、
符号认证非负、unresolved;五类互斥,总数须为登记箱数的 25 倍。
guard 失败或未决的箱不能计入第一类;输入/程序身份和独立精确算术认证仍是实施义务。

本源增量的 searched boxes、executed box guards、executed kernels、numerically evaluated slots、
certified computational exclusions 均为 0,没有实施 pruning,没有修改任何 kernel。
固定代数和整数恒等式的 CPU 验算只支撑正文记号,不是候选生成、指数箱搜索或旧结果重放。

**27.19 经典材料与历史访问限制。** Boyd/Vandenberghe 的
[Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)
Appendix A.1.2 印刷 p.634 给范数齐次性和三角不等式;
§3.1.5 印刷 pp.72-73 给范数凸性及由三角不等式、齐次性作的证明;
§3.1.3 式 (3.3) 印刷 p.70 给严格凸函数在不同点的严格一阶支撑不等式。
这些是 literature-attested 的经典材料,不是该书含有本节素数定理的断言。
27.4 的欧氏范数及增量等号、27.6 的严格 Bernoulli、27.13 的抽屉构造已在本节自足证明。
这里没有穷尽检索新颖性,没有 Lean 或 RH 结果。

caller 已检查这些书页,所供 PDF 为 6881335 字节,SHA256
40d976c83c18cce1900eff8c41bd5ad408c102b813af39d05ff85678ccf8d76e。
I11 读取所供核对材料、对应文字摘录,并核对 PDF 身份。
primary 当时无法读取所给 immutable raw URL 和 GitHub blob URL,因此没有独立检查仓库全文或其身份;
它使用请求提供的定义。这一历史限制不因 caller 后来的源核对或 I11 的本地前缀核对而抹去。
primary、caller 的有界数学核验与 I11 实施自查是不同职责,不组成三票独立 review。
本轮 provenance 和可复现的固定恒等式验算见
[prime-coordinate-separation-0909.md](../../reports/prime-coordinate-separation-0909.md)。

**27.20 本次 canonical 摄入及状态。** 本实施为 caller 的 consensus-rnd:sshx 编排下
Codex CLI I11,flight qgh0909-i11-separation-append,attempt 1,retry budget 1;
工作树为 /Users/auricstudio/trureturing-qgh-separation,分支
lane/math/quantized-gh-separation-0909。实施者 repo-prior-exposed,
primary external-prior-exposed;不声称 sterile priors 或模型族多样性。
本轮没有子 worker、新 oracle、同轮 review 输入、worker 日志或 opaque log_ref 内容读取,
没有邻近活跃工作树或 caller 会话发现。仅依指定参考源与显式供给材料执行本增量。
源文和一个新报告之外的新增 CAS/entry 仅由
~~~sh
make ingest BASE=391f7355698085c6500b46838a093dad05947ffb SOURCE=arithmetic-boundary-quantization
~~~
产生,不手编或重命名 generated 文件。实际路径为 Meta/Digestion/atoms/sha256
与 Meta/Digestion/backfill;schema 使用 fingerprints/cas_ref/coverage_gids,没有 body atom_id。
新条目保持 residual-open,不表示证明已被 Lean 吸收。generator 若产生历史 LF 变体则原样保留,
不重放历史 atom、不作全仓 harness/Lean 构建。每个新实质单元在本节中编号,
新 canonical 源跨度覆盖、文件身份和命令退出码由本次 implementation envelope 记录。
Git 暂存、提交、push、PR、merge 和后续独立评审均归 caller;本节没有代行这些动作,
也没有把有效实施信封当作独立评审或长期目标完成。

## 28. 固定三素数的相对跨度界与非负整数指数射线排除

**28.1 本层命题与证据身份。** 本节是 C33 / S17 的 PAPER_ARGUMENT / repo-derived
参考输入,主数学输入为实际 GPT PRO task aaaf57ba-7b72-4143-b830-b4b58fe7fc2c,
conversation conv_576df749336210e9,该调用观测模型 GPT-6 Astra。
本节证明一个对共同高度一致的远第三坐标负裕量,再与第 27 节的小坐标分离结果合成
固定三素数的有界相对跨度结论,并把射线排除扩展到所有非零非负整数方向。
经典范数与凹性材料的出处见 28.18;专门的组合估计是这里展开的推导,
其原创性未作评定,不声称新颖性、优先权或穷尽文献检索。
GH 保留为用户尚未数学定义的原标签。这个包络比较缺口不被称为 RH 等价判据,
本节没有 RH 进展或形式化证明主张。

本节只用已完成的 relative-spread primary、其 caller 固定核验和本树封存的先行源文。
后续 common-height 与 balanced-all-slab primaries 不是本层输入。
第 1-27 节的 201529 字节 / 3627 行前缀原样保留,SHA256 为
b7cb35d87d0a7b7e569c49ab57f2b556c454257de8bd65899587d13be1338537;
implementation BASE 为 feb497ec31f68e09ccc547a08810c398e66f3ee6。
原始 primary payload 的 SHA256 为
7d0bddfc1fcf761290f7bf777663f52f07af927eb2832001a67ff509bdeb4f11。
其两处转义的非负整数记号在本节排作通常的 \(\mathbb Z_{\ge0}\),原始 payload 不改。

**28.2 正步长、闭角点与同一比较目标。** 全部对数为自然对数,范数为通常欧氏范数。
固定有限 \(h_1,h_2,h_3>0\),要求八个子集和两两不同,并按值排列为
\[
0=v_0<v_1<\cdots<v_7=Q,\qquad Q=h_1+h_2+h_3,
\qquad \delta=\min_{0\le j<7}(v_{j+1}-v_j)>0.
\]
正步长本身不保证子集和不同;这是假设的一部分,素数情形在 28.13 验证它。
固定有限 \(S\ge0\)。对有限实数
\[
T\ge\log2,\qquad 0\le s\le S,\qquad t\ge s,
\qquad c=(T,T+s,T+t),\quad d_i=c_i+h_i,\quad A=3T+s+t,
\]
称有限实预算对 \((M_0,M_1)\) 可容许,当且仅当
\[
Q+\log5040<M_0<M_1<\infty
\]
且至少两个角点 \(x\in\prod_i\{c_i,d_i\}\) 的预算在闭区间
\([M_0,M_1]\) 中。角点预算恰为 \(A+v_j\);两端均可取到实际角点。
置
\[
f(x)=\log(1-e^{-x})\quad(x>0),\qquad
D(M_1)=\max_{\substack{0\le y_i\le1\\\sum_i h_i y_i\le M_1-A}}
\sum_{i=1}^3\bigl((1-y_i)f(c_i)+y_i f(d_i)\bigr),
\]
\[
\mu=M_1/3,\quad I=[M_0/3,M_1/3],\quad
\delta_i=\operatorname{dist}(I,\{c_i,d_i\}),\quad
\rho=\sqrt{\frac{\delta_1^2+\delta_2^2+\delta_3^2}{6}},
\qquad L=\mu-\rho,\quad H=\mu+2\rho,
\]
\[
\Psi=f(H)+2f(L),\qquad G(M_0,M_1)=D(M_1)-\Psi.
\]
\(\delta\) 是子集和最小间隔,\(\delta_i\) 是距离,二者不可混用。
角点存在保证 \(M_1\ge A\),所以 \(D\) 的可行域非空且紧,最大值存在。
28.4 先证 \(L,H\ge T>0\),再使用 \(\Psi\)。在原素数域,这仍是
\(G=U_{\rm dual}-U_{\rm var}\),共同的 \(\log E_S\) 抵消;
本节直接使用上述原始优化定义,无需重建背包价格证书。

**28.3 定理 A:显式一致远坐标界。** 保留 primary 的常数,其中
\(K\) 即原 payload 所记的 \(K_W\):
\[
\boxed{K=K_W=
\frac{(S+4Q)^2+(2S+4Q)^2+(S+Q)^2}{9}},\qquad
\boxed{\epsilon=\delta/18},
\]
\[
\boxed{a=e^{-(S+Q)/2}(1-e^{-\epsilon})>0},
\]
\[
\boxed{R=1+\max\left\{
2S+3Q,\ \sqrt{6K},\ \frac{9K}{\delta},\quad
\frac32(S+Q)+3\log\!\left(\frac{2}{1-e^{-\delta/18}}\right)
\right\}.}
\]
这些量有限,\(K>0\),所有分母和对数自变量均严格正。
若 \(t\ge R\),则 28.2 的每个可容许实薄层均满足
\[
\boxed{e^T G(M_0,M_1)<-a<0.}
\]
这也蕴含较弱的 \(e^TG\le-a\)。常数不依赖 \(T,s,M_0,M_1\)
或步长标签的排列;但依赖固定步长集合及所选 \(S\)。
证明依次由 28.4-28.12 给出。允许 \(T=\log2\)、\(s=0\)、\(s=S\),
特别在 \(t=R\) 仍是严格负裕量。

**28.4 正支持与饱和所需单调性。** 对 \(x\in\mathbb R^3\) 定义
\[
\bar x=\tfrac13\sum_i x_i,\qquad
\Pi x=x-\bar x\mathbf1,\qquad
\ell(x)=\bar x-\|\Pi x\|/\sqrt6.
\]
第 27 节已证明它的精确等号分类;此处只重述所需的自足范数步骤。
因为 \(\|\Pi e_i\|=\sqrt{2/3}\),对 \(u\ge0\),三角不等式给
\[
\ell(x+ue_i)-\ell(x)
\ge u/3-u\|\Pi e_i\|/\sqrt6=0.
\]
当 \(u=0\) 恒等;当 \(u>0\),取等恰为 \(\Pi x=\lambda\Pi e_i\)、\(\lambda\ge0\),
即三角等号的非负共线情形。因此 \(\ell\) 逐坐标非减。
若 \(x\) 是薄层中的实际角点,则 \(\bar x\in I\)、\(\mu\ge\bar x\),
逐项 \(\delta_i\le|x_i-\bar x|\)。故
\[
L\ge\mu-\|\Pi x\|/\sqrt6
=\ell(x)+(\mu-\bar x)\ge\ell(c)\ge\ell(T\mathbf1)=T.
\]
这与 primary 从 \(\delta_i\le|x_i-\mu|\) 和三角不等式得到的较弱式
\(L\ge\ell(x)+(1-1/\sqrt2)(\mu-\bar x)\ge T\) 一致。
于是 \(H\ge L\ge T\ge\log2\),包括 \(\rho=0\) 的情形。

在正支持域 \(\mu-\rho>0\)、\(\rho\ge0\),令
\(F(\mu,\rho)=f(\mu+2\rho)+2f(\mu-\rho)\)。直接微分得
\[
f'(x)=\frac1{e^x-1}>0,\qquad
f''(x)=-\frac{e^x}{(e^x-1)^2}<0,
\]
\[
F_\mu=f'(H)+2f'(L)>0,\qquad
F_\rho=2\bigl(f'(H)-f'(L)\bigr)\le0.
\]
后式在 \(\rho=0\) 为等号,在 \(\rho>0\) 严格负;无需在零距离处微分范数。
固定 \(M_1\) 而提高可容许的 \(M_0\) 时,区间缩小,各距离和 \(\rho\) 非减,
所以 \(\Psi\) 非增、\(G\) 非减。中间区间仍含保留角点,正支持一直有效。
这是非严格单调性,不能把所有饱和步骤都说成严格。证毕。

**28.5 第二角点饱和及空域的精确条件。** 给定任一可容许薄层,
令 \(A+v_j\) 是不超过 \(M_1\) 的最大角点预算。至少两个角点在薄层内,
故 \(j\ge1\),且第二大角点预算
\[
a_*=A+v_{j-1}\ge M_0>Q+\log5040,\qquad a_*<M_1.
\]
证明。若 \(A+v_{j-1}<M_0\),不超过 \(M_1\) 的角点至多一个落在薄层内,
与假设矛盾。又 \(v_{j-1}<v_j\) 且 \(A+v_j\le M_1\),所以最后不等式严格。
因此 \((a_*,M_1)\) 仍可容许,保留两个闭端点意义下的角点,
28.4 给
\[
G(M_0,M_1)\le G(a_*,M_1).
\]
若 \(M_1\le A+Q\),写 \(r=v_{j-1}\)、\(q=M_1-A\),则
\[
0\le r<q\le Q,\qquad q-r\ge v_j-v_{j-1}\ge\delta.
\]
\(M_1=A+v_j\) 时同样有效,不使用极限或开角点惯例。
若 \(M_1\ge A+Q\),则 \(j=7\)、\(a_*=A+v_6\),由 28.12 单独处理。

整个可容许域为空当且仅当
\[
\boxed{A+v_6\le Q+\log5040.}
\]
若右式成立,严格大于 cutoff 的角点至多一个,没有可容许薄层。
反之,若 \(A+v_6>Q+\log5040\),
取 \((M_0,M_1)=(A+v_6,A+Q)\) 即得可容许薄层。
cutoff 的等号属于空域,不能用闭角点约定把它纳入。证毕。

**28.6 饱和有限区间中的精确端点几何。** 现在只考虑
\(M_0=A+r,M_1=A+q\),其中 \(0\le r<q\le Q\)。若 \(t\ge2S+3Q\),则
\[
\frac{M_0}3-d_1=\frac{t+s+r}3-h_1
\ge\frac{2S}3+Q-h_1>0,
\]
\[
\frac{M_0}3-d_2=\frac{t+r-2s}3-h_2\ge Q-h_2>0,
\qquad
c_3-\frac{M_1}3=\frac{2t-s-q}3\ge S+\frac{5Q}3>0.
\]
严格性使用另外两个步长正,即 \(Q-h_i>0\)。因此最近端点分别是
\(d_1,d_2,c_3\),距离恰为
\[
\boxed{\delta_1=\frac{t+s+r}3-h_1,\quad
\delta_2=\frac{t+r-2s}3-h_2,\quad
\delta_3=\frac{2t-s-q}3.}
\]
这些式子由区间整体在前两个上端点之上、在第三个下端点之下直接得到。
整个有限范围没有最近端点的反射切换,并非只在相邻角点节点如此。
这里的 \(c_3>M_1/3\) **不外推到** \(M_1\to\infty\) 的上尾;
那时可失效的几何不参与 28.12 的证明。证毕。

**28.7 精确范数余项、零条件与正分母。** 在 28.6 的范围置
\[
\boldsymbol\delta=tU+W,\qquad U=\frac{(1,1,2)}3,\qquad
W=\left(\frac{s+r}3-h_1,\frac{r-2s}3-h_2,\frac{-s-q}3\right).
\]
由 \(s\le S\)、\(r,q\le Q\)、\(h_i\le Q\) 得
\[
|W_1|\le(S+4Q)/3,\quad |W_2|\le(2S+4Q)/3,\quad
|W_3|\le(S+Q)/3,\qquad \|W\|^2\le K.
\]
令
\[
u=U/\|U\|=(1,1,2)/\sqrt6,\qquad
v=\langle u,W\rangle=-\frac{s+h_1+h_2+2(q-r)/3}{\sqrt6},
\]
\[
W_\perp=W-vu,\qquad z=t\|U\|+v,\qquad
\|U\|^2=2/3,\quad \|u\|=1,\quad \langle u,W_\perp\rangle=0.
\]
如果 \(t\ge\sqrt{6K}\),则由 \(|v|\le\|W\|\le\sqrt K\),
\[
z\ge t\sqrt{2/3}-\sqrt K\ge t/\sqrt6>0.
\]
正交分解给 \(\|tU+W\|^2=z^2+\|W_\perp\|^2\)。定义线性化端点
\[
L_\infty=\mu-z/\sqrt6
=T+\frac s2+\frac{4q-r}9+\frac{h_1+h_2}6.
\]
这只是显式表达式,不以未经控制的渐近符号代替余项。精确有理化得到
\[
\boxed{L_\infty-L=
\frac{\|W_\perp\|^2}
{\sqrt6\bigl(\sqrt{z^2+\|W_\perp\|^2}+z\bigr)}.}
\]
分母至少 \(2\sqrt6z\ge2t>0\),故
\[
\boxed{0\le L_\infty-L\le\frac{K}{2t}.}
\]
余项为零当且仅当 \(W_\perp=0\),亦即 \(W\) 与 \(U\) 共线;
允许共线系数为负,因为 \(z>0\) 已另行保证。
这些恒等式及分母估计完全不含共同高度 \(T\)。阈值等号
\(t=\sqrt{6K}\) 也给严格正分母。证毕。

**28.8 前两坐标的资源上界。** 继续固定有限区间,记
\[
B=h_1+h_2>0,\qquad
m_{\rm low}=T+\frac{s+\min(q,B)}2.
\]
任意可行 \(y\) 满足
\(h_1y_1+h_2y_2\le\min(q,B)\)。由 \(f\) 凹,
\[
(1-y_i)f(c_i)+y_i f(d_i)\le f(c_i+h_i y_i).
\]
对前两行再作等权 Jensen,并用 \(f\) 递增,得它们的贡献至多
\[
2f\!\left(T+\frac{s+h_1y_1+h_2y_2}2\right)\le2f(m_{\rm low}).
\]
第三行至多 \(f(d_3)<0\),所以
\[
\boxed{D(M_1)\le2f(m_{\rm low})+f(d_3)<2f(m_{\rm low}).}
\]
证明对每个可行 \(y\) 成立,取最大即可;没有选择特定最优背包解或假定其价格无并列。
单行弦界在 \(y_i=0,1\) 取等,在 \(0<y_i<1\) 严格;
两行 Jensen 取等要求 \(c_1+h_1y_1=c_2+h_2y_2\)。资源界的等号另要求
\(h_1y_1+h_2y_2=\min(q,B)\),第三行上界取等要求 \(y_3=1\)。
无论这些条件能否同时达到,最后一步因 \(d_3\) 有限且正而始终严格。
\(q\le B\) 与 \(q\ge B\) 两种资源情形均被保留。证毕。

**28.9 两种资源情形的端点间隙。** 将 28.7 与 28.8 的显式式子相减,分别得
\[
\boxed{L_\infty-m_{\rm low}=
\begin{cases}
(B-q)/6+(q-r)/9,&q\le B,\\
(q-B)/3+(q-r)/9,&q\ge B.
\end{cases}}
\]
证明。在第一种情形,\(m_{\rm low}=T+(s+q)/2\),相减为
\(B/6-q/18-r/9\),即所列第一式;第二种情形减去
\(T+(s+B)/2\),得 \((4q-r)/9-B/3\),即第二式。
在 \(q=B\) 两式同为 \((q-r)/9\),无缺口也无额外分支限制。
各式首项非负,所以 \(q-r\ge\delta\) 给
\(L_\infty-m_{\rm low}\ge\delta/9\)。又若
\(t\ge\sqrt{6K}\) 且 \(t\ge9K/\delta\),28.7 给
\[
L\ge L_\infty-\frac K{2t}
\ge m_{\rm low}+\frac\delta9-\frac\delta{18}
=\boxed{m_{\rm low}+\epsilon}.
\]
允许 \(q-r=\delta\)、\(q=B\) 及两个余项阈值的等号。
相邻角点足以满足间隔假设,但证明覆盖其间的每个实上预算。证毕。

**28.10 一致负裕量在 \(t=R\) 仍严格。** 对 \(x\ge\log2\),
\[
-f(x)=\int_0^{e^{-x}}\frac{du}{1-u}\le2e^{-x}.
\]
同时对 \(m>0\)、\(\epsilon>0\),
\[
f(m+\epsilon)-f(m)=\int_0^\epsilon\frac{du}{e^{m+u}-1}
\ge e^{-m}(1-e^{-\epsilon}).
\]
所有积分均在正定义域。因 \(H\ge\mu=T+(s+t+q)/3\ge T+t/3\),
有 \(f(H)\ge-2e^{-T-t/3}\)。再用
\(m_{\rm low}\le T+(S+Q)/2\)、28.8-28.9,得到
\[
\Psi-D\ge2e^{-T}\bigl[a-e^{-t/3}\bigr],\qquad
 e^TG\le-2\bigl[a-e^{-t/3}\bigr].
\]
具体地,先用 \(D<2f(m_{\rm low})\)、\(L\ge m_{\rm low}+\epsilon\),
再应用上述积分差下界;将可能的严格步放宽为 \(\ge\) 不影响结论。
令
\[
B_{\rm tail}=\tfrac32(S+Q)+3\log\!\left(\frac2{1-e^{-\epsilon}}\right).
\]
则 \(e^{-B_{\rm tail}/3}=a/2\)。28.3 的 \(+1\) 保证
\(t\ge R>B_{\rm tail}\),从而 \(e^{-t/3}<a/2\)。于是
\[
\boxed{e^TG\le-2[a-e^{-t/3}]<-a<0.}
\]
这说明即使前面若干非严格估计取等,\(t=R\) 也不会失去严格裕量。
没有计算或声称任何数值半径。证毕。

**28.11 每个有限上预算薄层的归约。** 设 \(t\ge R\) 且
\(M_1\le A+Q\)。28.5 的第二角点饱和给 \(r=v_{j-1}\)、\(q=M_1-A\),
满足全部有限区间假设,特别是 \(q-r\ge\delta\)。
因为 \(R\) 大于 28.6-28.9 所需阈值,28.10 直接适用,故
\[
e^TG(M_0,M_1)\le e^TG(A+v_{j-1},M_1)<-a.
\]
上预算位于两个相邻角点之间、恰在角点、或恰为 \(A+Q\),结论一致。
因此此处不依赖一般箱体的有限最大值定理,也不需要运行其 25 槽设计。
若另有同箱体有限支配式 \(G\le\max_jG_j\),固定 \(T\) 下当然有
\(e^TG\le\max_j(e^TG_j)\);本节给的是覆盖整个饱和区间的直接证明,
不能把对角点的有限检查冒充这里的全实薄层证明。证毕。

**28.12 上尾单独由严格单调性控制。** 设 \(M_1\ge A+Q\)。若原薄层可容许,
28.5 给 \(A+v_6>Q+\log5040\),所以末相邻对
\((A+v_6,A+Q)\) 可容许,并已由 28.11 控制。
饱和后固定 \(M_0=A+v_6\)。整个上尾中全上角点可行,所有弦增益
\(f(d_i)-f(c_i)>0\),故
\[
D(M_1)=\sum_i f(d_i).
\]
这是常数;恰好达到全上目标需要全部 \(y_i=1\),所以一般而言
此饱和值可达当且仅当 \(M_1\ge A+Q\)。
随着上预算严格增加,\(\mu\) 严格增加,距离区间扩大,各 \(\delta_i\)
及 \(\rho\) 非增。28.4 的 \(F_\mu>0,F_\rho\le0\) 给 \(\Psi\) 严格增加。
比较两个参数点时可先在旧 \(\mu\) 减小 \(\rho\),再提高 \(\mu\);
两段的 \(\mu-\rho\) 都至少为原先的正 \(L\),故单调性使用域合法。
即使 \(\rho\) 在某段不变或为零,\(\mu\) 的严格增长仍使结论严格。
因此上尾 \(G\) 严格减少,并有
\[
e^TG(M_0,M_1)\le e^TG(A+v_6,M_1)
\le e^TG(A+v_6,A+Q)<-a.
\]
第二步在 \(M_1>A+Q\) 时严格,在 \(M_1=A+Q\) 时相等。
本证明完全没有假定上尾仍有 \(c_3>M_1/3\)。
28.11 与本段合起来完成定理 A;空域情形按 28.5 是全称空真。证毕。

**28.13 固定素数、标签排列与小坐标分离的正确符号。** 固定无序集合
\(P=\{p_1,p_2,p_3\}\),其中三个素数两两不同。对
\(b\in\mathbb Z_{\ge0}^3\),取
\[
h_i=\log p_i,\quad c_i=(b_i+1)h_i,\quad d_i=(b_i+2)h_i.
\]
若两个子集和相等,指数化后为两个平方自由素数乘积相等,唯一分解迫使子集相同。
故八个子集和不同、\(\delta>0\)。同理 \(c_i=c_j\) 会使两个不同素数的
严格正整数幂相等,不可能。可唯一按 \(c_1<c_2<c_3\) 重排坐标,
且必须把 \(p_i,b_i,h_i,d_i\) 一起搬动;这个 \(p_1\) 不必是最小素数。
于是 \(c=(T,T+s,T+t)\)、\(T\ge\log2\)、\(0<s<t\)。

为自足地连接第 27 节,记 \(E=\ell(c)\)、\(d_*=\min_i d_i\)。有
\[
E=T+\frac{s+t-\sqrt{s^2-st+t^2}}3\ge T+\frac s3,
\]
因为 \(s(t-s)\ge0\) 给根式不超过 \(t\)。在一般有序实坐标上,
此步取等恰为 \(s=0\) 或 \(t=s\);实际素数箱体中严格。
若 \(s\ge3\log(3p_1)\),则
\[
E\ge T+h_1+\log3=d_1+\log3\ge d_*+\log3.
\]
设 \(u=e^{-d_*}\in(0,1)\),精确展开给
\[
(1-u/3)^3-(1-u)=u^2/3-u^3/27>0.
\]
对正量取对数并用递增性,即
\(f(d_*)<3f(d_*+\log3)\le3f(E)\)。另一方面
\[
D\le\sum_i f(d_i)<f(d_*),\qquad
\Psi\ge3f(L)\ge3f(E),
\]
其中支持界来自 28.4。所以每个可容许薄层均有 \(G<0\),
包括分离阈值的等号。其等价整数充分条件为
\[
p_2^{b_2+1}\ge27p_1^{b_1+4},
\]
使用的是坐标次序标签;不同素数的唯一分解又排除了该整数式的等号。
**正确结论是条件证明 \(G<0\),从而排除 \(G\ge0\)**。
primary 已纠正 caller 早先把被排除符号写成 \(G<0\) 的措辞;
这里不沿用那个反向表述。证毕。

**28.14 定理 B:每个固定三素数集合的有界相对跨度。** 对上述固定 \(P\),置
\[
p_{\max}=\max P,\qquad S=3\log(3p_{\max}),
\]
并以此 \(S\) 和 \(h_i=\log p_i\) 定义 28.3 的同一 \(K,\epsilon,a,R\)。
如果某个指数箱体存在可容许实薄层使 \(G\ge0\),则
\[
\boxed{\max_i((b_i+1)\log p_i)-\min_i((b_i+1)\log p_i)<R.}
\]
证明。按 28.13 排列下坐标。若 \(s\ge3\log(3p_1)\),那里已严格排除
\(G\ge0\),故这样的箱体必须满足
\(s<3\log(3p_1)\le S\),特别 \(s<S\)。
如果再有 \(t\ge R\),定理 A 又对所有可容许薄层给严格负号,矛盾。
所以 \(t<R\)。\(Q,\delta,p_{\max},S,K,R\) 均在素数标签排列下不变,
半径只依赖固定的无序素数集合。
其逆否形式为跨度 \(\ge R\) 的箱体每个可容许薄层都有 \(G<0\),包括跨度等于 \(R\)。
这不对小坐标分离那一支另声称统一的 \(-ae^{-T}\) 裕量;
该显式裕量由定理 A 在 \(s\le S,t\ge R\) 的范围提供。证毕。

**28.15 定理 C:非零非负整数指数射线的 ceiling 截断。** 固定同一 \(P\),取
\[
m,r\in\mathbb Z_{\ge0}^3,\qquad m\ne(0,0,0),\qquad
b_i(n)=m_i n+r_i\quad(n\in\mathbb Z_{\ge0}).
\]
在原始固定标签下定义
\[
\alpha_i=m_i\log p_i,\qquad \gamma_i=(r_i+1)\log p_i,\qquad
c_i(n)=\alpha_i n+\gamma_i.
\]
任选最大斜率标签 \(i_+\) 与最小斜率标签 \(i_-\);若几个最小值同为零,
可任取其中一个。置
\[
\Delta=\alpha_{i_+}-\alpha_{i_-}>0,\qquad
\beta=\gamma_{i_+}-\gamma_{i_-},\qquad
\boxed{N=\max\left\{0,\left\lceil\frac{R-\beta}{\Delta}\right\rceil\right\}.}
\]
则对每个整数 \(n\ge N\),箱体 \(b(n)\) 的每个可容许实薄层均满足 \(G<0\)。

证明。先验 \(\Delta>0\):若全部 \(\alpha_i\) 相同且一个 \(m_i=0\),
共同斜率为零,使所有 \(m_i=0\),矛盾。若共同斜率严格正,则任意两个标签满足
\(p_i^{m_i}=p_j^{m_j}\),与不同素数的唯一分解矛盾。
因此 \(\Delta\) 严格正,\(N\) 有限且为非负整数。对每个 \(n\ge0\),
不管当前坐标的排序怎样,都有
\[
\max_i c_i(n)-\min_i c_i(n)
\ge c_{i_+}(n)-c_{i_-}(n)=\Delta n+\beta.
\]
当整数 \(n\ge N\) 时,ceiling 定义确保 \(\Delta n+\beta\ge R\),
即使 \((R-\beta)/\Delta\le0\) 而 \(N=0\) 也如此。
定理 B 的逆否形式遂给所需严格负号。\(\Delta n+\beta=R\) 被同一定理覆盖,
无需给 ceiling 加一,也无需第 27 节的坐标排序稳定化 cutoff。
零斜率坐标可以存在,\(\beta\) 可以为负,都不改变证明。
这里没有计算或认证任何数值 \(N\)。证毕。

**28.16 原整数角点的严格 cutoff 与射线空域。** 对素数箱体记
\[
N_e=\prod_{i=1}^3p_i^{b_i+e_i},\qquad e_i\in\{0,1\}.
\]
实际整数指数可为零,而平移坐标指数为 \(b_i+1\) 或 \(b_i+2\),均正。
角点预算恰为 \(Q+\log N_e\)。唯一分解给八个整数角点不同;
因此 28.5 精确等价于:可容许域为空,当且仅当第二大的 \(N_e\le5040\),
包括等于 5040 的边界。两端的角点包含仍是闭的,严格性只在
\(Q+\log5040<M_0\) 这个原下截断处。

定理 A-C 对空域的全称结论为空真,不声称存在薄层。
非零非负射线还满足
\[
N_e(n)=\left(\prod_i p_i^{m_i}\right)^n\prod_i p_i^{r_i+e_i},
\]
其中共同乘子 \(\prod_i p_i^{m_i}>1\),故所有八个整数角点及第二大角点最终超过 5040。
这是最终非空性的直接证明,但不是定理 C 的附加前提;
为了全称排除无需另加非空域 cutoff,也没有给出数值非空域界。证毕。

**28.17 未闭的共同高度与精确范围。** 固定 \(P\) 后,定理 B 只把可能的
\(G\ge0\) 限制到相对跨度 \(<R\);共同高度 \(T\) 仍无上界。
该几何区域含无穷多素数指数箱体:对任意充分大的实数 \(Z\ge\max_i h_i\),取
\[
b_i=\lceil Z/h_i\rceil-1\in\mathbb Z_{\ge0},\qquad
c_i=h_i\lceil Z/h_i\rceil\in[Z,Z+h_i).
\]
因而 \(\max c_i-\min c_i<\max h_i\le Q<R\),且 \(\min c_i\to\infty\)。
所以任意大的共同高度均有这种有界形状箱体;这构造的是剩余几何区域中的箱体,
**不是** \(G\ge0\) 的见证。一般这样取得的指数序列不属于一条固定整数射线,
与定理 C 无冲突。论证只是取整构造,本轮没有执行指数枚举。

剩余区域的符号尚未由本节判定,可容许薄层中是否有 \(G=0\) 也未决定。
远坐标区和小坐标分离区的结论都严格排除了零号。
这里的常数不是对变化素数集合一致的常数,没有有限完整的素数/指数搜索补集,
没有一般素数三坐标全域符号定理,也没有 RH 结论。
下一数学缺口是固定步长、有界相对偏移但共同高度无界时的 \(G\) 控制;
后续独立研究即使完成,也须作为另层输入,不能被本节提前引用。

**28.18 经典归属与已完成固定核验。** primary 已读并引用 Boyd/Vandenberghe,
[Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf),
Appendix A.1.2 印刷 p.634 的范数公理,§3.1.5 印刷 pp.72-73 的范数凸性,
以及 §3.1.3 印刷 p.70 式 (3.3) 的严格一阶条件。
第 27.19 节已保存 caller 的书页与 PDF 身份核对。
范数不等式、凹性、Jensen 及此处所用的初等微积分属于经典材料;
本书不被说成含有这里专门的 \(K,\epsilon,a,R\) 或素数跨度定理。
所需专门推导及正支持步骤已在本节给出,论文证明地位不等于 Lean 冻结。

caller 的既有审计为 caller-relative-prime-spread-audit-0909.json,
SHA256 493e5f8d2432469936611f95c5d34a42ea5463bb1b29188e827b135ac14b4c47:
SymPy 1.14.0,11 项固定符号恒等式已通过,所供 host session 11977 退出 0。
这些既有核验按其原身份保留,不作为本轮重新运行的 11 个结果,
更不作为独立评审或历史数值搜索的重放许可。
本轮 CPU 仅做源文/身份/生成覆盖验证及普通编排;搜索计数和 GPU dispatch 均为 0。
完整输入限制、11 项名称、核验出处和剩余交付义务见唯一新增报告
[relative-prime-spread-proof-0910.md](../../reports/relative-prime-spread-proof-0910.md)。

**28.19 实施、canonical 摄入与尚待交付。** 本层为 caller 的 consensus-rnd:sshx
编排下 Codex CLI I12 实施,flight qgh0910-i12-relative-spread,attempt 1,
工作树 /Users/auricstudio/trureturing-qgh-variance,分支
lane/math/quantized-gh-relative-spread-0910。
实施者继承 repo-prior-exposed 的 CLAUDE.md / agents/CONTEXT.md 及完整所供 GoalArtifact;
primary 自报 external-prior-exposed,账户/项目先验未知且不可控。
不声称先验无污染或模型族多样性。primary 当时读取 pinned 仓库 URL 遇到 DisabledError,
故其仓库全文忠实性未获独立检查;此历史访问限制不会被本次本地核对抹去。

本层源文之外只加一份纸面核验/provenance 报告。全部新增 CAS 与条目仅由
~~~sh
make ingest BASE=feb497ec31f68e09ccc547a08810c398e66f3ee6 SOURCE=arithmetic-boundary-quantization
~~~
产生;旧 CAS/entry/report 保留,生成字节及生成器拥有的 EOF 空行不手修。
源文是 paper reference input,CAS 是该输入的 canonical 摄入物,
覆盖源跨度不表示其命题已由 Lean 吸收。条目的 receipts.chain_atoms 及嵌套子项
按实际 schema 读取,不用删字段来迎合临时检查。
本轮没有工具、Lean、source registry、策略或 GPU kernel 改动,
没有候选生成、旧 fixed-xi 重放、子 worker、peer review 或 worker log_ref 内容读取。
canonical 工具的实际退出码、生成身份及每个新编号单元的跨度覆盖由实施信封记录;
工具若失败须显式交回,不能手工制造通过。

源实现候选仍需 caller 在实施 terminal 后封存,再安排独立源文评审、普通仓库门和 PR。
最终 S17 MERGED 依赖 S16 MERGED;本实施不判定前驱实时 review 状态。
Git 暂存、提交、push、PR 和 merge 都归 caller,不由 I12 执行。
本节交回候选不等于独立评审、正式交付、长期研究目标完成或允许立即用作已准入剪枝规则。

## 29. 共同高度的有限混合、矩判别与所选薄层邻域

**29.1 本层范围与已有前置。** 本节为 C38 / S18 的 PAPER_ARGUMENT / repo-derived
参考输入,主数学输入是已完成的 common-height primary
fd06c983-162f-4f98-adab-2049d31a9f8d。这里处理固定相对形状和固定相对薄层,
让共同高度变化;只在最后给出步长 \((\log2,\log3,\log5)\) 的一个所选薄层邻域。
第 25.7 节已有共同平移的绝对收敛级数和首项极限,
26.23 已有六排列的精确最大式,26.24-26.25 已有正质量级数和取最大值的误差传递。
这些准确命中直接作为前置引用,不被重新宣称为新定理。
本节补出有限原子矩的恒等判据、严格最终符号界、驻点次数及高度上确界的端点语义,
接住 28.14、28.17 留下的有界相对跨度而共同高度无界的问题的一部分。

全部专门化结论是本研究设置中的纸面推导,无新颖性、优先权、Lean、formal 或
kernel-frozen 主张。GH 仍是用户未另作数学定义的原标签。
\(G\) 只比较两个已有上界,不是 RH 等价判据,本节不构成 RH 进展。
后来的整箱全薄层邻域、实际 5040 箱体和第三素数射线问题均不进入本层。

**29.2 相对形状、真实端点角点和同一比较差。** 全部对数为自然对数,
内积为通常欧氏内积。固定有限正步长 \(h_i>0\) 和有限相对形状
\(\xi_i\ge0\)、\(\min_i\xi_i=0\),其中 \(1\le i\le3\)。置
\[
X=\sum_i\xi_i,\quad Q=\sum_i h_i,\quad
c_i(T)=T+\xi_i,\quad d_i(T)=T+\xi_i+h_i,\quad A(T)=3T+X.
\]
固定有限 \(u_0<u_1\),要求闭区间 \([u_0,u_1]\) 含至少两个不同的相对角点预算
\[
B_e=X+\sum_i e_i h_i,\qquad e\in\{0,1\}^3.
\]
这里角点必须来自每行实际选取一个端点,不能用分数混合支撑点代替。
一般正实步长不保证八个预算两两不同;本节只用上述两预算要求,
不借用 28.2 的全部子集和互异假设。令
\[
M_j(T)=3T+u_j\quad(j=0,1),\qquad r=u_1-X>0.
\]
因相对角点预算均至少为 \(X\),两个不同预算保证 \(u_1>X\)。
平移后的闭薄层 \([M_0,M_1]\) 始终含上述两个角点。

沿用 26.3、27.3 的定义,记 \(f(x)=\log(1-e^{-x})\) 对 \(x>0\),并置
\[
D_T=\max_{\substack{0\le y_i\le1\\\sum_i h_i y_i\le r}}
\sum_i\bigl((1-y_i)f(c_i(T))+y_i f(d_i(T))\bigr).
\]
这是同一精确分数背包对偶值;27.3 已说明 26.10-26.11 的匹配证书适用于正实网格。
置相对均值区间、距离和包络偏移为
\[
I_r=[u_0/3,u_1/3],\quad
\delta_i=\operatorname{dist}(I_r,\{\xi_i,\xi_i+h_i\}),\quad
\rho=\sqrt{\frac{\sum_i\delta_i^2}{6}},\quad
\lambda=u_1/3-\rho,\quad\eta=u_1/3+2\rho.
\]
则绝对均值为 \(\mu=T+u_1/3\),绝对距离仍为 \(\delta_i\),
\(V_0=\sum_i\delta_i^2\) 没有额外除以 3,
\[
L=T+\lambda,\quad H=T+\eta,\quad
\Psi_T=f(H)+2f(L),\qquad G_T=D_T-\Psi_T.
\]
本节 \(\lambda\) 专指包络偏移,不是 26.3 中优化的价格变量。
在素数域 \(h_i=\log p_i\)、\(c_i=(b_i+1)h_i\)、\(b_i\in\mathbb Z_{\ge0}\) 时,
仍精确有 \(G_T=U_{\rm dual}-U_{\rm var}\),共同常数 \(\log E_S\) 抵消。

**29.3 被容许的高度端点和反向的指数端点。** 固定有限
\(T_{\rm base}\ge\log2\)。若同时要求连续放宽后的下指数非负,
须另要求每行 \(T_{\rm base}+\xi_i\ge h_i\),
因为该指数是 \((T+\xi_i)/h_i-1\)。原整数素数箱体还须逐行满足整性,
并非每个连续高度都能实现。原严格 cutoff 为
\[
Q+\log5040<M_0(T)=3T+u_0.
\]
令
\[
\tau=\frac{Q+\log5040-u_0}{3},\qquad
T_* =\max(T_{\rm base},\tau),\qquad z_*=e^{-T_*}.
\]
在 29.2 的固定形状和两角点相对薄层下,容许的连续高度域恰为
\[
\mathcal T=
\begin{cases}
[T_*,\infty),&T_{\rm base}>\tau,\\
(T_*,\infty),&T_{\rm base}\le\tau.
\end{cases}
\]
证明只需把 \(T\ge T_{\rm base}\) 与 \(T>\tau\) 取交。
特别是 \(T_{\rm base}=\tau\) 时下端点仍排除。
\(M_0<M_1\) 来自 \(u_0<u_1\),角点包含是闭的,与此严格 cutoff 分开。
原指数预算 \(T_j=M_j-Q\) 仍满足 \(\log5040<T_0<T_1\);
它们与共同高度 \(T\) 不是同一个变量。
令 \(z=e^{-T}\),相应反向区间恰为
\[
J=
\begin{cases}
(0,z_*],&T_{\rm base}>\tau,\\
(0,z_*),&T_{\rm base}\le\tau.
\end{cases}
\qquad 0<z\le z_*\le\tfrac12.
\]
无穷大不是容许高度,\(z=0\) 也从不属于 \(J\)。

**29.4 实际相对角点保证非负偏移和正支持。** 在 29.2 的假设下,
\(\eta\ge\lambda\ge0\)。为核对这一相对坐标形式,取薄层内一个实际相对角点
\(v_i=\xi_i+e_i h_i\ge0\),记 \(B=\sum_i v_i\)、\(\mu_r=u_1/3>0\)。
因为 \(\mu_r\in I_r\),有 \(\delta_i\le|v_i-\mu_r|\);
又 \(0\le B\le3\mu_r\)、\(\sum_i v_i^2\le B^2\),所以
\[
\sum_i\delta_i^2\le B^2-2\mu_r B+3\mu_r^2\le6\mu_r^2.
\]
最后的凸二次式在 \([0,3\mu_r]\) 上最大于端点,端点值为
\(3\mu_r^2\) 和 \(6\mu_r^2\)。故 \(\rho\le\mu_r\),得 \(\lambda\ge0\)。
这是 26.4、27.5 的实际角点正支持机制在相对坐标中的直接核对,
不是额外的新正支持定理。所有容许高度均满足
\(c_i,d_i,L,H\ge T\ge\log2>0\)。
定义后续指数原子
\[
a_{i,0}=e^{-\xi_i},\quad a_{i,1}=e^{-\xi_i-h_i},\quad
a_L=e^{-\lambda},\quad a_H=e^{-\eta}.
\]
每个原子都在 \((0,1]\),允许 \(a_{i,0}=1\) 或 \(a_L=1\) 等边界。
由于 \(z\le1/2\),每个 \(1-za\ge1/2>0\),所有对数和下文分母均有严格正域。
\(\rho=0\) 时 \(\lambda=\eta\),此论证不在零范数处求导。

**29.5 六个固定混合及随高度变化的最优排列。** 使用 26.23 的同一贪心权重,
本节把其中 \(u-A\) 换成固定 \(r\):对全部六个 \(\pi\in S_3\),
\[
y^\pi_{\pi(\ell)}=
\min\left\{1,\max\left\{0,
\frac{r-\sum_{m<\ell}h_{\pi(m)}}{h_{\pi(\ell)}}\right\}\right\},
\qquad w^\pi_{i,0}=1-y^\pi_i,\quad w^\pi_{i,1}=y^\pi_i.
\]
沿排列分配的总容量是 \(\min(r,Q)\),故每个混合可行,
每行权重和为 1,全部权重和为 3,且权重完全不依赖高度。
对任意固定 \(z>0\),各行收益
\(f(T+\xi_i+h_i)-f(T+\xi_i)>0\)。26.10 的经典分数背包交换/匹配价格论证
使按收益除以 \(h_i\) 非增排序的一个排列达到最优;并列时任一一致次序均可。
当 \(r\ge Q\) 时六个排列全取 \(y_i=1\),含 \(r=Q\) 和预算松弛。
因此 26.23 的准确已有结论在这里给
\[
G(z):=G_T=\max_{\pi\in S_3}G_\pi(z),
\]
\[
G_\pi(z)=\sum_{i,e}w^\pi_{i,e}\log(1-za_{i,e})
-\log(1-za_H)-2\log(1-za_L).
\]
“六个固定混合”不表示一个排列必须对所有高度最优。
排序可以随 \(z\) 改变,取全部六个的最大值已经包括这些改变;
零权重、整数最优点、并列和饱和没有被删掉。

**29.6 带符号有限测度、系数界和归一化余项。** 记
\[
\nu_\pi=\delta_{a_H}+2\delta_{a_L}
-\sum_{i,e}w^\pi_{i,e}\delta_{a_{i,e}},\qquad
A_{\pi,n}=a_H^n+2a_L^n-\sum_{i,e}w^\pi_{i,e}a_{i,e}^n.
\]
\(\delta_a\) 在本条是点质量,与距离 \(\delta_i\) 不同。
26.24 的经典对数级数在每个 \(|za|<1\) 绝对收敛,故
\[
G_\pi(z)=-\int\log(1-z\alpha)\,d\nu_\pi(\alpha)
=\sum_{n\ge1}\frac{A_{\pi,n}}n z^n.
\]
符号是“包络指数矩减混合指数矩”,不能反置。
两侧正测度各有总质量 3,各自的 \(n\) 阶矩属于 \([0,3]\),因此
\[
|A_{\pi,n}|\le3\quad(n\ge1).
\]
这比 26.25 中仍有效的三角界 6 更紧,并不否定或修改那里已有的尾界。
不要求两侧支撑不相交。于是对每个分支
\[
\left|\frac{G_\pi(z)}z-A_{\pi,1}\right|
\le3\sum_{n\ge2}\frac{z^{n-1}}n
\le\frac32\frac z{1-z}.
\]
应用 26.25 已用的有限最大值稳定性
\(|\max x_\pi-\max y_\pi|\le\max|x_\pi-y_\pi|\),得到
\[
\boxed{\left|\frac{G(z)}z-\max_\pi A_{\pi,1}\right|
\le\frac32\frac z{1-z}.}
\]
此界对本节全部许可形状、正步长、相对薄层和容许高度一致;
特别 \(G(z)/z\to\max_\pi A_{\pi,1}\),而 \(G(z)\to0\)。

**29.7 合并原子后的恒等判据和七阶上界。** 对每个固定排列,先合并
\(\nu_\pi\) 中所有相同原子,再删除所得零质量,写成
\[
\nu_\pi=\sum_{j=1}^{q_\pi}s_j\delta_{\alpha_j},\qquad
0<\alpha_j\le1,\quad \alpha_j\text{ 两两不同},\quad s_j\ne0.
\]
这里 \(q_\pi\le8\),且 \(\sum_j s_j=A_{\pi,0}=0\)。
空测度允许 \(q_\pi=0\);非空时质量为零迫使 \(q_\pi\ge2\)。
有精确等价
\[
\boxed{G_\pi\equiv0\ \Longleftrightarrow\ \nu_\pi=0
\ \Longleftrightarrow\ A_{\pi,1}=\cdots=A_{\pi,7}=0.}
\]
若非恒等,首个非零矩的阶数 \(k\) 满足 \(k\le q_\pi-1\le7\)。

证明。若零至 \(q_\pi-1\) 阶矩均零,列向量 \((s_j)\) 被矩阵
\((\alpha_j^n)_{0\le n<q_\pi,\ 1\le j\le q_\pi}\) 消去。
经典 Vandermonde 行列式为
\(\prod_{i<j}(\alpha_j-\alpha_i)\ne0\),故所有 \(s_j=0\)。
反向由零测度立即得到全部矩和函数为零。级数在 \(|z|<1\) 解析;
函数恒等为零则各 Taylor 系数为零。即使“恒等”先只指 \(J\),
它含一个开区间,解析恒等原理仍给同一结论。
零阶矩原已为零,所以前七个正阶矩足够。证明也覆盖包络两原子重合、
端点间重合、两侧互相抵消及原来的零权重,不能在合并之前声称 Vandermonde 可逆。

由 \(s\mapsto e^{-s}\) 单射,还可在偏移坐标中表述恒等条件:
\[
\sum_{i,e}w^\pi_{i,e}\delta_{\xi_i+e h_i}
=2\delta_\lambda+\delta_\eta.
\]
若 \(\lambda<\eta\),所有正端点权重须只落在这两个偏移,
总权重分别为 2 和 1;若 \(\lambda=\eta\),全部正权重须集中于该一点,总量为 3。

**29.8 单分支的严格最终符号截断。** 若 29.7 中一个非恒等分支的首个非零矩为
\(A_{\pi,k}\),则对 \(0<z<1\)
\[
\left|G_\pi(z)-\frac{A_{\pi,k}}kz^k\right|
\le\frac{3z^{k+1}}{(k+1)(1-z)}.
\]
这是对从 \(k+1\) 起的尾项使用 \(|A_{\pi,n}|\le3\) 及
\(1/n\le1/(k+1)\)。令严格正数
\[
\zeta_\pi=
\frac{(k+1)|A_{\pi,k}|}{3k+(k+1)|A_{\pi,k}|}\in(0,1).
\]
当 \(z\in J\) 且 \(0<z<\zeta_\pi\) 时,尾项绝对值严格小于
\(|A_{\pi,k}|z^k/k\),所以 \(G_\pi(z)\) 与 \(A_{\pi,k}\) 同号。
等价地,在容许高度中再要求
\[
T>\log\left(1+\frac{3k}{(k+1)|A_{\pi,k}|}\right).
\]
本估计不认证截断边界的符号,不能把严格号换成非严格号。
这是给定非零矩后的精确解析界,没有算出或认证数值指数 cutoff。

**29.9 六分支最大值的最终正、负、零分类。** 对 29.5 的全部六个分支,
用 29.7 判恒等或取其首个非零矩。若存在非恒等分支,
取这些分支的 \(\zeta_\pi\) 的最小值 \(\zeta>0\);
若全部恒等,可取 \(\zeta=1\)。对容许域中充分小的 \(z<\zeta\),精确三分如下:

- 至少一个非恒等分支首个非零矩为正,则 \(G(z)>0\)。
- 六个分支均非恒等且各自首个非零矩为负,则 \(G(z)<0\)。
- 没有正首矩分支且至少一个恒等分支,则 \(G(z)=0\)。

证明是对有限六分支同时应用 29.8 后取最大值。
“首矩”在此指每个分支的首个非零矩,各分支阶数可以不同。
全部六分支恒等时,\(G\) 在全域恒等为零。
若只有部分分支恒等,它们在全域仅保证 \(G\ge0\);
其它分支在有限高度仍可能给更大值,必须保留。
一个恒等分支本身不推出 \(G\) 在全域恒等;
上述最终零结论还需要没有正首矩分支。没有恒等分支时,
解析性与有限阶判别排除了“每个分支都无首个非零矩却不恒等”的额外情况。

**29.10 正分母、六次导数分子与至多 36 个驻点高度。** 对 29.7 合并后的非恒等分支,
在 \([0,z_*]\) 上求导得
\[
G_\pi'(z)=\frac{P_\pi(z)}{\prod_{j=1}^{q_\pi}(1-z\alpha_j)},\qquad
P_\pi(z)=\sum_{j=1}^{q_\pi}s_j\alpha_j
\prod_{\ell\ne j}(1-z\alpha_\ell).
\]
分母每一项至少为 \(1/2\),严格为正。分子最高可能次项的系数为
\[
[z^{q_\pi-1}]P_\pi
=(-1)^{q_\pi-1}\left(\prod_j\alpha_j\right)\sum_j s_j=0.
\]
所以 \(\deg P_\pi\le q_\pi-2\le6\)。
分子不可能恒零:否则 \(G_\pi\) 为常数,而其解析延拓满足 \(G_\pi(0)=0\),
迫使分支恒等,矛盾。因此一个非恒等分支在 \(J\) 中至多有六个不同驻点。
\[
\frac{d}{dT}G_\pi(e^{-T})=-zG_\pi'(z)
\]
说明这些正 \(z\) 驻点与有限驻点高度一一对应。
六个分支的驻点清单长度总和至多 36,再去掉不同分支重合的高度只会减少。
这是各光滑分支的驻点数,不把最大包络的交叉折点都称为驻点。
若 \(P_\pi(0)=0\),该根只属于无穷高极限,不计为容许驻点。
恒等分支另作常数处理,不把其恒零导数列成无穷多待检查根。

**29.11 精确上确界、端点达到与无需搜索交叉。** 固定 29.2-29.3 的数据。
对每个非恒等分支,只需评价
\[
G_\pi(0)=0,\quad G_\pi(z_*),\quad
G_\pi(z)\text{ 对所有 }0<z<z_*\text{ 且 }P_\pi(z)=0.
\]
其中端点用连续延拓值。恒等分支只贡献 0。
这些值的最大值恰为 \(\sup_{z\in J}G_\pi(z)\),且
\[
\boxed{\sup_{z\in J}G(z)=\max_{\pi\in S_3}\sup_{z\in J}G_\pi(z).}
\]
证明。各分支在紧区间 \([0,z_*]\) 连续可微,非恒等函数的最大值在端点
或内部驻点取得。\(J\) 在该紧区间中稠密,故其上确界相同。
有限最大值与上确界可交换:左侧至少为每个分支的上确界,
而每点每个分支均不超过右侧。交叉处即使不可微,
也不能制造超过全部单分支上确界的新值,因此无需另作交叉高度搜索。

\(z=0\) 永远只表示 \(T\to\infty\)。\(z=z_*\) 当且仅当
\(T_{\rm base}>\tau\) 才是容许的下高度端点;
否则只是 \(T\downarrow T_*\) 的单侧极限。
内部驻点属于容许域。全局上确界被某个容许点达到,
当且仅当至少一个分支在容许点取到该值;恒等分支在上确界为 0 时处处达到。
被排除端点的值也可能在别的容许点再次出现,故不能仅凭一个端点候选判未达到。
每个固定形状的 \(G(z)\to0\),所以即使所有有限容许高度都严格负,
上确界仍为 0。上确界为 0 既不证明存在有限零点,也不证明没有全程严格负号。
此处不能挪用 26.16-26.17 对“固定箱体、改变预算”所得的达到性和零薄层等价。
本归约系数通常含对数、指数和实数参数;没有声称有理系数算法、已认证根隔离,
或对形状连续统的一致判定程序。

**29.12 仅所选 \((2,3,5)\) 薄层的明确邻域定理。** 固定
\[
(h_1,h_2,h_3)=(a,b,c)=(\log2,\log3,\log5),
\quad m=\frac{23}{12}-2e^{-3/10}-e^{-9/10},\quad
\varepsilon_0=\frac{3m}{64}.
\]
有 \(m>0\)。对每个 \(\xi_i\ge0\)、\(\min_i\xi_i=0\)、
\(\max_i\xi_i\le\varepsilon_0\),取且只取
\[
u_0=X+b,\quad u_1=X+c,\qquad
[M_0,M_1]=[A+b,A+c].
\]
两个端点分别为只升第 2 行和只升第 3 行的实际角点预算,且 \(b<c\)。
对每个有限 \(T\ge\log2\),这个比较函数满足
\[
\boxed{G_T<-\frac m2 e^{-T},\qquad
\max_\pi A_{\pi,1}<-\frac{3m}{4}.}
\]
这里先在正支持的较宽分析域证明,原非负指数、整性和严格 5040 条件另取交;
因此特别覆盖 29.3 的每个容许高度及其中可实现的素数箱体。
29.13-29.17 给出完整证明,29.18 给出任意高的实际箱体存在性。
量词中的薄层固定为上述一对,不表示该邻域箱体的每个薄层都负。

**29.13 零形状的固定最优排列与精确距离。** 为证明 29.12,先取
\(\xi=(0,0,0)\)、\([u_0,u_1]=[b,c]\)。因 \(2<3<5<6\),
有 \(a<b<c<a+b\)。对每个 \(T>0\),
\[
\frac{f(T+h)-f(T)}h=\frac1h\int_0^h f'(T+t)\,dt
\]
随 \(h>0\) 严格递减,因为 \(f'(x)=1/(e^x-1)\) 严格递减。
严格性可由把较长区间拆为初段及导数更小的尾段立即得到。
所以每个高度均由排列 \((1,2,3)\) 最优,容量 \(r=c\) 给
\[
y=(1,\theta,0),\qquad \theta=\frac{c-a}{b}\in(0,1).
\]
这个基本混合的实际下角点预算为 \(a<b=u_0\),
不满足第 24 节的“最优分数解下角点在薄层内”充分条件。

对 \(I_r=[b/3,c/3]\),各行的下端点距离均为 \(b/3\)。
\(5<8\) 给 \(a>c/3\),\(8<15\) 给 \(a-c/3<b/3\),
故第一行选上端点。\(5<9\) 给 \(b-c/3>b/3\),
\(3<25\) 给 \(2c/3>b/3\),其余两行选下端点。因此
\[
(\delta_1,\delta_2,\delta_3)=(a-c/3,b/3,b/3),\qquad
\rho^2=\frac{(3a-c)^2+2b^2}{54}.
\]
这些是固定薄层的精确距离比较,未枚举高度、形状或其它薄层。

**29.14 零形状的有理证据与正邻域半径。** 29.13 所需的初等界为
\[
a<\tfrac7{10},\quad 1<b<\tfrac{11}{10},\quad c>\tfrac85.
\]
它们不依赖浮点对数:指数正级数在 \(7/10\) 截到四次的和大于 2,
在 \(11/10\) 截到五次的和大于 3。由对数级数相减得经典正项式
\[
\log\frac{1+t}{1-t}=2\sum_{j\ge0}\frac{t^{2j+1}}{2j+1}\quad(0<t<1).
\]
取 \(t=1/2\),第一项为 1 且余项正,得 \(\log3>1\);
取 \(t=2/3\) 的前四项,
\[
2\sum_{j=0}^3\frac{(2/3)^{2j+1}}{2j+1}
=\frac85+\frac4{15309}>\frac85.
\]
又 \(0<3a-c<1/2\),故
\[
\frac1{27}<\rho^2<\frac{(1/2)^2+2(11/10)^2}{54}
=\frac{89}{1800}<\left(\frac7{30}\right)^2.
\]
于是 \(\lambda=c/3-\rho>8/15-7/30=3/10\)。
由于
\(1/27>((9/10-8/15)/2)^2\),还得 \(\eta=c/3+2\rho>9/10\)。
整数比较 \((5/2)^8<3^7\) 给 \(\theta<7/8\)。
最后,指数级数在 \(3/10\) 截到三次的和大于 \(4/3\),
在 \(9/10\) 截到四次的和大于 \(12/5\),从而
\[
e^{-\lambda}<e^{-3/10}<\tfrac34,\qquad
e^{-\eta}<e^{-9/10}<\tfrac5{12},\qquad
2\cdot\tfrac34+\tfrac5{12}=\tfrac{23}{12}.
\]
严格号给 \(m>0\),所以 \(\varepsilon_0>0\)。这里仅使用固定有理算术与正级数;
没有半径小数值、数值见证或数值指数界的主张。

**29.15 零形状的全部阶矩严格负。** 29.13 的最优混合有端点矩
\[
W_n=2-\theta+2^{-n}+\theta3^{-n}
>\frac98+2^{-n}+\frac78\,3^{-n},\qquad n\ge1.
\]
严格性来自 \(\theta<7/8\) 及 \(3^{-n}-1<0\)。包络矩为
\(E_n=e^{-n\eta}+2e^{-n\lambda}\),系数 \(A_n=E_n-W_n\)。分别估计:
\[
W_1>\frac{23}{12},\qquad
E_1<2e^{-3/10}+e^{-9/10},\qquad A_1<-m;
\]
\[
E_2<2(3/4)^2+(5/12)^2=\frac{187}{144}
<\frac{53}{36}=\frac98+\frac14+\frac78\cdot\frac19<W_2;
\]
\[
E_n<2(3/4)^n+(5/12)^n
\le\frac{1583}{1728}<\frac98<W_n\qquad(n\ge3).
\]
最后一行用两几何幂随 \(n\) 递减,并在 \(n=3\) 精确相加。
故此最优分支的每个矩均严格负。它在所有 \(T>0\) 都最优,
所以绝对收敛级数给零形状的差
\[
G_0(z)=\sum_{n\ge1}\frac{A_n}{n}z^n<-mz\qquad(0<z<1).
\]
这不是仅最终负号。由所有六分支均不超过该分支,除以 \(z>0\) 并令 \(z\downarrow0\),
还得 \(\max_\pi A_{\pi,1}(0)=A_1<-m\)。
没有声称其它五分支的所有高阶矩都满足同一逐项负号;
它们的函数被最优分支支配已足够。

**29.16 所选薄层扰动的投影几何。** 令
\(\varepsilon=\max_i\xi_i\le\varepsilon_0\)、\(\min_i\xi_i=0\),
仍按 29.12 把相对薄层移动为 \([X+b,X+c]\)。有 \(X\le2\varepsilon\),
容量始终为 \(u_1-X=c\),所以六组权重与零形状时逐项相同。
沿用 27.3 的正交投影 \(\Pi=\operatorname{Id}-\frac13\mathbf1\mathbf1^{\mathsf T}\)。
为估计其范数,可只在此计算中把形状排列为 \((0,v,\varepsilon)\),
\(0\le v\le\varepsilon\);范数不受排列影响,并未更换步长标签。
直接有
\[
\|\Pi\xi\|_2^2=\frac23(\varepsilon^2-\varepsilon v+v^2)
\le\frac23\varepsilon^2,
\]
其差为 \(2v(\varepsilon-v)/3\ge0\)。
把相对均值区间减去 \(X/3\),即回到固定 \([b/3,c/3]\),
第 \(i\) 行端点对则移动 \(\xi_i-X/3=(\Pi\xi)_i\)。
距离对平移是 1-Lipschitz:由三角不等式先得一个方向,反向交换两端得绝对值界。
所以
\[
|\delta_i(\xi)-\delta_i(0)|\le|(\Pi\xi)_i|,\qquad
|\rho(\xi)-\rho(0)|\le\frac{\|\Pi\xi\|_2}{\sqrt6}\le\frac\varepsilon3.
\]
由 \(X/3\le2\varepsilon/3\) 得
\[
|\lambda(\xi)-\lambda(0)|\le\varepsilon,\qquad
|\eta(\xi)-\eta(0)|\le\frac43\varepsilon.
\]
这些界允许最近端点或最优排列改变,无需稳定的节点拓扑;
每个扰动薄层仍含两个指定实际角点,故 29.4 的非负偏移始终适用。

**29.17 量化扰动完成严格负号和首矩裕量。** 对 \(s\ge0\)、\(0<z<1\),
\[
0<\frac{\partial}{\partial s}\log(1-ze^{-s})
=\frac{ze^{-s}}{1-ze^{-s}}\le\frac z{1-z}.
\]
每行权重和为 1,故全部端点的加权位移和为
\(\sum_{i,e}w^\pi_{i,e}\xi_i=X\le2\varepsilon\)。
包络位移以 \(2|\lambda(\xi)-\lambda(0)|+|\eta(\xi)-\eta(0)|\)
界定,至多 \(2\varepsilon+4\varepsilon/3\)。
中间偏移保持非负,故均值定理给每个排列的一致界
\[
|G_{\pi,\xi}(z)-G_{\pi,0}(z)|
\le\frac{16}{3}\varepsilon\frac z{1-z}.
\]
对六分支取最大值,结合 29.15 和 \(z\le1/2\),得
\[
G_\xi(z)<z\left(-m+\frac{32}{3}\varepsilon\right)
\le-\frac m2z,
\qquad \frac{32}{3}\varepsilon_0=\frac m2.
\]
另对首矩直接使用 \(|(e^{-s})'|\le1\) 及同一位移和,
\[
|A_{\pi,1}(\xi)-A_{\pi,1}(0)|\le\frac{16}{3}\varepsilon,
\]
从而
\[
\max_\pi A_{\pi,1}(\xi)<-m+\frac{16}{3}\varepsilon
\le-\frac{3m}{4},\qquad \frac{16}{3}\varepsilon_0=\frac m4.
\]
零形状处已有严格号,所以闭扰动边界 \(\varepsilon=\varepsilon_0\) 仍严格。
这完成 29.12,常数界定的是缩放差 \(e^TG_T\),不是无界高度上的未缩放负常数。

**29.18 零形状附近任意高的实际素数幂箱体。** 29.12 的邻域确实被无穷多个
\((2,3,5)\) 实际箱体达到。这里需要三个下坐标同时接近;
27.13 的准确已有命题只把两个坐标接近、第三个抬高,故引用其无理性机制,
再用经典二维齐次同时逼近,不把那条重述为本条。
设 \(\alpha=(a/b,a/c)\)。对每个整数 \(N\ge1\),
将 \([0,1)^2\) 分成 \(N^2\) 个边长 \(1/N\) 的半开小方格。
\(N^2+1\) 个小数部分向量 \(j\alpha\)、\(0\le j\le N^2\),有两个同格。
相减给整数 \(q,k_2,k_3\),满足
\[
1\le q\le N^2,\qquad
|qa-k_2b|<b/N,\qquad |qa-k_3c|<c/N.
\]
这些分母具有无界子序列。否则某个有限的正 \(q\) 会在误差趋零时反复出现,
迫使 \(qa/b\in\mathbb Z\),与 27.13 已证的 \(\log2/\log3\) 无理性矛盾。
等价地,有界正 \(q\) 的到整数距离具有严格正的最小值。
沿趋无穷的子序列,\(k_2,k_3\) 也趋无穷,丢弃有限前缀后均为正整数。

取实际下坐标
\[
(c_1,c_2,c_3)=(qa,k_2b,k_3c),\qquad
(b_1,b_2,b_3)=(q-1,k_2-1,k_3-1)\in\mathbb Z_{\ge0}^3.
\]
令 \(T=\min c_i\)、\(\xi_i=c_i-T\)。则 \(T\to\infty\),
\(\min\xi_i=0\),且由上面的两误差得
\(\max\xi_i\le2\max(b,c)/N\to0\)。
所以最终 \(\max\xi_i\le\varepsilon_0\),非负指数条件成立,
且 \(A+b>Q+\log5040\)。所选实际薄层
\([A+\log3,A+\log5]\) 由两个实际角点封端,宽度严格正,
因此在原域内满足 \(G_T<-(m/2)e^{-T}\)。
\(T\) 无界保证有无穷多个不同箱体。这是抽屉存在性证明,
没有执行该构造、产生指数候选、计算数值见证或有效指数 cutoff。
唯一分解只用于上述两个对数比的无理性,未被当作一般非齐次密度定理。

**29.19 矩零集、形状连续统和实际格点转移的剩余义务。** 对任意有界形状和
任意相对薄层,\(\max_\pi A_{\pi,1}\) 的符号及其零集上更高矩的符号仍未统一解决。
29.7-29.11 是每个固定实例的有限解析归约,不把形状连续统变成有限列表。
当首个非零矩趋零或接近恒等测度时,29.8 的截断可以趋向 \(z=0\);
没有一致非零量级控制,不能从逐点最终符号推出整个区域的统一共同高度 cutoff。

把任意指定固定形状转移到素数格点,仍须给出下指数整数序列,
使其归一化偏移趋向该形状,或证明适用的非齐次同时逼近定理。
29.18 只提供零形状附近的齐次转移,不提供任意形状密度,
也不推断倒数素数对数的一般有理线性独立。
在极限形状首个非零矩阶数 \(k>1\) 时,普通偏移收敛还可能制造更低阶矩并压过 \(z^k\)。
例如对一个拟转移的分支,足够的逐矩条件为
\[
A_j(T)=o(e^{-(k-j)T})\quad(1\le j<k),\qquad
A_k(T)\longrightarrow A_k^*\ne0.
\]
因为 \(z=e^{-T}\),这些低阶项除以 \(z^k\) 后趋零,
而统一系数界使 \(k\) 阶之后的尾项为 \(O(z^{k+1})\)。
须按最大值问题处理所有相关分支:证明最终负号不能漏掉一个可能为正或恒等的分支;
证明正号则至少要保住一个分支的正首项。未证明这些更强扰动速率时,
固定形状的高阶结果不能自动转成实际格点结论。

每个固定形状的全部分支及 \(G\) 都趋零,故本节没有无界高度上的统一未缩放负裕量。
第 26 节的 25 槽薄层归约若与本节合成,仍须逐项保留其原假设、guards、
固定箱体量词和达到性;本节不运行它,不修改稳定行号或实现剪枝。
一般三素数的全形状全薄层比较、有限零点分类及 RH 问题仍 OPEN,
本结果不完成长期研究目标。

**29.20 经典出处、重叠核对与 primary 的历史限制。** 分数背包、
对数幂级数、有限测度矩界、Vandermonde 可逆性、有理函数微分、
紧区间极值和抽屉齐次同时逼近均为经典方法。
分数背包的已有来源记录直接引用 26.28;
本次另实际取回 NIST DLMF [4.6.E1](https://dlmf.nist.gov/4.6.E1.tex) 的对数级数,
MathWorld [Vandermonde Determinant](https://mathworld.wolfram.com/VandermondeDeterminant.html)
式 (1)-(2),及 Encyclopedia of Mathematics
[Dirichlet theorem](https://encyclopediaofmath.org/wiki/Dirichlet_theorem)
中 Diophantine approximations 小节的同时逼近与抽屉原理说明。
这里使用的 \(Q=N^2\) 齐次特例已在 29.18 自足证明;
没有把这些经典出处说成含有本比较差的专门邻域结论。
三个限定站点的 Google 查询仅返回跳转页,DLMF 的完整 4.6 页面请求为 HTTP 403;
成功取回的公式与两个条目、实际查询和内容身份均记录于本层唯一报告。
收敛域和所需特殊化由本节的正支持及纸面证明核对。

primary 自报请求 pinned source 时遇 DisabledError,未独立看到其字节、SHA256、25.7 或
26 节全文,把先行源前提标为 ASSUMED-UNVERIFIED;它对原创性未作评定。
这些是该次 primary 的历史访问/新颖性限制,不会因本次读取本树旧源而变成
“primary 当时已经核查”。本次亲读 25.7、26.2-26.4、26.10-26.17、26.23-26.25、
27.2-27.5 的相关条款、27.11-27.14、28.14-28.19 等先行文本,区分准确重叠与新增组合。
本节专门推导的当前归属为 repo-derived,不以历史的“未评定”充当现行 provenance 状态,
不声称穷尽文献检索或文献中无先例。

**29.21 对 27.14 集合措辞的追加澄清。** 27.13 证明的是分离 guard 未排除的
剩余箱体集合无限,所以该 guard 的已排除区域不是余有限集。
另一个事实是 27.11 给出一条固定正整数指数射线上的无限已排除尾部,
所以已排除集合本身也无限。两个事实相容,但描述的是两个不同集合。
27.14 的“有限补集”措辞应按上述两句分别理解。
这里仅追加源文澄清,不修改 27.14,不新增定理,也不重开已结算的 S16 review。

**29.22 本层产地、固定核验与 canonical 摄入。** 本实施为 caller 的
consensus-rnd:sshx 1.0.0-beta.42 编排下 I13,flight qgh0910-i13-common-height,
attempt 1,工作树 /Users/auricstudio/trureturing-qgh-common-height,
分支 lane/math/quantized-gh-common-height-0910,immutable BASE
66001d3b87d7063c5dd2a4ea97e51f8f1b876afa。
实施者为 Codex CLI,继承完整所供 GoalArtifact 及 repo-prior-exposed 的仓库规范;
没有子 worker 或同轮独立 review 票。primary 自报 external-prior-exposed,
账户/项目上下文未知且不可控,其具体 serving-model/routing 未独立确认;
本层不从 ACTUAL GPT PRO 的 caller 标签推断模型版本或模型族多样性。

主 envelope 为 pro-common-height-envelope-0910.json,SHA256
7bba088ffbdf3ae327aa0bbf34c17905e90a7510252a0e3f699ba28a27d6eda7,
只消费 conclusion,所有 log_ref 保持不透明。
caller-common-height-audit-0910.json 是已完成先行审计,
记载 21 项成功固定精确核验、完整纸面审计及原 host exit 0,不是本轮 peer review。
本层仅将同一 21 项算式适配成报告内自足固定证明证书并运行,
原审计和原一次性程序字节不变;程序、实际结果和输入身份见
[common-height-finite-mixtures-0910.md](../../reports/common-height-finite-mixtures-0910.md)。
该证书不接受候选参数,不是可复用搜索器。CPU 仅用于固定核验、源和引用一致性;
没有指数、高度、形状、素数或薄层候选生成,没有 GPU、daemon 或旧搜索重放。

本节前的完整 224856 字节 / 4141 行源前缀保持不变,SHA256
69702718f3602c508146f50cf70ebd78ef81adb09c2b826041d357e4a7dc11c8。
所有历史 CAS、entry 和报告保留。源追加后唯一摄入门为
~~~sh
make ingest BASE=66001d3b87d7063c5dd2a4ea97e51f8f1b876afa SOURCE=arithmetic-boundary-quantization
~~~
全部新增 CAS/entry 仅由该命令生成,包括可能出现的历史末单元 terminal-LF 变体和
自动 chain children;生成字节及其 EOF 空行不手修。摄入只提供源文内容地址,
不表示数学被 Lean 吸收。本层源实现和独立源评审可在隔离树中推进,
由 caller 在本次 implementation terminal 后封存、安排评审与普通仓库门;
最终交付依赖 S17 MERGED。Git 暂存、提交、push、PR、merge 均由 caller 所有,
本实施不执行,也不读取另一在飞 target 或同轮 reviewer 工件。
交回本层候选不等于已独立批准、已正式交付或长期目标完成。

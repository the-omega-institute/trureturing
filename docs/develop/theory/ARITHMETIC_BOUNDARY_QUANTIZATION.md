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

## 30. 三素数 (2,3,5) 的整箱全薄层邻域与无界共同高度

**30.1 本层结果、状态与准确重叠。** 本节是 C41 / S19 的 PAPER_ARGUMENT / repo-derived
参考输入,只追加已完成的 balanced-all-slabs primary
8cfd404d-43c8-42f9-a5be-22e0811bc05a 及 caller 固定核验所支持的结果。
对步长 \((\log2,\log3,\log5)\),零相对形状的每个两角点实薄层均满足
\(e^TG<-1/60\);整个闭邻域 \(\max_i\xi_i\le1/480\) 均满足
\(e^TG<-1/120\),共同高度为任意有限 \(T\ge\log2\)。
第 26.4-26.15 节已有正支持、下预算饱和、临界节点和上尾论证,
26.23-26.24 已有六混合及对数矩展开,27.3 已定义欧氏投影,
29.13、29.16、29.18 已分别给出零形状贪心次序、投影估计和齐次格点逼近。
这些准确命中在本节直接复用;本层补的是去掉 cutoff 的有限支配应用、全部八节点的
无限矩证书和整箱统一裕量、改进为 2 的扰动常数及原域的精确非空阈值。
29.12-29.18 的所选薄层定理保留原量词,不被倒写为先前已有全薄层定理。
本节不提出新颖性、优先权、RH 或 Lean/kernel-frozen 主张。

**30.2 固定三步长、两个预算域与同一比较差。** 全部对数为自然对数,
固定
\[
a=\log2,\quad b=\log3,\quad c=\log5,\quad
h=(a,b,c),\quad Q=a+b+c.
\]
令有限 \(T\ge a\)、\(\xi_i\ge0\)、\(\min_i\xi_i=0\),并置
\[
\varepsilon=\max_i\xi_i,\quad X=\sum_i\xi_i,\quad A=3T+X,
\quad c_i=T+\xi_i,\quad d_i=c_i+h_i,\quad C_i=\{c_i,d_i\}.
\]
宽分析域 \(\mathscr W_{T,\xi}\) 由所有有限实数 \(M_0<M_1\) 组成,
要求闭区间 \([M_0,M_1]\) 至少包含两个不同的端点角点预算
\(\sum_i(c_i+e_i h_i)\)、\(e\in\{0,1\}^3\)。这里“角点”始终是每行选一个端点,
不是分数混合支撑点;连续参考箱体的角点不因此成为实际整数素数幂。
此域允许负下预算、恰等于角点的任一端点、\(M_1\ge A+Q\) 及上预算松弛,
不要求 \(M_0>Q+\log5040\),也不要求 \(c_i\ge h_i\)。
原素数问题还要求整数 \(b_i\ge0\)、\(c_i=(b_i+1)h_i\),且薄层属于
\[
\mathscr S_{T,\xi}=
\{(M_0,M_1)\in\mathscr W_{T,\xi}:Q+\log5040<M_0\}.
\]
原指数预算 \(T_j=M_j-Q\) 满足 \(\log5040<T_0<T_1\),与共同高度 \(T\) 分开。

沿用 26.3、27.3、29.2 的同一精确对偶、平方距离和包络:
\[
f(x)=\log(1-e^{-x}),\qquad
D(M_1)=\max_{\substack{0\le y_i\le1\\\sum_i h_i y_i\le M_1-A}}
\sum_i\bigl((1-y_i)f(c_i)+y_i f(d_i)\bigr),
\]
\[
I=[M_0/3,M_1/3],\quad \mu=M_1/3,\quad
\delta_i=\operatorname{dist}(I,C_i),\quad V_0=\sum_i\delta_i^2,
\quad \rho=\sqrt{V_0/6},
\]
\[
L=\mu-\rho,\quad H=\mu+2\rho,\quad
\Psi=f(H)+2f(L),\quad G=D-\Psi.
\]
距离和投影使用通常欧氏内积;\(V_0\) 没有额外除以 3。
两角点包含保证 \(M_1>A\),所以对偶可行域非空紧致。
26.10-26.11 的匹配价格证书保证它等于原价格下确界,包含并列、整数最优点和全上端点。
在原素数域仍有 \(G=U_{\rm dual}-U_{\rm var}\),共同的 \(\log E_S\) 精确抵消。

**30.3 宽域上的正支持。** 对 30.2 的任一薄层,取其中一个端点角点 \(v\),
令 \(\bar v=\sum_i v_i/3\in I\)、\(w_i=v_i-T\ge0\)。因为 \(v_i\in C_i\),
\[
\sum_i\delta_i^2\le\sum_i(v_i-\bar v)^2
=\sum_i w_i^2-3(\bar v-T)^2
\le6(\bar v-T)^2.
\]
最后一步是 \(\sum_iw_i^2\le(\sum_iw_i)^2=9(\bar v-T)^2\),
取等允许若干 \(w_i=0\)。故
\[
0\le\rho\le\bar v-T\le\mu-T,\qquad H\ge L\ge T>0.
\]
这是 26.4 的同一角点证明,现在显式用于不含 cutoff 的宽域。
它只需一个实际端点角点,不使用下预算符号、上预算有界区间或严格 5040 条件。
因而映射前后、\(\rho=0\) 和端点包含等号都有效。
定义 \(\lambda=L-T\)、\(\eta=H-T\),得到 \(0\le\lambda\le\eta\);
本节 \(\lambda\) 是包络偏移,不是对偶价格。

**30.4 去掉 cutoff 后的有限支配及其边界。** 固定 30.2 的箱体,
将八个预算严格排列为 \(\beta_0<\cdots<\beta_7\);
互异性来自不同子集乘积 \(1,2,3,5,6,10,15,30\)。
26.6-26.15 的有限支配证明在 \(\mathscr W_{T,\xi}\) 中仍成立,
其保留集合只删去原 eligibility 中的 \(\beta_{j-1}>Q+\log5040\) 一项。
以下核对全部步骤,不把原严格域定理直接用于域外。

给定 \(u=M_1\),令 \(j=\max\{s:\beta_s\le u\}\ge1\),
第二大的可行角点为 \(b_* =\beta_{j-1}\)。两角点包含给 \(M_0\le b_*\),
提高下预算至 \(b_*\) 保留两角点,使每个 \(\delta_i\) 弱增。
对 \(F(\mu,r)=f(\mu+2r)+2f(\mu-r)\)、\(r\ge0,\mu-r>0\),
\[
F_\mu=f'(H)+2f'(L)>0,\qquad F_r=2(f'(H)-f'(L))\le0.
\]
由 \(f''<0\),固定均值时 \(F\) 对不同半径严格递减,即使较小半径为零。
故 \(G(M_0,u)\le G(b_*,u)\),取等恰为全部行距离不变,
等价于两次 \(V_0\) 相等;不要求原来已经 \(M_0=b_*\)。

固定 \(b_*\)、\(\alpha=b_*/3\),26.7 的逐行距离公式为
\[
\delta_i(\mu)=
\begin{cases}
\alpha-d_i,&d_i\le\alpha,\\
(c_i-\mu)_+,&\alpha\le c_i,\\
\min\{\alpha-c_i,(d_i-\mu)_+\},&c_i<\alpha<d_i.
\end{cases}
\]
唯一内部向下斜率跳变要求
\(c_i<\alpha<(c_i+d_i)/2\),发生在
\(u_*=3(c_i+d_i)-b_*\)。其它端点过零是 \(-1\to0\) 的凸折点。
在不含活跃切换的任一闭段,各距离非负凸,欧氏范数的非负象限单调性和三角不等式
使 \(\rho\) 凸。26.5、26.9 的严格 Jensen 论证可原样使用:
\(F\) 联合严格凹,因为 \((\mu,r)\mapsto(\mu+2r,\mu-r)\) 单射且 \(f\) 严格凹;
对不同均值取凸组合,先用 \(\rho(\mu_t)\le t\rho_1+(1-t)\rho_2\) 和半径非增性,
再用 \(F\) 的严格凹性,得 \(\Psi(b_*,u)\) 严格凹。
中间点的下支持至少为两端下支持的凸组合,由 30.3 至少为 \(T\)。
故证明覆盖距离过零、全部距离为零及最近端点并列,不在零范数处作微分。

对固定箱体,收益密度与容量无关。26.10-26.11 的背包折点全是实际前缀角点,
并列只合并斜率,所以 \(D\) 在每个 \([\beta_j,\beta_{j+1}]\) 仿射。
因此上述无切换段上的 \(G\) 严格凸,内部值严格小于至少一个端点值。
左外端点已是相邻对;右外端点 \((\beta_{j-1},\beta_{j+1})\)
再提高下端点到 \(\beta_j\) 即被相邻对弱支配,等号仍恰为距离不变。
反射点只在严格内部时另留:
\[
1\le j\le6,\quad b_* =\beta_{j-1},\quad
c_i<b_*/3<(c_i+d_i)/2,\quad \beta_j<u_*<\beta_{j+1}.
\]
这些严格号的等号不产生额外内部节点,由相邻端点或兼容距离公式处理。
当 \(u\ge\beta_7\),\(D\) 恒为全上端点值,扩大均值区间使 \(\rho\) 非增,
增大均值严格增大 \(F\),故饱和后的 \(G(\beta_6,u)\) 严格递减。
综上,每个宽域薄层都被七个相邻对或满足上述 guards 的反射对之一弱支配。
全过程仅使用正支持和两角点包含,没有使用严格 5040 cutoff。

**30.5 零形状的全部反射 guards 与稳定槽 10。** 取 \(\xi=0\),写
\(\beta_s=3T+B_s\),其中
\[
(B_0,\ldots,B_7)=(0,a,b,c,a+b,a+c,b+c,Q),\qquad
(e^{B_0},\ldots,e^{B_7})=(1,2,3,5,6,10,15,30).
\]
对反射区间指标 \(j=1,\ldots,6\),令
\(u=B_{j-1}\)、\((P_j,L_j,U_j)=(e^{B_{j-1}},e^{B_j},e^{B_{j+1}})\)。
坐标素数 \(p\in\{2,3,5\}\) 的反射上相对预算为 \(\log(p^3/P_j)\),
30.4 的 eligibility 精确等价于
\[
P_j>1,\qquad P_j^2<p^3,\qquad L_jP_j<p^3<U_jP_j.
\]
这是指数函数单调性给出的纯整数判断;没有施加原 cutoff。
下表逐一处理全部 18 个固定反射槽,每个拒绝格给一条已经失败的必要条件:
\[
\begin{array}{c|c|l|l|l}
j&(P_j,L_j,U_j)&p=2&p=3&p=5\\\hline
1&(1,2,3)&7:\ P_j=1&8:\ P_j=1&9:\ P_j=1\\
2&(2,3,5)&10:\ 4<8,\ 6<8<10&11:\ 27>10&12:\ 125>10\\
3&(3,5,6)&13:\ 9>8&14:\ 27>18&15:\ 125>18\\
4&(5,6,10)&16:\ 25>8&17:\ 27<30&18:\ 125>50\\
5&(6,10,15)&19:\ 36>8&20:\ 36>27&21:\ 125>90\\
6&(10,15,30)&22:\ 100>8&23:\ 100>27&24:\ 125<150
\end{array}
\]
唯一幸存者是稳定反射 slot 10,相对预算对为 \((a,2a)\),且 \(b<2a<c\) 来自 \(3<4<5\)。
这里沿用 26.21 的零起点坐标 \(i=0,1,2\) 计算
\(\mathrm{slot}=7+3(j-1)+i\),并未更改稳定 ID。
下文纸面相邻节点标号 \(j=1,\ldots,7\) 对应 raw slots \(0,\ldots,6\),
其 \(j\) 不等于 slot;反射仍只写 slot 10。最终保留八个节点。

**30.6 每个正高度的严格贪心次序。** 零形状时,步长 \(h>0\) 的收益密度是
\[
\sigma_T(h)=\frac{f(T+h)-f(T)}h=\frac1h\int_0^h f'(T+s)\,ds.
\]
这是 29.13 的同一个经典平均导数论证,与薄层下端点无关。
若 \(0<h<h'\),前段平均严格大于 \(f'(T+h)\),尾段平均严格小于它,
因为 \(f'\) 严格递减;把两段按长度加权便得 \(\sigma_T(h')<\sigma_T(h)\)。
因此每个 \(T>0\) 均有严格次序 \(a,b,c\)。对任意容量 \(v\ge0\),可选最优权重
\[
y_1=\operatorname{clip}(v/a),\quad
y_2=\operatorname{clip}((v-a)/b),\quad
y_3=\operatorname{clip}((v-a-b)/c),\quad
\operatorname{clip}(t)=\min(1,\max(0,t)).
\]
容量恰在前缀端点时两侧公式一致;\(v\ge Q\) 时全取 1。
严格密度次序用于零形状,不被假设为任意扰动形状的共同最优次序。

**30.7 八个节点的精确距离、权重与矩。** 对 30.5 的每个相对对 \((u,v)\),
均有 \(u\ge0\)。令 \(q_i=3\delta_i\),则从区间 \([u/3,v/3]\) 到 \(\{0,h_i\}\) 的距离得
\[
q_i=\begin{cases}
u-3h_i,&3h_i<u,\\
0,&u\le3h_i\le v,\\
\min\{u,3h_i-v\},&3h_i>v.
\end{cases}
\]
若 \(3h_i=u\) 或 \(v\) 则距离为零;若 \(u=3h_i-v\),两个最近端点并列且值相同。
特别 slot 10 的第一行是这样的并列。定义
\[
R=\sqrt{\sum_iq_i^2/6},\quad \rho=R/3,\quad
\lambda=(v-R)/3,\quad\eta=(v+2R)/3,
\]
\[
W_n=\sum_i(1-y_i+y_i e^{-nh_i}),\quad
E_n=2e^{-n\lambda}+e^{-n\eta}\quad(n\ge1).
\]
逐行代入距离分支和 30.6 的权重给完整表:
\[
\begin{array}{c|c|c|c}
\text{纸面节点/raw slot}&(u,v)&(q_1,q_2,q_3)&(y_1,y_2,y_3)\\\hline
1/0&(0,a)&(0,0,0)&(1,0,0)\\
2/1&(a,b)&(a,a,a)&(1,(b-a)/b,0)\\
3/2&(b,c)&(3a-c,b,b)&(1,(c-a)/b,0)\\
4/3&(c,a+b)&(2a-b,2b-a,c)&(1,1,0)\\
5/4&(a+b,a+c)&(0,3b-a-c,a+b)&(1,1,(c-b)/c)\\
6/5&(a+c,b+c)&(c-2a,2b-c,2c-b)&(1,1,(c-a)/c)\\
7/6&(b+c,Q)&(b+c-3a,0,2c-a-b)&(1,1,1)\\
\text{反射}/10&(a,2a)&(a,a,a)&(1,a/b,0)
\end{array}
\]
表中的全部分支可由 30.10 的三个严格对数区间作有理线性比较认证,
零向量单独判等;报告给出不调用浮点对数的可执行核对。
令 \(r=a/b\)、\(\theta=(c-a)/b\)、\(s=b/c\)、\(t=a/c\),则按同一行序
\[
\begin{array}{c|l}
j&W_n\\\hline
1&2+2^{-n}\\
2&1+r+2^{-n}+(1-r)3^{-n}\\
3&2-\theta+2^{-n}+\theta3^{-n}\\
4&1+2^{-n}+3^{-n}\\
5&s+2^{-n}+3^{-n}+(1-s)5^{-n}\\
6&t+2^{-n}+3^{-n}+(1-t)5^{-n}\\
7&2^{-n}+3^{-n}+5^{-n}\\
\mathrm{slot}\ 10&2-r+2^{-n}+r3^{-n}
\end{array}
\]
这些是每个正整数 \(n\) 的恒等式,不是在有限个矩上拟合所得。

**30.8 两个累积质量界推出全部正整数矩的经典积分引理。**
令 \(\nu\) 为 \([0,1]\) 上总质量为 3 的非负测度。
对 \(0\le s\le3\),记 \(K_\nu(s)\) 为它最大的 \(s\) 单位质量之积分,
允许在边界原子处分割质量。等价地,按数值递减积分其分位函数;
该函数的边际斜率非增,所以 \(K_\nu\) 凹,且 \(K_\nu(0)=0\)。
若 \(0\le h_*\le l_*\le1\) 且
\[
K_\nu(2)\ge2l_*,\qquad K_\nu(3)\ge2l_*+h_*,
\]
则对每个整数 \(n\ge1\),
\[
\int x^n\,d\nu(x)\ge2l_*^n+h_*^n.
\]

证明。对 \(\nu_*=2\delta_{l_*}+\delta_{h_*}\),其累积积分在 \([0,2]\) 为
\(sl_*\),在 \([2,3]\) 为 \(2l_*+(s-2)h_*\)。凹函数位于连接其端点的弦之上,
由 \(s=0,2,3\) 的三个比较即得所有 \(s\) 上 \(K_\nu(s)\ge K_{\nu_*}(s)\),
也覆盖 \(l_*=h_*\)、\(h_*=0\) 和两条假设取等。
对任意 \(t\ge0\),取所有 \(x>t\) 的质量、\(x=t\) 处任意分割,直接得到
\[
\int(x-t)_+\,d\nu(x)=\max_{0\le s\le3}\{K_\nu(s)-st\}.
\]
一向因为任何所选质量的 \(x-t\) 积分不超过正部积分,另一向由上述选择达到。
因此 \(\nu\) 的正部积分也支配 \(\nu_*\)。对 \(n\ge2\),
\[
x^n=n(n-1)\int_0^1(x-t)_+t^{n-2}\,dt\quad(0\le x\le1),
\]
由直接积分至 \(t=x\) 得证;非负积分交换后得到全部高阶矩。
\(n=1\) 就是总积分 \(K_\nu(3)\)。这属于经典递增凸序/弱大序的积分比较,
不是要求一阶矩相等的普通大序。若另有
\(e^{-\lambda}<l_*\)、\(e^{-\eta}<h_*\),则严格单调的正整数幂立即给
\(E_n<2l_*^n+h_*^n\le W_n\) 对所有 \(n\ge1\) 同时成立。

**30.9 全八行有理大序证书与首矩裕量。** 对 30.7 的最优权重,取总质量为 3 的端点测度
\[
\nu=\sum_{i=1}^3\bigl((1-y_i)\delta_1+y_i\delta_{1/p_i}\bigr),\qquad
(p_1,p_2,p_3)=(2,3,5).
\]
这里 \(\delta_x\) 表示点质量,与行距离 \(\delta_i\) 不同。
零权重允许删去,每行总质量仍是 1,且 \(W_n=\int x^n\,d\nu\)。
下表给出严格原子上界 \(e^{-\lambda}<l_*\)、\(e^{-\eta}<h_*\),
以及弱下界 \(W_1\ge w_*\)、\(K_\nu(2)\ge k_*\):
\[
\begin{array}{c|c|c|c|c|c}
\text{节点}&l_*&h_*&w_*&k_*&w_*-2l_*-h_*\\\hline
1&4/5&4/5&5/2&2&1/10\\
2&5/6&8/15&67/30&9/5&1/30\\
3&3/4&2/5&23/12&25/16&1/60\\
4&3/4&5/16&11/6&3/2&1/48\\
5&5/8&2/7&47/30&23/18&13/420\\
6&5/9&9/40&289/210&47/42&101/2520\\
7&2/5&3/14&31/30&5/6&2/105\\
\mathrm{slot}\ 10&3/4&1/2&37/18&5/3&1/18
\end{array}
\]
每行均有 \(0<h_*\le l_*\le1\)、\(k_*\ge2l_*\) 及
\(w_*-2l_*-h_*\ge1/60\)。原子界在 30.10 证明。
其余两列并非数值猜测:把原子按 \(1>1/2>1/3>1/5\) 排序并取最大两单位质量,
用 30.7 的 \(r,\theta,s,t\) 可精确列成
\[
\begin{array}{c|c|c}
\text{节点}&W_1&K_\nu(2)\\\hline
1&5/2&2\\
2&11/6+2r/3&3/2+r/2\\
3&5/2-2\theta/3&2-\theta/2\\
4&11/6&3/2\\
5&31/30+4s/5&5/6+2s/3\\
6&31/30+4t/5&5/6+2t/3\\
7&31/30&5/6\\
\mathrm{slot}\ 10&5/2-2r/3&2-r/2
\end{array}
\]
例如第 2 行在 1 处质量 \(1+r\),再取 \(1-r\) 单位的 \(1/2\),得到 \(3/2+r/2\);
第 5 行在 1 处质量 \(s\),再取完整的 \(1/2\) 和 \(1-s\) 单位的 \(1/3\),
得到 \(5/6+2s/3\)。其它行同样按上述固定排序直接积分。
精确整数比较
\[
2^5>3^3,\quad2^3<3^2,\quad5^8<2^8\cdot3^7,\quad
3^3>5^2,\quad2^7>5^3
\]
分别给 \(3/5<r<2/3\)、\(\theta<7/8\)、\(s>2/3\)、\(t>3/7\)。
按各仿射式的单调方向代入即可逐行得到 \(w_*,k_*\)。
primary 中的压缩乘法串在本节明确解释为 `2^8 * 3^7`,原始 primary 字节不改。
第 3 行有理裕量恰为 \(1/60\)、第 4 行 \(k_*=2l_*\),但严格原子界仍保证
\(W_1-E_1>w_*-2l_*-h_*\ge1/60\),并不会在这些表格等号处丢失严格性。

**30.10 严格原子界的完整固定有理证书。** 首先认证
\[
693/1000<a<694/1000,\quad1098/1000<b<1099/1000,\quad
1609/1000<c<1610/1000.
\]
对每个固定 \(p=2,3,5\),令 \(y=(p-1)/(p+1)\in(0,1)\),经典对数正级数给
\[
S_p=2\sum_{k=0}^{19}\frac{y^{2k+1}}{2k+1}<\log p
<S_p+\frac{2y^{41}}{41(1-y^2)}.
\]
左侧尾项严格正;右侧以 \(1/(2k+1)\le1/41\) 对 \(k\ge20\) 几何求和,
且 \(k>20\) 时严格,所以右界也严格。
报告中的有理运算把两端严格夹入上列千分数区间。
第 1 节点有 \(R=0\)、\(\lambda=\eta=a/3\),而 \(125<128\) 给
\(e^{-a/3}=2^{-1/3}<4/5\)。第 2 节点与 slot 10 有 \(R=a/\sqrt2\),
由 \(2(480/1000)^2<(693/1000)^2\) 和
\((694/1000)^2<2(500/1000)^2\) 得 \(480/1000<R<500/1000\)。

对其余五行,30.7 的精确 \(q\) 及上述对数区间逐坐标给下表的向外界;
零坐标精确为零,非零坐标严格在界内。\(q^-\le1000q\le q^+\),并有
\(R_-/1000<R<R_+/1000\):
\[
\begin{array}{c|c|c|c}
j&q^-&q^+&(R_-,R_+)\\\hline
3&(469,1098,1098)&(473,1099,1099)&(660,664)\\
4&(287,1502,1609)&(290,1505,1610)&(900,910)\\
5&(0,990,1791)&(0,995,1793)&(830,840)\\
6&(221,586,2119)&(224,589,2122)&(902,904)\\
7&(625,0,1425)&(630,0,1429)&(635,638)
\end{array}
\]
全部 \(q^-\) 非负,每行精确整数比较
\(6R_-^2<\sum_i(q_i^-)^2\)、\(\sum_i(q_i^+)^2<6R_+^2\)
与 \(R^2=\sum q_i^2/6\) 证明严格平方根界。
以 \(v\) 的对数区间下端点 \(v_-\) 代入
\(\lambda>(v_--R_+/1000)/3\)、\(\eta>(v_-+2R_-/1000)/3\),得到
\[
\begin{array}{c|c|c}
\text{节点}&\lambda\text{ 的严格下界}&\eta\text{ 的严格下界}\\\hline
2&19/100&2/3\\
3&3/10&19/20\\
4&29/100&7/6\\
5&12/25&13/10\\
6&3/5&3/2\\
7&23/25&31/20\\
\mathrm{slot}\ 10&29/100&3/4
\end{array}
\]
最后令 \(P_N(x)=\sum_{k=0}^N x^k/k!\)。对 \(x>0\),指数正尾项给
\(e^x>P_N(x)\);以下十三个固定有理不等式 \(P_N(x)>t_*\)
完整认证 30.9 的倒数原子界:
\[
\begin{array}{c|r|c@{\qquad}c|r|c}
x&N&t_*&x&N&t_*\\\hline
19/100&2&6/5&2/3&2&15/8\\
3/10&3&4/3&19/20&3&5/2\\
29/100&3&4/3&7/6&5&16/5\\
12/25&3&8/5&13/10&4&7/2\\
3/5&3&9/5&3/2&5&40/9\\
23/25&4&5/2&31/20&5&14/3\\
3/4&3&2&&&
\end{array}
\]
例如 \(\lambda>19/100\) 且 \(P_2(19/100)>6/5\),故 \(e^{-\lambda}<5/6\)。
其它行取相应倒数同证;\(29/100\) 的多项式由第 4 节点与 slot 10 共用。
所有算式均在单一报告内给出自足可执行的固定有理核验,不用浮点 exp/log/sqrt,
没有生成高度、矩阶、素数或薄层候选。

**30.11 八节点的无限矩符号与全薄层统一缩放界。**
30.8-30.10 对每个保留节点给
\[
E_n<W_n\quad\text{对每个整数 }n\ge1,\qquad E_1-W_1<-1/60.
\]
令 \(z=e^{-T}\in(0,1/2]\)。复用 26.24、29.6 的同一对数展开,
零形状最优混合由 30.6 在每个高度确定,故
\[
G_0(z)=\sum_{n=1}^{\infty}\frac{E_n-W_n}{n}z^n.
\]
原子都在 \((0,1]\),两侧质量均为 3,所以 \(|E_n-W_n|\le3\),级数绝对收敛。
所有后续项严格负,首项已有严格裕量,因此
\[
\frac{G_0(z)}z<-\frac1{60}
\]
在全部八节点同时成立。对任意 \(\mathscr W_{T,0}\) 中的薄层,
30.4-30.5 在同一高度给一个保留节点弱支配它。
乘以正数 \(e^T=1/z\) 保持支配方向,从而
\[
\boxed{e^TG_0(M_0,M_1)<-1/60
\quad\text{对每个有限 }T\ge\log2\text{ 和每个宽域两角点薄层}.}
\]
这包含 \(T=\log2\)、端点角点、距离并列和上尾。
无限矩结论来自积分引理,不是检查前若干矩再假定尾项符号;
这里没有使用 26.25 的有限 24 项截断充当全矩证明。

**30.12 减去 \(X\) 的预算对应及其严格域限制。** 对任意 30.2 的形状和宽域薄层,
写 \(M_j^\xi=3T+X+r_j\),对应零形状预算为
\(M_j^0=3T+r_j=M_j^\xi-X\)。两箱的同一角点指标 \(e\) 的预算分别是
\[
3T+X+\sum_i e_i h_i,\qquad 3T+\sum_i e_i h_i.
\]
同时减去 \(X\) 精确保留闭区间中的每一个角点及端点等号,
并保留 \(r_0<r_1\) 和两角点数,故在两个宽域之间给双射。
两箱的背包容量同为 \(r_1>0\)。这对 \(r_0<0\)、角点上预算和 \(r_1\ge Q\) 一样成立。
但 \(M_0^\xi>Q+\log5040\) 不必推出 \(M_0^0>Q+\log5040\)。
因此后续传递使用 30.11 已在宽域证明的界;不能暗中把预算对应说成原严格域的双射。

**30.13 投影位移对所有薄层的统一几何界。** 沿用 27.3 的
\(\Pi=\operatorname{Id}-\mathbf1\mathbf1^{\mathsf T}/3\)。
30.12 中减去共同 \(T\) 后,形状箱的均值区间为
\([X/3+r_0/3,X/3+r_1/3]\),端点对为 \(\{\xi_i,\xi_i+h_i\}\)。
把均值区间再减去 \(X/3\),它与零形状的区间相同,第 \(i\) 行端点则平移
\(\xi_i-X/3=(\Pi\xi)_i\)。距离在平移下 1-Lipschitz:
对任一点对用三角不等式并取下确界,再交换两个平移即得绝对值界。
继而用反三角不等式,
\[
|\delta_i^\xi-\delta_i^0|\le|(\Pi\xi)_i|,\qquad
|\rho_\xi-\rho_0|\le\frac{\|\Pi\xi\|_2}{\sqrt6}.
\]
若 \(\varepsilon>0\),仅为计算范数可将形状排列为 \((0,v,\varepsilon)\),
\(0\le v\le\varepsilon\),并未重排步长标签。29.16 的同一恒等式给
\[
\|\Pi\xi\|_2^2=\frac23(\varepsilon^2-\varepsilon v+v^2)
\le\frac23\varepsilon^2.
\]
差为 \(2v(\varepsilon-v)/3\),等号恰在 \(v=0\) 或 \(v=\varepsilon\)。
令 \(u=X/3\)、\(t=\rho_\xi-\rho_0\),则
\[
\varepsilon/3\le u\le2\varepsilon/3,\quad |t|\le\varepsilon/3,\qquad
\lambda_\xi-\lambda_0=u-t,\quad\eta_\xi-\eta_0=u+2t.
\]
所以 \(|\lambda_\xi-\lambda_0|\le\varepsilon\)、
\(|\eta_\xi-\eta_0|\le4\varepsilon/3\)。当 \(\varepsilon=0\) 时全部相同。
这些界完全不依赖最近端点分支是否改变或某个反射槽是否活跃。

**30.14 共同六混合使对偶增量落入同一正区间。** 对 30.12 的共同容量 \(r_1\),
直接使用 26.23、29.5 的六排列权重
\[
y^\pi_{\pi(\ell)}=
\operatorname{clip}\left(\frac{r_1-\sum_{m<\ell}h_{\pi(m)}}{h_{\pi(\ell)}}\right),
\qquad \pi\in S_3.
\]
它们只依赖步长和容量,两箱完全相同,每个混合可行且总质量为 3。
每个箱体在每个高度都至少有一个排列按其自身收益密度排序,故由已有匹配证书
\(D_\xi=\max_\pi D_{\pi,\xi}\)、\(D_0=\max_\pi D_{\pi,0}\)。
这允许两个最大值使用不同排列;\(r_1\ge Q\) 时全部混合都取全上端点。
对 \(F_z(s)=\log(1-ze^{-s})\)、\(s\ge0\)、\(0<z<1\),
\[
0<F_z'(s)=\frac{ze^{-s}}{1-ze^{-s}}\le K_z:=\frac z{1-z}.
\]
形状第 \(i\) 行的两个偏移都增加 \(\xi_i\ge0\),每行权重和为 1,故
\[
0\le D_{\pi,\xi}-D_{\pi,0}\le XK_z\le2\varepsilon K_z.
\]
若逐项 \(a_\pi\le b_\pi\le a_\pi+C\),取最大值仍有
\(\max a_\pi\le\max b_\pi\le\max a_\pi+C\)。因此
\[
0\le D_\xi-D_0\le2\varepsilon K_z.
\]
没有对最优排列求导,也没有假设贪心次序对形状或高度稳定。

**30.15 包络增量的非负性及常数 2 的传递。** 在 30.13 的记号中 \(u-t\ge0\),且
\[
2|u-t|+|u+2t|\le2\varepsilon.
\]
若 \(u+2t\ge0\),左侧是 \(3u=X\le2\varepsilon\);
若 \(u+2t<0\),左侧是 \(u-4t\le u+4\varepsilon/3\le2\varepsilon\)。
由 30.3,两箱偏移均非负,连接每个对应偏移的线段也非负,
故 30.14 的导数界给 \(|\Psi_\xi-\Psi_0|\le2\varepsilon K_z\)。
还须保留增量方向,不能把两个绝对界相加后就称作常数 2。
当 \(t\ge0\),\(u\ge t\) 使两个偏移均弱增,\(F_z\) 递增,于是 \(\Psi_\xi\ge\Psi_0\)。
当 \(t<0\),先在旧半径 \(\rho_0\) 下把均值提高 \(u\),再在新均值下将半径由
\(\rho_0\) 降到 \(\rho_\xi\ge0\)。平移使包络弱增,降半径也使包络弱增,因为
\[
\partial_\rho\Psi=2\bigl(F_z'(\eta)-F_z'(\lambda)\bigr)\le0.
\]
中间下偏移先平移非负量,后随半径下降而上升,始终在正支持所许可的非负偏移域。
因此两个增量都属于同一区间:
\[
D_\xi-D_0\in[0,2\varepsilon K_z],\qquad
\Psi_\xi-\Psi_0\in[0,2\varepsilon K_z].
\]
两区间内数之差的绝对值至多区间长度,得到
\[
\boxed{|G_\xi(z;r_0,r_1)-G_0(z;r_0,r_1)|
\le2\varepsilon\frac z{1-z}.}
\]
这是对所有对应宽域薄层的统一估计。它使用共同六混合及区间距离的 Lipschitz 性,
不使用稳定临界节点拓扑、固定最优排列或最近端点 min 的可微性。
29.17 的 \(16/3\) 是仍有效的较弱常数,不被修改为错误的历史结果。

**30.16 闭半径 \(1/480\) 内每个薄层的严格负号。** 由 30.11、30.15 和
\(z=e^{-T}\le1/2\),对每个 \(\mathscr W_{T,\xi}\) 中的薄层有
\[
e^TG_\xi< -\frac1{60}+\frac{2\varepsilon}{1-z}
\le-\frac1{60}+4\varepsilon.
\]
因此若 \(0\le\varepsilon\le1/480\),
\[
\boxed{e^TG_\xi<-1/120\quad
\text{对每个有限 }T\ge\log2\text{ 和每个两角点宽域薄层}.}
\]
\(-1/60+4/480=-1/120\) 恰好取等,但第一步严格,故在闭半径边界和
\(T=\log2\) 同时取等时结论仍严格。\(\varepsilon=0\) 则保留更强的 \(-1/60\) 界。
原素数域取交后同样有效,其中没有 \(G=0\) 的等号薄层。
原提议的更小半径 \(3(1/60)/64=1/1280\) 当然也可用,但本结论不以它代替已证闭半径。

**30.17 齐次同时逼近给无界的实际素数幂箱体。** 复用 29.18 的抽屉构造,
其结论本来就给零相对形状附近任意高的实际箱体;本层把同一序列用于新的全薄层半径。
为写清量词,对每个整数 \(N\ge1\),把 \([0,1)^2\) 分成 \(N^2\) 个半开方格,
将 \(N^2+1\) 个点 \((\{ja/b\},\{ja/c\})\)、\(0\le j\le N^2\) 放入其中。
两点同格,相减得整数 \(q,m,n\),满足
\[
1\le q\le N^2,\qquad |qa-mb|<b/N,\qquad |qa-nc|<c/N.
\]
任何有界正 \(q\) 集合的 \(\operatorname{dist}(qa/b,\mathbb Z)\) 最小值严格正,
因为 \(a/b\) 无理:若 \(qa=mb\) 且 \(q>0\),则 \(2^q=3^m\),违反唯一分解。
故误差趋零时分母不可能保持有界。可取 \(N\to\infty\)、\(q\to\infty\) 的子序列,
此时 \(m,n\to\infty\),最终全为正整数。
取实际下坐标和非负整数箱体参数
\[
(c_1,c_2,c_3)=(qa,mb,nc),\qquad
(b_1,b_2,b_3)=(q-1,m-1,n-1).
\]
令 \(T=\min_i c_i\)、\(\xi_i=c_i-T\)。由误差界,
\[
T\to\infty,\qquad0\le\max_i\xi_i\le(b+c)/N\longrightarrow0.
\]
这里任意两坐标之差由相对于 \(qa\) 的两误差之和控制,不需倒数对数的一般线性独立。
无界 \(T\) 给无穷多个不同箱体,它们最终进入闭半径 \(1/480\),
于是每个箱体的每个被容许薄层均满足 30.16。
这是齐次存在性证明,没有执行指数构造或给出有效数值指数 cutoff。
等高参考箱体是连续模型;正的不同素数幂不能精确相等,
这里证明的是其对数下坐标之差趋零,不是精确相等的正素数幂。

**30.18 严格 5040 域非空的充要阈值。** 对任一本节箱体,
第二大角点为 \(A+b+c=A+Q-a\),最大角点为 \(A+Q\)。
存在两角点薄层且 \(Q+\log5040<M_0\) 当且仅当
\[
\boxed{A>\log2+\log5040.}
\]
必要性:含两个角点的下端点不超过全箱第二大角点,故
\(Q+\log5040<M_0\le A+Q-a\)。
充分性:取闭薄层 \([A+Q-a,A+Q]\),两端都是实际角点,宽度为 \(a>0\),
且下端点严格超过 cutoff。\(A=a+\log5040\) 时没有这样的薄层,
因为 cutoff 是严格的;不能把“下角点恰等于 cutoff”算入可容许域。
这是 26.16 的非空判据在本三步长的直接专门化,并非新的一般有限箱体判据。
对 30.17 的实际整数序列,\(A\ge3T\to\infty\),所以原域最终非空。
从那时起,其全部原域实薄层都满足严格缩放界 \(e^TG<-1/120\)。

**30.19 缩放、形状和研究目标的边界。** 取任一固定相对形状和固定相对两角点薄层,
29.6 的六有限混合给 \(|A_{\pi,n}|\le3\),从而
\(|G_\pi(z)|\le3\sum_{n\ge1}z^n/n\to0\),有限最大值也给 \(G(z)\to0\)。
例如零形状的最后相邻薄层在充分大高度进入严格 cutoff 域,其 \(G\) 仍趋于零。
因此本节的统一常数只约束 \(e^TG\),不存在由此得到的无界高度上统一未缩放负裕量。
\(T=\infty\)、\(z=0\) 是极限,不是容许点。

闭半径只覆盖 \(\xi_i\ge0,\min\xi_i=0,\max\xi_i\le1/480\) 的区域,
不覆盖所有形状或整个有界相对跨度残余。
齐次同时逼近只给零形状附近的实际序列,不证明任意非零形状的非齐次密度,
不提供连续共同平移的实际素数格点族或有效指数上限。
指数坐标配上通常欧氏内积才有本节的投影;格点与薄层编码没有新增正交性,
也没有产生新的 KL 损失恒等式。
GH 仍是用户的原标签,本节不为它发明数学定义。
两个上界之差为负既不是 RH 等价判据也不是 RH 证明或 RH 进展。
其它素数三元组、一般素数、其余形状和 RH 仍 OPEN;
后来的 \((2,3,7)\)、实际 fixed5040、translated5040 和第三素数射线结果不属于本层。
本次源实现不完成持续研究目标。

**30.20 当前文献归属、primary 访问限制及固定核验产地。**
本节专门的八节点、裕量、扰动组合及格点应用当前标为 repo-derived,
没有以历史的未评定原始措辞作为现行 provenance 标签。
经典分数背包、范数凸性和严格端点论证的已有核对直接引用 26.28;
本次亲读本树第 26 节、27.3-27.5、29.1-29.22 和第 10 节度量定义作重叠检查。
新增的聚合积分比较使用经典递增凸序:本次实际取得 Gushchin–Borzykh,
*Integrated quantile functions: properties and applications*,
Modern Stochastics: Theory and Applications 4(4) (2017),285–314,
DOI [10.15559/17-VMSTA88](https://doi.org/10.15559/17-VMSTA88),
[原文](https://arxiv.org/pdf/1801.00977) §2.3 Theorem 5(ii) 及其证明
(PDF p.10 / 期刊 p.294),核对递增凸序、正部积分及积分分位函数的等价关系。
把质量 3 的测度除以 3 后可与其概率约定对照;30.8 已直接证明本节所需版本。
另实际取回 NIST DLMF [4.6.E1](https://dlmf.nist.gov/4.6.E1.tex) 的对数级数,
及 Encyclopedia of Mathematics 的
[Dirichlet theorem](https://encyclopediaofmath.org/wiki/Dirichlet_theorem)
中同时逼近与抽屉原理小节。30.17 只用已自足证明的 \(Q=N^2\) 齐次特例。
这些出处只支持经典工具,不被说成含有本节专门素数比较定理。
本次另试的 EoM Majorization 页面返回 HTTP 404;检索不构成文献穷尽或优先权判定。

primary 原始 envelope 的 SHA256 为
5ad15f1f87730e33edd6ef2e9045aa4255a4a85efb1e456312b438da91c5288c。
只消费其中 conclusion,log_ref 保持不透明。它自报 pinned source 获取遇 DisabledError,
未读源字节或独立核对其 SHA256,且没有成功取回外部文献;
本次源/文献读取不改变那些历史事实。原压缩串 `2^83^7` 留在原始输入,
本节只按其数学意图显式写为 `2^8 * 3^7`。
primary 自报 34 项固定有理检查;caller 的原审计另记录总计 64 项成功检查、
host exit 0 及纸面核验,包含那 34 项及额外的分支、eligibility、权重和半径核对。
它们是已完成的先行数学输入,不是本轮同轮 peer review,也不能合称为 primary 跑了 64 项。
本实施把固定算式改成报告内不依赖绝对临时路径的自足证书并实际执行,
原 caller 审计和程序不改。全部输入身份、逐单元映射、当前调用结果及检索收据见
[balanced-prime-235-all-slabs-0910.md](../../reports/balanced-prime-235-all-slabs-0910.md)。

**30.21 单一源/报告/摄入层与交付义务。** 本实施是 caller 提供的
consensus-rnd:sshx 1.0.0-beta.42 runner 合约下的 I14,flight
qgh0910-i14-balanced-all-slabs,attempt 1,实施者为 Codex CLI。
未查阅另一版本的 skill,没有 native subagent、委派、额外 oracle 或本轮独立评审票;
只继承已供 GoalArtifact 与仓库先验,不声称无先验或模型族多样性。
primary 的具体 serving-model/routing 未在本实施独立鉴定,实际 GPT PRO 身份是 caller 的来源记录。
工作树为 /Users/auricstudio/trureturing-qgh-balanced-all-slabs,
分支 lane/math/quantized-gh-balanced-all-slabs-0910,immutable BASE 为
a8e208440d8a3f465a7b20c82ededbb27ee95026。
准备文件旧的 predecessor-in-flight 行只属准备时状态,当前以这个实际封存 S18 base 为准;
没有读取 S18 活跃评审 target、result、任何 worker 日志、log_ref 内容或 caller 转录。

第 1-29 节完整前缀保持 254298 字节、4743 个 LF,SHA256
c5e1fa97fff5921fe5ba10d84b0268c884caab112fb32beed0c92027ee1aa3f5,
每个历史 CAS、entry 和报告均保留。只允许本节、一个报告及下列 canonical 摄入输出:
~~~sh
make ingest BASE=a8e208440d8a3f465a7b20c82ededbb27ee95026 SOURCE=arithmetic-boundary-quantization
~~~
每个新 CAS/YAML、raw/normalized 指纹、源的完整连续跨度和有序 chain children
在实施结论中逐项给出;指纹/cas_ref 带 `sha256:`,子 atom_id 为裸 hash。
生成器拥有的 EOF、历史末单元 terminal-LF 变体和自动 child 均原样保留,
不手修 producer 字节。摄入是参考输入的内容寻址,不是 Lean 吸收或冻结。
CPU 仅运行固定证明证书和必要编排,没有指数、高度、形状、素数或薄层候选生成,
没有 GPU、daemon、旧搜索重放、工具/Lean/frozen 改动或广泛 build/preflight。
源、报告与摄入组成同一可审查的内容层;不能在未保真源语义时单独交付派生地址,
也没有理由把后来定理或新搜索绑入这一层。
caller 在本次 implementation terminal 后负责封存、独立评审和普通仓库门,
最终 S19 交付仍等待 S18 MERGED;本实施不执行暂存、commit、push、PR、merge 或生命周期动作。
候选交回不是独立批准、正式交付或长期研究目标完成。

## 31. 三素数 (2,3,7) 的九节点证书与整箱全薄层邻域

**31.1 结果、状态及前节引理的定义域审计。** 本节为 C43 / S20 的
PAPER_ARGUMENT / repo-derived 参考输入,实施已完成的实际 GPT PRO primary
107ae020-e13b-4e13-a174-c5f1544a39d1 和既有 caller 固定核验所支持的数学。
对步长 \((\log2,\log3,\log7)\),每个有限 \(T\ge\log2\) 的零形状两角点实薄层
满足 \(e^TG<-1/40\);整个闭形状邻域 \(\max_i\xi_i\le1/320\) 满足
\(e^TG<-1/80\)。这些量词包括所有下预算、端点包含和无界上预算。

先核对可复用陈述的字面域。30.2 固定的是 \((2,3,5)\),故
30.3-30.7、30.9-30.19 不能只替换一个符号就当作本三元组的既有定理;
尤其 30.4 的宽域归约、30.6 的零形状次序、30.12-30.15 的传递及
30.17 的格点序列都继承该限制。29.13、29.16、29.18 也分别限于此前的
\((2,3,5)\) 所选薄层或序列。本节为所需的新域补齐这些论证。
26.2-26.16 的原定理要求实际整数素数箱体和严格 cutoff,不能直接判本节连续宽域。
27.3 的正实网格匹配对偶证书和通常欧氏投影可复用;
29.2、29.4-29.6 的有限混合与级数机制具有正实步长域,但 29.3 的严格高度域
不冒充本节宽域。30.8 则是独立陈述的 \([0,1]\) 上质量 3 测度引理,
没有素数假设,可在逐项核对其假设后直接使用。31.10 写出其承重积分步骤。
本层专门组合不作优先权、新颖性、RH 或 Lean/kernel-frozen 主张。

**31.2 两个预算域、端点角点和同一归一化。** 全部对数为自然对数,固定
\[
a=\log2,\quad b=\log3,\quad c=\log7,\quad h=(a,b,c),\quad Q=a+b+c.
\]
取有限 \(T\ge a\)、有限 \(\xi_i\ge0\)、\(\min_i\xi_i=0\),置
\[
\varepsilon=\max_i\xi_i,\quad X=\sum_i\xi_i,\quad A=3T+X,\quad
c_i=T+\xi_i,\quad d_i=c_i+h_i,\quad C_i=\{c_i,d_i\}.
\]
宽分析域 \(\mathscr W_{T,\xi}\) 是所有有限实数对 \(M_0<M_1\),使闭区间
\([M_0,M_1]\) 至少含两个不同的实际端点角点预算
\(A+\sum_i e_i h_i\)、\(e\in\{0,1\}^3\)。这里“实际端点角点”指在该箱体中
每行确实选一个端点,不能以分数混合点替代;连续参考箱体的角点不因此具有整数性。
宽域允许 \(M_0\le0\)、端点恰为角点、\(M_1\ge A+Q\) 及预算松弛,
不要求 \(c_i\ge h_i\) 或严格 5040 cutoff。对任意本节连续箱体先记 cutoff 子域
\[
\mathscr S_{T,\xi}=\{(M_0,M_1)\in\mathscr W_{T,\xi}:Q+\log5040<M_0\}.
\]
称作原素数域时另要求 \(c_i=(b_i+1)h_i\)、\(b_i\in\mathbb Z_{\ge0}\)。
原指数预算 \(T_j=M_j-Q\) 满足 \(\log5040<T_0<T_1\),与共同高度 \(T\) 分开。

沿用 26.3、27.3 的同一比较,定义
\[
f(x)=\log(1-e^{-x}),\qquad
D(M_1)=\max_{\substack{0\le y_i\le1\\\sum_i h_i y_i\le M_1-A}}
\sum_i\bigl((1-y_i)f(c_i)+y_i f(d_i)\bigr),
\]
\[
I=[M_0/3,M_1/3],\quad\mu=M_1/3,\quad
\delta_i=\operatorname{dist}(I,C_i),\quad V_0=\sum_i\delta_i^2,\quad
\rho=\sqrt{V_0/6},
\]
\[
L=\mu-\rho,\quad H=\mu+2\rho,\quad\Psi=f(H)+2f(L),\quad G=D-\Psi.
\]
内积为通常欧氏内积,\(V_0\) 没有额外除以 3。两角点保证 \(M_1>A\),
故最大值在非空紧可行域上达到。27.3 的正实网格匹配证书使此最大值等于
原非负价格下确界,包括并列、整数最优点及全上端点。
在原素数域仍精确有 \(G=U_{\rm dual}-U_{\rm var}\),共同的 \(\log E_S\) 抵消。

**31.3 宽域正支持,包括零方差和零形状的严格下支持。**
取薄层内一个角点 \(x_i\in C_i\),记 \(\bar x=\sum_i x_i/3\in I\)、
\(w_i=x_i-T\ge0\)。三角距离和非负交叉项给
\[
V_0\le\sum_i(x_i-\bar x)^2
=\sum_iw_i^2-3(\bar x-T)^2\le6(\bar x-T)^2.
\]
因而 \(0\le\rho\le\bar x-T\le\mu-T\),得到 \(H\ge L\ge T>0\)。
这个证明只用端点角点包含与 \(c_i\ge T\),不使用整数指数或 cutoff;
角点在端点、某个 \(w_i=0\) 和 \(\rho=0\) 都包括在内。

当 \(\xi=0\),写 \(u=M_0-3T\)、\(v=M_1-3T\)。八角点的第二小偏移为
\(a>0\),所以 \(v\ge a\)。若 \(u\le0\),每行的下端点 0 属于相对均值区间,
\(\rho=0\),于是 \(L=T+v/3>T\)。若 \(u>0\),每行可选下端点作距离上界,
\(\delta_i\le u/3\),所以
\[
\rho\le\frac{u}{3\sqrt2},\qquad
L\ge T+\frac{v-u/\sqrt2}{3}>T
\]
因为 \(v>u>0\)。因此零形状的每个宽域薄层都有严格正偏移
\(\lambda=L-T>0\)、\(\eta=H-T\ge\lambda\)。本节 \(\lambda\) 是偏移,不是对偶价格。

**31.4 每个正高度的零形状贪心次序。** 对任意 \(T>0\) 和 \(h>0\),
\[
\sigma_T(h)=\frac{f(T+h)-f(T)}h=\frac1h\int_0^h f'(T+s)\,ds,
\qquad f'(x)=\frac1{e^x-1}>0,\quad f''(x)<0.
\]
若 \(h<h'\),初段导数平均严格大于 \(f'(T+h)\),尾段平均严格小于它;
按两段长度加权,得 \(\sigma_T(h')<\sigma_T(h)\)。因此本节的
\(a<b<c\) 在所有正高度都有严格收益密度次序 \(a,b,c\)。
对任意容量 \(v\ge0\),最优权重可选为
\[
y_1=\operatorname{clip}(v/a),\quad
y_2=\operatorname{clip}((v-a)/b),\quad
y_3=\operatorname{clip}((v-a-b)/c),\quad
\operatorname{clip}(s)=\min(1,\max(0,s)).
\]
其依据是 27.3 的匹配证书:写收益 \(g_i=f(T+h_i)-f(T)\),对可行 \(y\) 和
价格 \(s\ge0\),有 \(\sum_i y_i g_i\le sv+\sum_i(g_i-sh_i)_+\)。
令 \(s\) 为最后部分填充行的密度,上列权重使每一步取等。
容量 0 取全下端点和 \(s\ge\max_i\sigma_i\);容量 \(v\ge Q\) 取全上端点及
\(s=0\)。前缀端点的左右公式一致,不要求最优解真正分数。
唯一可能的折点 \(a,a+b,Q\) 都是本三元组的角点偏移。
此固定次序只用于零形状;扰动传递不假定它继续最优。

**31.5 下预算饱和的等号及完整上尾。** 定义
\[
F(\mu,r)=f(\mu+2r)+2f(\mu-r),\quad r\ge0,\ \mu-r>0.
\]
直接有 \(F_\mu=f'(H)+2f'(L)>0\)、\(F_r=2(f'(H)-f'(L))\le0\)。
固定均值时 \(F\) 对不同半径严格递减,因为 \(r>0\) 时导数严格负;
即使较小半径为零也一样。\((\mu,r)\mapsto(\mu+2r,\mu-r)\) 单射,
对严格凹的 \(f\) 应用 Jensen 即得 \(F\) 联合严格凹。

零形状角点顺序为
\[
(B_0,\ldots,B_7)=(0,a,b,a+b,c,a+c,b+c,Q),\quad
(e^{B_0},\ldots,e^{B_7})=(1,2,3,6,7,14,21,42).
\]
这里 \(6<7\) 与前节的 \(5<6\) 改变了中间两角点的顺序。
若 \(B_j\le v<B_{j+1}\)、\(1\le j\le6\),两角点包含必给 \(u\le B_{j-1}\)。
提高下相对预算至 \(B_{j-1}\) 保留两个角点,使每行距离弱增,故
\(G(u,v)\le G(B_{j-1},v)\)。此处简写 \(G(u,v)\) 表示绝对预算
\((3T+u,3T+v)\) 的差。等号恰在全部行距离不变时成立,
等价于两次 \(V_0\) 相等,不要求原下预算已经饱和。
当 \(v\ge Q\),最大可行下预算是 \(B_6\),同一结论有效。
在饱和上尾 \(G(B_6,v)\) 中,\(D\) 恒为全上端点值;增大 \(v\) 扩大距离区间,
使 \(\rho\) 非增,又严格提高均值,所以 \(\Psi\) 严格增加、\(G\) 严格下降。
比较中间点 \((\mu_2,\rho_1)\) 的下支持大于旧下支持,仍在正域。
因此最后相邻对 \((B_6,Q)\) 支配整个上尾,包含 \(v=Q\) 和任意有限松弛。

**31.6 无切换凸片与九节点归约所需的全部边界。**
在饱和条带 \(u=B_{j-1}\ge0\)、\(v\in[B_j,B_{j+1}]\) 上,令
\(q_i=3\delta_i\)。相对端点为 \(\{0,h_i\}\),故精确地
\[
q_i=\begin{cases}
u-3h_i,&3h_i<u,\\
0,&u\le3h_i\le v,\\
\min\{u,3h_i-v\},&3h_i>v.
\end{cases}
\qquad
R=\sqrt{\sum_iq_i^2/6},\quad\rho=R/3.
\]
端点相等给零距离,最近端点并列给两式同值。唯一内部向下斜率跳变是
\(v_*=3h_i-u\),且必须同时满足
\[
u>0,\qquad2u<3h_i,\qquad B_j<3h_i-u<B_{j+1}.
\]
否则该行在条带内是非负常数或 \((3h_i-v)_+\)。在每个不含上述内部切换的闭片,
各 \(q_i\) 非负凸;逐项凸性、非负象限范数单调性和三角不等式给 \(R\) 凸。
距离过零的 \(-1\to0\) 折点保留凸性,无须另添节点。

用 \(F\) 对半径非增和联合严格凹性,先把片内半径提高到两端半径的凸组合,
再用严格 Jensen,即得 \(\Psi\) 在片上严格凹。中间下支持是两端下支持的凸组合,
至少为 \(T\),所以复合没有越出定义域;不同 \(v\) 给不同均值,即使半径全为零
仍有严格 Jensen 步。31.4 的所有背包折点都是角点,所以 \(D\) 在整条带仿射,
\(G\) 在每个无切换片严格凸,内部值小于至少一个端点值。
左外端点是相邻对;右外端点 \((B_{j-1},B_{j+1})\) 再饱和为
\((B_j,B_{j+1})\),由 31.5 弱支配。切换落在条带端点无需新节点,
其公式连续兼容;严格 guards 的任一等号都不增加内部反射。
结合 31.5 的上尾,每个宽域零形状薄层均被一个相邻节点或通过 guards 的内部反射
弱支配。这是在本三元组宽域内补证的归约,没有从 30.4 或原严格域偷换量词。

**31.7 全部十八个整数 eligibility 与稳定反射槽。** 对 \(j=1,\ldots,6\),令
\((P_j,L_j,U_j)=(e^{B_{j-1}},e^{B_j},e^{B_{j+1}})\)。31.6 的 guards 精确等价于
\[
P_j>1,\qquad P_j^2<p_i^3,\qquad L_jP_j<p_i^3<U_jP_j,
\quad(p_1,p_2,p_3)=(2,3,7).
\]
反射上相对预算是 \(\log(p_i^3/P_j)\)。继承 26.21 的 j-major 标号,
以零起点坐标 \(i=0,1,2\) 写 \(\mathrm{slot}=7+3(j-1)+i\),只借用槽编号,
不引入那里的有限指数搜索域。下表每个拒绝格列出一条失败的必要条件,
同时给出全部乘积,只比较整数 \(8,27,343\):
\[
\begin{array}{c|c|c|c|l|l|l}
j&(P_j,L_j,U_j)&P_j^2&(L_jP_j,U_jP_j)&p=2&p=3&p=7\\\hline
1&(1,2,3)&1&(2,3)&7:P_j=1&8:P_j=1&9:P_j=1\\
2&(2,3,6)&4&(6,12)&10:4<8,\ 6<8<12&11:27>12&12:343>12\\
3&(3,6,7)&9&(18,21)&13:9>8&14:27>21&15:343>21\\
4&(6,7,14)&36&(42,84)&16:36>8&17:36>27&18:343>84\\
5&(7,14,21)&49&(98,147)&19:49>8&20:49>27&21:343>147\\
6&(14,21,42)&196&(294,588)&22:196>8&23:196>27&24:196<343,\ 294<343<588
\end{array}
\]
只有 raw slots 10、24 幸存,对应 \((u,v)=(a,2a)\)、\((a+c,2c-a)\)。
其内部性分别是 \(3<4<6\) 和 \(21<49/2<42\)。
加上相邻 slots 0 至 6,恰得九个保留节点;这是固定整数资格核对,
不是按近似数值选拓扑,也不是把前节的八节点表照搬到素数 7。

**31.8 九节点的精确距离与贪心权重。** 下表给 31.6 距离公式的完整代入。
类型 I 表示 \(y=(1,\theta,0)\)、\(\theta=(v-a)/b\);
类型 II 表示 \(y=(1,1,\theta)\)、\(\theta=(v-a-b)/c\)。
每行均有 \(0\le\theta\le1\),在 \(v=a+b\) 处两种权重一致。
\[
\begin{array}{c|c|c|c}
\mathrm{slot}&(u,v)&(q_1,q_2,q_3)&\text{类型}\\\hline
0&(0,a)&(0,0,0)&\mathrm I\\
1&(a,b)&(a,a,a)&\mathrm I\\
2&(b,a+b)&(2a-b,b,b)&\mathrm I\\
3&(a+b,c)&(3a-c,3b-c,a+b)&\mathrm {II}\\
4&(c,a+c)&(0,3b-a-c,c)&\mathrm {II}\\
5&(a+c,b+c)&(c-2a,2b-c,a+c)&\mathrm {II}\\
6&(b+c,Q)&(b+c-3a,0,2c-a-b)&\mathrm {II}\\
10&(a,2a)&(a,a,a)&\mathrm I\\
24&(a+c,2c-a)&(c-2a,3b-2c+a,a+c)&\mathrm {II}
\end{array}
\]
全部非零分支的线性对数符号由 31.11 的严格有理区间认证,零向量精确判等;
反射槽的并列最近端点用同值两式,没有数值容差。
每行的 \(R\) 如 31.6,并有
\[
\lambda=\frac{v-R}{3},\qquad\eta=\frac{v+2R}{3}.
\]
权重只依赖本表的相对容量,对每个正高度均最优;本表没有采样高度。

**31.9 有限带符号测度与绝对收敛矩展开。** 对每个保留节点,令
\[
\nu=\left(3-\sum_i y_i\right)\delta_1+\sum_i y_i\delta_{1/p_i},\qquad
W_n=\int x^n\,d\nu(x),\qquad E_n=2e^{-n\lambda}+e^{-n\eta}.
\]
这里 \(\delta_x\) 是点质量,不同于行距离 \(\delta_i\)。\(\nu\) 非负、总质量为 3,
支撑在 \([0,1]\);零权重可删。其全部正整数矩为
\[
W_n=\begin{cases}
2-\theta+2^{-n}+\theta3^{-n},&\mathrm I,\\
1-\theta+2^{-n}+3^{-n}+\theta7^{-n},&\mathrm {II}.
\end{cases}
\]
定义有限带符号测度 \(\sigma=2\delta_{e^{-\lambda}}+\delta_{e^{-\eta}}-\nu\),
则 \(\int x^n\,d\sigma=E_n-W_n\)。31.3 给所有指数原子在 \((0,1]\),
而有限 \(T\ge a\) 给 \(z=e^{-T}\in(0,1/2]\)。几何级数积分所得
\(\log(1-zx)=-\sum_{n\ge1}(zx)^n/n\) 在此绝对收敛,因此
\[
G_0(z)=-\int\log(1-zx)\,d\sigma(x)
=\sum_{n\ge1}\frac{E_n-W_n}{n}z^n.
\]
两侧正测度各质量 3,故 \(|E_n-W_n|\le3\),足以控制绝对收敛和 \(z\to0\) 的极限。
符号是“包络指数矩减混合指数矩”,没有反转比较方向。
同一有限测度表示、绝对收敛及系数绝对值界也适用于任意固定零形状宽域相对薄层:
取 31.4 的 clipped 最优权重和 31.3 的正偏移即可逐字展开,不要求该薄层是节点。
上尾权重取全 1;只对节点使用上面的类型 I/II 未截断公式。

**31.10 最大两单位质量与总质量控制每个正整数矩。**
可直接应用 30.8 的一般测度引理:这里 \(\nu\) 确为 \([0,1]\) 上质量 3 的非负测度,
并非把此前专属于 \((2,3,5)\) 的节点结论推广。写 \(K(s)\)、\(0\le s\le3\),
为取 \(\nu\) 最大的 \(s\) 单位质量时的积分,允许分割边界原子。
其递减分位函数使 \(K\) 凹、\(K(0)=0\)。若 \(0\le r_*\le l_*\le1\) 且
\[
K(2)\ge2l_*,\qquad K(3)=W_1\ge2l_*+r_*,
\]
凹性在 \([0,2]\)、\([2,3]\) 上给
\[
K(s)\ge\begin{cases}s l_*,&0\le s\le2,\\
2l_*+(s-2)r_*,&2\le s\le3.
\end{cases}
\]
右侧恰是 \(2\delta_{l_*}+\delta_{r_*}\) 的累积积分。对任意 \(t\in[0,1]\),
\[
\int(x-t)_+\,d\nu(x)=\max_{0\le s\le3}\{K(s)-st\}.
\]
任何选择的质量给不超过正部积分的一向;选择全部 \(x>t\) 的质量,
在 \(x=t\) 处任意分割即达到另一向。因此上式支配比较测度的正部积分。
对每个整数 \(n\ge2\),直接积分恒等式
\[
x^n=n(n-1)\int_0^1(x-t)_+t^{n-2}\,dt\quad(0\le x\le1)
\]
及非负积分交换给 \(W_n\ge2l_*^n+r_*^n\);\(n=1\) 是总积分假设。
若再有 \(e^{-\lambda}<l_*\)、\(e^{-\eta}<r_*\),严格递增的正整数幂给
\[
E_n<2l_*^n+r_*^n\le W_n\quad\text{对所有整数 }n\ge1.
\]
这是经典递增凸序/弱大序的积分应用,不要求相等的一阶矩。
无限量词由该解析证明承担,有限算术只负责其固定输入假设。

**31.11 三个严格对数区间与九行半径/原子证书。** 令 \(d=10^{15}\),固定
\[
\begin{array}{c|r|r}
&d\text{ 倍下界}&d\text{ 倍上界}\\\hline
a&693147180559945&693147180559946\\
b&1098612288668109&1098612288668110\\
c&1945910149055313&1945910149055314
\end{array}
\]
每个对数严格处于相应两有理数之间。认证不用浮点对数:对固定 \(p=2,3,7\),
取 \(t=(p-1)/(p+1)\in(0,1)\),令
\[
S=2\sum_{j=0}^{79}\frac{t^{2j+1}}{2j+1},\qquad
U=S+\frac{2t^{161}}{161(1-t^2)}.
\]
正对数级数给 \(S<\log p<U\):尾项为正,且把每个尾项分母放宽为 161
再作几何求和给严格上界。固定有理计算验证每行的下界 \(<S<U<\) 上界。

以下 \(R_-,R_+\) 以分母 \(10^4\) 给出,\(\alpha,\beta,l_*,r_*\) 以分母
\(10^3\) 给出;表中只列分子:
\[
\begin{array}{c|r|r|r|r|r|r}
\mathrm{slot}&R_-&R_+&\alpha&\beta&l_*&r_*\\\hline
0&0&0&231&231&794&794\\
1&4901&4902&202&692&818&501\\
2&6450&6451&382&1027&683&359\\
3&9174&9175&342&1260&711&284\\
4&8384&8385&600&1438&550&238\\
5&11061&11062&646&1752&526&174\\
6&9435&9436&931&1874&395&154\\
10&4901&4902&298&788&743&455\\
24&11020&11021&698&1800&498&166
\end{array}
\]
对 31.8 的每个线性对数式按系数符号取向外有理端点,得 \(v_-\le v\)、
\(q_i^-\le q_i\le q_i^+\),全部 \(q_i^-\ge0\)。slot 0 精确有 \(R=0\),
其余八行的有理平方比较为
\[
R_-^2<\frac16\sum_i(q_i^-)^2\le R^2
\le\frac16\sum_i(q_i^+)^2<R_+^2.
\]
每行均验证
\[
\frac{v_--R_+}{3}>\alpha>0,\qquad
\frac{v_-+2R_-}{3}>\beta\ge\alpha,
\]
所以 \(\lambda>\alpha\)、\(\eta>\beta\)。令 \(P_{12}(x)=\sum_{k=0}^{12}x^k/k!\),
每行另外精确验证
\[
l_*P_{12}(\alpha)>1,\qquad r_*P_{12}(\beta)>1,\qquad0<r_*\le l_*\le1.
\]
指数正尾项保证 \(e^x>P_{12}(x)\) 对 \(x>0\),故得到严格原子上界
\(e^{-\lambda}<l_*\)、\(e^{-\eta}<r_*\)。报告嵌入全部固定常数和可执行有理运算;
80 项对数证书和 12 次指数多项式均不是高度或矩阶扫描。

**31.12 每行的两个质量不等式及严格首矩裕量。** 依数值
\(1>1/2>1/3>1/7\) 取最大两单位质量,31.9 的两类分别给
\[
\begin{array}{c|c|c}
&W_1&K(2)\\\hline
\mathrm I&5/2-(2/3)\theta&2-\theta/2\\
\mathrm {II}&11/6-(6/7)\theta&3/2-(2/3)\theta
\end{array}
\]
类型 I 在 1 处质量为 \(2-\theta\),再取 \(\theta\) 单位的 \(1/2\)。
类型 II 先取 1 处的 \(1-\theta\) 单位及完整的 \(1/2\),再取
\(\theta\) 单位的 \(1/3\)。这些恰给两式,包含 \(\theta=0,1\) 及
\(v=a+b\) 的相容端点。

具体有限不等式用 31.11 的对数界作如下可复算证书。类型 I 令
\(N=v-a,D=b\),类型 II 令 \(N=v-a-b,D=c\),对线性式得
\(0\le N_-\le N\le N_+\)、\(0<D_-<D<D_+\),令 \(\theta_+=N_+/D_-\)。
按上表递减方向代入 \(\theta_+\) 得有理下界 \(w_-\le W_1\)、\(k_-\le K(2)\)。
对九行逐项验证的精确判据为
\[
k_->2l_*,\qquad w_--2l_*-r_*>1/40.
\]
当真实 \(\theta=1\),向外区间的 \(\theta_+\) 可略大于 1,仍给有效下界;
真实权重域须另由 \(0\le N\le D\) 的线性对数符号证明,不可由
\(\theta_-\le1\) 偷换成整个区间在 \([0,1]\)。报告的改编证书明确补上这一链接。
结合严格原子界,得到每个节点
\[
W_1-E_1>W_1-2l_*-r_*\ge w_--2l_*-r_*>1/40.
\]
最大两质量界和总质量界都已使用;单独首矩负号不被当作全部高阶矩的证明。

**31.13 九节点推出每个有限高度的全薄层界。** 31.10-31.12 给九节点同时满足
\[
E_n-W_n<0\ (n\ge1),\qquad E_1-W_1<-1/40.
\]
31.9 的绝对收敛级数于是对每个 \(0<z\le1/2\) 给
\[
G_0(z)<-z/40.
\]
31.5-31.7 对同一高度的每个宽域薄层给一个保留节点弱支配它,
乘以正数 \(e^T\) 保持方向,因此
\[
\boxed{e^TG_0(M_0,M_1)<-1/40
\quad\text{对所有有限 }T\ge\log2\text{ 及 }(M_0,M_1)\in\mathscr W_{T,0}.}
\]
这包括 \(T=\log2\)、角点封端、反射并列、零距离接缝及上尾。
没有以有限若干矩或浮点诊断外推无穷量词。

**31.14 预算对应保留角点与可行混合,不保留原 cutoff。**
对任意本节形状和宽域薄层写
\[
M_j^\xi=3T+X+r_j,\qquad M_j^0=3T+r_j=M_j^\xi-X\quad(j=0,1).
\]
角点预算分别是 \(3T+X+\sum_i e_i h_i\) 和 \(3T+\sum_i e_i h_i\),
同时减去 \(X\) 保留每个闭区间角点、端点等号和正宽度,给两个宽域的双射。
两个对偶可行域完全相同,容量为 \(r_1\ge a>0\);\(r_0<0\) 或 \(r_1\ge Q\) 不例外。
原严格下预算 \(M_0^\xi>Q+\log5040\) 不必使 \(M_0^0\) 超过 cutoff,
所以传递必须使用 31.13 的宽域定理,不能将此对应称为原域双射。

**31.15 投影和距离的统一扰动界。** 以 27.3 的通常欧氏投影
\(\Pi=\operatorname{Id}-\mathbf1\mathbf1^{\mathsf T}/3\),令
\(u_*=X/3\)、\(t_*=\rho_\xi-\rho_0\)。将扰动均值区间平移回 \(u_*\),
两个区间重合,第 \(i\) 行端点对则位移 \(\xi_i-u_*=(\Pi\xi)_i\)。
三角不等式及交换两个平移给距离的 1-Lipschitz 性,反三角不等式继而给
\[
|\delta_i^\xi-\delta_i^0|\le|(\Pi\xi)_i|,\qquad
|t_*|\le\frac{\|\Pi\xi\|_2}{\sqrt6}.
\]
仅为计算范数将形状排列为 \((0,s,\varepsilon)\)、\(0\le s\le\varepsilon\),
并未重排素数标签。直接展开有
\[
\|\Pi\xi\|_2^2=\frac23(\varepsilon^2-\varepsilon s+s^2)
\le\frac23\varepsilon^2,
\]
差为 \(2s(\varepsilon-s)/3\)。因此
\[
\varepsilon/3\le u_*\le2\varepsilon/3,\quad |t_*|\le\varepsilon/3,
\quad L_\xi-L_0=u_*-t_*,\quad H_\xi-H_0=u_*+2t_*.
\]
特别 \(L_\xi\ge L_0>T\),给全部扰动宽域薄层更强的下支持。
\(\varepsilon=0\) 时各增量为零。本证明允许最近端点标签、反射资格和零距离集合改变,
不对最近端点 min 或零范数求导。

**31.16 两个非负增量给传递常数 2。** 置 \(z=e^{-T}\)、\(K_z=z/(1-z)\)。
对 \(x\ge T\),有 \(0<f'(x)\le K_z\)。31.14 的每个共同可行权重 \(y\) 满足
\[
0\le\sum_i\bigl((1-y_i)[f(T+\xi_i)-f(T)]
+y_i[f(T+\xi_i+h_i)-f(T+h_i)]\bigr)
\le XK_z\le2\varepsilon K_z.
\]
对同一个紧可行域取最大值,即有 \(0\le D_\xi-D_0\le2\varepsilon K_z\)。
这直接比较全部可行混合,也包含 29.5 的全部六排列;
两个最大值可来自不同排列,不假设密度次序保持或最大值可微。

还须证明包络增量也在同一正区间。当 \(t_*\ge0\),\(u_*\ge t_*\),
两个包络自变量均弱增,所以 \(\Psi_\xi\ge\Psi_0\)。当 \(t_*<0\),先在旧半径
提高均值 \(u_*\),再把半径降到 \(\rho_\xi\ge0\);31.5 的两种单调性使包络弱增。
中间下支持先提高后继续提高,始终至少为 \(T\)。另一方面
\[
2|u_*-t_*|+|u_*+2t_*|\le2\varepsilon.
\]
若 \(u_*+2t_*\ge0\),左侧为 \(3u_*=X\le2\varepsilon\);
若为负,左侧为 \(u_*-4t_*\le u_*+4\varepsilon/3\le2\varepsilon\)。
连接相应端点的自变量线段均在 \([T,\infty)\),由导数界得
\(0\le\Psi_\xi-\Psi_0\le2\varepsilon K_z\)。两个同区间内数的差至多为区间长度,
所以
\[
\boxed{|G_\xi-G_0|\le2\varepsilon\frac z{1-z}.}
\]
不能把两个绝对界相加再冒称常数 2;承重的是两个增量均非负。
本条为本三元组所有对应宽域薄层补证了传递,不依赖 30.15 的字面三元组域。

**31.17 闭半径 \(1/320\) 的整箱严格裕量。** 31.13-31.16 给
\[
e^TG_\xi< -\frac1{40}+\frac{2\varepsilon}{1-z}
\le-\frac1{40}+4\varepsilon.
\]
因而
\[
\boxed{\max_i\xi_i\le1/320\quad\Longrightarrow\quad
e^TG_\xi<-1/80
\text{ 对每个有限 }T\ge\log2\text{ 和每个 }\mathscr W_{T,\xi}\text{ 薄层}.}
\]
\(-1/40+4/320=-1/80\),但首步严格,故闭半径边界和 \(T=\log2\) 同时取等
也不失严格性。\(\varepsilon=0\) 保留更强的 \(-1/40\) 界。
与原素数域取交后仍成立,其中没有 \(G=0\) 的薄层。

**31.18 齐次逼近给无界的实际 (2,3,7) 素数幂箱体。**
对每个整数 \(N\ge1\),把 \([0,1)^2\) 分成 \(N^2\) 个半开方格,
将 \(N^2+1\) 个点 \((\{ja/b\},\{ja/c\})\)、\(0\le j\le N^2\) 放入其中。
两点同格,取较大指标减较小指标,得整数 \(q,m,n\) 满足
\[
1\le q\le N^2,\qquad |qa-mb|<b/N,\qquad |qa-nc|<c/N.
\]
这是经典二维齐次 Dirichlet 抽屉论证,在此明确使用 \(c=\log7\),
不引用 29.18 或 30.17 的 \((2,3,5)\) 序列作为本三元组见证。
\(a/b\) 无理:正整数倍关系将给 \(2^q=3^m\),与唯一分解矛盾。
所以对任意固定整数 \(B\),有限集 \(1\le q\le B\) 的
\(\operatorname{dist}(qa/b,\mathbb Z)\) 有严格正的最小值。
当 \(N\to\infty\),上述误差趋零迫使任意这些选择的 \(q\to\infty\);
随后 \(m,n\to\infty\),最终均为正整数。

取下坐标 \((c_1,c_2,c_3)=(qa,mb,nc)\),非负原箱体参数为
\((b_1,b_2,b_3)=(q-1,m-1,n-1)\)。令 \(T=\min c_i\)、\(\xi_i=c_i-T\),则
\[
T\to\infty,\qquad0\le\varepsilon=\max c_i-\min c_i<(b+c)/N\to0.
\]
三坐标的两两差由相对于 \(qa\) 的两误差之和控制。故有无穷多个不同实际箱体,
最终进入 31.17 的闭邻域,每箱的全部宽域薄层均满足该严格界。
正素数幂不可能精确等高,因为 \(2^q=3^m\) 已不可能;可趋近零形状不等于可达到零形状。
没有执行上述抽屉构造或产生任何指数见证,没有有效数值指数 cutoff,
也不要求倒数对数的一般线性独立或任意非零形状的非齐次密度。

**31.19 原严格域非空的充要阈值与缺失素数 5 的等号排除。**
本三元组的最大、第二大角点分别为 \(A+Q\)、\(A+Q-a\)。
任意含两个角点的下端点必有 \(M_0\le A+Q-a\),所以
\[
Q+\log5040<M_0\quad\Longrightarrow\quad A>a+\log5040.
\]
反向若 \(A>a+\log5040\),取闭薄层 \([A+Q-a,A+Q]\),
宽度为 \(a>0\),两端皆角点,且下端点严格超过 cutoff。因此
\[
\boxed{\mathscr S_{T,\xi}\ne\varnothing\quad\Longleftrightarrow\quad
A>\log2+\log5040.}
\]
这里对连续箱体的 \(\mathscr S\) 表示宽域与 cutoff 的交;
称作原素数问题还须另满足 31.2 的整性条件。
等号 \(A=a+\log5040\) 和其下方均为空域,严格 cutoff 不能以端点包含消去。
对实际下坐标 \((q\log2,m\log3,n\log7)\),判据等价于
\[
2^q\cdot3^m\cdot7^n>10080,\qquad10080=2\cdot5040=2^5\cdot3^2\cdot5\cdot7.
\]
实际乘积没有素因子 5,所以不可能等于 10080。这只排除了实际格点的阈值等号,
不改变连续箱体的严格阈值或等号空域。31.18 的序列有 \(A\ge3T\to\infty\),
故原域最终非空;从那时起每箱的所有原域实薄层均满足 \(e^TG<-1/80\)。

**31.20 缩放极限与未覆盖的形状。** 对固定相对薄层,31.9 给
\(|G_0(z)|\le3\sum_{n\ge1}z^n/n\to0\)。任一固定本节邻域形状的对应薄层,
31.16 也给 \(G_\xi(z)\to0\)。同时每个有限高度的 \(e^TG\) 仍受上述负常数界约束;
例如零形状最后相邻薄层在充分大高度进入严格 cutoff 域,而其未缩放差仍趋零。
对 31.18 的实际箱体序列选对应的最后相邻薄层,同一系数界与传递估计也给
\(|G_\xi|\le3\sum_{n\ge1}z^n/n+2\varepsilon z/(1-z)\to0\),
且 31.19 保证这些实际薄层最终在原严格域中。
故不存在由这些结果得到的无界高度上统一未缩放负裕量。
\(T=\infty\)、\(z=0\) 仅为极限,不是容许点。

闭半径不覆盖任意相对形状,也不解决其它素数、一般素数或 C39 的第三素数射线。
固定实际 5040、共同平移 5040、密度次序及搜索/程序工作不属于本层。
齐次存在序列不等于每个连续平移高度都能达到的素数格点族。
第 10 节关于截面/薄层、指定内积、坐标编码和既有 KL 损失的区别保留;
本节没有从指数标签发明新的正交性。GH 仍为用户的原标签,没有新定义。
两个上界之差的符号不是 RH 等价判据、RH 证明或 RH 进展;
一般素数/形状问题仍 OPEN,本次实施不完成长期研究目标。

**31.21 经典出处、历史访问失败和固定核验的产地。** 专门九节点、两项缩放裕量、
整箱传递和实际格点应用标为 repo-derived。经典工具当场作聚焦只读核对:
HKUST [Lecture 14: Greedy Algorithms](https://home.cse.ust.hk/~dekai/271/notes/L14/L14.pdf)
PDF pp.4-7 的递减 value/weight 与最后一项可分数;
Boyd/Vandenberghe [Convex functions](https://web.stanford.edu/class/ee364a/lectures/functions.pdf)
PDF pp.6,16,26,27 的范数凸性、Jensen 和单调复合;
Gushchin–Borzykh, *Integrated quantile functions: properties and applications*,
Modern Stochastics: Theory and Applications 4(4) (2017),285–314,
DOI [10.15559/17-VMSTA88](https://doi.org/10.15559/17-VMSTA88),
[原文](https://arxiv.org/pdf/1801.00977) PDF p.10 / 期刊 p.294 Theorem 5(ii)
和证明的递增凸序/正部积分等价;本节质量约定除以 3 即与概率约定相容。
另核对 NIST DLMF [4.6.E1](https://dlmf.nist.gov/4.6.E1.tex) 的对数级数,
以及 Encyclopedia of Mathematics [Dirichlet theorem](https://encyclopediaofmath.org/wiki/Dirichlet_theorem)
的 Diophantine approximations 小节中多实数版本,本节只用 \(Q=N^2\) 的抽屉特例。
这些出处支持经典材料,不被说成已有本节专门素数差值定理。
PDF 文本提取有字体解码警告,HKUST 若干公式字形不全;实际可读的算法文字与
其它指定定理/公式已核对,本节的精确专门公式由上面的自足证明和证书承担。
检索收据及其适用范围见报告,不作穷尽文献或优先权声明。

primary envelope 的 SHA256 为
7170e171ad3596e697ff4d515393606b935fb6d5237505d7191b464c46852439;
只消费其 conclusion,log_ref 不透明。它原报两次公开获取均失败于 DisabledError:
封存 feb497ec31f68e09ccc547a08810c398e66f3ee6 的本源文件 URL,
及封存 391f7355698085c6500b46838a093dad05947ffb 的
docs/reports/prime-slab-finite-design-0909.md URL。它没有读取这些源字节;
本实施对本树的读取不改变这一历史事实。primary 自报九个指定节点的浮点计算
仅作有界诊断,另有 Fraction 固定证书与十八项整数资格核对;不把诊断列为证明前提。
caller 原审计记录 131 项全通过,不是 primary 的执行计数,也不是本轮独立评审票。
原审计与程序保持原字节且未重跑。新报告把相同常数改编为无 caller-local 路径依赖的
自足可执行证书,另补固定输入到证明假设的链接,只执行改编证书一次。
精确命令、版本、字节/hash、实际结果及各类证据分工见
[balanced-prime-237-all-slabs-0910.md](../../reports/balanced-prime-237-all-slabs-0910.md)。

**31.22 单一内容层、保留边界及 caller 交付义务。** 本层由隔离 Codex CLI 实施席 I15
在 caller 固定的 consensus-rnd:sshx 1.0.0-beta.42 和 CODEX_WORKER_SPEC.md 下产生,
flight qgh0910-i15-balanced-prime-237,attempt 1。遵照 CLAUDE 5.11 和明确 brief,
无 native subagent、委派、额外 oracle 或本轮评审票;repo-prior-exposed,
不声称上下文无先验或模型族多样性。实际 GPT PRO 来源取自 caller 既有身份记录,
本实施未独立鉴定 serving model。准备输入中旧的 predecessor-in-flight 描述属于其准备时刻,
本层实际 immutable BASE 为 7b443a1764e5756c670b3912300a71f5b2e470f3,
工作树为 /Users/auricstudio/trureturing-qgh-balanced-prime-237,
分支 lane/math/quantized-gh-balanced-prime-237-0910。

第 1-30 节完整前缀保留 286326 字节、5391 个 LF,SHA256
4856aba958844029d1c7150f610104d3652dcfd25139bdfb53e4346cd905db0a;
全部历史 CAS、entry 和报告保留。只追加本节、单一报告和以下命令的实际 canonical 输出:
~~~sh
make ingest BASE=7b443a1764e5756c670b3912300a71f5b2e470f3 SOURCE=arithmetic-boundary-quantization
~~~
源语义、固定证书及其 CAS/YAML 绑定属于同一可审查内容层,不拆出脱离源的派生地址。
全部自动 children、历史末单元 terminal-LF 变体和 producer EOF 均保留原字节,
指纹与 cas_ref 带 sha256: 前缀,子 atom_id 为裸 hash;完整映射由实施结论提供。
摄入不等于 Lean 吸收或冻结。CPU 仅用于固定证明核验和必要编排,
无候选搜索、旧搜索重放、GPU、daemon、工具/Lean/frozen 编辑或广泛 build/preflight。
没有读取任何 worker 日志、log_ref 内容、caller 转录、同轮 peer 结果或其它 live target。
本层返回 unstaged;caller 负责其后封存、独立评审、普通仓库门、push/PR/发布,
最终 S20 交付等待 S19 MERGED。本实施不作 review 或 termination 判词,
不执行暂存、commit、push、PR、merge 或生命周期命令。

## 32. 原始 fixed5040 四素数箱体的全实薄层严格比较

**32.1 本层的命题与状态。** 本节为 S21/C46 的 PAPER_ARGUMENT / repo-derived
参考输入:只研究原始固定箱体 \(p=(2,3,5,7)\)、\(b=(4,2,1,1)\),
即另行讨论平移时所称的固定 \(T=0\) 情形。本节不引入共同高度变量。
证明对象是所有有限实预算薄层,不是只比较整数预算或抽样薄层。
在下述原始严格域中,分数资源上界与范数/矩上界之差满足
\[
G(M_0,M_1)\le G_{\max}\in
\frac{[-821037164,-821037163]}{10^{12}}<-\frac1{1250}.
\]
区间记号表示一个包含关系;最右侧表示整个区间严格小于该有理数。
唯一保留节点最大者为相邻 raw slot 9。32.17 另用严格饱和等号分析,
证明它也是整个原始实薄层域的唯一最大者;有限表格本身不推出后一结论。
第 26 节的一般 \(k\) 定理在此满足其整数指数假设,第 31 节的三素数专用结论
不作为四素数扩张的依据。GH 保留为用户的字面标签,未赋予新的数学定义。

**32.2 普通指数、所选内积与编码的区别。** 唯一素因数分解给出
\[
5040=2^4\cdot3^2\cdot5^1\cdot7^1.
\]
所以 \((4,2,1,1)\) 是普通的素数指数,不是 Zeckendorf 数字串。
本节按素数次序使用 \(\mathbb R^4\) 的坐标,局部下标为 \(i=0,1,2,3\),
并明确选择标准欧氏内积 \(\langle x,y\rangle=\sum_{i=0}^3x_i y_i\)。
其标准基满足 \(\langle e_i,e_j\rangle=\mathbf1_{i=j}\),这是内积的选择;
唯一分解提供坐标的独立可辨识性,不自行提供正交性。
若 \(\bar x=\frac14\sum_i x_i\),则
\[
\langle x-\bar x\mathbf1,\mathbf1\rangle=0,\qquad
\|x\|_2^2=4\bar x^2+\|x-\bar x\mathbf1\|_2^2.
\]
这是指定内积下的勾股分解。等预算给出超平面截面,两预算给出闭薄层,
二者也不等同。Zeckendorf 可选择性地把每个普通指数重新编码;
例如按权重 \(1,2,3,5,\ldots\),整数 \(4=3+1\)、\(2=2\)、\(1=1\)。
可逆编码既不改变这些整数,也不证明下面的上界比较或额外正交关系。

**32.3 固定端点、预算平移与实际角点。** 所有对数均为自然对数。置
\[
h_i=\log p_i,\quad c_i=(b_i+1)h_i,\quad d_i=(b_i+2)h_i,
\quad C_i=\{c_i,d_i\},
\]
\[
(e^{c_i})=(32,27,25,49),\qquad(e^{d_i})=(64,81,125,343),
\]
\[
P=210,\quad Q=\log210,\quad A=\sum_i c_i=\log1058400=Q+\log5040.
\]
实际角点是 \(x_i=c_i+\varepsilon_i h_i\),\(\varepsilon_i\in\{0,1\}\)。
以 bit 0 对应素数 2,其严格递增次序为下表;每行
\(R_s=5040q_s\)、\(\beta_s=\log(PR_s)=\log(1058400q_s)\)。

~~~text
| \(s\) | \(q_s\) | mask | \(R_s\) |
| --- | --- | --- | --- |
| 0 | 1 | 0 | 5040 |
| 1 | 2 | 1 | 10080 |
| 2 | 3 | 2 | 15120 |
| 3 | 5 | 4 | 25200 |
| 4 | 6 | 3 | 30240 |
| 5 | 7 | 8 | 35280 |
| 6 | 10 | 5 | 50400 |
| 7 | 14 | 9 | 70560 |
| 8 | 15 | 6 | 75600 |
| 9 | 21 | 10 | 105840 |
| 10 | 30 | 7 | 151200 |
| 11 | 35 | 12 | 176400 |
| 12 | 42 | 11 | 211680 |
| 13 | 70 | 13 | 352800 |
| 14 | 105 | 14 | 529200 |
| 15 | 210 | 15 | 1058400 |
~~~

唯一分解保证 16 个不同 mask 的乘积互异。原始可容许域准确为
\[
\mathscr S_{5040}=\{(M_0,M_1)\in\mathbb R^2:
A<M_0<M_1,\ [M_0,M_1]\text{ 至少含两个不同的 }\beta_s\}.
\]
\(M_j\) 是平移后的预算。本节用 \(\tau_j=M_j-Q\) 表示旧指数预算,
不用 \(T_0\) 或共同高度符号;相应 \(e^{M_j}=210e^{\tau_j}\)。
条件等价于 \(\log5040<\tau_0<\tau_1\) 且旧闭预算区间含两个实际整数角点的对数。
预算本身是任意有限实数,其指数不必是整数。最低实际角点
\(\beta_0=A\) 被严格 cutoff 排除,原始整数 5040 不在任何可容许薄层中。
其余 15 个实际角点仍可作为闭薄层端点;两个混合支撑点不能代替两个实际角点。

**32.4 两个上界及比较的归一化。** 令 \(u=M_1\)、\(f(x)=\log(1-e^{-x})\),
\(v_i=f(d_i)-f(c_i)>0\),定义第 26 节的同一个价格上界
\[
D(u)=\inf_{\lambda\ge0}\left\{\lambda u+
\sum_i\max_{x\in C_i}(f(x)-\lambda x)\right\}
=\sum_i f(c_i)+\inf_{\lambda\ge0}
\left\{\lambda(u-A)+\sum_i\max(0,v_i-\lambda h_i)\right\}.
\]
置
\[
I=[M_0/4,u/4],\quad\delta_i=\operatorname{dist}(I,C_i),\quad
V_0=\sum_i\delta_i^2,\quad\mu=u/4,\quad\rho=\sqrt{V_0/12},
\]
\[
L=\mu-\rho,\quad H=\mu+3\rho,\qquad
\Psi(M_0,u)=f(H)+3f(L),\quad G(M_0,u)=D(u)-\Psi(M_0,u).
\]
\(V_0\) 是四个平方距离的和,没有另除以 4。
与旧记号相接时 \(E_S=\prod_i(1-p_i^{-1})^{-1}\),
\(U_{\rm dual}=\log E_S+D\)、\(U_{\rm var}=\log E_S+\Psi\);
共同常数抵消而得到这里的 \(G\)。实际离散薄层最优值
\[
W(M_0,u)=\max_{\substack{x_i\in C_i\\M_0\le\sum_i x_i\le u}}\sum_i f(x_i)
\]
满足 \(W\le D\),因为每个可行整数选择都是下述分数可行点。
\(D\) 是分数松弛的精确值,一般不是 \(W\) 的精确值;
严格比较两个上界不等于证明 Robin 不等式。

**32.5 全实域的正支撑。** 取薄层内任一实际角点 \(x\),记
\(\bar x=\frac14\sum_i x_i\in I\)、\(m=\min_i x_i\ge\log25>0\)。
令 \(w_i=x_i-m\ge0\)、\(s=\sum_i w_i=4(\bar x-m)\)。由
\(\delta_i\le|x_i-\bar x|\) 及非负数的 \(\sum_i w_i^2\le s^2\),有
\[
V_0\le\sum_i(x_i-\bar x)^2
=\sum_i w_i^2-s^2/4\le3s^2/4=12(\bar x-m)^2.
\]
于是 \(\rho\le\bar x-m\),而 \(\mu\ge\bar x\),故
\[
\boxed{H\ge L\ge m\ge\log25>0.}
\]
这是对每一个可容许实薄层的解析证明,包括角点落在端点、零距离和零方差。
所有后续饱和区间都保留实际角点,故逐点继承正域;有限程序的支撑检查只是固定输入链接。

**32.6 包络的严格性质与零半径。** 在凸域
\(\Omega=\{(\mu,r):r\ge0,\ \mu-r>0\}\) 上置
\(F(\mu,r)=f(\mu+3r)+3f(\mu-r)\)。由于
\[
f'(x)=\frac1{e^x-1}>0,\qquad f''(x)=-\frac{e^x}{(e^x-1)^2}<0,
\]
有 \(F_\mu>0\)、\(F_r=3(f'(\mu+3r)-f'(\mu-r))\le0\)。
当 \(r>0\) 时后一式严格负;固定 \(\mu\),对任意
\(0\le r_1<r_2<\mu\) 积分仍得 \(F(\mu,r_2)<F(\mu,r_1)\)。
不能由 \(F_r(\mu,0)=0\) 推出常值。
线性映射 \((\mu,r)\mapsto(\mu+3r,\mu-r)\) 行列式为 \(-4\),故单射。
对两个严格凹的正权 \(f\) 项用 Jensen,证明 \(F\) 联合严格凹。

**32.7 这个固定箱体的严格密度次序。** 令
\[
\sigma_i=\frac{v_i}{h_i}
=\frac{\log((1-e^{-d_i})/(1-e^{-c_i}))}{\log p_i}.
\]
以下为原 primary 给出、原 caller Arb 审计独立确认的四个闭有理区间;
每个端点都除以 \(10^{12}\),不是用打印小数判断舍入。

~~~text
| 素数 | 密度下端分子 | 密度上端分子 |
| --- | --- | --- |
| 2 | 23083613113 | 23083613114 |
| 3 | 23045261959 | 23045261960 |
| 5 | 20373462417 | 20373462418 |
| 7 | 9095783332 | 9095783333 |
~~~

各区间互不交叠且为正,所以 \(\sigma_0>\sigma_1>\sigma_2>\sigma_3>0\)。
只声明这些固定端点处的密度次序;不引用另一个全高度密度定理。

**32.8 分数背包的值、价格与端点。** 对 \(u\ge A\),分数问题为
\[
\max_{0\le y_i\le1,\ \sum_i h_i y_i\le u-A}
\left(\sum_i f(c_i)+\sum_i v_i y_i\right).
\]
对任意可行 \(y\) 及 \(\lambda\ge0\),
\[
\sum_i v_i y_i
\le\lambda(u-A)+\sum_i\max(0,v_i-\lambda h_i).
\]
令乘法容量 \(t=e^{u-A}\)、\(B=(1,2,6,30,210)\)。在
\(B_r\le t<B_{r+1}\)、\(r=0,1,2,3\) 时取
\[
y_i=\begin{cases}1&i<r,\\\log(t/B_r)/h_r&i=r,\\0&i>r,\end{cases}
\qquad\lambda=\sigma_r.
\]
容量精确用尽,前缀价格余值为正、后缀为负、分数行余值为零,
所以前述不等式同时取等,证明原始最大值和价格下确界都达到且等于
\[
\boxed{D(u)=\sum_i f(c_i)+\sum_{i<r}v_i+\sigma_r\log(t/B_r).}
\]
严格密度次序也保证分数最优向量唯一:任何未填高密度项与已填低密度项
之间的等重量交换都会严格改进;正收益又强制在总容量以下用尽资源。
在 \(t=B_r\)、\(1\le r\le3\),前一公式的分数为 1、后一为 0,
同一个整数前缀取等,任意 \(\lambda\in[\sigma_r,\sigma_{r-1}]\) 可作价格。
在 \(t=1\) 时 \(y=0\)、任意 \(\lambda\ge\sigma_0\) 匹配;
在 \(t=210\) 时 \(y=\mathbf1\)、任意 \(\lambda\in[0,\sigma_3]\) 匹配。
当 \(t>210\) 时仍为全上端点,价格可取且必须取 0 才与有松弛的容量匹配。
故 \(u\ge A+Q=\beta_{15}\) 时 \(D=\sum_i f(d_i)\) 恒定。
这些容量折点全是实际前缀角点,所以 \(D\) 在每个
\([\beta_j,\beta_{j+1}]\) 上仿射。此处密度无并列;
第 26 节的一般价格并列处理并未被删除。匹配的代数证明承担等值,
数值程序中的 primal/dual 区间交叠仅作一致性检查。

**32.9 下预算饱和及其等号。** 对任意 \((M_0,u)\in\mathscr S_{5040}\),取
\(j=\max\{s:\beta_s\le u\}\)、\(a=\beta_{j-1}\)。两实际角点条件给
\(M_0\le a<\beta_j\le u\);严格 \(M_0>A=\beta_0\) 又强制 \(j\ge2\)。
把 \(M_0\) 提高到 \(a\) 仍可容许,只缩小 \(I\),故各非负距离弱增。
由 32.6 在固定均值下严格随半径下降,得到
\[
G(M_0,u)\le G(a,u),
\]
且取等当且仅当 \(V_0(M_0,u)=V_0(a,u)\),等价于四行距离逐项不变。
一般不能把这个等号条件简写成 \(M_0=a\);本箱体在最大者处的严格性另见 32.17。

**32.10 唯一相关的向下距离切换。** 固定饱和 \(a\),写
\(v=a/4\)、\(\mu=u/4\ge v\)。对一行 \(c<d\),精确距离为
\[
\delta(\mu)=\begin{cases}
v-d,&d\le v,\\
(c-\mu)_+,&v\le c,\\
\min\{v-c,(d-\mu)_+\},&c<v<d.
\end{cases}
\]
边界 \(v=c,d\) 的公式相容。当 \(c<v<(c+d)/2\) 时,
存在活跃切换 \(\mu_*=c+d-v>v\):先为常数 \(v-c\),
后为 \((d-\mu)_+\),斜率发生 \(0\to-1\) 的向下跳变。
它的上预算是 \(u_*=4(c+d)-a\)。当 \(v\ge(c+d)/2\) 时,
这一中间行在 \(\mu\ge v\) 上直接为 \((d-\mu)_+\),无内部向下跳变。
到零的切换只会是 \(-1\to0\),保持凸性。最近端点并列发生于所列切换处,
两式取同值;\(v=c,d,(c+d)/2\) 均不制造额外活跃内部节点。

**32.11 切换间严格凸性与外端点比较。** 在
\([\beta_j,\beta_{j+1}]\)、\(2\le j\le14\)、\(a=\beta_{j-1}\) 上,
只用内部活跃向下切换划分。每个闭子段内各距离都是非负凸函数,
包括经过零的正部折点。逐坐标单调性和欧氏三角不等式给出
\[
\rho(tu_1+(1-t)u_2)\le t\rho(u_1)+(1-t)\rho(u_2)=\bar r,
\quad0<t<1.
\]
这里用的是距离向量的范数,不是把凹的平方根与任意凸函数复合。
由 32.5,插值点 \((\mu_t,\bar r)\) 也满足正支撑。
若 \(u_1\ne u_2\),均值不同使输入对不同,从而
\[
\Psi(a,u_t)=F(\mu_t,\rho(u_t))\ge F(\mu_t,\bar r)
>t\Psi(a,u_1)+(1-t)\Psi(a,u_2).
\]
即使半径为零,严格 Jensen 步仍成立。32.8 的 \(D\) 仿射性于是给
\[
G(a,u_t)<tG(a,u_1)+(1-t)G(a,u_2)\le\max\{G(a,u_1),G(a,u_2)\}.
\]
内部不能最大化。左外端点 \((\beta_{j-1},\beta_j)\) 为相邻对;
右外端点满足
\[
G(\beta_{j-1},\beta_{j+1})\le G(\beta_j,\beta_{j+1}),
\]
因为可再饱和下预算且保留两个实际角点。其等号仍准确为四行距离不变。
当上预算恰为角点时须按实际 \(j\) 重新饱和;
不能把上一段未再饱和的右端点误当作一个新的最大节点。

**32.12 无界上尾与全实薄层支配。** 若 \(u\ge\beta_{15}\),
饱和下预算为 \(a=\beta_{14}\),\(D\) 恒定。增加 \(u\) 扩大均值区间,
使 \(\rho\) 非增,同时 \(\mu\) 严格增加。对 \(\mu_2>\mu_1\)、
\(r_2\le r_1\),中间点仍在正域且
\[
F(\mu_2,r_2)\ge F(\mu_2,r_1)>F(\mu_1,r_1).
\]
所以整个饱和上尾的 \(G\) 严格递减,由最后相邻对控制。
32.9-32.11 因而证明第 26 节定理在本箱体的实例:
\[
\forall s\in\mathscr S_{5040}\ \exists n\in\mathcal K_{5040}:G(s)\le G(n),
\]
其中 \(\mathcal K_{5040}\) 仅含通过严格 cutoff 的相邻角点对,
以及活跃且严格位于下一角点区间内部的反射对。每个节点本身都可容许。
\(R_{14}=529200>5040\) 保证域非空。于是
\(\max_{s\in\mathscr S_{5040}}G(s)=\max_{n\in\mathcal K_{5040}}G(n)\),
并实际达到。连续量词由以上分析承担,不会从有限算术计数中自动产生。

**32.13 原始 71 槽的精确资格。** 相邻 raw slot \(r=0,\ldots,14\) 表示
\((\beta_r,\beta_{r+1})\),资格为 \(R_r>5040\)。因此只保留 1 至 14,
slot 0 的下端为 \(A\),被严格 cutoff 排除。
反射 raw slot 使用局部 \(k=4\) 编号
\[
15+4(j-1)+i,\qquad1\le j\le14,\quad0\le i\le3.
\]
这是 \(15+4\cdot14=71\) 个预先规定的定理槽,不是三素数 GPU 行号。
令 \(X=PR_{j-1}\)、\(E_i=p_i^{4(2b_i+3)}\),则反射为
\[
(M_0,M_1)=(\log X,\log(E_i/X)),\qquad
(e^{\tau_0},e^{\tau_1})=(R_{j-1},E_i/(P^2R_{j-1})).
\]
按次序编号的五个严格整数 guards 为
\[
\begin{array}{ll}
1:&R_{j-1}>5040,\\
2:&p_i^{4(b_i+1)}<X,\\
3:&X^2<E_i,\\
4:&P^2R_{j-1}R_j<E_i,\\
5:&E_i<P^2R_{j-1}R_{j+1}.
\end{array}
\]
由指数函数严格单调,它们分别等价于 cutoff、\(c_i<M_0/4\)、
\(M_0/4<(c_i+d_i)/2\)、\(\beta_j<M_1<\beta_{j+1}\)。
角点边界相等已经归相邻节点;其余 guard 等号不产生额外活跃向下切换。
对全部 56 个反射槽的精确整数分类如下,按首个失败 guard 互斥列出。

~~~text
| 首个失败 guard | 不活跃反射 raw slots |
| --- | --- |
| 1 | 15,16,17,18 |
| 2 | 22,26,30 |
| 3 | 27,28,31,32,35,36,39,40,41,43,44,45,47,48,49,51,52,53,55,56,57,59,60,61,63,64,65,67,68,69 |
| 4 | 空集 |
| 5 | 19,20,21,24,25,29,33,34,38,42,46,50,54,58,62,66,70 |
~~~

剩余恰为反射 slots 23、37。故 \(14+2=16\) 个保留节点,
不活跃数 \(1+4+3+30+0+17=55\)。不活跃槽只作资格核验,
没有被记作 55 个已计算负值的薄层。

**32.14 两个反射节点的整数证书与有理端点。** 两节点的严格 guards 可逐项核对:

~~~text
| slot | \(j,i\) | \(R_{j-1}\) | \(X\) | \(p_i^{4(b_i+1)}\) | \(X^2\) | 左乘积 | \(E_i\) | 右乘积 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 23 | 3,0 | 15120 | 3175200 | 1048576 | 10081895040000 | 16803158400000 | 17592186044416 | 20163790080000 |
| 37 | 6,2 | 35280 | 7408800 | 390625 | 54890317440000 | 78414739200000 | 95367431640625 | 109780634880000 |
~~~

左、右乘积分别指 guards 4、5 中的 \(P^2R_{j-1}R_j\)、\(P^2R_{j-1}R_{j+1}\)。
每行满足 \(5040<R_{j-1}\)、lower power \(<X\)、\(X^2<E_i\)、左乘积 \(<E_i<\) 右乘积。
其平移后指数端点分别为
\[
(3175200,17592186044416/3175200),\qquad
(7408800,95367431640625/7408800),
\]
而约分后的旧指数端点为
\[
(15120,274877906944/10418625),\qquad
(35280,762939453125/12446784).
\]
后者两个上端均非整数,但对应合法实预算。分子仅含指定行素数的幂,
其它素数在分母仍有正指数,唯一分解禁止全部约消。
相邻下端彼此不同;固定下端的不同反射行具有不同素数幂分子,
所以没有靠数值容差合并的重复节点。

**32.15 全部 48 个节点值包络。** 下表每个端点分子均除以 \(10^{12}\),
表示闭有理区间。它是原 primary 表及原 caller Arb 审计的共同精确端点数据;
本轮报告的自足改编证书对自己的静态副本另执行一次。
\(G\) 从未先舍入的 \(D-\Psi\) 直接包络,不是两个打印区间相减后强行缩窄。

~~~text
| slot | \(D_-\) | \(D_+\) | \(\Psi_-\) | \(\Psi_+\) | \(G_-\) | \(G_+\) |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | -105585917043 | -105585917042 | -99815050712 | -99815050711 | -5770866331 | -5770866330 |
| 2 | -93813806727 | -93813806726 | -89539949332 | -89539949331 | -4273857395 | -4273857394 |
| 3 | -89612158690 | -89612158689 | -86872489407 | -86872489406 | -2739669284 | -2739669283 |
| 4 | -86471575608 | -86471575607 | -83626367313 | -83626367312 | -2845208295 | -2845208294 |
| 5 | -79204872042 | -79204872041 | -76118124932 | -76118124931 | -3086747110 | -3086747109 |
| 6 | -72349767575 | -72349767574 | -69265007491 | -69265007490 | -3084760085 | -3084760084 |
| 7 | -70944143900 | -70944143899 | -68063358972 | -68063358971 | -2880784928 | -2880784927 |
| 8 | -64089039433 | -64089039432 | -61684687124 | -61684687123 | -2404352309 | -2404352308 |
| 9 | -56822335867 | -56822335866 | -56001298703 | -56001298702 | -821037164 | -821037163 |
| 10 | -55420214683 | -55420214682 | -54127825653 | -54127825652 | -1292389030 | -1292389029 |
| 11 | -53761857306 | -53761857305 | -51730182731 | -51730182730 | -2031674576 | -2031674575 |
| 12 | -49115498111 | -49115498110 | -45360861267 | -45360861266 | -3754636845 | -3754636844 |
| 13 | -45427475339 | -45427475338 | -41767225027 | -41767225026 | -3660250313 | -3660250312 |
| 14 | -39122758768 | -39122758767 | -35851557046 | -35851557045 | -3271201722 | -3271201721 |
| 23 | -92756306669 | -92756306668 | -88503048096 | -88503048095 | -4253258574 | -4253258573 |
| 37 | -75217271566 | -75217271565 | -72158981090 | -72158981089 | -3058290477 | -3058290476 |
~~~

所有 \(G_+\) 都严格小于 \(-10^{12}/1250=-800000000\),
而 slot 9 的 \(G_-=-821037164\) 严格大于其它每行 \(G_+\)。
故 slot 9 是唯一保留节点最大者。32.12 才把这个有限结论提升为
整个 \(\mathscr S_{5040}\) 的一致严格界 \(G<-1/1250\)。

**32.16 最大值的精确公式及分支链接。** 置
\[
\alpha=\log22226400=\beta_9,\qquad
\omega=\log31752000=\beta_{10},
\]
\[
z_0=(\alpha-24\log2)/4,\quad z_1=(16\log3-\omega)/4,
\quad z_2=(12\log5-\omega)/4,\quad z_3=(\alpha-8\log7)/4,
\]
\[
r_* = \sqrt{(z_0^2+z_1^2+z_2^2+z_3^2)/12}.
\]
四个 \(z_i\) 都严格正且恰为此节点的行距离,不只由数值交叠猜测。
令 \(X=22226400,Y=31752000\)。对素数 2 有 \(64^4<X<Y\),
所以最近端点为 \(d_0\),距离为 \(z_0\)。对 \(i=1,2,3\) 有
\((e^{c_i})^4<X<Y<(e^{d_i})^4\);此外
\[
XY>(27\cdot81)^4,\qquad XY>(25\cdot125)^4,\qquad XY<(49\cdot343)^4.
\]
前两式选择上端点,后一式选择下端点,给出 \(z_1,z_2,z_3\) 的精确分支。
这些是报告改编证书额外核验的固定整数链接。
容量 \(e^{\omega-A}=30\),故唯一分数最优向量为 \((1,1,1,0)\),
价格可取 \(\sigma_3\),其值精确为
\[
D(\omega)=\log\left(\frac{63}{64}\frac{80}{81}\frac{124}{125}\frac{48}{49}\right)
=\log\frac{496}{525}.
\]
这个向量的实际角点是 \(\beta_{10}\),本节点还恰有 \(W=D\);
这不改变其它预算处 \(D\) 一般只是离散上界的事实。最终
\[
\boxed{G_{\max}=\log\frac{496}{525}
-f(\omega/4+3r_*)-3f(\omega/4-r_*)
\in\frac{[-821037164,-821037163]}{10^{12}}.}
\]
旧预算指数为 \((e^{\tau_0},e^{\tau_1})=(105840,151200)\),
而平移后是 \((22226400,31752000)\),二者相差因子 210。

**32.17 整个实域的唯一性及等号资格。** 严格内部凸性、严格上尾和实际角点处再饱和
表明:任何最大薄层饱和后必须是一个保留的最大节点。由 32.15,
只能饱和到 \((\alpha,\omega)\),于是其上预算必须为 \(\omega\),
下预算 \(a\le\alpha\)。若 \(a<\alpha\),素数 2 行由于
\(\omega/4>\alpha/4>\log64\),有
\[
\delta_0(a,\omega)=\max(a/4-\log64,0)
<\alpha/4-\log64=\delta_0(\alpha,\omega).
\]
其它行在降低下预算时均不增加。平方和严格变小,32.6 遂给
\(G(a,\omega)<G(\alpha,\omega)\)。因此
\[
G(M_0,M_1)=G_{\max}\quad\Longleftrightarrow\quad
(M_0,M_1)=(\alpha,\omega).
\]
这一额外解析论证才建立全实域唯一性,没有把“唯一保留最大节点”直接当成它。
所有其它薄层严格小于 \(G_{\max}\);一般饱和步骤仍允许四行距离不变时取等。
\(G=0\)、\(G>0\) 及 \(G=-1/1250\) 在本域均不可能。
原 cutoff 的等号仍被排除,反射/零距离处的并列和闭端点资格均保留。

**32.18 原 primary 级数方法与勘误,不改历史原文。** 原 conclusion 的
对数余项含压缩串 `9/(41293^129)`。这是历史 raw 表达式;
其数学纠正是 `9/(4*129*3^129)`,即
\[
\frac{9}{4\cdot129\cdot3^{129}}.
\]
对 \(1\le t\le2\),令 \(z=(t-1)/(t+1)\le1/3\),则
\[
\log t=2\sum_{j=0}^{63}\frac{z^{2j+1}}{2j+1}+R,
\qquad0\le R\le\frac{2z^{129}}{129(1-z^2)}
\le\frac{9}{4\cdot129\cdot3^{129}}.
\]
最后一步是确切的 \(2(1/3)^{129}/[129(1-1/9)]\)。原 primary 自报的方法
在 \(2^{-160}\) 网格上逐运算向外取整,以 \(q=2^e t,1\le t<2\)
归约有理数对数,另用 \(t=2\) 求 \(\log2\)。平方根由整数平方根向外包络。
对需计算的 \(0<x<16\),令 \(t=x/16\),用
\(S_{80}(t)\le e^t\le S_{80}(t)+2/81!\):
首个遗漏项至多 \(1/81!\),后续项比例至多 \(1/82\),故该界有效。
再取 16 次幂并倒数求 \(e^{-x}\)。距离用 interval min/max 处理并列。
primary 自报所有节点的 \(L,H\) 位于
\([3571708000370,5592595433915]/10^{12}\),以保证其指数级数范围。
本实施不重跑或补造那份临时级数程序,也不把该自报执行当作本轮亲跑。
原 envelope/程序/审计全部保持字节不变;纠正只在新增文字中明示。
原 caller 与本轮改编使用的是独立的 outward Arb 运算,
不使用这个 raw 余项表达式来证明数值符号。

**32.19 证据分工、复现与历史限制。** caller 指定的实际 GPT PRO fixed-box primary
task 为 0838ec9d-f978-4cfc-8d59-965a3331f912,flight
qgh0910-pro-actual-5040-box。仅消费其已完成 conclusion;
primary 明报获取所供 immutable GitHub URL 失败为 DisabledError,
没有读取该源字节或独立核验 caller 给出的源 hash/字节数。
它从所给定义自行重导有限归约,临时整数/Fraction 级数程序的执行是其自报。
模型/service 元数据并未由 primary 或本实施独立鉴定,不补造 conversation 身份。
I16 则在本树实际阅读第 26 节,核对其 \(k\ge2\)、互异素数、\(b_i\in\mathbb Z_{\ge0}\)
及原始严格 cutoff 等全部适用条件;没有读取 S20 的其它物理工作树。

原 caller node audit 只核验这个箱体的 71 槽资格,没有 \(G\) 值计算。
原 caller sign audit 记录 python-flint 0.8.0 / Arb256 对四个密度区间和
48 个 \(D,\Psi,G\) 区间的独立确认,并另述纸面连续域核对;
这些是原先完成的证据,原程序未在本轮执行。
单一报告 [actual-5040-fixed-box-0910.md](../../reports/actual-5040-fixed-box-0910.md)
嵌入一份无 caller 绝对路径依赖的完整可执行证书,静态带入角点、整数 guards、
四个密度区间和 48 个节点区间。只抽取并执行该改编一次,
精确程序字节/hash、实际解释器/库版本、命令、结果和 stderr 见报告。
新增固定分支整数链接与原 52 个包络检查分列;它们不是候选生成或连续域的计算穷举。
Arb 的有理输入和区间比较承担向外认证,打印小数与区间交叠不承担等式证明。

**32.20 文献重叠与仓内归属。** 本层专门化的证明组合标为 repo-derived,
不声称经典工具或这个 fixed-box 陈述具有新颖性或优先权。
现场读取 HKUST [Lecture 14: Greedy Algorithms](https://home.cse.ust.hk/~dekai/271/notes/L14/L14.pdf)
PDF pp.4-7,支持按 value/weight 递减、最后一项可部分取入及交换论证;
文本提取的一些数学字体乱码保留为访问限制,本节自己给出精确价格证明。
读取 Boyd/Vandenberghe [Convex functions](https://web.stanford.edu/class/ee364a/lectures/functions.pdf)
PDF pp.6,16,26,27 (slides 3.4,3.14,3.24,3.25),支持范数凸性、Jensen 和受单调性控制的复合。
严格性、插值正域、端点最大化及零半径处理由本节证明,不冒充文献已经给出本 \(G\) 的符号。
NIST [DLMF 4.6.4](https://dlmf.nist.gov/4.6#E4) 支持上述奇次幂对数级数,
64 项截断的具体常数由 32.18 推出。
python-flint [arb 文档](https://python-flint.readthedocs.io/en/latest/arb.html)
成功读取的是显示为 0.9.0 的 latest 页面,介绍球区间及 \(\mathrm{ctx.prec}\);
指定 0.8.0 文档 URL 的实际请求返回 HTTP 403,不宣称读取了它。
实际证书库钉版与版本来自程序自己的运行记录,不由 latest 文档替代。
所有 URL 的访问时刻、字节/hash 和支持范围在报告列明,不把有限检索称为穷尽调查。

仓内直接复用的是第 26 节的一般有限集/等号定理和第 18-19 节的同一比较归一化。
ZECKENDORF_EULER_5040.md 定理 12.3 已给连续—整数差额的精确 KL 分解,
其第 11 章已有另一个 5040 单元的 Robin 证书;本层没有重做这些计算或把 \(G\) 当作该 KL 差额。
QUANTUM-RH.md 的“5040 还给出一个直接的维数障碍”已明确四个普通指数及可逆编码语义。
这些重叠是既有参考输入的归属,不是本节的新发现,也不是 Lean 冻结状态声明。

**32.21 单层摄入与交付边界。** 本层由 caller 指定的隔离 Codex CLI I16
在 consensus-rnd:sshx 1.0.0-beta.42 及其 CODEX_WORKER_SPEC.md 下实施,
flight qgh0910-i16-actual-5040-fixed,attempt 1;repo-prior-exposed。
遵守 CLAUDE 5.11 与本次 brief,无委派、native subagent、额外 worker/oracle 或本轮 review 票;
不声称 sterile priors 或模型族多样性。工作树为
/Users/auricstudio/trureturing-qgh-actual-5040-fixed,
分支 lane/math/quantized-gh-actual-5040-fixed-0910,
immutable BASE 为 fe3f12abe8bc2e14628a93990fee2755c30da2bd。
完整前缀保留 316724 字节、5974 个 LF,SHA256
9229e2affc81243efcdcbd228058d8ca19cea395630a94ae943afde374157dd2。
唯一源改动为追加本节,另加一个报告,canonical 输出仅来自一次
~~~sh
make ingest BASE=fe3f12abe8bc2e14628a93990fee2755c30da2bd SOURCE=arithmetic-boundary-quantization
~~~
全部历史 CAS、entry、报告和输入保留,自动 children、历史 terminal-LF 变体
及每个 producer EOF 字节均原样保留。编号内容单元作完整跨度和有序 chain 拼接核对,
结构标题不要求成为 atom;fingerprint/cas_ref 带 sha256: 前缀,child atom_id 为裸 hash。
源/报告/前后缀身份、完整改动清单与实际 canonical 绑定见实施结论及报告。
该源、证书及其摄入绑定是同一个内容层,不拆出脱离源语义的地址产物。

CPU 只作固定数学核验及必要编排;没有指数/高度/薄层 sweep、候选生成、旧搜索重放、
GPU、daemon、广泛 build/preflight、工具/metadata/Lean/frozen 修复或手工 canonical 规范化。
没有读取 worker 日志、log_ref 内容、caller 转录、同轮 peer 信封或其它 live target。
本节仅比较两个上界,不是 RH 等价判据、Robin 证书、RH 进展、新 GH 定义或 Lean freeze。
其它指数箱体、任意形状/素数、正高度 17 节点、全高度密度与未返回的平移全域结论
都在本层之外;\(G\) 本身的固定裕量不能外推为无界共同高度族的裕量。
全部改动返回 unstaged;不作 stage/commit/push/PR/merge 或生命周期动作。
caller 负责后续封存、公共字节核对、独立评审、普通仓库门与交付;
最终 S21 交付必须等待 S20 MERGED。本次实施不作 termination 判词,
不把有限层的实现或摄入标成持续目标完成。

## 33. Actual5040 common height: strict fractional densities and the moment obstruction

**33.1 Statement, labels and mathematical status.** This S22/C50 appendix implements
the completed C44 primary as PAPER_ARGUMENT / repo-derived reference input.
All logarithms are natural. The ordered prime labels are
\(\mathcal P=(p_1,p_2,p_3,p_4)=(2,3,5,7)\).
Subscripts \(p\in\mathcal P\) are prime labels, so \(h_2=\log2\) and
\(h_3=\log3\); a position \(k\in\{1,2,3,4\}\) instead means \(p_k\).
This differs from section 32's zero-based positional subscripts.
The ordinary exponent vector is \((b_2,b_3,b_5,b_7)=(4,2,1,1)\), with
\(5040=2^4\cdot3^2\cdot5\cdot7\). It is not a Zeckendorf digit string.
We prove a common optimizer for the specified fractional resource problem at every
finite height and a fixed obstruction to optimizing its moments separately.
This is not a sign theorem for \(G=D-\Psi\). GH remains the user's literal,
mathematically unidentified label. No RH equivalence, proof or progress, encoded
orthogonality, arbitrary-prime/shape theorem or Lean admission is asserted.

**33.2 Fixed data and exact height domain.** For each prime label \(p\), set
\(h_p=\log p\), \(c_p^*=(b_p+1)h_p\), \(d_p^*=c_p^*+h_p\), and
\(c_p(T)=c_p^*+T\), \(d_p(T)=d_p^*+T\), where \(T\) is finite and \(T\ge0\).
Thus \(z=e^{-T}\in(0,1]\), \(\alpha_p=e^{-c_p^*}\),
\(\beta_p=e^{-d_p^*}\), and \(A_p=\alpha_p-\beta_p\).

~~~text
prime label p     2          3          5          7
c_p^*            log32      log27      log25      log49
d_p^*            log64      log81      log125     log343
alpha_p          1/32       1/27       1/25       1/49
beta_p           1/64       1/81       1/125      1/343
A_p              1/64       2/81       4/125      6/343
~~~

Define
\[
s_p(z)=\frac{\log((1-\beta_pz)/(1-\alpha_pz))}{h_p},
\qquad w_p(z)=s_p(z)/z\quad(z>0).
\]
Every logarithm has positive argument, since \(0<\beta_p<\alpha_p<1\).
For a separate continuous extension put \(s_p(0)=0\) and
\(w_p(0)=A_p/h_p\). The point \(z=0\) is not a finite height or an actual
translated prime-exponent box. Common translation here is a continuous family;
no arithmetic-lattice attainability is inferred from it.

**33.3 Strict rational logarithm brackets with a derived remainder.** For a fixed
\(p\in\{2,3,5,7\}\), let \(t=(p-1)/(p+1)\in(0,1)\) and
\[
S_p=2\sum_{k=0}^{31}\frac{t^{2k+1}}{2k+1},\qquad
R_p=\frac{2t^{65}}{65(1-t^2)}.
\]
The finite identity \((1-u^2)^{-1}=\sum_{k=0}^{31}u^{2k}
+u^{64}/(1-u^2)\), integrated from 0 to \(t\), gives
\[
\log p=S_p+2\int_0^t\frac{u^{64}}{1-u^2}\,du,
\qquad S_p<\log p<S_p+R_p.
\]
The upper inequality is strict because \((1-u^2)^{-1}<(1-t^2)^{-1}\)
on \(0<u<t\). Exact rational calculation certifies \(L_p<S_p\) and
\(S_p+R_p<U_p\) for the following rational inputs:

~~~text
p      1000000 L_p     1000000 U_p
2      693147         693148
3      1098612        1098613
5      1609437        1609438
7      1945910        1945911
~~~

Consequently \(0<L_p<h_p<U_p\). These are strict proved brackets, not decimal
approximations assumed to be correctly rounded. The odd-power logarithm identity
is classical (NIST DLMF 4.6.4); the finite remainder above supplies its needed bound.

**33.4 Derivative comparison and its lower quadratic.** With the fixed data of
33.2 let \(B_p(z)=(1-\alpha_pz)(1-\beta_pz)\). For \(0\le z\le1\),
\(0<B_p(z)\le1\), and direct differentiation, including cancellation of mixed
terms in the numerator, gives
\[
s_p'(z)=\frac{\alpha_p/(1-\alpha_pz)-\beta_p/(1-\beta_pz)}{h_p}
=\frac{A_p}{h_pB_p(z)}.
\]
For an adjacent ordered pair \((i,j)\in\{(2,3),(3,5),(5,7)\}\), define
\[
N_{ij}=A_ih_jB_j-A_jh_iB_i,\qquad
Q_{ij}=A_iL_jB_j-A_jU_iB_i=q_0+q_1z+q_2z^2.
\]
Then \((s_i-s_j)'=N_{ij}/(h_ih_jB_iB_j)\), and
\[
N_{ij}-Q_{ij}=A_i(h_j-L_j)B_j+A_j(U_i-h_i)B_i>0.
\]
The coefficients, with no implicit multiplication, are
\[
q_0=A_iL_j-A_jU_i,\quad
q_1=-A_iL_j(\alpha_j+\beta_j)+A_jU_i(\alpha_i+\beta_i),
\]
\[
q_2=A_iL_j\alpha_j\beta_j-A_jU_i\alpha_i\beta_i.
\]
All these formulas hold at both endpoints by differentiable extension to an open
neighborhood of \([0,1]\); every denominator there is positive at the endpoints.

**33.5 Complete fixed quadratic certificate.** For the pairs and ascending
coefficients defined in 33.4, the exact rational rows are as follows.
Here \(E_{ij}=Q_{ij}(1)-\delta_{ij}U_iU_j\).

~~~text
(i,j)  q0                     q1                      q2
(2,3)  66157/1296000000        -1963/43200000          -31589/62208000000
(3,5)  7734773/1687500000      -433859/2531250000      -11475851/3417187500000
(5,7)  73135501/2143750000     -541169/5359375000      -69645943/13130468750000

(i,j)  Q_ij(1)                    delta_ij    E_ij
(2,3)  317227/62208000000          1/200000    15697188161267/12150000000000000000
(3,5)  470804057/106787109375      1/500       477045283208311/546750000000000000
(5,7)  27909964602/820654296875    1/100       2261528264218737/840350000000000000
~~~

Substitution into the coefficient formulas proves the first table; summation and
subtraction prove the second. Each row has \(q_1<0,q_2<0,E_{ij}>0\).
Hence, on the entire closed interval, \(Q_{ij}(z)\ge Q_{ij}(1)
>\delta_{ij}U_iU_j\). Also \(0<h_ih_jB_iB_j<U_iU_j\), so 33.4 implies
\[
(s_i-s_j)'(z)>\delta_{ij}\qquad(0\le z\le1).
\]
The sign proof is a global quadratic bound. Its fixed rational verification is
recorded in the report; no height sampling supplies this quantifier.

**33.6 Strict order at every finite height and at the scaled endpoint.** Integrate
the continuous strict derivative inequality in 33.5 from 0 to \(z>0\).
Because \(s_i(0)=s_j(0)=0\), this gives
\[
s_2-s_3>z/200000,\qquad s_3-s_5>z/500,\qquad s_5-s_7>z/100.
\]
Dividing by \(z\) gives the three strict scaled gaps for \(w\).
At \(z=0\), differentiation of \(s_i-s_j\) instead gives
\(w_i(0)-w_j(0)=(s_i-s_j)'(0)>\delta_{ij}\).
Finally \(s_7'>0\) and \(s_7(0)=0\), so
\[
s_2(z)>s_3(z)>s_5(z)>s_7(z)>0\quad(0<z\le1),
\]
\[
w_2(z)-w_3(z)>1/200000,\quad w_3(z)-w_5(z)>1/500,
\quad w_5(z)-w_7(z)>1/100\quad(0\le z\le1).
\]
Also \(w_7(0)=A_7/h_7>0\). None of these scaled bounds attains equality,
including at \(z=0\) and \(z=1\); the constants are not claimed sharp.

**33.7 The exact fractional resource problem.** For finite \(T\ge0\) and real
capacity \(r\), let
\[
K_r=\{y\in[0,1]^4:\sum_{p\in\mathcal P}h_py_p\le r\},\quad
F_0(z)=\sum_p\log(1-\alpha_pz),
\]
\[
D(T,r)=\max_{y\in K_r}\left[F_0(z)+\sum_ph_ps_p(z)y_p\right]\quad(r\ge0).
\]
For \(r<0\), \(K_r\) is empty since its resource is nonnegative: there is no
optimizer or matching finite dual optimum (one may assign value \(-\infty\)).
For every real \(r\ge0\), \(K_r\) is nonempty compact, so the displayed maximum
exists. Put \(H_m=\sum_{k=1}^m h_{p_k}\), \(H_0=0\). Then
\((H_0,H_1,H_2,H_3,H_4)=(0,\log2,\log6,\log30,\log210)\).
If an upper mean-budget \(u\) is used, its residual is
\(r=u-C(T)\), where \(C(T)=\sum_pc_p(T)=\log1058400+4T\).
This is only a change of capacity coordinates. It imposes no lower budget,
strict 5040 cutoff or requirement of two actual slab corners.

**33.8 The common greedy vector, including every boundary.** In the program of
33.7, for every \(r\ge0\) the finite-height optimizer is
\[
y^*_{p_k}(r)=\min\{1,\max\{0,(r-H_{k-1})/h_{p_k}\}\}\quad(k=1,2,3,4).
\]
Its explicit vectors, always in prime-label order \((2,3,5,7)\), are

~~~text
capacity regime        y* = (y_2,y_3,y_5,y_7)
r = 0                  (0,0,0,0)
0 <= r <= H1           (r/h_2,0,0,0)
H1 <= r <= H2          (1,(r-H1)/h_3,0,0)
H2 <= r <= H3          (1,1,(r-H2)/h_5,0)
H3 <= r <= H4          (1,1,1,(r-H3)/h_7)
r >= H4                (1,1,1,1)
at H0,H1,H2,H3,H4      (0,0,0,0); (1,0,0,0); (1,1,0,0); (1,1,1,0); (1,1,1,1)
~~~

Overlapping endpoint formulas give the same vector. The vector is independent
of \(T\), uses exactly \(\min(r,H_4)\) resource, and has one genuinely fractional
coordinate precisely when \(H_m<r<H_{m+1}\). Optimality and uniqueness follow
from the explicit zero-gap proof in 33.10-33.12, without an integer relaxation
being mistaken for an integer optimizer. For \(r>H_4\), unused capacity is
exactly \(r-H_4\); full saturation \(r=H_4\) has zero slack.

**33.9 The complete optimum value.** For the fixed data of 33.2 define, for
\(m=0,\ldots,4\),
\[
F_m(z)=\sum_{k\le m}\log(1-\beta_{p_k}z)
+\sum_{k>m}\log(1-\alpha_{p_k}z).
\]
On \(H_m\le r\le H_{m+1}\), \(m=0,1,2,3\), set
\(\theta=(r-H_m)/h_{p_{m+1}}\in[0,1]\). Substitution of 33.8 gives
\[
D(T,r)=(1-\theta)F_m(z)+\theta F_{m+1}(z)
=F_m(z)+(r-H_m)s_{p_{m+1}}(z).
\]
Thus \(D(T,H_m)=F_m(z)\) for all five prefixes; shared endpoint values agree.
For \(r\ge H_4\), \(D(T,r)=F_4(z)\). These include \(r=0\) and the entire
slack-capacity tail. The proof of maximality is the matching price certificate
below, not merely the evaluation of one feasible vector.

**33.10 A constructive nonnegative primal/dual gap.** Fix \(0<z\le1\),
\(r\ge0\), abbreviate \(s_p=s_p(z)\), and write \(x_+=\max(x,0)\).
For \(\lambda\ge0\) put
\[
\Phi_r(\lambda)=\lambda r+\sum_ph_p(s_p-\lambda)_+.
\]
For every \(y\in K_r\), exact rearrangement gives
\[
\Phi_r(\lambda)-\sum_ph_ps_py_p
=\lambda\left(r-\sum_ph_py_p\right)
+\sum_ph_p\big[(s_p-\lambda)_+-y_p(s_p-\lambda)\big]\ge0.
\]
Each box summand is \(h_p(s_p-\lambda)(1-y_p)\) when \(s_p>\lambda\),
\(h_p(\lambda-s_p)y_p\) when \(s_p<\lambda\), and zero when equal.
It vanishes exactly when the respective nonnegative factor product vanishes.
The upper-box multipliers are \(\mu_p=h_p(s_p-\lambda)_+\); if lower-box
multipliers are also desired, \(\nu_p=h_p(\lambda-s_p)_+\) gives
\(h_ps_p=\lambda h_p+\mu_p-\nu_p\). All are nonnegative.
This proves weak duality directly and will prove attainment by zero gap.
For \(r<0\), \(\Phi_r(\lambda)=\lambda r\) for \(\lambda\ge s_2\), so its
infimum is \(-\infty\), unattained by a finite price, consistently with infeasibility.

**33.11 All matching nonnegative prices.** For finite \(T\ge0\) and the exact
resource program 33.7, the complete sets of optimal resource prices are

~~~text
capacity                         all optimal lambda
r = 0                            [s_2,+infinity)
H_m < r < H_(m+1), m=0,1,2,3     {s_(p_(m+1))}
r = H_m, m=1,2,3                 [s_(p_(m+1)),s_(p_m)]
r = H4                           [0,s_7]
r > H4                           {0}
~~~

Here every \(s\) is evaluated at the same \(z=e^{-T}>0\), and \(H_m\) has the
definition of 33.7. Inserting each listed price and 33.8's vector into every
nonnegative term of 33.10 gives zero. Hence both extrema are attained and
\[
D(T,r)=F_0(z)+\min_{\lambda\ge0}\Phi_r(\lambda).
\]
The upper multipliers for every matching price are the \(\mu_p\) in 33.10.
Strict density inequalities do not make the price unique at prefix boundaries,
at zero capacity or at full saturation. There is no finite matching price for
negative capacity. Completeness, including price endpoints, is proved next.

**33.12 Completeness of prices and uniqueness of vectors.** For the finite-height
program, a price attaining the optimum must have zero 33.10 gap at \(y^*\).
A filled coordinate then requires \(\lambda\le s_p\); an empty one requires
\(\lambda\ge s_p\); a fractional one requires \(\lambda=s_p\).
Positive resource slack requires \(\lambda=0\). These necessary conditions
give exactly all the sets in 33.11, including their closed endpoints.
They also characterize objective equality. In an open prefix interval choose
its positive pivot price. Since all four densities are distinct, zero box gap
forces the earlier coordinates to 1 and later coordinates to 0, and zero budget
gap fixes the remaining fraction. At an internal prefix choose a price strictly
between the adjacent densities; this forces every coordinate of that prefix
vector. At \(r=0\), feasibility already forces \(y=0\). At \(r\ge H_4\),
choose price 0; positive densities force every coordinate to 1. Thus, for every
real \(r\ge0\), objective equality occurs exactly at \(y=y^*\).
In the full multiplier formulation, zero complementary products and stationarity
also force \(\mu_p,\nu_p\) to be the formulas in 33.10 for each listed price;
there are no additional optimal nonnegative box multipliers.

**33.13 Mass-four mixture and permutation labels.** For \(r\ge0\) define the
height-independent positive measure
\[
\mu_r=\sum_{p\in\mathcal P}[(1-y_p^*)\delta_{\alpha_p}+y_p^*\delta_{\beta_p}],
\qquad \mu_r(\mathbb R)=4.
\]
The symbol \(\delta_a\) denotes a point mass, not a gap constant. The exact value is
\(D(T,r)=\int\log(1-za)\,d\mu_r(a)\). This is a coordinate mixture measure
of mass four, not a probability measure of mass one. Away from prefixes below
saturation, the configuration mixture interpolates two corners; its upper corner
has resource \(H_{m+1}>r\). It therefore certifies the fractional mean budget,
not individual integer-budget or slab feasibility of both support corners.
For any permutation \(\pi\) of the four labels, the same clipping formula with
\(\pi\)-ordered prefixes is feasible and uses \(\min(r,H_4)\) resource.
Its value equals \(D\) if and only if its vector equals \(y^*\), by 33.12.
Permuting labels within filled or empty blocks can preserve the vector; at zero
capacity and at or above saturation all 24 labels agree. A unique optimizer
vector is thus compatible with nonunique permutation labels and prices.

**33.14 Density limits and all equality qualifications.** For the fixed family,
\(s_p(z)=zA_p/h_p+o(z)\) as \(z\downarrow0\), directly from differentiability
at zero. Consequently all unscaled densities and all unscaled adjacent gaps
tend to zero as \(T\to\infty\). Each adjacent unscaled gap has infimum 0 on
finite \(T\ge0\), never attained there. There is no finite-height tie, including
\(T=0\). At the formal endpoint \(z=0\), all \(s_p=0\) and the inequalities
\(s_i-s_j>\delta_{ij}z\) extend only as equalities \(0=0\).
The separate scaled extension has \(w_p(0)=A_p/h_p\) and retains every strict
margin in 33.6. An equality in the unscaled endpoint problem is not a scaled
density tie or an equality at an actual finite height.

**33.15 Value limits, endpoint degeneracy and scaled optimization.** For every
fixed real \(r\ge0\), the measure in 33.13 has mass four at strictly positive
support points below 1. Thus \(D(T,r)<0\) for every finite \(T\ge0\),
\(D(T,r)\to0\) from below, and
\[
\lim_{T\to\infty}\frac{D(T,r)}z
=-\sum_p[(1-y_p^*)\alpha_p+y_p^*\beta_p].
\]
At the formal unscaled endpoint \(z=0\), the objective is identically zero on
\(K_r\), so every feasible vector is optimal. The feasible set is a singleton
only for \(r=0\): when \(r>0\), a sufficiently small positive coordinate gives
a second feasible vector. The endpoint dual is \(\Phi_r(\lambda)=\lambda r\):
all \(\lambda\ge0\) are optimal at \(r=0\), and only \(\lambda=0\) is optimal
at \(r>0\). In contrast, the limiting gain divided by \(z\) is
\(\sum_p A_py_p\), with densities \(w_p(0)>0\). Its optimizer remains the
unique \(y^*\), and the complete table 33.11 holds with \(s_p\) replaced by
\(w_p(0)\). The limiting full scaled objective additionally has the constant
\(-\sum_p\alpha_p\), which does not change its optimizers or prices.

**33.16 Logarithm series and moment objectives.** For \(p\in\mathcal P\) and
integer \(n\ge1\), put
\[
a_{p,n}=\frac{\alpha_p^n-\beta_p^n}{h_p},\qquad
J_n(y)=\sum_py_p(\alpha_p^n-\beta_p^n).
\]
The classical logarithm series (NIST DLMF 4.6.1, applied to negative arguments)
gives, for \(0\le z\le1\),
\[
s_p(z)=\sum_{n\ge1}\frac{a_{p,n}}n z^n,\qquad
\mathcal L_z(y):=\sum_ph_ps_p(z)y_p
=\sum_{n\ge1}\frac{z^n}{n}J_n(y).
\]
Indeed \(a_{\max}=\max_p\alpha_p=1/25<1\), and, uniformly on every \(K_r\),
\(0\le J_n(y)\le4a_{\max}^n\). Comparison with a geometric series proves
absolute uniform convergence even at \(z=1\), justifying the sums and subsequent
limits. The first-moment density is \(a_{p,1}=w_p(0)\), whose strict order is
33.6. This does not imply the same order for every \(n\).

**33.17 The prescribed second-moment reversal and primary notation erratum.**
At precisely \(n=2\), direct rational arithmetic gives
\[
\alpha_2^2-\beta_2^2=3/4096,\qquad
\alpha_3^2-\beta_3^2=8/6561.
\]
Since \(3^5=243<256=2^8\), strict monotonicity of logarithms gives
\(h_3/h_2<8/5\). The exact multiplication is
\[
8\cdot19683=157464<163840=5\cdot32768,
\qquad 8/5<32768/19683.
\]
Thus \(19683h_3<32768h_2\), equivalently
\(a_{2,2}=3/(4096h_2)<8/(6561h_3)=a_{3,2}\); equality is impossible.
For historical fidelity, C44's returned conclusion literally used the compressed
tokens `819683` and `532768` in `Since 819683=157464<163840=532768`.
Those are not valid integer equalities as written. The mathematical exposition
explicitly corrects them to `8*19683` and `5*32768`, respectively, as proved above;
the original primary bytes are not edited or silently reinterpreted as a repaired
historical envelope. Only this second-moment pair is evaluated here.

**33.18 A fixed capacity witness against the moment order.** At the exact
capacity \(r=h_2=\log2\), the unique full logarithmic optimizer is
\(y^*=(1,0,0,0)\). The vector
\(\widetilde y=(0,h_2/h_3,0,0)\) is feasible because \(0<h_2/h_3<1\),
and both vectors use resource \(h_2\). By 33.17,
\[
J_2(\widetilde y)-J_2(y^*)=h_2(a_{3,2}-a_{2,2})>0.
\]
Nevertheless for every \(0<z\le1\),
\[
\mathcal L_z(y^*)-\mathcal L_z(\widetilde y)
=h_2(s_2-s_3)>h_2z/200000.
\]
The same difference holds for the full objective after adding \(F_0(z)\).
Thus improving the second moment strictly worsens the full logarithmic value
in this fixed witness. At \(z=0\) the two unscaled full values tie at zero,
while the second-moment inequality itself remains strict.

**33.19 Failure to commute optimization and momentwise maximization.** For fixed
\(r\ge0\), let \(M_n(r)=\max_{y\in K_r}J_n(y)\), which exists by compactness.
The uniform bound in 33.16 also bounds \(M_n\), so
\[
\max_{y\in K_r}\sum_{n\ge1}\frac{z^n}{n}J_n(y)
\le\sum_{n\ge1}\frac{z^n}{n}M_n(r)
\]
is an inequality between finite quantities for \(0\le z\le1\).
At \(r=h_2\), evaluate the left side at its unique \(y^*\). Every difference
\(M_n-J_n(y^*)\) is nonnegative, and 33.18 gives the strict bound
\[
\sum_{n\ge1}\frac{z^n}{n}M_n-
\max_{y\in K_{h_2}}\mathcal L_z(y)
\ge\frac{z^2}{2}h_2(a_{3,2}-a_{2,2})>0\quad(0<z\le1).
\]
Therefore maximizing the full logarithmic sum does not commute with separately
maximizing every moment. For \(z>0\), equality in the general inequality holds
exactly when the full optimizer also maximizes every \(J_n\), since all weights
\(z^n/n\) are positive. Equality holds at \(r=0\) and \(r\ge H_4\), where zero
or full vectors maximize every moment. At \(z=0\) both sides are zero for all
\(r\ge0\). No classification at other capacities or of other second-moment
pairs is asserted. No additional moment order has been sampled.

**33.20 Classical tools and bounded deduplication.** The sorting rule is
literature-attested fractional knapsack: HKUST's
[Lecture 14](https://home.cse.ust.hk/~dekai/271/notes/L14/L14.pdf), PDF pages 4-7,
states decreasing value/weight selection and at most one partial item.
Boyd/Vandenberghe's
[Duality](https://web.stanford.edu/class/ee364a/lectures/duality.pdf), PDF pages
14 and 21-23 (slides 5.12 and 5.19-5.21), attests weak duality and complementary
slackness/KKT. The identities [DLMF 4.6.1](https://dlmf.nist.gov/4.6.E1) and
[DLMF 4.6.4](https://dlmf.nist.gov/4.6.E4) attest the logarithm series.
These sources were retrieved online during this implementation; exact timestamps,
HTTP status, byte identities and extraction limitations are in the report.
The needed remainder, matching gap and all endpoints are proved here.
In this pinned predecessor, 18 and 26.10-26.11 already supply the fractional
framework; 29.5-29.6 concern mass-three mixtures, not this four-label specialization;
32.7-32.8 give the original fixed-height ordering. ZECKENDORF_EULER_5040's chapter
41 F-4 already distinguishes integer budgets from price relaxations. Targeted
text consultation of those volumes and QUANTUM-RH is not a whole-repository or
Lean theorem search. This coordinate specialization is repo-derived, with no
novelty, priority or exhaustive literature-search claim.

**33.21 Primary and fixed-check attribution.** The caller supplied C44 task
293edaba-2898-44f3-8038-c3fd198aa8cb's complete accepted conclusion, envelope SHA256
b885a078d12b09b23156ad92c898a3f044c154caf96f49082cd1cf16130e0aba,
with invocation-specific model observation `6\nPro`. This is previous-stage
mathematical input, not an independent review of this source.
C42 task 5f0129e1-eac7-4bfe-8837-91429f359565 remains formally abstained for its
malformed envelope and damaged executable. Its supplied raw response identity is
82671 bytes, SHA256 75e3e0cf945487ee43b3b2388debfa4e44d629fde3ce8953c4c16ede15114f39.
Its claimed 37 checks were not reproduced. The caller's separate 18-check program
is attributed historical evidence; it was not executed here. C44 reports a new
22-check adaptation (3056 bytes, SHA256
891f93fed300875cc3ceeca81116cff7aedc5b62e86bd77aa75164293151c60f) but returned no
executable bytes, so neither reconstruction nor reproduction is claimed.
Those historical byte identities are caller-supplied, not newly rehashed by I17.
The one report [actual-5040-density-order-0910.md](../../reports/actual-5040-density-order-0910.md)
contains I17's separately identified standalone adaptation and actual execution
receipt; its fixed inputs come from the displayed definitions and caller program.

**33.22 Implementation and remaining obligations.** This is the assigned Codex CLI
I17 implementation flight qgh0910-i17-actual-5040-density-order, attempt 1,
retry budget 1, under caller-pinned consensus-rnd:sshx beta.42 and CLAUDE 5.11.
The work is repo-prior-exposed, with no sterile-context or model-diversity claim,
no worker delegation and no source-review verdict. Only section 33, one report
and canonical ingest outputs form this increment; all predecessor bytes remain.
The new 24-check exact Fraction certificate comprises 18 corresponding caller
checks and six separately counted fixed links; it is executed once, with no
height/prime/exponent/moment sweep, G evaluation, GPU, daemon or historical replay.
The report audits complete numbered spans, actual CAS/child/chain bindings and
historical terminal-LF variants, separately from the one ingest exit code.
C49's translated5040 G theorem and C47's dimension-general transfer remain
unreturned and are neither consumed nor inferred. The caller owns sealing,
public verification, independent source review, ordinary gates and Git delivery;
S22 delivery requires S21 MERGED first. This finite implementation has no
termination authority and does not end the standing continuous research goal.

## 34. Arbitrary-dimension shape transfer with paired increments and closed margins

**34.1 Domain and theorem.** This S23/C55 reference-input appendix implements
the completed C47 PAPER_ARGUMENT / repo-derived perturbation theorem.
Fix any integer \(k\ge2\), finite real \(h_i>0\), \(a_i\ge0\), and
\(m=\min_{1\le i\le k}a_i\). Fix finite \(T_{\min}\ge0\) such that
\(m+T_{\min}>0\). At every finite \(T\ge T_{\min}\), put
\[
c_i=a_i+T,\qquad d_i=c_i+h_i,\qquad C_i=\{c_i,d_i\}.
\]
Admit every finite real \(M_0\le M_1\) for which the closed slab contains
an actual endpoint corner \(x(e)=(c_i+e_i h_i)_{i=1}^k\),
\(e\in\{0,1\}^k\): \(M_0\le\sum_i x_i(e)\le M_1\).
Here actual means a vertex of this specified grid, not a fractional mixture
and not necessarily an arithmetic prime-exponent point. For every finite
\(\epsilon\ge0\) and every vector \(0\le\xi_i\le\epsilon\) with
\(\min_i\xi_i=0\), translate both endpoints in row \(i\) by \(\xi_i\)
and both budgets by \(S=\sum_i\xi_i\). Subscripts \(0,\xi\) compare these
two shapes at the same height and corresponding budgets.

With the definitions in 34.2, write
\[
z=e^{-T}>0,\qquad K=\frac{z}{e^m-z}=\frac1{e^{m+T}-1},\qquad
C=(k-1)\epsilon K.
\]
The denominator is positive. The theorem is
\[
H_0\ge L_0\ge\ell(c)\ge m+T>0,\qquad
H_\xi\ge L_\xi\ge\ell(c+\xi)\ge\ell(c),\qquad L_\xi\ge L_0,
\]
\[
0\le D_\xi-D_0\le C,\qquad 0\le\Psi_\xi-\Psi_0\le C,\qquad
|G_\xi-G_0|\le C.
\]
There is no upper bound on \(k\), no restriction on step ratios and no
positive-width requirement. The one-corner analytical domain is inherited
from 27.2-27.5. A two-corner negative-sign theorem retains its own narrower
hypotheses; 34.14 gives an obstruction to extending such a sign by this estimate.

**34.2 Definitions and Euclidean normalization.** For the domain in 34.1 set
\[
A=\sum_i c_i,\qquad Q=\sum_i h_i,\qquad r=M_1-A,\qquad
I=[M_0/k,M_1/k],\qquad \mu=M_1/k.
\]
For nonempty subsets of the real line, \(\operatorname{dist}(E,F)\)
means \(\inf\{|v-w|:v\in E,\ w\in F\}\). Define
\[
\Delta_i=\operatorname{dist}(I,C_i),\quad
V_0=\sum_i\Delta_i^2,\quad
\rho=\frac{\|\Delta\|_2}{\sqrt{k(k-1)}}=\sqrt{\frac{V_0}{k(k-1)}},
\quad L=\mu-\rho,\quad H=\mu+(k-1)\rho.
\]
The subscript in \(V_0\) is the historical distance-variance notation; it
does not select the unperturbed shape. There is no additional division by
\(k\) in \(V_0\). On \(x>0\), let \(f(x)=\log(1-e^{-x})\), with natural logarithms.
Using the entire fractional polytope, set
\[
\mathcal P=\{y\in[0,1]^k:\sum_i h_i y_i\le r\},\qquad
J_0(y)=\sum_i\big((1-y_i)f(c_i)+y_i f(d_i)\big),
\]
\[
D_0=\max_{y\in\mathcal P}J_0(y),\qquad
\Psi_0=(k-1)f(L_0)+f(H_0),\qquad G_0=D_0-\Psi_0.
\]
Perturbed definitions replace \(c_i,d_i,M_j\) by
\(c_i+\xi_i,d_i+\xi_i,M_j+S\); thus \(J_\xi\) uses the translated endpoints.
The lower budget enters \(I\), not an extra lower constraint on \(y\).
This is exactly the positive-grid comparison of 27.3, including its
classically matched price formulation; a greedy representation is not needed here.

Throughout, \(\langle v,w\rangle=\sum_i v_iw_i\) and
\(\|v\|_2=\sqrt{\langle v,v\rangle}\) are ordinary Euclidean quantities.
For \(\mathbf1=(1,\ldots,1)^{\mathsf T}\) define
\[
\bar v=\frac1k\sum_i v_i,\qquad
\Pi=\operatorname{Id}-\frac1k\mathbf1\mathbf1^{\mathsf T},\qquad
\ell(v)=\bar v-\frac{\|\Pi v\|_2}{\sqrt{k(k-1)}}.
\]
Then \(\Pi v=v-\bar v\mathbf1\), \(\langle\Pi v,\mathbf1\rangle=0\) and
\(\|v\|_2^2=k\bar v^2+\|\Pi v\|_2^2\). This projection is a choice of
inner product, not orthogonality supplied by prime labels or an encoding.

**34.3 Exact corner, slab and capacity correspondence.** For every binary
index \(e\) in 34.1, the total \(A+\sum_i e_i h_i\) becomes
\(A+S+\sum_i e_i h_i\). Therefore
\[
M_0\le A+\sum_i e_i h_i\le M_1
\quad\Longleftrightarrow\quad
M_0+S\le A+S+\sum_i e_i h_i\le M_1+S.
\]
The inverse subtracts \(S\) from both budgets. It preserves each individual
corner's membership, endpoint equalities, slab width, and the number of
distinct actual corner vectors. Different vectors with equal totals remain
different; no strict ordering of corner totals is assumed. Thus the whole
one-corner domain is in bijection with its translated domain, and the
positive-width and at-least-two-corner subclasses are preserved separately.

The perturbed lower total is \(A_\xi=A+S\), so
\[
r_\xi=(M_1+S)-(A+S)=M_1-A=r,\qquad \mathcal P_\xi=\mathcal P_0.
\]
This preserves every feasible fractional vector, not only one presumed
optimal face. An admitted corner is coordinatewise at least \(c\), hence
\(M_1\ge A\ge k(m+T)>0\), \(r\ge0\), and \(0\in\mathcal P\).
The polytope is nonempty and compact. Its finite continuous objectives attain
their maxima. Endpoint density ties, nonunique maximizers and changes in
the maximizing face do not affect this argument.

**34.4 Positive support from the published lower-support lemma.** The
coordinatewise monotonicity of \(\ell\) is the existing theorem 27.4,
not a new theorem of this layer. Its relevant proof is short enough to
state with the application. For a standard basis vector \(e_i\),
\[
\|\Pi e_i\|_2^2=(k-1)/k,\qquad
\frac{\|\Pi e_i\|_2}{\sqrt{k(k-1)}}=\frac1k.
\]
For any \(v\in\mathbb R^k\) and \(b\ge0\), the triangle inequality gives
\[
\ell(v+be_i)-\ell(v)
=\frac bk-\frac{\|\Pi v+b\Pi e_i\|_2-\|\Pi v\|_2}{\sqrt{k(k-1)}}
\ge0.
\]
Successive coordinate increases prove \(v\le w\Rightarrow\ell(v)\le\ell(w)\).
Weak inequality is essential: 27.4 includes the zero increment and positive
collinear equality cases.

Choose any admitted actual corner \(x\). Since \(\bar x\in I\) and
\(\mu\ge\bar x\), every row satisfies
\(0\le\Delta_i\le|x_i-\bar x|\). Hence
\[
\rho\le\frac{\|\Pi x\|_2}{\sqrt{k(k-1)}},\qquad
L\ge\ell(x)\ge\ell(c)\ge\ell((m+T)\mathbf1)=m+T>0.
\]
Here \(x\ge c\ge(m+T)\mathbf1\). Apply the same argument to the translated
admitted corner \(x+\xi\) and lower vector \(c+\xi\); it gives
\[
L_\xi\ge\ell(c+\xi)\ge\ell(c)\ge m+T.
\]
In each grid \(\rho\ge0\) implies \(H\ge L\). This is precisely the
27.5 mechanism and establishes positive support before any derivative of
\(f\) is used. One corner, including a corner at a budget endpoint, suffices.
The further comparison \(L_\xi\ge L_0\) follows from the actual radius bounds
in 34.6, not from comparing these two lower bounds alone.

**34.5 Centered endpoint displacement and distance Lipschitz bound.** For
corresponding slabs define
\[
u=S/k,\qquad q=\xi-u\mathbf1=\Pi\xi,\qquad t=\rho_\xi-\rho_0.
\]
The perturbed interval is \(I+u\). Translating both arguments in a distance
back by \(u\) shows
\[
\Delta_i^\xi=\operatorname{dist}(I,\{c_i+q_i,d_i+q_i\}).
\]
For every \(v\in I\), \(w\in C_i\), the triangle inequality gives
\(|v-(w+q_i)|\le|v-w|+|q_i|\). Taking infima gives
\(\Delta_i^\xi\le\Delta_i^0+|q_i|\); reversing the translation gives the
opposite inequality. Consequently
\[
|\Delta_i^\xi-\Delta_i^0|\le|q_i|,\qquad
|t|\le\frac{\|\Delta^\xi-\Delta^0\|_2}{\sqrt{k(k-1)}}
\le\frac{\|q\|_2}{\sqrt{k(k-1)}}.
\]
The first norm comparison is the reverse triangle inequality. No nearest
endpoint is selected for differentiation. These statements include distance
ties, switches of the nearest endpoint, vanishing distances and either zero
norm. They impose no stable critical-node topology.

**34.6 Both bounds on the actual radius change and the signed argument shifts.**
The nonnegative shifts and a zero coordinate imply
\[
0\le S\le(k-1)\epsilon,\qquad
\|q\|_2^2=\sum_i\xi_i^2-\frac{S^2}{k}.
\]
First, \(\sum_i\xi_i^2\le S^2\), since all cross products are nonnegative.
Combining this with 34.5 yields
\[
|t|\le\frac{\sqrt{(k-1)S^2/k}}{\sqrt{k(k-1)}}=\frac Sk=u.
\]
Second, \(\xi_i^2\le\epsilon\xi_i\) gives
\(\sum_i\xi_i^2\le\epsilon S\), and therefore
\[
|t|\le\frac{\sqrt{S(k\epsilon-S)}}{k\sqrt{k-1}}.
\]
Both are simultaneous bounds on the same radius difference produced by the
distances. Their radicands are nonnegative because
\(0\le S\le(k-1)\epsilon\le k\epsilon\). No positive lower bound on
\(S\) or \(\epsilon\) was used.

Since \(\mu_\xi-\mu_0=u\), the actual envelope argument shifts are
\[
L_\xi-L_0=u-t\ge0,\qquad H_\xi-H_0=u+(k-1)t.
\]
The second shift can be negative; it is not assigned a sign in general.
Neither radius bound is presumed attained, and \(t\) is not a free
parameter chosen independently of the slab geometry.

**34.7 Dimension-general weighted displacement with signs checked before squaring.**
For the \(u,t\) in 34.5-34.6 define
\[
B=(k-1)|u-t|+|u+(k-1)t|.
\]
We prove \(B\le(k-1)\epsilon\). Since \(u\ge|t|\), the first absolute value is
\(u-t\). If \(u+(k-1)t\ge0\), cancellation gives
\[
B=(k-1)(u-t)+u+(k-1)t=ku=S\le(k-1)\epsilon.
\]
Otherwise \(t<0\), and the second actual-radius bound gives
\[
B=(k-2)u-2(k-1)t
\le\frac{(k-2)S+2\sqrt{(k-1)S(k\epsilon-S)}}k.
\]
Set
\[
A_0=k(k-1)\epsilon-(k-2)S,\qquad
R=2\sqrt{(k-1)S(k\epsilon-S)}.
\]
Before comparing squares, \(k-2\ge0\) and \(S\le(k-1)\epsilon\) imply
\[
A_0\ge2(k-1)\epsilon\ge0,\qquad R\ge0.
\]
Direct polynomial expansion proves
\[
\begin{aligned}
A_0^2-R^2
&=k^2(k-1)^2\epsilon^2
 -2k^2(k-1)\epsilon S+k^2S^2\\
&=k^2\big(S-(k-1)\epsilon\big)^2\ge0.
\end{aligned}
\]
Thus \(A_0\ge R\). Substitution into the displayed bound for \(B\) proves
\[
\boxed{(k-1)|L_\xi-L_0|+|H_\xi-H_0|\le(k-1)\epsilon.}
\]
For \(k=2\), the negative-high-shift case is impossible because \(u+t\ge0\).
If \(S=0\) or \(\epsilon=0\), nonnegativity forces \(\xi=0\), \(u=t=B=0\).
Nothing was divided by either of these quantities. The historical single
symbolic audit concerns only the displayed polynomial identity; the radius
connection and nonnegative square-root premises are the analytical proof above.

**34.8 The mixed-objective increment is nonnegative and bounded.** For
\(x\ge m+T>0\),
\[
0<f'(x)=\frac1{e^x-1}\le K=\frac z{e^m-z}.
\]
For either row endpoint \(w=c_i\) or \(d_i\), the segment from \(w\) to
\(w+\xi_i\) lies in this domain, so the mean-value inequality gives
\[
0\le f(w+\xi_i)-f(w)\le \xi_i K.
\]
Every \(y\) in the common \(\mathcal P\) has nonnegative row weights
\(1-y_i,y_i\) summing to one. Summing the endpoint inequalities gives
\[
0\le J_\xi(y)-J_0(y)\le SK.
\]
Comparison of maxima over exactly this common set now yields
\[
D_0\le D_\xi\le D_0+SK\le D_0+(k-1)\epsilon K.
\]
For example, the upper inequality follows by applying
\(J_\xi(y)\le J_0(y)+SK\le D_0+SK\) to every \(y\); the lower one follows
at a maximizer of \(J_0\). No density order or differentiability of a
maximum is assumed. This covers different optimal faces and every capacity
allowed by 34.3.

**34.9 The envelope increment is nonnegative even if its high argument decreases.**
On positive support \(f''(x)=-e^x/(e^x-1)^2<0\). Reuse 26.5's function
\[
F(\mu,r)=(k-1)f(\mu-r)+f(\mu+(k-1)r),\qquad r\ge0,\quad\mu-r>0.
\]
With \(L=\mu-r\), \(H=\mu+(k-1)r\),
\[
F_\mu=(k-1)f'(L)+f'(H)>0,\qquad
F_r=(k-1)(f'(H)-f'(L))\le0.
\]
If the actual change \(t\ge0\), then \(u\ge t\), so both argument shifts
\(u-t\) and \(u+(k-1)t\) are nonnegative. Increasing \(f\) proves
\(\Psi_\xi\ge\Psi_0\).

If \(t<0\), first increase the mean from \(\mu_0\) to \(\mu_0+u\) at
radius \(\rho_0\); then decrease the radius to the actual
\(\rho_\xi=\rho_0+t\ge0\) at the new mean. Each operation weakly increases
\(F\). Along the first segment the lower support is \(L_0+v\ge m+T\)
for \(0\le v\le u\). Along the second it is at least \(L_0+u\ge m+T\),
and the radius remains nonnegative, so \(H\ge L>0\).
All calculus therefore stays in the valid domain, including a final
radius zero. In particular, a negative value of \(H_\xi-H_0\) does not
invalidate the nonnegative total envelope increment.

**34.10 The envelope increment has the same upper bound.** By 34.4, both
ends of the scalar segment joining \(L_0,L_\xi\) lie in \([m+T,\infty)\);
the same holds for the segment joining \(H_0,H_\xi\), even when \(H\) decreases.
The derivative bound of 34.8 applies to each whole segment. Together with
34.7 this gives
\[
\begin{aligned}
|\Psi_\xi-\Psi_0|
&\le K\big((k-1)|L_\xi-L_0|+|H_\xi-H_0|\big)\\
&\le(k-1)\epsilon K=C.
\end{aligned}
\]
Combine this upper bound with the separately proved sign in 34.9:
\[
\boxed{0\le\Psi_\xi-\Psi_0\le C.}
\]
The segment estimate alone would give only an absolute bound; its
nonnegative sign comes from the mean/radius argument, not from an
unsupported assumption that both endpoints increase.

**34.11 The common interval before subtraction and the bound for \(G\).**
At every point of the full domain of 34.1, 34.8 and 34.10 have already shown
\[
d:=D_\xi-D_0\in[0,C],\qquad p:=\Psi_\xi-\Psi_0\in[0,C],
\qquad C=\frac{(k-1)\epsilon z}{e^m-z}.
\]
Only now subtract. Since two numbers in \([0,C]\) differ by at most its
length, \(-C\le d-p\le C\). Therefore
\[
\boxed{|G_\xi-G_0|\le\frac{(k-1)\epsilon z}{e^m-z}.}
\]
The loss is this one interval length, not its double. Adding two unsigned
Lipschitz estimates would lose the separately established paired signs.
This is a valid uniform common-increment bound; no sharpness or optimal
Lipschitz constant for \(G\) is claimed, and it does not establish the
sign of an unperturbed grid.

**34.12 Zero radius, zero perturbation and the height boundary.** The proof
in 34.5 uses no derivative of a distance minimum or a norm. Closest endpoints
may switch and tie, and any distance may become zero. If \(\rho_0=0\), then
\(t=\rho_\xi\ge0\); if \(\rho_\xi=0\), the decreasing-radius path of 34.9
ends at a permitted boundary point. At either zero radius,
\(H=L=\mu\) and \(\Psi=kf(\mu)\). Every estimate remains valid.

If merely \(S=0\), nonnegative coordinates force \(\xi=0\); this includes
\(\epsilon=0\) and also an unused positive upper bound \(\epsilon\).
Both increments and \(G_\xi-G_0\) then vanish. The theorem does not require
\(\epsilon=\max_i\xi_i\). The endpoint \(T=T_{\min}\) is included:
if \(m=0\), it requires \(T_{\min}>0\); if \(T_{\min}=0\), it requires \(m>0\).
Infinite \(T\) and \(z=0\) are limits, not admitted points. The estimates
use \(e^T=1/z\) only for \(z>0\). For fixed finite \(\epsilon\), their
unscaled difference bound tends to zero as \(T\) tends to infinity;
this is not a uniform unscaled negative margin or a new optimizer theorem
at the limiting point.

**34.13 Corners, equal totals, zero width and full saturation/slack.** One
actual corner suffices for the analytical theorem, including a corner
at either endpoint and \(M_0=M_1\). Two distinct corner vectors may have
the same total for arbitrary steps. For example, if \(h_1=h_2=h>0\),
the corners with just coordinate 1 or just coordinate 2 raised have total
\(A+h\); the zero-width slab \([A+h,A+h]\) contains both. Translation
preserves these two vectors and their equal totals separately. This example
does not extend the positive-width sign domains of sections 30 or 31.

Write \(r=M_1-A\ge0\) and \(Q=\sum_i h_i>0\). At \(r=0\), positivity of
every \(h_i\) forces \(\mathcal P=\{0\}\), so \(D=\sum_i f(c_i)\).
At \(r=Q\), and also at every slack capacity \(r>Q\), \(\mathcal P=[0,1]^k\).
Since \(f(d_i)>f(c_i)\), its maximum is \(D=\sum_i f(d_i)\) at the full
upper vector. Tight full saturation and slack above it are both covered.
For \(0<r<Q\), the pointwise proof in 34.8 covers all feasible weights,
including fractional or integer optimizers, density ties and nonunique faces.
Changing \(M_0\), even below zero, introduces no lower mixture constraint.
The upper budget is finite at each point but has no uniform finite upper bound.

**34.14 A one-corner zero-sign witness.** To see why the analytical domain
does not imply a negative baseline on that whole domain, choose any positive
steps, let all \(a_i=0\), and fix \(T>0\) with \(T_{\min}=T\).
Set \(M_1=kT=A\) and choose any finite \(M_0\le M_1\).
Only the lower corner is admitted: raising any coordinate increases its
total strictly above \(M_1\). The capacity is zero and every row distance
is zero because \(T=M_1/k\in I\). Thus
\[
D_0=\sum_i f(T)=kf(T),\qquad \rho_0=0,\qquad
\Psi_0=kf(T),\qquad G_0=0.
\]
This includes both \(M_0=M_1\) and \(M_0<M_1\).
In particular, even the zero perturbation cannot turn a two-corner
negative-margin theorem into a one-corner negative theorem.
A transferred sign requires a separately proved margin on the actual
inverse-image family, as stated next.

**34.15 Transfer of a separately supplied scaled margin.** Keep the fixed
data and height domain of 34.1. Let \(\mathcal W_T\) be any family of baseline
slabs in that domain for which a separate theorem proves, with one
\(\eta>0\) independent of finite \(T\) and of the slab,
\[
e^T G_0(M_0,M_1)<-\eta.
\]
For each allowed shape \(\xi\), define the target family exactly as
\[
\mathcal W_{T,\xi}
=\{(M_0+S,M_1+S):(M_0,M_1)\in\mathcal W_T\}.
\]
Every inverse image must be covered by the assumed baseline theorem; its
corner-count and width conditions are retained. Put
\[
d_{\min}=e^m-e^{-T_{\min}}>0.
\]
Multiplication of 34.11 by \(e^T>0\) gives
\[
|e^T(G_\xi-G_0)|
\le\frac{(k-1)\epsilon}{e^m-e^{-T}}
\le\frac{(k-1)\epsilon}{d_{\min}}.
\]
The second denominator inequality follows from \(T\ge T_{\min}\).
At every corresponding finite point it follows that
\[
e^TG_\xi<-\eta+\frac{(k-1)\epsilon}{e^m-e^{-T}}
\le-\eta+\frac{(k-1)\epsilon}{d_{\min}}.
\]
The first inequality is strict because the baseline bound is strict,
even if every subsequent loss estimate attains equality.

**34.16 Complete closed-radius statement and retained margins.** Under the
separate baseline hypothesis of 34.15, for every \(0\le\gamma\le\eta\),
\[
0\le\epsilon\le\frac{(\eta-\gamma)d_{\min}}{k-1}
\quad\Longrightarrow\quad
\boxed{e^TG_\xi<-\gamma\quad
\text{on every }\mathcal W_{T,\xi},\ T_{\min}\le T<\infty.}
\]
Indeed \((k-1)\epsilon/d_{\min}\le\eta-\gamma\), and substitution into
the strict inequality in 34.15 proves the assertion. In particular,
\[
\epsilon\le\frac{\eta\,d_{\min}}{2(k-1)}
\quad\Longrightarrow\quad e^TG_\xi<-\eta/2,
\qquad
\epsilon\le\frac{\eta\,d_{\min}}{k-1}
\quad\Longrightarrow\quad e^TG_\xi<0.
\]
The raw primary token etadmin denotes the product eta*dmin, explicitly
\(\eta\,d_{\min}\), as fixed by the preceding general \(\gamma\) formula;
the raw token is preserved in the provenance report. It is not a new symbol.
The endpoints \(\epsilon=(\eta-\gamma)d_{\min}/(k-1)\) and
\(T=T_{\min}\) may hold simultaneously without losing strictness.
The case \(\gamma=\eta\) requires \(\epsilon=0\) and recovers the baseline;
\(\gamma=0\) retains strict negativity. These are pointwise strict bounds
throughout the admitted finite domain. They do not assert that a limiting
supremum over that domain is strictly below the same right-hand side.

**34.17 Exact inverse image of a fixed strict cutoff.** Let \(B_{\rm cut}\)
be a fixed finite number and retain the notation \(M_j^\xi=M_j^0+S\).
Then the exact equivalence is
\[
M_0^\xi>B_{\rm cut}
\quad\Longleftrightarrow\quad M_0^0>B_{\rm cut}-S.
\]
In particular it is not generally equivalent to \(M_0^0>B_{\rm cut}\).
The baseline cutoff-restricted domain maps onto exactly the target subset
\[
M_0^\xi>B_{\rm cut}+S,
\]
with all other baseline family restrictions still imposed. Translation is
a bijection of the full corresponding wider domains in 34.3, but need not
be a bijection of the two domains using the same fixed strict cutoff.
This generalizes the warnings in 30.12 and 31.14, preserving their meaning.
A baseline theorem on all inverse-image slabs, for example the entire wider
two-corner domain, permits intersection of the transferred result with
the original cutoff afterward. A theorem known only above the old cutoff
does not supply that premise.

**34.18 Strict uniform buffers and a two-corner endpoint counter-witness.**
For the bound \(S\le(k-1)\epsilon\), a sufficient shape-uniform target
buffer for a baseline theorem above \(B_{\rm cut}\) is
\[
M_0^\xi>B_{\rm cut}+(k-1)\epsilon.
\]
It implies \(M_0^\xi>B_{\rm cut}+S\), hence \(M_0^0>B_{\rm cut}\).
Alternatively, to cover all target slabs with \(M_0^\xi>B_{\rm cut}\),
it suffices to prove the baseline theorem on the larger strict domain
\[
M_0^0>B_{\rm cut}-(k-1)\epsilon,
\]
with its other hypotheses retained. Indeed
\(M_0^0=M_0^\xi-S>B_{\rm cut}-S\ge B_{\rm cut}-(k-1)\epsilon\).
These sufficient conditions are strict. Replacing the target buffer by
a weak inequality can leave \(M_0^0=B_{\rm cut}\) when
\(S=(k-1)\epsilon\), so the old strict theorem cannot be applied there.

There is a positive-width, two-actual-corner witness to the domain failure.
Whenever \(A=B_{\rm cut}\), let \(h_*=\min_i h_i>0\).
The baseline slab \([A,A+h_*]\) contains the lower corner and a corner
obtained by raising a minimum-step coordinate, at its two endpoints.
It fails the strict cutoff. For every permitted shape with \(S>0\),
the translated slab \([A+S,A+S+h_*]\) clears the same fixed cutoff.
For \(S=(k-1)\epsilon>0\), it also attains equality in the weak uniform
target-buffer condition just discussed. At \(T=0\) the continuous fixed5040
family has \(A=B_{\rm cut}=\log1058400\) by 32.3, so this exact witness
applies. It uses neither an unproved mass/tail sign nor a claim of
prime-lattice attainability for the translated box.

**34.19 Recovery of the published three-dimensional constants.** For
\(k=3\), all \(a_i=0\), and \(T_{\min}=\log2\), one has
\[
m=0,\qquad d_{\min}=1-\tfrac12=\tfrac12,\qquad
|e^T(G_\xi-G_0)|\le4\epsilon.
\]
The zero coordinate and \(0\le\xi_i\le\epsilon\) are as in 34.1.
Use the separately published positive-width two-corner wider domains:
30.2 and 30.11 for \((\log2,\log3,\log5)\), and 31.2 and 31.13 for
\((\log2,\log3,\log7)\). The baseline margins, closed radii and retained
strict margins are exactly
\[
(\eta,\epsilon_{\max},\gamma)
=(1/60,1/480,1/120)\quad\text{for }(2,3,5),
\]
\[
(\eta,\epsilon_{\max},\gamma)
=(1/40,1/320,1/80)\quad\text{for }(2,3,7).
\]
Indeed \((\eta-\eta/2)d_{\min}/2=\eta/8\) in dimension three.
Thus 34.16 recovers 30.16 and 31.17, including closed radius and
\(T=\log2\) simultaneously. Their finite-node sign certificates are
inherited facts, not re-executed or independently revalidated in this layer.
Their strict-width and two-corner hypotheses remain in force.
Intersection with the original strict 5040 domain is legitimate because
these particular baselines already hold on their respective wider domains.

**34.20 The four-dimensional 5040 consequence remains conditional.** Take
\[
k=4,\qquad h=(\log2,\log3,\log5,\log7),\qquad
a=(5\log2,3\log3,2\log5,2\log7)
=(\log32,\log27,\log25,\log49),\qquad T_{\min}=0.
\]
These are the lower coordinates associated with ordinary exponents
\((4,2,1,1)\) in 32.2-32.3; subsequent common translation is a continuous
family. Here
\[
m=\log25,\qquad d_{\min}=24,\qquad
|e^T(G_\xi-G_0)|\le3\epsilon/24=\epsilon/8.
\]
Only if a separate theorem establishes the full wider-domain bound
\[
e^TG_0<-1/2000
\]
for every finite \(T\ge0\) and every corresponding finite positive-width
real slab containing two actual translated corners, without the fixed
lower cutoff, does 34.16 imply
\[
0\le\epsilon\le1/500\quad\Longrightarrow\quad e^TG_\xi<-1/4000
\]
on that whole translated class. The calculation is
\((1/2000-1/4000)\,24/3=1/500\); it includes \(T=0\) and the closed
radius boundary. A subsequent intersection with
\(\log1058400<M_0^\xi<M_1^\xi\) is then valid.
A baseline result limited to the old cutoff instead supports only
inverse-image-covered slabs, such as the buffers of 34.17-34.18.

The raw C47 response calls this open mass/tail obligation C45.
That is its historical name: the original C45 and later C49 carriers
failed, and the still-open full mathematical obligation is now carried
by C51. No old flight is revived or relabeled. No C51 result is supplied
or inferred here. Section 32's fixed \(T=0\), cutoff-restricted certificate
and section 33's density order do not establish this wider-domain margin.

**34.21 Proof attribution and preserved primary evidence.** The lower-support
theorem is reused from 27.4-27.5 and the envelope derivative signs from 26.5.
The projection/distance and paired-nonnegative-increment method already
appears in 30.12-30.15 and 31.14-31.16 within their stated three-dimensional
domains. The arbitrary-\(k\) two-radius estimate, weighted displacement
with its signed square comparison, and precise closed-margin/cutoff
combination are the specialized repo-derived extension validated by C47.

Triangle and reverse-triangle inequalities, elementary calculus and
comparison of maxima over a common set are classical. For inherited
literature evidence, 26.28 attests Boyd/Vandenberghe's
[Convex functions](https://web.stanford.edu/class/ee364a/lectures/functions.pdf),
slides 3.4 and 3.14 (PDF pages 6 and 16), for norms/convexity and Jensen;
26.28 and 33.20 attest HKUST's
[Lecture 14](https://home.cse.ust.hk/~dekai/271/notes/L14/L14.pdf),
PDF pages 4-7, for fractional knapsack. The latter locates the inherited
interpretation of \(D\); this proof uses the full polytope directly.
These are inherited source-attested references, not documents freshly
retrieved by I18 and not literature proofs of this particular transfer theorem.
No necessary new classical premise required an external query.
The actual I18 literature work was bounded consultation of the pinned
source and those recorded attributions; external retrievals and priority
searches were zero. No novelty or priority claim is made.

The completed previous-stage actual PRO primary is task
192f8575-55cf-4bc0-b180-dd0589f9c31f, conversation conv_efec2f91277779d1,
completed 2026-09-09T23:55:45.528Z, original envelope SHA256
e5d84e0dc8c6935b329694f3cf278151543a4ce4460cf0e1d42d4371cd5ce822.
Its task-observed display was 6/Pro: invocation-display evidence only,
not hidden serving identity or independent model-family diversity.
The [single report](../../reports/quantized-gh/dimension-general-transfer-0910.md)
preserves the raw response as TEXT data, including etadmin and the
historical C45 label, the exact symbolic program with final LF and SHA,
and its original one-run receipt and preregistration.
No historical mathematical certificate is executed by this implementation.

**34.22 Implementation scope and remaining obligations.** This is the
assigned Codex CLI I18 flight qgh0910-i18-dimension-general-transfer,
attempt 1, retry budget 1, implementation stage, under the caller-pinned
consensus-rnd:sshx 1.0.0-beta.42 skill and worker specification,
with CLAUDE 5.11's repository overrides. It is repo-prior-exposed;
there is no delegation, independent source-review vote, sterile-context
or model-diversity claim. The layer consists of section 34, one report,
and the canonical ingestion outputs, preserving the entire predecessor
source prefix and all historical atoms, entries, reports and LF variants.
The report records the one canonical ingest, complete new-unit and
inherited-final-unit CAS coverage, and all observed whitespace diagnostics.
Structural byte/hash/span checks are not mathematical theorem proofs.
Implementation mathematical-code executions, numerical probes, searches
and GPU dispatches are zero; the caller's original single symbolic
execution belongs to its different historical stage.

The theorem does not imply a general all-grid sign, sharp \(G\) constant,
arbitrary nonzero-shape prime-lattice density, exact common prime
translation, encoding-induced orthogonality, uniform unscaled negative
margin, a new GH definition, an RH result or Lean/kernel certification.
C51's full wider-domain 5040 margin remains open; pending C53 and C54
results are not imported. The historical statement in 33.22 that C47 was
unreturned describes that I17 handoff and is preserved unchanged.
At this I18 handoff the changes are unstaged, the index is unchanged,
and S23 has not been delivered. The caller owns sealing, public verification,
independent review, ordinary gates and Git/PR delivery; final S23 delivery
requires S22 MERGED. This finite implementation has no lifecycle or
termination authority and does not end the standing continuous goal.

## 35. Fixed-prime recurrence, actual near-balanced boxes and logarithmic counting

**35.1 Statement and inherited scope.** This S24/C66 reference-input appendix
implements the completed C64 analytical primary as PAPER_ARGUMENT / repo-derived.
For every fixed ordered list of distinct primes \(p_0,\ldots,p_{k-1}\), every
integer \(k\ge2\), and every fixed integer \(Q\ge3\), the strict simultaneous
return set defined in 35.2 has positive natural density on its actual compact
orbit closure, uniformly over consecutive blocks. Its density is at least
\(Q^{-(k-1)}\), its forward returns are syndetic with a rotation-dependent
bound, and nearest rounding produces actual nonnegative integer exponent boxes.
Their distinct lower-corner integers have counting function
\((d_Q/(k\log p_0))\log X+o(\log X)\). The proof is given in 35.3-35.18.
No joint independence of reciprocal prime logarithms is assumed.

Sections 30.17 and 31.18 already give qualitative homogeneous approximation
near zero relative shape. Their arguments are not replayed as a new search;
the present addition supplies fixed-neighborhood frequency, return gaps and
integer counting. Sections 30.16 and 31.17 are the only inherited sign inputs
to the applications in 35.19-35.23, after their domains are checked. Their
finite-node and moment certificates are not independently recertified here.
Classical tools and the specialized deductions are distinguished in 35.28.
This is neither independent review nor a Lean/kernel-frozen or RH theorem.

**35.2 Fixed parameters and distinct height symbols.** All logarithms are
natural. Fix the primes, \(k\) and \(Q\) as in 35.1 throughout all limits, and set
\[
d=k-1,\qquad h_i=\log p_i>0,\qquad
\alpha_i=h_0/h_i\ (1\le i\le d),\qquad
\alpha=(\alpha_1,\ldots,\alpha_d).
\]
Write \(\mathbb T=\mathbb R/\mathbb Z\),
\(\|t\|_{\mathbb T}=\min_{a\in\mathbb Z}|t-a|\), and
\[
H=\overline{\{n\alpha:n\in\mathbb Z\}}\subseteq\mathbb T^d,
\qquad r=1/Q,\qquad
U_Q=\{x\in H:\max_{1\le i\le d}\|x_i\|_{\mathbb T}<r\},
\]
\[
B_Q=\{n\in\mathbb Z_{\ge1}:n\alpha\in U_Q\},\qquad
d_Q=\mu_H(U_Q),\qquad
S_h=\sum_{i=0}^{k-1}h_i,\quad h_{\max}=\max_i h_i,\quad
E_Q=\frac1Q\sum_{i=1}^{d}h_i.
\]
Here \(\mu_H\) is normalized Haar probability, justified in 35.3. The group
\(H\) need not be the full torus or connected. The source's earlier slab
symbol \(Q=\sum h_i\) is denoted \(S_h\) in this section, so it cannot be
confused with the integer recurrence parameter. For each rounded box below,
\(T_n=\min_i c_i\) is its lower height and \(A_n=\sum_i c_i\) is its total;
these two quantities have different roles and are never identified.

**35.3 Individual irrationality and Haar probability.** If
\(\alpha_i=u/v\in\mathbb Q\), positivity permits positive integers \(u,v\)
with \(v\log p_0=u\log p_i\). Exponentiating gives
\(p_0^v=p_i^u\), contradicting unique prime factorization. Thus each
\(\alpha_i\) is irrational. This proves no rational independence of
\(1,\alpha_1,\ldots,\alpha_d\).

The integer orbit is a subgroup of \(\mathbb T^d\). If two sequences from
that subgroup converge, continuity of subtraction puts the difference of
their limits in its closure. Hence \(H\) is a closed subgroup. It is compact
and metrizable, as a closed subset of a compact metrizable torus. The classical
Haar theorem supplies a unique translation-invariant regular Borel probability
\(\mu_H\). No connectedness or ambient positive-volume premise is used.

**35.4 Restricted characters and uniform geometric sums.** For
\(\ell\in\mathbb Z^d\), restrict the character
\(\chi_\ell(x)=\exp(2\pi\mathrm i\,\ell\cdot x)\) to \(H\), and let
\(w=\chi_\ell(\alpha)\). If \(w=1\), this character is 1 on the entire
integer orbit and, by continuity, on \(H\). Its integral and every orbit
average are therefore 1. If \(w\ne1\), Haar invariance gives
\[
\int_H\chi_\ell\,d\mu_H=w\int_H\chi_\ell\,d\mu_H,
\qquad\text{so}\qquad\int_H\chi_\ell\,d\mu_H=0.
\]
For every \(x\in H\) and integer \(M\ge1\), the geometric-sum identity is
\[
\frac1M\sum_{n=1}^M\chi_\ell(x+n\alpha)
=\chi_\ell(x)\frac{w(1-w^M)}{M(1-w)},\qquad
\left|\frac1M\sum_{n=1}^M\chi_\ell(x+n\alpha)\right|
\le\frac2{M|1-w|}.
\]
The bound is uniform in \(x\). Nontrivial roots of unity \(w\ne1\), which
can occur for characters of disconnected closures, are covered by this same
calculation. A nonzero ambient \(\ell\) may restrict to the trivial character;
the \(w=1\) case handles that possibility explicitly.

**35.5 Stone-Weierstrass passage to continuous functions.** Finite complex
linear combinations of the restricted characters form a unital algebra:
products add their integer indices and complex conjugation negates them.
The coordinate characters separate distinct torus points, hence separate
points of \(H\). The complex Stone-Weierstrass theorem makes this algebra
uniformly dense in \(C(H)\). Given \(f\in C(H)\) and \(\varepsilon>0\),
choose a finite character combination \(P\) with
\(\|f-P\|_\infty<\varepsilon\). Its orbit averages converge uniformly by
35.4, while both its integral error and average error relative to \(f\)
are at most \(\varepsilon\). Consequently
\[
\limsup_{M\to\infty}\sup_{x\in H}
\left|\frac1M\sum_{n=1}^M f(x+n\alpha)-\int_H f\,d\mu_H\right|
\le2\varepsilon.
\]
Letting \(\varepsilon\downarrow0\) proves uniform continuous
equidistribution on the actual group \(H\). This is the classical character
form of the Weyl criterion, here proved in the precise form needed.

**35.6 Full Haar support and every positive forward tail.** Every nonempty
relatively open \(V\subseteq H\) has positive Haar measure. Its translates
cover \(H\); a finite subcover exists by compactness. If \(\mu_H(V)=0\),
translation invariance would then give \(\mu_H(H)=0\), a contradiction.
In the compact metric space choose a continuous \(f\) with
\(0\le f\le1\), supported in \(V\), and positive on a nonempty open set.
Such a function exists by taking a sufficiently small metric ball with closure
in \(V\) and a continuous distance cutoff. Its integral \(a\) is positive:
a smaller nonempty open set has \(f\) bounded below by a positive constant.
By 35.5, for all sufficiently large \(M\), uniformly in \(x\),
\[
\frac1M\#\{1\le n\le M:x+n\alpha\in V\}
\ge\frac1M\sum_{n=1}^M f(x+n\alpha)>a/2>0.
\]
Thus the positive orbit of every \(x\in H\) meets every such \(V\), with
positive lower visit density. Starting instead at \(x+M_0\alpha\), for
any prescribed nonnegative integer \(M_0\), proves the same assertion for
every forward tail. All positive forward orbits and their tails are dense;
in particular \(H\) is also the closure of the positive orbit of 0.

**35.7 Surjective coordinates and Haar marginals.** For each \(1\le i\le d\),
\(\pi_i(H)\) is a compact, hence closed, circle subgroup containing all
integer multiples of the irrational \(\alpha_i\). It is infinite, since
two equal multiples would give a nonzero integer multiple in \(\mathbb Z\).
An infinite closed subgroup of the circle is the circle itself. To see this,
compactness supplies distinct subgroup elements arbitrarily close together;
their differences, with sign chosen, have representatives \(t>0\) tending
to 0. The subgroup contains \(0,t,\ldots,\lfloor1/t\rfloor t\), whose
circle mesh has gaps at most \(t\). Every circle point is a limit of such
subgroup elements and belongs to the closed subgroup. Thus \(\pi_i\) is onto.

For a circle translation \(t\), choose \(y\in H\) with \(\pi_i(y)=t\).
For every Borel circle set \(E\), translation by \(y\) identifies
\(\pi_i^{-1}(E)\) with \(\pi_i^{-1}(E+t)\). The pushforward
\(\nu_i=(\pi_i)_*\mu_H\) is therefore translation-invariant circle
probability, hence normalized circle length by Haar uniqueness. In particular
\(\mu_H(\pi_i^{-1}(\{t\}))=0\) for every \(t\). These are marginal
statements, not independence or ambient-dimensional volume statements.

**35.8 Null boundary and uniform consecutive-block density.** The continuous
function \(g(x)=\max_i\|x_i\|_{\mathbb T}\) has
\[
\partial_H U_Q\subseteq\{g=r\}
\subseteq\bigcup_{i=1}^d\pi_i^{-1}(\{r,-r\}).
\]
All these fibers are Haar-null by 35.7. Thus both \(\{g=r\}\) and the
relative boundary of the strict neighborhood are null. For small
\(0<\delta<\min(r,1/2-r)\), define continuous cutoffs by composing \(g\)
with the piecewise linear functions
\[
f^-_\delta=\min(1,\max(0,(r-g)/\delta)),\qquad
f^+_\delta=\min(1,\max(0,(r+\delta-g)/\delta)).
\]
They satisfy \(f^-_\delta\le\mathbf1_{U_Q}\le f^+_\delta\), and differ
from that indicator only in \(\{|g-r|\le\delta\}\). As \(\delta\downarrow0\),
continuity from above of finite measure makes the strip measure tend to 0.
The two integrals therefore tend to \(d_Q\). Applying 35.5 to the two
cutoffs, then squeezing and taking \(\delta\downarrow0\), proves
\[
\sup_{x\in H}\left|\frac1M\sum_{n=1}^M\mathbf1_{U_Q}(x+n\alpha)-d_Q\right|
\longrightarrow0.
\]
In particular, with integer \(m\ge0\),
\[
\sup_{m\ge0}\left|
\frac{\#(B_Q\cap\{m+1,\ldots,m+M\})}{M}-d_Q\right|\longrightarrow0.
\]
Taking \(m=0\) gives natural density. Taking any fixed forward tail gives
the same density. Merely observing that an orbit avoids the boundary would
not have justified the indicator passage; the Haar-null boundary is essential
to this proof.

**35.9 Strict half-open-cell lower bound.** Represent torus points uniquely
in \([0,1)^d\) and partition it into the \(Q^d\) Borel half-open cubes
\[
C_j=\prod_{i=1}^d[j_i/Q,(j_i+1)/Q),\qquad 0\le j_i<Q.
\]
The sets \(H\cap C_j\) form a disjoint exhaustive Borel partition of \(H\).
Some member \(A\) has \(\mu_H(A)\ge Q^{-d}>0\). Choose \(a\in A\).
For every \(x\in A\), the chosen representatives of \(x_i,a_i\) are in
the same half-open interval of length \(1/Q\), so
\(|x_i-a_i|<1/Q\), strictly. Circle distance is at most this real distance.
It follows that \(A-a\subseteq U_Q\). Since \(a\in H\), Haar invariance gives
\[
\boxed{d_Q\ge\mu_H(A-a)=\mu_H(A)\ge Q^{-(k-1)}>0.}
\]
No positive ambient Lebesgue measure of \(A\) is needed. Any coordinate
marginal also gives \(d_Q\le2/Q\). For \(k=2\), 35.7 gives \(H=\mathbb T\)
and \(d_Q=2/Q\). For larger \(k\), the value \((2/Q)^{k-1}\) is justified
under a separately established full-torus hypothesis; it is not inferred here.

**35.10 A proper disconnected closure is compatible with irrational coordinates.**
As an illustration outside the prime setting, let \(\beta\) be irrational
and \(\alpha=(\beta,\beta+1/2)\). The even orbit subsequence is dense in
\(\{(t,t):t\in\mathbb T\}\), since \(2\beta\) is irrational; the odd
subsequence is dense in \(\{(t,t+1/2):t\in\mathbb T\}\). The union of these
two circles is closed and is exactly \(H\). It is a proper disconnected
subgroup of \(\mathbb T^2\), although both coordinate projections are onto
and both rotation coordinates are irrational. The proof in 35.3-35.9 covers
this situation. This example makes no assertion about which closure occurs
for any particular prime-logarithm vector.

**35.11 Rotation-dependent forward syndeticity.** The relatively open
neighborhood \(U_Q\) is nonempty, since it contains 0. By 35.6 every positive
forward orbit meets it. Thus \(\{U_Q-j\alpha:j\ge1\}\) covers \(H\).
Compactness gives a finite nonempty set \(J\subseteq\mathbb Z_{\ge1}\)
whose corresponding sets still cover \(H\). Define
\(L=L(\alpha,Q)=\max J\). For every integer \(m\ge0\), some \(j\in J\)
satisfies \(m\alpha\in U_Q-j\alpha\). Hence
\[
B_Q\cap\{m+1,\ldots,m+L\}\ne\varnothing.
\]
The positive choice of \(j\) proves a forward-return statement. Consecutive
members of \(B_Q\) differ by at most \(L\). Removing finitely many indices
preserves this bound for sufficiently late blocks and preserves both natural
density and the uniform block limit: the block count changes by at most the
total number removed, independently of its starting index. This proof gives
existence of \(L\); it evaluates no numerical maximum-gap bound.

**35.12 Dirichlet's first return is a different assertion.** Place the
\(Q^d+1\) points \(j\alpha\), \(0\le j\le Q^d\), in the half-open cubes
of 35.9. Two share a cube. Subtract the smaller index from the larger to get
an integer \(q\) with
\[
1\le q\le Q^d,\qquad
\max_i\|q\alpha_i\|_{\mathbb T}<1/Q.
\]
Thus the first positive return from 0 is at most \(Q^{k-1}\). This is the
classical simultaneous Dirichlet pigeonhole argument. Applying it to a
translated block again gives a difference of two indices, which need not
belong to that block. It proves neither \(L\le Q^{k-1}\) nor the location
of the first rounded box surviving positivity or the strict original cutoff.

**35.13 Generic irrational rotations refute a uniform maximum-gap inference.**
Fix \(Q\ge3\), any integer \(R\ge1\), and \(r=1/Q\). Choose an irrational
\[
0<\beta<\min\bigl(r,(1-2r)/(R+1)\bigr).
\]
For integers \(\ell\ge0\), let
\(t_\ell=\lfloor(\ell+r)/\beta\rfloor+1\). For \(0\le j<R\),
\[
\ell+r<(t_\ell+j)\beta<\ell+r+R\beta<\ell+1-r.
\]
The first strict upper estimate follows from
\(t_\ell\beta<\ell+r+\beta\); equality there would make \(\beta\) rational.
Every one of the \(R\) consecutive positive indices
\(t_\ell,\ldots,t_\ell+R-1\) consequently avoids
\(\{n\ge1:\|n\beta\|_{\mathbb T}<r\}\). These blocks occur arbitrarily
late because \(t_\ell\to\infty\). Nevertheless 1 is a return, since
\(\beta<r\), and the one-dimensional result gives density \(2/Q\).
There are returns on either side of sufficiently late empty blocks, so
their enclosing consecutive returns differ by at least \(R+1\).
Taking \(R=Q\) disproves a generic maximum-gap bound \(Q\) in dimension one;
arbitrary \(R\) rules out any bound depending only on \(Q\) across all
irrational steps. The rotation changes with \(R\), so this is consistent
with 35.11 for each fixed rotation. It is not a counterexample for any fixed
prime tuple and does not refute a separately proved prime-specific estimate.

**35.14 Unique rounding, finite positivity discard and actual boxes.** For
every integer \(n\ge1\), each \(n\alpha_i\) is irrational, hence never a
half-integer. Its nearest integer is unique. Set
\[
m_0(n)=n,\qquad
m_i(n)=\lfloor n\alpha_i+1/2\rfloor\ (i>0),\qquad
c_i=m_i(n)h_i.
\]
As \(n\to\infty\), all \(m_i(n)\to\infty\), because all \(\alpha_i>0\).
Choose a finite \(n_0\) after which every \(m_i(n)\ge1\). For \(n\ge n_0\),
\[
b_i(n)=m_i(n)-1\in\mathbb Z_{\ge0},\qquad
C_i=\{c_i,c_i+h_i\}=\{m_i(n)h_i,(m_i(n)+1)h_i\}.
\]
These are actual logarithms of adjacent integer prime powers. In the source's
original exponent convention the box is \(b_i\in\{m_i-1,m_i\}\), and its
lower-corner integer is
\[
N_n=\prod_{i=0}^{k-1}p_i^{m_i(n)-1}.
\]
Only the finite initial indices with a nonpositive \(m_i\) are removed;
write \(B_Q^{\rm valid}=B_Q\cap[n_0,\infty)\). This retains all density
and eventual syndeticity conclusions of 35.8-35.11. No exponent enumeration
or numerical first valid index is supplied by the construction.

**35.15 Errors, minimum height, total height and relative shape.** For
\(n\in B_Q^{\rm valid}\), nearest rounding and the strict return condition give
\[
\Delta_0=0,\qquad\Delta_i=c_i-nh_0,
\qquad |\Delta_i|<h_i/Q\quad(i>0).
\]
Define separately
\[
T_n=\min_i c_i,\qquad\xi_i=c_i-T_n,\qquad A_n=\sum_i c_i,
\qquad R_n=\sum_{i=1}^{d}\Delta_i.
\]
The coordinate \(\Delta_0=0\) and the strict error bounds imply
\[
nh_0-h_{\max}/Q<T_n\le nh_0,\qquad
\min_i\xi_i=0,\quad\xi_i\ge0,\quad
\max_i\xi_i=\max_i\Delta_i-\min_i\Delta_i<2h_{\max}/Q.
\]
Summing the coordinates instead gives the exact identity and separate error
\[
A_n=knh_0+R_n,\qquad |R_n|<E_Q.
\]
Thus \(T_n\to\infty\) and \(A_n\ge kT_n\to\infty\) along the selected
indices. For fixed \(Q\) these statements give a uniform neighborhood of
zero shape; they do not claim that the shapes of every successive selected
box converge to zero. That stronger convergence belongs to a separate
approximation subsequence or to a different target, not to a varying-\(Q\)
limit silently inserted into this theorem.

**35.16 Monotone exponents, strict integer order and exact logarithmic size.**
Each floor \(m_i(n)\) is nondecreasing in \(n\), and \(m_0(n)=n\) increases
strictly. For any \(n'>n\ge n_0\), even without a return assumption,
\[
\frac{N_{n'}}{N_n}
=p_0^{n'-n}\prod_{i=1}^d p_i^{m_i(n')-m_i(n)}
\ge p_0^{n'-n}>1.
\]
Thus \(N_n\) is strictly increasing on the entire valid tail and on its
\(B_Q\) subsequence. Index counts therefore count distinct integers.
Distinct coordinates \(c_i,c_j\) cannot be exactly equal on that tail:
equality would imply \(p_i^{m_i}=p_j^{m_j}\) with positive exponents,
contrary to unique factorization. Near balance is not exact equal height.
For every selected valid index, 35.15 gives
\[
\boxed{\log N_n=A_n-S_h=knh_0-S_h+R_n,\qquad |R_n|<E_Q.}
\]
In particular the requested error \(O((\sum_{i>0}h_i)/Q)\) has absolute
implied constant 1, uniformly in these indices at the fixed parameters.

**35.17 Full squeeze proof of integer counting.** For real \(t\), put
\(F(t)=\#\{n\in B_Q^{\rm valid}:n\le t\}\), with zero count below the
valid range. The density theorem and finite discard give
\(F(t)=d_Qt+o(t)\) as real \(t\to\infty\); passing from integer to real
cutoffs changes the argument by less than 1. For \(X\to\infty\), define
\[
y_X=\frac{\log X+S_h}{kh_0},\qquad
\delta_Q=\frac{E_Q}{kh_0},\qquad
C(X)=\#\{n\in B_Q^{\rm valid}:N_n\le X\}.
\]
If \(n\le y_X-\delta_Q\), then 35.16 gives
\(\log N_n<kh_0n-S_h+E_Q\le\log X\). Conversely,
\(N_n\le X\) and \(R_n>-E_Q\) give \(n<y_X+\delta_Q\), hence
\[
F(y_X-\delta_Q)\le C(X)\le F(y_X+\delta_Q).
\]
The two real cutoffs differ from \(y_X\) by fixed constants. Since \(F\)
counts a subset of the integers, each difference from \(F(y_X)\) is
\(O(1)\), bounded by the number of integers in an interval of fixed length;
possible endpoint equalities change no conclusion. Therefore
\[
C(X)=d_Qy_X+o(y_X)
=\boxed{\frac{d_Q}{kh_0}\log X+o(\log X)}.
\]
By 35.16 this is the number of distinct constructed integers at most \(X\).
Removing any further fixed finite prefix preserves the coefficient. The
primes and \(Q\) remain fixed; no shrinking-target statement follows.

**35.18 Bounded exponent and log-size gaps, divergent additive integer gaps.**
Let \(n<n'\) be consecutive sufficiently late selected indices. By 35.11,
\(n'-n\le L(\alpha,Q)\). For \(i>0\), the elementary floor inequality
\(\lfloor x+t\rfloor-\lfloor x\rfloor\le\lceil t\rceil\), \(t\ge0\),
gives
\[
0\le m_i(n')-m_i(n)\le\lceil L\alpha_i\rceil,
\qquad 1\le m_0(n')-m_0(n)\le L.
\]
The floor inequality holds because \(x+t\le x+\lceil t\rceil\) and
integer translation commutes with the floor. From the exact size identity,
\[
0<\log N_{n'}-\log N_n<kh_0L+2E_Q.
\]
All these bounds depend on the fixed rotation and primes. In ordinary integer
size, 35.16 instead gives
\[
N_{n'}-N_n\ge(p_0-1)N_n\longrightarrow\infty.
\]
Bounded gaps in the reference exponent, in rounded exponents or in logarithmic
size do not become bounded additive gaps among ordinary integers.

**35.19 The exact three-coordinate comparison and wider domain.** For either
ordered triple \((2,3,5)\) or \((2,3,7)\), take a selected valid box from
35.14-35.15. For \(e\in\{0,1\}^3\), its endpoint corner is
\(v(e)=(c_i+e_i h_i)_{i=0}^2\), with total \(A_n+\sum_i e_i h_i\).
Distinct \(e\) have distinct totals: equality, after canceling \(A_n\)
and exponentiating, would identify two different products of distinct primes.
Define \(\mathscr W_n\) to be all finite real pairs \(M_0<M_1\) whose
closed interval \([M_0,M_1]\) contains at least two such corner totals.
Corners are actual endpoints of this box, not fractional mixtures. This
domain permits negative \(M_0\), equality of budgets with corner totals,
zero envelope radius, upper saturation \(M_1\ge A_n+S_h\), and arbitrary
finite upper-budget slack. It imposes no 5040 cutoff.

For \((M_0,M_1)\in\mathscr W_n\), set
\[
f(x)=\log(1-e^{-x})\ (x>0),\qquad C_i=\{c_i,c_i+h_i\},
\]
\[
D(M_1)=\max_{\substack{0\le y_i\le1\\\sum_i h_i y_i\le M_1-A_n}}
\sum_{i=0}^2\bigl((1-y_i)f(c_i)+y_i f(c_i+h_i)\bigr),
\]
\[
I=[M_0/3,M_1/3],\quad\mu=M_1/3,\quad
V_0=\sum_{i=0}^2\operatorname{dist}(I,C_i)^2,\quad\rho=\sqrt{V_0/6},
\]
\[
L_{\rm env}=\mu-\rho,\quad H_{\rm env}=\mu+2\rho,\qquad
\Psi=f(H_{\rm env})+2f(L_{\rm env}),\qquad G=D-\Psi.
\]
Here distance is the infimum of \(|u-v|\) over the two indicated sets.
There is no extra division by 3 in \(V_0\). The projection explicitly uses
\(\langle u,v\rangle=\sum_i u_iv_i\), the chosen Euclidean inner product
on real logarithmic coordinates. These are precisely the definitions of
30.2 and 31.2; the lower budget is not an additional LP constraint on \(y\).

**35.20 Feasibility, nonempty wider domains and positive support.** The least
corner total is \(A_n\). Two distinct admitted totals imply \(M_1>A_n\),
so \(y=0\) is feasible in 35.19. The feasible polytope is closed and bounded;
its objective is continuous on positive endpoints, so \(D\) exists as an
attained finite maximum. The wider domain itself is nonempty: the closed
interval between the largest two corner totals has positive width and
contains both of them. This does not yet check the original strict cutoff.

For an admitted corner \(v\), let \(\bar v=\sum_i v_i/3\in I\) and
\(w_i=v_i-T_n\ge0\). Then
\[
\sum_i\operatorname{dist}(I,C_i)^2\le\sum_i(v_i-\bar v)^2
=\sum_i w_i^2-3(\bar v-T_n)^2
\le6(\bar v-T_n)^2.
\]
The last step uses \(\sum_iw_i^2\le(\sum_iw_i)^2=9(\bar v-T_n)^2\),
valid also when some \(w_i=0\). It follows that
\[
0\le\rho\le\bar v-T_n\le\mu-T_n,\qquad
H_{\rm env}\ge L_{\rm env}\ge T_n>0.
\]
Thus both envelope arguments and all prime-power endpoints have positive
support. The proof includes budget endpoints at corners, negative lower
budgets, zero radius, saturated LPs, ties of optimal mixtures and any finite
upper slack; no stable greedy order or critical-node topology is assumed.

**35.21 Two scoped strict scaled margins.** The exponential series, with
its strictly positive remainder after degree four, gives
\[
e^2>1+2+2+4/3+2/3=7.
\]
Hence \(\log5<2\) and \(\log7<2\), analytically, without numerical
logarithms or an exponent search. In the \((2,3,5)\) family set \(Q=1920\)
and \(d_{235}=\mu_{H_{235}}(U_{1920})\). Equations 35.9 and 35.15 give
\[
d_{235}\ge1/1920^2,\qquad
\max_i\xi_i<2\log5/1920<1/480.
\]
Validity gives \(c_i\ge h_i\ge\log2\), thus finite \(T_n\ge\log2\).
Together with 35.19-35.20 these verify every hypothesis of the inherited
30.16 estimate. Therefore
\[
\boxed{e^{T_n}G<-1/120\quad\text{on every }\mathscr W_n
\text{ for the valid }(2,3,5),Q=1920\text{ boxes}.}
\]
For the separate \((2,3,7)\) family, set \(Q=1280\) and
\(d_{237}=\mu_{H_{237}}(U_{1280})\). The same construction gives
\[
d_{237}\ge1/1280^2,\qquad
\max_i\xi_i<2\log7/1280<1/320,\qquad T_n\ge\log2.
\]
Apply its own inherited theorem 31.17, with the same checked domain and
support, to obtain
\[
\boxed{e^{T_n}G<-1/80\quad\text{on every }\mathscr W_n
\text{ for the valid }(2,3,7),Q=1280\text{ boxes}.}
\]
Both inherited radii are closed; these constructed shapes lie strictly
inside them. All permitted endpoint and saturation cases remain included.
The second sign is not an unproved substitution into the first triple's
theorem. Neither inequality is a bound on unscaled \(G\).

**35.22 Exact strict original-domain threshold and 10080.** For either triple,
define the original-domain intersection
\[
\mathscr S_n=\{(M_0,M_1)\in\mathscr W_n:S_h+\log5040<M_0\}.
\]
Its source exponent budgets are \(M_j-S_h\); they are distinct from
\(T_n=\min c_i\). Because \(\log2\) is the unique smallest step, the
largest corner total is \(A_n+S_h\), and the second largest is
\(A_n+S_h-\log2\). Every interval containing two corners has
\(M_0\le A_n+S_h-\log2\). Thus nonemptiness of \(\mathscr S_n\) implies
\(A_n>\log2+\log5040\). Conversely, under this strict inequality the closed
slab
\[
[A_n+S_h-\log2,\ A_n+S_h]
\]
has width \(\log2>0\), two actual corner endpoints, and lower endpoint
strictly above the cutoff. This proves
\[
\boxed{\mathscr S_n\ne\varnothing\quad\Longleftrightarrow\quad
A_n>\log2+\log5040.}
\]
At equality the domain is empty. This is a threshold on the sum \(A_n\),
not on the minimum \(T_n\). It reproduces the exact 30.18/31.19 endpoint
argument to make the present application self-contained.

Equivalently \(\prod_i p_i^{m_i}>10080\), where
\(10080=2\cdot5040=2^5\cdot3^2\cdot5\cdot7\). Equality is arithmetically
impossible for \((2,3,5)\), whose product has no factor 7, and for
\((2,3,7)\), whose product has no factor 5. The continuous-domain equality
case nevertheless stays empty because the cutoff is strict. Since
\(A_n\ge3T_n\to\infty\), every sufficiently late selected box has
nonempty original domain. Discarding the finite earlier set changes neither
index density nor eventual syndeticity nor the integer counting coefficients:
\[
C_{235}(X)=\frac{d_{235}}{3\log2}\log X+o(\log X),\qquad
C_{237}(X)=\frac{d_{237}}{3\log2}\log X+o(\log X).
\]
Here the counts concern exactly the constructed valid boxes with nonempty
original domain, represented injectively by their lower-corner integers.

**35.23 Wider estimates precede cutoff intersection; unscaled gaps vanish.**
In section 34 take \(k=3\), baseline offsets \(a_i=0\) and
\(T_{\min}=\log2\). Its paired-increment theorem gives
\(|e^T(G_\xi-G_0)|\le4\epsilon\) when \(\epsilon=\max_i\xi_i\).
The budget correspondence adds \(S_\xi=\sum_i\xi_i\) to both endpoints
and preserves endpoint corners. But
\[
M_0^\xi>S_h+\log5040
\quad\Longleftrightarrow\quad
M_0^0>S_h+\log5040-S_\xi,
\]
which need not imply the old fixed cutoff. As 34.17-34.19 require, one
first applies the separate triple-specific wider-domain sign theorem, then
intersects with \(\mathscr S_n\). Transfer alone provides no baseline sign,
and a theorem restricted to the old cutoff would not suffice for all these
inverse-image slabs. The signs in 35.21 consume only 30.16 and 31.17.

There is a uniform direct estimate independent of the relative slab. Since
\(f\) is increasing and negative on \((0,\infty)\), all endpoint arguments
and both envelope arguments being at least \(T_n\) imply
\[
D,\Psi\in[3f(T_n),0],\qquad
\boxed{|G|\le-3f(T_n)=-3\log(1-e^{-T_n})\longrightarrow0.}
\]
The interval bound for \(D\) holds for every feasible mixture and therefore
for its maximum. The bound for \(\Psi\) uses its total weight 3. Their
difference is bounded by the length of that same interval, not twice its
length. This is uniform over all admitted wider-domain slabs, and hence
over the original intersections. By 35.22 there are actual original slabs
at unbounded heights, so no unscaled negative margin bounded away from zero
can hold on this family. The constants constrain \(e^{T_n}G\). Infinite
height, or \(e^{-T_n}=0\), is a limit and never an admitted parameter.

**35.24 Three density meanings.** The positive density \(d_Q\) concerns the
one-dimensional reference exponent \(n\). Let
\(\mathcal N_Q=\{N_n:n\in B_Q^{\rm valid}\}\). Its counting function is
of order \(\log X\) by 35.17 and \(d_Q>0\), so its ordinary natural
integer density is zero:
\(\#(\mathcal N_Q\cap[1,X])/X\to0\). Its logarithmic integer density is
also zero, with the usual definition
\[
\lim_{X\to\infty}\frac1{\log X}
\sum_{\substack{N\in\mathcal N_Q\\N\le X}}\frac1N=0.
\]
Indeed validity gives \(N_n\ge p_0^{n-1}\), so the sum over the entire
selected tail is bounded by the convergent geometric series
\(\sum_{n\ge n_0}p_0^{-(n-1)}\). Logarithmic growth of a counting function
does not mean positive logarithmic density among integers.

In full exponent space, among \(b\in\{0,\ldots,R\}^k\) the constructed
family has at most \(R+1\) points, since \(b_0=n-1\) determines \(n\).
Its proportion is at most \((R+1)^{1-k}\to0\) for \(k\ge2\).
These statements describe the constructed subfamily, not all boxes that
might satisfy a \(G\) inequality. Finite validity/cutoff removal does not
change any of these density conclusions.

**35.25 Fibonacci cutoffs are inherited limits, not sparse orbit sampling.**
Let \(F_j\to\infty\) be increasing Fibonacci numerical cutoffs. Substituting
this sequence of cutoffs into already established limits immediately gives
\[
\frac{\#(B_Q\cap[1,F_j])}{F_j}\longrightarrow d_Q,\qquad
\frac{\#(\mathcal N_Q\cap[1,F_j])}{\log F_j}
\longrightarrow\frac{d_Q}{kh_0}.
\]
The same holds after the finite discards. No new equidistribution theorem
is needed for these cutoff limits. Sampling only the indices \(n=F_j\)
instead asks about \(F_j\alpha\) and
\(J^{-1}\#\{j\le J:F_j\in B_Q\}\). Its convergence or equality to
\(d_Q\) is not proved here; uniform consecutive-block frequency does not
answer this different sparse-sampling question.

**35.26 Numerical-order Zeckendorf recoding preserves every finite count.**
Use the stipulated Zeckendorf bijection: Fibonacci weights \(1,2,3,5,\ldots\),
digits in \(\{0,1\}\) with no adjacent occupied weights, and unique decoding
to the original integer. Under numerical-order enumeration the first \(M\)
positive decoded integers are exactly \(1,\ldots,M\). For any membership
set, including \(B_Q\) as indices or \(\mathcal N_Q\) as integers, its
count among these codes therefore equals its numerical count for every
finite \(M\), identically. This is an immediate use of the existing
bijection, not a new proof of the Zeckendorf theorem.

A complete digit-length cutoff that corresponds to a Fibonacci numerical
interval inherits 35.25. Conditioning on a digit-prefix cylinder, changing
weights assigned to codewords, or enumerating codes in an arbitrary different
order changes the sampling operation and needs separate analysis. Bijectivity
alone does not preserve density under arbitrary reordering.

**35.27 Golden-ratio frequency, other metrics and chosen orthogonality.**
For every irrational one-dimensional step \(\beta\) and every circle
interval \(I\), 35.4-35.8 in dimension one give limiting visit frequency
equal to the circle length of \(I\); its boundary has at most two points.
Thus irrationality of the golden ratio yields no improved limiting interval
frequency. No golden-ratio extremality theorem is invoked. Approximation
quality such as \(\min_{1\le q\le M}\|q\beta\|_{\mathbb T}\), discrepancy
of finite empirical interval counts from interval length, and minimum spacing
between finitely many orbit points are distinct quantities. A comparison of
any of them requires its own hypotheses, metric and correctly attributed
extremal theorem; limiting interval frequency determines none of them.

The Euclidean inner product in 35.19 is explicitly chosen. Prime labels,
ordinary exponent coordinates and Zeckendorf digits supply neither an inner
product nor new orthogonality or a new KL-loss identity. A lattice slice,
a positive-width budget slab, a numerical-order cutoff and a digit cylinder
remain different constructions, as in the existing section 10 discussion.

**35.28 Classical attribution and exact source-access limits.** Unique prime
factorization, Haar existence/uniqueness, compactness, Stone-Weierstrass,
the character/Weyl criterion and Dirichlet pigeonholing are classical tools.
C64 attributes Haar probability and invariance to Christopher White,
*Ergodic Theory and Topological Groups*, Theorem 1.1. It attributes Haar
distribution on the closure of a homomorphism's image to Tom Meyerovitch,
*Well-distribution of polynomial maps on locally compact groups*,
arXiv:2210.01429v2, Proposition 3.2 (PDF page 8), and the compact metrizable
abelian character criterion to Lemma 5.3 (PDF page 11). For minimal recurrence
and torus return sets it cites Terence Tao's *254A Lecture 3*, Lemma 1 and
Theorem 2. The specialized restricted-group/null-boundary/half-open-cell
combination, rounded prime-box counting and scoped \(G\) applications are
the repo-derived paper deductions written out here, with no novelty or
priority claim. The finite geometric series, elementary exponential series,
floor inequalities and squeeze arguments are classical elementary steps.

The complete primary reports successful retrieval of the pinned raw Markdown
and rendered GitHub page at d79a2cd3cd3d5881dce26df9cee8266de9ae61e7,
focused checking of 30.1-30.3, 30.16-30.19, 31.1-31.2, 31.17-31.20 and relevant
section 34 statements; it expressly does not claim a whole-paper audit or
independent source byte-hash verification. Its retrieval of the Meyerovitch
PDF, screenshots of the indicated closure notation, Tao's lecture and White's
university-hosted notes is worker-reported evidence. It is not caller-independent
retrieval or retrieval performed by I22. C64 reports a supplementary Steif PDF
HTTP 403 and attempted Meyerovitch HTML HTTP 404; neither unavailable text
supports a premise. Caller EoM attempts timed out, as supplied in this brief.
No missing URL, screenshot or hash is reconstructed. I22's fresh consultation
is of this pinned local source and the explicitly supplied complete C64
response; new external reference accesses are zero, since no new premise
requires a focused lookup. These classical attributions do not independently
certify the inherited specialized \(G\) estimates.

**35.29 Primary identity and remaining mathematical obligations.** The supplied
completed actual-PRO C64 task is 72c4fe58-e7c0-4e6a-ab0f-fb5d446ecb48,
flight qgh0910-pro-near-balanced-recurrence-capacity-recovery,
caller attempt 1/retry budget 0. Its complete raw response is 25631 bytes,
SHA256 4402fa6cc3d85c184f775a34441488dbcc7c8276ffb81fca3d7bba8219ba3604.
The caller-supplied captured task display was 6/Pro. This is display evidence;
no independent invocation-specific selector observation or serving-identity
telemetry was available, and neither requested model nor pool label attests
hidden serving identity. There is no sterile-prior or model-diversity claim.
The supplied carrier history remains: C62 was terminally abstained after
navigation failure without mathematics; C63 was prepared, never dispatched,
and superseded before launch after company capacity was exhausted; C64 used
the distinct capacity-recovery flight. No C56 or other failed task is revived,
no retry budget reset, and no current review vote or live merge state read.

The fixed-prime/fixed-\(Q\) recurrence and counting arguments have no residual
mathematical premise beyond the classical tools proved or attributed above;
they do not depend on any \(G\) sign. This primary proved verdict is still
subject to independent source review. No numerical \(d_Q\) beyond its bounds
is asserted without identifying \(H\); no evaluated gap bound, first valid
box, discrepancy rate, shrinking target, arbitrary nonzero-shape density or
continuously realizable prime-lattice translation family is supplied. General
prime-data gap estimates remain distinct from the generic rotation example.
Sparse Fibonacci sampling and changed code order/weighting retain their
separate questions. Full translated/wider-domain 5040, uniform-third-prime,
density/optimizer-stability, arbitrary-fixed-prime-triple and arbitrary-shape
sign obligations remain open in their assigned scopes, including C61, C53,
C54 and C56. GH remains the user's undefined label. Neither recurrence nor
a negative difference of the supplied upper bounds is an RH theorem,
an RH-equivalent criterion or RH progress. No exhaustive literature audit,
novelty, priority, independent certificate verification or kernel freeze is
claimed; the standing continuous research goal remains active.

**35.30 Implementation, report and canonical handoff boundary.** This is the
single Codex CLI I22 implementation flight
qgh0910-i22-near-balanced-recurrence, attempt 1, retry budget 1, under the
caller-pinned consensus-rnd:sshx 1.0.0-beta.42 SKILL.md and
CODEX_WORKER_SPEC.md, with CLAUDE 5.11 and the explicit no-delegation brief.
The work target is /Users/auricstudio/trureturing-qgh-recurrence, branch
lane/math/quantized-gh-recurrence-0910, immutable BASE
d79a2cd3cd3d5881dce26df9cee8266de9ae61e7. The complete predecessor prefix is
preserved: 394297 bytes, 7571 LF, SHA256
06331627e46c9e19fbb784282b192d521cb953e4c9a34fb421f74c44c0655b9b.
Historical source, CAS, YAML and report bytes, including partial/table atoms
and terminal-LF variants, retain their original identities. This layer adds
only section 35, the [single provenance and binding report](../../reports/quantized-gh/near-balanced-recurrence-0910.md),
and the actual outputs of one canonical invocation on the finished source:
~~~text
make ingest BASE=d79a2cd3cd3d5881dce26df9cee8266de9ae61e7 SOURCE=arithmetic-boundary-quantization
~~~
The report preserves the exact C64 response as inert tilde-fenced text,
separately identifies its delimiter-only LF, maps every new numbered unit to
primary fields, and records whole-span CAS coverage, inherited 34.22 LF
extension, actual children/chains if emitted, links and whitespace diagnostics.
Byte/hash/JSON/span checks and make orchestration are structural evidence,
not theorem proof. Mathematical code execution, sampled orbits, exponent/prime
enumeration, historical certificates or tests replayed, CPU candidate
generation, GPU work and runtime-state reads/writes are all zero in this flight.
There are no tool, producer, Lean or frozen edits or broad builds/cache warmup.

The worker is repo-prior-exposed. No other worktree, live source/review target,
caller transcript, task registry, worker envelope or log/log_ref content is
an input; the explicitly supplied complete C64 response is the permitted
previous-stage mathematical input. No delegation, worker/oracle launch,
independent review panel or lifecycle/termination authority is exercised.
At this I22 handoff the changes are unstaged and not independently reviewed;
this describes this handoff, not future delivery status. Caller sealing,
public verification, independent review and ordinary gates remain required,
and final S24 delivery must follow S23 MERGED. Canonical ingestion is not
Lean absorption, independent approval, MERGED delivery or completion of the
standing goal. The report and final structured envelope expose any coverage
or whitespace failure without hand-editing canonical data or repeating ingest.

## 36. Complete fixed-width prime-box tubes: multiplicity, Haar counting and baseline boundaries

**36.1 Fixed data, complete family and theorem.** This S25/C70 appendix
implements the terminal C67 primary as PAPER_ARGUMENT / repo-derived. All
logarithms are natural. Fix an ordered list of distinct primes
\(p_0,\ldots,p_{k-1}\), an integer \(k\ge2\), and a finite real
\(0<\epsilon<\infty\). Write \(d=k-1\), \(h_i=\log p_i>0\),
\(S_h=\sum_{i=0}^d h_i\), and \(h_{\max}=\max_i h_i\). For every
\(m\in\mathbb Z_{\ge1}^k\), define
\[
c_i=m_i*h_i,\quad T(m)=\min_i c_i,\quad A(m)=\sum_i c_i,\quad
\operatorname{width}(m)=\max_i c_i-\min_i c_i,\quad
N(m)=\prod_{i=0}^d p_i^{m_i-1}.
\]
Let \(C_\epsilon(X)\) count all these tuples with
\(\operatorname{width}(m)\le\epsilon\) and \(N(m)\le X\), for real \(X>0\).
Unique factorization makes this also a count of distinct ordinary integers.
The theorem proved below is
\[
C_\epsilon(X)=\frac{\kappa_\epsilon}{k*h_0}*\log X+o(\log X),
\qquad \kappa_\epsilon>0.
\]
Here \(\kappa_\epsilon\) is the bounded multiplicity mean on the actual
orbit closure defined in 36.2 and 36.6, not a visit probability. Its ratio
\(\kappa_\epsilon/h_0\) is independent of the reference prime. Every branch
of the fixed-width family is counted; section 35's selected nearest-rounding
Bohr family is only a source of a lower bound. Every asymptotic fixes the
prime list and \(\epsilon\). The explicit higher-dimensional volume formula
is conditional on a full orbit closure; no such hypothesis enters the main
theorem. The shifted-5040 count is unconditional, while its proposed full
wider-domain \(G\) margin stays conditional on C61 throughout this appendix.

**36.2 Pairwise irrationality and the integer annihilator.** Set
\(\alpha_i=h_0/h_i\) for \(1\le i\le d\), and in
\(\mathbb T^d=(\mathbb R/\mathbb Z)^d\) let
\[
H=\overline{\{n*\alpha:n\in\mathbb Z\}},\qquad
\Lambda=\{\ell\in\mathbb Z^d:\ell\mathbin{\cdot}\alpha\in\mathbb Z\}.
\]
The closure of a subgroup is a subgroup, so \(H\) is a compact abelian group;
\(\mu_H\) denotes its normalized regular Haar probability measure. If
\(h_i/h_j=u/v\) for distinct indices and positive integers \(u,v\), then
\(p_i^v=p_j^u\), contradicting unique prime factorization. Thus every such
ratio, including each \(\alpha_i\), is irrational. This does not prove joint
rational independence of \(1,\alpha_1,\ldots,\alpha_d\).

For \(\ell\in\mathbb Z^d\), write
\(\chi_\ell(x)=\exp(2*\pi*\mathrm i*(\ell\mathbin{\cdot}x))\).
Continuity and orbit density show that \(\chi_\ell|_H=1\) exactly when
\(\ell\in\Lambda\). Its Haar integral then equals 1. Otherwise choose
\(v\in H\) with \(\chi_\ell(v)\ne1\); translating the integral multiplies
it by \(\chi_\ell(v)\) without changing it, so its integral is zero. These
character facts include finite-order characters on disconnected \(H\).

**36.3 Exact annihilator description without a full-torus assumption.** One has
\[
H=\{x\in\mathbb T^d:\chi_\ell(x)=1\text{ for all }\ell\in\Lambda\}.
\]
The forward inclusion follows from 36.2. For the converse suppose \(x\notin H\).
In a translation-invariant torus metric let \(g(y)=\operatorname{dist}(y,H)\).
This continuous function is invariant under translations by \(H\), satisfies
\(g(0)=0\), and has \(g(x)>0\). Ambient characters and their finite linear
combinations form a conjugation-closed unital algebra separating torus points.
The complex Stone-Weierstrass theorem gives a trigonometric polynomial \(P\)
with \(\|P-g\|_\infty<g(x)/3\). Average \(P(y+v)\) over \(v\in H\).
Character integration from 36.2 produces a polynomial \(Q\) using only
\(\ell\in\Lambda\); the same error bound holds because \(g(y+v)=g(y)\).
If \(x\) satisfied every annihilator character, then \(Q(x)=Q(0)\). But
\(g(x)=|g(x)-g(0)|<2*g(x)/3\) would follow, a contradiction. This establishes
the description using Haar measure and character approximation, not an
unproved joint-independence assertion.

**36.4 Rational tangent space and all finite components.** Every subgroup of
\(\mathbb Z^d\) is finitely generated: induct on \(d\), project to the first
coordinate, lift a generator of its nonzero image in \(\mathbb Z\) if needed,
and add generators for the kernel by induction. Apply this to \(\Lambda\),
put its generators in the rows of an integer matrix \(B\) with \(s\) rows,
and set \(V=\ker_{\mathbb R}B\). The empty matrix is allowed. By 36.3,
\[
H=\{x\bmod\mathbb Z^d:B*x\in\mathbb Z^s\}.
\]
Rational row reduction gives a rational basis of \(V\); clearing denominators
gives integer vectors spanning \(V\) over \(\mathbb R\). No saturation of
\(\Lambda\) is assumed. In a sufficiently small injective coordinate cube
about zero, every component of \(B*x\) has absolute value less than 1. The
local lift of \(H\) is therefore exactly \(V\) intersected with that cube.
For the quotient map \(\pi:\mathbb R^d\to\mathbb T^d\), the subgroup
\(\pi(V)\) contains a neighborhood of zero in \(H\). It is open; its other
cosets are open, so it is also closed. Compactness gives finitely many cosets.
The image \(\pi(V)\) is connected. Conversely a connected subset of \(H\)
cannot cross those disjoint open cosets. Thus \(H^0=\pi(V)\) is exactly the
identity component and those finitely many cosets are all components.

The discrete group \(V\cap\mathbb Z^d\) contains a real spanning set of
integer vectors, so it is a full lattice in \(V\). The quotient
\(V/(V\cap\mathbb Z^d)\) identifies with \(H^0\). Lebesgue measure on a
lattice fundamental domain, normalized to total mass 1, pushes forward to
Haar probability on \(H^0\). Haar measure on \(H\) assigns equal mass to
its finitely many component cosets. In every local affine chart of a component,
a hyperplane with nonzero derivative on \(V\) consequently has Haar measure
zero. This gives the measure model needed even for proper, disconnected \(H\).

**36.5 Surjective component coordinates and null seams.** The projection of
\(H\) to coordinate circle \(i\) is a closed subgroup containing all multiples
of irrational \(\alpha_i\), hence is the circle. To recall the elementary
circle fact: an infinite closed subgroup has arbitrarily small nonzero
representatives by compactness and subtraction of two nearby distinct points;
choose their signs positive. Successive multiples of such a representative
approximate every circle point, so closedness gives the whole circle.
The image of the connected compact group \(H^0\) is a connected compact circle
subgroup, hence either the trivial subgroup or the circle. If it were trivial,
the finite component decomposition in 36.4 would make the image of \(H\)
finite, a contradiction. Thus each projection of \(H^0\) is surjective;
in particular \(v\mapsto v_i\) is a nonzero linear form on \(V\).

The pushforward of \(\mu_H\) under this projection is circle Haar measure:
surjectivity lifts any circle translation to a translation of \(H\), and
Haar uniqueness applies. Every coordinate fiber is therefore Haar-null,
including the representative seam \(x_i=0\bmod1\). Component surjectivity is
stronger than the marginal statement and will also control mixed faces.

**36.6 Bounded periodic branch multiplicity.** For representatives
\(x_i\in[0,1)\) and a branch \(j\in\mathbb Z^d\), define
\[
\Delta_0=0,\qquad \Delta_i=h_i*(j_i-x_i),\qquad
w_\epsilon(x)=\#\{j:\max_{0\le i\le d}\Delta_i-
                         \min_{0\le i\le d}\Delta_i\le\epsilon\}.
\]
Because zero is among the anchored coordinates, each contributing branch has
\(-\epsilon\le\Delta_i\le\epsilon\). Thus
\(x_i-\epsilon/h_i\le j_i\le x_i+\epsilon/h_i\); an interval of that length
contains at most \(\lfloor2*\epsilon/h_i\rfloor+1\) integers. Consequently
\[
0\le w_\epsilon\le B_\epsilon,
\qquad B_\epsilon=\prod_{i=1}^d(\lfloor2*\epsilon/h_i\rfloor+1).
\]
For all representatives at once it suffices to use the finite branch set
\(-\lceil\epsilon/h_i\rceil\le j_i\le1+\lceil\epsilon/h_i\rceil\).
Changing a lift from \(x\) to \(x+z\), \(z\in\mathbb Z^d\), and reindexing
\(j\) to \(j+z\) preserves every \(\Delta_i\); hence \(w_\epsilon\) is a
well-defined periodic Borel function on the torus. Put
\[
\kappa_\epsilon=\int_H w_\epsilon\,d\mu_H,
\qquad \nu_\epsilon=\mu_H(\{x:w_\epsilon(x)>0\}).
\]
The first is a multiplicity-weighted mean; the second is a support probability.

**36.7 Exact every-branch correspondence and positivity cutoff.** For an integer
reference exponent \(n\ge1\), take \(x=\{n*\alpha\}\) and set
\[
m_0=n,\qquad m_i=\lfloor n*\alpha_i\rfloor+j_i.
\]
Then \(m_i*h_i=n*h_0+\Delta_i\). Thus contributing branches are in bijection
with all integer tuples at reference coordinate \(n\) whose width is at most
\(\epsilon\), before the remaining positivity restrictions. Conversely,
every such tuple gives the unique branch
\(j_i=m_i-\lfloor n*\alpha_i\rfloor\). Since
\(m_i*h_i\ge n*h_0-\epsilon\), every branch is a valid positive tuple once
\(n*h_0>\epsilon\), equivalently for all
\(n\ge\lfloor\epsilon/h_0\rfloor+1\). At equality the lower estimate alone
does not certify positivity; the finitely many earlier indices are handled
by imposing \(m_i\ge1\) exactly. There are at most \(B_\epsilon\) branches
per such index, so the invalid initial tuples form a finite set. No nearest
rounding, single-branch choice or presumed monotonic order of boxes is used.

**36.8 All possible threshold faces and every derivative.** Away from seams,
a fixed branch is admitted exactly when
\(\Delta_i-\Delta_j\le\epsilon\) for every ordered pair
\(i,j\in\{0,\ldots,d\}\). Its indicator is locally constant unless a
threshold equality occurs. Both signs are covered by the two orders; ordinary
ties away from the threshold do not change admission. For a tangent vector
\(v\in V\), every distinct-index derivative is explicitly
\[
\begin{aligned}
d(\Delta_i-\Delta_j)(v)&=-h_i*v_i+h_j*v_j &&(i,j>0,\ i\ne j),\\
d(\Delta_i-\Delta_0)(v)&=-h_i*v_i &&(i>0),\\
d(\Delta_0-\Delta_j)(v)&= h_j*v_j &&(j>0).
\end{aligned}
\]
The last two forms are nonzero on \(V\) by 36.5. If a mixed form vanished
identically, evaluate it on the integer spanning set of \(V\) in 36.4.
For each such integer vector, \(h_i*v_i=h_j*v_j\) and irrational
\(h_i/h_j\) force \(v_i=v_j=0\): one zero forces the other, and two nonzero
integers would give a rational ratio. Both coordinate projections would
then vanish on the real span \(V\), contradicting 36.5. So every mixed
form is nonzero as well.

For **every diagonal pair** \(i=j\), including each \(i>0\) and \(i=0\),
\(\Delta_i-\Delta_i=0\) identically. Its threshold equality is
\(0=\epsilon\), impossible for \(\epsilon>0\). The diagonal derivative is
zero but there is no diagonal face to measure. Tied extrema at width
\(\epsilon\) are already in the union of the distinct-index faces above.

**36.9 Null boundary at every positive width, including closed width.** In each
component chart, each possible distinct-index threshold face from 36.8 is an
affine hyperplane with nonzero derivative on \(V\), hence is Haar-null by
36.4. Components have countable chart covers, and there are finitely many
components, branch indices and ordered pair types. Their union is null.
Add the null seams from 36.5. This contains every discontinuity of
\(w_\epsilon|_H\), proving Haar-almost-everywhere continuity for **each**
fixed finite \(\epsilon>0\). No exceptional width, connectedness assumption
or full-torus hypothesis is discarded.

Let \(w_{<\epsilon}\) use strict width. Its branch indicators differ from
the closed indicators only where a distinct-index difference equals
\(\epsilon\); diagonal equalities are impossible by 36.8. Therefore
\(\int_H w_{<\epsilon}\,d\mu_H=\kappa_\epsilon\), and their support
probabilities agree as well. Chart seams have no effect on this conclusion.
This is a Haar-measure argument on all of \(H\), not an inference from a
possibly exceptional orbit's finite or zero frequency of boundary hits.

**36.10 The actual strict-versus-closed correction is finite.** If a positive
integer tuple has width exactly \(\epsilon>0\), choose its ordered distinct
maximum/minimum pair \(i,j\). The equation
\(m_i*h_i-m_j*h_j=\epsilon\) has at most one integer solution pair. Indeed
subtracting two solutions gives
\((m_i-m'_i)*h_i=(m_j-m'_j)*h_j\); irrationality in 36.2 forces both
differences to vanish. Once this pair is fixed, every other coordinate
\(m_l*h_l\) lies in the fixed bounded closed interval
\([m_j*h_j,m_i*h_i]\), which contains only finitely many positive multiples
of \(h_l\). There are finitely many ordered maximum/minimum pairs. Thus the
actual boundary set \(\mathcal E_\epsilon\) is finite. Exactly,
\[
C_\epsilon(X)-C_{<\epsilon}(X)
=\sum_{m\in\mathcal E_\epsilon}\mathbf1_{\{N(m)\le X\}}\ge0.
\]
This correction is bounded in \(X\) and eventually constant. Multiple extreme
pairs count the tuple only once in \(\mathcal E_\epsilon\). It supplements
the Haar-null proof in 36.9 and preserves every equality at the integer-size
cutoff. Width zero is classified separately in 36.25.

**36.11 Uniform distribution for continuous observables on the actual closure.**
For a restricted character let \(t=\chi_\ell(\alpha)\). If \(t=1\), the
character is identically 1 on \(H\). Otherwise its integral is zero and the
finite geometric sum gives, for every \(x\in H\),
\[
\left|\frac1M*\sum_{n=1}^M\chi_\ell(x+n*\alpha)\right|
\le\frac{2}{M*|1-t|}\longrightarrow0.
\]
This is uniform in \(x\); a nontrivial finite-order \(t\) causes no exception.
Restricted characters form a conjugation-closed unital algebra separating
points of \(H\). Given continuous \(f\) and \(\eta>0\), Stone-Weierstrass
gives a finite character polynomial \(P\) with \(\|f-P\|_\infty<\eta\).
The difference between the orbit mean and Haar integral of \(f\) is bounded
by \(2*\eta\) plus the corresponding difference for \(P\), uniformly in the
starting point. The latter tends to zero by the displayed estimate. Letting
\(\eta\) decrease proves uniform convergence to \(\int_H f\,d\mu_H\).
This proves the needed specialized classical distribution statement on proper
or disconnected \(H\), with no assumed joint rational independence.

**36.12 Uniform weighted and support-frequency means.** If a Borel set
\(E\subset H\) has null boundary, continuous functions sandwich its indicator
with arbitrarily small integral gap. Explicitly, on compact metric \(H\) use
\(l_\delta(x)=\min(1,\operatorname{dist}(x,H\setminus E^\circ)/\delta)\)
and \(u_\delta(x)=\max(0,1-\operatorname{dist}(x,\overline E)/\delta)\),
with the empty/full-set cases treated by constant functions. They satisfy
\(l_\delta\le\mathbf1_E\le u_\delta\), and as \(\delta\downarrow0\) their
integrals tend to those of \(E^\circ\) and \(\overline E\). The limits agree
because the boundary is null. Uniform convergence for continuous functions
in 36.11, followed by squeezing, proves uniform convergence for \(\mathbf1_E\).

For \(1\le t\le B_\epsilon\), set \(E_t=\{w_\epsilon\ge t\}\). At a
continuity point the integer-valued \(w_\epsilon\) is locally constant, so
\(\partial E_t\) is contained in its null discontinuity set from 36.9.
Apply the indicator result to each \(E_t\) and the finite identity
\(w_\epsilon=\sum_{t=1}^{B_\epsilon}\mathbf1_{E_t}\). Consequently
\[
\sup_{a\in\mathbb Z_{\ge0}}
\left|\frac1M*\sum_{n=a+1}^{a+M}w_\epsilon(n*\alpha)-\kappa_\epsilon\right|
\longrightarrow0,
\]
and replacing \(w_\epsilon\) by \(\mathbf1_{\{w_\epsilon>0\}}\) gives the
same assertion with limit \(\nu_\epsilon\). This follows by taking starting
point \(x=a*\alpha\) in the stronger all-starting-point statement.

**36.13 Positive Bohr inclusion and an explicit Haar lower bound.** Choose any
integer \(Q\ge3\) with \(2*h_{\max}/Q<\epsilon\), for example
\(Q=\max(3,\lfloor2*h_{\max}/\epsilon\rfloor+1)\), and put
\[
U_Q=\{x\in H:\max_{1\le i\le d}\|x_i\|_{\mathbb R/\mathbb Z}<1/Q\}.
\]
In each coordinate of \(U_Q\) choose the unique nearest integer branch:
\(j_i=0\) near zero and \(j_i=1\) near one in \([0,1)\). Its errors satisfy
\(|\Delta_i|<h_i/Q\), with \(\Delta_0=0\), so the full range is strictly
less than \(2*h_{\max}/Q<\epsilon\). Thus \(U_Q\subset\{w_\epsilon>0\}\).
Partition \([0,1)^d\) into \(Q^d\) half-open cubes of side \(1/Q\) and
intersect with \(H\). Some cell \(E\) has measure at least \(Q^{-d}\).
Choose \(a\in E\); differences of representatives in the same half-open
coordinate interval have absolute value strictly less than \(1/Q\).
Therefore \(E-a\subset U_Q\). Translation invariance proves
\[
\kappa_\epsilon\ge\nu_\epsilon\ge\mu_H(U_Q)\ge Q^{-d}>0.
\]
This strict half-open-cell argument works on disconnected and proper \(H\).
The Bohr family proves positivity; it does not replace the complete family
or turn its weighted mean into this lower bound.

**36.14 Multiplicity, visit density and eventual syndeticity.** The pointwise
inequalities \(\mathbf1_{\{w>0\}}\le w\le B_\epsilon*
\mathbf1_{\{w>0\}}\), together with 36.12-36.13, yield
\[
0<\nu_\epsilon\le\kappa_\epsilon\le B_\epsilon,
\qquad \kappa_\epsilon/B_\epsilon\le\nu_\epsilon
\le\min(\kappa_\epsilon,1).
\]
By 36.7, the natural density of reference indices admitting an actual box is
\(\nu_\epsilon\), whereas their average number of boxes is \(\kappa_\epsilon\).
The finite initial positivity correction changes neither mean. These numbers
can differ: 36.19 proves that for \(k=2\) and \(\epsilon=h_1\),
\(\kappa_\epsilon=2\) but \(\nu_\epsilon=1\).

Uniform support-frequency convergence supplies an integer \(L\) such that
every block of \(L\) consecutive indices with nonnegative starting index has
support average greater than \(\nu_\epsilon/2\). Every such block contains a
positive multiplicity. Beyond the finite positivity cutoff in 36.7, this is
syndetic occurrence of actual boxes. The argument establishes a finite gap
bound depending on this rotation and window; it evaluates no numerical bound.
It is neither a Dirichlet first-return estimate nor a maximal-gap bound
depending only on \(Q\). Section 35's distinction between those questions
remains in force.

**36.15 All-branch index count and exact logarithmic size.** Let \(F(t)\) count
all valid width-at-most-\(\epsilon\) tuples with
\(1\le m_0\le\lfloor t\rfloor\), and set \(F(t)=0\) for \(t<1\). The
exact correspondence and finite positivity discard in 36.7 give
\[
F(t)=\sum_{1\le n\le\lfloor t\rfloor}w_\epsilon(n*\alpha)-J(t)
=\kappa_\epsilon*t+o(t),
\]
where \(J(t)\) is the nonnegative count of invalid initial branches. It is
bounded independently of \(t\) and eventually constant. There are at most
\(B_\epsilon\) valid tuples at every reference index. For **each** such
tuple with \(m_0=n\),
\[
\log N(m)=k*n*h_0-S_h+R(m),\qquad
R(m)=\sum_{i=1}^d\Delta_i,\qquad |R(m)|\le d*\epsilon.
\]
This follows by summing \(c_i=n*h_0+\Delta_i\) and subtracting \(S_h\).
It applies to every branch, including branches with non-nearest integers.
Neither \(R(m)\) nor \(N(m)\) is assumed to have a common monotone ordering
as the reference index changes.

**36.16 Closed cutoff squeeze and reference-invariant coefficient.** Set
\(y_X=(\log X+S_h)/(k*h_0)\) and
\(\delta=d*\epsilon/(k*h_0)\). The exact size bound in 36.15 gives
\[
F(y_X-\delta)\le C_\epsilon(X)\le F(y_X+\delta).
\]
For the left inequality, \(n\le y_X-\delta\) forces \(\log N\le\log X\).
For the right one, \(\log N\le\log X\) and \(R\ge-d*\epsilon\) force
\(n\le y_X+\delta\). Both arguments allow equality. A change of real index
cutoff by fixed \(\delta\) crosses at most \(\lceil\delta\rceil+1\) integers,
each of multiplicity at most \(B_\epsilon\). Hence
\[
C_\epsilon(X)=F(y_X)+O(1)
=\frac{\kappa_\epsilon}{k*h_0}*\log X+o(\log X).
\]
Floor endpoints, positivity discards and multiple branches are all included.
If \(N(m)=N(m')\), unique factorization gives \(m_i-1=m'_i-1\) for every
labeled prime, so no distinct tuples are identified in this count.

Repeat this proved theorem with \(p_r\) as reference and write the resulting
mean as \(\kappa_\epsilon^{(r)}\). The intrinsic counting function is unchanged
by the coordinate permutation. Its limit divided by \(\log X\) therefore gives
\[
\frac{\kappa_\epsilon^{(r)}}{k*h_r}
=\frac{\kappa_\epsilon^{(0)}}{k*h_0}.
\]
It is \(\kappa_\epsilon^{(r)}/h_r\) that is invariant; raw multiplicity means
and support probabilities need not be. This fixed-parameter proof supplies no
discrepancy rate, evaluated annihilator or uniform shrinking-window error.

**36.17 Conditional full-torus unfolding.** By 36.3,
\(H=\mathbb T^d\) exactly when \(\Lambda=\{0\}\), equivalently when
\(1,\alpha_1,\ldots,\alpha_d\) are rationally independent. Pairwise
logarithmic irrationality does not establish this for \(d\ge2\). Define
\[
\mathcal D_\epsilon=\{\Delta\in\mathbb R^d:
\max(0,\Delta_1,\ldots,\Delta_d)-\min(0,\Delta_1,\ldots,\Delta_d)
\le\epsilon\}.
\]
Under the **full-torus hypothesis**, integrate the branch sum of 36.6 over
\([0,1)^d\). For branch \(j\), put \(y_i=j_i-x_i\) and
\(\Delta_i=h_i*y_i\). The \(y\) cells \(\prod_i(j_i-1,j_i]\) tile
\(\mathbb R^d\) up to null endpoints. The absolute Jacobian from \(y\) to
\(\Delta\) is \(\prod_{i=1}^d h_i\). Summing the integrals yields
\[
\kappa_\epsilon=\frac{\operatorname{vol}_d(\mathcal D_\epsilon)}
                         {\prod_{i=1}^d h_i}.
\]
The domain is bounded, and only the finite relevant branches can meet it
over the fundamental cube. Thus this unfolds every branch for any fixed
finite width; it assumes neither a small window nor multiplicity at most one.

**36.18 Exact anchored-range volume.** Partition \(\mathcal D_\epsilon\)
according to which of its \(k\) anchored coordinates
\(0,\Delta_1,\ldots,\Delta_d\) is minimal. Equal minima lie in finitely
many Euclidean hyperplanes and contribute zero volume. If zero is minimal,
all \(\Delta_i\in[0,\epsilon]\), a region of volume \(\epsilon^d\).
If \(\Delta_j\) is minimal, put \(\Delta_j=-t\), \(0\le t\le\epsilon\).
Each remaining \(\Delta_i\) ranges independently in
\([-t,\epsilon-t]\); the anchored zero belongs to that interval. Integrating
\(\epsilon^{d-1}\) over \(t\) gives another \(\epsilon^d\). This also
works for \(d=1\), with empty product equal to 1. There are \(d\) such
regions in addition to the minimum-at-zero region. Consequently
\[
\operatorname{vol}_d(\mathcal D_\epsilon)
=(d+1)*\epsilon^d=k*\epsilon^{k-1}.
\]
Together with 36.16-36.17 this gives, **conditionally on \(H=\mathbb T^d\)**,
\[
\kappa_\epsilon=\frac{k*\epsilon^{k-1}}{\prod_{i=1}^d h_i},
\qquad C_\epsilon(X)=\frac{\epsilon^{k-1}}{\prod_{i=0}^d h_i}*\log X
+o(\log X).
\]
The geometric volume is unconditional as a Euclidean calculation; its use
as the Haar integral for a prime list of dimension at least three requires
the stated orbit-closure hypothesis.

**36.19 Unconditional two-prime coefficient and its scoped comparison.** For
\(k=2\), the irrational rotation \(\alpha_1=h_0/h_1\) has the whole circle
as its closure, by the circle argument in 36.5. Thus 36.18 applies
unconditionally and gives, for every finite \(\epsilon>0\),
\[
\kappa_\epsilon=2*\epsilon/h_1,\qquad
C_\epsilon(X)=\frac{\epsilon}{\log p_0*\log p_1}*\log X+o(\log X).
\]
Here the width condition is just \(|h_1*(j_1-x_1)|\le\epsilon\).
There is some branch exactly when the circle distance to the nearest integer
is at most \(\epsilon/h_1\). Circle Haar measure therefore gives
\(\nu_\epsilon=\min(1,2*\epsilon/h_1)\), including closed endpoints, whose
measure is zero. This also proves the multiplicity/probability example in
36.14. At a fixed logarithmic width, a smaller product
\(\log p_0*\log p_1\) has a larger leading absolute counting coefficient;
fixing one prime and increasing the other decreases it. This is an asymptotic
coefficient comparison, not finite-\(X\) set inclusion, a \(G\)-sign comparison
or positive ordinary integer density. No unconditional blanket comparison
for \(k\ge3\) follows from a formula requiring a full torus.

**36.20 All fixed-prime smooth numbers: simplex estimate with endpoint control.**
Let \(S_P(X)\) count all integers \(\prod_i p_i^{b_i}\le X\) with
\(b\in\mathbb Z_{\ge0}^k\). For \(L=\log X\ge0\), define
\(\Omega(L)=\{t\in\mathbb R_{\ge0}^k:\sum_i h_i*t_i\le L\}\).
Scaling by \(u_i=h_i*t_i\) gives
\(\operatorname{vol}\Omega(L)=L^k/(k!*\prod_i h_i)\).
The elementary simplex formula follows by induction: in dimension one its
length is \(L\); integrating the \((k-1)\)-dimensional volume over the last
coordinate gives \(\int_0^L(L-u)^{k-1}/(k-1)!\,du=L^k/k!\).

For each eligible integer \(b\), take the half-open cube \(b+[0,1)^k\).
These cubes are disjoint and their union has volume \(S_P(X)\), since unique
factorization is injective. The union contains \(\Omega(L)\): if
\(t\in\Omega(L)\), then \(\lfloor t\rfloor\) is eligible and its cube
contains \(t\), including integral coordinates. The union is contained in
\(\Omega(L+S_h)\), because \(\sum_i h_i*t_i<\sum_i h_i*b_i+S_h\)
inside each cube. Hence
\[
\frac{L^k}{k!*\prod_i h_i}\le S_P(X)
\le\frac{(L+S_h)^k}{k!*\prod_i h_i},
\qquad
S_P(X)=\frac{(\log X)^k}{k!*\prod_i h_i}+O((\log X)^{k-1}).
\]
The inequalities remain valid at \(L=0\); the error estimate is as
\(L\to\infty\) with the prime list fixed.

**36.21 Exact asymptotic smooth-family ratio and integer densities.** Divide
36.16 by 36.20, whose leading coefficient is positive. The exact asymptotic
ratio is
\[
\frac{C_\epsilon(X)}{S_P(X)}\sim
\kappa_\epsilon*(k-1)!*\left(\prod_{i=1}^d h_i\right)*
(\log X)^{1-k}\longrightarrow0.
\]
Under \(H=\mathbb T^d\) this simplifies to
\(k!*\epsilon^{k-1}*(\log X)^{1-k}\); for \(k=2\) the simplification
is unconditional and equals \(2*\epsilon/\log X\). Thus the leading
proportion within a two-prime smooth family is independent of its prime
labels even though its absolute coefficient in 36.19 depends on them.

The bound \(C_\epsilon(X)=O(1+\log X)\) gives natural integer density zero.
For the set of its distinct integers, partial summation gives
\[
\sum_{\substack{N\text{ in the tube}\\N\le X}}\frac1N
=\frac{C_\epsilon(X)}X+\int_1^X\frac{C_\epsilon(t)}{t^2}\,dt.
\]
The integral is bounded as \(X\to\infty\), because
\(\int_1^\infty(1+\log t)/t^2\,dt<\infty\). Consequently the total
reciprocal sum converges, and its quotient by \(\log X\) tends to zero:
logarithmic density is also zero. A counting function proportional to
\(\log X\) is not positive logarithmic density. These facts do not conflict
with positive support or weighted frequency in the reference exponent.

**36.22 Full exponent-lattice density.** In the cube
\(0\le b_i\le R\) with \(b_i=m_i-1\) and integer \(R\ge0\), there are
only \(R+1\) possible reference indices and at most \(B_\epsilon\) tube
tuples per index, by 36.6-36.7. The tube therefore contains at most
\((R+1)*B_\epsilon\) of the \((R+1)^k\) tuples. Their proportion tends
to zero for \(k\ge2\). This density in full exponent cubes, the smooth-number
ratio in 36.21, ordinary and logarithmic integer density, support density
\(\nu_\epsilon\), and multiplicity mean \(\kappa_\epsilon\) have different
reference measures. A positive-width family fills a window on its actual
compact orbit closure with positive occurrence, while remaining sparse in
each of those larger arithmetic domains.

**36.23 Integer baselines and the exact finite nonnegative correction.** Fix
\(r_i\in\mathbb Z_{\ge0}\), put \(a_i=r_i*h_i\), and
\(K=\prod_i p_i^{r_i}\). Let \(C_{a,\epsilon}(X)\) count all \(m_i\ge1\)
with \(\min_i(c_i-a_i)\ge0\), translated width at most \(\epsilon\), and
\(N(m)\le X\). Set \(q_i=m_i-r_i\). The precise positivity conditions are
\(q_i\ge0\) for all \(i\), and \(q_i\ge1\) whenever \(r_i=0\).
If every \(q_i\ge1\), the map \(q\mapsto m=q+r\) bijects the unshifted
tube with this interior part and
\(N(m)=K*N(q)\). Its count is exactly \(C_\epsilon(X/K)\).

If some \(q_i=0\), translated minimum is zero, so every coordinate satisfies
\(0\le q_j*h_j\le\epsilon\). Let \(\mathcal B_{a,\epsilon}\) be exactly
these integer vectors satisfying the stated positivity restrictions and
having at least one zero. It is finite, with size at most
\(\prod_j(\lfloor\epsilon/h_j\rfloor+1)\). Define
\[
E_{a,\epsilon}(X)=\sum_{q\in\mathcal B_{a,\epsilon}}
 \mathbf1_{\{N(q+r)\le X\}}.
\]
Then, with no asymptotic qualification,
\[
C_{a,\epsilon}(X)=C_\epsilon(X/K)+E_{a,\epsilon}(X).
\]
The correction is nonnegative, uniformly bounded in \(X\), and eventually
constant. It retains all nonnegative translated-boundary vectors allowed by
\(m\ge1\); it is not an unspecified signed error. These definitions and
the exact identity also make sense at \(\epsilon=0\).

**36.24 Shifted coefficient, unbounded translated heights and coset limitation.**
For \(\epsilon>0\), 36.23 and \(\log(X/K)=\log X-\log K\) give the same
positive leading coefficient \(\kappa_\epsilon/(k*h_0)\) for the shifted
family. Its ratio to \(S_P(X)\) has exactly the leading factor in 36.21;
ordinary and logarithmic densities are zero. In a full exponent cube its
count remains \(O(R)\): for each reference translated integer \(q_0\), the
same length-\(2*\epsilon/h_i\) branch bound applies, and the boundary set is
finite. Put \(\tau=\min_i(c_i-a_i)=\min_i q_i*h_i\). For any fixed finite
\(U\), tuples with \(\tau\le U\) have \(q_i*h_i\le U+\epsilon\), so
are finite in number. The positive logarithmic asymptotic therefore forces
infinitely many tuples at unbounded translated height, not merely repeats
of boundary tuples. At positive threshold width the strict/closed correction
is finite too: apply the two-solution subtraction proof of 36.10 to the
integer coordinates \(q_i\), whose nonnegative domain only restricts choices.

Integer baselines are essential to the unchanged coefficient argument.
For arbitrary real offsets, using reference integer \(m_0=n\) would put
the rotation in the coset \(\theta+H\), where
\(\theta_i=(a_i-a_0)/h_i\). Indeed the translated coordinate difference is
\(h_i*(m_i-n*\alpha_i-\theta_i)\). Here, with integer baselines,
\(\theta_i=r_i-r_0*\alpha_i\), hence \(\theta\bmod\mathbb Z^d
=-r_0*\alpha\in H\). The exact integer bijection of 36.23 is stronger
than a coset argument. No equal-coefficient or positivity assertion for
arbitrary real-offset cosets is being made.

**36.25 Complete zero-width classification.** At unshifted width zero,
\(m_0*h_0=m_1*h_1\) with both integers positive would contradict 36.2.
Therefore \(C_0(X)=0\) for every \(X>0\). At shifted width zero under 36.23,
all \(q_i*h_i\) equal a common \(\tau\ge0\). If \(\tau>0\), all \(q_i\)
are positive integers and the same irrationality contradiction applies.
If \(\tau=0\), every \(q_i=0\), so \(m=r\). This is valid exactly when
every \(r_i\ge1\). Consequently
\[
C_{a,0}(X)=
\begin{cases}
\mathbf1_{\{X\ge\prod_i p_i^{r_i-1}\}},&\text{if every }r_i\ge1,\\
0,&\text{if some }r_i=0.
\end{cases}
\]
Thus a shifted zero-width family has at most its height-zero baseline. The
positive-width theorem is stated for each fixed \(\epsilon>0\); it does not
assert a uniform asymptotic as \(\epsilon\downarrow0\) or interchange that
limit with \(X\to\infty\).

**36.26 Actual 5040 arithmetic and the exact small-width edge.** Take
\(p=(2,3,5,7)\), \(r=(5,3,2,2)\), and
\(a=(5*\log2,3*\log3,2*\log5,2*\log7)\).
The ordinary prime exponents of the baseline integer are \(r-\mathbf1
=(4,2,1,1)\). The explicit arithmetic is
\[
5040=2^4*3^2*5*7,
\qquad K=2^5*3^3*5^2*7^2=1058400=5040*(2*3*5*7).
\]
Thus \(N(r)=5040\), whereas the interior scaling factor is \(K=1058400\).
Also \(a=(\log32,\log27,\log25,\log49)\),
\(\min_i a_i=\log25\), and \(\sum_i a_i=\log1058400\).
The zero-width count is exactly \(C_{a,0}(X)=\mathbf1_{\{X\ge5040\}}\).

For \(0\le\epsilon<\log2\), a boundary tuple in 36.23 with some \(q_i=0\)
must have all \(q_j=0\), since any positive \(q_j\) gives
\(q_j*h_j\ge\log2>\epsilon\). All \(r_i\) are positive, so this single
boundary tuple is allowed. Therefore for every \(X>0\),
\[
C_{a,\epsilon}(X)=C_\epsilon(X/1058400)+\mathbf1_{\{X\ge5040\}}
\qquad(0\le\epsilon<\log2).
\]
In particular this covers radius \(1/500\). At \(\epsilon=\log2\), the
additional boundary vector \(q=(1,0,0,0)\) is valid and yields
\(N(q+r)=2*5040=10080\); the baseline-only correction must not be extended
to that endpoint. Every fixed positive width has the previously proved
positive logarithmic coefficient. This attainable-tube result does not make
positive-height exact common translation attainable on the prime lattice:
such translation would require equal positive integer multiples of distinct
prime logarithms, excluded in 36.25.

**36.27 General-dimensional box, LP and envelope definitions.** For the actual
positive coordinates \(c_i=m_i*h_i\), use row sets
\(\mathcal C_i=\{c_i,c_i+h_i\}\), \(T=\min_i c_i>0\),
\(A=\sum_i c_i\), and \(f(x)=\log(1-\exp(-x))\) on \(x>0\).
For finite real \(M_0<M_1\), put
\[
I=[M_0/k,M_1/k],\quad \mu=M_1/k,\quad
\delta_i=\operatorname{dist}(I,\mathcal C_i),\quad V_0=\sum_i\delta_i^2,
\]
\[
\rho=\sqrt{V_0/(k*(k-1))},\quad L_{\rm env}=\mu-\rho,\quad
U_{\rm env}=\mu+(k-1)*\rho,\quad r_{\rm cap}=M_1-A.
\]
The distance is the infimum of absolute differences, and \(V_0\) has no
additional division by \(k\). With the full fractional feasible polytope,
\[
\mathcal P(r_{\rm cap})=\{y\in[0,1]^k:\sum_i h_i*y_i\le r_{\rm cap}\},
\]
\[
D(M_1)=\max_{y\in\mathcal P(r_{\rm cap})}
\sum_i\big((1-y_i)*f(c_i)+y_i*f(c_i+h_i)\big),
\]
\[
\Psi=f(U_{\rm env})+(k-1)*f(L_{\rm env}),\qquad G=D-\Psi.
\]
The lower budget enters \(I\), not another constraint on \(y\).
These are the existing comparison definitions of sections 27, 30, 31 and 34.
The stipulated inner product is ordinary Euclidean,
\(\langle u,v\rangle=\sum_i u_i*v_i\), with its norm; prime labels and
encodings do not supply orthogonality. Support and feasibility are checked
below before using \(f(L_{\rm env})\) or any sign input.

**36.28 Wider two-corner domain and all LP endpoint cases.** The wider domain
consists of every finite \(M_0<M_1\) whose closed budget interval contains
at least two actual endpoint-corner totals
\(A+\sum_i e_i*h_i\), \(e\in\{0,1\}^k\). These are distinct: equality
of two totals exponentiates to equality of prime products, forcing \(e=e'\).
Actual corners are endpoint choices, not fractional mixtures. The domain
permits negative lower budgets, corner equality at either endpoint, saturation
\(M_1\ge A+S_h\), and arbitrary finite upper slack.

Two distinct corners imply \(M_1>A\), hence \(r_{\rm cap}>0\). More
generally, if \(r_{\rm cap}<0\), the polytope is empty and this appendix
assigns it no finite maximum or \(G\) sign. At \(r_{\rm cap}=0\), it consists
only of \(y=0\) and \(D=\sum_i f(c_i)\); an admitted corner can only be
the lower corner, so the two-corner sign hypotheses fail. At
\(0<r_{\rm cap}<S_h\), it is nonempty and compact, its continuous objective
attains a maximum, and every maximizer uses full capacity. To prove the last
claim, all gains \(f(c_i+h_i)-f(c_i)\) are strictly positive; any feasible
vector with slack and some \(y_i<1\) can be increased slightly to improve it.
At \(r_{\rm cap}=S_h\) or \(r_{\rm cap}>S_h\), the unique maximizing
vector is \(\mathbf1\), and \(D=\sum_i f(c_i+h_i)\); extra capacity leaves
this value unchanged. Possible ties of gain-per-cost ratios or nonunique
interior maximizers need no greedy order for any argument here. Envelope
values may still change with the budgets in the saturated regime.

Closed corner inclusions and distance-branch switches are retained throughout.
Zero-width budget slabs \(M_0=M_1\) are excluded from the stated sign domain;
with distinct prime corner totals they cannot contain two corners. A one-corner
or zero-variance support statement does not enlarge a two-corner sign theorem.

**36.29 Positive envelope support, including ties and zero radius.** Suppose
at least one actual corner \(v\) lies in the closed budget slab, and let
\(\bar v=\sum_i v_i/k\). Then \(\bar v\in I\), \(v_i\in\mathcal C_i\),
and \(u_i=v_i-T\ge0\). Thus
\[
\delta_i\le|v_i-\bar v|,\qquad
V_0\le\sum_i(v_i-\bar v)^2
=\sum_i u_i^2-k*(\bar v-T)^2
\le k*(k-1)*(\bar v-T)^2.
\]
The last inequality uses \(\sum_i u_i^2\le(\sum_i u_i)^2
=k^2*(\bar v-T)^2\), since all cross-products are nonnegative.
Consequently \(\rho\le\bar v-T\le\mu-T\), whence
\(U_{\rm env}\ge L_{\rm env}\ge T>0\). This proves the support directly,
including endpoints, ties, branch changes, zero distance and \(\rho=0\),
where \(\Psi=k*f(\mu)\). It also covers one-corner slabs and degenerate
mean intervals when support alone is considered; their \(G\) signs are not
supplied by the two-corner results. With no corner, this proof asserts no
positive envelope support. The same calculation applies to the continuous
positive-coordinate baseline and shifted grids used below.

**36.30 Exact budget inverse image and strict cutoff buffers.** Fix steps
\(h_i>0\) and a positive baseline box \(c_i^0\). Translate independently by
\(\xi_i\ge0\) with \(\min_i\xi_i=0\), and set
\(S_\xi=\sum_i\xi_i\), \(c_i^\xi=c_i^0+\xi_i\),
\(A_\xi=A_0+S_\xi\). Target budgets \(M_j^\xi\) correspond exactly to
baseline budgets \(M_j^0=M_j^\xi-S_\xi\), for \(j=0,1\). For each corner,
\[
M_0^\xi\le A_\xi+\sum_i e_i*h_i\le M_1^\xi
\quad\Longleftrightarrow\quad
M_0^0\le A_0+\sum_i e_i*h_i\le M_1^0.
\]
The bijection preserves each endpoint equality, the width, corner count and
residual fractional capacity \(M_1^\xi-A_\xi=M_1^0-A_0\), including zero
capacity, saturation and slack. It therefore identifies the full feasible
polytopes, not just an assumed optimal face.

For a fixed cutoff \(B_{\rm cut}\), however, the exact inverse image is
\[
M_0^\xi>B_{\rm cut}\quad\Longleftrightarrow\quad
M_0^0>B_{\rm cut}-S_\xi.
\]
A baseline result restricted to \(M_0^0>B_{\rm cut}\) covers exactly the
target subset \(M_0^\xi>B_{\rm cut}+S_\xi\), with its other hypotheses.
If \(0\le\xi_i\le\epsilon\), then \(S_\xi\le(k-1)*\epsilon\).
A sufficient uniform target buffer is the **strict** inequality
\(M_0^\xi>B_{\rm cut}+(k-1)*\epsilon\); alternatively a baseline theorem
on \(M_0^0>B_{\rm cut}-(k-1)*\epsilon\) covers the full target cutoff
domain. Weak buffer equality can give \(M_0^0=B_{\rm cut}\) when
\(S_\xi=(k-1)*\epsilon\), outside the strict baseline domain. Only a
theorem on the entire wider domain permits unrestricted transfer followed
by intersection with the original strict cutoff, as already proved in 34.17.

**36.31 Every 235 tube box inherits its supplied whole-domain sign.** Fix
\(p=(2,3,5)\) and \(0<\epsilon\le1/480\). Every tuple of the full tube
has \(T=\min_i m_i*h_i\ge\log2\) and
\(\xi_i=c_i-T\ge0\), \(\min_i\xi_i=0\),
\(\max_i\xi_i=\operatorname{width}(m)\le\epsilon\). The separately supplied
paper estimate 30.16 states
\(\exp(T)*G<-1/120\) for **every** finite \(T\ge\log2\), closed shape
radius \(\max_i\xi_i\le1/480\), and finite positive-width two-corner slab
in its wider domain. The definitions, feasibility and positive support in
36.27-36.29 match that input exactly. It follows that every such slab in
every counted tube box satisfies
\[
\exp(T)*G<-1/120.
\]
This includes all multiplicity branches, closed tube-width equality, the
closed radius endpoint, corner inclusions at the two budget endpoints,
saturation and arbitrary finite upper slack. The strict inequality at the
radius endpoint is part of 30.16's supplied theorem. No finite certificate
is rerun and no sign for boxes outside these hypotheses is inferred.

**36.32 Every 237 tube box inherits its separate whole-domain sign.** Fix
\(p=(2,3,7)\) and \(0<\epsilon\le1/320\). Again each full-tube tuple has
\(T=\min_i m_i*h_i\ge\log2\) and \(c_i=T+\xi_i\) with
\(0\le\xi_i\le\epsilon\) and \(\min_i\xi_i=0\). The **separate**
supplied paper theorem 31.17 proves \(\exp(T)*G<-1/80\) for every finite
\(T\ge\log2\), closed shape radius \(1/320\), and every positive-width
two-corner slab of its wider domain. Thus every such slab in every counted
237 tube box obeys
\[
\exp(T)*G<-1/80.
\]
The same closed endpoints, saturation and slack cases are included by that
theorem, with support checked in 36.29. This is not substitution of a new
prime into the 235 theorem. The primary's and this appendix's use of 30.16
and 31.17 consumes their given whole-domain paper estimates; it is not an
independent revalidation of their finite-node certificates.

**36.33 Strict SUM cutoff, equality and exact finite exclusions.** For a fixed
distinct-prime box put \(h_* =\min_i h_i\). Its largest and second-largest
corner totals are \(A+S_h\) and \(A+S_h-h_*\): lowering the top corner
by a nonempty subset subtracts at least \(h_*\), attained by a minimum
step. A slab with two corners has lower endpoint at most the second-largest
total. Therefore a positive-width two-corner slab with
\(S_h+\log5040<M_0<M_1\) exists **if and only if**
\[
A>h_*+\log5040.
\]
Necessity follows from \(S_h+\log5040<M_0\le A+S_h-h_*\).
For sufficiency, the closed slab \([A+S_h-h_*,A+S_h]\) has positive width,
two endpoint corners and lower endpoint strictly above the cutoff. Equality
\(A=h_*+\log5040\) gives an empty original domain despite closed corner
inclusion. This is a condition on the **sum** \(A\), not on \(T\).

For either triple 235 or 237, \(h_*=\log2\). Let
\(\mathcal F_{P,\epsilon}=\{m\ge1:\operatorname{width}(m)\le\epsilon,
A(m)\le\log2+\log5040\}\). This is finite: each positive coordinate
is at most the displayed bound, so each integer exponent is bounded.
The exact number of excluded boxes up to \(X\) is
\(\sum_{m\in\mathcal F_{P,\epsilon}}\mathbf1_{\{N(m)\le X\}}\);
its eventual value is \(\#\mathcal F_{P,\epsilon}\), not an evaluated
enumeration. Subtract precisely this finite count from \(C_\epsilon(X)\).
At the respective radii in 36.31-36.32 the remaining boxes all have nonempty
original domain and the stated sign for every admitted original slab. Their
count remains
\((\kappa_\epsilon/(3*\log2))*\log X+o(\log X)\), using the corresponding
actual orbit closure. This does not count all possible negative boxes outside
the chosen tube.

**36.34 Recorded-radius occurrence bounds and vanishing unscaled gaps.** The
positive exponential series gives
\(\exp(2)>1+2+2+4/3+2/3=7\), so \(\log5<2\) and \(\log7<2\).
At \(\epsilon=1/480\) for 235, choose \(Q=1920\); then
\(2*\log5/1920<1/480\), and 36.13 gives
\(\kappa_\epsilon\ge\nu_\epsilon\ge1920^{-2}\).
At \(\epsilon=1/320\) for 237, \(Q=1280\) similarly gives
\(\kappa_\epsilon\ge\nu_\epsilon\ge1280^{-2}\).
These lower bounds on full-family occurrence are not substituted for its
actual multiplicity mean or leading coefficient. Smaller positive widths
use an appropriate larger \(Q\) as in 36.13.

For any admitted box, all row endpoints and envelope arguments are at least
\(T\), by 36.29. Since \(f\) is increasing and negative,
\(D,\Psi\in[k*f(T),0]\) and \(|G|\le-k*f(T)\), uniformly over its
admitted slabs, including the upper slack regime. In a fixed-width unshifted
tube, \(T\le U\) forces \(c_i\le U+\epsilon\), leaving only finitely many
tuples. Thus \(T\to\infty\) outside finite subsets, and
\(-k*f(T)\to0\). For the two triples, original-domain nonemptiness also
holds outside the finite set in 36.33. Their infinite families therefore
cannot carry an unscaled negative margin bounded away from zero over all
boxes and slabs. The supplied strictly negative margins are **scaled**.
For an integer-baseline tube, \(T\ge\min_i a_i+\tau\) and 36.24 likewise
implies vanishing of this absolute bound at unbounded translated height,
without supplying any missing \(G\) sign.

**36.35 The 5040 transfer remains conditional on C61's wider-domain premise.**
Use exactly the baseline in 36.26. For a tuple in its shifted tube set
\[
\tau=\min_i(c_i-a_i)\ge0,\qquad \xi_i=c_i-a_i-\tau,
\qquad c_i=a_i+\tau+\xi_i.
\]
Then \(\min_i\xi_i=0\) and \(0\le\xi_i\le\epsilon\). The common
translation \(\tau\) is distinct from actual lower height
\(T(m)=\min_i c_i\): indeed
\(\tau+\log25\le T(m)\le\tau+\log25+\epsilon\).
At the baseline \(\tau=0\) but \(T=\log25\). Also
\(A=\log1058400+4*\tau+S_\xi\) and \(S_h=\log(2*3*5*7)\).

The supplied general-dimensional transfer 34.20 gives, on corresponding
wider two-corner slabs, the unconditional loss estimate
\[
|\exp(\tau)*(G_\xi-G_0)|\le\epsilon/8.
\]
Its constant is \((k-1)/(\exp(\min a)-1)=3/(25-1)=1/8\), for finite
\(\tau\ge0\). **If C61 establishes**
\(\exp(\tau)*G_0<-1/2000\) for every such finite height and every finite
positive-width two-corner slab of \(c_i^0=a_i+\tau\) on the entire wider
domain, then and only under that premise the transfer yields
\[
\exp(\tau)*G_\xi<-1/2000+\epsilon/8\le-1/4000
\qquad(0\le\epsilon\le1/500).
\]
Strictness survives at the closed radius, since the baseline inequality is
strict. This conditional consequence applies to every shifted-tube branch,
including its height-zero baseline and finite boundary corrections. The
counting theorem for that family was proved unconditionally in 36.23-36.26;
counting and transfer do not prove the C61 premise. Section 32's fixed-box
cutoff certificate and section 33's density ordering do not supply it.

**36.36 5040 cutoff nonemptiness and the remaining sign boundary.** Here the
fixed original cutoff is
\(B_{\rm cut}=S_h+\log5040=\log1058400\). The exact budget inverse image
for \(S_\xi=\sum_i\xi_i\) is 36.30:
\(M_0^\xi>B_{\rm cut}\) corresponds to
\(M_0^0>B_{\rm cut}-S_\xi\). A baseline sign theorem only above
\(B_{\rm cut}\) would cover just
\(M_0^\xi>B_{\rm cut}+S_\xi\), not the entire target original domain.
Only the wider-domain premise explicitly retained in 36.35 allows the
conditional transferred sign to be intersected afterward with the original
cutoff. No same-cutoff equivalence is assumed.

Every shifted-5040 tuple satisfies
\(A\ge\sum_i a_i=\log1058400>\log2+\log5040\), since
\(1058400=5040*(2*3*5*7)>2*5040\). With \(h_*=\log2\), the top-two-corner
proof of 36.33 makes its original domain nonempty, including the baseline.
There are therefore zero exclusions from this shifted family for original
domain nonemptiness. This statement and its positive-width counting are
unconditional. Its proposed \(1/4000\) scaled all-slab margin remains
conditional on C61, as in 36.35. No full C61 result is supplied, consumed or
inferred; historical C45/C49/C51 names in earlier papers do not revive their
failed carriers or alter the current open obligation.

**36.37 Fibonacci cutoffs, encoding and distinct geometric domains.** Every
established ordinary cutoff limit persists along increasing Fibonacci
cutoffs \(F_j\to\infty\), simply because a convergent function or sequence
has the same limit on a subsequence. Thus
\(C_\epsilon(F_j)/\log F_j\to\kappa_\epsilon/(k*h_0)\), and weighted
reference-index averages over all \(1\le n\le F_j\) tend to
\(\kappa_\epsilon\). Shifted-family limits behave the same way. None of
these statements determines the sparsely sampled orbit \(F_j*\alpha\), or
membership frequency among the isolated indices \(n=F_j\).

Numerical-order Zeckendorf recoding leaves the underlying integers unchanged,
so membership counts at **every** numerical cutoff are exactly preserved;
complete Fibonacci numerical intervals inherit the proved limits. Digit
cylinders, codeword weighting and nonnumerical enumerations ask different
sampling questions. No golden-ratio extremality, improved density, full-torus
distribution or new orthogonality follows from recoding. A superiority claim
would need its own precisely attributed theorem and metric. The stipulated
Euclidean inner product in 36.27 remains a choice. A positive-width tube,
the zero-width equal-coordinate locus, a real budget slab and a digit cylinder
are distinct sets; their measures, densities and geometries cannot be exchanged.

**36.38 Classical inputs, specialized paper boundaries and actual access limits.**
Existence and uniqueness of normalized regular Haar measure, the complex
Stone-Weierstrass theorem, unique prime factorization and elementary integer
linear algebra are classical inputs. The classical closed-subgroup framework
was attributed by C67 to the real Lie-group theorem recalled in Helge
Glöckner's *Non-Lie subgroups in Lie groups over local fields of positive
characteristic*. The needed torus-specific annihilator, rational tangent,
finite-component and Haar-chart conclusions are proved in 36.2-36.5.
C67 attributes the distribution context to Tom Meyerovitch,
*Well-distribution of Polynomial maps on locally compact groups*,
arXiv:2210.01429v2, Proposition 3.2 and Lemma 5.3. The stated homomorphism
result uses the **closure** of the image. The required specialized uniform
character and discontinuous-observable arguments are proved in 36.11-36.12.
The complete-family multiplicity, boundary, counting, volume, baseline and
application arguments are repo-derived paper deductions, not novelty claims.
The scoped sign inputs 30.16 and 31.17 and conditional transfer input 34.20
are inherited repo-derived paper results, not classical \(G\)-sign theorems
or Lean/kernel admissions.

All following access facts are **C67-worker-reported**, not I24 or caller
independent retrieval. C67 reports retrieving Meyerovitch's v2 PDF and
examining printed pages 8 and 11 with screenshots, retrieving Glöckner's
arXiv abstract, and seeing only a lecture listing on a Raghuram course page.
The listing was not treated as a proof source. A Tao author-site Smith-normal-
form search and an attempted MIT Etingof lecture PDF returned Internal Error;
neither supports a premise. C67 reports opening both supplied project-source
addresses at immutable d79a2cd3cd3d5881dce26df9cee8266de9ae61e7 and focused
checks of sections 30, 31 and 34, not a whole-volume audit, byte-hash check,
checkout inspection, review-status inquiry or merge-status check. Missing
URLs, hashes and screenshot/selector evidence are not invented. Raw citation
fragments such as arXiv+1 and GitHub+1 remain untouched in the inert payload.
I24 consulted the supplied raw proof and this local pinned predecessor's
relevant statements, with zero new external accesses and zero certificate
replays; these checks do not independently recertify earlier signs.

**36.39 Primary identity, unconditional settlement and remaining obligations.**
The supplied terminal actual-PRO C67 task is
4abf944a-5964-4f3c-8fda-45ffeb1d77fc, flight
qgh0910-pro-full-near-balanced-tube-counting, caller attempt 1/retry budget 0.
Its exact raw response has 39985 bytes and 119 LF bytes, SHA256
b882817054914d14c1bf13e1fa48bc5087534c5c8b6a04704ace04a0c44b38a9,
and no terminal LF. The supplied task-observed 6/Pro label is display evidence,
not hidden serving telemetry. C67 itself had no independent invocation-specific
selector observation or serving-identity evidence. Configured/requested labels
do not supply it; no model-diversity or sterile-prior claim is made. C67 used
the complete C64 response as previous-stage mathematical context, not as an
independent review vote. Its raw log_ref remains opaque and is never opened.

The fixed-width full-family theorem, null faces, finite strict/closed correction,
reference-invariant coefficient, two-prime specialization, smooth-family ratio,
integer-baseline translation and zero-width classification have the full
paper proofs above. No unresolved premise for those unconditional statements
is concealed. Particular elementary or numerical coefficients for \(k\ge3\)
may require additional information about \(H\); no procedure deciding all
reciprocal-logarithm relations, discrepancy rate, shrinking-width estimate or
uniform comparison over changing prime lists is supplied. C53, C54, C56 and
C61 keep their separate broader scopes. In particular 36.35-36.36 retain the
missing 5040 wider-domain baseline margin as conditional; no general-prime or
arbitrary-shape \(G\) sign is proved. GH remains the user's undefined label.
Counting actual boxes and comparing these upper bounds produce no new RH
equivalence, generalized-GH definition, RH theorem or RH progress. There is
no novelty, priority, exhaustive literature audit, independent-review verdict,
Lean/kernel-frozen or MERGED claim. The standing research goal remains active.

**36.40 Implementation, report and canonical handoff.** This is the sole Codex
CLI I24 implementation flight qgh0910-i24-full-tube-counting, attempt 1/retry
budget 1, under consensus-rnd:sshx 1.0.0-beta.42 SKILL.md and
CODEX_WORKER_SPEC.md, with CLAUDE 5.11 and the explicit no-delegation override.
Work target: /Users/auricstudio/trureturing-qgh-full-tube; branch:
lane/math/quantized-gh-full-tube-0910; immutable BASE and starting HEAD:
e3c946d63039999549b4bf47f33d255854456560. Every one of the predecessor's
432403 source bytes and 8304 LF bytes is preserved, SHA256
09702761d0d445ab798d54d6a1d26394394aa330e219400617ea46373871dc71.
All historical CAS/YAML/report bytes, partial/table atoms and terminal-LF
variants retain their original identities. This layer adds section 36,
the [single full-family proof and provenance report](../../reports/quantized-gh/full-near-balanced-tube-counting-0910.md),
and actual canonical output from exactly one invocation on the finished source:
~~~text
make ingest BASE=e3c946d63039999549b4bf47f33d255854456560 SOURCE=arithmetic-boundary-quantization
~~~
The report links back to this source, embeds the entire exact raw C67 response
as inert tilde-fenced text with its delimiter-only LF separately accounted,
maps every primary field to complete numbered proof units, and records current
whole-CAS/YAML spans including the inherited 35.30 LF extension. Actual emitted
children/chains, concatenation evidence, missing bytes and whitespace outcomes
are reported as observed, never reconstructed by manual canonical edits.

This worker is repo-prior-exposed and exercises no delegation, oracle launch,
independent-review or lifecycle authority. Other worktrees/live targets, caller
transcripts, task registries, worker envelopes, peer results and logs/log_ref
referents are excluded; the explicitly supplied C67 response is the permitted
previous-stage primary exception. New mathematical programs, sampled orbits,
symbolic computation, exponent/prime/candidate enumeration, CPU candidate
generation, historical certificate/test/ingest/pilot/fixed-xi replay, GPU/runtime
access, broad builds, Lean/cache warmup, tool/frozen edits and Git/PR mutation
are zero. Structural byte/span/JSON/link checks and the one canonical make
orchestration are not mathematical computation or independent proof validation.
The caller-reported donor_behind_base 7 with matching cache pin records
unmerged predecessors, not a request to inspect a donor or rebuild Lean.

At this I24 handoff the changes are unstaged and not independently reviewed;
this describes the handoff, not later status. Caller sealing, public byte
verification, independent review and ordinary canonical PR/CI gates remain
required. Final S25 delivery must follow S24 MERGED. Ingestion is not Lean
absorption, independent approval, MERGED delivery or completion of the standing
goal. No second ingest or manual canonical repair is authorized here.

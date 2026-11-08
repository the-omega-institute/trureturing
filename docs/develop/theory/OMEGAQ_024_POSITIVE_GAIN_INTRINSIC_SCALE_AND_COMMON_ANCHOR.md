# ΩQ-024：正向增益、内生标尺与共同锚

> 理论参考输入：本稿为用户提供的研究正文，包含普通数学证明，未作本候选的 Lean/kernel 认证。原图以文内文字和公式呈现。

QUANTUM ORIGINS / $\Omega Q$-024

只需增大\
不必规定倍数

正向增益、内生标尺与共同锚闭合

**本轮唯一候选的改动。** 将上一轮的精确等式 $p(2u)=2p(u)>0$ 削弱为

$$\boxed{\exists u:\qquad 0<p(u)<p(u+u).}$$

其余五组关系保留。由同一二元乘法，读数比 $d=p(2u)/p(u)>1$ 与探针无关，内生指数 $\alpha=\log_2d$。 本文证明原可读商为四元数，而原读出准确为

$$p(x)=|\theta([x])|^\alpha,\qquad \alpha>0.$$

长度 $\ell=p^{1/\alpha}$、二次型 $q=\ell^2$ 与复二维量子几何内生恢复。 原 $p$ 保留，不能把它直接改称范数或把 $p^2$ 直接改称 Born 权重。

**模型类的实质变化。** 本轮完整模型类允许全部正幂；上一轮对应 $\alpha=1$。 六个命名条件仍为六个。规范几何不变，原始读数的数值限制严格变弱。

2026 年 11 月 9 日（新加坡时间）

|              |                                             |
|:-------------|:--------------------------------------------|
| 研究分支     | `the-omega-institute/trureturing / dev`     |
| 主要固定快照 | `242a5734ea66a228dbf09acad2a72249e2b84c4d`  |
| 提交时间     | 2026-11-09 00:03:22（Asia/Singapore）       |
| 主要检索范围 | 1364 份理论文件；4 新增、5 修改的真增量     |
| 形式         | 定义、定理、证明、反例与逐区域输入账本      |
| 证明状态     | 普通数学工作稿；未宣称已有 Lean kernel 认证 |

## 摘要

本稿延续第23轮，在同一实向量背景、同一二元乘法、同一原非负读出中， 继续减少必须预先规定的数值关系。精确翻倍标定被一次严格正向自合成增益替代。 乘性先抽出共用标量字符 $w$；$w(2)>1$ 内生确定 $\alpha>0$， 幂变换 $\ell=p^{1/\alpha}$ 精确满足已定标条件。 本稿完整重证该定标引理的全部关键链： 有限局部界、精确零核商、有理尺度、有理完成、新连续实作用、 欧氏二元平面、非交换中心对原实轴的锁定，以及同对响应的内生四维投影。 由此取得原读出的完整正幂分类，既没有预设连续性、内积或有限维， 也没有丢掉原读数或把辅助完成中的新元冒充原对象。

反向检验显示，严格增大的方向不可只改为“不相等”。 在原实数域上延拓一个2-adic绝对值，并对非交换自由多项式取系数Gauss读出， 可以同时满足其余五组条件，却在翻倍时缩小，且保留无限维。 恒等增益、纯存在指示、局部合成失控和八元数盲方向分别定位不同缺口。 这些反例保留准确量词域，不把局部反例扩大为整个项目候选的反例。

共同锚的有限Gram拼接给出另一个精确结论： 在一个秩为 $r$ 的正定锚中，单个新标签没有剩余方向， 再要求每一对新标签连同同一个锚的块为正， 就能锁定整个有限关系表，并且表示维数仍为 $r$。 所需最大联合检查规模为 $r+2$； 只检查 $r+1$ 个标签并不足够，等相关矩阵给出显式反例。 因此三维表示中的一致性证明可能同时涉及五个标签， 标签数、逻辑量词数、相位纤维维数和物理空间维数不能混为一项。

最新仓库新增的中央平方窗口定理已从原P2/PB、已付Jordan及JC接口 证明同一个旧面积响应的窗口双线性，并由两根方向及其自身响应得到闭合三轴。 同稿的四维Clifford窗口表明，任意更大窗口的面积输出不必返回原窗口。 新增移位铅笔进一步支付一类成对单位偏移；这些结果保留各自原域， 尚不能删除本轮原乘法的实双线性输入。

有限量子理论在规范二次型上展开，事件、联合、完整参考过程与实际钟流另列接口。 观察者以内部记录系统表示；Gram秩、纯化秩和固定未来效果闭包决定何时扩张、何时停止。 Gödel、Lawvere及丢番图可定义性分别按其输入条件处理。 本稿既不从几何描述推出必然无限增维，也不从有限表示推出一般问题具有可计算停止界。

## 目录

- [1　固定来源、真实增量与证明地位](#section-1)
- [2　唯一候选与三种读数的输入账本](#section-2)
- [3　只输入一次自合成增长，内生读出幂指数](#section-3)
- [4　辅助定理：已齐次读出的范数恢复](#section-4)
- [5　辅助定理续：乘性迫使二元平面成为欧氏平面](#section-5)
- [6　定标引理的完整重证：从一次等式恢复原实轴](#section-6)
- [7　同一对比较的三元闭合及四元数分类](#section-7)
- [8　反向检查：增长方向、非离散读出与有限合成预算](#section-8)
- [9　其余反向删除：在一次幂子类中保留原反例](#section-9)
- [10　同一合读结构的几何完成：方向、复幅度与正读出](#section-10)
- [11　由规范几何到概率平方：原读数与事件质量的接口](#section-11)
- [12　线、面积、相位与钟：同一几何的准确分工](#section-12)
- [13　态的三元相位：第三个方向保留了哪一份关系](#section-13)
- [14　存在、面积与最小内部表示](#section-14)
- [15　有限量子理论的完整数学完成及实际接口](#section-15)
- [16　从局部球到最小完整表示：何时扩张，何时停止](#section-16)
- [17　共同锚：有限关系怎样锁成同一个整体](#section-17)
- [18　把控制器和过程也放回关系中：相干拼接的全部自由度](#section-18)
- [19　固定点、有限三维提升与完整内部时间](#section-19)
- [20　内部表示、对角边界与全局余弦的算术表达力](#section-20)
- [21　有限关系的三种闭合：预测、实现与有效停止](#section-21)
- [22　项目新进展：共同面积表与自己生成的三轴](#section-22)
- [23　与现有研究的准确比较](#section-23)
- [24　完整闭合链、输入计数与白话](#section-24)

<a id="section-1"></a>

## 1　固定来源、真实增量与证明地位

本轮固定项目的 `dev` 分支，主提交完整标识为

$$\texttt{242a5734ea66a228dbf09acad2a72249e2b84c4d}.$$

提交时间为 2026 年 11 月 9 日 00:03:22， 一次主分支观察时间为 00:06:51，均为新加坡时间。 直接前驱是第 23 轮最终固定提交

$$\texttt{69a777d001b184cfce81bed62bad140fb93706d2}.$$

完整理论树现有 **1364 份文件、163977870 字节**； 全部文件按固定 Git blob 逐份核对，错误数为零。 前驱为 1360 份、163740251 字节， 本次净增 237619 字节：四份新增、五份修改、无删除。 五份修改均为原正文后纯追加，九份变化合计新增 4621 行。 这里的覆盖指来源固定、全树检索和真实增量阅读， 不表示已经证明或形式化认证全仓数学。 [\[1\]](#ref-repo)

| 来源 | 本次真实规模 | 核读到的新增范围 |
|:---|:---|:---|
| 中央响应平方与径向一致 | $2369\to2792$ 行 | 第53–67节：中央平方的带权原模块、标量平方窗口的旧响应双线性， 自身三轴闭合及四维不闭合反例。 |
| 移位单位铅笔与非中央参考一致 | 新增217行 | 同一完整原候选下，有限奇周期支付两个配对单位移位； 不推广为任意首槽单位平移。 |
| 原多项式零响应与 Cayley 原域边界 | $712\to952$ 行 | 第8–11节：全部原通勤演员的有限运输分量， 以及原独立分块端点的不可达性。 |
| FIB原子边界几何附录V | $3046\to3172$ 行 | 第230节：已有角坐标的分离数字池构造； 全部有限时序与可数输出记录的精确同律及其恒正运动。 |
| 原能量纤维几何 | $2124\to2555$ 行 | 第16–17节：保留支撑掩码的第一类叶编译、 完成信息代数不变及有限逆的生成容差。 |
| 原有限能量取得 | $2088\to2570$ 行 | 第15–16节：有限标量与导数供应者、 原词误差、同一成功事件和完整有限资源账。 |
| OTF-007观察纤维与最小补全 | 新增1275行 | 观察映射类型、最小补全、有限未来读出闭包、 量子与内部记录的条件桥接、单点 Gram 补全。 |
| 丢番图编码与有效读出 | 新增848行 | 高度分离、有限关系电路、有界与无界见证、 收缩率之外的读出间隙；强算术结论保留条件接口。 |
| UPPM-RG 002关系编译与停止边界 | 新增579行 | 明确隔离 $\mathsf H_{\mathbb Z/\mathbb Q}$； 区分有限门编译、有界复杂性与通用有理求解的条件性障碍。 |

九份真实新增正文均已阅读全文核查。 其中中央、铅笔、多项式、能量与 FIB 的关键结论在项目模块中处理； OTF-007 与两份丢番图稿按各自前提核查， 不把文件新增等同于数学首创或独立确认。 [\[2\]](#ref-radial24), [\[3\]](#ref-pencil24), [\[4\]](#ref-poly24), [\[5\]](#ref-fib24), [\[6\]](#ref-energyfiber24), [\[7\]](#ref-finiteenergy24), [\[8\]](#ref-otf724), [\[9\]](#ref-dio24), [\[10\]](#ref-uppmrg224)

**继承与本轮推进分开。**

V49 幂律与平方标定、R5-007 最小后继闭合、OTF-005、 未来响应充分性及动态未来商等关联文稿， 在本次主快照中均与前驱 blob 相同。 重新检索或引用它们不算本轮项目增量。 V49 的未归一权重有界、乘性与有限相干标定是相关前例， 与本轮原代数读出 $p$ 的单探针增长条件并非同一套前提。 [\[11\]](#ref-v49q24)（第13节）

**数学地位。**

本稿的核心候选是一次前提回溯：原读出满足一个严格自合成增长关系， 经同一乘性及有限合成界恢复幂律，并由内生指数给 $\ell$。 本稿提供普通数学证明，不宣称新候选已有 Lean/kernel 认证。 项目中的 JC 表示、完整 PB、原 $\Gamma$ 几何、解析源、 有限参考与实际仪器等仍按来源计账。 特别地，项目局部 $D$ 的双线性不供应本稿原乘法 $m$ 的全域双线性， 数学记录同律不供应实际制备、在线记忆或物理时间。

### 1.1　唯一末检：独立固定的支持计数增量

主快照及上述统计保持不变。唯一末检于 2026 年 11 月 9 日 00:28:59（新加坡时间）固定提交

$$\texttt{e5f31a9c7a1c4154423d2f2ba8ecf80368bb2ac9},$$

其提交时间为 00:21:55。末检理论树仍为1364份， 总计164000701字节，逐blob核对零错误。 相对主快照仅支持关联续卷一份纯追加： $3883\to4438$行，增加555行、22831字节；第44–47节已阅读全文。 中央响应、移位铅笔及本稿量子核心相关来源没有再次变化。

来源定理46.2的准确范围是：任意整数 $L\ge4$，令 $K=4$、$n=L+3$； 对任意原正递增整数位置 $s_1<\cdots<s_n$，取 $c_i=s_i+4$、$W=\sum_i c_i$。 在原假设21.1的全部执行图中，每条输入同时满足查询数不超过$n$、 字母费用不超过$W$且计算阈值四时，

$$\boxed{4L-\max(0,L-6)\le m_{\rm exec}(c,4)\le4L.}$$

全部安装状态、自适应顺序及付费认证查询与重复保持原定义， 没有添加 read-once 或全局无环前提。 $L\ge7$ 时下界为 $3L+6$；未断言下界可达或全族最小值等于 $4L$。 第47节将剩余长轴链的共同补偿准确隔离为尚未证明的式SI.302， 不能把这一未证步骤当作新公理已被内生消去。[\[12\]](#ref-support24end)（第44–47节）

<a id="section-2"></a>

## 2　唯一候选与三种读数的输入账本

### 2.1　原签名与定义

使用通常实数、集合、函数及经典逻辑；证明中的实复分析与赋值延拓属于明示数学基础。 给定实向量空间 $\mathcal A$、二元运算 $m:\mathcal A^2\to\mathcal A$ 及有限函数 $p:\mathcal A\to[0,\infty)$。 记 $xy=m(x,y)$。定义

$$N=p^{-1}(0),\quad k_{a,b}=ab-ba,\quad L_x(c)=xc, \quad T_{a,b}c=(ab-ba)c+a(bc)-b(ac).$$

这时还没有定义 $p$ 为范数，没有要求原乘法结合，没有指定维数、完备性或相位。

### 2.2　输入区域：六个命名关系组

$$
\begin{aligned}
\mathsf B_1:\;&m\text{ 对原实数作用双线性};\\
\mathsf{LB}:\;&\exists M<\infty\ \forall x,y,\quad
p(x),p(y)\le1\Longrightarrow p(x+y)\le M;\\
\mathsf G:\;&\exists u,\quad 0<p(u)<p(u+u);\\
\mathsf N:\;&\forall x,y,\quad p(xy)=p(x)p(y);\\
\mathsf U:\;&\exists\varepsilon\ \forall x,\quad
p(\varepsilon x-x)+p(x\varepsilon-x)=0;\\
\mathsf F:\;&\exists a,b\ \forall c,\quad
p(T_{a,b}c)=0\Longrightarrow p(c)=0.
\end{aligned}
$$

标定探针、单位代表和忠实比较对可以不同。 全部加法与乘法均是原运算；$2u=u+u$。

**本轮相对上一轮仅改一个条件。**

$$\exists u:p(2u)=2p(u)>0 \quad\Longrightarrow\quad \exists u:0<p(u)<p(2u).$$

前者蕴含后者，反向不成立，且完整模型类也严格扩大。 其余五组不改。$\mathsf G$ 已包含非零性，不另重复计数。 条件组可以拆分或合并；六组不等于已经证明六条独立最小公理。

### 2.3　输出区域：保留原读出，内生取得规范几何

在证明以后，对任何 $p(u)>0$ 的探针定义

$$d=\frac{p(2u)}{p(u)}>1,\qquad \alpha=\frac{\log d}{\log2},\qquad \ell(x)=p(x)^{1/\alpha},\qquad q(x)=\ell(x)^2.$$

其中 $d,\alpha$ 与所选非零探针无关，零处按 $0^\beta=0$（$\beta>0$）定义。 输出是存在保原乘法的实代数同构 $\theta:\mathcal A/N\to\mathbb H$，使

$$\boxed{ p(x)=|\theta([x])|^\alpha,\quad \ell(x)=|\theta([x])|,\quad q(x)=p(x)^{2/\alpha}. }$$

因而

$$p(tx)=|t|^\alpha p(x),\qquad \ell(tx)=|t|\ell(x),\qquad \ell(x+y)\le\ell(x)+\ell(y),$$

$$q(x+y)+q(x-y)=2q(x)+2q(y),\qquad B(x,y)=\tfrac14(q(x+y)-q(x-y)).$$

同对比较给

$$T=2L_kP_H,\quad \ker T=H^\perp=0,\qquad J=\frac{T}{2\ell(k)},\quad J^2=-I,$$

$$(\mathcal A/N,J,h)\cong\mathbb C^2,\qquad h(x,y)=B(x,y)+iB(Jx,y),\qquad S^1\longrightarrow S^3\longrightarrow S^2.$$

| 名称 | 准确定义 | 允许的结论 |
|:---|:---|:---|
| 原存在读出 | $p$ | 非负、乘性、$\alpha$次齐次；不自动是范数或概率。 |
| 规范长度 | $\ell=p^{1/\alpha}$ | 半范数、内积长度；商上为四元数模。 |
| 规范二次型 | $q=p^{2/\alpha}$ | 平行四边形、正交加和；量子幅度平方的几何载体。 |
| 事件概率 | $\Pr(E\mid\rho)=\operatorname{Tr}(\rho E)$ | 还须正归一读出及实际事件绑定；纯幅度投影时为$q(P\psi)/q(\psi)$。 |

若原 $p$ 的全部数值属于要保留的资料，则必须连同 $\alpha$ 一起保存； $p=\ell^\alpha$ 使其可精确重建。仅保留规范几何相当于忽略保序乘性幂重标号， 这是明确的等价关系，不能说原数值完全没有变化。

### 2.4　各区域不相互隐藏输入

| 区域 | 明示输入 | 闭合输出 |
|:---|:---|:---|
| 本轮核心 | 原签名与六组关系 | 正幂分类、内生$\alpha,\ell,q$、四元数和复二维几何。 |
| 定标辅助引理 | $\ell(2u)=2\ell(u)>0$及对应其余条件；由本轮关系验证 | 同一原实作用上的范数和内积，及忠实四维分类。 |
| 项目旧响应窗口 | A1–A3、准确锥、P2/PB、已付JB/JC及平方标量窗口 | 旧$D\vert _{W^2}$双线性、面积式、同对三轴闭合；不补全域$m$。 |
| 共同锚拼接 | 秩$r$正定锚、单点零余量、双点联合块正性 | 全表正性与同一$r$维表示。 |
| 有限量子接口 | 事件绑定、同复中心联合、全参考正过程、钟流与理想更新四组 | 密度、Born、CP、内部记录、Lüders与薛定谔形式。 |
| 未来及算法闭合 | 固定总系统/菜单/允许分支；若要执行另需有效数据及判零 | 有限维停止；不自动供应计算时间界或物理压缩。 |
| 自指与逻辑 | 指定表示类、评价结构，或有效一致算术理论 | 条件固定点或不可判定性；不输出物理维数增长。 |

### 2.5　全体对象内生所要求的类型

基本幅度块、正事件与过程都可以放入同一有类型的数学理论。 但不能在全部事件矩阵上强加同一正定乘性读出： 若非零正交投影 $P,Q$ 满足 $PQ=0$，则 $p(PQ)=p(P)p(Q)>0$ 与 $p(0)=0$ 矛盾。 因此“均在$\Omega$内”所要求的是同一有类型二元复合和三元相容， 并不是把全部对象都当作一个无零因子的四元数乘法块。

<a id="section-3"></a>

## 3　只输入一次自合成增长，内生读出幂指数

### 3.1　唯一候选与准确的原对象

设 $\mathcal A$ 为原实向量空间，$m:\mathcal A\times\mathcal A\to\mathcal A$ 为原乘法， 记 $xy=m(x,y)$；$p:\mathcal A\to[0,\infty)$ 是原有限非负读出。 本轮核心条件只有以下六组：

$$
\begin{aligned}
\mathsf B_1:\quad&m\text{ 为原实双线性};\\
\mathsf{LB}:\quad&\exists M<\infty\ \forall x,y,\quad
p(x),p(y)\le1\Longrightarrow p(x+y)\le M;\\
\mathsf G:\quad&\exists u,\quad 0<p(u)<p(2u);\\
\mathsf N:\quad&\forall x,y,\quad p(xy)=p(x)p(y);\\
\mathsf U:\quad&\exists\varepsilon\ \forall x,\quad
p(\varepsilon x-x)=p(x\varepsilon-x)=0;\\
\mathsf F:\quad&\exists a,b\ \forall c,\quad
p(T_{a,b}c)=0\Longrightarrow p(c)=0,
\end{aligned}
$$

其中

$$T_{a,b}c=(ab-ba)c+a(bc)-b(ac).$$

$2u=u+u$ 使用原加法。$\mathsf G$ 只要求一份非零可读对象自合成后严格增长， 没有输入增长倍率、指数或原读出的齐次次数。 通常实数、实对数与此前完整证明的标定定理属于明示数学基础。

$$\boxed{\exists u:\quad 0<p(u)<p(u+u).}$$

本轮输出将是原 $p$ 的唯一正幂律， 而不是未经标定就宣称原 $p$ 已具有一次齐次。

### 3.2　同一乘法传播探针，自合成确定唯一指数

#### 引理 3.1：同一个标量字符与探针无关

固定任意满足 $p(u)>0$ 的原对象，定义

$$w(t):=\frac{p(tu)}{p(u)}\qquad(t\in\mathbb R).$$

则对所有原 $t,x$ 有

$$\boxed{p(tx)=w(t)p(x).} \tag{3.1}$$

$w$ 满足

$$w(st)=w(s)w(t),\quad w(1)=1,\quad w(0)=0, \quad w(-t)=w(t),\quad w(t)>0\ (t\ne0).$$

因此 $w$ 与所选非零可读探针无关，且

$$\boxed{ d:=\frac{p(2u)}{p(u)}=w(2)>1, \qquad \alpha:=\frac{\log d}{\log2}>0 } \tag{3.2}$$

是原数据确定的唯一常数。

**证明。**

原双线性给完全相同的原乘积 $(tx)u=x(tu)$。 乘性给 $p(tx)p(u)=p(x)p(tu)$，消去 $p(u)>0$ 得 (3.1)。 将其用于 $x=su$，得 $w(ts)=w(t)w(s)$；定义给 $w(1)=1$。 $\mathsf G$ 的某一探针给 $w(2)=d>1$。 于是 $w(0)=w(2)w(0)=dw(0)$；有限性和 $d>1$ 迫使 $w(0)=0$，进而 $p(0)=0$。 又 $w(-1)^2=1$，非负性给 $w(-1)=1$。 对 $t\ne0$，$w(t)w(t^{-1})=1$，所以 $w(t)>0$。

若 $v$ 是另一个满足 $p(v)>0$ 的探针，式 (3.1) 给 $p(tv)/p(v)=w(t)$，因此同一字符及同一 $d$ 不依赖探针。 $2^\alpha=d$ 在 $\alpha\in\mathbb R$ 上只有一个解；$d>1$ 保证该解为正。

$\square$

在使用 $\mathsf{LB}$ 或分类以前，原对象已经满足

$$p(2^j x)=d^jp(x)=2^{\alpha j}p(x)\qquad(j\in\mathbb Z).$$

不过此时尚未证明 $w(t)=|t|^\alpha$；完整原实轴恢复仍需其余关系约束。

#### 定义 3.2：由原增长率定义的规范读出

用式 (3.2) 中已经内生确定的 $\alpha$，定义

$$\ell(x):=p(x)^{1/\alpha}\quad(=p_\ast(x)),\qquad q(x):=\ell(x)^2=p(x)^{2/\alpha}. \tag{3.3}$$

这里 $0^{1/\alpha}=0$。原 $p$ 始终保留，并可由 $p=\ell^\alpha$ 精确恢复。

#### 引理 3.3：逐项进入单次精确标定定理

保持原空间、原实作用和原乘法不变，以 $\ell$ 作证明辅助读出， 则它满足上一轮的六组条件：原实双线性、有限单位输入合成界、 单探针精确标定、精确乘性、可读双侧单位及同对忠实。

**证明。**

正指数保证 $\ell$ 有限、非负，且

$$\ell(x)=0\Longleftrightarrow p(x)=0, \qquad \ell(x)\le1\Longleftrightarrow p(x)\le1.$$

原双线性未作任何改动。 若 $\ell(x),\ell(y)\le1$，原 $\mathsf{LB}$ 给

$$\ell(x+y)=p(x+y)^{1/\alpha}\le M^{1/\alpha},$$

所以仍有同一个对全部原输入适用的有限局部界。 原探针给

$$\ell(2u)=d^{1/\alpha}\ell(u)=2\ell(u)>0,$$

恰为上一轮的单次精确标定。 乘性逐点给

$$\ell(xy)=\bigl(p(x)p(y)\bigr)^{1/\alpha} =\ell(x)\ell(y).$$

由于零集合完全相同，原 $\mathsf U$ 的两份零差原样保留， 原 $\mathsf F$ 的同一对、同一个 $T_{a,b}$ 和全部原第三元量词也原样保留。 没有添加连续性、完备性、内积、维数或原乘法结合性。

$\square$

### 3.3　原读出的完整幂律分类

#### 定理 3.4：自合成增长的完整分类

在本轮六组条件下，令 $N_0=p^{-1}(0)$。 则 $N_0$ 为原实线性双边理想，原读出精确恒于其陪集。 同一原可读商 $A=\mathcal A/N_0$ 带原乘法满足

$$\boxed{(A,m,p)\cong(\mathbb H,\cdot,|\cdot|^\alpha),} \tag{3.4}$$

其中 $\alpha$ 是 (3.2) 唯一确定的正数。 特别地，对全部原 $t,x$，

$$\boxed{p(tx)=|t|^\alpha p(x).} \tag{3.5}$$

原函数还满足

$$p(x+y)^{1/\alpha}\le p(x)^{1/\alpha}+p(y)^{1/\alpha}, \tag{3.6}$$

以及

$$p(x+y)^{2/\alpha}+p(x-y)^{2/\alpha} =2p(x)^{2/\alpha}+2p(y)^{2/\alpha}. \tag{3.7}$$

其规范极化

$$\mathcal B(x,y)=\frac14\bigl(p(x+y)^{2/\alpha}-p(x-y)^{2/\alpha}\bigr)$$

为原实半正双线性型，且 $\operatorname{rad}\mathcal B=N_0$。

**证明。**

引理 3.3 已逐项验证单次精确标定定理的前提。 因此将完整保留的定理 7.5 应用于 $\ell$， 得到同一个原实作用下

$$\ell(tx)=|t|\ell(x),$$

以及 $\ell$ 的普通三角、平行四边形和精确零核下降。 其零核就是原 $N_0$，所以商空间与原零读出等价关系没有变化。 由 $p=\ell^\alpha$，这些结论分别成为 (3.5)–(3.7)， 且 $p(x+n)=\ell(x+n)^\alpha=\ell(x)^\alpha=p(x)$。

同一标定恢复定理中的忠实分类部分 给出原实代数等距同构

$$\Phi:(A,m,\ell)\longrightarrow(\mathbb H,\cdot,|\cdot|).$$

因而原读出满足 $p(x)=|\Phi([x])|^\alpha$，即 (3.4)。 极化是原规范平方 $q=\ell^2$ 的极化，故为原实半正双线性型，根基恰为 $N_0$。 上述调用中的辅助完成、原实轴恢复与同对投影均有独立完整证明； 原 $\mathsf F$ 没有被擅自延拓到任何完成。

$\square$

#### 定理 3.5：反向实现与指数唯一

固定原实双线性代数 $\mathcal A$。 本轮其余五组条件成立，当且仅当存在 $\alpha>0$ 和满射原实代数同态

$$\Psi:\mathcal A\longrightarrow\mathbb H$$

使

$$p(x)=|\Psi(x)|^\alpha\qquad(x\in\mathcal A). \tag{3.8}$$

在这种表示中，$\ker\Psi=N_0$，而 $\alpha$ 由原读出唯一决定。 代数同构的坐标选择可以不同，指数不能不同。

**证明。**

正向，将上一主定理的商映射与 $\Phi$ 复合即得 $\Psi$。

反向，设 (3.8) 成立。 满射性允许选择 $\varepsilon,a,b$，使 $\Psi(\varepsilon)=1$、$\Psi(a)=i$、$\Psi(b)=j$。 实线性与范数给 $p(2\varepsilon)=2^\alpha>1=p(\varepsilon)$，所以 $\mathsf G$ 成立。 若 $p(x),p(y)\le1$，则 $|\Psi(x)|,|\Psi(y)|\le1$，从而

$$p(x+y)=|\Psi(x)+\Psi(y)|^\alpha\le2^\alpha.$$

故 $\mathsf{LB}$ 可取 $M=2^\alpha$。 同态性质与四元数范数给精确乘性。 原两份单位差均被 $\Psi$ 映为零，所以 $\mathsf U$ 成立。 结合性仅在目标四元数内使用，给

$$\Psi(T_{a,b}c)=4k\,\Psi(c).$$

因此

$$p(T_{a,b}c)=4^\alpha p(c),$$

同一原对满足 $\mathsf F$。 $\ker\Psi=N_0$ 直接来自范数正定性。

若同一个原 $p$ 还以另一个 $\alpha'>0$ 实现，对任意 $p(u)>0$ 有

$$2^\alpha=\frac{p(2u)}{p(u)}=2^{\alpha'}.$$

正实指数函数单射，故 $\alpha=\alpha'$。

$\square$

#### 推论 3.6：共同局部预算的最小值也被恢复

在完整候选下，单位输入合成的最小共同上界为

$$\sup_{p(x),p(y)\le1}p(x+y)=2^\alpha=d.$$

若原输入提供某个有限 $M$，必有 $d\le M$，但它无需给出 $d$ 的具体值。

**证明。**

范数分类给上界 $2^\alpha$。 取原可读单位的任意代表 $\varepsilon$，有 $p(\varepsilon)=1$， 而 $p(\varepsilon+\varepsilon)=2^\alpha$，所以上界达到。

$\square$

### 3.4　几何不依赖正幂刻度，原数值读出仍被保留

#### 定理 3.7：正幂改写的规范几何不变性

对任意 $\beta>0$，定义 $\widetilde p=p^\beta$，并由该新读出的同一自合成实验定义 $\widetilde d,\widetilde\alpha,\widetilde\ell,\widetilde q$。 则新读出满足同一六组条件，并有

$$\widetilde d=d^\beta,\qquad \widetilde\alpha=\beta\alpha,\qquad \boxed{\widetilde\ell=\ell,\quad\widetilde q=q.} \tag{3.9}$$

因此原零核、规范实内积、同一对投影、复结构及射影几何完全相同。

**证明。**

正幂保持零集合、单位子水平集和严格大小关系，所以 $\mathsf G,\mathsf U,\mathsf F$ 保留； 原乘法与双线性不变，精确乘性保留，$\mathsf{LB}$ 可用上界 $M^\beta$。 同一探针给

$$\widetilde d=\frac{p(2u)^\beta}{p(u)^\beta}=d^\beta, \qquad \widetilde\alpha=\frac{\log(d^\beta)}{\log2}=\beta\alpha.$$

故

$$\widetilde\ell=(p^\beta)^{1/(\beta\alpha)}=p^{1/\alpha}=\ell, \qquad \widetilde q=(p^\beta)^{2/(\beta\alpha)}=p^{2/\alpha}=q.$$

规范内积由 $q$ 极化，因而不变。 原乘法没有改变，所以同一原对的 $k=ab-ba$、$T_{a,b}$ 也不变， 继而由规范平方读出定义的

$$P_H=-\frac{L_kT_{a,b}}{2q(k)},\qquad J=\frac{T_{a,b}}{2\sqrt{q(k)}},\qquad h(x,y)=B(x,y)+iB(Jx,y)$$

全部不变。复射线、正交关系及其 Hopf 几何随之相同。

$\square$

#### 引理 3.8：保序乘性重标号恰好是正幂

若 $f:[0,\infty)\to[0,\infty)$ 严格递增，且满足

$$f(0)=0,\quad f(1)=1,\quad f(st)=f(s)f(t),$$

则存在唯一 $\beta>0$ 使 $f(t)=t^\beta$ 对所有 $t\ge0$ 成立。 反之每个正幂都满足这些条件。

**证明。**

严格递增使 $f(t)>0$ 对 $t>0$ 成立。 定义 $g(s)=\log f(e^s)$，则乘性给 $g(s+t)=g(s)+g(t)$，且 $g$ 严格递增。 令 $\beta=g(1)>0$。可加性给 $g(r)=\beta r$ 对全部有理数成立； 用有理数从上下逼近任意实数，单调性给 $g(s)=\beta s$。 故对 $t>0$，$f(t)=\exp(g(\log t))=t^\beta$；零点已知。 唯一性可由 $f(e)=e^\beta$ 得到，反向直接验证。

$\square$

此引理分类的是允许的保序乘性重标号，不是向主候选添加一个新输入。 给定原 $p$ 后 $\alpha$ 唯一；对读数作这样的重标号时，$\alpha$ 按 $\alpha\mapsto\beta\alpha$ 变化，而规范 $\ell$ 完全不变。

#### 引理 3.9：只用原读数比较恢复同一个规范长度

设 $\varepsilon$ 为原可读双侧单位的任意代表，则

$$\boxed{\ell(x)=\sup\{r\in\mathbb Q_{\ge0}:p(r\varepsilon)\le p(x)\}.}$$

**证明。**

主分类给 $p(\varepsilon)=1$、$p(r\varepsilon)=r^\alpha$、$p(x)=\ell(x)^\alpha$。 由于 $\alpha>0$，集合中的比较等价于 $r\le\ell(x)$；有理数的稠密性给所列上确界。 该集合非空且有界，包括 $\ell(x)=0$ 的情形。

$\square$

上式是原读数关系中的精确定义，没有由此声称该上确界能够被有效计算。

规范二分权重具有显式原读出形式

$$\frac{q(x)}{q(x)+q(y)} =\frac{p(x)^{2/\alpha}}{p(x)^{2/\alpha}+p(y)^{2/\alpha}} \qquad(q(x)+q(y)>0).$$

这一表达式在同时替换 $p\mapsto p^\beta$、$\alpha\mapsto\beta\alpha$ 后不变。 将实际准备、事件与该规范平方读出绑定，仍属于明确保留的量子读出接口。 本节没有证明任意原数值比 $p(x)/(p(x)+p(y))$ 都已经是上述规范权重。

### 3.5　相对上一轮的真实弱化与原读出的限制

#### 命题 3.10：增长严格弱于精确翻倍

上一轮的 $\mathsf{CAL}:\exists u,\ p(2u)=2p(u)>0$ 蕴含本轮 $\mathsf G$。 反向即使加入其余全部核心条件也不成立。 原读出满足全实一次齐次，当且仅当内生 $\alpha=1$。

**证明。**

正向直接由 $2p(u)>p(u)>0$。 反向，在标准四元数上取任意 $\alpha>0$、$\alpha\ne1$，令

$$p(x)=|x|^\alpha.$$

反向实现定理保证全部新条件成立。 但每个非零探针都满足 $p(2u)/p(u)=2^\alpha\ne2$，所以没有探针满足旧精确翻倍条件。

若 $\alpha=1$，式 (3.5) 就是全实一次齐次。 若原 $p$ 全实一次齐次，对非零探针取 $t=2$，得 $2^\alpha=2$，于是 $\alpha=1$。

$\square$

两轮的 *原读出模型类* 因此不同：本轮允许全部唯一确定的正指数。 相同的是由 $\ell$、$q$ 和原乘法定义的规范四元数几何。 这里没有把一次幂变换冒充原 $p$ 自己已经一次齐次，也没有把指数自由抹去。

#### 推论 3.11：原读出的普通三角何时成立

完整候选中的原 $p$ 满足普通三角不等式，当且仅当 $0<\alpha\le1$。 其规范读出 $\ell$ 对全部 $\alpha>0$ 都是半范数。

**证明。**

若 $0<\alpha\le1$，由 $\ell$ 的三角和正实数的凹幂不等式，

$$p(x+y)\le\bigl(\ell(x)+\ell(y)\bigr)^\alpha \le p(x)+p(y).$$

若 $\alpha>1$，取任意 $p(u)>0$，则 $p(u+u)=2^\alpha p(u)>2p(u)$，普通三角失败。 $\ell$ 的结论已经由标定恢复定理证明。

$\square$

**图示（文字版）。** 横轴为规范长度 $\ell(x)$，纵轴为原读数 $p(x)$。三条曲线分别为 $p=\ell^{1/2}$、$p=\ell$ 与 $p=\ell^2$；均经过 $(0,0)$ 和 $(1,1)$，当 $\ell=2$ 时读数分别为 $\sqrt2$、$2$ 与 $4$。

**图 1。** 三种合法原读数具有同一个零点、单位球和规范几何。 从一次自合成读数比$d$确定$\alpha$后，$p^{1/\alpha}$都回到同一条长度轴； 若保留原数值，指数也必须保留。

<a id="section-4"></a>

## 4　辅助定理：已齐次读出的范数恢复

本节重证一个已定标读出的独立辅助命题。以下的 $\ell$ 始终是长度读出，不是本轮原 $p$。它的局部输入是实双线性乘法、非零读出、 精确乘性、可读左单位，以及下列 *已齐次* 背景：

$$\mathsf B_2^{22}:\quad \ell(tx)=|t|\ell(x)\quad(t\in\mathbb R),\qquad \ell(x),\ell(y)\le1\Longrightarrow \ell(x+y)\le M<\infty.$$

本节中的 $\mathsf E$ 只表示 $\exists x:\ell(x)>0$；$\mathsf U_q$ 是可读单位的平方读数版本。 **全实齐次在本节是辅助假设，在本辅助证明内部尚未取得。** 下一阶段先由单探针标定构造新的连续实标量作用，再对该辅助结构应用本节， 最后另证新旧实标量相同。这个次序避免用原齐次证明原齐次。 本节恢复普通三角只使用左单位，不使用 $\mathsf F$； 下一阶段锁定原实标量则确实使用 $\mathsf F$ 所给的非交换见证。

$$\ell(x),\ell(y)\le1\Longrightarrow \ell(x+y)\le M\quad(M<\infty\text{ 对所有原输入共同适用}). \tag{4.1}$$

### 4.1　准三角与有限加和的准确代价

#### 引理 4.1：有限单位合成界等价于某个统一准三角界

对绝对一次齐次的非负函数 $\ell$，式 (4.1) 的局部有界部分 等价于存在有限常数 $C\ge1$ 使

$$\ell(x+y)\le C\bigl(\ell(x)+\ell(y)\bigr)\qquad(\forall x,y). \tag{4.2}$$

**证明。**

准三角在 $\ell(x),\ell(y)\le1$ 上给局部界 $2C$。 反向令 $s=\ell(x)+\ell(y)$。若 $s>0$，则 $\ell(x/s),\ell(y/s)\le1$， 局部界与齐次性给 $\ell(x+y)\le Ms$。 若 $s=0$，则对每个 $t>0$ 都有 $\ell(tx)=\ell(ty)=0\le1$， 从而 $t \ell(x+y)\le M$。令 $t\to\infty$ 得 $\ell(x+y)=0$。 取 $C=\max\{1,M\}$ 即可。

$\square$

下文固定这样一份由原局部界导出的 $C$。这没有增加另一个独立输入条件。 定义

$$K_n=C^{\lceil\log_2n\rceil}\qquad(n\ge1).$$

#### 引理 4.2：平衡二叉加和界

对任意 $n\ge1$ 与 $z_1,\ldots,z_n\in\mathcal A$，

$$\ell\!\left(\sum_{j=1}^nz_j\right) \le K_n\sum_{j=1}^n\ell(z_j). \tag{4.3}$$

**证明。**

补零到 $2^h$ 项，其中 $h=\lceil\log_2n\rceil$。 按等深二叉树逐层相加，在每一层使用一次 (4.2)， 共乘以 $C^h$。向量加法可重新分组；本证明未使用原乘法结合性。

$\square$

### 4.2　零核与连续性均须由乘法重复推出

#### 引理 4.3：原零核上的精确不变性

在 $\mathsf B_1+\mathsf B_2^{22}+\mathsf N$ 下， $N=\ell^{-1}(0)$ 为实线性双边理想，且

$$\boxed{\ell(x+n)=\ell(x)\qquad(x\in\mathcal A,\ n\in N).} \tag{4.4}$$

因此原商 $A_0$ 上的 $\ell([x])=\ell(x)$ 良定、正定、绝对一次齐次、 满足同一个准三角界且精确乘性。 在 $\mathsf E$ 与可读左单位下，商非零，并有真正左单位 $1=[\varepsilon]$，$\ell(1)=1$。 原条件若含右单位，它也分别下降。

**证明。**

齐次性与准三角给 $N$ 线性，乘性给 $\ell(xn)=\ell(nx)=0$，故 $N$ 为理想。 此时只由准三角尚只能得到 $\ell(x+n)\le C\ell(x)$，不能直接下推 $\ell$。

对每个正整数 $k$ 固定一份完全括号方式，记含 $k$ 个 $x$ 的乘法单项式为 $x^{[k]}$。 由双线性与理想性，

$$(x+n)^{[k]}-x^{[k]}\in N.$$

精确乘性与准三角给

$$\ell(x+n)^k =\ell\bigl((x+n)^{[k]}\bigr) \le C \ell\bigl(x^{[k]}\bigr) =C \ell(x)^k.$$

取 $k$ 次根，再令 $k\to\infty$，得到 $\ell(x+n)\le \ell(x)$。 对 $x+n$ 和 $-n$ 反向重复，得等式。 商乘法由理想性良定，原各条件继承。 可读单位的零差在商中成为真正等式。 非平凡性给非零 $x$，从 $\ell(1x)=\ell(1)\ell(x)=\ell(x)$ 消去 $\ell(x)$，得到 $\ell(1)=1$。

$\square$

#### 引理 4.4：有限乘法幂的差界

若 $\ell(x),\ell(y)\le R$、$R>0$，并记 $\delta=\ell(x-y)$， 则对任意 $n\ge1$ 及任意固定完全括号的乘法单项式有

$$\ell\bigl(x^{[n]}-y^{[n]}\bigr) \le nK_nR^{n-1}\delta. \tag{4.5}$$

**证明。**

固定括号方式给一个实 $n$ 线性映射 $F_n$。 逐个槽替换的望远镜展开为

$$F_n(x,\ldots,x)-F_n(y,\ldots,y) =\sum_{j=1}^nF_n(y,\ldots,y,x-y,x,\ldots,x).$$

第 $j$ 项的读出由乘性精确等于 $\ell(y)^{j-1}\delta \ell(x)^{n-j}$，至多为 $R^{n-1}\delta$。 应用引理 4.2 即得。

$\square$

#### 引理 4.5：原读出在有界集合上一致连续

对 $\ell(x),\ell(y)\le R$、$R>0$ 及 $\delta=\ell(x-y)$，

$$\boxed{ |\ell(x)-\ell(y)| \le (C^{1/n}-1)R+ \bigl(CnK_nR^{n-1}\delta\bigr)^{1/n} \quad(\forall n\ge1). } \tag{4.6}$$

特别地，$\ell$ 在每个 $\ell$ 有界集合上一致连续。

**证明。**

原准三角、乘性及引理 4.4 给

$$\ell(x)^n\le C \ell(y)^n+CnK_nR^{n-1}\delta.$$

对非负数使用 $(a+b)^{1/n}\le a^{1/n}+b^{1/n}$，得

$$\ell(x)-\ell(y) \le(C^{1/n}-1)\ell(y)+\bigl(CnK_nR^{n-1}\delta\bigr)^{1/n}.$$

将 $\ell(y)$ 换为上界 $R$，再交换 $x,y$，得到显示式。 给定 $\epsilon>0$，先选有限 $n$ 使 $(C^{1/n}-1)R<\epsilon/2$； 再令 $\delta$ 足够小，使余项小于 $\epsilon/2$。 次序是先固定一个有限幂，再缩小输入差，不是无依据地交换两个极限。

$\square$

### 4.3　精确保留原乘法读出的完成

#### 引理 4.6：直接 Cauchy 完成

原商 $A_0$ 可嵌入一个非零完备实向量空间 $B$，其读出 $\ell$ 和乘法 保留原准三角界、绝对一次齐次性、精确乘性以及原单位律。 完成不需要先把 $\ell$ 改换为等价的幂次准范数。

**证明。**

称 $(x_n)$ 为 Cauchy 序列，若 $\ell(x_n-x_m)\to0$。 准三角给它 $\ell$ 有界：固定一个足够晚的 $x_N$，对其后的项用 $\ell(x_n)\le C(\ell(x_N)+\ell(x_n-x_N))$。 引理 4.5 因而给 $\ell(x_n)$ 为实 Cauchy 序列。

对两个 Cauchy 序列规定

$$(x_n)\sim(y_n)\quad\Longleftrightarrow\quad \ell(x_n-y_n)\to0.$$

准三角保证传递性。令 $B$ 为这些序列的商，并定义

$$\ell([x_n])=\lim_{n\to\infty}\ell(x_n).$$

有界集一致连续性保证代表无关。 该极限为零恰好表示 $(x_n)$ 等价于零序列，因此完成中的 $\ell$ 正定。 和、固定实数倍按逐项运算定义；准三角与齐次性保证良定。

若 $x_n,y_n$ 为 Cauchy 序列，双线性与准三角给

$$
\begin{split}
\ell(x_ny_n-x_my_m)
\le C\bigl(&\ell(x_n-x_m)\ell(y_n)\\
&+\ell(x_m)\ell(y_n-y_m)\bigr).
\end{split}
$$

两序列有界，故乘积也 Cauchy；同一估计说明更换代表不改变乘积等价类。 精确乘性由

$$\ell([x_n][y_n]) =\lim_n \ell(x_n)\ell(y_n) =\ell([x_n])\ell([y_n])$$

保留。双线性、原准三角、一次齐次性和单位等式也逐项下降。

常值序列给原商的等读出嵌入。任一 $X=[x_n]$ 满足

$$\ell(X-x_N)=\lim_{n\to\infty}\ell(x_n-x_N)\longrightarrow0\quad(N\to\infty),$$

其中最后一步由原 Cauchy 条件给出，故原商稠密。 为证明 $B$ 完备，设 $(X_j)$ 是 $B$ 中 Cauchy 序列。 由稠密性选 $a_j\in A_0$ 使 $\ell(X_j-a_j)<1/j$。 三项加和界给

$$\ell(a_j-a_k) \le K_3\bigl(1/j+\ell(X_j-X_k)+1/k\bigr),$$

所以 $(a_j)$ 为原商中的 Cauchy 序列。 令 $X=[a_j]$，则 $\ell(a_j-X)\to0$，再由

$$\ell(X_j-X)\le C\bigl(\ell(X_j-a_j)+\ell(a_j-X)\bigr)$$

得到 $X_j\to X$。

引理 4.5 的证明只使用已保留的代数与准三角条件， 所以同样适用于 $B$。 其读出球是开集并构成可数邻域基：若 $\ell(x-a)<\epsilon$， 由连续性可选足够小的 $\ell(y-x)$ 保证 $\ell(y-a)<\epsilon$。 向量运算连续由准三角与齐次性给出，乘法在有界邻域上由上述乘积差估计连续。 因此此完成是所需的完备拓扑代数。

$\square$

完成仅作证明工具。后续所有分类结论必须限制回同一个原商； 原 $\mathsf F$ 的量词没有自动扩张到 $B$。

### 4.4　算子、左除和有限重复

对 $B$ 的有界实线性算子，定义

$$\|R\|_{\rm op} =\sup_{x\ne0}\frac{\ell(Rx)}{\ell(x)}.$$

#### 引理 4.7：算子完成与小半径 Neumann 公式

有界算子构成完备实向量空间，满足

$$\|R+S\|_{\rm op}\le C(\|R\|_{\rm op}+\|S\|_{\rm op}), \qquad \|RS\|_{\rm op}\le\|R\|_{\rm op}\|S\|_{\rm op}.$$

若 $\|R\|_{\rm op}<1/C$，则

$$(I+R)^{-1}=\sum_{n=0}^{\infty}(-R)^n.$$

**证明。**

逐个作用于 $x$ 并取上确界给两个不等式。 若 $R_n$ 是算子 Cauchy 序列，则每个 $R_nx$ 在 $B$ 中收敛。 向量运算连续，故逐点极限 $R$ 实线性。 原算子序列的读数统一有界；$\ell$ 的连续性给极限算子有界。 对

$$\ell((R_n-R_m)x) \le\|R_n-R_m\|_{\rm op}\ell(x)$$

令 $m\to\infty$，再取上确界，即得 $R_n\to R$ 的算子准范数收敛。

令 $\rho=\|R\|_{\rm op}<1/C$。 对有限尾和采用右嵌套加和，每一步用原准三角，得

$$\left\|\sum_{k=m}^{n}(-R)^k\right\|_{\rm op} \le C\rho^m\sum_{j=0}^{n-m}(C\rho)^j \le\frac{C\rho^m}{1-C\rho}.$$

它随 $m\to\infty$ 一致趋零，故级数在完整算子空间中收敛。 有限几何恒等式给部分和与 $I+R$ 的两侧乘积均趋于 $I$； 算子复合连续性使极限为双侧逆。 这里只使用算子复合的结合律，未使用 $B$ 原乘法的结合律。

$\square$

#### 引理 4.8：所有非零左乘为满射相似

对每个非零 $x\in B$，$L_x:y\mapsto xy$ 为满射，且

$$\|L_x\|_{\rm op}=\ell(x), \qquad \|L_x^{-1}\|_{\rm op}=\ell(x)^{-1}.$$

**证明。**

乘性给 $\ell(L_xy)=\ell(x)\ell(y)$，因此 $L_x$ 单射，算子读数恰为 $\ell(x)$； 若满射，逆读数必为其倒数。 实维数一时非零线性单射自动满射。 实维数至少二时，令

$$\mathcal G=\{x\in B\setminus\{0\}:L_x\text{ 满射}\}.$$

左单位使 $\mathcal G$ 非空。 若 $x\in\mathcal G$ 且 $\ell(y-x)/\ell(x)<1/C$，则

$$L_y=L_x\bigl[I+L_x^{-1}(L_y-L_x)\bigr], \qquad \|L_x^{-1}(L_y-L_x)\|_{\rm op} \le\frac{\ell(y-x)}{\ell(x)}<1/C.$$

Neumann 引理给 $L_y$ 可逆，故 $\mathcal G$ 相对开。 若 $x_n\in\mathcal G$ 且 $x_n\to x\ne0$，读出连续性给 $\ell(x_n)\to \ell(x)>0$，充分大的 $n$ 满足同一小扰动条件，故 $x\in\mathcal G$。 读出球构成可数邻域基，因此这证明相对闭。

穿孔实向量空间 $B\setminus\{0\}$ 在维数至少二时路径连通： 直线段若过零，就取不在该直线上的一个中间点，用两条避零线段连接。 每条线段在当前拓扑中连续，因为其参数差的读出等于参数差绝对值乘以一个固定读数。 因此非空开闭集 $\mathcal G$ 等于整个穿孔空间。

$\square$

#### 定理 4.9：有限局部界恢复普通三角不等式

在实双线性乘法、$\mathsf B_2^{22}+\mathsf E+\mathsf N$ 以及可读左单位下， 原读出满足

$$\boxed{\ell(x+y)\le \ell(x)+\ell(y)\qquad(\forall x,y\in\mathcal A).} \tag{4.7}$$

**证明。**

在上述完成中取 $y\ne0$，定义

$$S=L_xL_y^{-1},\qquad S+I=L_{x+y}L_y^{-1},\qquad \alpha=\frac{\ell(x)}{\ell(y)},\quad \beta=\frac{\ell(x+y)}{\ell(y)}.$$

它们是比例分别为 $\alpha,\beta$ 的精确相似；零比例的情形按零算子理解。 因此

$$\|S^k\|_{\rm op}=\alpha^k\quad(k\ge1),\qquad \|(S+I)^n\|_{\rm op}=\beta^n,$$

且 $\|S^0\|_{\rm op}=\|I\|_{\rm op}=1$。 算子复合的有限二项式与引理 4.2 的算子版本给

$$
\begin{aligned}
\beta^n
&=\left\|\sum_{k=0}^{n}\binom nk S^k\right\|_{\rm op}\\
&\le K_{n+1}\sum_{k=0}^{n}\binom nk\alpha^k
=K_{n+1}(1+\alpha)^n.
\end{aligned}
$$

故

$$\beta\le C^{\lceil\log_2(n+1)\rceil/n}(1+\alpha).$$

因为 $\lceil\log_2(n+1)\rceil/n\to0$，令 $n\to\infty$ 得 $\beta\le1+\alpha$，即完成中的普通三角不等式。 $y=0$ 情形直接成立。 限制回原商，再使用精确零核下降，得到原 $\mathcal A$ 上同一读出的显示结论。

$\square$

<a id="section-5"></a>

## 5　辅助定理续：乘性迫使二元平面成为欧氏平面

在上一节明确的辅助假设下，已经证明该结构上的 $\ell$ 是半范数。所构造的同一 Cauchy 完成 $B$ 现在是普通实 Banach 空间；无需另加完备性条件。 所有非零左乘的满射相似性质已由引理 4.8 证明。 本节不使用 $\mathsf F$，也不把它延拓到辅助完成。 单侧除法绝对值代数的内积范数性质有既有研究；以下给出自足谱证明。[\[13\]](#ref-rodriguez)

### 5.1　每个二元平面都被迫成为欧氏平面

下面仅构造一个复线性证明辅助空间；它不预先赋予原系统任何复数结构。

#### 引理 5.1：保持相似倍率的复化

对实 Banach 空间 $B$，在 $B_{\mathbb C}:=B\oplus iB$ 上定义

$$\|u+iv\|_{\mathbb C} :=\sup_{\theta\in[0,2\pi]} \|u\cos\theta-v\sin\theta\|.$$

这给出复 Banach 空间范数。 若 $R:B\to B$ 为满射实线性相似，倍率为 $r>0$，则其复化 $R_{\mathbb C}(u+iv):=Ru+iRv$ 仍为满射相似，倍率同为 $r$。

**证明。**

正定性和三角不等式逐点成立。 乘以 $e^{i\phi}$ 仅把上式中的角度 $\theta$ 平移为 $\theta+\phi$， 故范数具有复绝对齐次性。并且

$$\max\{\|u\|,\|v\|\}\le\|u+iv\|_{\mathbb C} \le\|u\|+\|v\|,$$

所以该范数完备。 相似律直接给

$$\|Ru+iRv\|_{\mathbb C} =\sup_\theta r\|u\cos\theta-v\sin\theta\| =r\|u+iv\|_{\mathbb C}.$$

实逆算子的复化是复逆，因此满射性也保持。

$\square$

#### 引理 5.2：仅用到的谱事实及证明

设 $X\ne0$ 为复 Banach 空间，$S\in\mathcal L(X)$。 定义

$$\sigma(S):=\{\lambda\in\mathbb C:\lambda I-S\text{ 无有界双侧逆}\}.$$

则 $\sigma(S)\ne\varnothing$。 若 $S$ 是倍率为 $r>0$ 的满射相似，则

$$\sigma(S)\subset\{\lambda:|\lambda|=r\}.$$

若 $\lambda\in\sigma(S)$、$\alpha,\beta\in\mathbb R$，则 $\alpha\lambda+\beta\in\sigma(\alpha S+\beta I)$。

**证明。**

先证非空。若处处可逆，则 $R(z):=(zI-S)^{-1}$ 为处处解析的算子值函数； 这一解析性来自每一点附近的 Neumann 级数。 当 $|z|>\|S\|$，

$$R(z)=z^{-1}\sum_{n\ge0}(S/z)^n, \qquad \|R(z)\|\le\frac1{|z|-\|S\|}.$$

对任意 $v\in X$ 和连续复线性泛函 $\varphi$， $z\mapsto\varphi(R(z)v)$ 为在无穷远趋零的有界整函数， 由 Liouville 定理恒为零。连续线性泛函分离点，故 $R(z)=0$， 与 $(zI-S)R(z)=I\ne0$ 矛盾。

对满射相似，$\|S\|=r$、$\|S^{-1}\|=r^{-1}$。 若 $|\lambda|>r$，则对 $\lambda I-S$ 使用外圈 Neumann 级数； 若 $|\lambda|<r$，则

$$S-\lambda I=S(I-\lambda S^{-1})$$

可由内圈 Neumann 级数求逆。 所以谱只能在 $|\lambda|=r$ 上。

最后若 $\alpha\ne0$，

$$(\alpha\lambda+\beta)I-(\alpha S+\beta I) =\alpha(\lambda I-S)$$

给出所需非可逆性；若 $\alpha=0$，则 $\sigma(\beta I)=\{\beta\}$。

$\square$

#### 定理 5.3：二元平面欧氏化

设 $B$ 满足引理 4.8 的条件。 任给 $x,y\in B$、$y\ne0$，存在一个复数 $\lambda$，使所有 $\alpha,\beta\in\mathbb R$ 同时满足

$$\boxed{\quad \|\alpha x+\beta y\|^2 =\|y\|^2\,|\alpha\lambda+\beta|^2. \quad} \tag{P}$$

因此原范数满足平行四边形恒等式。

**证明。**

令 $S:=L_xL_y^{-1}$，并按引理 5.1 将其复化。 选取一个 $\lambda\in\sigma(S_{\mathbb C})$。 对实数 $\alpha,\beta$，双线性给原实算子等式

$$\alpha S+\beta I=L_{\alpha x+\beta y}L_y^{-1}.$$

若 $\alpha x+\beta y\ne0$，引理 4.8 使右式成为 倍率

$$r_{\alpha,\beta}=\frac{\|\alpha x+\beta y\|}{\|y\|}$$

的满射相似。复化保留此倍率，而 $\alpha\lambda+\beta$ 属于其谱，因此谱圆结论给 $|\alpha\lambda+\beta|=r_{\alpha,\beta}$。 若 $\alpha x+\beta y=0$，对应算子为零，其谱仅为 $\{0\}$， 所以 $\alpha\lambda+\beta=0$；同一公式仍成立。 这证明 (P)。

由 (P) 对 $(\alpha,\beta)=(1,1),(1,-1),(1,0)$ 使用同一个 $\lambda$，得

$$
\begin{aligned}
\|x+y\|^2+\|x-y\|^2
&=\|y\|^2\bigl(|\lambda+1|^2+|\lambda-1|^2\bigr)\\
&=2\|y\|^2(|\lambda|^2+1)
=2\|x\|^2+2\|y\|^2.
\end{aligned}
$$

$y=0$ 时该式直接成立。 若 $x,y$ 独立，$\operatorname{Im}\lambda\ne0$，否则 $(\alpha,\beta)=(1,-\lambda)$ 会使一个非零实线性组合的范数为零。 故独立二元张成的平面等距于通常的欧氏平面。

$\square$

#### 引理 5.4：极化双线性无需再次输入

设实范数 $\|\cdot\|$ 满足平行四边形恒等式。则

$$B(x,y):=\frac14\bigl(\|x+y\|^2-\|x-y\|^2\bigr)$$

为实内积，并满足 $B(x,x)=\|x\|^2$。

**证明。**

记 $Q(x)=\|x\|^2$。$Q$ 偶性给 $B(x,y)=B(y,x)$， 且 $B(0,y)=0$、$B(x,x)=Q(x)$。 将平行四边形恒等式分别应用于 $(x+y,z)$ 与 $(x-y,z)$，相减得

$$B(x+z,y)+B(x-z,y)=2B(x,y).$$

取 $z=x$ 得 $B(2x,y)=2B(x,y)$。 再令 $x=(u+v)/2$、$z=(u-v)/2$，得到

$$B(u,y)+B(v,y)=2B((u+v)/2,y)=B(u+v,y).$$

于是第一槽可加，继而有有理数齐次性。 由于范数连续，$B$ 连续；对有理数序列取极限得到实数齐次性。 对称性再给第二槽线性。 最后 $B(x,x)=\|x\|^2>0$ 对 $x\ne0$ 成立，故为内积。

$\square$

#### 推论 5.5：恢复的是原 $q$

在实双线性乘法及 $\mathsf B_2^{22}+\mathsf E+\mathsf N+\mathsf U_q$ 下，

$$q(x+y)+q(x-y)=2q(x)+2q(y)$$

对原 $\mathcal A$ 的所有 $x,y$ 成立，并且

$$\mathcal B(x,y):=\frac14\bigl(q(x+y)-q(x-y)\bigr)$$

为半正实双线性型，$\mathcal B(x,x)=q(x)$， $\operatorname{rad}\mathcal B=N$。 此结论的证明只使用 $\mathsf U_q$ 中的左单位部分。

**证明。**

使用前节的同一个原商 $A_0$ 与辅助完成 $B$，在 $B$ 中用上面两条定理得到平行四边形和内积。 将恒等式限制回 $A_0$，再经原商映射拉回 $\mathcal A$，得到所列原函数公式。 核为 $N$，因为商中内积正定。 整个过程没有改变原乘法、原 $q$ 或原零读出等价关系。

$\square$

证明采用通常实、复分析，包括 Neumann 级数、Liouville 定理，以及 Hahn–Banach 的连续泛函分离结论。这些属于明示数学基础；谱证明中的辅助 $i$ 并非原物理幅度已经拥有复结构。原幅度的复结构稍后由原见证对导出；辅助复化不属于主候选的物理输入。

<a id="section-6"></a>

## 6　定标引理的完整重证：从一次等式恢复原实轴

本节作为独立定标引理工作；其输入读出记为 $\ell$。本稿将用内生函数 $\ell=p^{1/\alpha}$ 满足这些条件，再调用结论。这里的对象是实向量空间 $\mathcal A$、原实双线性乘法 $xy$ 和有限非负读出 $\ell:\mathcal A\to[0,\infty)$。这里不输入 $\ell(tx)=|t|\ell(x)$。 除原实双线性 $\mathsf B_1$ 外，准确使用以下条件：

$$
\begin{aligned}
\mathsf{LB}:\quad&\exists M<\infty\ \forall x,y,\quad
\ell(x),\ell(y)\le1\Longrightarrow \ell(x+y)\le M;\\
\mathsf{CAL}:\quad&\exists u,\quad \ell(2u)=2\ell(u)>0;\\
\mathsf N:\quad&\ell(xy)=\ell(x)\ell(y);\\
\mathsf U:\quad&\exists\varepsilon\ \forall x,\quad
\ell(\varepsilon x-x)=\ell(x\varepsilon-x)=0;\\
\mathsf F:\quad&\exists a,b\ \forall c,\quad
\ell(T_{a,b}c)=0\Longrightarrow \ell(c)=0,
\end{aligned}
$$

其中

$$T_{a,b}c=(ab-ba)c+a(bc)-b(ac).$$

$\mathsf{CAL}$ 是本辅助定理的条件，由本稿 $\mathsf G$ 经内生幂变换取得，不增加核心输入； $2u=u+u$ 是原加法中的同一对象自合成。 本节全部 $\ell$ 值在辅助构造中保持；本稿原读出仍为 $p=\ell^\alpha$，不可把这两个函数混同。

证明中必须区分两种实标量作用。原作用始终写作 $tx$。 完成后由有理数极限新构造的连续实作用写作 $r\mathbin\bullet X$。 参数 $t,r$ 都来自通常实数域，但在证明它们作用相同以前，不能交换这两种作用。 所有乘法、零核和读出均保留原值。

### 6.1　同一个原二元乘法抽出标量字符

#### 引理 6.1：单探针决定全体对象的同一标量字符

固定 $\mathsf{CAL}$ 中的 $u$，定义

$$w(t):=\frac{\ell(tu)}{\ell(u)}\qquad(t\in\mathbb R).$$

则

$$\boxed{\ell(tx)=w(t)\ell(x)\qquad(t\in\mathbb R,\ x\in\mathcal A).} \tag{6.1}$$

并且

$$w(st)=w(s)w(t),\quad w(1)=1,\quad w(2)=2,\quad w(0)=0,$$

$$w(-t)=w(t),\qquad w(t)>0\quad(t\ne0).$$

特别地，$\ell(0)=0$、$\ell(-x)=\ell(x)$，且

$$\ell(\pm2^j x)=2^j \ell(x)\qquad(j\in\mathbb Z). \tag{6.2}$$

**证明。**

原实双线性给相同的原乘积

$$(tx)u=x(tu).$$

精确乘性因此给

$$\ell(tx)\ell(u)=\ell(x)\ell(tu).$$

因 $\ell(u)>0$，消去它即得 (6.1)。 将该式用于 $x=tu$，得到 $\ell(stu)=w(s)w(t)\ell(u)$，所以 $w(st)=w(s)w(t)$。 定义给 $w(1)=1$，单次标定给 $w(2)=2$。 由于 $w(0)=w(2)w(0)=2w(0)$，且读数有限，得 $w(0)=0$，进而 $\ell(0)=0$。 又 $w(-1)^2=w(1)=1$，非负性给 $w(-1)=1$，所以 $w$ 偶且 $\ell$ 偶。 对 $t\ne0$，有 $w(t)w(t^{-1})=1$，故 $w(t)>0$。 最后用乘性及逆元得到全部有符号二进比例 (6.2)。

$\square$

此处没有证明 $w(t)=|t|$。后面的域自同构反例说明，仅有一个实域上的乘性绝对值， 即使它固定有理数尺度，也不能在未检查原实轴时直接认作通常绝对值。

### 6.2　二进比例足以恢复准三角和精确原商

#### 引理 6.2：有限二元预算给统一准三角

令 $C=\max\{1,2M\}$，则

$$\ell(x+y)\le C\bigl(\ell(x)+\ell(y)\bigr)\qquad(x,y\in\mathcal A). \tag{6.3}$$

因此，若 $K_n:=C^{\lceil\log_2n\rceil}$，则

$$\ell\!\left(\sum_{j=1}^n z_j\right)\le K_n\sum_{j=1}^n\ell(z_j) \qquad(n\ge1). \tag{6.4}$$

**证明。**

若 $r=\max\{\ell(x),\ell(y)\}>0$，选择整数 $j$ 使 $r\le2^j<2r$。 式 (6.2) 给 $\ell(2^{-j}x),\ell(2^{-j}y)\le1$。 由 $\mathsf{LB}$，

$$\ell(x+y)=2^j \ell(2^{-j}x+2^{-j}y)\le2^jM\le2Mr \le C\bigl(\ell(x)+\ell(y)\bigr).$$

若 $\ell(x)=\ell(y)=0$，则对任意正整数 $j$，$2^jx,2^jy$ 都满足局部界前提； 故 $2^j\ell(x+y)\le M$。令 $j\to\infty$，得 $\ell(x+y)=0$。

式 (6.4) 的证明与引理 4.2 相同： 补零到 $2^{\lceil\log_2n\rceil}$ 项，按平衡二叉树相加，每层只使用一次准三角。 它只依赖向量加法的结合性，没有使用原乘法结合性或全实齐次性。

$\square$

#### 引理 6.3：原实零核、精确陪集读出与非交换见证

令 $N_0=\ell^{-1}(0)$。则 $N_0$ 是原实线性双边理想，并有

$$\boxed{\ell(x+n)=\ell(x)\qquad(x\in\mathcal A,\ n\in N_0).} \tag{6.5}$$

同一原商 $A_0=\mathcal A/N_0$ 的原实作用、原乘法和原读出良定。 其中 $\ell$ 正定、精确乘性，满足式 (6.1)–(6.4)。 $\mathsf U$ 给真正双侧单位 $1=[\varepsilon]$，且 $\ell(1)=1$。 同一原见证 $a,b$ 在商上满足

$$k:=ab-ba\ne0. \tag{6.6}$$

**证明。**

式 (6.1) 使 $N_0$ 对全部原实标量封闭；偶性给负号封闭， 准三角给加法封闭，精确乘性给两侧理想性。 但准三角本身只给 $\ell(x+n)\le C\ell(x)$，还不够直接下降原读出。

对正整数 $j$ 固定一个完全括号的乘法单项式，记为 $x^{[j]}$。 双线性与理想性给

$$(x+n)^{[j]}-x^{[j]}\in N_0.$$

因此

$$\ell(x+n)^j=\ell((x+n)^{[j]})\le C \ell(x^{[j]})=C\ell(x)^j.$$

开 $j$ 次方并令 $j\to\infty$，得 $\ell(x+n)\le \ell(x)$。 对 $x+n$ 和 $-n$ 重复，得到反向不等式，故 (6.5) 成立。 原商上读出精确下降，其他所列性质随之保留。

单位的两份零差在商中分别成为真正等式。 $\mathsf{CAL}$ 使商非零，选择 $\ell(x)>0$，从 $\ell(1)\ell(x)=\ell(1x)=\ell(x)$ 消去 $\ell(x)$，得到 $\ell(1)=1$。 理想性也使 $T_{a,b}$ 良定，$\mathsf F$ 下降为该原商上 $T_{a,b}$ 的单射性。 双侧单位给

$$T_{a,b}1=(ab-ba)+ab-ba=2k.$$

若 $k=0$，则 $T_{a,b}1=0$，单射性迫使 $1=0$，与 $\ell(1)=1$ 矛盾。 所以原商已经含有非交换见证。本步骤没有构造任何完成，也没有扩张 $\mathsf F$ 的量词。

$\square$

### 6.3　先锁定原有理轴，不预设原实轴连续

#### 引理 6.4：整数上界与标量的精确三角

标量字符 $w$ 满足

$$w(n)\le n\qquad(n\in\mathbb Z_{\ge0}),$$

以及

$$w(s+t)\le w(s)+w(t)\qquad(s,t\in\mathbb R). \tag{6.7}$$

**证明。**

将准三角用于 $su,tu$，并消去 $\ell(u)>0$，得

$$w(s+t)\le C\bigl(w(s)+w(t)\bigr).$$

因此 $w$ 也满足常数为 $K_n$ 的平衡加和界。 $n=0,1$ 的上界已经成立。固定整数 $n\ge2$，把 $n^j$ 作二进展开。 最多需要

$$L_j=\lfloor j\log_2n\rfloor+1$$

个二进位。每个非零位的读数是 $w(2^h)=2^h$，于是

$$w(n)^j=w(n^j)\le K_{L_j}n^j.$$

因为 $\log K_{L_j}=O(\log j)$，开 $j$ 次方并令 $j\to\infty$，得到 $w(n)\le n$。

原标量域的乘法结合且交换，故对任意正整数 $j$ 可使用普通有限二项式。 整数系数上界给

$$
\begin{aligned}
w(s+t)^j
&=w\!\left(\sum_{h=0}^j\binom jh s^h t^{j-h}\right)\\
&\le K_{j+1}\sum_{h=0}^j
w\!\left(\binom jh\right)w(s)^h w(t)^{j-h}\\
&\le K_{j+1}\bigl(w(s)+w(t)\bigr)^j.
\end{aligned}
$$

其中零次幂按通常多项式约定处理。 开 $j$ 次方，再用 $K_{j+1}^{1/j}\to1$，得 (6.7)。 这一二项式发生在标量域，不是对尚未证明结合的原代数作非法展开。

$\square$

#### 引理 6.5：全部原有理数的尺度恢复

对每个 $r\in\mathbb Q$，有

$$w(r)=|r|,\qquad \ell(rx)=|r|\ell(x). \tag{6.8}$$

**证明。**

固定整数 $m\ge2$，对每个正整数 $j$ 作整数除法

$$2^j=q_jm+r_j,\qquad 0\le r_j<m.$$

精确标量三角、乘性和整数上界给

$$2^j=w(2^j)\le w(q_j)w(m)+w(r_j)\le q_jw(m)+r_j.$$

除以 $2^j$ 并令 $j\to\infty$。由于 $q_j/2^j\to1/m$，$r_j/2^j\to0$， 得到 $w(m)\ge m$。和上一引理合用，得 $w(m)=m$。 乘法逆和偶性再给全部有理数；最后代回 (6.1)。

$\square$

### 6.4　只从有理作用构造完成

#### 引理 6.6：不使用全实齐次的原读出连续性

若 $\ell(x),\ell(y)\le R$、$R>0$、$\delta=\ell(x-y)$，则对每个正整数 $n$，

$$|\ell(x)-\ell(y)| \le(C^{1/n}-1)R+ \bigl(CnK_nR^{n-1}\delta\bigr)^{1/n}. \tag{6.9}$$

所以原 $\ell$ 在每个 $\ell$ 有界集合上一致连续。

**证明。**

固定一个含 $n$ 个槽的完全括号乘法单项式 $F_n$。 逐槽替换给

$$F_n(x,\ldots,x)-F_n(y,\ldots,y) =\sum_{h=1}^n F_n(y,\ldots,y,x-y,x,\ldots,x).$$

每项的读数由精确乘性至多为 $R^{n-1}\delta$，平衡加和因此给

$$\ell(x^{[n]}-y^{[n]})\le nK_nR^{n-1}\delta.$$

再由准三角与乘性，

$$\ell(x)^n\le C \ell(y)^n+CnK_nR^{n-1}\delta.$$

开 $n$ 次方，使用 $(a+b)^{1/n}\le a^{1/n}+b^{1/n}$，再交换 $x,y$，得到显示式。 给定 $\epsilon>0$，先选一个有限 $n$ 使第一项小于 $\epsilon/2$， 再让 $\delta$ 足够小使第二项小于 $\epsilon/2$。 这与引理 4.5 的证明一致；其实际前提只有双线性、乘性和准三角， 所以没有借用尚待证明的全实齐次。

$\square$

#### 引理 6.7：保留原读出与原乘法的有理 Cauchy 完成

原商 $A_0$ 作为有理代数，等读出稠密嵌入一个非零完备有理代数 $B$。 完成中的 $\ell$ 正定、满足同一准三角、对有理标量绝对一次齐次且精确乘性； $1$ 仍为双侧单位。这里尚不赋予 $B$ 新的实标量作用。

**证明。**

本证明重证引理 4.6 所需的有理版本。 原序列 $(x_n)$ 称为 Cauchy，若 $\ell(x_n-x_m)\to0$。 准三角使这种序列 $\ell$ 有界：固定足够晚的 $x_N$，使用 $\ell(x_n)\le C(\ell(x_N)+\ell(x_n-x_N))$，并补入前面有限项即可。 引理 6.6 使 $\ell(x_n)$ 成为通常实 Cauchy 序列。 规定

$$(x_n)\sim(y_n)\quad\Longleftrightarrow\quad \ell(x_n-y_n)\to0, \qquad \ell([x_n]):=\lim_n \ell(x_n).$$

准三角保证等价关系的传递性，偶性保证对称性。 有界集一致连续性使读出与代表无关；该极限为零当且仅当序列等价于零序列， 所以 $\ell$ 在商 $B$ 上正定。 逐项加法及逐项有理数倍由准三角和 (6.8) 保证良定。

对两个原 Cauchy 序列，双线性给

$$
\begin{aligned}
\ell(x_ny_n-x_my_m)
\le C\bigl(&\ell(x_n-x_m)\ell(y_n)\\
&+\ell(x_m)\ell(y_n-y_m)\bigr).
\end{aligned}
$$

由于两序列有界，乘积序列也 Cauchy。 同一估计保证更换代表不改变乘积；全部有理双线性和单位等式逐项成立。 由

$$\ell([x_n][y_n])=\lim_n \ell(x_n)\ell(y_n)=\ell([x_n])\ell([y_n])$$

得到精确乘性。准三角和有理齐次也直接通过极限保留。

常值序列给 $A_0$ 的等读出嵌入。对 $X=[x_n]$，

$$\ell(X-x_N)=\lim_{n\to\infty}\ell(x_n-x_N)\longrightarrow0\qquad(N\to\infty),$$

所以原商稠密。若 $(X_j)$ 是 $B$ 中的 Cauchy 序列，由稠密性选 $a_j\in A_0$， 使 $\ell(X_j-a_j)<1/j$。平衡三项界给

$$\ell(a_j-a_k)\le K_3\bigl(1/j+\ell(X_j-X_k)+1/k\bigr),$$

故 $(a_j)$ 是原商中的 Cauchy 序列。 令 $X=[a_j]$，则 $\ell(a_j-X)\to0$，再由准三角得 $\ell(X_j-X)\to0$。 这证明完备性。

引理 6.6 的有限代数证明在 $B$ 上同样有效。 加法连续由准三角给出；乘法的连续性由前述乘积差界及有界性给出。 所有构造仅使用有理标量的通常齐次，没有预设原实参数 $t\mapsto tx$ 连续。

$\square$

### 6.5　新连续实作用与内积化只在辅助完成上发生

#### 引理 6.8：由有理极限唯一构造的连续实作用

对通常实数 $r$、$X\in B$，取任意有理序列 $r_n\to r$，定义

$$r\mathbin\bullet X:=\lim_n r_n X. \tag{6.10}$$

该定义与序列无关，使 $B$ 成为完备实向量空间，并满足

$$\ell(r\mathbin\bullet X)=|r|\ell(X).$$

原乘法在此新作用下实双线性，读出、加法、乘法和单位均未改变。

**证明。**

有理齐次给

$$\ell(r_nX-r_mX)=|r_n-r_m|\ell(X),$$

所以 $(r_nX)$ 为 Cauchy。若 $s_n\to r$ 也是有理序列，则 $\ell(r_nX-s_nX)=|r_n-s_n|\ell(X)\to0$，故极限与选择无关。 由读出连续性，

$$\ell(r\mathbin\bullet X)=\lim_n|r_n|\ell(X)=|r|\ell(X).$$

向量加法连续，故 $(r+s)\mathbin\bullet X=r\mathbin\bullet X+s\mathbin\bullet X$ 及 $r\mathbin\bullet(X+Y)=r\mathbin\bullet X+r\mathbin\bullet Y$ 可由有理恒等式取极限。 单位作用也直接成立。为核查标量乘法结合律，取有理 $r_n\to r$、$s_n\to s$。 因 $r_n$ 有界，

$$\ell\bigl(r_n(s_nX)-r_n(s\mathbin\bullet X)\bigr) =|r_n|\ell(s_nX-s\mathbin\bullet X)\longrightarrow0.$$

右侧序列 $r_n(s\mathbin\bullet X)$ 趋于 $r\mathbin\bullet(s\mathbin\bullet X)$， 而 $r_ns_n\to rs$ 使左侧序列 $(r_ns_n)X$ 趋于 $(rs)\mathbin\bullet X$。 正定性和准三角使极限唯一，因此两者相同。

实双线性来自乘法连续性与有理双线性，例如

$$(r\mathbin\bullet X)Y =\lim_n(r_nX)Y =\lim_n r_n(XY) =r\mathbin\bullet(XY).$$

另一槽同理。此时新实标量的联合连续性可由

$$\ell(r\mathbin\bullet X-s\mathbin\bullet Y) \le C\bigl(|r|\ell(X-Y)+|r-s|\ell(Y)\bigr)$$

直接得到。原 Cauchy 条件与完备性只由 $\ell$ 决定，因而没有改变。

$\square$

#### 引理 6.9：辅助完成的原读出成为内积范数

在 $(B,\mathbin\bullet)$ 上，同一个 $\ell$ 满足普通三角和平行四边形恒等式。 因此

$$B_0(X,Y):=\frac14\bigl(\ell(X+Y)^2-\ell(X-Y)^2\bigr)$$

为针对新实作用 $\mathbin\bullet$ 的正定实内积，$B_0(X,X)=\ell(X)^2$。

**证明。**

现在才具备通常实齐次的全部前提： $(B,\mathbin\bullet)$ 非零且完备，$\ell$ 正定、绝对一次齐次并满足统一准三角， 乘法对此新实作用双线性且精确乘性，并有双侧单位。 因此可在该辅助实结构上使用引理 4.7、 引理 4.8 和定理 4.9 的证明， 得到全部非零左乘为满射相似和普通三角不等式。 这些结论只需左单位，不使用 $\mathsf F$。

为显式核查这里的类型，左乘和算子线性均相对于 $\mathbin\bullet$。 满射性证明中的穿孔空间路径是 $r\mapsto (1-r)\mathbin\bullet X+r\mathbin\bullet Y$， 其连续性来自上一引理，未使用原实作用的连续性。 普通三角恢复中的有限算子二项式只用有理系数及同一准三角，故无额外输入。

随后定理 5.3 给：对每个 $X,Y$、$Y\ne0$，存在同一个复数 $\lambda$，使

$$\ell(\alpha\mathbin\bullet X+\beta\mathbin\bullet Y)^2 =\ell(Y)^2|\alpha\lambda+\beta|^2 \qquad(\alpha,\beta\in\mathbb R).$$

因而 $\ell$ 满足平行四边形恒等式。 引理 5.4 对新实作用极化，得到所述 $B_0$。 谱证明使用的复化只作分析辅助；它没有改变原乘法或预设原物理复标量。

$\square$

### 6.6　非交换比较把原实轴锁回唯一的单位轴

#### 引理 6.10：内积乘性中的纯方向反交换

记 $Q(X)=\ell(X)^2$，$W=\{X:B_0(1,X)=0\}$。 对 $V,U\in W$，有

$$V^2=-Q(V)\mathbin\bullet1,\qquad VU+UV=-2B_0(V,U)\mathbin\bullet1.$$

**证明。**

由双侧单位及 $\ell(1)=1$，对 $V\in W$ 比较

$$Q((1+s\mathbin\bullet V)Y)=Q(1+s\mathbin\bullet V)Q(Y)$$

关于通常实参数 $s$ 的一次项，得到 $B_0(Y,VY)=0$。 对 $Y$ 极化可得

$$B_0(VY,Z)=-B_0(Y,VZ).$$

另一方面，对精确乘性 $Q(VY)=Q(V)Q(Y)$ 关于 $Y$ 极化，得到

$$B_0(VY,VZ)=Q(V)B_0(Y,Z).$$

合并两式，

$$B_0(V(VY),Z)=-Q(V)B_0(Y,Z).$$

正定性消去配对，给 $L_V^2=-Q(V)I$；作用于单位即得 $V^2=-Q(V)\mathbin\bullet1$。 再对 $V+U$ 使用同一平方关系，利用双线性及内积展开，得到反交换公式。 这里不要求有限维、预给结合律或任何分类定理。

$\square$

#### 引理 6.11：非交换幺内积乘性代数只有一条全体交换轴

设 $B$ 不交换，则

$$\{Z\in B:\ ZX=XZ\text{ 对所有 }X\in B\} =\mathbb R\mathbin\bullet1. \tag{6.11}$$

这里左侧仅指和全部元素交换，不另外要求非结合代数中心的结合子条件。

**证明。**

写 $Z=r\mathbin\bullet1+V$，其中 $V\in W$。 若 $Z$ 和全部元素交换，则 $V$ 也和全部元素交换。 不交换性使 $\dim_{\mathbb R}W\ge2$：若维数至多一，整个代数是 $1$ 和至多一个纯方向的实线性张成， 单位律与双线性会使所有元素交换。

若 $V\ne0$，选择不与 $V$ 成比例的 $W_1\in W$，并令

$$U=W_1-\frac{B_0(W_1,V)}{Q(V)}\mathbin\bullet V.$$

则 $U\in W$、$U\ne0$、$B_0(U,V)=0$。 上一引理给 $UV+VU=0$，而 $V$ 的全体交换性给 $UV=VU$，所以 $UV=0$。 精确乘性却给 $\ell(UV)=\ell(U)\ell(V)>0$，矛盾。 故 $V=0$。反向包含由双侧单位和新实双线性立即成立。

$\square$

#### 定理 6.12：单次自合成标定恢复全部原实齐次

在本节列出的六组原条件下，

$$\boxed{\ell(tx)=|t|\ell(x)\qquad(t\in\mathbb R,\ x\in\mathcal A).} \tag{6.12}$$

同一个原 $\ell$ 还满足普通三角和平行四边形恒等式； 其极化为原实半正双线性型，零根基恰为 $N_0$。 原商嵌入完成后，原实作用与新作用相同：

$$tx=t\mathbin\bullet x\qquad(t\in\mathbb R,\ x\in A_0). \tag{6.13}$$

**证明。**

原商中的非交换见证由引理 6.3 给出，并由等读出嵌入保留在 $B$ 中。 故辅助完成满足引理 6.11 的不交换前提。

对每个 *原* 实数 $t$，取原商中已经存在的元素

$$z_t:=t1\in A_0\subset B.$$

原实双线性及原双侧单位给

$$z_tx=(t1)x=tx=x(t1)=xz_t\qquad(x\in A_0).$$

由于 $A_0$ 稠密，乘法连续，$z_t$ 也和全部 $X\in B$ 交换。 具体地，若 $x_n\to X$，普通三角及乘性给

$$\ell(z_tX-Xz_t) \le \ell(z_t)\ell(X-x_n)+\ell(x_n-X)\ell(z_t)\longrightarrow0.$$

正定性使交换子为零。这里对每个固定 $t$ 只用了 $\ell(z_t)<\infty$， 没有假定原实参数 $t$ 的连续性。

由引理 6.11，存在唯一通常实数 $\rho(t)$，使

$$z_t=\rho(t)\mathbin\bullet1.$$

原实作用与乘法给

$$z_{s+t}=z_s+z_t,\qquad z_{st}=z_sz_t,\qquad z_1=1.$$

新实双线性及 $\ell(1)=1$ 因而给

$$\rho(s+t)=\rho(s)+\rho(t),\quad \rho(st)=\rho(s)\rho(t),\quad \rho(1)=1.$$

所以 $\rho:\mathbb R\to\mathbb R$ 是含幺域同态；它固定有理数。 若 $t>0$，原实数域中存在非零 $v$ 使 $t=v^2$。 域同态的单射性给 $\rho(v)\ne0$，于是

$$\rho(t)=\rho(v)^2>0.$$

故 $\rho$ 严格保序。若 $\rho(t)>t$，在两者间选一个有理数 $r$， 则 $t<r$ 给 $\rho(t)<\rho(r)=r$，与 $r<\rho(t)$ 矛盾。 $\rho(t)<t$ 同理排除。因此 $\rho(t)=t$ 对所有原实数成立。

最后对原商中的 $x$，

$$tx=z_tx=(t\mathbin\bullet1)x=t\mathbin\bullet x.$$

这证明 (6.13)；新实齐次继而给原商上的 (6.12)。 由精确陪集读出 (6.5) 拉回原 $\mathcal A$，得到同一原 $\ell$ 的全部实齐次。 普通三角、平行四边形及内积都已在 $B$ 上成立，现可按相同原实作用限制回 $A_0$， 再拉回 $\mathcal A$。原极化的根基恰为原零核，因为商内积正定。

$\square$

#### 推论 6.13：恢复原条件后的分类接口

本辅助定理的 $\ell$ 标定背景恢复 $\Omega Q\text{-}022$ 的全部原条件。 因此同一原商、原乘法与规范读出满足

$$(A_0,m,\ell)\cong(\mathbb H,\cdot,|\cdot|).$$

原见证对的三元投影与复二维表示证明全部适用。 辅助完成没有增加最终可读方向：$A_0=B$。

**证明。**

定理 6.12 恢复原全实齐次；$\mathsf{LB},\mathsf N,\mathsf U,\mathsf F$ 原样保留，$\mathsf{CAL}$ 给非零。 在原商上使用后文完整证明的同一对投影恒等式

$$T_{a,b}=2L_kP_H,\qquad \ker T_{a,b}=H^\perp,$$

其中 $H$ 是该对生成的四维四元数子代数。 原 $\mathsf F$ 只在 $A_0$ 上使用，迫使 $H^\perp=0$，所以原商恰为 $H$。 最后有限维 Euclidean 空间 $A_0$ 完备，它在 $B$ 中的等距像因此闭合； 该像又稠密，所以 $A_0=B$。这一步不能移到分类之前当作前提。

$\square$

本稿原实尺度恢复确实使用了 $\mathsf F$ 所产生的非交换见证。 “范数与内积恢复不使用 $\mathsf F$”仅指引理 6.9 中已经具有新连续实作用的辅助空间；不能把这一依赖说明误写成原实尺度也无需非交换关系。 全过程没有把 $\mathsf F$ 延拓到 $B$。

### 6.7　严格背景弱化与三种删项反例

#### 反例 6.14：一个标定加有限预算严格弱于全实齐次背景

在原 $\mathbb R^2$ 上取

$$\ell(s,t)=|s|+t^2.$$

它连续、正定，满足 $\mathsf{CAL}$ 和 $\mathsf{LB}$，但不满足全实绝对一次齐次。

**证明。**

取 $u=(1,0)$，有 $\ell(u)=1$、$\ell(2u)=2$。 对 $x=(s,t)$、$y=(r,v)$，

$$\ell(x+y)=|s+r|+(t+v)^2 \le |s|+|r|+2t^2+2v^2 \le2\bigl(\ell(x)+\ell(y)\bigr).$$

所以单位输入局部界可取 $M=4$。 但对 $e=(0,1)$，有 $\ell(2e)=4\ne2\ell(e)=2$。 这仅比较读出背景，没有声称此例配备了满足其他乘法条件的原乘法。

$\square$

旧非零及全实齐次显然推出某个非零探针的 $\mathsf{CAL}$；上述例子排除背景反向蕴含。 加入本辅助定理的 $\ell$ 标定背景其余条件后，定理 6.12 又恢复旧齐次，因此这一标定辅助背景的完整模型类等价。 本轮主候选的原 $p$ 则允许全部 $\alpha>0$，不能与该辅助模型类混同。 真正弱化的是输入的量词与内容，而不是将若干条件重命名为一行。

#### 反例 6.15：删去单次标定：读出幂指数不被固定

在标准四元数 $\mathbb H$ 上，对任意 $\beta>0$ 定义

$$\ell_\beta(x)=|x|^\beta.$$

原实双线性、非零、精确乘性、双侧单位、有限单位输入预算及同对忠实条件全部成立。 但 $\beta\ne1$ 时不满足单次标定，也不恢复通常实齐次。

**证明。**

除读出外保留通常四元数运算。乘性来自标准四元数范数。 $\ell_\beta(x),\ell_\beta(y)\le1$ 意味着 $|x|,|y|\le1$，故 $\ell_\beta(x+y)\le2^\beta$，给 $\mathsf{LB}$。 单位 $1$ 真正双侧成立，且 $\ell_\beta(1)=1$。 取同一对 $a=i,b=j$，由结合性，

$$T_{i,j}c=4kc.$$

它的零核为零，所以 $\mathsf F$ 成立。 对于任意 $u\ne0$，

$$\ell_\beta(2u)=2^\beta \ell_\beta(u).$$

因此存在非零探针满足 $\ell_\beta(2u)=2\ell_\beta(u)$ 当且仅当 $\beta=1$。

还可以取纯存在读出 $\ell(0)=0$、$\ell(x)=1$ 对 $x\ne0$。 四元数无零因子使它精确乘性，$\mathsf{LB}$ 可取 $M=1$，单位及同对忠实仍成立； 所有非零对象的自合成却保持读数 $1$，无法满足单次翻倍标定。

$\square$

#### 反例 6.16：删去非交换忠实：固定有理尺度仍可扭曲原实轴

存在原通常实向量空间 $\mathcal A=\mathbb C$ 上的正定函数 $\ell$， 它满足普通三角、精确乘性、双侧单位、$\mathsf{CAL}$ 和 $\mathsf{LB}$， 但不满足原实绝对一次齐次。 此例中的所有 $T_{a,b}$ 为零，故 $\mathsf F$ 不成立。

**证明。**

选择一个超越实数 $t>1$，将 $\{t\}$ 扩充为 $\mathbb C/\mathbb Q$ 的超越基 $\mathcal T$。 令

$$\mathcal T'=(\mathcal T\setminus\{t\})\cup\{t^2\}.$$

它仍为超越基。事实上，若其有限子集满足一个非零有理多项式关系， 将相应变量替换为 $t^2$ 会得到原超越基的非零多项式关系，矛盾； 而 $t$ 在 $\mathbb Q(\mathcal T')$ 上满足 $X^2-t^2=0$， 故 $\mathbb Q(\mathcal T)$ 在 $\mathbb Q(\mathcal T')$ 上代数， 继而 $\mathbb C$ 在 $\mathbb Q(\mathcal T')$ 上代数。

自由生成元替换给域同构

$$\varphi:\mathbb Q(\mathcal T)\longrightarrow\mathbb Q(\mathcal T'), \qquad \varphi(t)=t^2,$$

其余超越基元固定。 两侧的 $\mathbb C$ 都是相应基础域的代数闭包：它代数、代数闭且包含该基础域。 代数闭包延拓定理因此将 $\varphi$ 延拓为域同构

$$\sigma:\mathbb C\longrightarrow\mathbb C, \qquad \sigma(t)=t^2.$$

这里确为满射：延拓像是代数闭子域，包含 $\mathbb Q(\mathcal T')$； 整个目标 $\mathbb C$ 在它上代数，故不可能再有真代数扩张。 这一构造使用通常集合论中的超越基与代数闭包延拓，不主张连续或可计算。

保留 $\mathbb C$ 的原通常实向量结构与原通常复乘法，定义

$$\ell(z)=|\sigma(z)|.$$

由于 $\sigma$ 加法、乘法保持且为单射，$\ell$ 正定、满足普通三角及精确乘性。 单位 $1$ 真正双侧成立，$\ell(1)=1$。 域同构固定有理数，故 $\ell(2)=2$，以 $u=1$ 得 $\mathsf{CAL}$；普通三角给 $\mathsf{LB}$，可取 $M=2$。 然而对原实数 $t$，

$$\ell(t\cdot1)=|\sigma(t)|=t^2\ne t=|t|\ell(1).$$

因此原实齐次失败。 原复乘法交换且结合，所以对全部 $a,b,c$ 有 $T_{a,b}c=0$。 由于 $\ell(1)=1$，$\mathsf F$ 失败。 此例准确表明：从本稿局部界和单次标定回到原实轴时，不能省略产生非交换约束的那一步。

$\square$

#### 反例 6.17：删去共同有限预算：高阶读出可被相消任意放大

取中央不定元 $\tau$ 的四元数多项式代数 $\mathbb H[\tau]$。 若非零 $f$ 的最低非零系数为 $a_m$，定义

$$f(\tau)=\sum_{j=m}^n a_j\tau^j,\quad a_m\ne0, \qquad \ell(f)=|a_m|,\qquad \ell(0)=0.$$

该例满足原双线性、$\mathsf{CAL},\mathsf N,\mathsf U,\mathsf F$， 但不满足 $\mathsf{LB}$，原可读商也不是 $\mathbb H$。

**证明。**

该代数结合、实双线性、有双侧单位，$\ell$ 正定且对原实标量绝对一次齐次。 因而 $\ell(2\cdot1)=2\ell(1)=2$，单次标定成立。 若 $g$ 的最低非零系数为 $b_\ell$，则 $fg$ 的最低非零系数是 $a_mb_\ell$； 四元数无零因子及范数乘性给 $\ell(fg)=\ell(f)\ell(g)$。 取原常数多项式 $a=i,b=j$，有 $T_{i,j}c=4kc$，故 $\ell(T_{i,j}c)=4\ell(c)$，同对忠实成立。

对任意 $R>0$，取 $f_R=1+R\tau$、$g=-1$。则

$$\ell(f_R)=\ell(g)=1,\qquad \ell(f_R+g)=\ell(R\tau)=R.$$

因此共同有限预算不存在。 这里零核为零，原商仍是无限维 $\mathbb H[\tau]$，不可能为四元数代数。

$\square$

这些反例分别检查具体删除项的数学后果，并不声称已经证明所有命名条件组相互独立。 相对上一轮，单次标定确实取代了全体原实比例的统一齐次输入； 单位、乘性、有限合成预算及同对忠实仍是明确保留的约束。

<a id="section-7"></a>

## 7　同一对比较的三元闭合及四元数分类

前节定标引理已对 $\ell$ 恢复原实绝对齐次、普通三角不等式与半正二次型 $q=\ell^2$。这里完成该辅助引理的分类；本轮原 $p$ 的分类由 $p=\ell^\alpha$ 返回。以下始终在原商 $A=\mathcal A/N$ 上工作，不向辅助完成延伸 $\mathsf F$。全部使用的投影恒等式在此重新证明。

#### 引理 7.1：忠实合成自动产生同一对非交换见证

候选中的同一对 $a,b$ 必满足 $q(k_{a,b})>0$。

**证明。**

在正定商中，单位律给

$$T_{a,b}(1)=(ab-ba)+ab-ba=2k_{a,b}.$$

若 $q(k_{a,b})=0$，则 $q(T_{a,b}(1))=0$，忠实性迫使 $q(1)=0$， 与 $q(1)=1$ 矛盾。 这也说明原 $q$ 非零不可删除，否则 $\mathsf F$ 会真空成立。

$\square$

### 7.1　只由单位与乘性恢复的代数恒等式

以下在任意非零实正内积空间 $A$ 上工作，乘法双线性且有单位 $1$， 满足 $q(xy)=q(x)q(y)$。仍不假定有限维或结合性。 令

$$L_x(y):=xy,\quad R_x(y):=yx,\quad t(x):=B(1,x),\quad \bar x:=2t(x)1-x,\quad W:=1^\perp.$$

#### 引理 7.2：共轭、交替性与纯方向 Clifford 关系

对全部 $x,y,z\in A$，

$$B(xy,z)=B(y,\bar xz),\quad B(yx,z)=B(y,z\bar x),$$

$$L_{\bar x}L_x=L_xL_{\bar x}=q(x)I,\qquad R_{\bar x}R_x=R_xR_{\bar x}=q(x)I,$$

$$x^2-2t(x)x+q(x)1=0,\qquad L_x^2=L_{x^2},\quad R_x^2=R_{x^2}.$$

对 $x,y\in W$，

$$x^2=-q(x)1,\quad xy+yx=-2B(x,y)1,$$

$$L_x^2=-q(x)I,\qquad L_xL_y+L_yL_x=-2B(x,y)I.$$

**证明。**

单位非零且 $q(1)=q(1)^2$，故 $q(1)=1$。 比较 $q((1+sx)y)=q(1+sx)q(y)$ 关于 $s$ 的一次项，再对 $y$ 极化， 得 $B(xy,z)=B(y,(2t(x)1-x)z)$。右槽同理。 极化 $q(xy)=q(x)q(y)$ 得 $B(xy,xz)=q(x)B(y,z)$。 与配对伴随合用并由正定性消去配对，得 $L_{\bar x}L_x=q(x)I$。 由于 $L_{\bar x}=2t(x)I-L_x$，两个左乘算子交换；右乘同理。 所以 $L_x^2-2t(x)L_x+q(x)I=0$。作用于单位给元素二次式， 将该元素式左乘线性化即得 $L_x^2=L_{x^2}$；右式相同。 纯方向有 $t(x)=0$；分别将其元素平方和左乘平方对 $x+y$ 极化，即得所列反交换关系。 全程伴随均以显式配对给出，没有调用有限维 Riesz 表示。

$\square$

### 7.2　主恒等式：合成读出本来就是内部四维投影

#### 定理 7.3：单对内生投影与反射公式

在上节背景中，给定任意不交换对 $a,b$，令

$$k=ab-ba,\qquad M=[L_a,L_b],\qquad T=L_k+M, \qquad \mathscr A_{a,b}=L_{ab}-L_aL_b.$$

则由同一对内生生成一个四维四元数子代数 $H$，其正交投影 $P$ 与补投影 $Q=I-P$ 满足

$$\boxed{M=L_k(2P-I),\quad T=2L_kP,\quad\mathscr A_{a,b}=L_kQ.}$$

特别地，

$$\boxed{P=-\frac{L_kT}{2q(k)},\qquad P(c)=-\frac{k\,\bigl(kc+a(bc)-b(ac)\bigr)}{2q(k)}.}$$

每个括号均如式中所写。这个公式由原乘法、实标量与原读数在同一可读商上下降得到。

$$\operatorname{ran}T=H,\qquad \ker T=H^\perp, \qquad\operatorname{rank}_{\mathbb R}T=4.$$

算子 $K:=2P-I$ 为正交自伴反射；$K=+I$ 于 $H$，$K=-I$ 于 $H^\perp$。

**证明。**

写 $a=\alpha1+x$、$b=\beta1+y$，其中 $x,y\in W$。 若 $x,y$ 线性相关，则 $a,b$ 交换，故两纯部独立。 Gram–Schmidt 给正交单位纯方向 $u,v$ 及 $r,h>0$、$s\in\mathbb R$，使

$$a=\alpha1+ru,\qquad b=\beta1+su+hv.$$

令 $w=uv$。配对恒等式与乘性给 $q(w)=1$ 及 $w\perp1,u,v$。 由左右交替性和纯方向反交换，

$$u^2=v^2=w^2=-1,\quad uv=w=-vu,\quad uw=-v,\quad wu=v,\quad wv=-u,\quad vw=u.$$

因此 $H=\operatorname{span}\{1,u,v,w\}$ 为四维四元数子代数。 此处只建立 $H$ 内的乘法表，未把 $L_uL_v$ 误认作整个 $A$ 上的 $L_w$。

定义整个 $A$ 上的算子

$$K:=-L_wL_uL_v.$$

三个纯方向左乘平方均为 $-I$，且两两反交换。 因此 $K$ 与 $L_u,L_v,L_w$ 分别交换。 又

$$K1=-w(uv)=-w^2=1,$$

故 $K$ 在 $1,u,v,w$ 上均为恒等，因而在 $H$ 上为 $+I$。

若 $z\perp H$，则 $z\in W$ 且 $L_z$ 与 $L_u,L_v,L_w$ 分别反交换。 三次翻号给

$$KL_z=-L_zK.$$

作用于单位便得 $Kz=-z$。 任意 $c\in A$ 都可减去在这四个正交单位向量上的有限投影，故 $A=H\oplus H^\perp$，不需预给维数或完备性。 显式地，$P(c)=B(1,c)1+B(u,c)u+B(v,c)v+B(w,c)w$。 所以 $K=2P-I$，它是正交自伴反射。

左乘 $L_w$ 于 $K=-L_wL_uL_v$ 得

$$L_uL_v=L_wK.$$

双线性展开给

$$k=2rh\,w,\qquad M=rh[L_u,L_v]=2rhL_uL_v=L_kK.$$

因此 $T=L_k(I+K)=2L_kP$。 再令 $F(x,y)=L_xL_y-L_{xy}$。 它双线性，$F(1,y)=F(x,1)=F(x,x)=0$，所以

$$\mathscr A_{a,b}=-F(a,b) =-rh(L_uL_v-L_w) =rhL_w(I-K)=L_kQ.$$

$k$ 为纯方向且 $q(k)>0$，故 $L_k^2=-q(k)I$， 给出显示的内生投影公式。 $L_k$ 可逆并保持 $H$ 和 $H^\perp$（因 $K$ 与 $L_w$ 交换）， 所以 $\operatorname{ran}T=H$、$\ker T=H^\perp$，秩恰为四。

$\square$

#### 推论 7.4：二元响应的精确正分解

对所有 $c,d\in A$，

$$q(Tc)=4q(k)q(Pc),\qquad q(\mathscr A_{a,b}c)=q(k)q(Qc),$$

$$B(Tc,\mathscr A_{a,b}d)=0,$$

$$\boxed{q(Tc)+4q(\mathscr A_{a,b}c)=4q(k)q(c).}$$

两条被比较的响应 $X=L_k$、$Y=M$ 有同样预算：

$$q(Xc)=q(Yc)=q(k)q(c).$$

其中 $Yc=Xc$ 在 $H$ 上成立，而 $Yc=-Xc$ 在 $H^\perp$ 上成立。

**证明。**

使用 $T=2L_kP$、$\mathscr A=L_kQ$、$M=L_kK$，以及 $B(L_kx,L_ky)=q(k)B(x,y)$、$P\perp Q$ 即得。

$\square$

**图示（文字版）。** 同一第三元 $c=Pc+Qc$ 分为两条正交支路：经 $P$ 得到 $Pc\in H$，再由同向的两份响应得到 $Tc=2L_kPc$；经 $Q=I-P$ 得到 $Qc\in H^\perp$，两份响应在合读中反向抵消，而结合缺口给出 $\mathscr A c=L_kQc$。

**图 2。** 同一第三元的正交分解。上支由合读 $T$ 读出；下支在合读中抵消，由结合缺口 $\mathscr A$ 精确读出。忠实条件排除下支中的非零可读元。

#### 定理 7.5：一对忠实合成的完整定标分类

在本辅助定理的实双线性、有限局部合成及精确定标背景中，$\mathsf N+\mathsf U_q+\mathsf F$ 成立， 当且仅当 $N=q^{-1}(0)$ 为双边理想，且由同一原乘法与同一原读数下降得到的 $\mathcal A/N$ 等距代数同构于标准四元数 $\mathbb H$。 此时原候选对已经不交换，商上的全部三元精确结合，原层全部结合缺口具有零读数。

**证明。**

正向，前节的原商、原标量、三角与内积恢复给非零正定幺商，$\mathsf F$ 下降为 $T$ 的单射性。 在单位上计算 $T1=2k$，故 $k\ne0$，投影定理可用。 但 $\ker T=H^\perp$，因此 $H^\perp=0$，全部商就是四维 $H$。 全局商结合性及原层零结合缺口随即成立。

反向，若同一商等距同构于 $\mathbb H$，选择 $1,i,j$ 的原代表作为 $\varepsilon,a,b$。 四元数范数给乘性，可读单位成立且读数非零。 结合性给 $T(c)=2k c$，其中 $k=2k_{\mathbb H}$ 非零。 所以 $q(Tc)=4q(k)q(c)$，得到原层忠实条件。

$\square$

#### 推论 7.6：新产生的过程也满足有限二元、三元闭合

在内生投影定理的背景中，

$$T^2=-4q(k)P,\quad T^3=-4q(k)T,\qquad \mathscr A_{a,b}^2=-q(k)Q,\quad \mathscr A_{a,b}^3=-q(k)\mathscr A_{a,b}.$$

定义 $J:=T/(2\sqrt{q(k)})$，则

$$J^2=-P,\qquad J^3=-J,\qquad J^*J=P.$$

若候选忠实条件成立，则 $P=I$，故

$$J^2=-I,\qquad J^*=-J,\qquad J^*J=I.$$

并且原层任意二元差满足

$$\boxed{q(Tx-Ty)=4q(k)q(x-y).}$$

**证明。**

$P,Q$ 与 $L_k$ 交换，而 $L_k^2=-q(k)I$，故各算子乘积直接得出。 忠实性给 $P=I$。最后把尺度公式应用于 $x-y$，并使用 $T$ 的原实线性性。

$\square$

#### 命题 7.7：由同一对内生的复二维表示

在正定可读商中，忠实比较给出的 $J$ 定义复标量作用

$$(s+it)x:=sx+tJx.$$

若约定第二槽复线性，则

$$h(x,y):=B(x,y)+iB(Jx,y)$$

是正定 Hermitian 内积，$h(x,x)=q(x)$，且 $\dim_{\mathbb C}A=2$。

**证明。**

$J^2=-I$ 保证复标量乘法律。$`J^*=-J`$ 给共轭对称性；

$$h(x,Jy)=B(x,Jy)+iB(Jx,Jy) =-B(Jx,y)+iB(x,y)=i h(x,y).$$

实双线性性给其余标量律。$B(Jx,x)=0$，所以 $h(x,x)=q(x)>0$ 对非零 $x$ 成立。 实维四意味着复维二。

$\square$

这个 $J$ 是原左乘 $L_{k/\sqrt{q(k)}}$。 若把 $J$ 用作复标量，$e^{tJ}$ 就是该复结构的相位圆，射影化后作用为恒等；不能同时称其为必然的可观测时钟。 下文统一采用此处的左复标量约定；实际可转向的酉作用由与之交换的右乘给出。

#### 推论 7.8：存在、反向与逆的正读数

在该可读商中，每个 $x\ne0$ 都有双侧逆

$$x^{-1}=\frac{\bar x}{q(x)},\qquad q(x^{-1})=\frac1{q(x)}>0,\qquad q(-x)=q(x)>0.$$

因此按 $q(x)>0$ 定义可读存在时，反向和取逆都不产生负存在； 取逆是非零可读元素集合上的对合双射。

**证明。**

元素二次式给 $x\bar x=\bar x x=q(x)1$， 而 $q(\bar x)=q(x)$ 由共轭定义与极化直接得到。 结合性给显示的双侧逆；平方齐次性给其读数和 $q(-x)=q(x)$。 逆的唯一性给 $(x^{-1})^{-1}=x$。

$\square$

<a id="section-8"></a>

## 8　反向检查：增长方向、非离散读出与有限合成预算

本节保留同一个原签名。反例分别检查具体弱化， 不把它们写成全部命名条件组已经相互独立的证明。 特别要区别 $d<1$、$d=1$ 与 $d>1$ 三种自合成响应。

### 8.1　零倍率已经被乘法排除，下降倍率没有被局部界排除

#### 引理 8.1：非零探针的自合成倍率不能为零

仅用原实双线性、精确乘性和某个 $p(u)>0$，就能定义与探针无关的 $w(t)=p(tu)/p(u)$，满足 $p(tx)=w(t)p(x)$ 和 $w(st)=w(s)w(t)$。 因此

$$d=w(2)>0.$$

这一结论不使用增长方向或有限局部界。

**证明。**

重复等式 $(tx)u=x(tu)$ 的乘性读出并消去 $p(u)>0$，即可得到字符及其乘性。 由于 $w(1)=1$，有 $w(2)w(1/2)=1$。 两数有限非负，所以 $w(2)>0$。

$\square$

接下来的完整反例表明，$0<d<1$ 确实可能和其余关系条件同时成立。 因此把 $p(2u)>p(u)$ 改成 $p(2u)\ne p(u)$ 会失去本轮结论。

#### 引理 8.2：通常实数域上存在下降的非 Archimedean 绝对值

存在一个有限函数 $v:\mathbb R\to[0,\infty)$，满足

$$v(t)=0\Longleftrightarrow t=0,\quad v(st)=v(s)v(t),\quad v(s+t)\le\max\{v(s),v(t)\},$$

并且 $v(2)=1/2$。 这里的实数域保留通常代数结构，但不要求 $v$ 对原通常实拓扑连续。

**证明。**

选择 $\mathbb R/\mathbb Q$ 的一个超越基 $\mathcal T$。 在有限支撑的交换多项式环 $\mathbb Q[\mathcal T]$ 上定义 Gauss 绝对值

$$v_G\!\left(\sum_\nu a_\nu\mathcal T^\nu\right) :=\max_\nu |a_\nu|_2,$$

其中 $|\cdot|_2$ 为通常 $2$-adic 绝对值，$|2|_2=1/2$。 每个多项式只使用超越基的有限子集。 加法的强三角直接按系数成立。 为证乘性，对两个非零多项式分别除以一个达到最大绝对值的系数， 使全部系数位于 $2$-adic 单位球，且至少一个系数为单位。 约化到 $\mathbb F_2[\mathcal T]$ 后，二者都是非零多项式，其乘积非零。 故规范后乘积至少有一个单位系数，同时所有系数都在单位球内，Gauss 值恰为 $1$。 乘回两份系数即得精确乘性。

于是 $v_G(f/g)=v_G(f)/v_G(g)$ 良定，给 $K=\mathbb Q(\mathcal T)$ 一个非 Archimedean 绝对值。 超越基的定义保证 $\mathbb R/K$ 为代数扩张。 绝对值的代数扩张存在定理给一个延拓 $v$ 到 $\mathbb R$。 该标准定理适用于非完备的基础域；一种证明是先完成 $K$， 将绝对值延拓到完成域的代数闭包，再把代数扩张 $\mathbb R/K$ 嵌入其中并拉回。 这里准确使用的是该数学延拓定理，不是主候选中的任何新条件。[\[14\]](#ref-conrad_absolutevalues)

该延拓固定 $2$-adic 有理读数，所以 $v(2)=1/2$，且 $v(n)\le1$ 对全部整数成立。 为核查强三角，对任意 $s,t$ 和正整数 $n$，普通三角及有限标量二项式给

$$v(s+t)^n \le\sum_{j=0}^n v\!\left(\binom nj\right)v(s)^jv(t)^{n-j} \le(n+1)\max\{v(s),v(t)\}^n.$$

开 $n$ 次方并令 $n\to\infty$，得到所需强三角。 正定性、有限性和精确乘性均属于延拓绝对值的性质。

$\square$

#### 引理 8.3：非交换自由多项式的 Gauss 读出精确乘性

设 $F$ 为带非 Archimedean 绝对值 $v$ 的域。 在非交换自由多项式代数 $F\langle X,Y\rangle$ 上定义

$$P\!\left(\sum_w a_w w\right)=\max_w v(a_w),\qquad P(0)=0,$$

其中 $w$ 遍历有限字，和只有有限项。 则 $P$ 正定、满足强三角，并且

$$P(fg)=P(f)P(g).$$

**证明。**

正定性及加法强三角逐系数成立。 记 $\mathcal O=\{a:v(a)\le1\}$、$\mathfrak m=\{a:v(a)<1\}$。 强三角和乘性使 $\mathcal O$ 为环、$\mathfrak m$ 为理想； 若 $v(a)=1$，则 $a^{-1}\in\mathcal O$，故 $\mathfrak m$ 是极大理想， $\kappa=\mathcal O/\mathfrak m$ 为剩余域。

给定非零 $f,g$，选择达到最大读数的系数 $a,b$，令 $f_0=a^{-1}f$、$g_0=b^{-1}g$。 两者系数都在 $\mathcal O$ 中，约化后分别是 $\kappa\langle X,Y\rangle$ 中的非零多项式。 该自由代数无零因子：取两个非零多项式各自的最高次数部分， 选其中非零词 $u,v$，长度分别为 $m,n$。 最高次数 $m+n$ 的乘积词 $uv$ 只能在固定长度 $m$ 处拆分， 所以其系数恰是这两个非零系数之积，不会由其他拆分抵消。 故约化乘积非零。

因此 $f_0g_0$ 至少有一个系数读数为 $1$；另一方面逐系数强三角给全部系数读数至多为 $1$。 于是 $P(f_0g_0)=1$，乘回中央系数 $a,b$ 得 $P(fg)=v(a)v(b)=P(f)P(g)$。 任一因子为零时等式直接成立。

$\square$

#### 反例 8.4：严格异值不能替代严格增长

取引理 8.2 的原实域绝对值 $v$，令

$$\mathcal A=\mathbb R\langle X,Y\rangle, \qquad p\!\left(\sum_w a_ww\right)=\max_w v(a_w).$$

则 $\mathsf B_1,\mathsf{LB},\mathsf N,\mathsf U,\mathsf F$ 和非零条件均成立， 而全部非零探针满足

$$p(2u)=\tfrac12p(u)\ne p(u).$$

原商不可能是四元数代数。

**证明。**

原自由多项式代数实双线性、结合并有真正双侧单位 $1$。 上一引理给正定性、精确乘性及强三角，所以 $\mathsf{LB}$ 可取 $M=1$，且 $p(1)=1$。 取原同一对 $a=X,b=Y$。结合性给

$$T_{X,Y}c=2(XY-YX)c.$$

不同词 $XY,YX$ 的系数分别为 $1,-1$，故 $p(XY-YX)=1$。 精确乘性于是给

$$p(T_{X,Y}c)=v(2)p(XY-YX)p(c)=\tfrac12p(c).$$

所以原同一对对全部原 $c$ 忠实。 逐系数标量乘法给 $p(2u)=v(2)p(u)=p(u)/2$，满足异值而违反增长。

$p$ 正定，故零核为零；原商仍为无限维自由代数。 它不是四元数代数，而且原标量 $2$ 的读数已经排除任何正指数 $|2|^\alpha$ 的表示。 因此严格异值替换在其余全部条件下仍然失败。

$\square$

进一步，给定任意 $d_0\in(0,1)$，令

$$\gamma=\frac{\log d_0}{\log(1/2)}>0.$$

将上述域绝对值换成 $v^\gamma$ 后，强三角与精确乘性保留， 同一自由代数构造的自合成倍率恰为 $d_0$。 所以这一反例覆盖整个下降区间，不只是孤立的 $d=1/2$。

这个例子没有引入负读数：所有非零读数始终为正。 被保留为输入的是 *自合成后向哪一边改变* ，不是“有没有正性”。

### 8.2　不增长并不只意味着存在与不存在两种读数

#### 反例 8.5：纯存在读出不能推出规范长度

在标准四元数上令

$$p(0)=0,\qquad p(x)=1\quad(x\ne0).$$

它满足 $\mathsf B_1,\mathsf{LB},\mathsf N,\mathsf U,\mathsf F$ 及非零条件， 但不满足 $\mathsf G$。

**证明。**

单位和原双线性来自四元数。 四元数无零因子，所以 $p(xy)=p(x)p(y)$。 全部读数至多为 $1$，故 $\mathsf{LB}$ 可取 $M=1$。 取 $a=i,b=j$，则 $T_{i,j}c=4kc$，其零核为零，故 $\mathsf F$ 成立。 但对所有非零 $u$，有 $p(2u)=p(u)=1$。 非零实数倍的读数都为 $1$，不能成为任何正指数的通常长度幂律。

$\square$

#### 反例 8.6：非离散小读数与等值二元变化仍不足

固定 $0<r<1$，在中央变量四元数多项式代数 $\mathbb H[\tau]$ 上令

$$p(0)=0,\qquad p(f)=r^{\operatorname{ord}_\tau f}\quad(f\ne0),$$

其中 $\operatorname{ord}_\tau f$ 是最低非零次数，完全不读取该系数的通常模长。 则 $\mathsf B_1,\mathsf{LB},\mathsf N,\mathsf U,\mathsf F$ 和非零条件成立， 但 $p(2u)=p(u)$ 对所有 $u$ 成立。 与此同时，存在趋零的非零读数，以及等值输入合成后的严格正异值读数。

**证明。**

若非零 $f,g$ 的最低次数分别为 $m,n$，对应四元数系数为 $a_m,b_n$， 则 $fg$ 的最低系数为 $a_mb_n\ne0$，所以

$$\operatorname{ord}_\tau(fg)=m+n,\qquad p(fg)=p(f)p(g).$$

和的最低次数不小于两者最低次数的较小值；若完全抵消则和为零。 由于 $0<r<1$，这给

$$p(f+g)\le\max\{p(f),p(g)\},$$

故 $\mathsf{LB}$ 可取 $M=1$。 原代数实双线性且有双侧单位，$p(1)=1$。 非零常数左乘不改变最低次数，因而 $T_{i,j}c=4kc$ 满足 $p(T_{i,j}c)=p(c)$，同对忠实成立。 同理，任意非零原实标量都不改变次数，特别是 $p(2u)=p(u)$。

但是 $p(\tau^n)=r^n\to0$，每个 $\tau^n\ne0$； 由 $d(f,g)=p(f-g)$ 定义的强三角度量因此不是离散拓扑。 取

$$x=1,\qquad y=-1+\tau,$$

有

$$p(x)=p(y)=1, \qquad 0<p(x+y)=r<1.$$

所以仅要求“某等值二元合成后读数改变，且输出仍存在”，也不能替代严格增长。 零核为零，原商仍无限维。

$\square$

#### 反例 8.7：即使全部正实读数都出现，仍可保持 $d=1$

令 $\mathcal A=\mathbb H[\mathbb R]$ 为实加法群的有限支撑群代数。 其元素写成有限和

$$f=\sum_{t\in S}a_t Z^t, \qquad Z^sZ^t=Z^{s+t},$$

群元 $Z^t$ 与四元数系数交换。对非零 $f$，令

$$\nu(f)=\min\{t:a_t\ne0\},\qquad p(f)=e^{-\nu(f)},\qquad p(0)=0.$$

则上述不含增长的五组条件和非零条件均成立， $p(\mathcal A)=[0,\infty)$，但 $d=1$。

**证明。**

每个支撑有限，故最小指数存在。 两个非零元素相乘时，最小指数只能由两个最小指数相加得到； 对应系数是两个非零四元数的乘积，因此不为零。 所以 $\nu(fg)=\nu(f)+\nu(g)$，给精确乘性。 加法只可能保留或提高最小指数，给强三角和 $M=1$ 的局部界。 原双线性、结合性及双侧单位由群代数定义得到。 同一对 $i,j$ 仍给 $T_{i,j}c=4kc$，不改变指数，所以忠实。

任意非零实系数都不改变指数，因此 $p(2u)=p(u)$。 另一方面 $p(Z^t)=e^{-t}$，当 $t$ 遍历原实数时遍历全部正实数。 加上零元，读出范围恰为 $[0,\infty)$。 因此连“非离散”“有任意小正读数”或“有完整连续数值范围”也不能独自决定增长方向。

$\square$

### 8.3　有限二元预算仍承担不可替代的作用

#### 反例 8.8：保留严格增长而删除有限预算

在 $\mathbb H[\tau]$ 上，对最低非零系数为 $a_m$ 的非零多项式定义

$$p\!\left(\sum_{j=m}^n a_j\tau^j\right)=|a_m|, \qquad p(0)=0.$$

这与上一反例的次数读出不同。 它满足原 $\mathsf B_1,\mathsf G,\mathsf N,\mathsf U,\mathsf F$， 甚至满足旧精确翻倍标定，但没有共同有限单位输入合成界。

**证明。**

实双线性、结合性和双侧单位来自原多项式代数。 原读出正定，且 $p(2\cdot1)=2>1=p(1)$。 若另一多项式最低非零系数为 $b_\ell$，乘积最低非零系数为 $a_mb_\ell$； 四元数范数乘性给 $p(fg)=p(f)p(g)$。 同一对 $a=i,b=j$ 给 $T_{i,j}c=4kc$，从而 $p(T_{i,j}c)=4p(c)$，满足忠实。

然而对任意 $R>0$，取 $f_R=1+R\tau$、$g=-1$，则

$$p(f_R)=p(g)=1,\qquad p(f_R+g)=p(R\tau)=R.$$

因此没有适用于全部原输入的有限 $M$。 原零核为零，原商仍为无限维 $\mathbb H[\tau]$。

$\square$

### 8.4　本轮能删掉什么，已经证明不能怎样删

#### 命题 8.9：已证弱化边界

在固定其余关系条件下，以下陈述成立：

1.  精确倍率 $2$ 可以删除；一次严格增长足以恢复唯一正指数及规范四元数几何。

2.  严格增长不能仅换成异值：$0<d<1$ 的非交换自由代数反例满足其余条件。

3.  严格增长不能仅换成非零、读数非恒定、趋零的非零读数、 等值输入合成后的严格正异值，或完整正实数值范围。

4.  共同有限合成预算不能同时删除：最低非零系数模长反例连旧精确标定也保留。

这些结论不声称主候选在任意语言中已达到最弱，也不将尚未证明等价的其他二元条件列为定理。

**证明。**

第一项由主分类及严格弱化命题 3.10 给出。 第二项由例 8.4 给出。 第三项分别由例 8.5、 例 8.6 和例 8.7 给出。 第四项由例 8.8 给出。

$\square$

#### 命题 8.10：只依赖自合成倍率时的精确最弱接受域

固定 $\mathsf B_1,\mathsf{LB},\mathsf N,\mathsf U,\mathsf F$，并要求存在非零可读探针。 只允许通过一个集合 $S\subset(0,\infty)$，对探针无关的倍率 $d=p(2u)/p(u)$ 施加条件 $d\in S$。 若该条件既足以推出正幂四元数分类，又保留全部 $\alpha>0$ 的四元数模型， 则且仅则

$$\boxed{S=(1,\infty).}$$

这是在明确限定的倍率条件类中得到的结论，不是任意语言中的最少公理数。

**证明。**

每个 $d>1$ 都由 $\mathbb H$ 上 $p(x)=|x|^{\log_2d}$ 实现。 要求保留全部正指数模型，故必须有 $(1,\infty)\subseteq S$。 对每个 $0<d<1$，例 8.4 及其正幂变体给满足其余五组的无限维反例； $d=1$ 则由例 8.6 给同样的反例。 因此充分性迫使 $S$ 不含任何 $0<d\le1$，即 $S\subseteq(1,\infty)$。 两者合用得到唯一可能的接受域。 反向，当 $S=(1,\infty)$ 时，条件恰为主候选 $\mathsf G$； 主分类与反向实现定理已分别证明充分性和全部正指数模型的保留。

$\square$

<a id="section-9"></a>

## 9　其余反向删除：在一次幂子类中保留原反例

以下反例取原 $p=\ell$（即 $\alpha=1$）或显式注明其读出。因此它们也是本轮较大模型类中的合法删除检验，不预先要求本轮所有原 $p$ 都为一次齐次。

#### 反例 9.1：删除忠实条件：八元数的尖锐边界

令 $\mathbb O=\mathbb H\oplus\mathbb H$，乘法为

$$(a,b)(c,d)=(ac-\bar d b,\;da+b\bar c),\qquad q(a,b)=|a|^2+|b|^2.$$

四元数平方展开及实部循环性给

$$|ac-\bar d b|^2+|da+b\bar c|^2=(|a|^2+|b|^2)(|c|^2+|d|^2),$$

故其范数确实乘性。取 $a=(i,0)$、$b=(j,0)$、$c=(0,1)$。 则 $k=ab-ba=(2k_{\mathbb H},0)$，

$$X(c)=(0,2k_{\mathbb H}),\qquad Y(c)=(0,-2k_{\mathbb H}),\qquad T(c)=0,$$

而 $q(c)=1$，$q(k)=4$，且

$$(ab)c-a(bc)=(0,2k_{\mathbb H}).$$

这给出非零可读第三元上两份响应完全抵消的显式例子。 更一般地，任意非交换对的 $T$ 由投影定理都只有实秩四， 而 $\mathbb O$ 实维八，故不可能忠实；交换对则有 $T(1)=0$。 所以不存在其他见证对能够挽救八元数上的 $\mathsf F$。 同一对生成的所有有限代数表达式都在 $\mathbb H\oplus0$ 内； 在该子代数上 $T=2L_k$ 忠实。只检验自生成的小域会漏掉 $c$。

#### 反例 9.2：即使保留左单位，右单位仍不可删除

在实空间 $\mathbb C$ 上定义 $x\star y=\bar x y$，$\ell(x)=|x|$。 乘法实双线性，范数乘性，$1$ 是左单位。取 $a=1,b=i$，则

$$k=a\star b-b\star a=2i,\quad Y(c)=a\star(b\star c)-b\star(a\star c)=0,\quad T(c)=-2ic.$$

所以 $T$ 全域忠实。右单位只能是 $1$，但 $i\star1=-i\ne i$。 该商实维二，不是四元数原乘法。 因此范数恢复只需要左单位，不意味着最终候选也可删除右单位。

#### 反例 9.3：删除乘性

令 $A=M_3(\mathbb R)$，通常乘法，$q(X)=\operatorname{Tr}(X^{\mathsf T}X)/3$。 取 $a=E_{12}+E_{23}$、$b=E_{21}+2E_{32}$，则

$$k=ab-ba=\operatorname{diag}(1,1,-2)$$

可逆。结合性给 $T(c)=2kc$，所以 $T$ 忠实；正性、单位、存在均成立。 但是 $q(E_{12}E_{21})=1/3\ne1/9=q(E_{12})q(E_{21})$。 可读维数九，不能得到本结论。

#### 反例 9.4：删除原双线性：一个连续例子

在通常四元数实空间及通常平方范数上，令

$$\phi(t)=\frac\pi4t(t-1),\qquad s(x)=e^{i\phi(\operatorname{Re}x)}, \qquad x\star y=x\,s(x)^{-1}ys(x).$$

范数乘性成立，且 $1\star y=y$、$x\star1=x$。 对纯方向 $i,j,2k$，均有 $s(x)=1$，所以同一见证 $a=i,b=j$ 仍给 $T=4L_k$ 忠实。 然而 $s(2)=i$，故

$$2\star j=-2j\ne2(1\star j),$$

原乘法不对原实线性结构双线性。

#### 反例 9.5：原算子等式只能模同一读出核成立

取原代数 $\mathcal A=\mathbb H\times M_3(\mathbb R)$，逐分量通常乘法， $q(h,X)=|h|^2$。令

$$A_0=E_{12}+E_{23},\qquad B_0=E_{21}+2E_{32},\qquad K=[A_0,B_0]=\operatorname{diag}(1,1,-2),$$

并取原见证 $a=(i,A_0)$、$b=(j,B_0)$。 全部候选条件成立，$N=0\times M_3(\mathbb R)$，$q([a,b])=4$。 但是原合成算子为

$$\mathcal T(h,X)=(4k_{\mathbb H}h,\,2KX).$$

所以

$$(\mathcal T^3+16\mathcal T)(0,I) =(0,8K^3+32K)\ne0.$$

原投影表达式在矩阵分量上的作用是 $X\mapsto-K^2X/4$，也不精确幂等。 这些算子差的读数仍为零；商上的 $T^3=-16T$ 与 $P^2=P$ 均准确成立。 这说明原层与可读商的区别有真实反例，不能省略。

连同前节标定、局部界和非交换边界的反例，这些反例分别否定指定删除后的蕴含；并不声称六组条件构成某个语言无关的最小公理基。

八元数反例没有出现负读出或逻辑矛盾；它出现的是本候选所指定合读的盲方向。 要求这个合读忠实仍是选模型的关系输入，并未由“读出非负”单独证明。

本轮的三角恢复使用精确乘性。若只给近似乘性，重复合成的误差可能指数积累， 取第 $n$ 次根后仍留下非一常数；本稿没有把精确结论宣称为任意噪声下的稳定性定理。

<a id="section-10"></a>

## 10　同一合读结构的几何完成：方向、复幅度与正读出

本节只使用主定理已得的

$$A=\mathcal A/N\cong\mathbb H,\qquad B(x,y)=\operatorname{Re}(\bar x y),\qquad q(x)=B(x,x),\qquad W=\mathbf 1^\perp.$$

原单位类、原乘法与原二次读数均保持不变。以下定义及定理不是第二个候选公理。 记 $L_ax=ax$、$R_ax=xa$；算子复合从右向左作用，故 $R_aR_b=R_{ba}$。始终用 $H_J$ 表示复幅度空间，用 $W$ 表示实三维方向空间。

### 10.1　三维叉积、面积与二元关系的三元返回

#### 定义 10.1：同一乘法的对称部分与反对称部分

对 $x,y,z\in W$ 定义

$$x\times y:=\frac{xy-yx}{2},\qquad \nu(x,y,z):=B(x\times y,z).$$

#### 定理 10.2：二元长度、面积与三元返回

对全部 $x,y,z\in W$，有

$$
\begin{aligned}
xy&=-B(x,y)\mathbf 1+x\times y,
\end{aligned}
\tag{10.1}
$$

$$
\begin{aligned}
B(x\times y,x)&=B(x\times y,y)=0,
\end{aligned}
\tag{10.2}
$$

$$
\begin{aligned}
q(x\times y)&=q(x)q(y)-B(x,y)^2,
\end{aligned}
\tag{10.3}
$$

$$
\begin{aligned}
x\times(y\times z)&=B(x,z)y-B(x,y)z,
\end{aligned}
\tag{10.4}
$$

$$
\begin{aligned}
(x\times y)\times z&=B(x,z)y-B(y,z)x.
\end{aligned}
\tag{10.5}
$$

三线性型 $\nu$ 交替；$\times$ 满足 Jacobi 恒等式。

**证明。**

纯方向反交换关系 $xy+yx=-2B(x,y)\mathbf 1$ 给式 (10.1)。 共轭反转乘法次序，故 $x\times y\in W$。 原配对伴随恒等式给

$$B(xy,x)=q(x)B(y,\mathbf 1)=0,\qquad B(xy,y)=q(y)B(x,\mathbf 1)=0.$$

标量部分与 $W$ 正交，得到式 (10.2)。 将乘性二次型分成这两个正交部分，得到

$$q(x)q(y)=q(xy)=B(x,y)^2+q(x\times y),$$

即式 (10.3)。 取主定理中的正交单位基 $u,v,w=uv$。原乘法表给 $u\times v=w$、$v\times w=u$、$w\times u=v$，反序取负。 对三个变量作实三线性展开，即得两条三元返回式。 同一张表给 $\nu(u,v,w)=1$ 并在交换任意两槽时变号，故 $\nu$ 交替。 式 (10.4) 的循环和为零，得到 Jacobi 恒等式。

$\square$

这是四元数纯部的标准三维几何；本轮先由一次正向自合成增益内生取得 $\alpha$ 与 $\ell=p^{1/\alpha}$，再对 $\ell$ 应用定标引理，用同一对忠实合读取得该原代数。原 $p$ 保持为 $\ell^\alpha$。 R5-022 已从另一种三元返回入口研究同一三维结果。[\[15\]](#ref-baez), [\[16\]](#ref-r522)

#### 推论 10.3：归一化二元二次式

若 $r,s\in W$ 为单位方向，则

$$q(\alpha r+\beta s) =\alpha^2+2B(r,s)\alpha\beta+\beta^2, \qquad -2\le2B(r,s)\le2.$$

当 $r\perp s$ 时，$q(\alpha r+\beta s)=1$ 的全部解构成平面圆； 一个已指定的非零直角三角形归一化只确定其中一个点。

**证明。**

极化恒等式给二次式，Cauchy–Schwarz 给系数范围。 正交时归一方程为 $\alpha^2+\beta^2=1$， 映射 $(\alpha,\beta)\mapsto\alpha r+\beta s$ 是平面的等距映射。 给定两条直角边的长度并除以斜边，只给这个方程的一组解。

$\square$

#### 命题 10.4：由原乘法导出的各向同性与半角

单位集合 $\mathcal U=\{u\in A:q(u)=1\}$ 是群。 共轭 $\operatorname{Ad}_u(x)=ux\bar u$ 在 $W$ 上保持 $B$ 与 $\times$， 其像恰为 $\operatorname{SO}(W,B)$，核为 $\{\pm\mathbf 1\}$。 若 $n\in W$ 为单位，$u=\cos(\theta/2)\mathbf 1+n\sin(\theta/2)$，则

$$\operatorname{Ad}_u(x)=\cos\theta\,x +(1-\cos\theta)B(n,x)n+\sin\theta\,(n\times x).$$

**证明。**

原乘性和 $u^{-1}=\bar u$ 给群律。 共轭保持乘法、单位、共轭与 $q$，所以保持 $W,B,\times$。 把 $x$ 分成 $B(n,x)n$ 与垂直分量，使用纯部反交换式展开 $ux\bar u$，即得显示公式。每个单位四元数均可写成所示半角形式， 故所得作用是定向正交变换。 反之，三维实定向正交变换必有本征值 $1$：非实本征值成共轭对， 实本征值为 $\pm1$，行列式为一。其固定轴的正交平面上是二维旋转， 因而由显示公式实现。若共轭固定全部纯部，则 $u$ 与三个纯基元交换； 原乘法表迫使 $u$ 为实标量，单位范数再给 $u=\pm\mathbf 1$。

$\square$

### 10.2　忠实合读直接给出左复标量

沿用候选的同一对见证，令

$$k=[a,b],\qquad e=\frac{k}{\sqrt{q(k)}},\qquad J=\frac{T_{a,b}}{2\sqrt{q(k)}}=L_e.$$

前文已得 $q(k)>0$、$e\in W$、$q(e)=1$，以及 $J^2=-I$、$`J^*=-J`$、$`J^*J=I`$。

#### 定义 10.5：内部复标量与幅度比较

以内部平面 $\mathbb C_e=\operatorname{span}_\mathbb R\{\mathbf 1,e\}$ 表示复数，规定

$$(\alpha+i\beta)x:=\alpha x+\beta Jx, \qquad h(x,y):=B(x,y)+iB(Jx,y),\qquad H_J=(A,J,h).$$

这里的 $i$ 从左作用；下文的 $h$ 第一槽共轭线性、第二槽线性。

#### 定理 10.6：复二维幅度与完整复线性算子空间

$H_J$ 是复二维 Hilbert 空间，$h(x,x)=q(x)$。 记 $R_A=\{R_a:a\in A\}$，则有实线性直和

$$\boxed{\operatorname{End}_{\mathbb C}(H_J)=R_A\oplus J R_A.}$$

其共轭伴随为

$$(R_a+JR_b)^*=R_{\bar a}-JR_{\bar b}.$$

**证明。**

$J$ 反自伴给共轭对称性，并给

$$h(Jx,y)=-ih(x,y),\qquad h(x,Jy)=ih(x,y).$$

又 $h(x,x)=B(x,x)>0$ 对 $x\ne0$ 成立。 选单位 $f\in W$、$f\perp e$，则 $\{\mathbf 1,f\}$ 为复正交基： 其复张成是实基 $\mathbf 1,e,f,ef$ 的张成，两个基向量的 $h$ 配对为零。 因而复维二，有限维保证完备。

结合性使每个 $R_a$ 与 $J$ 交换，故两类算子均复线性。 若 $R_a=JR_b$，在 $\mathbf 1$ 上作用得 $a=eb$，于是 $(xe-ex)b=0$ 对全部 $x$ 成立。 若 $b\ne0$，右乘 $b^{-1}$ 得 $xe=ex$ 对全部 $x$ 成立， 这与取 $x=f\perp e$ 矛盾。因此 $a=b=0$，直和实维八。 $\operatorname{End}_{\mathbb C}(H_J)$ 的实维也是八，故该直和为全部算子空间。 原配对伴随式给 $`R_a^*=R_{\bar a}`$；$`J^*=-J`$ 且左右乘交换， 得到显示伴随式。对复线性算子，这个实伴随同时保持 $h$ 的虚部，故也是复伴随。

$\square$

### 10.3　Pauli 关系、自伴锥与 Born 表示

#### 定义 10.7：由原右乘定义观测算子

对 $z\in W$ 定义

$$\sigma_z:=-JR_z=-L_eR_z.$$

算子正性定义为 $`F=F^*`$ 且 $h(x,Fx)\ge0$ 对全部幅度 $x$ 成立。

#### 定理 10.8：Pauli 乘法与自伴算子的全部形式

对 $z,t\in W$，有

$$
\begin{aligned}
\sigma_z^*&=\sigma_z,\qquad
\sigma_z\sigma_t=B(z,t)I+i\sigma_{z\times t},
\end{aligned}
\tag{10.6}
$$

$$
\begin{aligned}
\operatorname{Tr}\sigma_z&=0,\qquad
\operatorname{Tr}(\sigma_z\sigma_t)=2B(z,t).
\end{aligned}
\tag{10.7}
$$

每个自伴算子唯一为 $F=sI+\sigma_z$，其本征值为 $s\pm\sqrt{q(z)}$。因此

$$E:=\operatorname{Herm}(H_J)=\mathbb RI\oplus\sigma(W),\qquad E_+=\{sI+\sigma_z:s\ge\sqrt{q(z)}\}.$$

**证明。**

纯元右乘和 $J$ 都反自伴且交换，所以 $-JR_z$ 自伴。 注意右乘次序反转，故

$$\sigma_z\sigma_t=J^2R_zR_t=-R_{tz} =B(z,t)I+R_{z\times t} =B(z,t)I+i\sigma_{z\times t}.$$

若 $z\ne0$，选单位 $t\perp z$；上式给 $\sigma_t\sigma_z\sigma_t=-\sigma_z$ 与 $\sigma_t^2=I$。 迹在相似变换下不变，故 $\operatorname{Tr}\sigma_z=0$；$z=0$ 也成立。 再次取迹即得配对公式。

上一全算子表示中，自伴性等价于 $a=\bar a$、$b=-\bar b$， 所以自伴算子恰为 $sI+\sigma_z$，且表示唯一。 式 (10.6) 给 $\sigma_z^2=q(z)I$；自伴性与迹零给两个本征值 $\pm\sqrt{q(z)}$，包括 $z=0$ 的退化情形。 加上 $sI$ 后逐一判定本征值非负，得到正锥。

$\square$

#### 推论 10.9：同一比较的正锥与可读性

$$E_+=\{F^2:F=F^*\},\qquad E_+\cap(-E_+)=\{0\},$$

且 $E_+$ 对迹配对自对偶：

$$G\in E_+\iff\operatorname{Tr}(GF)\ge0\quad\forall F\in E_+.$$

每个非零 $G\in E_+$ 都满足 $\operatorname{Tr}G>0$。

**证明。**

自伴平方的本征值非负；反之，对正算子的两个非负本征值取平方根， 得到自伴平方根。正锥及其负锥只能在两个本征值全零时相交。 若 $F=sI+\sigma_z$、$G=tI+\sigma_w$ 都正，则

$$\operatorname{Tr}(FG)=2(st+B(z,w))\ge2(st-\lVert z\rVert\lVert w\rVert)\ge0.$$

若 $G\notin E_+$ 且 $w\ne0$，取 $F=I-\sigma_{w/\lVert w\rVert}$， 得到 $\operatorname{Tr}(FG)=2(t-\lVert w\rVert)<0$。 若 $w=0,t<0$，取 $F=I$ 即可。最后非零正算子至少有一个正本征值，故迹为正。

$\square$

幅度集合 $A$ 与正对象集合 $E_+$ 类型不同。$q(-x)=q(x)$ 表示幅度反向不产生负读数， 而 $G,-G$ 同为正对象只可能 $G=0$。两者都由显示关系表达，不需赋予负幅度“负存在”的含义。

#### 定义 10.10：正读出状态与效果

$$\operatorname{St}(E)=\{\ell:E\to\mathbb R:\ell\text{ 实线性},\ \ell(E_+)\ge0,\ \ell(I)=1\},\qquad \operatorname{Eff}(E)=\{F:0\le F\le I\}.$$

这里定义的是数学读出对象；实际准备、装置与这些对象的对应另需给定。

#### 定理 10.11：密度球、效果与二元平方律

全部正读出状态唯一表示为

$$\rho_r=\frac{I+\sigma_r}{2},\qquad q(r)\le1, \qquad\ell_r(F)=\operatorname{Tr}(\rho_rF).$$

效果 $F=\eta I+\sigma_b$ 的准确条件是

$$\sqrt{q(b)}\le\min\{\eta,1-\eta\}.$$

极点状态恰对应 $q(r)=1$；对单位 $n,m\in W$，

$$P_n=\frac{I+\sigma_n}{2},\qquad \operatorname{Tr}(P_nP_m)=\frac{1+B(n,m)}2.$$

**证明。**

非退化迹配对使每个实线性泛函唯一为 $F\mapsto\operatorname{Tr}(\rho F)$、$`\rho=\rho^*`$。 正锥自对偶使其正性等价于 $\rho\ge0$，单位评价等价于 $\operatorname{Tr}\rho=1$。 自伴形式及其两个本征值立即给 $\rho_r$ 和 $q(r)\le1$。 对 $F$ 与 $I-F$ 同时应用正锥条件，得到效果条件。

若 $\lVert r\rVert<1$，可沿任意小的非零方向作对称扰动 $r\pm v$，仍在球内， 故该态不是极点。若 $\lVert r\rVert=1$ 且 $r=\lambda a+(1-\lambda)b$、 $0<\lambda<1$、$\lVert a\rVert,\lVert b\rVert\le1$，与 $r$ 配对迫使 $B(r,a)=B(r,b)=1$；Cauchy–Schwarz 的等号条件给 $a=b=r$，故为极点。 $P_n^2=P_n$ 由 Pauli 式得出，其迹为一，故秩一。 最后展开两个投影并使用迹配对，得到二元概率式。

$\square$

### 10.4　Hopf 圆纤维与表示轴独立性

#### 定理 10.12：从幅度到方向的准确相位商

对 $x\ne0$ 定义

$$r_e(x)=\frac{\bar x e x}{q(x)}\in W.$$

它是单位方向。对归一幅度 $x,y$，有

$$r_e(x)=r_e(y)\iff y=e^{\phi e}x=e^{\phi J}x \quad\text{对某个 }\phi\in\mathbb R.$$

该映射满射，所以

$$S^1\longrightarrow S^3\longrightarrow S^2, \qquad \mathbb P(H_J)=\mathbb{CP}^1\cong S(W).$$

并有

$$P_{r_e(x)}y=\frac{h(x,y)}{q(x)}\,x,\qquad \operatorname{Tr}(P_{r_e(x)}P_{r_e(y)}) =\frac{|h(x,y)|^2}{q(x)q(y)}.$$

右端系数均按前述左复标量约定作用。

**证明。**

共轭和范数乘性给 $r_e(x)\in W$、$q(r_e(x))=1$。 已证共轭覆盖全部三维旋转，所以 $\bar x e x$ 在单位幅度上取遍单位球。 若归一 $x,y$ 具有相同方向，置 $u=y\bar x$，则 $q(u)=1$ 且 $ue=eu$。 由纯部乘法式，$e$ 的中心化子恰为 $\mathbb R\mathbf 1+\mathbb Re$； 其中单位元恰为 $\cos\phi\mathbf 1+e\sin\phi$，得到纤维式。 反向把 $y=e^{\phi e}x$ 代入即可。 一般非零幅度先除以 $\sqrt{q(x)}$，故相同方向恰对应同一复射线。

结合性给 $x r_e(x)=e x$，于是

$$\sigma_{r_e(x)}x=-e(xr_e(x))=-e(e x)=x.$$

秩一投影 $P_{r_e(x)}$ 的像因此是复线 $\mathbb Cx$；正交投影的系数由 $h(x,y-\lambda x)=0$ 唯一确定为 $\lambda=h(x,y)/q(x)$。 两个秩一投影的迹乘积遂为所示平方模。

$\square$

射线商并不等于原零读出商：$\mathbf 1$ 与 $e$ 有相同的 $r_e$， 但原带参考表达式给 $q(\mathbf 1+\mathbf 1)=4$、$q(e+\mathbf 1)=2$。 因此实际相位参考若仍可使用，必须作为内部对象保留； 只有经过上述相位不变读出的菜单才将这些幅度识别为同一纯态。 一般复 $d$ 维幅度的射线空间为 $\mathbb{CP}^{d-1}$，局部用 $d-1$ 个复坐标表示， 实维为 $2d-2$；本节三维球面的方向表示只对应 $d=2$。

#### 定理 10.13：见证所选复轴仅改变表示坐标

对任意单位 $e,e'\in W$，存在单位 $u\in A$，使 $F=L_u$ 满足

$$J_{e'}F=FJ_e,\qquad h_{e'}(Fx,Fy)=h_e(x,y),$$

$$\sigma_z^{e'}F=F\sigma_z^e\quad(\forall z\in W),\qquad r_{e'}(Fx)=r_e(x).$$

因此无需在见证之外再指定一个物理上优先的复轴。

**证明。**

若 $e'\ne-e$，定义

$$u=\frac{\mathbf 1-e'e}{\sqrt{2(1+B(e,e'))}}.$$

分母是分子的范数，且 $(\mathbf 1-e'e)e=e+e'=e'(\mathbf 1-e'e)$，故 $e'u=ue$。 若 $e'=-e$，取任意单位 $u\perp e$，纯部反交换仍给 $e'u=ue$。 所以 $J_{e'}L_u=L_uJ_e$。左乘单位元是实等距映射， 从而保持 $h$ 的实部及虚部；它又与全部右乘交换，得到 Pauli 交织式。 最后 $\bar u e'u=e$，所以

$$r_{e'}(ux)=\frac{\bar x\bar u e'ux}{q(x)}=r_e(x).$$

该证明消除的是表示坐标的额外选择，不删除主候选中忠实见证对的存在条件。

$\square$

### 10.5　酉门、整体相位与端点未确定的自由度

#### 定理 10.14：全部单比特酉门及其方向作用

单位四元数右乘的集合恰为 $\operatorname{SU}(H_J)$；每个酉算子都可写成

$$U=e^{\phi J}R_u,\qquad q(u)=1.$$

对单位 $z\in W$，

$$U_z(\theta)=e^{-i\theta\sigma_z/2}=R_{e^{-\theta z/2}}, \qquad r_e(U_z(\theta)x)=e^{\theta z/2}r_e(x)e^{-\theta z/2}.$$

整体相位 $e^{\phi J}$ 保持 $r_e(x)$ 不变。

**证明。**

在复基 $\{\mathbf 1,f\}$ 中写 $u=\alpha+\beta f$，$\alpha,\beta\in\mathbb C_e$。 由 $f\alpha=\bar\alpha f$、$f\beta f=-\bar\beta$，右乘矩阵为

$$
R_u\ \widehat{=}\quad
\begin{pmatrix}\alpha&-\bar\beta\\ \beta&\bar\alpha\end{pmatrix}.
$$

$q(u)=|\alpha|^2+|\beta|^2=1$ 恰使该矩阵酉且行列式为一。 反过来，二维酉矩阵的列正交和行列式一迫使它具有这个形式。 给任意 $U\in U(2)$，选 $e^{2i\phi}=\det U$，则 $e^{-i\phi}U\in SU(2)$， 得到分解。这里 $u\mapsto R_u$ 是反表示；若需群同态，应取 $u\mapsto R_{u^{-1}}$。

由于 $-i\sigma_z=-J(-JR_z)=-R_z$，指数幂级数给门公式。 直接代入 Hopf 映射得到 $r_e(xu)=\bar u r_e(x)u$； 代入 $u=e^{-\theta z/2}$ 给正角度的 Rodrigues 旋转。 左相位与 $e$ 交换，故在 $\bar x e x$ 中抵消。

$\square$

<a id="section-11"></a>

## 11　由规范几何到概率平方：原读数与事件质量的接口

**本节输入。** 已取得$\ell=p^{1/\alpha}$和$q=\ell^2$的复Hilbert结构； 事件读出绑定为同一矩阵代数上的正归一 *线性* 泛函， 非零纯准备$\psi$绑定为 $\rho_\psi=|\psi\rangle\langle\psi|/q(\psi)$， 并指定正交事件投影。仅有非负和总概率一不等于上述接口。 **闭合输出。** 分支概率为规范二次读数之比。 只有另要求原$p$本身等于未归一概率质量时，才需要识别原指数$\alpha$。

#### 定理 11.1：纯态投影概率的原读数公式

在上述线性事件与纯准备绑定下，设$\psi\ne0$，且$P$为复正交投影。则规范Born表示为

$$\boxed{ \Pr(P\mid\psi) =\frac{q(P\psi)}{q(\psi)} =\left(\frac{p(P\psi)}{p(\psi)}\right)^{2/\alpha}. }$$

若$\{P_i\}_{i=1}^n$为完整正交分区，则

$$\sum_i\Pr(P_i\mid\psi)=1.$$

**证明。**

正交分解$\psi=P\psi+(I-P)\psi$使$q$相加。 正归一矩阵态的迹表示对纯态给$q(P\psi)/q(\psi)$； 代入$q=p^{2/\alpha}$即得第一式。 完整正交分区使$\sum_iq(P_i\psi)=q(\psi)$，分母严格正，故第二式成立。 这里没有对零质量分支作除法。

$\square$

#### 命题 11.2：若原读数本身被绑定为概率质量

在复二维空间选正交单位$e_1,e_2$，令 $\psi=(e_1+e_2)/\sqrt2$，$P_i$为投影到$\mathbb Ce_i$的正交投影。 若另要求$p(P_1\psi)+p(P_2\psi)=p(\psi)$， 则$\alpha=2$。反之，$\alpha=2$使所有正交分解均满足原$p$可加。

**证明。**

规范长度给$\ell(\psi)=1$、$\ell(P_i\psi)=1/\sqrt2$， 故所加要求为$2(1/\sqrt2)^\alpha=1$，等价于$\alpha=2$。 反向由$p=\ell^2=q$及内积的正交加和立即成立。

$\square$

#### 命题 11.3：谱平方与存在量词不同

对$\psi\ne0$，其可读性仅要求$p(\psi)>0$。 任意正幂$p^\beta$保留同一零核及可读对象， 但若未同时变换指数，数值平方$(p^\beta)^2$一般改变事件比例。 同时变换$\alpha\mapsto\beta\alpha$后，

$$(p^\beta)^{2/(\beta\alpha)}=p^{2/\alpha}=q,$$

因此规范事件概率不变。

**证明。**

严格正幂保持零与正值，并按实幂指数律化简。 取$p(\psi_1)/p(\psi_2)\ne0,1$即可看到未校正的数值平方随$\beta$变化。

$\square$

同一规范读数对任意两元给

$$B(x,y)=\frac14\left[p(x+y)^{2/\alpha}-p(x-y)^{2/\alpha}\right],$$

所以二元夹角不是在原读数之外额外放入的函数。 三元的有向比较由同一乘法的反对称部分及该配对取得， 后文的叉积、Bargmann相位和量子几何张量保持这一归属。

<a id="section-12"></a>

## 12　线、面积、相位与钟：同一几何的准确分工

本节没有新增核心候选。固定已导出的 $W=1^\perp\cong\mathbb R^3$、内积与取向， 用 $a\cdot b$ 表示 $B(a,b)$。外积空间 $\Lambda^2W$ 带导出的欧氏面积范数， Hodge 星满足 $\star(a\times b)=a\wedge b$。 这些是同一结构的构造；指定哪条历史实际发生，仍是另一个输入。

#### 定理 12.1：单态稳定子面与转向面

对单位 $n$，定义

$$\pi_n:\Lambda^2W\to T_nS^2,\qquad \pi_n(\beta)=(\star^{-1}\beta)\times n.$$

则每个 $\beta$ 唯一分解为

$$\boxed{\beta=\lambda\star n+n\wedge v,\quad v\perp n,\quad \pi_n(\beta)=v,\quad \|\beta\|^2=\lambda^2+\|v\|^2.}$$

特别地，$\ker\pi_n=\mathbb R\star n$。

**证明。**

取正交定向基 $(n,u_1,u_2)$。 $u_1\wedge u_2=\star n,n\wedge u_1,n\wedge u_2$ 构成 $\Lambda^2W$ 的正交单位基。 第一项对应旋转轴 $n$，故在 $n$ 上作用为零。 对 $v\perp n$， $\pi_n(n\wedge v)=(n\times v)\times n=v$。 逐基展开给分解、唯一性、范数与核。

$\square$

这与最新 OTF-005 的轴面分解一致。[\[17\]](#ref-otf5) 单态所决定的 $\star n$ 是绕自身方向的生成面； 把该态转往别处所需的面由 $n\wedge\dot n$ 给出。 一个方向不自动确定横向的零相位： 若旋转等变地给每个 $n$ 选非零 $v(n)\perp n$， 绕 $n$ 的半周转动既固定 $n$ 又把 $v(n)$ 变成 $-v(n)$，产生矛盾。

#### 命题 12.2：端点、最短扇形与非唯一的实际门

设单位 $a,b$ 不平行，$\theta=\arccos(a\cdot b)\in(0,\pi)$，

$$u=\frac{b-(a\cdot b)a}{\sin\theta},\quad c=a\times u,\quad \Sigma=\frac\theta2\,a\wedge u.$$

单位平面扇形从 $a$ 到 $b$ 的有向面积是 $\Sigma$，对应门

$$U_{ab}=\exp(-i\theta\sigma_c/2) =\frac{(1+a\cdot b)I-i\sigma_{a\times b}}{\sqrt{2(1+a\cdot b)}}$$

满足 $`U_{ab}P_aU_{ab}^*=P_b`$。 端点还容许全部 $e^{-i\chi\sigma_b/2}U_{ab}$，故不能恢复唯一的实际门。

**证明。**

参数化扇形 $X(r,t)=r(\cos t\,a+\sin t\,u)$，$0\le r\le1,0\le t\le\theta$。 有 $\partial_rX\wedge\partial_tX=r\,a\wedge u$，积分得到 $\Sigma$。 Pauli 关系使指数为 $\cos(\theta/2)I-i\sin(\theta/2)\sigma_c$； 半角恒等式给显示分式。已证 Rodrigues 公式把 $a$ 旋转到 $b$。 任意主角 $\phi\in[0,\pi]$ 的轴旋转若把 $a$ 送到 $b$， 则 $a\cdot b=\cos\phi+(1-\cos\phi)(a\cdot d)^2\ge\cos\phi$， 故 $\theta\le\phi$；所构造的垂直轴达到下界。 绕 $b$ 的任意后续旋转固定 $P_b$，所以显示族共享端点。

$\square$

垂足 $C=(a\cdot b)a$ 是 $a,b$ 的确定函数，不是额外自由数据。 若 $b=-a$，转向平面不唯一；若 $b=a$，最短门可取恒等而实际历史仍可闭路。 两端点上的 $\sin\theta$、$\sin\theta/2$ 与 $\theta/2$ 分别是平行四边形、三角形与单位扇形的面积模， 球面闭路的立体角又是另一种量。

#### 定理 12.3：同一投影张量内的长度与面积

对 $n\in S^2$、$v,w\in T_nS^2$，令

$$\mathcal Q_n(v,w)=\operatorname{Tr}\bigl(P_n\,dP_n(v)\,dP_n(w)\bigr).$$

则

$$\boxed{\mathcal Q_n(v,w)=\frac14\bigl(v\cdot w+i\,n\cdot(v\times w)\bigr).}$$

其实部为 Fubini–Study 度量，约定 $d_{\rm FS}=\arccos|h(\psi,\phi)|$； 虚部给有向面积的四分之一。 采用联络 $\mathcal A=i\langle\psi,d\psi\rangle$ 时，曲率为 $\mathcal F=-2\operatorname{Im}\mathcal Q$，闭路几何相位为 $-\Omega/2$ 模 $2\pi$。

**证明。**

$dP_n(v)=\sigma_v/2$。代入 Pauli 乘法和迹公式即得张量等式。 单位幅度的水平微分满足 $ds_{\rm FS}^2=\langle d\psi,d\psi\rangle-|\langle\psi,d\psi\rangle|^2$， 以 $P=|\psi\rangle\langle\psi|$ 展开，恰等于 $\operatorname{Re}\mathcal Q$。 在球面局部坐标选 $\psi=(\cos(\vartheta/2),e^{i\varphi}\sin(\vartheta/2))^{\mathsf T}$， 直接计算

$$\mathcal A=-\tfrac12(1-\cos\vartheta)d\varphi,\qquad d\mathcal A=-\tfrac12\sin\vartheta\,d\vartheta\wedge d\varphi.$$

后者等于所列 $-2\operatorname{Im}\mathcal Q$。 在可选局部截面的曲面片上用 Stokes 定理；换片只改变相位的 $2\pi$ 整数倍，得闭路式。

$\square$

这是几何量子力学与投影算子几何的标准结构。[\[18\]](#ref-ashtekar), [\[19\]](#ref-projector), [\[20\]](#ref-berry) 同一 $\mathcal Q$ 包含长度和面积，并不赋予它们相同的物理量纲。

#### 命题 12.4：同一方向路径不能确定唯一 Hamiltonian 或时长

给定 $C^1$ 的 $n(t)\in S^2$，全部使其满足薛定谔方向运动的自伴生成元为

$$H(t)=h_0(t)I+\frac\hbar2\sigma_{n\times\dot n+\lambda(t)n}, \qquad h_0,\lambda\text{ 任意实连续函数}.$$

其射影速度为 $ds_{\rm FS}/dt=\Delta H/\hbar=\|\dot n\|/2$。 同一几何路径和闭路面积在重新参数化后不变，而经过的钟时可以改变。

**证明。**

写 $H=h_0I+(\hbar/2)\sigma_\omega$。 Pauli 对易式将 $\dot P=-i[H,P]/\hbar$ 化为 $\dot n=\omega\times n$。 上一分解给其全部解 $\omega=n\times\dot n+\lambda n$。 纯态方差为

$$(\Delta H)^2=\frac{\hbar^2}{4} \bigl(\|\omega\|^2-(\omega\cdot n)^2\bigr) =\frac{\hbar^2}{4}\|\dot n\|^2.$$

度量公式给速度。取 $t=a\tau$、$a>0$， 新生成元 $H'(\tau)=aH(a\tau)$ 描述相同轨迹， 总参数时长由 $T$ 变成 $T/a$，面积不变，证明不可唯一识别。

$\square$

### 12.1　正性、正交与“存在”的类型

#### 命题 12.5：两个不同的正交关系

Bloch 方向 $n\cdot m=0$ 当且仅当 $\operatorname{Tr}(P_nP_m)=1/2$； 幅度射线正交当且仅当 $\operatorname{Tr}(P_nP_m)=0$，也即 $m=-n$。 复二维幅度空间不存在三个非零两两正交的幅度。

**证明。**

前两项代入 $\operatorname{Tr}(P_nP_m)=(1+n\cdot m)/2$。 最后，非零正交向量线性无关，而复维数仅为二。 因此三根相互正交的是比较方向，不是三个相互排斥的 qubit 纯态。

$\square$

对指定的二路径基，$\rho_r=(I+r\cdot\sigma)/2$ 的可预测性和干涉可见度可定义为

$$P=|r_z|,\qquad V=\sqrt{r_x^2+r_y^2},\qquad P^2+V^2=\|r\|^2\le1.$$

证明只需将 $\rho_r$ 的对角差与非对角条目写出；混合态和基的选择都会改变这些数值。 一个纯态可同时有非零 $P,V$，所以方向本身没有被唯一分成“粒子时刻”与“波时刻”。 与记忆的纠缠和条件读出会进一步改变可访问的干涉关系。[\[21\]](#ref-ding), [\[22\]](#ref-englert), [\[23\]](#ref-siddiqui)

#### 命题 12.6：幅度乘性不能不分类型地施加于全部事件

若对全部事件要求 $p(XY)=p(X)p(Y)$，并要求每个非零正投影都有正读数， 则任何含两个非零正交投影的量子事件代数都不满足该要求。

**证明。**

取 $P,Q\ne0$、$PQ=0$。左边为 $p(0)=0$，右边严格为正，矛盾。

$\square$

因此主候选的 $p$ 是基本幅度比较的读出。 事件正性、过程完全正性与记录 Gram 保持是它们各自的二元、三元相容关系， 不能把不同类型的条件压成同一个无区别的乘法等式。

<a id="section-13"></a>

## 13　态的三元相位：第三个方向保留了哪一份关系

**本区域的输入。**

沿用已经构造的复二维幅度空间 $H_J$， 第一槽共轭线性、第二槽线性的内积 $h$， 三维实纯部 $(W,B,\times)$， 以及

$$\sigma_a\sigma_b=B(a,b)I+i\sigma_{a\times b},\qquad P_a=\frac{I+\sigma_a}{2}\quad(q(a)=1).$$

以下没有新增基础公理。 为每个单位方向 $a$ 选择一个归一射线代表 $\psi_a$， $P_a=|\psi_a\rangle\langle\psi_a|$。 记

$$g_{ab}=h(\psi_a,\psi_b),\qquad p_{ab}=|g_{ab}|^2=\operatorname{Tr}(P_aP_b),\qquad \mathcal B_{abc}=g_{ab}g_{bc}g_{ca}. \tag{Q21-B1}$$

#### 定理 13.1：三元幅度的坐标无关公式

对任意三个单位方向 $a,b,c\in W$，

$$\boxed{\quad \mathcal B_{abc} =\operatorname{Tr}(P_aP_bP_c) =\frac{1+B(a,b)+B(b,c)+B(c,a)+iB(a,b\times c)}4 . \quad} \tag{Q21-B2}$$

改变各射线代表的相位不改变 $\mathcal B_{abc}$； 交换其中两个方向使其复共轭。

**证明。**

秩一投影的作用为 $P_a x=h(\psi_a,x)\psi_a$。 连续复合三个投影，再取迹，得到 $\operatorname{Tr}(P_aP_bP_c) =h(\psi_a,\psi_b)h(\psi_b,\psi_c)h(\psi_c,\psi_a)$。 另一方面，Pauli 公式给

$$\operatorname{Tr}I=2,\quad \operatorname{Tr}\sigma_a=0,\quad \operatorname{Tr}(\sigma_a\sigma_b)=2B(a,b),\quad \operatorname{Tr}(\sigma_a\sigma_b\sigma_c)=2iB(a\times b,c).$$

展开 $(I+\sigma_a)(I+\sigma_b)(I+\sigma_c)/8$ 并逐项取迹， 即得 (Q21-B2)；三重积的循环对称性给 $B(a\times b,c)=B(a,b\times c)$。 若 $\psi_a'=e^{i\alpha_a}\psi_a$， 则 $g_{ab}'=e^{i(\alpha_b-\alpha_a)}g_{ab}$， 三个因子相乘时相位全部相消。 最后，公式中的实部对三个方向对称，而三重积在一次交换下变号。

$\square$

#### 定理 13.2：复二维 Gram 约束与二元数据的剩余歧义

令 $G=(g_{jk})_{j,k\in\{a,b,c\}}$。则

$$G\ge0,\qquad \operatorname{rank}G\le2,\qquad 0=\det G =1-p_{ab}-p_{bc}-p_{ca}+2\operatorname{Re}\mathcal B_{abc}. \tag{Q21-B3}$$

因而

$$\operatorname{Re}\mathcal B_{abc} =\frac{p_{ab}+p_{bc}+p_{ca}-1}{2},\qquad |\mathcal B_{abc}|^2=p_{ab}p_{bc}p_{ca}, \tag{Q21-B4}$$

$$(\operatorname{Im}\mathcal B_{abc})^2 =p_{ab}p_{bc}p_{ca} -\frac{(p_{ab}+p_{bc}+p_{ca}-1)^2}{4}. \tag{Q21-B5}$$

所以三份二元概率确定三元幅度的实部及虚部绝对值， 一般不确定虚部符号。

**证明。**

对任意 $\lambda_a,\lambda_b,\lambda_c\in\mathbb C$，

$$\sum_{j,k}\overline{\lambda_j}g_{jk}\lambda_k =h\!\left(\sum_j\lambda_j\psi_j,\sum_k\lambda_k\psi_k\right)\ge0.$$

三向量位于复二维空间，故 Gram 矩阵秩不超过二。 展开行列式，三个对角元给 $1$， 三项交换给 $-|g_{ab}|^2-|g_{bc}|^2-|g_{ca}|^2$， 两个三循环给 $g_{ab}g_{bc}g_{ca}+\overline{g_{ab}g_{bc}g_{ca}}$。 这证明 (Q21-B3)，第一条推论随即成立。 取乘积的绝对值平方得到第二式，再用 $|\mathcal B|^2=(\operatorname{Re}\mathcal B)^2+ (\operatorname{Im}\mathcal B)^2$ 即得最后一式。

$\square$

#### 命题 13.3：相同全部二元概率、相反三元方向

取 $(e_1,e_2,e_3)$ 为 $W$ 的定向正交单位基， $e_1\times e_2=e_3$。 两组三元组

$$(a,b,c)=(e_1,e_2,e_3),\qquad (a',b',c')=(e_1,e_2,-e_3)$$

的三份二元转移概率均为 $1/2$，但

$$\mathcal B_{abc}=\frac{1+i}{4},\qquad \mathcal B_{a'b'c'}=\frac{1-i}{4}. \tag{Q21-B6}$$

这里三根 Bloch 轴两两正交，三个射线代表却没有两两正交： 其两两内积绝对值都为 $1/\sqrt2$。

**证明。**

两组三元组的不同方向内积均为零， 故 $p=(1+B)/2=1/2$。 第一组三重积为 $1$，第二组为 $-1$， 代入 (Q21-B2) 即得。 最后一句由 $|g|^2=p=1/2$ 成立。

$\square$

**关系的关系。**

当三个重叠均非零，定义

$$u_{ab}=\frac{g_{ab}}{|g_{ab}|},\qquad \kappa_{abc}=u_{ab}u_{bc}u_{ca} =\frac{u_{ab}u_{bc}}{u_{ac}} =\frac{\mathcal B_{abc}}{|\mathcal B_{abc}|}. \tag{Q21-B7}$$

第二个等号使用 $u_{ca}=u_{ac}^{-1}$。 因此 $\kappa$ 比较的是两条二元比较链： 先 $a\to b\to c$，以及直接 $a\to c$。 它是相位代表无关的三元闭路量； 若某个重叠为零，$\mathcal B$ 仍有定义， 但 $u$ 与 $\kappa$ 在该闭路上不再有定义。

#### 命题 13.4：把第三点设为端点会退化闭路

若 $c=a$ 或 $c=b$，则

$$\mathcal B_{aba}=\mathcal B_{abb}=p_{ab}\ge0 . \tag{Q21-B8}$$

当 $p_{ab}>0$ 时相应 $\kappa=1$； 当 $p_{ab}=0$ 时相应归一相位未定义。 这项端点选择不能确定任意第三方向的闭路不变量。

**证明。**

若 $c=a$，则 $g_{ab}g_{ba}g_{aa}=|g_{ab}|^2$； 若 $c=b$ 同理。 或者用投影幂等性和迹循环性得到同一结果。 固定 $a=e_1,b=e_2$ 后，上一命题的 $c=\pm e_3$ 已给不同闭路不变量， 而两端点及它们的二元概率完全不变。

$\square$

第三点可以是整体内部已有的参考态、记录态或经过确定操作产生的态。 若使用既有叉积，还可在 $a\times b\ne0$ 时明确规定 $`c_*=(a\times b)/\|a\times b\|`$； 这是一个特定的内部构造，不能代替所有实际闭路的第三点。 选择 $c=a$ 或 $c=b$ 是合法的退化选择， 它把相应三元相位压为零，并没有从两个端点唯一恢复一般的闭路面积。 相位、长度或面积公式中仍没有时间参数， 故这些运动学恒等式本身不推出“场等于时间”。

**与过程相关矩阵的严格区别。**

本节 $G$ 是同一复二维空间中纯态代表的 Gram 矩阵， 所以 $\operatorname{rank}G\le2$、三个向量的行列式等于零。 过程节的 $(\gamma_{jk})$ 来自一般内部环境记录； 其秩可以大于二，三阶行列式只须非负。 环境内生不把它自动压成同一个单 qubit， 也不把一般过程三元不等式改成这里的等式。

**外部结果的准确角色。**

Magnot 的 2026 年论文   *Remarks on pairwise comparisons, transition amplitudes, and qubit states*   以既定的 $\mathbb C^2$ qubit 为起点， 讨论复振幅、转移概率、相位比较与 Bargmann 三角不变量之间的对应， 以及 Gram 正性与秩约束。 它为本节提供非常直接的研究对应， 没有从不含量子结构的前件完成量子力学重建。 上面的公式均由本轮已声明的 Pauli 和 Hilbert 结构逐项证明。[\[24\]](#ref-magnot)

<a id="section-14"></a>

## 14　存在、面积与最小内部表示

本节继承项目 R5-006 的纤维精化、正核与 Schur 秩判据，[\[25\]](#ref-r5006) 不把这些既有结果另计为本稿新发现。 本稿将它们与三种不同的量子面积、最新有限获取稿的线性特征反例连接， 以检验“表达存在必然增加维数”的准确范围。

**输入：** 已取得的复内积结构；或另行给定的 Hermitian 关系核与全部有限正性。 **输出：** 最小关系表示、面积与独立余量、严格增秩判据。 此分支不单独产生复数、Born 接口、物理复合律或时间律。

### 14.1　面积的三个类型

#### 定义 14.1：振幅面积

内积 $h$ 对第二变量复线性，$q(x)=h(x,x)$。 定义复 Gram 面积与实 Gram 面积

$$\mathcal S_{\mathbb C}(x,y)^2=q(x)q(y)-|h(x,y)|^2,\qquad \mathcal S_{\mathbb R}(x,y)^2=q(x)q(y)-(\operatorname{Re}h(x,y))^2.$$

前者是复外积的平方范数；后者把同一振幅空间视为实内积空间。

#### 定理 14.2：面积读取旧线之外的成分

若 $x\ne0$，令

$$y_\parallel=\frac{h(x,y)}{q(x)}\cdot x,\qquad y_\perp=y-y_\parallel.$$

这里 $\alpha\cdot x$ 是 $J$ 定义的左复标量作用，不能改读为四元数右乘。 则

$$h(x,y_\perp)=0,\qquad q(y)=\frac{|h(x,y)|^2}{q(x)}+q(y_\perp),\qquad \mathcal S_{\mathbb C}(x,y)^2=q(x)q(y_\perp).$$

特别地，$\mathcal S_{\mathbb C}(x,y)=0$ 当且仅当 $x,y$ 复线性相关。 它不等价于 $q(x)=0$ 或 $q(y)=0$。

**证明。**

第二变量线性给 $h(x,y_\parallel)=h(x,y)$，故得到正交分解。 展开 $q(y_\parallel+y_\perp)$，交叉项为零， 且 $q(y_\parallel)=|h(x,y)|^2/q(x)$。 代回定义即得。若 $x=0$，面积本来为零；若 $x\ne0$， 正定性使零面积等价于 $y_\perp=0$。

$\square$

#### 命题 14.3：实、复与 Bloch 面积不能互换

有

$$\mathcal S_{\mathbb R}(x,y)^2 =\mathcal S_{\mathbb C}(x,y)^2+(\operatorname{Im}h(x,y))^2.$$

单位振幅 $x$ 与 $ix$ 的实面积为 $1$，复面积为 $0$， 但它们代表同一量子射线。 对单位量子比特振幅 $x,y$，对应 Bloch 方向为 $n,m$， 记 $p=|h(x,y)|^2$，则

$$\mathcal S_{\mathbb C}(x,y)^2=1-p=\frac{1-n\cdot m}{2}, \qquad \lVert n\wedge m\rVert^2=4p(1-p).$$

**证明。**

第一式由 $|h|^2=(\operatorname{Re}h)^2+(\operatorname{Im}h)^2$ 得到。 $h(x,ix)=i$，而 $ix$ 与 $x$ 的秩一投影相同。 最后使用 $p=(1+n\cdot m)/2$ 与 $\lVert n\wedge m\rVert^2=1-(n\cdot m)^2$。

$\square$

取 $x=y\ne0$，已有非零存在而零复面积。 若要求不同纯态，可取正交振幅；它们的 Bloch 方向互反， 因此 Bloch 面积为零，而复振幅面积最大。 故任何“面积即存在”的定义首先必须说明对象类型与所用面积； 上述几种既有面积均不与单元的非零存在等价。

#### 命题 14.4：中央响应面积的 Pauli 分支

令 $n,m\in\mathbb R^3$，$A=n\cdot\sigma$、$B=m\cdot\sigma$，并置

$$A\circ B=(AB+BA)/2,\qquad D_{\rm P}=i(AB-BA)/2.$$

则

$$D_{\rm P}=-(n\times m)\cdot\sigma,\qquad D_{\rm P}^2=A^2B^2-(A\circ B)^2 =\bigl(\lVert n\rVert^2\lVert m\rVert^2-(n\cdot m)^2\bigr)I.$$

**证明。**

Pauli 乘法为 $(n\cdot\sigma)(m\cdot\sigma) =(n\cdot m)I+i(n\times m)\cdot\sigma$。 交换 $n,m$，分别相加、相减，再用 $(v\cdot\sigma)^2=\lVert v\rVert^2I$，即得全部等式。

$\square$

这是项目中央响应面积在明确矩阵模型中的实现； 此处采用 $A\circ B-iD_{\rm P}=AB$ 的项目乘法恢复约定。 响应 $D_{\rm P}=0$ 不要求 $A=0$ 或 $B=0$。 新稿的较弱 JC 载体证明另有完整的源条件，不能从本例反向推广到任意未知响应。

### 14.2　无需先指定外在载体的最小 Gram 实现

#### 定理 14.5：关系决定最小生成空间

给定 $m$ 阶 Hermitian 正半定矩阵 $G$，令

$$\mathcal H_G=\mathbb C^m/\ker G,\qquad \langle[c],[d]\rangle_G=c^*Gd.$$

这是正定内积空间，$v_i=[e_i]$ 满足

$$\langle v_i,v_j\rangle_G=G_{ij},\qquad \dim_{\mathbb C}\mathcal H_G=\operatorname{rank}G.$$

任意具有相同 Gram 数据的向量族 $w_i$，均给出唯一的标签保持酉同构

$$[c]\longmapsto\sum_i c_iw_i: \mathcal H_G\longrightarrow\operatorname{span}\{w_i\}.$$

**证明。**

正半定性给 $`c^*Gc=0\iff Gc=0`$，例如用 $G$ 的正平方根即可验证。 所以配对与代表元无关，且商上正定。 标准基的像张成商空间，秩–零度公式给维数。 另一实现的组合范数恰为 $`\lVert\sum c_iw_i\rVert^2=c^*Gc`$， 故线性映射的零核恰为 $\ker G$，能下降为等距映射。 其像按定义为全部张成空间；标签像已确定，所以唯一。

$\square$

对无限标签集，先在有限支撑自由空间上使用同一正核， 商去零长度部分，再按需要完成，即得相应核表示。 所有有限正性是明确输入；它不是仅检查最初标签的任意两两正性。 这是成熟的正核表示构造，参见 Aronszajn 的原论文[\[26\]](#ref-q022-aronszajn)。

#### 命题 14.6：过程必须保持同一零核

系数线性操作 $M:\mathbb C^m\to\mathbb C^m$ 下降为 $\mathcal H_G$ 上操作， 当且仅当 $M\ker G\subseteq\ker G$。 若 $`M^*GM=G`$，则它保持全部二元关系，并自动下降为酉操作。 若 $M,N$ 都保持关系，则 $MN$ 也保持关系。

**证明。**

下降等价于 $c-d\in\ker G\Rightarrow M(c-d)\in\ker G$。 矩阵等式给 $`\langle Mc,Md\rangle_G=c^*M^*GMd=c^*Gd`$， 从而零核条件自动成立，商映射为等距自映射。 商空间有限维，所以等距自映射满射。 最后 $`(MN)^*G(MN)=N^*(M^*GM)N=N^*GN=G`$。

$\square$

### 14.3　最小增维判据及其信息边界

#### 定理 14.7：新关系的最小独立余量

设旧表 $G\ge0$，新关系向量为 $g\in\mathbb C^m$，新元平方读出为 $s\ge0$。 则

$$
\widetilde G=\begin{pmatrix}G&g\\g^*&s\end{pmatrix}\ge0
 \iff
 g\in\operatorname{ran}G,\quad
 \delta=s-g^*G^+g\ge0.
$$

成立时

$$\operatorname{rank}\widetilde G=\operatorname{rank}G+\mathbf1_{\{\delta>0\}}.$$

在最小旧空间中，新增元可以取成

$$v_{\rm new}=[G^+g]+\sqrt{\delta}\,e_\perp,$$

其中 $\delta=0$ 时不加入 $e_\perp$， $\delta>0$ 时只需一个正交单位元。

**证明。**

若 $z\in\ker G$，在 $(tz,1)$ 上的块二次型为 $`s+2\operatorname{Re}(\bar t z^*g)`$。 若 $`z^*g\ne0`$，选相位并放大 $t$ 即得负值。 故 $g\perp\ker G$，即 $g\in\operatorname{ran}G$。 置 $y=G^+g$，有 $Gy=g$，并且

$$\binom{x}{t}^{\!*}\widetilde G\binom{x}{t} =(x+yt)^*G(x+yt)+\delta|t|^2.$$

取 $x=-yt$ 得必要性；同式给充分性。 可逆变量替换将矩阵合同到 $G\oplus[\delta]$，给出秩式。 实现公式中的旧配对为 $GG^+g=g$，范数为 $`g^*G^+g+\delta=s`$，故精确保持全部数据。

$\square$

此判据与 R5-006 §4.1 一致。 增维说的是 *最小生成线性空间* ； 若整体已经有尚未使用的正交方向，就可在整体内部使用它。 当旧振幅已张成 $\mathbb C^2$，任何新的量子比特振幅仍有 $\delta=0$， 即便它是此前未列出的不同纯态。

若旧向量独立，则 $\det\widetilde G=(\det G)\delta$； 只有一个旧元时，恰是 $\mathcal S_\mathbb C(x,y)^2=q(x)\delta$。 所以面积可以读取相对独立余量，而不等同于绝对存在。

#### 命题 14.8：线性残差不等于新增信息

令 $X$ 均匀分布于 $[-1,1]$，在实 $L^2$ 中取

$$V=\operatorname{span}\{1,X\},\qquad S=L^2(\sigma(X)),\qquad z=X^2.$$

则

$$\operatorname{dist}(z,V)^2=\frac4{45}>0,\qquad \operatorname{dist}(z,S)^2=0.$$

**证明。**

有 $\mathbb E X=\mathbb E X^3=0$、 $\mathbb E X^2=1/3$、 $\mathbb E X^4=1/5$。 故对实数 $a,b$，

$$\mathbb E(X^2-a-bX)^2 =(a-\tfrac13)^2+\frac{b^2}{3}+\frac4{45}.$$

最小值为 $4/45$。 另一方面 $X^2$ 是旧读口 $X$ 的确定函数，属于 $S$。

$\square$

在三个标签 $1,X,X^2$ 上，关系表精确为

$$
G_3=\begin{pmatrix}
1&0&1/3\\0&1/3&0\\1/3&0&1/5
\end{pmatrix},\qquad
\det G_3=\frac4{135}>0.
$$

旧 $G=\operatorname{diag}(1,1/3)$、新 $g=(1/3,0)^T$、$s=1/5$，故 $\delta=1/5-1/9=4/45$。 这是一个明确的二维到三维最小线性提升，仍没有超出旧读口 $X$ 的信息。

该反例来自本次项目有限获取稿 §12.2。[\[27\]](#ref-energy22) 它严格说明：正的线性余量迫使扩充指定特征空间， 却不迫使增加完整旧读口的信息。 一般地，目标 $f:X\to Y$ 能由旧读口 $q:X\to S$ 恢复， 当且仅当 $f$ 在每个 $q$-纤维上为常数； 存在唯一 $\bar f:q(X)\to Y$ 使 $f=\bar f\circ q$； 直接定义 $\bar f(q(x))=f(x)$ 即证明其必要充分性。 这与 Gram 秩判据属于不同的类型。

<a id="section-15"></a>

## 15　有限量子理论的完整数学完成及实际接口

核心候选选择了一个复二维幅度块。下面先定义其有限数学完成， 再证明状态、概率、过程、记录和连续可逆演化的标准形式。 数学完成中的对象可由内部有限构造得到；某个原实际世界是否供应全部这些对象，是另一个命题。

### 15.1　本区域的输入与输出

$$\mathsf D_0:\quad H_J\cong\mathbb C^2,\quad M_2=\operatorname{End}_{\mathbb C}(H_J),$$

$$\mathsf D_1:\quad \mathsf{QFin}:= \langle M_2,\mathbb C\rangle_{\otimes_{\mathbb C},\ \oplus,\ P\mathcal M P\ (P\ne0)}, \qquad\mathcal M_+:=\{X=X^*: \langle v,Xv\rangle\ge0\ \forall v\},$$

$$\mathsf D_2:\quad \operatorname{State}(\mathcal M)= \{\omega\in\mathcal M^*:\omega(\mathcal M_+)\ge0,\ \omega(I)=1\}, \quad\operatorname{Eff}(\mathcal M)=[0,I],$$

$$\Phi\in\operatorname{Hom}_{\mathbb C}(M_d,M_e),\qquad \mathsf P_{\rm ref}(\Phi):\quad \forall n\ge0,\quad(\Phi\otimes\operatorname{id}_{2^n})((M_d\otimes M_{2^n})_+)\subseteq (M_e\otimes M_{2^n})_+,$$

$$
\begin{gathered}
T:\mathbb R\longrightarrow\operatorname{End}_{\mathbb C}(M_d),\qquad \mathsf P_{\rm time}(T):\\
T_{s+t}=T_sT_t\ (s,t\in\mathbb R),\quad T_0=\operatorname{id},\quad t\mapsto T_t\text{ 连续},\\
T_t\text{ 满足 }\mathsf P_{\rm ref}\text{ 且保迹}\qquad(t\in\mathbb R).
\end{gathered}
$$

$$\mathsf{QFin}=\left\{\bigoplus_{j=1}^rM_{d_j}(\mathbb C):r,d_j\in\mathbb N_{\ge1}\right\}, \quad\omega(X)=\sum_j\operatorname{Tr}(\rho_jX_j), \quad\Phi(X)=\sum_\mu K_\mu XK_\mu^*,$$

$$T_t(\rho)=e^{-itH/\hbar}\rho e^{itH/\hbar}\qquad(H=H^*,\ \hbar>0).$$

上面 $\mathsf D_i$ 是数学完成与对象类型的定义， $\mathsf P_{\rm ref},\mathsf P_{\rm time}$ 是作用在待识别原过程上的条件。 不能把定义某类良好过程，改写成所有原过程已自动属于该类。 若原资料要识别为标准有限量子力学，至少应逐项绑定以下四组接口：

| 接口 | 数学关系 | 原来源须说明的对象 |
|:---|:---|:---|
| 原事件绑定 | $p_h(k)=\omega_h(E_k)$，$E_k\ge0$，$\sum_kE_k=I$ | 实际准备、全部结果、失败与归一化，及其是否经所选相位不变表示下降。 |
| 联合绑定 | $\mathcal M_{AB}\cong\mathcal M_A\otimes_\mathbb C\mathcal M_B$，使用完整正锥 | 同一复中心、真实相关准备、原系统分解与观察者记录。 |
| 完整过程绑定 | 原箭头复线性下降，全部迭代参考满足 $\mathsf P_{\rm ref}$ | 每次旁接的都是整个箭头，保留环境、记录、失败与仍合法未来。 |
| 时间与更新绑定 | 可逆钟流满足 $\mathsf P_{\rm time}$；理想投影分支有指定无扰动条件 | 实际时钟、时间单位、具体生成元及测量装置性质。 |

这些接口不计入本轮六组核心输入，也没有被它们全部证明。 项目 C139 对完整参考递归已有专门的来源条件与误差版本，正说明此处不能只写“再加入一个环境”就略过实际供应。[\[28\]](#ref-c139cp)

#### 定理 15.1：有限矩阵代数完成

上面的 $\mathsf{QFin}$ 恰为全部有限直和复矩阵代数。 若原联合是非零复含幺结合 $`*`$-代数，并有两个同复中心的可交换含幺 $`*`$-嵌入 $M_m(\mathbb C),M_n(\mathbb C)$， 且它们的乘积线性张成全部联合代数，则联合代数同构于 $M_{mn}(\mathbb C)$。

**证明。**

$M_2^{\otimes k}=M_{2^k}$。对任意 $d$，选 $2^k\ge d$，取秩 $d$ 投影的角便得 $M_d$； 有限直和给全部显示代数。反向，张量、直和与投影角都留在这一类中。 对于原联合，映射 $A\otimes B\mapsto\iota_A(A)\iota_B(B)$ 为含幺 $`*`$-同态且由张成条件满射。 $M_{mn}$ 没有非平凡双边理想：任意非零理想元素有一个非零矩阵条目， 左右乘矩阵单位便得到所有矩阵单位。因此该同态核只能是零或全部；单位不被消掉，故核为零。

$\square$

#### 定理 15.2：密度、观测与平方律

对 $\mathcal M=\bigoplus_jM_{d_j}(\mathbb C)$，每个归一正线性泛函唯一为

$$\omega(X)=\sum_j\operatorname{Tr}(\rho_jX_j),\quad \rho_j\ge0,\quad\sum_j\operatorname{Tr}\rho_j=1.$$

单块的纯态为秩一投影；一般纯态只占一个块且在该块秩一。 POVM $E_k\ge0,\sum_kE_k=I$ 给归一概率 $p_k=\omega(E_k)$。 对正交投影测量和纯态，$p_k=\|P_k\psi\|^2$。

**证明。**

每块的非退化迹配对给唯一自伴 $\rho_j$。在所有向量秩一投影上非负等价于各 $\rho_j\ge0$， 单位评价给总迹一。反向由正算子迹乘积非负成立。 若有两个正本征权重，可作一正一负的小扰动并保持归一，故不是极点； 若仅一个权重为一，其秩一支撑不能非平凡分解为正态凸组合，故为极点。 POVM 式的非负与归一直接求和得到；纯投影概率由 $\operatorname{Tr}(|\psi\rangle\langle\psi|P_k)=\langle\psi,P_k\psi\rangle=\|P_k\psi\|^2$ 得出。

$\square$

#### 定理 15.3：锐读出的共同相容性有确定条件

对两个正交投影 $P,Q$，存在四个正效果 $G_{ij}$、$i,j\in\{0,1\}$， 总和为 $I$ 且满足

$$G_{10}+G_{11}=P,\qquad G_{01}+G_{11}=Q,$$

当且仅当 $PQ=QP$。

**证明。**

若 $0\le A\le P$，则对 $v\in\ker P$ 有 $0\le\langle v,Av\rangle\le0$；正平方根给 $Av=0$， 故 $PA=AP=A$。 于是 $PG_{11}=G_{11}=G_{11}P$； $G_{01}\le I-P$ 又给 $PG_{01}=G_{01}P=0$。 由 $Q=G_{11}+G_{01}$ 得 $PQ=QP=G_{11}$。 反向，若 $P,Q$ 交换，取 $G_{11}=PQ$、$G_{10}=P(I-Q)$、 $G_{01}=(I-P)Q$、$G_{00}=(I-P)(I-Q)$； 这些都是正投影且有要求的边缘和。

$\square$

所以允许更大的联合系统，并不自动使原来的全部锐读出共同可测。 替换原效果或降低读出精度，可以定义另一组相容任务；原投影是否相容仍由上述等式判定。 这里的等价仅针对锐投影，不把一般 POVM 的非交换直接等同于不可联合测量。

#### 定理 15.4：递归二元参考充分恢复完全正性

对复线性 $\Phi:M_d\to M_e$，以下三项等价：

1.  $\mathsf P_{\rm ref}(\Phi)$ 成立；

2.  $C_\Phi=(\Phi\otimes\operatorname{id}_d)(|\Gamma\rangle\langle\Gamma|)\ge0$， 其中 $|\Gamma\rangle=\sum_{i=1}^d|i\rangle|i\rangle$；

3.  存在有限矩阵族 $K_\mu$，使 $`\Phi(X)=\sum_\mu K_\mu XK_\mu^*`$。

而 $\Phi$ 迹不增、保迹，分别等价于 $`\sum_\mu K_\mu^*K_\mu\le I`$、$=I$。

**证明。**

选 $2^n\ge d$，将 $\mathbb C^d$ 等距嵌入参考 $\mathbb C^{2^n}$。 对嵌入后的 $|\Gamma\rangle\langle\Gamma|$ 用第一项，再压回该参考子空间，得到第二项。 将正矩阵 $C_\Phi$ 分解成有限秩一和 $\sum_\mu|v_\mu\rangle\langle v_\mu|$， 按输出、输入两个指标把 $v_\mu$ 重排成矩阵 $K_\mu$。 比较 $C_\Phi$ 中每个输入矩阵单位的系数即得第三项。 反向，任意参考上的 $`\sum_\mu(K_\mu\otimes I)X(K_\mu^*\otimes I)`$ 都保持正性。 最后 $`\operatorname{Tr}\Phi(X)=\operatorname{Tr}[X\sum_\mu K_\mu^*K_\mu]`$， 在全部正 $X$ 上比较迹即得相应算子不等式或等式。

$\square$

这是 Choi–Kraus 表示的完整有限证明，其标准等价式见 Watrous 定理 2.22。[\[29\]](#ref-watrous) 对直和源 $\bigoplus_iM_{d_i}$ 与目标 $\bigoplus_jM_{e_j}$，完全正过程恰为

$$\Phi((X_i)_i)_j=\sum_{i,\mu}K_{ji\mu}X_iK_{ji\mu}^*, \qquad K_{ji\mu}:\mathbb C^{d_i}\to\mathbb C^{e_j}.$$

证明只需将输入块嵌入、输出块压缩与原箭头复合，对每个分量应用单块定理； 反向是这些完全正分量的有限和。 保迹条件为每个 $i$ 的 $`\sum_{j,\mu}K_{ji\mu}^*K_{ji\mu}=I_{d_i}`$， 迹不增将等号换成 $\le$。 只要求局部正性不够：转置 $T$ 保正，但 $(T\otimes\operatorname{id})(|\Gamma\rangle\langle\Gamma|)$ 是交换算子， 在反对称二体向量上取负本征值。二元参考的递归量词不能删除。

#### 定理 15.5：内部仪器与记录的酉实现

若分支 $`\Phi_k(X)=\sum_\mu K_{k\mu}XK_{k\mu}^*`$ 满足 $`\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I`$，则

$$V\psi=\sum_{k,\mu}K_{k\mu}\psi\otimes|k,\mu\rangle$$

是等距映射；读取内部记录投影 $Q_k=\sum_\mu|k,\mu\rangle\langle k,\mu|$ 并取环境偏迹，恰得到原分支 $\Phi_k$。 该等距映射在适当有限扩张中可延为酉算子。

**证明。**

内积展开给 $`V^*V=I`$。展开 $`VX V^*`$，记录投影保留同一 $k$， 偏迹只保留相同 $\mu$，得到给定 Kraus 和。 把输入与输出放进一个足够大的等维空间，补全等距像的正交基，就得到酉扩张。

$\square$

#### 定理 15.6：理想投影更新的准确条件

设完全正分支 $\Phi$ 的效果为投影 $P$，即 $`\sum K_\mu^*K_\mu=P`$， 并且 $\Phi$ 固定每个支撑在 $P$ 内的归一态。 则 $\Phi(X)=PXP$。成功概率非零时，条件态为 $P\rho P/\operatorname{Tr}(\rho P)$。

**证明。**

若 $P=0$，则全部 $K_\mu=0$，结论直接成立；以下设 $P\ne0$。 对 $x\in\ker P$，$\sum\|K_\mu x\|^2=0$，故 $K_\mu=K_\mu P$。 对每个 $x\in\operatorname{im}P$ 的秩一态，输出仍为该秩一态， 正和的每一项必须留在同一条线，故 $K_\mu x$ 与 $x$ 平行。 线性算子若保持一个空间的每条线，则在其上为标量：用两个独立向量及其和即可证明。 所以 $K_\mu=c_\mu P$，效果式给 $\sum|c_\mu|^2=1$，遂得结论。

$\square$

只固定某组基态不够：在 $P$ 内退相干的通道会破坏其叠加态，仍可保持那些基态。

#### 定理 15.7：连续可逆过程给薛定谔形式

固定单块 $M_d$ 上满足 $\mathsf P_{\rm time}$ 的群，必为

$$T_t(\rho)=U_t\rho U_t^*,\qquad U_t=e^{-itH/\hbar},\quad H=H^*.$$

因此 $i\hbar\dot\psi=H\psi$、$\dot\rho=-i[H,\rho]/\hbar$。

**证明。**

先取任一 $T$ 及其完全正逆 $S$，令其 Kraus 为 $A_i,B_j$。 $ST=\operatorname{id}$ 的 Choi 矩阵秩一，故各 $B_jA_i$ 都为单位矩阵的标量倍。 某一倍数非零，所以对应 $B_{j_0}$ 可逆；于是所有 $A_i$ 均互相成比例， $T$ 只有一个有效 Kraus 矩阵。保迹迫使该矩阵酉。 故每个 $T_t$ 为矩阵代数的 $`*`$-自同构。

有限维连续矩阵一参数群可写成 $T_t=e^{t\delta}$：在单位附近取连续矩阵对数， 用群律、交换性和有理细分得到局部对数对 $t$ 线性，再以群律延到全部实数。 对乘法恒等式求导得 $\delta(XY)=\delta(X)Y+X\delta(Y)$。 用矩阵单位定义 $B=\sum_i\delta(E_{i1})E_{1i}$， 对 $\delta(E_{kl}E_{i1})$ 求和直接得 $[B,E_{kl}]=\delta(E_{kl})$，所以 $\delta=[B,\cdot]$。 $`*`$ 保持性使 $`B+B^*`$ 为标量，去掉该标量后 $B$ 反自伴，写成 $B=-iH/\hbar$ 即得。

$\square$

具体 $H$、与实际时钟的对应及作用量单位 $\hbar$ 没有由上述代数分类选择。 同一静态结构允许许多不同的可逆流。

#### 命题 15.8：标准结构的若干直接后果

在该数学完成中，局部保迹过程不改变另一方边缘态； 任意两个自伴量满足 Robertson 不等式；标准二体纯态可以纠缠。

**证明。**

局部无信号性由 $\operatorname{Tr}_B[(\operatorname{id}\otimes\Phi)(\rho_{AB})]=\operatorname{Tr}_B\rho_{AB}$， 将 Kraus 和与 $`\sum K^*K=I`$ 代入即可。 对 $`\langle X,Y\rangle_\rho=\operatorname{Tr}(\rho X^*Y)`$ 用 Cauchy–Schwarz， 取中心化自伴 $\Delta A,\Delta B$，便得 $(\Delta_\rho A)^2(\Delta_\rho B)^2\ge|\operatorname{Tr}(\rho[A,B])/(2i)|^2$。 最后 $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$ 的约化态为 $I/2$， 不可能是纯乘积；其秩一投影也不能是乘积态的凸组合，因为正和的各项必须落在同一条射线上。

$\square$

这些结论均来自明确的有限完成。若只供应可分离联合锥，也能保留全部局域 qubit， 却不会自动得到纠缠准备。无限维位置、动量、场方程与引力仍未由本候选恢复； 例如有限矩阵不可能满足 $[X,P]=i\hbar I$、$\hbar\ne0$，因为取迹立即矛盾。

<a id="section-16"></a>

## 16　从局部球到最小完整表示：何时扩张，何时停止

本节固定已识别的有限复矩阵接口，回答一个独立问题： 原表示不足以完成指定任务时，最少应补什么；补齐以后是否仍被迫无限扩张。 这里的矩阵状态、迹读出、复合或完全正过程均为相应区域的明确输入。 这些条件性定理不反向承担从原始候选到全部实际量子接口的来源义务。

| 对象 | 维数或不变量 | 准确含义 |
|:---|:---|:---|
| 纯 qubit 态 | $\mathbb CP^1\cong S^2$，内在实维 $2$ | 三维 Bloch 坐标中的单位球面；不是三个独立态矢量。 |
| 一般 qubit 态 | 闭球 $B^3$，实仿射维 $3$ | 保存全部局部效果统计。 |
| 振幅代表 | $S^3\to\mathbb CP^1$ 的 $U(1)$ 纤维 | 相同射线有相位不同的代表；这不是额外局部态。 |
| 纯化实现 | 最小环境复维 $\operatorname{rank}\rho$ | 针对同一个密度态的纯态实现任务。 |
| 过程实现 | 最小环境复维 $\operatorname{rank}J_\Phi$ | 针对同一个完整通道的等距实现任务。 |
| 未来读口 | $\dim V_\infty-\dim V_0$ | 固定菜单下所缺少的独立线性关系读数。 |

描述一个流形不会自动增加它的物理自由度；例如复射线空间可由坐标片及过渡映射内在定义。 在本节，是否增加表示维数须由明确的任务与最小性定理决定。

### 16.1　局部 Bloch 表示的完整性与联合未来的缺口

**输入：** 局部 $H=\mathbb C^2$，状态 $\rho\ge0,\operatorname{Tr}\rho=1$，效果 $0\le E\le I$， 读出为 $\operatorname{Tr}(\rho E)$。讨论联合未来时，另给同一总系统中的记录端口与具体联合操作。 **输出：** 局部统计的无损 Bloch 坐标；改变任务后旧边缘读口不足的精确反例。

#### 定义 16.1：局部方向及效果坐标

取 Pauli 矩阵 $\sigma_1,\sigma_2,\sigma_3$，满足 $\operatorname{Tr}\sigma_i=0$、$\operatorname{Tr}(\sigma_i\sigma_j)=2\delta_{ij}$，并写

$$\rho(r)=\frac12(I+r\cdot\sigma),\qquad E=\alpha I+v\cdot\sigma, \quad r,v\in\mathbb R^3, \quad\alpha\in\mathbb R.$$

#### 定理 16.2：全部局部 POVM 的完整坐标

$\rho(r)$ 为状态当且仅当 $|r|\le1$；$E$ 为效果当且仅当 $0\le\alpha\pm|v|\le1$。全部局部 POVM 的统计由 $r$ 唯一决定， 而这些统计反过来唯一决定 $r$。

**证明。**

由 Pauli 乘法有 $(r\cdot\sigma)^2=|r|^2I$，故 $\rho(r)$ 的特征值为 $(1\pm|r|)/2$，效果的特征值同理为 $\alpha\pm|v|$。 于是正性条件恰为所述不等式。迹配对给

$$\operatorname{Tr}(\rho(r)E)=\alpha+r\cdot v.$$

每个效果概率均由 $r$ 给出，故任意 POVM 的全部概率亦然。 反向取 $E_i=(I+\sigma_i)/2$，得到 $r_i=2\operatorname{Tr}(\rho E_i)-1$，所以三个效果的统计已恢复 $r$。

$\square$

对纯态 $\rho(r),\rho(s)$，同一迹计算给

$$|\langle\psi_r,\psi_s\rangle|^2 =\operatorname{Tr}(\rho(r)\rho(s))=\frac{1+r\cdot s}{2}.$$

因此 Hilbert 正交对应 $s=-r$，Bloch 实轴正交对应转移概率 $1/2$。 三个 Pauli 实轴和三个两两正交的态矢量不是同一种对象。

#### 命题 16.3：同一局部球点具有不同联合未来

在内部总系统 $H_S\otimes H_O=\mathbb C^2\otimes\mathbb C^2$ 中， 存在两份纯态，其两个端口各自的约化态都相同， 但经过同一个联合门后，一个局部效果可以将它们完全区分。

**证明。**

取

$$|\Phi^\pm\rangle=\frac{|00\rangle\pm|11\rangle}{\sqrt2}.$$

两态在任意一个端口的约化均为 $I/2$，即两个局部 Bloch 点都为原点。 令 $U$ 为 $S$ 控制、$O$ 为目标的 CNOT，则

$$U|\Phi^\pm\rangle=|\pm\rangle_S\otimes|0\rangle_O.$$

随后在 $S$ 读取 $E_+=|+\rangle\langle+|$，概率分别为 $1$ 与 $0$。

$\square$

这个反例指出，$\rho_{SO}\mapsto\rho_S$ 对包含该联合未来的任务不充分。 记录端口与联合门都在同一个总系统内；补充的是原先舍去的相关性。 若任务始终只有局部 POVM，定理 16.2 已经完整。

### 16.2　高维复合的状态空间不再是仿射圆球

**输入：** 标准有限复矩阵态空间 $\mathcal D_d=\{\rho\in M_d(\mathbb C):\rho\ge0,\operatorname{Tr}\rho=1\}$，并保留其凸混合结构。 **输出：** 仿射维数与非圆球判据；不把态空间维数解释为物理空间维数。

#### 定理 16.4：一般密度态凸体的维数与非球性

$\mathcal D_d$ 的实仿射维数为 $d^2-1$。 若 $d\ge3$，不存在把 $\mathcal D_d$ 变为同维欧氏闭球的可逆仿射映射。

**证明。**

Hermitian 矩阵的 $d$ 个对角元为实数，另有 $d(d-1)/2$ 个复数自由条目， 故 $\dim_\mathbb R\operatorname{Herm}(M_d)=d^2$。迹一施加一条实仿射约束， 而 $I/d$ 为该超平面内的正定内点，所以态空间仿射维数恰为 $d^2-1$。

对 $d\ge3$，考虑

$$\rho_t=\operatorname{diag}(t,1-t,0,\ldots,0),\qquad0\le t\le1.$$

它们形成非退化线段，且全部为边界点：每个 $\rho_t$ 都有非零核， 沿核方向减去任意小的正秩一算子，再沿一个正特征值方向补回相同迹， 便得到任意接近它的非正矩阵。 但欧氏单位球严格凸：若 $x\ne y$ 且 $|x|=|y|=1$，则

$$|tx+(1-t)y|^2=1-t(1-t)|x-y|^2<1\qquad(0<t<1).$$

可逆仿射映射保持边界及线段，故不可能把上述边界线段送入欧氏球边界。

$\square$

这里否定的是保持凸混合的仿射圆球表示。 不能把它改写成“拓扑上不是闭球”：具有内点的有限维紧凸体可径向同胚于闭球。 纯态空间则为 $\mathbb CP^{d-1}$，其实维是 $2d-2$； 当 $d\ge3$ 时，$\mathcal D_d$ 的边界还含有秩大于一的混态。 因此复合后增加的是复射线与正矩阵结构，不是单纯把 Bloch 球半径或轴数增大。

### 16.3　同一个态需要多大的纯化伙伴

**输入：**$H_A=\mathbb C^d$、密度态 $\rho$；指定实现任务是寻找 $|\Psi\rangle\in H_A\otimes H_E$，满足 $\operatorname{Tr}_E|\Psi\rangle\langle\Psi|=\rho$。 张量、偏迹和纯态实现要求均在这里明确给出。 **输出：** 最小环境维数、环境酉唯一性及重复同一任务的停止条件。

#### 定理 16.5：最小纯化维数

上述任务所需的最小环境复维数恰为 $\operatorname{rank}\rho$。

**证明。**

设 $r=\operatorname{rank}\rho$，谱分解为

$$\rho=\sum_{j=1}^r\lambda_j|j\rangle\langle j|, \qquad\lambda_j>0.$$

在 $H_E=\mathbb C^r$ 中取正交基并定义

$$|\Psi_\rho\rangle =\sum_{j=1}^r\sqrt{\lambda_j}|j\rangle_A|j\rangle_E.$$

直接偏迹得到 $\rho$，给出上界。 反向，若环境维数为 $m$，将任意纯化展开成 $|\Psi\rangle=\sum_{\mu=1}^m|v_\mu\rangle\otimes|\mu\rangle$，则

$$\rho=\sum_{\mu=1}^m|v_\mu\rangle\langle v_\mu|,$$

所以 $\operatorname{rank}\rho\le m$。

$\square$

#### 定理 16.6：最小纯化的环境酉唯一性

同一 $\rho$ 的两份最小纯化 $\Psi,\Xi$ 满足 $\Xi=(I\otimes U)\Psi$，其中 $U$ 是两个环境空间之间的酉映射。

**证明。**

沿同一正特征值基，令

$$|e_j\rangle=\lambda_j^{-1/2} (\langle j|\otimes I)|\Psi\rangle.$$

约化等式给 $\langle e_i,e_j\rangle=\delta_{ij}$， 且 $\Psi=\sum_j\sqrt{\lambda_j}|j\rangle|e_j\rangle$。 对 $\Xi$ 同样得到正交族 $f_j$。 最小性使这两族分别为环境的基；取 $Ue_j=f_j$ 即得所述等式。

$\square$

#### 推论 16.7：重复纯化不迫使无限严格扩张

令 $P=|\Psi_\rho\rangle\langle\Psi_\rho|$。 再对同一个总态 $P$ 要求纯化时，最小新增环境维数为一。

**证明。**

$\operatorname{rank}P=1$，由定理 16.5 得结论； $P\otimes|0\rangle\langle0|$ 已实现它。

$\square$

一维环境没有新增可区分自由度。 若后续加入尚未纳入的实际相关或新的独立记录，任务已经改变， 应对新总态重新计算，而不能从“再次描述”直接断定严格增长。 纯化秩与酉等价是成熟结果，以上给出其完整有限证明； 标准来源见 Watrous 定理 2.10、2.12。[\[29\]](#ref-watrous)

### 16.4　由正关系商直接构造有限 GNS 表示

**输入：** 结合星代数 $\mathcal A=M_d(\mathbb C)$ 与正归一泛函 $\omega_\rho(A)=\operatorname{Tr}(\rho A)$。 **输出：** 从同一二元配对构造的循环 Hilbert 表示、维数与唯一性。 这里已给的结合星结构不能被省略成单独一个“正性”词语。

#### 定义 16.8：正配对的商空间

置

$$\mathcal N_\rho=\{A:\omega_\rho(A^*A)=0\} =\{A:A\sqrt\rho=0\},\qquad H_\rho=\mathcal A/\mathcal N_\rho,$$

$$\langle[A],[B]\rangle=\operatorname{Tr}(\rho A^*B),\qquad \pi(C)[A]=[CA],\qquad\xi=[I].$$

#### 定理 16.9：有限 GNS 的存在、维数与循环唯一性

定义 16.8 良定，并给出

$$\dim_\mathbb CH_\rho=d\,\operatorname{rank}\rho,\qquad \omega_\rho(C)=\langle\xi,\pi(C)\xi\rangle.$$

$\pi$ 为含幺星表示，$\xi$ 是循环单位向量。 任何给出同一 $\omega_\rho$ 的循环表示都与之存在唯一的、保持循环向量且交织表示的酉同构。

**证明。**

映射 $A\mapsto A\sqrt\rho$ 的 Hilbert–Schmidt 内积满足

$$\langle A\sqrt\rho,B\sqrt\rho\rangle_{\mathrm{HS}} =\operatorname{Tr}(\sqrt\rho A^*B\sqrt\rho)=\operatorname{Tr}(\rho A^*B).$$

其核恰为 $\mathcal N_\rho$，所以在商空间上内积良定且正定。 若 $N\in\mathcal N_\rho$，则 $CN\sqrt\rho=0$， 因此 $\pi(C)$ 良定。 矩阵结合律给 $\pi(CD)=\pi(C)\pi(D)$；内积公式给 $`\pi(C^*)=\pi(C)^*`$，且 $\pi(I)=I$。

在 $\rho$ 的特征基中，$A\sqrt\rho$ 的前 $r=\operatorname{rank}\rho$ 列可任取， 其余列为零，故像的复维数为 $dr$。 又 $[A]=\pi(A)\xi$，所以 $\xi$ 循环，且 $\|\xi\|^2=\operatorname{Tr}\rho=1$。 代入 $[I]$ 直接得到所述状态表示式。

若 $(\pi',K,\xi')$ 为另一循环表示，定义 $U[A]=\pi'(A)\xi'$。 由

$$\langle\pi'(A)\xi',\pi'(B)\xi'\rangle =\omega_\rho(A^*B)=\langle[A],[B]\rangle$$

知 $U$ 良定且等距；循环性使其像稠密，有限维性使其满射，故 $U$ 酉。 $U\xi=\xi'$ 与 $U\pi(C)=\pi'(C)U$ 直接成立。 循环生成性又使任何这样的映射都必须在每个 $[A]$ 上取这个值，因此唯一。

$\square$

将 $A\sqrt\rho$ 的 $r$ 个非零列排列为向量，可识别

$$H_\rho\cong\mathbb C^d\otimes\mathbb C^r, \qquad\pi(C)=C\otimes I_r, \qquad\xi\longleftrightarrow|\Psi_\rho\rangle.$$

若 $\rho$ 本来为纯态，则 $r=1$，GNS 空间复维仍为 $d$。 该表示由同一正关系构造，不需要先指定另一个物理世界。 但它没有识别实际未知环境，也没有证明任何特定纯化已经可准备。

近期的 Sorce 工作将规范纯化扩展到一般星代数状态，并研究其与 GNS 表示的关系。 其预印本版本为 2025 年，期刊发表于 2026 年；一般非有界情形还区分弱纯性与强纯性。 在忠实 von Neumann 分支，相关 GNS 空间可以规范同构，而非必然严格增大。 这些结论与本节的“按任务计算最小表示”相容，不是无条件的几何升维律。[\[30\]](#ref-sorce23)

### 16.5　同一个完整过程需要多大的环境

**输入：** 已给 CPTP 映射 $\Phi:M_d(\mathbb C)\to M_e(\mathbb C)$。 若任务含结果、失败或细记录，应先把这些全部保留为完整仪器的输出。 **输出：** 等距实现的最小环境维数及其酉唯一性；不自动产生实际相干控制。

#### 定义 16.10：过程正表

令 $|\Gamma\rangle=\sum_{i=1}^d|i\rangle|i\rangle$，并定义

$$J_\Phi=(\Phi\otimes\operatorname{id}_d)(|\Gamma\rangle\langle\Gamma|) \in M_e(\mathbb C)\otimes M_d(\mathbb C).$$

#### 定理 16.11：最小 Stinespring 环境维数

满足

$$\Phi(X)=\operatorname{Tr}_E(VXV^*),\qquad V:\mathbb C^d\longrightarrow\mathbb C^e\otimes H_E,\qquad V^*V=I,$$

的环境最小复维数为 $\operatorname{rank}J_\Phi$。 两份最小实现只差环境酉映射。

**证明。**

记 $r=\operatorname{rank}J_\Phi$。完全正性给 $J_\Phi\ge0$，取谱分解

$$J_\Phi=\sum_{\mu=1}^r|v_\mu\rangle\langle v_\mu|.$$

按输出、输入指标将 $v_\mu$ 重排成矩阵 $K_\mu:\mathbb C^d\to\mathbb C^e$。 比较 Choi 表中的每个输入矩阵单位，得到

$$\Phi(X)=\sum_{\mu=1}^rK_\mu XK_\mu^*.$$

保迹等价于 $`\sum_\mu K_\mu^*K_\mu=I`$。因此

$$Vx=\sum_{\mu=1}^rK_\mu x\otimes|\mu\rangle$$

满足 $`V^*V=I`$，偏迹亦给原 $\Phi$，得到上界。 反向，任何 $m$ 维环境实现按环境基展开，给 $K_\mu=(I\otimes\langle\mu|)V$ 及 $m$ 项 Kraus 和； 故 $J_\Phi$ 是 $m$ 个正秩一矩阵之和，$\operatorname{rank}J_\Phi\le m$。

为证明唯一性，将两份最小 Kraus 向量排列成满列秩矩阵 $F,G$， 使 $`FF^*=GG^*=J_\Phi`$。 置 $R_F=J_\Phi^{+1/2}F$、$R_G=J_\Phi^{+1/2}G$，其中上标 $+$ 表示谱伪逆。 二者的列均为 $\operatorname{ran}J_\Phi$ 的正交基， 故 $R_G=R_FU$ 对某个 $r\times r$ 酉 $U$，从而 $G=FU$。 重排回 Kraus 指标，环境基作 $U^T$ 变换便将一份 $V$ 变为另一份。

$\square$

这一秩最小性属于标准 Choi–Kraus–Stinespring 接口。 可与 Watrous 定理 2.22、推论 2.27 对照。[\[29\]](#ref-watrous) 对于同一 $d\to e$ 过程，$\operatorname{rank}J_\Phi\le de$。 重新表示同一过程不会改变该秩；新增实际记录或新的允许联合未来，改变的是目标过程。

### 16.6　固定未来菜单的最小闭合与停止

**输入：** 固定有限总空间 $H$，$\dim H=d$；已声明的有限 CP 迹不增分支族 $\{\Phi_a\}_{a\in A}$；含 $I$ 的初始 Hermitian 实线性读口空间 $V_0$。 本节任务包括这些分支的全部有限字与相应有限自适应协议。 若有类型、失败、记录或可返回环境，它们须已经进入同一固定接口与合法性语义。 **输出：** 该任务的最小线性充分空间、有限停止界及最少新增读口数。

项目 V42 的定义 11.1、命题 11.2 已给下面的未来空间闭合， 其定理 2.2 已给最小新增读口公式。这里完整展开这些既有结论， 作为本稿几何判断的接口，不将其记为新的量子公理或新发现。[\[31\]](#ref-v42q23)

#### 定义 16.12：未来效果空间

以迹配对定义每个 $\Phi_a$ 的对偶 $`\Phi_a^*`$，置

$$V_{n+1}=V_n+ \operatorname{span}_{\mathbb R}\{\Phi_a^*(F):F\in V_n,\ a\in A\}.$$

记 $V_\infty=\bigcup_{n\ge0}V_n$。

#### 定理 16.13：全部有限未来的闭合、最小性与有限停止

$V_n$ 等于长度不超过 $n$ 的全部回溯读口的实张成。 严格增长至多发生 $d^2-\dim V_0$ 次； 一旦 $V_n=V_{n+1}$，以后全部相等。 $V_\infty$ 是包含 $V_0$ 且由各 $`\Phi_a^*`$ 保持的最小实子空间， 它保留全部允许有限字的分支统计及由这些分支组成的有限自适应协议概率。 对 $V_\infty$ 再作相同闭合不增加任何读口。

**证明。**

$n=0$ 时结论由定义成立。每一步在已有字外侧前接一个 $`\Phi_a^*`$， 按字长归纳即得 $V_n$ 的所述等式。 若 $V_n=V_{n+1}$，各 $`\Phi_a^*`$ 都保持 $V_n$； 任意有限复合仍保持它，所以以后全部相等。 每次严格包含至少增加一维，而 $\dim_\mathbb R\operatorname{Herm}(H)=d^2$，得停止界。 任何包含 $V_0$ 且由各对偶保持的子空间都逐步包含 $V_n$，故包含 $V_\infty$，证明最小性。

对有限分支字 $w$ 及终端效果 $E\in V_0$，

$$p(w,E\mid\rho)=\operatorname{Tr}(E\Phi_w(\rho)) =\operatorname{Tr}(\Phi_w^*(E)\rho).$$

所以统计由 $V_\infty$ 决定。 有限自适应协议的每个叶子仍为一条指定的动作与结果字， 协议事件概率是有限叶子的概率和，因而也由该空间决定。 最后，$V_\infty$ 已被全部对偶保持，重复闭合不会增加它。

$\square$

#### 定理 16.14：最少新增线性读口，允许任意解码

在全部密度态上，允许另选 Hermitian 线性读口并使用任意解码函数， 为了恢复定理 16.13 的全部目标， 最少新增独立实读口数恰为

$$\boxed{k_{\min}=\dim V_\infty-\dim V_0.}$$

**证明。**

补取 $V_\infty/V_0$ 的一组代表基即可恢复每个目标，给出上界。 反向，设新增读口与 $V_0$ 的合成空间为 $W$，但存在 $F\in V_\infty\setminus W$。 按迹内积写 $F=F_W+\Delta$，其中 $\Delta\ne0$、$\Delta\perp W$。 因为 $I\in W$，有 $\operatorname{Tr}\Delta=0$。 取 $0<\varepsilon<(d\|\Delta\|_{\mathrm{op}})^{-1}$，则

$$\rho_\pm=I/d\pm\varepsilon\Delta$$

均为正定迹一态。 它们在 $W$ 的全部读数相同，但

$$\operatorname{Tr}(F\rho_+)-\operatorname{Tr}(F\rho_-) =2\varepsilon\operatorname{Tr}(\Delta^2)>0.$$

所以任何解码函数都无法由这些相同输入恢复该目标。 故必须有 $V_\infty\subseteq W$，从而得到维数下界。

$\square$

例如 qubit 的 $V_0=\operatorname{span}_\mathbb R\{I,Z\}$，仅允许绕 $y$ 轴的 $\pi/2$ 门时， 回溯生成 $X$ 后停在 $\operatorname{span}_\mathbb R\{I,X,Z\}$。 若再允许绕 $z$ 轴的 $\pi/2$ 门，便生成 $Y$，闭合为全部 $\operatorname{Herm}(\mathbb C^2)$。 这说明任务闭合可以先停在一个较小空间；修改菜单才改变需要保留的信息。

### 16.7　本区域的闭合范围

| 已给对象 | 闭合推出的量 | 仍须由原任务声明的内容 |
|:---|:---|:---|
| 单 qubit 状态与全部局部效果 | Bloch 点的完整统计表示 | 是否允许联合返回或额外参考。 |
| 指定密度态及纯化任务 | 最小环境 $\operatorname{rank}\rho$、酉等价 | 实际共同来源与纯化准备。 |
| 同一正泛函与结合星代数 | 循环 GNS 表示及唯一性 | 原非结合关系是否已下降到该代数。 |
| 指定完整 CPTP 过程 | 最小环境 $\operatorname{rank}J_\Phi$ | 全部记录、失败和实现的实际供应。 |
| 固定有限未来菜单 | $V_\infty$、幂等及精确新增读口数 | 是否另有尚未纳入的合法未来或增长记忆。 |

一个球是否够用，由允许的问题决定。 只问同一个量子比特的局部测量，球内一点已经给全答案； 若后来允许它与内部记录再相遇，就可能需要补回先前舍去的相关性。 同一个态需要多少纯化伙伴由态秩决定，一段过程需要多少环境由过程秩决定。 把固定菜单的全部有限未来补齐后，再补一次没有新内容。 因此这组结果确定的是指定任务中的最小完整表示及其停止条件， 并没有把未知的全部物理来源、无限历史或所有可执行过程宣布闭合。

<a id="section-17"></a>

## 17　共同锚：有限关系怎样锁成同一个整体

**本区域输入：** 已给定实数域或复数域上的同一张 Hermitian 关系表； 同一组 $r$ 个锚标签的关系块正定；每个新标签相对该锚无新增秩； 每一对新标签与同一个锚合成的关系块半正定。 这里的正性是矩阵二次型正性，来自已标定的内积接口， 不把未经标定的原读出 $p^2$ 当作二次型。 **闭合输出：** 所有交叉关系被唯一锁定；整表半正定、秩恰为 $r$， 并有同一个 $r$ 维实现。最多需要 $r+2$ 个标签的检验， 这个标签数一般不能降为 $r+1$。

项目 OTF-007 定理 10.1 已重述 V44 的单点广义 Schur 补判据。 下面先给出该判据的复数版本，再把它用于多个新点共享同一个锚。 后一个结论是标准 Schur 补的直接推论，本稿不主张历史首创。[\[8\]](#ref-otf724)（第10.1节）

### 17.1　一个新点究竟新增了什么

#### 定义 17.1：关系表、实现与最小维数

令 $\mathbb F\in\{\mathbb R,\mathbb C\}$，有限标签集为 $L$。 一张关系表是 $G=(g_{ij})_{i,j\in L}$，满足 $g_{ji}=\overline{g_{ij}}$。 其内积实现是向量族 $(v_i)_{i\in L}$，使 $`g_{ij}=v_i^*v_j`$。 若 $G\ge0$，谱分解给出一个实现，且所有实现的张成空间维数均为 $\operatorname{rank}G$。 标签可以多于张成维数；重复标签关系不等于新增独立方向。

#### 引理 17.2：单点 Schur 余量

给定 $G\ge0$、列向量 $b$ 与实数 $c$，记 $G^+$ 为 Moore–Penrose 逆。 则

$$
\widetilde G=\begin{pmatrix}G&b\\b^*&c\end{pmatrix}\ge0
 \quad\Longleftrightarrow\quad
 b\in\operatorname{ran}G,
 \qquad \delta:=c-b^*G^+b\ge0.
$$

成立时，$\operatorname{rank}\widetilde G=\operatorname{rank}G+\mathbf 1_{\{\delta>0\}}$。

**证明。**

若 $z\in\ker G$，把 $(z,t)$ 代入 $\widetilde G$ 的二次型， 并让实数或复数 $t$ 沿使交叉项为负的方向趋于零，得 $`z^*b=0`$。 所以 $b\perp\ker G$，即 $b\in\operatorname{ran}G$。 置 $a=G^+b$，则 $Ga=b$，且

$$
\begin{pmatrix}I&0\\-a^*&1\end{pmatrix}
 \widetilde G
 \begin{pmatrix}I&-a\\0&1\end{pmatrix}
 =\begin{pmatrix}G&0\\0&\delta\end{pmatrix}.
$$

左右因子互为伴随且可逆，故保持正性与秩，给出全部结论。

$\square$

若 $b_i=\langle v_i,w\rangle$、$c=\|w\|^2$，则

$$\delta=\bigl\|w-\Pi_{\operatorname{span}\{v_i\}}w\bigr\|^2.$$

因此 $\delta>0$ 是关系数据迫使最小表示维数增加的证据； $\delta=0$ 则表示新标签仍在旧张成空间内。 这个判据本身不认定某一物理空间新增了一条坐标轴。

### 17.2　共同锚锁定全部交叉关系

#### 定义 17.3：共同锚与关系余量

选择同一标签集中的 $r\ge1$ 个锚，令其关系块 $A>0$。 其余标签的锚交叉列记为 $b_j$，彼此关系记为 $c_{jk}$。 写成

$$
G=\begin{pmatrix}A&B\\B^*&C\end{pmatrix},\qquad
 B=(b_j)_j,\quad C=(c_{jk})_{j,k},\qquad
 \Delta=C-B^*A^{-1}B.
$$

所有局部检验使用同一份 $A$、$b_j$ 与 $c_{jk}$； 不允许在不同局部块中给同名标签另换一份关系。

#### 定理 17.4：共同锚的有限拼接

在定义 17.3 下，假定：

1.  每个单点锚块 $`G_{I\cup\{j\}}=\begin{psmallmatrix}A&b_j\\b_j^*&c_{jj}\end{psmallmatrix}`$ 半正定且秩恰为 $r$；

2.  对每对不同的新标签 $j,k$，共同锚块 $G_{I\cup\{j,k\}}\ge0$。

则全部新关系被强制为

$$c_{jk}=b_j^*A^{-1}b_k, \qquad G=Y^*A^{-1}Y,\qquad Y=(A\ B). \tag{17.1}$$

故 $G\ge0$、$\operatorname{rank}G=r$。反过来，若 $G\ge0$ 且 $\operatorname{rank}G=r$， 上面两个条件必成立。

**证明。**

由引理 17.2，第一个条件等价于 $`\Delta_{jj}=c_{jj}-b_j^*A^{-1}b_j=0`$。 第二个条件对 $A$ 取 Schur 补，得到

$$
\begin{pmatrix}0&\Delta_{jk}\\\overline{\Delta_{jk}}&0\end{pmatrix}\ge0.
$$

该二阶 Hermitian 矩阵的特征值为 $\pm|\Delta_{jk}|$， 所以 $\Delta_{jk}=0$。这对每一对成立，故 $\Delta=0$， 直接展开便得式 (17.1)。 $A^{-1}>0$ 给出整表正性，而 $Y$ 含有可逆块 $A$，故秩为 $r$。

反向，半正定矩阵的主块均半正定。 每个单点锚块包含秩为 $r$ 的 $A$，且秩不超过整表的 $r$， 故恰为 $r$。

$\square$

#### 推论 17.5：坐标由关系产生，最小实现仅差规范

以 $A^{-1/2}Y$ 的列为向量，得到共同的 $\mathbb F^r$ 实现。 任意两个最小实现之间存在唯一把每个标签向量对应起来的酉映射 （实数情形为正交映射）。该结论同样适用于任意多个标签， 只要它们共享一个有限锚且每一对都满足定理的条件。

**证明。**

列向量的 Gram 表正是 $`Y^*A^{-1}Y`$。 若 $(v_i)$ 与 $(w_i)$ 是两个最小实现，定义 $U(\sum_i\lambda_i v_i)=\sum_i\lambda_i w_i$。 两边平方范数都等于 $\sum_{i,j}\overline{\lambda_i}g_{ij}\lambda_j$， 故零线性组合对应零线性组合，$U$ 良定且保持内积。 标签向量张成两侧，故 $U$ 为唯一酉同构。 标签无限时，每个新列仍由同一公式 $A^{-1/2}b_j$ 给出， 每个有限关系块均由该向量族实现，不需要再加坐标轴。

$\square$

### 17.3　为什么三元检验还需要明确的拼接条件

#### 反例 17.6：$r+1$ 个标签的全部检查仍不够

取 $n=r+2$，令

$$G_{ii}=1,\qquad G_{ij}=-\frac1r\ (i\ne j),\qquad G=\left(1+\frac1r\right)I_n-\frac1r\mathbf 1\mathbf 1^*.$$

任意 $m$ 阶主块的特征值为

$$1+\frac1r\quad(m-1\text{ 次}),\qquad 1-\frac{m-1}{r}\quad(1\text{ 次}).$$

因此全部不超过 $r+1$ 阶的主块半正定， 每个 $r+1$ 阶主块恰有秩 $r$，每个 $r$ 阶锚块正定； 但整表在全一向量上有特征值 $-1/r$，不半正定。 特别地，全部三阶正性不能推出整体正性：取 $r=2$ 即得四阶反例。

这个反例通过了共同锚定理的全部单点条件， 失败恰在两份新标签与同一锚的交叉相容性上。 因此“每一个局部三元都能实现”与“这些局部实现使用同一个整体”是不同条件。 它们的区别由 $\Delta_{jk}$ 精确测量，不能靠重命名维数消去。

| 锚的秩  | 表示空间        | 足够的最大检查标签数 | 仍不足的标签数 |
|:--------|:----------------|:---------------------|:---------------|
| $r=1$ | $\mathbb F^1$ | $3$                | $2$          |
| $r=2$ | $\mathbb F^2$ | $4$                | $3$          |
| $r=3$ | $\mathbb F^3$ | $5$                | $4$          |

这里的“足够”始终包含同一个正定锚及单点零余量条件。 检查五个标签可以只是在三维中检查五个向量； 它没有把三维表示升为五维表示。 同样，复二维振幅的四标签检查没有增加复振幅空间的维数。

#### 命题 17.7：全局秩承诺是更强的输入

若另外已知整张 Hermitian 表 $G$ 的秩不超过 $r$， 且所有大小不超过 $r$ 的主块半正定，则 $G\ge0$。 这个结论不适用于只有各单点锚块秩为 $r$ 的情形。

**证明。**

令 $m=\operatorname{rank}G$。$m=0$ 时 $G=0$。 否则特征多项式中对应 $m$ 阶主子式之和的系数， 等于 $m$ 个非零特征值的乘积，因而非零。 所以存在可逆 $m$ 阶主块 $A$；由 $m\le r$ 与假设，$A>0$。 重排后写 $`G=\begin{psmallmatrix}A&B\\B^*&C\end{psmallmatrix}`$。 可逆合同变换给出 $`\operatorname{rank}G=m+\operatorname{rank}(C-B^*A^{-1}B)`$，故余量为零。 于是 $`G=(A\ B)^*A^{-1}(A\ B)\ge0`$。

$\square$

### 17.4　三维窗口与整个理论分别计账

**已闭合：** 给定完整共同锚条件，任意多标签仍能在同一个秩 $r$ 的 内积模型中实现；无需每增加一个标签就增加一维。 **仍为输入：** 关系表的标量域、准确数值、共同标签身份、 正定锚与指定的零余量条件；含噪数据还须给误差与秩间隙。 这些条件不从“正读出”三个字自动推出。

本轮主重构得到的 $\operatorname{Im}\mathbb H\simeq\mathbb R^3$， 以及项目中由一对正交原元素生成的三轴窗口，都是有明确类型的局部结构。 上述定理允许同一窗口容纳任意多个彼此一致的关系标签， 但没有断言原整体 $\Omega$ 的全部对象、全部记录、全部联合操作只占三维。 单 qubit 的三实 Bloch 坐标、复二维振幅、 多个 qubit 的张量积空间与一般 Gram 秩分别属于不同接口。 例如 $n$ 个 qubit 的复振幅维数为 $2^n$，密度态实仿射维数为 $4^n-1$； 它们不由“每个局部窗口有三个轴”缩成一个共同三维球。

**本轮几何的白话。**

先选几根已经互相标定好的尺子。 每个新对象若都完全落在这些尺子张成的空间里， 它与尺子的关系就已经定死了它的位置。 再把任意两个新对象放回同一组尺子检查， 它们彼此的关系便不能另写一份；所有局部图因此拼成同一个整体。 要增加维数，必须真的读到无法落回旧空间的正余量。

<a id="section-18"></a>

## 18　把控制器和过程也放回关系中：相干拼接的全部自由度

**本区域的输入。**

本节继承有限维复量子态、Born 配对和张量复合的数学接口。 取有限维复 Hilbert 空间 $H=\mathbb C^d$、 控制空间 $C=\mathbb C^n$ 及其正交标签 $|1\rangle,\ldots,|n\rangle$。 给定 $n$ 个完全正保迹映射 $\Phi_j:\mathcal L(H)\to\mathcal L(H)$。 完整过程要求为完全正保迹映射 $\Lambda:\mathcal L(C\otimes H)\to\mathcal L(C\otimes H)$， 并满足标签保持条件

$$\Lambda(|j\rangle\langle j|\otimes X) =|j\rangle\langle j|\otimes\Phi_j(X) \qquad(j=1,\ldots,n;\ X\in\mathcal L(H)). \tag{Q21-C1}$$

这些是本区域的接口前件；它们并不由一个 qubit 的球面图像单独推出。 控制、记录和相位参考均可作为有限附属系统纳入同一整体， 但该整体不被要求仍具有单个 qubit 的四维实振幅空间。

**与项目已有结论的关系。**

项目 `RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md` 第 335 节已指出：普通通道的相等不保证相干控制后的相等。 相关 tester 和后继闭包陈述，应采用第 396 节及第 400 节修订后的条件： 过程差须满足合法归一化约束，实际 tester 还须与该可实现差有非零配对。 下面把这一存在性边界补成全部相容过程的参数分类。 有限维通道拼接的基本非唯一性及其分类属于已知结果， 不是本轮新基础公理；参见 Åberg 及 Vanrietvelde–Chiribella。 本轮的作用是给出可直接核算的接口、证明和删项反例。[\[32\]](#ref-waveprocess), [\[33\]](#ref-aberg), [\[34\]](#ref-vanrietvelde)

### 18.1　二元过程的完整正性条件

**定义。**

采用输出在前、输入在后的 Choi 约定：

$$J(\Psi)=\sum_{a,b=1}^{d}\Psi(|a\rangle\langle b|) \otimes|a\rangle\langle b|, \qquad |A\rangle\!\rangle=\sum_a A|a\rangle\otimes|a\rangle .$$

这里 $\Psi$ 可以是一般复线性映射，并不要求它单独完全正。 线性映射与 Choi 矩阵一一对应，因为矩阵的输入侧第 $(a,b)$ 块 正好是 $\Psi(|a\rangle\langle b|)$。

前面的递归参考定理已证明 Choi–Kraus 等价。 以下复用该定理；一般线性映射的交叉 Choi 块不要求单独为正。

#### 定理 18.1：全部标签保持拼接

满足 (Q21-C1) 的所有完全正保迹映射，恰好由一个正块矩阵

$$\mathcal J=(J_{jk})_{j,k=1}^n\ge0,\qquad J_{jj}=J(\Phi_j) \tag{Q21-C2}$$

参数化。若 $\Gamma_{jk}$ 是 $J_{jk}$ 唯一确定的线性映射，则

$$\Lambda\left(\sum_{j,k}|j\rangle\langle k|\otimes X_{jk}\right) =\sum_{j,k}|j\rangle\langle k|\otimes\Gamma_{jk}(X_{jk}). \tag{Q21-C3}$$

等价地，存在共同索引的 Kraus 族 $A_{j\mu}$，使

$$\Phi_j(X)=\sum_\mu A_{j\mu}X A_{j\mu}^\dagger,\qquad \Gamma_{jk}(X)=\sum_\mu A_{j\mu}X A_{k\mu}^\dagger. \tag{Q21-C4}$$

其中 $J_{kj}=J_{jk}^\dagger$ 等价于 $\Gamma_{kj}(X)=[\Gamma_{jk}(X^\dagger)]^\dagger$。

**证明。**

先设 $\Lambda$ 完全正，写 Kraus 族 $K_\mu$。 记 $P_j=|j\rangle\langle j|\otimes I$。 对任意 $\psi\in H$ 和 $\ell\ne j$， 标签保持给出

$$0=\operatorname{Tr}\!\left[ P_\ell\Lambda(|j,\psi\rangle\langle j,\psi|)\right] =\sum_\mu\|P_\ell K_\mu|j,\psi\rangle\|^2 .$$

各项非负，故每个 $K_\mu$ 都保持每个标签子空间。 于是 $K_\mu=\sum_j|j\rangle\langle j|\otimes A_{j\mu}$。 展开 $K_\mu X K_\mu^\dagger$ 得 (Q21-C3)–(Q21-C4)。 各分支保迹给 $\sum_\mu A_{j\mu}^\dagger A_{j\mu}=I$， 因而 $\sum_\mu K_\mu^\dagger K_\mu=I$。

由向量化恒等式， $J_{jk}=\sum_\mu|A_{j\mu}\rangle\!\rangle \langle\!\langle A_{k\mu}|$， 所以 $\mathcal J\ge0$。 反之，将任意满足 (Q21-C2) 的正块矩阵分解为 $\mathcal J=\sum_\mu v_\mu v_\mu^\dagger$， 把每个块分量 $v_{j\mu}$ 写成 $|A_{j\mu}\rangle\!\rangle$。 对角块条件给各 $\Phi_j$ 的 Kraus 表示与保迹条件。 以上述块对角 $K_\mu$ 构造 $\Lambda$，立即完全正、保迹且保持标签。 Choi 对应的一一性给参数化的一一性。

$\square$

#### 引理 18.2：两个正块之间只剩一个收缩

设 $A,B\ge0$ 是有限维正矩阵。则

$$
\begin{pmatrix}A&Z\\Z^\dagger&B\end{pmatrix}\ge0
 \quad\Longleftrightarrow\quad
 Z=A^{1/2}K B^{1/2},\qquad \|K\|\le1 ,
\tag{Q21-C5}
$$

其中 $K:\operatorname{supp}B\to\operatorname{supp}A$。 在这两个支撑空间间 $K$ 唯一，零延拓仍是收缩。 在支撑之外作其他扩展虽不改变 $Z$，若要求扩展后仍为收缩， 仍须另满足其算子范数不超过一。

**证明。**

记左侧正矩阵为 $M$。 若 $x\in\ker A$，则 $(x,0)^\dagger M(x,0)=0$。 对正矩阵，$v^\dagger Mv=\|M^{1/2}v\|^2=0$ 蕴含 $Mv=0$， 故 $Z^\dagger x=0$。同理 $Zy=0$ 对所有 $y\in\ker B$ 成立。 因此 $Z$ 只连接所列支撑空间。 在支撑上 $A,B$ 可逆，作可逆合同变换得到

$$
\begin{pmatrix}A^{-1/2}&0\\0&B^{-1/2}\end{pmatrix}
 M
 \begin{pmatrix}A^{-1/2}&0\\0&B^{-1/2}\end{pmatrix}
 =\begin{pmatrix}I&K\\K^\dagger&I\end{pmatrix},
 \qquad K=A^{-1/2}ZB^{-1/2}.
$$

最后一个矩阵的二次型为

$$\|x+Ky\|^2+\|y\|^2-\|Ky\|^2 .$$

它对所有 $x,y$ 非负，当且仅当 $\|Ky\|\le\|y\|$。 反向将该正矩阵与 $\operatorname{diag}(A^{1/2},B^{1/2})$ 作合同变换即得结论。唯一性来自支撑上的可逆性。

$\square$

#### 推论 18.3：二元过程的精确缺项

对两个已给分支通道 $\Phi_0,\Phi_1$，全部允许交叉映射 $\Gamma$ 恰好满足

$$\boxed{\; J(\Gamma)=J(\Phi_0)^{1/2}KJ(\Phi_1)^{1/2},\qquad \|K\|\le1 . \;} \tag{Q21-C6}$$

两个普通通道固定了两个对角块，未固定这个收缩 $K$。 将 $K$ 包入内部实现后，完整过程才有确定的相干输出。

**证明。**

在全部拼接定理中取 $n=2$，应用上一引理。

$\square$

### 18.2　记录内生：酉分支的相关矩阵

#### 定理 18.4：酉分支的全部相干拼接

若各分支为酉通道 $\Phi_j(X)=U_jXU_j^\dagger$，则全部允许拼接恰好具有形式

$$\Gamma_{jk}(X)=\gamma_{jk}U_j XU_k^\dagger,\qquad G=(\gamma_{jk})\ge0,\qquad \gamma_{jj}=1 . \tag{Q21-C7}$$

每个这样的 $G$ 都有一个完全内生的有限环境实现

$$V(|j\rangle\otimes\psi) =|j\rangle\otimes U_j\psi\otimes e_j,\qquad \langle e_j,e_j\rangle=1,\qquad \gamma_{jk}=\langle e_k,e_j\rangle. \tag{Q21-C8}$$

这里内积采用物理 convention，即对第一变量共轭线性。 所需最小纯环境维数为 $\operatorname{rank}G$。

**证明。**

$J(\Phi_j)=|U_j\rangle\!\rangle\langle\!\langle U_j|$ 为秩一矩阵。 正块矩阵的零空间传播性质说明：$J_{jk}$ 的像包含于 $\operatorname{span}|U_j\rangle\!\rangle$， 其伴随的像包含于 $\operatorname{span}|U_k\rangle\!\rangle$。 故 $J_{jk}=\gamma_{jk}|U_j\rangle\!\rangle \langle\!\langle U_k|$。 各 $|U_j\rangle\!\rangle$ 的范数为 $\sqrt d$； 它们放在不同标签块后互相正交。 因此 $\mathcal J\ge0$ 等价于 $G\ge0$，而对角条件等价于 $\gamma_{jj}=1$。 反向由拼接定理成立。

将 $G$ 分解成 $G=BB^\dagger$，其中 $B$ 只有 $r=\operatorname{rank}G$ 列。 取 $e_j=\sum_{\alpha=1}^rB_{j\alpha}|\alpha\rangle$， 即有 $\langle e_k,e_j\rangle=\gamma_{jk}$ 和 $\|e_j\|=1$。 不同控制标签彼此正交，所以 (Q21-C8) 的 $V$ 保持全部内积； 对环境取偏迹得到 (Q21-C7)。 反之，完整通道的 Choi 矩阵是 $\mathcal J$ 在 输出标签等于输入标签子空间中的等距嵌入， 而前述秩一块分解给 $\operatorname{rank}J(\Lambda)=\operatorname{rank}\mathcal J =\operatorname{rank}G$。 任意维数为 $m$ 的纯环境等距实现， 沿环境正交基展开即产生至多 $m$ 个 Kraus 算子， 故其 Choi 秩不超过 $m$。 所以任意纯环境实现都需 $m\ge r$， 所构造的 $r$ 维环境达到下界。

$\square$

#### 推论 18.5：两分支的圆盘、相位规范与实际读出

当 $n=2$，全部自由度是一个复数 $\gamma=\gamma_{01}$，满足 $|\gamma|\le1$。 取控制初态 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$， 目标初态 $\rho$，以及 $|+_\phi\rangle=(|0\rangle+e^{i\phi}|1\rangle)/\sqrt2$， 则

$$p_+(\phi)=\frac12\left[ 1+\operatorname{Re} \left(e^{i\phi}\gamma\operatorname{Tr} (U_0\rho U_1^\dagger)\right)\right]. \tag{Q21-C9}$$

酉矩阵代表改为 $U_j'=e^{i\alpha_j}U_j$ 时， 同一个完整过程要求 $\gamma'=e^{-i(\alpha_0-\alpha_1)}\gamma$。 因此普通分支的整体相位不会自动成为可观测量； 可观测量是完整交叉映射 $\Gamma$。

**证明。**

$G=\left(\begin{smallmatrix}1&\gamma\\ \bar\gamma&1\end{smallmatrix}\right)\ge0$ 当且仅当 $1-|\gamma|^2\ge0$。 目标取偏迹后，控制态为 $\frac12\left(\begin{smallmatrix}1&z\\\bar z&1\end{smallmatrix}\right)$， $z=\gamma\operatorname{Tr}(U_0\rho U_1^\dagger)$。 与 $|+_\phi\rangle\langle+_\phi|$ 配对即得公式。 最后直接要求 $\gamma'U_0'XU_1'^\dagger=\gamma U_0 XU_1^\dagger$ 即得规范变换。

$\square$

**相位参考也留在公式内。**

式 (Q21-C9) 中的 $\phi$ 是控制效果的标定参数， 不能在声称完全内生时把它当成无代价的外部旋钮。 若参考 $R$ 取有限正交标签 $|\ell\rangle$，以 $\xi_R=\sum_\ell q_\ell|\ell\rangle\langle\ell|$ 编码实际可用相位 $\phi_\ell$，定义整体效果

$$F_+=\sum_\ell|\ell\rangle\langle\ell|_R \otimes|+_{\phi_\ell}\rangle\langle+_{\phi_\ell}|_C .$$

在这一独立参考制备模型内，实际概率正好是

$$\operatorname{Tr}[F_+(\xi_R\otimes\rho_C)] =\frac12\left[1+\operatorname{Re}(\eta z)\right], \qquad \eta=\sum_\ell q_\ell e^{i\phi_\ell}. \tag{Q21-C10}$$

这是有限维 Born 配对的直接展开，不另外假定一个外部观察者。 若 $R$ 已与控制、目标或源相关，必须使用实际联合态 $\rho_{RCT}$，不能继续把它替换成 $\xi_R\otimes\rho_{CT}$。 本模型没有宣称从任意初态免费产生相位参考，也没有预设能量守恒的 $U(1)$ 协变操作限制；若另加该限制，需要另列资源前件。

### 18.3　三元不是三个独立的二元

以下四分支反例在项目 UPPM-RG-001 例 5.3 已出现，在此重证并接入过程记录。[\[35\]](#ref-uppm)

#### 定理 18.6：三分支兼容与四分支反例

三个酉分支的交叉系数可以放进同一个完整过程，当且仅当

$$|\gamma_{12}|,\ |\gamma_{23}|,\ |\gamma_{31}|\le1,$$

$$\boxed{\quad 1+2\operatorname{Re}(\gamma_{12}\gamma_{23}\gamma_{31}) -|\gamma_{12}|^2-|\gamma_{23}|^2-|\gamma_{31}|^2\ge0 . \quad} \tag{Q21-C11}$$

然而，每个三分支子系统兼容，并不保证任意多个分支整体兼容。

**证明。**

三阶 Hermitian 矩阵半正定当且仅当全部主子式非负： 正性显然使每个主子矩阵半正定；反向， $\det(tI+G)$ 的各系数是相应阶主子式之和，最高项为 $t^3$， 故当这些主子式均非负时，$\det(tI+G)>0$ 对全部 $t>0$ 成立。 若 $G$ 有负特征值 $\lambda$，取 $t=-\lambda$ 即矛盾。 一阶子式为 $1$，二阶子式为 $1-|\gamma_{jk}|^2$， 展开三阶行列式即得 (Q21-C11)。 对最后一句，取四阶相关候选

$$G_4=\frac75 I_4-\frac25\mathbf1_4\mathbf1_4^\dagger . \tag{Q21-C12}$$

它的对角元均为 $1$，非对角元均为 $-2/5$。 任一三阶主子矩阵的特征值是 $7/5,7/5,1/5$，因而正定； 但整个矩阵在 $\mathbf1_4$ 上的特征值为 $-1/5$。 故全部原始三元测试通过而整体不合法。

$\square$

#### 定理 18.7：新增分支的递归兼容判据

设已有 $G\ge0$，新增一个归一分支，与旧分支的交叉列为 $g$。 记 $G^+$ 为 Moore–Penrose 广义逆。则

$$
\begin{pmatrix}G&g\\g^\dagger&1\end{pmatrix}\ge0
 \quad\Longleftrightarrow\quad
 g\in\operatorname{ran}G,\qquad
 g^\dagger G^+g\le1 .
\tag{Q21-C13}
$$

这里 $^\dagger$ 始终表示共轭转置。

**证明。**

正性先迫使 $g$ 正交于 $\ker G$，即 $g\in\operatorname{ran}G$。 写 $h=G^{+}g$，便有 $Gh=g$。 对任意列向量 $x$ 与标量 $t$，块二次型为

$$x^\dagger Gx+2\operatorname{Re}(x^\dagger gt)+|t|^2 =(x+ht)^\dagger G(x+ht) +|t|^2(1-g^\dagger G^{+}g).$$

若块矩阵为正，取 $x=-ht$ 即得第二条件。 反向由同一公式立即得到。

$\square$

式 (Q21-C13) 保留的是新分支与全部已有线性组合的关系。 因此可以逐次添加有限分支，并在每一步保存已经确定的比较； 但不能把这个条件换成“只检查原始标签中的每一组三个”。 若已经显式构造同一个环境内的记录向量 $e_j$， 则所有有限相关矩阵的正性由同一个内积自动保证。 这是构造性闭合，不是把四元以上的反例用定义删掉。

### 18.4　新过程的组合与同一记忆的回声

#### 定理 18.8：无共享记忆时的交叉映射组合律

设 $\Lambda$ 和 $\mathcal M$ 为同一控制标签上的两次确定完全正保迹操作， 其交叉映射分别为 $\Gamma_{jk}$ 和 $\Delta_{jk}$。 作为完整控制–目标系统上的普通通道组合， $\mathcal M\circ\Lambda$ 的交叉映射是

$$(\Delta\circ\Gamma)_{jk}=\Delta_{jk}\circ\Gamma_{jk}. \tag{Q21-C14}$$

若两次酉分支为 $U_j,V_j$，相关矩阵为 $G,D$， 则合成酉分支是 $V_jU_j$，相关矩阵是 $D\circ G=(\delta_{jk}\gamma_{jk})$。

**证明。**

对 $|j\rangle\langle k|\otimes X$ 连续应用 (Q21-C3) 即得第一式。 代入酉分支公式，得 $\delta_{jk}\gamma_{jk}V_jU_jXU_k^\dagger V_k^\dagger$。 相应有限环境实现使用记录 $e_j\otimes f_j$， 其反序 Gram 元为 $\langle e_k,e_j\rangle\langle f_k,f_j\rangle$， 故 $D\circ G\ge0$。

$\square$

#### 命题 18.9：同一个内部记忆不能被重置公式替代

存在两次完全相同的整体酉操作，使第一次约化控制过程完全去相干， 第二次操作后却恢复全部相干。 因此不能用第一次约化通道的自复合来描述同一记忆的再次使用。

**证明。**

目标取一维，控制 $C$ 与环境 $E$ 各取一个 qubit， 环境初态为 $|0\rangle$。 整体酉操作为

$$W=|0\rangle\langle0|_C\otimes I_E +|1\rangle\langle1|_C\otimes X_E .$$

第一次作用后，两个内部记录为 $e_0=|0\rangle,e_1=|1\rangle$， 故 $\gamma_{01}=0$，约化控制通道为完全去相干 $\mathcal D$。 再在同一个 $E$ 上作用同一个 $W$，有 $W^2=I$， 整体及约化控制初态全部恢复，合成过程的 $\gamma_{01}=1$。 但 $\mathcal D\circ\mathcal D=\mathcal D$，不会恢复相干。 更强地，控制初态 $|+\rangle$ 与 $|-\rangle$ 在第一次约化后 同为 $I/2$，第二次整体作用后却分别恢复为两个不同纯态； 因此不存在仅以第一次约化状态为输入、能同时给出这两个后继的函数。 差别在于第二次操作前 $C$ 与 $E$ 已相关； 从第二次的约化输入态单独出发，并不存在本例中所假定的同一个 与环境无关的约化通道 $\mathcal D$。

$\square$

**本区域闭合推出的内容。**

在已声明的有限维复量子接口和标签保持条件下： 完整过程由正 Choi 块矩阵分类； 两个分支之间的全部未定量是一个支撑空间间的收缩； 酉分支时缩为内部记录的相关矩阵； 三元约束给出精确行列式，新增分支由 Schur 条件逐次验收； 保留环境时全部步骤由同一个有限等距或酉实现闭合。 没有从普通分支通道唯一推出相干控制， 没有从三元原始数据推出所有有限整体， 没有从“观察者内生”推出任意参考资源都已可用。

<a id="section-19"></a>

## 19　固定点、有限三维提升与完整内部时间

**本区域的输入。**

$$I=[-1,1],\quad s\in\{-1,1\},\quad F_s(x)=s\cos x, \quad \omega:I\to\mathbb R\text{ Lipschitz},$$

$$T_s:I\times S^1\to I\times S^1,\qquad T_s(x,z)=(F_s(x),e^{i\omega(x)}z).$$

角度编码、反馈函数、符号政策和相位更新均为本区域给定资料， 不是六组主条件自行选定。$z$ 表示可访问的内部 *相对* 相位； 若它只是整体共同相位，应先按实际菜单取相位商。 本节的余弦与相位结论已经出现在 OTF-004、OTF-005， 以下给出所需证明并保留其输入。[\[36\]](#ref-otf4), [\[17\]](#ref-otf5)

#### 定义 19.1：固定点的二元关系

对 $f:X\to X$，定义 $\Gamma_f=\{(x,f(x)):x\in X\}$、 $\Delta_X=\{(x,x):x\in X\}$。 固定点集合准确为 $\Gamma_f\cap\Delta_X$ 在第一坐标的投影。

#### 定理 19.2：正负余弦与政策二周期

存在唯一 $r\in(0,1)$ 满足 $\cos r=r$。 $F_s$ 在实轴的唯一固定点为 $sr$，任意实初值一步后进入 $I$， 并以常数 $L=\sin1<1$ 几何收敛到 $sr$。 两方程 $\cos x=x$ 与 $\cos x=-x$ 没有共同实解。 若给定内部政策 $G(s,x)=(-s,-s\cos x)$，则

$$(1,r)\longleftrightarrow(-1,-r)$$

是一条二周期。

**证明。**

$\cos x-x$ 在 $0,1$ 端点异号。 任何实固定点模至多为一；在 $I$ 上中值定理给 $|F_s(x)-F_s(y)|\le L|x-y|$。 余弦偶性给 $F_s(sr)=sr$，压缩估计给唯一性与迭代误差 $|x_n-sr|\le L^{n-1}|x_1-sr|$。 同时满足两方程将迫使 $x=0$，与 $\cos0=1$ 矛盾。 把 $(1,r),(-1,-r)$ 依次代入 $G$ 即得二周期。

$\square$

若每步允许任意符号 $s_n$，则一步后 $|x_{n+1}|=\cos|x_n|$，故模长仍趋 $r$； 符号却可持续切换。这是给定政策的结论，未唯一规定自然常数、粒子种类或时间箭头。

#### 定理 19.3：标量固定不保证相位固定

令 $`x_*=sr`$、$`\omega_*=\omega(x_*)`$。级数

$$A(x)=\sum_{j=0}^{\infty}\bigl(\omega(F_s^j x)-\omega_*\bigr)$$

一致绝对收敛，且 $\operatorname{Lip}(A)\le K/(1-L)$，其中 $K=\operatorname{Lip}(\omega)$。 同胚 $\mathcal H(x,z)=(x,e^{iA(x)}z)$ 满足

$$\boxed{\mathcal H\circ T_s=(F_s\times R_{\omega_*})\circ\mathcal H,\quad R_{\omega_*}(z)=e^{i\omega_*}z.}$$

因此完整模型有固定点，当且仅当 $`\omega_*\in2\pi\mathbb Z`$； 有理非整数 $`\omega_*/2\pi=p/q`$ 给极限 $q$ 周期， 无理比值给极限圆上的稠密旋转。

**证明。**

每项绝对值至多 $`KL^j|x-x_*|\le2KL^j`$，给一致收敛； 逐项比较 $x,y$ 给 Lipschitz 界。 去掉首项得到

$$A(x)-A(F_sx)=\omega(x)-\omega_*.$$

将其代入 $\mathcal H(T_s(x,z))$ 即得共轭；逆为 $(x,z)\mapsto(x,e^{-iA(x)}z)$。 对迭代求和还给

$$z_n=e^{i[n\omega_*+A(x_0)-A(x_n)]}z_0, \quad |A(x_n)|\le\frac K{1-L}L^n|x_0-x_*|.$$

固定或周期点的基底必须是 $`x_*`$，因为 $F_s^q$ 仍压缩。 余下分类就是圆周旋转：有理转角返回，无理转角的整数倍模 $2\pi$ 稠密。 后者可由鸽巢原理得到任意小的非零整数倍角，再以其倍数逼近任意圆周角。

$\square$

#### 命题 19.4：完整幺正整体没有非平凡吸引固定点

若 $`\rho_n=U^n\rho_0(U^*)^n`$ 在迹范数下收敛到 $`\rho_*`$，则 $`\rho_0=\rho_*`$ 且 $`U\rho_0U^*=\rho_0`$。 若完整状态还包含严格追加的记录 $m\mapsto m+1$，也不存在固定点。

**证明。**

极限连续性给 $`U\rho_*U^*=\rho_*`$。 于是 $`\|\rho_n-\rho_*\|_1=\|\rho_0-\rho_*\|_1`$ 对全部 $n$ 成立； 左边趋零使初始差已经为零。记录部分的不动要求 $m=m+1$，不可能。

$\square$

### 19.1　三维图像与有限动态闭合

#### 命题 19.5：静态三维归一化

$$v(x)=(1,x,\cos x),\quad n(x)=v(x)/\|v(x)\|_2$$

给球面中的曲线，并且 $\cos x=\pm x$ 分别等价于 $n_3(x)=\pm n_2(x)$。 但若要求提升中线性读出原 $x$，余弦迭代没有任何精确有限维线性提升。

**证明。**

第一坐标非零，归一化不改变第二、第三坐标的等比关系，给静态结论。 对第二项，若存在有限特征 $\Theta$、固定矩阵 $K$， $\Theta(\cos x)=K\Theta(x)$，且 $1,x$ 均为 $\Theta$ 的线性读数， 则 $1,x,\cos x,\cos(\cos x),\ldots$ 全在同一个有限维函数空间。

这些函数实际上在每个非空实开区间上线性无关。 设 $f_0(x)=x,f_{j+1}=\cos f_j$，有限关系 $c_{-1}+\sum_{j=0}^Nc_jf_j=0$ 在区间成立。 各项整函数，解析恒等定理将关系延到实轴。 $f_0$ 无界，而所有 $j\ge1$ 项在实轴有界，故 $c_0=0$。 以 $y=\cos x$ 遍历 $[-1,1]$，余下关系变为 $c_{-1}+\sum_{j=1}^Nc_jf_{j-1}(y)=0$；再次解析延拓，得 $c_1=0$。 有限重复消去全部系数，矛盾。

$\square$

该命题没有排除状态依赖矩阵、近似、无限维表示或改变读出坐标的共轭。 归一化后的 $x=n_2/n_1$ 是比值读数，不能直接拿上一线性读数判据排除一切射影模型。 对所写自然坐标本身，还可独立证明不存在固定非零射影推进，附完整短证如下。

#### 命题 19.6：自然三维坐标没有固定射影线性推进

不存在固定 $M\in M_3(\mathbb R)$ 使 $Mv(x)=\lambda(x)v(\cos x)\ne0$ 在一个非空实开区间恒成立。

**证明。**

将三行记为 $(a,b,c),(d,e,f),(g,h,k)$。 首行给 $\lambda=a+bx+c\cos x$。 次行的整函数恒等式延拓到 $x=iy$，虚部给 $ey=by\cosh y$，故 $b=e=0$；实部给 $d+(f-a)\cosh y-c\cosh^2y=0$，故 $c=d=0,f=a$。 因此 $\lambda=a\ne0$。 第三行成为 $g+hx+k\cos x=a\cos(\cos x)$。 再置 $x=iy$，虚部使 $h=0$，右端有界而 $\cosh y$ 无界使 $k=0$。 取 $\cosh y=\pi,2\pi$，分别给 $g=-a,g=a$，矛盾。

$\square$

### 19.2　把钟和操作写进整体的一个有限模型

#### 定理 19.7：有限内部历史态与传播约束

给定门序列 $U_1,\ldots,U_N$，令 $V_0=I$、$V_k=U_k\cdots U_1$，

$$|\Psi\rangle=\frac1{\sqrt{N+1}}\sum_{k=0}^N|k\rangle_T\otimes V_k|\psi\rangle, \quad L_k=\langle k|\otimes I-\langle k-1|\otimes U_k, \quad G_{\rm hist}=\sum_{k=1}^NL_k^*L_k.$$

则 $G_{\rm hist}\ge0$、$G_{\rm hist}|\Psi\rangle=0$。 条件于内部钟记录 $k$ 的系统态为 $V_k|\psi\rangle$。

**证明。**

平方和给正性。每个 $L_k|\Psi\rangle$ 等于 $(V_k-U_kV_{k-1})|\psi\rangle/\sqrt{N+1}=0$。 钟投影 $|k\rangle\langle k|$ 的概率为 $1/(N+1)$，收缩并归一即得条件态。

$\square$

这属于关系时钟的有限数学实现；门、标签次序及初始数据均留在式中。[\[37\]](#ref-pw), [\[38\]](#ref-trinity), [\[39\]](#ref-baumann) 它不自动选择秒、连续时长或唯一宇宙态；$G_{\rm hist}$ 是传播约束，未被默认为驱动实际装置的 Hamiltonian。

若实验二值结果 $Y\in\{-1,1\}$ 仅满足 $\mathbb E[Y\mid x]=\cos x$， 则单次反馈 $x'=sY$ 一步后只取 $\pm1$，到 $sr$ 的距离至少为 $1-r>0$。 因此理想期望反馈的压缩不等于单次量子结果的轨迹。 重复准备、估计误差和控制资源均须作为内部协议继续保留。

<a id="section-20"></a>

## 20　内部表示、对角边界与全局余弦的算术表达力

**输入：** 指定的表达语言、合法读出类与评价规则。 讨论不完备时还需有效公理化、一致性及足够的算术表达力。 **输出：** 表达像的对角障碍、定义保守性及相应不可证性。 本节不以这些逻辑结果代替几何正性、复线性、Born 或时间接口。

### 20.1　不需要负存在的对角障碍

#### 定理 20.1：内部自评价的精确对角条件

设 $E:A\times A\to Y$ 为全域评价表， $\alpha:Y\to Y$ 为指定响应。 若存在 $a\in A$ 使

$$E(a,x)=\alpha(E(x,x))\qquad(x\in A),$$

则 $\alpha$ 有不动点。

**证明。**

取 $y=E(a,a)$，代入 $x=a$，即得 $y=\alpha(y)$。

$\square$

这就是 Lawvere 固定点定理的集合形式[\[40\]](#ref-q022-lawvere)， 也已见项目 R5-006 §8。 如果全部允许响应都可由旧行表示， 且允许响应类包含 $x\mapsto\alpha(E(x,x))$， 则每个允许的 $\alpha$ 都必须有不动点。

取两个正的存在标签 $Y=\{1,2\}$，令 $\alpha(1)=2,\alpha(2)=1$，便没有不动点。 因此“全域评价、全部表示、允许该对角反转”不能同时成立。 这不使用任何负存在。 若改用 $Y=[0,1]$、$\alpha(y)=1-y$， 不动点 $1/2$ 只解除这一特定反转的矛盾， 没有推出 Born 规则。 $\cos$ 有不动点也不能反向证明全部内部表示条件。

### 20.2　定义、证明与真值应分别计账

#### 定理 20.2：显式关系定义的保守性

设 $T$ 使用语言 $L$，$\varphi(x)$ 是旧语言公式。 加入新关系符号 $R$ 及定义 $R(x)\leftrightarrow\varphi(x)$，得到 $T'$。 对任意旧语言句子 $\psi$，有

$$T'\vdash\psi\iff T\vdash\psi.$$

**证明。**

先对绑定变量重命名以免捕获， 再把新证明中 $R(t)$ 的每次出现替换为 $\varphi(t)$。 定义公理化为逻辑恒真式，旧公理与推理步骤仍有效， 得到 $T$ 中的证明。反向由 $T\subseteq T'$。

$\square$

所以把约束写进定义能明确研究对象，却不会自动证明原世界满足这些约束。 若引入函数符号，相关唯一存在必须先在旧理论中证明， 才能按通常规则称为保守定义扩展。

#### 引理 20.3：对角句的条件性构造

固定句法编码：$\#\varphi\in\mathbb N$ 表示公式代码， $\ulcorner\varphi\urcorner:=\overline{\#\varphi}$ 表示对象语言中的对应数码。 令 $d(n)$ 为把代码 $n$ 的单自由变量公式 代入其自身代码数码后得到的句子代码；非法或非单自由变量代码统一取 $d(n)=0$。 假设理论 $T$ 中的关系 $D(x,y)$ 对每个标准自然数 $n$ 满足

$$T\vdash\forall y\,[D(\bar n,y)\leftrightarrow y=\overline{d(n)}].$$

则对每个单自由变量公式 $\theta(y)$，存在句子 $G$ 使

$$T\vdash G\leftrightarrow\theta(\ulcorner G\urcorner).$$

**证明。**

令 $\beta(x):=\exists y\,[D(x,y)\land\theta(y)]$， $b:=\#\beta$，并令 $G:=\beta(\bar b)$。 按 $d$ 的定义，$d(b)=\#G$。 使用关于固定标准数 $b$ 的显示条件，得

$$T\vdash G\leftrightarrow \exists y\,[y=\overline{d(b)}\land\theta(y)] \leftrightarrow\theta(\ulcorner G\urcorner).$$

$\square$

这里的句法编码与递归代入可表示性是明确逻辑基础， 在足够算术中由标准算术化取得；本稿不把它们算成由量子面积导出的事实。 新句子的代码仍是同一自然数域中的一个数。

#### 定理 20.4：第二不完备的条件性核心

令 $T$ 为一致经典理论，具有上述对角构造。 记 $\Box\varphi:=\operatorname{Prov}_T(\ulcorner\varphi\urcorner)$， 并明确要求 Hilbert–Bernays–Löb 三个可导性条件：

$$
\begin{aligned}
T\vdash\varphi&\ \Longrightarrow\ T\vdash\Box\varphi,\\
T&\vdash\Box(\varphi\to\psi)\to(\Box\varphi\to\Box\psi),\\
T&\vdash\Box\varphi\to\Box\Box\varphi.
\end{aligned}
$$

若 $\operatorname{Con}(T):=\neg\Box\bot$，则

$$T\nvdash\operatorname{Con}(T).$$

**证明。**

对角构造给 $T\vdash G\leftrightarrow\neg\Box G$。 首先 $T\nvdash G$：否则第一可导性条件给 $T\vdash\Box G$， 而该等价式给 $T\vdash\neg\Box G$，违反一致性。

在 $T$ 内，由 $G\to\neg\Box G$ 和前两可导性条件有

$$\Box G\to\Box\neg\Box G.$$

第三条件又给 $\Box G\to\Box\Box G$。 将经典恒真式 $\neg\Box G\to(\Box G\to\bot)$ 用前两条件搬入可证明性中，得到

$$\Box\neg\Box G\to(\Box\Box G\to\Box\bot).$$

因此 $T\vdash\Box G\to\Box\bot$。 经典逆否及对角等价式给

$$T\vdash\operatorname{Con}(T)\to\neg\Box G,\qquad T\vdash\neg\Box G\to G.$$

故

$$T\vdash\operatorname{Con}(T)\to G.$$

若 $T\vdash\operatorname{Con}(T)$，就有 $T\vdash G$， 与第一段矛盾。

$\square$

这是在列明可导性条件后的完整短证明，不把任意自称“可证明”的谓词 都视为标准证明谓词，也不把第二不完备用于任意有限关系表。 有关 Gödel 两个定理的作者级机器形式化可参见 Paulson[\[41\]](#ref-q022-paulson)。

#### 命题 20.5：Gödel–Rosser 的适用范围

一致、有效可公理化且包含或有效解释足够算术的经典理论， 例如包含 Robinson $Q$ 的理论，不完备。 即存在句子 $R_T$，使

$$T\nvdash R_T,\qquad T\nvdash\neg R_T.$$

这里引用标准 Gödel–Rosser 定理，而不把对原始 Gödel 句的 单侧不可证短证当成 Rosser 的完整证明。 Gödel 原文与 Rosser 的加强分别见 [\[42\]](#ref-q022-godel), [\[43\]](#ref-q022-rosser)。 项目 R5-006 §9.2–9.4 已明确保留对角引理、 原始句与 Rosser 句的区别，以及第二不完备的可导性条件； 作者级机器形式化可参见 Paulson[\[41\]](#ref-q022-paulson)。

#### 定理 20.6：同层全真值障碍

设经典理论 $T$ 具有所需语法编码与对角引理。 若同一语言中的谓词 $\operatorname{Tru}$， 对包含该谓词自身的每个句子 $\varphi$ 都满足

$$T\vdash\operatorname{Tru}(\ulcorner\varphi\urcorner) \leftrightarrow\varphi,$$

则 $T$ 不一致。

**证明。**

对角引理给句子 $L$，使

$$T\vdash L\leftrightarrow \neg\operatorname{Tru}(\ulcorner L\urcorner).$$

对 $L$ 使用真值条件，得到 $T\vdash L\leftrightarrow\neg L$， 与经典一致性不相容。

$\square$

这是一种 Tarski 型真值障碍[\[44\]](#ref-q022-tarski-truth)。 语法代码可以仍在同一个自然数域里； 分层真值关系也可以作为同一整体中的有类型对象。 这些定理没有推出空间每次增加一根轴。

### 20.3　固定有限的代数量子关系可判定

#### 定理 20.7：有限代数量子片段的有效归约

考虑每次给定固定有限矩阵尺寸的公式， 只使用实代数常数、复向量与矩阵的加乘、伴随、有限张量积、 迹、秩约束、正性、归一化和有限次一阶量词。 该公式能有效翻译为实闭域公式，其闭句真值可判定。

**证明。**

每个复坐标以两个实坐标表示。 复加乘、共轭及固定尺寸的矩阵运算均变为有限个实多项式。 正性可写成 $`X=B^*B`$ 对某个同尺寸复矩阵 $B$ 成立， 故也能用一阶多项式关系表示。 秩不超过 $r$ 由全部 $(r+1)$ 阶子式为零表达； 酉性为 $`U^*U=I`$，密度态、效果和 Choi 条件均由这些关系组合。 实代数常数用整系数多项式及隔离区间有效指定。 因此每个公式翻译为有限个实变量上的有序域公式。 应用 Tarski 的有效消去量词定理，即得判定算法 [\[45\]](#ref-q022-tarski-decision), [\[46\]](#ref-q022-marker)。

$\square$

这里完整证明的是到实闭域的归约，量词消去作为明确的成熟定理引用。 该片段不包含任意实数输入 oracle，不包含对无界离散历史或矩阵维数的 内层量化，也不包含全局 $\cos,\exp$ 或任意微分方程。 实闭域语言不能定义完整自然数算术； 其一维可定义集合是有限个点与区间的并， 特别地不能定义 $\mathbb Z$[\[46\]](#ref-q022-marker)。

### 20.4　全局余弦却可在同一实轴中定义整数

#### 定理 20.8：全局余弦的算术解释

在标准结构

$$\mathcal R_{\cos} =(\mathbb R;0,1,+,\times,<,\cos)$$

中定义

$$
\begin{split}
 \operatorname{Per}(p)\ \Longleftrightarrow\
 &p>0\ \land\ \cos p=1\\
 &{}\land\forall u\,(0<u<p\Rightarrow\cos u\ne1).
\end{split}
$$

则 $\operatorname{Per}$ 恰好定义 $p=2\pi$。 进而

$$\operatorname{Int}(x) \ \Longleftrightarrow\ \exists p\,[\operatorname{Per}(p)\land\cos(px)=1]$$

恰好定义 $\mathbb Z$。 再令 $\operatorname{Nat}(x)\leftrightarrow \operatorname{Int}(x)\land x\ge0$， 实加乘在该定义集上的限制就是标准自然数加乘。

**证明。**

全局余弦满足 $\cos t=1\iff t=2\pi k$ 对某个 $k\in\mathbb Z$ 成立。 故最小正根恰为 $2\pi$，且 $\cos(2\pi x)=1\iff x\in\mathbb Z$。 自然数定义与加乘限制随即成立。

$\square$

#### 定理 20.9：完整真理论不可判定，但语义上完备

所有真句组成的 $\operatorname{Th}(\mathcal R_{\cos})$ 是完备理论，但不可判定，也不可有效公理化。

**证明。**

把任意算术句 $\varphi$ 的量词限制到 $\operatorname{Nat}$：

$$(\exists n\,\psi)^* =\exists x\,(\operatorname{Nat}(x)\land\psi^*),$$

$$(\forall n\,\psi)^* =\forall x\,(\operatorname{Nat}(x)\Rightarrow\psi^*).$$

加乘项不变。对公式结构归纳得到

$$\mathbb N\models\varphi \iff \mathcal R_{\cos}\models\varphi^*.$$

若后者的全部真句可判定，就能判定全部真算术，矛盾。 所有真句的集合按定义对每个句子包含它或其否定，因此语义上完备。 若该集合还可有效公理化，则同时枚举某句与其否定的证明， 完备性保证其中一个搜索终止，得到判定算法，再次矛盾。

$\square$

这里的算术不可判定性可由 Gödel–Rosser 得到： 若全部真算术可判定，它本身就给出一致、有效、完备且包含足够算术的理论。 全局周期函数与算术不可判定性的关系也属于成熟研究范围； Richardson 的原论文研究更受限表达式类的不同判定问题， 其具体前提不能与上述全一阶归约互换[\[47\]](#ref-q022-richardson)。

因此应分开三个对象：

1.  单个任务 $\cos x=x$：有唯一可计算实不动点；

2.  限制区间上的余弦：本节的全局周期编码证明不适用；

3.  全局余弦加上实加乘与任意一阶量化： 能定义整数，整个真理论不可判定。

不完备结论作用于一致、有效且足够表达算术的公理体系； 不能把完整真理论 $\operatorname{Th}(\mathcal R_{\cos})$ 本身误写成“语义不完备”。

这给出用户所提余弦与不完备之间的一条准确联系： 改变的是允许的运算、编码和量化范围； 一个不动点已经找到，不代表同一语言内的全部命题已经封闭判定。 该联系没有从逻辑推出面积、量子概率或物理时间。

<a id="section-21"></a>

## 21　有限关系的三种闭合：预测、实现与有效停止

本节接入项目新收录的 OTF-007、丢番图读出札记与 UPPM-RG-002。 来源文件的新增不等于其所用经典定理首次出现。 我们分别标明代数表示、指定未来的充分预测、有限算法与物理实现的条件， 不把它们合并成“有限三元关系已经解决全部问题”。 [\[8\]](#ref-otf724), [\[9\]](#ref-dio24), [\[10\]](#ref-uppmrg224)

### 21.1　预测闭包的精确用途与实现边界

**输入：** 固定有限总 Hilbert 空间；已给有限 CP 迹不增分支菜单， 每个完整仪器的全部输出（含失败与停止）满足迹保持； 初始线性效果空间含 $I$；对象、控制、参考与记录的类型已经声明。 **输出：** 定理 16.13 的幂等未来空间及以下更新式。 该闭包只覆盖这些已给分支的合法有限协议。 判断精确线性相关还需可判定的系数域，或足够的认证秩间隙。

#### 命题 21.1：闭合读数的内部更新

取闭合空间 $V_\infty$ 的实基 $F_0=I,F_1,\ldots,F_{s-1}$， 令 $q_i(\rho)=\operatorname{Tr}(F_i\rho)$。对任意给定分支 $a$，存在实矩阵 $C_a$，使

$$\Phi_a^*(F_j)=\sum_{i=0}^{s-1}(C_a)_{ji}F_i.$$

其分支概率与条件更新分别为

$$p_a=(C_aq)_0,\qquad q'_j=\frac{(C_aq)_j}{(C_aq)_0}\quad(p_a>0).$$

未归一读数的更新始终是 $\widetilde q'=C_aq$，包括零概率分支。

**证明。**

$V_\infty$ 由每个 $`\Phi_a^*`$ 保持，所以基展开存在且唯一。 迹对偶给出

$$\operatorname{Tr}(F_j\Phi_a(\rho))=\sum_i(C_a)_{ji}\operatorname{Tr}(F_i\rho).$$

取 $j=0$ 得分支质量，再除以非零质量即得条件态读数。 对零概率分支只保留未归一的零质量，不作未定义的除法。

$\square$

#### 反例 21.2：线性预测投影不必是物理通道

在 qubit 上令

$$\Psi(\rho)=\frac{\rho+\rho^{\mathsf T}}2.$$

它保留 $I,X,Z$ 的读数，去掉 $Y$，正、迹保持且幂等。 但是它不完全正。

**证明。**

转置保持正性与迹，故前三项性质由定义成立；二次作用仍给同一实对称部分。 令 $\lvert\Phi^+\rangle=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$，$S$ 为交换两因子的算子。 直接展开四个矩阵单位可得

$$(\operatorname{id}\otimes\Psi)(\lvert\Phi^+\rangle\langle\Phi^+\rvert) =\tfrac12\lvert\Phi^+\rangle\langle\Phi^+\rvert+\tfrac14S.$$

在 $\lvert\psi^-\rangle=(\lvert 01\rangle-\lvert 10\rangle)/\sqrt2$ 上， 右侧期望值为 $-1/4$，所以带内部参考后的输出不正。

$\square$

这个既有反例正是 OTF-007 第 6.5 节的边界。 有限维张成在有限步停止，是线性代数结论； 将该坐标商制成可与任意内部参考共同使用的压缩装置，另需 CP 编码与恢复合同。 只知道矩阵元是可计算实数，也不自动得到判定它是否精确为零的算法。 [\[8\]](#ref-otf724)（第6.5–6.6节）

### 21.2　把每个运算写成二元、三元关系

**输入：** 有理数的精确有限编码、有限算术电路及其共享变量身份。 **输出：** 等价的局部二次关系网络与一个四次平方和方程。 这里证明的是表达等价性，没有预付其解的高度界、搜索停止界或物理实现。

#### 定理 21.3：有限算术的三变量编译

任意有理系数多项式方程 $f(\mathbf x)=0$， 都能有效改写为有限个局部方程 $r_j(\mathbf x,\mathbf z)=0$： 每个 $r_j$ 至多涉及三个变量、次数不超过二， 并且

$$f(\mathbf x)=0 \quad\Longleftrightarrow\quad \exists\mathbf z\in\mathbb Q^m:\quad \sum_j r_j(\mathbf x,\mathbf z)^2=0.$$

对给定 $\mathbf x$，电路的所有中间变量唯一。 若还允许除法门，须同时保留其非零分母守卫。

**证明。**

给每个算术门的输出引入一个新变量，把加法、乘法与常数门分别写成

$$z-x-y=0,\qquad z-xy=0,\qquad z-c=0,$$

并加上最终输出为零的方程。 按电路的拓扑顺序，已给输入唯一决定每个中间输出， 故原方程与该网络等价；同一条线在所有后继门中使用同一个变量。 有理数上每个平方非负，因而平方和为零当且仅当每项为零。 各项次数至多二，故平方和次数至多四；清除系数分母可得整数系数方程。 对于 $z=a/b$，加入 $bu-1=0$ 与 $bz-a=0$， 前式强制 $b\ne0$ 且唯一指定 $u=1/b$，后式唯一指定商。

$\square$

局部门数有限不代表数值长度有统一上界。 例如从 $z_0=2$ 出发，只用 $T$ 个平方门 $z_{j+1}=z_j^2$， 便得到 $z_T=2^{2^T}$，其二进制整数表示需要 $2^T+1$ 位。 上述编译是 UPPM-RG-002 第 4 节所用的经典算术编译； 它允许把整个过程也列入同一关系表，但不会免除数值表示成本。 [\[10\]](#ref-uppmrg224)（第4节）

### 21.3　有限存在描述与无条件可读出之间的边界

#### 定义 21.4：单独登记的算术输入 $\mathsf D$

假设已给定一个固定、有限且有效描述的整数多项式 $P(t,\mathbf w)$，满足

$$t\in\mathbb Z \quad\Longleftrightarrow\quad \exists\mathbf w\in\mathbb Q^m:\ P(t,\mathbf w)=0 \qquad(t\in\mathbb Q).$$

这称为本节的条件 $\mathsf D$，对应来源的 $\mathsf H_{\mathbb Z/\mathbb Q}$。

最新公开原稿 Version 13（2026 年 11 月 7 日）按定理声称上述存在定义； 其公开说明同时保留完整主目标尚未形式化证明的边界。 本稿未独立认证该长篇算术证明，以下所有消费它的结论都保留 $\mathsf D$。 [\[48\]](#ref-glazer13)[\[10\]](#ref-uppmrg224)（第1、3节）

另登记经典 DPRM 定理作为本节的已知外部数学结果： 存在固定整数多项式 $F(e,\mathbf x)$，使程序 $e$ 停机当且仅当 它对某组整数 $\mathbf x$ 为零。 自然数见证若需改成整数见证，可用四平方和编码； 本节不重证 DPRM 定理。[\[49\]](#ref-matiyasevich24)

#### 定理 21.5：条件性固定网络的不可判定性

在 $\mathsf D$ 与上述 DPRM 输入下，存在一个固定的有限三变量二次关系网络， 只有整数参数 $e$ 改变，其有理数解存在性不可判定。

**证明。**

取 DPRM 的 $F$，对每个整数见证坐标 $x_i$ 引入一份 $P$ 的见证，令

$$U(e,\mathbf x,\mathbf w) =F(e,\mathbf x)^2+\sum_iP(x_i,\mathbf w_i)^2.$$

有理平方和为零强制所有项为零，$\mathsf D$ 又强制每个 $x_i$ 为整数。 反向，为每个整数 $x_i$ 选取 $P$ 的见证即可。 所以程序 $e$ 停机当且仅当 $U(e,\cdot)$ 有有理数零点。 $F,P,U$ 都固定，定理 21.3 给出同一个固定网络； 若其解存在性可判定，就可判定停机，矛盾。

$\square$

这里始终是有限个变量、有限张局部关系， 但变量取值域 $\mathbb Q$ 无限，见证编码长度未被界定。 它与固定有限维线性空间的张成闭包没有冲突。 局部网络的共享赋值还须满足全部关系；每个局部关系分别有解并不提供共同解。

#### 命题 21.6：存在投影不是纤维上的既有真值

令 $q:X\to Y$、$C\subset X$。 存在判定 $y\in q(C)$ 是一个良定的新目标， 但 $\mathbf1_C$ 能写成 $h\circ q$ 当且仅当它在每个 $q$ 纤维上常值。

**证明。**

若 $\mathbf1_C=h\circ q$，同纤维的值显然相等。 若纤维上常值，令 $h(y)$ 等于该共同值即得分解。 例如 $q(t,w)=t$、$C=\{(t,w):w^2=t\}$， $(1,1)\in C$、$(1,0)\notin C$，却有同一读数 $t=1$。 因此“存在某个见证”不是已读到的那一个内部赋值满足条件。

$\square$

### 21.4　何时精确读出真的可以停下来

#### 定理 21.7：有效见证界的充要条件

设 $R(x,w)$ 是有限字符串上的可判定关系， $L=\{x:\exists w\ R(x,w)\}$。 $L$ 可判定，当且仅当存在总可计算函数 $b:\mathbb N\to\mathbb N$，使

$$x\in L\ \Longrightarrow\ \exists w:\ R(x,w)\quad\text{且}\quad |w|\le b(|x|).$$

**证明。**

若有 $b$，只需枚举并检查长度不超过 $b(|x|)$ 的有限个见证， 有一个成功则接受，否则拒绝。 反向，若 $L$ 有判定器，给定 $n$，先判定所有长度不超过 $n$ 的有限个输入。 对其中每个被接受的输入枚举见证，直到找到一个；所有这些搜索都会结束。 取已找到见证长度的最大值；若没有被接受的输入，取零。 这是一个总可计算的 $b(n)$，且满足要求。

$\square$

在 $\mathsf D$ 下，定理 21.5 的通用网络没有这种统一界。 但固定 $P(t,\mathbf w)$ 的整数成员参数问题有这种界： 最简有理数 $t$ 的分母是否为一可判定，故上一定理适用。 后者给某个可计算最坏界，不给实际可用或多项式的界。 这些区别在两份新项目稿中均已明确。 [\[10\]](#ref-uppmrg224)（第6节）[\[9\]](#ref-dio24)（第6节）

#### 引理 21.8：给定高度后的非零间隙

若 $f\in\mathbb Z[x_1,\ldots,x_m]$ 对 $x_i$ 的次数不超过 $d_i$， 且 $x_i=a_i/b_i$、$1\le b_i\le H$，则

$$f(\mathbf x)\ne0\quad\Longrightarrow\quad |f(\mathbf x)|\ge H^{-\sum_i d_i}.$$

**证明。**

乘以 $D=\prod_i b_i^{d_i}$ 后，$Df(\mathbf x)$ 是整数。 非零时其绝对值至少为一，且 $D\le H^{\sum_i d_i}$，即得结论。

$\square$

故在已给高度承诺时，误差小于上述间隙三分之一的认证近似， 可用间隙二分之一作为阈值决定是否精确为零。 没有高度或另一正间隙合同，单纯残差趋于零不能提供同一个决定规则。

#### 命题 21.9：可计算正读数不自动带零值判定

对有理多项式 $f$，有效枚举全部有理元组 $w_1,w_2,\ldots$，令

$$\pi(f)=\sum_{j\ge1}2^{-j}\mathbf1_{\{f(w_j)=0\}}.$$

则 $\pi(f)\in[0,1]$ 为一致可计算实数，且 $\pi(f)>0$ 当且仅当 $f$ 有有理零点。 在 $\mathsf D$ 下，通用实例上没有总可计算的正有理函数 $g(f)$， 保证 $\pi(f)>0\Rightarrow\pi(f)\ge g(f)$。

**证明。**

每个代入可精确判定，前 $N$ 项之和可计算，尾项至多 $2^{-N}$。 全部项非负且每个权重正，故正值与解存在性等价。 若有这样的 $g$，有效选择 $N$ 使 $2^{-N}<g(f)/2$。 无解时前 $N$ 项和为零；有解时该和大于 $g(f)/2$。 所以可判定解存在性，与条件性定理 21.5 矛盾。

$\square$

这个概率是明确选择权重后的数学编码，不是从主候选推出的 Born 概率， 也没有免费提供一次测量就判定精确零值的装置。[\[10\]](#ref-uppmrg224)（第7节）

#### 命题 21.10：已有有效收敛模仍可缺少零值判据

存在一致可计算的一族 $1/2$ 压缩映射，其不动点是否为零不可判定。 此结论不依赖 $\mathsf D$。

**证明。**

令 $r_e=2^{-\tau}$，若程序 $e$ 在第 $\tau\ge1$ 步停机；否则令 $r_e=0$。 模拟 $N$ 步即可把它逼近到误差不超过 $2^{-N}$，故 $r_e$ 一致可计算。 $T_e(x)=(x+r_e)/2$ 为 $1/2$ 压缩，唯一不动点为 $r_e$， 从零迭代的误差至多 $2^{-N}$。 若可判定不动点是否为零，就可判定程序是否停机。

$\square$

### 21.5　本区域输入账本

| 明确输入 | 已闭合输出 | 没有随之推出 |
|:---|:---|:---|
| 固定有限 CP 菜单与线性读口 | 最小未来空间、有限停止与条件更新 | 对未知未来的充分性、任意 CP 压缩装置。 |
| 精确有理算术与有限电路 | 同源共享变量的二、三元网络 | 搜索界、有限数值长度或低物理成本。 |
| 条件 $\mathsf D$ 加已知 DPRM | 固定有限网络的条件性不可判定性 | 本稿对 $\mathsf D$ 的独立认证。 |
| 可判定验证关系与有效见证界 | 全部实例的有限判定算法 | 该界自动存在或算法为多项式时间。 |
| 给定高度或有效正间隙 | 足够精度后的零值判定 | 无间隙时的精确零值预言。 |

**本区域的白话。**

把每一步都写成两三个对象之间的关系，可以把整个过程收进同一张网络。 若网络只是在一个固定有限空间里生成新的线性读数，它会补齐并停止。 若网络要求在无限多种数值中寻找一个见证，有限的画面仍可能没有统一的搜索终点。 要把“存在这样的关系”变成“观察者现在能准确读出”，还必须交代见证范围、 精度间隙和真正实现这些读数的操作。

<a id="section-22"></a>

## 22　项目新进展：共同面积表与自己生成的三轴

本节重证固定项目中已经写出的条件性结果，主体是中央响应卷第 61–64 节 和移位单位铅笔卷定理 2.1。它们使用项目自己的完整正表与 PB 合同， 不从本轮单探针增长条件 $\mathsf G$ 自动产生。 来源的 JB 范数 $N$ 在本节改记 $N_{\rm src}$，以区别本稿的读出零核 $N$。它也与本轮尚未标定的原读出 $p$ 不同； 本轮一般只有 $p=\ell^\alpha$，不能把原 $p$ 直接称为范数， 也不能把原 $p^2$ 直接解释为 Born 概率。

### 22.1　完整原条件与明确消费的旧接口

#### 定义 22.1：同一原关系合同

原数据是实 Archimedean 序单位空间 $(E,C,u)$、原范数 $N_{\rm src}$、 分离原元素且准确决定锥的正实线性评价族 $\mathcal P$， 以及同一对总映射 $S,D:E^2\to E$。 准确锥指 $x\in C\Longleftrightarrow \alpha(x)\ge0$ 对全部 $\alpha\in\mathcal P$ 成立。 各质量 $\alpha(u)$ 保留原值，包括零、不等和次归一质量。 完整来源保留：

1.  A1：对全部原 $a,b$、$\alpha\in\mathcal P$，令 $(a_1,a_2)=(a,b)$，有向二表 $G^\alpha_{ij}=\alpha S(a_i,a_j)-i\alpha D(a_i,a_j)$ 为 Hermitian 半正定矩阵；不是只检验其行列式。

2.  A2：对 $(x_1,x_2,x_3)=(a+b,a,b)$ 及全部排列， $M_{ij}=\alpha S(x_i,x_j)$ 实半正定； 在显示顺序上 $(1,-1,-1)M(1,-1,-1)^{\mathsf T}=0$。

3.  A3：$S(u,u)=u$，并对同一个固定有理 $0<\theta\le1$， $0\le e\le\theta u$ 蕴含 $S(e,e)\le e$。

4.  在已得 $S(a,b)=a\circ b$ 的接口上，对全部原 $a,b,c\in E$， 完整三元配平为

    $$
    \begin{aligned}
    \nu&=D(a,b)-a\circ c,&
     \omega&=a\circ b+D(a,c),\\
    D(b+\nu,c+\omega)-D(b-\nu,c-\omega)
     &=-2b\circ\nu-2c\circ\omega .
    \end{aligned}
    \tag{22.1}
    $$

原 $\Omega$、实际准备、完整菜单、同源联合、全仪器输出、 所有合法历史与每个合法未来、失败与停止、真实双向返回等来源条件， 按源定义 58.3、66.1 保留。上述分组不宣称逻辑独立或公理数最小。 [\[2\]](#ref-radial24)（定义53.1、60.1及66.1）

下面明确使用来源已经恢复的 Jordan 乘法、自身 JB 完成 $X$， 及忠实、含单位、等距、准确保锥的 JC 包含

$$E\subset X\subset\mathcal A_{\rm sa},\qquad a\circ b=(ab+ba)/2,\qquad N_{\rm src}(a)=\|a\|_{\mathcal A}.$$

$E$ 可不完备，不要求等于环境的整个自伴部。 本节按来源接口使用这些结论，不重证其全部上游恢复。 完整二表预算对所有环境数学态 $\phi$、全部原 $a,b$ 给

$$|\phi D(a,b)|^2\le\phi(a^2)\phi(b^2)-\phi(a\circ b)^2. \tag{22.2}$$

数学态在这里用于分离，不自动是实际可准备态。

#### 定义 22.2：四项已支付接口

以下均作用于同一个旧 $D$，而非另造的线性替代品：

1.  原反对称性、各槽奇性、零输入， 以及实际输入对的 $\mathrm{SO}(2)$ 不变性： $D(Q(a,b))=D(a,b)$。

2.  对任意原 $h^2=u$，令 $V_h=\{b\in E:h\circ b=0\}$、$J_hb=D(h,b)$。 全部实横向强度与径向给 $D(sh,tb)=stJ_hb$（$s,t\in\mathbb R,\ b\in V_h$）。 另有

    $$
    J_hb\in V_h,\quad J_h^2b=-b,\quad
     (J_hb)^2=b^2,\quad b\circ J_hb=0.
    $$

3.  每个自身平面保留 $J_h(\xi b+\eta J_hb)=\xi J_hb-\eta b$。 若原实线性子空间 $L\subset V_h$ 的全部交叠 $b\circ c$ 都在全局 Jordan 中心 $Z(X)$， 则 $J_h|_L:L\to V_h$ 实线性；未预付 $J_h(L)\subset L$。

4.  同轴仿射零行 $D(su+xa,tu+ya)=0$ 对全部原 $a$ 与实 $s,t,x,y$ 成立。

它们分别消费三角卷 185.1、中央响应卷 19–20、29.1、35.1； 源第 61–62 节明确列出这一依赖。 本节不把它们缩写成无前提的“存在性”。 [\[2\]](#ref-radial24)（第60–65节）[\[3\]](#ref-pencil24)（定义1.1）

### 22.2　同一原窗口上的有向面积确实恢复双线性

#### 定义 22.3：标量平方窗口

选择原实线性子空间 $W\subset E$，满足 $x^2\in\mathbb R u$ 对每个 $x\in W$ 成立。 不要求 $W$ 有限维、完备或输出闭合。 非零 $X$ 中，由 Jordan 极化唯一得到

$$x\circ y=g(x,y)u,\qquad x^2=g(x,x)u.$$

$g$ 实对称双线性；自伴平方正性及平方零只在零元素成立， 使 $g$ 正定，且 $N_{\rm src}(x)^2=g(x,x)$。 因此每个非零 $x$ 仅除以正实数 $N_{\rm src}(x)$， 就得到真正原单位方向 $h=x/N_{\rm src}(x)$。 零 $X$ 时 $W=0$，以下结论按零对象理解。

#### 定理 22.4：整片原二维平面的行列式律；来源61.1

若 $h,k\in W$ 为 $g$ 正交单位对，则对任意实 $\alpha,\beta,\gamma,\delta$，

$$D(\alpha h+\beta k,\gamma h+\delta k) =(\alpha\delta-\beta\gamma)D(h,k). \tag{22.3}$$

**证明。**

记两份输入为 $x,y$。若它们独立，用 $Q\in\mathrm{SO}(2)$ 对角化它们的实二阶 Gram 矩阵，得到原正交输入 $x',y'$， 且旧值仍为 $D(x,y)$。 令 $r=N_{\rm src}(x')>0$、$s=N_{\rm src}(y')>0$，写 $x'=rh'$、$y'=sk'$。 已支付的横向缩放给 $D(x',y')=rsD(h',k')$。 两组正交单位基由某 $O\in\mathrm O(2)$ 相联系； $\det O=1$ 时用原旋转不变性，$\det O=-1$ 时另用一次输入奇性， 得 $D(h',k')=(\det O)D(h,k)$。 而 $\det Q=1$ 给 $rs\det O=\alpha\delta-\beta\gamma$，故结论成立。 这里不能把 $\det Q=1$ 误作 $\det O=1$。 若 $x,y$ 相关，一次原 $\mathrm{SO}(2)$ 旋转可令一个输入为零， 两边都为零。

$\square$

#### 定理 22.5：同一个旧窗口响应的双线性；来源62.1

$D|_{W\times W}:W\times W\to E$ 是实交替双线性。 对非零 $x\in W$，令 $r=N_{\rm src}(x)$、$h=x/r$ 及 $P_hy=y-g(h,y)h$，则

$$D(x,y)=rJ_h(P_hy), \tag{22.4}$$

$$D(x,y)^2=\bigl(g(x,x)g(y,y)-g(x,y)^2\bigr)u,$$

$$D(x,y)\circ D(x,z) =\bigl(g(x,x)g(y,z)-g(x,y)g(x,z)\bigr)u. \tag{22.5}$$

等价地，存在唯一实线性映射 $\mathcal B:\Lambda^2W\to E$，使 $\mathcal B(x\wedge y)=D(x,y)$。

**证明。**

若 $P_hy=0$，相关对的零值给式 (22.4)。 否则以 $k=P_hy/N_{\rm src}(P_hy)$ 和 $h$ 为原正交单位对， 应用定理 22.4，再用已支付的横向径向式即得该式。 此时没有把未知 $D$ 在 $y$ 的两个分量上先行拆开。

原 $W_h=W\cap V_h$ 的任意交叠都为实数倍单位，故在全局中心； 定义 22.2 已给 $J_h|_{W_h}$ 实线性。 $P_h$ 本身实线性，因此投影公式先支付第二槽线性。 $x=0$ 用零行，原反对称性再支付第一槽线性。 面积平方由 $(J_hP_hy)^2=g(P_hy,P_hy)u$ 得到； 在已证明第二槽可加之后，才将该式对 $y+z$ 极化，得到混合关系。 外幂表示是交替双线性的标准泛性质，没有新增自由度。

$\square$

这里输出在原 $E$ 中，不保证在 $W$ 中。 面积式只识别可分解面积及同一首方向的混合 Gram， 没有断言整个 $\Lambda^2W$ 的像都具有标量 Gram， 更没有把 $D|_{W^2}$ 扩张成全原域旧 $D$ 的双线性。

### 22.3　两方向自己产生第三方向，但更大世界仍可有第四方向

#### 推论 22.6：实际三轴闭合；来源63.1

取上述 $h,k$，令真正原 $j=D(h,k)$。则

$$h^2=k^2=j^2=u,\qquad h\circ k=h\circ j=k\circ j=0,$$

$$D(h,k)=j,\qquad D(h,j)=-k,\qquad D(k,j)=h.$$

故 $U=\operatorname{span}_{\mathbb R}\{h,k,j\}$ 为三维， $D(U,U)\subset U$，且旧 $D$ 在这组有向基中就是三维叉积。

**证明。**

已付自身平面式给 $j^2=u$ 及两份正交，三根方向因而独立。 又 $D(h,j)=J_h^2k=-k$。 反向行给 $J_kh=-j$、$J_k(-j)=-h$，奇性给 $D(k,j)=h$。 $U$ 的每个平方都是实数倍 $u$，故此时才将 定理 22.5 应用于 $U$， 展开三条旧值，取得输出闭合与叉积表。

$\square$

#### 反例 22.7：四维原窗口不闭合；来源64.1

在满足完整静态合同的标准模型中，令

$$E=M_4(\mathbb C)_{\rm sa},\qquad D(a,b)=i[a,b]/2.$$

取

$$\gamma_1=\sigma_x\otimes I_2,\quad \gamma_2=\sigma_y\otimes I_2,\quad \gamma_3=\sigma_z\otimes\sigma_x,\quad \gamma_4=\sigma_z\otimes\sigma_y.$$

四者平方为单位、两两反交换且实线性无关， 所以其四维实张成 $W$ 满足标量平方条件。 但 $D(\gamma_1,\gamma_2)=-\sigma_z\otimes I_2\notin W$， 由 Pauli 张量基独立性即可验证。 因此三轴结论属于一个输入对及其自身响应生成的窗口， 不限制整个原世界或任意 $W$ 的维数。 这些是 Jordan 方向，也不等于三个两两正交的量子比特纯态。

### 22.4　有限奇周期锁定配对单位移位

#### 定理 22.8：移位单位铅笔；新卷2.1

保持定义 22.1–22.2。 对任意整数 $n\ge1$，令 $m=2n+1$、$r=\tan(\pi/(2m))$。 任意原 $h^2=u$、$x\in V_h$ 和实 $s,v$ 满足

$$D\bigl(sh+vu,\ x+r(su+vh)\bigr)=sJ_hx. \tag{22.6}$$

**证明。**

写 $J=J_h$。将原 $(a,b,c)=(rh,sh+vu,x)$ 送入完整 PB。 同轴零行与横向公式给 $\nu=0$、$\omega=r(su+vh)+rJx$。 定义 $H(w)=D(sh+vu,w+r(su+vh))$， 第二槽奇性及 PB 准确给

$$H(x+rJx)+H(-x+rJx)=-2rsx.$$

$x=0$ 用同轴零行。其余在实际自身平面 $L=\operatorname{span}_{\mathbb R}\{x,Jx\}$ 上， $J$ 已线性且 $J^2=-I$，故

$$T=(-I+rJ)(I+rJ)^{-1} =\frac{r^2-1}{1+r^2}I+\frac{2r}{1+r^2}J$$

是一个原实二维矩阵，而非原代数逆元。 对 $w\in L$，上式等于 $H(w)+H(Tw)=-2rs(I+rJ)^{-1}w$。 已知线性函数 $H_0(w)=sJw$ 满足同式， 故 $F=H-H_0$ 满足 $F(Tw)=-F(w)$。 $T$ 的旋转角为 $2\pi n/(2n+1)$，因而 $T^m=I$， 有限次迭代给 $F(w)=(-1)^mF(w)=-F(w)$，所以 $F=0$。 不需要 $H$ 可加或连续，也未对旧 $D$ 取极限。

$\square$

$n=1$ 就是三步周期。 新内容是首槽的 $vu$ 与第二槽的 $rvh$ 成对出现； $v=0$ 属于早已支付的第二槽单位平移。 结论不推广为任意第一槽单位平移， 也不识别一般 $D(Sh,th+b+Lu)$ 或整个 $(\mathbb Ru+W)^2$。 [\[3\]](#ref-pencil24)（定理2.1、第3节）[\[2\]](#ref-radial24)（第65节）

### 22.5　其余真实增量与不能删除的来源

| 固定新增 | 已闭合的关系 | 适用边界 |
|:---|:---|:---|
| 中央响应第53–58节 | 原 $a^2=R\in Z(X)$、$N_{\rm src}(a)<1$ 时，令 $T_ab=D(a,b)$、$H=E\cap Z(X)$。 原模块 $M_{a,b}=Hb+HT_ab$ 满足 $T_a(sb+tT_ab)=sT_ab-tRb$、$T_a^2=-R$； 不必先有非平凡原单位轴。 | 系数 $s,t\in H$ 原有；全局中央性与严格收缩保留。 这是带权模块，不是全域自由复空间。 |
| 原多项式零响应第8–11节 | 在零点仅有标量的原矩阵多项式域， 满秩线性种子 $(tA,tB)$ 的全部通勤演员有限运输分量 恰为整体 $\mathrm{SO}(2)$ 旋转；原独立分块端点可不可达。 | 排除一种运输机制； 标准完整模型的两个端点旧响应仍相等。 没有非可加总 $D$ 反模型。 |
| 原能量纤维第16–17节；有限能量取得第15–16节 | 用第一类叶与原 $\Gamma$ 树，配合保留支撑掩码的终端公式， 精确编译第二类叶 $\phi(b)r$ 及有限混合菜单； 转移有限逆、标量误差和同一事件上的原词系数界。 | 保留原源、全主度量、jet、合法括号、数值及资源服务。 删除一个叶模板不表示更低成本， 词系数不提供隐藏点的特征值。 |
| FIB附录V第230节 | 现有角坐标分成互不相交二进制位池， 产生一列预定硬菜单，精确复现全部有限时序及可数软标签记录律。 | 不是同一静态菜单或隐路径条件同律； 构造的每步菜单差之 $m$ 测度大于 $21/32$，未给趋零运动、 有效有限生成或实际生产者。 |

各行分别保留原源中的全量词与退化支撑。 [\[2\]](#ref-radial24)（第53–58节）[\[4\]](#ref-poly24)（第8–11节） [\[6\]](#ref-energyfiber24)（第16–17节）[\[7\]](#ref-finiteenergy24)（第15–16节） [\[5\]](#ref-fib24)（第230节）

V49 本轮没有正文变化。其既有幂律标定仍要求未归一权重的乘性与有界性； 有限相干回返和粗事件守恒不能替代该正则性， 归一概率落在 $[0,1]$ 也不能替代它。 [\[11\]](#ref-v49q24)（第13.1–13.5节）

**与本轮唯一候选的关系。**

项目新增的双线性是特定 $W$ 上同一个旧 $D$ 的结论； 本轮核心输入 $\mathsf B_1$ 则是原乘法 $m$ 的实双线性。 对象、全称域和前提不同，前者不能用来删除后者。 同样，源 $N_{\rm src}$ 的平方和本轮原 $p^2$ 不是未经标定的同一个量。 本节不把这些条件分支改称第二个量子候选， 也不把几何闭合当作全部实际量子公理已经内生完成。

**完整白话。**

先保留同一张原关系表和已经支付的正性、相加与三元配平。 在平方都由同一个单位读取的一片方向中， 每一对都能用原来的实数长度归一； 把输入对旋到正交，再保留取向认回原基， 旧响应就只剩同一份有向面积。 所有垂直方向能在这张表里相加，才使不同小平面接成同一张双线性面积表。 两根方向自己的响应给出第三根，再作用便返回原两根； 但更大的原世界仍可有第四根，输出可以离开开始选的小片。 三步或其他有限奇周期还能让一种成对移位的额外偏差归零， 却没有自动支付任意移位、全世界的乘法、实际观察程序或物理时间。

<a id="section-23"></a>

## 23　与现有研究的准确比较

本节按所提供的定理比较来源，不给没有统一指标的“最好”排序。 Köplinger–Habeck–Goyal的组成代数路线于2026-04-23发表， 不预先指定二维幅度；它从操作模型及表示选择出发，研究关联组成代数与概率平方律。 其第4.7.1节明确使用连续标量响应，第6.1节保留实标量表示等选择。 本稿不预付原$p$连续性，但预付原实向量结构、双线性乘法及特定忠实比较。 两条路线的输入不同，本文不宣称以更弱条件覆盖其全部结论。[\[50\]](#ref-koplinger26)

| 来源 | 本题直接使用的结构 | 仍需支付的输入 |
|:---|:---|:---|
| Köplinger 等，2026 | 幅度合成与平方读出，组成代数分类的操作入口 | 路径合同、表示与标量选择等；本稿另有不同忠实性输入。 |
| Magnot，2026 | 二元相位比较、三角缺口与Bargmann不变量；已发表于Physics Letters A 591, 131886 | 已有qubit幅度和Gram正性及秩限制；没有零输入量子重建。[\[24\]](#ref-magnot) |
| Sorce，2026 | 一般代数态的规范纯化；本稿使用有限矩阵最小实现作精确例子 | 已给正代数态与相应表示条件。[\[30\]](#ref-sorce23) |
| Watrous | 纯化、Choi/Kraus、Stinespring的有限维表示及最小环境 | 复矩阵正性、完整过程与张量结构。[\[29\]](#ref-watrous) |
| Chiribella 等 | 从操作原理重建有限量子论 | 五项信息条件加纯化，仍有明确输入。[\[51\]](#ref-cdp) |
| Ashtekar–Schilling；Höhn 等 | 射影度量/辛结构及内部钟的关系动力学 | 指定几何、Hamiltonian或约束和钟；面积不单独选择时间。[\[18\]](#ref-ashtekar), [\[38\]](#ref-trinity) |

对本轮原读数的分类，改进指标是严格的模型蕴含： 第23轮只允许$\alpha=1$，本轮允许全部$\alpha>0$并内生计算指数， 同时取得同一规范几何。这个比较不要求对整个文献作首创或强弱总排名。

<a id="section-24"></a>

## 24　完整闭合链、输入计数与白话

### 24.1　本轮唯一候选的结论

$$
\begin{gathered}
\mathsf B_1+\mathsf{LB}+\mathsf G+\mathsf N+\mathsf U+\mathsf F\\
\Downarrow\\
w(t)\text{为同一标量字符},\quad d=w(2)>1,\quad
\alpha=\log_2d>0\\
\Downarrow\\
\ell=p^{1/\alpha}\text{满足完整定标引理}\\
\Downarrow\\
q=\ell^2\text{为原实内积二次型},\quad
T=2L_kP_H,\quad H^\perp=0\\
\Downarrow\\
\mathcal A/N\cong\mathbb H,\quad p=|\cdot|^\alpha,\quad
(\mathcal A/N,J,h)\cong\mathbb C^2\\
\Downarrow\\
S^1\longrightarrow S^3\longrightarrow S^2.
\end{gathered}
$$

这一链没有把原$p$换名为长度；原数值由$p=\ell^\alpha$精确保留。 严格增长保证$\alpha>0$，读数方向不颠倒。 纯“存在”指示、恒等增益和反向增益分别有满足其余条件的反模型。

### 24.2　标准量子关系的来源

| 标准结构 | 数学取得方式 | 实际接口 |
|:---|:---|:---|
| 复幅度与叠加 | 原线性、内生$J$及$h$；有限矩阵完成 | 相干准备与所选幅度表示。 |
| 态与Born概率 | 正归一泛函的唯一迹表示；纯态用$q=p^{2/\alpha}$ | 事件、失败与完整归一读出。 |
| 复合与纠缠 | 同复中心矩阵张量；相关正态 | 实际联合、完整输入及记录。 |
| 一般过程 | 对全部递归二元参考保持正性，推出CP及Kraus | 同一完整箭头及全部参考供应。 |
| 测量与观察者 | 内部等距记录；在无扰动前件下得Lüders | 仪器分支、记录标签与理想性。 |
| 连续演化 | 可逆CPTP群的酉表示及生成元 | 实际钟、$H$和作用量尺度。 |
| 面积与相位 | 反对称乘法、Gram行列式、射影曲率 | 实际路径；端点不足以识别全部门。 |

六组核心条件只选基本幅度块，四组实际量子接口另列。 无限维场、具体相互作用和时空动力学尚未由这六组唯一选出。 有限矩阵不能满足$[X,P]=i\hbar I$且$\hbar\ne0$，因为取迹矛盾。

### 24.3　三种闭合不可混同

1.  **代数闭合：** 同一对生成的三轴窗口对其面积响应闭合。 项目的四维窗口反例允许更大原域；局部三轴不限制整个$\Omega$为三维。

2.  **表示闭合：** 同一锚的Schur余量全零则无需新增维数。 检查可以同时涉及$r+2$个标签，表示维数仍为$r$。

3.  **算法闭合：** 固定有限效果空间能在有限次严格增维后稳定。 实际计算其稳定点还需有效资料、判零或明确误差预算； 一般丢番图存在性不自带统一可计算高度界。

因此，描述三维时使用更多标签、更多公式或一个证明系统， 不能直接改写为更高物理维度。Gödel的不完备条件、Lawvere的表示条件 及Gram增秩条件分别属于不同数学命题。

### 24.4　输入数量的准确表述

本轮仍为六个核心命名组；由精确等式减为严格不等式。 完整原读出模型类严格扩大为全部正幂，但规范几何保持唯一。 数学基础、量子接口及每个条件性来源没有从账本中删除。 定义只引入可消去记号；新限制仍需证明或保留为输入。

### 24.5　本轮一段完整白话

先不用告诉世界“变成两份，读数就必须是两倍”。只要求有一个确实能读出的东西， 它和自己合起来以后，读数会增大。二元合成沿用同一读法，有限大小的输入不能合出 没有上界的读数；再要求同一对比较对任何可读第三元都没有盲方向。 这样，增大多少会自己变成整个结构共用的一个指数。 把这个指数从刻度中分离出来，所有长度、正交、圆与量子相位便使用同一把内生的尺子； 原读数仍能完整还原。两根方向及它们共同产生的第三根可以闭合成一个三轴窗口， 但窗口之外是否还有关系，要看实际加入了什么。用同一组锚比较全部对象， 如果每个新对象都没有剩余方向，而且任意两个新对象之间的旧关系也对得上， 整体就已经拼齐，可以停止。为了核对三维中的关系而同时比较五个标签， 并不等于世界因此增加了两维；真正需要增加的，是旧关系无法容纳的那一份正余量。

## 参考来源

<a id="ref-repo"></a>

\[1\] Trureturing，`dev`分支。 固定主提交[242a5734ea66](https://github.com/the-omega-institute/trureturing/commit/242a5734ea66a228dbf09acad2a72249e2b84c4d)， 2026-11-09 00:03:22（Asia/Singapore）；相对Q23末检69a777d001b1， 1364份理论文件、163977870字节、4新增和5纯追加修改。 完整树身份核对与数学证明地位分开。

<a id="ref-radial24"></a>

\[2\] Trureturing， *中央响应平方与径向一致性* ，本次新增第53–67节，重点定义60.1、定理61.1、62.1、推论63.1和反例64.1；完整旧合同保留。 <https://github.com/the-omega-institute/trureturing/blob/242a5734ea66a228dbf09acad2a72249e2b84c4d/docs/develop/theory/AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md>。

<a id="ref-pencil24"></a>

\[3\] Trureturing， *移位单位铅笔与非中央平方的配对一致* ，本次新增全文，重点定理2.1的有限奇周期；适用载体与配对参数不删。 <https://github.com/the-omega-institute/trureturing/blob/242a5734ea66a228dbf09acad2a72249e2b84c4d/docs/develop/theory/AURIC_SHIFTED_UNIT_PENCILS_AND_NONCENTRAL_REFERENCE_CONSISTENCY.md>。

<a id="ref-poly24"></a>

\[4\] Trureturing， *原多项式零响应与Cayley原域边界* ，本次新增第8–11节；有限运输分量与原独立分块端点边界。 <https://github.com/the-omega-institute/trureturing/blob/242a5734ea66a228dbf09acad2a72249e2b84c4d/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md>。

<a id="ref-fib24"></a>

\[5\] Trureturing， *FIB原子递归全息边界几何续卷III附录V* ，本次新增第230节；既有角坐标的分离数字池与精确记录律。 <https://github.com/the-omega-institute/trureturing/blob/242a5734ea66a228dbf09acad2a72249e2b84c4d/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_V.md>。

<a id="ref-energyfiber24"></a>

\[6\] Trureturing， *原能量纤维几何* ，本次新增第16–17节；保支撑掩码编译与有限逆容差。 <https://github.com/the-omega-institute/trureturing/blob/242a5734ea66a228dbf09acad2a72249e2b84c4d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_ENERGY_FIBRE_GEOMETRY.md>。

<a id="ref-finiteenergy24"></a>

\[7\] Trureturing，  *原有限能量取得*  ，本次新增第15–16节；原词、jet、数值与有限资源供应者的继承合同。 <https://github.com/the-omega-institute/trureturing/blob/242a5734ea66a228dbf09acad2a72249e2b84c4d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_FINITE_ENERGY_ACQUISITION.md>。

<a id="ref-otf724"></a>

\[8\] Trureturing， *OTF-007：观察纤维、最小补全与维度层级* ，本次新增全文；第6节有限未来效果闭合、第10.1节单点Schur余量等按条件使用。 <https://github.com/the-omega-institute/trureturing/blob/242a5734ea66a228dbf09acad2a72249e2b84c4d/docs/develop/theory/OTF_007_OBSERVATION_FIBRES_MINIMAL_COMPLETION_AND_DIMENSIONAL_HIERARCHIES.md>。

<a id="ref-dio24"></a>

\[9\] Trureturing， *丢番图编码、高度界与有效观察者读出* ，本次新增全文；区分存在见证、有效高度界与可执行读出。 <https://github.com/the-omega-institute/trureturing/blob/242a5734ea66a228dbf09acad2a72249e2b84c4d/docs/develop/theory/DIOPHANTINE_ENCODING_HEIGHT_BOUNDS_AND_EFFECTIVE_OBSERVER_READOUT.md>。

<a id="ref-uppmrg224"></a>

\[10\] Trureturing， *UPPM-RG 002：丢番图定义、关系编译与停止边界* ，本次新增全文；强算术输入与条件性结论逐项隔离。 <https://github.com/the-omega-institute/trureturing/blob/242a5734ea66a228dbf09acad2a72249e2b84c4d/docs/develop/theory/UPPM_RG_002_DIOPHANTINE_DEFINITIONS_RELATIONAL_COMPILATION_AND_STOPPING_BOUNDARIES.md>。

<a id="ref-v49q24"></a>

\[11\] Trureturing， *V49：和、乘积、幂、二次关系闭合与归一化提升* ，与前驱blob相同；第13节的原权重有界、幂律与有限平方标定为既有前例。 <https://github.com/the-omega-institute/trureturing/blob/242a5734ea66a228dbf09acad2a72249e2b84c4d/docs/develop/theory/AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md>。

<a id="ref-support24end"></a>

\[12\] Trureturing， *原生支持关联与计数松弛续卷* ， 唯一末检新增第44–47节：定理46.2的统一安装状态区间及SI.302的剩余长链补偿； 固定提交e5f31a9c7a1c4154423d2f2ba8ecf80368bb2ac9，2026-11-09 00:21:55（Asia/Singapore）。 <https://github.com/the-omega-institute/trureturing/blob/e5f31a9c7a1c4154423d2f2ba8ecf80368bb2ac9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SUPPORT_INCIDENCE_AND_COUNT_RELAXATION_CONTINUATION.md>。

<a id="ref-rodriguez"></a>

\[13\] Á. Rodríguez Palacios， *One-sided division absolute valued algebras* ，Publicacions Matemàtiques 36(2B) (1992), 925–954。<https://doi.org/10.5565/PUBLMAT_362B92_12>；作者机构原文目录与摘要 <https://ddd.uab.cat/record/60222>。其单侧除法理论包括内积范数结论与无限维左单位实例。

<a id="ref-conrad_absolutevalues"></a>

\[14\] B. Conrad， *Some basics concerning absolute values* ，Math 248A讲义， 第7节Theorem 7.1：一般赋值域的代数扩张存在绝对值延拓； 其证明使用完成与Theorem 6.4。 <https://math.stanford.edu/~conrad/154Page/handouts/ostrowski.pdf>。

<a id="ref-baez"></a>

\[15\] J. C. Baez， *The Octonions* ，Bull. Amer. Math. Soc. 39 (2002), 145–205。 作者原稿 <https://math.ucr.edu/home/baez/octonions/octonions.pdf>。 合成代数、Clifford 关系、spinor 与射影几何的既有背景；本稿不认领这些一般结构的历史优先权。

<a id="ref-r522"></a>

\[16\] Trureturing， *R5-022：有向面积与三元返回* ，定理 2.2，第 9 节。<https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/AURIC_R5_022_ORIENTED_AREA_AND_TERNARY_RETURN.md>。

<a id="ref-otf5"></a>

\[17\] Trureturing， *OTF-005：轴面几何、相位纤维与内生闭合* ，尤其 C1–C7、§§6、9–10。<https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/OTF_005_AXIS_PLANE_GEOMETRY_PHASE_FIBRES_AND_ENDOGENOUS_CLOSURE.md>。

<a id="ref-ashtekar"></a>

\[18\] A. Ashtekar and T. A. Schilling， *Geometrical Formulation of Quantum Mechanics* ，1997。 <https://arxiv.org/abs/gr-qc/9706069>。

<a id="ref-projector"></a>

\[19\] J. Mitscherling, A. Avdoshkin and J. E. Moore， *Gauge-invariant projector calculus for quantum state geometry and applications to observables in crystals* ，arXiv:2412.03637v2，2025-05-22 版本，§II.6.1。<https://arxiv.org/html/2412.03637v2>。

<a id="ref-berry"></a>

\[20\] M. V. Berry， *Quantal phase factors accompanying adiabatic changes* ，Proc. R. Soc. Lond. A 392 (1984), 45–57。 <https://doi.org/10.1098/rspa.1984.0023>；作者稿 <https://michaelberryphysics.wordpress.com/wp-content/uploads/2013/07/berry120.pdf>。

<a id="ref-ding"></a>

\[21\] Z. Ding, Y. Deng, S.-M. Fei et al.， *Universal conservation laws of the wave-particle-entanglement triad: theory and experiment* ，Light: Science & Applications 14, 82 (2025)，2025-02-12。<https://doi.org/10.1038/s41377-025-01759-4>。

<a id="ref-englert"></a>

\[22\] B.-G. Englert， *Fringe Visibility and Which-Way Information: An Inequality* ，Phys. Rev. Lett. 77 (1996), 2154。 <https://doi.org/10.1103/PhysRevLett.77.2154>。

<a id="ref-siddiqui"></a>

\[23\] M. A. Siddiqui， *Entanglement inference from quantum erasure and path discrimination* ，arXiv:2611.02679v1，2026-11-02 预印本，§§II–IV 及相应补充材料。<https://arxiv.org/abs/2611.02679>；全文 <https://arxiv.org/pdf/2611.02679>。本稿不将预印本标作已同行评审。

<a id="ref-magnot"></a>

\[24\] J.-P. Magnot，  *Remarks on pairwise comparisons, transition amplitudes, and qubit states*  ， Physics Letters A 591, 131886，2026-09-28。 <https://doi.org/10.1016/j.physleta.2026.131886>； 作者稿<https://arxiv.org/abs/2605.04092>。

<a id="ref-r5006"></a>

\[25\] Trureturing， *R5-006：关系角色、反思与对角化* ，第 2–4、8–9 节；直接前驱，本文使用其关系与对角判据。 <https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/AURIC_R5_006_RELATIONAL_ROLES_REFLECTION_AND_DIAGONALIZATION.md>。

<a id="ref-q022-aronszajn"></a>

\[26\] N. Aronszajn.  *Theory of Reproducing Kernels* . Transactions of the American Mathematical Society 68(3) (1950), 337–404. DOI: 10.1090/S0002-9947-1950-0051437-7. Original-paper university mirror: <https://www.mit.edu/~9.520/spring09/Papers/aron.pdf>.

<a id="ref-energy22"></a>

\[27\] Trureturing，  *原有限能量取得*  ，既有第 9–13 节，重点 12.2 的特征空间与信息边界。 <https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_FINITE_ENERGY_ACQUISITION.md>。

<a id="ref-c139cp"></a>

\[28\] Trureturing， *C139: Fixed-source comparators and native event boundary* ，定义 66.1、定理 67.1，第 68、74–85 节。 <https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md>。

<a id="ref-watrous"></a>

\[29\] J. Watrous， *The Theory of Quantum Information* ，Cambridge University Press，2018。 作者开放稿Chapter 2，Theorems 2.10, 2.12, 2.22及Corollary 2.27。 <https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf>。

<a id="ref-sorce23"></a>

\[30\] J. Sorce， *Continuum canonical purifications* ， Journal of High Energy Physics 2026(9), 33，2026-09-02。 <https://doi.org/10.1007/JHEP09(2026)033>；作者稿 <https://arxiv.org/abs/2512.17014v2>，2025-12-22。 第1–2节区分规范与GNS纯化；一般无界情形的弱纯性不等同全部强纯性。

<a id="ref-v42q23"></a>

\[31\] Trureturing， *V42：关系语义、量子三轴与递归相容* ，既有定理2.2、定义11.1、命题11.2；最少新增线性读口与有限未来闭合。 <https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/AURIC_F13_RELATIONAL_SEMANTICS_QUANTUM_THREE_AXES_AND_RECURSIVE_COMPATIBILITY_V42.md>。

<a id="ref-waveprocess"></a>

\[32\] Trureturing， *递归关系观察：波、粒与事件* ，§335 的相干控制实例；§396、§400 对旧 §§336–338 的修订。 <https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md>。

<a id="ref-aberg"></a>

\[33\] J. Åberg， *Gluing of completely positive maps* ，2003 预印本，Propositions 2–3； 与相关研究合并发表于  *Subspace preservation, subspace locality, and gluing of completely positive maps* ， Annals of Physics 313 (2004), 326–367。 <https://doi.org/10.1016/j.aop.2004.04.013>； <https://arxiv.org/html/quant-ph/0302182v2>。

<a id="ref-vanrietvelde"></a>

\[34\] A. Vanrietvelde and G. Chiribella，  *Universal control of quantum processes using sector-preserving channels* ， Quantum Information and Computation 21 (2021), 1320–1352。 <https://doi.org/10.26421/QIC21.15-16-5>； <https://arxiv.org/abs/2106.12463>。

<a id="ref-uppm"></a>

\[35\] Trureturing， *UPPM-RG-001：几何计算中的内生关系与可验证证明* ，定理 4.3、4.6，例 5.3。 <https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/UPPM_RG_001_ENDOGENOUS_RELATIONS_AND_VERIFIABLE_PROOFS_IN_GEOMETRIC_COMPUTATION.md>。

<a id="ref-otf4"></a>

\[36\] Trureturing， *OTF-004：内生观察、注意、控制与余弦反馈* ，第 2、6–7 节。<https://github.com/the-omega-institute/trureturing/blob/c20a31d1caabd516a60f694f1a5799b7ae4e7bf3/docs/develop/theory/OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md>。

<a id="ref-pw"></a>

\[37\] D. N. Page and W. K. Wootters，  *Evolution without evolution: Dynamics described by stationary observables* ，Phys. Rev. D 27 (1983), 2885–2892。 <https://doi.org/10.1103/PhysRevD.27.2885>。

<a id="ref-trinity"></a>

\[38\] P. A. Höhn, A. R. H. Smith and M. P. E. Lock，  *Trinity of relational quantum dynamics* ，Phys. Rev. D 104 (2021), 066001。 <https://arxiv.org/abs/1912.00033>。

<a id="ref-baumann"></a>

\[39\] V. Baumann and M. P. E. Lock， *Time delocalization and causality across temporal quantum reference frames* ，Phys. Rev. D 114, 086005 (2026)，2026-10-05。<https://doi.org/10.1103/9pl6-z9g4>。

<a id="ref-q022-lawvere"></a>

\[40\] F. W. Lawvere.  *Diagonal arguments and cartesian closed categories* . Lecture Notes in Mathematics 92 (1969), 134–145; reprinted with author commentary in Reprints in Theory and Applications of Categories 15 (2006), 1–13. <https://tac.mta.ca/tac/reprints/articles/15/tr15.pdf>. Theorem 1.1.

<a id="ref-q022-paulson"></a>

\[41\] L. C. Paulson. *A Mechanised Proof of Gödel’s Incompleteness Theorems using Nominal Isabelle*. Journal of Automated Reasoning 55 (2015), 1–37. DOI: 10.1007/s10817-015-9322-8. Author-uploaded version: <https://arxiv.org/abs/2104.13792>.

<a id="ref-q022-godel"></a>

\[42\] K. Gödel. *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I*. Monatshefte für Mathematik und Physik 38 (1931), 173–198. DOI: 10.1007/BF01700692. English translation by B. Meltzer: <https://gtts.ehu.es/German/Docencia/2021/MTBYC/pdf/Godel.pdf>. Original Proposition VI and the explicit assumptions following its proof.

<a id="ref-q022-rosser"></a>

\[43\] B. Rosser. *Extensions of some theorems of Gödel and Church*. Journal of Symbolic Logic 1(3) (1936), 87–91. DOI: <https://doi.org/10.2307/2269028>. Publisher extract consulted; it explicitly distinguishes simple from omega consistency.

<a id="ref-q022-tarski-truth"></a>

\[44\] A. Tarski.  *The Semantic Conception of Truth and the Foundations of Semantics* . Philosophy and Phenomenological Research 4(3) (1944), 341–376. Original text: <https://www.jfsowa.com/logic/tarski.htm>. Sections 8–10.

<a id="ref-q022-tarski-decision"></a>

\[45\] A. Tarski.  *A Decision Method for Elementary Algebra and Geometry* , prepared for publication with J. C. C. McKinsey. RAND Report R-109, revised edition, 1951. <https://www.rand.org/pubs/reports/R109.html>.

<a id="ref-q022-marker"></a>

\[46\] D. Marker.  *Model Theory II: Quantifier Elimination* . MSRI introductory lectures, October 14, 2020. Author’s University of Illinois at Chicago notes: <https://homepages.math.uic.edu/~marker/MSRI-2.pdf>. Real closed fields and the o-minimality consequence.

<a id="ref-q022-richardson"></a>

\[47\] D. Richardson.  *Some Undecidable Problems Involving Elementary Functions of a Real Variable* . Journal of Symbolic Logic 33(4) (1968), 514–520. DOI: 10.2307/2271358. Original-paper university mirror: <https://www.math.tecnico.ulisboa.pt/~lgodin/Seminario/richardson.pdf>. Its expression-class assumptions are not silently replaced by the full first-order cosine language.

<a id="ref-glazer13"></a>

\[48\]  *Z is Diophantine in Q* ，公开项目Version 13，标注日期2026-11-07。 <https://github.com/elliotglazer/diophantine-z-q>。 2026-11-09读取当前README：保留原算术论证、系数表检查与未完成主Lean声明的区别。 本稿仅记录来源提出的主张并保留条件接口，不独立认证其算术主定理。

<a id="ref-matiyasevich24"></a>

\[49\] Yu. V. Matiyasevich， *Diophantine representation of enumerable predicates* ， Mathematics of the USSR-Izvestiya 5(1), 1–28，1971。 <https://www.mathnet.ru/eng/im1910>； <https://doi.org/10.1070/IM1971v005n01ABEH001004>。

<a id="ref-koplinger26"></a>

\[50\] J. Köplinger, M. Habeck, P. Goyal，  *Operational Reconstruction of Feynman Rules for Quantum Amplitudes via Composition Algebras* ， International Journal of Theoretical Physics 65, 128，2026-04-23。 <https://doi.org/10.1007/s10773-026-06330-4>； 作者稿v3（2026-04-05）： <https://arxiv.org/html/2508.14822v3>。 本文只比较已明确的表示、连续性与组成代数接口，不宣称审定其全部操作重建。

<a id="ref-cdp"></a>

\[51\] G. Chiribella, G. M. D’Ariano and P. Perinotti，  *Informational derivation of quantum theory* ，Physical Review A 84 (2011), 012311。 <https://doi.org/10.1103/PhysRevA.84.012311>；<https://arxiv.org/abs/1011.6451>。

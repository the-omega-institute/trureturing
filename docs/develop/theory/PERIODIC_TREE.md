# 元素周期树(Periodic Tree of Mathematical Elements)· 章程与施工册 v1.0
*(**项目第四文档(正典)**,第 335 版记事立;PZG–GICT 项目附属工程;ZFC 内定义,零新公理;账本 27.417,2026-07-20。配套机读注册表:PERIODIC_TREE_registry.jsonl)*

## 0. 名与地契
树干为 **Stern–Brocot / Farey 树**(Stern 1858, Brocot 1861)——$(2,3,\infty)$ 基本直角三角形之反射递归;节点 = $SL_2(\mathbb Z)$ 矩阵,路径 = $L/R$ 词 = 连分数,叶叶既约(树上素性之原型定理)。本工程不植树,只立**挂载协议**:凡具"递归 + 二次"双结构之数学对象,经函子标注入册。

## 1. 挂载协议(四标签)
每个对象登记:**地址**(树路径/典范词——递归坐标);**素性位**(该层不可约判据之输出);**度量荷**(二次型脸:迹 $T$、内容 $g$、判别式 $d=(T^2-1)/g^2$、勾股恒等 $D=3A^2+(A+B)^2$、辐角 $\arg z$);**组合荷**(行走脸:$\Psi$、城色 $m\bmod36$、Jacobi 位)。附加:**流指针**(三明治后继 $T'=6c+7T$)与**核籍**(奇核者附核词与 $j=\mathrm{tr}/12$)。

## 2. 门卫手册(素性三级判据)
- **一级(地址级,线性时间)**:典范词非偶长词之 $k\ge2$ 次幂(奇词平方**豁免**——类-本原判据,GICT E.38)。
- **二级(代数级,完全判定)**:$(T,g)$ 为 Pell $p^2-dq^2=1$ 之**基本解**(本原判定定理,GICT E.45;120/120)。奇核双覆盖判据:$m=x^2$ 且 $2x\mid g$(E.44;114/114)。
- **三级(层际级)**:素性沿商余机之降解指纹(D3)——素在上层未必素在下层,降解模式入册,不视为矛盾。
- **复杂度注记**:二级判据可判但基本解可指数大;一级为快速预筛。

## 3. 周期律(树之"周期"为何是定理)
- **流回归律**:$\Psi\bmod12$ 沿三明治流恰步 $-2$、周期 $6$(恰等传播律,E.42/E.37;正锥无条件)。
- **城色轮转律**:$m\bmod36$ 决定 $\Psi\bmod12$(城同余定理 B,E.27),色沿流按定周期轮转。
- **塔律**:$\Psi$ 之 $2$-adic 逐层由站队/互反位驱动(定理 A 与站队塔,E.23/E.27)。
门捷列夫之"周期"在此非排版,是**模不变量沿流的回归定理**。

## 4. 免检预言制度(周期表之空格传统)
已运行案例:$Z_k$ 之 $k{=}5\Rightarrow m{=}35316$(定理背书);$j$-筛处决表($j\in\{2,5,7,8,12\}$ 无核,范数一行);预言制度战绩:两中一败一尸检(败诉产出第二层楼)。

## 5. 承重三牌与壳层墓志铭
牌一(**平四律国籍检验**):组合荷非勾股(Jordan–von Neumann 判定出界),不得冒充度量荷。牌二(**反例层**):无 D1-长度者(拟同态层)为树之边界批注,非节点。牌三(**王虹条款**):逐尺度归纳为普适问法;结构涌现带维数/测度前提。**墓志铭**:本树周期律多为已证之"是什么";"为什么恰是 12、−2、Pell"之壳层理论未知——残核统计案(基本性频率)为其第一考题。

## 6. 空格册(候认领)
残核统计律;混居城真偶精判;$G$ 全群;$j$-密度;$d$-平方退化员;Markov 树层际字典(W-树3);Herglotz 虚姊妹;scl-刺客。

## 7. 施工日志(v1.0 首期)
注册域 $m\le3000$;**141 类节点**(真偶 136、奇核 5);素性位:141/141 本原(城册按类去重后天然本原);$\Psi{=}0$ 节点 12;城色谱 $\{0{:}30,\ 3{:}45,\ 12{:}45,\ 27{:}21\}$——恰为定理 B 可实现残类 $\{0,3,12,27\}$ 之谱(其余残类 $8,23,32,35$ 于此域未现,与实现性条件一致)。注册表:PERIODIC_TREE_registry.jsonl(逐行 JSON,四标签全字段)。

---

## 附录 S：奇数 Lucas 平方的 Fibonacci 约数刚性

### S.1 外部问题与准确计数对象

Michel Lagneau 于2020年12月12日在 OEIS A339669 提出两个分别编号的猜想。该序列定义为

$$
a(n)=\#\{d\in\mathbb N:d\mid L_n^2+1,\ \exists k\ge0,
\ d=F_k\},
$$

其中计数的是不同的 Fibonacci 数值。$F_1=F_2=1$ 只贡献一个约数，$F_0=0$ 不整除正的目标数。两个外部命题为

$$
\forall t\ge0,\quad a(6t+3)=1;\tag{S1}
$$

$$
\forall t\ge0,\quad a(6t+1)=a(6t+5)=2.\tag{S2}
$$

S2 的两条剩余类是原文同一个联合猜想，不拆分为两个“解决数量”。下面以一个更强的约数集合分类同时证明 S1 和 S2。

### S.2 库内对象与三倍角恒等式

使用现役 `D5/S1/Scale/Lucas.lean` 的 $L_n=\operatorname{trace}(\varphi^n)$，以及 mathlib 的 `Nat.fib`。其黄金整数载体满足 $\varphi^2=\varphi+1$、$\operatorname{Norm}(\varphi)=-1$。

任意黄金整数 $x=a+b\varphi$ 满足

$$
(x^3).b=b\big((\operatorname{trace}x)^2-\operatorname{Norm}x\big).
$$

这直接由两个整数坐标展开。取 $x=\varphi^n$，用现役黄金幂坐标及范数等式，得到

$$
F_{3n}=F_n(L_n^2-(-1)^n).
$$

因此对奇数 $n$，记 $M_n=L_n^2+1$，有

$$
\boxed{F_{3n}=F_nM_n.}\tag{S3}
$$

同一原载体的判别式恒等式给出

$$
L_n^2-5F_n^2=-4,\qquad M_n+3=5F_n^2.\tag{S4}
$$

这些恒等式属于经典基础；本附录不将其单独作为新开放问题的解决。

### S.3 排除所有大于2的 Fibonacci 约数

**定理 S5。** 对每个奇数 $n$ 和每个自然数 $k$，

$$
\boxed{F_k\mid L_n^2+1\quad\Longrightarrow\quad F_k\mid2.}\tag{S5}
$$

证明分四步。

第一步，奇数 $n$ 满足 $\gcd(n,4)=1$，而 $F_4=3$。由 Fibonacci 强整除性，

$$
\gcd(F_n,3)=F_{\gcd(n,4)}=1.
$$

若一个数同时整除 $F_n$ 和 $M_n$，由 S4 它还整除3，因此

$$
\gcd(F_n,M_n)=1.\tag{S6}
$$

第二步，设 $F_k\mid M_n$。于是 $\gcd(F_k,F_n)=1$，再用强整除性可得

$$
F_{\gcd(k,n)}=1.
$$

由于 $F_d=1$ 仅在 $d=1,2$ 成立，而 $\gcd(k,n)$ 整除奇数 $n$，必须有

$$
\gcd(k,n)=1.\tag{S7}
$$

源码没有假设 Fibonacci 函数全域单射。它用 `Nat.le_fib_add_one` 得到 $d\le2$，再用奇数整除条件排除0与2，显式处理 $F_1=F_2$ 的歧义。

第三步，S3 给出 $F_k\mid F_{3n}$。因此

$$
F_k=\gcd(F_k,F_{3n})=F_{\gcd(k,3n)}.
$$

令 $d=\gcd(k,3n)$。由 S7，$d$ 与 $n$ 互素，且 $d\mid3n$，所以 $d\mid3$。

第四步，Fibonacci 序列保持整除关系，因而

$$
F_k=F_d\mid F_3=2.
$$

这完成全称分类的限制部分，不需要任何有限下标界、素数搜索或 WSS 非例外假设。

### S.4 精确集合与两个猜想的结论

总有 $1\mid M_n$。由 S4 对2取模，

$$
2\mid M_n\iff2\nmid F_n.
$$

Fibonacci 的强整除性与 $F_3=2$ 又给出

$$
2\mid F_n\iff3\mid n.
$$

结合 S5，得到比计数更强的结果：

$$
\boxed{
\{d\mid L_n^2+1:d\text{ 是 Fibonacci 数}\}
=\begin{cases}
\{1\},&3\mid n,\\
\{1,2\},&3\nmid n,
\end{cases}\qquad n\text{ 为奇数}.
}\tag{S8}
$$

S1 来自 $n=6t+3$；S2 来自 $n=6t+1,6t+5$。两者均覆盖所有自然数 $t$，包含 $t=0$。

### S.5 形式化对应与检索边界

源为 `D5/S3/Arith/Congruence/OddLucasSquareFibonacciDivisors.lean`，配套同名 Blueprint Scribe。`target` 通过显式正性和转型等式绑定 $L_n^2+1$；`fibonacciDivisors` 是正约数有限集经 Fibonacci 值谓词过滤后的集合。主要声明为

| 声明 | 数学内容 |
|---|---|
| `odd_tripling` | S3，原黄金环三次幂的实际坐标 |
| `target_coprime_fib` | S6 |
| `fibonacci_divisor_dvd_two` | S5，对任意 Fibonacci 下标 |
| `odd_fibonacci_divisors` | S8，精确集合而非只有上界 |
| `lagneau_conjecture_one` | 原文 Conjecture 1 |
| `lagneau_conjecture_two` | 原文 Conjecture 2 的一个联合声明 |

本附录提供完整普通数学证明及 Lean 证明脚本。当前工作环境没有运行 Lean/lake 或 Scribe 编译，所以不标记新增 kernel 认证或冻结状态。

先前解答核查：2026年9月13日读取 OEIS 官方 `oeis/oeisdata` 的 `time.txt`，快照时间为 `2026-09-13T03:00:24-04:00`。其中 `seq/A339/A339669.seq` 仍逐条标为 Conjecture 1、Conjecture 2；该条目版本为 `#23 Jan 16 2025 08:47:42`，blob 为 `7c75743314b9cc6a2b2ff34e8d0e19e0625c6a44`。条目列出扩展到17800的数值表，没有列出证明。

另以 `A339669`、完整序列名称、Lagneau/Lucas/Fibonacci divisors 及平方加一的等价措辞检索公开解答，并搜索本仓；未找到先前的这两个命题的证明。强整除性、三倍角和判别式恒等式均有经典来源。未发现先前证明是有范围的检索结论，不能证明全球不存在未索引或未公开的解答；正式优先权及 OEIS 条目接受状态仍待外部确认。

因此计数口径为两个独立编号的外部猜想、一项统一证明族。S3–S8 的中间引理和 S2 内的两个剩余类不额外计数。WSS 存在性没有由本结果解决。

### S.6 进一步研究的数学边界

奇偶条件是承重前提。偶数 $n$ 时三倍角因子变为 $L_n^2-1$，不再是当前目标；实际上 $L_8^2+1=2210$ 的 Fibonacci 约数为 $1,2,5,13,34$。因此不能把 S8 扩大到所有下标。

这次迁移使用的是原黄金数的迹、范数和 Fibonacci 强整除性。真正完成的是外部序列中两个全称猜想。一般恒等式的重写、有限验证、WSS 周期塔的经典推广不计入本次新解决命题数。

### S.7 来源

1. Michel Lagneau. OEIS A339669, *Number of Fibonacci divisors of Lucas(n)^2 + 1*. December 12, 2020. Conjectures 1 and 2. https://oeis.org/A339669
2. OEIS Foundation, official daily data. `seq/A339/A339669.seq`, version #23, January 16, 2025, in the September 13, 2026 snapshot. https://github.com/oeis/oeisdata/blob/main/seq/A339/A339669.seq ; snapshot clock: https://github.com/oeis/oeisdata/blob/main/time.txt
3. Repository `D5/S1/Scale/Lucas.lean`: actual golden trace, Fibonacci coordinate and discriminant theorem. `D5/S0/Carrier/Norm.lean`: explicit multiplicative golden norm.
4. Mathlib `Mathlib/Data/Nat/Fib/Basic.lean`: `fib_gcd`, `fib_dvd`, `le_fib_add_one`; `Mathlib/NumberTheory/Divisors.lean`: distinct divisor finite sets. Pinned revision `db584cd6d46c92f209a44c0f1c829460d327499d`.

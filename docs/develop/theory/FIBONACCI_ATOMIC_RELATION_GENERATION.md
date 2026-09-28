# Fibonacci 原子关系生成理论

> **参考输入。** 本卷是 trureturing 的数学参考输入，不是真源；Lean 内核验证的声明、证明项及其公理闭包才是真源。本卷在当前会话中由用户提供理论文本，Codex（GPT-6）作结构化整理；作者类型记为 `mixed`，会话日期为 2026-09-28。本文新增的统一构造与证明尚未整体编译为 Lean 证明。

## 1. 目标与层次

本理论把“以 Fibonacci 素项为原子”的设想拆成三个层次：原始的自由二叉树结构；由替换关系产生的组成和数量观察；以及在数量半环中定义的乘法素性和可展开封装。自然数、整数、矩阵和素数均属于外部数学描述或解释，不是原始语法的叶子。两个无关系的符号也不会自动产生算术；算术来自明确给出的关系、商和操作。

后文的“完整恢复”总是相对于指定的观察族而言。数量观察恢复组成向量，但忘记树的次序和括号；全部路径观察才恢复原始树。

## 2. 原始语法与结构解释

### definition 2.1 原子与原始语法

取两个不同原子 $\mathsf A=\{\alpha,\beta\}$，令 $\mathcal T$ 为自由二叉树：

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle .
$$

构造 $\langle s,t\rangle$ 是有序且不预设交换律或结合律。因此 $\langle\alpha,\beta\rangle\ne\langle\beta,\alpha\rangle$，且不同括号结构保持不同。

### theorem 2.2 结构解释的唯一延拓

对任意集合 $X$、元素 $a_X,b_X\in X$ 和二元运算 $\mu:X\times X\to X$，存在唯一映射 $\operatorname{Eval}:\mathcal T\to X$ 满足

$$
\operatorname{Eval}(\alpha)=a_X,\qquad
\operatorname{Eval}(\beta)=b_X,\qquad
\operatorname{Eval}(\langle s,t\rangle)=\mu(\operatorname{Eval}(s),\operatorname{Eval}(t)).
$$

**证明。** 按树结构递归给出存在性；对两个满足条件的映射作结构归纳，在两个原子处相同，在二元构造处由归纳假设和 $\mu$ 相同，故唯一。$□$

同一原始树可被解释成数值、语法树、关系档案、程序或图；解释相等不能反推原始结构相等。

## 3. Fibonacci 替换与组成动力学

### definition 3.1 斐波那契替换

定义 $\rho:\mathcal T\to\mathcal T$：

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle .
$$

令 $T_j=\rho^j(\alpha)$，于是 $T_0=\alpha$、$T_1=\beta$、$T_2=\langle\beta,\alpha\rangle$。

### theorem 3.2 结构级 Fibonacci 递归

对所有 $j\ge0$，

$$
T_{j+2}=\langle T_{j+1},T_j\rangle .
$$

**证明。** $j=0$ 时是 $\rho(\beta)=\langle\beta,\alpha\rangle$。若 $T_{j+2}=\langle T_{j+1},T_j\rangle$，则

$$
T_{j+3}=\rho(T_{j+2})=\langle T_{j+2},T_{j+1}\rangle .
$$

结构归纳完成。$□$

### definition 3.3 原子组成观察

定义 $c:\mathcal T\to\mathbb N^2$：

$$
c(\alpha)=(1,0),\quad c(\beta)=(0,1),\quad c(\langle s,t\rangle)=c(s)+c(t).
$$

它保留两类原子数量而忘记次序和括号。记

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

### theorem 3.4 组成观察下的闭合动力学

$$
c(\rho(t))=Mc(t),\qquad M^2=M+I.
$$

**证明。** $\alpha$ 替换为一个 $\beta$，$\beta$ 替换为一个 $\alpha$ 和一个 $\beta$，所以组成向量变为 $(a,b)\mapsto(b,a+b)$；结构归纳给出第一式，矩阵乘法给出第二式。$□$

矩阵特征多项式为 $x^2-x-1$，谱为 $\varphi=(1+\sqrt5)/2$ 与 $-\varphi^{-1}$。黄金比例来自替换关系的谱，而不是预置的几何长度。

## 4. 数量商与自然数半环

### definition 4.1 数量商

令 $\mathcal G=\mathbb Z\alpha\oplus\mathbb Z\beta$ 为有向组成的自由交换群，指定唯一数量关系

$$
\beta+\beta\sim_q\alpha+\alpha+\alpha.
$$

令 $r=3\alpha-2\beta$，并定义 $\mathcal Q=\mathcal G/\mathbb Zr$。这只是选定的观察商，不是原始符号所蕴含的等式。

### theorem 4.2 单位从原子差中出现

在 $\mathcal Q$ 中令 $e=\bar\beta-\bar\alpha$，则

$$
\bar\alpha=2e,\qquad \bar\beta=3e,\qquad \mathcal Q\cong\mathbb Z.
$$

更明确地，

$$
a\alpha+b\beta=(2a+3b)(\beta-\alpha)+(a+b)(3\alpha-2\beta).
$$

**证明。** 由 $2\bar\beta=3\bar\alpha$ 得 $2e=\bar\alpha$、$3e=\bar\beta$。映射 $q(a\alpha+b\beta)=2a+3b$ 消去 $r$，下降为 $\bar q:\mathcal Q\to\mathbb Z$，且 $\bar q(e)=1$；故 $n\mapsto ne$ 与 $\bar q$ 互逆。$□$

### definition 4.3 内部自然数与乘法

令 $\mathcal N$ 为包含 $0$ 且对 $S(x)=x+e$ 封闭的最小子集，并递归定义

$$
x\otimes0=0,\qquad x\otimes S(y)=(x\otimes y)+x.
$$

### theorem 4.4 内部自然数半环

映射 $\eta(n)=ne$ 是从 $\mathbb N$ 到 $\mathcal N$ 的双射，并保持零、后继、加法和 $\otimes$；因此

$$
(\mathcal N,0,e,+,\otimes)\cong(\mathbb N,0,1,+,\times).
$$

**证明。** 生成定义给出满射，定理 4.2 给出单射；加法由 $me+ne=(m+n)e$，乘法对第二变量归纳得到 $(me)\otimes(ne)=(mn)e$。$□$

于是 $e,\bar\alpha,\bar\beta$ 才可分别读作 $1,2,3$。

## 5. 数量商的边界与行为恢复

### theorem 5.1 单个数量读数不承载替换动力学

不存在 $F:\mathbb Z\to\mathbb Z$ 使 $q(Mv)=F(q(v))$ 对所有 $v\in\mathcal G$ 成立。

**证明。** $v=3\alpha$ 与 $w=2\beta$ 都读为 $6$，但 $Mv=3\beta$ 读为 $9$，$Mw=2\alpha+2\beta$ 读为 $10$。同一输入不能有两个输出。$□$

### theorem 5.2 若数量关系在替换下稳定，交换结构塌缩

若交换群中 $S(A)=B$、$S(B)=A+B$ 且 $3A=2B$，则 $A=B=0$。

**证明。** 对 $3A=2B$ 施加 $S$ 得 $3B=2(A+B)$，故 $B=2A$；代回得 $3A=4A$，所以 $A=B=0$。$□$

因此 $3\alpha\sim_q2\beta$ 只能是数量观察的等价，不能同时当作整个替换系统中的原始等式。

### definition 5.3 数量行为

令 $\mathcal B_q(v)=(q(v),q(Mv),q(M^2v),\ldots)$。行为等价要求全部这些数量读数相同。

### theorem 5.4 两次数量读数恰好恢复组成

令 $\mathcal O(v)=(q(v),q(Mv))$。写 $v=a\alpha+b\beta$，并令 $n=q(v)$、$n'=q(Mv)$，则

$$
\binom n{n'}=
\begin{pmatrix}2&3\\3&5\end{pmatrix}\binom ab,
\qquad
a=5n-3n',\quad b=2n'-3n.
$$

因此 $\mathcal O:\mathbb Z^2\to\mathbb Z^2$ 是格同构，且 $\mathcal B_q(v)=\mathcal B_q(w)$ 当且仅当 $v=w$。

**证明。** 观察矩阵行列式为 $1$，逆矩阵为 $\begin{pmatrix}5&-3\\-3&2\end{pmatrix}$。由 $M^2=M+I$，后续读数满足 $q(M^{j+2}v)=q(M^{j+1}v)+q(M^jv)$，故前两项决定全部未来。$□$

数量状态的闭合更新是 $(n,n')\mapsto(n',n+n')$。该恢复只针对组成；例如 $\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$ 的数量行为相同。

### corollary 5.5 有限模数容量

对任意 $m\ge2$，$(q(v)\bmod m,q(Mv)\bmod m)$ 区分全部 $m^2$ 个组成余数状态。保持该更新和全部数量响应的有限表示至少需要 $m^2$ 个状态，两个模坐标达到此界。

**证明。** 上述逆矩阵可直接模 $m$ 使用；若两个不同状态被合并，则其两次读数应相同，违背模 $m$ 可逆性。$□$

## 6. 无损观察权重的完整分类

### definition 6.1 两次观察矩阵

对正整数权重 $u,v$，令 $q_{u,v}(a,b)=ua+vb$，并定义

$$
H_{u,v}=\begin{pmatrix}u&v\\v&u+v\end{pmatrix},
\qquad \Delta(u,v)=u^2+uv-v^2.
$$

称读出为整数无损的，若 $H_{u,v}$ 是 $\mathbb Z^2$ 的自同构。

### theorem 6.2 无损条件

$$
H_{u,v}\in\operatorname{GL}_2(\mathbb Z)\iff|\Delta(u,v)|=1.
$$

固定模数 $m$ 时，模 $m$ 无损当且仅当 $\gcd(\Delta(u,v),m)=1$。

**证明。** 整数矩阵可逆当且仅当行列式为 $\pm1$；模 $m$ 时由伴随矩阵公式，可逆当且仅当行列式在 $\mathbb Z/m\mathbb Z$ 中可逆。$□$

### theorem 6.3 正权重分类

对正整数 $u,v$，

$$
|u^2+uv-v^2|=1
\iff (u,v)=(F_j,F_{j+1})\quad(j\ge1).
$$

**证明。** $(1,1)$ 满足条件，且变换 $(u,v)\mapsto(v,u+v)$ 使 $\Delta$ 变号，产生全部相邻 Fibonacci 对。反向地，若 $u>v$ 则 $\Delta=u^2+v(u-v)>1$；若 $u=v$ 只有 $(1,1)$；若 $u=1<v$ 直接解得 $v=2$。其余情形 $u\ge2,v>u$ 必有 $u<v<2u$，下降变换 $(u,v)\mapsto(v-u,u)$ 保持正性、严格降低最大坐标并使 $\Delta$ 变号，最终到达 $(1,1)$ 或 $(1,2)$。反向过程正是 Fibonacci 更新。$□$

### corollary 6.4 素数种子

若 $u,v$ 都为素数且两次读出整数无损，则

$$
(u,v)=(2,3)\quad\text{或}\quad(3,5).
$$

**证明。** 定理 6.3 先给出相邻 Fibonacci 对。利用 $d\mid n\Rightarrow F_d\mid F_n$，若 $F_n$ 为素数，则 $n$ 必为素数或 $n=4$（$n=4$ 是唯一因子 $2$ 只给出 $F_2=1$ 的例外）。若相邻下标 $n,n+1$ 都大于 $3$，其中一个被 $3$ 整除且严格大于 $3$，不可能是素数下标；相应 Fibonacci 项因整除性质而合成。因此只剩下 $n=3$ 与下标 $4$ 的例外，得到 $(F_3,F_4)=(2,3)$ 和 $(F_4,F_5)=(3,5)$。$□$

再以数值最小为选择规则，唯一种子是 $(2,3)$；$(3,5)$ 是其一步后读数。该唯一性只在固定 Fibonacci 替换和两次完整恢复条件下成立。

### proposition 6.5 跳过中间项会产生模盲点

权重 $(5,13)$ 虽由两个 Fibonacci 素数构成，但 $\Delta(5,13)=-79$。取 $z=(-13,5)$，则 $q_{5,13}(z)=0$ 且 $q_{5,13}(Mz)=-79\equiv0\pmod{79}$；由递推，所有后续读数也模 $79$ 为零。因此两项为素数不足以保证删去中间关系后的观察无损。

## 7. $k$-bonacci 推广

### definition 7.1 $k$ 原子替换

取 $k$ 个原子 $\alpha_0,\ldots,\alpha_{k-1}$，在 $\mathbb Z^k$ 上令

$$
C_ke_i=e_{i+1}\ (0\le i<k-1),\qquad C_ke_{k-1}=\sum_{i=0}^{k-1}e_i.
$$

原始语法中用固定顺序和括号把最后一式接成 $k$ 个子结构，于是

$$
C_k^k=C_k^{k-1}+\cdots+C_k+I.
$$

令 $q_k(e_i)=2^i$，并记由这些初始位权和递推得到的序列为 $G_i^{(k)}$。

### theorem 7.2 连续 $k$ 次读数无损恢复

令

$$
\mathcal O_k(z)=(q_k(z),q_k(C_kz),\ldots,q_k(C_k^{k-1}z)).
$$

其矩阵 $H_k=(G_{i+j}^{(k)})_{0\le i,j<k}$ 满足

$$
\det H_k=(-1)^{k(k-1)/2}.
$$

因此 $\mathcal O_k$ 是整数格同构，模任意 $m\ge2$ 后仍可逆。

**证明。** 对列 $j=k-1,\ldots,1$ 作 $\operatorname{Col}_j\leftarrow\operatorname{Col}_j-2\operatorname{Col}_{j-1}$。第一行变成 $(1,0,\ldots,0)$；余下子矩阵在反对角线一侧为零，反对角线为 $-1$。反转列顺序后为三角矩阵，计算符号得所示行列式。$□$

所以 $k$ 类原子组成与 $k$ 次连续数量响应相互可恢复；初始权重是否为素数是另一层问题。

## 8. 数量素性与 Fib 素原子封装

### definition 8.1 数量层的乘法原子

在 $\mathcal N$ 中定义 $\operatorname{Prime}_{\mathcal N}(p)$：$p\ne0,e$，且 $p=x\otimes y$ 时 $x=e$ 或 $y=e$。由定理 4.4，这等价于普通自然数素性。

### theorem 8.2 生成轨道的数量读数

对 $T_j=\rho^j(\alpha)$，

$$
q(c(T_j))=F_{j+3}.
$$

**证明。** 初始读数为 $2,3$；定理 3.2 和数量加性给出 Fibonacci 递推。$□$

### definition 8.3 经认证的 Fib 素原子

当已有 $\operatorname{Prime}_{\mathcal N}(q(c(T_j)))$ 证明时，注册 $T_j$ 为 Fib 素原子并定义封装名 $\mathsf P_j=\operatorname{Pack}(T_j)$，保存

$$
\operatorname{Expand}(\mathsf P_j)=T_j.
$$

例如 $T_2$ 的读数为 $5$，$T_4$ 的读数为 $13$，二者都可作为更高层接口。乘法不可分不妨碍其 Fibonacci 结构可展开。

### theorem 8.4 保结构封装的行为运输

设扩展码集 $\mathcal C$ 允许原始原子、二元节点和封装名，且有 $\operatorname{Expand}:\mathcal C\to\mathcal T$ 与表示映射 $s:\mathcal T\to\mathcal C$ 满足 $\operatorname{Expand}\circ s=\operatorname{id}_{\mathcal T}$。定义

$$
\widehat\rho=s\circ\rho\circ\operatorname{Expand}.
$$

则对所有 $j\ge0$，

$$
\operatorname{Expand}(\widehat\rho^j(c))=\rho^j(\operatorname{Expand}(c)).
$$

**证明。** $\operatorname{Expand}\circ\widehat\rho=\rho\circ\operatorname{Expand}$，对 $j$ 归纳。$□$

封装必须保留原结构或足够行为信息；仅凭当前数值相等不能把 $3\alpha$ 与 $2\beta$ 合并。

## 9. 不预置自然数的结构编码

### definition 9.1 原子字母上的序列化

定义

$$
\operatorname{code}(\alpha)=\alpha\alpha,\qquad
\operatorname{code}(\beta)=\alpha\beta,\qquad
\operatorname{code}(\langle s,t\rangle)=\beta\,\operatorname{code}(s)\,\operatorname{code}(t).
$$

这里没有先把对象转换成整数。

### theorem 9.2 唯一解析与前缀自由

上述编码是单射、码集前缀自由，并存在递归解码器满足 $\operatorname{decode}(\operatorname{code}(t))=t$。

**证明。** 首字母为 $\alpha$ 时再读一个字母即可识别原子；首字母为 $\beta$ 时递归读取两个完整子码即可识别二元节点。结构归纳给出唯一解析和恰在末尾停止；完整码不可能成为另一完整码的真前缀。$□$

该语法可逐层描述树、列表、有序对表、有限关系和带名字的有限图。环需用显式引用表示，不能把环当成已完全展开的有限树。既有 `HFEncoding` 与 `FiniteGraphEncoding` 可作为元数学目标表示，但它们不消除基础元理论。

### theorem 9.3 全部路径读数恢复原始树

给每条有限左/右路径读取终点是 $\alpha$、$\beta$、分支或不存在。若两棵树的全部路径读数相同，则两树相等。

**证明。** 比较空路径根标签；若为原子即相同，若为分支则分别比较左、右前缀路径并用结构归纳恢复两个子树。$□$

所以全部路径读数恢复原始结构，而数量的全部未来读数只恢复组成。

## 10. 可选执行层

### definition 10.1 组合操作结构码

令 $\mathsf K=\langle\alpha,\alpha\rangle$、$\mathsf S=\langle\alpha,\beta\rangle$、$\operatorname{App}(x,y)=\langle\beta,\langle x,y\rangle\rangle$，并额外声明归约规则

$$
\mathsf Kxy\to x,\qquad \mathsf Sxyz\to xz(yz).
$$

这些是额外的执行语义，不是 Fibonacci 递推自动推出的规则。

### theorem 10.2 函数抽象的有限树编译

令 $\mathsf I=\mathsf S\mathsf K\mathsf K$，对含变量 $x$ 的应用表达式递归定义

$$
[x]x=\mathsf I,\qquad [x]t=\mathsf Kt\ (x\text{ 不在 }t\text{ 中自由出现}),\qquad [x](uv)=\mathsf S([x]u)([x]v).
$$

则 $([x]t)a\to^*t[x:=a]$。

**证明。** 变量情形由 $\mathsf I a\to a$；无自由变量情形由 $\mathsf Kt\,a\to t$；应用情形由 $\mathsf S$ 规则和归纳假设。$□$

因此闭合函数表达式可编译为有限原子树。递归可通过不动点表达式编译，但不保证每个程序终止，也不把任意无限对象变成有限可计算对象。

## 11. 总结性结论与边界

### theorem 11.1 Fibonacci 原子关系模型

上述定义组合出如下链条：

$$
\text{原始原子树}\xrightarrow{\rho}\text{原始原子树}
\quad\leadsto\quad
\mathbb Z^2\xrightarrow{M}\mathbb Z^2,
\ M^2=M+I,
$$

$$
\mathbb Z^2/\langle3\alpha-2\beta\rangle\cong\mathbb Z,
$$

当前和下一次数量读数恢复组成；正权重无整除损失恰好给出相邻 Fibonacci 权重；两个权重都为素数时只有 $(2,3)$、$(3,5)$，最小选择为 $(2,3)$；已证明为素数的轨道读数可以封装成更高层原子而保持展开后的响应；同一原始语法可以编码有限关系结构，并在另加组合规则后承载函数和递归程序。

**证明。** 由定理 2.2、3.2、3.4、4.2、4.4、5.1、5.4、6.2、6.3、推论 6.4、定理 8.4、9.2、9.3 和 10.2 逐项组合。$□$

### proposition 11.2 结论范围

本文没有声称：数量商保持全部原始递归；单个数量值能恢复括号和次序；任意两个素数权重都无损；存在无穷多个 Fibonacci 素数；有限核验替代无限证明；或 Fibonacci 替换单独产生通用计算。数量商只是一个观察接口，素原子封装必须保留可展开来源或足够行为信息。

## 12. 核验状态与项目接口

本文所述统一构造和证明尚未整体 Lean 内核验证。来源文本报告了以下有限精确核验：至多六叶的 3,238 棵原子树编解码及替换检查、6,561 组整数坐标恢复、正权重不超过 1000 的单位范数分类、224 组模数可逆性检查，以及二阶至十二阶观察矩阵行列式检查。该报告只支持相应有限样本和实现例子，不替代全称证明，也不改变本卷的参考输入状态。

可复用的项目接口包括 `SourceTreeEncoding`、`ControlledBehaviorUniversality`、`PrimeAxisEncoding`、`HFEncoding` 和 `FiniteGraphEncoding`。真正的形式化交付仍须先在消化账本中定位 atom，再依 §3.2 的准入规则判断是否存在新的逃逸内容；本卷本身不执行该流程。

## 追加锚（本行以下为增补区）

## 13. 与递归时空全息几何的关系

本节把本卷的 Fibonacci 结构接到仓内已有的“动态充分边界”和“算术全息 RT”语言。这里的“体”“边界”“径向层”是一个有限关系模型中的角色名；它们不自动成为物理时空、引力体或 AdS/CFT 对偶。仓内 `RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md` 的动态充分边界判据，以及 `ARITHMETIC_HOLOGRAPHIC_RT.md` 对有限网络与物理 RT 的分界，都是本节的边界条件。

### definition 13.1 组成体与两层边界读数

把组成向量 $z=(a,b)^{\mathsf T}\in\mathbb Z^2$ 看作一个二通道体状态，体更新为

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

对权重 $(u,v)$，定义两层边界读数

$$
\partial_{u,v}(z)=H_{u,v}z,
\qquad
H_{u,v}=\begin{pmatrix}u&v\\v&u+v\end{pmatrix}.
$$

第一行是当前数量，第二行是一次替换后的数量。对本卷最小素数种子 $(u,v)=(2,3)$，记 $H=H_{2,3}$。

### theorem 13.2 体更新与边界更新严格交织

令

$$
U=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

对所有整数权重 $u,v$ 和组成状态 $z$，有

$$
H_{u,v}M=UH_{u,v},
\qquad
\partial_{u,v}(Mz)=U\partial_{u,v}(z).
$$

因此边界状态 $(n,n')$ 的递归更新恒为

$$
(n,n')\longmapsto(n',n+n').
$$

**证明。** 直接计算

$$
H_{u,v}M
=\begin{pmatrix}v&u+v\\u+v&u+2v\end{pmatrix}
=U H_{u,v}.
$$

第二式由第一式作用于 $z$ 得到。$□$

这正是一个离散的边界—体交织关系：体先更新再读数，与先读当前和下一层再在边界上更新，结果相同。它比“边界数值看起来服从 Fibonacci”更强，因为它给出一个逐态的交换方块。

### corollary 13.3 最小素数种子给出精确有限全息码

对 $H=H_{2,3}$，

$$
\det H=1,
$$

且

$$
H^{-1}=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}.
$$

所以两层边界读数与组成体状态之间是整数格同构；边界递归保存全部未来数量行为，并可在每一步恢复 $(a,b)$。

**证明。** 行列式和逆矩阵直接计算；由定理 13.2，未来边界读数由 $U$ 迭代生成。$□$

这给出一个严格的有限模型：在“只关心两类原子组成及其 Fibonacci 未来响应”的任务商上，边界两寄存器不是近似摘要，而是无损编码。它不恢复原始树的括号和次序，因为这些信息已被 $c$ 的观察商丢弃。

### theorem 13.4 一寄存器边界不可能完成组成重建

任何单个整数线性读数

$$
\ell(a,b)=ua+vb
$$

都不能在整个 $\mathbb Z^2$ 上单射；在非负组成上也不能单射。因而要恢复全部组成，至少需要两个独立的边界读数。两层读数 $\partial_{2,3}$ 达到这一下界。

**证明。** 在 $\mathbb Z^2$ 上，非零向量 $(v,-u)$ 位于 $\ell$ 的核。即使限制到 $\mathbb N^2$，两个不同点 $(v,0)$ 与 $(0,u)$ 都读为 $uv$（对 $u,v>0$）；若某个权重为零则更直接。定理 13.2 和推论 13.3 给出两个读数的可逆实现。$□$

### proposition 13.5 算术亏损对应有限指标，而不是自动的熵亏损

对一般正权重 $(u,v)$，边界像是子格

$$
H_{u,v}(\mathbb Z^2)\subseteq\mathbb Z^2
$$

其指标为 $|\Delta(u,v)|$，其中 $\Delta=u^2+uv-v^2$。当 $|\Delta|>1$ 时，从任意整数边界对反解体状态需要整除相容条件；模 $m$ 时若 $\gcd(\Delta,m)>1$，存在非零组成方向在两层读数中不可见。

**证明。** 整数矩阵像的指标等于行列式绝对值；模 $m$ 的核非平凡当且仅当行列式不是单位。$□$

因此“非 Fibonacci 权重造成的损失”首先是格的算术损失。只有在另行指定概率态、量子态或熵函数后，才可以把它转译为信息熵或纠缠熵；不能把行列式大于一直接称为 RT 熵亏损。

### definition 13.6 径向层与观察边界

把 $T_j=\rho^j(\alpha)$ 的迭代次数 $j$ 作为离散径向层。层 $j$ 的组成体为 $c(T_j)$，边界读数为

$$
\partial_{2,3}(c(T_j))=(F_{j+3},F_{j+4}).
$$

层更新与边界更新形成

$$
\partial_{2,3}(c(T_{j+1}))
=U\partial_{2,3}(c(T_j)).
$$

这是一种关系定义的“径向演化”，不是预先给定的距离函数或 Lorentz 度规。

### theorem 13.7 有限行为边界在两步处稳定于组成商

在状态空间 $\mathbb Z^2$、更新 $M$ 和数量读数 $q_{2,3}$ 上，长度一的观察核可能包含不同组成状态；长度二的观察核为零关系：

$$
\ker\bigl(z\mapsto(q(z),q(Mz))\bigr)=\{0\}.
$$

因而在组成商上，有限未来观察的核链在两层处稳定；完整无限未来观察不会进一步细化该商。

**证明。** 长度二的观察矩阵是 $H_{2,3}$，由推论 13.3 可逆，故核为零。长度更长的观察包含前两项，核只能继续保持为零；由 $M^2=M+I$，后续坐标是前两项的 Fibonacci 线性组合。$□$

这与仓内 `FiniteHorizonKernelRecurrence` 的一般结论相符：观察视界逐层细化，完整核是有限核的交。这里的“稳定”只针对组成商；若把原始树、路径或语法操作加入任务，稳定深度必须重新计算。

### proposition 13.8 一个有限容量的边界计数律

把每个边界寄存器限制为 $m$ 个符号，并要求恢复所有模 $m$ 的组成状态。则边界至少需要 $m^2$ 个联合状态，也就是至少两个 $m$ 元寄存器；两次读数

$$
(q(z)\bmod m,q(Mz)\bmod m)
$$

恰好达到该容量。

**证明。** 模 $m$ 的组成状态有 $m^2$ 个。可恢复编码必须单射，故联合边界状态数至少为 $m^2$；推论 5.5 给出两个寄存器的双射实现。$□$

这个计数律可以作为有限模型中的“边界容量”基准，但它不是面积律：没有定义连续面积、引力常数、量子纠缠或 RT 最小曲面。

### 14. 全息几何解释的可用部分与未证桥梁

在当前模型中，可以严格保留以下对应：

1. **体状态**：原始树的组成商 $\mathbb Z^2$，或更丰富的树状态 $\mathcal T$；
2. **径向递归**：$\rho$ 或组成层的 $M$；
3. **边界读数**：$q$ 及其未来读数，尤其是两层交织映射 $H_{2,3}$；
4. **边界重建**：在组成任务上由整数逆矩阵完成，在完整树任务上必须增加路径读数；
5. **粗化损失**：$|\Delta|>1$ 的有限指标或模核，表示观察分辨率不足。

仍未由本理论推出的内容包括：

- 从 $M$ 或 $\rho$ 构造满足因果性、局部性和曲率条件的时空度规；
- 把边界寄存器的对数容量识别为纠缠熵；
- 证明某个连续几何的最小割等于量子态的约化熵；
- 给出共同跨尺度态、量子纠错码和物理边界理论；
- 将 Fibonacci 层与真实时间或真实径向距离一一对应。

因此，本卷与 `ARITHMETIC_HOLOGRAPHIC_RT.md` 的关系是：本卷提供一个可逆的 Fibonacci 边界—体递归模块，可作为有限算术网络中的局部编码块；该模块本身不完成物理 RT 或 AdS/CFT 证明。若要继续到 2027 年，最短的可检验路线是先在 Lean 中形式化 $H_{u,v}M=UH_{u,v}$、$|\Delta|=1$ 的恢复判据和有限行为核稳定，再单独提出带有态、熵和几何割的桥接命题。

## 追加锚（本行以下为增补区）

## 15. 黄金整数操作代数、共轭与素性回返

本批把上一节的 Fibonacci 体—边界模块进一步接到仓内已经存在的黄金整数载体。可核对的代码入口是 `D5/S0/Carrier/Ring.lean`、`D5/S0/Carrier/Conj.lean`、`D5/S0/Carrier/Norm.lean`、`D5/S1/Scale/Fibonacci.lean`、`D5/S3/Arith/GoldenApparition.lean`、`D5/S3/Arith/FibonacciRank.lean`、`D5/S3/Arith/GoldenPrimeSplitting.lean` 和 `D5/S3/PrimeForms/GoldenPrimeClassification.lean`。本批仍是理论桥接；新增组合尚未整体编译为一个 Lean 模块。

### definition 15.1 递归相容的线性操作

在组成群 $V=\mathbb Z\alpha\oplus\mathbb Z\beta\cong\mathbb Z^2$ 上，令 $M=\begin{pmatrix}0&1\\1&1\end{pmatrix}$。称整数线性操作 $A:V\to V$ 与递归相容，若

$$
AM=MA.
$$

记相容操作环为

$$
\mathscr A_M=\{A\in\operatorname{Mat}_2(\mathbb Z):AM=MA\}.
$$

### theorem 15.2 相容操作环就是黄金整数环

$$
\mathscr A_M=\{aI+bM:a,b\in\mathbb Z\},
$$

并且

$$
\mathscr A_M\cong\mathbb Z[\theta]/(\theta^2-\theta-1).
$$

在坐标 $(a,b)$ 下，乘法为

$$
(a,b)(c,d)=(ac+bd,\ ad+bc+bd),
$$

与仓内 `GoldenInt` 的乘法逐项一致。

**证明。** 写 $A=\begin{pmatrix}r&s\\t&u\end{pmatrix}$。比较 $AM$ 与 $MA$ 得 $t=s$、$u=r+s$，所以 $A=rI+sM$；反向显然。由于 $M^2=M+I$，复合乘法正是 $\theta^2=\theta+1$ 的商环乘法。$□$

这里 $I$ 是相容操作的单位，$M$ 是递归生成元。原子在数量接口中读成 $2,3$，与操作环中的单位和生成元属于不同解释层，二者不冲突。

### definition 15.3 观察元素

令 $R=\mathbb Z[\theta]/(\theta^2-\theta-1)$，并以

$$
\varepsilon(a+b\theta)=b
$$

为基本系数观察。对任意整数权重 $u,v$，令 $q_{u,v}(a+b\theta)=ua+vb$。

### theorem 15.4 每个线性观察都由黄金整数作用产生

存在唯一

$$
 h=(v-u)+u\theta\in R
$$

使

$$
q_{u,v}(x)=\varepsilon(hx)\qquad(x\in R).
$$

**证明。** 若 $h=c+d\theta$，则

$$
\varepsilon(h(a+b\theta))=da+(c+d)b.
$$

比较系数得 $d=u$、$c=v-u$，且唯一。$□$

### definition 15.5 共轭与范数

定义

$$
\theta^*=1-\theta,qquad
(a+b\theta)^*=(a+b)-b\theta,
$$

以及

$$
\mathcal N(a+b\theta)=a^2+ab-b^2.
$$

这分别对应仓内 `conj` 和 `norm`；已有源码证明共轭是对合环自同构，且 $\mathcal N(xy)=\mathcal N(x)\mathcal N(y)$。

### theorem 15.6 完整两层观察等价于范数单位

令

$$
\mathcal O_{u,v}(x)=(q_{u,v}(x),q_{u,v}(\theta x)).
$$

其矩阵是 $H_{u,v}$，并满足

$$
\det H_{u,v}=u^2+uv-v^2=-\mathcal N((v-u)+u\theta).
$$

因此

$$
\mathcal O_{u,v}\in\operatorname{GL}_2(\mathbb Z)
\iff
\mathcal N((v-u)+u\theta)=\pm1.
$$

模 $m$ 时可逆当且仅当 $\gcd(\mathcal N(h),m)=1$。

**证明。** 直接展开行列式与范数；整数和模 $m$ 的可逆性分别由行列式判据给出。$□$

### corollary 15.7 相邻 Fibonacci 权重是同一观察的时间平移

对 $j\ge1$，

$$
\theta^j=F_{j-1}+F_j\theta,
$$

从而

$$
\varepsilon(\theta^j x)=F_j a+F_{j+1}b.
$$

特别地，$q_{2,3}(x)=\varepsilon(\theta^3x)$，因为 $\theta^3=1+2\theta$。每个 $\theta^j$ 的范数为 $(-1)^j$，所以这条连续观察链的每一项都给出整数格上的无损两层接口。

### theorem 15.8 数量核隐藏的是一个可逆方向

令 $q=q_{2,3}$，则

$$
\ker q=\mathbb Z(3-2\theta),
$$

且

$$
(3-2\theta)(-1-2\theta)=1.
$$

因此

$$
R/\mathbb Z(3-2\theta)\cong\mathbb Z
$$

作为加法群，但环理想商 $R/(3-2\theta)$ 为零环。

**证明。** $2a+3b=0$ 的整数解为 $(a,b)=(3t,-2t)$；乘法恒等式由 $\theta^2=\theta+1$ 直接展开。由于核生成元是单位，理想商含有 $1$；而加法子群商仍由一个原始向量的商得到 $\mathbb Z$。$□$

这精确解释了数量读数的边界：它是有效的观察商，但不是保留全部递归操作的环商。要在压缩上继续执行，必须增加下一次读数或等价的行为方向。

### theorem 15.9 共轭给出带符号的逆递归

有

$$
\theta^*=1-\theta=-\theta^{-1},
$$

并且对任意整数 $j$，

$$
(\theta^j x)^*=(-1)^j\theta^{-j}x^*.
$$

**证明。** $\theta(\theta-1)=1$，故 $1-\theta=-\theta^{-1}$；共轭保持乘法，逐次取幂即得。$□$

因此向前 Fibonacci 递归和反向递归加交替符号是代数共轭关系。逆步存在于带符号的黄金整数中，不等于原始正叶子控制器自动拥有物理逆操作。

### proposition 15.10 递归单位与数量素性分离

$\theta^j$ 全部是黄金整数环的单位，因为 $\mathcal N(\theta^j)=(-1)^j$；但其数量读数可以是素数或合数，例如

$$
q(\theta^4)=13,\quad q(\theta^5)=21,\quad q(\theta^8)=89,\quad q(\theta^{16})=4181=37\cdot113.
$$

所以“递归操作可逆”与“数量读数是乘法素数”是两种独立性质。Fib 素原子必须同时保留递归来源、数量读数和素性证明，不能以环单位性代替素性。

### theorem 15.11 Fibonacci 整除是模观察中的标量回返

对 $m\ge1$，

$$
\theta^m=F_{m-1}+F_m\theta.
$$

因此对 $d\ge2$，

$$
 d\mid F_m
\iff
\theta^m\bmod dR\text{ 属于标量子环},
$$

等价地

$$
 d\mid F_m
\iff
M^m\equiv\lambda I\pmod d
\quad\text{对某个 }\lambda.
$$

**证明。** 幂公式按 $\theta^2=\theta+1$ 归纳；商环中表示 $a+b\theta$ 的系数唯一，所以标量性等价于 $F_m\equiv0\pmod d$。矩阵表述使用 $M^m$ 的 Fibonacci 坐标公式。$□$

### definition 15.12 素数通道的标量回返

对素数 $p$，令

$$
 r(p)=\min\{m\ge1:\theta^m\bmod pR\text{ 为标量}\}.
$$

这是模观察中的首次方向回返。它组织的是素因子通道，而非只组织那些自身为 Fibonacci 素数的项。

### theorem 15.13 黄金 Frobenius 给出回返上界

设 $p$ 为奇素数且 $p\ne5$，令 $\chi=(5/p)\in\{1,-1\}$。则

$$
\theta^{p-\chi}=\chi\pmod {pR},
\qquad r(p)\mid p-\chi.
$$

**证明。** 令 $\delta=2\theta-1$，则 $\delta^2=5$。Frobenius 给出 $\delta^p=\chi\delta$。于是 $\theta^p=\theta$（$\chi=1$）或 $\theta^p=1-\theta=\theta^*$（$\chi=-1$）；第二种再乘以 $\theta$ 得 $\theta^{p+1}=-1$。这些都是标量回返，故首次回返指数整除相应指数。$□$

仓内 `GoldenApparition` 与 `FibonacciRank` 已形式化相同的 $p-\chi$ / $p+\chi$ 型 Fibonacci 零点界；本节的黄金整数表述仍需单独建立与这些声明的精确桥接。

### proposition 15.14 模五是分歧观察，而非普通素数通道

令 $\delta=2\theta-1$。模 $5$ 有 $\delta^2=0$，且

$$
R/5R\cong\mathbb F_5[\varepsilon]/(\varepsilon^2),
\qquad \theta=3+\varepsilon.
$$

故任意多项式满足

$$
P(3+\varepsilon)=P(3)+P'(3)\varepsilon.
$$

这说明模五观察自然保留“值加一阶变化”两类信息；仓内 `GoldenPrimeSplitting` 与 `GoldenPrimeClassification` 已证明五的分歧平方和非分裂素数的模五分类。其状态机的最小状态数仍是另一项带读取合同的证明义务。

### definition 15.15 有来源的 Fib 素原子

一个经认证的 Fib 素原子记录为

$$
\mathsf P=(T_j,q,n,\Pi),
$$

其中 $n=q(c(T_j))=F_{j+3}$，而 $\Pi$ 是对 $\operatorname{Prime}(n)$ 的可核验有限证明。封装保存 $\operatorname{Expand}(\mathsf P)=T_j$，并要求展开后行为与原递归接口相容。

素性证明可以引用一般的乘法证书子图；证书中的辅助素数不必成为底层原子字母。因而基础语法由递归构造提供，素原子注册由数量接口和证明规则决定。

## 16. 本批结论与未决桥梁

本批把三条链放进同一载体：

$$
\text{递归相容操作}
\longrightarrow
\mathbb Z[\theta]
\longrightarrow
\text{共轭与范数}
\longrightarrow
\text{无损观察与模回返}
\longrightarrow
\text{带来源的素性封装}.
$$

可以直接从当前源码支持的部分保留：`GoldenInt` 的乘法正是相容操作环的坐标乘法；`conj` 和 `norm` 提供观察反向与范数判据；Fibonacci/黄金 Frobenius 模块提供素数通道的回返边界。仍需单独形式化的桥梁是：相容操作环与 `GoldenInt` 的环同构、观察元素表示、$H_{u,v}M=UH_{u,v}$ 的 Lean 版本、素性证书对象及其与 `PrimeAxisEncoding` 的接口。

这些桥梁完成前，不能把“已经有黄金整数源码”报告为“本理论已被 Lean 验证”；它只能说明本理论有一个现成、可核对的候选代数载体。

本批独立精确核验覆盖了 $-20\le r,s\le20$ 的相容矩阵（所有 91 个有界命中均为 $rI+sM$ 形）、$-25\le u,v\le25$ 的观察—范数恒等式，以及 23 个奇素数 $p\le97$（排除 $5$）的黄金 Frobenius 标量回返。它们只核对有限样本和坐标公式，不替代本节全称证明或 Lean 编译。

## 追加锚（本行以下为增补区）

## 17. 共轭双通道与恢复边界

本节把单个观察元素的作用与共轭双通道分开，恢复对象始终是组成环中的元素；读数的类型、是否取模以及允许的解码运算，都是恢复合同的一部分。

### definition 17.1 同一输入的共轭权重双通道

沿用 $R=\mathbb Z[\theta]/(\theta^2-\theta-1)$、$x=a+b\theta$，并记

$$
\theta^*=1-\theta,\qquad
x^*=(a+b)-b\theta,\qquad
N(x)=xx^*=a^2+ab-b^2,\qquad
\operatorname{Tr}(x)=x+x^*=2a+b.
$$

这里 $N$ 与第 15 节的 $\mathcal N$ 是同一范数。对整数权重 $u,v$，定义

$$
h=(v-u)+u\theta,\qquad
E_h:R\longrightarrow R^2,\qquad
E_h(x)=(hx,h^*x).
$$

第二通道是以共轭权重 $h^*$ 乘同一个输入 $x$；它不是把第一通道的输出取共轭，因为 $(hx)^*=h^*x^*$。这里输出的是两个完整的 $R$ 值，亦即四个整数系数；$E_h$ 是双通道编码，不称为压缩。

### proposition 17.2 Fib 素权重 $(5,13)$ 的整环值解码器

对 $u=5,v=13$，有

$$
h=8+5\theta,\qquad h^*=13-5\theta,\qquad
N(h)=79,\qquad \operatorname{Tr}(h)=21.
$$

由 $4\cdot79-15\cdot21=1$，得到环内的 Bezout 恒等式

$$
\begin{aligned}
1&=4hh^*-15(h+h^*)\\
 &=(37-20\theta)h-15h^*.
\end{aligned}
$$

因此定义有明确类型的解码器

$$
L:R^2\longrightarrow R,\qquad
L(y,z)=(37-20\theta)y-15z,
$$

便有

$$
L(E_h(x))=\bigl((37-20\theta)h-15h^*\bigr)x=x
\qquad(x\in R).
$$

对每个整数 $m\ge1$，把系数、输入和输出同时约化到 $\bar R_m=R/mR$，同一恒等式给出

$$
\bar E_h:\bar R_m\longrightarrow\bar R_m^2,\qquad
\bar L:\bar R_m^2\longrightarrow\bar R_m,\qquad
\bar L\circ\bar E_h=\operatorname{id}_{\bar R_m}.
$$

所以该双通道在每个模数下都可恢复组成余数。$37-20\theta$ 与 $-15$ 是所选权重的 Bezout 见证，不是物理常数，也不指定任何物理测量装置。

### proposition 17.3 精确像指标与模碰撞分离

对 $h=c+d\theta$，乘法 $x\mapsto hx$ 在整数基 $(1,\theta)$ 下的矩阵为

$$
A_h=\begin{pmatrix}c&d\\d&c+d\end{pmatrix},\qquad
\det A_h=N(h)=c^2+cd-d^2.
$$

由于 $R$ 嵌入 $\mathbb Q(\sqrt5)$，非零 $h$ 的乘法在精确的 $R$ 上是单射，并且

$$
[R:hR]=|N(h)|.
$$

特别地，$h=8+5\theta$ 时指标为 $79$：它说明单个 $h$ 通道的精确像不是整个 $R$，任意指定的输出未必有整数原像；它不说明两个不同的精确整数输入会碰撞。

对整数 $m\ge2$，单个 $h$ 通道在 $R/mR$ 上可逆当且仅当 $\gcd(N(h),m)=1$；当且仅当 $\gcd(N(h),m)>1$ 时存在不同余数输入的碰撞。这里使用的是有限模上的行列式判据，不能反推精确整数域有碰撞。例如

$$
w=-13+5\theta=-h^*,\qquad
hw=-79,
$$

所以 $w\bmod79R$ 非零而 $hw\equiv0\pmod{79R}$。这是单通道的模盲点；命题 17.2 的双通道解码恒等式保证它不会同时成为双通道的非零核。

### proposition 17.4 两个标量系数读数是另一接口

若只保留两个通道的 $\theta$ 系数，即读取 $\varepsilon(hx)$ 与 $\varepsilon(h^*x)$，则在上述 $(5,13)$ 例中

$$
\binom{\varepsilon(hx)}{\varepsilon(h^*x)}
=\begin{pmatrix}5&13\\-5&8\end{pmatrix}\binom ab,
\qquad
\det\begin{pmatrix}5&13\\-5&8\end{pmatrix}=105.
$$

这两个标量在精确整数域仍区分不同输入，但其像指标为 $105$，不是整个 $\mathbb Z^2$；模 $m\ge2$ 的可逆性要求 $\gcd(105,m)=1$。$L$ 的定义域是 $R^2$，它使用完整环值，因而命题 17.2 本身不能充当这个两标量接口的解码证明，更不能推出两标量在每个模数下都可恢复。

### theorem-form 17.5 本原元素的条件代数桥梁（open）

以下仅作为散文层的条件桥梁记录，形式化状态保持 open。设 $h=c+d\theta$ 满足 $\gcd(c,d)=1$，令

$$
N=c^2+cd-d^2,\qquad T=2c+d.
$$

拟采用的本原性桥梁为

$$
\gcd(N,T)\in\{1,5\}.
$$

其中 $T^2-4N=5d^2$ 是连接本原性与分歧素数 $5$ 的代数关系；本条不把这一桥梁报告为 Lean 已验证定理。

若 $\gcd(N,T)=1$，取整数 $r,s$ 使 $rN+sT=1$，结合 $hh^*=N$ 和 $h+h^*=T$，得到条件解码式

$$
(rh^*+s)h+sh^*=1,\qquad
L_{r,s}(y,z)=(rh^*+s)y+sz,\qquad
L_{r,s}(E_h(x))=x.
$$

该 Bezout 构造在前提成立时可同时约化到每个 $R/mR$。若公因子为 $5$，Bezout 组合先给出的是 $5$ 而不是 $1$；对与 $5$ 互素的模数，可以再乘以 $5$ 的逆元。对含因子 $5$ 的模数，可能剩余的恢复障碍是分歧的一阶方向：模五的候选局部描述为

$$
R/5R\cong\mathbb F_5[\eta]/(\eta^2),\qquad
\theta=3+\eta.
$$

在 $5\mid N,T$ 的本原情形中，$h$ 与其共轭的常数部分模五消失，一阶方向因此必须单独处理。这不是精确 $R$ 上出现非零乘法核的断言；模数含高次 $5$ 因子时的完整联合核、可用解码及其条件仍留作 open。一般桥梁及分歧恢复分析均未在本节完成 Lean 形式化。

### proposition 17.6 递归、共轭与加法的运输

固定同一个 $h$。在 $R^2$ 上令乘以 $\theta$ 和加法均逐分量进行，则

$$
E_h(\theta x)=\theta E_h(x),\qquad
E_h(x+x')=E_h(x)+E_h(x').
$$

若 $E_h(x)=(y,z)$，由共轭保持乘法及其对合性，有

$$
E_h(x^*)=(hx^*,h^*x^*)=(z^*,y^*).
$$

所以输入取共轭对应输出交换两通道后逐通道取共轭。上述规则只表达环运算与编码的相容性，不赋予通道或递归任何物理含义。

## 18. Minkowski 双坐标、窗口与全息解释边界

### definition 18.1 算术的两个实嵌入

令

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
\psi=\frac{1-\sqrt5}{2}=-\varphi^{-1},
$$

并对 $x=a+b\theta\in R$ 定义

$$
\sigma_+(x)=a+b\varphi,\qquad
\sigma_-(x)=a+b\psi,\qquad
\iota(x)=(x_+,x_-)=(\sigma_+(x),\sigma_-(x)).
$$

这里的 Minkowski 双坐标是数域的两个实嵌入所给出的算术映射，不是 Lorentz 时空度规。由两个根都满足 $t^2=t+1$，有

$$
\iota(\theta x)=(\varphi x_+,\psi x_-),\qquad
\iota(x^*)=(x_-,x_+),\qquad
N(x)=x_+x_-.
$$

沿用 $F_0=0,F_1=1$ 的 Fibonacci 编号，对 $j\ge1$，

$$
\theta^j=F_{j-1}+F_j\theta.
$$

这些是递归作用、共轭交换与范数的坐标表达，范数乘积本身不提供物理距离或因果关系。

### proposition 18.2 旧数量观察的双嵌入表达

由于 $x_+-x_-=b\sqrt5$，有

$$
\varepsilon(x)=\frac{x_+-x_-}{\sqrt5},\qquad
q_{2,3}(x)=\varepsilon(\theta^3x).
$$

因此对每个 $j\ge0$，

$$
q_{2,3}(\theta^j x)
=\frac{\varphi^{j+3}x_+-\psi^{j+3}x_-}{\sqrt5}.
$$

这个表达把既有的整数数量响应分解为两个算术谱方向，并没有把原来一个标量观察改成两个独立可取得的实数测量。

### definition 18.3 组成状态的观察视界

在组成状态空间 $V=\mathbb Z^2\cong R$ 上取 $q=q_{2,3}$ 和更新 $M$。本条的 $h\in\mathbb N$ 是观察视界，与第 17 节的环元素 $h$ 分属不同记号作用域。定义

$$
R_h(z,z')\iff
\forall k\in\mathbb N,\ 0\le k\le h\Longrightarrow q(M^kz)=q(M^kz'),
\qquad
R_\infty=\bigcap_{h\ge0}R_h.
$$

### proposition 18.4 两次观察已给出组成对角关系

记 $\operatorname{Diag}(V)=\{(z,z):z\in V\}$。由

$$
\binom{q(z)}{q(Mz)}
=\begin{pmatrix}2&3\\3&5\end{pmatrix}z,\qquad
\det\begin{pmatrix}2&3\\3&5\end{pmatrix}=1,
$$

得到

$$
R_1=\operatorname{Diag}(V),\qquad R_\infty=R_1.
$$

这里使用的是 $k=0,1$ 的两次观察，即初始读数和更新一次后的读数；不把它称为“两步”。这也限定第 13.7 节标题中的“两步”说法：稳定依据是这两次读数的整数可逆矩阵，而非某个有限状态数的估计。

拉回到原始树时，由 $c(\rho(t))=Mc(t)$，所得关系仍为

$$
(c\times c)^{-1}(R_\infty)
=\ker(c)
:=\{(t,t'):c(t)=c(t')\}.
$$

这里 $\ker(c)$ 指映射的核等价关系；它继续忘记树的次序、括号和原始语法，不等于全部路径观察的核。状态空间 $\mathbb Z^2$ 是无限集，上面的论证直接使用整数矩阵；未给出显式商或有界域前，不能对它套用要求 `Fintype` 的有限状态定理。

### proposition 18.5 算术伸缩与可见性的条件

因为 $\varphi>1$ 且 $|\psi|<1$，递归在 $x_+$ 方向扩张，在 $x_-$ 方向交替变号并收缩。这是算术谱方向的性质；只有在另行指定观察接口及其解释映射后，才可条件性地赋予它们“可见边界”与“内部稳定方向”的角色。

精确的单个嵌入 $\sigma_+:R\to\mathbb R$ 已经是单射：若 $a+b\varphi=0$，则由 $\varphi$ 的无理性知 $a=b=0$。所以收缩不会产生一个非零而精确不可见的环状态；某一坐标趋于零也不等于完整状态等于零。有限精度、噪声条件下的恢复稳定性尚未证明，须另给精度、误差、输入范围和解码成本合同。

### definition 18.6 条件窗口模型

若显式选择一个内部窗口 $W\subseteq\mathbb R$，可以定义

$$
\Lambda(W)=\{\sigma_+(x):x\in R,\ \sigma_-(x)\in W\}.
$$

本定义只给出条件性的选点模型，并未选定任何具体窗口。窗口的紧致性、非空内点、端点纳入约定及边界测度条件，都是须分别声明的条件；投影在所用格上的单射性、内部投影的稠密性、选点集对更新的前向不变性，以及它与树／路径语言之间的因子化及相容性，也各有独立的假设或证明义务。命题 18.5 的精确单射性只处理其中一个问题，不包办其余条件。

因为 $\theta$ 是单位且 $\theta^{-1}=\theta-1$，对任意已选 $W$ 有纯代数运输式

$$
\varphi\Lambda(W)=\Lambda(\psi W),\qquad
\psi W=\{\psi w:w\in W\}.
$$

正向取 $y=\theta x$，反向取 $x=\theta^{-1}y$，即得到等式的两个包含。它运输的是窗口；它不自动给出固定窗口下的前向不变性，例如 $\psi W\subseteq W$ 才是一个另外可用的充分条件。

这里没有证明任何窗口选点恰好等于 Fibonacci 生成轨道，也没有给出完整的模型集定理。窗口有界亦不意味着选点集有限：仅约束内部坐标，并未把两个坐标同时限制在有界区域。

### proposition 18.7 对“有限”与“亏损”的读法限定

第 13.3、13.7 节及第 14 节中的“有限”须区分有限观察深度、有限寄存器个数和在已声明合同下的有限寄存器字母表。两个整数寄存器具有无限取值范围；有限状态需要显式商（如模 $m$ 的组成余数域）或显式有界域，并须说明更新怎样在该域上定义或保持封闭。

对非退化的 $H_{u,v}$，$|\Delta|>1$ 是格像指标，表示目标整数对须满足像内相容条件，不会把不同的精确整数输入识别为同一个输出。因此第 14 节把有限指标统称为“观察分辨率不足”的语言在精确整数合同下不适用。模碰撞必须声明模数并使用 $\gcd(\Delta,m)>1$ 的条件；精度碰撞必须声明量化或舍入、误差及输入域。格像指标本身不提供这些碰撞合同，也不自动成为熵亏损。

### 18.8 全息角色的严格物理边界

在本批的可用解释中，“边界”只指为一个已声明的组成任务服务的观察接口，“径向深度”只指递归的迭代次数。把算术谱方向、观察接口或迭代编号进一步解释为物理对象，必须独立提出桥接假设并接受审查。

本节没有断言物理度规或因果结构、量子态、熵／面积泛函、边界场论、物理常数、RT 等式或 AdS/CFT 字典。这些物理桥梁均保持 open，需要独立的假设、构造与评审。

本批状态：第 17、18 节是纯理论增补，未经过 Lean 验证；既有有限核验和仓内源码检查均不构成本批的 Lean 证明。条件代数桥梁、窗口模型及物理解释保留上述未决边界。



## 19. 递归、共轭与方向提取生成的完整操作系统

本节把第 15 节的黄金整数载体和第 17 节的观察接口继续组织成一个操作系统。这里的“完整”只指二维整数组成空间上的线性操作完备，不把它解释为原始树语法、物理时空或所有非线性过程的完备。

### definition 19.1 递归、共轭与方向提取

令

$$
R=\mathbb Z[\theta]/(\theta^2-\theta-1),
\qquad x=a+b\theta.
$$

在坐标空间 $R\cong\mathbb Z^2$ 上定义

$$
M(a,b)=(b,a+b),
$$

$$
J(a,b)=(a+b,-b),
$$

以及选定的归一化方向提取

$$
\partial(a,b)=(b,0).
$$

前两个操作分别是乘以 $\theta$ 和黄金共轭；$\partial$ 不是由指数5唯一强迫的操作，而是选择了“读取 $\theta$ 系数并把结果放回标量方向”的基本接口。

它们的矩阵为

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},
\qquad
J=\begin{pmatrix}1&1\\0&-1\end{pmatrix},
\qquad
\partial=\begin{pmatrix}0&1\\0&0\end{pmatrix}.
$$

### theorem 19.2 递归与共轭的操作格有指数五缺口

$$
M^2=M+I,
\qquad J^2=I,
\qquad JM=(I-M)J.
$$

因此，由 (M,J) 的加法、取负与复合生成的整数操作环为

$$
\boxed{
\mathbb Z\langle M,J\rangle
=\mathbb ZI+\mathbb ZM+\mathbb ZJ+\mathbb ZMJ.
}
$$

并且它作为 $\operatorname{Mat}_2(\mathbb Z)$ 中的整数格具有指数5：

$$
\boxed{
[\operatorname{Mat}_2(\mathbb Z):\mathbb Z\langle M,J\rangle]=5.
}
$$

**证明。**

三条关系把任意操作词化为 (aI+bM+cJ+dMJ)。按矩阵坐标展开这四个基矩阵，列向量矩阵为

$$
K=
\begin{pmatrix}
1&0&1&0\\
0&1&1&-1\\
0&1&0&1\\
1&1&-1&0
\end{pmatrix},
\qquad \det K=5.
$$

所以四个矩阵在有理数上张成全部二维矩阵空间，但在整数格中留下指数5的余量。证毕。 $\square$

当 $5\nmid n$ 时，$K$ 在模 $n$ 下可逆，故 $M,J$ 模 $n$ 已能生成全部二维矩阵；当 $5\mid n$ 时，缺口正是黄金关系的分歧方向，不能被同一组整数系数消去。

### theorem 19.3 共轭差分提取缺失方向

令

$$
\delta=2\theta-1.
$$

则

$$
\delta^2=5,
\qquad
x-x^*=\delta\,\partial x.
$$

并且

$$
\boxed{
\partial(xy)=\partial(x)y+x^*\partial(y).
}
$$

此外，作为整数线性操作有

$$
\boxed{
5\partial=(2M-I)(I-J).
}
$$

所以当5可逆时，$\partial$ 可以从递归和共轭恢复；模5时，$\partial$ 是一个必须单独保留的方向接口。

**证明。**

若 $x=a+b\theta$，则 $x-x^*=b(2\theta-1)$，给出第一式。对 $x=a+b\theta$、$y=c+d\theta$ 展开乘法，左边的 $\theta$ 系数为 $ad+bc+bd$，而右边同样为

$$
b(c+d\theta)+((a+b)-b\theta)d.
$$

最后一式由

$$
(2M-I)(I-J)x=\delta(x-x^*)=\delta^2\partial x=5\partial x
$$

得到。证毕。 $\square$

### theorem 19.4 递归与方向提取生成全部线性操作

$$
\boxed{
\mathbb Z\langle M,\partial\rangle
=\operatorname{Mat}_2(\mathbb Z).
}
$$

因此对每个 $n\ge2$，模 $n$ 后的 $M,\partial$ 生成

$$
\operatorname{Mat}_2(\mathbb Z/n\mathbb Z).
$$

**证明。**

由 $\partial=E_{12}$ 有

$$
E_{11}=\partial M-\partial,
\qquad
E_{21}=ME_{11},
\qquad
E_{22}=I-E_{11}.
$$

四个标准矩阵单位均已生成，结论随即成立。还可由

$$
J=I+(I-2M)\partial
$$

恢复共轭。这里的完备性是二维整数线性意义下的完备，不涉及原始树的括号、次序或物理解释。证毕。 $\square$

## 20. 模结构、Fib 项与非硬编码的素性刻画

### definition 20.1 模 $n$ 的操作系统

固定 $n\ge2$，令

$$
V_n=(\mathbb Z/n\mathbb Z)^2
$$

并把 $M,\partial$ 按同一坐标公式降到 $V_n$。称加法子群 $W\subseteq V_n$ 为封闭子结构，当

$$
M(W)\subseteq W,
\qquad
\partial(W)\subseteq W.
$$

这是操作闭包的定义；它不把 $W$ 预先假设成某个因子生成的子群。

### theorem 20.2 全部封闭子结构恰为因子倍子结构

$$
\boxed{
W\text{ 封闭}
\iff
W=dV_n\text{ 对某个唯一 }d\mid n.
}
$$

**证明。**

若 $(a,b)\in W$，则

$$
\partial(a,b)=(b,0)\in W,
\qquad
M(b,0)=(0,b)\in W.
$$

相减得到 $(a,0)\in W$，所以 $W=H\times H$，其中

$$
H=\{t\in\mathbb Z/n\mathbb Z:(t,0)\in W\}
$$

是循环群 $\mathbb Z/n\mathbb Z$ 的子群。循环群的子群唯一写成 $d(\mathbb Z/n\mathbb Z)$，其中 $d\mid n$，故 $W=dV_n$。反向包含显然成立，因为任何整数矩阵都保持 $dV_n$。证毕。 $\square$

### corollary 20.3 素数等价于操作原子性

$$
\boxed{
n\text{ 为素数}
\iff
\text{封闭子结构只有 }\{0\}\text{ 与 }V_n.
}
$$

这里明确要求 $n\ge2$。它是有限操作系统的结构判据，不是黄金整数环中元素为素元的判据，也不是声称固定局部读数即可完成的快速判素算法。

若 $n$ 为合数，任何真因子 $1<d<n$ 都给出

$$
\{0\}\subsetneq dV_n\subsetneq V_n.
$$

若 $n$ 为素数，则因子只有1与 $n$，相应地只剩全体与零子结构。

### definition 20.4 递归生成的 Fib 标量

令 $e=(1,0)\in R$，并定义

$$
s_j=\partial(M^j e),
\qquad j\ge0.
$$

由

$$
\theta^j=F_{j-1}+F_j\theta
$$

得到

$$
s_0=0,
\qquad s_1=1,
\qquad s_{j+2}=s_{j+1}+s_j,
$$

故 $s_j=F_j$。这与第 15 节使用的数量读数 $q_{2,3}(\theta^j)=F_{j+3}$ 是不同接口：前者是方向提取生成的标量，后者是给定权重的数量读数。

### theorem 20.5 Fib 素项的封闭结构刻画

对 $j\ge3$，定义

$$
\mathfrak V_j=(V_{F_j},M,\partial).
$$

则

$$
\boxed{
F_j\text{ 是素数}
\iff
\mathfrak V_j\text{ 没有非零真封闭加法子结构}.
}
$$

**证明。**

把定理 20.2 应用于 $n=F_j$ 即得。证毕。 $\square$

例如 (F_7=13) 的系统只有零和全体，而 (F_8=21) 的系统还含有 (3V_{21}) 与 (7V_{21})。这是由统一生成规则产生的结构差别，不是为素数项另写的标签规则。

## 21. 端口关系、记录与动态边界

### definition 21.1 局部关系元与相容解

一个端口取值域可以是 $R$、$V_n$ 或另行声明的有限标签集。对操作 $T$ 定义关系

$$
\mathcal R_T=\{(x,y):y=T(x)\}.
$$

一份有限端口网络由端口、局部关系元及共享端口组成。其相容解集记为

$$
\mathcal S(\mathcal K)=\{\text{满足全部局部关系的端口赋值}\}.
$$

静态整体在本层就是这份关系网络及其相容解集；选择某些端口作输入、输出或边界，是在同一关系上增加观察和任务。

### theorem 21.2 关系网络按共享端口作纤维积拼接

设网络 $U,V$ 覆盖 $U\cup V$，并且每个局部关系都包含在至少一个区域中。保留交界上的全部共享端口，则

$$
\boxed{
\mathcal S(U\cup V)
\cong
\mathcal S(U)\times_{\mathcal S(U\cap V)}\mathcal S(V).
}
$$

**证明。**

整体解限制到两个区域，必然在交界一致；反过来，交界一致的两份局部解唯一拼成整体赋值，且每个局部关系已在某个区域中验证。证毕。 $\square$

这条纤维积公式表达了“关系的关系”：高层对象保存的不是两个区域名称，而是它们能否在共同端口上拼接。

### definition 21.3 边界任务的全息性

给定相容解集 $\mathcal S(\mathcal K)$ 和边界观察

$$
O_B:\mathcal S(\mathcal K)\to\mathcal B,
$$

对任务 $\tau:\mathcal S(\mathcal K)\to Y$，若存在 $D_B$ 使

$$
\tau=D_B\circ O_B,
$$

则称边界 $B$ 对任务 $\tau$ 全息。等价地，$O_B$ 的每个纤维上 $\tau$ 都是常值的。若 $\tau$ 是恒等任务，则全息性就是边界观察的单射性。

这里的“全息”是任务相对的边界充分性，不等于物理全息原理。

### proposition 21.4 方向提取的记录扩展

在 $V_n$ 上，裸方向提取

$$
\partial(a,b)=(b,0)
$$

丢掉 $a$。定义带记录的扩展

$$
\widetilde\partial(a,b)=((b,0),a).
$$

它是单射，且逆恢复为

$$
((b,0),a)\longmapsto(a,b).
$$

对允许全部 $V_n$ 输入的合同，固定活动输出 $(b,0)$ 时仍有 $n$ 个不同的 $a$，所以任何无损记录至少需要 $n$ 个可能值；记录 $a$ 达到这个下界。沿受限路径可有更小的实际记录，但必须另行证明。

因此，动态边界应保留活动状态、动作身份及从活动状态移出的必要记录。仅保留 $\partial x$ 不能声称旧整体仍可由新边界恢复。

### proposition 21.5 截面推进与非交换路径

给事件网络指定依赖关系。若事件集 $C$ 包含每个已选事件的全部前驱，则 $C$ 给出一个合法截面；加入一个前驱已满足的事件，使活动边界从 $\Sigma_C$ 移到 $\Sigma_{C'}$。这给出内部过程的离散时间顺序。

它不是无向图自动产生的物理时间；依赖方向和记录接口必须是模型的一部分。

在本操作系统中还有

$$
\boxed{\partial M-M\partial=J.}
$$

因为 $J$ 在所有模数下可逆，所以对非零状态先递归再提取和先提取再递归必然不同。只按起点、终点的名称合并两条路径，会丢失接续顺序。

## 22. 黄金不定二次型与代数时空的边界

### theorem 22.1 递归保持一个签名为 ((1,1)) 的二次型

定义

$$
Q(a,b)=a^2+ab-b^2.
$$

则

$$
\boxed{
Q(Mx)=-Q(x),
\qquad
Q(M^2x)=Q(x).
}
$$

在实对称二次型中，满足 (H(M^2x,M^2x)=H(x,x)) 的 (H) 都是 (Q) 的实数倍。

**证明。**

第一式直接展开，第二式由第一式应用两次得到。若

$$
H=\begin{pmatrix}r&s\\s&t\end{pmatrix},
$$

代入 $(M^2)^{\mathsf T}HM^2=H$ 得 $r=2s$、$t=-2s$，故 $H$ 与 $Q$ 成比例。其行列式为负，签名为 $(1,1)$。证毕。 $\square$

令

$$
\xi=a+\frac b2,
\qquad
\tau=\frac{\sqrt5}{2}b.
$$

则

$$
Q=\xi^2-\tau^2,
$$

而 (M^2) 在这组坐标下为

$$
\begin{pmatrix}\xi'\\\tau'\end{pmatrix}
=
\begin{pmatrix}
3/2&\sqrt5/2\\
\sqrt5/2&3/2
\end{pmatrix}
\begin{pmatrix}\xi\\\tau\end{pmatrix}.
$$

这是代数上的 (1+1) 维 boost，满足

$$
\left(\frac32\right)^2-\left(\frac{\sqrt5}{2}\right)^2=1,
\qquad
\eta=2\log\varphi.
$$

### proposition 22.2 物理解释的独立义务

上面的 $Q$、$\xi$、$\tau$ 只属于黄金整数的实代数载体；递归次数只属于事件网络的离散依赖。它们不能仅凭矩阵恒等式被命名为物理度规、固有时间、因果方向或径向坐标。

若要作这些物理解释，至少还需独立给出状态到物理事件的映射、合法方向、测量规则、单调性和误差合同。现实中的光速、引力方程、维数和 AdS/CFT 字典均不由本节推出。

## 23. 四次 Fibonacci 响应、量子张量与闭环约束

### definition 23.1 独立的四响应关系

在有限标签环 $R_n=\mathbb Z/n\mathbb Z$ 中独立取 $u,v\in R_n$，定义

$$
T_n(u,v)=(u,v,u+v,u+2v).
$$

这四个端口是同一 Fibonacci 关系的连续响应；这里的 $u,v$ 是独立坐标，不是第 20 节的 $q_{5,13}$ 三读中的某个标量，也不要求 $\gcd(n,79)=1$。

### theorem 23.2 四腿相干态在奇数模数下为完美张量

对 $n\ge2$，在独立加入 Hilbert 空间 $\mathbb C^n$、计算基和等权相干叠加后，定义

$$
|T_n\rangle
=
\frac1n\sum_{u,v\in R_n}
|u,v,u+v,u+2v\rangle.
$$

则

$$
\boxed{
|T_n\rangle\text{ 的任意两腿约化态最大混合}
\iff n\text{ 为奇数}.
}
$$

**证明。**

四个端口的系数行分别是

$$
(1,0),\quad(0,1),\quad(1,1),\quad(1,2).
$$

任取两行，行列式为 $\pm1$ 或 $\pm2$。当 $n$ 为奇数时均为单位，任意两端口唯一确定 $u,v$，偏迹后得到 $I_{n^2}/n^2$。当 $n$ 为偶数时，端口0和3的行列式为2，不可逆，约化态不能最大混合。证毕。 $\square$

这里必须区分三种对象：经典四响应是一个有限关系；四腿完美张量是额外选择 Hilbert 空间和相干振幅后的量子对象；量子秘密分享还需要编码映射、恢复通道和对单份信息的独立验证。三者不能仅凭同一组整数公式互相等同。

### proposition 23.3 四端口编码的成对恢复

对奇数 (n)，定义编码器

$$
\mathcal V_n|s\rangle
=
\frac1{\sqrt n}\sum_{j\in R_n}|j,j+s,j+2s\rangle.
$$

任意两份边界足以恢复输入。以前两份为例，变换

$$
(u,v)\longmapsto(v-u,2v-u)
$$

把 ((j,j+s)) 送到 ((s,j+2s))，从而将输入与剩余的均匀相关寄存器分离。另两对使用相应的可逆线性变换，其中 ((u,w)) 的恢复需要2在模 (n) 下可逆。

这个命题属于量子编码层；它不把 $n$ 的素性、$M,\partial$ 的操作原子性或物理引力性质作为前提或结论。

### theorem 23.4 闭环的全局约束可造成全息亏损

将局部四响应关系按闭环拼接，并令输出满足

$$
b_i=x_i+2x_{i+1}\pmod n.
$$

在奇数 (n)、奇数环长 (L) 以及归一化等权状态的指定边界子系统下，不可见变化满足

$$
x_{i+1}=-2^{-1}x_i,
$$

绕环一致性等价于

$$
(2^L+1)x_0=0\pmod n.
$$

因此其不可见方向数为 $\gcd(n,2^L+1)$，相应的熵表达式为

$$
\boxed{
S(A)=L\log n-\log\gcd(n,2^L+1).
}
$$

这里的熵必须理解为该闭环网络、该归一化态和该边界分割下的 von Neumann 熵；它不是所有网络或所有分布的普适公式。局部张量完美只给出几何割的上界，不能消除闭环的算术相容条件。

例如 (n=3,L=3) 时，

$$
S(A)=2\log3,
$$

而三条割腿的容量为 $3\log3$。差额来自闭环的全局核，而非某个局部张量失去完美性。

### proposition 23.5 关系求和的三种语义

对区域 (U) 的边界赋值 (b)，定义边界响应

$$
\mathcal H_U(b)=
\sum_{\text{内部相容变量}}
\prod_{e\subseteq U}W_e.
$$

若取布尔权重，它表达合法拼接的存在性；取非负整数权重，它统计相容见证数；取复权重，它计算相干振幅。相同的消元结合律可用于三种语义，但三者的读数不可互换。

增加一个事件后的动态规划为

$$
\mathcal H_{\Sigma'}(b')
=
\sum_{b,z}\mathcal H_\Sigma(b)W_e(b,z,b'),
$$

其中 (z) 包含新收进内部的变量与必要记录。有限求和的结合律保证同一关系网络的合法消元顺序得到同一边界响应；它不允许交换原本不交换的局部操作。

## 24. 本批结论、范围与未决桥梁

本批把前面的黄金整数操作、Fib 生成、边界观察和全息张量连接成五层结构：

$$
\boxed{
\text{递归与共轭操作格}
\longrightarrow
\text{方向提取与模操作原子性}
\longrightarrow
\text{端口关系与记录边界}
\longrightarrow
\text{代数不定型}
\longrightarrow
\text{可选的量子张量与闭环全局约束}.
}
$$

其中可以直接由整数代数证明的是操作关系、封闭子结构分类、$F_j$ 的结构素性判据、端口纤维积、记录扩展、二次型不变量以及四响应的奇数模数线性可逆性。四腿态、秘密分享、熵和动态规划需要另行声明 Hilbert 空间、权重、归一化和边界分割。

本批没有声称：

- 任何新增结论已经由 Lean 编译或冻结；
- $Q$、$\partial$、$J$ 或递归深度就是物理度规、时间、因果或径向坐标；
- 素性判据是常数半径或固定局部资源的快速判素算法；
- 局部完美张量自动给出任意闭环的面积律或 RT 等式；
- 算术关系网络已经构成现实的时空或 AdS/CFT 理论。

需要独立解决的开放桥梁包括：有限关系网络到项目行为商的正式 Lean 接口、记录路径的最小性合同、闭环熵公式的完整状态空间证明、算术标签到 Hilbert 张量的统一函子，以及任何物理解释所需的动力学和测量公理。

本批状态：纯理论追加，保留精确适用条件和上述 open 边界。形式化、消化、冻结与远程合并状态以项目机器读数为准。

## 25. 进位关系与层级连接

本批把前面的端口关系继续提升到分辨率塔。低层坐标和高层坐标的集合分解是可逆的，但运算是否分层，取决于进位关系是否被保留。

### definition 25.1 两层数字分解与进位

令 $D=de$，把 $x\in\mathbb Z/D\mathbb Z$ 写成

$$
x=a+db,
\qquad 0\le a<d,\quad 0\le b<e.
$$

这是集合双射

$$
\mathbb Z/D\mathbb Z
\longleftrightarrow
\{0,\ldots,d-1\}\times\{0,\ldots,e-1\}.
$$

对 $y=c+df$，定义低位进位

$$
\boxed{
\kappa_d(a,c)=\frac{a+c-[a+c]_d}{d}.
}
$$

于是

$$
x+y=[a+c]_d+d\bigl(b+f+\kappa_d(a,c)\bigr),
$$

其中高位结果再模 $e$。高层后继因此等于高层自己的加法和低层共同关系产生的进位。

### theorem 25.2 进位满足接续相容律

$$
\boxed{
\kappa_d(a,c)+\kappa_d([a+c]_d,z)
=
\kappa_d(c,z)+\kappa_d(a,[c+z]_d).
}
$$

**证明。** 两边都等于

$$
\frac{a+c+z-[a+c+z]_d}{d}.
$$

所以不同的二元拼接顺序携带相同的总进位。证毕。 $\square$

### proposition 25.3 层间加法分裂的互素条件

对标准短序列

$$
0\longrightarrow\mathbb Z/e\mathbb Z
\overset{\times d}{\longrightarrow}\mathbb Z/de\mathbb Z
\longrightarrow\mathbb Z/d\mathbb Z
\longrightarrow0
$$

存在保持加法的截面，当且仅当

$$
\boxed{\gcd(d,e)=1.}
$$

**证明。** 截面由 $1$ 的像 $t$ 决定，必须满足 $t\equiv1\pmod d$ 且 $dt\equiv0\pmod{de}$，即 $e\mid t$。这两个条件可同时满足恰当且仅当 $d,e$ 互素。证毕。 $\square$

所以不同素数方向可以用 CRT 分离；同一素数的连续精度通常不能拆成独立层，而要由进位耦合。

## 26. 递归操作的跨尺度运输

### definition 26.1 整数操作的进位函数

令 $T$ 为整数矩阵，低层代表为 $a$。定义

$$
\boxed{
c_T(a)=\frac{Ta-[Ta]_d}{d}\pmod e.
}
$$

则

$$
\boxed{
T(a+db)\longleftrightarrow
\bigl([Ta]_d,\,Tb+c_T(a)\bigr).
}
$$

对 Fibonacci 更新 $M(a_0,a_1)=(a_1,a_0+a_1)$，其低层进位为

$$
\boxed{
c_M(a_0,a_1)=left(0,\left\lfloor\frac{a_0+a_1}{d}\right\rfloor\right).
}
$$

### theorem 26.2 操作复合的进位律

对整数矩阵 $T,U$，有

$$
\boxed{
c_{TU}(a)=T c_U(a)+c_T([Ua]_d)\pmod e.
}
$$

**证明。** 先写 $Ua=[Ua]_d+d c_U(a)$，再施加 $T$ 并对 $T[Ua]_d$ 作同一低高分解。证毕。 $\square$

低位取模与整数线性更新相容，因而低位动力学可以闭合；这不表示低层和高层独立，也不表示量子态在丢弃高层后仍保持纯态。仓库已有的联合进位修正正是为保留后一种联合关系。

## 27. 线性关系网络的细层提升障碍

### definition 27.1 模数关系网络

令 $A\in\operatorname{Mat}_{r\times s}(\mathbb Z)$，并定义

$$
\mathcal S_n=\{x\in(\mathbb Z/n\mathbb Z)^s:Ax=0\}.
$$

$A$ 可以同时包含局部递推、共享端口一致性和闭环约束。取 $a\in\mathcal S_d$ 的整数代表 $\widetilde a$，于是 $A\widetilde a=d\,\kappa_A(a)$。

### theorem 27.2 跨尺度提升障碍

定义

$$
\boxed{
\delta_{d,e}(a)=
\left[\frac{A\widetilde a}{d}\right]
\in
\frac{(\mathbb Z/e\mathbb Z)^r}{\operatorname{im}(A\bmod e)}.
}
$$

则

$$
\boxed{
a\text{ 能提升为 }\mathcal S_{de}\text{ 中的状态}
\iff
\delta_{d,e}(a)=0.
}
$$

该定义与代表选择无关：若 $\widetilde a'=\widetilde a+dt$，则商中的残差只增加 $At$。

**证明。** 细层候选写成 $x=\widetilde a+db$。条件 $Ax=0\pmod{de}$ 等价于

$$
Ab=-\frac{A\widetilde a}{d}\pmod e,
$$

这恰好表示残差属于 $\operatorname{im}(A\bmod e)$。证毕。 $\square$

令 $Y_{d,e}=\ker\delta_{d,e}\subseteq\mathcal S_d$。对每个 $a\in Y_{d,e}$，高层解是某个陪集 $b_0(a)+\mathcal S_e$，故

$$
\boxed{
|\mathcal S_{de}|=|Y_{d,e}|\,|\mathcal S_e|.
}
$$

相应地，以下序列在核与像处正合：

$$
0\longrightarrow\mathcal S_e
\overset{\times d}{\longrightarrow}\mathcal S_{de}
\longrightarrow\mathcal S_d
\overset{\delta_{d,e}}{\longrightarrow}
\operatorname{coker}(A\bmod e).
$$

因此每层分别存在合法状态，并不意味着任意粗层状态都能沿同一相容路径细化。

## 28. 量子粗化与进位相干

### definition 28.1 均匀相容态

在明确加入 Hilbert 空间和计算基后，定义

$$
|\Psi_n\rangle
=
\frac1{\sqrt{|\mathcal S_n|}}
\sum_{x\in\mathcal S_n}|x\rangle.
$$

按 $x=\widetilde a+db$ 分解，细层态为

$$
|\Psi_{de}\rangle
=
\frac1{\sqrt{|Y_{d,e}|\,|\mathcal S_e|}}
\sum_{a\in Y_{d,e}}
\sum_{z\in\mathcal S_e}
|a\rangle|b_0(a)+z\rangle.
$$

### theorem 28.2 受控进位修正后的层级分解

对每个可提升的 $a$ 选定高层解 $b_0(a)$，定义受控置换

$$
U|a\rangle|b\rangle=|a\rangle|b-b_0(a)\rangle.
$$

在无效低层标签上任意延拓为全空间置换，则

$$
\boxed{
U|\Psi_{de}\rangle
=|\Psi_{Y_{d,e}}\rangle\otimes|\Psi_e\rangle.
}
$$

**证明。** 每个细层纤维恰为 $b_0(a)+\mathcal S_e$；减去受控代表后，所有高层求和都相同，因而分离。证毕。 $\square$

这是均匀相容态的结论。对任意未知输入，$U$ 只是可逆坐标变换，并不自动把输入态变成两层乘积态；$b_0(a)$ 的取得也可能需要跨多个节点的联合操作。

### proposition 28.3 $T_9$ 直接丢高层时的混合谱

对四腿态

$$
|T_n\rangle=\frac1n\sum_{x,y\in\mathbb Z/n\mathbb Z}|x,y,x+y,x+2y|,
$$

取 $n=9$ 并写 $x=a+3b$、$y=c+3f$。输出进位为

$$
\kappa_1=\left\lfloor\frac{a+c}{3}\right\rfloor,
\qquad
\kappa_2=\left\lfloor\frac{a+2c}{3}\right\rfloor.
$$

九个低层输入的进位对计数为

$$
\begin{array}{c|cccc}
(\kappa_1,\kappa_2)&(0,0)&(0,1)&(1,1)&(1,2)\\ \hline
\text{次数}&4&2&2&1
\end{array}
$$

直接对高层取偏迹时，低层约化态的非零谱为

$$
\boxed{\left\{\frac49,\frac29,\frac29,\frac19\right\}},
$$

从而

$$
\boxed{S(\rho_{\mathrm{low}})=2\log3-\frac43\log2.}
$$

按低位联合信息从输出高位减去 $\kappa_1,\kappa_2$ 后，则有

$$
|T_9\rangle\longmapsto|T_3\rangle\otimes|T_3\rangle.
$$

所以混合谱正是未处理的进位记录，而不是抽象的“层级信息损失”。

## 29. 闭环隐藏核与相容极限

### definition 29.1 三节点闭环的隐藏核

令

$$
B=\begin{pmatrix}1&2&0\\0&1&2\\2&0&1\end{pmatrix},
\qquad
K_r=\ker(B\bmod3^r).
$$

$K_r$ 只记录边界看不见的内部差异，不是全部内部允许状态。

### proposition 29.2 每层隐藏数稳定但不形成无限线程

闭环递推给出 $x_{i+1}=-2^{-1}x_i$ 及 $9x_0=0\pmod{3^r}$，因此

$$
|K_r|=3^{\min(r,2)}.
$$

特别地，$|K_1|=3$、$|K_2|=9$，并且从 $K_{r+2}$ 自然约化到 $K_r$ 的像为零：高层核中的 $x_0$ 被 $3^r$ 整除。

### theorem 29.3 相容隐藏线程的逆极限为零

$$
\boxed{
\operatorname{im}(K_{r+2}\to K_r)=\{0\},
\qquad
\varprojlim_rK_r=\{0\}.
}
$$

**证明。** 模 $3^{r+2}$ 的隐藏条件要求 $x_0$ 是 $3^r$ 的倍数，其余坐标由 $x_0$ 决定；约化模 $3^r$ 后整个向量为零。相容线程的每个分量都来自更高两层，故只能为零。证毕。 $\square$

例如模9的隐藏差异 $(1,4,7)$ 满足 $B(1,4,7)=(9,18,9)$，但写成 $x=a+9b$ 提升到模27要求 $Bb=-(1,2,1)\pmod3$，右侧坐标和非零，而 $B\bmod3$ 的输出坐标和恒为零。因此它不能保持隐藏，只能在细边界暴露。

## 30. 恢复精度滞后与 Smith 因子

### theorem 30.1 三节点闭环需要两级三进精度

若 $y=Bx$，则

$$
\begin{aligned}
9x_0&=y_0-2y_1+4y_2,\\
9x_1&=4y_0+y_1-2y_2,\\
9x_2&=-2y_0+4y_1+y_2.
\end{aligned}
$$

所以 $y\bmod3^{r+2}$ 能恢复 $x\bmod3^r$。只给 $y\bmod3^{r+1}$ 不够：

$$
\Delta x=3^{r-1}(4,-2,1)
$$

在模 $3^r$ 下非零，而 $B\Delta x=3^{r-1}(0,0,9)\equiv0\pmod{3^{r+1}}$。

这里的两级是分辨率滞后，不是未经桥接的物理时间延迟。

### theorem 30.2 一般整数矩阵的恢复滞后

设方阵 $B$ 的行列式非零，Smith 标准形为

$$
UBV=\operatorname{diag}(s_1,\ldots,s_q),
$$

其中 $U,V$ 整数可逆，令 $\nu_i=v_p(s_i)$。则

$$
\boxed{
|\ker(B\bmod p^r)|=p^{\sum_i\min(r,\nu_i)}.
}
$$

从 $Bx\bmod p^{r+t}$ 统一恢复 $x\bmod p^r$ 所需的最小额外精度为

$$
\boxed{t_{\min}=\max_i\nu_i.}
$$

**证明。** 整数可逆换基不改变模 $p^r$ 的恢复性，故只需研究标量乘法 $z_i\mapsto s_i z_i$。其核大小为 $p^{\min(r,\nu_i)}$；已知输出多 $\max_i\nu_i$ 位足以逐项消去因子，不足该数时对应方向仍有不可见差异。证毕。 $\square$

因此

$$
\sum_i\min(r,\nu_i)
$$

计量当前未区分的信息量，而 $\max_i\nu_i$ 计量最坏方向的恢复滞后。二者不能混同。

## 31. 跨尺度全息的交换条件

### definition 31.1 同一整体的跨尺度编码

设 $\mathcal E_D$、$\mathcal E_d$ 是内部到边界的编码，$\mathcal Q_{D,d}$ 是内部粗化，$\mathcal R_{D,d}$ 是边界粗化。一个跨尺度编码系统要求对声明的全部输入满足

$$
\boxed{
\mathcal R_{D,d}\circ\mathcal E_D
=
\mathcal E_d\circ\mathcal Q_{D,d}.
}
$$

三个尺度还应满足

$$
\boxed{
\mathcal R_{d,f}\circ\mathcal R_{D,d}=\mathcal R_{D,f}.
}
$$

这两个等式把“属于同一个整体”写成交换图，而不是只比较每层状态数。对关系网络，首先还必须检查粗层状态的提升障碍是否为零。

### definition 31.2 算术恢复谱

对固定边界关系矩阵 $B$，定义

$$
\boxed{
\mathfrak D(B)=\{(p;\nu_1(p),\ldots,\nu_q(p))\}_p,
}
$$

其中 $\nu_i(p)$ 是 Smith 因子的 $p$-进指数。它同时记录素数方向上的碰撞数量、各层未区分信息量和最坏恢复精度滞后。

该谱在整数可逆换基下不变，但依赖实际关系系数和边界选择，不能称为只由裸图拓扑决定的不变量。局部 Fibonacci 更新满足 $\det M=-1$，因而没有恢复滞后；三节点闭环满足 $\det B=9$，故产生两级三进滞后。

## 32. 本批跨尺度结论与边界

同一关系系统现在有三个彼此不同但必须相容的方向：

$$
\boxed{
\text{事件方向：合法操作与记录接续};\quad
\text{精度方向：进位与提升障碍};\quad
\text{区域方向：局部拼接与闭环约束}.
}
$$

本批证明或直接构造了进位接续律、操作复合进位律、线性网络的提升障碍、均匀相容态的受控分解、$T_9$ 的未修正混合谱、闭环隐藏核的零逆极限以及 Smith 因子给出的恢复滞后。它们仍分别依赖所声明的模数、关系矩阵、态、边界和精度合同。

本批没有声称：

- 各层局部合法就自动存在共同的无限相容整体；
- 经典余数约化自动保留任意量子输入的相干性；
- 每层隐藏状态的数量等于无限隐藏历史的数量；
- 恢复精度滞后就是物理时间、曲率、引力或光速；
- 算术恢复谱只由网络拓扑决定，或已经给出现实全息时空模型。

新增的 Lean 接口、任意关系网络的统一量子函子、有限深度实现成本，以及物理动力学桥梁均保持 open。本批仍是纯理论追加，有限核验不替代 Lean 编译或项目冻结。

## 33. 边界缺陷群：核与余核的共同来源

本批把前两批的隐藏方向、合法边界、量子谱和恢复记录统一到一个整数缺陷群中。这里的边界矩阵是关系网络经消元和缝合后得到的模型数据；缺陷群不被解释为只由裸图拓扑决定的不变量。

### definition 33.1 整数边界缺陷群

令内部和形式边界均为整数格，取

$$
 y=Bx,
 \qquad B\in\operatorname{Mat}_d(\mathbb Z),
 \qquad \det B\ne0.
$$

定义

$$
\boxed{\mathcal D_B=\mathbb Z^d/B\mathbb Z^d.}
$$

它记录形式上可写出的边界与实际具有整数内部来源的边界之间的差别。由 Smith 标准形

$$
UBV=\operatorname{diag}(s_1,\ldots,s_d),
\qquad s_i>0,\quad s_i\mid s_{i+1},
$$

得到

$$
\boxed{\mathcal D_B\cong\bigoplus_i\mathbb Z/s_i\mathbb Z,\qquad |\mathcal D_B|=|\det B|.}
$$

### definition 33.2 有限精度的核与余核

固定素数 $p$ 和 $r\ge1$，令 $G_r=(\mathbb Z/p^r\mathbb Z)^d$，并记 $B_r$ 为模 $p^r$ 的约化。定义

$$
K_r=\ker B_r,
\qquad
C_r=G_r/\operatorname{im}B_r.
$$

$K_r$ 表示同一边界背后的内部混同，$C_r$ 表示没有任何内部来源的形式边界类别。

### theorem 33.3 核与余核来自同一个缺陷群

令 $\mathcal D_B[p^r]=\{z\in\mathcal D_B:p^rz=0\}$。则

$$
\boxed{K_r\cong\mathcal D_B[p^r],\qquad C_r\cong\mathcal D_B/p^r\mathcal D_B.}
$$

**证明。** 对 $x\in K_r$ 取整数代表 $\widetilde x$，定义

$$
\alpha_r(x)=\left[\frac{B\widetilde x}{p^r}\right]\in\mathcal D_B.
$$

更换代表只增加 $B\mathbb Z^d$，故无歧义；其像被 $p^r$ 消去。若像为零，$B$ 在整数格上单射，得到 $\widetilde x\in p^r\mathbb Z^d$，所以 $x=0$。反过来，$p^r[y]=0$ 恰好给出 $p^ry=Bx$ 的核原像。余核同构直接由

$$
G_r/\operatorname{im}B_r\cong\mathbb Z^d/(B\mathbb Z^d+p^r\mathbb Z^d)
$$

得到。证毕。 $\square$

## 34. 相容极限消除内部混同，但保留边界约束

### theorem 34.1 两种缺陷的跨尺度映射

在定理 33.3 的识别下，核的自然约化对应

$$
\boxed{\mathcal D_B[p^{r+1}]\overset{\times p}{\longrightarrow}\mathcal D_B[p^r],}
$$

而余核对应商约化

$$
\mathcal D_B/p^{r+1}\mathcal D_B
\longrightarrow
\mathcal D_B/p^r\mathcal D_B.
$$

因为对同一代表有

$$
\left[\frac{B\widetilde x}{p^r}\right]
=p\left[\frac{B\widetilde x}{p^{r+1}}\right].
$$

所以相邻精度的核即使有相同大小，也不必按恒等方式对应。

### theorem 34.2 完整相容极限

令 $\mathcal D_{B,p}$ 为 $\mathcal D_B$ 的 $p$-主子群，则

$$
\boxed{\varprojlim_rK_r=0,\qquad \varprojlim_rC_r\cong\mathcal D_{B,p}.}
$$

等价地，在 $p$-进整数上有

$$
\boxed{0\longrightarrow\mathbb Z_p^d\overset B\longrightarrow\mathbb Z_p^d\longrightarrow\mathcal D_{B,p}\longrightarrow0.}
$$

**证明。** 取 $t$ 使 $p^t\mathcal D_{B,p}=0$。相容核线程满足 $z_r=p^tz_{r+t}=0$。余核商在 $r$ 超过所有 $p$-幂阶后稳定为 $\mathcal D_{B,p}$。Smith 坐标中这分别是 $p$-进整数上非零标量乘法的单射性和有限商 $\mathbb Z_p/s_i\mathbb Z_p$。证毕。 $\square$

因此“隐藏线程消失”不等于边界任意自由；准确说法是实际边界有唯一内部来源，但并非每个形式边界都可实现。

### proposition 34.3 三节点环的模九边界条件

取

$$
B=\begin{pmatrix}1&2&0\\0&1&2\\2&0&1\end{pmatrix}.
$$

其 Smith 因子为 $(1,1,9)$，所以 $\mathcal D_B\cong\mathbb Z/9\mathbb Z$。令 $s(y)=y_0-2y_1+4y_2$。由于

$$
(1,-2,4)B=(9,0,0),
$$

实际边界满足 $s(y)\equiv0\pmod9$；这也是充分条件，因为

$$
\begin{aligned}
9x_0&=y_0-2y_1+4y_2,\\
9x_1&=4y_0+y_1-2y_2,\\
9x_2&=-2y_0+4y_1+y_2.
\end{aligned}
$$

后三个分子模9分别为 $s(y),4s(y),-2s(y)$。所以闭环留下的是一条九值边界约束，而不是九条永远隐藏的内部线程。

## 35. 相位校验与边界熵亏损

令 $q=p^r$，$G=(\mathbb Z/q\mathbb Z)^d$，并定义

$$
Z_B=\ker(B^{\mathsf T}\bmod q).
$$

### theorem 35.1 合法边界的相位校验

$$
\boxed{
\mathbf1_{\operatorname{im}B}(y)
=\frac1{|Z_B|}\sum_{z\in Z_B}
\exp\left(\frac{2\pi i}{q}z^{\mathsf T}y\right).
}
$$

**证明。** 若 $y=Bx$，所有相位均为1。若 $y$ 不在像中，有限群字符对偶性给出一个 $z\in Z_B$ 使相位非平凡；把求和指标整体平移该 $z$，总和乘上一个不等于1的因子，故只能为零。证毕。 $\square$

这把“边界合法”写成全部指定相位校验一致；它是编码合法性判据，不是一般整数的素数标签。

### proposition 35.2 有限相干态的边界谱

明确选择有限 Hilbert 空间和等权相干叠加，令

$$
|\Psi_B\rangle=\frac1{\sqrt{|G|}}\sum_{x\in G}|x\rangle|Bx\rangle.
$$

边界约化态为

$$
\rho_\partial=\frac{|\ker B|}{|G|}\sum_{y\in\operatorname{im}B}|y\rangle\langle y|,
$$

所以

$$
\boxed{S(\rho_\partial)=\log|G|-\log|\ker B|.}
$$

每个实际边界标签有同样多的内部原像，故偏迹后的非零本征值相等。对方阵而言 $|\ker B|=|\operatorname{coker}B|$，于是同一个整数缺陷同时给出内部混同、边界约束和相对于满边界空间的熵亏损。

## 36. 记录容量与线性记录的分界

### theorem 36.1 任意记录的最小容量

考虑联合编码 $x\mapsto(Bx,\eta(x))$。在有限精度层，任意记录使其单射时都满足

$$
\boxed{|\mathcal R|\ge|\ker B|.}
$$

这个界可达到：逐个给每个边界纤维编号即可。

量子计算基版本可写成

$$
V|x\rangle=|Bx\rangle|\eta(x)\rangle.
$$

同一纤维内的环境态必须正交，因此环境维数也至少为 $|\ker B|$；该构造保持任意叠加而不复制未知态。

### theorem 36.2 加法记录的容量下界

设 $UBV=\operatorname{diag}(s_1,\ldots,s_d)$，固定素数 $p$，令

$$
 b_p=\#\{i:p\mid s_i\}.
$$

若 $\eta:G_r\to H$ 是有限交换群上的加法同态，且 $x\mapsto(B_rx,\eta(x))$ 单射，则

$$
\boxed{|H|\ge p^{r b_p}.}
$$

**证明。** 在 Smith 坐标中取所有 $p\mid s_i$ 的坐标所成的子群 $W\cong(\mathbb Z/p^r\mathbb Z)^{b_p}$。若 $\eta|_W$ 有非零核，则其有限 $p$-群核含有一个非零、被 $p$ 消去的元素；该元素同时属于 $\ker B_r$，与联合编码单射矛盾。因此 $\eta|_W$ 必须单射，得到 $|H|\ge|W|$。直接记录这些坐标可达此界。证毕。 $\square$

这给出一个编码分界：任意非线性记录只需区分当前纤维，而加法记录必须承载整条有缺陷坐标。进位正是后者压缩为前者所需要的非线性结构。

对三节点环、$r\ge2$，有 $|\ker B_r|=9$ 且 $b_3=1$，所以任意记录最少9个值，而加法记录至少 $3^r$ 个值。一份达到九值下界的记录为

$$
\eta_r(x)=\left\lfloor\frac{[x_2]_{3^r}}{3^{r-2}}\right\rfloor\in\{0,\ldots,8\}.
$$

同一边界纤维内的差异是 $3^{r-2}t(4,-2,1)$。该记录一般不是加法同态；这正是进位的作用。

## 37. 缺陷的递归拼接是扩张

### theorem 37.1 顺序边界映射的短正合列

若满秩整数映射先后为 $B_1$、$B_2$，整体为 $B_2B_1$，则

$$
\boxed{
0\longrightarrow\mathcal D_{B_1}
\overset\iota\longrightarrow\mathcal D_{B_2B_1}
\overset\pi\longrightarrow\mathcal D_{B_2}
\longrightarrow0,
}
$$

其中 $\iota([v])=[B_2v]$，$\pi([w])=[w]$。$B_2$ 的整数单射性给出 $\iota$ 的单射性，$\ker\pi$ 正好是 $\iota$ 的像。因此

$$
|\mathcal D_{B_2B_1}|=|\mathcal D_{B_1}|\,|\mathcal D_{B_2}|,
$$

但一般没有自然直和分解。

例如

$$
B_1=\begin{pmatrix}p&0\\0&1\end{pmatrix}.
$$

若 $B_2=B_1$，则整体缺陷为 $\mathbb Z/p^2\mathbb Z$；若 $\widetilde B_2=\operatorname{diag}(1,p)$，则整体缺陷为 $(\mathbb Z/p\mathbb Z)^2$。二者都有 $p^2$ 个类别，但前者需要两级恢复精度，后者只需一级。接续关系决定了缺陷深度。

## 38. Fibonacci 周期闭合自然产生素数方向

令

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},
\qquad M^2=M+I,
$$

并定义 $t$ 步闭合边界映射

$$
B_t=M^t-I,
\qquad
\mathcal D_t=\mathbb Z^2/(M^t-I)\mathbb Z^2.
$$

若 $L_t=\operatorname{tr}(M^t)$ 为 Lucas 数，则

$$
\boxed{\det(M^t-I)=1+(-1)^t-L_t.}
$$

### theorem 38.1 偶数步闭合缺陷分解

对 $m\ge1$，有

$$
\boxed{
\mathcal D_{2m}\cong
\begin{cases}
(\mathbb Z/L_m\mathbb Z)^2,&m\text{ 奇};\\[1mm]
\mathbb Z/F_m\mathbb Z\oplus\mathbb Z/(5F_m)\mathbb Z,&m\text{ 偶}.
\end{cases}}
$$

**证明。** 令 $X=M^m$。当 $m$ 奇时，$X-X^{-1}=L_mI$，故

$$
M^{2m}-I=L_mX,
$$

而 $X$ 整数可逆，Smith 因子为 $(L_m,L_m)$。当 $m$ 偶时，利用 $M^m=F_mM+F_{m-1}I$ 以及 $L_m=F_m+2F_{m-1}$，得到

$$
M^{2m}-I=F_mM^m(2M-I).
$$

矩阵 $2M-I$ 的 Smith 因子为 $(1,5)$，故结论为 $(F_m,5F_m)$。证毕。 $\square$

例如 $t=4$ 给出 $\mathbb Z/5\mathbb Z$，$t=5$ 给出 $\mathbb Z/11\mathbb Z$，$t=6$ 给出 $(\mathbb Z/4\mathbb Z)^2$，$t=8$ 给出 $\mathbb Z/3\mathbb Z\oplus\mathbb Z/15\mathbb Z$，$t=10$ 给出 $(\mathbb Z/11\mathbb Z)^2$。

这些素数方向只来自统一矩阵 $M$ 的周期闭合和整数可实现性，不是预先写入的素数标签。更一般地，对任意素数 $p$，有限群 $\operatorname{GL}_2(\mathbb F_p)$ 中的 $M\bmod p$ 有有限阶，故某个 $t$ 满足 $M^t\equiv I\pmod p$；于是 $p$ 必作为某个闭合缺陷的算术方向出现。这不要求该素数本身是 Fibonacci 数。

## 39. 缺陷精度曲线与跨尺度几何

对 Smith 因子的 $p$-进指数 $\nu_i=v_p(s_i)$，定义

$$
\boxed{h_r=\log_p|\ker(B\bmod p^r)|=\sum_i\min(r,\nu_i),\qquad h_0=0.}
$$

则

$$
\boxed{h_r-h_{r-1}=\#\{i:\nu_i\ge r\},}
$$

以及

$$
\boxed{(h_r-h_{r-1})-(h_{r+1}-h_r)=\#\{i:\nu_i=r\}.}
$$

逐项检查 $\min(r,\nu_i)$ 即得。故整条有限精度亏损曲线恢复

$$
\mathcal D_{B,p}\cong\bigoplus_i\mathbb Z/p^{\nu_i}\mathbb Z.
$$

这里总混同量 $\sum_i\min(r,\nu_i)$、最坏恢复滞后 $\max_i\nu_i$ 和有缺陷方向数 $\#\{i:\nu_i>0\}$ 是三个不同量；一个熵值不能决定另外两个。

## 40. 本批统一结论与边界

同一离散边界系统现在由一个共同对象连接：

$$
\boxed{
\text{局部递归与闭合矩阵}
\longrightarrow
\text{整数缺陷群 }\mathcal D_B
\longrightarrow
\text{有限层核与余核}
\longrightarrow
\text{相位校验、熵亏损与记录容量}
\longrightarrow
\text{跨尺度恢复与 Fibonacci 素数方向}.
}
$$

核描述当前边界看不见什么，余核描述哪些形式边界不能任意出现；完整相容极限可以消除前者，却保留后者。最短记录只需区分边界纤维，加法记录则可能必须保存整个有缺陷坐标；缺陷的顺序拼接形成群扩张，不能只按总数量相加。Fibonacci 递归的周期闭合还会自然产生素数方向，因此素数层可以来自关系而不来自标签。

本批没有声称缺陷群只由图拓扑决定、量子相位校验等同于一般判素、有限层熵公式自动给出物理 RT、或 $p$-进极限就是物理空间。新增 Lean 接口、任意网络的统一量子实现、局部门成本和现实物理桥梁均保持 open；有限核验也不替代 Lean 编译和冻结。

本批状态：纯理论追加，保留上述矩阵、模数、态、边界分割和精度条件。

## 追加锚（本行以下为增补区）

## 41. 缺陷扩张何时分裂

第 37 节给出的短正合列保留了顺序信息，但只知道三个群的大小还不能判断它是否是直和。下面给出一个直接的整数矩阵判据。

### definition 41.1 分裂截面

对满秩整数矩阵 $B_1,B_2\in\operatorname{Mat}_d(\mathbb Z)$，记第 37 节的商群序列为

$$
0\longrightarrow\mathcal D_{B_1}
\overset\iota\longrightarrow\mathcal D_{B_2B_1}
\overset\pi\longrightarrow\mathcal D_{B_2}
\longrightarrow0.
$$

称它分裂，是指存在群同态截面 $\sigma$ 满足

$$
\pi\circ\sigma=\operatorname{id}_{\mathcal D_{B_2}}.
$$

这一定义只涉及整数格商，不涉及 Hilbert 空间或物理子系统。

### theorem 41.2 矩阵提升判据

上述序列分裂，当且仅当存在整数矩阵 $S,A,C$ 使

$$
\boxed{
S-I=B_2A,
\qquad
SB_2=B_2B_1C.
}
$$

**证明。** 若有截面，取标准基在 $\mathcal D_{B_2}$ 中的整数代表，并把其像提升为 $S$ 的各列。截面在商 $\mathcal D_{B_2}$ 上为恒等，正好给出 $S-I=B_2A$。为了使这个列映射不依赖代表 $w$，每个 $B_2z$ 都必须被送进 $B_2B_1\mathbb Z^d$，等价于存在 $C$ 使 $SB_2=B_2B_1C$。

反过来，令 $\sigma([w])=[Sw]$。第一式保证 $\pi\sigma([w])=[w]$，第二式保证它在 $w$ 换成 $w+B_2z$ 时良定义。证毕。 $\square$

这个判据是一个有限的整数可解性问题；可用 Hermite 或 Smith 变换检验。它比比较 $|\det B_1|$、$|\det B_2|$ 或熵值更强。

### corollary 41.3 对角层的 CRT 分裂

令

$$
B_1=\operatorname{diag}(a_1,\ldots,a_d),
\qquad
B_2=\operatorname{diag}(b_1,\ldots,b_d),
$$

其中 $a_i,b_i>0$。则第 37 节的序列分裂，当且仅当

$$
\boxed{\gcd(a_i,b_i)=1\quad\text{对每个 }i.}
$$

充分性是每个坐标上的 CRT 截面相加。必要性可逐坐标检验：总序列是这些坐标扩张的直和；若整体有截面，把第 $i$ 个商坐标嵌入商群，再投影到第 $i$ 个总群坐标，便得到该坐标扩张的截面。因此若 $p\mid a_i$ 且 $p\mid b_i$，坐标扩张

$$
0\longrightarrow\mathbb Z/a_i\mathbb Z
\longrightarrow\mathbb Z/(a_ib_i)\mathbb Z
\longrightarrow\mathbb Z/b_i\mathbb Z
\longrightarrow0
$$

的 $p$-部分含有不可分裂的循环因子，矛盾。故整体也不分裂。证毕。 $\square$

例如，连续两次压同一方向的 $\operatorname{diag}(5,1)$ 得到

$$
\mathcal D\cong\mathbb Z/25\mathbb Z,
$$

而先压 $\operatorname{diag}(5,1)$、再压 $\operatorname{diag}(1,5)$ 得到

$$
\mathcal D\cong(\mathbb Z/5\mathbb Z)^2.
$$

两者都有 25 个缺陷类别，但前者把两层缺陷合并成两级深度，后者保持两个独立的一层方向。

### theorem 41.4 Fibonacci 偶步闭合的分裂边界

对正偶数 $m\ge2$，令

$$
B_1=2M-I,
\qquad
B_2=F_mM^m.
$$

则 $B_2B_1=M^{2m}-I$，并且第 38 节的扩张

$$
0\longrightarrow\mathbb Z/5\mathbb Z
\longrightarrow\mathcal D_{2m}
\longrightarrow(\mathbb Z/F_m\mathbb Z)^2
\longrightarrow0
$$

分裂，当且仅当

$$
\boxed{\gcd(F_m,5)=1.}
$$

**证明。** 因为 $M^m$ 是整数可逆矩阵，$\mathcal D_{B_2}\cong(\mathbb Z/F_m\mathbb Z)^2$。第 38 节给出总群的 Smith 因子 $(F_m,5F_m)$。

若 $\gcd(F_m,5)=1$，有限交换群的互素初等部分给出一个截面；等价地，$\mathbb Z/(5F_m)\cong\mathbb Z/5\oplus\mathbb Z/F_m$，于是总群与子群嵌入均可按 5-部分和其互补部分分解。

若 $5\mid F_m$，写 $v_5(F_m)=a\ge1$。总群的 5-部分为

$$
\mathbb Z/5^a\mathbb Z\oplus\mathbb Z/5^{a+1}\mathbb Z,
$$

而分裂所需的 5-部分应为

$$
\mathbb Z/5\mathbb Z\oplus(\mathbb Z/5^a\mathbb Z)^2.
$$

两者的循环因子不同，故不可能分裂。证毕。 $\square$

因此 $m=4,6$ 的扩张分裂，而 $m=10$（$F_{10}=55$）不分裂。这个判断来自缺陷扩张的 5-初等结构，不是来自总熵或总类别数。

## 42. 自治记录塔的容量下界

第 36 节分别优化每一个精度层的记录容量，但“每层最优”不自动给出一套能跨层运行的记录。下面把记录只依赖记录本身的额外要求单独写出。

固定素数 $p$，令 $X_r=(\mathbb Z/p^r\mathbb Z)^d$，并令 $\pi_r:X_{r+1}\to X_r$ 是自然约化。取 Smith 分解

$$
UBV=\operatorname{diag}(s_1,\ldots,s_d),
$$

其中 $U,V$ 为整数可逆矩阵。设

$$
I_p=\{i:p\mid s_i\},
\qquad b_p=|I_p|.
$$

### definition 42.1 跨层记录契约

在每层选择有限记录集 $R_r$ 与函数 $\eta_r:X_r\to R_r$，要求联合编码

$$
E_r(x)=(B_rx,\eta_r(x))
$$

在整个 $X_r$ 上单射。若还存在只看记录的转移

$$
\rho_r:R_{r+1}\to R_r
$$

满足

$$
\boxed{\rho_r\circ\eta_{r+1}=\eta_r\circ\pi_r,}
$$

则称这是一套自治记录塔。这里明确禁止把细层边界 $B_{r+1}x$ 偷渡给 $\rho_r$。

### theorem 42.2 自治记录塔的尖锐下界

任意自治记录塔都满足

$$
\boxed{|R_r|\ge p^{rb_p}.}
$$

这个界可以达到：在 Smith 坐标中记录所有满足 $p\mid s_i$ 的坐标，并按模 $p^r$ 约化记录。

**证明。** 令 $W_r$ 为 Smith 坐标中 $I_p$ 个坐标的子群，再经 $V$ 变回原坐标。先看 $r=1$。对 $W_1$ 中任意两个元素，$B_1$ 都为零；联合编码单射迫使 $\eta_1$ 在 $W_1$ 上单射。

归纳设 $\eta_{r-1}$ 在 $W_{r-1}$ 上单射。若 $x,x'\in W_r$ 且 $\eta_r(x)=\eta_r(x')$，自治关系给出

$$
\eta_{r-1}(\pi_{r-1}x)=\eta_{r-1}(\pi_{r-1}x').
$$

归纳假设说明 $x-x'=p^{r-1}w$，其中 $w\in W_1$。由于 $p\mid s_i$ 对 $i\in I_p$，有 $B_rx=B_rx'$。再用 $E_r$ 的单射性，得到 $x=x'$。故 $\eta_r|_{W_r}$ 单射，而 $|W_r|=p^{rb_p}$，所以 $|R_r|$ 至少如此。

达到性来自 $z=V^{-1}x$ 的 $I_p$ 坐标记录：若两个输入的边界和记录相同，非缺陷 Smith 坐标由可逆 $s_i$ 立即相同，缺陷坐标由记录相同，因而输入相同；这些记录按自然约化给出自治转移。证毕。 $\square$

标量例子 $B=[p]$ 说明这个条件确实增加了成本：每层单独只需 $p$ 个记录值，但若强行让记录只依赖记录本身，$|R_r|\ge p^r$。直接记录最高位的 $p$ 值，其粗层更新必须读取细层边界，因而不满足自治契约。

对三节点环，Smith 因子为 $(1,1,9)$。在 $p=3$ 时，逐层最小记录容量是

$$
|\ker B_r|=3^{\min(r,2)},
$$

而自治记录塔要求 $|R_r|\ge3^r$。所以“每层只保留当前隐藏纤维身份”不能直接组成一套只看记录的无限精度编码。

## 43. 联合运输、自治粗化与本批边界

若只要求完整编码的有效像之间存在跨层运输，则给定单射 $E_r$ 可以在有效像上定义

$$
\widehat\pi_r=E_r\circ\pi_r\circ E_{r+1}^{-1}.
$$

这个运输可以同时读取边界和记录；它与第 34 节的进位修正属于同一类联合操作。它不推出第 42 节的自治记录映射 $\rho_r$。

因此，跨尺度理论至少有三种不同的资源合同：

$$
\boxed{
\begin{aligned}
\text{层级合法性}:&\quad\text{提升障碍是否为零};\\
\text{联合无损运输}:&\quad\text{边界与记录一起是否可逆};\\
\text{自治记录粗化}:&\quad\text{记录是否能脱离细层边界独立更新}.
\end{aligned}}
$$

它们的容量和深度结论不同，不能用同一个熵值替代。扩张是否分裂由第 41 节的整数商决定；自治记录的成本由第 42 节的缺陷方向数和精度决定；联合运输还要保留具体的进位和端口接续。

本批仍然是纯理论追加。矩阵判据、Smith 因子比较和记录塔下界尚未在仓库中完成 Lean 编译，也没有声称由此得到固定局域门深度、量子态的普遍因子化或现实物理中的时间、曲率和全息定律。有限枚举只用于检查给出的反例和小阶实例；任意网络的实现成本与物理解释保持 open。

## 追加锚（第 43 节后）

## 44. 时间采样边界与共同步长

在组成状态 $x=(a,b)^{\mathsf T}\in(\mathbb Z/n\mathbb Z)^2$ 上，令

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},
\qquad \varepsilon(a,b)=b,
\qquad r_t(x)=\varepsilon(M^tx)=F_ta+F_{t+1}b.
$$

固定同一来源的时刻集合

$$
\mathcal T=\{t_0<t_1<\cdots<t_{m-1}\},\qquad m\ge2,
$$

定义采样边界 $O_{\mathcal T}(x)=(r_{t_0}(x),\ldots,r_{t_{m-1}}(x))$。时刻标签属于边界数据；不带来源和时刻的边缘读数不能直接视为同一编码。

### theorem 44.1 两个时刻的行列式

对 $s<t$，有

$$
\boxed{\det\begin{pmatrix}F_s&F_{s+1}\\F_t&F_{t+1}\end{pmatrix}=(-1)^{s+1}F_{t-s}.}
$$

**证明。** 令 $\ell_t=(F_t,F_{t+1})=\varepsilon M^t$。把两行同时右乘 $M^{-s}$ 后变为 $\ell_0,\ell_{t-s}$；前者行列式为 $-F_{t-s}$，再乘 $\det(M^s)=(-1)^s$ 即得。证毕。 $\square$

因此两次读数在模 $n$ 下完整恢复，当且仅当 $\gcd(n,F_{t-s})=1$。

### theorem 44.2 任意有限采样的 Smith 缺陷

令 $g(\mathcal T)=\gcd(t_1-t_0,\ldots,t_{m-1}-t_0)$，并令 $H_{\mathcal T}$ 为 $O_{\mathcal T}$ 的整数矩阵。其非零 Smith 因子为

$$
\boxed{1,\ F_{g(\mathcal T)}.}
$$

所以

$$
\boxed{|\ker(O_{\mathcal T}\bmod n)|=\gcd(n,F_{g(\mathcal T)})},
$$

且 $O_{\mathcal T}\bmod n$ 单射，当且仅当 $\gcd(n,F_{g(\mathcal T)})=1$。

**证明。** 以 $M^{t_0}x$ 为新坐标后，第一行是 $(0,1)$；对其他行减去其第二坐标倍的第一行，得到 $(F_{t_i-t_0},0)$。这些数的最大公因数是 $F_g$，使用强整除律 $\gcd(F_u,F_v)=F_{\gcd(u,v)}$。行列变换在模 $n$ 下可逆，故核大小为 $\gcd(n,F_g)$。证毕。 $\square$

当边界有 $m$ 个坐标时，整数余核还包含自由相容约束：

$$
\operatorname{coker}H_{\mathcal T}\cong\mathbb Z^{m-2}\oplus\mathbb Z/F_g\mathbb Z.
$$

有限挠部分 $\mathbb Z/F_g\mathbb Z$ 才是时间采样产生的算术缺陷。增加同一步格内的读数不一定减少它；必须改变共同步长。

### proposition 44.3 三读的互补恢复

取 $n=255=3\cdot5\cdot17$ 与 $\mathcal T=\{0,4,9\}$。三次读数为

$$
 r_0=b,\qquad r_4=3a+5b,\qquad r_9=34a+55b.
$$

任意两次读数的核大小分别为 $3,17,5$，但 $g(\mathcal T)=1$，三次合起来单射，并且

$$
\boxed{b=r_0,\qquad a=r_9-11r_4.}
$$

这是互补素数方向的联合恢复；没有按输入是否为素数改变编码。

## 45. 粗时钟闭合与细时钟失败

固定 $g=g(\mathcal T)$，令 $u_j=r_{t_0+jg}(x)$，并记 $L_g=\operatorname{tr}(M^g)$。Cayley–Hamilton 关系给出

$$
\boxed{u_{j+2}=L_g u_{j+1}-(-1)^g u_j.}
$$

### theorem 45.1 采样边界实现粗时钟行为商

在有限模状态空间上，$O_{\mathcal T}(x)=O_{\mathcal T}(y)$，当且仅当

$$
 r_{t_0+jg}(x)=r_{t_0+jg}(y)\quad\text{对所有 }j\ge0.
$$

**证明。** 定理 44.2 将采样核化为 $b=0,F_ga=0$；而 $r_{t_0}$ 与 $r_{t_0+g}$ 具有同一核。上面的二阶递推由这两项决定全部粗时钟读数。反向蕴含显然。证毕。 $\square$

### theorem 45.2 非零采样核不能独立承载一步细时钟

若 $\ker O_{\mathcal T}\ne0$，不存在函数 $\Phi$ 使 $O_{\mathcal T}(Mx)=\Phi(O_{\mathcal T}(x))$ 对所有 $x$ 成立。

**证明。** 若存在，$K=\ker O_{\mathcal T}$ 必须在 $M$ 下稳定。对 $z\in K$，已有 $r_{t_0}(z)=0$，稳定性又给出 $r_{t_0+1}(z)=0$。相邻两行行列式为 $\pm1$，故 $z=0$，矛盾。证毕。 $\square$

例如模3有 $M^4=2I$。每四步读取一次只看到 $b,2b,b,2b,\ldots$，但 $(0,0)$ 与 $(1,0)$ 的一步读数分别为 $0$ 与 $1$。粗时钟闭合因此不等于细时钟闭合。

## 46. 时间切片的四端口谱

假设四个互异时刻的联合读数在 $V=(\mathbb Z/n\mathbb Z)^2$ 上单射，并在每个端口使用 $\mathbb C^n$，定义等权相干态

$$
|\Psi_{\mathcal T,n}\rangle=\frac1n\sum_{x\in V}|r_{t_0}(x),r_{t_1}(x),r_{t_2}(x),r_{t_3}(x)\rangle.
$$

把端口分成两对 $A|B$，两侧时刻间隔为 $d_A,d_B$，并令 $k_A=\gcd(n,F_{d_A})$、$k_B=\gcd(n,F_{d_B})$。

### theorem 46.1 二分的平坦谱

约化态的非零谱平坦，Schmidt 秩与熵为

$$
\boxed{R_{A|B}=\frac{n^2}{k_Ak_B},\qquad S(A)=2\log n-\log k_A-\log k_B.}
$$

**证明。** 两侧读数核分别为 $K_A,K_B$，大小为 $k_A,k_B$；联合单射给出 $K_A\cap K_B=0$。按 $K_A+K_B$ 的陪集分块，每块内的相干和分解成一侧只随另一侧核参数变化的乘积向量；不同陪集的两侧标签支撑正交。块数为 $n^2/(k_Ak_B)$，故谱平坦且熵为秩的对数。证毕。 $\square$

连续四次采样给出 $(u,v,u+v,u+2v)$，即本卷已有的 Fibonacci 四端口态；它在且仅在 $n$ 为奇数时为完美张量。反例 $n=27,\mathcal T=\{0,1,4,5\}$、分割 $\{0,4\}|\{1,5\}$ 有 $k_A=k_B=3$，故秩为 $81$、熵为 $4\log3$，比 $2\log27=6\log3$ 少 $2\log3$。

## 47. 观察方向的周期与两两互补数量

对素数 $p$，令 $z(p)=\min\{d\ge1:p\mid F_d\}$。由于 $M^d=F_{d-1}I+F_dM$ 且 $M$ 模 $p$ 不是标量，

$$
 p\mid F_d\iff M^d\text{ 模 }p\text{ 是标量矩阵}.
$$

### theorem 47.1 两两可恢复时刻的最大规模

固定 $n\ge2$，在本固定读数族中，要求任意两份时刻读数都能模 $n$ 恢复来源，则

$$
\boxed{m_{\max}(n)=\min_{p\mid n}z(p).}
$$

**证明。** 取达到最小值的素因子 $p$。超过 $z(p)$ 个时刻时，两个标签模 $z(p)$ 相同，差值的 Fibonacci 数被 $p$ 整除，不能恢复。反过来取连续标签 $0,1,\ldots,m-1$；所有非零差值小于每个 $z(p)$，所以对应 Fibonacci 数不被 $n$ 的素因子整除。证毕。 $\square$

例如 $z(2),z(3),z(5),z(7),z(11),z(13)=(3,4,5,8,10,7)$，完整矩阵周期分别为 $(3,8,20,16,10,28)$；故 $m_{\max}(5040)=3$，而 $m_{\max}(315)=4$。这些是固定 Fibonacci 读出族的结论。

## 48. $p$-进观察距离与恢复滞后

对素数 $p$ 定义

$$
 d_p(s,t)=\begin{cases}0,&s=t,\\p^{-v_p(F_{|s-t|})},&s\ne t.\end{cases}
$$

### theorem 48.1 超度量与精度参数

$d_p$ 是平移不变超度量。若 $z(p)$ 如上并令 $e_p=v_p(F_{z(p)})$，则对奇素数 $p$

$$
 v_p(F_d)=\begin{cases}0,&z(p)\nmid d,\\e_p+v_p(d/z(p)),&z(p)\mid d,\end{cases}
$$

并有

$$
 z(p^r)=z(p)p^{\max(0,r-e_p)}.
$$

**证明。** 若 $p^q$ 同时整除两个差值的 Fibonacci 数，则相应矩阵幂是可逆标量矩阵；相乘或取逆给出第三个差值的同样整除性，得到超三角不等式。赋值公式是奇素数 Fibonacci 赋值提升定理（见 Lengyel, *The Order of the Fibonacci and Lucas Numbers*, 1995）；二进通道不纳入本式。证毕。 $\square$

对间隔 $g$ 的采样，Smith 因子 $F_g$ 还给出精度滞后 $\lambda_p(g)=v_p(F_g)$。例如 $F_{12}=144=9\cdot16$，由 $r_0=b,r_{12}=144a+233b$ 可在合法边界上按

$$
 a\equiv16^{-1}\frac{r_{12}-233r_0}{9}\pmod{3^r}
$$

恢复 $a$ 到模 $3^r$；边界需要多两位三进精度。参数 $e_p$ 不统一设为1，$p=2$ 需单独处理。

## 49. 更高阶递推与观察优化

对 $k$-bonacci 递推矩阵 $C_k$ 和基本读数 $\varepsilon_k$，采样矩阵为

$$
H_{\mathcal T}=\begin{pmatrix}\varepsilon_kC_k^{t_0}\\\vdots\\\varepsilon_kC_k^{t_{m-1}}\end{pmatrix}.
$$

若其满列秩 Smith 因子为 $s_1,\ldots,s_k$，则

$$
\boxed{|\ker(H_{\mathcal T}\bmod n)|=\prod_i\gcd(n,s_i)}.
$$

因此完整恢复等价于所有 $k\times k$ 子式的最大公因数与 $n$ 互素。二阶 Fibonacci 的额外简化来自强整除律把这些子式压缩为一个 $F_g$。

给定允许时刻集合 $\mathcal A$ 与成本 $c(\mathcal T)$，最小完整恢复问题是

$$
\min_{\mathcal T\subseteq\mathcal A}c(\mathcal T)
\quad\text{subject to}\quad
\gcd(n,F_{g(\mathcal T)})=1.
$$

若要求任意两两时刻都可恢复，则对所有时刻对施加 $\gcd(n,F_{|t_i-t_j|})=1$；若要求量子四端口完美性，还需联合单射和对应二分的 $k_A,k_B$ 条件。这个优化保持关系和时钟标签，不把素性答案编码进端口。

## 50. 时间采样批次的边界

第 44–49 节把递归时刻、边界缺陷、粗细时钟闭合和四端口谱放在同一观察矩阵上。它们仍是有限算术与明确相干态的结论：没有把 $p$-进距离称为物理距离，也没有把递归步称为真实时间；奇素数赋值公式、Smith 理论和高阶递推的统一物理解释保持 open。

## 追加锚（时间采样批次后）

## 51. 共同联合纤维与边界下降

最新三输出树反例显示：两个边界分别足够，不代表它们同时压缩后仍然足够。这里的失败可以发生在一棵无环关系图上，因为压缩后的联合纤维本身可能断开。

设 $D\subseteq X\times Y$ 是合法来源关系，任务为 $F:D\to O$，两侧编码为 $\alpha:X\to A$、$\beta:Y\to B$。定义联合纤维

$$
D_{a,b}=D\cap(\alpha^{-1}(a)\times\beta^{-1}(b)).
$$

把每个非空 $D_{a,b}$ 看成二部图：顶点是其中出现的 $x$、$y$，合法来源是带任务标签的边。

### theorem 51.1 纤维分量判据

若 $\alpha,\beta$ 各自在保持另一侧原始输入时是单侧充分的，则 $F$ 在每个 $D_{a,b}$ 的每个连通分量上为常数；联合解码器存在，当且仅当同一纤维的所有连通分量要求相同任务值。

**证明。** 两条边若共享 $y$，由行侧单侧充分性任务值相同；若共享 $x$，由列侧单侧充分性任务值相同。沿路径传播即得前半。联合解码器只看到 $(a,b)$，所以后半是良定义性的充要条件。证毕。 $\square$

因此“每个联合纤维连通”是对任意单侧充分任务都足够的条件；整个来源图连通或无环都不能替代它。最新树反例的 $(0,0)$ 消息纤维含 $(0,0)$ 与 $(2,2)$ 两条互不相接的边，正是分量身份丢失。

### theorem 51.2 固定局部码的最小补充记录

允许记录 $\eta:D\to R$ 访问共同来源。使 $F(x,y)$ 可由 $(\alpha(x),\beta(y),\eta(x,y))$ 恢复的最小记录字母数为

$$
\boxed{|R|_{\min}=\max_{D_{a,b}\ne\varnothing}|F(D_{a,b})|.}
$$

**证明。** 每个联合纤维中要求 $r$ 种结果时至少需 $r$ 个记录值；各纤维可重复使用同一套标签编号达到最大值。证毕。 $\square$

## 52. 邻居编码会改变边界成本

固定列编码 $\beta$，若存在合法 $(x,y),(x',y')$ 使 $\beta(y)=\beta(y')$ 且 $F(x,y)\ne F(x',y')$，就在行集合上连边 $x\mathrel{\#_\beta}x'$。

### theorem 52.1 固定对方编码后的最小行消息数

假设 $\beta$ 自身单侧充分，则

$$
\boxed{\min_\alpha|\operatorname{im}\alpha|=\chi(G_X^\beta).}
$$

**证明。** 正确行码必须给冲突图相邻顶点不同消息；反过来合法着色不会让同一联合消息对要求不同输出，故可定义联合解码器。证毕。 $\square$

树反例的未压缩冲突图是路径 $0-1-2$，两种颜色足够；将列 $0,2$ 合并后冲突图成为 $K_3$，行端必须使用三种消息。因此局部最小容量依赖相邻区域采用的编码。

## 53. 线性联合下降障碍群

令 $X,Y$ 为有限交换群，$D\le X\oplus Y$ 为加法子群，$\alpha:X\to A$、$\beta:Y\to B$ 为同态。记 $K_X=\ker\alpha$、$K_Y=\ker\beta$，并定义

$$
E=D\cap(K_X\oplus K_Y),\quad E_X=D\cap(K_X\oplus\{0\}),\quad E_Y=D\cap(\{0\}\oplus K_Y).
$$

定义联合下降障碍

$$
\boxed{\mathfrak J(D;\alpha,\beta)=E/(E_X+E_Y).}
$$

### theorem 53.1 障碍群是联合纤维的分量群

每个非空联合消息纤维在选定基点后，其连通分量集合与 $\mathfrak J(D;\alpha,\beta)$ 同构；不选基点时是该群作用的同型陪集集合。

**证明。** 联合纤维是 $E$ 的陪集。共享同一左端点的移动差异属于 $E_Y$，共享同一右端点的移动差异属于 $E_X$；沿路径恰能生成 $E_X+E_Y$，所以分量是其陪集。证毕。 $\square$

### theorem 53.2 加法任务的完整障碍

若 $F:D\to Z$ 是群同态，则两侧单独充分当且仅当 $F(E_X)=F(E_Y)=0$。在此条件下，$F|_E$ 下降为 $\bar F:\mathfrak J\to Z$，并且

$$
\boxed{\text{联合解码存在}\iff\bar F=0,\qquad |R|_{\min}=|\operatorname{im}\bar F|=|F(E)|.}
$$

**证明。** 固定另一侧时的差异正是 $E_X$ 或 $E_Y$；联合消息相同的来源相差 $E$ 中元素，因此联合正确性等价于 $F(E)=0$。任一纤维的任务值是 $F(E)$ 的陪集，记录容量结论随即得到。证毕。 $\square$

所以 $\mathfrak J=0$ 当且仅当所有满足单侧条件的加法任务都能共同下降；若 $\mathfrak J\ne0$，商映射 $D\to D/(E_X+E_Y)$ 给出单侧可行而联合失败的任务。

## 54. Fibonacci 双区域的联合障碍

令 $V=(\mathbb Z/n\mathbb Z)^2$，$r_t(a,b)=F_ta+F_{t+1}b$。两个区域保留完整相邻历史

$$
A_s=(r_s,r_{s+1}),\qquad B_t=(r_t,r_{t+1}),\qquad s<t,
$$

把共同来源关系明确写成

$$
D_{s,t}=\{(A_s(x),B_t(x)):x\in V\}\le V\oplus V.
$$

在这个 $D_{s,t}$ 上，两个局部码分别是 $A_s(x)\mapsto r_s(x)$ 与 $B_t(x)\mapsto r_t(x)$。完整历史各自可逆，但共同压缩只保留 $(r_s,r_t)$。

### theorem 54.1 Fibonacci 双区域障碍

若附加记录的目标是恢复完整来源 $x$（即恒等任务），令 $g=\gcd(n,F_{t-s})$。则

$$
\boxed{\mathfrak J\cong\mathbb Z/g\mathbb Z,\qquad |R|_{\min}=g.}
$$

**证明。** 完整相邻历史可逆，故 $E_X=E_Y=0$。在时刻 $s$ 的可逆坐标中，两个保留读数是 $b_s$ 与 $F_{t-s}a_s+F_{t-s+1}b_s$；其核为 $b_s=0$、$F_{t-s}a_s=0$。它有 $g$ 个元素，且是循环群 $\mathbb Z/g\mathbb Z$。证毕。 $\square$

例如模27取 $s=0,t=4$，三个来源 $(0,0),(9,0),(18,0)$ 都给出 $(r_0,r_4)=(0,0)$。记录 $\eta(a,b)=\lfloor[a]_{27}/9\rfloor$ 用三个值区分它们；增加相邻观察 $r_5$ 也可恢复，因为

$$
 a=5r_5-8r_4,\qquad b=5r_4-3r_5.
$$

同一步格的 $r_0,r_4,r_8,\ldots$ 不会消除这个模3缺陷。

## 55. 经典下降、量子相干与未来行为

经典源标签可恢复，不等于任意量子输入可恢复。$\alpha|00\rangle+\beta|11\rangle$ 丢掉第二份后，其第一份约化态只保留 $|\alpha|^2,|\beta|^2$，丢失相位相干。仓库已有 $T_9$ 的联合进位修正：细层到粗层需要共享低位决定的进位，不能由每条腿独立处理；这与经典分量障碍同形，但量子通道还须保持矩阵单位与外部参考系统，不能用经典计数替代量子恢复证明。

令历史状态为 $h$、动作集合为 $\mathcal A$，完整行为记录为

$$
\mathcal B(h)(w)=\text{操作词 }w\text{ 的合法性、记录与读数}.
$$

联合边界 $Q$ 若要回答指定未来，至少满足

$$
Q(h)=Q(h')\Longrightarrow\mathcal B(h)=\mathcal B(h').
$$

若还要直接在码集上继续更新，则另需

$$
Q(T_ah)=\widehat T_a(Q(h)),
$$

等价于 $Q(h)=Q(h')\Rightarrow Q(T_ah)=Q(T_ah')$。第一条件保证行为可恢复，第二条件保证摘要本身闭合；完整行为商按定义满足后者，具体压缩码仍须逐动作证明。

## 56. 共同来源边界对象与本批边界

一个可递归使用的边界不只是局部码列表，而是

$$
\boxed{\mathfrak B=(\text{局部码},\text{合法联合关系},\text{纤维分量记录},\text{相容更新接口}).}
$$

树结构、局部单侧最优和无闭环都不能单独保证联合充分；线性情形的 $\mathfrak J$ 与 Fibonacci 双区域的 $\mathbb Z/\gcd(n,F_{t-s})$ 是可以计算的共同障碍。只有在指定关系、观察和未来操作下，边界纤维内不再残留不同的结果或行为，才可称为共同下降。

这些新增桥接仍未在 Lean 中编译，也没有把经典障碍提升成一般量子网络定理或现实物理全息定律；所需操作、来源域、合法性标记和外部参考系统必须逐项声明。固定半径判素仍未由这些关系推出。

## 追加锚（联合边界批次后）

## 57. 三项素数窗口与非相邻模式

取连续 Fibonacci 位权

$$
F_3=2,\qquad F_4=3,\qquad F_5=5
$$

并只观察这三个位置。按从高到低的顺序写成 $(b_5,b_3,b_2)$，下标表示对应的数值权，施加非相邻条件

$$
b_5b_3=0,\qquad b_3b_2=0.
$$

合法字串及其读数为

$$
\begin{array}{c|c|c}
\text{字串}&\text{选择}&\text{读数}\\ \hline
000&\varnothing&0\\
001&\{2\}&2\\
010&\{3\}&3\\
100&\{5\}&5\\
101&\{2,5\}&7
\end{array}
$$

所以这个窗口的合法非空读数恰为

$$
\boxed{\{2,3,5,7\}.}
$$

### theorem 57.1 三项全素 Fibonacci 窗口的范围

在连续的 Fibonacci 项中，除 $(F_3,F_4,F_5)=(2,3,5)$ 外，不存在另一段三个连续项全部为素数。

**证明。** $F_0=0$、$F_1=F_2=1$ 已排除起始窗口。起点 $n=4$ 时三项包含 $F_6=8$，因而不是全素。对起点 $n\ge5$，三个连续指标中含有一个偶数指标 $2m\ge6$；由 $F_m\mid F_{2m}$ 且 $1<F_m<F_{2m}$，该偶指标对应的 Fibonacci 项为合数。起点 $n=3$ 正好给出 $(2,3,5)$。证毕。 $\square$

这里的素数结论只属于这个指定窗口。一般合法的非相邻 Fib 选择仍可能是合数，例如 $13+2=15$；非相邻规则本身不是普适素数判定器。

## 58. 5040 的四轴与共同成块关联

把四个非空模式记为

$$
A_2=[2],\qquad A_3=[3],\qquad A_5=[5],\qquad A_7=[2+5].
$$

在乘法层固定块的顺序，一个块配置写成

$$
n=2^{a_2}3^{a_3}5^{a_5}7^{a_7}.
$$

这四个数值轴正是已有 5040 寄存器 $P_{5040}=(2,3,5,7)$；`CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md` 的定理 169、212、214 分别给出其容量、局部槽表示和七位置窗口，`ZECKENDORF_EULER_5040.md` 第 2.2 节也给出 60 个状态的独立有限盒描述。这里增加的是它们的共同 Fib 来源解释。

定义三类叶子计数与共同成块数

$$
u=a_2+a_7,\qquad v=a_3,\qquad w=a_5+a_7,\qquad \kappa=a_7.
$$

于是结构记录为

$$
\boxed{\mathcal C(n)=(u,v,w;\kappa).}
$$

### theorem 58.1 叶子计数加关联数的可逆性

在非负整数坐标上，

$$
a_2=u-\kappa,\qquad a_3=v,\qquad a_5=w-\kappa,\qquad a_7=\kappa,
$$

且其合法性条件为

$$
u,v,w,\kappa\ge0,\qquad \kappa\le\min(u,w).
$$

因此

$$
n=2^{u-\kappa}3^v5^{w-\kappa}7^\kappa.
$$

**证明。** 把 $(u,v,w;\kappa)$ 的定义逐项反解即可；代回得到原四个指数，故记录既充分又唯一。两份块列表相乘时四个指数相加，所以 $\mathcal C(nm)=\mathcal C(n)+\mathcal C(m)$。证毕。 $\square$

关联数不是一个预先写入答案的素数标签。它记录 $2$ 与 $5$ 是否在同一合法加法块中共同出现。最小碰撞是

$$
7=[2+5],\qquad 10=[2]\,[5],\qquad
(u,v,w)=(1,0,1)
$$

两者的叶子计数相同，而块关系和数值不同。

在已有容量盒

$$
0\le a_2\le4,\quad0\le a_3\le2,\quad0\le a_5\le1,\quad0\le a_7\le1
$$

中，

$$
5040=2^4 3^2 5\,7,\qquad \mathcal C(5040)=(5,2,2;1).
$$

四种局部模式只确定四个块值，并不单独强制指数 $(4,2,1,1)$。若另加“把 $1$ 到 $7$ 的合法读数全部相乘”的组合规则，则

$$
7!=1\cdot2\cdot3\cdot4\cdot5\cdot6\cdot7
   =2^4 3^2 5\,7=5040,
$$

其中 $4=2\cdot2$、$6=2\cdot3$；这一步是乘法层的额外规则，不是三位非相邻窗口本身的结论。

若另记块总数 $\Omega=a_2+a_3+a_5+a_7$，则 $\kappa=u+v+w-\Omega$；对 5040，这个差为 $9-8=1$。

## 59. 黄金代数中的关联记录

在已有黄金整数环

$$
R=\mathbb Z[\theta]/(\theta^2-\theta-1)
$$

中，沿用范数

$$
\mathcal N(a+b\theta)=a^2+ab-b^2.
$$

四个块可由

$$
1,\qquad \theta,\qquad \theta^2=1+\theta,\qquad 2+\theta
$$

记录；它们的数量读数 $q(a+b\theta)=2a+3b$ 分别为 $2,3,5,7$，而范数分别为 $1,-1,1,5$。

直接有

$$
2+\theta=\theta(2\theta-1),\qquad (2\theta-1)^2=5,\qquad (2+\theta)^2=5\theta^2.
$$

### theorem 59.1 黄金范数恢复共同成块数

定义结构性乘法记录

$$
U(n)=1^{a_2}\theta^{a_3}(\theta^2)^{a_5}(2+\theta)^{a_7}.
$$

则

$$
\boxed{\mathcal N(U(n))=(-1)^{a_3}5^{a_7}.}
$$

特别地，

$$
\boxed{\kappa=a_7=v_5\!\left(|\mathcal N(U(n))|\right).}
$$

**证明。** 范数的乘法性给出

$$
\mathcal N(U(n))=1^{a_2}(-1)^{a_3}1^{a_5}5^{a_7}.
$$

取绝对值再取 5-赋值即可。证毕。 $\square$

对 5040，

$$
U(5040)=\theta^4(2+\theta)=7+11\theta,\qquad \mathcal N(U(5040))=5.
$$

这里 $U(n)$ 是结构记录，不是普通整数 $n$ 的数值表示；$q$ 是标量读出而非环同态，不能只用 $q(U(n))$ 替代四个指数与关联记录。只有在本节有限盒 $a_7\in\{0,1\}$ 且范数记录已取得时，才可进一步写成 $\kappa=(|\mathcal N(U(n))|-1)/4$；一般指数范围仍应使用 $v_5$。

## 60. 60 个因子、48 个叶子纤维与一位补充记录

上述容量盒有

$$
(4+1)(2+1)(1+1)(1+1)=60
$$

个来源状态。投影到三叶计数 $(u,v,w)$ 时，$a_7=0$ 给出 $10$ 个 $(u,w)$ 位置，$a_7=1$ 也给出 $10$ 个位置，两者交集为 $4$ 个位置。再乘以三个 $v$ 值，得到

$$
\boxed{48\text{ 个叶子计数纤维},\qquad 12\text{ 个二元碰撞纤维}.}
$$

因此

$$
60=36+2\times12.
$$

### theorem 60.1 关联位是一位且恰好充分

在上述 60 状态域中，三叶计数的最坏纤维大小为 $2$。补充二元结构记录 $\kappa=a_7\in\{0,1\}$ 后，记录

$$
(u,v,w;\kappa)
$$

对 60 个状态单射；没有补充记录则不能恢复全部状态。

**证明。** $a_7=0$ 与 $a_7=1$ 的四个重叠 $(u,w)$ 位置各产生三个 $v$ 值，故有 12 个大小为二的纤维，其余 36 个为单点。补充 $a_7$ 区分每个重叠纤维并由定理 58.1 反解四个指数。由于 $7$ 与 $10$ 位于同一三叶纤维而不同，零容量记录不可能在所有状态上单射；一位记录达到下界。证毕。 $\square$

因子互补 $d\mapsto5040/d$ 在指数上是

$$
(a_2,a_3,a_5,a_7)\mapsto(4-a_2,2-a_3,1-a_5,1-a_7),
$$

故新坐标按

$$
\boxed{\mathcal C(5040/d)=(5-u,\,2-v,\,2-w;\,1-\kappa).}
$$

这是一份整体反射：关联位翻转的同时，三个叶子计数也反射，不能把补码误说成只翻一位。

若把所有有符号分布写成 60 维向量，三叶计数的 48×60 推送矩阵秩为 48，核维数为 12。这 12 维正对应上述 12 个二元碰撞纤维；它与已有四寄存器边缘观察留下的 51 维联合关联空间（QUANTUM-RH 第31节式（105）–（107）的 Hoeffding/ANOVA 分解）不是同一个核，也不能由维数相等式替代二者的关系。

## 61. 适用域与“关系递归成原子”的边界

在这个四块生成域中，对 $n\ge1$，素性有一个精确但受限的判据：

$$
\boxed{
n\text{ 为素数}
\iff a_2+a_3+a_5+a_7=1
\iff u+v+w-\kappa=1.
}
$$

它只适用于 $n=2^{a_2}3^{a_3}5^{a_5}7^{a_7}$ 的乘法生成域。加入下一项 $13$ 后，合法非相邻选择 $13+2=15$ 已经给出合数，因此不能把当前窗口的四个素数模式推广为所有 Fib 模式的素数判定。

这批结果把层级关系写成了一个具体链条：底层 $2,3,5$ 通过非相邻选择产生块 $7=[2+5]$；在乘法层，四个块成为 $2,3,5,7$ 四根轴；在更粗的三叶观察中，块内共同来源关系又必须以 $\kappa$ 保存。于是“原子”与“关联”可以在相邻层级互换角色，而不能只保留无标签的叶子数量。

这些 5040 桥接仍是有限窗口、有限容量和指定黄金环记录的数学结论；它们尚未作为新增定理在 Lean 中编译，也不推出一般整数的固定半径素性判定。

## 追加锚（Fib–5040 关联批次后）

## 62. 同块关系坐标与有限反演

前面的关联位可以推广为一般的同块记录。令 $A$ 是有限原子位置集，令

$$
\mathcal K\subseteq 2^A
$$

是对取子集封闭的合法块族，并记 $\mathcal K^+=\mathcal K\setminus\{\varnothing\}$。一个无序块多重集由非负整数重数 $(m_S)_{S\in\mathcal K^+}$ 描述。对每个非空合法子集 $T$ 定义

$$
\boxed{y_T=\sum_{\substack{S\in\mathcal K^+\\T\subseteq S}}m_S.}
$$

它记录有多少个块同时包含 $T$ 的全部原子。

### theorem 62.1 同块关系的容斥反演

$$
\boxed{
 m_S=\sum_{\substack{T\in\mathcal K^+\\S\subseteq T}}
 (-1)^{|T|-|S|}y_T.
}
$$

**证明。** 代入 $y_T$ 并交换有限求和，得到

$$
\sum_{U\supseteq S}m_U
 \sum_{S\subseteq T\subseteq U}(-1)^{|T|-|S|}.
$$

由于 $\mathcal K$ 对取子集封闭，区间内的所有 $T$ 都合法；内层和为 $(1-1)^{|U|-|S|}$，只在 $U=S$ 时为1。证毕。 $\square$

也可以从最大块开始递归计算

$$
\boxed{m_S=y_S-\sum_{T\supsetneq S}m_T.}
$$

因此同块关系不是一个新的答案标签，而是一层可递归反演的观察坐标。合法记录还必须满足反演所得的 $m_S$ 全部为非负整数；任意关系计数并不自动来自真实块多重集。

对三原子窗口，$y_{\{2\}}=u$、$y_{\{3\}}=v$、$y_{\{5\}}=w$、$y_{\{2,5\}}=\kappa$，正好恢复第 58 节的四坐标。

## 63. 5040 状态上的联合观察与 $51\to8$

令

$$
X=\{0,\ldots,4\}\times\{0,1,2\}\times\{0,1\}\times\{0,1\}
$$

为 5040 的 60 个指数状态，并定义

$$
C(a_2,a_3,a_5,a_7)=(a_2+a_7,a_3,a_5+a_7).
$$

对有符号分布 $\mu\in\mathbb R^X$，令 $L\mu=C_*\mu$ 为三叶计数的联合分布，令 $\Pi\mu$ 为四个原始指数寄存器的单寄存器边缘。概率分布只是满足非负性和总质量为1的子集；下面的核计算在线性有符号空间中进行。

对 $a=1,2,3,4$、$b=0,1,2$ 定义

$$
\boxed{D_{a,b}=\delta_{(a,b,1,0)}-\delta_{(a-1,b,0,1)}.}
$$

### theorem 63.1 三叶观察的完整核

$$
\boxed{\ker L=\operatorname{span}\{D_{a,b}:1\le a\le4,\ 0\le b\le2\},\qquad\dim\ker L=12.}
$$

**证明。** 两个状态的 $C$ 值都是 $(a,b,1)$。这 12 个二点纤维之外，其余 36 个纤维为单点；每个二点纤维恰有一个总量不变方向，且支撑互不相交。证毕。 $\square$

### theorem 63.2 加入单寄存器边缘后的剩余核

$$
\boxed{\dim(\ker L\cap\ker\Pi)=8,}
$$

并且一组基为

$$
\boxed{D_{a,1}-D_{a,0},\qquad D_{a,2}-D_{a,0}\quad(a=1,2,3,4).}
$$

**证明。** 写 $\nu=\sum_{a,b}t_{a,b}D_{a,b}$，并令 $T_a=\sum_{b=0}^2t_{a,b}$。2 寄存器的边缘变化依次为

$$
-T_1,\quad T_1-T_2,\quad T_2-T_3,\quad T_3-T_4,\quad T_4.
$$

故边缘不变当且仅当 $T_1=\cdots=T_4=0$。3 寄存器在每个 $D_{a,b}$ 内抵消，5、7 寄存器的变化也由 $\sum_aT_a$ 决定；所以剩余维数为 $12-4=8$，所列向量逐行给出零和空间的基。证毕。 $\square$

把所有三寄存器边缘记为 $\Pi_3$，则同一有限矩阵的精确秩表为

$$
\begin{array}{c|c|c}
\text{观察}&\text{秩}&\text{核维数}\\ \hline
\Pi&9&51\\
L&48&12\\
(L,\Pi)&52&8\\
\Pi_3&52&8\\
(L,\Pi_3)&60&0
\end{array}
$$

这里的 51 维是原四寄存器边缘观察的核；第 63 节的 12 维是三叶投影的碰撞核，二者不是同一个子空间。$8$ 个额外联合读数可取

$$
\boxed{z_{a,b}=\mathbb E_\mu\left[\kappa\,\mathbf1_{\{C=(a,b,1)\}}\right],\qquad a=1,\ldots,4,\ b=1,2.}
$$

在上述 8 维基上其响应矩阵为 $-I_8$；在已保留 $L$ 与 $\Pi$ 的模型中，少于 8 个独立实线性读数不能恢复全部剩余核。

## 64. Möbius 权重的第四阶关联

定义局部向量

$$
 g_2=(1,-1,0,0,0),\qquad g_3=(1,-1,0),\qquad g_5=g_7=(1,-1).
$$

在 60 个状态上，Möbius 权重恰为

$$
\boxed{\boldsymbol\mu=g_2\otimes g_3\otimes g_5\otimes g_7.}
$$

每个局部向量的分量和为零，所以对任意一个寄存器求和，张量都消失。它属于纯四寄存器关联空间；该空间维数为

$$
(5-1)(3-1)(2-1)(2-1)=8,
$$

与 $51=21+22+8$ 的原 ANOVA/Hoeffding 分解中的最后一层相同，但这里给出的是具体 Möbius 方向，不把数值相同的维数当作子空间相等。

定义两份严格正的概率分布

$$
p_\pm(a)=\frac1{60}\pm\frac{\mu(n(a))}{120}.
$$

因为平方自由状态有 $2^4=16$ 个，

$$
\boxed{\mathbb E_{p_+}\mu=\frac2{15},\qquad
\mathbb E_{p_-}\mu=-\frac2{15}.}
$$

两者所有一、二、三寄存器边缘相同，却给出相反的 Möbius 读数。这是一个有限观察反例：恢复低阶边缘不保证恢复该任务的四阶关联。

更一般地，在平方自由子域上引入形式变量，得到

$$
\mathcal P(x,y,z;t)=(1-x)(1-y)(1-z)(1-xzt).
$$

令 $t=1$ 只适合忘掉关联后的叶子任务；对 Dirichlet 权重必须使用

$$
(x,y,z,t)=\left(2^{-s},3^{-s},5^{-s},(10/7)^s\right),
$$

此时

$$
\boxed{\mathcal P=\prod_{p\in\{2,3,5,7\}}(1-p^{-s}).}
$$

所以关联变量在数量截断或 zeta 权重任务中不能提前抹掉。

## 65. 更高合法块需要更高阶关系

加入位置 $13$ 后，合法块族（在 $2,3,5,13$ 这些位置上）包含 4 个单元素块、4 个二元素块和 1 个三元素块，共 9 个非空块。只看三个互不相邻位置 $2,5,13$，比较

$$
\mathcal A=\{[2+5+13],[2],[5],[13]\},\qquad
\mathcal B=\{[2+5],[2+13],[5+13]\}.
$$

两者每个原子出现两次，每一对出现一次，但三阶关系分别为1和0。按块内求和、块间相乘，它们的数值分别为

$$
20\cdot2\cdot5\cdot13=2600,qquad 7\cdot15\cdot18=1890.
$$

这说明一阶和二阶同块记录不总能恢复三阶关系；而 $[2+13]$ 的读数 $15$ 也说明一般合法块不必是素数。完整块重数仍由第 62 节反演公式恢复，但结构身份与数量相等必须分开保存。

## 66. $7r\leftrightarrow10r$ 的关联边界

令

$$
M_{70}(Y)=\sum_{\substack{r\le Y\\(r,70)=1}}\mu(r),qquad
\Delta_{7,10}(X)=\sum_{\substack{X/10<r\le X/7\\(r,70)=1}}\mu(r).
$$

在截断 $n\le X$ 中，配对 $7r$ 与 $10r$ 的实际贡献为

$$
\mu(7r)\mathbf1_{7r\le X}+\mu(10r)\mathbf1_{10r\le X}
=-\mu(r)\mathbf1_{7r\le X<10r}.
$$

因此它在关联边界区间 $[7r,10r)$ 中暂时存在，实际成对总贡献为 $-\Delta_{7,10}(X)$。

### theorem 66.1 关联边界与 Mertens 判据

对任意 $\alpha>0$，

$$
\boxed{\Delta_{7,10}(X)=O(X^\alpha)
\iff M_{70}(X)=O(X^\alpha).}
$$

因而，使用经典 Mertens 判据时，

$$
\boxed{
\mathrm{RH}
\iff
\forall\varepsilon>0,\quad
\Delta_{7,10}(X)=O_\varepsilon(X^{1/2+\varepsilon}).
}
$$

**证明。** 直接有 $\Delta_{7,10}(X)=M_{70}(X/7)-M_{70}(X/10)$。反向取 $q=7/10$，则

$$
\Delta_{7,10}(7Y)=M_{70}(Y)-M_{70}(qY).
$$

有限回溯给出

$$
M_{70}(Y)=\sum_{j\ge0}\Delta_{7,10}(7q^jY),
$$

因为当 $q^jY<1$ 时计数函数为零。对 $\alpha>0$，该几何级数收敛，得到两个大 $O$ 估计的等价性。

再令 $\mathcal S=\{2^i5^j7^k:i,j,k\ge0\}$。精确卷积恒等式为

$$
M(X)=\sum_{d\mid70}\mu(d)M_{70}(X/d),
$$

$$
M_{70}(X)=\sum_{q\in\mathcal S}M(X/q),
$$

其中第二个和实际上因 $q\le X$ 而有限。对任意 $\alpha>0$，

$$
\sum_{q\in\mathcal S}q^{-\alpha}
=\prod_{p\in\{2,5,7\}}(1-p^{-\alpha})^{-1}<\infty,
$$

故 $M_{70}(X)=O(X^\alpha)$ 与 $M(X)=O(X^\alpha)$ 等价。最后使用经典等价性 $\mathrm{RH}\iff\forall\varepsilon>0, M(X)=O_\varepsilon(X^{1/2+\varepsilon})$。证毕。 $\square$

这里的等价性使用所有实数截断 $X\ge1$；只检查某个离散端点序列并不足以推出它。

## 67. Mellin 响应、Fibonacci 端点与活动密度

对 $\Re s>1$，定义

$$
\mathcal T(s)=s\int_1^\infty\Delta_{7,10}(X)X^{-s-1}\,dX.
$$

绝对收敛时逐个关系对积分，得到

$$
\boxed{
\mathcal T(s)=
\frac{7^{-s}-10^{-s}}
{\zeta(s)(1-2^{-s})(1-5^{-s})(1-7^{-s})}.
}
$$

该公式首先在 $\Re s>1$ 成立，再作为亚纯延拓解释。对 $\Re s>0$，分子 $7^{-s}-10^{-s}$ 与三个因子 $1-p^{-s}$ 均不为零；所以 zeta 在右半平面的零点不会被这个关系滤波器消掉。这只是精确的零点传递陈述，不是 RH 证明。

对 $k\ge2$，$F_{k+1}/F_k\ge3/2>10/7$。因此若 $[7r,10r)$ 在 $F_k$ 端点仍活动，它会在下一端点前结束；但端点序列可能完全漏掉中间区间，例如 $r=13$ 时 $[91,130)\subset(89,144)$。所以第 66 节的等价判据不能只采样 Fibonacci 端点。

令 $N_{\mathrm{live}}(X)$ 统计区间 $X/10<r\le X/7$ 中平方自由且与 70 互素的 $r$。固定模数的平方自由密度为

$$
\frac1{\zeta(2)}\frac23\frac56\frac78=\frac{35}{12\pi^2},
$$

区间长度为 $3X/70$，故

$$
\boxed{N_{\mathrm{live}}(X)=\frac{X}{8\pi^2}+O(\sqrt X).}
$$

若 $N_+$、$N_-$ 按 $\mu(r)=1,-1$ 分开计数，则 $N_++N_-=N_{\mathrm{live}}$、$N_+-N_-=\Delta_{7,10}$。所以

$$
\boxed{
\mathrm{RH}\iff
N_\pm(X)=\frac{X}{16\pi^2}+O_\varepsilon(X^{1/2+\varepsilon})
\quad(\forall\varepsilon>0).
}
$$

这里无符号密度是无条件计数，带符号平衡才承载 RH 等价性。

## 68. $5040^h$ 的关联容量增长

令 $h\ge1$，把容量盒扩展为

$$
0\le a_2\le4h,\quad0\le a_3\le2h,\quad0\le a_5,a_7\le h.
$$

则

$$
\boxed{|\operatorname{Div}(5040^h)|=(4h+1)(2h+1)(h+1)^2.}
$$

三叶投影的 $(u,w)$ 像是矩形并集

$$
R_k=\{(u,w):k\le u\le4h+k,\ k\le w\le h+k\},\qquad0\le k\le h.
$$

按固定 $w$ 求并集宽度并求和，得到

$$
\boxed{|\operatorname{im}C|=(3h+1)^2(2h+1).}
$$

确切地，$w=0,\ldots,h$ 时宽度为 $4h+1+w$，$w=h+1,\ldots,2h$ 时宽度为 $4h+1+2h-w$；两段总和为 $(3h+1)^2$，再乘 $2h+1$ 个 $v$ 值。于是有符号推送的核维数为

$$
\boxed{4h^3(2h+1).}
$$

固定 $(u,v,w)=(h,0,h)$ 时，$\kappa=0,\ldots,h$ 的 $h+1$ 个来源都合法，所以给定三叶观察恢复完整来源至少需要 $h+1$ 个记录值；记录 $\kappa$ 达到此界，固定二进制字宽为 $\lceil\log_2(h+1)\rceil$。

但扩大 $5040^h$ 只提高四个已有素数方向的指数容量。对任意 $h$，有限 Dirichlet 多项式仍为

$$
\boxed{\sum_{d\mid5040^h}\frac{\mu(d)}{d^s}
=(1-2^{-s})(1-3^{-s})(1-5^{-s})(1-7^{-s}).}
$$

它不会自动引入新的素数方向。

## 追加锚（同块关系与关联边界批次后）

## 69. 本批桥接的范围

第 62–65 节是有限合法块族与 60 状态观察矩阵的精确线性结论；第 66–67 节把一个明确的局部配对边界约化为经典 Mertens 判据，使用全部实数截断和 $α>0$ 的幂增长估计。Mellin 公式的积分等式只在 $\Re s>1$ 初始成立，右端的更大域表述是亚纯延拓；它不构成 RH 证明。

第 68 节只增加 $2,3,5,7$ 四个既有素数方向的指数容量。一般合法块的高阶同块坐标、来源顺序、共享节点身份和未来更新接口仍需按具体任务另行保留；它们不能由当前的无序重数自动恢复。

这些新增桥接尚未作为新增定理在 Lean 中编译，也没有把 51、12 或 8 解释成物理维数。它们给出的可复用对象是：同块关系的反演、指定观察矩阵的核、以及局部关联边界与全局算术增长之间的精确映射。

## 追加锚（同块关系与关联边界批次后）

## 70. 截断同块观察的秩与隐藏高阶关系

沿用第 62 节的有限向下封闭块族 $\mathcal K$。对 $r\ge1$ 定义

$$
\mathcal K_{\le r}=\{T\in\mathcal K^+:|T|\le r\},qquad
\mathcal K_{>r}=\mathcal K^+\setminus\mathcal K_{\le r}.
$$

令 $I$ 为完整同块观察矩阵

$$
(Im)_T=\sum_{S\supseteq T}m_S,qquad T\in\mathcal K^+,
$$

令 $I_{\le r}$ 只保留 $T\in\mathcal K_{\le r}$ 的行。把块按大小从大到小排列后，$I$ 是对角为1的整数三角矩阵；它的逆正是第 62 节的容斥反演。

### theorem 70.1 截断关系的精确秩

在整数格及其任意特征零标量扩张中成立；若限制到笛卡尔有界盒
$0\le m_S\le H$（$H\ge1$），其线性张成空间也具有同一秩。带有额外全局约束的状态集，须另行证明其仿射张成空间仍为全空间。

$$
\boxed{\operatorname{rank}I_{\le r}=|\mathcal K_{\le r}|,\qquad
\dim\ker I_{\le r}=|\mathcal K_{>r}|.}
$$

**证明。** 取行列由 $\mathcal K_{\le r}$、列也由 $\mathcal K_{\le r}$ 的子矩阵。按大小降序排列后，它是对角为1的三角矩阵，因而行满秩。总列数为 $|\mathcal K^+|$，秩—零化度公式给出核维数。证毕。 $\square$

所以，若只保留至 $r$ 阶的同块关系，线性意义下恰好遗漏每个高于 $r$ 阶关系的一个自由方向。对全体关系做无损恢复，必须达到合法块的最大大小；对特定任务，可以只补回该任务在这些核方向上的响应。

三原子窗口的合法块最大大小为2，因此只保留一阶读数 $(u,v,w)$ 时恰有一个高阶方向，即 $[2+5]$ 与 $[2][5]$ 的关联；加入它便得到第 58 节的四坐标。加入 $13$ 后，三阶块 $[2+5+13]$ 产生新的独立高阶方向，二阶关系不再充分。

## 71. 同块关系的递归更新与交换图

对任意合法块 $R\in\mathcal K^+$，令 $e_R$ 表示只在 $R$ 坐标取1的块多重集增量，并定义增量关系向量

$$
\iota_R(T)=\mathbf1_{\{T\subseteq R\}},qquad T\in\mathcal K^+.
$$

在完整关系坐标和截断关系坐标上分别定义

$$
U_R(m)=m+e_R,\qquad
\widehat U_R(y)=y+\bigl(\iota_R(T)\bigr)_{T\in\mathcal K^+},\qquad
\widehat U_R^{(r)}(y)=y+\bigl(\iota_R(T)\bigr)_{T\in\mathcal K_{\le r}}.
$$

### theorem 71.1 关系坐标对块增量闭合

$$
\boxed{
I\circ U_R=\widehat U_R\circ I,qquad
I_{\le r}\circ U_R=\widehat U_R^{(r)}\circ I_{\le r}.
}
$$

并且对所有合法块 $R,S$，

$$
\widehat U_R^{(r)}\circ\widehat U_S^{(r)}
=
\widehat U_S^{(r)}\circ\widehat U_R^{(r)}.
$$

**证明。** 对每个观察坐标 $T$，加入一份 $R$ 恰使 $y_T$ 增加 $1$ 当且仅当 $T\subseteq R$，所以两条交换式逐坐标成立。增量是加法，故不同块的更新交换。证毕。 $\square$

这给出一个明确的有限交换更新接口：截断观察虽然不能恢复所有高阶块重数，却可以独立执行所有“加入一个合法块”的未来操作。它能否回答某个终端任务，取决于该任务是否在 $\ker I_{\le r}$ 的每个方向上保持不变。

### theorem 71.2 终端任务的截断充分性判据

设 $\Phi$ 是块多重集上的任务。若

$$
I_{\le r}m=I_{\le r}m'
\Longrightarrow
\Phi(m)=\Phi(m')
$$

对所有声明的状态，则在 $\operatorname{im}I_{\le r}$ 上存在唯一函数 $\widehat\Phi$ 使

$$
\Phi=\widehat\Phi\circ I_{\le r}.
$$

反之，若存在一对同截断读数但任务值不同的状态，则任何只访问 $I_{\le r}m$ 的解码器都会失败。

**证明。** 这是把任务在观察纤维上良定义的充要条件；正向按纤维定义 $\widehat\Phi$，反向由同一观察值必须得到同一输出。证毕。 $\square$

因此，更新闭合与任务充分性是两个不同义务：第 71.1 节保证摘要本身能继续演化，第 71.2 节才决定它是否保存了指定未来所需的关系。

## 72. 有界重数中的记录容量与下一层原子

若每种合法块的重数满足 $0\le m_S\le H$，则在环境整数格中，截断观察的差分核仍由第 70.1 节给出的 $|\mathcal K_{>r}|$ 个线性方向生成；限制到有限盒后，实际纤维是这些方向与盒的交集，大小取决于边界位置。对恢复全部块重数，直接补回 $y_T$（$|T|>r$）达到无损恢复；对单个目标 $\Phi$，只需补回其在这些纤维上的变化。

把一个合法块 $R$ 封装为下一层原子时，必须同时保留其展开映射

$$
\operatorname{expand}(R)=R
$$

及递归更新接口 $U_R$。封装只改变调用层级，不删除底层共同来源；若下一层操作能区分两个展开具有相同低阶关系却不同高阶关系的块，则必须把相应 $y_T$ 或等价记录暴露给下一层。

这条原则把第 62 节的静态反演接回第 55 节的行为闭合：一个摘要可以在当前读数上充分，却因未来操作读取高阶关系而不再是递归模块。下一步若要得到 Lean 真值，最小候选是形式化有限向下封闭块族上的 $I\circ U_R=\widehat U_R\circ I$ 与截断任务纤维判据；本批仍只保留纸面证明。

## 追加锚（动态同块更新批次后）

## 73. 截断关系的核稳定性与删除反例

第 71.1 节的交换图只处理“加入一份已知块”这一类更新。对可能删除或合并高阶块的更新，截断观察还必须满足核稳定性。

### theorem 73.1 有限观察可递归闭合的充要条件

设 $M$ 是有限状态集，且令 $W=\operatorname{im}p$；$p:M\to W$ 是观察，$\tau_u:M\to M$ 是允许更新，$\rho:M\to O$ 是当前读出。存在

$$
\widehat\tau_u:W\to W,\qquad \widehat\rho:W\to O
$$

使

$$
p\circ\tau_u=\widehat\tau_u\circ p,\qquad
\rho=\widehat\rho\circ p
$$

当且仅当对所有 $m,m'$，若 $p(m)=p(m')$，则

$$
\rho(m)=\rho(m'),\qquad
p(\tau_u(m))=p(\tau_u(m'))\quad\text{对所有 }u.
$$

**证明。** 必要性由交换式直接得到。充分性是在每个观察纤维上定义 $\widehat\rho$ 与 $\widehat\tau_u$；纤维上的常值性保证定义良好。沿操作词归纳，还可得到任意有限未来行为在 $p$ 上因子化。证毕。 $\square$

### 一个三原子删除反例

取 $A=\{1,2,3\}$、$\mathcal K=2^A\setminus\{\varnothing\}$，并令 $p=I_{\le2}$。考虑两个二进制块多重集

$$
m_A=\{123,1,2,3\},\qquad
m_B=\{12,13,23\}.
$$

它们都有相同的截断关系读数

$$
p(m_A)=p(m_B)=(2,2,2,1,1,1),
$$

其中坐标顺序为三个单点、三个二点。令 $\tau$ 删除一份 $123$ 块（若不存在则不变），则

$$
p(\tau m_A)=(1,1,1,0,0,0),\qquad
p(\tau m_B)=(2,2,2,1,1,1).
$$

所以截断摘要不能闭合这个未来更新，尽管它对当前截断读数本身完全一致。

这个碰撞在二进制状态盒中是唯一的。若 $d=m-m'$ 的截断读数为零，则三条二点方程给出

$$
d_{12}=d_{13}=d_{23}=-d_{123},
$$

代入三个单点方程得到

$$
d_1=d_2=d_3=d_{123}.
$$

由于每个坐标只取 $0,1$，非零差异只能是 $m_A-m_B$ 或其相反数。因此 $p$ 的图像有 $2^7-1=127$ 个值；加入一次删除更新后的行为对

$$
m\longmapsto\bigl(p(m),p(\tau m)\bigr)
$$

则为单射，共有 128 个行为类。

这说明“当前读数上闭合”与“对所有允许未来操作递归闭合”是两个独立条件。完整同块坐标保留三阶坐标后，删除更新可由

$$
\widehat\tau(y)_T=y_T-\mathbf1_{\{123\text{ 块存在}\}}\mathbf1_{\{T\subseteq123\}}
$$

直接实现；截断到二阶时，这个必要的三阶状态已经被丢掉。

## 追加锚（核稳定性反例批次后）


## 74. Robin 作为关系子结构的加权读出

经典 Robin 判据写成

$$
\mathrm{RH}
\iff
\forall n>5040,\qquad
\frac{\sigma(n)}n<e^\gamma\log\log n,
$$

其中 $\sigma(n)=\sum_{d\mid n}d$，严格范围是 $n>5040$。利用约数互补，定义

$$
Z(n):=\frac{\sigma(n)}n=\sum_{d\mid n}\frac1d.
$$

因此它读取的是全部合法约数子结构的正权重总和，而不是约数个数。

在此前的 Fibonacci 操作载体 $V_n=(\mathbb Z/n\mathbb Z)^2$ 中，若 $\mathscr L_n$ 表示同时由递归更新与方向提取保持的加法子群，已有分类给出

$$
\mathscr L_n=\{dV_n:d\mid n\}.
$$

因为 $[V_n:dV_n]=d^2$，同一个读数可写成

$$
Z(n)=\sum_{W\in\mathscr L_n}[V_n:W]^{-1/2}.
$$

这里的指数 $1/2$ 来自二维载体的指数，不能单独解释为 ζ 函数的临界线。它只把 Robin 的约数权重准确翻译成关系子结构的加权读出。

沿用四个合法块

$$
[2],\quad[3],\quad[5],\quad[2+5],
$$

及其乘法轴 $2,3,5,7$。若

$$
(u,v,w;\kappa)=(a_2+a_7,a_3,a_5+a_7;a_7),
$$

则

$$
 n=2^{u-\kappa}3^v5^{w-\kappa}7^\kappa,
$$

而令 $A_p(a)=1+p^{-1}+\cdots+p^{-a}$，便有

$$
\boxed{
Z_{\mathrm{blk}}(u,v,w;\kappa)
=A_2(u-\kappa)A_3(v)A_5(w-\kappa)A_7(\kappa).
}
$$

相应的数量尺度为

$$
\boxed{
\log n=u\log2+v\log3+w\log5-\kappa\log\frac{10}{7}.
}
$$

所以在这四块生成域内，关联数同时改变 Robin 不等式的左右两侧：它改变约数权重，也改变整体的对数规模。

### 5040 的配置与已有全称结果

对

$$
(a_2,a_3,a_5,a_7)=(4,2,1,1),
$$

有

$$
\mathcal C(5040)=(5,2,2;1),\qquad
Z(5040)=\frac{31}{16}\frac{13}{9}\frac65\frac87=\frac{403}{105}.
$$

该值严格超过 $e^\gamma\log\log5040$，这正是 Robin 判据把 $5040$ 排除在严格不等式范围之外的原因。

仓库已有的

```text
D5.S3.Arith.Robin.SevenSmooth.robin_seven_smooth
```

则证明：对任意无上界的 $a,b,c,d\in\mathbb N$，只要

$$
2^a3^b5^c7^d>5040,
$$

就满足 Robin 严格不等式。该 Lean 定理覆盖当前四个块反复增加深度的整个乘法族；本节只作关系语言的解释，没有把它扩展为新素数方向的全局结论。

## 75. 同块纤维中的精确 Robin 权重

固定母体

$$
 n=2^{A_2}3^{A_3}5^{A_5}7^{A_7}.
$$

约数

$$
 d=2^{b_2}3^{b_3}5^{b_5}7^{b_7}
$$

的叶子坐标为

$$
 u=b_2+b_7,\qquad v=b_3,\qquad w=b_5+b_7,\qquad k=b_7.
$$

于是

$$
 d=2^u3^v5^w\left(\frac7{10}\right)^k,
\qquad
\frac1d=2^{-u}3^{-v}5^{-w}\left(\frac{10}{7}\right)^k.
$$

固定 $(u,v,w)$ 后，可行的关联数正好是

$$
 k_{\min}=\max(0,u-A_2,w-A_5),\qquad
 k_{\max}=\min(A_7,u,w).
$$

因此无需逐一恢复纤维内部状态，也能保留 Robin 所需的精确权重：

$$
\boxed{
\Omega_{u,v,w}=2^{-u}3^{-v}5^{-w}
\sum_{k=k_{\min}}^{k_{\max}}\left(\frac{10}{7}\right)^k,
\qquad
Z(n)=\sum_{\substack{u,v,w\\ k_{\min}\le k_{\max}}}\Omega_{u,v,w}.
}
$$

其中

$$
\mathcal F_n=
\{(u,v,w):k_{\min}(u,v,w)\le k_{\max}(u,v,w)\}
$$

是非空纤维的叶子读数集合。

这是“关系记录”与“任务权重”之间的具体接口。若只记录纤维大小而把每个来源按同一倒数权重处理，得到的不是 $Z(n)$。

### 5040 的 13/112 漏项

5040 的叶子投影有12个二点纤维。对 $a=1,2,3,4$、$b=0,1,2$，其两个约数为

$$
 d_0=2^a3^b5,\qquad d_1=2^{a-1}3^b7,
$$

对应 $k=0,1$。正确纤维权重为

$$
\frac1{d_0}+\frac1{d_1}
=2^{-a}3^{-b}\left(\frac15+\frac27\right)
=\frac{17}{35}2^{-a}3^{-b}.
$$

若错误地把二者都按 $d_0$ 的权重计算，则每个纤维少算

$$
\frac1{d_1}-\frac1{d_0}=\frac3{35}2^{-a}3^{-b}.
$$

12 个纤维的总漏项为

$$
\frac3{35}\left(\sum_{a=1}^4 2^{-a}\right)
\left(\sum_{b=0}^2 3^{-b}\right)
=\boxed{\frac{13}{112}}.
$$

错误值为

$$
\widetilde Z(5040)=\frac{403}{105}-\frac{13}{112}=\frac{6253}{1680}.
$$

精确有理区间核验给出

$$
\widetilde Z(5040)<e^\gamma\log\log5040<Z(5040),
$$

所以忽略关联权重会把真实的 Robin 例外伪装成满足不等式的状态。正确的纤维几何级数粗化保持 $Z$；错误的是把同一叶子读数误当成同一算术权重。

## 76. 5040 的资源极值与 Robin 的区别

定义

$$
J_\varepsilon(n)=\frac{Z(n)}{n^\varepsilon}.
$$

由于它按素数方向分解，令

$$
 r_p(a)=\frac{A_p(a+1)}{A_p(a)}
 =1+\frac{p-1}{p(p^{a+1}-1)}.
$$

该边际比严格随 $a$ 下降；增加一个 $p$ 块使 $J_\varepsilon$ 乘以 $r_p(a)p^{-\varepsilon}$。因此最优重复深度由相邻边际比夹住。

仓库的

```text
D5.S3.Arith.GoldenResourceOptimalInteger.golden_resource_unique_optimum
```

已证明在 $\varepsilon=1/25$ 时，5040 是全部正整数上的唯一最优点，即

$$
\frac{\sigma(n)}{n^{26/25}}
\le
\frac{\sigma(5040)}{5040^{26/25}},
$$

等号仅在 $n=5040$。对四个当前方向，将前一层边际比

$$
\frac{31}{30},\ \frac{13}{12},\ \frac65,\ \frac87
$$

与下一层边际比

$$
\frac{63}{62},\ \frac{40}{39},\ \frac{31}{30},\ \frac{57}{56}
$$

分别与 $p^{1/25}$ 比较，可以验证四个方向的阈值；新增素数方向从 $11$ 开始，其第一份也低于该价格。仓库另有价格区间定理，说明一段严格价格区间内仍由5040唯一最优。

这个极值结论与 Robin 全称不等式承担不同任务：前者固定一个线性幂成本并寻找最大配置，后者要求所有 $n>5040$ 的双对数上界。不能由单一价格下的全局最优性替代 Robin 的全尺度估计。

## 77. 已有方向的深度与新原子方向

对有限素数支持集 $P$，有

$$
Z(n)=
\underbrace{\prod_{p\in P}(1-p^{-1})^{-1}}_{C(P)}
\underbrace{\prod_{p\in P}(1-p^{-(a_p+1)})}_{D(\mathbf a)}.
$$

这里 $0<D(\mathbf a)\le1$，且 $C(P)$ 只是该固定支持集上的容量上界。增加已有方向的指数，只使 $D(\mathbf a)$ 趋近1；增加新素数方向则提高容量上限 $C(P)$。因此沿固定有限 $P$ 让指数增长时，$Z(n)$ 有界而 Robin 右侧最终增长；真正的全局难点在于允许 $P$ 不断扩展。

在 Robin 域 $n>5040$ 中，若 $p$ 为素数且 $a=v_p(n)\ge0$（允许 $a=0$ 表示 $p\nmid n$），Robin 比值 $\mathcal R(n)=Z(n)/\log\log n$ 的单步更新为

$$
\boxed{
\frac{\mathcal R(np)}{\mathcal R(n)}
=
\frac{1-p^{-(a+2)}}{1-p^{-(a+1)}}
\frac{\log\log n}{\log(\log n+\log p)}.
}
$$

第一因子是新增约数子结构的收益，第二因子是规模增长的惩罚。该公式是继续研究新关系块时应保持的精确预算方程。

在当前关系语言中，7 块同步移位 $2\mapsto3$、$5\mapsto8$ 给出 $3+8=11$，提供了一个候选结构对应和搜索线索；它不构成新素数轴存在或资源最优性的证明。再移一步得到 $5+13=18$，已是合数。因此合法 Fibonacci 块与可作为 Euler 乘法轴的素数块必须继续分开认证。

## 78. Robin 桥接的范围与开放边界

到此为止，关系语言已经给出三层精确接口：

$$
\boxed{
\text{合法 Fib 块}
\longrightarrow
\text{同块纤维}
\longrightarrow
\text{纤维内的倒数权重总和}
\longrightarrow
\text{Robin 余量}.
}
$$

有限四轴域的关联权重、5040 的临界漏项，以及四轴指数的资源极值都可以直接计算；四轴族在 $n>5040$ 上的 Robin 全称结论由仓库现有 Lean 定理承担。

仍未解决的是让新素数方向不断加入时保持统一的 Robin 余量控制。这里需要的是跨所有有限素数支持集的定量估计，而不是继续增加 $2,3,5,7$ 四根轴的重复深度。第 74–78 节的新增桥接尚未作为新增 Lean 声明编译；上述内容没有证明 RH，也没有把 Fibonacci 关系载体的二维指数解释成物理临界维数。

## 追加锚（Robin 加权关系批次后）

### 78.1 递归素 Fib 原子块是主模型，逐素数 Fib 行是辅助索引

本卷的主对象是前文的递归块语言：叶子是已认证的素 Fib 原子，同层允许的加法节点由当前合法窗口给出，块之间的乘法节点只组合完整块。结构配置保留加法节点的层级边界与同块关系，因此 $[2+5]$ 与 $[2][5]$ 是不同结构，值分别为 $7$ 与 $10$。

设 $\mathscr B_{\mathrm{rec}}$ 为给定块语法和合法性规则下的规范结构配置。对乘法配置

$$
B=\prod_A A^{m_A}
$$

定义完整块子配置

$$
C\preceq_\times^{\mathrm{blk}}B
\iff
C=\prod_A A^{r_A},\quad 0\le r_A\le m_A.
$$

这里不能把已选块内部的叶子拆出后再当作独立子配置。令 $\operatorname{val}$ 按“块内求和、块间相乘”递归解释结构，$\mathcal E_{\mathrm{blk}}(C)=\log\operatorname{val}(C)$，并定义

$$
\boxed{
\mathcal Z_{\mathrm{blk}}(B)
=\sum_{C\preceq_\times^{\mathrm{blk}}B}e^{-\mathcal E_{\mathrm{blk}}(C)}.
}
$$

只有当所考察的规范块域对整数及其约数代表无重复（或先经过 canonical value quotient）时，才可把这份结构求和识别为 $\sigma(\operatorname{val}B)/\operatorname{val}B$。四块域 $[2],[3],[5],[2+5]$ 的值为互异素数 $2,3,5,7$，所以在 $2^a3^b5^c7^d$ 子域中该条件成立。

逐素数 Fibonacci 行（第 79–80 节）只为每个指数提供唯一的数值码，从而把全体正整数与 Robin 的全称量词接上；它不定义、替换或恢复递归块的层级和同块关系，也不能把行位支撑包含当作块子配置关系。


## 79. 辅助的全局 Fib 重数表与 F–Robin 等价式

前面的四块系统只覆盖 $2^a3^b5^c7^d$。下面的逐素数重数表只是把任意正整数接入全局量词的辅助索引；它不是前文“素 Fib 原子—加法成块—乘法组合”的递归块语法。递归块版本的 Robin 读出见第 82 节。

要得到与 Robin 判据同量词的全局辅助版本，让每个素数标签各自携带一行 Fibonacci 重数码。

定义

$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j.
$$

令 $\mathscr F$ 为所有有限支撑表

$$
B=(b_{p,j})_{p\in\mathbb P,\ j\ge0},
$$

其中 $b_{p,j}\in\{0,1\}$，并满足

$$
 b_{p,j}b_{p,j+1}=0
$$

对每个 $p,j$。第 $p$ 行表示重数

$$
 a_p(B)=\sum_j b_{p,j}G_j,
$$

表的数值与对数规模定义为

$$
N(B)=\prod_p p^{a_p(B)},
\qquad
\mathcal E(B)=\sum_{p,j}b_{p,j}G_j\log p.
$$

唯一素因数分解与每一行的 Zeckendorf 唯一性给出

$$
\boxed{N:\mathscr F\overset{\sim}{\longrightarrow}\mathbb N_{>0},\qquad
\mathcal E(B)=\log N(B).}
$$

这里 $p$ 是乘法原子标签，$G_j$ 是编码该原子重数的 Fibonacci 位权；两层原子不能混同。

对 $B,C\in\mathscr F$ 定义乘法子配置关系

$$
\boxed{
C\preceq_\times B
\iff
 a_p(C)\le a_p(B)\quad\text{对每个素数 }p.
}
$$

这等价于 $N(C)\mid N(B)$，而不等价于每一行码字的支撑逐位包含。例如 $2\le4$，但重数码 `010` 不是 `101` 删除若干个1得到的码字。

定义完整配置的约数配分函数

$$
\boxed{
\mathcal Z(B)=\sum_{C\preceq_\times B}e^{-\mathcal E(C)}.
}
$$

由于 $e^{-\mathcal E(C)}=1/N(C)$，有

$$
\mathcal Z(B)=\sum_{d\mid N(B)}\frac1d=\frac{\sigma(N(B))}{N(B)}.
$$

因此经典 Robin 定理等价于如下全局 Fibonacci 命题：

$$
\boxed{
\mathrm{RH}
\iff
\forall B\in\mathscr F,\quad
\mathcal E(B)>\log5040
\Longrightarrow
\mathcal Z(B)<e^\gamma\log\mathcal E(B).
}
\tag{F--Robin}
$$

右侧是 $e^\gamma\log\log N(B)$；不能误写成 $e^\gamma\mathcal E(B)$。若定义

$$
\Delta_{\mathrm{Fib}}(B)=\gamma+\log\log\mathcal E(B)-\log\mathcal Z(B),
$$

则 F--Robin 要求所有超过阈值的配置满足 $\Delta_{\mathrm{Fib}}(B)>0$。

**证明。** 对任意 $B$ 代入 $n=N(B)$，上式化为经典 Robin 不等式；反向由 $N$ 的双射性覆盖每个正整数。证毕。 $\square$

## 80. 合法窗口递归生成约数权重

对长度 $L$ 的非相邻词，定义

$$
P_L(z)=\sum_{w\in\mathcal W_L}z^{\operatorname{val}(w)}.
$$

最高位是否选择给出

$$
P_0(z)=1,\qquad P_1(z)=1+z,
$$

以及（对 $L\ge2$）

$$
\boxed{P_L(z)=P_{L-1}(z)+z^{G_{L-1}}P_{L-2}(z).}
$$

完整窗口双射进一步给出

$$
\boxed{P_L(z)=1+z+\cdots+z^{G_L-1}.}
$$

所以当第 $p$ 行的重数容量为 $G_L-1$ 时，该行对 $\mathcal Z$ 的贡献是 $P_L(p^{-1})$。这里的递归只是逐素数重数的辅助 Fibonacci 索引递归，不是主块语法中的递归成块；它说明行级 Fibonacci 语法生成的是约数权重，而不只是状态数。

5040 的四行重数为

$$
4=G_3-1,\qquad 2=G_2-1,\qquad 1=G_1-1,\qquad1=G_1-1,
$$

对应高位在左的码字 `101`、`10`、`1`、`1`。于是

$$
\mathcal Z(B_{5040})
=P_3(1/2)P_2(1/3)P_1(1/5)P_1(1/7)
=\frac{31}{16}\frac{13}{9}\frac65\frac87
=\frac{403}{105}.
$$

该值高于 $e^\gamma\log\log5040$；严格不等式要求从 $5040$ 之后的全部配置，而不是把 $5040$ 本身纳入量词。

## 81. 全局配置与四块关联坐标的边界

完整表 $B$ 的 F--Robin 形式覆盖所有素数方向，并且每个约数只由其唯一整数值计数一次。四块关联坐标

$$
(u,v,w;\kappa)
$$

只是将 $2,3,5,7$ 这一有限子族的指数重新参数化；在该子族内，前述精确纤维权重给出同一个 $\mathcal Z$。若加入如 $[2+13]$ 这样的合数值块，必须重新选择规范块语言，避免同一整数同时由不同块语法重复计数。

因此当前成果的边界是：辅助配置双射把 Robin 等价式写成全体正整数的一个全局索引；四块递归关联分析给出主模型中的局部权重；`robin_seven_smooth` 闭合四个旧素数方向在 $n>5040$ 的全称不等式。新素数方向不断加入时的统一余量估计仍然开放。

第 79–81 节是纸面桥接，尚未作为新增 Lean 声明编译，也没有由此宣称 RH 已被证明。

## 追加锚（全局 F–Robin 配置批次后）

## 82. 递归素 Fib 原子块上的 Robin 读出

本节回到本卷的主编码对象。第一层素 Fib 原子为

$$
\mathcal A_0=\{2,3,5\},
$$

这里仍用数值标签作简写；严格地可取带类型的叶子 $\mathfrak f_2,\mathfrak f_3,\mathfrak f_5$，其值映射为 $\nu(\mathfrak f_2)=2$、$\nu(\mathfrak f_3)=3$、$\nu(\mathfrak f_5)=5$。符号 $[2+5]$ 表示一个加法节点，不把它与任意同值的其他语法树识别为同一结构。

禁止相邻选择的非空合法块族为

$$
\mathcal K_1=\{[2],[3],[5],[2+5]\}.
$$

块内使用加法，块之间使用乘法。记四个块的数值为

$$
v_{[2]}=2,\qquad v_{[3]}=3,\qquad v_{[5]}=5,\qquad v_{[2+5]}=7.
$$

在这一层，一个规范乘法配置是块重数表

$$
m=(m_{[2]},m_{[3]},m_{[5]},m_{[2+5]})\in\mathbb N^4,
$$

其数值与规模为

$$
N_1(m)=\prod_{S\in\mathcal K_1}v_S^{m_S},
\qquad
\mathcal E_1(m)=\log N_1(m).
$$

完整乘法子配置关系是

$$
\boxed{m'\preceq_\times m\iff m'_S\le m_S\quad(S\in\mathcal K_1).}
$$

因此，若这些块作为独立的规范乘法轴，Robin 左侧的递归块读出为

$$
\boxed{
\mathcal Z_1(m)
=\sum_{m'\preceq_\times m}\frac1{N_1(m')}
=\prod_{S\in\mathcal K_1}\left(\sum_{j=0}^{m_S}v_S^{-j}\right).
}
$$

这一定义对子配置取的是完整块重数，不能把一个 $[2+5]$ 块拆成独立的 $[2]$ 与 $[5]$ 子配置。若改用叶子摘要

$$
(u,v,w;\kappa)=(m_{[2]}+m_{[2+5]},m_{[3]},m_{[5]}+m_{[2+5]},m_{[2+5]}),
$$

同一个子配置的权重精确变为

$$
\frac1{N_1(m')}
=2^{-u}3^{-v}5^{-w}\left(\frac{10}{7}\right)^\kappa.
$$

这就是当前四块层、在该叶子坐标下同块关系对 Robin 权重的唯一修正；第 75 节的纤维几何级数是在不恢复每个块重数时保留这份权重的方式。

递归扩展时，块本身可以作为下一层的部件，例如 $8=[5+3]$、$11=[3+[5+3]]$。但每个新块必须保留层级边界、加法节点和乘法节点的结构身份，并重新认证其数值是否允许作为独立 Euler 轴。若某个新块的数值与已有乘法组合相同（例如 $[2+13]$ 的数值为 $15=3\cdot5$），必须选择规范块身份或按整数值取商，不能把两种语法重复计入同一个 Robin 子配置。

在当前四块层，5040 的主编码为

$$
5040=[2]^4[3]^2[5][2+5],
\qquad
(u,v,w;\kappa)=(5,2,2;1),
$$

并且

$$
\mathcal Z_1(4,2,1,1)=\frac{403}{105}.
$$

所以本卷的主结论应读作：Robin 检验的是递归素 Fib 块生成的**规范乘法子配置的倒数权重总和**。第 79–81 节的逐素数 Fibonacci 表只负责给出一个覆盖全部整数的辅助索引；它不取代这里的同块关系编码。

本节仍是纸面定义与桥接，尚未作为新增 Lean 声明编译；它没有把四块递归模型外推为全局 RH 证明。

## 追加锚（递归块 Robin 主编码批次后）

## 83. 同源模观测与联合乘法谱

**定义 83.1（同源关系 DAG）。** 令 $\Omega$ 为允许的源赋值集合。每个带类型的叶子、加法节点和乘法节点 $v$ 都在同一个 $\omega\in\Omega$ 上取整数值 $N_v(\omega)$；共享子节点只表示一个来源。对 $m\ge2$ 定义 $r_m(v,\omega)=N_v(\omega)\bmod m$。不同模数、不同节点的联合状态是同一赋值的像

$$
\mathcal J=\{(r_{m_i}(v_i,\omega))_i:\omega\in\Omega\},
$$

不能以各坐标像的笛卡尔积代替。下文对正整数写 $Z(n)=\sigma(n)/n$，所有对数取自然底。

**命题 83.2（关系保留与模求值）。** 沿 DAG 按拓扑次序执行模加法、模乘法，得到的恰是整数求值后的余数；若把共享源改成独立副本，此结论只对改写后的源模型成立，不能回用于原联合状态。

**证明。** 每个叶子由定义成立；$\mathbb Z\to\mathbb Z/m\mathbb Z$ 保持加法和乘法，故逐节点归纳成立。联合像必须使用同一个 $\omega$。例如均匀比特 $U$ 给出的两种关系 $(U,U)$ 与 $(U,1-U)$ 有相同边缘分布，但前者乘积为 $U$，后者乘积恒为零；边缘读数没有保存乘法所需的关系。这里的同源要求不等于各输出独立。 $\square$

**命题 83.3（CRT 联合像与乘法纤维）。** 给定有限非空模数族 $m_i\ge2$，令 $L=\operatorname{lcm}_i m_i$，固定整数 $N$。余数组 $(y_i)_i$ 属于 $x\mapsto(Nx\bmod m_i)_i$ 的像，当且仅当

$$
y_i\equiv y_j\pmod{\gcd(m_i,m_j)},\qquad
\gcd(N,m_i)\mid y_i\quad\text{对所有 }i,j.
$$

在 $x\bmod L$ 上，每个非空纤维的大小都是 $d=\gcd(N,L)$，联合像大小为 $L/d$。若去掉乘子 $N$，第一组条件本身就是广义 CRT 的存在条件，解唯一到模 $L$。

**证明。** 广义 CRT 将兼容元组唯一识别为 $y\bmod L$。线性同余 $Nx\equiv y\pmod L$ 可解当且仅当 $d\mid y$，可解时有 $d$ 个解。局部整除条件等价于这一全局条件：对每个素数 $p$，取 $v_p(m_i)$ 最大的一个模数，就检查了 $\min(v_p(N),v_p(L))$ 所需的全部 $p$ 次幂；$N=0$ 时直接读作各输出均为零。 $\square$

**命题 83.4（均匀同源下的信息读出）。** 在命题 83.3 中，若 $X$ 在 $\mathbb Z/L\mathbb Z$ 上均匀，令

$$
Y_i=NX\bmod m_i,\qquad a_i=\frac{m_i}{\gcd(N,m_i)},\qquad A=\operatorname{lcm}_i a_i.
$$

则

$$
\begin{aligned}
A&=\frac{L}{\gcd(N,L)},\\
H((Y_i)_i)&=\log A,\qquad H(Y_i)=\log a_i,\\
I(Y_i;Y_j)&=\log\gcd(a_i,a_j)
=\log\frac{\gcd(m_i,m_j)}{\gcd(N,\gcd(m_i,m_j))},\\
\sum_iH(Y_i)-H((Y_i)_i)&=\log\frac{\prod_i a_i}{A}.
\end{aligned}
$$

全族相互独立当且仅当 $a_i$ 两两互素。若再观测模 $m\ge2$，则新增条件熵公式另须假设同一个源 $X$ 在 $\mathbb Z/L_{\mathrm{new}}\mathbb Z$ 上均匀，其中 $L_{\mathrm{new}}=\operatorname{lcm}(L,m)$，且旧观测 $Y_i=NX\bmod m_i$ 与新观测 $NX\bmod m$ 全部由这个共同源给出。在此假设下，令 $a=m/\gcd(N,m)$，有 $H(NX\bmod m\mid(Y_i)_i)=\log(a/\gcd(a,A))$；前述固定族公式仍只需原来的模 $L$ 均匀性。

**证明。** 逐素数比较最大指数得有效最小公倍数公式；等纤维大小把均匀源推为均匀像，熵就是像大小的对数。对二元子族应用同一公式，再用 $\operatorname{lcm}(a,b)\gcd(a,b)=ab$。对新增模数，在上述模 $L_{\mathrm{new}}$ 均匀共同源假设下，对扩展族应用同一公式，并减去旧族熵，得到 $\log\operatorname{lcm}(A,a)-\log A=\log(a/\gcd(a,A))$。联合支持等于边缘支持之积当且仅当 $\prod a_i=\operatorname{lcm}a_i$，这又等价于两两互素。 $\square$

新增模数所需的均匀性不能由旧边缘的均匀性推出。例如 $N=1$、旧模数为 $2$，整数源 $X$ 在 $\{0,1\}$ 上均匀，则 $L=A=2$ 且旧输出 $X\bmod2$ 已确定 $X$。加入模数 $3$ 时，新输出 $X\bmod3$ 也由旧输出确定，故条件熵为 $0$，而非 $\log3$。若只给定抽象的 $\mathbb Z/L\mathbb Z$ 源，新模数观测未必是良定义函数，须指定整数提升或使用更大的共同源。

均匀性是等式的条件。任意源律只能由支持大小推出 $H((Y_i)_i)\le\log A$；不得把支持计数直接称为该源律的熵。作为具体联合谱，$N=14$、模数 $8,12$ 的边缘像大小为 $4,6$，联合像为 $12$，每个像有两个原像，互信息为 $\log2$；兼容对 $(1,1)$ 却不属于乘法像。$N=2$、模数 $6,10$ 的有效模数为 $3,5$，所以非恒定输出仍可独立。这些是广义 CRT 和有限群同态的应用；仓内对应来源为 `CompatibleResidueJointImage.joint_residue_image_eq_compatible_pairs`，上游对应为 Mathlib 的 `Nat.chineseRemainder'`，不另作原创性主张。

## 84. 精确局部指数与未解析余因子的统一上界

**命题 84.1（局部指数的精确性边界）。** 对正整数 $n$、素数 $p$ 和 $e\ge0$，$v_p(n)=e$ 等价于 $n\bmod p^{e+1}$ 是 $p^e$ 的倍数且不是零。只观察到 $n\bmod p^b=0$ 时，得到的是 $v_p(n)\ge b$，不能把 $b$ 当成精确指数。若已知所有 $p\le y$ 的精确指数，令

$$
C=\prod_{p\le y}p^{v_p(n)},\qquad n=CR,
$$

则 $\gcd(C,R)=1$，$R$ 不含任何 $p\le y$ 的素因子，且 $Z(n)=Z(C)Z(R)$。

**证明。** 前两项是整除与不整除的定义。精确除去这些素数的全部次数，余项与其素数乘积互素；归一化约数和在互素乘法下相乘。若只除去已知下界次数，余项仍可含相同素数，此乘法分解便没有所需的互素前提。 $\square$

**定理 84.2（两个未解析纤维的精确最大值）。** 对正整数 $R$，有

$$
\begin{aligned}
\max_{R\le4181,\ \gcd(R,210)=1}Z(R)&=\frac{3024}{2431},
&&\text{唯一取等于 }R=2431=11\cdot13\cdot17,\\
\max_{R<46189,\ \gcd(R,210)=1}Z(R)&=\frac{33516}{26741},
&&\text{唯一取等于 }R=26741=11^2\cdot13\cdot17.
\end{aligned}
$$

这些是对观测兼容集合的最大值；它们不宣布实际余因子 $R$ 等于某个极大点，也不提供实际 $R$ 的分解。

**证明。** 所有素因子至少为 $11$。若不同素因子不超过两个，则

$$
Z(R)<\frac{11}{10}\frac{13}{12}=\frac{143}{120}
<\frac{3024}{2431}<\frac{33516}{26741};
$$

$R=1$ 也满足这些界。对 $R\le4181$，由 $11^4>4181$，计重数的素因子总数不超过三；三个不同素因子只能各出现一次。有限几何和 $G_p(a)=\sum_{j=0}^a p^{-j}$ 对 $p$ 严格递减（$a\ge1$），故最大值唯一在前三个允许素数各一次时取得。

对 $R<46189=11\cdot13\cdot17\cdot19$，不同素因子不超过三个；由 $11^5>46189$，计重数总数不超过四。三个不同素因子的非平方自由情形仅有三个指数型。按递增素数顺序逐项用 $11,13,17$ 替代，得到

$$
\begin{aligned}
G_{11}(2)G_{13}(1)G_{17}(1)&=\frac{33516}{26741},\\
G_{11}(1)G_{13}(2)G_{17}(1)&=\frac{39528}{31603},\\
G_{11}(1)G_{13}(1)G_{17}(2)&=\frac{51576}{41327}.
\end{aligned}
$$

第一项严格最大；平方自由情形严格小于增加一次指数后的界。逐项单调性同时给出唯一取等条件。端点 $46189$ 不能纳入“三个不同素因子”的论证。 $\square$

**推论 84.3（固定 5040 核的局部 Robin 证书）。** 若 $\gcd(R,210)=1$，则 $R\le4181$ 时

$$
Z(5040R)\le\frac{4464}{935},
$$

而 $833\le R<46189$ 时

$$
e^\gamma\log\log(5040R)-Z(5040R)
>\frac{136783}{10285000}>0.
$$

在较小区间 $3329\le R<46189$ 上还可用更大的下界 $44611/257125$。

**证明。** $Z(5040)=403/105$。定理 84.2 相乘给出第二族上界 $49476/10285$。由 $833\cdot5040>2^{22}$、$\log2>69/100$、$e^{271/100}<151/10<22(69/100)$，有 $\log\log(5040R)>271/100$；再用 $e^\gamma>89/50$，相减即得第一余量。对 $R\ge3329$，用 $3329\cdot5040>2^{24}$ 和 $e^{14/5}<33/2<24(69/100)$，得到后一个余量。上述对数、指数常数可由正项级数及几何尾界验证；例如 $H_{1000}-\log1001>5767/10000$ 且 $e^{5767/10000}>89/50$，结合 $H_m-\log(m+1)<\gamma$ 即得 Euler 常数所需界。余量是归一化差；未归一化差还须乘 $5040R$。 $\square$

这里的精确最大值不声称最小 Robin 差也在同一 $R$ 取得。已有 `ExponentExchange.IntegerSwap.prime_exponent_swap` 表明：若 $p<q$ 且 $v_p(m)<v_q(m)$，交换两次指数会严格减小整数并严格增大 $Z$；该结论的精确指数与共同余因子条件必须保留，不能用指数下界代替。

## 85. 正价格层和、面积恒等式与有限区间转移

**定义 85.1（层增益与压力）。** 对素数 $p$、整数 $k\ge1$ 和价格 $\lambda>0$，定义

$$
\beta_{p,k}=\log\left(1+\frac1{p+\cdots+p^k}\right),\qquad
\theta_{p,k}=\frac{\beta_{p,k}}{\log p},\qquad
M(\lambda)=\sup_{n\ge1}\bigl(\log Z(n)-\lambda\log n\bigr).
$$

由仓内 `GoldenResourceSupremum.golden_resource_supremum_eq_positive_part_sum` 对应的层和结论，可写

$$
M(\lambda)=\sum_{p,k}(\beta_{p,k}-\lambda\log p)_+.
$$

这是既有结果的直接使用：$\log G_p(a)=\sum_{k=1}^a\beta_{p,k}$，同一素数的阈值严格递减，选择所有正增益层必然构成指数前缀。由 $\theta_{p,k}<1/(p\log p)$ 及固定 $p$ 时阈值趋零，每个正价格仅有有限个活跃层。等价价格层可以选或不选，其目标值相同；零价格不在有限性结论内。

**命题 85.2（面积与余因子支持界）。** 令 $A(t)=\sum_{\theta_{p,k}>t}\log p$，则对 $\lambda>0$

$$
M(\lambda)=\int_\lambda^\infty A(t)\,dt.
$$

若 $n=CR$，$C$ 只含 $p\le y$ 的素因子，$R$ 不含这些素因子，且 $1\le R\le B$，则

$$
\log Z(n)\le\log Z(C)+
\inf_{\lambda>0}\left\{\lambda\log B+
\sum_{p>y,k\ge1}(\beta_{p,k}-\lambda\log p)_+\right\}.
$$

精确观测下一个素数 $q>y$ 的指数 $e$ 后，将 $C$ 改为 $Cq^e$、$B$ 改为 $B/q^e$，并从未解析层和移除整个 $q$ 方向，所得上界不增加。

**证明。** 对每个层积分 $\log p\,1_{t<\theta_{p,k}}$，在 $t\ge\lambda$ 上只有有限项，逐项积分即为正部分和。余因子实际所取的层增益和不超过全部正部分；再用 $\log R\le\log B$。每个价格给出有效上界，故可取下确界。更新时，对固定价格有

$$
\log G_q(e)-\lambda e\log q
\le\sum_{k\ge1}(\beta_{q,k}-\lambda\log q)_+,
$$

逐价格比较再取下确界即可。该不增结论不保证严格改善。 $\square$

此界是线性支持包络，不总是精确约束最大值。例如 $y=2,B=2$ 的唯一允许余因子为 $1$，实际最大 $\log Z$ 为零，而包络为 $(\log(4/3)/\log3)\log2>0$。理由是剩余最大阈值来自 $(p,k)=(3,1)$：价格不低于此阈值时层和为零，低于时仅这一层就给出匹配下界。只在一个已认证的正价格区间内取下确界仍有效，但可更弱；全谱价格证书不能自动充当每个新余因子优化问题的精确证书。

**定理 85.3（有限价格证书的全整数转移）。** 取 $\delta=123/500000$。有限层数据在 $10^{-6}\le\lambda\le1/25$ 上给出

$$
K(\lambda):=\max_{x>1}
\{\gamma+\log\log x-M(\lambda)-\lambda x\}>\delta.
$$

结合下面的起始区间比较，得到每个整数 $5040<n\le10^{30000}$ 都满足 $Z(n)<e^\gamma\log\log n$。这是有限数值证书及纸面转移；不是新增的 Lean 定理，也不主张超越已发表的有限验证范围。

**证明。** $p\ge100000$ 时 $\theta_{p,k}<1/(p\log p)<10^{-6}$。较小素数各方向只须检查到第一个不活跃层；严格递减排除了余下尾部。有限数据包含 $9592$ 个素数、低价格处 $8665$ 个活跃层、$8657$ 个切换点与 $8658$ 个闭端价格胞腔。每个非初始胞腔的最优配置令 $A=\log n_*$、$B_* =\log Z(n_*)$，以 $x=A$ 作见证：

$$
\gamma+\log\log A-M(\lambda)-\lambda A
=\gamma+\log\log A-B_*>\delta.
$$

初始胞腔的最优整数为 $5040$，这与既有 `GoldenResourceOptimalInteger.golden_resource_unique_optimum` 在价格 $1/25$ 的结论一致。改取 $x=\log8000>\log5040$，其见证值随价格递减，故价格 $1/25$ 的下界覆盖整个初始胞腔。切换时两个配置的目标相等，胞腔间没有遗漏端点。

对固定 $\lambda$，见证函数导数为 $1/(x\log x)-\lambda$，在 $x\log x=1/\lambda$ 处唯一最大。对 $40000\le n\le10^{30000}$，取 $x=\log n$ 和 $\lambda=1/(x\log x)$。有限端点比较

$$
(\log40000)\log\log40000>25,\qquad
(30000\log10)\log(30000\log10)<10^6
$$

使此价格落在认证区间，故

$$
\gamma+\log\log\log n-\log Z(n)\ge K(\lambda)>\delta.
$$

对 $8000\le n\le40000$，价格 $1/25$ 的支持线给出以下差的下界（$x=\log n$）：

$$
\gamma+\log\log x-\log(403/105)-\frac{x-\log5040}{25}.
$$

此函数在 $[\log8000,\log40000]$ 凹，两个端点都为正，故全区间为正。最后 $5041\le n\le7999$ 的 $2959$ 个整数以精确约数和及向外对数界逐个覆盖。指数函数严格递增，以上对数差为正即给出 Robin 不等式。 $\square$

该证书使用分母 $2^{128}$ 的整数区间和 $100$ 项 atanh 对数展开；$z=(a-b)/(a+b)\in[0,1/3]$ 时，截断尾不超过 $2z^{201}/(201(1-z^2))$，一般正有理数先按二次幂缩放。Euler 常数以 $H_m-\log m-1/m<\gamma<H_m-\log m$、$m=10^6$ 夹住。非初始胞腔最小下端约为 $0.0002461836616312356422357908016$，显示小数仅作读数，符号判断取整数区间端点。对应的完整数据可由 [price_band.py](../../reports/fib-robin-boundary/price_band.py) 重建；小结果在 [price_band.json](../../reports/fib-robin-boundary/price_band.json)。价格低于 $10^{-6}$ 的范围没有被这张证书覆盖。

## 86. 文献停止规则、必要核与可复用状态

**定义 86.1（五方向停止观测）。** 对 $n>5040$，只观测下列任意一个模数的非零余数，就足以应用已有文献中的 Robin 定理：

$$
2^{21},\qquad3^{13},\qquad5^9,\qquad7^7,\qquad11^6.
$$

具体对应的指数条件分别为 $v_2(n)\le20$、$v_3(n)\le12$、$v_5(n)\le8$、$v_7(n)\le6$、$v_{11}(n)\le5$。$2,5$ 两项引自 Christian Axler, *On Robin's inequality*, The Ramanujan Journal 61 (2023), 909–919, [Theorem 3](https://link.springer.com/article/10.1007/s11139-022-00683-0)；$3,7,11$ 三项引自 Alexander Hertlein, *Robin's inequality for new families of integers*, Integers 18 (2018), A71, [作者版本 v2 的 Theorem 2](https://arxiv.org/pdf/1612.05186v2)。这些是已发表结论的条件匹配，不在此重证其解析定理，也不作为新发现。

**推论 86.2（可能反例的语义必要核）。** 若正整数 $n>5040$ 不满足 Robin 严格不等式，则

$$
2^{21}3^{13}5^9 7^7 11^6\mid n.
$$

因此在同源 DAG 上，可能反例必须同时位于这五个零余数纤维中；任何一个非零方向即可停止当前 Robin 判定。

**证明。** 对五个已发表的充分条件分别取逆否命题，得到各指数的必要下界；五个素数不同，所需素数幂两两互素，故可合成整除乘积。这是必要条件，不是反例存在性，也不是满足该整除条件就违反 Robin。 $\square$

**推论 86.3（Fibonacci 样本只需一个奇偶读数）。** 按 $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$，$N=5040F_{19}$ 满足 Robin 不等式。

**证明。** 模 $2$ 的连续对按 $(0,1),(1,1),(1,0)$ 循环，故 $F_j$ 为偶数当且仅当 $3\mid j$。于是 $F_{19}$ 为奇数；递推的正性给出 $F_{19}>1$。由 $5040=16\cdot315$ 得 $v_2(N)=4\le20$ 且 $N>5040$，直接应用 Axler 的条件。不需要求出 $F_{19}$ 的完整数值或其素因子。 $\square$

**命题 86.4（任务停止不等于状态闭包）。** 用一个充分条件把当前节点标为“Robin 安全”，只允许停止该节点的当前任务；若将此标签作为以后任意 Add/Mul 的唯一输入，既没有保留模求值状态，也没有保留该充分条件。

**证明。** 精确指数 $v_2(n)=4$ 给出 $n\equiv16\pmod{32}$，但 $2n\equiv0\pmod{32}$，$n+16\equiv0\pmod{32}$；原来的精确指数状态已不保持，虽然 $2n$ 仍满足更宽的 Axler 条件 $v_2\le20$。若乘以 $2^{17}$，指数变为 $21$，这个 $2$ 方向的停止条件也不再适用。更一般地，安全标签合并了不同余数，无法决定下一次加法或乘法的余数。要复用计算，须保留源关系、节点操作及所需模数上的值，或另证可在后续运算下保持的性质。此处否定的是证书与状态的任意运算闭包，不是在声称上述新整数违反 Robin。 $\square$

## 87. 有限参考最优值与逐素数正储备

**定义 87.1（参考层与实际层）。** 对实数 $x>1$，令 $\lambda_x=1/(x\log x)$。对素数 $p$ 与整数 $a\ge0$，定义

$$
Q_p(a)=\sum_{k=1}^a\frac1{kp^k},\qquad
G_p(a)=\sum_{k=0}^a p^{-k},\qquad
v_p(x)=\max\bigl(\{0\}\cup\{k\ge1:p^k\le x\}\bigr).
$$

这里 $v_p(x)$ 是参考层数，不是实数 $x$ 的算术赋值。令 $a_p$ 是 $\log G_p(a)-\lambda_x a\log p$ 的任一最优整数指数，定义

$$
R_p(x)=Q_p(v_p(x))-\lambda_xv_p(x)\log p
-\bigl(\log G_p(a_p)-\lambda_xa_p\log p\bigr).
$$

**定理 87.2（前缀支配与逐项非负）。** 对所有素数 $p$、整数 $a\ge0$，$Q_p(a)\ge\log G_p(a)$，且 $a\ge1$ 时严格。参考目标 $Q_p(a)-\lambda_xa\log p$ 在 $a=v_p(x)$ 取得最大值。因此

$$
\begin{aligned}
R_p(x)={}&\bigl[Q_p(v_p(x))-\lambda_xv_p(x)\log p
-Q_p(a_p)+\lambda_xa_p\log p\bigr]\\
&+\bigl[Q_p(a_p)-\log G_p(a_p)\bigr]\ge0.
\end{aligned}
$$

**证明。** 对 $0<z<1$，置

$$
D_a(z)=\sum_{k=1}^a\frac{z^k}{k}-\log(1+z+\cdots+z^a).
$$

直接求导得

$$
D_a'(z)=\frac{z^a}{1-z}
\left(\frac{a+1}{1+z+\cdots+z^a}-1\right).
$$

$a=0$ 时恒零；$a\ge1$ 时括号严格为正，且 $D_a(0)=0$。代入 $z=1/p$。参考增量 $1/(kp^k)-\lambda_x\log p$ 非负当且仅当 $p^k\log(p^k)\le x\log x$，即 $p^k\le x$。这些增量递减，故取其前缀最大化；在 $x=p^k$ 时最后一个零增量可取可不取。于是所展示的两个括号分别非负。实际层阈值也严格递减，实际并列最优只涉及相邻指数，其目标值相同，因而 $R_p$ 不依赖并列约定。 $\square$

前缀支配不等于增量逐项支配。例如 $p=2,k=2$ 时 $\beta_{2,2}=\log(7/6)>1/8$，不能以 $1/(kp^k)$ 逐层压住实际边际。以上证明明确通过“先比较整个前缀，再取最优值”避免这一错误。

**定理 87.3（有限分解与已有尾积分的对应）。** 定义有限和

$$
\Psi(x)=\sum_{p^k\le x}\log p,\qquad
P(x)=\sum_{p^k\le x}\frac1{kp^k},\qquad
\Phi(x)=\gamma+\log\log x-P(x)+\frac{\Psi(x)-x}{x\log x}.
$$

令 $R(x)=\sum_pR_p(x)$，并取定义 85.1 中无附加整数约束的压力 $M$，则

$$
\boxed{\Delta(\lambda_x):=\gamma+\log\log x-\frac1{\log x}-M(\lambda_x)
=\Phi(x)+R(x).}
$$

每个 $x>1$ 的上述素数和都只有有限支撑，且 $R(x)\ge0$。

**证明。** $p\ge x$ 时，实际第一层阈值小于 $1/(p\log p)\le\lambda_x$，故实际最优指数为零；参考在 $p=x$ 可能有一层，但其参考目标为零。因此 $R_p=0$ 对所有 $p\ge x$ 成立。求和给出

$$
R(x)=P(x)-\lambda_x\Psi(x)-M(\lambda_x).
$$

代入 $\Phi$ 且用 $\lambda_xx=1/\log x$ 即得恒等式；非负性来自定理 87.2。 $\square$

这里的 $\Phi$ 正是 [ZECKENDORF_EULER_5040.md](ZECKENDORF_EULER_5040.md) 中“两个有限素数幂求和”之后的“定理 1.1：尾积分的有限算式”的 $I_\psi$（该处 $M_0=P$），$R$ 正是随后“定理 1.2：压力余量的精确二分解”的 $D_{\mathrm{disc}}$，条件是两处使用同一实际最优配置与同一个压力。有限恒等式不是本节发明；本节补充的是任意有限尺度下的逐素数非负性和下一条显式子储备。若使用受限整数域的压力，必须另证其与 $M$ 相等的适用域，不能直接代换。

上述既有积分表达为

$$
I_\psi(x)=\int_x^\infty(\Psi(t)-t)
\frac{\log t+1}{t^2\log^2t}\,dt.
$$

其推导依赖经典有效素数定理、Stieltjes 分部积分与 Mertens 极限；Mertens 背景可参见 Jared Duker Lichtman, *Mertens' prime product formula, dissected*, [arXiv:2002.03361v3, Theorem 1.1](https://arxiv.org/html/2002.03361v3)。本节有限分解本身不需数值计算无穷尾。此积分权重来自 $-d(1/(x\log x))/dx$；它与此前 $q(x)=\log(1+1/x)/\log x$ 所生成的尾权重不同，不能把两者的积分、常数或已证界混用。

**定理 87.4（显式正子储备）。** 令

$$
B(x)=\sum_{\substack{p\text{ 素数}\\\sqrt{2x}\le p\le x-1}}
\left(\frac1p-\log(1+1/p)\right).
$$

则 $R(x)\ge B(x)\ge0$；求和区间含素数时 $B(x)>0$。无条件的素数定理给出

$$
B(x)\sim\frac1{\sqrt2\sqrt x\log x}\qquad(x\to\infty).
$$

**证明。** 对区间内的 $p$，$p^2\ge2x>x$ 且 $p<x$，所以 $v_p(x)=1$。实际第一层满足

$$
\log(1+1/p)>\frac1{p+1}\ge\frac1x>\lambda_x\log p.
$$

第二层满足 $\beta_{p,2}<1/p^2<\lambda_x\log p$，最后一步来自
$p^2\log p\ge x\log(2x)>x\log x$。于是 $a_p=1$ 唯一，$R_p=1/p-\log(1+1/p)>0$。其余方向非负，得到子储备下界。又 $1/p-\log(1+1/p)=1/(2p^2)+O(p^{-3})$。素数定理和部分求和给出 $\sum_{p\ge t}p^{-2}\sim1/(t\log t)$；取 $t=\sqrt{2x}$，减去 $p>x-1$ 的 $O(1/(x\log x))$ 尾并控制三次项，即得所述常数。该渐近式没有提供一个已指定的有限起点。 $\square$

## 88. 连续胞腔证书与未解决的尺度条件

**命题 88.1（事件连续性与全局下界的条件）。** $\Phi$ 在每个素数幂事件 $x=p^k$ 连续。在无事件区间固定 $C=\Psi(x)$、$P_0=P(x)$ 后，若 $C>1$，则对所有 $x>1$

$$
\gamma+\log\log x-P_0+\frac{C-x}{x\log x}
\ge\gamma+\log\log C-P_0.
$$

在指定闭区间上的最小点是把 $C$ 截到该区间后的点。$C\le1$ 时不得使用右侧的 $\log\log C$。

**证明。** 在事件 $t=p^k$，$\Delta P=1/(kt)$，$\Delta\Psi=\log p$，故 $\Delta\Phi=-1/(kt)+\log p/(t\log t)=0$。在无事件处，对所展示的函数求导得

$$
\Phi'(x)=\frac{(x-C)(\log x+1)}{x^2\log^2x}.
$$

当 $C>1$ 时，全定义域上的唯一最小点为 $C$，限制区间时按导数符号截断。 $\square$

**定理 88.2（有限连续区间）。** 在 $144\le x\le121393$ 上，有限区间证书给出

$$
\Phi(x)+B(x)>\frac{13}{100000},\qquad
\Phi(x)\ge-\frac1{2\sqrt x\log x}.
$$

因此在同一区间 $\Delta(\lambda_x)>13/100000$。

**证明。** 以素数幂事件和两个端点切分为 $11493$ 个区间 $[a,b]$；内部使用左端之后的常数 $C=\Psi(a)>1$、$P_0=P(a)$，右端可由 $\Phi$ 的连续性接上。命题 88.1 提供整个区间的共同下界

$$
L_{a,b}=\gamma+\log\log\Psi(a)-P(a).
$$

对 $a\le x\le b$，所有满足 $p^2\ge2b$ 且 $p\le a-1$ 的素数都属于 $B(x)$，因此

$$
\Phi(x)+B(x)\ge L_{a,b}
+\sum_{\substack{p^2\ge2b\\p\le a-1}}
\left(\frac1p-\log(1+1/p)\right).
$$

此外 $\sqrt x\log x$ 递增，故

$$
\Phi(x)+\frac1{2\sqrt x\log x}
\ge L_{a,b}+\frac1{2\sqrt b\log b}.
$$

逐个区间用向外整数区间验证这两式右侧，第一式最小认证下端约为 $0.0001387077093931118879802602466$（区间 $[120539,120551]$），严格超过 $13/100000$；第二式最小认证下端约为 $0.0001234545027142578218122253261>0$（区间 $[118973,119027]$）。这些是下界表达式的最小下端，不宣称是实际函数的精确最小值。所有区间的并覆盖闭区间；$121393$ 本身不是素数幂，末区间无遗漏的单点。再用 $R\ge B$ 即得压力差结论。 $\square$

该有限证书所需数据是 $11425$ 个素数与 $11539$ 个素数幂事件。Euler 常数取 $m=10000$ 的界

$$
H_m-\log m-\frac1{2m}<\gamma<
H_m-\log m-\frac1{2(m+1)},
$$

它可由梯形积分误差逐项夹住 $H_m-\log m-\gamma$ 得到。其余对数界同 §85，平方根界来自整数平方根。有限算术与复现入口为 [finite_reserve.py](../../reports/fib-robin-boundary/finite_reserve.py) 和 [finite_reserve.json](../../reports/fib-robin-boundary/finite_reserve.json)；连续区间覆盖依赖上述导数、事件抵消与子储备论证，不能把离散采样冒充连续覆盖。

**命题 88.3（障碍函数的精确局部最小点）。** 在无事件区间上令 $V(x)=\Phi(x)+1/(2\sqrt x\log x)$，仍以 $C=\Psi$、$P_0=P$ 表示该区间的常数。置

$$
T(x)=x-\frac{\sqrt x(\log x+2)}{4(\log x+1)}.
$$

则

$$
V'(x)=\frac{\log x+1}{x^2\log^2x}(T(x)-C),\qquad
T'(x)=1-\frac{\log x(\log x+3)}{8\sqrt x(\log x+1)^2}>0.
$$

若 $C>1/2$，唯一 $r>1$ 满足 $T(r)=C$，在区间上的最小点为截断后的 $r$。若 $r$ 在区间内，则

$$
V(r)=\gamma+\log\log r-P_0+
\frac1{4\sqrt r(\log r+1)}.
$$

**证明。** 求导并合并项即得两导数。令 $t=\log x>0$，有 $t(t+3)/(t+1)^2\le9/8$ 且 $\sqrt x>1$，故 $T'$ 中减去的项小于 $9/64$。又 $T(1+)=1/2$，$T(x)\to\infty$，存在唯一根，导数变号给出最小点。在 $V(r)$ 中代入 $C-r=-\sqrt r(\log r+2)/(4(\log r+1))$，约分即得最后一式。 $\square$

这一局部判据展示仍缺的联合约束：须控制同一素数历史给出的 $(P_0,C)$，而不是把分别可达的最优读数当成同时可达。有限区间证书和 $R_p\ge0$ 均没有证明存在 $X_0>1$ 使所有 $x\ge X_0$ 都满足 $\Phi(x)\ge-1/(2\sqrt x\log x)$。若将来取得这个统一界，则由定理 87.4 可选常数 $1/2<c<1/\sqrt2$，在共同的充分大起点后有 $\Delta(\lambda_x)\ge(c-1/2)/(\sqrt x\log x)>0$；这里的前提仍待证明。本批不据此宣称 RH 等价式或 RH 结论。

## 89. 第 75 节纤维定义域与合数块完整性的更正

**命题 89.1（补足第三行指数边界）。** 第 75 节固定母体 $n=2^{A_2}3^{A_3}5^{A_5}7^{A_7}$ 后，非空纤维域必须改读为

$$
\mathcal F_n^{\mathrm{corr}}=
\left\{(u,v,w)\in\mathbb N^3:
0\le v\le A_3,\quad
\max(0,u-A_2,w-A_5)\le\min(A_7,u,w)\right\}.
$$

在这个域上，第 75 节的 $k_{\min}$、$k_{\max}$ 与 $\Omega_{u,v,w}$ 公式保持成立，且

$$
Z(n)=\sum_{(u,v,w)\in\mathcal F_n^{\mathrm{corr}}}\Omega_{u,v,w}.
$$

原先只写 $k_{\min}\le k_{\max}$ 的定义域遗漏了 $v\le A_3$；后续使用必须附上此条件。

**证明。** 由 $b_2=u-k$、$b_3=v$、$b_5=w-k$、$b_7=k$，四个条件 $0\le b_p\le A_p$ 等价于新定义域及 $k_{\min}\le k\le k_{\max}$。逐纤维求倒数和再相加就是对每个约数恰计一次。对 $5040$ 有 $A_3=2$；遗漏条件会允许 $(u,v,w;k)=(0,3,0;0)$，数值为 $27$，但 $27\nmid5040$。第 75 节已将局部漏项计算中的 $b$ 限于 $0,1,2$，故其 $13/112$ 漏项计算在更正域内保持原结论。 $\square$

**命题 89.2（合数值块的去重不保证约数完整性）。** §81–82 中，按整数值去重可以避免重复计数，但不能单独保证完整的算术约数族。对一个 $[2+13]$ 块，若只允许整块乘法子配置，其值集合为 $\{1,15\}$；算术约数 $3,5$ 没有被表示。

**证明。** 一个不可拆块的重数只有 $0,1$，所以只产生空积和整个块。去重是对现有值取商，不能增添不存在的 $3,5$；其倒数和为 $1+1/15=16/15$，而

$$
Z(15)=(1+1/3)(1+1/5)=\frac85.
$$

要把块子配置的倒数和识别为 $Z(n)$，必须另外证明该语言对 $n$ 的全部算术约数既完整又按值唯一，或提供包含全部约数的精确纤维权重；合数块仅作值去重不满足前一要求。当前四个素数值块 $2,3,5,7$ 的独立重数模型满足它；未经该认证的递归合数块没有自动的 Euler 轴资格。 $\square$

本批的新增推导和有限证书是理论参考输入，未成为新增 Lean 声明。既有 `IntegerSwap`、`GoldenResourceSupremum`、`GoldenResourceOptimalInteger` 与 `Robin.SevenSmooth` 的源结果只在其原条件内复用；它们不以内核证明的名义承担本批的数值证书、连续转移或尚未解决的无限尺度条件。

## 追加锚（递归块 Robin 主编码批次后）

## 90. 粗糙剩余量的精确极值与携证 Bellman 递推

本节至第 97 节追加有限极值、联合解析状态、递归储备、来源指标停止和未来乘法比较。沿用 $Z(n)=\sigma(n)/n=\prod_pG_p(v_p(n))$，其中 $G_p(a)=\sum_{j=0}^ap^{-j}$。这些是带完整条件的纸面推导和有限实验；以下没有新增 Lean 声明。第 83–89 节的有限证书不因本批的最终尺度等价式而扩大验证范围。

**定理 90.1（包含零指数的规范化）。** 固定整数 $y\ge1,B\ge1$，称 $n$ 为 $y$-rough，若每个素因子均严格大于 $y$，并允许 $n=1$。令 $q_0<q_1<\cdots$ 为所有大于 $y$ 的连续素数。则

$$
U_y(B)=\max_{\substack{1\le n\le B\\p\mid n\Rightarrow p>y}}Z(n)
$$

在某个 $n=\prod_{i=0}^{s-1}q_i^{a_i}$ 处取得，其中 $a_0\ge\cdots\ge a_{s-1}>0$；$s=0$ 表示 $1$。

**证明。** 在直到原最大素因子的有限素数表上补齐零指数。若 $p<q$ 且 $0\le a<b$，交换 $p^aq^b$ 为 $p^bq^a$ 将整数乘以 $(p/q)^{b-a}<1$。同时

$$
\frac{G_p(k+1)}{G_p(k)}=1+\frac1{p+p^2+\cdots+p^{k+1}},\qquad
\frac{G_p(b)}{G_p(a)}=
\prod_{k=a}^{b-1}\left(1+\frac1{p+\cdots+p^{k+1}}\right).
$$

每个因子随 $p$ 严格递减，所以 $G_p(b)G_q(a)>G_p(a)G_q(b)$，其余素数的因子不变，$Z$ 严格增大。这里 $a=0$ 同样有效，因而漏掉较小允许素数也能被修正。反复交换相邻逆序，有限指数表的逆序数严格减少，终止于非增排列；正指数遂形成连续前缀。整数不增、$Z$ 不减、rough 条件保留。原可行整数集合有限非空，故最大值存在且可在规范族取得。这个交换步骤正是既有 `D5.S3.Arith.ExponentExchange.IntegerSwap.prime_exponent_swap` 的内容，包括较小指数可以为零；从局部交换到整个规范族的归约在这里给出纸面证明。 $\square$

**定理 90.2（完整分支、上界与取到）。** 状态 $V(i,b,h)$ 表示从 $q_i$ 起、剩余整数预算 $b\ge1$、首指数上限 $h\ge0$ 的规范后缀最大权重。它满足有限递推

$$
V(i,b,h)=\max\left(\{1\}\cup
\left\{G_{q_i}(a)V\left(i+1,\left\lfloor b/q_i^a\right\rfloor,a\right):
1\le a\le h,\ q_i^a\le b\right\}\right).
$$

令 $h_0=\max\{a\ge0:q_0^a\le B\}$，则 $U_y(B)=V(0,B,h_0)$。

**证明。** 后缀为空时整数和权重都为 $1$。非空时其首指数恰属于所列范围；余下指数至多为 $a$，其乘积至多为 $\lfloor b/q_i^a\rfloor$。反向把任一合法首幂与合法子后缀相乘，也恰是父状态的合法候选。因此分支既无遗漏也无额外候选。零指数不是“跳过当前素数继续搜索”，而是终止整个后缀。

每个非空分支将预算至少除以 $2$，所以路径长度有限；每层指数分支亦有限。对终端向根归纳：终端无正指数分支，最大值及见证均为 $1$。若所有子状态已有上界及取到见证，则每个父候选至多为递推右侧的最大值；选择取到此最大值的分支，把首幂乘以子见证，即给出预算内、指数非增且权重恰等于该最大值的父见证。由此同时证明上界和取到，而不只给出一个候选下界。

有限证书不必列出所有 $p\le B$，只须列出每个可达状态所需的连续素数，包括终端状态的当前素数。检查器逐个验证素性和中间无漏素数；只要当前幂能放入预算，就要求完整的下一状态。少列一个仍需使用的素数、删掉一个可达子状态或省略一个允许指数分支都会被拒绝。按素数下标递减处理是拓扑归纳，因为每条边严格增加下标；共享子状态可把证明树压成 DAG。检查器分别核对全部候选不超过所报值及某合法分支取到所报值，并拒绝不可达额外状态。它认证的是有限规范递推；定理 90.1 的全整数归约是检查器之外的数学前提，不是 Python 或新增内核定理。 $\square$

**命题 90.3（精确有限读数与松弛边界）。** `rough_max.py` 生成、`rough_max_check.py` 独立检查下列有理数最大值：

| rough 阈值与预算 $(y,B)$ | 取到整数 | $U_y(B)$ |
|---|---:|---:|
| $(7,1000)$ | $143$ | $168/143$ |
| $(7,4181)$ | $2431$ | $3024/2431$ |
| $(7,46188)$ | $26741$ | $33516/26741$ |
| $(7,10^6)$ | $508079$ | $35280/26741$ |
| $(7,10^{12})$ | $388705330871$ | $30888345600/20458175309$ |
| $(1,5040)$ | $5040$ | $403/105$ |

**证明与有限证据。** 各行保留完整有限分支证书，独立检查器按定理 90.2 的归纳合同计算精确分数。第五行有 134 状态、140 分支；第六行有 63 状态、66 分支。可移植回归还对 $y\in\{1,2,7,13\}$、所有 $1\le B\le256$ 作 1,024 次直接约数和比较，并拒绝八种被破坏的证书；这些回归不替代全称规范化证明。尤其当 $1\le R\le4181$ 且 $\gcd(R,210)=1$ 时，$R$ 为 7-rough，且与 $5040$ 互素，故

$$
Z(5040R)=\frac{403}{105}Z(R)
\le\frac{403}{105}\frac{3024}{2431}=\frac{4464}{935}.
$$

若还规定同余、来源或历史约束，交换操作未必保留它们。此时 $U_y(B)$ 仍是删除这些约束后的安全上界，但其取到整数不必属于原纤维，也不能冒称原受限极值。文献给出的布尔停止条件只认证相应整数满足 Robin；它既不输出这一量化极值，也不保存后续运算需要的关系状态。 $\square$

**命题 90.4（支持直线只有上界保证）。** 对 $\lambda>0$ 定义

$$
H_y(\lambda)=\sup_{n\text{ 为 }y\text{-rough}}
\{\log Z(n)-\lambda\log n\}.
$$

则

$$
\log U_y(B)\le
\inf_{\lambda>0}\{H_y(\lambda)+\lambda\log B\}.
$$

**证明。** 每个 $n\le B$ 满足 $\log Z(n)\le H_y(\lambda)+\lambda\log n\le H_y(\lambda)+\lambda\log B$，先取可行最大值，再取价格下确界。固定正价格时各素数的边际收益递减，只有有限个首层收益能超过价格，所以压力有限。该论证只给支持线的上包络；离散整数预算未提供自动的强对偶等式。 $\square$

## 91. 单调强制核、不可行状态与总指数预算

**定理 91.1（保留强制核的规范化）。** 设 $p_1=2<p_2<\cdots$ 为连续素数，

$$
M=\prod_{i=1}^rp_i^{\ell_i},\qquad
\ell_1\ge\ell_2\ge\cdots\ge\ell_r>0,
$$

并在 $i>r$ 置 $\ell_i=0$，允许空核 $M=1$。若 $B<M$，集合 $\{n:M\mid n,1\le n\le B\}$ 为空；否则其 $Z$ 最大值在总指数非增的连续素数前缀取得。

**证明。** 任意可行总指数 $a_i\ge\ell_i$ 若在 $i<j$ 满足 $a_i<a_j$，交换后

$$
a'_i=a_j\ge a_i\ge\ell_i,\qquad
 a'_j=a_i\ge\ell_i\ge\ell_j.
$$

因此强制下界保留。定理 90.1 的交换又减小整数、增大权重；同一终止论证给出规范化。必须交换 $n=Mt$ 的总指数；重叠素数的指数相加，而非把 $Z(Mt)$ 写成 $Z(M)Z(t)$。例如 $Z(8)=15/8$，但 $Z(4)Z(2)=21/8$。 $\square$

**定理 91.2（强制后缀的精确剪枝）。** 写

$$
C_i=\prod_{j=i}^rp_j^{\ell_j}\ (i\le r),\qquad C_i=1\ (i>r).
$$

状态 $V_M(i,b,h)$ 不可行当且仅当 $h<\ell_i$ 或 $b<C_i$；不可行值记为独立符号 $\bot$，不是空后缀的 $1$。可行状态满足

$$
V_M(i,b,h)=\max\left(
\{1:i>r\}\cup
\left\{G_{p_i}(a)V_M\left(i+1,\left\lfloor b/p_i^a\right\rfloor,a\right):
\max(1,\ell_i)\le a\le h,\ p_i^a\le b,
\text{子状态可行}\right\}\right).
$$

根为 $(1,B,\lfloor\log_2B\rfloor)$。对允许的首指数 $a$，余核预算剪枝恰为

$$
p_i^aC_{i+1}>b
\quad\Longleftrightarrow\quad
\left\lfloor b/p_i^a\right\rfloor<C_{i+1}.
$$

**证明。** 不可行的两个条件显然必要。若均不成立，恰取剩余下界指数就能完成后缀：单调性保证后续每一项符合上一指数上限；核已结束时取空后缀。因此它们也充分。空分支只在强制核结束后允许，但结束后仍允许继续加入更大素数。每个非空可行后缀唯一分解为首幂和子状态。剪枝使用整数商等价式，没有浮点预算。按定理 90.2 同时归纳上界和见证即可；独立检查器重建每个允许分支及每次剪枝，不信任证书自报的可行性。 $\square$

**命题 91.3（非单调核反例与四个有限预算）。** 下界单调性不能省略。$M=150=2\cdot3\cdot5^2$、$B=1200$ 的八个倍数中，真最大值为 $Z(1200)=961/300$；规范子族仅有 $900$，其值为 $2821/900$，损失 $31/450$。把 $1200=2^4\cdot3\cdot5^2$ 的后两指数交换成 $720$，已经丢掉强制 $5^2$。

对

$$
M_* =2^{21}3^{13}5^97^711^6
=9527493263501079465984000000000
$$

则 `core_max.py` 和独立 `core_max_check.py` 给出：

| 强制核预算 | 取到整数 | 精确最大值 | 状态数 | 余核剪枝数 |
|---|---|---|---:|---:|
| $M_*$ | $M_*$ | $72365886696479164830959537/15037079014364077440000000$ | 6 | 95 |
| $2M_*$ | $2M_*$ | $434195371939002974359607059/90222474086184464640000000$ | 11 | 110 |
| $10M_*$ | $6M_*$ | $43060704045486908310829897/8947683380448046080000000$ | 36 | 166 |
| $1000M_*$ | $884M_*$ | $12474190844475097810717/2273178989321856000000$ | 363 | 563 |

**证明与有限证据。** 非单调反例由直接约数枚举计算八个候选。四个单调核证书按完整分支归纳检查，另对每个预算中的全部实际倍数 $M_*t$ 独立枚举、合并素数指数后比较；末行见证为 $M_*2^2\cdot13\cdot17$。保留的回归覆盖长度至多 3、正指数取自 $\{1,2,3\}$ 的所有非增核加空核，共 20 个 profile，对预算 1 至 180 作 3,600 次直接约数和比较，其中 1,802 次正确判空，并拒绝六种破坏证书。 $\square$

**命题 91.4（Robin 分母必须使用同一整数）。** 记上述极值为 $U_M(B)$。对 $e<A\le B$，若

$$
U_M(B)<e^\gamma\log\log A,
$$

则区间 $[A,B]$ 的每个 $M$ 倍数均满足 Robin 严格不等式。

**证明。** $Z(n)\le U_M(B)$，且 $\log\log n\ge\log\log A>0$。只与右端点的 $e^\gamma\log\log B$ 比较不足以覆盖较小 $n$。另一路线是保留同一对象的联合对 $(n,Z(n))$，直接最大化 $Z(n)/\log\log n$；本节每状态单个 $Z$ 最大值不等于已优化 Robin 比值。若所有可行整数均大于 $e$，规范化使正分母下降、分子上升，仍可用于这种联合优化，但必须保留相应信息。 $\square$

## 92. 联合事件状态、截断最小点与最终障碍的 RH 强度

沿用第 87 节的右连续和式 $P(x)=\sum_{m\le x}\Lambda(m)/(m\log m)$、$\Psi(x)=\sum_{m\le x}\Lambda(m)$ 及

$$
\Phi(x)=\gamma+\log\log x-P(x)+\frac{\Psi(x)-x}{x\log x}
=\int_x^\infty(\Psi(v)-v)\frac{\log v+1}{v^2\log^2v}\,dv.
$$

它正是 [ZECKENDORF_EULER_5040.md](ZECKENDORF_EULER_5040.md) 在“两个有限素数幂求和”后的“定理 1.1：尾积分的有限算式”中的 $I_\psi$；同处“定理 1.2：压力余量的精确二分解”的 $D_{\mathrm{disc}}$ 就是本卷的 $R$。这里复用有限公式，不把它重新命名为新发现。以下归一化状态写作 $\mathcal Z$，以区别整数的 $Z(n)$。

**定理 92.1（精确双状态事件递推）。** 令

$$
\mathcal Z(x)=\sqrt x\log x\,\Phi(x),\qquad
 e(x)=\frac{\Psi(x)-x}{\sqrt x}.
$$

对连续素数幂事件 $1<a<b=p^k$，取右连续状态，并置

$$
\sigma=\sqrt{a/b},\quad
\rho=\sqrt{b/a}\frac{\log b}{\log a},\quad
K_0=\sqrt b\log b\log\frac{\log b}{\log a}-\frac{b-a}{\sqrt b}.
$$

则

$$
\begin{aligned}
e(b)&=\sigma e(a)+\frac{\log p-(b-a)}{\sqrt b},\\
\mathcal Z(b)&=\rho\mathcal Z(a)+(\sigma-\rho)e(a)+K_0.
\end{aligned}
$$

**证明。** 在旧区间令 $C=\Psi(a)$、$P_0=P(a)$ 不变，有限公式给出

$$
\Phi(b)-\Phi(a)=\log\frac{\log b}{\log a}
+C\left(\frac1{b\log b}-\frac1{a\log a}\right)
-\left(\frac1{\log b}-\frac1{\log a}\right).
$$

事件处 $\Delta P=1/(kb)$ 与 $\Delta\Psi/(b\log b)=\log p/(b\log b)$ 相等，所以 $\Phi$ 连续；上述旧区间式可以延伸至右端点。代入 $C=a+\sqrt a\,e(a)$，再乘以 $\sqrt b\log b$，即得第二式；第一式保留 $\Psi$ 的脉冲。 $\square$

若 $H=\mathcal Z+1/2$，则 $H(b)=\rho H(a)+(\sigma-\rho)e(a)+K_0+(1-\rho)/2$。因为 $\sigma-\rho<0$，单个标量条件 $H(a)\ge0$ 不是归纳合同。两次极值若来自不同素数历史，也不能当作同一个 $(H,e)$ 状态。事件间令 $t=\log x$，直接求导得

$$
\frac{d\mathcal Z}{dt}=\left(\frac12+\frac1t\right)\mathcal Z-
\left(1+\frac1t\right)e,\qquad
\frac{de}{dt}=-\sqrt x-\frac e2.
$$

在障碍 $\mathcal Z=-1/2$ 上，导数指向可行侧需要 $e\le-(t+2)/(4(t+1))$；这是局部切向条件，尚不是每条实际素数历史满足它的定理。

**定理 92.2（障碍余量的完整截断规则）。** 在事件间冻结 $\Psi=C,P=P_0$，令 $V(x)=\Phi(x)+1/(2\sqrt x\log x)$。定义

$$
T(x)=x-\frac{\sqrt x(\log x+2)}{4(\log x+1)}.
$$

对 $x>1$ 有

$$
V'(x)=\frac{\log x+1}{x^2\log^2x}[T(x)-C],\qquad
T'(x)=1-\frac{\log x(\log x+3)}{8\sqrt x(\log x+1)^2}>0.
$$

若 $C>1/2$，唯一根 $r=T^{-1}(C)$ 在闭区间 $[a,b]$ 上截断后的点是最小点；内点情形的最小值为

$$
V(r)=\gamma+\log\log r-P_0+\frac1{4\sqrt r(\log r+1)}.
$$

若 $C\le1/2$，最小点是左端点。这里的右端点值按连续延拓取值。

**证明。** 求导得两式。写 $t=\log x>0$，$t(t+3)/(t+1)^2\le9/8$，故 $T'$ 中减项小于 $9/64$；且 $T(1+)=1/2,T(\infty)=\infty$。导数变号给出两种情形。在内点代入 $C-r=-\sqrt r(\log r+2)/(4(\log r+1))$ 得所示正修正项。对不带障碍修正的 $\Phi$，导数为 $(\log x+1)(x-C)/(x^2\log^2x)$，所以全域最小值 $\gamma+\log\log C-P_0$ 只在 $C>1$ 才适用；闭区间最小点是截断的 $C$。若 $C\le1$，应使用左端点，不能计算实数域外的 $\log\log C$。 $\square$

**定理 92.3（最终障碍等价于 RH）。** 在经典有效素数定理、积分显式公式、零点计数与对称性、Landau 非负 Laplace 变换定理下，

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\exists X_0>1\ \forall x\ge X_0,
\quad\Phi(x)\ge-\frac1{2\sqrt x\log x}.
$$

更一般地，任意有限 $K\ge0$ 的这种最终下界都推出 RH；RH 反向给出每个 $K>C_\gamma$ 的最终下界，其中 $C_\gamma=2+\gamma-\log(4\pi)<1/2$。不声称反向对所有 $K\ge0$ 成立。

**证明。** 使用同一理论卷“二、一个更强的定理：只证明下界就足够”及“定理 2.1：单边界判据”的零点响应结构，但把所需正逆变换与收敛条件写全。置

$$
J(x)=\int_x^\infty\frac{\Psi(v)-v}{v^2}\,dv,\qquad
q(x)=\frac{\log x+1}{\log^2x},\qquad r(x)=q(x)^{-1}.
$$

有效 PNT 的无条件估计 $\Psi(v)-v=O(v e^{-c\sqrt{\log v}})$ 给出，令 $s=\sqrt{\log x}$，

$$
J(x)=O((s+1)e^{-cs}),\qquad \Phi(x)=O(e^{-cs}/s).
$$

这些估计保证 $q(x)J(x)\to0,r(x)\Phi(x)\to0$，且下列分部积分的尾项绝对收敛：

$$
\begin{aligned}
\Phi(x)&=q(x)J(x)+\int_x^\infty q'(v)J(v)\,dv,\\
J(x)&=r(x)\Phi(x)+\int_x^\infty r'(v)\Phi(v)\,dv,\\
q'(v)&=-\frac{\log v+2}{v\log^3v},\qquad
r'(v)=\frac{\log v(\log v+2)}{v(\log v+1)^2}>0.
\end{aligned}
$$

第二式是正逆变换。若 $x\ge X_0$ 时 $\Phi(x)\ge-K/(\sqrt x\log x)$，则令 $L=\log x$，利用 $(u+2)/(u+1)^2$ 递减及 $\int_x^\infty v^{-3/2}dv=2/\sqrt x$ 得

$$
J(x)\ge-\frac K{\sqrt x}
\left[\frac L{L+1}+\frac{2(L+2)}{(L+1)^2}\right].
$$

于是 $\sqrt xJ(x)$ 最终有有限下界。经典积分显式公式为

$$
J(x)=-\sum_\rho\frac{x^{\rho-1}}{\rho(1-\rho)}-\frac{\log(2\pi)}x+R_0(x),
\qquad R_0(x)=\sum_{k\ge1}\frac{x^{-2k-1}}{2k(2k+1)}.
$$

零点计重数；标准零点计数保证 $\sum_\rho|\rho(1-\rho)|^{-1}<\infty$。因此

$$
F(t)=\sum_\rho\frac{e^{(\rho-1/2)t}}{\rho(1-\rho)}
=-e^{t/2}J(e^t)-\log(2\pi)e^{-t/2}+e^{t/2}R_0(e^t)
$$

在紧区间上一致绝对收敛，为实连续函数；$|F(t)|\le Ae^{t/2}$。所得 $J$ 下界使 $F$ 最终有上界。结合剩余紧区间的连续性，可选有限常数 $M$ 使 $h(t)=M-F(t)\ge1$ 对所有 $t\ge0$ 成立。其 Laplace 积分收敛横坐标满足 $0\le\sigma_c\le1/2$；下界 $h\ge1$ 排除了负横坐标与负无穷的歧义。

在 $\Re z>1/2$ 可逐项变换：

$$
\mathcal Lh(z)=\frac Mz-
\sum_\rho\frac1{\rho(1-\rho)[z-(\rho-1/2)]}.
$$

避开所列极点的紧集上，高零点项为 $O(|\Im\rho|^{-3})$，故级数正常收敛并给出亚纯延拓。它没有正实极点：实数 $0<s<1$ 上，交错 eta 级数为正而 $1-2^{1-s}<0$，所以 $\zeta(s)<0$，不存在相应实零点。

若 $\sigma_c>0$，Landau 定理要求实点 $\sigma_c$ 为奇点，与上式矛盾。其非负性原理也可直接看出：若能跨过横坐标全纯延拓，取其右侧足够近的实中心 $a$，使 Taylor 圆盘伸到 $a-r<\sigma_c$；导数积分中的 $(-1)^j\mathcal Lh^{(j)}(a)$ 为非负矩，由非负项交换求和与积分，Taylor 和等于 $\int_0^\infty h(t)e^{-(a-r)t}dt<\infty$，违反收敛横坐标的定义。因此 $\sigma_c=0$，Laplace 积分在整个 $\Re z>0$ 全纯。

若有 $\Re\rho_0>1/2$，亚纯表达式在 $z_0=\rho_0-1/2$ 的留数为

$$
-\frac{m_{\rho_0}}{\rho_0(1-\rho_0)}\ne0.
$$

不同位置的零点产生不同极点，同一位置的重数同号相加；其余正常收敛项及 $M/z$ 在此全纯，故该极点不可消去。这与右半平面全纯矛盾，零点反射对称性遂给 RH。此方向未假设 RH，也未以单个振荡项的大小替代无消去论证。

反向明确假设 RH。此时 $\rho(1-\rho)=|\rho|^2>0$，经典零点和为

$$
\sum_\rho\frac1{|\rho|^2}=C_\gamma
=2+\gamma-\log(4\pi)=0.0461914179\ldots.
$$

显式公式给 $|J(x)|\le C_\gamma/\sqrt x+O(1/x)$。由正向变换、$|q'|$ 以及

$$
\int_x^\infty\frac{\log v+2}{v^{3/2}\log^3v}\,dv
\le\frac2{\sqrt x}\frac{\log x+2}{\log^3x}
$$

得

$$
|\sqrt x\log x\,\Phi(x)|
\le C_\gamma\left(1+\frac3{\log x}+\frac4{\log^2x}\right)+O(x^{-1/2}).
$$

因为 $C_\gamma<1/2$，所需最终下界成立。 $\square$

上述经典输入的显式公式与零点对称性见同卷“平滑显式公式”“单边界判据”及 [DLMF §25.10](https://dlmf.nist.gov/25.10)；Landau 的具体非负变换版本与证明已在本证明中列出。有限 Euler 和的 Mertens 背景可参照 J. D. Lichtman, *Mertens' prime product formula, dissected*, [Theorem 1.1](https://arxiv.org/html/2002.03361v3)，但有限素数乘积与 $P(x)$ 的素数幂截断必须区别。这是既有经典工具的纸面综合，不作新原创判据或已编译 Lean 真值声明。它补足第 88 节未作的强度判断；等价式没有证明任何一侧成立。

## 93. 递归储备的显式尾界与双层常数

本节使用无约束压力

$$
\mathcal M(\lambda)=\sum_p\max_{a\ge0}
\{\log G_p(a)-\lambda a\log p\},\qquad
\lambda_x=\frac1{x\log x},\qquad
\Delta(\lambda_x)=\gamma+\log\log x-\frac1{\log x}-\mathcal M(\lambda_x).
$$

若改用受限压力，须另证它与此压力相等的适用域。令 $Q_p(a)=\sum_{k=1}^a1/(kp^k)$、$v_p=\lfloor\log x/\log p\rfloor$，并置

$$
R_p(x)=Q_p(v_p)-\lambda_xv_p\log p
-\max_{a\ge0}\{\log G_p(a)-\lambda_xa\log p\},\qquad R=\sum_pR_p.
$$

第 87 节的同一压力恒等式为 $\Delta(\lambda_x)=\Phi(x)+R(x)$。

**定理 93.1（所有有限尺度的递归尾界）。** 对每个实数 $x>1$ 和整数 $K\ge2$，定义

$$
R_K(x)=\sum_{x^{1/K}<p\le x}R_p(x).
$$

则

$$
0\le R(x)-R_K(x)\le\left(4+\frac2K\right)x^{-K/(K+1)}.
$$

此外，当 $x\ge K^K$ 时，对保留的素数 $p>x^{1/K}$，实际最优指数都满足 $a_p\le K$。

**证明。** 写 $z=1/p$ 及 $D_p(a)=Q_p(a)-\log G_p(a)$。有限几何和给

$$
D_p(a)=-\log(1-z^{a+1})-\sum_{k>a}\frac{z^k}{k},\qquad
\frac{dD_p(a)}{dz}=\frac{z^a}{1-z}
\left(\frac{a+1}{1+z+\cdots+z^a}-1\right).
$$

在 $a=0$ 时它恒为零；在 $a\ge1,0<z<1$ 时导数为正且 $D_p(a)(0)=0$。因此 $D_p(a)\ge0$，又由 $-\log(1-u)<u/(1-u)$ 得

$$
D_p(a)<\frac{z^{a+1}}{1-z^{a+1}}\le2z^{a+1}.
$$

参考目标 $Q_p(a)-\lambda_xa\log p$ 的第 $k$ 个增量非负恰当 $p^k\le x$，所以 $v_p$ 是其最大点，端点允许零增量。逐前缀 $\log G_p(a)\le Q_p(a)$ 给 $R_p\ge0$；在实际最大式中取 $a=v_p$ 则给

$$
0\le R_p(x)\le D_p(v_p)<2p^{-v_p-1}<2/x.
$$

实际边际 $h_p(k)=\log(1+1/(p+\cdots+p^k))$ 严格递减且小于 $p^{-k}$。对 $p\ge x$，首层 $h_p(1)<1/p\le\lambda_x\log p$，故实际最大点为零，参考最大值也为零，$R_p=0$；总储备只有有限支撑。

令 $t=x^{1/(K+1)}$。对 $t<p\le x^{1/K}$，恰有 $v_p=K$，故

$$
R-R_K\le\frac{2\pi(t)}x+2\sum_{t<p\le x^{1/K}}p^{-K-1}.
$$

使用 $\pi(t)\le t$ 和递减函数的整数尾和估计

$$
\sum_{n>t}n^{-K-1}\le t^{-K-1}+\frac{t^{-K}}K
\le\left(1+\frac1K\right)t^{-K}
$$

即得所示常数。这一界无需 PNT。

最后，若 $x\ge K^K,p>x^{1/K}$，则 $p>K$、$\log p>\log x/K$，从而 $p^{K+1}\log p>xp\log p>x\log x$。于是 $h_p(K+1)<\lambda_x\log p$，所有后续边际也为负，最优指数至多 $K$。该结论不能扩展到所有素数：$K=2,x=16,p=2$ 时 $h_2(3)=\log(15/14)>1/15>1/64=\lambda_{16}\log2$，故最优指数至少为 3。 $\square$

**定理 93.2（双候选储备及其渐近主项）。** 对 $\sqrt x<p\le x-1$ 定义

$$
d_1(p)=\frac1p-\log(1+1/p),\qquad
d_2(p,x)=\frac1p-\log(1+1/p+1/p^2)+\lambda_x\log p,
$$

并令 $B_2(x)=\sum_{\sqrt x<p\le x-1}\min\{d_1(p),d_2(p,x)\}$。对所有 $x>1$，该掩码内实际最优指数属于 $\{1,2\}$，并且

$$
R_p(x)=\min\{d_1(p),d_2(p,x)\}>0,\qquad
0\le R(x)-B_2(x)\le5x^{-2/3}+2/x.
$$

使用无条件 PNT 时，

$$
B_2(x)\sim R(x)\sim\frac{c_R}{\sqrt x\log x},\qquad
c_R=2(\sqrt2-1).
$$

**证明。** 掩码内 $v_p=1$，首层满足 $\log(1+1/p)>1/(p+1)\ge1/x>\lambda_x\log p$。第三层则因 $x<p^2,p\ge2$ 而有

$$
\frac{h_p(3)}{\log p}<\frac1{p^3\log p}
\le\frac1{2p^2\log p}<\frac1{x\log x}.
$$

故实际最优只能是 1 或 2，平局不改储备；分别相减正好得到 $d_1,d_2$。$d_1>0$；由 $\log G_p(2)\le Q_p(2)$ 和 $\lambda_x\log p>1/(2p^2)$ 得 $d_2>0$。掩码为空时和为零。$R_2-B_2$ 只含 $(x-1,x]$ 中至多一个素数，使用定理 93.1 的 $K=2$ 和 $R_p<2/x$ 得误差界。

为计算主项，均匀展开 $p>\sqrt x$ 上的两候选：

$$
d_1(p)=\frac1{2p^2}+O(p^{-3}),\qquad
d_2(p,x)=-\frac1{2p^2}+\lambda_x\log p+O(p^{-3}).
$$

取最小值的误差至多为两误差的最大值，求和为 $O(x^{-1})$。置 $p=u\sqrt x$，在固定有界 $u\ge1$ 区间上，

$$
x\min(d_1,d_2)\longrightarrow\frac12\min(u^{-2},1-u^{-2}).
$$

PNT 给该尺度素数的渐近密度 $2\sqrt x/\log x$。对未截断尾部用 $0\le\min(d_1,d_2)\le d_1\le1/(2p^2)$ 及 PNT 分部求和，将 $p>A\sqrt x$ 的归一化贡献界为 $O(1/A)$。先取 $x\to\infty$ 再取 $A\to\infty$，得到

$$
\int_1^{\sqrt2}(1-u^{-2})\,du+
\int_{\sqrt2}^{\infty}u^{-2}\,du=2(\sqrt2-1).
$$

显式误差 $O(x^{-2/3})=o(1/(\sqrt x\log x))$ 把同一主项传给 $R$。这不是某个已指定起点后的显式渐近阈值。 $\square$

## 94. 储备的区间组合、Fibonacci 覆盖与最终价格间隙

**定理 94.1（带质量和位置的精确传输）。** 对 $1<a\le b$ 定义有限二端点量

$$
J_{a,b}=\sum_{a<m\le b}\Lambda(m)(\lambda_m-\lambda_b),\qquad
M_{a,b}=\sum_{a<m\le b}\Lambda(m).
$$

它不同于第 92 节的一变量尾积分 $J(x)$。有

$$
\Phi(b)=\Phi(a)+\log\frac{\log b}{\log a}
+(\Psi(a)-b)\lambda_b-(\Psi(a)-a)\lambda_a-J_{a,b},
$$

且对 $a\le b\le c$，

$$
M_{a,c}=M_{a,b}+M_{b,c},\qquad
J_{a,c}=J_{a,b}+J_{b,c}+(\lambda_b-\lambda_c)M_{a,b}.
$$

**证明。** 用 $P(b)-P(a)=\sum_{a<m\le b}\Lambda(m)\lambda_m$ 和 $\Psi(b)=\Psi(a)+M_{a,b}$ 代入有限公式，合并质量项即得负号为 $-J_{a,b}$ 的传输式。把 $(a,c]$ 切为 $(a,b]$ 与 $(b,c]$，在第一段每项添加 $\lambda_b-\lambda_c$，即得 cocycle。事件 $m=b$ 的旧零权重也在该修正中被恢复。因此组合必须携带 $J,M$ 及绝对端点位置，不能只携带一个平移无关的标量 $J$。 $\square$

**定理 94.2（非退化区间的统一下界）。** 对实数 $4\le a<b$，置 $C=\Psi(a)>1$，并定义

$$
\Gamma(a,b)=\gamma+\log\log C-P(b^-)
+\sum_{\sqrt b<p\le a-1}\min\{d_1(p),d_2(p,b)\}.
$$

则对每个 $x\in[a,b]$ 有 $\Delta(\lambda_x)\ge\Gamma(a,b)$；对 $a\le a'<b'\le b$ 有 $\Gamma(a',b')\ge\Gamma(a,b)$。

**证明。** 当 $a\le x<b$，$P(x)\le P(b^-)$、$\Psi(x)\ge C$，故

$$
\Phi(x)\ge f_{C,P(b^-)}(x),\qquad
f_{C,P_0}(x)=\gamma+\log\log x-P_0+(C-x)\lambda_x.
$$

其导数为 $(\log x+1)(x-C)/(x^2\log^2x)$，且 $C>1$，所以全域下界为 $\gamma+\log\log C-P_0$。右端点由 $\Phi$ 的事件连续性取极限；等价地，左极限 $\Psi(b^-)\ge\Psi(a)$ 因 $a<b$ 而成立。保留掩码在整个闭区间都是 $B_2(x)$ 掩码的子集，而 $\lambda_x\ge\lambda_b$ 使 $d_2(p,x)\ge d_2(p,b)$，故同一储备和也统一有效。

缩小区间时 $\Psi(a')$ 不减、$P(b'^-)$ 不增、共同素数掩码扩大且各 $d_2$ 不减，新增项非负，给出单调性。非退化条件不可删：若 $a=b$ 为素数幂，$\Psi(a)$ 已含事件而 $P(b^-)$ 尚未含它，前述跨端点不等式的条件失效。单独在 $a=b=x$ 计算储备和则没有这一问题。 $\square$

**命题 94.3（单调细分的松弛量与有效加强）。** 令 $z=\max(a,\min(C,b))$，则

$$
\Gamma_{\mathrm{clip}}(a,b)=
\gamma+\log\log z-P(b^-)+(C-z)\lambda_z
+\sum_{\sqrt b<p\le a-1}\min\{d_1(p),d_2(p,b)\}
$$

也是统一下界，且不小于 $\Gamma$，随子区间细分不减。无论使用哪一式，单调性本身不保证递归最终得到正叶片。

**证明。** $z$ 是冻结函数在真实闭区间上的精确最小点。增加 $C$、减小 $P_0$ 逐点提高该函数，限制最小化定义域也不能降低最小值；储备部分沿用上一证明。在非素数幂且非 $x=p+1$ 掩码边界的普通点，把非退化区间缩至 $x$，原 $\Gamma$ 的极限为 $\gamma+\log\log\Psi(x)-P(x)+B_2(x)$，与真间隙之差为

$$
\left[\log\log x+\frac{\Psi(x)-x}{x\log x}-\log\log\Psi(x)\right]
+[R(x)-B_2(x)]\ge0.
$$

第一项除 $x=\Psi(x)$ 外严格为正，第二项也可为正；边界另有单侧掩码松弛。截断式去掉普通点处的第一种极限松弛，却未去掉储备尾项。因此真间隙为正不自动让这个充分下界变正，有限终止仍须由实际叶片证书或额外统一下界保证。 $\square$

**命题 94.4（实际有限 Fibonacci 覆盖）。** `recursive_reserve.py` 使用定理 94.2 的原 $\Gamma$，在 14 个根区间 $[F_j,F_{j+1}]$、$j=12,\ldots,25$ 上递归，覆盖 $[144,121393]$。长度 $F_m$ 的失败区间在 $a+F_{m-1}$ 分成长度 $F_{m-1},F_{m-2}$ 两段。所有终止叶片都以外向区间的下端点认证 $\Gamma>9/10^8$。

**有限证据。** 整数区间计算共 3,202 次下界求值、1,608 个叶片、最大深度 12（根深度为零），使用 11,425 个素数和 11,539 个素数幂事件。最小叶片为 $[44627,44771]$，其下界端点的十进制显示为 $9.45202409092205664866\times10^{-8}>9\times10^{-8}$。决定性比较使用分母 $2^{128}$ 的整数端点；显示小数不是端点定义。Euler 常数使用 $m=10^6$ 的调和界

$$
H_m-\log m-\frac1{2m}<\gamma<
H_m-\log m-\frac1{2(m+1)}.
$$

程序检查每个分裂的 Fibonacci 长度、邻接与全叶片覆盖；序列化检查入口再次检查可达性、覆盖、停止比较及下表六个区间的十二位小数舍入。完整压缩证书由命令在运行输出目录生成；只保留可重生的小结果。

| $x=100000$ 的储备名称 | 区间端点的十进制显示（近似） |
|---|---:|
| 旧掩码 $B$ | $0.0001563106368398430577032307435$ |
| $B_2$ | $0.0001917077846203446426790616033$ |
| $R_2$ | $0.0001917077846203446426790616033$ |
| $R_3$ | $0.0002136066629966230676164578705$ |
| $R_4$ | $0.0002192525856014055727857889397$ |
| 完整 $R$ | $0.0002294849318088087412288509040$ |

此处 $(99999,100000]$ 无素数，故 $B_2=R_2$ 的数学理由是两掩码相同。程序的区间重叠诊断本身不证明两个实数相等。有效求和使用阈值 $t_p=\log((p^2+p+1)/(p^2+p))/\log p$，因 $d_2-d_1=(\lambda_b-t_p)\log p$，可以将已验证严格有序的阈值分成前缀和后缀；与价格区间重叠的阈值逐项作区间最小值。14 个预定节点与直接逐项和的区间重叠只是转录诊断，数值表达式相等来自上述代数恒等式。截断加强式未用于这些计算，不能把它的性能归给此森林。此有限结果没有认证无限尺度或自动终止定理。

**定理 94.5（最终储备目标与价格间隙仍有 RH 强度）。** 有

$$
\begin{aligned}
\mathrm{RH}
&\Longleftrightarrow
\exists X>1\ \forall x\ge X,
\quad\Phi(x)\ge-\frac{4}{5\sqrt x\log x}\\
&\Longleftrightarrow\Delta(\lambda_x)>0\text{ 最终处处成立}\\
&\Longleftrightarrow\Delta(\lambda_x)\ge0\text{ 最终处处成立}.
\end{aligned}
$$

这里每个“最终”都量化某一阈值之后的所有实数 $x$，且 $\Delta$ 是本节指定的无约束压力间隙。在明确假设 RH 时，还有

$$
c_R-C_\gamma\le\liminf_{x\to\infty}\sqrt x\log x\,\Delta(\lambda_x)
\le\limsup_{x\to\infty}\sqrt x\log x\,\Delta(\lambda_x)
\le c_R+C_\gamma.
$$

**证明。** 常数 $4/5>C_\gamma$，第一条由定理 92.3 的一般形式给出。在 RH 下，$\limsup|\sqrt x\log x\Phi(x)|\le C_\gamma$，而定理 93.2 无条件给 $\sqrt x\log xR(x)\to c_R$，故所示带成立；$c_R-C_\gamma>0$ 推出最终严格正性。严格正性蕴含非负性。反之若最终 $\Delta\ge0$，则 $\Phi\ge-R$；任取固定 $K>c_R$，渐近式给最终 $R\le K/(\sqrt x\log x)$，再由正逆变换和 Landau 论证得到 RH。 $\square$

这些等价关系明确标出尚缺的无限尺度前提；有限森林与局部 $R_p\ge0$ 没有证明此前提，也没有证明 RH。

## 95. 不构造 Fibonacci 大整数的来源指标停止

本节只用标准编号 $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$，对象必须满足数学等式 $n=5040F_j$。

**定理 95.1（五种停止测试的精确失败模数）。** 对每个整数 $j\ge3$，下列五个充分条件在 $n=5040F_j$ 上全部失败，当且仅当 $D\mid j$：

$$
v_2(n)\le20,\quad v_3(n)\le12,\quad v_5(n)\le8,\quad
v_7(n)\le6,\quad v_{11}(n)\le5,
$$

其中

$$
D=2^{15}3^{10}5^87^511^5
=2045861090389670400000000.
$$

因此 $D\nmid j$ 就足以在构造 $F_j$ 之前认证 $\sigma(5040F_j)<e^\gamma(5040F_j)\log\log(5040F_j)$。

**证明。** 使用 T. Lengyel, *The Order of the Fibonacci and Lucas Numbers*, Fibonacci Quarterly 33(3) (1995), 234–239，[原文 Lemmas 1、2（页 235）及 §3 的 rank/lifting 定理](https://www.fq.math.ca/Scanned/33-3/lengyel.pdf)。其标准公式为

$$
v_2(F_j)=\begin{cases}
0&3\nmid j,\\1&j\equiv3\pmod6,\\v_2(j)+2&6\mid j,
\end{cases}\qquad v_5(F_j)=v_5(j).
$$

对 $p\ne2,5$，若 $\alpha(p)$ 是首次正整除指标，则 $\alpha(p)\mid j$ 时 $v_p(F_j)=v_p(j)+v_p(F_{\alpha(p)})$，否则为零。此处 $\alpha(3)=4,\alpha(7)=8,\alpha(11)=10$，且 $F_4=3,F_8=21,F_{10}=55$ 给三个初始指数都为 1；此前较小正指标直接检验无相应整除。只使用这三个具体事实，不假设所有素数初始指数都是 1。公式也见 Medina–Rowland, *p-regularity of the p-adic valuation of the Fibonacci sequence*, FQ 53(3) (2015), 265–271，[Theorem 1.4](https://arxiv.org/pdf/0910.2907)。

由 $5040=2^4\cdot3^2\cdot5\cdot7$，五个失败条件逐一化为：

| 停止方向 | $F_j$ 的失败指数下界 | 等价指标条件 |
|---|---:|---|
| 素数 2 方向 | $v_2(F_j)\ge17$ | $3\cdot2^{15}\mid j$ |
| 素数 3 方向 | $v_3(F_j)\ge11$ | $4\cdot3^{10}\mid j$ |
| 素数 5 方向 | $v_5(F_j)\ge8$ | $5^8\mid j$ |
| 素数 7 方向 | $v_7(F_j)\ge6$ | $8\cdot7^5\mid j$ |
| 素数 11 方向 | $v_{11}(F_j)\ge6$ | $10\cdot11^5\mid j$ |

例如二进下界 17 排除了前两个分支，剩下 $6\mid j$ 且 $v_2(j)\ge15$，恰为首行。其余行由各 rank 条件与指数下界直接得到。五个模数的最小公倍数恰为 $D$，证明双向等价。

因为 $j\ge3$ 保证 $n\ge10080>5040$，可以应用 Christian Axler, *On Robin's inequality*, Ramanujan Journal 61 (2023), 909–919，[Theorem 3](https://link.springer.com/article/10.1007/s11139-022-00683-0) 的 2、5 方向，以及 Alexander Hertlein, *Robin's inequality for new families of integers*, Integers 18 (2018), A71，[原文 Theorem 2、页 2](https://math.colgate.edu/~integers/s71/s71.pdf) 的 3、7、11 方向。这些文献结论不要求 $n$ 极大丰。只要 $D\nmid j$，至少一个条件成功，得到严格 Robin。 $\square$

**命题 95.2（过滤器边界不是 Robin 真值边界）。** 在 $j=D$ 时，$5040F_j$ 的五个指数恰为 $(21,13,9,7,6)$；在 $j=D/p$、$p\in\{2,3,5,7,11\}$ 时，只有对应方向降一并成功。因此该失败模数精确描述这五个测试。但 $j=D$ 本身已由 Axler 的 13 方向 $v_{13}(n)\le4$ 认证。

**证明。** 代入上一公式即可得五个边界值。另有 $\alpha(13)=7,F_7=13$，而 $7\mid D,13\nmid D$，所以 $v_{13}(5040F_D)=v_{13}(D)+1=1$。故五过滤器的幸存者不能被统称为尚未解决的 Robin 实例。 $\square$

该捷径应用既有 valuation 定理，没有原创性或内核验证声明。来源必须由标准递推的符号定义或独立算术证书给出；任意 `source_index` 元数据并不证明 $n=5040F_j$。编号从 $1,2,3,5,\ldots$ 开始的语言也须先证明指标平移。`index_stopping.py` 的保留默认回归直接构造至指标 10,000 并作 50,000 个五素数 valuation 比较；208 个选定大指标由矩阵幂和 fast doubling 两路计算模 $p^{e+1}$，作 1,040 个比较，同时检验残数非零且指数恰为 $e$。它还检验 $F_D$ 被 $2^{17}$ 整除而 $F_{D+1}$ 为奇数的移位负控制。有限实验不替代无限指标定理，额外输入指标可由命令行指定。

## 96. 非互素约数的规范接缝与条件化代价

**定理 96.1（任意两块的规范接缝）。** 对正整数 $A,B$，定义

$$
\Gamma_{A,B}=\{(u,v):u\mid A,\ v\mid B,\ \gcd(v,A/u)=1\}.
$$

乘法映射 $(u,v)\mapsto uv$ 给出 $\Gamma_{A,B}$ 与 $AB$ 的全部正约数之间的双射，其逆为

$$
d\longmapsto\bigl(\gcd(d,A),\ d/\gcd(d,A)\bigr).
$$

特别地，$Z(AB)=\sum_{(u,v)\in\Gamma_{A,B}}1/(uv)$。

**证明。** 对任意素数 $p$，令 $a=v_p(A),b=v_p(B),k=v_p(d)\le a+b$。逆映射的两个指数分别为 $\min(k,a)$ 和 $\max(k-a,0)$，都在各自上限内，并满足接缝条件。反向若 $s=v_p(u),t=v_p(v)$，则 $\min(t,a-s)=0$：或 $t=0$，或 $s=a$。给定和 $k=s+t$，这恰迫使 $s=\min(k,a),t=\max(k-a,0)$，所以逐素数唯一。乘法双射使加权和每个算术约数恰计一次。 $\square$

**定理 96.2（条件 Gibbs 律、KL 与结合 cocycle）。** 在 $A$ 的约数上取 $\mu_A(u)=1/(uZ(A))$，类似定义 $\mu_B$，并令 $P=\mu_A\otimes\mu_B$。则

$$
P(\Gamma_{A,B})=\frac{Z(AB)}{Z(A)Z(B)},\qquad
I(A,B)=\log\frac{Z(A)Z(B)}{Z(AB)}\ge0.
$$

条件律 $\nu=P(\cdot\mid\Gamma_{A,B})$ 经乘法推前恰为 $\mu_{AB}$，并且

$$
D_{\mathrm{KL}}(\nu\Vert P)=I(A,B),\qquad
I(A,B)=0\Longleftrightarrow\gcd(A,B)=1.
$$

写 $W=\log Z$，则对第三个正整数 $C$，

$$
I(A,B)+I(AB,C)=I(B,C)+I(A,BC)
=W(A)+W(B)+W(C)-W(ABC).
$$

**证明。** 双射加权和除以 $Z(A)Z(B)$ 给接缝概率；每个 $d$ 的唯一合法对在条件化后的概率为 $1/(dZ(AB))$。接缝上似然比 $\nu/P$ 恒为 $1/P(\Gamma)$，故 KL 等于负对数概率。互素时整个直积都合法；若有共同素数 $p$，正质量对 $(1,p)$ 不合法，故接缝概率严格小于 1。最后展开 $I=W(A)+W(B)-W(AB)$，两种括号排列都望远镜消去中间项。 $\square$

这个 KL 是对原始乘积律的条件化代价，一般不是条件律的互信息。确切的有限分布恒等式为

$$
I(A,B)=\operatorname{MI}_\nu(U;V)
+D_{\mathrm{KL}}(\nu_U\Vert\mu_A)
+D_{\mathrm{KL}}(\nu_V\Vert\mu_B).
$$

它由把对数似然比分解为相对条件边缘乘积、再相对原始边缘两项后求期望得到。例 $A=B=2$ 时原边缘均为 $(2/3,1/3)$，条件边缘却为 $(4/7,3/7)$ 和 $(6/7,1/7)$，所以不能删掉后两项。一般条件化 KL 公式也已见 [ZECKENDORF_EULER_5040.md](ZECKENDORF_EULER_5040.md) 的条件化熵讨论；这里的新增推导是任意重叠约数接缝的明确双射和组合。

**命题 96.3（5040 的带标签历史与算术约数）。** 把 $5040$ 看成八个带标签素数出现 $(2,2,2,2,3,3,5,7)$。独立选或不选的历史有 $2^8=256$ 个，按每个素数组“先填前缀”的规范接缝只留 $5\cdot3\cdot2\cdot2=60$ 个，恰为全部算术约数。独立历史权重与规范权重之比为 $1296/403$。

**证明。** 每个素数 $p$ 出现 $a$ 次，独立子集对同一指数会有二项式重数，规范前缀却对指数 $0,\ldots,a$ 各留一次。故独立倒数权重与规范权重分别为

$$
(1+1/2)^4(1+1/3)^2(1+1/5)(1+1/7)=\frac{432}{35},
\qquad Z(5040)=\frac{403}{105},
$$

比值即为 $1296/403$。第 89 节的合数块缺约数问题仍须另证完整性；此处八个块本身是素数，故前缀确实覆盖全部指数。 $\square$

**定理 96.4（不完整 valuation 给出安全接缝下界）。** 对 $k$ 个正整数块 $A_i$，在任一有限集 $\mathcal P$ 的互异、已认证素数上，若已知 $0\le\ell_{p,i}\le v_p(A_i)$，则

$$
L_{\mathrm{join}}=
\sum_{p\in\mathcal P}\left[\sum_i\log G_p(\ell_{p,i})-
\log G_p\left(\sum_i\ell_{p,i}\right)\right]
\le\sum_iW(A_i)-W\left(\prod_iA_i\right).
$$

若另有 $W(A_i)\le U_i$，就有 $W(\prod_iA_i)\le\sum_iU_i-L_{\mathrm{join}}$。增加已知素数或提高已认证指数下界只能加强这个保证。

**证明。** 单素数修正 $I_p(a_1,\ldots,a_k)=\sum_i\log G_p(a_i)-\log G_p(\sum_i a_i)$ 非负，因为几何和的乘积对每个总指数至少包含一项。令 $g_p(j)=\log(G_p(j)/G_p(j-1))$，它严格递减。把 $a_i$ 增加一时，修正增量为 $g_p(a_i+1)-g_p(\sum_j a_j+1)\ge0$，故逐坐标单调。真实总修正逐素数相加；遗漏通道非负，保留通道可用下界代替，证明所示不等式。合成上界按方向相减即可。 $\square$

这里可省略的是非负接缝成本。二叉接缝树按 cocycle 望远镜相加，却不能把所有两两修正都相加：$A=B=C=2$ 时，两两乘性修正为 $(9/7)^3=729/343$，真实三块修正仅为 $9/5$。错误地减去前者会过减。素数标记也不能换成相互重叠的任意合数轴。具体有 $\exp I(5040,2)=31/21$、$\exp I(5040,3)=13/10$；三块 $(5040,6,8)$ 在 2、3 方向的下界指数 $(1,1,1)$、$(1,1,0)$ 给 $\exp L_{\mathrm{join}}=144/65$，提高到 $(4,1,3)$、$(2,1,0)$ 给真实修正 $3627/1022$。这些数由上述几何和公式作精确有理运算得到。

## 97. 未来响应等价、精确下确界与安全剪枝

固定允许素数集 $S$，令 $\mathcal M(S)$ 为所有素因子在 $S$ 中的正整数乘法幺半群，含 1；每个乘数只有有限支撑，但各指数没有预定上限。本节所有比较使用同一个实际有限乘数 $c$。

**定理 97.1（未来相对响应恰识别允许 valuation）。** 两个正整数 $n,m$ 满足

$$
\frac{Z(nc)}{Z(n)}=\frac{Z(mc)}{Z(m)}
\quad\text{对所有 }c\in\mathcal M(S)
$$

当且仅当 $v_p(n)=v_p(m)$ 对所有 $p\in S$ 成立。

**证明。** 写 $a_p=v_p(n),t_p=v_p(c)$，则相对响应为 $\prod_{p\in S}G_p(a_p+t_p)/G_p(a_p)$，只依赖所列 valuation。反向取可用的单素数继续量 $c=p$，响应是 $1+1/(p+\cdots+p^{a_p+1})$，关于 $a_p$ 严格递减，故逐素数相等。如果允许未来是更小的受限家族、缺少这些单素数探针，完整 valuation 向量的必要性就不能自动沿用。绝对比较还需要起始比值 $Z(n)/Z(m)$；价格增量也只多出同一 $-\lambda\log c$。 $\square$

**定理 97.2（共同未来权重比的精确下确界）。** 令 $a_p=v_p(n),b_p=v_p(m)$，$T=\{p\in S:a_p>b_p\}$，则 $T$ 有限，且

$$
\inf_{c\in\mathcal M(S)}\frac{Z(nc)}{Z(mc)}
=L_S(n,m):=\frac{Z(n)}{Z(m)}
\prod_{p\in T}\frac{G_p(b_p)}{G_p(a_p)}.
$$

所以全部共同未来满足 $Z(nc)\ge Z(mc)$ 当且仅当 $L_S(n,m)\ge1$。$T\ne\varnothing$ 时下确界不被任何有限 $c$ 取到。

**证明。** 固定素数、置 $z=1/p$，变化因子为

$$
f_p(t)=\frac{G_p(a+t)}{G_p(b+t)}
=\frac{1-z^{a+t+1}}{1-z^{b+t+1}}.
$$

若 $a>b$，它严格下降趋于 1；若 $a<b$，它严格上升，最小值在 $t=0$；若相等则恒为 1。这些方向也可由相邻比的边际递减直接验证。各因子的下界除以初值 $f_p(0)$ 后相乘，正好得到 $L_S$，所以每个实际共同乘数都满足此下界。

为证明确切性，使用真实有限乘数 $c_N=\prod_{p\in T}p^N$。所有非优势方向保持零指数，故 $Z(nc_N)/Z(mc_N)\downarrow L_S$。若 $L_S<1$，某个有限 $N$ 就给出反例，建立必要性，而非把分属不同对象的最优值拼在一起。若 $T$ 非空，有限指数在至少一个优势方向仍严格大于其极限，其余方向不低于各自下界，所以不取到；若 $T$ 为空则 $c=1$ 取到。比如 $n=2,m=1,S=\{2\}$ 时下确界为 1，而每个有限比值都严格大于 1。等号 $L_S=1$ 仍足以保证非严格支配。 $\square$

**推论 97.3（价格、预算与所有素数未来）。** 对任意固定实数 $\lambda$，定义 $J_\lambda(n)=W(n)-\lambda\log n$，则

$$
\left[\forall c\in\mathcal M(S),\ J_\lambda(nc)\ge J_\lambda(mc)\right]
\Longleftrightarrow
J_\lambda(n)-J_\lambda(m)\ge
\sum_{p\in T}\log\frac{G_p(a_p)}{G_p(b_p)}.
$$

若 $S$ 是所有素数，则全部未来的 $Z$ 支配当且仅当 $m\mid n$；再附加预算方向 $n\le m$，只剩 $n=m$。

**证明。** 共同乘数使价格惩罚之差恒为 $-\lambda\log(n/m)$；对比值取下确界得 $\log L_S\ge\lambda\log(n/m)$，即所示式。所有素数都允许时，起始比值的所有优势因子在下确界被抵消，剩下

$$
L_{\mathrm{all}}(n,m)=\prod_{p:a_p<b_p}\frac{G_p(a_p)}{G_p(b_p)}\le1.
$$

它达到 1 恰当没有亏损素数，即 $m\mid n$。结合 $n\le m$ 给相等。此结论不使价格比较平凡化，例如 $n=1,m=2,\lambda=1$ 时全部未来权重比至少 $2/3>1/2$，故价格比较仍有严格余量。 $\square$

要用 $n$ 剪掉预算状态 $m$，还须证明 $n\le m$ 并允许传输每个相关继续量：两状态有共同的可行继续域，或给出从 $m$ 到 $n$ 的可行性映射。预算大小只保证 $nc\le mc$，不能保证同余、指数帽、支撑或历史约束也被保留。共享有限预算或联合限制下，无约束幺半群下确界仍给充分下界，但不一定是受限族的精确最小值。只有独立矩形帽 $0\le t_p\le h_p$ 才能把每个优势方向的无穷极限直接替换成 $t_p=h_p$ 得精确有限版本；共同乘积预算不是矩形。

**命题 97.4（当前支配可以在乘法后逆转）。** 仅有 $n\le m$ 和 $Z(n)\ge Z(m)$ 不足以剪枝。精确反例如下：

| 继续比较对象 $(n,m;c)$ | 继续前 $Z(n)/Z(m)$ | 继续后 $Z(nc)/Z(mc)$ | $S=\{3\}$ 的未来下确界 |
|---|---:|---:|---:|
| $(6,8;3)$ | $16/15$ | $13/15$ | $4/5$ |
| $(30240,40320;3)$ | $224/221$ | $847/850$ | $84/85$ |

**证明。** 分别按总素数指数代入 $G_p$ 的有限几何和公式即可。第二行是 $5040\cdot6$ 与 $5040\cdot8$，前后都处在大于 5040 的正倍数族内，故不是脱离目标族的反例。 $\square$

**定理 97.5（未知损失不能省略，粗糙极值可给保守替代）。** 精确未来下界也可写作

$$
L_S(n,m)=\frac{Z(n)}{Z(m)}
\prod_{p\in S}\min\left(1,\frac{G_p(b_p)}{G_p(a_p)}\right).
$$

每项至多为 1，遗漏未知允许方向会把下界错误提高。若已认证 $n=Ar$、$\gcd(A,r)=1$，完整知道 $A$ 的素因子及指数，并有 $Z(r)\le U$，令 $K_{\mathrm{known}}$ 含尽 $A$ 上所有允许方向的损失因子，则

$$
L_S(n,m)\ge\frac{Z(n)}{Z(m)}\frac{K_{\mathrm{known}}}{U}.
$$

起始比值可以换成已认证下界；已知方向中的 $b_p$ 也可换成已认证下界，而 $a_p$ 在此为准确指数。

**证明。** 未知通道全部来自与 $A$ 互素的 $r$。因为 $G_p(b_p)\ge1$，

$$
\prod_{p\mid r,\ p\in S}\min\left(1,\frac{G_p(b_p)}{G_p(a_p)}\right)
\ge\prod_{p\mid r}\frac1{G_p(a_p)}=\frac1{Z(r)}\ge\frac1U.
$$

不属于 $n$ 支撑的通道因子为 1，故没有漏项；已知与未知支撑不重叠，所以可乘合。$G_p(b)$ 递增，使用 $b$ 下界只会降低保证。若 $r$ 已知 $y$-rough 且 $r\le B$，定理 90.2 的携证 $U_y(B)$ 就能充当 $U$。另对完整有限 $S$，准确掌握上界 $a_p\le u_p$ 与下界 $b_p\ge\ell_p$ 时，可逐方向用 $\min(1,G_p(\ell_p)/G_p(u_p))$；两种方法都不允许静默丢掉潜在损失方向。 $\square$

这与第 96 节遗漏非负接缝成本的方向不同。例如 $n=6,m=8,A=2,r=3,S=\{3\}$，若省略未知 3 方向，会错误保留当前比值 $16/15>1$；取 $U=Z(3)=4/3$ 后给出安全下界 $4/5$，正好揭示不能剪枝。

保留的 `relational_gluing.py` 用整数和 `Fraction` 检查 4,096 个 $A,B\le64$ 接缝对、4,096 个 $A,B,C\le16$ cocycle 三元组、2,720 个局部单调性实例、24,768 个实际共同乘数比较、4,096 个全素数支配对和 8,192 个部分分解下界；还逐历史检查第 96 节的 256/60 计数及权重比。无限支撑、下确界必要性和所有未来的结论由上述证明承担，有限计数不代替它们。

本批程序与结果入口集中于 [fib-robin-boundary/README.md](../../reports/fib-robin-boundary/README.md)。rough 和强制核的规范化是 Python 检查器外的证明前提；解析经典输入、无限尺度界、未来可行性传输及来源语义也各自保留上述条件。本批没有新增 Lean、冻结或消化状态；既有模块的局部构建证据不延伸到这些纸面推导或 Python 证书。最终 RH 等价条件仍未被证明成立，后续研究目标保持开放。

## 追加锚（递归块 Robin 主编码批次后）

## 98. 完整价格裕度的临界切片与严格自匹配归约

**定义 98.1（同一无约束价格目标）。** 沿用第 85、87、93 节，令 $Z(n)=\sigma(n)/n$、$W(n)=\log Z(n)$，对正价格 $\lambda>0$ 在全部正整数上取

$$
S(\lambda)=\max_{n\ge1}\{W(n)-\lambda\log n\},\qquad
\lambda(x)=\frac1{x\log x},\quad x>1.
$$

这里 $S$ 就是前文的无约束压力 $M$。认证素数块保持来源，数值域仍含全部正整数，并非只含本身为 Fibonacci 数的素数。置

$$
G_p(a)=\sum_{j=0}^ap^{-j},\qquad
r_{p,k}=\frac{\log(G_p(k)/G_p(k-1))}{\log p}\quad(k\ge1).
$$

配置 $T_x$ 取全部 $r_{p,k}>\lambda(x)$ 的层，零收益层一律不取。设

$$
\mathcal A(x)=\log N(T_x),\qquad \mathcal F(x)=W(N(T_x)),
$$

$$
\mathfrak D(x)=\gamma+\log\log x-\lambda(x)x-S(\lambda(x))
=\Phi(x)+R(x).
$$

最后一个恒等式正是定理 87.3，要求两项使用同一压力和同一实际最优配置。正价格最大值与有限正部公式来自既有全局价格目标；本节接续其临界点结构。自身规模处的匹配切线价格也已见 [ZECKENDORF_EULER_5040.md](ZECKENDORF_EULER_5040.md) 的“Robin 余量的精确三项修正”及式（19）。

**命题 98.2（紧区间局部有限与精确导数）。** 每个 $[a,b]\subset(1,\infty)$ 上仅有有限个可能活跃的层及激活事件。$\mathfrak D$ 连续，稳定胞腔内光滑；令

$$
w(x)=-\lambda'(x)=\frac{\log x+1}{x^2(\log x)^2}>0,
$$

则稳定胞腔内有

$$
\mathfrak D(x)=\gamma+\log\log x-\mathcal F+
\frac{\mathcal A-x}{x\log x},\qquad
\mathfrak D'(x)=(x-\mathcal A)w(x).
$$

**证明。** 因为 $G_p(k)/G_p(k-1)=1+1/(p+\cdots+p^k)$，有

$$
0<r_{p,k}<\frac1{p^k\log p}.
$$

在紧区间内 $\lambda(x)\ge\lambda(b)>0$。当 $p\ge b$ 时没有活跃层或事件；其余有限个素数各只有有限个 $k$ 能满足 $p^k\log p<1/\lambda(b)$。不同素数可以同时激活，同一素数的阈值严格递减，不能同时激活两层。由有限正部公式

$$
S(\lambda(x))=\sum_{p,k}\log p\,(r_{p,k}-\lambda(x))_+
$$

及局部有限性，得到连续性及稳定区间表达。微分时 $d(\log\log x)/dx=\lambda(x)$，它与 $-\lambda(x)x$ 的一项恰好相消，余下为 $(x-\mathcal A)w$。同样，在参考素数幂与实际激活事件均未发生处，

$$
\Phi'(x)=(x-\Psi(x))w(x),\qquad
R'(x)=(\Psi(x)-\mathcal A(x))w(x).
$$

所以 $\Psi$ 精确消去。仅有参考素数幂事件而没有实际激活时，完整裕度的导数不跳跃；不能把两个分量的事件效应再次当作独立负载相加。 $\square$

**定理 98.3（同时激活与严格自匹配谷底）。** 实际激活点不能是 $\mathfrak D$ 的局部极小点。其余内部局部极小点恰与以下严格自匹配配置一一对应：有限 $T=\prod_pP_p^{a_p}$，$A=\log N(T)>1$，在价格 $\lambda_T=1/(A\log A)$ 下满足

$$
r_{p,a_p+1}<\lambda_T\quad(\text{全部素数 }p),\qquad
\lambda_T<r_{p,a_p}\quad(a_p>0).
$$

对应的极小点是 $x=A$，且

$$
\mathfrak D''(A)=w(A)>0,\qquad
\mathfrak D(A)=\gamma+\log\log A-W(N(T)).
$$

这是 $N(T)$ 的 Robin 对数裕度。

**证明。** 在激活点 $\tau$，设有限非空同时激活层集为 $E_\tau$，$H_\tau=\sum_{(p,k)\in E_\tau}\log p>0$。净收益在阈值处为零，故函数连续；规模从 $\mathcal A_-$ 增到 $\mathcal A_-+H_\tau$，因此

$$
\mathfrak D'_+(\tau)-\mathfrak D'_-(\tau)=-H_\tau w(\tau)<0.
$$

局部极小所需的 $\mathfrak D'_-(\tau)\le0\le\mathfrak D'_+(\tau)$ 不可能成立。稳定胞腔中导数符号恰是 $x-A$，所以只有 $x=A$ 在胞腔内部时才能取得内部极小，并给出上述二阶导数与值。

逐轴严格递减使所列阈值条件等价于：每个已取层严格有益、每个未取层严格无益。这给出价格下唯一的数值最优者。严格性还给出共同开放邻域：阈值至少 $\lambda_T/2$ 的层只有有限个，其他层已有固定正距离，故不可能有未控制的无限阈值逼近 $\lambda_T$。所以配置在 $A$ 附近固定，得到反向对应。数值唯一不要求来源语法树唯一。闭区间端点不在内部极小结论内，必须另查。此对应没有给出“按自身规模反复更新最优者”的迭代收敛定理。 $\square$

**定理 98.4（无条件无穷远极限）。** 不假设 RH，有

$$
\lim_{x\to\infty}\mathfrak D(x)=0.
$$

**证明。** 令 $v_p=v_p(x)$ 为定义 87.1 的参考层数，并令

$$
M_{\mathrm{prod}}(x)=\sum_{p\le x}-\log(1-p^{-1}).
$$

将它与 $P(x)=\sum_{p^k\le x}1/(kp^k)$ 比较。对 $p\le\sqrt x$，遗漏的几何尾给

$$
\sum_{k>v_p}\frac1{kp^k}\le\sum_{k>v_p}p^{-k}
\le2p^{-v_p-1}<\frac2x.
$$

对 $\sqrt x<p\le x$，$v_p=1$，遗漏尾至多 $2/p^2$。于是

$$
0\le M_{\mathrm{prod}}(x)-P(x)
\le\frac{2\pi(\sqrt x)}x+2\sum_{\sqrt x<p\le x}p^{-2}
=O(x^{-1/2}).
$$

最后一步只需 $\pi(t)\le t$ 和整数尾和 $\sum_{n>t}n^{-2}=O(1/t)$。经典 Mertens 乘积渐近给
$M_{\mathrm{prod}}(x)=\gamma+\log\log x+o(1)$，普通素数定理给 $\Psi(x)=x+o(x)$，故

$$
\Phi(x)=\gamma+\log\log x-P(x)+\frac{\Psi(x)-x}{x\log x}\longrightarrow0.
$$

这两项经典输入沿用第 87、92 节的文献范围；Mertens 乘积公式可见 [Lichtman, Theorem 1.1](https://arxiv.org/html/2002.03361v3)。储备则由定理 93.1 的 $0\le R_p\le D_p(v_p)<2p^{-v_p-1}$ 及 $p\ge x$ 时 $R_p=0$，以同一分组得到

$$
0\le R(x)\le\frac{2\pi(\sqrt x)}x+
2\sum_{\sqrt x<p\le x}p^{-2}=O(x^{-1/2}).
$$

因此 $\mathfrak D=\Phi+R\to0$。这里没有使用平方根级的素数定理误差，更没有确定趋近零的方向。 $\square$

**命题 98.5（有限临界切片及起始整数补丁）。** 有限有理区间证书给出

$$
\forall x\in[\log40000,121393],\qquad
\mathfrak D(x)>\frac{51}{250000},
$$

并给出 $5041\le n\le40000$ 上的严格 Robin 不等式。此外 $x_0=\log40000$ 满足 $x_0\log x_0>25$。

**证明。** 紧区间连续函数达到最小值；若不在端点，则定理 98.3 使它位于稳定胞腔的严格自匹配点。因此须覆盖全部事件及胞腔，检查两端和每个内部谷底，而非只列举部分候选。若胞腔的价格区间是 $(\lambda_{\mathrm{low}},\lambda_{\mathrm{high}})$，固定规模为 $A$，则其内部含谷底恰当

$$
\lambda_{\mathrm{low}}<\frac1{A\log A}<\lambda_{\mathrm{high}}.
$$

两个截断胞腔用所给区间端点的价格代替相应界。分母 $2^{128}$ 的向外整数区间及第 85 节的 $100$ 项对数级数余项给出精确比较；Euler 常数使用更窄的包络

$$
H_m-\log m-\frac1{2m}<\gamma<
H_m-\log m-\frac1{2(m+1)},\qquad m=10^6.
$$

此包络可直接证明：$H_m-\log m-\gamma=\sum_{k=m}^\infty[\log(1+1/k)-1/(k+1)]$。对 $1/t$ 的严格梯形上界使每项小于 $1/(2k(k+1))$，总和小于 $1/(2m)$；积分表示 $\int_k^{k+1}(u-k)u^{-2}\,du$ 使每项大于 $1/(2(k+1)^2)$，总和大于 $\frac12\int_{m+1}^\infty t^{-2}\,dt$。

素数范围完整取至 $121393$；更大素数满足 $r_{p,1}<1/(p\log p)<\lambda(121393)$。每根轴生成到第一个严格低于终点价格的层，再以严格递减排除其余层。全部相邻阈值区间在此有限范围严格分离，全部胞腔分类均被确定，得到以下读数。显示小数仅为近似读数，严格比较使用有理端点。

| 临界切片量 | 实际值 |
|---|---:|
| 完整素数数目 | 11425 |
| 起始 5040 配置层数 | 8 |
| 内部激活事件数 | 11568 |
| 稳定胞腔数 | 11569 |
| 内部严格自匹配点数 | 133 |
| 其中 $x\ge144$ 的点数 | 117 |
| 首个自匹配整数 | 720720 |
| 最小内部谷底下界所在尺度 | $119544.1883346433876462307764\ldots$ |
| 内部谷底最小下界 | $0.0002052870022118778275605233327\ldots$ |
| 左端下界 | $0.008314953821252398723132344539\ldots$ |
| 右端下界 | $0.0002044061996600856183985968307\ldots$ |

起始补丁在每块 $[a,b]$ 取完整整数域上的精确最大值 $Z_{\max}$，再以单调预算检查
$\gamma+\log\log\log a-\log Z_{\max}>0$。四块覆盖全部 $34960$ 个整数：

| 起始补丁区间 | 最大值达到处 | 未约分 $Z_{\max}$ |
|---|---:|---:|
| $5041\le n\le9410$ | 7560 | $28800/7560$ |
| $9411\le n\le13780$ | 10080 | $39312/10080$ |
| $13781\le n\le22520$ | 15120 | $59520/15120$ |
| $22521\le n\le40000$ | 27720 | $112320/27720$ |

[临界切片结果](../../reports/fib-robin-boundary/critical_slice.json) 与[独立重放结果](../../reports/fib-robin-boundary/critical_slice_check.json)给出对应有限证据；证据的精确区间和覆盖范围由其可重建证书承担。此处的四块与窄 $\gamma$ 包络只说明本证书的数值，不替换旧证书的读数。 $\square$

**定理 98.6（非正失败归约与完整 RH 等价式）。** 以下三个断言等价：RH；每个 $N>40000$ 的严格自匹配配置满足严格 Robin 不等式；每个 $N>40000$ 且 $5040\mid N$ 的严格自匹配配置满足严格 Robin 不等式。这里必须合用命题 98.5 的 $5041\le n\le40000$ 补丁与经典 Robin 等价定理。

**证明。** 先证任意 $x>x_0=\log40000$ 上的非正完整裕度都产生一个失败的严格自匹配 5040 扩展。若 $[x_0,\infty)$ 上无负值，已有的零点本身就是内部局部极小。若存在 $\mathfrak D(y)=-\eta<0$，由定理 98.4 选 $M>y$，使所有 $t\ge M$ 都有 $\mathfrak D(t)>-\eta/2$。连续性给 $[x_0,M]$ 上的最小值；$\mathfrak D(x_0)>0$ 且右端大于 $-\eta/2$，所以负最小值位于内部。两种情形都由定理 98.3 得到严格自匹配点 $t=\log N(T_t)>x_0$，并有

$$
\gamma+\log\log\log N(T_t)-W(N(T_t))\le0.
$$

这包括恰为零的严格 Robin 失败。又 $x_0\log x_0>25$，故 $\lambda(t)<1/25$；5040 在 $1/25$ 的八个严格有益层仍全部保留，从而 $N(T_t)>40000$ 且 $5040\mid N(T_t)$。

对于任意 Robin 失败整数 $n>40000$，在 $x=\log n$ 处，由全局最优性

$$
S(\lambda(x))\ge W(n)-\lambda(x)x,\qquad
\mathfrak D(x)\le\gamma+\log\log\log n-W(n)\le0.
$$

故上述归约必可启动。结论是存在另一个失败的严格自匹配 5040 倍数，不是原失败整数一定属于该类。反向，失败的严格自匹配整数自身就是 Robin 反例。补丁排除剩余有限区间，再用 Robin 的 $n>5040$ 等价判据，得到三个断言等价。 $\square$

同一运输还把命题 98.5 扩展为所有整数 $5041\le n\le e^{121393}$ 的 Robin 不等式。无限任务仍是由严格阈值条件统一推出

$$
\sum_p\log G_p(a_p)<\gamma+\log\log A,
\qquad A=\log N(T)>\log40000.
$$

此前标量障碍 $\Phi\ge-4/(5\sqrt x\log x)$ 配合储备渐近给出较强的充分路线；逐点所需的联合目标仅为同一对象上的 $\Phi+R>0$，允许实际储备补偿更深的 $\Phi$ 负值。这个逐点条件较弱不削弱第 94 节最终全称条件的 RH 等价强度。无条件极限、有限正区间和逐个可生成的未来事件，都没有证明余下无限族的正性。

## 99. 上下文最优补全、最小动作状态与全部乘法未来

**定理 99.1（逐轴严格单峰下的唯一数值补全）。** 设有限支撑非负整数向量 $(h_p)_p$ 给出 $H=\prod_pp^{h_p}$。目标可分解为

$$
J(n)=\sum_pf_p(v_p(n)),\qquad f_p(0)=0,
$$

且每个 $f_p$ 在 $0\le a\le h_p$ 上严格增加、在 $a\ge h_p$ 上严格下降。对给定正整数 $C$，允许任意正整数新增乘数 $A$，则唯一数值最优动作为

$$
A_*(C)=\frac{H}{\gcd(C,H)},\qquad
CA_*(C)=\operatorname{lcm}(C,H).
$$

**证明。** 写 $c_p=v_p(C)$。只许乘法新增意味着总指数被限制在 $a\ge c_p$；逐轴严格单峰给该半直线的唯一最大点 $\max(c_p,h_p)$，新增指数为 $\max(h_p-c_p,0)$。在 $C,H$ 支撑之外任意正指数均严格降值。对任意竞争 $A$，三者支撑并仍有限，逐项比较并求和即可；等号迫使所有指数准确取到各自最大点。gcd 与 lcm 的指数分别是最小值与最大值，给出所示式。 $\square$

仅有无约束的唯一全局最优不足以推出本结论。例如 $f(0)=0,f(1)=3,f(2)=0$，而对 $k\ge3$ 令 $f(k)=5-k$。唯一全局最大在 1，但限制 $k\ge2$ 后最大在 3，不在 2。该反例说明不能省略本定理的单峰前提。

取 $J=J_{1/25}=\log Z(n)-\frac1{25}\log n$、$H=5040=2^4 3^2 5\cdot7$ 时，所需前提来自既有每根素数轴的严格边际递减和严格相邻阈值：$h_2=4,h_3=2,h_5=h_7=1$，其余 $h_p=0$。因而

$$
\operatorname*{argmax}_{A\ge1}J_{1/25}(CA)
=\left\{\frac{5040}{\gcd(C,5040)}\right\}.
$$

这是保持已有 $C$ 的任务。比如 $C=65520=5040\cdot13$ 时最优新增块为 1，最终仍为 65520，不能删除已有 13 因子返回 5040。来源语法可以有多个表示，唯一性只在整数值上。其他价格需另给有限严格最优模板；阈值平局时须改成集合值动作。一般 $H$ 的下述状态定理针对指定函数，不断言每个 $H$ 都是某价格的最优模板。

**定理 99.2（一般模板的最小乘法动作状态）。** 固定正整数 $H$，任务输出准确整数

$$
F_H(C)=\frac{H}{\gcd(C,H)},\qquad C\ge1.
$$

在状态独自承担输出与更新、不重开已删来源、全部正整数初态和任意共同乘法续接均允许的合同下，最小确定性状态数为 $\tau(H)$。充分且必要的行为商为 $q_H(C)=\gcd(C,H)$。

**证明。** 在正约数集 $\operatorname{Div}(H)$ 上定义 $d\odot e=\gcd(de,H)$。逐素数有

$$
\min(v_p(C)+v_p(D),h_p)
=\min(\min(v_p(C),h_p)+\min(v_p(D),h_p),h_p),
$$

所以 $q_H(CD)=q_H(C)\odot q_H(D)$。这是有限交换幺半群，单位为 1，$H$ 是吸收态；结合律也可由上述同态及每个约数均可实现推出。同一 $q_H$ 在每条共同乘法输入词后都有同一状态与输出，故充分。反之，不同约数 $d$ 对应的当前输出 $H/d$ 已不同，任何准确输出系统至少区分所有 $\tau(H)$ 个代表初态；当前输出即允许空续接。$q_H$ 达到下界。$H=1$ 是单态特例。 $\square$

对 5040，该状态可写成

$$
\bigl(\min(v_2(C),4),\min(v_3(C),2),\min(v_5(C),1),\min(v_7(C),1)\bigr),
$$

共有 $5\cdot3\cdot2\cdot2=60$ 态。允许来源重读、额外免费 oracle、近似动作、部分初态或受限后续输入时，合同已变，不能照搬下界。约数集合可以通过既有黄金窗口双射命名，但固定容量截断不等于把任意指数投影到 Fibonacci 窗口端点。

**命题 99.3（规范关系位与加法反例）。** 先取 $d=q_{5040}(C)=2^i3^j5^k7^\ell$，再采用指定素块 $[2],[3],[5],[2+5]$，定义

$$
(u,v,w;\kappa)=(i+\ell,j,k+\ell;\ell).
$$

最优补块的规范表达与关系坐标分别为

$$
[2]^{4-i}[3]^{2-j}[5]^{1-k}[2+5]^{1-\ell},\qquad
(5-u,2-v,2-w;1-\kappa).
$$

省略关系位 $\kappa$ 不足以决定动作；同一粗乘法态也不足以更新加法。

**证明。** 补块公式直接代入定理 99.1 的互补指数；关系式按叶子计数相加。$7=[2+5]$ 与 $10=[2][5]$ 都给 $(u,v,w)=(1,0,1)$，但动作分别为 720 和 504，所以须保留区别两者的关系位。这里的坐标属于规范 $q(C)$，不能把任意原始来源树的叶子数作同样减法，也不恢复原始全部语法。另有 $q(11)=q(13)=1$，同加 2 后得到 13 与 15，动作分别为 5040 与 336，故 $q$ 不支持一般加法更新。 $\square$

**定理 99.4（任意加法续接需要恰好 $H$ 态）。** 对同一准确输出任务 $F_H$，若允许任意正整数加法续接且不重读来源，完整行为等价恰为模 $H$ 同余，最小确定性状态数为 $H$。再允许乘法仍恰为 $H$ 态。

**证明。** 余数 $r_H(C)=C\bmod H$ 支持

$$
r_H(C+D)=(r_H(C)+r_H(D))\bmod H,\qquad
r_H(CD)=r_H(C)r_H(D)\bmod H,
$$

并由 $F_H(C)=H/\gcd(r_H(C),H)$ 给出输出，故 $H$ 态充分，二元加乘 DAG 也可逐节点求值，但必须保留实际逻辑引用。若 $H\ge2$ 且 $r\ne s$，取同一正续接

$$
t=2H+((-r)\bmod H)\ge2.
$$

则 $F_H(r+t)=1$ 而 $F_H(s+t)>1$。所有余数都有正整数代表，故至少 $H$ 态。所用 $t$ 不要求零或负数，也不要求原子 1：每个 $t\ge2$ 都能用 2、3 相加表示，偶数用若干个 2，奇数用一个 3 加若干个 2；若只逐次允许加 2 或 3，该后缀词同样区分两态。$H=1$ 单态结论立即成立。加入乘法既不破坏充分模型，也不削弱纯加法给出的下界。 $\square$

因此 5040 的乘法动作合同需要 60 态，允许任意加法后需要 5040 态。这些是状态基数，不是物理空间维度。上述证明直接在无限正整数域建立行为商，再给出有限实现；不能把只针对有限初态载体的既有行为普适性定理自动当成此无限域桥接。

**命题 99.5（因子—单位纤维）。** 对每个 $d\mid H$，模 $H$ 余数中 $\gcd(r,H)=d$ 的纤维大小为 $\varphi(H/d)$，因此

$$
\sum_{d\mid H}\varphi(H/d)=H,\qquad \varphi(5040)=1152.
$$

**证明。** 当 $d<H$ 时，写 $r=du$，$0\le u<H/d$；恒等式 $\gcd(du,H)=d\gcd(u,H/d)$ 将该纤维与模 $H/d$ 的单位一一对应。当 $d=H$ 时只含 $r=0$，其大小为 $\varphi(1)=1$。所有余数按 gcd 分割即给总和。对 5040，Euler 乘积给 $5040(1-1/2)(1-1/3)(1-1/5)(1-1/7)=1152$。 $\square$

乘法动作只需饱和因子深度；加法还需纤维内的单位标签。如果另外选用基标签 Hilbert 实现，基双射给 $\mathbb C^H\cong\bigoplus_{d\mid H}\mathbb C^{\varphi(H/d)}$；这是不同大小纤维的直和，不是 $\tau(H)$ 个等大独立张量因子。丢掉单位标签会丢掉状态信息，并可能丢掉相干实现中的相干信息；该实现不把上述基数解释成物理维数定律。

**推论 99.6（第 97 节全部未来定理的 gcd 形式）。** 对正整数 $A,B$，令 $g=\gcd(A,B)$。定理 97.2 对全部素数的特例及其对称形式为

$$
\inf_{C\ge1}\frac{Z(AC)}{Z(BC)}=\frac{Z(g)}{Z(B)},\qquad
\sup_{C\ge1}\frac{Z(AC)}{Z(BC)}=\frac{Z(A)}{Z(g)}.
$$

下确界当且仅当 $A\mid B$ 时能由有限 $C$ 达到，上确界当且仅当 $B\mid A$ 时能由有限 $C$ 达到；可达到时 $C=1$ 即可。对任意实数 $\lambda$，精确的全部共同乘法未来价格支配判据是

$$
\left[\forall C\ge1,\ J_\lambda(AC)\ge J_\lambda(BC)\right]
\iff \log\frac{Z(g)}{Z(B)}\ge\lambda\log\frac AB.
$$

当 $\lambda=1/25$ 时，右侧等价于有理不等式 $[Z(g)/Z(B)]^{25}\ge A/B$。

**证明。** 映射第 97 节的 $(n,m,c)$ 为 $(A,B,C)$。若 $a=v_p(A),b=v_p(B),k=v_p(C)$，则局部比

$$
\frac{G_p(a+k)}{G_p(b+k)}=
\frac{1-p^{-a-k-1}}{1-p^{-b-k-1}}
$$

在 $a>b$ 时严格降向 1，在 $a<b$ 时严格升向 1。下界保留全部缺额方向 $a<b$ 的 $k=0$，让优势方向趋向无穷，其乘积是 $\prod_{a<b}G_p(a)/G_p(b)=Z(g)/Z(B)$。同一实际整数序列
$C_N=\prod_{a>b}p^N$ 同时逼近这个值；存在优势方向时每个有限比值均严格大于下确界，没有优势方向时 $C=1$ 达到。交换 $A,B$ 后取倒数即给上确界和达到条件。共同价格项 $-\lambda\log C$ 相消，取上述下确界得到充要判据。若判据失败，真实 $C_N$ 序列中必有一个有限成员反转价格次序，不要求下确界被取到。这是既有全部未来结果的特化与对称重写。 $\square$

当 $\lambda>0$，判据本身蕴含 $A\le B$，因为左侧对数非正，而 $A>B$ 会使右侧为正。这保证单一数值预算下 $AC\le BC$；若要用 $A$ 剪掉 $B$，还须每个 $B$ 的合法继续量在 $A$ 下合法，或已有保持所需比较的可行性运输证明。同余、历史、素数分配、指数帽等限制不由大小自动保持。受限未来族上，上述无约束判据仍充分，但未必必要；它不处理加法未来，也不把价格支配变成完整 Robin 目标支配。

**推论 99.7（上下文 Robin 支撑界与动作—值分离）。** 令 $H=5040$、$L=\operatorname{lcm}(C,H)$。每个 $N=CA$ 满足

$$
J_{1/25}(N)\le J_{1/25}(L),\qquad
Z(N)\le Z(L)(N/L)^{1/25}.
$$

若 $N>5040$，写 $E=\log N>1$，则

$$
\Delta_{\mathrm{Robin}}(N)=\gamma+\log\log E-\log Z(N)
\ge\gamma+\log\log E-\frac E{25}-J_{1/25}(L).
$$

**证明。** 第一式直接应用定理 99.1，移项后指数化得到第二式；代入 $E$ 给出最后的裕度下界。$N$ 未必含全部模板层，所以 $N/L$ 可以小于 1，这不影响推导。只有右侧在声明的规模区域严格为正时，才给出 Robin 证书。 $\square$

动作 $q(C)$ 不恢复 $\log C$、$Z(C)$ 或 $J(L)$。例如 $C=11$ 与 $121$ 同有 $q=1$ 和动作 5040，但两者权重、规模与目标值不同；新增的第 2 个 11 层严格降价目标，所以各自 $J(L)$ 也不同。需要定量值时须另存规模、权重或严谨上下界。只乘法区域的动作状态可压至 60 态，后续仍有加法则须保留细余数或显式保留来源重读接口，不能从粗态无损恢复细态。固定价格支撑线没有证明所有无限尺度的正性。

[上下文有限结果](../../reports/fib-robin-boundary/context_completion.json)对应 $263$ 个上下文及 $34384$ 个候选动作比较、全部 $3600$ 个状态积和 $216000$ 个结合律三元组、$5040$ 个单位纤维坐标，以及 $32768$ 个实际共同未来的 gcd 端点比较。$A,B\le64$ 的 $4096$ 个有序对中，$388$ 对满足永久价格支配判据，其余 $3708$ 对均有有限反向续接见证。目标次序用 $\exp(25J(n))=\sigma(n)^{25}/n^{26}$ 化为精确有理比较；这些有限事实不代替上述全称证明。两节均为既有数学输入上的纸面推导和有限证据，不取得新增 Lean 内核证明身份，也不提出原创性或 RH 完成结论。

## 追加锚（递归块 Robin 主编码批次后）

## 100. 操作库决定的最优补全边界、共同来源合并与条件记录容量

### 100.1 任务、操作库与任意有限续接

**定义 100.1（指定操作库的动作行为）。** 固定整数 $H\ge2$，目标是准确返回

$$
F_H(C)=\frac{H}{\gcd(C,H)},\qquad C\ge1.
$$

在定理 99.1 的逐素数严格单峰前提下，这就是上下文的唯一数值最优补全动作；特别地，价格 $1/25$ 对应 $H=5040$。本节直接复用该定理，不以无约束全局唯一性替代其逐轴前提。一般 $H$ 的下述分类针对指定函数 $F_H$，不要求每个 $H$ 都来自某个价格。

给定有限加法库 $\mathcal A=\{c_1,\ldots,c_s\}$，各 $c_i$ 是已声明块的正整数数值。输入操作为任意正标量乘法 $C\mapsto mC$，$m\ge1$，以及 $C\mapsto C+c_i$。合同要求：全部正整数初态均可输入，允许任意有限操作词（含空词），每个词后都能准确读出；表示和更新确定，状态独自承担任务，删除内部后不能免费重读来源，也不能调用额外 oracle。词长没有预设上限。记

$$
d=\gcd(H,c_1,\ldots,c_s),
$$

空加法库时约定 $d=H$。行为等价表示对每个相同合法续接词都有相同 $F_H$，等价地有相同 $q_H(C)=\gcd(C,H)$。

这里允许的每个词都是有限的，但词的集合不受统一长度限制；并非断言任意一个有限来源 DAG 都有这些续接权限。固定 DAG、有限剩余步数、部分初态、近似输出或允许重读来源，均是另一合同，可能有更小的边界。下文“状态数”只指该行为商的基数，不是物理维数、运算步数或二进制位数。用 $\varphi_E$ 表示 Euler 函数，$\varphi_E(1)=1$，与黄金比记号区分。

### 100.2 模平移闭包与全局仿射形式

**定理 100.2（有限加法库的仿射闭包）。** 模 $H$ 上，加法库生成的平移恰为 $d\mathbb Z/H\mathbb Z$；全部合法词的作用恰为

$$
C\longmapsto aC+db\pmod H.
$$

因此

$$
x\sim_{H,d}y
\quad\Longleftrightarrow\quad
\gcd(ax+db,H)=\gcd(ay+db,H)
\quad\text{对每个 }a\in\mathbb Z/H\mathbb Z,\ b\in\mathbb Z/(H/d)\mathbb Z.
$$

**证明。** 有限循环群中每个正向平移有有限阶，其逆可由有限次正向平移得到。因此正向加法幺半群就是由 $c_i$ 生成的子群，即 $d\mathbb Z/H\mathbb Z$；空库只生成恒等平移。任意混合词展开为 $aC+t$，新增常数和后续标量放大始终保持 $d\mid t$。反之，先乘 $a$ 的正整数代表，再以原库实现 $db$，便得到每个所列仿射作用。乘数零余数用正整数 $H$ 代表，平移参数可取非负代表；$+d$ 是合法宏平移，不必是库内原始一步，也未给它统一的短实现长度。

所有读出和操作经模 $H$ 投影因子化。每个余数都可由正整数实现，零余数由 $H$ 实现，所以有限模模型与全部正整数源有同一行为商。 $\square$

### 100.3 完整局部编码与可执行的区分续接

**定理 100.3（局部分类及全局实现）。** 设 $p^h\parallel H$，$h\ge1$，令

$$
e=v_p(d),\qquad 0\le e\le h,\qquad k=h-e,\qquad M=p^k.
$$

对 $x\bmod p^h$，非零余数的截断深度为 $r=\min(v_p(x),h)$，零余数直接规定 $r=h$。以不同标签区分以下两类：

$$
\eta_{p,h,e}(x)=
\begin{cases}
S(r,u),&r<e,\quad u=(x/p^r)\bmod M,\\
D(z),&r\ge e,\quad z=(x/p^e)\bmod M.
\end{cases}
$$

低类型 $S$ 的 $u$ 取模 $M$ 的单位类；$M=1$ 时单位类集合仍为单点，可记作 $0\bmod1$，而非要求其代表整数 0 素于 $p$。该编码恰好分类所有标量乘法和 $p^e$ 倍平移后的截断深度响应。全局编码

$$
\eta_{H,d}(x)=\bigl(\eta_{p,h_p,e_p}(x)\bigr)_{p\mid H}
$$

恰好分类定理 100.2 的全局行为。

**证明。** 编码不依赖代表：高类型的商在换代表后增加 $p^{h-e}$ 的倍数，低类型的单位商增加 $p^{h-r}$ 的倍数，且 $h-r>h-e$。

先证局部充分性。高类型 $D(z)$ 保留完整余数 $p^ez\bmod p^h$。同一低类型的两个源可写成 $x=p^ru,y=p^ru'$，其中 $r<e$，$p^k\mid u-u'$。对任意正乘数 $a$，令 $s=v_p(a)$。若 $r+s<e$，加任意 $p^e$ 倍平移不能改变最低非零层，二者深度同为 $r+s$。若 $r+s\ge e$，则

$$
v_p(a(x-y))\ge s+r+k\ge e+k=h,
$$

所以乘后余数相同，加同一平移仍相同；相同整数之差为零时直接使用整除表述。此论证包括结果饱和为零余数的情形。

再证必要性。当前深度不同，空续接即区分。当前深度相同且 $r<e$，但单位类不同，先乘 $a=p^{e-r}$，再平移 $p^e\delta$，取 $\delta\equiv-u\pmod M$。第一源成为零模 $p^h$，第二源与其差 $p^e(u'-u)$ 非零模 $p^h$。若同深度 $r\ge e$ 而 $D(z)\ne D(z')$，取 $a=1$、$\delta\equiv-z\pmod M$ 即可。两种情形都把一个读出推至饱和而另一个未饱和。

上述平移须落实到全局 $db$。写 $d=p^et$，则 $p\nmid t$。当 $M>1$，$t=d/p^e$ 在模 $p^{h-e}$ 可逆；所需局部 $p^e\delta$ 由

$$
b\equiv\left(\frac d{p^e}\right)^{-1}\delta\pmod{p^{h-e}}
$$

实现。特别地，消去第一源时可取

$$
b\equiv-\frac{ax}{p^e}\left(\frac d{p^e}\right)^{-1}\pmod{p^{h-e}}.
$$

这个全局 $a$ 和 $db$ 可同时改变其他素数方向；只要指定 $p$ 方向的 gcd 指数不同，两个全局 gcd 就不同，无须固定其余方向。原加法库的闭包保证 $db$ 有合法有限词实现。$M=1$ 时同深度没有不同单位坐标，只有已由空词区分的不同深度，不需对模一调用逆元。

全局编码相同蕴含每根轴的所有响应相同；编码不同则选一根不同的轴并用上述全局续接区分。任意一组局部余数均由中国剩余定理共同实现，故没有把不相容来源的局部状态强拼成虚假全局源。 $\square$

### 100.4 最小状态数及端点

**推论 100.4（精确状态乘积）。** 定义 100.1 的合同下，最小确定性状态数为

$$
\kappa_H(d)=\prod_{p\mid H}\kappa_{p,h_p}(e_p),\qquad
\kappa_{p,h}(e)=p^{h-e}+e\varphi_E(p^{h-e}).
$$

**证明。** 局部高类型有 $M=p^{h-e}$ 个值；低类型有 $e$ 个深度，各有 $\varphi_E(M)$ 个单位类。每个高类型取源 $p^ez$；每个低类型选择其单位类的素于 $p$ 的整数提升，再乘 $p^r$。模一时可选单位提升 1。中国剩余定理实现全部局部组合，得到乘积。不同的行为类若被合并为同一确定性状态，在相同区分词后必被迫给相同输出，违背准确性；定理 100.3 的编码达到该下界。 $\square$

端点为：$e=0$ 时没有低类型，$D(z)$ 就是完整模 $p^h$ 余数，共 $p^h$ 态；$e=h$ 时 $M=1$，每个 $r<h$ 有一个低类型，另有 $D(0)$，共 $h+1$ 态，该轴允许的平移皆为零。零余数总属于 $D(0)$，当前深度为 $h$。因此 $d=1$ 给 $H$ 态，$d=H$ 给 $\tau(H)$ 态，与第 99 节的两端合同相接。$H=1$ 可另取空乘积，只有一个状态和恒定输出 1。

### 100.5 读出、操作更新与两个抽象操作数相乘

**定理 100.5（封闭更新）。** 固定 $p,h,e,k,M$ 如上，各坐标按模 $M$ 计算。令 $\nu_{p,k}(z)$ 为模 $p^k$ 的截断深度，零余数取 $k$，则读出为

$$
S(r,u)\longmapsto r,\qquad
D(z)\longmapsto e+\nu_{p,k}(z).
$$

各轴的 $p$ 幂相乘恢复 gcd，进而恢复 $F_H$。对允许加数 $c=p^e\delta$，更新为

$$
D(z)\longmapsto D(z+\delta),\qquad
S(r,u)\longmapsto S(r,u+p^{e-r}\delta).
$$

对正乘数 $m=p^sv$，$p\nmid v$，更新为

$$
D(z)\longmapsto D(mz),\qquad
S(r,u)\longmapsto
\begin{cases}
S(r+s,vu),&r+s<e,\\
D(p^{r+s-e}vu),&r+s\ge e.
\end{cases}
$$

对两个同合同的抽象操作数，乘法良定义且满足

$$
D(z)D(w)=D(p^ezw),\qquad S(r,u)D(z)=D(p^ruz),
$$

$$
S(r,u)S(s,v)=
\begin{cases}
S(r+s,uv),&r+s<e,\\
D(p^{r+s-e}uv),&r+s\ge e.
\end{cases}
$$

**证明。** 直接展开整数代表 $p^ru$ 和 $p^ez$ 的和、标量积及二元积，再按编码除去相应 $p$ 幂。低类型平移中 $e-r\ge1$，故不会破坏单位性；$M=1$ 时只更新唯一坐标。所有被忽略的单位误差均为 $M$ 的倍数，乘后在新坐标中仍为 $M$ 的倍数。公式也包含 $r+s\ge h$ 的饱和、$e=0$、$e=h$ 及正乘数代表零余数的情形。

另从行为等价看，对每个固定正标量乘法稳定且数值乘法交换，因而 $x\sim x'$、$y\sim y'$ 推出 $xy\sim x'y\sim x'y'$。所以二元积由数值乘法投影，结合、交换，单位是源 1 的状态。该结论不授权任意两个压缩操作数的加法；平移仍须满足既定库或已证等效宏平移合同。 $\square$

### 100.6 共同来源合并取实际像

**定理 100.6（操作单调性与同源联合）。** 若 $d_{\mathrm{new}}\mid d_{\mathrm{old}}\mid H$，从 $\eta_{H,d_{\mathrm{new}}}$ 有唯一诱导投影到 $\eta_{H,d_{\mathrm{old}}}$ 的实际像。对于同一正整数源 $C$，联合观察

$$
C\longmapsto\bigl(\eta_{H,d_1}(C),\eta_{H,d_2}(C)\bigr)
$$

与 $\eta_{H,\gcd(d_1,d_2)}(C)$ 有完全相同的源纤维。因此二者实际像之间存在保持来源映射的双射，联合实际像的基数为 $\kappa_H(\gcd(d_1,d_2))$，而非任意两个标签集的笛卡尔积基数。

**证明。** 新平移子群包含旧平移子群，故新行为等价更细。也可局部检查：$e_{\mathrm{new}}\le e_{\mathrm{old}}$，新高类型保存完整局部余数，能求旧类型；新低类型的深度低于两个 $e$，且保留的单位模数不小于旧模数，可向下投影。由分类的充分必要性，局部等价关系随 $e$ 构成嵌套链。联合观察在每根轴取两种等价关系之交，恰为 $e=\min(e_1,e_2)$ 的较细者，而

$$
v_p(\gcd(d_1,d_2))=\min(v_p(d_1),v_p(d_2)).
$$

故全局联合纤维恰为所述编码纤维；中国剩余定理给实际像基数，定理 100.5 给混合操作的更新闭合。 $\square$

两摘要必须来自同一个实际源，不能独立选择不相容标签。上述结论使用已证的局部嵌套分类；一般控制系统中，两套库分别得到的行为摘要之联合未必已经对混合词闭合，不能无条件迁移本例结论。

### 100.7 已知 gcd 后的最少记录取值数

**定理 100.7（条件记录容量）。** 已知粗状态 $q_H(C)=g$，希望再记录一个有限映射 $\rho:\mathbb Z/H\mathbb Z\to R$，使某个解码器满足

$$
\operatorname{Dec}(q_H(C),\rho(C))=\eta_{H,d}(C)
\quad\text{对全部正整数 }C.
$$

此处 $R=\operatorname{im}\rho$，$|R|$ 是同一个有限记录映射的不同取值个数。允许解码依赖已经知道的 $g$，不要求记录单独执行状态更新。最少记录取值数为

$$
\min_{\rho,\operatorname{Dec}}|R|=\varphi_E(H/d).
$$

**证明。** 固定一根轴的粗深度 $r$，其粗纤维中精细类数为

$$
f_{p,h,e}(r)=
\begin{cases}
\varphi_E(p^{h-e}),&r<e,\\
\varphi_E(p^{h-r}),&e\le r<h,\\
1,&r=h.
\end{cases}
$$

低类型只剩单位类；高类型 $z$ 的固定深度为 $r-e$，单位部分按模 $p^{h-r}$ 分类；零余数只有一个类。所有这些类均可实现。固定 $g\mid H$ 时，中国剩余定理给精确全局类数

$$
N_g=\prod_{p\mid H}f_{p,h_p,e_p}(v_p(g)).
$$

因为 $\varphi_E(p^j)$ 对整数 $j\ge0$ 单调不减，局部最大值为 $\varphi_E(p^{h-e})$，且 $r=0$ 达到，包括 $e=0$ 与 $e=h$。所以

$$
\max_{g\mid H}N_g
=N_1
=\prod_{p\mid H}\varphi_E(p^{h_p-e_p})
=\varphi_E(H/d).
$$

同一 $g$ 纤维内两个精细类必须取不同记录值，否则解码器无法区分，故 $|R|\ge\max_gN_g$。反之，在每个 $g$ 纤维内给精细类编号，跨纤维复用同一个大小为 $\max_gN_g$ 的值集，解码器以 $(g,\text{编号})$ 复原，即达到下界。 $\square$

该数是最大条件纤维容量，不是总状态数之商、平均信息量，也不表示各纤维等大。若记录用字符串表示，$|R|$ 数的是实际可取的不同完整记录，而非字符数或无限制变长字符串的底层字母表大小；二元字母表可以通过长度编码任意有限值集，不能据本定理给字符表大小设同样下界。

定理不提供从旧 $g$ 免费算出记录的方法：同一粗纤维中的不同精细类已被合并，任何仅对 $g$ 的后处理都不能恢复它们。须在丢弃源前保存足够记录；若允许重读或额外观测，则需另行声明合同和成本。

### 100.8 5040 的中间容量、显式更新与宏接口

**命题 100.8（5040 操作库实例）。** 对 $H=5040=2^4 3^2 5\cdot7$，始终允许任意正标量乘法，下表给出最小行为状态数与已知 gcd 后的最少记录取值数：

| 100.8 允许加数库 | $d$ | $\kappa_{5040}(d)$ | $\varphi_E(5040/d)$ |
|---|---:|---:|---:|
| 100.8 无加数 | 5040 | 60 | 1 |
| 100.8 加数 2 | 2 | 3780 | 576 |
| 100.8 加数 3 | 3 | 2800 | 384 |
| 100.8 加数 5 | 5 | 2016 | 288 |
| 100.8 加数 7 | 7 | 1440 | 192 |
| 100.8 加数 10 | 10 | 1512 | 144 |
| 100.8 加数 13 | 1 | 5040 | 1152 |
| 100.8 加数 2520 | 2520 | 60 | 1 |
| 100.8 分别开放加数 2、5 | 1 | 5040 | 1152 |

只开放 $+2520$ 时，令 $q=\gcd(C,5040)$、$r=v_2(q)\in\{0,1,2,3,4\}$，该 60 态上的更新是

$$
q\longmapsto
\begin{cases}
q,&r<3,\\
2q,&r=3,\\
q/2,&r=4.
\end{cases}
$$

同源的 $+7$ 摘要和 $+10$ 摘要各有 1440、1512 态，联合实际像仅有 5040 态。

**证明。** 状态数和记录数分别代入推论 100.4、定理 100.7。对 $+2520$，模 $3^2,5,7$ 都是零平移；模 16 是加 8。深度 $r<3$ 不变，深度 3 的唯一余数 8 变 0，深度 4 的余数 0 变 8，给所列更新。联合像用 $\gcd(7,10)=1$ 和定理 100.6。于是增加操作不一定严格增加状态数：$d=5040$ 与 $2520$ 给相同粗分区，但不授权一般加法。 $\square$

**命题 100.9（宏操作与暴露微操作的区别）。** 数值块 $[2+5]$ 作为允许加数给 $+7$ 合同，而 $[2]\cdot[5]$ 作为允许加数给 $+10$ 合同；相同叶子集不决定行为容量。如果 $+7$ 内部实现为先 $+2$ 再 $+5$，且中间既不观察、也不允许插入其他操作，外部仍只需要 1440 态。若分别开放 $+2$、$+5$ 供任意调用，则需要 5040 态；旧宏状态不能一般地承担其中间读出。

**证明。** $\gcd(5040,7)=7$、$\gcd(5040,10)=10$，容量见命题 100.8。封闭宏的外部净作用是 $C\mapsto C+7$，可以直接使用宏更新；这不证明同一个宏边界能逐步实现两个微更新，内部也可能需要临时细状态。具体取 $C=5,725$：在 $2,3,5$ 方向两者分别模 $16,9,5$ 相同，在 7 方向同为深度 0，所以 $\eta_{5040,7}(5)=\eta_{5040,7}(725)$。但同加 2 后为 7 与 727，当前 gcd 分别为 7 和 1。故宏状态不足以提供该中间输出。分别开放两加数后，$\gcd(5040,2,5)=1$，推论 100.4 给精确 5040 态。 $\square$

只开放固定微路径的中间观测、却不开放任意重排时，仍须分析那个更强合同，不能自动套用“任意调用 $+2,+5$”的精确状态数。剩余步数、额外程序计数器和固定控制路径都会改变可允许的续接集合。

若块 $[13]$ 来源标识为 Fibonacci 素数 $F_7=13$，本节加数仍是数值 13，故 $d=1$；来源索引 7 不能代替数值加数。7 可由原始素 Fib 叶子 2、5 相加得到，不要求 7 自身是 Fibonacci 数。操作类型与来源引用仍属于原始关系层，本节编码不恢复来源树。完整动作状态也不恢复 $Z(C)$、$J(C)$ 或 Robin 余量；这些目标仍须保留第 99 节说明的额外规模和值信息。

### 100.9 有限行为细化的完备性

**命题 100.10（与候选编码无关的行为细化）。** 对有限模状态集，先按 $\gcd(x,H)$ 分区，再反复按当前类及每个生成操作的后继类细化，稳定后恰得全部有限生成词的行为商。若生成标量为模 $H$ 单位群的一组生成元及各 $p\mid H$，再加入平移 $+d$，则所得行为商正是本节全操作库的行为商。

**证明。** 第 $t$ 次细化的等价关系恰为长度不超过 $t$ 的生成词下所有输出相同：初始为长度零，归纳时按词首操作及剩余后缀分解。每次真细化增加类数，有限载体上必停止；稳定关系对生成操作闭合，故对全部有限词闭合。不同最终类已有有限区分词。全过程只使用具体模转移和 gcd 读出，不用候选编码或计数公式作为分区依据。

对任意正整数 $m$，移去所有整除 $H$ 的素因子后，剩余部分与 $H$ 互素，所以模 $H$ 的每个标量作用由所列素因子乘法和单位乘法合成，包括由正代表 $H$ 实现的零余数。单位群生成性需独立确认，不能由行为状态数吻合推断；也可直接从余数 1 沿乘法生成元遍历，核对到达模 $H$ 的全部余数。$+d$ 与原加法库生成同一平移群，见定理 100.2。生成词和原库词可互相展开为有限词，故其完整行为商相同；展开的长度可以不同。 $\square$

本节为指定操作合同下的数学推导；有限实例可核对分类、更新与区分见证，但不替代全称证明。本节不取得新增 Lean 内核证明身份，不提出原创性或 RH 完成结论，也不解除无限尺度 Robin 正性义务。

## 追加锚（递归块 Robin 主编码批次后）

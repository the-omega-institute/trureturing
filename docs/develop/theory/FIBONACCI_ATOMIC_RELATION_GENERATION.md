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

## 附录 FAR：有限加法读出的实际相干态与陪集谱

本节把第 46.1 节所需的共同来源分块写成一般有限加法群命题。振幅从实际来源逐项求和，约化矩阵从该振幅的纯态密度取偏迹；陪集分块、投影与谱均为结论。本节是项目内的有限群与 Schmidt 分解推导，不提出原创性主张。

**定理 46.1a（联合单射有限加法读出的实际态、完整谱与熵）。** 设 $G,A,B$ 为有限加法交换群，$\alpha:G\to A$、$\beta:G\to B$ 为加法群同态，并假设配对映射

$$
f:G\longrightarrow A\times B,\qquad f(x)=(\alpha(x),\beta(x))
$$

单射。不要求任一读出满射，也不要求任一读出单独恢复来源。记

$$
\begin{aligned}
N&=|G|,& K_A&=\ker\alpha,& K_B&=\ker\beta,\\
H&=K_A+K_B=\{s+t:s\in K_A,\ t\in K_B\},&
Q&=G/H,& R&=|Q|,\\
k_A&=|K_A|,& k_B&=|K_B|,& \lambda&=\frac{k_Ak_B}{N}.
\end{aligned}
$$

各群均含零元，故 $N,k_A,k_B,R$ 为正整数；分式、平方根和对数中的基数均取其实数值，矩阵系数再嵌入复数。$\sqrt{\cdot}$ 取正平方根，$\log$ 为自然对数。对谓词 $P$，$\mathbf1_{[P]}$ 在 $P$ 成立时为 1，否则为 0；对集合 $E$，$\mathbf1_E$ 为其指标函数。

在标准正交基 $\{|a\rangle:a\in A\}$、$\{|b\rangle:b\in B\}$ 上定义实际系数矩阵、相干向量及联合纯态密度：

$$
\begin{aligned}
C(a,b)&=\frac1{\sqrt N}\sum_{x\in G}
  \mathbf1_{[\alpha(x)=a\ \land\ \beta(x)=b]},
  &&C\in\mathbb C^{A\times B},\\
|\Psi\rangle&=\frac1{\sqrt N}\sum_{x\in G}
  |\alpha(x)\rangle\otimes|\beta(x)\rangle
  =\sum_{a\in A,\ b\in B}C(a,b)|a\rangle\otimes|b\rangle,\\
J\bigl((a,b),(a',b')\bigr)&=C(a,b)\overline{C(a',b')}.
\end{aligned}
$$

这里没有来源依赖的相位。取实际偏迹，约定 $\operatorname{partialTraceRight}$ 消去 $B$、保留 $A$，$\operatorname{partialTraceLeft}$ 消去 $A$、保留 $B$：

$$
\begin{aligned}
\rho_A(a,a')&=\operatorname{partialTraceRight}(J)(a,a')
  =\sum_{b\in B}J\bigl((a,b),(a',b)\bigr),\\
\rho_B(b,b')&=\operatorname{partialTraceLeft}(J)(b,b')
  =\sum_{a\in A}J\bigl((a,b),(a,b')\bigr).
\end{aligned}
$$

上述对象满足以下全部结论。

核与归一化为

$$
\begin{gathered}
K_A\cap K_B=\{0\},\qquad |H|=k_Ak_B,\qquad
N=Rk_Ak_B,\qquad \lambda=\frac1R>0,\\
\sum_{a\in A,\ b\in B}|C(a,b)|^2=\langle\Psi,\Psi\rangle=1.
\end{gathered}
$$

$J$ 为 Hermitian 正半定矩阵，$\operatorname{Tr}J=1$、$J^2=J$、$\operatorname{rank}_{\mathbb C}J=1$，因此确为归一化纯态密度。

对任意 $q\in Q$，任选代表 $x\in q$，定义两侧标签集

$$
A_q=\alpha(x)+\alpha(K_B),\qquad
B_q=\beta(x)+\beta(K_A).
$$

这些集合与代表无关，$|A_q|=k_B$、$|B_q|=k_A$；不同 $q$ 的 $A_q$ 两两不交，$B_q$ 也两两不交，且

$$
\alpha(G)=\bigsqcup_{q\in Q}A_q,\qquad
\beta(G)=\bigsqcup_{q\in Q}B_q.
$$

实际配对读出把每个来源陪集 $q$ 双射到 $A_q\times B_q$。故每块有 $k_B$ 个 $A$ 标签、$k_A$ 个 $B$ 标签，块内每个系数恰为 $1/\sqrt N$；块外为零。实际矩阵条目为

$$
\begin{aligned}
C(a,b)&=\frac1{\sqrt N}\sum_{q\in Q}
  \mathbf1_{A_q}(a)\mathbf1_{B_q}(b),\\
\rho_A(a,a')&=\frac{k_A}{N}\sum_{q\in Q}
  \mathbf1_{A_q}(a)\mathbf1_{A_q}(a'),\\
\rho_B(b,b')&=\frac{k_B}{N}\sum_{q\in Q}
  \mathbf1_{B_q}(b)\mathbf1_{B_q}(b').
\end{aligned}
$$

因此 $\rho_A$ 的每个支撑块条目是 $k_A/N$，$\rho_B$ 的每个支撑块条目是 $k_B/N$。定义归一化块指标向量

$$
u_q(a)=\frac{\mathbf1_{A_q}(a)}{\sqrt{k_B}},\qquad
v_q(b)=\frac{\mathbf1_{B_q}(b)}{\sqrt{k_A}}.
$$

两族分别在 $\mathbb C^A$、$\mathbb C^B$ 中正交归一。以 $w^*$ 表示共轭转置，有实际 Schmidt 分解与矩阵恒等式

$$
\begin{aligned}
|\Psi\rangle&=\sqrt\lambda\sum_{q\in Q}u_q\otimes v_q,\\
C(a,b)&=\sqrt\lambda\sum_{q\in Q}u_q(a)v_q(b),\\
P_A&=\sum_{q\in Q}u_qu_q^*,&
P_B&=\sum_{q\in Q}v_qv_q^*,\\
\rho_A&=\lambda P_A,& \rho_B&=\lambda P_B,\\
P_A^2&=P_A=P_A^*,& P_B^2&=P_B=P_B^*,\\
\rho_A^2&=\lambda\rho_A,& \rho_B^2&=\lambda\rho_B.
\end{aligned}
$$

$P_A,P_B$ 是对应块向量张成空间的正交投影。两约化矩阵均 Hermitian 正半定、迹为 1，且

$$
\operatorname{rank}_{\mathbb C}C
=\operatorname{rank}_{\mathbb C}\rho_A
=\operatorname{rank}_{\mathbb C}\rho_B
=R\le\min(|A|,|B|).
$$

完整特征值按重数计算：$\rho_A$ 的 $\lambda$ 特征空间为 $\operatorname{span}\{u_q:q\in Q\}$，代数与几何重数均为 $R$；零特征空间为其正交补，重数均为 $|A|-R$。$\rho_B$ 对应地有 $\lambda$ 重复 $R$ 次、零重复 $|B|-R$ 次。重数为零时该特征值不出现；这些零重数包含块内与常量向量正交的方向和读出像之外的全部标签方向。$C$ 的非零奇异值均为 $\sqrt\lambda$，共 $R$ 个，因而 $|\Psi\rangle$ 的 Schmidt 秩为 $R$。按完整特征值列表定义 von Neumann 熵，约定 $0\log0=0$，得到

$$
S(\rho_A)=S(\rho_B)
=-R\lambda\log\lambda
=\log R
=\log N-\log k_A-\log k_B.
$$

**证明。** 若 $z\in K_A\cap K_B$，则 $f(z)=f(0)$，联合单射给出 $z=0$。加法映射 $K_A\times K_B\to H$ 满射；若 $s+t=s'+t'$，则 $s-s'=t'-t$ 属于交核，故 $s=s'$、$t=t'$。所以该映射双射，$|H|=k_Ak_B$。每个 $H$ 陪集的大小为 $|H|$，陪集划分 $G$，得 $N=Rk_Ak_B$。此外 $f$ 单射使实际振幅和中的每个位置至多有一个来源，恰有 $N$ 个非零位置，每个为 $1/\sqrt N$，故向量范数平方为 1。外积 $J$ 于是正半定、Hermitian、迹为 1；$J^2=\langle\Psi,\Psi\rangle J=J$，其像为非零向量 $\Psi$ 张成的一维空间。

交核为零还说明 $\alpha$ 在 $K_B$ 上、$\beta$ 在 $K_A$ 上分别单射，故标签集大小分别是 $k_B,k_A$。若更换代表 $x$ 为 $x+s+t$，其中 $s\in K_A,t\in K_B$，则 $\alpha(x)$ 只平移一个 $\alpha(K_B)$ 元素，$\beta(x)$ 只平移一个 $\beta(K_A)$ 元素，两标签集不变。若 $A_q,A_{q'}$ 相交，取代表 $x,y$ 及 $t,t'\in K_B$ 使 $\alpha(x+t)=\alpha(y+t')$，则 $x-y+t-t'\in K_A$，故 $x-y\in H$，即 $q=q'$。$B_q$ 的不交性同理；任一实际读出标签属于其来源所在陪集的标签集，反向包含由定义给出，故两侧确为读出像的划分。

每个 $q=x+H$ 的来源唯一写成 $x+s+t$，$s\in K_A,t\in K_B$，且

$$
f(x+s+t)=\bigl(\alpha(x)+\alpha(t),\ \beta(x)+\beta(s)\bigr).
$$

两个核参数独立遍历；由各自受限读出的单射性，该式给出 $q\to A_q\times B_q$ 的双射。因此由原始来源和直接得到上述 $C$ 的块公式。把它代入已经定义的实际偏迹，利用各块指标为实数，得到

$$
\begin{aligned}
\rho_A(a,a')
&=\frac1N\sum_{q,r\in Q}
 \mathbf1_{A_q}(a)\mathbf1_{A_r}(a')
 \sum_{b\in B}\mathbf1_{B_q}(b)\mathbf1_{B_r}(b),\\
\sum_{b\in B}\mathbf1_{B_q}(b)\mathbf1_{B_r}(b)
&=\begin{cases}k_A,&q=r,\\0,&q\ne r.\end{cases}
\end{aligned}
$$

这给出 $\rho_A$ 的条目公式；交换两侧，内层计数为 $k_B$，给出 $\rho_B$ 的条目公式。此处使用的是实际共同来源的支撑，未把候选约化矩阵或候选谱当作假设。

支撑不交及标签集大小给出 $\langle u_q,u_r\rangle=\langle v_q,v_r\rangle=\mathbf1_{[q=r]}$。由于 $\sqrt\lambda/\sqrt{k_Ak_B}=1/\sqrt N$，系数块公式恰为所列 Schmidt 分解；由于 $\lambda/k_B=k_A/N$、$\lambda/k_A=k_B/N$，偏迹块公式恰为两投影公式。正交归一性使 $P_A,P_B$ 均自伴且平方等于自身，因此约化矩阵的平方关系、正半定性与 $\operatorname{Tr}\rho_A=\operatorname{Tr}\rho_B=R\lambda=1$ 随之成立。

在 $u_q$ 张成空间上 $\rho_A$ 作用为乘 $\lambda$，在其正交补上作用为零。前者维数为 $R$，后者为 $|A|-R$；两个特征空间给出整个 $\mathbb C^A$ 的直和分解，故完整代数与几何重数如述。$B$ 侧同理。作为从 $\mathbb C^B$ 到 $\mathbb C^A$ 的线性映射，实系数矩阵 $C$ 把每个 $v_q$ 送到 $\sqrt\lambda u_q$，把它们的正交补送到零，故其秩为 $R$、非零奇异值为 $\sqrt\lambda$。最后把两侧的完整谱代入熵定义，用 $\lambda=1/R$ 及所有基数为正，得到熵的各个等式。$\square$

平凡群和非满射读出都在定理范围内：当 $G=\{0\}$ 时 $N=k_A=k_B=R=1$，实际态为 $|0_A\rangle\otimes|0_B\rangle$，两侧各有特征值 1 一次，其余全为零；一般 $R=1$ 时仍是一个归一化乘积块、熵为零。上述证明未删除这些端点。

第 46.1 节的直接消费者取 $G=(\mathbb Z/n\mathbb Z)^2$，$n\ge1$，$A,B$ 各为两个端口标签的乘积群，$\alpha,\beta$ 为同一来源的四个互异自然时刻读数按任意两对切分。此时 $N=n^2$，实际振幅因子 $1/\sqrt N=1/n$。把两侧核基数与对应时刻间隔的 $\gcd(n,F_{d_A})$、$\gcd(n,F_{d_B})$ 接合，才得到第 46.1 节的秩与对数表达式。对应通用结果及保留原有联合单射假设的全切分精确应用已通过 Lean 编译，包含原始 ket 的逐项相等、任意端口重排、两侧算术接口、实际矩阵条目、投影、特征空间、Schmidt 分解、完整奇异值和重数，以及 $n=1$ 和熵公式。精确应用仅为临时核验，不新增绑定声明；本节正文仍为参考输入，不表示新增冻结或 atom 覆盖。

## 追加锚（有限加法读出附录）

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

### 87.5 严格有限前缀支配的单独解析命题

**定理 87.5（严格有限几何前缀支配）。** 对所有自然数 $a\ge1$ 和实数 $0<z<1$，

$$
\log\left(\sum_{k=0}^{a}z^k\right)
<\sum_{k=1}^{a}\frac{z^k}{k}.
$$

**证明。** 令 $S(t)=(1-t^{a+1})/(1-t)$ 以及
$D(t)=\sum_{k=1}^{a}t^k/k-\log S(t)$。
在 $0\le t<1$，几何和恒等式给出 $S(t)=\sum_{k=0}^{a}t^k>0$。
有限求和与商的求导法则给出

$$
D'(t)=\frac{t^a}{1-t}\left(\frac{a+1}{S(t)}-1\right).
$$

对 $0<t<1$，每个正指数项严格小于 $1$，所以 $S(t)<a+1$，从而 $D'(t)>0$。
又 $D$ 在 $[0,z]$ 连续且 $D(0)=0$，由严格单调性得 $D(z)>0$。 $\square$

本命题是定理 87.2 中严格前缀子句的通用实变量形式；取 $z=1/p$ 得该子句。
$a=0$ 时两侧均为零。它不含定理 87.2 的参考目标最大值与 $R_p(x)\ge0$ 子句，
也不控制 §87.3 的有符号无限尾项。

### 87.6 局部储备的量级与两个拓扑观察边界

以下定量估计与拓扑构造是纸面推导，不扩大定理 87.5 的 Lean 覆盖。
在 $a\ge1$、$0<z<1$ 下，令 $S_a(t)=\sum_{k=0}^a t^k$，
$D_a(t)=\sum_{k=1}^a t^k/k-\log S_a(t)$。对 $0\le t\le z$，

$$
D_a'(t)=\frac{t^a((a+1)-S_a(t))}{(1-t)S_a(t)}
\ge\frac{a t^a}{S_a(z)},\qquad
D_a(z)\ge\frac{a z^{a+1}}{(a+1)S_a(z)}.
$$

这里 $(a+1)-S_a(t)=\sum_{j=1}^a(1-t^j)\ge a(1-t)$，
再从 $0$ 积分；$a=1$ 给出
$z-\log(1+z)\ge z^2/(2(1+z))$。
因此定理 87.4 的**正储备**（区别于 §87.3 的有符号 $\Phi$）满足

$$
B(x)\ge\sum_{\substack{p\text{ 素数}\\\sqrt{2x}\le p\le x-1}}
\frac1{2p(p+1)}.
$$

此界逐项来自 $z=1/p,a=1$，保留原有的正储备量级，
但不估计 $\Phi(x)$，也不推出所有 $n>5040$ 的 Robin 不等式。

对 $n>1$，令 $K_n$ 为真约数偏序集
$\{d:1<d<n,\ d\mid n\}$ 的序复形。
Philip Hall 的链公式给出
$\widetilde\chi(K_n)=\mu(n)$，故 $\chi(K_n)=1+\mu(n)$；
本仓 `StrictDivisorChainMobius` 的冻结链和对应这一交替计数。
若 $p^2\mid n$，映射 $d\mapsto\operatorname{lcm}(d,p)$
在真约数偏序集上满足 $d\le f(d)$ 与 $p\le f(d)$，
由偏序映射的同伦给出到点 $p$ 的收缩。
特别地 $5040=2^4 3^2 5\cdot7$，所以 $K_{5040}$ 可缩且
$\chi(K_{5040})=1$；Klein 瓶的 $\chi=0$，不是这个复形。
§86.2 引用的 Axler (2023, Theorem 3) 与 Hertlein (2018, Theorem 2)
若按其所列充分条件使用，则任何 $n>5040$ 的潜在 Robin 反例都被 $4$ 整除，
故其 $\mu(n)=0$ 且 $K_n$ 可缩；这不排除潜在反例。
Euler 示性数或**无标签**同伦型因此不能单独判定加权 Robin 目标；
完整保留整数标签、端点与权重 $1/d$ 的约数数据仍能恢复
$\sum_{d\mid n}1/d=\sigma(n)/n$。

另构造 Fibonacci 传递矩阵 $Q=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$
在完整 $\mathbb{RP}^1(\mathbb R)$ 上的射影圆映射，
并取 $Q^m$ 的映射环面。对 $v(\theta)=(\cos\theta,\sin\theta)$，
像的角导数为 $\det(Q^m)/\|Q^mv(\theta)\|^2$，
故圆映射的定向度为 $(-1)^m$。
圆同胚按定向类同痕，映射环面在奇数 $m$ 时为 Klein 瓶，
偶数 $m$ 时为环面：$7$ 与所有奇素数步属前者，$5040$ 与素数步 $2$ 属后者。
这是额外构造的**完整实射影圆**上的分类；正 Fibonacci 轨道、
$\mathbb{CP}^1$ 和 Li 的 $\xi$ 圆盘均是不同对象，未得到内禀 zeta 或 RH 拓扑。
Klein 瓶在 $\chi=0$ 时的 Heawood 表达式取值 $7$，但其实际地图色数上限为 $6$；
地图区域着色也不是 Franklin 图的顶点着色。
圆映射环面的分类见 [mapping torus](https://en.wikipedia.org/wiki/Mapping_torus)，
偏序链与约化 Euler 示性数的关系见
[incidence algebra](https://en.wikipedia.org/wiki/Incidence_algebra#Euler_characteristic)，
Klein 着色例外见 [Heawood conjecture](https://en.wikipedia.org/wiki/Heawood_conjecture)。

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

## 101. 增补二·不增加乘法动作边界的加法库

**本批导航。** 本批在第 100 节的操作分辨率分类之上只作两项直接推论：§101 给出何时加法库不细化乘法动作边界，并给出偶数模数的半周直接更新；§102 给出嵌套操作库之间的最少条件记录。旧章和本卷已有追加块逐字不改判。本批所有结论仍以正整数源、精确输出和“删除源后不免费重读”为合同边界。

### 101.1. 合同、状态数与局部记号

固定整数 $H\ge 2$。允许任意正整数乘法，并允许有限正加法库

$$
A=\{c_1,\ldots,c_s\},\qquad
d=\gcd(H,c_1,\ldots,c_s),
$$

空库约定为 $d=H$。每个有限续接词之后都必须准确输出 $H/\gcd(C,H)$；模 $H$ 的零余数用正代表 $H$（或其正倍数）表示。第 100 节的分类把最小行为状态数写成

$$
\kappa_H(d)=\prod_{p^h\parallel H}
\left[p^{h-e}+e\,\phi_E(p^{h-e})\right],
\qquad e=v_p(d),
$$

其中 $\phi_E$ 是 Euler  totient 函数，特意用下标 $E$ 与黄金比记号区分；纯乘法边界是

$$
\tau(H)=\prod_{p^h\parallel H}(h+1).
$$

这里的状态是完整有限续接行为的等价类，不是任意选取的编码标签，也不是物理维数。

**命题 101.1（不增加状态数的完整条件）。**

$$
\boxed{
\kappa_H(d)=\tau(H)
\quad\Longleftrightarrow\quad
d=H\ \text{或}\ (H\ \text{为偶数且}\ d=H/2).}
$$

等价地，若直接用原加法库表述：当 $H$ 为奇数时每个 $c_i$ 都必须被 $H$ 整除；当 $H$ 为偶数时每个 $c_i$ 都必须被 $H/2$ 整除。

**证明。** 固定一个素数幂轴 $p^h\parallel H$，令 $e=v_p(d)$、$k=h-e$。当 $k=0$ 时局部因子是 $1+e=h+1$。当 $k\ge1$ 时，局部因子超过纯乘法因子的差为

$$
p^k+e\phi_E(p^k)-(h+1)
=(p^k-k-1)+e\bigl(\phi_E(p^k)-1\bigr).
$$

两项都非负：$\phi_E(p^k)\ge1$，并且 $p^k\ge2^k\ge k+1$。等号 $p^k=k+1$ 只可能是 $p=2,k=1$；当 $k\ge2$，由 $2^2>3$ 和倍增归纳得 $2^k>k+1$。因此局部因子等于 $h+1$ 恰好发生在 $e=h$，或 $p=2,e=h-1$；后者的第二项也为零，因为 $\phi_E(2)=1$。

每个局部因子至少是正整数 $h+1$，所以正整数乘积相等当且仅当每根轴都相等。奇素数轴只能取 $e=h$；2 轴可以取 $e=h$ 或（仅当存在 2 轴时）$e=h-1$。这正好给出 $d=H$，或 $H$ 偶数且 $d=H/2$。由 $d$ 是所有 $c_i$ 与 $H$ 的 gcd，奇数情形的逐项条件给出 $d=H$；偶数情形的逐项条件给出 $d$ 为 $H$ 或含有奇数倍 $H/2$ 时的 $H/2$。

最后，行为分区总是细于当前的 gcd 读出分区。上面的等号使两者拥有同样的 $\tau(H)$ 个类，故完整有限词行为分区与 gcd 分区相同；这不是两个不同分区碰巧拥有相等基数。$\square$

### 101.2. 半周平移的直接更新

令当前粗状态为 $q=\gcd(C,H)$。任意正乘法仍有闭合更新

$$
q(Cm)=\gcd(qm,H).
$$

若 $H\mid c$，则 $C+c\equiv C\pmod H$，所以加法更新是恒等。其余不增加边界的加法只发生在偶数 $H$：写

$$
H=2^hM,\qquad h\ge1,\quad M\text{ 奇},\qquad c=(H/2)t.
$$

当 $t$ 偶数时仍是整周平移；当 $t$ 奇数时令 $r=v_2(q)\in\{0,\ldots,h\}$（约数 $q$ 的零余数以 $r=h$ 表示），则

$$
\boxed{
q(C+c)=
\begin{cases}
q,&r<h-1,\\
2q,&r=h-1,\\
q/2,&r=h.
\end{cases}}
$$

**命题 101.2（半周更新的端点完备性）。** 对所有正源，当 $t$ 为正奇数时，上述三支公式成立；当 $t$ 为正偶数时，$q(C+c)=q$。两种情形的更新都落在 $H$ 的正约数状态空间中。

**证明。** 在每个奇素数幂模数上，$H/2$ 是零平移，所以局部余数和截断深度不变。在 $2^h$ 轴上，奇数倍的 $H/2$ 等于 $2^{h-1}$。深度小于 $h-1$ 的余数加上它仍保持最低非零位；唯一的深度 $h-1$ 余数 $2^{h-1}$ 加上它成为零；零余数加上它变为 $2^{h-1}$。CRT 合并奇轴不变、2 轴上述切换，得到三支更新。

当 $h=1$ 时第一支为空，深度 0 与深度 1 直接交换；特别地 $H=2$ 的两个余数态已经被 gcd 区分，任何正加数都不再增加状态。若 $r=h-1$，则 $2q\mid H$；若 $r=h$，则 $q/2$ 是正约数，故两条边界也合法。零余数从未要求源为整数零：正源 $C=H$ 或任意正倍数即可代表它；恒等平移用正加数 $H$，乘法零余数用正乘数 $H$。把 $C$、$c$ 或乘数换成大于 $H$ 的正整数只改变同余代表，不改变证明。$\square$

### 101.3. 宏端口与暴露微操作

**命题 101.3（宏端口合同）。** 对 $H=5040$，外部只开放整个 $+2520$ 的合同与分别开放 $+2,+5$ 的合同是不同任务。前者在 60 个 gcd 状态上闭合，后者的联合行为有 5040 个状态；不能由宏端口的状态数推出其内部微操作可被逐步观察或重排。

**证明。** $\gcd(5040,2520)=2520$，命题 101.2 在 2 轴深度 $3\leftrightarrow4$ 之间切换，3、5、7 轴不变，因而只需第 100 节的 60 个 gcd 状态。相反，$\gcd(5040,2,5)=1$，两个微操作的任意有限词可读出全部 5040 个余数。更直接地，两个源 $C=5$ 和 $C=725$ 的 $+7$ 宏状态相同，但一次 $+2$ 后的 gcd 分别为 $\gcd(7,5040)=7$ 与 $\gcd(727,5040)=1$；宏状态不能提供这个中间输出。若 $+7$ 的内部实现固定为先 $+2$ 再 $+5$，而中间不观察、也不插入其它动作，外部仍只面对 $+7$ 端口，故使用 1440 个状态；一旦把两个叶子作为可任意调用的端口，合同已改变，必须按联合行为计算。固定微路径的步数、程序计数器和允许插入的动作都属于合同，不能省略。$\square$

来源标签、Fib 叶子树和数值加数也是不同字段：数值 $13=F_7$ 的块仍是 $+13$，所以 $d=1$；由叶子 2、5 形成数值 7 不要求 7 本身是 Fibonacci 数。任何这些动作状态都不恢复源树、$Z(C)$、$J(C)$ 或 Robin 余量。

### 101.4. 范围与核验边界

独立程序 `coarse_additions.py` 直接枚举 $H=2,\ldots,256$ 的全部正加数代表，逐 gcd 纤维检查后继唯一性；随后在 $H=2,\ldots,48$ 对指定库做以具体模转移为输入的 Moore 稳定细化，最后检查 5040 模板和正提升。它不以 $\kappa_H(d)$ 公式生成待比较分区。实际计数、命令与输出哈希记录在报告 README；这些有限核对支持实现的边界，不替代上面的全称纸面证明。本节没有新增 Lean、kernel、原创性、RH 或物理维数结论。

## 102. 增补三·嵌套操作库的精确条件记录

**本批导航。** 本节固定一次旧到新操作库的细化并计算其最少记录值域；§102.1–102.5 给出局部计数、CRT 同时达到、编号解码、退化端点、不可比较库和 5040 成本，§102.6 给出连续细化的反例与在线边界。它扩充第 100 节的单次记录结论，不把多次最大纤维的数值关系提升为一般分区恒等式。

### 102.1. 一次细化的完整合同

固定 $H\ge2$，旧库和新库分别由 $d_o,d_n$ 表示，并假设

$$
d_n\mid d_o\mid H.
$$

旧摘要是 $\eta_{H,d_o}(C)$，新摘要是 $\eta_{H,d_n}(C)$，两者都要求对每个正源以及每个有限合法续接准确输出 $H/\gcd(C,H)$。允许保存一个有限确定性记录映射

$$
\rho:\mathbb Z_{>0}\longrightarrow R,
$$

其中 $R$ 指实际出现的有限记录值集合。解码器收到 $(\eta_{H,d_o}(C),\rho(C))$，可依赖旧摘要，也允许不同旧摘要纤维复用同一个标签；记录不要求单独在线更新，也不允许在源已删除后免费重读或调用未声明 oracle。目标是存在

$$
\operatorname{Dec}\bigl(\eta_{H,d_o}(C),\rho(C)\bigr)=\eta_{H,d_n}(C)
$$

对所有正 $C$ 成立。

**命题 102.1（最少记录值数）。** 令 $m_H(d_o,d_n)$ 为满足上述合同的 $|R|$ 的最小值，则

$$
\boxed{
m_H(d_o,d_n)=
\frac{\phi_E(H/d_n)}{\phi_E(H/d_o)}
}
$$

这是整数。这个比值只在下述局部分类和 CRT 同时达到之后成立；它不是一个对任意嵌套分区都成立的“最大值相除”规则。

### 102.2. 最大条件纤维与实际记录像

对每个旧摘要值 $s$，令

$$
E_s=\{\eta_{H,d_n}(C):\eta_{H,d_o}(C)=s\}
$$

为该旧纤维中实际出现的新摘要像。若同一 $s$ 内两个不同的新摘要共用记录值，解码器面对同一对输入却要输出两个值，矛盾。因此每个 $E_s$ 内记录值必须两两不同，得到

$$
|R|\ge \max_s|E_s|.
$$

反向构造不是只给出一个抽象字母表：对每个有限 $E_s$ 固定任意顺序，给其元素编号 $0,\ldots,|E_s|-1$；令 $\rho(C)$ 为 $\eta_{H,d_n}(C)$ 在其实际旧纤维 $E_{\eta_{H,d_o}(C)}$ 中的编号。取统一值集 $\{0,\ldots,M-1\}$，其中 $M=\max_s|E_s|$，未用编号在较小纤维中不出现。解码器查旧摘要对应的编号表即可恢复新摘要；达到最大纤维的旧类实际使用全部 $M$ 个值。因此这是记录映射的实际像基数，而不是仅声明一个更大的候选集合。构造要求编码时能取得新摘要或足以确定它的源信息；它不承诺只凭旧摘要生成记录，也不承诺时间、空间或平均码长最优。

### 102.3. 局部纤维计数与 Euler 比值

固定 $p^h\parallel H$，记 $e_o=v_p(d_o)$、$e_n=v_p(d_n)$。旧局部标签分为低型 $S_o(r,u)$（$r<e_o$，$u$ 是模 $p^{h-e_o}$ 的单位）和高型 $D_o(z)$（保存完整的 $p^{e_o}z\bmod p^h$ 余数）。

约定 $\phi_E(1)=1$；因此完全饱和的旧轴的分母和模一单位类都确实只有一个值。

若旧标签是高型，它已经固定了完整模 $p^h$ 余数，细化后只产生 1 个新类。若 $e_o<h$ 且旧标签为低型：当 $r<e_n$，单位余数从模 $p^{h-e_o}$ 提升到模 $p^{h-e_n}$，每个旧单位有恰好

$$
p^{e_o-e_n}
$$

个单位提升；当 $e_n\le r<e_o$，新标签转为高型，旧类中完整余数的数目为

$$
p^{e_o-r}\le p^{e_o-e_n}.
$$

最大值在 $r=0$ 达到；当 $e_o=0$ 没有低型且 $e_n=0$，同一公式给 1。

若 $e_o=h$，旧单位模数为 1，旧摘要只保存深度 $r<h$。当 $r<e_n$，新单位类数为 $\phi_E(p^{h-e_n})$；当 $e_n\le r<h$，新高型完整余数类数为 $\phi_E(p^{h-r})$；$r=h$ 的零余数只有 1 类。由于 $\phi_E(p^j)$ 对 $j\ge0$ 单调不减，最大值仍是 $\phi_E(p^{h-e_n})$，在深度零旧类达到，并包含 $e_n=h$ 的模一单位端点。

逐轴最大值可由同一个全局单位源同时达到。CRT 把各轴的单位标签任意组合成一个模 $H$ 的单位余数；取其正代表得到同一旧摘要类中的实际源。因此最大条件纤维的大小是局部最大值之积。逐轴有

$$
\frac{\phi_E(p^{h-e_n})}{\phi_E(p^{h-e_o})}
=p^{e_o-e_n}\quad(e_o<h),
$$

而 $e_o=h$ 时分母是 $\phi_E(1)=1$。相乘才得到

$$
\max_s|E_s|
=\prod_{p^h\parallel H}m_{p,h}(e_o,e_n)
=\frac{\phi_E(H/d_n)}{\phi_E(H/d_o)},
$$

同时证明该比值整除性和命题 102.1 的下界达到。这里的理由是已证局部分类与共同单位源，而非一般分区最大值的相除法则。

### 102.4. 只凭旧摘要可恢复的退化情形

命题 102.1 给出

$$
m_H(d_o,d_n)=1
\Longleftrightarrow
d_n=d_o,
\text{ 或 }\bigl(2\mid H,\ v_2(d_o)=v_2(H),\ d_n=d_o/2\bigr).
$$

逐轴看，第一种是所有指数不变；第二种只把饱和的 2 轴降低一级，并用 $\phi_E(2)=1$。若 $m>1$，同一旧纤维内至少有两个新类，任何只对旧摘要做确定性后处理的函数都无法恢复它们。具体地，$e_o<h$ 且严格细化时，单位源 $1$ 与 $1+p^{h-e_o}$ 旧单位标签相同而新单位标签不同；$e_o=h$ 且 $\phi_E(p^{h-e_n})>1$ 时，取新单位模数中 $1$ 与 $-1$ 两类。其余轴固定为单位类，CRT 给出真实的正整数源对。

对偶数 $H$，向**任何**旧加法库加入 $+H/2$ 都不增加行为状态：新参数是 $\gcd(d_o,H/2)$，只可能保持所有指数，或把已饱和的 2 轴降低一级。这是命题 101.2 的库级推论，仍不授权其它未声明加法。

### 102.5. 不可比较的库与 5040 成本

当 $d_o$ 与 requested 参数 $d_r$ 不可比较时，先取

$$
d_n=\gcd(d_o,d_r).
$$

第 100 节的共同来源分类说明，旧摘要与 requested 摘要的联合实际像，与 $\eta_{H,d_n}$ 具有相同纤维；所以条件记录成本按这个 gcd 细化计算。不能把不相容的两个标签独立拼接，也不能把 $d_r$ 直接代入只对整除链成立的比值。

对 $H=5040=2^4\cdot3^2\cdot5\cdot7$，具体成本如下；“记录值数”是共同解码旧摘要后的实际 $|R|$：

| 旧 $d_o$ | 新 $d_n$ | 旧状态数 | 新状态数 | 最少记录值数 |
|---:|---:|---:|---:|---:|
| 5040 | 2520 | 60 | 60 | 1 |
| 5040 | 1 | 60 | 5040 | 1152 |
| 5040 | 2 | 60 | 3780 | 576 |
| 2 | 1 | 3780 | 5040 | 2 |
| 7 | 1 | 1440 | 5040 | 6 |
| 10 | 1 | 1512 | 5040 | 8 |
| 1 | 1 | 5040 | 5040 | 1 |

因此同源的 $+7$ 与 $+10$ 库联合时，若旧摘要来自 $+7$，细化到联合库需 6 个记录值；若旧摘要来自 $+10$，需 8 个。联合状态数都是 5040，但条件纤维容量不同。$M$ 个值可用 $\lceil\log_2M\rceil$ 个固定二进制位表示，$M=1$ 用 0 位；允许任意长度字符串时，字符表大小不构成这里的下界。

### 102.6. H=8 的连续细化边界

一次细化的存在性和基数不自动给出可在线串接的记录。取 $H=8$，先从旧 $d_o=8$ 细化到 $d=2$，再从 $d=2$ 细化到 $d=1$。源 $1$ 与 $5$ 在旧 $d=8$ 摘要中都属于单位类；在 $d=2$ 摘要中也相同，因为二者模 4 的单位标签同为 1。该旧单位类在第一次细化中恰有两个 $d=2$ 类，最少记录正好为

$$
\frac{\phi_E(8/2)}{\phi_E(8/8)}=\phi_E(4)=2.
$$

因此任何达到最小值的第一次记录都必须把源 1、5 赋予同一标签。可是共同允许的正加法 $+7$ 在第二阶段把它们分开：

$$
\gcd(1+7,8)=8,\qquad \gcd(5+7,8)=4.
$$

所以旧 $d=2$ 摘要与第一次最优记录的配对，不能合成第二次 $d=1$ 所需的新区别；若不另存记录或重新取得源信息，未来缺失的信息无法凭旧标签后处理恢复。这个例子也说明最少值域的单次**存在性/基数**与 source-free record acquisition 是两回事：它没有构造只读旧摘要的编码算法。

连续细化若要求前缀兼容的在线编码，必须另行规定每一级标签如何扩展、旧标签是否可变、记录是否允许独立更新、以及编码时能访问哪些源数据。命题 102.1 没有声称存在这样的 prefix-compatible stream，也没有声称各级记录可以独立更新；固定链上 Euler 比值的数值望远镜性不能代替这些构造义务。

### 102.7. 有限核对、来源与边界

`refinement_records.py` 先在 $H=2,\ldots,24$ 直接枚举所有仿射作用 $ax+db$ 的 gcd 响应，以实际响应向量独立形成分区，再检查嵌套细化的纤维、编号解码和单位源最大值；随后在 $H=2,\ldots,128$ 枚举全部整除链，并检查 5040 的指定细化、任意旧库加入 $+2520$ 和不可比较库的 gcd 联合。它只使用标准库整数运算，输出写入调用者指定的路径；实际计数和哈希记在报告 README。该程序核对公式的有限实现和端点，不能替代全称证明，也不推出无限 Robin 裕度、RH、原创性或物理维数结论。

本批两节都是第 100 节既有分类、局部计数和最大纤维编号论证的推论与展开，数学正文是未编译的参考输入，**新增 Lean 候选为零**。不得伪造冻结前置、把纸面证明写成 kernel 证明，或把有限核对扩大为研究总目标完成。

## 追加锚（递归块 Robin 主编码批次后）

## 103. 有限整数列的 Bézout 归一化

**定理 103.1（有限列的整数最大公因子归一化）。** 令 $\iota$ 是带可判定相等的任意类型，$s\subseteq\iota$ 是有限集，$p\in\iota$ 且 $p\notin s$。给定整数 $a$ 与列 $v:\iota\to\mathbb Z$，存在 $\mathbb Z$-线性等价

$$
e:(\iota\to\mathbb Z)\simeq_{\mathbb Z}(\iota\to\mathbb Z)
$$

使得对每个满足 $x(p)=a$ 且 $x(i)=v(i)$（$i\in s$）的 $x$，有

$$
e(x)(i)=
\begin{cases}
\gcd\bigl(|a|,\gcd_{j\in s}|v(j)|\bigr),&i=p,\\
0,&i\in s,\\
x(i),&i\ne p\ \text{且}\ i\notin s.
\end{cases}
$$

这里右侧的最大公因子先在 $\mathbb N$ 中取值，再嵌入 $\mathbb Z$；有限集为空、$a$ 或某些 $v(j)$ 为零、以及所有输入同时为零的情形都包含在断言中。等价只对满足所列前提的输入作上述值承诺，外部坐标的承诺正是最后一行所写的原值保持。

证明使用有限集归纳。先处理一个枢轴坐标 $p$ 与一个新坐标 $q$。若 $\gcd(a,b)=0$，则 $a=b=0$，取恒等等价即可；这也覆盖两项同时为零的分支。否则令 $g=\gcd(a,b)$，$c=\operatorname{gcdA}(a,b)$，$d=\operatorname{gcdB}(a,b)$，并置 $u=a/g$、$w=b/g$。Bezout 恒等式 $ac+bd=g$ 给出 $cu+dw=1$，所以

$$
\begin{pmatrix}c&d\\-w&u\end{pmatrix}
$$

是行列式为 $1$ 的整数单位。它把 $(a,b)$ 变为 $(g,0)$，并在所有其它坐标上取恒等作用。空有限集时只需对负的 $a$ 乘以 $-1$，非负时取恒等；这一步把枢轴值规范化为 $|a|$，并保留零情形。

归纳步把已经归一化的枢轴和新坐标 $q$ 再交给上述二坐标单位。二坐标单位在此前清零的坐标上保持零，在未选坐标上保持输入值，因此复合等价仍满足同一个外部坐标条件。有限集归纳结束时，枢轴值是 $\gcd(|a|,\gcd_{j\in s}|v(j)|)$，所有选中坐标为零，结论成立。 $\square$

## 追加锚（递归块 Robin 主编码批次后）

## 104. 规范三位窗口、正值 End 与任务相关的联合未来商

**约定 104.1（参考推导的范围）。** 本节与 §105 把 §§99–102 的算术行为接到低位优先的规范窗口语言上，所有新增桥接均为普通、未编译的数学推导，不具有 Lean kernel 真值身份。五种三位模式、Fibonacci 三步递推，以及允许高位补零的位级未来理论分别沿用既有定义与结果；这里要明确的是正值规范 End 对共同后缀、实际可达像和最小状态数的约束。尤其不能直接把允许任意补零终止的状态数用于本节。

### 104.1. 单位初始化、窗口与终端观察

**定义 104.2（正值规范窗口合同）。** 固定 $H\ge2$、$d\mid H$，其中 $d$ 是正整数，记 $R=\mathbb Z/H\mathbb Z$。Fibonacci 数按 $F_0=0,F_1=1$ 编号。外部先选择单位位 $\varepsilon\in\{0,1\}$，其权重是 $F_2=1$；随后输入窗口字母

$$
\mathcal B=\{000,100,010,101,001\}.
$$

三位 $b=(b_0,b_1,b_2)$ 一律由低到高排列。第 $j$ 个窗口从 $j=0$ 开始，权重为 $(F_{3j+3},F_{3j+4},F_{3j+5})$，即 $(2,3,5),(8,13,21),\ldots$。接缝位 $s$ 记录刚读过的最高位；新字母合法当且仅当不出现 $s=b_0=1$，新接缝为 $b_2$。初始 $s=\varepsilon$，所以单位位为 1 时也禁止首窗低位为 1。合法 $j$ 窗前缀的整数值是

$$
N=\varepsilon+\sum_{i=0}^{j-1}
\bigl(b_{i,0}F_{3i+3}+b_{i,1}F_{3i+4}+b_{i,2}F_{3i+5}\bigr).
$$

这些字母只是无相邻 1 的三位分组；§57 的局部窗口若用高到低坐标，须先反转位序。五种模式中每一种合法读入后都还可以继续，例如共同后继 $010$ 总合法。$000$ 消耗三个位置，并不是终止符。

另设布尔量 $E$ 表示此刻能否作正值规范终止。单位初始化取 $E=\varepsilon$；每次合法输入 $b$ 后取 $E=[b\ne000]$。因此空窗口列在 $\varepsilon=0$ 时不能 End，在 $\varepsilon=1$ 时表示正整数 1 并可 End；非空窗口列恰在最高窗口非零时可 End。最后一窗内部允许在最高非零位以上补至窗界，但不许再保留整个零窗。合法开放前缀的结构标签恰在

$$
\mathcal T=\{(0,0),(0,1),(1,1)\}
$$

中；$E$ 不是“曾经见过非零位”的累积标记。末窗 $000$ 即使不改变正整数值，也必须清除 $E$。

End 是一次终端查询，不再读取权重，不计作第六种窗口转移。非法接缝进入吸收错误状态 $\bot$；在 $\bot$ 或 $E=0$ 时查询 End 均输出同一个错误符号 $\mathsf{err}$，它与所有合法数值或标签不同。一个活状态当前 End 报错，仍可在尚未查询 End 的另一条继续路径上读更高窗口；终端查询之后没有窗口输入。

先固定原始任务：$d=H$ 时，合法 End 仅返回

$$
F_H(N)=\frac{H}{\gcd(N,H)},\qquad N>0.
$$

对于一般 $d$，本节另外声明更强的保留任务：合法 End 返回 $\eta_{H,d}(N)$，或其类集合的任意单射标签。它要求保留足以支持 End **之后**全部已声明算术未来的信息，具体操作为任意正标量乘法以及有限正加法库 $\{c_1,\ldots,c_t\}$，其中 $d=\gcd(H,c_1,\ldots,c_t)$，空库取 $d=H$。每个有限算术词后读出 $F_H$，含空词。算术操作与窗口读取不交错。一般 $d$ 不能悄悄代入原始的一次 $F_H$/错误任务；某些操作库的行为分区确会退化为同一个粗分区，见 §101。这里的算术阶段仅解释 End 标签应保留什么，不计其动态状态或终端输出存储。

**定义 104.3（任意自主有限读者与未来相等）。** 一个候选读者是任意有限集 $Q$、两个指定初始状态 $q_0,q_1\in Q$、每个 $b\in\mathcal B$ 对应的总函数 $\delta_b:Q\to Q$，以及终端输出函数 $o:Q\to\mathcal Y\sqcup\{\mathsf{err}\}$。它必须在两种初始化和所有有限窗口词上满足定义 104.2；$\mathcal Y$ 取对应任务的输出集。初始映射不要求满射，也不预设 $Q$ 有余数、相位或解析标签的乘积结构。状态必须独自承担转移与输出，不另获免费时钟、已读长度或源前缀重读接口。

两个已初始化前缀有相同未来，指对每个共同窗口后缀 $w\in\mathcal B^*$，在 $w$ 后查询 End 的输出都相同；其中空后缀也须比较。非法后缀给 $\mathsf{err}$。计数范围是单位初始化以后、End 以前的可达状态，包含一个吸收错误状态，排除单位选择之前的分派器与 End 之后的存储。多余不可达状态不能降低此下界。所有非法接缝前缀具有同一恒错未来，故最小模型只保留一个 $\bot$。

### 104.2. 算术余数、局部标签与精确稳定子

**定义 104.4（开放前缀的算术坐标）。** 记活前缀坐标为 $X=(s,E,r,u,v)$，其中 $r=N\bmod H$，$(u,v)$ 是下一窗的前两个权重模 $H$。初始值和合法字母更新是

$$
X_\varepsilon=(\varepsilon,\varepsilon,\varepsilon,2,3),
$$

$$
\begin{aligned}
s'&=b_2,& E'&=[b\ne000],\\
r'&=r+(b_0+b_2)u+(b_1+b_2)v,\\
(u',v')&=(u+2v,2u+3v).
\end{aligned}
$$

所有算术等式在 $R$ 中理解。令 $S(u,v)=(v,u+v)$，则权重更新是 $S^3$，与三个位的逐步求和相符。这是既有逐位 Fibonacci 递推的三步复合；接缝路径的计数矩阵与这里的权重算子承担不同任务。每个实际权重对是相邻 Fibonacci 数的约化，因相邻整数互素而满足某个 $\alpha u+\beta v=1$；称这样的行是幺模行。

为使 End 标签的使用完整，重述 §100.3 的编码。对 $p^h\parallel H$，置 $e=v_p(d)$、$M=p^{h-e}$，令 $t$ 是 $x\bmod p^h$ 的截断 $p$ 深度，零余数取 $t=h$。不同类型的标签保持分离：

$$
\eta_{p,h,e}(x)=
\begin{cases}
S(t,\,x/p^t\bmod M),&t<e,\\
D(x/p^e\bmod M),&t\ge e,
\end{cases}
\qquad
\eta_{H,d}(x)=\bigl(\eta_{p,h,e}(x)\bigr)_{p\mid H}.
$$

低型第二坐标为单位类；$M=1$ 时该类为单点。各商先在可整除的整数代表上计算，再约化；换代表的差是所需模数的倍数。高型保存完整局部余数 $p^ez\bmod p^h$，低型保存深度和所需单位部分。因此

$$
\eta_{H,d}(x)=\eta_{H,d}(0)\quad\Longleftrightarrow\quad x=0\text{ in }R.
$$

这里使用零余数作标签并未允许整数零 End；正整数 $H$ 已给这个标签一个合法正代表。$d=H$ 时各轴仅保留截断深度，标签与 $\gcd(x,H)$、$F_H(x)$ 的输出分区相同；$d=1$ 时它保留完整余数。

§100.2–100.3 的操作对应也可在本接口内直接读出：有限模群中的正向加法库生成平移子群 $dR$，故所有算术词恰产生 $x\mapsto ax+db$。对于同一低型 $x=p^tu,y=p^tu'$，有 $p^{h-e}\mid u-u'$。乘数深度为 $s$ 时，若 $s+t<e$，加 $p^e$ 倍数不改最低层；若 $s+t\ge e$，两者乘后之差已被 $p^h$ 整除。高型则本来就是同一局部余数。反向区分时，深度不同用空词；低型单位不同先乘 $p^{e-t}$ 再平移消去第一源，高型不同直接平移消去第一源，另一源均非零模 $p^h$。全局 $d=p^e t_p$ 中 $t_p$ 在模 $p^{h-e}$ 可逆，故所需局部平移能由全局 $db$ 实现。一根轴的深度差已能区分全局 gcd，不必冻结其余轴。由此，标签相等恰为所声明算术未来相等；这是既有分类的接口复用。

**命题 104.5（End 标签的全局单位稳定子）。** 在 $R$ 的单位群中，处处保持 End 标签的元素恰为

$$
G_{H,d}=\{a\in R^\times:\ a\equiv1\pmod{H/d}\}
=\{a\in R^\times:\ \forall x\in R,\ \eta_{H,d}(ax)=\eta_{H,d}(x)\}.
$$

证明。单位乘法保持各轴截断深度，只把低型单位坐标或高型商坐标乘以 $a$。若 $a\equiv1\pmod{p^{h-e}}$，两个类型的标签都保持。反之，在 $e<h$ 的轴取局部余数 $x=p^e$，高型标签 $D(1)$ 的保持迫使 $a\equiv1\pmod{p^{h-e}}$；它有全局整数代表，故全局“对每个 $x$”确实包含这个测试。$e=h$ 时模数为 1，无附加限制。各轴条件通过 CRT 合起来恰为 $a\equiv1\pmod{H/d}$。这也是一个子群。$\square$

### 104.3. 在规范终止语言内实现所有系数

**引理 104.6（三网格探针与非零末窗）。** 存在共同的 Fibonacci 返回长度 $T\ge3$、$3\mid T$，使每个 $A,B\in R$ 都有一个从任意接缝合法的整窗后缀 $W_{A,B}$。它最后一窗是 $010$，从任意初始权重行 $(u,v)$ 出发贡献恰为 $Au+Bv$，故在实际正权重上必能作正值规范 End。

证明。$S$ 在有限集 $R^2$ 上可逆，逆映射是 $(u,v)\mapsto(v-u,u)$，所以有有限正阶。取其阶与 3 的公倍数 $T\ge3$，则 $S^T=I$，等价于 $F_T=0,F_{T+1}=1$ 模 $H$。按低到高的位序定义

$$
P_0=0^T1\,0^{T-1},\qquad
P_1=0^{T+1}1\,0^{T-2}.
$$

两词长度都是 $2T$，均以零开头、以零结束、内部只有一个 1；因此从任意接缝合法，任意次串接仍合法。第一个 1 在偏移 $T$，因 $S^T=I$ 而贡献 $u$；第二个在偏移 $T+1$，贡献 $v$。每个词走完 $2T$ 位，恢复全部模 $H$ 权重行。又因 $3\mid T$，词界都在三位窗界上，切成三元组时每组必在 $\mathcal B$ 中，组间接缝也合法。

令 $[C]_H\in\{0,\ldots,H-1\}$ 是余数 $C$ 的非负代表，取

$$
W_{A,B}=P_0^{[A]_H}P_1^{[B-1]_H}\,010.
$$

脉冲部分贡献 $Au+(B-1)v$ 并恢复权重，最后 $010$ 再贡献 $v$。即使两个指数都是零，$010$ 也从任意接缝合法。最后一窗非零且末位为零，所以终点标签为 $(0,1)$；在实际 Fibonacci 权重上它选择了一个严格正权重，整数总值为正。最终贡献是 $Au+Bv$，而最终权重为 $S^3(u,v)$。**恢复时钟的是加帽之前的脉冲部分；完整后缀并不承诺恢复时钟。** End 探针只需要贡献与终止合法性，不需要帽后时钟恢复。$\square$

这里的脉冲取自 [Katz 接口笔记 §12 的 ZP1–ZP2](../../../Library/notes/katz2015goldeninterfaces.md#12-exact-zeckendorf-predictive-states-at-the-original-prime-square-scale) 与 `ZeckendorfFutureKernel` 的既有构造；三网格对齐、$B-1$ 系数和末窗帽明确履行本节规范 End 的额外条件。它不是任意抽象系数查询：同一个字面后缀同时作用于待比较的两个前缀。

### 104.4. 共同缩放的充分性与必要性

**定理 104.7（规范窗口的精确联合未来）。** 对两个实际合法开放前缀，写坐标为 $X=(s,E,r,u,v)$、$\widetilde X=(\widetilde s,\widetilde E,\widetilde r,\widetilde u,\widetilde v)$。定义 104.2 的终端标签任务下有

$$
X\sim\widetilde X
\quad\Longleftrightarrow\quad
(s,E)=(\widetilde s,\widetilde E)
\ \text{且}\quad
\exists a\in G_{H,d},\quad
(\widetilde r,\widetilde u,\widetilde v)=a(r,u,v).
$$

$d=H$ 时同一结论准确适用于仅返回 $F_H$/错误的原始任务，此时 $G_{H,H}=R^\times$。一个活状态与吸收错误状态的未来永不相等。

证明。若两个 $E$ 不同，立即 End 就在合法输出与 $\mathsf{err}$ 间区分。若 $E$ 相同而接缝不同，$\mathcal T$ 中只能是 $(0,1)$ 与 $(1,1)$：共同读入低位为 1 的 $100$，前者合法且可立即 End，后者进入错误状态。这个 End 的实际总值严格为正；若还要接共同的安全非零后继，$010$ 仍保持前者合法、后者吸收错误。任意活状态也可用 $010$ 后 End 与 $\bot$ 区分。因此结构标签和错误状态确须分离，不能只数接缝。

固定相同结构标签。由引理 104.6 和未来相等，对所有 $A,B\in R$ 有

$$
\eta_{H,d}(r+Au+Bv)
=\eta_{H,d}(\widetilde r+A\widetilde u+B\widetilde v).
$$

在 $d=H$ 的原始任务中，$F_H$ 的相同输出恰等于这条标签等式。记满射 $R$-线性映射

$$
\lambda(A,B)=Au+Bv,\qquad
\widetilde\lambda(A,B)=A\widetilde u+B\widetilde v.
$$

两者满射来自各自幺模行的 Bézout 关系；不把复合模环当作域。标签的零纤维是单点，故仿射零集合相同。取 $z_0\in R^2$ 使 $\lambda(z_0)=-r$，则也有 $\widetilde\lambda(z_0)=-\widetilde r$，并且

$$
z_0+\ker\lambda=z_0+\ker\widetilde\lambda,
\qquad \ker\lambda=\ker\widetilde\lambda.
$$

于是 $\alpha:R\to R$，$\alpha(\lambda(z))=\widetilde\lambda(z)$，是良定义的 $R$-线性双射。良定义用核相等，满射用 $\widetilde\lambda$ 满射，单射再用核相等。令 $a=\alpha(1)$，则 $\alpha(x)=ax$；其逆也为线性映射，故 $a$ 是单位。代入两个标准坐标向量得到 $\widetilde u=au,\widetilde v=av$，代入 $z_0$ 得 $\widetilde r=ar$。由于 $r+\lambda(z)$ 遍历整个 $R$，完整标签等式进一步给出

$$
\forall x\in R,\qquad \eta_{H,d}(ax)=\eta_{H,d}(x),
$$

命题 104.5 遂迫使 $a\in G_{H,d}$。这个必要性不是仅证明余数零测试相同：零纤维先确定共同单位，完整 $\eta$ 再限制该单位。

反向若同一 $a\in G_{H,d}$ 同时缩放三个算术坐标，同结构标签给出相同接缝合法域和 End 合法性。合法窗口更新是 $R$-线性的，故每个共同后缀后仍保持同一个 $a$ 的关系；非法输入则同时进入 $\bot$。End 合法时稳定子性质给相同标签，否则两边均报错。由词长归纳得到全部未来相等。充分性与必要性合起来也说明：凡不满足所列条件的两个前缀，必有某个有限共同后缀再接 End 将它们区分。$\square$

## 105. 实际联合可达性、标量返回与精确自主记忆

### 105.1. 从最高位置得到三段实际整数像

**引理 105.1（合并两种单位初始化后的区间）。** 对每个 $j\ge1$，允许 $\varepsilon=0,1$ 两种初始化，合法 $j$ 窗前缀按结构标签的整数值集合恰为

$$
\begin{aligned}
I_j(0,0)&=[0,F_{3j}-1]\cap\mathbb Z,\\
I_j(0,1)&=[F_{3j},F_{3j+2}-1]\cap\mathbb Z,\\
I_j(1,1)&=[F_{3j+2},F_{3j+3}-1]\cap\mathbb Z.
\end{aligned}
$$

这些是实际前缀的像，不是独立假定的结构、余数和相位直积。此断言不适用于固定一个 $\varepsilon$。

证明。沿用 Zeckendorf 的有限区间性质：使用位置 $F_2,\ldots,F_m$、不许相邻 1 的有限位列，其值恰为 $[0,F_{m+1}-1]$。该性质由最高位分为零与一得到：最高位为零时是 $[0,F_m-1]$；最高位为一时邻位为零，较低部分是 $[0,F_{m-1}-1]$，平移 $F_m$ 后是 $[F_m,F_{m+1}-1]$。两段相邻，且基础空列值为 0；这也是既有 Zeckendorf 区间结果的直接归纳说明，不另提出唯一性结论。

在 $j$ 窗末端，最高三个位是 $F_{3j},F_{3j+1},F_{3j+2}$。标签 $(0,0)$ 表示三个位全零，只余至 $F_{3j-1}$ 的低段，所以第一段成立。标签 $(1,1)$ 表示最高位 $F_{3j+2}$ 为 1，其相邻位必须为零，以下可使用至 $F_{3j}$，得到

$$
F_{3j+2}+[0,F_{3j+1}-1]
=[F_{3j+2},F_{3j+3}-1].
$$

标签 $(0,1)$ 的最高位为零，而另外两位至少一个非零。这是使用至 $F_{3j+1}$ 的完整区间 $[0,F_{3j+2}-1]$ 去掉最高两位都零的区间 $[0,F_{3j}-1]$，得到第二段。每个低段都包括自由选择的单位位，并仍遵守邻接条件，故区间内每个整数都有相应合法前缀。特别地，$j=1$ 的三段为 $\{0,1\}$、$\{2,3,4\}$、$\{5,6,7\}$；若固定 $\varepsilon=0$，中段只有 $\{2,3\}$，数字 4 的缺失已经反驳固定初始化的区间等式。$\square$

三段长度分别为 $F_{3j},F_{3j+1},F_{3j+1}$。因此只要能在某个实际权重相位选取任意大的 $j$，三段长度最终都超过 $H$，每段便含每个模 $H$ 余数。这里必须先保持相位再令深度增大；一个预先指定的小深度没有这种结论。

### 105.2. 标量返回位置构成循环相位的子群

**命题 105.2（允许的相位平移）。** 定义 Fibonacci 秩与对周期

$$
\rho(H)=\min\{n\ge1:H\mid F_n\},\qquad
\pi(H)=\min\{n\ge1:(F_n,F_{n+1})\equiv(0,1)\pmod H\}.
$$

令

$$
P=\frac{\pi(H)}{\gcd(\pi(H),3)},\qquad
L_{H,d}=\min\{\ell\ge1:H\mid F_{3\ell},\quad
F_{3\ell-1}\equiv1\pmod{H/d}\}.
$$

$L_{H,d}$ 存在且整除 $P$。读完 $j$ 窗的实际下一权重行为

$$
w_j=(F_{3j+3},F_{3j+4})\pmod H.
$$

这些行恰有 $P$ 个，且 $w_k=a w_j$ 对某个 $a\in G_{H,d}$ 成立，当且仅当 $k-j$ 是 $L_{H,d}$ 的倍数。若记 $L=L_{H,d}$、$c=F_{3L-1}\bmod H$，则 $c\in G_{H,d}$；当 $k=j+nL$ 时，唯一的共同标量为 $c^n$，负 $n$ 用单位逆。因此整个前缀未来相同还必须有相同结构标签以及 $r_k=c^n r_j$。

证明。列向量形式的 $S$ 矩阵为

$$
S=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
S^m=\begin{pmatrix}F_{m-1}&F_m\\F_m&F_{m+1}\end{pmatrix}\quad(m\ge1).
$$

该式由 Fibonacci 递推归纳得到。$S$ 在 $R$ 上可逆，故对周期存在，且其阶就是 $\pi(H)$。从初始行 $(2,3)$ 开始，$w_j=S^{3j}(2,3)$。对 $\ell>0$，Fibonacci 加法式与 Cassini 恒等式给出

$$
\det(w_j,w_{j+\ell})=(-1)^{3j+4}F_{3\ell}\pmod H.
$$

若后行是前行的标量倍，该行列式为零，于是 $H\mid F_{3\ell}$。反向有此整除时，矩阵式直接变成

$$
S^{3\ell}=F_{3\ell-1}I\pmod H.
$$

其标量是单位，因为矩阵仍可逆（也可由相邻 Fibonacci 数互素看出）。单位作用在每个幺模行上自由：若 $aw=w$ 且 $\alpha u+\beta v=1$，则 $a-1=\alpha(a-1)u+\beta(a-1)v=0$。故允许单位 $a$ 唯一，并由命题 104.5 恰受 $F_{3\ell-1}\equiv1\pmod{H/d}$ 限制。特别地，$w_{j+\ell}=w_j$ 等价于 $S^{3\ell}=I$，所以三步相位的实际周期确为 $P$，没有把所有位相位都算入。

在有限循环群 $\mathbb Z/P\mathbb Z$ 中取

$$
K=\{\overline\ell:S^{3\ell}=aI\text{ for some }a\in G_{H,d}\}.
$$

恒等、乘积和逆都保持此性质，故 $K$ 是子群；对应标量的唯一性还给一个同态 $K\to G_{H,d}$。它在 $\mathbb Z$ 中的原像是包含 $P\mathbb Z$ 的非零子群，故恰为 $L\mathbb Z$，其中 $L$ 为上述最小正返回位置。相位商有 $L$ 个元素，标量沿 $n$ 次平移为 $c^n$。注意这不是说任意 $a\in G_{H,d}$ 都把实际相位集合映到自身；只有实际的标量返回子群 $K$ 参与相位计数。$\square$

**推论 105.3（两个端点的精确相位）。** 有

$$
L_{H,H}=\frac{\rho(H)}{\gcd(\rho(H),3)},\qquad
L_{H,1}=\frac{\pi(H)}{\gcd(\pi(H),3)}.
$$

证明。由同一个矩阵式，$S^n$ 是标量矩阵恰在 $H\mid F_n$ 时成立。所有标量矩阵在 $\langle S\rangle$ 中构成子群，所以零指标在整数中的集合恰为 $\rho(H)\mathbb Z$；这也给出秩的存在与整除周期。$d=H$ 时无额外单位限制，条件是 $\rho(H)\mid3\ell$。$d=1$ 时标量必须是 1，条件变为 $\pi(H)\mid3\ell$。分别求最小正 $\ell$ 即得两式。$\square$

### 105.3. 可达上界与任意读者的同一下界

**定理 105.4（精确最小窗口状态数）。** 在定义 104.2–104.3 的自主读者合同下，End 以前的最小可达状态数为

$$
\boxed{3H L_{H,d}+1}.
$$

其中 $3H L_{H,d}$ 是合法开放前缀的未来类数，额外的 1 是吸收错误状态。该结论对任意有限确定性状态实现成立，不要求其内部状态预先分解成结构标签、余数与时钟。

证明。先核实实际共同可达性。对任一原始相位 $j_0\bmod P$，取 $j=j_0+nP\ge1$ 并使 $n$ 足够大。引理 105.1 的三段长度都超过 $H$，而权重仍为 $w_{j_0}$。每段连续整数包含所有余数，所以在同一实际相位和每个结构标签上，全部 $H$ 个余数均由某个真实前缀达到。允许使用两种初始化正是这里的量词。由此才得到完整的实际像 $\mathcal T\times R\times\{w_0,\ldots,w_{P-1}\}$，而非在证明前假定它。

接着按定理 104.7 取商。相位分成 $L=L_{H,d}$ 个类，每类选 $w_t$，$0\le t<L$。若 $j=t+nL$，把实际状态的余数连同行同时乘 $c^{-n}$，即可用

$$
(s,E,\ c^{-n}r,\ w_t)
$$

表示其未来类。取不同的 $j$ 周期代表不会改变它，因为 $c^{P/L}=1$，由 $S^{3P}=I$ 可知。每个选定 $w_t$ 都为幺模行，固定它的单位只能为 1，因此该相位代表下的 $H$ 个余数两两不合并。结构标签之间也不合并，故合法类数恰为 $3HL$。这同时显示为何不能只丢掉相位而原样保留余数：跨标量返回时二者必须共同缩放。

这些类构成上界实现：在类上按窗口更新任取代表再取类，定理 104.7 的线性充分性保证良定义；接缝非法送入 $\bot$，$\bot$ 上五种字母都自环。End 按 $E$ 与 $\eta$ 输出，$d=H$ 时换用同分区的 $F_H$。两个初始类由 $X_0,X_1$ 指定。错误状态也实际可达，例如 $\varepsilon=1$ 后读 $100$。

下界直接对任意候选 $Q$ 证明。为每个上述实际未来类选择一个已初始化的真实前缀。如果两个不同类被 $Q$ 送到同一状态，确定性将迫使它们在所有共同后缀后给出相同 End 输出；这与定理 104.7 提供的区分后缀矛盾。选出的每个类因此必须占据不同状态，不涉及初始映射满射或内部坐标假设。错误前缀还须另占一态，因为每个活前缀都有非零规范后缀 $010$ 后 End 与它区分。得到 $|Q_{\mathrm{reachable}}|\ge3HL+1$，与上界吻合。$\square$

本定理只计窗口读取阶段。End 后若另设带操作输入的算术状态机，须单独声明其状态类型与计数范围；§100 的 $\kappa_H(d)$ 不是应乘到 $3HL$ 上的自由因子。免费提供当前窗号、缩短允许后缀、只比较合法且可整除的布尔接受、或保存终端输出状态，都改变了定义 104.3，不能沿用这个计数口径。

### 105.4. 模 5040 的有限递推与 CRT 特化

**命题 105.5（5040 的两个窗口容量）。** 对 $H=5040=16\cdot9\cdot5\cdot7$ 及任意 $d\mid5040$，有

$$
L_{5040,d}=\begin{cases}40,&7\mid d,\\80,&7\nmid d,\end{cases}
\qquad
3\cdot5040\cdot L_{5040,d}+1
=\begin{cases}604801,&7\mid d,\\1209601,&7\nmid d.\end{cases}
$$

证明。以下局部表由 $(F_0,F_1)=(0,1)$ 起，重复 $(a,b)\mapsto(b,a+b)$ 并逐步约化即可检查。表中列出一个完整周期内全部正零指标及其后一项；第一次回到 $(0,1)$ 才结束周期，故同时排除了更早的秩或完整返回。

| 局部模数 $m$ | $\rho(m)$ | $\pi(m)$ | $1\le n\le\pi(m)$ 中全部 $(n,F_{n+1}\bmod m)$，其中 $F_n=0$ |
|---:|---:|---:|---|
| $16$ | $12$ | $24$ | $(12,9),(24,1)$ |
| $9$ | $12$ | $24$ | $(12,8),(24,1)$ |
| $5$ | $5$ | $20$ | $(5,3),(10,4),(15,2),(20,1)$ |
| $7$ | $8$ | $16$ | $(8,6),(16,1)$ |

零指标是秩的倍数，完整返回指标是周期的倍数，CRT 要求四轴同时满足，因而

$$
\rho(5040)=\operatorname{lcm}(12,12,5,8)=120,
\qquad
\pi(5040)=\operatorname{lcm}(24,24,20,16)=240.
$$

在指标 120，模 16、9、5 分别走了完整周期的 $5,5,6$ 倍，返回标量为 1；模 7 是 15 个秩返回，标量 $6^{15}\equiv-1$。又因 $F_{120}=0$，前后一项模 5040 相等。CRT 得

$$
F_{119}\equiv F_{121}\equiv1441\pmod{5040},\qquad
1441\equiv(1,1,1,-1)\pmod{(16,9,5,7)},\qquad
1441^2\equiv1\pmod{5040}.
$$

首次可能的三窗标量返回在 $3\ell=120$，即 $\ell=40$。此时属于 $G_{5040,d}$ 恰要求

$$
5040/d\mid1441-1=1440=2^5\cdot3^2\cdot5.
$$

因为 $d\mid5040$，2、3、5 三轴总已满足，唯一额外条件是 $7\mid d$。若失败，下一次 $\ell=80$ 的标量是 $1441^2=1$，必满足；其间没有其它标量返回。最后代入定理 105.4，合法类分别为 $604800$ 与 $1209600$，再加共同错误态即得所列总数。这个数值特化只需至多 24 步的各局部模递推和 CRT，不依赖对 5040 模读者作巨量状态枚举。$\square$

因此原始 $F_{5040}$/错误任务取 $d=5040$，窗口数为 $604801$ 态；要求保留 $+7$ 的算术未来仍在 $7\mid d$ 一侧。要求保留 $+10$ 或 gcd 为 1 的加法库则在另一侧。这里比较的是任务所需的读取记忆；End 后纯乘法的 60 个 gcd 类既不是原窗口类数，也不自动增加到本节的计数中。

### 105.5. 两个不可删除的字段与宏展开的边界

**命题 105.6（末窗标记不能由余数和权重恢复）。** 取 $H=2,\varepsilon=0$，两个前缀 $[010]$ 与 $[010,000]$ 的当前整数值都为 3，余数都为 1，接缝都为 0，下一权重行分别为 $(8,13)$ 与 $(34,55)$，约化后都为 $(0,1)$。但原始终端任务的输出不同。

证明。第一前缀的末窗非零，所以 $E=1$，End 返回 $F_2(3)=2$；第二个末窗为 $000$，所以 $E=0$，End 返回 $\mathsf{err}$。二者差别确在 $E$，不能从相同的其它坐标中恢复。初始零值也正因此必须取 $E=0$；把所有单位初始化统一设成 $E=1$ 会错误接受整数零。$\square$

**命题 105.7（相同余数不允许单独删除相位）。** 取 $H=5,d=5,\varepsilon=0$，前缀 $[010]$ 与 $[000,100]$ 分别表示 3 与 8，均有 $(s,E,r)=(0,1,3)$。它们在共同后缀 $[000,001]$ 后查询 End，分别输出 5 与 1。

证明。两前缀下一权重行为 $(8,13)\equiv(3,3)$ 和 $(34,55)\equiv(4,0)$ 模 5。共同后缀先跳过一窗，再选择下一窗最高位：第一前缀加 $F_{11}=89$，得到 $92$；第二前缀加 $F_{14}=377$，得到 $385$。两条路径都无相邻 1，最高窗 $001$ 非零，故均允许 End；但

$$
F_5(92)=5,\qquad F_5(385)=1.
$$

因此只存 $(s,E,r)$，甚至再附当前 $\eta_{5,5}(r)$，仍不能完成全部窗口未来。定理 104.7 允许的只是同一个单位对余数与权重行的共同作用。$\square$

**命题 105.8（内部数值展开不改外部规范位置）。** 外部数值 8 的规范窗口表示为 $\varepsilon=0;[000,100]$。在独立的内部表达式中写 $8=5+3$，不改变这个外部选择；若把内部两项直接暴露成同级外部选位，所得并非合法规范窗口。

证明。外部选择的是 $F_6=8$。若改选 $F_5=5,F_4=3$，第一窗会成为低到高的 $011$，它不属于 $\mathcal B$，因为占据相邻位置。内部封闭表达式与外部位置选择是不同类型的对象。对作为窗口词作用的封闭宏，安全替换须在每个实际输入状态上有相同合法域和相同最终未来类；若开放内部切点、End 或中间读出，则这些新增上下文也必须相同。仅有末端整数相等未履行这些条件。$\square$

**约定 105.9（来源与形式边界）。** §§99–102 提供本节沿用的 $F_H$、操作库、$\eta_{H,d}$、共同来源与宏端口合同。[Katz 接口笔记 §12](../../../Library/notes/katz2015goldeninterfaces.md#12-exact-zeckendorf-predictive-states-at-the-original-prime-square-scale) 的 ZP1–ZP3 针对允许高位补零的逐位语言，给出系数脉冲、单位缩放未来和该语言的状态计数；不能把这些计数直接当作正值规范三位 End 的结论。[ZeckendorfFutureKernel.lean](../../../D5/S3/Arith/ZeckendorfFutureKernel.lean) 的 `result` 在显式 Fibonacci 返回与两行 Bézout 前提下，陈述合法位词的所有系数探针及同接缝的终端可整除未来等价；证明内部的 `pulseFacts`、`repeats` 给出脉冲长度和恢复性质，导出陈述本身未携带规范三窗末端条件。[PrimePowerAffineBehavior.lean](../../../D5/S3/Arith/Congruence/PrimePowerAffineBehavior.lean) 的 `local_classification` 是素幂局部 $S/D$ 标签、代表无关性、正提升及有限算术词的现有形式化来源，其范围不包含这里的全局 CRT 窗口读者。

本附录的规范帽、正值初始化、联合可达区间、实际标量返回及全体自主读者最小性，均以上述明确合同作普通参考推导；准确连接这些子句的 canonical Lean bridge 尚未编译。引用既有声明不把整个接口提升为 kernel 证明，也不表示取得新增形式化声明准入或原创性结论。固定 $H$ 的终端任务只保留所声明的 gcd/算术未来；它不是任意素数判定器，也不是 Robin 裕度判定器。它不恢复无限整数的规模、$Z(N)$ 或全部因子信息，亦未处理读取与算术交错的新合同。无限自匹配族上所需的 Robin 严格正性仍为开放问题，本附录没有给出该无界定量结论。

## 追加锚（递归块 Robin 主编码批次后）

## 106. 短共同系数探针与模 5040 的精确饱和深度

### 106.1. 对所有权重行同时成立的系数合同

**定义 106.1（两接缝规范词与系数深度）。** 固定整数 $H\ge2$，令 $R=\mathbb Z/H\mathbb Z$，并取

$$
F_0=0,\quad F_1=1,\quad F_{k+2}=F_{k+1}+F_k,
\qquad \phi=\frac{1+\sqrt5}{2},\quad \alpha=\phi^{-1}.
$$

位词均按低位到高位排列。对整数 $L\ge1$，令 $\mathcal W_L$ 为所有长度 $3\ell$、$1\le\ell\le L$ 的位词 $w=(b_0,\ldots,b_{3\ell-1})$，要求无相邻 1、$b_0=0$，且最后三位不全为零。因而这些词非空并至少含一个 1。条件 $b_0=0$ 恰使一个内部合法的非空词在两种输入接缝之后都合法。令 $\mathcal W^{00}_L$ 为其中另满足 $b_1=0$ 的词；第二个零是更强的限制。

对任意有限位词，包括空词，把缺失的位视为零，定义模 $H$ 系数

$$
A_w=b_0+\sum_{k\ge2}b_kF_{k-1},\qquad
B_w=b_1+\sum_{k\ge2}b_kF_k,\qquad C_H(w)=(A_w,B_w)\in R^2.
$$

从任意行 $(u,v)\in R^2$ 出发，令 $a_0=u,a_1=v,a_{k+2}=a_{k+1}+a_k$，定义词值 $\operatorname{value}(u,v,w)=\sum_k b_ka_k$。系数饱和深度为

$$
\begin{aligned}
D(H)&=\min\{L\ge1:C_H(\mathcal W_L)=R^2\},\\
D_{00}(H)&=\min\{L\ge1:C_H(\mathcal W^{00}_L)=R^2\},
\end{aligned}
$$

其中空的最小值集合暂记为 $+\infty$。这里要求覆盖整个系数对空间 $R^2$。

**引理 106.2（字面词的普遍系数）。** 每个有限位词 $w$ 满足

$$
\forall (u,v)\in R^2,\qquad
\operatorname{value}(u,v,w)=A_wu+B_wv.
$$

在对所有行成立的恒等式中，系数对唯一。特别地，同一个字面词在任何两个待比较的权重行上使用同一对系数。

证明。递推在 $k=2$ 给出 $a_2=u+v=F_1u+F_2v$，在 $k=3$ 给出 $a_3=u+2v=F_2u+F_3v$。相加归纳得到 $a_k=F_{k-1}u+F_kv$，$k\ge2$。把 $k=0,1$ 的两项分别保留，再对各位求和，便得到所列公式。若另一对系数也对每行成立，代入 $(1,0)$ 和 $(0,1)$ 分别确定其第一、第二坐标。因此固定一行的值覆盖与本定义的系数对覆盖是不同条件。$\square$

### 106.2. 移位圆网格与对数长度构造

**定理 106.3（短共同规范探针）。** 令 $j$ 是满足 $F_j>2H$ 的最小指标，置 $q=F_j$；令 $m$ 是满足 $F_m\ge H(q+1)$ 的最小指标，并置

$$
L(H)=\left\lceil\frac m3\right\rceil.
$$

则 $j\ge5$、$2H<q<4H$，且

$$
D(H)\le D_{00}(H)\le L(H)=O(\log H).
$$

具体而言，对每个 $(A,B)\in R^2$，存在一个 $w\in\mathcal W^{00}_{L(H)}$，使引理 106.2 的恒等式在所有行上等于 $Au+Bv$。该词接在任意实际合法前缀后，都能作正值规范 End。

证明。先给出所用的严格逼近估计。由 $\phi>3/2$、$\phi^2=\phi+1$、$\phi^3=2\phi+1$，有

$$
F_2=1<\frac{\phi^2}{2},\qquad
F_3=2<\frac{\phi^3}{2}.
$$

若相邻两项满足此不等式，则

$$
F_{k+2}=F_{k+1}+F_k
<\frac{\phi^{k+1}+\phi^k}{2}
=\frac{\phi^{k+2}}2.
$$

故 $F_k<\phi^k/2$ 对每个 $k\ge2$ 成立；$k=1$ 不在此范围，事实上 $F_1=1>\phi/2$。令 $p=F_{j-1}$。Euclid 递推给出 $\gcd(p,q)=1$。再令 $e_k=F_k\alpha-F_{k-1}$，则 $e_1=\alpha$，由 $\alpha^2+\alpha=1$ 得 $e_{k+1}=-\alpha e_k$，所以

$$
|q\alpha-p|=\alpha^j,\qquad
\left|\alpha-\frac pq\right|=\frac{\alpha^j}{q}<\frac1{2q^2}.
$$

这里最后一步正用 $q\alpha^j<1/2$。因 $F_4=3\le2H$，最小指标 $j\ge5$。又 $F_{j-1}\le2H$ 且 $F_{j-2}<F_{j-1}$，故 $2H<q<2F_{j-1}\le4H$。

接着证明一个移位网格估计。给定任意整数 $p$、整数 $q\ge1$、$\gcd(p,q)=1$，以及实数 $\beta$ 满足 $|\beta-p/q|<1/(2q^2)$。在圆 $\mathbb R/\mathbb Z$ 上使用距离

$$
d_{\mathbb T}(x,y)=\min_{z\in\mathbb Z}|x-y-z|.
$$

对任意实数移位 $\theta$，点 $\theta+tp/q$，$1\le t\le q$，组成一个间距 $1/q$ 的完整移位网格：乘以 $p$ 置换模 $q$ 的剩余类，而 $t=q$ 包含零类。每个圆上目标 $x$ 都在某个网格点的距离 $1/(2q)$ 以内。对该点对应的同一个 $t$，有

$$
\begin{aligned}
d_{\mathbb T}(\theta+t\beta,\theta+tp/q)
&\le t|\beta-p/q|<\frac{t}{2q^2}\le\frac1{2q},\\
d_{\mathbb T}(x,\theta+t\beta)&<\frac1q.
\end{aligned}
$$

此估计也包括 $t=q$。当 $q>2H$ 时，对 $a\in\{0,\ldots,H-1\}$ 取胞的中点 $x=(a+1/2)/H$，所得距离严格小于 $1/(2H)$，从而

$$
\{\theta+t\beta\}\in\left(\frac aH,\frac{a+1}{H}\right).
$$

圆上以该中点为中心、半径 $1/(2H)$ 的开球，在 $[0,1)$ 中恰落在所示开区间；即使 $a=0$ 或 $a=H-1$ 也不越过端点。因此没有整胞端点的取整歧义。

现在取 $A,B$ 的代表 $a,b\in\{0,\ldots,H-1\}$，令 $\beta=\alpha$、$\theta=(b+1)\alpha/H$。上面的估计给出某个 $1\le t\le q$，使

$$
\left\{\frac{(b+Ht+1)\alpha}{H}\right\}
\in\left(\frac aH,\frac{a+1}{H}\right).
$$

置 $n=b+Ht$，则 $n\equiv B\pmod H$，并由恒等式 $\lfloor Hz\rfloor=H\lfloor z\rfloor+\lfloor H\{z\}\rfloor$ 得

$$
\lfloor(n+1)\alpha\rfloor\equiv A\pmod H,
\qquad H\le n\le Hq+H-1<H(q+1).
$$

特别地，目标 $(A,B)=(0,0)$ 也由正整数 $n$ 实现。

令 $Z(n)$ 为 $n$ 的规范 Zeckendorf 指标集，所有指标均至少为 2，互不相邻，且 $n=\sum_{k\in Z(n)}F_k$。对这里的 $n>0$，直接使用[既有移位 Zeckendorf 恒等式](../../../D5/S3/Analytic/GoldenEulerBetaZeckendorf.lean)（`shiftedFibSum` 与 `floor_succ_div_golden_eq_shifted`）：

$$
\sum_{k\in Z(n)}F_{k-1}=\lfloor(n+1)\alpha\rfloor.
$$

在位位置 $k\in Z(n)$ 恰放置 1，其余位置放置 0。位置 0、1 都是零。由引理 106.2，该词在任意行上的值为

$$
\left(\sum_{k\in Z(n)}F_{k-1}\right)u
+\left(\sum_{k\in Z(n)}F_k\right)v
=Au+Bv\quad\text{于 }R.
$$

选择 $n$ 和此位词只用了 $H,A,B$，所以这个恒等式由一个共同字面词同时实现。

因 $n>0$，$Z(n)$ 非空。设其最大指标为 $K$，则

$$
F_K\le n<H(q+1)\le F_m.
$$

Fibonacci 数在指标至少为 2 时严格递增，故 $K<m$，未补零的长度 $K+1\le m$。把长度补至 $3\lceil(K+1)/3\rceil$，只需在高端补零、一个零或两个零，位置 $K$ 的 1 仍在最后一窗中。因此所得词属于 $\mathcal W^{00}_{L(H)}$。其首位为零，接在两种接缝后都合法；非空支集在实际 Fibonacci 权重上至少选择一个严格正项，所以最终整数为正，且非零末窗保证规范 End。由 $\mathcal W^{00}_L\subseteq\mathcal W_L$ 得两种深度的次序与上界。

最后，$F_k\ge\phi^{k-2}$ 对 $k\ge2$ 由 $F_2=1$、$F_3=2>\phi$ 和相同递推归纳成立。因此若

$$
M=\left\lceil 2+\log_\phi(4H^2+H)\right\rceil,
$$

则 $F_M\ge4H^2+H>H(q+1)$，从而 $m\le M$、$L(H)\le\lceil M/3\rceil=O(\log H)$。$\square$

### 106.3. 规范词的精确计数与 13 窗最优性

**命题 106.4（两接缝语言的计数障碍）。** 对每个 $L\ge1$，有

$$
|\mathcal W_L|=F_{3L+1}-1,\qquad
|\mathcal W^{00}_L|=F_{3L}-1.
$$

因此 $D(H)\le L$ 必须满足 $F_{3L+1}-1\ge H^2$，而 $D_{00}(H)\le L$ 必须满足 $F_{3L}-1\ge H^2$。

证明。把 $w\in\mathcal W_L$ 在高端补零到长度 $3L$，得到一个非零、无相邻 1、首位为零的定长串。反向对任意这样的串，令 $K$ 为最高的 1 的位置，删除所有完整的高端零窗，保留长度 $3\lceil(K+1)/3\rceil$。所得词末窗非零，属于 $\mathcal W_L$。原词的规范末窗条件使这两个映射互逆。首两位为零的限制也在两边对应，故同样给出 $\mathcal W^{00}_L$ 的双射。这里补零是计数映射；如果它添加完整的零窗，补零后的串本身不再允许规范 End。

设 $a_r$ 为长度 $r$ 的无相邻 1 位串数。$a_0=1=F_2$、$a_1=2=F_3$；按末位为零，或末两位为 $01$ 分组，$r\ge2$ 时有 $a_r=a_{r-1}+a_{r-2}$，所以 $a_r=F_{r+2}$。固定首位为零，剩下 $3L-1$ 位任意合法，去掉全零串便得 $F_{3L+1}-1$。固定首两位为零，同理得 $F_{3L}-1$。

每个词只给出一个系数对。覆盖 $R^2$ 的 $H^2$ 个元素至少需要 $H^2$ 个词，故有必要不等式。不同词可以给出相同系数对，此计数条件一般只作为必要条件。$\square$

**定理 106.5（模 5040 的共同系数深度）。** 对定义 106.1 的两种语言，

$$
\boxed{D(5040)=D_{00}(5040)=13}.
$$

证明。由整数 Fibonacci 递推，

$$
F_{20}=6765\le10080<F_{21}=10946,
$$

所以定理 106.3 中 $q=10946$。进而

$$
H(q+1)=55172880,\qquad
F_{38}=39088169<55172880\le F_{39}=63245986.
$$

故 $m=39$，$D(5040)\le D_{00}(5040)\le13$。另一方面，

$$
|\mathcal W_{12}|=F_{37}-1=24157816
<5040^2=25401600.
$$

命题 106.4 排除 $D(5040)\le12$，遂得两种深度都恰为 13。这个下界的语言要求在两种接缝后均合法。若只要求接在接缝 0 之后，首位可以为 1，完全相同的补零计数给出较大的词数 $F_{3L+2}-1$；在 $L=12$ 时为 $39088168>5040^2$，因而该计数不能排除较大语言的 12 窗覆盖。$\square$

### 106.4. 任意固定余数读出的有限未来界

**定义 106.6（固定读出的终端观察）。** 保留定义 104.2 的单位初始化、字母表 $\mathcal B$、接缝规则、正值规范 End 和吸收错误态。给定任意集合 $Y$、函数 $f:R\to Y$ 及 $\mathsf{err}\notin Y$，在成功 End 时输出 $f(N\bmod H)$，其余情形输出 $\mathsf{err}$。实际已初始化前缀为 $p=(\varepsilon,x)$，其中 $\varepsilon\in\{0,1\}$、$x\in\mathcal B^*$；这里也包括已进入错误态的前缀。以 $O_f(p,w)$ 表示在该前缀后接字面窗口词 $w\in\mathcal B^*$，随后查询 End 的输出。空后缀、非法接缝和末窗为零的词都在比较范围内，End 本身不计窗口。

**定理 106.7（共同系数探针的 horizon 转移）。** 对定义 106.6 中每个固定 $f$，以及任意两个实际已初始化前缀 $p,p'$，有

$$
\left[\forall w\in\mathcal B^*,\ |w|\le L(H)
\ \Longrightarrow\ O_f(p,w)=O_f(p',w)\right]
\quad\Longrightarrow\quad
\left[\forall w\in\mathcal B^*,\ O_f(p,w)=O_f(p',w)\right].
$$

前缀长度可以不同。此处 $|w|$ 为窗口数，$L(H)$ 为定理 106.3 的长度界。

证明。$L(H)\ge1$，所以假设包含空后缀和全部单窗词。任意活前缀接 $010$ 都合法并可作正值 End，其输出在 $Y$ 中；吸收错误态在这个后缀后仍报错。因此假设排除了一个活、一个错误的情形。两个错误态本来就有相同的全部未来。

若两者均活，空后缀先迫使其 End 标记 $E$ 相同，因为 $\mathsf{err}$ 不在 $Y$。接缝不同则用 $100$ 区分：接缝 0 一侧合法并增加正权重，末窗非零；接缝 1 一侧进入错误态。因此两者具有同一结构标签 $(s,E)$。记它们的算术坐标分别为 $(r,u,v)$ 与 $(r',u',v')$。

对每个 $A,B\in R$，定理 106.3 给出一个长度至多 $L(H)$ 的共同词，接在两边都允许正值规范 End。短词观察相等遂给出

$$
\forall A,B\in R,\qquad
f(r+Au+Bv)=f(r'+Au'+Bv').
$$

这是施加 $f$ 之后的标签等式。

现取任意字面后缀 $w$。两边同接缝，故其接缝非法与否一致；非法时都进入错误态。空词的输出已在假设中相等。非空合法词若末窗为 $000$，两边 End 标记都为零，仍同报错。其余非空合法词有非零末窗，在实际正权重上都给出正整数。引理 106.2 为这个任意长词提供同一个系数对 $(A_w,B_w)$，不论其首位是否为零。将此对代入标签等式，便得两边成功 End 的输出相等。

证明只用固定函数 $f$ 的标签等式，不要求 $f$ 单射、某个纤维唯一，或权重行间存在单位缩放。特别地，定理 106.5 给任意固定模 5040 读出一个充分的 13 窗界；其系数计数下界并不是各个读出任务的区分 horizon 下界。$\square$

## 107. 同源 CRT、有限稳定证书与三窗终端 horizon

### 107.1. 全部共同后缀的最小区分长度

**定义 107.1（完整未来的区分 horizon）。** 对 $H\ge2$，取定义 106.6 的固定读出

$$
\overline F_H(r)=\frac H{\gcd(\widetilde r,H)},\qquad r\in\mathbb Z/H\mathbb Z,
$$

其中 $\widetilde r$ 为任意整数代表；换代表不改变 gcd。在实际成功 End 上，它等于定义 104.2 的 $F_H(N)$。记相应观察为 $O_H(p,w)$。定义 $h(H)$ 为满足下式的最小非负整数 $L$：

$$
\forall p,p'\in\{0,1\}\times\mathcal B^*,\qquad
\left[\forall w\in\mathcal B^*,\ |w|\le L
\ \Longrightarrow\ O_H(p,w)=O_H(p',w)\right]
\quad\Longrightarrow\quad
\left[\forall w\in\mathcal B^*,\ O_H(p,w)=O_H(p',w)\right].
$$

定理 106.7 保证此最小值存在。每个前缀均按自己的实际单位初始化与字面词解释，允许两前缀长度不同，也允许错误前缀。后缀量词包含空词和全部产生错误输出的词，End 不消耗窗口。等价地，$h(H)$ 是使每对不同未来都存在一个长度至多 $h(H)$ 的共同区分后缀的最小界。

### 107.2. 同一源上的互素因子转移

**定理 107.2（互素因子的最大 horizon 界）。** 设 $I$ 为非空有限集，$H_i\ge2$ 两两互素，$H=\prod_{i\in I}H_i$。各模数均采用定义 107.1 的初始化、窗口和错误合同。若对每个 $i$，$h(H_i)\le L_i$，则

$$
h(H)\le\max_{i\in I}L_i.
$$

证明。把一个全局实际前缀 $p=(\varepsilon,x)$ 投影到模 $H_i$，保留同一个 $\varepsilon$ 和同一个字面词 $x$，只把算术坐标约化。定义 104.4 的加法和 Fibonacci 递推与约化交换，所以投影就是该字面前缀在局部模数上的实际运行。接缝、吸收错误和 End 标记均与模数无关。接入任意同一个后缀 $w$ 后，这些性质仍成立。

成功 End 时，各投影解释的是同一个正整数 $N$。因 $H_i$ 两两互素，每个素数幂仅属于一个因子，故

$$
\gcd(N,H)=\prod_{i\in I}\gcd(N,H_i),\qquad
F_H(N)=\prod_{i\in I}F_{H_i}(N).
$$

又 $F_{H_i}(N)\mid H_i$，而其它局部输出均与 $H_i$ 互素，因此每个局部标签可以从全局成功标签恢复：

$$
F_{H_i}(N)=\gcd(F_H(N),H_i).
$$

于是两个全局成功输出相等时，所有对应局部输出相等；反过来，所有局部输出相等时，乘积也相等。错误情形另行处理：同一源的全局和所有局部运行同步报错，不把 $\mathsf{err}$ 参与乘法或 gcd 运算。由于 $I$ 非空，一对源若一边成功、一边错误，任何局部观察也会区分它们。

置 $L=\max_iL_i$。若两个全局实际前缀在所有长度至多 $L$ 的共同后缀后输出相等，上述恢复式便给出每个局部投影在所有长度至多 $L_i$ 的后缀后输出相等。局部 horizon 假设推出该因子上所有有限后缀的输出相等。最后固定任意一个全局后缀 $w$，把这些针对同一个 $w$ 的局部等式按成功乘积或同步错误重组，就得到全局等式。

整个推导只投影实际共同来源，没有假定局部状态集合的笛卡尔积全部可达，也没有把分别取得的局部区分词拼成一个全局见证。$\square$

### 107.3. 有限覆盖与分区稳定的证明原则

**命题 107.3（有限语义状态与覆盖证书）。** 固定 $H\ge2$，令

$$
\mathcal U_H=\{\bot\}\ \sqcup\
\bigl\{(s,E,r,u,v):(s,E)\in\mathcal T,\ (r,u,v)\in(\mathbb Z/H\mathbb Z)^3\bigr\}.
$$

其两个初始状态为 $X_\varepsilon=(\varepsilon,\varepsilon,\varepsilon,2,3)$。对 $b=(b_0,b_1,b_2)\in\mathcal B$，在 $s=b_0=1$ 时转到 $\bot$，否则转到

$$
\delta_b(s,E,r,u,v)
=\bigl(b_2,[b\ne000],
 r+(b_0+b_2)u+(b_1+b_2)v,
 u+2v,2u+3v\bigr).
$$

$\bot$ 的五个后继均为 $\bot$。输出 $o_H$ 在 $\bot$ 或 $E=0$ 时为 $\mathsf{err}$，其余为 $\overline F_H(r)$。

设有限列出的状态集 $Q_H\subseteq\mathcal U_H$ 包含两个初始状态和 $\bot$，且每行的五个所列后继都属于 $Q_H$，并恰等于上述 $\delta_b$；所列输出也恰等于 $o_H$。则该表包含所有实际已初始化前缀的状态，并且在每个有限后缀上给出定义 107.1 的输出。若另为每个所列状态给出一个实际初始化与有限窗口词，并使其终态等于该状态，则 $Q_H$ 恰为实际可达集。

证明。先对实际输入窗数归纳验证语义不变量。读过 $j$ 窗的活状态满足

$$
r=N\bmod H,\qquad
(u,v)=(F_{3j+3},F_{3j+4})\bmod H,
$$

且 $s$ 是实际最高位，$E$ 是定义 104.2 的当前规范 End 标记。初始 $j=0$ 时 $N=\varepsilon$、$(u,v)=(2,3)$，各式成立。合法新窗的三个位权为 $u,v,u+v$，所加值和下一行正是上式的更新；新的最高位和末窗标记也与定义相同。非法接缝进入吸收态，与语义合同一致。活状态若 $E=1$，则或是尚无窗口而 $\varepsilon=1$，或最后一窗选择了正的实际 Fibonacci 权重；两种情形均有 $N>0$。所以成功输出确为 $F_H(N)$，即使 $r=0$ 也不会接受整数零。

两个初始状态在 $Q_H$ 中，且 $Q_H$ 对每个精确语义后继闭合，故对任意有限输入词归纳，其状态都在表中。输出一致性及相同的后继公式又给出任意后缀上的观察一致性。这个覆盖方向不需要假定表中每行可达。若每行另有具体实际见证，直接沿该见证应用同一语义不变量，得到反向包含，故表恰为实际可达集。$\square$

**引理 107.4（稳定观察分区给出全部未来）。** 在任意有限、具有五个总转移 $\delta_b$ 和终端输出 $o$ 的状态集 $Q$ 上，定义等价关系 $P_k$：

$$
\begin{aligned}
x\mathrel{P_0}y
&\quad\Longleftrightarrow\quad o(x)=o(y),\\
x\mathrel{P_{k+1}}y
&\quad\Longleftrightarrow\quad
x\mathrel{P_k}y\quad\text{且}\quad
\forall b\in\mathcal B,\ \delta_b(x)\mathrel{P_k}\delta_b(y).
\end{aligned}
$$

即新类由旧类及五个后继的旧类共同组成的签名确定。则 $P_{k+1}\subseteq P_k$，且 $x\mathrel{P_k}y$ 恰表示从 $x,y$ 出发对所有长度至多 $k$ 的后缀具有相同终端输出。若对某个 $d\ge0$ 有等价关系的实际相等

$$
P_d=P_{d+1},
$$

则 $P_d$ 就是全部有限后缀的输出等价关系。若 $Q$ 满足命题 107.3 的证书条件，这给出 $h(H)\le d$。

证明。递推定义立即给出嵌套性。$P_0$ 对应空后缀。假设结论对 $k$ 成立，则 $P_{k+1}$ 中旧类相同给出所有长度至多 $k$ 的观察相同，而每个后继的 $P_k$ 类相同，恰给出所有首字母为该 $b$、余词长度至多 $k$ 的观察相同。这些词覆盖全部非空、长度至多 $k+1$ 的后缀。反向若这些观察相同，则空词和较短词给出旧类相同，每个以 $b$ 开始的词给出对应后继类相同。归纳成立。

若 $P_d=P_{d+1}$，则 $P_d$ 等价的两个状态具有相同输出，因为 $P_d\subseteq P_0$；并且任一同字母后继仍 $P_d$ 等价，因为该对也属于 $P_{d+1}$。对任意后缀长度归纳，整个运行中保持 $P_d$ 等价，终端输出遂相等。反过来，所有有限后缀观察相等当然包括长度至多 $d$ 的词。命题 107.3 将每个实际前缀送入 $Q$，所以这一等价关系证明了实际 horizon 上界。

这里稳定的对象是等价关系本身。有限集上若已经证明 $P_{d+1}\subseteq P_d$，则类数相等也能推出关系相等：任何严格分裂都会增加类数。脱离此细化关系，两个相等的类数不能替代稳定性前提。$\square$

### 107.4. 四个局部有限证书的数学依赖

**假设 107.5（闭合乘积覆盖的有限证书条件）。** 对 $H_i\in\{16,9,5,7\}$，令 $R_i=\mathbb Z/H_i\mathbb Z$，并定义权重行的精确轨道与有限状态集

$$
\begin{aligned}
T_i(u,v)&=(u+2v,2u+3v),\\
\mathcal O_i&=\{T_i^j(2,3):j\ge0\}\subseteq R_i^2,\\
\mathcal T&=\{(0,0),(0,1),(1,1)\},\\
Q_{H_i}&=\{\bot\}\ \sqcup\
\{(s,E,r,u,v):(s,E)\in\mathcal T,\ r\in R_i,\ (u,v)\in\mathcal O_i\}.
\end{aligned}
$$

这里 $T_i$ 的行列式为 $-1$，所以它是有限集 $R_i^2$ 上的置换，轨道从 $(2,3)$ 出发并首次重复于 $(2,3)$。$Q_{H_i}$ 包含所有余数与三个结构标签的组合，是允许含不可达状态的闭合乘积覆盖。两个初始状态取 $X_\varepsilon=(\varepsilon,\varepsilon,\varepsilon,2,3)$，转移和终端输出取命题 107.3 的精确公式。

本节所用的有限证书条件是：[局部有限证书](../../reports/fib-canonical-horizon/README.md)在这些明确指定的 $Q_{H_i}$ 上，逐项核对两个初始状态及吸收错误态的包含、每行五个语义后继的闭合与输出一致性，并对引理 107.4 的关系给出

$$
P^{(16)}_3=P^{(16)}_4,\qquad
P^{(9)}_3=P^{(9)}_4,\qquad
P^{(5)}_2=P^{(5)}_3,\qquad
P^{(7)}_3=P^{(7)}_4.
$$

这些等式指同一局部状态集上的等价关系相等，初始标记为 $E=\varepsilon$，成功输出为 $H_i/\gcd(r,H_i)$，错误符号与数值输出分离。所引证书给出的轨道、完整后继表、输出及分区满足上述条件，其有限范围为

| $H_i$ | $\lvert\mathcal O_i\rvert$ | $\lvert Q_{H_i}\rvert=3H_i\lvert\mathcal O_i\rvert+1$ | 稳定关系 |
| --- | --- | --- | --- |
| $16$ | $8$ | $385$ | $P_3=P_4$ |
| $9$ | $8$ | $217$ | $P_3=P_4$ |
| $5$ | $20$ | $301$ | $P_2=P_3$ |
| $7$ | $16$ | $337$ | $P_3=P_4$ |

五个后继在全部 $1240$ 个状态上共给出 $6200$ 项转移核对。分区从实际终端输出开始；以当前输出和五个后继的旧类为签名，恰递推所有长度至多 $k$ 的观察等价，故与引理 107.4 的 $P_k$ 相同。固定状态次序、按类首次出现次序编号后，证书核对的是相邻完整分区向量逐项相等。有限条件只使用初始化、语义闭合、输出和稳定关系，不要求为乘积覆盖的每行提供实际字面词见证。

**推论 107.6（局部证书的全局上界）。** 在假设 107.5 的有限证书条件下，

$$
h(16)\le3,\qquad h(9)\le3,\qquad h(5)\le2,\qquad h(7)\le3,
\qquad h(5040)\le3.
$$

证明。对四个局部证书分别应用命题 107.3 和引理 107.4。两个实际初始化属于覆盖，且覆盖对精确语义转移闭合，故全部实际前缀都在有限表中。所列稳定关系使深度分别为 $3,3,2,3$ 的观察等价成为任意长后缀的输出合同；将此结论限制到实际前缀，便得到四个局部上界，无需其余行可达。最后 $5040=16\cdot9\cdot5\cdot7$，四因子两两互素，定理 107.2 给出最大值 3。这个上界的有限前提恰是四个局部证书的语义覆盖与稳定关系。$\square$

### 107.5. 两窗不够的实际前缀对

**命题 107.7（实际共同源对的三窗区分）。** 两个初始化均为 $\varepsilon=0$，取十窗前缀

$$
\begin{aligned}
x_1&=[010,100,100,100,010,000,000,000,000,001],\\
x_2&=[100,000,101,000,010,100,000,000,000,001],
\qquad p_i=(0,x_i).
\end{aligned}
$$

在模 5040 的正值规范 End 合同中，这两个实际前缀在全部长度至多 2 的共同后缀后输出相等，而共同后缀 $[000,000,010]$ 将它们区分。因此 $h(5040)\ge3$。

证明。按定义 104.2 的位序，两词选择的 Fibonacci 指标分别为 $\{4,6,9,12,16,32\}$ 和 $\{3,9,11,16,18,32\}$。每个集合内任意相邻指标差至少为 2，故均合法；最后一窗均为 $001$，故共同结构标签是 $(s,E)=(1,1)$。整数值为

$$
\begin{aligned}
N_1&=F_4+F_6+F_9+F_{12}+F_{16}+F_{32}=2179485,\\
N_2&=F_3+F_9+F_{11}+F_{16}+F_{18}+F_{32}=2182005.
\end{aligned}
$$

两者读过同样的十窗，下一实际行都是

$$
(F_{33},F_{34})=(3524578,5702887).
$$

又有

$$
\begin{gathered}
N_2-N_1=2520=8\cdot315,\\
(N_1,N_2)\equiv(2205,4725)\pmod{5040},\qquad
(N_1,N_2)\equiv(13,5)\pmod{16},\\
N_1\equiv N_2\equiv0\pmod{315},\qquad
N_1\equiv N_2\equiv5\pmod8.
\end{gathered}
$$

因为两个源具有相同接缝、End 标记和实际下一权重行，每个字面后缀的接缝合法性及最终 End 合法性在两边相同。非法或不能规范 End 的后缀都同报错；每个合法后缀则给两整数加上同一个实际增量 $\Delta$。成功时两者模 315 仍相等，所以 $F_{315}$ 标签相等。

为处理模 16，只须列出长度至多 2 的成功后缀可能给出的 $\Delta\bmod8$。初始权重行模 8 是 $(2,7)$，一窗之后变为

$$
(u+2v,2u+3v)\equiv(0,1)\pmod8.
$$

输入接缝是 1，第一窗只允许 $000,010,001$，其增量分别为 $0,7,1$，输出接缝分别为 $0,0,1$。在第二窗的行 $(0,1)$ 上，非零窗口 $100$ 的增量为 0，$010,101,001$ 的增量均为 1。若输入接缝为 0，这四种都合法；若输入接缝为 1，只有 $010,001$ 合法。第二窗若为 $000$ 则 End 报错，故成功的两窗后缀只可能产生

$$
\begin{array}{c|c}
\text{第一窗}&\text{两窗总增量模 }8\\ \hline
000&\{0,1\}\\
010&\{7,0\}\\
001&\{2\}
\end{array}
$$

空后缀增量为 0；成功的一窗后缀增量为 7 或 1。综上，所有成功且长度至多 2 的后缀均满足

$$
\Delta\bmod8\in\{0,1,2,7\},\qquad
(N_i+\Delta)\bmod8\in\{5,6,7,4\}.
$$

这些余数都非零，所以两个正整数的 2 进赋值均小于 3。它们相差 $2520$，模 16 相差 8；对任何赋值 $k<3$ 的整数 $a=2^kb$，$b$ 为奇数，加上 $8$ 的任意整数倍后仍为 $2^k$ 乘奇数。因此这里的两整数具有相同的 2 进赋值，进而有相同的 $\gcd(N_i+\Delta,16)$ 和 $F_{16}$ 标签。$16$ 与 $315$ 互素，成功时

$$
F_{5040}(N_i+\Delta)=F_{16}(N_i+\Delta)F_{315}(N_i+\Delta),
$$

所以所有这些成功短词也给出相同全局标签。连同已经处理的错误词和空词，得到对全部长度至多 2 的后缀的观察等式。

最后取 $w=[000,000,010]$。它在两边均合法，末窗非零。前两窗不增加整数，只推进六个位位置，第三窗的中位恰选择 $F_{40}=102334155$。故两个最终整数及其 gcd 为

$$
\begin{aligned}
N_1+F_{40}&=104513640,&\gcd(104513640,5040)&=840,\\
N_2+F_{40}&=104516160,&\gcd(104516160,5040)&=1680.
\end{aligned}
$$

于是 $O_{5040}(p_1,w)=6$，$O_{5040}(p_2,w)=3$。两者全部未来不同，却无法被任何至多两窗的后缀区分，故 $h(5040)\ge3$。$\square$

**定理 107.8（模 5040 的精确终端 horizon）。** 在假设 107.5 的有限证书条件下，定义 107.1 的原始终端 $F_{5040}/\mathsf{err}$ 任务满足

$$
\boxed{h(5040)=3},\qquad
\boxed{D(5040)=D_{00}(5040)=13}.
$$

证明。推论 107.6 由局部有限证书和同源 CRT 给出 $h(5040)\le3$，命题 107.7 的实际前缀对给出反向不等式。第二个等式是定理 106.5，与局部证书无关。

两种最小值的量词不同：$D$ 要求对每个模系数对都有一个两接缝合法、非零末窗的共同词，并且其值公式对所有行同时成立；$h$ 要求每对不同的实际终端未来存在一个共同区分词。粗读出 $F_{5040}$ 可以合并不同系数作用的结果，因此前者为 13 与后者为 3 相容。后者的读出固定为 $F_{5040}$，并只在窗口词结束后查询 End。$\square$

## 追加锚（递归块 Robin 主编码批次后）

## 108. 有限未来预算的共同相位支撑与最小静态摘要

### 108.1. 从当前任意前缀开始的未来预算

**定义 108.1（实际响应向量与静态摘要合同）。** 沿用定义 104.2、107.1 的原始终端任务。源域是全部实际已初始化前缀

$$
\mathcal P=\{0,1\}\times\mathcal B^*,\qquad
\mathcal B=\{000,100,010,101,001\}.
$$

单位位 $\varepsilon$ 的两种选择、任意有限过去长度、空窗口列及已进入吸收错误态的字面前缀均在域内。位序由低到高，初始化接缝与 End 标记均为 $\varepsilon$。非法接缝进入 $\bot$，合法非空输入后的 End 标记为末窗是否非零；只有合法且可作正值规范 End 的前缀输出 $F_H(N)=H/\gcd(N,H)$，其余输出共同的 $\mathsf{err}$。End 是终端查询，本身消耗零窗。

对 $t\ge0$，令 $\mathcal W_t=\{w\in\mathcal B^*:|w|\le t\}$，定义

$$
S_{H,t}(p)=\bigl(O_H(p,w)\bigr)_{w\in\mathcal W_t},\qquad
Q_{H,t}=S_{H,t}(\mathcal P),\qquad
N_{H,t}=|Q_{H,t}|.
$$

向量按所有字面后缀索引，包含空词、非法接缝词、不能规范 End 的词以及错误输出；不先筛选成功词。$H=5040$ 时简记为 $S_t,Q_t,N_t$。$Q_{H,t}$ 也等同于按响应相等得到的实际前缀商集。计数对象是不同响应向量，不是前缀、相位见证或整数的数目。

静态编码器可读取一个实际前缀或它的充分表示，形成摘要 $e_t(p)$；解码器输入摘要及任意 $w\in\mathcal W_t$，必须返回 $O_H(p,w)$。解码器可知道剩余未来预算 $t$，但不免费得到过去相位、过去长度、接缝或 End 标签、源余数或原前缀。预算从当前边界开始，不约束已经读过多少窗；获取这个快照的过程与逐窗在线编码任意长过去是两个合同。

### 108.2. 实际共同相位及局部签名的相容性

**命题 108.2（每个共同相位的实际满余数纤维）。** 取 $H=5040=16\cdot9\cdot5\cdot7$，记

$$
A=(0,0),\qquad B=(0,1),\qquad C=(1,1),\qquad
T(u,v)=(u+2v,2u+3v).
$$

从 $(2,3)$ 出发的模 $5040$ 轨道，以及它在四因子上的投影，具有下列精确周期；这些有限轨道等式是本命题的有限计算前提，见[共同相位有限证书](../../reports/fib-canonical-budget/README.md)。

$$
\operatorname{per}_{5040}(2,3)=80,\qquad
\bigl(\operatorname{per}_{16},\operatorname{per}_{9},
\operatorname{per}_{5},\operatorname{per}_{7}\bigr)=(8,8,20,16).
$$

令 $J=\{0,\ldots,79\}$，$w_j=T^j(2,3)\bmod5040$。在这些轨道条件下，实际活坐标的像恰为

$$
\{A,B,C\}\times(\mathbb Z/5040\mathbb Z)\times\{w_j:j\in J\}.
$$

每个坐标还可由正整数值的实际前缀实现；另有一个吸收错误态。

证明。引理 105.1 已给出合并两种单位初始化后，对每个实际窗数 $n\ge1$ 的三个整数像：

$$
\begin{aligned}
I_n(A)&=[0,F_{3n}-1]\cap\mathbb Z,\\
I_n(B)&=[F_{3n},F_{3n+2}-1]\cap\mathbb Z,\\
I_n(C)&=[F_{3n+2},F_{3n+3}-1]\cap\mathbb Z.
\end{aligned}
$$

这里每个整数均由实际合法位列取得。所用有限区间性质把最高位为零和为一的两段 $[0,F_m-1]$、$F_m+[0,F_{m-1}-1]$ 接成 $[0,F_{m+1}-1]$；按最高三位分类便是上述三段。其长度分别为 $F_{3n},F_{3n+1},F_{3n+1}$，不能在这一论证中固定某个 $\varepsilon$。

固定 $j_0\in J$ 和标签 $a$，取 $n=j_0+80k\ge1$，令 $k$ 足够大，使 $I_n(a)$ 的长度严格大于 5040。此时下一权重行仍为 $w_{j_0}$，连续整数区间含每个模 5040 余数。$B,C$ 两段本来全为正数；$A$ 段也含 $1,\ldots,5040$，因而零余数可选正代表 5040，其余余数也可选正代表。引理 105.1 将所选整数还原为同一相位、同一标签下的实际前缀，得满纤维方向。

反向，任何实际活前缀都有这三个标签之一，其下一行是 $(F_{3n+3},F_{3n+4})$ 的约化，由轨道条件属于所列 80 行，其余数当然属于 $\mathbb Z/5040\mathbb Z$；这也覆盖 $n=0$ 的两个初始化。实际非法前缀例如 $(0,[001,100])$ 进入 $\bot$，其后所有词都保持错误。由定义 104.4 的语义不变量，相同坐标在每个后缀上给出相同输出；所以整数零及全零活前缀不会在上述正代表之外增加签名，但它们仍不能在 $E=0$ 时成功 End。$T$ 的行列式为 $-1$，在各有限模环上可逆，故从初始行首次返回的有限轨道列举确实给出精确周期，并覆盖所有非负时刻。

取任意大的 $n=j_0+80k$ 是本结论的承重步骤；一个预先固定的小过去长度没有此满纤维保证。例如固定 $\varepsilon=0,n=1$ 时标签 $B$ 只有值 2、3，缺少合并两种初始化区间内的 4。$\square$

**定理 108.3（共同相位支撑的充要条件与签名双射）。** 设非空有限因子列 $H_1,\ldots,H_m\ge2$ 两两互素，$H=\prod_iH_i$。固定标签 $a$、深度 $t$ 和非空有限共同相位集 $J$。假设同一实际源模型在每个 $j\in J$、标签 $a$ 下具有全部模 $H$ 余数的实际纤维，且每个该标签的实际源均由某个 $(j,r)$ 表示。其局部模型是同一窗口语义的模 $H_i$ 投影，使用同一字母表与后缀集合；对固定 $a,w$，成功或错误的模式与余数、相位无关，成功时全局与局部均读同一正整数的 $F$ 标签。

记局部模型在 $(a,j,r_i)$ 处的响应为 $S_{i,t}(a,j,r_i)$，并置

$$
\begin{aligned}
\Sigma_i(a,t)&=\{S_{i,t}(a,j,r_i):j\in J,\ r_i\in\mathbb Z/H_i\mathbb Z\},\\
M_i(\sigma)&=\{j\in J:\exists r_i\in\mathbb Z/H_i\mathbb Z,
\ S_{i,t}(a,j,r_i)=\sigma\}.
\end{aligned}
$$

则局部签名元组 $(\sigma_1,\ldots,\sigma_m)$ 来自一个该标签的实际全局前缀，当且仅当

$$
\bigcap_{i=1}^m M_i(\sigma_i)\ne\varnothing.
$$

而且实际全局签名与这些相容元组之间是双射。

证明。若元组来自一个实际前缀，该前缀有同一个相位 $j$ 和全局余数 $r$；投影余数 $r\bmod H_i$ 在此 $j$ 实现各分量，因此 $j$ 属于全部支撑，得必要性。

反之，先选交集内的一个 $j$，再对每个 $i$ 选一个在此 $j$ 实现 $\sigma_i$ 的局部余数 $r_i$。中国剩余定理给出同时满足 $r\equiv r_i\pmod{H_i}$ 的全局余数 $r$。满实际纤维假设再给出标签 $a$、相位 $j$、余数 $r$ 的一个实际前缀。模约化与窗口更新交换，其局部签名正是所选元组。这里先同步相位，再用 CRT，最后用实际可达性；局部各自有实现并不能替代最后一步。

对每个成功后缀，由两两互素性，

$$
F_H(N)=\prod_{i=1}^m F_{H_i}(N),\qquad
F_{H_i}(N)=\gcd(F_H(N),H_i).
$$

前式构造全局标签，后式从全局标签唯一恢复每个局部标签，因为其它因子的标签均与 $H_i$ 互素。错误位置在所有分量中同步，另以 $\mathsf{err}$ 处理，不对它作乘法或 gcd。逐坐标应用这两个互逆规则，便将实际全局签名与相容元组互相恢复；这同时证明单射性，故不是仅有一个满射。$\square$

**命题 108.4（仅有边缘支撑不足以保证共同实现）。** 若删除定理 108.3 的满余数纤维假设，则非空共同相位支撑不足以推出联合实现。

证明。取单相位集 $J=\{j\}$，两坐标的实际允许对仅为 $(0,0),(1,1)$，各坐标读出自己的值。每个坐标的两个局部值都在 $j$ 有实现，所以每个支撑都是 $\{j\}$，但元组 $(0,1),(1,0)$ 没有共同实现。即使用本节的 $F$ 读出，也可在 $t=0$、同一成功标签和相位下，把实际全局余数限制为模 6 的 0、1：模 2、模 3 的余数对仍只有 $(0,0),(1,1)$，其局部输出对分别为 $(1,1),(2,3)$。两个局部输出集中的每个标签都有完整单相位支撑，但 $(1,3),(2,1)$ 不可联合实现。这样的受限规范源域可从命题 108.2 的同一标签 $B$、同一相位纤维中，仅选模 5040 余数为 0、1 的两个实际正前缀，再约化到模 6 得到；这里主动限制了源域。CRT 给出其余组合的余数，却不能提供被限制掉的实际源。这正是满实际纤维假设排除的障碍。$\square$

### 108.3. 支撑直方图、重叠与精确有限计数

**定理 108.5（交集直方图只计签名一次）。** 在定理 108.3 的假设下，定义

$$
h_i(M)=\#\{\sigma\in\Sigma_i(a,t):M_i(\sigma)=M\},
\qquad \varnothing\ne M\subseteq J.
$$

令 $D_0(J)=1$、其余 $D_0(K)=0$。按因子顺序递推，对非空 $K\subseteq J$ 取

$$
D_{k+1}(K)=
\sum_{\substack{M,L\subseteq J\\ M\cap L=K\ne\varnothing}}
D_k(M)h_{k+1}(L).
$$

则固定标签 $a$ 的实际全局签名数为

$$
C_{a,t}=\sum_{\varnothing\ne K\subseteq J}D_m(K).
$$

证明。归纳断言为：$D_k(K)$ 等于共同支撑恰为 $K$ 的有序 $k$ 元局部签名组数。空元组的支撑按约定为 $J$，故初值成立。一个 $k+1$ 元组唯一拆成前 $k$ 个分量和最后一个分量；若两者支撑分别为 $M,L$，新支撑恰为 $M\cap L$。有 $D_k(M)h_{k+1}(L)$ 种这样的选择，对给定交集求和不漏不重。交集为空者再增加分量也不可能变成非空，因此可立即丢弃。归纳完成后，定理 108.3 的双射把相容元组数变成实际全局签名数。

一个签名被多个余数或多个相位实现时，仍只在 $h_i$ 中计一次；$|K|$ 表示见证相位数，不能再乘到 $D_m(K)$ 上。各局部签名数的独立乘积则把空交集元组也算入，因而通常不等于所求计数。$\square$

**命题 108.6（标签分离与零预算的重叠）。** 对本节的实际规范源域，$t\ge1$ 时三个活标签的签名集两两不交，且均不含吸收态的恒错签名，故

$$
N_t=1+C_{A,t}+C_{B,t}+C_{C,t}\qquad(t\ge1).
$$

$t=0$ 时，$A$ 与吸收态具有同一个错误签名，$B,C$ 各自具有同一个完整的 60 元正标签像，因此 $N_0=61$。

证明。$A$ 的空后缀输出为错，而 $B,C$ 的空后缀输出成功。对 $B,C$，一窗 $100$ 在接缝 0 时合法且以正非零窗终止，在接缝 1 时非法。最后 $010$ 从任一活接缝都合法，选择正的中位权重，因而成功；从吸收态出发则仍报错。这三个共同后缀均在 $t\ge1$ 的比较域内，给出所需分离。

零预算只看空后缀。任一正整数 $N$ 的 $H/\gcd(N,H)$ 都是 $H$ 的正因子；反之，给定 $d\mid H$，取正整数 $H/d$ 所属余数，命题 108.2 在标签 $B$ 和 $C$ 下分别给出该余数的实际正代表 $N$，于是 $\gcd(N,H)=H/d$，输出正是 $d$。因此两标签各自的像恰为全部正因子。$5040=2^4 3^2 5\cdot7$ 的正因子数是 $(4+1)(2+1)(1+1)(1+1)=60$。$A$ 和吸收态都只输出同一个 $\mathsf{err}$，遂得 $60+1=61$；把四个像误当作互不相交而求和得到的 $1+60+60+1=122$ 并非实际像基数。$\square$

**定理 108.7（四层实际签名数及三窗后的稳定值）。** 命题 108.2 的轨道条件及下述精确有限递推给出

| 预算 $t$ | $C_{A,t}$ | $C_{B,t}$ | $C_{C,t}$ | 实际总数 $N_t$ |
| --- | --- | --- | --- | --- |
| $t=0$ | $1$ | $60$ | $60$ | $61$（标签像重叠） |
| $t=1$ | $11790$ | $31096$ | $5572$ | $48459$ |
| $t=2$ | $189000$ | $189000$ | $157500$ | $535501$ |
| $t=3$ | $201600$ | $201600$ | $201600$ | $604801$ |

再在假设 107.5 的有限稳定关系条件下，有

$$
N_t=604801\qquad\text{对所有 }t\ge3.
$$

证明。对每个局部模数 $q\in\{16,9,5,7\}$，取命题 107.3 的局部语义状态及输出，递归定义精确输出树

$$
\begin{aligned}
R_{q,0}(z)&=o_q(z),\\
R_{q,t+1}(z)&=\bigl(o_q(z),
 (R_{q,t}(\delta_bz))_{b\in\mathcal B}\bigr).
\end{aligned}
$$

对 $t$ 归纳，树相等恰表示所有长度至多 $t$ 的字面后缀输出相等：根是空词，五个子树分别是五种首窗之后的全部余词，错误态也遵守同一递推。故相等树可作局部签名的精确代表。

固定 $a,t$，对每个共同相位 $j\in J$ 与每个局部余数 $r\bmod q$ 取状态 $(a,r,w_j\bmod q)$，合并相等树，并给每棵不同树记录其全部实现相位的集合。得到的正是定理 108.3 的 $\Sigma_i,M_i$；将每个支撑的不同树数形成 $h_i$，再按定理 108.5 求交集直方图。命题 108.2 保证这些模型覆盖全部实际源，并具有所需满纤维；错误模式仅由初始标签、窗口接缝与最后一窗决定，与算术余数及相位无关。

本表的有限数值依赖是[有限证书及完整支撑直方图](../../reports/fib-canonical-budget/README.md)所列上述递推的精确整数值：它们按因子顺序 $16,9,5,7$，在共同的 80 相位上合并不同局部树，再计算非空支撑交集。前四行仅依赖这一次有限递推和命题 108.6 的并集规则，不以完整未来稳定性作为计数输入。例如 $t=1,a=A$ 的四个局部签名数是 $17,20,9,9$，独立乘积为 27540，而非空共同支撑的元组数是 11790。差额来自不相容的共同相位，不能用各自存在局部相位来补足。

最后，定理 107.8 在假设 107.5 下给出 $h(5040)=3$。因此两个实际前缀的 $S_3$ 相等当且仅当全部未来相等，也就当且仅当任意 $t\ge3$ 的 $S_t$ 相等。这些响应向量虽有不同的坐标集，却划分同一个实际源域，故其像基数均为 $N_3$。这一步使用 §107 的稳定关系证明；四个计数本身不蕴含更长未来的稳定性。精确系数任务的 13 窗深度是另一个合同，不参与本节计数。$\square$

### 108.4. 静态最小性、递减预算与固定层的障碍

**定理 108.8（最小静态摘要与逐层更新）。** 在定义 108.1 的合同中，对每个固定 $t$，充分摘要的实际像基数最小值恰为 $N_{H,t}$。对 $t\ge1$ 和每个 $b\in\mathcal B$，存在良定义的更新

$$
\delta_b^t:Q_{H,t}\longrightarrow Q_{H,t-1},\qquad
\delta_b^t(S_{H,t}(p))=S_{H,t-1}(pb),
$$

其中 $pb=(\varepsilon,xb)$。每层的当前输出由空后缀坐标给出。

证明。若两个不同响应向量的源被编码成同一个摘要，必有某个 $w\in\mathcal W_t$ 使它们的正确输出不同；解码器却在相同摘要、相同 $t$、相同 $w$ 上只能返回一个值，矛盾。因此每个摘要纤维包含于一个响应等价类，摘要的实际像至少有 $N_{H,t}$ 个元素。反向直接以 $S_{H,t}(p)$ 为摘要，按 $w$ 查对应坐标即可准确解码，达到该基数。

若 $S_{H,t}(p)=S_{H,t}(p')$，则对任意 $|w|\le t-1$，有 $|bw|\le t$，所以

$$
O_H(pb,w)=O_H(p,bw)=O_H(p',bw)=O_H(p'b,w).
$$

故后继的 $S_{H,t-1}$ 相等，更新不依赖代表元。该等式也适用于非法窗与吸收态。空后缀本来就在每层的索引域中，给出输出函数。$\square$

**命题 108.9（预算控制与获取摘要的合同边界）。** 外部已知的剩余预算允许使用依赖 $t$ 的解码与更新函数，各层可复用标签，因而各层的最小基数不推出 $\sum_tN_t$ 是必须的记忆大小。若预算也须在内部保存，在一个有限初始预算 $T$ 下，带预算标签的不交并

$$
\bigsqcup_{t=0}^T\bigl(\{t\}\times Q_{H,t}\bigr)
$$

可实现预算内的逐层精确输出；其最小性需要另一个完整合同。若总输入预算 $T$ 从单位初始化开始计，则剩余预算 $t$ 处的过去长度至多 $T-t$，不能直接套用本节任意过去源域的计数。

证明。外部给定 $t$ 时，令每层编码取值于同一个标签集合的前 $N_{H,t}$ 个元素，以 $t$ 选择相应坐标解码和定理 108.8 的更新即可；同一个标签在不同层有不同解释，不构成冲突。若 $t$ 不外给，状态 $(t,q)$ 明确保留层号，正预算时读一窗转为 $(t-1,\delta_b^t(q))$，空后缀输出由 $q$ 决定，因此不交并是预算内合同的一个充分实现。预算如何传入、耗尽后窗口是否被拒绝以及拒绝后怎样继续，均须在自主合同中另行指定；若要求总转移，可按该合同另加耗尽处理态。这里没有据此证明不交并最小。

静态上界允许编码器先获得实际前缀或充分表示，并没有为读入任意长过去提供只用 $N_{H,t}$ 个状态的更新法。外给的 $t$ 仅计当前边界之后的窗口，不能作为过去相位时钟。若另改成总预算合同，$n\le T-t$ 排除了命题 108.2 中任意增大 $n=j_0+80k$ 的步骤；可用的实际纤维必须在这个受限域重新计算。因此本节的精确最小值不自动成为受限总长度合同的最小值。$\square$

**命题 108.10（前三层不支持全部固定层更新）。** $Q_0,Q_1,Q_2$ 都不能使每个字母诱导同层更新 $Q_t\to Q_t$；$Q_3$ 的同层闭合性则在假设 107.5 下由定理 107.8 给出。

证明。记 $p\sim_t p'$ 当且仅当 $S_t(p)=S_t(p')$。这些关系随 $t$ 细化。若每个字母都诱导良定义的 $Q_t\to Q_t$，则 $\sim_t$ 是右同余；它又保持空后缀输出。对词长归纳，$p\sim_t p'$ 将保持每个后缀后的输出，因而已是全部未来等价，尤其 $\sim_t=\sim_{t+1}$。但是定理 108.7 给出

$$
61<48459<535501<604801,
$$

故 $t=0,1,2$ 各自存在严格细化，不可能有全部同层更新。这里不能把定理 108.8 的 $Q_t\to Q_{t-1}$ 偷换为同层映射。

具体取命题 107.7 的实际前缀 $p_1,p_2$，其整数分别为 2179485、2182005，下一行均为 $(3524578,5702887)$，标签均为 $C$。该命题已证明它们在全部 $1+5+25=31$ 个长度至多 2 的字面后缀上相等，即 $S_2(p_1)=S_2(p_2)$。在共同读入一个 $000$ 后，剩余词 $[000,010]$ 却分别给出 6、3，所以后继的 $S_2$ 不同，直接否定 $\delta_{000}:Q_2\to Q_2$ 的良定义性。

再令 $q_i=p_i[000]$。任意至多一窗后缀接到 $q_i$，对应于原来至多两窗的后缀，故 $S_1(q_1)=S_1(q_2)$。再共同读一个 $000$ 后，单窗 $010$ 分别给出 6、3，直接否定 $Q_1$ 的固定层更新。零预算可取实际活前缀 $(0,[000])$ 和实际错误前缀 $(0,[001,100])$：当前都报错；共同读入 $010$ 后，前者值为 $F_7=13$，成功输出 5040，后者仍在吸收态报错。因此 $Q_0$ 也失败。

最后由定理 107.8，$\sim_3$ 恰为全部未来等价，而全部未来等价在同字母延伸下仍保持；故 $Q_3$ 及所有 $t\ge3$ 的对应商具有良定义的同层更新。这一结论沿用原始正值规范 End 的稳定证明，不由有限支撑计数单独推出。$\square$

## 追加锚（递归块 Robin 主编码批次后）

## 109. 实际规范来源的 gcd 终端深度与平衡相位下界

**定义 109.1（本节合同与最大完整素幂）。** 沿用定义 104.2、104.4、107.1。模数 $H\ge2$，实际源是全部 $(\varepsilon,x)\in\{0,1\}\times\mathcal B^*$，其中 $\mathcal B=\{000,100,010,101,001\}$ 按低位到高位排列；两种初始化、任意过去长度以及已经非法的前缀均在量词内。初始活坐标为 $(s,E,r,u,v)=(\varepsilon,\varepsilon,\varepsilon,2,3)$ 模 $H$。合法 $j$ 窗后的实际下一行为 $(F_{3j+3},F_{3j+4})$，更新算子为 $T(u,v)=(u+2v,2u+3v)$。每次比较都接入同一个字面后缀，不提供额外相位、已读长度或前缀重读。

$h(H)$ 仍是定义 107.1 的最小区分窗口界：全部长度至多 $L$ 的共同后缀响应相等蕴含全部有限共同后缀响应相等。响应向量保留空后缀、非法接缝与不合规范的 End。End 本身计零窗；吸收态或活态 $E=0$ 输出 $\mathsf{err}$，活态 $E=1$ 才成功，且其实际整数 $N>0$，输出 $F_H(N)=H/\gcd(N,H)$。余数零是成功标签；整个末窗 $000$ 则清除 $E$，不能因过去已有正值而成功 End。

置

$$
Q(H)=\max_{p\mid H}p^{v_p(H)},\qquad \phi=\frac{1+\sqrt5}{2}.
$$

最大值取的是每个素数在 $H$ 中的**完整**素幂。将 Fibonacci 递推扩展到全部整数指标，约定 $F_{-n}=(-1)^{n+1}F_n$。对整数 $L\ge1$，记

$$
r_0=\lfloor L/2\rfloor,\qquad
B_L=F_{3r_0+2}+F_{3(L-r_0)+1}-2.
$$

以下推导以 §§104–107 的既有结论为前提，属于本仓合同上的普通数学推导（repo-derived）；负指标只用来选取模权重的整数代表，并不允许读者倒退。

**命题 109.2（平衡相位的严格缺失余数判据）。** 若 $q=p^a\parallel H$，$a\ge1$，且整数 $L\ge1$ 满足

$$
B_L+1<q-q/p,
$$

则 $h(H)>L$。这是充分判据；判据失败不推出相反的 horizon 上界。

证明。令 $P=P(H)=\pi(H)/\gcd(\pi(H),3)$ 为命题 105.2 的实际三步行周期。因为 $T=S^3$，$S(u,v)=(v,u+v)$ 可逆，实际行可写成

$$
w_j=T^{j+1}(0,1).
$$

取一个实际整数 $j\ge1$，满足 $j+1+r_0\equiv0\pmod P$。不断给 $j$ 加 $P$，直到 $F_{3j+1}\ge H$；Fibonacci 数无界，故可做到。所有这些 $j$ 都处于同一实际相位，并有

$$
w_j\equiv T^{-r_0}(0,1)
=(F_{-3r_0},F_{-3r_0+1})\pmod H.
$$

引理 105.1 在**两种初始化的并集**上给标签 $C=(1,1)$ 的精确实际整数像

$$
I_j(C)=[F_{3j+2},F_{3j+3}-1]\cap\mathbb Z.
$$

其长度是 $F_{3j+1}\ge H$，所以在这一个 $j$、一个标签和一个实际行上，每个模 $H$ 余数都有正整数前缀实现。所选两个前缀的单位初始化不必相同；此处不假定不同局部相位可以任意拼接。

对任意至多 $L$ 窗的合法后缀，其贡献模 $H$ 可用连续权重

$$
F_i,\qquad -3r_0\le i\le3(L-r_0)-1
$$

的一个子集和表示。短词只在计算此和时补零到 $3L$ 位。令 $J_-$ 为这些权重中全部负项之和，$J_+$ 为全部正项之和，则每个贡献代表都在整数区间 $[J_-,J_+]$ 中。忽略接缝与无相邻 1 的限制只会扩大集合。用 $|F_{-n}|=F_n$ 和求和恒等式 $\sum_{n=1}^{m}F_n=F_{m+2}-1$，得

$$
\begin{aligned}
J_+-J_-
&=\sum_{n=1}^{3r_0}F_n+\sum_{n=0}^{3(L-r_0)-1}F_n\\
&=(F_{3r_0+2}-1)+(F_{3(L-r_0)+1}-1)=B_L.
\end{aligned}
$$

求和恒等式由 $m=0$ 的空和及 Fibonacci 递推归纳即得，故也覆盖 $r_0=0$。特别地 $L=1$ 时指标为 $0,1,2$，$B_1=2$。这里仅断言包络包含；没有断言每个内部整数、两个端点都由合法词达到。补零也仅用于包含关系，不执行补上的零窗，更不把最后一窗 $000$ 当作成功 End。

令 $V_L\subseteq\mathbb Z/q\mathbb Z$ 为从上述共同标签与相位出发、至多 $L$ 窗且成功 End 的后缀贡献集合。它只由行、标签及字面后缀决定，与初始余数无关。空后缀成功，故 $0\in V_L$；即使区间取模后有重合，仍有 $|V_L|\le B_L+1$。假设给出

$$
|\,\mathbb Z/q\mathbb Z\setminus V_L\,|>q/p.
$$

模 $q/p=p^{a-1}$ 只有 $q/p$ 个类，故有两个不同的缺失余数 $z_1,z_2$，满足 $z_1\equiv z_2\pmod{q/p}$。置 $c_i=-z_i\pmod q$。任一成功短后缀的贡献 $v\in V_L$ 都使 $c_1+v,c_2+v$ 非零模 $q$，且两者模 $p^{a-1}$ 相同。若其共同类非零模 $p^{a-1}$，它决定两者相同的深度 $t<a-1$；若共同类为零，非零模 $p^a$ 则迫使两者深度都为 $a-1$。$a=1$ 时只有后一种情形，即两者都是单位。因此所有成功短后缀后的局部 gcd 相等。

由 CRT 取全局余数 $R_1,R_2$：在完整因子 $q$ 上分别为 $c_1,c_2$，在其它完整素幂因子上取相同余数，例如都取零。由同一个 $I_j(C)$ 实现这两个余数为实际正前缀。两者标签和实际行相同，所以非法后缀与不合规范的 End 都同步报错；成功短后缀在选定因子上 gcd 相同，在其它因子上连最终余数都相同。因此全局 $F_H$ 响应相同，空词也在其中。

最后证全部未来不同。共同实际行 $(u,v)$ 是幺模行，取 $\alpha u+\beta v=1\pmod H$，并取 $(A,B)=(-R_1\alpha,-R_1\beta)$。定理 106.3 给出一个以 $00$ 开头、末窗非零的有限共同字面探针，普遍系数为 $(A,B)$ 模 $H$。它在两边合法且成功 End，最终余数分别为 $0$ 与 $R_2-R_1\ne0\pmod H$，故 $F_H$ 分别为 $1$ 与大于 $1$ 的数。实际整数仍严格为正，模零没有被误当作整数零。于是已有实际源对在全部至多 $L$ 窗上相等而完整未来不同，即 $h(H)>L$；无需再用分类器必要性。$\square$

**定理 109.3（端点的统一对数阶）。** 对每个 $H\ge2$，有

$$
\left|h(H)-\frac23\log_\phi Q(H)\right|<3.
$$

更具体地，置 $Q=Q(H)$，则

$$
\frac23\log_\phi Q-\frac23\log_\phi8
<h(H)
\le\left\lceil\frac{2+\log_\phi(4Q^2+Q)}3\right\rceil
<\frac23\log_\phi Q+\frac{5+\log_\phi(9/2)}3.
$$

证明。先给所有 $H$ 共同的 $h(H)\ge1$。实际前缀 $(0,\text{空词})$ 是活态且 $E=0$；$(1,[100])$ 已进入吸收错误态。两者立即 End 都报错，但共同后缀 $010$ 只在前者成功，实际值为 $3$。所以零窗观察不足。

由递推和 $F_1=1,F_2=1$ 得 $F_n\le\phi^{n-1}$（$n\ge1$）。若 $L=2r\ge2$，则

$$
B_L+2=F_{3r+3}\le\phi^{3r+2}
=\phi^2\phi^{3L/2}<4\phi^{3L/2}.
$$

若 $L=2r+1\ge1$，则

$$
\begin{aligned}
B_L+2&=F_{3r+2}+F_{3r+4}\\
&\le\phi^{3r+1}(1+\phi^2)
=\phi^{3L/2}\frac{\phi+2}{\sqrt\phi}
<4\phi^{3L/2}.
\end{aligned}
$$

最后一步用 $1<\phi<2$。因此包括 $L=1$ 在内，有 $B_L+2\le4\phi^{3L/2}$。若 $q\ge8\phi^{3L/2}$，便有

$$
B_L+1\le q/2-1<q/2\le q-q/p,
$$

即使 $p=2$，命题 109.2 要求的严格不等式也成立。

记 $t=\frac23\log_\phi Q$、$a_0=\frac23\log_\phi8$。若 $t-a_0\ge1$，取 $L=\lfloor t-a_0\rfloor\ge1$，则 $Q\ge8\phi^{3L/2}$，从而 $h(H)\ge L+1>t-a_0$。若 $t-a_0<1$，直接用 $h(H)\ge1>t-a_0$。这给出端点下界，取整没有再损失一个窗口。

上界只复用定理 106.3 的 first-$00$ 构造。为避免和当前窗口预算 $L$ 混淆，把该定理在模数 $n\ge2$ 的长度界记为 $\ell(n)$：令 $J$ 是 $F_J>2n$ 的最小指标，$T_n=F_J$，$M$ 是 $F_M\ge n(T_n+1)$ 的最小指标，则 $\ell(n)=\lceil M/3\rceil$ 且 $2n<T_n<4n$。递推从 $m=2,3$ 给出 $F_m\ge\phi^{m-2}$，所以

$$
\begin{aligned}
M&\le\lceil2+\log_\phi(4n^2+n)\rceil,\\
\ell(n)&\le
\left\lceil\frac{\lceil2+\log_\phi(4n^2+n)\rceil}{3}\right\rceil
=\left\lceil\frac{2+\log_\phi(4n^2+n)}3\right\rceil=:U(n).
\end{aligned}
$$

中间的取整恒等式用分母 $3$ 为正整数。定理 106.7 直接把共同系数探针转为固定读出的 horizon 上界，故每个完整素幂因子 $q\parallel H$ 都有 $h(q)\le\ell(q)\le U(q)$。定理 107.2 投影的是同一实际前缀与同一字面后缀，给出

$$
h(H)\le\max_{q\parallel H}h(q)\le U(Q),
$$

此处最大值中的 $q$ 只取完整素幂；$U$ 随参数不减。其同源 CRT 依据是成功时 $F_H=\prod_qF_q$ 且 $F_q=\gcd(F_H,q)$，错误则单独同步处理，并非独立局部相位的可达性假定。

因为 $Q\ge2$，$4+1/Q\le9/2$，且对每个实数 $y$ 都有 $\lceil y\rceil<y+1$，所以

$$
U(Q)<t+\frac{5+\log_\phi(9/2)}3.
$$

最后 $\phi^3=2\phi+1>4$ 蕴含 $\phi^{9/2}>8$，故 $a_0<3$；$\phi^4=3\phi+2>9/2$ 蕴含 $(5+\log_\phi(9/2))/3<3$。两侧都是严格界，小 $Q$ 已由 $h(H)\ge1$ 处理，定理成立。$\square$

## 110. 终端算术分辨率与由操作参数控制的区分窗口

**定义 110.1（一般终端分辨率的 horizon）。** 固定 $H\ge2$ 和正因子 $d\mid H$，沿用定义 109.1 的全部实际源、字面后缀及 End/错误合同，只把成功输出换为定理 100.3、定义 104.4 的 $\eta_{H,d}$。对 $p^h\parallel H$，置 $e=v_p(d)$、$k=h-e$，令 $t=\min(v_p(x),h)$，其中模 $p^h$ 的零余数取 $t=h$。局部与全局标签为

$$
\eta_{p,h,e}(x)=
\begin{cases}
S(t,x/p^t\bmod p^k),&t<e,\\
D(x/p^e\bmod p^k),&t\ge e,
\end{cases}
\qquad
\eta_{H,d}(x)=\bigl(\eta_{p,h,e}(x)\bigr)_{p\mid H}.
$$

$S,D$ 是不同类型，$S$ 还记录深度；模 $1$ 的坐标是单点。各除法在可整除的整数代表上完成，再约化。用 $O_{H,d}(p,w)$ 记响应，定义

$$
h_\eta(H,d)=\min\left\{L\ge0:
\ \forall p,p',\quad
\bigl[\forall |w|\le L,\ O_{H,d}(p,w)=O_{H,d}(p',w)\bigr]
\Rightarrow
\bigl[\forall w\in\mathcal B^*,\ O_{H,d}(p,w)=O_{H,d}(p',w)\bigr]
\right\}.
$$

这里 $L$ 为整数，$p,p'$ 遍历两种初始化的全部实际前缀，所有 $w$ 都是共同字面窗口词。定理 106.7 保证最小值存在。$d=H$ 时标签与 gcd 输出单射互编码，故 $h_\eta(H,H)=h(H)$；$d=1$ 时为完整余数输出。若用 End 之后允许的算术操作解释标签，它代表的是**整个**算术响应族，而不是一次 $F_H$ 查询。此处只计 End 以前的窗口，不计查询次数、算术延续长度、运行时间或状态数，也不允许算术操作与窗口交错。

**引理 110.2（局部精度与一窗恢复）。** 局部标签相等蕴含余数模 $p^k$ 相等；若第一余数是高型 $D$，则蕴含两余数模 $p^h$ 完全相等。并且

$$
\eta_{p,h,e}(x)=\eta_{p,h,e}(0)
\quad\Longleftrightarrow\quad x\equiv0\pmod{p^h}.
$$

若两个实际前缀在全部至多一窗后缀上响应相等，则要么都为吸收态，要么结构标签相同，并且各局部算术三元组 $(r,u,v)$ 模 $p^k$ 相同。特别地，所有 $H\ge2$ 都有 $h_\eta(H,1)=1$；所有 $d\mid H$ 都有 $h_\eta(H,d)\ge1$。

证明。低型相等要求相同的 $t<e$ 以及 $x/p^t\equiv y/p^t\pmod{p^k}$，于是 $x-y$ 被 $p^{k+t}$ 整除，尤其被 $p^k$ 整除。第一源为高型时，标签相等迫使第二源也为高型，并给 $x/p^e\equiv y/p^e\pmod{p^k}$，所以 $x\equiv y\pmod{p^{e+k}}$。更换整数代表引入的差分别被 $p^{h-t}$、$p^{h-e}$ 整除，不影响所需商坐标。零余数是高型，故零标签纤维恰为模 $p^h$ 的零。$e=0$ 时所有标签都是高型并记录完整余数；$k=0$ 时粗同余为空条件，但高型本身已表示模 $p^h$ 为零，故完全相等及零纤维结论仍成立。

现在假设一窗内全部响应相等。$010$ 从任何活态都合法、末窗非零，在吸收态则恒错，因此先分出活态与吸收态。两个吸收态的全部未来已相等。对两个活态，空后缀的成功或报错确定 $E$；$100$ 在接缝 $0$ 成功、接缝 $1$ 非法，因此确定 $s$。这些区分与模数、过去长度以及具体余数无关。

把每个成功局部标签映到其确定的模 $p^k$ 余数。若 $E=1$，空后缀、$010$、$001$ 给出

$$
r,\quad r+v,\quad r+u+v\pmod{p^k},
$$

遂恢复 $r,v,u$；两个非空词都从任一接缝合法。若 $E=0$，活标签必为 $(0,0)$，三个成功词 $100,010,001$ 给出

$$
P=r+u,\quad Q=r+v,\quad T=r+u+v,
\qquad r=P+Q-T,\quad u=T-Q,\quad v=T-P.
$$

所以即使当前 End 报错，也无需查询当前余数就能恢复粗三元组。$k=0$ 时这一恢复仅为空同余，仍不遗漏任何结构区分。

$d=1$ 时所有因子上 $k=h$，CRT 给完整模 $H$ 的三元组相同。同结构标签与同算术坐标按定义 104.4 更新后始终相同，故 $h_\eta(H,1)\le1$。反向仍取定理 109.3 证明中的实际源 $(0,\text{空词})$ 和 $(1,[100])$：当前都报错，$010$ 只在前者成功。成功标签与 $\mathsf{err}$ 分离，对每个 $d$ 都适用，故 $h_\eta(H,d)\ge1$，并得 $d=1$ 的等号。$\square$

**命题 110.3（仅在 $p^e$ 取共同探针的局部上界）。** 若 $1\le e\le h$，则

$$
h_\eta(p^h,p^e)\le D_{00}(p^e)\le\ell(p^e),
$$

其中 $\ell$ 是定理 109.3 证明中重记的定理 106.3 长度界。这个界不依赖额外精度 $h-e$。

证明。置 $q=p^e$、$k=h-e$、$R=\mathbb Z/q\mathbb Z$。设两个实际前缀在长度至多 $D_{00}(q)\ge1$ 的全部共同后缀上局部响应相等。引理 110.2 处理了吸收态情形；其余情形有同一活标签，且三元组 $X=(r,u,v)$、$Y=(r',u',v')$ 模 $p^k$ 相同。因而有唯一的 $\delta\in R^3$，满足

$$
Y-X=p^k\delta\pmod{p^h}.
$$

这里乘 $p^k$ 是 $R$ 到模 $p^h$ 环中理想 $p^k(\mathbb Z/p^h\mathbb Z)$ 的同构，不是在环内除以非单位。$k=0$ 时就是直接取差。

把 $X$ 约化到 $R^3$，对每个满足 $r+Au+Bv=0$ 的 $(A,B)\in R^2$，取一个定义 106.1、定理 106.3 保证的 first-$00$ 共同词。其整数系数记为 $(C,D)$，只要求 $C\equiv A,D\equiv B\pmod q$。它在两边合法且末窗非零，包括两源当前 $E=0$ 的情形。第一终值 $r+Cu+Dv$ 被 $q=p^e$ 整除，故其标签为高型。由标签相等和引理 110.2，两个终值模 $p^h$ 完全相等，因而

$$
p^k(\delta_r+C\delta_u+D\delta_v)=0\pmod{p^h},
\qquad
\delta_r+A\delta_u+B\delta_v=0\quad\text{in }R.
$$

系数仅知模 $q$ 已足够：换 $C,D$ 的提升只使括号改变 $q$ 的倍数，原差改变 $p^kq=p^h$ 的倍数。第一源为高型也只要求模 $q$ 为零。因此并没有暗中使用模 $p^h$ 的短探针。

下面完整推出比例关系。在 $R^2$ 上令

$$
\lambda(A,B)=Au+Bv,\qquad
\mu(A,B)=A\delta_u+B\delta_v.
$$

实际行相邻 Fibonacci 互素，约化后仍是幺模行。在素幂局部环上至少一个坐标是单位：若 $u$ 是单位可取 $t_0=(u^{-1},0)$，否则 $v$ 是单位可取 $t_0=(0,v^{-1})$；都有 $\lambda(t_0)=1$。这是分裂满射，不使用域上的核维数论证。置 $z_0=-r t_0$。对每个 $z\in\ker\lambda$，$z_0,z_0+z$ 都属于上述仿射零集合；将它们代入差等式相减，得 $\mu(z)=0$。任意 $w\in R^2$ 有分解

$$
w=\lambda(w)t_0+\bigl(w-\lambda(w)t_0\bigr),
\qquad w-\lambda(w)t_0\in\ker\lambda.
$$

令 $b=\mu(t_0)$，则 $\mu(w)=b\lambda(w)$。代入两个标准基向量得到 $\delta_u=bu,\delta_v=bv$；再代入 $z_0$ 得 $\delta_r-br=0$。因此

$$
\delta=bX\quad\text{in }R^3.
$$

把 $b$ 任取提升至模 $p^h$，令 $a=1+p^kb$，遂有 $Y=aX\pmod{p^h}$ 和 $a\equiv1\pmod{p^k}$。提升之差被 $q$ 整除，不改变 $a$ 模 $p^h$。若 $k\ge1$，则 $a\equiv1\pmod p$，自动为单位。若 $k=0$，第二源的实际行也是幺模行；由 $(u',v')=a(u,v)$ 和某个 $\alpha u'+\beta v'=1$，得到 $a(\alpha u+\beta v)=1$，故 $a$ 仍为单位。

现在恰满足定理 104.7 的**充分方向**（亦即 §105 所用的共同单位缩放规则）：同结构标签，三个坐标共同乘单位 $a$，且 $a\equiv1\pmod{p^{h-e}}$。其线性更新与命题 104.5 的标签稳定子说明全部未来的 $\eta/\mathsf{err}$ 相等。这里只在有界模 $p^e$ 探针上证明所需关系，没有重证完整未来分类的必要方向。故局部上界成立。$\square$

**命题 110.4（一般分辨率的平衡相位下界）。** 若 $p^h\parallel H$、$e=v_p(d)\ge1$，记 $q=p^e$。对整数 $L\ge2$，若

$$
B_L+1<q-q/p,
$$

则 $h_\eta(H,d)>L$。特别地，$q\ge8\phi^{3L/2}$ 是充分条件。

证明。按命题 109.2 选同一个足够大的实际 $j$，满足 $j+1+\lfloor L/2\rfloor\equiv0\pmod{P(H)}$，且标签 $C$ 的区间长度 $F_{3j+1}\ge H$。因此仍可在一个实际相位实现任意两个全局余数。所有成功短词的贡献模 $q$ 构成 $V_L$，其大小至多 $B_L+1$，且包含空贡献。以下只补充一般标签所需的局部差异。

若 $e=h$，沿用命题 109.2 的两个缺失余数 $z_1,z_2$，取 $c_i=-z_i$ 模 $p^h$。每个成功短后缀后的两值非零且有相同深度 $t<h$。此时 $k=h-e=0$，低型单位坐标模 $1$ 为单点，故相同深度就是相同 $\eta$ 标签。

若 $1\le e<h$，从 $V_L$ 外选一个 $z\pmod q$，取任意提升 $c_1\pmod{p^h}$ 满足 $c_1\equiv-z\pmod q$，再置

$$
c_2=c_1+p^{h-1}\pmod{p^h}.
$$

两者不同模 $p^h$，但因 $h-1\ge e$ 而相同模 $q$。对每个成功短词，终值均非零模 $q$，所以有共同深度 $t<e$。还必须核对低型单位，不能只核对 gcd：除以 $p^t$ 后，二者的差被

$$
p^{h-1-t},\qquad h-1-t\ge h-e=k
$$

整除，故单位坐标模 $p^k$ 相同。即使 $t=e-1$，指数正好等于 $k$，也足够；换代表额外引入的 $p^{h-t}$ 倍数同样消失。于是所有成功短词的完整局部 $S$ 标签相等。

两种情形均由 CRT 取全局余数 $R_1,R_2$，在选定 $p^h$ 轴分别为 $c_1,c_2$，在其它完整素幂轴取相同余数。一个共同的 $I_j(C)$ 实现两者为实际正前缀，实际下一行相同。选定轴的短标签刚已核对，其它轴的短终值相同；标签相同也同步所有接缝错误、末零窗错误。全局短响应包括空词全部相等。

为区分完整未来，只在选定轴模 $p^h$ 取系数消去 $c_1$：幺模行给 $Au+Bv=-c_1$，定理 106.3 给某个有限 first-$00$ 共同探针，末窗非零。两边成功 End，选定轴的终值为 $0$ 与 $c_2-c_1\ne0$。引理 110.2 的零纤维结论给不同标签，故全局元组不同。此探针只证明最终能够区分，不要求它短于 $L$；两个实际总值都为正。由此 $h_\eta(H,d)>L$。最后套用定理 109.3 证明中的 $B_L+2\le4\phi^{3L/2}$，得到所述充分条件。$\square$

**定理 110.5（操作参数决定的统一对数阶）。** 对全部 $H\ge2$、$d\mid H$，有 $h_\eta(H,1)=1$。若 $d\ge2$，令 $Q=Q(d)=\max_{p\mid d}p^{v_p(d)}$，则

$$
\frac23\log_\phi Q-4<h_\eta(H,d)<\frac23\log_\phi Q+3.
$$

更具体地，常数可取

$$
C_-=1+\frac23\log_\phi8<4,\qquad
C_+=\frac{5+\log_\phi(9/2)}3<3,
$$

且 $\frac23\log_\phi Q-C_-<h_\eta(H,d)\le U(Q)<\frac23\log_\phi Q+C_+$。这些常数与 $H,d,H/d$、素因子个数和过去长度都无关。

证明。$d=1$ 已由引理 110.2 证明，不定义 $Q(1)$。对 $d\ge2$，将一个全局实际前缀逐轴投影至 $p^h\parallel H$，始终保留同一初始化与同一字面前缀，算术约化与窗口递推交换。对每一个共同字面后缀，各轴与全局的合法性、吸收态和 End 成功性同步；成功全局标签恰为各局部标签的元组。

置

$$
L_* =\max\bigl(1,\ \max_{p\mid d}\ell(p^{v_p(d)})\bigr).
$$

若一对全局源在全部至多 $L_*$ 窗的后缀上响应相等，成功元组可逐轴投影，错误则同步处理。$e=0$ 的轴由引理 110.2 一窗恢复完整三元组；$e\ge1$ 的轴由命题 110.3 得完整未来相等。现固定任意一个全局字面后缀，将各轴对这个**同一词**的等式重新组成成功元组，或同步的 $\mathsf{err}$，就得到全局完整未来相等。因此

$$
h_\eta(H,d)\le L_*\le U(Q).
$$

后一不等式用 $\ell(n)\le U(n)$、$U$ 不减及 $U(Q)\ge1$。这是直接的同源元组论证；没有把 gcd 专用的乘积公式替换成一般标签公式，也没有假定自由局部相位或拼接各轴分别选择的词。定理 109.3 已证明 $U(Q)<\frac23\log_\phi Q+C_+$。

下界保留命题 110.4 的 $L\ge2$ 范围。置 $t=\frac23\log_\phi Q$、$a_0=\frac23\log_\phi8$。若 $t-a_0\ge2$，取 $L=\lfloor t-a_0\rfloor\ge2$。最大完整素幂 $Q$ 满足 $Q\ge8\phi^{3L/2}$，故 $h_\eta(H,d)\ge L+1>t-a_0>t-(a_0+1)$。若 $t-a_0<2$，引理 110.2 给

$$
h_\eta(H,d)\ge1>t-(a_0+1).
$$

这处理了所有小 $Q$，没有使用未陈述的 $L=0,1$ 一般下界。由 $a_0<3$ 得 $C_-<4$，而 $C_+<3$ 已证。$d=H$ 时还可单独使用定理 109.3 的更强端点下界；一般情形的证明并非从粗 gcd horizon 或读出细化的单调性推得。$\square$

**命题 110.6（相同 $Q(d)$ 的有限反例与数值边界）。** 在定义 110.1 的实际源合同下，有限分区给出

$$
h_\eta(2,2)=1,\qquad h_\eta(4,2)=2.
$$

两者的 $Q(d)$ 都为 $2$，所以精确 horizon 不是 $Q(d)$ 单独的函数。定理 110.5 的统一加性误差界与此相容。

证明。取模 $H$ 的实际三步行轨道 $\mathcal O_H$，对状态集 $\{\bot\}\sqcup(\mathcal T\times\mathbb Z/H\mathbb Z\times\mathcal O_H)$ 使用定义 104.4 的五个转移和本节的终端标签。它恰为实际源的像：实际运行只取这些行；反向对任一轨道相位取任意大的同相位 $j$，由引理 105.1 的三段区间长度最终都至少为 $H$，每个标签与余数都被实际前缀实现，且两种初始化都允许。吸收态由 $(1,[100])$ 达到。这里的反向包含来自区间证明，不能仅由转移闭合推出。

从终端输出分区 $P_0$ 起，用引理 107.4 的旧类加五个后继类递推，有限数据如下；末项重复稳定分区。

| $(H,d)$ | 实际行周期 | 所列状态数 | $|P_0|,|P_1|,\ldots$ | 第一次 $P_L=P_{L+1}$ |
|---|---:|---:|---|---:|
| $(2,2)$ | 1 | 7 | $3,7,7$ | 1 |
| $(4,2)$ | 2 | 25 | $4,21,25,25$ | 2 |

完整分区相等给全部未来相等，先前的严格细化则给此前预算不足的状态对。每个所列状态都实际可达，所以同时得到实际 horizon 的上下界。[有限补充数据](../../reports/fib-resolution-horizon/results.json) 保留了这些任务和全部固定范围任务的逐层类数与分区指纹；其精确有限解释见[补充说明](../../reports/fib-resolution-horizon/README.md)。数值证据只覆盖 $2\le H\le40$ 的全部 $d\mid H$ 及 $H=64,128$ 的 $d=1,2,4,8$，共 165 个任务；其中 $h(23)=5$ 也仅以该有限枚举给出。有限测量不推出所有模数的定理或最优加性常数；任意模数的统一界由前述普通证明承担。$\square$

## 追加锚（本行以下为增补区）

## 111. 无穷多个严格稳定的自匹配配置

**定义 111.1（规范端点、全部同价层与稳定胞腔）。** 本节沿用定义 85.1、命题 85.2 及定义 98.1 的全体正整数价格目标。所有对数为自然对数，$p$ 遍历普通素数，$k\ge1$ 为整数；记

$$
\lambda(x)=\frac1{x\log x}\quad(x>1),\qquad
G_p(a)=\sum_{j=0}^a p^{-j},\qquad
r_{p,k}=\frac{\log(G_p(k)/G_p(k-1))}{\log p}.
$$

把第 98 节的 $\mathcal A$ 明记为排除全部等价层的 $A^-$，并引入包含全部等价层的 $A^+$：

$$
\begin{aligned}
A^-(x)&=\sum_{r_{p,k}>\lambda(x)}\log p=\log N^-(x),\\
A^+(x)&=\sum_{r_{p,k}\ge\lambda(x)}\log p=\log N^+(x).
\end{aligned}
$$

对应的 $N^\pm$ 取各素数轴的指数前缀。压力始终是

$$
S(\lambda)=\max_{n\ge1}\left\{\log\frac{\sigma(n)}n-\lambda\log n\right\}.
$$

这里没有 $n>5040$ 的限制。命题 85.2 的有限正层结论及逐轴严格边际递减，保证 $N^-$ 是最小的数值最优者；没有等价层时，它是唯一数值最优者。

由于 $\lambda$ 在 $(1,\infty)$ 上连续严格递减，值域为 $(0,\infty)$，每一层有唯一激活尺度 $\tau_{p,k}$，满足 $\lambda(\tau_{p,k})=r_{p,k}$。记不同激活尺度的集合为 $\mathcal E$，其补集的连通分量称为稳定胞腔。命题 98.2 已给出局部有限性；具体地，对固定 $y>1$，所有在 $x\le y$ 活跃或同价的层都在有限集合

$$
L_y=\{(p,k):r_{p,k}\ge\lambda(y)\}
$$

中，因为已有的边际界给 $p^k\log p<y\log y$。在实际事件 $\tau\in\mathcal E$ 处，令

$$
E_\tau=\{(p,k):r_{p,k}=\lambda(\tau)\},\qquad
J_\tau=\sum_{(p,k)\in E_\tau}\log p>0.
$$

同一素数不能同时有两层同价，不同素数的同价不予排除。$A^-$ 左连续，$A^+$ 是它的右极限；在事件处有

$$
A^+(\tau)=A^-(\tau)+J_\tau.
$$

这是一整个同时激活层集的总跳跃。非事件处 $A^-=A^+$，并在所在胞腔内为常数。称 $z>1$ 为严格稳定自匹配根，若 $z\notin\mathcal E$ 且 $A^-(z)=z$；这正是定理 98.3 的严格自匹配条件。下文在稳定点也简写 $A=A^-=A^+$。

**命题 111.2（已有尺度与 Littlewood 振荡给出无界双侧符号）。** 规范规模满足

$$
\limsup_{x\to\infty}\frac{A^-(x)-x}{\sqrt x}=+\infty,\qquad
\liminf_{x\to\infty}\frac{A^-(x)-x}{\sqrt x}=-\infty.
$$

尤其，对任意实数 $H$，都有稳定点 $u>H$ 满足 $A(u)>u$，也有稳定点 $v>H$ 满足 $A(v)<v$。

证明。先明确所复用的尺度公式的适用域。[ZECKENDORF_EULER_5040.md](ZECKENDORF_EULER_5040.md) 的定义 7.1、定理 8.1 及式（19）—（24）已经给出最小端点最优者的尺度分解。该处较早的压力排除了 $n\le5040$，只有在

$$
0<\lambda<\lambda_c:=\frac{\log(12/11)}{\log11}
$$

时，式（19）才把受限压力与无约束压力识别起来。因为 $\lambda(x)\to0$，本节的 $x$ 最终满足这个条件；此时最小端点最优者就是定义 111.1 的 $N^-(x)$。因此可直接使用那里已证的

$$
A^-(x)=\psi(x)+(\sqrt2-1)\sqrt x+o(\sqrt x),\qquad
\psi(x)=\sum_{p^j\le x}\log p.
$$

旧定理同时控制了所有 $k\ge3$ 层的总量为 $O(x^{1/3}(\log x)^{7/3})=o(\sqrt x)$；这里不把固定层的渐近擅自求无限和，也不重新建立该尺度定理。其严格端点约定已包括事件点，本证明不需要另设 $A^+$ 的渐近公式。

外部解析输入是 Littlewood 的无条件结论

$$
\psi(x)-x=\Omega_\pm\bigl(\sqrt x\,\log\log\log x\bigr).
$$

本处引用的具体文本是 D. J. Platt 与 Tim Trudgian，*On the first sign change of $\theta(x)-x$*，*Mathematics of Computation* **85**(299) (2016), 1539–1547，[DOI: 10.1090/mcom/3021](https://doi.org/10.1090/mcom/3021) 的[作者手稿 arXiv:1407.1914v1](https://arxiv.org/pdf/1407.1914v1)，引言第 1 页式（2）的第二行。该行直接陈述的是 $\psi$ 的上述双侧振荡，没有 RH 假设。它是这里实际采用的二手定理来源；Littlewood 原文以及该手稿所引 Ingham 定理 34、35 的原始定理页未在此核读，不把手稿转述冒充对原始证明的核验。该论文后文的数值符号范围不是本证明的前提。

写 $L(x)=\log\log\log x$；在充分大的实数上 $L(x)\to\infty$。上述 $\Omega_\pm$ 的含义是：存在常数 $c_+,c_->0$ 及趋于无穷的两列样本，使得分别有

$$
\psi(x)-x\ge c_+\sqrt x\,L(x),\qquad
\psi(x)-x\le-c_-\sqrt x\,L(x).
$$

将已有尺度式写成 $A^-(x)-x=\psi(x)-x+\sqrt x(\sqrt2-1+\varepsilon(x))$，其中 $\varepsilon(x)\to0$。在正样本列上，除以 $\sqrt x$ 后的下界为 $c_+L(x)+\sqrt2-1+\varepsilon(x)\to+\infty$；在负样本列上的上界为 $-c_-L(x)+\sqrt2-1+\varepsilon(x)\to-\infty$。这证明两个极限断言。

还须把严格符号样本移到稳定点。若样本 $t$ 本来稳定，无需移动。若 $t\in\mathcal E$，局部有限性给出一个无其他事件的左邻区间，且其常值为 $A^-(t)$。记 $d=A^-(t)-t\ne0$，在该区间取 $t-h$，其中 $0<h<|d|/2$，则

$$
A(t-h)-(t-h)=d+h
$$

与 $d$ 同号。可再令 $h<1$，并小到保留所需的 $t-h>H$。因原样本任意高，稳定的两种符号样本仍各自无界。这一步只转移严格符号，不需要排除事件相等或控制所有事件的跳幅。$\square$

**引理 111.3（正跳阶梯的严格向下穿零）。** 设 $u<v$ 是定义 111.1 的稳定点，且

$$
A(u)-u>0,\qquad A(v)-v<0.
$$

则存在 $z\in(u,v)\setminus\mathcal E$，使 $A(z)=z$。它位于稳定胞腔内部，$A(x)-x$ 在它的充分小左邻域为正、右邻域为负。

证明。$[u,v]$ 内只有有限个事件，按不同尺度排列为 $\tau_1<\cdots<\tau_m$。若 $m=0$，整个区间上的 $A$ 为同一常数 $c$；两端符号给 $u<c<v$，取 $z=c$ 即可。一般情形在相邻事件之间仍有 $A(x)-x=c_i-x$，斜率严格为 $-1$。

反设所有这些开区间内都没有零点。第一片从 $u$ 的正值出发，连续仿射函数若在到达其右端点前变为非正，便已在内部过零；故它在整片上保持正，其右端的左极限至少为零。在事件 $\tau_i$ 处，若左极限为 $d_i\ge0$，则右极限为 $d_i+J_{\tau_i}>0$。下一片因而也从严格正值出发；在没有内部零点的反设下，它一直为正，下一事件的左极限仍至少为零。沿有限事件列归纳，最后一片从严格正值出发，却须在稳定点 $v$ 取得负值，仿射函数必在这片内部过零，矛盾。所得零点在开片内，且由斜率 $-1$ 自动有所述左右符号。

两个事件端点的零值不能替代这一步。记事件两侧规模为 $a=A^-(\tau)$、$b=A^+(\tau)=a+J_\tau$。若左端约定给 $a-\tau=0$，则紧靠事件左侧的值为正，而右极限是 $J_\tau>0$；这个规范端点零尚未完成向负值的穿越。若右极限给 $b-\tau=0$，则左极限为 $-J_\tau<0$，紧靠事件左侧已经为负，不可能是沿正片推进时的第一次向下穿越。若 $a-\tau<0<b-\tau$，事件只向上跳。两侧都严格同号时也没有向下穿零。因此反设归纳没有遗漏任何端点情形。

若最初给出的符号读数采用含同价层的右端约定，也可先变成稳定样本：在事件右侧取 $\tau+h$，其符号值为 $A^+(\tau)-\tau-h$，选择小于非零绝对值一半的 $h$ 即保号。左端约定的移动已在命题 111.2 处理。全部同时激活层只通过严格正的总量 $J_\tau$ 进入证明，无需假定不同素数的事件互异。$\square$

**定理 111.4（严格自匹配根的无穷供给与真整除链）。** 存在严格递增且趋于无穷的严格稳定自匹配根列 $z_j$，及有限素数配置 $N_j=N^-(z_j)$，满足

$$
z_j=A(z_j)=\log N_j,\qquad
N_j\mid N_{j+1},\quad N_j\ne N_{j+1}.
$$

每个 $N_j$ 是价格 $\lambda(z_j)$ 下全体正整数中的唯一数值最优者；最终有 $5040\mid N_j$ 且 $N_j>5040$。

证明。由命题 111.2，任意给定高度以上都可选稳定正样本，再在它以上选稳定负样本。递归取

$$
u_j<v_j<u_{j+1},\qquad u_j>j,\qquad
A(u_j)>u_j,\quad A(v_j)<v_j.
$$

引理 111.3 在每个开区间 $(u_j,v_j)$ 内给出一个严格稳定根 $z_j$。各区间有序且互不相交，故 $z_j$ 严格递增，并因 $z_j>j$ 而趋于无穷。这一选择可从任何指定高度以上开始。

每个 $z_j$ 上的活跃层集有限，且无等价层，故它给出有限整数 $N_j$。对于任意正整数 $n=\prod_p p^{b_p}$，既有正部公式的逐层表达为

$$
\log\frac{\sigma(n)}n-\lambda\log n
=\sum_p\sum_{k=1}^{b_p}(r_{p,k}-\lambda)\log p.
$$

在 $\lambda=\lambda(z_j)$ 时，所取前缀包含全部正项而不含任何负项。任何不同指数向量必遗漏至少一个严格正项或加入至少一个严格负项，因而目标严格变小。这复用定义 85.1 及定理 98.3 的唯一性判据，证明唯一数值最优性。所称唯一性是整数值及其素因子指数配置的唯一性，不是来源编码或语法树的唯一性。

由于 $z_{j+1}>z_j$，有 $\lambda(z_{j+1})<\lambda(z_j)$，先前活跃的每一层仍活跃；于是每个素数的指数不减，$N_j\mid N_{j+1}$。又 $\log N_{j+1}=z_{j+1}>z_j=\log N_j$，两者不同，所以整除是严格的。

最后复用第 76 节的价格 $1/25$ 最优者及第 98.6、99.1 条所用的八个严格有益层：$5040=2^4 3^2 5\cdot7$ 的四个 $2$ 层、两个 $3$ 层、一个 $5$ 层及一个 $7$ 层，在价格 $1/25$ 时都严格活跃。因 $\lambda(z_j)\to0$，最终 $\lambda(z_j)<1/25$，这八层全部保留，故 $5040\mid N_j$。同时 $N_j=e^{z_j}\to\infty$，最终 $N_j>5040$。这只说明所构造最优配置链的性质，不把任意正整数限制为 $5040$ 的倍数。$\square$

**推论 111.5（无穷多个 Robin 临界谷底及其未决符号）。** 定理 111.4 的每个 $z_j$ 都是第 98 节完整裕度 $\mathfrak D$ 的严格局部极小点，而且

$$
\begin{aligned}
\mathfrak D(z_j)
&=\gamma+\log\log z_j-\log\frac{\sigma(N_j)}{N_j}\\
&=\log\left(\frac{e^\gamma N_j\log\log N_j}{\sigma(N_j)}\right)
\longrightarrow0.
\end{aligned}
$$

特别地，$\sigma(N_j)/(e^\gamma N_j\log\log N_j)\to1$。

证明。$z_j$ 位于稳定胞腔内部且 $A(z_j)=z_j$，故直接应用定理 98.3，得到严格局部极小及 $\mathfrak D''(z_j)=w(z_j)>0$。同一定理给出根处的裕度表达；将 $z_j=\log N_j$ 代入，得到所写对数比值。定理 98.4 已无条件给出 $\mathfrak D(x)\to0$，沿 $z_j\to\infty$ 即得结论，再对 $-\mathfrak D(z_j)$ 取指数。$\square$

这里的来源分工是：尺度分解来自旧卷定理 8.1，完整裕度分解 $\mathfrak D=\Phi+R$ 来自定理 87.3，储备尾与主项来自定理 93.1—93.2，压力尾积分亦已有旧卷引理 9.1、定理 9.2；局部极小与趋零来自定理 98.3—98.4。本节接上的推导是 Littlewood 双侧符号到稳定向下穿零，再到无穷配置链。局部极小和趋零均未决定 $\mathfrak D(z_j)$ 的符号；所有所需自匹配配置的裕度严格为正仍是未解决问题，正的储备主项不能单独替代同尺度的有符号尾项。上述存在证明不给有效的首根尺度、根间隔、密度或计数渐近式。

## 112. 有限价格迭代、同价绕越与严格根的有限证书

**定义 112.1（从任意实数开始的规范价格迭代）。** 固定一个已给定的严格稳定根 $z_*>1$，即 $A^-(z_*)=A^+(z_*)=z_*$。对任意实数 $x_0\ge z_*$，考虑

$$
x_{n+1}=A^-(x_n),\qquad n\ge0.
$$

这里尚未把任意实数规定为可计算输入；下述有限终止先是经典实数命题。序列始终位于 $x>1$ 的合法域这一点，由下一定理的不变区间证明承担，不能从递推式本身省去。

**定理 112.2（不变区间上的有限规范迭代）。** 对定义 112.1 的每个实数初值，轨道有限步停在规范固定点 $q\ge z_*$。更确切地，取任意 $y>x_0$ 满足 $A^-(y)<y$，令

$$
I=[z_*,y],\qquad S=\{x_0\}\cup A^-(I),\qquad M=|S|.
$$

则 $I$ 对 $A^-$ 不变，$S$ 有限，且第一次满足 $x_{K+1}=x_K$ 的指标满足

$$
0\le K\le M-1\le |L_y|+1.
$$

全部 $n\ge K$ 都有 $x_n=q=x_K$。初次比较 $x_0\le A^-(x_0)$ 或 $A^-(x_0)\le x_0$，分别决定全轨道不减或不增；初次相等时 $K=0$。

证明。命题 111.2 提供任意高的负符号样本，故可选所需 $y$。$y$ 稳定与否不影响证明。$x$ 增大时 $\lambda(x)$ 严格下降，严格活跃层只增不减，故 $A^-$ 单调不减。对每个 $t\in I$，

$$
z_*=A^-(z_*)\le A^-(t)\le A^-(y)<y.
$$

所以 $A^-(I)\subseteq I$；由归纳，全部迭代有定义且位于 $I$。尤其不会落到 $1$ 以下使下一步价格失去定义。

若 $x_0\le x_1$，对不等式应用 $A^-$ 得 $x_1\le x_2$，归纳得到 $x_n\le x_{n+1}$。若 $x_1\le x_0$，同理得到反向的全部相邻不等式。这里不需要在整个 $I$ 上有 $t\le A^-(t)$ 或 $A^-(t)\le t$。这正对应既有 `Monotone.monotone_iterate_of_le_map` 与 `Monotone.antitone_iterate_of_map_le`：在不变区间的子类型上，以限制后的映射及初值代入即可。

对 $t\in I$，每个活跃层属于定义 111.1 的有限集合 $L_y$。记其活跃子集为 $P_t$，则 $A^-(t)=\sum_{P_t}\log p$。这些子集随 $t$ 增大而嵌套；任何一次真包含至少增加一个层。因此不同子集至多有 $|L_y|+1$ 个，不同像值也至多有这么多。事件上排除全部同价层仍是这个嵌套链中的一个子集，故端点没有产生额外的无限值族。于是

$$
|A^-(I)|\le |L_y|+1,\qquad 1\le M\le |L_y|+2,
$$

而全轨道在有限集 $S$ 内。

此时可以直接应用已有的[有限有序迭代定理](../../../D5/S1/FixedPoints/FiniteMonotoneTermination.lean) `finite_monotone_iteration_reaches_fixed_point`。它的实际假设是：有限偏序类型、一个保序自映射、初值，以及对该类型每个状态都成立的“更新值不大于状态”。为逐项满足这些假设，取实际轨道子类型

$$
\mathcal O=\{x_n:n\in\mathbb N\}\subseteq S.
$$

它在尚未使用终止结论之前已经有限，且更新把 $x_n$ 送到 $x_{n+1}$，因而对 $\mathcal O$ 封闭。在下降情形，使用从实数继承的偏序；对任意状态 $s=x_n$，有 $A^-(s)=x_{n+1}\le x_n=s$。在上升情形，使用 $\mathcal O$ 的反序 `OrderDual`；把定义域和值域同时反序仍保序，而 $x_n\le x_{n+1}$ 恰好成为反序中的更新值不大于状态。初值是 $x_0\in\mathcal O$。这就是既有定理所需的全部代入，它给出一个固定阶段及其后的恒定性。不能直接把整个 $S$ 当作该定理的类型而忽略逐状态更新方向的核对；方向已在实际轨道上得到。

指标界可在同一有限轨道上直接计数。第一次相邻相等之前，每一步都严格沿已定方向移动，否则相等经确定性的同一映射传播，以后全相等。因此若前 $M$ 次相邻比较都不相等，$x_0,\ldots,x_M$ 就是 $S$ 中 $M+1$ 个不同元素，矛盾。故第一次相等的指标 $K\le M-1$，再用 $M\le |L_y|+2$ 得所述界。这个数是相对于选定上屏障 $y$ 的状态数上界，不是位运算、精度或实际耗时界。$\square$

**命题 112.3（全域极值性质与严格下降的终点）。** 若定理 112.2 的轨道不减，则其终点是整个定义域 $(1,\infty)$ 中不小于 $x_0$ 的最小规范固定点。若轨道不增，则其终点是不大于 $x_0$ 的最大规范固定点。若首步严格下降 $A^-(x_0)<x_0$，终点还是严格稳定根；首步上升或初值已固定时，仅凭这些条件不能排除事件处的弱固定点。

证明。设轨道不减，$t>1$ 是任意满足 $t\ge x_0$ 且 $A^-(t)=t$ 的点。由归纳，$x_n\le t$ 推出 $x_{n+1}=A^-(x_n)\le A^-(t)=t$，故终点 $q\le t$。同时 $q\ge x_0$，证明其最小性。这里 $t$ 无须属于所选 $I$；结论是全域的。下降情形对任意 $1<t\le x_0$ 的规范固定点作同样归纳，得到 $t\le x_n$，因而 $t\le q\le x_0$，证明全域最大性。

现在设首步严格下降。第一次固定指标 $K\ge1$，且 $x_{K-1}>q=x_K$。若 $q$ 为事件，则 $A^-(q)=q$ 与总跳跃严格正给

$$
A^+(q)=q+J_q>q.
$$

对任意 $t>q$，在 $q$ 已经活跃或同价的每一层，在 $t$ 都严格活跃，因为 $\lambda(t)<\lambda(q)$。所以

$$
A^-(t)\ge A^+(q)>q.
$$

代入 $t=x_{K-1}$，与 $A^-(x_{K-1})=x_K=q$ 矛盾。故 $q$ 非事件，局部有限性使它处于稳定胞腔内部，成为严格稳定根。对从下方到达的轨道，这个“不能从上方落到事件”的论证不适用；初值若已在事件上固定，也没有严格下降的最后一步。$\square$

**命题 112.4（同时同价的离散选择与非算术弱停点）。** 在事件 $\tau$ 处，记 $a=A^-(\tau)$、$b=A^+(\tau)=a+J_\tau$。规范固定点要求 $\tau=a$，包含全部同价层的固定点要求 $\tau=b$。一般同价最优配置是从 $E_\tau$ 中选择实际子集 $U$，其自匹配条件恰为

$$
\tau=a+\sum_{(p,k)\in U}\log p.
$$

因此 $a\le\tau\le b$ 只是必要条件，不能代替同价层的子集和条件。并且，单调、局部有限、正跳跃、无界双侧符号及严格下方根这些抽象条件，并不蕴含所有上升规范轨道都停在严格根。

证明。所有严格有益层必须取，所有严格无益层不能取，零收益层可以选或不选。逐轴边际严格递减保证同一素数最多有一个零收益层，且其更低层已严格有益，故选择任何 $U\subseteq E_\tau$ 都仍是合法指数前缀。由唯一分解，它的对数规模正是所写子集和。自匹配要求这个离散规模恰好等于 $\tau$；虽然全部子集和落在 $[a,b]$，却不能把它们当作整个连续区间。特别地，空集与全集给出两种端点固定条件，而 $J_\tau>0$ 使两个端点不能同时等于 $\tau$。

以下是一个明确的**非算术**阶梯反例。对 $x>1$ 定义左连续映射

$$
C^-(x)=
\begin{cases}
2,&1<x\le3,\\
4m,&4m-1<x\le4m,\quad m\ge1,\\
4m+2,&4m<x\le4m+3,\quad m\ge1,
\end{cases}
$$

并令 $C^+$ 为其右极限。这些区间按序无缝覆盖 $(1,\infty)$，相邻常值每次上跳 $2$；事件为 $4m-1$、$4m$，局部有限。$C^-$ 单调不减、左连续，其严格稳定根恰为 $2,6,10,\ldots$：$2$ 在第一片内部，每个 $4m+2$ 在 $(4m,4m+3)$ 内部，而常值 $4m$ 只在右端事件 $x=4m$ 等于横坐标。对每个 $m\ge1$，稳定点 $4m+1/2$ 给正差 $3/2$，稳定点 $4m+5/2$ 给负差 $-1/2$，故两种符号都无界。

然而从 $x_0=7/2\ge2$ 出发，有

$$
\frac72\longmapsto4\longmapsto4,\qquad
C^-(4)=4,\quad C^+(4)=6.
$$

这是上升后停在事件的弱固定点，反驳了上述抽象的“普遍严格上升收敛”推断。它不是素数层的算术实例。对实际素数层，在 $z=\log N>1$ 处同价须满足形如

$$
\log\frac{G_p(k)}{G_p(k-1)}\,\log N\,\log\log N=\log p
$$

的等式以及其余最优阈值条件；这里既没有展示这种算术自匹配同价实例，也没有证明它们全部不存在。$\square$

**定理 112.5（绕过同价弱停点的单调更新）。** 定义

$$
B(x)=
\begin{cases}
A^+(x),&A^-(x)=x,\\
A^-(x),&A^-(x)\ne x.
\end{cases}
$$

则 $B$ 单调不减，$A^-(x)\le B(x)\le A^+(x)$，其固定点恰为原规范映射的严格稳定根。从任意实数 $x_0\ge z_*$ 开始的 $B$ 迭代有限步停在这样的根。对任意目标高度 $H$，可选择正符号种子 $u>\max(H,z_*)$，使从 $u$ 开始的 $B$ 轨道不减并停在严格根 $q>H$。

证明。先证强于各自单调性的交错不等式。若 $s<t$，在 $s$ 被 $A^+$ 包含的每层满足 $r_{p,k}\ge\lambda(s)>\lambda(t)$，因而被 $A^-(t)$ 包含。逐项权重为正，故

$$
A^+(s)\le A^-(t).
$$

由定义中的两种选择均位于 $[A^-,A^+]$，得到

$$
B(s)\le A^+(s)\le A^-(t)\le B(t),
$$

所以 $B$ 单调不减。又 $z_*$ 严格，故 $B(z_*)=z_*$。取命题 111.2 的任意 $y>x_0$，使 $A^-(y)<y$。此时条件分支必取 $B(y)=A^-(y)<y$，即使 $y$ 是事件也成立。于是对 $t\in[z_*,y]$，

$$
z_*=B(z_*)\le B(t)\le B(y)<y,
$$

同一区间仍不变。每个 $B(t)$ 选取的是 $L_y$ 的一个子集，或排除全部同价层，或包含全部同价层。对 $s<t$，所选子集仍嵌套，故像集有限，至多 $|L_y|+1$ 个。按定理 112.2 的同一有限轨道代入，下降用继承序、上升用反序，既有有限迭代定理给出有限固定阶段；状态数界也以 $\{x_0\}\cup B([z_*,y])$ 原样成立。

检查固定点时必须包含全部同时同价层。若 $x\in\mathcal E$ 且 $A^-(x)=x$，则

$$
B(x)=A^+(x)=x+J_x>x.
$$

若 $x\in\mathcal E$ 且 $A^-(x)\ne x$，则 $B(x)=A^-(x)\ne x$。因此事件处没有 $B$ 固定点。非事件处两种规模相同，$B(x)=x$ 恰好等价于 $A^-(x)=x$，即严格稳定根。这同时证明每个终点是原映射的严格根，而不是另造的固定点概念。

最后由命题 111.2 取稳定 $u>\max(H,z_*)$，使 $A(u)>u$。此时 $B(u)=A^-(u)>u$，故全轨道不减；上述有限终止给严格根 $q\ge B(u)>u>H$。这个构造是经典实数更新公式，其分支条件尚未提供可计算的实数相等判定器。$\square$

**命题 112.6（一个整数候选的有限严格证书）。** 给定整数 $N\ge3$，精确分解为 $N=\prod_p p^{a_p}$，置

$$
z=\log N>1,\qquad \lambda_z=\frac1{z\log z}.
$$

选择一个有认证上界保证的整数 $C>z$。如下有限组严格不等式足以证明 $N=N^-(z)=N^+(z)$、$z=A(z)$，并证明 $z$ 是严格稳定根：

$$
\begin{aligned}
\lambda_z&<r_{p,a_p}&&\text{对每个实际素因子 }p\mid N,\\
r_{p,a_p+1}&<\lambda_z&&\text{对每个素数 }p<C.
\end{aligned}
$$

第二行对未整除 $N$ 的素数取 $a_p=0$。第一行包含所有实际素因子，即使某个 $p\ge C$ 也不能省略。

证明。对 $p\ge C$ 和每个 $k\ge1$，已有边际界与 $t\log t$ 在 $t>1$ 上严格递增给

$$
r_{p,k}\le\frac1{p^k\log p}
\le\frac1{p\log p}
<\frac1{z\log z}=\lambda_z.
$$

所以这些整条素数轴都严格无益。这还表明：若候选实际含有 $p\ge C$，第一行必不能成立；检查全部实际素因子正是为了防止把这种不合法的已取层漏掉。

对每个 $p<C$，若 $a_p>0$，第一行及同轴边际严格递减说明 $1\le k\le a_p$ 的各层都严格有益；第二行及同一递减性说明 $k\ge a_p+1$ 的各层都严格无益。若 $a_p=0$，第二行从首层起排除整条轴。结合尾部 $p\ge C$ 的结论，全部素数的全部层都已分类，没有同价层；严格正层恰为 $N$ 的指数前缀。定义 85.1 的正部最优性因此给出全体正整数上的唯一数值最优者 $N$，而 $A(z)=\log N=z$。

为确认“严格稳定”而不只是逐点无等价层，复用命题 98.2 的局部有限性：在 $z$ 的一个紧邻域中，可能活跃或同价的层只有有限个。它们在 $z$ 的比较全部严格，可共同缩小邻域，使每个比较保持原符号；其余层在整个原邻域均不活跃。故所得根位于稳定胞腔内部。反向地，任何严格稳定根 $z=\log N$ 对每个 $C>z$ 都满足上述有限比较，所以这套证书没有遗漏严格根。$\square$

**定理 112.7（公平交错的严格根取得与共尾子列）。** 若目标 $H$ 以带已知误差界的可计算 Cauchy 名给定，则存在不使用实数相等判定器的搜索过程，有限步输出一个严格稳定根的整数 $N$ 及命题 112.6 的有限严格证书，并保证 $\log N>H$。若目标是任意实数，则给出其认证有限上界也足够；给出 Cauchy 预言机时同一结论相对于该预言机成立。反复选择认证整数新目标 $H_j>\log N_j+1$，可取得严格递增且趋于无穷的根子列；首次完成的证书不保证对应最小的下一个根。

证明。首先说明证书中的实数比较为何可半判定。正有理数 $t$ 的对数可以用有理包络计算。例如令 $v=(t-1)/(t+1)$，则 $|v|<1$，且

$$
\log t=2\sum_{j=0}^{m}\frac{v^{2j+1}}{2j+1}+R_m,
\qquad
|R_m|\le
\frac{2|v|^{2m+3}}{(2m+3)(1-v^2)}.
$$

这是对 $2\sum_{j\ge0}v^{2j+1}/(2j+1)$ 的尾项取绝对值，再用几何级数所得的显式有理误差；它随 $m\to\infty$ 趋零。因而 $\log N$、$\log p$ 及有理数 $G_p(k)/G_p(k-1)$ 的对数均有任意精度的有理包络。对 $z>1$，先取得落在 $(1,\infty)$ 内的 $z$ 包络，再用对数的连续单调性计算 $\log z$ 的包络；对正分母作有理区间除法，即得 $\lambda_z$ 及各 $r_{p,k}$ 的包络，误差可以趋零。

因此每个真正严格的比较最终会由分离的包络认证：要证 $\alpha<\beta$，找到 $\alpha$ 的上界严格小于 $\beta$ 的下界即可。给定 $H$ 的已知误差日程后，$z>H$ 同样可以这样认证。若真实差为零，包络可能永不分离；不断得到相同小数或相交区间不构成等式证明，也不构成严格不等式证明。

为每个整数 $N\ge3$ 启动一个候选过程。它用有限整数运算精确分解 $N$，取得 $z=\log N$ 的认证上界，从而选择整数 $C>z$；枚举并判定所有 $p<C$ 的素数是有限整数任务。它对命题 112.6 的全部有限比较及 $z>H$ 同时逐级细化包络，只有全部比较认证成功才输出。证书由精确分解、有限素数范围、$C>z$ 的界及严格比较的分离包络组成。候选不合法时可以因反向严格比较而剔除，也可以保持未完成；正确性不依赖每个不合格候选都被判退。

对这些候选采用公平交错，而不是在一个 $N$ 上等待结束后才看下一个。例如第 $s$ 轮把 $3\le N\le s+2$ 的候选都纳入，并各推进有限个基本计算步骤；每个已纳入候选在以后各轮持续获得计算步骤。于是任何固定候选的任何有限计算前缀都会最终被执行。这个调度可以同时涵盖分解、包络及全部比较，避免一个零差比较永久阻塞后续候选。

由定理 111.4，存在严格稳定根 $z=\log N>\max(H,1)$。该 $N$ 是某个有限整数，因而最终被纳入。对它，所选 $C>z$ 的有限证书全部比较都有严格正的余量，且 $z-H>0$。有限多个严格比较各需有限精度；取这些有限完成阶段的最大值，该候选就会完成。公平调度最终运行到该阶段，故整个搜索有限步输出某个有效严格根。这是以无界根存在性证明搜索停机，不需要一个有效的 Littlewood 首次振荡界。

输入约定须保留。可计算 $H$ 的 Cauchy 名及误差日程提供上述有效包络；若给定的是任意实数目标 $h$ 的认证有理数或整数上界 $H\ge h$，只需搜索 $z>H$，即保证 $z>h$，完全不必求值 $h$。若只给非可计算实数的 Cauchy 预言机，则调用带误差的一次粗近似便能取得有限整数上界，或相对该预言机执行严格比较。一个没有表示、上界或预言机的任意实数，不是有限算法输入；定理 112.2 对任意实数的量词并未赋予它这种输入表示。

输出第 $j$ 个根后，由它的对数上包络选择整数 $H_j>\log N_j+1$，重新运行同一搜索。每次调用仍由无界严格根保证停机，且所得 $z_{j+1}>H_j>z_j+1$，所以根列严格递增且趋于无穷。首次完成取决于各证书何时认证，前面较小的整数仍可处于未完成状态；因此该共尾子列不保证列出全部严格根，也不保证每次给出最小的下一个根。这里没有执行数值搜索，证明不提供首个成功整数、分解成本、比较精度或根间距的实用上界。$\square$

**命题 112.8（有限终止、有限截断与相等判定的不同边界）。** 定理 112.2、112.5 的经典有限轨道结论不蕴含 $A^-$ 或 $B$ 对全部实数 Cauchy 名的统一可计算求值。有效有限层截断、层比较三分判定、整数状态相等以及定理 112.7 的严格证书半判定，是不同的要求。

证明。先看有限截断。若价格 $\lambda>0$ 有可计算表示，可以通过包络找到有理数 $0<\ell<\lambda$，再选整数 $T$ 使 $2/T<\ell$。由 $\log p\ge\log2>1/2$ 及边际界，

$$
r_{p,k}<\frac1{p^k\log p}<\frac2{p^k}.
$$

故 $p^k\ge T$ 时必有 $r_{p,k}<\lambda$。只剩 $p^k<T$ 的有限层需要比较。然而对这个有限清单，严格规范成员资格是 $r_{p,k}>\lambda$，包含同价层的成员资格是 $r_{p,k}\ge\lambda$；两个严格方向的半判定都不能在零差时自动结束。有限清单的取得并没有变成相等判定器。

如果对每个遇到的有限层都给出总的三分比较预言机，或另有有效的相等证书与完整比较办法，就足以精确求值两种更新。另一种充分合同是已知全部访问点均非事件，此时有限清单上逐项运行双向严格比较最终结束。$B$ 还显式测试 $A^-(x)=x$；在任意初值的第一步以后，状态可表示成某个精确整数的对数。只要层集合已被精确算出，比较连续两个状态就等价于比较其两个整数，因对数严格单调而可由整数相等判定。第一步即使已经固定，也可以从下一步开始作这种整数比较。这消除了后续的状态相等问题，却没有解决 $r_{p,k}=\lambda(\log N)$ 的层相等问题，亦没有免除 $B$ 在弱停点包含全部同时同价层的要求。

还可从函数本身看出统一实数求值的限制。在任意事件 $\tau$，$A^-$ 的左、右极限分别为 $a$ 与 $b=a+J_\tau>a$，故它不连续。$B$ 在事件附近的每个非事件点都等于该点的 $A^-$：即使稳定胞腔内有固定点，那里 $A^+=A^-$，条件分支也不改变值。因此 $B$ 在 $\tau$ 的两侧极限同样是 $a,b$；选择某个端点值不能消去跳跃。通常 Cauchy 名表示下的全域实数可计算函数必须连续：一个要求给定输出精度并停机的计算只读取输入名的有限信息，在一个留有误差余量的合法名字上，这些有限信息也可由足够接近的输入共享，从而迫使输出在该点连续。正跳跃与此矛盾，所以不能从组成公式中的对数可计算就推出覆盖全部事件的统一求值器。

这个不连续性论证是关于所有实数输入的统一表示，不证明某一条具体算术等式不可判定，也不判定命题 112.4 所述算术同价是否存在。定理 112.7 另走整数候选的有限严格证书，用公平交错避开对零差作总判定；它证明的是有表示目标下的有效取得，未证明原轨道对任意实数都可直接执行。经典轨道的有限状态数、可计算的尾部截断及搜索停机均不意味着低成本。所有取得的严格根虽由定理 98.3 给出 Robin 裕度的严格局部极小，仍没有由此得到裕度严格为正。$\square$

## 追加锚（本行以下为增补区）

## 113. 同一实际来源的重置查询与精确取得成本

### 113.1. 查询合同、实际满纤维与共同字面词

**定义 113.1（重置取得的源、目标与成本）。** 固定整数 $H\ge2$，沿用定义 104.2 的正值规范语言、低位到高位的三位字母表 $\mathcal B=\{000,100,010,101,001\}$，只取共同结构标签 $(s,E)=(1,\mathrm{true})$。源域允许两种 $\varepsilon$ 初始化及任意有限过去深度。从该域选择一个未知的正值实际规范前缀，此后每次重置都返回这一个前缀；它的初始化、深度、整数值、余数及下一权重行均固定。允许两种初始化是整个候选族的量词，并非每个固定初始化各有满余数纤维的断言。

一次查询由重置、一个有限字面窗口后缀和紧随其后的真实 End 构成，计一个查询回合。空后缀也计一问；没有免费的初始 End 观察。成功时只读原始完整 $\gcd(N_{\rm final},H)$，或与之双射的 $F_H(N_{\rm final})=H/\gcd(N_{\rm final},H)$；不另读单位部分、$\eta_{H,d}$ 的较强坐标或中途状态。非法词或不适当 End 给同一个 $\mathsf{err}$。非空成功词的首位必须为 0、内部没有相邻 1、最后一个三位窗口非零；最后单个位不必为 1。End 的整数值必须为正，零余数只表示一个正的 $H$ 倍数。

策略是确定性自适应决策树，下一字面词可依赖此前全部回答；目标是精确确定完整未来行为类，允许推断最后唯一候选而不再查询确认。最坏回合数记为 $Q$。计算时间在这个成本中不收费，但最大单词窗口数、全部提交窗口数、两两区分 horizon、自主记忆态数和查询回合数始终是不同资源。

已知行问题供应一个固定的实际模 $H$ 下一行 $(u,v)$，未知的是该行上的 $r\in\mathbb Z/H\mathbb Z$。实际行均幺模，可取已知 $\alpha,\beta$ 使 $\alpha u+\beta v=1$。若仅在抽象幺模行上规定相同读出和满余数先验，下述代数结论仍有意义，但这种行不自动是实际 Fibonacci 相位。未知方向问题则只允许实际的三步相位轨道，不把先验扩大成全部幺模行。

满纤维的实际依据是引理 105.1 与定理 105.4；模 5040 的共同相位表述见命题 108.2。具体地，若某实际行在深度 $j_0$ 出现，$T(u,v)=(u+2v,2u+3v)$ 在有限模行空间可逆，故该原始行在 $j=j_0+nP$ 的任意大深度返回。标签 $(1,\mathrm{true})$ 的正整数像是

$$
[F_{3j+2},F_{3j+3}-1]\cap\mathbb Z,
\qquad\text{长度 }F_{3j+1}.
$$

选择一次足够大的返回深度，使长度至少为 $H$，便可在同一实际整数权重行和同一深度为每个 $r$ 选一个正值实际前缀。不同候选可有不同 $\varepsilon$；选定隐藏候选后不再变化。不同原始行的这项存在性不要求在同一数值深度实现。有限乘积状态的转移闭合本身不能代替此返回区间论证。

后续直接复用定理 104.7 在 $d=H$ 的分类：同标签的三元组 $(r,u,v)$ 按一个共同单位缩放取商，恰为完整未来类。固定幺模行的 $H$ 个余数因此是 $H$ 个不同未来类。引理 106.2 给每个字面词一个与源无关的系数对

$$
A_w=b_0+\sum_{i\ge2}b_iF_{i-1},\qquad
B_w=b_1+\sum_{i\ge2}b_iF_i,
\qquad c_w=A_wu+B_wv.
$$

同一词在所有源上用同一 $(A_w,B_w)$；同标签使其错误模式也与算术坐标无关。定理 106.3 已给出每个模 $H$ 系数对的一个共同、首两位为 $00$、末窗非零的成功字面词，且长度至多

$$
L(H)=\left\lceil\frac m3\right\rceil,
\quad q=\text{首个大于 }2H\text{ 的 Fibonacci 数},
\quad m=\min\{n:F_n\ge H(q+1)\}.
$$

这里调用该既有构造，不另证明系数分类或通用短词构造。对已知行，请求平移 $c$ 时取 $(A,B)=(\alpha c,\beta c)$ 即可；对未知行，请求的是一个共同系数对而不是按候选分别选词。每次词后立即 End，下一问依靠重置资源，不要求该词末端恢复相位。

### 113.2. 素数上的等值搜索与受限方向几何

**定理 113.2（已知实际素数方向的精确成本）。** 令 $H=p$ 为素数。若已知实际下一行，或仅已知其射影方向并把余数随行共同归一化，且该方向上的全部 $p$ 个归一化余数都可能，则

$$
Q_{\rm known}(p)=p-1.
$$

下界允许任意词长；上界每问至多 $L(p)$ 窗。若先验只有该方向上的 $n\ge1$ 个余数，成本相应为 $n-1$。

证明。成功回答只有 $\gcd=p$ 与 $\gcd=1$，以下分别称 YES 与 NO。固定非零行后，一问恰测试

$$
r=-Au-Bv.
$$

所以沿全 NO 路径，每问至多删除一个余数，恒错词不删候选。少于 $p-1$ 问时至少两个未来类仍存。反向依次测试任意 $p-1$ 个余数 $a$：若 $u\ne0$，取 $(A,B)=(-a/u,0)$；否则 $v\ne0$，取 $(0,-a/v)$。每个系数对用定义 113.1 的同一通用构造实现；YES 确定该余数，全 NO 后推断剩下一个。$n$ 元先验同理。实际满纤维为每个候选提供固定源代表，故下界路径不需要改变隐藏源。给定固定小深度、固定 $\varepsilon$ 或额外前缀信息时，不能未经核对就使用 $p$ 元先验。$\square$

**定理 113.3（任意非空方向集的受限查询成本）。** 在 $\operatorname{PG}(2,p)$ 中固定 $O=[1:0:0]$。令 $\Omega\subseteq\operatorname{PG}(1,p)$ 非空，$k=|\Omega|$。每个方向 $\omega=[u:v]$ 选一个非零代表，候选域为

$$
D_\Omega=\bigsqcup_{\omega\in\Omega}
\{[r:u:v]:r\in\mathbb F_p\}.
$$

它是过 $O$ 的 $k$ 条射影直线分别去掉 $O$ 后的并，恰有 $pk$ 点。唯一的非常数查询是“不经过 $O$ 的射影直线是否含隐藏点”，即

$$
\ell_{A,B}:r+Au+Bv=0.
$$

在确定性自适应、最坏成本、允许最后候选推断的合同中，精确成本为

$$
Q(p,\Omega)=p+k-2,\qquad 1\le k\le p+1.
$$

证明。先给只用规定查询的上界。在系数仿射平面中把候选 $X=[r:u:v]$ 对偶成隐藏直线

$$
L_X=\{(A,B):r+Au+Bv=0\}.
$$

每个 $\omega$ 给一个平行类，该类的全部 $p$ 条直线都可能；查询 $(A,B)$ 就是测试该点是否在隐藏直线上。这里没有增加任意点候选测试或过 $O$ 的原平面直线查询。

当 $k\le p$，在系数平面选非零方向 $d$，使 $d\cdot(u,v)\ne0$ 对每个 $\omega$ 成立。被禁止的垂直方向只有 $k$ 个，而射影方向共有 $p+1$ 个，所以可选。直线 $h=\{td:t\in\mathbb F_p\}$ 与每条候选隐藏直线恰交一点。依次查询 $h$ 上任意 $p-1$ 点，遇到 YES 即停止这一段；全 NO 时交点只能是未问的那一点。记已确定交点为 $x$。恰有 $k$ 条候选直线通过 $x$，每方向一条；对于代表 $(u_i,v_i)$，点 $x+(v_i,-u_i)$ 位于对应候选线上，且不在其它方向的候选线上。至多再问 $k-1$ 个这种点便能确定隐藏线，包括对最后一条的推断。总数至多 $p+k-2$，亦覆盖 $k=1$。

当 $k=p+1$，取系数平面的一条直线 $h$，依次问其全部 $p$ 点，在首个 YES 处停。若首问就是 YES，通过该点的 $p+1$ 条候选线至多再用 $p$ 个上述单候选测试区分，总计 $p+1\le2p-1$，$p=2$ 时也成立。若第 $i\ge2$ 问首次 YES，早先的 NO 已排除 $h$ 本身，只剩通过该点的 $p$ 条其它线，至多再用 $p-1$ 问，总计 $i+p-1\le2p-1$。若 $h$ 的 $p$ 点全 NO，隐藏线是另 $p-1$ 条平行线之一，至多再问 $p-2$ 个代表点即可推断最后一条，总计 $2p-2$。这给出 $p+k-2=2p-1$ 的上界。

下界需要完整覆盖的私人点引理，而不能直接借用全射影平面的最优搜索数。所用原始出处是 Héger–Patkós–Takáts, *Search problems in vector spaces*, [DOI:10.1007/s10623-014-9941-9](https://doi.org/10.1007/s10623-014-9941-9)，[作者稿 arXiv:1309.6731v2](https://arxiv.org/pdf/1309.6731v2)，Corollary 2.2，第 4 页：若 $\mathcal C$ 是覆盖整个 $\operatorname{PG}(2,q)$ 的直线集合，且 $\ell\in\mathcal C$ 是 essential（删去它不再覆盖），则

$$
\left|\ell\setminus\bigcup_{\ell'\in\mathcal C\setminus\{\ell\}}\ell'\right|
\ge2q+1-|\mathcal C|.
$$

这里用 $q=p$ 的 Desarguesian 平面。该文第 4–5 页的覆盖对手论证提供方法；其 Theorem 1.1 的全平面目标及点或线查询合同不等于本定理。作者稿把前述引理追溯到 Blokhuis–Brouwer 的阻塞集切线结果；本处使用的是已核对的 HPT 明文对偶陈述，不声称读过 1986 年原论文证明。

$k=1$ 已由定理 113.2 的等值搜索证明。设 $k\ge2$，置 $b=p+1-k$，取 $\mathcal C_0$ 为缺失方向对应的 $b$ 条过 $O$ 直线。$b>0$ 时它们的并恰为 $D_\Omega$ 的补集；$b=0$ 时唯一额外的非候选点是 $O$。这些缺失径向线只用于证明，绝不是附赠查询。

固定任意正确的确定性策略，沿其全 NO 路径考虑实际问出的不同可用直线 $\ell_1,\ell_2,\ldots$；重复词、重复直线和恒错词只增加总成本，可在这个编号中忽略。对手在首次满足下述条件的 $t$ 回答 YES：

$$
\mathcal C_0\cup\{\ell_1,\ldots,\ell_t\}
\quad\text{添加至多一条射影直线 }m\text{ 后可覆盖全平面。}
$$

在此之前回答 NO。初始时没有这种覆盖：一条额外径向线最多覆盖 $p$ 个候选，非径向线最多覆盖 $k$ 个，而 $pk>p,k$。在触发前若仅剩零或一个候选，取一条经过该候选的线即可补成覆盖；$b=0$ 时让补线也经过 $O$。这与尚未触发矛盾。因此触发前策略不能正确结束，任何有限正确策略必遇到首次触发。

选取触发所需的 $m$，令

$$
\mathcal C=\mathcal C_0\cup\{\ell_1,\ldots,\ell_t,m\},
\qquad |\mathcal C|\le b+t+1.
$$

若无需 $m$ 就已覆盖，可省掉它或取任意一条而按集合去重。新线 $\ell_t$ 必 essential；否则删除它后已有 $\mathcal C_0\cup\{\ell_1,\ldots,\ell_{t-1}\}$ 加至多一线的覆盖，违反首次性。私人点引理给 $\ell_t$ 至少

$$
2p+1-(b+t+1)=p+k-t-1
$$

个不在其它覆盖线上的点。$b>0$ 时这些点不在 $\mathcal C_0$，故全是允许候选；$b=0$ 时 $\ell_t$ 不经过 $O$，同样没有混入非候选。它们避开全部此前 NO 线，并在当前线给 YES。因此首个 YES 后至少有 $n\ge p+k-t-1$ 个一致候选，且 essential 性保证至少一个。往后任何不同的可用线与 $\ell_t$ 至多交一点；重复 $\ell_t$ 则恒为 YES。于是最坏还要 $n-1$ 个单候选排除，总数至少

$$
t+n-1\ge p+k-2.
$$

若触发时 $t$ 本身已超过此界，下界当然成立。此后继续保留所有未被排除的点直到最后；任意一个最终存活点产生整段回答，确定性又保证每步选择同一条查询线。这是一个固定隐藏候选的最坏路径存在证明，不是允许对手在查询之间更换源。$\square$

**推论 113.4（实际未知素数方向）。** 对定义 113.1 的完整实际源域，令

$$
\Omega_p=\{[F_{3j+3}:F_{3j+4}]:j\ge0\},
\quad k=|\Omega_p|=\frac{\rho(p)}{\gcd(\rho(p),3)}.
$$

原始 gcd 任务在共同标签上的行为类恰有 $pk$ 个，且未知方向时

$$
Q_{\rm unknown}(p)=p+\frac{\rho(p)}{\gcd(\rho(p),3)}-2.
$$

证明。命题 105.2、推论 105.3 已给实际三步轨道的方向数 $k$；不能将位步长的 $\rho(p)$ 原样当作窗口相位数。定理 104.7 的共同非零缩放把实际三元组恰送到定理 113.3 的 $D_{\Omega_p}$。定义 113.1 的返回区间又使每个实际方向的全部 $p$ 个归一化余数都可达，故这是候选域的等号，而不仅是嵌入。引理 106.2 把任意长成功词送到非径向线；定理 106.3 反向把每个 $(A,B)$ 实现为同一条至多 $L(p)$ 窗的实际词。恒错词无额外信息。两查询模型因而完全对应，应用定理 113.3 即得精确数。下界的最终存活类由返回区间选一个正值前缀代表，所有重置均使用它。

例如 $p=17$ 时 $F_1,\ldots,F_8=1,1,2,3,5,8,13,21$ 均非零模 17，$F_9=34$ 为零，故 $\rho(17)=9,k=3$。前三方向为 $[2:3],[8:13],[0:4]$，即 $[1:10],[1:8],[0:1]$；下一行 $(144,233)\equiv(8,12)$ 返回首方向。因此有 51 类、精确 18 问，并没有全部 18 个方向。$p=2$ 时 $\rho(2)=3,k=1$，未知方向也只需 1 问。$p=7$ 时首个零 Fibonacci 项为 $F_8=21$，$k=8=p+1$，需 13 问，说明上界中的全方向分支确有用途。

这里识别的是行为类；标量相位和平移后共同缩放的余数可能给完全相同未来，故不能再宣称恢复原始深度、精确整数或源的字面身份。一个两两区分词长上界只说“每对不同类有一个短测试”，并不限制逐步取得该类的问数。即使每问词长为 $O(\log p)$，已知方向仍需 $p-1$ 问，未知方向需 $p+k-2$ 问。$\square$

### 113.3. 素幂的完整低位优先反馈

**定理 113.5（已知行的完整估值对手）。** 设 $H=p^h$，$p$ 为素数、$h\ge1$，源先验和已知实际行满足定义 113.1。则

$$
Q_{\rm known}(p^h)=h(p-1).
$$

更具体地，把余数写成恰长 $h$ 的低位优先 $p$ 进数字词。若当前候选集具有固定前缀 $P$、长度 $k<h$，下一位属于 $A\subseteq\{0,\ldots,p-1\}$、$|A|=m\ge2$，其余高位自由，则从该候选集开始的精确剩余成本为

$$
V(P,A)=(m-1)+(h-k-1)(p-1).
$$

证明。请求中心 $a$ 指请求平移 $c=-a$，它由 $(A_w,B_w)=(-\alpha a,-\beta a)$ 的一个合法词实现。成功回答等价于完整截断深度

$$
\lambda_a(r)=\max\{j\in\{0,\ldots,h\}:r\equiv a\pmod{p^j}\},
\qquad \gcd(r-a,p^h)=p^{\lambda_a(r)}.
$$

定义按同余给出，故 $r=a$ 时取 $h$，不涉及未截断估值在零的约定。低位优先且高位补至 $h$ 位后，$\lambda_a(r)$ 就是与查询词的最长共同前缀长度（LCP）；一问有 $h+1$ 个可能深度，不能当作只收到一个布尔位。

记上述候选集为 $S(P,A)$。当 $A$ 为单点时，将该位并入 $P$；若还未到长度 $h$，下一位重新取全部 $p$ 个符号。反复作此规范化，完整固定词是终端单点，势取 0。规范化保留显示的势：$m=1$ 时剩余的 $(h-k-1)(p-1)$ 恰是下一层的满符号势。非终端规范态有 $m\ge2$，候选数是 $mp^{h-k-1}$，势严格正。初态为 $k=0,A=\{0,\ldots,p-1\}$，势为 $h(p-1)$。

对任意中心，全部可能分支如下，且没有遗漏深匹配或精确命中。

1. 中心在 $j<k$ 处首次偏离固定前缀，则全部候选都给 $\lambda=j$，后验及势不变。
2. 中心符合 $P$，但第 $k$ 位不在 $A$，则全部候选给 $\lambda=k$，后验及势不变。
3. 中心符合 $P$ 且第 $k$ 位在 $A$，回答恰为 $k$，则从 $A$ 删除该位，其余高位仍全自由。因 $m\ge2$，分支非空，规范化后势恰降 1。
4. 同一在集内中心若得到 $k<\ell<h$，则前 $\ell$ 位固定为中心的位，第 $\ell$ 位可取除中心该位之外的全部 $p-1$ 个符号，更高位自由。规范化前的新势为 $(p-2)+(h-\ell-1)(p-1)$，故下降量为

$$
(m-1)+(\ell-k-1)(p-1)+1
=m+(\ell-k-1)(p-1)\ge1.
$$

5. 回答 $h$ 是精确中心命中，后验立即是单点，势为 0。
6. 非法词或不适当 End 的共同 $\mathsf{err}$ 不改变候选集。

这些后验均由原来完整候选集与所报深度相交得到，不只是保留某个足够大的子集。集内中心的所有深度 $k,\ldots,h$ 都有源实现，因为尚未指定的高位自由；$p=2$ 时第四分支的单符号集也按上述规则规范化。

上界在每个非终端态选任意 $a\in S(P,A)$，用一个共同字面词查询，读取完整深度并更新到对应后验。每问势至少降 1，或直接成为单点，故至多初始势那么多问；已经唯一时直接推断，不强制补一次 YES。

下界固定任意确定性策略，维护同样的规范态和所有此前完整回答。对于前两类中心返回其被迫常数；错误词返回 $\mathsf{err}$；对于集内中心总返回第三类的恰好深度 $k$，仅删除其下一位。这个浅不匹配是实际存在的完整回答，因至少还有另一个完整子树；保留子树的高位不受约束。每问势至多降 1。因此少于 $V(P,A)$ 问时势仍正，至少两个不同余数及未来类一致，策略不能正确停止。深匹配和精确命中在其它路径上完全允许，这条下界只需一条合法硬路径。初始实际满纤维中嵌套保留的候选代表非空，任取最终存活代表，即为产生整段回答的一个固定正值实际源。故这是完整值反馈的下界，不是二进制信息量界，也不是把各位假装成互不影响的等值搜索。

初态代入给 $h(p-1)$。$h=1$ 恰回到 $p-1$；$p=2$ 时每次浅回答固定一位，最坏恰为 $h$，容易路径仍可一问揭示多位。例如模 8，中心 $0,1,3$ 对同一 $r=7$ 的深度为 $0,1,2$，依次留下 $\{1,3,5,7\},\{3,7\},\{7\}$；第三问靠推断结束。$\square$

该 LCP 模型与 Afshani 等的 [*The Query Complexity of a Permutation-Based Variant of Mastermind*, arXiv:1812.08480v1](https://arxiv.org/pdf/1812.08480v1)，§1.1、§2 的完整分数决策树相接：固定其排列并令二进制词长为 $h$，才得到这里 $p=2$ 的已知位序模型。其未知排列不是本卷的未知 Fibonacci 行；未知排列的成本界不转入这里。Doerr–Winzen 的 [*Black-Box Complexity: Breaking the O(n log n) Barrier of LeadingOnes*, arXiv:1210.6465v1](https://arxiv.org/pdf/1210.6465v1)，第 2–3 页给相同前缀分数及随机黑箱优化合同，但其成本是直到实际查询最优词的最坏期望评估数。随机化、隐藏排列和要求命中最优词均不同于本节的确定性识别并允许推断；上述数值等式来自所列完整分支证明，不引用这些优化界。仅返回 $[\lambda_a(r)>j]$ 的阈值预言机也更弱：完整深度能回答阈值问题，反向未必能一问模拟，故阈值模型的下界不能未经证明移给完整深度模型。

### 113.4. 复合模数的同步中心与实际坐标轴

**定理 113.6（已知实际行的 CRT 最大值）。** 设

$$
H=\prod_{i=1}^s p_i^{h_i}\ge2,
\qquad p_i\text{ 两两不同},\quad h_i\ge1.
$$

在定义 113.1 的已知实际行、完整余数先验及原始完整 gcd 合同下，

$$
Q_{\rm known}(H)=\max_i h_i(p_i-1).
$$

每问至多 $L(H)$ 窗足以取得这个回合数。抽象幺模行上若另行规定相同满纤维读出模型，也有同一代数成本；实际源的结论仍以定义 113.1 的返回区间为依据。

证明。一个完整 gcd 回答唯一分解成每个 $p_i$ 的截断深度；若原标签是 $F_H$，先取 $H/F_H$ 即恢复同一元组。上界并行运行定理 113.5 的局部策略。在一个已固定历史上，每个未结束因子请求中心 $a_i$，已结束因子任取中心。CRT 给一个全局平移 $c$，满足

$$
c\equiv-a_i\pmod{p_i^{h_i}}\quad(1\le i\le s).
$$

用已知 Bézout 对取 $A=\alpha c,B=\beta c$，便有 $Au+Bv=c$ 模 $H$。定理 106.3 在模 $H$ 产生一个共同字面词；这一个词的一次 End 同时提供各局部策略所需的完整回答，不是串接不同局部词，也不是拼接不同源。每一局部策略在至多 $h_i(p_i-1)$ 轮结束，所以至多其最大值轮确定全部局部余数，CRT 再确定 $r$。不能假定 $u$ 或 $v$ 有一个在全局必为单位；幺模性给 $\alpha u+\beta v=1$ 已经足够。

为证下界，任选因子 $i$，为其它因子预先固定余数 $b_j$。令 $x$ 遍历 $\mathbb Z/p_i^{h_i}\mathbb Z$，由 CRT 取全局余数 $r_x$，其第 $i$ 坐标为 $x$，其余坐标为 $b_j$。定义 113.1 的同一返回深度满纤维为全部 $r_x$ 选实际代表，标签、深度和原始行一致。

在策略的某个完整历史上，下一词 $w$ 已确定，故平移 $c_w=A_wu+B_wv$ 也已确定。对 $j\ne i$，回答分量是

$$
\max\{t\le h_j:b_j+c_w\equiv0\pmod{p_j^t}\},
$$

是已选词和固定坐标的已知函数，条件于该历史并不再含 $x$ 的信息。它可随轮次、随早先含 $x$ 的回答而改变，却不能成为新的独立读数。一个局部模拟者因此可用至多一个第 $i$ 轴的深度查询，计算并附上全部其它分量，模拟每个成功全局回合；恒错回合可直接模拟。全局树若识别所有 $r_x$，局部树就识别所有 $x$。定理 113.5 的完整值下界给至少 $h_i(p_i-1)$ 回合。对每个 $i$ 成立，取最大值。

等价地，可在变化轴上运行浅不匹配对手，其余轴从一开始就取固定 $b_j$。所有局部回答组成一个真实完整 gcd，嵌套剩余 CRT 候选均有实际前缀，最终一个代表实现整段历史。这同时说明上界为何能取最大值，以及下界为何没有把多个不相容局部最坏源强行合并。$\square$

**推论 113.7（5040 的六回合与充分窗口预算）。** 对任一已知实际行的完整模 5040 纤维，任意长度查询的精确最坏成本为 6；每问 13 窗、总计至多 78 窗是一个充分实现预算。

证明。$5040=2^4\cdot3^2\cdot5\cdot7$ 的局部成本为 $4,4,4,6$，定理 113.6 给最大值 6。下界也可直接固定模 $720$ 余数、变化模 7 的七个余数：其余 gcd 分量在所选词条件下确定，模 7 一问只作一次等值测试，五次错过后仍至少两个实际源。

对定理 106.3 的长度参数，$F_{20}=6765<10080<10946=F_{21}$，所以 $q=10946$，并且

$$
5040(q+1)=55172880,
\qquad F_{38}=39088169<55172880\le63245986=F_{39}.
$$

故 $m=39,L(5040)=13$，六问共至多 $6\cdot13=78$ 窗。这里 13 是通用系数实现给出的充分预算，78 是随之得到的总窗口上界；没有由此声称它们是识别所需的最小预算。§107 的三窗结论是两两完整未来区分 horizon，且保留其假设 107.5；它既不是六问策略，也不是一次三窗查询就能恢复余数。下一节专门处理限制每问词长后的取得问题。未知实际行时，局部相位受同一过去深度约束，平移也不再是已知可选中心，不能直接沿用本节的 CRT 最大值公式。$\square$

## 114. 有限窗口词族的取得、联合收尾与五十二个实际相位

### 114.1. 完整可用族与有限可识别性

**定义 114.1（有界词长的完整平移像）。** 保持定义 113.1 的合同，供应已知实际行 $(u,v)$。令 $Q_t(H;u,v)$ 为每问至多 $t\ge0$ 窗时的精确最坏回合数；不存在有限精确策略时取 $+\infty$。每问仍可依赖此前全部 gcd 回答，并重置到同一个源。对 $t\ge1$，令

$$
\begin{aligned}
\mathcal I_t&=\{I\subseteq\{1,\ldots,3t-1\}:I\text{ 不含相邻整数}\},\\
c_I&=\sum_{i\in I}(F_{i-1}u+F_iv)\pmod H,\\
C_t(H;u,v)&=\{c_I:I\in\mathcal I_t\},\qquad
\mathcal A_t(H;u,v)=-C_t(H;u,v).
\end{aligned}
$$

$C_t$ 是平移像，$\mathcal A_t$ 是等值中心像：平移 $c$ 的测试为 $\gcd(r+c,H)$，中心 $a=-c$ 的测试为 $\gcd(r-a,H)$。取 $C_0=\mathcal A_0=\{0\}$。不同词有相同模平移时可以在像中去重，但先验允许的词不因去重而删减。

集合 $I=\varnothing$ 对应收费的空查询；非空 $I$ 对应偏移 0 为零、恰在 $I$ 置 1，并在含 $\max I$ 的窗口末端停止的词。把它表示成 $3t$ 位只是记法，执行前删除末尾整个零窗口；不得删除前导或中间零窗，也不得把末位为零的非零窗口裁掉。特别地，首两位为 $01$ 的成功词必须保留，不能用 §106 的首 $00$ 构造子族替换完整有界词族。

**命题 114.2（全部成功词的参数化与计数）。** 定义 114.1 的独立集与标签 $(1,\mathrm{true})$ 出发、长度至多 $t$ 的成功词一一对应，其数为 $F_{3t+1}$，$t=0$ 时为 1。其它字面词在整个纤维上均为恒错。$t=3$ 时有 55 个成功词，156 个长度至多 3 的字面词中其余 101 个恒错；成功词的模平移像大小至多 55。

证明。共同接缝为 1 强制首位 0；内部合法性恰排除相邻 1。成功非空词的最高一个 1 位于某个末窗口内，而该窗口非零，所以由其所有置 1 偏移恰恢复 $I$ 和停止窗口。反向定义 114.1 的构造满足这些条件，且末窗非零，故正值 End 合法。空 $I$ 与空词相配。引理 106.2 的系数式在首位为零时正是 $c_I$；尤其偏移 1 的权重是 $v=F_0u+F_1v$。

长度 $n$ 的路径独立集数满足 $a_n=a_{n-1}+a_{n-2}$，由最后位置不选或选而禁其前邻得到，$a_0=1,a_1=2$，故 $a_n=F_{n+2}$。代入 $n=3t-1$ 即得。至多 $0,1,2,3$ 窗的成功数分别为 $1,3,13,55$，所以恰长各层为 $1,2,10,42$；全部字面数为 $1+5+25+125=156$。对三窗，八个可选偏移的权重完整地是

$$
v,\ u+v,\ u+2v,\ 2u+3v,\ 3u+5v,\ 5u+8v,\ 8u+13v,\ 13u+21v.
$$

这证明的是词族及其像的符号描述；55 不必是每行上不同模中心的数目。末尾整窗 $000$ 会清除 $E$，例如 $[010,000]$ 不是 $[010]$ 的成功重复。相反末窗 $100$ 或 $010$ 虽最高单个位为零，却完全可以成功 End。$\square$

**定理 114.3（底层兄弟块判据）。** 固定定义 113.1 的完整已知行纤维，令 $\mathcal A$ 为任一有限可用中心集，每个中心附有一个允许的成功字面词。对每个 $p^h\parallel H$，令 $\mathcal A_p$ 为它在 $\mathbb Z/p^h\mathbb Z$ 的投影。有限精确识别存在，当且仅当每个底层兄弟块

$$
B_b=\{b+jp^{h-1}:0\le j<p\},
\qquad b\in\mathbb Z/p^{h-1}\mathbb Z,
$$

都满足 $|\mathcal A_p\cap B_b|\ge p-1$。特别地，本判据适用于完整的 $\mathcal A_t$，有限识别的必要计数条件为

$$
F_{3t+1}\ge\max_{p^h\parallel H}p^{h-1}(p-1).
$$

证明。同一底层块内的两个不同叶子 $x,y$，低 $h-1$ 位相同。从任何中心 $a\notin\{x,y\}$ 看，两者的截断 LCP 相同：若中心不在该块，两者都在同一个更低位置失配；若中心是该块的第三个叶子，两者都在最后一位失配。因此一个块若缺两个可用叶子，就有一对无法被任何局部投影测试区分。

反向若每块至少有 $p-1$ 个可用叶子，同块不同 $x,y$ 至少一个本身是可用中心，精确命中它即区分。异块的 $x,y$，取 $x$ 所在块的任一可用中心；它与 $x$ 匹配至少 $h-1$ 位，与 $y$ 不到 $h-1$ 位，仍区分。$h=1$ 时只有一个底层块，异块分支为空。

若某局部对无法区分，固定其它所有素幂坐标，再用 CRT 得到两个全局余数。返回区间为它们提供同深度、同行、同标签的两个实际源。每个可用词在问题轴上回答相同，在其它轴上因余数固定也相同，恒错词当然相同；确定性自适应重复这些测试也不能分离两源。反向，若所有局部投影都分离，对任何两个不同全局余数，取一个不同轴和分离该轴的投影中心，再取它在 $\mathcal A$ 中的一个原像。这个全局词的完整 gcd 在该轴不同，因而全局不同。查询全部有限中心便可识别。此论证只选择一个已存在全局中心，未要求任意局部中心元组都可实现。

一个模 $p^h$ 的投影至少要 $p^{h-1}(p-1)$ 个元素，而 $|\mathcal A_t|\le F_{3t+1}$，得必要计数条件。计数本身不保证这些元素在各底层块的分布，故非充分条件。$\square$

### 114.2. 固定完整历史后的后验与可用中心

**定理 114.4（受限族的素幂等号和复合上下界）。** 若定理 114.3 的有限族 $\mathcal A$ 分离完整余数纤维，置 $D_i=h_i(p_i-1)$，则

$$
\max_iD_i\le Q_{\mathcal A}\le
\min\left\{|\mathcal A|,\ H-1,\ 1+\sum_i(D_i-1)\right\}.
$$

在单个素幂 $H=p^h$ 上，有限即有 $Q_{\mathcal A}=h(p-1)$；不分离则为 $+\infty$。这些式子对 $\mathcal A_t$ 同样成立。

证明。首先固定一个可行的完整自适应历史 $\tau$。在这条分支上，所有先前字面词已经确定。每次完整 gcd 回答是一组局部截断深度条件，所以其支持集恰为

$$
S(\tau)=\operatorname{CRT}^{-1}\left(\prod_iS_i(\tau)\right),
$$

其中 $S_i(\tau)$ 是该轴全部既往深度条件的交。定理 113.5 的全部分支计算说明，每个非空 $S_i$ 是一个规范前缀态 $S(P_i,A_i)$ 或单点。完整实际满纤维实现此乘积中每个元组，因此这里的乘积不是假定各轴概率独立；它是固定整段历史后源候选的准确支持集。

中心可用性是另一关系。可选元组只有

$$
\{(a\bmod p_i^{h_i})_i:a\in\mathcal A\},
$$

一般不是各投影的笛卡尔积。独立选好局部中心再作 CRT，不能保证所得中心还在 $\mathcal A$。

然而每个非终端局部规范态都含一个可用局部中心。若未固定位只剩最后一位，$m\ge2$ 已在同一底层块给两个叶子；若还有更高自由位，固定其它允许位而改变最高位，也在态内给同块两个叶子。根据定理 114.3，其中至少一个属于 $\mathcal A_p$。取它在 $\mathcal A$ 中的一个原像，便得到一个真实允许词，且该词在选定轴的中心位于当前候选态内。

单素幂时不断这样选择；定理 113.5 的分支计算使势 $V$ 每问至少下降 1，故至多 $h(p-1)$。其任意中心下界允许更大的查询族，限制中心不会使最优值更小，所以得到等号。

复合时，先作任意一个允许成功查询，包括收费的空词若其可用。起初各轴都是满纤维，所以每个局部中心都在其候选态内；第一问使每个初始势 $D_i$ 至少下降 1，或直接结束该轴。以后每问选择任一未结束轴，按上一段取一个全局中心推进它。其势至少降 1；其它轴按定理 113.5 的完整分支只会下降或不变。因此在第一问后最多还需 $\sum_i(D_i-1)$ 问。此过程从不把独立的局部词拼成一个假想短词。

另两项上界分别来自查询所有不同中心，以及在每个非单点候选集选择一个能分离其中两点的测试：后一过程每个回答分支都严格缩小候选数，故最多 $H-1$ 问。下界仍固定除一轴外的所有余数，以定理 113.6 的实际轴族模拟局部完整值查询，给 $Q_{\mathcal A}\ge D_i$。其它轴的回答只在已选词条件下作为固定函数补入，故不会越过局部下界。$\square$

这里的有限允许测试模型是标准多值决策树识别：Cicalese–Laber–Saettler, [*Decision Trees for Function Evaluation: Simultaneous Optimization of Worst and Expected Cost*, arXiv:1309.2796v2](https://arxiv.org/pdf/1309.2796v2)，第 2–3 页的 DFEP 定义，取对象集 $\mathbb Z/H\mathbb Z$、单点目标类、测试 $a\mapsto[r\mapsto\gcd(r-a,H)]$ 和单位测试成本即可。它的 completeness 指两两分离，最坏成本是决策树最大路径成本；其近似算法和一般实例困难性都不提供本卷的六问数值界。定理 114.4 使用的是这里的前缀后验及可用中心结构。

**推论 114.5（5040 的全行条件界与两窗障碍）。** 在假设 107.5 的语义覆盖与分区稳定条件下，对每个供应给策略的已知实际行，

$$
6\le Q_3(5040;u,v)\le15.
$$

无论是否使用该有限证书前提，命题 107.7 的已知实际行给出

$$
Q_2(5040;1618,2647)=+\infty.
$$

证明。在假设 107.5 下，推论 107.6、定理 107.8 使全部三窗词分离任意不同完整未来；固定行的不同余数确为不同未来类，所以 $\mathcal A_3$ 分离。代入定理 114.4 的 $D_i=(4,4,4,6)$ 得 $1+3+3+3+5=15$，下界为 6。至多 15 问、每问三窗，给至多 45 个提交窗口的充分预算，仍非最优性断言。

对两窗，直接复用命题 107.7 的两个十窗正值前缀：其下一实际整数行都是 $(3524578,5702887)$，模 5040 为 $(1618,2647)$，标签相同，余数分别为 2205 与 4725。它们对全部 31 个至多两窗字面后缀，包括空词及错误词，回答相同，但被 $[000,000,010]$ 区分。任何自适应树若只使用该两窗族，两源每步回答都相同，归纳得整条路径相同，故无法确定完整未来类。

上式全行上界保留假设 107.5，不把其有限覆盖、稳定关系省成无条件结论。以下给出的具体六问构造则直接识别全部余数，不以该假设作上界前提。对所有行量化时，每个策略仍知道所供应的那一行；这不是未知相位问题。$\square$

**命题 114.6（一窗模 12 的单位差）。** 对每个已知实际行，$Q_1(12;u,v)=2$；对任意抽象幺模行规定完整纤维时也成立。

证明。完整成功词仅为空词、$[010]$、$[001]$，平移为 $0,v,u+v$。这三平移的两两差在符号上是 $u,v,u+v$。因行幺模，该三项中恰有两项为奇数，且至少两项非零模 3；两个至少二元的指标集在三元指标域内有交，故至少一个差同时不被 2、3 整除，是模 12 单位。选该差的两端平移：相应中心奇偶不同，在模 4 的每个底层二叶块各占一叶；模 3 中也为两个不同叶子。因此两次完整 gcd 回答同时分离模 4 和模 3，再由 CRT 分离全部 12 个余数。下界由定理 113.6 为 $\max(2,2)=2$，或直接用模 3 的三元实际轴族。$\square$

**命题 114.7（平方自由有限族的静态覆盖等式及其边界）。** 若 $H=\prod_i p_i$ 平方自由，$\mathcal A$ 为分离完整纤维的有限中心族，则

$$
Q_{\mathcal A}=
\min\{|B|:B\subseteq\mathcal A,\quad
|B\bmod p_i|\ge p_i-1\text{ 对每个 }i\}.
$$

这是平方自由的等值坐标结论，不断言高素幂完整估值模型也静态化。

证明。满足条件的固定测试套件 $B$ 在每轴测试至少 $p_i-1$ 个不同值；命中即确定，全部未命中则推断唯一未测值，故给所列上界。反向沿任意自适应树维护剩余局部值的乘积：在某轴仍有至少两个候选时，若查询值在候选中则给 NO 并删此值，否则给被迫的 NO；一旦该轴成为单点，以后给其真实被迫回答，可能为 YES。各轴回答合成一个可行完整 gcd，乘积候选一直非空。到全局唯一时，每轴至少问过 $p_i-1$ 个不同中心值；该路径问过的不同全局中心于是组成所列一种 $B$，路径长度至少为显示的最小值。完整实际纤维存在时，一个最终源代表实现全路径。

例如抽象模 35 中人为限定 CRT 中心族为两个坐标轴

$$
\mathcal A=\{a:a\equiv0\pmod5\text{ 或 }a\equiv0\pmod7\}.
$$

其投影各自完整，仍需精确 8 问，而非无限制的 $\max(4,6)=6$。因为一个分离套件需至少四个模 5 值、六个模 7 值，除了可能共同出现的零，至少要三个非零模 5 轴中心和五个非零模 7 轴中心，且这两批不交，所以至少八个。八个 CRT 中心

$$
(1,0),(2,0),(3,0),(0,1),(0,2),(0,3),(0,4),(0,5)
$$

达到此界。这里没有声称这族是任何实际行的完整 $\mathcal A_t$，因而它不是规范 Fibonacci 行的反例，更不是 $Q_3(5040)>6$ 的证据；它只说明局部中心投影完整不蕴含全局同步中心可用。$\square$

### 114.3. 三个局部候选对的联合收尾

**定理 114.8（单词联合见证的分块匹配判据）。** 令 $C$ 是某个已知实际行的完整三窗平移像。固定前三次实际查询的一个可行完整历史，假设这三次的平移模 7 颜色两两不同，且模 $16,9,5$ 的后验各为单点或二元对。令 $J$ 为尚未解决的这些因子集合，$P_m=\{x_m,y_m\}$ 为对应二元对；令 $U$ 为四个尚未测试的平移模 7 颜色，$V=U\cap(C\bmod7)$。

对每个非空块 $B\subseteq J$，定义

$$
\begin{aligned}
\mathcal N(B)=\{\gamma\in U:\ &\text{存在一个实际允许词，平移 }c\in C, c\equiv\gamma\pmod7,\\
&\gcd(x_m+c,m)\ne\gcd(y_m+c,m)\quad\text{对每个 }m\in B\}.
\end{aligned}
$$

于是存在三次非自适应、使用三个不同未测颜色的追加查询分离该完整后验乘积，当且仅当 $|V|\ge3$ 且 $J$ 有一个非空块分拆 $B_1,\ldots,B_k$ 满足 Hall 条件

$$
\left|\bigcup_{\ell\in L}\mathcal N(B_\ell)\right|\ge|L|
\quad\text{对每个 }L\subseteq\{1,\ldots,k\}.
$$

$J=\varnothing$ 时用空分拆。这个必要性只针对所述三次、非自适应、不同未测颜色的收尾形态，不是所有自适应六问策略的必要条件。

证明。先说明局部区分条件可直接按完整估值检验。若 $m=p^h$、$x\ne y$，令 $t=\max\{j<h:x\equiv y\pmod{p^j}\}$。中心 $a=-c$ 区分两者，当且仅当

$$
a\equiv x\text{ 或 }y\pmod{p^{t+1}}.
$$

中心若在共同前缀以前偏离，给相同浅深度；若共享低 $t$ 位但第 $t$ 位与两者都不同，两边都给 $t$；若匹配其中一个第 $t$ 位，则对它至少给 $t+1$，对另一个恰给 $t$。所以底层模 16 二元对需要一个平移模 8 类，底层模 9 对需要两个平移模 9 类之一，模 5 对需要两个平移模 5 类之一。此处仍读取完整深度，不把回答替换成一个收费相同的新布尔预言机。

Hall 条件给互不相同的代表 $\gamma_\ell\in\mathcal N(B_\ell)$。有限匹配事实可归纳证明：若一个非空真子集的邻居数恰等于其大小，先匹配它并删除其全部邻居；把任意余下子集与该紧子集合并使用原不等式，便得到余下 Hall 条件。若没有非空真子集紧，就为一个块选任意邻居并删该颜色；其它非空子集此前至少多一个邻居，删除后仍满足不等式，归纳结束。单块及空族是基础情形。

为每个 $\gamma_\ell$ 使用定义 $\mathcal N(B_\ell)$ 中那一个实际词，它同时区分块内全部局部对，不能用几个不同词的各自见证冒充。因 $|J|\le3$，块数至多三；用 $V$ 中尚未使用的颜色补至三词，每个补色也取一个实际见证。指定给某局部对的词区分原来的两候选；其它追加回答只会缩小这对，不会破坏其充分性。若模 7 前三问已有命中，它已确定；否则三次新的不同颜色令总计六个颜色被测，命中即确定，没有命中则推断第七个。所有局部坐标都确定，CRT 确定 $r$。

反向，若三次这种非自适应收尾分离后验乘积，每个未解决局部对必至少被其中一词区分。否则固定其它坐标，取该轴两个值，便得到两个实际后验源，在前三问及这三问全部同答。将每个因子指定给一个区分它的收尾词；同词所负担的因子构成一个非空块。相应实际词同时区分块内各对，其不同颜色便是这些块的不同代表，故必满足 Hall 条件，且至少三个可用未测颜色存在。

乘积后验和所有元组的实际性来自定理 114.4；它们不使可用词像自动成为乘积。若分别给每个因子单独分配不同颜色，所得单元素块 Hall 条件只是一个充分特例；一个词可同时解决多个因子时，应合成一块。$\square$

### 114.4. 实际行 $(2,3)$ 的完整六问策略

**定理 114.9（行 $(2,3)$ 的三窗精确六问）。** 在定义 113.1 的满实际纤维合同下，

$$
Q_3(5040;2,3)=6.
$$

同一结论转移到实际轨道中所有与 $(2,3)$ 相差共同单位倍的行。

证明。该行是初始实际下一行，且在足够大的返回深度具有共同标签的全部余数代表，允许两种初始化跨候选族出现。这里不要求每个固定 $\varepsilon$ 各自实现全纤维。八个可选偏移的权重是

$$
3,5,8,13,21,34,55,89.
$$

令

$$
\begin{aligned}
D&=\{0,3,5,8,11,13,16,18\},\\
E&=\{0,3,5,8,11,13,16,18,21,24,26,29,32\}.
\end{aligned}
$$

$D$ 是前四位置的无相邻选择像，$E$ 是前五位置的像；下面给出每个值的具体偏移见证，标为 $D$ 的八项同时属于 $E$。

| 114.9 基本平移 | 偏移集合 $I$ | 基本范围 |
| --- | --- | --- |
| $0$ | $\varnothing$ | $D,E$ |
| $3$ | $\{1\}$ | $D,E$ |
| $5$ | $\{2\}$ | $D,E$ |
| $8$ | $\{3\}$ | $D,E$ |
| $11$ | $\{1,3\}$ | $D,E$ |
| $13$ | $\{4\}$ | $D,E$ |
| $16$ | $\{1,4\}$ | $D,E$ |
| $18$ | $\{2,4\}$ | $D,E$ |
| $21$ | $\{5\}$ | $E$ |
| $24$ | $\{1,5\}$ | $E$ |
| $26$ | $\{2,5\}$ | $E$ |
| $29$ | $\{3,5\}$ | $E$ |
| $32$ | $\{1,3,5\}$ | $E$ |

按最高选择位置分类：至多选到 21 时为 $E$；最高为 34 时禁止 21，得 $34+D$；最高为 55 时禁止 34，得 $55+E$；最高为 89 时禁止 55，且可选择或不选择 34，分别得 $123+D$ 与 $89+E$。所以完整平移像为

$$
C_3=E\ \cup\ (34+D)\ \cup\ (55+E)\ \cup\ (89+E)\ \cup\ (123+D).
$$

其五个互不交的数值块完整展开为

$$
\begin{aligned}
E&=\{0,3,5,8,11,13,16,18,21,24,26,29,32\},\\
34+D&=\{34,37,39,42,45,47,50,52\},\\
55+E&=\{55,58,60,63,66,68,71,73,76,79,81,84,87\},\\
89+E&=\{89,92,94,97,100,102,105,107,110,113,115,118,121\},\\
123+D&=\{123,126,128,131,134,136,139,141\}.
\end{aligned}
$$

这也给下面每个平移的实际合法词：在基本表的 $I$ 上，分别添加 $\{6\}$、$\{7\}$、$\{8\}$ 或 $\{6,8\}$，然后按定义 114.1 分窗并在最高非零窗口结束。所有集合无相邻位置，故是单个允许词的符号见证，而不是独立局部平移的拼合。五块共 $13+8+13+13+8=55$ 个不同整数，均小于 5040，配合命题 114.2 给出完整性。

前三问取平移 $c=0,13$；若第一问的截断 2 深度恰为 1，第三问取 $c=26$，称 A 分支，否则取 $c=11$，称 B 分支。它们的字面见证分别为

$$
0:\varnothing,\qquad
13:[000,010],\qquad
26:[001,001],\qquad
11:[010,100].
$$

以下所有颜色均指平移 $c$ 模 7，命中的隐藏余数是 $-c$，不能把两者符号混同。

模 16 的全部分支如下。A 分支的第一深度 1 给 $r\in\{2,6,10,14\}$；第二平移 13 是奇数，对这些候选深度都为零。第三平移 26 对 $r=6,14$ 分别给深度 4、3，单独确定；对 $\{2,10\}$ 都给深度 2，留下这一对，任意 $c\equiv6\pmod8$ 区分它。B 分支若第一深度为 4、3，分别已知 $r=0,8$；若为 2，留下 $\{4,12\}$，后两奇平移不区分，需 $c\equiv4\pmod8$。剩下第一深度为零的奇数候选：第二平移 13 给深度 4、3 时分别为 $r=3,11$；给深度 2 时留下 $\{7,15\}$，第三平移 11 对两者均深度 1，需 $c\equiv1\pmod8$；给深度 1 时留下 $\{1,5,9,13\}$，第三平移 11 分别在 $r=5,13$ 给深度 4、3，或留下深度 2 的 $\{1,9\}$，需 $c\equiv7\pmod8$。这些情形穷尽第一、第二、第三问的全部模 16 后验。

模 9 中，前三平移模 3 恰各一个值，因而恰有一问正深度，其余两问深度零。若该问深度为 2，余数已定；深度为 1 时的全部二元对与所需追加平移为

| 114.9 模 9 的正深度查询 | 精确命中余数 | 深度 1 后验 | 区分所需平移模 9 |
| --- | --- | --- | --- |
| $c=0$ | $0$ | $\{3,6\}$ | $3$ 或 $6$ |
| $c=13$ | $5$ | $\{2,8\}$ | $1$ 或 $7$ |
| A 的 $c=26$ | $1$ | $\{4,7\}$ | $2$ 或 $5$ |
| B 的 $c=11$ | $7$ | $\{1,4\}$ | $5$ 或 $8$ |

模 5 中两分支的平移都是 $\{0,3,1\}$，测试隐藏值 $\{0,2,4\}$。有命中即确定；全部错过留下 $\{1,3\}$，平移模 5 为 2 或 4 即可区分。模 7 中有命中也立即确定；没有命中时，A 已测颜色 $\{0,6,5\}$、未测 $U_A=\{1,2,3,4\}$，B 已测 $\{0,6,4\}$、未测 $U_B=\{1,2,3,5\}$。

现在给每个可能局部对足够多的真实未测颜色见证。模 16 所需各平移类可用下列词值：

| 114.9 模 16 需求 | $C_3$ 中的平移见证 | 按所列次序的模 7 颜色 |
| --- | --- | --- |
| $c\equiv6\pmod8$ | $94,102,110,118,126,134$ | $3,4,5,6,0,1$ |
| $c\equiv1\pmod8$ | $73,81,89,97,105,113,121$ | $3,4,5,6,0,1,2$ |
| $c\equiv4\pmod8$ | $52,60,68,76,84,92,100$ | $3,4,5,6,0,1,2$ |
| $c\equiv7\pmod8$ | $39,47,55,63,71,79,87$ | $4,5,6,0,1,2,3$ |

第一行与 $U_A$ 交得 $\{1,3,4\}$ 三色，其余三行含全部七色，故与 $U_B$ 都交四个颜色。每个数的基本表见证及添加偏移规则已给出；例如 $134=123+11$ 对应 $I=\{1,3,6,8\}$，真实词为 $[010,100,101]$。

模 9 的完整余数分组如下，它同时保留所有用于颜色选择的实际平移见证。

| 114.9 平移模 9 | 该类在 $C_3$ 中的全部平移 |
| --- | --- |
| $0$ | $0,18,45,63,81,126$ |
| $1$ | $37,55,73,100,118,136$ |
| $2$ | $11,29,47,92,110,128$ |
| $3$ | $3,21,39,66,84,102$ |
| $4$ | $13,58,76,94,121,139$ |
| $5$ | $5,32,50,68,113,131$ |
| $6$ | $24,42,60,87,105,123,141$ |
| $7$ | $16,34,52,79,97,115$ |
| $8$ | $8,26,71,89,107,134$ |

这些互不交的行合起来恰为前述五块。所需类对 $3/6,1/7,2/5,5/8$ 的模 7 颜色并分别为

$$
\{0,1,3,4\},\quad\{2,3,6\},\quad
\{1,2,4,5\},\quad\{1,2,4,5\}.
$$

与对应未测集相交后，A 的三种后验依次有 $\{1,3,4\},\{2,3\},\{1,2,4\}$，B 的三种后验依次有 $\{1,3\},\{2,3\},\{1,2,5\}$。每个未解决模 9 对至少有两个未测颜色。

模 5 所需平移类 2 或 4 有全部七色见证，按颜色 $0,1,2,3,4,5,6$ 的次序为

$$
42,29,37,24,32,47,34.
$$

它们模 5 依次为 $2,4,2,4,2,2,4$；在基本块中的表达依次为 $34+8,21+8,34+3,21+3,21+11,34+13,34+0$。因此所有四个未测颜色均能用一个允许词区分模 5 对。这些见证也在模 5 已知时提供任意所需补色词。

最后三问按如下确定性规则选择，可以固定按整数最小值破除所有选择歧义。先为尚未解决的模 9 对在其至少两色中取一词；再为模 16 对在其至少三色中取一个不同于先选颜色的词；再为模 5 对在其四色中取不同于已选颜色的词。已解决因子跳过。用仍未用的颜色补足三次查询，补色见证取上一段的七项表。每个指定词区分自己承担的原局部对，其它查询的附加信息只会缩小候选。总六问的模 7 颜色两两不同；有命中确定模 7，无命中推断唯一未测值。因此所有四个 CRT 坐标已定。这是定理 114.8 的单元素块充分情形，所需的 2、3、4 个颜色均附单词见证，没有任意局部中心 CRT 可用性的假设。模 7 在前三问已有命中也不妨继续这套至多六问的安排。

下界取定理 113.7 的七元实际轴族：固定模 720、变化模 7，任意成功字面词的其它分量条件于已选词都固定，每问至多排除一个模 7 候选，恒错不排除，故五问不足。这个下界覆盖完整 55 词及任意更长词，而非只覆盖本构造用到的子族。

若另一实际行是 $\lambda(2,3)$，$\lambda$ 为模 5040 单位，同一字面词的平移是 $\lambda c$。置 $x=\lambda^{-1}r$，有 $\gcd(r+\lambda c,5040)=\gcd(x+c,5040)$，所以同一策略转移。未证明实际性的抽象单位倍不因此进入实际源域。$\square$

### 114.5. 八个连续单位仿射中心与普遍短词等差列

**定理 114.10（八个中心的完整六问构造）。** 若一个已知实际行的三窗成功平移像 $C$ 包含

$$
b+d\{0,1,\ldots,7\},\qquad \gcd(d,5040)=1,
$$

则 $Q_3(5040;u,v)=6$。若这些平移全有至多两窗的词见证，同样有 $Q_2=6$。

证明。置

$$
x=-d^{-1}(r+b)\pmod{5040}.
$$

查询平移 $c=b+da$ 时，

$$
\gcd(r+c,5040)=\gcd(d(a-x),5040)=\gcd(x-a,5040).
$$

这保持全部局部截断深度，把问题变成完整余数 $x$ 与可用等值中心 $a\in\{0,\ldots,7\}$ 的模型；最后恢复 $r=-b-dx$。先问中心 1、2。第一回答的截断 2 深度恰为 1 时第三问取中心 3，称 A；否则第三问取中心 0，称 B。

A 的模 16 候选在第一问后为 $\{3,7,11,15\}$，第二中心 2 对它们都给零深度。第三中心 3 在 $x=3,11$ 分别给深度 4、3并确定；其它为深度 2 的对 $\{7,15\}$，指定收尾中心 7。

B 的模 16 分支完整如下：第一深度为 4 或 3 时分别已知 $x=1,9$；为 2 时留下 $\{5,13\}$，中心 2、0 都给零，指定收尾中心 5；为零时 $x$ 为偶数，第二中心 2 若给深度 4、3，分别已知 $x=2,10$；若给深度 2，留下 $\{6,14\}$，第三中心 0 对两者给深度 1，指定中心 6；若第二深度为 1，留下 $\{0,4,8,12\}$，第三中心 0 在 $x=0,8$ 给深度 4、3并确定，或留下深度 2 的 $\{4,12\}$，指定中心 4。没有其它模 16 分支。

模 9 中，两种前三中心组合都是模 3 的完整三个值，所以恰一问深度正。深度 2 即确定，深度 1 的全部情形为

| 114.10 模 9 正深度中心 | 深度 1 后验 | 指定收尾中心 |
| --- | --- | --- |
| $1$ | $\{4,7\}$ | $4$ |
| $2$ | $\{5,8\}$ | $5$ |
| A 的 $3$ | $\{0,6\}$ | $6$ |
| B 的 $0$ | $\{3,6\}$ | $3$ |

其余两问深度为零。模 5 有命中即确定；全部未命中时，A 的前三中心 $1,2,3$ 留下 $\{0,4\}$，指定中心 4；B 的 $1,2,0$ 留下 $\{3,4\}$，指定中心 3。

在 A，模 16 若未定，指定 7；模 9 若未定，指定 $4,5,6$ 中之一；模 5 若未定，指定 4。这些指定中心的并至多三个，均在 $\{7,4,5,6\}$，其模 7 颜色恰是四个未测颜色 $\{0,4,5,6\}$。用该四元集中任意余项补足三个不同中心并查询。在 B，指定中心的并也至多三个：模 16 用 $4,5,6$ 之一，模 9 用 $4,5,3$ 之一，模 5 用 3；它们全在 $\{3,4,5,6\}$，也是四个未测模 7 颜色。仍补足三个不同中心查询。相同指定中心只问一次，它可以同时解决几个局部对。指定查询之外的额外信息只会缩小后验，故三次收尾足以确定模 $16,9,5$。六个不同模 7 颜色再由命中或末值推断确定模 7，CRT 得全部 $x$。

这正体现定理 114.8 的联合块必要性：例如 B 中可同时出现模 16 对 $\{4,12\}$ 与模 9 对 $\{4,7\}$，在八中心族的未测颜色内，这两对都只有颜色 4 能区分。将两因子要求分配不同颜色的单元素块 Hall 会失败，但同一个实际中心 4 同时区分两对，也能区分模 5 的 $\{3,4\}$，合成一块即可。固定前三问的完整后验是乘积，故这些兼容局部后验可共同实现。

每个中心由假设中的一个实际词实现；归一化是读出等式，不改变真实隐藏源。下界沿用定理 113.7 的实际模 7 轴族，给精确六问。模 16 的八个底层对 $\{z,z+8\}$ 还说明任何分离中心族至少有八个不同中心：每对必须至少出现一端。这是可用中心族的基数障碍，不能替代六问的回合数下界。$\square$

**命题 114.11（所有行共有的十一项合法平移列）。** 对每个实际或抽象行 $(u,v)$，其完整三窗平移像包含

$$
b+kd\quad(0\le k\le10),\qquad b=u+3v,\quad d=2u+3v.
$$

此词恒等式不要求 $d$ 为单位；用定理 114.10 取得六问时才需要单位条件。

证明。八位置的系数对按次序为 $(0,1),(1,1),(1,2),(2,3),(3,5),(5,8),(8,13),(13,21)$。下表逐项给出总系数 $(1+2k,3+3k)$ 的一个无相邻偏移集合及其真实字面词。

| 114.11 项 $k$ | 偏移集合 $I$ | 总系数 $(A,B)$ | 低位到高位窗口词 |
| --- | --- | --- | --- |
| $0$ | $\{1,3\}$ | $(1,3)$ | $[010,100]$ |
| $1$ | $\{1,5\}$ | $(3,6)$ | $[010,001]$ |
| $2$ | $\{1,6\}$ | $(5,9)$ | $[010,000,100]$ |
| $3$ | $\{1,4,6\}$ | $(7,12)$ | $[010,010,100]$ |
| $4$ | $\{3,7\}$ | $(9,15)$ | $[000,100,010]$ |
| $5$ | $\{5,7\}$ | $(11,18)$ | $[000,001,010]$ |
| $6$ | $\{8\}$ | $(13,21)$ | $[000,000,001]$ |
| $7$ | $\{4,8\}$ | $(15,24)$ | $[000,010,001]$ |
| $8$ | $\{2,5,8\}$ | $(17,27)$ | $[001,001,001]$ |
| $9$ | $\{2,6,8\}$ | $(19,30)$ | $[001,000,101]$ |
| $10$ | $\{2,4,6,8\}$ | $(21,33)$ | $[001,010,101]$ |

每行将所选系数对相加即得所列总系数，值为 $(u+3v)+k(2u+3v)$。所列集合均无相邻偏移，词首位是零，至多三窗，末窗非零；前导和中间 $000$ 实际执行，末尾没有添加整零窗。因此每项都是一个共同字面词的符号见证。尤其末窗为 $100$ 或 $010$ 的行也可正值 End。本命题只给完整族中的一个显式子族，任何下界仍须针对全部允许词。$\square$

### 114.6. 五十二个实际相位与行变换的边界

**定理 114.12（八十个实际行中的五十二个六问行）。** 令 $w_j=T^j(2,3)\bmod5040$，$0\le j<80$，复用命题 105.5、108.2 的实际周期和标量返回结论。以下 52 个不同实际行满足 $Q_3(5040;w_j)=6$：

$$
\{j:0\le j<80,\ j\not\equiv3\pmod4,\ j\not\equiv1\pmod5\}
\ \cup\ \{36,39,76,79\}.
$$

其中前一族恰有 48 行，是 $2u+3v$ 为单位的全部实际行；另四行分别属于实际单位类 $(0,1)$ 和 $(34,-21)$。$(0,1)$ 的实际单位类还满足 $Q_2=6$。这些构造性上界不依赖假设 107.5。

证明。对 $w_j=(F_{3j+3},F_{3j+4})$，递推给

$$
d_j=2u+3v=F_{3j+7}.
$$

素数 $2,3,5,7$ 的 Fibonacci 零秩分别为 $3,4,5,8$：在这些指标的矩阵标量分别为 $1,2,3,6$，均是相应模数的单位；此前的正 Fibonacci 项分别取自 $1,1,2,3,5,8,13$，直接可见尚未被相应素数整除。命题 105.2 的标量子群论证于是给零指标恰为这些秩的倍数。因此 $3j+7\equiv1\pmod3$ 使 $d_j$ 总为奇数；被 3 整除恰在 $j\equiv3\pmod4$；被 5 整除恰在 $j\equiv1\pmod5$；被 7 整除恰在 $j\equiv3\pmod8$，后者已被模 4 的排除包含。故 $d_j$ 模 5040 为单位当且仅当显示的两个排除条件成立。

每个长度 20 的指标区间中，模 4 有三个允许值、模 5 有四个允许值；CRT 给 $3\cdot4=12$ 个允许指标。80 个指标包含四个这样的周期，所以为 48 行。对每一行，命题 114.11 的前八项和定理 114.10 给六问上界，定理 113.7 给匹配下界。实际 80 行的互异性以及

$$
T^{40}=1441I,\qquad T^{80}=I,\qquad1441^2=1\pmod{5040}
$$

直接复用命题 105.2、105.5 和 108.2 的既有相位结论；这里没有把新的相位枚举作为证明前提。原行 $(2,3)$ 的相位是 0，其另一个实际单位倍在 40，均已在此 48 行族内。

这是对行 $(2,3)$ 的单位类的严格扩展。例如 $w_2=(34,55)$，其 $b=199,d=233$，233 不被 $2,3,5,7$ 整除；显式短词给平移 $199+233k$，$0\le k\le7$。它与 $(2,3)$ 的行列式为 $2\cdot55-3\cdot34=8\not\equiv0\pmod{5040}$，所以不可能是其标量倍。

还可增加两个实际单位类。首先 $T(0,1)=(2,3)$，在有限可逆轨道上 $(0,1)$ 是一个实际模行。周期 80 将其定位为 $w_{79}$，标量返回给 $w_{39}=1441(0,1)$。下表在代表 $(0,1)$ 给出八个连续平移的至多两窗见证。

| 114.12 零首坐标平移 | 偏移集合 $I$ | 窗口词 |
| --- | --- | --- |
| $0$ | $\varnothing$ | 空词 |
| $1$ | $\{2\}$ | $[001]$ |
| $2$ | $\{3\}$ | $[000,100]$ |
| $3$ | $\{4\}$ | $[000,010]$ |
| $4$ | $\{2,4\}$ | $[001,010]$ |
| $5$ | $\{5\}$ | $[000,001]$ |
| $6$ | $\{2,5\}$ | $[001,001]$ |
| $7$ | $\{3,5\}$ | $[000,101]$ |

这些词各自合法，非空者末窗非零；以 $b=0,d=1$ 应用定理 114.10，得 $Q_2=Q_3=6$。同一词在实际单位倍行上平移共同乘单位，定理 114.9 末段的等式仍适用。此类的普遍等差列步长 $2u+3v$ 为 3 的单位倍，故不在前述单位步长族；它与 $(2,3)$ 的行列式为 2，也不属于原行的单位类。

其次使用模 5040 的整数代表 $(34,-21)$。精确递推为

$$
(34,-21)\xrightarrow{T}(-8,5)\xrightarrow{T}(2,-1)
\xrightarrow{T}(0,1)\xrightarrow{T}(2,3).
$$

所以它是实际相位 $w_{76}$，其另一个实际单位倍为 $w_{36}=1441(34,-21)$。负数只是模行的整数代表；相应真实源的下一权重仍是正 Fibonacci 整数，End 也在正整数上执行。八个权重在这些代表中写为

$$
-21,13,-8,5,-3,2,-1,1.
$$

连续平移 $-4,-3,\ldots,3$ 的具体三窗见证如下。

| 114.12 负代表平移 | 偏移集合 $I$ | 窗口词 |
| --- | --- | --- |
| $-4$ | $\{5,7\}$ | $[000,001,010]$ |
| $-3$ | $\{5\}$ | $[000,001]$ |
| $-2$ | $\{5,8\}$ | $[000,001,001]$ |
| $-1$ | $\{7\}$ | $[000,000,010]$ |
| $0$ | $\varnothing$ | 空词 |
| $1$ | $\{8\}$ | $[000,000,001]$ |
| $2$ | $\{6\}$ | $[000,000,100]$ |
| $3$ | $\{6,8\}$ | $[000,000,101]$ |

每行之和给所列平移；所有词按同一偏移规则合法。定理 114.10 用 $b=-4,d=1$ 给六问。该类的 $2u+3v=5$ 的单位倍不是单位，故也未包含在 48 行族中；其与 $(2,3)$ 的行列式为 $-144\not\equiv0\pmod{5040}$。

命题 105.2、105.5 给两个实际相位相差单位倍当且仅当指标差为 40 的倍数，因此新两类恰为 $\{39,79\}$ 和 $\{36,76\}$，没有把任意抽象单位倍都算成实际行。前一类指标是模 4 的 3，后一类是模 5 的 1，彼此不同且都在 48 行之外，总计 $48+4=52$。其上界完全由所列真实词给出，下界只需实际完整余数纤维。$\square$

**命题 114.13（实际行递推不保持完整短词像的单位仿射类型）。** 在模 5040 上，相邻实际行 $(2,-1)$、$T(2,-1)=(0,1)$ 的完整三窗平移像分别为整数区间的约化

$$
C_3(2,-1)=[-1,9]\cap\mathbb Z,
\qquad C_3(0,1)=[0,33]\cap\mathbb Z.
$$

因此不存在模 5040 单位 $\lambda$ 和平移 $b$ 使后一完整像等于 $b+\lambda C_3(2,-1)$。这不构成 $Q_3>6$ 的反例。

证明。对一般行 $w$，记 $a_i(w)=F_{i-1}u+F_iv$。Fibonacci 递推给

$$
a_i(Tw)=a_{i+3}(w).
$$

所以新行上的三窗词对应旧行中位置 $4,\ldots,11$ 的无相邻选择；字面上是在旧行先加一个 $000$，然后执行新行词，可能共四窗。前导零窗后还有非零末窗，End 合法；这不能当作旧行仍至多三窗的转移。

对 $(2,-1)$，八个权重为 $-1,1,0,1,1,2,3,5$。唯一负权是 $-1$，所以任意合法和至少为 $-1$。将相邻位置配成 $(1,2),(3,4),(5,6),(7,8)$，每对至多选一，给上界 $1+1+2+5=9$。位置 $5,6,7,8$ 的权重 $1,2,3,5$ 由引理 105.1 所用有限 Zeckendorf 区间性质给全部 $0,\ldots,7$；合法集合 $\{1\},\{4,6,8\},\{2,4,6,8\}$ 又分别给 $-1,8,9$。故完整像恰为 $[-1,9]$。

对 $(0,1)$，权重为 $1,1,2,3,5,8,13,21$，全非负；同样相邻配对给上界 $1+3+8+21=33$。位置 $2,\ldots,8$ 的 $F_2,\ldots,F_8$ 由同一有限区间性质给全部 $0,\ldots,F_9-1=33$，故完整像恰为 $[0,33]$。两区间宽度小于 5040，分别有 11、34 个不同余数。单位仿射变换是余数环的双射，不能改变像的基数，故所述等式不可能。

前面的逆相位链给这两行的实际性，周期定位分别为 78、79。第一行 $2u+3v=1$，第二行有定理 114.12 的两窗构造，所以两行事实上都已取得六问。这里反驳的只是用一个统一单位仿射置换把 $T$ 前后的完整短词像相同化，再自动转移三窗策略的主张。$\square$

**约定 114.14（尚未闭合的全行问题）。** 定理 114.12 所列族以外的 28 个实际行，本节未确定其 $Q_3$ 是否等于 6，亦未给出任何实际行 $Q_3>6$ 的下界。在假设 107.5 下它们仍满足推论 114.5 的 $6\le Q_3\le15$。尤其 $w_1=(8,13)$ 的普遍等差列只有 $b=47,d=55$，十一项全同余于 $2\pmod5$，在模 5 的四个未命中候选上仅重复该列不能取得更多信息；但完整族中 $[010]$ 的平移为 13，是另一模 5 颜色，所以这只是所选子族的不足，不能推出完整族的下界。

一种仍待证明的充分路线，是为每个剩余行找到三问，使每个可行历史都有定理 114.8 的局部对、足够未测颜色和实际单词联合分块见证；其它形态的完整六问策略也可能满足原问题。若要给反例，必须对完整 55 个成功词及恒错词建立保持全历史、具有一个实际存活源的超过六问对手。上述两个任务以及未知行的回合数均未由本节解决。

## 115. 未知实际相位的素数平方提升与完整历史

### 115.1. 共同单位图册与实际方向提升

**定义 115.1（模 $p^2$ 的实际提升图册）。** 令 $p$ 为任意素数，包括 2、3，取 $S=\mathbb Z/p^2\mathbb Z$、$\mathbb F=\mathbb F_p$。沿用定义 113.1 的原始完整 gcd、共同标签、正实际源及同源重置合同；此节下一行未知，候选行仅为实际三步轨道。为矩阵计算把行写成列向量，置

$$
Q=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad M=Q^3,
\qquad w_j=M^j(2,3)^{\mathsf T}.
$$

$\Omega_e$ 表示 $w_j$ 在模 $p^e$ 的共同单位射影轨道，$e=1,2$；这里射影类指幺模向量在同一个单位的乘法作用下的轨道。令

$$
L_e=|\Omega_e|=\frac{\rho(p^e)}{\gcd(\rho(p^e),3)},\qquad k=L_1,
$$

等式复用命题 105.2、推论 105.3，不预设秩从 $p$ 到 $p^2$ 如何增长。

固定一个实际模 $p$ 行为类 $\beta=[r_0:u_0:v_0]$。若 $v_0\ne0$，每个提升的 $v$ 在 $S$ 中是单位，用同一个 $v^{-1}$ 同时缩放三坐标，得唯一图册代表

$$
(R,U,1)=(r/v,u/v,1),\qquad
R=R_0+pz,\quad U=U_0+pt,
$$

其中 $0\le R_0,U_0<p$ 是固定整数代表，$z,t\in\mathbb F$。若 $v_0=0$，幺模性给 $u_0\ne0$，改用 $u$ 图册

$$
(R,1,V)=(r/u,1,v/u),\qquad
R=R_0+pz,\quad V=V_0+pt.
$$

图册归一化不声称该代表本身就是原始 Fibonacci 行，也不允许单独缩放余数或两行坐标。未知的高位 $t$ 必来自实际方向轨道，其支持由下一定理确定。

**定理 115.2（实际提升纤维的二择一及精确增长判据）。** 定义 115.1 中，固定任一实际基类 $\beta$，选它的方向的一个实际模 $p^2$ 提升 $w_*$。在 $v$ 图册写 $u_*/v_*=U_0+pt_*$；选整数代表使

$$
M^k=\alpha I+pK\pmod{p^2},\qquad
p\nmid\alpha,\qquad C=\alpha^{-1}K\pmod p.
$$

令 $q=(U_0,1)^{\mathsf T}$，

$$
\tau_v=(Cq)_1-U_0(Cq)_2,\qquad
\mathcal T_\beta=t_*+\mathbb F\tau_v.
$$

则 $\beta$ 上方的全部实际行为类恰为

$$
D_\beta=\mathbb F\times\mathcal T_\beta,
$$

坐标次序为 $(z,t)$。$u$ 图册以 $q=(1,V_0)^{\mathsf T}$ 和

$$
\tau_u=(Cq)_2-V_0(Cq)_1
$$

代替，结论相同。每个方向约化纤维均有 $L_2/L_1\in\{1,p\}$ 个元素，并且

$$
\begin{aligned}
\mathcal T_\beta=\mathbb F
&\ \Longleftrightarrow\ L_2=pL_1
\ \Longleftrightarrow\ p^2\nmid F_{3k},\\
\mathcal T_\beta=\{t_*\}
&\ \Longleftrightarrow\ L_2=L_1
\ \Longleftrightarrow\ p^2\mid F_{3k}.
\end{aligned}
$$

故实际行为提升数分别为 $p^2$ 或 $p$，不把单点 $t_*$ 默认为零。

证明。先核对“某实际行返回”等价于“矩阵标量返回”，这是排除额外任意行的关键。对 $w=(F_n,F_{n+1})^{\mathsf T}$，其中 $n=3j+3$，Cassini 给

$$
\det(w,Qw)=F_nF_{n+2}-F_{n+1}^2=(-1)^{n+1}.
$$

故 $w,Qw$ 在模 $p$ 和模 $p^2$ 上都是一组基。若 $M^\ell w=a w$ 为单位射影返回，$M^\ell$ 与 $Q$ 交换，便也有 $M^\ell Qw=aQw$；因此 $M^\ell=aI$。反向显然。没有实际行会因碰巧是某非标量矩阵的特征行而取得更短周期。

又有既有矩阵式

$$
Q^n=F_{n-1}I+F_nQ.
$$

标量返回指数构成子群，所以其最小正指数是 $\rho(p^e)$，限制为三步即为 $L_e$。把实际方向轨道写成相位指标模 $L_e$，约化映射就是 $j\bmod L_2\mapsto j\bmod L_1$，故 $L_1\mid L_2$，每个约化纤维大小均为 $L_2/L_1$。固定一个基方向后，其提升恰来自 $M^{kn}w_*$，没有其它实际相位可添入。

由于 $k$ 是模 $p$ 的标量返回，显示的 $\alpha,K$ 存在；$K$ 与 $Q$ 模 $p$ 交换，故 $C$ 也交换。模 $p^2$ 的平方零展开给

$$
(M^k)^n=\alpha^n(I+npC)\pmod{p^2}.
$$

取 $n=p$ 得 $M^{kp}$ 为标量，所以 $L_2\mid pL_1$。结合 $L_1\mid L_2$，比值只可能为 1 或 $p$。此展开对 $p=2$ 同样成立，无奇素数条件。

在 $v$ 图册，忽略不影响射影坐标的单位因子后，$I+npC$ 作用在 $(U_0+pt_*,1)$ 上，其第一坐标为 $U_0+p(t_*+n(Cq)_1)$，第二坐标为 $1+np(Cq)_2$。用 $(1+py)^{-1}=1-py$ 再归一化，得到

$$
U'=U_0+p\bigl(t_*+n[(Cq)_1-U_0(Cq)_2]\bigr).
$$

所以恰有 $t=t_*+n\tau_v$。$u$ 图册同算得 $t=t_*+n\tau_u$。若切向量为零，则 $Cq$ 是 $q$ 的标量倍。实际 Cassini 基在单位缩放后仍给 $q,Qq$ 一组模 $p$ 基；$C$ 与 $Q$ 交换，遂在两基向量上都是同一标量，故 $C$ 必标量。反向标量 $C$ 显然使切向量为零。非标量时 $\tau\ne0$，$n\in\mathbb F$ 遍历全部 $p$ 个高位，且全部由实际相位取得；标量时只有 $t_*$。

精确的 Fibonacci 判据可写得更直接。取

$$
\alpha=F_{3k-1},\qquad f=F_{3k}/p\in\mathbb Z,
\qquad K=fQ,\quad C=(f/\alpha)Q\pmod p.
$$

$\alpha$ 模 $p$ 是单位，$Q$ 非标量，其非对角元为 1。因此 $C$ 标量当且仅当 $f\equiv0\pmod p$，即 $p^2\mid F_{3k}$。在两图册上还得到

$$
\tau_v=(f/\alpha)(1-U_0-U_0^2),\qquad
\tau_u=(f/\alpha)(1+V_0-V_0^2).
$$

括号项在实际行上均非零：它们分别是 $-\det(q,Qq)$ 与 $\det(q,Qq)$，Cassini 基已保证单位。故上述条件对每个实际基方向相同，不能用抽象特征方向扩大或缩小纤维。

还须证 $z$ 的所有值确由实际正源实现。对每个已取得的实际方向高位 $t$，选一个实际原始行 $w=(u,v)$ 模 $p^2$。它有有限原始返回周期 $P_2$。在深度 $j=j_w+nP_2\ge1$，标签 $(1,\mathrm{true})$ 的整数像仍为

$$
[F_{3j+2},F_{3j+3}-1],\qquad\text{长度 }F_{3j+1}.
$$

由引理 105.1，允许两种初始化后区间中每个整数都有实际前缀；选一次足够大的 $j$ 使长度至少 $p^2$。该同深度纤维包含所有 $r\bmod p^2$。在 $v$ 图册为每个 $z$ 选择 $r=v(R_0+pz)$，在 $u$ 图册选择 $r=u(R_0+pz)$，即实现所有 $(z,t)$。不同实际行可以用不同返回深度，选中一个代表后全部重置仍固定它。仅有限行轨道的闭合并不证明这一步。

反向，任意实际提升的方向必在上述实际轨道，故其 $t$ 属于 $\mathcal T_\beta$，其归一化余数有唯一 $z$。两个图册点相同，原三元组恰相差单位 $v_2/v_1$ 或 $u_2/u_1$；图册点不同则由定理 104.7 不同未来。因此 $D_\beta$ 是实际行为提升纤维的精确双射描述。$\square$

**命题 115.3（三步提升的模 3 例外）。** 对 $p=3$，上述方向提升为单点，且 $L_2=L_1=4$。本结论不要求普遍的秩增长公式。

证明。$Q^2=Q+I$ 给 $Q^4=2I+3Q$。模 3 时 $Q^4$ 标量，$Q,Q^2$ 非标量，故 $Q$ 的射影阶是 4；$M=Q^3$ 的射影阶也为 4，所以 $k=4$。模 9 时

$$
M^4=(Q^4)^3=(2I+3Q)^3\equiv8I\pmod9,
$$

因展开的每个非常数项都被 9 整除。约化要求 $4\mid L_2$，此恒等式又使 $L_2\mid4$，故相等。等价地，$F_{3k}=F_{12}=144$ 被 9 整除。

若对某素数另有 $\rho(p^2)=p\rho(p)$，可代入定义得到

$$
\frac{L_2}{L_1}
=p\frac{\gcd(\rho(p),3)}{\gcd(p\rho(p),3)}.
$$

$p\ne3$ 时该比为 $p$，而 $p=3$ 且 $3\nmid\rho(p)$ 时三步取样消去这个增长因子。不能据此假设每个素数都有所写秩增长；定理 115.2 的条件 $p^2\mid F_{3k}$ 明确保留所有其它不增长情形，不排除任何尚未判定的例外素数。$\square$

### 115.2. 全整数进位与一个共同词的直线查询

**定理 115.4（实际提升上的精确进位读出）。** 固定定义 115.1 的一个基类 $\beta$ 及其图册。任一成功字面词有引理 106.2 的共同整数系数 $A,B$。在 $v$ 图册令

$$
B_0=R_0+AU_0+B\in\mathbb Z.
$$

若 $B_0\not\equiv0\pmod p$，该词在整个实际提升纤维上恒给 $\gcd=1$。若 $p\mid B_0$，须先除整个整数，再约化，定义

$$
c=\frac{R_0+AU_0+B}{p}\pmod p,\qquad a=A\bmod p.
$$

则该词恰在

$$
z+at+c=0
$$

时给 $\gcd=p^2$，否则给 $\gcd=p$。在 $u$ 图册相应取

$$
B_0=R_0+A+BV_0,\qquad
c=\frac{R_0+A+BV_0}{p}\pmod p,\qquad a=B\bmod p.
$$

每条 $z+at+c=0$，$a,c\in\mathbb F$，都由一个共同、合法、正值 End 的字面词模 $p^2$ 实现。实际全高位纤维 $\mathcal T_\beta=\mathbb F$ 时，可用仿射直线恰缺 $t=\text{常数}$ 这一平行类。

证明。在 $v$ 图册把三个坐标一同除以单位 $v$，真实终值满足

$$
N_{\rm final}\equiv v(R+AU+B)\pmod{p^2}.
$$

乘单位不变截断估值，且

$$
R+AU+B\equiv R_0+AU_0+B+p(z+At)\pmod{p^2}.
$$

底部非零时所有源深度为零；底部为零时除以 $p$，深度达到 2 当且仅当 $z+(A\bmod p)t+c=0$，否则恰为 1。$u$ 图册同理由 $N_{\rm final}\equiv u(R+A+BV)$ 得所列式。原始标签 $F_{p^2}$ 对三个 gcd 值 $1,p,p^2$ 分别为 $p^2,p,1$，只是双射重标；没有新增单位数据。$\gcd=p^2$ 表示真实终值为正的 $p^2$ 倍数，并非整数零。

高位系数必须参与进位。若选模 $p^2$ 代表

$$
A=a+pa_1,\quad B=b+pb_1,\quad0\le a,b<p,
\qquad R_0+aU_0+b=pq_0,
$$

则 $v$ 图册的完整进位为

$$
c=q_0+a_1U_0+b_1\pmod p.
$$

只保存 $a,b$ 会漏掉最后两项。$u$ 图册中若 $R_0+a+bV_0=pq_0$，则为 $c=q_0+a_1+b_1V_0$。这些等式也说明要先作整数除法，不能先把被除式约化为零再除。

代表选择不改变测试。把 $A,B$ 加上 $p^2$ 的倍数，只使可整除的 $B_0/p$ 加上 $p$ 的倍数。若 $v$ 图册的底部代表改成 $R_0+p\delta_R,U_0+p\delta_U$，则同一点的高位改为 $z-\delta_R,t-\delta_U$，进位改成 $c+\delta_R+a\delta_U$，所以直线左端不变。$u$ 图册同样以 $\delta_V$ 和系数 $B\bmod p$ 代替。两分母都为单位时，两图册由 $R\mapsto R/U,\ U\mapsto1/U$ 对应，且

$$
R/U+A+B/U=U^{-1}(R+AU+B),
$$

所以跨图册也是乘同一单位后的同一估值测试。直线的符号必须保留：$z+at+c=0$ 的图像是 $z=-at-c$，$c$ 不是把式子解成图像后的截距。

给定所需 $a,c\in\mathbb F$，在 $v$ 图册选 $A\equiv a\pmod p$，再选

$$
B\equiv-R_0-AU_0+pc\pmod{p^2}.
$$

则底部为零，整数进位模 $p$ 正是 $c$。在 $u$ 图册选 $B\equiv a\pmod p$，再取 $A\equiv-R_0-BV_0+pc\pmod{p^2}$。定理 106.3 在 $H=p^2$ 对这一个共同系数对给出一个首 $00$、末窗非零、长度至多 $L(p^2)$ 的真实词，对所有候选行同时成立。词可依赖已经供应的基类及希望测试的直线，但不能按未见的候选行重编。反向任意字面词在固定基类上不是常数，就是所列直线及其补集测试；非法接缝或不适当 End 则在共同标签上恒为 $\mathsf{err}$。

$\mathcal T_\beta=\mathbb F$ 时，方程中 $z$ 系数总为 1，故恰有全部非 $t$ 常数方向的直线。$\mathcal T_\beta=\{t_*\}$ 时，每条这样的直线只在纤维上留下一个 $z=-at_*-c$，而所有 $z$ 单点都可查询。$\square$

### 115.3. 所有既往回答的交与同一实际源

**定理 115.5（完整自适应历史的实际后验）。** 设

$$
\mathfrak h=((w_1,g_1),\ldots,(w_n,g_n))
$$

是一条确定性策略的记录分支，其中 $w_i$ 是这条分支上实际选择的字面词，$g_i\in\{1,p,p^2,\mathsf{err}\}$ 是完整 gcd 或错误回答。对每个实际模 $p$ 基类 $\beta$，用定理 115.2 的 $D_\beta=\mathbb F\times\mathcal T_\beta$ 和定理 115.4 的精确整数进位直线定义兼容集合 $S_i(\beta)$，则此历史的实际行为后验恰为

$$
\mathcal P_{\mathfrak h}(\beta)
=D_\beta\cap\bigcap_{i=1}^nS_i(\beta).
$$

这里后验指一致类的支持集，不预设概率律。$S_i(\beta)$ 的全部情形为

| 115.5 查询在基类上的类型 | 记录回答 | 兼容集合 |
| --- | --- | --- |
| 非法接缝或不适当 End | $\mathsf{err}$ | $D_\beta$ |
| 非法接缝或不适当 End | 任意数值 gcd | $\varnothing$ |
| 合法且底部表达式非零模 $p$ | $1$ | $D_\beta$ |
| 合法且底部表达式非零模 $p$ | $p,p^2$ 或 $\mathsf{err}$ | $\varnothing$ |
| 合法且底部表达式为零模 $p$ | $p^2$ | $D_\beta\cap\{z+a_it+c_i=0\}$ |
| 合法且底部表达式为零模 $p$ | $p$ | $D_\beta\setminus\{z+a_it+c_i=0\}$ |
| 合法且底部表达式为零模 $p$ | $1$ 或 $\mathsf{err}$ | $\varnothing$ |

如果 $\beta$ 仍未知，总支持集是全部兼容实际 $\beta$ 的这些后验的不交并。额外的源先验限制须另外相交，不能自动恢复为 $D_\beta$。

证明。必要性逐问应用定理 115.4：同一源经每次重置后取相同初始三元组，必须满足全部所记录条件。系数是记录中那一个词的共同系数，与该词选择时是否已经知道 $\beta$ 无关。

反向取任一点 $(z,t)$ 属于显示的交。由定理 115.2 为它选一个正值实际前缀代表，一次选定。该源第一回答符合表中条件。归纳假定前 $i-1$ 回答等于历史，则确定性策略必选择历史记录中的同一个 $w_i$；该源仍是原前缀，表中第 $i$ 项使其回答恰为 $g_i$。故这一个实际源实现整段自适应历史，证明充分性。空交恰表示该基类上不可能的记录分支；不能从其它未走分支拿约束来相交。不同模 $p$ 基类是不同约化类，所以尚未知基类时取不交并。$\square$

**命题 115.6（早期完整回答不会在得知基类后消失）。** 取任一实际底部方向及归一化余数 $R_0=0$ 的基类。即使在方向尚未知时，只作一次收费的空词 End，也可把后来已知基类内的纤维严格缩小。因此“已经得知 $\beta$”不蕴含“尚有完整新鲜先验 $D_\beta$”。

证明。空词系数 $A=B=0$，初始标签 $E=\mathrm{true}$ 且源正，所以合法并计一问。两图册的底部表达式都是 $R_0=0$，进位零，方程为 $z=0$。完整回答 $p^2$ 留下

$$
\{0\}\times\mathcal T_\beta,
$$

回答 $p$ 留下

$$
(\mathbb F\setminus\{0\})\times\mathcal T_\beta.
$$

两种回答约化到模 $p$ 的原始 gcd 都是 $p$，或原始 $F_p$ 标签都是 1；只记模 $p$ 输出就会丢掉它们的区别。若 $\mathcal T_\beta=\mathbb F$，上述支持大小分别为 $p$ 和 $p(p-1)$，都严格小于 $p^2$；若为单点，大小分别是 1 和 $p-1$，都严格小于 $p$，包括 $p=2$。所有列出的点均有正值实际代表，并以同一选定源产生其回答。后来学到基类只选择对应后验分支，不能抹去这项早期信息。$\square$

### 115.4. 新鲜纤维的成本复用与全局未决界

**推论 115.7（仅对完整新鲜提升先验的精确成本）。** 如果作为问题输入直接供应实际基类 $\beta$，并明确把完整 $D_\beta=\mathbb F\times\mathcal T_\beta$ 作为尚未被其它信息限制的先验，则原始模 $p^2$ gcd 查询识别其行为提升的精确最坏回合数为

$$
Q_{\rm fresh}(\beta)=p+|\mathcal T_\beta|-2
=\begin{cases}
2p-2,&\mathcal T_\beta=\mathbb F,\\
p-1,&\mathcal T_\beta=\{t_*\}.
\end{cases}
$$

每问至多 $L(p^2)$ 窗足够。这个数不是完整未知相位模 $p^2$ 问题的总最优值，也不是可以加到先前模 $p$ 成本上的阶段下界。

证明。把 $(z,t)$ 嵌入 $\operatorname{PG}(2,p)$ 为 $[X:Y:W]=[z:t:1]$，仍令 $O=[1:0:0]$。每个 $t\in\mathcal T_\beta$ 给径向线 $Y=tW$ 去掉 $O$ 后的全部 $p$ 个点。于是定理 113.3 的方向集在这里是

$$
\Omega_{\rm lift}=\{[t:1]:t\in\mathcal T_\beta\},
\qquad k_{\rm lift}=|\mathcal T_\beta|.
$$

这个方向集用于查询模型同构，不是声称模 $p$ 的 Fibonacci 原方向轨道有 $p$ 个方向。定理 115.4 的全部非常数查询是

$$
X+aY+cW=0,
$$

恰为所有不经过 $O$ 的射影直线；每条线由一个共同字面词实现，YES 是 $\gcd=p^2$，NO 是 $\gcd=p$。其它合法底部非零词和错误词只给常数。定理 115.2 已证明每个嵌入点都有实际正源代表。因此定理 113.3 对任意非空 $\Omega$ 的上界和受限覆盖下界全部适用，代入 $k_{\rm lift}=p$ 或 1 即得。下界对手最后的存活点也由同一实际代表实现；HPT 私人点引理的使用条件仍是定理 113.3 中构造的完整覆盖及 essential 线，没有另行套用全平面最优数。

实际未知相位策略可能先作许多查询，再在某一步得知基类。到那时正确先验是定理 115.5 的 $\mathcal P_{\mathfrak h}(\beta)$，命题 115.6 已给严格缩小的具体分支。早先回答可以同时帮助底部识别与高位提升，所以不能把本推论的成本加到模 $p$ 的最优成本而宣称总下界，也不能为了使用这个推论丢弃已有完整回答并称所得策略全局最优。$\square$

**约定 115.8（全局未知相位的剩余问题）。** 全部实际源上的模 $p^2$ 确定性最坏总成本，还需要在尚未知的实际基类不交并及其逐步受限提升纤维之间，构造一个保留完整历史的全局策略与匹配对手。本节未给该总最优值。实际方向是否增长则已有定理 115.2 的逐素数精确条件；它不假定 $\rho(p^2)=p\rho(p)$，模 3 已由命题 115.3 单独解决，其它满足标量不增长条件的情形仍被保留。这里的普通证明、既有分类的应用和有限词的显式见证，不把未解决的全行六问问题、全局未知相位最优值或计算效率作为附带结论。

## 追加锚（本行以下为增补区）

## 116. 规范数值的前缀、隐藏尾部与接缝密度

### 116.1. 来源、数值编码和终止信息的类型

**约定 116.1（沿用的对象与证明范围）。** 本节至 §118 给出普通数学推导。原始有序树、替换 $\rho$、组成观察 $c$、矩阵 $M$ 和数量观察 $q$ 沿用 §§2–5：

$$
\begin{gathered}
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\qquad
\rho(\alpha)=\beta,\quad\rho(\beta)=\langle\beta,\alpha\rangle,\\
\rho(\langle t_1,t_2\rangle)=\langle\rho(t_1),\rho(t_2)\rangle,\qquad
c\rho=Mc,\\
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
q(a,b)=2a+3b,\qquad
\mathbf e=(-1,1),\quad\mathbf r=(3,-2).
\end{gathered}
$$

这里 $\mathbb N$ 包含 0，$F_0=0,F_1=1$，$G_j=F_{j+2}$。记 $\mathscr C$ 为全部规范数值码：正值部分采用定义 104.2 的单位位、三位窗口与规范 End，另加一个结构零码。既有 Zeckendorf 唯一性给出 $\nu:\mathscr C\to\mathbb N$ 的双射。它观察的是数值；原始树 $t$ 的规范数值码为 $f(t)=\nu^{-1}(q(c(t)))$。不同树可以有相同的 $f(t)$，甚至不同组成也可以有相同的 $f(t)$。

沿用规范位移 $s$，即把规范表示的每个占用位置提高一格；其既有闭式见 [规范位移读出中的位移闭式](../../../D5/S1/Deficit/ZeckendorfDisplacementReading.lean)。为连接组成坐标，写

$$
n=\sum_{j\ge0}b_jG_j,\qquad
s(n)=\sum_{j\ge0}b_jG_{j+1},\qquad
\iota(n)=\sum_{j\ge0}b_jM^j\mathbf e.
$$

所有和都有限，$b_j\in\{0,1\}$ 且 $b_jb_{j+1}=0$。这些记号是既有规范位移、数量商和两次读数的坐标连接；本节不把它们另称为新的生成机制。以下证明的地位是普通理论，不是本批的 Lean 内核证明，也不作原创性认证。

**定义 116.2（裸观察与另外观察到的 End）。** 对每个 $n\in\mathbb N$，将其规范数位看成有限支持的无限序列，在最高非零位以上补零。$O_L(n)$ 只读单位位 $b_0$ 和随后 $L$ 个三位窗口，故共固定 $1+3L$ 个完整数位；$L=0$ 仍观察单位。若 $0\le L\le K$，截去后面的窗口给投影 $\pi_L^K$，从而

$$
O_L=\pi_L^K O_K,\qquad
\pi_L^L=\mathrm{id},\qquad
\pi_L^J\pi_J^K=\pi_L^K\quad(L\le J\le K).
$$

这些恒等式逐位成立，也在与 $q\circ c$ 复合后成立。提高 $L$ 始终观察同一个数值源；它没有施加 $\rho$。若另有证书确认已读前缀就在其实际规范 End 处结束，即已读到最后非零窗口，或单位 1 后立即 End，则未读尾部被证明全零，完整数值码的相容纤维为单点。只知道更高处的 End 位置而没有观察中间窗口，只给长度限制，不能据此断言单点。裸观察的高位补零约定本身不供应 End 证书。

对语义上的尾部，允许全零有限支持序列；删除它的首个零窗仍得同一全零尾部。对实际执行并终止的正值词，规则仍严格采用定义 104.2：单位初始化时 $\chi=\varepsilon$，每次合法读入窗口 $b$ 后

$$
\chi_{\mathrm{new}}=[b\ne\mathsf E],\qquad\mathsf E=000.
$$

这是当前 End 合法性，不能改成与旧 $\chi$ 作逻辑或。非空词的最后整个窗口须非零，最后一个单独数位可以为零；因此 $100$、$010$ 都可作末窗。$\varepsilon=1$ 的空窗口词可 End，$\varepsilon=0$ 的空窗口词不能作正值 End，结构零另外表示。首窗条件 $\varepsilon b_{0,0}=0$ 只在至少有一个窗口时才有该下标。

为说明单位在提升中的位置，令 $R=M^3$，对三位窗口 $b$ 置 $d_b=(b_0+b_2,b_1+b_2)$，对窗口词 $w=(b_0,\ldots,b_{L-1})$ 置 $x(w)=\sum_{j<L}R^jd_{b_j}$。由于 $M\mathbf e=(1,0)$，且 $M^{j+1}\mathbf e=c(\rho^j(\alpha))$，合法完整码满足

$$
\iota(\nu(\varepsilon;w))=\varepsilon\mathbf e+x(w),\qquad
\nu(\varepsilon;w)=\varepsilon+q(x(w)).
$$

证明就在每个占用位置上应用上述等式后求和；单位不能从第一式删去。特别地 $\iota(0)=0$、$\iota(1)=(-1,1)$。若 $w$ 非空，在它前面插入一个零窗口而保留单位字段，$x(\mathsf Ew)=M^3x(w)$，所以数值变成

$$
n\longmapsto\varepsilon+s^3(n-\varepsilon).
$$

例如 $4=1+3$ 的码是 $(1;010)$，插入零窗得到 $1+13=14$；整体位移却是 $s^3(4)=s^3(1)+s^3(3)=5+13=18$，这里的相加是两个不相邻位置的逐位计算。若 $w$ 为空，插入完整零窗不会创造新的正值规范 End 码，补零语义中的数值仍只是原单位。

组成矩阵的可逆性也不恢复原始树。$\langle\alpha,\beta\rangle$ 与 $\rho(\beta)=\langle\beta,\alpha\rangle$ 组成相同，前者却不在 $\rho(\mathcal T)$ 中：它不是叶子，也不是 $\rho(\beta)$；若它等于一个二叉来源的像，其左子树就要求 $\rho(t)=\alpha$，而任何像都不是 $\alpha$。因此整数矩阵 $M^{-1}$ 所恢复的组成不构成有序来源的逆。来源封装若采用 §8.4 的展开映射 $E:\mathcal A\to\mathcal T$ 和截面 $\zeta:\mathcal T\to\mathcal A$，则仍须 $E\zeta=\mathrm{id}$；这才给 $E\widehat\rho^k=\rho^kE$，其中 $\widehat\rho=\zeta\rho E$。观察 $O_L\circ q\circ c\circ E$ 的投影相容性与这个展开恒等式类型不同，不能互相代替。

**约定 116.3（实际像上的任务解码与正值算术域）。** 复用 §73.1 的实际像原则。给集合及映射 $O:X\to B$、$\tau:X\to Y$，令 $I=O(X)$，$\bar O:X\to I$。存在唯一 $D_I:I\to Y$ 使 $\tau=D_I\bar O$，当且仅当

$$
O(x)=O(x')\ \Longrightarrow\ \tau(x)=\tau(x').
$$

为说明空域边界，必要性直接由复合式成立。反向，对每个 $b\in I$，关系“存在 $x$ 满足 $O(x)=b$ 且 $\tau(x)=y$”给出恰一个 $y$：存在性来自实际像，唯一性来自纤维恒值。用这个唯一值定义 $D_I$，便得到因子化；每个 $b$ 都被达到，故解码器唯一。$X=\varnothing$ 时 $I=\varnothing$，空函数仍成立。若要求把解码器定义在整个 $B$，准确的附加条件是 $B=\varnothing$ 或 $Y\ne\varnothing$：有 $y_0\in Y$ 时在 $B\setminus I$ 取常值 $y_0$；$B=\varnothing$ 时使用空函数；反向若 $B$ 非空且有总解码器，取其任一输出就得到 $Y$ 的元素。特别地 $X=Y=\varnothing$、$B$ 为单点时，纤维恒值却没有这样的总解码器。

这个原则只判某任务是否由观察决定。若还需在观察商上执行动作 $A:X\to X$，须另证 $O(x)=O(x')$ 蕴含 $O(Ax)=O(Ax')$；实际像原则才给出商上的更新。§5.1 的两组成 $(3,0)$、$(0,2)$ 同读 6，而下一读数分别为 9、10，已经阻止把任意来源的 $\rho$ 更新交给单个数值或其裸前缀。

将规范码用于约数或对数目标时，固定正值子域

$$
\mathscr C_+=\{C\in\mathscr C:\nu(C)\ge1\},\qquad
\mathcal Z(C)=\sum_{\substack{D\in\mathscr C_+\\\nu(D)\mid\nu(C)}}\frac1{\nu(D)},\qquad
\mathcal E(C)=\log\nu(C)\quad(C\in\mathscr C_+).
$$

若 $n=\nu(C)\ge1$，正约数有限，$d\mapsto n/d$ 是其自身的双射，故 $\mathcal Z(C)=\sum_{d\mid n,d>0}1/d=\sigma(n)/n$。既有[正整数资源目标的最优性](../../../D5/S3/Arith/GoldenResourceOptimalInteger.lean)因而只在 $\mathscr C_+$ 上运输。零码不在这个目标的定义域：每个正整数都整除 0，所得倒数和发散，而且实对数 $\log0$ 没有这里要求的含义。此处没有增加约数估计或全局 Robin 不等式。

### 116.2. 每个固定前缀的精确尾部参数化

**定理 116.4（接缝调整后的规范柱集及组成提升）。** 设 $w=(w_0,\ldots,w_{m-1})$ 是内部无相邻 1 的二进前缀。若 $m=0$，约定 $V=0,\sigma=0$；若 $m\ge1$，置

$$
V=\sum_{j<m}w_jG_j,\qquad\sigma=w_{m-1}.
$$

令 $h=m+\sigma$，$\mathcal C_w\subseteq\mathbb N$ 为补零规范数位的前 $m$ 位等于 $w$ 的全部数。则

$$
\begin{aligned}
\mathbb N&\longrightarrow\mathcal C_w,&t&\longmapsto n_t=V+s^h(t)
\end{aligned}
$$

是严格递增双射，包括 $t=0$，并且

$$
\iota(n_t)=\iota(V)+M^h\iota(t).
$$

特别地，最低 $m$ 位全零的柱集为 $\mathcal H_m=s^m(\mathbb N)$；$m=0$ 时就是整个 $\mathbb N$。

证明。若 $\sigma=0$，未固定数位从位置 $m$ 起可以任意取一个有限支持非相邻序列。若 $\sigma=1$，位置 $m$ 强制为零，未固定数位从 $m+1$ 起可以任意取这样的序列。删除固定前缀及这个强制零位，再把剩余位置降低 $h$，得到唯一的规范整数 $t$。反向将 $t$ 的规范数位提高 $h$ 后与 $w$ 合并，两部分支持不交且接缝不相邻，故显示的和本身就是规范表示，没有额外归一化。两个操作互逆。全零尾部给 $t=0$，不能删掉；$m=0$ 时两操作都是恒等。对同一数位分解逐项使用 $M^{h+j}\mathbf e=M^hM^j\mathbf e$ 就得到组成提升式。

下面同时给出单调性和下一条密度所需的既有位移计算。令 $\varphi=(1+\sqrt5)/2$、$\theta=\varphi^{-1}$、$\psi=-\theta$。Fibonacci 恒等式 $F_{k+1}-\varphi F_k=\psi^k$ 在 $k=0,1$ 成立，两边同满足 Fibonacci 递推，故归纳成立。于是

$$
\delta(t):=s(t)-\varphi t=\sum_{j\ge0}b_j\psi^{j+2}.
$$

有限个正项的和严格小于 $\theta^2+\theta^4+\cdots=\theta$；有限个负项的绝对值和严格小于 $\theta^3+\theta^5+\cdots=\theta^2$。所以

$$
-\varphi^{-2}<\delta(t)<\varphi^{-1}.
$$

因 $\theta+\theta^2=1$，有 $0<\varphi(t+1)-(s(t)+1)<1$，从而复得既有闭式

$$
s(t)=\lfloor(t+1)\varphi\rfloor-1.
$$

相邻输入使取整前的数增加 $\varphi>1$，故 $s$ 严格递增，各次迭代也严格递增，固定平移 $V$ 保持这一性质。最后，位移后的数位仍然规范，逐位 Fibonacci 递推给 $s^2(t)=t+s(t)$，并归纳给

$$
s^h(t)=F_{h-1}t+F_hs(t)\quad(h\ge1),\qquad s^0(t)=t.
$$

这些闭式是所引用位移结果及 Fibonacci 递推在本柱集证明中的应用。$\square$

**定理 116.5（自然密度与条件细化比）。** 对定理 116.4 的每个固定前缀 $w$，当 $X\to\infty$ 时有

$$
|\mathcal C_w\cap[0,X)|=\varphi^{-h}X+O_w(1),\qquad
d(\mathcal C_w)=\varphi^{-h}.
$$

若 $b$ 是一个与输入接缝 $\sigma$ 相容的 $r$ 位扩展，输出接缝为 $\tau$，则

$$
\lim_{X\to\infty}
\frac{|\mathcal C_{wb}\cap[0,X)|}{|\mathcal C_w\cap[0,X)|}
=\frac{d(\mathcal C_{wb})}{d(\mathcal C_w)}
=\varphi^{-(r+\tau-\sigma)}.
$$

$r=0$ 时取 $\tau=\sigma$。上述误差是对固定前缀的有界误差，不断言对所有前缀长度一致。

证明。$h\ge1$ 时，上一证明和 $F_{h-1}+\varphi F_h=\varphi^h$ 给

$$
s^h(t)=\varphi^h t+F_h\delta(t),\qquad |F_h\delta(t)|<F_h.
$$

固定 $B=F_h$，所有满足 $V+\varphi^ht+B<X$ 的非负整数 $t$ 都被计入；被计入的 $t$ 必满足 $V+\varphi^ht-B<X$。任一实数阈值以下的非负整数个数与该阈值的非负部分相差至多 1。因此在 $X$ 足够大时，这两个界的计数均为 $\varphi^{-h}X+O(V\varphi^{-h}+B\varphi^{-h}+1)$。双射给出所需计数，除以 $X$ 得密度。$h=0$ 时直接数 $t<X-V$，在本情形 $V=0$，同样成立。扩展后的前缀长 $m+r$，末位为 $\tau$，其密度为 $\varphi^{-(m+r+\tau)}$；原密度正，故取两个计数渐近式的比就得到公式。$\square$

**推论 116.6（三位与六位扩展的接缝权重）。** 这些密度比对应“在 $[0,X)$ 均匀取整数，再条件于给定前缀，最后令 $X\to\infty$”的合同。输入接缝为 0 时，三位模式 $000,100,010$ 各有条件密度 $\varphi^{-3}$，$101,001$ 各有 $\varphi^{-4}$。输入接缝为 1 时只允许 $000,010,001$，对应 $\varphi^{-2},\varphi^{-2},\varphi^{-3}$。对六位扩展，输入接缝为 0 时有 13 个末位为零的词，每个条件密度 $\varphi^{-6}$，以及 8 个末位为一的词，每个 $\varphi^{-7}$；输入接缝为 1 时则分别是 8 个、5 个，条件密度分别为 $\varphi^{-5}$、$\varphi^{-6}$。

证明。长度 $r$ 的合法位词按末位分成两类。输入接缝为 0 时，末位为零的数量为 $F_{r+1}$，末位为一的数量为 $F_r$：末位零可以接任何长 $r-1$ 的合法词；末位一强制前一位零，再取长 $r-2$ 的合法词，配合长度 0、1 的基础情形归纳。输入接缝为 1 强制首位零，$r\ge1$ 时余下是长 $r-1$ 的自由合法词。代入 $r=3,6$ 并使用定理 116.5 即得；六位的两个归一化恒等式为

$$
13\varphi^{-6}+8\varphi^{-7}=1,\qquad
8\varphi^{-5}+5\varphi^{-6}=1.
$$

它们也由合法扩展对子柱集的不交穷尽及正密度直接推出。没有对全体 $\mathbb N$ 假定均匀概率，更没有给组成或树结构指定先验。若另知最多 $K$ 窗，已经读了 $L$ 窗、$0\le L\le K$，单位固定且未观察 End，剩余 $r=3(K-L)$ 位的合法补全数为 $F_{r+2}$（接缝 0）或 $F_{r+1}$（接缝 1）；$r=0$ 时两者都是 1。补全后裁去最高整零窗才得到规范完整码；若只允许正值，恰在已固定部分连同单位全零时删去唯一的零补全。这个有限上界合同与上面的开放柱集不同。$\square$

**命题 116.7（位置双射不运输算术性质）。** 规范位移及前缀密度不蕴含加法、乘法、素性或约数权重的保持。更具体地，对每个素数 $p$ 和每个有限裸观察 $O_L$，存在合数 $n$ 满足 $O_L(n)=O_L(p)$。

证明。直接有 $s(2+2)=s(4)=7\ne6=s(2)+s(2)$，且 $s(2\cdot2)=7\ne9=s(2)s(2)$；$s(13)=21$ 还将素数送到合数。这些例子已排除把位置双射理解成通常算术同构。

为证后一断言，模 $p$ 的 $M$ 可逆，因为行列式为 $-1$，故在有限群中有正阶 $P$。于是 $M^{kP}=I$ 模 $p$，由 §105.2 的矩阵式得到 $p\mid F_{kP}$。取 $j=kP$ 大于所有已观察的 Fibonacci 指标，并至少比 $p$ 的最高规范指标高两格。此时 $p+F_j$ 的两个数位支持不交且不相邻，故规范表示直接拼接，全部已观察位及单位位与 $p$ 相同。同时

$$
p+F_j=p\left(1+\frac{F_j}{p}\right)
$$

的两个因子都至少为 2，所以是合数。这里复用的是既有模返回及规范唯一性。结论只针对给定素数的有限裸前缀；有 End、规模限制或其它证书时须使用相应收缩后的纤维，也没有断言每个任意前缀都含素数。$\square$

## 117. 固定数量的非负组成容量与前缀的依赖联合源

### 117.1. 两次读数的坐标复用及其适用域

**约定 117.1（组成差异记录及符号）。** 对 $\mathbf v\in\mathbb Z^2$ 且 $n=q(\mathbf v)\ge0$，令

$$
z=q(M\mathbf v),\qquad \kappa(\mathbf v)=s(n)-z.
$$

§5.4 的两次读数逆式给

$$
\iota(n)=(5n-3s(n),\ 2s(n)-3n),\qquad
\mathbf v=\iota(n)+\kappa(\mathbf v)\mathbf r.
$$

确实，定义 116.1 给 $q\iota(n)=n$、$qM\iota(n)=s(n)$，代入同一逆矩阵即得第一式；而 $q\mathbf r=0$、$qM\mathbf r=-1$ 给第二式。这里 $(n,\kappa)$ 只是既有 $(n,z)$ 的可逆换坐标 $z=s(n)-\kappa$，不另构造一个恢复来源树的机制。

为固定符号，复用既有[黄金相位亏量](../../../D5/S1/Deficit/GoldenPhaseDeficit.lean)及[带符号进位路径](../../../D5/S1/Deficit/ChargedCarryPath.lean)，记

$$
\mathfrak c(a,b)=s(a)+s(b)-s(a+b)\quad(a,b\in\mathbb N).
$$

其值在 $\{-1,0,1\}$。在当前坐标中，这可由 $s(n)=\lfloor\varphi n+\varphi^{-1}\rfloor$ 直接核对：若 $f_n=\{\varphi n+\varphi^{-1}\}$，则

$$
\mathfrak c(a,b)=-\lfloor f_a+f_b-\varphi^{-1}\rfloor.
$$

括号内在 $(-1,2)$ 中，故取整只有三种可能。由于 $\ker q=\mathbb Z\mathbf r$，对数量为零的差向量再施加 $qM$，得到符号恒等式

$$
\iota(a)+\iota(b)-\iota(a+b)=-\mathfrak c(a,b)\mathbf r.
$$

若用黄金整数坐标 $\xi^2=\xi+1$ 和 $\Lambda(a,b)=(a+2b)+(2a+3b)\xi$，则 $\Lambda(\mathbf r)=-1$，故上式的 $\Lambda$ 像为 $+\mathfrak c(a,b)$。$\Lambda$ 的坐标矩阵行列式为 $-1$；它在 $a+b\xi$ 坐标下是乘 $\xi^3$ 的加法格同构，不是保持通常乘法单位的环同构。这与既有路径总电荷和规范终点的一致性相容。

再由 $M^2=M+I$，序列 $q(M^k\mathbf r)$ 从 $0,-1$ 开始按 Fibonacci 递推，因此

$$
q(M^k\mathbf r)=-F_k,\qquad
q(M^k\mathbf v)=s^k(n)-F_k\kappa\quad(k\ge0).
$$

所以 $qM^k$ 作用于两个规范加数与规范和的差时，给 $+F_k\mathfrak c(a,b)$。对数量非负的两个组成，来源相加的记录是 $\kappa_1+\kappa_2-\mathfrak c(n_1,n_2)$。这些均是同一两读数恢复与既有进位的直接应用；两个加数的三值净修正不限制任意来源的 $\kappa$ 只能取三个值，也不限制多次加法的总修正只有三值。

**命题 117.2（有向组成更新的守卫与不变域）。** 在 $q(\mathbf v)\ge0$ 的有向组成域上，记录坐标的一步更新是带守卫的部分映射：只有

$$
n'=s(n)-\kappa\ge0
$$

时，才可写

$$
(n,\kappa)\longmapsto\bigl(n',\ s(n')-n-n'\bigr).
$$

它在下列锥上是总映射，该锥同时在组成相加下封闭：

$$
\mathcal V_+=\{\mathbf v\in\mathbb Z^2:q(\mathbf v)\ge0,\ q(M\mathbf v)\ge0\}
\longleftrightarrow
\{(n,\kappa):n\in\mathbb N,\ \kappa\le s(n)\}.
$$

原始非负组成域 $\mathbb N^2$ 也在 $M$ 下不变。

证明。下一次的当前读数是 $n'$，再下一次是 $q(M^2\mathbf v)=n+n'$；按记录定义便得更新式。若 $n,n'\ge0$，更新后的两个读数 $n',n+n'$ 仍非负，故 $M$ 保持 $\mathcal V_+$。$q$ 和 $qM$ 都线性，组成相加也保持两项不等式。由 $n'=s(n)-\kappa$ 得记录中的准确域。$M(a,b)=(b,a+b)$ 直接保持 $\mathbb N^2$。

仅有 $q(\mathbf v)\ge0$ 不够：$\mathbf v=\mathbf r=(3,-2)$ 满足 $q\mathbf v=0$，却有 $qM\mathbf v=-1$。因此不能省去一步守卫，或把这个半平面说成不变域。$\square$

### 117.2. 非负组成的完整区间与最少辅助记录

**定理 117.3（固定数量的实际非负组成像）。** 对每个 $n\in\mathbb N$，令

$$
P_n=\{(a,b)\in\mathbb N^2:2a+3b=n\},\qquad
\ell_n=s(n)-\left\lfloor\frac{5n}{3}\right\rfloor,\quad
u_n=s(n)-\left\lceil\frac{3n}{2}\right\rceil.
$$

在 $P_n$ 上，下一读数 $z=3a+5b$ 恰遍历每个整数

$$
\left\lceil\frac{3n}{2}\right\rceil\le z\le
\left\lfloor\frac{5n}{3}\right\rfloor,
$$

且每个恰有一个原像。等价地，$\kappa=s(n)-z$ 给出双射

$$
P_n\ \longleftrightarrow\ [\ell_n,u_n]\cap\mathbb Z,
$$

其逆为

$$
a=5n-3s(n)+3\kappa,\qquad
b=2s(n)-3n-2\kappa.
$$

下端超过上端时区间为空。组成数准确为

$$
\begin{aligned}
C(n):=|P_n|
&=\max\left(0,\left\lfloor\frac{5n}{3}\right\rfloor
-\left\lceil\frac{3n}{2}\right\rceil+1\right)\\
&=\left\lfloor\frac n6\right\rfloor+1-\mathbf1_{\{n\equiv1\pmod6\}}.
\end{aligned}
$$

其中 $P_0=\{(0,0)\}$ 是一个空组成，$P_1=\varnothing$，每个 $n\ge2$ 的纤维非空。若来源限定为原始非空树，则数量 0、1 都无来源，数量 $n\ge2$ 的组成类数仍是 $C(n)$。

证明。复用 §5.4 的行列式为 1 的观察矩阵，有整数逆式

$$
a=5n-3z,\qquad b=2z-3n.
$$

两坐标非负当且仅当 $3n/2\le z\le5n/3$。反过来，区间中的每个整数 $z$ 都给非负整数 $a,b$，且逐项代回有

$$
2(5n-3z)+3(2z-3n)=n,\qquad
3(5n-3z)+5(2z-3n)=z.
$$

所以整个整数区间无遗漏地给出所有组成，也没有额外奇偶限制。$\kappa=s(n)-z$ 反转两个端点，并代回上述逆式，就得记录区间和逆映射。

为完成包括小值在内的计数，写 $n=6h+r$，$0\le r<6$。端点差加一是

$$
h+\left(\left\lfloor\frac{5r}{3}\right\rfloor-
\left\lceil\frac{3r}{2}\right\rceil+1\right).
$$

六个括号值逐项为 $1,0,1,1,1,1$：相应的下、上端点分别为 $(0,0),(2,1),(3,3),(5,5),(6,6),(8,8)$。因此显示的六余数公式成立；唯一空纤维是 $h=0,r=1$，$h=r=0$ 给一个组成。任意非零 $(a,b)\in\mathbb N^2$ 都能用 $a$ 个 $\alpha$ 与 $b$ 个 $\beta$ 排成一个非空叶列，再任取二叉括号实现为原始有序树。空组成不能由非空树实现；此外没有新增限制。这计的是组成类，排列或括号不同的树仍可在同一类中。$\square$

**定理 117.4（外部给定数量时的尖锐辅助容量）。** 固定并外部供应一个 $n$，假设 $P_n\ne\varnothing$。考虑辅助记录 $R:P_n\to A$，只计实际记录像 $R(P_n)$ 的大小，解码器另行获知 $n$。以下任一任务要求的最小记录像大小都恰为 $C(n)$：恢复组成；给出下一次数值 $qM\mathbf v$；给出全部数值未来；或仅给出预先固定的某一次 $q(M^k\mathbf v)$，其中 $k\ge1$。若用固定长度二进记录，最少位数是 $\lceil\log_2 C(n)\rceil$。

证明。固定 $n$ 后，定理 117.3 给不同 $\kappa$ 对应不同的下一读数 $s(n)-\kappa$。若记录把两个这样的组成合并，任何记录解码器都不能在这两个组成上给正确的下一读数，因此至少要 $C(n)$ 个实际记录值。恢复组成当然不能合并不同组成，恢复全部未来也不能合并下一读数不同的组成。

对单个指定的 $k\ge1$，§5.4 的 Fibonacci 递推具体给

$$
q(M^k\mathbf v)
=F_{k-1}n+F_k\bigl(s(n)-\kappa\bigr).
$$

$F_k>0$，故在固定 $n$ 下这仍严格区分每个不同 $\kappa$，得到同一下界。反向只记录区间排名 $\kappa-\ell_n\in\{0,\ldots,C(n)-1\}$ 即可：已知 $n$ 就知道 $\ell_n$，恢复 $\kappa$ 后由定理 117.3 恢复组成，再由此式给全部未来。它同时达到每个任务的下界。固定长 $b$ 位有至多 $2^b$ 个记录，取最小满足 $2^b\ge C(n)$ 的 $b$ 即得位数；$C(n)=1$ 时为零位。若 $P_n$ 为空，则没有须被记录的实际输入，其记录像为空，不对零作对数。

这是一项固定输入数量的记录像下界。它没有计入取得记录的查询、在线更新所需的中间状态，也不是一个具有 $C(n)$ 态的全局自主机器，因为 $\rho$ 会改变 $n$。$\square$

**命题 117.5（规范截面与原始组成的两个边界实例）。** $n=4$ 时，原始非负组成唯一为 $(2,0)$，其 $\kappa=1$；规范截面 $\iota(4)=(-1,2)$ 不在 $P_4$。而 $n=6h$ 时 $C(6h)=h+1$，故固定数量所需的辅助记录容量在不同数量之间无界。

证明。$4=G_0+G_2=1+3$，故 $s(4)=G_1+G_3=2+5=7$，$\iota(4)=\mathbf e+M^2\mathbf e=(-1,2)$。定理 117.3 的下一读数区间只有整数 6，给 $(a,b)=(2,0)$ 和 $\kappa=7-6=1$。对 $6h$，完整组成列为

$$
(a,b)=(3h-3t,2t),\qquad t=0,\ldots,h,
$$

其下一读数为 $9h+t$，互不相同，因此恰有 $h+1$ 类。特别地，$n=6$ 的 $(3,0)$ 与 $(0,2)$ 具有相同的整个规范数值码，却有记录 1 与 0。再多读这个数值码也不能分离它们；须观察来源组成或下一数值等额外关系。$\square$

### 117.3. 前缀尾部与组成记录的实际联合支持

**定理 117.6（非负组成上的依赖尾部族）。** 采用定理 116.4 的 $w,V,h$，置 $n_t=V+s^h(t)$，令

$$
X_w=\{\mathbf v\in\mathbb N^2:q(\mathbf v)\in\mathcal C_w\}.
$$

则实际联合源有双射

$$
X_w\ \longleftrightarrow\
\{(t,k):t\in\mathbb N,\ k\in\mathbb Z,\ \ell_{n_t}\le k\le u_{n_t}\},
$$

其中前向映射取 $q(\mathbf v)$ 的唯一尾部参数 $t$ 及 $k=\kappa(\mathbf v)$，反向映射为

$$
\mathbf v=\iota(V)+M^h\iota(t)+k(3,-2).
$$

只保留非空原始树的组成时，再去掉 $n_t=0$ 的点；$n_t=1$ 已因记录区间为空而没有点。若改用所有满足 $q(\mathbf v)\ge0$ 的有向整数组成，并保持同一数值前缀条件，则记录坐标不受区间限制，所有 $k\in\mathbb Z$ 都出现。

证明。给 $\mathbf v\in X_w$，定理 116.4 唯一写 $q(\mathbf v)=n_t$，并给

$$
\iota(n_t)=\iota(V)+M^h\iota(t).
$$

$\mathbf v-\iota(n_t)$ 属于 $\ker q=\mathbb Z(3,-2)$；这个核式也可由 $2a+3b=0$ 先推出 $3\mid a$，再写 $(a,b)=k(3,-2)$ 得到。施加 $qM$，利用 $qM(3,-2)=-1$，系数就唯一等于 $s(n_t)-qM\mathbf v=\kappa(\mathbf v)$。定理 117.3 说明这个向量非负当且仅当 $\ell_{n_t}\le k\le u_{n_t}$。

反向给任何满足这些条件的 $(t,k)$，显示的向量等于 $\iota(n_t)+k\mathbf r$，所以数量为 $n_t$、记录为 $k$，且由同一定理两坐标非负。再取前向映射恢复原 $t,k$。这同时证明满射、单射和两个复合为恒等。非负域上数量为 0 只可能是 $(0,0)$，所以去掉它准确表达非空来源条件。在有向域中，每个整数 $k$ 都给整数向量，数量仍是非负的 $n_t$；不再有组成坐标非负的约束，故全部 $k$ 出现。若还要有向演化处处合法，须另用命题 117.2 的守卫或不变锥。$\square$

这里连接的是同一组成的数值前缀和来源差异。记录的可行区间随尾部通过 $n_t$ 改变，因而非负联合源是依赖族；不能用一个不受约束的“任意尾部乘任意记录”直积替代。也没有由自然密度得到条件组成的概率独立或熵分解。两个坐标恢复组成，仍不恢复同组成内部的有序树、括号或共享引用；后者须有各自的来源语法和观察。以下有限查询问题同样必须证明实际联合词像，不能仅由某个单独坐标的双射推断可任意同步选择其它坐标。

## 118. 完整三窗词的位移桥与五十四个实际六问相位

### 118.1. 完整短词像的规范位移表达

**约定 118.1（固定实际来源的查询合同）。** 本节沿用定义 113.1、114.1：模数为 $H=5040=16\cdot9\cdot5\cdot7$，已知实际下一权重行，结构标签为 $(\sigma,E)=(1,\mathrm{true})$。候选族允许两种单位初始化和任意返回深度；一旦选择隐藏的正值实际前缀，每次重置都回到这一个前缀，其单位、深度和值保持固定。每问提交一个至多三窗的字面后缀并作规范 End，读取完整 $\gcd(N_{\rm final},5040)$，或与之双射的 $F_{5040}$ 标签；空后缀也收费一问，非法词与不适当 End 都返回同一错误符号。策略保留全部回答，目标是确定该已知行上的源余数 $r$，允许不再查询而推断最后唯一候选。按定理 104.7，这也准确确定该行上的完整未来类。

实际相位严格采用定理 114.12 的编号：

$$
T(u,v)=(u+2v,2u+3v),\qquad
w_j=T^j(2,3)=(F_{3j+3},F_{3j+4})\pmod{5040},\qquad0\le j<80.
$$

矩阵 $T=M^3$，与前面的逐位 $s$ 不是同一类型的映射。本节复用 §§113–115 对实际源、完整历史和既有相位的结论；新构造仍在该合同内，既不另给免费观察，也不把未知相位当成已知行。

**定理 118.2（全部五十五词的整数位移像）。** 从接缝 1、可 End 的标签出发，全部至多三窗成功词与独立集

$$
\mathcal I_3=\{I\subseteq\{1,\ldots,8\}:I\text{ 无相邻元素}\}
$$

一一对应。它们又由

$$
n(I)=\sum_{i\in I}F_{i+1}
$$

一一编号为 $n=0,\ldots,54$。对任意整数权重行 $(u,v)$，其完整整数平移像为

$$
\left\{(2u-v)n+(v-u)s(n):0\le n<55\right\}.
$$

对正 Fibonacci 代表 $(u,v)=(F_{3j+3},F_{3j+4})$，这恰为 $s^{3j+2}(\{0,\ldots,54\})$；模 5040 的实际行平移像是这个整数像的约化。

证明。接缝 1 强制后缀偏移 0 为零。非空成功词的所有占用位置因此在 $\{1,\ldots,8\}$，没有相邻位置，而且最后一个完整三位窗口必须包含最高占用位。给定占用集，执行词的长度就由该窗口唯一确定；反向在这些位置置 1，并在含最高位置的窗口后 End，便得合法词。前导及中间零窗必须执行，只有高端整零窗不保留。空集对应收费的空词，因初始 $E=\mathrm{true}$ 而成功。这正是命题 114.2 的完整族，包含首两位为 $01$ 的词。

为证编号的完整性，设可用位置为 $1,\ldots,d$，权重为 $F_2,\ldots,F_{d+1}$。$d=0$ 只有 0，$d=1$ 给 0、1。$d\ge2$ 时，末位置不占用给区间 $[0,F_{d+1}-1]$；末位置占用强制前邻为空，给区间

$$
F_{d+1}+[0,F_d-1]=[F_{d+1},F_{d+2}-1].
$$

归纳中每段都唯一表示，两段不交且相邻，所以得到 $[0,F_{d+2}-1]$ 的唯一表示。取 $d=8$，$F_{10}=55$，便得到全部 55 个编号。最大编号 $54=2+5+13+34$ 对应 $I=\{2,4,6,8\}$、词 $[001,010,101]$；编号 55 首次需要 $F_{10}$，对应偏移 9，已进入第四窗。

根据定义 114.1，偏移 $i\ge1$ 的实际权重为 $uF_{i-1}+vF_i$。Fibonacci 递推逐项给

$$
(2u-v)F_{i+1}+(v-u)F_{i+2}=uF_{i-1}+vF_i.
$$

对 $I$ 求和，第二个和正是 $s(n(I))$，所以每个词有显示的平移；反向每个 $n<55$ 都有唯一的 $I$，故两个集合包含方向都成立。代入 Fibonacci 行，有 $2u-v=F_{3j+1}$、$v-u=F_{3j+2}$，由定理 116.4 中的迭代式即得 $s^{3j+2}(n)$。

这也与前缀柱集直接相接。实际读过 $d$ 窗的源有 $m=1+3d$ 个完整数位，末位为 1；故定理 116.4 的自由尾部提高 $m+1=3d+2$ 位。限制再用至多三窗，恰允许删去强制零位后的八个自由位置，亦即 $t=0,\ldots,54$。在返回深度 $d=j+80h$，整数权重通常大于相位代表的权重，但同一个词的模行及模平移相同，故与上述约化式一致。

这个对应只给完整可用像，不给任意可选的局部中心元组。若记 $f_{u,v}(n)=(2u-v)n+(v-u)s(n)$，则

$$
f_{u,v}(a)+f_{u,v}(b)-f_{u,v}(a+b)
=(v-u)\mathfrak c(a,b).
$$

线性项相消即得；作为三窗查询时，每个使用的编号还须小于 55。位置对应和这个进位关系都不证明短词像对相加封闭，更不证明它是各素幂投影的直积。$\square$

### 118.2. 相位一的全部字面见证与前三问分支

**命题 118.3（二十二个合法共同词）。** 在实际行 $w_1=(8,13)$，八个偏移位置的权重为

$$
(13,21,34,55,89,144,233,377),
$$

编号所用的规范权重为 $(1,2,3,5,8,13,21,34)$。以下每行给出一个合法的至多三窗词；其整数平移就是所列中心 $c$。这里令 $x=-r\pmod{5040}$，所以查询平移 $c$ 的完整回答为 $\gcd(r+c,5040)=\gcd(x-c,5040)$；中心一词是相对于 $x$，最终须恢复 $r=-x$。

| 118.3 见证编号 | 占用位置 $I$ | 规范编号 $n$ | 中心 $c$ 的逐项和 | 低到高窗口词，随后 End |
| --- | --- | ---: | --- | --- |
| 118.3.1 | $\varnothing$ | 0 | $0$ | 空词 |
| 118.3.2 | $\{1\}$ | 1 | $13$ | $[010]$ |
| 118.3.3 | $\{1,3\}$ | 4 | $13+34=47$ | $[010,100]$ |
| 118.3.4 | $\{1,4\}$ | 6 | $13+55=68$ | $[010,010]$ |
| 118.3.5 | $\{1,5\}$ | 9 | $13+89=102$ | $[010,001]$ |
| 118.3.6 | $\{1,3,5\}$ | 12 | $13+34+89=136$ | $[010,101]$ |
| 118.3.7 | $\{3,6\}$ | 16 | $34+144=178$ | $[000,100,100]$ |
| 118.3.8 | $\{1,3,6\}$ | 17 | $13+34+144=191$ | $[010,100,100]$ |
| 118.3.9 | $\{1,4,6\}$ | 19 | $13+55+144=212$ | $[010,010,100]$ |
| 118.3.10 | $\{2,4,6\}$ | 20 | $21+55+144=220$ | $[001,010,100]$ |
| 118.3.11 | $\{7\}$ | 21 | $233$ | $[000,000,010]$ |
| 118.3.12 | $\{1,7\}$ | 22 | $13+233=246$ | $[010,000,010]$ |
| 118.3.13 | $\{2,7\}$ | 23 | $21+233=254$ | $[001,000,010]$ |
| 118.3.14 | $\{3,7\}$ | 24 | $34+233=267$ | $[000,100,010]$ |
| 118.3.15 | $\{1,4,7\}$ | 27 | $13+55+233=301$ | $[010,010,010]$ |
| 118.3.16 | $\{3,5,7\}$ | 32 | $34+89+233=356$ | $[000,101,010]$ |
| 118.3.17 | $\{3,8\}$ | 37 | $34+377=411$ | $[000,100,001]$ |
| 118.3.18 | $\{5,8\}$ | 42 | $89+377=466$ | $[000,001,001]$ |
| 118.3.19 | $\{3,5,8\}$ | 45 | $34+89+377=500$ | $[000,101,001]$ |
| 118.3.20 | $\{6,8\}$ | 47 | $144+377=521$ | $[000,000,101]$ |
| 118.3.21 | $\{3,6,8\}$ | 50 | $34+144+377=555$ | $[000,100,101]$ |
| 118.3.22 | $\{1,3,6,8\}$ | 51 | $13+34+144+377=568$ | $[010,100,101]$ |

证明。每个所列集合的相邻元素之差至少为 2，最小位置至少为 1，最大位置至多为 8。将位置 $(0,1,2),(3,4,5),(6,7,8)$ 分组，正好逐行得到显示的窗口词；其最后整窗都非零。因而接缝、内部合法性、三窗预算及 End 条件全部成立，包括末窗为 $100$ 或 $010$ 的情形。规范编号由前述八个规范权重相加得到，例如 $\{1,3,6,8\}$ 给 $1+3+13+34=51$；实际平移的各个加项在表中全部写出，所以等式逐行直接成立。实际源为正，实际权重也为正，故非空查询的终端值仍为正；空词使用已允许的 End。这些是共同字面词，在不同候选上没有更换词。$\square$

**命题 118.4（前三问的完整局部分支）。** 记截断深度

$$
d_2(y)=\max\{a\le4:2^a\mid y\},\qquad
d_3(y)=\max\{a\le2:3^a\mid y\}.
$$

它们分别只依赖模 16、模 9 余数，零余数取最大深度 4、2。完整 gcd 回答同时给这两个深度及模 5、模 7 的命中信息。先问中心 0，再问中心 13；第三问准确取为

$$
\begin{cases}
254,&\text{第一问在中心 0 的回答满足 }d_2(x)=1\quad\text{（甲支）},\\
47,&\text{第一问在中心 0 的回答满足 }d_2(x)\ne1\quad\text{（乙支）}.
\end{cases}
$$

分支不要求第二问也有二进深度 1；事实上甲支第二问的二进深度恒为 0。三问后，模 $16,9,5$ 的后验各为单点或下面列出的二元对。两支的中心余数为

| 118.4 分支 | 整数中心序列 | 模 16 | 模 9 | 模 5 | 模 7 | 尚未问过的模 7 颜色 $U$ |
| --- | --- | --- | --- | --- | --- | --- |
| 118.4 甲 | $(0,13,254)$ | $(0,13,14)$ | $(0,4,2)$ | $(0,3,4)$ | $(0,6,2)$ | $\{1,3,4,5\}$ |
| 118.4 乙 | $(0,13,47)$ | $(0,13,15)$ | $(0,4,2)$ | $(0,3,2)$ | $(0,6,5)$ | $\{1,2,3,4\}$ |

证明。先完整计算模 16 的分支。甲支的第一深度 1 恰给 $x\in\{2,6,10,14\}$。这些都是偶数，所以与中心 13 的差为奇数，第二深度全部是 0。第三中心为 14 模 16，对 $x=14$ 给深度 4，对 $x=6$ 给深度 3，对 $x=2,10$ 都给深度 2。故甲支只有 $\{2,10\}$ 未分离，其余为单点。

乙支第一深度只能是 $0,2,3,4$。深度 4 给 $x=0$，深度 3 给 $x=8$，都已确定。深度 2 给 $\{4,12\}$，后两中心 13、15 都是奇数，均对两候选给深度 0，故保留这一对。第一深度为 0 时 $x$ 为奇数，第二中心 13 的深度必为正：深度 4 给 $x=13$，深度 3 给 $x=5$；深度 2 给 $\{1,9\}$，这两值与第三中心 15 的差均恰含一个因子 2，因此仍保留这一对；深度 1 给 $\{3,7,11,15\}$，第三中心 15 对它们依次给 $2,3,2,4$，所以只剩 $\{3,11\}$ 未分离。上述分支穷尽第一、第二问所有可能截断深度，精确相等的最大深度分支也已包括。

再看模 9，两支的中心都是 $0,4,2$，模 3 恰各占一类。所以恰有一次回答的三进深度为正，其余两次深度为零。如果这个正深度为 2，$x$ 就是相应模 9 中心；若为 1，则在同一模 3 类中删去这个中心，分别留下

$$
\{3,6\}\quad\text{（中心 0）},\qquad
\{1,7\}\quad\text{（中心 4）},\qquad
\{5,8\}\quad\text{（中心 2）}.
$$

这也穷尽全部模 9 分支。

模 5 的前三个中心各不相同。任一命中就确定该坐标；全部未命中时，甲支删去 $0,3,4$ 后剩 $\{1,2\}$，乙支删去 $0,3,2$ 后剩 $\{1,4\}$，两支都可由一个模 5 中心为 1 的查询分离。模 7 也已测试三个不同颜色，命中就确定该坐标，否则只余表中四个颜色。所有余数都是显示整数中心的直接约化；例如 $254=16\cdot15+14=9\cdot28+2=5\cdot50+4=7\cdot36+2$，$47$ 相应给 $15,2,2,5$。$\square$

### 118.3. 单个实际词承担的局部区分与联合收尾

**命题 118.5（每个剩余对的不同未测颜色）。** 对命题 118.4 的每个未解决二进或三进候选对，下表给出两个实际允许词的中心。它们都区分所列候选对，并有两个不同且属于该支 $U$ 的模 7 颜色。

| 118.5 二进分支与候选对 | 两个中心 | 共同模 8 余数 | 各自模 7 颜色 |
| --- | --- | ---: | --- |
| 118.5 二进甲 $\{2,10\}$ | $178,466$ | 2 | $3,4$ |
| 118.5 二进乙 $\{4,12\}$ | $212,220$ | 4 | $2,3$ |
| 118.5 二进乙 $\{1,9\}$ | $233,521$ | 1 | $2,3$ |
| 118.5 二进乙 $\{3,11\}$ | $267,555$ | 3 | $1,2$ |

| 118.5 三进分支与候选对 | 两个中心 | 各自模 9 余数 | 各自模 7 颜色 |
| --- | --- | --- | --- |
| 118.5 三进甲乙 $\{3,6\}$ | $102,246$ | $3,3$ | $4,1$ |
| 118.5 三进甲乙 $\{1,7\}$ | $136,568$ | $1,1$ | $3,1$ |
| 118.5 三进甲 $\{5,8\}$ | $68,500$ | $5,5$ | $5,3$ |
| 118.5 三进乙 $\{5,8\}$ | $212,500$ | $5,5$ | $2,3$ |

此外，七个中心

$$
136+55t,\qquad 0\le t\le6,
$$

全由命题 118.3 的词实现，全部为 1 模 5，且依次给模 7 颜色 $3,2,1,0,6,5,4$。它们既能解决任一模 5 剩余对，又能供应任意尚需的模 7 颜色。

证明。先说明复用定理 114.8 的局部区分规则时符号如何与 $x=-r$ 相接。若 $x\ne y$ 模 $p^h$，令 $t<h$ 为两者差的 $p$ 深度，则中心 $c$ 的完整截断估值区分二者，当且仅当

$$
c\equiv x\text{ 或 }y\pmod{p^{t+1}}.
$$

若中心在共同低 $t$ 位以前已偏离，两深度相同且小于 $t$；若共享这 $t$ 位但下一位与两者都不同，两深度都为 $t$；若下一位匹配其中之一，对该候选的深度至少 $t+1$，对另一候选恰为 $t$。这穷尽中心的位置，证明充要性。

模 16 的每对相差 8，故一个中心属于其共同模 8 类就够：它模 16 必等于其中一员，对该员给深度 4，对另一员给 3。表中模 8 算术逐项为

$$
\begin{gathered}
178=8\cdot22+2,\quad466=8\cdot58+2,\quad
212=8\cdot26+4,\quad220=8\cdot27+4,\\
233=8\cdot29+1,\quad521=8\cdot65+1,\quad
267=8\cdot33+3,\quad555=8\cdot69+3.
\end{gathered}
$$

它们模 7 分别由

$$
\begin{gathered}
178=7\cdot25+3,\quad466=7\cdot66+4,\quad
212=7\cdot30+2,\quad220=7\cdot31+3,\\
233=7\cdot33+2,\quad521=7\cdot74+3,\quad
267=7\cdot38+1,\quad555=7\cdot79+2
\end{gathered}
$$

给出。因此每行有两个不同颜色；甲行的 $3,4$ 属于 $\{1,3,4,5\}$，乙各行的 $2,3$ 或 $1,2$ 属于 $\{1,2,3,4\}$，均未被前三问使用。

模 9 的每对差为 3 或 6，一个中心等于其中一员模 9 时给深度 2，另一员给 1。所用等式为

$$
\begin{gathered}
102=9\cdot11+3=7\cdot14+4,\qquad
246=9\cdot27+3=7\cdot35+1,\\
136=9\cdot15+1=7\cdot19+3,\qquad
568=9\cdot63+1=7\cdot81+1,\\
68=9\cdot7+5=7\cdot9+5,\qquad
500=9\cdot55+5=7\cdot71+3,\\
212=9\cdot23+5=7\cdot30+2.
\end{gathered}
$$

故前两行的颜色 $4,1$ 和 $3,1$ 同属两个 $U$；甲的第三对有颜色 $5,3$，乙的第三对有颜色 $2,3$。每对都得到两个不同且正确未测的颜色。所有中心在命题 118.3 中各有完整字面词，并非只有孤立的局部数值见证。

最后，七项等差列依次是 $136,191,246,301,356,411,466$，其规范编号为 $12,17,22,27,32,37,42$。直接对相应占用位置的权重系数求和，任意行上的系数对依次为

$$
(4,8),(6,11),(8,14),(10,17),(12,20),(14,23),(16,26).
$$

例如首项 $I=\{1,3,5\}$ 给 $(0,1)+(1,2)+(3,5)=(4,8)$，第二项 $\{1,3,6\}$ 给 $(0,1)+(1,2)+(5,8)=(6,11)$，其余五项分别是 $(0,1)+(8,13)$、$(0,1)+(2,3)+(8,13)$、$(1,2)+(3,5)+(8,13)$、$(1,2)+(13,21)$、$(3,5)+(13,21)$，恰得所列各对。故这些共同词在任意行上的平移是

$$
(4u+8v)+t(2u+3v),\qquad0\le t\le6.
$$

在 $(8,13)$ 上即 $136+55t$。模 5 始终为 1，模 7 则因 $55\equiv-1$ 而依次给七个不同颜色。模 5 的两种剩余对都含 1，故命中 1 与不命中 1 区分两候选。这里只使用整数等式及模 5、模 7 的约化，绝不把 55 当作模 5040 的单位或除以 55；事实上 $5\mid55$。$\square$

**定理 118.6（实际相位一的精确六问成本）。** 在约定 118.1 的同源、完整 gcd、三窗合同下，

$$
Q_3(5040;8,13)=6.
$$

构造性上界不使用假设 107.5。

证明。先执行命题 118.4 的三问，保留它们的全部回答。在这个已固定的完整历史上，令 $U$ 为表中的四个未测模 7 颜色。为最后三问按下列确定规则选择实际词。

如果模 16 仍是二元对，选命题 118.5 对应行的第一个中心及其字面词。如果模 9 仍是二元对，在对应行的两个中心中，按表顺序选第一个颜色尚未被选用的词；此前至多选过一个颜色，而这两个不同颜色都在 $U$，所以必有选择。如果模 5 仍是二元对，从七项等差列表中选颜色属于 $U$ 且尚未选过的最小颜色对应的词；此前至多两个颜色被选用，故至少还有两个可选颜色。已是单点的坐标无需分配专用词。若目前选出的词不到三个，就继续用同一七项表按最小未选颜色补足，直到恰有三个词；因为 $|U|=4$，全过程可完成。前三问的完整历史确定以后，这三个词已经确定，可以依次查询而无须再适应。

每个未解决的模 16、模 9、模 5 对至少被分配的一词区分，所以最后三份完整回答确定这三个坐标。一个词可以附带完成其它坐标的区分，这种同时承担的任务直接从该词的完整回答使用；没有把几个词的局部余数拼成一个虚构词。若两个任务的表中出现同一个词，它只有自己的一个模 7 颜色，不能当成两个不同颜色。上述固定选择规则仍为后分配的任务另取异色见证，即使前一词已能附带解决它；存在性由两选择与七项表保证。保留各自的分配词已经足够，额外的同时区分只会缩小后验，不能破坏它。

前三问用三个不同模 7 颜色，最后三问用另外三个不同颜色。若任一问命中，$x\bmod7$ 立即确定；若六问全部未命中，唯一未问的第七个颜色就是 $x\bmod7$，无需追加确认。这也包括前三问已有模 7 命中的所有历史：仍执行同一选择规则，只会得到冗余而相容的信息。于是模 $16,9,5,7$ 全部确定，CRT 给唯一的 $x\bmod5040$，输出 $r=-x$。所有词都来自命题 118.3，至多三窗且正值 End 合法，每问都回到最初那一个实际源，故上界确为六问。

为明确实际先验与下界的来源，复用引理 105.1、定义 113.1 的返回区间。对任一相位 $j$，在一个足够大的共同返回深度 $d=j+80h\ge1$，标签 $(1,\mathrm{true})$ 的实际正整数像是

$$
[F_{3d+2},F_{3d+3}-1]\cap\mathbb Z,
\qquad\text{长度 }F_{3d+1}.
$$

取该长度至少为 5040，就能在这一个深度、同一实际整数权重行上，为每个模 5040 余数选一个实际正前缀。两种单位初始化是在候选族中合并使用，不能改说每种初始化分别有满纤维。每个被选前缀的初始化此后固定。

沿任意可行完整历史，已经提交的词都已固定，完整 gcd 的局部分量各给一个余数条件。故后验支持是这些局部条件交集的 CRT 乘积；分支所用的第一问二进条件已包含其中。上述满纤维为每个相容元组提供实际源。这个论证保证源的联合实现，没有扩大允许中心的集合。

精确下界直接复用推论 113.7 的实际坐标轴论证。固定一个模 $720=16\cdot9\cdot5$ 的余数，让模 7 的七个值变化，上述同深度满纤维给七个实际候选。在任何固定历史上，下一次成功词的平移已经确定，前三个素幂分量对这七个候选相同，只有模 7 作一次等值测试。在仍有至少两个候选时取未命中分支，每问至多排除一个候选，恒错词排除零个。五问以后至少两个实际候选留下，不能精确识别。嵌套候选集中任一最终存活源都实现整段回答，其原始前缀和单位从未改变；这里没有每问更换源。此下界覆盖完整 55 个成功词、全部错误词和空查询，甚至允许更大的中心族。因此 $Q_3\ge6$，与上界相等。$\square$

### 118.4. 实际单位转移与同一前三问不能普遍转移的反例

**推论 118.7（五十四个实际相位的六问结论）。** 在定理 114.12 原有 52 个相位之外，实际相位 $1,41$ 也满足 $Q_3=6$。因此现在给出六问策略的实际相位集合是

$$
\begin{aligned}
\mathcal J_{54}={}&\{j:0\le j<80,\ j\not\equiv3\pmod4,\ j\not\equiv1\pmod5\}\\
&\cup\{1,36,39,41,76,79\},
\end{aligned}
$$

恰有 54 个元素。这是一个已给出构造的集合，不是所有六问相位的最大性分类。

证明。$T(2,3)=(8,13)$，所以定理 118.6 的行确是相位 1。它的普遍等差列步长为 $2\cdot8+3\cdot13=55$，不是模 5040 单位；本节的构造使用不同模 5 类的实际词补足了定理 114.14 保留的这个缺口，没有在原单位步长定理中非法求逆。

命题 105.5 及定理 114.12 已给实际标量返回

$$
T^{40}=1441I\pmod{5040},\qquad
1441\equiv(1,1,1,-1)\pmod{(16,9,5,7)},\qquad
1441^2\equiv1\pmod{5040}.
$$

它在四个素幂因子上都是单位，且

$$
1441\cdot8=11528\equiv1448,\qquad
1441\cdot13=18733\equiv3613\pmod{5040}.
$$

故 $w_{41}=1441w_1=(1448,3613)$ 是一个实际行。对同一字面词，其平移线性地变为 $1441c$。若该行的隐藏源余数为 $r$，令 $x=-1441^{-1}r$，则

$$
r+1441c=1441(c-x),\qquad
\gcd(r+1441c,5040)=\gcd(x-c,5040).
$$

因此完整回答逐问等于相位一策略所使用的回答；第一问的二进深度也一致。原策略的所有分支、词与收尾选择可原样执行，最后输出 $r=-1441x$。模 7 的实际颜色被乘以 $-1$，互异性和未测关系保持。该实际行的完整源纤维及六问下界仍由定理 118.6 末段的同深度论证供给，所以 $Q_3(w_{41})=6$。这里只转移到已经证明实际的单位倍行。

定理 114.12 的两个同余排除条件在每 20 个指标中给 $3\cdot4=12$ 个，80 个指标中共 48 个；原有四个额外相位是 $36,39,76,79$，合计 52。$1,41$ 均为 1 模 5，均不在前 48 个之中，也都不是原四个额外相位，彼此不同。实际周期 80 使这 54 个指标对应 54 个不同实际行，所以余下恰有 $80-54=26$ 个相位未由这些构造确定为六问。$\square$

**命题 118.8（相位二十一对同一字面前三问的障碍）。** 在实际相位 $21$，若仍先使用空词、$[010]$，并仅按第一问的二进深度是否为 1 来在 $[001,000,010]$ 与 $[010,100]$ 中选第三词，则任何再接至多三问的策略都不能对全部实际源完成识别。后三问即使从完整允许词族中自适应选择，此结论也成立。这只否定这个固定的前三问方案，不断言 $Q_3(w_{21})>6$。

证明。由命题 105.5 的模 7 Fibonacci 周期 16，

$$
w_{21}=(F_{66},F_{67})\equiv(F_2,F_3)=(1,2)\pmod7.
$$

前两词的平移模 7 是 $0,v=2$。甲支第三词的占用集 $\{2,7\}$ 有系数对 $(1,1)+(8,13)=(9,14)$，故平移模 7 为 $9\cdot1+14\cdot2=37\equiv2$。乙支第三词的占用集 $\{1,3\}$ 有系数对 $(0,1)+(1,2)=(1,3)$，平移为 $1+3\cdot2=7\equiv0$。所以无论进入哪一支，三问只测试模 7 的两个不同颜色 0、2。

固定任一个模 720 源余数。它确定这三问全部非 7 分量，也确定第一问的二进深度及所选第三词。共同返回深度的满纤维给这一个模 720 余数的七个模 7 提升各一个实际正源。取其中满足 $r\not\equiv0,-2\pmod7$ 的五个源；它们对三问的模 7 分量全未命中，非 7 分量相同，所以共有同一完整三问历史。此后任意成功词在固定模 720 轴上仍只能测试一个模 7 等值，沿未命中分支至多删除一个候选；错误词不删候选。再问三次后至少 $5-3=2$ 个实际源存活，故不能识别。每个最终存活源都有原先固定的前缀、深度与单位，实现整段回答，无须在途中改变来源。

这个障碍针对完整允许族的任意后三问，不仅针对命题 118.5 的收尾表；但其前提固定了前三个字面词和分支规则。换用别的开头或别的六问结构不在反证范围内。$\square$

**约定 118.9（剩余相位所需的共同实现条件）。** 对相位 $j$，真正可选的中心元组仍只有

$$
\left\{\bigl(f_j(n)\bmod16,\ f_j(n)\bmod9,\ f_j(n)\bmod5,\ f_j(n)\bmod7\bigr):0\le n<55\right\},
$$

其中 $f_j(n)=F_{3j+1}n+F_{3j+2}s(n)$。在采用 $x=-r$ 的坐标后，一个未测颜色 $\gamma$ 能帮助区分局部候选对 $\{a,b\}$，要求存在同一个 $n<55$，使 $f_j(n)\equiv\gamma\pmod7$ 且该中心对 $a,b$ 的截断深度不同。若希望一词同时区分几个局部对，也须由同一个 $n$ 满足全部区分条件。这是定理 114.8 的实际单词条件在规范位移编号中的写法。

本节在相位 1 用二进、三进各两个未测颜色及模 5 的全部颜色，证明了一个足够的选择条件，再经实际单位返回转移至 41。这个条件不是六问的必要条件；命题 118.8 也没有排除相位 21 的其它策略。余下 26 个实际相位是否全有六问策略仍未解决，不能由规范柱集的双射、边缘投影的覆盖或没有反例推出结论。在假设 107.5 的语义覆盖与分区稳定条件下，推论 114.5 原有的全行 $6\le Q_3\le15$ 仍成立；本节新增的两个六问上界不依赖该假设。已知实际行、完整反馈与每次同源重置始终保留；§115 的未知相位及依赖完整历史的提升问题没有由此得到全局最优值。前缀密度、非负组成容量和本节实际短词查询分别具有这里明示的来源与操作，不能互换为别种算术观察的分类，也不附带全局 Robin 或素性结论。

## 追加锚（本行以下为增补区）


## 119. 替换塌缩与有限寄存器下界的假设更正

### proposition 119.1 定理 5.2 的加性假设

定理 5.2 的塌缩结论须在替换保持加法的假设下使用：设 $G$ 为交换群，$S:G\to G$ 为加法群同态，且 $A,B\in G$ 满足

$$
S(A)=B,\qquad S(B)=A+B,\qquad 3A=2B.
$$

则 $A=B=0$。这里的整数倍表示交换群中的重复加法，不要求 $G$ 无挠。若只假设 $S$ 是集合映射，原结论不成立。

**证明。** 加性给出 $S(3A)=3S(A)=3B$ 和 $S(2B)=2S(B)=2A+2B$。因此 $3B=2A+2B$，在群中消去 $2B$ 得 $B=2A$。代入原关系得到 $3A=4A$，再消去 $3A$ 得 $A=0$，继而 $B=0$。

反之，在 $G=\mathbb Z$ 中取 $A=2$、$B=3$，定义集合映射

$$
S(x)=
\begin{cases}
3,&x=2,\\
5,&x=3,\\
0,&x\notin\{2,3\}.
\end{cases}
$$

它满足 $S(A)=B$、$S(B)=A+B$ 及 $3A=2B=6$，但 $A,B$ 均非零。故本命题以加法群同态假设替代定理 5.2 中对任意映射的表述。$\square$

### proposition 119.2 命题 13.8 的非退化字母表假设

命题 13.8 中“至少两个 $m$ 元寄存器”的结论须限定为整数 $m\ge2$。具体地，令 $r\in\mathbb N$，令 $E$ 为恰有 $m$ 个元素的集合。若编码

$$
C:(\mathbb Z/m\mathbb Z)^2\longrightarrow E^r
$$

有解码器 $D:E^r\to(\mathbb Z/m\mathbb Z)^2$ 满足 $D\circ C=\operatorname{id}$，则 $m^r\ge m^2$ 且 $r\ge2$。取 $E=\mathbb Z/m\mathbb Z$ 和 $r=2$，当前与下一次数量读数达到该下界。

**证明。** 若 $C(z)=C(w)$，施加 $D$ 得 $z=w$，所以 $C$ 单射。源集有 $m^2$ 个元素，目标集有 $m^r$ 个元素，故 $m^2\le m^r$。当 $m\ge2$ 时，$r=0$ 给出 $m^r=1<m^2$，$r=1$ 给出 $m^r=m<m^2$，所以 $r\ge2$。

两寄存器编码与解码分别为

$$
C(a,b)=(2a+3b,3a+5b),\qquad
D(n,n')=(5n-3n',2n'-3n),
$$

全部运算在 $\mathbb Z/m\mathbb Z$ 中进行。展开得到 $D(C(a,b))=(a,b)$ 和 $C(D(n,n'))=(n,n')$，因此编码为双射，使用恰好 $m^2$ 个联合状态。

当 $m=1$ 时，$(\mathbb Z/m\mathbb Z)^2$ 是单点集，零个寄存器的状态集 $E^0$ 也是单点集，已足以无损编码。此时联合状态数下界 $m^2=1$ 仍成立，却不能推出寄存器数至少为二；本命题据此限定命题 13.8 的寄存器数结论。$\square$

## 追加锚（本行以下为增补区）

## 120. 仅作同源替换时的 gcd 全未来商与实际容量

### 120.1. 实际来源、未来等价与局部标签

**定义 120.1（同源 gcd 未来的作用域）。** 沿用 §3 的 $\rho$、$M$ 与 §5 的 $q=(2,3)$，来源为包含结构零的完整非负组成 $v=(a,b)\in\mathbb N^2$。每个未来都从同一个 $v$ 反复施加 $\rho$，不能在保持当前数量的条件下换一个来源。复用约定 117.1 与定理 117.3 的坐标和实际支持：

$$
\begin{gathered}
(n,z)=(qv,qMv)=(2a+3b,3a+5b),\qquad
(a,b)=(5n-3z,2z-3n),\\
A=\left\lceil\frac{3n}{2}\right\rceil,\quad
B=\left\lfloor\frac{5n}{3}\right\rfloor,\quad
I_n=[A,B]\cap\mathbb Z,\quad L=|I_n|=C(n),\\
L=\left\lfloor\frac n6\right\rfloor+1-\mathbf1_{\{n\equiv1\pmod6\}}.
\end{gathered}
$$

这里每个 $z\in I_n$ 恰有上述一个实际来源。这是既有两读数逆式和完整支持的复用。尤其 $n=0$ 有一个来源 $(0,0)$，$n=1$ 没有来源；原始非空树是另一种域，不能据其不含空树删掉本节的结构零，也不能用有向组成的规范单位填补 $I_1$。

令 $F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$。对整数 $H\ge1$，记

$$
y_0=n,\qquad y_k=F_{k-1}n+F_kz=qM^kv\quad(k\ge1),\qquad
R_H(n,z)=\bigl(\gcd(y_k,H)\bigr)_{k\ge1}.
$$

递推式来自 §5.4 的 $M^2=M+I$。在固定 $n$ 的实际区间上，$z\sim_{n,H}z'$ 表示两个 $R_H$ 相等，记类数为 $Q_H(n)$。这是 gcd 全未来任务；定理 117.4 的完整数值任务仍有自己的容量 $C(n)$。

**定理 120.2（实际未来商的记录含义）。** 外部给定确切 $n$，只要求从辅助记录解码每个 $k\ge1$ 的 gcd 读数时，最少的实际记录像大小恰为 $Q_H(n)$。非空纤维上，最少固定长度二进位数为 $\lceil\log_2Q_H(n)\rceil$；$Q_H(n)=1$ 时不需辅助位。空纤维没有实际记录，不对零取对数。

证明。若两个来源在某个未来时刻的 gcd 不同，它们不能得到同一记录，否则该时刻的解码器会给两个来源相同答案。故任何记录至少区分所有未来等价类。反向记录类本身，每个时刻的读数在该类上恒定，因而给出良定义的解码器并达到下界。固定 $b$ 位至多编码 $2^b$ 类，取最小满足 $2^b\ge Q_H(n)$ 的整数即可。这没有计入取得记录的查询或工作空间；固定 $n$ 的纤维也不在 $\rho$ 下封闭，故此容量不是固定纤维上的自主机器状态数。$\square$

**定理 120.3（一般素数幂的共同含量、保留深度与相位分类）。** 取 $p^e\parallel H$，约定 $\nu_p(0)=\infty$，所有可见指数截断在 $e$。对任意整数对 $(n,z)$，令

$$
d=\min\{e,\nu_p(n),\nu_p(z)\}.
$$

若 $d=e$，赋予一个独立的饱和零标签 $\mathsf Z_{p,e}$。若 $d<e$，令 $m=e-d$，在局部环射影直线

$$
P_j=\mathbb P^1(\mathbb Z/p^j\mathbb Z),\qquad
O_j=\{M^t[1:0]:t\in\mathbb Z\},\qquad
r_j=\min\{r\ge1:p^j\mid F_r\}
$$

中取 $x_j=[n/p^d:z/p^d]$，$1\le j\le m$。这里 $P_j$ 是至少一坐标为单位的二元组模共同单位倍数，不能换成所有非零二元组。定义

$$
h=\max\bigl(\{0\}\cup\{j\le m:x_j\in O_j\}\bigr),\qquad
\lambda_{p,e}(n,z)=
\begin{cases}
\mathsf Z_{p,e},&d=e,\\
(d,0,*),&d<e, h=0,\\
(d,h,x_h),&d<e, h\ge1.
\end{cases}
$$

两对整数的全部正时刻 gcd 读数的 $p$ 部分相同，当且仅当其标签相同。因而实际来源的 $H$ 全未来等价，恰是每个素数幂标签都相同。若 $h\ge1$，还可唯一地写

$$
x_h=M^{-(\tau-1)}[1:0],\qquad \tau\in\mathbb Z/r_h\mathbb Z.
$$

此时

$$
p^{d+j}\mid y_k\ \Longleftrightarrow\ k\equiv\tau\pmod{r_j}\quad(1\le j\le h),
$$

而 $h<j\le m$ 的整除永不发生。无命中标签 $h=0$ 的所有读数指数恒为 $d$；饱和零标签的所有读数指数恒为 $e$。

证明。$M$ 在每个有限剩余环上可逆，所以有正次幂为单位矩阵。由 $M^2=M+I$ 归纳得

$$
M^r=F_{r-1}I+F_rM\qquad(r\ge1).
$$

$M^r[1:0]=[1:0]$ 当且仅当 $p^j\mid F_r$；在返回时 $F_{r-1}$ 必是单位，且整个矩阵为单位标量。因此 $r_j$ 存在，既是这条轨道长度，也是 $M$ 在这里的射影阶，$|O_j|=r_j$。它不必等于矩阵阶或 Pisano 周期。

前两次读数给

$$
\min\{e,\nu_p(y_1),\nu_p(y_2)\}
=\min\{e,\nu_p(z),\nu_p(n+z)\}=d,
$$

因为 $(n,z)$ 与 $(z,n+z)$ 生成同一个整数理想。$d=e$ 时一切未来都为零模 $p^e$，无需也不能再除出一个射影方向。否则除以 $p^d$ 后的二元组本原。

作用于观察坐标 $(n,z)$ 的第 $k$ 个行向量为 $(F_{k-1},F_k)$，也是 $M^{k-1}$ 的第二行。相邻 Fibonacci 数互素，这个行在模 $p^j$ 下至少一坐标为单位。解它的一条线性方程，核由 $(F_k,-F_{k-1})$ 生成；核内本原向量恰是生成向量的单位倍数。所以它的唯一射影核线为

$$
[(F_k,-F_{k-1})]=M^{-(k-1)}[1:0],
$$

并且 $p^{d+j}\mid y_k$ 当且仅当 $x_j$ 等于这条核线。此核是观察坐标中的第二坐标读出核，不是直接把来源坐标中的 $q$ 核当作 $[1:0]$。正整数 $k$ 在有限循环上遍历全部 $O_j$，故没有额外可用的方向。

约化把 $O_{j+1}$ 满射到 $O_j$，所以一个方向的命中层恰为初段 $1,\ldots,h$。保留 $x_h$ 就保留了所有较低层方向，并决定每层的整除条件；更高层一律无命中。这证明标签相同足以给相同未来。反过来，前两次读数已经恢复 $d$，全部未来中最大达到的截断指数是 $d+h$，因为最高命中层确有一个正时刻命中。因此相同未来恢复同一个 $h$。若 $h>0$，选一个达到该层的正时刻，两方向必须同时是那一行的唯一核线，于是 $x_h$ 相同。若 $h=0$，确实没有剩余方向信息。

循环轨道给相位的唯一性；约化给 $r_j\mid r_h$，同一核线在第 $j$ 层的时刻恰为 $\tau$ 模 $r_j$。最后，一个与 $H$ 的 gcd 由所有素因子的截断指数唯一决定，故得到乘积标签判据。局部零标签只表示模 $p^e$ 的零，不表示来源作为整数向量必为零。$\square$

### 120.2. 射影秩提升与一般计数

**定理 120.4（允许停滞的轨道提升与容量公式）。** 对每个素数 $p$ 和 $j\ge1$，

$$
\frac{r_{j+1}}{r_j}\in\{1,p\}.
$$

置

$$
\chi=\mathbf1_{\{r_1<p+1\}},\qquad
b_j=(r_1-1)\frac{r_j}{r_1}.
$$

固定一个 $p$ 单位 $n$，让 $z$ 遍历全部模 $p^e$ 剩余类，所得全未来类数为

$$
K_p(e)=b_e+\chi+
\sum_{j=1}^{e-1}b_j\mathbf1_{\{r_{j+1}=r_j\}}.
$$

让 $(n,z)$ 联合遍历全部模 $p^e$ 剩余对，所得类数为

$$
G_p(e)=1+\sum_{m=1}^{e}
\left(r_m+\chi+
\sum_{j=1}^{m-1}r_j\mathbf1_{\{r_{j+1}=r_j\}}\right).
$$

这些是以实际射影秩为参数的准确公式，不假设每层都按 $p$ 倍增长。

证明。用互不重叠的坐标图 $[1:t]$ 与 $[s:1]$（第二图要求 $p\mid s$）可知

$$
|P_j|=p^j+p^{j-1},
$$

且每个点到下一层恰有 $p$ 个提升。循环轨道的约化纤维大小恒为 $r_{j+1}/r_j$。写

$$
M^{r_j}=aI+p^jB_0,\qquad p\nmid a.
$$

取 $p$ 次幂，二项式展开的一次项含 $p^{j+1}$，次数至少二的项含 $p^{2j}$，而 $2j\ge j+1$。故该次幂模 $p^{j+1}$ 是单位标量。这一论证包含 $p=2,j=1$。约化和此标量式共同给

$$
r_j\mid r_{j+1}\mid pr_j,
$$

证明提升二分。

对剩余精度为 $m$ 的本原方向，标签只有三种来源。一直留在轨道至末层者贡献 $r_m$ 个标签。若在第 $j$ 层后退出，则只有 $r_{j+1}=r_j$ 的停滞步能发生：该步每个轨道父点恰有一个轨道子点和 $p-1$ 个非轨道子点；所有这些非轨道子点及其后续提升都只保留同一父点，故每个父点贡献一个退出标签，共 $r_j$ 个。若增长比为 $p$，全部 $p$ 个子点都在轨道，没有退出标签。最后，第一层轨道之外的所有方向合为一个无命中类，它存在恰当且仅当 $\chi=1$。这三类互斥，且每个都能选相应方向、子点及后续任意提升来实现。于是本原类数就是括号内的量。乘以 $p^{e-m}$ 给含量 $d=e-m$ 的类，所有含量都可实现且可区分，再加饱和零类即得 $G_p(e)$。

若 $p\nmid n$，只出现第一坐标为单位的图，$z/n$ 遍历该图。$O_1$ 中恰有一个第一坐标为零的点 $[0:1]=M[1:0]$；其余 $r_1-1$ 个基点各有 $r_j/r_1$ 个轨道提升。因此该图中轨道点数为 $b_j$。同样按末层、停滞退出、首层无命中来数，把 $r_j$ 换成 $b_j$ 即得 $K_p(e)$。该图第一层的补集大小也是 $p+1-r_1$，故仍用同一 $\chi$。

当 $\gcd(n,H)=1$ 时，CRT 在完整 $z$ 剩余宇宙上给 $\prod_{p^e\parallel H}K_p(e)$ 类。长度至少 $H$ 的实际 $I_n$ 含一套完整剩余系，因而达到此积；短区间须另算联合占用，不能由各局部边缘非空推出其交集非空。$\square$

### 120.3. 模 5040 的轨道、异常二进分支与全部局部类

**定理 120.5（模 5040 的实际射影轨道）。** 对 $5040=2^4\cdot3^2\cdot5\cdot7$，所需秩为

$$
\begin{gathered}
r(2)=3,\quad r(4)=6,\quad r(8)=6,\quad r(16)=12,\\
r(3)=4,\quad r(9)=12,\quad r(5)=5,\quad r(7)=8.
\end{gathered}
$$

模 $2,4,3,9,7$ 的轨道是整个射影直线；模 5 的轨道恰漏掉 $[1:3]$。定义

$$
\mathcal Q(n,z)=z^2-nz-n^2.
$$

模 8 的轨道恰为满足 $\mathcal Q\equiv\pm1\pmod8$ 的本原方向，模 16 的轨道恰为这一集合的全部提升。除共同含量后，在模 $2^m$、$m\le3$ 以及模 $3,9,5,7$ 上，未来商区分完整射影方向。在模 16 上，轨道方向保留完整模 16 方向；非轨道方向只保留模 4 父点及退出事实。

证明。由 $M^2=M+I$ 逐次乘得以下恒等式：

$$
\begin{aligned}
M^3&=I+2M,&M^4&=2I+3M,&M^5&=3I+5M,\\
M^6&=5I+8M,&M^8&=13I+21M.
\end{aligned}
$$

模 2 时 $M^3$ 为标量而 $M$ 不是，故秩为 3。模 4 时秩是 3 的倍数，$M^3$ 非标量而 $M^6$ 为标量，故为 6。模 8 时仍为 6。模 16 时 $M^6$ 非标量，但 $(5I+8M)^2\equiv9I$，结合提升二分得秩 12。模 2、4 的射影点数分别为 3、6，所以轨道全满。

模 3 时 $M^4$ 为标量而 $M^2$ 不是，故秩为 4。模 9 的秩只能为 4 或 12，$M^4=2I+3M$ 非标量，所以为 12，两个层的点数也恰为 4、12。模 5 时 $M^5$ 为标量而 $M$ 不是，故秩为 5；六点射影直线中 $[1:3]$ 是固定点，因为 $M(1,3)=(3,4)=3(1,3)$，它不在五点轨道中，故正是唯一缺点。模 7 时 $M^8$ 为标量而 $M^4$ 不是，阶整除 8 而不整除 4，故为 8，填满八点射影直线。这些是矩阵恒等式与阶的论证；例如模 5 的 $M^5=3I$ 并不表示矩阵周期为 5，其矩阵周期为 20，因为 3 模 5 的乘法阶为 4。

直接代入给 $\mathcal Q(M(n,z))=-\mathcal Q(n,z)$。奇单位的平方模 8 都是 1，所以 $\mathcal Q\equiv\pm1$ 是射影良定义的条件，且轨道满足它。在第一图 $[1:t]$，条件为

$$
t(t-1)\equiv0\ \text{或}\ 2\pmod8.
$$

积为零时，相邻两因子中的奇数可逆，偶数必须为零模 8，得 $t=0,1$。积为 2 时，若 $t=2u$ 为偶数，则 $u(2u-1)\equiv1\pmod4$，其中 $u$ 为奇数，解得 $u\equiv1\pmod4$，故 $t\equiv2\pmod8$；若 $t-1=2u$，则 $u(2u+1)\equiv1\pmod4$，解得 $u\equiv3\pmod4$，故 $t\equiv7\pmod8$。这一图恰给

$$
S=\{0,1,2,7\}\subset\mathbb Z/8\mathbb Z.
$$

在第二图 $[s:1]$、$s$ 偶，条件为 $s(s+1)\equiv0$ 或 2；前者给 $s=0$，后者写 $s=2u$ 后解 $u(2u+1)\equiv1\pmod4$，给 $s=6$。因此该条件总共六个方向，与轨道大小相同，遂是准确轨道。

从模 4 到模 8，秩均为 6，故每个模 4 点恰有一个轨道提升和一个遗漏提升。遗漏方向虽然不命中模 8，仍由其模 4 父点唯一确定，所以模 8 的未来商没有合并两个不同方向。从模 8 到模 16，秩翻倍，轨道父点的两个提升全在轨道；每个遗漏模 8 方向的两个模 16 提升却只保留其模 4 父点，故合并。这产生 12 个末层轨道类与 6 个退出类。模 5 的唯一无命中方向本身只有一点，也不造成方向间合并。其余满轨道情形立即给完整方向的区分。$\square$

**定理 120.6（固定数量的全部局部划分与满剩余容量）。** 令 $s_p=\min(e_p,\nu_p(n))$，其中 $(e_2,e_3,e_5,e_7)=(4,2,1,1)$。下表每个类都是整数 $z$ 轴上的周期集合；“单独”表示各个所列剩余类分别成类。本节表函数 $K_p(s_p)$ 表示该行类数，按 $n$ 的截断赋值索引，区别于定理 120.4 中按模数指数索引的单位情形函数 $K_p(e)$；$w_p(s_p)$ 表示一个类在模 $p^{e_p}$ 完整剩余系中所含剩余数的最大值。固定 $n$ 的两个 $z$ 具有相同 gcd5040 全未来，当且仅当对四个素数分别落在各自的同一个类中。

| 120.6 二进条件 | 完整的 $z$ 类 | $K_2(s_2)$ | $w_2(s_2)$ |
| --- | --- | --- | --- |
| $s_2=0$ | 置 $t=zn^{-1}\pmod{16}$。$t\bmod8\in S=\{0,1,2,7\}$ 的八个模 16 剩余各自单独；$t\bmod8\in\{3,4,5,6\}$ 的四个模 8 同余类各自成类 | 12 | 2 |
| $s_2=1$，$a_*=n/2$ 为奇数 | 八个偶 $z\bmod16$ 各自单独；$z\equiv a_*\pmod4$ 为一类；$z\equiv3a_*\pmod4$ 中两个不同模 8 剩余各自成类 | 11 | 4 |
| $s_2=2$ | 所有奇 $z$ 为一类；$z\equiv2\pmod8$ 与 $z\equiv6\pmod8$ 各为一类；$z\equiv0,4,8,12\pmod{16}$ 各自单独 | 7 | 8 |
| $s_2=3$ | 五个截断赋值类 $\min(4,\nu_2(z))=0,1,2,3,4$ | 5 | 8 |
| $s_2=4$ | 五个截断赋值类 $\min(4,\nu_2(z))=0,1,2,3,4$ | 5 | 8 |

| 120.6 三进条件 | 完整的 $z$ 类 | $K_3(s_3)$ | $w_3(s_3)$ |
| --- | --- | --- | --- |
| $s_3=0$ | 九个 $z\bmod9$ 各自单独 | 9 | 1 |
| $s_3=1$ | $z\equiv1\pmod3$、$z\equiv2\pmod3$ 各为一类；$z\equiv0,3,6\pmod9$ 各自单独 | 5 | 3 |
| $s_3=2$ | 三个截断赋值类 $\min(2,\nu_3(z))=0,1,2$ | 3 | 6 |

| 120.6 其余素数条件 | 完整的 $z$ 类 | $K_p(s_p)$ | $w_p(s_p)$ |
| --- | --- | --- | --- |
| $s_5=0$ | 五个 $z\bmod5$ 各自单独 | 5 | 1 |
| $s_5=1$ | $5\mid z$ 与 $5\nmid z$ | 2 | 4 |
| $s_7=0$ | 七个 $z\bmod7$ 各自单独 | 7 | 1 |
| $s_7=1$ | $7\mid z$ 与 $7\nmid z$ | 2 | 6 |

证明。先处理除含量后保留完整射影方向的情形。两个点必须先有相同

$$
d=\min\{e,\nu_p(n),\nu_p(z)\}.
$$

若 $d<e$，两个本原二元组在局部环上同射影，当且仅当其行列式为零：取一方的单位坐标解比例，另一方的本原性保证比例仍为单位。因而这里的判据为

$$
p^{e-d}\mid\frac{n}{p^d}\frac{z'-z}{p^d}
\quad\Longleftrightarrow\quad p^{e+d}\mid n(z'-z).
$$

若 $s=\nu_p(n)<e$，这等价于 $z'\equiv z\pmod{p^{e+d-s}}$；若 $s\ge e$，在共同赋值相等后此条件自动成立。$d=e$ 的饱和类另列，不能套用本原方向判据。

在模 9 上，$s_3=0$ 时 $d=0$ 且 $n$ 为单位，故必须完整保留 $z\bmod9$。$s_3=1$ 时，单位 $z$ 的 $d=0$ 要求相同模 3 剩余，给两个单位类；$3\mid z$ 时 $d=1$，除以 3 后第一坐标为单位，要求 $z\bmod9$ 相同，给三个类。$s_3=2$ 时只剩截断赋值，其中 $9\mid z$ 是饱和零类。模 5、7 的 $n$ 为单位时同样保留每个 $z$ 剩余；模 5 唯一无命中方向 $[1:3]$ 自成一类，不能把它删掉。若 $p\mid n$，只可能是 $p\mid z$ 的零标签或单位 $z$ 的方向 $[0:1]$，得到各自两类。

模 16 在 $d\ge1$ 时只剩精度至多 3，故仍可用上述完整方向判据。$n$ 为奇数时 $d=0$，定理 120.5 在第一图直接给表中八个模 16 轨道类和四个模 8 退出类；后四类分别合并 $t$ 与 $t+8$，其模 4 父点彼此不同。

设 $\nu_2(n)=1$，写 $n=2a_*$、$a_*$ 奇。偶 $z$ 总有 $d=1$，除含量后的第一坐标为奇数，故八个偶剩余完整保留。奇 $z$ 的 $d=0$，用第二图 $[w:1]$，其中

$$
w=nz^{-1}\pmod8\in\{2,6\}.
$$

遗漏方向 $w=2$ 等价于 $z\equiv a_*\pmod4$，它们有同一个模 4 父点，合成含四个模 16 剩余的一类。轨道方向 $w=6$ 等价于 $z\equiv3a_*\pmod4$，须完整保留模 16 方向，判据 $16\mid n(z'-z)$ 恰为 $z'\equiv z\pmod8$，所以分成两个类。遗漏的奇分支与保留的奇分支并不对称。

设 $\nu_2(n)=2$。奇 $z$ 总给 $w=n/z\equiv4\pmod8$，这是遗漏方向，且模 4 父点恒为 $[0:1]$，所以所有奇数成一类。若 $\nu_2(z)=1$，则 $d=1$，判据要求相同模 8 剩余，给 2、6 两类。若 $4\mid z$，则 $d=2$，归一化第一坐标为奇，要求相同模 16 剩余，给 0、4、8、12 四类。

设 $\nu_2(n)=3$。奇 $z$ 的完整模 16 方向恒为 $[8:1]$，其模 8 约化在轨道中，故这些奇数同类。$\nu_2(z)=1$ 时共同含量为 1，所需模 4 同余在该赋值层内自动成立；$\nu_2(z)=2$ 时共同含量为 2，所需模 8 同余也自动成立。但 $8\mid z$ 时两种情况的共同含量同为 3，仍须区别

$$
z\equiv8\pmod{16}\ \Longrightarrow\ [n/8:z/8]=[1:1]\pmod2,
\qquad
z\equiv0\pmod{16}\ \Longrightarrow\ [1:0]\pmod2.
$$

因此最后两类不能因共同含量相等而合并，恰得到表中五个截断赋值类。若 $16\mid n$，则 $d<4$ 时归一化第一坐标在剩余精度下为零，方向总为 $[0:1]$，只保留 $d$；$16\mid z$ 则是独立零标签，也给五类。

这些分支对每个 $z$ 恰选一类，且每类在完整剩余宇宙中都有点。数出各同余类或赋值类所含的剩余数，便得表中类数和最大类大小。四素数幂的联合相同性由定理 120.3 等价于整个 gcd 未来相同性。$\square$

### 120.4. 实际区间的联合占用与互素数量的闭式

**定理 120.7（联合 CRT 与取整容斥的实际容量）。** 对任一整数区间 $I=[A,B]\cap\mathbb Z$，定义

$$
W_I(m,r)=
\begin{cases}
\left\lfloor\dfrac{B-r}{m}\right\rfloor-
\left\lfloor\dfrac{A-1-r}{m}\right\rfloor,&A\le B,\\
0,&A>B,
\end{cases}\qquad m\ge1.
$$

它与剩余代表元的选择无关。令 $\mathcal P_p(n)$ 为定理 120.6 的局部划分。对四个局部类组成的元组 $C$，按以下方式定义 $N_C$。

一个同余类给基础条件 $z\equiv r_p\pmod{m_p}$，其中 $m_p$ 为 $p$ 的幂。有限赋值类 $\nu_p(z)=d_p<e_p$ 给基础条件 $z\equiv0\pmod{p^{d_p}}$，另排除 $p^{d_p+1}\mid z$；饱和赋值类只给 $z\equiv0\pmod{p^{e_p}}$。第一表中的斜率同余乘以单位 $n$ 后也是这种普通同余。设 $E$ 是带排除条件的素数集合，$D_C=\prod_pm_p$。对每个 $T\subseteq E$，把 $T$ 中素数的基础模数提升一层，并用 CRT 得到剩余 $r_T$ 与模数

$$
D_T=D_C\prod_{p\in T}p.
$$

模数为 1 时只有剩余 0。则准确实际占用与类数为

$$
N_C=\sum_{T\subseteq E}(-1)^{|T|}W_{I_n}(D_T,r_T),\qquad
Q_{5040}(n)=
\sum_{C\in\mathcal P_2(n)\times\mathcal P_3(n)\times\mathcal P_5(n)\times\mathcal P_7(n)}
\mathbf1_{\{N_C>0\}}.
$$

若记完整剩余宇宙的容量与最大类大小为

$$
K(n)=\prod_pK_p(s_p),\qquad W(n)=\prod_pw_p(s_p),
$$

则表中的数组分别是

$$
\begin{aligned}
K_2&=(12,11,7,5,5),&w_2&=(2,4,8,8,8),\\
K_3&=(9,5,3),&w_3&=(1,3,6),\\
K_5&=(5,2),&w_5&=(1,4),\\
K_7&=(7,2),&w_7&=(1,6).
\end{aligned}
$$

从 $s_p=0$ 开始索引。$L>0$ 时有

$$
\left\lceil\frac{\min(L,5040)}{W(n)}\right\rceil
\le Q_{5040}(n)\le\min\{L,K(n)\},
$$

$L\ge5040$ 时 $Q_{5040}(n)=K(n)$；$L=0$ 时 $Q_{5040}(n)=0$。

证明。$W_I(m,r)$ 直接数出可写为 $r+jm$ 且落在区间的整数 $j$，故是准确同余占用。不同素数的基础模数互素，CRT 恰给它们的共同解；对有限赋值排除条件作容斥，恰留下而且只留下指定类元组中的实际 $z$。定理 120.6 说明这些联合类就是未来等价类，所以数 $N_C>0$ 得准确容量。这里的每一计数先形成联合条件，再与实际区间相交，没有把区间内的局部边缘当作独立随机量或独立可达集合。

占用类数至多是区间点数 $L$，也至多是完整宇宙中的类数 $K(n)$。由 CRT，完整联合类的剩余数等于局部类剩余数的积，至多 $W(n)$。在 $I_n$ 里取长度 $\min(L,5040)$ 的子区间，其中各点模 5040 互异，每类至多占 $W(n)$ 个点，得到下界。当 $L\ge5040$，区间含完整剩余系，每个由 CRT 实现的非空元组都出现，故达到 $K(n)$。

例如 $n=5040$ 的实际区间是 $[7560,8400]$，长度 841；它没有 5040 的倍数。故完整剩余宇宙中的 $\gcd(z,5040)=5040$ 类没有实际来源，不能在这个短区间直接采用 $K(n)=60$。$\square$

**定理 120.8（互素数量的碰撞类与实际闭式）。** 若 $\gcd(n,5040)=1$，置 $B_8=\{3,4,5,6\}\subset\mathbb Z/8\mathbb Z$。任意整数 $z,z'$ 的 gcd 全未来相同，当且仅当

$$
z\equiv z'\pmod{5040}
\quad\text{或}\quad
\left(z\equiv z'\pmod{2520}\ \text{且}\ zn^{-1}\bmod8\in B_8\right).
$$

完整模 5040 宇宙恰有 2520 个单剩余类和 1260 个双剩余类，总数 3780。实际支持上的准确公式为

$$
Q_{5040}(n)=
\begin{cases}
0,&L=0,\\
L,&1\le L\le2520,\\
L-\displaystyle\sum_{r\in nB_8\bmod8}W_{[A,B-2520]\cap\mathbb Z}(8,r),&2520<L<5040,\\
3780,&L\ge5040.
\end{cases}
$$

中间式也在 $L=5040$ 给正确值。在互素 $n$ 的域内，长度条件 $L\ge5040$ 等价于 $n\ge30239$；这是容量饱和的充分条件，不声称是最早饱和阈值。

证明。奇素数部分要求 $z\equiv z'\pmod{315}$。二进单剩余类要求模 16 相同，联合为模 5040 相同；二进退出类要求模 8 相同及遗漏斜率条件，联合为模 2520 相同。因此第二分支的非平凡伙伴恰是加 2520，它保持模 8 斜率。十六个二进剩余中八个各自保留，另八个两两合并，所以完整宇宙中有 $8\cdot315=2520$ 个单类和 $4\cdot315=1260$ 个双类。

若 $L\le5040$，不同实际整数不可能模 5040 相同。所有非平凡碰撞只能为 $(z,z+2520)$，其较小端点恰在 $[A,B-2520]$，并满足 $z\bmod8\in nB_8$。同一类不能在此区间含三个点，故这些碰撞对彼此不重叠，按较小端点的四个模 8 条件计数后从 $L$ 中扣除即可。$L\le2520$ 时没有碰撞；$L=5040$ 时端点区间长度为 $2520=315\cdot8$，恰扣 $4\cdot315=1260$。更长区间含完整剩余系，所以一直为 3780。

互素 $n$ 必为 $6u+1$ 或 $6u+5$，相应 $L$ 为 $u$ 或 $u+1$。第一支的长度条件是 $u\ge5040$，第二支为 $u\ge5039$；在这两种允许余数中合起来恰为 $n\ge30239$。该等价只针对长度条件，不能把它加强为饱和的必要条件。

有一个实际碰撞发生在 $n=15131$：

$$
v=(7564,1),\quad v'=(4,5041),\qquad
z=22697,\quad z'=25217=z+2520.
$$

两来源均非负，直接代入 $2a+3b$ 均为 15131，代入 $3a+5b$ 得上述 $z,z'$。实际区间为 $[22697,25218]$。$15131$ 与 $2,3,5,7$ 都互素；模 8 有 $n=3,z=1,n^{-1}=3$，故 $z/n=3\in B_8$。所证判据保证它们全部 gcd 未来相同，但下一精确数量和组成不同，组成差为 $(-7560,5040)=-2520(3,-2)$。

本定理的 3780 属于仅作 $\rho$ 的未来商。它与较早的 $+2$ 任务有相同数值，不提供两个操作契约、编码或等价关系的认同。实际记录仍按定理 120.2 取 $Q_{5040}(n)$ 类，而不是不分区间地一律取 3780。$\square$

### 120.5. 整除退化与联合自主机器

**定理 120.9（$H\mid n$ 的退化及实际除数占用）。** 对任意 $H\ge1$，若 $H\mid n$，则

$$
R_H(n,z)=R_H(n,z')\ \Longleftrightarrow\ \gcd(z,H)=\gcd(z',H).
$$

若 $d=\gcd(z,H)$，第 $k$ 项准确为

$$
\gcd(y_k,H)=d\gcd(F_k,H/d).
$$

令 $\mu$ 为 Möbius 函数，则实际类数为

$$
Q_H(n)=\sum_{d\mid H}\mathbf1_{\left\{
\sum_{t\mid H/d}\mu(t)W_{I_n}(dt,0)>0\right\}}.
$$

长度至少 $H$ 时它等于除数个数 $\tau(H)$。特别地 $H=5040$ 的完整除数容量为 $5\cdot3\cdot2\cdot2=60$，短区间仍取上述占用。

证明。$H\mid n$ 给 $y_k\equiv F_kz\pmod H$。写 $z=du,H=dH'$，有 $\gcd(u,H')=1$，于是

$$
\gcd(F_kz,H)=d\gcd(F_ku,H')=d\gcd(F_k,H').
$$

这证明充分性；$k=1$ 的读数就是 $d$，证明必要性。对于 $d\mid H$，条件 $\gcd(z,H)=d$ 的指标为

$$
\mathbf1_{\{d\mid z\}}\sum_{t\mid H/d}\mu(t)\mathbf1_{\{dt\mid z\}}.
$$

把它对实际区间求和就是内层取整和，再数非空类即可。$z=0$ 时也成立：$d<H$ 的 Möbius 和为零，$d=H$ 时为一。完整剩余系中每个除数都可作为 gcd 出现，给饱和结论。

实际 $n=0$ 只含 $z=0$，全部读数为 $H$，所以 $Q_H(0)=1$；$n=1$ 为空，故 $Q_H(1)=0$。$H=1$ 时素数标签元组为空，所有读数恒为 1，非空纤维类数为一，空纤维类数为零。$\square$

**定理 120.10（联合域、闭合标签更新与最小 42840 态机器）。** 定义实际联合域

$$
\mathcal D=\{(n,z)\in\mathbb N^2:5n-3z\ge0,\ 2z-3n\ge0\},\qquad
T(n,z)=(z,n+z).
$$

考虑允许 $\mathcal D$ 中任意点初始化的确定性机器，只含一步操作 $T$，当前读出为下一数量的 $\gcd(z,H)$。其最少使用状态数为

$$
\prod_{p^e\parallel H}G_p(e).
$$

标签给出达到下界的闭合机器：非零标签的 $d,h$ 保持，$h>0$ 时 $x_h\mapsto Mx_h$，亦即 $\tau\mapsto\tau-1\pmod{r_h}$；无命中与饱和零标签保持。$H=5040$ 时最小状态数恰为

$$
40\cdot17\cdot7\cdot9=42840.
$$

证明。$T(n,z)$ 的逆来源为

$$
(2z-3n,2n-z)=(b,a+b),
$$

所以 $\mathcal D$ 前向不变，并与来源上的 $\rho$ 相同。单个固定 $n$ 切片无需也通常不满足这种不变性。$M$ 可逆，保持两坐标生成的局部理想，因而保持共同含量 $d$。每个 $O_j$ 在 $M$ 及其逆下都不变，所以命中层与 $h$ 也保持。约化与 $M$ 交换，得到所述保留方向更新；由 $x_h=M^{1-\tau}[1:0]$ 得相位减一。

标签上的下一读出可直接定义：零标签给指数 $e$；无命中标签 $h=0$ 给指数 $d$；其余标签给 $d$ 加上最大的 $1\le j\le h$，使 $x_h$ 约化到第 $j$ 层等于 $[1:0]$，若无这样的层则加零。这就是 $y_1=z$ 的核条件；各素数幂相乘得到 $\gcd(z,H)$。因此更新和读出都在标签上良定义。

每个模 $H$ 的联合剩余对确有实际来源。给定 $(\bar n,\bar z)$，在模 $H$ 下应用 §5.4 的整数逆矩阵，取得 $\bar a,\bar b$，再取二者的非负整数代表元。其确切观察对 $(2a+3b,3a+5b)$ 属于 $\mathcal D$ 并实现给定剩余。CRT 把各素数幂的任意联合剩余对合成一个模 $H$ 剩余对，因此定理 120.4 所数的每个标签元组都能在这个联合域实现。这里并未要求这些来源共享一个确切 $n$。

若一个确定性机器在初始化时合并两个不同未来类，则相同状态经同一转移反复读出，得到完全相同未来，与两来源某个正时刻的不同读数矛盾。定理 120.3 因而给出所有标签元组数的下界，上述闭合构造达到它。

在二进剩余精度 $m=1,2,3,4$，本原类数分别为 $3,6,12,18$：后两项分别是 $6+6$ 与 $12+6$，保留真实停滞产生的退出类。所以

$$
G_2(4)=1+3+6+12+18=40,\quad
G_3(2)=1+4+12=17,\quad
G_5(1)=1+(5+1)=7,\quad
G_7(1)=1+8=9.
$$

$H=1$ 的空积是一态机器。对于 5040，乘积即 42840。此最小性允许任意实际初始化，不要求所有状态从一个固定初始组成可达；它也不涉及数值的完整恢复、树的次序或括号、窗口位置、取得初始标签的空间，以及加法或乘法操作库。一般 $H$ 的分类与秩参数公式已经成立，但没有由此给出所有素数高次幂秩的数值简式，也没有给每个非互素 $n$、任意 $H$ 都写出类似 5040 的短同余表。$\square$

## 121. 连续观察的准确全局八步与已知数量七步界

### 121.1. 连续前缀契约与整数对引理

**定义 121.1（连续观察长度）。** 本节固定 $H=5040$，沿用定义 120.1 的实际来源、$\mathcal D$、$I_n$ 及 $y_k$，记 $g_k=\gcd(y_k,5040)$。首 $T$ 次严格指 $k=1,\ldots,T$；$T=0$ 是空前缀。全局长度 $T_{\mathrm{all}}$ 是最小非负整数，使任意两个 $\mathcal D$ 中的来源若前 $T$ 个 $g_k$ 相等，就有全部正时刻 $g_k$ 相等。固定纤维的 $T_n$ 是在同一个确切 $n$、$z,z'\in I_n$ 上的同一最小值。外部给定的确切 $n$ 免费决定 $g_0=\gcd(n,5040)$，但全局契约并未供应 $n$。

$R(v)=\gcd(qMv,5040)$ 是 $g_1$，故首 $T$ 次是 $R(v),R(\rho v),\ldots,R(\rho^{T-1}v)$。这固定了读数与替换的索引，不额外向后偏移一步。

**引理 121.2（所有整数初始对的八读数充分性）。** 对任意两个整数初始对 $(n,z),(n',z')\in\mathbb Z^2$，按 $y_0=n,y_1=z,y_{k+2}=y_{k+1}+y_k$ 递推。允许负项，并约定 $\gcd(y,H)=\gcd(|y|,H)$。若两对的 $g_1,\ldots,g_8$ 分别相等，则所有 $k\ge1$ 的 $g_k$ 相等。证明中模 $16,9,5,7$ 分别使用长度 $6,8,5,8$ 的充分前缀；这里不主张这些个别局部长度各自最优。

证明。对每个 $p^e\parallel5040$，前两次截断赋值恢复

$$
d=\min\{e,\nu_p(y_1),\nu_p(y_2)\}
=\min\{e,\nu_p(n),\nu_p(z)\}.
$$

若 $d=e$，所有局部读数恒饱和。否则令 $u_k=y_k/p^d$，这是整数本原递推，剩余精度 $m=e-d$，其可见指数就是原指数减 $d$。两来源相同的前缀因而给相同 $d$ 与相同的本原前缀。因为 $\det M=-1$，本原性在各时刻保持；一个项被 $p$ 整除时，其相邻项必是 $p$ 单位。以下每个素数的本原论证中，把归一化初始对 $(n/p^d,z/p^d)$ 暂记为 $(n,z)$，所以此局部记号下 $u_0=n,u_1=z$。

先处理二进部分。本原 $(n,z)$ 模 2 只有 $(1,0),(1,1),(0,1)$ 三种。前三项 $z,n+z,n+2z$ 中的唯一偶数分别在位置 $s=1,2,3$。$M^3=I+2M\equiv I\pmod2$，所以偶数项恰为 $k\equiv s\pmod3$。当 $u_k$ 为偶数时 $u_{k+1}$ 为奇数，而

$$
u_{k+3}=u_k+2u_{k+1}
$$

使这些偶数项在模 4 的 0、2 之间交替。于是 $s,s+3$ 中恰有一个位置 $\sigma$ 被 4 整除，$1\le\sigma\le6$，且全部被 4 整除的位置恰为 $\sigma\pmod6$。

在这些位置，由 $M^6=5I+8M$ 有

$$
u_{k+6}=5u_k+8u_{k+1}.
$$

模 8 时这等于 $5u_k$，而 $4\mid u_k$，故是否被 8 整除沿整个模 6 类保持。首个 $\sigma$ 的读数区分两个分支：若没有 8 整除，整个类的赋值都恰为 2；若有，则 $u_k$ 为 8 的倍数，$u_{k+1}$ 奇，模 16 得

$$
u_{k+6}\equiv u_k+8\pmod{16}.
$$

所以被 16 整除与恰有赋值 3 的项在该类交替，$\sigma$ 的读数决定交替相位。其它位置的指数已由模 3、模 6 的类确定为 0 或 1。首六项因此恢复整个截断二进序列。剩余精度 $m=1$ 只需偶数相位，$m=2$ 停在 $\sigma$，$m=3$ 停在模 8 有无命中，$m=4$ 才需最后的交替；没有在除含量后偷用更高精度。

再处理三进部分。本原初始对模 3 下，$z=0$、$n=-z$、$n=z$、$n=0$ 四种射影方向分别使前三至四项中的唯一零位置为 $s=1,2,3,4$；当两坐标皆为单位时正负两支穷尽，坐标为零时另一坐标为单位。这从

$$
u_1=z,\quad u_2=n+z,\quad u_3=n+2z,\quad u_4=2n+3z
$$

直接得到。$M^4\equiv2I\pmod3$ 保证全部被 3 整除的位置恰为 $s\pmod4$，已解决剩余精度 $m=1$。

若 $m=2$，写 $u_s=3A_*,u_{s+1}=B_*$，其中 $B_*$ 模 3 非零。由 $M^4=2I+3M$ 和 $M^8=13I+21M$，在 $s,s+4,s+8$ 三个位置，除以 3 后模 3 分别是

$$
A_*,\qquad 2A_*+B_*,\qquad A_*+B_*.
$$

其为零的条件分别为 $A_*=0$、$A_*=B_*$、$A_*=-B_*$。$B_*\ne0\pmod3$ 使三种条件互斥且穷尽，所以三个位置恰有一个被 9 整除。又

$$
M^{12}=(2I+3M)^3
=8I+36M+54M^2+27M^3\equiv8I\pmod9,
$$

故该性质按模 12 重复。只观察 $s,s+4$，若命中 9 就确定其模 12 相位，若两次都未命中就由排除确定第三个相位；两次均在位置 8 以内。这恢复所有三进读数，包括除含量后精度为 1 的情形及先前的饱和情形。

最后，$M^5\equiv3I\pmod5$、$M^8\equiv6I\pmod7$，标量都是单位。因此对任意初始对，包括零对，是否被 5 整除按周期 5 重复，是否被 7 整除按周期 8 重复；分别读前五、前八项足够。四个素数的截断指数一起唯一决定 gcd5040，证明八项引理。所有步骤只使用整数递推，也适用于负的辅助初值。$\square$

### 121.2. 两个准确最坏界及其实际来源

**定理 121.3（全局连续长度恰为八）。** 在定义 121.1 的实际联合域上，$T_{\mathrm{all}}=8$。

证明。上界由引理 121.2 限制到 $\mathcal D$ 得到。下界取两个实际非负来源

$$
v=(6,5042),\qquad v'=(8406,2).
$$

它们的观察坐标分别为

$$
(n,z)=(15138,25228),\qquad(n',z')=(16818,25228),
$$

因为 $2\cdot6+3\cdot5042=15138$、$3\cdot6+5\cdot5042=25228$，另一对同样直接代入得到所示值。其差为 $(1680,0)$，而 $1680=3\cdot560$、$560=16\cdot5\cdot7$。故任意未来数量差 $1680F_{k-1}$ 均为 560 的倍数，二进、模 5、模 7 部分始终相同。

模 9 的初始对为 $(0,1)$ 与 $(6,1)$，模 3 均为 $(0,1)$，其可被 3 整除的位置恰是 $k\equiv0\pmod4$。在 $1,\ldots,7$ 中只需看位置 4，此时 $y_4=2n+3z$ 模 9 分别为 3、6，两个截断三进指数均为 1，其它六个位置均为 0。位置 8 的 $y_8=13n+21z$ 模 9 则分别为 3、0，指数变为 1、2。该位置共同的模 $16,5,7$ 剩余分别为 $6,2,3$，所以确切分离读数为

$$
g_8(v)=6,\qquad g_8(v')=18.
$$

它们恰在第八项首次分开，故所有 $T\le7$ 均不足。$\square$

**定理 121.4（已知确切数量的统一连续界恰为七）。** 对每个 $n\in\mathbb N$，$T_n\le7$，且 $\sup_nT_n=7$。

证明。若两个实际来源有同一个确切 $n$，则免费知道它们相同的 $g_0$。假设另有 $g_1,\ldots,g_7$ 相同。对每个来源只在证明中引入辅助整数初始对 $(z-n,n)$。该递推的第一、二项为 $n,z$，因而其前八项恰是原递推的 $y_0,\ldots,y_7$。相同八个 gcd 由引理 121.2 推出相同全部未来，随即给原来源的全部正时刻相同。辅助对无需有实际非负来源，也不是允许执行的新来源操作；这正是先证明整数对引理的用途。

为证明七不能统一降为六，取

$$
n=10153,\quad v=(5051,17),\quad v'=(11,3377),\qquad
z=15238,\quad z'=16918.
$$

来源数量分别为 $10102+51=10153$、$22+10131=10153$，下一数量分别为 $15153+85=15238$、$33+16885=16918$。定理 117.3 给实际区间 $I_{10153}=[15230,16921]$，两点均在内。$10153$ 模 $2,3,5,7$ 的剩余为 $1,1,3,3$，与 5040 互素。

下一数量差为 $1680$，故未来差为 $1680F_k$，所有二进、模 5、模 7 部分相同。模 9 的初始对为 $(1,1)$、$(1,7)$，它们模 3 相同且只在 $k\equiv3\pmod4$ 有三进命中。首六项中只有位置 3，它的数量 $n+2z$ 模 9 分别为 3、6，所以首六项 gcd 相同。位置 7 的 $8n+13z$ 模 9 分别为 3、0，而共同的模 $16,5,7$ 剩余分别为 $6,3,4$，于是

$$
g_7(v)=6,\qquad g_7(v')=18.
$$

所以 $T_{10153}=7$，与上界共同给准确最坏值。

还可对每个整数 $t\ge0$ 取

$$
v_t=(5051+5040t,17),\quad v'_t=(11+5040t,3377).
$$

它们仍为实际非负来源，共同数量为 $10153+10080t$，下一数量为 $15238+15120t$、$16918+15120t$。$n,z$ 的增量都是 5040 的倍数，所以各自整个 gcd 未来保持为 $t=0$ 的未来，$n$ 也仍互素。故这给出无限个实际纤维 $T_{10153+10080t}=7$。$\square$

**定理 121.5（达到七的一个充分长度条件）。** 若 $3\nmid n$ 且 $L\ge1689$，则 $T_n=7$。此长度条件只保证以下构造可行，不主张必要性或最小性。

证明。$J=[A,B-1680]\cap\mathbb Z$ 至少含九个连续整数。若 $n\equiv1\pmod3$，在 $J$ 选 $z\equiv n\pmod9$；若 $n\equiv2\pmod3$，选 $z\equiv7n\pmod9$。令 $z'=z+1680$，二者均在实际 $I_n$，由整数逆式分别给非负来源。

$1680\equiv6\pmod9$。第一支 $6n\equiv6\pmod9$，第二支 $-6n\equiv6\pmod9$，所以两支的无序剩余对都为 $\{n,7n\}\pmod9$。它们模 3 均满足 $z=n$ 且非零，只在 $k\equiv3\pmod4$ 被 3 整除。首六项唯一这样的项在位置 3，其剩余为 $3n,15n$，都恰含一个因子 3；位置 7 剩余为 $21n,99n$，分别恰含一个因子 3 与被 9 整除。其它素数部分因数量差 $1680F_k$ 而始终相同，即使 $n$ 被 2、5 或 7 整除也如此。这个实际对因此首六项相同、第七项不同。与统一上界合并得结论。$\square$

### 121.3. 零长度、整除纤维与数值恢复边界

**命题 121.6（退化纤维及 gcd 与精确数量的区别）。** 空纤维或单来源纤维有 $T_n=0$。单来源纤维恰为 $n=0,2,3,4,5,7$，空纤维为 $n=1$。更一般地，$T_n=0$ 当且仅当整个纤维至多有一个实现的 gcd 全未来类；若 $5040\mid n$，则 $T_n\le1$。即便 $n$ 已知，全部 gcd 未来也不必恢复下一精确数量。

证明。由 $L=C(n)$ 的六余数公式，直接得到空、单来源清单，$n=0$ 的唯一来源所有 $g_k$ 都为 5040。空前缀对任意两个来源都相等，所以它能决定未来恰当且仅当纤维中任意两个来源的未来相同；空纤维按全称命题的空真处理。多个组成也可能只有一个未来类，不能只数来源就断言正长度。若 $5040\mid n$，定理 120.9 已给

$$
g_k=d\gcd(F_k,5040/d),\qquad d=\gcd(z,5040)=g_1,
$$

所以第一项决定全部未来。

取实际来源 $(15120,0)$、$(0,10080)$，共同 $n=30240$，却有 $z=45360$、$z'=50400$。它们相差 5040，每个未来差为 $5040F_k$，故所有 gcd 读数相同而精确下一数量不同。这也排除了由 gcd 未来恢复组成的主张，更不提供树的次序与括号。

本节得到的是连续前缀长度 $8$ 与最坏固定纤维长度 $7$；对其余 $n$ 没有完整给出 $T_n$。选非连续时刻的查询数是另一项最小化，§122 将在同源重置契约下给出其准确全局值与最坏已知数量值。这里的连续长度不能替代 §118 完整三窗词的查询数、未知窗口相位的恢复，或任一取得过程的工作空间与总替换成本。$\square$

## 122. 同源重置的选择时刻查询：全局七问与最坏已知数量六问

### 122.1. 查询契约、共同时间与完整局部表

**定义 122.1（选择正时刻的确定性查询复杂度）。** 固定一个实际来源 $v\in\mathbb N^2$，每次可以从这个相同原始来源的重置副本选一个整数 $k\ge1$，返回完整 $g_k=\gcd(qM^kv,5040)$。不同查询可以不按时刻递增，选下一个时刻可以依赖全部先前答案。一次完整 gcd 观察计一问，沿副本执行中间替换不免费附送中间读数。重置不能换成同数量的另一个来源。

目标是输出 $R_{5040}(n,z)$ 的全未来等价类，或一个等价的完整解码器。无需恢复确切 $n,z$、组成、树或未知窗口相位。记 $D_{\mathrm{all}}$ 为未供应 $n$ 时对全体实际来源的最小确定性最坏查询数；记 $D(n)$ 为免费供应确切 $n$ 后、对实际 $I_n$ 的同一最小值。空纤维约定 $D(1)=0$，这与一个已有来源无需观察是不同情况。计算索引、算术、重置资源、工作空间与逐步替换工作量均与查询次数分开。

**引理 122.2（L1：周期与合法共同查询）。** 每个 gcd5040 未来的周期都整除 120。一次查询可以独立指定

$$
r=k\bmod3,\qquad s=k\bmod8,\qquad b=k\bmod5,
$$

但它的模 4 列必为 $c=s\bmod4$。每个这样的三元组都恰有一个代表 $k\in\{1,\ldots,120\}$。等价地，模 12 剩余 $u$ 与模 8 剩余 $s$ 能来自同一时刻，当且仅当 $u\equiv s\pmod4$。

证明。记 $f_p(k)=\nu_p(g_k)$。定理 120.3 对 $h\ge1$ 的非零局部标签给

$$
f_p(k)=d+\sum_{j=1}^{h}\mathbf1_{\{k\equiv\tau\pmod{r_j}\}},
$$

零标签恒为 $e$，无命中标签恒为 $d$。所需秩 $3,6,6,12;4,12;5;8$ 全部整除 120，故各局部指数及其乘积都具有所述周期。此结论是 gcd 周期，不是确切数值周期，也没有把射影秩当成矩阵周期。

模数 3、8、5 两两互素，CRT 给唯一模 120 剩余；零剩余选正代表 120。模 12 与模 8 的最大公因数为 4，所以相容条件正是共同模 4 相等；用 $(r,s)$ 选时刻自动执行此条件。代数上的时间零也有相位解释：$y_0=n$ 的核为 $[0:1]=M[1:0]$，恰是相位零的核。因此已知 $n$ 可免费计算该时刻指数；这不允许 $k=0$ 的查询，也不要求物理上向后替换。$\square$

**引理 122.3（L2：全部二进标签及其取得规则）。** 令 $d=\min(4,\nu_2(n),\nu_2(z))$。下面的“行”指模 3 剩余，“正确奇偶”指在该行内属于 $\tau\pmod6$；同一行的另一个奇偶是错误奇偶。表列尽全部标签：

| 122.3 共同含量与深度 | $k\not\equiv\tau\pmod3$ | 同行而 $k\not\equiv\tau\pmod6$ | $k\equiv\tau\pmod6$ |
| --- | --- | --- | --- |
| $d=4$，饱和零标签 | 恒为 4 | 恒为 4 | 恒为 4 |
| $d=3,h=1$ | 3 | 同行一律为 4，无需再分奇偶 | 同行一律为 4 |
| $d=2,h=2$ | 2 | 3 | 4 |
| $d=1,h=2$，退出 | 1 | 2 | 3 |
| $d=1,h=3$，末层轨道 | 1 | 2 | 4 |
| $d=0,h=2$，退出 | 0 | 1 | 2 |
| $d=0,h=4$，末层轨道 | 0 | 1 | $k\equiv\tau\pmod{12}$ 时为 4，另一提升为 3 |

$d=3$ 的相位只按模 3 定义，该行的最后两列仅合起来表示同行，不另选模 6 标签。取三个模 3 行互异的查询，能恢复 $d$；若 $d<4$，能恢复唯一升高读数所在行 $t=\tau\bmod3$。除了一种情况外，这已决定全部二进标签；尚未完成的情况恰为 $d\le2$ 且该升高读数等于 $d+1$，这时再在行 $t$ 取相反奇偶的一问即可完成。

证明。模 2、模 4 的轨道全满，故没有首层无命中或深度 1 退出；模 4 到模 8 的停滞允许深度 2 退出；模 8 到模 16 的全提升排除剩余精度 4 中的深度 3 退出。把相位公式按剩余精度 $4-d$ 截断，正好得到表中所有行，也证明这些行穷尽。

三个不同模 3 行中，$d<4$ 时恰有一个读数大于 $d$，另两个等于 $d$；$d=4$ 时全为 4。因此最小值恢复 $d$，升高行恢复 $t$。$d=3$ 时行就是完整标签。$d\le2$ 时，升高读数至少为 $d+2$ 就已到正确奇偶，表中对应终端值决定标签；只有值 $d+1$ 表示落在错误奇偶。同行换成相反奇偶必到 $\tau\pmod6$。保留实际查询时刻 $k$ 后，终端的解释逐项为：

- $d=2$ 时值 4 给相位 $k\pmod6$；
- $d=1$ 时值 3、4 分别给 $h=2,3$，相位均为 $k\pmod6$；
- $d=0$ 时值 2 给深度 2 退出及相位 $k\pmod6$，值 3 给深度 4 轨道及相位 $k+6\pmod{12}$，值 4 给深度 4 轨道及相位 $k\pmod{12}$。

这些终端值互不混淆；尤其值 3 已确定另一模 12 提升，不留下待查的二进相位。$\square$

**引理 122.4（L3：全部三进标签及其取得规则）。** 令 $d=\min(2,\nu_3(n),\nu_3(z))$。完整表为

$$
f_3(k)=
\begin{cases}
2,&d=2,\\
1+\mathbf1_{\{k\equiv\tau\pmod4\}},&d=1,\\
\mathbf1_{\{k\equiv\tau\pmod4\}}+
\mathbf1_{\{k\equiv\tau\pmod{12}\}},&d=0.
\end{cases}
$$

三个不同模 4 列的查询以最小值恢复 $d$。若 $d<2$，有升高读数时该列就是 $\tau\bmod4$；没有升高读数时，唯一未访问的列就是该列。$d=1$ 只需列；$d=0$ 时，同一已知列上至多两个不同模 3 行的测试决定其完整模 12 相位。

证明。模 3、9 轨道全满，没有退出或本原无命中标签，所以相位公式给显示表。三个不同列中至少两个在相位列外，故最小值准确为 $d$。若未命中升高列，由四列的穷尽性只能在遗漏列。$d=1$ 的相位只需模 4，已完成。$d=0$ 时，值 2 直接给查询时刻的模 12 相位；值 1 只排除该列中的当前模 3 行。若该列已测过一次值 1，再测一个不同行，命中值 2 则直接确定，仍为 1 则排除第二行，只剩第三行。如果该列尚未测过，两次不同行的测试同样通过命中或排除确定唯一行。列与行合起来才是模 12 相位；其与模 8 槽位的相容性必须按引理 122.2 实行。$\square$

**引理 122.5（L4：模 5、模 7 的等值测试解码）。** 模 5 的标签有：常指数 1 的零标签、常指数 0 的本原无命中标签，以及五个模 5 相位的单峰标签。五个不同模 5 查询分别产生全命中、全未命中或唯一命中，准确识别它们。模 7 的标签有：常指数 1 的零标签与八个模 8 单峰相位。七个不同模 8 查询准确识别这些标签。

若确切 $n$ 已知且 $7\nmid n$，只可能有相位 $1,\ldots,7\pmod8$，在其中选六个不同槽位即可。若 $7\mid n$，则只可能是零标签或相位 0，任何非零模 8 槽位的一问可区分。

证明。模 5 轨道长度为 5 且恰漏一个射影方向，模 7 长度为 8 且轨道全满。内容饱和时全命中；其它情形按定理 120.3 恰是一相位命中，或模 5 的唯一无命中。五个不同模 5 坐标覆盖全部相位，给第一结论。七个不同模 8 槽位中，七次命中表示零标签，一次命中指出被测相位，零次命中表示唯一未测相位；两至六次命中不是合法标签的反馈。已知 $7\nmid n$ 时，时间零不是命中，排除零标签与相位 0；剩余七相位用六次测试，通过命中或唯一排除项识别。已知 $7\mid n$ 时，若 $7\mid z$ 则零标签，否则本原方向为 $[0:1]$，即相位 0；在非零槽位二者的指数分别为 1、0。$\square$

### 122.2. 满足共同 CRT 条件的七问与六问策略

**定理 122.6（全局七问上界的联合策略）。** 定义 122.1 的每个实际来源都能用至多七问确定其 gcd 全未来，且所有选定时刻在 $1,\ldots,120$ 内。

证明。每问指定模 3 行 $r$ 和一个尚未用过的模 8 槽位 $s$。将查询按实际执行顺序编号 $i=1,2,\ldots$，每问再强制

$$
k\equiv i+3\pmod5.
$$

按引理 122.2 取唯一正代表 $k\le120$。前五个查询的模 5 坐标因而固定为 $4,0,1,2,3$，与中间反馈分支无关。

首先用 $(r,s)=(0,1),(1,2),(2,3)$，实际时刻依次是 $9,10,11$。它们同时遍历三个模 3 行和模 4 列 1、2、3。记录二进、三进指数，依引理 122.3、122.4 恢复两种共同含量与所述粗相位。

先完成三进标签，穷尽分支如下。

1. 若 $d_3=2$，标签恒饱和，不需追加。
2. 若 $d_3=1$，初始升高列或唯一未测列 0 已决定相位，不需追加。
3. 若 $d_3=0$ 且初始读到指数 2，该实际时刻已决定完整模 12 相位，不需追加。
4. 若 $d_3=0$ 且在列 $c\in\{1,2,3\}$ 初始读到指数 1，使用槽位 $c+4$，并将行取为原来该列所用行加一模 3。此槽位尚未使用，列相同而行不同；命中指数 2 或再排除一行都能完成相位。
5. 若 $d_3=0$ 且初始三次都没有升高，则相位列为 0。追加 $(r,s)=(0,0)$ 与 $(1,4)$ 两问。这是同一列两个不同行；命中或排除给唯一细相位。即使第一问已命中，也可保留第二问，仍满足七问预算。

若初始二进表尚未完成，令 $t$ 为它已知的升高行，令 $\epsilon$ 为与该初始升高查询相反的奇偶。从尚未使用的、奇偶为 $\epsilon$ 的槽位中取最小者，并在行 $t$ 查询。引理 122.3 说明此问完成二进标签。三进追加问可能已经提供了额外二进信息，但可以忽略这些额外信息，仍按此规则取得一个足够上界；若初始二进表已经完成，则省去此问。

这里必须证明所需槽位真正存在。槽位 $0,\ldots,7$ 各有四个奇槽和四个偶槽。初始使用 1、2、3，即奇、偶使用数为 $(2,1)$。三进不追加时保持此数；追加一个槽位时，若 $c=1,3$，使用数为 $(3,1)$，若 $c=2$，为 $(2,2)$；遗漏列分支追加 0、4 后为 $(2,3)$。每个分支都仍留下至少一个奇槽与至少一个偶槽，故二进要求的相反奇偶槽必可用。三进至多两问、二进至多一问，所以此时总数至多六。

再用最小未用槽位、行 0 填到恰七问。八个槽位中至多已有六个，因此填充总可进行。前五问已覆盖所有模 5 坐标，七问又使用七个不同模 8 槽位，引理 122.5 同时完成其余两轴。四个标签共同解码整个未来。所有局部内容、二进退出、三进遗漏列、模 5 无命中及各素数的零标签均在这些分支中；特别地精确零来源也被处理，只需确定其未来类，无须与非零但同余为零的来源分开。每个测试来自一个共同 CRT 时刻，故这证明的是可同时实现的七问策略。$\square$

**定理 122.7（已知确切数量的六问上界）。** 对每个非空实际纤维，$D(n)\le6$；若 $7\mid n$，上述界可改为 $D(n)\le5$，后者只为上界，不声称每个这样的纤维都需五问。所用时刻仍在 $1,\ldots,120$。

证明。采用相同的查询编号模 5 规则与前三问 $9,10,11$，但只允许模 8 槽位 $1,\ldots,7$，永不使用槽位 0。三进内容为 1、2 或初始已有指数 2 的分支仍不需追加。$d_3=0$ 且在列 $c\in\{1,2,3\}$ 初始值为 1 时，仍用槽位 $c+4$ 与不同行的一问完成。

唯一要改的是 $d_3=0$ 且相位列遗漏为 0 的分支。由时间零的相位公式，必有 $3\mid n$。确切 $n$ 已知，所以：若 $9\mid n$，时间零的指数为 2，完整相位必为 $0\pmod{12}$，不需追加；若 $3\mid n$ 但 $9\nmid n$，时间零指数为 1，排除相位 0，只剩模 12 的 4、8 两相位。选行 1、槽位 4，其共同模 12 剩余为 4，指数 2 表示相位 4，指数 1 表示相位 8。它是第 4 问，模 5 坐标为 2，实际正时刻恰为

$$
k=52,\qquad52\equiv1\pmod3,\quad52\equiv4\pmod8,\quad52\equiv2\pmod5.
$$

这完整覆盖遗漏列分支，免费使用的只是由 $n$ 算出的 $g_0$，没有作时间零查询。

随后若初始二进表未完成，仍在其已知行选相反奇偶的最小未用允许槽。允许槽中有四奇三偶，初始使用数为 $(2,1)$，三进至多再用一槽；若追加奇槽则为 $(3,1)$，追加偶槽则为 $(2,2)$，若不追加则不变。每种情况都至少留一个允许奇槽与一个允许偶槽，所以二进追加可行。两轴至迟在第 5 问完成。

若 $7\nmid n$，填到六问，全部槽位在七个非零槽中互异；引理 122.5 的已知数量模 7 解码给完整标签。若 $7\mid n$，模 7 轴已在初始槽位 1 的查询完成，只需填到五问。两种填充均可用最小未用允许槽与行 0；前五个模 5 坐标都完整，故模 5 标签也已获得。

此策略在所有与给定 $n$ 相容的剩余对上正确，因此当然在其实际 $I_n$ 上正确。它没有假设一个短区间能实现所有局部组合；小纤维可以利用支持提前停止，六问与五问是分别对所述域统一成立的上界。$\square$

### 122.3. 不改变来源的对抗下界

**定理 122.8（八个实际相位给全局七问下界）。** 在允许任意正整数时刻、确定性自适应及同源重置的契约下，$D_{\mathrm{all}}\ge7$，所以结合定理 122.6 有 $D_{\mathrm{all}}=7$。

证明。对每个 $\tau\in\{1,\ldots,8\}$，分别取下列两个模 7 剩余的唯一代表元 $\alpha_\tau,\beta_\tau\in\{0,\ldots,6\}$：

$$
\begin{aligned}
\alpha_\tau&\equiv5F_\tau+3F_{\tau-1}\pmod7,\\
\beta_\tau&\equiv-3F_\tau-2F_{\tau-1}\pmod7.
\end{aligned}
$$

令实际来源为

$$
v_\tau=720(\alpha_\tau,\beta_\tau),\qquad720=16\cdot9\cdot5.
$$

这些坐标非负。观察矩阵记为 $C=\begin{pmatrix}2&3\\3&5\end{pmatrix}$。在取剩余代表以前，直接相乘有

$$
C\binom{5F_\tau+3F_{\tau-1}}{-3F_\tau-2F_{\tau-1}}
=\binom{F_\tau}{-F_{\tau-1}}.
$$

取代表元保持这个模 7 等式，而 $720$ 模 7 为单位，所以 $v_\tau$ 的观察方向恰为时间 $\tau$ 的核线。相邻 Fibonacci 数不可能同时为零模 7，故它本原；八点满轨道使这八个方向恰有八个不同模 8 相位。其余三个素数幂的观察坐标均为零，因为来源坐标为 720 的倍数。因此此实际族在任意时刻的完整答案只有两种：模 7 未命中时为 720，命中时为 5040。

取任意确定性策略，沿着每次都回答 720 的路径运行，直到六问或策略提前停止。任意正时刻 $k$，无论多大，都只测试模 8 的一个相位 $k\bmod8$，故这问至多排除一个族成员；重复相位没有新的排除。六问以内至少剩两个成员。它们的相位不同，所以在一个正时刻命中其中一个相位时，全部未来不同。

这一回答路径不依赖过程中更换来源。事实上，取任一最终存活的 $v_\tau$ 并从最初固定它。第一问按定义没有命中它，所以真实答案为 720；若前 $i-1$ 问已经重现相同历史，确定性保证第 $i$ 问选择同一时刻，而最终存活意味着该时刻也没有命中它，故第 $i$ 个真实答案仍为 720。归纳得到完整路径。于是两个最终存活的固定实际来源具有同一全部查询历史，策略的同一输出不能对两个不同未来都正确。它不能在每个来源上六问内停止并成功，证明下界。$\square$

**定理 122.9（已知数量的实际六问下界及充分长区间族）。** 有

$$
D(25920)=6,\qquad \sup_{n\in\mathbb N}D(n)=6.
$$

更一般地，若 $7\nmid n$ 且 $L\ge4321$，则 $D(n)=6$。4321 只为此构造的充分长度，不主张必要性或最早出现六问的阈值。

证明。首先对 $j=0,\ldots,6$ 取七个实际来源

$$
v_j=\bigl(2160(6-j),1440j\bigr).
$$

它们坐标都非负，而且

$$
qv_j=4320(6-j)+4320j=25920,\qquad
qMv_j=6480(6-j)+7200j=38880+720j.
$$

准确区间为 $I_{25920}=[38880,43200]$，长度 4321，这七个值都在区间中且包含两端点。共同 $n\equiv6\pmod7$ 为单位，步长 720 也是单位，所以七个 $z$ 恰遍历模 7 所有剩余。第一坐标为单位的七个射影点正是相位 $1,\ldots,7\pmod8$，相位 0 的核线 $[0:1]$ 不在其中。来源坐标都是 720 的倍数，故其它素数幂部分恒饱和。

沿着五问均回答 720 的自适应路径，槽位 0 不排除任何成员，任何其它槽位至多排除一个。五问后至少两个实际来源仍具有同一个确切 $n$ 和完整查询历史，其模 7 相位不同，未来也不同。定理 122.8 的固定存活来源归纳逐字适用，所以没有五问策略能在该纤维总成功。与六问上界合并，得 $D(25920)=6$ 及准确最坏值。

现在取任意满足 $7\nmid n,L\ge4321$ 的纤维。令

$$
z_j=A+720j\quad(0\le j\le6),\qquad
v_j=\bigl(5n-3(A+720j),\ 2(A+720j)-3n\bigr).
$$

最大下一数量为 $A+4320\le B$，故所有 $z_j\in I_n$，每个 $v_j$ 都是同一个确切 $n$ 的非负来源。任意时刻有

$$
y_k(n,z_j)-y_k(n,z_0)=720jF_k.
$$

因此七个来源共享完全相同的模 720 gcd 部分

$$
h(k)=\gcd(y_k(n,A),720).
$$

这个共同部分可以随 $k$ 变化，不要求恒为 720。同时，$n$ 模 7 为单位、七个 $z_j$ 覆盖全剩余，故仍为七个不同非零相位。

对任意确定性策略，在它选定的每个 $k$ 回答共同 $h(k)$，不带因子 7。每问至多排除该时刻相位的一个来源，槽位 0 不排除任何来源。五问后至少两个来源存活。每个最终存活来源在所有已经选择的时刻都不被 7 整除，而其它部分恰为 $h(k)$；从第一问起按确定性归纳，它就是实现整条自适应路径的一个固定实际来源。两个存活来源未来不同，故五问不足。统一上界给 $D(n)=6$。本构造使用实际区间中的七个点，完全不依赖把短区间内的局部 CRT 边缘独立拼接。$\square$

### 122.4. 退化、工作量与仍未确定的资源

**命题 122.10（实际纤维的零问与整除退化的准确零或一问）。** 非空实际纤维有 $D(n)=0$，当且仅当其全部来源只有一个 gcd 全未来类。$D(0)=0$ 对应一个确实存在的零来源，$D(1)=0$ 只为空纤维约定；单来源纤维 $n=2,3,4,5,7$ 也均为零问。若 $5040\mid n$，则

$$
D(n)=
\begin{cases}
0,&\gcd(z,5040)\text{ 在实际 }I_n\text{ 上恒定},\\
1,&\gcd(z,5040)\text{ 在实际 }I_n\text{ 上不恒定}.
\end{cases}
$$

证明。零问策略只有一个固定输出，能同时适用于所有来源恰当且仅当所有来源的目标类相同。结构零的未来恒为 5040，而 $I_1$ 没有来源；这些与单来源清单均由定理 117.3 得到。全局策略识别结构零所在的未来类即可，不需把它从同一零剩余类的非零实际来源中单独识别。

若 $5040\mid n$，定理 120.9 给 $g_k=d\gcd(F_k,5040/d)$，其中 $d=\gcd(z,5040)$。一问 $k=1$ 就读出 $d$，因此一问足够；若 $d$ 在实际区间恒定，不问即知未来；若有两个实际 $d$ 值，它们第一个未来读数就不同，零问不可能成功。这也包括 $n=0,z=0,d=5040$。类是否实际出现始终以区间占用为准。$\square$

**命题 122.11（不同资源的准确范围）。** 上述选择时刻策略具有正时刻上界 120。若每个重置副本逐步执行 $k$ 次 $\rho$ 后只读一次，则全局七问策略使用的 $\rho$ 次数至多 840，已知数量六问策略至多 720。这些是足够的粗工作量上界，不主张最优。

证明。每一查询由模 $3,8,5$ 的 CRT 选在 $1,\ldots,120$。即使模 120 剩余为零也取 120，不出现时间零查询；实际前三问是 9、10、11，已知数量遗漏列的特殊问为 52。每个查询用不同模 8 槽位，故不会无意重复同一时刻；重置允许后问的时刻小于先问。逐个副本从原来源开始，最多七个或六个长度不超过 120 的替换链，直接相加得 $7\cdot120=840$ 与 $6\cdot120=720$。此计数只含 $\rho$ 次数，不估算副本取得、重置、算术计算和空间。

由定理 121.3、121.4 与定理 122.6—122.9，连续首段的准确全局长度为 8、最坏已知数量长度为 7；任意选择正时刻且同源重置时，准确全局查询数为 7、最坏已知数量查询数为 6。选择查询确实减少了这两个最坏观察次数，但没有由此证明最大所选时刻或总工作量更小。§118 的完整三窗词六问使用不同的允许查询与来源记录；定理 120.10 的 42840 则是任意实际初始化下全部未来标签的数目。这些量不能互换，状态个数本身也不证明本节的准确查询下界。

在本节给出的充分六问族、零问判据及 $5040\mid n$ 的零或一问公式之外，完整的逐 $n$ 函数 $D(n)$ 尚未确定；$7\mid n$ 的五问上界不宣称处处取等。查询最优策略中的最小最大索引、最少总替换工作量，以及随机化期望查询数、带噪反馈、没有同源重置的访问和取得标签所需的工作空间，均未由这些定理解决。目标始终是指定来源的 gcd 全未来类，既不恢复精确整数或树，也不恢复未知窗口相位；这里没有引入其它算术操作，亦不推出 RH、全局 Robin 或素性结论。$\square$

## 追加锚（本行以下为增补区）
## 123. 实际相位二十一与六十一的共同词六问构造

**约定 123.1（来源、完整词域与共同系数）。** 本节及 §§124–125 沿用定义 104.2、104.4、113.1、114.1 和约定 118.1，固定 $H=5040=16\cdot9\cdot5\cdot7$。已知实际相位为

$$
w_j=T^j(2,3)=(F_{3j+3},F_{3j+4})\pmod H,
\qquad T(u,v)=(u+2v,2u+3v),\qquad 0\le j<80.
$$

初始结构标签为 $(\sigma,E)=(1,\mathrm{true})$。未知 $r$ 来自该相位任意返回深度上的一个正值实际合法前缀。候选族合并两种单位初始化 $\varepsilon$；一旦选定来源，它的前缀、初始化、深度、整数值和下一权重行在所有重置中固定。每问重置到这个来源，追加至多三个完整字面窗口并请求 End；成功返回完整 $\gcd(r+C,H)$，非法接缝或不适当 End 都返回同一个 $\mathsf{err}$。空后缀也成功且收费，不存在免费初始读数。目标是原始 $r\bmod H$，成本 $Q_3(5040;w_j)$ 是整个候选族上的最小确定性自适应最坏查询数，允许从最后唯一候选直接推断。

为使用定理 118.2 的完整词域，把后缀位置按低到高分为 $(0,1,2),(3,4,5),(6,7,8)$。初始接缝使位置 0 必为零。每个非空成功词由一个无相邻元素的集合 $I\subseteq\{1,\ldots,8\}$ 唯一给出，并恰在包含 $\max I$ 的完整窗口后结束。前导、中间的 $000$ 都执行；末窗 $100$、$010$ 都可作规范 End，不得裁掉其内部高位零。$I=\varnothing$ 表示空词，非空全零词或额外尾随整窗 $000$ 不成功。完整允许族是全部 55 个成功词及全部恒错尝试，不是下面各策略的小字典。

同一占用集定义

$$
n=\sum_{i\in I}F_{i+1},\qquad s=\sum_{i\in I}F_{i+2},\qquad
(A,B)=\sum_{i\in I}(F_{i-1},F_i)=(2n-s,s-n).
$$

这里 $s$ 是数位移位后的整数，不是接缝 $\sigma$；反向有 $n=A+B,s=A+2B$。定理 118.2 的编号 $n=0,\ldots,54$ 在本节记为词 $V_n$。其在任意实际行 $(u,v)$ 上的物理平移始终是

$$
C_I=Au+Bv=(2u-v)n+(v-u)s.
$$

这些式子是同一个词的整数恒等式。具体地，八个位置的系数对为

$$
(0,1),(1,1),(1,2),(2,3),(3,5),(5,8),(8,13),(13,21).
$$

Fibonacci 递推逐项给 $F_{i-1}=2F_{i+1}-F_{i+2}$、$F_i=F_{i+2}-F_{i+1}$，故求和得到上式。编号的完整性也可直接从定理 118.2 的归纳看出：在 $F_2,\ldots,F_m$ 上，最高位零给 $[0,F_m-1]$，最高位一给 $F_m+[0,F_{m-1}-1]$；两段相邻且不交，空列和单位置启动唯一性归纳。取 $m=9$ 得 $[0,54]$。模平移碰撞不会删掉允许词。所有非空字典词在真实权重上加上正 Fibonacci 数，空词作用于原先正来源；因此模零不会被误当成整数零 End。下文的单位归一化只是坐标变换，不是对来源施加额外操作。

**命题 123.2（实际周期与同词伴随标量）。** 实际行的精确窗口周期为 80，且

$$
T^{40}=\lambda I,\qquad T^{80}=I\pmod H,
\qquad \lambda=1441\equiv(1,1,1,-1)\pmod{(16,9,5,7)},
\qquad\lambda^2=1.
$$

因此对同一字面词，其在 $w_{j+40}$ 和 $w_j$ 上的平移满足 $C_{j+40}=\lambda C_j$。

证明。这里给出命题 105.5 的局部恒等式在当前相位编号中的直接依据。令 $S(u,v)=(v,u+v)$，把行写成列，则 $T=S^3$ 且

$$
S^m=\begin{pmatrix}F_{m-1}&F_m\\F_m&F_{m+1}\end{pmatrix}\quad(m\ge1).
$$

$F_{11}=89,F_{12}=144,F_{13}=233$ 给模 16 的 $S^{12}=9I$ 和模 9 的 $S^{12}=8I$，故两者均有 $S^{24}=I$、$S^{12}\ne I$。$S^8$ 的非对角元为 $F_8=21$，在两轴均非零，所以 $S^8\ne I$。24 的每个真因子都整除 12 或 8，故两轴精确阶都是 24。模 5 有 $S^5=3I$、$S^{10}=-I$、$S^{20}=I$；又 $S^4$ 的非对角元 $F_4=3$ 非零，排除全部真因子，精确阶为 20。模 7 有 $S^8=-I$、$S^{16}=I$，16 的每个真因子都整除 8，故精确阶为 16。

$(0,1)$ 返回意味着 $F_m=0,F_{m+1}=1$，递推还给 $F_{m-1}=1$，所以等价于整个 $S^m=I$。由于 $(2,3)=S^3(0,1)$ 且 $S$ 可逆，$(2,3)$ 有相同的稳定子。于是 $T=S^3$ 在四个局部实际行上的精确周期为 $8,8,20,16$，最小公倍数为 80；这也保证 80 个相位确为不同实际行。$S^{120}$ 在前三轴为 $I$，在模 7 为 $(S^8)^{15}=-I$。CRT 给上述 $\lambda$ 及其平方。最后，同一词的 $A,B$ 不变，故 $A(\lambda u)+B(\lambda v)=\lambda(Au+Bv)$。$\square$

**命题 123.3（共同深度的实际支撑与全策略六问下界）。** 约定 123.1 的每个实际相位都有一个共同返回深度，其正值实际来源覆盖全部模 5040 余数。该合同下，任何确定性自适应策略的最坏查询数至少为六；这一下界包括全部 55 个成功词、恒错词、收费空词和提前停止。

证明。将引理 105.1 的窗数代入 $N=j+80q\ge1$，取其标签 $(1,1)$；命题 123.2 保证下一模行仍是 $w_j$。其实际整数像恰为

$$
[F_{3N+2},F_{3N+3}-1]\cap\mathbb Z,
\qquad\text{长度 }F_{3N+1}.
$$

原因是最高位 $F_{3N+2}$ 为一，邻位 $F_{3N+1}$ 为零，以下至 $F_{3N}$ 的自由非相邻展开给 $[0,F_{3N+1}-1]$。这正是引理 105.1 和定义 113.1 的来源，而非抽象 CRT 直积假设。取一次足够大的 $q$ 使长度至少为 5040，此全正区间就含每个余数的代表；为每个余数选一个实际前缀，它们具有同一深度和实际整数权重行。不同代表可使用不同 $\varepsilon$，各自一经选定便固定。此处既未给每个小深度满支撑，也未给分别固定 $\varepsilon$ 的满纤维。

这也说明后验的实际意义。固定一个可行完整历史，已选字面词由先前回答依次确定；每份 gcd 的四个分量各自限制一个源余数坐标。任一满足这些局部限制的 CRT 元组会归纳地产生相同回答和下一词选择。共同深度满纤维给它一个始终固定的实际源。单位变换 $x=-hr$ 保持满纤维。因此在这个完整候选族上，固定历史的余数后验就是相应局部后验的乘积；这只证明源的共同实现，不扩大词的可用中心。后面的上界对全部余数成立，故也适用于任何支撑较小的实际深度。

下界复用推论 113.7 的坐标轴论证并写明全词量词。固定一个模 $720=16\cdot9\cdot5$ 余数，将它的七个模 5040 提升分别选为上述共同深度的实际源。在任一共同历史上，确定性策略下一词固定。若它成功，则平移 $C$ 固定，所有存活源的模 $16,9,5$ 回答相同，模 7 仅测试 $r\equiv-C\pmod7$。取未命中回答至多排除一个源；已测或不在存活集中的颜色排除零个。非法或 End 不适当的词共同报错，排除零个；空词就是收费的 $C=0$。前五问的每一步都有未命中存活者，五问后至少有 $7-5=2$ 个不同原始余数。若提前停止，存活者只会更多。

每个最终存活源都以原先固定的前缀、初始化和深度实现整段完整历史，故这个对手论证没有逐问换源。策略在同一历史只能给一个答案，不能同时识别两个存活余数。该论证甚至允许任意平移，故当然涵盖完整三窗族，而非只涵盖某个字典或某个前三问。它是整个来源族的确定性最坏下界，不是每个单独来源的固有成本断言。$\square$

**引理 123.4（局部分隔与三个新颜色的收尾接口）。** 对不同 $z,z'\bmod p^a$，令 $t=v_p(z-z')<a$。中心 $c$ 的完整截断深度区分二者，当且仅当 $c$ 与其中一个同余模 $p^{t+1}$。特别地，模 16 对 $\{z,z+8\}$ 要求 $c\equiv z\pmod8$；下文的模 9 对要求中心等于其中一员模 9；模 5 对要求中心等于其中一员模 5。

此外，设前三问测试三个不同模 7 颜色，$U$ 为四个未测颜色；模 $16,9,5$ 后验各是单点或指定二元对。若二进、三进的每个适用分配由一个实际词分隔，合并相同词以后至多有两个词，且颜色不同并属于 $U$；又对 $U$ 的每个颜色都有一个实际词可分隔该支可能的模 5 对，则可以确定地再用恰三问识别全部四个坐标。

证明。若 $c$ 与 $z$ 同余模 $p^{t+1}$，则对 $z$ 的深度大于 $t$，对 $z'$ 恰为 $t$；反之亦然。否则，若在共同的前 $t$ 位以前偏离，二者深度同为那个较小值；若前 $t$ 位相同但下一位均未对上，二者深度同为 $t$。这给必要性和充分性，也给三个特例。

收尾先保留每个未决二进、三进对的分配词，单点不分配，相同词只保留一次。若模 5 仍是对，选 $U$ 中尚未使用的最小颜色的模 5 分隔词；此前至多用两色，故至少还有两色可选，选后至多三词。模 5 已知时跳过这一步。随后仍从相应颜色的这些实际词中，按最小未用颜色补到恰三词。$|U|=4$ 保证每一步存在；新颜色保证不重复词。固定前三问历史后，按规范编号 $n$ 递增查询这三词即可，无须再适应。

全部已分配分隔词保留，模 5 若未决也有分隔词；其余坐标不会因增加回答失去信息。六问一共测试六个不同模 7 颜色。已有命中时直接知道该坐标；全部未命中时，唯一未测的第七色就是该坐标，无须确认。CRT 遂确定归一化余数。这里可合并的是同一实际词，不能只因两个不同词颜色相同就合并；每次应用都须给出对应字面见证、完整联合分配和各色补词。$\square$

**命题 123.5（相位二十一的归一化与十八词字典）。** 实际行及单位为

$$
w_{21}=(568,3173),\qquad h=1961\equiv(9,8,1,1)\pmod{(16,9,5,7)},\qquad h^2=1.
$$

令 $x=-1961r$、$d_n=1961C_{V_n}$，则回答恰为 $\gcd(x-d_n,5040)$。写 $L_n=3n+5s$，有

$$
d_n\equiv L_n\pmod{720},\qquad d_n\equiv s\pmod7.
$$

下表列全本节会使用的十八个实际词；$L$ 只代表模 720 的中心，$\gamma$ 是该同一词的模 7 中心，不能把 $L$ 当成完整相位二十一中心。

| 123.5 词 | $n$ | $s$ | $(A,B)$ | $I$ | 字面窗口 | $L$ | $\gamma$ |
| --- | ---: | ---: | --- | --- | --- | ---: | ---: |
| $V_0$ | 0 | 0 | $(0,0)$ | $\varnothing$ | 空词 | 0 | 0 |
| $V_1$ | 1 | 2 | $(0,1)$ | $\{1\}$ | `[010]` | 13 | 2 |
| $V_2$ | 2 | 3 | $(1,1)$ | $\{2\}$ | `[001]` | 21 | 3 |
| $V_3$ | 3 | 5 | $(1,2)$ | $\{3\}$ | `[000,100]` | 34 | 5 |
| $V_6$ | 6 | 10 | $(2,4)$ | $\{1,4\}$ | `[010,010]` | 68 | 3 |
| $V_7$ | 7 | 11 | $(3,4)$ | $\{2,4\}$ | `[001,010]` | 76 | 4 |
| $V_{11}$ | 11 | 18 | $(4,7)$ | $\{3,5\}$ | `[000,101]` | 123 | 4 |
| $V_{12}$ | 12 | 20 | $(4,8)$ | $\{1,3,5\}$ | `[010,101]` | 136 | 6 |
| $V_{16}$ | 16 | 26 | $(6,10)$ | $\{3,6\}$ | `[000,100,100]` | 178 | 5 |
| $V_{17}$ | 17 | 28 | $(6,11)$ | $\{1,3,6\}$ | `[010,100,100]` | 191 | 0 |
| $V_{18}$ | 18 | 29 | $(7,11)$ | $\{4,6\}$ | `[000,010,100]` | 199 | 1 |
| $V_{21}$ | 21 | 34 | $(8,13)$ | $\{7\}$ | `[000,000,010]` | 233 | 6 |
| $V_{22}$ | 22 | 36 | $(8,14)$ | $\{1,7\}$ | `[010,000,010]` | 246 | 1 |
| $V_{27}$ | 27 | 44 | $(10,17)$ | $\{1,4,7\}$ | `[010,010,010]` | 301 | 2 |
| $V_{32}$ | 32 | 52 | $(12,20)$ | $\{3,5,7\}$ | `[000,101,010]` | 356 | 3 |
| $V_{36}$ | 36 | 58 | $(14,22)$ | $\{2,8\}$ | `[001,000,001]` | 398 | 2 |
| $V_{37}$ | 37 | 60 | $(14,23)$ | $\{3,8\}$ | `[000,100,001]` | 411 | 4 |
| $V_{42}$ | 42 | 68 | $(16,26)$ | $\{5,8\}$ | `[000,001,001]` | 466 | 5 |

证明。$w_{21}=S^{60}w_1$，其中 $w_1=(8,13)$。由命题 123.2 的局部矩阵式，$S^{60}$ 在模 16、9 分别为 $9I,8I$，模 5 为 $I$；模 7 则将 $(F_{66},F_{67})$ 约为 $(F_2,F_3)=(1,2)$。所以该行四轴为 $(8,5),(1,5),(3,3),(1,2)$，CRT 代表正是 $(568,3173)$。$h$ 是单位且自逆；乘 $h$ 后前三轴成为相位一行，而模 7 行仍是 $(1,2)$。相位一的平移为 $8A+13B=3n+5s$，模 7 的平移为 $A+2B=s$，得到所述共同中心式。

每行系数由约定 123.1 的八个位置对在所列 $I$ 上相加，随后 $n=A+B,s=A+2B$ 给编号和移位数。例如 $V_{18}$ 的对为 $(2,3)+(5,8)=(7,11)$；$V_{36}$ 为 $(1,1)+(13,21)=(14,22)$；关键 $V_{16}$ 为 $(1,2)+(5,8)=(6,10)$。全部 $I$ 均不含 0、没有相邻位置且最高位置不超过 8；按三位分组恰得表中词，所有非空末窗非零。因此这些是同一实际词的四轴信息。最后 $x-d_n=-h(r+C_{V_n})$，单位及负号保持完整 gcd；还原原始余数必须取 $r=-1961x$。$\square$

**命题 123.6（相位二十一前三问的完整后验）。** 先查询 $V_0,V_{18}$。记第一问的二进截断深度为 $e=D_2(x)$；若 $e=1$，第三问用 $V_{36}$，称甲支；否则用 $V_{21}$，称乙支。其中 $D_p(z)=\min(v_p(z),a)$，$p^a\parallel5040$，零模 $p^a$ 的深度取 $a$。这三个深度和两个等值位都由完整 gcd 读出。

| 123.6 初问词 | $d\bmod16$ | $d\bmod9$ | $d\bmod5$ | $d\bmod7$ |
| --- | ---: | ---: | ---: | ---: |
| $V_0$ | 0 | 0 | 0 | 0 |
| $V_{18}$ | 7 | 1 | 4 | 1 |
| 甲支 $V_{36}$ | 14 | 2 | 3 | 2 |
| 乙支 $V_{21}$ | 9 | 8 | 3 | 6 |

二进的完整分区如下，深度按三问顺序排列。

| 123.6 二进分支 | 模 16 后验 | 深度三元组 |
| --- | --- | --- |
| 甲一 | $\{6\}$ | $(1,0,3)$ |
| 甲二 | $\{14\}$ | $(1,0,4)$ |
| 甲三 | $\{2,10\}$ | $(1,0,2)$ |
| 乙一 | $\{0\}$ | $(4,0,0)$ |
| 乙二 | $\{8\}$ | $(3,0,0)$ |
| 乙三 | $\{4,12\}$ | $(2,0,0)$ |
| 乙四 | $\{7\}$ | $(0,4,1)$ |
| 乙五 | $\{15\}$ | $(0,3,1)$ |
| 乙六 | $\{3,11\}$ | $(0,2,1)$ |
| 乙七 | $\{1\}$ | $(0,1,3)$ |
| 乙八 | $\{9\}$ | $(0,1,4)$ |
| 乙九 | $\{5,13\}$ | $(0,1,2)$ |

三进分区为：

| 123.6 三进历史 | 甲支模 9 后验 | 乙支模 9 后验 |
| --- | --- | --- |
| $(2,0,0)$ | $\{0\}$ | $\{0\}$ |
| $(1,0,0)$ | $\{3,6\}$ | $\{3,6\}$ |
| $(0,2,0)$ | $\{1\}$ | $\{1\}$ |
| $(0,1,0)$ | $\{4,7\}$ | $\{4,7\}$ |
| $(0,0,2)$ | $\{2\}$ | $\{8\}$ |
| $(0,0,1)$ | $\{5,8\}$ | $\{2,5\}$ |

两支模 5 都依次测试 $0,4,3$：命中三元组 $(1,0,0),(0,1,0),(0,0,1)$ 分别识别 $0,4,3$，全未命中恰留 $\{1,2\}$。模 7 在甲支依次测试 $0,1,2$，乙支测试 $0,1,6$；有命中即识别相应值，全未命中后验分别为

$$
U_{\mathrm{甲}}=\{3,4,5,6\},\qquad U_{\mathrm{乙}}=\{2,3,4,5\}.
$$

无论是否已经命中，下文 $U$ 都指未查询的颜色集；命中后它不再表示后验。

证明。甲支的 $e=1$ 给 $\{2,6,10,14\}$；第二中心 7 对它们深度全为零，第三中心 14 的深度依次为 $2,3,2,4$，得到甲表。乙支第一深度为 $4,3,2$ 时分别给 $0,8,\{4,12\}$；后两中心皆奇数，后二进信息如表。第一深度零时 $x$ 为奇数，中心 7 的深度 $4,3,2,1$ 分别给 $7,15,\{3,11\},\{1,5,9,13\}$。最后四项对中心 9 的深度依次是 $3,2,4,2$；$\{3,11\}$ 的最后深度都为 1。这穷尽模 16。三进中心在甲支是 $0,1,2$，乙支是 $0,1,8$，各占一个模 3 类；恰一问深度正，深度 2 给中心本身，深度 1 给其模 3 类另两员，恰为所列表。模 5 和模 7 的三个中心分别互异，所以最多一次命中，其余为补集。各局部组合由命题 123.3 的共同实际支撑实现，分支条件已包含在第一深度内。$\square$

**命题 123.7（相位二十一的联合分配与同词合并）。** 下列每个适用行分隔所列有序对，深度按对中元素的顺序排列。

| 123.7 分配 | 因子与有序对 | 实际词 | 所用局部中心 | 两个深度 | 颜色 |
| --- | --- | --- | --- | --- | ---: |
| 甲二进 | $16:(2,10)$ | $V_{16}$ | $2\bmod16$ | $(4,3)$ | 5 |
| 甲三进一 | $9:(3,6)$ | $V_2$ | $3\bmod9$ | $(2,1)$ | 3 |
| 甲三进二 | $9:(4,7)$ | $V_{16}$ | $7\bmod9$ | $(1,2)$ | 5 |
| 甲三进三 | $9:(5,8)$ | $V_6$ | $5\bmod9$ | $(2,1)$ | 3 |
| 乙二进一 | $16:(4,12)$ | $V_7$ | $12\bmod16$ | $(3,4)$ | 4 |
| 乙二进二 | $16:(3,11)$ | $V_{11}$ | $11\bmod16$ | $(3,4)$ | 4 |
| 乙二进三 | $16:(5,13)$ | $V_1$ | $13\bmod16$ | $(3,4)$ | 2 |
| 乙三进一 | $9:(3,6)$ | $V_2$ | $3\bmod9$ | $(2,1)$ | 3 |
| 乙三进二 | $9:(4,7)$ | $V_3$ | $7\bmod9$ | $(1,2)$ | 5 |
| 乙三进三 | $9:(2,5)$ | $V_6$ | $5\bmod9$ | $(1,2)$ | 3 |

把单点记为“已知”，适用分配合并后的全部同时情形为以下两个矩阵。

| 123.7 甲二进后验 | 三进已知 | $\{3,6\}$ | $\{4,7\}$ | $\{5,8\}$ |
| --- | --- | --- | --- | --- |
| 甲已知 | $\varnothing$ | $\{V_2\}$ | $\{V_{16}\}$ | $\{V_6\}$ |
| 甲 $\{2,10\}$ | $\{V_{16}\}$ | $\{V_{16},V_2\}$ | $\{V_{16}\}$ | $\{V_{16},V_6\}$ |

| 123.7 乙二进后验 | 三进已知 | $\{3,6\}$ | $\{4,7\}$ | $\{2,5\}$ |
| --- | --- | --- | --- | --- |
| 乙已知 | $\varnothing$ | $\{V_2\}$ | $\{V_3\}$ | $\{V_6\}$ |
| 乙 $\{4,12\}$ | $\{V_7\}$ | $\{V_7,V_2\}$ | $\{V_7,V_3\}$ | $\{V_7,V_6\}$ |
| 乙 $\{3,11\}$ | $\{V_{11}\}$ | $\{V_{11},V_2\}$ | $\{V_{11},V_3\}$ | $\{V_{11},V_6\}$ |
| 乙 $\{5,13\}$ | $\{V_1\}$ | $\{V_1,V_2\}$ | $\{V_1,V_3\}$ | $\{V_1,V_6\}$ |

每格至多两个不同词，其颜色不同且属于对应 $U$。

证明。将命题 123.5 的同词中心代入引理 123.4 就得到分隔表。甲支唯一可能同时重复的颜色是 5；二进 $\{2,10\}$ 与三进 $\{4,7\}$ 指向的确实是同一个 $V_{16}$。它的 $I=\{3,6\}$、字面词 `[000,100,100]`、系数对 $(6,10)$ 给物理平移 $6u+10v$。在 $w_{21}$ 上该平移为 $35138\equiv4898\pmod{5040}$，归一化中心为 $3778$，四轴是

$$
(2,7,3,5)\pmod{(16,9,5,7)}.
$$

所以二进、三进分隔确由同一问完成，它的模 5 中心也固定为 3；没有分别选择两个局部词后拼接。甲支另两个三进对使用颜色 3，与二进颜色 5 不同；两种三进要求互斥。乙支二进颜色属于 $\{2,4\}$，三进颜色属于 $\{3,5\}$，两集不交；同为二进颜色 4 的两个词属于互斥后验。故表中已列出所有同时情形，且每格都满足所述性质。本构造无需假设每个因子有两个可选颜色。$\square$

**定理 123.8（相位二十一的精确六问）。** 在约定 123.1 的合同下，$Q_3(5040;w_{21})=6$。

证明。前三问用命题 123.6，后二进、三进任务按命题 123.7 的对应矩阵格选择。模 5 及补词使用以下七个实际词：

| 123.8 补词参数 $t$ | 词 | $(A,B)$ | $L$ | 模 5 中心 | 模 7 颜色 |
| --- | --- | --- | ---: | ---: | ---: |
| $0$ | $V_{12}$ | $(4,8)$ | 136 | 1 | 6 |
| $1$ | $V_{17}$ | $(6,11)$ | 191 | 1 | 0 |
| $2$ | $V_{22}$ | $(8,14)$ | 246 | 1 | 1 |
| $3$ | $V_{27}$ | $(10,17)$ | 301 | 1 | 2 |
| $4$ | $V_{32}$ | $(12,20)$ | 356 | 1 | 3 |
| $5$ | $V_{37}$ | $(14,23)$ | 411 | 1 | 4 |
| $6$ | $V_{42}$ | $(16,26)$ | 466 | 1 | 5 |

这些词已全部包含在十八词字典中。对 $0\le t\le6$，其系数对是 $(4+2t,8+3t)$，故 $L=136+55t\equiv1\pmod5$；同一个词的模 7 中心是 $A+2B=20+8t\equiv6+t\pmod7$。因此每个颜色恰有一个分隔 $\{1,2\}$ 的实际词；没有对非单位 55 求逆，也没有使用独立的模 5 和模 7 探针。

在每个完整前三问历史上，先保留矩阵格中的词。模 5 若仍为 $\{1,2\}$，加入上表中颜色属于 $U$ 且尚未使用的最小颜色的词；随后同样按最小未用颜色补足到三个词，按 $n$ 递增查询。甲支共享 $V_{16}$ 时只算一次；若二进和三进 $\{4,7\}$ 同时未决，格内只有颜色 5，模 5 未决时可加入颜色 3 的 $V_{32}$，再以颜色 4 的 $V_{37}$ 补齐。甲支其它双任务格用颜色 5、3，还可用颜色 4 的模 5 词。乙支每个双任务格的两色已由互不相交的颜色集保证不同，四个未测颜色中至少还有两色。所有单点、仅一项未决及合并后仅一词的格均按同一规则补足；模 5 已命中时省掉专用分配而照常补词。

这完整满足引理 123.4：每个二进、三进后验对被对应实际词区分，模 5 的未决对被中心 1 区分。前三问有三种颜色，后三问恰选三个新颜色；模 7 已命中时保留该值，六次全失配时推断唯一第七色。CRT 得 $x$，输出 $r=-1961x\pmod{5040}$。即使前三问已有模 7 命中，仍执行相同补词，不增加成本或改变来源。六问中的空词 $V_0$ 也已收费。全部六次都从同一来源重置，至多三窗且 End 合法，上界对每个允许的实际源成立。命题 123.3 对完整词域给六问下界，故相等。$\square$

**推论 123.9（相位六十一的同字面转移）。** 实际行 $w_{61}=(2008,1013)$ 满足 $Q_3(5040;w_{61})=6$。使用与定理 123.8 完全相同的字面词、分支与补词，归一化及原始解码为

$$
x=-3401r,\qquad r=-3401x\pmod{5040}.
$$

证明。命题 123.2 给 $w_{61}=\lambda w_{21}$，约化两项为 $(2008,1013)$。令 $h_{61}=1961\lambda=3401$；其四轴为 $(9,8,1,-1)$，故平方为一。每个同一字面词满足 $C_{61}=\lambda C_{21}$，于是

$$
h_{61}C_{61}=1961\lambda^2C_{21}=1961C_{21}.
$$

对 $x=-h_{61}r$，原回答就是 $\gcd(x-h_{61}C_{61},5040)$。因此不仅局部分区，连十八词的完整联合中心、第一问分支、共享词及未测颜色补词都逐项不变。以相同六问取得 $x$ 后，必须用显示的负号和逆单位恢复原始 $r$。没有加前导窗、物理缩放或额外查询。命题 123.3 在实际相位 61 本身给共同深度来源和匹配下界。$\square$

**推论 123.10（五十六个相位与原前三问障碍的保留）。** 推论 118.7 的 $\mathcal J_{54}$ 加入 $21,61$ 得到 56 个不同实际六问相位。命题 118.8 对原固定前三问的失败结论仍成立。

证明。$21,61$ 都为 $1\pmod5$，不在原 48 个同余族中，也不在原六个额外相位 $\{1,36,39,41,76,79\}$ 中，所以新增恰为两个。原命题 118.8 的前三问是 $V_0,V_1$，再按首问二进深度选择 $V_{23}$ 或 $V_4$；在相位 21 上它们只使用模 7 平移颜色 0、2。固定模 720 余数可取五个全失配实际源，任意再三问仍留下至少两个，因此该特定开头不能六问完成。这里的新开头 $V_0,V_{18}$ 再用 $V_{36}$ 或 $V_{21}$ 具有三个不同颜色，没有使用或否定旧失败前提。一个前三问方案的障碍并不是全策略 $Q_3\ge7$。$\square$

## 124. 实际相位七与四十七的联合分隔和异色收尾

**命题 124.1（相位七的归一化与十一词字典）。** 保持约定 123.1 的已知相位、正实际来源、两种初始化合并候选族、同源重置、完整 gcd 和三窗合同。实际行及归一化单位、逆单位是

$$
w_7=(1008,4465),\qquad h_7=3457,\qquad g_7=433,\qquad h_7g_7=1\pmod{5040}.
$$

令 $x=-3457r$。一个实际词的系数对 $(A,B)$ 给归一化中心

$$
d=3457C=2016A+3025B,
\qquad
(d\bmod16,d\bmod9,d\bmod5,d\bmod7)
=(B\bmod16,B\bmod9,A\bmod5,B\bmod7).
$$

下表 $W_k$ 指该行指定的 $B=k$ 的实际词；$k$ 不是规范编号 $n$，也不是完整模 5040 中心。它与 §123 的 $V_n$ 通过表中 $n$ 对应。各节出现同一 $W_k$ 时只按明确给出的同一占用集识别，中心随相位改变。

| 124.1 词 | $n$ | $s$ | $(A,B)$ | $I$ | 字面窗口 | 中心 $(16,9,5,7)$ |
| --- | ---: | ---: | --- | --- | --- | --- |
| $W_1$ | 1 | 2 | $(0,1)$ | $\{1\}$ | `[010]` | $(1,1,0,1)$ |
| $W_2$ | 3 | 5 | $(1,2)$ | $\{3\}$ | `[000,100]` | $(2,2,1,2)$ |
| $W_3$ | 5 | 8 | $(2,3)$ | $\{4\}$ | `[000,010]` | $(3,3,2,3)$ |
| $W_4$ | 7 | 11 | $(3,4)$ | $\{2,4\}$ | `[001,010]` | $(4,4,3,4)$ |
| $W_5$ | 8 | 13 | $(3,5)$ | $\{5\}$ | `[000,001]` | $(5,5,3,5)$ |
| $W_6$ | 9 | 15 | $(3,6)$ | $\{1,5\}$ | `[010,001]` | $(6,6,3,6)$ |
| $W_7$ | 11 | 18 | $(4,7)$ | $\{3,5\}$ | `[000,101]` | $(7,7,4,0)$ |
| $W_{12}$ | 19 | 31 | $(7,12)$ | $\{1,4,6\}$ | `[010,010,100]` | $(12,3,2,5)$ |
| $W_{13}$ | 21 | 34 | $(8,13)$ | $\{7\}$ | `[000,000,010]` | $(13,4,3,6)$ |
| $W_{14}$ | 22 | 36 | $(8,14)$ | $\{1,7\}$ | `[010,000,010]` | $(14,5,3,0)$ |
| $W_{24}$ | 38 | 62 | $(14,24)$ | $\{1,3,8\}$ | `[010,100,001]` | $(8,6,4,3)$ |

证明。$w_7=(F_{24},F_{25})$。命题 123.2 的局部周期给其四轴为 $(0,1),(0,1),(3,0),(0,6)$，CRT 代表为 $(1008,4465)$。$3457$ 的四轴为 $(1,1,2,6)$，$433$ 的四轴为 $(1,1,3,6)$，逐轴乘积为一。乘单位后行是 $(2016,3025)$；2016 模 1008 为零、模 5 为一，3025 模 1008 为一、模 5 为零，故得到显示的同词联合中心。$x-d=-3457(r+C)$ 保持原始完整 gcd，最终逆解码是 $r=-433x$。

字典中单点词 $W_1,W_2,W_3,W_5,W_{13}$ 直接取位置 $1,3,4,5,7$。其余对由同一位置向量相加：$W_4$ 是 $(1,1)+(2,3)=(3,4)$，$W_6$ 是 $(0,1)+(3,5)=(3,6)$，$W_7$ 是 $(1,2)+(3,5)=(4,7)$，$W_{12}$ 是 $(0,1)+(2,3)+(5,8)=(7,12)$，$W_{14}$ 是 $(0,1)+(8,13)=(8,14)$，$W_{24}$ 是

$$
(0,1)+(1,2)+(13,21)=(14,24).
$$

逐行 $n=A+B,s=A+2B$ 得到规范列；尤其 $W_{24}$ 的 $n=1+3+34=38$、$s=2+5+55=62$。每个集合都排除相邻占位且不含 0，按三位分组得到表中完整字面词。前导或中间零窗保留，非空末窗非零。故全部词均合法、正值 End 且至多三窗；每个四元组来自这一行的单个实际词。$\square$

**命题 124.2（相位七前三问的全部局部分区）。** 查询 $W_1,W_2$，用第一问的 $e=D_2(x-1)$ 分支：$e=1$ 时第三问用 $W_3$，称甲支；否则用 $W_{12}$，称乙支。规范编号就是 $1,3$，再用 $5$ 或 $19$。两支的联合中心依次为

$$
\begin{aligned}
\mathrm{甲}:&(1,1,0,1),\ (2,2,1,2),\ (3,3,2,3),\\
\mathrm{乙}:&(1,1,0,1),\ (2,2,1,2),\ (12,3,2,5).
\end{aligned}
$$

完整二进后验如下。

| 124.2 二进分支 | 模 16 后验 | 三问深度 |
| --- | --- | --- |
| 甲一 | $\{3\}$ | $(1,0,4)$ |
| 甲二 | $\{11\}$ | $(1,0,3)$ |
| 甲三 | $\{7,15\}$ | $(1,0,2)$ |
| 乙一 | $\{1\}$ | $(4,0,0)$ |
| 乙二 | $\{9\}$ | $(3,0,0)$ |
| 乙三 | $\{5,13\}$ | $(2,0,0)$ |
| 乙四 | $\{2\}$ | $(0,4,1)$ |
| 乙五 | $\{10\}$ | $(0,3,1)$ |
| 乙六 | $\{6,14\}$ | $(0,2,1)$ |
| 乙七 | $\{4\}$ | $(0,1,3)$ |
| 乙八 | $\{12\}$ | $(0,1,4)$ |
| 乙九 | $\{0,8\}$ | $(0,1,2)$ |

两支三进中心都为 $1,2,3$，所以共同的完整三进分区为：

| 124.2 三进后验 | 三问深度 |
| --- | --- |
| $\{1\}$ | $(2,0,0)$ |
| $\{4,7\}$ | $(1,0,0)$ |
| $\{2\}$ | $(0,2,0)$ |
| $\{5,8\}$ | $(0,1,0)$ |
| $\{3\}$ | $(0,0,2)$ |
| $\{0,6\}$ | $(0,0,1)$ |

两支模 5 均测试 $0,1,2$；三个单命中位置分别识别 $0,1,2$，全失配恰留 $\{3,4\}$。甲支模 7 测试 $1,2,3$，乙支测试 $1,2,5$；命中即识别对应值，全失配时分别留四个未测颜色

$$
U_{\mathrm{甲}}=\{0,4,5,6\},\qquad U_{\mathrm{乙}}=\{0,3,4,6\}.
$$

即使已命中，$U$ 仍保留“未测颜色”的含义。

证明。甲支第一深度一给 $\{3,7,11,15\}$，第二中心 2 给深度零，第三中心 3 的深度依次为 $4,2,3,2$。乙支第一深度 $4,3,2$ 给 $1,9,\{5,13\}$，后二中心均偶，表中的零深度成立。第一深度零时 $x$ 为偶数；第二中心 2 的深度 $4,3,2,1$ 分别给 $2,10,\{6,14\},\{0,4,8,12\}$。第三中心 12 对最后四个值的深度是 $2,3,2,4$，对 $\{6,14\}$ 都为 1。因而二进分区穷尽全部十六个余数。三进三个中心覆盖三个模 3 类，恰一深度为正；深度 2 是中心本身，深度 1 是同类另两员，得到表中全部六种后验。模 5 和模 7 的测试颜色各自互异，故三个单命中或全失配穷尽其历史，不存在两次命中。命题 123.3 的共同纤维和完整历史归纳保证这些局部后验的相容元组都有一个固定实际源；没有遗漏联合历史。$\square$

**命题 124.3（相位七的所有分配矩阵与单词三轴分隔）。** 对命题 124.2 的未决二进、三进对，采用以下分配。

| 124.3 分配 | 因子与有序对 | 实际词 | 有序深度 | 颜色 |
| --- | --- | --- | --- | ---: |
| 甲二进 | $16:(7,15)$ | $W_7$ | $(4,3)$ | 0 |
| 甲三进一 | $9:(4,7)$ | $W_4$ | $(2,1)$ | 4 |
| 甲三进二 | $9:(5,8)$ | $W_5$ | $(2,1)$ | 5 |
| 甲三进三 | $9:(0,6)$ | $W_6$ | $(1,2)$ | 6 |
| 乙二进一 | $16:(5,13)$ | $W_{13}$ | $(3,4)$ | 6 |
| 乙二进二 | $16:(6,14)$ | $W_6$ | $(4,3)$ | 6 |
| 乙二进三 | $16:(0,8)$ | $W_{24}$ | $(3,4)$ | 3 |
| 乙三进一 | $9:(4,7)$ | $W_4$ | $(2,1)$ | 4 |
| 乙三进二 | $9:(5,8)$ | $W_{14}$ | $(2,1)$ | 0 |
| 乙三进三 | $9:(0,6)$ | $W_{24}$ | $(1,2)$ | 3 |

以下矩阵列出所有同时分配，单点合写为“已知”，同一词已合并。

| 124.3 甲二进后验 | 三进已知 | $\{4,7\}$ | $\{5,8\}$ | $\{0,6\}$ |
| --- | --- | --- | --- | --- |
| 甲已知 | $\varnothing$ | $\{W_4\}$ | $\{W_5\}$ | $\{W_6\}$ |
| 甲 $\{7,15\}$ | $\{W_7\}$ | $\{W_7,W_4\}$ | $\{W_7,W_5\}$ | $\{W_7,W_6\}$ |

| 124.3 乙二进后验 | 三进已知 | $\{4,7\}$ | $\{5,8\}$ | $\{0,6\}$ |
| --- | --- | --- | --- | --- |
| 乙已知 | $\varnothing$ | $\{W_4\}$ | $\{W_{14}\}$ | $\{W_{24}\}$ |
| 乙 $\{5,13\}$ | $\{W_{13}\}$ | $\{W_{13},W_4\}$ | $\{W_{13},W_{14}\}$ | $\{W_{13},W_{24}\}$ |
| 乙 $\{6,14\}$ | $\{W_6\}$ | $\{W_6,W_4\}$ | $\{W_6,W_{14}\}$ | $\{W_6,W_{24}\}$ |
| 乙 $\{0,8\}$ | $\{W_{24}\}$ | $\{W_{24},W_4\}$ | $\{W_{24},W_{14}\}$ | $\{W_{24}\}$ |

每格至多两词，具有不同的未测颜色。尤其乙支最后一格的两项任务由同一个 $W_{24}$ 完成。

证明。命题 124.1 给每个词一个联合中心。各二进中心依次属于指定对的模 8 类，各三进中心等于指定对的一员模 9，由引理 123.4 给所列深度。甲支二进颜色 0 与三进颜色 $4,5,6$ 不交。乙支二进颜色为 6 或 3，三进颜色为 4、0 或 3；唯一可能同时碰撞的是 3，而双方都指定完全相同的 $W_{24}$。$W_{13}$、$W_6$ 同为颜色 6，但属于互斥的两个二进后验，不同时分配。所有颜色都在对应四元 $U$ 中，因而矩阵穷尽每种二进、三进组合且满足异色条件。

关键词的完整实际见证不能省略：$W_{24}$ 的规范编号是 38，$I=\{1,3,8\}$，字面词是 `[010,100,001]`，单个物理平移为

$$
C=14u+24v,\qquad d=2016\cdot14+3025\cdot24,
\qquad d\equiv(8,6,4,3)\pmod{(16,9,5,7)}.
$$

于是有序二进对 $(0,8)$ 给深度 $(3,4)$，三进对 $(0,6)$ 给 $(1,2)$，模 5 对 $(3,4)$ 给命中位 $(0,1)$。这些是同一来源接受这一条词时的同一份 gcd 的三个分量；它在乙支使用尚未问过的颜色 3。所以合并只需一次查询，且可同时完成三个未决对，没有把几个局部可用探针拼成虚构中心。$\square$

**定理 124.4（相位七的精确六问与补词全定义性）。** 在约定 123.1 的合同下，$Q_3(5040;w_7)=6$。

证明。先作命题 124.2 的三问，再按命题 124.3 的矩阵保留二进、三进分配词。模 5 与补词使用下面的实际字典子表：

| 124.4 未测颜色 | 分隔兼补词 | 模 5 中心 | 规范编号 $n$ |
| --- | --- | ---: | ---: |
| $0$ | $W_7$ | 4 | 11 |
| $3$ | $W_{24}$ | 4 | 38 |
| $4$ | $W_4$ | 3 | 7 |
| $5$ | $W_5$ | 3 | 8 |
| $6$ | $W_6$ | 3 | 9 |

它覆盖 $U_{\mathrm{甲}}\cup U_{\mathrm{乙}}=\{0,3,4,5,6\}$ 的每色。$W_4,W_5,W_6$ 的系数首项均为 3，$W_7,W_{24}$ 的首项分别为 4、14；故每词模 5 中心为 3 或 4，能分隔唯一可能的对 $\{3,4\}$。这些同时是该色的实际词，不需要全部七色的模 5 词族。

固定完整前三问历史后，先取对应矩阵格，并合并相同词。设已选数为 $m$，矩阵给 $0\le m\le2$，颜色互异且都在相应 $U$。若模 5 尚未决，加入上表中颜色为 $U$ 内最小未用颜色的词，此时至少还有两色可用，加入后至多三词。即使格内某词将附带分隔模 5，也允许这一步保守地再取异色分隔词。模 5 已命中时跳过此步。随后仍按最小未用颜色补至恰三词，按规范编号 $n$ 递增执行。

补词按颜色排除而非只按词名排除：乙支若已用 $W_{14}$ 的颜色 0，就不能再用 $W_7$ 补该色；已用 $W_{13}$ 的颜色 6，就不能再用 $W_6$ 补该色。四个未测颜色中至多要选三个，故其余颜色始终足够。甲支双任务占 0 和 $4,5,6$ 中一色；乙支非合并格占两种不同色，合并格只占颜色 3；单点及仅一项任务也由同一规则补齐。这逐一涵盖两个矩阵的所有格，且不依赖模 7 是否已有命中。

由引理 123.4 的分隔判据和以上具体字面实现，六问后模 $16,9,5$ 都确定。甲支前三色 $1,2,3$、乙支前三色 $1,2,5$，各与所选三个新色不交，所以每条历史都恰测试六个不同模 7 色。任一命中确定 $x\bmod7$，六次未命中时确定唯一未测色。CRT 还原 $x\bmod5040$，输出原始 $r=-433x$。所有问都用命题 124.1 的合法词，各自重置到同一来源；这个上界既不要求改变来源，也不使用假设 107.5。命题 123.3 在相位 7 的共同深度满纤维上给全词、全确定性策略的匹配下界，故成本恰六。$\square$

**推论 124.5（相位四十七的同词策略与原始解码）。** 实际行 $w_{47}=(1008,3025)$ 满足 $Q_3(5040;w_{47})=6$。保持以上每个实际字面词和所有选择，改用

$$
x=-2017r,\qquad r=-4033x\pmod{5040}.
$$

证明。命题 123.2 给 $w_{47}=\lambda w_7$，其四轴为 $(0,1),(0,1),(3,0),(0,1)$，所以 CRT 代表为 $(1008,3025)$。取 $h_{47}=3457\lambda=2017$，逆单位是 $g_{47}=433\lambda=4033$，四轴分别为 $(1,1,2,1)$、$(1,1,3,1)$。每个相同字面词的系数 $(A,B)$ 保持，故 $C_{47}=\lambda C_7$ 及

$$
h_{47}C_{47}=3457C_7.
$$

对 $x=-2017r$，完整回答与相位七的归一化回答逐问相同。因此十一词字典、全部后验、两个分配矩阵、$W_{24}$ 的单词合并和颜色补词完全转移，成本仍为六问；最后乘逆单位并保留负号给原始 $r$。这里没有前置一窗、源的物理缩放或另收一问。命题 123.3 的同深度来源与全词下界在相位 47 本身成立。$\square$

**推论 124.6（五十八相位及受限等差列的准确边界）。** 在推论 123.10 的 56 个相位之外，新增 $7,47$，总计 58 个实际相位。相位七上的旧等差列子族不足与本节六问结论相容。

证明。$7,47$ 都为 $3\pmod4$，不在原 48 个同余族中，也不在此前八个额外相位中，故新增恰为二。这里不把两个编号误当成同一实际行，因为命题 123.2 给精确周期 80。

命题 114.11 的等差列为 $C=b+td$，其中 $b=u+3v,d=2u+3v$。在相位七模 3 上 $u=0,v=1$，所以 $b=d=0$；所有该列中心都为零模 3。固定其它源坐标，取两种不同且非零的模 3 源余数，所有该子族查询的三进深度都为零，其余回答也相同。共同深度满支撑提供两个实际源，因此任意重复该子族都不能区分它们。本节却使用归一化模 3 中心为 1、2 的 $W_1,W_2$，所以没有受限于这条等差列。该子族失败和命题 118.8 的固定前三问失败均保留各自范围，不能提升为完整词域的七问下界。$\square$

## 125. 实际相位三与四十三的共同合法尾部和六十相位结论

**命题 125.1（相位三的精确归一化与模 144 同词复用边界）。** 在约定 123.1 的合同下，实际行 $w_3=(144,233)$ 可取归一化单位 $h_3=1817$，其逆单位为 233。对同一个实际词的系数对 $(A,B)$，令 $x=-1817r$，则

$$
d=1817C=4608A+B\pmod{5040},
$$

$$
(d\bmod16,d\bmod9,d\bmod5,d\bmod7)
=(B\bmod16,B\bmod9,(B+3A)\bmod5,(B+2A)\bmod7).
$$

相位七的前三问二进、三进分区可按同一字面词、同一规范编号、同一归一化模 144 源坐标复用；该复用不包括模 5、模 7 中心或整个收尾策略。

证明。$w_3=(F_{12},F_{13})=(144,233)$，且

$$
1817\cdot233=1+84\cdot5040,\qquad
1817\cdot144=51\cdot5040+4608.
$$

4608 四轴为 $(0,0,3,2)$，故逐词联合中心如式。$x-d=-1817(r+C)$ 保持完整 gcd；恢复原始余数的公式为 $r=-233x$，不是去掉负号的缩放。

命题 124.1 在相位七给每个占用集 $I$ 的中心 $d_7(I)\equiv B\pmod{144}$，因为 $1008\equiv0$、$4465\equiv1$、$3457\equiv1\pmod{144}$。本节 $4608=32\cdot144$，所以对完全相同的 $I$ 和字面窗口也有 $d_3(I)\equiv B\pmod{144}$。对应映射保持 $I$、$n$、两个截断深度以及第一问二进深度的分支条件，因此可逐条复用命题 124.2 在这两个因子上的证明。

但相位七的模 5、模 7 中心是 $A,B$，这里是 $B+3A,B+2A$，前三问就已有差别。因此这个投影没有给物理来源的全局等价，也没有给相位七联合分配的转移；本节以下另给同一词实现的新中心和全部收尾。$\square$

**命题 125.2（共同尾部构造与十三个实际词）。** 相位三的六问策略使用下列十三词，$W_k$ 仍只标识表中 $B=k$ 的指定词。与 §124 共名的词具有相同的占用集和字面窗口，但这里使用相位三的联合中心。

| 125.2 词 | $n$ | $s$ | $(A,B)$ | $I$ | 字面窗口 | 中心 $(16,9,5,7)$ |
| --- | ---: | ---: | --- | --- | --- | --- |
| $W_1$ | 1 | 2 | $(0,1)$ | $\{1\}$ | `[010]` | $(1,1,1,1)$ |
| $W_2$ | 3 | 5 | $(1,2)$ | $\{3\}$ | `[000,100]` | $(2,2,0,4)$ |
| $W_3$ | 5 | 8 | $(2,3)$ | $\{4\}$ | `[000,010]` | $(3,3,4,0)$ |
| $W_{12}$ | 19 | 31 | $(7,12)$ | $\{1,4,6\}$ | `[010,010,100]` | $(12,3,3,5)$ |
| $W_4$ | 7 | 11 | $(3,4)$ | $\{2,4\}$ | `[001,010]` | $(4,4,3,3)$ |
| $W_{14}$ | 22 | 36 | $(8,14)$ | $\{1,7\}$ | `[010,000,010]` | $(14,5,3,2)$ |
| $W_{15}$ | 24 | 39 | $(9,15)$ | $\{3,7\}$ | `[000,100,010]` | $(15,6,2,5)$ |
| $W_{21}$ | 33 | 54 | $(12,21)$ | $\{1,3,5,7\}$ | `[010,101,010]` | $(5,3,2,3)$ |
| $W_{30}$ | 48 | 78 | $(18,30)$ | $\{1,6,8\}$ | `[010,000,101]` | $(14,3,4,3)$ |
| $W_{31}$ | 50 | 81 | $(19,31)$ | $\{3,6,8\}$ | `[000,100,101]` | $(15,4,3,6)$ |
| $W_{32}$ | 52 | 84 | $(20,32)$ | $\{4,6,8\}$ | `[000,010,101]` | $(0,5,2,2)$ |
| $W_9$ | 15 | 24 | $(6,9)$ | $\{2,6\}$ | `[001,000,100]` | $(9,0,2,0)$ |
| $W_{19}$ | 30 | 49 | $(11,19)$ | $\{1,5,7\}$ | `[010,001,010]` | $(3,1,2,6)$ |

证明。记位置系数向量为 $p_i=(F_{i-1},F_i)$。若两个占用集各自无相邻元素，且任一跨集距离至少为二，则并集仍合法，系数向量为两者之和。这个操作同时平移四个中心，不能只取其中一个因子而另选其它因子。

关键共同尾部取 $K=\{6,8\}$，其对是

$$
p_6+p_8=(5,8)+(13,21)=(18,29).
$$

$\{1\},\{3\},\{4\}$ 与 $K$ 的全部跨距都至少为二；分别并入得到

$$
W_{30}:(18,30),\qquad W_{31}:(19,31),\qquad W_{32}:(20,32).
$$

相邻两对的差是 $(1,1)$，故模 16、9 中心各加一，模 5 中心加四，模 7 颜色加三。由命题 125.1，联合中心分别为 $(14,3,4,3),(15,4,3,6),(0,5,2,2)$。其中 $W_{32}$ 同时落在二进 $\{0,8\}$ 的模 8 分隔类、三进 $\{5,8\}$ 的一员及模 5 对 $\{2,4\}$ 的一员。

其它词也从合法位置和得到。前三个单点词取 $p_1,p_3,p_4$；$W_{12}=p_1+p_4+p_6=(7,12)$；$W_4=p_2+p_4=(3,4)$。分别向 $\{1\}$、$\{3\}$ 添加分离的 $\{7\}$ 得 $W_{14}=(8,14)$、$W_{15}=(9,15)$。奇位置链 $\{1,3,5,7\}$ 给 $W_{21}=(12,21)$，它与 $W_{30}$ 的向量差为 $(6,9)$，模 7 颜色差 $2\cdot6+9=21\equiv0$；二者因此同色 3，但模 8 中心分别为 5、6，供互斥的二进分支使用。$\{2,6\}$ 给 $W_9=(6,9)$，提供模 9 中心 0 和颜色 0。$\{1,5,7\}$ 给 $W_{19}=(11,19)$；它由 $\{1,5\}$ 添加 $\{7\}$ 而来，新增 $(8,13)$ 同时使模 5 中心增加 $13+3\cdot8\equiv2$、模 7 颜色增加 $13+2\cdot8\equiv1$，从而得到模 5 中心 2、颜色 6。

对全部行用 $n=A+B,s=A+2B$ 得到规范列。例如三种共同尾部词有 $n=48,50,52$，$s=78,81,84$；$W_{21}$ 有 $n=1+3+8+21=33$、$s=2+5+13+34=54$。按表中顺序，未约化的 $(B+3A,B+2A)$ 是

$$
\begin{aligned}
&(1,1),(5,4),(9,7),(33,26),(13,10),(38,30),(42,33),\\
&(57,45),(84,66),(88,69),(92,72),(27,21),(52,41),
\end{aligned}
$$

分别约化模 5、7，并将同一 $B$ 约化模 16、9，正得所有四元组。每个占用集均在 $\{1,\ldots,8\}$ 内且不相邻；逐窗位序恰是表中词。特别地，$W_4$ 的位置 2 后接零位置 3，$W_9$ 的位置 2 后保留整窗 $000$；$W_{21},W_{19}$ 的位置 5 后第三窗首位为零；$W_{12},W_{30},W_{31},W_{32}$ 的第三窗首位为一时位置 5 均为零。故两处跨窗接缝均合法。所有非空末窗非零，特别是 $W_{32}$ 恰为 `[000,010,101]`，没有删去或替换其中任何完整窗口。$\square$

**命题 125.3（相位三前三问的所有后验）。** 先问 $W_1,W_2$，用第一问的 $e=D_2(x-1)$ 决定第三词：$e=1$ 用 $W_3$，称甲支；否则用 $W_{12}$，称乙支。联合中心现在为

$$
\begin{aligned}
\mathrm{甲}:&(1,1,1,1),\ (2,2,0,4),\ (3,3,4,0),\\
\mathrm{乙}:&(1,1,1,1),\ (2,2,0,4),\ (12,3,3,5).
\end{aligned}
$$

二进和三进的完整分区如下。

| 125.3 二进分支 | 模 16 后验 | 三问深度 |
| --- | --- | --- |
| 甲一 | $\{3\}$ | $(1,0,4)$ |
| 甲二 | $\{11\}$ | $(1,0,3)$ |
| 甲三 | $\{7,15\}$ | $(1,0,2)$ |
| 乙一 | $\{1\}$ | $(4,0,0)$ |
| 乙二 | $\{9\}$ | $(3,0,0)$ |
| 乙三 | $\{5,13\}$ | $(2,0,0)$ |
| 乙四 | $\{2\}$ | $(0,4,1)$ |
| 乙五 | $\{10\}$ | $(0,3,1)$ |
| 乙六 | $\{6,14\}$ | $(0,2,1)$ |
| 乙七 | $\{4\}$ | $(0,1,3)$ |
| 乙八 | $\{12\}$ | $(0,1,4)$ |
| 乙九 | $\{0,8\}$ | $(0,1,2)$ |

| 125.3 三进后验（两支相同） | 三问深度 |
| --- | --- |
| $\{1\}$ | $(2,0,0)$ |
| $\{4,7\}$ | $(1,0,0)$ |
| $\{2\}$ | $(0,2,0)$ |
| $\{5,8\}$ | $(0,1,0)$ |
| $\{3\}$ | $(0,0,2)$ |
| $\{0,6\}$ | $(0,0,1)$ |

甲支模 5 依次测试 $1,0,4$，单命中三元组 $(1,0,0),(0,1,0),(0,0,1)$ 分别识别 $1,0,4$，全失配恰留 $\{2,3\}$。乙支依次测试 $1,0,3$，同样三个单命中分别识别 $1,0,3$，全失配恰留 $\{2,4\}$。两支的模 5 后验不同，不能沿用相位七的 $\{3,4\}$。

甲支模 7 依次测试 $1,4,0$，乙支测试 $1,4,5$；命中则识别相应值，全失配时剩下

$$
U_{\mathrm{甲}}=\{2,3,5,6\},\qquad U_{\mathrm{乙}}=\{0,2,3,6\}.
$$

命中后 $U$ 仍指四个未测颜色，并非剩余候选。

证明。二进、三进采用命题 125.1 的同词映射，命题 124.2 的每个假设均保持：三个二进中心是 $1,2,3$ 或 $1,2,12$，三进中心均是 $1,2,3$，分支使用相同的第一深度。因此其逐深度证明原样给上面全部分区。具体地，甲支的 $3,7,11,15$ 对末中心 3 的深度是 $4,2,3,2$；乙支偶数分支末四个 $0,4,8,12$ 对中心 12 的深度是 $2,3,2,4$，其余第一或第二深度分支正如所列。三进恰一问深度为正，深度 2 给中心，深度 1 给同模 3 类的另两员。

新模 5、模 7 中心来自命题 125.2 的实际四元组，逐支三个值都不同，所以只有一个命中或全部未命中；其补集正是所列二元对与四色集。这穷尽两轴历史。命题 123.3 的完整历史论证适用相同来源合同：分支已由记录的第一二进深度确定，任一相容局部元组由共同深度的固定实际源实现。上界对这些元组全部成立，也就涵盖所有任意返回深度的实际来源。$\square$

**命题 125.4（相位三的全部联合矩阵与两个相同词合并）。** 对命题 125.3 的未决对，采用如下分配。

| 125.4 分配 | 因子与有序对 | 实际词 | 有序深度 | 颜色 |
| --- | --- | --- | --- | ---: |
| 甲二进 | $16:(7,15)$ | $W_{15}$ | $(3,4)$ | 5 |
| 甲三进一 | $9:(4,7)$ | $W_4$ | $(2,1)$ | 3 |
| 甲三进二 | $9:(5,8)$ | $W_{14}$ | $(2,1)$ | 2 |
| 甲三进三 | $9:(0,6)$ | $W_{15}$ | $(1,2)$ | 5 |
| 乙二进一 | $16:(5,13)$ | $W_{21}$ | $(4,3)$ | 3 |
| 乙二进二 | $16:(6,14)$ | $W_{30}$ | $(3,4)$ | 3 |
| 乙二进三 | $16:(0,8)$ | $W_{32}$ | $(4,3)$ | 2 |
| 乙三进一 | $9:(4,7)$ | $W_{31}$ | $(2,1)$ | 6 |
| 乙三进二 | $9:(5,8)$ | $W_{32}$ | $(2,1)$ | 2 |
| 乙三进三 | $9:(0,6)$ | $W_9$ | $(2,1)$ | 0 |

合并相同词后，所有同时分配如下。

| 125.4 甲二进后验 | 三进已知 | $\{4,7\}$ | $\{5,8\}$ | $\{0,6\}$ |
| --- | --- | --- | --- | --- |
| 甲已知 | $\varnothing$ | $\{W_4\}$ | $\{W_{14}\}$ | $\{W_{15}\}$ |
| 甲 $\{7,15\}$ | $\{W_{15}\}$ | $\{W_{15},W_4\}$ | $\{W_{15},W_{14}\}$ | $\{W_{15}\}$ |

| 125.4 乙二进后验 | 三进已知 | $\{4,7\}$ | $\{5,8\}$ | $\{0,6\}$ |
| --- | --- | --- | --- | --- |
| 乙已知 | $\varnothing$ | $\{W_{31}\}$ | $\{W_{32}\}$ | $\{W_9\}$ |
| 乙 $\{5,13\}$ | $\{W_{21}\}$ | $\{W_{21},W_{31}\}$ | $\{W_{21},W_{32}\}$ | $\{W_{21},W_9\}$ |
| 乙 $\{6,14\}$ | $\{W_{30}\}$ | $\{W_{30},W_{31}\}$ | $\{W_{30},W_{32}\}$ | $\{W_{30},W_9\}$ |
| 乙 $\{0,8\}$ | $\{W_{32}\}$ | $\{W_{32},W_{31}\}$ | $\{W_{32}\}$ | $\{W_{32},W_9\}$ |

每格至多两个不同实际词，颜色不同且属于本支 $U$。甲支唯一同时颜色碰撞合并为 $W_{15}$，乙支唯一同时颜色碰撞合并为 $W_{32}$。

证明。将命题 125.2 的实际中心代入引理 123.4：二进中心分别在所需模 8 类，三进中心分别等于所需对的一员模 9，故得到显示的全部有序深度。甲支二进色为 5，三进色为 3、2 或 5；唯一同色时两任务都是 $W_{15}$。它的字面词 `[000,100,010]`、$I=\{3,7\}$ 给一个物理平移 $9u+15v$，在相位三为 4791，归一化四元组是 $(15,6,2,5)$。所以它同时给二进 $(7,15)$ 深度 $(3,4)$、三进 $(0,6)$ 深度 $(1,2)$，并给模 5 对 $(2,3)$ 命中位 $(1,0)$。这个共同词同时履行三项功能，只算一问和一个颜色。

乙支二进色为 3、3 或 2，三进色为 6、2 或 0。颜色 3 的 $W_{21}$ 和 $W_{30}$ 属于互斥的二进后验，绝不同时分配；它们是不同词，不能因同色而合并。唯一同时碰撞是颜色 2，双方确实都指定 $W_{32}$。该词的完整见证为

$$
I=\{4,6,8\},\quad n=52,\quad s=84,\quad(A,B)=(20,32),
\quad W_{32}=[000,010,101].
$$

其实际物理平移与归一化中心为

$$
C=20\cdot144+32\cdot233=10336\equiv256\pmod{5040},
\qquad d=1817\cdot256\equiv1472\pmod{5040},
$$

$$
d\equiv(0,5,2,2)\pmod{(16,9,5,7)}.
$$

于是对有序二进 $(0,8)$ 的深度为 $(4,3)$，对三进 $(5,8)$ 为 $(2,1)$，对模 5 的 $(2,4)$ 命中位为 $(1,0)$。这一份完整 gcd 同时分隔三对，颜色 2 在乙支未测。矩阵的其余格颜色已经不同。将所有单点历史合写只删掉无需分配的义务，不丢失任何二进、三进后验；两种模 5 及所有模 7 命中情形由下一条的同一规则处理。$\square$

**定理 125.5（相位三的三新色收尾与精确六问）。** 约定 123.1 下 $Q_3(5040;w_3)=6$；其后三问可以在前三问完整历史确定后一次选定。

证明。模 5 分隔及补词分别用以下实际词，每行来自命题 125.2。

| 125.5 分支和颜色 | 实际词 | 模 5 中心 | 规范编号 $n$ |
| --- | --- | ---: | ---: |
| 甲 $2$ | $W_{14}$ | 3 | 22 |
| 甲 $3$ | $W_4$ | 3 | 7 |
| 甲 $5$ | $W_{15}$ | 2 | 24 |
| 甲 $6$ | $W_{19}$ | 2 | 30 |
| 乙 $0$ | $W_9$ | 2 | 15 |
| 乙 $2$ | $W_{32}$ | 2 | 52 |
| 乙 $3$ | $W_{21}$ | 2 | 33 |
| 乙 $6$ | $W_{19}$ | 2 | 30 |

甲支的每个 $U_{\mathrm{甲}}=\{2,3,5,6\}$ 颜色都有模 5 中心 2 或 3 的词，分隔该支的 $\{2,3\}$；乙支的每个 $U_{\mathrm{乙}}=\{0,2,3,6\}$ 颜色都有中心 2 的词，分隔 $\{2,4\}$。特别地，两支的颜色 6 均可用同一合法三位置词 $W_{19}$，没有假设不存在于字典的全七色词族。

确定选择规则如下。取命题 125.4 中实际后验对应的矩阵格，保留全部二进、三进分配词，单点不分配，相同词合并一次。设格内词数为 $m$，已证明 $m\le2$ 且颜色不同、均在 $U$。若前三问后模 5 仍是对，加入本支表中颜色为最小未用 $U$ 颜色的词；此时至少两个颜色可选，加入后至多三词。若模 5 已命中则跳过。随后用同一表按最小未用颜色补足到恰三词，按规范编号 $n$ 递增查询。这只读取前三问历史，不需要任何尚未取得的后三问回答。

为核对每种冲突和补齐情形：甲支双任务若同时指定 $W_{15}$，合并后只占颜色 5；其它双任务格占 $5,3$ 或 $5,2$，均余至少两色。乙支同时指定 $W_{32}$ 时只占颜色 2；其它双任务格占两种不同色。若乙支已经选择 $W_{30}$ 的颜色 3，补词表中的 $W_{21}$ 被该颜色排除；若已经选择 $W_{31}$ 的颜色 6，表中的 $W_{19}$ 被该颜色排除。它们虽不同词，但绝不以同色重复填充。其余尚未使用的颜色仍各有表中实际词，四个可用颜色足以选恰三个。零任务、一任务、合并后只余一词、模 5 已知或未决，全部按这个同一规则终止；允许在已有分配词会附带解决模 5 时再保守地取一个异色模 5 词，仍不超过三问。

所有原分隔词都保留，所以每个未决二进、三进对得到不同的完整深度；每个模 5 对都有同源实际分隔词。前三色在甲支为 $1,4,0$、乙支为 $1,4,5$，后三问严格从各自未测 $U$ 中选三个不同色，所以每条历史都有六种不同测试颜色。模 7 的早命中已确定该坐标，不妨仍完成补词；六问全失配则由唯一未测色确定该坐标。CRT 得全部 $x\bmod5040$，输出原始 $r=-233x$。

每次实际执行均重置到选定的原始正来源，所有词至多三窗且 End 合法，规范编号和字面词没有由坐标变换修改。故上界对所有允许深度上的来源成立。命题 123.3 在相位三给七个共同深度、同模 720 的实际源；完整 55 词、恒错、收费空词、自适应及提前停止都受其六问下界约束。于是最坏成本恰六；既不依赖假设 107.5，也不宣称每个单独来源都必须用六问。$\square$

**推论 125.6（相位四十三的同字面伴随与逆解码）。** 实际行 $w_{43}=(864,3113)$ 满足 $Q_3(5040;w_{43})=6$。其归一化和原始余数解码为

$$
x=-2537r,\qquad r=-3113x\pmod{5040}.
$$

证明。命题 123.2 给 $w_{43}=\lambda w_3=1441(144,233)\equiv(864,3113)$。取 $h_{43}=\lambda\cdot1817=2537$，逆单位为 $\lambda\cdot233=3113$；也有直接恒等式 $2537\cdot3113=1+1567\cdot5040$。对每个相同占用集及相同字面窗口，$C_{43}=\lambda C_3$，所以

$$
h_{43}C_{43}=1817C_3.
$$

因而 $x=-2537r$ 时 $x-d=-2537(r+C_{43})$，所有完整 gcd 回答都是本节相位三策略使用的归一化回答。十三词的四轴中心、两支前三问分区、所有矩阵格、$W_{15}$ 与 $W_{32}$ 的合并、模 5 分隔及补齐次序全都保持。仍用同一六个字面查询，从 CRT 取得 $x$ 后按显示逆单位和负号输出原始 $r$。没有另加一窗、来源缩放或查询。实际相位 43 自身满足命题 123.3 的同深度正来源合同，匹配下界也因此保持。$\square$

**推论 125.7（六十个实际六问相位与剩余边界）。** 在定义 113.1、114.1 及约定 123.1 的合同下，现在给出完整六问构造的实际相位集合为

$$
\begin{aligned}
\mathcal J_{60}={}&\{j:0\le j<80,\ j\not\equiv3\pmod4,\ j\not\equiv1\pmod5\}\\
&\cup\{1,3,7,21,36,39,41,43,47,61,76,79\}.
\end{aligned}
$$

它有 60 个元素，且对每个 $j\in\mathcal J_{60}$ 都有 $Q_3(5040;w_j)=6$。尚未由这些构造解决的相位恰为

$$
\{6,11,15,16,19,23,26,27,31,35\}+\{0,40\},
$$

这里加号表示该十元集与其平移 40 后的十元集之并，不是包含相位 0、40 的额外未决项。本结论不是全部 80 相位的六问分类，也未给出任何相位的全策略下界 $Q_3\ge7$。

证明。定理 114.12 的同余族在每个 20 指标区间有 $3\cdot4=12$ 个，共 48 个；原四个额外相位为 $36,39,76,79$。推论 118.7 增加 $1,41$ 得 54；推论 123.10 增加 $21,61$ 得 56；推论 124.6 增加 $7,47$ 得 58；定理 125.5、推论 125.6 增加 $3,43$ 得 60。最后两项为 $3\pmod4$，不在同余族或此前十个额外相位中。显示的十二个额外相位互异且都在同余族之外，命题 123.2 的精确实际周期保证不发生行编号重复。

在 $0,\ldots,39$ 中，同余族的补集为 $\{1,3,6,7,11,15,16,19,21,23,26,27,31,35,36,39\}$；删去已有的 $1,3,7,21,36,39$，余下正是显示的十元集。另一半是它平移 40 的集合，所以剩余恰 20 个。各六问上界都有自己的实际字面策略，共同下界由实际来源支撑给出；计数没有把独立的边缘中心或相同相位重复算入。

命题 118.8 的窄前三问失败及约定 114.14 等先前受限子族结论仍保持原前提，不被本节的不同构造改判，也不能推出更强的全策略负结论。对剩余二十相位，命题 123.3 给无条件的六问下界；推论 114.5 的上界十五仍保留假设 107.5 的语义覆盖与短词分离前提，不能从本次六个具体相位的策略把该前提统一去掉。相位三对相位七的模 144 同词投影也不自动转移其它相位的联合收尾。

这些命题只确定已知实际行、完整 gcd 回答、每问同源重置、三窗字面预算下原始模 5040 余数的确定性最坏查询数。没有据此恢复完整整数、原树或生成前缀，没有解决未知相位、随机化成本、取得标签的工作空间、最优总窗口工作量或别种访问模型；也不产生经验检验、文献原创性、RH 或全局 Robin 结论。$\square$

## 追加锚（本行以下为增补区）
## 126. 一般模数的准确连续时域与停滞秩提升

### 126.1. 同一来源及首次分离

**定义 126.1（一般模数的连续时域）。** 本节复用定义 120.1 的来源与定理 117.3 的实际支持，不另设来源机制。令 $\mathbb N$ 包含零，固定

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad q=(2,3),\qquad
C=\begin{pmatrix}2&3\\3&5\end{pmatrix},\qquad
C^{-1}=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}.
$$

一个来源 $v=(a,b)\in\mathbb N^2$ 给出 $(n,z)=Cv$、$y_0=n$、$y_1=z$ 与 $y_{k+2}=y_{k+1}+y_k$；因而 $y_k=F_{k-1}n+F_kz=qM^kv$（$k\ge1$）。固定 $n$ 时，准确支持及逆式为

$$
A_n=\left\lceil\frac{3n}{2}\right\rceil,\quad
B_n=\left\lfloor\frac{5n}{3}\right\rfloor,\quad
I_n=[A_n,B_n]\cap\mathbb Z,\quad
L_n=\max(0,B_n-A_n+1),\quad
v=(5n-3z,2z-3n).
$$

每个 $z\in I_n$ 都有且只有这个非负整数来源。对 $H\ge1$，$T_H$ 是使任意两个实际来源的前 $T_H$ 项 $\gcd(y_k,H)$ 相同即可推出全部正时刻相同的最小非负整数。前 $T$ 项严格为 $k=1,\ldots,T$，$T=0$ 为空；全局没有免费供应 $n$、$g_0$ 或共同含量，两个来源的 $n$ 可以不同。局部量 $L_p(e)$ 对模 $p^e$、所有整数初始对作同样定义，负数的 gcd 取绝对值。本节将证明它也恰是实际非负来源上的局部最小值。

对两个局部未来，首次分离为

$$
\Delta=\min\{k\ge1:\gcd(y_k,p^e)\ne\gcd(y'_k,p^e)\},
$$

永不分离时记为 $\infty$。长度 $T$ 充分，等价于每个有限的 $\Delta$ 都不超过 $T$。本节目标只是 gcd 全未来，不是完整数量、组成或树的恢复。

**引理 126.2（所复用的局部层与可实现分支）。** 采用定理 120.3、120.4 的射影直线 $P_j$、轨道 $O_j$ 及秩

$$
r_j=\min\{r\ge1:p^j\mid F_r\}.
$$

这些秩是射影返回阶，不是 Pisano 周期或矩阵阶。剩余精度 $m$ 的本原标签恰为：首层无命中；深度 $h<m$ 的退出及相位 $\tau\bmod r_h$；或深度 $m$ 的末层轨道及相位。无命中存在恰当且仅当 $r_1<p+1$；深度 $h$ 的退出存在恰当且仅当 $r_{h+1}=r_h$。每个所列相位与分支均可实现。

对标签 $\lambda$ 定义第 $j$ 层命中集

$$
E_j(\lambda)=
\begin{cases}
\{k\ge1:k\equiv\tau\pmod{r_j}\},&j\le h,\\
\varnothing,&j>h.
\end{cases}
$$

无命中标签的所有集合为空，本原截断指数为 $\sum_{j=1}^m\mathbf1_{E_j(\lambda)}(k)$。

证明。此处只提取既有分类中将用到的对应。由 $M^r=F_{r-1}I+F_rM$，$[1:0]$ 返回恰当且仅当 $p^j\mid F_r$，此时整个矩阵为单位标量。第 $k$ 行读出的本原核是 $[F_k:-F_{k-1}]=M^{-(k-1)}[1:0]$，故轨道相位恰给显示的同余命中集。约化使命中层构成初段，较高层命中集包含在较低层内。

每个射影点恰有 $p$ 个提升，且 $r_j\mid r_{j+1}\mid pr_j$。后一整除可由 $M^{r_j}=aI+p^jB$ 的 $p$ 次幂模 $p^{j+1}$ 为标量看出，包含 $p=2,j=1$。增长时全部 $p$ 个子点都在轨道；停滞时只有一个轨道子点，其余 $p-1$ 个都是退出。取任一非轨道子点并任意继续提升，它不会重新进入更高轨道；轨道子点则始终可沿轨道提升。首层有 $p+1$ 个点，故其补集准确给无命中条件。这样同时说明了全部标签及其实际局部代表的存在，而非仅列形式标签。$\square$

**定理 126.3（第一处分叉给准确首次分离）。** 两个不同本原标签 $\lambda,\mu$，设 $\ell$ 为 $E_\ell(\lambda)\ne E_\ell(\mu)$ 的最小层。用 $[t]^+_R\in\{1,\ldots,R\}$ 表示正代表，特别 $[0]^+_R=R$。若恰有一个第 $\ell$ 层命中集非空，相位为 $\alpha$，则

$$
\Delta=[\alpha]^+_{r_\ell}.
$$

若两个集合非空、相位分别为不同的 $\alpha,\beta$，则

$$
\Delta=\min\bigl([\alpha]^+_{r_\ell},[\beta]^+_{r_\ell}\bigr).
$$

相同标签的首次分离为 $\infty$。

证明。较低层集合逐层相同。同层两个不同非空集合是同一模数的两个不交剩余类；其中较早的正代表是它们对称差的首点。只有一集合非空时，首点就是它的正代表。在这个首点之前，两来源都未命中第 $\ell$ 层；更高命中集分别包含于各自第 $\ell$ 层，故也不可能提前产生差别。低层贡献相等，所以首点以前的全部截断指数相等。到首点时，一个指数至少为 $\ell$，另一个小于 $\ell$；任何高层贡献都不能抵消这个阈值差别。

若 $\ell>1$，共同父层必须非空，否则两个子层都为空。两个不同非空子相位只发生在增长步；空子层与非空子层的分叉只发生在停滞步。首层则另允许无命中。因而上述情形覆盖所有不同标签。$\square$

### 126.2. 准确阶梯、共同含量与全局实现

**定理 126.4（本原时域的尖锐阶梯）。** 定义

$$
B_p=
\begin{cases}r_1-1,&r_1=p+1,\\r_1,&r_1<p+1,\end{cases}
\qquad
W_j=
\begin{cases}r_j,&r_{j+1}=r_j,\\(p-1)r_j,&r_{j+1}=pr_j.\end{cases}
$$

剩余精度 $m\ge1$ 的准确本原时域为

$$
P_p(m)=\max\bigl(\{B_p\}\cup\{W_j:1\le j<m\}\bigr).
$$

其中每个候选最大值都有两个本原整数初始对达到。于是 $P_p(1)=B_p$，而 $m\ge2$ 时

$$
P_p(m)=
\begin{cases}
r_m,&r_m=r_{m-1},\\
r_m-r_{m-1},&r_m=pr_{m-1}.
\end{cases}
$$

证明。首层不同相位的正代表在 $1,\ldots,r_1$ 中，两个代表的较小者最大为 $r_1-1$，由最后两个相位达到。若有无命中类，把它与相位零比较，首次分离为 $r_1$。这些就是 $B_p$ 的两个情形，所选轨道相位均能提升到末层。

增长步令 $R=r_j$。若父相位首个正命中是 $s\in\{1,\ldots,R\}$，其 $p$ 个子相位的正代表为

$$
s,s+R,\ldots,s+(p-1)R.
$$

两个不同子相位的较小代表至多为 $s+(p-2)R$；对 $s$ 取最大即 $(p-1)R$，由 $s=R$ 及最后两个子相位达到。它们都能继续沿轨道提升至精度 $m$。停滞步则选同一父点的轨道子点与退出子点，首次分离就是 $s$；父相位零给最大值 $R$。退出子点的后续任意提升仍退出，而另一个可沿轨道升至末层，所以停滞最大值也真正达到。

这些构造可直接指定整数代表。对 $t\ge1$ 令

$$
K_t=(F_t,-F_{t-1}).
$$

相邻 Fibonacci 数的 Euclid 递推给互素，故 $K_t$ 本原，且它在每层的相位为 $t$。增长步用 $K_{(p-1)R}$ 与 $K_{pR}$；首层满轨道用 $K_{r_1-1}$ 与 $K_{r_1}$；首层非满用 $K_{r_1}$ 与一个首层轨道外方向的本原提升。停滞步用相位零的轨道父点，一个轨道子点及一个非轨道子点，再分别提升。有限环的本原代表至少有一坐标为 $p$ 单位，可取整数代表，因而这些都是实际整数初始对。定理 126.3 证明任意一对首次分离都落在上述某类，且每个候选界均被达到，故最大值恰为最小充分长度。

最后，若末步停滞，其值 $r_m$ 不小于以前的停滞值和 $B_p$；以前任一增长值严格小于那一步的结果秩，也不超过 $r_m$。若末步增长，写 $R=r_{m-1}$；以前所有候选均不超过 $R$，末候选 $(p-1)R\ge R$，所以仍为最大。$p=2$ 时允许相等，不要求最大位置唯一。$\square$

**定理 126.5（不免费供应含量的一般模数准确公式）。** 有 $T_1=0$。若 $H>1$，则

$$
T_H=\max_{p^e\parallel H}L_p(e),\qquad L_p(e)=P_p(e).
$$

具体地，$L_p(1)=B_p$，而 $e\ge2$ 时

$$
L_p(e)=
\begin{cases}
r_e,&r_e=r_{e-1},\\
r_e-r_{e-1},&r_e=pr_{e-1}.
\end{cases}
$$

局部值在全整数初始对与实际非负来源上相同；全局下界甚至可取每个来源坐标在 $\{0,\ldots,H-1\}$ 内。这里不声称任一固定 $n$ 纤维也取这个最大值。

证明。记 $c(k)=\min(e,\nu_p(y_k))$、$d=\min(e,\nu_p(n),\nu_p(z))$。理想 $(n,z)=(z,n+z)$ 给

$$
d=\min(c(1),c(2)).
$$

所以不同含量最迟第二项分开。$d=e$ 时整个未来恒饱和；此标签包括整数零，但并不要求整数来源为零。$d<e$ 时除以 $p^d$ 得本原对，剩余精度 $m=e-d$，原读数指数为 $d$ 加本原指数。因此相同含量的有限首次分离由定理 126.3 控制，至多为 $P_p(m)$。

阶梯公式给 $P_p(m)\le P_p(e)$。又 $F_1=F_2=1$，故 $r_1\ge3$、$B_p\ge2$；前两项恢复含量的成本已经包含在这个时域内。饱和、无命中、各级退出和全部剩余精度因此都受同一界控制。定理 126.4 在精度 $e$ 的本原见证达到它，证明全整数域的 $L_p(e)=P_p(e)$。

一个 gcd 由所有完整素数幂的截断指数唯一决定，所以长度 $\max L_p(e)$ 同时确定每个局部未来，给全局上界。为实现下界，选达到最大值的 $P=p^e$，在这个因子上用定理 126.4 的尖锐初始剩余对；在每个其它完整因子 $Q$ 上，把两来源的 $n,z$ 都置为零模 $Q$。逐坐标 CRT 给模 $H$ 的两个观察对。分别施加 $C^{-1}$，把两个来源坐标取在 $0,\ldots,H-1$ 内，便得到非负实际来源。其真实观察对乘回 $C$ 后恰有指定剩余；逆式也直接保证实际不等式 $5n\ge3z$、$2z\ge3n$。

选定因子上的首次分离仍恰为 $L_p(e)$，其余因子永远饱和，所以完整 gcd 的首次分离也恰在此处。取 $H=P$ 还证明局部界在实际来源上同样尖锐。这个 CRT 构造允许两来源有不同 $n$，不能搬到任意固定纤维而省去区间占用证明。$H=1$ 时包括零项在内所有 gcd 都为 1，故空前缀已足够。$\square$

### 126.3. 秩的全部提升与模 5040 的局部尖锐值

**定理 126.6（保留奇素数初始赋值及二进停滞的秩公式）。** 对奇素数 $p$，令 $r=r_1$、$s=\nu_p(F_r)$。则 $s$ 是有限正整数，且

$$
r_j=r p^{\max(j-s,0)}.
$$

相应地

$$
L_p(1)=r-\mathbf1_{\{r=p+1\}},\qquad
L_p(e)=
\begin{cases}
r,&2\le e\le s,\\
(p-1)r p^{e-s-1},&e>s.
\end{cases}
$$

第二式用于 $e\ge2$；$s=1$ 时中间停滞区间为空。这里不假定所有奇素数都有 $s=1$。二进秩另为

$$
r_1=3,\quad r_2=6,\quad r_j=3\cdot2^{j-2}\quad(j\ge3),
$$

其中 $r_2=r_3=6$ 是真正停滞。故

$$
\begin{aligned}
&L_2(1)=2,\quad L_2(2)=3,\quad L_2(3)=6,\quad
L_2(e)=3\cdot2^{e-3}\quad(e\ge4),\\
&L_3(1)=3,\quad L_3(e)=8\cdot3^{e-2}\quad(e\ge2),\\
&L_5(1)=5,\quad L_5(e)=4\cdot5^{e-1}\quad(e\ge2),\\
&L_7(1)=7,\quad L_7(e)=48\cdot7^{e-2}\quad(e\ge2).
\end{aligned}
$$

证明。奇素数情形，$r\ge3$ 给 $F_r>0$，故 $s$ 有限。写

$$
M^r=aI+p^s bM,\qquad a=F_{r-1},\quad b=F_r/p^s.
$$

相邻项互素说明 $a,b$ 都是 $p$ 单位。此幂在 $j\le s$ 层为标量，而约化到第一层迫使每个返回阶是 $r$ 的倍数，所以这些层的秩都为 $r$。其非对角系数的赋值恰为 $s$，下一层不能继续保持这个秩。

为排除之后的停滞，设 $A=aI+p^j bM$，其中 $j\ge1$、$a,b$ 为 $p$ 单位。二项式展开 $A^p$ 的一次 $M$ 项为 $p^{j+1}a^{p-1}bM$。次数 $2\le t\le p-1$ 的项有因子 $p^{jt+1}$，均被 $p^{j+2}$ 整除；最后一项有因子 $p^{jp}$，因 $p\ge3$ 也被 $p^{j+2}$ 整除。把 $M^t$ 用 $M^2=M+I$ 写回整数基 $I,M$ 不会降低这些整除性。因此

$$
A^p=a'I+p^{j+1}b'M,\qquad
 a'\equiv a^p\pmod p,\quad b'\equiv a^{p-1}b\pmod p.
$$

两个新系数仍为单位，非对角系数的赋值准确增加一，而不是仅有下界。这个论证包含边界 $p=3,j=1$。由 $M^r$ 开始迭代，$M^{rp^t}$ 的非对角系数赋值恰为 $s+t$；结合提升比只有 $1,p$，每次旧秩在下一层非标量，故之后必须次次乘 $p$。这证明完整秩公式。它未用特征根分离，对分歧素数 5 也适用。

二进部分不用上述奇素数论证。定理 120.5 的恒等式 $M^3=I+2M$、$M^6=5I+8M$ 给模 2、4、8 的秩 $3,6,6$。从 $j=3$ 开始，若

$$
M^{r_j}=aI+2^j bM,\qquad a,b\text{ 均为奇数},
$$

则平方后得到

$$
(M^{r_j})^2=(a^2+2^{2j}b^2)I+
2^{j+1}b(a+2^{j-1}b)M.
$$

标量系数与除出 $2^{j+1}$ 后的 $M$ 系数都为奇数。旧幂在模 $2^{j+1}$ 非标量，提升二分便强制下一秩翻倍。以 $M^6=5I+8M$ 为初值，归纳给所有二进秩，准确保留模 4 到模 8 的停滞。

最后，定理 120.5 给模 $3,5,7$ 的秩分别为 $4,5,8$，且 $F_4=3,F_5=5,F_8=21$，所以这三素数的 $s$ 均为 1。模 3、7 轨道满，模 5 不满。逐项代入定理 126.5 即得显示的全部时域。特别，对 $2,3,5,7$ 的任意幂所组成的 $H$，取对应局部值的最大值即可；缺失因子的值取零，全缺失给 $H=1$。一般奇素数的 $r,s$ 仍是准确算术参数，没有把尚未给出的参数数值当作已知。$\square$

**命题 126.7（四个实际局部尖锐见证）。** 模 $16,9,5,7$ 的准确局部连续长度依次为 $6,8,5,7$。以下每对均为实际非负来源，首个分离位置分别达到这些值。

证明。模 16 取 $v=(13,2)$、$v'=(1,6)$，实际观察对分别为 $(32,49)$、$(20,33)$，模 16 为 $(0,1)$、$(4,1)$。这两个剩余代表的前六项分别是

$$
(1,1,2,3,5,8),\qquad(1,5,6,11,17,28).
$$

故前五个局部 gcd 同为 $(1,1,2,1,1)$，第六个为 8、4。秩 $3,6,6,12$ 给上界 $12-6=6$。

模 9 取 $v=(6,2)$、$v'=(0,2)$，实际观察对为 $(18,28)$、$(6,10)$，剩余为 $(0,1)$、$(6,1)$。两者模 3 的命中列均为 $0\pmod4$；首七项只有第四项命中。第四项 $2n+3z$ 在剩余代表上为 3、15，都给 gcd 3，其余六项给 1。第八项 $13n+21z$ 为 21、99，给 gcd 3、9。秩 $4,12$ 给上界 $12-4=8$。

模 5 取 $v=(2,2)$、$v'=(1,3)$，实际观察对为 $(10,16)$、$(11,18)$，剩余为 $(0,1)$、$(1,3)$。第一条是 $F_k$；第二条满足 $M(1,3)=3(1,3)\pmod5$，故 $y_k=3^k\pmod5$ 永不命中。前四项 gcd 均为 1，第五项为 5、1。此处 $r_1=5<6$，无命中分支使准确界为 5。

模 7 取 $v=(4,2)$、$v'=(2,6)$，实际观察对为 $(14,22)$、$(22,36)$，剩余为 $(0,1)$、$(1,1)$，所以序列分别为 $F_k,F_{k+1}$。由

$$
F_1,\ldots,F_8=1,1,2,3,5,8,13,21
$$

知前六项 gcd 均为 1，第七项为 1、7。$r_1=8=p+1$ 排除本原无命中，给准确界 7。

每个实际观察对均由 $C$ 直接乘所列来源得到；局部读数只依赖其剩余，故这些是实际尖锐见证。由定理 126.5，$T_{5040}=\max(6,8,5,7)=8$；其全局实际尖锐对也已由定理 121.3 给出。引理 121.2 所列模 7 长度 8 明确只是充分值，本命题将它收紧到 7，不改变定理 121.3、121.4 的全局八步与最坏已知数量七步结论。$\square$

## 127. 同一自适应策略同时达到最少查询与最短索引

### 127.1. 资源契约及六项块解码

**定义 127.1（查询数与最大索引的联合目标）。** 固定 $H=5040$，沿用定义 122.1 的确定性同源重置查询。每一问选择一个正时刻 $k$，在同一个原始来源的副本上执行准确 $k$ 次 $\rho$，只读 $g_k=\gcd(qM^kv,5040)$；没有免费的中间读数。全局不供应 $n$ 或 $g_0$；已知数量契约免费供应确切 $n$，故可算 $g_0$。目标始终为全部正时刻的 gcd 未来类。

策略的 $Q$ 为最坏付费查询数，$T$ 为最坏最大查询索引；不查询的运行最大索引取零。$D_{\mathrm{all}},D(n)$ 仍为 §122 的最小查询数；另记 $H_{\mathrm{all}},H(n)$ 为允许任意有限查询数时最小的最大索引。空纤维的值按零约定。独立重置时的替换工作量是各被查询时刻之和，不能与 $Q,T$ 混同。

记 $f_p(k)=\nu_p(g_k)$，即截断于 $(e_2,e_3,e_5,e_7)=(4,2,1,1)$ 的指数。完整局部标签复用引理 122.3、122.4、122.5；它们分别来自定理 120.3—120.5，时间零的代数解释及 gcd 周期整除 120 复用引理 122.2。以下明确给出这些标签在同一短查询表上的解码，不重新建立来源或标签分类。

**引理 127.2（连续六项块完全解决二进分量）。** 对 $b=0$ 或 $b=1$，若已得到 $g_b,\ldots,g_{b+5}$，则二进完整未来已确定；$b=0$ 的第一项只在已知 $n$ 契约免费取得。

证明。任意相邻两项生成的整数理想都等于 $(n,z)$，因为更新 $(u,v)\mapsto(v,u+v)$ 有整数逆，故

$$
d_2=\min(4,\nu_2(n),\nu_2(z))
=\min(f_2(b),f_2(b+1)).
$$

$d_2=4$ 时恒饱和。否则六项包含每个模 3 行，升高指数唯一所在行 $r\pmod3$ 被确定；$d_2=3$ 时这已完成全部标签。若 $d_2\le2$，六项又恰各取一个模 6 类，其中恰有一个实际时刻 $s$ 的指数至少为 $d_2+2$，它给正确相位 $s\pmod6$。同一行的另一个模 6 类指数为 $d_2+1$，行外为 $d_2$。保留这个实际 $s$，终端读数逐项决定剩余分支：

- $d_2=2$ 时值为 4，只需相位 $s\pmod6$；
- $d_2=1$ 时值 3 为深度二退出，值 4 为剩余末层轨道；两者相位都为 $s\pmod6$；
- $d_2=0$ 时值 2 为深度二退出；值 3 为末层轨道、模 12 相位 $s+6$；值 4 为末层轨道、模 12 相位 $s$。

这是引理 122.3 的全部含量和深度行。尤其读到截断值 4 并无歧义，读到 3 时无需再试另一模 12 提升。已知 $n$ 时 $s$ 可以是零，它只是同一相位表的已供应条目；零来源由饱和行处理。$\square$

**引理 127.3（唯一可能未完成的三进列及可见分支）。** 在引理 127.2 的同一块之后，至多有一个三进细相位尚未确定。再查询

$$
K=
\begin{cases}
b+7,&d_3=0\text{ 且 }f_3(b+3)=1,\\
b+6,&\text{其它情况},
\end{cases}
\qquad d_3=\min(f_3(b),f_3(b+1))
$$

即可完成三进全未来。

证明。引理 122.4 的全部三进形式为：含量 2 时恒为 2；含量 1 时为 $1+\mathbf1_{k\equiv c\ (4)}$；含量 0 时为

$$
f_3(k)=\mathbf1_{\{k\equiv c\pmod4\}}+
\mathbf1_{\{k\equiv t\pmod{12}\}},\qquad t\equiv c\pmod4.
$$

六项涵盖全部四列，故含量 2 已结束，含量 1 的唯一升高列也已确定。含量 0 时唯一正读数列给 $c$；该列有三个可能的模 12 相位，值 2 确定本时刻的相位，值 1 排除本时刻的相位。

列 $b,b+1$ 各在块内出现两次，时刻相差 4，故测试的是不同细相位；出现 2 即确定，两个 1 则排除两个相位、确定第三个。只有列 $b+2,b+3$ 各出现一次。未完成恰在正读数列是这两列之一且其唯一读数为 1 时发生；因正读数列唯一，不会同时欠两列测试。

若 $d_3=0,f_3(b+3)=1$，未完成列就是 $b+3$，时刻 $b+7$ 补同列第二个不同细相位。其它分支若仍未完成，只可能是列 $b+2$，由 $b+6$ 补足；已经完成时 $b+6$ 是明确的默认选择。补问读到 2 就取它的模 12 相位，读到 1 就排除第一问与补问两相位，取该列第三相位。两问相差 4，绝非重复同一细相位。分支只依赖已得到的截断指数，没有用隐藏相位选择时刻。$\square$

### 127.2. 联合策略、实际下界与共同尖锐纤维

**定理 127.4（全局 $(Q,T)=(7,8)$ 与已知数量统一 $(6,7)$ 的同一策略）。** 全局先查询 $1,2,3,4,5,6$，然后按

$$
K=8\ \Longleftrightarrow\
\min(\nu_3(g_1),\nu_3(g_2))=0\ \text{且}\ \nu_3(g_4)=1
$$

选择最后一问，否则 $K=7$。已知 $n$ 时先免费算 $g_0$，查询 $1,2,3,4,5$，然后按

$$
K=7\ \Longleftrightarrow\
\min(\nu_3(g_0),\nu_3(g_1))=0\ \text{且}\ \nu_3(g_3)=1
$$

选择最后一问，否则 $K=6$。这两种策略分别同时满足 $Q\le7,T\le8$ 和 $Q\le6,T\le7$。

证明。二进部分由引理 127.2 在最后一问前已完成，三进部分由引理 127.3 在最后一问后完成。现核对另外两轴确由这同一组实际时刻完成。

模 5 用全局的 $1,\ldots,5$，或已知数量的 $0,\ldots,4$，均恰覆盖五个剩余。按引理 122.5，五次命中是饱和，零次是本原无命中，恰一次指出相位；两至四次命中不可能来自合法标签。

全局所取集合是 $\{1,\ldots,6,7\}$ 或 $\{1,\ldots,6,8\}$，都含七个不同模 8 槽位。七次模 7 命中表示饱和，恰一次指出相位，零次确定唯一未测相位；后一推断依赖模 7 没有本原无命中标签。在 $K=7$ 分支，未测相位为 0；在 $K=8$ 分支为 7。

已知数量时的六个付费时刻是 $\{1,\ldots,5,6\}$ 或 $\{1,\ldots,5,7\}$，均为不同的非零模 8 槽位。加免费零时刻后仍有七个不同槽位，上述解码适用。也可直接看：$7\nmid n$ 时零时刻排除饱和与相位 0，六问命中即知相位，全未命中则分别确定唯一遗漏的非零相位 7 或 6；$7\mid n$ 时只可能饱和或相位 0，恒被查询的时刻 1 已可区分。

得到四个局部标签后，对任意 $k\ge1$ 输出

$$
g_k=2^{f_2(k)}3^{f_3(k)}5^{f_5(k)}7^{f_7(k)}.
$$

这是完整未来解码器。所有时刻均是同一来源上的一个实际 $\rho^k$ 查询，每一步选择所依赖的答案也来自该来源；没有独立拼接四个不相容的轴向查询表。全局恰七问且不超过 8，已知数量至多六问且不超过 7。空纤维无需运行，单来源纤维可由 $n$ 直接输出，作为零问捷径；这不影响统一界。$\square$

**命题 127.5（任意大时刻仍不能突破的查询下界）。** 有 $D_{\mathrm{all}}=7$；若 $7\nmid n$ 且 $L_n\ge4321$，则 $D(n)=6$，因而 $\sup_nD(n)=6$。长度条件仅为充分条件。

证明。复用定理 122.8 的八个实际来源构造。记 $\operatorname{res}_m$ 为逐坐标取 $0,\ldots,m-1$ 内代表，则

$$
v_\tau=720\operatorname{res}_7(C^{-1}K_\tau),\qquad1\le\tau\le8
$$

均非负；$720$ 模 7 为单位，故其模 7 相位恰为 $\tau\pmod8$，其余因子 $16,9,5$ 恒饱和。每个完整答案是：命中该相位给 5040，否则给 720。任意确定性策略沿全答 720 的路径至六问或提前停止，每问无论时刻多大都至多排除一个相位，故至少两个实际来源存活。固定任一最终存活者作为从始至终的来源：第一问真实答案为 720；若先前历史相同，确定性使下一时刻相同，而该来源仍未被命中，故真实答案仍为 720。归纳证明每个存活者都实现整条历史，绝非每问更换来源。两个存活相位的未来不同，故六问不能普遍成功。定理 127.4 给七问上界。

固定 $n$ 时，复用定理 122.9 的实际区间族，但保留其全答案形式。令

$$
z_j=A_n+720j,\qquad
v_j=(5n-3A_n-2160j,\ 2A_n-3n+1440j),\qquad0\le j\le6.
$$

$L_n\ge4321$ 保证最后一点 $A_n+4320\le B_n$，所以这七个都是同一个确切 $n$ 的非负来源。它们的未来数量差是 $720jF_k$，非 7 部分全部相同，为

$$
b_n(k)=\gcd(F_{k-1}n+F_kA_n,720).
$$

因 $7\nmid n$ 且步长 720 模 7 可逆，七个 $z_j$ 覆盖所有模 7 剩余，即七个非零模 8 相位；相位 0 需要第一坐标为零，不能出现。沿每问回答 $b_n(k)$ 的路径，一问至多排除一个来源，模 8 槽位零不排除任何来源。五问后两个实际同 $n$ 来源仍实现整个历史；上述固定存活者归纳仍适用，故五问不够。六问上界给等号。

特别在 $n=25920$，$I_n=[38880,43200]$、$L_n=4321$、$n\equiv6\pmod7$。这族具体为 $(2160(6-j),1440j)$，共同非 7 答案恒为 720；五问仍有两条完整全答 720 历史，未来在某时刻分为 5040 与 720。这证明最坏纤维确实达到六问。$\square$

**定理 127.6（最大索引下界及同一 $n=30313$ 的双重尖锐性）。** 有

$$
H_{\mathrm{all}}=8,\qquad \sup_nH(n)=7,
$$

而在同一个实际纤维

$$
n=30313,\qquad I_n=[45470,50521],\qquad L_n=5052
$$

中，$D(n)=6$、$H(n)=7$。定理 127.4 的同一策略因而全局达到 $(7,8)$，并在这个纤维达到 $(6,7)$；两项是各自最坏运行的资源，不要求其最坏情况为同一个单独来源。

证明。若两个来源的免费信息相同，且在每个 $1\le k\le h$ 的答案相同，则任意限制在这些时刻的确定性策略都得到相同历史：按询问次数归纳，历史相同使选择时刻相同，其答案再相同。这个论证容许任意次序、重复和任意有限查询数。因此未来不同的这样的实际对，排除一切索引上限为 $h$ 的策略，而不只是连续策略。反向，若整个前缀足以区分未来，直接问该前缀即给索引上界。

全局下界直接使用定理 121.3 的实际对 $(6,5042),(8406,2)$，观察对为 $(15138,25228),(16818,25228)$。它们差 $(1680,0)$ 保持模 $16,5,7$ 的全部未来；模 9 为 $(0,1),(6,1)$，首七项只在第四项有共同指数 1，而第八项指数为 1、2。该定理已给准确 $g_8=6,18$，所以任意索引不超过 7 的策略失败。定理 127.4 给上界 8。

现在在所述同一纤维取

$$
v=(15131,17),\qquad v'=(10091,3377),\qquad
z=45478,\quad z'=47158.
$$

直接有 $2\cdot15131+3\cdot17=30262+51=30313$，以及 $2\cdot10091+3\cdot3377=20182+10131=30313$；下一读数分别为 $45393+85=45478$、$30273+16885=47158$，均在实际区间。其差 $z'-z=1680$ 使非 3 部分永远相同。模 9 的对为 $(1,1),(1,7)$，共同正读数列为 $3\pmod4$；前六项中只有第三项，它的模 9 值是 3、6，均仅给一个因子 3。第七项 $8n+13z$ 的模 9 值为 3、0，出现分离。完整前六个 gcd 同为

$$
(g_1,\ldots,g_6)=(2,1,3,20,1,7),\qquad
(g_7(v),g_7(v'))=(6,18).
$$

这些也可由定理 121.4 的实际对同时在第一来源坐标加 10080 得到：$n,z$ 分别增加 $20160,30240$，都是 5040 的倍数，所以整条 gcd 未来不变。这里是构造另一个纤维中的见证，不是对被查询来源执行额外操作。由不可区分论证，此纤维 $H(n)\ge7$，联合策略给等号及全部纤维的统一上界。

还需在这个相同纤维核对查询下界。$30313=7\cdot4330+3$ 且 $5052\ge4321$，所以命题 127.5 适用。其实际七点具体为

$$
z_j=45470+720j,\qquad
v_j=(15155-2160j,\ 1+1440j),\qquad0\le j\le6.
$$

最大 $z_j=49790\le50521$，最小第一坐标为 2195，均非负，故确有 $D(30313)=6$。这不是把两个不同纤维的最优值合起来冒称同纤维取等。查询数与索引的全局下界分别作用于每个正确策略，而定理 127.4 构造的一个策略同时满足两个上界；所以联合取等成立。它不声称每个纤维或每个来源都需要这些资源。$\square$

### 127.3. 替换工作量与当前读出的条件桥

**命题 127.7（重置工作上界及单副本推进）。** 定理 127.4 的策略，在各问独立重置并逐步替换的计数下，全局工作量至多 29，已知数量至多 22。若另行允许对推进中的单副本作不破坏状态的当前读出 $R_{\rm cur}(s)=\gcd(qs,5040)$，相同历史分别可用至多 8、7 次替换取得。这些工作量都是上界，不是工作最优定理。

证明。重置计数分别为

$$
1+2+3+4+5+6+K=21+K\le29,\qquad
1+2+3+4+5+K=15+K\le22.
$$

免费 $g_0$ 不执行替换；零问捷径只会减少成本。此计数不含副本取得、重置、存储及算术。

在另行指定的当前读出契约下，对递增的选定时刻 $k_1<\cdots<k_m$，先推进 $k_1$ 步，以后在两读数之间推进 $k_i-k_{i-1}$ 步。由

$$
M^{k_i-k_{i-1}}M^{k_{i-1}}v=M^{k_i}v
$$

归纳，读取时确为原来源的第 $k_i$ 个状态。过去读数相同又保证自适应分支选择相同，故重现同一查询历史。本节两策略始终递增，推进到 7 或 8、以及 6 或 7 即可；跳过的时刻没有免费观察。

此桥确实要求读当前状态。若换成 $R_{\rm next}(s)=\gcd(qMs,5040)$，在状态 $M^kv$ 读取的是 $g_{k+1}$，不是 $g_k$；保持上述状态时刻不变就使所有索引偏移一，不能代替此桥。它也未模拟任意非递增的重置表。重置界 29、22 不因这个不同契约而变成 8、7。

已知 $n=0$ 时只有零来源，未来恒 5040；$n=1$ 为空纤维；单来源或仅一个未来类的非空纤维不需查询。全局只需识别饱和未来类，不需将零来源与同剩余的非零来源分开。本节未确定其余逐 $n$ 的完整 $D(n),H(n)$、所有逐纤维最优资源能否共同达到、完整查询数与最大索引权衡、最少总工作、随机或带噪查询、工作空间以及其它操作契约。$\square$

## 128. 非自适应查询的完整全局判据与三种量词次序

### 128.1. 预选时间表及任意时刻的局部解码

**定义 128.1（非自适应的三个问题）。** 沿用定义 127.1 的同源重置、正时刻 gcd5040 读数及全未来目标。非自适应表是有限集合 $S\subset\mathbb Z_{>0}$，必须在任何答案出现前选定；重复同一时刻没有新信息。定义：

- $N_{\mathrm{all}}$：无免费 $n$ 或 $g_0$，选一个 $S$ 识别所有实际来源的最小 $|S|$；比较来源可以有不同 $n$。
- $N(n)$：确切 $n$ 免费供应，表 $S_n$ 可依赖 $n$、不能依赖答案，只需区分该实际纤维的未来；空纤维取零。
- $U$：先选一个与 $n$ 无关的 $S$，再对每个 $n$ 允许解码器使用确切 $n$ 和 $S$ 上的答案，要求每个纤维都正确时的最小 $|S|$。

所以 $\sup_nN(n)$ 的次序是“对每个 $n$，存在 $S_n$”，$U$ 是“存在一个 $S$，对每个 $n$”；它们也都不同于不供应 $n$ 的全局问题。再记

$$
H_6=\min\{H:\text{对每个 }n\text{，存在识别表 }S_n\subseteq\{1,\ldots,H\},\ |S_n|\le6\}.
$$

$H_6$ 限制非自适应六问，不是 §121 的连续长度，也不是 §127 的自适应最大索引。

**引理 128.2（任意索引集合的完整局部解码）。** 令 $E$ 为一组已合法得到读数的非负时刻；其中零只可来自已知 $n$。复用引理 122.2—122.5 的完整局部表，有以下充分解码规则。

第一，若 $E$ 覆盖全部模 6 剩余，则二进未来确定。第二，若 $E$ 在每个模 4 列中包含至少两个不同模 12 剩余，则三进未来确定。第三，全部五个模 5 剩余确定模 5 未来；至少七个不同模 8 槽位确定模 7 未来。若 $n$ 已知且 $7\nmid n$，六个不同非零模 8 槽位已经足够；$7\mid n$ 时任一非零槽位足够。各局部指数确定后，它们的乘积确定全部 gcd 未来，周期整除 120。

证明。二进表中，非饱和标签在两个模 3 行恒等于含量 $d_2$，另一行升高。因此全模 6 覆盖使最小读数恰为 $d_2$，不必额外供应含量或相邻时刻。饱和时全为 4；否则唯一升高行被定位。$d_2=3$ 只需该行；$d_2\le2$ 时指数至少为 $d_2+2$ 的类唯一确定模 6 相位。在这个类任取一个已测实际时刻 $s$，引理 127.2 的逐项终端解码仍适用：$d_2=2$ 的 4；$d_2=1$ 的 3 或 4；$d_2=0$ 的 2、3、4，分别给该引理列出的退出或末层相位。实际 $s\bmod12$ 被保留，所以无需同时测试其另一提升。这个理由与所选整数的大小及顺序无关。

三进表中，每个非饱和标签仅有一个升高列，另三列为含量 $d_3$。四列均出现使最小值恢复含量并定位升高列。$d_3=2$ 恒饱和，$d_3=1$ 只需列；$d_3=0$ 时该列的两个不同细相位由一次指数 2，或两次指数 1 的排除，确定三个可能相位中的唯一一个。模 5、7 的全命中、单命中、无命中及已知 $n$ 分支，正是引理 122.5 的穷尽解码。

这些表包括每种共同含量、二进退出、模 5 本原无命中和所有饱和标签。其局部周期分别整除 $12,12,5,8$，故完整 gcd 周期整除 $\operatorname{lcm}(12,5,8)=120$。这是从标签公式推出的无限时间结论，不是短时刻搜索，也不是矩阵或精确数量的周期。$\square$

### 128.2. 一个全局时间表的充要条件

**定理 128.3（非自适应全局识别的完整判据）。** 一个有限正时间表 $S$ 能识别全部实际来源的 gcd5040 全未来，当且仅当同一个 $S$ 同时满足：

1. $S\bmod6$ 包含全部六个剩余；
2. $S\bmod5$ 包含全部五个剩余；
3. $S\bmod8$ 至少有七个不同剩余；
4. 对每个 $c\in\mathbb Z/4\mathbb Z$，$S$ 中属于该列的时刻至少给出两个不同的模 12 剩余。

证明。充分性直接把引理 128.2 的四个解码器应用于这同一个集合；它们不需额外 $g_0$，所得四个截断指数给所有未来 gcd。

必要性逐项给实际完整答案相同的反例。以下 $\operatorname{res}_m$ 仍逐坐标取最小非负剩余，$K_t=(F_t,-F_{t-1})$；来源公式中的整数逆矩阵只用于构造见证，不授权任何向后执行或改变查询来源的操作。

若缺少模 6 类 $\sigma$，取其正代表 $s\in\{1,\ldots,6\}$，令 $h=(0,1)$、$h'=(4,1)$，构造

$$
v_h=315\operatorname{res}_{16}(6C^{-1}M^{-s}h),\qquad
v_{h'}=315\operatorname{res}_{16}(6C^{-1}M^{-s}h').
$$

两来源坐标非负，模 $9,5,7$ 恒饱和。因 $315\cdot6\equiv2\pmod{16}$，其观察初值模 16 为 $2M^{-s}h$、$2M^{-s}h'$；除以共同因子 2 后，在时刻 $s$ 的递推状态分别为 $(0,1)$、$(4,1)$ 模 8，故均本原，且同余模 4。它们有同一模 3 升高行及模 6 终端类 $\sigma$；一条继续命中模 8，另一条退出。引理 122.3 给原截断指数在 $\sigma\pmod6$ 上为 4、3，在其余位置完全相同。因此对每个 $k\in S$，完整答案同为

$$
\begin{cases}
630,&k\not\equiv\sigma\pmod3,\\
1260,&k\equiv\sigma\pmod3\text{ 且 }k\not\equiv\sigma\pmod6.
\end{cases}
$$

所有被测时刻只可能落在这两支。任一正时刻 $k\equiv\sigma\pmod6$ 的答案却为 5040、2520。这覆盖缺少的任意类，包括零类，未使用时间零查询。

若某模 4 列 $c$ 只有至多一个被测试的细相位，选该列中两个不同的未测相位 $\tau,\tau'\pmod{12}$，用 $1,\ldots,12$ 的代表构造

$$
v_\tau=560\operatorname{res}_9(C^{-1}K_\tau),\qquad
v_{\tau'}=560\operatorname{res}_9(C^{-1}K_{\tau'}).
$$

这些是非负来源，模 $16,5,7$ 恒饱和；$560$ 模 9 为单位，故三进相位为所选的两个相位。对整个 $S$，答案同为：列 $c$ 内 1680，列外 560。到正时刻 $k\equiv\tau\pmod{12}$，两答案为 5040、1680。因此该条件必要，即使 $S$ 含任意大的时刻或重复同一细相位也一样。

若缺少模 5 相位 $\tau$，构造

$$
1008\operatorname{res}_5(C^{-1}K_\tau),\qquad
1008\operatorname{res}_5(C^{-1}(1,3)).
$$

$1008=16\cdot9\cdot7$ 模 5 为单位，第一来源是所选单峰，第二来源是本原无命中方向，其余轴恒饱和。整个 $S$ 的答案均为 1008，而相位 $\tau$ 上为 5040、1008。

若只有至多六个模 8 槽位，选两个未测相位 $\tau,\tau'$，构造

$$
720\operatorname{res}_7(C^{-1}K_\tau),\qquad
720\operatorname{res}_7(C^{-1}K_{\tau'}).
$$

这是命题 127.5 的实际族，两来源的整个 $S$ 答案均为 720，却在一个未测相位上为 5040、720。

每对都由一个完整来源实现所有素数分量：乘数先饱和其它轴，单位倍数保留所选相位，$C^{-1}$ 把观察剩余变成非负来源坐标。没有只存在于形式标签上的未实现反例，也没有要求这些全局反例有相同 $n$。四项必要性与共同集合的充分性合并，即为所述充要条件。$\square$

**定理 128.4（全局非自适应恰八问及准确重置工作）。** 有 $N_{\mathrm{all}}=8$，由 $S=\{1,\ldots,8\}$ 达到。全局非自适应最小最大索引为 8，按独立副本逐步推进的最小替换次数和为 36；此同一表同时达到三者。

证明。四个模 4 列两两不交，每列必须有两个不同细相位，所以任何识别表至少有八个时刻。若至多七个时刻，定理 128.3 的三进构造在一个不足的列给两个实际来源：全部被测答案在列外为 560、列内为 1680，未来分离为 5040、1680。这是任意正整数时间表的下界，不以索引上限为前提。

集合 $1,\ldots,8$ 覆盖所有模 6、模 5 剩余及八个模 8 槽位，且四列的细相位对为 $(1,5),(2,6),(3,7),(4,8)$；每对相差 4，模 12 不同，故满足全部条件。八个不同正整数的最大值至少 8，和至少 $1+\cdots+8=36$；更多时刻不能降低这两个下界。所示表达到二者。36 只计每个重置副本的替换次数，不计复制、重置、空间或算术。$\square$

### 128.3. 允许时间表依赖确切数量时的六问

**定理 128.5（每个已知数量纤维的六问构造与最坏值）。** 对每个 $n$，有 $N(n)\le6$。可按 $n$ 而不按答案预选

$$
S_n=
\begin{cases}
S_B=\{1,2,3,4,5,6\},&3\mid n,\\
S_A=\{1,3,5,7,10,14\},&3\nmid n.
\end{cases}
$$

若 $7\nmid n$ 且 $L_n\ge4321$，则 $N(n)=6$。特别 $N(25920)=6$，并有 $\sup_nN(n)=6$；所述长度只是充分条件。

证明。先逐个核对这些同一实际整数的联合剩余。$S_A$ 按显示顺序的模 6、5、8 剩余分别为

$$
(1,3,5,1,4,2),\qquad(1,3,0,2,0,4),\qquad(1,3,5,7,2,6).
$$

加免费时刻 0 后模 6 全覆盖，正时刻本身模 5 全覆盖，模 8 是六个不同非零槽。它在非零模 4 列的配对为列 1 的 $(1,5)$、列 2 的 $(10,14)$、列 3 的 $(3,7)$，都相差 4，故各测两个不同细相位。$S_B$ 的模 6、5、8 剩余依次是

$$
(1,2,3,4,5,0),\qquad(1,2,3,4,0,1),\qquad(1,2,3,4,5,6).
$$

它也同时满足所需的二进、模 5 与已知数量模 7 覆盖，并访问全部模 4 列及细相位 $4\pmod{12}$。因此引理 128.2 已在同一表上解决三轴；$7\mid n$ 时所需只是非零槽位的一问，这两表均包含时刻 1。

只剩三进。若 $3\nmid n$，共同含量必为零，免费 $f_3(0)=0$ 又排除列 0；正读数列只能是 1、2、3。$S_A$ 在每个这样的列都测两相位，读到 2 或两个 1 后排除即可确定完整细相位。

若 $3\mid n$，用 $S_B$，前两读数恢复 $d_3$。含量 2 恒饱和；含量 1 只须唯一升高列，四列都已访问。含量 0 时 $z$ 为 3 单位，正读数列必是零列。若 $9\mid n$，免费 $f_3(0)=2$ 已指出细相位 $0\pmod{12}$；若 $3\mid n$ 而 $9\nmid n$，免费值为 1，排除相位零，只剩 4、8。时刻 4 的值分别是 2、1，准确区分。这穷尽了全部含量及 $n$ 的赋值，包括饱和与零来源。

上界作用于每个与已知 $n$ 相容的剩余对，因而不需假设固定短纤维含所有组合。下界用命题 127.5 的七个实际点 $z_j=A_n+720j$。任一至多五问的固定表遗漏至少两个非零模 8 相位；选对应两个来源，它们有相同确切 $n$，在整个表上共同返回 $b_n(k)$，而在一个遗漏相位处分别为 $7b_n(k)$ 与 $b_n(k)$。故五问不够。$n=25920$ 的完整区间与实际来源已在命题 127.5 列出，见证非 7 部分恒为 720，确实达到六问。

两表的最大索引分别为 6、14，重置替换和分别为 21、40。这些是构造上界，尚未声称每个纤维的最小工作量。$\square$

### 128.4. 固定纤维的三个必要条件与十四的尖锐性

**定理 128.6（充分长实际纤维上的必要覆盖）。** 下列各结论都针对一个原先固定的确切 $n$ 及其识别表 $S$：

1. 若 $3\nmid n$ 且 $L_n\ge5040$，则每个非零模 4 列必须至少测试两个不同模 12 相位。
2. 若 $7\nmid n$ 且 $L_n\ge4321$，则必须测试至少六个不同非零模 8 槽位。
3. 若 $\nu_2(n)=1$ 且 $L_n\ge2536$，则必须分别测试模 6 的类 2 与类 4。

这些是所述纤维上的必要条件；三个长度都仅保证以下实际构造可行，不主张最小阈值，也不是任意固定纤维的完整充要判据。

证明。第一项，若非零列 $c$ 至多测试一个细相位，选它的两个未测相位 $\tau,\tau'$。取正代表后，$F_\tau,F_{\tau'}$ 都是模 9 单位：Fibonacci 本身的模 3 零项恰在零模 4 列，这由引理 121.2 的本原计算或定理 120.5 的秩 4 给出。对每个所选相位定义唯一剩余 $R_\tau\pmod{5040}$，满足

$$
R_\tau\equiv -nF_{\tau-1}F_\tau^{-1}\pmod9,\qquad
R_\tau\equiv0\pmod{560}.
$$

令

$$
z_\tau=A_n+\operatorname{res}_{5040}(R_\tau-A_n),\qquad
v_\tau=(5n-3z_\tau,2z_\tau-3n).
$$

这里对标量的 $\operatorname{res}$ 也取最小非负代表。$A_n\le z_\tau\le A_n+5039\le B_n$，所以这是同一个原定 $n$ 的实际来源，不是仅有 CRT 标签。模 9 的观察对是单位倍数 $(n/F_\tau)K_\tau$，故有相位 $\tau$；两个来源模 560 的观察对相同。整个失败表上的完整共同答案是

$$
\gcd(F_{k-1}n,560)\begin{cases}3,&k\equiv c\pmod4,\\1,&k\not\equiv c\pmod4.\end{cases}
\qquad(k\in S).
$$

到正时刻 $k\equiv\tau\pmod{12}$，共同非 3 部分分别乘 9 与 3，所以未来不同。两个来源得到的免费 $n$ 与 $g_0$ 自然相同。

第二项，命题 127.5 的七个实际来源具有七个非零模 8 相位。若少于六个不同非零槽位被测，无论表中有多少重复剩余或零槽位，至少两个来源从未命中；它们对整个表都给共同答案 $b_n(k)$，但未来不同。这证明的是不同槽位数条件，不仅是查询总数下界。

第三项，写 $n=2m$，其中 $m$ 奇。对 $\sigma=2$，取第一个不小于 $A_n$ 且满足 $z\equiv-n\pmod{16}$ 的整数；对 $\sigma=4$，改取 $z\equiv2n\pmod{16}$。两次构造各令 $z'=z+2520$。有

$$
z\le A_n+15,\qquad z'\le A_n+2535\le B_n,
$$

所以每一对都在同一个实际 $I_n$。差 $2520=8\cdot9\cdot5\cdot7$ 保持所有非 2 部分的未来相同。原对的共同二进含量恰为 1，除以 2 后的初值模 8 分别为 $(m,-m)$（$\sigma=2$）或 $(m,2m)$（$\sigma=4$）。对应项为

$$
u_2=m-m=0\pmod8,\qquad
u_4=2m+3(2m)=8m=0\pmod8.
$$

第二来源的归一化 $z$ 增量是 $1260\equiv4\pmod8$，在这两个时刻造成 $4F_\sigma\equiv4\pmod8$，因为 $F_2=1,F_4=3$ 都奇。两个本原对仍同余模 4，故同一模 6 终端类恰为 $\sigma$；第一个继续命中模 8，第二个深度二退出。原指数只在 $\sigma\pmod6$ 不同，分别为 4、3。

更具体，令 $b_\sigma(k)=\gcd(F_{k-1}n+F_kz,315)$。若 $S$ 漏掉类 $\sigma$，每个 $k\in S$ 的完整共同答案是：行 $\sigma\pmod3$ 外 $2b_\sigma(k)$，该行内而终端类外 $4b_\sigma(k)$；终端类上的未来答案却为 $16b_\sigma(k)$ 与 $8b_\sigma(k)$。所以两个类 2、4 都必须被测，且各自有原定 $n$ 的实际全答案反例。$\square$

**定理 128.7（至多六问的统一索引上限恰为十四）。** 有 $H_6=14$。更强地，在单一实际纤维 $n=30242$ 中，每个正确的至多六问非自适应表都含一个至少为 14 的时刻，定理 128.5 的 $S_A$ 达到此界。

证明。统一上界由定理 128.5 得到。下界固定

$$
n=30242=2\cdot15121,\qquad n\equiv2\pmod3,\quad n\equiv2\pmod7,
\qquad I_n=[45363,50403],\quad L_n=5041.
$$

三个必要条件的所有假设在这同一个纤维同时成立。设 $S$ 至多六问且识别成功。三进条件强制恰有六个不同时间，每个非零模 4 列恰两问，零列无问。模 7 条件又要求六个不同非零模 8 槽位；零模 4 列已被排除，所以它们必须准确为

$$
\{1,2,3,5,6,7\}\pmod8.
$$

恰有两个偶数查询，分别在槽位 2、6。二进条件要求模 6 类 2、4 都被测，它们也都是偶数，因此必须由这两个偶查询各承担一个。若全部索引不超过 13，槽位 6 的正时刻只能是 6，因为下一个为 14；但 6 是零模 6，两个必需类都未承担。剩下一个偶查询不可能同时承担两类，矛盾。这是共同条件下的槽位论证，没有枚举短表，也没有以某个强充分条件失败代替必要性。

为明确此同一纤维每个缺轴的实际反例，三进缺列的来源按定理 128.6 取

$$
z_\tau=45363+\operatorname{res}_{5040}(R_\tau-45363),\quad
v_\tau=(151210-3z_\tau,2z_\tau-90726),
$$

其中 $R_\tau\equiv-30242F_{\tau-1}F_\tau^{-1}\pmod9$、$R_\tau\equiv0\pmod{560}$。它满足 $45363\le z_\tau\le50402<50403$，并具有该定理给出的整个失败表共同答案。模 7 缺槽时，用

$$
z_j=45363+720j,\quad v_j=(15121-2160j,1440j),\quad0\le j\le6.
$$

最后一点为 49683，最小第一坐标为 2161，故全部实际。任取两个未测相位的成员，整个表共同返回 $\gcd(F_{k-1}30242+F_k45363,720)$，未来在一个相位上相差因子 7。

二进两对还可完全写成数字。若漏类 $2\pmod6$，取

$$
(z,z')=(45374,47894),\qquad
(v,v')=((15088,22),(7528,5062)).
$$

两数量分别为 $30176+66=30242$、$15056+15186=30242$，下一数量为所列 $z,z'$，均在区间。观察对模 16 为 $(2,14),(2,6)$，除以 2 后为 $(1,7),(1,3)\pmod8$，第二项分别为 0、4 模 8。令

$$
b_2(k)=\gcd(F_{k-1}30242+F_k45374,315).
$$

在类 2 模 6 外的整个失败表，完整共同答案为 $2b_2(k)$（$k\not\equiv2\pmod3$）或 $4b_2(k)$（同行）；类 2 模 6 上则为 $16b_2(k),8b_2(k)$。在 $k=2$，非 2 部分为 1，准确 gcd 为 16、8。

若漏类 $4\pmod6$，取

$$
(z,z')=(45364,47884),\qquad
(v,v')=((15118,2),(7558,5042)).
$$

两数量为 $30236+6=30242$、$15116+15126=30242$。模 16 初值为 $(2,4),(2,12)$，归一化模 8 为 $(1,2),(1,6)$，第四项为 0、4 模 8。令

$$
b_4(k)=\gcd(F_{k-1}30242+F_k45364,315).
$$

类 4 模 6 外的共同答案为 $2b_4(k)$（$k\not\equiv1\pmod3$）或 $4b_4(k)$（同行）；终端类上为 $16b_4(k),8b_4(k)$，在 $k=4$ 准确为 16、8。两对差均为 2520，故非 2 部分确实在所有时刻相同，免费 $g_0$ 同为 2。

因此任一违反所需条件的表都有实际同 $n$ 的完整不可区分对；不要求同一对同时见证所有可能的表缺陷。$S_A$ 在此纤维正确且最大时刻为 14，完成等号。这个结论不排除七问取 $1,\ldots,7$，也不排除 §127 的依答案选择时刻的六问策略。$\square$

### 128.5. 查询表独立于数量的七问与退化边界

**定理 128.8（固定通用表、知数量解码的准确七问）。** 定义 128.1 的 $U=7$，尽管 $\sup_nN(n)=6$。

证明。正时刻表 $S=\{1,\ldots,7\}$ 不依赖 $n$。解码时加入免费 $g_0$，得到时刻 $0,\ldots,7$：它们覆盖全部模 6、5、8 剩余，四个模 4 列的细相位对分别为 $(0,4),(1,5),(2,6),(3,7)$，每对模 12 不同。引理 128.2 给所有纤维的解码，故 $U\le7$。

若存在通用于所有 $n$ 的至多六问表，先在 $n=30242$ 应用定理 128.6 的三进必要条件，迫使这个同一个表恰在每个非零模 4 列有两问，零列无问。保持表不变，转到另一个纤维

$$
n=30243,\qquad I_n=[45365,50405],
$$

取其中两个实际来源

$$
v=(15114,5),\qquad v'=(1674,8965),\qquad
z=45367,\quad z'=49847.
$$

它们的数量分别为 $30228+15=30243$、$3348+26895=30243$；下一数量分别为 $45342+25=45367$、$5022+44825=49847$，均属此区间。差 $4480=8\cdot560$ 保持所有非 3 分量。模 9 的观察对是 $(3,7)=K_4$、$(3,5)=K_8$，所以三进细相位分别为 4、8，正读数都只在零模 4 列。

在整个被迫避开零列的 $S$ 上，两来源的完整答案相同，准确为

$$
b(k)=\gcd(F_{k-1}30243+F_k45367,560),\qquad k\in S.
$$

免费信息也相同：同一个 $n=30243$ 及 $g_0=3$。但时刻 4 的实际数量为 196587、210027，非 3 gcd 部分都为 1，模 9 剩余为 0、3，故准确答案为 $g_4(v)=9,g_4(v')=3$。同一表无法区分这两个未来，矛盾。

这里 $30242$ 的作用是限制一个声称通用的表；真正的不可区分对两成员都在 $30243$ 纤维。没有用不同的免费 $n$ 冒充已知数量的下界，也没有由两个相同的最坏值推出逐纤维成本相同。$\square$

**命题 128.9（零问、整除纤维及资源结论的边界）。** $N(0)=0$，$N(1)=0$ 为空纤维约定。任一非空纤维有 $N(n)=0$，当且仅当所有实际来源的 gcd 全未来相同；单来源纤维因此不需查询。若 $5040\mid n$，则准确有

$$
N(n)=
\begin{cases}
0,&\gcd(z,5040)\text{ 在 }I_n\text{ 上恒定},\\
1,&\gcd(z,5040)\text{ 在 }I_n\text{ 上不恒定}.
\end{cases}
$$

证明。非负来源满足 $2a+3b=0$ 时只能为零；$I_0=\{0\}$，未来恒 5040，而 $I_1$ 为空。零问时输出只由免费 $n$ 决定，故在非空纤维中存在正确零问输出恰当且仅当只有一个实际未来类。多个不同来源可以属于同一类，不能只用来源数判正查询下界。

整除情形复用定理 120.9 的公式，并核对零项：写 $g=\gcd(z,5040)$、$z=gu$、$5040=gh$，则 $\gcd(u,h)=1$，且

$$
g_k=\gcd(F_kz,5040)=g\gcd(F_ku,h)=g\gcd(F_k,h).
$$

一次预定的时刻 1 就读出 $g$，决定全部未来。$g$ 在区间恒定则零问足够；有两个实际值则第一项就有两种未来，零问失败。$z=0$ 时 $g=5040,h=1,u=0$，仍有 $\gcd(0,1)=1$，所以没有除零或遗漏。全局饱和未来也包含非零来源；本任务只确定未来类，不负责识别整数零来源本身。

在同一操作契约下，全局自适应七问与非自适应八问相差一问；允许表依赖 $n$ 时两种最坏纤维查询数都为六，但这不推出每个 $n$ 的两种成本相等。全局非自适应表 $1,\ldots,8$ 同时达到查询数 8、最大索引 8、重置替换和 36；已知数量非自适应六问的统一最大索引恰为 14，构造替换和至多 40；后者只为上界。通用已知数量表 $1,\ldots,7$ 达到七问、索引 7 及替换和 28。§127 的重置和 29、22 以及条件式当前读出推进界 8、7 也只为各自契约的上界。

尚未确定的是：所述充分六问族及零或一问情形之外的完整逐 $n$ 函数；每个固定短纤维的完整时间表判据；三个长度阈值的最小性；一般已知数量纤维的最小重置工作及完整资源权衡；随机或带噪访问、无同源重置的访问、存储和算术成本、其它操作以及精确来源或树的恢复。本节给出普通数学证明，不作 Lean 核验、经验测量、研究原创性、RH 或全局 Robin 结论。$\square$

## 129. 素数种子推论的追加证明修正

**命题 129.1（保留推论 6.4 结论的正确证明）。** 原推论 6.4 中“相邻下标都大于 3 则其中一个被 3 整除”的句子不成立，$7,8$ 就是反例。该句及其所给排除理由不应继续作为证明使用；推论的准确有序正权重结论仍为

$$
(u,v)=(2,3)\quad\text{或}\quad(3,5).
$$

证明。定理 6.3 已将整数无损的正有序权重准确分类为 $(u,v)=(F_j,F_{j+1})$、$j\ge1$。不改这一定理，只需重新判断相邻两项何时都可能为素数。

相邻两个下标恰有一个偶数。Fibonacci 加法式

$$
F_{r+t}=F_{r-1}F_t+F_rF_{t+1}\qquad(r\ge1,t\ge0)
$$

在 $t=0,1$ 时由定义成立，其两边按 $t$ 满足同一递推，故归纳成立。取 $t=r$ 得

$$
F_{2r}=F_r(F_{r-1}+F_{r+1}).
$$

若偶下标 $2r\ge6$，则 $r\ge3$，第一因子 $F_r\ge2$，第二因子 $F_{r-1}+F_{r+1}\ge F_2+F_4=4$，所以该 Fibonacci 数合成。偶下标 2 给 $F_2=1$，不是素数。因而两项都为素数时，偶下标只能为 4，邻接下标对只能是 $(3,4)$ 或 $(4,5)$，得到 $(2,3)$ 或 $(3,5)$。低下标 $j=1,2$ 的对含 1，不能另给素数对；即使把下标零列作边界，$F_0=0$ 也非素数。

反向，这两对的元素都是素数，而且定理 6.3 给其无损性；也可直接代入 $u^2+uv-v^2$，分别为 $1,-1$。所以原分类及随后按数值最小选择 $(2,3)$ 的结论均不变，只以此偶下标论证替换旧的错误排除步骤，旧正文保留供明确指认。

§§120—122、126—128 的取得证明把 $q=(2,3)$ 作为指定观察，所需来源桥是 §5.4 的显式矩阵逆及定理 117.3 的实际区间；其局部分类、连续时域与查询上下界都没有使用推论 6.4 的错误句子，也不依赖由素数种子分类来重新选择 $q$。本修正不改变这些取得结论的前提。$\square$

## 追加锚（本行以下为增补区）
## 130. 固定实际接枝的操作闭包与可观察理想

### 130.1. 实际来源、同名词与自主状态

**定义 130.1（固定接枝的受控行为）。** 本节及 §131 的自然数包含零。固定整数 $H\ge1$ 和一个实际接枝组成 $w=(w_1,w_2)\in\mathbb N^2$，每个初始来源都是完整实际组成 $v=(a,b)\in\mathbb N^2$。沿用定理 3.4、4.2、5.4 的

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
q=(2,3),\qquad R(v)=Mv,\qquad G_w(v)=v+w.
$$

允许任意有限操作词，包括空词；书写 $R^k,G_w^A,R^j$ 时按从左到右的时间顺序执行。当前读出为 $o_H(v)=\gcd(qv,H)$，其中 $\gcd(0,H)=H$。定义

$$
v\sim_{H,w}v'
\quad\Longleftrightarrow\quad
 o_H(W(v))=o_H(W(v'))\quad\text{对每个相同的有限词 }W.
$$

每个前缀本身也是合法词，所以该等价覆盖每个可能前缀的当前读出；它没有赋予一次取得查询免费的中间观察。这里没有固定窗口相位、字面 End 或 Zeckendorf 前缀条件。

自主表示是映射 $E:\mathbb N^2\to S$，配备确定更新 $\delta_R,\delta_G$ 及当前解码器 $o$，满足

$$
E(Rv)=\delta_R(Ev),\qquad E(G_wv)=\delta_G(Ev),\qquad
o(Ev)=\gcd(qv,H).
$$

最小化的是允许任意实际来源初始化时的 $|\operatorname{im}E|$，而不是从一个指定来源可达的状态数。令

$$
C=\begin{pmatrix}2&3\\3&5\end{pmatrix}=M^4,\qquad
x=Cv=(n,z),\qquad
C^{-1}=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}.
$$

这里 $\det C=1$，$\det M=-1$。观察坐标上的两个命名操作分别为 $x\mapsto Mx=(z,n+z)$ 和 $x\mapsto x+Cw$，并记 $n_k=(M^kx)_1=qM^kv$，$k\ge0$。所有模 $H$ 组成对都有实际非负代表；所有模 $H$ 观察对也都有实际代表：先在剩余环中应用 $C^{-1}$，再取两组成坐标的非负代表。这个选取不在实际来源上执行减法。

### 130.2. 正向词实现全部可观察平移

**定理 130.2（仿射闭包与接枝理想）。** 设 $H>1$，记 $A_H=\mathbb Z/H\mathbb Z$、$d=\gcd(w_1,w_2,H)$ 及

$$
L_w=A_Hw+A_HMw.
$$

全部合法词在模 $H$ 上的变换恰为 $v\mapsto M^kv+t$，其中 $k\ge0$、$t\in L_w$，且

$$
q(L_w)=dA_H.
$$

因此

$$
v\sim_{H,w}v'
\quad\Longleftrightarrow\quad
\gcd(qM^kv+db,H)=\gcd(qM^kv'+db,H)
\quad(k\ge0,\ b\in\mathbb Z).
$$

证明。逐字归纳给出实际整数等式 $W(v)=M^kv+t_W$：空词取 $k=0,t_W=0$，追加 $R$ 把 $t_W$ 变为 $Mt_W$，追加 $G_w$ 把它变为 $t_W+w$。$t_W$ 只依赖选定的词。由 $M^2=M+I$，所有 $M^jw$ 都在 $L_w$ 中；$M^{-1}=M-I$ 还表明该子模在逆矩阵下稳定，此处只是剩余环中的代数事实。

取正整数 $L=(H^2)!$。矩阵 $M$ 置换 $H^2$ 个剩余对，每个循环的长度都整除 $L$，故 $M^L=I\pmod H$。对非负整数 $A,B$，实际词

$$
R^k,\ G_w^A,\ R^{L-1},\ G_w^B,\ R
$$

的整数终态是

$$
M^{k+L}v+A M^Lw+B Mw,
$$

模 $H$ 为 $M^kv+Aw+BMw$。令 $A,B$ 分别取所需系数在 $0,\ldots,H-1$ 中的代表，便实现每个 $t\in L_w$。实际中间向量始终非负；没有执行逆替换或负次接枝。

置 $a_w=qw=2w_1+3w_2$、$b_w=qMw=3w_1+5w_2$。定理 5.4 的逆式给

$$
w_1=5a_w-3b_w,\qquad w_2=-3a_w+2b_w,
$$

所以 $\gcd(a_w,b_w,H)=d$，其生成的剩余理想正是 $dA_H$。更具体地，取整数 $\lambda,\mu,\nu$ 使

$$
\lambda a_w+\mu b_w+\nu H=d.
$$

需要平移 $db$ 时，用 $A=\lambda b\bmod H$、$B=\mu b\bmod H$ 的非负代表代入上述词，其终端数量就是 $qM^kv+db\pmod H$。当 $d=H$ 时所需可观察平移全为零，可直接省去接枝。这样既证明每个词属于所列测试族，也给每个测试一个作用于同一实际来源的合法词；对两个来源使用的是同一个词。所有前缀仍满足同样的仿射形式，故不留前缀缺口。$\square$

**命题 130.3（理想参数的准确含义）。** 固定 $H$，行为等价关系及其容量仅通过 $d$ 依赖接枝 $w$。这不要求 $L_w=A_H^2$，不意味着不同 $d$ 必给不同划分，也不把相同 $d$ 的不同接枝的同名 $G_w$ 转移等同。

证明。划分的断言直接由定理 130.2 的双向测试式得到。模 11 取 $w=(1,4)$，有 $Mw=(4,5)=4w$，故 $L_w$ 只有一个维度，而 $qw=14$ 为单位，$d=1$，仍得到全部标量平移。另一方面，模 3 的 $w=\alpha=(1,0)$ 与 $w=\beta=(0,1)$ 均有 $d=1$，但在实际来源零上，一个同名接枝词分别给 $\gcd(2,3)=1$ 与 $\gcd(3,3)=3$。故划分相同不蕴含该词输出相同。不同 $d$ 产生相同划分的二进例子见定理 131.4。$\square$

### 130.3. 平移可见的准确局部标量

**定理 130.4（局部平移观察与全步来源关系）。** 对 $p^h\parallel H$ 置 $e=\nu_p(d)$，$0\le e\le h$。模 $p^h$ 的截断深度记为 $\nu_{p,h}(X)$，零剩余取 $h$。定义带类型的标签

$$
\psi_e(X)=
\begin{cases}
\mathsf{Low}(r),&r=\nu_{p,h}(X)<e,\\
\mathsf{Exact}(X\bmod p^h),&p^e\mid X.
\end{cases}
$$

则

$$
\gcd(X+p^eb,p^h)=\gcd(Y+p^eb,p^h)\quad\text{对全部 }b\in\mathbb Z
\quad\Longleftrightarrow\quad \psi_e(X)=\psi_e(Y).
$$

全局的 $v\sim_{H,w}v'$ 当且仅当在每个 $p^h\parallel H$ 上，对全部 $k\ge0$ 都有 $\psi_e(n_k)=\psi_e(n_k')$。

证明。低于 $e$ 的深度不被 $p^e$ 倍数平移改变，故相同低深度充分；不同低深度以及低、高两类已经被 $b=0$ 分开。高类中相同剩余当然充分。若高类剩余 $X\ne Y$，选 $p^eb=-X\pmod {p^h}$，两次读出的指数分别为 $h$ 与严格小于 $h$ 的 $\nu_{p,h}(Y-X)$，证明必要性。这也包含 $e=0$ 的全剩余标签和 $e=h$ 时仅零剩余属于高类的情形。

写 $d=p^e t$，其中 $p\nmid t$。$e<h$ 时，任何局部平移 $p^e\beta$ 都可由整数 $b$ 满足 $tb=\beta\pmod {p^{h-e}}$ 得到，再由定理 130.2 实现为一个全局词；$e=h$ 时只需零平移。如果某局部测试不同，这个素因子的指数不同已使两个完整 gcd 不同，无须控制其余素因子。反向每个合法词在各轴上都是这样的平移测试，逐轴相同便给全局相同。$\square$

这里低标签只留深度，不留旧 §100.3 的低单位部分。§§100.4–100.7 讨论的是允许任意正标量乘法的标量任务，其乘法能把低单位信息提升到可见精度；本节来源操作的线性部只有 $M^k$。§100.9 的命题 100.10 提供有限行为细化的一般原理，但其标量生成元断言也没有改变本节操作库。以下直接证明来源上的分类及实际像，不借用那些标量容量。

### 130.4. 原始原子及实际 Fibonacci 块的分离词

**定理 130.5（原子接枝的完整组成商）。** 若 $w=\alpha$，或 $w=c(T_j)=M^j\alpha$、$j\ge0$，则

$$
v\sim_{H,w}v'\quad\Longleftrightarrow\quad v=v'\pmod H,
$$

允许任意实际初始化的最小自主状态数为 $H^2$。对任何不同的组成剩余，都有一个有限正向共同词将它们分开。

证明。所有操作与 gcd 读出都因子化经过组成模 $H$，给出充分性。若剩余不同，$C$ 可逆使 $qv$、$qMv$ 至少有一个与另一来源不同。选 $k\in\{0,1\}$ 对应该坐标，令 $c=-qM^kv\pmod H$。

对 $\alpha$，取 $c$ 在 $0,\ldots,H-1$ 的代表，令 $A=-c\bmod H$、$B=c$，使用定理 130.2 的词。因为 $M\alpha=\beta$，其数量平移为 $2A+3B=c\pmod H$。第一来源的终端 gcd 为 $H$，第二来源的终端数量与之相差非零剩余 $qM^k(v'-v)$，故 gcd 是 $H$ 的真因子。词长为 $L+k+A+B\le L+2(H-1)+1$；这是有限存在界。

对实际块，$c(T_0)=(1,0)$，且 $j\ge1$ 时 $c(T_j)=(F_{j-1},F_j)$。列矩阵 $[c(T_j),Mc(T_j)]=M^j$ 的行列式为 $(-1)^j$，所以两组成坐标不可能被同一个素数整除，$d=1$。等价地，$q(T_j)=F_{j+3}$ 与 $q(MT_j)=F_{j+4}$ 是互素的相邻 Fibonacci 数；其互素性由递推作 Euclid 消去得到。用它们的 Bézout 系数在定理 130.2 中实现同一个平移 $c$，便得分离词。这里不要求任一个数量或 $F_j$ 单独是模 $H$ 的单位，也不把块 $T_j$ 替换成其索引 $j$ 或一个纯标量加数。

全部 $H^2$ 组成剩余由 $0\le a,b<H$ 的实际来源实现。机器若合并两个不同剩余，相同状态执行刚给出的相同词便应给相同输出，矛盾。记录组成剩余，按 $M$ 与 $+w$ 更新并解码 gcd，达到下界。$H=1$ 时直接是一态，无需构造区分词。$\square$

## 131. 任意固定接枝的局部分类、联合实际像与准确容量

### 131.1. 射影秩及三个局部类型

**定义 131.1（秩、命中与保留精度）。** 固定素数 $p$、指数 $h\ge1$ 和 $0\le e\le h$。本节的 $e$ 是接枝理想指数，$h$ 才是模数指数。沿用定理 120.3–120.4 的局部环射影点：$\mathbb P^1(\mathbb Z/p^j\mathbb Z)$ 是至少一坐标为单位的二元组模共同单位倍数。令

$$
\begin{gathered}
F_0=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,\\
r_j=\min\{r\ge1:p^j\mid F_r\},\qquad
O_j=\{M^t[1:0]:t\in\mathbb Z\},\qquad
c_j=\nu_p(F_{r_j}),\\
\chi_p=\mathbf1_{\{r_1<p+1\}}.
\end{gathered}
$$

$r_j$ 是 $O_j$ 的长度，也是此矩阵的射影阶，不必是矩阵周期。$F_1=F_2=1$，所以 $r_j\ge3$，$c_j$ 是有限整数且 $c_j\ge j$。这些事实及 $r_{j+1}/r_j\in\{1,p\}$ 正是定理 120.3–120.4 对这个 $M$、本原二元组及所有素数的结论；特别不排除 $p=2$ 或轨道提升停滞。令 $\varphi$ 表示 Euler 函数，约定 $\varphi(1)=1$。

对 $x=(n,z)\bmod p^h$，若两坐标均被 $p^e$ 整除，定义标签 $\mathsf{High}(x)$，保留完整二元组，包括零对。否则令

$$
s=\min\{\nu_{p,h}(n),\nu_{p,h}(z)\}<e,\qquad m=e-s,\qquad u=x/p^s.
$$

$u$ 定义在模 $p^{h-s}$ 上且为本原对，往下约化到每个所用精度。若 $[u\bmod p^m]\notin O_m$，令

$$
j=\max\bigl(\{0\}\cup\{i:1\le i<m,\ [u\bmod p^i]\in O_i\}\bigr).
$$

标签为 $\mathsf{NoHit}(s,j,P)$，其中 $j\ge1$ 时 $P=[u\bmod p^j]$，$j=0$ 时 $P=*$。

若 $[u\bmod p^m]\in O_m$，令 $t$ 为 $0,\ldots,r_m-1$ 中唯一满足 $(M^tu)_1=0\pmod {p^m}$ 的整数，写

$$
(A,B)=M^t x\pmod {p^h},\qquad
\ell=\max(h-s-c_m,0),\qquad U=(B/p^s)\bmod p^\ell.
$$

标签为 $\mathsf{Hit}(s,t,A,U)$。这里 $p^e\mid A$、$\nu_{p,h}(B)=s$；$\ell>0$ 时 $U$ 为单位类，$\ell=0$ 时取模一的唯一类。除法先在模 $p^{h-s}$ 上定义再约化，不给零向量赋射影方向。

**定理 131.2（局部标签的充分必要性）。** 两个模 $p^h$ 观察对有相同的全部 $\psi_e((M^kx)_1)$、$k\ge0$，当且仅当定义 131.1 的标签相同。

证明。高类型的全部时刻都被 $p^e$ 整除，所以 $\psi_e$ 保留其完整剩余；时刻 $0,1$ 已给 $n,z$，故必须且只须完整二元组相同。若至少一对是低类型，前两读数的深度之最小值识别低含量 $s<e$，也将它与高类型区分。

对于含量 $s$ 的低对，第一坐标读出在时刻 $k$ 的唯一射影核是

$$
M^{-k}[0:1]=M^{1-k}[1:0].
$$

于是对 $1\le i\le h-s$，

$$
p^{s+i}\mid (M^kx)_1
\quad\Longleftrightarrow\quad
[u\bmod p^i]=M^{1-k}[1:0]\quad\text{在模 }p^i\text{ 上}.
$$

这是定理 120.3 的核线在当前读出时刻 $k\ge0$ 的写法；不能把该定理的正时刻编号不作转换地套用。因为 $k\ge0$ 遍历每个有限循环，核线恰遍历 $O_i$。约化把高层轨道送入低层，命中层构成初段。

无命中类型从不达到深度 $e$。其最高命中层 $j<m$ 与该层方向 $P$ 决定全部较低层整除测试，更高层全不发生，故决定全部低标量标签。反向，全部时刻中最大的深度恰为 $s+j$：若 $j>0$，该层核线有一个非负时刻实际命中；若 $j=0$，所有深度均为 $s$。故观察可恢复 $j$，再选一个最高命中时刻恢复该时刻唯一核线 $P$。同层不同方向在此时刻分开。这包含首层就在轨道外的所有方向合并为一个 $j=0$ 标签，并非丢弃一个更高的已命中层。

命中类型在模 $p^m$ 的轨道长为 $r_m$，故有且仅有上述相位 $t$，所有深度至少 $e$ 的非负时刻恰为

$$
k=t+jr_m,\qquad j\ge0.
$$

将相位约化到较低层，得到所有未命中时刻低于 $e$ 的深度；这些深度只依赖 $s,t$。矩阵可逆，保持两坐标生成的局部理想，故在第一次命中处 $A$ 被 $p^e$ 整除而 $B$ 深度恰为 $s$。

置 $r=r_m$、$a=F_{r-1}$、$f=F_r$。定理 120.3 中的恒等式给

$$
M^r=aI+fM,\qquad p\nmid a,\qquad \nu_p(f)=c_m.
$$

前两次命中读数是 $A$ 与 $aA+fB$，均由 $\psi_e$ 完整保留。固定 $A$ 后，第二个数相同当且仅当

$$
f(B-B')=0\pmod {p^h}
\quad\Longleftrightarrow\quad
B/p^s=B'/p^s\pmod {p^{\max(h-s-c_m,0)}}.
$$

当 $c_m+s\ge h$ 时这个约束为空，正是 $\ell=0$；没有假设 $c_m=m$。

这两个命中读数也足够。令 $N=M^r$，由二阶特征恒等式

$$
N^2-\operatorname{tr}(N)N+\det(N)I=0
$$

得序列 $(N^j(A,B))_1$ 满足同一二阶递推。前两项相同便使所有 $j\ge0$ 相同。因 $0\le t<r$，这些已经是全部非负命中时刻，无需任何实际逆操作。加上由 $s,t$ 决定的低时刻读数，证明命中标签的充分性。

必要性也给具体分离位置。命中与无命中在一个命中时刻分开；不同相位在一方命中而另一方未命中时分开。同一 $s,t$ 下，不同 $A$ 在 $k=t$ 给不同高标量；相同 $A$ 而不同 $U$ 在 $k=t+r_m$ 给不同高标量。高类型不同二元组在 $k=0$ 或 $1$ 给不同高标量。这些高标量若原 gcd 尚未分开，用定理 130.4 的抵消平移即可分开。至此所有标签分量均必要。$\square$

### 131.2. 每个标签的实际实现与精确乘积

**定理 131.3（固定接枝的准确最小状态数）。** 定义

$$
N_p(m)=\chi_p+\sum_{j=1}^{m-1}r_j\mathbf1_{\{r_{j+1}=r_j\}}\qquad(m\ge1),
$$

空和为零。局部全部实际标签数为

$$
K_{p,h}(e)=p^{2(h-e)}+
\sum_{s=0}^{e-1}\left[
N_p(e-s)+r_{e-s}p^{h-e}
\varphi\!\left(p^{\max(h-s-c_{e-s},0)}\right)
\right].
$$

固定 $w$ 的全局行为类及最小自主状态数恰为

$$
K_H(d)=\prod_{p^h\parallel H}K_{p,h}(\nu_p(d)),\qquad
 d=\gcd(w_1,w_2,H).
$$

$H=1$ 的空积取 1。乘积是一个实际来源的联合像，并且不同类有一个全局共同分离词。

证明。高类型有 $p^{2(h-e)}$ 对。固定低含量 $s$ 并置 $m=e-s$。定理 120.4 已证明每个射影点恰有 $p$ 个下一层提升，轨道约化的纤维数为 $r_{j+1}/r_j\in\{1,p\}$。若首层不在轨道，只留下一个无命中标签，它存在恰在 $\chi_p=1$ 时。若第一次退出发生在 $j$ 到 $j+1$，只能是秩停滞：每个轨道父点有一个轨道子点和 $p-1$ 个遗漏子点，全部遗漏子点及其后代共用该父点的一个标签，贡献 $r_j$。满 $p$ 倍提升则无遗漏子点。故无命中类数正是 $N_p(m)$。选一个轨道外点，或选一个相应停滞处的遗漏子点并继续提升，就实现每个计入的标签；退出后不能重返轨道，因为高层轨道必约化到低层轨道。这一计数保留每个实际停滞，包括二进异常及 $p=5$ 的情形，不使用一般位置假设。

命中类型有 $r_m$ 个相位。固定相位和含量，$A$ 可为任意模 $p^h$ 的 $p^e$ 倍数，共 $p^{h-e}$ 个；$U$ 可为模 $p^\ell$ 的任意单位，共 $\varphi(p^\ell)$ 个，$\ell=0$ 时为一。这两个选择确实独立且能实现：将 $U$ 提升为模 $p^{h-s}$ 的单位 $b$（模一时可取 $b=1$），令 $B=p^sb$，取任意上述 $A$，在剩余环内置

$$
x=M^{-t}(A,B).
$$

所得对的含量为 $s$，且 $M^t(x/p^s)$ 在模 $p^m$ 上方向为 $[0:1]$，故第一次非负命中相位就是选定的 $t$。所有逆矩阵只用于选初始剩余，实际执行仍只用正向词。无命中类同样可先选本原方向，再乘 $p^s$；高类任意选相应坐标。因此局部公式数的是恰好实际出现的类。

对于每根素数幂轴任意选一个标签及刚构造的代表 $x_p$，CRT 给一个共同 $x\bmod H$。先应用 $C^{-1}\pmod H$，再取非负组成代表，便得一个实际 $v\in\mathbb N^2$ 同时实现全部局部选择。这证明联合像为所列乘积，未将不同来源的边缘标签冒充联合。

等标签由定理 131.2、130.4、130.2 给每个共同词输出相同。不同标签时，选一根不同的轴：不同含量在 $k=0,1$ 之一分开；无命中的不同深度或方向用对应层的核时刻分开；不同命中状态或相位用一方的命中时刻分开。这些情形在原始深度上已经不同，只用 $R^k$ 即可。其余情形使用定理 131.2 指定的 $k=0,1,t$ 或 $t+r_m$，得到两个不同而都被 $p^e$ 整除的高标量。解

$$
db=-n_k\pmod {p^h}
$$

并用定理 130.2 的 Bézout 词实现此全局平移，第一读数的 $p$ 指数成为 $h$，第二严格较小。其余轴无需同步区分；同一个实际词已经使完整 gcd 不同。

最后，行为等价在前接同一个生成操作后仍成立，因为随后任何词与此前操作合成另一个合法词。因此两个命名更新和当前读出在行为类上良定义。可为每个标签固定一个组成剩余代表，施加 $M$ 或 $+w$ 后重新编码；结果与代表的选择无关。所得商机器达到上述类数。任意机器若合并两个不同类，则在共同分离词后应给同一输出，矛盾，故这是准确最小值。$\square$

### 131.3. 完整组成恢复的边界与退化

**定理 131.4（完整组成商的充要条件）。** 行为等价恰为组成模 $H$ 相等，当且仅当

$$
d=1\qquad\text{或}\qquad \bigl(\nu_2(H)=1\ \text{且}\ d=2\bigr).
$$

证明。局部 $e=0$ 时所有对都是完整高标签。若 $p^h=2$ 且 $e=1$，虽无有效平移，$\gcd(X,2)$ 本身已区分标量剩余 0、1，前两次当前读数就区分所有 $(n,z)\bmod2$。这些轴组合时，CRT 给完整组成恢复。

其余每根 $e>0$ 的轴都有实际可提升的碰撞。若 $h\ge2$，在观察坐标取

$$
x=(0,1),\qquad x'=(0,1+p^{h-1})\pmod {p^h}.
$$

两对不同且互为单位倍数。每个时刻 $n_k'=(1+p^{h-1})n_k$；低于 $e$ 的深度保持，高于或等于 $e\ge1$ 时差 $p^{h-1}n_k$ 为零模 $p^h$，包括 $n_k=0$。故每个 $\psi_e$ 都相同。若 $h=1$ 且 $p$ 为奇素数，$e=1$，取 $(0,1)$、$(0,2)$，同样是不同单位倍数，所有时刻零与非零的模式相同，全部平移又为零。唯一未覆盖的 $e>0$ 轴正是前述模 2。

在其余轴取相同剩余，用 CRT、$C^{-1}$ 及非负代表实现这两个局部碰撞为两个实际全局来源；它们组成剩余不同但每个共同词输出相同。因此任何坏轴都严格阻止完整恢复。允许的指数格局恰为陈述中的两种。$H=1$ 时 $d=1$，普遍等价正是模一相等。$\square$

整数接枝非本原并不自动损失模信息：其共同因子若与 $H$ 互素，仍有 $d=1$。模 2 时 $d=1$ 与 $d=2$ 都给完整四态，这也证明参数 $d$ 不必由划分反向唯一确定。

**命题 131.5（无有效接枝端点、读出时刻桥与 5040）。** 若 $d=H$，固定接枝对剩余的作用为恒等，局部公式化为定理 120.4 的

$$
K_{p,h}(h)=1+\sum_{m=1}^{h}\bigl[N_p(m)+r_m\bigr]=G_p(h).
$$

它与定理 120.10 的下一数量读出机器有相同的行为划分，但当前解码器须经过下述时刻转换。$H=5040$ 时，无有效接枝的最小值为 $42840$；接枝 $\alpha$ 或任意实际 $T_j$ 的最小值为 $25401600$。

证明。$d=H$ 当且仅当 $w=0\pmod H$，包含实际 $w=0$。公式中 $e=h$，高项为 1，$m=h-s$，且 $c_m\ge m$ 使 $\ell=0$，遂得所列 $G_p(h)$。为准确连接读出，置

$$
o_0(v)=\gcd(qv,H),\qquad o_1(v)=\gcd(qMv,H).
$$

$H>1$ 时取定理 130.2 的正矩阵周期 $L$，则对 $k\ge0$

$$
o_1(R^kv)=o_0(R^{k+1}v),\qquad
o_0(R^kv)=o_1(R^{k+L-1}v).
$$

两指数都非负，且一直使用相同实际来源。更一般地，对任意混合词 $W$，将 $R$ 或 $R^{L-1}$ 追加在 $W$ 的末尾给同样的双向读出桥；没有把替换穿过接枝。故两个全词行为划分相同，解码器本身仍相差一个替换更新。$H=1$ 则两读出恒为 1。

定理 120.5、120.10 对同一个 $M$ 及全体实际联合来源已给

$$
G_2(4)=40,\quad G_3(2)=17,\quad G_5(1)=7,\quad G_7(1)=9.
$$

特别二进本原类数为 $3,6,12,18$，保留模 4 到模 8 的停滞。上述桥允许直接复用乘积 $40\cdot17\cdot7\cdot9=42840$。而原子及实际块有 $d=1$，定理 130.5 给 $5040^2=25401600$。因为 $\nu_2(5040)=4$，定理 131.4 的二进例外不适用：全 $25401600$ 态恰在 $d=1$ 时必需。

一般 $e=0$ 时低项为空，$K_{p,h}(0)=p^{2h}$；$H=1$ 时无任何轴，恒为一态。零剩余类可含许多非零实际来源，不能认作唯一整数零来源。实际零在 $R$ 下保持零，接枝后可以离开零；与它模 $H$ 同余的任意来源仍在每个共同词后与它同余。因此这些端点不要求排除结构零。$\square$

### 131.4. 固定数量只是初始化限制

**命题 131.6（实际数量纤维上的初始行为容量）。** 若外部固定确切 $n$，实际来源由定理 5.4 的逆式一一对应于

$$
I_n=\left[\left\lceil\frac{3n}{2}\right\rceil,
\left\lfloor\frac{5n}{3}\right\rfloor\right]\cap\mathbb Z,
\qquad
L_n=\max\left(0,\left\lfloor\frac{5n}{3}\right\rfloor-
\left\lceil\frac{3n}{2}\right\rceil+1\right).
$$

初始化限于该纤维而随后允许任意词时，接枝 $\alpha$ 或 $T_j$ 的初始行为数是 $\min(L_n,H)$；一般 $w$ 的准确初始行为数是 $I_n\ni z\mapsto$ 定义 131.1 的全局乘积标签（作用于 $(n,z)$）的实际像大小。

证明。$a=5n-3z$、$b=2z-3n$ 的非负性恰给该区间，与定义 120.1 的实际支持相同。对原子或块，定理 130.5 表明行为相同恰为组成剩余相同；固定 $n$ 后，经 $C$ 等价于 $z=z'\pmod H$。连续的 $L_n$ 个整数恰占 $\min(L_n,H)$ 个剩余，故得公式。一般接枝直接用定理 131.2–131.3 的必要充分分类限制到该区间；短区间不能由局部标签分别非空推出联合占用，也不能直接乘不受限的局部类数。

$n=0$ 有唯一实际来源，初始容量为 1；$n=1$ 的区间为空，容量为 0，不用有向组成的单位填充它。固定 $n$ 的切片一般不在 $R$ 或非零接枝下封闭，因此这个初始或辅助记录容量不定义切片上的自主机器。全域自主机器仍有定理 131.3 的状态数；§120 的固定数量 gcd 全未来任务与 §100 的标量乘法任务也各保留自己的操作和目标。$\square$

## 132. 素数幂上完整赋值查询的自适应下界

### 132.1. 仿射查询与单点支撑

**定义 132.1（完整局部赋值识别）。** 本节固定素数 $p$、整数 $e,d\ge1$，记 $P=p^e$、$X=(\mathbb Z/P\mathbb Z)^d$；这里 $d$ 表示维数，与 §§130–131 的接枝理想参数无关。对整数或模 $P$ 剩余 $a$ 定义

$$
\nu_e(a)=\max\{s\in\{0,\ldots,e\}:p^s\mid a\}.
$$

特别 $\nu_e(0)=e$。一个查询选任意仿射形式 $f(x)=a\mathbin{\cdot}x+c\pmod P$，得到完整 $\nu_e(f(x))$，包括深度 $e$ 的饱和响应。行向量可非本原或为零。目标是识别一个固定未知的完整点 $x\in X$，不是它的某个商。策略确定且自适应，每次选形式或终止答案只能依赖先前的完整响应；每次查询收费一问，考察有限最坏次数。

**引理 132.2（单点支撑的整行列式约束）。** 取 $m\ge0$ 个仿射形式 $f_j(x)=a_j\mathbin{\cdot}x+c_j\pmod P$，以及 $0\le r_j<e$。令 $\zeta$ 为本原 $P$ 次复单位根，并置

$$
b_j=p^{e-r_j-1},\qquad
F(x)=\prod_{j=1}^{m}\bigl(1-\zeta^{b_j f_j(x)}\bigr).
$$

若 $F$ 的非零支撑恰为单点 $\{x_*\}$，且每个 $j$ 满足 $\nu_e(f_j(x_*))=r_j$，则

$$
m\ge de(p-1).
$$

证明。形式和点的代表改变一个 $P$ 倍数不会改变根的幂，故乘积良定义。对每个模 $P$ 单位 $t$，用 $\zeta^t$ 代替 $\zeta$ 定义 $F_t$。因 $t$ 可逆，

$$
1-\zeta^{t b_j f_j(x)}=0
\quad\Longleftrightarrow\quad
p^{r_j+1}\mid f_j(x),
$$

所以每个 $F_t$ 都有完全相同的单点支撑。

现在对乘积作有限字符展开。对于子集 $J\subseteq\{1,\ldots,m\}$，记

$$
a_J=\sum_{j\in J}b_j a_j\pmod P,\qquad
c_J=\sum_{j\in J}b_j c_j\pmod P,
$$

并以 $[c_J]\in\{0,\ldots,P-1\}$ 表示其非负代表。定义一个与 $t$ 无关的整系数多项式

$$
A(T)=\sum_{J:\ a_J=0\bmod P}(-1)^{|J|}T^{[c_J]}\in\mathbb Z[T].
$$

各子集可以给相同指数，正负项也可以抵消，这都只改变整数系数。对展开中第 $J$ 项求和，坐标分离给

$$
\sum_{x\in X}\zeta^{t a_J\cdot x}
=\prod_{i=1}^{d}\sum_{u=0}^{P-1}(\zeta^{t(a_J)_i})^u
=\begin{cases}P^d,&a_J=0\pmod P,\\0,&\text{否则}.\end{cases}
$$

非零频率坐标即使被 $p$ 整除，$\zeta^{t(a_J)_i}$ 仍不等于 1，而其 $P$ 次幂为 1，几何级数遂为零。零频率判据因 $t$ 为单位而不变。因此对每个单位 $t$，同一个 $A$ 满足

$$
P^d A(\zeta^t)=\sum_{x\in X}F_t(x)=F_t(x_*).
$$

由准确深度，在模 $P$ 上可写 $f_j(x_*)=p^{r_j}u_j$，其中 $p\nmid u_j$。令 $\eta=\zeta^{p^{e-1}}$，它是本原 $p$ 次单位根，于是

$$
P^d A(\zeta^t)=\prod_{j=1}^{m}(1-\eta^{t u_j}).\tag{132.1}
$$

右边每一因子都非零，所以每个 $A(\zeta^t)$ 非零。

为取得所需的整数性，直接使用如下显式首一多项式及整矩阵，而不诉诸未证的代数整数断言。置

$$
D=p^{e-1}(p-1),\qquad
\Phi(T)=\sum_{s=0}^{p-1}T^{s p^{e-1}}
=\frac{T^P-1}{T^{P/p}-1}.
$$

$\Phi\in\mathbb Z[T]$ 的次数为 $D$，其 $D$ 个互异根恰为 $\zeta^t$，$t$ 遍历模 $P$ 单位：分母移去的正是指数被 $p$ 整除的 $P$ 次根，余下的是全部本原根。令 $B$ 为自由整数模 $\mathbb Z[T]/(\Phi)$ 在基 $1,T,\ldots,T^{D-1}$ 中的乘 $T$ 矩阵，即整系数伴随矩阵。首一性保证约化的系数仍为整数，故 $B$ 与 $A(B)$ 都是整数矩阵。

在复数上，对上述互异根求值给一个可逆线性映射：若次数小于 $D$ 的多项式在 $D$ 个互异点都为零，它必是零多项式。因此该求值矩阵可逆，并把乘 $T$ 的 $B$ 共轭为以所有 $\zeta^t$ 为对角元的矩阵。于是

$$
\det A(B)=\prod_{t\in(\mathbb Z/P\mathbb Z)^\times} A(\zeta^t)
\in\mathbb Z\setminus\{0\}.
$$

这里既不需要 $\Phi$ 的不可约性，也不需要对环中单位差作假设。

每个非零模 $p$ 剩余有 $p^{e-1}$ 个模 $P$ 单位提升，且乘 $u_j$ 置换这些非零模 $p$ 剩余。又由 $(T^p-1)/(T-1)$ 在 $T=1$ 的值有

$$
\prod_{s=1}^{p-1}(1-\eta^s)=p.
$$

故对每个 $j$，

$$
\prod_{t\in(\mathbb Z/P\mathbb Z)^\times}(1-\eta^{t u_j})
=p^{p^{e-1}}.
$$

将式 (132.1) 对全部 $D$ 个单位 $t$ 相乘，得到准确整数等式

$$
p^{edD}\det A(B)=p^{m p^{e-1}}.\tag{132.2}
$$

左侧行列式为非零整数，故 $m p^{e-1}\ge edD$，即 $m\ge de(p-1)$。

$p=2$ 时 $\eta=-1$，每个叶因子为 2，上述乘积完全适用；$e=1$ 时单位提升数为 1，给 $m\ge d(p-1)$；两者同时成立时 $\Phi=T+1$、$B=[-1]$，仍是同一论证。$m=0$ 时空乘积在全部 $P^d\ge2$ 个点上恒为 1，单点支撑假设不可能成立。对非本原行、零行或常数形式，字符求和及支撑论证均未添加排除条件。$\square$

### 132.2. 最小完整深度与一个固定困难来源

**定理 132.3（任意维仿射完整赋值下界）。** 定义 132.1 的任意确定性自适应识别策略，其最坏查询数至少为 $de(p-1)$。该结论允许全部深度、饱和响应及任意相关的先前查询。

证明。没有有限最坏界的策略不会违反此下界。设策略有有限最坏界 $K$。从非空有限集 $S=X$ 开始；某个历史固定下一个查询形式 $f$ 后，回答

$$
r=\min_{x\in S}\nu_e(f(x)),\qquad
S'=\{x\in S:\nu_e(f(x))=r\}.
$$

最小值总被取到，故 $S'$ 非空。归纳可知 $S$ 恰是产生已发出的全部完整响应的点集，而非二元化响应的候选集。该集合内所有点有相同历史，所以确定策略选择同一个下一形式。

同时维护复值函数，其初始值是处处为 1 的空乘积。如果 $r<e$，加入因子

$$
1-\zeta^{p^{e-r-1}f(x)};
$$

若 $r=e$，不加因子。归纳证明乘积的非零支撑恰为当前 $S$。在 $r<e$ 时，最小性保证当前每个候选的深度至少 $r$；因此在 $S$ 内新因子非零恰在深度等于 $r$ 时，深度大于 $r$（包括饱和）全部被删掉。已经在 $S$ 外的点原乘积为零，不能重返支撑。新因子单独在全域可能保留更浅深度，但这些点并不在当前支撑中。若 $r=e$，所有当前候选均饱和，$S'=S$，所以不加因子准确保持支撑，查询仍收费。无信息的非饱和查询也可加入处处在 $S$ 上非零的因子，仍保持该不变量。

此分支必须在 $K$ 问以内终止。否则到第 $K$ 问后仍有候选实现全部历史，策略在这个候选上会选择第 $K+1$ 问，违反最坏界。正确终止时 $S$ 必为单点 $\{x_*\}$；两个不同存活点若得到同一历史就会得到同一个答案，不能同时恢复完整点。

令 $m$ 为这条分支中非饱和响应数，$T$ 为全部收费查询数。叶乘积具有单点支撑，而且 $x_*$ 属于每个先前候选集，故每个所加因子在 $x_*$ 上的形式深度恰是当时记录的 $r_j$。引理 132.2 的全部条件满足，给

$$
T\ge m\ge de(p-1).
$$

最后选这个 $x_*$ 作为固定未知点。由历史上的确定性归纳，它从第一问起就产生所构造的每个形式和每个完整响应。末端选取只是证明一个困难固定输入存在，实际执行没有更换来源，也没有把不相容的各层或各轴困难分支拼接。$\square$

## 133. 原始原子接枝的准确终端 gcd 取得复杂度

### 133.1. 同源重置、完整目标与实际测试词

**定义 133.1（组成剩余的终端查询成本）。** 固定 $H\ge1$ 和一个未知实际 $v\in\mathbb N^2$，其中包括零。本节只用原始接枝 $G_\alpha(v)=v+(1,0)$ 及 $R(v)=Mv$。每次收费查询从同一个原始 $v$ 重置，选一个有限正向词 $W$，只返回终端的当前读数

$$
\gcd(q(W(v)),H).
$$

空词允许但同样收费；没有免费初始 $n$、$g_0$、前缀、执行中间读数或时间侧信道。下一个词和终止答案仅依赖先前的完整 gcd 响应。确定性策略须对所有实际来源终止并准确输出 $v\bmod H$；等价地输出同一来源的 $(n,z)=(qv,qMv)\bmod H$，再用 $C^{-1}$ 解码。$Q(H)$ 是这些有限最坏成本策略的最小最坏收费次数。本节目标是完整组成剩余，不是 §122 的纯替换 gcd 全未来类，也不是免费给定确切 $n$ 的条件目标。

**命题 133.2（单次标量测试的实际词）。** 对 $H>1$、$k\in\{0,1\}$ 和任意 $c\bmod H$，存在一个对所有实际来源统一有效的有限正向词，其唯一终端响应为

$$
\gcd(qM^kv+c,H).
$$

证明。复用定理 130.2、130.5 的实际构造，而把所有读出集中于词末。取

$$
L=(H^2)!,\qquad 0\le c<H,\qquad
A=(-c\bmod H)\in\{0,\ldots,H-1\},\qquad B=c,
$$

按时间顺序执行

$$
W(k,c):\quad R^k,\ G_\alpha^A,\ R^{L-1},\ G_\alpha^B,\ R.
$$

$M^L=I\pmod H$，其整数终态为 $M^{k+L}v+A M^L\alpha+B M\alpha$，模 $H$ 为 $M^kv+A\alpha+B\beta$。终端数量是 $qM^kv+2A+3B=qM^kv+c\pmod H$，故给所需完整 gcd。这个词有 $L+k$ 次替换及 $A+B$ 次接枝，总长至多 $L+2(H-1)+1$，并只在末端收费观察一次。$A,B$ 可为零且始终非负，所有实际中间组成非负。负号只选择剩余代表；重置、逆矩阵以及中间状态均未提供额外观察。此构造只保证所需的共同方向 $q$ 或 $qM$，没有供应任意局部行向量。$\square$

### 133.2. 全部响应深度下的逐位取得

**引理 133.3（标量的至多 $e(p-1)$ 问取得）。** 对固定未知 $y\bmod p^e$，若一次测试返回 $\nu_e(y+c)$，则仅用平移可在至多 $e(p-1)$ 问内恢复 $y$。

证明。保持前缀不变量 $y=r\pmod {p^s}$、$0\le r<p^s$。初始 $(r,s)=(0,0)$，不含任何免费已知位。若 $s<e$，依次试下一位 $a=0,\ldots,p-2$，选

$$
c=-r-a p^s\pmod {p^e}.
$$

写 $y=r+p^su$，则 $y+c=p^s(u-a)\pmod {p^e}$。响应深度不可能小于 $s$；它等于 $s$ 恰在下一位不是 $a$ 时，属于 $s+1,\ldots,e$ 恰在下一位为 $a$ 时。匹配后作同时更新

$$
(r,s)\longleftarrow(r+a p^s,\ s+1),
$$

右侧两个位置都使用更新前的 $s$。若全部 $p-1$ 个已试位均失败，剩下的位必为 $p-1$，不再查询而作同样的同时更新。每次更新保持前缀不变量，匹配给出的额外高位深度可丢弃而不影响正确性。每层至多 $p-1$ 问，$e$ 层后 $s=e$，取得完整剩余。

$p=2$ 每层只试位 0；最后一层的匹配就是饱和深度 $e$，零剩余也按同一规则处理。深度大于 $s+1$、直到 $e$ 均是合法匹配，不是异常退出。推得最后一个未试位省去的是一次测试，并非免费终端观察。$\square$

**定理 133.4（每个素数幂的准确取得成本）。** 定义 133.1 的契约下，对每个素数 $p$ 和 $e\ge1$，

$$
Q(p^e)=2e(p-1).
$$

证明。上界先以命题 133.2 的 $k=0$ 词及引理 133.3 取得 $n=qv\pmod {p^e}$，再以 $k=1$ 取得 $z=qMv\pmod {p^e}$。每个阶段至多 $e(p-1)$ 问；所有查询都重置到相同 $v$，所以两个所得坐标相容。输出

$$
(a,b)=(5n-3z,-3n+2z)\pmod {p^e}
$$

便是目标组成。这是剩余解码，不是对实际来源执行减法。

对下界，限制实际来源为 $0\le a,b<p^e$ 的全部代表，恰实现 $(\mathbb Z/p^e\mathbb Z)^2$ 的每个不同目标。定理 130.2 的整数词归纳给 $W(v)=M^kv+t_W$，故某历史选定词后的标量是

$$
f(v)=qM^kv+q(t_W)\pmod {p^e}.
$$

完整响应 $p^{\nu_e(f(v))}$ 与完整深度相互确定。允许任意仿射行的定义 132.1 是这个实际词查询类的扩大，仅在下界中作此扩大；定理 132.3 取维数 $d=2$，给每个原策略一个实际固定代表至少需要 $2e(p-1)$ 问。它允许策略使用全部深度和两坐标之间的关联，所以不是只下界化上述逐位策略，也不是将有限域下界乘以位数。上下界相合。$\square$

### 133.3. 一个共同词的 CRT 上界与一根困难轴的下界

**定理 133.5（任意正模数的准确公式）。** 在定义 133.1 的实际来源、同源重置、确定性自适应、仅终端当前 gcd 及完整组成目标下，

$$
Q(1)=0,\qquad
Q(H)=2\max_{p^e\parallel H}e(p-1)\quad(H>1).
$$

证明。设 $H>1$，置 $B_H=\max_{p^e\parallel H}e(p-1)$。先取一个标量阶段，固定共同 $k\in\{0,1\}$，目标为 $y=qM^kv\pmod H$。在每根素数幂轴上运行引理 133.3 的前缀过程。每轮，未完成轴根据此前该轴的响应给出下一平移 $c_p$；已完成轴用已取得的 $y_p$ 给 $c_p=-y_p\pmod {p^e}$，因而其响应是已知饱和。由 CRT 选一个 $c\pmod H$ 满足全部局部平移，然后执行唯一的实际词 $W(k,c)$。

这次完整 gcd 的每个素因子指数正是该轴所请求的完整局部响应。各轴共享同一个 $k$，组合的只有平移，故没有把独立选择的局部行向量假定为可执行。每个未完成轴每轮获得一个测试，其总预算至多 $e(p-1)$，而推得未试位只是本轮后的确定更新，不再占一轮。因此至多 $B_H$ 轮，所有轴都完成，CRT 恢复该标量。先 $k=0$ 后 $k=1$，两阶段同源，再经 $C^{-1}$ 输出组成，给

$$
Q(H)\le2B_H.
$$

下界只选一根轴。任取 $P=p^e\parallel H$，置 $D=H/P$，$\gcd(D,p)=1$。预先固定如下一个实际来源族：

$$
v_x=(D x_1,D x_2),\qquad 0\le x_1,x_2<P.
$$

它包含零且全部非负。两个成员模 $H$ 相等当且仅当 $P\mid x_i-x_i'$ 对两个坐标都成立，所以族内 $P^2$ 个目标互异。所有成员模 $D$ 为零，模 $P$ 则经固定单位 $D$ 实现每个剩余对。这是一次共同实际构造，不是分别选择不相容的局部来源。

某个完整历史选定一个词后，写其整数形式 $W(v)=M^kv+t_W$，则族上的终端数量为

$$
N_x=DqM^kx+q(t_W).
$$

定义已由该词确定的正整数 $d_W=\gcd(q(t_W),D)$。因为 $D$ 与 $P$ 互素，完整响应恰为

$$
\gcd(N_x,H)
=d_W\,p^{\nu_e(DqM^kx+q(t_W))}.\tag{133.1}
$$

$q(t_W)=0$ 时 $d_W=D$，$D=1$ 时 $d_W=1$，局部饱和时右侧局部因子为 $P$，公式均成立。其余素数部分不必等于 1，也可随自适应选词改变；但在选定节点上它们全是已知、与 $x$ 无关的常数。

因此可把原策略在这个族上的每一问准确模拟成 $x\in(\mathbb Z/P\mathbb Z)^2$ 上的完整仿射赋值查询：局部深度和词给定的 $d_W$ 恢复整个模 $H$ 响应，反向完整响应也给局部深度。模拟器据该完整响应选择与原策略相同的后续词。完整组成目标在此族上单射，所以一个成功的原策略也必须识别完整 $x$。定理 132.3 取维数 2，给一个固定 $x_*$ 及实际 $v_{x_*}$，其完整自适应历史至少收费 $2e(p-1)$ 问。

选取达到 $B_H$ 的一根素数幂便得 $Q(H)\ge2B_H$。不需要、也未声称各轴的局部最坏历史能够同时达到。这个单根困难轴的下界与共同 $k$ 的 CRT 上界使用完全相同的契约，故给等式。$H=1$ 时目标只有一个剩余对，不查询即可输出，得 $Q(1)=0$；这不是把空词观察改成免费。$\square$

### 133.4. 素数与 5040 的推论及资源边界

**推论 133.6（准确问数与状态、工作量的区别）。** 对素数 $p$ 有 $Q(p)=2(p-1)$。对 $5040=2^4\cdot3^2\cdot5\cdot7$，

$$
(e(p-1))_{p=2,3,5,7}=(4,4,4,6),\qquad Q(5040)=12.
$$

每个标量阶段可用至多六个实际词取得，而该任务的自主受控行为容量仍是 $5040^2=25401600$。

证明。两问数直接代入定理 133.5。为具体给出共同平移，令四个过程在某轮请求 $c_{16},c_9,c_5,c_7$，则可选

$$
c=945c_{16}+2800c_9+2016c_5+4320c_7\pmod {5040}.
$$

每个系数在自己的模数上为 1，在另外三个模数上为 0：它们分别是 $3\cdot315$、$5\cdot560$、$2\cdot1008$、$6\cdot720$。各阶段使用同一个 $k$，命题 133.2 把这个平移实现为一个完整实际词。上述按 $0,\ldots,p-2$ 次序试位的具体策略在实际 $v=(5,1)$ 上的 $n=13,z=20$ 均为模 7 剩余 6，所以两阶段的模 7 六次测试全失败后才推得末位，各需六轮。这说明该策略的最坏成本确达十二；所有策略的最优下界则来自定理 132.3 及式 (133.1)，不靠这个单一例子。

状态数来自定理 130.5，问数来自定理 133.5。取得后，在观察剩余坐标上命名更新仍为

$$
R:(n,z)\mapsto(z,n+z),\qquad
G_\alpha:(n,z)\mapsto(n+2,z+3),\qquad
o_H(n,z)=\gcd(n,H).
$$

因此十二不是状态数或位数，也不恢复无界精确组成、确切数量、树的次序或括号。相同剩余的实际来源在每个共同词下始终同余，故精确零与所有同余非零来源也不由该目标区分。

对一般 $H>1$，若仍用 $L=(H^2)!$ 的构造，两阶段各至多 $B_H$ 问，每问至多 $L+2(H-1)+1$ 个生成操作。全部查询共至多 $2B_HL+B_H$ 次替换、$4B_H(H-1)$ 次接枝；在 5040 时分别为 $12L+6$ 与 $24(H-1)$。这些只证明执行词有限，不给最短词、最小最大时刻或高效算术结论。实际执行始终使用整数来源，中间组成没有被模代表替代。控制过程只需有限的剩余、前缀、位号、阶段及重复计数器，其大小可依赖 $H,L$；这里不求最优工作空间。重置保留同一个实际来源是查询模型的条件，没有由问数给出保存其无界坐标的统一位界。

§121 的连续首段任务与 §122 的选择正时刻任务只用纯替换，目标是 gcd 全未来类；它们的八/七步及七/六问分别保留其原来的全局或已知数量合同。本节加入实际接枝且要求完整组成剩余，既无免费确切 $n$ 也无免费 $g_0$，这些数字不相互替代。固定 $n$、无重置而持续推进、End 或窗口接口、随机期望成本、噪声、近似恢复，以及最优重置存储和工作空间均不是定理 133.5 的契约。$\square$

## 追加锚（本行以下为增补区）
## 134. 同一实际词的参数化六问构造与三色分隔词库

**约定 134.1（参数、来源与逐词归一化）。** 本节先给统一参数构造，§135 再确定哪些实际行满足参数条件。沿用定义 104.2、104.4、113.1、114.1 及约定 123.1，取 $H=5040$。已知相位 $j\bmod80$，初始标签为 $(\sigma,E)=(1,\mathrm{true})$；未知 $r\bmod H$ 来自该相位任意返回深度上的一个正值实际合法前缀。候选族允许两种初始化 $\varepsilon$，选定来源后，其原始前缀、初始化、深度和整数权重行在全部重置中固定。每个收费查询均重置到此来源，追加至多三个完整字面窗口，再请求规范 End；成功只返回完整 $\gcd(r+C,H)$，或等价的 $H/\gcd(r+C,H)$，所有非法词和不适当 End 共用一个错误符号。空后缀成功且收费；前导、中间 $000$ 消耗位置，末窗 $100$、$010$ 均可规范终止。

每个成功词对应无相邻元素的 $I\subseteq\{1,\ldots,8\}$。按 $(0,1,2),(3,4,5),(6,7,8)$ 分组，位置 0 为零，非空词恰在含 $\max I$ 的整窗后结束；$I=\varnothing$ 是空词。全部允许族仍为约定 123.1 的 55 个成功词和全部恒错尝试。以下十八词只是上界所用子族。一个词始终只有一个系数对和一个物理平移：

$$
(A,B)=\sum_{i\in I}(F_{i-1},F_i),\qquad
C_I=Au+Bv,\qquad n=A+B,\quad s=A+2B.
$$

这里 $(u,v)=w_j$，$n,s$ 与约定 123.1 相同。固定一个全局单位 $h\in(\mathbb Z/H\mathbb Z)^\times$，设对每个相同的实际词有

$$
d_I=hC_I\equiv
(B\bmod16,\ B\bmod9,\ aA+bB\bmod5,\ B+qA\bmod7),
$$

其中

$$
a,b\in\mathbb F_5,\qquad q\in\{0,2\}\subset\mathbb F_7,\qquad
a(a+b)(2a+b)\ne0.
$$

这包含 $hu=0,hv=1\pmod{144}$，并要求局部系数分别来自同一个 $h$ 与同一个实际行；参数可否实现由命题 135.1–135.2 处理。令

$$
x=-hr,\qquad x-d_I=-h(r+C_I),\qquad r=-h^{-1}x\pmod H.
$$

因此原始完整 gcd 正是 $\gcd(x-d_I,H)$。单位只改变用于解释回答和逆解码的坐标，不缩放物理来源、不改变字面词，也不提供独立局部探针。记 $L_5(I)=aA+bB$、$\gamma_q(I)=B+qA$；称后者为颜色。对 $p^{e_p}\parallel H$，置 $D_p(z)=\min(v_p(z),e_p)$，零模 $p^{e_p}$ 时取 $e_p$，四个深度均可从完整 gcd 读出。

**命题 134.2（十八词的共同实现与参数中心）。** 在约定 134.1 下，以下十八个实际词同时可用。$W_k$ 只命名表中 $B=k$ 的指定占用集；它不是任意可选的数值中心。局部中心由同一行的 $(A,B)$ 决定，$\gamma_0,\gamma_2$ 是 $q$ 的两种选择。

| 134.2 实际词 | 占用集 $I$ | 字面窗口（低位在前） | $(A,B)$ | $B\bmod16$ | $B\bmod9$ | $L_5$ | $\gamma_0$ | $\gamma_2$ |
| --- | --- | --- | --- | ---: | ---: | --- | ---: | ---: |
| 134.2 $W_1$ | $\{1\}$ | $[010]$ | $(0,1)$ | 1 | 1 | $b$ | 1 | 1 |
| 134.2 $W_2$ | $\{3\}$ | $[000,100]$ | $(1,2)$ | 2 | 2 | $a+2b$ | 2 | 4 |
| 134.2 $W_3$ | $\{4\}$ | $[000,010]$ | $(2,3)$ | 3 | 3 | $2a+3b$ | 3 | 0 |
| 134.2 $W_4$ | $\{2,4\}$ | $[001,010]$ | $(3,4)$ | 4 | 4 | $3a+4b$ | 4 | 3 |
| 134.2 $W_5$ | $\{5\}$ | $[000,001]$ | $(3,5)$ | 5 | 5 | $3a$ | 5 | 4 |
| 134.2 $W_6$ | $\{1,5\}$ | $[010,001]$ | $(3,6)$ | 6 | 6 | $3a+b$ | 6 | 5 |
| 134.2 $W_7$ | $\{3,5\}$ | $[000,101]$ | $(4,7)$ | 7 | 7 | $4a+2b$ | 0 | 1 |
| 134.2 $W_9$ | $\{2,6\}$ | $[001,000,100]$ | $(6,9)$ | 9 | 0 | $a+4b$ | 2 | 0 |
| 134.2 $W_{12}$ | $\{1,4,6\}$ | $[010,010,100]$ | $(7,12)$ | 12 | 3 | $2a+2b$ | 5 | 5 |
| 134.2 $W_{13}$ | $\{7\}$ | $[000,000,010]$ | $(8,13)$ | 13 | 4 | $3a+3b$ | 6 | 1 |
| 134.2 $W_{14}$ | $\{1,7\}$ | $[010,000,010]$ | $(8,14)$ | 14 | 5 | $3a+4b$ | 0 | 2 |
| 134.2 $W_{15}$ | $\{3,7\}$ | $[000,100,010]$ | $(9,15)$ | 15 | 6 | $4a$ | 1 | 5 |
| 134.2 $W_{19}$ | $\{1,5,7\}$ | $[010,001,010]$ | $(11,19)$ | 3 | 1 | $a+4b$ | 5 | 6 |
| 134.2 $W_{21}$ | $\{1,3,5,7\}$ | $[010,101,010]$ | $(12,21)$ | 5 | 3 | $2a+b$ | 0 | 3 |
| 134.2 $W_{24}$ | $\{1,3,8\}$ | $[010,100,001]$ | $(14,24)$ | 8 | 6 | $4a+4b$ | 3 | 3 |
| 134.2 $W_{30}$ | $\{1,6,8\}$ | $[010,000,101]$ | $(18,30)$ | 14 | 3 | $3a$ | 2 | 3 |
| 134.2 $W_{31}$ | $\{3,6,8\}$ | $[000,100,101]$ | $(19,31)$ | 15 | 4 | $4a+b$ | 3 | 6 |
| 134.2 $W_{32}$ | $\{4,6,8\}$ | $[000,010,101]$ | $(20,32)$ | 0 | 5 | $2b$ | 4 | 2 |

证明。使用约定 123.1 的位置向量

$$
p_1,\ldots,p_8=(0,1),(1,1),(1,2),(2,3),(3,5),(5,8),(8,13),(13,21).
$$

若两个合法占用集之间所有跨距至少为二，其并集仍无相邻元素，系数对就是两集系数对之和。这一分离并集规则作用在一个实际词上，同时给四轴的中心相加。单点 $W_1,W_2,W_3,W_5,W_{13}$ 分别取 $p_1,p_3,p_4,p_5,p_7$；其余基本词为

$$
\begin{aligned}
W_4 &:p_2+p_4=(3,4),&
W_6 &:p_1+p_5=(3,6),\\
W_7 &:p_3+p_5=(4,7),&
W_9 &:p_2+p_6=(6,9),\\
W_{12}&:p_1+p_4+p_6=(7,12).
\end{aligned}
$$

向 $\{1\},\{3\},\{1,5\},\{1,3,5\}$ 分别添加共同尾部 $\{7\}$，即同时加 $(8,13)$，得到 $W_{14},W_{15},W_{19},W_{21}$。这些基集最高位置至多为 5，故全部跨距至少为二。向 $\{1,3\}$ 添加 $\{8\}$，即加 $(13,21)$，得到 $W_{24}=(14,24)$。最后取

$$
K=\{6,8\},\qquad p_6+p_8=(18,29).
$$

$K$ 与 $\{1\},\{3\},\{4\}$ 都分离，故分别产生 $W_{30},W_{31},W_{32}$，系数对是 $(18,30),(19,31),(20,32)$，相邻两对之差为 $(1,1)$。在 $q=2$ 时其颜色依次为 $3,6,2$；$W_{32}$ 的同一 $B=32$ 同时给模 8 的 0 与模 9 的 5。另有 $W_{30}-W_{21}=(6,9)$，其颜色差为 $9+2\cdot6=21=0\pmod7$，但它们仍是两个不同实际词。

上述构造逐项给表中系数，将同一对代入 $B,L_5,\gamma_q$ 得所有局部列。例如 $W_{31}$ 的模 5 中心为 $19a+31b=4a+b$，两种颜色为 $31=3$ 与 $31+2\cdot19=6\pmod7$。这也表明共同尾部的模 5 增量是 $18a+29b$，不随意替换为某个独立中心。

所有列出的集合均不含 0，最高位置不超过 8，内外间距均至少为二；分组后恰为显示的完整窗口。在跨窗位置 2、3 及 5、6 也没有相邻占位，前导、中间零窗照常保留，每个末窗非零，故 End 规范且至多三窗。实际整数平移是若干正 Fibonacci 权重之和，保持原始来源为正。这些性质不依赖其模余数，也不依赖返回深度。$\square$

**命题 134.3（唯一的模 144 复用与参数化前三问）。** 先查询 $W_1,W_2$，仅按第一份回答的 $e=D_2(x-1)$ 选择第三问：$e=1$ 时查询 $W_3$，称甲支；否则查询 $W_{12}$，称乙支。两支模 16 中心依次为 $1,2,3$ 与 $1,2,12$，模 9 中心均为 $1,2,3$。二进、三进的全部分区按命题 124.2 复用一次；其非单点恰为

$$
\begin{aligned}
\text{甲二进}:&\quad \{7,15\},\\
\text{乙二进}:&\quad \{5,13\},\{6,14\},\{0,8\},\\
\text{两支三进}:&\quad \{4,7\},\{5,8\},\{0,6\}.
\end{aligned}
$$

甲支其余二进后验是 $\{3\},\{11\}$；乙支其余二进后验是 $\{1\},\{9\},\{2\},\{10\},\{4\},\{12\}$；三进其余后验是 $\{1\},\{2\},\{3\}$。模 5 的前三中心和全未命中补集 $P_5$ 如下，单次命中即确定对应中心：

$$
\begin{aligned}
T_{5,\mathrm{甲}}&=(b,a+2b,2a+3b),&
P_{5,\mathrm{甲}}&=\{3a+4b,4a\},\\
T_{5,\mathrm{乙}}&=(b,a+2b,2a+2b).
\end{aligned}
$$

全部允许参数恰分为 $b=0,a\ne0$，或 $b\ne0,a=b$，或 $b\ne0,a=3b$。乙支的三种完整补集是

$$
P_{5,\mathrm{乙}}=
\begin{cases}
\{3a,4a\},&b=0,\ a\ne0,\\
\{0,2b\},&a=b,\ b\ne0,\\
\{2b,4b\},&a=3b,\ b\ne0.
\end{cases}
$$

模 7 的三个中心和四色未查询集 $U$ 为：

| 134.3 颜色分支 | 前三中心（依查询顺序） | $U$ |
| --- | --- | --- |
| $q=0$ 甲 | $(1,2,3)$ | $\{0,4,5,6\}$ |
| $q=0$ 乙 | $(1,2,5)$ | $\{0,3,4,6\}$ |
| $q=2$ 甲 | $(1,4,0)$ | $\{2,3,5,6\}$ |
| $q=2$ 乙 | $(1,4,5)$ | $\{0,2,3,6\}$ |

有模 7 命中时该坐标已知；无命中时其后验是 $U$。此后始终以 $U$ 表示未查询颜色，即使此前已有命中。

证明。先明确唯一复用映射：保持占用集 $I$、字面窗口和规范编号 $n$ 原样，把本节 $x\bmod144$ 对应到命题 124.2 的同值归一化坐标。由约定 134.1，每个相同词的中心都为 $B\bmod144$，恰与命题 124.1 相同。因此完整二进、三进深度及第一二进深度分支谓词全部保持，命题 124.2 的分区及其穷尽证明适用。命题 125.1、125.3 是同一映射在相位三上的应用。本节不再次按参数或相位重证这些分区；此映射没有关于模 5、模 7 的结论，下面的两轴均由命题 134.2 重新推导。

令 $\delta=a+b\ne0$。甲支三个模 5 中心为 $b,b+\delta,b+2\delta$，故不同；双射 $t\mapsto b+t\delta$ 的另两值是 $b+3\delta=3a+4b$ 和 $b+4\delta=4a$，恰给甲支补集。乙支的两两差，忽略符号，是 $\delta,2a+b,a$，由假设均非零；所以其三个中心也不同。若 $b=0$，参数条件等价于 $a\ne0$。若 $b\ne0$，置 $t=a/b$，条件排除 $t=0,4,2$。在 $\mathbb F_5^\times$ 上，

$$
t^4-1=(t-1)(t-2)(t-3)(t-4)=0.
$$

消去非零因子即得 $t=1$ 或 $t=3$，反向两值均满足条件。代入乙支中心得到 $\{0,a,2a\}$、$\{b,3b,4b\}$、$\{b,0,3b\}$；乘非零 $a$ 或 $b$ 是域的双射，所列三种补集随之成立。甲支公式在这三类也分别给 $\{3a,4a\}$、$\{2b,4b\}$、$\{3b,2b\}$。每个补集都有两个不同元素；这穷尽模 5 命中及全失配历史。

模 7 中心由 $W_1,W_2,W_3,W_{12}$ 的同一系数对给 $1,2+q,3+2q,5$，其中末项因 $A=7$ 与 $q$ 无关。代入 $q=0,2$ 即得表中互异三元组及各自补集。

联合后验的量词沿用命题 123.3：固定一份可行完整前三问历史后，查询的实际词已经确定，每份 gcd 分别限制四个余数坐标；满足全部局部限制的元组也重现同一第一深度，因而重现同一第三词。共同返回深度的满实际纤维实现每个这样的 CRT 元组，故在整个来源族上后验确为这些局部后验的乘积。固定一个额外指定的小深度或单一初始化时，乘积只需作为包含实际候选的上界集合；本节策略分隔这个更大集合，仍对其中每个实际源有效。源的共同实现没有扩大实际词库。$\square$

**命题 134.4（四个分支的全部二进、三进分配）。** 对命题 134.3 中每个非单点后验，按下表选取实际分隔词；单点不产生需求。二进列的顺序在甲支为 $\{7,15\}$，乙支为 $\{5,13\},\{6,14\},\{0,8\}$；三进列的顺序始终为 $\{4,7\},\{5,8\},\{0,6\}$。词后的括号给该词颜色。

| 134.4 分配分支 | 二进需求对应词（颜色） | 三进需求对应词（颜色） |
| --- | --- | --- |
| $q=0$ 甲 | 134.2 $W_7(0)$ | 134.2 $W_4(4),W_5(5),W_6(6)$ |
| $q=0$ 乙 | 134.2 $W_{13}(6),W_6(6),W_{24}(3)$ | 134.2 $W_4(4),W_{14}(0),W_{24}(3)$ |
| $q=2$ 甲 | 134.2 $W_{15}(5)$ | 134.2 $W_4(3),W_{14}(2),W_{15}(5)$ |
| $q=2$ 乙 | 134.2 $W_{21}(3),W_{30}(3),W_{32}(2)$ | 134.2 $W_{31}(6),W_{32}(2),W_9(0)$ |

对于每一种同时出现的二进、三进后验，省掉单点需求并合并完全相同的词后，留下至多两个实际词，颜色两两不同且都在该支 $U$ 中。允许合并的同时碰撞只有 $W_{24}$、$W_{15}$、$W_{32}$ 本身。

证明。引理 123.4 的局部分隔判据在此直接适用：二进对 $\{z,z+8\}$ 要求 $B\equiv z\pmod8$，三进对要求 $B$ 等于其中一个元素模 9。这是完整截断深度的判据，不能换成仅测试整除的一个布尔值。命题 134.2 的同一 $B$ 给出：

$$
\begin{array}{c|c|c}
(q,\text{支})&\text{二进分隔类 }B\bmod8&\text{三进中心 }B\bmod9\\ \hline
(0,\mathrm{甲})&7&4,5,6\\
(0,\mathrm{乙})&5,6,0&4,5,6\\
(2,\mathrm{甲})&7&4,5,6\\
(2,\mathrm{乙})&5,6,0&4,5,0
\end{array}
$$

所以每项需求都被指定词分隔。颜色也从同一表逐词计算，属于对应 $U$。现证明所有同时情形的异色性，而不对联合历史加额外限制。$q=0$ 甲支二进色集 $\{0\}$ 与三进色集 $\{4,5,6\}$ 不交。$q=0$ 乙支两个色集分别为 $\{6,3\}$ 和 $\{4,0,3\}$，交集只有 3；同时出现色 3 时两项确实都是 $W_{24}$。$q=2$ 甲支两个色集为 $\{5\}$ 和 $\{3,2,5\}$，交集只有 5，双方都是 $W_{15}$。$q=2$ 乙支两个色集为 $\{3,2\}$ 和 $\{6,2,0\}$，交集只有 2，双方都是 $W_{32}$。

三个合并的完整对应分别是：$W_{24}$ 的 $B=24$ 给二进 $\{0,8\}$ 和三进 $\{0,6\}$；$W_{15}$ 的 $B=15$ 给二进 $\{7,15\}$ 和三进 $\{0,6\}$；$W_{32}$ 的 $B=32$ 给二进 $\{0,8\}$ 和三进 $\{5,8\}$。相应有序深度分别为 $((3,4),(1,2))$、$((3,4),(1,2))$、$((4,3),(2,1))$。每项由命题 134.2 中唯一占用集、唯一字面词和唯一系数对实现。

同为 $q=0$ 乙支色 6 的 $W_{13},W_6$ 属于不同且互斥的二进后验；同为 $q=2$ 乙支色 3 的 $W_{21},W_{30}$ 也只在互斥二进后验上使用。它们不会同时成为需求，绝不能以同色为由将两个词合并。每个历史至多一个二进需求、一个三进需求，以上色集交集已经穷尽其全部组合，包括零需求、一需求及合并后只余一词的情形。$\square$

**命题 134.5（每种参数的三色实际分隔词库与四色补词）。** 对命题 134.3 的每个允许参数和分支，存在三个不同颜色组成的 $R\subset U$，每色都有一个实际词，其模 5 中心属于该支 $P_5$。下表完整指定这些词，词、颜色、模 5 中心的各列按同一顺序对应；“全参数”指约定 134.1 的全部允许参数。

| 134.5 分隔词库情形 | 实际词依次为 | $R$ 中对应颜色 | 对应模 5 中心 |
| --- | --- | --- | --- |
| $q=2$ 甲，全参数 | 134.2 $W_{14},W_4,W_{15}$ | $2,3,5$ | $3a+4b,3a+4b,4a$ |
| $q=2$ 乙，$b=0,a\ne0$ | 134.2 $W_{14},W_{30},W_{31}$ | $2,3,6$ | $3a,3a,4a$ |
| $q=2$ 乙，$a=b\ne0$ | 134.2 $W_9,W_{32},W_{19}$ | $0,2,6$ | $0,2b,0$ |
| $q=2$ 乙，$a=3b,b\ne0$ | 134.2 $W_9,W_{32},W_{19}$ | $0,2,6$ | $2b,2b,2b$ |
| $q=0$ 甲，$b=0,a\ne0$ | 134.2 $W_{14},W_4,W_6$ | $0,4,6$ | $3a,3a,3a$ |
| $q=0$ 甲，$a=b\ne0$ | 134.2 $W_{14},W_4,W_6$ | $0,4,6$ | $2b,2b,4b$ |
| $q=0$ 甲，$a=3b,b\ne0$ | 134.2 $W_{14},W_4,W_{13}$ | $0,4,6$ | $3b,3b,2b$ |
| $q=0$ 乙，$b=0,a\ne0$ | 134.2 $W_{14},W_4,W_6$ | $0,4,6$ | $3a,3a,3a$ |
| $q=0$ 乙，$a=b\ne0$ | 134.2 $W_{14},W_{31},W_4$ | $0,3,4$ | $2b,0,2b$ |
| $q=0$ 乙，$a=3b,b\ne0$ | 134.2 $W_7,W_3,W_{13}$ | $0,3,6$ | $4b,4b,2b$ |

此外，每个 $U$ 的全部四色都有下列实际补词；补词只承担所指定颜色，不要求一律分隔模 5。

| 134.5 补词分支 | $U$ 按递增次序 | 对应实际补词 |
| --- | --- | --- |
| $q=0$ 甲 | $0,4,5,6$ | 134.2 $W_7,W_4,W_5,W_6$ |
| $q=0$ 乙 | $0,3,4,6$ | 134.2 $W_{14},W_{24},W_4,W_6$ |
| $q=2$ 甲 | $2,3,5,6$ | 134.2 $W_{14},W_4,W_{15},W_{19}$ |
| $q=2$ 乙 | $0,2,3,6$ | 134.2 $W_9,W_{32},W_{21},W_{19}$ |

证明。每个词的支持和四轴共同实现已经由命题 134.2 给出，只须证明这些特定参数下的中心确实落在相应实际补集中。$q=2$ 甲支的三个中心直接为 $3a+4b,3a+4b,4a$，即甲支补集的元素。$q=2$ 乙支在 $b=0$ 时是 $3a,3a,4a$；在 $b\ne0$ 时同三个词 $W_9,W_{32},W_{19}$ 给 $a+4b,2b,a+4b$。取 $a=b$ 得 $0,2b,0$，取 $a=3b$ 得 $2b,2b,2b$，分别属于 $\{0,2b\}$ 和 $\{2b,4b\}$。不同颜色可以有相同模 5 中心；测试二元对的任一成员就已足够分隔。

$q=0$ 甲支先取 $W_{14},W_4$，其中心同为 $3a+4b$。在 $b=0$ 或 $a=b$ 时，色 6 的 $W_6$ 给 $3a+b$，分别等于 $3a$ 或 $4a$。在 $a=3b,b\ne0$ 时，须改用同为色 6 的 $W_{13}$；其中心 $3a+3b=2b=4a$，所以也在甲支补集内。这说明最后一类不能无条件沿用 $W_6$。

$q=0$ 乙支在 $b=0$ 时三个词都给 $3a$。在 $a=b\ne0$ 时，$W_{14},W_{31},W_4$ 的中心是 $(2b,4a+b,2b)=(2b,0,2b)$，故色 3 必须由这里指定的实际 $W_{31}$ 供应。在 $a=3b,b\ne0$ 时，$W_7,W_3,W_{13}$ 的中心分别为 $4a+2b,2a+3b,3a+3b$，即 $4b,4b,2b$，均属于 $\{2b,4b\}$。乙支第三问是 $W_{12}$，因此这里使用 $W_3$ 的色 3 确是新色。

命题 134.2 的 $\gamma_0,\gamma_2$ 列同时给表中每行的三个不同颜色；与命题 134.3 的四个 $U$ 比较，它们逐行都在 $U$ 内。补词表也逐项使用相同字典的颜色列，恰覆盖对应 $U$。因此每个分隔词、每个补词都是一个可执行的实际词，模 5 中心与模 7 颜色来自同一 $(A,B)$，不存在分别选择两个边缘见证再用 CRT 拼成查询的步骤。$\square$

**定理 134.6（全参数的确定性六问上界）。** 对满足约定 134.1 参数条件的每个实际行，在其每个允许返回深度、每个正值实际来源上，存在一个恰执行六次收费合法三窗内查询的确定性策略，恢复原始 $r\bmod5040$。后三问由前三问完整历史一次确定，无须再适应，也不要求假设 107.5 的短词分离条件。

证明。前三问用命题 134.3。随后从命题 134.4 选取实际二进、三进需求词，省掉单点需求，只合并完全相同的词。记所留词集为 $\mathcal S$，其颜色集为 $S$；已证 $|\mathcal S|=|S|\le2$，且 $S\subset U$。

这里使用已有的“三色分隔词足够”观察，并给出所需的完整鸽巢论证：命题 134.5 提供三元素 $R\subset U$，故 $|S|\le2<|R|$ 保证 $R\setminus S\ne\varnothing$。若模 5 后验仍是二元对，从该行分隔词库取颜色为 $R\setminus S$ 中最小代表元的词并加入；若模 5 已命中，则省去此步。选取的新颜色保证该词不同于所有已选词，且所选数至多三。即使一个已有词会附带分隔模 5，仍允许按此规则保守地另取一个异色分隔词。

若目前不足三词，就从补词表取最小未用 $U$ 颜色的对应实际词，直到恰有三个不同颜色的词。由于 $|U|=4$，每次不足三词时都有未用颜色及其实际补词。此规则按颜色排除重复；例如已经选 $W_{30}$ 的色 3 时，不能再用同色 $W_{21}$ 补齐，已经选 $W_{31}$ 的色 6 时也不能用 $W_{19}$ 补同一色。选定的三词按唯一 $B$ 标签递增执行，次序无歧义，且都在前三问历史给定后确定。

所有原需求的分隔词仍保留，所以二进、三进后验确定。模 5 若原已是单点就保留其值，否则至少有一个所选词的中心在其补集对内，完整 gcd 的等值位区分该对。这个论证同时涵盖零、一、两个原需求，以及两需求使用同一词而合并的情形；新增信息不能取消已有区分。

模 7 的前三个测试色互异，后三色互异且全在 $U$，所以每条历史合共测试六种不同颜色。任一问命中即可确定 $x\bmod7$；六次全未命中则确定唯一未测的第七色。即使前三问已有模 5 或模 7 命中，省需求、选分隔词及补齐规则仍全定义，并照常完成六问。由四个确定的坐标作 CRT 得 $x\bmod5040$，最后输出 $r=-h^{-1}x$。单位恒等式 $x-d=-h(r+C)$ 保证这正是物理回答所识别的原始余数。

命题 134.2 保证每个实际执行词都至多三窗、接缝合法、末窗非零、整数值为正。全部六问各自从固定原始来源重置，没有免费空词观察、来源或初始化切换、物理标量乘法、前置第四窗。上界证明分隔全部归一化余数，故在任意允许返回深度也成立。三色足够的初等观察在这里作为既有依据；本节给出的内容是对全部允许参数共同成立的实际分隔词库、补词及联合分配。$\square$

## 135. 实际行的精确参数像与六十八个六问相位

**命题 135.1（模 144 同词接口的充要条件与局部参数限制）。** 对一个固定实际行 $(u,v)$ 和单位 $h$，每个相同实际词都有 $h(Au+Bv)\equiv B\pmod{144}$，当且仅当

$$
hu=0,\qquad hv=1\pmod{144}.
$$

存在这种单位的充要条件是 $u=0\pmod{144}$ 且 $v$ 为模 144 单位。在实际相位 $w_j=(F_{3j+3},F_{3j+4})$、$0\le j<80$ 上，这恰好等价于 $j\equiv3\pmod4$。固定这种行以后，模 5、模 7 的局部系数对必须分别是

$$
h_p(u,v)\in\mathbb F_p^2,\qquad h_p\ne0,\qquad p=5,7.
$$

只有非零共同标量自由度，不能从任意两个局部边缘值独立选系数。

证明。必要性只用两个实际词即可：$W_1$ 的系数对 $(0,1)$ 给 $hv=1$，$W_2$ 的 $(1,2)$ 给 $hu+2hv=2$，从而 $hu=0$。充分性由线性式逐词得到。因 $h$ 为单位，这等价于 $u=0$、$v$ 为单位且 $h_{144}=v^{-1}$；反向可将这个 $h_{144}$ 与模 5、7 的任意非零局部单位用 CRT 合成一个全局单位。

实际行条件采用命题 105.5 的 $\rho(16)=\rho(9)=12$ 及推论 105.3 的零指标整除性质：

$$
144\mid F_{3j+3}
\quad\Longleftrightarrow\quad 12\mid3j+3
\quad\Longleftrightarrow\quad j\equiv3\pmod4.
$$

相邻 Fibonacci 数互素，故此时 $F_{3j+4}$ 在模 144 上必为单位。这只是该指定同词接口的充要条件。

由 $d=h(Au+Bv)$，模 $p$ 上系数确为 $h_p(u,v)$；连续 Fibonacci 数不同时为零，且非零标量不能把零系数改成非零系数。若 $v\ne0\pmod p$，可取 $h_p=v^{-1}$ 得到图

$$
L_p=B+(u/v)A.
$$

若 $v=0\pmod p$，则 $u\ne0$，须取 $h_p=u^{-1}$ 得到另一图 $L_p=A$；它不能写成有限 $t$ 的 $B+tA$。其它选择只是将整对系数和目标 $x_p$ 一起乘非零标量，仍保持深度及同一字面词。CRT 能合并这些合法局部单位；它不能生成额外的实际行、额外的占用集或任意局部中心。$\square$

**命题 135.2（归一化实际族的矩阵公式与精确射影像）。** 将全部满足命题 135.1 的实际相位写为

$$
j=4k-1,\qquad 1\le k\le20.
$$

令 $S=\begin{pmatrix}0&1\\1&1\end{pmatrix}$，将权重对写成列。则

$$
w_{4k-1}=S^{12k}\binom{0}{1},\qquad
S^{12}=\begin{pmatrix}89&144\\144&233\end{pmatrix}.
$$

其局部行具有下列全参数公式：

$$
\begin{aligned}
(u,v)&=(0,89^k)\pmod{144},\\
(u,v)&=(4k,1+2k)\pmod5,\\
(u,v)&=
\begin{cases}
(-1)^\ell(0,1),&k=2\ell,\\
(-1)^\ell(4,2),&k=2\ell+1
\end{cases}
\pmod7.
\end{aligned}
$$

因此模 7 总有 $v\ne0$，其正规图 $B+qA$ 的参数为偶 $k$ 时 $q=0$、奇 $k$ 时 $q=2$。全部实际射影参数像恰为

$$
\left(\mathbb P^1(\mathbb F_5)\setminus\{[2:1]\}\right)\times\{0,2\}.
$$

对每行可明确取以下局部单位，CRT 唯一确定 $h\bmod5040$：

$$
h_{144}=89^k,\qquad
h_5=
\begin{cases}
(1+2k)^{-1},&1+2k\ne0\pmod5,\\
(4k)^{-1},&1+2k=0\pmod5,
\end{cases}
$$

$$
h_7=
\begin{cases}
(-1)^\ell,&k=2\ell,\\
4(-1)^\ell,&k=2\ell+1.
\end{cases}
$$

此时模 5 参数是 $(a,b)=(4k/(1+2k),1)$ 或 $(1,0)$，分别对应 $B+tA$ 与 $A$；每个恢复出的 $x=-hr$ 都按 $r=-h^{-1}x$ 还原。

证明。命题 123.2 的 Fibonacci 矩阵式给显示的 $S^{12}$。模 144 它为 $89I$，且 $89^2=7921=1+55\cdot144$，所以其 $k$ 次幂给第一公式与 $h_{144}$。模 5 写为

$$
S^{12}=I+N,\qquad
N=\begin{pmatrix}3&4\\4&2\end{pmatrix},\qquad
N^2=\begin{pmatrix}25&20\\20&20\end{pmatrix}=0\pmod5.
$$

二项式展开给 $(I+N)^k=I+kN$，从而第二列为 $(4k,1+2k)$；特别地

$$
2u+v=1\pmod5.
$$

模 7 写 $M=\begin{pmatrix}5&4\\4&2\end{pmatrix}$，则

$$
M^2=\begin{pmatrix}41&28\\28&20\end{pmatrix}=-I\pmod7.
$$

依 $k$ 奇偶取幂便给显示的两种行，除以 $v$ 分别得到 $q=0,2$；$2^{-1}=4\pmod7$ 给所列 $h_7$。这都是整个参数族的矩阵恒等式，不需要枚举 80 相位轨道。

为证射影像的“恰好”，一个射影点 $[\alpha:\beta]$ 能在仿射直线 $2u+v=1$ 上取代表，当且仅当 $2\alpha+\beta\ne0$；此时唯一代表是 $(\alpha,\beta)/(2\alpha+\beta)$。被排除的唯一直线 $2\alpha+\beta=0$ 是 $[2:1]$。对于直线上每个代表，$u=4k$ 唯一决定 $k\bmod5$，继而 $v=1+2k$ 自动满足；所以模 5 像没有遗漏或额外点。另一方面 $k\bmod2$ 独立选择 $q=0$ 或 2。由模 5 与模 2 的 CRT，每一对参数恰对应一个 $k\bmod10$，在 $1\le k\le10$ 中各出现一次；$k+10$ 给第二个实际相位，其同词伴随关系见推论 135.3。这证明实际像正是所示直积，同时没有把抽象允许参数一律当成实际参数。

$2u+v=1$ 还保证模 5 的 $u,v$ 不同时为零，所以显示的两个 $h_5$ 分支均有定义。所有局部单位合成的 $h$ 为全局单位，逐词满足约定 134.1 的联合中心形式；只有多项式非零条件还待下一条筛选。$\square$

**推论 135.3（十二个族内相位及不增加查询的同词伴随）。** 在 $j=4k-1$、$1\le k\le20$ 的实际族内，约定 134.1 的多项式条件精确等价于

$$
k\not\equiv0,4\pmod5.
$$

因此定理 134.6 适用于十二个相位

$$
\mathcal J_{\mathrm{par}}=\{3,7,11,23,27,31\}+\{0,40\}.
$$

这里加号表示六元集与其平移 40 后的六元集之并。对于任意已选归一化单位 $h_j$，相位 $j+40$ 可取 $h_{j+40}=h_j\lambda$，其中 $\lambda=1441$。全部字面词、分支和选词规则不变，解码为

$$
x=-h_j\lambda r,\qquad r=-\lambda h_j^{-1}x\pmod{5040}.
$$

证明。对任意非零模 5 标量 $h_5$，命题 135.2 给

$$
a=4kh_5,\qquad a+b=(1+k)h_5,\qquad 2a+b=h_5.
$$

三因子同时非零当且仅当 $k\not\equiv0,4\pmod5$。非零共同标量不能改变这个条件。$1\le k\le20$ 的四个五指标区间各留下三种余数，故共有十二行。将条件按 $k\bmod10$ 写成 $1,2,3,6,7,8$，由 $j=4k-1$ 得所示六元集和 $+40$ 伴随，不需要另作相位轨道表。

四个新的低半相位可直接在矩阵公式中作精确代入：

| 135.3 新低半相位 | $k$ | 原模 5 行 $(u,v)$ | 正规参数 $(a,b)$ | $q$ | $+40$ 相位 |
| --- | ---: | --- | --- | ---: | ---: |
| 135.3 相位 $11$ | 3 | $(2,2)$ | $(1,1)$ | 2 | 51 |
| 135.3 相位 $23$ | 6 | $(4,3)$ | $(3,1)$ | 0 | 63 |
| 135.3 相位 $27$ | 7 | $(3,0)$ | $(1,0)$ | 2 | 67 |
| 135.3 相位 $31$ | 8 | $(2,2)$ | $(1,1)$ | 0 | 71 |

相应三因子依次为 $(1,2,3)$、$(3,4,2)$、$(1,1,2)$、$(1,2,3)$，均非零。第三行明确使用 $A$ 图，不能丢掉 $v=0$ 的实际情形。$k+10$ 保持模 5 类与奇偶性，所以四个伴随具有同一 $(a,b),q$。

更强的逐词结论由命题 123.2 直接给出：$w_{j+40}=\lambda w_j$、$\lambda^2=1$，且 $\lambda=1\pmod{144}$。每个相同占用集的物理平移满足 $C_{j+40}=\lambda C_j$，于是

$$
h_{j+40}C_{j+40}=h_j\lambda^2C_j=h_jC_j.
$$

故全部归一化中心逐词相同，第一二进深度分支、需求分配、分隔词库、补词和递增 $B$ 顺序均转移。逆单位为 $\lambda h_j^{-1}$，必须保留显示的负号。此过程只重命名解释坐标，没有缩放来源、替换词或前置窗口，也没有另加一问。$\square$

**定理 135.4（共同实际来源上的精确六问与六十八相位）。** 在约定 123.1、134.1 的已知相位、正实际来源、两初始化合并候选族、每问固定同源重置、完整 gcd、至多三窗和规范 End 合同下，对每个 $j\in\mathcal J_{\mathrm{par}}$ 有

$$
Q_3(5040;w_j)=6.
$$

与推论 125.7 合并，已有实际六问构造的集合扩充为

$$
\mathcal J_{68}=\mathcal J_{60}\cup\{11,23,27,31,51,63,67,71\},
\qquad |\mathcal J_{68}|=68.
$$

这里新增恰八个不同实际相位；本参数族另外四个 $3,7,43,47$ 已在 $\mathcal J_{60}$ 中。尚未由这些构造解决的集合恰为

$$
\{6,15,16,19,26,35\}+\{0,40\}
=\{6,15,16,19,26,35,46,55,56,59,66,75\}.
$$

证明。推论 135.3 已对全部十二个实际行验证定理 134.6 的参数前提，故上界在每个允许返回深度及每个正值实际来源成立。匹配下界按命题 123.3 原合同应用，保留其共同实现量词：对给定相位 $j$ 选择一次足够大的 $N=j+80t\ge1$。引理 105.1 的标签 $(1,\mathrm{true})$ 实际整数像为

$$
[F_{3N+2},F_{3N+3}-1]\cap\mathbb Z,
\qquad\text{长度 }F_{3N+1}.
$$

使其长度至少为 5040，就在同一深度、同一实际整数权重行上取得全部余数的正值实际来源。区间采用两种初始化合并的来源族；不同候选可以有不同 $\varepsilon$，但每个候选一经选择，其 $\varepsilon$、原始前缀和深度始终固定。这不声称任意小深度满支撑，也不声称分别固定 $\varepsilon$ 的满纤维。

在该共同深度固定一个模 720 余数，选它的七个模 5040 提升所对应的七个实际源。任一共同历史确定下一查询词；若成功，七个候选中尚存者的模 $16,9,5$ 回答相同，模 7 只测试一个等值。因此沿未命中历史每问至多排除一个候选，恒错词排除零个。空词也是收费的一次等值测试；重复或已排除颜色不会多排除候选。五问后至少两个固定实际源产生同一整段历史，提前停止仍不能区分它们。这个论证覆盖全部 55 个成功词和全部恒错词，及任意确定性适应选择，没有逐问更换隐藏来源。因此全策略的最坏成本至少六，与所给上界相合；它不是每个单独来源都固有需要六问的断言。

推论 125.7 的 $\mathcal J_{60}$ 及其证明保持原范围。$\mathcal J_{\mathrm{par}}$ 的十二行全为 $3\pmod4$，所以与 $\mathcal J_{60}$ 的 48 行同余族不交；与其十二个额外相位的交集恰为 $\{3,7,43,47\}$。故新并集增加 $12-4=8$ 个，正是显示的八元集。命题 123.2 的精确周期 80 保证不同相位编号代表不同实际行。推论 125.7 的二十元未决集为 $\{6,11,15,16,19,23,26,27,31,35\}+\{0,40\}$，删去新得的四个低半相位及其伴随后，恰余上述十二项。$\square$

**命题 135.5（未适用行、既有构造与负结论的界限）。** 命题 135.1 的接口充要条件和推论 135.3 的多项式分类，都只分类本参数构造的适用范围。剩余十二相位中，$6,16,26$ 及其 $+40$ 伴随不满足该模 144 同词接口；$15,35$ 及其伴随使甲支模 5 三中心合一；$19,59$ 使乙支模 5 中心重复。这些事实均不推出 $Q_3\ge7$，也不否定其它六问策略。已由推论 125.7 包含的 $39,79$ 保持六问结论，即使它们也有 $a=0$。

证明。第一组三个低半相位及其伴随均不为 $3\pmod4$，故由命题 135.1 无法实现每个同词中心为 $B\bmod144$。后两组在归一化族中：$15,35$ 对应 $k=4,9$，即 $k=4\pmod5$，于是 $a+b=0$，甲支中心 $b,b+(a+b),b+2(a+b)$ 全为 $b$；$19,59$ 对应 $k=5,15$，即 $k=0\pmod5$，于是 $a=0$，乙支中心为 $b,2b,2b$。这时全失配模 5 后验分别有四个或三个元素，命题 134.5 针对二元补集的词库没有给出相应收尾定理。$39,79$ 的 $k=10,20$ 同样使 $a=0$，但其六问结论由此前不同构造给出；本节充分条件失败不会撤销该结论。

同理，命题 118.8 的指定前三问失败和约定 114.14 的受限子族结论均保留各自的查询前提；它们不分类完整三窗域的全部策略。本节既未为剩余十二行建立替代模 144 接口，也未处理上述三元、四元模 5 后验的统一收尾。命题 123.3 在剩余行上仍给全策略下界六；推论 114.5 的全行上界十五仍保留假设 107.5 的语义覆盖、分区稳定与由之得到的短词分离前提，不能由本节的具体策略去掉该条件。

本节确定的是所列已知实际相位上原始模 5040 余数的确定性最坏查询数。所得参数像及六十八相位集合不包含全部八十相位的解法，不给未知相位、完整整数或生成前缀的恢复结论，不给随机化成本、取得标签的工作空间或最优总窗口工作量结论；也不蕴含 RH 或全局 Robin 结论。$\square$

## 追加锚（本行以下为增补区）

## 136. 一般模数的任意索引非自适应时间表

**定义 136.1（同源正时刻的固定表识别）。** 沿用定义 126.1 的实际来源、观察和递推，令 $\mathbb N$ 包含零，固定

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad q=(2,3),\qquad
C=\begin{pmatrix}2&3\\3&5\end{pmatrix},\qquad
C^{-1}=\begin{pmatrix}5&-3\\-3&2\end{pmatrix}.
$$

一个来源是 $v=(a,b)\in\mathbb N^2$，包括 $(0,0)$。写 $x=(n,z)=Cv$，则 $y_0=n$、$y_1=z$，且

$$
y_{k+2}=y_{k+1}+y_k,\qquad
 y_k=F_{k-1}n+F_kz=qM^kv\quad(k\ge1).
$$

这里 $F_0=0,F_1=1$。定理 5.4 的整数逆式给出实际观察对的准确条件：$n,z\ge0$、$5n\ge3z$、$2z\ge3n$，其来源为 $(5n-3z,2z-3n)$。本节在全部实际来源上识别，不把 $n$ 固定为已知参数。

固定整数 $H\ge1$。一问选正整数 $k$，从同一个原始来源的重置副本执行 $k$ 次 $\rho$，只取得终端读数

$$
g_H(v;k)=\gcd(qM^kv,H).
$$

时间表是预先选定的有限集合 $S\subset\mathbb Z_{>0}$，选择不能依赖答案，重复同一时刻不增加信息。称 $S$ 在模 $H$ 下充分，若

$$
\forall v,w\in\mathbb N^2,\qquad
\bigl(\forall k\in S,\ g_H(v;k)=g_H(w;k)\bigr)
\quad\Longrightarrow\quad
\bigl(\forall k\ge1,\ g_H(v;k)=g_H(w;k)\bigr).
$$

记最小 $|S|$ 为 $N_{\mathrm{nonadaptive}}(H)$；记定义 126.1 的连续时域 $T_H$ 为 $T_{\mathrm{consecutive}}(H)$。所有局部条件都作用于这个同一整数集合 $S$。来源之间的确切 $n$ 可不同；$n$、$g_0$、共同含量与推进途中的读数均不免费供应。目标是全部正时刻的 gcd 未来，不是确切数量或完整组成。这里把 $q$ 作为指定观察，所需桥是定理 5.4 的矩阵逆，不以素数种子分类为前提。

**定义 136.2（局部精度及所复用的命中层）。** 对素数 $p$、整数 $e\ge1$ 和任意整数观察对 $x=(n,z)$，定义

$$
c_x^{(e)}(k)=\min\{e,\nu_p(F_{k-1}n+F_kz)\},\qquad
 d_x=\min\{e,\nu_p(n),\nu_p(z)\},\qquad \nu_p(0)=\infty.
$$

称 $x$ 在 $p$ 处本原，若至少一个坐标不被 $p$ 整除。本原性只针对 $p$，不要求两坐标在整数中互素。若 $d_x=e$，所有指数恒为 $e$；若 $d_x<e$，写 $x=p^{d_x}u$、$m=e-d_x$，则 $u$ 本原，且

$$
c_x^{(e)}(k)=d_x+c_u^{(m)}(k).
$$

沿用定理 120.3、120.4 和引理 126.2 的射影秩

$$
r_j=\min\{r\ge1:p^j\mid F_r\},\qquad
P_j=\mathbb P^1(\mathbb Z/p^j\mathbb Z),\qquad
O_j=\{M^t[1:0]:t\in\mathbb Z\}.
$$

$P_j$ 中的点是本原向量模共同单位倍数。已有分类给 $3\le r_1\le p+1$、$|O_j|=r_j$ 和 $r_j\mid r_{j+1}\mid pr_j$。这些是射影返回阶，不能当作完整矩阵周期。每个射影父点有 $p$ 个子点：$r_{j+1}=pr_j$ 时，一个轨道父点的全部子点在轨道中；$r_{j+1}=r_j$ 时，恰有一个轨道子点，另 $p-1$ 个退出且不再进入任何更高轨道。

在剩余精度 $m$，本原未来恰有下列标签：深度 $h=0$ 的首层无命中；深度 $1\le h<m$ 的退出和相位 $\tau\bmod r_h$；或 $h=m$ 的末层轨道相位。首层无命中存在当且仅当 $r_1<p+1$；深度 $h<m$ 的退出存在当且仅当 $r_{h+1}=r_h$。各个所列标签都可实现。其命中集和指数为

$$
E_j(h,\tau)=
\begin{cases}
\{k\ge1:k\equiv\tau\pmod{r_j}\},&j\le h,\\
\varnothing,&j>h,
\end{cases}
\qquad
c_{h,\tau}^{(m)}(k)=\sum_{j=1}^{m}\mathbf1_{E_j(h,\tau)}(k).
$$

$h=0$ 时所有集合为空。每个来源的这些集合逐层嵌套。定理 126.4 中的整数向量 $K_t=(F_t,-F_{t-1})$ 在每层都有相位 $t$；等价地，第 $k$ 行 $(F_{k-1},F_k)$ 的本原核线为 $M^{-(k-1)}[1:0]$。以下复用这些已证分类、分支和代表，不重新证明秩提升。

**定义 136.3（末层覆盖与全塔覆盖）。** 对正整数 $R$ 记

$$
\mathcal R_R(S)=\{k\bmod R:k\in S\}.
$$

在增长层 $j\ge2$，对父类 $a\in\mathbb Z/r_{j-1}\mathbb Z$，记

$$
b_j(a;S)=\bigl|\{b\in\mathcal R_{r_j}(S):b\equiv a\pmod{r_{j-1}}\}\bigr|.
$$

它数不同子剩余类，多次访问同一子类只计一次。末层条件 $D_{p,e}(S)$ 按互斥的四种情形定义为

$$
\begin{array}{ll}
e=1,\ r_1=p+1:&|\mathcal R_{r_1}(S)|\ge r_1-1;\\
e=1,\ r_1<p+1:&\mathcal R_{r_1}(S)=\mathbb Z/r_1\mathbb Z;\\
e\ge2,\ r_e=r_{e-1}:&\mathcal R_{r_e}(S)=\mathbb Z/r_e\mathbb Z;\\
e\ge2,\ r_e=pr_{e-1}:&b_e(a;S)\ge p-1\quad\text{对每个 }a\bmod r_{e-1}.
\end{array}
$$

全塔条件 $\mathcal C_{p,e}(S)$ 是首层条件与所有 $2\le j\le e$ 层条件的合取：停滞层要求全部模 $r_j$ 剩余，增长层要求每个父类至少 $p-1$ 个不同子类。$e=1$ 时只有首层条件。

## 137. 末层覆盖、未知共同含量与全部剩余精度

**引理 137.1（末层条件恰覆盖全塔）。** 对每个 $p,e,S$，

$$
D_{p,e}(S)\ \Longleftrightarrow\ \mathcal C_{p,e}(S).
$$

而且这两个条件蕴含 $\mathcal C_{p,m}(S)$ 对每个 $1\le m\le e$ 成立。

证明。$e=1$ 时两定义相同。设 $e\ge2$。若末步停滞，$D_{p,e}$ 给全部模 $r_e$ 剩余，而每个较低 $r_j$ 整除 $r_e$，故投影后仍覆盖全部模 $r_j$ 剩余。若末步增长，每个父类至少有 $p-1\ge1$ 个被测子类，故覆盖全部模 $r_{e-1}$ 剩余；再向下投影也覆盖全部较低秩的剩余。较低层的全覆盖满足首层要求和每个停滞要求；在任何较低增长层，它更覆盖每个父类的全部 $p$ 个子类，因而满足所需的 $p-1$ 条件。加上原已满足的末层条件，便是全塔条件。这个投影不要求此前一直增长；重复秩和先停滞后增长同样成立。

反过来，全塔的最后一项就是末层条件。截去全塔中高于 $m$ 的条件，得到 $\mathcal C_{p,m}$，所以所有较低剩余精度也同时得到覆盖。$\square$

**引理 137.2（任意被测时刻的本原分离）。** 若 $\mathcal C_{p,m}(S)$ 成立，则在精度 $m$，两个本原整数观察对在 $S$ 上的截断指数相同必有相同的全部正时刻指数。

证明。反设两个本原未来不同。按定义 136.2 的分类，取最小层 $j$，使两条未来的命中集 $E_j,E'_j$ 不同。所有更低层集合相同。

若 $j=1$，两个非空命中集就是两个不同模 $r_1$ 相位。首层满轨道时最多漏测一个相位，因此这两个相位中至少一个被测；非满时全部轨道相位都被测，结论也成立。若一个命中集为空、另一个非空，则无命中方向存在，所以首层非满，那个非空相位必被测。两个空集不可能是首次差别。故总能取 $k\in S$，恰属于两个首层集合之一。

若 $j>1$，共同父层命中集必须非空，否则嵌套性使两个第 $j$ 层都空。增长时，轨道父点的全部 $p$ 个子点仍在轨道，不能在这一层退出；两不同命中集只能是该父类的两个不同子相位。至少 $p-1$ 个子类被测，两个不同子类不能同时漏测，故其一含某个 $k\in S$。停滞时，轨道父点只有一个轨道子点；两不同命中集只能是该子点的相位与退出的空集。全部模 $r_j$ 剩余都被测，所以这个相位也含某个 $k\in S$。

在选定的实际被测时刻，一个指数至少为 $j$，另一个至多为 $j-1$。较高命中集包含在各自的第 $j$ 层中，不能消去这个阈值差别。于是两个 $S$ 上的 transcript 不同，矛盾。这里使用的是所选 $k$ 所在的剩余类，并没有要求它是某个相位的首次正代表，也没有限制 $S$ 的最大值。$\square$

**引理 137.3（同一时间表恢复共同含量并识别任意整数对）。** 若 $D_{p,e}(S)$ 成立，则 $S\ne\varnothing$，且对每个整数观察对 $x$，

$$
d_x=\min_{k\in S}c_x^{(e)}(k).
$$

因此 $S$ 识别所有整数观察对的模 $p^e$ 全未来，特别识别全部实际非负来源。

证明。引理 137.1 给首层条件。$r_1\ge3$，所以即使在较弱的满轨道情形，仍至少覆盖 $r_1-1\ge2$ 个不同首层相位；非满情形覆盖更多。这也说明 $S$ 非空。

若 $d_x<e$，除出 $p^{d_x}$ 得剩余精度 $m=e-d_x$ 的本原对 $u$。其首层命中集只有一个相位，或为空。$S$ 至少覆盖两个不同首层类，其中至少一个不在这个命中集中。在那个被测时刻，本原指数为零，原指数恰为 $d_x$；所有其它被测原指数都至少为 $d_x$。故显示的最小值等式成立。若 $d_x=e$，所有被测指数都是 $e$，同一等式仍成立，包含零对与非零的模 $p^e$ 零对。

现在设 $x,x'$ 在 $S$ 上的读数相同。取最小值得到同一个 $d$，不需要外部供应含量。若 $d=e$，两者未来都恒饱和。若 $d<e$，逐项减去已恢复的 $d$，得到两个本原对在精度 $m=e-d$ 的相同 transcript。引理 137.1 保证 $\mathcal C_{p,m}(S)$；引理 137.2 遂给其全部本原未来相同，加回 $d$ 即得原未来相同。除法在整数观察对上完成，充分性已在这个域证明，无需假设除后的观察对仍位于实际非负来源的像内。$\square$

## 138. 四种完整时间表碰撞与实际来源的全局实现

**引理 138.1（隔离一个完整素数幂的实际来源）。** 固定 $H>1$ 的完整因子 $P=p^e\parallel H$，置 $Q=H/P$。对任意观察剩余对 $x=(\bar n,\bar z)\bmod P$，逐坐标取最小非负剩余，定义

$$
A_x=[C^{-1}x]_P
 =\bigl([5\bar n-3\bar z]_P,[-3\bar n+2\bar z]_P\bigr),\qquad
V_{H,P}(x)=Q A_x.
$$

则 $V_{H,P}(x)\in\{0,\ldots,H-1\}^2$ 是实际来源，而且对每个 $k\ge1$，

$$
g_H(V_{H,P}(x);k)=Qp^{c_x^{(e)}(k)}.
$$

证明。每个 $A_x$ 坐标介于 $0$ 与 $P-1$，故 $V_{H,P}(x)$ 的坐标介于 $0$ 与 $Q(P-1)=H-Q<H$。$CA_x\equiv x\pmod P$，所以由定理 5.4 的递推式，

$$
qM^k A_x\equiv F_{k-1}\bar n+F_k\bar z\pmod P
\quad(k\ge1).
$$

截断赋值只依赖模 $P$ 的剩余，于是准确的整数恒等式给

$$
\begin{aligned}
\gcd(qM^k V_{H,P}(x),H)
 &=\gcd(QqM^k A_x,QP)\\
 &=Q\gcd(qM^k A_x,P)
 =Qp^{c_x^{(e)}(k)}.
\end{aligned}
$$

因为 $P$ 是完整因子，$Q$ 是 $p$ 单位；实际观察对在模 $P$ 下是 $Qx$，保留了 $x$ 的局部指数。在其它完整素数幂处，来源及观察都为零，永远饱和。这是同一实际来源同时实现全部局部条件的构造。其确切观察对 $CV_{H,P}(x)$ 自动满足实际不等式，因而没有把独立局部边缘的存在冒充联合来源的存在。$\square$

**定理 138.2（末层条件失败的四类全表反例）。** 固定素数 $p$ 和 $e\ge1$，置 $P=p^e$。若 $D_{p,e}(S)$ 失败，则存在两个在 $p$ 处本原的观察剩余对 $x,x'\bmod P$，其局部指数对每个 $k\in S$ 都相同，却在一个未被 $S$ 覆盖的相位的正代表 $t$ 处分别为 $e,e-1$。在任意含完整因子 $P=p^e$ 的 $H$ 中，引理 138.1 的两个实际来源因此在整个 $S$ 上有相同完整 gcd transcript，并在 $t$ 处分离为 $H,H/p$。

证明。令 $[a]^+_R\in\{1,\ldots,R\}$ 是剩余类 $a$ 的正代表，零类取 $R$。以下 $c_x$ 均指精度 $e$ 的截断指数。四种情况分别覆盖定义 136.3 的四项失败。

第一，$e=1$ 且首层满轨道。失败意味着至少漏掉两个不同相位 $\alpha,\beta\bmod r_1$。令 $t=[\alpha]^+_{r_1}$、$u=[\beta]^+_{r_1}$，取 $x=K_t$、$x'=K_u$ 模 $p$。相邻 Fibonacci 数互素，故两对本原；定义 136.2 的相位公式给所有正时刻的准确指数

$$
c_x(k)=\mathbf1_{\{k\equiv\alpha\ (\mathrm{mod}\ r_1)\}},\qquad
c_{x'}(k)=\mathbf1_{\{k\equiv\beta\ (\mathrm{mod}\ r_1)\}}.
$$

$S$ 中两个指示函数都为零，所以完整答案恒为 $Q$。在 $t$ 处指数为 $1,0$，完整答案为 $H,H/p$。

第二，$e=1$ 且首层非满。取漏掉的相位 $\alpha$，令 $t=[\alpha]^+_{r_1}$、$x=K_t$ 模 $p$。$|P_1|=p+1>r_1=|O_1|$，故可以从非空集合 $P_1\setminus O_1$ 选一点，取其本原代表 $x'$。分类给 $c_{x'}(k)=0$ 对所有正时刻成立，而 $c_x(k)$ 是上一式的 $\alpha$ 指示函数。因此整个 $S$ 上两完整答案都为 $Q$，在 $t$ 处为 $H,H/p$。这里的代表由非空集合的存在取得，不要求有限搜索。

第三，$e\ge2$ 且末步增长。写 $R=r_{e-1}$，于是 $r_e=pR$。失败给某父类 $a\bmod R$ 仅有至多 $p-2$ 个被测子类，故有两个不同未测子类 $\alpha,\beta\bmod pR$。取其正代表 $t,u$，令 $x=K_t$、$x'=K_u$ 模 $P$。由于每个 $r_j$（$j<e$）整除 $R$，两个满深度相位在所有较低层相同。写

$$
B_a(k)=\sum_{j=1}^{e-1}\mathbf1_{\{k\equiv a\ (\mathrm{mod}\ r_j)\}}.
$$

则对所有 $k\ge1$，

$$
\begin{aligned}
c_x(k)&=B_a(k)+\mathbf1_{\{k\equiv\alpha\ (\mathrm{mod}\ pR)\}},\\
c_{x'}(k)&=B_a(k)+\mathbf1_{\{k\equiv\beta\ (\mathrm{mod}\ pR)\}}.
\end{aligned}
$$

两个末层指示函数在整个 $S$ 上都为零，故完整答案同为 $Qp^{B_a(k)}$。在 $k=t$，全部 $e-1$ 个较低指示函数等于一，两个末层指示函数为一、零，给完整答案 $H,H/p$。当 $p=2$ 时，失败就是某父类没有被测子类，其两个子类均遗漏；同一构造仍成立。

第四，$e\ge2$ 且末步停滞。写 $R=r_e=r_{e-1}$，取遗漏相位的正代表 $t\in\{1,\ldots,R\}$。在观察状态坐标中，$M^t(n,z)=(y_t,y_{t+1})$。因 $\det M=-1$，整数逆幂存在，故可取

$$
x_+=M^{-t}\binom01\pmod P,\qquad
x_-=M^{-t}\binom{p^{e-1}}1\pmod P.
$$

两对均本原，并且模 $p^{e-1}$ 相同。又 $M(1,0)=(0,1)$，故 $x_+=M^{-(t-1)}(1,0)$，其相位确为 $t$，没有一位偏移。两者在第 $e-1$ 层同为相位 $t$ 的轨道父点。停滞时该父点只有一个轨道子点；该子点在时刻 $t$ 的第一坐标必须为零模 $P$，但 $x_-$ 的此坐标为 $p^{e-1}\not\equiv0\pmod P$。所以 $x_-$ 正好在深度 $e-1$ 后退出，不能在任何正时刻命中第 $e$ 层。

还可直接逐类核对这个退出的准确赋值。写

$$
B_t(k)=\sum_{j=1}^{e-1}\mathbf1_{\{k\equiv t\ (\mathrm{mod}\ r_j)\}}.
$$

若 $k\equiv t\pmod R$，由射影秩的标量返回性质，$M^{k-t}$ 模 $P$ 是单位标量。于是 $x_+$ 在时刻 $k$ 的读数为零模 $P$，而 $x_-$ 的读数为某个单位乘 $p^{e-1}$，截断指数准确为 $e-1$。若 $k\not\equiv t\pmod R$，则 $x_+$ 在第 $e-1$ 层已不命中，指数为 $B_t(k)\le e-2$；两读数同余模 $p^{e-1}$，所以 $x_-$ 的指数也准确为 $B_t(k)$。这证明所有正时刻的完整公式

$$
c_{x_+}(k)=B_t(k)+\mathbf1_{\{k\equiv t\ (\mathrm{mod}\ R)\}},\qquad
c_{x_-}(k)=B_t(k).
$$

整个 $S$ 不含该剩余类，两完整答案均为 $Qp^{B_t(k)}$；在 $t$ 处它们为 $H,H/p$。这个证明适用于真实停滞，包括模 4 到模 8 以及奇素数初始停滞，不以通常增长来代替停滞。

四类公式都对任意大的正 $k$ 成立，所以证明了整个任意稀疏 $S$ 的碰撞。所选 $t$ 为遗漏类的正代表，必不在 $S$；零相位也使用正时刻而非免费时间零。若还要求分离时刻大于 $\max S$，在同一遗漏相位中加足够大的末层秩倍数，上述指数差和完整答案差仍成立。逆幂只构造初始剩余，实际查询全是从各自固定的非负来源向前执行。最后对每对施加引理 138.1，即得同一来源实现所有因子的完整 transcript 和所述 $H,H/p$ 分离。$\square$

**定理 138.3（任意索引识别的准确局部与全局判据）。** 固定 $p,e,S$。下列条件等价：末层条件 $D_{p,e}(S)$；全塔条件 $\mathcal C_{p,e}(S)$；识别全部本原整数观察对的局部未来；识别全部整数观察对的局部未来；识别全部实际非负来源的模 $p^e$ 未来。实际来源还可限制为在 $p$ 处本原而保持同一判据。

对任意 $H>1$，同一个有限正时间表 $S$ 充分，当且仅当

$$
\bigwedge_{p^e\parallel H} D_{p,e}(S).
$$

$H=1$ 时这是空合取，每个 $S$ 都充分，包括空表。

证明。引理 137.1 给末层与全塔的等价；引理 137.2、137.3 给充分性，包括本原、未知含量、饱和和全部较低精度。若末层条件失败，定理 138.2 的两个本原对在 $S$ 上相同而未来不同，故本原域与全部整数域均不能识别。取 $H=P=p^e$，则引理 138.1 中 $Q=1$，两个实际来源的观察剩余恰为所选本原对；$C$ 模 $p$ 可逆，所以来源本身也本原。这同时否定实际域及其本原子域的识别性，完成所有局部等价。

全局充分性中，两个实际来源的完整 gcd 答案在 $S$ 上相同，便使每个 $p^e\parallel H$ 的截断指数在同一个 $S$ 上相同。分别用局部结论得到所有正时刻的各素数指数相同，唯一分解遂给完整 gcd 未来相同。全局必要性中，若一个因子失败，定理 138.2 与引理 138.1 给一对实际来源；其它因子恒饱和，所选因子的差别在完整 gcd 中保留，整个 $S$ 答案相同但未来为 $H,H/p$。这里没有拼接独立选择的局部时间表，也没有要求这对来源的确切 $n$ 相同。

最后，$\gcd(y,1)=1$ 包括 $y=0$，所以模 1 只有一个未来，空表即可识别。模数大于一时，首层覆盖至少两个不同相位，故空表不充分。$\square$

## 139. 准确非自适应查询数及同一表的三项最小值

**定理 139.1（任意索引查询数等于连续时域）。** 沿用定理 126.5 的局部连续长度，显式写为

$$
L_p(e)=
\begin{cases}
r_1-1,&e=1,\ r_1=p+1,\\
r_1,&e=1,\ r_1<p+1,\\
r_e,&e\ge2,\ r_e=r_{e-1},\\
r_e-r_{e-1},&e\ge2,\ r_e=pr_{e-1}.
\end{cases}
$$

置 $T(1)=0$，对 $H>1$ 置 $T(H)=\max_{p^e\parallel H}L_p(e)$。则

$$
N_{\mathrm{nonadaptive}}(H)=T_{\mathrm{consecutive}}(H)=T(H).
$$

同一个表 $S_* =\{1,\ldots,T(H)\}$ 达到上界。任何 $|S|<T(H)$ 的表，无论索引有多大，都有定理 138.2 给出的实际来源全表碰撞。

证明。先从准确覆盖条件给局部基数下界。首层满轨道至少需要 $r_1-1$ 个不同相位，非满则需 $r_1$ 个；末步停滞需全部 $r_e$ 个相位，所以这些情形都要求 $|S|\ge L_p(e)$。末步增长时写 $R=r_{e-1}$，$R$ 个父类两两不交，而每个父类需要至少 $p-1$ 个不同子类。因此

$$
|S|\ge |\mathcal R_{r_e}(S)|
 =\sum_{a\in\mathbb Z/R\mathbb Z}b_e(a;S)
 \ge (p-1)R=r_e-r_{e-1}=L_p(e).
$$

这数的是一个任意整数集合覆盖了多少类；一个很大的时刻仍只测试一个父类的一个子类。若 $|S|$ 小于相应局部界，首层满轨道必有两个相位遗漏，首层非满必有一个相位遗漏，停滞必有一个末层相位遗漏，或增长必有一个父类至多测试 $p-2$ 个子类。恰好落入定理 138.2 的四类之一。

对 $H>1$，选择达到有限最大值 $T(H)$ 的一个完整因子 $P=p^e$。若 $|S|<T(H)$，上述局部计数迫使该因子的末层条件失败。定理 138.2 给一对在整个 $S$ 上答案相同的实际来源，并以引理 138.1 固定所有其它因子，证明 $N_{\mathrm{nonadaptive}}(H)\ge T(H)$。这个下界来自任意索引的相位计数，不是从连续前缀的较晚首次分离推出。

上界准确复用定理 126.5：其模数 $H$ 就是本定理的 $H$，其完整因子 $p^e$、观察 $q$、实际来源 $v\in\mathbb N^2$、局部 $L_p(e)=P_p(e)$ 与这里相同，其 $T_H$ 按定义恰为 $T_{\mathrm{consecutive}}(H)$。该定理在不供应 $n,g_0$ 或含量的条件下，已证明同一个前 $T(H)$ 项表充分，包含零与所有含量。故 $S_*$ 是一个基数 $T(H)$ 的合法非自适应表，给反向不等式；该定理还直接给连续时域等于 $T(H)$。取 $H=p^e$，也得局部任意索引最小数恰为 $L_p(e)$。$H=1$ 时空表和恒一未来给两种长度都为零。$\square$

**定理 139.2（同一首段表同时达到三个资源最小值）。** 对有限表约定 $\max\varnothing=0$、空和为零。在定义 136.1 的同源独立重置契约下，所有充分非自适应表的最小查询数、最小最大索引和最小独立推进替换次数和分别为

$$
T(H),\qquad T(H),\qquad \frac{T(H)(T(H)+1)}2.
$$

同一个 $S_*$ 同时达到这三个最小值。

证明。令充分表的不同正时刻依次为 $k_1<\cdots<k_n$。由定理 139.1，$n\ge T(H)$；由正整数及严格递增，$k_i\ge i$。非空表于是满足

$$
\max S=k_n\ge n\ge T(H),\qquad
\sum_{k\in S}k\ge\sum_{i=1}^{n}i
 =\frac{n(n+1)}2\ge\frac{T(H)(T(H)+1)}2.
$$

$S_* =\{1,\ldots,T(H)\}$ 充分，其基数、最大索引和索引和恰等于这三个下界，所以达到它们的是同一个表。$H=1$ 时 $S_*$ 为空，三个量均为零；其它表各量非负，结论仍成立。

这里第 $k$ 问从重置副本单独执行 $k$ 次替换，故总替换次数正是索引和。这个等式的计费契约不包括副本或重置成本、算术、存储，也不允许把不同问题的推进前缀共享后仍按此式主张最优。若允许单轨迹复用、保存中间状态或不破坏当前状态的读出，成本函数已改变；本定理不对那些函数断言最优。$\square$

## 140. 初始停滞、二进异常及模 5040 的一致特化

**推论 140.1（奇素数的完整初始停滞区间）。** 对奇素数 $p$，令 $r=r_1$、$s=\nu_p(F_r)$。复用定理 126.6 的准确秩律

$$
r_j=r p^{\max(j-s,0)}.
$$

则 $N_{\mathrm{nonadaptive}}(p)=r-\mathbf1_{\{r=p+1\}}$，其充分表在满轨道时恰需至少 $r-1$ 个不同模 $r$ 相位，非满时恰需全部 $r$ 个。对 $e\ge2$，

$$
N_{\mathrm{nonadaptive}}(p^e)=
\begin{cases}
r,&2\le e\le s,\\
(p-1)r p^{e-s-1},&e>s.
\end{cases}
$$

第一支的准确条件是全部模 $r$ 相位；第二支令 $R=r p^{e-s-1}$，准确条件是在每个模 $R$ 父类中至少测试 $p-1$ 个不同模 $pR$ 子类。

证明。$e=1$ 直接代入首层条件和定理 139.1。若 $2\le e\le s$，则 $r_e=r_{e-1}=r$，所以定理 138.3 的停滞条件是全模 $r$ 覆盖，定理 139.1 给准确数 $r$。若 $e>s$ 且 $e\ge2$，则 $r_{e-1}=r p^{e-s-1}=R$、$r_e=pR$，增长条件及其基数下界给第二支。$s=1$ 时停滞区间为空；$s>1$ 时每个初始停滞层均保留。先停滞再增长后，末层条件仍由引理 137.1 覆盖全部此前层及每个含量的剩余精度。这一应用包括 $p=5$，没有假定所有奇素数的 $s$ 都等于一。$\square$

**推论 140.2（二进各指数的准确条件）。** 复用定理 126.6 的 $r_1=3,r_2=6$ 及 $r_j=3\cdot2^{j-2}$（$j\ge3$）。各个模 $2^e$ 的最小非自适应查询数和充分表的充要条件如下：

| 指数 $e$ | $N_{\mathrm{nonadaptive}}(2^e)$ | 同一个 $S$ 的准确条件 |
| --- | --- | --- |
| 140.2：$e=1$ | $2$ | 至少两个不同模 $3$ 剩余 |
| 140.2：$e=2$ | $3$ | 覆盖全部模 $3$ 剩余 |
| 140.2：$e=3$ | $6$ | 覆盖全部模 $6$ 剩余 |
| 140.2：$e\ge4$ | $3\cdot2^{e-3}$ | 覆盖全部模 $3\cdot2^{e-3}$ 剩余 |

证明。首层 $r_1=3=p+1$，故需两个相位。$e=2$ 为 $3\to6$ 的增长；$p-1=1$，所以每个模 3 父类至少测一个子类，恰等价于全模 3 覆盖。$e=3$ 是 $6\to6$ 的真实停滞，必须测每个模 6 相位，不能用增长条件替代。$e\ge4$ 都增长，父秩为 $r_{e-1}=3\cdot2^{e-3}$；每父类测一个子类恰为覆盖全部父类，不要求其两个子类都测。代入定理 139.1 给表中的数值。$e=3$ 与 $e=4$ 的数值都为 6，但前者来自停滞、后者来自增长，这两个理由保持区别。$\square$

**推论 140.3（模 5040 的同一表判据及契约边界）。** 对 $5040=16\cdot9\cdot5\cdot7$，一般判据恰化为定理 128.3 的四个条件：全模 6 覆盖；每个模 4 父类至少两个不同模 12 子类；全模 5 覆盖；至少七个不同模 8 相位。它们须由同一个 $S$ 同时满足。局部最小数依次为 $6,8,5,7$，全局最小数为 8，由 $\{1,\ldots,8\}$ 同时达到最大索引 8 和独立重置替换次数和 36。

证明。模 16 用推论 140.2 的 $e=4$，父秩为 6，需全模 6 覆盖。模 9 的秩为 $4,12$，是 $p=3$ 的增长，故四个父类各需两个不同子类，准确数为 $12-4=8$。模 5 的首层秩为 $5<6$，无命中方向存在，需全部五个相位；模 7 的首层秩为 $8=p+1$，需至少七个相位。所用小素数秩及轨道满否来自定理 120.5、126.6，局部数值也与命题 126.7 一致。定理 139.1 取四值之最大得 8，定理 139.2 给最大索引 8 和索引和 $8\cdot9/2=36$。这些正是定理 128.3、128.4 的全局非自适应结论。

本推论与一般结论均只使用定义 136.1 的全局量词。§127 的自适应策略允许下一问依赖答案，§128 的已知数量问题允许时间表依赖免费给定的确切 $n$，而固定通用表再用 $n$ 解码又是另一种量词次序；这里的下界没有转移到这些契约。引理 138.1 的见证允许不同 $n$，只证明全部实际来源上的全局下界。较早的充分长度仍为充分长度，定理 126.5 的准确连续时域仍是连续任务的结论；新增的相位计数说明任意稀疏索引也不能减少非自适应查询数。$\square$

## 追加锚（本行以下为增补区）

## 141. 五种 FIB 素项窗口与同一来源的完整剩余时间切面

**本批导航与范围。** 本节把 §§57–58、104、116 的五窗语法接到实际来源的时间观察；§142 给原始时间损失的闭包。沿用 §§117–133 的原子替换与实际组成，不改判既有条目。这里以及后续加权桥是参考层纸面推导，有限实验另列；没有新增 Lean 声明、冻结或覆盖。依据 CLAUDE §1.2，纯理论追加不以摄入为前置。

### 141.1. 五类的位序与来源合同

用户的 $[\mathrm{null},2,3,2\ 5,5]$，在 §104 的低位优先坐标下依次是

$$
000,\quad100,\quad010,\quad101,\quad001.
$$

首窗权重为 $(2,3,5)$，故 $2\ 5$ 是同一块内选 $\{2,5\}$，数值为 7。下一窗权重为 $(8,13,21)$，不会再次自动得到全素数窗口。`null` 仍消耗三个位置；它不是 End。单位位、相邻禁令、接缝和最高非零窗的 End 条件均保持 §104 原合同，计数与密度复用 §116.6。窗口分类、整数乘法素因子与下文时间秩是三个不同索引。

实际组成记为 $(a,b)\in\mathbb N^2$，数量与下一数量分别为 $n=2a+3b$、$z=3a+5b$。替换 $\beta=\rho(\alpha)$ 的组成作用是 $M(a,b)=(b,a+b)$，因而 $N_0=n,N_1=z,N_{d+2}=N_{d+1}+N_d$。对 $d\ge1$，

$$
N_d=F_{d-1}n+F_dz,\qquad F_0=0, F_1=1.
$$

固定 **模数** $H\ge1$，选择数量 $n=6H$ 的实际来源族

$$
(a_t,b_t)=(3H-3t,2t),\quad z_t=9H+t,
\qquad 0\le t<H. \tag{141.1}
$$

全部坐标非负，同一 $t$ 在所有时刻保持同一来源。固定 $n=6H$ 的完整实际族还含 $t=H$；这里有意省去端点 $(0,2H)$，使相位恰为一套均匀模 $H$ 剩余。省去端点是统计模型选择，不是来源不存在。$H$ 不是数量 $n$，更不是把 5040 当作所有来源的共同数量。

### 141.2. 单时刻与固定多时刻纤维

**命题 141.1（完整剩余时间切面）。** 在式 (141.1) 的来源族，观察 $Y_d(t)=N_d(t)\bmod H$，含 $Y_0=0$。令

$$
g_d=\gcd(H,F_d),\qquad M_d=H/g_d.
$$

则 $Y_d(t)=F_dt\bmod H$，且

$$
Y_d(t)=Y_d(u)\quad\Longleftrightarrow\quad t\equiv u\pmod {M_d}. \tag{141.2}
$$

对预先固定的有限时间集合 $D$，同时观察全部 $Y_d$ 的纤维为模

$$
M_D=\mathop{\mathrm{lcm}}_{d\in D}M_d
=\frac H{\gcd(H,(F_d)_{d\in D})} \tag{141.3}
$$

的剩余类；空 $D$ 取分母 $H$、$M_D=1$。特别地 $M_{\{d,e\}}=H/\gcd(H,F_{\gcd(d,e)})$。

**证明。** 数量公式消去 $6H,9H$ 后给 $Y_d$。写 $H=g_dM_d,F_d=g_dc_d$，有 $\gcd(c_d,M_d)=1$；$H\mid F_d(t-u)$ 当且仅当 $M_d\mid t-u$。多个同余取交即 lcm；逐素数比较赋值得第二式，再用 Fibonacci 强整除律得双时刻式。$d=0$ 时 $g_0=H$，观察恒定，也符合公式。$\square$

这使用标准 gcd 消去（Mathlib `Nat.ModEq.cancel_left_div_gcd` 及整数版本），并没有新造消去定理。固定多时刻的公式不能直接替代依赖此前读数选择时刻的自适应合同。

三种读数必须区分：上述读数是 **完整模 $H$ 剩余**；若读取整数 $N_d$，在 $d\ge1$ 时 $F_d>0$，同一数量族上的不同 $t$ 已被分开；若只读 $\gcd(N_d,H)$，例如 $d=1,H=5040$ 的 $t=1,11$ 都给 1，却有不同完整剩余。后者不能直接套用式 (141.2)，应回到 §§119–133 的 gcd 行为合同。

## 142. 原始时间损失的秩闭包与 5040 目录

### 142.1. 可达损失与最小连带损失

对正整数 $m$，记 $R(m)$ 为最小正指标满足 $m\mid F_{R(m)}$，并取 $R(1)=1$。它存在：模 $m$ 的相邻 Fibonacci 对由可逆有限状态递推作用，初态 $(0,1)$ 必在正时间返回。已有 `FibonacciRank.fibonacci_entry_point` 给

$$
m\mid F_d\quad\Longleftrightarrow\quad R(m)\mid d.
$$

这里允许合数 $m$；素数上界不是这一整除等价的必要条件。对正除数 $g\mid H$ 定义

$$
C_H(g)=\gcd(H,F_{R(g)}). \tag{142.1}
$$

**定理 142.1（原始时间损失的闭包）。** 存在正时刻 $d$ 满足 $\gcd(H,F_d)=g$，当且仅当 $C_H(g)=g$。在 $H$ 的正除数偏序中，$C_H$ 扩张、单调、幂等，且 $R(C_H(g))=R(g)$。它是包含所要求损失 $g$ 的最小可达损失。

**证明。** 若 $g$ 在 $d$ 实现，则 $R(g)\mid d$，故 $F_{R(g)}\mid F_d$，从而 $C_H(g)\mid\gcd(H,F_d)=g$；反向 $g\mid C_H(g)$ 直接成立。固定点在时刻 $R(g)$ 实现。若 $g\mid h$，则 $R(g)\mid R(h)$，所以 $C_H(g)\mid C_H(h)$。又 $g\mid C_H(g)$ 给 $R(g)\mid R(C_H(g))$，而 $C_H(g)\mid F_{R(g)}$ 给反向整除，故秩相等并得到幂等。若可达 $h$ 包含 $g$，单调性给 $C_H(g)\mid C_H(h)=h$。$\square$

### 142.2. 5040 的全部损失

**实例 142.2（原始时间目录）。** 对 $H=5040=2^4 3^2 5\cdot7$，

$$
\begin{array}{c|rrrrrrrr}
m&2&4&8&16&3&9&5&7\\\hline
R(m)&3&6&6&12&4&12&5&8
\end{array}
\qquad R(5040)=120.
$$

$1\le d\le120$ 的全部不同 $g_d$ 及首次出现时刻为

| 损失 $g_d$ | 1 | 2 | 3 | 5 | 8 | 10 | 15 | 21 | 40 | 105 | 144 | 720 | 1008 | 5040 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 首时刻 $d$ | 1 | 3 | 4 | 5 | 6 | 15 | 20 | 8 | 30 | 40 | 12 | 60 | 24 | 120 |

**核验与完备性。** 每个素数幂的秩可由有限模递推直接检验；$p^k\mid F_d$ 恰由表中的秩整除 $d$ 决定，所有秩都整除 120，所以一段 $1,\ldots,120$ 穷尽损失。这不把 120 称作完整 Fibonacci 剩余对的周期。可复用的精确枚举见 [temporal_projection.py](../../reports/fib-robin-boundary/temporal_projection.py) 与其 [结果](../../reports/fib-robin-boundary/temporal_projection.json)，包括 $H=1,2,3,6,8,12$ 的边界诊断。

特别地 $C_{5040}(7)=\gcd(5040,F_8)=21$；要求原始时刻只丢失一层 7、完整保留其它轴，即要求 $M_d=720$，不可达。实际 $d=8$ 给 $M_8=240$，而 $d=4$ 给 $M_4=1680$。2 轴也有 $R(4)=R(8)=6$，不能逐层由原始时间切开。

**后处理边界。** $F_1=1$，故 $Y_1=t\bmod H$ 已保留完整相位，对任何 $M\mid H$ 可后处理得到 $t\bmod M$。因此上述不可达性只限制直接形如 $Y_d$ 的原始时间纤维，绝非“任何实验或算法都无法得到素切面”的断言。新增接枝、重置、自适应 gcd、读整数，以及比较两个总体能量，都各自改变观察或操作合同。

**来源与证据层。** 五窗来自本卷既有语法，秩整除和强整除来自仓内/钉版 Mathlib；闭包是它们的纸面综合，不主张原创。精确整数枚举只覆盖所列有限模数，尚未编译本节一般闭包与实际来源桥。实现由调用方已协调的研究结论与单一实施席核算汇合；独立评审由调用方承担。

## 追加锚（本行以下为增补区）

## 143. 同源加权投影与非负时间秩壳

**本批导航。** 在 §§141–142 的完整剩余合同上，§143 从同一个均匀相位定义体与边界，§144 接到 Robin 精确增量、种子射线和新增素轴的缺口。新增一般桥仍是纸面推导；既有投影、秩整除、除数和公式是输入，不另造 bind-only Lean 包装。

### 143.1. 加权的除数探针与可见能量

在式 (141.1) 的同一均匀相位 $t\in\mathbb Z/H\mathbb Z$ 上用归一化内积 $\langle f,h\rangle=H^{-1}\sum_t f(t)h(t)$。对每个 $q\mid H$，置 $f_q(t)=\mathbf1_{q\mid t}$。对 $M\mid H$，令 $P_M$ 为按 $t\bmod M$ 的纤维取条件平均的正交投影。

**命题 143.1（体与商边界）。** 记 $Z(H)=\sigma(H)/H$，则

$$
\begin{aligned}
(P_Mf_q)(r)&=\frac{\gcd(q,M)}q\mathbf1_{\gcd(q,M)\mid r},\\
Z(H)&=\sum_{q\mid H}\|f_q\|_2^2=\sum_{q\mid H}\frac1q,\\
V_M(H)&:=\sum_{q\mid H}\|P_Mf_q\|_2^2
=\sum_{q\mid H}\frac{\gcd(q,M)}{q^2},\\
E_M(H)&:=\sum_{q\mid H}\|f_q-P_Mf_q\|_2^2
=Z(H)-V_M(H)\ge0. \tag{143.1}
\end{aligned}
$$

**证明。** 联立 $t\equiv r\pmod M,t\equiv0\pmod q$ 的相容条件是 $\gcd(q,M)\mid r$；相容时在该纤维中所占比例为 $\gcd(q,M)/q$。有 $1/\gcd(q,M)$ 的纤维相容，平方并取平均给第二个范数公式。最后逐探针用正交投影的勾股分解。$\square$

这些是 **逐探针能量之和**，即直和空间的范数；没有换成 $\|\sum_q f_q\|^2$，后者会多出 $\langle f_q,f_s\rangle=1/\mathrm{lcm}(q,s)$ 的交叉项。归一化探针 $\sqrt q f_q$ 的权重是 $1/q$，这也解释“加权”的含义。CRT 乘积从同一均匀相位的联合分布导出，未分别优化各轴的来源。改变相位分布，或者补回省去的端点并按 $H+1$ 个来源平均，均须重算公式。

写 $H=\prod_p p^{a_p},M=\prod_p p^{b_p}$，$0\le b_p\le a_p$，则

$$
v_{p,a}(b)=\sum_{j=0}^a p^{\min(j,b)-2j},\qquad
V_M(H)=\prod_{p\mid H}v_{p,a_p}(b_p),\qquad
Z(H)=\prod_{p\mid H}v_{p,a_p}(a_p). \tag{143.2}
$$

空积给 $H=1$ 时 $Z=V=1,E=0$。这些乘积只是有限除数和的乘法分解，不给予不同实际来源之间的联合极值。

### 143.2. 时间 Möbius 反演只按零秩分层

定义第 $k$ 层损失代价（$1\le k\le a$）

$$
\ell_{p,k}=\log v_{p,a}(a-k+1)-\log v_{p,a}(a-k)>0.
$$

深度用 $a-k$ 而非 $k$：事件 $p^k\mid F_d$ 表示从原商指数 $a$ 向下已丢失至少 $k$ 层。令 $V_d^{\rm time}(H)=V_{H/\gcd(H,F_d)}(H)$，并对正 $d$ 定义

$$
L_H(d)=\log\frac{Z(H)}{V_d^{\rm time}(H)},\qquad
A_H(r)=\sum_{d\mid r}\mu(r/d)L_H(d).
$$

**定理 143.2（原始时间秩壳）。** 有

$$
\begin{aligned}
L_H(d)&=\sum_{p^k\mid H\,;\,R(p^k)\mid d}\ell_{p,k},\\
A_H(r)&=\sum_{p^k\mid H\,;\,R(p^k)=r}\ell_{p,k}\ge0,\\
L_H(d)&=\sum_{r\mid d}A_H(r). \tag{143.3}
\end{aligned}
$$

此处 $p$ 只遍历素数，$1\le k\le a_p$。非零壳的秩均整除 $R(H)$。

**证明。** 局部 $v(b+1)>v(b)>0$，因为至少 $j=b+1$ 项严格增加。式 (143.2) 取对数后逐轴望远镜相消，已丢失层数为 $\min(a_p,\nu_p(F_d))$；用秩整除替换每层条件得首式。标准除数 Möbius 反演使用 $\sum_{d\mid r,\,s\mid d}\mu(r/d)=\mathbf1_{r=s}$，给第二、三式。最后 $p^k\mid H\mid F_{R(H)}$ 给支撑界。$\square$

$A_H$ 是规范的 **秩壳**，不是唯一素轴。对于 5040，精确的 $\exp(-A_H(r))$ 为

| 秩 $r$ | 3 | 4 | 5 | 6 | 8 | 12 |
| --- | --- | --- | --- | --- | --- | --- |
| $\exp(-A_H(r))$ | $61/62$ | $37/39$ | $13/15$ | $213/244$ | $25/28$ | $31031/47286$ |
| 所合并的 $p^k$ | 2 | 3 | 5 | 4、8 | 7 | 16、9 |

其它壳为零。分数由式 (143.2) 的有限有理数给出；程序另用 $\prod_{d\mid r}(V_d^{\rm time}/Z)^{\mu(r/d)}$ 检验反演。相同秩的层不能凭这组 $L_H(d)$ 唯一拆开为独立未知代价，因为它们具有完全相同的时间指示函数；已知 $H$ 的算术公式仍可分别计算代价。时间 Möbius 系数在这里非负，不是整数求和中的带符号 Mertens 抵消，也不给其平方根界。

### 143.3. 两个时间能量可隔离 7 增长

**推论 143.3（共同背景消去）。** 对每个 $7\mid H$，

$$
\frac{Z(7H)}{Z(H)}
=1+\frac{1-V_8^{\rm time}(H)/V_4^{\rm time}(H)}6. \tag{143.4}
$$

**证明。** $F_4=3,F_8=21$，所以两个时间商在所有非 7 轴完全相同；在 7 轴恰从 $a$ 降至 $a-1$。故比值等于 $v_{7,a}(a-1)/v_{7,a}(a)$。两局部量之差为 $6/7^{a+1}$，而 $Z(7^{a+1})-Z(7^a)=1/7^{a+1}$，相除得式。$\square$

5040 时 $V_8^{\rm time}/V_4^{\rm time}=25/28$，故 $Z(35280)/Z(5040)=57/56$。这里比较的是同一来源分布上的两个总体能量，不是单个来源的相位标签；它与 $C_{5040}(7)=21$ 相容。一般素数不能只凭最小秩声称其壳是单层，表中的 6、12 已给反例。

## 144. Robin 增量、种子射线与扩张支撑的剩余估计

### 144.1. 旧体与未来体的精确增量

**命题 144.1（素乘增量）。** 对任意素数 $p$ 和 $H\ge1$，写 $H=p^aK,p\nmid K$，允许 $a=0$，有

$$
G_p(H):=Z(pH)-Z(H)=\frac{Z(K)}{p^{a+1}}
=\frac p{p-1}E_H(pH). \tag{144.1}
$$

若 $p\mid H$，还可用旧体切面：

$$
G_p(H)=\frac{E_{H/p}(H)}{p-1}. \tag{144.2}
$$

**证明。** $Z(p^a)=1+\cdots+p^{-a}$，差为 $p^{-(a+1)}$。式 (143.1) 的局部损失只在最高探针层出现：旧体为 $(p-1)p^{-(a+1)}Z(K)$，未来体为 $(p-1)p^{-(a+2)}Z(K)$。$\square$

$p\nmid H$ 时不存在旧体的 $H/p$ 商；$E_H(pH)$ 是 **未来体** 上的新探针层，不是旧体零误差。未来模数的均匀相位约化到模 $H$ 给旧相位分布，这是已声明的耦合；实际来源数量由 $6H$ 换为 $6pH$，并未称它为固定数量来源的 FIB 时间演化。

对 $H>1$ 定义 Robin 余量与预算

$$
\Delta(H)=e^\gamma\log\log H-Z(H),\qquad
b_p(H)=e^\gamma\log\left(1+\frac{\log p}{\log H}\right).
$$

精确关系为 $\Delta(pH)=\Delta(H)+b_p(H)-G_p(H)$。特别地，一个便于核验的充分条件是

$$
G_p(H)\le e^\gamma\frac{\log p}{\log(pH)}\le b_p(H), \tag{144.3}
$$

因为 $\log(1+x)\ge x/(1+x)$。$\Delta(H)>0$ 与此条件一起保证下一步严格为正；它不是必要条件。

### 144.2. 固定素轴的种子传播

**命题 144.2（种子射线）。** 设 $p\mid H$、$\Delta(H)>0$，并且 $G_p(H)\le b_p(H)$，则对所有整数 $j\ge0$，$\Delta(p^jH)>0$。

**证明。** 每步增量 $G_p(pH)=G_p(H)/p$。写 $L=\log H,h=\log p$，因 $p\mid H$ 有 $L\ge h>0$，而

$$
L(L+2h)^2-(L+h)^3=h(L^2+Lh-h^2)>0.
$$

所以 $((L+2h)/(L+h))^2>(L+h)/L$，取对数得 $b_p(pH)>b_p(H)/2\ge b_p(H)/p$。归纳保持预算覆盖与正余量。$\square$

$H=10080,p=2$ 是有证书的例子：

$$
Z(10080)=\frac{39}{10},\quad G_2(10080)=\frac{13}{420},\quad
\Delta(10080)>\frac2{125},\quad b_2(10080)>\frac{89}{750}>\frac{13}{420}.
$$

用 $e^\gamma>89/50$、$\log\log10080>11/5$ 得余量界；用 $\log2>2/3$、$\log20160<10$ 与式 (144.3) 得预算界。精确区间程序使用 atanh 对数展开的有理尾界，$N=1000$ 的调和数以及既有 `RobinRationalBasis.eulerMascheroni_remainder_bounds` 的两侧界；指数下界用 $\gamma>577/1000$ 后的六项 Taylor 下和。输出端点向外取整，不以浮点近似判正。

这只给 $10080\cdot2^j$ 射线的一种预算解释；既有 `SevenSmooth.robin_seven_smooth` 已覆盖它及全部大于 5040 的七光滑整数，故不称为新增安全族。固定有限素支撑下的 Euler 乘积上界也不能控制不断加入新素数的路径。

### 144.3. 累计余量是目标，逐步非负仅为充分策略

对同一实际整数链 $H_{i+1}=p_iH_i$，任意 $m$ 都有

$$
\Delta(H_m)=\Delta(H_0)+\sum_{i<m}\bigl(b_{p_i}(H_i)-G_{p_i}(H_i)\bigr). \tag{144.4}
$$

因而从一个正种子覆盖某条链所需的准确条件是对每个前缀，右侧仍严格为正。允许某几步使用已有余量，不要求每一步的增益都严格为正。要借此证明全部 $n>5040$ 的 Robin 不等式，还须构造覆盖全部目标的种子/路径，并证明同一整数历史上的累计预算；本节没有这样的扩张素支撑控制。

§92 的带符号尾积分目标仍是另一条主线表述：在其经典解析输入下，要证明最终所有 $x$ 的 $\Phi(x)\ge-1/(2\sqrt x\log x)$，而不是仅求非负投影壳。独立优化各素轴、不同时间的边缘值或不同来源的最好余量，均不能填入式 (144.4) 或 §92 的联合 $(\mathcal Z,e)$ 状态。

**核验边界。** [精确实验](../../reports/fib-robin-boundary/temporal_projection.py) 从小模数的真实纤维平均另算投影范数，检查 5040 全部秩壳、旧/未来体增量及 10080 有理种子。一般加权桥、时间反演组合与射线传播为未编译纸面推导；既有组件的局部编译不升级它们的证据身份，也不证明 RH。

## 追加锚（本行以下为增补区）

## 145. 五窗递归中的守恒、异号扇区与勾股的适用对象

**本批导航。** 本节区分既有黄金二次型、条件投影与窗口细化的三种守恒；§146 把 Robin 主线与替代判据接到实际缺失的估计。所有对 RH 的全称估计仍未建立，不改判旧卷或冻结结果。

### 145.1. 计数坐标与组成坐标不能混用

按输出接缝 0、1 排列的计数列向量 $(x,y)^\mathsf T$，每读一窗的转移为

$$
C=\begin{pmatrix}3&2\\2&1\end{pmatrix}
=T^3,\qquad T=\begin{pmatrix}1&1\\1&0\end{pmatrix}.
$$

输入接缝 0 有三个输出 0、两个输出 1 的字母；输入接缝 1 仅有两个输出 0、一个输出 1 的字母。这正是 §116.6 已有计数，不再当作新分类。

**命题 145.1（异号与两步守恒）。** 在计数坐标令 $Q(x,y)=x^2-xy-y^2$，则

$$
Q(Tv)=-Q(v),\qquad Q(Cv)=-Q(v),\qquad Q(C^2v)=Q(v).
$$

在实际组成坐标 $M(a,b)=(b,a+b)$ 中，对应的形式为 $Q'(a,b)=a^2+ab-b^2$，满足 $Q'(Mv)=-Q'(v)$。

**证明。** 首式直接展开，$C=T^3$ 给后两式；组成式也直接展开，或交换两个坐标后取相反数。$\square$

这复用 §22 的黄金二次型和 `GoldenAntiIsometry.golden_anti_isometry`。一次转移把正、负扇区互换，零锥保持；两次转移保存原值。因此同一递归可以同时有扇区交换和两步守恒。$Q$ 不是正定能量；符号交替本身也不是物理学意义的自发对称破缺。若要作后者解释，还缺物理状态、作用量/测度、对称群及所选状态等模型对应。

本库实际可定位的“勾股分类”包括 [GICT 附录 E.46](GICT.md) 的三角群/度量区分，以及 `SeatTowerArithmetic.pythagorean_gate_iff_eisenstein_norm` 的精确关系

$$
(\gamma_0-2\beta)^2+3\gamma_0^2=4m(m+1)
\quad\Longleftrightarrow\quad
\beta^2-\beta\gamma_0+\gamma_0^2=m(m+1).
$$

它是整坐标的 Eisenstein 范数门，不自动给出 FIB 五窗到全部原始勾股三元组的分类映射，也不能用名称把它认作 Berggren 树。

### 145.2. 正定投影守恒与窗口概率守恒

对同一概率空间上的两个嵌套观察 $\mathcal F\subseteq\mathcal G$，条件平均满足已有的投影勾股关系

$$
\|f-\mathbb E[f\mid\mathcal F]\|_2^2
=\|f-\mathbb E[f\mid\mathcal G]\|_2^2
+\|\mathbb E[f\mid\mathcal G]-\mathbb E[f\mid\mathcal F]\|_2^2. \tag{145.1}
$$

它适用于 §143 的逐探针直和。精细读数把旧残差分解为新残差和已取得的变化量，两项非负；这不是 $Q$ 的符号交换。时间 $d$ 增加也不保证观察按包含关系变细，应先比较 $M_d$ 的整除关系，再使用嵌套投影公式。

在 §116 的自然密度合同中，设 $\varphi=(1+\sqrt5)/2$。五窗的条件概率对输入接缝 0 为三份 $\varphi^{-3}$、两份 $\varphi^{-4}$；对输入接缝 1 为两份 $\varphi^{-2}$、一份 $\varphi^{-3}$。因此

$$
3\varphi^{-3}+2\varphi^{-4}=1,\qquad
2\varphi^{-2}+\varphi^{-3}=1. \tag{145.2}
$$

这是合法延伸的概率质量守恒，并非五个字母等概率。任意固定有限层的柱集划分都保持总质量；将一片叶子细化为全部合法后继仍保持它的质量。程序若枚举规范整数，应同时保留单位位、接缝与 End，否则会重复零窗尾或纳入非法串。该自然密度与 §143 的模 $H$ 均匀来源分布是不同合同，没有默认的保测等同。

有限分支平均控制不了每个整数的 Robin 余量：即使一个分支的条件平均为正，其中仍可有负值。式 (145.1) 的非负项只给分解，尚不给 $G_p(H)$ 与 $b_p(H)$ 的大小比较。“体”在本批具体指除数探针的直和，“边界”指观察投影保留或丢失的能量；要上升为 RH 判据，仍须下节的算术尺度和全称量词。

## 146. Robin 主线与四条替代路线的准确缺口

### 146.1. 判据地图与共同来源

下表的等价判据来自所列经典来源或既有仓内接口。本批没有证明表中待估计量满足目标界；“已能表达判据”与“已达到判据”分别记述。

| 路线 | 载体与精确目标 | 与本批关系及剩余估计 |
| --- | --- | --- |
| Robin（主线） | 每个整数 $n>5040$，$Z(n)<e^\gamma\log\log n$ | §§143–144 精确给素乘增量；缺少覆盖全部目标整数、允许新素轴进入的共同路径累计余量界。固定 5040 或七光滑族不够。 |
| 七—十 Mertens 边界 | 对每个 $\varepsilon>0$，$B(X)=O_\varepsilon(X^{1/2+\varepsilon})$，$X\to\infty$ 经过全部实截断 | $B(X)=\sum_{X/10<r\le X/7,(r,70)=1}\mu(r)$。既有 `MertensBoundary.power_bounds_iff` 把任意正幂界与普通 $M(X)$ 连接；再用经典 Mertens–RH 判据。缺少带符号抵消，§143 的非负时间壳并不给该界。 |
| Weil 的素数—Archimedean 能量 | 对每个仓内偶、光滑、紧支撑复测试函数 $f$ 和每个包含其支撑的半径 $L$，满足式 (146.1) | 实际 zeta 零点载体已由 `UnconditionalCanonicalZeroData.zetaZeroData` 提供；缺口是所有测试函数的能量估计，不是载体存在性。 |
| Lagarias | $h_n=\sum_{j=1}^n1/j$，对每个 $n\ge1$，$\sigma(n)\le h_n+e^{h_n}\log h_n$，等号仅 $n=1$ | 同一个除数和体，改变预算且消去陈述中的未知常数；仍缺对全部整数的上界，换预算不自动提供它。 |
| Báez-Duarte 的 Nyman–Beurling 加强式 | 在 $L^2((0,\infty),dx)$ 中，$\chi_{(0,1]}$ 属于 $\{\{1/(mx)\}:m\in\mathbb N_{>0}\}$ 的线性张成之闭包 | 给一个可优化的逼近任务；缺少趋零残差与全域尾部控制。FIB 的有限模数投影尚无连接这些分数部分函数并保误差的桥。 |

Mertens 边界复用 §§66–67；只在 Fibonacci 端点检查不是全部实截断的界。已有 $[91,130)$ 内相对端点 $89,144$ 的采样障碍继续适用。改为更多有限端点仍须给端点之间和无穷尺度的统一控制，不能重命名采样为全称估计。

### 146.2. 实际 Weil 能量与 Li 的索引范围

为固定表中 Weil 量的归一化，令

$$
\begin{aligned}
T_x(f)&=\int_{\mathbb R}|f(y)-f(y-x)|^2\,dy,\\
W_L&=\sum_{2\le n\le e^{2L}}\frac{\Lambda(n)}{\sqrt n},\qquad
J_L(f)=\sum_{2\le n\le e^{2L}}\frac{\Lambda(n)}{\sqrt n}T_{\log n}(f),\\
J_\infty(f)&=\int_0^\infty\frac{e^{-x/2}}{1-e^{-2x}}T_x(f)\,dx,\qquad
c_\infty=\Re\psi(1/4)-\log\pi,
\end{aligned}
$$

其中 $\psi$ 为 digamma，和按整数截断，$\Lambda$ 自动去掉非素数幂。对于 $\operatorname{supp}f\subseteq[-L,L]$，准确目标是

$$
(2W_L-c_\infty)\|f\|_2^2
\le2\left|\int_{\mathbb R}e^{x/2}f(x)\,dx\right|^2
+J_\infty(f)+J_L(f). \tag{146.1}
$$

`PrimeArchimedeanPoincareCriterion.rh_iff_primeArchimedeanPoincare` 取实际 `zetaZeroData`，得到此全称不等式与 RH 的既有接口。该旧模块注释所述 M1-b 存在性缺口已由后续载体构造填补；本批以当前声明的组合为准，不把旧注释继续当作现状，也不改写冻结模块。

`PrimeOnlyNoGap.prime_only_no_gap` 另给：圆上非负、可求和跳跃权重的能量，在非零 Fourier 模上之下确界为零。故不能用这种模型的素数项独自提供统一正谱隙；其可求和假设不能被丢弃后用于否定式 (146.1) 的实际临界素数权重和 Archimedean 项。有限矩阵正半定也不直接推出式 (146.1) 对全部 $f,L$ 成立。

Li 路线可复用 `CanonicalLiNonnegativeConverse.canonical_li_nonnegative_implies_rh`：实际完成 zeta 的规范系数

$$
\lambda_n=\frac1{(n-1)!}
\Re\left.\frac{d^n}{ds^n}\bigl[s^{n-1}\log\xi(s)\bigr]\right|_{s=1},\qquad n\ge1,
$$

若对 **每个** 正指标非负，便给 RH。这里引用的是这一既有充分方向；本批没有计算或证明全部系数非负。有限正壳 $A_H(r)$ 与 $\lambda_n$ 不是同一列，也未建立保号变换。既有 Li 曲率/圆测度结果同样须保持实际系数、共同测度和全部阶数条件，不能把任意有限 Gram 矩阵的正性代入。

### 146.3. 逼近路线的全域尾部与研究终点

把 Báez-Duarte 条件写成可执行目标：

$$
D_N^2=\inf_{c_1,\ldots,c_N\in\mathbb R}
\int_0^\infty\left|\chi_{(0,1]}(x)-\sum_{m=1}^Nc_m\left\{\frac1{mx}\right\}\right|^2dx
\longrightarrow0.
$$

对任何固定实系数，$x>1$ 上每个分数部分都是 $1/(mx)$，故

$$
\int_1^\infty\left|\sum_{m=1}^Nc_m\left\{\frac1{mx}\right\}\right|^2dx
=\left(\sum_{m=1}^N\frac{c_m}m\right)^2. \tag{146.2}
$$

这是全域目标的一项可精确检查的尾成本；仅最小化有限网格或 $(0,1)$ 的离散误差会漏掉它。有限维 Gram 正性保证目标非负，没有保证最优残差趋零。原论文还说明直接的 Möbius 截断不在该 Hilbert 范数中收敛，故“取 Möbius 系数即可”并不是可用的无条件实现。

本批更明确的可推进对象是：由原始时间读数算秩壳，用能够消去共同背景的比值识别某些素乘增量，再与 **同一整数链** 的累计 Robin 预算比较。余下决定性桥是扩张素支撑上的统一估计，或 §92 已列的最终带符号尾界。投影守恒、五窗分类与有限精确证书都没有填平这条解析缺口。

**来源与证据界限。** Lagarias, *An Elementary Problem Equivalent to the Riemann Hypothesis*, [arXiv:math/0008177v2](https://arxiv.org/abs/math/0008177v2)，Problem E、Theorem 1.1 及式 (1.2)；Báez-Duarte, *A Strengthening of the Nyman–Beurling Criterion for the Riemann Hypothesis*, [arXiv:math/0202141v2](https://arxiv.org/abs/math/0202141v2)，Theorem 1.1 与 §1，均按原文载体和量词引用。其它对应为本卷既有结果、仓内 Lean 组件及本批纸面综合；不主张文献穷尽或原创性。一般时间/投影/预算桥与外部判据的全文证明没有在本批形式化；有限结果和局部编译不构成 RH 证明。

## 追加锚（本行以下为增补区）

## 147. 时间秩壳的素乘上界与有界碰撞数的失效

**本批导航与合同。** 本节在 §§141–144 的同源均匀相位模型内给既有素轴增长的壳上界及其误差；§148 给有限素数符号反模型和 §6.4 的追加勘误。§§134–140 的实际接枝词及任意索引 gcd 识别保持各自合同，不替代这里的完整剩余读数与总体能量。新增结论均为纸面推导与有限实验，不是 Lean 证明；RH 所需的全称解析桥仍未建立。

### 147.1. 不要求素轴隔离的充分上界

**命题 147.1（既有素轴的秩壳控制）。** 设整数 $H\ge2$、素数 $p$ 且 $p^a\parallel H$、$a\ge1$，沿用 §143 的 $Z,V,\ell,A$，令 $r=R(p)$。则

$$
g_p(H):=\frac{Z(pH)-Z(H)}{Z(H)}
=\frac{1-e^{-\ell_{p,1}}}{p-1}
\le B_p(H):=\frac{1-e^{-A_H(r)}}{p-1}. \tag{147.1}
$$

等号当且仅当该壳除 $(p,1)$ 外没有其它损失层。对每个 $r>1$，置 $M_d=H/\gcd(H,F_d)$，还有

$$
e^{-A_H(r)}=\prod_{d\mid r}V_{M_d}(H)^{\mu(r/d)}. \tag{147.2}
$$

证明。写 $H=p^aK$、$p\nmid K$。式 (143.2) 给

$$
v_{p,a}(a)-v_{p,a}(a-1)=\frac{p-1}{p^{a+1}},\qquad
g_p(H)=\frac{p^{-(a+1)}}{v_{p,a}(a)}.
$$

相除即得式 (147.1) 的等式。定理 143.2 给 $A_H(R(p))\ge\ell_{p,1}>0$；$1-e^{-x}$ 严格递增，且每个其它层严格为正，遂得上界和等号条件。反演式中 $L_H(d)=\log Z(H)-\log V_{M_d}(H)$，而 $r>1$ 时 $\sum_{d\mid r}\mu(r/d)=0$，故 $Z$ 的系数消去，指数化给式 (147.2)。这不消去每个可见能量所需的同源均匀总体合同。$\square$

若已有独立成立的上界 $U(H)\ge Z(H)$，那么

$$
U(H)B_p(H)\le b_p(H)
\quad\Longrightarrow\quad \Delta(pH)\ge\Delta(H), \tag{147.3}
$$

其中 $b_p,\Delta$ 如 §144.1。证明只需 $G_p=Zg_p\le UB_p$ 与 Robin 精确增量式。这个充分条件允许相同秩不能分离，但 $U$ 必须另有依据；取 $U=Z$ 本身不给更便宜的算法或新的全局界，也不处理 $p\nmid H$ 的新轴。

### 147.2. 精确超额、相对隔离与两素数反例

令 $c_{H,p}=A_H(R(p))-\ell_{p,1}\ge0$，它是同秩其它层的总损失，不是 §142 的闭包 $C_H$。直接相减得

$$
B_p-g_p=\frac{e^{-\ell_{p,1}}(1-e^{-c_{H,p}})}{p-1}. \tag{147.4}
$$

若 $\eta\ge0$ 且 $c_{H,p}\le\eta\ell_{p,1}$，则 $B_p\le(1+\eta)g_p$：函数 $h(x)=1-e^{-x}$ 在 $x\ge0$ 上递增、凹且 $h(0)=0$，所以 $h((1+\eta)x)\le(1+\eta)h(x)$。这是需要另证的相对隔离条件；仅限制其它层的数目并不给它。

**实例 147.2（单层壳与共同秩）。** $H=5040,p=7$ 时壳只有 $(7,1)$，$e^{-A_H(8)}=25/28$，故 $B_7=g_7=1/56$。相反，$F_{19}=4181=37\cdot113$；19 为素数，两个素因子的秩都整除 19 且不为 1，故都为 19，且两者平方均不整除 $F_{19}$。在 $H=4181$，

$$
e^{-A_H(19)}=\frac{4373725}{4528023},\qquad
g_{37}=\frac1{1406},\quad g_{113}=\frac1{12882},\qquad
B_{37}=\frac{77149}{81504414},\quad B_{113}=\frac{77149}{253569288}.
$$

这些数由 $e^{-\ell_{37,1}}=685/703$、$e^{-\ell_{113,1}}=6385/6441$ 相乘并代入式 (147.1) 得到。反演只取得这个乘积，并未隔离 37 或 113。

**命题 147.3（两个碰撞素数已足以造成无界相对超额）。** 对 $H_a=37^a\cdot113$、整数 $a\ge1$，秩 19 壳恰含 $(37,1),(113,1)$ 两层，而且

$$
g_{37}(H_a)=\frac{36}{37(37^{a+1}-1)}\longrightarrow0,\qquad
B_{37}(H_a)\longrightarrow
\frac{1-6385/6441}{36}=\frac{14}{57969}>0. \tag{147.5}
$$

因此 $B_{37}(H_a)/g_{37}(H_a)\to\infty$。

证明。因 $37^2,113^2\nmid F_{19}$，没有更高层具有秩 19；$H_a$ 又没有其它素因子。局部几何和给所示 $g_{37}$，式 (147.1) 给 $e^{-\ell_{37,1}}=1-36g_{37}\to1$；113 指数恒为一，其层比恒为 $6385/6441$，故得到 $B$ 的正极限。真实 $Z(H_a)$ 仍受固定支撑 Euler 界 $(37/36)(113/112)$ 控制，而 $b_{37}(H_a)\to0$。任何 $U\ge Z(H_a)\ge1$ 都使 $UB_{37}$ 保留正下限，因此式 (147.3) 最终无法验证这条增量，即使真实 $G_{37}=Zg_{37}$ 指数衰减。这是否定有界碰撞数的估计充分性，不是否定 Robin。$\square$

## 148. 有限素数符号、数字正交与根节点常数分量

### 148.1. 同平方自由支撑的正均值反模型

**命题 148.1（任意固定有限素数集的符号模型）。** 固定有限素数集 $P$（允许为空），令 $Q=\prod_{p\in P}p$，对正整数定义

$$
f_P(n)=\mu(n)^2\prod_{p\in P}\bigl(1-2\mathbf1_{p\mid n}\bigr).
$$

它是有界乘法函数，$f_P(n)^2=\mu(n)^2$；对每个 $p\in P$、$p\nmid n$，有 $f_P(pn)=-f_P(n)$，并在全部 $P$-光滑整数上等于 $\mu$。对每个实数 $X\ge1$，

$$
\sum_{n\le X}f_P(n)
=c_PX+E_P(X),\qquad
c_P=\frac1{\zeta(2)}\prod_{p\in P}\frac{p-1}{p+1}>0,\qquad
|E_P(X)|\le3^{|P|+1}\sqrt X. \tag{148.1}
$$

证明。素数处的值在 $P$ 内为 $-1$、在其外为 $1$，每个指数至少二的素数幂处为零；互素乘法、符号规则及平方恒等式随之成立。对平方自由 $d$，设 $S_d(X)=\sum_{n\le X,d\mid n}\mu(n)^2$。用 $\mu(n)^2=\sum_{k^2\mid n}\mu(k)$ 得准确有限展开

$$
S_d(X)=\sum_{k\le\sqrt X}\mu(k)
\left\lfloor\frac X{\operatorname{lcm}(d,k^2)}\right\rfloor. \tag{148.2}
$$

令 $N=\lfloor\sqrt X\rfloor\ge1$。去掉取整的误差至多 $N$；因 $\operatorname{lcm}(d,k^2)\ge k^2$，补齐无限和的误差至多 $X\sum_{k>N}k^{-2}\le X/N\le2\sqrt X$。故总误差至多 $3\sqrt X$，与 $d$ 无关。绝对收敛系数的 Euler 乘积为

$$
\sum_{k\ge1}\frac{\mu(k)}{\operatorname{lcm}(d,k^2)}
=\prod_{p\mid d}(p^{-1}-p^{-2})\prod_{p\nmid d}(1-p^{-2})
=\frac1{\zeta(2)}\prod_{p\mid d}\frac1{p+1}. \tag{148.3}
$$

把定义中的有限乘积展开，得到 $\sum_{n\le X}f_P(n)=\sum_{d\mid Q}(-2)^{\omega(d)}S_d(X)$。主项因子化为式 (148.1) 的 $c_P$，误差系数的绝对值和为 $\sum_{d\mid Q}2^{\omega(d)}=3^{|P|}$，证明完毕。这里的正均值与渐近结论均固定 $P$；不把 $P$ 随 $X$ 增大时的误差当作统一平方根界。$\square$

在任意有限整数区间的均匀概率空间上，对任何合法 FIB 前缀划分及其细化，$f_P$ 都满足 §145.2 的条件投影勾股分解；每个柱集上的平方能量还与 $\mu$ 相同，因为二者逐点平方相同。这没有宣称二者的带符号柱集平均相同。故这些守恒和任意固定有限组新素数翻号规则，无法单独推出所有满足它们的函数都有 $O_\varepsilon(X^{1/2+\varepsilon})$ 总和；取 $0<\varepsilon<1/2$，式 (148.1) 即给反模型。这不是实际 $\mu$ 或 RH 的反例。

### 148.2. 已发表数字正交仍不控制常数模式

Drmota、Müllner、Spiegelhofer 的 *Möbius orthogonality for the Zeckendorf sum-of-digits function*，原始 [arXiv:1706.09680v1](https://arxiv.org/abs/1706.09680v1) Theorem 1（Proc. AMS，2018，[DOI:10.1090/proc/14015](https://doi.org/10.1090/proc/14015)）证明：令 $s_\varphi(n)$ 为规范 Zeckendorf 展开的数位和，则对**每个有界乘法函数** $m$，

$$
\sum_{1\le n\le X}(-1)^{s_\varphi(n)}m(n)=o(X). \tag{148.4}
$$

端点与原文 $n<N$ 的差为有界项。因命题 148.1 已核对乘法性和有界性，式 (148.4) 同时适用于 $m=\mu$ 和 $m=f_P$；取 $m=1$ 也表明这个数字奇偶观察的 Cesàro 均值为零。于是对这个中心化数字观察的渐近正交，可以与 $f_P$ 沿常数函数 $1$ 的正均值 $c_P$ 同时成立。它不控制未加数字权重的根节点总和，也没有在陈述中给出 RH 所需的平方根尺度。原文 Lemma 1 把固定低位条件写成 $(-1)^kn\varphi$ 模一的区间条件；这是数字柱集的表示，不是整数乘法符号的全尺度估计。

**实例 148.2（有限数字诊断）。** 对 $P=\{2,3,5,7\}$，$c_P=1/(12\zeta(2))$。在 $X=100000$，精确整数计算给

$$
\sum\mu=-48,\quad \sum\mu^2=60794,\quad \sum f_P=5064,\quad
\sum(-1)^{s_\varphi}f_P=326,\quad \sum(-1)^{s_\varphi}\mu=-230.
$$

所有和均取 $1\le n\le X$。[保留程序](../../reports/fib-robin-boundary/temporal_projection.py) 另保留 $X=100,1000,10000$、平方自由展开及秩壳碰撞的精确诊断，[结果](../../reports/fib-robin-boundary/temporal_projection.json) 只承担这些有限范围；式 (148.1) 的无穷结论由上面的证明承担，式 (148.4) 由所引原定理承担。

### 148.3. 素数种子的追加勘误与未解边界

**勘误 148.3（§6.4 的相邻指标论证）。** 旧证明称相邻 $n,n+1>3$ 中总有一个被 3 整除，此句错误，例如 $7,8$。保留其结论，改用 §57.1 的偶指标方法：当相邻对起点 $n\ge5$，其中一个指标为 $2m\ge6$，且 $1<F_m<F_{2m}$、$F_m\mid F_{2m}$，故相应项为合数；$n\le2$ 含非素项，只有 $n=3,4$ 给 $(2,3),(3,5)$。这修正证明的一步，不改两次完整恢复及 Fibonacci 替换的前提；本批壳估计也未用错误的被 3 整除断言。

**来源、产地与剩余目标。** 秩壳上界和超额是 §§143–144 的纸面推导，有限素数均值使用经典平方自由展开与 Euler 乘积，数字正交按上述原文的量词引用；不主张新颖性。调用方提供研究结论，本实施席核对推导、原文与有限数据，独立审查由调用方负责。当前障碍是同秩其它层的相对损失控制，以及实际 $\mu$ 在全部整数尺度上的带符号估计；有限分类、守恒、固定素支撑和数字正交均未填补它们。这里没有新增 Lean 声明或全局 Robin/RH 结论。

## 追加锚（本行以下为增补区）

## 149. 五窗包含细化与组成层的四相旋转

五窗 $[\mathrm{null},2,3,2\ 5,5]$ 对应合法位置集 $[\varnothing,\{2\},\{3\},\{2,5\},\{5\}]$。
其包含是偏序，例如 $\varnothing\subset\{2\}\subset\{2,5\}$；五个标签不是一条包含链。同层窗口柱集互斥，延伸前缀则把原柱集细分为包含于其中的合法后继柱集。
四分类 $[1,i,-1,-i]$ 在本节表示组成平面的四相旋转；它与上述包含、细化是不同关系，不能按标签数目相互替代。

**定义 149.1（组成坐标、共轭与四相）。** 取 $x=(a,b)^{\mathsf T}\in\mathbb Z^2$，基向量为 $\alpha=(1,0)^{\mathsf T}$、$\beta=(0,1)^{\mathsf T}$，约定

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}1&1\\0&-1\end{pmatrix},\qquad
C=MJ=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

$M$ 是替换 $\rho$ 的组成作用；在黄金坐标 $a+b\varphi$、$\varphi^2=\varphi+1$ 中，$J(a,b)=(a+b,-b)$ 表示 $\varphi\mapsto1-\varphi$ 的黄金共轭。
另用复坐标 $z=a+ib$ 表示同一有向平面，则 $Cx=(-b,a)$ 对应 $z\mapsto iz$。这个复坐标表示不把黄金乘法认作复数乘法。
本节的 $C$ 专指此旋转，区别于 §145.1 记为 $C=T^3$ 的接缝计数矩阵。

**命题 149.2（四相与递归的共轭关系）。** 在上述组成坐标中，

$$
M^2=M+I,\qquad J^2=I,\qquad JM=(I-M)J,\qquad C^2=-I,\quad C^4=I.
$$

若 $S=M^3$、$L=M^6$，则

$$
CMC^{-1}=I-M=-M^{-1},\qquad
CSC^{-1}=-S^{-1},\qquad CLC^{-1}=L^{-1}. \tag{149.1}
$$

证明。直接乘法给 $M^2=\left(\begin{smallmatrix}1&1\\1&2\end{smallmatrix}\right)=M+I$、$J^2=I$，以及
$JM=\left(\begin{smallmatrix}1&2\\-1&-1\end{smallmatrix}\right)=(I-M)J$；所列 $C$ 的平方为 $-I$。
由 $M(M-I)=I$ 得 $M^{-1}=M-I$，且 $C^{-1}=JM^{-1}$，所以

$$
CMC^{-1}=M(JMJ)M^{-1}=M(I-M)M^{-1}=I-M=-M^{-1}.
$$

共轭保持矩阵乘法，取三次、六次幂即得式 (149.1)。$\square$
这些恒等式属于组成层；有限矩阵的共轭关系本身没有构造 zeta 的零点载体或谱。

在此基下，$M$ 的轨道为 $\alpha\mapsto\beta\mapsto\alpha+\beta\mapsto\alpha+2\beta\mapsto\cdots$，而
$C$ 的轨道为 $\alpha\mapsto\beta\mapsto-\alpha\mapsto-\beta\mapsto\alpha$，对应 $1\mapsto i\mapsto-1\mapsto-i\mapsto1$。
负向量属于非负组成幺半群 $\mathbb N^2$ 的有向 $\mathbb Z^2$ 完备化，不是原非负词语法中的合法负字母；旋转也不自动保持接缝与 End 的合法性。

**命题 149.3（守恒须指定操作与量）。** 定义欧氏平方范数 $E(a,b)=a^2+b^2$，并沿用 §22 的黄金不定二次型 $Q(a,b)=a^2+ab-b^2$。则

$$
E(Cx)=E(x),\qquad E(Mx)-E(x)=2ab+b^2,\qquad
Q(Mx)=Q(Cx)=-Q(x). \tag{149.2}
$$

证明。$E(-b,a)=b^2+a^2$，而 $E(b,a+b)=a^2+2ab+2b^2$；后二式分别展开为
$Q(b,a+b)=-a^2-ab+b^2$ 与 $Q(-b,a)=b^2-ab-a^2$。因此 $M$ 一般改变 $E$，例如 $E(M\beta)=2\ne1=E(\beta)$；$M^2$ 和 $C^2$ 各自保持 $Q$，任意连续两次从 $M,C$ 中选取的操作也保持 $Q$。$\square$
这里 $Q$ 不是正定能量，$E$ 也不是 §143 的投影残差 $E_M(H)$；“守恒”不能省略操作、载体和所守的量。
相关仓内锚点 `GoldenAntiIsometry.golden_anti_isometry` 给黄金二次型的反等距关系，`SeatTowerArithmetic.pythagorean_gate_iff_eisenstein_norm` 给 Eisenstein 范数门；二者均不作为本节完整 $M/J$ 矩阵桥的现成证明。

**命题 149.4（五窗更新的协同搬运）。** 首窗权重为 $(2,3,5)$，固定读出 $q(a,b)=2a+3b$。五种贡献向量为

$$
d_{\mathrm{null}}=(0,0)^{\mathsf T},\quad d_2=(1,0)^{\mathsf T},\quad
d_3=(0,1)^{\mathsf T},\quad d_{2\ 5}=(2,1)^{\mathsf T},\quad d_5=(1,1)^{\mathsf T}.
$$

证明其读数分别为 $0,2,3,7,5$，只需代入 $q$；其中 $d_{2\ 5}=d_2+d_5$。
按从高窗向低窗的 Horner 更新 $x\mapsto Sx+d$，$S=M^3=\left(\begin{smallmatrix}1&2\\2&3\end{smallmatrix}\right)$ 消耗三个位置；`null` 仍作 $x\mapsto Sx$，只是不增加新贡献，不等于 End 或停步。
这些向量公式须与 §141.1 的单位位、相邻禁令、接缝及 End 合同共同使用。
对 $k\in\mathbb Z$，将状态、转移、贡献和读出一起搬到旋转坐标：

$$
S_k=C^kSC^{-k},\qquad d^{(k)}=C^kd,\qquad q_k(y)=q(C^{-k}y).
$$

则对每个合法更新有

$$
C^k(Sx+d)=S_k(C^kx)+d^{(k)},\qquad
q_k(C^kx)=q(x). \tag{149.3}
$$

证明。把 $C^{-k}C^k=I$ 代入右边即可；逐步应用第一式，再用第二式，整个合法窗串的解码数值保持不变。合法状态和接缝条件也须随原串搬运，不能把旋转后的负坐标重新当成原语法的计数。
若只旋转状态而固定旧读出，则 $q(2,1)=7$，但 $C(2,1)=(-1,2)$ 且 $q(-1,2)=4$；搬运后的读出才满足 $q_1(-1,2)=7$。$\square$

**命题 149.5（Robin 模型的搬运不改善界）。** 固定 §143 的一个有限来源模型及算术参数 $H\ge2$。用 $R=C^k$ 双射搬运其组成状态，来源概率取推前分布，所有探针与观察取逆像读出。
具体令 $(Uf)(Rx)=f(x)$、$\eta_k(Rx)=\eta(x)$，其中 $\eta$ 是原观察；设 $P,P_k$ 为相应的条件平均投影，则

$$
\|Uf\|_{2,k}=\|f\|_2,\qquad P_kU=UP.
$$

证明。有限加权求和在双射下逐项相同，且新旧观察纤维及其权重一一对应，故纤维内条件平均相同。于是逐探针的总能量、可见能量及残差能量分别不变，即

$$
Z_k(H)=Z(H),\qquad V_k(H)=V(H),\qquad E_k(H)=E(H),\qquad
\Delta_k(H)=\Delta(H)=e^\gamma\log\log H-Z(H). \tag{149.4}
$$

这里 $V,E$ 指 §143 在选定观察下的量；算术参数及数值读出也按式 (149.3) 保持，故 Robin 余量不变。$\square$
因此 $C$ 是选定有限组成模型的重参数化；同时搬运所有结构时，它给模型之间的对称，未必是原非负来源集合的自同构。
只有在固定外部算术探针并且它不具 $C$ 不变性时，旋转才可能提供不同读数；还须证明变换后的来源类对该算术问题确实可容许，并由此取得真正的新界，才可能推进 Robin。这里没有证明这条桥。
五窗细化可以在同一来源合同内揭示粗观察合并的隐藏类别；局部四相的范数保持既不给随尺度增长的新素轴估计，也不给实际 Möbius 函数的带符号抵消界，§§146–148 的全称缺口仍在。

## 追加锚（本行以下为增补区）

## 150. 共轭收缩坐标上的五窗仿射递归固定点

本节把五窗递归放到黄金共轭的收缩坐标中。
令

$$
\phi=\frac{1+\sqrt5}{2},\qquad
\psi=-\phi^{-1},\qquad
\lambda=\psi^3,\qquad |\lambda|<1.
$$

对五个窗口取组成向量

$$
d_{\mathrm{null}}=(0,0),\quad d_2=(1,0),\quad d_3=(0,1),\quad
d_{25}=(2,1),\quad d_5=(1,1).
$$

写 $\sigma_-(a,b)=a+b\psi$，并置 $\delta_\sigma=\sigma_-(d_\sigma)$。
按上述顺序，五个共轭坐标为

$$
0,\quad 1,\quad \psi,\quad 2+\psi,\quad 1+\psi=\psi^2.
$$

相应的仿射分支为

$$
f_\sigma(y)=\delta_\sigma+\lambda y.
$$

因 $\sigma_-(M^3x)=\psi^3\sigma_-(x)$，$f_\sigma$ 正是 §149 的三步递归在共轭坐标下的分支。
本节路径地址按低窗到高窗读取；§149 对有限地址作从高窗到低窗的 Horner 求值，二者方向相反。
状态 $0$ 表示 incoming seam 未被占用，状态 $1$ 表示低位侧 incoming seam 已占用。
采用 incoming occupied seam rule 时，状态 $1$ 的当前窗首位必须为零；边从当前输入状态指向当前窗最高位决定的输出状态。
在这个低到高约定下，有向两状态图的方程为

$$
\begin{aligned}
K_0={}&f_{\mathrm{null}}(K_0)\cup f_2(K_0)\cup f_3(K_0)
       \cup f_{25}(K_1)\cup f_5(K_1),\\
K_1={}&f_{\mathrm{null}}(K_0)\cup f_3(K_0)\cup f_5(K_1).
\end{aligned}
$$

因此，从 $0$ 出发的 $25$、$5$ 分支进入 $1$，而从 $1$ 出发的
$\mathrm{null}$、$3$ 分支回到 $0$，$5$ 分支留在 $1$。
若改用高窗到低窗的扫描，必须相应反向或重标图；不能在未声明约定时混用这两种方向。
这些并集只表达允许的分支，不能声称各子集彼此不交；重叠是允许的。

**命题 150.1（图有向 Hutchinson 算子的唯一紧集对）。**
令 $\mathscr K(\mathbb R)$ 为非空紧子集空间，$H$ 为最大 Hausdorff 距离，
并在 $\mathscr K(\mathbb R)^2$ 上置

$$
d_\infty((A_0,A_1),(B_0,B_1))=\max\{H(A_0,B_0),H(A_1,B_1)\}.
$$

右端两式定义算子 $\mathcal T(A_0,A_1)=(\mathcal T_0,\mathcal T_1)$。
每个 $f_\sigma$ 都是比率 $|\lambda|$ 的仿射压缩，故

$$
H(f_\sigma(A),f_\sigma(B))=|\lambda|H(A,B).
$$

对相同标签的有限并，有

$$
H\!\left(\bigcup_j A_j,\bigcup_j B_j\right)
\le\max_j H(A_j,B_j).
$$

逐行应用这个不等式，得到

$$
d_\infty(\mathcal T A,\mathcal T B)
\le |\lambda|d_\infty(A,B).
$$

非空紧子集的 Hausdorff 空间在 $\mathbb R$ 完备时完备，最大度量的有限乘积仍完备。
由于 $|\lambda|<1$，Banach 不动点定理给出唯一的非空紧集对 $(K_0,K_1)$。
这是合法无限路径的完成，而非一个额外的整数对象。

令 $\Omega_s$ 为从状态 $s$ 出发的所有合法无限标记路径，取有限字母积的乘积拓扑。
若路径为 $(\sigma_0,\sigma_1,\ldots)$，则其编码为

$$
\kappa_s(\sigma_0,\sigma_1,\ldots)
=\lim_{N\to\infty}f_{\sigma_0}\circ\cdots\circ f_{\sigma_{N-1}}(0)
=\sum_{n\ge0}\lambda^n\delta_{\sigma_n}.
$$

收缩性使该级数一致收敛，故 $\kappa_s$ 连续；标准的逐层逼近给出
$K_s=\kappa_s(\Omega_s)$。
每个有限 Zeckendorf 地址都可在末尾接上无限个 $\mathrm{null}$，成为 eventually-null path。
因为两个状态都存在通向状态 $0$ 的 $\mathrm{null}$ 边，eventually-null paths 在 $\Omega_s$ 中稠密。
连续编码遂使这些路径的像在各 $K_s$（亦即 $K=K_0\cup K_1$）中稠密。
这里不把所有无限路径等同于普通自然数；自然数地址只是其中的 eventually-null 子族。

**命题 150.2（四相表示闭包）。** 在 $\mathbb C$ 中定义

$$
\widehat K_s=\bigcup_{k=0}^{3}i^kK_s,\qquad s\in\{0,1\}.
$$

因为 $K_s\subset\mathbb R$，有 $i\widehat K_s=\widehat K_s$，且普通复共轭也保持
$\widehat K_s$：$\overline{i^kx}=i^{4-k}x$。
这只是表示闭包，把实共轭坐标的四相放进复平面。
组成坐标中的 $J$ 并不自动等于复数的普通共轭；若要声称 $J$ 对称，必须另外给出运输后的标签作用及其保持定理。

另有一条离散的逆极限表述。
令 $B_r$ 为有限边界或分辨率对象，$\pi_r:B_{r+1}\to B_r$ 为键合映射，
并令 $g_r:B_r\to B_r$ 满足

$$
\pi_r\,g_{r+1}=g_r\,\pi_r.
$$

在 $\Omega=\varprojlim B_r$ 上定义
$g_\infty((b_r)_r)=(g_r(b_r))_r$，则相容性保证它落在逆极限中。
若每个 $g_r$ 都是双射，逐坐标取逆即得 $g_\infty$ 为双射。
这个逆极限兼容性是有限对象作用的极限陈述，不能与上面的紧集 IFS 不动点混为同一构造。

对 Robin 问题，本固定点只证明递归自相似与闭包。
它没有给出 $Z(H)$ 的统一上界，没有给出带符号 Möbius 抵消，也没有给出 zeta 零点谱。
有用的下一座桥需要一个算术 observable 或 probe，并且要证明共轭编码或四相作用保持、截断其误差，
再配合随 growing-prime 尺度统一有效的估计；当前固定点本身不承担这些算术结论。

## 追加锚（本行以下为增补区）

## 151. 显式区间闭包与黄金共轭的紧性障碍

本节把 §150 的图方程写成一个可直接核对的区间结果，并说明收缩坐标不能承载完整黄金共轭。
令

$$
t=\phi^{-1}=\frac{\sqrt5-1}{2},\qquad t^2=1-t,
\qquad \lambda=\psi^3=1-2t=-t^3.
$$

这里 $\frac12<t<1$，因而 $t^3=2t-1$、$t^4=2-3t$，且
$t^3(1+t)=t^2$。
对 §150 的两个状态，固定

$$
K_0=[-1,1+t]=[-1,\phi],\qquad K_1=[-1,t].
$$

五个标签的仿射平移量依次为

$$
\delta_{\mathrm{null}}=0,\quad \delta_2=1,\quad
\delta_3=-t,\quad \delta_{2\ 5}=2-t,\quad \delta_5=1-t=t^2.
$$

直接把 $f_\sigma(y)=\delta_\sigma+\lambda y$ 作用到这两个区间，得到

$$
\begin{aligned}
\mathrm{null}(K_0)&=[-1+t,-1+2t],\\
2(K_0)&=[t,2t],\\
3(K_0)&=[-1,-1+t],\\
(2\ 5)(K_1)&=[2t,1+t],\\
5(K_1)&=[-1+2t,t].
\end{aligned}
$$

这是二次环中的等式，不依赖小数近似。
例如 $\lambda K_0=[-1+t,-1+2t]$，而
$\lambda K_1=[-t^4,t^3]$；再分别加上上述五个 $\delta_\sigma$ 即得全部端点。
由于 $\frac12<t<1$，端点严格按

$$
-1<-1+t<-1+2t<t<2t<1+t
$$

排列。
所以 $3,\mathrm{null},5,2,2\ 5$ 正好按这个顺序铺满 $K_0$。
状态 $1$ 的方程只取 $3(K_0),\mathrm{null}(K_0),5(K_1)$，
它们按同一端点顺序铺满 $K_1$。
相邻区间的共同端点允许重叠，故这里没有唯一编码的断言。
这也给出对 §150 图方程的纸面精确验证；独立的二次环小检查与这些端点恒等式一致。

必须把这个紧的单嵌入对象同完整组成晶格分开。
取既有基向量 $\alpha=(1,0)$，令

$$
x_n=M^{3n}\alpha\qquad(n\ge0).
$$

因 $\sigma_-(\alpha)=\sigma_+(\alpha)=1$，有

$$
\sigma_-(x_n)=\psi^{3n}=\lambda^n\longrightarrow0,
\qquad
\sigma_+(x_n)=\phi^{3n}\longrightarrow\infty.
$$

黄金共轭 $J$ 交换两个嵌入，因此

$$
\sigma_-(Jx_n)=\sigma_+(x_n)=\phi^{3n}
$$

无界。
若一个紧的单嵌入固定点集上的连续自映射要在这条序列上实现精确的 $J$，
它的像必须仍是紧集中的有界序列，却同时被迫包含 $\phi^{3n}$，这是矛盾。
换言之，收缩坐标可以记录 $x_n$ 的趋零方向，但不能在同一紧集内记录其被 $J$ 交换后的扩张方向。

这不等于精确整数格上的信息不可恢复：由于 $\psi$ 无理，
$\sigma_-:\mathbb Z^2\to\mathbb R$ 仍是单射，故一个已知来自整数格的精确收缩读数在集合论意义下仍确定组成坐标。
这里失败的是把 $J$ 或 $C$ 的扩张读数作为有界、连续的完成空间自映射；有限精度下的稳定恢复则还需要另给误差与解码合同。

同样，$C=MJ$ 的收缩坐标满足

$$
\sigma_-(Cx_n)=\psi\,\sigma_-(Jx_n)=\psi\,\phi^{3n},
$$

所以其绝对值为固定因子 $t$ 乘以 $\phi^{3n}$，仍然无界。
这不是说 $J$ 不可用；可行选择包括保留两个嵌入的非紧乘积、只运输标签而不要求精确自映射，
或另行定义一个不同的相位闭包。
§150.2 人工四相闭包中的普通复共轭只是在 $\mathbb C$ 中交换相位 $i^k$，
它与组成环的黄金共轭 $J$ 是两个不同的操作，不能互相代替。

对 Robin 的结论因此保持克制：显式区间证明了收缩完成是一个紧的编码对象，
但这个完成没有把扩张坐标保留为有界连续的可观测量；因此在没有额外算术观测器和统一估计的条件下，
当前构造不给出统一 $Z(H)$ 上界，也不给出随 growing-prime 尺度有效的带符号估计。
有限自然数只有在采用完整 §104 的 unit-bit、合法接缝和 End 约定之后，才可作为 eventually-null 的窗口路径；
没有该约定时，不把一般有限地址自动等同于自然数。
本节没有新增 Lean、消化或冻结内容。

## 追加锚（本行以下为增补区）

## 152. 新素数尾部与 $10080p^a$ 的 Robin 安全族

本节沿用 §144.1 的记号

$$
Z(H)=\frac{\sigma(H)}H,
\qquad
\Delta(H)=e^\gamma\log\log H-Z(H).
$$

只研究一个固定的新素数方向；本节不处理同时加入两个或更多新素数的路径。
令 $H_0=10080$，并取素数 $p\ge11$。由于

$$
10080=2^5\cdot3^2\cdot5\cdot7,
$$

所以 $p\nmid H_0$。若 $p\nmid H$，直接从约数和的乘法性得到

$$
Z(pH)-Z(H)=\frac{Z(H)}p.
$$

记 $L=\log H$、$x=\log p$，则 Robin 余量的单步变化为

$$
\Delta(pH)-\Delta(H)
 =e^\gamma\log\left(1+\frac{x}{L}\right)-\frac{Z(H)}p.
\tag{152.1}
$$

对 $u>0$ 使用

$$
\log(1+u)\ge\frac{u}{1+u},
$$

可见下面的条件足以保证单步余量不减：

$$
\frac{Z(H)}p
\le e^\gamma\frac{\log p}{\log H+\log p}.
\tag{152.2}
$$

为控制素数方向，固定 $L>0$ 并置

$$
R_L(x)=e^\gamma\frac{e^x x}{L+x}.
$$

它在 $x>0$ 上严格递增，因为

$$
\frac{d}{dx}\log R_L(x)
 =1+\frac1x-\frac1{L+x}
 =1+\frac{L}{x(L+x)}>0.
\tag{152.3}
$$

因此，只要式 (152.2) 在某个 $p_0$ 处成立，它就对所有 $p\ge p_0$ 成立。

### 152.1. $10080$ 的新素数入口

已有的有理证书给出

$$
Z(10080)=\frac{39}{10},
\qquad
\Delta(10080)>\frac2{125}.
$$

为验证 $p_0=11$ 的入口，只需使用以下严格有理界：

$$
 e^\gamma>\frac{89}{50},
\qquad
\frac{239}{100}<\log11<\frac{240}{100},
\qquad
\log10080<\frac{922}{100}.
$$

于是

$$
 e^\gamma\frac{\log11}{\log10080+\log11}
>
\frac{89}{50}\cdot\frac{239}{100}\cdot\frac{50}{581}
=\frac{21271}{58100}
>\frac{39}{110}
=\frac{Z(10080)}{11}.
\tag{152.4}
$$

式 (152.4) 严格给出式 (152.2)；由 (152.3)，同一结论对每个素数 $p\ge11$ 成立。因此

$$
\Delta(10080p)>\Delta(10080)>0.
$$

这里的三条对数界可由

$$
\log y=2\sum_{j=0}^{N-1}\frac{z^{2j+1}}{2j+1}+T_N,
\qquad z=\frac{y-1}{y+1},
$$

以及

$$
0<T_N\le
\frac{2z^{2N+1}}{(2N+1)(1-z^2)}
$$

得到；本节的独立脚本以 $N=32$ 的有理运算核对这些方向。$e^\gamma>89/50$ 沿用 §144.1 的 $H_{1000}$ 余量界与六项指数下和证书。

### 152.2. 任意指数层

令

$$
H_a=10080p^a,
\qquad
L_0=\log10080,
\qquad
x=\log p,
\qquad
D_a=L_0+ax.
$$

在从 $H_a$ 到 $H_{a+1}$ 的一步中，约数和的精确增量是

$$
Z(H_{a+1})-Z(H_a)=\frac{39}{10p^{a+1}}.
\tag{152.5}
$$

预算增量由式 (152.1) 的对数下界满足

$$
 e^\gamma\log\left(1+\frac{x}{D_a}\right)
\ge e^\gamma\frac{x}{D_{a+1}}.
\tag{152.6}
$$

入口 $a=0$ 已由式 (152.4) 严格证明。若对某个 $a\ge1$ 有

$$
 e^\gamma\frac{x}{D_a}>\frac{39}{10p^a},
$$

则

$$
D_{a+1}\le pD_a,
$$

因为

$$
pD_a-D_{a+1}
=(p-1)L_0+\bigl(a(p-1)-1\bigr)x>0
$$

对 $p\ge11$、$a\ge1$ 成立。于是

$$
 e^\gamma\frac{x}{D_{a+1}}
\ge\frac1p e^\gamma\frac{x}{D_a}
>\frac{39}{10p^{a+1}}.
$$

结合式 (152.5) 与式 (152.6)，归纳得到

$$
\Delta(H_{a+1})>\Delta(H_a)>0
\qquad(a\ge0).
$$

所以得到这一条明确的无限安全族：

$$
\boxed{
\forall\,p\ge11\text{ 素数},\ \forall\,a\ge1,
\qquad
 e^\gamma\log\log(10080p^a)>Z(10080p^a).
}
\tag{152.7}
$$

这是一条单新素数、任意指数的 Robin 局部推进。它没有给出多个新素数同时加入时的联合估计，也没有给出所有 $H>5040$ 的统一证明；因而不能据此宣称 Robin 猜想或黎曼猜想已经得到证明。

FIB 结构在这里提供的是规范窗口、来源路径与观察切面；式 (152.1)--(152.7) 的实际上界来自约数和增量、对数预算和单调性。把五窗收缩固定点或四相运输直接当作 Robin 的统一上界，仍缺少独立的算术观测器与 growing-prime 误差估计。

独立脚本 `docs/reports/fib-robin-boundary/new_prime_tail.py` 只做有理数证书与代数归纳核验，不使用浮点数，也不替代无界命题的纸面证明。本节是仓内研究推导，没有新增 Lean 声明、冻结或消化覆盖。

## 追加锚（本行以下为增补区）


## 153. 原第 13 节两个边界命题的更正

### proposition 153.1（更正定理 13.4 的证明）

定理 13.4 的陈述仍然成立；本命题替换其证明。原证明称 $(v,-u)$ 为非零向量而未排除 $u=v=0$，且其在 $\mathbb N^2$ 中给出的见证只适用于 $u,v>0$。

对任意整数权重 $u,v$，线性读数

$$
\ell(a,b)=ua+vb
$$

在整个 $\mathbb Z^2$ 上都不是单射；把定义域限制为 $\mathbb N^2$（其中 $0\in\mathbb N$）时也不是单射。

**证明。** 当 $(u,v)\ne(0,0)$ 时，非零向量 $(v,-u)$ 属于整数核，故整数域上不单射。为同时得到非负见证，令

$$
x=(\max\{-v,0\},\max\{u,0\}),\qquad
y=(\max\{v,0\},\max\{-u,0\}).
$$

则 $x,y\in\mathbb N^2$，$y-x=(v,-u)\ne(0,0)$，且 $\ell(y)-\ell(x)=u v+v(-u)=0$。当 $(u,v)=(0,0)$ 时，任意两个不同点都是非负核内点。因此所有权重，包括全零权重，都满足结论。两层读数达到的下界仍由定理 13.2 和推论 13.3 给出。$\square$

### proposition 153.2（更正命题 13.5 的模数假设）

令 $u,v$ 为正整数，令

$$
H_{u,v}=\begin{pmatrix}u&v\\v&u+v\end{pmatrix},
\qquad
\Delta=u^2+uv-v^2,
$$

则 $\Delta\ne0$，整数线性映射 $z\mapsto H_{u,v}z$ 是单射，且其像在 $\mathbb Z^2$ 中的指标为 $|\Delta|$。对每个**正**整数模数 $m\ge1$，约化映射

$$
H_{u,v}: (\mathbb Z/m\mathbb Z)^2\longrightarrow(\mathbb Z/m\mathbb Z)^2
$$

可逆当且仅当 $\gcd(|\Delta|,m)=1$；当且仅当 $\gcd(|\Delta|,m)>1$ 时，它有非零核，因而存在不同余数输入的碰撞。

**证明。** 行列式直接计算为 $\Delta$。若 $\Delta=0$，则 $(2u+v)^2=5v^2$；因 $v>0$，这会给出 $\sqrt5=(2u+v)/v\in\mathbb Q$，与 $\sqrt5$ 的无理性矛盾。非零行列式给出整数域上的单射，整数矩阵像的指标是行列式绝对值。正模数时，矩阵在 $\mathbb Z/m\mathbb Z$ 上可逆当且仅当其行列式为单位；而整数 $\Delta$ 在该环中为单位当且仅当 $\gcd(|\Delta|,m)=1$。模 $1$ 的环只有一个元素，此时前一条件成立且核为零；当最大公因子大于 $1$ 时，有限集合上的非可逆线性映射必有非零核，得到碰撞。取正权重 $(u,v)=(1,3)$，则 $\Delta=-5$。若把 $m=0$ 纳入原命题的“模 $m$”句子，则 $\gcd(|\Delta|,0)=5>1$，但 $\mathbb Z/0\mathbb Z\cong\mathbb Z$，而非零行列式使核仍为零。这给出原句在模 $0$ 下的反例。因此本命题以正模数条件替换命题 13.5 的模碰撞句，保留其正权重整数像指标结论。$\square$

## 追加锚（本行以下为增补区）

## 153. 超出二进筛的固定高赋值素数尾部

§152 的族 $10080p^a$ 有 $v_2=5$，因此已经包含在本卷 §95 所引用的 Axler 条件
$v_2(n)\le20$ 中。本节保留 §152 的增量方法，但把种子移到
$v_2=21$，明确记录它在该筛之外；这只是适用范围的推进，不是对文献结果的原创性声明。

这里的“筛之外”只指 $2$-方向。对本节的全部整数，固定种子给出

$$
v_3=2,\qquad v_5=1,\qquad v_7=1,\qquad v_{11}=0.
$$

所以 $v_3\le12$（以及其它三个方向）仍满足 §86.1 引用的 Hertlein 停止条件。
本节是对同一安全区域的独立增量证书，不扩大已发表的 Robin 覆盖范围。

令

$$
H_*=315\cdot2^{21}=3^2\cdot5\cdot7\cdot2^{21}.
$$

约数和的乘法性给出

$$
Z(H_*)
=\left(2-2^{-21}\right)\frac{13}{9}\frac65\frac87
=\left(2-2^{-21}\right)\frac{208}{105}
<\frac{416}{105}.
\tag{153.1}
$$

有理对数证书给出

$$
\log H_*>\frac{203}{10},
\qquad
\log\frac{203}{10}>3,
\qquad
e^\gamma>\frac{89}{50}.
$$

所以

$$
\Delta(H_*)
=e^\gamma\log\log H_*-Z(H_*)
>\frac{89}{50}\cdot3-\frac{416}{105}
=\frac{1447}{1050}>0.
\tag{153.2}
$$

现在取素数 $p\ge19$。由于 $p\nmid H_*$，首次加入 $p$ 的精确体增量为

$$
Z(pH_*)-Z(H_*)=\frac{Z(H_*)}{p}.
$$

使用

$$
\log(1+u)\ge\frac{u}{1+u}
$$

后，只需验证

$$
 e^\gamma\frac{\log p}{\log H_*+\log p}
\ge\frac{Z(H_*)}{p}.
\tag{153.3}
$$

在 $p=19$ 处，脚本使用

$$
\log H_*<\frac{2031}{100},
\qquad
\frac{294}{100}<\log19<\frac{295}{100},
$$

得到

$$
 e^\gamma\frac{\log19}{\log H_*+\log19}
>
\frac{89}{50}\frac{294/100}{2031/100+295/100}
=\frac{13083}{58150}
>\frac{416}{1995}
>\frac{Z(H_*)}{19}.
\tag{153.4}
$$

对固定 $L>0$，函数

$$
R_L(x)=e^\gamma\frac{e^x x}{L+x}
$$

在 $x>0$ 上严格递增，见式 (152.3)。因此式 (153.4) 推出式 (153.3) 对每个素数 $p\ge19$ 成立，并且

$$
\Delta(pH_*)>\Delta(H_*)>0.
$$

最后令 $H_a=H_*p^a$，$D_a=\log H_*+a\log p$。从 $H_a$ 到 $H_{a+1}$ 的精确增量是

$$
Z(H_{a+1})-Z(H_a)=\frac{Z(H_*)}{p^{a+1}}.
\tag{153.5}
$$

若某层已满足

$$
 e^\gamma\frac{\log p}{D_a}>\frac{Z(H_*)}{p^a},
$$

则

$$
D_{a+1}\le pD_a,
$$

因为

$$
 pD_a-D_{a+1}
=(p-1)\log H_*+\bigl(a(p-1)-1\bigr)\log p>0
$$

对 $p\ge19$、$a\ge1$ 成立。与式 (153.5) 及对数下界合并，得到任意指数层的严格正增量。

于是得到仓内目前一条不落入 $v_2\le20$ 筛的安全射线：

$$
\boxed{
\forall\,p\ge19\text{ 素数},\ \forall\,a\ge1,
\qquad
 e^\gamma\log\log\left(315\cdot2^{21}p^a\right)
>Z\left(315\cdot2^{21}p^a\right).
}
\tag{153.6}
$$

这一结论仍只处理固定奇数支撑 $3^2\cdot5\cdot7$ 与一个新增素数方向。它没有控制多个不断变化的新素数、没有覆盖所有 $v_2\ge21$ 的整数，也没有证明 Robin 全称不等式或黎曼猜想。FIB 窗口在这里仍是来源编码与递归分辨率；正性来自 Robin 的算术增量估计。

独立验证脚本同时核对 §152 的证书、式 (153.1)--(153.5) 的有理边界和指数归纳系数；脚本不使用浮点数，也不替代无界解析证明。

## 追加锚（本行以下为增补区）

## 154. 固定高二赋值种子的多素数支撑预算

§153 只沿一个新素数方向推进。这里把同一个种子上的有限多个新素数放在同一条整数链上，先给出一个不需要逐步判断符号的支撑预算。
由于这个种子仍有 $v_3=2\le12$，下面的族同样已经落在 §86.1 的已发表停止条件内；新增内容是联合 Euler 因子预算，而不是新的 Robin 覆盖区域。

仍令

$$
H_*=315\cdot2^{21},
\qquad
Z_*=Z(H_*),
\qquad
\Delta_*=e^\gamma\log\log H_*-Z_*.
$$

取互异素数 $p_1,\ldots,p_k\ge19$，以及正整数 $a_1,\ldots,a_k$，并设

$$
N=H_*\prod_{i=1}^k p_i^{a_i},
\qquad
U(P)=\prod_{i=1}^k\frac{p_i}{p_i-1}.
$$

所有 $p_i$ 都不整除 $H_*$，故约数和的乘法性给出精确恒等式

$$
Z(N)=Z_*\prod_{i=1}^k
\frac{p_i}{p_i-1}\left(1-p_i^{-(a_i+1)}\right).
\tag{154.1}
$$

特别地，

$$
Z(N)\le Z_*U(P),
\qquad
\log\log N\ge\log\log H_*.
\tag{154.2}
$$

### 命题 154.1（支撑预算充分条件）

若

$$
U(P)\le1+\frac{1447}{4160},
\tag{154.3}
$$

则

$$
\boxed{
e^\gamma\log\log N>Z(N).
}
\tag{154.4}
$$

**证明。** 由式 (153.2) 和式 (154.2)，

$$
\begin{aligned}
\Delta(N)
&\ge\Delta_*-Z_*(U(P)-1)\\
&>\frac{1447}{1050}-\frac{416}{105}(U(P)-1).
\end{aligned}
$$

式 (154.3) 使最后一项非负；前两处至少有一处严格，故最终严格为正。证毕。 $\square$

这个条件只使用最终支撑的 Euler 因子上界；它没有把不同素数的单步预算增量分别当成同时可用的余量，因而避开了同一整数链上的联合累计错误。

### 推论 154.2（至多九个新素数）

若 $k\le9$ 且所有 $p_i\ge19$ 互异，则式 (154.4) 成立。

证明中只需注意 $p\mapsto p/(p-1)$ 严格递减。九个最坏的素数是

$$
19,23,29,31,37,41,43,47,53,
$$

并且

$$
\prod_{p\in P_9}\frac p{p-1}
=
\frac{2775498881101}{2092278988800}
<1+\frac{1447}{4160}.
\tag{154.5}
$$

所以任意至多九个不同的新素数、任意正指数的这类整数都安全。这个推论仍固定 $v_2=21$ 和奇数种子 $3^2\cdot5\cdot7$；它没有处理 $p=11,13,17$，也没有覆盖任意高二赋值整数。由于 $v_3=2$ 不随这些新素数变化，这一整族仍由 §86.1 的 $3$-方向条件覆盖。

脚本 `docs/reports/fib-robin-boundary/multi_prime_tail.py` 核验这些有理常数、最坏九素数乘积、一个混合指数实例和十素数边界；一般乘法恒等式与预算推导仍由本节证明承担。该边界失效只表示当前证书不够强，不表示对应整数违反 Robin 不等式。

## 追加锚（本行以下为增补区）

## 155. 五方向必要核上的粗素数支撑预算

§86.2 给出一个可能反例必须满足的必要整除条件。令

$$
M=2^{21}3^{13}5^9 7^7 11^6
=9527493263501079465984000000000.
$$

本节固定这个核的五个指数，只允许加入互异的新素数 $p_i\ge13$ 的正指数：

$$
N=M\prod_{i=1}^k p_i^{a_i},
\qquad a_i\ge1.
$$

这不是对所有可能反例的参数化；例如核内五个素数的额外指数，以及其余小素数的其它停止条件，均另属不同分支。

定义

$$
U(P)=\prod_{i=1}^k\frac{p_i}{p_i-1}.
$$

因为 $M$ 的五个素因子都小于 $13$，有

$$
Z(M)<
2\cdot\frac32\cdot\frac54\cdot\frac76\cdot\frac{11}{10}
=\frac{77}{16}.
\tag{155.1}
$$

有理对数展开给出

$$
\log M>71,
\qquad
\log71>\frac{21}{5},
\qquad
e^\gamma>\frac{89}{50}.
\tag{155.2}
$$

从而

$$
\Delta(M)>\frac{89}{50}\cdot\frac{21}{5}-\frac{77}{16}
=\frac{5327}{2000}>0.
\tag{155.3}
$$

### 命题 155.1（必要核的支撑充分条件）

若

$$
U(P)\le\frac{2136}{1375}=1+\frac{761}{1375},
\tag{155.4}
$$

则

$$
\boxed{
e^\gamma\log\log N>Z(N).
}
\tag{155.5}
$$

**证明。** 约数和乘法性给出

$$
Z(N)
=Z(M)\prod_i\frac{p_i}{p_i-1}\left(1-p_i^{-(a_i+1)}\right)
<\frac{77}{16}U(P).
$$

又 $N\ge M$，故 $\log\log N\ge\log\log M$。结合式 (155.3)，

$$
\begin{aligned}
\Delta(N)
&\ge\Delta(M)-Z(M)(U(P)-1)\\
&>\frac{5327}{2000}-\frac{77}{16}(U(P)-1)\ge0.
\end{aligned}
$$

最后一个下界由式 (155.4) 给出，而前面的严格界保证最终严格为正。证毕。 $\square$

### 推论 155.2（至多十二个新素数）

若 $k\le12$，且 $p_i\ge13$ 互异，则式 (155.5) 成立。最坏的十二个素数为

$$
13,17,19,23,29,31,37,41,43,47,53,59,
$$

其 Euler 因子乘积为

$$
\frac{95993978542907}{61802702438400}
<\frac{2136}{1375},
\tag{155.6}
$$

并留下严格余量

$$
\frac{68552407001}{64210599936000}>0
$$

在式 (155.3) 的粗界下。加入下一个最小允许素数 $61$ 后，乘积为

$$
\frac{5855632691117327}{3708162146304000}>\frac{2136}{1375},
$$

所以十三素数只表示这份粗预算不再足够，不表示出现 Robin 反例。

本节确实作用在 §86.2 的五方向必要核上，但核内成员仍可能满足额外素数方向的已发表停止条件；本节没有覆盖所有五方向核，也没有证明 Robin 全称不等式或 RH。脚本 `docs/reports/fib-robin-boundary/kernel_tail.py` 核验式 (155.1)--(155.9) 中的整数、有理乘积和对数方向；通用乘法与预算推导仍由本节证明承担。

### 命题 155.3（把新增素数的对数增长计入预算）

对每个 $k\ge1$，令 $p_{k,1}<\cdots<p_{k,k}$ 为不小于 $13$ 的前 $k$ 个素数，置

$$
P_k=\prod_{j=1}^k p_{k,j},\qquad
U_k=\prod_{j=1}^k\frac{p_{k,j}}{p_{k,j}-1}.
$$

把 $N$ 中的新增素数按升序写为 $q_1<\cdots<q_k$。若 $1\le k\le121$，则

$$
N\ge MP_k,\qquad
\prod_{j=1}^k\frac{q_j}{q_j-1}\le U_k.
$$

同一有理对数核验给出

$$
\frac{89}{50}\log\log(MP_k)-\frac{77}{16}U_k>\frac1{3000}\qquad(1\le k\le121).
\tag{155.7}
$$

因此，对任意正指数 $a_j$，有

$$
\boxed{
N=M\prod_{j=1}^kq_j^{a_j},\quad k\le121,\quad q_j\ge13
\Longrightarrow
 e^\gamma\log\log N>Z(N).
}
\tag{155.8}
$$

**证明。** 按素数的单调性，$q_j\ge p_{k,j}$，所以 $N\ge MP_k$，且新增 Euler 因子乘积不超过 $U_k$。由于 $\log\log$ 在这里递增，式 (155.7)、$e^\gamma>89/50$ 以及式 (155.1) 给出

$$
\begin{aligned}
 e^\gamma\log\log N-Z(N)
 &>\frac{89}{50}\log\log(MP_k)-\frac{77}{16}U_k\\
 &>\frac1{3000}>0.
\end{aligned}
$$

这覆盖 $k=1,\ldots,121$；$k=0$ 已由命题 155.1 覆盖。对第 $122$ 个最小允许素数 $709$，同一有理下界的值已经小于 $0$；这只表示该粗糙下界在此处耗尽，不表示出现 Robin 反例。证毕。 $\square$

式 (155.7) 是一个有限的、按 $k$ 逐项检查的有理证书；它没有把有限核推广为所有整数。脚本还核对了第 $122$ 项的边界，使用的前 $122$ 个允许素数以 $709$ 结束。

### 命题 155.4（精确核值的有限延伸）

对固定核，实际约数权重可写成

$$
Z_*=
\left(2-2^{-21}\right)
\left(\frac32-\frac1{2\cdot3^{13}}\right)
\left(\frac54-\frac1{4\cdot5^9}\right)
\left(\frac76-\frac1{6\cdot7^7}\right)
\left(\frac{11}{10}-\frac1{10\cdot11^6}\right)
=\frac{72365886696479164830959537}{15037079014364077440000000}.
$$

用同一个 $m=1000$ 的 Euler 常数有理下界，并保留其精确分数而不截成 $577/1000$，可得

$$
 e^\gamma>\frac{1781}{1000}.
$$

于是，对 $1\le k\le131$，前 $k$ 个不小于 $13$ 的素数的最坏支撑满足

$$
\frac{1781}{1000}\log\log(MP_k)-Z_*U_k>\frac1{10000}.
\tag{155.9}
$$

所以式 (155.8) 的同一结论可将 $121$ 替换为 $131$。前 $131$ 个允许素数的末项是 $769$；第 $132$ 个是 $773$，而同一有理下界在该项已小于 $0$。

**证明。** 对任意新增素数集合，按大小排序后逐项与最小允许素数比较，得到 $N\ge MP_k$ 和 Euler 乘积不超过 $U_k$。将 $Z(N)<Z_*U_k$ 与 $e^\gamma>1781/1000$ 代入式 (155.9)，即得严格正的 Robin 差额。式 (155.9) 及第 $132$ 项的符号由 `kernel_tail.py` 的有理 atanh 展开、向下取整的累计对数和有限素数筛逐项核验；第 $132$ 项仅标记这份证书的边界，不给出反例。证毕。 $\square$

## 156. 固定共同核心上的指数交换与 Robin 联合前沿

前面的有限支撑预算把新增素数的 Euler 因子一起估计；本节处理另一种互补的压缩：在一个固定的高于阈值的共同核心上，把可能降低 Robin 余量的指数排列规范化。它使用已有的
`D5.S3.Arith.ExponentExchange.IntegerSwap.prime_exponent_swap`，不把该局部交换误报成全局 Robin 证明。

仍记

$$
Z(n)=\frac{\sigma(n)}n,
\qquad
\Delta(n)=e^\gamma\log\log n-Z(n).
$$

### 命题 156.1（单次交换严格降低 Robin 余量）

设 $m>e$，$p<q$ 为素数，并令

$$
a=v_p(m)<b=v_q(m).
$$

把 $p^a q^b$ 与 $p^b q^a$ 交换，所得整数记为 $m'$. 则

$$
m'<m,
\qquad Z(m')>Z(m),
\qquad \Delta(m')<\Delta(m).
\tag{156.1}
$$

**证明。** 前两个不等式是既有 `prime_exponent_swap` 的结论；其余素数赋值保持不变。函数 $x\mapsto e^\gamma\log\log x$ 在 $x>e$ 上严格递增，因此 $m'<m$ 给出预算项严格下降，而 $Z(m')>Z(m)$ 又使减项严格上升。两者相加即得最后一个不等式。$\square$

这里的 $m>e$ 是必要的定义域条件；对 Robin 任务中的 $m\ge5040$ 它自动满足。该命题给出的是**负余量搜索的下降方向**，不是把交换后的整数仍留在任意外部约束纤维中的保证。

### 定理 156.2（高共同核心上的规范化）

固定 $C\ge5040$ 和 $y\ge1$，假设 $C$ 的全部素因子不超过 $y$. 令

$$
q_0<q_1<\cdots
$$

为严格大于 $y$ 的连续素数。对任意

$$
n=C\prod_{i=0}^{r-1}q_i^{a_i},
\qquad a_i\ge0,
\qquad a_{r-1}>0,
$$

其中允许在最大的已出现素数之前补零指数。则存在一个规范整数

$$
\bar n=C\prod_{i=0}^{s-1}q_i^{c_i},
\qquad c_0\ge c_1\ge\cdots\ge c_{s-1}>0,
\tag{156.2}
$$

使得

$$
\bar n\le n,
\qquad Z(\bar n)\ge Z(n),
\qquad \Delta(\bar n)\le\Delta(n).
\tag{156.3}
$$

若原指数表不是非增表，则后三个比较中相应的 $Z$ 与 $\Delta$ 都严格；若原表已经是非增表，则取 $\bar n=n$.

**证明。** 在有限指数表中取一个相邻逆序 $a_i<a_{i+1}$，对 $q_i,q_{i+1}$ 应用 `prime_exponent_swap`。交换保留共同核心 $C$ 及其它指数，严格减小整数并严格增大 $Z$. 逆序数

$$
I(a)=\#\{(i,j):i<j,\ a_i<a_j\}
$$

每次至少下降一个单位，故有限次后得到非增表。把末尾零指数删去，就得到式 (156.2). 所有中间整数都至少为 $C\ge5040>e$，所以命题 156.1 可在每一步使用；传递比较即得式 (156.3). $\square$

定理 156.2 只在同一共同核心、同一 rough 素数域内作约化。它不保持同余、来源历史或加法约束；若这些约束属于任务合同，规范化所得整数只是删除约束后的安全上界，不能冒称仍在原纤维中。

### 推论 156.3（固定核心反例的规范搜索）

若存在

$$
n=Ct>5040,
\qquad t\text{ 的素因子均大于 }y,
\qquad \Delta(n)\le0,
$$

则同一 $C$ 和 $y$ 下存在满足式 (156.2) 的 $\bar n$，并且

$$
\bar n\le n,
\qquad \Delta(\bar n)\le0.
\tag{156.4}
$$

所以在固定高核心的有限预算搜索中，只需保留素数连续前缀上的非增指数。这个推论没有把任意 $n>5040$ 约化到该族：若没有预先固定共同核心，交换路径可能越过阈值，也可能破坏外部约束。

### 命题 156.4（Bellman 最大值必须升级为联合前沿）

令 $\mathcal P(i,b,h)$ 为从 $q_i$ 开始、预算至多 $b$、首指数上限 $h$ 的规范后缀的 Pareto 前沿；一对 $(u,w)$ 被另一对 $(u',w')$ 支配，当

$$
u'\le u,\qquad w'\ge w,
$$

且至少一项严格。则

$$
\begin{aligned}
\mathcal P(i,b,h)=\operatorname{Pareto}\Bigl(&\{(1,1)\}\\
&\cup\bigcup_{\substack{1\le a\le h\\q_i^a\le b}}
\{(q_i^a u,\,G_{q_i}(a)w):(u,w)\in
\mathcal P(i+1,\lfloor b/q_i^a\rfloor,a)\}\Bigr),
\end{aligned}
\tag{156.5}
$$

其中 $G_p(a)=\sum_{j=0}^a p^{-j}$. 这是一个有限递推；终止分支 $(1,1)$ 表示当前 rough 后缀停止。

若 $C\ge5040$ 且 $C$ 与所有 $q_i$ 互素，任何被另一点支配的 $(u,w)$ 都不能成为 $\Delta(Cu)$ 的唯一最小点，因为

$$
u'\le u,\quad w'\ge w
\Longrightarrow
\Delta(Cu')\le\Delta(Cu).
\tag{156.6}
$$

所以 `RoughPrimeSuffixBellman` 的 $V$ 只给出前沿的最大 $w$ 投影；要检验 Robin 余量，必须保留式 (156.5) 的联合 $(u,w)$ 前沿，最后再对同一整数 $Cu$ 的对数预算作有理区间比较。把不同整数的最大 $Z$ 放进同一个分母，是不合法的替换。

本节的规范化与前沿递推只给出固定共同核心上的有限搜索压缩。它没有估计前沿随 $y$ 或核心变化的统一尾部，也没有证明 Robin 全称不等式或黎曼猜想。

独立脚本 `docs/reports/fib-robin-boundary/robin_frontier.py` 生成式 (156.5) 的精确有理前沿；`robin_frontier_check.py` 不调用生成器而重算所有状态、分支、支配删除与根前沿。它们只核验有限规范递推，不把有限结果提升为无限尺度结论。

## 追加锚（本行以下为增补区）

## 157. 联合前沿上的有限 Robin 余量读数

命题 156.4 的前沿只保存精确的整数和约数权重；要比较 Robin 余量，还要在同一个整数上评价双对数预算。脚本 `robin_frontier_margin.py` 复用 `kernel_tail.py` 的有理 atanh 对数区间和 Euler 常数下界，逐点计算

$$
L_-(n)=c_\gamma\,\log_-(\log_-(n))-Z(C)w,
$$

其中 $c_\gamma<e^\gamma$，$w$ 是前沿中该后缀的精确权重，且 $C$ 与后缀素数互素。若 $L_-(n)>0$，则该点的真实 Robin 余量严格为正；这个蕴含只作用在脚本声明的有限前沿和共同核心上。

在

$$
y=7,\qquad B=1000,\qquad C=10080
$$

的四点前沿上，独立运行得到四个严格正的 $L_-$ 下界，最小点是 $n=10080$。这与 §152 的单新素数安全族相容，但任务范围更窄：这里先枚举固定预算中的规范前沿，再对每个实际整数作同一分母的读数；没有把一个点的最大 $Z$ 与另一个点的 $\log\log n$ 拼接。

该读数仍是有限算术证书。它没有覆盖无限 rough 后缀、变化共同核心或所有 Robin 整数，也没有证明 Robin 猜想或黎曼猜想。

## 追加锚（本行以下为增补区）

## 158. §156.1 的 Robin 定义域勘误

§156.1 的最后一个比较需要交换前后两个整数都落在实值 Robin 定义域。准确条件是

$$
m>e\quad\text{且}\quad m'>e.
$$

只写 $m>e$ 不够：$m=3$、$p=2$、$q=3$、$(a,b)=(0,1)$ 时交换得到 $m'=2<e$。§156.2 的固定核心应用没有这个问题，因为每个中间整数都至少为 $C\ge5040$。空 rough 后缀也按空乘积单独处理，不经过交换。

## 追加锚（本行以下为增补区）

## 159. 交换定义域、空后缀与前沿目标的完整条件

### 命题 159.1（更正 §156.1 与 §158 的定义域论证）

实函数 $x\mapsto e^\gamma\log\log x$ 的定义域是 $x>1$，且在这个定义域上严格递增；$x>e$ 只保证预算严格为正。因此，§156.1 中“$m>e$ 是必要的定义域条件”及 §158 中“准确条件是交换前后均大于 $e$”的说法均由本命题替代。

对任意正整数 $m$，若素数 $p<q$ 的指数满足 $a=v_p(m)<b=v_q(m)$，交换得到的 $m'$ 自动满足

$$
m'\ge p\ge2>1,\qquad m\ge q\ge3>1.
$$

所以 §156.1 的三个严格比较仍然成立，而且不需要另加 $m>e$ 或 $m'>e$。

证明。$\log\log x$ 为实数当且仅当 $\log x>0$，即 $x>1$；它是两个严格递增对数函数在相应定义域上的复合。由 $b>a\ge0$ 得 $b\ge1$，而交换后 $p^b\mid m'$，故 $m'\ge p$。整数下降与约数权重上升仍由素数指数交换给出；在 $(1,\infty)$ 上比较预算，即得 $\Delta(m')<\Delta(m)$。特别地，交换 $3\to2$ 不越出定义域，虽然 $2$ 的预算为负。$\square$

### 定理 159.2（含空后缀且保持 Robin 阈值的核心规范化）

§156.2 与 §156.3 的完整共同条件为：$C\ge5040$、$y\ge1$、$C$ 的全部素因子不超过 $y$，并且 $n=Ct$ 中的整数 $t\ge1$ 只有大于 $y$ 的素因子。令 $q_0<q_1<\cdots$ 为大于 $y$ 的连续素数，则存在

$$
\bar n=C\prod_{i=0}^{s-1}q_i^{c_i},
\qquad
c_0\ge\cdots\ge c_{s-1}>0\quad(s>0),
$$

满足 $\bar n\le n$、$Z(\bar n)\ge Z(n)$ 和 $\Delta(\bar n)\le\Delta(n)$。这里允许 $s=0$，空乘积为 $1$，而且

$$
s=0\iff t=1,
\qquad
n>5040\Longrightarrow\bar n>5040.
$$

因此，在这些完整条件下，§156.3 的规范反例若存在，仍属于 Robin 的目标范围 $\bar n>5040$。

证明。当 $t=1$ 时直接取 $s=0$ 与 $\bar n=C$，不使用含 $a_{r-1}$ 的非空指数表。若 $t>1$，把截至最大素因子的缺位指数补零，然后使用 §156.2 的相邻交换。交换保持指数多重集，至少一个正指数仍在，故删去尾部零项后 $s\ge1$，且 $\bar n\ge Cq_0>C\ge5040$。若 $t=1$ 且 $n>5040$，则 $\bar n=C=n>5040$。其余比较沿交换链传递。$\square$

### 命题 159.3（前沿上的阈值排除与空目标）

固定定理 159.2 的 $C,y$，以及整数预算 $B\ge1$。令 $\mathcal P_B$ 为 §156.4 中根状态的真实前沿，其成员是 $(u,Z(u))$。对任意 $1\le t\le B$ 的 $y$-rough 后缀，都存在 $(u,w)\in\mathcal P_B$ 使

$$
u\le t,\qquad w\ge Z(t),\qquad \Delta(Cu)\le\Delta(Ct).
$$

当 $C>5040$ 时，前沿的全部点都在 Robin 目标范围中。当 $C=5040$ 时，唯一落在目标外的点为 $(1,1)$，而这个点不支配任何非空后缀。因此，只要对前沿中 $Cu>5040$ 的点均有 $\Delta(Cu)>0$，就有

$$
\forall t\in\mathbb N,\quad
1\le t\le B,\quad t\text{ 的素因子均大于 }y,\quad Ct>5040
\Longrightarrow \Delta(Ct)>0.
$$

证明。先用定理 159.2 将 $t$ 规范化，再在有限点集中沿支配关系走到未被支配点；整数与权重比较传递，且互素性给出 $Z(Cu)=Z(C)Z(u)$。预算单调性于是给出余量比较。若 $t>1$，约数 $1,t$ 已给出 $Z(t)\ge1+1/t>1$，所以权重为 $1$ 的空后缀不可能支配它。若 $C=5040$ 且 $B<q_0$，不存在目标内的 rough 后缀，上述全称结论为空真；它不要求 $\Delta(5040)>0$。若不排除空后缀而对整个前沿求正，则所得充分条件更强，不能把它在 $5040$ 处的失败当成目标内反例。$\square$

### 命题 159.4（余量下界还需要正因子的条件）

设 $n=Cu$ 满足上述核心条件，$w=Z(u)$，且实数下界满足

$$
0<c_\gamma\le e^\gamma,
\qquad 1<\ell\le\log n,
\qquad 0\le h\le\log\ell.
$$

则

$$
c_\gamma h-Z(C)w\le\Delta(n).
$$

证明。由对数单调性有 $h\le\log\ell\le\log\log n$；非负性给出 $c_\gamma h\le e^\gamma h$，再减去精确的 $Z(Cu)=Z(C)w$ 即得结论。这个正因子条件不能仅从 $n>1$ 推出：在 $1<n<e$ 上，$\log\log n<0$，用 $e^\gamma$ 的下界替换系数会逆转相应乘积比较。函数定义域与特定下界算法的适用域是两件不同的事。$\square$

## 追加锚（本行以下为增补区）


## 160. 文献联合估计与任务所需的素数分辨率

本节沿用 §86 的五方向必要核与 §95 的真实 Fibonacci 来源。Hertlein 的局部因子保留法和 Axler 证明内部的 totient 上界可以联合使用；详细出处、参数及有理证书见 [Hertlein 文献笔记](../../../Library/notes/hertlein2018robin.md) 与 [Axler 文献笔记](../../../Library/notes/axler2023robin.md)。这是既有文献的应用，不新增解析定理或已验证的 Robin 全局范围。

**命题 160.1（同一整数的联合停止）。** 令 $n>5040$，$P$ 是实际整除 $n$ 的有限素数集。若

$$
\eta_P(n)=\prod_{p\in P}(1-p^{-v_p(n)-1})
\le T_A:=\frac{10^{12}}{10^{12}+315367},
$$

则 Robin 严格不等式成立。

证明。Axler 作者版本 v3 的 Lemma 2.3 给 $5041\le n\le N_K$ 的已验证范围，其中 $N_K$ 是第 $K=999999476056$ 个 primorial，$p_K=29996208012611$。其式 (3.4)–(3.5) 在上方给

$$
\frac n{\varphi(n)}<e^\gamma\left(L+\frac{0.0094243}{L^2}\right),
\qquad L=\log\log n.
$$

解析门槛的素数端点 $29996161880813$ 小于 $p_K$，因此两范围相接。引用原文式 (3.3) 的 theta 下界后，有理对数区间核验给 $\log\vartheta(p_K)>31032091744463/10^{12}$；该下界的立方乘 $315367/10^{12}$ 严格大于 $0.0094243$。故上方有 $n/\varphi(n)<T_A^{-1}e^\gamma L$。约数恒等式给 $Z(n)\le\eta_P(n)n/\varphi(n)$，两式合成即得结论，等号 $\eta_P=T_A$ 也成立。文献的原始大规模计算与解析界作为明确外部输入，本节没有重新执行或 Lean 核验。$\square$

**定义 160.2（判据的截断观察）。** 在指数域

$$
a\ge b=(21,13,9,7,6),\qquad P=(2,3,5,7,11)
$$

上，观察 $u_p=\min(a_p,c_p)$，其中

$$
c=(31,21,13,11,9).
$$

最后一格 $u_p=c_p$ 包含全部 $a_p\ge c_p$，其局部因子位于 $[1-p^{-c_p-1},1]$；其它格子的局部因子为精确值。各坐标的区间相乘后，[精确报告](../../reports/fib-robin-boundary/valuation_slices_axler.json) 的 9900 格全部完成比较：1144 格的上界不超过 $T_A$，8756 格的下界严格大于 $T_A$，没有未定格。计数是该分割的格数，不是自然数密度。

**命题 160.3（该判据的准确逐坐标分辨率）。** 在上述有理报告的有限比较前提下，$u$ 完全决定 $\eta_P(a)\le T_A$；对逐坐标截断观察，任意一个 $c_p$ 都不能降低，即使其它坐标给出全部精确赋值。

证明。每格都位于阈值同一侧，给充分性。乘积随指数递增，未通过条件的上集由报告中的 42 个极小向量生成。其逐坐标最大值恰为 $c$。对任一坐标，选一个达到该最大值的极小向量 $v$；$v$ 未通过，而 $v-e_p$ 通过。这里 $c_p>b_p$，故前驱仍在规定域内。把该坐标截断在任何更小深度，会合并这两个向量，而其它坐标相同。两向量均可由对应素数幂整数实现，故无法正确决定这个判据。$\square$

完整模余数 $n\bmod p^{c_p}$ 可以恢复这些截断赋值，因而足够；本节没有声称完整余数是最少状态，也没有声称这些数据决定未通过充分条件时 Robin 的真值。42 个极小向量对应的整除生成元见文献笔记。若 $M=2^{21}3^{13}5^97^711^6$，反例必须属于这些 $Mr$ 的倍数之并。这个并严格包含于 Hertlein 较弱阈值得到的 12 区域之并；生成元数量增加不表示候选范围扩大。

**命题 160.4（新增素方向的共同来源限制）。** 对真实来源 $n=5040F_j$、$j\ge3$，令 $D$ 如 §95，令

$$
Q=13^4 17^4 19^4 23^3.
$$

若 $n$ 是 Robin 反例，则 $j=DQt$，并且 $13\mid t$ 或 $23\mid t$。还须同时满足命题 160.3 的 42 个旧素方向整除条件。

证明。§95 先给 $D\mid j$，写 $j=Dk$。直接由标准递推核对，四素数 $13,17,19,23$ 的首次整除指标分别为 $7,9,18,24$，对应 Fibonacci 数为 $13,34,2584,46368$，各首赋值均为 1；四个指标都整除 $D$，四个素数均不整除 $5040D$。§95 已引用的赋值提升公式给 $v_p(n)=1+v_p(k)$。Axler 的单素停止条件分别迫使 $v_{13},v_{17},v_{19}\ge5$、$v_{23}\ge4$，所以 $Q\mid k$。此外

$$
T_A-(1-13^{-6})(1-23^{-5})
=\frac{1465648493004484688}{31067008116993059021656729}>0.
$$

故不可能同时 $v_{13}(n)=5$ 与 $v_{23}(n)=4$，从而 $v_{13}(k)\ge5$ 或 $v_{23}(k)\ge4$。除去 $Q$ 即得结论。$\square$

各条件作用于同一 $j$；它们没有选择不同局部来源再拼接。42 个旧方向分支与这两个新方向分支只给 84 个必要整除区域，不给危险实例：这 84 个区域的最低九素赋值角点全部通过完整九因子乘积条件。继续增加指数时局部因子会增大，最低角点安全不能认证整个上方区域。联合估计必须在同一实际整数上继续执行。

## 161. 固定五窗前缀仍允许全部算术剩余

本节使用 §104 的合法低位 Zeckendorf 前缀，单位位固定，已读窗口的占位和接缝固定，尚未承诺最终 End；允许在任意高位继续合法有限延长。它承接 §§150–151 的收缩区间，区分越来越小的几何像与模观察的精度。

**命题 161.1（每个低位柱集的满剩余像）。** 对任何上述固定合法有限前缀、任何 $m\ge2$ 和任何 $r\in\mathbb Z/m\mathbb Z$，存在正整数的有限规范 Zeckendorf 延长，其数量为 $r\pmod m$。

证明。模 $m$ 的相邻 Fibonacci 对由可逆更新 $(u,v)\mapsto(v,u+v)$ 推进。有限性与可逆性给某个正周期 $P$，使 $(F_P,F_{P+1})\equiv(0,1)\pmod m$。故每个 $h\equiv1\pmod P$ 都满足 $F_h\equiv1\pmod m$。

取一个足够高的 $h_0\equiv1\pmod P$，与前缀最高位置之间至少留一个空位，且 $h_0\ge3$。此后的位置 $h_t=h_0+2tP$ 两两不邻。设前缀数量为 $N_0$，选择 $k\in\{1,\ldots,m\}$ 满足 $k\equiv r-N_0\pmod m$，把 $F_{h_0},\ldots,F_{h_{k-1}}$ 加入表示。所有新增位均不相邻，也不碰原接缝；中间填空位，因此仍为规范表示。它以非零最高项终止，数量为正且恰为目标余数。把这些位重新按三位一窗分组，正是 $[null,2,3,2\ 5,5]$ 的合法有限延长。$\square$

**推论 161.2（任意精细低位观察都不能确定素赋值）。** 对任意素数 $p$、任意整数 $e\ge0$，每个上述前缀都有赋值恰为 $e$ 的正整数延长。特别地，不存在定义在合法无限五窗来源空间上的连续离散值函数，在所有有限自然数来源上都返回其模 $m$ 余数，其中该来源空间使用前缀柱集拓扑。

证明。对模数 $m=p^{e+1}$ 选余数 $p^e$，命题 161.1 给恰好 $e$ 层整除。若所述连续函数存在，在任意无限来源点处，离散值的连续性给一个前缀柱集，其上函数恒定；但命题 161.1 给同一柱集内两个有限来源，其模 $m$ 余数不同，矛盾。$\square$

在共轭收缩切面中，共同 $L$ 窗前缀的像直径至多为 $\phi^2|\psi|^{3L}$，依旧包含每种算术余数的有限来源影像。若收缩区间上有连续解码器给出这些余数，与连续编码复合就违反推论 161.2。这里没有否定精确有限格点上 $a+b\psi$ 的单射性，也没有把任意有限精度区间与一个特定前缀柱集混同。

因此，可以让同一个有限窗口流同时更新两份读数：共轭方向更新 $y\mapsto\delta_\sigma+\psi^3y$，整数模方向更新 $x\mapsto Sx+d_\sigma\pmod H$。这两式采用从高窗向低窗的读入顺序；输入的合法性仍由同一完整地址、单位位和接缝确定。结束时按 $N=\varepsilon+(2,3)x$ 读出模数。命题 160.3 给当前联合 Robin 判据的一组足够模数，而命题 161.1 说明这些模信息不能从任意固定低位前缀的收缩精度中省去。两种完成保留不同的连续任务，这与 §151 的旋转障碍相容。

本批为文献应用、有限有理证书与上述纸面来源论证；没有新增 Lean 或冻结声明。素数支撑与重数共同无界时的 Robin 全称估计仍未获得，区间长度守恒没有被当成约数倒数权重上界。

## 追加锚（本行以下为增补区）

## 162. 源规模预算、有限素方向与缺素数补位

本节到 §164 继续使用标准来源 $n=5040F_j$，其中 $F_0=0,F_1=1,j\ge3$；$D=2^{15}3^{10}5^87^511^5=2045861090389670400000000$。这里的指标必须与同一个整数来源相符。任意整数的 Zeckendorf 编码，不是单项 Fibonacci 来源的证明。新增论证为文献输入上的纸面推导；新增桥接尚未 Lean 形式化。

**命题 162.1（来源规模加强局部停止）。** 若 $D\mid j$，令 $L=\log\log(5040F_j)$、$a_0=94243/10^7$，则

$$
\log(5040F_j)>j/4,\qquad L>\log(j/4)>54,\qquad 5040F_j>N_K.
$$

因此，对实际整除该 $n$ 的素数集 $P$，任何已证下界 $0<h<L$ 都给出充分条件

$$
\prod_{p\in P}(1-p^{-v_p(n)-1})\left(1+\frac{a_0}{h^3}\right)\le1
\quad\Longrightarrow\quad
\frac{\sigma(n)}n<e^\gamma\log\log n.
$$

证明。$j$ 为偶数，递推给 $F_j\ge2^{j/2-1}$，因 $5040>2$、$\log2>1/2$，有 $\log(5040F_j)>j/4$。有理比较 $(49/18)^{54}<D/4$ 与 $e<49/18$ 给 $L>54$。又 $\log N_K\le K\log p_K<32\cdot10^{12}<D/4$，所以进入 Axler 的解析范围。保留同一整数的局部因子，再用 $a_0/L^3<a_0/h^3$，即得结论。特别地，$h=54$ 时可用阈值 $1574640000000/1574640094243$。$\square$

若该标准来源违反 Robin，依次使用整数下界 $h=54,61,64$，五个独立素方向给出它必须满足的条件链

$$
D\mid j\ \Longrightarrow\ 1260D\mid j\ \Longrightarrow\ 27720D\mid j
$$

三步分别迫使 $n$ 的五赋值至少为 $(23,15,10,8,6)$、$(24,15,10,8,7)$、$(24,15,10,8,7)$。计算规则是：$p^{a+1}\le1+h^3/a_0$ 时指数 $a$ 已安全。此处第三步没有继续增长，只描述这五个单因子和整数取整策略；不能解释成所有联合判据都已穷尽。

**命题 162.2（固定九方向的明确方法反例）。** 令 $P_9=2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17\cdot19\cdot23$，$j=DP_9^{10}$。在这个实际来源上，前九素数的 $n$ 赋值为

$$
(31,23,19,17,16,11,11,11,11).
$$

即使用真实 $L$，九因子充分条件 $\eta_9(1+a_0/L^3)\le1$ 也失败；但 $v_{29}(n)=1$，加入素数 $29$ 后即可认证 Robin。

证明。赋值由 §95 的提升公式和首秩求得，也可用模 $p^{a+1}$ 的 Fibonacci 快速倍增独立核验。精确有理数给 $1-\eta_9<1/(4\cdot10^9)$。另一方面 $D<e^{57}$、$P_9<e^{20}$，故 $j<e^{257}$；由 $F_j<2^j$ 与 $j>9$ 得 $\log n<2j$、$L<258$。而

$$
\frac{a_0}{258^3+a_0}>\frac1{2\cdot10^9}>1-\eta_9,
$$

所以该九因子条件失败。$29$ 的首次整除秩为 $14\mid D$，首赋值为一，且 $29\nmid j$，从而 $v_{29}(n)=1$；其局部因子已经满足 §160.1 的停止条件。这是方法的反例，不是 Robin 反例。$\square$

**命题 162.3（真实缺素数的补位证书）。** 仍设 $D\mid j$、$n=5040F_j$。令 $P$ 为实际整除 $n$ 的素数集，$Q$ 为互不相同且均不整除 $n$ 的素数之积，允许 $Q=1$。若 $0<h\le\log(j/4)$、$b\ge\log Q$，则

$$
\eta_P(n)\prod_{q\mid Q}\left(1-\frac1q\right)
\left(1+\frac{4b}{jh}\right)
\left(1+\frac{a_0}{h^3}\right)\le1
$$

足以认证 Robin。

证明。由于缺素数与 $n$ 互素，totient 恒等式为

$$
\frac n{\varphi(n)}
=\prod_{q\mid Q}\left(1-\frac1q\right)
\frac{nQ}{\varphi(nQ)}.
$$

在 $nQ>N_K$ 应用 Axler。写 $L_Q=\log\log(nQ)$，则 $L_Q\ge L>h$，而

$$
\frac{L_Q}L
=1+\frac{\log(1+\log Q/\log n)}L
\le1+\frac{4b}{jh}.
$$

乘以同一 $n$ 的真实局部因子即得结论。这没有把缺素数插入 $\eta_P$；收益来自补位前后的 totient 比值，并明确扣除了规模增加的成本。$\square$

`source_scale.py` 在指定素数与赋值深度预算内读取同一 $j$ 的模响应。非零模余数给精确赋值；超过预算时只保留已知下界，并把未知局部因子上界置为 $1$。预算耗尽返回未定。在命题 162.2 的来源上，前九方向返回未定，观察 $29$ 给安全证书；如果所有正赋值只读到一层，继续观察到缺素数 $59$ 也能通过命题 162.3 给证书。这些是有限计算接口，不代替下一节对所有未见素数的统一估计。

## 163. 首次整除秩切面与未见素数的统一尾界

记 $z(p)$ 为素数 $p$ 第一次整除 Fibonacci 数的正指标。经典秩性质为

$$
p\mid F_j\iff z(p)\mid j,
\qquad p\ne2,5\Longrightarrow z(p)\mid p-1\text{ 或 }z(p)\mid p+1.
$$

这些性质的原文定位是 Lengyel (1995), p.236, §3 开头与 Theorem A；仓内 `FibonacciRank` 的 `fibonacci_entry_point` 和 `fibonacci_rank_dvd_prime_bound` 给相应形式化接口。这里不需要首赋值为一，不假设 WSS 素数不存在。

**引理 163.1（一个秩桶的 Euler 对数贡献）。** 对整数 $d>5$，令 $\mathcal P_d=\{p\text{ 素数}:z(p)=d\}$。则

$$
\sum_{p\in\mathcal P_d}\log\frac p{p-1}
\le\frac{6H_d}{d}\le\frac{6(1+\log d)}d,
\qquad H_d=\sum_{k=1}^d\frac1k.
$$

证明。桶内不同素数的乘积整除 $F_d<2^d$，所以个数小于 $d$。因 $z(2)=3,z(5)=5$，此桶不含例外素数。每个素数写作 $p=kd\pm1$，$k\ge1$，且每个 $k$ 至多对应两个素数。由 $kd\ge3$，

$$
\log\frac p{p-1}\le\frac1{p-1}\le\frac3{kd}.
$$

按 $k$ 递增排列，固定至多个数时倒数和由最小允许的 $k$ 给上界；粗放地保留每个 $k=1,\ldots,d$ 的两个位置已足够。因此总和至多 $6H_d/d$。最后使用调和数的积分上界。这里估计的是 $\log(p/(p-1))$，不是 $(\log p)/(p-1)$。$\square$

**命题 163.2（共同指标的大小秩分解）。** 令 $j\ge3$、$t=\tau(j)$、$Y\ge5$，并设

$$
A=\prod_{\substack{d\mid j\\d\le Y}}F_d\ge2.
$$

则

$$
\frac{F_j}{\varphi(F_j)}
=\frac A{\varphi(A)}\exp(R),
\qquad
0\le R\le\frac{6t(1+\log Y)}Y.
$$

证明。小秩素数 $z(p)\le Y$ 且 $p\mid F_j$ 的集合，恰是 $A$ 的素支撑：两个方向分别用 $z(p)\mid j$ 和 $z(p)\mid d$。其 Euler 乘积恰为 $A/\varphi(A)$，不要求 $A\mid F_j$。其余素数按不同的 $d\mid j,d>Y$ 分桶，每个素数恰出现一次。引理 163.1 与 $(1+\log x)/x$ 在 $x>1$ 的递减性给尾界，因为桶数不超过 $t$。$\square$

这是一种可直接用于 Robin 的 FIB 素切面：用来源指标的因子关系把所有素数通道分组，保留小秩的共同素支撑，并一次估计全部高秩贡献。权重由 Euler 乘积给出，不是五窗区间的长度权重。黄金递归在这里实际提供的是模素数回返关系 $z(p)\mid j$ 与 $z(p)\mid p\pm1$。

## 164. 标准 Fibonacci 倍数族的纸面 Robin 估计

本节把 §163 的尾界与已发表的解析输入合成。结论只关于 $5040F_j$ 这条标准来源族；没有覆盖所有合法五窗仿射历史。外部解析定理、其大规模有限验证和新增合成证明均未在本项目中重新形式化。

**引理 164.1（Axler 输入导出的通用包络）。** 对每个整数 $A\ge2$，有

$$
\frac A{\varphi(A)}
<e^\gamma\max\{32,\log\log A+a_0\},\qquad a_0=0.0094243.
$$

证明。若 $A\ge N_K$，§160.1 的解析输入以及 $\log\log A>1$ 直接给结论。若 $A<N_K$，其不同素因子数小于 $K$；把这些素数逐个换成最小的连续素数只增加 Euler 乘积，故 $A/\varphi(A)\le N_K/\varphi(N_K)$。又

$$
1<\log\log N_K<63/2,
$$

因为 $K\log2\le\log N_K\le K\log p_K<32\cdot10^{12}$，且 $e^{63}>(32\cdot10^{12})^2$。在 $N_K$ 使用 Axler 得 $N_K/\varphi(N_K)<32e^\gamma$。$\square$

**引理 164.2（指标除数数目的显式界）。** 对任意正整数 $j$，

$$
\tau(j)\le8(3/35)^{1/3}j^{1/3}<4j^{1/3}.
$$

证明。逐素数最大化 $(a+1)/p^{a/3}$。素数 $2,3,5,7$ 的最大值分别为 $2,3^{1/3},2/5^{1/3},2/7^{1/3}$，达到最大值的指数为 $3,2,1,1$；相邻比值 $(a+2)/(a+1)$ 递减，故只需检查这些峰值两侧。对 $p\ge11$，$a+1\le2^a\le p^{a/3}$。相乘得到第一式，常数立方 $1536/35<64$ 给第二式。第一式在 $j=2520$ 取等。$\square$

**定理 164.3（已发表输入上的标准来源族结论）。** 在 §160 引用的 Robin 有限验证、Axler 解析上界及 §95 引用的经典 Fibonacci 赋值定理下，

$$
\forall j\ge3,\qquad
\frac{\sigma(5040F_j)}{5040F_j}
<e^\gamma\log\log(5040F_j).
$$

这些输入均为已发表的无条件结果；本节给其纸面组合，没有增加 RH 假设。

证明。若 $D\nmid j$，§95 的五停止条件至少一条成立，结论已有。因此只需 $D\mid j$。定义

$$
v=\log j>55,\qquad t=\tau(j)\ge\tau(D)=57024,
\qquad u=\log t>10,\qquad Y=\lceil512tu\rceil.
$$

$\log D>55$、$\log57024>10$ 可由 $65/24<e<49/18$ 的有理幂比较核对。引理 164.2 与 $\log4<7/5$ 给

$$
u<v/3+7/5.
$$

在命题 163.2 中使用这个 $Y$。由于 $3\mid j,Y\ge3$，乘积 $A$ 包含 $F_3=2$，故 $A\ge2$。由 $F_d<2^d<e^d$，得到 $\log A<tY$。又 $Y\le513tu$、$\log513<7$，因此

$$
\log Y<7+u+\log u.
$$

对于 $u\ge10$，有 $\log u\le u/4$：在 $10$ 处由 $e^5>100$ 验证，之后 $u/4-\log u$ 的导数为正。于是高秩对数尾界满足

$$
R\le\frac{6t(1+\log Y)}Y
<\frac6{512}\left(1+\frac{8+\log u}{u}\right)
<\frac{123}{5120}<\frac1{40}.
$$

由 $e^x\le(1-x)^{-1}$ 对 $0\le x<1$，得 $e^R<40/39$。同时

$$
\begin{aligned}
\log(tY)+a_0
&<7+2u+\log u+1/100\\
&\le7+9u/4+1/100\\
&<3v/4+254/25.
\end{aligned}
$$

因 $v>55$，右端也大于 $32$。结合引理 164.1、命题 163.2，得到

$$
\frac{F_j}{\varphi(F_j)}
<e^\gamma\frac{40}{39}\left(\frac34v+\frac{254}{25}\right)
<e^\gamma(v-7/5).
$$

最后一个比较的差恰为 $3v/13-461/39$，在 $v=55$ 为 $34/39>0$，随 $v$ 严格增加。命题 162.1 给 $\log\log(5040F_j)>v-\log4>v-7/5$。

最后核对共同素支撑：$z(2),z(3),z(5),z(7)$ 分别为 $3,4,5,8$，全都整除 $D$，所以 $2,3,5,7\mid F_j$。因此 $5040F_j$ 与 $F_j$ 的素支撑相同，且

$$
\frac{\sigma(5040F_j)}{5040F_j}
<\frac{5040F_j}{\varphi(5040F_j)}
=\frac{F_j}{\varphi(F_j)}
<e^\gamma\log\log(5040F_j).
$$

这就处理了 $D\mid j$ 的全部指标，与前一分支合成全族结论。$\square$

本节相对于 §§95、160 的必要整除区域，补上了该标准来源族的全指标估计；旧区域仍是旧充分条件的合法未决输出，但已不代表本族在上述纸面组合下仍可能超界。更一般的 $n=5040\sum_r F_{j_r}$ 或任意五窗来源，没有 $p\mid n\Rightarrow z(p)\mid j$ 这样一个共同指标关系，不能套用定理 164.3。连接任意 FIB 地址与同等强度的素支撑尾界，是仍未解决的证明义务。

有限核验由 [源规模程序](../../reports/fib-robin-boundary/source_scale.py) 与 [精确输出](../../reports/fib-robin-boundary/source_scale.json) 给出：所有阈值使用有理数；大指标模响应由倍增和独立矩阵幂对照；小指标 $1\le j\le48$ 的实际因子给出 77 个高秩桶检查。它们核验常数与有限实现，不承担全称定理。新增内容是经典秩性质与已发表 Robin 输入的综合；未完成文献重复性判断，不主张原创。现有 `FibonacciRank` 已在本快照定向构建成功；这不等于新增 §164.3 已经通过 Lean。

## 追加锚（本行以下为增补区）

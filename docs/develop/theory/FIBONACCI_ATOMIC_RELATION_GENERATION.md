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

在独立加入 Hilbert 空间 $\mathbb C^n$、计算基和等权相干叠加后，定义

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

对奇数 (n)，定义

$$
V_n|s\rangle
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

## 追加锚（本行以下为增补区）

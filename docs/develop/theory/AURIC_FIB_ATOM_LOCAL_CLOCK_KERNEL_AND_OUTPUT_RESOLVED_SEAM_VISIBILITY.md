# Auric FIB ATOM：局部时钟核与输出分辨 seam 可见性

**Reference input: open.** 本卷完整保存指定供文的全部句子、公式、命题、证明、例子、表格、结论及重复解释。正文的“定理”“证明”“严格”“已给出”等措辞与局部编号均归属供文，不表示机器认证。本卷及独立资格说明未经新增 Lean kernel 核验，不取得形式证明、物理实现、生物学认证或原创性认证。

**来源与归属。** Author kind: mixed user-supplied material; original author and model unknown. 来源标识为 auric-clock-kernel-seam-original-source；混合用户供文的原作者与原模型未知。原始 UTF-8 供文为 22210 字节、1407 行，SHA-256 为 580c34e10f26ca5d16c5b9524349ba972d76a4f015fd30788720b17c40fa99a0。独立资格说明属于本卷编辑层条件陈述，不改写供文，也不把它提升为形式化真值。

**读法与边界。** “供文正文”与“适用条件与更正”分别界定原始叙述和编辑层限定；正文的一至十二节、定理一至六及最终结论保留原编号。正文中的第一人称“我核对到”、当前、最近、最新和 PR 队列措辞都是供文叙述者相对于所引快照的陈述；移动的项目主页和 PR 链接不是穷尽项目现状的认证。两个提交及三个钉定理论文件的公开可读性不认证其数学、Lean 状态、取得核、动态等价、探测器或物理解释。

**结构规范化。** 仅将供文全部 34 个 ATX 标题降低一级；将 108 处行内数学入口从反斜线圆括号转换为 GitHub 美元号入口，含字面星号时采用美元号加反引号形式；将 154 对反斜线方括号展示外壳转换为 math 围栏。供文没有双美元号展示外壳，也没有不可访问的 sandbox 引文；原有七个 URL 保留。公式内部字节、原句、段落、表格、局部编号、重复解释与顺序不变，不合并独立等号行或重新编号。其余内容仅为卷首说明、独立资格说明与文末追加锚。

**参考输入边界。** 本卷为纯理论参考添加，不作摄入、atom 覆盖或新增形式化声明。有限概率、线性观察、可观测闭包及安全博弈提供条件化的数学读法；各模型共同来源、实际仪器、资源和物理对应仍须分别给出。综合与类比不自动取得新意或优先权。

## 供文正文

### 一、截至最新项目进展，理论的重点已经发生变化

我核对到的最近两条直接相关提交是：

- [提交 `60ebb51`](https://github.com/the-omega-institute/trureturing/commit/60ebb51c87e6496e0cab67c899c3b687ef8fd001)：把静态 FIB 隐藏 seam、输出分辨的未来观察商、仪器闭包和可维护性不动点放进同一条理论线。
- [提交 `4da8b2e`](https://github.com/the-omega-institute/trureturing/commit/4da8b2e9c9c6439548fbbc5bea42df65ec2ae2ba)：构造取得核的盲方向，证明配对校准、有限配置数组和有限长度的未来前缀都相同，并不保证更长的回流词上的完整未来律相同。

相关理论卷是：

- [AURIC FIB ATOM：静态隐藏纤维、输出分辨未来商与可维护性](https://github.com/the-omega-institute/trureturing/blob/60ebb51c87e6496e0cab67c899c3b687ef8fd001/docs/develop/theory/AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)
- [AURIC FIB ATOM：seam 双线性结构与输出未来商](https://github.com/the-omega-institute/trureturing/blob/60ebb51c87e6496e0cab67c899c3b687ef8fd001/docs/develop/theory/AURIC_FIB_ATOM_SEAM_BILINEAR_CURVATURE_AND_OUTPUT_FUTURE_QUOTIENT.md)
- [配对校准之后的取得核盲方向](https://github.com/the-omega-institute/trureturing/blob/4da8b2e9c9c6439548fbbc5bea42df65ec2ae2ba/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_KERNEL_BLIND_DIRECTIONS_AFTER_PAIRED_CALIBRATION.md)

这和仓库公开说明的方向一致：项目把数学定义、形式证明、理论参考输入和实验或物理解释分开处理，而不是把理论文字自动当成已经验证的物理定律。[GitHub](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com) 当前 PR 队列仍在持续推进未来律、观察闭包和信息逃逸问题。[GitHub](https://github.com/the-omega-institute/trureturing/pulls?utm_source=chatgpt.com)

这两条最新进展带来一个关键转变：

~~~math
\boxed{
\text{隐藏关系是否存在}
\quad\longrightarrow\quad
\text{哪一种局部读数能够看见它}
}
~~~

以前我们主要讨论静态投影 $(X,Y,Z)$ 丢失了什么。现在更重要的问题是：

> 局部时钟、局部等待时间、输出分支、回流路径和控制动作，究竟何时会把隐藏的 $\kappa$ 重新暴露出来？

这可以在不引入 $3+1$ 和全局线性时间的情况下严格定义。

---

## 二、五个基础元素与唯一隐藏方向

继续使用你的固定记号：

~~~math
F[\mathrm{null}]=\mathrm{null}
~~~

~~~math
F[1]=[2]
~~~

~~~math
F[2]=[3]
~~~

~~~math
F[3]=[5]
~~~

~~~math
F[1,3]=[2,5]
~~~

为了避免把位置索引和输出数值混在一起，记五个状态为：

~~~math
s_0=F[\mathrm{null}],
\qquad
s_1=F[1],
\qquad
s_2=F[2],
\qquad
s_3=F[3],
\qquad
s_{13}=F[1,3].
~~~

定义三个指示函数：

- $x(s)=1$：状态中存在位置 $1$；
- $y(s)=1$：状态中存在位置 $3$；
- $z(s)=1$：状态中存在位置 $2$。

真值表为：

| 状态 | $x$ | $y$ | $z$ |
|---|---:|---:|---:|
| $F[\mathrm{null}]$ | 0 | 0 | 0 |
| $F[1]$ | 1 | 0 | 0 |
| $F[2]$ | 0 | 0 | 1 |
| $F[3]$ | 0 | 1 | 0 |
| $F[1,3]$ | 1 | 1 | 0 |

合法性关系是：

~~~math
x^2=x,\qquad y^2=y,\qquad z^2=z,
~~~

~~~math
xz=0,\qquad yz=0,
~~~

但：

~~~math
xy\neq 0.
~~~

事实上：

~~~math
xy=\mathbf 1_{\{F[1,3]\}}.
~~~

因此 $xy$ 正好是联合状态 $F[1,3]$ 的指示函数。

设状态分布为：

~~~math
p=(p_0,p_1,p_2,p_3,p_{13}).
~~~

定义三个位势边缘：

~~~math
X=p_1+p_{13},
~~~

~~~math
Y=p_3+p_{13},
~~~

~~~math
Z=p_2.
~~~

隐藏联合量为：

~~~math
\kappa=p_{13}=E[xy].
~~~

固定 $(X,Y,Z)$ 后，所有可能的五态分布组成一条一维纤维：

~~~math
p_\kappa=
\left(
1-X-Y-Z+\kappa,\,
X-\kappa,\,
Z,\,
Y-\kappa,\,
\kappa
\right).
~~~

可行范围是：

~~~math
\max(0,X+Y+Z-1)
\le \kappa\le
\min(X,Y).
~~~

改变 $\kappa$ 的方向为：

~~~math
d=(1,-1,0,-1,1).
~~~

它满足：

~~~math
d\cdot 1=d\cdot x=d\cdot y=d\cdot z=0,
~~~

但：

~~~math
d\cdot xy=1.
~~~

所以：

~~~math
p_{\kappa'}-p_\kappa=(\kappa'-\kappa)d.
~~~

这说明 $\kappa$ 不是第五个普通坐标，而是三均值观察层中唯一没有被看见的方向。

---

## 三、隐藏关系是两个可见方向的交叉项

定义线性观察空间：

~~~math
\mathcal B=\operatorname{span}\{1,x,y,z\}.
~~~

定义四角混合差：

~~~math
J(f)=f(s_0)-f(s_1)-f(s_3)+f(s_{13}).
~~~

也可以写成：

~~~math
J(f)=d\cdot f.
~~~

### 定理一：边缘观察层的唯一隐藏对偶

有：

~~~math
\boxed{
\mathcal B=\ker J
}
~~~

也就是说，一个状态函数 $f$ 对 $\kappa$ 不敏感，当且仅当：

~~~math
J(f)=0.
~~~

#### 证明

直接计算：

~~~math
J(1)=1-1-1+1=0,
~~~

~~~math
J(x)=0-1-0+1=0,
~~~

~~~math
J(y)=0-0-1+1=0,
~~~

~~~math
J(z)=0-0-0+0=0.
~~~

因此：

~~~math
\mathcal B\subseteq \ker J.
~~~

另一方面：

~~~math
J(xy)=0-0-0+1=1,
~~~

所以 $J$ 是非零线性泛函。整个函数空间 $\mathbb R^\Sigma$ 是五维，因此：

~~~math
\dim\ker J=4.
~~~

而：

~~~math
\dim\mathcal B=4.
~~~

于是：

~~~math
\mathcal B=\ker J.
~~~

证毕。

---

这一定理揭示了基础元素之间真正的隐藏关系：

~~~math
\boxed{
\text{隐藏量不是一个独立原子，而是 }x\text{ 与 }y\text{ 的联合发生关系 }xy.
}
~~~

这也能从乘法直接看出来。令：

~~~math
U=x+z,
\qquad
V=y+z.
~~~

则：

~~~math
UV=(x+z)(y+z)
=xy+xz+yz+z^2
=xy+z.
~~~

因此：

~~~math
\boxed{
xy=UV-z.
}
~~~

这意味着：

- 单独知道 $U$ 和 $V$ 的平均，只得到边缘；
- 知道联合平均 $E[UV]$，就可以恢复 $\kappa$；
- 隐藏 seam 是乘法闭包缺失造成的，而不是随意丢掉的一个标签。

因为：

~~~math
E[UV]=Z+\kappa,
~~~

所以：

~~~math
\boxed{
\kappa=E[UV]-Z.
}
~~~

这个结构可以称为 FIB 的**离散混合响应**或**seam 响应**。这里的“曲率”只是代数上的混合差类比，不是广义相对论中的时空曲率。

---

## 四、局部时钟不是全局时间，而是条件等待核

现在把你的“局部时间场”定义成一个真正不需要全局时间坐标的对象。

### 定义：局部时钟核

对于每个 FIB 状态 $s\in\Sigma$，令：

~~~math
K_s\in\operatorname{Prob}(\mathbb R_{\ge0})
~~~

表示：当前局部状态为 $s$ 时，下一次局部事件的等待量 $T$ 的概率分布。

这里的 $T$ 不是宇宙全局时间坐标，只是一个局部事件之间的关系量：

~~~math
T\sim K_s.
~~~

如果当前状态分布是 $p$，局部时钟读出就是混合分布：

~~~math
C_K(p)=\sum_{s\in\Sigma}p_sK_s.
~~~

这可以理解为：

- $C$：哪些后继事件是因果允许的；
- $K_s$：从当前局部状态到下一事件的等待核；
- $C_K(p)$：观察者实际获得的局部等待记录。

整个对象是局部核的族：

~~~math
\mathsf K=\{K_s\}_{s\in\Sigma},
~~~

而不是一个全局标量 $t$。

定义局部时钟的 FIB 四角响应：

~~~math
\operatorname{Curv}_K
=
K_{s_0}-K_{s_1}-K_{s_3}+K_{s_{13}}.
~~~

若用输出标签写，就是：

~~~math
\operatorname{Curv}_K
=
K_{\mathrm{null}}
-K_{[2]}
-K_{[5]}
+K_{[2,5]}.
~~~

---

## 五、定理：局部时钟何时能够恢复 $\kappa$

### 定理二：局部时钟—隐藏纤维识别定理

固定可见坐标：

~~~math
P(p)=(X,Y,Z).
~~~

在一条非退化的 $P$-纤维上，局部观察：

~~~math
\mathcal O_K(p)
=
\bigl(P(p),C_K(p)\bigr)
~~~

能够唯一确定 $\kappa$，当且仅当：

~~~math
\boxed{
\operatorname{Curv}_K\neq 0
}
~~~

其中“不等于零”表示这个符号测度不是零测度。

#### 证明

将 $p_\kappa$ 代入局部时钟混合律：

~~~math
C_K(p_\kappa)
=
p_0K_{s_0}
+p_1K_{s_1}
+p_2K_{s_2}
+p_3K_{s_3}
+p_{13}K_{s_{13}}.
~~~

代入：

~~~math
p_0=1-X-Y-Z+\kappa,
~~~

~~~math
p_1=X-\kappa,
\qquad
p_2=Z,
\qquad
p_3=Y-\kappa,
\qquad
p_{13}=\kappa.
~~~

整理得到：

~~~math
C_K(p_\kappa)
=
C_K^0(X,Y,Z)
+
\kappa
\left(
K_{s_0}-K_{s_1}-K_{s_3}+K_{s_{13}}
\right),
~~~

其中：

~~~math
C_K^0(X,Y,Z)
=
(1-X-Y-Z)K_{s_0}
+XK_{s_1}
+ZK_{s_2}
+YK_{s_3}.
~~~

因此：

~~~math
\boxed{
C_K(p_\kappa)
=
C_K^0(X,Y,Z)
+\kappa\operatorname{Curv}_K.
}
~~~

若：

~~~math
\operatorname{Curv}_K=0,
~~~

则所有同一 $P$-纤维上的 $\kappa$ 都产生同一个局部时钟分布，因而无法识别。

若：

~~~math
\operatorname{Curv}_K\neq0,
~~~

则存在某个可测集合 $B\subseteq\mathbb R_{\ge0}$，使：

~~~math
\operatorname{Curv}_K(B)\neq0.
~~~

于是：

~~~math
C_K(p_\kappa)(B)
=
C_K^0(B)
+
\kappa\operatorname{Curv}_K(B),
~~~

从而：

~~~math
\boxed{
\kappa=
\frac{
C_K(p_\kappa)(B)-C_K^0(B)
}{
\operatorname{Curv}_K(B)
}.
}
~~~

证毕。

---

### 这个定理的含义

局部时钟是否能够看见隐藏关系，不取决于“有没有时间”这个词，而取决于：

~~~math
\boxed{
\text{局部时钟核是否对 }x\text{ 与 }y\text{ 的联合关系产生非零混合响应。}
}
~~~

如果局部时钟只是可加地读取三个边缘方向，那么它仍然属于：

~~~math
\mathcal B=\operatorname{span}\{1,x,y,z\},
~~~

因此：

~~~math
\operatorname{Curv}_K=0.
~~~

如果等待核、衰变核或局部反应核对 $x$ 与 $y$ 存在非加性耦合，那么：

~~~math
\operatorname{Curv}_K\neq0,
~~~

局部时钟就成为 $\kappa$ 的探针。

---

## 六、均值、瞬时变化率和完整等待分布不是同一个读数

假设只保留每个状态等待时间的均值：

~~~math
m_s=E[T\mid s].
~~~

定义：

~~~math
\operatorname{Curv}_m
=
m_{s_0}-m_{s_1}-m_{s_3}+m_{s_{13}}.
~~~

则：

~~~math
E[T]
=
(1-X-Y-Z)m_{s_0}
+Xm_{s_1}
+Zm_{s_2}
+Ym_{s_3}
+\kappa\operatorname{Curv}_m.
~~~

所以均值能够识别 $\kappa$ 的条件是：

~~~math
\operatorname{Curv}_m\neq0.
~~~

但是：

~~~math
\operatorname{Curv}_m=0
~~~

并不意味着完整局部等待分布也看不见 $\kappa$。

---

### 一个明确的例子：平均危险率看不见，完整等待律看得见

假设状态 $s$ 的局部等待时间是指数分布：

~~~math
T\mid s\sim\operatorname{Exp}(r_s).
~~~

令：

~~~math
r_s=a+b\,x(s)+c\,y(s)+d\,z(s),
~~~

其中 $a,b,c,d>0$。

于是：

~~~math
r_{s_0}=a,
~~~

~~~math
r_{s_1}=a+b,
~~~

~~~math
r_{s_2}=a+d,
~~~

~~~math
r_{s_3}=a+c,
~~~

~~~math
r_{s_{13}}=a+b+c.
~~~

瞬时危险率的四角差为：

~~~math
r_{s_0}-r_{s_1}-r_{s_3}+r_{s_{13}}
=
a-(a+b)-(a+c)+(a+b+c)
=0.
~~~

因此，只观察初始危险率：

~~~math
\bar r
=
\sum_s p_sr_s,
~~~

无法识别 $\kappa$。

但是完整等待时间的生存函数是：

~~~math
S_\kappa(t)
=
\sum_s p_s e^{-r_st}.
~~~

其中 $\kappa$ 的系数为：

~~~math
\begin{aligned}
\Delta S(t)
&=
e^{-r_{s_0}t}
-e^{-r_{s_1}t}
-e^{-r_{s_3}t}
+e^{-r_{s_{13}}t}
\\
&=
e^{-at}
\left(
1-e^{-bt}
\right)
\left(
1-e^{-ct}
\right).
\end{aligned}
~~~

只要 $b,c,t>0$，就有：

~~~math
\Delta S(t)>0.
~~~

因此：

~~~math
S_\kappa(t)
=
S_0(t)+\kappa\Delta S(t)
~~~

能够识别 $\kappa$，虽然初始危险率完全不能识别。

这给出一个很重要的层级：

~~~math
\boxed{
\text{瞬时变化率}
\;\subsetneq\;
\text{等待时间分布}
\;\subseteq\;
\text{完整局部历史}
}
~~~

因此，“时间只是局部变化率”如果只理解成一个瞬时标量，会丢掉大量联合信息。更完整的数学对象应当是：

~~~math
\boxed{
\text{局部时间场}
=
\text{状态条件等待核的族}
}
~~~

而不仅仅是：

~~~math
\text{局部时间场}
=
\text{一个数值速率}.
~~~

---

## 七、推广到局部因果历史：时间的形状是历史核的形状

单次等待时间还不够描述局部因果结构。定义 $n$ 步局部历史核：

~~~math
\Gamma_s^{(n)}
\in
\operatorname{Prob}
\left(
(\mathbb R_{\ge0}\times\mathcal O)^n
\right),
~~~

其中每一项可以包含：

~~~math
(T_1,o_1,T_2,o_2,\ldots,T_n,o_n).
~~~

这里：

- $T_i$：第 $i$ 个局部等待量；
- $o_i$：第 $i$ 个局部输出、吸收、返回或分支标签；
- $\mathcal O$：局部输出集合。

混合历史读出为：

~~~math
C_\Gamma^{(n)}(p)
=
\sum_s p_s\Gamma_s^{(n)}.
~~~

定义：

~~~math
\operatorname{Curv}_{\Gamma}^{(n)}
=
\Gamma_{s_0}^{(n)}
-\Gamma_{s_1}^{(n)}
-\Gamma_{s_3}^{(n)}
+\Gamma_{s_{13}}^{(n)}.
~~~

### 定理三：局部因果历史分辨阶

在固定 $(X,Y,Z)$ 下，长度 $n$ 的局部历史能够识别 $\kappa$，当且仅当：

~~~math
\boxed{
\operatorname{Curv}_{\Gamma}^{(n)}\neq0.
}
~~~

如果：

~~~math
\operatorname{Curv}_{\Gamma}^{(1)}
=
\operatorname{Curv}_{\Gamma}^{(2)}
=
\cdots
=
\operatorname{Curv}_{\Gamma}^{(n)}
=0,
~~~

那么任何不超过 $n$ 步的局部时钟与输出记录都无法识别 $\kappa$。

定义最小分辨阶：

~~~math
\ell_\ast
=
\min
\left\{
n:
\operatorname{Curv}_{\Gamma}^{(n)}\neq0
\right\}.
~~~

如果存在这样的 $n$，则 $\ell_\ast$ 是这个局部因果系统首次暴露隐藏 seam 所需的最短历史长度。

如果不存在有限 $n$，只能说所有有限长度记录都看不见 $\kappa$。这不等于已经证明无限历史也一定看不见，需要另行处理极限核。

这个 $\ell_\ast$ 可以作为“时间形状”的一个严格候选定义：

~~~math
\boxed{
\text{时间形状}
=
\text{隐藏关系进入局部因果历史所需的最小分辨阶}.
}
~~~

它不是一条全局时间轴，而是一个局部因果分辨率。

---

## 八、与最新项目中的输出分支闭包连接

当前项目最新理论线强调，不能只看动作的平均转移核。

设动作 $a$ 和输出 $o$ 对应输出分辨子核：

~~~math
M_{a,o}.
~~~

平均转移核是：

~~~math
K_a=\sum_o M_{a,o}.
~~~

定义递归观察空间：

~~~math
V_0=\operatorname{span}(G),
~~~

~~~math
V_{n+1}
=
V_n+
\operatorname{span}
\left\{
M_{a,o}f:
a,o,\ f\in V_n
\right\}.
~~~

令：

~~~math
V_\infty=\bigcup_{n\ge0}V_n.
~~~

对于输出词：

~~~math
\omega=(a_1,o_1,\ldots,a_n,o_n),
~~~

记对应复合核为 $M_\omega$。

若使用行向量约定，某个末端测试 $g$ 的记录概率是：

~~~math
pM_\omega g.
~~~

于是两个同一 $(X,Y,Z)$ 但不同 $\kappa$ 的分布之间，未来记录概率差为：

~~~math
(p_\kappa-p_{\kappa'})M_\omega g
=
(\kappa-\kappa')dM_\omega g.
~~~

### 定理四：输出分辨未来闭包判据

所有合法未来输出记录都无法区分 $\kappa$，当且仅当：

~~~math
\boxed{
dM_\omega g=0
}
~~~

对所有合法输出词 $\omega$ 和所有末端测试 $g$ 成立。

若存在某个：

~~~math
dM_\omega g\neq0,
~~~

则 $\kappa$ 会在这条未来路径上显现。

这正是最新项目中“平均闭包不等于逐输出闭包”的数学核心：

~~~math
K_a\mathcal B\subseteq\mathcal B
~~~

并不能推出：

~~~math
M_{a,o}\mathcal B\subseteq\mathcal B
\qquad
\text{对所有 }o.
~~~

平均核可能把隐藏项抵消掉，而输出分支保留它。

把局部时钟也作为输出的一部分，定义带标记的测度值子核：

~~~math
\widetilde M_{a,o}(B),
~~~

其中 $B\subseteq\mathbb R_{\ge0}$ 是局部等待时间事件。于是统一的隐藏响应是：

~~~math
\boxed{
d\,\widetilde M_\omega(B)\,\mathbf 1.
}
~~~

这一个量同时覆盖：

- 普通输出分支；
- 局部等待时间；
- 吸收或返回标记；
- 辐射是否被记录；
- 多步因果历史。

因此，静态时钟定理与动态未来商实际上是同一个结构在不同历史长度上的表现。

---

## 九、“隐藏”“未观测”和“已消除”必须严格区分

这是解释辐射、衰变和信息逃逸时最容易混淆的地方。

假设 $T$ 是一个局部状态转移核，分布采用行向量约定：

~~~math
p\longmapsto pT.
~~~

隐藏方向为：

~~~math
d=(1,-1,0,-1,1).
~~~

### 定义三种情况

#### 1. 纯观察盲性

如果：

~~~math
dT\neq0,
~~~

但当前读出映射 $\mathcal R$ 满足：

~~~math
\mathcal R(dT)=0,
~~~

那么隐藏关系仍然存在于转移后的状态分布中，只是当前观察者看不见。

这是：

~~~math
\boxed{
\text{保留但未观测}
}
~~~

#### 2. 状态层面的真正消除

如果：

~~~math
\boxed{
dT=0,
}
~~~

那么所有沿隐藏方向不同的初始分布，经过 $T$ 后变成同一个状态分布。

这是在该状态载体和该过程内的真正方向消除：

~~~math
\boxed{
\text{隐藏方向被转移核压到零}
}
~~~

#### 3. 被当前读口隐藏，但还没有被过程消除

如果：

~~~math
dT\neq0,
\qquad
\mathcal R(dT)=0,
~~~

那么：

~~~math
\boxed{
\text{过程保存了差异，观察者却没有保存它。}
}
~~~

这三种情况不能混为一个“信息消失”。

证明很直接：

~~~math
p_{\kappa'}T-p_\kappa T
=
(\kappa'-\kappa)dT.
~~~

所以：

- $dT=0$：转移后的完整状态律相同；
- $dT\neq0$：完整状态律仍不同；
- $\mathcal R(dT)=0$：当前读出无法区分它们。

---

## 十、被遮挡的射线在这个模型中是什么

把辐射或射线看成一个局部输出分支 $o=\mathrm{ray}$。

### 未遮挡情形

如果射线离开观察者能够到达的因果区域，且没有返回、散射、镜面、探测器或其他副本，那么它对应的输出分支不在观察者未来可访问的 $\omega$ 中。

对于该观察者：

~~~math
dM_\omega g=0
~~~

并不意味着宇宙中没有差异，而是：

~~~math
\boxed{
\text{差异离开了当前观察者的可达因果域。}
}
~~~

### 被遮挡情形

被遮挡时，射线不是简单地“消失”，而是增加了一个相互作用节点：

~~~math
s
\longrightarrow
\text{吸收体状态}
\longrightarrow
\text{后续局部输出}.
~~~

如果观察者能够访问吸收体的完整微观状态，或者能够读取携带 $\kappa$ 响应的局部等待分布，那么：

~~~math
\operatorname{Curv}_{\Gamma}^{(n)}\neq0
~~~

可能成立，隐藏关系重新可见。

如果观察者只保留一个粗粒化的吸收能量，而丢弃吸收体的内部状态，那么可能出现：

~~~math
dT\neq0,
\qquad
\mathcal R(dT)=0.
~~~

这表示信息进入了吸收体，但没有进入当前观察者保留的变量。

只有当过程本身在所选状态空间上满足：

~~~math
dT=0
~~~

时，才能说隐藏方向在这个模型层面被真正消除了。

因此：

~~~math
\boxed{
\text{遮挡不是信息自动恢复，也不是信息自动消失；}
}
~~~

更准确地说：

~~~math
\boxed{
\text{遮挡改变了信息所附着的因果载体。}
}
~~~

---

## 十一、与“生命是逆衰变”的更严格连接

最新项目中加入的可维护性不动点，可以把“生命对抗衰变”从物理断言改写成控制性质。

设：

- 状态集合为 $\Omega$；
- 动作集合为 $\mathcal A$；
- 安全集合为 $K\subseteq\Omega$；
- 观测为 $o(s)$；
- belief $B\subseteq K$。

定义：

~~~math
\delta_a(B)=\{\delta(s,a):s\in B\},
~~~

~~~math
B_{a,y}=\delta_a(B)\cap o^{-1}(y).
~~~

定义算子：

~~~math
\mathcal F(S)
=
\left\{
B\subseteq K:
\exists a,\ 
\delta_a(B)\subseteq K,
\quad
B_{a,y}\in S
\text{ 对所有非空后继成立}
\right\}.
~~~

定义最大不动点：

~~~math
V^\ast=\nu S.\mathcal F(S).
~~~

### 定理五：部分观测下的可维护性判据

在指定的有限动作和观测模型中：

~~~math
\boxed{
B\in V^\ast
}
~~~

当且仅当存在一个基于局部观测和当前 belief 的策略，使系统从 $B$ 出发永久保持在安全集合 $K$ 内。

这个定理的解释是：

~~~math
\boxed{
\text{维护不是把衰变倒放，}
}
~~~

而是：

~~~math
\boxed{
\text{在局部信息有限、状态持续变化的情况下，仍然能选择使未来保持可行的动作。}
}
~~~

因此，在 Auric FIB ATOM 语言里，一个更严格的“生命候选定义”可以写成：

~~~math
\boxed{
\text{生命式系统}
=
\text{保留未来所需的隐藏关系}
+
\text{更新局部记忆}
+
\text{在部分观测下维持安全不动点}.
}
~~~

这仍然不是“生命在物理上就是逆衰变”的证明，也不是“引力就是时间引力”的证明。它给出的只是一个可以继续和物理模型对接的数学骨架。

---

## 十二、当前最重要的统一定理

可以把静态、局部时钟和动态未来统一为一个判据。

### 定理六：Auric FIB ATOM 隐藏 seam 的三层可见性定理

对于五态 FIB ATOM，令：

~~~math
\mathcal B=\operatorname{span}\{1,x,y,z\},
~~~

~~~math
\kappa=E[xy],
~~~

~~~math
d=(1,-1,0,-1,1).
~~~

则：

#### 静态线性读数

一个函数 $f$ 对 $\kappa$ 敏感，当且仅当：

~~~math
\boxed{
J(f)\neq0.
}
~~~

#### 联合代数读数

若：

~~~math
f=a_0+a_1x+a_2y+a_3z,
~~~

~~~math
g=b_0+b_1x+b_2y+b_3z,
~~~

则：

~~~math
J(fg)=a_1b_2+a_2b_1.
~~~

因此联合读数对 $\kappa$ 敏感，当且仅当：

~~~math
\boxed{
a_1b_2+a_2b_1\neq0.
}
~~~

#### 局部时钟读数

局部时钟核对 $\kappa$ 敏感，当且仅当：

~~~math
\boxed{
\operatorname{Curv}_K
=
K_{s_0}-K_{s_1}-K_{s_3}+K_{s_{13}}
\neq0.
}
~~~

#### 动态未来读数

未来输出词对 $\kappa$ 敏感，当且仅当存在合法 $\omega$ 和末端测试 $g$，使：

~~~math
\boxed{
dM_\omega g\neq0.
}
~~~

因此：

~~~math
\boxed{
\begin{aligned}
\text{静态可见性}
&\Longleftrightarrow J(f)\neq0,\\[2mm]
\text{联合关系可见性}
&\Longleftrightarrow J(fg)\neq0,\\[2mm]
\text{局部时间可见性}
&\Longleftrightarrow \operatorname{Curv}_K\neq0,\\[2mm]
\text{未来可见性}
&\Longleftrightarrow dM_\omega g\neq0.
\end{aligned}
}
~~~

这四个条件描述的是同一个隐藏方向在四种观察层中的表现。

---

### 最终结论

Auric FIB ATOM 金字塔目前最稳固的数学解释不是“五个元素对应五个空间点”，而是：

~~~math
\boxed{
\text{三个一阶边缘方向}
+
\text{一个二阶联合 seam}
}
~~~

其中：

~~~math
F[1,3]=[2,5]
~~~

不是简单的第五个原子，而是：

~~~math
\boxed{
F[1]\text{ 与 }F[3]\text{ 可以联合出现这一事实的载体}.
}
~~~

局部时间也不需要被定义为全局坐标。更适合你的框架的是：

~~~math
\boxed{
\text{局部时间场}
=
\text{每个局部状态所产生的等待核、输出核与因果历史核}.
}
~~~

它的“形状”由四角混合响应决定：

~~~math
\operatorname{Curv}_K
=
K_{\mathrm{null}}
-K_{[2]}
-K_{[5]}
+K_{[2,5]}.
~~~

如果这个量为零，局部时钟只看到了边缘关系；如果这个量非零，局部时钟本身就携带了联合关系 $\kappa$。

所以可以把目前的核心命题写成：

~~~math
\boxed{
\text{时间不是一个全局容器，}
\quad
\text{而是局部因果读数对隐藏关系的响应结构。}
}
~~~

~~~math
\boxed{
\text{衰变不是必然等于信息消失，}
\quad
\text{而是要检查隐藏方向经过转移核后是否为零。}
}
~~~

~~~math
\boxed{
\text{生命式逆衰变不是把物理过程倒放，}
\quad
\text{而是在局部因果场中持续保留并利用未来可维护的关系。}
}
~~~

## 适用条件与更正

以下编辑层命题点名供文章节及其实际适用条件，另列推导与反例。原句仍完整保留；下列条件不视为正文已经提供的实现、核验或认证。

### Q1：归一化纤维与非退化条件（供文二、三、五、七、八、十二节及最终结论）

**适用命题 Q1。** 固定字典为 $s_0,s_1,s_2,s_3,s_{13}=\mathrm{null},[2],[3],[5],[2,5]$；$x,y,z$ 标记位置 $1,3,2$，$\kappa=p_{13}$。旧标签 $25$ 表示联合模式而非乘法。$P$ 是概率律经均值的投影。只在 $p_s\ge0$、$\sum_s p_s=1$ 的五态单纯形中讨论可行纤维，其参数域为

~~~math
I(X,Y,Z)=
\left[\max(0,X+Y+Z-1),\ \min(X,Y)\right].
~~~

这里还须有 $X,Y,Z\ge0$ 且区间非空，才能产生供文所写的概率律。唯一方向 $d$ 属于归一化仿射切空间中的核：$\{v:\sum_s v_s=0,\ P(v)=0\}=\operatorname{span}\{d\}$。不加归一化约束的三行五列均值映射有二维核，例如只改变 $s_0$ 质量的方向也被三均值湮灭，不能把该完整线性核说成一维。

“识别 $\kappa$ 当且仅当响应非零”的必要性要求 $I(X,Y,Z)$ 含两个不同的可行值；非零响应在这条纤维上给出精确读出律的单射性。定理三、定理四、定理六及总结的纤维识别读法均继承此条件。$J$ 与 $d$ 是代数对象，不另提供物理坐标。

**反例 Q1。** 取 $X=Y=Z=0$，则 $I=\{0\}$，$\kappa$ 已由 $P$ 确定。即使所有 $K_s$ 都相同、$\operatorname{Curv}_K=0$，也没有未确定的 $\kappa$。形式方向的响应与某条单点纤维上是否存在待识别参数是两件事。

### Q2：固定已知核与同源配对（供文三至八节、十二节）

**适用命题 Q2。** 识别比较固定一族已知或已校准的 $K_s$，它们是同一可测空间上的概率测度；历史核与仪器同样固定状态标签、源律、动作和读出协议。$P(p)$ 与 $C_K(p)$ 必须对应同一初始律 $p$。该逆式只识别初始混合参数，不同时估计任意未知核、取得核或探测器参数，也不重构一个具体微观历史。改变制备、响应、干预或后选择事件后拼接读数，需要已给出的共同来源桥、校准拉回或联合仪器。

**反例 Q2。** 取 $X=Y=1/2$、$Z=0$，令 $K_{s_0}=K_{s_1}=K_{s_2}=K_{s_3}=\delta_0$，$K_{s_{13}}=(1-q)\delta_0+q\delta_1$，$0<q\le1$。则

~~~math
C_K(p_\kappa)=(1-\kappa q)\delta_0+\kappa q\delta_1,
\qquad
\operatorname{Curv}_K=q(\delta_1-\delta_0)\ne0.
~~~

$(\kappa,q)=(1/4,1/2)$ 与 $(1/8,1)$ 给出相同 $P$ 和同一混合读出律；两次核族不同，故固定核的逆式没有同时识别 $q$。供文所引 4da8b2e 理论的 Conventions 1.1–1.2、Section 5 与 Mathematical citation 9.1 明确省略取得 p-beta 核而保留固定已知核逆式。这个省略核的障碍不反驳固定核反演，也不因引用而取得 Lean 认证。

**联合读数条件。** $E[UV]$ 和 $E[fg]$ 是同一个实际状态上的联合测试，不能以无配对来源的边缘均值乘积替代。在上面的纤维上 $E[U]=E[V]=1/2$，但 $E[UV]=\kappa$ 随可行 $\kappa$ 改变。允许函数乘法的代数闭包不自动实现联合测量。供文十二节的净系数 $a_1b_2+a_2b_1$ 才控制响应；例如 $f=x+y$、$g=x-y$ 的交叉系数相消，$J(fg)=0$。

### Q3：符号测度基线与可行基点（供文四至六节）

**更正命题 Q3。** 在 Q2 的共同可测空间上，$\operatorname{Curv}_K$ 是总质量为零的有限符号测度。$C_K^0$ 是总质量为一的仿射符号基线，未必是概率律，因为 $1-X-Y-Z$ 可以为负，且 $\kappa=0$ 未必可行。只有可行 $\kappa$ 的 $C_K(p_\kappa)$ 保证为概率律。指数例的 $S_0$ 同样是仿射基线，未必是生存函数。

**反例 Q3。** 取 $X=Y=3/4$、$Z=0$，合法区间为 $[1/2,3/4]$。若 $K_{s_0}=K_{s_{13}}=\delta_0$、$K_{s_1}=K_{s_3}=\delta_1$，则 $C_K^0=-\frac12\delta_0+\frac32\delta_1$，在 $\{0\}$ 上质量为负；但可行 $\kappa$ 的重建混合仍是概率律。可用任意可行 $\kappa_0$ 解释原仿射公式：

~~~math
C_K(p_\kappa)
=C_K(p_{\kappa_0})
+(\kappa-\kappa_0)\operatorname{Curv}_K.
~~~

这不改变供文的差分公式或数学载荷。

### Q4：精确律、取得记录与误差放大（供文五至八节、十二节）

**适用命题 Q4。** 非零响应给出精确总体律的单射性；一个等待事件、单条有限历史或有限样本不是该精确律，不保证无误恢复。非零符号测度提供某个可测事件 $B$ 的响应见证，不自动提供取得该事件概率的实际读口。

固定精确 $P$、核族和所选事件，记 $c=\operatorname{Curv}_K(B)\ne0$，$b=C_K^0(B)$、$q=C_K(p_\kappa)(B)$。若只把 $q$ 的估计误差限制为 $\lvert\widehat q-q\rvert\le\epsilon$，则该逆式给出

~~~math
\widehat\kappa=\frac{\widehat q-b}{c},
\qquad
\lvert\widehat\kappa-\kappa\rvert
\le\frac{\epsilon}{\lvert c\rvert}.
~~~

非零 $c$ 没有统一正下界，故不提供统一稳定性、样本预算或可实现探测器。$P$ 的噪声、基线与响应的校准误差、重复取样独立性及单轨迹的代表性均另需精度与取得合同。

### Q5：有限均值、初始危险率与完整等待律（供文五、六节）

**更正命题 Q5。** 均值公式须假设相关状态条件等待量的第一矩有限，以排除无定义的无穷减无穷。核的“可加读取”是对每个可测事件 $B$ 都有 $s\mapsto K_s(B)\in\mathcal B$；仅速率参数属于 $\mathcal B$ 不足以推出整个核族的四角差为零。

在供文正速率指数例中，每个试验的潜在状态在等待期间保持不变。混合生存函数与危险率为

~~~math
S_p(t)=\sum_s p_s e^{-r_st},
\qquad
h_p(t)=-\frac{S'_p(t)}{S_p(t)}
=\frac{\sum_s p_s r_s e^{-r_st}}{\sum_s p_s e^{-r_st}}.
~~~

因此 $\sum_s p_sr_s=h_p(0)$ 只是初始危险率；后续危险率使用存活条件下的状态权重。指数律的混合一般不是平均速率的指数律；状态在期间切换时还需另一动力学核。供文的生存响应分解在 $b,c,t>0$ 时为正，区分初始危险率与等待律，不证明平均等待时间也盲。事实上该例的均值四角差为

~~~math
\operatorname{Curv}_m
=\frac1a-\frac1{a+b}-\frac1{a+c}+\frac1{a+b+c}
=\frac{bc(2a+b+c)}{a(a+b)(a+c)(a+b+c)}>0.
~~~

**均值盲而完整律不盲的条件例。** 若 $K_{s_0}=\frac12\delta_0+\frac12\delta_2$，其他四个核均为 $\delta_1$，所有条件均值为一而 $\operatorname{Curv}_K=\frac12\delta_0+\frac12\delta_2-\delta_1\ne0$。这说明一般的均值投影确可丢失读出律信息，但不是供文指数例证明的事。

供文包含号图只比较指定读出映射能取得的信息；不同抽象量之间没有未经合同限定的普遍严格层级。完整危险率函数也不同于一个初始危险率值。持续量 $t$、速率式中的系数 $d$ 和 seam 行向量 $d$ 分属不同对象，不能凭符号相同作物理时间解释。

### Q6：共同历史、停止与条件化（供文四、七节）

**适用命题 Q6。** $\Gamma_s^{(n)}$ 应为一个共同初态过程的投影相容边缘，具有固定可测输出空间、事件计数、等待和停止约定，且与 $P$ 共用初始律。不能为每个长度独立选核而仍声称属于同一历史。$K_s\in\operatorname{Prob}(\mathbb R_{\ge0})$ 已假设下一事件几乎必然在有限等待后发生；停止、永不返回或无限等待须增加终止标记、墓地状态或 $+\infty$，并在各长度中一致编码。使用次概率语义时应声明遗漏的质量。

对完成、存活或输出事件后选择不是原始混合读出。若状态 $s$ 的选择概率为 $u_s$，选择后的状态权重一般为 $p_su_s/\sum_t p_tu_t$，而非原 $p_s$；分母须严格正。该条件化可改变关于 $\kappa$ 的仿射公式。

### Q7：有界前缀与全部有限前缀（供文七节的无限历史保留句）

**更正命题 Q7。** 若已存在同一无限序列空间 $(\mathbb R_{\ge0}\times\mathcal O)^{\mathbb N}$ 上、采用柱集生成乘积 $\sigma$-代数的概率律，且各 $\Gamma_s^{(n)}$ 是其相容有限维边缘，则两个混合律的每个有限前缀律相同，已经推出整个无限律相同。有限前缀柱集是生成该 $\sigma$-代数的 $\pi$-系统，概率测度唯一性给出结论。若只有边缘族，标准 Borel 坐标与投影相容性提供通常的无限过程扩张框架；停止须按 Q6 编码。

在这个合同下，若所有正整数 $n$ 的 $\operatorname{Curv}_\Gamma^{(n)}=0$，同一可行纤维上任意两个混合无限历史律相同。因此供文“这不等于已经证明无限历史也一定看不见”的保留句仅适用于尚未给出相容性、存在性或观察事件空间合同的情形；不能解释为合同齐全后仍可在乘积 $\sigma$-代数中分离。额外非乘积可测的尾部读口是另一合同。

**反例 Q7。** 固定有限截止 $H$，两条确定序列可前 $H$ 项均为零，第 $H+1$ 项分别为零与一。它们的前 $H$ 项律相同而较长律不同。这说明一个有界前缀不足，不是全部有限前缀不足；把任意延迟计数实现为动力学时，须承担相应状态记忆，不自动获得固定五态表示。

### Q8：最小响应长度的定义域（供文七、八、十二节）

**适用命题 Q8。** 历史长度取 $n\in\mathbb N_{\ge1}$，在检测集合非空时取供文的最小值，空集时明确约定 $\ell_\ast=\infty$。该量描述所选核族与事件空间对形式方向的最早响应，不是一次记录的无误恢复时间，也不是物理流逝时间。

识别非退化纤维时使用 Q1；单点纤维的目标参数已知，可把目标恢复深度记为零，不能将它与形式方向的 $\ell_\ast$ 混同。在 Q6 的相容过程上，一个较短前缀的区别可由后续前缀投影保留；任意独立指定的历史核族不提供此性质。

### Q9：输出分辨仪器的线性与合法性合同（供文八、十二节）

**适用命题 Q9。** 采用同一已知、固定的有限状态 Markov／线性仪器：$p,d$ 是行向量，$g$ 是列测试，$M_{a,o}$ 非负并将测试向后拉回。每个启用动作的输出总核行和为一；漏失或终止质量须计入终止输出或明确的次随机合同。输出标签、状态载体、动作菜单和真正可用的测试集 $G$ 都固定。按时间先后

~~~math
M_\omega=M_{a_1,o_1}\cdots M_{a_n,o_n},
\qquad M_\varnothing=I.
~~~

$pM_\omega g$ 对事件指示函数或实际可实施的 $0\le g\le1$ 测试才是记录与测试通过的联合概率；对任意实 $g$ 是加权期望。例如空词与常函数 $g=2$ 给出数值二，不能叫概率。条件输出更新还须该输出质量严格正。

“所有合法未来”须量化同一合同中的词与末端测试。动作可用性、隐藏 guard、反馈和停止若改变可执行记录，就须编码到共同载体和联合核中。自适应策略每个观察节点选择同一个对该节点全部可能状态启用的动作，保留所有可能分支；隐藏状态各自选一个有利动作不构成观察者策略。

### Q10：等待、输出与后继的联合标记核（供文八节）

**适用命题 Q10。** $\widetilde M_{a,o}(B)_{ij}$ 是从状态 $i$ 出发的等待事件 $B$、输出 $o$ 与后继状态 $j$ 的联合质量，对 $B$ 可数可加、非负，并符合 Q9 的总行质量约定。等待边缘与后继状态边缘各自给出，不自动指定其联合分布。

对于 $n$ 次等待的矩形事件 $B_1\times\cdots\times B_n$，其联合记录概率为

~~~math
p\,\widetilde M_{a_1,o_1}(B_1)\cdots
\widetilde M_{a_n,o_n}(B_n)\,\mathbf1.
~~~

一般历史事件须用该仪器诱导的路径测度与迭代积分；若只读总等待量，则须声明总量映射并取联合律的推前。供文 $\widetilde M_\omega(B)$ 只有在补充此含义后才能代表一般多步事件，单个 $B\subseteq\mathbb R_{\ge0}$ 不能无定义地代表全部等待向量事件。

**反例 Q10。** 等待标记和后继二值标签均各有均匀边缘时，二者恒相等与二者独立的联合合同，事件“等待为零且后继为零”的概率分别为 $1/2$ 和 $1/4$。仅边缘不能确定所需联合核。

### Q11：固定维度的闭包稳定化（供文七、八节）

**适用命题 Q11。** 对实际完整的固定 $D$ 维表示、固定完整算子族及固定末端空间 $V_0$，令 $r=\dim V_0\ge1$，按供文递推定义 $V_n$。若 $V_{n+1}=V_n$，每个生成算子均将 $V_n$ 送回自身，故后续不再增长；未稳定时维数至少增加一。因此

~~~math
V_{D-r}=V_\infty.
~~~

在同一五态仪器上，record-only 的 $V_0=\operatorname{span}\{\mathbf1\}$ 给出存在响应时长度至多四的见证；若允许完整 $\mathcal B=\operatorname{span}\{1,x,y,z\}$ 作末端空间，其维数为四，则要么 $\mathcal B$ 对所有子核不变，要么一步补足全五维，新增 seam 可见性至多需要一步。这里引用供文所引 60ebb51 仪器卷的 Q4 与“有限状态 horizon 上界”，不把此成熟有限维结论认作新一般定理。

隐藏深度、phase、历史计数、守卫、时变或未知核可扩大实际载体，或使此表示不适用。无限标记算子族虽仍可落在有限维空间中，只有证明已检查算子张成完整所需族，有限抽查才认证完整闭包。4da8b2e 的 Corollary 5.2 对任意截止增长 $N$；它不反驳一个固定五维完整仪器的稳定化上界。

### Q12：保留、不可见与载体内消除（供文九节）

**更正命题 Q12。** $\mathcal R(dT)=0$ 要求 $\mathcal R$ 是线性律读出，并已延拓到符号差分；非线性读出应直接比较所有相关可行参数的 $\mathcal R(p_\kappa T)$，不能无定义地对 $dT$ 应用它。$dT=0$ 只消除所选后继状态载体内的初态差异，不证明环境、已发射输出或扩大系统中没有区别。

供文九节第 1 项与第 3 项都写 $dT\ne0$、$\mathcal R(dT)=0$，它们是同一保留但未观测条件的重复解释，全文保留，不构成三个互斥分支。线性读出的互斥分类是：$dT=0$；$dT\ne0$ 且 $\mathcal R(dT)=0$；以及 $\mathcal R(dT)\ne0$。

**反例 Q12。** 令 $h=xy$，两个输出子核为

~~~math
M_1(i,j)=h(i)\mathbf1_{\{j=s_0\}},
\qquad
M_0(i,j)=(1-h(i))\mathbf1_{\{j=s_0\}}.
~~~

它们非负，总核 $T=M_0+M_1$ 的每行均为重置到 $s_0$ 的概率行，故 $dT=0$，最终状态相同；但 $dM_1\mathbf1=d\cdot h=1$，输出一的概率仍为 $\kappa$。平均核可消除方向而逐输出记录保留方向；末态重置不删除已经取得的输出。

### Q13：不可访问射线不等于全部可访问读口盲（供文十节及最终结论）

**更正命题 Q13。** 只把 ray 分支排除出可访问记录，不推出每个其余可访问 $\omega,g$ 都满足 $dM_\omega g=0$。残余物、反冲、相关发射、吸收体或后续响应仍可携带区别；Q12 的输出可作为一个保留区别的可访问记录。全域局部盲性须证明 $d$ 湮灭整个声明的可访问输出／测试闭包。

反向也不成立：所有指定响应为零可以来自读口本来盲或响应抵消，不证明射线确已离开因果域。例如恒等转移与只允许常数测试不读取任何初态区别，完全不需要射线离域。

吸收、反射、碰撞或热化本身既不提供一个非零校准响应，也不证明方向消除。恢复只能针对某个已明确目标及实际可访问、已校准的联合响应律断言；所需状态特异探测器仍为 open 的实现义务。

### Q14：非空 belief 上的确定安全博弈（供文十一节）

**适用命题 Q14。** 采用有限状态 $\Omega$、有限动作与观察模型、声明的初始非空 belief $B_0\subseteq K$，以及精确观察更新。状态、动作、观察三者的有限性分别声明；仅动作与观察有限不保证 belief 枚举有限。每个 belief 的可选动作须在其全部状态共同启用。供文的 $\delta(s,a)$ 是确定转移；取总转移语义，或明确将死锁作为失败，将已声明安全终止编码为安全吸收态。

定义安全非空 belief 空间 $\mathfrak B=\{B:\varnothing\ne B\subseteq K\}$，算子在集合族 $S\subseteq\mathfrak B$ 上取

~~~math
\mathcal F(S)=
\left\{B\in\mathfrak B:
\exists a\in\bigcap_{s\in B}\operatorname{Enabled}(s),\quad
\delta_a(B)\subseteq K,\quad
\forall y,\ B_{a,y}\ne\varnothing\Rightarrow B_{a,y}\in S
\right\}.
~~~

策略取依赖已取得观察历史的确定策略。一个共同控制动作之后，要对全部可实现的非空观察后继成立，不能每个隐藏状态另选动作；对手的状态与输出选择须符合该合同。若 $S\subseteq S'$，同一个动作见证仍成立，故 $\mathcal F$ 单调。最大不动点刻画从 $B_0$ 中每个可能真态、每条可实现观察分支都保持安全的 sure safety。在有限 $\mathfrak B$ 中从全空间迭代删除失败 belief 可有限稳定；胜出选择器无记忆于 belief，未必无记忆于原始观察。

非确定或随机转移扩展须用全部允许后继支持更新，不沿用单一 $\delta$ 冒充一般合同。随机策略、almost-sure 而非 sure 目标、扰动与终止约定均需另定。无限载体不继承有限迭代、有限表示或有界记忆结论。这个集合安全结论没有证明物理无限时长、非 Zeno、能量、排热、资源、校准或生理功能，也不认证生物学生命。

### Q15：模型术语与物理、量子解释（供文三、四、七、十至十二节及最终结论）

**适用命题 Q15。** 混合响应是代数差分，状态条件等待律是局部记录的统计模型，$\ell_\ast$ 是指定历史读口的响应深度。称它们为曲率、局部时钟、时间形状、生命式维护或逆衰变是供文的定义性提案与类比；这些公式不识别物理时空曲率、固有时、引力、相对论因果、材料衰变规律或实际探测器。

经典五态概率律与 Markov 仪器不是量子层析、量子相干恢复、量子 no-hiding 或通道可逆性证明。量子实现须给出状态、联合仪器、测量反作用、可访问环境和恢复目标。供文关于时间及 $3+1$ 的措辞保留为作者建模提案；未证明物理时间只等于信息响应，也未否定全局坐标描述。物理与生物解释仍为 open，缺少实现映射、动力学、时钟校准及经验判据。

### Q16：跨模型综合的共同实现与归属（供文一、八、十一、十二节及最终结论）

**适用命题 Q16。** 静态混合律、取得核预测器、Fibonacci 深度／计数未来商和 belief 安全模型各自有来源、先验、合法历史、操作、响应与目标合同。它们共享仿射符号响应机制或相似术语，不自动成为同一实际过程、概率律或可执行接口。组合结果前须提供共同来源、参数与标签对应、合法操作及联合后继／输出律，并保留各引用的条件；Q2、Q6、Q9 与 Q14 分别约束这些接口。

供文八节“实际上是同一个结构”可读为响应机制的应用性综合；它没有提供静态时钟到精确 Fibonacci 动态未来商的 native 延续桥或精确 Lean 应用。安全不变性只认证声明的安全目标，不自动要求或保存每个隐藏关系；哪些信息是控制所必需的，须相对该目标和仪器另判。

供文所引三个公开理论文件保留各自开放输入与适用边界；固定核反演与省略取得核反演不是同一问题。有限维观察与 belief 最大不动点是既有数学方法；这份来源特异综合可作为应用／提案保存，不能仅据类比、重述或链接宣称数学优先权、新一般证明、物理实现或生物认证。

## 追加锚（本行以下为增补区）

## 十三、校准的共同等待解析实际五模式可行纤维

### 定义17（五模式来源与可行纤维）

沿用本卷 Q1 及 [隐藏 seam 卷，第二节定理一、Q1](AURIC_FIB_ATOM_HIDDEN_SEAM_CAUSAL_READOUT_CLOSURE.md) 的归一化五模式载体：

~~~math
\Sigma=\{s_0,s_1,s_2,s_3,s_{13}\}
=\{F[\varnothing],F[1],F[2],F[3],F[1,3]\}.
~~~

令 $x,y,z$ 分别指示位置 $1,3,2$。给定已知实数 $X,Y,Z\ge0$，要求

~~~math
I_{X,Y,Z}=\bigl[\max(0,X+Y+Z-1),\ \min(X,Y)\bigr]\ne\varnothing.
~~~

在顺序 $(s_0,s_1,s_2,s_3,s_{13})$ 下，以这三项边缘为均值的全部概率律为

~~~math
p_\kappa=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\qquad \kappa\in I_{X,Y,Z}.
~~~

端点允许零质量；区间为单点时没有待识别的方向。上述条件保证每项非负且总和为一。既有纤维与四角泛函在这里的参数对应为

~~~math
p_\kappa-p_{\kappa'}=(\kappa-\kappa')d,
\qquad d=(1,-1,0,-1,1),\qquad J(f)=d\cdot f.
~~~

### 假设18（一个完整运行的校准相位探针合同）

取已校准的两种等待时长 $a,b>0$、实数 $\Omega _2$，置

~~~math
\Omega _1=\frac{2\pi}{a},\qquad \Omega _3=\frac{2\pi}{b},
\qquad
\omega(s)=\Omega _1x(s)+\Omega _2z(s)+\Omega _3y(s).
~~~

每次完整运行从固定的 $p_\kappa$ 抽取一个模式 $s$，在该次运行的全部等待阶段保持这个 $s$。探针为有固定校准基 $|0\rangle,|1\rangle$ 的量子比特，每次运行与来源无初始关联，并重新制备为

~~~math
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2}.
~~~

对每个 $t\ge0$，实际供应的条件相对相位操作及状态为

~~~math
V_s(t)=|0\rangle\langle0|+e^{-i\omega(s)t}|1\rangle\langle1|,
\qquad
|\psi_s(t)\rangle=V_s(t)|+\rangle
=\frac{|0\rangle+e^{-i\omega(s)t}|1\rangle}{\sqrt2}.
~~~

同一模式上的等待满足 $V_s(t_2)V_s(t_1)=V_s(t_1+t_2)$。这些操作由同一对角生成元产生并彼此交换；有序 FIB 树的其他非交换表示不由此实现。这里测量的是两基矢之间相对于校准参照的相位，整体相位不产生该读数。重复运行按同一来源律作独立同分布准备；一个未知模式永久固定于所有运行是另一统计实验。

使用标准矩阵

~~~math
X_{\rm P}=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Y_{\rm P}=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
Z_{\rm P}=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
~~~

允许的仪器是运行末端的二值测量，$\theta\in\mathbb R$ 为校准方向：

~~~math
M_\theta=\cos\theta\,X_{\rm P}+\sin\theta\,Y_{\rm P}
=\begin{pmatrix}0&e^{-i\theta}\\e^{i\theta}&0\end{pmatrix},
\qquad E_{\theta,\pm}=\frac{I\pm M_\theta}{2}.
~~~

输出标记为 $\pm1$。分别准备的 $\theta=0,\pi/2$ 试验用于取得两项期望；一次输出不直接给出精确复数。中途测量、反馈、重置、动态切换及任意中间仪器均须另供合同。本卷 Q2、Q9–Q10 及 [输出仪器卷 Q2–Q4、Q13](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md) 在此分别约束共同来源、菜单和概率取得。下文的重抽及环境重置仅是显式声明的比较协议。

### 定理19（实际终端密度矩阵及其纤维响应）

在假设18下，对每个 $t\ge0$，平均探针态及复读数为

~~~math
\varrho_\kappa(t)=\sum_s p_\kappa(s)|\psi_s(t)\rangle\langle\psi_s(t)|
=\frac12\begin{pmatrix}1&\overline{C_\kappa(t)}\\C_\kappa(t)&1\end{pmatrix},
\qquad C_\kappa(t)=\sum_s p_\kappa(s)e^{-i\omega(s)t}=B(t)+\kappa J(t),
~~~

其中

~~~math
B(t)=1-X-Y-Z+X e^{-i\Omega _1t}+Z e^{-i\Omega _2t}+Y e^{-i\Omega _3t},
\qquad
J(t)=\bigl(1-e^{-i\Omega _1t}\bigr)\bigl(1-e^{-i\Omega _3t}\bigr).
~~~

$B(t)$ 为本卷 Q3 意义的代数基线，$\kappa=0$ 可以不可行。实际输出律为

~~~math
\mathbb E[M_\theta]=\operatorname{Tr}(\varrho_\kappa M_\theta)
=\operatorname{Re}\!\bigl(e^{-i\theta}C_\kappa(t)\bigr),
\qquad
\Pr(\pm\mid\theta,t)=\frac{1\pm\operatorname{Re}(e^{-i\theta}C_\kappa(t))}{2}.
~~~

**证明。** 条件纯态的外积是 $\frac12\left(\begin{smallmatrix}1&e^{i\omega(s)t}\\e^{-i\omega(s)t}&1\end{smallmatrix}\right)$；按概率平均给出所示密度矩阵，且 $|C_\kappa|\le1$。五个相位依次是 $1,e^{-i\Omega _1t},e^{-i\Omega _2t},e^{-i\Omega _3t},e^{-i(\Omega _1+\Omega _3)t}$。代入定义17，$\kappa$ 的系数为 $1-e^{-i\Omega _1t}-e^{-i\Omega _3t}+e^{-i(\Omega _1+\Omega _3)t}$，即既有四角泛函在这个实际条件响应上的因子式。最后直接乘矩阵取迹，两个对角项之和是 $\operatorname{Re}(e^{-i\theta}C_\kappa)$；$M_\theta^2=I$ 给出相应二值概率。若改从 $|0\rangle$ 开始，操作保持 $|0\rangle$，所有这些赤道期望为零，故上述制备是必要的实验前提。证毕。

### 定理20（单时钟整纤维盲性与共同混合等待的分离）

对所有 $m,n\in\mathbb Z_{\ge0}$，

~~~math
J(ma)=J(nb)=0.
~~~

所以单独 $a$-时钟或 $b$-时钟在所有非负整数刻度的终端密度矩阵和所供二值律均与 $\kappa$ 无关。该密度矩阵相等也使任何另行供应的同一终端 POVM 律相等，但不确定任意多时刻仪器记录。

对 $t\ge0$，$J(t)\ne0$ 当且仅当 $t/a,t/b$ 都不是整数。特别地，

~~~math
J(a+b)=\bigl(1-e^{-2\pi i b/a}\bigr)\bigl(1-e^{-2\pi i a/b}\bigr)\ne0
\quad\Longleftrightarrow\quad b/a\notin\mathbb Z\ \text{且}\ a/b\notin\mathbb Z.
~~~

若 $b/a=p/q$ 为既约正整数比，则条件等价于 $p,q>1$，例如 $3/2$ 已足够；无理比不是此处必要条件。对一般 $t=ma+nb$，判据为 $nb/a,ma/b$ 都不是整数。若 $p=1$ 或 $q=1$，每个这种混合等待仍盲。对含至少两个点的可行区间，在任一 $J(t)\ne0$ 处，每对 $\kappa\ne\kappa'$ 都满足

~~~math
C_\kappa(t)-C_{\kappa'}(t)=(\kappa-\kappa')J(t)\ne0.
~~~

**证明。** 第一时钟的因子在 $ma$ 为零，第二时钟的因子在 $nb$ 为零；其余判据来自 $e^{-2\pi i u}=1\iff u\in\mathbb Z$。定理19把这些等式落实为实际密度矩阵及概率律的等式；非零响应则至少被一个所供赤道方向检测。

为解释这条纤维为何不能靠增加同种刻度解除盲性，在本证明中消费既有单时钟所有者 [事件采样卷定理11.1](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) 和 [有限 Vandermonde 所有者](../../../D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography.lean) 的 finite_moment_readout_injective、finite_moments_eq_iff。取任一固定步长 $h>0$（本应用取 $a$ 或 $b$），将实际频率测度 $\mu_\kappa=\sum_s p_\kappa(s)\delta_{\omega(s)}$ 中相同节点 $z=e^{-i\omega h}$ 合并，删去零质量，得到 $q$ 个不同节点及正质量 $P_j$。两份有限测度的全部单时钟响应相等，恰等于每个相位类的总质量相等：在两者节点的并集上，最初若干矩给出上述所有者的单射映射。这里的别名关系是 $(\omega-\omega')h\in2\pi\mathbb Z$，并非模式标签相等。

同一正质量分解给出本实际来源的记录矩阵

~~~math
G^{(h)}_\ell=\bigl[C_\kappa((n-m)h)\bigr]_{m,n=0}^{\ell},\qquad
G_{mn}=\sum_{j=1}^q P_j\overline{z_j^m}z_j^n,
\qquad G^{(h)}_\ell\succeq0,\quad
\operatorname{rank}G^{(h)}_\ell=\min(\ell+1,q).
~~~

这是特征列 $(\sqrt{P_j}z_j^n)_j$ 的 Gram 矩阵；秩等式直接消费同一所有者的 vandermonde_det_ne_zero_of_injective，正质量不改变特征矩阵的秩。负参数项仅由 $C(-t)=\overline{C(t)}$ 填入，实际等待仍为非负。故无限多同刻度记录和有限 Gram 秩都只描述采样相位类，不能超出定理的盲性边界。

此机制不应转给前述实衰减模型：若另有 $M(t)=\sum_{j=1}^q w_j e^{-\lambda_jt}$，$w_j>0$、互异 $\lambda_j>0$，则 $x_j=e^{-\lambda_jh}$ 互异。对 $R,C\ge1$，从零开始的矩形 Hankel 块为

~~~math
H_{mn}=M((m+n)h),\quad 0\le m<R,\ 0\le n<C,
\qquad \operatorname{rank}H=\min(R,C,q).
~~~

应用同一 Vandermonde 所有者于实节点，分解 $H=V_R\operatorname{diag}(w)V_C^T$ 给秩上界；令 $d=\min(R,C,q)$，左上 $d\times d$ 块是正权 Gram 矩阵，$V_d$ 行满秩给下界。全秩 $q$ 需要两边尺寸都至少 $q$。实指数单射排除周期性精确别名，不能排除有限精度病态。

经典采样边界的文献定位为 [Yue、Thunberg、Goncalves，arXiv:1605.06973v1，§II.A 定理1、定义5及§III.A](../../../Library/Dynamics/yue2016systemaliasing.md)。其主对数使用严格开条带 $-\pi<\operatorname{Im}z<\pi$；对采样矩阵 $e^{hA}$ 使用时，生成元的对应条件是 $-\pi<h\operatorname{Im}\lambda(A)<\pi$。本文不导入端点唯一性，也不由该引用取得本五模式实验的实现。证毕。

### 定理21（一个实际混合终端读数的整纤维逆式与目标边界）

在假设18下，已知 $X,Y,Z$ 且校准的 $t\ge0$ 满足 $J(t)\ne0$ 时，

~~~math
\kappa=\frac{\operatorname{Re}\!\left(\overline{J(t)}[C_\kappa(t)-B(t)]\right)}{|J(t)|^2}
=\frac{\mathbb E[M_{\arg J(t)}]-\operatorname{Re}(e^{-i\arg J(t)}B(t))}{|J(t)|}.
~~~

这是整个闭可行区间上的逆式，随后定义17逐项恢复全部五个质量。任取可行 $\kappa_0$，也可用 $C_\kappa-C_{\kappa_0}=(\kappa-\kappa_0)J$ 作为概率来源之间的比较。若复响应误差至多 $\varepsilon$，上述线性逆式的误差至多 $\varepsilon/|J(t)|$；若对齐二值的正输出概率误差至多 $\varepsilon$，则相应误差至多 $2\varepsilon/|J(t)|$。这里固定精确占据及校准，有限样本如何达到给定概率误差另需取得合同。

**证明。** 在定理19的 $C_\kappa-B=\kappa J$ 两边乘 $\overline J$ 取实部，或直接令 $\theta=\arg J$，即得斜率 $|J|$。复误差的实投影不超过其模；概率与期望相差因子二。这是本卷第五节定理二及 Q1–Q4 的既有纤维逆式在假设18所供事件上的具体应用。

准确描述这一恢复的范围，可对任一实际实验族定义 $\mu\sim_{\mathscr E}\nu$ 为每个 $e\in\mathscr E$ 的结果律均相等。若 $\mathscr E\subseteq\mathscr E'$，增加等式条件给出 $\sim_{\mathscr E'}\subseteq\sim_{\mathscr E}$。定理20的两个单时钟终端族之并把整条纤维合为一类；加入一个同源混合等待及其对齐测量，逆式使本纤维上的类成为单点。这一新增操作不是旧边缘律的后处理；合法菜单及实际可行增量的所有者为 [输出仪器卷 Q1–Q4、Q7–Q8](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)。单点纤维则无需任何新增读数。

本逆式也不是未知频谱恢复。为限定两者的关系，在此消费 [Kunis 等，arXiv:1506.00450v1，§2、定理3.1](../../../Library/Fourier/kunis2015multivariateprony.md) 的有限节点插值方法：若另把来源类改为至多 $r\ge1$ 个未知实频率，仍供应同源等待及假设18的探针，并要求 $b/a\notin\mathbb Q$，则相位对 $\omega\mapsto(z,w)=(e^{-i\omega a},e^{-i\omega b})$ 单射。因为相同相位对给 $(\omega-\omega')a=2\pi k$、$(\omega-\omega')b=2\pi l$，非零差会使 $b/a=l/k$。相反，对约分有理比 $p/q$，频率差 $2\pi q/a$ 给完全相同的相位对，所以无界实频率上全局单射需要无理比；这比定理20的已知模式纤维目标更强。

这里所需的三角形取样界由如下普通分离步骤给出，不冒称是该文矩形取样定理的逐字结论。两份至多 $r$ 点测度的相位对并集有 $q\le2r$ 个不同点 $\zeta_j=(z_j,w_j)$。对每个 $k\ne j$ 选一个能区分两点的坐标函数 $u_{jk}\in\{z,w\}$，置

~~~math
P_j(z,w)=\prod_{k\ne j}
\frac{u_{jk}(z,w)-u_{jk}(\zeta_k)}{u_{jk}(\zeta_j)-u_{jk}(\zeta_k)}.
~~~

分母非零，$P_j(\zeta_k)=\delta_{jk}$，总次数 $q-1\le2r-1$。故若两测度的同源混合矩

~~~math
c_{mn}=C(ma+nb)=\sum_j p_j z_j^m w_j^n,
\qquad m,n\in\mathbb Z_{\ge0},\quad m+n\le2r-1
~~~

相同，则积分每个 $P_j$ 得各点质量相同，再由相位对单射得频率测度相同。取样数量为 $\sum_{d=0}^{2r-1}(d+1)=r(2r+1)$，含已知的 $c_{00}=1$，只为充分数量，不声称最少。没有预给 $r$ 时，全部混合矩也通过任意两份有限测度的有限并集给唯一性。

这段插值用于界定本纤维应用的外推范围：它仅是另一个目标的精确唯一性，不能替代这里的一次对齐期望，也不提供无界频率的统一有限精度反演。该文定义3.6、定理3.7另有节点分离和系数比条件；多原子支撑合并、权重趋零及校准误差仍需额外限制。即使完整频率测度可知，若 $\Omega _2$ 与其他模式频率相撞，频率测度也不分辨相撞的模式标签；本定理依靠另已知的 $X,Y,Z$ 仍可由非零 $J$ 恢复 $p_\kappa$。

最后，正单位变换 $t'=ct,\ a'=ca,\ b'=cb,\ \omega'=\omega/c$（$c>0$）保持每个相位和时长比，属于 [事件采样卷定理11.5](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) 的已知单位运输在此处的应用。它不供应漂移、时钟噪声、空间运输或相位控制模型，也不把局部校准提升为绝对物理时间。证毕。

### 定理22（同源接续、独立重抽与历史闭包的边界）

在假设18的实验中，同一模式贯穿两次等待给 $C_\kappa(a+b)$。作为比较协议，若第一等待后保持同一探针，但第二等待的模式按同一 $p_\kappa$ 独立重抽，则终端相干为 $C_\kappa(a)C_\kappa(b)$，在本纤维上不含 $\kappa$。若来源重抽时还将探针重新制备为 $|+\rangle$，最后仅得到 $C_\kappa(b)$；分别在两次完整运行末端读出才构成两次独立的单时钟实验。它们均不代替定理21所用的保留来源、保留探针的接续。

**证明。** 保留模式 $s$ 时，实际终态为

~~~math
V_s(b)V_s(a)|+\rangle
=\frac{|0\rangle+e^{-i\omega(s)(a+b)}|1\rangle}{\sqrt2}.
~~~

按 $p_\kappa(s)$ 平均后得到 $\varrho(C_\kappa(a+b))$，其中 $\varrho(C)=\frac12\left(\begin{smallmatrix}1&\overline C\\C&1\end{smallmatrix}\right)$。独立重抽时，实际终态条件于 $(s,s')$ 的下分量是 $e^{-i\omega(s)a}e^{-i\omega(s')b}/\sqrt2$，联合权重是 $p_\kappa(s)p_\kappa(s')$，所以

~~~math
\sum_{s,s'}p_\kappa(s)p_\kappa(s')e^{-i\omega(s)a}e^{-i\omega(s')b}
=C_\kappa(a)C_\kappa(b).
~~~

等价地，对保留的已平均探针施加第二次随机相位通道，将其下非对角元乘 $C_\kappa(b)$。定理20给 $J(a)=J(b)=0$，故乘积不含 $\kappa$；探针制备映射则直接删除第一段相干，仅留下第二段。这证明两种实际终端律不同的来源，并落实本卷 Q2、Q6、Q9–Q10 的同源与历史合同。

要解释本结论为何不等于整个观察空间的闭包，可在此消费既有 [AnalyticFlowGeneration](../../../D5/S3/Quantum/Dynamics/AnalyticFlowGeneration.lean) 的 analytic_flow_generates_commutator_closure（复观察空间），连同其中已有的 flow_span_eq_power_orbit、hasDerivAt_heisenbergFlow。它们与这里的实 Hermitian 表述有如下明确桥梁：另供有限维 Hermitian 生成元 $\Omega$ 和含 $I$ 的实 Hermitian 子空间 $\mathcal V$，令 $\mathcal A_t(F)=e^{i\Omega t}Fe^{-i\Omega t}$。复化 $\mathcal V_{\mathbb C}=\mathcal V+i\mathcal V$ 满足 $\mathcal V_{\mathbb C}\cap\mathrm{Herm}=\mathcal V$，因为 $A+iB$（$A,B\in\mathcal V$）为 Hermitian 迫使 $B=0$。因此该既有复流结论不能直接省略实载体的条件。

对上述另供空间，$b/a$ 无理时的适用判据为

~~~math
\bigl[\mathcal A_a\mathcal V\subseteq\mathcal V\ \text{且}\ \mathcal A_b\mathcal V\subseteq\mathcal V\bigr]
\quad\Longleftrightarrow\quad
\bigl[\mathcal A_t\mathcal V\subseteq\mathcal V\ (t\in\mathbb R)\bigr]
\quad\Longleftrightarrow\quad
\bigl[i[\Omega,F]\in\mathcal V\ (F\in\mathcal V)\bigr].
~~~

在本证明中使用的稠密子群步骤为：有限维单射使两次包含成为等号，从而其数学逆及所有整数复合 $ma+nb$ 保持 $\mathcal V$。鸽巢原理作用于 $jb/a$ 的小数部分给任意小的非零整数线性组合；取其整数倍逼近任意实数，故该群稠密。连续共轭与有限维子空间的闭性将不变性延至所有 $t$；在零点求导给 $i[\Omega,F]$。反向用保 $\mathcal V$ 的实线性算子 $L(F)=i[\Omega,F]$ 及 $e^{tL}=\mathcal A_t$。同类稠密性已有 [SparseWindowMutualDetermination 的 natural_phase_visit](../../../D5/S1/Digit/Infinite/SparseWindowMutualDetermination.lean)，其调用 AddCircle.denseRange_zsmul_coe_iff；这里的两时判据只作为所需量词的中间说明。数学逆不供应倒放仪器，且它量化整个 $\mathcal V$，比本定理两来源终端律的比较更强。

这个区别在 $\Omega=\pi Z_{\rm P}/a$、$\mathcal V=\operatorname{span}_{\mathbb R}\{I,X_{\rm P}\}$ 处可直接看出：整数 $a$ 刻度的酉为标量，但 $\mathcal A_{a/4}(X_{\rm P})=-Y_{\rm P}\notin\mathcal V$。这套另外供应的观察空间不是从五模式实验推得的共同历史。

同样，为限定“局部消失后返回”的量子读法，消费 [二阶关系卷命题110.4、假设111.1与定理111.2、命题115.2](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md) 的保留环境与新环境区分。其连续参数示例采用 [Ziman 等，Quantum homogenization，arXiv:quant-ph/0110164v1，§II 式(2.1)–(2.7)](../../../Library/QuantumChannels/ziman2001quantumhomogenization.md) 的标准部分交换：另给系统比特 $S$、环境比特 $E$、$g>0$、初态 $\rho\otimes I/2$，令

~~~math
U_t=\cos(gt)I-i\sin(gt)\mathsf S,\qquad \mathsf S^2=I.
~~~

该文约定 $P(\eta)=\cos\eta I+i\sin\eta\mathsf S$，此处 $\eta=-gt$；原文每个 reservoir 粒子至多交互一次，给的是新环境标准模型，不能把其递推当作保留同一个 $E$ 的返回证明。这里直接展开同一个联合态：令 $c=\cos(gt),s=\sin(gt)$，则

~~~math
U_t(\rho\otimes I/2)U_t^\dagger
=c^2(\rho\otimes I/2)+s^2(I/2\otimes\rho)
+ics\bigl[(\rho\otimes I/2)\mathsf S-\mathsf S(\rho\otimes I/2)\bigr].
~~~

交叉项的环境偏迹为 $ics[\rho,I/2]=0$，故

~~~math
\Phi_t(\rho)=\operatorname{Tr}_E[U_t(\rho\otimes I/2)U_t^\dagger]
=c^2\rho+s^2 I/2,\qquad \mathbf r(t)=c^2\mathbf r(0).
~~~

每个时刻三方向等缩放，且对任意系统酉 $W$ 有 $\Phi_t(W\rho W^\dagger)=W\Phi_t(\rho)W^\dagger$。令本量子示例的刻度为 $h_Q=\pi/g$，在 $n h_Q$（$n\ge0$ 为整数）有 $U_{n h_Q}=(-1)^nI$。半刻度 $U_{h_Q/2}=-i\mathsf S$，给出的实际两段历史为

~~~math
\rho\otimes I/2
\ \longmapsto\ I/2\otimes\rho
\ \xrightarrow{\text{同一 }E}\ \rho\otimes I/2,
~~~

而在半刻度另行丢弃 $E$ 并放入新 $I/2$ 后，联合态变为 $I/2\otimes I/2$，第二次交换仍是它。对 $\rho=|0\rangle\langle0|$，末端 $Z_{\rm P}$ 的正输出概率分别为 $1$ 和 $1/2$。各向同性与粗刻度返回因而没有确定中间的局部信息或替换环境后的历史。

这个联合态计算只消费已有模型来限定本五模式结论的外推；它不是该五模式的量子实现，也没有增加假设18的干预菜单。[Pollock 等，arXiv:1801.09811v1，第2页过程张量及第3页定义、定理与引理](../../../Library/QuantumChannels/pollock2018operationalmarkov.md) 要求以明确控制序列及因果断裂讨论过程记忆。若另供半刻度系统替换 $\mathcal R_\sigma(A)=\operatorname{Tr}(A)\sigma$，则两初始准备 $\rho,\rho'$ 在该时刻分别变为 $\sigma\otimes\rho,\sigma\otimes\rho'$，末次交换给不同系统态 $\rho,\rho'$；这才是相同系统再准备后的记忆见证，且使用了额外控制。本应用仅以已写出的保留/重置对照说明限制，不从 $\Phi_t$ 或 $C_\kappa(t)$ 单独推断完整过程张量。证毕。

### 定义23（原树上的辅助黄金时长选择）

采用 [FIBONACCI_ATOMIC_RELATION_GENERATION，定义2.1、3.1、3.3及定理2.2、3.4](FIBONACCI_ATOMIC_RELATION_GENERATION.md) 的有序原树、替换 $\rho$ 与组成列向量 $c(u)=(c_\alpha(u),c_\beta(u))^T$：$\rho(\alpha)=\beta$、$\rho(\beta)=\langle\beta,\alpha\rangle$。对 $\Delta>0$，另赋辅助时长

~~~math
\varphi=\frac{1+\sqrt5}{2},\qquad
 d(u)=\Delta\,[c_\alpha(u)+\varphi c_\beta(u)].
~~~

由此 $d(\alpha)=\Delta$、$d(\beta)=\varphi\Delta$、$d(\langle u,v\rangle)=d(u)+d(v)$。其在假设18中的用途仅是选择 $a=\Delta,b=\varphi\Delta$。这份加法解释忘掉树的次序和括号，不改原数量映射，也不认证原生时钟、物理黄金时长或其他非交换表示。

### 定理24（黄金等待的实际边界辨别值与校准限制）

在假设18及定义23下，取边界来源

~~~math
p_+=\tfrac12\delta_{s_0}+\tfrac12\delta_{s_{13}},\qquad
p_-=\tfrac12\delta_{s_1}+\tfrac12\delta_{s_3}.
~~~

它们同属 $(X,Y,Z)=(1/2,1/2,0)$ 的纤维，$\kappa_+=1/2,\kappa_-=0$。在有序树 $\rho(\beta)$ 所赋的共同等待 $t=a+b=\varphi^2\Delta$ 处，令 $z=e^{-2\pi i\varphi}$，有

~~~math
\delta C=C_+(t)-C_-(t)=\frac12(1-z)^2,\qquad
D_{\rm tr}(\varrho_+(t),\varrho_-(t))=\sin^2(\pi\varphi).
~~~

所供菜单中的 $M_{\arg\delta C}$ 已达到等先验二值分类成功率

~~~math
P_{\rm succ}=\frac{1+D_{\rm tr}}2.
~~~

模型值分别约为 $0.8686844390$ 和 $0.9343422195$。它们描述两种规定来源的单次概率分类；定理21对整条连续纤维的恢复仍以精确律或所声明的概率误差为输入。黄金时长在此供应一个非零响应的选择，不供应未知频谱的统一有限精度恢复。

**证明。** 原树组成传输 $c(\rho u)=Mc(u)$、$M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$ 的精确所有者是上述定理3.4，以及 [GeometryEntranceRatio 中已有的 private composition_transport](../../../D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.lean)。在这个应用中 $(1,\varphi)M=\varphi(1,\varphi)$，故 $d(\rho u)=\varphi d(u)$，尤其 $d(\rho\beta)=(1+\varphi)\Delta=\varphi^2\Delta$。这只应用既有组成传输，不另立时长递推定理。

由 $\varphi^{-1}=\varphi-1$，$t/a=1+\varphi$、$t/b=1+\varphi^{-1}=\varphi$ 的两个相位均为 $z$，定理19给 $\delta C=(1-z)^2/2$。平均探针态一般是混合态；直接计算它们之差

~~~math
D=\varrho_+-\varrho_-
=\frac12\begin{pmatrix}0&\overline{\delta C}\\\delta C&0\end{pmatrix},
\qquad \operatorname{spec}(D)=\{+|\delta C|/2,-|\delta C|/2\}.
~~~

因此 $D_{\rm tr}=\tfrac12\|D\|_1=|\delta C|/2=|1-z|^2/4=\sin^2(\pi\varphi)$。设 $\theta=\arg\delta C$，则 $D=(|\delta C|/2)M_\theta$；允许的 $E_{\theta,+}$ 正是正特征空间投影。以正输出判 $p_+$，其等先验成功率为

~~~math
\tfrac12\operatorname{Tr}(E_{\theta,+}\varrho_+)
+\tfrac12\operatorname{Tr}((I-E_{\theta,+})\varrho_-)
=\tfrac12+\tfrac12\operatorname{Tr}(E_{\theta,+}D)
=\tfrac12+\tfrac14|\delta C|.
~~~

任意二值效应 $0\le E\le I$ 在 $D$ 的两个特征方向上的对角元均在 $[0,1]$，故 $\operatorname{Tr}(ED)\le|\delta C|/2$；上述菜单已达到上界，不借用未供应的测量。

为限定这一黄金参数选择的校准含义，先按 [事件采样卷定理11.1](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) 复用整数刻度别名：若 $\omega'-\omega=2\pi k/\Delta$，$k\in\mathbb Z$，则对任意非负整数序列 $n_j$ 有 $e^{-i\omega'n_j\Delta}=e^{-i\omega n_j\Delta}$，取 $n_j=F_j$ 仍成立。代数等式也适用于负整数，但本等待合同不使用它们。Fibonacci 采样索引并未提供第二种黄金时长。

取 $F_0=0,F_1=1$。精确残差直接采用 [FibonacciErrorRatio 的 fibonacci_golden_residual](../../../D5/S1/Scale/FibonacciErrorRatio.lean)：

~~~math
F_n\varphi-F_{n+1}=(-1)^{n+1}\varphi^{-n}\quad(n\ge0).
~~~

把它用在定理21所区分的未知频率目标，令 $\omega_n=2\pi F_n/\Delta$。与零频率相比，第一时钟完全别名；第二时钟的弦长和有界混合等待误差为

~~~math
\bigl|e^{-i\omega_n\varphi\Delta}-1\bigr|=2\bigl|\sin(\pi\varphi^{-n})\bigr|,
\qquad
\bigl|e^{-i\omega_n(m\Delta+k\varphi\Delta)}-1\bigr|
\le2\pi L\varphi^{-n},
\quad m,k,L\in\mathbb Z_{\ge0},\quad 0\le k\le L.
~~~

这是将残差代入相位后用 $|e^{iu}-1|\le|u|$ 得到的消费步骤。残差式在 $n=0$ 仍成立，此时 $\omega_0=0$ 不是不同来源；非零频率比较和以下有理比需要 $n\ge1$。频率从 $n\ge2$ 起严格增加；把 $\varphi^{-n}$ 称为最近整数距离也必须 $n\ge2$，因为 $n=1$ 的残差为 $\varphi^{-1}>1/2$。该有限深度上界趋零，限制的是任意固定相位精度及第二时钟深度的统一分离，不否定无限精度唯一性或另供更多资源的估计。

若实际校准改为 $\varphi_n=F_{n+1}/F_n$（$n\ge1$），同一残差所有者及其中 private fibonacci_convergent_error_eq 的指标平移给

~~~math
|\varphi-\varphi_n|=\frac{\varphi^{-n}}{F_n},\qquad
\omega_n\Delta=2\pi F_n,\quad
\omega_n\varphi_n\Delta=2\pi F_{n+1}.
~~~

两个采样相位此时完全重合，说明理想无理比不能由有限校准精度代替。此处比较的是零频率与 $\omega_n$ 的未知频谱目标，不将校准改变后的信号误作原固定五模式合同的结果。

反向分离下界也须保留其准确前提。对非零整数第一时钟别名编号 $k$，选最近整数 $\ell$，置 $\delta=\ell-\varphi k$，故 $|\delta|\le1/2$。其二次范数机制来自 [GoldenHurwitzBound 的 private golden_form_ne_zero 及 golden_hurwitz_bound](../../../D5/S1/Depth/GoldenHurwitzBound.lean)；后者逐字给的是有理数 $q$ 的 $1/(\sqrt5\operatorname{den}(q)^2+\operatorname{den}(q))<|\varphi-q|$，不是下面的更强最近整数分母。此处所需的有域估计为

~~~math
N=\ell^2-k\ell-k^2
=(\ell-\varphi k)(\ell+\varphi^{-1}k)
=\delta(\sqrt5 k+\delta)\in\mathbb Z\setminus\{0\}.
~~~

非零性因为 $k\ne0$ 且两个根 $\varphi,-\varphi^{-1}$ 都无理；于是

~~~math
1\le|N|\le|\delta|(\sqrt5|k|+1/2),\qquad
\operatorname{dist}(\varphi k,\mathbb Z)=|\delta|
\ge\frac1{\sqrt5|k|+1/2}.
~~~

对 $0\le d\le1/2$，正弦在 $[0,\pi/2]$ 上的凹性给 $\sin(\pi d)\ge2d$，从而同一编号的第二时钟弦长满足

~~~math
|1-e^{-2\pi i\varphi k}|\ge\frac4{\sqrt5|k|+1/2}.
~~~

这只控制已限制别名编号的频率差，不是有界频率区间内任意不同频率的统一正分离；后者仍可任意接近。多原子权重趋零、支撑合并和时长/参照误差也不由该下界消除。因此黄金模型的边界分类值、已校准纤维逆式和未知频谱的有限精度问题各保留其来源、量词和资源条件。证毕。

## 追加锚（本行以下为增补区）

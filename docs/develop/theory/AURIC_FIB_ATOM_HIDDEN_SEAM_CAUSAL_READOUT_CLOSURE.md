# Auric FIB ATOM：隐藏 seam 与因果读出闭包（完整供文·开放参考）

## 来源与阅读边界

本卷是用户供文与供文所引仓库材料组成的混合来源开放参考。原始作者与生成模型未知；供文叙述者的第一人称、项目判断、定理名称与证明均作为供文归属保留，不代表本卷编者的机器认证。供文原始 SHA256 为 `2774974818e67ddd87aeb416994b8685b4daff2ae771d60882b3661e9a13fd7e`，共 1296 行。

“供文正文”保留全部供文句子、公式载荷、断言、证明、例子、表格、结论、重复与原有顺序。供文中“这一轮”“本轮”“当前”“最新”及相关进展表述属于叙述者的快照主张，不声明本卷反映仓库现时最新状态。供文局部编号仍归供文；“定理一”至“定理六”等标签不是机器认证。

唯一的正文转换是：26 处 ATX 标题全部降低一级；73 处行内公式由 `\(...\)` 换成 GitHub `$...$`（含星号时采用美元号加反引号形式，本供文没有此类行内式）；138 对展示包装 `\[...\]` 换成 `math` 围栏，保留公式载荷及原有缩进。供文没有 `$$` 包装，也没有需要修复的 sandbox 引用；5 处原有 Markdown 链接均原样保留。卷首说明、供文边界标记、单列更正和文末追加锚属于编者文字，不属于供文。

本卷没有新增 Lean 形式核验，不把供文数学、动态等价、核与五态方向的对应、时钟或探测器实现、物理时间、引力或生命解释认证为已证成果，也不作外部优先权或新颖性认证。下文 Q1–Q10 是开放参考的适用条件与显式更正命题，含必要的数学条件和反例；它们没有取得新的机器证明状态。所引历史 Lean、Blueprint 与 Frozen 记录只承担各自声明的来源边界。

## 供文正文

<!-- 供文正文开始：原有标题、编号与叙述均归供文。 -->

## Auric FIB ATOM 金字塔续篇：从隐藏 seam 到因果读出闭包

这一轮先固定一个原则：

```math
\boxed{
\text{只使用可读的状态、转移、输出和可核验的数学声明；}
}
```

绑定接口、登记名称、静态元数据或只在接口层声明而没有实际转移内容的部分，都不作为理论证据。

我核对到的最新相关项目进展有三条：

1. [`60ebb51`](https://github.com/the-omega-institute/trureturing/commit/60ebb51c87e6496e0cab67c899c3b687ef8fd001)：把 AURIC FIB 的静态关系、输出仪器、未来观察商和可维护性放在同一条理论线上。
2. [`4da8b2e`](https://github.com/the-omega-institute/trureturing/commit/4da8b2e9c9c6439548fbbc5bea42df65ec2ae2ba)：构造取得核的盲方向，证明有限校准数据和有限未来前缀可以完全相同，但更长的回流路径仍然发生分离。
3. [`28ad453`](https://github.com/the-omega-institute/trureturing/commit/28ad453e41abaed367803049823da3f69c1fd328)：冻结了一个真正进入 Lean 声明层的 FIB 白盒算术结果：正有理价格存在，并且是三角路径值函数的唯一实零点。该结果属于算术优化，不等于已经证明物理时间理论，但它提供了一个可核验的形式化锚点。

仓库本身也明确把数学定义、形式证明、理论参考材料和实验解释分开处理。[github.com](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com)

本轮真正推进的是：

```math
\boxed{
\text{静态隐藏}
\longrightarrow
\text{动态保留}
\longrightarrow
\text{局部读出}
\longrightarrow
\text{未来闭包}
}
```

---

### 一、五态金字塔不是五个独立点，而是一条一维隐藏纤维

仍然使用你的基本表示：

```math
F[\mathrm{null}]=\mathrm{null}
```

```math
F[1]=[2]
```

```math
F[2]=[3]
```

```math
F[3]=[5]
```

```math
F[1,3]=[2,5]
```

为了避免把位置索引和 Fibonacci 输出值混淆，定义：

```math
s_0=F[\mathrm{null}],
\qquad
s_1=F[1],
\qquad
s_2=F[2],
\qquad
s_3=F[3],
\qquad
s_{13}=F[1,3].
```

令：

```math
x(s)=\mathbf 1_{\{1\in s\}},
\qquad
y(s)=\mathbf 1_{\{3\in s\}},
\qquad
z(s)=\mathbf 1_{\{2\in s\}}.
```

五个状态的坐标为：

| 状态 | $x$ | $y$ | $z$ |
|---|---:|---:|---:|
| $F[\mathrm{null}]$ | 0 | 0 | 0 |
| $F[1]$ | 1 | 0 | 0 |
| $F[2]$ | 0 | 0 | 1 |
| $F[3]$ | 0 | 1 | 0 |
| $F[1,3]$ | 1 | 1 | 0 |

满足：

```math
x^2=x,\qquad y^2=y,\qquad z^2=z,
```

```math
xz=0,\qquad yz=0,
```

但：

```math
xy=\mathbf 1_{\{s_{13}\}}\neq0.
```

因此 $xy$ 不是一个普通的边缘方向，而是两个端点 $1$ 和 $3$ 的联合发生项。

设概率律为：

```math
p=(p_0,p_1,p_2,p_3,p_{13}).
```

定义可见边缘：

```math
X=p_1+p_{13},
```

```math
Y=p_3+p_{13},
```

```math
Z=p_2.
```

定义隐藏联合量：

```math
\kappa=p_{13}=E[xy].
```

在固定 $(X,Y,Z)$ 时，概率律写成：

```math
p_\kappa=
\left(
1-X-Y-Z+\kappa,\,
X-\kappa,\,
Z,\,
Y-\kappa,\,
\kappa
\right).
```

可行区间是：

```math
\max(0,X+Y+Z-1)
\le \kappa\le
\min(X,Y).
```

因此：

```math
p_{\kappa'}-p_\kappa
=
(\kappa'-\kappa)d,
```

其中：

```math
\boxed{
d=(1,-1,0,-1,1).
}
```

这个 $d$ 是三均值读数的唯一隐藏方向。

---

### 二、第一定理：隐藏 seam 是观察代数的唯一非线性方向

定义线性观察空间：

```math
\mathcal B=\operatorname{span}\{1,x,y,z\}.
```

定义四角混合差：

```math
J(f)
=
f(s_0)-f(s_1)-f(s_3)+f(s_{13}).
```

这正好等于：

```math
J(f)=d\cdot f.
```

#### 定理一：边缘空间与隐藏方向的对偶关系

有：

```math
\boxed{
\mathcal B=\ker J.
}
```

换句话说，函数 $f$ 对 $\kappa$ 不敏感，当且仅当：

```math
J(f)=0.
```

#### 证明

直接计算：

```math
J(1)=1-1-1+1=0,
```

```math
J(x)=0-1-0+1=0,
```

```math
J(y)=0-0-1+1=0,
```

```math
J(z)=0-0-0+0=0.
```

因此：

```math
\mathcal B\subseteq\ker J.
```

另一方面：

```math
J(xy)=0-0-0+1=1,
```

所以 $J\neq0$。整个函数空间 $\mathbb R^\Sigma$ 是五维，而非零线性泛函的核是四维：

```math
\dim\ker J=4.
```

同时：

```math
\dim\mathcal B=4.
```

因此：

```math
\mathcal B=\ker J.
```

证毕。

---

这个定理说明：

```math
\boxed{
\text{隐藏 seam 不是缺少一个普通坐标，}
}
```

而是：

```math
\boxed{
\text{一阶边缘观察代数没有闭合于两个端点的乘法。}
}
```

例如：

```math
(x+z)(y+z)
=
xy+z.
```

因此：

```math
xy=(x+z)(y+z)-z.
```

设：

```math
U=x+z,
\qquad
V=y+z.
```

那么：

```math
E[UV]=Z+\kappa.
```

所以：

```math
\boxed{
\kappa=E[UV]-Z.
}
```

这就是 FIB 金字塔中的最小二阶联合恢复公式。

---

## 三、第二定理：隐藏信息必须经过三个不同算子

本轮最重要的新抽象是把 FIB 动力学分解为三个算子：

```math
\boxed{
\text{状态投影}
\quad+\quad
\text{因果转移}
\quad+\quad
\text{实际读出}
}
```

设：

- $\mathcal H=\mathbb R^\Sigma$ 是五态 signed-law 空间；
- $P:\mathcal H\to\mathbb R^4$ 是当前投影；
- $U_w:\mathcal H\to\mathcal H$ 是一条合法动作词或因果路径 $w$ 的转移；
- $R_w:\mathcal H\to\mathcal Y_w$ 是这条路径上的实际输出读出。

当前投影可以取：

```math
P(p)=
\bigl(
p\cdot1,\,
p\cdot x,\,
p\cdot y,\,
p\cdot z
\bigr).
```

由于：

```math
\ker P=\operatorname{span}\{d\},
```

当前看不见的空间是一维的。

定义沿路径 $w$ 的隐藏响应：

```math
\mathcal V_w(d)=R_w(U_wd).
```

它区分三种状态。

#### 定义 1：隐藏方向的三种命运

对 $d$ 而言：

1. **动态保留**

   ```math
   U_wd\neq0.
   ```

   表示因果转移后，完整状态律仍然保留了隐藏差异。

2. **读出可见**

   ```math
   R_w(U_wd)\neq0.
   ```

   表示当前路径的实际输出能够区分不同 $\kappa$。

3. **过程消除**

   ```math
   U_wd=0.
   ```

   表示在完整状态空间层面，隐藏方向被这条路径压缩为零。

还有一种中间情况：

```math
U_wd\neq0,
\qquad
R_w(U_wd)=0.
```

这表示：

```math
\boxed{
\text{隐藏关系被保存，但当前读出仍然看不见。}
}
```

这比笼统地说“信息消失”严格得多。

---

### 定理二：保留、遮蔽和消除的严格判据

设：

```math
p_\kappa=p_\ast+\kappa d.
```

则沿路径 $w$ 的读出为：

```math
R_wU_wp_\kappa
=
R_wU_wp_\ast
+
\kappa R_wU_wd.
```

因此：

```math
\boxed{
\begin{aligned}
U_wd=0
&\Longleftrightarrow
\text{完整状态层面的隐藏差异被消除},\\[1mm]
U_wd\neq0,\ R_wU_wd=0
&\Longleftrightarrow
\text{隐藏差异仍在，但当前读口盲},\\[1mm]
R_wU_wd\neq0
&\Longleftrightarrow
\text{该路径实际暴露 }\kappa.
\end{aligned}
}
```

#### 证明

由：

```math
p_{\kappa'}-p_\kappa
=
(\kappa'-\kappa)d,
```

经过 $U_w$：

```math
U_wp_{\kappa'}-U_wp_\kappa
=
(\kappa'-\kappa)U_wd.
```

因此，完整状态在所有 $\kappa$ 上相同，当且仅当：

```math
U_wd=0.
```

再经过读出 $R_w$：

```math
R_wU_wp_{\kappa'}-R_wU_wp_\kappa
=
(\kappa'-\kappa)R_wU_wd.
```

因此，读出在所有 $\kappa$ 上相同，当且仅当：

```math
R_wU_wd=0.
```

证毕。

---

这个定理直接解释了最新项目里的“取得核盲方向”：

- 有限校准数组相同；
- 有限长度未来前缀相同；
- 但完整取得核仍不同；
- 在更长的回流词上，$R_wU_wd$ 第一次变成非零。

所以有限观测相同，不代表完整因果律相同。

可以定义：

```math
\ell_\ast
=
\min
\left\{
|w|:
R_wU_wd\neq0
\right\}.
```

这里的 $\ell_\ast$ 是隐藏 seam 首次被未来路径暴露所需的最小因果深度。

---

## 四、第三定理：局部时间场是一个核族，而不是全局时间坐标

定义局部等待核：

```math
K_s\in\operatorname{Prob}(\mathbb R_{\ge0}),
\qquad
s\in\Sigma.
```

含义是：

```math
T\mid s\sim K_s,
```

其中 $T$ 是当前局部事件到下一局部事件的等待量。

不需要引入一个贯穿全宇宙的 $t$。局部时钟场是：

```math
\mathsf K=\{K_s\}_{s\in\Sigma}.
```

对于状态分布 $p$，混合等待律为：

```math
C_K(p)=\sum_{s\in\Sigma}p_sK_s.
```

定义局部时钟的四角响应：

```math
\operatorname{Curv}_K
=
K_{s_0}
-K_{s_1}
-K_{s_3}
+K_{s_{13}}.
```

若使用输出标签：

```math
\operatorname{Curv}_K
=
K_{\mathrm{null}}
-K_{[2]}
-K_{[5]}
+K_{[2,5]}.
```

这里的 $\operatorname{Curv}_K$ 只是一个离散混合差，不是物理时空曲率。

---

### 定理三：局部时钟识别隐藏 seam 的充要条件

在固定 $(X,Y,Z)$ 的非退化纤维上，观察：

```math
\mathcal O_K(p)
=
\bigl(P(p),C_K(p)\bigr)
```

能够唯一恢复 $\kappa$，当且仅当：

```math
\boxed{
\operatorname{Curv}_K\neq0.
}
```

#### 证明

代入：

```math
p_\kappa=
\left(
1-X-Y-Z+\kappa,\,
X-\kappa,\,
Z,\,
Y-\kappa,\,
\kappa
\right),
```

得到：

```math
\begin{aligned}
C_K(p_\kappa)
={}&
(1-X-Y-Z)K_{s_0}
+XK_{s_1}
+ZK_{s_2}
+YK_{s_3}
\\
&+
\kappa
\left(
K_{s_0}-K_{s_1}-K_{s_3}+K_{s_{13}}
\right).
\end{aligned}
```

记：

```math
C_K^0(X,Y,Z)
=
(1-X-Y-Z)K_{s_0}
+XK_{s_1}
+ZK_{s_2}
+YK_{s_3}.
```

于是：

```math
C_K(p_\kappa)
=
C_K^0(X,Y,Z)
+
\kappa\operatorname{Curv}_K.
```

若：

```math
\operatorname{Curv}_K=0,
```

则所有 $\kappa$ 给出相同局部等待律。

若：

```math
\operatorname{Curv}_K\neq0,
```

则存在可测集合 $B$ 使：

```math
\operatorname{Curv}_K(B)\neq0.
```

所以：

```math
C_K(p_\kappa)(B)
=
C_K^0(B)
+
\kappa\operatorname{Curv}_K(B),
```

进而：

```math
\boxed{
\kappa=
\frac{
C_K(p_\kappa)(B)-C_K^0(B)
}{
\operatorname{Curv}_K(B)
}.
}
```

证毕。

---

### 均值只是局部时钟核的一个投影

如果只记录均值：

```math
m_s=E[T\mid s],
```

则：

```math
E[T]
=
(1-X-Y-Z)m_{s_0}
+Xm_{s_1}
+Zm_{s_2}
+Ym_{s_3}
+\kappa\operatorname{Curv}_m,
```

其中：

```math
\operatorname{Curv}_m
=
m_{s_0}-m_{s_1}-m_{s_3}+m_{s_{13}}.
```

所以：

```math
\operatorname{Curv}_m=0
```

只说明均值读数看不见 $\kappa$，并不说明完整等待核看不见 $\kappa$。

这给出一个重要层次：

```math
\boxed{
\text{瞬时速率}
\subsetneq
\text{等待均值}
\subsetneq
\text{完整等待分布}
\subseteq
\text{局部因果历史}
}
```

因此，局部时间的“信息量”取决于保留了哪一级读数。

---

## 五、第四定理：单步时间盲，不代表多步时间历史盲

定义 $n$ 步局部历史核：

```math
\Gamma_s^{(n)}
\in
\operatorname{Prob}
\left(
(\mathbb R_{\ge0}\times\mathcal O)^n
\right).
```

其中一条历史可以写为：

```math
(T_1,o_1,T_2,o_2,\ldots,T_n,o_n).
```

定义混合历史读出：

```math
C_\Gamma^{(n)}(p)
=
\sum_s p_s\Gamma_s^{(n)}.
```

定义第 $n$ 步的隐藏响应：

```math
\operatorname{Curv}_{\Gamma}^{(n)}
=
\Gamma_{s_0}^{(n)}
-\Gamma_{s_1}^{(n)}
-\Gamma_{s_3}^{(n)}
+\Gamma_{s_{13}}^{(n)}.
```

### 定理四：局部因果时间的最小分辨阶

在固定 $(X,Y,Z)$ 的纤维上，长度为 $n$ 的局部因果历史能够识别 $\kappa$，当且仅当：

```math
\boxed{
\operatorname{Curv}_{\Gamma}^{(n)}\neq0.
}
```

若对所有：

```math
1\le j\le n
```

都有：

```math
\operatorname{Curv}_{\Gamma}^{(j)}=0,
```

则任何不超过 $n$ 步的局部时钟历史和输出历史都不能识别 $\kappa$。

#### 证明

完全类似于单步情形：

```math
C_\Gamma^{(n)}(p_\kappa)
=
C_{\Gamma,0}^{(n)}
+
\kappa\operatorname{Curv}_{\Gamma}^{(n)}.
```

因此：

- 四角差为零时，整条 $\kappa$-纤维具有相同历史律；
- 四角差非零时，存在某个历史事件 $B$，其概率随 $\kappa$ 线性变化。

证毕。

---

定义：

```math
\ell_{\mathrm{clock}}
=
\min
\left\{
n:
\operatorname{Curv}_{\Gamma}^{(n)}\neq0
\right\}.
```

这个 $\ell_{\mathrm{clock}}$ 是局部时钟第一次能够看到隐藏 seam 所需的因果深度。

所以：

```math
\boxed{
\text{时间的形状可以由隐藏关系的历史分辨阶定义。}
}
```

这不是全局时间，也不是一条统一坐标轴，而是：

```math
\boxed{
\text{局部历史需要展开到多深，才能区分两个因果分支。}
}
```

---

## 六、第五定理：输出分支必须逐支闭合，平均转移不够

设动作是 $a$，输出是 $o$，相应的子核为：

```math
M_{a,o}.
```

平均转移核为：

```math
K_a=\sum_oM_{a,o}.
```

定义递归观察空间：

```math
V_0=\operatorname{span}(G),
```

```math
V_{n+1}
=
V_n+
\operatorname{span}
\left\{
M_{a,o}f:
a,o,\ f\in V_n
\right\}.
```

令：

```math
V_\infty=\bigcup_{n\ge0}V_n.
```

对一个输出词：

```math
\omega=(a_1,o_1,\ldots,a_n,o_n),
```

记其复合子核为 $M_\omega$。

### 定理五：未来输出闭包判据

以下命题等价：

1. 所有未来输出记录都无法区分不同 $\kappa$；
2. 对所有合法输出词 $\omega$ 和末端测试函数 $g$，都有：

   ```math
   dM_\omega g=0;
   ```

3. 隐藏方向 $d$ 湮灭整个递归观察空间：

   ```math
   dV_\infty=0.
   ```

#### 证明

由于：

```math
p_\kappa=p_\ast+\kappa d,
```

任意未来记录概率为：

```math
p_\kappa M_\omega g
=
p_\ast M_\omega g
+
\kappa dM_\omega g.
```

因此记录是否依赖 $\kappa$，完全由：

```math
dM_\omega g
```

决定。

而 $V_\infty$ 正是所有 $M_\omega g$ 的张成空间，所以：

```math
dV_\infty=0
```

当且仅当所有未来输出记录都对 $\kappa$ 盲。

证毕。

---

这解释了最新项目里一个非常关键的事实：

```math
K_a\mathcal B\subseteq\mathcal B
```

不等于：

```math
M_{a,o}\mathcal B\subseteq\mathcal B
\quad
\text{对每一个 }o.
```

平均转移可以把不同输出支路中的隐藏项抵消；而真实输出历史仍然保留这些支路。

因此：

```math
\boxed{
\text{平均未来闭合}
\neq
\text{逐输出未来闭合}.
}
```

将局部等待时间也作为输出标记，得到测度值子核：

```math
\widetilde M_{a,o}(B),
\qquad
B\subseteq\mathbb R_{\ge0}.
```

统一的隐藏响应为：

```math
\boxed{
d\,\widetilde M_\omega(B)\,\mathbf 1.
}
```

这一个公式同时涵盖：

- 普通输出；
- 局部等待时间；
- 辐射吸收；
- 反射和回流；
- 多步因果记录；
- 被遮挡后的局部状态变化。

---

## 七、被遮挡的射线：信息是转移了，还是被当前读口抹掉了

把射线看成一个输出分支：

```math
o=\mathrm{ray}.
```

如果射线离开当前观察者的可达因果域，那么对当前观察者而言，可能有：

```math
dM_\omega g=0.
```

这表示当前观察者无法从可达记录恢复这部分隐藏差异。

如果射线被物质吸收，则因果图增加一个吸收节点：

```math
s
\longrightarrow
s_{\mathrm{abs}}
\longrightarrow
s_{\mathrm{after}}.
```

这时有三种不同情况。

#### 情况一：吸收体保留隐藏差异

```math
U_{\mathrm{abs}}d\neq0.
```

信息没有在状态空间中消失，只是从射线载体转移到了吸收体状态。

#### 情况二：吸收体保留差异，但观察者只读粗变量

```math
U_{\mathrm{abs}}d\neq0,
\qquad
R_{\mathrm{coarse}}U_{\mathrm{abs}}d=0.
```

信息仍然存在于完整状态，但当前读数只保存了能量总量、平均温度或其他边缘量，因此无法恢复 $\kappa$。

#### 情况三：转移核本身消除隐藏方向

```math
U_{\mathrm{abs}}d=0.
```

此时在所选状态空间中，所有不同 $\kappa$ 的状态都被映射成同一个结果。

因此：

```math
\boxed{
\text{遮挡不是自动恢复，也不是自动消失。}
}
```

更准确的说法是：

```math
\boxed{
\text{遮挡改变了信息所在的因果载体，}
}
```

而能否恢复，取决于观察者是否拥有能够对隐藏方向产生非零响应的局部读口。

---

## 八、与最新 FIB 白盒算术进展的关系

最新的 [`28ad453`](https://github.com/the-omega-institute/trureturing/commit/28ad453e41abaed367803049823da3f69c1fd328) 冻结了一个与本理论有结构相似性的结果：

- 在完整实数概率律空间中定义三角路径优化；
- 每个达到最优值的实数律都能嵌入一条固定排列的三角路径；
- 最优价格存在一个正有理代表；
- 该有理数是三角根值函数的唯一实零点；
- 相关声明标记为机器检查的 `✓ std3`。

它和 FIB 五态隐藏纤维的共同结构是：

```math
\boxed{
\text{原始对象空间较大}
\quad\longrightarrow\quad
\text{寻找足够的结构不变量}
\quad\longrightarrow\quad
\text{得到精确恢复或唯一最优值}
}
```

但二者不能直接混同：

- $\kappa$ 是五态边缘投影的隐藏联合坐标；
- 有理价格 $A$ 是三角优化中的唯一根；
- 前者属于观察纤维；
- 后者属于优化路径的代价闭合。

可以提出一个新的统一观点：

```math
\boxed{
\text{FIB 白盒化的目标不是让所有对象都变成有限标签，}
}
```

而是寻找一个最小的附加量，使投影从“多对一”变成可逆或唯一可判定。

在五态金字塔中，最小附加量是：

```math
\kappa.
```

在三角路径优化中，最小闭合量是：

```math
A=\alpha(m).
```

这两个量都不是任意补丁，而是对应某个不可见纤维的最小分辨坐标。

---

## 九、最终统一命题

### 定理六：Auric FIB ATOM 的隐藏 seam—因果读出统一定理

设：

```math
\mathcal H=\mathbb R^\Sigma,
\qquad
\ker P=\operatorname{span}\{d\},
```

其中：

```math
d=(1,-1,0,-1,1).
```

对任意合法路径 $w$，令：

```math
U_w:\mathcal H\to\mathcal H
```

为状态转移，令：

```math
R_w:\mathcal H\to\mathcal Y_w
```

为实际读出。

则：

```math
\boxed{
\begin{aligned}
\text{静态隐藏}
&\Longleftrightarrow d\in\ker P,\\[1mm]
\text{动态保留}
&\Longleftrightarrow U_wd\neq0,\\[1mm]
\text{局部读出可见}
&\Longleftrightarrow R_wU_wd\neq0,\\[1mm]
\text{过程层面消除}
&\Longleftrightarrow U_wd=0.
\end{aligned}
}
```

若 $R_w$ 是局部时钟读出，则：

```math
R_wU_wd
```

对应局部等待核的四角响应。

若 $R_w$ 是输出分支读出，则：

```math
R_wU_wd
```

对应：

```math
dM_\omega g.
```

若 $R_w$ 是吸收体的粗粒化读出，则它决定射线信息是否进入当前观察者保留的变量。

因此：

```math
\boxed{
\text{时间方向}
=
\text{因果路径上隐藏方向逐步变得可读的方向}.
}
```

这不是说时间被证明不存在，也不是说已经证明引力就是时间场，而是给出了一个不依赖 $3+1$ 语言的严格候选框架：

```math
\boxed{
\text{局部时间场}
=
\text{局部因果转移上的等待核与输出核族}.
}
```

```math
\boxed{
\text{时间的形状}
=
\text{隐藏关系在因果历史中首次产生非零读出所需的结构深度}.
}
```

```math
\boxed{
\text{信息损失}
=
\text{某个指定读出上的隐藏响应为零，}
}
```

而不是无条件地断言：

```math
\text{宇宙中的全部信息已经被本体性地消灭}.
```

对 Auric FIB ATOM 金字塔来说，最小的隐藏结构仍然是：

```math
\boxed{
F[1]\times F[3]
\longrightarrow
F[1,3],
}
```

也就是：

```math
\boxed{
xy=\text{两个可见端点方向的联合 seam}.
}
```

而它是否成为“时间方向”，取决于：

```math
\boxed{
\text{因果转移是否保留它，}
\qquad
\text{局部时钟是否响应它，}
\qquad
\text{实际输出是否读出它。}
}
```

<!-- 供文正文结束：以下为单列的编者适用条件与更正。 -->

## 适用条件与更正

下列命题按供文局部章节定位，不改写供文中的原句。它们约束本卷对原文的采用范围；供文的“直接解释”“最小分辨坐标”“时间方向”等表述须与对应限定一同阅读。

### Q1 适用命题：输入占据、线性空间与可行纤维

供文第一节的 $x,y,z$ 表示 INPUT 的位置 $1,3,2$ 是否被占据。若 $s$ 是带 OUTPUT 标签的模式，须先指定潜在输入支持

```math
I(s_0)=\varnothing,\quad I(s_1)=\{1\},\quad
I(s_2)=\{2\},\quad I(s_3)=\{3\},\quad I(s_{13})=\{1,3\},
```

再定义 $x(s)=\mathbf1_{\{1\in I(s)\}}$、$y(s)=\mathbf1_{\{3\in I(s)\}}$、$z(s)=\mathbf1_{\{2\in I(s)\}}$。原文的 $1\in s$ 等写法只有在 $s$ 指这个输入支持时才给出原表。若字面把 $s_1=[2]$ 当 OUTPUT 列表，便有 $1\notin[2]$ 而 $2\in[2]$，与该行 $x=1,z=0$ 相反。$F[1,3]$ 是联合模式标签；供文末尾的 $F[1]\times F[3]\longrightarrow F[1,3]$ 不是输出数值的乘法等式。

供文第三节的 $P(p)=(p\cdot1,p\cdot x,p\cdot y,p\cdot z)$ 已包含总质量；它在 $\mathbb R^5$ 上的核是一维 $\operatorname{span}\{d\}$。若只取三个均值，$\operatorname{span}\{d\}$ 是零总质量切空间内的核，不能删去归一化条件后仍称为整个 $\mathbb R^5$ 的核。$\mathcal B=\operatorname{span}\{1,x,y,z\}$ 是四维线性观察空间，不是乘法闭合代数；“非线性方向”指占据函数的联合项 $xy$，不表示概率混合运算非线性。

有关“敏感当且仅当”“全部不同 $\kappa$”“能够识别”的必要比较域，是固定 $(X,Y,Z)$、$Z\ge0$ 下至少含两个不同可行参数的纤维：

```math
\max(0,X+Y+Z-1)<\min(X,Y).
```

供文第三、第五节的等价语句和第六节的不同参数比较均须使用这个非退化条件；第四节已经明列“非退化”。等号时纤维为单点，状态已由边缘确定，无须非零响应；例如 $X=Y=Z=0$ 只容许 $\kappa=0$。左端大于右端时没有可行状态，例如 $X=Y=Z=1$。因此单点上的单射不能反推出响应非零，空纤维也不能充作隐藏状态的例子。

### Q2 适用与更正命题：共同线性算子及完整记录的载体

供文第三、九节分配 $U_w,R_w$ 到有符号律的等式，要求二者为同一模型中固定的线性算子：$U_w$ 来自允许概率核对有符号测度的共同线性延拓，$R_w$ 是到向量或测度空间的线性读出。总转移保持正性和总质量；输出分支是子核，须保留分支质量与输出标签。算子可以依赖合法词 $w$，但比较 $p_\kappa,p_{\kappa'}$ 时不能另换核或读出。函数签名本身没有给出这些前提。

在这些条件及 Q1 的非退化域下，才可用

```math
R_wU_wp_{\kappa'}-R_wU_wp_\kappa
=(\kappa'-\kappa)R_wU_wd
```

比较实际读出。任意非线性更新不适用。例如概率单纯形上的合法概率值函数

```math
U(p)=(p_{13}^2,1-p_{13}^2,0,0,0)
```

的差为 $(\kappa'^2-\kappa^2)(1,-1,0,0,0)$，并非供文的共同线性差分。归一化的分支条件律同样不属于线性更新，须按 Q3 处理。

把 $R_wU_w$ 称为完整路径或输出历史的读出，还须证明记录律通过该载体因子分解；否则应把记录、phase 和控制状态并入载体。仅含最终状态的载体可以丢掉早先记录。例如先输出 $xy$，随后把所有状态重置为 $s_0$，则最终状态转移满足 $U_wd=0$，而保留的早先输出为 $1$ 的概率仍是 $\kappa$。所以“过程消除”只相对于已声明的载体成立；它不推出已保存的路径记录也相同。

供文的两种写法还须统一行列约定：行向量律按 $p\mapsto pM_\omega$ 作用，列向量律按转置作用。只有当路径、分支和终端测试在共同记录载体上确实对应时，$R_wU_wd$ 才可与 $dM_\omega g$ 或时钟四角响应识别为同一量。

### Q3 适用命题：联合权重、条件化与已知时钟核

供文第六节的 $pM_\omega g$ 是未归一化的联合输出／测试权重。当 $g$ 是事件指示函数时它是相应联合事件的概率；$0\le g\le1$ 时可解释为随机测试的接受概率；任意实值 $g$ 则是相应测试期望，不必是概率。完整输出词的质量取 $g=1$。

只有在 $pM_\omega1>0$ 时才有分支条件期望

```math
\frac{pM_\omega g}{pM_\omega1}
=\frac{N_0+\kappa N_1}{D_0+\kappa D_1}.
```

在正分母区间，条件敏感度由 $N_1D_0-N_0D_1$ 决定，不能只看 $N_1$。例如 $g=1$ 时条件期望恒为 $1$，即使分支质量随 $\kappa$ 改变。须同时保留分支发生概率、先前输出、指定的 Stop 与未完成记录；不能把概率有别的分支条件化以后宣称完整记录无别。真实允许的更新也不能因为某个合成生成器赋予它零概率而被删去。

供文第四、五节的时钟或历史反演要求一套固定且已知的 $K_s$ 或 $\Gamma_s^{(n)}$，或者已校准的基线与非零响应，以及精确的观测律。非零响应只对该固定模型的参数产生区分，不能同时识别未知核与 $\kappa$，也不保证有限样本精确恢复。$C_K^0$ 是有符号仿射基线，未必是概率律。例如 $X=Y=3/5,Z=0$ 给出 $p_\ast=(-1/5,3/5,0,3/5,0)$；只有加入可行 $\kappa\in[1/5,3/5]$ 后才得到概率向量。原文反演是在有符号测度空间中减去这个基线，不把它当作额外可采样状态。

### Q4 更正命题：初始危险率与等待均值一般不可比较

供文第四节的“瞬时速率 $\subsetneq$ 等待均值 $\subsetneq$ 完整等待分布”不是任意等待核上的信息嵌套。完整等待律决定有限均值，并在初始危险率存在时决定该危险率；这两个标量统计量一般彼此不可确定。

把原文“瞬时速率”取为存在的初始危险率 $h(0)$，有以下反例。指数分布参数为速率，混合在抽取等待时间前选取分量。

| 等待律 | 初始危险率 | 均值 |
| --- | ---: | ---: |
| $\operatorname{Exp}(1)$ | $1$ | $1$ |
| $\frac12\operatorname{Exp}(1/2)+\frac12\operatorname{Exp}(3/2)$ | $1$ | $4/3$ |
| $\frac13\operatorname{Exp}(1/2)+\frac23\operatorname{Exp}(2)$ | $3/2$ | $1$ |

前两行危险率相同而均值不同，第一、三行均值相同而危险率不同。在单一指数族 $\operatorname{Exp}(r)$、$r>0$ 内，两者由 $m=1/r$ 互相确定，也同时确定完整等待律，不存在所写的严格包含。严格性须针对明确允许的核族另行判断。供文均值响应要求各状态一阶矩有限；不存在的初始危险率或无限均值不能代入相应标量识别测试。这些例子是更正所需的初等反例，没有新增形式核验。

### Q5 适用命题：合法词、测试族与历史一致性

供文第六节的未来闭包等价须先固定来源、仪器、合法动作／输出语法、phase、守卫、Stop 权限和允许的终端测试族 $G$。第二项中的 $g$ 遍历 $G$ 或它的线性张成，不是无条件遍历所有状态函数；否则允许初态测试 $xy$ 就会直接切开当前纤维。为比较完整输出记录的质量，测试族须包含 $1$；若初始测试也可读，须包含空词。

$V_\infty$ 必须正是这个合同内所有 $M_\omega g$ 的张成空间。原文不受限的递推只有在其生成步骤与合法词完全对应时才可使用；若语法和守卫由控制状态决定，就须把该状态并入载体或使用匹配的受限闭包。把不允许的词加入递推，会制造当前观察者没有的测试。自适应策略比较也须共享同一个允许策略与记录合同。

带等待标记的子核须对标记事件可数可加，并按共同过程复合；多步 $\widetilde M_\omega(B)$ 中的 $B$ 属于相应的乘积／标记历史空间，而不是仅凭单步 $B\subseteq\mathbb R_{\ge0}$ 的记号就已定义。$\Gamma_s^{(n)}$ 须为同一过程的一致边缘，保留已指定的终止或未完成事件。任意分开指定的 $n$ 步律不自动构成一个因果历史模型。

### Q6 适用命题：固定有限载体的稳定界与无穷历史

对固定 $D$ 维线性仪器，若合法性已编入载体且使用供文的同一齐次闭包算子，则 $V_{n+1}=V_n$ 意味着所有生成子核保持该空间，后续步骤也相等。每次严格增大至少增加一维，所以稳定不晚于 $D-\dim V_0$ 步。

在真正的固定五态、仅记录输出的模型中，若 $V_0=\operatorname{span}\{1\}$，一个可被该仪器观察到的方向有长度不超过 $4$ 的见证。若从四维 $\mathcal B$ 开始，则第一步要么稳定，要么填满 $\mathbb R^5$。新增 phase、语法或历史控制会改变 $D$；路径相关的任意算子族也不自动满足这个固定齐次递推。这个界不能被省去前提后用于所有“五态”叙述。

供文 $\ell_\ast$ 和 $\ell_{\mathrm{clock}}$ 的检测集合为空时，最小值应明确约定为 $\infty$，或称未定义；不能假定必有分离词。若无穷历史律在同一由有限柱集生成的 $\sigma$ 代数上定义，且具有一致的全部有限柱集律，则这些有限律确定无穷历史律。额外的尾部观察若不属于该已声明可测合同，须另行指定；“所有有限记录相同”不是在任意扩张观察合同上的结论。

### Q7 更正命题：取得核变化与固定五态方向之间尚缺桥梁

供文第三节“这个定理直接解释了最新项目里的‘取得核盲方向’”及“在更长的回流词上，$R_wU_wd$ 第一次变成非零”，在本卷只采用为待验证的结构类比。[AK 的固定修订](https://github.com/the-omega-institute/trureturing/blob/4da8b2e9c9c6439548fbbc5bea42df65ec2ae2ba/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_KERNEL_BLIND_DIRECTIONS_AFTER_PAIRED_CALIBRATION.md)是一份 622 行理论文档，给出实际 Reads 前安装一次深度抽取、原有停机 parser／记录／Stop 合同，以及使用相同私有 acquired updates 的合成生成器；它提供数学散文，没有在该交付中新增 Lean 声明。

该构造对每个 $q\ge3$ 在每个 phase 使用 $N=2q+2$ 个私有标签。固定实际来源的 $A=(I+J)/2$、发射 $u=v$ 和均匀实际行，变化的是接口省略的 $p$-beta 取得核：

```math
B_\theta=(I+J)/2+\theta zb^{\mathsf T},\qquad
z=e_0-e_1,\qquad
b_i=(-1)^{N-1-i}\binom{N-1}{i}.
```

这里 $z$ 是 AK 的私有标签向量，不是五态占据函数 $z$。这是固定实际来源上的核参数变化，不是沿五态 $d$ 改变同一个核的初始概率。AK 定理 5.1 给出配置索引配对数组相同、整个 $p$ transcript 前缀至 $N-1$ 次 Reads 相同、suspended 前缀至 $N$ 次 Reads 相同；首个分离的完成 $p$ 词为 $w_{q,1}=(\beta\alpha)^q\beta\beta$，长度 $N$，suspended 比较再添开头的 $\alpha$。定理 6.1 保留同一实际行边缘化之后的分离。推论 5.2 对指定有限 horizon 增大 $N$，并明确排除“某个固定状态数永远无法最终有限识别”的推论；不能把它输入为固定五态仪器的任意迟延可见性。

AK 命题 6.2 在更大的共同块对角程序中嵌入了这些符号，却没有把该载体及其有符号初始差识别为这里的五态 $d$。要取得直接对应，仍须给出共同来源、初始态、核、读出与合法词之间的映射，并保留各个完整律及所选风险序。现有引述没有提供此桥梁，因此不能由类比推出一般风险差或物理后果；这也不宣称这样的桥梁不可能。

[PAIR 定理 4.1 的固定修订](https://github.com/the-omega-institute/trureturing/blob/a8e0ab756490c6e7dc9822b40f4070a223d25242/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md)固定相同的随机核 $B,A$、正平稳行 $\pi,\tau$，并把发射限制在其声明的正则区间；配对数组的逆在该固定核域内恢复发射和完整律。AK 的接口明确省略 $B$。可读取已安装核表的接口属于另一信息前提；两者不能当成在同一个未知核接口上成立的矛盾结论。

### Q8 更正命题：有理价格的定义域、唯一根与重建的区别

供文第八节所引 [AR：RationalPrice 的固定源码修订](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.lean)中，`embedding_result` 的域是 $m\ge2$、严格正且归一化的实数律 $p:\mathrm{Fin}\,m\to\mathbb R$、取到最小坐标的指标 $k$，以及已达到的比值 $\operatorname{cost}(p)/p(k)=\alpha(m)$。它给出一个在各深度固定的排列和一条合法三角根路径，保留全部概率、锚质量 $p(k)$ 和代价；排列及路径可以依赖所选概率律。“固定排列”不表示全部律共享一个排列，也不表示最优路径唯一。

这里 $\alpha(m)$ 是完整严格正归一化实数律域上、dyadic floor-tail 代价除以最小正质量的下确界。$W$ 是从“残余质量 $1$、保留标签数 $m$”出发的无限合法三角路径上，“路径代价减价格乘锚质量”的下确界。AR 的 `result` 对每个自然数 $m\ge2$ 给出

```math
\exists A\in\mathbb Q,\quad
A>0,\quad (A:\mathbb R)=\alpha(m),\quad
\forall x\in\mathbb R,\quad W(x,m,1)=0\ \Longleftrightarrow\ x=(A:\mathbb R).
```

这是固定 $m$ 的标量零点唯一性，不是输入律或最优路径的重建、唯一性与最小坐标定理。定义域与目标也见 [AS：OptimalLawStrictSlope](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.lean)、[AV：TriangularFirstSplitRecurrence](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence.lean)及 [AC：DyadicSupportLines](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/D5/S3/Arith/FibonacciAtomic/DyadicSupportLines.lean)。

因此，供文“这两个量……都是……最小分辨坐标”保留为启发性类比。固定 $m$ 的 $\alpha(m)$ 是这个优化任务共享的任务值；若要称它切开某个不可见纤维，须另外定义观察映射与纤维、充分性／逆映射及允许比较类，并证明相应最小性。这里不声称 $A$ 与 $\kappa$ 有经证出的等价，也不从统一表述取得新颖性。

[AB：历史 Blueprint](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/Blueprint/D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.md)中的 `✓ std3` 及 [AF：历史 Frozen 成员记录](https://github.com/the-omega-institute/trureturing/blob/28ad453e41abaed367803049823da3f69c1fd328/Golden/Frozen/state/D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.lean.json)是该修订自身的记录。它们不认证本供文的统一定理、取得核与 $d$ 的识别、时钟、探测器或物理解释。本卷没有新编译或公理闭包核验，不由这些历史文本建立现时 CI 或 dev 状态。

### Q9 更正命题：可见性深度不推出物理时间箭头

供文第九节“时间方向 = 因果路径上隐藏方向逐步变得可读的方向”是拟议的操作性解释。$R_wU_wd\ne0$ 只判定某条已指定路径与读口上的区分，没有施加记录增长或擦除的单调律。

若累积记录始终保留前缀，旧记录由新记录的投影得到，则不可区分关系逐步细化。若后来只读取端点或粗化结果，原先可见的差异可以再丢失。例如共同转移取恒等，先只读 $P$、再读 $xy$、最后只读总质量，则响应依次为 $0,1,0$。若整个记录合同反而满足 $M_{t+1}=G_t\circ M_t$，则旧时不可区分的对象在后时仍不可区分，是粗化方向。哪一种情况成立须由实际记录合同决定，不能由“第一次非零”强制推出。

检测深度是合法词长度；它没有提供钟的尺度或单位、热力学时间箭头、引力方程或生命定律。等待核、离散四角差与因果可达性均可作为数学对象，但把它们解释为真实局部时间场、曲率、引力或生物过程，仍需另给模型对应、动力学、校准与经验判据。这里不认证物理／生物实现。

### Q10 适用命题：指定观察合同、量子接口与开放边界

供文第七节的一个 $dM_\omega g=0$ 只说明该词与该测试无响应；要称该方向对观察者全部未来记录不可恢复，须量化 Q5 合同内的全部允许词和测试。射线逸出或吸收的描述本身没有建立这个量化，也没有证明宇宙全部信息被删除。数学上的“完整状态”只完整于所选载体；能量、温度、输出数值与 $x,y,z,xy$ 的映射须由具体探测器另行定义。

若借用量子解释，须改用密度算子及其共同线性延拓，总信道为完全正且保迹的映射，输出仪器分支为完全正且迹不增的映射，各分支之和为总信道，保留迹质量与经典输出记录。局部信道输出相同，则施加同一个后续局部信道仍相同；不同密度算子或保留环境不自动给出单次完美判别、可取得的逆映射或物理上实现的恢复。全局幺正／等距、环境可访问性和恢复目标都是额外条件；不把量子术语或 no-hiding 类比当成五态器件实现。

本卷采用的现有开放参考 [FC：输出分辨仪器闭包的固定修订](https://github.com/the-omega-institute/trureturing/blob/60ebb51c87e6496e0cab67c899c3b687ef8fd001/docs/develop/theory/AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)仅用于记录、合法性、测试与有限载体稳定范围的接口说明，不能把它的开放参考身份升级成 Lean 证据。所有“当前／最新”的原句保持叙述者快照归属。尚未提供 AK 核扰动到共同五态 $d$ 的完整实现桥梁，也未提供算术价格的最小坐标重建定理；这两个缺口是关于所引材料的范围结论，不是不可实现性判决。

## 追加锚（本行以下为增补区）

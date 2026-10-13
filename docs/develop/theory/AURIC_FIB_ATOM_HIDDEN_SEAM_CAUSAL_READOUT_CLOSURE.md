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
## 10. 三体接缝、交互次序与最小预测闭包

本章研究一个明确的数学任务：在有序五态系统中，只允许指定的相邻交换，最后读取单点占据的期望，什么线性记录足以预测所有有限动作词？三点构造表明，完整两体边缘相同的混合态仍可被两次相邻接触区分；一般链的答案则取决于是否另外允许各点独立相位动作。准备域是所声明扇区内的全部归一化正半定密度矩阵。

静态五态坐标、已定义的有序交换以及输出分支拉回的方法分别沿用各自来源。本章证明它们在这个准备域和动作菜单下的具体连接。所有角参数均为无量纲实数；动作菜单与准备域是模型的额外规定，不由 Fibonacci 标签或静态仿射关系自行产生。

### 10.1 五标签、底面张量结构与供应接口

**定义 10.1（五态载体与占据）。** 取正交单位基，次序固定为

$$
\Sigma=(0,1,2,3,13),\qquad
\mathcal H=\operatorname{span}_{\mathbb C}\{|s\rangle:s\in\Sigma\},
$$

$$
(x_s,y_s,z_s)=
\begin{cases}
(0,0,0),&s=0,\\
(1,0,0),&s=1,\\
(0,0,1),&s=2,\\
(0,1,0),&s=3,\\
(1,1,0),&s=13.
\end{cases}
$$

$x,y,z$ 依次指低、高、中占据。$s_0$ 对应单位向量 $|0\rangle$，不是零向量。中态 $s_2$ 不属于四个底角。精确的直和分解为

$$
\mathcal H=\mathbb C|2\rangle\oplus\mathcal H_{\rm bot},
\qquad
\mathcal H_{\rm bot}\simeq\mathbb C_x^2\otimes\mathbb C_y^2,
$$

$$
|0\rangle\leftrightarrow|0,0\rangle,\quad
|1\rangle\leftrightarrow|1,0\rangle,\quad
|3\rangle\leftrightarrow|0,1\rangle,\quad
|13\rangle\leftrightarrow|1,1\rangle.
$$

这是四维底面的张量分解；整个五维空间并非两个二态系统的张量积。定义全空间算子

$$
N_x=|1\rangle\langle1|+|13\rangle\langle13|,
\qquad N_y=|3\rangle\langle3|+|13\rangle\langle13|,
$$

$$
N_z=|2\rangle\langle2|,
\qquad R=|1\rangle\langle0|+|13\rangle\langle3|.
$$

$R,R^\dagger$ 均消去 $|2\rangle$；它们只翻转底面低占据，保留高占据。

数学引文与符号对应。[Circulation §24.1][C10-circulation] 的质量—占据矩阵、核方向和五函数基，在本章直接使用为

$$
W=\begin{pmatrix}
1&1&1&1&1\\
0&1&0&0&1\\
0&0&0&1&1\\
0&0&1&0&0
\end{pmatrix},\qquad
\ker_{\mathbb R}W=\mathbb R(1,-1,0,-1,1)^{\mathsf T},
$$

$$
\mathbb R^\Sigma=\operatorname{span}\{1,x,y,z,xy\}.
$$

基础公式的标签 $(0,2,3,5,25)$、隐藏关系的标签 $(O,L,T,R,J)$，均依次对应本章 $(0,1,2,3,13)$；旧标签中的字母 $R$ 不指本章升算子。对概率律，令 $X=\mathbb E x,Y=\mathbb E y,Z=\mathbb E z,\kappa=\mathbb E(xy)$，已有反解为

$$
p=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa).
$$

[Symplectic §35.8][C10-symplectic] 的目标四角系数恰为

$$
J_f=f_0-f_1-f_3+f_{13},
$$

$$
\mathbb E_p f=f_0+(f_1-f_0)X+(f_3-f_0)Y+(f_2-f_0)Z+J_f\kappa.
$$

它说明静态目标对隐藏坐标的依赖；正宽度纤维上 $J_f=0$ 是均值充分性的判据。零宽度纤维没有两点分离的必要性。这里消费该坐标公式，不把它再立为一般核定理。

相位背景采用同一来源的负相位约定

$$
\psi_s=\sqrt{p_s}e^{-i\theta_s},\qquad
\chi=\theta_0-\theta_1-\theta_3+\theta_{13},
$$

$$
\psi_0\psi_{13}\overline{\psi_1}\,\overline{\psi_3}
=\sqrt{p_0p_1p_3p_{13}}e^{-i\chi}.
$$

与正相位记法的精确对应为 $\theta_s^{\rm old}=-\theta_s$、$\Phi^{\rm old}=-\chi$。若任一底角概率为零，使用上式多项式乘积，不给零振幅指定相位。该来源的 $\iota_{X_H}\omega=dH$、$\omega_{\rm red}=d\chi\wedge d\kappa$ 给 $\dot\chi=\partial_\kappa H$、$\dot\kappa=-\partial_\chi H$，所以对角目标有 $\dot\chi=J_f$。

[Symplectic §35.9][C10-symplectic] 另给单份五态振幅上的四次实 Hamilton 函数

$$
H_{\rm int}=2g_0\operatorname{Re}
(\psi_0\psi_{13}\overline{\psi_1}\,\overline{\psi_3})
=2g_0\sqrt{p_0p_1p_3p_{13}}\cos\chi.
$$

这是射影纯态上的非线性动力学背景，不是作用于有序双系统的线性 Hermitian 矩阵。本章下节的 $K$ 精确取自 [Circulation 定理 24.3][C10-circulation] 的 $V$，且 $A_{ab}$ 就是该定理的 $A$。两种载体、两种 Hamilton 对象不得互换。该卷命题 24.7 已给相同独立纯准备时每份能量及初始导数的联系；这种初始联系不使任意链态在每次接触前恢复为相同乘积准备。

### 10.2 完整二十五维上的受控交换

**命题 10.2（既有有序交换的低占据因式分解）。** 在可区分的两个五态因子 $a,b$ 上，使用已定义的

$$
A_{ab}=|0,13\rangle\langle1,3|+|13,0\rangle\langle3,1|,
\qquad K_{ab}=A_{ab}+A_{ab}^\dagger.
$$

下标表示张量位置，并对未写因子张量单位算子。令

$$
B_{ab}=R_aR_b^\dagger+R_a^\dagger R_b,
\qquad G_{ab}=N_{y,a}+N_{y,b}-2N_{y,a}N_{y,b}.
$$

则在整个 $\mathcal H_a\otimes\mathcal H_b$ 上

$$
K_{ab}=B_{ab}G_{ab}=G_{ab}B_{ab}.
$$

它满足

$$
[K_{ab},N_{y,a}]=[K_{ab},N_{y,b}]
=[K_{ab},N_{z,a}]=[K_{ab},N_{z,b}]=0,
$$

$$
[K_{ab},N_{x,a}+N_{x,b}]=0,
\qquad [K_{ab},N_{x,a}]\ne0.
$$

证明。$R$ 的每个非零矩阵元连接高占据相同、中占据均零的两个标签，所以 $R,R^\dagger$ 与 $N_y,N_z$ 交换。故 $B_{ab}$ 与 $G_{ab}$ 交换。

先在十六个底面有序基上检查。$G_{ab}$ 的本征值为 $y_a+y_b-2y_ay_b$：高标签相反时是一，相同时是零。$B_{ab}$ 在 $x_a=x_b$ 时消去该基向量，在 $x_a\ne x_b$ 时交换两个低标签而保持高标签。两种高标签相反的情况逐项为

$$
\begin{array}{c|c|c}
(y_a,y_b)&\text{非零连接}&\text{系数}\\ \hline
(0,1)&|0,13\rangle\longleftrightarrow|1,3\rangle&1\\
(1,0)&|3,1\rangle\longleftrightarrow|13,0\rangle&1
\end{array}
$$

这四个矩阵单位正是 $A_{ab}+A_{ab}^\dagger$，其余底面基向量均被乘积消去。

再检查含中态的九个有序基向量。只要某个因子为 $|2\rangle$，$B_{ab}$ 的两项均因该因子的 $R$ 或 $R^\dagger$ 而为零；$K_{ab}$ 的四个矩阵单位也均为零。不能声称 $G_{ab}$ 自身排除了中态，例如

$$
G_{ab}|2,3\rangle=|2,3\rangle,
\qquad B_{ab}|2,3\rangle=0.
$$

因此中态保护由跃迁因子负责，高占据不相等的条件由 $G_{ab}$ 负责。两者合用才给整个二十五维上的公式，而不只是活动块上的公式。

高、中占据的各自交换关系由上述保标签性得出。又有

$$
[N_x,R]=R,\qquad [N_x,R^\dagger]=-R^\dagger,
$$

故每个 $R_aR_b^\dagger$ 或 $R_a^\dagger R_b$ 与 $N_{x,a}+N_{x,b}$ 交换；$G_{ab}$ 也与此总量交换。个体不守恒的实际作用为

$$
[K_{ab},N_{x,a}]|1,3\rangle=|0,13\rangle\ne0.
$$

证毕。

四角仿射关系只约束总占据相同，没有唯一指定谁携带、谁转移。一个不同的例子是高占据升算子

$$
R_y=|3\rangle\langle0|+|13\rangle\langle1|,
$$

以及

$$
K^{(y)}_{ab}=(R_{y,a}R_{y,b}^\dagger+R_{y,a}^\dagger R_{y,b})
(N_{x,a}+N_{x,b}-2N_{x,a}N_{x,b}).
$$

同样逐底角求值得到 $|0,13\rangle\leftrightarrow|3,1\rangle$ 和 $|1,3\rangle\leftrightarrow|13,0\rangle$；含中态仍由跃迁因子消去。它保留个体 $x$，转移 $y$，因而与 $K_{ab}$ 不同。这足以排除“静态关系唯一决定有序生成元”的推断。

既有 $K_{ab}$ 虽与双因子交换算子对易，也只对任意输入保证总占据守恒。Circulation §24.4 的两个单边缘均值分别保持使用了相同准备与交换对称性。链中的任意相关态不满足这一额外准备前提；同一生成元的对称性不允许在每次接触时重新假设输入对称。

### 10.3 三点八维扇区的实际嵌入

**定义 10.3（交替高标签扇区与动作菜单）。** 在一百二十五维 $\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_C$ 中，固定

$$
(y_A,y_B,y_C)=(0,1,0),\qquad z_A=z_B=z_C=0.
$$

定义局部等距映射

$$
E_A|0\rangle=|0\rangle_A,\quad E_A|1\rangle=|1\rangle_A,
$$

$$
E_B|0\rangle=|3\rangle_B,\quad E_B|1\rangle=|13\rangle_B,
$$

$$
E_C|0\rangle=|0\rangle_C,\quad E_C|1\rangle=|1\rangle_C,
\qquad E=E_A\otimes E_B\otimes E_C.
$$

令 $\mathcal I_3=\operatorname{im}E$。其八个正交基记为 $|abc\rangle$，表示三个低占据，而非原五标签的三个数字。特别地，逻辑 $B=0$ 是物理标签 $3$，逻辑 $B=1$ 是物理标签 $13$。

在逻辑二态空间中重新用

$$
R=|1\rangle\langle0|,\quad L=R^\dagger=|0\rangle\langle1|,
\quad n=|1\rangle\langle1|,\quad Z^{\rm sf}=I-2n
$$

表示限制后的算子。$Z^{\rm sf}$ 是自旋符号算子，不是前节的中占据均值 $Z$，也不是五态的 $N_z$。

**命题 10.4（扇区不变性与交换限制）。** $\mathcal I_3$ 对 $K_{AB},K_{BC}$ 及其任意实参数指数不变，而且

$$
K_{AB}E=Eh_{AB},\qquad K_{BC}E=Eh_{BC},
$$

$$
h_{AB}=R_AL_B+L_AR_B,\qquad
h_{BC}=R_BL_C+L_BR_C.
$$

证明。命题 10.2 的逐点 $N_y,N_z$ 交换关系使它们的共同特征空间不变，该共同空间正是 $\mathcal I_3$。其两条边的高标签都相反，故 $G=I$；又因 $E_j^\dagger R_jE_j=|1\rangle\langle0|$，得上述限制。对幂逐次应用交织式，再对收敛的指数级数求和，得到

$$
e^{-iuK_{AB}}E=Ee^{-iuh_{AB}},\qquad
e^{-ivK_{BC}}E=Ee^{-ivh_{BC}}.
$$

这证明了八维计算在完整五态三复制中的嵌入，而不是仅另外假设一个三比特模型。证毕。

本章另行允许两条边的动作 $e^{-iuh_{AB}}$、$e^{-ivh_{BC}}$ 独立选择任意 $u,v\in\mathbb R$，并允许任意有限次顺序组合。不在这一定义中加入中间测量、输出反馈、任意三点门或独立相位动作。准备集合为

$$
\mathcal D_3=\{\rho\in\operatorname{Herm}(8):\rho\succeq0,
\ \operatorname{Tr}\rho=1\}.
$$

实际五态密度矩阵为 $E\rho E^\dagger$，其余正交方向为零。此域没有纯态、乘积态、Gaussian 态或固定总激发数的限制。生成元保持 $n_A+n_B+n_C$，但守恒并不等于这个初值在所有准备之间相同。

### 10.4 双重交换子产生的三体方向

**命题 10.5（三体接缝及其线性独立性）。** 在 $\mathcal I_3$ 上定义

$$
T=R_AZ^{\rm sf}_BL_C+L_AZ^{\rm sf}_BR_C.
$$

它是 Hermitian 算子，并且

$$
[h_{BC},n_C]=R_BL_C-L_BR_C,
\qquad [h_{AB},[h_{BC},n_C]]=T.
$$

$T$ 的每个单因子偏迹为零，$\operatorname{Tr}T^2=4$，所以它不在所有至多二体算子的线性张成空间中。

证明。二态矩阵的直接乘法给

$$
RL=n,\quad LR=I-n,\quad [L,R]=Z^{\rm sf},
\quad R^2=L^2=0,
$$

$$
[R,n]=-R,\qquad[L,n]=L,
\qquad RZ^{\rm sf}=R,\quad Z^{\rm sf}R=-R,
$$

$$
LZ^{\rm sf}=-L,\qquad Z^{\rm sf}L=L.
$$

异点因子彼此交换。首先只在 $C$ 点使用 $[L,n]=L$、$[R,n]=-R$，得到第一个交换子。再展开第二个交换子，两个含 $R_B^2$ 或 $L_B^2$ 的项为零，其余为

$$
[R_AL_B,R_BL_C]=R_A[L_B,R_B]L_C=R_AZ^{\rm sf}_BL_C,
$$

$$
[L_AR_B,-L_BR_C]=-L_A[R_B,L_B]R_C=L_AZ^{\rm sf}_BR_C.
$$

两项互为伴随，故和为 $T=T^\dagger$。

由于 $\operatorname{Tr}R=\operatorname{Tr}L=\operatorname{Tr}Z^{\rm sf}=0$，对 $A,B,C$ 中任何一个因子取偏迹，$T$ 的两项都给零。令

$$
\mathcal S=\{001,011,100,110\}.
$$

逐基作用为

$$
T|001\rangle=|100\rangle,\quad T|100\rangle=|001\rangle,
$$

$$
T|011\rangle=-|110\rangle,\quad T|110\rangle=-|011\rangle,
$$

且消去其余四个基向量。因此

$$
T^2=\sum_{r\in\mathcal S}|r\rangle\langle r|,
\qquad \operatorname{Tr}T^2=4.
$$

若 $O$ 只支撑于至多两个因子，选不在其支撑中的点 $j$，有

$$
\operatorname{Tr}(TO)=\operatorname{Tr}((\operatorname{Tr}_jT)O)=0.
$$

这里右边的 $O$ 表示删去该单位因子后的算子。同理 $T$ 正交于所有这类算子的和。若 $T$ 自己属于该张成空间，就应有 $\operatorname{Tr}T^2=0$，与四矛盾。这不仅证明 $T\ne0$，还证明它不能由任意二体算子的线性组合代替。证毕。

### 10.5 完整两体边缘相同的混合准备

**命题 10.6（正半定见证及全部两体约化）。** 定义

$$
\rho_\pm=\frac14\sum_{r\in\mathcal S}|r\rangle\langle r|\ \pm\frac14T.
$$

它们属于 $\mathcal D_3$，且

$$
\rho_+-\rho_-=\frac12T,
$$

$$
(\rho_\pm)_{AB}=(\rho_\pm)_{BC}=\frac14I_4,
\qquad
(\rho_\pm)_{AC}=\frac12(|01\rangle\langle01|+|10\rangle\langle10|).
$$

证明。在有序基 $(001,100)$ 上，两个密度矩阵的块为

$$
\frac14\begin{pmatrix}1&\pm1\\\pm1&1\end{pmatrix};
$$

在有序基 $(011,110)$ 上则为

$$
\frac14\begin{pmatrix}1&\mp1\\\mp1&1\end{pmatrix}.
$$

每块分别是向量 $(1,\pm1)$ 或 $(1,\mp1)$ 的外积除以四，故正半定、秩一，非零特征值为 $1/2$。其余四维为零，所以整个谱是两个 $1/2$ 和六个零，迹一。第二块的相反符号来自 $B=1$ 时 $Z_B^{\rm sf}=-1$，不能省略。

对角部分的四个基在 $AB$ 上依次给 $00,01,10,11$，在 $BC$ 上依次给 $01,11,00,10$，权重都是 $1/4$；在 $AC$ 上则两次给 $01$、两次给 $10$。命题 10.5 说明非对角部分 $T$ 的每个单点偏迹均为零，所以以上就是完整约化矩阵，包含所有非对角元的结论，并非只有单点均值相同。

在完整五态物理空间中，任意一对 $j,k$ 的约化恰为

$$
(E\rho_\pm E^\dagger)_{jk}
=(E_j\otimes E_k)(\rho_\pm)_{jk}(E_j\otimes E_k)^\dagger.
$$

这是因为被迹去的局部嵌入满足 $E_\ell^\dagger E_\ell=I_2$。其余二十一维以及与它们的交叉块全为零。因此两个实际二十五维物理边缘也完全相同。证毕。

[Walck–Lyons 的 Main Result][C10-walck] 分类的是在纯态比较类中不能由全部 $(n-1)$ 点边缘确定的纯 $n$ 比特态，得到广义 GHZ 的局部幺正等价类。这里的 $\rho_\pm$ 是秩二混合态；它们的正性、两个活动块和约化式由上述直接证明承担，不是该纯态分类的实例。

### 10.6 两接触读出的精确全实参数公式

定义 Hermitian 流算子

$$
J_{AB}=-i(R_AL_B-L_AR_B),\qquad
J_{BC}=-i(R_BL_C-L_BR_C).
$$

由命题 10.6 的边缘和 $T$ 的块作用得到

$$
\langle n_A\rangle_\pm=\langle n_B\rangle_\pm
=\langle n_C\rangle_\pm=\frac12,
$$

$$
\langle J_{AB}\rangle_\pm=\langle J_{BC}\rangle_\pm=0,
\qquad \langle T\rangle_\pm=\pm1.
$$

前两个流的迹在相应 $I_4/4$ 上为零；最后一个式子使用对角部分与 $T$ 正交及 $\operatorname{Tr}T^2=4$。

**定理 10.7（任意实角的双接触分离）。** 先接触 $AB$，再接触 $BC$，总动作是

$$
W(u,v)=e^{-ivh_{BC}}e^{-iuh_{AB}}.
$$

对每个 $u,v\in\mathbb R$，终端 $C$ 点占据满足

$$
q_C^\pm(u,v)=\operatorname{Tr}(\rho_\pm W^\dagger n_CW)
=\frac12\mp\frac12\sin u\sin2v.
$$

特别地，$u=\pi/2,v=\pi/4$ 时 $q_C^+=0,q_C^-=1$。

证明。两点交换 $h=RL+LR$ 仅在 $|01\rangle,|10\rangle$ 上为 $\sigma_x$，在 $|00\rangle,|11\rangle$ 上为零，故在完整两点空间有

$$
e^{-ith}=I+(\cos t-1)h^2-i\sin t\,h.
$$

例如在 $BC$ 的有序活动基 $(|01\rangle,|10\rangle)$ 上，$n_C=\operatorname{diag}(1,0)$、$J_{BC}=\begin{pmatrix}0&i\\-i&0\end{pmatrix}$，直接相乘得到

$$
e^{iv\sigma_x}\begin{pmatrix}1&0\\0&0\end{pmatrix}e^{-iv\sigma_x}
=\begin{pmatrix}\cos^2v&-i\sin v\cos v\\i\sin v\cos v&\sin^2v\end{pmatrix}.
$$

在 $|00\rangle,|11\rangle$ 上，两边分别给零和一。将同一计算用于 $AB$ 的右端占据 $n_B$，便得到完整算子式

$$
e^{ivh_{BC}}n_Ce^{-ivh_{BC}}
=n_C\cos^2v+n_B\sin^2v-\frac12J_{BC}\sin2v,
$$

$$
e^{iuh_{AB}}n_Be^{-iuh_{AB}}
=n_B\cos^2u+n_A\sin^2u-\frac12J_{AB}\sin2u.
$$

第二式对于一般准备不可删去；只有在本见证上取期望后，它才化为 $1/2$。

为计算跨边流，令 $X=R_AL_B,Y=R_BL_C,F=R_AZ_B^{\rm sf}L_C$。前节乘法规则给

$$
[h_{AB},Y-Y^\dagger]=F+F^\dagger=T,
\qquad [h_{AB},T]=Y-Y^\dagger.
$$

例如后式的两项可分别写成

$$
[h_{AB},F]=(I-n_A)R_BL_C+n_AR_BL_C=Y,
$$

$$
[h_{AB},F^\dagger]=-Y^\dagger.
$$

因此 $i[h_{AB},J_{BC}]=T$、$i[h_{AB},T]=-J_{BC}$。设 $F_1(u)=e^{iuh_{AB}}J_{BC}e^{-iuh_{AB}}$、$F_2(u)=e^{iuh_{AB}}Te^{-iuh_{AB}}$，则

$$
F_1'=F_2,\qquad F_2'=-F_1,
\qquad(F_1(0),F_2(0))=(J_{BC},T).
$$

常系数微分方程的唯一解给出所有实数上的恒等式

$$
e^{iuh_{AB}}J_{BC}e^{-iuh_{AB}}=J_{BC}\cos u+T\sin u.
$$

又因 $n_C$ 与 $h_{AB}$ 交换，完整拉回为

$$
\begin{aligned}
W^\dagger n_CW={}&n_C\cos^2v
+n_B\sin^2v\cos^2u+n_A\sin^2v\sin^2u\\
&-\frac12J_{AB}\sin^2v\sin2u
-\frac12J_{BC}\sin2v\cos u
-\frac12T\sin2v\sin u.
\end{aligned}
$$

这是任意 $\rho\in\mathcal D_3$ 都能取期望的算子等式。代入本节六个初始期望，三个占据系数的和是一，流期望为零，得所述 $q_C^\pm$。所用指数和微分方程恒等式对所有实角成立，不依赖小角近似或有限参数抽样。证毕。

### 10.7 单次任意二点幺正仍不能区分

**命题 10.8（本准备与终端任务的接触次数下界）。** 对物理五态三复制，取任意支撑在至多两个点上的幺正 $U_S$，并在最后任一点 $j$ 读取任意一个占据 $N_{x,j},N_{y,j},N_{z,j}$。则该一次动作不能区别 $E\rho_+E^\dagger$ 与 $E\rho_-E^\dagger$，即使 $U_S$ 将态移出 $\mathcal I_3$。允许本章两条相邻交换时，两次接触可以区别，故在“一次至多二点动作加一次单点终端占据读数”的比较类中，所需接触数恰为二。

证明。若 $j\notin S$，则 $U_S^\dagger N_{a,j}U_S=N_{a,j}$；若 $j\in S$，则该拉回算子仍仅支撑在 $S$。这在完整物理空间中成立，不要求扇区不变。命题 10.6 已证明所有物理至多二点边缘相同，故两种准备对该拉回的迹相同。零次动作当然也相同。命题 10.4 保证定理 10.7 的两次接触是实际物理五态空间内的合法嵌入动作，而其 $0,1$ 终端概率给出区别。证毕。

这个下界固定了准备、允许接触的支撑和终端读口；它没有把任意多点联合测量都放入一次动作，也没有允许以中间测量记录作额外输出。三体信息可经二体动作序列进入单点读口，不要求另设三体原始 Hamiltonian。由于区别需要实际的交互序列，也不能据此推断无交互的超距信号。

### 10.8 七维未来观察空间与完整闭合表

**定义 10.9（开环动作词的未来空间）。** 令 $\mathcal W$ 为独立边动作 $e^{-iuh_{AB}},e^{-ivh_{BC}}$ 的所有有限词，包括空词。终端测试为 $n_A,n_B,n_C$，并保留已知的归一化测试 $I$。定义实线性空间

$$
\mathcal O_3=\operatorname{span}_{\mathbb R}
\{I,W^\dagger n_jW:j\in\{A,B,C\},\ W\in\mathcal W\}
\subseteq\operatorname{Herm}(8).
$$

量子拉回是 [Output-resolved §15][C10-output] 的逐动作拉回方法在此菜单的具体应用：$\mathcal U_W(\rho)=W\rho W^\dagger$，迹的循环性给

$$
\operatorname{Tr}(\mathcal U_W(\rho)F)
=\operatorname{Tr}(\rho\,\mathcal U_W^*(F)),
\qquad\mathcal U_W^*(F)=W^\dagger FW.
$$

若按时间先 $U_1$ 后 $U_2$，则态动作是 $U_2U_1$，拉回是 $U_1^\dagger U_2^\dagger F U_2U_1$。这是实际矩阵与迹配对的对应，不从经典子核自动取得量子操作许可。

**定理 10.10（恰为七维的闭包）。** 有

$$
\mathcal O_3=
\operatorname{span}_{\mathbb R}\{I,n_A,n_B,n_C,J_{AB},J_{BC},T\},
\qquad \dim_{\mathbb R}\mathcal O_3=7.
$$

证明。记 $\mathcal L_A(F)=i[h_{AB},F]$、$\mathcal L_B(F)=i[h_{BC},F]$。两生成元作用在全部七个基元素上的表为

| $F$ | $\mathcal L_A(F)$ | $\mathcal L_B(F)$ |
| --- | --- | --- |
| $I$ | $0$ | $0$ |
| $n_A$ | $J_{AB}$ | $0$ |
| $n_B$ | $-J_{AB}$ | $J_{BC}$ |
| $n_C$ | $0$ | $-J_{BC}$ |
| $J_{AB}$ | $2(n_B-n_A)$ | $-T$ |
| $J_{BC}$ | $T$ | $2(n_C-n_B)$ |
| $T$ | $-J_{BC}$ | $J_{AB}$ |

现给出表中所有类型的计算依据。单位项和远离支撑的占据项交换为零；占据项使用 $[R,n]=-R,[L,n]=L$。对 $X=R_AL_B$，

$$
XX^\dagger=n_A(I-n_B),\qquad
X^\dagger X=(I-n_A)n_B,
$$

$$
i[X+X^\dagger,-i(X-X^\dagger)]
=-2[X,X^\dagger]=2(n_B-n_A).
$$

以 $Y=R_BL_C$ 代替 $X$ 得另一条同边流公式。混边部分由

$$
[X,Y]=F,\quad [X,Y^\dagger]=[X^\dagger,Y]=0,
\quad [X^\dagger,Y^\dagger]=-F^\dagger
$$

得到 $\mathcal L_AJ_{BC}=T$ 以及 $\mathcal L_BJ_{AB}=-T$。最后，命题 10.7 证明中的 $[h_{AB},T]=Y-Y^\dagger$ 给 $\mathcal L_AT=-J_{BC}$。交换 $A,C$ 将 $h_{AB}$ 换成 $h_{BC}$，将 $Y-Y^\dagger$ 换成 $-(X-X^\dagger)$，而 $T$ 保持不变，故 $\mathcal L_BT=J_{AB}$。因此表没有遗漏的生成元作用。

令右边七元素的张成空间为 $V_7$。表说明 $\mathcal L_A V_7\subseteq V_7$、$\mathcal L_B V_7\subseteq V_7$；有限维空间闭合于这两个线性算子的指数。因此 $e^{u\mathcal L_A},e^{v\mathcal L_B}$ 以及任意有限乘积都保持 $V_7$。初始测试属于 $V_7$，给第一个包含 $\mathcal O_3\subseteq V_7$。

反向，轨道张成空间 $\mathcal O_3$ 在任一允许动作的共轭下仍不变：共轭一个词的拉回等于另一个合法词的拉回。它是有限维实向量空间，故拓扑闭。对于 $F\in\mathcal O_3$，差商

$$
\frac{e^{it h_{AB}}Fe^{-it h_{AB}}-F}{t}
$$

都属于 $\mathcal O_3$，其 $t\to0$ 极限 $\mathcal L_AF$ 也属于该空间；另一边同理。从空词的 $n_A,n_C$ 得到 $J_{AB},J_{BC}$，再由 $\mathcal L_AJ_{BC}=T$ 得 $T$。因此 $V_7\subseteq\mathcal O_3$。这个导数论证只用于观察空间的线性闭包；一般链的精确动作可达性将在下文另证。

为证明维数，考虑七元素的一条实线性关系。取 $001\leftrightarrow100$ 的矩阵元，只有 $T$ 非零，故其系数为零；取 $010\leftrightarrow100$，只有 $J_{AB}$ 非零，故其系数为零；取 $001\leftrightarrow010$，只有 $J_{BC}$ 非零，故其系数也为零。剩余对角关系

$$
a_0I+a_An_A+a_Bn_B+a_Cn_C=0
$$

在 $000,100,010,001$ 上依次求值，给 $a_0=a_A=a_B=a_C=0$。七个算子线性独立，维数恰为七。证毕。

若依次排列这七个算子为列 $F$，将表中的系数写成 $\mathcal L_jF_a=\sum_b L^{(j)}_{ab}F_b$，则状态记录 $r_a=\operatorname{Tr}(\rho F_a)$ 经一次动作满足

$$
r'=e^{tL^{(j)}}r.
$$

因为 $r'_a=\operatorname{Tr}(\rho e^{it h_j}F_ae^{-it h_j})$。按时间顺序乘这些实矩阵即可维护所有未来读数。$r_I=1$ 已知，余下六个数是任务的充分线性记录；该更新式不要求重建密度矩阵。

### 10.9 全正准备基点上的六坐标锐下界

**定理 10.11（全密度域的最小线性期望记录）。** 在 $\mathcal D_3$ 上，预测定义 10.9 的全部未来单点占据期望，至少需要六个独立的非归一化实线性期望坐标。定理 10.10 的六坐标记录达到此界。

证明。任意候选记录可写成 $\operatorname{Tr}(\rho F_1),\ldots,\operatorname{Tr}(\rho F_r)$，其中 $F_i$ 为 Hermitian；加入已知归一化，令

$$
V=\operatorname{span}_{\mathbb R}\{I,F_1,\ldots,F_r\}.
$$

即使允许从这些数进行任意非线性后处理，只要两个准备的记录相同，预测也必须相同。若 $\mathcal O_3\not\subseteq V$，其轨道生成集中至少有一个真实未来测试 $F=W^\dagger n_jW$ 不在 $V$，否则整个张成空间已包含于 $V$。

在 Hermitian 实空间上使用 Hilbert–Schmidt 内积 $\langle A,B\rangle=\operatorname{Tr}(AB)$。令 $P_V$ 为正交投影，取

$$
D=F-P_VF.
$$

则 $D\ne0,D=D^\dagger,D\perp V$。由于 $I\in V$，有 $\operatorname{Tr}D=0$，并且

$$
\operatorname{Tr}(DF)=\|D\|_{\rm HS}^2>0.
$$

选 $0<\varepsilon<1/(8\|D\|_{\rm op})$，令

$$
\sigma_\pm=I_8/8\pm\varepsilon D.
$$

任意单位向量 $v$ 满足

$$
\langle v,\sigma_\pm v\rangle
\ge1/8-\varepsilon\|D\|_{\rm op}>0,
$$

故两者正定且迹一，都在完整准备域内。因为 $D\perp V$，它们的所有候选记录相同；但实际未来测试差为

$$
\operatorname{Tr}((\sigma_+-\sigma_-)F)
=2\varepsilon\|D\|_{\rm HS}^2>0.
$$

这与未来充分性矛盾。所以任何充分记录都必须满足 $\mathcal O_3\subseteq V$，从而 $r+1\ge\dim V\ge7$，即 $r\ge6$。反向充分性已由定理 10.10 给出。证毕。

正定基点 $I_8/8$ 是必要的域内工具：若只允许纯态、一个固定激发数扇区或某个特殊准备族，两个微扰未必仍在该族中，不能直接沿用这个下界。例如固定 $n_A+n_B+n_C$ 的值，会使三个占据记录之间多一个已知关系，须重新计算限制后的观察空间及其正性域。

“六个实线性坐标”不是六比特、六个样本、六次仪器操作，也不是一次测量即可精确取得全部数值的承诺。任意实数的集合论编码不在本最小性比较类中。该结论既不主张全态层析，也不提供制备成本或统计精度的资源定理。

### 10.10 接触次序与端点钟读数的不足

**命题 10.12（相同两角、不同次序）。** 两条边的生成元满足

$$
[h_{AB},h_{BC}]=R_AZ_B^{\rm sf}L_C-L_AZ_B^{\rm sf}R_C\ne0.
$$

若反过来先接触 $BC$ 再接触 $AB$，令

$$
\widetilde W(u,v)=e^{-iuh_{AB}}e^{-ivh_{BC}},
$$

则对所有实参数，$\widetilde q_C^+(u,v)=\widetilde q_C^-(u,v)=1/2$。

证明。利用定理 10.10 中的四个混边乘积，

$$
[X+X^\dagger,Y+Y^\dagger]=F-F^\dagger.
$$

它将 $|001\rangle$ 送到 $|100\rangle$，故确实非零。反序中最后的 $AB$ 动作与 $n_C$ 交换，因而

$$
\widetilde W^\dagger n_C\widetilde W
=e^{ivh_{BC}}n_Ce^{-ivh_{BC}}.
$$

输入的 $BC$ 完整边缘是 $I_4/4$，经任意 $BC$ 幺正仍为 $I_4/4$，所以其 $n_C$ 期望为 $1/2$。证毕。

在同一角对 $u=\pi/2,v=\pi/4$，得到

| 接触次序 | $\rho_+$ 的 $C$ 点占据 | $\rho_-$ 的 $C$ 点占据 |
| --- | ---: | ---: |
| 先 $AB$ 后 $BC$ | $0$ | $1$ |
| 先 $BC$ 后 $AB$ | $1/2$ | $1/2$ |

若每条边的单独运行参数由校准速率积分定义，

$$
u=\int g_{AB}(\tau_{AB})\,d\tau_{AB},\qquad
v=\int g_{BC}(\tau_{BC})\,d\tau_{BC},
$$

沿每条边，生成元始终是同一个固定矩阵乘标量，故其单独传播子由积分角决定。但仅给两个积分的最终值没有给出不同边之间的排序；上表证明，相同端点角不决定联合终态，甚至不决定一个终端单点读数。一般交错或同时控制须使用对应时间序列的传播子，不能把两角相加后忘记顺序。

这里未假定任意接触前的两边缘交换对称，也未假定每点 $n_j$ 独自守恒。保持的是总激发数与既定的各点高、中标签。

### 10.11 双参数相容条件与有限事件偏序

**命题 10.13（平坦双参数态势的必要条件）。** 设在原点邻域存在二次连续可微的向量值函数 $\Psi(u,v)$，满足

$$
\partial_u\Psi=-ih_{AB}\Psi,\qquad
\partial_v\Psi=-ih_{BC}\Psi.
$$

则邻域内每一点都必须满足 $[h_{AB},h_{BC}]\Psi(u,v)=0$。若要求这种态势对所有初始向量存在，则必须有算子交换；反之，算子交换时 $e^{-iuh_{AB}-ivh_{BC}}\Psi_0$ 给出这样的势。

证明。交换混合偏导得

$$
\partial_u\partial_v\Psi=-h_{BC}h_{AB}\Psi,
\qquad
\partial_v\partial_u\Psi=-h_{AB}h_{BC}\Psi,
$$

所以交换子在每个点的向量上为零。若允许任意初值，在原点对全部向量成立就强制交换子为零；交换子为零时，指数可拆分且分别微分给两条方程。

只在初始点检查交换子的核并不充分。例如令 $\Psi_0=|010\rangle$，则 $(F-F^\dagger)\Psi_0=0$。但任何候选解沿 $v=0$ 都由第一条常系数方程唯一确定为

$$
\Psi(u,0)=\cos u\,|010\rangle-i\sin u\,|100\rangle.
$$

由于 $(F-F^\dagger)|100\rangle=-|001\rangle$，有

$$
[h_{AB},h_{BC}]\Psi(u,0)=i\sin u\,|001\rangle,
$$

在任意原点邻域内都有非零值。因此该初值虽在初始交换子核中，仍没有满足两条方程的邻域态势。需要的是沿实际轨道的相容性，而非一次核检查。证毕。

这给出顺序依赖的数学障碍，适用对象是指定的控制参数空间和传播子。它没有定义物理空间的曲率，也不构造闭合因果回路。

**命题 10.14（相容事件偏序的顺序无关性）。** 给定有限事件偏序 $(\mathcal E,\preceq)$，每个事件 $e$ 附一个实际幺正动作 $U_e$。假设任何两个不可比事件的实际动作都交换：

$$
e\not\preceq f,\ f\not\preceq e
\quad\Longrightarrow\quad U_eU_f=U_fU_e.
$$

那么所有线性扩展按时间顺序组成的总幺正相同。

证明。先证明线性扩展的相邻交换连接性。取两个线性扩展 $e_1,\ldots,e_N$ 与 $f_1,\ldots,f_N$。在第一个列表中找到 $f_1$。所有位于它之前的事件均与它不可比：若某事件必须在 $f_1$ 之前，第二个列表不可能以 $f_1$ 开始；若必须在其之后，第一个列表已违反偏序。因此可把 $f_1$ 通过逐次相邻不可比交换移到首位，每次交换后仍是线性扩展。删去共同首项，在剩余有限偏序上归纳，得到把一个扩展变为另一个的有限相邻不可比交换序列。

实际总作用按后发生者乘在左侧。每次相邻交换只把某两个相邻因子 $U_eU_f$ 换成 $U_fU_e$；由假设二者相等，其余因子不变，所以总幺正不变。归纳完成。证毕。

不交叠支撑的张量局部动作必交换，故可据此设为不可比。对于交叠且在允许参数范围内可能不交换的事件对，若要偏序保证任意参数的排序无关性，合同必须保留它们的顺序，或另证实际参数下的交换。不能只画一张偏序图就让任意非交换事件保持无定向。同一边同一生成元的指数彼此交换，若合同允许，它们即使支撑重叠也可不可比。这个有限事件结论没有认证一个适用于所有物理过程的共同钟。

### 10.12 一般链的扇区、Jordan–Wigner 符号与二次闭合

**定义 10.15（交替五态链）。** 给整数 $m\ge1$，在 $\mathcal H^{\otimes m}$ 固定所有 $z_j=0$，并选定 $y_j\in\{0,1\}$ 使 $y_j\ne y_{j+1}$。每点保留两个低标签，局部嵌入按定义 10.3 的 $y=0$ 或 $y=1$ 情况选取，得

$$
E_m:(\mathbb C^2)^{\otimes m}\longrightarrow\mathcal H^{\otimes m},
\qquad \mathcal I_m=\operatorname{im}E_m,\qquad\dim\mathcal I_m=2^m.
$$

$m=1$ 时无邻接条件。命题 10.2 在每条边适用，所以各 $K_{j,j+1}$ 保持 $\mathcal I_m$，其限制为

$$
h_j=R_jL_{j+1}+L_jR_{j+1},\qquad 1\le j<m.
$$

所有 $h_j$ 的实参数动作可独立选择。这里的 $m$ 是有序五态复制的点数，不是单个 no-$11$ 长窗口内的位置数。

在逻辑扇区上，令

$$
P_j=\prod_{\ell<j}Z_\ell^{\rm sf},\qquad
c_j=P_jL_j,\qquad c_j^\dagger=P_jR_j.
$$

以下 CAR 和单位算子都仅指 $\mathcal I_m$。若把这些表达式用五态升降算子写在整个 $5^m$ 维空间上，单点反交换子在中态处为零而不是一，故不能声称全空间 CAR。

Jordan–Wigner 变换及二次费米子方法是经典方法。[Pereira–Mueller §II A，式 (1)–(5)][C10-pereira] 的具体约定对应为

$$
a_j=c_j,\quad n_j^{\rm paper}=n_j,\quad
\sigma_j^+=2R_j,\quad \sigma_j^-=2L_j,
\quad \sigma_j^z=2n_j-I=-Z_j^{\rm sf}.
$$

该文 $J(\sigma_j^x\sigma_{j+1}^x+\sigma_j^y\sigma_{j+1}^y)=2Jh_j$，本章的边角等于该单边固定耦合的 $2Jt$。其无穷链均匀演化及特定自旋螺旋准备不在本章的有限独立控制假设内。

本章所需的符号与闭合推导如下。$P_j^2=I$ 且与第 $j$ 点的 $L_j,R_j$ 交换，所以

$$
c_j^2=0,\qquad c_jc_j^\dagger+c_j^\dagger c_j
=L_jR_j+R_jL_j=I.
$$

对于 $a<b$，令 $P_{(a,b)}=\prod_{a<\ell<b}Z_\ell^{\rm sf}$。消去重复前缀得

$$
c_ac_b=L_aZ_a^{\rm sf}P_{(a,b)}L_b
=-L_aP_{(a,b)}L_b,
$$

$$
c_bc_a=Z_a^{\rm sf}L_aP_{(a,b)}L_b
=L_aP_{(a,b)}L_b.
$$

故两者之和为零。将 $L_b$ 换成 $R_b$，同一计算给 $c_ac_b^\dagger+c_b^\dagger c_a=0$。取伴随及交换指标即覆盖所有异点组合。因此

$$
\{c_a,c_b\}=0,\qquad
\{c_a,c_b^\dagger\}=\delta_{ab}I.
$$

端点系数也须计算：利用 $R_aZ_a^{\rm sf}=R_a$，

$$
c_a^\dagger c_b
=R_aZ_a^{\rm sf}P_{(a,b)}L_b
=R_a\left(\prod_{a<\ell<b}Z_\ell^{\rm sf}\right)L_b,
\qquad a<b.
$$

这里没有额外负号；负号只在用 $L_aZ_a^{\rm sf}=-L_a$ 的组合中出现。邻点之间字符串为空，所以

$$
h_j=c_j^\dagger c_{j+1}+c_{j+1}^\dagger c_j.
$$

以外文自旋记号写，一般字符串是

$$
c_a^\dagger c_b
=\frac14\sigma_a^+
\left(\prod_{a<\ell<b}(-\sigma_\ell^z)\right)\sigma_b^-.
$$

Pereira–Mueller 式 (9) 的印刷自旋表达式没有按式 (2)–(4) 展示此 $1/4$ 和每个中点的负号；其式 (11) 的振幅表达式则使用 $|A_{\downarrow}|^2-|A_{\uparrow}|^2$，对应这里的 $Z^{\rm sf}$。因此本章用 CAR 和局部矩阵乘法确定系数，不将式 (9) 的印刷式直接作本章恒等式。其式 (10) 的乘积因子化还依赖该文的无关联初态；这里不使用该准备假设。

对于任意复矩阵 $M\in\mathbb C^{m\times m}$，定义二次算子

$$
Q(M)=\sum_{a,b=1}^mM_{ab}c_a^\dagger c_b.
$$

由 CAR，逐矩阵单位计算

$$
\begin{aligned}
[c_a^\dagger c_b,c_c^\dagger c_d]
={}&\delta_{bc}c_a^\dagger c_d
-\delta_{da}c_c^\dagger c_b\\
&-c_a^\dagger c_c^\dagger c_bc_d
+c_c^\dagger c_a^\dagger c_dc_b.
\end{aligned}
$$

最后一项先交换两个产生算子，再交换两个湮灭算子，得到正的 $c_a^\dagger c_c^\dagger c_bc_d$，恰好抵消前一四次项。因此

$$
[c_a^\dagger c_b,c_c^\dagger c_d]
=\delta_{bc}c_a^\dagger c_d-\delta_{da}c_c^\dagger c_b,
$$

$$
[Q(M),Q(N)]=Q(MN-NM)=Q([M,N]).
$$

这一步对任意 $M,N$ 都成立。$M$ Hermitian 时 $Q(M)$ Hermitian。局部自旋表示中 $c_a^\dagger c_b$ 可支撑整段 $a,\ldots,b$，而在费米子记号中仍是二次项；两种“阶数”不是同一概念。

### 10.13 任意准备的一粒子矩阵与无相位菜单

取任意 $\rho\succeq0,\operatorname{Tr}\rho=1$ 于完整 $\mathcal I_m$，定义

$$
C_{ab}=\operatorname{Tr}(\rho\,c_b^\dagger c_a).
$$

这里 $C_{ab}=\overline{C_{ba}}$，故 $C$ Hermitian。Pereira–Mueller 的 $\rho_{lm}^{\rm paper}=\langle a_l^\dagger a_m\rangle$ 对应 $C_{ml}$，即矩阵指标转置。对于本章的 $Q$，直接展开给

$$
\langle Q(M)\rangle_\rho
=\sum_{a,b}M_{ab}C_{ba}=\operatorname{Tr}(MC).
$$

该指标顺序保证下面的共轭方向。无论准备是否 Gaussian，所有这些式子都只是二次算子的期望恒等式。更具体地，对任意向量 $v$，取 $d_v=\sum_a\overline v_a c_a$，则 $v^\dagger Cv=\langle d_v^\dagger d_v\rangle\ge0$，由 CAR 还得 $\|v\|^2-v^\dagger Cv=\langle d_vd_v^\dagger\rangle\ge0$，所以 $0\preceq C\preceq I_m$。这不宣称 $C$ 决定整个多体态。

令 $E_{ab}$ 为一粒子矩阵单位，$H_j=E_{j,j+1}+E_{j+1,j}$。因 $h_j=Q(H_j)$，CAR 也给

$$
[Q(H_j),c_a]=-\sum_b(H_j)_{ab}c_b.
$$

于是 Heisenberg 方程的唯一解是

$$
e^{iuh_j}c_ae^{-iuh_j}=\sum_b(V_j(u))_{ab}c_b,
\qquad V_j(u)=e^{-iuH_j}.
$$

对 $\rho'=e^{-iuh_j}\rho e^{iuh_j}$，逐指标代入得到

$$
\begin{aligned}
C'_{ab}
&=\sum_{r,s}\overline{(V_j)_{br}}(V_j)_{as}
\operatorname{Tr}(\rho c_r^\dagger c_s)\\
&=\sum_{r,s}(V_j)_{as}C_{sr}\overline{(V_j)_{br}}
=(V_jCV_j^\dagger)_{ab}.
\end{aligned}
$$

因此按时间顺序的有限词在一粒子矩阵上给 $C\mapsto VCV^\dagger$，其中 $V$ 是对应顺序的有限乘积。

**定理 10.16（无局部相位时的精确链闭包）。** 对上述独立相邻交换菜单、全部归一化正半定准备和末端 $n_j$ 期望，令

$$
D=\operatorname{diag}(1,i,i^2,\ldots,i^{m-1}).
$$

则未来观察空间是

$$
\mathcal O_m=
\mathbb RI\ \oplus\
\{Q(DSD^\dagger):S\in\operatorname{Sym}_m(\mathbb R)\},
$$

$$
\dim\mathcal O_m=1+\frac{m(m+1)}2.
$$

因而最小非归一化实线性期望坐标数为 $m(m+1)/2$。

证明。先确定实际有限动作群。逐矩阵元求值得

$$
D^\dagger H_jD=i(E_{j,j+1}-E_{j+1,j}),
$$

$$
D^\dagger V_j(u)D
=O_j(u)=\exp\bigl(u(E_{j,j+1}-E_{j+1,j})\bigr).
$$

$O_j(u)$ 在相邻二维平面上的块为

$$
\begin{pmatrix}\cos u&\sin u\\-\sin u&\cos u\end{pmatrix},
$$

在其余坐标上为单位，故在 $SO(m)$ 中。$D$ 只是一次固定的数学换基；此菜单没有因写下 $D$ 就增加可执行的局部相位动作。

为证明每个 $O\in SO(m)$ 都恰为这些相邻旋转的有限词，使用逐列自下而上的消元。处理列 $k=1,\ldots,m-1$，依次处理相邻行对 $(m-1,m),(m-2,m-1),\ldots,(k,k+1)$。若该列在当前两行的分量为实数 $x,y$，置 $r=\sqrt{x^2+y^2}$。$r>0$ 时，左乘可用旋转

$$
G(x,y)=\begin{pmatrix}x/r&y/r\\-y/r&x/r\end{pmatrix}
$$

将 $(x,y)^{\mathsf T}$ 送到 $(r,0)^{\mathsf T}$；$r=0$ 时取单位。它确是某个 $O_{i-1}(u)$，因为两系数平方和一且允许所有实角。

前 $k-1$ 列若已成为 $e_1,\ldots,e_{k-1}$，行号至少为 $k$ 的这些旋转不会破坏它们。第 $k$ 列与它们正交，故前 $k-1$ 个分量为零，剩余范数为一。自下而上消元后，第 $k$ 个分量是正枢轴 $1$，而非不确定的 $\pm1$。即使该列开始已经只有一个负的第 $k$ 分量，最后一次 $(k,k+1)$ 旋转也以 $x/r=-1,y/r=0$ 把它变成正一。

所有前 $m-1$ 列完成后，正交性使最后一列为 $\pm e_m$。各消元旋转及原矩阵的行列式都是一，因此最后符号必须为正。于是有限个相邻旋转的左积把 $O$ 精确化为 $I$；逆序取逆便给出 $O$ 的有限动作词。这里用的是有限消元，不是仅由 Lie 代数维数推断稠密性。$m=1$ 时 $SO(1)=\{1\}$，无边菜单单独符合此结论。

现在写

$$
\widetilde C=D^\dagger CD=S_\rho+iA_\rho,
\quad S_\rho=\operatorname{Re}\widetilde C\in\operatorname{Sym}_m(\mathbb R),
\quad A_\rho\in\mathfrak{so}(m,\mathbb R).
$$

每个实际词 $V=DOD^\dagger$ 给

$$
S_\rho\longmapsto OS_\rho O^{\mathsf T},
\qquad
\langle n_j\rangle_{W\rho W^\dagger}
=(OS_\rho O^{\mathsf T})_{jj}.
$$

实反对称矩阵 $OA_\rho O^{\mathsf T}$ 的对角元为零，所以它在此菜单与此终端读口下不可见。由迹对偶，终端拉回是

$$
W^\dagger n_jW
=Q(V^\dagger E_{jj}V)
=Q(DO^{\mathsf T}E_{jj}OD^\dagger).
$$

算子等式可直接由 $c_a$ 的共轭式代入验证；因此所有拉回都在所列空间中，给充分包含。

对于 $m\ge2$，$SO(m)$ 在实单位球面上传递。具体地，把任意实单位向量 $v$ 补成正交基；若所得矩阵行列式为负，就翻转一个不承载 $v$ 的基向量。这样得到正定向正交矩阵，且指定行或列为 $v$。已证有限生成性保证这个矩阵来自实际动作词。因此 $O^{\mathsf T}E_{jj}O$ 的轨道包含全部 $vv^{\mathsf T}$。这些投影张成全部实对称矩阵：$v=e_a$ 给 $E_{aa}$，$v=(e_a+e_b)/\sqrt2$ 给

$$
\frac12(E_{aa}+E_{bb}+E_{ab}+E_{ba}),
$$

减去已得对角项即得每个对称非对角矩阵单位。故反向包含也成立。$m=1$ 时唯一测试本身给全部一维实对称空间，不需要球面传递性。

还须排除二次表示的核和归一化冗余。定义逻辑真空与单激发向量

$$
|\Omega\rangle=|0\cdots0\rangle,\qquad
|a\rangle=c_a^\dagger|\Omega\rangle.
$$

它们全都属于固定高、中标签的 $\mathcal I_m$；这里的逻辑真空仍在每个 $y_j=1$ 点有物理高占据。由 CAR，

$$
Q(M)|\Omega\rangle=0,\qquad
Q(M)|b\rangle=\sum_aM_{ab}|a\rangle.
$$

所以 $Q$ 在矩阵空间上单射。若 $\alpha I+Q(M)=0$，先作用于真空得 $\alpha=0$，再作用于全部单激发向量得 $M=0$。故所列直和确为直和，维数为 $1+m(m+1)/2$，没有把可变的总激发数误当归一化。

最后，在 $d=2^m$ 维的全部密度域上重复定理 10.11 的有限维 Hilbert–Schmidt 分离：若候选空间 $V$ 含 $I$ 却不含 $\mathcal O_m$，取真实轨道测试 $F\notin V$ 和 $D_0=F-P_VF$，则 $\operatorname{Tr}D_0=0$，$\operatorname{Tr}(D_0F)>0$。选

$$
0<\varepsilon<\frac1{2^m\|D_0\|_{\rm op}},\qquad
\rho_\pm^{(0)}=\frac{I_{2^m}}{2^m}\pm\varepsilon D_0.
$$

两者正定、迹一、记录相同而未来不同。故任何充分线性记录连同常数必须包含全部 $\mathcal O_m$，至少需要 $m(m+1)/2$ 个非归一化坐标；$S_\rho$ 的这些独立实元素达到下界。证毕。

$m=1$ 时显式地 $\mathcal O_1=\operatorname{span}_{\mathbb R}\{I,n_1\}$，最少一个实数。$n_1$ 的期望可在零与一之间变化，所以它不能由归一化推出。

$m=3$ 时 $D=\operatorname{diag}(1,i,-1)$，$S_\rho=\operatorname{Re}(D^\dagger CD)$ 与前面的六坐标精确对应为

$$
\langle n_A\rangle=S_{11},\quad
\langle n_B\rangle=S_{22},\quad
\langle n_C\rangle=S_{33},
$$

$$
\langle J_{AB}\rangle=2S_{12},\qquad
\langle J_{BC}\rangle=2S_{23},\qquad
\langle T\rangle=-2S_{13}.
$$

例如 $c_1^\dagger c_3=R_AZ_B^{\rm sf}L_C$，故 $\langle T\rangle=C_{31}+C_{13}=2\operatorname{Re}C_{13}$，而 $S_{13}=-\operatorname{Re}C_{13}$。相邻项由 $\langle J_{AB}\rangle=-i(C_{21}-C_{12})$ 与 $S_{12}=\operatorname{Re}(iC_{12})$ 给出。这样三点七维表与一般链公式具有相同的符号及归一化。

### 10.14 加入实际局部相位后的精确有限可达性

**定义 10.17（扩大后的相位菜单）。** 在每条独立边交换之外，另行允许每一点独立的实际动作

$$
e^{-i\theta_jn_j},\qquad\theta_j\in\mathbb R.
$$

这是操作菜单的扩充，不是时钟重命名，也不是上一节数学换基 $D$ 的自动实现。在完整五态空间中，另行声明的 $e^{-i\theta_jN_{x,j}}$ 保持扇区，并满足 $e^{-i\theta_jN_{x,j}}E_m=E_me^{-i\theta_jn_j}$；其一粒子动作是 $e^{-i\theta_jE_{jj}}$。

**定理 10.18（相位菜单的链闭包与锐坐标数）。** 扩大后的菜单在一粒子空间上以有限动作词精确生成 $U(m)$，且

$$
\mathcal O_m^{\rm phase}
=\mathbb RI\ \oplus\ \{Q(M):M\in\operatorname{Herm}(m)\},
$$

$$
\dim_{\mathbb R}\mathcal O_m^{\rm phase}=1+m^2.
$$

在完整 $\mathcal I_m$ 的全部归一化正半定准备上，最少需要 $m^2$ 个非归一化实线性期望坐标。

证明。先给精确有限生成的实际菜单桥。对相邻对 $(j,j+1)$，局部相位允许在该二维块实现 $P=\operatorname{diag}(1,i)$ 及其逆，故由真正的三段动作可实现

$$
P^\dagger e^{-iu\begin{pmatrix}0&1\\1&0\end{pmatrix}}P
=\begin{pmatrix}\cos u&\sin u\\-\sin u&\cos u\end{pmatrix}.
$$

这些是实际可执行的相邻实旋转；也可看出相位共轭把实对称耦合变为 $i(E_{j,j+1}-E_{j+1,j})$，提供第二个耦合象限。下面直接用前一个有限分解，不诉诸 Lie 稠密性。

给任意 $U\in U(m)$，仍逐列、从底行向上使用相邻行对消元。若当前待消的一列在两行上是 $x,y\in\mathbb C$，先左乘两点独立对角相位

$$
P_{x,y}=\operatorname{diag}(e^{-i\arg x},e^{-i\arg y}),
$$

其中零分量的角任取零。它把两分量变成 $|x|,|y|$。若 $r=\sqrt{|x|^2+|y|^2}>0$，再左乘实际可用的实旋转

$$
\begin{pmatrix}|x|/r&|y|/r\\-|y|/r&|x|/r\end{pmatrix}
$$

将它们送到 $(r,0)^{\mathsf T}$；若 $r=0$ 则用单位。所有相位及旋转都只作用在当前相邻两行。

完成前 $k-1$ 列后，这些列为 $e_1,\ldots,e_{k-1}$，而处理第 $k$ 列的行号均至少为 $k$，所以之前的列保持不变。幺正性使当前残余列范数为一；自下而上的消元给第 $k$ 列正枢轴一。完成前 $m-1$ 列后，最后一列必为 $e^{i\phi}e_m$，再用末点相位 $e^{-i\phi E_{mm}}$ 消去。这样有限个独立局部相位和相邻交换的左积把 $U$ 化为单位；逆序取逆仍在菜单中，得到 $U$ 的精确有限词。

$m=1$ 时没有边，独立相位本身已给 $U(1)$。对于所有 $m$，本证明只需要允许任意实角和有限词，不要求单词长度事先有统一预算。它也没有从全多体 $U(2^m)$ 的可控性推出结论：所生成的只是二次数守恒表示的一粒子 $U(m)$ 动作。

由 CAR 共轭公式，任意终端拉回都是 $Q(V^\dagger E_{jj}V)$，故包含于 $Q(\operatorname{Herm}(m))$。反向，$U(m)$ 可把任意单位复向量补入一组标准正交基，所以这些轨道包含所有秩一投影 $vv^\dagger$。它们的实张成是全部 Hermitian 矩阵：除 $v=e_a$ 给出的 $E_{aa}$ 外，取

$$
v_+=\frac{e_a+e_b}{\sqrt2},\qquad
v_i=\frac{e_a+i e_b}{\sqrt2}
$$

分别得到

$$
2v_+v_+^\dagger-E_{aa}-E_{bb}=E_{ab}+E_{ba},
$$

$$
2v_iv_i^\dagger-E_{aa}-E_{bb}=-iE_{ab}+iE_{ba}.
$$

这些矩阵给 $m$ 个实对角方向及每对指标两个实非对角方向，共 $m+2\binom m2=m^2$。因此两侧包含均成立。上一节已用真空与单激发扇区证明 $Q$ 单射且 $I$ 与其像独立，所以维数为 $1+m^2$。

最小性仍在 $I_{2^m}/2^m$ 周围分离。若 $r$ 个候选期望连同 $I$ 的空间不包含本观察空间，选轨道测试 $F$ 的非零正交残差 $D_0$。取 $0<\varepsilon<1/(2^m\|D_0\|_{\rm op})$，密度矩阵 $I_{2^m}/2^m\pm\varepsilon D_0$ 在全部候选记录上相同而在 $F$ 上不同。故 $r+1\ge1+m^2$。整个 Hermitian 一粒子矩阵 $C$ 的 $m^2$ 个实坐标给充分记录，从而达到下界。证毕。

即使 $m=1$，相位动作不改变 $n_1$，所以两种菜单都只需一个坐标。几个明确的链规模为

| 有序五态复制数 $m$ | 固定高、中标签扇区维数 $2^m$ | 仅交换的最小实坐标 | 另有独立局部相位的最小实坐标 |
| ---: | ---: | ---: | ---: |
| $1$ | $2$ | $1$ | $1$ |
| $3$ | $8$ | $6$ | $9$ |
| $5$ | $32$ | $15$ | $25$ |
| $9$ | $512$ | $45$ | $81$ |

这些最小性要求每条边和每一点相位都能独立选择，实角没有精度或总时长预算，并在整扇区上比较全部准备。若只允许均匀耦合、同步角、有限词长、某个固定激发数或受限准备，必须重算轨道空间。即使相位菜单成立，$C$ 仍不确定一般多体态的高阶相关；这里只预测指定的最终占据期望。

### 10.15 单窗静态方向、严格低矩复制下界与仪器边界

九点链的 $\mathcal I_9$ 与单个 no-$11$ 长窗口 $\Gamma_9$ 是不同对象。前者是九个五态复制的交替高标签扇区，全部九个低标签可独立变化，故有 $2^9=512$ 个逻辑基态。后者是一个长度九的二进制词，要求相邻位置不能同时为一；按末位分类，其词数满足 $a_n=a_{n-1}+a_{n-2}$、$a_0=1,a_1=2$，故 $a_9=89$。

在该单窗的经典函数空间中，已有矩基由合法独立子集的占据单项式组成。固定阶数零、一、二的联合矩，所固定的线性方向数为

$$
1+9+\bigl(\tbinom92-8\bigr)=38,
$$

故静态隐藏方向数为 $89-38=51$。这里二阶只计不相邻的位置对；相邻对的占据乘积恒为零。该经典矩基与隐藏方向沿用 [Correlation §23.2][C10-correlation] 的完整矩反演。这里的 $51$ 是完整有符号来源空间的线性核维数；若固定报告纤维含处处正的律，它也是该可行纤维的仿射维数。边界支撑受限时，必须用实际可行支撑重算，不能无条件沿用 $51$。$45,81$ 则是九复制量子链上、两种动作菜单的最小未来实线性期望坐标数。它们与 $51$ 没有可相减或可相等的共同空间：载体、准备、动作、终端测试和所计对象都不同。

数学引文与严格复制合同。[Correlation 定理 26.15、§26.7][C10-correlation] 指定单窗位置集合中含 $k$ 个两两不相邻位置的 $T$，外部总占据为零，且只有支撑在 $T$ 的完整模式。令整数直方图为 $\nu_I\ge0$，$I\subseteq T$，总复制数为 $r=\sum_I\nu_I>0$；这里以 $r$ 表示该来源的 $m$，避免与本章的链长混同。归一化经典律为 $p_I=\nu_I/r$。其联合计数为

$$
M_S(\nu)=\sum_{I\supseteq S}\nu_I,\qquad
M_\varnothing=r.
$$

该定理要求每一步净变化都固定每个真子集 $S\subsetneq T$ 的 $M_S$，并且不借助辅助模式。在这个合同下，非零净变化至少移动 $2^{k-1}$ 份完整模式；正规序产生、湮灭单项式的总 Fock 次数至少为 $2^k$。本章直接消费这一定理，不将它改成关于任意二点空间门的下界。

有两个精确例子显示合同为何不同。第一，取该来源允许的 $T=\{a,b,c\}$（例如长窗口位置 $1,3,5$），其余位置全零。原始两组直方图为

$$
\{\varnothing,ab,ac,bc\},\qquad\{a,b,c,abc\}.
$$

它们各有四份完整模式，每个单点计数为二，每个二点计数为一，顶端计数从零变一。定理给一次严格保留全部真子集计数的交换至少四份、总 Fock 次数八。若改用两步

$$
\{\varnothing,ab,ac,bc\}
\longrightarrow\{\varnothing,a,abc,bc\}
\longrightarrow\{a,b,c,abc\},
$$

第一步把 $ab+ac$ 换成 $a+abc$，第二步把 $\varnothing+bc$ 换成 $b+c$。每步保留三个单点计数，但 $M_{bc}$ 依次为 $1,2,1$；归一化二点矩依次为 $1/4,1/2,1/4$。因此每步只动两份的路线恰好违反了每步严格二阶守恒的前提。这个例子及其计数消费自该来源 §26.7。

第二，本章量子链的三点见证在第一次 $AB$ 接触 $u=\pi/2$ 后，四个对角支撑基变成

$$
\{001,101,010,110\},
$$

各仍重 $1/4$；相位改变不影响这个对角列表。由命题 10.6，输入与这一中间态的低占据二点期望分别为

$$
\langle n_An_C\rangle:\ 0\longmapsto1/4,
\qquad
\langle n_Bn_C\rangle:\ 1/4\longmapsto0.
$$

三单点期望在这个特例中仍全为 $1/2$，但完整两点关系已经改变。流拉回还给中间态 $\langle J_{BC}\rangle_\pm=\pm1$，所以它的两点相干性也不再相同。更一般地，单个准备 $|101\rangle$ 经同一接触变成 $-i|011\rangle$：总低占据均为二，而 $n_A$ 从一变零、$n_B$ 从零变一、$n_An_C$ 从一变零、$n_Bn_C$ 从零变一。

本章固定的是各点高、中标签和总低占据的算子守恒；这些明确改变的低阶跨点读数不满足经典严格复制合同。因此用二体门词读出高支撑信息，与 $2^{k-1}$ 复制及 $2^k$ 次数界没有冲突。经典完整模式的复制、链的五态张量因子以及 CAR 模式的激发数是三种不同计数。

最后，若加入中间仪器或反馈，必须重新定义未来观察空间。设仪器分支为完全正、迹不增的映射 $\mathcal M_{a,o}$，同一动作的分支和保迹。其对偶满足

$$
\operatorname{Tr}(\mathcal M_{a,o}(\rho)F)
=\operatorname{Tr}(\rho\,\mathcal M_{a,o}^*(F)).
$$

对于实际分支记录 $\omega=((a_1,o_1),\ldots,(a_k,o_k))$，带末端效果 $F$ 的联合概率是

$$
\operatorname{Tr}\!\left(
\rho\,\mathcal M_{a_1,o_1}^*\cdots
\mathcal M_{a_k,o_k}^*(F)\right).
$$

因此要从终端测试和 $I$ 出发，对每个分支对偶反复闭合；只对平均通道 $\sum_o\mathcal M_{a,o}$ 闭合会丢掉实际输出。反馈还要求在每个记录前缀上保留公共策略所指定的动作与合法性。条件概率只在分支概率为正时由联合概率相除定义，零概率分支不能强行归一化。

这正对应 [Output-resolved §15 及 Q2、Q4、Q12、Q13][C10-output] 的逐分支、终端、合法性和资源边界。本章已完整证明幺正开环菜单的共轭应用；没有由该方法自动推出扩大仪器菜单仍保留六坐标或 $m^2$ 坐标，也没有由经典读者的合法标签取得量子制备与相位操作。

### 10.16 来源映射与数学适用边界

本章把经典方法用于一个具体有序五态模型：受控交换因式分解、三体混合见证及其精确顺序响应、指定链菜单的观察空间及全准备域最小性，由章内证明相互连接。一般 Jordan–Wigner 方法、CAR 二次闭合、单粒子矩阵演化、Givens 消元及观察空间方法保留其文献归属。

| 来源 | 本章的精确消费 | 不随引用转入的结论 |
| --- | --- | --- |
| [Circulation §§24.1–24.4][C10-circulation] | 标签、$W,d$、负相位；定理 24.3 的 $A,V$ 精确对应 $A_{ab},K_{ab}$ | 相同乘积准备或交换对称输入不作为每次链接触的新假设 |
| [Symplectic §§35.8–35.9][C10-symplectic] | $J_f$ 的目标系数、$\theta^{\rm old}=-\theta$、$\Phi^{\rm old}=-\chi$、非线性四次 Hamilton 背景 | 四次单份流不被识别为有序张量对线性 $K$ |
| [Correlation §23.2、定理 26.15、§26.7][C10-correlation] | 单窗矩基；孤立位置、外部零、每步固定全部真子集计数的复制下界及其实际四份例子 | 不约束允许中间低阶关系变化的任意链协议 |
| [Output-resolved §15 与编者限定][C10-output] | 终端测试经逐分支拉回闭合的原则；本章用迹对偶给出量子应用 | 不直接供应量子操作许可、反馈闭包维数或样本复杂度 |
| [Walck–Lyons，Main Result][C10-walck] | 纯态由全部 $(n-1)$ 点边缘确定性的 GHZ 分类背景 | 不作为秩二混合 $\rho_\pm$ 的正性或两体边缘证明 |
| [Pereira–Mueller，§II A–B、式 (1)–(11)][C10-pereira] | XX/Jordan–Wigner 方法，因子二、$Z^{\rm sf}=-\sigma^z$ 和相关矩阵指标对应 | 不使用其螺旋乘积准备、无穷链极限或式 (9) 的未换算自旋字符串 |
| [D’Alessandro，§2、Theorem 1][C10-observation] | 共轭轨道、交换子稳定空间与 Hilbert–Schmidt 不可分辨方向的方法 | 不把本文的七维或链维数说成其直接定理结论 |
| [Frerix–Bruna，§§2–3][C10-givens] | Givens 二维旋转与有限矩阵分解的经典背景 | 不用低因子数近似或 Lie 稠密性替代本章相邻菜单的精确消元 |
| [Taranto 等，Definition 2、Theorem 4][C10-markov] | 相对于指定记忆仪器的量子 Markov 阶；其条件化历史与未来统计的范围 | 不提供本章线性坐标维数公式，也不把无中间仪器的词任务称为一般 Markov 阶定理 |

D’Alessandro 的 *On Quantum State Observability and Measurement* 在 §2 以 $iS$ 及其反复交换子定义反 Hermitian 观察空间，Theorem 1 将相同受控终端期望与对该空间的迹配对相同联系。本章使用 Hermitian 记法，生成元为 $i[h,\cdot]$，并将多个终端占据和 $I$ 一起纳入。因此本章定理 10.10 的双包含及定理 10.11 的全正基点分离是该方法在明示菜单、明示准备域上的具体计算。

Taranto、Pollock、Milz、Tomamichel、Modi 的 *Quantum Markov Order*（PRL 122, 140401）在 Definition 2 中固定记忆块的仪器族，历史与未来仪器仍任意；其 Theorem 4 排除非 Markov 过程对所有仪器都具有有限 Markov 阶。这是“仪器选择属于任务合同”的背景。它没有把记忆长度、观察空间维数、比特数和末端读数数目等同。

相关书目还包括 Reck、Zeilinger、Bernstein、Bertani，*Experimental realization of any discrete unitary operator*，PRL 73, 58，DOI [10.1103/PhysRevLett.73.58][C10-reck]。此条只作书目背景，不作为本章的定理输入；有限可达性由定理 10.16、10.18 中逐列、相邻、正枢轴的完整构造承担，不作光学器件到本模型的移植。

所有最小性均是“全部所声明归一化正半定准备、所有菜单内有限动作词、最终单点占据期望”这一合同内的实线性坐标最小性。它允许任意非 Gaussian、相关及跨激发数准备，既不假定固定激发数，也不承诺任意准备可免费获得。中间测量、反馈、新增动作、受限角度、资源预算或不同终端测试会改变合同，需要重新闭合和重新分离。

[C10-circulation]: https://github.com/the-omega-institute/trureturing/blob/ed6e098014aa3914eaf3450cde7c07f0dbbab6da/docs/develop/theory/AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS.md
[C10-symplectic]: https://github.com/the-omega-institute/trureturing/blob/9cc2ff145de5d4a6ad7357b22025b00b0557f630/docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md
[C10-correlation]: https://github.com/the-omega-institute/trureturing/blob/f80965d4f7d8cade37c2ae23809730c6c030a2cc/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md
[C10-output]: https://github.com/the-omega-institute/trureturing/blob/9cc2ff145de5d4a6ad7357b22025b00b0557f630/docs/develop/theory/AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md
[C10-walck]: https://arxiv.org/abs/0707.4428v2
[C10-pereira]: https://arxiv.org/html/2110.05972v3
[C10-observation]: https://arxiv.org/abs/quant-ph/0307127
[C10-givens]: https://arxiv.org/abs/1905.05796
[C10-markov]: https://arxiv.org/abs/1805.11341
[C10-reck]: https://doi.org/10.1103/PhysRevLett.73.58

## 追加锚（本行以下为增补区）

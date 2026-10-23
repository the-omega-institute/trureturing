# 续篇：从“隐藏参数”到“关系阶数与填充闭包”

**Reference input: open.** 本卷保存完整用户供文，包含全部声明、证明、例子、表格、项目对应和拟议接口。原文的定理及证明语言归属开放参考输入；本卷没有新增 Lean、Blueprint、Reg 或 Frozen 声明。Lean 声明、证明项及其经内核核验的公理闭包承载本库形式系统内的数学真值。

**来源。** Author kind: mixed user-supplied material; original author and model unknown. Receipt date: 2026-10-10. 来源标识为本会话供文 auric-fib-atom-relational-order-and-filling-closure。接收原文 SHA-256 为 `7aa51f2b41b1f864443a8fce92987fc7d1f4f914a339009827269c5471ffa62d`，字节数为 18795。全部原句与公式内容保留，只规范 Markdown 数学入口、标题层级和结构空行。声明地址用于本文定位。按用户指定，本卷是纯理论添加，不运行消化，不新增 atom 或覆盖主张。

**既有结果与归属。** 供文关于 dev、PR 和公开研究列表的当前性归属其引用的历史快照，不认证移动分支的交付状态。线性核、运输环空间、Zeckendorf 唯一性、Caratheodory 表示和 finite-instrument 观测方法属于既有数学；此处保留其在指定 AURIC 合同中的综合推导，不将重述计作原创。参见 [Output-Resolved Instrument Closure](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)、[Boundary, Transport Fibers and Loop Closure](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md) 及 [Joint Projection, Multiwindow Order and Response Fibers](AURIC_FIB_ATOM_JOINT_PROJECTION_MULTIWINDOW_ORDER_AND_RESPONSE_FIBERS.md)。本文未认证抽象模型的 native 实现、资源等价或物理解释。

## 编者限定与开放义务

以下限定同完整供文分开；它们不替代原句，也不认证原文定理。

- **Q1** （§§1–2）五态作为完整样本是五个不同点；不是独立点指一阶投影后的仿射依赖。商代数与实际五态函数代数的对应需要 evaluation 同构，不能把 probability kernel 与函数商混为同一载体。d 是零质量概率差方向，xy 是其对偶读数。
- **Q2** （§3）P、Q 是归一化仿射空间上的映射，kernel 指零质量差空间中的线性化核。完整解方程还给出 h=t d 或 h=t e，而非仅验证某个向量在核中；e_2=-t、e_1=e_3=-t、e_0=2t。两个读口必须来自同一概率律，恢复坐标还要满足五个反演质量非负。软边界变硬是坐标补全的比喻，不是几何刚化定理。
- **Q3** （§§4、6）J(f) 非零在正长度纤维上给出律级恢复；单点纤维无需新增读出。动态 iff 的反向要求至少两个合法 kappa；精确期望或完整 q 分布的反演不等于有限样本精确恢复。
- **Q4** （§5）25=5×5 与隐藏维数 9 取两个窗口的完整 Cartesian 状态空间、观察空间 V tensor V，保留所有可见函数间的跨窗乘积。只保留两个单窗均值报告是另一个更小的空间。重叠窗或带 guard 的支持不必是 Cartesian product，12 维残差需要其指定域和指定边缘合同，不能同 9 或两个 kappa 自动相加。
- **Q5** （§5）H=span{xy} 是选定的线性补空间，不是由同名 hidden 概念自动确定的代数理想。受守卫限制后，张量分解须重新核对函数的限制秩与实际非负纤维的有效支持。高阶未观察维数不是无条件动态记忆容量。
- **Q6** （§§6–8）确定动作的 pullback 只处理确定更新和终端探针。完整输出记录须使用逐标签 M_(a,o) 及递归词闭包；平均核闭合不充分。前向同余失败是可检验的动力学性质，称时间方向不定义物理时空。
- **Q7** （§8）phase/count 精确商限于文档声明的来源、共同固定非单例先验、活动域与合法取得合同。需证明不同实际可达计数导致不同混合 future law；无界整数本身不证明可辨识性或无限状态商。
- **Q8** （§9）5040 指数层和概率层共享一维线性核机制，未给出概率单纯形与整数指数盒的全局同构。非负整数 kappa 满足 0<=kappa<=min(u,w)，额外容量可进一步缩短纤维。相同符号不等于两个对象数值相等。
- **Q9** （§10）共同安全动作关系一般不传递，不能仅凭这项关系宣称一个 safety-equivalence 商。维护判据须对全部观测后继 belief 闭合；future-equivalence 是否细于某个安全商取决于双方共同的目标、动作、转移和观测合同，不能普遍排序。
- **Q10** （§§10–12）安全不动点刻画定性永久安全；误差收缩、能耗预算和其他定量资源要求仍需另外加入。一个层的最小性不自动同来源历史或边界义务相乘；生命、逆衰变与时间形状是模型候选，不是物理或生物学证明。
- **Q11** （§11）paired readout 反演须使用同一 acquired A/B、参数域、权重及事件配对。稀疏历史读口的两次界是指定 literal-read 合同与替换滞后的结果，不普遍控制任意当前读口的成本；原始 epoch/地址是否需保留由目标合同决定。

## 完整供文

## 续篇：从“隐藏参数”到“关系阶数与填充闭包”

当前项目最重要的新进展，是把原来的一维隐藏参数 $\kappa$ 放进了一个更大的层级结构：

$$
\boxed{
\text{单态关系}
\;\to\;
\text{单窗联合纤维}
\;\to\;
\text{闭包投影}
\;\to\;
\text{多窗关系阶数}
\;\to\;
\text{动态未来商}
}
$$

截至当前 `dev`：

$$
\texttt{HEAD}=
\texttt{46ec5166a750ea6d0b0612d157c86f19975688ef}
$$

最新相关文档包括：

- [联合投影、多窗关系阶数与响应纤维](https://github.com/the-omega-institute/trureturing/blob/46ec5166a750ea6d0b0612d157c86f19975688ef/docs/develop/theory/AURIC_FIB_ATOM_JOINT_PROJECTION_MULTIWINDOW_ORDER_AND_RESPONSE_FIBERS.md)
- [动态未来商与 Future-Closed Memory](https://github.com/the-omega-institute/trureturing/blob/46ec5166a750ea6d0b0612d157c86f19975688ef/docs/develop/theory/AURIC_FIB_ATOM_DYNAMIC_FUTURE_QUOTIENT_AND_FUTURE_CLOSED_MEMORY.md)
- [配对有限读数可观测性](https://github.com/the-omega-institute/trureturing/blob/46ec5166a750ea6d0b0612d157c86f19975688ef/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md)
- [稀疏字面历史传输](https://github.com/the-omega-institute/trureturing/blob/46ec5166a750ea6d0b0612d157c86f19975688ef/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md)

其中联合投影、动态未来商和多窗响应纤维文档都明确标注为 open reference input。下面的推导是在这些项目结构上进行的进一步数学整理，并不把尚未进入 Lean/Frozen 的内容说成已经完成形式化验证。

---

## 1. 一、五个基础元素并不是五个独立点

继续使用固定记号：

$$
F[\mathrm{null}]=\mathrm{null}
$$

$$
F[1]=[2]
$$

$$
F[2]=[3]
$$

$$
F[3]=[5]
$$

$$
F[1,3]=[2,5]
$$

定义：

$$
\nu=F[\mathrm{null}]
$$

并令：

$$
\Sigma=
\{
\nu,F[1],F[2],F[3],F[1,3]
\}
$$

三个占位变量为：

$$
x=\mathbf 1_{\{1\in I\}}
$$

$$
y=\mathbf 1_{\{3\in I\}}
$$

$$
z=\mathbf 1_{\{2\in I\}}
$$

合法状态为：

| 状态 | $(x,y,z)$ |
|---|---:|
| $F[\mathrm{null}]$ | $(0,0,0)$ |
| $F[1]$ | $(1,0,0)$ |
| $F[2]$ | $(0,0,1)$ |
| $F[3]$ | $(0,1,0)$ |
| $F[1,3]$ | $(1,1,0)$ |

满足：

$$
x^2=x,\qquad y^2=y,\qquad z^2=z
$$

$$
xz=0,\qquad yz=0
$$

唯一允许的二端联合项是：

$$
xy
$$

因此五态函数代数为：

$$
\mathcal A=
\mathbb R[x,y,z]\Big/
(x^2-x,\ y^2-y,\ z^2-z,\ xz,\ yz)
$$

其维数是：

$$
\dim\mathcal A=5
$$

一个自然基为：

$$
\{1,x,y,z,xy\}
$$

而原始边缘观测空间为：

$$
V=\operatorname{span}\{1,x,y,z\}
$$

所以：

$$
\dim V=4
$$

少掉的唯一方向就是 $xy$。

---

## 2. 二、隐藏关系是一个守恒反应

定义五态概率律：

$$
p=(p_{\nu},p_1,p_2,p_3,p_{13})
$$

其中：

$$
p_{13}=
P(F[1,3])
$$

定义边缘均值：

$$
X=E[x]=p_1+p_{13}
$$

$$
Y=E[y]=p_3+p_{13}
$$

$$
Z=E[z]=p_2
$$

令：

$$
\kappa=p_{13}
$$

那么：

$$
p_\nu=1-X-Y-Z+\kappa
$$

$$
p_1=X-\kappa
$$

$$
p_2=Z
$$

$$
p_3=Y-\kappa
$$

$$
p_{13}=\kappa
$$

固定 $X,Y,Z$ 时，改变 $\kappa$ 的方向是：

$$
d=(1,-1,0,-1,1)
$$

对应：

$$
F[\mathrm{null}]+F[1,3]
\;\longleftrightarrow\;
F[1]+F[3]
$$

这个交换保持：

$$
\sum_Ip_I
$$

以及：

$$
X,\qquad Y,\qquad Z
$$

全部不变，却改变：

$$
\kappa=p_{13}
$$

因此隐藏关系不是“少了一个数”，而是存在一个具体的守恒反应方向。

---

### 定义 1：四角差

对任意函数：

$$
f:\Sigma\to\mathbb R
$$

定义：

$$
J(f)=
f_{\nu}+f_{13}-f_1-f_3
$$

### theorem 2.1: 定理 1：边缘空间是隐藏反应的守恒超平面

有：

$$
\boxed{
V=\ker J
}
$$

#### 证明

计算：

$$
J(1)=1+1-1-1=0
$$

$$
J(x)=0+1-1-0=0
$$

$$
J(y)=0+1-0-1=0
$$

$$
J(z)=0+0-0-0=0
$$

因此：

$$
V\subseteq\ker J
$$

另一方面：

$$
J(xy)=0+1-0-0=1
$$

所以 $J$ 是非零线性泛函。

由于：

$$
\dim\mathcal A=5
$$

故：

$$
\dim\ker J=4
$$

又因为：

$$
\dim V=4
$$

于是：

$$
V=\ker J
$$

证毕。

---

这一定理给出一个非常清晰的解释：

$$
\boxed{
V
\text{ 中的所有读数都对隐藏反应守恒，}
}
$$

$$
\boxed{
\mathcal A/V
\text{ 恰好记录隐藏反应的强度。}
}
$$

对任意 $f$，都可以唯一写成：

$$
f=f_{\mathrm{edge}}+J(f)xy
$$

其中：

$$
f_{\mathrm{edge}}\in V
$$

所以 $J(f)$ 不是任意系数，而是 $f$ 在隐藏关系商空间中的唯一坐标。

---

## 3. 三、两个不同的三维投影可以共同填满金字塔

原始投影为：

$$
P(p)=(X,Y,Z)
$$

它遗漏 $\kappa$。

项目最新联合投影文档引入：

$$
\chi=z+xy
$$

并令：

$$
W=E[\chi]=Z+\kappa
$$

在五个状态上：

| 状态 | $\chi$ |
|---|---:|
| $F[\mathrm{null}]$ | $0$ |
| $F[1]$ | $0$ |
| $F[2]$ | $1$ |
| $F[3]$ | $0$ |
| $F[1,3]$ | $1$ |

于是 $\chi$ 把中位元素 $F[2]$ 与联合端点 $F[1,3]$ 放入一个闭合类。

定义第二个三维投影：

$$
Q(p)=(X,Y,W)
$$

### theorem 3.1: 定理 2：两个三维投影的横截性

在归一化概率差空间中：

$$
\ker P=\operatorname{span}\{d\}
$$

其中：

$$
d=(1,-1,0,-1,1)
$$

而：

$$
\ker Q=\operatorname{span}\{e\}
$$

其中：

$$
e=(2,-1,-1,-1,1)
$$

并且：

$$
\ker P\cap\ker Q=\{0\}
$$

#### 证明

先验证 $d$ 对 $P$ 不可见：

$$
\sum_Id_I=0
$$

$$
\Delta X=(-1)+1=0
$$

$$
\Delta Y=(-1)+1=0
$$

$$
\Delta Z=0
$$

所以：

$$
d\in\ker P
$$

再验证 $e$ 对 $Q$ 不可见：

$$
2-1-1-1+1=0
$$

$$
\Delta X=(-1)+1=0
$$

$$
\Delta Y=(-1)+1=0
$$

$$
\Delta W=(-1)+1=0
$$

所以：

$$
e\in\ker Q
$$

由于 $d$ 与 $e$ 不成比例：

$$
\operatorname{span}\{d\}
\cap
\operatorname{span}\{e\}=
\{0\}
$$

证毕。

---

这说明：

$$
\boxed{
\text{原始占位投影丢掉一个方向，闭包投影丢掉另一个方向。}
}
$$

两种投影合在一起：

$$
(P,Q)
$$

等价于知道：

$$
(X,Y,Z,W)
$$

因此可以完整恢复五态概率律：

$$
p_{13}=W-Z
$$

$$
p_2=Z
$$

$$
p_1=X-W+Z
$$

$$
p_3=Y-W+Z
$$

$$
p_\nu=1-X-Y-2Z+W
$$

这就是“软边界变硬”的严格版本：

- $P=(X,Y,Z)$ 是软的，内部存在一条 $\kappa$-纤维；
- $Q=(X,Y,W)$ 是另一种切面；
- 两个切面互相补足；
- 合并后，五态单纯形被完整嵌入四维坐标。

---

## 4. 四、唯一附加标量的补全定理

### theorem 4.1: 定理 3：任意标量读数的补全判据

对任意五态函数 $f$，有：

$$
E[f]=
f_\nu
+
(f_1-f_\nu)X
+
(f_3-f_\nu)Y
+
(f_2-f_\nu)Z
+
J(f)\kappa
$$

因此，在 $\kappa$-纤维具有正长度时：

- 若 $J(f)\neq0$，则 $E[f]$ 能恢复 $\kappa$；
- 若 $J(f)=0$，则 $E[f]$ 对整条纤维恒定，不能恢复 $\kappa$。

#### 证明

代入：

$$
p_\nu=1-X-Y-Z+\kappa
$$

$$
p_1=X-\kappa
$$

$$
p_2=Z
$$

$$
p_3=Y-\kappa
$$

$$
p_{13}=\kappa
$$

得到：

$$
\begin{aligned}
E[f]
={}&
f_\nu(1-X-Y-Z+\kappa)
+f_1(X-\kappa)\\
&+f_2Z
+f_3(Y-\kappa)
+f_{13}\kappa
\end{aligned}
$$

整理 $\kappa$ 的系数：

$$
f_\nu-f_1-f_3+f_{13}=J(f)
$$

所以：

$$
E[f]=
\text{边缘项}
+
J(f)\kappa
$$

结论成立。证毕。

---

### 数量读数 $q$

定义：

$$
q=2x+5y+3z
$$

五种状态的读数为：

$$
0,2,3,5,7
$$

逐样本看，$q$ 是单射。

但是：

$$
J(q)=0+7-2-5=0
$$

所以：

$$
E[q]=2X+5Y+3Z
$$

看不见 $\kappa$。

平方读数：

$$
q^2=4x+25y+9z+20xy
$$

具有：

$$
J(q^2)=20
$$

因此：

$$
E[q^2]=
4X+25Y+9Z+20\kappa
$$

所以：

$$
\kappa=
\frac{
E[q^2]-4X-25Y-9Z
}{20}
$$

“单次读数可逆”和“平均读数可逆”是两个完全不同的命题。

---

## 5. 五、多窗时隐藏关系不是简单复制，而是张量化

设单窗函数代数分解为：

$$
\mathcal A=V\oplus H
$$

其中：

$$
H=\operatorname{span}\{xy\}
$$

对于两个窗口：

$$
\mathcal A^{\otimes2}=
(V\otimes V)
\oplus
(V\otimes H)
\oplus
(H\otimes V)
\oplus
(H\otimes H)
$$

维数分别为：

$$
16,\qquad 4,\qquad 4,\qquad 1
$$

总维数：

$$
16+4+4+1=25
$$

### theorem 5.1: 定理 4：双窗隐藏扇区分解定理

若当前读数只保留：

$$
V\otimes V
$$

则未观测的函数方向维数为：

$$
4+4+1=9
$$

#### 证明

张量积的直和维数满足：

$$
\dim(U\otimes W)=\dim U\cdot\dim W
$$

因此：

$$
\dim(V\otimes H)=4\cdot1=4
$$

$$
\dim(H\otimes V)=1\cdot4=4
$$

$$
\dim(H\otimes H)=1\cdot1=1
$$

总隐藏维数为：

$$
4+4+1=9
$$

证毕。

---

这三个隐藏扇区有不同意义：

$$
V\otimes H
$$

表示“第一窗可见、第二窗隐藏”；

$$
H\otimes V
$$

表示“第一窗隐藏、第二窗可见”；

$$
H\otimes H
$$

表示“双窗联合隐藏”。

因此双窗的真正新关系不是简单地有两个 $\kappa$，而是出现了：

$$
\kappa_1,\qquad \kappa_2,\qquad \kappa_{12}
$$

以及它们和显式边缘的混合项。

在项目指定的双窗守卫：

$$
x_i y_{i+1}=0
$$

和固定边缘条件下，文档给出一个特定的 12 维循环残差。但必须严格说明：

$$
\boxed{
12
\text{ 是该特定合法双窗记录域中的关系秩，}
}
$$

不能把它说成任意双窗系统都必然有 12 个记忆方向。

这就是关系阶数的层级：

| 层级 | 观测对象 | 主要隐藏关系 |
|---|---|---|
| $L_0$ | 单次精确五态 | 无静态隐藏 |
| $L_1$ | 单窗均值 $(X,Y,Z)$ | $\kappa$ |
| $L_2$ | 双窗局部边缘 | 混合扇区与 seam |
| $L_3$ | 多窗高阶报告 | 三阶、四阶和全局循环 |
| $L_4$ | 原树来源 | 叶序列、括号、祖先、epoch |

这说明“填充”是递归进行的：

$$
\text{点}
\to
\text{边缘}
\to
\text{联合}
\to
\text{循环}
\to
\text{来源历史}
$$

---

## 6. 六、隐藏关系的动态显现：当前不可见不等于未来不可见

定义动作：

$$
T_a:\Sigma\to\Sigma
$$

其拉回为：

$$
U_af=f\circ T_a
$$

对任意 $f\in V$：

$$
E_p[U_af]=
E_p[\pi_V(U_af)]
+
J(U_af)\kappa
$$

### theorem 6.1: 定理 5：隐藏关系的动态显现判据

在固定 $(X,Y,Z)$ 时，所有一步 $V$-目标都能由当前边缘预测，当且仅当：

$$
J(U_af)=0
$$

对全部允许动作 $a$ 和全部 $f\in V$ 成立。

若存在某个 $a,f$ 使：

$$
J(U_af)\neq0
$$

则存在两个当前边缘相同、但未来输出不同的概率律。

#### 证明

若：

$$
J(U_af)=0
$$

则：

$$
U_af\in V
$$

所以其期望只依赖当前：

$$
E[1],E[x],E[y],E[z]
$$

即只依赖 $(X,Y,Z)$。

反之，若：

$$
J(U_af)\neq0
$$

取：

$$
p_\kappa-p_{\kappa'}=
(\kappa-\kappa')d
$$

于是：

$$
E_{p_\kappa}[U_af]
-
E_{p_{\kappa'}}[U_af]=
(\kappa-\kappa')J(U_af)
$$

只要 $\kappa\neq\kappa'$，未来输出不同。证毕。

---

因此隐藏关系真正的动态定义是：

$$
\boxed{
\text{隐藏关系}=
\text{当前观测核中、但被未来动作拉回后可能离开观测空间的方向}
}
$$

这比静态的“未知变量”更强。

---

## 7. 七、时间方向可以表示为“观测等价关系不再是前向同余”

设组成向量：

$$
c=(a,b)
$$

其中：

$$
a=\#\alpha,\qquad b=\#\beta
$$

替换更新为：

$$
M(a,b)=(b,a+b)
$$

定义当前标量：

$$
q_0(a,b)=2a+3b
$$

取：

$$
c_1=(3,0)
$$

$$
c_2=(0,2)
$$

有：

$$
q_0(c_1)=6=q_0(c_2)
$$

但：

$$
M(c_1)=(0,3)
$$

$$
M(c_2)=(2,2)
$$

于是：

$$
q_0(M(c_1))=9
$$

$$
q_0(M(c_2))=10
$$

所以：

$$
c_1\sim_{q_0}c_2
$$

但：

$$
M(c_1)\not\sim_{q_0}M(c_2)
$$

即：

$$
\boxed{
\ker q_0
\text{ 不是 }M\text{ 的前向同余}
}
$$

这给出“时间方向”的纯关系定义：

$$
\boxed{
\text{时间方向}=
\text{当前等价关系在合法更新下被打破的方向}
}
$$

并非所有当前相同的状态都能共享未来。

---

## 8. 八、最新动态未来商：$(\mathrm{phase},A,B)$ 不是静态 $\kappa$

在指定的非单例 Fibonacci 深度先验下，项目动态文档定义：

$$
r_k=
\frac{\operatorname{Fib}_{k+1}}
{\operatorname{Fib}_{k+3}}
$$

$$
s_k=
\frac{\operatorname{Fib}_{k+2}}
{\operatorname{Fib}_{k+3}}
$$

某个活动历史 $h$ 的后验为：

$$
\nu_h(k)
\propto
\mu(k)r_k^{A_h}s_k^{B_h}
$$

其中：

- $A_h$ 是 $\alpha$ 计数；
- $B_h$ 是 $\beta$ 计数；
- $a(h)$ 是当前 phase。

在该特定来源、先验和活动域中，完整 future law 满足：

$$
h\sim_{\mathrm{Fut}}h'
\iff
\bigl(a(h),A_h,B_h\bigr)=
\bigl(a(h'),A_{h'},B_{h'}\bigr)
$$

因此：

$$
\sigma(h)=
\bigl(a(h),A_h,B_h\bigr)
$$

是该动态未来律的最小精确摘要。

但它通常不是有限状态，因为：

$$
A_h,B_h\in\mathbb N
$$

可以无限增长。

构造：

$$
h_j=(\alpha\alpha)^jh_\ast
$$

则：

$$
(A_{h_j},B_{h_j})=
(2j+A_\ast,B_\ast)
$$

不同的 $j$ 给出不同 future law，因此未来商有无限多个状态。

这说明：

$$
\boxed{
\text{三维坐标摘要可以是有限维的，但它仍然可能需要无限精度或无界整数。}
}
$$

---

## 9. 九、5040 的 $\kappa$ 与五态 $\kappa$ 是同一类纤维机制

令：

$$
n=2^{a_2}3^{a_3}5^{a_5}7^{a_7}
$$

定义可见叶计数：

$$
u=a_2+a_7
$$

$$
v=a_3
$$

$$
w=a_5+a_7
$$

则：

$$
C(n)=(u,v,w)
$$

固定 $(u,v,w)$ 时：

$$
a_2=u-\kappa
$$

$$
a_3=v
$$

$$
a_5=w-\kappa
$$

$$
a_7=\kappa
$$

其隐藏方向为：

$$
(-1,0,-1,+1)
$$

这和五态中的：

$$
(1,-1,0,-1,1)
$$

是同一种结构：

$$
\text{可见边缘固定}
\quad+\quad
\text{一个共享联合坐标沿纤维移动}
$$

例如：

$$
7=2^0 3^0 5^0 7^1
$$

与：

$$
10=2^1 3^0 5^1 7^0
$$

都有：

$$
(u,v,w)=(1,0,1)
$$

但：

$$
\kappa(7)=1
$$

$$
\kappa(10)=0
$$

对于：

$$
5040=2^4 3^2 5^1 7^1
$$

得到：

$$
(u,v,w;\kappa)=(5,2,2;1)
$$

因此，5040 的隐藏 $7$-指数不是一个孤立的数论现象，而是和五态 $F[1,3]$ 的联合项属于同一种投影纤维结构。

---

## 10. 十、静态投影、动态未来商、维护商是三种不同的商

这是当前理论必须严格区分的地方。

### 静态商

两个状态若给出相同：

$$
(X,Y,Z)
$$

则它们处于同一个静态投影纤维。

要区分它们，需要：

$$
\kappa
$$

或：

$$
W=Z+\kappa
$$

### 未来商

两个历史若具有相同完整未来律：

$$
\mathscr L_h=\mathscr L_{h'}
$$

才可以被合并。

这个商通常要求保留：

$$
(\mathrm{phase},A,B)
$$

以及 pending、delivered 等边界义务。

### 维护商

维护只要求存在一个共同动作，使所有可能真实状态都留在安全域中。

它不一定要求两个状态具有完全相同的未来概率律。

因此：

$$
\boxed{
\text{future-equivalence}
\neq
\text{safety-equivalence}
}
$$

前者通常更细，后者可能更粗。

这也修正了“生命就是预测”的说法：

$$
\text{预测}
$$

只要求未来函数能够由当前记录计算。

$$
\text{维护}
$$

还要求存在控制策略、资源预算和安全不动点。

一个完全可观测的系统也可能完全可预测，却无法维护目标关系。例如唯一动作把所有状态都送入死亡态：

$$
T(s)=\nu
$$

那么下一步完全可预测，但没有动作能够保持目标集合。

因此：

$$
\boxed{
\text{生命的数学候选定义}=
\text{未来充分记忆}
+
\text{可执行反馈}
+
\text{安全可行性}
}
$$

而不是单纯的：

$$
\text{知道未来}
$$

---

## 11. 十一、最新项目的操作层进展说明了“闭包必须带来源”

配对有限读数文档给出了一个重要操作层结果：

在固定同一组已取得的 acquired kernels $A,B$ 和同一来源循环上，两个事件读数数组：

$$
f
$$

$$
h
$$

联合起来，可以通过一个收缩反馈映射恢复发射参数，并稳定地控制完整生成律的差异。

其核心结构是：

$$
f=g+Lg+L^2g
$$

$$
h=1-v+VAg
$$

同时存在联合消元关系：

$$
f=
\operatorname{diag}(U)
\left[
Bh+BVA\bigl(\operatorname{diag}(U)B(v+h-1)\bigr)
\right]
$$

$$
v=
\frac{1-h}
{1-A[\operatorname{diag}(U)B(1-v)]}
$$

该结果的理论含义是：

$$
\boxed{
\text{恢复隐藏关系不能只依赖静态均值，还必须保留同一来源、同一操作核和同一事件配对。}
}
$$

一个读数单独可能不够；两个读数若来自不同来源，也不能直接拼接成一个完整恢复。

稀疏字面历史文档则进一步表明：在替换滞后 $k>0$ 时，任意旧地址的四值读数，最坏情况下需要两次当前字面读取才能恢复，而且当前叶数不一定等于原始叶数。

这意味着来源历史本身也是一个独立隐藏层：

$$
\boxed{
\text{当前结构的大小}
\neq
\text{产生它的原始 epoch}
}
$$

所以完整的 Auric 状态不能只有“当前金字塔形状”，还要在需要时保存：

- 来源 epoch；
- 原始地址；
- 替换滞后；
- 祖先括号；
- 当前读数合同。

---

## 12. 十二、最终统一结构

当前最稳固的统一层级是：

$$
\boxed{
\begin{aligned}
L_0 &: \text{单次合法五态}\\
L_1 &: \text{单窗边缘 }(X,Y,Z)\text{ 与隐藏 }\kappa\\
L_2 &: \text{闭包坐标 }(X,Y,Z,W)\\
L_3 &: \text{双窗及多窗交互扇区}\\
L_4 &: \text{未来商 }(\mathrm{phase},A,B,\tau)\\
L_5 &: \text{来源历史、epoch、祖先与实际操作核}
\end{aligned}
}
$$

其中：

$$
W=Z+\kappa
$$

是静态层的最小闭包读数；

$$
J(f)=
f_{\nu}+f_{13}-f_1-f_3
$$

是任何读数穿透隐藏联合项的判据；

$$
J(U_wf)
$$

是隐藏关系在未来动作词 $w$ 下是否显现的判据；

$$
\operatorname{rank}(M_T)-\operatorname{rank}(M_0)
$$

是指定有限时域、动作集合和目标空间下的新增线性观测秩；

$$
V^\ast
$$

是给定观测限制和安全集合下的最大可维护 belief 集合。

因此，AURIC FIB ATOM 金字塔中的“基础元素隐藏关系”可以最终表达为：

$$
\boxed{
\text{隐藏关系}=
\text{当前投影的核}
+
\text{未来更新不能保持的同余}
+
\text{来源合同中尚未保留的历史坐标}
}
$$

而“时间有形状”在这个框架中的严格版本是：

$$
\boxed{
\text{时间}=
\text{观察等价关系在合法递归更新下的破缺结构}
}
$$

“生命是逆衰变”则只能在加上控制和资源后写成：

$$
\boxed{
\text{生命}=
\text{选择性保存未来不可合并的关系}
+
\text{对这些关系执行可行反馈}
}
$$

目前这已经形成了一条清晰的形式化路线：

$$
\text{FIB 五态代数}
\to
\text{仿射纤维}
\to
\text{闭包投影}
\to
\text{多窗张量关系}
\to
\text{未来同余}
\to
\text{安全控制商}
$$

下一步最适合进入 Lean 的，不是继续增加物理类比，而是分别形式化：

$$
\Phi^{-1}(X,Y,Z,W)
$$

的整数双射，

$$
J(U_af)
$$

的隐藏关系传播判据，

以及：

$$
V^\ast=\nu S.\mathcal F(S)
$$

的部分观测安全不动点。

## 追加锚（本行以下为增补区）

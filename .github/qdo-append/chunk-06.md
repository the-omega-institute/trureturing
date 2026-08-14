\boxed{
\ker q_i
}
\]

统一描述。若 \(X=\mathscr H\) 为 Hilbert 空间且 \(q_i=P_i\) 是正交投影到闭子空间 \(S_i\)，则

\[
\boxed{
\ker P_i=S_i^\perp.
}
\]

此时商与余具有规范等距关系：

\[
\boxed{
\mathscr H/S_i^\perp\cong S_i,
\qquad
\mathscr H/S_i\cong S_i^\perp.
}
\]

因此“隐藏”不是向量的绝对属性，而是向量与所选投影之间的关系。

---

## 30.2 绝对整体是相容关系的闭合，而不是超级界面

设观察指标构成有向偏序 \(I\)，并有逆系

\[
(X_i,p_{j,i})_{j\succeq i}.
\]

定义规范观察映射

\[
\boxed{
\Phi:X\to\varprojlim_iX_i,
\qquad
\Phi(x)=(q_i(x))_i.
}
\]

### 定义 30.5（最终不可分关系）

定义

\[
\boxed{
x\sim_\infty y
\iff
q_i(x)=q_i(y)
\quad
\text{对全部 }i.
}
\]

于是

\[
{\sim_\infty}
=
\bigcap_i{\sim_i}.
\]

### 定理 30.6（分离判据）

规范映射 \(\Phi\) 单射，当且仅当

\[
\boxed{
{\sim_\infty}=\Delta_X,
}
\]

其中 \(\Delta_X\) 为对角相等关系。

在线性情形，这等价于

\[
\boxed{
\bigcap_i\ker q_i=\{0\}.
}
\]

#### 证明

\[
\Phi(x)=\Phi(y)
\iff
q_i(x)=q_i(y)\ \forall i
\iff
x\sim_\infty y.
\]

故 \(\Phi\) 单射恰当且仅当最终不可分关系就是相等。线性情形令 \(y=0\) 即得核交判据。 \(\square\)

### 定义 30.7（形式相容与可实现性）

逆极限中的元素是一族形式相容读出

\[
(x_i)_i,
\qquad
p_{j,i}(x_j)=x_i.
\]

若存在 \(x\in X\) 满足

\[
q_i(x)=x_i
\quad
\forall i,
\]

则称该族可实现。

### 定理 30.8（完成判据）

有规范同构

\[
\boxed{
X/{\sim_\infty}
\cong
\operatorname{im}\Phi
\subseteq
\varprojlim_iX_i.
}
\]

并且

\[
\boxed{
X/{\sim_\infty}
\cong
\varprojlim_iX_i
}
\]

当且仅当每个形式相容族均可实现。

#### 证明

\(\ker\Phi={\sim_\infty}\)，故第一同构定理给出第一式。满射性恰等价于所有逆极限点都来自某个整体对象。 \(\square\)

这表明：

\[
\boxed{
\text{绝对整体不是另一个“最大屏幕”，而是全部相对读出之间的可实现相容闭合。}
}
\]

仅有相容性仍可能不够。第 28 节 Hilbert 塔已经给出反例：普通集合逆极限允许能量无界的形式坐标族；真正的 Hilbert 完成还需

\[
\sup_n\|x_n\|<\infty
\]

或等价的平方可和增量条件。因此在不同范畴中，“可实现”分别携带连续性、有界性、可测性、正性或局域性等附加要求。

---

## 30.3 \(\infty\) 的界面定义：无有限终止与可完成性必须分开

设

\[
S_1\subseteq S_2\subseteq\cdots\subseteq\mathscr H
\]

为有限维闭子空间，投影为 \(P_n\)，余空间为

\[
R_n=S_n^\perp.
\]

### 定义 30.9（有限终止）

若存在有限 \(N\) 使

\[
S_N=\mathscr H,
\]

则观察塔有限终止。

### 定义 30.10（逐态完成）

若对每个固定 \(x\in\mathscr H\)，

\[
P_nx\to x,
\]

则称观察塔逐态完成。

### 定义 30.11（一致完成）

若

\[
\|I-P_n\|_{\mathrm{op}}\to0,
\]

则称观察塔一致完成。

### 定理 30.12（无限维中的三者分离）

若 \(\mathscr H\) 无限维，每个 \(S_n\) 有限维，且

\[
\overline{\bigcup_nS_n}=\mathscr H,
\]

则：

1. 观察塔不在任何有限层终止；
2. 观察塔逐态完成；
3. 观察塔不一致完成，且
   \[
   \boxed{
   \|I-P_n\|_{\mathrm{op}}=1
   \quad
   \forall n.
   }
   \]

#### 证明

有限维真子空间不可能等于无限维空间，故第一项成立。递增闭子空间投影强收敛到闭并投影，闭并为全空间，故 \(P_nx\to x\)。对每个 \(n\)，取单位向量 \(r_n\in R_n\)，则

\[
(I-P_n)r_n=r_n,
\]

所以算子范数至少为一；投影补的范数至多为一，故等号成立。 \(\square\)

因此：

\[
\boxed{
\infty
\text{ 可以被刻画为“任何有限界面都留下余量”，}
}
\]

但这不妨碍

\[
\boxed{
\text{所有相容有限界面在逐态意义下完成整体。}
}
\]

“没有有限终止”与“没有完成”是两个不同命题。

---

## 30.4 对角化是相对自描述的闭合缺陷

设 \(A\) 为地址集合，\(Y\) 为值集合，评价器为

\[
e:A\to Y^A.
\]

第 \(a\) 行 \(e(a)\) 是一个 \(A\)-索引对象。设

\[
\tau:Y\to Y
\]

无不动点：

\[
\tau(y)\ne y
\quad
\forall y.
\]

定义对角逃逸对象

\[
\boxed{
d_e(a)=\tau(e(a)(a)).
}
\]

### 定理 30.13（相对对角逃逸）

有

\[
\boxed{
d_e\notin\operatorname{range}(e).
}
\]

#### 证明

若 \(d_e=e(b)\)，则在 \(b\) 坐标

\[
d_e(b)
=
\tau(e(b)(b))
=
\tau(d_e(b)),
\]

与 \(\tau\) 无不动点矛盾。 \(\square\)

这里有一个重要的相对—绝对分层：

\[
\boxed{
d_e\text{ 的具体内容依赖于名单 }e;
}
\]

但

\[
\boxed{
\text{每个同类型名单都存在逃逸对象}
}
\]

是不依赖特定名单的结构定理。

所以对角化不是在一个绝对空间中寻找固定的“外部对象”，而是：

\[
\boxed{
\text{给定一个自描述界面，由该界面自身构造其相对外部。}
}
\]

### 定义 30.14（界面上的对角自然性）

设值界面

\[
q:Y\to Z
\]

及粗层扭曲

\[
\bar\tau:Z\to Z.
\]

若

\[
q\tau=\bar\tau q,
\]

并逐坐标压缩评价表，则对角操作满足

\[
\boxed{
Q\Delta_\tau
=
\Delta_{\bar\tau}P.
}
\]

若不交换，定义缺陷

\[

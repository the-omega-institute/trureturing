
---

# 28. 追加：Hilbert 正交商余塔、有限切片完成与持续逃逸

本节把“在一个已知有限维 Hilbert 空间之外取反，再对余部作商余分类，并持续递归”收紧为类型正确的 Hilbert 空间结构。首先必须修正记号：若 \(H_0\) 只是一个抽象有限维 Hilbert 空间，则表达式
\[
\mathscr H_\infty-H_0
\]
没有定义。必须先给出一个等距线性嵌入
\[
\iota:H_0\hookrightarrow\mathscr H,
\]
并令
\[
M=\iota(H_0)
\subseteq\mathscr H.
\]
真正的“取反”不是集合差，而是闭子空间格中的正交补
\[
M^\perp
=
\{x\in\mathscr H:\langle x,m\rangle=0\ \forall m\in M\},
\]
或者等价地，是正交投影的补
\[
P_M\longmapsto I-P_M.
\]

本节证明五组互相衔接的结论。

1. 对闭子空间，商空间 \(\mathscr H/M\) 与正交余空间 \(M^\perp\) 规范等距同构；
2. 直接重复取正交补只形成二周期，不能产生真正的递归深度；
3. 非平凡递归必须在当前余空间中继续选择有限维切片，形成正交分裂的商余塔；
4. 在无限维空间中，每个有限阶段的余空间仍与原空间同型，但全部有限切片的完成可以重构整个空间；
5. 点态强收敛可以与最坏情形误差恒等于一同时成立，因此任何有限观察层都存在一个完全不可见的正交逃逸方向。

这一结构同时澄清“连续如何产生离散”。Hilbert 向量空间本身仍是连续的；离散性来自所选择的投影族、壳层编号与测量结果，而每个离散壳层内部仍携带实或复的连续振幅。

## 28.1 类型正确的取反：投影补、正交补与商余代表

以下标量域固定为
\[
\mathbb K\in\{\mathbb R,\mathbb C\},
\]
\(\mathscr H\) 为 \(\mathbb K\)-Hilbert 空间。

有限维线性子空间自动闭合，所以有限维 \(M\subseteq\mathscr H\) 存在唯一正交投影
\[
P_M:\mathscr H\to M.
\]
每个 \(x\in\mathscr H\) 唯一分解为
\[
\boxed{
x=P_Mx+(I-P_M)x,
}
\]
其中
\[
P_Mx\in M,
\qquad
(I-P_M)x\in M^\perp.
\]
并且
\[
\boxed{
\|x\|^2
=
\|P_Mx\|^2
+
\|(I-P_M)x\|^2.
}
\]

### 定理 28.1（投影补是子空间取反）

对任意闭子空间 \(M\subseteq\mathscr H\)：
\[
\boxed{
P_{M^\perp}=I-P_M,
}
\]
并有
\[
\boxed{
P_M^2=P_M,
\qquad
P_{M^\perp}^2=P_{M^\perp},
}
\[
\boxed{
P_MP_{M^\perp}=P_{M^\perp}P_M=0,
}
\[
\boxed{
P_M+P_{M^\perp}=I.
}

### 证明

对任意 \(x\)，正交分解
\[
x=P_Mx+(x-P_Mx)
\]
的第二项属于 \(M^\perp\)。因此投影到 \(M^\perp\) 的分量恰为
\[
x-P_Mx=(I-P_M)x.
\]
其余恒等式由互补正交投影直接计算。\(\square\)

### 定理 28.2（商—正交余规范等距同构）

令
\[
q_M:\mathscr H\to\mathscr H/M
\]
为 Banach 商映射。定义
\[
U_M:\mathscr H/M\to M^\perp,
\qquad
U_M(q_M(x))=(I-P_M)x.
\]
则 \(U_M\) 是规范线性等距同构：
\[
\boxed{
\mathscr H/M
\cong_{\mathrm{iso}}
M^\perp.
}
\]

### 证明

若
\[
q_M(x)=q_M(x'),
\]
则 \(x-x'\in M\)，故
\[
(I-P_M)(x-x')=0.
\]
所以 \(U_M\) 良定义。

任意 \(r\in M^\perp\) 满足
\[
U_M(q_M(r))=r,
\]
故满射。若 \(U_M(q_M(x))=0\)，则 \(x=P_Mx\in M\)，所以 \(q_M(x)=0\)，故单射。

最后，商范数满足
\[
\|q_M(x)\|
=
\inf_{m\in M}\|x-m\|.
\]
由正交分解，对任意 \(m\in M\)：
\[
\|x-m\|^2
=
\|P_Mx-m\|^2
+
\|(I-P_M)x\|^2
\ge
\|(I-P_M)x\|^2.
\]
取 \(m=P_Mx\) 达到等号，故
\[
\|q_M(x)\|
=
\|(I-P_M)x\|.
\]
所以 \(U_M\) 等距。\(\square\)

因此“商”和“余”在 Hilbert 空间中不是两个互不相干的操作：
\[
\boxed{
\text{按 }M\text{ 取商}
=
\text{为每个商类选取唯一的正交余代表}.
}
\]

## 28.2 相对正交余、orthomodular 分解与非 Boolean 性

如果
\[
M\subseteq N\subseteq\mathscr H
\]
均为闭子空间，定义 \(M\) 在 \(N\) 中的相对正交余：
\[
\boxed{
N\ominus M
:=
N\cap M^\perp.
}
\]
这才是“从 \(N\) 中扣除已知部分 \(M\)”的类型正确版本。

### 定理 28.3（相对商余分解）

若 \(M\subseteq N\) 为闭子空间，则
\[
\boxed{
N=M\oplus(N\ominus M).
}
并且存在规范等距同构
\[
\boxed{
N/M
\cong_{\mathrm{iso}}
N\ominus M.
}

### 证明

把 \(x\in N\) 按 \(M\) 分解：
\[
x=P_Mx+(I-P_M)x.
\]
由于 \(M\subseteq N\)，第一项属于 \(N\)，所以第二项也属于 \(N\)；同时第二项属于 \(M^\perp\)。故
\[
(I-P_M)x\in N\cap M^\perp=N\ominus M.
\]
唯一性来自正交和。商同构是定理 28.2 限制到 \(N\) 的版本。\(\square\)

该式正是闭子空间格的 orthomodular law：
\[
\boxed{
M\subseteq N
\Longrightarrow
N=M\vee(N\wedge M^\perp).
}
\]
其中
\[
M\wedge N=M\cap N,
\qquad
M\vee N=\overline{M+N}.
\]

### 定理 28.4（正交 De Morgan 公式）

对闭子空间 \(M,N\subseteq\mathscr H\)：
\[
\boxed{
(M\vee N)^\perp
=M^\perp\cap N^\perp,
}
\]
\[
\boxed{
(M\cap N)^\perp
=
\overline{M^\perp+N^\perp}.
}

### 证明

一个向量与 \(M+N\) 中全部向量正交，当且仅当它同时与 \(M\) 和 \(N\) 正交；闭包不改变正交补，得到第一式。对第一式应用双重正交补并交换 \(M,N\) 与其正交补，即得第二式。\(\square\)

正交补虽然具有 involution 与 De Morgan 结构，但闭子空间格一般不是 Boolean 代数，因为分配律失败。

### 例 28.5（二维 Hilbert 格的非分配性）

在
\[
\mathscr H=\mathbb C^2
\]
中取
\[
A=\operatorname{span}(e_1),
\]
\[
B=\operatorname{span}(e_1+e_2),
\qquad
C=\operatorname{span}(e_1-e_2).
\]
因为 \(B\vee C=\mathscr H\)，有
\[
A\wedge(B\vee C)=A.
\]
但三条直线互不相同，所以
\[
A\wedge B=A\wedge C=\{0\},
\]
从而
\[
(A\wedge B)\vee(A\wedge C)=\{0\}.
\]
因此
\[
\boxed{
A\wedge(B\vee C)
\ne
(A\wedge B)\vee(A\wedge C).
}

所以 Hilbert 子空间中的“取反—交—并”不能被无条件当作经典集合的 Boolean 运算。它是 orthomodular，而不是分配的。

## 28.3 直接重复取反只产生二周期

定义闭子空间取反算子
\[
\mathcal C(M)=M^\perp.
\]

### 定理 28.6（双重正交补）

对任意线性子空间 \(M\subseteq\mathscr H\)：
\[
\boxed{
M^{\perp\perp}=\overline M.
}
因此若 \(M\) 闭合，特别是若 \(M\) 有限维，则
\[
\boxed{
\mathcal C^2(M)=M.
}

### 证明

显然 \(M\subseteq M^{\perp\perp}\)，而 \(M^{\perp\perp}\) 闭合，所以
\[
\overline M\subseteq M^{\perp\perp}.
\]
若 \(x\notin\overline M\)，按闭子空间 \(\overline M\) 作正交分解：
\[
x=P_{\overline M}x+r,
\qquad
r\in M^\perp,
\qquad
r\ne0.
\]
则
\[
\langle x,r\rangle
=
\|r\|^2\ne0,
\]
故 \(x\notin M^{\perp\perp}\)。所以反向包含成立。\(\square\)

于是直接迭代为
\[
M,
\quad
M^\perp,
\quad
M,
\quad
M^\perp,
\quad\ldots
\]
只是二周期：
\[
\boxed{
\mathcal C^{2k}(M)=M,
\qquad
\mathcal C^{2k+1}(M)=M^\perp.
}

因此真正有内容的递归不能是“对同一个整体不断再取正交补”。必须在当前余空间内部继续选择一个新切片，并把它加入累计已知空间。

## 28.4 无限吸收：有限切片不改变余空间的 Hilbert 同构类型

Hilbert 维数定义为任一正交规范基的基数。设
\[
\dim_{\mathrm H}\mathscr H=\kappa
\]
为无限基数，而
\[
\dim M=n<\infty.
\]

### 定理 28.7（有限抽取后的余空间维数不变）

有
\[
\boxed{
\dim_{\mathrm H}M^\perp=\kappa.
}
因此
\[
\boxed{
M^\perp\cong_{\mathrm{unitary}}\mathscr H,
}
以及
\[
\boxed{
\mathscr H/M
\cong_{\mathrm{unitary}}\mathscr H.
}

### 证明

由
\[
\mathscr H=M\oplus M^\perp
\]
得到 Hilbert 维数的基数和：
\[
\kappa=n+\dim_{\mathrm H}M^\perp.
\]
若右侧余维有限，则右侧总和有限，与 \(\kappa\) 无限矛盾；若余维无限，则有限基数加无限基数等于该无限基数，所以余维必须为 \(\kappa\)。Hilbert 空间由正交规范基基数分类，故得到酉同构。商同构再由定理 28.2。\(\square\)

在可分无限维情形：
\[
\mathscr H\cong\ell^2(\mathbb N),
\]
对任意有限维 \(M\)：
\[
\boxed{
M^\perp\cong\ell^2(\mathbb N).
}

这给出“无限减去有限仍是无限”的严格含义：它是**抽象 Hilbert 同构类型不变**，而不是集合论差、不是规范恒等，也不表示被抽出的有限部分没有留下结构记录。

若递归只保存
\[
[R_n]_{\cong}
\]
这样的抽象同构类，那么所有有限阶段都会坍缩为同一个值
\[
[\mathscr H].
\]
真正的信息存在于嵌入、投影、商映射及每轮抽出的切片中，而不只存在于余空间对象的同构类型中。

## 28.5 无规范逃逸向量：递归必须携带选择结构

裸 Hilbert 空间在酉群下高度齐性。任意两个同维有限子空间都可由某个酉算子互相送达。因此仅凭 \(\mathscr H\) 本身，没有一个被全体酉对称性保留的首选非零有限切片。

### 定理 28.8（不存在酉自然的正交逃逸选择器）

设 \(\mathscr H\) 无限维。不存在映射
\[
\eta:
\{M\subseteq\mathscr H:M\text{ 为有限维闭子空间}\}
\to
\{x\in\mathscr H:\|x\|=1\}
\]
同时满足：

1. 对每个 \(M\)，
   \[
   \eta(M)\in M^\perp;
   \]
2. 对每个酉算子 \(U\)，
   \[
   \boxed{
   \eta(UM)=U\eta(M).
   }
   \]

### 证明

固定有限维 \(M\)，令
\[
e=\eta(M)\in M^\perp.
\]
取一个酉算子 \(V\)，使它在 \(M\) 上恒等，在 \(e\) 张成的一维空间上取负号，并在其余正交补上恒等。则
\[
VM=M,
\qquad
Ve=-e.
\]
酉自然性要求
\[
e=\eta(M)=\eta(VM)=V\eta(M)=-e,
\]
矛盾。\(\square\)

所以从余空间中“抠出下一个对象”需要额外数据，例如：

- 一组已命名正交规范基；
- 自伴算子的谱投影；
- 一个观察者给出的有限秩投影；
- 一组生成向量及正交化规则；
- 局域性、能量、尺度或复杂度排序；
- 任何明确打破全酉对称性的选择接口。

正交补只给出一个逃逸**空间**，一般不给出一个规范逃逸**向量**。

## 28.6 非平凡递归：有限切片—商—余空间塔

设初始已知空间
\[
S_0=M
\]
为有限维闭子空间，并令
\[
R_0=S_0^\perp.
\]
递归地，已知
\[
\mathscr H=S_n\oplus R_n
\]
后，从当前余空间中选择一个有限维闭子空间
\[
E_{n+1}\subseteq R_n.
\]
定义
\[
\boxed{
S_{n+1}=S_n\oplus E_{n+1},
}
\[
\boxed{
R_{n+1}=R_n\cap E_{n+1}^\perp.
}

### 定理 28.9（单步正交商余递推）

对全部 \(n\ge0\)：
\[
\boxed{
R_{n+1}=S_{n+1}^\perp,
}
\[
\boxed{
R_n=E_{n+1}\oplus R_{n+1},
}
\[
\boxed{
\mathscr H=S_{n+1}\oplus R_{n+1}.
}

### 证明

由
\[
S_{n+1}=S_n\oplus E_{n+1}
\]
及正交 De Morgan：
\[
S_{n+1}^\perp
=S_n^\perp\cap E_{n+1}^\perp
=R_n\cap E_{n+1}^\perp
=R_{n+1}.
\]
又因为 \(E_{n+1}\subseteq R_n\)，在 Hilbert 空间 \(R_n\) 中对闭子空间 \(E_{n+1}\) 作正交分解，得到
\[
R_n=E_{n+1}\oplus(R_n\cap E_{n+1}^\perp).
\]
其余结论代入即得。\(\square\)

### 推论 28.10（有限阶段展开）

对每个 \(n\)：
\[
\boxed{
S_n
=
S_0
\oplus
E_1
\oplus\cdots\oplus
E_n,
}
\[
\boxed{
\mathscr H
=
S_0
\oplus
E_1
\oplus\cdots\oplus
E_n
\oplus
R_n.
}

因此递归的正确形态不是
\[
M\mapsto M^\perp\mapsto M\mapsto M^\perp,
\]
而是
\[
\boxed{
R_n
=
E_{n+1}
\oplus
R_{n+1}.
}
每一步从当前余空间抽取一个有限正交壳层，并把未抽取部分传给下一步。

## 28.7 商余短正合列与 associated graded 重构

定义第 \(n\) 层剩余商：
\[
Q_n=\mathscr H/S_n.
\]
由定理 28.2：
\[
Q_n\cong R_n.
\]
因为 \(S_n\subseteq S_{n+1}\)，存在规范商映射
\[
\rho_n:Q_n\twoheadrightarrow Q_{n+1},
\qquad
\rho_n(x+S_n)=x+S_{n+1}.
\]

### 定理 28.11（一步商余短正合列）

存在正交分裂短正合列
\[
\boxed{
0
\longrightarrow
E_{n+1}
\overset{\jmath_n}{\longrightarrow}
Q_n
\overset{\rho_n}{\longrightarrow}
Q_{n+1}
\longrightarrow
0,
}
其中
\[
\jmath_n(e)=e+S_n.
\]
并且
\[
\boxed{
\ker\rho_n
\cong
S_{n+1}/S_n
\cong
E_{n+1}.
}
在 Hilbert 同构下：
\[
\boxed{
Q_n
\cong
E_{n+1}\oplus Q_{n+1}.
}

### 证明

\(\rho_n\) 显然满射。其核由满足
\[
x\in S_{n+1}
\]
的 \(S_n\)-商类构成，所以
\[
\ker\rho_n=S_{n+1}/S_n.
\]
由
\[
S_{n+1}=S_n\oplus E_{n+1}
\]
得到
\[
S_{n+1}/S_n\cong E_{n+1}.
\]
再用
\[
Q_n\cong R_n=E_{n+1}\oplus R_{n+1}\cong E_{n+1}\oplus Q_{n+1}.
\]
\(\square\)

定义过滤的 associated graded Hilbert 空间：
\[
\operatorname{gr}(S_\bullet)
=
S_0
\oplus_2
\bigoplus_{n\ge0}
(S_{n+1}/S_n),
\]
其中 \(\oplus_2\) 表示平方可和 Hilbert 直和。

由于
\[
S_{n+1}/S_n\cong E_{n+1},
\]
它等距同构于
\[
S_0\oplus_2\bigoplus_{n\ge1}E_n.
\]
这说明递归真正累积的是商层
\[
S_{n+1}/S_n,
\]
而不是每次都与 \(\mathscr H\) 同型的抽象余空间。

## 28.8 无限极限：累计已知空间与最终余空间

定义
\[
\boxed{
S_\infty
=
\overline{\bigcup_{n\ge0}S_n}
=
\overline{
S_0\oplus\bigoplus_{n\ge1}E_n
},
}
\[
\boxed{
R_\infty
=
\bigcap_{n\ge0}R_n.
}

### 定理 28.12（极限商余分解）

有
\[
\boxed{
R_\infty=S_\infty^\perp,
}
并且
\[
\boxed{
\mathscr H=S_\infty\oplus R_\infty.
}

### 证明

若 \(x\in\bigcap_nR_n\)，则它与每个 \(S_n\) 正交，故与
\[
\bigcup_nS_n
\]
及其闭包 \(S_\infty\) 正交。因此
\[
R_\infty\subseteq S_\infty^\perp.
\]
反之，若 \(x\perp S_\infty\)，则 \(x\perp S_n\) 对全部 \(n\) 成立，所以
\[
x\in\bigcap_nS_n^\perp=\bigcap_nR_n.
\]
得到等号。最后对闭子空间 \(S_\infty\) 作正交分解。\(\square\)

### 推论 28.13（递归完备性判据）

下列条件等价：
\[
\boxed{
R_\infty=\{0\},
}
\[
\boxed{
S_\infty=\mathscr H,
}
\[
\boxed{
\overline{
S_0\oplus\bigoplus_{n\ge1}E_n
}
=
\mathscr H.
}

若这些条件成立，则
\[
\boxed{
\mathscr H
\cong
S_0
\oplus_2
\bigoplus_{n\ge1}E_n.
}
若不成立，则完整分解为
\[
\boxed{
\mathscr H
\cong
S_0
\oplus_2
\bigoplus_{n\ge1}E_n
\oplus
R_\infty.
}

所以 \(R_\infty\) 是相对于当前选择规则永远没有被命名的终极余扇区。

## 28.9 一维切片与正交规范基

最小递归每次只选择一个单位向量：
\[
e_{n+1}\in R_n,
\qquad
\|e_{n+1}\|=1,
\]
并令
\[
E_{n+1}=\mathbb K e_{n+1}.
\]
由于
\[
e_{n+1}\perp S_n,
\]
序列 \((e_n)\) 两两正交。

若 \(S_0=\{0\}\) 且 \(R_\infty=0\)，则 \((e_n)\) 是 \(\mathscr H\) 的正交规范基；反过来，任意有序正交规范基都给出这样的完备商余塔。

对每个 \(x\in\mathscr H\)：
\[
\boxed{
x
=
P_{S_0}x
+
\sum_{n\ge1}
\langle x,e_n\rangle e_n
+
P_{R_\infty}x,
}
并有
\[
\boxed{
\|x\|^2
=
\|P_{S_0}x\|^2
+
\sum_{n\ge1}
|\langle x,e_n\rangle|^2
+
\|P_{R_\infty}x\|^2.
}

这里的“离散”是坐标标签
\[
n=1,2,3,\ldots,
\]
而系数
\[
\langle x,e_n\rangle\in\mathbb K
\]
仍是连续振幅。因此：
\[
\boxed{
\text{正交递归产生离散坐标骨架，
不是把 Hilbert 向量变成有限离散集合}.
}

## 28.10 可分与不可分：何时可数递归足够

### 定理 28.14（可数有限切片只产生可分部分）

若每个 \(E_n\) 有限维，则
\[
S_\infty
=
\overline{S_0\oplus\bigoplus_{n\ge1}E_n}
\]
是可分 Hilbert 空间。

因此若 \(\mathscr H\) 不可分，则
\[
\boxed{
R_\infty\ne0
}
对任意可数有限切片递归都成立。

### 证明

每个有限维空间有有限正交规范基；全部切片基的可数并是可数集合，其线性包在 \(S_\infty\) 中稠密。故 \(S_\infty\) 可分。若 \(S_\infty=\mathscr H\)，则 \(\mathscr H\) 可分，矛盾。\(\square\)

对不可分 Hilbert 空间，需要超限递归。

### 定理 28.15（正交基诱导的超限商余塔）

设
\[
\dim_{\mathrm H}\mathscr H=\kappa
\]
为无限基数，并选择以初始序数 \(\kappa\) 编号的正交规范基
\[
(e_\alpha)_{\alpha<\kappa}.
\]
对 \(\alpha\le\kappa\) 定义
\[
S_\alpha
=
\overline{\operatorname{span}}
\{e_\beta:\beta<\alpha\},
\]
\[
R_\alpha=S_\alpha^\perp.
\]
则：

1. 后继阶段
   \[
   \boxed{
   R_\alpha
   =
   \mathbb K e_\alpha
   \oplus
   R_{\alpha+1};
   }
   \]
2. 极限序数 \(\lambda\le\kappa\) 满足
   \[
   \boxed{
   S_\lambda
   =
   \overline{\bigcup_{\alpha<\lambda}S_\alpha},
   \qquad
   R_\lambda
   =
   \bigcap_{\alpha<\lambda}R_\alpha;
   }
   \]
3. 对每个 \(\alpha<\kappa\)：
   \[
   \boxed{
   \dim_{\mathrm H}R_\alpha=\kappa,
   }
   \]
   因而
   \[
   R_\alpha\cong\mathscr H;
   \]
4. 最终
   \[
   \boxed{
   R_\kappa=0.
   }
   \]

### 证明

前两项由基向量集合的分割与正交补定义直接得到。对 \(\alpha<\kappa\)，已抽出的基向量数 \(|\alpha|<\kappa\)；剩余指标集合仍有基数 \(\kappa\)，故余空间 Hilbert 维数为 \(\kappa\)。在阶段 \(\kappa\)，全部基向量已被抽取，其闭线性包为 \(\mathscr H\)，故余空间为零。\(\square\)

这给出一个精确的“无限吸收直到完成”现象：
\[
\boxed{
\text{每个真前阶段的余空间仍与整体同型，
只有完成全部基数长度的递归后余空间才归零}.
}

## 28.11 投影强收敛与持续的最坏情形盲区

令
\[
P_n=P_{S_n},
\qquad
P_\infty=P_{S_\infty}.
\]
因为 \(S_n\) 递增，\((P_n)\) 是递增投影族。

### 定理 28.16（递增投影的强极限）

对每个 \(x\in\mathscr H\)：
\[
\boxed{
P_nx\longrightarrow P_\infty x.
}
特别地，若递归完备，即 \(R_\infty=0\)，则
\[
\boxed{
P_n\xrightarrow{\mathrm{SOT}}I.
}

### 证明

若 \(m>n\)，由于
\[
S_n\subseteq S_m,
\]
向量
\[
P_mx-P_nx
\]
属于 \(S_m\cap S_n^\perp\)，并与 \(P_nx\) 正交。因此
\[
\|P_mx-P_nx\|^2
=
\|P_mx\|^2-
\|P_nx\|^2.
\]
序列 \(\|P_nx\|\) 单调有界，故 \((P_nx)\) Cauchy，收敛到某个 \(y\in S_\infty\)。对任意 \(s\in\bigcup_nS_n\)，充分大 \(n\) 时
\[
\langle x-P_nx,s\rangle=0.
\]
取极限得到 \(x-y\perp S_\infty\)，故 \(y=P_\infty x\)。\(\square\)

### 定理 28.17（有限层的范数一逃逸）

若 \(R_n\ne0\)，则
\[
\boxed{
\|I-P_n\|_{\mathrm{op}}=1.
}
更精确地，存在单位向量
\[
e_n^{\mathrm{esc}}\in R_n
\]
满足
\[
\boxed{
P_ne_n^{\mathrm{esc}}=0,
\qquad
\operatorname{dist}(e_n^{\mathrm{esc}},S_n)=1.
}

### 证明

正交投影补 \(I-P_n\) 的算子范数至多为一。取任意单位向量
\[
e_n^{\mathrm{esc}}\in R_n,
\]
则
\[
(I-P_n)e_n^{\mathrm{esc}}=e_n^{\mathrm{esc}},
\]
故算子范数至少为一。距离公式由正交性得到。\(\square\)

如果递归完备且每个 \(S_n\) 都仍是真子空间，则同时成立：
\[
\forall x\in\mathscr H,
\qquad
\|(I-P_n)x\|\to0,
\]
但
\[
\forall n,
\qquad
\sup_{\|x\|=1}
\|(I-P_n)x\|=1.
\]
所以
\[
\boxed{
\sup_{\|x\|=1}
\lim_{n\to\infty}
\|(I-P_n)x\|
=0,
}
而
\[
\boxed{
\lim_{n\to\infty}
\sup_{\|x\|=1}
\|(I-P_n)x\|
=1.
}

这是一条严格的有限—无限交换失败：

> 对每个预先固定的对象，观察可以越来越完整；但在任意有限阶段，总能在当前余空间中选择一个新的单位对象，使该观察完全失明。

因此强收敛不蕴含算子范数收敛。有限观察的逐对象完备性与全单位球上的统一完备性是两个不同命题。

## 28.12 正交逃逸与 Cantor/Lawvere 对角化的区别

给定有限层 \(S_n\)，正交补提供逃逸集合
\[
\boxed{
\mathfrak E(S_n)
=
\{e\in S_n^\perp:\|e\|=1\}.
}
每个 \(e\in\mathfrak E(S_n)\) 都满足
\[
P_ne=0
\]
及单位距离逃逸。

这与经典对角化具有共同的“逃出当前表示”形态，但不是同一定理：

1. Cantor/Lawvere 对角化从一个评价表的自坐标机械地产生一个指定新对象；
2. 正交逃逸只证明余空间中存在大量候选，通常没有规范唯一选择；
3. Cantor 逃逸依赖无不动点扭曲；正交逃逸依赖内积与闭子空间；
4. Cantor 新对象逐行不同；正交逃逸向量与整个已知线性包同时正交；
5. 正交逃逸边际在单位球上恰为一，是一个几何而非 Hamming 差异。

若加入选择规则
\[
\eta_n(S_n)\in\mathfrak E(S_n),
\]
则可递归定义
\[
S_{n+1}
=S_n\oplus\mathbb K\eta_n(S_n).
\]
但定理 28.8 说明该规则不能同时保持全部酉对称性；它必然编码一个观察者、基、算子或命名偏置。

所以更准确的术语是：
\[
\boxed{
\text{正交逃逸递归},
}
而不是把它直接等同于布尔对角化。

## 28.13 有界能量的 projective completion

有限切片还给出一个自然的有限坐标逆系。对 \(m\ge n\)，定义
\[
p_{m,n}:S_m\to S_n,
\qquad
p_{m,n}=P_{S_n}|_{S_m}.
\]
则
\[
p_{n,n}=\mathrm{id},
\qquad
p_{\ell,n}=p_{m,n}p_{\ell,m}.
\]
定义集合逆极限
\[
\varprojlim S_n
=
\left\{
(x_n)_n:
 x_n\in S_n,
\ p_{m,n}(x_m)=x_n
\ (m\ge n)
\right\}.
\]

普通集合逆极限允许坐标能量无限增长，因此一般比 Hilbert 完成更大。定义有界部分
\[
\boxed{
\varprojlim_{\!b}S_n
=
\left\{
(x_n)\in\varprojlim S_n:
\sup_n\|x_n\|<\infty
\right\}.
}
以范数
\[
\|(x_n)\|_b=\sup_n\|x_n\|.
\]

### 定理 28.18（有界逆极限重构累计完成）

映射
\[
J:S_\infty\to\varprojlim_{\!b}S_n,
\qquad
J(x)=(P_nx)_n
\]
是规范线性等距同构：
\[
\boxed{
S_\infty
\cong_{\mathrm{iso}}
\varprojlim_{\!b}S_n.
}
因此
\[
\boxed{
\mathscr H/R_\infty
\cong_{\mathrm{iso}}
\varprojlim_{\!b}S_n.
}

### 证明

相容性来自
\[
P_nP_m=P_n
\quad(m\ge n).
\]
由定理 28.16，若 \(x\in S_\infty\)，则
\[
P_nx\to x,
\]
所以
\[
\sup_n\|P_nx\|=\|x\|.
\]
故 \(J\) 等距，特别地单射。

现在取有界相容族 \((x_n)\)。定义正交增量
\[
d_0=x_0,
\qquad
d_{n+1}=x_{n+1}-x_n.
\]
由相容性
\[
P_nx_{n+1}=x_n,
\]
所以
\[
d_{n+1}\in S_{n+1}\cap S_n^\perp.
\]
不同增量两两正交，并且
\[
x_n=\sum_{j=0}^{n}d_j,
\]
\[
\|x_n\|^2
=
\sum_{j=0}^{n}\|d_j\|^2.
\]
有界性给出
\[
\sum_{j\ge0}\|d_j\|^2<\infty.
\]
故正交级数
\[
x=\sum_{j\ge0}d_j
\]
在 \(\mathscr H\) 中收敛；其部分和属于 \(S_n\)，所以 \(x\in S_\infty\)。并且
\[
P_nx=x_n.
\]
因此 \(J\) 满射。最后由
\[
\mathscr H/R_\infty\cong S_\infty
\]
得到第二式。\(\square\)

### 例 28.19（相容但无限能量的形式坐标）

取
\[
\mathscr H=\ell^2(\mathbb N),
\qquad
S_n=\operatorname{span}(e_1,\ldots,e_n),
\]
并定义
\[
x_n=e_1+\cdots+e_n.
\]
则
\[
P_nx_{n+1}=x_n,
\]
所以 \((x_n)\) 是普通逆极限中的相容族。但
\[
\|x_n\|=\sqrt n\to\infty,
\]
不存在 \(x\in\ell^2\) 满足
\[
P_nx=x_n
\]
对全部 \(n\) 成立。

因此：
\[
\boxed{
\text{有限坐标相容}
\not\Longrightarrow
\text{存在 Hilbert 向量};
}
还必须加入
\[
\boxed{
\text{统一有界能量／平方可和条件}.
}

这与第 26 节“普通状态逆极限只保留周期核”的结论处理不同对象，但共享一个方法论边界：仅写下形式相容条件，不能自动冒充目标范畴中的完备对象；必须检查该范畴额外要求的有界性、正则性或可实现性。

## 28.14 壳层投影、Born 权重与连续—离散接口

定义壳层投影
\[
P_0=P_{S_0},
\qquad
Q_n=P_{E_n}\quad(n\ge1),
\qquad
Q_\infty=P_{R_\infty}.
\]
这些投影两两正交。定理 28.12 与 28.16 给出强算子意义的分解
\[
\boxed{
P_0+
\sum_{n\ge1}Q_n
+Q_\infty
=I.
}

### 定理 28.20（向量壳层能量分解）

对任意 \(\psi\in\mathscr H\)：
\[
\boxed{
\|\psi\|^2
=
\|P_0\psi\|^2
+
\sum_{n\ge1}\|Q_n\psi\|^2
+
\|Q_\infty\psi\|^2.
}
若 \(\|\psi\|=1\)，则
\[
p_0=\|P_0\psi\|^2,
\qquad
p_n=\|Q_n\psi\|^2,
\qquad
p_\infty=\|Q_\infty\psi\|^2
\]
构成离散概率分布：
\[
\boxed{
p_0+
\sum_{n\ge1}p_n+p_\infty=1.
}

### 证明

有限阶段由 Pythagoras 定理：
\[
\|\psi\|^2
=
\|P_{S_n}\psi\|^2
+
\|P_{R_n}\psi\|^2,
\]
并且
\[
\|P_{S_n}\psi\|^2
=
\|P_0\psi\|^2
+
\sum_{j=1}^{n}\|Q_j\psi\|^2.
\]
令 \(n\to\infty\)，使用
\[
P_{S_n}\psi\to P_{S_\infty}\psi,
\qquad
P_{R_n}\psi\to P_{R_\infty}\psi.
\]
\(\square\)

若 \(\rho\) 为密度算子，定义
\[
p_0=\operatorname{Tr}(\rho P_0),
\qquad
p_n=\operatorname{Tr}(\rho Q_n),
\qquad
p_\infty=\operatorname{Tr}(\rho Q_\infty).
\]
由正性与迹的单调收敛：
\[
\boxed{
p_0+
\sum_{n\ge1}p_n+p_\infty=1.
}

因此商余塔诱导一个投影值离散读出：
\[
\text{“初始已知层”},
\quad
1,2,3,\ldots,
\quad
\text{“最终余层”}.
\]
但离散标签来自投影分解；状态向量、每个壳层与壳层内振幅仍是连续的。不能从壳层概率公式推出 Hilbert 空间本体是有限离散集合。

对于单个有限维 \(M\)，二元投影族
\[
(P_M,I-P_M)
\]
给出最小“已知／余部”测量。对单位向量 \(\psi\)：
\[
\boxed{
\Pr(M)=\|P_M\psi\|^2,
\qquad
\Pr(M^\perp)=\|(I-P_M)\psi\|^2.
}
这正是“取反”在投影测量中的精确概率含义，而不是向量本身被布尔取反。

## 28.15 裸商余塔的酉分类

考虑两套有序正交塔：
\[
\mathscr H
=
S_0
\oplus_2
\bigoplus_{n\ge1}E_n
\oplus R_\infty,
\]
\[
\mathscr H'
=
S_0'
\oplus_2
\bigoplus_{n\ge1}E_n'
\oplus R_\infty'.
\]
称它们塔等价，如果存在酉算子
\[
U:\mathscr H\to\mathscr H'
\]
满足
\[
U(S_0)=S_0',
\qquad
U(E_n)=E_n'\ \forall n,
\qquad
U(R_\infty)=R_\infty'.
\]

### 定理 28.21（裸塔的维数分类）

两套塔等价，当且仅当
\[
\boxed{
\dim S_0=\dim S_0',
}
\[
\boxed{
\dim E_n=\dim E_n'
\quad\forall n,
}
\[
\boxed{
\dim R_\infty=\dim R_\infty'.
}

### 证明

酉算子保持各块 Hilbert 维数，故必要性显然。

反之，按维数相等分别选择酉同构
\[
U_0:S_0\to S_0',
\]
\[
U_n:E_n\to E_n',
\]
\[
U_\infty:R_\infty\to R_\infty'.
\]
其 Hilbert 正交直和
\[
U=U_0\oplus\bigoplus_{n\ge1}U_n\oplus U_\infty
\]
是所需酉同构。\(\square\)

所以在没有任何额外算子、局域结构或语义标签时，商余塔只记录：
\[
\boxed{
\text{每一层抽出了多少 Hilbert 维度}.
}
它不自动记录这些维度“代表什么”。

## 28.16 加入动力学后必须保存块耦合

令
\[
T:\mathscr H\to\mathscr H
\]
为有界线性算子。记正交块为
\[
B_0=S_0,
\qquad
B_n=E_n\ (n\ge1),
\qquad
B_\infty=R_\infty,
\]
投影为 \(P_i\)。完整算子由块矩阵
\[
\boxed{
T_{ij}=P_iTP_j
}
决定。

### 定理 28.22（过滤不变性与三角块结构）

下列条件等价：

1. 对全部有限 \(n\)，
   \[
   T(S_n)\subseteq S_n;
   \]
2. 对全部有限块指标 \(j\) 与所有严格更晚的指标 \(i>j\)，
   \[
   \boxed{
   P_iTP_j=0,
   }
   \]
   并且
   \[
   P_{R_\infty}TP_j=0.
   \]

若每个 \(S_n\) 还是 \(T\) 的 reducing subspace，即同时对 \(T\) 与 \(T^*\) 不变，则每个壳层 \(E_n\) 与 \(R_\infty\) 都 reducing，并且
\[
\boxed{
P_iTP_j=0
\quad(i\ne j).
}
即 \(T\) 对商余塔块对角化。

### 证明

若 \(T(S_j)\subseteq S_j\)，则源于 \(B_j\subseteq S_j\) 的向量不能产生任何位于更晚壳层或最终余空间的分量，得到块消失。

反之，若所有晚向块消失，则每个
\[
S_n=B_0\oplus\cdots\oplus B_n
\]
在 \(T\) 下保持。

若 \(S_n\) 同时对 \(T,T^*\) 不变，则 \(S_n^\perp\) 对 \(T\) 不变。壳层
\[
E_n=S_n\cap S_{n-1}^\perp
\]
是两个 reducing subspace 的交，故 reducing。不同 reducing 正交块之间的块矩阵为零。\(\square\)

因此一旦研究量子动力学、谱算子或观察更新，维数序列不再足够。必须保留
\[
\boxed{
P_iTP_j
}
这些跨层耦合。它们描述：

- 已知层是否向余空间泄漏；
- 余空间是否反向影响已知层；
- 壳层之间是否发生跃迁；
- 过滤是否真正形成闭合有效动力学。

这与本文前面对角自然性审计一致：只保存商空间的对象类型，而不保存算子如何穿过投影，无法判断局部—整体动力学是否交换。

## 28.17 Hilbert 商余塔与观察者完成的接口

把有限观察定义为
\[
q_n:\mathscr H\to S_n,
\qquad
q_n=P_n.
\]
其不可见纤维为
\[
q_n^{-1}(s)=s+R_n.
\]
所以
\[
\ker q_n=R_n.
\]
观察者只能区分商
\[
\mathscr H/R_n
\cong S_n.
\]
随着 \(n\) 增加，核递减：
\[
R_0\supseteq R_1\supseteq\cdots,
\]
可见空间递增：
\[
S_0\subseteq S_1\subseteq\cdots.
\]

这与有限集合上的 Nerode 细化具有共同图式：观察核逐步缩小，可区分类逐步增加。但两者仍有重要区别：

1. 有限集合关系格在有限步后必稳定；无限维 Hilbert 投影塔一般只在极限中强收敛；
2. 有限预测完成的商类数是整数并有 \(|Y|-|O|\) 界；Hilbert 维数可以保持无限不变；
3. Hilbert 有限切片的最坏情形盲区恒为一，尽管逐向量误差趋零；
4. Hilbert 完成需要平方可和／有界能量条件；集合关系完成不携带范数；
5. 若有动力学 \(T\)，必须另外检查过滤不变性或近似半共轭。

因此不能把第 19 节的有限稳定定理原样套到无限维 Hilbert 空间。正确替代是：
\[
\boxed{
\text{关系有限步稳定}
\quad\rightsquigarrow\quad
\text{投影强极限与有界能量完成}.
}

## 28.18 最终统一式

本节得到三种“余”的严格统一。

### 代数商余

\[
\boxed{
\mathscr H/S_n
\cong R_n.
}

### 递归商余

\[
\boxed{
R_n
=E_{n+1}\oplus R_{n+1}.
}

### 完成商余

\[
\boxed{
\mathscr H
=
S_0
\oplus_2
\bigoplus_{n\ge1}E_n
\oplus R_\infty.
}

并且有限坐标完成满足
\[
\boxed{
\mathscr H/R_\infty
\cong
\varprojlim_{\!b}S_n.
}

所以“从无限空间中不断扣除有限对象”的准确结构不是把无限数值逐次做减法，而是：
\[
\boxed{
\text{选择有限闭子空间}
\longrightarrow
\text{正交分裂}
\longrightarrow
\text{记录商层}
\longrightarrow
\text{更新余空间}
\longrightarrow
\text{以平方可和条件完成全部有限坐标}.
}

无限维余空间在每个有限阶段可以与整体同型；递归的历史却保存在 associated graded、投影过滤与跨层算子块中。若把这些结构全部忘掉，只保留“余空间仍是无限维”这一同构类，整个递归便会坍缩成一个无信息固定点。

## 28.19 严格边界

1. \(\mathscr H-H_0\) 不是合法的 Hilbert 空间运算；必须先指定嵌入并使用正交补或商。
2. 直接重复正交补只产生闭包后二周期，不会自动生成无限层级。
3. 每一轮新切片都需要额外选择结构；裸 Hilbert 空间没有酉自然的首选逃逸向量。
4. 有限维切片仍是连续向量空间；离散性来自壳层标签或投影测量结果，而不是有限维本身。
5. \(M^\perp\cong\mathscr H\) 是非规范酉同构，不是子空间相等，也不允许删除嵌入账本。
6. 强算子收敛不等于算子范数收敛；有限层对每个固定向量可渐近完备，同时仍有单位范数的最坏盲区。
7. 普通有限坐标逆极限包含无限能量形式点；Hilbert 重构需要有界范数或平方可和条件。
8. 裸塔的维数分类在加入动力学、局域性或可观测代数后不再完整；必须保存块耦合。
9. 二元投影概率是标准 Hilbert 测量结构，不证明所有物理离散性都来自同一个商余塔。
10. 本节不把正交逃逸等同于 Cantor/Lawvere 对角化，也不从 Hilbert 维数吸收推出 Riemann 假设、光速信息率或意识模型。

## 28.20 形式化状态

定理 28.1—28.22 及例 28.5、28.19 均给出纸面定义与证明，尚未成为 Lean 真源。适合拆分的数学内核包括：

- 闭子空间商与正交补的等距同构；
- 相对正交余与 orthomodular 分解；
- 有限维抽取后的 Hilbert 维数吸收；
- 无酉自然逃逸选择器；
- 正交商余塔的有限阶段与极限分解；
- 递增投影的强收敛及范数一逃逸；
- 有界 inverse limit 与平方可和增量重构；
- 壳层投影的向量／密度算子概率分解；
- 裸塔的块维数分类；
- 过滤不变性与算子块三角／块对角判据。

在获得 kernel proof term、依赖闭包与冻结收据以前，本节不得标记为 `Closed`。

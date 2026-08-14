\boxed{
\varepsilon^\Delta(E)
=
d\bigl(
Q\Delta_\tau E,
\Delta_{\bar\tau}PE
\bigr).
}
\]

这不是“观察改变一切”的模糊命题，而是一个可测的自然性失败。

### 定理 30.15（商可以完全隐藏对角扭曲）

若

\[
q\tau=q,
\]

则

\[
\boxed{
Q\Delta_\tau(E)
=
QD(E)
}
\]

对所有评价表成立。

#### 证明

逐坐标：

\[
q(\tau(E(a,a)))
=
q(E(a,a)).
\]

\(\square\)

所以一个界面可以得到零自然性缺陷，却完全失去扭曲可见性。这再次证明：

\[
\boxed{
\text{操作交换}
\ne
\text{操作被忠实观察}.
}
\]

需要同时审计分离量

\[
\operatorname{sep}_\tau(q)
=
\inf_{y\notin\operatorname{Fix}\tau}
d(qy,q\tau y).
\]

---

## 30.5 相对性不是任意性：自然变换与不变量

考虑两个界面

\[
q_i:X\to X_i,
\qquad
q_j:X\to X_j
\]

以及转换

\[
p_{j,i}:X_j\to X_i.
\]

若整体动力学为

\[
T:X\to X,
\]

有效动力学为

\[
T_i:X_i\to X_i,
\]

则严格协变条件是

\[
\boxed{
q_iT=T_iq_i.
}
\]

若 \(j\succeq i\)，还要求

\[
\boxed{
p_{j,i}T_j=T_ip_{j,i}.
}
\]

这些交换图保证不同观察者不是各自任意发明规律，而是在重叠可见部分上给出一致描述。

若只近似交换，可定义

\[
\boxed{
\delta_i(T)
=
\sup_{x\in K}
d_i(q_iTx,T_iq_ix)
}
\]

于指定有界状态集 \(K\)。对连续的多尺度链，缺陷按 Lipschitz 常数满足 telescoping bound，这正是本文第 2 节一般缺陷复合定理的观察者版本。

因此一个严格相对理论至少必须同时给出：

\[
\boxed{
\text{界面}
+
\text{界面转换}
+
\text{协变规律}
+
\text{转换不变量}
+
\text{非协变缺陷}.
}
\]

缺少界面转换的“每人有自己的真理”不是数学相对性，而只是不可比较的多重命名。

---

## 30.6 概率是状态—effect 配对，不是投影对象本身

令 \(\mathcal A\) 为含幺 \(C^*\)-代数。一个状态是正的归一化线性泛函

\[
\omega:\mathcal A\to\mathbb C,
\qquad
\omega(I)=1.
\]

一个 effect 是满足

\[
0\le E\le I
\]

的元素。定义事件概率

\[
\boxed{
p_\omega(E)=\omega(E).
}
\]

若 \(E=P=P^*=P^2\)，则 \(P\) 是锐利事件。Hilbert 表示中若

\[
\omega(A)=\operatorname{Tr}(\rho A),
\]

则

\[
\boxed{
p_\rho(P)
=
\operatorname{Tr}(\rho P).
}
\]

纯态 \(\rho=|\psi\rangle\langle\psi|\) 时：

\[
\boxed{
p_\psi(P)
=
\|P\psi\|^2.
}
\]

因此：

\[
\boxed{
\text{投影定义问题，状态定义权重，配对产生概率。}
}
\]

### 定理 30.16（正交可加性）

若 \((P_i)\) 为有限或可数正交投影族，且

\[
\sum_iP_i=I
\]

于强算子拓扑，则

\[
\boxed{
\sum_i\omega(P_i)=1.
}
\]

纯态情形为 Parseval 分解：

\[
\boxed{
\sum_i\|P_i\psi\|^2=\|\psi\|^2.
}
\]

#### 证明

有限情形由线性性。可数情形由正态状态对递增投影和的单调连续性；纯态情形等价于正交分量的 Pythagoras/Parseval。 \(\square\)

概率因此是完整状态经离散投影族后留下的标量质量，但不能把

\[
P_i
\]

与

\[
\omega(P_i)
\]

识别为同一个对象。

---

## 30.7 经典概率也是 Hilbert 投影；量子性来自非交换

设经典概率空间

\[
(\Omega,\Sigma,\mu)
\]

并取

\[
\mathscr H=L^2(\Omega,\mu).
\]

对事件 \(A\in\Sigma\)，定义乘法投影

\[
(P_Af)(\omega)=\mathbf1_A(\omega)f(\omega).
\]

则

\[
P_A^2=P_A=P_A^*,
\]

并且

\[
\boxed{
\mu(A)
=
\langle\mathbf1,P_A\mathbf1\rangle.
}
\]

若 \(\mathcal G\subseteq\Sigma\) 为子 \(\sigma\)-代数，则条件期望

\[
\boxed{
\mathbb E[X\mid\mathcal G]
}
\]

是 \(L^2(\mathcal G)\) 上的正交投影。

所以“概率来自 Hilbert 投影”并不区分经典与量子。真正的差异是：

\[
\boxed{
\text{经典事件投影形成交换 Boolean 代数；}
}
\]

而

\[
\boxed{
\text{量子投影总体形成非分配的 orthomodular 格，且一般不交换。}
}
\]

---

## 30.8 两个投影何时属于同一个经典界面

设 \(P,Q\) 为 Hilbert 空间上的正交投影。

### 定理 30.17（共同四扇区分解判据）

下列条件等价：

1. \(PQ=QP\)；
2. 四个算子
   \[
   PQ,\quad
   P(I-Q),\quad
   (I-P)Q,\quad
   (I-P)(I-Q)
   \]
   都是正交投影；
3. \(\mathscr H\) 有正交分解
   \[
   \boxed{
   \mathscr H
   =
   \operatorname{ran}(PQ)
   \oplus
   \operatorname{ran}(P(I-Q))
   \oplus
   \operatorname{ran}((I-P)Q)
   \oplus
   \operatorname{ran}((I-P)(I-Q)).
   }
   \]
4. 存在一个四结果 PVM \((R_{ab})_{a,b\in\{0,1\}}\)，使
   \[
   P=R_{10}+R_{11},
   \qquad
   Q=R_{01}+R_{11}.
   \]

#### 证明

若 \(P,Q\) 交换，则所有多项式组合仍为自伴幂等元，四项两两正交且和为 \(I\)，得到 2、3、4。

若存在第 4 项，则

\[
PQ
=
(R_{10}+R_{11})(R_{01}+R_{11})
=
R_{11}
=
QP.
\]

故 4 推出 1。其余蕴含由对应投影构造直接得到。 \(\square\)

因此：

\[
\boxed{
PQ=QP
}
\]

恰好意味着两个是／否问题可以被嵌入同一个经典四格界面。


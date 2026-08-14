\qquad
\|e\|=1.
\]

它是**线性张成的完备失败**，但没有规范唯一逃逸对象。

### 量子上下文障碍

局部交换上下文各自允许经典赋值，但这些赋值不能拼成保持全部函数关系的全局 \(0/1\) 截面。

它是**局部 Boolean 图册的全局拼接失败**。

三者共同具有：

\[
\boxed{
\text{相对于当前描述存在未闭合余量。}
}
\]

但不能相互替代：

\[
\boxed{
\text{自描述满射失败}
\ne
\text{正交张成失败}
\ne
\text{上下文全局截面失败}.
}
\]

只有在给出明确函子、自然变换及双向定理后，才能把一个障碍传递到另一个领域。

---

## 30.18 “绝对是全部相对关系的闭合”的形式版本

设 \(\mathsf I\) 为界面范畴，给出逆系统

\[
F:\mathsf I^{op}\to\mathsf C,
\]

其中 \(F(i)=X_i\) 是第 \(i\) 个相对读出对象。整体候选是锥

\[
(q_i:X\to X_i)_i.
\]

若该锥满足极限泛性质，则

\[
\boxed{
X\cong\varprojlim_{i\in\mathsf I}X_i.
}
\]

这意味着：对任何另一个对象 \(Y\)，只要有一族相容读出

\[
f_i:Y\to X_i,
\qquad
p_{j,i}f_j=f_i,
\]

就存在唯一

\[
f:Y\to X
\]

使

\[
q_if=f_i.
\]

所以“绝对”不是一个内容最多的单一视角，而是：

\[
\boxed{
\text{使全部相对视角相容因子化的普适对象。}
}
\]

但在 Hilbert、拓扑、概率或算子代数范畴中，必须使用相应范畴的极限与可实现性条件；集合极限可能过大或忘记范数、正性和连续性。

量子理论进一步提示，全部交换上下文的简单集合极限未必给出一个全局经典样本空间。正确全局对象是非交换代数 \(\mathcal A\) 及其状态，而不是所有局部 Gelfand 谱的普通拼接。

因此：

\[
\boxed{
\text{绝对不是相对性的反面；绝对是相对转换规律及其闭合对象。}
}
\]

---

## 30.19 相对性六层审计

一个声称“从有限观察重构整体”的理论至少应通过以下六层审计。

### 第一层：身份审计

明确：

\[
x\sim_qy
\iff
q(x)=q(y).
\]

回答哪些差异被界面商掉。

### 第二层：余量审计

明确纤维、核、正交补或条件分布，回答被删除的信息在哪里。

### 第三层：自然性审计

检查

\[
qT=T_q q
\]

或对角版本

\[
Q\Delta=\Delta P.
\]

回答有效规律是否严格下降。

### 第四层：忠实性审计

检查界面是否仍能区分

\[
y
\quad\text{与}\quad
\tau y,
\]

避免“盲自然性”。

### 第五层：完成审计

区分：

\[
\text{分离性},
\quad
\text{形式相容性},
\quad
\text{可实现性},
\quad
\text{有界能量/正则性}.
\]

### 第六层：上下文审计

当存在多个不兼容界面时，检查：

\[
\text{重叠一致性},
\quad
\text{共同精化},
\quad
\text{全局截面},
\quad
\text{非交换障碍}.
\]

只有全部六层同时说明，才可以把“相对观察”提升为严谨的局部—整体理论。

---

## 30.20 与 Riemann 假设接口的再解释

第 29 节得到：

\[
\mathrm{RH}
\iff
P_{R_\infty}\chi=0
\]

于 Nyman–Beurling 商余塔。

本节说明其相对性含义：

- \(S_N\) 是由前 \(N\) 个显式算术生成元形成的有限观察界面；
- \(R_N\) 是相对于该算术界面仍未解释的方向；
- \(d_N=\|P_{R_N}\chi\|\) 是指定目标的相对余量；
- RH 不要求所有可能向量都被该界面塔统一解释；
- RH 只要求 \(\chi\) 相对于完整算术界面族最终可实现，即
  \[
  [\chi]=0
  \quad
  \text{于 }
  \mathscr H/S_\infty.
  \]

因此 RH 的 Hilbert 表述不是“绝对余空间不存在”，而是：

\[
\boxed{
\text{相对于指定算术生成规则，目标向量没有最终不可解释分量。}
}
\]

这与量子状态完成的形式完全平行：

\[
\operatorname{Tr}(\rho Q_\infty)=0.
\]

两者共享“状态/目标相对完成”结构，但一个是解析数论逼近判据，一个是量子状态支撑判据；二者不能仅凭形式相同而互相证明。

---

## 30.21 可形式化拆分

建议新增以下 Lean 纸面目标，按依赖顺序推进。

1. `ObserverInterfaceKernel`
   \[
   q_i=p_{j,i}q_j
   \Rightarrow
   \ker q_j\subseteq\ker q_i.
   \]

2. `ObserverLimitSeparation`
   \[
   \Phi\text{ injective}
   \iff
   \bigcap_i\ker q_i=\{0\}.
   \]

3. `ObserverLimitRealizability`
   \[
   X/{\sim_\infty}\cong\operatorname{im}\Phi.
   \]

4. `DiagonalInterfaceNaturality`
   \[
   q\tau=\bar\tau q
   \Rightarrow
   Q\Delta_\tau=\Delta_{\bar\tau}P.
   \]

5. `DiagonalBlindQuotient`
   \[
   q\tau=q
   \Rightarrow
   Q\Delta_\tau=QD.
   \]

6. `CommutingProjectionJointPVM`
   两投影交换当且仅当存在共同四结果 PVM。

7. `HilbertSchmidtDephasingProjection`
   \[
   \mathcal D_P^2=\mathcal D_P=\mathcal D_P^*.
   \]

8. `ProjectionProbabilityFlow`
   \[
   \frac d{dt}\operatorname{Tr}(\rho_tP)
   =
   i\operatorname{Tr}(\rho_t[H,P]).
   \]

9. `StateRelativeCompletion`
   \[
   \operatorname{Tr}(\rho Q_\infty)=0
   \iff
   \operatorname{supp}\rho\le P_\infty.
   \]

10. `ContextRestrictionCompatibility`
    状态在交换子代数交集上的限制一致。

Kochen–Specker、Gleason、Naimark、Stinespring 与 GNS 等一般结果应作为具名、来源可审计的经典接口接入，不能以无名公理隐藏。

---

## 30.22 最终统一式

本节得到：

\[
\boxed{
\text{相对性}
=
\text{选择界面并声明界面转换}.
}
\]

\[
\boxed{
\text{商}
=
\text{该界面保留的身份空间}.
}
\]

\[
\boxed{
\text{余}
=
\text{该界面删除的纤维、核或正交分量}.
}
\]

\[
\boxed{
\text{对角化}
=
\text{描述界面不能以同类型封闭自身的证书}.
}
\]

\[
\boxed{
\infty
=
\text{任何有限界面都不终止，但全部相容界面可以完成}.
}
\]

\[
\boxed{
\text{概率}
=
\text{状态对 effect 的评价，而非 effect 本身}.
}
\]

\[
\boxed{
\text{量子性}
=
\text{一族局部经典上下文不能被压平为单一全局 Boolean 上下文}.
}
\]

最凝练的结论是：

\[
\boxed{
\text{整体不是某个观察者看到的最大画面；整体是全部相对观察、转换、余量与一致性条件的闭合。}
}
\]

而量子力学在这个框架中的位置是：

\[
\boxed{
\text{每个测量上下文投影出一个经典概率世界；
完整量子世界则保存这些局部经典世界之间不可交换、不可共同锐化的关系。}
}
\]

## 30.23 严格非主张与形式化状态

1. 本节不把哲学上的全部相对性约化为数学商映射。
2. 本节不声称集合逆极限总能恢复拓扑、Hilbert 或算子代数整体。
3. 本节不把概率等同于投影；概率始终依赖状态—effect 配对。
4. 本节不把 Naimark/Stinespring 扩张解释为唯一隐藏经典本体。
5. 本节不把退相干等同于单一结果选择。
6. 本节不把量子上下文性、Bell 非局域性与 Cantor 对角化视为同一定理。
7. 本节不从界面相对性推出 Riemann 假设、光速信息率或意识模型。
8. 本节新增定理均为纸面结论；在获得 kernel verification 以前不得标记为 `Closed`。

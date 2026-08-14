## 31.3 互相无偏基在算子 Hilbert 空间中给出正交对角平面

取两组正交基

\[
\mathcal B=(|b_j\rangle)_j,
\qquad
\mathcal C=(|c_k\rangle)_k.
\]

定义重叠矩阵

\[
M_{jk}
=
|\langle b_j,c_k\rangle|^2
=
\operatorname{Tr}(P_j^{\mathcal B}P_k^{\mathcal C}).
\]

\(M\) 是双随机矩阵。

两基互相无偏，是指

\[
\boxed{
M_{jk}=\frac1d
\qquad
\forall j,k.
}
\]

### 定理 31.5（MUB 等价于无迹对角平面正交）

下列命题等价：

1. \(\mathcal B,\mathcal C\) 互相无偏；
2. \(\mathcal D_{\mathcal B}^0\perp\mathcal D_{\mathcal C}^0\) 于 Hilbert–Schmidt 内积；
3. 对任意 \(X\in\operatorname{Herm}_d^0\)，

   \[
   \mathbb E_{\mathcal B}\mathbb E_{\mathcal C}(X)=0
   =
   \mathbb E_{\mathcal C}\mathbb E_{\mathcal B}(X);
   \]

4. 对任意 \(X\in\operatorname{Herm}_d\)，

   \[
   \boxed{
   \mathbb E_{\mathcal B}\mathbb E_{\mathcal C}(X)
   =
   \mathbb E_{\mathcal C}\mathbb E_{\mathcal B}(X)
   =
   \frac{\operatorname{Tr}X}{d}I.
   }
   \]

#### 证明

若两基互相无偏，取

\[
A=\sum_ja_jP_j^{\mathcal B},
\qquad
B=\sum_kb_kP_k^{\mathcal C},
\]

且

\[
\sum_ja_j=\sum_kb_k=0.
\]

则

\[
\langle A,B\rangle_{\mathrm{HS}}
=
\sum_{j,k}a_jb_kM_{jk}
=
\frac1d
\left(\sum_ja_j\right)
\left(\sum_kb_k\right)
=
0.
\]

故 1 推出 2。正交投影到两个正交子空间的复合为零，故 2 推出 3。

对任意 \(X\)，写

\[
X=\frac{\operatorname{Tr}X}{d}I+X_0,
\qquad
\operatorname{Tr}X_0=0.
\]

两映射均固定 \(I\)，而在 \(X_0\) 上复合为零，故得到 4。

最后，令 \(X=P_k^{\mathcal C}\)。由 4，

\[
\mathbb E_{\mathcal B}(P_k^{\mathcal C})
=
\sum_jM_{jk}P_j^{\mathcal B}
=
\frac Id,
\]

比较各 \(P_j^{\mathcal B}\) 系数得到 \(M_{jk}=1/d\)，故 4 推出 1。 \(\square\)

### 关键反例 31.6（去相干通道交换不等于锐利兼容）

当 \(\mathcal B,\mathcal C\) 为 MUB 时，

\[
\boxed{
[\mathbb E_{\mathcal B},\mathbb E_{\mathcal C}]=0,
}
\]

因为两种复合都等于完全退极化投影

\[
X\mapsto\frac{\operatorname{Tr}X}{d}I.
\]

然而任意非平凡 \(P_j^{\mathcal B},P_k^{\mathcal C}\) 一般满足

\[
[P_j^{\mathcal B},P_k^{\mathcal C}]\ne0.
\]

所以

\[
\boxed{
\text{粗粒化顺序无差异}
\not\Rightarrow
\text{锐利测量兼容}.
}
\]

事实上，MUB 是最大互补的锐利坐标系，却给出零去相干顺序缺陷。由此，第 30 节所定义的

\[
\mathbb E_i\mathbb E_j-\mathbb E_j\mathbb E_i
\]

只能测量“丢弃信息的顺序是否重要”，不能单独充当上下文不兼容度。

---

## 31.4 锐利不兼容度、坐标冗余与投影交换子的精确公式

定义中心化投影

\[
\widetilde P_j^{\mathcal B}
=
P_j^{\mathcal B}-\frac Id,
\qquad
\widetilde P_k^{\mathcal C}
=
P_k^{\mathcal C}-\frac Id.
\]

则

\[
\left\langle
\widetilde P_j^{\mathcal B},
\widetilde P_k^{\mathcal C}
\right\rangle_{\mathrm{HS}}
=
M_{jk}-\frac1d.
\]

定义对角平面冗余能量

\[
\boxed{
\mathcal R(\mathcal B,\mathcal C)
=
\sum_{j,k}
\left(M_{jk}-\frac1d\right)^2.
}
\]

利用双随机性，

\[
\boxed{
\mathcal R(\mathcal B,\mathcal C)
=
\sum_{j,k}M_{jk}^2-1.
}
\]

由于任意双随机矩阵满足

\[
1\le\sum_{j,k}M_{jk}^2\le d,
\]

故

\[
0\le\mathcal R\le d-1.
\]

- \(\mathcal R=0\) 当且仅当两基互相无偏；
- \(\mathcal R=d-1\) 当且仅当 \(M\) 为置换矩阵，即两基相同到相位与重标记。

定义归一化锐利不兼容度

\[
\boxed{
\mathcal I(\mathcal B,\mathcal C)
=
1-\frac{\mathcal R(\mathcal B,\mathcal C)}{d-1}
=
\frac{
d-\sum_{j,k}M_{jk}^2
}{
d-1
}.
}
\]

于是

\[
\boxed{
0\le\mathcal I\le1,
}
\]

\[
\boxed{
\mathcal I=0
\iff
\text{同一锐利上下文},
}
\]

\[
\boxed{
\mathcal I=1
\iff
\text{MUB 最大互补上下文}.
}
\]

### 定理 31.7（聚合投影交换子公式）

对秩一上下文，

\[
\boxed{
\sum_{j,k}
\left\|
[P_j^{\mathcal B},P_k^{\mathcal C}]
\right\|_2^2
=
2(d-1)\mathcal I(\mathcal B,\mathcal C).
}
\]

#### 证明

对两个秩一投影 \(P,Q\)，若

\[
m=\operatorname{Tr}(PQ),
\]

直接计算得

\[
\|[P,Q]\|_2^2
=
2m(1-m).
\]

因此

\[
\sum_{j,k}\|[P_j,Q_k]\|_2^2
=
2\sum_{j,k}M_{jk}(1-M_{jk}).
\]

又因

\[
\sum_{j,k}M_{jk}=d,
\]

故

\[
2\sum_{j,k}M_{jk}(1-M_{jk})
=
2\left(
d-\sum_{j,k}M_{jk}^2
\right)
=
2(d-1)\mathcal I.
\]

\(\square\)

因此本节得到三种必须分开的量：

\[
\boxed{
\begin{aligned}
\mathcal I(\mathcal B,\mathcal C)
&=\text{锐利投影不兼容度},\\
\mathcal O_{\mathcal B,\mathcal C}(\rho)
&=
\|
\mathbb E_{\mathcal B}\mathbb E_{\mathcal C}(\rho)
-
\mathbb E_{\mathcal C}\mathbb E_{\mathcal B}(\rho)
\|
=\text{粗粒化顺序缺陷},\\
\mathcal G
&=\text{多上下文全局拼接／非上下文模型缺陷}.
\end{aligned}
}
\]

MUB 给出

\[
\mathcal I=1,
\qquad
\mathcal O=0.
\]

相同基给出

\[
\mathcal I=0,
\qquad
\mathcal O=0.
\]

因此 \(\mathcal O\) 甚至不能按 \(\mathcal I\) 单调排序。全局 contextuality 又不能由任意单个成对量完全决定；一般化非上下文性中，测量不兼容既非必要也非充分条件。故“量子上下文缺陷”必须是多分量审计，而不是一个被过度命名的交换子。

---

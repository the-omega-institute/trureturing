## 31.10 熵的三重分家：状态混合、测量不确定性与相干余量

为避免把“熵”当成唯一无序标量，本节区分：

### 状态熵

\[
\boxed{
S(\rho)=-\operatorname{Tr}(\rho\log\rho).
}
\]

它测量状态本身的混合度，基无关。

### 上下文结果熵

\[
\boxed{
H_{\mathcal B}(\rho)
=
-\sum_jp_j^{\mathcal B}\log p_j^{\mathcal B}.
}
\]

它依赖观察坐标系。纯态可以有

\[
S(\rho)=0
\]

但在某个 MUB 上有

\[
H_{\mathcal B}(\rho)=\log d.
\]

### 相对熵相干

\[
\boxed{
C_{\mathcal B}(\rho)
=
D(\rho\|
\mathbb E_{\mathcal B}\rho)
=
S(\mathbb E_{\mathcal B}\rho)-S(\rho).
}
\]

它测量相对于指定对角代数被删除的跨扇区关系。

最大混合态满足

\[
S(I/d)=\log d
\]

但对所有基都有

\[
C_{\mathcal B}(I/d)=0.
\]

所以：

\[
\boxed{
\text{高状态熵不等于高量子相干，}
}
\]

\[
\boxed{
\text{高测量熵也不等于状态本身高度混合.}
}
\]

MUB 塔的二次恒等式使用的是 purity／Hilbert–Schmidt 质量，而不是 Shannon 或 von Neumann 熵。不同熵可以通过不等式关联，但不得直接互换定义。

---

## 31.11 无限维推广的正确边界

有限维完整 MUB 塔提供了一个清洁模型，但不能未经证明直接推广到任意无限维 Hilbert 空间。

无限维中需要分别处理：

1. 是否存在合适的互补基、frame 或 POVM；
2. 对角子空间的闭合性；
3. 测量映射是否有 frame 上下界；
4. 状态是否为迹类，二次量是否有限；
5. 无限概率坐标族是否满足统一能量界；
6. 形式相容坐标是否确实来自一个正常状态；
7. 动力学与各条件期望的定义域是否稳定。

合理推广是：在一个 von Neumann 代数 \(\mathcal A\) 中取一族正常条件期望

\[
\mathbb E_i:\mathcal A\to\mathcal C_i,
\]

令可见算子子空间逐层增长，并在 \(L^2(\mathcal A,\omega)\) 或标准形式 Hilbert 空间中研究其正交余量。完成不能只取普通集合逆极限，还必须加入正常性、能量或平方可和条件。这与第 28 节的 bounded-energy inverse limit 完全一致。

---

## 31.12 与既有文献的边界及候选新贡献

以下事实属于成熟理论，不应重新命名为本项目独有发现：

- 一组基测量只给出状态在该基上的概率；
- \(d+1\) 组完整 MUB 可用于最优量子态层析；
- 素数幂维数存在完整 MUB 集；
- 去相干是到交换子代数的条件期望／投影；
- relative entropy of coherence 等于去相干熵增；
- 重复测量可诱导经典 Markov 动力学；
- contextuality 与 measurement incompatibility 不是同一概念。

本稿的候选新贡献位于它们的组合方式：

1. 把 MUB 对角代数组织成第 28 节意义下的严格正交商余塔；
2. 同时定义状态无关的余维率和状态相关的 Hilbert–Schmidt 余质量；
3. 由余质量给出自指对角操作与动力学降阶误差的统一 Lipschitz 界；
4. 识别并证明“MUB 最大不兼容但去相干交换子为零”的框架反例；
5. 将锐利不兼容、粗粒化顺序、层析冗余与全局 contextuality 拆成四维审计；
6. 把重复投影的熵箭头写成逐步删除相干的精确 telescoping identity；
7. 将坐标精化时间与物理动力时间明确分离，再通过自然性缺陷研究二者耦合。

是否具有发表意义仍取决于进一步文献审计、非平凡推广以及至少一个不能由现有 MUB／资源理论定理直接重写得到的新结果。

---

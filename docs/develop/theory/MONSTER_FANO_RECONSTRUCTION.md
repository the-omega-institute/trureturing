# Monster 标签三元组的 Fano 接合重构

## 1. 范围与来源

本卷是参考输入；数学真源是 Lean 声明及其证明项。这里从七点三元组的唯一点对关联重构组合闭包，作为 [PR #10310](https://github.com/the-omega-institute/trureturing/pull/10310) §30.1 的逆向组合接口。不预设标签加法、二次型、子空间、块数或标准 Fano 编号。

与 [既有理论问卷](MONSTER_SHORT_SUPPORT_SPIN.md#理论问卷下一轮入口) 的关系是：本卷只回答有限三元组闭包问题，不回答实际 VOA 模、融合、最低共形权、OPE 或弦理论存在性问题。

## 2. 七点块系统

**定义 2.1（唯一点对关联）。** 令 $X=\{0,\ldots,6\}$，$\mathcal B$ 是 $X$ 的子集所成的有限集合。要求每个 $A\in\mathcal B$ 满足 $|A|=3$，并且任意不同的 $i,j\in X$ 恰在一个 $A\in\mathcal B$ 中同时出现。

**定理 2.2（对称差补集闭包）。** 对每个满足定义 2.1 的 $\mathcal B$，以及任意不同的 $A,B\in\mathcal B$，都有

$$
X\setminus(A\mathbin\triangle B)\in\mathcal B.
$$

**证明。** 不同块交点数至多一：若两个不同点同时在两个块中，唯一点对关联就使这两个块相等。

假设 $A,B$ 不交。它们的并有六点，其补集是单点 $\{c\}$。固定 $a\in A$ 和不同的 $b,b'\in B$。经过 $a,b$ 的块 $C$ 不同于 $A,B$，因而在 $A$ 中只能含 $a$，在 $B$ 中只能含 $b$。所以 $C\subseteq\{a,b,c\}$，且三元性强迫 $c\in C$。同样，经过 $a,b'$ 的块 $C'$ 含 $c$。由点对 $a,c$ 的唯一性，$C=C'$。此块含 $b,b'$，又由该点对的唯一性得到 $C=B$，与 $a\notin B$ 矛盾。因此不同块交点数恰为一。

令 $A\cap B=\{o\}$。由三元性，$|A\cup B|=5$，所以 $X\setminus(A\cup B)=\{p,q\}$，其中 $p\ne q$。取经过 $p,q$ 的唯一块 $D$。它不同于 $A,B$，与两者分别相交恰一点。由于 $D\setminus\{p,q\}$ 恰含一点，这两个交点必须相同，故都是 $o$。于是 $D=\{p,q,o\}=X\setminus(A\mathbin\triangle B)$。证毕。

## 3. 文献与未解边界

本结论是七点 Steiner 三元组系统的组合推导，不主张新的文献原创性。PR #10310 §30.1 从全奇异标签子空间推出 Fano 关联；这里证明关联公理足以推出对称差补集闭包，但不据此声称三十种完成的计数、向量空间重构或 VOA 扩展已形式化。

- Tathagata Basak, *The octonions as a twisted group algebra*, arXiv:1702.05705v1 (2017), Theorem 1：七个非零标签与八元数扭群代数的背景，不作为本组合证明的前提。
- J. van Ekeren, S. Möller, N. R. Scheithauer, *Construction and Classification of Holomorphic Vertex Operator Algebras*, J. reine angew. Math. 759 (2020), 61–99, DOI 10.1515/crelle-2017-0046（VEMS20）：实际简单流扩展所需的独立接口，不由唯一点对关联推出。
- [PR #10310 §30.1](MONSTER_LOCAL_COMPLETION_AND_CUBIC_RESPONSE.md#30-三十种局部整数自旋完成及其全-a-型对偶)：有限标签与 Fano 接合的理论来源。
- [Monster 短支持自旋问卷](MONSTER_SHORT_SUPPORT_SPIN.md#理论问卷下一轮入口)：实际模块、融合与共形权的未解义务保持不变。

## 追加锚（本行以下为增补区）
